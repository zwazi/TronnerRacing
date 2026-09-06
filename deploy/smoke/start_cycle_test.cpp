#include "config.h"
#include "defs.h"
#include "gCycle.h"
#include "eGrid.h"
#include "ePlayer.h"
#include "eTimer.h"
#include "nNetwork.h"
#include "tConfiguration.h"
#include "tDirectories.h"
#include "tLocale.h"
#include <cstdlib>
#include <cassert>
#include <cmath>
#include <sstream>
#include <iostream>

bool *sg_GetSpecs()
{
    static bool spectators[MAXCLIENTS + 2] = {};
    return spectators;
}

// This fixture creates its grid directly, without gGame's network handshake.
// Model the already-ready grid while retaining the player creation dependency;
// gCycle's actual sync gate and all movement/release code remain under test.
bool eNetGameObject::ClearToTransmit(int user) const
{
    return !Player() || Player()->HasBeenTransmitted(user);
}

class InputCycle : public gCycle
{
public:
    using gCycle::gCycle;
    void SetInputDirection(eCoord const &direction) { dirDrive = dir = direction; }
    void StepStockPhysics(REAL now) { gCycleMovement::TimestepCore(now, true); }
    void Known(int user, bool known = true) { knowsAbout[user].knowsAboutExistence = known; }
    void ClearSync(int user) { knowsAbout[user].syncReq = knowsAbout[user].nextSyncAck = false; }
    bool ReliableSync(int user) const { return knowsAbout[user].syncReq && knowsAbout[user].nextSyncAck; }
};

class KnownPlayer : public ePlayerNetID
{
public:
    void Known(int user) { knowsAbout[user].knowsAboutExistence = true; }
};

int main()
{
    char const *data = std::getenv("TRONNER_ENGINE_DATA_DIR");
    assert(data && *data);
    tDirectories::SetData(tString(data));
    tLocale::Load("languages.txt");
    // Exercise the real cycle implementation without touching a game client.
    tCurrentAccessLevel access(tAccessLevel_Owner, true);
    std::istringstream settings(
        "CYCLE_SPEED 125\nCYCLE_START_SPEED 20\n"
        "CYCLE_SPEED_DECAY_BELOW 0.2\nCYCLE_SPEED_MIN 0\nCYCLE_BRAKE 30\n"
        "SERVER_PORT 0\n");
    tConfItemBase::LoadAll(settings);
    sn_SetNetState(nSERVER);
    se_MakeGameTimer();
    se_ResetGameTimer(0);
    tJUST_CONTROLLED_PTR<eGrid> grid = new eGrid;
    grid->Create();
    grid->SetWinding(8);
    ePlayerNetID *player = new ePlayerNetID;
    gCycle *cycle = new gCycle(grid, eCoord(0, 0), eCoord(1, 0), player);
    const REAL nativeSpeed = cycle->Speed();
    assert(nativeSpeed > 0);
    cycle->StartBraked(3);
    REAL release = se_GameTime() + 3;
    assert(cycle->GetBraking() == 1);
    assert(cycle->IsStartHeld(0));
    cycle->SetBraking(0);
    gDestination early(*cycle);
    assert(cycle->HandleStartHoldDestination(early));
    cycle->TimestepCore(release - .1);
    assert(cycle->IsStartHeld(release - .1));
    assert(cycle->MapPosition().NormSquared() < 1e-8);
    cycle->TimestepCore(release + .01);
    assert(!cycle->IsStartHeld(release + .01));
    assert(std::abs(cycle->RaceStartTime() - release) < .01);
    assert(cycle->Speed() >= nativeSpeed);
    assert(cycle->GetBraking() == 0);
    std::cout << "Real cycle countdown hold/release passed" << std::endl;
    InputCycle *prediction = new InputCycle(grid, eCoord(50, 50), eCoord(1, 0), new ePlayerNetID);
    prediction->StartBraked();
    eCoord const predictionPosition = prediction->MapPosition();
    REAL const predictionStart = se_GameTime();
    for (int tick = 1; tick <= 60; ++tick)
        prediction->StepStockPhysics(predictionStart + tick * .05);
    assert((prediction->MapPosition() - predictionPosition).NormSquared() < 1e-8);
    assert(std::abs(prediction->Speed()) < 1e-6);
    std::cout << "Stock brake physics holds without a decay override" << std::endl;
    gCycle *manual = new gCycle(grid, eCoord(100, 100), eCoord(1, 0), player);
    InputCycle *input = new InputCycle(grid, eCoord(200, 200), eCoord(1, 0), new ePlayerNetID);
    manual->StartBraked();
    eCoord const heldPosition = manual->MapPosition();
    input->SetBraking(1);
    const int initialWinding = grid->DirectionWinding(manual->Direction());
    const unsigned short initialTurns = manual->GetTurns();
    for (int winding = 1; winding <= 5; ++winding)
    {
        input->SetInputDirection(grid->GetDirection((initialWinding + winding) % 8));
        gDestination turn(*input);
        assert(manual->HandleStartHoldDestination(turn));
    }
    assert(manual->GetTurns() == initialTurns + 3);
    manual->TimestepCore(se_GameTime() + 2);
    assert(manual->IsStartHeld(0));
    assert((manual->MapPosition() - heldPosition).NormSquared() < 1e-8);
    input->SetBraking(0);
    gDestination off(*input);
    manual->HandleStartHoldDestination(off);
    player->SetChatting(ePlayerNetID::ChatFlags_Away, true);
    manual->TimestepCore(se_GameTime() + 3);
    player->SetChatting(ePlayerNetID::ChatFlags_Away, false);
    manual->TimestepCore(se_GameTime() + 4);
    assert(manual->IsStartHeld(0));
    manual->HandleStartHoldDestination(off);
    manual->TimestepCore(se_GameTime() + 5);
    assert(!manual->IsStartHeld(0));
    assert(std::abs(manual->Speed() - nativeSpeed) < .01);
    std::cout << "Real cycle held turns, focus cancellation and manual release passed" << std::endl;
    KnownPlayer *networkPlayer = new KnownPlayer;
    networkPlayer->Known(0);
    networkPlayer->Known(1);
    InputCycle *networkCycle = new InputCycle(grid, eCoord(300, 300), eCoord(1, 0), networkPlayer);
    input->SetInputDirection(eCoord(1, 0));
    input->SetBraking(0);
    gDestination networkOff(*input);
    networkCycle->StartBraked();
    networkCycle->Known(0);
    networkCycle->Known(1);
    assert(networkCycle->ClearToTransmit(0));
    assert(networkCycle->HandleStartHoldDestination(networkOff));
    // Only the owner's contradictory held-state updates are deferred. Other
    // viewers, object creation and the server's own physics stay unchanged.
    assert(!networkCycle->ClearToTransmit(0));
    assert(networkCycle->ClearToTransmit(1));
    networkCycle->Known(0, false);
    assert(networkCycle->ClearToTransmit(0));
    networkCycle->Known(0);
    REAL requestTime = se_GameTime();
    eCoord serverHold = networkCycle->MapPosition();
    networkCycle->TimestepCore(requestTime + .1);
    assert(networkCycle->IsStartHeld(0));
    assert(networkCycle->GetBraking() == 1);
    assert(networkCycle->Speed() == 0);
    assert((networkCycle->MapPosition() - serverHold).NormSquared() < 1e-8);
    networkPlayer->SetChatting(ePlayerNetID::ChatFlags_Away, true);
    networkCycle->TimestepCore(requestTime + .15);
    assert(networkCycle->ClearToTransmit(0));
    assert(networkCycle->IsStartHeld(0));
    networkPlayer->SetChatting(ePlayerNetID::ChatFlags_Away, false);
    networkCycle->HandleStartHoldDestination(networkOff);
    networkCycle->ClearSync(0);
    networkCycle->ClearSync(1);
    networkCycle->TimestepCore(requestTime + 2);
    assert(!networkCycle->IsStartHeld(0));
    assert(networkCycle->ClearToTransmit(0));
    assert(networkCycle->ReliableSync(0));
    assert(networkCycle->ReliableSync(1));
    assert(std::abs(networkCycle->Speed() - nativeSpeed) < .01);
    // Death cannot remain hidden behind a pending manual release.
    InputCycle *dying = new InputCycle(grid, eCoord(400, 400), eCoord(1, 0), networkPlayer);
    dying->StartBraked();
    dying->Known(0);
    dying->HandleStartHoldDestination(networkOff);
    assert(!dying->ClearToTransmit(0));
    dying->Kill();
    assert(dying->ClearToTransmit(0));
    std::cout << "Owner prediction, spectator sync, cancellation and reliable release passed" << std::endl;
    // Leave static game-object cleanup to the OS, as in a dedicated shutdown.
    std::_Exit(0);
}
