#include "gStartBrake.h"
#include <cassert>
#include <limits>

int main()
{
    gStartBrake hold;
    // A turn before receiving the initial brake sync is not a launch.
    hold.Input(false, true, false, 1, .05);
    assert(!hold.Ready(false, 2));
    hold.Input(true, true, false, 2, .05);
    assert(!hold.Ready(false, 3));
    // Native brake-off starts after the confirmation window.
    hold.Input(false, false, false, 3, .05);
    assert(!hold.Ready(false, 3.249));
    assert(hold.Ready(false, 3.25));
    hold.Reset();
    // ClearKeys can precede the chat/away sync. Cancel, do not defer launch.
    hold.Input(false, false, false, 4, .05);
    assert(!hold.Ready(true, 4.1));
    assert(!hold.Ready(false, 5));
    hold.Input(false, false, true, 5, .05);
    assert(!hold.Ready(false, 6));
    hold.Input(true, true, false, 6, .05);
    hold.Input(false, false, false, 7, .05);
    assert(hold.Ready(false, 7.25));
    hold.Reset();
    // Repeated brake-off packets don't postpone launch indefinitely.
    hold.Input(false, false, false, 10, .2);
    hold.Input(false, false, false, 10.4, .2);
    assert(!hold.Ready(false, 10.499));
    assert(hold.Ready(false, 10.5));
    hold.Input(true, false, false, 10.51, .2);
    assert(!hold.Ready(false, 12));
    hold.Reset();
    hold.Input(false, false, false, 20, std::numeric_limits<double>::quiet_NaN());
    assert(hold.Ready(false, 20.25));
}
