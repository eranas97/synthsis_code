############################################
# MTI - Video Poker
#
# Copyright 1991-2016 Mentor Graphics Corporation
#
# All Rights Reserved.
#
# THIS WORK CONTAINS TRADE SECRET AND PROPRIETARY INFORMATION WHICH IS THE PROPERTY OF 
# MENTOR GRAPHICS CORPORATION OR ITS LICENSORS AND IS SUBJECT TO LICENSE TERMS.
#
# v0.1 - Initial Release 
# v0.2 - Modified to work with 5.1*
# v0.3 - 1) Switched selection around.  Now you select what to keep.
#        2) Deal now pauses between cards for effect, Draw now turns over 
#           discards, waits, then releals, pausing between cards.  Looks good.
# v0.4 - Limited bet to no more than you have.  Fixed cheat so you only get taxed, not rewarded.
# v0.5 - 1) Turned status line into a three line scrollable text widget.
#        2) Added bankroll comments.  If you bust, you get more money.
# v0.6 - The bet was not being deducted from bankroll at Deal time.  Shouldn't then deduct it again
#        if the player fails to get Jacks or Better.
# v0.7 - Made seed get redriven each hand for even more randomness
# v0.8 - Fixed a reference to a Windows specific background color (SystemMenu).  Made it more generic.
# v0.9 - changed calls to 'exa' to explicit 'examine' to avoid ambiguity.
# v1.0 - Added AutoPlay
# v1.1 - Eliminated Tix widgets for Modelsim 5.6 compatability
############################################

########## Globals #########################
# Version
set appVersion "1.0"

# Card Image details
set card_width 0
set card_height 0

# Configuration
# if 1, add the "Lucky Rhino Casino" graphic to the GUI
set gameFelt 1
# Name of the image to use for the felt, size should be roughly 600 pixels wide, height around 150 pixels
set feltName "luckyrhino.gif"
set noRandSeed 25117

# Basic game details
set bankroll 1000
set betsize 20
set gameState 0
set statusLine ""
set defbg ""

# Card specifics
set allSuit {c d s h nocard back}
set allRank {a 2 3 4 5 6 7 8 9 10 j q k}
set display {0 0 0 0 0}
set dealt   {0 0 0 0 0}

# Payout formula
set payout  {0 1 2 3 4 6 9 25 50 800}

# Hand comments
set nohandCom {"No winner. Sorry, nothing there" "No winner. Tough luck!" "No winner. Better luck next time" "No winner. Too bad!" "No winner. If it weren't for bad luck, you'd have no luck at all..."}
set pairCom {"A Pair" "A Pair. It's not much, but it'll do" "A Pair. Two of a kind!" "A Pair. You squeaked out a winner"}
set twopairCom {"Two Pair. A Winner!" "Two Pair. A decent hand" "Two Pair. Not bad" "Two Pair. Time for Vegas!"}
set threeofakindCom {"Three of a kind." "Three of a kind. Triplets!" "Three of a kind. Three ways lucky" "Three of a kind. Nice job"}
set straightCom {"A Straight" "A Straight. All in a row..." "A straight. What are the odds of that?" "A straight. Was that an inside straight?"}
set flushCom {"A flush" "A Flush. Five in a suit" "A Flush. Sweet deal." "A Flush. Sometimes you just got it."}
set fullhouseCom {"A Full House" "A Full House.  Full Boat!" "A Full House. Too hot to handle" "A Full House. Way to go!" }
set fourofakindCom {"Four of a Kind" "Four of a Kind - Two pairs of pairs!" "Four of a Kind. A pair just like the other pair" "Four of a Kind.  Wow!" }
set straightflushCom {"A Straight Flush" "A Straight Flush - That's some hand" "A Straight Flush. Now that's cooking with gas!" "A Straight Flush - Time for Vegas, baby!" }
set royalflushCom {"A Royal Flush" "A Royal Flush - Jackpot!" "A Royal Flush - You broke the bank!" "A Royal Flush - Holy Grand Slam, Batman!" }

set bankrollCom {"a kindly gentleman lends you some cash." "you hock the pinkslip to the '78 Pinto." "Great Aunt Frieda leaves you some dough." "you find a rare coin worth some serious money." "you mortgage the house." "Robert Redford offers you some cash to spend one night with your partner."}

# General vars
set amountbet 0
set globalWin .
set cards {}
set breakResolver 0
set cheat 0
set game Poker
set gotRand 0
set handResolved 0

# Vars for the autoplay
set auto 0
set autoDelay 500
set autoDefBet 20

########## TCL Procedures ####################

proc autoPlay {} {
    global auto autoDelay 
    global betsize bankroll

    if {$auto == 1} {

        # Now, autoplay the game...
        pushPokerDeal
        after [expr 2 * $autoDelay] ; update idletasks
        set cards [autoEval]
        foreach card $cards {
            after $autoDelay ; pushCard $card ; update idletasks
        }
        after $autoDelay ; update idletasks
        pushPokerDraw
        after [expr 4 * $autoDelay] ; update idletasks
        # Fiddle with bet if appropriate.
        # incr betsize 5
        # Schedule next wakeup
        after $autoDelay { autoPlay }
    }
}

proc autoEval {} {
    set list {}
    set suits {}
    set ranks {}

    # Here is where we'll examine the hand dealt to figure out what to keep.
    # No promises of stellar AI.  First cut will be pretty dumb...

    set ranks [lappend ranks [xlateRank [examine -radix binary /top/rank0]]]
    set ranks [lappend ranks [xlateRank [examine -radix binary /top/rank1]]]
    set ranks [lappend ranks [xlateRank [examine -radix binary /top/rank2]]]
    set ranks [lappend ranks [xlateRank [examine -radix binary /top/rank3]]]
    set ranks [lappend ranks [xlateRank [examine -radix binary /top/rank4]]]

    set suits [lappend suits [xlateSuit [examine -radix binary /top/suit0]]]
    set suits [lappend suits [xlateSuit [examine -radix binary /top/suit1]]]
    set suits [lappend suits [xlateSuit [examine -radix binary /top/suit2]]]
    set suits [lappend suits [xlateSuit [examine -radix binary /top/suit3]]]
    set suits [lappend suits [xlateSuit [examine -radix binary /top/suit4]]]

    set value 0
    set total 0
    set straight 0
    set pair 0 
    set twopair 0 
    set threeofakind 0
    set fourofakind 0
    set fullhouse 0
             
    # Resolve the value of the hand - sitting on rank/suit0:4

    # Some sort of flush?
    if { ([lindex $suits 0] == [lindex $suits 1]) &&
         ([lindex $suits 0] == [lindex $suits 2]) &&
         ([lindex $suits 0] == [lindex $suits 3]) &&
         ([lindex $suits 0] == [lindex $suits 4]) } {
         # If we have a flush, just pick it and go.  Don't really care if it's royal or straight or normal
         set list [lappend list 0 1 2 3 4]
    } else {
        # Not a flush - Do some stuff to make deciding the hand easier
        # Sum the total of each rank
        foreach count {0 1 2 3 4 5 6 7 8 9 10 11 12 13} {
            set sum($count) 0
        }
        incr sum([lindex $ranks 0]); set whichcard([lindex $ranks 0]) [lappend whichcard([lindex $ranks 0]) 0]
        incr sum([lindex $ranks 1]); set whichcard([lindex $ranks 1]) [lappend whichcard([lindex $ranks 1]) 1]
        incr sum([lindex $ranks 2]); set whichcard([lindex $ranks 2]) [lappend whichcard([lindex $ranks 2]) 2]
        incr sum([lindex $ranks 3]); set whichcard([lindex $ranks 3]) [lappend whichcard([lindex $ranks 3]) 3]
        incr sum([lindex $ranks 4]); set whichcard([lindex $ranks 4]) [lappend whichcard([lindex $ranks 4]) 4]
        foreach count { 1 2 3 4 5 6 7 8 9 10 11 12 13 } {
            # Check for a straight
            if {$count > 4} {
                if { ($sum($count) == 1) && 
                     ($sum([expr $count-1]) == 1) && 
                     ($sum([expr $count-2]) == 1) && 
                     ($sum([expr $count-3]) == 1) && 
                     ($sum([expr $count-4]) == 1) } {
                         # Straight.  Pick all five and go
                         set list [lappend list 0 1 2 3 4]
                     }
            }
            if { ($count == 1) && 
                 ($sum(0) == 1) && 
                 ($sum(12) == 1) && 
                 ($sum(11) == 1) && 
                 ($sum(10) == 1) && 
                 ($sum(9) == 1) } {
                     # "Wrap" Straight (10, J, Q, K, A)
                     # Straight.  Pick all five and go
                     set list [lappend list 0 1 2 3 4]
            }
            # Check for pairs, two pair, three of a kind, four of a kind, full house...
            if { $sum($count) == 2 } {
                incr pair
                set list [concat $list $whichcard($count)]
            }
            if { $sum($count) == 3} {
                incr threeofakind
                set list [concat $list $whichcard($count)]
            }
            if { $sum($count) == 4} {
                incr fourofakind
                set list [concat $list $whichcard($count)]
            }
        }
        # Full House Check - not necessary since it's picked up w/ pair and 3ofakind
    }
    # Last chance try anything kinds of things
    # With nothing better showing, a better algorithm would go for 
    # four-to-straight, four-to-a-flush, inside-straight, that kind of thing.
    # First iteration will be to just pick anything Jack or Better
    if {[llength $list] == 0} {
        # Nothing interesting to pick
        foreach count {0 1 2 3 4} {
            if { ([lindex $ranks $count] >= 10) || ([lindex $ranks $count] == 0) } {
                set list [lappend list $count]
            }
        }
    }
    return $list
}

proc setRand {} {
    global gotRand noRandSeed
    # Create and load the random number seed to the deck
    if {$gotRand} {
        set seed [expr int(rand()*65536)]
    } else {
        # If the version of Tcl is pre 8.0, we have no rand or srand
        # so we drive an arbitrary value in on seed.  Pick another to
        # get a different sequence of cards
        set seed $noRandSeed
    }
#    puts "Seed from TCL is $seed."
    force /top/seed 10#${seed}
}

# Custom When Code - when the signal reaches the specified state, call the function
proc loadWhen {} {
    global handResolved
    when {/top/resolved == 1} {
        # The following construct keeps ModelSim/Tcl from echoing '1' to the transcript
        # There is probably a better way...
        # In a Tcl procedure: "The return value for the {procedure} is the value 
        # returned by the last command in {the procedure's} body"
        if {[set handResolved 1] == 1} {}
    }
}

# Add a line to the status window
proc addLine {a} {
    global statusLine
    
    $statusLine insert 1.0 "$a\n"
}

# Clear the lines of the transcript
proc clearLines {} {
    global statusLine
    
    # Delete all the text
    $statusLine delete 1.0 end
}

proc setBreak {} {
    global breakResolver

    puts "breakResolver is $breakResolver"
    if {$breakResolver == 1} {
        bp resolver.v 63
    } else {
        bd resolver.v 63
    }
}

proc setCheat {} {
    global cheat

    if {$cheat == 1} {
        addLine "Sorry, the cheat isn't working.  You'll have to play fair."
        force /top/cheat 1
    } else {
        force /top/cheat 0
    }
}

proc dialog {w title text bitmap default args} {

    toplevel $w -class Dialog
    wm title $w $title
    wm iconname $w Dialog
    frame $w.top -relief raised -bd 1
    pack $w.top -side top -fill both
    frame $w.bot -relief raised -bd 1
    pack $w.bot -side bottom -fill both

    message $w.top.msg -width 3i -text $text
    pack $w.top.msg -side right -expand 1 -fill both -padx 3m -pady 3m
    if {$bitmap != ""} {
        label $w.top.bitmap -bitmap $bitmap
        pack $w.top.bitmap -side left -padx 3m -pady 3m
    }

    set i 0
    foreach but $args {
        button $w.bot.button$i -text $but -command "dialogPush $w $i"
        if {$i == $default} {
            frame $w.bot.default -relief sunken -bd 1
            raise $w.bot.button$i
            pack $w.bot.default -side left -expand 1 -padx 3m -pady 2m
            pack $w.bot.button$i -in $w.bot.default -side left -padx 2m -pady 2m -ipadx 2m -ipady 1m
        } else {
            pack $w.bot.button$i -side left -expand 1 -padx 3m -pady 3m -ipadx 2m -pady 1m
        }   
        incr i
    }
}

proc dialogPush {w val} {
    if {$val == 0} {destroy $w}
}

# Display the Help message
proc displayHelp {} {
    puts "Foo"
    dialog .a {Help} "MTI Video Poker\n\nThis application simulates a \"Jacks or Better\" Video Poker Game.\nTo Play:\n\t1) Press Deal.\n\t2) Select the cards to keep.\n\t3) Press Draw\n\t4) Repeat\n\nPayout Schedule:\n\tPair (Jacks or Better) \t-> 1:1\n\tTwo Pair \t\t\t-> 2:1\n\tThree of a Kind \t\t-> 3:1\n\tStraight \t\t\t-> 4:1\n\tFlush \t\t\t-> 6:1\n\tFull House \t\t-> 9:1\n\tFour of a Kind \t\t-> 25:1\n\tStraight Flush \t\t-> 50:1\n\tRoyal Straight Flush \t-> 800:1" {} -1 OK
#    dialog .a {Help} "MTI" {} -1 OK
    puts "Goo"
}
# Display the About message
proc displayAbout {} {
    global appVersion
    dialog .a {About} "MTI Video Poker - v${appVersion}\nCopyright - 2005" {} -1 OK
}

# Restart the simulation
proc restartSim {} {
    global gameState bankroll betsize statusLine

    restart -f
    displayCard 0 "a" "back"
    displayCard 1 "a" "back"
    displayCard 2 "a" "back"
    displayCard 3 "a" "back"
    displayCard 4 "a" "back"

    set gameState 0
    set bankroll 1000
    set betsize 20
    clearLines
    addLine "Simulation Restarted"
    addLine "Welcome back to the Lucky Rhino Casino\!"

}
# Hand is complete, resolve the change to bankroll and update the status
proc statusHand {} {
    global bankroll betsize amountbet payout gotRand
    global nohandCom pairCom twopairCom threeofakindCom straightCom flushCom fullhouseCom fourofakindCom straightflushCom royalflushCom bankrollCom

    # Cheater check
    if {$amountbet != $betsize} {
        addLine "Bet changed during hand. \$20 cheater tax applied."
        set bankroll [expr $bankroll - 20]
    } else {
        set v [examine -radix binary /top/value]
        switch $v {
            0000 { 
                set win [expr $amountbet * -1]
                #set bankroll [expr $bankroll + $win]
                set a $nohandCom
            }
            0001 { 
                set win [expr $amountbet * [lindex $payout 1]]
                set bankroll [expr $bankroll + $win]
                set a $pairCom
            }
            0010 { 
                set win [expr $amountbet * [lindex $payout 2]]
                set bankroll [expr $bankroll + $win]
                set a $twopairCom
            }
            0011 { 
                set win [expr $amountbet * [lindex $payout 3]]
                set bankroll [expr $bankroll + $win]
                set a $threeofakindCom
            }
            0100 { 
                set win [expr $amountbet * [lindex $payout 4]]
                set bankroll [expr $bankroll + $win]
                set a $straightCom
            }
            0101 { 
                set win [expr $amountbet * [lindex $payout 5]]
                set bankroll [expr $bankroll + $win]
                set a $flushCom
            }
            0110 { 
                set win [expr $amountbet * [lindex $payout 6]]
                set bankroll [expr $bankroll + $win]
                set a $fullhouseCom
            }
            0111 { 
                set win [expr $amountbet * [lindex $payout 7]]
                set bankroll [expr $bankroll + $win]
                set a $fourofakindCom
            }
            1000 { 
                set win [expr $amountbet * [lindex $payout 8]]
                set bankroll [expr $bankroll + $win]
                set a $straightflushCom
            }
            1001 { 
                set win [expr $amountbet * [lindex $payout 9]]
                set bankroll [expr $bankroll + $win]
                set a $royalflushCom
            }
            default {puts "ERROR: Unrecognized hand value."}
        }
        # Modify the bankroll
        if {$win < 0} {
            addLine "Player loses \$${amountbet}. "
        } else {
            if {$win > 0} {
                addLine "Player wins \$${win}."
            } else {
                # No bet, poke the player
                addLine "Loitering fee: \$5."
                set bankroll [expr $bankroll - 5]
            }
        }
        if {$gotRand} {
            set comment [lindex $a [expr int(rand()*[llength $a])]]
        } else {
            set comment ""
        }
        addLine "${comment}"
    }
    
    # Check to be sure player still has money
    if {$bankroll <= 0} {
        if {$gotRand} {
            set comment [lindex $bankrollCom [expr int(rand()*[llength $a])]]
        } else {
            set comment [lindex $a 0]
        }
        set bankroll 1000
        set betsize 20
        addLine "You are busted\!  But, ${comment}  Bankroll is now \$$bankroll."
    }
}

# Display a card at the given spot with a given rank/suit
proc displayCard {posn rank suit} {
    global globalWin display dealt

    #set button [$globalWin.f subwidget frame]
    set button $globalWin.f

    switch $posn {
        0 {append button .c1}
        1 {append button .c2}
        2 {append button .c3}
        3 {append button .c4}
        4 {append button .c5}
        default {puts "Illegal posn $posn passed to displayCard."}
    }

    if {$suit == "nocard"} {
        $button configure -image nocard
    } elseif {$suit == "back"} {
        $button configure -image backcard
    } else {
        $button configure -image cards(${rank},${suit})
    }
    set display [lreplace $display $posn $posn [list $rank $suit]]
}

# Since the rank comes in as a 4-bit value, translate to an index
proc xlateRank r {
    switch $r {
        0001 {set r1 0}
        0010 {set r1 1}
        0011 {set r1 2}
        0100 {set r1 3}
        0101 {set r1 4}
        0110 {set r1 5}
        0111 {set r1 6}
        1000 {set r1 7}
        1001 {set r1 8}
        1010 {set r1 9}
        1011 {set r1 10}
        1100 {set r1 11}
        1101 {set r1 12}
        default {set r1 0; puts "ERROR: Unexpected value for card rank: $r"}
    }
    return $r1
}

# Since the suit comes in as a 2-bit value, translate to an index
proc xlateSuit s {
    
    switch $s {
        00 {set s1 0}
        01 {set s1 1}
        10 {set s1 2}
        11 {set s1 3}
        default {set s1 0; puts "ERROR: Unexpected value for card suit: $s"}
    }
    return $s1
}

# Determine from the simulation the card for the particular position
proc getCard c {
    global allSuit allRank
    switch $c {
        0 {set r [examine -radix binary /top/rank0]; set s [examine -radix binary /top/suit0]}
        1 {set r [examine -radix binary /top/rank1]; set s [examine -radix binary /top/suit1]}
        2 {set r [examine -radix binary /top/rank2]; set s [examine -radix binary /top/suit2]}
        3 {set r [examine -radix binary /top/rank3]; set s [examine -radix binary /top/suit3]}
        4 {set r [examine -radix binary /top/rank4]; set s [examine -radix binary /top/suit4]}
        default {puts "ERROR: Bad Card Position: $c"}
    }
    set r1 [xlateRank $r]
    set s1 [xlateSuit $s]
    displayCard $c [lindex $allRank $r1] [lindex $allSuit $s1]
}

# GUI Deal Pushed - toggle the button states, capture the amountbet,
# run the simulation, get and display the cards, change state
proc pushPokerDeal {} {
    global gameState display dealt globalWin bankroll betsize amountbet
    
    if {$gameState == 0} {
        # Activate Draw button, deactivate Deal button
          $globalWin.c.p.b1 configure -state disabled
          $globalWin.c.p.b2 configure -state normal

        set amountbet $betsize
        if {$amountbet > $bankroll} {
            addLine "Request for credit denied!  Does this look like a bank?!?"
            set amountbet $bankroll
            set betsize   $bankroll
        }

        # Don't forget to deduct the bet from the bankroll
        set bankroll [expr $bankroll - $amountbet]
        
        #addLine "Dealing..."
        displayCard 0 "a" "back"
        displayCard 1 "a" "back"
        displayCard 2 "a" "back"
        displayCard 3 "a" "back"
        displayCard 4 "a" "back"
        update idletasks

        # Delay for effect
        after 300
        update idletasks

        force /top/GUIdeal 1
        run 900
        force /top/GUIdeal 0
        run 100
        foreach i {0 1 2 3 4} {
            getCard $i
            # Delay for effect
            after 200
            update idletasks
        }

        set dealt $display
        set gameState 1
    }
}

# GUI Draw Pushed - toggle the button states, tell the simulation
# which cards to replace, run the simulation, change state
proc pushPokerDraw {} {
    global gameState display dealt globalWin handResolved defbg

    set t {}

    if {$gameState == 1} {
        # Deactivate Draw button, Activate Deal button
        $globalWin.c.p.b2 configure -state disabled
        $globalWin.c.p.b1 configure -state normal

        #addLine "Drawing..."
        # Figure out which cards need to be replaced and do so
        foreach i {0 1 2 3 4} {
            set tmpi [expr $i + 1]
            set path "${globalWin}.f.c${tmpi}"
            set bg [lindex [$path configure -background] 4]
            if {$bg == $defbg} {
                force /top/discard${i} 1
                set t [lappend t $i]
            }
        }

        # Now, flip the cards that are discards over
        foreach i $t {
            displayCard $i "a" "back"
        }

        # Now advance simulation
        force /top/GUIdraw 1
        run 900
        force /top/discard0 0
        force /top/discard1 0
        force /top/discard2 0
        force /top/discard3 0
        force /top/discard4 0
        force /top/GUIdraw 0
        run 100

        # Delay for effect
        after 750
        update idletasks

        foreach i $t {
            getCard $i
            # Delay for effect
            after 300
            update idletasks
        }
        # Reset variables and background
        set gameState 0
        foreach i {0 1 2 3 4} {
            set tmpi [expr $i + 1]
            set path "${globalWin}.f.c${tmpi}"
            $path configure -background $defbg
        }
        if {$handResolved} {statusHand; set handResolved 0}
        # Re-Randomize
        setRand
    }
}

# When the card is pressed (it's actually a Tcl button, of course),
# toggle the card between highlighted and not
proc pushCard {a} {
    global gameState display dealt globalWin defbg

    if {$gameState == 1} {
        # Toggle card background to indicate whether to keep it
        incr a
        set path "${globalWin}.f.c${a}"
        set bg [lindex [$path configure -background] 4]
        if {$bg == $defbg} {
            $path configure -background green
        } else {
            $path configure -background $defbg
        }
    }
}

# Create the GUI for the game
proc Create_UI win {
    global bankroll betsize game gameFelt statusLine defbg
    global allRank breakResolver cheat

    # Some menus...
    frame $win.mbar -relief raised -bd 2
    pack $win.mbar -side top -fill x
    menubutton $win.mbar.file -text File -underline 0 -menu $win.mbar.file.menu
    menubutton $win.mbar.sim -text Simulation -underline 0 -menu $win.mbar.sim.menu
    menubutton $win.mbar.help -text Help -underline 0 -menu $win.mbar.help.menu
    pack $win.mbar.file $win.mbar.sim -side left
    pack $win.mbar.help -side right

    menu $win.mbar.file.menu
    $win.mbar.file.menu add command -label "Restart" -command "restartSim"
    $win.mbar.file.menu add separator
    $win.mbar.file.menu add command -label "Quit" -command {destroy $globalWin}

    menu $win.mbar.sim.menu
    $win.mbar.sim.menu add command -label "Display top level in Wave Window" -command {add wave /top/* }
    $win.mbar.sim.menu add checkbutton -label "Set break in resolver.v:60" -variable breakResolver -command {setBreak}
### no cheat signal in design */
    $win.mbar.sim.menu add checkbutton -label "Auto Play" -variable auto -command {autoPlay}

    menu $win.mbar.help.menu
    $win.mbar.help.menu add command -label "Instructions" -command "displayHelp"
    $win.mbar.help.menu add command -label "About" -command displayAbout

    # First major frame - the player's hand
    label $win.flabel -text "Player's Hand:"
    pack $win.flabel -side top

    frame $win.f
    pack $win.f -side top
    set f $win.f

    button $f.c1 -relief flat -borderwidth 0 -image backcard -command {pushCard 0}
    button $f.c2 -relief flat -borderwidth 0 -image backcard -command {pushCard 1}
    button $f.c3 -relief flat -borderwidth 0 -image backcard -command {pushCard 2}
    button $f.c4 -relief flat -borderwidth 0 -image backcard -command {pushCard 3}
    button $f.c5 -relief flat -borderwidth 0 -image backcard -command {pushCard 4}
    pack $f.c1 $f.c2 $f.c3 $f.c4 $f.c5 -side left
    set defbg [lindex [$f.c1 configure -background] 4]

    # This is just a decoration added to make the GUI a little larger and more attractive.
    if {$gameFelt == 1} {
        # Intermediate frame for the felt
        frame $win.feltframe
        pack $win.feltframe -side top -expand 1 -fill x
        label $win.feltframe.felt -borderwidth 0 -image felt
        pack $win.feltframe.felt
    }
    
    # Second major frame Controls -> Poker/BlackJack
    frame $win.c
    pack $win.c -expand 1 -fill x

    label $win.c.plabel -text "Poker - Jacks or Better"
    pack $win.c.plabel -side top

    frame $win.c.p
    pack $win.c.p -side top
    set pf $win.c.p

    button $pf.b1 -text Deal -command {pushPokerDeal}
    button $pf.b2 -text Draw -command {pushPokerDraw} -state disabled
    pack $pf.b1 $pf.b2 -side left -expand 1 -fill x

    # Third major frame
    frame $win.l
    pack $win.l -expand 1 -fill x

    frame $win.l.b -relief groove -bd 2
    frame $win.l.c -relief groove -bd 2
    frame $win.l.x -relief groove -bd 2
    pack $win.l.b $win.l.c $win.l.x -side left -expand 1 -fill both

    label $win.l.b.bet -text "Bet"
    label $win.l.b.l -text "$"
    entry $win.l.b.e -width 6 -relief sunken -bd 2 -textvariable betsize -justify right
    pack $win.l.b.bet -side top
    pack $win.l.b.e $win.l.b.l -side right -expand 1 -fill x

    label $win.l.c.bankroll -text "Bankroll"
    label $win.l.c.dollar -text "$"
    label $win.l.c.cash -textvariable bankroll -relief flat -justify right
    pack $win.l.c.bankroll -side top
    pack $win.l.c.cash $win.l.c.dollar -side right -expand 1 -fill x

    button $win.l.x.exit -text "Quit" -command {destroy $globalWin}
    pack $win.l.x.exit -expand 1 -fill both

    frame $win.s -relief sunken -bd 2
    pack $win.s -side bottom -expand 1 -fill both
    text $win.s.t -relief raised -bd 2 -yscrollcommand "$win.s.s set" -height 3
    scrollbar $win.s.s -command "$win.s.t yview"
    pack $win.s.s -side right -fill y
    pack $win.s.t -side left -fill both -expand 1
    set statusLine $win.s.t

    addLine "Welcome to the Lucky Rhino Casino\!"

    # Can't resize the UI
    wm resizable $win 0 0
}

###############TCL Main################
proc Main {} {
    global card_width card_height globalWin allSuit allRank cards feltName auto
    global tcl_version gotRand

    set globalWin .game
    
    if {[winfo exists $globalWin]} {destroy $globalWin}
    toplevel $globalWin -bg white

    # Set some characteristics of the window
	wm title $globalWin "[ProductName] - Video Poker Example"
    

    # Create Card images
    foreach suit $allSuit {
        foreach rank $allRank {
            if {($suit != "nocard") && ($suit != "back")} {
                image create photo cards(${rank},${suit}) -file "Images/${rank}${suit}.gif"
            }
        }
    }

    # Other card images needed
    image create photo nocard   -file "Images/nocard.gif"
    image create photo backcard -file "Images/back.gif"
    image create photo felt -file "Images/luckyrhino.gif"

    # Set some variables
    set card_width  [image width  nocard]
    set card_height [image height nocard]
    if {$tcl_version >= 8.0} {
        set gotRand 1
    }

    if {$gotRand} {
        # Randomize - pick your favorite, each is, more or less, successively more random
        #expr srand(0)
        #expr srand([pid])
        #expr srand([expr [expr [clock clicks] % 65536] | [pid]])
        expr srand([expr [clock clicks] % 65536])
    }

    # Create the GUI
    Create_UI $globalWin
    # Start the simulation
    vsim top
    # Custom When code
    loadWhen
    # 
    setRand

    # Setup the autoPlay routine
    autoPlay
}

# Call the main proc
Main
