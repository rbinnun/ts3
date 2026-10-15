# ts3

A runner, worked out in logic first.

The machine decides; the runner does, one thing at a time.

- **A machine** is a Mangle program (`machine.mg`). Each turn it says the one thing it `wants` done next.
- **A turn is pure logic** (`runner/step.mg`): it does the wanted thing and carries everything else into the next turn as `next_` facts.
- **Effects are simulated.** The world is facts, such as `file(Path, Content)`. Reading looks a fact up; writing replaces one.
- **The only code outside logic** (`runner/main.go`) repeats the turn until the machine wants nothing. It stops a machine that wants two things at once.

The loop can't be one Mangle program. "Do what isn't done yet" depends on its own past through negation, which Mangle rejects as unstratifiable. So a pure turn is repeated instead.

## Run it

Go 1.25 or newer:

```
./run machines/copy_notes
```

```
turn 0: wants("read notes","read_a_file","notes.txt","")
turn 1: wants("copy notes","write_a_file","copy.txt","hello")
after 2 turns:
file("copy.txt","hello")
file("notes.txt","hello")
tells("notes say: hello")
```

## Next

Real effects come later. The simulated effect rules in `runner/step.mg` get swapped for real ones; the machines and the rest of the turn stay as they are.
