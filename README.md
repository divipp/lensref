
# lensref: State-based FRP framework

`lensref` is an FRP framework which is built around views of the program state. The
views can be editable or non-editable.

An editable view of the program state can be modelled by a lens whose domain is the program state.
In `lensref`s terminology such views are called **references**.
`lensref` provides combinators to create references with **bidirectional dependencies** between them which are automatically maintained as the program state evolves.

A non-editable view of the program state can be modelled by a function whose domain is the program state.
In `lensref`s terminology such views are called **state-varying values** or **read-only references**.
State-varying values form a monad.

Compared to other FRP frameworks, `lensref` has an emphasis on state-varying values rather than time-varying values.
The program state varies by time so a state-varying value is also time-varying value but the opposite direction is generally not true because the program may have the same state in different time intervals.

More documentation can be found in the `docs` directory:
[Introduction to state-based FRP (pdf)](https://github.com/divipp/lensref/blob/master/docs/Introduction.pdf)


## Status

* The interface is getting stable. The scheduling of change propagation should be rewritten.
* The documentation should be finished.
* A tutorial should be written.

## Usage

There is a demo GUI framework built on top of `lensref` in the `LensRef.Demo.SevenGUIs` module.


## Links

* [Introduction to state-based FRP (pdf)](https://github.com/divipp/lensref/blob/master/docs/Introduction.pdf)
* [Haddock documentation on HackageDB](http://hackage.haskell.org/package/lensref)
* [Wordpress blog](http://lgtk.wordpress.com/)
* [haskell.org wiki page](http://www.haskell.org/haskellwiki/LGtk)
* [GitHub repository (this page)](https://github.com/divipp/lensref)



