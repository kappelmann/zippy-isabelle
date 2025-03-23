# Zippy - Generic White-Box Proof Search with Zippers

The supplementary material for the submission
"Zippy - Generic White-Box Proof Search with Zippers",
The International Conference on Interactive Theorem Proving, ITP 2025.

## Requirements

- Isabelle2025 (March 2025) release candidate
  - At the time of submission (23 March, 2025), obtainable from the official website: https://isabelle.in.tum.de
- AFP (March 2025) release candidate
  - At the time of submission (23 March, 2025), obtainable from the official website: https://www.isa-afp.org/download/
  - You have to add the AFP to Isabelle as a component. Instructions are here: https://www.isa-afp.org/help/

## Connections Paper <--> Formalisation

- All links and explanations are given in `Zippy/Zippy_Paper.thy`. You can CTRL+click on each referenced ressource.

## Run (interactive)

1. Navigate into the root of this folder.
2. Open JEdit: `<path_to_isabelle>/bin/isabelle jedit -l HOL -d .`
  - Building HOL might take a while.
3. Open `Zippy_Paper.thy` and explore
  - Building `Zippy_Prover_Instances.thy` might take a while due some slowness in Poly/ML's compiler that we have to investigate in the future.
    You can see the progress bars by opening the `Theories` panel on the very right of JEdit.

Note: If your computer is struggling, you can first build the `Zippy` session (see below)
and then execute above command using the `-l Zippy` flag.
This way, you can navigate the files without having to dynamically load the ML code.

## Build (non-interactive)

Navigate into the root of this folder.
Then build the Zippy code: `<path_to_isabelle>/bin/isabelle build -vbd . Zippy`
