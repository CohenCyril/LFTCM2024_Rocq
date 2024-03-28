# LFTCM2024 Rocq tutorial and practice

This repository provides the supporting material for the Coq/Rocq sessions at the venue
[Lean For The Curious Mathematician 2024 at CIRM](https://conferences.cirm-math.fr/2970.html).

We provide three methods to explore the contents interactively and give a short desciption of the files.

## Usage

### Remote use: codespaces

1. Create a [New Codespace from this repository](https://github.com/codespaces/new?hide_repo_select=true&ref=main&repo=767514192&skip_quickstart=true).
2. Wait until the Codespace launches
3. Click on one of the files and wait a few seconds
4. In case of error press `F1` and type `> Coq LSP: Restart the Coq Language Server`

### Local installation: clone & vscode (does not work with M2 mac)

1. Clone the repository using `git clone https://github.com/CohenCyril/LFTCM2024_Rocq.git`
2. Change directory to it `cd LFTCM2024_Rocq`
3. Launch vscode using `code .`
4. If asked, click "Install Dev Containers".
5. Confirm "Reopen in container" or press `F1` and type `> Reopen in container`
6. Click on one of the files and wait a few seconds
7. In case of error press `F1` and type `> Coq LSP: Restart the Coq Language Server`

### Global system installation: opam

  1. Install [opam](https://opam.ocaml.org/doc/Install.html) and configure the [coq opam repository](https://coq.inria.fr/opam-using.html#coq-packages)
  2. Clone and install the dependencies of the project
  ```shell
  git clone https://github.com/CohenCyril/LFTCM2024_Rocq.git
  cd LFTCM2024_Rocq
  opam install . --deps-only # to install dependencies
  ```
  3. run vscode `code .` and install the following extensions in your workspace:
     - coq-lsp
     - errorlens

## Contents

### Tutorial session

The files [kerjean_slides.pdf](kerjean_slides.pdf) provides an introduction to Rocq and mathcomp, and the file [tutorial.v](tutorial.v) gives an interactive introduction to the topic.

### Practice session

The file [practice.v](practice.v) contains exercises for you to try it out.
Even if the [solutions are here](solutions.v) do not look at them 😉.
