# Analysis lectures material

This repository contains course material for the [Analysis](https://ocasys.rug.nl/current/catalog/course/WBMA012-05) course at the University of Groningen.

The lectures material can be accessed at [mseri.me/analysis_rug](https://mseri.me/analysis_rug).
This contains both the syllabus, including tutorial exercises, and navigable slides for the lectures.

The `theories` folder contains the content of the lectures, separated in thematic sections, formalized in Waterproof (WIP).
The `exercises` folder contains the barebone homework exercises in Waterproof format, ready to be formalized.

## Waterproof

Waterproof is educational software designed to help students with learning the skill of proving mathematical statements. It uses a natural syntax that makes the exercise very close to what one would write on paper. The software checks the correctness of the proofs and provides feedback to the user.
See [here](https://impermeable.github.io/) for more information.

Part of the material, for instance the tutorial, is based on the one available from the [waterproof-exercise-sheets](https://github.com/impermeable/waterproof-exercise-sheets) and [introduction-to-proofs](https://github.com/impermeable/introduction-to-proof-sheets) repositories.

## Tutorial

This repository also contains an edited version of the Waterproof tutorial, `tutorial.mv`, which explains how to use Waterproof's custom proof language with very simple examples.

## Note

Currently, some material requires an extended Waterproof version, which can be found on [this branch in my fork](https://github.com/mseri/coq-waterproof/tree/rug-analysis-9.1).
Once this is integrated in Waterproof, or appropriately moved in this repository, everything below should work. At the moment it requires manual installs that I am happy to explain individually but I will not detail here.

# Quickstart

## Quickstart (in browser)

You can try out these exercises in Github codespaces, which is a service that offers a free number of hours per month. To open the exercises in Github codespaces, you can click on the following link.

[![Open in GitHub Codespaces](https://github.com/codespaces/badge.svg)](https://codespaces.new/mseri/waterproof-analysis?quickstart=1)

This link should give you the option of continuing in an earlier opened workspace, if you have opened these exercises in codespaces before.

Tip: make sure you close your Github codespace environment after using it.

## Quickstart (local)

1. Download the [exercises](https://github.com/mseri/waterproof-analysis/archive/refs/heads/main.zip) and unzip them in a new folder.
2. Go to [https://vscode.dev?enable-coi](https://vscode.dev?enable-coi) using Google Chrome or Chromium.
3. Go to extensions (Ctrl+Shift+x or Cmd+Shift+x), search for Waterproof and install it (choose to "trust" the extension).
4. Go to files (Ctrl+Shift+e or Cmd+Shift+x), click "Open folder" and choose the folder from step 1 (choose to "trust" the folder).
5. If the browser asks for permission to view or edit files in that location,
allow this.
6. Open the relevant `.mv` file, for instance `tutorial.mv`.
7. If everything installed correctly, you should see a "Goal" window on the right, which shows what is left to prove when you click in the text of proofs.
