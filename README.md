# Switched systems in Coq

## Overview

Code for the paper "Switched Systems in Coq for Modeling Periodic Controllers".

Switched systems (i.e. systems switching between a finite set of continuous systems) are an important subclass of hybrid systems, expressive enough for a wide range of systems. This paper introduces the first formalization of switched systems in the proof assistant Coq – a step towards building verified controllers in Coq. We define switched systems and the trajectories they induce while prioritizing verification. Moreover, we offer a specialized formalization for the efficient modeling of periodic controllers. Finally, we illustrate the formalization by modeling and verifying an air filter.

Link: [https://link.springer.com/chapter/10.1007/978-3-031-77019-7_20](https://link.springer.com/chapter/10.1007/978-3-031-77019-7_20)

## Usage

To compile the project, use "build.ps1". Tested with Coq Platform 2023.11.0. Main file of the project is "switched_systems.v".
