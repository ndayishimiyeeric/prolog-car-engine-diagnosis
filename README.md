# prolog car engine diagnosis

In this era where automotive technology is advancing at a rapid pace, the complexity and variety of car engines have significantly increased, posing challenges in maintenance and diagnostics. The main objective of my project is to develop a system capable of accurately identifying a wide range of car engine types and their common issues. This system integrates detailed information on three engine layouts, nine configurations, and three fuel types, alongside twenty observable symptoms associated with sixteen distinct engine-related diseases. By leveraging this comprehensive knowledge base, the tool facilitates precise identification and diagnosis of engine problems, enabling users to effectively pinpoint and address specific malfunctions.

Here is a list of all the engine diseases along with their symptoms and engine types.

| **Engine Disease**                 | **Symptoms**                                                                                                   | **Applicable Engine Type**          |
| ---------------------------------- | -------------------------------------------------------------------------------------------------------------- | ----------------------------------- |
| Blown Head Gasket                  | White smoke from the exhaust, Engine overheating, Milky substance under oil cap, Loss of coolant               | Inline, Flat, V-Engine              |
| Timing Belt Failure                | Misfires or rough running, Ticking noise, Difficulty starting, Complete failure if snapped                     | Inline, V-Engine                    |
| Cylinder Misfire                   | Misfires or rough running, Loss of power, Vibrations, Check Engine light for misfires                          | All Engine Types                    |
| Oil Leaks                          | Visible oil spots/puddles, Burning oil smell, Low oil level, Wet components                                    | All Engine Types                    |
| Valve Cover Gasket Leak            | Oil leaks around valve covers, Burning oil smell, Visible oil on engine, Misfires                              | Flat (Boxer Engine)                 |
| Coolant Leak from Cylinder Head    | Low coolant level, Overheating, Milky substance in oil, White smoke from exhaust                               | Flat (Boxer Engine)                 |
| Exhaust Manifold Cracks            | Loud exhaust noise, Decreased performance, Burning smell, Check Engine light for oxygen readings               | Flat (Boxer Engine)                 |
| Piston Ring Wear                   | Blue/gray smoke from exhaust, Loss of power, Increased oil consumption, Rough running                          | Flat (Boxer Engine)                 |
| Intake Manifold Gasket Leak        | Misfires, Decreased performance, Vacuum leaks, Check Engine light for fuel mixture                             | V-Engine                            |
| Variable Valve Timing Failure      | Loss of power, Rough idling or stalling, Check Engine light for camshaft position, Decreased fuel economy      | V-Engine                            |
| Oil Pump Failure                   | Low oil pressure light, Engine knocking, Overheating, Severe damage if not addressed                           | V-Engine                            |
| Crankshaft Position Sensor Failure | Engine not starting or stalling, Loss of power, Check Engine light for crankshaft position, Erratic tachometer | V-Engine                            |
| Clogged Fuel Injectors             | Rough idling, Decreased performance, Starting difficulties, Check Engine light for fuel system                 | Alternative Fuel Engines (CNG, LPG) |
| Ignition System Issues             | Misfires during acceleration, Starting difficulties, Loss of power, Check Engine light for ignition faults     | Alternative Fuel Engines (CNG, LPG) |
| Battery Degradation (EV)           | Reduced driving range, Slow charging times, Check Battery light, Loss of power                                 | Electric Vehicle Engines            |
| Charging System Failure (EV)       | Inability to charge, Charging port malfunctions, Check Charging System light, Unable to maintain charge        | Electric Vehicle Engines            |

## Problem representation

Car engines are in a variety of categories based on the way they are installed (layout), configuration and what fuel they use, and each category has it own issues based on what makes it. We are trying to know based on what we observe (characteristics) and in case they have an issue(symptoms) what category they belong to and their corresponding diseases. To achieve this, I used four abducibles with two parameters each: engine_disease/2, engine_layout/2, engine_configuration/2, fuel_type/2 .
Remark: the no_cylinder predicate is used to model engines configurations which do not use cylinders this not just a negation as it sounds, for example electrical engines have a no_cylinder configuration. Moreover, all alternative engines are considered to have inline layouts in this project.
In a general schema, the abducible predicates are derived from 16 auxiliary predicates which in turn are derived by observable predicates.
The problem formulation here is: what is the abducible hypothesis if we have a set of observations? And before deriving our abducibles we must derive the possible auxiliary predicates, which characteristics and symptoms will derive the abducibles.

### Integrity constraints

In this problem we have different types of integrity constraints:

- Integrity constraints on observables predicates: we have mutual exclusion between predicates such as:

  `ic:- blue_smoke(Engine), white_smoke(Engine).`

  means we cannot observe that a car engine produces white smoke and blue_smoke at the same time.

- Integrity constraints on auxiliary predicates: we have mutual exclusion within predicates defining a category type.

  `ic:- alternative(Engine), petrol(Engine).`

  `ic:- alternative(Engine), diesel(Engine).`

  Means we cannot have an alternative engine using diesel or petrol.

- Integrity constraints on abducible predicates – engine_disease/2, as discussed in the table 1 there are engine diseases that are specific for a given engine type.

  `ic:- engine_disease(Engine, charging_system_failure), \+ alternative(Engine).`

  Means an engine can not have charging issues while it is not an electrical engine.

- Integrity constraints on abducible predicates – engine_layout/2, as discussed in table 2 all engine layouts are mutual exclusive, we can have only one engine layout.

  `ic:- engine_layout(X, Y), engine_layout(X, Z), Y \= Z.`

  Means we cannot have two different engine layouts at the same time.

## Experiments

- vacuum_leak symptom is due to only one engine disease, this query will explain the exact engine layout, and disease.

  `query([vacuum_leak(engine)], (E,_,_)).`

- diseases causing power loss on alternative fuel engines

  `query([fuel(engine, alternative), power_loss(engine)], (E,_,_)).`

## Running the project

### Prerequisites: [A system](https://sicstus.sics.se/eval.html)

1. Consult the abduction model “abduction.pl”.
2. Load the project theory “main.pl”.
3. Start querying.
