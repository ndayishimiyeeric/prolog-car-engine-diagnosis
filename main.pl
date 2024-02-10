% =================================================================== %
% 		    		          Car Engine Diagnosis					                %
%									-- Ndayishimiye Eric -- Paris 2024 --               %                %
% =================================================================== %

% ----- Abducible Predicates ----- %
abducible(engine_layout(_,_)).    %%% engine_layout(Engine, Layout)
abducible(engine_configuration(_,_)).   %%% engine_configuration(Engine, Configuration)
abducible(engine_disease(_,_)).   %%% engine_disease(Engine, Disease)
abducible(fuel_type(_,_)).    %%% fuel_type(Engine, Fuel)

% ----- Background Knowledge ----- %

% observables %

% ------------------- Characteristics of an engine ------------------ %

cylinders(Engine, Cylinders):- engine_configuration(Engine, Cylinders), petrol(Engine), inline(Engine).
cylinders(Engine, Cylinders):- engine_configuration(Engine, Cylinders), petrol(Engine), flat(Engine).
cylinders(Engine, Cylinders):- engine_configuration(Engine, Cylinders), petrol(Engine), v_engine(Engine).
cylinders(Engine, Cylinders):- engine_configuration(Engine, Cylinders), diesel(Engine), inline(Engine).
cylinders(Engine, Cylinders):- engine_configuration(Engine, Cylinders), diesel(Engine), flat(Engine).
cylinders(Engine, Cylinders):- engine_configuration(Engine, Cylinders), diesel(Engine), v_engine(Engine).

fuel(Engine, Fuel):- fuel_type(Engine, Fuel), twin_cylinder(Engine), inline(Engine).
fuel(Engine, Fuel):- fuel_type(Engine, Fuel), twin_cylinder(Engine), flat(Engine).
fuel(Engine, Fuel):- fuel_type(Engine, Fuel), twin_cylinder(Engine), v_engine(Engine).
fuel(Engine, Fuel):- fuel_type(Engine, Fuel), three_cylinder(Engine), inline(Engine).
fuel(Engine, Fuel):- fuel_type(Engine, Fuel), three_cylinder(Engine), flat(Engine).
fuel(Engine, Fuel):- fuel_type(Engine, Fuel), three_cylinder(Engine), v_engine(Engine).
fuel(Engine, Fuel):- fuel_type(Engine, Fuel), four_cylinder(Engine), inline(Engine).
fuel(Engine, Fuel):- fuel_type(Engine, Fuel), four_cylinder(Engine), flat(Engine).
fuel(Engine, Fuel):- fuel_type(Engine, Fuel), four_cylinder(Engine), v_engine(Engine).
fuel(Engine, Fuel):- fuel_type(Engine, Fuel), five_cylinder(Engine), inline(Engine).
fuel(Engine, Fuel):- fuel_type(Engine, Fuel), five_cylinder(Engine), flat(Engine).
fuel(Engine, Fuel):- fuel_type(Engine, Fuel), five_cylinder(Engine), v_engine(Engine).
fuel(Engine, Fuel):- fuel_type(Engine, Fuel), six_cylinder(Engine), inline(Engine).
fuel(Engine, Fuel):- fuel_type(Engine, Fuel), six_cylinder(Engine), flat(Engine).
fuel(Engine, Fuel):- fuel_type(Engine, Fuel), six_cylinder(Engine), v_engine(Engine).
fuel(Engine, Fuel):- fuel_type(Engine, Fuel), eight_cylinder(Engine), inline(Engine).
fuel(Engine, Fuel):- fuel_type(Engine, Fuel), eight_cylinder(Engine), flat(Engine).
fuel(Engine, Fuel):- fuel_type(Engine, Fuel), eight_cylinder(Engine), v_engine(Engine).
fuel(Engine, Fuel):- fuel_type(Engine, Fuel), ten_cylinder(Engine), inline(Engine).
fuel(Engine, Fuel):- fuel_type(Engine, Fuel), ten_cylinder(Engine), flat(Engine).
fuel(Engine, Fuel):- fuel_type(Engine, Fuel), ten_cylinder(Engine), v_engine(Engine).
fuel(Engine, Fuel):- fuel_type(Engine, Fuel), twelve_cylinder(Engine), inline(Engine).
fuel(Engine, Fuel):- fuel_type(Engine, Fuel), twelve_cylinder(Engine), flat(Engine).
fuel(Engine, Fuel):- fuel_type(Engine, Fuel), twelve_cylinder(Engine), v_engine(Engine).
fuel(Engine, Fuel):- fuel_type(Engine, Fuel), no_cylinder(Engine), inline(Engine).

layout(Engine, Layout):- engine_layout(Engine, Layout), alternative(Engine), no_cylinder(Engine).
layout(Engine, Layout):- engine_layout(Engine, Layout), diesel(Engine), twin_cylinder(Engine).
layout(Engine, Layout):- engine_layout(Engine, Layout), diesel(Engine), three_cylinder(Engine).
layout(Engine, Layout):- engine_layout(Engine, Layout), diesel(Engine), four_cylinder(Engine).
layout(Engine, Layout):- engine_layout(Engine, Layout), diesel(Engine), five_cylinder(Engine).
layout(Engine, Layout):- engine_layout(Engine, Layout), diesel(Engine), six_cylinder(Engine).
layout(Engine, Layout):- engine_layout(Engine, Layout), diesel(Engine), eight_cylinder(Engine).
layout(Engine, Layout):- engine_layout(Engine, Layout), diesel(Engine), ten_cylinder(Engine).
layout(Engine, Layout):- engine_layout(Engine, Layout), diesel(Engine), twelve_cylinder(Engine).
layout(Engine, Layout):- engine_layout(Engine, Layout), petrol(Engine), twin_cylinder(Engine).
layout(Engine, Layout):- engine_layout(Engine, Layout), petrol(Engine), three_cylinder(Engine).
layout(Engine, Layout):- engine_layout(Engine, Layout), petrol(Engine), four_cylinder(Engine).
layout(Engine, Layout):- engine_layout(Engine, Layout), petrol(Engine), five_cylinder(Engine).
layout(Engine, Layout):- engine_layout(Engine, Layout), petrol(Engine), six_cylinder(Engine).
layout(Engine, Layout):- engine_layout(Engine, Layout), petrol(Engine), eight_cylinder(Engine).
layout(Engine, Layout):- engine_layout(Engine, Layout), petrol(Engine), ten_cylinder(Engine).
layout(Engine, Layout):- engine_layout(Engine, Layout), petrol(Engine), twelve_cylinder(Engine).

% --------------------- Symptoms of engine diseases ------------------ %

white_smoke(Engine):- engine_disease(Engine, blow_head_gasket).
blue_smoke(Engine):- engine_disease(Engine, piston_ring_wear).

coolant_loss(Engine):- engine_disease(Engine, blow_head_gasket).
coolant_smell(Engine):- engine_disease(Engine, coolant_leaks).
coolant_level_loss(Engine):- engine_disease(Engine, coolant_leaks).

overheating(Engine):- engine_disease(Engine, blow_head_gasket).
overheating(Engine):- engine_disease(Engine, oil_pump_failure).

stalling(Engine):- engine_disease(Engine, timing_belt_failure).
stalling(Engine):- engine_disease(Engine, vvt_system_failure).
stalling(Engine):- engine_disease(Engine, crankshaft_position_sensor_failure).

misfire(Engine):- engine_disease(Engine, timing_belt_failure).
misfire(Engine):- engine_disease(Engine, cylinder_misfire).
misfire(Engine):- engine_disease(Engine, intake_manifold_gasket_leak).
misfire(Engine):- engine_disease(Engine, vvt_system_failure).
misfire(Engine):- engine_disease(Engine, crankshaft_position_sensor_failure).
misfire(Engine):- engine_disease(Engine, clogged_fuel_injectors).
misfire(Engine):- engine_disease(Engine, ignition_system_issues).

vibrations(Engine):- engine_disease(Engine, timing_belt_failure).
vibrations(Engine):- engine_disease(Engine, cylinder_misfire).
vibrations(Engine):- engine_disease(Engine, vvt_system_failure).
vibrations(Engine):- engine_disease(Engine, crankshaft_position_sensor_failure).
vibrations(Engine):- engine_disease(Engine, clogged_fuel_injectors).
vibrations(Engine):- engine_disease(Engine, ignition_system_issues).

oil_spots(Engine):- engine_disease(Engine, oil_leaks).
oil_spots(Engine):- engine_disease(Engine, valve_cover_gasket_leak).
oil_smell(Engine):- engine_disease(Engine, oil_leaks).
oil_smell(Engine):- engine_disease(Engine, valve_cover_gasket_leak).
oil_smell(Engine):- engine_disease(Engine, oil_pump_failure).
oil_level_loss(Engine):- engine_disease(Engine, oil_leaks).
oil_level_loss(Engine):- engine_disease(Engine, valve_cover_gasket_leak).
oil_level_loss(Engine):- engine_disease(Engine, piston_ring_wear).
oil_pressure_loss(Engine):- engine_disease(Engine, oil_pump_failure).

noise(Engine):- engine_disease(Engine, exhaust_manifold_cracks).
noise(Engine):- engine_disease(Engine, intake_manifold_gasket_leak).
noise(Engine):- engine_disease(Engine, oil_pump_failure).

power_loss(Engine):- engine_disease(Engine, cylinder_misfire).
power_loss(Engine):- engine_disease(Engine, exhaust_manifold_cracks).
power_loss(Engine):- engine_disease(Engine, piston_ring_wear).
power_loss(Engine):- engine_disease(Engine, intake_manifold_gasket_leak).
power_loss(Engine):- engine_disease(Engine, vvt_system_failure).
power_loss(Engine):- engine_disease(Engine, clogged_fuel_injectors).
power_loss(Engine):- engine_disease(Engine, battery_degradation).

vacuum_leak(Engine):- engine_disease(Engine, intake_manifold_gasket_leak).

difficulty_starting(Engine):- engine_disease(Engine, clogged_fuel_injectors).
difficulty_starting(Engine):- engine_disease(Engine, ignition_system_issues).
difficulty_starting(Engine):- engine_disease(Engine, battery_degradation).
battery_light(Engine):- engine_disease(Engine, charging_system_failure).
slow_charging(Engine):- engine_disease(Engine, battery_degradation).
slow_charging(Engine):- engine_disease(Engine, charging_system_failure).
port_malfunction(Engine):- engine_disease(Engine, charging_system_failure).
small_driving_range(Engine):- engine_disease(Engine, battery_degradation).

% ------------------ Engine type definitions ------------------ %

% Engine Layouts
inline(Engine):- engine_layout(Engine, inline).
flat(Engine):- engine_layout(Engine, flat).
v_engine(Engine):- engine_layout(Engine, v_engine).

% Engine Configurations
no_cylinder(Engine):- engine_configuration(Engine, no_cylinder).
twin_cylinder(Engine):- engine_configuration(Engine, twin_cylinder).
three_cylinder(Engine):- engine_configuration(Engine, three_cylinder).
four_cylinder(Engine):- engine_configuration(Engine, four_cylinder).
five_cylinder(Engine):- engine_configuration(Engine, five_cylinder).
six_cylinder(Engine):- engine_configuration(Engine, six_cylinder).
eight_cylinder(Engine):- engine_configuration(Engine, eight_cylinder).
ten_cylinder(Engine):- engine_configuration(Engine, ten_cylinder).
twelve_cylinder(Engine):- engine_configuration(Engine, twelve_cylinder).

% Fuel Types
petrol(Engine):- fuel_type(Engine, petrol).
diesel(Engine):- fuel_type(Engine, diesel).
alternative(Engine):- fuel_type(Engine, alternative).


% ----------------- Integrity Constraints ---------------------- %
ic:- blue_smoke(X), white_smoke(X).

ic:- alternative(X), diesel(X).
ic:- alternative(X), petrol(X).
ic:- alternative(X), v_engine(X).
ic:- alternative(X), flat(X).
ic:- alternative(X), \+ no_cylinder(X).

ic:- engine_layout(X, Y), engine_layout(X, Z), Y \= Z.
ic:- engine_configuration(X, Y), engine_configuration(X, Z), Y \= Z.
ic:- fuel_type(X, Y), fuel_type(X, Z), Y \= Z.
ic:- engine_disease(X, Y), engine_disease(X, Z), Y \= Z.
ic:- engine_disease(X, battery_degradation), \+ alternative(X).
ic:- engine_disease(X, charging_system_failure), \+ alternative(X).
ic:- engine_disease(X, clogged_fuel_injectors), \+ alternative(X).
ic:- engine_disease(X, ignition_system_issues), \+ alternative(X).
ic:- engine_disease(X, blow_head_gasket),  alternative(X).
ic:- engine_disease(X, cylinder_misfire),  alternative(X).
ic:- engine_disease(X, piston_ring_wear),  \+ flat(X).
ic:- engine_disease(X, coolant_leaks),  \+ flat(X).
ic:- engine_disease(X, valve_cover_gasket_leak),  \+ flat(X).
ic:- engine_disease(X, exhaust_manifold_cracks),  \+ flat(X).
ic:- engine_disease(X, oil_pump_failure),  \+ v_engine(X).
ic:- engine_disease(X, vvt_system_failure),  \+ v_engine(X).
ic:- engine_disease(X, crankshaft_position_sensor_failure),  \+ v_engine(X).
ic:- engine_disease(X, intake_manifold_gasket_leak),  \+ v_engine(X).
ic:- engine_disease(X, timing_belt_failure), flat(X).
ic:- engine_disease(X, timing_belt_failure), alternative(X).
ic:- engine_disease(X, oil_leaks), alternative(X).

% ---------------- Query Exemples ----------------- %

% vacuum_leak symptom is due to only one engine disease, this query will explain the exact engine layout, and disease.
% query([vacuum_leak(engine)], (E,_,_)).

% diseases causing power loss on alternative fuel engines
% query([fuel(engine, alternative), power_loss(engine)], (E,_,_)).

% query a symptom caused by diseases of different engine types
% query([white_smoke(engine)], (E,_,_)).

% query a symptom caused by only a disease of a one specific engine type
% query([blue_smoke(engine)], (E,_,_)).

% query for an engine details layout, configuration, and fuel type
% query([cylinders(engine, twelve_cylinder), fuel(engine, petrol)], (E,_,_)).

% expanding the query to include the engine layout and a symptom
% query([cylinders(engine, twelve_cylinder), fuel(engine, petrol), layout(engine, v_engine), white_smoke(engine)], (E,_,_)).

% query with symptoms only
% query([vibrations(engine), misfire(engine), stalling(engine)], (E,_,_)).

% checking the integrity constraints
% query([oil_leaks(engine), fuel(engine, alternative)], (E,_,_)).
