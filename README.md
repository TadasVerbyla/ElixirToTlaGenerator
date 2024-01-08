# ElixirToTlaGenerator

Šis projektas yra kursiniame darbe "Formalus Elixir standartinės bibliotekos verifikavimas TLA+ kalba" aprašomo Elixir kodo į TLA+ generatorius. 

## Naudojimas
1. Pasirenkamas **.ex** failas, aprašantis modulį su Elixir funkcija, kuriai pridėtas
specialus atributas **@tlagen_function :[function_name]**.

2. Sukompiliuojamas generatoriaus projektas su **iex -S mix** komanda

3. Iškviečiama generatoriaus funkcija **ElixirToTlaGenerator.generate(directory)**, su parametru **directory**, kuris nurodo kelią iki generavimui naudojamo **.ex** failo. 

4. Sugeneruotas **.tla** failas randamas **generated_tla** direktorijoje.

## Projekto esminė struktūra

### elixir_files

Šiame aplanke laikomi įvairūs **.ex** failai, kurie buvo naudojami testiniams tikslams generuojant specifikacijas. Čia laikomas **map_range.ex** failas naudotas tyrime aprašytos **map_range** funkcijos specifikacijos generavimui. 

### generated_tla

Šiame aplanke įrašomos sugeneruotos **.tla** formato specifikacijos. 

### lib moduliai:

1. **extract_ast.ex** 
Modulis, naudojamas išgauti supaprastintą AST medį pažymėtai funkcijai iš pateikiamo .ex failo. 

2. **simplified_ast_to_tla.ex**
Modulis, kuris apdoroja supaprastintą AST medį iš jo išgaudamas esminius TLA+ specifikacijos elementus. 

3. **tla_maker.ex**
Modulis, kuris gautus esminius TLA+ elementus sujungia į vientisą specifikacijos tekstą ir jį išsaugo kaip **.tla** failą. 

4.  **snake_to_camel.ex**
Pagalbinis modulis, kuris "snake_case" formato tekstą pakeičia į "CamelCase"

5. **elixir_to_tla_generator.ex**
Pagrindinis modulis, kuris kviečia kitų modulių funkcijas specifikacijos sugeneravimui. 

### tla_testing

Aplankas, kuriame sudėtos ranka apdorotos TLA+ specifikacijos po jų sugeneravimo. Šiuo metu čia laikomos dvi skirtingos **map_range** specifikacijos versijos, skirtingai implementuojančios funkcijos kintamojo specifikavimą. Šių specifikacijų veikimas ištestuotas naudojantis **Visual Studio Code** modulio **TLA+ language support** model checker įrankiu. 