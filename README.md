# ElixirToTlaGenerator

Šis projektas yra bakalauriniame darbe "Formalus Elixir standartinės bibliotekos verifikavimas TLA+ kalba" aprašomo Elixir kodo į TLA+ generatorius. 

## Naudojimas
1. Pasirenkamas **.ex** failas, aprašantis modulį su Elixir funkcija, kuriai pridėtas
specialus atributas **@tlagen_function :[function_name]**. Šiuo metu išbandytas generavimas Fibonacci.ex failui, randamam elixir_filed direktorijoje. 

2. Sukompiliuojamas generatoriaus projektas su **iex -S mix** komanda

3. Iškviečiama generatoriaus funkcija **ElixirToTlaGenerator.generate(path)**, su parametru **path**, kuris nurodo kelią iki generavimui naudojamo **.ex** failo. 

4. Sugeneruotas **.tla** failas randamas **generated_tla** direktorijoje.

## Projekto esminė struktūra

### elixir_files

Šiame aplanke laikomi įvairūs **.ex** failai, kurie buvo naudojami testiniams tikslams generuojant specifikacijas. Čia laikomas **fibonacci.ex** failas naudotas tyrime aprašytos Fibonači funkcijos specifikacijos generavimui. 

### generated_tla

Šiame aplanke įrašomos sugeneruotos **.tla** formato specifikacijos. 

### lib moduliai:

1. **extract_ast.ex** 
Modulis, naudojamas išgauti AST medį pažymėtai funkcijai iš pateikiamo .ex failo. 

3. **ast_parser.ex**
Modulis, kuris iš **extract_ast.ex** gautą AST struktūrą transformuoja, išgaudamas esminę informaciją TLA+ specifikacijos sudarymui.

5. **tla_ast_maker**
Modulis, kuris pagal gautą esminę informaciją iš **ast_parser** sudaro TLA+ AST struktūrą ir naudojant **ast.ex** funkciją **to_tla** išsaugo ją kaip **.tla** specifikacijos failą. 

6. **ast.ex**
Modulis, nusakantis TLA+ AST struktūrą bei funkcijas jai konvertuoti į TLA+ specifikaciją. 

7.  **string.ex**
Pagalbinis modulis, kuriame yra funkcija **snalke_to_camel**, kuri "snake_case" formato tekstą pakeičia į "CamelCase"

8. **elixir_to_tla_generator.ex**
Pagrindinis modulis, kuris kviečia kitų modulių funkcijas specifikacijos sugeneravimui. 

### manual_tla

Aplankas, kuriame laikomi ranka aprašyti prototipai sukurto Elixir funkcijų specifikavimo šablono. Visuose modeliuota Fibonači funkcija. 

### test

Aplankas skirtas testavimui parašytų elixir funkcijų. Testuojama buvo specifiniais atvejais kai buvo naudojama test driven development strategija. 

### tla_testing

Aplankas, kuriame sudėtos ranka apdorotos TLA+ specifikacijos po jų sugeneravimo. Šiuo metu čia laikomas aplankas su senomis specifikacijomis, kurtomis kursinio darbo metu, bei naujas aplankas Fibonači funkcijos specifikacijai ir jos konfigūraciniam failui, kuris buvo aprašytas ranka siekiant ištestuoti specifinių Fibonači skaičių radimą nurodant konstantai N specifinę įvesties reikšmę. Kol kas naudojant TLC įrankį specifikacija sutinką klaidą paskutiniame žingsnyje, tad galima matyti pilną būsenų perėjimų išrašą bei patikrinti rasto Fibonači skaičiaus teisingumą pagal paskutinio žingsnio return reikšmę.  