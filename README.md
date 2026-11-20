# El palíndromo combinatorio más largo del mundo

Demostración en Lean 4 de dos propiedades de la [obra de Pedro Poitevin](https://pedropoitevin.com/es/interactivos/palindromo/). La edición certificada comprende veinte millardos de décimas.

- [`book_is_palindrome`](Palindromo.lean) demuestra que la secuencia de letras de la obra completa, en orden de lectura, es igual a su reverso.
- [`stanzas_are_unique`](Palindromo.lean) demuestra que dos páginas distintas tienen décimas distintas, incluso después de normalizar cada verso. Los diez versos se comparan en orden, conservando sus límites.

La normalización conserva las letras del alfabeto español, convierte las mayúsculas en minúsculas y omite los espacios, la puntuación, las tildes de las vocales y la diéresis de la `ü`. La `ñ` sigue siendo una letra distinta de la `n`.

## Demostración

Los diez dígitos del número de la combinación seleccionan los versos. Las unidades eligen el primer verso, las decenas el segundo y así sucesivamente. La segunda mitad del libro recorre las combinaciones en orden inverso y presenta los versos de cada décima espejo en orden inverso al de los grupos.

Para el palíndromo, Lean comprueba los cien pares de versos. En algunas posiciones, una letra pasa de un verso al siguiente al comparar una décima con el reverso de su espejo. Esa letra es la misma para las diez alternativas de la posición. La prueba encadena estas igualdades y obtiene un espejo para cada décima, lo que implica la simetría de la obra completa.

Para la unicidad, Lean comprueba que las diez variantes de cada verso son distintas en ambas mitades. Así se puede recuperar cada dígito a partir del verso correspondiente. Además, los primeros versos de una mitad son distintos de todos los primeros versos de la otra.

## Reproducir la verificación

Con [Elan](https://github.com/leanprover/elan) y Node.js:

```sh
node verify-source.mjs
lake build --wfail
lake env leanchecker --fresh Palindromo
```

`lean-toolchain` fija la versión de Lean. El núcleo evalúa con `decide +kernel` las tres comprobaciones finitas sobre los versos, cuyo conjunto de axiomas es vacío. Los dos teoremas sobre la obra completa dependen únicamente de `propext`, el axioma de extensionalidad proposicional. La compilación comprueba esas dependencias y `leanchecker --fresh` vuelve a comprobar las demostraciones en un entorno nuevo del núcleo. [Referencia de Lean sobre la validación de demostraciones](https://lean-lang.org/doc/reference/latest/ValidatingProofs/)

[`versos.js`](versos.js) contiene una copia exacta del [archivo servido por el lector](https://pedropoitevin.com/es/interactivos/palindromo-app/versos.js) el 20 de noviembre de 2026. El verificador comprueba su SHA-256 y que [los datos de Lean](Palindromo/Versos.lean) reproducen sus cien pares, carácter por carácter, en el mismo orden. Para comparar también con el archivo servido en el momento de la verificación:

```sh
curl -fLsS https://pedropoitevin.com/es/interactivos/palindromo-app/versos.js -o /tmp/palindromo-versos-publicados.js
node verify-source.mjs /tmp/palindromo-versos-publicados.js
```

El [código del lector](https://pedropoitevin.com/es/interactivos/palindromo-app/libro.js) usado para cotejar el orden de lectura tenía el SHA-256 `fcafcc1a31e3f3a3d60a45180c918a87b19bfcc7f4d051f9d1aec6536a570b0d`.
