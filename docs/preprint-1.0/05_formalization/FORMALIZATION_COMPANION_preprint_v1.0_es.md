---
title: 'Descomposiciones en triángulos II: Documento de formalización y reproducibilidad'
author: 'Juan Pablo Traverso Gianini'
date: '20 de octubre de 2026'
---

**Documento complementario de Paper II:** *Descomposiciones en triángulos II: Absorción robusta para triángulos tipados* [1], preprint 1.0.

**Preprint 1.0 — 20 de octubre de 2026.**

**DOI:** https://doi.org/10.5281/zenodo.23502224.

## 1. Alcance validado

Se compilaron tres entradas explícitas en la campaña alineada: `PartitionedTriangleAbsorption.PaperII.Core`, `PartitionedTriangleAbsorption.PaperII.Families` y `PartitionedTriangleAbsorption.PaperII.PaperIApplications`. La unión de sus clausuras de importaciones contiene 1.510 módulos. La campaña comenzó con un directorio vacío de resultados del proyecto y compiló todos los módulos desde las fuentes; 623 se compilaron en la fase de Paper I y 887 en la fase de Paper II. Se reutilizó la caché de Mathlib fijada. Las quince consultas finales pasaron con sólo `propext`, `Classical.choice` y `Quot.sound`.

El resultado incluye certificados efectivos de existencia para las diecisiete familias con leyes de conservación. Incluye también el censo exhaustivo, el puente de representantes a la biblioteca de construcciones y el transporte al etiquetado original. En conjunto demuestran la propiedad para grafos típicos de toda familia de multiconjuntos de tamaño tres sobre cuatro etiquetas que utiliza cada etiqueta y da a cada una un compañero prohibido. El teorema final no supone un productor latino ni pertenencia al catálogo.

La campaña local terminada registra `PASS_CLEAN_ALIGNED_BUILD`; no es una reproducción independiente. La revisión v2 corrige posteriormente sólo las cabeceras de autoría y tiene estado `PASS_HEADER_ONLY_REVISION`; la revisión seleccionada v4 tiene estado `PASS_README_ONLY_REVISION` y modifica únicamente el README del archivo y su manifiesto. Se conserva cada byte del cuerpo de las pruebas. Los recibos históricos describen las fuentes anteriores a esa corrección, y la verificación reversible de la sección 5 reconstruye sus bytes exactos. No se afirma una nueva compilación Lean de las cabeceras corregidas.

## 2. Fuentes congeladas

El archivo de fuentes seleccionado es `PAPER_II_LEAN_20261020_ALIGNED_v4.zip`, en [la referencia inmutable de las fuentes](https://github.com/jtraverso/nash-williams-triangle-decompositions/blob/d6d020982ebf3f3cd8c104b6befc6c094850b3e7/archives/PAPER_II_LEAN_20261020_ALIGNED_v4.zip). Su SHA-256 es:

`677faa70a76444a000b8c2192a45d0ab0e39f8899825c004fdf6cbe52bb755cc`.

El archivo contiene 4.562 ficheros y su `SHA256SUMS.txt` comprueba 4.561 entradas. El informe conservado de la campaña, `evidence/verification.json`, tiene SHA-256:

`8b609b174b9f16086c2faf243e2cb828d34c4110f220e59556482610f519ce59`.

La herramienta exacta es `leanprover/lean4:v4.35.0-rc3`. Mathlib está fijado en `c55e6e786f49471c72fbddbec5415808896aec1e`; el archivo de dependencias y `evidence/environment.json` identifican sus paquetes auxiliares.

El predecesor limpio es `PAPER_II_LEAN_20261020_ALIGNED_v1`, SHA-256 `2ed5e683dae4ff9ab4a24187957dbd2fb3ec18d04e7236c88dd4c6c38ac079b7`. La revisión v2 añade 1.352 cabeceras de autoría ausentes, corrige 59 grafías del apellido y conserva 99 cabeceras ya correctas. Los 1.510 archivos Lean del proyecto identifican a Juan Pablo Traverso Gianini y Apache-2.0. `LICENSE` y `source/LICENSE` proporcionan esa licencia para los materiales propios de empaquetado y las fuentes del proyecto. Se conservan sin cambios los nueve textos de licencia de dependencias en `dependencies/licenses/`. Las revisiones v3–v4 corrigen el título del paper, la tipografía UTF-8 y el alcance de las notas históricas del README; sus otros 4.560 archivos son idénticos byte a byte a v2, incluidas todas las fuentes, los datos de atribución, las licencias y la evidencia.

La clausura anterior de Paper II contenía 1.511 módulos. La alineación sustituye en `PaperIApplications` la importación y consulta de `FourColourConsumerStage84` por el puente utilizado en Paper I. La clausura pierde `FourColourConsumerStage84` y `FourClassGraphConsumerStage80` y añade `PaperII.FourColourApplication`; los demás archivos comunes son idénticos salvo la importación y consulta de la entrada. Antes de la revisión de cabeceras de autoría, el módulo trasladado coincidía byte a byte con el antiguo `RequestProject.NW18.FourColourPaperII` del freeze original de Paper I. En el archivo seleccionado se conserva idéntico su cuerpo, mientras que su cabecera de autoría está corregida. No cambian su espacio de nombres ni los enunciados. `evidence/ALIGNMENT_MANIFEST.json` registra la alineación.

Paper I selecciona ahora `PAPER_I_LEAN_20261020_ALIGNED_v3`, con 1.070 módulos y seis consultas finales de la misma campaña alineada. Sus 623 módulos compartidos y este archivo usan los mismos cuerpos de prueba y cabeceras corregidas. Cada paper conserva su propia clausura, recibos y consultas de entrada.

## 3. Correspondencia y entradas

Aquí `PTA` abrevia `PartitionedTriangleAbsorption` para facilitar la lectura; las fuentes no definen ese alias.

| Resultado escrito | Declaración |
|---|---|
| Propiedad (2.7) | `PTA.BlowupB.KeevashTypedSpec` |
| Teorema A | `PaddedGeneral.RealInverse.keevashTypedSpec_of_threeStepLinks` |
| Teorema B | `PTA.BlowupB.teoremaB_of_keevash` |
| Deducción equilibrada | `PTA.BlowupB.teoremaB_balanced` |
| Corolario 4.2 | `PaddedGeneral.RealInverse.nearlyComplete_F123` |
| F1/F2 idealizado | `PaddedGeneral.RealInverse.idealized_F12` |
| Teorema C | `PTA.BlowupB.F0Direct.theorem146_ordered` |
| Lema SC | `PTA.BlowupB.LemmaSC.absorber_onePart` |
| Realización física | `PTA.BlowupB.LatinCore.RootPhysicalRefiner.exists_refiner` |
| Productor físico | `PTA.BlowupB.LatinCore.PhysicalProducer.physicalCycRefiner3` |
| Diecisiete certificados | `PTA.BlowupB.LatinCore.Conserved17.all_family_certificates` |
| Diecisiete conclusiones | `PTA.BlowupB.LatinCore.Conserved17.all_typed_specs` |
| Construcción de representantes | `PTA.BlowupB.keevashTypedSpec_of_closed765` |
| Clasificación exacta | `PTA.BlowupB.FiniteCensus.census_complete` |
| Número de representantes | `PTA.BlowupB.FiniteCensus.representativeMasks_card` |
| Puente del catálogo | `PTA.BlowupB.FiniteCensus.representative_closed765` |
| Teorema D | `PTA.BlowupB.FiniteCensus.keevashTypedSpec_of_admissible` |

`KeevashTypedSpec` es una definición, no un axioma atribuido a Keevash. La conclusión del Teorema D conserva las hipótesis sobre el grafo de (2.7). No afirma una descomposición de todo grafo íntegramente divisible. El inverso real conserva perfiles locales además de conteos globales. El Teorema C cuenta discrepancias ordenadas; el costo no ordenado del manuscrito es la mitad.

`Core`, `Families` y `PaperIApplications` tienen cuatro, siete y cuatro consultas finales. Son las entradas exactas auditadas; la validación no fue un `lake build` por defecto ni una única entrada agregada. Se conservan los nombres internos para preservar las fuentes validadas.

La tabla es una correspondencia de fuentes, no una lista de quince consultas individuales de axiomas. Los registros históricos contienen consultas adicionales por módulo. En particular, `teoremaB_balanced` tiene un recibo satisfactorio del módulo `BlowupB/TeoremaBBalanced.lean`, pero no aparece entre las quince consultas finales ni en la lista registrada de consultas de la fase de Paper II. Su fuente compila; este documento no afirma una auditoría final de axiomas separada de esa declaración.

El nombre `KeevashTypedSpec` registra la interfaz prevista a nivel de grafos. `BlowupB/KeevashBridge.lean` la define y demuestra aplicaciones condicionales; no importa una formalización del Teorema 3.1 de complejos etiquetados de Keevash. `isIntDiv_iff_physDiv_uniform`, en `BlowupB/Uniform.lean`, supone `IsCompleteBlowup` y `Reps p 5`. Su alcance es, por tanto, un grafo completo permitido con cinco representantes por clase. No establece la identificación correspondiente de retículos para un grafo arbitrario de (2.7). La Sección 2.3 del manuscrito registra la comparación y esta limitación; no se afirma equivalencia con el teorema etiquetado general.

La consulta de cuatro colores en `PaperIApplications` es ahora `NashWilliams18.PaperII.margin_four_colour_decomposition`, el puente hacia `nearlyComplete_F123` utilizado en Paper I. Su auditoría de dependencias exige este puente y excluye el consumidor anterior. Ambos papers certifican ahora la misma interfaz de cuatro colores, dentro de sus clausuras de entrada separadas.

## 4. Censo y familias con leyes de conservación

La prueba finita usa una codificación reversible de veinte tipos y veintiséis cajas determinadas por compañeros prohibidos. Los certificados de cobertura proporcionan permutaciones reales de etiquetas. La minimalidad prueba unicidad del representante. `census_complete` reúne estos hechos en una clasificación exacta con 765 representantes.

El predicado de construcción no tiene por qué ser invariante bajo toda permutación. La prueba final transporta la propiedad para grafos típicos ya demostrada mediante la permutación inversa; no infiere pertenencia al catálogo para el etiquetado original. Los 28 módulos del puente se compilaron en la clausura completa.

Para las familias con leyes de conservación, la prueba proporciona certificados del núcleo y de los demás componentes a escala común antes de aplicar la transferencia por división. La reserva física y el catálogo se fijan antes del residuo. Los pesos cuentan todas las apariciones de cada arco y la cota de grado se refiere al grado dirigido total. Python generó certificados candidatos; Lean comprobó cobertura, unicidad y transporte. El puente del censo no usa `native_decide` ni axiomas matemáticos nuevos.

## 5. Reproducción y evidencia

Para una comprobación estática, se extrae el archivo seleccionado y se ejecuta desde su raíz:

`python tools/verify_attribution.py`

Esto comprueba las huellas actuales de todas las fuentes, reconstruye las fuentes históricas exactas mediante `attribution/source_changes.json`, comprueba 1.510 recibos históricos satisfactorios y 3.096 vínculos de huellas de objetos importados del proyecto y verifica el manifiesto interno. No ejecuta Lean. Los 3.029 archivos de evidencia existentes permanecen idénticos byte a byte al predecesor limpio.

`evidence/verification.json` registra el resultado de la campaña, incluidas quince consultas con axiomas estándar. `evidence/build_plan.json` da el orden topológico. Cada módulo tiene un recibo en `evidence/receipts/` y salida del compilador en `evidence/module_logs/`; `evidence/entry_audit.log` reúne las salidas de las tres entradas. Al preparar el archivo, las huellas de fuentes coincidían con los recibos y todos los objetos compilados en disco coincidían con sus huellas registradas. El archivo no contiene objetos compilados.

La campaña se ejecutó en varias invocaciones, retomando sólo objetos con recibos válidos de esa campaña. La última invocación de Paper II registra 517 módulos compilados entonces y 370 reutilizados de invocaciones anteriores de la misma campaña limpia, que suman los 887 módulos de la fase de Paper II. Esos 370 no proceden de una caché del proyecto de otra campaña. Los 517 módulos compilados en la última invocación usaron el límite de memoria ampliado; cambiaron los límites de recursos, no las fuentes matemáticas. Los primeros 23 módulos se recompilaron contra la copia final de Mathlib de la misma revisión, con bytes de salida idénticos, según `evidence/early_module_recheck.txt`. Son partes de una única campaña limpia local, no replicaciones independientes.

Para una compilación nueva se instala `leanprover/lean4:v4.35.0-rc3`, se prepara Mathlib en `c55e6e786f49471c72fbddbec5415808896aec1e` y las revisiones registradas de dependencias, y se obtiene su caché con `lake exe cache get`. Se conserva el archivo de dependencias; no se ejecuta `lake update`. Se compila el árbol `source/` suministrado en un directorio de resultados separado y se generan recibos nuevos. Los programas históricos `tools/build.py` y `tools/align.py` usan rutas fijas de Windows y requieren adaptación; son registros de la campaña, no un reproductor portable de un solo comando. En particular, el programa de alineación reconstruye las fuentes anteriores a la corrección y no debe sobrescribir el árbol corregido seleccionado. Las instrucciones originales de la campaña permanecen en `evidence/BUILD_README.md`.

Algunos comentarios de las fuentes remiten a notas históricas de investigación o generadores externos al archivo. El inventario de revisión registra sus rutas exactas, distingue las referencias explícitas a `cegis/` de otros nombres de notas y comprueba que no son importaciones del proyecto ni lecturas necesarias en ejecución. No se suministran como recursos de reproducibilidad. Se conservan las pruebas Lean y los recibos sin editar esos comentarios. El inventario de auditoría está en `02_validation/SOURCE_NOTE_INVENTORY.json` dentro del repositorio de la serie.

Los enlaces relativos y las rutas de los programas de auditoría describen el monorrepositorio completo de la serie. Copiar sólo `preprints/PAPER_II/` no produce una distribución autónoma. El verificador estático del ZIP de fuentes es una comprobación separada y autocontenida de sus archivos.

Esta integración editorial no ejecuta ninguna compilación Lean. Su auditoría estática verifica la evidencia suministrada y la correspondencia exacta de fuentes; no inspecciona de nuevo los objetos compilados omitidos ni afirma una reproducción independiente.

## 6. Demostración escrita y correspondencia formal

Los apéndices matemáticos de Paper II integran ahora los seis dossiers de pruebas escritas del commit `61f752fc87bff6f5654725b23ce10ad4302364ab`. La sección 7 identifica sus fuentes. La edición conserva los enunciados y las fuentes congeladas. Añade exposición; no deduce validez matemática de la composición tipográfica ni de comprobaciones aritméticas finitas.

La correspondencia tiene dos niveles. Las declaraciones de la sección 3 enuncian los resultados principales. Los módulos de la sección 7 proporcionan el inverso real, los certificados firmados, el refinador, la geometría semidensa, el equilibrio por componentes y el catálogo conservado. Los resultados auxiliares de refinamiento ordinario, emparejamiento robusto, empaquetamiento y cobertura siguen siendo dependencias explícitas. La clasificación universal necesita además las tablas finitas de familias: los componentes dados como ejemplo no sustituyen esas tablas.

El teorema semidenso, la deducción equilibrada F1–F3 y el Lema SC son distintos. En la interfaz semidensa, la discrepancia ordenada duplica el costo de edición no ordenado del manuscrito. En el catálogo conservado, el grado es la suma de los grados de entrada y salida, y la carga suma todos los elementos del catálogo. La división de vértices puede cambiar el orden del grafo, por lo que se ajustan las cotas relativas de oferta y grado antes de proyectar. Estas convenciones son esenciales para la correspondencia.

El manuscrito, sus apéndices matemáticos y enunciados auxiliares y este documento complementario están disponibles íntegramente en inglés y español. Ambas ediciones conservan las mismas expresiones matemáticas, identificadores de declaraciones y huellas de fuentes. Las versiones anteriores se conservan en el archivo superseded.

El archivo seleccionado documenta la campaña alineada terminada y sus revisiones posteriores exclusivas de cabeceras y de README. Las fuentes del proyecto y los materiales propios de empaquetado usan Apache-2.0; se conservan las licencias de dependencias. El manuscrito y este documento complementario usan CC BY 4.0. La compilación registrada es una campaña local, no una reproducción independiente.

## 7. Mapa de los apéndices matemáticos

Las rutas siguientes son relativas a `source/PartitionedTriangleAbsorption/` en el archivo fijo de Paper II, salvo que una tabla indique una base más específica. El Apéndice A corresponde al inverso acotado y a los componentes terminales utilizados por las entradas de la sección 3. El Apéndice D corresponde a `BlowupB/VertexSplit/{Basic,Div,Decomp,Supply,Transfer,ComponentsT}.lean`. Se traducen los rótulos del mapa técnico; los nombres de archivos e identificadores se conservan exactamente como en las fuentes. Las llaves y los comodines describen familias de archivos; no son instrucciones de importación.

### Apéndice A

| Argumento | Módulos congelados |
|---|---|
| Inversa real del anfitrión completo permitido | `BlowupB/PaddedGeneral/RealInverse/{Basic,Global,Modes,Factors,Stages}.lean` |
| Inversa real e interfaces de aplicación | `BlowupB/PaddedGeneral/RealInverse/{Producer,Uniform,ProducerConsumer,Consumer}.lean` |
| Certificados firmados acotados | `TypedBoundedCoefficients.lean`, `TypedLatticePadding.lean` y sus dependencias |
| Construcciones terminales físicas y presupuestos | `BlowupB/CertAbsorber/{Basic,Cert,Gadget,Decomp,Host,Greedy,Budgets,Terminal,Produce}.lean` |



### Apéndice B



| Argumento | Fuentes |
|---|---|
| Retículo local | `BlowupB/UniversalProducer/PairLattice.lean` |
| Refinador finito ordinario | `UniversalRefiner/{Basic,Level,Hierarchy,Heap,Assembly,Loads,Main}.lean`; `ParityChain.lean`, `ModThreeLayer.lean` |
| Biblioteca virtual y realización mediante caminos | `BlowupB/UniversalProducer/{VirtualRefiner,LabelWalk,WeightedRouting,WeightedRoutingChoice,WeightedRoutingBudget,RoutedEvenProducer}.lean` |
| Grupo de cargas y patrones finitos | `BlowupB/UniversalProducer/{ChargeAtoms,Patterns,PatternSupply,IterLayers}.lean` |
| Registro y ajustes de torsión | `BlowupB/UniversalProducer/{GroupLedger,GroupLayer,Reduction,ReductionArith}.lean`; `BlowupB/StructuralF3General/TokenLedger.lean` |
| Absorbedores privados | Apéndice A.4–A.6; `BlowupB/UniversalProducer/Refiner.lean` |
| Aplicación cuantitativa | `BlowupB/PaddedGeneral/{InverseScales,ScaledPipeline}.lean`; `BlowupB/PaddedGeneral/RealInverse/{ProducerConsumer,Consumer}.lean` |


### Apéndice C

Las rutas de esta tabla son relativas a `BlowupB/F0Direct/`, salvo `PhysicalHingeSupply/Template.lean`, que es relativa a la raíz del espacio de nombres del proyecto.

| Paso | Fuentes congeladas |
|---|---|
| Hipótesis del anfitrión y borrado | `Geometry.lean`, `GeometryDeletion.lean` |
| Estabilidad de recorridos cortos | `WalkSupply.lean`, `WalkCounts.lean`, `WalkConsequences.lean`, `HostWalkQueries.lean` |
| Certificado entero | `CertificateIncidence.lean`, `CertificatePeeling.lean`, `CertificateColumns.lean`, `CertificateAssembly.lean`, `CertificateHost.lean` |
| Bisagras explícitas y conteos físicos | `HingeTemplates.lean`, `HostHinges.lean`, `HostBadHinges.lean`, `HostCrossHinges.lean`, `HingeCounting.lean`, `HostHingeSupply.lean`; `PhysicalHingeSupply/Template.lean` |
| Constantes terminales | `FiniteTerminal.lean`, `LocalProducer.lean` |
| Inversa real | `RealInternalInverse.lean`, `RealCompleteAlgebra.lean`, `RealCompleteBounds.lean`, `RealCompleteInverse.lean`, `InverseRestriction.lean`, `DiscardedCopies.lean`, `HostRealInverse.lean` |
| Pesos exactos | `UniformWeights.lean`, `PositiveWeights.lean`, `WeightProducer.lean` |
| Reserva universal y cierre | `UniversalScales.lean`, `Closure.lean`, `Theorem146.lean` |


### Apéndice E

Las rutas de esta tabla son relativas a `BlowupB/`.

| Paso escrito | Módulos fuente |
|---|---|
| Criterios enteros locales y escalares | `BalFixer/BalInside.lean`, `BalFixer/TorsInside.lean`, `FinT/Lattice.lean` |
| Realización de componentes PAR | `FinT/BudgetKappa.lean`, `FinT/ChargeU12.lean`, `Flex/Even3.lean`, `Flex/TokenCerts.lean`, `Flex/CompWrappers.lean` |
| Fichas raíz y disponibilidad geométrica | `BalFixer/{RootedTokens,BalSupply,BalSupplyX,BalSupplyY}.lean` |
| Invariantes de tamaño y carga | `BalFixer/{VertexLayer,VertexLayers,VertexLayersX,VertexLayersY,VertexLayersD}.lean` |
| Variantes de carga global | `BalFixer/{BalLibraryChi,BalLibraryChiY,BalLibraryChiYM,ChiTokens,ChiTokensM}.lean` |
| Cadena de torsión | `TorsionQ/{Chain,Finite,Refiner,Value}.lean`; `BalFixer/BalLibraryTors.lean` |
| Potenciales de congruencia | `BalFixer/{Pot3,PotQ,PotQ6}.lean` |
| Cierre cuantitativo de componentes | `BalFixer/BalComponent*.lean`, `BalFixer/BalScales*.lean`, `BalFixer/CompBal*.lean`, `BalFixer/FlexL.lean` |
| Transporte de familias | `Flex/ParAssembly.lean`, `Flex/Par/`, `Flex/ParClosed/`, `BalFixer/Fam/`, `BalFixer/All.lean` |
| Cobertura final | `TeoremaB748.lean`, `TeoremaB765.lean`, el censo importado por la entrada de familias de Paper II |


### Apéndice F

Las rutas de esta tabla son relativas a `BlowupB/LatinCore/`.

| Argumento escrito | Fuentes congeladas |
|---|---|
| Redondeo de flujos e inversa tensorial | `RealTensorFilling.lean`, dependencias de flujos enteros y rellenos enteros acotados |
| Grafo de cuatro permutaciones | `Expander/BinomialEstimates.lean`, `Expander/PermutationExpander.lean` |
| Normalización de perfiles y rectángulos | `DenseProducer/{ExpanderFlow,Faces,Counting,Profile,Filling}.lean` |
| Cobertura positiva exacta y cotas densas | `Positivization/{ExactCover,Load}.lean`, `DenseProducer/{DenseVc,Main}.lean` |
| Partición voraz en centros y carga enraizada | `Cycles/{GreedyPartition,DenseReduction,DenseAssemblyBounds,DenseOldLoad,DenseAssembly}.lean` |
| Red de ocho permutaciones en la raíz | `Expander/EightPermutation.lean`, `RootChannels.lean`, `RootPaths.lean`, `RootLift.lean`, `RootInput.lean` |
| Catálogo fijo completo | `CompletedCatalogue.lean`, `RootMesoscopic.lean`, `RootCatalogue.lean`, `RootCatalogueBudget.lean` |

## 8. Resultados auxiliares: ubicaciones exactas en las fuentes

El Apéndice G del manuscrito enuncia los resultados auxiliares utilizados en el ensamblaje. Las rutas siguientes son relativas a `source/PartitionedTriangleAbsorption/` en el freeze seleccionado de Paper II. Los nombres identifican declaraciones dentro del módulo indicado, no nuevas consultas de entradas públicas. La evidencia es la fuente y su cierre de dependencias registrado; esta revisión no añade compilaciones Lean ni consultas de axiomas.

- **G.1**: `ReturnedBasic.lean`; `AntiEdgeful`.
- **G.2**: `BlowupB/PaddedNibble/TypedEffectiveConsumer.lean`; `typed_nibble_packing_near_effective`.
- **G.2**: `BlowupB/PaddedNibble/TypedNibbleAdapter.lean`; `typed_nibble_packing`.
- **G.2**: `BlowupB/PaddedNibble/Nibble/PolynomialThreshold.lean`; `packingPolynomial`.
- **G.2**: `BlowupB/PaddedQuantitative/EffectiveSchedule.lean`; `loadTolerance`.
- **G.2**: `BlowupB/PaddedNibble/ReserveConstruction.lean`; `exists_reserve_of_decomposition`.
- **G.3**: `BlowupB/PaddedNibble/TypedEffectiveConsumer.lean`; `typed_cover_down_absorption_effective`.
- **B.3/G.4**: `BlowupB/UniversalProducer/RoutedEvenProducer.lean`; `evenRefinerProducer_routed`.
- **G.4/H.5, C.5a**: `TypedRefinerF0/RobustSlots.lean`; `exists_robust`.
- **B.3/G.4/H.6**: `UniversalRefiner/Main.lean`; `exists_universal_refiner`.
- **G.5**: `BlowupB/LatinCore/WeightedPathStep.lean`; `exists_weighted_path`.
- **B.4**: `BlowupB/UniversalProducer/IterLayers.lean`; `iterate_layers`.
- **B.6**: `BlowupB/PaddedF12/HostGap.lean`; `degree_gap_of_guarded`.
- **C.5a**: `F0FlexibleCompressed.lean`; `compatible_producer`.
- **C.5a**: `TypedRefinerF0/ChargeLayer.lean`; `charge_layer`.
- **C.5a**: `CompatibleShared/Host.lean`; `compatible_shared_host`.
- **C.6**: `BlowupB/F0Direct/UniversalScales.lean`; `universal_from_small_reserve`.
- **E.8**: `BlowupB/PaddedF12/PaddedDefinitions.lean`; `KeevashPaddedSpec`.
- **E.8**: `BlowupB/PaddedComponents/ReductionLarge.lean`; `keevashPaddedSpec_of_certs₈`.
- **E.8**: `BlowupB/KeevashPaddedMain.lean`; `keevashTypedSpec_of_padded`.
- **8**: `BlowupB/BalFixer/FlexL.lean`; `UniversalCertFlexL`.
- **8**: `BlowupB/BalFixer/CompL.lean`; `compScalesL`.
- **8**: `BlowupB/BalFixer/CompL.lean`; `universalCertFlexL_of_split`.

El Apéndice H da ahora demostraciones matemáticas escritas de la biblioteca compatible de cargas (H.1–H.4), las posiciones robustas (H.5), el refinador ordinario (H.6), el empaquetamiento (H.7–H.8) y la selección de reserva por bloques completos (H.9). H.3 deduce los factores por capa de B.4. G.3 y G.5 dan las reducciones de cobertura y caminos ponderados. Los certificados finitos de familias siguen siendo datos explícitos de las fuentes congeladas. Esta exposición conserva los cuerpos de prueba del freeze alineado seleccionado y no añade una compilación Lean ni consultas de axiomas. La reconstrucción escrita y las comprobaciones de regresión finita son materiales auxiliares del desarrollo; las ubicaciones anteriores identifican las dependencias congeladas de las pruebas. Las comprobaciones finitas son evidencia de transcripción, no premisas de los teoremas universales.

Los 120 casos de enlaces conexos no bipartitos comprenden 93 casos de tres pasos y otros 27 casos con posiciones adicionales. Las demás rutas cubren 271 casos PAR y 357 casos BAL, seguidos por los 17 casos conservados. La especificación con posiciones adicionales es una interfaz intermedia demostrada, no un axioma matemático adicional ni un teorema atribuido a un manuscrito inaccesible.

Los scripts de comprobación del repositorio esperan el árbol completo de fuentes congeladas en las rutas relativas documentadas. Una copia dispersa que contenga solo documentos no basta. Se debe restaurar el archivo de fuentes o utilizar una copia completa antes de ejecutar esos scripts; esto es distinto de una nueva reconstrucción Lean.

## Uso de inteligencia artificial y herramientas computacionales

Se utilizaron Claude, de Anthropic, y ChatGPT/Codex, de OpenAI, para explorar y revisar argumentos y preparar el manuscrito. Aristotle, de Harmonic, contribuyó a explorar enfoques, buscar contraejemplos, desarrollar demostraciones y formalizarlas y revisarlas en Lean. Su participación no se limitó a traducir pruebas terminadas.

Certo [3] y Jacobian [4] se utilizaron para explorar casos finitos, comprobar identidades y evaluar construcciones candidatas. Las comprobaciones finitas no se trataron como demostraciones de enunciados universales. La búsqueda del censo produjo certificados finitos. Lean verificó después la cobertura del universo admisible, la unicidad salvo permutaciones reales y la conexión con los teoremas de construcción; esto es más que compilar una lista de ejemplos.

El autor es responsable de los argumentos, las citas, el código y la presentación. Ningún sistema de inteligencia artificial figura como autor.

## Referencias

[1] J. P. Traverso Gianini, *Triangle decompositions II: Robust absorption for typed triangles*, preprint 1.0 (2026). https://doi.org/10.5281/zenodo.23502224. [Documento](https://github.com/jtraverso/nash-williams-triangle-decompositions/blob/main/preprints/PAPER_II/01_manuscript/PAPER_II_preprint_v1.0_es.md).

[2] J. P. Traverso Gianini, *Triangle decompositions I: Formalizing the Nash–Williams theorem in Lean*, preprint 1.0 (2026). https://doi.org/10.5281/zenodo.23428173. [Documento](https://github.com/jtraverso/nash-williams-triangle-decompositions/blob/main/preprints/PAPER_I/01_manuscript/PAPER_I_preprint_v1.0_es.md).

[3] J. P. Traverso Gianini, *Certo*. https://github.com/jtraverso/certo-math.

[4] *Jacobian*. https://github.com/morluto/jacobian.

Copyright © 2026 Juan Pablo Traverso Gianini. Este documento se distribuye bajo [CC BY 4.0](https://creativecommons.org/licenses/by/4.0/).
