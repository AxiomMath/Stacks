module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GrothendieckAbelian
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HypercohomologyEdge.EdgeMorphism
public import StacksFrontier.Topology.Sheaves.Cohomology.FilteredComplexSpectralSequence.HypercohomologySpectralSequence
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedInternalHom

/-!
# Ext sheaves on a ringed space

Let `(X, O_X)` be a ringed space and let `K`, `L` be objects of the derived category `D(O_X)`.
The *Ext sheaves* of `K` and `L` are the cohomology sheaves of the derived internal Hom,

`SheafExt^n(K, L) = H^n(RSheafHom(K, L))`,

a family of `O_X`-modules indexed by `n : ℤ` and functorial in both variables. Two descriptions
of them are recorded here.

First, `SheafExt^n(K, L)` is the sheafification of a presheaf of Ext groups. The degree-`n`
hypercohomology of `RSheafHom(K, L)` over the opens of `X`, taken on all opens at once, is a
presheaf of `O_X`-modules whose sheafification is `SheafExt^n(K, L)`; its value over an open `U`
is `H^n(U, RSheafHom(K, L))`, which is the Ext group `Ext^n_{D(O_U)}(K|_U, L|_U)` by
[Stacks, Tag 08DK]. The unit of sheafification, read on sections over `U`, is the canonical
comparison `H^n(U, RSheafHom(K, L)) ⟶ Γ(U, SheafExt^n(K, L))`.

Second, the Ext sheaves are the second page of the local-to-global spectral sequence. The
hypercohomology spectral sequence of [Stacks, Tag 0BKM] applied to `RSheafHom(K, L)` has

`E_2^{p, q} = H^p(X, SheafExt^q(K, L))`,

and converges, when `RSheafHom(K, L)` is bounded below, to the hypercohomology
`H^{p + q}(X, RSheafHom(K, L))`, which is `Ext^{p + q}_{D(O_X)}(K, L)` by [Stacks, Tag 08DK].

## Main definitions

* `Stacks.SheafOfModules.derivedSheafExt`: the Ext sheaf `SheafExt^n(K, L)`, the degree-`n`
  cohomology sheaf of the derived internal Hom.
* `Stacks.SheafOfModules.derivedSheafExtFunctor`: the same as a bifunctor on `D(O_X)`,
  contravariant in the first variable.
* `Stacks.SheafOfModules.derivedSheafExtPresheaf`: the presheaf of degree-`n` hypercohomology of
  `RSheafHom(K, L)`, whose sheafification is the Ext sheaf.
* `Stacks.SheafOfModules.derivedSheafExtEdge`: the canonical comparison
  `H^n(U, RSheafHom(K, L)) ⟶ Γ(U, SheafExt^n(K, L))`.

## Main results

* `Stacks.SheafOfModules.derivedSheafExtIsoSheafifyPresheaf`: the Ext sheaf is the
  sheafification of that presheaf.
* `Stacks.SheafOfModules.derivedSheafExtPresheafEvaluationIso`: the value of that presheaf over
  an open `U` is the degree-`n` hypercohomology of `RSheafHom(K, L)` over `U`.
* `Stacks.SheafOfModules.hypercohomologySpectralSequence_e₂_derivedSheafExt`: the second page of
  the hypercohomology spectral sequence of `RSheafHom(K, L)` is `H^p(X, SheafExt^q(K, L))`.

## Implementation notes

The Ext sheaves are the cohomology sheaves of the derived internal Hom, not the right derived
functors of the underived internal Hom: they are defined on objects of `D(O_X)` and in every
integer degree. `Stacks.RingedSpace.sheafExt` is the other object, the right derived functor of
`Stacks.SheafOfModules.InternalHom.internalHomSecondFunctor` evaluated at a single sheaf of
modules and indexed by a natural number; the two agree on modules, but that comparison is a
statement about a derived functor of a left exact functor and is not made here.

The identification of the presheaf's values with Ext groups is [Stacks, Tag 08DK] and is cited
rather than composed in. Derived sections appear here in the form
`Stacks.Cohomology.HypercohomologyEdge.derivedSections`, the right derived functor of evaluation
at an open with values in modules over the sections of `O_X` there, whereas
`Stacks.SheafOfModules.derivedSheafHomSectionsEquiv` of Tag 08DK is stated for
`Stacks.Cohomology.Localization.derivedSectionsOverObject`, the right derived functor of sections
on the slice site with values in abelian groups. The two are right derived functors of the same
underlying functor read in different target categories; no declaration below asserts the Ext
reading.

The spectral sequence statement is about the second page only. Convergence of the sequence of
[Stacks, Tag 0BKM] to `H^{p + q}(X, -)` needs a bounded below complex representing the object,
and is `Stacks.Cohomology.FilteredComplex.exists_boundedBelowHypercohomologySpectralSequence`;
it is stated there of an existentially produced spectral sequence rather than of the canonical
one carrying the second-page identification, so the two clauses are not available as a single
statement about one term, and the boundedness below of `RSheafHom(K, L)` is not deduced here
from boundedness of `K` and `L`.

The spectral sequence is stated for a `AlgebraicGeometry.RingedSpace`, since that is the setting
of Tag 0BKM, while the Ext sheaves themselves are stated for a sheaf of commutative rings on a
space, the setting of the derived internal Hom. The structure sheaf of a ringed space is
`structureSheaf` of its sheaf of rings by definition, so the two settings meet with no comparison
functor between them.

## References

* [Stacks Project, Tag 0BQP](https://stacks.math.columbia.edu/tag/0BQP)
* [Stacks Project, Tag 08DK](https://stacks.math.columbia.edu/tag/08DK)
* [Stacks Project, Tag 0BKM](https://stacks.math.columbia.edu/tag/0BKM)
* [Stacks Project, Tag 0BKJ](https://stacks.math.columbia.edu/tag/0BKJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite AlgebraicGeometry
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.FilteredComplex
open Stacks.Cohomology.HypercohomologyEdge

namespace Stacks.SheafOfModules

universe u

attribute [local instance] HasDerivedCategory.standard

variable {X : TopCat.{u}} (Rc : TopCat.Sheaf CommRingCat.{u} X)
  [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- Sheaves of `O_X`-modules on a ringed space form a Grothendieck abelian category. -/
local instance isGrothendieckAbelian_structureSheafModules :
    IsGrothendieckAbelian.{u} (StructureSheafModules Rc) :=
  _root_.SheafOfModules.isGrothendieckAbelianU.{u, u, u} (structureSheaf Rc)

/-! ### The Ext sheaves -/

/-- **The Ext sheaves.** For objects `K`, `L` of `D(O_X)` and an integer `n`, the Ext sheaf
`SheafExt^n(K, L)` is the degree-`n` cohomology sheaf of the derived internal Hom
`RSheafHom(K, L)`, an `O_X`-module. -/
@[stacks 0BQP "the definition of the Ext sheaves: SheafExt^n(K, L) is the n-th cohomology sheaf \
of RSheafHom(K, L), for K and L objects of D(O_X) and n an integer",
  ega "0 12.3.1" "more general",
  sga "4 V 6.0" "special case"]
abbrev derivedSheafExt (K L : DerivedCategory (StructureSheafModules Rc)) (n : ℤ) :
    StructureSheafModules Rc :=
  (DerivedCategory.homologyFunctor (StructureSheafModules Rc) n).obj
    (((derivedSheafHom Rc).obj (op K)).obj L)

/-- **The Ext sheaves as a bifunctor.** `SheafExt^n(-, -)` is a functor of both variables,
contravariant in the first: it is the derived internal Hom followed by the degree-`n` cohomology
sheaf. -/
@[stacks 0BQP "the Ext sheaves are functorial in both variables, contravariantly in the first",
  ega "0 12.3.1" "more general", sga "4 V 6.0" "6.0.1, special case"]
def derivedSheafExtFunctor (n : ℤ) :
    (DerivedCategory (StructureSheafModules Rc))ᵒᵖ ⥤
      DerivedCategory (StructureSheafModules Rc) ⥤ StructureSheafModules Rc :=
  derivedSheafHom Rc ⋙ (Functor.whiskeringRight _ _ _).obj
    (DerivedCategory.homologyFunctor (StructureSheafModules Rc) n)

/-- The bifunctor `SheafExt^n(-, -)` takes the value `SheafExt^n(K, L)` at `(K, L)`. -/
lemma derivedSheafExtFunctor_obj_obj (K L : DerivedCategory (StructureSheafModules Rc))
    (n : ℤ) :
    ((derivedSheafExtFunctor Rc n).obj (op K)).obj L = derivedSheafExt Rc K L n :=
  rfl

/-! ### The Ext sheaf is a sheafification -/

/-- **The presheaf behind the Ext sheaf.** The degree-`n` hypercohomology of
`RSheafHom(K, L)` taken over all opens of `X` at once, as a presheaf of `O_X`-modules. Its value
over an open `U` is `H^n(U, RSheafHom(K, L))`, which is `Ext^n_{D(O_U)}(K|_U, L|_U)` by
[Stacks, Tag 08DK], and its sheafification is `SheafExt^n(K, L)`. -/
def derivedSheafExtPresheaf (K L : DerivedCategory (StructureSheafModules Rc)) (n : ℤ) :
    PresheafOfModules.{u} (structureSheaf Rc).obj :=
  (DerivedCategory.homologyFunctor (PresheafOfModules.{u} (structureSheaf Rc).obj) n).obj
    ((derivedSectionsPresheaf (structureSheaf Rc)).obj (((derivedSheafHom Rc).obj (op K)).obj L))

/-- The value of `derivedSheafExtPresheaf` over an open `U` is the degree-`n` hypercohomology of
`RSheafHom(K, L)` over `U`. -/
def derivedSheafExtPresheafEvaluationIso (K L : DerivedCategory (StructureSheafModules Rc))
    (U : Opens X) (n : ℤ) :
    (PresheafOfModules.evaluation (structureSheaf Rc).obj (op U)).obj
        (derivedSheafExtPresheaf Rc K L n) ≅
      (derivedSections (structureSheaf Rc) U ⋙
          DerivedCategory.homologyFunctor
            (ModuleCat.{u} ((structureSheaf Rc).obj.obj (op U))) n).obj
        (((derivedSheafHom Rc).obj (op K)).obj L) :=
  (sectionsEvaluationIso (structureSheaf Rc) U n).app _

/-- **The Ext sheaf is a sheafification.** `SheafExt^n(K, L)` is the sheaf of `O_X`-modules
associated to the presheaf of degree-`n` hypercohomology of `RSheafHom(K, L)`, whose value over
an open `U` is `Ext^n_{D(O_U)}(K|_U, L|_U)` by [Stacks, Tag 08DK].

This is [Stacks, Tag 0BKJ] — a cohomology sheaf is the sheafification of the cohomology presheaf
— read at `RSheafHom(K, L)`. -/
@[stacks 0BQP "the Ext sheaf is the sheafification of the presheaf of degree-n hypercohomology \
of RSheafHom(K, L) on the opens of X; the identification of that presheaf's values with the Ext \
groups Ext^n(K|_U, L|_U) is Tag 08DK and is cited, not composed in here"]
def derivedSheafExtIsoSheafifyPresheaf (K L : DerivedCategory (StructureSheafModules Rc))
    (n : ℤ) :
    (PresheafOfModules.sheafification (𝟙 (structureSheaf Rc).obj)).obj
        (derivedSheafExtPresheaf Rc K L n) ≅ derivedSheafExt Rc K L n :=
  (sheafificationCohomologyPresheafIso (structureSheaf Rc) n).app _

/-- **The canonical comparison into the Ext sheaf.** The map
`H^n(U, RSheafHom(K, L)) ⟶ Γ(U, SheafExt^n(K, L))` from degree-`n` hypercohomology over an open
`U` to the sections of the Ext sheaf there, the unit of sheafification read on sections over `U`.
Its source is `Ext^n_{D(O_U)}(K|_U, L|_U)` by [Stacks, Tag 08DK]. -/
def derivedSheafExtEdge (K L : DerivedCategory (StructureSheafModules Rc)) (U : Opens X)
    (n : ℤ) :
    (derivedSections (structureSheaf Rc) U ⋙
          DerivedCategory.homologyFunctor
            (ModuleCat.{u} ((structureSheaf Rc).obj.obj (op U))) n).obj
        (((derivedSheafHom Rc).obj (op K)).obj L) ⟶
      (_root_.SheafOfModules.evaluation (structureSheaf Rc) (op U)).obj
        (derivedSheafExt Rc K L n) :=
  (hypercohomologyEdge (structureSheaf Rc) U n).app _

/-! ### The second page of the local-to-global spectral sequence -/

section SpectralSequence

variable (Y : RingedSpace.{u, u})
  [HasSheafify (Opens.grothendieckTopology Y.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology Y.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **The second page of the local-to-global spectral sequence of Ext.** The hypercohomology
spectral sequence of [Stacks, Tag 0BKM] applied to `RSheafHom(K, L)` has second page

`E_2^{p, q} = H^p(X, SheafExt^q(K, L))`,

the hypercohomology of the Ext sheaves. Its abutment is `H^{p + q}(X, RSheafHom(K, L))`, which is
`Ext^{p + q}_{D(O_X)}(K, L)` by [Stacks, Tag 08DK]. -/
@[stacks 0BQP "the second page of the local-to-global spectral sequence of Ext: the Tag 0BKM \
hypercohomology spectral sequence of RSheafHom(K, L) has E_2^{p, q} = H^p(X, SheafExt^q(K, L)); \
convergence to Ext^{p+q}(K, L) is not claimed here -- the Tag 0BKM convergence clause needs a \
bounded below complex representing RSheafHom(K, L) and is stated of an existentially produced \
spectral sequence rather than of the canonical one carrying this second page, and the Ext \
reading of the abutment is Tag 08DK", sga "7 VIII 1.1" "partial"]
theorem hypercohomologySpectralSequence_e₂_derivedSheafExt
    (K L : DerivedCategory (_root_.SheafOfModules.{u} (structureSheafRing Y))) (p q : ℤ) :
    Nonempty ((((hypercohomologySpectralSequence Y
          (((derivedSheafHom Y.sheaf).obj (op K)).obj L)).spectralSequence.page 2).X (p, q)) ≅
      (DerivedCategory.homologyFunctor
          (ModuleCat.{u} ((structureSheafRing Y).obj.obj (op ⊤))) p).obj
        ((hypercohomologySpectralSequence Y
            (((derivedSheafHom Y.sheaf).obj (op K)).obj L)).truncation.RΓ.obj
          ((DerivedCategory.singleFunctor (_root_.SheafOfModules.{u} (structureSheafRing Y)) 0).obj
            (derivedSheafExt Y.sheaf K L q)))) :=
  hypercohomologySpectralSequence_e₂ Y (((derivedSheafHom Y.sheaf).obj (op K)).obj L) p q

end SpectralSequence

end Stacks.SheafOfModules

end
