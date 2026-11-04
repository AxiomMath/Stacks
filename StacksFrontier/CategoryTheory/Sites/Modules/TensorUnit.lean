module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.MonoidalSheafTensor
public import StacksFrontier.Topology.Sheaves.Cohomology.KFlat.Defs
public import StacksFrontier.Homology.KFlat.BifunctorSingleSecondFactor
public import StacksFrontier.Homology.KFlat.BifunctorBoundedAbove
import StacksCore.Tactic.StacksAttribute

/-! # Tensoring with the structure sheaf on a ringed site

Let `(C, O)` be a ringed site. The structure sheaf, viewed as a sheaf of modules over itself,
is the unit of the tensor product of Stacks 06YM: `F ⊗_O O ≅ F` naturally in `F`. This file
records that isomorphism and the three consequences a derived-category client needs: the
termwise complex `p ↦ K^p ⊗_O O` is `K`, the complex `O[0]` is K-flat, and the total tensor
complex `Tot(K ⊗_O O[0])` is `K`.

## Main definitions

* `Stacks.SheafOfModules.sheafTensorUnitNatIso`: `- ⊗_O O ≅ id`, the right unitor read off the
  bifunctor `Stacks.SheafOfModules.Tensor.sheafTensor`.
* `Stacks.SheafOfModules.rowComplexUnitIso`: the termwise complex `p ↦ K^p ⊗_O O` is `K`.
* `Stacks.SheafOfModules.tensorComplexUnitIso`: `Tot(K ⊗_O O[0]) ≅ K`.
* `Stacks.SheafOfModules.sheafTensorUnitNatIsoFreeSections`,
  `Stacks.SheafOfModules.rowComplexUnitIsoFreeSections` and
  `Stacks.SheafOfModules.tensorComplexUnitIsoFreeSections`: the same three isomorphisms with the
  universe of the sections free.

## Main results

* `Stacks.SheafOfModules.isKFlat_single_unit`: the structure sheaf placed in degree zero is a
  K-flat complex.

## Implementation notes

Nothing here is new mathematics; the point is to connect two existing constructions. The
monoidal structure on `Mod(O)` whose curried tensor product *is*
  `Stacks.SheafOfModules.Tensor.sheafTensor`
and whose unit *is* `SheafOfModules.unit` is
`SheafOfModules.monoidalCategorySheafTensor`, and
`SheafOfModules.curriedTensor_sheafTensor` and `SheafOfModules.tensorUnit_sheafTensor` are the
two equalities that let Mathlib's `rightUnitorNatIso` be read as a statement about
`sheafTensor`. So `sheafTensorUnitNatIso` is `rightUnitorNatIso` transported along an
`eqToIso` between two functors that are *equal*, not merely isomorphic.

K-flatness of `O[0]` is then `CochainComplex.KFlatBifunctor.kFlat_single_of_exact` (the base
case of Stacks 06YQ), whose hypothesis is that the termwise complex against `O` carries acyclic
complexes to acyclic complexes — which `rowComplexUnitIso` turns into a tautology. Going
through that lemma rather than through flatness of `O` and the bounded-above criterion avoids
needing the flatness of the unit as a separate input.

`tensorComplexUnitIso` is `CochainComplex.KFlatBifunctor.totalSingleIso`, the single-row
comparison for an arbitrary additive bifunctor, specialised to `⊗_O`; no total-complex
bookkeeping is redone here.

**Universes.** `sheafTensorUnitNatIso` reads the unitor off the re-seated monoidal structure of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/MonoidalSheafTensor.lean`, which needs the
sections of the structure sheaf in `max u v`, `u` and `v` being the object and morphism
universes of the site: that structure is localized along sheafification from the monoidal
structure on presheaves of modules, and the monoidality of the localizing class is proved there
through the internal hom, which lives in `max u v`.

The unit law itself does **not** need the localization, and
`sheafTensorUnitNatIsoFreeSections` states it at a free sections universe `w`: the value of
`- ⊗_O O` at `F` is the sheafification of `F.val ⊗_{pre} O`, the right unitor of *presheaves* of
modules identifies `F.val ⊗_{pre} O` with `F.val`, and the counit of the sheafification
adjunction identifies the sheafification of `F.val` with `F`. Both of those are available at a
free `w` (`Stacks.SheafOfModules.Tensor.ringSheafPresheafMonoidalCategory` and
`SheafOfModules.sheafifyCounitIso`), and so are
`Stacks.SheafOfModules.Tensor.sheafTensor` and the K-flatness predicate. The free-universe forms
are what the Tor-amplitude development consumes; `isKFlat_single_unit` is stated at the free
universe outright, there being no monoidal-structure form of it to keep.

DEDUP OWED: `Stacks.SheafOfModules.tensorSheafUnitRightIso`
(`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/TensorUnitSections.lean`) is the same
isomorphism at the `structureSheaf` spelling of the sheaf of rings, also at a free sections
universe and with formulas on local sections; the two should be merged onto one declaration.
`SheafOfModules.rightUnitor_sheafTensor_eq`
(`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/MonoidalSheafTensorUnitors.lean`) identifies it
with the re-seated unitor, hence with `sheafTensorUnitNatIso`, at `w = max u v`; that is the
comparison the merge needs, and it is why the two isomorphisms here are not two different
unitors.

## References

* [Stacks Project, Tag 06YM](https://stacks.math.columbia.edu/tag/06YM)
* [Stacks Project, Tag 06YQ](https://stacks.math.columbia.edu/tag/06YQ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory

universe v u w

namespace Stacks.SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (R : Sheaf J CommRingCat.{max u v}) [HasWeakSheafify J AddCommGrpCat.{max u v}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]

attribute [local instance] _root_.SheafOfModules.monoidalCategorySheafTensor

/-- Tensoring on the right with the structure sheaf is, as a functor, the right-unitor functor
of the monoidal structure on `Mod(O)` re-seated on `Stacks.SheafOfModules.Tensor.sheafTensor`. The
  two sides
are equal, not merely isomorphic, by
`SheafOfModules.curriedTensor_sheafTensor` and `SheafOfModules.tensorUnit_sheafTensor`. -/
lemma sheafTensor_flip_obj_unit_eq :
    (Stacks.SheafOfModules.Tensor.sheafTensor R).flip.obj
        (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf R)) =
      tensorUnitRight (_root_.SheafOfModules.{max u v} (Stacks.SheafOfModules.Tensor.ringSheaf R))
        := by
  rw [← _root_.SheafOfModules.curriedTensor_sheafTensor R,
    ← _root_.SheafOfModules.tensorUnit_sheafTensor R]

/-- **The structure sheaf is the unit of `⊗_O`:** `F ⊗_O O ≅ F`, naturally in the sheaf of
modules `F`. -/
def sheafTensorUnitNatIso :
    (Stacks.SheafOfModules.Tensor.sheafTensor R).flip.obj
        (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf R)) ≅
      𝟭 (_root_.SheafOfModules.{max u v} (Stacks.SheafOfModules.Tensor.ringSheaf R)) :=
  eqToIso (sheafTensor_flip_obj_unit_eq R) ≪≫
    rightUnitorNatIso (_root_.SheafOfModules.{max u v} (Stacks.SheafOfModules.Tensor.ringSheaf R))

variable [(Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, max u v, max u v} R).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, max u v, max u v} R).obj M).Additive]
  [∀ (K L : CochainComplex (_root_.SheafOfModules.{max u v}
      (Stacks.SheafOfModules.Tensor.ringSheaf R)) ℤ),
    HomologicalComplex.HasMapBifunctor K L (Stacks.SheafOfModules.Tensor.sheafTensor R)
      (ComplexShape.up ℤ)]

open CochainComplex.KFlatBifunctor in
/-- The termwise complex `p ↦ K^p ⊗_O O` is `K`. -/
def rowComplexUnitIso
    (K : CochainComplex (_root_.SheafOfModules.{max u v}
      (Stacks.SheafOfModules.Tensor.ringSheaf R)) ℤ) :
    rowComplex (Stacks.SheafOfModules.Tensor.sheafTensor R) K
      (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf R)) ≅ K :=
  (NatIso.mapHomologicalComplex (sheafTensorUnitNatIso R) (ComplexShape.up ℤ)).app K ≪≫
    (Functor.mapHomologicalComplexIdIso _ (ComplexShape.up ℤ)).app K

/-- **The total tensor complex of `K` with the structure sheaf in degree zero is `K`.** The
double complex is concentrated in the row zero, where it is the termwise complex
(`CochainComplex.KFlatBifunctor.totalSingleIso`), and that termwise complex is `K` by
`rowComplexUnitIso`. -/
def tensorComplexUnitIso
    (K : CochainComplex (_root_.SheafOfModules.{max u v}
      (Stacks.SheafOfModules.Tensor.ringSheaf R)) ℤ) :
    ((Stacks.SheafOfModules.Tensor.tensorComplex R).obj K).obj
        ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj
          (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf R))) ≅ K :=
  CochainComplex.KFlatBifunctor.totalSingleIso (Stacks.SheafOfModules.Tensor.sheafTensor R) K
      (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf R)) ≪≫
    rowComplexUnitIso R K

/-! ### The unit law at a free universe of the sections -/

section FreeSections

variable (S : Sheaf J CommRingCat.{w}) [HasWeakSheafify J AddCommGrpCat.{w}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}]

attribute [local instance] Stacks.SheafOfModules.Tensor.ringSheafPresheafMonoidalCategory

/-- **The structure sheaf is the unit of `⊗_O`, at one sheaf of modules and with the universe of
the sections free:** `F ⊗_O O ≅ F`.

`F ⊗_O O` is the sheafification of `F.val ⊗_{pre} O`, which is `F.val` by the right unitor of
presheaves of modules, and the sheafification of `F.val` is `F` by the counit of the
sheafification adjunction. Neither step uses the monoidal structure on sheaves of modules, which
is where the pin `w = max u v` of `Stacks.SheafOfModules.sheafTensorUnitNatIso` comes from. -/
def sheafTensorUnitIsoFreeSections
    (F : _root_.SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf S)) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor S).flip.obj
        (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf S))).obj F ≅ F :=
  (PresheafOfModules.sheafification.{w}
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf S).obj)).mapIso
      (ρ_ ((_root_.SheafOfModules.forget (Stacks.SheafOfModules.Tensor.ringSheaf S)).obj F)) ≪≫
    _root_.SheafOfModules.sheafifyCounitIso (Stacks.SheafOfModules.Tensor.ringSheaf S) F

omit [HasWeakSheafify J AddCommGrpCat.{max u v}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}] in
/-- `Stacks.SheafOfModules.sheafTensorUnitIsoFreeSections` is natural in the sheaf of modules:
its two factors are, by the naturality of the presheaf right unitor and of the sheafification
counit. -/
theorem sheafTensorUnitIsoFreeSections_naturality
    {F G : _root_.SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf S)} (f : F ⟶ G) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor S).flip.obj
          (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf S))).map f ≫
        (sheafTensorUnitIsoFreeSections S G).hom =
      (sheafTensorUnitIsoFreeSections S F).hom ≫ f := by
  have key :
      (PresheafOfModules.sheafification.{w}
            (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf S).obj)).map
          ((_root_.SheafOfModules.forget (Stacks.SheafOfModules.Tensor.ringSheaf S)).map f ▷
            𝟙_ (PresheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf S).obj)) ≫
          ((PresheafOfModules.sheafification.{w}
              (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf S).obj)).map
            (ρ_ ((_root_.SheafOfModules.forget
              (Stacks.SheafOfModules.Tensor.ringSheaf S)).obj G)).hom ≫
            (_root_.SheafOfModules.sheafifyCounitIso
              (Stacks.SheafOfModules.Tensor.ringSheaf S) G).hom) =
        ((PresheafOfModules.sheafification.{w}
              (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf S).obj)).map
            (ρ_ ((_root_.SheafOfModules.forget
              (Stacks.SheafOfModules.Tensor.ringSheaf S)).obj F)).hom ≫
          (_root_.SheafOfModules.sheafifyCounitIso
            (Stacks.SheafOfModules.Tensor.ringSheaf S) F).hom) ≫ f := by
    rw [← Functor.map_comp_assoc, MonoidalCategory.rightUnitor_naturality,
      Functor.map_comp_assoc, _root_.SheafOfModules.sheafifyCounitIso_naturality]
    exact (Category.assoc _ _ _).symm
  exact key

/-- **The structure sheaf is the unit of `⊗_O`, with the universe of the sections free:**
`F ⊗_O O ≅ F`, naturally in the sheaf of modules `F`.

This is `Stacks.SheafOfModules.sheafTensorUnitNatIso` with the pin `w = max u v` lifted; see the
implementation notes. -/
def sheafTensorUnitNatIsoFreeSections :
    (Stacks.SheafOfModules.Tensor.sheafTensor S).flip.obj
        (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf S)) ≅
      𝟭 (_root_.SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf S)) :=
  NatIso.ofComponents (sheafTensorUnitIsoFreeSections S)
    (sheafTensorUnitIsoFreeSections_naturality S)

-- `Mod(O)` is abelian at a free sections universe only under `HasSheafify`; at `max u v`
-- Mathlib's size-restricted instance supplies it, which is why the pinned statements above need
-- `HasWeakSheafify` alone.
variable [HasSheafify J AddCommGrpCat.{w}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, w, w} S).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, w, w} S).obj M).Additive]
  [∀ (K L : CochainComplex (_root_.SheafOfModules.{w}
      (Stacks.SheafOfModules.Tensor.ringSheaf S)) ℤ),
    HomologicalComplex.HasMapBifunctor K L (Stacks.SheafOfModules.Tensor.sheafTensor S)
      (ComplexShape.up ℤ)]

open CochainComplex.KFlatBifunctor in
/-- The termwise complex `p ↦ K^p ⊗_O O` is `K`, with the universe of the sections free. -/
def rowComplexUnitIsoFreeSections
    (K : CochainComplex (_root_.SheafOfModules.{w}
      (Stacks.SheafOfModules.Tensor.ringSheaf S)) ℤ) :
    rowComplex (Stacks.SheafOfModules.Tensor.sheafTensor S) K
      (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf S)) ≅ K :=
  (NatIso.mapHomologicalComplex (sheafTensorUnitNatIsoFreeSections S)
      (ComplexShape.up ℤ)).app K ≪≫
    (Functor.mapHomologicalComplexIdIso _ (ComplexShape.up ℤ)).app K

omit [HasWeakSheafify J AddCommGrpCat.{max u v}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}] in
open CochainComplex.KFlatBifunctor in
/-- **The structure sheaf placed in degree zero is a K-flat complex.** By the base case of
Stacks 06YQ it suffices that `K ↦ K ⊗_O O` carry acyclic complexes to acyclic complexes, and
that functor is the identity by `rowComplexUnitIsoFreeSections`. -/
theorem isKFlat_single_unit :
    IsKFlat S ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj
      (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf S))) :=
  kFlat_single_of_exact (Stacks.SheafOfModules.Tensor.sheafTensor S) _ 0
    (fun G hG n =>
      HomologicalComplex.ExactAt.of_iso (hG n) (rowComplexUnitIsoFreeSections S G).symm)

omit [HasWeakSheafify J AddCommGrpCat.{max u v}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}] in
open CochainComplex.KFlatBifunctor in
/-- **The structure sheaf placed in any single degree `q` is a K-flat complex**, by the base case
of Stacks 06YQ exactly as `isKFlat_single_unit`, which is the case `q = 0`. -/
theorem isKFlat_single_obj_unit (q : ℤ) :
    IsKFlat S ((HomologicalComplex.single _ (ComplexShape.up ℤ) q).obj
      (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf S))) :=
  kFlat_single_of_exact (Stacks.SheafOfModules.Tensor.sheafTensor S) _ q
    (fun G hG n =>
      HomologicalComplex.ExactAt.of_iso (hG n) (rowComplexUnitIsoFreeSections S G).symm)

/-- **The total tensor complex of `K` with the structure sheaf in degree zero is `K`**, with the
universe of the sections free. -/
def tensorComplexUnitIsoFreeSections
    (K : CochainComplex (_root_.SheafOfModules.{w}
      (Stacks.SheafOfModules.Tensor.ringSheaf S)) ℤ) :
    ((Stacks.SheafOfModules.Tensor.tensorComplex S).obj K).obj
        ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj
          (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf S))) ≅ K :=
  CochainComplex.KFlatBifunctor.totalSingleIso (Stacks.SheafOfModules.Tensor.sheafTensor S) K
      (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf S)) ≪≫
    rowComplexUnitIsoFreeSections S K

end FreeSections

end Stacks.SheafOfModules

end
