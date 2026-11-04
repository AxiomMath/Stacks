module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposModules
public import StacksFrontier.AlgebraicGeometry.Divisors.Meromorphic.BasicOpenVanishing
public import StacksFrontier.AlgebraicGeometry.Divisors.Meromorphic.MeromorphicSections
public import StacksFrontier.Topology.Sheaves.Modules.Invertible

/-!
# The ideal of denominators of a meromorphic section

Let `X` be a scheme, `L` a sheaf of `𝒪_X`-modules and `s` a meromorphic section of `L`, that
is, a global section of `K_X(L) = L ⊗_{𝒪_X} K_X`. The *ideal of denominators* of `s` is the
sheaf of ideals
`I(V) = {f ∈ 𝒪_X(V) | f s ∈ L(V)}`,
realised here as the fibre product of `𝒪_X` and `L` over `K_X(L)`, the two maps to `K_X(L)`
being multiplication by `s` and the canonical map `L ⟶ K_X(L)`. Its first projection is the
inclusion of the ideal in the structure sheaf and its second projection is multiplication by
`s`.

## Main definitions

* `AlgebraicGeometry.meromorphicSectionSheafAsModule`: `K_X(L)`, read as a sheaf of
  `𝒪_X`-modules by restriction of scalars along `𝒪_X ⟶ K_X`.
* `AlgebraicGeometry.toMeromorphicSectionSheafAsModule`: the canonical `𝒪_X`-linear map
  `L ⟶ K_X(L)`, the unit of extension of scalars along `𝒪_X ⟶ K_X`.
* `AlgebraicGeometry.meromorphicSectionMul`: multiplication by a meromorphic section, as a map
  `𝒪_X ⟶ K_X(L)`.
* `AlgebraicGeometry.denominatorIdeal`: the sheaf of denominators, as the fibre product of
  those two maps, with its two projections `AlgebraicGeometry.denominatorIdealι` and
  `AlgebraicGeometry.denominatorIdealMul`.
* `AlgebraicGeometry.denominatorIdealData`: the same ideal presented as affine-local
  ideal-sheaf data, the form in which a blowup consumes it.

## Main results

* `AlgebraicGeometry.denominatorIdeal_section_mono`: multiplication by a regular meromorphic
  section is injective on its ideal of denominators.
* `AlgebraicGeometry.toMeromorphicSectionSheafAsModule_val_app_apply`: the sections of the
  canonical map `L ⟶ K_X(L)` send `x` to the image of `1 ⊗ x` in the sheafification.
* `CategoryTheory.SheafOfModules.mono_of_forall_app_injective` and
  `CategoryTheory.SheafOfModules.app_injective_of_mono`: a morphism of sheaves of modules is a
  monomorphism exactly when it is injective on sections over every object.

## Implementation notes

The ideal is a categorical fibre product rather than a sectionwise-defined subsheaf, so that
the two maps of the source are literally its projections and no separate sheaf condition has to
be checked. Extension of scalars along `𝒪_X ⟶ K_X` is
`Stacks.Sheaves.ChangeOfRings.changeOfRings`, which is what
`AlgebraicGeometry.meromorphicSectionSheaf` is built from; the unit used here is the one of
`Stacks.Sheaves.RingedToposModules.extendRestrictScalarsAdjunction`, whose left adjoint is that
same functor. That adjunction is a term rather than a choice of inhabitant of a `Nonempty`, so
its sections are computable: `toMeromorphicSectionSheafAsModule_val_app_apply` evaluates them.

Injectivity of multiplication by `s` reduces to injectivity on sections over every open, where
it factors as the canonical map `𝒪_X(V) → K_X(V)`, injective by
`AlgebraicGeometry.toTotalQuotientSheaf_app_injective`, followed by multiplication by `s` on
`K_X(V)`, injective because `s` is regular. Invertibility of `L` is therefore not needed for
this clause, but is kept as a hypothesis to match the source.

The other assertions of Tag 02P0 — quasi-coherence of the ideal, injectivity of the inclusion,
and the nowhere dense closed supports of the two cokernels — are **not** in this file.
Injectivity of the inclusion is injectivity of `toMeromorphicSectionSheafAsModule`, which for an
invertible `L` is the image under `L ⊗ -` of the injection `𝒪_X ⟶ K_X`; what is missing for it
is the comparison of extension of scalars with the sheafified tensor product, that is, a natural
isomorphism between `Stacks.Sheaves.ChangeOfRings.changeOfRings` and
`AlgebraicGeometry.SheafOfModules.tensorLeftFunctor` by the target ring sheaf. The other two
rest on the affine-local description of the ideal.

## References

* [Stacks Project, Tag 02P0](https://stacks.math.columbia.edu/tag/02P0)
* [Stacks Project, Tag 02P1](https://stacks.math.columbia.edu/tag/02P1)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open scoped TensorProduct

universe u

namespace CategoryTheory.SheafOfModules

/-- A morphism of sheaves of modules is a monomorphism iff it is injective on all sections. -/
private theorem mono_iff_forall_app_injective {C : Type u} [SmallCategory C]
    {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
    [HasWeakSheafify J AddCommGrpCat.{u}]
    {M N : SheafOfModules.{u} R} (f : M ⟶ N) :
    Mono f ↔ ∀ V, Function.Injective ((f.val.app V).hom) := by
  rw [← (SheafOfModules.toSheaf R).mono_map_iff_mono, Sheaf.Hom.mono_iff_presheaf_mono,
    CategoryTheory.NatTrans.mono_iff_mono_app]
  exact forall_congr' fun V =>
    ConcreteCategory.mono_iff_injective_of_preservesPullback
      (((SheafOfModules.toSheaf R).map f).hom.app V)

/-- A morphism of sheaves of modules which is injective on sections over every object is a
monomorphism. -/
theorem mono_of_forall_app_injective {C : Type u} [SmallCategory C]
    {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
    [HasWeakSheafify J AddCommGrpCat.{u}]
    {M N : SheafOfModules.{u} R} (f : M ⟶ N)
    (h : ∀ V, Function.Injective ((f.val.app V).hom)) : Mono f :=
  (mono_iff_forall_app_injective f).2 h

/-- A monomorphism of sheaves of modules is injective on sections over every object. -/
theorem app_injective_of_mono {C : Type u} [SmallCategory C]
    {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
    [HasWeakSheafify J AddCommGrpCat.{u}]
    {M N : SheafOfModules.{u} R} {f : M ⟶ N} (hf : Mono f) (V : Cᵒᵖ) :
    Function.Injective ((f.val.app V).hom) :=
  (mono_iff_forall_app_injective f).1 hf V

end CategoryTheory.SheafOfModules

namespace AlgebraicGeometry

variable (X : Scheme.{u})

/-- The morphism of sheaves of rings along which scalars are extended to form the meromorphic
sections of a module: the canonical map `𝒪_X ⟶ K_X`, read in `RingCat`. -/
abbrev toTotalQuotientRingSheaf :
    Stacks.Sheaves.Differentials.ringSheaf (J := Opens.grothendieckTopology X) X.sheaf ⟶
      Stacks.Sheaves.Differentials.ringSheaf (J := Opens.grothendieckTopology X)
        X.totalQuotientSheaf :=
  Stacks.Sheaves.RingedToposModules.commRingSheafMap (Opens.grothendieckTopology X)
    X.toTotalQuotientSheaf.hom
    (Stacks.Sheaves.Differentials.ringSheaf (J := Opens.grothendieckTopology X) X.sheaf).property
    (Stacks.Sheaves.Differentials.ringSheaf (J := Opens.grothendieckTopology X)
      X.totalQuotientSheaf).property

/-- The sheaf `K_X(L)` of meromorphic sections of `L`, read as a sheaf of `𝒪_X`-modules by
restriction of scalars along `𝒪_X ⟶ K_X`. -/
def meromorphicSectionSheafAsModule
    (L : SheafOfModules.{u}
      (Stacks.Sheaves.Differentials.ringSheaf (J := Opens.grothendieckTopology X) X.sheaf)) :
    SheafOfModules.{u} (Stacks.Sheaves.Differentials.ringSheaf (J := Opens.grothendieckTopology X)
      X.sheaf) :=
  (SheafOfModules.restrictScalars (toTotalQuotientRingSheaf X)).obj
    (meromorphicSectionSheaf X.sheaf L)

/-- The canonical `𝒪_X`-linear map `L ⟶ K_X(L)`, the unit of extension of scalars along
`𝒪_X ⟶ K_X`. The source regards `L(V)` as a submodule of `K_X(L)(V)` along it. -/
def toMeromorphicSectionSheafAsModule
    (L : SheafOfModules.{u}
      (Stacks.Sheaves.Differentials.ringSheaf (J := Opens.grothendieckTopology X) X.sheaf)) :
    L ⟶ meromorphicSectionSheafAsModule X L :=
  (Stacks.Sheaves.RingedToposModules.extendRestrictScalarsAdjunction
    (Opens.grothendieckTopology X) X.toTotalQuotientSheaf.hom
    (Stacks.Sheaves.Differentials.ringSheaf (J := Opens.grothendieckTopology X) X.sheaf).property
    (Stacks.Sheaves.Differentials.ringSheaf (J := Opens.grothendieckTopology X)
      X.totalQuotientSheaf).property).unit.app L

/-- The sections of `toMeromorphicSectionSheafAsModule` over an open `V`: a section `x` of `L`
is sent to the image of `1 ⊗ x` under the map to the sheafification, where `1` is the unit of
`K_X(V)` and the tensor product is over `𝒪_X(V)`. -/
theorem toMeromorphicSectionSheafAsModule_val_app_apply
    (L : SheafOfModules.{u}
      (Stacks.Sheaves.Differentials.ringSheaf (J := Opens.grothendieckTopology X) X.sheaf))
    (V : (Opens X)ᵒᵖ) (x : L.val.obj V) :
    ((toMeromorphicSectionSheafAsModule X L).val.app V).hom x =
      letI := (X.toTotalQuotientSheaf.hom.app V).hom.toAlgebra
      (CategoryTheory.toSheafify (Opens.grothendieckTopology X)
          ((Stacks.PresheafOfModules.ChangeOfRings.changeOfRings X.toTotalQuotientSheaf.hom).obj
            L.val).presheaf).app V
        ((1 : X.totalQuotientSheaf.obj.obj V) ⊗ₜ[X.sheaf.obj.obj V] x) :=
  Stacks.Sheaves.RingedToposModules.extendRestrictScalarsAdjunction_unit_app_val_app_apply
    (Opens.grothendieckTopology X) X.toTotalQuotientSheaf.hom
    (Stacks.Sheaves.Differentials.ringSheaf (J := Opens.grothendieckTopology X) X.sheaf).property
    (Stacks.Sheaves.Differentials.ringSheaf (J := Opens.grothendieckTopology X)
      X.totalQuotientSheaf).property L V x

/-- Multiplication by a meromorphic section `s` of `L`, as a map `𝒪_X ⟶ K_X(L)` of sheaves of
`𝒪_X`-modules. -/
def meromorphicSectionMul
    (L : SheafOfModules.{u}
      (Stacks.Sheaves.Differentials.ringSheaf (J := Opens.grothendieckTopology X) X.sheaf))
    (s : MeromorphicSection X.sheaf L) :
    SheafOfModules.unit (Stacks.Sheaves.Differentials.ringSheaf (J := Opens.grothendieckTopology X)
      X.sheaf) ⟶
      meromorphicSectionSheafAsModule X L :=
  (meromorphicSectionSheafAsModule X L).unitHomEquiv.symm s

/-- The sheaf of denominators of a meromorphic section, as the fibre product of the structure
sheaf and `L` over `K_X(L)`. Its sections over `V` are the pairs `(f, t)` with `f s = t` in
`K_X(L)(V)`, so the image of its first projection is `{f ∈ 𝒪_X(V) | f s ∈ L(V)}`. -/
@[stacks 02P1 "the ideal sheaf of denominators of `s`", ega "IV 20.2.14" "definition"]
def denominatorIdeal
    (L : SheafOfModules.{u}
      (Stacks.Sheaves.Differentials.ringSheaf (J := Opens.grothendieckTopology X) X.sheaf))
    (s : MeromorphicSection X.sheaf L) :
    SheafOfModules.{u} (Stacks.Sheaves.Differentials.ringSheaf (J := Opens.grothendieckTopology X)
      X.sheaf) :=
  pullback (meromorphicSectionMul X L s) (toMeromorphicSectionSheafAsModule X L)

/-- Inclusion of the denominator ideal in the structure sheaf, the map `1` of the source. -/
def denominatorIdealι
    (L : SheafOfModules.{u}
      (Stacks.Sheaves.Differentials.ringSheaf (J := Opens.grothendieckTopology X) X.sheaf))
    (s : MeromorphicSection X.sheaf L) :
    denominatorIdeal X L s ⟶
      SheafOfModules.unit (Stacks.Sheaves.Differentials.ringSheaf (J := Opens.grothendieckTopology
        X) X.sheaf) :=
  pullback.fst _ _

/-- Multiplication by the meromorphic section on its denominator ideal, the map `s` of the
source. -/
def denominatorIdealMul
    (L : SheafOfModules.{u}
      (Stacks.Sheaves.Differentials.ringSheaf (J := Opens.grothendieckTopology X) X.sheaf))
    (s : MeromorphicSection X.sheaf L) : denominatorIdeal X L s ⟶ L :=
  pullback.snd _ _

/-- The denominator ideal as affine-local ideal-sheaf data. -/
def denominatorIdealData
    (L : SheafOfModules.{u}
      (Stacks.Sheaves.Differentials.ringSheaf (J := Opens.grothendieckTopology X) X.sheaf))
    (s : MeromorphicSection X.sheaf L) : X.IdealSheafData :=
  Scheme.IdealSheafData.ofIdeals fun U =>
    ((denominatorIdealι X L s).val.app (op U.1)).hom.range

/-- On sections over an open set, multiplication by a meromorphic section is the canonical map
from the structure sheaf to the sheaf of total quotient rings followed by multiplication by the
section on meromorphic sections. -/
theorem meromorphicSectionMul_val_app
    (L : SheafOfModules.{u}
      (Stacks.Sheaves.Differentials.ringSheaf (J := Opens.grothendieckTopology X) X.sheaf))
    (s : MeromorphicSection X.sheaf L) (V : (Opens X)ᵒᵖ)
    (f : (Stacks.Sheaves.Differentials.ringSheaf (J := Opens.grothendieckTopology X)
      X.sheaf).obj.obj V) :
    ((meromorphicSectionMul X L s).val.app V).hom f
      = (((meromorphicSectionSheaf X.sheaf L).unitHomEquiv.symm s).val.app V).hom
          (((toTotalQuotientRingSheaf X).hom.app V).hom f) := rfl

/-- **Stacks Project, Tag 02P0**, injectivity of multiplication by the section. For a regular
meromorphic section `s` of `L`, multiplication by `s` embeds the ideal of denominators of `s`
in `L`. -/
@[stacks 02P0 "multiplication is injective"]
theorem denominatorIdeal_section_mono
    (L : SheafOfModules.{u}
      (Stacks.Sheaves.Differentials.ringSheaf (J := Opens.grothendieckTopology X) X.sheaf))
    (s : MeromorphicSection X.sheaf L)
    (_hL : AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj
      (Stacks.Sheaves.Differentials.ringSheaf (J := Opens.grothendieckTopology X) X.sheaf).property
        L)
    (hs : IsRegularMeromorphicSection X.sheaf L s) :
    Mono (denominatorIdealMul X L s) := by
  have hmul : Mono (meromorphicSectionMul X L s) := by
    refine SheafOfModules.mono_of_forall_app_injective _ fun V a b hab => ?_
    refine toTotalQuotientSheaf_app_injective X V.unop
      (SheafOfModules.app_injective_of_mono hs V ?_)
    exact (meromorphicSectionMul_val_app X L s V a).symm.trans
      (hab.trans (meromorphicSectionMul_val_app X L s V b))
  exact pullback.snd_of_mono

end AlgebraicGeometry
