module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.CategoryTheory.Limits.Shapes.ConcreteCategory
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Mono
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Divisors.Meromorphic.BasicOpenVanishing
public import StacksFrontier.AlgebraicGeometry.Divisors.Meromorphic.MeromorphicSections
public import StacksFrontier.AlgebraicGeometry.SheafifyMono.RestrictScalars
public import StacksFrontier.AlgebraicGeometry.SheafifyMono.TotalQuotient
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposModules

/-!
# Denominators of a meromorphic section

Let `X` be a scheme, `L` a sheaf of `𝒪_X`-modules and `s` a meromorphic section of `L`, that is,
a global section of the sheaf `K_X(L)` of meromorphic sections of `L`.  Multiplication by `s` is
a morphism `𝒪_X ⟶ K_X(L)`, and the canonical map `L ⟶ K_X(L)` is the unit of extension of
scalars along `𝒪_X ⟶ K_X`.  The *denominator ideal* of `s` is the fibre product of those two
morphisms: a section `f` of `𝒪_X` lies in it exactly when `f · s` is a section of `L`.

## Main definitions

* `Stacks.DenominatorIdeal.denominatorIdeal`: the fibre product of multiplication by `s` and of
  the canonical map from `L`.
* `Stacks.DenominatorIdeal.denominatorIdealι`: its first projection, the inclusion in the
  structure sheaf.
* `Stacks.DenominatorIdeal.denominatorIdealMul`: its second projection, multiplication by `s`.

## Main results

* `Stacks.DenominatorIdeal.denominatorIdeal_sections`: the denominator rule.  On every open set,
  a section of the structure sheaf is in the image of the inclusion exactly when its product with
  the meromorphic section comes from a section of `L`.
* `Stacks.DenominatorIdeal.mono_sectionMap`: multiplication by a regular meromorphic section is a
  monomorphism from the structure sheaf.
* `Stacks.DenominatorIdeal.denominatorIdeal_section_mono`: multiplication by a regular meromorphic
  section embeds its denominator ideal in `L`.

## References

* [Stacks Project, Tag 02P0](https://stacks.math.columbia.edu/tag/02P0)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace Stacks.DenominatorIdeal

variable (X : Scheme.{u})

/-- The structure sheaf of a scheme, read as a sheaf of rings. -/
abbrev O : Sheaf (Opens.grothendieckTopology X) RingCat.{u} :=
  Stacks.Sheaves.Differentials.ringSheaf.{u, u} (C := Opens X) (J := Opens.grothendieckTopology X)
    X.sheaf

/-- The sheaf of total quotient rings of a scheme, read as a sheaf of rings. -/
abbrev KRing : Sheaf (Opens.grothendieckTopology X) RingCat.{u} :=
  Stacks.Sheaves.Differentials.ringSheaf.{u, u} (C := Opens X) (J := Opens.grothendieckTopology X)
    (totalQuotientSheaf X.sheaf)

/-- The sheaf `K_X(L)` of meromorphic sections of `L`. -/
abbrev K (L : SheafOfModules.{u} (O X)) : SheafOfModules.{u} (KRing X) :=
  meromorphicSectionSheaf.{u, u} X.sheaf L

/-- The morphism of sheaves of rings underlying the canonical map to the sheaf of total
quotient rings. -/
abbrev ringSheafMap : O X ⟶ KRing X :=
  (sheafCompose (Opens.grothendieckTopology X)
    (forget₂ CommRingCat.{u} RingCat.{u})).map (toTotalQuotientSheaf X.sheaf)

/-- The sheaf of meromorphic sections of `L`, read as a sheaf of `𝒪_X`-modules. -/
def kAsOModule (L : SheafOfModules.{u} (O X)) : SheafOfModules.{u} (O X) :=
  (SheafOfModules.restrictScalars (ringSheafMap X)).obj (K X L)

/-- The canonical morphism from `L` to its sheaf of meromorphic sections: the unit of extension
of scalars along `𝒪_X ⟶ K_X`. -/
def toK (L : SheafOfModules.{u} (O X)) : L ⟶ kAsOModule X L :=
  (Stacks.Sheaves.RingedToposModules.extendRestrictScalarsAdjunction
    (Opens.grothendieckTopology X) (toTotalQuotientSheaf X.sheaf).hom
    (O X).property (KRing X).property).unit.app L

/-- Multiplication by a meromorphic section, as a morphism from the structure sheaf to the sheaf
of meromorphic sections. -/
def sectionMap (L : SheafOfModules.{u} (O X)) (s : MeromorphicSection.{u, u} X.sheaf L) :
    SheafOfModules.unit (O X) ⟶ kAsOModule X L :=
  (kAsOModule X L).unitHomEquiv.symm s

variable (L : SheafOfModules.{u} (O X)) (s : MeromorphicSection.{u, u} X.sheaf L)

/-- The sheaf of denominators of a meromorphic section, as the fibre product of multiplication by
the section and of the canonical map from `L`. -/
@[ega "IV 20.2.14"]
def denominatorIdeal : SheafOfModules.{u} (O X) := pullback (sectionMap X L s) (toK X L)

/-- Inclusion of the denominator ideal in the structure sheaf. -/
def denominatorIdealι : denominatorIdeal X L s ⟶ SheafOfModules.unit (O X) := pullback.fst _ _

/-- Multiplication by the meromorphic section on its denominator ideal. -/
def denominatorIdealMul : denominatorIdeal X L s ⟶ L := pullback.snd _ _

/-- The commuting square of the fibre product, read on an open set and at a section of the
denominator ideal there. -/
lemma app_condition (U : Opens X) (d : (denominatorIdeal X L s).val.obj (op U)) :
    (sectionMap X L s).val.app (op U) ((denominatorIdealι X L s).val.app (op U) d) =
      (toK X L).val.app (op U) ((denominatorIdealMul X L s).val.app (op U) d) :=
  ConcreteCategory.congr_hom
    (congrArg (fun φ : denominatorIdeal X L s ⟶ kAsOModule X L => φ.val.app (op U))
      (pullback.condition (f := sectionMap X L s) (g := toK X L))) d

/-- A section of the structure sheaf is a denominator of the meromorphic section `s` exactly when
its product with `s` is a section of `L`. -/
@[stacks 02P0 "the denominator rule"]
theorem denominatorIdeal_sections (U : Opens X)
    (f : (SheafOfModules.unit (O X)).val.obj (op U)) :
    (∃ d : (denominatorIdeal X L s).val.obj (op U),
      (denominatorIdealι X L s).val.app (op U) d = f) ↔
    (∃ t : L.val.obj (op U),
      (sectionMap X L s).val.app (op U) f =
        (toK X L).val.app (op U) t) := by
  constructor
  · rintro ⟨d, rfl⟩
    exact ⟨(denominatorIdealMul X L s).val.app (op U) d, app_condition X L s U d⟩
  · rintro ⟨t, ht⟩
    exact ⟨(PreservesPullback.iso (SheafOfModules.evaluation (O X) (op U))
      (sectionMap X L s) (toK X L)).inv (Limits.Concrete.pullbackMk _ _ f t ht),
      (ConcreteCategory.congr_hom
        (PreservesPullback.iso_inv_fst (SheafOfModules.evaluation (O X) (op U))
          (sectionMap X L s) (toK X L)) _).trans
        (Limits.Concrete.pullbackMk_fst _ _ f t ht)⟩

/-- Multiplication by a regular meromorphic section is injective on the sections over every open
set, as a map from the sections of the sheaf of total quotient rings. -/
lemma injective_regularSection_app (hs : IsRegularMeromorphicSection X.sheaf L s)
    (U : (Opens X)ᵒᵖ) :
    Function.Injective (((K X L).unitHomEquiv.symm s).val.app U) := by
  have hq : Mono ((K X L).unitHomEquiv.symm s) := hs
  have happ : Mono (((SheafOfModules.forget (KRing X) ⋙
      PresheafOfModules.toPresheaf (KRing X).obj).map
        ((K X L).unitHomEquiv.symm s)).app U) := inferInstance
  exact fun _ _ hab =>
    (ConcreteCategory.mono_iff_injective_of_preservesPullback _).mp happ hab

/-- On an open set, multiplication by a meromorphic section is the ring map to the total quotient
sheaf followed by multiplication by that section over the total quotient sheaf. -/
lemma sectionMap_app_apply (U : (Opens X)ᵒᵖ) (f : (SheafOfModules.unit (O X)).val.obj U) :
    (sectionMap X L s).val.app U f =
      ((K X L).unitHomEquiv.symm s).val.app U
        ((toTotalQuotientSheaf X.sheaf).hom.app U f) := rfl

/-- Multiplication by a regular meromorphic section is a monomorphism from the structure
sheaf. -/
lemma mono_sectionMap (hs : IsRegularMeromorphicSection X.sheaf L s) :
    Mono (sectionMap X L s) :=
  Functor.mono_of_mono_map
    (SheafOfModules.forget (O X) ⋙ PresheafOfModules.toPresheaf (O X).obj)
    ((NatTrans.mono_iff_mono_app _).mpr fun U =>
      ConcreteCategory.mono_of_injective _ fun _ _ hab =>
        toTotalQuotientSheaf_app_injective X U.unop
          (injective_regularSection_app X L s hs U hab))

/-- Multiplication by a regular meromorphic section embeds its denominator ideal in `L`. -/
@[stacks 02P0 "multiplication is injective"]
theorem denominatorIdeal_section_mono (hs : IsRegularMeromorphicSection X.sheaf L s) :
    Mono (denominatorIdealMul X L s) :=
  have := mono_sectionMap X L s hs
  pullback.snd_of_mono

end Stacks.DenominatorIdeal
