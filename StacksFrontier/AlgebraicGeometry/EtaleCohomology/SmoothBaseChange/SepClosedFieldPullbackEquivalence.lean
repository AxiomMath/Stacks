module

public import Mathlib.CategoryTheory.Sites.LocalSite
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ConstantRingDerivedEquivalence
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.BaseChangeCondition
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GeometricFibreBaseChangeSections
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmoothBaseChange.SepClosedFieldConstantSheaf
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmoothBaseChange.FirstFailureFunctionField

/-!
# Pullback between spectra of separably closed fields is an equivalence

Let `k` be a separably closed field. Every covering of the terminal object `Spec k` of the small
étale site of `Spec k` contains a section, so the only covering sieve of the terminal object is the
maximal one: the site is a *local site* in the sense of
`CategoryTheory.GrothendieckTopology.IsLocalSite`.
On a local site the constant sheaf functor is fully faithful, and every abelian sheaf on
`(Spec k)_étale` is constant (`Stacks.EtaleCohomology.SepClosedField.isIso_counit_app`), so the
constant sheaf functor `Ab ⥤ Sheaf (Spec k)_étale` is an equivalence.

For an extension `K/k` of separably closed fields, inverse image along `g : Spec K ⟶ Spec k`
carries the constant sheaf to the constant sheaf, hence is an equivalence too, and so its bounded
below derived functor is fully faithful. This is the step of [Stacks, Tag 0F0B] which turns the
base change map over `Spec K ⟶ Spec k` into a statement about cohomology.

## Main results

All names are in the namespace `Stacks.EtaleCohomology`.

* `SepClosedField.isLocalSite` — the small étale site of the spectrum of a separably closed field
  is a local site.
* `SepClosedField.constantSheaf_isEquivalence` — the constant sheaf functor is an equivalence.
* `smallEtalePullbackAb_isEquivalence_of_isSepClosed` — inverse image along `Spec K ⟶ Spec k` is
  an equivalence.
* `rightDerivedFunctorPlusFullyFaithfulOfIsEquivalence` — the bounded below derived functor of an
  equivalence of abelian categories is fully faithful.
* `bijective_smallEtalePullbackAb_rightDerivedFunctorPlus_map_of_isSepClosed` — the derived
  inverse image along `Spec K ⟶ Spec k` is bijective on morphisms.

## References

* [Stacks Project, Tag 0F0B](https://stacks.math.columbia.edu/tag/0F0B)
* [Stacks Project, Tag 04JQ](https://stacks.math.columbia.edu/tag/04JQ)

Tags covered: none.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

section DerivedEquivalence

variable {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
  [HasDerivedCategory A] [HasDerivedCategory B] [EnoughInjectives A]

/-- **The bounded below derived functor of an equivalence is fully faithful.** An equivalence of
abelian categories is exact, so its right derived functor is its action on bounded below derived
categories, the restriction of its action on unbounded derived categories, which is an equivalence.
-/
def rightDerivedFunctorPlusFullyFaithfulOfIsEquivalence (L : A ⥤ B) [L.IsEquivalence]
    [L.Additive] : L.rightDerivedFunctorPlus.FullyFaithful :=
  haveI : L.asEquivalence.functor.Additive := ‹L.Additive›
  haveI : L.mapDerivedCategory.IsEquivalence :=
    Stacks.DerivedCategory.mapDerivedCategory_isEquivalence L.asEquivalence
  ((((DerivedCategory.TStructure.t.plus.fullyFaithfulι).comp
      (Functor.FullyFaithful.ofFullyFaithful L.mapDerivedCategory)).ofIso
        (ObjectProperty.liftCompιIso _ _ _).symm).ofCompFaithful).ofIso
    (Stacks.DerivedFunctor.exactMapDerivedCategoryPlusIso L)

end DerivedEquivalence

namespace SepClosedField

variable (Ω : Type u) [Field Ω] [IsSepClosed Ω]

/-- Every covering sieve of the terminal object of `(Spec Ω)_étale` contains the identity: the
point of `Spec Ω` lifts along a member of the covering, and the lift is a section. -/
theorem id_mem_of_mem {R : Sieve (terminal Ω)}
    (hR : R ∈ smallEtaleTopology (Spec (.of Ω)) (terminal Ω)) : R.arrows (𝟙 _) := by
  obtain ⟨Y, g, hg, ψ, -⟩ :=
    (Scheme.pointSmallEtale (𝟙 (Spec (.of Ω)))).jointly_surjective R hR (𝟙 _)
  have hw : ψ.left ≫ Y.hom = (terminal Ω).hom := (by simpa using Over.w ψ : _ = 𝟙 _)
  rw [← (terminalIsTerminal Ω).hom_ext
    ((MorphismProperty.Over.homMk ψ.left hw : terminal Ω ⟶ Y) ≫ g) (𝟙 _)]
  exact R.downward_closed hg _

/-- Every covering sieve of `(Spec Ω)_étale` contains every morphism out of the terminal object. -/
theorem arrows_of_mem {X : (Spec (.of Ω)).Etale} (f : terminal Ω ⟶ X) {R : Sieve X}
    (hR : R ∈ smallEtaleTopology (Spec (.of Ω)) X) : R.arrows f := by
  simpa using id_mem_of_mem Ω ((smallEtaleTopology _).pullback_stable f hR)

/-- **The small étale site of the spectrum of a separably closed field is a local site.** -/
instance isLocalSite : (smallEtaleTopology (Spec (.of Ω))).IsLocalSite where
  __ := (terminalIsTerminal Ω).hasTerminal
  eq_top_of_mem S hS := by
    let e := terminalIsoIsTerminal (terminalIsTerminal Ω)
    rw [← Sieve.id_mem_iff_eq_top, ← e.hom_inv_id]
    exact S.downward_closed (arrows_of_mem Ω e.inv hS) e.hom

/-- Every abelian sheaf on `(Spec Ω)_étale` is constant. -/
instance constantSheaf_essSurj :
    (constantSheaf (smallEtaleTopology (Spec (.of Ω))) AddCommGrpCat.{u + 1}).EssSurj where
  mem_essImage F := ⟨_, ⟨asIso ((constantSheafAdj (smallEtaleTopology (Spec (.of Ω)))
    AddCommGrpCat.{u + 1} (terminalIsTerminal Ω)).counit.app F)⟩⟩

/-- **The constant sheaf functor `Ab ⥤ Sheaf (Spec Ω)_étale` is an equivalence.** It is fully
faithful because the site is local, and essentially surjective because every sheaf is constant. -/
instance constantSheaf_isEquivalence :
    (constantSheaf (smallEtaleTopology (Spec (.of Ω))) AddCommGrpCat.{u + 1}).IsEquivalence where

end SepClosedField

section Pullback

variable {k K : Type u} [Field k] [Field K] [IsSepClosed k] [IsSepClosed K]
  (g : Spec (.of K) ⟶ Spec (.of k))

/-- **Inverse image along `Spec K ⟶ Spec k` is an equivalence**, for separably closed fields: it
carries the constant sheaf functor of `Spec k`, an equivalence, to that of `Spec K`. -/
instance smallEtalePullbackAb_isEquivalence_of_isSepClosed :
    (smallEtalePullbackAb g).IsEquivalence := by
  have : (constantSheaf (smallEtaleTopology (Spec (.of k))) AddCommGrpCat.{u + 1} ⋙
      smallEtalePullbackAb g).IsEquivalence :=
    Functor.isEquivalence_of_iso (FirstFailureFunctionField.smallEtalePullbackAbConstantIso g).symm
  exact Functor.isEquivalence_of_comp_left
    (constantSheaf (smallEtaleTopology (Spec (.of k))) AddCommGrpCat.{u + 1}) _

/-- **Pullback from `Spec k` to `Spec K` is bijective on morphisms of `D⁺`**, for separably
closed fields: it is an equivalence on abelian sheaves, so its bounded below derived functor is
fully faithful. -/
theorem bijective_smallEtalePullbackAb_rightDerivedFunctorPlus_map_of_isSepClosed
    [HasDerivedCategory (Sheaf (smallEtaleTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]
    [HasDerivedCategory (Sheaf (smallEtaleTopology (Spec (.of K))) AddCommGrpCat.{u + 1})]
    (M N : DerivedCategory.Plus (Sheaf (smallEtaleTopology (Spec (.of k))) AddCommGrpCat.{u + 1})) :
    Function.Bijective (fun φ : M ⟶ N ↦ (smallEtalePullbackAb g).rightDerivedFunctorPlus.map φ) :=
  (rightDerivedFunctorPlusFullyFaithfulOfIsEquivalence (smallEtalePullbackAb g)).map_bijective M N

end Pullback

end Stacks.EtaleCohomology
