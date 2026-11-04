module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjConeTwistPuncturedCoproduct
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjConeTwistStandardOpenSum

/-!
# `π_* 𝒪_L = ⨁_{m ≥ 0} 𝒪_P(m)`

Let `A = ⨁_{d ≥ 0} 𝒜 d` be a graded ring, `P = Proj A` and let `π : L = Proj B ⟶ P` be the cone
attached to the truncation algebra `B = ⨁_{d ≥ 0} A_{≥ d}`. This file proves the identification

  `π_* 𝒪_L ≅ ∐_{m ∈ ℤ} (nonnegative twists)_m`

of [Stacks, Tag 0EKG] as an isomorphism of sheaves of `𝒪_P`-modules, the coproduct being the
categorical one and the family the homogeneous pieces
`Stacks.AlgebraicGeometry.ProjConeTwist.nonnegTwistingSheaf` of the graded algebra
`Stacks.AlgebraicGeometry.ProjConeTwist.nonnegTwistAlgebra`: the twisting sheaf `𝒪_P(m)` in a
nonnegative degree and the zero sheaf in a negative one.

## Main definitions

* `Stacks.AlgebraicGeometry.ProjConeTwist.coneTwistNatDirectSumHom`: the degreewise inclusions as
  a morphism out of the objectwise direct sum over the natural numbers.
* `Stacks.AlgebraicGeometry.ProjConeTwist.coneTwistDirectSumHom`: the same over all of `ℤ`, out of
  the objectwise direct sum of the pieces of `nonnegTwistAlgebra`.
* `Stacks.AlgebraicGeometry.ProjConeTwist.coneStructureSheafifyIso`: `π_* 𝒪_L` is the
  sheafification of that objectwise direct sum.
* `Stacks.AlgebraicGeometry.ProjConeTwist.coneStructureCoproductIso`: **the identification
  `π_* 𝒪_L ≅ ∐_{m ∈ ℤ} (nonnegTwistAlgebra 𝒜).piece m`.**

## Main results

* `Stacks.AlgebraicGeometry.ProjConeTwist.bijective_coneTwistNatDirectSumHom_app` and
  `Stacks.AlgebraicGeometry.ProjConeTwist.bijective_coneTwistDirectSumHom_app`: **both
  comparisons are bijective on the sections over a standard open of a positive-degree homogeneous
  element.**
* `Stacks.AlgebraicGeometry.ProjConeTwist.coneTwistDirectSumHom_app_directSumNatToIntApp`: the
  reindexing identifies the two comparisons on the sections over such an open.

## References

* [Stacks Project, Tag 0EKG](https://stacks.math.columbia.edu/tag/0EKG)
* [Stacks Project, Tag 01CF](https://stacks.math.columbia.edu/tag/01CF)
-/

@[expose] public noncomputable section

open AlgebraicGeometry AlgebraicGeometry.ProjectiveSpectrum.Proj CategoryTheory
open CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.AlgebraicGeometry.ProjAndSpecTruncation Stacks.Truncation
open Stacks.AlgebraicGeometry.ProjTwistComparison

namespace Stacks.AlgebraicGeometry.ProjConeTwist

universe u

attribute [local instance] ProjectiveSpectrum.isPrime
attribute [local implicit_reducible] TopCat.Sheaf sheafCompose
  PresheafOfModules.presheaf SheafOfModules.toSheaf
attribute [local instance_reducible] ProjectiveSpectrum.top

/-- A map whose composite after a bijection is a bijection is itself a bijection. -/
private theorem bijective_of_comp_eq {α β γ : Type*} {f : α → β} {g : β → γ} {h : α → γ}
    (hfg : ∀ a, g (f a) = h a) (hf : Function.Bijective f) (hh : Function.Bijective h) :
    Function.Bijective g := by
  refine ⟨fun x y hxy => ?_, fun c => ?_⟩
  · obtain ⟨a, rfl⟩ := hf.2 x
    obtain ⟨b, rfl⟩ := hf.2 y
    exact congrArg f (hh.1 ((hfg a).symm.trans (hxy.trans (hfg b))))
  · obtain ⟨a, ha⟩ := hh.2 c
    exact ⟨f a, (hfg a).trans ha⟩

variable {A : Type u} {σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜]

/-! ### The comparison over the natural numbers -/

/-- **The degreewise inclusions `𝒪_P(m) ⟶ π_* 𝒪_L` as a single morphism out of the objectwise
direct sum over the natural numbers.** -/
@[stacks 0EKG "the family of degreewise inclusions O_P(m) -> pi_* O_L as one morphism out of the \
objectwise direct sum over the natural numbers, for the truncation cone"]
def coneTwistNatDirectSumHom :
    Stacks.directSum (fun n : ℕ => (twistingSheaf 𝒜 (n : ℤ)).val) ⟶
      (Stacks.Morphisms.pushforwardStructureSheaf (pi 𝒜)).val :=
  Stacks.directSumDesc _ fun n => (coneTwistHom 𝒜 n).val

/-- On a standard open of the basis the comparison sends the `n`-th summand to the glued
degreewise inclusion. -/
theorem coneTwistNatDirectSumHom_app_incl (n : ℕ) (p : PositiveElem 𝒜)
    (s : (twistingSheaf 𝒜 (n : ℤ)).val.obj (op (positiveBasicOpen 𝒜 p))) :
    (coneTwistNatDirectSumHom 𝒜).app (op (positiveBasicOpen 𝒜 p)) (DirectSum.of _ n s) =
      (coneTwistHom 𝒜 n).val.app (op (positiveBasicOpen 𝒜 p)) s :=
  congrArg (fun q : (twistingSheaf 𝒜 (n : ℤ)).val ⟶
      (Stacks.Morphisms.pushforwardStructureSheaf (pi 𝒜)).val =>
        q.app (op (positiveBasicOpen 𝒜 p)) s)
    (Stacks.inclHom_directSumDesc (fun k : ℕ => (twistingSheaf 𝒜 (k : ℤ)).val)
      (fun k => (coneTwistHom 𝒜 k).val) n)

/-- On a standard open of the basis the comparison sends the `n`-th summand to the local
degreewise inclusion. -/
theorem coneTwistNatDirectSumHom_app_of (n : ℕ) (p : PositiveElem 𝒜)
    (s : (twistingSheaf 𝒜 (n : ℤ)).val.obj (op (positiveBasicOpen 𝒜 p))) :
    (coneTwistNatDirectSumHom 𝒜).app (op (positiveBasicOpen 𝒜 p)) (DirectSum.of _ n s) =
      (coneTwistApp 𝒜 n (Classical.choose p.2) (Classical.choose_spec p.2).2
        (Classical.choose_spec p.2).1).hom s := by
  refine (coneTwistNatDirectSumHom_app_incl 𝒜 n p s).trans ?_
  exact congrArg (fun φ : (twistingSheaf 𝒜 (n : ℤ)).val.obj (op (positiveBasicOpen 𝒜 p)) ⟶
      (Stacks.Morphisms.pushforwardStructureSheaf (pi 𝒜)).val.obj
        (op (positiveBasicOpen 𝒜 p)) => φ.hom s)
    (coneTwistHom_app 𝒜 n (Classical.choose_spec p.2).2 (Classical.choose_spec p.2).1)

/-- **Over a standard open of a positive-degree homogeneous element the comparison out of the
direct sum over the natural numbers is bijective.** -/
@[stacks 0EKG "the morphism out of the objectwise direct sum over the natural numbers of the \
twisting sheaves is bijective on the sections over a standard open of a positive-degree \
homogeneous element, for the cone of the truncation algebra"]
theorem bijective_coneTwistNatDirectSumHom_app (p : PositiveElem 𝒜) :
    Function.Bijective
      ((coneTwistNatDirectSumHom 𝒜).app (op (positiveBasicOpen 𝒜 p))).hom := by
  have hdpos : 0 < Classical.choose p.2 := (Classical.choose_spec p.2).1
  have hmem : p.1 ∈ 𝒜 (Classical.choose p.2) := (Classical.choose_spec p.2).2
  have happ : ∀ z, (coneTwistNatDirectSumHom 𝒜).app (op (positiveBasicOpen 𝒜 p)) z =
      (coneAlgebraSectionsEquivTwistSections 𝒜 (Classical.choose p.2) hmem hdpos).symm z := by
    refine DFunLike.congr_fun (DirectSum.addHom_ext
      (f := Stacks.homToAddMonoidHom (fun k : ℕ => (twistingSheaf 𝒜 (k : ℤ)).val)
        (coneTwistNatDirectSumHom 𝒜) (op (positiveBasicOpen 𝒜 p)))
      (g := (coneAlgebraSectionsEquivTwistSections 𝒜 (Classical.choose p.2) hmem
        hdpos).symm.toAddMonoidHom) fun k s => ?_)
    exact (coneTwistNatDirectSumHom_app_of 𝒜 k p s).trans
      (coneAlgebraSectionsEquivTwistSections_symm_of 𝒜 k (Classical.choose p.2) hmem hdpos s).symm
  rw [show ⇑((coneTwistNatDirectSumHom 𝒜).app (op (positiveBasicOpen 𝒜 p))).hom = _ from
    funext happ]
  exact (coneAlgebraSectionsEquivTwistSections 𝒜 (Classical.choose p.2) hmem hdpos).symm.bijective

/-! ### The comparison over all integers -/

/-- **The homogeneous pieces of the algebra of nonnegative twists, included in `π_* 𝒪_L` out of
the objectwise direct sum over all integers.** -/
@[stacks 0EKG "the inclusions of the homogeneous pieces of the nonnegative twist algebra as one \
morphism out of the objectwise direct sum over all integers, for the truncation cone"]
def coneTwistDirectSumHom :
    Stacks.directSum (fun m : ℤ => (nonnegTwistingSheaf 𝒜 m).val) ⟶
      (Stacks.Morphisms.pushforwardStructureSheaf (pi 𝒜)).val :=
  Stacks.directSumDesc _ fun m => (coneIota 𝒜 m).val

/-- On a standard open of the basis the integer-indexed comparison sends the `m`-th summand to
the inclusion of the `m`-th homogeneous piece. -/
theorem coneTwistDirectSumHom_app_of (m : ℤ) (p : PositiveElem 𝒜)
    (x : (nonnegTwistingSheaf 𝒜 m).val.obj (op (positiveBasicOpen 𝒜 p))) :
    (coneTwistDirectSumHom 𝒜).app (op (positiveBasicOpen 𝒜 p)) (DirectSum.of _ m x) =
      (coneIota 𝒜 m).val.app (op (positiveBasicOpen 𝒜 p)) x :=
  congrArg (fun q : (nonnegTwistingSheaf 𝒜 m).val ⟶
      (Stacks.Morphisms.pushforwardStructureSheaf (pi 𝒜)).val =>
        q.app (op (positiveBasicOpen 𝒜 p)) x)
    (Stacks.inclHom_directSumDesc (fun k : ℤ => (nonnegTwistingSheaf 𝒜 k).val)
      (fun k => (coneIota 𝒜 k).val) m)

/-- **The reindexing `ℕ → ℤ` identifies the two comparisons** on the sections over a standard
open of the basis. -/
@[stacks 0EKG "the inclusion of the nonnegative part of the objectwise direct sum carries the \
integer-indexed comparison to the one indexed by the natural numbers, on the sections over a \
standard open of a positive-degree homogeneous element"]
theorem coneTwistDirectSumHom_app_directSumNatToIntApp (p : PositiveElem 𝒜)
    (z : Stacks.DirectSumType (fun k : ℕ => (nonnegTwistingSheaf 𝒜 (k : ℤ)).val)
      (op (positiveBasicOpen 𝒜 p))) :
    (coneTwistDirectSumHom 𝒜).app (op (positiveBasicOpen 𝒜 p))
        (Stacks.directSumNatToIntApp (fun m : ℤ => (nonnegTwistingSheaf 𝒜 m).val)
          (op (positiveBasicOpen 𝒜 p)) z) =
      (coneTwistNatDirectSumHom 𝒜).app (op (positiveBasicOpen 𝒜 p)) z := by
  refine DFunLike.congr_fun (DirectSum.addHom_ext
    (f := (Stacks.homToAddMonoidHom (fun m : ℤ => (nonnegTwistingSheaf 𝒜 m).val)
        (coneTwistDirectSumHom 𝒜) (op (positiveBasicOpen 𝒜 p))).comp
      (Stacks.directSumNatToIntApp (fun m : ℤ => (nonnegTwistingSheaf 𝒜 m).val)
        (op (positiveBasicOpen 𝒜 p))))
    (g := Stacks.homToAddMonoidHom (fun k : ℕ => (twistingSheaf 𝒜 (k : ℤ)).val)
      (coneTwistNatDirectSumHom 𝒜) (op (positiveBasicOpen 𝒜 p)))
    fun n x => ?_) z
  refine Eq.trans (congrArg (fun w => (coneTwistDirectSumHom 𝒜).app
      (op (positiveBasicOpen 𝒜 p)) w)
    (Stacks.directSumNatToIntApp_of (fun m : ℤ => (nonnegTwistingSheaf 𝒜 m).val)
      (op (positiveBasicOpen 𝒜 p)) n x)) ?_
  exact (coneTwistDirectSumHom_app_of 𝒜 (n : ℤ) p x).trans
    (coneTwistNatDirectSumHom_app_incl 𝒜 n p x).symm

/-- **Over a standard open of a positive-degree homogeneous element the comparison out of the
direct sum over all integers is bijective.** -/
@[stacks 0EKG "the morphism out of the objectwise direct sum over all integers of the \
homogeneous pieces of the nonnegative twist algebra is bijective on the sections over a standard \
open of a positive-degree homogeneous element, for the cone of the truncation algebra"]
theorem bijective_coneTwistDirectSumHom_app (p : PositiveElem 𝒜) :
    Function.Bijective
      ((coneTwistDirectSumHom 𝒜).app (op (positiveBasicOpen 𝒜 p))).hom := by
  refine bijective_of_comp_eq
    (f := Stacks.directSumNatToIntApp (fun m : ℤ => (nonnegTwistingSheaf 𝒜 m).val)
      (op (positiveBasicOpen 𝒜 p)))
    (h := fun z => (coneTwistNatDirectSumHom 𝒜).app (op (positiveBasicOpen 𝒜 p)) z)
    (coneTwistDirectSumHom_app_directSumNatToIntApp 𝒜 p)
    (Stacks.bijective_directSumNatToIntApp (fun m : ℤ => (nonnegTwistingSheaf 𝒜 m).val) _
      fun n hn => Stacks.subsingleton_of_isZero (isZero_nonnegTwistingSheaf 𝒜 hn) _)
    (bijective_coneTwistNatDirectSumHom_app 𝒜 p)

/-- **`π_* 𝒪_L` is the sheafification of the objectwise direct sum of the homogeneous pieces of
the algebra of nonnegative twists.** -/
@[stacks 0EKG "the direct image of the structure sheaf of the cone is the sheafification of the \
objectwise direct sum of the homogeneous pieces of the nonnegative twist algebra, for the \
truncation cone"]
def coneStructureSheafifyIso :
    (PresheafOfModules.sheafification (𝟙 _)).obj
        (Stacks.directSum fun m : ℤ => (nonnegTwistingSheaf 𝒜 m).val) ≅
      Stacks.Morphisms.pushforwardStructureSheaf (pi 𝒜) :=
  Stacks.sheafifyIsoOfLocallyBijective (coneTwistDirectSumHom 𝒜)
    (Stacks.AlgebraicGeometry.MeromorphicConstantModule.isLocallyInjective_of_injective_basis
      (Y := ProjectiveSpectrum.top 𝒜) (B := positiveBasicOpen 𝒜) _
      (isBasis_positiveBasicOpen 𝒜) fun p => (bijective_coneTwistDirectSumHom_app 𝒜 p).1)
    (Stacks.AlgebraicGeometry.MeromorphicConstantModule.isLocallySurjective_of_surjective_basis
      (Y := ProjectiveSpectrum.top 𝒜) (B := positiveBasicOpen 𝒜) _
      (isBasis_positiveBasicOpen 𝒜) fun p => (bijective_coneTwistDirectSumHom_app 𝒜 p).2)

/-- **`π_* 𝒪_L ≅ ∐_{m ∈ ℤ} (nonnegTwistAlgebra 𝒜).piece m`**: the identification of the direct
image of the structure sheaf of the cone with the coproduct of the homogeneous pieces of the
algebra of nonnegative twists. -/
@[stacks 0EKG "the identification pi_* O_L = the coproduct of the homogeneous pieces of the \
nonnegative twist algebra, as sheaves of O_P-modules, for the cone of the truncation algebra"]
def coneStructureCoproductIso :
    Stacks.Morphisms.pushforwardStructureSheaf (pi 𝒜) ≅
      ∐ fun m : ℤ => nonnegTwistingSheaf 𝒜 m :=
  (coneStructureSheafifyIso 𝒜).symm ≪≫
    Stacks.sheafifyDirectSumIso fun m : ℤ => nonnegTwistingSheaf 𝒜 m

end Stacks.AlgebraicGeometry.ProjConeTwist

end
