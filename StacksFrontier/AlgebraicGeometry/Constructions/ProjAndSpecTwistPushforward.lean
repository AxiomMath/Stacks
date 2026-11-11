module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjAndSpecTwistPushforwardLocal
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjConeTwistConeCoproduct

/-!
# `π_* 𝒪_L(i) = ⨁_{m ≥ i} 𝒪_P(m)`

Let `A = ⨁_{d ≥ 0} A_d` be a graded ring, `P = Proj A`, and let `π : L = Proj B ⟶ P` be the cone
attached to the truncation algebra `B = ⨁_{d ≥ 0} A_{≥ d}` (Stacks, Section 0EKF). For every
integer `i` this file proves

  `π_* 𝒪_L(i) ≅ ∐_{m ≥ i} 𝒪_P(m)`

as sheaves of `𝒪_P`-modules. Over a standard open `D₊(f)`, `f ∈ A_d`, `d > 0`, it is the
equality of homogeneous parts `(B[1/ψ f])_i = ⨁_{m ≥ i} (A[1/f])_m` that the section displays,
read through `Γ(D₊(ψ f), 𝒪_L(i)) = (B[1/ψ f])_i` and `Γ(D₊(f), 𝒪_P(m)) = (A[1/f])_m`.

The footnote of Section 0EKF states `π_* 𝒪_L(i) = ⨁_{m ≥ -i} 𝒪_P(m)`; the section's own formula
`(B[1/g])_{m'} = ⨁_{m ≥ m'} (A[1/f])_m`, taken at `m' = i`, gives the range `m ≥ i`, which is the
one proved here. (For `A = k[x, y]` and `i = 2` the two ranges give different sheaves:
`⨁_{m ≥ -2} 𝒪_P(m)` has the summand `𝒪_P(-2)`, with `H¹(ℙ¹, 𝒪(-2)) ≠ 0`, while
`⨁_{m ≥ 2} 𝒪_P(m)` has `H¹ = 0`.)

## Main definitions

* `Stacks.AlgebraicGeometry.ProjAndSpecTwistPushforward.twistSectionsEquiv`:
  `⨁_{m ≥ i} Γ(D₊(f), 𝒪_P(m)) ≃+ Γ(D₊(ψ f), 𝒪_L(i))`.
* `Stacks.AlgebraicGeometry.ProjAndSpecTwistPushforward.twistPushforwardHom`: the inclusion
  `𝒪_P(m) ⟶ π_* 𝒪_L(i)`, for `m ≥ i`.
* `Stacks.AlgebraicGeometry.ProjAndSpecTwistPushforward.twistPushforwardDirectSumHom`: those
  inclusions out of the objectwise direct sum over `m ≥ i`.
* `Stacks.AlgebraicGeometry.ProjAndSpecTwistPushforward.twistPushforwardCoproductIso`:
  **`π_* 𝒪_L(i) ≅ ∐_{m ≥ i} 𝒪_P(m)`.**

## Main results

* `Stacks.AlgebraicGeometry.ProjAndSpecTwistPushforward.bijective_twistPushforwardDirectSumHom_app`:
  the comparison is bijective on the sections over a standard open of a positive-degree
  homogeneous element.

## References

* [Stacks Project, Tag 0EKF](https://stacks.math.columbia.edu/tag/0EKF)
* [Stacks Project, Tag 01M6](https://stacks.math.columbia.edu/tag/01M6)
-/

@[expose] public noncomputable section

open AlgebraicGeometry AlgebraicGeometry.ProjectiveSpectrum.Proj CategoryTheory
open CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.AlgebraicGeometry.ProjAndSpecTruncation Stacks.Truncation
open Stacks.AlgebraicGeometry.ProjTwistComparison Stacks.AlgebraicGeometry.ProjConeTwist

namespace Stacks.AlgebraicGeometry.ProjAndSpecTwistPushforward

universe u

attribute [local instance] ProjectiveSpectrum.isPrime
attribute [local implicit_reducible] TopCat.Sheaf sheafCompose
  PresheafOfModules.presheaf SheafOfModules.toSheaf
attribute [local instance_reducible] ProjectiveSpectrum.top

variable {A : Type u} {σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜]

/-! ### Gluing the local maps -/

/-- The local data of the inclusion `𝒪_P(m) ⟶ π_* 𝒪_L(i)`: the local maps over the
positive-degree standard opens, a degree being chosen for each, with their compatibility with
restriction. -/
def twistPushforwardStandardOpenHomData (i m : ℤ) (him : i ≤ m) :
    StandardOpenHomData 𝒜 (twistGrading (S := A) 𝒜 m) (twistPushforward 𝒜 i) where
  app p := twistPushforwardApp 𝒜 i m him (Classical.choose p.2) (Classical.choose_spec p.2).2
    (Classical.choose_spec p.2).1
  app_restrict p q h s :=
    twistPushforwardApp_restrict 𝒜 i m him (Classical.choose_spec p.2).2
      (Classical.choose_spec p.2).1 (Classical.choose_spec q.2).2 (Classical.choose_spec q.2).1 h s

/-- **The inclusion `𝒪_P(m) ⟶ π_* 𝒪_L(i)`, for `m ≥ i`**: the morphism of sheaves of
`𝒪_P`-modules glued from the local inclusions `(A[1/f])_m ⊆ (B[1/ψ f])_i`. -/
@[stacks 0EKF "the inclusion O_P(m) to pi_* O_L(i), for m ≥ i, as a morphism of sheaves of \
O_P-modules, for the truncation cone"]
def twistPushforwardHom (i m : ℤ) (him : i ≤ m) :
    twistingSheaf 𝒜 m ⟶ twistPushforward 𝒜 i :=
  homOfStandardOpenHomData 𝒜 (twistGrading (S := A) 𝒜 m) (twistPushforward 𝒜 i)
    (twistPushforwardStandardOpenHomData 𝒜 i m him)

/-- The glued inclusion restricts on a positive-degree standard open to the local map. -/
theorem twistPushforwardHom_app (i m : ℤ) (him : i ≤ m) (p : PositiveElem 𝒜) :
    (twistPushforwardHom 𝒜 i m him).val.app (op (positiveBasicOpen 𝒜 p)) =
      twistPushforwardApp 𝒜 i m him (Classical.choose p.2) (Classical.choose_spec p.2).2
        (Classical.choose_spec p.2).1 :=
  homOfStandardOpenHomData_app 𝒜 (twistGrading (S := A) 𝒜 m) (twistPushforward 𝒜 i)
    (twistPushforwardStandardOpenHomData 𝒜 i m him) p

/-! ### The comparison out of the direct sum -/

/-- **The inclusions `𝒪_P(m) ⟶ π_* 𝒪_L(i)`, `m ≥ i`, as one morphism out of the objectwise
direct sum.** -/
@[stacks 0EKF "the inclusions O_P(m) to pi_* O_L(i), m ≥ i, as one morphism out of the \
objectwise direct sum, for the truncation cone"]
def twistPushforwardDirectSumHom (i : ℤ) :
    Stacks.directSum (fun m : {m : ℤ // i ≤ m} => (twistingSheaf 𝒜 m.1).val) ⟶
      (twistPushforward 𝒜 i).val :=
  Stacks.directSumDesc _ fun m => (twistPushforwardHom 𝒜 i m.1 m.2).val

/-- On a standard open of the basis the comparison sends the `m`-th summand to the local
inclusion. -/
theorem twistPushforwardDirectSumHom_app_of (i : ℤ) (m : {m : ℤ // i ≤ m}) (p : PositiveElem 𝒜)
    (s : (twistingSheaf 𝒜 m.1).val.obj (op (positiveBasicOpen 𝒜 p))) :
    (twistPushforwardDirectSumHom 𝒜 i).app (op (positiveBasicOpen 𝒜 p)) (DirectSum.of _ m s) =
      (twistPushforwardApp 𝒜 i m.1 m.2 (Classical.choose p.2) (Classical.choose_spec p.2).2
        (Classical.choose_spec p.2).1).hom s := by
  refine (congrArg (fun q : (twistingSheaf 𝒜 m.1).val ⟶ (twistPushforward 𝒜 i).val =>
      q.app (op (positiveBasicOpen 𝒜 p)) s)
    (Stacks.inclHom_directSumDesc (fun k : {m : ℤ // i ≤ m} => (twistingSheaf 𝒜 k.1).val)
      (fun k => (twistPushforwardHom 𝒜 i k.1 k.2).val) m)).trans ?_
  exact congrArg (fun φ : (twistingSheaf 𝒜 m.1).val.obj (op (positiveBasicOpen 𝒜 p)) ⟶
      (twistPushforward 𝒜 i).val.obj (op (positiveBasicOpen 𝒜 p)) => φ.hom s)
    (twistPushforwardHom_app 𝒜 i m.1 m.2 p)

/-- The standard-open description of the sections of `𝒪_L(i)` over `D₊(ψ f)`:
`⨁_{m ≥ i} Γ(D₊(f), 𝒪_P(m)) ≃+ Γ(D₊(ψ f), 𝒪_L(i))`, the composite of the descriptions of the
summands, the equality of homogeneous parts `⨁_{m ≥ i} (A[1/f])_m = (B[1/ψ f])_i`, and the
description of the sections of `𝒪_L(i)` over `D₊(ψ f)`. -/
@[stacks 0EKF "the identification of the sections of O_L(i) over D+(psi f) = pi^{-1}(D+(f)) with \
⨁_{m ≥ i} of the sections of O_P(m) over D+(f)"]
def twistSectionsEquiv (i : ℤ) {d : ℕ} {f : A} (hf : f ∈ 𝒜 d) (hd : 0 < d) :
    (DirectSum {m : ℤ // i ≤ m} fun m =>
        ↥((twistingSheaf 𝒜 m.1).val.obj (op (ProjectiveSpectrum.basicOpen 𝒜 f)))) ≃+
      ↥((twistingSheaf (grading 𝒜) i).val.obj
        (op (ProjectiveSpectrum.basicOpen (grading 𝒜) (psi 𝒜 f)))) :=
  (((DFinsupp.mapRange.addEquiv fun m : {m : ℤ // i ≤ m} =>
      Stacks.ProjectiveCohomology.sectionsTwistEquivAwayGrading 𝒜 hf hd m.1).trans
    (twistPieceSumEquiv 𝒜 hf hd i)).trans
    (Stacks.ProjectiveCohomology.sectionsTwistEquivAwayGrading (grading 𝒜)
      ((psi 𝒜).map_mem hf) hd i).symm)

/-- On the `m`-th summand, `twistSectionsEquiv` is `twistLift`. -/
theorem twistSectionsEquiv_of (i : ℤ) {d : ℕ} {f : A} (hf : f ∈ 𝒜 d) (hd : 0 < d)
    (m : {m : ℤ // i ≤ m})
    (s : (twistingSheaf 𝒜 m.1).val.obj (op (ProjectiveSpectrum.basicOpen 𝒜 f))) :
    twistSectionsEquiv 𝒜 i hf hd (DirectSum.of _ m s) = twistLift 𝒜 m.2 hf hd s := by
  have h0 : (DFinsupp.mapRange.addEquiv fun m : {m : ℤ // i ≤ m} =>
      Stacks.ProjectiveCohomology.sectionsTwistEquivAwayGrading 𝒜 hf hd m.1)
        (DirectSum.of _ m s) =
      DirectSum.of _ m (Stacks.ProjectiveCohomology.sectionsTwistEquivAwayGrading 𝒜 hf hd m.1 s) :=
    DFinsupp.mapRange_single (hf := fun k => map_zero _)
  simp only [twistSectionsEquiv, AddEquiv.trans_apply, h0]
  exact congrArg (Stacks.ProjectiveCohomology.sectionsTwistEquivAwayGrading (grading 𝒜)
    ((psi 𝒜).map_mem hf) hd i).symm (twistPieceSum_of 𝒜 hf hd i m _)

/-- A restriction map of a presheaf of modules along an equality of opens is bijective. -/
theorem bijective_map_eqToHom_op {X : TopCat.{u}}
    {R : (TopologicalSpace.Opens X)ᵒᵖ ⥤ RingCat.{u}} (M : PresheafOfModules.{u} R)
    {U V : TopologicalSpace.Opens X} (h : U = V) :
    Function.Bijective (M.map (eqToHom h).op) := by
  subst h
  rw [eqToHom_refl, op_id]
  exact ⟨fun x y hxy => (M.map_id_apply_ungraded _ x).symm.trans
      (hxy.trans (M.map_id_apply_ungraded _ y)),
    fun y => ⟨y, M.map_id_apply_ungraded _ y⟩⟩

/-- The standard-open description of the sections of `π_* 𝒪_L(i)`, as an additive map
`⨁_{m ≥ i} Γ(D₊(f), 𝒪_P(m)) → Γ(D₊(f), π_* 𝒪_L(i))`: `twistSectionsEquiv` followed by the
transport along `π⁻¹(D₊(f)) = D₊(ψ f)`. -/
def twistPushforwardSectionsHom (i : ℤ) {d : ℕ} {f : A} (hf : f ∈ 𝒜 d) (hd : 0 < d) :
    (DirectSum {m : ℤ // i ≤ m} fun m =>
        ↥((twistingSheaf 𝒜 m.1).val.obj (op (ProjectiveSpectrum.basicOpen 𝒜 f)))) →+
      ↥((twistPushforward 𝒜 i).val.obj (op (AlgebraicGeometry.Proj.basicOpen 𝒜 f))) :=
  ((twistingSheaf (grading 𝒜) i).val.map
    (eqToHom (pi_preimage_basicOpen 𝒜 f d hf hd)).op).hom.toAddMonoidHom.comp
      (twistSectionsEquiv 𝒜 i hf hd).toAddMonoidHom

/-- **The standard-open description of the sections of `π_* 𝒪_L(i)` is bijective.** -/
@[stacks 0EKF "the identification pi_* O_L(i) = ⨁_{m ≥ i} O_P(m) over one standard open D+(f) \
of P is bijective, with the summands written as the sections of the twisting sheaves"]
theorem bijective_twistPushforwardSectionsHom (i : ℤ) {d : ℕ} {f : A} (hf : f ∈ 𝒜 d)
    (hd : 0 < d) : Function.Bijective (twistPushforwardSectionsHom 𝒜 i hf hd) :=
  (bijective_map_eqToHom_op (twistingSheaf (grading 𝒜) i).val
    (pi_preimage_basicOpen 𝒜 f d hf hd)).comp
      (twistSectionsEquiv 𝒜 i hf hd).bijective

/-- On the `m`-th summand the standard-open description is the local inclusion. -/
theorem twistPushforwardSectionsHom_of (i : ℤ) {d : ℕ} {f : A} (hf : f ∈ 𝒜 d) (hd : 0 < d)
    (m : {m : ℤ // i ≤ m})
    (s : (twistingSheaf 𝒜 m.1).val.obj (op (ProjectiveSpectrum.basicOpen 𝒜 f))) :
    twistPushforwardSectionsHom 𝒜 i hf hd (DirectSum.of _ m s) =
      (twistPushforwardApp 𝒜 i m.1 m.2 d hf hd).hom s :=
  (congrArg (fun z => (twistingSheaf (grading 𝒜) i).val.map
    (eqToHom (pi_preimage_basicOpen 𝒜 f d hf hd)).op z)
      (twistSectionsEquiv_of 𝒜 i hf hd m s)).trans
    (twistPushforwardApp_apply 𝒜 i m.1 m.2 d hf hd s).symm

/-- **Over a standard open of a positive-degree homogeneous element the comparison out of the
direct sum is bijective.** -/
@[stacks 0EKF "the morphism out of the objectwise direct sum over m ≥ i of the twisting sheaves \
O_P(m) into pi_* O_L(i) is bijective on the sections over a standard open of a positive-degree \
homogeneous element, for the truncation cone"]
theorem bijective_twistPushforwardDirectSumHom_app (i : ℤ) (p : PositiveElem 𝒜) :
    Function.Bijective
      ((twistPushforwardDirectSumHom 𝒜 i).app (op (positiveBasicOpen 𝒜 p))).hom := by
  have hdpos : 0 < Classical.choose p.2 := (Classical.choose_spec p.2).1
  have hmem : p.1 ∈ 𝒜 (Classical.choose p.2) := (Classical.choose_spec p.2).2
  have happ : ∀ z, (twistPushforwardDirectSumHom 𝒜 i).app (op (positiveBasicOpen 𝒜 p)) z =
      twistPushforwardSectionsHom 𝒜 i hmem hdpos z := by
    refine DFunLike.congr_fun (DirectSum.addHom_ext
      (f := Stacks.homToAddMonoidHom (fun k : {m : ℤ // i ≤ m} => (twistingSheaf 𝒜 k.1).val)
        (twistPushforwardDirectSumHom 𝒜 i) (op (positiveBasicOpen 𝒜 p)))
      (g := twistPushforwardSectionsHom 𝒜 i hmem hdpos) fun k s => ?_)
    exact (twistPushforwardDirectSumHom_app_of 𝒜 i k p s).trans
      (twistPushforwardSectionsHom_of 𝒜 i hmem hdpos k s).symm
  rw [show ⇑((twistPushforwardDirectSumHom 𝒜 i).app (op (positiveBasicOpen 𝒜 p))).hom = _ from
    funext happ]
  exact bijective_twistPushforwardSectionsHom 𝒜 i hmem hdpos

/-- `π_* 𝒪_L(i)` is the sheafification of the objectwise direct sum of the `𝒪_P(m)`, `m ≥ i`. -/
def twistPushforwardSheafifyIso (i : ℤ) :
    (PresheafOfModules.sheafification (𝟙 _)).obj
        (Stacks.directSum fun m : {m : ℤ // i ≤ m} => (twistingSheaf 𝒜 m.1).val) ≅
      twistPushforward 𝒜 i :=
  Stacks.sheafifyIsoOfLocallyBijective (twistPushforwardDirectSumHom 𝒜 i)
    (Stacks.AlgebraicGeometry.MeromorphicConstantModule.isLocallyInjective_of_injective_basis
      (Y := ProjectiveSpectrum.top 𝒜) (B := positiveBasicOpen 𝒜) _
      (isBasis_positiveBasicOpen 𝒜) fun p => (bijective_twistPushforwardDirectSumHom_app 𝒜 i p).1)
    (Stacks.AlgebraicGeometry.MeromorphicConstantModule.isLocallySurjective_of_surjective_basis
      (Y := ProjectiveSpectrum.top 𝒜) (B := positiveBasicOpen 𝒜) _
      (isBasis_positiveBasicOpen 𝒜) fun p => (bijective_twistPushforwardDirectSumHom_app 𝒜 i p).2)

/-- **`π_* 𝒪_L(i) ≅ ∐_{m ≥ i} 𝒪_P(m)`**, for every integer `i`, as sheaves of `𝒪_P`-modules, for
the cone `π : L = Proj B ⟶ P = Proj A` of the truncation algebra `B = ⨁_{d ≥ 0} A_{≥ d}`. -/
@[stacks 0EKF "the footnote pi_* O_L(i) = ⨁ O_P(m), as an isomorphism of sheaves of O_P-modules \
for every integer i, the direct sum being the coproduct. The footnote of the source reads \
m ≥ -i; the correct range, given by the section's own formula (B[1/g])_{m'} = ⨁_{m ≥ m'} \
(A[1/f])_m at m' = i, is m ≥ i, and that is the range stated here"]
def twistPushforwardCoproductIso (i : ℤ) :
    (Scheme.Modules.pushforward (pi 𝒜)).obj (twistingSheaf (grading 𝒜) i) ≅
      ∐ fun m : {m : ℤ // i ≤ m} => twistingSheaf 𝒜 m.1 :=
  (twistPushforwardSheafifyIso 𝒜 i).symm ≪≫
    Stacks.sheafifyDirectSumIso fun m : {m : ℤ // i ≤ m} => twistingSheaf 𝒜 m.1

end Stacks.AlgebraicGeometry.ProjAndSpecTwistPushforward

end
