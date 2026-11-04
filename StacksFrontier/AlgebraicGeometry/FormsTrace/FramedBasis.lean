module

public import StacksFrontier.AlgebraicGeometry.FormsTrace.FiniteTrace
public import StacksFrontier.AlgebraicGeometry.Different.FiniteSyntomicMorphisms.FreeSections
public import StacksFrontier.AlgebraicGeometry.NaiveCotangentDeterminant.Charts
public import StacksFrontier.RingTheory.FormsTrace.Framed
public import StacksFrontier.AlgebraicGeometry.AnnihilatorQcoh.Basic

/-!
# The basis of framed opens of a finite syntomic morphism

Let `f : Y → X` be a finite syntomic morphism (finite, flat, locally of finite presentation and
syntomic). Call an affine open `U ⊆ X` *framed* if `Γ(Y, f⁻¹U)` is zero, or if
`(Γ(X, U), Γ(Y, f⁻¹U))` has a frame (`Stacks.FormsTrace.ChartFrame`): a basis with first vector
`1` and a syntomic-good element `g` of the universal ring whose image under the classifying map
of the basis is a unit. Over a framed open the trace on forms of Stacks, Proposition 0FLC is
pulled back from a universal chart, and the framed opens form a basis of the topology of `X`.

* Frames restrict: a frame of a pair induces a frame of any base change of it with the same
  syntomic-good element (`Stacks.FormsTrace.ChartFrame.ofIsPushout`; it suffices that the image
  of `g` becomes a unit after base change), so a frame over an affine open `U` restricts to every
  affine open `V ⊆ U`, as `Γ(Y, f⁻¹V) = Γ(X, V) ⊗_{Γ(X, U)} Γ(Y, f⁻¹U)`.
* Points outside the image of `f` (which is closed, `f` being finite) have affine neighbourhoods
  over which `f⁻¹` is empty.
* A point in the image has an affine neighbourhood `U` over which `Γ(Y, f⁻¹U)` is free on a basis
  with first vector `1` (`AlgebraicGeometry.exists_isAffineOpen_basis_one`); the classifying
  images of the syntomic-good elements generate the unit ideal
  (`Stacks.FormsTrace.span_classify_isSyntomicGood_eq_top`, Tag 0FL4), so one of them, `a`, is a
  unit at the point, and on any basic open inside `D(a)` the basis is a frame.

## Main definitions

* `Stacks.FormsTrace.ChartFrame.ofIsPushout`: the frame induced on a base change.
* `Stacks.FormsTrace.frameOfBasisRestrict`, `Stacks.FormsTrace.restrictFrame`: frames on smaller
  affine opens.
* `Stacks.FormsTrace.IsFramedOpen`: framed affine opens.

## Main results

* `Stacks.FormsTrace.restrictFrame_g`: restriction keeps the syntomic-good element.
* `Stacks.FormsTrace.isBasis_framedOpens`: the framed opens form a basis.

## References

* [Stacks Project, Tag 0FLC](https://stacks.math.columbia.edu/tag/0FLC)
* [Stacks Project, Tag 0FL4](https://stacks.math.columbia.edu/tag/0FL4)
-/

@[expose] public noncomputable section

open AlgebraicGeometry AlgebraicGeometry.FiniteFreeAlgebra CategoryTheory Opposite TopologicalSpace

universe u

namespace Stacks.FormsTrace

variable {d : ℕ} [NeZero d]

section Algebra

variable {A B A' B' : Type u} [CommRing A] [CommRing B] [CommRing A'] [CommRing B'] [Algebra A B]
  [Algebra A A'] [Algebra A' B'] [Algebra B B'] [Algebra A B'] [IsScalarTower A A' B']
  [IsScalarTower A B B'] [Algebra.IsPushout A B A' B']

/-- The basis of a base change `B' = A' ⊗_A B` induced by a basis of `B`. -/
def pushoutBasis (b : Module.Basis (Fin d) A B) : Module.Basis (Fin d) A' B' :=
  (Algebra.IsPushout.symm (inferInstance : Algebra.IsPushout A B A' B')).out.basis b

omit [NeZero d] in
/-- The `i`-th vector of `pushoutBasis b` is the image of `b i` under `B → B'`. -/
theorem pushoutBasis_apply (b : Module.Basis (Fin d) A B) (i : Fin d) :
    pushoutBasis (A' := A') (B' := B') b i = algebraMap B B' (b i) :=
  IsBaseChange.basis_apply _ _ i

/-- If the first vector of `b` is `1`, so is the first vector of `pushoutBasis b`. -/
theorem pushoutBasis_zero (b : Module.Basis (Fin d) A B) (hb : b 0 = 1) :
    pushoutBasis (A' := A') (B' := B') b 0 = 1 := by
  rw [pushoutBasis_apply, hb, map_one]

/-- The table of the induced basis is the base change of the table of the basis. -/
theorem ofBasis_pushoutBasis (b : Module.Basis (Fin d) A B) (hb : b 0 = 1) :
    ofBasis (pushoutBasis (A' := A') (B' := B') b) (pushoutBasis_zero b hb) =
      FiniteFreeAlgebra.map (algebraMap A A') (ofBasis b hb) := by
  refine (ofBasis_map (algebraMap A A') (algebraMap B B') (fun r => ?_) b hb
    (pushoutBasis b) (pushoutBasis_zero b hb) fun i => ?_).symm
  · rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
  · rw [pushoutBasis_apply]

/-- **The frame induced on a base change** `B' = A' ⊗_A B` by a basis `b` of `B` with first
vector `1` and a syntomic-good `g` whose classifying image becomes a unit in `A'`. -/
def ChartFrame.ofIsPushout (b : Module.Basis (Fin d) A B) (hb : b 0 = 1) (g : universalRing d)
    (hg : IsSyntomicGood.{u} d g) (hu : IsUnit (algebraMap A A' ((ofBasis b hb).classify g))) :
    ChartFrame d A' B' where
  basis := pushoutBasis b
  basis_zero := pushoutBasis_zero b hb
  g := g
  good := hg
  isUnit := by
    rw [ofBasis_pushoutBasis, classify_map_eq_comp]
    exact hu

end Algebra

section Scheme

variable {X Y : Scheme.{u}} (f : Y ⟶ X) [IsFinite f] [Flat f] [LocallyOfFinitePresentation f]

/-- **A basis over an affine open induces a frame over a smaller affine open** on which the
classifying image of a syntomic-good element is a unit: `Γ(Y, f⁻¹V)` is the base change of
`Γ(Y, f⁻¹U)` along `Γ(X, U) → Γ(X, V)`. -/
def frameOfBasisRestrict (U V : X.affineOpens) (h : V.1 ≤ U.1) :
    letI := (f.app U.1).hom.toAlgebra
    letI := (f.app V.1).hom.toAlgebra
    ∀ (b : Module.Basis (Fin d) Γ(X, U.1) Γ(Y, f ⁻¹ᵁ U.1)) (hb : b 0 = 1) (g : universalRing d),
      IsSyntomicGood.{u} d g →
      IsUnit (X.presheaf.map (homOfLE h).op ((ofBasis b hb).classify g)) →
      ChartFrame d Γ(X, V.1) Γ(Y, f ⁻¹ᵁ V.1) :=
  letI : Algebra Γ(X, U.1) Γ(Y, f ⁻¹ᵁ U.1) := (f.app U.1).hom.toAlgebra
  letI : Algebra Γ(X, V.1) Γ(Y, f ⁻¹ᵁ V.1) := (f.app V.1).hom.toAlgebra
  letI : Algebra Γ(X, U.1) Γ(X, V.1) := (X.presheaf.map (homOfLE h).op).hom.toAlgebra
  letI : Algebra Γ(Y, f ⁻¹ᵁ U.1) Γ(Y, f ⁻¹ᵁ V.1) :=
    (Y.presheaf.map (homOfLE (f.preimage_mono h)).op).hom.toAlgebra
  letI : Algebra Γ(X, U.1) Γ(Y, f ⁻¹ᵁ V.1) :=
    (f.app U.1 ≫ Y.presheaf.map (homOfLE (f.preimage_mono h)).op).hom.toAlgebra
  haveI : IsScalarTower Γ(X, U.1) Γ(X, V.1) Γ(Y, f ⁻¹ᵁ V.1) :=
    IsScalarTower.of_algebraMap_eq fun x => by
      change (f.app U.1 ≫ Y.presheaf.map (homOfLE (f.preimage_mono h)).op).hom x =
        (X.presheaf.map (homOfLE h).op ≫ f.app V.1).hom x
      rw [(f.isPushout_app_restrict U V h).w]
  haveI : IsScalarTower Γ(X, U.1) Γ(Y, f ⁻¹ᵁ U.1) Γ(Y, f ⁻¹ᵁ V.1) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : Algebra.IsPushout Γ(X, U.1) Γ(Y, f ⁻¹ᵁ U.1) Γ(X, V.1) Γ(Y, f ⁻¹ᵁ V.1) :=
    (CommRingCat.isPushout_iff_isPushout.mp (f.isPushout_app_restrict U V h).flip).symm
  fun b hb g hg hu => ChartFrame.ofIsPushout b hb g hg hu

/-- **Restriction of a frame** over an affine open `U` to an affine open `V ⊆ U`. -/
def restrictFrame (U V : X.affineOpens) (h : V.1 ≤ U.1) :
    letI := (f.app U.1).hom.toAlgebra
    letI := (f.app V.1).hom.toAlgebra
    ChartFrame d Γ(X, U.1) Γ(Y, f ⁻¹ᵁ U.1) → ChartFrame d Γ(X, V.1) Γ(Y, f ⁻¹ᵁ V.1) :=
  letI : Algebra Γ(X, U.1) Γ(Y, f ⁻¹ᵁ U.1) := (f.app U.1).hom.toAlgebra
  fun F => frameOfBasisRestrict f U V h F.basis F.basis_zero F.g F.good
    (F.isUnit.map (X.presheaf.map (homOfLE h).op).hom)

/-- Restriction of frames keeps the syntomic-good element. -/
theorem restrictFrame_g (U V : X.affineOpens) (h : V.1 ≤ U.1) :
    letI := (f.app U.1).hom.toAlgebra
    letI := (f.app V.1).hom.toAlgebra
    ∀ F : ChartFrame d Γ(X, U.1) Γ(Y, f ⁻¹ᵁ U.1), (restrictFrame f U V h F).g = F.g :=
  fun _ => rfl

/-- **Framed opens**: affine opens `U` with `Γ(Y, f⁻¹U) = 0`, or such that
`(Γ(X, U), Γ(Y, f⁻¹U))` has a frame. -/
def IsFramedOpen (U : X.Opens) : Prop :=
  IsAffineOpen U ∧ (Subsingleton Γ(Y, f ⁻¹ᵁ U) ∨ ∃ (d : ℕ) (_ : NeZero d),
    letI := (f.app U).hom.toAlgebra
    Nonempty (ChartFrame d Γ(X, U) Γ(Y, f ⁻¹ᵁ U)))

/-- **The framed opens of a finite syntomic morphism form a basis of the topology** of the
target. -/
theorem isBasis_framedOpens (hf : Syntomic f) :
    Opens.IsBasis {U : X.Opens | IsFramedOpen f U} := by
  rw [Opens.isBasis_iff_nbhd]
  intro W x hxW
  by_cases hx : ∃ y : Y, f.base y = x
  · have : Stacks.Morphisms.IsFiniteLocallyFree f :=
      (Stacks.Morphisms.isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation f).2
        ⟨‹_›, ‹_›, ‹_›⟩
    obtain ⟨U, hU, hxU, d, hd, hb⟩ := exists_isAffineOpen_basis_one f x hx
    let : Algebra Γ(X, U) Γ(Y, f ⁻¹ᵁ U) := (f.app U).hom.toAlgebra
    obtain ⟨b, hb⟩ := hb
    have : Algebra.Syntomic Γ(X, U) Γ(Y, f ⁻¹ᵁ U) := by
      have h : RingHom.Syntomic (f.appLE U (f ⁻¹ᵁ U) le_rfl).hom :=
        f.syntomic_chartAlgebra hf ⟨U, hU⟩ ⟨f ⁻¹ᵁ U, hU.preimage f⟩ le_rfl
      rw [← Scheme.Hom.app_eq_appLE] at h
      exact h
    have hspan := span_classify_isSyntomicGood_eq_top b hb
    set p := hU.primeIdealOf ⟨x, hxU⟩
    obtain ⟨a, ⟨g, hg, rfl⟩, hap⟩ : ∃ a ∈ {a : Γ(X, U) | ∃ g : universalRing d,
        IsSyntomicGood.{u} d g ∧ (ofBasis b hb).classify g = a}, a ∉ p.asIdeal := by
      by_contra hcon
      push Not at hcon
      exact p.isPrime.ne_top (eq_top_iff.2 (hspan ▸ Ideal.span_le.2 hcon))
    have hxa : x ∈ X.basicOpen ((ofBasis b hb).classify g) := by
      rw [← hU.fromSpec_image_basicOpen]
      exact ⟨p, hap, hU.fromSpec_primeIdealOf ⟨x, hxU⟩⟩
    obtain ⟨a', ha'le, hxa'⟩ := hU.exists_basicOpen_le
      (V := W ⊓ X.basicOpen ((ofBasis b hb).classify g)) ⟨x, hxW, hxa⟩ hxU
    have hle : X.basicOpen a' ≤ U := X.basicOpen_le a'
    refine ⟨X.basicOpen a', ⟨hU.basicOpen a', Or.inr ⟨d, hd, ⟨?_⟩⟩⟩, hxa',
      ha'le.trans inf_le_left⟩
    exact frameOfBasisRestrict f ⟨U, hU⟩ ⟨X.basicOpen a', hU.basicOpen a'⟩ hle b hb g hg
      (Stacks.AlgebraicGeometry.AnnihilatorQcoh.isUnit_map_of_le_basicOpen _
        (ha'le.trans inf_le_right))
  · have hC : IsClosed (Set.range f.base) := f.isClosedMap.isClosed_range
    obtain ⟨V, hV, hxV, hVle⟩ := exists_isAffineOpen_mem_and_subset
      (U := W ⊓ ⟨(Set.range f.base)ᶜ, hC.isOpen_compl⟩) ⟨hxW, hx⟩
    refine ⟨V, ⟨hV, Or.inl ?_⟩, hxV, fun z hz => (hVle hz).1⟩
    have hbot : f ⁻¹ᵁ V = ⊥ := eq_bot_iff.2 fun y hy => ((hVle hy).2 ⟨y, rfl⟩).elim
    rw [hbot]
    infer_instance

end Scheme

end Stacks.FormsTrace

end
