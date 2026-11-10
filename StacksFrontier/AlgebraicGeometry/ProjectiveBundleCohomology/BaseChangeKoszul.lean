module

public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleCohomology.BaseChangeTwistMul

/-!
# The Koszul filtration of a projective bundle under base change

Let `b : 𝐏(E') ⟶ 𝐏(E)` be the morphism of projective bundles over `g : S' ⟶ S`, `E' ≅ g^*E`. The
pullback along `b` of the twisted Koszul filtration of `𝐏(E)` is the twisted Koszul filtration of
`𝐏(E')`, and the base change map of higher direct images commutes with the connecting morphisms
of these filtrations.

## Main definitions

* `Stacks.AlgebraicGeometry.ProjectiveBundleCohomology.koszulTwistSequenceBaseChange`: the
  identification of the pulled-back twisted Koszul filtration with that of `𝐏(E')`.

## Main results

* `Stacks.AlgebraicGeometry.ProjectiveBundleCohomology.canonicalδ_koszul_baseChange`: the base
  change map commutes with the connecting morphisms of the twisted Koszul filtrations.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Stacks.AlgebraicGeometry.RelativeProjBridge Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjTwists
open Stacks.AlgebraicGeometry.LerayAffineBase (pushDelta)

universe u

attribute [local instance 10000] HasDerivedCategory.standard

namespace Stacks.AlgebraicGeometry.ProjectiveBundleCohomology

variable {S S' : Scheme.{u}} (g : S' ⟶ S) (E : S.Modules) [E.IsQuasicoherent]
  (hqc : Stacks.SymGraded.IsQuasicoherentPieces E) (E' : S'.Modules) [E'.IsQuasicoherent]
  (hqc' : Stacks.SymGraded.IsQuasicoherentPieces E') (hE : E' ≅ (Scheme.Modules.pullback g).obj E)
  (D : TwistData (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc))
  (D' : TwistData (Stacks.SymGraded.schemeSheafGradedAlgebra E' hqc'))

/-- **The pullback of the twisted Koszul filtration of `𝐏(E)` along `b` is that of `𝐏(E')`.** -/
public def koszulTwistSequenceBaseChange (p : ℕ) :
    (koszulTwistSequence E hqc D p).map
        (Scheme.Modules.pullback (bundleBaseChange g E hqc E' hqc' hE)) ≅
      koszulTwistSequence E' hqc' D' p :=
  koszulTwistSequencePullbackIsoOf (bundleBaseChange g E hqc E' hqc' hE)
    (fun d => asIso (thetaSharp g E hqc E' hqc' hE D D' d))
    (bundlePullbackBaseChange g E hqc E' hqc' hE)
    (tautologicalMap_baseChange g E hqc E' hqc' hE D D')
    (tautKernelBaseChange g E hqc E' hqc' hE D D')
    (tautKernelBaseChange_ι g E hqc E' hqc' hE D D') p

include D' in
/-- The pullback of the twisted Koszul filtration is short exact. -/
public theorem shortExact_koszulTwistSequence_baseChange (p : ℕ) :
    ((koszulTwistSequence E hqc D p).map
      (Scheme.Modules.pullback (bundleBaseChange g E hqc E' hqc' hE))).ShortExact :=
  ShortComplex.shortExact_of_iso (koszulTwistSequenceBaseChange g E hqc E' hqc' hE D D' p).symm
    (shortExact_koszulTwistSequence E' hqc' D' p)

/-- Pasting a square `a ≫ b = d ≫ e` with a naturality square `c ≫ g = e ≫ f`. -/
private theorem comp_comp_eq_of_eq_of_eq {C : Type*} [Category C] {A B D X Y Z : C}
    {a : A ⟶ B} {b : B ⟶ X} {f : X ⟶ Y} {d : A ⟶ D} {e : D ⟶ X} {c : D ⟶ Z} {g : Z ⟶ Y}
    (h₁ : a ≫ b = d ≫ e) (h₂ : c ≫ g = e ≫ f) : a ≫ b ≫ f = d ≫ c ≫ g := by
  rw [← Category.assoc, h₁, Category.assoc, h₂]

/-- **The base change map commutes with the connecting morphisms of the twisted Koszul
filtrations.** -/
public theorem canonicalδ_koszul_baseChange (p q : ℕ) :
    (Scheme.Modules.pullback g).map (Stacks.DerivedIndexing.canonicalδ
        (bundlePushforward E hqc) (shortExact_koszulTwistSequence E hqc D p) q) ≫
      Stacks.AlgebraicGeometry.HigherDirectImageBaseChange.higherBaseChange
          (relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc)).toBase g
          (relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E' hqc')).toBase
          (bundleBaseChange g E hqc E' hqc' hE) (bundleBaseChange_toBase g E hqc E' hqc' hE) (q + 1)
          (koszulTwistSequence E hqc D p).X₁ ≫
        ((bundlePushforward E' hqc').rightDerivedPlus ((q + 1 : ℕ) : ℤ)).map
          (koszulTwistSequenceBaseChange g E hqc E' hqc' hE D D' p).hom.τ₁ =
      Stacks.AlgebraicGeometry.HigherDirectImageBaseChange.higherBaseChange
          (relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc)).toBase g
          (relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E' hqc')).toBase
          (bundleBaseChange g E hqc E' hqc' hE) (bundleBaseChange_toBase g E hqc E' hqc' hE) q
          (koszulTwistSequence E hqc D p).X₃ ≫
        ((bundlePushforward E' hqc').rightDerivedPlus (q : ℤ)).map
          (koszulTwistSequenceBaseChange g E hqc E' hqc' hE D D' p).hom.τ₃ ≫
        Stacks.DerivedIndexing.canonicalδ (bundlePushforward E' hqc')
          (shortExact_koszulTwistSequence E' hqc' D' p) q := by
  have h₁ := Stacks.AlgebraicGeometry.HigherDirectImageBaseChange.canonicalδ_comp_higherBaseChange
    (relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc)).toBase g
    (relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E' hqc')).toBase
    (bundleBaseChange g E hqc E' hqc' hE) (bundleBaseChange_toBase g E hqc E' hqc' hE)
    (shortExact_koszulTwistSequence E hqc D p)
    (shortExact_koszulTwistSequence_baseChange g E hqc E' hqc' hE D D' p) q
  have h₂ := (Stacks.DerivedIndexing.plusDelta (bundlePushforward E' hqc')).δ_naturality
    (shortExact_koszulTwistSequence_baseChange g E hqc E' hqc' hE D D' p)
    (shortExact_koszulTwistSequence E' hqc' D' p)
    (koszulTwistSequenceBaseChange g E hqc E' hqc' hE D D' p).hom q
  exact comp_comp_eq_of_eq_of_eq h₁ h₂

/-- **`(⋀ᵖ K ⊗ 𝒪(1)) ⊗ 𝒪(-p-1) ≅ ⋀ᵖ K ⊗ 𝒪(-p)` under base change.** -/
public theorem koszulTwistIso_baseChange (p : ℕ) :
    (Scheme.Modules.pullback (bundleBaseChange g E hqc E' hqc' hE)).map
          (koszulTwistIso E hqc D p).hom ≫
        (koszulTermIsoOf (bundleBaseChange g E hqc E' hqc' hE)
          (fun d => asIso (thetaSharp g E hqc E' hqc' hE D D' d))
          (tautKernelBaseChange g E hqc E' hqc' hE D D') p).hom =
      (tensorPullbackIso (bundleBaseChange g E hqc E' hqc' hE).toLRSHom.toShHom
          (tensorPullbackIso (bundleBaseChange g E hqc E' hqc' hE).toLRSHom.toShHom
            (kerExtIsoOf (bundleBaseChange g E hqc E' hqc' hE)
              (tautKernelBaseChange g E hqc E' hqc' hE D D') p)
            (@asIso _ _ _ _ (thetaSharp g E hqc E' hqc' hE D D' ((1 : ℕ) : ℤ))
              (isIso_thetaSharp g E hqc E' hqc' hE D D' _)))
          (@asIso _ _ _ _ (thetaSharp g E hqc E' hqc' hE D D' (-((p + 1 : ℕ) : ℤ)))
            (isIso_thetaSharp g E hqc E' hqc' hE D D' _))).hom ≫
        (koszulTwistIso E' hqc' D' p).hom :=
  koszulTwistIso_pullback_of (bundleBaseChange g E hqc E' hqc' hE)
    (fun d => asIso (thetaSharp g E hqc E' hqc' hE D D' d))
    (fun i j => thetaSharp_twistMul g E hqc E' hqc' hE D D' i j)
    (tautKernelBaseChange g E hqc E' hqc' hE D D') p

/-- `b^*(⋀ᵖ K ⊗ 𝒪(-p)) ≅ ⋀ᵖ K' ⊗ 𝒪'(-p)`. -/
public abbrev koszulTermBaseChange (p : ℕ) :
    (Scheme.Modules.pullback (bundleBaseChange g E hqc E' hqc' hE)).obj (koszulTerm E hqc D p) ≅
      koszulTerm E' hqc' D' p :=
  koszulTermIsoOf (bundleBaseChange g E hqc E' hqc' hE)
    (fun d => asIso (thetaSharp g E hqc E' hqc' hE D D' d))
    (tautKernelBaseChange g E hqc E' hqc' hE D D') p

/-- The base change map commutes with the connecting morphisms of the twisted Koszul
filtrations, in the indexing by injective resolutions. -/
public theorem δ_koszul_baseChange (p q : ℕ) :
    (Scheme.Modules.pullback g).map
        ((pushDelta _).δ (shortExact_koszulTwistSequence E hqc D p) q) ≫
      Stacks.AlgebraicGeometry.HigherDirectImageBaseChange.higherBaseChangeNat
          (relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc)).toBase g
          (relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E' hqc')).toBase
          (bundleBaseChange g E hqc E' hqc' hE) (bundleBaseChange_toBase g E hqc E' hqc' hE) (q + 1)
          (koszulTwistSequence E hqc D p).X₁ ≫
        ((bundlePushforward E' hqc').rightDerived (q + 1)).map
          (koszulTermBaseChange g E hqc E' hqc' hE D D' (p + 1)).hom =
      Stacks.AlgebraicGeometry.HigherDirectImageBaseChange.higherBaseChangeNat
          (relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc)).toBase g
          (relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E' hqc')).toBase
          (bundleBaseChange g E hqc E' hqc' hE) (bundleBaseChange_toBase g E hqc E' hqc' hE) q
          (koszulTwistSequence E hqc D p).X₃ ≫
        ((bundlePushforward E' hqc').rightDerived q).map
          (koszulTwistSequenceBaseChange g E hqc E' hqc' hE D D' p).hom.τ₃ ≫
        (pushDelta _).δ (shortExact_koszulTwistSequence E' hqc' D' p) q := by
  have h₁ := Stacks.AlgebraicGeometry.HigherDirectImageBaseChange.δ_comp_higherBaseChangeNat
    (relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc)).toBase g
    (relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E' hqc')).toBase
    (bundleBaseChange g E hqc E' hqc' hE) (bundleBaseChange_toBase g E hqc E' hqc' hE)
    (shortExact_koszulTwistSequence E hqc D p)
    (shortExact_koszulTwistSequence_baseChange g E hqc E' hqc' hE D D' p) q
  have h₂ := (pushDelta
      (relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E' hqc')).toBase).δ_naturality
    (shortExact_koszulTwistSequence_baseChange g E hqc E' hqc' hE D D' p)
    (shortExact_koszulTwistSequence E' hqc' D' p)
    (koszulTwistSequenceBaseChange g E hqc E' hqc' hE D D' p).hom q
  exact comp_comp_eq_of_eq_of_eq h₁ h₂

variable {n : ℕ} (hn : 1 ≤ n) (hfree : Scheme.Modules.IsFiniteLocallyFreeOfRank E (n + 1))
  (hfree' : Scheme.Modules.IsFiniteLocallyFreeOfRank E' (n + 1))

/-- **The dimension shift of the twisted Koszul filtration is compatible with base change.** -/
public theorem koszulShiftIso_baseChange {p : ℕ} (hp : p + 1 ≤ n) (q : ℕ) :
    (Scheme.Modules.pullback g).map (koszulShiftIso E hqc D hn hfree hp q).hom ≫
        Stacks.AlgebraicGeometry.HigherDirectImageBaseChange.higherBaseChangeNat
          (relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc)).toBase g
          (relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E' hqc')).toBase
          (bundleBaseChange g E hqc E' hqc' hE) (bundleBaseChange_toBase g E hqc E' hqc' hE) (q + 1)
          (koszulTerm E hqc D (p + 1)) ≫
        ((bundlePushforward E' hqc').rightDerived (q + 1)).map
          (koszulTermBaseChange g E hqc E' hqc' hE D D' (p + 1)).hom =
      Stacks.AlgebraicGeometry.HigherDirectImageBaseChange.higherBaseChangeNat
          (relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc)).toBase g
          (relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E' hqc')).toBase
          (bundleBaseChange g E hqc E' hqc' hE) (bundleBaseChange_toBase g E hqc E' hqc' hE) q
          (koszulTerm E hqc D p) ≫
        ((bundlePushforward E' hqc').rightDerived q).map
          (koszulTermBaseChange g E hqc E' hqc' hE D D' p).hom ≫
        (koszulShiftIso E' hqc' D' hn hfree' hp q).hom := by
  have hδ := δ_koszul_baseChange g E hqc E' hqc' hE D D' p q
  have hnat := Stacks.AlgebraicGeometry.HigherDirectImageBaseChange.higherBaseChangeNat_naturality
    (relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc)).toBase g
    (relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E' hqc')).toBase
    (bundleBaseChange g E hqc E' hqc' hE) (bundleBaseChange_toBase g E hqc E' hqc' hE) q
    (koszulTwistIso E hqc D p).inv
  have htw : (Scheme.Modules.pullback (bundleBaseChange g E hqc E' hqc' hE)).map
        (koszulTwistIso E hqc D p).inv ≫
        (koszulTwistSequenceBaseChange g E hqc E' hqc' hE D D' p).hom.τ₃ =
      (koszulTermBaseChange g E hqc E' hqc' hE D D' p).hom ≫ (koszulTwistIso E' hqc' D' p).inv := by
    have key : ∀ {C : Type _} [Category C] {A B A' B' : C} (e : A ≅ B) (e' : A' ≅ B')
        (K : B ⟶ B') (T : A ⟶ A'), e.hom ≫ K = T ≫ e'.hom → e.inv ≫ T = K ≫ e'.inv := by
      intro C _ A B A' B' e e' K T h
      rw [Iso.inv_comp_eq, ← Category.assoc, h, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    exact key ((Scheme.Modules.pullback (bundleBaseChange g E hqc E' hqc' hE)).mapIso
      (koszulTwistIso E hqc D p)) (koszulTwistIso E' hqc' D' p) _ _
      (koszulTwistIso_baseChange g E hqc E' hqc' hE D D' p)
  change (Scheme.Modules.pullback g).map
      (((bundlePushforward E hqc).rightDerived q).map (koszulTwistIso E hqc D p).inv ≫
        (pushDelta _).δ (shortExact_koszulTwistSequence E hqc D p) q) ≫ _ =
    _ ≫ _ ≫ ((bundlePushforward E' hqc').rightDerived q).map (koszulTwistIso E' hqc' D' p).inv ≫
        (pushDelta _).δ (shortExact_koszulTwistSequence E' hqc' D' p) q
  refine ((Functor.map_comp _ _ _ =≫ _).trans (Category.assoc _ _ _)).trans ?_
  refine (congrArg (_ ≫ ·) hδ).trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (· ≫ _) hnat).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  refine congrArg (_ ≫ ·) ?_
  refine ((Category.assoc _ _ _).symm.trans
    (congrArg (· ≫ _) (Functor.map_comp _ _ _).symm)).trans ?_
  refine (congrArg (fun x => ((bundlePushforward E' hqc').rightDerived q).map x ≫ _) htw).trans ?_
  exact (congrArg (· ≫ _) (Functor.map_comp _ _ _)).trans (Category.assoc _ _ _)

/-- **Dimension shifting along the twisted Koszul filtration is compatible with base change.** -/
public theorem koszulChainIso_baseChange : ∀ (p : ℕ) (hp : p ≤ n),
    (Scheme.Modules.pullback g).map (koszulChainIso E hqc D hn hfree p hp).hom ≫
        Stacks.AlgebraicGeometry.HigherDirectImageBaseChange.higherBaseChangeNat
          (relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc)).toBase g
          (relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E' hqc')).toBase
          (bundleBaseChange g E hqc E' hqc' hE) (bundleBaseChange_toBase g E hqc E' hqc' hE) p
          (koszulTerm E hqc D p) ≫
        ((bundlePushforward E' hqc').rightDerived p).map
          (koszulTermBaseChange g E hqc E' hqc' hE D D' p).hom =
      Stacks.AlgebraicGeometry.HigherDirectImageBaseChange.higherBaseChangeNat
          (relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc)).toBase g
          (relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E' hqc')).toBase
          (bundleBaseChange g E hqc E' hqc' hE) (bundleBaseChange_toBase g E hqc E' hqc' hE) 0
          (koszulTerm E hqc D 0) ≫
        ((bundlePushforward E' hqc').rightDerived 0).map
          (koszulTermBaseChange g E hqc E' hqc' hE D D' 0).hom ≫
        (koszulChainIso E' hqc' D' hn hfree' p hp).hom
  | 0, _ => ((congrArg (· ≫ _) ((Scheme.Modules.pullback g).map_id _)).trans
      (Category.id_comp _)).trans (congrArg (_ ≫ ·) (Category.comp_id _)).symm
  | p + 1, hp => by
    have ih := koszulChainIso_baseChange p (by omega)
    have hs := koszulShiftIso_baseChange g E hqc E' hqc' hE D D' hn hfree hfree' hp p
    change (Scheme.Modules.pullback g).map ((koszulChainIso E hqc D hn hfree p (by omega)).hom ≫
        (koszulShiftIso E hqc D hn hfree hp p).hom) ≫ _ =
      _ ≫ _ ≫ (koszulChainIso E' hqc' D' hn hfree' p (by omega)).hom ≫
        (koszulShiftIso E' hqc' D' hn hfree' hp p).hom
    refine ((Functor.map_comp _ _ _ =≫ _).trans (Category.assoc _ _ _)).trans ?_
    refine (congrArg (_ ≫ ·) hs).trans ?_
    refine (Category.assoc _ _ _).symm.trans ?_
    simpa only [Category.assoc] using ih =≫ (koszulShiftIso E' hqc' D' hn hfree' hp p).hom

end Stacks.AlgebraicGeometry.ProjectiveBundleCohomology

end
