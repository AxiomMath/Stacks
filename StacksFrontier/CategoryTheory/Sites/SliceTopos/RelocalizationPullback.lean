module

public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.CategoryTheory.Monoidal.Mon
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init

/-!
# Relocalization for a morphism of topoi: the formal pullback identity

Stacks tag 04IV builds, from a morphism of topoi `f : Sh(C) → Sh(D)`, sheaves
`G ∈ Sh(D)`, `F ∈ Sh(C)` and a morphism `s : F → f⁻¹G`, a commuting square of topoi
relating `Sh(C)/F → Sh(C)` and `Sh(D)/G → Sh(D)`, identifies the inverse image by
`(f_s)⁻¹(H → G) = (f⁻¹H ×_{f⁻¹G} F → F)`, and closes its last compatibility square —
for further data `a : F' → F`, `b : G' → G`, `s' : F' → f⁻¹G'` with
`a ∘ s = (f⁻¹b) ∘ s'` — using the formal identity
`f⁻¹H ×_{f⁻¹G} F ×_F F' = f⁻¹(H ×_G G') ×_{f⁻¹G'} F'`.

Mathlib does not host the slice-topos machinery needed to state the diagram of topoi, so
only that identity is formalized here, with the inverse image `f⁻¹` replaced by an
arbitrary functor `F : D ⥤ C` preserving the pullback of `φ` and `b` (an inverse image is
a left adjoint, hence preserves finite limits). The resulting canonical isomorphism
`(F.obj H ×_{F.obj G} Fbar) ×_{Fbar} Fbar' ≅ F.obj (H ×_G G') ×_{F.obj G'} Fbar'` is
`relocalizeMorphismTopoiPullbackIso`, built from `PreservesPullback.iso` and the
universal property of pullbacks.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits


universe v₁ v₂ u₁ u₂

variable {D : Type u₁} [Category.{v₁} D] {C : Type u₂} [Category.{v₂} C]
variable (F : D ⥤ C)
variable {H G G' : D} (φ : H ⟶ G) (b : G' ⟶ G)
variable {Fbar Fbar' : C} (a : Fbar' ⟶ Fbar)
variable (s : Fbar ⟶ F.obj G) (s' : Fbar' ⟶ F.obj G')
variable (hsq : a ≫ s = s' ≫ F.map b)
variable [HasPullback φ b]
variable [HasPullback (F.map φ) (F.map b)]
variable [HasPullback (F.map φ) s]
variable [HasPullback (pullback.snd (F.map φ) s) a]
variable [HasPullback (F.map (pullback.snd φ b)) s']
variable [PreservesLimit (cospan φ b) F]

/-- Forward map of the relocalization pullback isomorphism. -/
noncomputable def relocalizeHom :
    pullback (pullback.snd (F.map φ) s) a ⟶
      pullback (F.map (pullback.snd φ b)) s' :=
  pullback.lift
    (pullback.lift
        (pullback.fst (pullback.snd (F.map φ) s) a ≫ pullback.fst (F.map φ) s)
        (pullback.snd (pullback.snd (F.map φ) s) a ≫ s')
        (by
          simp only [Category.assoc]
          rw [pullback.condition, pullback.condition_assoc, hsq])
      ≫ (PreservesPullback.iso F φ b).inv)
    (pullback.snd _ _)
    (by
      have hinv : (PreservesPullback.iso F φ b).inv ≫ F.map (pullback.snd φ b)
          = pullback.snd (F.map φ) (F.map b) := by
        rw [← PreservesPullback.iso_hom_snd F φ b, ← Category.assoc,
          Iso.inv_hom_id, Category.id_comp]
      rw [Category.assoc, hinv, pullback.lift_snd])

/-- Backward map of the relocalization pullback isomorphism. -/
noncomputable def relocalizeInv :
    pullback (F.map (pullback.snd φ b)) s' ⟶
      pullback (pullback.snd (F.map φ) s) a :=
  pullback.lift
    (pullback.lift
        (pullback.fst (F.map (pullback.snd φ b)) s'
          ≫ (PreservesPullback.iso F φ b).hom
          ≫ pullback.fst (F.map φ) (F.map b))
        (pullback.snd (F.map (pullback.snd φ b)) s' ≫ a)
        (by
          simp only [Category.assoc, PreservesPullback.iso_hom_fst_assoc]
          rw [← F.map_comp, pullback.condition, F.map_comp, pullback.condition_assoc, hsq]))
    (pullback.snd _ _)
    (by rw [pullback.lift_snd])

/-- Let `F : D ⥤ C` be a functor preserving the pullback of `φ` and `b`.
Given `φ : H ⟶ G`, `b : G' ⟶ G` in `D` and `a : Fbar' ⟶ Fbar`,
`s : Fbar ⟶ F.obj G`, `s' : Fbar' ⟶ F.obj G'` in `C` satisfying
`a ≫ s = s' ≫ F.map b`, there is a canonical isomorphism
`(F.obj H ×_{F.obj G} Fbar) ×_{Fbar} Fbar'  ≅  F.obj (H ×_G G') ×_{F.obj G'} Fbar'`.

This is the formal pullback identity at the end of the proof, with the
topos-theoretic inverse image `f⁻¹` replaced by the generic
pullback-preserving functor `F`. -/
@[stacks 04IV]
noncomputable def relocalizeMorphismTopoiPullbackIso :
    pullback (pullback.snd (F.map φ) s) a ≅
      pullback (F.map (pullback.snd φ b)) s' where
  hom := relocalizeHom F φ b a s s' hsq
  inv := relocalizeInv F φ b a s s' hsq
  hom_inv_id := by
    unfold relocalizeHom relocalizeInv
    apply pullback.hom_ext
    · apply pullback.hom_ext
      · simp [Category.id_comp, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc]
      · have hY : pullback.fst (pullback.snd (F.map φ) s) a ≫
            pullback.snd (F.map φ) s
              = pullback.snd (pullback.snd (F.map φ) s) a ≫ a :=
          pullback.condition
        simp [Category.id_comp, Category.assoc, pullback.lift_fst, pullback.lift_snd,
          pullback.lift_snd_assoc, hY]
    · simp [Category.id_comp, Category.assoc, pullback.lift_snd]
  inv_hom_id := by
    unfold relocalizeHom relocalizeInv
    apply pullback.hom_ext
    · apply (cancel_mono (PreservesPullback.iso F φ b).hom).mp
      apply pullback.hom_ext
      · simp [Category.id_comp, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc]
      · have hPb : pullback.fst (F.map (pullback.snd φ b)) s' ≫
            F.map (pullback.snd φ b)
              = pullback.snd (F.map (pullback.snd φ b)) s' ≫ s' :=
          pullback.condition
        simp [Category.id_comp, Category.assoc, pullback.lift_fst, pullback.lift_snd,
          pullback.lift_snd_assoc, hPb]
    · simp [Category.id_comp, Category.assoc, pullback.lift_snd]

