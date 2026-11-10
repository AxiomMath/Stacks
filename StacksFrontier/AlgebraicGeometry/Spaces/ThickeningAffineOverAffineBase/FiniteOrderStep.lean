module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ThickeningAffineFiniteOrder
public import StacksFrontier.AlgebraicGeometry.Spaces.ThickeningAffineOverAffineBase.FirstOrderStep

/-!
# Affineness over a finite-order thickening of an affine base

Let `U` be an algebraic space over an affine object `T` of the site and let `T₀ ⟶ T` be a
finite-order thickening.  If `U ×_T T₀` is affine, then `U` is affine.

The proof is the adic filtration of the defining ideal sheaf `𝓘` of `T₀ ⟶ T`.  The closed
subschemes `Z_j = V(𝓘 ^ (j + 1))` of `T` are objects of the site, affine, and interpolate between
`Z_0 = V(𝓘) ≅ T₀` and `Z_n = V(⊥) ≅ T` when `𝓘 ^ (n + 1) = ⊥`.  Each inclusion `Z_j ⟶ Z_{j+1}`
is a first-order thickening (`Stacks.Thickenings.isFirstOrderThickening_inclusion_pow`), and
`(U ×_T Z_{j+1}) ×_{Z_{j+1}} Z_j ≅ U ×_T Z_j`, so the first-order case
`AlgebraicGeometry.Space.isAffineSpace_of_isFirstOrderThickening_pullback`, applied over the
base `Z_{j+1}`, propagates affineness from `U ×_T Z_j` to `U ×_T Z_{j+1}`.

## Main results

* `AlgebraicGeometry.Space.isAffineSpace_of_isFiniteOrderThickening_pullback`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The closed subscheme of the scheme underlying an object `T` of the site cut out by an ideal
sheaf `J`, as an object of the site over `S`. -/
def closedSubschemeOverObj (T : BigFppfOver B S hS)
    (J : ((BigFppfOver.toScheme B S hS).obj T).IdealSheafData) : BigFppfOver B S hS :=
  BigFppfOver.mk B S hS (Scheme.size_lt_of_isClosedImmersion J.subschemeι T.left.property)
    (J.subschemeι ≫ B.inclusion.map T.hom)

/-- The inclusion of the closed subscheme cut out by `J` into `T`, as a morphism of the site. -/
def closedSubschemeOverι (T : BigFppfOver B S hS)
    (J : ((BigFppfOver.toScheme B S hS).obj T).IdealSheafData) :
    closedSubschemeOverObj B S hS T J ⟶ T :=
  Over.homMk (ObjectProperty.homMk J.subschemeι) rfl

/-- The underlying morphism of schemes of `closedSubschemeOverι B S hS T J` is the closed
immersion `J.subschemeι`. -/
lemma toScheme_map_closedSubschemeOverι (T : BigFppfOver B S hS)
    (J : ((BigFppfOver.toScheme B S hS).obj T).IdealSheafData) :
    (BigFppfOver.toScheme B S hS).map (closedSubschemeOverι B S hS T J) = J.subschemeι :=
  rfl

/-- The inclusion of closed subschemes `V(K) ⟶ V(J)` for `J ≤ K`, as a morphism of the site. -/
def closedSubschemeOverInclusion (T : BigFppfOver B S hS)
    {J K : ((BigFppfOver.toScheme B S hS).obj T).IdealSheafData} (h : J ≤ K) :
    closedSubschemeOverObj B S hS T K ⟶ closedSubschemeOverObj B S hS T J :=
  BigFppfOver.homMk B S hS _ _ (Scheme.IdealSheafData.inclusion h)
    (Scheme.IdealSheafData.inclusion_subschemeι_assoc h _)

/-- The inclusion `V(K) ⟶ V(J)` for `J ≤ K` composed with the inclusion of `V(J)` into `T` is the
inclusion of `V(K)` into `T`. -/
lemma closedSubschemeOverInclusion_ι (T : BigFppfOver B S hS)
    {J K : ((BigFppfOver.toScheme B S hS).obj T).IdealSheafData} (h : J ≤ K) :
    closedSubschemeOverInclusion B S hS T h ≫ closedSubschemeOverι B S hS T J =
      closedSubschemeOverι B S hS T K :=
  BigFppfOver.map_toScheme_injective B S hS
    ((Functor.map_comp _ _ _).trans (Scheme.IdealSheafData.inclusion_subschemeι h))

/-- If `φ` is an isomorphism and the base change of `π : U ⟶ T` along `φ ≫ b` is an affine space,
then so is the base change of `π` along `b`. -/
lemma isAffineSpace_pullback_of_isIso_comp {U : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {T T₁ T₂ : BigFppfOver B S hS} (π : U ⟶ yoneda.obj T) (φ : T₁ ⟶ T₂) [IsIso φ]
    (b : T₂ ⟶ T) (h : IsAffineSpace B S hS (pullback π (yoneda.map (φ ≫ b)))) :
    IsAffineSpace B S hS (pullback π (yoneda.map b)) := by
  rw [Functor.map_comp] at h
  exact h.of_iso ((pullbackLeftPullbackSndIso π (yoneda.map b) (yoneda.map φ)).symm ≪≫
    asIso (pullback.fst _ _))

/-- **An algebraic space over an affine base whose base change to a finite-order thickening of
the base is affine is affine.** -/
theorem isAffineSpace_of_isFiniteOrderThickening_pullback {U : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hU : IsAlgebraicSpace B S hS U) {T₀ T : BigFppfOver B S hS}
    [IsAffine ((BigFppfOver.toScheme B S hS).obj T)] (k : T₀ ⟶ T)
    (hk : Stacks.Thickenings.IsFiniteOrderThickening ((BigFppfOver.toScheme B S hS).map k))
    (π : U ⟶ yoneda.obj T) (hU₀ : IsAffineSpace B S hS (pullback π (yoneda.map k))) :
    IsAffineSpace B S hS U := by
  classical
  have : _root_.AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map k) := hk.1
  obtain ⟨n, hn⟩ := hk.2
  set i := (BigFppfOver.toScheme B S hS).map k with hi
  set I := i.ker with hI
  let Z : ℕ → BigFppfOver B S hS := fun j ↦ closedSubschemeOverObj B S hS T (I ^ (j + 1))
  let z : ∀ j, Z j ⟶ T := fun j ↦ closedSubschemeOverι B S hS T (I ^ (j + 1))
  have hZaff : ∀ j, IsAffine ((BigFppfOver.toScheme B S hS).obj (Z j)) := fun j ↦
    @isAffine_of_isAffineHom _ _ (I ^ (j + 1)).subschemeι
      (isAffineHom_of_isInducing _ (I ^ (j + 1)).subschemeι.isClosedEmbedding.isInducing
        (I ^ (j + 1)).subschemeι.isClosedEmbedding.isClosed_range) _
  have hpb : ∀ {W : BigFppfOver B S hS} (a : W ⟶ T),
      IsAlgebraicSpace B S hS (pullback π (yoneda.map a)) := fun a ↦
    isAlgebraicSpace_pullback B S hS π (yoneda.map a) hU (isAlgebraicSpace_yoneda B S hS _)
      (isAlgebraicSpace_yoneda B S hS T)
  have h0 : IsAffineSpace B S hS (pullback π (yoneda.map (z 0))) := by
    change IsAffineSpace B S hS
      (pullback π (yoneda.map (closedSubschemeOverι B S hS T (I ^ (0 + 1)))))
    rw [pow_one]
    let φ : T₀ ⟶ closedSubschemeOverObj B S hS T I :=
      BigFppfOver.homMk B S hS _ _ i.toImage (by
        rw [← Category.assoc]
        exact (congrArg (· ≫ B.inclusion.map T.hom) i.toImage_imageι).trans
          (congrArg B.inclusion.map (Over.w k)))
    have : IsIso ((BigFppfOver.toScheme B S hS).map φ) :=
      inferInstanceAs (IsIso i.toImage)
    have : IsIso φ := isIso_of_reflects_iso φ (BigFppfOver.toScheme B S hS)
    have hφ : φ ≫ closedSubschemeOverι B S hS T I = k :=
      BigFppfOver.map_toScheme_injective B S hS i.toImage_imageι
    exact isAffineSpace_pullback_of_isIso_comp B S hS π φ _ (hφ ▸ hU₀)
  have hstep : ∀ j, IsAffineSpace B S hS (pullback π (yoneda.map (z j))) →
      IsAffineSpace B S hS (pullback π (yoneda.map (z (j + 1)))) := by
    intro j hj
    have := hZaff (j + 1)
    have hle : I ^ (j + 2) ≤ I ^ (j + 1) :=
      Stacks.Thickenings.idealSheafData_pow_le_pow I (Nat.le_succ _)
    let e : Z j ⟶ Z (j + 1) := closedSubschemeOverInclusion B S hS T hle
    refine isAffineSpace_of_isFirstOrderThickening_pullback B S hS (hpb (z (j + 1))) e
      (Stacks.Thickenings.isFirstOrderThickening_inclusion_pow I j hle)
      (pullback.snd π (yoneda.map (z (j + 1)))) (hj.of_iso ((pullback.congrHom rfl ?_).trans
        (pullbackLeftPullbackSndIso π (yoneda.map (z (j + 1))) (yoneda.map e)).symm))
    rw [← Functor.map_comp, closedSubschemeOverInclusion_ι B S hS T hle]
  have hall : ∀ j, IsAffineSpace B S hS (pullback π (yoneda.map (z j))) := Nat.rec h0 hstep
  have hn' : IsAffineSpace B S hS (pullback π (yoneda.map (closedSubschemeOverι B S hS T ⊥))) :=
    hn ▸ hall n
  have : IsIso ((BigFppfOver.toScheme B S hS).map (closedSubschemeOverι B S hS T ⊥)) :=
    inferInstanceAs (IsIso (Scheme.IdealSheafData.subschemeι ⊥))
  have : IsIso (closedSubschemeOverι B S hS T ⊥) :=
    isIso_of_reflects_iso _ (BigFppfOver.toScheme B S hS)
  exact hn'.of_iso (asIso (pullback.fst _ _))

end AlgebraicGeometry.Space
