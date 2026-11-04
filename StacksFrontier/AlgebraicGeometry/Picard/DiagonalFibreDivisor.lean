module

public import StacksFrontier.AlgebraicGeometry.Picard.HilbertPointAddition
public import StacksFrontier.AlgebraicGeometry.Divisors.IdealSheafPullbackComap
public import StacksFrontier.AlgebraicGeometry.Divisors.DivisorPicardClass
public import StacksFrontier.AlgebraicGeometry.Divisors.RegularImmersion.BaseChangeDivisor
public import StacksFrontier.AlgebraicGeometry.PicardGroup.PullbackHom
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The diagonal of a smooth relative curve, restricted to the fibres

Let `f : X ⟶ S` be separated and smooth of relative dimension one, and let `Δ ⊆ X ×_S X` be the
diagonal, the graph of the identity regarded as a relative point of `X` over `X` (the second
factor). For a section `t : S ⟶ X` of `f`, the fibre of the second projection over `t` is the
morphism `X ⟶ X ×_S X`, `y ↦ (y, t)`, and the restriction of the diagonal to it is the divisor
of the point `t`:

  `Δ ∩ (X × {t}) = t(S) ⊆ X`,   and   `[ℐ_Δ|_{X × {t}}] = [ℐ_{t(S)}]`   in   `Pic(X)`.

The diagonal is a relative effective Cartier divisor over the second factor (Tag 0B9D), so its
restriction to a fibre is again effective Cartier (Tag 056Q), and the ideal sheaf pulls back to
the ideal sheaf of the restriction. This is the input `ℒ' = 𝒪_{X×X}(Δ) ⊗ pr^*𝒪_X(-x')` of the
family argument in the last paragraph of the proof of Stacks 0FH9.

## Main definitions

* `Stacks.Hilbert.diagonalIdeal`: the ideal of the diagonal of `X ×_S X`.
* `Stacks.Hilbert.fibreAt`: the fibre `X ⟶ X ×_S X`, `y ↦ (y, t)`, over a section `t`.

## Main results

* `Stacks.Hilbert.isEffectiveCartierDivisor_diagonalIdeal`: the diagonal is an effective Cartier
  divisor.
* `Stacks.Hilbert.diagonalIdeal_comap_fibreAt`: its restriction to the fibre over `t` is cut out
  by the kernel of `t`.
* `Stacks.Hilbert.isEffectiveCartierDivisor_ker_section`: the image of a section is an
  effective Cartier divisor.
* `Stacks.Hilbert.pullbackPicardClass_fibreAt_diagonalIdeal`: `[ℐ_Δ|_{X × {t}}] = [ℐ_{t(S)}]`.

## References

* [Stacks Project, Tag 0B9D](https://stacks.math.columbia.edu/tag/0B9D)
* [Stacks Project, Tag 056Q](https://stacks.math.columbia.edu/tag/056Q)
* [Stacks Project, Tag 0FH9](https://stacks.math.columbia.edu/tag/0FH9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.Hilbert

variable {S X : Scheme.{u}} (f : X ⟶ S)

/-- The ideal of the diagonal of `X ×_S X`, i.e. of the graph of the identity regarded as a
relative point of `X` over the second factor. -/
def diagonalIdeal : (pullback f f).IdealSheafData :=
  pointIdeal (Over.mk f) (Over.mk f) (𝟙 _)

/-- The diagonal of a separated morphism is a closed immersion, in the form of the graph of the
identity. -/
instance isClosedImmersion_pointGraph_id [IsSeparated f] :
    IsClosedImmersion (pointGraph (Over.mk f) (Over.mk f) (𝟙 _)) :=
  have : IsSeparated (Over.mk f).hom := inferInstanceAs (IsSeparated f)
  isClosedImmersion_pointGraph_of_isSeparated (Over.mk f) (Over.mk f) (𝟙 _)

/-- **The diagonal of a smooth relative curve is a relative effective Cartier divisor** over the
second factor. -/
theorem isRelativeEffectiveCartierDivisor_diagonalIdeal [IsSeparated f]
    [SmoothOfRelativeDimension 1 f] :
    Stacks.Divisors.IsRelativeEffectiveCartierDivisor (pullback.snd f f) (diagonalIdeal f) := by
  have : SmoothOfRelativeDimension 1 (pullback.snd f f) :=
    (smoothOfRelativeDimension_isStableUnderBaseChange 1).of_isPullback
      (IsPullback.of_hasPullback f f) inferInstance
  have := isFiniteLocallyFreeOfRank_pointIdeal (Over.mk f) (Over.mk f) (𝟙 _)
  have : Stacks.Morphisms.IsFiniteLocallyFree
      ((diagonalIdeal f).subschemeι ≫ pullback.snd f f) :=
    Stacks.Morphisms.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree
      ((pointIdeal (Over.mk f) (Over.mk f) (𝟙 _)).subschemeι ≫
        ((Over.pullback (Over.mk f).hom).obj (Over.mk f)).hom) 1
  exact isRelativeEffectiveCartierDivisor_of_isFiniteLocallyFree _ _

/-- **The diagonal of a smooth relative curve is an effective Cartier divisor.** -/
theorem isEffectiveCartierDivisor_diagonalIdeal [IsSeparated f]
    [SmoothOfRelativeDimension 1 f] :
    Stacks.Divisors.IsEffectiveCartierDivisor (diagonalIdeal f) :=
  (isRelativeEffectiveCartierDivisor_diagonalIdeal f).1

variable {f}

/-- The fibre `X ⟶ X ×_S X`, `y ↦ (y, t)`, of the second projection over a section `t` of `f`. -/
def fibreAt (t : S ⟶ X) (ht : t ≫ f = 𝟙 S) : X ⟶ pullback f f :=
  pullback.lift (𝟙 X) (f ≫ t) (by rw [Category.assoc, ht, Category.comp_id, Category.id_comp])

/-- The first projection of `fibreAt t ht` is the identity of `X`. -/
@[reassoc (attr := simp)]
theorem fibreAt_fst (t : S ⟶ X) (ht : t ≫ f = 𝟙 S) : fibreAt t ht ≫ pullback.fst f f = 𝟙 X :=
  pullback.lift_fst _ _ _

/-- The second projection of `fibreAt t ht` is `f ≫ t`. -/
@[reassoc (attr := simp)]
theorem fibreAt_snd (t : S ⟶ X) (ht : t ≫ f = 𝟙 S) :
    fibreAt t ht ≫ pullback.snd f f = f ≫ t :=
  pullback.lift_snd _ _ _

/-- The fibre over `t` is the base change of the second projection along `t`. -/
theorem isPullback_fibreAt (t : S ⟶ X) (ht : t ≫ f = 𝟙 S) :
    IsPullback (fibreAt t ht) f (pullback.snd f f) t := by
  refine IsPullback.of_right ?_ (fibreAt_snd t ht) (IsPullback.of_hasPullback f f)
  rw [fibreAt_fst, ht]
  exact IsPullback.id_horiz f

/-- The diagonal morphism `X ⟶ X ×_S X`. -/
def diag (f : X ⟶ S) : X ⟶ pullback f f :=
  pullback.lift (𝟙 X) (𝟙 X) (by simp)

/-- The first projection of the diagonal is the identity of `X`. -/
@[reassoc (attr := simp)]
theorem diag_fst : diag f ≫ pullback.fst f f = 𝟙 X := pullback.lift_fst _ _ _

/-- The second projection of the diagonal is the identity of `X`. -/
@[reassoc (attr := simp)]
theorem diag_snd : diag f ≫ pullback.snd f f = 𝟙 X := pullback.lift_snd _ _ _

/-- The graph of the identity is the diagonal. -/
theorem pointGraph_id_eq : pointGraph (Over.mk f) (Over.mk f) (𝟙 _) = diag f :=
  rfl

/-- The section `t` is the scheme-theoretic intersection of the diagonal with the fibre over
`t`. -/
theorem isPullback_section_fibreAt (t : S ⟶ X) (ht : t ≫ f = 𝟙 S) :
    IsPullback t t (fibreAt t ht) (pointGraph (Over.mk f) (Over.mk f) (𝟙 _)) := by
  rw [pointGraph_id_eq]
  have hw : t ≫ fibreAt t ht = t ≫ diag f := by
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, Category.assoc, fibreAt_fst, diag_fst]
    · rw [Category.assoc, Category.assoc, fibreAt_snd, diag_snd, ← Category.assoc, ht,
        Category.id_comp, Category.comp_id]
  have key : ∀ s : PullbackCone (fibreAt t ht) (diag f),
      s.fst = s.snd ∧ s.fst ≫ f ≫ t = s.snd := fun s => by
    have h1 := congrArg (fun m => m ≫ pullback.fst f f) s.condition
    have h2 := congrArg (fun m => m ≫ pullback.snd f f) s.condition
    simp only [Category.assoc, fibreAt_fst, fibreAt_snd, diag_fst, diag_snd,
      Category.comp_id] at h1 h2
    exact ⟨h1, h2⟩
  refine ⟨⟨hw⟩, ⟨PullbackCone.IsLimit.mk _ (fun s => s.fst ≫ f) ?_ ?_ ?_⟩⟩
  · intro s
    rw [Category.assoc, (key s).2, (key s).1]
  · intro s
    rw [Category.assoc, (key s).2]
  · intro s m hm1 _
    rw [← hm1, Category.assoc, ht, Category.comp_id]

/-- **The restriction of the diagonal to the fibre over `t` is cut out by the kernel of `t`.** -/
theorem diagonalIdeal_comap_fibreAt [IsSeparated f] (t : S ⟶ X) (ht : t ≫ f = 𝟙 S) :
    (diagonalIdeal f).comap (fibreAt t ht) = t.ker := by
  have h := isPullback_section_fibreAt t ht
  rw [diagonalIdeal, pointIdeal, ← Scheme.IdealSheafData.ker_fst_of_isClosedImmersion,
    ← Scheme.Hom.ker_comp_of_isIso h.isoPullback.hom, h.isoPullback_hom_fst]

/-- **The restriction of the diagonal to the fibre over a section is an effective Cartier
divisor**: the fibre is a base change of the second projection, over which the diagonal is a
relative effective Cartier divisor (Tag 056Q). -/
theorem isPullbackDefined_fibreAt_diagonalIdeal [IsSeparated f] [SmoothOfRelativeDimension 1 f]
    (t : S ⟶ X) (ht : t ≫ f = 𝟙 S) :
    Stacks.Divisors.IsPullbackDefined (fibreAt t ht) (diagonalIdeal f) := by
  have hrel := isRelativeEffectiveCartierDivisor_diagonalIdeal f
  have : Flat ((diagonalIdeal f).subschemeι ≫ pullback.snd f f) := hrel.2
  have hbc := AlgebraicGeometry.isEffectiveCartierDivisor_comap_pullback (pullback.snd f f) t
    (diagonalIdeal f) hrel.1
  have h := (isPullback_fibreAt t ht).flip
  have hcomp : (diagonalIdeal f).comap (fibreAt t ht) =
      ((diagonalIdeal f).comap (pullback.snd t (pullback.snd f f))).comap h.isoPullback.hom := by
    rw [← Scheme.IdealSheafData.comap_comp, h.isoPullback_hom_snd]
  show Stacks.Divisors.IsEffectiveCartierDivisor _
  rw [hcomp]
  exact Stacks.Divisors.isPullbackDefined_of_flat h.isoPullback.hom _ hbc

/-- **The image of a section of a separated smooth relative curve is an effective Cartier
divisor.** -/
@[sga "4 XVII 6.3.8" "partial"]
theorem isEffectiveCartierDivisor_ker_section [IsSeparated f] [SmoothOfRelativeDimension 1 f]
    (t : S ⟶ X) (ht : t ≫ f = 𝟙 S) :
    Stacks.Divisors.IsEffectiveCartierDivisor t.ker := by
  have h := isPullbackDefined_fibreAt_diagonalIdeal t ht
  change Stacks.Divisors.IsEffectiveCartierDivisor _ at h
  rwa [diagonalIdeal_comap_fibreAt] at h

/-- The invertibility of the ideal sheaf of an effective Cartier divisor, in the spelling the
Picard group of a scheme is stated at. -/
theorem isInvertible_negativeTwist' {Y : Scheme.{u}} (D : Y.IdealSheafData)
    (hD : Stacks.Divisors.IsEffectiveCartierDivisor D) :
    Stacks.SheafOfModules.IsInvertible Y.presheaf Y.ringCatIsSheaf
      (Stacks.Divisors.negativeTwist' D) :=
  have := hD
  Stacks.Divisors.isInvertible_negativeTwist_picard D

/-- **The ideal sheaf of an effective Cartier divisor pulls back to the ideal sheaf of its
inverse image**, on Picard classes, whenever the inverse image is again effective Cartier. -/
theorem pullbackPicardClass_negativeTwist' {Y Z : Scheme.{u}} (h : Z ⟶ Y) (D : Y.IdealSheafData)
    (E : Z.IdealSheafData) (hDE : D.comap h = E) (hD : Stacks.Divisors.IsEffectiveCartierDivisor D)
    (hE : Stacks.Divisors.IsEffectiveCartierDivisor E) :
    Stacks.SheafOfModules.pullbackPicardClass h (Stacks.Divisors.negativeTwist' D)
        (isInvertible_negativeTwist' D hD) =
      Z.picardClass (Stacks.Divisors.negativeTwist' E) (isInvertible_negativeTwist' E hE) := by
  subst hDE
  exact (Z.picardClass_eq_iff _ _ _ _).mpr
    ⟨Stacks.Divisors.pullbackIdealSheafComapIso h D hE⟩

/-- **The restriction of the diagonal to the fibre over a section is the divisor of the
section**, on Picard classes of ideal sheaves: `[ℐ_Δ|_{X × {t}}] = [ℐ_{t(S)}]`. -/
theorem pullbackPicardClass_fibreAt_diagonalIdeal [IsSeparated f] [SmoothOfRelativeDimension 1 f]
    (t : S ⟶ X) (ht : t ≫ f = 𝟙 S) :
    Stacks.SheafOfModules.pullbackPicardClass (fibreAt t ht)
        (Stacks.Divisors.negativeTwist' (diagonalIdeal f))
        (isInvertible_negativeTwist' _ (isEffectiveCartierDivisor_diagonalIdeal f)) =
      X.picardClass (Stacks.Divisors.negativeTwist' t.ker)
        (isInvertible_negativeTwist' _ (isEffectiveCartierDivisor_ker_section t ht)) :=
  pullbackPicardClass_negativeTwist' _ _ _ (diagonalIdeal_comap_fibreAt t ht)
    (isEffectiveCartierDivisor_diagonalIdeal f) (isEffectiveCartierDivisor_ker_section t ht)

end Stacks.Hilbert

end
