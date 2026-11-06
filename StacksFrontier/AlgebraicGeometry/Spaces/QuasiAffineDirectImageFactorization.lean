module

public import StacksFrontier.AlgebraicGeometry.Spaces.DescendingProperties.Separated
public import StacksFrontier.AlgebraicGeometry.Spaces.DirectImageAlgebraFactorization
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ResolutionPropertyQuasiAffine
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiAffineComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiSeparatedTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentPushforwardQcqs

/-!
# Quasi-affineness and the canonical factorization through the relative spectrum

Let `f : Y ⟶ X` be a quasi-compact, quasi-separated morphism of algebraic spaces over a scheme
`S`, with its canonical factorization `Y ⟶ \underline{Spec}_X(f_* 𝒪_Y) ⟶ X`. If the first factor
is an open immersion then `f` is quasi-affine.

## Main results

* `AlgebraicGeometry.Space.isQuasiAffineHom_of_isOpenImmersion`: a quasi-compact open immersion
  of algebraic spaces over `S` is quasi-affine.
* `AlgebraicGeometry.Space.isQuasiAffineHom_of_isOpenImmersion_directImageFactorizationMap`: if
  the canonical morphism `Y ⟶ \underline{Spec}_X(f_* 𝒪_Y)` of a quasi-compact `f` with
  quasi-coherent direct-image algebra is an open immersion, then `f` is quasi-affine.
* `AlgebraicGeometry.Space.isQuasiAffineHom_of_isOpenImmersion_qcqsDirectImageFactorizationMap`:
  if the canonical morphism `Y ⟶ \underline{Spec}_X(f_* 𝒪_Y)` of a quasi-compact,
  quasi-separated `f` is an open immersion, then `f` is quasi-affine.

## References

* [Stacks Project, Tag 03KS](https://stacks.math.columbia.edu/tag/03KS)
* [Stacks Project, Tag 03WL](https://stacks.math.columbia.edu/tag/03WL)
* [Stacks Project, Tag 03WN](https://stacks.math.columbia.edu/tag/03WN)
* [Stacks Project, Tag 081X](https://stacks.math.columbia.edu/tag/081X)
* [Stacks Project, Tag 086S](https://stacks.math.columbia.edu/tag/086S)
* [Stacks Project, Tag 0BCK](https://stacks.math.columbia.edu/tag/0BCK)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Pullbacks of presheaves on the big fppf site over `S` (instance search times out without this
shortcut). -/
private instance (priority := high) hasPullback_presheaf
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

/-! ### Quasi-compact open immersions are quasi-affine -/

/-- A quasi-compact open immersion of algebraic spaces over `S` is quasi-affine. -/
theorem isQuasiAffineHom_of_isOpenImmersion {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (g : F ⟶ G)
    (hoi : IsOpenImmersion B S hS g) (hgqc : IsQuasiCompact B S hS g) :
    IsQuasiAffineHom B S hS g := by
  intro Z k
  obtain ⟨W, snd, fst, hsq⟩ := hoi.1 k
  have hoiW : _root_.AlgebraicGeometry.IsOpenImmersion
      ((BigFppfOver.toScheme B S hS).map snd) := hoi.2 k fst snd hsq
  have e : yoneda.obj W ≅ pullback k g := hsq.isoPullback ≪≫ pullbackSymmetry g k
  have hZaff : IsAffine ((BigFppfOver.toScheme B S hS).obj
    ((BigAffineFppf.inclusion B S hS).obj Z)) := Z.property
  have hWcompact : CompactSpace ((BigFppfOver.toScheme B S hS).obj W) :=
    compactSpace_of_isQuasiCompactSpace_yoneda_obj B S hS <| isQuasiCompactSpace_of_iso B S hS
      e.symm (hgqc _ (isAlgebraicSpace_yoneda B S hS _)
        (isQuasiCompactSpace_yoneda_of_isAffine B S hS _ hZaff) k)
  have hZqa : Scheme.IsQuasiAffine ((BigFppfOver.toScheme B S hS).obj
    ((BigAffineFppf.inclusion B S hS).obj Z)) := inferInstance
  exact ⟨W, Scheme.IsQuasiAffine.of_isImmersion ((BigFppfOver.toScheme B S hS).map snd), ⟨e⟩⟩

/-! ### Open immersion of the canonical factorization -/

variable (E : AffineAlgebraAntiEquivalence B S hS) (C : BaseChangeCompatibility B S hS E)
  {X Y : AlgebraicSpaces B S hS}

/-- If the canonical morphism `Y ⟶ \underline{Spec}_X(f_* 𝒪_Y)` attached to a quasi-compact
morphism `f : Y ⟶ X` of algebraic spaces with quasi-coherent direct-image algebra is an open
immersion, then `f` is quasi-affine. -/
theorem isQuasiAffineHom_of_isOpenImmersion_directImageFactorizationMap (f : Y ⟶ X)
    (hfqc : IsQuasiCompact B S hS f.hom)
    (hqc : (pushforwardAlgebra B S hS (Over.mk f)).IsQuasicoherent)
    (hoi : IsOpenImmersion B S hS
      (directImageFactorizationMap B S hS E C f hqc).left.hom) :
    IsQuasiAffineHom B S hS f.hom := by
  have hfac : (directImageFactorizationMap B S hS E C f hqc).left.hom ≫
      (relativeSpecDirectImage B S hS E f hqc).obj.hom.hom = f.hom := by
    rw [← ObjectProperty.FullSubcategory.comp_hom]
    exact congrArg (fun m : Y ⟶ X ↦ m.hom)
      (directImageFactorizationMap_factorization B S hS E C f hqc)
  have hpaff : IsAffineHom B S hS (relativeSpecDirectImage B S hS E f hqc).obj.hom.hom :=
    isAffineHom_relativeSpecDirectImage B S hS E f hqc
  have hpqs : IsQuasiSeparated B S hS (relativeSpecDirectImage B S hS E f hqc).obj.hom.hom :=
    isQuasiSeparated_of_isSeparated B S hS
      (isSeparated_of_isAffineHom B S hS _
        (relativeSpecDirectImage B S hS E f hqc).obj.left.2 X.2 hpaff)
  have hgqc : IsQuasiCompact B S hS
      (directImageFactorizationMap B S hS E C f hqc).left.hom :=
    isQuasiCompact_of_comp_of_isQuasiSeparated B S hS _ _ Y.2 X.2 (by rwa [hfac]) hpqs
  rw [← hfac]
  exact IsQuasiAffineHom.comp Y.2 (relativeSpecDirectImage B S hS E f hqc).obj.left.2 X.2
    (isQuasiAffineHom_of_isOpenImmersion B S hS _ hoi hgqc)
    (isQuasiAffineHom_of_isAffineHom hpaff)

/-- A quasi-compact, quasi-separated morphism `f : Y ⟶ X` of algebraic spaces over `S` whose
canonical morphism `Y ⟶ \underline{Spec}_X(f_* 𝒪_Y)` is an open immersion is quasi-affine. -/
@[stacks 086S "proves only: the factorization is an open immersion implies f is quasi-affine"]
theorem isQuasiAffineHom_of_isOpenImmersion_qcqsDirectImageFactorizationMap (f : Y ⟶ X)
    (hfqc : IsQuasiCompact B S hS f.hom) (hfqs : IsQuasiSeparated B S hS f.hom)
    (hoi : IsOpenImmersion B S hS
      (qcqsDirectImageFactorizationMap B S hS E C f hfqc hfqs
        fun hqc hqs => isQuasicoherentOnSite_modulePushforward_of_qcqs B S hS f hqc hqs).left.hom) :
    IsQuasiAffineHom B S hS f.hom :=
  isQuasiAffineHom_of_isOpenImmersion_directImageFactorizationMap B S hS E C f hfqc _ hoi

end AlgebraicGeometry.Space

end
