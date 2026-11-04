module

public import StacksFrontier.AlgebraicGeometry.Descent.AffineHomFpqcLocal
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ResolutionPropertyQuasiAffine
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactSmallerBase
public import StacksFrontier.AlgebraicGeometry.Spaces.RelocalizeAffineDescent
public import StacksFrontier.AlgebraicGeometry.Stacks.AffineMorphismStability
public import StacksFrontier.AlgebraicGeometry.Stacks.DiagonalStructureMorphismComparison
public import StacksFrontier.AlgebraicGeometry.Stacks.FpqcDescent.QuasiAffineDiagonal
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiCompactDiagonalDecent
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiCompactDiagonalGerbe

/-!
# An affine absolute diagonal is affine, hence quasi-affine, over the base

Let `𝒳` be an algebraic stack over `S`.  Unqualified separation notions are read over `Spec ℤ`
(Stacks 050D): the *absolute* diagonal of `𝒳` is the diagonal of `𝒳` viewed over the terminal
scheme (`AlgebraicGeometry.Stack.AlgebraicStacks.viewOverIntegers`).  This file shows that if the
absolute diagonal is affine, then so is the diagonal `𝒳 ⟶ 𝒳 ×_S 𝒳` over `S`, and in particular
it is quasi-affine, which is the hypothesis of Stacks 0GRH
(`AlgebraicGeometry.Stack.isStack_fpqc_of_isQuasiAffineHom_diagonal`).

The argument is the one of
`AlgebraicGeometry.Stack.isQuasiCompact_relativeDiagonal_structureMorphism_of_changeBase` with
affineness in place of quasi-compactness: the fibres of the relative diagonal of the
structure morphism over `S` are represented by the same algebraic spaces as those over `Spec ℤ`
(`CategoryTheory.TwoFibreProductOver.representedFibre_structure_absolute`), and affineness of the
structural morphism of an algebraic space does not depend on the base it is read over, because
the lower-shriek extension reflects affineness of morphisms of presheaves.

## Main results

* `AlgebraicGeometry.Space.isAffineHom_of_relocalizeMap`: a morphism of presheaves on the big
  fppf site of `W` is affine as soon as its lower-shriek extension is.
* `AlgebraicGeometry.Space.isAffineHom_spacesOverSmallerBaseFunctor_of`: affineness of the
  structural morphism of an algebraic space does not depend on the base.
* `AlgebraicGeometry.Stack.AlgebraicStacks.isAffineHom_diagonal_of_viewOverIntegers`: an affine
  absolute diagonal is affine over `S`.
* `AlgebraicGeometry.Stack.AlgebraicStacks.isQuasiAffineHom_diagonal_of_viewOverIntegers`: an
  affine absolute diagonal is quasi-affine over `S`.

## References

* [Stacks Project, Tag 03WF](https://stacks.math.columbia.edu/tag/03WF)
* [Stacks Project, Tag 050D](https://stacks.math.columbia.edu/tag/050D)
* [Stacks Project, Tag 0GRH](https://stacks.math.columbia.edu/tag/0GRH)
-/

@[expose] public section

open CategoryTheory Opposite CategoryTheory.Limits

universe u w

namespace AlgebraicGeometry

variable (B : BigFppfSite.{u}) (W S : Scheme.{u}) (hW : B.Contains W) (hS : B.Contains S)
  (h : B.obj hW ⟶ B.obj hS)

/-- **A morphism of presheaves on the big fppf site of `W` is affine as soon as its lower-shriek
extension is.**  An affine test object over `W` is carried by the extension to an affine test
object over `S` with the same underlying scheme; the extension preserves fibre products, and a
presheaf whose extension is representable is representable by an object with the same
underlying scheme (`CategoryTheory.OverShriek.exists_iso_yoneda_of_relocalize_iso`). -/
theorem Space.isAffineHom_of_relocalizeMap {X Y : (BigFppfOver B W hW)ᵒᵖ ⥤ Type u}
    (k : X ⟶ Y)
    (hk : Space.IsAffineHom B S hS ((OverShriek.relocalizePresheafFunctor h).map k)) :
    Space.IsAffineHom B W hW k := by
  have : PreservesLimitsOfShape WalkingCospan (OverShriek.relocalizePresheafFunctor h) :=
    relocalizePresheaf_preservesConnectedLimits h
  intro Z γ
  let Λ := OverShriek.relocalizePresheafFunctor h
  let i := (OverShriek.relocalizeYonedaIso h).app ((BigAffineFppf.inclusion B W hW).obj Z)
  obtain ⟨W', p', q', hpb⟩ :=
    hk ⟨(Over.map h).obj ((BigAffineFppf.inclusion B W hW).obj Z), Z.property⟩
      (i.inv ≫ Λ.map γ)
  let c : pullback (Λ.map k) (i.inv ≫ Λ.map γ) ⟶ pullback (Λ.map k) (Λ.map γ) :=
    pullback.map _ _ _ _ (𝟙 _) i.inv (𝟙 _) (by simp) (by simp)
  let E : Λ.obj (pullback k γ) ≅ yoneda.obj ((BigAffineFppf.inclusion B S hS).obj W') :=
    PreservesPullback.iso Λ k γ ≪≫ (hpb.isoPullback ≪≫ asIso c).symm
  obtain ⟨T, hT, ⟨eT⟩⟩ := OverShriek.exists_iso_yoneda_of_relocalize_iso h E
  have hTa : IsAffine ((BigFppfOver.toScheme B W hW).obj T) := by
    show IsAffine (B.inclusion.obj T.left)
    rw [hT]
    exact W'.property
  refine ⟨⟨T, hTa⟩, eT.inv ≫ pullback.fst k γ,
    yoneda.preimage (eT.inv ≫ pullback.snd k γ), ?_⟩
  rw [yoneda.map_preimage]
  exact IsPullback.of_iso_pullback ⟨by simp [pullback.condition]⟩ eT.symm (by simp) (by simp)

variable (S' : Scheme.{u}) (hS' : B.Contains S') (g : B.obj hS ⟶ B.obj hS')

/-- **Affineness of the structural morphism of a lower-shriek extension does not depend on the
base.**  The structural morphism over `S'` is the image under `Λ_g` of the one over `S`, up to
isomorphisms (`CategoryTheory.OverShriek.relocalizeToYoneda_comp_relocalizeYonedaComp`). -/
theorem Space.isAffineHom_relocalizeToYoneda_comp_of
    (F : (BigFppfOver B W hW)ᵒᵖ ⥤ Type u)
    (hF : Space.IsAffineHom B S' hS' (OverShriek.relocalizeToYoneda (h ≫ g) F)) :
    Space.IsAffineHom B S hS (OverShriek.relocalizeToYoneda h F) := by
  refine Space.isAffineHom_of_relocalizeMap B S S' hS hS' g _ ?_
  have h1 := Space.isAffineHom_comp_iso (OverShriek.relocalizeYonedaComp h g).hom hF
  rw [OverShriek.relocalizeToYoneda_comp_relocalizeYonedaComp h g F] at h1
  simpa using Space.isAffineHom_iso_comp (OverShriek.relocalizeCompIso h g F).hom h1

/-- **Stacks 03WF for the image of Stacks 04SG's forward functor does not depend on the base.**
An algebraic space over `W`, viewed over `S` along `h` and over `S'` along a factorization
`h ≫ g`, has affine structural morphism over `S` as soon as it has one over `S'`. -/
theorem Space.isAffineHom_spacesOverSmallerBaseFunctor_of
    (u : B.obj hW ⟶ B.obj hS') (hu : h ≫ g = u)
    (F : (BigFppfOver B W hW)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B W hW F)
    (haff : Space.IsAffineHom B S' hS'
      (((spacesOverSmallerBaseFunctor B W S' hW hS' u).obj ⟨F, hF⟩).1.hom)) :
    Space.IsAffineHom B S hS
      (((spacesOverSmallerBaseFunctor B W S hW hS h).obj ⟨F, hF⟩).1.hom) := by
  subst hu
  have h₁ := Space.isAffineHom_iso_comp
    ((spacesOverSmallerBaseFunctorForgetIso B W S' hW hS' (h ≫ g)).inv.app ⟨F, hF⟩) haff
  rw [Space.relocalizeToYoneda_eq B W S' hW hS' (h ≫ g) ⟨F, hF⟩] at h₁
  have h₂ := Space.isAffineHom_relocalizeToYoneda_comp_of B W S hW hS h S' hS' g F h₁
  rw [← Space.relocalizeToYoneda_eq B W S hW hS h ⟨F, hF⟩] at h₂
  simpa using Space.isAffineHom_iso_comp
    ((spacesOverSmallerBaseFunctorForgetIso B W S hW hS h).hom.app ⟨F, hF⟩) h₂

end AlgebraicGeometry

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Affineness of the relative diagonal of a structure morphism descends along a change of
base.**  If the relative diagonal of the structure morphism of Construction A of `𝒳` along
`g : S ⟶ S'` is affine in the sense of Stacks 04XB, then so is the relative diagonal of the
structure morphism of `𝒳`: the fibres of the two are represented by the same algebraic spaces
(`CategoryTheory.TwoFibreProductOver.representedFibre_structure_absolute`). -/
theorem isAffineHom_relativeDiagonal_structureMorphism_of_changeBase
    (S' : Scheme.{u}) (hS' : B.Contains S') (g : B.obj hS ⟶ B.obj hS')
    (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (h𝒳 : IsAffineHom B S' hS'
      (relativeDiagonalAlgebraicStacks B S' hS'
        (structureMorphism B S' hS'
          (changeBaseAlgebraicStack B S S' hS hS' g 𝒳))).hom) :
    IsAffineHom B S hS
      (relativeDiagonalAlgebraicStacks B S hS (structureMorphism B S hS 𝒳)).hom := by
  rintro U y hy F hF ⟨e⟩
  obtain ⟨y', hy', he'⟩ := TwoFibreProductOver.representedFibre_structure_absolute
    𝒳.val.val.p g U
    (structureMorphism B S hS 𝒳).hom.hom.w
    (structureMorphism B S' hS' (changeBaseAlgebraicStack B S S' hS hS' g 𝒳)).hom.hom.w
    y hy (presheafOfCategories (F ⋙ typeToCat)).p e
  exact Space.isAffineHom_spacesOverSmallerBaseFunctor_of B U.left.1 S U.left.2 hS
    U.hom S' hS' g _ rfl F hF (h𝒳 (Over.mk (U.hom ≫ g)) y' hy' F hF he')

namespace AlgebraicStacks

/-- **An affine absolute diagonal is affine over the base.**  If the diagonal of `𝒳` viewed over
`Spec ℤ` (the absolute diagonal of Stacks 050D) is affine, then the diagonal
`𝒳 ⟶ 𝒳 ×_S 𝒳` is affine. -/
theorem isAffineHom_diagonal_of_viewOverIntegers (hZ : B.Contains (⊤_ Scheme.{u}))
    (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (hΔ : IsAffineHom B (⊤_ Scheme.{u}) hZ
      (AlgebraicStacks.diagonal B (⊤_ Scheme.{u}) hZ (viewOverIntegers B S hS hZ 𝒳))) :
    IsAffineHom B S hS (AlgebraicStacks.diagonal B S hS 𝒳) := by
  obtain ⟨_, _, hrep, _⟩ := 𝒳.property
  refine ⟨hrep, ?_⟩
  have hrel := (relativeProperty_diagonal_iff_relativeDiagonal_structureMorphism.{u, w}
    B (⊤_ Scheme.{u}) hZ (viewOverIntegers B S hS hZ 𝒳)
    (Space.affineMorphismProperty B (⊤_ Scheme.{u}) hZ)).1 hΔ.2
  exact (relativeProperty_diagonal_iff_relativeDiagonal_structureMorphism.{u, w} B S hS 𝒳
    (Space.affineMorphismProperty B S hS)).2
    (isAffineHom_relativeDiagonal_structureMorphism_of_changeBase B S hS (⊤_ Scheme.{u}) hZ
      (⟨terminal.from S⟩ : B.obj hS ⟶ B.obj hZ) 𝒳 hrel)

/-- **An affine absolute diagonal is quasi-affine over the base.**  This is the hypothesis of
Stacks 0GRH (`AlgebraicGeometry.Stack.isStack_fpqc_of_isQuasiAffineHom_diagonal`) for an
algebraic stack whose absolute diagonal is affine. -/
theorem isQuasiAffineHom_diagonal_of_viewOverIntegers (hZ : B.Contains (⊤_ Scheme.{u}))
    (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (hΔ : IsAffineHom B (⊤_ Scheme.{u}) hZ
      (AlgebraicStacks.diagonal B (⊤_ Scheme.{u}) hZ (viewOverIntegers B S hS hZ 𝒳))) :
    Stack.IsQuasiAffineHom B S hS (Stack.diagonal.{u, u, u} B S hS 𝒳.val) := by
  obtain ⟨-, haff⟩ := isAffineHom_diagonal_of_viewOverIntegers B S hS hZ 𝒳 hΔ
  exact fun U y hy F hF he ↦ Space.isQuasiAffineHom_of_isAffineHom (haff U y hy F hF he)

end AlgebraicStacks

end AlgebraicGeometry.Stack
