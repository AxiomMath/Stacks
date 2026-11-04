module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineOfUniversallyClosedSurjection
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.IntegralAlgebraFiniteColimitQcqs
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.IntegralLimitFinitePresentationFixedOnOpen

/-!
# An integral morphism to a qcqs algebraic space is a directed limit of finite ones

Stacks 09YA: let `f : X ⟶ Y` be an integral morphism of algebraic spaces over `S`, with `Y`
quasi-compact and quasi-separated.  Then `X` is a directed limit `X = lim X_i` of algebraic
spaces `X_i` finite and of finite presentation over `Y`.

The proof is the source's.  The direct image `𝒜 = f_* 𝒪_X` is an integral quasi-coherent
`𝒪_Y`-algebra; by Stacks 082C it is a directed colimit `𝒜 = colim 𝒜_i` of quasi-coherent
`𝒪_Y`-algebras that are finite and of finite presentation; the stages are the relative spectra
`X_i = \underline{Spec}_Y(𝒜_i)` of Stacks 081W, finite and of finite presentation over `Y`
because the `𝒜_i` are, and `X = lim X_i` because `𝒜 = colim 𝒜_i`.

## Main results

* `AlgebraicGeometry.Space.exists_isColimit_pushforwardAlgebra_of_isIntegralHom`: Stacks 082C
  applied to `f_* 𝒪_X`.
* `AlgebraicGeometry.Space.integralFiniteSystemOfIsIntegralHom`: **Stacks 09YA**, the inverse
  system, as an `AlgebraicGeometry.Space.IntegralFiniteSystem`.

## Implementation notes

The relative spectrum of a stage is the functor of points
`AlgebraicGeometry.Space.relativeSpecPoints` of Stacks 081W, which is an algebraic space finite
and of finite presentation over `Y` for a finite, finitely presented quasi-coherent algebra
(`AlgebraicGeometry.Space.isAlgebraicSpace_isFinite_isFinitePresentation_relativeSpecPointsπ`).
Two facts give `X = lim X_i`: the relative spectrum turns a colimit of algebras over a connected
index into a limit of presheaves
(`AlgebraicGeometry.Space.isLimitMapConeRelativeSpecPointsFunctor`), and an affine `f` identifies
`X` with the relative spectrum of `f_* 𝒪_X` (`AlgebraicGeometry.Space.isIso_toRelativeSpecPoints`).

`AlgebraicGeometry.Space.IntegralFiniteSystem` presents `X` as the limit of a directed inverse
system of presheaves on the big fppf site, indexed by a nonempty directed preorder in the universe
of the schemes, the limit being the objectwise one, that is, the limit of fppf sheaves.

## References

* [Stacks Project, Tag 09YA](https://stacks.math.columbia.edu/tag/09YA)
* [Stacks Project, Tag 082C](https://stacks.math.columbia.edu/tag/082C)
* [Stacks Project, Tag 081W](https://stacks.math.columbia.edu/tag/081W)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **Stacks 082C for `f_* 𝒪_X`.**  For an integral morphism `f : X ⟶ Y` of algebraic spaces with
`Y` quasi-compact and quasi-separated, the direct image `f_* 𝒪_X` is the colimit of a directed
system, over a nonempty directed preorder, of quasi-coherent `𝒪_Y`-algebras that are finite and
of finite presentation.  The direct image is quasi-coherent because `f` is affine, hence
quasi-compact and quasi-separated, and integral because `f` is. -/
theorem exists_isColimit_pushforwardAlgebra_of_isIntegralHom (f : X ⟶ Y)
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hf : IsIntegralHom B S hS f) (hYqc : IsQuasiCompactSpace B S hS Y)
    (hYqs : IsAbsolutelyQuasiSeparated B S hS B.contains_terminal Y) :
    ∃ (I : Type u) (_ : Preorder I) (_ : Nonempty I) (_ : IsDirected I (· ≤ ·))
      (D : I ⥤ AlgebraSheaf.{u, u} B S hS Y hY)
      (t : D ⟶ (Functor.const I).obj (pushforwardAlgebra B S hS
        (Over.mk (ObjectProperty.homMk (P := IsAlgebraicSpace B S hS)
          (X := (⟨X, hX⟩ : AlgebraicSpaces B S hS)) (Y := ⟨Y, hY⟩) f))))
      (_ : IsColimit (Cocone.mk _ t)),
      ∀ i, (D.obj i).IsQuasicoherent ∧ (D.obj i).IsFinite ∧ (D.obj i).IsFinitePresentation := by
  let fa : (⟨X, hX⟩ : AlgebraicSpaces B S hS) ⟶ ⟨Y, hY⟩ := ObjectProperty.homMk f
  have haff : IsAffineHom B S hS f := isAffineHom_of_isIntegralHom f hf
  have hA : (pushforwardAlgebra B S hS (Over.mk fa)).IsQuasicoherent :=
    isQuasicoherent_pushforwardAlgebra B S hS fa
      (isQuasiCompact_of_isAffineHom' B S hS f hX hY haff)
      (isQuasiSeparated_of_isAffineHom B S hS f hX hY haff)
      fun h₁ h₂ F hF => isQuasicoherentOnSite_modulePushforward_of_qcqs B S hS fa h₁ h₂ F hF
  exact (isFiltered_isColimit_finiteSubalgebra_and_exists_directed_finite B S hS
    Y hY hYqc hYqs _ hA (isIntegral_pushforwardAlgebra_of_isIntegralHom B S hS fa hf)).2

/-- **Stacks 09YA.** An integral morphism `f : X ⟶ Y` of algebraic spaces over `S`, with `Y`
quasi-compact and quasi-separated, presents `X` as a directed limit `X = lim X_i` of algebraic
spaces `X_i` finite and of finite presentation over `Y`.

The system is a directed inverse system of algebraic spaces over `Y` indexed by a nonempty
directed preorder, with a cone from `X` compatible with `f` which is a limit cone; every stage is
finite and of finite presentation over `Y`
(`AlgebraicGeometry.Space.IntegralFiniteSystem`).  The stages are the relative spectra
`\underline{Spec}_Y(𝒜_i)` (Stacks 081W) of the finite, finitely presented algebras of
Stacks 082C presenting `f_* 𝒪_X`. -/
@[stacks 09YA]
def integralFiniteSystemOfIsIntegralHom (f : X ⟶ Y) (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (hf : IsIntegralHom B S hS f)
    (hYqc : IsQuasiCompactSpace B S hS Y)
    (hYqs : IsAbsolutelyQuasiSeparated B S hS B.contains_terminal Y) :
    IntegralFiniteSystem B S hS f :=
  Classical.choice <| by
    obtain ⟨I, _, _, _, D, t, ht, hD⟩ :=
      exists_isColimit_pushforwardAlgebra_of_isIntegralHom B S hS f hX hY hf hYqc hYqs
    let Ya : AlgebraicSpaces B S hS := ⟨Y, hY⟩
    let fa : (⟨X, hX⟩ : AlgebraicSpaces B S hS) ⟶ Ya := ObjectProperty.homMk f
    have : IsFiltered I := isFiltered_of_directed_le_nonempty I
    have : IsConnected I := IsFiltered.isConnected I
    have := isIso_toRelativeSpecPoints B S hS (f := fa) (isAffineHom_of_isIntegralHom f hf)
    have hspec : ∀ i : I,
        IsAlgebraicSpace B S hS (relativeSpecPoints B S hS (X := Ya) (D.obj i)) ∧
        IsFinite B S hS (relativeSpecPointsπ B S hS (X := Ya) (D.obj i)) ∧
        IsFinitePresentation B S hS (relativeSpecPointsπ B S hS (X := Ya) (D.obj i)) := fun i =>
      isAlgebraicSpace_isFinite_isFinitePresentation_relativeSpecPointsπ B S hS (X := Ya) (D.obj i)
        (hD i).1 (hD i).2.1 (hD i).2.2
    let c : Cone (D.op ⋙ relativeSpecPointsFunctor B S hS Ya) :=
      toRelativeSpecPointsCone B S hS fa t
    have hc : IsLimit ((relativeSpecPointsFunctor B S hS Ya).mapCone (Cocone.mk _ t).op) :=
      isLimitMapConeRelativeSpecPointsFunctor B S hS ht
    have hlim : IsLimit c := hc.ofIsoLimit
      (Cones.ext (asIso (toRelativeSpecPoints B S hS fa)).symm fun j => by
        change relativeSpecPointsMap B S hS (t.app j.unop) =
          inv (toRelativeSpecPoints B S hS fa) ≫ toRelativeSpecPoints B S hS fa ≫
            relativeSpecPointsMap B S hS (t.app j.unop)
        rw [IsIso.inv_hom_id_assoc])
    have hcomp : ∀ i : Iᵒᵖ,
        f = c.π.app i ≫ (relativeSpecPointsπNatTrans B S hS (Y := Ya) D).app i := by
      intro i
      change f = (toRelativeSpecPoints B S hS fa ≫ relativeSpecPointsMap B S hS (t.app i.unop)) ≫
        relativeSpecPointsπ B S hS (X := Ya) (D.obj i.unop)
      rw [Category.assoc, relativeSpecPointsMap_comp_π, toRelativeSpecPoints_comp_π]
      rfl
    exact ⟨{
      indexType := I
      diagram := D.op ⋙ relativeSpecPointsFunctor B S hS Ya
      structureMap := relativeSpecPointsπNatTrans B S hS (Y := Ya) D
      limitCone := c.π
      compatible := hcomp
      isLimit := hlim
      stageAlgebraicSpace := fun i => (hspec i.unop).1
      stageFinite := fun i => (hspec i.unop).2.1
      stageFinitePresentation := fun i => (hspec i.unop).2.2 }⟩

end AlgebraicGeometry.Space

end
