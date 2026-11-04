module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralMorphismDirectedLimit
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.QuasicoherentAlgebraFinitePresentationColimitQcqs
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeSpecFinite

/-!
# An affine morphism to a qcqs algebraic space is a directed limit of finitely presented ones

Let `f : X ⟶ Y` be an affine morphism of algebraic spaces over `S`, with `Y` quasi-compact and
quasi-separated. Then `X` is a directed limit `X = lim X_i` of algebraic spaces `X_i` affine and
of finite presentation over `Y` (Stacks 0870). The stages are the relative spectra
`X_i = \underline{Spec}_Y(𝒜_i)` (Stacks 081W) of a presentation `f_* 𝒪_X = colim 𝒜_i` as a
directed colimit of quasi-coherent `𝒪_Y`-algebras of finite presentation (Stacks 082A).

## Main results

* `AlgebraicGeometry.Space.exists_directed_limit_isFinitePresentation_of_isAffineHom`: an affine
  morphism `X ⟶ Y` to a quasi-compact and quasi-separated algebraic space exhibits `X` as a
  directed limit of algebraic spaces affine and of finite presentation over `Y`.

## References

* [Stacks Project, Tag 0870](https://stacks.math.columbia.edu/tag/0870)
* [Stacks Project, Tag 082A](https://stacks.math.columbia.edu/tag/082A)
* [Stacks Project, Tag 081W](https://stacks.math.columbia.edu/tag/081W)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 0870.** Let `S` be a scheme and let `f : X ⟶ Y` be an affine morphism of algebraic
spaces over `S`.  If `Y` is quasi-compact and quasi-separated, then `X` is a directed limit
`X = lim X_i` of algebraic spaces `X_i` affine over `Y` and of finite presentation over `Y`.

The system is indexed by the opposite of a nonempty directed preorder, so it is an inverse
system; `t` is the family of structure morphisms `X_i ⟶ Y`, which are affine and of finite
presentation, `p` is the family of projections `X ⟶ X_i`, each of which composes with the
structure morphism to `f`, and `X` is the limit of the underlying presheaves, that is, of the
fppf sheaves. -/
@[stacks 0870 "the whole statement, under the source's hypotheses only: a directed inverse \
system of algebraic spaces affine and of finite presentation over Y, with X its limit and the \
projections compatible with f"]
theorem exists_directed_limit_isFinitePresentation_of_isAffineHom
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Y)
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hf : IsAffineHom B S hS f)
    (hYqc : IsQuasiCompactSpace B S hS Y)
    (hYqs : IsAbsolutelyQuasiSeparated B S hS B.contains_terminal Y) :
    ∃ (I : Type u) (_ : Preorder I) (_ : Nonempty I) (_ : IsDirected I (· ≤ ·))
      (D : Iᵒᵖ ⥤ ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u))
      (t : D ⟶ (Functor.const Iᵒᵖ).obj Y) (p : (Functor.const Iᵒᵖ).obj X ⟶ D)
      (_ : IsLimit (Cone.mk X p)),
      (∀ i, IsAlgebraicSpace B S hS (D.obj i)) ∧
        (∀ i, IsAffineHom B S hS (t.app i)) ∧
          (∀ i, IsFinitePresentation B S hS (t.app i)) ∧
            ∀ i, p.app i ≫ t.app i = f := by
  let Ya : AlgebraicSpaces B S hS := ⟨Y, hY⟩
  let fa : (⟨X, hX⟩ : AlgebraicSpaces B S hS) ⟶ Ya := ObjectProperty.homMk f
  have hfqc : IsQuasiCompact B S hS f := isQuasiCompact_of_isAffineHom' B S hS f hX hY hf
  have hfqs : IsQuasiSeparated B S hS f := isQuasiSeparated_of_isAffineHom B S hS f hX hY hf
  have hA : (pushforwardAlgebra B S hS (Over.mk fa)).IsQuasicoherent :=
    isQuasicoherent_pushforwardAlgebra B S hS fa hfqc hfqs
      fun h₁ h₂ F hF => isQuasicoherentOnSite_modulePushforward_of_qcqs B S hS fa h₁ h₂ F hF
  obtain ⟨I, hI, hne, hdir, D, t, ht, hD⟩ :=
    exists_directed_isFinitePresentation_algebra_of_isQuasiCompactSpace Ya hYqc hYqs _ hA
  let _ := hI
  have : IsFiltered I := isFiltered_of_directed_le_nonempty I
  have : IsConnected I := IsFiltered.isConnected I
  have := isIso_toRelativeSpecPoints B S hS (f := fa) hf
  let P : I → AffineOver B S hS Ya := fun i =>
    finiteTypeRelativeSpec B S hS ⟨D.obj i, (hD i).1⟩ (hD i).2.isFiniteType
  let c : Cone (D.op ⋙ relativeSpecPointsFunctor B S hS Ya) :=
    toRelativeSpecPointsCone B S hS fa t
  have hc : IsLimit ((relativeSpecPointsFunctor B S hS Ya).mapCone (Cocone.mk _ t).op) :=
    isLimitMapConeRelativeSpecPointsFunctor B S hS ht
  have hlim : IsLimit c := hc.ofIsoLimit
    (Cone.ext (asIso (toRelativeSpecPoints B S hS fa)).symm fun j => by
      change relativeSpecPointsMap B S hS (t.app j.unop) =
        inv (toRelativeSpecPoints B S hS fa) ≫ toRelativeSpecPoints B S hS fa ≫
          relativeSpecPointsMap B S hS (t.app j.unop)
      rw [IsIso.inv_hom_id_assoc])
  refine ⟨I, inferInstance, hne, hdir, D.op ⋙ relativeSpecPointsFunctor B S hS Ya,
    relativeSpecPointsπNatTrans B S hS (Y := Ya) D, c.π, hlim,
    fun i => (P i.unop).obj.left.property, fun i => (P i.unop).property,
    fun i => ?_, fun i => ?_⟩
  · exact isFinitePresentation_finiteTypeRelativeSpec B S hS
      (⟨D.obj i.unop, (hD i.unop).1⟩ : QuasicoherentAlgebra B S hS Ya) (hD i.unop).2
  · change (toRelativeSpecPoints B S hS fa ≫ relativeSpecPointsMap B S hS (t.app i.unop)) ≫
      relativeSpecPointsπ B S hS (X := Ya) (D.obj i.unop) = f
    rw [Category.assoc, relativeSpecPointsMap_comp_π, toRelativeSpecPoints_comp_π]
    rfl

end AlgebraicGeometry.Space

end
