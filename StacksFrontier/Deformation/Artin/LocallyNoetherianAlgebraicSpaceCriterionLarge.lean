module

public import StacksFrontier.Deformation.Artin.LocallyNoetherianAlgebraicSpaceCriterion

/-!
# Artin's criterion on the locally Noetherian site for functors with large values

`AlgebraicGeometry.LocallyNoetherianOver.existsUnique_isAlgebraicSpace_restriction_iso`
(Stacks 0GE7) is stated for functors `F` on the locally Noetherian site `(Noetherian/S)_étale`
with values in `Type u`, the universe of the schemes. Some functors that occur naturally, such
as Artin's contraction functor of Stacks 0GHA, take values in `Type (u + 1)` while having
`u`-small values. This file proves the existence half of Stacks 0GE7 for those: if `F` has
`u`-small values, a representable diagonal and satisfies Artin's axioms, then there is a limit
preserving algebraic space `X` of `Type u` on the big fppf site whose restriction to the locally
Noetherian site, lifted to `Type (u + 1)`, is `F`.

The proof is that of Stacks 0GE7: extend `F` by Stacks 0GE3, check the diagonal of the extension
by Stacks 0GE5, shrink the extension to `Type u` (its values are `u`-small because those of `F`
are), and apply Stacks 07Y1. Axioms `[3]` and `[5]` pass to the shrunk extension through the
comparison `AlgebraicGeometry.LocallyNoetherianOver.elementsToFibredCategoryULift` of the
category fibred in sets of `F` with its category fibred in groupoids, which is in
`StacksFrontier.Deformation.Artin.LocallyNoetherianAlgebraicSpaceCriterion`.

## Main results

* `AlgebraicGeometry.LocallyNoetherianOver.exists_isAlgebraicSpace_restriction_iso_of_small`.

## References

* [Stacks Project, Tag 0GE7](https://stacks.math.columbia.edu/tag/0GE7)
* [Stacks Project, Tag 07Y1](https://stacks.math.columbia.edu/tag/07Y1)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.LocallyNoetherianOver

open Deformation Deformation.Artin ExtendingFunctors CategoryTheory.Presheaf

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **Stacks 0GE7, existence, for a functor with `u`-small values in `Type (u + 1)`.** Let `S` be
a locally Noetherian scheme and let `F` be a functor on the locally Noetherian étale site
`(Noetherian/S)_étale` with values in `Type (u + 1)` which are `u`-small. If the diagonal of `F`
is representable, `F` satisfies Artin's axioms `[-1]`–`[5]` in the form of Section 0GE6, and the
local rings of `S` at its finite type points are G-rings, then there is a limit preserving
algebraic space `X` of `Type u` on the big fppf site `(Sch/S)_fppf` whose restriction to
`(Noetherian/S)_étale`, lifted to `Type (u + 1)`, is `F`. -/
theorem exists_isAlgebraicSpace_restriction_iso_of_small [IsLocallyNoetherian S]
    (F : (LocallyNoetherianOver B S hS)ᵒᵖ ⥤ Type (u + 1)) (hsmall : ∀ V, Small.{u} (F.obj V))
    (hdiag : (uliftYoneda.{u + 1} (C := LocallyNoetherianOver B S hS)).relativelyRepresentable
      (diag F))
    (hax : SatisfiesArtinAxioms B S hS F)
    (hG : ∀ s : S, IsFiniteTypePoint s → IsGRing (S.presheaf.stalk s)) :
    ∃ X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u, IsAlgebraicSpace B S hS X ∧
      LimitPreserving.{u, u, u, u, u + 1, u} (BigFppfOver.toScheme B S hS) X ∧
      Nonempty ((LocallyNoetherianOver.toBigFppfOver B S hS).op ⋙ X ⋙ uliftFunctor.{u + 1} ≅
        F) := by
  have hFs : ∀ E : Covering (LocallyNoetherianOver B S hS), IsEtaleCovering B S hS E →
      E.2.presieve₀.IsSheafFor F := hax.isSheaf
  have hFl : LimitPreserving.{u, u + 1, u, u, u + 1, u}
      (LocallyNoetherianOver.toScheme B S hS) F := hax.limitPreserving
  -- the extension of `F` to the big fppf site (Stacks 0GE3)
  let F' := extensionToBigFppfOver.{0} B hS F
  have hs' : IsCoveringSheafOnSubcategory.{u + 1, u, u} .zariski (IsContainedOver B (S := S))
      ((ExtendingFunctors.toBigFppfOver B hS).op ⋙ F') :=
    isCoveringSheafOnSubcategory_extensionToBigFppfOver.{0} hFs hFl
  have hl' : LimitPreserving.{u, u + 1, u, u, u + 1, u} (BigFppfOver.toScheme B S hS) F' :=
    limitPreserving_extensionToBigFppfOver.{0} hFs hFl
  have het : Presheaf.IsSheaf ((AlgebraicGeometry.etaleTopology B).over (B.obj hS)) F' :=
    isSheaf_etaleTopology_extensionToBigFppfOver.{0} hFs hFl
  obtain ⟨e'⟩ := nonempty_restriction_extensionToBigFppfOver_iso.{0} hFs hFl
  -- its diagonal is representable (Stacks 0GE5)
  have hdF' : (uliftYoneda.{u + 1} (C := BigFppfOver B S hS)).relativelyRepresentable
      (diag F') :=
    relativelyRepresentable_diag_of_restriction.{0} (B := B) (hS := hS) (hFs := hs') (hFl := hl')
      (hdiag := uliftYoneda_relativelyRepresentable_diag_of_iso e'.symm hdiag)
  -- its values are `u`-small, so it is the lift of a `Type u`-valued functor `G`
  have hsmall' : FunctorToTypes.Small.{u} F' := fun T =>
    small_obj_of_small_restriction.{0} B hS hs' hl' (fun V =>
      small_map (e'.app (op V)).toEquiv) T.unop
  let G := FunctorToTypes.shrink.{u} F'
  let eG : G ⋙ uliftFunctor.{u + 1} ≅ F' :=
    NatIso.ofComponents (fun T => Equiv.toIso (Equiv.ulift.trans (equivShrink _).symm))
      (fun f => by ext x; exact Equiv.symm_apply_apply (equivShrink _) _)
  let e : (LocallyNoetherianOver.toBigFppfOver B S hS).op ⋙ G ⋙ uliftFunctor.{u + 1} ≅ F :=
    Functor.isoWhiskerLeft (LocallyNoetherianOver.toBigFppfOver B S hS).op eG ≪≫ e'
  -- the hypotheses of Stacks 07Y1 for `G`
  have hdiagG : Space.IsRepresentableByAlgebraicSpaces B S hS (diag G) :=
    .of_relativelyRepresentable <| yoneda_relativelyRepresentable_diag_iff.2 fun T a b => by
      obtain ⟨X, snd, h⟩ := uliftYoneda_relativelyRepresentable_diag_iff.1
        (uliftYoneda_relativelyRepresentable_diag_of_iso eG.symm hdF') T ⟨a⟩ ⟨b⟩
      exact ⟨X, snd, (representsEqualizer_comp_uliftFunctor_iff snd a b).1 h⟩
  have hsize : ∃ T₀ : BigFppfOver B S hS, ∀ (U : BigFppfOver B S hS) (k : Type u) [Field k],
      Nonempty ((BigFppfOver.toScheme B S hS).obj U ≅ Spec (.of k)) →
      LocallyOfFiniteType (B.inclusion.map U.hom) →
      Cardinal.mk (G.obj (op U)) ≤ ((BigFppfOver.toScheme B S hS).obj T₀).size := by
    obtain ⟨T₀, hT₀⟩ := hax.sizeBounded
    refine ⟨T₀, fun U k _ ⟨φ⟩ hlft => ?_⟩
    have hN : IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj U) :=
      isLocallyNoetherian_of_isOpenImmersion φ.hom
    let U₀ : LocallyNoetherianOver B S hS := ⟨U, hN⟩
    have h := hT₀ U₀ k ⟨φ⟩ hlft
    have h₂ : Cardinal.mk (F.obj (op U₀)) = Cardinal.lift.{u + 1} (Cardinal.mk (G.obj (op U))) :=
      (Cardinal.mk_congr (e.app (op U₀)).toEquiv).symm.trans (Cardinal.mk_uLift _)
    rwa [h₂, Cardinal.lift_lift, Cardinal.lift_le] at h
  have hF : Presheaf.IsSheaf ((AlgebraicGeometry.etaleTopology B).over (B.obj hS)) G := by
    rw [isSheaf_iff_isSheaf_of_type] at het ⊢
    exact (Presieve.isSheaf_comp_uliftFunctor_iff _).1 (Presieve.isSheaf_iso _ eG.symm het)
  have hlim : LimitPreserving.{u, u, u, u, u + 1, u} (BigFppfOver.toScheme B S hS) G :=
    limitPreserving_of_comp_uliftFunctor (limitPreserving_of_iso eG.symm hl')
  have htangent := fun {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k] [Module.Finite Λ k]
      (iΛ : Spec (.of Λ) ⟶ S) [IsOpenImmersion iΛ]
      (x₀ : (Stack.fibredCategory B S hS G).val.obj)
      (hx₀ : ((Stack.fibredCategory B S hS G).val.p ⋙ Over.post B.inclusion).obj x₀ =
        Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
      (_ : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
      (_ : QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)) =>
    finiteDimensional_tangentSpaceArtinian_fibredCategory e
      hax.finiteDimensionalTangentSpaces iΛ x₀ hx₀
  refine ⟨G, Deformation.Artin.isAlgebraicSpace_of_artinAxioms hdiagG hsize hF hlim
    (satisfiesRSFunctor_of_satisfiesRS_uliftFunctor e hax.satisfiesRS) htangent
    (isEffective_fibredCategory_of_hasEffectiveFormalObjects (Iso.refl _)
      (hasEffectiveFormalObjects_restriction e hax.effective))
    (openVersality_fibredCategory_of_hasOpenVersality e hax.openVersality) hG,
    hlim, ⟨e⟩⟩

end AlgebraicGeometry.LocallyNoetherianOver

end
