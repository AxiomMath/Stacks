module

public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionSmallerBase
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperSmallerBase
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallerBaseEquivalence
public import StacksFrontier.AlgebraicGeometry.Spaces.NagataCompactification.HasCompactification

/-!
# Compactifications and change of the base scheme

Let `g : S ⟶ S'` be a morphism of a big fppf site and let `f : X ⟶ Y` be a morphism of algebraic
spaces over `S`. Viewing `f` over `S'` along the lower-shriek extension of Stacks 03I5 part (2),
`X` has a compactification over `Y` as a space over `S` exactly when it has one as a space over
`S'`. For `S' = Spec ℤ` this is the step "we may replace `S` by `Spec ℤ`" with which the source
begins the proof of Nagata's theorem, by Spaces, Section 03I3 and Properties of Spaces,
Definition 03BS.

A compactification over `S` is carried to one over `S'` because the extension preserves
algebraic spaces, open immersions, quasi-compact morphisms and proper morphisms. Conversely, a
compactification `X ⟶ X̄' ⟶ Y` over `S'` lies over the representable presheaf of `S`, through
the structure morphism of the extension of `Y`; by Stacks 04SG
(`AlgebraicGeometry.smallerBasePresheafEquivalence`) it is the extension of a factorization of
`f` over `S`, whose two morphisms have the same properties since the extension reflects them.

## Main results

* `AlgebraicGeometry.Space.isOpenImmersion_relocalize_iff`: being an open immersion is unchanged
  by the extension.
* `AlgebraicGeometry.Space.hasCompactification_relocalize_iff`: `f` has a compactification over
  `S` exactly when its extension has one over `S'`.

## References

* [Stacks Project, Section 03I3](https://stacks.math.columbia.edu/tag/03I3)
* [Stacks Project, Tag 03I5](https://stacks.math.columbia.edu/tag/03I5)
* [Stacks Project, Tag 04SG](https://stacks.math.columbia.edu/tag/04SG)
* [Stacks Project, Tag 0F4D](https://stacks.math.columbia.edu/tag/0F4D)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S S' : Scheme.{u}} {hS : B.Contains S} {hS' : B.Contains S'}

/-- **Being an open immersion is unchanged by the lower-shriek extension** along a morphism
`g : S ⟶ S'` of the site, being a property tested on representable base changes. -/
theorem isOpenImmersion_relocalize_iff (g : B.obj hS ⟶ B.obj hS')
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Y) :
    IsOpenImmersion B S' hS' ((OverShriek.relocalizePresheafFunctor g).map f) ↔
      IsOpenImmersion B S hS f :=
  ⟨presheaf_relocalizeMap_of B S S' hS hS' g _ f, presheaf_relocalizeMap B S S' hS hS' g _ f⟩

/-- **Compactifiability is unchanged by the lower-shriek extension.** Let `g : S ⟶ S'` be a
morphism of the site and `f : X ⟶ Y` a morphism of presheaves on the big fppf site of `S`, with
`Y` an algebraic space. Then `f` has a compactification over `S` if and only if its extension
along `g` has one over `S'`.

For `g` the structure morphism of `S` to the terminal scheme `Spec ℤ` this says that `X` has a
compactification over `Y` exactly when it has one after viewing `X` and `Y` as algebraic spaces
over `Spec ℤ`. -/
theorem hasCompactification_relocalize_iff (g : B.obj hS ⟶ B.obj hS')
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) :
    HasCompactification B S' hS' ((OverShriek.relocalizePresheafFunctor g).map f) ↔
      HasCompactification B S hS f := by
  set Φ := OverShriek.relocalizePresheafFunctor g
  constructor
  · rintro ⟨X'', j', p', hX'', hj', hj'qc, hp', hjp'⟩
    have _ := relocalizePresheaf_faithful g
    let E := smallerBasePresheafEquivalence B S S' hS hS' g
    let ψ := smallerBasePresheafForgetIso B S S' hS hS' g
    -- the compactification, as a presheaf over the representable presheaf of `S`
    let Xo : Over (yoneda.obj (Over.mk g)) := Over.mk (p' ≫ ψ.inv.app Y ≫ (E.functor.obj Y).hom)
    let Xb := E.inverse.obj Xo
    let φp : Xo ⟶ E.functor.obj Y := Over.homMk (p' ≫ ψ.inv.app Y)
    have hfψ : ψ.hom.app X ≫ Φ.map f = (E.functor.map f).left ≫ ψ.hom.app Y :=
      (ψ.hom.naturality f).symm
    let φj : E.functor.obj X ⟶ Xo := Over.homMk (ψ.hom.app X ≫ j') (by
      show (ψ.hom.app X ≫ j') ≫ p' ≫ ψ.inv.app Y ≫ (E.functor.obj Y).hom = _
      simp only [Category.assoc]
      rw [reassoc_of% hjp', reassoc_of% hfψ, Iso.hom_inv_id_app_assoc]
      exact Over.w (E.functor.map f))
    let p : Xb ⟶ Y := E.inverse.map φp ≫ E.unitIso.inv.app Y
    let j : X ⟶ Xb := E.unitIso.hom.app X ≫ E.inverse.map φj
    have hFp : E.functor.map p = E.counitIso.hom.app Xo ≫ φp := by
      simp [p]
    have hFj : E.functor.map j = φj ≫ E.counitIso.inv.app Xo := by
      simp [j]
    -- the extension of `Xb` is `X''`
    let eX : Φ.obj Xb ≅ X'' := (ψ.app Xb).symm ≪≫ (Over.forget _).mapIso (E.counitIso.app Xo)
    have key : ∀ {A B : _} (m : A ⟶ B) (u : Φ.obj A ⟶ Φ.obj B),
        (E.functor.map m).left ≫ ψ.hom.app B = ψ.hom.app A ≫ u → Φ.map m = u := fun m u h => by
      rw [← cancel_epi (ψ.hom.app _), ← ψ.hom.naturality m]
      exact h
    have hj : Φ.map j = j' ≫ eX.inv := key j _ (by rw [hFj]; simp [eX, φj])
    have hp : Φ.map p = eX.hom ≫ p' := by
      refine key p _ ?_
      rw [hFp]
      simp only [eX, φp, Over.comp_left, Over.homMk_left, Iso.trans_hom, Iso.symm_hom,
        Functor.mapIso_hom, Over.forget_map, Iso.app_hom, Iso.app_inv, Category.assoc,
        Iso.inv_hom_id_app]
      exact congrArg (fun t => _ ≫ t) (Category.comp_id p')
    have hXb : IsAlgebraicSpace B S hS Xb :=
      (isAlgebraicSpace_viewOver_iff B S S' hS hS' g Xb).1
        (isAlgebraicSpace_of_iso B S' hS' eX.symm hX'')
    refine ⟨Xb, j, p, hXb, ?_, ?_, ?_, ?_⟩
    · refine (isOpenImmersion_relocalize_iff g j).1 ?_
      rw [hj]
      exact (MorphismProperty.cancel_right_of_respectsIso _ _ _).2 hj'
    · refine (isQuasiCompact_relocalize_iff B S hS S' hS' g j).1 ?_
      rw [hj]
      exact (isQuasiCompact_comp_isIso_iff B S' hS' j' eX.inv).2 hj'qc
    · refine (isProper_relocalize_iff B S hS S' hS' g hXb hY p).1 ?_
      rw [hp]
      exact (isProper_isIso_comp_iff B S' hS' eX.hom p').2 hp'
    · apply Φ.map_injective
      rw [Φ.map_comp, hj, hp, Category.assoc, Iso.inv_hom_id_assoc, hjp']
  · rintro ⟨X'', j, p, hX'', hj, hjqc, hp, rfl⟩
    refine ⟨Φ.obj X'', Φ.map j, Φ.map p, isAlgebraicSpace_viewOver B S S' hS hS' g X'' hX'',
      (isOpenImmersion_relocalize_iff g j).2 hj,
      (isQuasiCompact_relocalize_iff B S hS S' hS' g j).2 hjqc,
      (isProper_relocalize_iff B S hS S' hS' g hX'' hY p).2 hp, (Φ.map_comp j p).symm⟩

end AlgebraicGeometry.Space

end
