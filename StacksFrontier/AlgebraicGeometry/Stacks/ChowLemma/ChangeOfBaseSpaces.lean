module

public import StacksFrontier.AlgebraicGeometry.Spaces.AdmissibleBlowupSmallerBase
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperSmallerBase
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallerBaseEquivalence
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallerBaseSpacesEtale
public import StacksFrontier.AlgebraicGeometry.Spaces.ZariskiLocallyQuasiSeparated
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocusChangeOfBase
public import StacksFrontier.CategoryTheory.Sites.Localization.RelocalizeComposite

/-!
# Change of base for algebraic spaces, in the shape the proof of Stacks 0CQ8 uses

Let `g : S ⟶ S'` be a morphism of a big fppf site and `Λ_g` the lower-shriek extension of
Stacks 03I5 part (2). This file records what the change of base `S ⟶ S'` of the conclusion and of
the hypotheses of Stacks 0CQ8 needs at the level of algebraic spaces.

## Main results

* `AlgebraicGeometry.Space.isAbsolutelyQuasiSeparated_relocalize`: absolute quasi-separatedness
  (Stacks 03BS, part (3)) is carried by `Λ_g`.
* `AlgebraicGeometry.Space.smallerBaseDescent` and
  `AlgebraicGeometry.Space.smallerBaseDescentIso`: an algebraic space over `S'` with a morphism to
  `h_{S/S'}` is the lower-shriek extension of an algebraic space over `S` (Stacks 04SG), over
  `h_{S/S'}`.
* `AlgebraicGeometry.Space.exists_descent_isOpenImmersion_isProper`: an open immersion followed
  by a proper morphism to `Λ_g Y` descends to an open immersion followed by a proper morphism to
  `Y`.

## Implementation notes

The descent uses the presheaf-level equivalence `AlgebraicGeometry.smallerBasePresheafEquivalence`
of Stacks 04SG and its identification `AlgebraicGeometry.smallerBasePresheafForgetIso` with
`Λ_g`; properness and being an open immersion are reflected by `Λ_g` by
`AlgebraicGeometry.Space.isProper_relocalize_iff` and
`AlgebraicGeometry.presheaf_relocalizeMap_of`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S S' : Scheme.{u}) (hS : B.Contains S) (hS' : B.Contains S')
  (g : B.obj hS ⟶ B.obj hS')

/-- **Absolute quasi-separatedness (Stacks 03BS, part (3)) is carried by the lower-shriek
extension.** Viewing `Λ_g F` over `Spec(ℤ)` is viewing `F` over `Spec(ℤ)` (the two terminal
morphisms agree), up to the isomorphism `CategoryTheory.OverShriek.relocalizeCompIso`. -/
theorem isAbsolutelyQuasiSeparated_relocalize (hZ : B.Contains (⊤_ Scheme.{u}))
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAbsolutelyQuasiSeparated B S hS hZ F) :
    IsAbsolutelyQuasiSeparated B S' hS' hZ ((OverShriek.relocalizePresheafFunctor g).obj F) := by
  have hcomp : g ≫ (⟨terminal.from S'⟩ : B.obj hS' ⟶ B.obj hZ) = ⟨terminal.from S⟩ := by
    ext1
    exact terminal.hom_ext _ _
  have e := OverShriek.relocalizeCompIso g (⟨terminal.from S'⟩ : B.obj hS' ⟶ B.obj hZ) F
  rw [hcomp] at e
  exact isQuasiSeparatedOver_of_iso B (⊤_ Scheme.{u}) hZ e.symm hF

/-! ### Descent of algebraic spaces over `S'` which map to `S` (Stacks 04SG) -/

section Descent

/-- The equivalence of Stacks 04SG at the level of presheaves, abbreviated. -/
local notation "E₀" => smallerBasePresheafEquivalence B S S' hS hS' g

/-- **Descent of an algebraic space over `S'` with a morphism to `S` (Stacks 04SG).** The
presheaf on the big fppf site of `S` which the quasi-inverse of Stacks 04SG attaches to a presheaf
`X` on the big fppf site of `S'` together with a morphism `π : X ⟶ h_{S/S'}`. -/
noncomputable abbrev smallerBaseDescent {X : (BigFppfOver B S' hS')ᵒᵖ ⥤ Type u}
    (π : X ⟶ yoneda.obj (Over.mk g)) : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u :=
  (E₀).inverse.obj (Over.mk π)

/-- The descended presheaf of an algebraic space is an algebraic space. -/
theorem isAlgebraicSpace_smallerBaseDescent {X : (BigFppfOver B S' hS')ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S' hS' X) (π : X ⟶ yoneda.obj (Over.mk g)) :
    IsAlgebraicSpace B S hS (smallerBaseDescent B S S' hS hS' g π) :=
  isAlgebraicSpace_smallerBasePresheafEquivalence_inverse B S S' hS hS' g (Over.mk π) hX

/-- **The lower-shriek extension of the descended presheaf is the presheaf one started from.** -/
noncomputable def smallerBaseDescentIso {X : (BigFppfOver B S' hS')ᵒᵖ ⥤ Type u}
    (π : X ⟶ yoneda.obj (Over.mk g)) :
    (OverShriek.relocalizePresheafFunctor g).obj (smallerBaseDescent B S S' hS hS' g π) ≅ X :=
  ((smallerBasePresheafForgetIso B S S' hS hS' g).app _).symm ≪≫
    (Over.forget _).mapIso ((E₀).counitIso.app (Over.mk π))

/-- The identification `AlgebraicGeometry.Space.smallerBaseDescentIso` is one over `h_{S/S'}`:
it carries the structural morphism of the lower-shriek extension to `π`. -/
@[reassoc]
theorem smallerBaseDescentIso_hom_comp {X : (BigFppfOver B S' hS')ᵒᵖ ⥤ Type u}
    (π : X ⟶ yoneda.obj (Over.mk g)) :
    (smallerBaseDescentIso B S S' hS hS' g π).hom ≫ π =
      OverShriek.relocalizeToYoneda g (smallerBaseDescent B S S' hS hS' g π) := by
  -- `AlgebraicGeometry.Space.smallerBasePresheafForgetIso_inv_app_comp_hom` states this for
  -- `CategoryTheory.OverShriek.viewStructureMap`, which is the same morphism.
  have hforget : (smallerBasePresheafForgetIso B S S' hS hS' g).inv.app
        (smallerBaseDescent B S S' hS hS' g π) ≫
        ((E₀).functor.obj (smallerBaseDescent B S S' hS hS' g π)).hom =
      OverShriek.relocalizeToYoneda g (smallerBaseDescent B S S' hS hS' g π) :=
    smallerBasePresheafForgetIso_inv_app_comp_hom B hS hS' g _
  rw [← hforget]
  simp only [smallerBaseDescentIso, Iso.trans_hom, Iso.symm_hom, Iso.app_inv,
    Functor.mapIso_hom, Over.forget_map, Category.assoc]
  congr 1
  exact Over.w ((E₀).counitIso.app (Over.mk π)).hom

/-- **Being an open immersion is inherited from the lower-shriek extension.** -/
theorem isOpenImmersion_of_relocalizeMap {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (k : X ⟶ Y)
    (hk : IsOpenImmersion B S' hS' ((OverShriek.relocalizePresheafFunctor g).map k)) :
    IsOpenImmersion B S hS k :=
  presheaf_relocalizeMap_of B S S' hS hS' g
    (@AlgebraicGeometry.IsOpenImmersion.{u} : MorphismProperty Scheme.{u}) k hk

/-- **Descent of the compactified cover of Stacks 0CQ8 at the level of algebraic spaces.** Let
`Y` be an algebraic space over `S`, and let `i : X ⟶ X̄` be an open immersion and `ḡ : X̄ ⟶ Λ_g Y`
a proper morphism of algebraic spaces over `S'`. Then `X̄`, and with it `X`, map to `h_{S/S'}`
through the structural morphism of `Λ_g Y`, so by Stacks 04SG they descend to algebraic spaces
`X₀`, `X̄₀` over `S`; `i` and `ḡ` descend to an open immersion `i₀ : X₀ ⟶ X̄₀` and a proper
morphism `ḡ₀ : X̄₀ ⟶ Y`, and the extension of `i₀ ≫ ḡ₀` is `i ≫ ḡ` read through the
identification `θ : Λ_g X₀ ≅ X`. -/
theorem exists_descent_isOpenImmersion_isProper {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hY : IsAlgebraicSpace B S hS Y) {X Xbar : (BigFppfOver B S' hS')ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S' hS' X) (hXbar : IsAlgebraicSpace B S' hS' Xbar)
    (i : X ⟶ Xbar) (gbar : Xbar ⟶ (OverShriek.relocalizePresheafFunctor g).obj Y)
    (hi : IsOpenImmersion B S' hS' i) (hg : IsProper B S' hS' gbar) :
    ∃ (X₀ Xbar₀ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (_ : IsAlgebraicSpace B S hS X₀)
      (_ : IsAlgebraicSpace B S hS Xbar₀)
      (θ : (OverShriek.relocalizePresheafFunctor g).obj X₀ ≅ X) (i₀ : X₀ ⟶ Xbar₀)
      (g₀ : Xbar₀ ⟶ Y),
      IsOpenImmersion B S hS i₀ ∧ IsProper B S hS g₀ ∧
        (OverShriek.relocalizePresheafFunctor g).map (i₀ ≫ g₀) = θ.hom ≫ i ≫ gbar := by
  let πbar := gbar ≫ OverShriek.relocalizeToYoneda g Y
  let π := i ≫ πbar
  have hXbar₀ := isAlgebraicSpace_smallerBaseDescent B S S' hS hS' g hXbar πbar
  let θbar := smallerBaseDescentIso B S S' hS hS' g πbar
  let θ := smallerBaseDescentIso B S S' hS hS' g π
  obtain ⟨g₀, hg₀⟩ := exists_relocalizePresheafFunctor_map_eq
    (θbar.hom ≫ gbar) (by
      rw [Category.assoc]
      exact smallerBaseDescentIso_hom_comp B S S' hS hS' g πbar)
  obtain ⟨i₀, hi₀⟩ := exists_relocalizePresheafFunctor_map_eq
    (θ.hom ≫ i ≫ θbar.inv) (by
      rw [Category.assoc, Category.assoc, ← smallerBaseDescentIso_hom_comp B S S' hS hS' g πbar,
        Iso.inv_hom_id_assoc]
      exact smallerBaseDescentIso_hom_comp B S S' hS hS' g π)
  refine ⟨_, _, isAlgebraicSpace_smallerBaseDescent B S S' hS hS' g hX π, hXbar₀, θ, i₀, g₀,
    ?_, ?_, ?_⟩
  · refine isOpenImmersion_of_relocalizeMap B S S' hS hS' g i₀ ?_
    rw [hi₀]
    exact (isOpenImmersion_respectsIso B S' hS').precomp _ _ _
      ((isOpenImmersion_respectsIso B S' hS').postcomp _ _ _ hi)
  · refine (isProper_relocalize_iff B S hS S' hS' g hXbar₀ hY g₀).1 ?_
    rw [hg₀]
    exact (isProper_isIso_comp_iff B S' hS' θbar.hom gbar).2 hg
  · rw [Functor.map_comp, hi₀, hg₀]
    simp

end Descent

end AlgebraicGeometry.Space
