module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupoidSchemeRealization
public import StacksFrontier.AlgebraicGeometry.Spaces.SitePullbackContainment

/-!
# Testing an equational implication on objects of the big fppf site

Let `V`, `U`, `U'` be objects of the big fppf site over `S`, and let `X, Y : V ⟶ U` and
`X', Y' : V ⟶ U'` be two pairs of parallel morphisms. If every morphism `W ⟶ V` from an object of
the site which equalizes `X` and `Y` also equalizes `X'` and `Y'`, then the same holds for every
morphism `T ⟶ V` from an arbitrary scheme over `S`: the equalizer of `X` and `Y`, formed in
schemes over `S`, is a fibre product of two schemes of the site, hence lies in the site
(`AlgebraicGeometry.BigFppfSite.contains_pullback_left`), and every such `T ⟶ V` factors through
it.

This is how a statement about sections of representable presheaves on the site — such as the
stabilizer property of the proof of Stacks 0DUQ — becomes a statement about all generalized points
in schemes over `S`, which is the form the hypotheses of Stacks 0DT9 take.

## Main results

* `AlgebraicGeometry.Space.comp_eq_of_forall_site`: the transfer.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (C : BigFppfSite.{u}) {S : Scheme.{u}} (hS : C.Contains S)

/-- **An equational implication tested on objects of the site holds on all schemes over `S`.** -/
theorem comp_eq_of_forall_site {V U U' : BigFppfOver C S hS} (X Y : V ⟶ U) (X' Y' : V ⟶ U')
    (h : ∀ (W : BigFppfOver C S hS) (v : W ⟶ V), v ≫ X = v ≫ Y → v ≫ X' = v ≫ Y')
    {T : Over S} (r : T ⟶ (siteToOver C hS).obj V)
    (hr : r ≫ (siteToOver C hS).map X = r ≫ (siteToOver C hS).map Y) :
    r ≫ (siteToOver C hS).map X' = r ≫ (siteToOver C hS).map Y' := by
  let F := siteToOver C hS
  let a : F.obj V ⟶ F.obj U ⨯ F.obj U := prod.lift (F.map X) (F.map Y)
  let d : F.obj U ⟶ F.obj U ⨯ F.obj U := prod.lift (𝟙 (F.obj U)) (𝟙 (F.obj U))
  have hE : C.Contains (pullback a d).left :=
    BigFppfSite.contains_pullback_left C a d V.left.2 U.left.2
  let ι : pullback a d ⟶ F.obj V := pullback.fst a d
  have hι : ι ≫ F.map X = ι ≫ F.map Y := by
    have h₁ := congrArg (· ≫ prod.fst) (pullback.condition (f := a) (g := d))
    have h₂ := congrArg (· ≫ prod.snd) (pullback.condition (f := a) (g := d))
    simp only [Category.assoc, a, d, prod.lift_fst, prod.lift_snd, Category.comp_id] at h₁ h₂
    exact h₁.trans h₂.symm
  have e : F.obj (schemeSiteObject C hS hE) = pullback a d :=
    siteToOver_obj_schemeSiteObject C hS hE
  let ιs : schemeSiteObject C hS hE ⟶ V := F.preimage (eqToHom e ≫ ι)
  have hιs : F.map ιs = eqToHom e ≫ ι := F.map_preimage _
  have h₁ : ιs ≫ X = ιs ≫ Y := by
    apply F.map_injective
    rw [F.map_comp, F.map_comp, hιs, Category.assoc, Category.assoc, hι]
  have h₂ := congrArg F.map (h _ ιs h₁)
  rw [F.map_comp, F.map_comp, hιs, Category.assoc, Category.assoc] at h₂
  have h₃ : ι ≫ F.map X' = ι ≫ F.map Y' := (cancel_epi (eqToHom e)).1 h₂
  let r' : T ⟶ pullback a d := pullback.lift r (r ≫ F.map X)
    (prod.hom_ext (by simp [a, d]) (by simpa [a, d] using hr.symm))
  rw [show r = r' ≫ ι from (pullback.lift_fst _ _ _).symm, Category.assoc, Category.assoc, h₃]

end AlgebraicGeometry.Space

end
