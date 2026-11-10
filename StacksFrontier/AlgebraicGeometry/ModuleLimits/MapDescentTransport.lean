module

public import StacksFrontier.AlgebraicGeometry.ModuleLimits.MapDescentGlue
/-!
# Restricting a morphism of restrictions, read functorially

`Stacks.AlgebraicGeometry.ModuleLimits.restrictHomOfLE` restricts a morphism `χ : M|_W ⟶ N|_W`
to a smaller open `V ≤ W` sectionwise. This file identifies `restrictHomOfLE e χ` with the
conjugate of `χ` by the comparison `restrictLEIso e` between `(-)|_V` and `((-)|_W)|_V`, i.e. the
image of `χ` under `Scheme.Modules.restrictFunctor (X.homOfLE e)` read through that comparison.

## Main definitions

* `Stacks.AlgebraicGeometry.ModuleLimits.restrictLEIso`: for `V ≤ W` the natural isomorphism
  between restricting to `W` and then to `V`, and restricting to `V` directly. It is Mathlib's
  `AlgebraicGeometry.Scheme.Modules.restrictFunctorComp` followed by
  `AlgebraicGeometry.Scheme.Modules.restrictFunctorCongr` applied to
  `AlgebraicGeometry.Scheme.homOfLE_ι`.

## Main results

* `Stacks.AlgebraicGeometry.ModuleLimits.restrictHomOfLE_eq`: `restrictHomOfLE e χ` is the
  functorial conjugate of `χ`.
* `Stacks.AlgebraicGeometry.ModuleLimits.restrictHomOfLE_eq_of_map_eq`: two morphisms with the
  same image under `restrictFunctor (X.homOfLE e)` have the same restriction to `V`.
* `Stacks.AlgebraicGeometry.ModuleLimits.exists_restrictFunctor_map_eq_of_cover_of_restrictLEIso`:
  the Zariski glueing of a morphism out of morphisms of restrictions, with the agreement
  hypothesis on the pairwise intersections stated through `restrictLEIso`.
* `Stacks.AlgebraicGeometry.ModuleLimits.imageSections_eq_map_eqToHom`: the action on sections
  of a morphism of restrictions, written as a conjugation by the two restriction maps belonging
  to the equality of opens `W.ι ''ᵁ Q = U`.

## References

* [Stacks Project, Tag 01ZR](https://stacks.math.columbia.edu/tag/01ZR)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

universe u

namespace Stacks.AlgebraicGeometry.ModuleLimits

variable {X : Scheme.{u}} {M N : X.Modules}

/-! ### The action on sections as a conjugation by restriction maps -/

/-- The action on sections of a morphism of restrictions `χ : M|_W ⟶ N|_W` over an open `U` of
`X` presented as `W.ι ''ᵁ Q`, written as the conjugate of `χ.app Q` by the restriction maps that
the presentation provides. -/
theorem imageSections_eq_map_eqToHom {W : X.Opens}
    (χ : Scheme.Modules.restrict M W.ι ⟶ Scheme.Modules.restrict N W.ι)
    {U : X.Opens} {Q : W.toScheme.Opens} (hQ : W.ι ''ᵁ Q = U) (m : Γ(M, U)) :
    imageSections χ hQ m =
      N.presheaf.map (eqToHom hQ.symm).op (χ.app Q (M.presheaf.map (eqToHom hQ).op m)) := by
  subst hQ
  simp only [imageSections_rfl, restrictAppIso_eq_refl, Iso.refl_hom, Iso.refl_inv,
    eqToHom_refl, op_id, CategoryTheory.Functor.map_id]
  rfl

/-! ### Restriction to a smaller open as a functorial conjugate -/

/-- Two successive restriction maps along equalities of opens compose to the one along the
composite equality. -/
private theorem map_eqToHom_op_apply_trans (P : X.Modules) {A B C : X.Opens} (h₁ : A = B)
    (h₂ : C = A) (y : Γ(P, B)) :
    P.presheaf.map (eqToHom h₂).op (P.presheaf.map (eqToHom h₁).op y) =
      P.presheaf.map (eqToHom (h₂.trans h₁)).op y := by
  subst h₁ h₂
  simp

/-- For `V ≤ W`, restricting to `W` and then along `X.homOfLE e : V ⟶ W` is restricting to `V`.
-/
noncomputable def restrictLEIso {V W : X.Opens} (e : V ≤ W) :
    Scheme.Modules.restrictFunctor W.ι ⋙ Scheme.Modules.restrictFunctor (X.homOfLE e) ≅
      Scheme.Modules.restrictFunctor V.ι :=
  (Scheme.Modules.restrictFunctorComp (X.homOfLE e) W.ι).symm ≪≫
    Scheme.Modules.restrictFunctorCongr (X.homOfLE_ι e)

/-- **The restriction of a morphism of restrictions to a smaller open is the functorial
conjugate.** For `V ≤ W` and `χ : M|_W ⟶ N|_W`, the sectionwise-defined
`restrictHomOfLE e χ : M|_V ⟶ N|_V` is the image of `χ` under
`AlgebraicGeometry.Scheme.Modules.restrictFunctor (X.homOfLE e)`, conjugated by `restrictLEIso e`.
-/
theorem restrictHomOfLE_eq {V W : X.Opens} (e : V ≤ W)
    (χ : Scheme.Modules.restrict M W.ι ⟶ Scheme.Modules.restrict N W.ι) :
    restrictHomOfLE e χ =
      (restrictLEIso e).inv.app M ≫
        (Scheme.Modules.restrictFunctor (X.homOfLE e)).map χ ≫ (restrictLEIso e).hom.app N := by
  refine Scheme.Modules.hom_ext _ _ fun P => ?_
  have h1 : (X.homOfLE e ≫ W.ι) ''ᵁ P = V.ι ''ᵁ P := by
    simp only [Scheme.homOfLE_ι]
  have h2 : W.ι ''ᵁ (X.homOfLE e ''ᵁ P) = (X.homOfLE e ≫ W.ι) ''ᵁ P :=
    (Scheme.Hom.comp_image _ _ _).symm
  have hQ : W.ι ''ᵁ (X.homOfLE e ''ᵁ P) = V.ι ''ᵁ P := h2.trans h1
  have hR : ∀ m : Γ(M, V.ι ''ᵁ P),
      ((restrictLEIso e).inv.app M ≫
          (Scheme.Modules.restrictFunctor (X.homOfLE e)).map χ ≫
            (restrictLEIso e).hom.app N).app P m
        = N.presheaf.map (eqToHom hQ.symm).op (χ.app (X.homOfLE e ''ᵁ P)
            (M.presheaf.map (eqToHom hQ).op m)) := by
    intro m
    change N.presheaf.map (eqToHom h1.symm).op (N.presheaf.map (eqToHom h2.symm).op
        (χ.app (X.homOfLE e ''ᵁ P) (M.presheaf.map (eqToHom h2).op
          (M.presheaf.map (eqToHom h1).op m)))) = _
    rw [map_eqToHom_op_apply_trans M h1 h2]
    exact map_eqToHom_op_apply_trans N h2.symm h1.symm _
  have hL : ∀ m : Γ(M, V.ι ''ᵁ P), (restrictHomOfLE e χ).app P m
      = N.presheaf.map (eqToHom hQ.symm).op (χ.app (X.homOfLE e ''ᵁ P)
          (M.presheaf.map (eqToHom hQ).op m)) := by
    intro m
    rw [← imageSections_rfl_app (restrictHomOfLE e χ) P m,
      imageSections_restrictHomOfLE_rfl, imageSections_congr χ _ hQ m,
      imageSections_eq_map_eqToHom]
  ext m
  exact (hL m).trans (hR m).symm

/-- **Transport along the restriction functor.**  Two morphisms `M|_W ⟶ N|_W` with the same image
under `restrictFunctor (X.homOfLE e)` have the same restriction to `V`. -/
theorem restrictHomOfLE_eq_of_map_eq {V W : X.Opens} (e : V ≤ W)
    (χ₁ χ₂ : Scheme.Modules.restrict M W.ι ⟶ Scheme.Modules.restrict N W.ι)
    (h : (Scheme.Modules.restrictFunctor (X.homOfLE e)).map χ₁ =
      (Scheme.Modules.restrictFunctor (X.homOfLE e)).map χ₂) :
    restrictHomOfLE e χ₁ = restrictHomOfLE e χ₂ := by
  rw [restrictHomOfLE_eq, restrictHomOfLE_eq, h]

/-! ### The glueing with the agreement hypothesis read functorially -/

/-- **Zariski glueing of a morphism of sheaves of modules out of morphisms of restrictions**, with
the agreement on the pairwise intersections of the covering stated as an equality of the two
functorial conjugates rather than of the two `restrictHomOfLE`s. -/
theorem exists_restrictFunctor_map_eq_of_cover_of_restrictLEIso {ι : Type u} (W : ι → X.Opens)
    (hW : ∀ x : X, ∃ a, x ∈ W a)
    (χ : ∀ a, Scheme.Modules.restrict M (W a).ι ⟶ Scheme.Modules.restrict N (W a).ι)
    (hagree : ∀ a b,
      (restrictLEIso (inf_le_left : W a ⊓ W b ≤ W a)).inv.app M ≫
          (Scheme.Modules.restrictFunctor
            (X.homOfLE (inf_le_left : W a ⊓ W b ≤ W a))).map (χ a) ≫
          (restrictLEIso (inf_le_left : W a ⊓ W b ≤ W a)).hom.app N =
        (restrictLEIso (inf_le_right : W a ⊓ W b ≤ W b)).inv.app M ≫
          (Scheme.Modules.restrictFunctor
            (X.homOfLE (inf_le_right : W a ⊓ W b ≤ W b))).map (χ b) ≫
          (restrictLEIso (inf_le_right : W a ⊓ W b ≤ W b)).hom.app N) :
    ∃ φ : M ⟶ N, ∀ a, (Scheme.Modules.restrictFunctor (W a).ι).map φ = χ a :=
  exists_restrictFunctor_map_eq_of_cover_of_inf W hW χ fun a b => by
    rw [restrictHomOfLE_eq, restrictHomOfLE_eq]
    exact hagree a b

end Stacks.AlgebraicGeometry.ModuleLimits

end
