module

public import Mathlib.CategoryTheory.Sites.LocallyBijective

/-!
# A morphism of sheaves of sets which is an isomorphism over a covering family

Let `C` be a site and `Ψ : A ⟶ Y` a morphism of sheaves of sets over a presheaf `X`. Suppose a
family of morphisms `c_i : W_i ⟶ X` covers `X` locally: every section of `X` is, locally, in the
image of some `c_i`. If over every `c_i` there are cartesian squares `φ_i : W'_i ⟶ A` and
`φ_i ≫ Ψ : W'_i ⟶ Y` with the same second projection `W'_i ⟶ W_i`, then `Ψ` is an isomorphism.
This is the family version of
`AlgebraicGeometry.Space.isIso_of_isPullback_of_isLocallySurjective`; it is how an isomorphism
of algebraic spaces over `X` is detected on the affine étale charts of `X`, which do not form one
chart.

## Main definitions

* `CategoryTheory.Presheaf.familyImageSieve`: the sieve of the morphisms along which a section of
  `X` lifts to one of the `W_i`.

## Main results

* `CategoryTheory.Presheaf.isIso_of_isPullback_family`: the criterion.
-/

@[expose] public section

open CategoryTheory Opposite

universe w v u

namespace CategoryTheory.Presheaf

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

/-- **The sieve of the morphisms along which a section of `X` lifts to one of the `W_i`.** -/
def familyImageSieve {X : Cᵒᵖ ⥤ Type w} {ι : Type*} {W : ι → Cᵒᵖ ⥤ Type w}
    (c : ∀ i, W i ⟶ X) {T : C} (x : X.obj (op T)) : Sieve T where
  arrows T' f := ∃ (i : ι) (t : (W i).obj (op T')), (c i).app _ t = X.map f.op x
  downward_closed := by
    rintro T' T'' f ⟨i, t, ht⟩ g
    refine ⟨i, (W i).map g.op t, ?_⟩
    rw [NatTrans.naturality_apply, ht, ← Functor.map_comp_apply]
    rfl

/-- **A morphism of sheaves of sets over `X` is an isomorphism if it is one over a locally
covering family `c_i : W_i ⟶ X`**, in the form: there are cartesian squares `φ_i : W'_i ⟶ A` over
`c_i` and `φ_i ≫ Ψ : W'_i ⟶ Y` over `c_i`, with the same second projection `w_i : W'_i ⟶ W_i`. -/
theorem isIso_of_isPullback_family {A Y X : Cᵒᵖ ⥤ Type v}
    (hA : Presheaf.IsSheaf J A) (hY : Presheaf.IsSheaf J Y) (a : A ⟶ X) (q : Y ⟶ X)
    (Ψ : A ⟶ Y) (hΨ : Ψ ≫ q = a) {ι : Type*} {W W' : ι → Cᵒᵖ ⥤ Type v} (c : ∀ i, W i ⟶ X)
    (hc : ∀ (T : C) (x : X.obj (op T)), familyImageSieve c x ∈ J T)
    (φ : ∀ i, W' i ⟶ A) (w : ∀ i, W' i ⟶ W i) (hφ : ∀ i, IsPullback (φ i) (w i) a (c i))
    (hφΨ : ∀ i, IsPullback (φ i ≫ Ψ) (w i) q (c i)) :
    IsIso Ψ := by
  let Ψs : (⟨A, hA⟩ : Sheaf J (Type v)) ⟶ ⟨Y, hY⟩ := ObjectProperty.homMk Ψ
  have hsurj : Sheaf.IsLocallySurjective Ψs := by
    refine ⟨fun {T} y ↦ ?_⟩
    refine J.superset_covering ?_ (hc T (q.app (op T) y))
    rintro T' f ⟨i, v, hv⟩
    let yh : yoneda.obj T' ⟶ Y := yonedaEquiv.symm (Y.map f.op y)
    let vh : yoneda.obj T' ⟶ W i := yonedaEquiv.symm v
    have hw : yh ≫ q = vh ≫ c i := by
      apply yonedaEquiv.injective
      rw [yonedaEquiv_comp, yonedaEquiv_comp, Equiv.apply_symm_apply, Equiv.apply_symm_apply,
        hv]
      exact q.naturality_apply f.op y
    refine ⟨(φ i).app _ (yonedaEquiv ((hφΨ i).lift yh vh hw)), ?_⟩
    have h := congrArg yonedaEquiv ((hφΨ i).lift_fst yh vh hw)
    rw [yonedaEquiv_comp, Equiv.apply_symm_apply] at h
    change Ψ.app _ ((φ i).app _ _) = _
    rw [← h]
    rfl
  have hinj : Sheaf.IsLocallyInjective Ψs := by
    refine ⟨fun {T} x₁ x₂ hx ↦ ?_⟩
    refine J.superset_covering ?_ (hc T.unop (a.app T x₁))
    rintro T' f ⟨i, v, hv⟩
    change A.map f.op x₁ = A.map f.op x₂
    let xh₁ : yoneda.obj T' ⟶ A := yonedaEquiv.symm (A.map f.op x₁)
    let xh₂ : yoneda.obj T' ⟶ A := yonedaEquiv.symm (A.map f.op x₂)
    let vh : yoneda.obj T' ⟶ W i := yonedaEquiv.symm v
    have ha : a.app T x₂ = a.app T x₁ := by
      rw [← hΨ]
      exact congrArg (q.app T) hx.symm
    have hw₁ : xh₁ ≫ a = vh ≫ c i := by
      apply yonedaEquiv.injective
      rw [yonedaEquiv_comp, yonedaEquiv_comp, Equiv.apply_symm_apply, Equiv.apply_symm_apply,
        hv]
      exact a.naturality_apply f.op x₁
    have hw₂ : xh₂ ≫ a = vh ≫ c i := by
      apply yonedaEquiv.injective
      rw [yonedaEquiv_comp, yonedaEquiv_comp, Equiv.apply_symm_apply, Equiv.apply_symm_apply,
        hv, ← ha]
      exact a.naturality_apply f.op x₂
    have hl : (hφ i).lift xh₁ vh hw₁ = (hφ i).lift xh₂ vh hw₂ := by
      apply (hφΨ i).hom_ext
      · rw [← Category.assoc, (hφ i).lift_fst, ← Category.assoc, (hφ i).lift_fst]
        apply yonedaEquiv.injective
        rw [yonedaEquiv_comp, yonedaEquiv_comp, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
        change (Ψ.app _ (A.map f.op x₁)) = Ψ.app _ (A.map f.op x₂)
        rw [Ψ.naturality_apply, Ψ.naturality_apply]
        exact congrArg (Y.map f.op) hx
      · rw [(hφ i).lift_snd, (hφ i).lift_snd]
    have h := ((hφ i).lift_fst xh₁ vh hw₁).symm.trans (hl ▸ (hφ i).lift_fst xh₂ vh hw₂)
    simpa [xh₁, xh₂] using congrArg yonedaEquiv h
  have : IsIso Ψs := (Sheaf.isLocallyBijective_iff_isIso Ψs).1 ⟨hinj, hsurj⟩
  exact (sheafToPresheaf J (Type v)).map_isIso Ψs

end CategoryTheory.Presheaf

end
