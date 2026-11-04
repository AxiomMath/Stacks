module

public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Factorization
public import StacksFrontier.CategoryTheory.Sites.Gerbe.Basic

/-! # Being a gerbe over a base is invariant under a vertical isomorphism of the structure functor

Let `q : 𝒴 ⥤ 𝒞` fibre `𝒴` over a site `(𝒞, J)` and let `F, G : 𝒳 ⥤ 𝒴` be two functors which
are 1-morphisms over `𝒞` for the *same* fibration of `𝒳`, that is `F ⋙ q = G ⋙ q`. If they are
isomorphic by an isomorphism whose components are `q`-vertical, then `F` makes `𝒳` a gerbe over
`𝒴` exactly when `G` does.

This is the invariance of `CategoryTheory.IsGerbeOver` under 2-isomorphism of its 1-morphism
argument. It is what the invariance under equivalence of Stacks 06P0 — available as
`CategoryTheory.isGerbeOver_iff_of_isEquivalenceOver_base` — does not cover: that result moves
the gerbe condition along a comparison functor `a` with `a ⋙ F' = F` *strictly*, whereas a
comparison produced by a 2-categorical universal property identifies the two structure functors
only up to a 2-cell.

## Main results

* `CategoryTheory.Functor.IsVerticalNatTrans.inv`: the inverse of a vertical natural
  isomorphism is vertical.
* `CategoryTheory.IsGerbeOver.of_verticalNatIso` and
  `CategoryTheory.isGerbeOver_iff_of_verticalNatIso`: the transfer and its biconditional form.

## Implementation notes

Verticality of a natural transformation is stated at the components of its *source* functor
(`CategoryTheory.Functor.IsVerticalNatTrans`), so passing to the inverse changes the object the
identity is taken at; the two are identified by the `eqToHom` form of verticality,
`CategoryTheory.IsHomLift.id_iff_exists_eqToHom`.

Both local conditions of a gerbe transfer by conjugating with the components of the
isomorphism. For the essential-surjectivity condition the comparison is prepended to the
produced morphism, and for the fullness condition the given fibre morphism is conjugated before
the condition is applied to `F` and the resulting square is then conjugated back; the
conjugating components cancel, which is why no compatibility between them is needed.
-/

@[expose] public section

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory

variable {𝒞 : Type u₁} {𝒳 : Type u₂} {𝒴 : Type u₃}
  [Category.{v₁} 𝒞] [Category.{v₂} 𝒳] [Category.{v₃} 𝒴]

/-- The inverse of a `q`-vertical natural isomorphism is `q`-vertical. -/
theorem Functor.IsVerticalNatTrans.inv (q : 𝒴 ⥤ 𝒞) {F G : 𝒳 ⥤ 𝒴} (e : F ≅ G)
    (he : q.IsVerticalNatTrans e.hom) : q.IsVerticalNatTrans e.inv := by
  intro x
  obtain ⟨hx, hmap⟩ := (IsHomLift.id_iff_exists_eqToHom q (e.hom.app x)).mp (he x)
  have hcomp : q.map (e.inv.app x) ≫ eqToHom hx = 𝟙 _ := by
    have hc := congrArg (fun n : G ⟶ G => q.map (n.app x)) e.inv_hom_id
    change q.map (e.inv.app x ≫ e.hom.app x) = q.map (𝟙 (G.obj x)) at hc
    rw [Functor.map_comp, hmap] at hc
    simpa using hc
  refine (IsHomLift.id_iff_exists_eqToHom q (e.inv.app x)).mpr ⟨hx.symm, ?_⟩
  calc q.map (e.inv.app x)
      = (q.map (e.inv.app x) ≫ eqToHom hx) ≫ eqToHom hx.symm := by
        rw [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]
    _ = eqToHom hx.symm := by rw [hcomp, Category.id_comp]

namespace IsGerbeOver

variable {J : GrothendieckTopology 𝒞} {q : 𝒴 ⥤ 𝒞} {F G : 𝒳 ⥤ 𝒴}

/-- **Being a gerbe over a base transfers along a vertical isomorphism of structure functors.**
If `F` makes `𝒳` a gerbe over `𝒴`, if `G` fibres `𝒳` over `𝒞` in the same way (`F ⋙ q = G ⋙ q`)
and if `e : F ≅ G` has `q`-vertical components, then `G` makes `𝒳` a gerbe over `𝒴`. -/
theorem of_verticalNatIso (hF : IsGerbeOver J q F) (hcomp : F ⋙ q = G ⋙ q) (e : F ≅ G)
    (he : q.IsVerticalNatTrans e.hom) : IsGerbeOver J q G := by
  have heInv := Functor.IsVerticalNatTrans.inv q e he
  have hq : ∀ x, q.obj (F.obj x) = q.obj (G.obj x) := Functor.congr_obj hcomp
  have vert : ∀ {A B : 𝒳 ⥤ 𝒴} (n : A ⟶ B), q.IsVerticalNatTrans n → ∀ x U,
      q.obj (A.obj x) = U → q.IsHomLift (𝟙 U) (n.app x) := by
    rintro A B n hn x _ rfl
    exact hn x
  refine ⟨hF.base_isFiberedInGroupoids, hcomp ▸ hF.isFiberedInGroupoids, ?_, ?_⟩
  · intro U y hy
    obtain ⟨S, hS, hcov⟩ := hF.locally_essSurj y hy
    refine ⟨S, hS, fun V f hf => ?_⟩
    obtain ⟨x, ψ, hψ⟩ := hcov f hf
    have hinvV := vert e.inv heInv x V ((hq x).symm.trans (IsHomLift.domain_eq q f ψ))
    refine ⟨x, e.inv.app x ≫ ψ, ?_⟩
    have := hinvV
    have := hψ
    simpa using IsHomLift.comp q (𝟙 V) f (e.inv.app x) ψ
  · intro U x x' b hb
    have hGx : q.obj (G.obj x) = U := IsHomLift.domain_eq q (𝟙 U) b
    have hGx' : q.obj (G.obj x') = U := IsHomLift.codomain_eq q (𝟙 U) b
    have heU := vert e.hom he x U ((hq x).trans hGx)
    have heInvU := vert e.inv heInv x' U hGx'
    have hb₀ : q.IsHomLift (𝟙 U) (e.hom.app x ≫ b ≫ e.inv.app x') := by
      have h₁ : q.IsHomLift (𝟙 U ≫ 𝟙 U) (b ≫ e.inv.app x') := by
        have := hb
        have := heInvU
        exact IsHomLift.comp q (𝟙 U) (𝟙 U) b (e.inv.app x')
      have := heU
      have := h₁
      simpa using IsHomLift.comp q (𝟙 U) (𝟙 U ≫ 𝟙 U) (e.hom.app x) (b ≫ e.inv.app x')
    obtain ⟨S, hS, hcov⟩ := hF.locally_full _ hb₀
    refine ⟨S, hS, fun V f hf => ?_⟩
    obtain ⟨x₁, x₁', ξ, ξ', a, hξ, hξ', ha, hsq⟩ := hcov f hf
    refine ⟨x₁, x₁', ξ, ξ', a, hcomp ▸ hξ, hcomp ▸ hξ', hcomp ▸ ha, ?_⟩
    have h₁ : e.hom.app x₁ ≫ G.map a = F.map a ≫ e.hom.app x₁' := (e.hom.naturality a).symm
    have h₂ : e.hom.app x₁' ≫ G.map ξ' = F.map ξ' ≫ e.hom.app x' := (e.hom.naturality ξ').symm
    have h₃ : e.hom.app x₁ ≫ G.map ξ = F.map ξ ≫ e.hom.app x := (e.hom.naturality ξ).symm
    have key : e.hom.app x₁ ≫ G.map a ≫ G.map ξ' = e.hom.app x₁ ≫ G.map ξ ≫ b := by
      rw [reassoc_of% h₁, h₂, reassoc_of% hsq, reassoc_of% h₃]
      simp
    exact (Iso.cancel_iso_hom_left (e.app x₁) _ _).mp key

end IsGerbeOver

/-- **Stacks 06P0 for a vertical isomorphism of structure functors.** Two 1-morphisms over `𝒞`
with the same source fibration which are isomorphic by a `q`-vertical isomorphism make `𝒳` a
gerbe over `𝒴` at the same time. -/
theorem isGerbeOver_iff_of_verticalNatIso {J : GrothendieckTopology 𝒞} {q : 𝒴 ⥤ 𝒞}
    {F G : 𝒳 ⥤ 𝒴} (hcomp : F ⋙ q = G ⋙ q) (e : F ≅ G)
    (he : q.IsVerticalNatTrans e.hom) : IsGerbeOver J q F ↔ IsGerbeOver J q G :=
  ⟨fun hF => hF.of_verticalNatIso hcomp e he,
    fun hG => hG.of_verticalNatIso hcomp.symm e.symm
      (Functor.IsVerticalNatTrans.inv q e he)⟩

end CategoryTheory

end
