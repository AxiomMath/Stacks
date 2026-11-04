module

public import StacksFrontier.CategoryTheory.FiberedCategory.HomLift
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Comp
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.CostructuredArrow
public import StacksFrontier.CategoryTheory.Sites.CostructuredArrowRestrictedTopology
public import StacksFrontier.CategoryTheory.Sites.Gerbe.Basic

/-!
# Gerbes over a category of costructured arrows, read over the base

Let `G : C ⥤ D` be a functor, `Y` an object of `D` and `K` a Grothendieck topology on `C`, and
give the costructured arrows `CostructuredArrow G Y` the topology restricted from `K` along the
projection `j : CostructuredArrow G Y ⥤ C`.  A category `𝒴` over the costructured arrows is then
also a category over `C`, through `j`.  This file shows that a functor `F : 𝒳 ⥤ 𝒴` which makes
`𝒳` a gerbe over `𝒴` in the sense of Stacks 06P2 over the costructured arrows also does so over
`C`.

The typical instance is a category over the schemes `T` with a morphism to a fixed algebraic
space `B`, read as a category over all the schemes of the site: the condition over `(Sch/B)` is
where the data live, the condition over `(Sch/S)` is what the source's definitions ask.

## Main results

* `CategoryTheory.CostructuredArrow.eq_of_left_eq_eqToHom`: the fibres of the projection are
  discrete — a morphism of costructured arrows whose component is an identity is an identity.
* `CategoryTheory.IsGerbeOver.comp_costructuredArrowProj`: a gerbe over the costructured arrows
  with the restricted topology is a gerbe over `C`.

## Implementation notes

The two topologies match because a sieve of a costructured arrow `T` is covering for the restricted
topology exactly when its image under `j` is a covering of `T.left`
(`CategoryTheory.CostructuredArrow.mem_restrictedTopology_proj_iff`), and an arrow `f` of that
image underlies the canonical lift `CategoryTheory.CostructuredArrow.liftHom` lying in the sieve
itself.  So the local data over the costructured arrows are the local data over `C`, read along
`j`.  For the second condition one also needs a morphism of `𝒴` lying over an identity of `C` to
lie over an identity of the costructured arrows, which is the discreteness of the fibres of `j`.
-/

@[expose] public section

namespace CategoryTheory

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

namespace CostructuredArrow

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D] {G : C ⥤ D} {Y : D}

/-- **The fibres of the projection of the costructured arrows are discrete**: a morphism of
costructured arrows whose component in `C` is the identity, read along an equality of the two
underlying objects, has equal source and target. -/
lemma eq_of_left_eq_eqToHom {T T' : CostructuredArrow G Y} (g : T ⟶ T') (h : T.left = T'.left)
    (hg : g.left = eqToHom h) : T = T' :=
  CostructuredArrow.obj_ext T T' h (by rw [← hg]; exact CostructuredArrow.w g)

/-- A morphism of costructured arrows whose component in `C` is an identity is the identity, read
along the equality of its source and target. -/
lemma eq_eqToHom_of_left_eq_eqToHom {T T' : CostructuredArrow G Y} (g : T ⟶ T')
    (h : T.left = T'.left) (hg : g.left = eqToHom h) :
    g = eqToHom (eq_of_left_eq_eqToHom g h hg) := by
  ext
  rw [hg, CostructuredArrow.eqToHom_left]

end CostructuredArrow

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D] {G : C ⥤ D} {Y : D}
  {K : GrothendieckTopology C} {𝒳 : Type u₃} [Category.{v₃} 𝒳] {𝒴 : Type u₄} [Category.{v₄} 𝒴]
  {q : 𝒴 ⥤ CostructuredArrow G Y} {F : 𝒳 ⥤ 𝒴}

/-- **A gerbe over the costructured arrows is a gerbe over the base.**  If `F : 𝒳 ⥤ 𝒴` makes
`𝒳` a gerbe over `𝒴` (Stacks 06P2) for the structure functor `q : 𝒴 ⥤ CostructuredArrow G Y`
and the topology restricted from `K` along the projection `j`, then it does so for the structure
functor `q ⋙ j : 𝒴 ⥤ C` and the topology `K`. -/
theorem IsGerbeOver.comp_costructuredArrowProj
    (h : IsGerbeOver ((CostructuredArrow.proj G Y).restrictedTopology K) q F) :
    IsGerbeOver K (q ⋙ CostructuredArrow.proj G Y) F where
  base_isFiberedInGroupoids :=
    Functor.IsFiberedInGroupoids.comp q _ h.base_isFiberedInGroupoids
      (Functor.IsFiberedInGroupoids.costructuredArrow_proj G Y)
  isFiberedInGroupoids :=
    Functor.IsFiberedInGroupoids.comp (F ⋙ q) _ h.isFiberedInGroupoids
      (Functor.IsFiberedInGroupoids.costructuredArrow_proj G Y)
  locally_essSurj := by
    intro U y hy
    subst hy
    obtain ⟨R, hR, hcov⟩ := h.locally_essSurj y rfl
    refine ⟨R.functorPushforward (CostructuredArrow.proj G Y),
      (CostructuredArrow.mem_restrictedTopology_proj_iff G Y K _ R).1 hR, ?_⟩
    intro V f hf
    obtain ⟨x, ψ, hψ⟩ := hcov _
      ((CostructuredArrow.mem_functorPushforward_proj_liftHom_iff G Y R f).1 hf)
    exact ⟨x, ψ, Functor.isHomLift_comp_functor (CostructuredArrow.proj G Y) _ ψ hψ⟩
  locally_full := by
    intro U x x' b hb
    have hU := IsHomLift.domain_eq (q ⋙ CostructuredArrow.proj G Y) (𝟙 U) b
    have hU' := IsHomLift.codomain_eq (q ⋙ CostructuredArrow.proj G Y) (𝟙 U) b
    have hfac := IsHomLift.fac' (q ⋙ CostructuredArrow.proj G Y) (𝟙 U) b
    subst hU
    have hl : (q.map b).left = eqToHom hU'.symm := by
      simpa using hfac
    have hT := CostructuredArrow.eq_of_left_eq_eqToHom (q.map b) hU'.symm hl
    have hlift : q.IsHomLift (𝟙 (q.obj (F.obj x))) b :=
      IsHomLift.of_fac' q _ b rfl hT.symm (by
        rw [CostructuredArrow.eq_eqToHom_of_left_eq_eqToHom (q.map b) hU'.symm hl]
        simp)
    obtain ⟨R, hR, hcov⟩ := h.locally_full b hlift
    refine ⟨R.functorPushforward (CostructuredArrow.proj G Y),
      (CostructuredArrow.mem_restrictedTopology_proj_iff G Y K _ R).1 hR, ?_⟩
    intro V f hf
    obtain ⟨x₁, x₁', ξ, ξ', a, hξ, hξ', ha, hsq⟩ := hcov _
      ((CostructuredArrow.mem_functorPushforward_proj_liftHom_iff G Y R f).1 hf)
    exact ⟨x₁, x₁', ξ, ξ', a,
      Functor.isHomLift_comp_functor (CostructuredArrow.proj G Y) _ ξ hξ,
      Functor.isHomLift_comp_functor (CostructuredArrow.proj G Y) _ ξ' hξ',
      Functor.isHomLift_comp_functor (CostructuredArrow.proj G Y) _ a ha, hsq⟩

end CategoryTheory

end
