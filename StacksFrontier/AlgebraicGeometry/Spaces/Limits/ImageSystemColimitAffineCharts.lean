module

public import StacksFrontier.AlgebraicGeometry.Spaces.AlgebraSheafImageQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.AffineSectionsOfColimitInjective
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.ModuleColimitAffineChartSections

/-!
# Images of a module in a filtered colimit of quasi-coherent modules

Let `Φ` be a filtered diagram of quasi-coherent modules on an algebraic space `X`, with colimit
`ℳ = colim Φ`, and let `β_k : 𝒩 ⟶ Φ_k` be a compatible family of maps out of a quasi-coherent
module `𝒩`.  Then the images `Ψ_k = Im(β_k) ⊆ Φ_k` form a diagram with surjective transition
maps whose colimit is the image of `𝒩` in `ℳ`.

## Main results

* `AlgebraicGeometry.Space.nonempty_isColimit_of_mono_of_epi`: a cocone of quasi-coherent
  subobjects of a filtered colimit whose legs are epimorphisms onto a subobject of the colimit is
  a colimit.
* `AlgebraicGeometry.Space.exists_imageSystem_isColimit`: the images of a compatible family of
  maps out of a quasi-coherent module form a diagram with epimorphic transitions whose colimit is
  the image in the colimit.

## References

* [Stacks Project, Tag 0GV1](https://stacks.math.columbia.edu/tag/0GV1)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {hF : IsAlgebraicSpace B S hS F}

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

/-- **A cocone of quasi-coherent subobjects of a filtered colimit, whose legs are epimorphisms
onto a subobject of the colimit, is a colimit.**  Let `c` be a colimit cocone of a filtered
diagram `Φ` of modules on an algebraic space, let `α : Ψ ⟶ Φ` be a monomorphism of diagrams and
let `d` be a cocone of `Ψ` with a monomorphism `m : d.pt ⟶ c.pt` compatible with `α`.  If the
members of `Ψ` and `d.pt` are quasi-coherent and every leg of `d` is an epimorphism, then `d` is a
colimit cocone. -/
theorem nonempty_isColimit_of_mono_of_epi {K : Type u} [SmallCategory K] [IsFiltered K]
    {Φ Ψ : K ⥤ Modules.{u, u} B S hS F hF} {c : Cocone Φ} (hc : IsColimit c) (α : Ψ ⟶ Φ)
    (hα : ∀ k, Mono (α.app k)) (d : Cocone Ψ) (m : d.pt ⟶ c.pt) (_hm : Mono m)
    (hdm : ∀ k, d.ι.app k ≫ m = α.app k ≫ c.ι.app k) (hd : ∀ k, Epi (d.ι.app k))
    (hΨ : ∀ k, (Ψ.obj k).IsQuasicoherentOnSite) (hN : d.pt.IsQuasicoherentOnSite) :
    Nonempty (IsColimit d) := by
  obtain ⟨k₀⟩ : Nonempty K := IsFiltered.nonempty
  refine ⟨isColimit_modules_of_affineChartSections_of_isFiltered d
    (fun U hU x => ?_) (fun U hU k y hy => ?_)⟩
  · obtain ⟨y, hy⟩ := surjective_val_app_of_epi_of_isQuasicoherentOnSite (d.ι.app k₀) (hd k₀)
      (hΨ k₀) hN U hU x
    exact ⟨k₀, y, hy⟩
  · have h0 : (c.ι.app k).val.app (op U) ((α.app k).val.app (op U) y) = 0 := by
      have := congrArg (fun φ => φ.val.app (op U) y) (hdm k)
      change m.val.app (op U) ((d.ι.app k).val.app (op U) y) =
        (c.ι.app k).val.app (op U) ((α.app k).val.app (op U) y) at this
      rw [← this, hy, map_zero]
    obtain ⟨l, f, hf⟩ := exists_map_eq_zero_of_isColimit hc hU k _ h0
    refine ⟨l, f, Stacks.SheafOfModules.injective_app_of_mono (α.app l) (op U) ?_⟩
    have := congrArg (fun φ => φ.val.app (op U) y) (α.naturality f)
    change (α.app l).val.app (op U) ((Ψ.map f).val.app (op U) y) =
      (Φ.map f).val.app (op U) ((α.app k).val.app (op U) y) at this
    rw [this, hf, map_zero]

/-- The square from `u : A ⟶ B` to `v : A ⟶ C` given by `w : B ⟶ C` with `u ≫ w = v`. -/
private def imageSq {C : Type*} [Category C] {A B' C' : C} (u : A ⟶ B') (v : A ⟶ C')
    (w : B' ⟶ C') (h : u ≫ w = v) : Arrow.mk u ⟶ Arrow.mk v :=
  Arrow.homMk (𝟙 A) w (by simp [h])

private theorem factorThruImage_imageSq {C : Type*} [Category C] [HasImages C] [HasImageMaps C]
    {A B' C' : C} (u : A ⟶ B') (v : A ⟶ C') (w : B' ⟶ C') (h : u ≫ w = v) :
    factorThruImage u ≫ image.map (imageSq u v w h) = factorThruImage v :=
  (image.factor_map (imageSq u v w h)).trans (Category.id_comp _)

private theorem imageSq_ι {C : Type*} [Category C] [HasImages C] [HasImageMaps C]
    {A B' C' : C} (u : A ⟶ B') (v : A ⟶ C') (w : B' ⟶ C') (h : u ≫ w = v) :
    image.map (imageSq u v w h) ≫ image.ι v = image.ι u ≫ w :=
  image.map_ι (imageSq u v w h)

/-- A compatible family `β_k : 𝒩 ⟶ Φ_k` commutes with the transition maps of `Φ`. -/
private theorem imageSystem_comm {K : Type u} [SmallCategory K]
    {Φ : K ⥤ Modules.{u, u} B S hS F hF}
    {N : Modules.{u, u} B S hS F hF} (β : (Functor.const K).obj N ⟶ Φ) {k l : K} (f : k ⟶ l) :
    β.app k ≫ Φ.map f = β.app l := by
  simpa only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp] using
    (β.naturality f).symm

/-- **The images of a compatible family of maps out of a quasi-coherent module, in a filtered
colimit of quasi-coherent modules.**  Let `c` be a colimit cocone of a filtered diagram `Φ` of
quasi-coherent modules on an algebraic space, with quasi-coherent vertex, and let
`β_k : 𝒩 ⟶ Φ_k` be a compatible family of maps out of a quasi-coherent module `𝒩`.  There are a
diagram `Ψ` of quasi-coherent modules with epimorphic transition maps, a monomorphism of
diagrams `α : Ψ ⟶ Φ` and epimorphisms `e_k : 𝒩 ⟶ Ψ_k` with `e_k ≫ α_k = β_k` (so `Ψ_k` is the
image of `β_k`), and a colimit cocone `d` of `Ψ` with a monomorphism `m : d.pt ⟶ c.pt` and an
epimorphism `e : 𝒩 ⟶ d.pt` with `e ≫ m = β_k ≫ c.ι_k` (so `d.pt` is the image of `𝒩` in the
colimit), compatible with `α`. -/
theorem exists_imageSystem_isColimit {K : Type u} [SmallCategory K] [IsFiltered K]
    {Φ : K ⥤ Modules.{u, u} B S hS F hF} {c : Cocone Φ} (hc : IsColimit c)
    (hΦ : ∀ k, (Φ.obj k).IsQuasicoherentOnSite) (hM : c.pt.IsQuasicoherentOnSite)
    {N : Modules.{u, u} B S hS F hF} (hN : N.IsQuasicoherentOnSite)
    (β : (Functor.const K).obj N ⟶ Φ) :
    ∃ (Ψ : K ⥤ Modules.{u, u} B S hS F hF) (α : Ψ ⟶ Φ) (eΨ : (Functor.const K).obj N ⟶ Ψ)
      (d : Cocone Ψ) (m : d.pt ⟶ c.pt) (e : N ⟶ d.pt),
      (∀ k, Mono (α.app k)) ∧ (∀ k, Epi (eΨ.app k)) ∧ (∀ k, eΨ.app k ≫ α.app k = β.app k) ∧
      (∀ {k l : K} (f : k ⟶ l), Epi (Ψ.map f)) ∧ (∀ k, (Ψ.obj k).IsQuasicoherentOnSite) ∧
      Mono m ∧ Epi e ∧ (∀ k, e ≫ m = β.app k ≫ c.ι.app k) ∧
      (∀ k, d.ι.app k ≫ m = α.app k ≫ c.ι.app k) ∧ (∀ k, eΨ.app k ≫ d.ι.app k = e) ∧
      d.pt.IsQuasicoherentOnSite ∧ Nonempty (IsColimit d) := by
  obtain ⟨k₀⟩ : Nonempty K := IsFiltered.nonempty
  let γ : N ⟶ c.pt := β.app k₀ ≫ c.ι.app k₀
  have hγ' : ∀ {k l : K} (f : k ⟶ l), β.app k ≫ c.ι.app k = β.app l ≫ c.ι.app l := by
    intro k l f
    rw [← imageSystem_comm β f, Category.assoc, c.w f]
  have hγ : ∀ k, β.app k ≫ c.ι.app k = γ := fun k =>
    (hγ' (IsFiltered.leftToMax k k₀)).trans (hγ' (IsFiltered.rightToMax k k₀)).symm
  let Ψ : K ⥤ Modules.{u, u} B S hS F hF :=
    { obj := fun k => image (β.app k)
      map := fun {k l} f => image.map (imageSq _ _ (Φ.map f) (imageSystem_comm β f))
      map_id := fun k => by
        rw [← cancel_epi (factorThruImage (β.app k)), factorThruImage_imageSq,
          Category.comp_id]
      map_comp := fun {k _ _} f g => by
        rw [← cancel_epi (factorThruImage (β.app k)), factorThruImage_imageSq, ← Category.assoc,
          factorThruImage_imageSq, factorThruImage_imageSq] }
  let α : Ψ ⟶ Φ :=
    { app := fun k => image.ι (β.app k)
      naturality := fun k l f => imageSq_ι _ _ _ _ }
  let eΨ : (Functor.const K).obj N ⟶ Ψ :=
    { app := fun k => factorThruImage (β.app k)
      naturality := fun k l f =>
        (Category.id_comp _).trans (factorThruImage_imageSq _ _ _ _).symm }
  let sqc : ∀ k, Arrow.mk (β.app k) ⟶ Arrow.mk γ := fun k => imageSq _ _ (c.ι.app k) (hγ k)
  let d : Cocone Ψ :=
    { pt := image γ
      ι :=
        { app := fun k => image.map (sqc k)
          naturality := fun k l f => by
            rw [← cancel_epi (factorThruImage (β.app k))]
            change factorThruImage (β.app k) ≫
                image.map (imageSq _ _ (Φ.map f) (imageSystem_comm β f)) ≫
                image.map (sqc l) = factorThruImage (β.app k) ≫ image.map (sqc k) ≫ 𝟙 _
            rw [Category.comp_id, ← Category.assoc, factorThruImage_imageSq]
            exact (factorThruImage_imageSq _ _ _ _).trans
              (factorThruImage_imageSq _ _ _ _).symm } }
  have hd : ∀ k, factorThruImage (β.app k) ≫ d.ι.app k = factorThruImage γ := fun k =>
    factorThruImage_imageSq _ _ _ _
  have hΨ : ∀ k, (Ψ.obj k).IsQuasicoherentOnSite := fun k =>
    isQuasicoherentOnSite_image_unconditional B S hS F hF (β.app k) hN (hΦ k)
  have hdpt : d.pt.IsQuasicoherentOnSite :=
    isQuasicoherentOnSite_image_unconditional B S hS F hF γ hN hM
  have hdm : ∀ k, d.ι.app k ≫ image.ι γ = α.app k ≫ c.ι.app k := fun k =>
    imageSq_ι _ _ _ _
  have hdepi : ∀ k, Epi (d.ι.app k) := fun k => epi_of_epi_fac (hd k)
  refine ⟨Ψ, α, eΨ, d, image.ι γ, factorThruImage γ, fun k => inferInstanceAs (Mono (image.ι _)),
    fun k => inferInstanceAs (Epi (factorThruImage _)), fun k => image.fac _, fun {k l} f => ?_,
    hΨ, inferInstance, inferInstance, fun k => by rw [image.fac, hγ k], hdm, hd, hdpt,
    nonempty_isColimit_of_mono_of_epi hc α (fun k => inferInstanceAs (Mono (image.ι _))) d
      (image.ι γ) inferInstance hdm hdepi hΨ hdpt⟩
  exact epi_of_epi_fac (factorThruImage_imageSq _ _ _ (imageSystem_comm β f))

end AlgebraicGeometry.Space

end
