module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.ModulesOnACategory.QuasiCoherenceOnAChaoticSite
public import StacksFrontier.CategoryTheory.Sites.Modules.UniverseLift

/-!
# Universal arrows along equivalences, and restriction of scalars along a ring transport

A morphism `g : X ⟶ G.obj Y` is a universal arrow for a functor `G` when every morphism
`X ⟶ G.obj Z` factors uniquely through `g` (`CategoryTheory.Functor.IsUniversalArrow`); for the
restriction of scalars along a ring map this is the base-change property of a semilinear map,
and for derived restriction of scalars it is the cartesian condition of Stacks 0GYV. This file
shows that universal arrows are transported along equivalences compatible with the two
functors, and records the two pieces of a ring transport `T : RingTransport e O O'` that such a
transport needs: restriction of scalars along the ring isomorphisms `O'(Y) ≃+* O(e⁻¹ Y)` as an
equivalence of module categories, and its compatibility with restriction of scalars along the
restriction maps of `O` and of `O'`.

## Main definitions

* `Stacks.UniverseLift.RingTransport.modEquiv`: restriction of scalars along
  `O'(Y) ≃+* O(e⁻¹ Y)`, as an equivalence `Mod(O(e⁻¹ Y)) ≌ Mod(O'(Y))`.
* `Stacks.UniverseLift.RingTransport.restrictScalarsSquare`: for `a' : V' ⟶ U'` in `Dᵒᵖ`, the
  square of restrictions of scalars relating `O'(V') ⟶ O'(U')` and
  `O(e⁻¹ V') ⟶ O(e⁻¹ U')`.

## Main results

* `CategoryTheory.Functor.IsUniversalArrow.of_equivalence`: universal arrows are transported
  along fully faithful, essentially surjective functors compatible with the two functors.
-/

@[expose] public section

open CategoryTheory Opposite

universe m u v r u' v' r'

namespace CategoryTheory.Functor

variable {X₁ Y₁ X₂ Y₂ : Type*} [Category X₁] [Category Y₁] [Category X₂] [Category Y₂]

/-- **Universal arrows are transported along equivalences.** Let `G₁ : Y₁ ⥤ X₁` and
`G₂ : Y₂ ⥤ X₂` be related by fully faithful functors `ΨX : X₁ ⥤ X₂` and `ΨY : Y₁ ⥤ Y₂`, the
latter essentially surjective, through an isomorphism `ΨY ⋙ G₂ ≅ G₁ ⋙ ΨX`. If `g₁` is a
universal arrow for `G₁`, then so is any arrow `g₂` for `G₂` corresponding to it. -/
theorem IsUniversalArrow.of_equivalence {G₁ : Y₁ ⥤ X₁} {G₂ : Y₂ ⥤ X₂} {ΨX : X₁ ⥤ X₂}
    {ΨY : Y₁ ⥤ Y₂} [ΨX.Full] [ΨX.Faithful] [ΨY.Full] [ΨY.Faithful] [ΨY.EssSurj]
    (β : ΨY ⋙ G₂ ≅ G₁ ⋙ ΨX) {x₁ : X₁} {y₁ : Y₁} {g₁ : x₁ ⟶ G₁.obj y₁} {x₂ : X₂} {y₂ : Y₂}
    {g₂ : x₂ ⟶ G₂.obj y₂} (σx : x₂ ≅ ΨX.obj x₁) (σy : y₂ ≅ ΨY.obj y₁)
    (h : g₂ ≫ G₂.map σy.hom ≫ β.hom.app y₁ = σx.hom ≫ ΨX.map g₁)
    (hg : G₁.IsUniversalArrow g₁) : G₂.IsUniversalArrow g₂ := by
  refine IsUniversalArrow.of_iso (G := G₂) (g := ΨX.map g₁ ≫ β.inv.app y₁) σx.symm σy.symm ?_ ?_
  · have h' : ΨX.map g₁ = σx.inv ≫ g₂ ≫ G₂.map σy.hom ≫ β.hom.app y₁ := by
      rw [h, Iso.inv_hom_id_assoc]
    rw [Iso.symm_hom, Iso.symm_hom, h']
    simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
    rw [← G₂.map_comp, σy.hom_inv_id, G₂.map_id, Category.comp_id]
  · intro Z
    let Z₁ := ΨY.objPreimage Z
    let eZ : ΨY.obj Z₁ ≅ Z := ΨY.objObjPreimageIso Z
    have key : Function.Bijective (fun f₁ : y₁ ⟶ Z₁ ↦
        (ΨX.map g₁ ≫ β.inv.app y₁) ≫ G₂.map (ΨY.map f₁ ≫ eZ.hom)) := by
      have e₁ : (fun f₁ : y₁ ⟶ Z₁ ↦ (ΨX.map g₁ ≫ β.inv.app y₁) ≫ G₂.map (ΨY.map f₁ ≫ eZ.hom)) =
          (fun φ ↦ φ ≫ β.inv.app Z₁ ≫ G₂.map eZ.hom) ∘ ΨX.map ∘ (fun f₁ ↦ g₁ ≫ G₁.map f₁) := by
        funext f₁
        have := β.inv.naturality f₁
        dsimp at this
        simp only [Function.comp_apply, G₂.map_comp, Category.assoc, ΨX.map_comp]
        rw [reassoc_of% this]
      rw [e₁]
      refine Function.Bijective.comp ?_ (Function.Bijective.comp ?_ (hg Z₁))
      · exact ⟨fun _ _ hab ↦ (cancel_mono (β.inv.app Z₁ ≫ G₂.map eZ.hom)).1 hab,
          fun c ↦ ⟨c ≫ G₂.map eZ.inv ≫ β.hom.app Z₁, by simp⟩⟩
      · exact (Functor.FullyFaithful.ofFullyFaithful ΨX).map_bijective _ _
    have e₂ : (fun f : ΨY.obj y₁ ⟶ Z ↦ (ΨX.map g₁ ≫ β.inv.app y₁) ≫ G₂.map f) =
        (fun f₁ : y₁ ⟶ Z₁ ↦ (ΨX.map g₁ ≫ β.inv.app y₁) ≫ G₂.map (ΨY.map f₁ ≫ eZ.hom)) ∘
          (fun f ↦ ΨY.preimage (f ≫ eZ.inv)) := by
      funext f
      simp
    rw [e₂]
    exact key.comp ⟨fun a b hab ↦ by simpa using congrArg (fun f ↦ ΨY.map f ≫ eZ.hom) hab,
      fun f₁ ↦ ⟨ΨY.map f₁ ≫ eZ.hom, by simp⟩⟩

end CategoryTheory.Functor

namespace Stacks.UniverseLift.RingTransport

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D] {e : C ≌ D}
  {O : Cᵒᵖ ⥤ RingCat.{r}} {O' : Dᵒᵖ ⥤ RingCat.{r'}} (T : RingTransport e O O')

/-- Restriction of scalars along the ring isomorphism `O'(Y) ≃+* O(e⁻¹ Y)`, as an equivalence
of categories of modules. Its functor is `ModuleCat.restrictScalars (T.iso Y).toRingHom`. -/
noncomputable abbrev modEquiv (Y : Dᵒᵖ) :
    ModuleCat.{m} (O.obj (e.inverse.op.obj Y)) ≌ ModuleCat.{m} (O'.obj Y) :=
  ModuleCat.restrictScalarsEquivalenceOfRingEquiv (T.iso Y)

/-- The square of restrictions of scalars attached to `a' : V' ⟶ U'` in `Dᵒᵖ`: restricting along
`O'(U') ≃+* O(e⁻¹ U')` and then along `O'(V') ⟶ O'(U')` is restricting along
`O(e⁻¹ V') ⟶ O(e⁻¹ U')` and then along `O'(V') ≃+* O(e⁻¹ V')`, by naturality of the ring
isomorphisms. -/
noncomputable def restrictScalarsSquare {U' V' : Dᵒᵖ} (a' : V' ⟶ U') :
    (T.modEquiv.{m} U').functor ⋙ ModuleCat.restrictScalars.{m} (O'.map a').hom ≅
      ModuleCat.restrictScalars.{m} (O.map (e.inverse.op.map a')).hom ⋙
        (T.modEquiv.{m} V').functor :=
  (ModuleCat.restrictScalarsComp' (O'.map a').hom (T.iso U').toRingHom
      ((T.iso U').toRingHom.comp (O'.map a').hom) rfl).symm ≪≫
    ModuleCat.restrictScalarsComp' (T.iso V').toRingHom (O.map (e.inverse.op.map a')).hom
      ((T.iso U').toRingHom.comp (O'.map a').hom)
      (RingHom.ext fun x ↦ T.naturality a' x)

end Stacks.UniverseLift.RingTransport
