module

public import StacksFrontier.AlgebraicGeometry.PullbackSections.Stalk
public import StacksFrontier.AlgebraicGeometry.Smooth.LiftTorsor

/-!
# Germs at a point pulled back along a morphism landing in its generizations

Let `h : T ⟶ Y` be a morphism of schemes all of whose image points specialize to a point `y`
of `Y`. Every open neighbourhood of `y` then contains the whole image of `h`, so a function
defined near `y` pulls back to a global function on `T`, compatibly with restriction. This
gives a ring map `𝒪_{Y, y} ⟶ Γ(T, 𝒪_T)`, and morphisms `T ⟶ Y` landing in the generizations
of `y` are exactly the ring maps `𝒪_{Y, y} ⟶ Γ(T, 𝒪_T)`.

## Main definitions

* `AlgebraicGeometry.Scheme.Hom.stalkToΓOfSpecializes`: the ring map `𝒪_{Y, y} ⟶ Γ(T, 𝒪_T)`.

## Main results

* `AlgebraicGeometry.Scheme.Hom.germ_stalkToΓOfSpecializes`: on a germ it is the pullback.
* `AlgebraicGeometry.Scheme.Hom.stalkToΓOfSpecializes_comp` and
  `AlgebraicGeometry.Scheme.Hom.stalkToΓOfSpecializes_comp_right`: naturality in the source
  and in the target.
* `AlgebraicGeometry.Scheme.Hom.eq_of_stalkToΓOfSpecializes_eq` and
  `AlgebraicGeometry.Scheme.Hom.exists_stalkToΓOfSpecializes_eq`: the construction is a
  bijection from the morphisms landing in the generizations of `y` onto the ring maps.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace AlgebraicGeometry

namespace Scheme.Hom

variable {T Y : Scheme.{u}} (h : T ⟶ Y) (y : Y) (hy : ∀ t : T, h.base t ⤳ y)

/-- A morphism all of whose image points specialize to `y` maps into every open neighbourhood
of `y`. This generalizes `AlgebraicGeometry.Scheme.Hom.top_le_preimage_of_forall_base_eq`, where
every image point is `y` itself. -/
theorem top_le_preimage_of_specializes (hy' : ∀ t : T, h.base t ⤳ y) (U : Y.Opens)
    (hU : y ∈ U) : (⊤ : T.Opens) ≤ h ⁻¹ᵁ U := fun t _ ↦ (hy' t).mem_open U.isOpen hU

/-- The pullbacks along `h` of the functions on the open neighbourhoods of `y`, as a cocone on
the diagram computing the stalk `𝒪_{Y, y}`. -/
def stalkToΓOfSpecializesCocone : Cocone ((OpenNhds.inclusion y).op ⋙ Y.presheaf) where
  pt := Γ(T, ⊤)
  ι :=
    { app U := h.appLE U.unop.1 ⊤ (top_le_preimage_of_specializes h y hy U.unop.1 U.unop.2)
      naturality := fun _ _ _ ↦ (h.map_appLE _ _).trans (Category.comp_id _).symm }

/-- **The pullback of germs at `y` along a morphism landing in the generizations of `y`**: the
germ at `y` of a function on an open neighbourhood `U` of `y` goes to its pullback along `h`,
which is defined on the whole of `T` because `h` maps `T` into `U`. -/
def stalkToΓOfSpecializes : Y.presheaf.stalk y ⟶ Γ(T, ⊤) :=
  colimit.desc _ (stalkToΓOfSpecializesCocone h y hy)

/-- `AlgebraicGeometry.Scheme.Hom.stalkToΓOfSpecializes` on a germ is the pullback of the
function. -/
theorem germ_stalkToΓOfSpecializes (U : Y.Opens) (hU : y ∈ U) :
    Y.presheaf.germ U y hU ≫ h.stalkToΓOfSpecializes y hy =
      h.appLE U ⊤ (top_le_preimage_of_specializes h y hy U hU) :=
  colimit.ι_desc (stalkToΓOfSpecializesCocone h y hy) (op ⟨U, hU⟩)

/-- On the germ of a global function, `AlgebraicGeometry.Scheme.Hom.stalkToΓOfSpecializes` is
the pullback of global functions. -/
theorem germ_top_stalkToΓOfSpecializes :
    Y.presheaf.germ ⊤ y trivial ≫ h.stalkToΓOfSpecializes y hy = h.appTop :=
  (germ_stalkToΓOfSpecializes h y hy ⊤ trivial).trans h.appLE_eq_app

/-- `AlgebraicGeometry.Scheme.Hom.stalkToΓOfSpecializes` depends only on the morphism. -/
theorem stalkToΓOfSpecializes_congr {h₁ h₂ : T ⟶ Y} (e : h₁ = h₂)
    (hy₁ : ∀ t : T, h₁.base t ⤳ y) (hy₂ : ∀ t : T, h₂.base t ⤳ y) :
    h₁.stalkToΓOfSpecializes y hy₁ = h₂.stalkToΓOfSpecializes y hy₂ := by
  subst e
  rfl

/-- **Naturality in the source**: precomposing `h` with `φ : T' ⟶ T` composes the map with the
pullback `φ^# : Γ(T, 𝒪_T) ⟶ Γ(T', 𝒪_{T'})`. -/
theorem stalkToΓOfSpecializes_comp {T' : Scheme.{u}} (φ : T' ⟶ T)
    (hy' : ∀ t : T', (φ ≫ h).base t ⤳ y) :
    (φ ≫ h).stalkToΓOfSpecializes y hy' = h.stalkToΓOfSpecializes y hy ≫ φ.appTop := by
  refine TopCat.Presheaf.stalk_hom_ext _ fun U hU ↦ ?_
  have htop : φ.appTop = φ.appLE ⊤ ⊤ (by simp) := φ.appLE_eq_app.symm
  rw [germ_stalkToΓOfSpecializes (φ ≫ h) y hy', ← Category.assoc,
    germ_stalkToΓOfSpecializes h y hy, htop]
  exact (Scheme.Hom.appLE_comp_appLE φ h U ⊤ ⊤ _ _).symm

/-- **Naturality in the target**: postcomposing `h` with `f : Y ⟶ Y'` precomposes the map with
the map of stalks `𝒪_{Y', f y} ⟶ 𝒪_{Y, y}`. -/
theorem stalkToΓOfSpecializes_comp_right {Y' : Scheme.{u}} (f : Y ⟶ Y')
    (hy' : ∀ t : T, (h ≫ f).base t ⤳ f.base y) :
    (h ≫ f).stalkToΓOfSpecializes (f.base y) hy' =
      f.stalkMap y ≫ h.stalkToΓOfSpecializes y hy := by
  refine TopCat.Presheaf.stalk_hom_ext _ fun U hU ↦ ?_
  rw [germ_stalkToΓOfSpecializes, Scheme.Hom.germ_stalkMap_assoc,
    germ_stalkToΓOfSpecializes h y hy (f ⁻¹ᵁ U) hU, Scheme.Hom.comp_appLE]

/-- **Morphisms landing in the generizations of `y` are determined by their map on the
stalk.** -/
theorem eq_of_stalkToΓOfSpecializes_eq {h₁ h₂ : T ⟶ Y} (hy₁ : ∀ t : T, h₁.base t ⤳ y)
    (hy₂ : ∀ t : T, h₂.base t ⤳ y)
    (e : h₁.stalkToΓOfSpecializes y hy₁ = h₂.stalkToΓOfSpecializes y hy₂) : h₁ = h₂ := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hyU, -⟩ :=
    (isBasis_affineOpens Y).exists_subset_of_mem_open (Set.mem_univ y) isOpen_univ
  refine Stacks.Smooth.hom_ext_of_appLE hU (top_le_preimage_of_specializes h₁ y hy₁ U hyU)
    (top_le_preimage_of_specializes h₂ y hy₂ U hyU) ?_
  rw [← germ_stalkToΓOfSpecializes h₁ y hy₁ U hyU, ← germ_stalkToΓOfSpecializes h₂ y hy₂ U hyU,
    e]

/-- The morphism `T ⟶ Spec Γ(T, 𝒪_T) ⟶ Spec 𝒪_{Y, y} ⟶ Y` of a ring map `𝒪_{Y, y} ⟶ Γ(T, 𝒪_T)`
lands in the generizations of `y`. -/
theorem specializes_toSpecΓ_specMap_fromSpecStalk (φ : Y.presheaf.stalk y ⟶ Γ(T, ⊤)) (t : T) :
    (T.toSpecΓ ≫ Spec.map φ ≫ Y.fromSpecStalk y).base t ⤳ y := by
  have hmem : (T.toSpecΓ ≫ Spec.map φ ≫ Y.fromSpecStalk y).base t ∈
      Set.range (Y.fromSpecStalk y).base := ⟨_, (Scheme.Hom.comp_apply _ _ _).symm.trans
        (congrArg (fun g : T ⟶ Y ↦ g.base t) (Category.assoc _ _ _))⟩
  rwa [Scheme.range_fromSpecStalk] at hmem

/-- `AlgebraicGeometry.Scheme.Hom.stalkToΓOfSpecializes` of the morphism
`T ⟶ Spec Γ(T, 𝒪_T) ⟶ Spec 𝒪_{Y, y} ⟶ Y` of a ring map `φ` is `φ`. -/
theorem stalkToΓOfSpecializes_toSpecΓ_specMap_fromSpecStalk
    (φ : Y.presheaf.stalk y ⟶ Γ(T, ⊤)) :
    (T.toSpecΓ ≫ Spec.map φ ≫ Y.fromSpecStalk y).stalkToΓOfSpecializes y
      (specializes_toSpecΓ_specMap_fromSpecStalk y φ) = φ := by
  refine TopCat.Presheaf.stalk_hom_ext _ fun U hyU ↦ ?_
  have e₁ : (⊤ : (Spec Γ(T, ⊤)).Opens) ≤ (Spec.map φ ≫ Y.fromSpecStalk y) ⁻¹ᵁ U := fun p _ ↦
    le_preimage_fromSpecStalk_of_mem y U hyU (Set.mem_univ ((Spec.map φ).base p))
  have e₂ : (⊤ : T.Opens) ≤ T.toSpecΓ ⁻¹ᵁ ⊤ := le_top
  have e₃ : (⊤ : (Spec Γ(T, ⊤)).Opens) ≤ Spec.map φ ⁻¹ᵁ ⊤ := le_top
  rw [germ_stalkToΓOfSpecializes, ← Scheme.Hom.appLE_comp_appLE _ _ U ⊤ ⊤ e₁ e₂,
    ← Scheme.Hom.appLE_comp_appLE _ _ U ⊤ ⊤ (le_preimage_fromSpecStalk_of_mem y U hyU) e₃,
    fromSpecStalk_appLE_top, Stacks.Smooth.appLE_top_top, Stacks.Smooth.appLE_top_top,
    Scheme.toSpecΓ_appTop, Category.assoc, Category.assoc,
    ← Scheme.ΓSpecIso_inv_naturality_assoc, Iso.inv_hom_id, Category.comp_id]

/-- **Every ring map `𝒪_{Y, y} ⟶ Γ(T, 𝒪_T)` comes from a morphism landing in the generizations
of `y`.** -/
theorem exists_stalkToΓOfSpecializes_eq (φ : Y.presheaf.stalk y ⟶ Γ(T, ⊤)) :
    ∃ (h : T ⟶ Y) (hy : ∀ t : T, h.base t ⤳ y), h.stalkToΓOfSpecializes y hy = φ :=
  ⟨_, _, stalkToΓOfSpecializes_toSpecΓ_specMap_fromSpecStalk y φ⟩

end Scheme.Hom

end AlgebraicGeometry

end
