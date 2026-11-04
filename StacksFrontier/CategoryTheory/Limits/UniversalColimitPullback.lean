module

public import Mathlib.CategoryTheory.Limits.VanKampen
public import StacksFrontier.CategoryTheory.Limits.UniqueLiftingAlongPullback
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Base change of a universal colimit

Let `c` be a cocone over a diagram `G : I ⥤ C` in a category with pullbacks, and let
`g : X ⟶ c.pt` be a morphism into its vertex. Base changing the members of `c` along `g` gives
a diagram `j ↦ G j ×_{c.pt} X` with a cocone of vertex `X`. When `c` is a universal colimit
(`CategoryTheory.Limits.IsUniversalColimit`), that cocone is again a colimit.

Consequently a morphism `α : X ⟶ Y` over `c.pt` is an isomorphism as soon as each of its base
changes along the members of `c` is one: it is then the morphism of colimits induced by a natural
isomorphism of diagrams.

## Main definitions

* `CategoryTheory.Limits.Cocone.pullbackDiagram`: the diagram `j ↦ G j ×_{c.pt} X`.
* `CategoryTheory.Limits.Cocone.pullbackCocone`: its cocone of vertex `X`.

## Main results

* `CategoryTheory.Limits.IsUniversalColimit.nonempty_isColimit_pullbackCocone`: the base change
  of a universal colimit is a colimit.
* `CategoryTheory.Limits.IsUniversalColimit.isIso_of_isIso_pullbackMap`: a morphism over the
  vertex of a universal colimit is an isomorphism when all its base changes along the members
  of the colimit are.
-/

@[expose] public section

open CategoryTheory

namespace CategoryTheory.Limits

universe v u w w'

section General

variable {C : Type u} [Category.{v} C] {I : Type w} [Category.{w'} I] [HasPullbacks C]
  {G : I ⥤ C}

/-- The member at `j` of a cocone, as a morphism into its vertex. -/
abbrev Cocone.leg (c : Cocone G) (j : I) : G.obj j ⟶ c.pt := c.ι.app j

/-- The diagram of base changes of the members of a cocone `c` along a morphism `g` into its
vertex. -/
@[simps, sga "4 I 2.5"]
noncomputable abbrev Cocone.pullbackDiagram (c : Cocone G) {X : C} (g : X ⟶ c.pt) : I ⥤ C where
  obj j := pullback (c.leg j) g
  map {j k} f := pullback.map (c.leg j) g (c.leg k) g (G.map f) (𝟙 X) (𝟙 c.pt)
    (by simp) (by simp)
  map_id j := by
    apply pullback.hom_ext <;> simp [pullback.map, pullback.lift_fst, pullback.lift_snd,
      pullback.lift_fst_assoc, pullback.lift_snd_assoc]
  map_comp f f' := by
    apply pullback.hom_ext <;> simp [pullback.map, pullback.lift_fst, pullback.lift_snd,
      pullback.lift_fst_assoc, pullback.lift_snd_assoc]

/-- The cocone of vertex `X` over the diagram of base changes of the members of `c` along `g`. -/
@[simps]
noncomputable def Cocone.pullbackCocone (c : Cocone G) {X : C} (g : X ⟶ c.pt) :
    Cocone (c.pullbackDiagram g) where
  pt := X
  ι :=
    { app := fun j ↦ pullback.snd (c.leg j) g
      naturality := fun j k f ↦ by
        simp [pullback.map, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc,
          pullback.lift_snd_assoc] }

/-- The first projections of the base changes, a morphism of diagrams to `G`. -/
@[simps]
noncomputable def Cocone.pullbackFst (c : Cocone G) {X : C} (g : X ⟶ c.pt) :
    c.pullbackDiagram g ⟶ G where
  app j := pullback.fst (c.leg j) g
  naturality j k f := by
    simp [pullback.map, pullback.lift_fst, pullback.lift_snd,
      pullback.lift_fst_assoc, pullback.lift_snd_assoc]

/-- The transition squares of the diagram of base changes are cartesian. -/
@[ega "I 3.3.9" "Objectwise transitivity"]
theorem Cocone.isPullback_pullbackDiagram_map (c : Cocone G) {X : C} (g : X ⟶ c.pt)
    {j k : I} (f : j ⟶ k) :
    IsPullback ((c.pullbackDiagram g).map f) (pullback.fst (c.leg j) g)
      (pullback.fst (c.leg k) g) (G.map f) := by
  show IsPullback (pullback.map (c.leg j) g (c.leg k) g (G.map f) (𝟙 X) (𝟙 c.pt)
    (by simp) (by simp)) (pullback.fst (c.leg j) g) (pullback.fst (c.leg k) g) (G.map f)
  have h₁ : pullback.map (c.leg j) g (c.leg k) g (G.map f) (𝟙 X) (𝟙 c.pt)
      (by simp) (by simp) ≫ pullback.snd (c.leg k) g = pullback.snd (c.leg j) g := by
    simp [pullback.map, pullback.lift_fst, pullback.lift_snd,
      pullback.lift_fst_assoc, pullback.lift_snd_assoc]
  have hout : IsPullback (pullback.map (c.leg j) g (c.leg k) g (G.map f) (𝟙 X) (𝟙 c.pt)
      (by simp) (by simp) ≫ pullback.snd (c.leg k) g) (pullback.fst (c.leg j) g) g
      (G.map f ≫ c.leg k) := by
    rw [h₁, c.w f]
    exact (IsPullback.of_hasPullback (c.leg j) g).flip
  exact IsPullback.of_right hout (pullback.lift_fst _ _ _)
    (IsPullback.of_hasPullback (c.leg k) g).flip

/-- The transition maps of the diagram of base changes lie over the transition maps of `G`. -/
@[reassoc]
theorem Cocone.pullbackDiagram_map_fst (c : Cocone G) {X : C} (g : X ⟶ c.pt)
    {j k : I} (f : j ⟶ k) :
    (c.pullbackDiagram g).map f ≫ pullback.fst (c.leg k) g =
      pullback.fst (c.leg j) g ≫ G.map f :=
  (c.isPullback_pullbackDiagram_map g f).w

/-- **The base change of a universal colimit is a colimit.** If `c` is a universal colimit and
`g : X ⟶ c.pt`, then `X` is the colimit of the base changes `G j ×_{c.pt} X`. -/
theorem IsUniversalColimit.nonempty_isColimit_pullbackCocone {c : Cocone G}
    (hc : IsUniversalColimit c) {X : C} (g : X ⟶ c.pt) :
    Nonempty (IsColimit (c.pullbackCocone g)) := by
  refine hc (c.pullbackCocone g) (c.pullbackFst g) g ?_
    (fun _ _ f ↦ c.isPullback_pullbackDiagram_map g f)
    fun j ↦ (IsPullback.of_hasPullback (c.leg j) g).flip
  ext j
  simp [pullback.condition, Cocone.pullbackCocone, Cocone.pullbackFst]

/-- **Isomorphisms are detected after base change to the members of a universal colimit.** Let
`c` be a universal colimit and let `α : X ⟶ Y` be a morphism over `c.pt`. If the morphism
`G j ×_{c.pt} X ⟶ G j ×_{c.pt} Y` induced by `α` is an isomorphism for every `j`, then `α` is an
isomorphism. -/
theorem IsUniversalColimit.isIso_of_isIso_pullbackMap {c : Cocone G}
    (hc : IsUniversalColimit c) {X Y : C} (x : X ⟶ c.pt) (y : Y ⟶ c.pt) (α : X ⟶ Y)
    (hα : α ≫ y = x)
    (h : ∀ j, IsIso (pullback.map (c.leg j) x (c.leg j) y (𝟙 _) α (𝟙 c.pt) (by simp)
      (by simp [hα]))) :
    IsIso α := by
  obtain ⟨hx⟩ := IsUniversalColimit.nonempty_isColimit_pullbackCocone hc x
  obtain ⟨hy⟩ := IsUniversalColimit.nonempty_isColimit_pullbackCocone hc y
  let θ : c.pullbackDiagram x ⟶ c.pullbackDiagram y :=
    { app := fun j ↦ pullback.map (c.leg j) x (c.leg j) y (𝟙 _) α (𝟙 c.pt) (by simp)
        (by simp [hα])
      naturality := fun j k f ↦ by
        apply pullback.hom_ext <;> simp only [pullback.map,
          Category.assoc, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc,
          pullback.lift_snd_assoc, Category.comp_id, Category.id_comp] }
  have : ∀ j, IsIso (θ.app j) := h
  have : IsIso θ := NatIso.isIso_of_isIso_app θ
  have key : (IsColimit.coconePointsIsoOfNatIso hx hy (asIso θ)).hom = α :=
    hx.hom_ext fun j ↦ (IsColimit.comp_coconePointsIsoOfNatIso_hom hx hy (asIso θ) j).trans
      (pullback.lift_snd _ _ _)
  exact key ▸ Iso.isIso_hom _

/-- **Two objects over the vertex of a universal colimit are isomorphic when their base changes
are, compatibly.** If `c` is a universal colimit and the diagrams of base changes of
`x : X ⟶ c.pt` and `y : Y ⟶ c.pt` are isomorphic over `G`, then `X ≅ Y` over `c.pt`. -/
theorem IsUniversalColimit.exists_iso_of_pullbackDiagram_iso {c : Cocone G}
    (hc : IsUniversalColimit c) {X Y : C} (x : X ⟶ c.pt) (y : Y ⟶ c.pt)
    (Θ : c.pullbackDiagram x ≅ c.pullbackDiagram y)
    (hΘ : ∀ j, Θ.hom.app j ≫ pullback.fst (c.leg j) y = pullback.fst (c.leg j) x) :
    ∃ e : X ≅ Y, e.hom ≫ y = x := by
  obtain ⟨hx⟩ := IsUniversalColimit.nonempty_isColimit_pullbackCocone hc x
  obtain ⟨hy⟩ := IsUniversalColimit.nonempty_isColimit_pullbackCocone hc y
  refine ⟨IsColimit.coconePointsIsoOfNatIso hx hy Θ, hx.hom_ext fun j ↦ ?_⟩
  refine (IsColimit.comp_coconePointsIsoOfNatIso_hom_assoc hx hy Θ j y).trans ?_
  show Θ.hom.app j ≫ pullback.snd (c.leg j) y ≫ y = pullback.snd (c.leg j) x ≫ x
  rw [← pullback.condition, ← Category.assoc, hΘ, pullback.condition]

end General

section Preorder

variable {C : Type u} [Category.{v} C] {I : Type w} [Preorder I] [HasPullbacks C]
  {G : I ⥤ C}

/-- **Unique lifting of morphisms of base changes from a stage `j₀`.** For `x : X ⟶ c.pt` and
`y : Y ⟶ c.pt`, every morphism `X_{j₀} ⟶ Y_{j₀}` of base changes over `G j₀` extends uniquely to
a morphism `X_j ⟶ Y_j` over `G j` compatible with the transition maps, for every `j ≥ j₀`. -/
def Cocone.LiftsFrom (c : Cocone G) (j₀ : I) {X Y : C} (x : X ⟶ c.pt)
    (y : Y ⟶ c.pt) : Prop :=
  ∀ (j : I) (f : j₀ ⟶ j) (φ : pullback (c.leg j₀) x ⟶ pullback (c.leg j₀) y),
    φ ≫ pullback.fst (c.leg j₀) y = pullback.fst (c.leg j₀) x →
    ∃! ψ : pullback (c.leg j) x ⟶ pullback (c.leg j) y,
      ψ ≫ pullback.fst (c.leg j) y = pullback.fst (c.leg j) x ∧
        (c.pullbackDiagram x).map f ≫ ψ = φ ≫ (c.pullbackDiagram y).map f

/-- Unique lifting along the transition maps of `G` out of `j₀` gives `Cocone.LiftsFrom`. -/
theorem Cocone.liftsFrom_of_uniqueLiftingAlong (c : Cocone G) (j₀ : I) {X Y : C}
    (x : X ⟶ c.pt) (y : Y ⟶ c.pt)
    (h : ∀ (j : I) (f : j₀ ⟶ j),
      UniqueLiftingAlong (G.map f) (pullback.fst (c.leg j) x) (pullback.fst (c.leg j) y)) :
    c.LiftsFrom j₀ x y := fun j f φ hφ ↦
  h j f _ _ _ _ (c.isPullback_pullbackDiagram_map x f) (c.isPullback_pullbackDiagram_map y f)
    φ hφ

/-- An endomorphism of a base change over `G j` compatible with the identity at `j₀` is the
identity. -/
theorem Cocone.LiftsFrom.eq_id {c : Cocone G} {j₀ : I} {Z : C} {z : Z ⟶ c.pt}
    (hzz : c.LiftsFrom j₀ z z) {j : I} (f : j₀ ⟶ j)
    {ω : pullback (c.leg j) z ⟶ pullback (c.leg j) z}
    (hω₁ : ω ≫ pullback.fst (c.leg j) z = pullback.fst (c.leg j) z)
    (hω₂ : (c.pullbackDiagram z).map f ≫ ω = (c.pullbackDiagram z).map f) : ω = 𝟙 _ :=
  (hzz j f (𝟙 _) (Category.id_comp _)).unique ⟨hω₁, by rw [hω₂, Category.id_comp]⟩
    ⟨Category.id_comp _, by simp⟩

/-- If `ψ` and `χ` lift mutually inverse morphisms `θ`, `θ'` at `j₀`, then `ψ ≫ χ` is the
identity. -/
private theorem comp_eq_id_of_liftsFrom {c : Cocone G} {j₀ j : I} {X Y : C} {x : X ⟶ c.pt}
    {y : Y ⟶ c.pt} (hxx : c.LiftsFrom j₀ x x) (f : j₀ ⟶ j)
    {θ : pullback (c.leg j₀) x ⟶ pullback (c.leg j₀) y}
    {θ' : pullback (c.leg j₀) y ⟶ pullback (c.leg j₀) x} (hθ : θ ≫ θ' = 𝟙 _)
    {ψ : pullback (c.leg j) x ⟶ pullback (c.leg j) y}
    {χ : pullback (c.leg j) y ⟶ pullback (c.leg j) x}
    (hψ : ψ ≫ pullback.fst (c.leg j) y = pullback.fst (c.leg j) x ∧
      (c.pullbackDiagram x).map f ≫ ψ = θ ≫ (c.pullbackDiagram y).map f)
    (hχ : χ ≫ pullback.fst (c.leg j) x = pullback.fst (c.leg j) y ∧
      (c.pullbackDiagram y).map f ≫ χ = θ' ≫ (c.pullbackDiagram x).map f) :
    ψ ≫ χ = 𝟙 _ :=
  hxx.eq_id f (by rw [Category.assoc, hχ.1, hψ.1])
    (by rw [← Category.assoc, hψ.2, Category.assoc, hχ.2, ← Category.assoc, hθ, Category.id_comp])

/-- **Gluing an isomorphism of base changes from one stage.** Let `c` be a universal colimit
over a preorder with a least element `j₀`, and let `x : X ⟶ c.pt`, `y : Y ⟶ c.pt` be such that
morphisms of base changes between any two of `x`, `y` lift uniquely from the stage `j₀`. Then an
isomorphism `X_{j₀} ≅ Y_{j₀}` over `G j₀` of the base changes at `j₀` gives an isomorphism
`X ≅ Y` over `c.pt`. -/
theorem IsUniversalColimit.exists_iso_of_liftsFrom {c : Cocone G}
    (hc : IsUniversalColimit c) (j₀ : I) (h₀ : ∀ j, j₀ ≤ j) {X Y : C} (x : X ⟶ c.pt)
    (y : Y ⟶ c.pt) (hxy : c.LiftsFrom j₀ x y) (hyx : c.LiftsFrom j₀ y x)
    (hxx : c.LiftsFrom j₀ x x) (hyy : c.LiftsFrom j₀ y y)
    (θ₀ : pullback (c.leg j₀) x ≅ pullback (c.leg j₀) y)
    (hθ₀ : θ₀.hom ≫ pullback.fst (c.leg j₀) y = pullback.fst (c.leg j₀) x) :
    ∃ e : X ≅ Y, e.hom ≫ y = x := by
  let f₀ : ∀ j, j₀ ⟶ j := fun j ↦ homOfLE (h₀ j)
  choose ψ hψ using fun j ↦ (hxy j (f₀ j) θ₀.hom hθ₀).exists
  choose χ hχ using fun j ↦ (hyx j (f₀ j) θ₀.inv (θ₀.inv_comp_eq.2 hθ₀.symm)).exists
  -- the two families are mutually inverse, by uniqueness of the lift of an identity
  have hψχ : ∀ j, ψ j ≫ χ j = 𝟙 _ := fun j ↦
    comp_eq_id_of_liftsFrom hxx (f₀ j) θ₀.hom_inv_id (hψ j) (hχ j)
  have hχψ : ∀ j, χ j ≫ ψ j = 𝟙 _ := fun j ↦
    comp_eq_id_of_liftsFrom hyy (f₀ j) θ₀.inv_hom_id (hχ j) (hψ j)
  -- naturality, by uniqueness of the lift at the source of each transition map
  have hnat : ∀ {j k : I} (f : j ⟶ k),
      (c.pullbackDiagram x).map f ≫ ψ k = ψ j ≫ (c.pullbackDiagram y).map f := by
    intro j k f
    have sq := c.isPullback_pullbackDiagram_map y f
    have hw : ((c.pullbackDiagram x).map f ≫ ψ k) ≫ pullback.fst (c.leg k) y =
        pullback.fst (c.leg j) x ≫ G.map f := by
      rw [Category.assoc, (hψ k).1, c.pullbackDiagram_map_fst]
    let ω := sq.lift _ _ hw
    have hω₁ : ω ≫ pullback.fst (c.leg j) y = pullback.fst (c.leg j) x := sq.lift_snd _ _ hw
    have hω₂ : ω ≫ (c.pullbackDiagram y).map f = (c.pullbackDiagram x).map f ≫ ψ k :=
      sq.lift_fst _ _ hw
    have hf₀ : f₀ k = f₀ j ≫ f := Subsingleton.elim _ _
    have hω₃ : (c.pullbackDiagram x).map (f₀ j) ≫ ω =
        θ₀.hom ≫ (c.pullbackDiagram y).map (f₀ j) := by
      refine sq.hom_ext ?_ ?_
      · rw [Category.assoc, hω₂, Category.assoc, ← Category.assoc _ _ (ψ k),
          ← Functor.map_comp, ← hf₀, (hψ k).2, hf₀, Functor.map_comp]
      · rw [Category.assoc, hω₁, Category.assoc, c.pullbackDiagram_map_fst,
          c.pullbackDiagram_map_fst, ← Category.assoc, hθ₀]
    have hωψ : ω = ψ j := (hxy j (f₀ j) θ₀.hom hθ₀).unique ⟨hω₁, hω₃⟩ (hψ j)
    rw [← hω₂, hωψ]
  exact IsUniversalColimit.exists_iso_of_pullbackDiagram_iso hc x y
    (NatIso.ofComponents (fun j ↦ ⟨ψ j, χ j, hψχ j, hχψ j⟩) hnat) fun j ↦ (hψ j).1

end Preorder

end CategoryTheory.Limits

end
