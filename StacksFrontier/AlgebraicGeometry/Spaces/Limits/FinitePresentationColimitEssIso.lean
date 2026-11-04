module

public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.FinitePresentationLocalRingGlueing

/-!
# The isomorphism condition of a finite-presentation colimit follows from the other two

`AlgebraicGeometry.FinitePresentationSpacesOver.IsFinitePresentationColimit` carries four
conditions, and its own docstring records that the third, `essIso`, follows from `full` and
`faithful` by a cofiltered argument but is carried separately. This file proves that
implication. It is needed because Stacks 07SK has three clauses — essential surjectivity,
fullness, faithfulness — and no clause for isomorphisms, so a construction of
`IsFinitePresentationColimit` from the clauses of Stacks 07SK has to produce `essIso` from the
other two.

The argument is the usual one. An isomorphism `Θ` over `M` has both `Θ.hom` and `Θ.inv` coming
from stages, by fullness; a common stage below both receives the two morphisms, and there their
composites base change to the identity over `M`, so by faithfulness they *are* the identity at a
yet later stage. At that stage the morphism coming from `Θ.hom` is an isomorphism.

The one thing to be careful about is that a morphism found at a stage does not base change to a
morphism at a later stage on the nose: the base change along a composite is only isomorphic to
the iterated base change. Every transport below is therefore conjugated by
`AlgebraicGeometry.FinitePresentationSpacesOver.baseChangeFactorIso`, and the statement that a
transported morphism still represents the given morphism over `M` is
`AlgebraicGeometry.FinitePresentationSpacesOver.representsFactor_trans` of
`StacksFrontier.AlgebraicGeometry.Spaces.Limits.FinitePresentationLocalRingGlueing`, which exists
for exactly this purpose.

## Main results

* `AlgebraicGeometry.FinitePresentationSpacesOver.essIso_of_full_of_faithful`: the `essIso`
  condition, from the `full` and `faithful` conditions.

## References

* [Stacks Project, Tag 07SK](https://stacks.math.columbia.edu/tag/07SK)
* [Stacks Project, Tag 0E91](https://stacks.math.columbia.edu/tag/0E91)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.FinitePresentationSpacesOver

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {I : Type u} [Category.{u} I] [IsCofiltered I] {W : I ⥤ BigFppfOver B S hS}
  {M : BigFppfOver B S hS} (p : (i : I) → (M ⟶ W.obj i))
  (hp : ∀ {i j : I} (e : j ⟶ i), p j ≫ W.map e = p i)

/-- The conjugated base change of a morphism of a stage to a later stage: the base change along
the transition, read through the comparison of the factorisation. -/
noncomputable def transportStage {i j : I} (e : j ⟶ i) {k : I} (u : k ⟶ j) {ue : k ⟶ i}
    (hue : u ≫ e = ue) {X Y : FinitePresentationSpacesOver B S hS (W.obj i)}
    (g : (baseChange B S hS (W.map e)).obj X ⟶ (baseChange B S hS (W.map e)).obj Y) :
    (baseChange B S hS (W.map ue)).obj X ⟶ (baseChange B S hS (W.map ue)).obj Y :=
  (baseChangeFactorIso B S hS
      (show W.map u ≫ W.map e = W.map ue by rw [← W.map_comp, hue])).hom.app X ≫
    (baseChange B S hS (W.map u)).map g ≫
      (baseChangeFactorIso B S hS
        (show W.map u ≫ W.map e = W.map ue by rw [← W.map_comp, hue])).inv.app Y

omit [IsCofiltered I] in
/-- Transport to a later stage is functorial on composites. -/
theorem transportStage_comp {i j : I} (e : j ⟶ i) {k : I} (u : k ⟶ j) {ue : k ⟶ i}
    (hue : u ≫ e = ue) {X Y Z : FinitePresentationSpacesOver B S hS (W.obj i)}
    (g : (baseChange B S hS (W.map e)).obj X ⟶ (baseChange B S hS (W.map e)).obj Y)
    (g' : (baseChange B S hS (W.map e)).obj Y ⟶ (baseChange B S hS (W.map e)).obj Z) :
    transportStage B S hS e u hue (g ≫ g') =
      transportStage B S hS e u hue g ≫ transportStage B S hS e u hue g' := by
  simp only [transportStage, Functor.map_comp, Category.assoc, Iso.inv_hom_id_app_assoc]

omit [IsCofiltered I] in
/-- Two morphisms of a stage with the same base change along the transition have the same
transport to the later stage. -/
theorem transportStage_congr {i j : I} (e : j ⟶ i) {k : I} (u : k ⟶ j) {ue : k ⟶ i}
    (hue : u ≫ e = ue) {X Y : FinitePresentationSpacesOver B S hS (W.obj i)}
    {g g' : (baseChange B S hS (W.map e)).obj X ⟶ (baseChange B S hS (W.map e)).obj Y}
    (hgg : (baseChange B S hS (W.map u)).map g = (baseChange B S hS (W.map u)).map g') :
    transportStage B S hS e u hue g = transportStage B S hS e u hue g' := by
  simp only [transportStage, hgg]

omit [IsCofiltered I] in
/-- Transport to a later stage preserves identities. -/
theorem transportStage_id {i j : I} (e : j ⟶ i) {k : I} (u : k ⟶ j) {ue : k ⟶ i}
    (hue : u ≫ e = ue) (X : FinitePresentationSpacesOver B S hS (W.obj i)) :
    transportStage B S hS e u hue (𝟙 ((baseChange B S hS (W.map e)).obj X)) =
      𝟙 ((baseChange B S hS (W.map ue)).obj X) := by
  simp [transportStage]

include hp in
omit [IsCofiltered I] in
/-- **A morphism transported to a later stage still represents the given morphism over `M`.**
This is `AlgebraicGeometry.FinitePresentationSpacesOver.representsFactor_trans` read through
`AlgebraicGeometry.FinitePresentationSpacesOver.transportStage`. -/
theorem represents_transportStage {i j : I} (e : j ⟶ i) {k : I} (u : k ⟶ j) {ue : k ⟶ i}
    (hue : u ≫ e = ue) {X Y : FinitePresentationSpacesOver B S hS (W.obj i)}
    {m : (baseChange B S hS (p i)).obj X ⟶ (baseChange B S hS (p i)).obj Y}
    {g : (baseChange B S hS (W.map e)).obj X ⟶ (baseChange B S hS (W.map e)).obj Y}
    (hg : (baseChangeFactorIso B S hS (hp e)).hom.app X ≫ (baseChange B S hS (p j)).map g =
      m ≫ (baseChangeFactorIso B S hS (hp e)).hom.app Y) :
    (baseChangeFactorIso B S hS (hp ue)).hom.app X ≫
        (baseChange B S hS (p k)).map (transportStage B S hS e u hue g) =
      m ≫ (baseChangeFactorIso B S hS (hp ue)).hom.app Y :=
  representsFactor_trans B S hS (hp u)
    (show W.map u ≫ W.map e = W.map ue by rw [← W.map_comp, hue]) (hp ue) (hp e) hg

/-- Two transported morphisms representing mutually inverse morphisms over `M` compose to
something with the same base change as the identity. -/
private theorem map_comp_eq_id_of_represents {I : Type u} [Category.{u} I]
    {W : I ⥤ BigFppfOver B S hS} {M : BigFppfOver B S hS} (p : (i : I) → (M ⟶ W.obj i))
    (hp : ∀ {i j : I} (e : j ⟶ i), p j ≫ W.map e = p i) {i k : I} (ue : k ⟶ i)
    {X Y : FinitePresentationSpacesOver B S hS (W.obj i)}
    (Θ : (baseChange B S hS (p i)).obj X ≅ (baseChange B S hS (p i)).obj Y)
    {c : (baseChange B S hS (W.map ue)).obj X ⟶ (baseChange B S hS (W.map ue)).obj Y}
    {d : (baseChange B S hS (W.map ue)).obj Y ⟶ (baseChange B S hS (W.map ue)).obj X}
    (hc : (baseChangeFactorIso B S hS (hp ue)).hom.app X ≫ (baseChange B S hS (p k)).map c =
      Θ.hom ≫ (baseChangeFactorIso B S hS (hp ue)).hom.app Y)
    (hd : (baseChangeFactorIso B S hS (hp ue)).hom.app Y ≫ (baseChange B S hS (p k)).map d =
      Θ.inv ≫ (baseChangeFactorIso B S hS (hp ue)).hom.app X) :
    (baseChange B S hS (p k)).map (c ≫ d) = (baseChange B S hS (p k)).map (𝟙 _) := by
  refine (Iso.cancel_iso_hom_left
    (Iso.app (baseChangeFactorIso B S hS (hp ue)) X) _ _).mp ?_
  simp only [Functor.map_comp, Iso.app_hom]
  rw [reassoc_of% hc, hd, Iso.hom_inv_id_assoc]
  simp

/-- Equal base changes along `r` remain equal along any composite `s ≫ r`. -/
private theorem map_eq_of_map_comp_eq {I : Type u} [Category.{u} I]
    {W : I ⥤ BigFppfOver B S hS} {k m₁ m : I} (r : m₁ ⟶ k) (s : m ⟶ m₁) {rs : m ⟶ k}
    (hs : s ≫ r = rs) {X Y : FinitePresentationSpacesOver B S hS (W.obj k)} {f g : X ⟶ Y}
    (h : (baseChange B S hS (W.map r)).map f = (baseChange B S hS (W.map r)).map g) :
    (baseChange B S hS (W.map rs)).map f = (baseChange B S hS (W.map rs)).map g :=
  map_eq_of_natIso (baseChangeFactorIso B S hS
    (show W.map s ≫ W.map r = W.map rs by rw [← W.map_comp, hs])).symm
    (congrArg ((baseChange B S hS (W.map s)).map) h)

include hp in
/-- **The isomorphism condition follows from fullness and faithfulness.** Both `Θ.hom` and
`Θ.inv` come from stages; at a common stage below both, their two composites base change to the
identity over `M`, so faithfulness makes them the identity at a yet later stage, where the
morphism coming from `Θ.hom` is therefore an isomorphism. -/
theorem essIso_of_full_of_faithful
    (hfull : ∀ (i : I) (X Y : FinitePresentationSpacesOver B S hS (W.obj i))
      (h : (baseChange B S hS (p i)).obj X ⟶ (baseChange B S hS (p i)).obj Y),
      ∃ (j : I) (e : j ⟶ i) (h' : (baseChange B S hS (W.map e)).obj X ⟶
        (baseChange B S hS (W.map e)).obj Y),
        (baseChangeFactorIso B S hS (hp e)).hom.app X ≫ (baseChange B S hS (p j)).map h' =
          h ≫ (baseChangeFactorIso B S hS (hp e)).hom.app Y)
    (hfaithful : ∀ (i : I) (X Y : FinitePresentationSpacesOver B S hS (W.obj i)) (f g : X ⟶ Y),
      (baseChange B S hS (p i)).map f = (baseChange B S hS (p i)).map g →
      ∃ (j : I) (e : j ⟶ i),
        (baseChange B S hS (W.map e)).map f = (baseChange B S hS (W.map e)).map g)
    (i : I) (X Y : FinitePresentationSpacesOver B S hS (W.obj i))
    (Θ : (baseChange B S hS (p i)).obj X ≅ (baseChange B S hS (p i)).obj Y) :
    ∃ (j : I) (e : j ⟶ i) (Θ' : (baseChange B S hS (W.map e)).obj X ≅
      (baseChange B S hS (W.map e)).obj Y),
      (baseChangeFactorIso B S hS (hp e)).hom.app X ≫ (baseChange B S hS (p j)).map Θ'.hom =
        Θ.hom ≫ (baseChangeFactorIso B S hS (hp e)).hom.app Y := by
  obtain ⟨j₁, e₁, a, ha⟩ := hfull i X Y Θ.hom
  obtain ⟨j₂, e₂, b, hb⟩ := hfull i Y X Θ.inv
  -- a common stage below both, on which the two transitions to `i` agree
  obtain ⟨k₀, u₀, v₀, -⟩ := IsCofilteredOrEmpty.cone_objs j₁ j₂
  obtain ⟨k, w, hw⟩ := IsCofilteredOrEmpty.cone_maps (u₀ ≫ e₁) (v₀ ≫ e₂)
  have hu : (w ≫ u₀) ≫ e₁ = w ≫ u₀ ≫ e₁ := Category.assoc _ _ _
  have hv : (w ≫ v₀) ≫ e₂ = w ≫ u₀ ≫ e₁ := by rw [Category.assoc]; exact hw.symm
  have ha' := represents_transportStage B S hS p hp e₁ (w ≫ u₀) hu ha
  have hb' := represents_transportStage B S hS p hp e₂ (w ≫ v₀) hv hb
  -- the two composites base change to the identity over `M`
  have hone := map_comp_eq_id_of_represents B S hS p hp (w ≫ u₀ ≫ e₁) Θ ha' hb'
  have htwo := map_comp_eq_id_of_represents B S hS p hp (w ≫ u₀ ≫ e₁) Θ.symm hb' ha'
  obtain ⟨m₁, r₁, hr₁⟩ := hfaithful k _ _ _ _ hone
  obtain ⟨m₂, r₂, hr₂⟩ := hfaithful k _ _ _ _ htwo
  -- a common stage on which both composites are already the identity
  obtain ⟨m₀, s₀, t₀, -⟩ := IsCofilteredOrEmpty.cone_objs m₁ m₂
  obtain ⟨m, z, hz⟩ := IsCofilteredOrEmpty.cone_maps (s₀ ≫ r₁) (t₀ ≫ r₂)
  have hs : (z ≫ s₀) ≫ r₁ = z ≫ s₀ ≫ r₁ := Category.assoc _ _ _
  have ht : (z ≫ t₀) ≫ r₂ = z ≫ s₀ ≫ r₁ := by rw [Category.assoc]; exact hz.symm
  have key₁ := map_eq_of_map_comp_eq B S hS r₁ (z ≫ s₀) hs hr₁
  have key₂ := map_eq_of_map_comp_eq B S hS r₂ (z ≫ t₀) ht hr₂
  refine ⟨m, (z ≫ s₀ ≫ r₁) ≫ w ≫ u₀ ≫ e₁, ?_, ?_⟩
  · refine
      { hom := transportStage B S hS (w ≫ u₀ ≫ e₁) (z ≫ s₀ ≫ r₁) rfl
          (transportStage B S hS e₁ (w ≫ u₀) hu a)
        inv := transportStage B S hS (w ≫ u₀ ≫ e₁) (z ≫ s₀ ≫ r₁) rfl
          (transportStage B S hS e₂ (w ≫ v₀) hv b)
        hom_inv_id := ?_
        inv_hom_id := ?_ }
    · rw [← transportStage_comp,
        transportStage_congr B S hS (w ≫ u₀ ≫ e₁) (z ≫ s₀ ≫ r₁) rfl key₁,
        transportStage_id]
    · rw [← transportStage_comp,
        transportStage_congr B S hS (w ≫ u₀ ≫ e₁) (z ≫ s₀ ≫ r₁) rfl key₂,
        transportStage_id]
  · exact represents_transportStage B S hS p hp (w ≫ u₀ ≫ e₁) (z ≫ s₀ ≫ r₁) rfl ha'

end AlgebraicGeometry.FinitePresentationSpacesOver

end
