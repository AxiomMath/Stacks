module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Points

/-!
# The topology on the points of an algebraic space

For a presheaf `F` on the big fppf site of `S`, a subset `W ⊆ |F|` is open when, for every object
`U` of the site and every morphism `yoneda.obj U ⟶ F`, the preimage of `W` in `|U|` is cut out by
an open subset of the scheme `U`, under the canonical description of the points of a represented
presheaf. This is the final topology for the maps `|U| → |F|` indexed by the scheme-valued points
of `F`. On a represented presheaf it is the topology of the representing scheme, and every
morphism of presheaves is continuous on points.

## Main definitions

* `AlgebraicGeometry.Space.schemePoint` is the point of the scheme `U` underlying a
  field-valued point of `yoneda.obj U`.
* `AlgebraicGeometry.Space.IsSchemeOpen` is the condition on a set of points of
  `yoneda.obj U` that it is cut out by an open subset of the scheme `U`, membership being
  tested at `schemePoint`.
* `AlgebraicGeometry.Space.pointTopology` is the topology on `|F|`.

## Main results

* `AlgebraicGeometry.Space.isOpen_pointTopology_iff` is the defining characterization of
  the open sets.
* `AlgebraicGeometry.Space.isOpen_yoneda_iff_isSchemeOpen`: on a represented presheaf the
  topology is the one induced from the scheme.
* `AlgebraicGeometry.Space.continuous_pointsMap`: every morphism of presheaves is continuous on
  points.

## References

* [Stacks Project, Tag 03BX](https://stacks.math.columbia.edu/tag/03BX)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The point of the scheme `U` underlying a field-valued point of its represented
presheaf: the image of the closed point of the field spectrum along the section. -/
noncomputable def schemePoint (U : BigFppfOver B S hS)
    (p : FieldValuedPoint B S hS (yoneda.obj U)) :
    (BigFppfOver.toScheme B S hS).obj U :=
  (BigFppfOver.toScheme B S hS).map p.value (IsLocalRing.closedPoint p.carrier)

/-- Applying a morphism of the site to a field-valued point of a represented presheaf moves
its underlying scheme point along the underlying morphism of schemes. -/
theorem schemePoint_map_yoneda {U V : BigFppfOver B S hS} (h : U ⟶ V)
    (p : FieldValuedPoint B S hS (yoneda.obj U)) :
    schemePoint B S hS V
        (FieldValuedPoint.map B S hS (yoneda.obj U) (yoneda.map h) p) =
      (BigFppfOver.toScheme B S hS).map h (schemePoint B S hS U p) := by
  change (BigFppfOver.toScheme B S hS).map (p.value ≫ h) _ = _
  rw [Functor.map_comp]
  rfl

/-- A set of points of a represented presheaf is *scheme open* when it is cut out by an
open subset of the representing scheme, membership being tested at the underlying scheme
point of a field-valued representative. -/
def IsSchemeOpen (U : BigFppfOver B S hS)
    (W : Set (points B S hS (yoneda.obj U))) : Prop :=
  ∃ V : Set ((BigFppfOver.toScheme B S hS).obj U), IsOpen V ∧
    ∀ p : FieldValuedPoint B S hS (yoneda.obj U),
      (p.class B S hS (yoneda.obj U) ∈ W ↔ schemePoint B S hS U p ∈ V)

/-- The topology on the points of a presheaf on the big fppf site of `S`: a set of points
is open when its preimage under every scheme-valued point is scheme open. -/
@[instance_reducible, stacks 03BY "the underlying topological space of an algebraic space"]
def pointTopology (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :
    TopologicalSpace (points B S hS F) where
  IsOpen W := ∀ (U : BigFppfOver B S hS) (a : yoneda.obj U ⟶ F),
    IsSchemeOpen B S hS U (pointsMap B S hS (yoneda.obj U) a ⁻¹' W)
  isOpen_univ := fun _ _ ↦ ⟨Set.univ, isOpen_univ, fun _ ↦ by simp⟩
  isOpen_inter := by
    rintro W₁ W₂ h₁ h₂ U a
    obtain ⟨V₁, hV₁, hmem₁⟩ := h₁ U a
    obtain ⟨V₂, hV₂, hmem₂⟩ := h₂ U a
    refine ⟨V₁ ∩ V₂, hV₁.inter hV₂, fun p ↦ ?_⟩
    simp only [Set.mem_preimage, Set.mem_inter_iff] at hmem₁ hmem₂ ⊢
    exact and_congr (hmem₁ p) (hmem₂ p)
  isOpen_sUnion := by
    intro s hs U a
    choose V hVopen hVmem using fun W : s ↦ hs W.1 W.2 U a
    refine ⟨⋃ W : s, V W, isOpen_iUnion hVopen, fun p ↦ ?_⟩
    simp only [Set.mem_preimage, Set.mem_sUnion, Set.mem_iUnion] at hVmem ⊢
    constructor
    · rintro ⟨W, hW, hpW⟩
      exact ⟨⟨W, hW⟩, (hVmem ⟨W, hW⟩ p).mp hpW⟩
    · rintro ⟨W, hpW⟩
      exact ⟨W.1, W.2, (hVmem W p).mpr hpW⟩

/-- The open sets of `AlgebraicGeometry.Space.pointTopology` are exactly those whose
preimage under every scheme-valued point is scheme open. -/
theorem isOpen_pointTopology_iff {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (W : Set (points B S hS F)) :
    @IsOpen _ (pointTopology B S hS F) W ↔
      ∀ (U : BigFppfOver B S hS) (a : yoneda.obj U ⟶ F),
        IsSchemeOpen B S hS U (pointsMap B S hS (yoneda.obj U) a ⁻¹' W) :=
  Iff.rfl

/-- On a represented presheaf the point topology is the
topology of the representing scheme: a set of points is open exactly when it is cut out by
an open subset of the scheme. -/
theorem isOpen_yoneda_iff_isSchemeOpen (U : BigFppfOver B S hS)
    (W : Set (points B S hS (yoneda.obj U))) :
    @IsOpen _ (pointTopology B S hS (yoneda.obj U)) W ↔ IsSchemeOpen B S hS U W := by
  constructor
  · intro hW
    simpa only [pointsMap_id, Set.preimage_id] using hW U (𝟙 _)
  · rintro ⟨V, hV, hmem⟩ U' a
    obtain ⟨h, rfl⟩ : ∃ h : U' ⟶ U, yoneda.map h = a :=
      ⟨yoneda.preimage a, by simp⟩
    refine ⟨(BigFppfOver.toScheme B S hS).map h ⁻¹' V,
      hV.preimage ((BigFppfOver.toScheme B S hS).map h).continuous, fun p ↦ ?_⟩
    rw [Set.mem_preimage, pointsMap_class, hmem, schemePoint_map_yoneda]
    rfl

/-- Every morphism of presheaves on the big fppf site of `S`
is continuous on points. -/
theorem continuous_pointsMap {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : F ⟶ G) :
    @Continuous _ _ (pointTopology B S hS F) (pointTopology B S hS G)
      (pointsMap B S hS F f) := by
  rw [continuous_def]
  intro W hW U a
  simpa only [pointsMap_comp, Set.preimage_comp] using hW U (a ≫ f)

end AlgebraicGeometry.Space

end
