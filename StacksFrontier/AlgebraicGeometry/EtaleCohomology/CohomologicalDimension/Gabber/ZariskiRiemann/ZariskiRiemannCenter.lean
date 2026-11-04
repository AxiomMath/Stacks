module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologicalDimension.Gabber.ZariskiRiemann.ZariskiRiemannLimitStep
public import Mathlib.AlgebraicGeometry.ValuativeCriterion
public import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-!
# The center of a valuation ring on a proper model

Let `B` be a domain with fraction field `K = Frac B` and let `V` be a valuation subring of `K`
containing `B`. For a proper model `f : Y ⟶ Spec B` of `η = Spec K`
(`AlgebraicGeometry.Scheme.ZariskiRiemann.ProperModel`), the valuative criterion of properness
applied to the square

```
Spec K ──j──▶ Y
  │           │ f
  ▼           ▼
Spec V ─────▶ Spec B
```

gives a unique morphism `Spec V ⟶ Y` through which both triangles commute: the **center** of
`V` on `Y`. The image `y_Y(V)` of the closed point of `Spec V` is the center point; the induced
map `𝒪_{Y, y_Y(V)} ⟶ V` is a local homomorphism; when `B` is local and `V` dominates `B`, the
center point lies over the closed point of `Spec B`. Centers are compatible with refinements of
models (by uniqueness), so the images of the local rings `𝒪_{Y, y_Y(V)}` in `V` grow along
refinements. This is the first layer of the Zariski–Riemann side of Gabber's proof of Exposé
XVIII-A, Corollary 1.2 (the last remark of §2 of that exposé): the points of the Zariski–Riemann
space are the valuation rings `V`, and the colimit of the `𝒪_{Y, y_Y(V)}` is `V`.

## Main definitions

* `AlgebraicGeometry.Scheme.ZariskiRiemann.valuationSubringBaseMap` — the ring map `B → V`.
* `AlgebraicGeometry.Scheme.ZariskiRiemann.ProperModel.center` — the center `Spec V ⟶ Y`.
* `AlgebraicGeometry.Scheme.ZariskiRiemann.ProperModel.centerPoint` — the point `y_Y(V)`.
* `AlgebraicGeometry.Scheme.ZariskiRiemann.ProperModel.centerStalkMap` — the local
  homomorphism `𝒪_{Y, y_Y(V)} ⟶ V`.
* `AlgebraicGeometry.Scheme.ZariskiRiemann.ProperModel.centerRange` — its image, a subring
  of `V`.

## Main results

* `AlgebraicGeometry.Scheme.ZariskiRiemann.ProperModel.eq_center` — uniqueness of the center.
* `AlgebraicGeometry.Scheme.ZariskiRiemann.ProperModel.f_centerPoint` — for `V` dominating the
  local ring `B`, the center lies over the closed point of `Spec B`.
* `AlgebraicGeometry.Scheme.ZariskiRiemann.ProperModel.j_specializes_centerPoint`,
  `AlgebraicGeometry.Scheme.ZariskiRiemann.ProperModel.centerStalkMap_comp_algebraMap` — `j(η)`
  specializes to `y_Y(V)`, and `𝒪_{Y, y_Y(V)} ⟶ V ⊆ K` is the specialization map to
  `𝒪_{Y, j(η)}` followed by the stalk map of `j`.
* `AlgebraicGeometry.Scheme.ZariskiRiemann.ProperModel.Refinement.center_eq`,
  `AlgebraicGeometry.Scheme.ZariskiRiemann.ProperModel.Refinement.π_centerPoint` — a refinement
  `π : Y' ⟶ Y` carries the center on `Y'` to the center on `Y`.
* `AlgebraicGeometry.Scheme.ZariskiRiemann.ProperModel.Refinement.centerRange_mono` — the image
  of `𝒪_{Y, y_Y(V)}` in `V` is contained in the image of `𝒪_{Y', y_{Y'}(V)}`.

## References

* Travaux de Gabber sur l'uniformisation locale et la cohomologie étale des schémas
  quasi-excellents, Exposé XVIII-A (L. Illusie), last remark of §2, Astérisque 363–364 (2014)
* O. Zariski, P. Samuel, *Commutative Algebra*, Vol. II, Chapter VI, §17
* [Stacks Project, Tag 0BX5](https://stacks.math.columbia.edu/tag/0BX5)
-/

@[expose] public noncomputable section

open CategoryTheory IsLocalRing

universe u

namespace AlgebraicGeometry.Scheme.ZariskiRiemann

variable {B : Type u} [CommRing B] [IsDomain B]

/-- The ring map `B → V` for a valuation subring `V` of `Frac B` containing (the image of) `B`. -/
def valuationSubringBaseMap (V : ValuationSubring (FractionRing B))
    (hV : ∀ b : B, algebraMap B (FractionRing B) b ∈ V) : B →+* V :=
  (algebraMap B (FractionRing B)).codRestrict V hV

/-- The ring map `B → V` followed by `V ⊆ Frac B` is the inclusion `B ⊆ Frac B`. -/
theorem valuationSubringBaseMap_comp (V : ValuationSubring (FractionRing B))
    (hV : ∀ b : B, algebraMap B (FractionRing B) b ∈ V) :
    CommRingCat.ofHom (valuationSubringBaseMap V hV) ≫
        CommRingCat.ofHom (algebraMap V (FractionRing B)) =
      CommRingCat.ofHom (algebraMap B (FractionRing B)) :=
  rfl

/-- For `f : Spec R ⟶ X` with `R` local and `g : X ⟶ Y`, the image of `𝒪_{Y, g (f 𝔪)} ⟶ R`
is contained in the image of `𝒪_{X, f 𝔪} ⟶ R`. -/
theorem range_stalkClosedPointTo_comp_le {R : CommRingCat.{u}} [IsLocalRing R] {X Y : Scheme.{u}}
    (f : Spec R ⟶ X) (g : X ⟶ Y) :
    (Scheme.stalkClosedPointTo (f ≫ g)).hom.range ≤ (Scheme.stalkClosedPointTo f).hom.range := by
  rw [Scheme.stalkClosedPointTo_comp]
  rintro _ ⟨a, rfl⟩
  exact ⟨_, rfl⟩

namespace ProperModel

variable (M : ProperModel B) (V : ValuationSubring (FractionRing B))
  (hV : ∀ b : B, algebraMap B (FractionRing B) b ∈ V)

/-- **The valuative square of a model and a valuation ring**: `j : Spec K ⟶ Y` on top,
`Spec V ⟶ Spec B` at the bottom. -/
def valuativeCommSq : ValuativeCommSq M.f where
  R := V
  K := FractionRing B
  i₁ := M.j
  i₂ := Spec.map (CommRingCat.ofHom (valuationSubringBaseMap V hV))
  commSq := ⟨by rw [M.fac, ← Spec.map_comp, valuationSubringBaseMap_comp]⟩

omit [IsDomain B] in
/-- A proper model satisfies the valuative criterion (Stacks 0BX5). -/
theorem valuativeCriterion : ValuativeCriterion M.f := by
  have h : (ValuativeCriterion ⊓ @QuasiCompact ⊓ @QuasiSeparated ⊓ @LocallyOfFiniteType) M.f := by
    rw [← IsProper.eq_valuativeCriterion]
    exact M.isProper
  exact h.1.1.1

/-- The unique lift of the valuative square. -/
def centerLift : (M.valuativeCommSq V hV).commSq.LiftStruct :=
  (Classical.choice (M.valuativeCriterion (M.valuativeCommSq V hV))).default

/-- **The center of `V` on the model `Y`**: the unique morphism `Spec V ⟶ Y` over `Spec B`
extending `j : Spec K ⟶ Y`. -/
def center : Spec (.of V) ⟶ M.Y :=
  (M.centerLift V hV).l

/-- The center extends `j`. -/
@[reassoc]
theorem specMap_comp_center :
    Spec.map (CommRingCat.ofHom (algebraMap V (FractionRing B))) ≫ M.center V hV = M.j :=
  (M.centerLift V hV).fac_left

/-- The center lies over `Spec V ⟶ Spec B`. -/
@[reassoc]
theorem center_comp_f :
    M.center V hV ≫ M.f = Spec.map (CommRingCat.ofHom (valuationSubringBaseMap V hV)) :=
  (M.centerLift V hV).fac_right

/-- **Uniqueness of the center** (the separatedness half of the valuative criterion). -/
theorem eq_center {l : Spec (.of V) ⟶ M.Y}
    (h₁ : Spec.map (CommRingCat.ofHom (algebraMap V (FractionRing B))) ≫ l = M.j)
    (h₂ : l ≫ M.f = Spec.map (CommRingCat.ofHom (valuationSubringBaseMap V hV))) :
    l = M.center V hV :=
  congrArg CommSq.LiftStruct.l
    ((Classical.choice (M.valuativeCriterion (M.valuativeCommSq V hV))).uniq ⟨l, h₁, h₂⟩)

/-- **The center point** `y_Y(V)`: the image of the closed point of `Spec V`. -/
def centerPoint : M.Y :=
  M.center V hV (closedPoint V)

/-- If `B` is local and `V` dominates `B` (the map `B → V` is local), the center point lies over
the closed point of `Spec B`. -/
theorem f_centerPoint [IsLocalRing B] [IsLocalHom (valuationSubringBaseMap V hV)] :
    M.f (M.centerPoint V hV) = closedPoint B := by
  have : IsLocalHom (CommRingCat.ofHom (valuationSubringBaseMap V hV)).hom := ‹_›
  change (M.center V hV ≫ M.f) (closedPoint (CommRingCat.of V)) = _
  rw [center_comp_f]
  exact Spec_closedPoint

/-- **The local homomorphism `𝒪_{Y, y_Y(V)} ⟶ V`** induced by the center. -/
def centerStalkMap : M.Y.presheaf.stalk (M.centerPoint V hV) ⟶ CommRingCat.of V :=
  Scheme.stalkClosedPointTo (M.center V hV)

/-- The stalk map `𝒪_{Y, y_Y(V)} ⟶ V` induced by the center is a local homomorphism. -/
instance isLocalHom_centerStalkMap : IsLocalHom (M.centerStalkMap V hV).hom :=
  Scheme.isLocalHom_stalkClosedPointTo (M.center V hV)

/-- The image of `𝒪_{Y, y_Y(V)}` in `V`. -/
def centerRange : Subring V :=
  (M.centerStalkMap V hV).hom.range

/-- The center of `V` composed with the generic point: the composite
`Spec K ⟶ Spec V ⟶ Spec 𝒪_{Y, y_Y(V)} ⟶ Y` is `j`. -/
theorem specMap_centerStalkMap_fromSpecStalk :
    Spec.map (M.centerStalkMap V hV) ≫ M.Y.fromSpecStalk (M.centerPoint V hV) =
      M.center V hV :=
  Scheme.Spec_stalkClosedPointTo_fromSpecStalk (M.center V hV)

/-- The point `j(η)` specializes to the center point `y_Y(V)`. -/
theorem j_specializes_centerPoint :
    M.j (closedPoint (FractionRing B)) ⤳ M.centerPoint V hV := by
  have h : M.j (closedPoint (FractionRing B)) =
      M.center V hV ((Spec.map (CommRingCat.ofHom (algebraMap V (FractionRing B))))
        (closedPoint (FractionRing B))) := by
    conv_lhs => rw [← M.specMap_comp_center V hV]
    rfl
  rw [h]
  exact (specializes_closedPoint _).map (M.center V hV).continuous

/-- **The stalk map at the center is compatible with `j`**: `𝒪_{Y, y_Y(V)} ⟶ V ⊆ K` is the
specialization map `𝒪_{Y, y_Y(V)} ⟶ 𝒪_{Y, j(η)}` followed by the stalk map
`𝒪_{Y, j(η)} ⟶ K` of `j : Spec K ⟶ Y`. -/
theorem centerStalkMap_comp_algebraMap :
    M.centerStalkMap V hV ≫ CommRingCat.ofHom (algebraMap V (FractionRing B)) =
      M.Y.presheaf.stalkSpecializes (M.j_specializes_centerPoint V hV) ≫
        Scheme.stalkClosedPointTo M.j := by
  apply Spec.map_injective
  apply (cancel_mono (M.Y.fromSpecStalk (M.centerPoint V hV))).1
  rw [Spec.map_comp, Category.assoc, specMap_centerStalkMap_fromSpecStalk,
    specMap_comp_center, Spec.map_comp, Category.assoc,
    Scheme.SpecMap_stalkSpecializes_fromSpecStalk, Scheme.Spec_stalkClosedPointTo_fromSpecStalk]

namespace Refinement

variable {V} {M' M : ProperModel B} (φ : Refinement M' M)

/-- **Centers are compatible with refinements**: the center on `Y` is the center on `Y'`
followed by `π : Y' ⟶ Y`. -/
theorem center_eq : M.center V hV = M'.center V hV ≫ φ.π :=
  (M.eq_center V hV (by rw [specMap_comp_center_assoc, φ.fac])
    (by rw [Category.assoc, φ.comm, center_comp_f])).symm

/-- A refinement carries the center point on `Y'` to the center point on `Y`. -/
theorem π_centerPoint : φ.π (M'.centerPoint V hV) = M.centerPoint V hV := by
  rw [centerPoint, centerPoint, φ.center_eq hV]
  rfl

include φ in
/-- **The local rings at the centers grow along refinements**: the image of
`𝒪_{Y, y_Y(V)}` in `V` is contained in the image of `𝒪_{Y', y_{Y'}(V)}`. -/
theorem centerRange_mono : M.centerRange V hV ≤ M'.centerRange V hV := by
  have key : ∀ l : Spec (.of V) ⟶ M.Y, l = M'.center V hV ≫ φ.π →
      (Scheme.stalkClosedPointTo l).hom.range ≤ M'.centerRange V hV := by
    rintro l rfl
    exact range_stalkClosedPointTo_comp_le _ _
  exact key _ (φ.center_eq hV)

end Refinement

end ProperModel

end AlgebraicGeometry.Scheme.ZariskiRiemann

end
