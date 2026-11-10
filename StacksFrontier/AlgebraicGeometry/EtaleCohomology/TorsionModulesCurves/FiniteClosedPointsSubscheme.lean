module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Integral
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.RingTheory.Finiteness.Basic

/-!
# The closed subscheme on a finite set of closed points with residue field `k`

Let `X` be a scheme and `T` a finite set of closed points of `X` at each of which the residue
field is a fixed field `k`. The disjoint union of one copy of `Spec k` for each point of `T`
is a scheme `Z` with a closed immersion into `X` whose image is exactly `T`, and it is finite
over `Spec k`.

## Main definitions

* `Stacks.EtaleCohomology.TorsionModules.pointsScheme` — the disjoint union `Z = ∐_{z ∈ T} Spec k`.
* `Stacks.EtaleCohomology.TorsionModules.pointHom` — the closed immersion `Spec k ⟶ X` at a point
  of `T`.
* `Stacks.EtaleCohomology.TorsionModules.pointsSchemeHom` — the closed immersion `Z ⟶ X`.
* `Stacks.EtaleCohomology.TorsionModules.pointsSchemeToSpec` — the structure morphism
  `Z ⟶ Spec k`.

## Main results

* `Stacks.EtaleCohomology.TorsionModules.isClosedImmersion_pointsSchemeHom` — `Z ⟶ X` is a closed
  immersion.
* `Stacks.EtaleCohomology.TorsionModules.range_pointsSchemeHom` — its image is `T`.
* `Stacks.EtaleCohomology.TorsionModules.isIntegralHom_pointsSchemeToSpec` — `Z ⟶ Spec k` is
  integral.

## Implementation notes

That `Z ⟶ X` is a closed immersion is checked by hand rather than through a stability property
of coproducts, which Mathlib has only for binary ones: surjectivity on stalks is Zariski-local
at the source, so it is inherited from the components through
`AlgebraicGeometry.sigmaOpenCover`; and the underlying map is a closed embedding because it is
continuous, injective — distinct points of `T` are distinct, and `Spec k` has one point — and a
closed map, every subset of its image being a finite union of closed points of `X`.

Integrality over `Spec k` goes through `AlgebraicGeometry.sigmaSpec`, which identifies a finite
coproduct of spectra with the spectrum of the product ring: `Z = Spec (T → k)` and the structure
morphism is `Spec` of the diagonal `k ⟶ (T → k)`, a finite and hence integral ring map.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.EtaleCohomology.TorsionModules

variable (k : Type u) [Field k] {X : Scheme.{u}} (T : Set X)

/-- **The disjoint union of one copy of `Spec k` for each point of `T`.** -/
abbrev pointsScheme : Scheme.{u} := ∐ fun _ : T ↦ Spec (CommRingCat.of k)

variable (e : ∀ z : T, X.residueField z.1 ≅ CommRingCat.of k)

/-- **The morphism `Spec k ⟶ X` at a point of `T`**: the canonical morphism from the spectrum of
the residue field, read through the given identification of that residue field with `k`. -/
def pointHom (z : T) : Spec (CommRingCat.of k) ⟶ X :=
  Spec.map (e z).hom ≫ X.fromSpecResidueField z.1

/-- Precomposing with an isomorphism does not change the image of a morphism of schemes. -/
private theorem range_comp_of_isIso {Y Z W : Scheme.{u}} (f : Y ⟶ Z) [IsIso f] (g : Z ⟶ W) :
    Set.range (f ≫ g).base = Set.range g.base := by
  have hsurj : Function.Surjective f.base := fun z ↦
    ⟨(inv f).base z, by rw [← Scheme.Hom.comp_apply, IsIso.inv_hom_id]; simp⟩
  ext w
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨f.base y, (Scheme.Hom.comp_apply f g y).symm⟩
  · rintro ⟨z, rfl⟩
    obtain ⟨y, rfl⟩ := hsurj z
    exact ⟨y, Scheme.Hom.comp_apply f g y⟩

/-- The image of `pointHom` is the single point it is taken at. -/
theorem range_pointHom (z : T) : Set.range (pointHom k T e z).base = {z.1} := by
  rw [pointHom, range_comp_of_isIso, Scheme.range_fromSpecResidueField]

/-- `pointHom` sends every point of `Spec k` to the point it is taken at. -/
theorem pointHom_base_apply (z : T) (w : Spec (CommRingCat.of k)) :
    (pointHom k T e z).base w = z.1 := by
  have : (pointHom k T e z).base w ∈ Set.range (pointHom k T e z).base := ⟨w, rfl⟩
  rwa [range_pointHom] at this

/-- `pointHom` is a closed immersion when the point is closed. -/
theorem isClosedImmersion_pointHom (hcl : ∀ z : T, IsClosed ({z.1} : Set X)) (z : T) :
    IsClosedImmersion (pointHom k T e z) :=
  have : IsClosedImmersion (X.fromSpecResidueField z.1) :=
    isClosed_singleton_iff_isClosedImmersion.mp (hcl z)
  inferInstanceAs (IsClosedImmersion (Spec.map (e z).hom ≫ X.fromSpecResidueField z.1))

/-- **The morphism `Z ⟶ X`** out of the disjoint union of the points. -/
def pointsSchemeHom : pointsScheme k T ⟶ X := Sigma.desc (pointHom k T e)

/-- The restriction of `pointsSchemeHom` to the copy of `Spec k` indexed by `z` is
`pointHom k T e z`. -/
@[reassoc (attr := simp)]
theorem ι_pointsSchemeHom (z : T) :
    Sigma.ι (fun _ : T ↦ Spec (CommRingCat.of k)) z ≫ pointsSchemeHom k T e =
      pointHom k T e z :=
  Sigma.ι_comp_desc _ _

/-- `pointsSchemeHom` sends every point of the copy of `Spec k` indexed by `z` to `z`. -/
private theorem pointsSchemeHom_base_sigmaMk (z : T) (w : Spec (CommRingCat.of k)) :
    (pointsSchemeHom k T e).base
      (sigmaMk (fun _ : T ↦ Spec (CommRingCat.of k)) ⟨z, w⟩) = z.1 := by
  rw [sigmaMk_mk, ← Scheme.Hom.comp_apply, ι_pointsSchemeHom, pointHom_base_apply]

/-- **The image of `Z ⟶ X` is `T`.** -/
theorem range_pointsSchemeHom : Set.range (pointsSchemeHom k T e).base = T := by
  ext y
  constructor
  · rintro ⟨p, rfl⟩
    obtain ⟨⟨z, w⟩, rfl⟩ := (sigmaMk fun _ : T ↦ Spec (CommRingCat.of k)).surjective p
    rw [pointsSchemeHom_base_sigmaMk]
    exact z.2
  · intro hy
    obtain ⟨w⟩ : Nonempty (Spec (CommRingCat.of k)) := inferInstance
    exact ⟨sigmaMk (fun _ : T ↦ Spec (CommRingCat.of k)) ⟨⟨y, hy⟩, w⟩,
      pointsSchemeHom_base_sigmaMk k T e ⟨y, hy⟩ w⟩

variable (hT : T.Finite) (hcl : ∀ z : T, IsClosed ({z.1} : Set X))

include hT hcl in
/-- Every subset of `T` is closed in `X`: it is a finite union of closed points. -/
theorem isClosed_of_subset (A : Set X) (hA : A ⊆ T) : IsClosed A := by
  rw [← Set.biUnion_of_singleton A]
  exact (hT.subset hA).isClosed_biUnion fun a ha ↦ hcl ⟨a, hA ha⟩

include hcl in
/-- **`Z ⟶ X` is surjective on stalks**: surjectivity on stalks is Zariski-local at the source,
and the components of the coproduct are closed immersions. -/
theorem surjectiveOnStalks_pointsSchemeHom :
    SurjectiveOnStalks (pointsSchemeHom k T e) := by
  let 𝒰 : (pointsScheme k T).OpenCover :=
    Scheme.Cover.mkOfCovers T (fun _ ↦ Spec (CommRingCat.of k))
      (fun z ↦ Sigma.ι (fun _ : T ↦ Spec (CommRingCat.of k)) z)
      (fun p ↦ by
        obtain ⟨⟨z, w⟩, rfl⟩ := (sigmaMk fun _ : T ↦ Spec (CommRingCat.of k)).surjective p
        exact ⟨z, w, (sigmaMk_mk (fun _ : T ↦ Spec (CommRingCat.of k)) z w).symm⟩)
  rw [IsZariskiLocalAtSource.iff_of_openCover (P := @SurjectiveOnStalks) (𝒰 := 𝒰)]
  intro z
  rw [show 𝒰.f z ≫ pointsSchemeHom k T e = pointHom k T e z from
    ι_pointsSchemeHom k T e z]
  exact (isClosedImmersion_pointHom k T e hcl z).toSurjectiveOnStalks

include hT hcl in
/-- **`Z ⟶ X` is a closed immersion.** -/
theorem isClosedImmersion_pointsSchemeHom : IsClosedImmersion (pointsSchemeHom k T e) := by
  have := surjectiveOnStalks_pointsSchemeHom k T e hcl
  refine ⟨Topology.IsClosedEmbedding.of_continuous_injective_isClosedMap
    (pointsSchemeHom k T e).base.hom.continuous ?_ ?_⟩
  · intro p q hpq
    obtain ⟨⟨z, w⟩, rfl⟩ := (sigmaMk fun _ : T ↦ Spec (CommRingCat.of k)).surjective p
    obtain ⟨⟨z', w'⟩, rfl⟩ := (sigmaMk fun _ : T ↦ Spec (CommRingCat.of k)).surjective q
    rw [pointsSchemeHom_base_sigmaMk, pointsSchemeHom_base_sigmaMk] at hpq
    obtain rfl : z = z' := Subtype.ext hpq
    rw [Subsingleton.elim w w']
  · intro A _
    exact isClosed_of_subset T hT hcl _
      ((Set.image_subset_range _ _).trans (range_pointsSchemeHom k T e).subset)

/-- **The structure morphism `Z ⟶ Spec k`.** -/
def pointsSchemeToSpec : pointsScheme k T ⟶ Spec (CommRingCat.of k) :=
  Sigma.desc fun _ ↦ 𝟙 _

/-- The diagonal ring map `k ⟶ (T → k)`, of which the structure morphism of `Z` is the
spectrum.

This is Mathlib's `Pi.constRingHom`, bundled into `CommRingCat`. It had been re-derived here as
`Pi.ringHom fun _ ↦ RingHom.id k`, the same map spelled differently, while two other places in
this library already wrote `CommRingCat.ofHom (Pi.constRingHom _ _)` for it
(`StacksFrontier/Examples/QuasiCoherentPushforward/SeparatedNotQuasiCompact.lean:70` and
`StacksFrontier/AlgebraicGeometry/Spaces/PointsAndCoverings/InfiniteProduct.lean:109`) and a third
composed it (`StacksFrontier/AlgebraicGeometry/LimitConeBound/Basic.lean:199`). -/
def constRingHom : CommRingCat.of k ⟶ CommRingCat.of (∀ _ : T, k) :=
  CommRingCat.ofHom (Pi.constRingHom T k)

include hT in
/-- The diagonal ring map `k ⟶ (T → k)` is integral: `T → k` is a finite `k`-module. -/
theorem isIntegral_constRingHom : (constRingHom k T).hom.IsIntegral := by
  have : Finite T := hT
  exact algebraMap_isIntegral_iff.mpr (Algebra.IsIntegral.of_finite k (∀ _ : T, k))

include hT in
/-- The structure morphism of `Z` is `Spec` of the diagonal, read through the identification of
a finite coproduct of spectra with the spectrum of the product ring. -/
theorem pointsSchemeToSpec_eq :
    pointsSchemeToSpec k T =
      sigmaSpec (fun _ : T ↦ CommRingCat.of k) ≫ Spec.map (constRingHom k T) := by
  have : Finite T := hT
  refine Sigma.hom_ext _ _ fun z ↦ ?_
  rw [pointsSchemeToSpec, Sigma.ι_comp_desc, ← Category.assoc, ι_sigmaSpec, ← Spec.map_comp,
    show constRingHom k T ≫ CommRingCat.ofHom (Pi.evalRingHom (fun _ : T ↦ k) z) =
      𝟙 (CommRingCat.of k) by ext; rfl, Spec.map_id]

include hT in
/-- **`Z ⟶ Spec k` is integral.** -/
theorem isIntegralHom_pointsSchemeToSpec : IsIntegralHom (pointsSchemeToSpec k T) := by
  have : Finite T := hT
  have : IsIntegralHom (Spec.map (constRingHom k T)) :=
    AlgebraicGeometry.IsIntegralHom.SpecMap_iff.mpr (isIntegral_constRingHom k T hT)
  rw [pointsSchemeToSpec_eq k T hT]
  infer_instance

end Stacks.EtaleCohomology.TorsionModules

end
