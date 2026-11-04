module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.FlatMono
public import Mathlib.AlgebraicGeometry.Morphisms.IsIso
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.NeighborhoodsStalksPoints.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Connected components along a closed map, and sections of finite étale morphisms

A closed surjection with connected fibres induces a bijection on connected components, and if a
continuous map is injective on connected components, then every clopen subset of the source which
meets a fibre contains that whole fibre.

A section `i : B ⟶ E` of a finite étale morphism `p : E ⟶ B` is both an open and a closed
immersion, hence an isomorphism as soon as `E` is connected. If a scheme `A` carries a finite
étale morphism `p : A ⟶ X` with a section together with a morphism `c : A ⟶ T` that is injective
on connected components, then a geometric point of `X` admits at most one lift to `A` compatible
with both `p` and `c`.

## Main results

* `AlgebraicGeometry.isPreconnected_preimage_of_surjective_closed_connectedFibres`: the preimage
  of a preconnected set under a closed surjection with connected fibres is preconnected.
* `AlgebraicGeometry.closedMap_connectedFibres_bijective_connectedComponentsMap`: a closed
  continuous map with connected fibres is a bijection on connected components.
* `AlgebraicGeometry.fiber_subset_of_clopen_component`: a clopen set containing one point of a
  fibre of a map injective on connected components contains the whole fibre.
* `AlgebraicGeometry.finiteEtaleSection_isOpenAndClosed`: a section of a finite étale morphism of
  schemes is both an open immersion and a closed immersion.
* `AlgebraicGeometry.finiteEtaleSection_isIso_of_connected`: a section of a finite étale morphism
  with connected source is an isomorphism.
* `AlgebraicGeometry.geometricFiber_pair_subsingleton_of_section`: uniqueness of a compatible
  lift of a geometric point along a sectioned finite étale morphism.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- Let `f : X → Y` be a closed surjection all of whose fibres are connected. Then the preimage
of a preconnected subset of `Y` is a preconnected subset of `X`. -/
theorem isPreconnected_preimage_of_surjective_closed_connectedFibres
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (f : X → Y)
    (hfclosed : IsClosedMap f) (hfsurj : Function.Surjective f)
    (hfib : ∀ y : Y, IsConnected (f ⁻¹' {y}))
    {S : Set Y} (hS : IsPreconnected S) :
    IsPreconnected (f ⁻¹' S) := by
  refine isPreconnected_closed_iff.2 fun U V hU hV hcover ⟨u, huS, huU⟩ ⟨v, hvS, hvV⟩ ↦ ?_
  have hcoverS : S ⊆ f '' U ∪ f '' V := by
    intro y hy
    obtain ⟨x, rfl⟩ := hfsurj y
    exact (hcover hy).imp (fun hx ↦ ⟨x, hx, rfl⟩) (fun hx ↦ ⟨x, hx, rfl⟩)
  obtain ⟨y, hyS, ⟨x, hxU, hfx⟩, x', hxV, hfx'⟩ :=
    isPreconnected_closed_iff.1 hS _ _ (hfclosed U hU) (hfclosed V hV) hcoverS
      ⟨f u, huS, u, huU, rfl⟩ ⟨f v, hvS, v, hvV, rfl⟩
  have hfibS : f ⁻¹' {y} ⊆ f ⁻¹' S := Set.preimage_mono (Set.singleton_subset_iff.mpr hyS)
  obtain ⟨z, hzfib, hzUV⟩ := isPreconnected_closed_iff.1 (hfib y).isPreconnected
    U V hU hV (hfibS.trans hcover) ⟨x, hfx, hxU⟩ ⟨x', hfx', hxV⟩
  exact ⟨z, hfibS hzfib, hzUV⟩

/-- A continuous closed map all of whose fibres are connected induces a bijection on the spaces
of connected components. -/
theorem closedMap_connectedFibres_bijective_connectedComponentsMap
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (f : X → Y)
    (hfcont : Continuous f) (hfclosed : IsClosedMap f)
    (hfib : ∀ y : Y, IsConnected (f ⁻¹' {y})) :
    Function.Bijective hfcont.connectedComponentsMap := by
  have hfsurj : Function.Surjective f := fun y ↦ (hfib y).nonempty
  refine ⟨?_, ?_⟩
  · intro a b hab
    induction a using Quotient.inductionOn with | h x₁ =>
    induction b using Quotient.inductionOn with | h x₂ =>
    have hx₂ : x₂ ∈ connectedComponent x₁ :=
      (isPreconnected_preimage_of_surjective_closed_connectedFibres f hfclosed hfsurj hfib
        isPreconnected_connectedComponent).subset_connectedComponent mem_connectedComponent
        (ConnectedComponents.coe_eq_coe.mp hab ▸ mem_connectedComponent)
    exact ConnectedComponents.coe_eq_coe.mpr (connectedComponent_eq hx₂)
  · intro c
    induction c using Quotient.inductionOn with | h y =>
    obtain ⟨x, hx⟩ := hfsurj y
    exact ⟨ConnectedComponents.mk x, congrArg _ hx⟩

/-- Let `f : X → Y` be continuous and injective on connected components. If a clopen subset `U`
of `X` contains a point `x` with `f x = y`, then `U` contains the whole fibre of `f` over `y`. -/
theorem fiber_subset_of_clopen_component
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (f : X → Y)
    (hf : Continuous f)
    (hcomponents : Function.Injective hf.connectedComponentsMap)
    {U : Set X} (hU : IsClopen U) {x : X} (hx : x ∈ U) {y : Y}
    (hxy : f x = y) :
    f ⁻¹' {y} ⊆ U := by
  intro z (hz : f z = y)
  have hmap : hf.connectedComponentsMap (ConnectedComponents.mk z) =
      hf.connectedComponentsMap (ConnectedComponents.mk x) :=
    congrArg ConnectedComponents.mk (hz.trans hxy.symm)
  exact hU.connectedComponent_subset hx
    (ConnectedComponents.coe_eq_coe.mp (hcomponents hmap) ▸ mem_connectedComponent)

/-- A section `i : B ⟶ E` of a finite étale morphism `p : E ⟶ B` of schemes is simultaneously an
open immersion and a closed immersion. -/
@[ega "IV 17.9.3" "finite étale morphisms", sga "6 VIII 1.3" "special case"]
theorem finiteEtaleSection_isOpenAndClosed {B E : Scheme.{u}}
    (p : E ⟶ B) [IsFinite p] [Etale p] (i : B ⟶ E)
    (hi : i ≫ p = 𝟙 B) : IsOpenImmersion i ∧ IsClosedImmersion i := by
  have : Mono i := (SplitMono.mk p hi).mono
  have : Etale (i ≫ p) := hi ▸ inferInstance
  have : Etale i := Etale.of_comp i p
  have : IsClosedImmersion (i ≫ p) := hi ▸ inferInstance
  exact ⟨IsOpenImmersion.of_flat_of_mono i, IsClosedImmersion.of_comp i p⟩

/-- A section of a finite étale morphism of schemes whose source is connected is an
isomorphism. -/
@[sga "1 I 5.3" "special case"]
theorem finiteEtaleSection_isIso_of_connected {B E : Scheme.{u}}
    [ConnectedSpace E] (p : E ⟶ B) [IsFinite p] [Etale p] (i : B ⟶ E)
    (hi : i ≫ p = 𝟙 B) : IsIso i := by
  obtain ⟨hOpen, hClosed⟩ := finiteEtaleSection_isOpenAndClosed p i hi
  have hrange : Set.range i.base = Set.univ :=
    (isClopen_iff.mp ⟨i.isClosedMap.isClosed_range, hOpen.isOpen_range⟩).resolve_left
      (Set.Nonempty.ne_empty ⟨_, Set.mem_range_self (p.base (Classical.arbitrary E))⟩)
  exact (isIso_iff_isOpenImmersion_and_surjective i).2
    ⟨hOpen, (surjective_iff i).2 (Set.range_eq_univ.mp hrange)⟩

/-- Let `p : A ⟶ X` be finite étale with a section `i : X ⟶ A`, and let `c : A ⟶ T` be a
morphism which is injective on connected components. Then a geometric point `x` of `X` has at
most one lift `q` to `A` which agrees with `x ≫ i` after composing with `c` and with `x` after
composing with `p`. -/
theorem geometricFiber_pair_subsingleton_of_section
    {A T X : Scheme.{u}} (c : A ⟶ T) (p : A ⟶ X)
    [IsFinite p] [Etale p] (i : X ⟶ A) (hi : i ≫ p = 𝟙 X)
    (hcomponents : Function.Injective c.continuous.connectedComponentsMap)
    (x : GeometricPoint X) :
    Subsingleton {q : x.source ⟶ A //
      q ≫ c = x.hom ≫ i ≫ c ∧ q ≫ p = x.hom} := by
  obtain ⟨hiOpen, hiClosed⟩ := finiteEtaleSection_isOpenAndClosed p i hi
  have hfactor (q : {q : x.source ⟶ A //
      q ≫ c = x.hom ≫ i ≫ c ∧ q ≫ p = x.hom}) :
      ∃ a : x.source ⟶ X, q.1 = a ≫ i := by
    have hrange : Set.range q.1.base ⊆ Set.range i.base := by
      rintro _ ⟨ξ, rfl⟩
      have hxy : c.base (i.base (x.hom.base ξ)) = (x.hom ≫ i ≫ c).base ξ := by simp
      have hz : c.base (q.1.base ξ) = (x.hom ≫ i ≫ c).base ξ := by
        simpa using congrArg (fun g : x.source ⟶ T => g.base ξ) q.2.1
      exact fiber_subset_of_clopen_component c.base c.continuous hcomponents
        ⟨i.isClosedMap.isClosed_range, hiOpen.isOpen_range⟩
        (x := i.base (x.hom.base ξ)) (Set.mem_range_self (x.hom.base ξ)) hxy hz
    exact ⟨IsOpenImmersion.lift i q.1 hrange,
      (IsOpenImmersion.lift_fac i q.1 hrange).symm⟩
  refine ⟨fun q q' => Subtype.ext ?_⟩
  obtain ⟨a, ha⟩ := hfactor q
  obtain ⟨a', ha'⟩ := hfactor q'
  have hxa : a = x.hom := by rw [← q.2.2, ha, Category.assoc, hi, Category.comp_id]
  have hxa' : a' = x.hom := by rw [← q'.2.2, ha', Category.assoc, hi, Category.comp_id]
  rw [ha, hxa, ha', hxa']

end AlgebraicGeometry

end
