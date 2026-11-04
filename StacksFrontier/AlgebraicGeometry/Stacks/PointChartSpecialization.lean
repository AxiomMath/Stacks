module

public import StacksFrontier.AlgebraicGeometry.Stacks.FullSubcategoryBaseChangeOpen

/-!
# Specialization along a scheme-valued point of an algebraic stack

Let `𝒳` be an algebraic stack over `S` and `z` a scheme-valued point of `𝒳` with values in `V`.
The map `|V| → |𝒳|` it induces is continuous (Stacks 04XL), so it carries specializations of
points of `V` to specializations in `|𝒳|`. Read on the locus `AlgebraicGeometry.Stack.pointsWithin`
of a set `Ω` of points of `|𝒳|`: if every point of `|T₂|` is a specialization of a point of
`|T₁|` in `V`, and every point of `|𝒳|` seen by `z T₁` lies in `Ω`, then every point seen by
`z T₂` lies in the closure of `Ω`.

## Main results

* `AlgebraicGeometry.Stack.pointsWithin_closure_of_specializes`: the locus of the closure of `Ω`
  contains `z T₂` when the locus of `Ω` contains `z T₁` and `|T₂|` specializes from `|T₁|`.
* `AlgebraicGeometry.Stack.pointsWithin_closure_of_isHomLift_of_specializes`: the same statement
  for objects `x₁`, `x₂` of `𝒳` with morphisms to a common object `y₀`.

## References

* [Stacks Project, Tag 04XL](https://stacks.math.columbia.edu/tag/04XL)
* [Stacks Project, Tag 0E86](https://stacks.math.columbia.edu/tag/0E86)
-/

@[expose] public section

open CategoryTheory

universe u w

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (𝒳 : AlgebraicStacks.{u, w} B S hS) {V : BigFppfOver B S hS}
  (z : BigFppfOver B V.left.1 V.left.2 ⥤ 𝒳.val.val.obj)
  (hz : z ⋙ 𝒳.val.val.p = Over.map V.hom)

include hz in
/-- The closure of the set of points of `V` that a scheme-valued point carries into `Ω` lies in
the set of points carried into the closure of `Ω`: the map `|V| → |𝒳|` is continuous. -/
theorem closure_pointChartSchemePointSet_subset
    (Ω : Set (points B S hS 𝒳.val.val 𝒳.val.property)) :
    closure (pointChartSchemePointSet B S hS 𝒳 z hz Ω) ⊆
      pointChartSchemePointSet B S hS 𝒳 z hz (@closure _ (pointTopology B S hS 𝒳.val) Ω) := by
  let := Space.pointTopology B S hS (yoneda.obj V)
  let := pointTopology B S hS 𝒳.val
  set e := Space.schemePointsHomeomorph B S hS V
  set c := spacePointMap B S hS (yoneda.obj V) 𝒳.val (pointChart B S hS 𝒳 z hz)
  have hc : Continuous c := continuous_spacePointMap B S hS (yoneda.obj V)
    (isAlgebraicSpace_yoneda B S hS V) 𝒳.val _
  have himg : ∀ Ω' : Set (points B S hS 𝒳.val.val 𝒳.val.property),
      pointChartSchemePointSet B S hS 𝒳 z hz Ω' = e '' (c ⁻¹' Ω') := fun _ => rfl
  rw [himg, himg, ← e.image_closure]
  exact Set.image_mono (hc.closure_preimage_subset Ω)

include hz in
/-- **Specialization on a scheme-valued point.** Let `z` be a scheme-valued point of `𝒳` with
values in `V`, and `T₁`, `T₂` schemes over `V` such that every point of `V` in the image of `T₂`
is a specialization of a point in the image of `T₁`. If every point of `|𝒳|` seen by `z T₁`
lies in `Ω`, then every point seen by `z T₂` lies in the closure of `Ω`. -/
theorem pointsWithin_closure_of_specializes
    (Ω : Set (points B S hS 𝒳.val.val 𝒳.val.property))
    {T₁ T₂ : BigFppfOver B V.left.1 V.left.2}
    (hspec : ∀ v₂ ∈ Set.range (B.inclusion.map T₂.hom),
      ∃ v₁ ∈ Set.range (B.inclusion.map T₁.hom), v₁ ⤳ v₂)
    (h₁ : pointsWithin 𝒳 Ω (z.obj T₁)) :
    pointsWithin 𝒳 (@closure _ (pointTopology B S hS 𝒳.val) Ω) (z.obj T₂) := by
  rw [pointsWithin_iff_range_subset_pointChartSchemePointSet B S hS 𝒳 z hz] at h₁ ⊢
  intro v₂ hv₂
  obtain ⟨v₁, hv₁, hsp⟩ := hspec v₂ hv₂
  exact closure_pointChartSchemePointSet_subset B S hS 𝒳 z hz Ω
    (closure_mono (Set.singleton_subset_iff.mpr (h₁ hv₁))
      (specializes_iff_mem_closure.mp hsp))

section ObjectSpecialization

variable {B S hS} {𝒳}

/-- A morphism `x ⟶ y₀` of `𝒳` over `a : T ⟶ V` identifies `x` with the value at `T` of a
scheme-valued point classifying `y₀`. -/
theorem nonempty_iso_obj_of_isHomLift {V : BigFppfOver B S hS} {y₀ : 𝒳.val.val.obj}
    (G : Over V ⥤ 𝒳.val.val.obj) (hGq : G ⋙ 𝒳.val.val.p = Over.forget V)
    (ξ : G.obj (Over.mk (𝟙 V)) ≅ y₀) (hξ : 𝒳.val.val.p.IsHomLift (𝟙 V) ξ.hom)
    {T : BigFppfOver B S hS} (a : T ⟶ V) {x : 𝒳.val.val.obj} (m : x ⟶ y₀)
    [𝒳.val.val.p.IsHomLift a m] :
    Nonempty (x ≅ (Over.iteratedSliceBackward V ⋙ G).obj
      (Over.mk a.left : BigFppfOver B V.left.1 V.left.2)) := by
  let β : (Over.iteratedSliceBackward V).obj (Over.mk a.left : BigFppfOver B V.left.1 V.left.2) ⟶
      Over.mk (𝟙 V) := Over.homMk (Over.homMk a.left) (by ext; rfl)
  let m' := G.map β ≫ ξ.hom
  have hdom : 𝒳.val.val.p.obj ((Over.iteratedSliceBackward V ⋙ G).obj
      (Over.mk a.left : BigFppfOver B V.left.1 V.left.2)) = T := by
    rw [← Functor.comp_obj, Functor.assoc, hGq]
    show (Over.mk (a.left ≫ V.hom) : BigFppfOver B S hS) = T
    exact CostructuredArrow.obj_ext _ _ rfl (by simp)
  have hcod : 𝒳.val.val.p.obj y₀ = V := IsHomLift.codomain_eq 𝒳.val.val.p (𝟙 V) ξ.hom
  have : 𝒳.val.val.p.IsHomLift a m' := by
    refine IsHomLift.of_fac 𝒳.val.val.p a m' hdom hcod ?_
    have h1 := Functor.congr_hom hGq β
    have h2 := IsHomLift.fac' 𝒳.val.val.p (𝟙 V) ξ.hom
    ext
    simp only [m', Functor.map_comp, h2, Functor.comp_map] at h1 ⊢
    rw [h1]
    simp [β]
    rfl
  exact ⟨Stacks.RepresentableMorphism.ClassifyingFunctor.vertIso 𝒳.val.val.p 𝒳.val.property a m m'
    inferInstance inferInstance⟩

/-- **Specialization along morphisms to an object.** Let `y₀` be an object of `𝒳` over `V` and
`m₁ : x₁ ⟶ y₀`, `m₂ : x₂ ⟶ y₀` morphisms over `a₁ : T₁ ⟶ V` and `a₂ : T₂ ⟶ V`. If every point of
`V` in the image of `T₂` is a specialization of a point in the image of `T₁`, and every point of
`|𝒳|` seen by `x₁` lies in `Ω`, then every point seen by `x₂` lies in the closure of `Ω`. -/
theorem pointsWithin_closure_of_isHomLift_of_specializes
    (Ω : Set (points B S hS 𝒳.val.val 𝒳.val.property))
    {V : BigFppfOver B S hS} {y₀ : 𝒳.val.val.obj} (hy₀ : 𝒳.val.val.p.obj y₀ = V)
    {T₁ T₂ : BigFppfOver B S hS} (a₁ : T₁ ⟶ V) (a₂ : T₂ ⟶ V) {x₁ x₂ : 𝒳.val.val.obj}
    (m₁ : x₁ ⟶ y₀) (m₂ : x₂ ⟶ y₀) [𝒳.val.val.p.IsHomLift a₁ m₁]
    [𝒳.val.val.p.IsHomLift a₂ m₂]
    (hspec : ∀ v₂ ∈ Set.range (B.inclusion.map a₂.left),
      ∃ v₁ ∈ Set.range (B.inclusion.map a₁.left), v₁ ⤳ v₂)
    (h₁ : pointsWithin 𝒳 Ω x₁) :
    pointsWithin 𝒳 (@closure _ (pointTopology B S hS 𝒳.val) Ω) x₂ := by
  obtain ⟨G, hGq, ξ, hξ⟩ :=
    Stacks.RepresentableMorphism.ClassifyingFunctor.exists_classifying_functor 𝒳.val.val.p
      𝒳.val.property V y₀ hy₀
  let z := Over.iteratedSliceBackward V ⋙ G
  have hz : z ⋙ 𝒳.val.val.p = Over.map V.hom := by
    dsimp [z]
    rw [Functor.assoc, hGq]
    exact Over.iteratedSliceBackward_forget V
  obtain ⟨e₁⟩ := nonempty_iso_obj_of_isHomLift G hGq ξ hξ a₁ m₁
  obtain ⟨e₂⟩ := nonempty_iso_obj_of_isHomLift G hGq ξ hξ a₂ m₂
  exact pointsWithin_of_hom 𝒳 _ e₂.hom
    (pointsWithin_closure_of_specializes B S hS 𝒳 z hz Ω (T₁ := Over.mk a₁.left)
      (T₂ := Over.mk a₂.left) hspec
      (pointsWithin_of_hom 𝒳 _ e₁.inv h₁))

end ObjectSpecialization

end AlgebraicGeometry.Stack

end
