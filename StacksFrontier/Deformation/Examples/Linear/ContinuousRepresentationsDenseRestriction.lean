module

public import StacksFrontier.Deformation.Examples.Linear.ContinuousRepresentationsRimSchlessinger
public import StacksFrontier.Deformation.PredeformationTangent.DifferentialLinear
public import StacksFrontier.Deformation.Representation.Hull
public import StacksFrontier.Deformation.Smooth.IsomorphismClasses

/-!
# Restricting a continuous deformation to a dense subgroup

Let `Γ` be a topological group, `H ≤ Γ` a subgroup and `ρ₀` a finite-dimensional continuous
representation of `Γ`. Restricting the action along `H → Γ` carries a continuous deformation
of `ρ₀` to a deformation of `ρ₀|_H` in the sense of Stacks 0D3J, and the resulting functor is
fully faithful as soon as `H` is dense: a continuous representation is locally constant, so the
locus where an `H`-equivariant map is `Γ`-equivariant is closed and contains `H`.

Consequently the differential of the restriction is an injective `k`-linear map of tangent
spaces, so the tangent space of the continuous deformation category of `ρ₀` is finite
dimensional whenever that of the deformation category of `ρ₀|_H` is. For `H` finitely
generated the latter is Stacks 0DVT.

## Main definitions

* `Deformation.Examples.FiniteProjectiveRepresentation.restrictToSubgroup`: a finite projective
  representation of `Γ`, read as one of `H` in the presentation of Stacks 0D3J.
* `Deformation.Examples.FiniteProjectiveRepresentation.restrictContinuousBasedFunctor`: the
  induced morphism of deformation categories over `𝒞_Λ`.

## Main results

* `Deformation.finiteDimensional_artinianTangentSpace_of_fullyFaithful`: a fully faithful
  morphism of predeformation categories inherits finite-dimensionality of the tangent space
  from its target.
* `Deformation.finiteDimensional_artinianTangentSpace_of_essSurj`: a morphism which is
  essentially surjective on every fibre passes finite-dimensionality of the tangent space on
  to its target.
* `Deformation.Examples.FiniteProjectiveRepresentation.equivariant_of_dense_subgroup`: a map of
  continuous representations which is equivariant for a dense subgroup is equivariant.
* `Deformation.Examples.FiniteProjectiveRepresentation.full_restrictContinuousBasedFunctor` and
  `faithful_restrictContinuousBasedFunctor`: restriction to a dense subgroup is fully faithful.

## Implementation notes

The two parallel presentations of the category of Stacks 0D3J — `Deformation.Examples.
FiniteProjectiveRepresentation`, in which the continuous theory is written, and
`Deformation.RepresentationCategory`, in which Stacks 0DVT is written — have the same fields,
so the restriction functor is the identity on the coefficient algebra, the module and the
semilinear map, and the comparison of their special-fibre objects is the identity morphism.

Injectivity of the differential is injectivity of the map on fibrewise isomorphism classes at
the dual numbers, which holds at every coefficient algebra: a fully faithful based functor
induces a fully faithful functor on each strict fibre, and such a functor reflects
isomorphism.

## References

* [Stacks Project, Tag 0DVW](https://stacks.math.columbia.edu/tag/0DVW)
* [Stacks Project, Tag 0DVT](https://stacks.math.columbia.edu/tag/0DVT)
* [Stacks Project, Tag 0D3J](https://stacks.math.columbia.edu/tag/0D3J)
* [Stacks Project, Tag 0D3K](https://stacks.math.columbia.edu/tag/0D3K)
-/

@[expose] public noncomputable section

open CategoryTheory

namespace Deformation

universe u v w u₁ v₁ u₂ v₂ m g

/-! ### Fibrewise classes along a fully faithful based functor -/

section Fibres

variable {C : Type u} [Category.{v} C]
  {𝓕 : BasedCategory.{v₁, u₁} C} {𝓖 : BasedCategory.{v₂, u₂} C}

/-- The functor induced on a strict fibre by a faithful based functor is faithful. -/
theorem faithful_fiberFunctor (φ : BasedFunctor 𝓕 𝓖) [φ.toFunctor.Faithful] (A : C) :
    (fiberFunctor φ A).Faithful where
  map_injective {x y} f g h :=
    Functor.Fiber.hom_ext (φ.toFunctor.map_injective (congrArg Functor.Fiber.fiberInclusion.map h))

/-- The functor induced on a strict fibre by a fully faithful based functor is full. -/
theorem full_fiberFunctor (φ : BasedFunctor 𝓕 𝓖) [φ.toFunctor.Full] [φ.toFunctor.Faithful]
    (A : C) : (fiberFunctor φ A).Full where
  map_surjective {x y} g := by
    obtain ⟨h, hh⟩ := φ.toFunctor.map_surjective g.val
    have : 𝓖.p.IsHomLift (𝟙 A) (φ.toFunctor.map h) := by
      rw [hh]; exact g.2
    exact ⟨⟨h, BasedFunctor.isHomLift_map φ (𝟙 A) h⟩, Functor.Fiber.hom_ext hh⟩

/-- A fully faithful based functor is injective on fibrewise isomorphism classes: its fibre
functors reflect isomorphism, and the classes are the quotients by fibrewise isomorphism. -/
theorem mapIsomorphismClasses_injective
    (h𝓕 : IsCofiberedInGroupoids 𝓕.p) (h𝓖 : IsCofiberedInGroupoids 𝓖.p)
    (φ : BasedFunctor 𝓕 𝓖) [φ.toFunctor.Full] [φ.toFunctor.Faithful] (A : C) :
    Function.Injective (mapIsomorphismClasses h𝓕 h𝓖 φ A) := by
  let : (fiberFunctor φ A).Full := full_fiberFunctor φ A
  let : (fiberFunctor φ A).Faithful := faithful_fiberFunctor φ A
  intro z z' hzz'
  obtain ⟨x, rfl⟩ := classOf_surjective 𝓕 h𝓕 A z
  obtain ⟨y, rfl⟩ := classOf_surjective 𝓕 h𝓕 A z'
  rw [mapIsomorphismClasses_classOf, mapIsomorphismClasses_classOf] at hzz'
  have hq := congrArg (cast (isomorphismClasses_obj 𝓖 h𝓖 A)) hzz'
  rw [classOf_eq, classOf_eq] at hq
  obtain ⟨i⟩ : Nonempty ((fiberFunctor φ A).obj x ≅ (fiberFunctor φ A).obj y) :=
    Quotient.exact hq
  exact classOf_eq_of_isIsomorphic 𝓕 h𝓕 x y ⟨(fiberFunctor φ A).preimageIso i⟩

/-- A based functor whose fibre functor over `A` is essentially surjective is surjective on
fibrewise isomorphism classes over `A`. -/
theorem mapIsomorphismClasses_surjective
    (h𝓕 : IsCofiberedInGroupoids 𝓕.p) (h𝓖 : IsCofiberedInGroupoids 𝓖.p)
    (φ : BasedFunctor 𝓕 𝓖) (A : C) (hess : (fiberFunctor φ A).EssSurj) :
    Function.Surjective (mapIsomorphismClasses h𝓕 h𝓖 φ A) := by
  intro z
  obtain ⟨y, rfl⟩ := classOf_surjective 𝓖 h𝓖 A z
  obtain ⟨x, ⟨i⟩⟩ := Functor.EssSurj.mem_essImage (F := fiberFunctor φ A) y
  exact ⟨classOf 𝓕 h𝓕 x, (mapIsomorphismClasses_classOf h𝓕 h𝓖 φ x).trans
    (classOf_eq_of_isIsomorphic 𝓖 h𝓖 _ y ⟨i⟩)⟩

end Fibres

/-! ### Finite-dimensionality along a fully faithful morphism -/

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]

/-- **The tangent space of a predeformation category is finite dimensional as soon as that of
a target of a fully faithful morphism is.** The differential of such a morphism is `k`-linear
by Stacks 06IJ and injective because the morphism reflects fibrewise isomorphism. -/
theorem finiteDimensional_artinianTangentSpace_of_fullyFaithful
    (𝓕 : BasedCategory.{v₁, u₁} (ArtinianLocalAlgCat.{u, w, w} Λ k))
    (𝓖 : BasedCategory.{v₂, u₂} (ArtinianLocalAlgCat.{u, w, w} Λ k))
    (h𝓕 : IsPredeformationCategory 𝓕.p) (h𝓖 : IsPredeformationCategory 𝓖.p)
    (hS2𝓕 : SchlessingerConditionS2
      (CategoryOfElements.π (isomorphismClasses 𝓕 h𝓕.cofibered)))
    (hS2𝓖 : SchlessingerConditionS2
      (CategoryOfElements.π (isomorphismClasses 𝓖 h𝓖.cofibered)))
    (φ : BasedFunctor 𝓕 𝓖) (hfull : φ.toFunctor.Full) (hfaithful : φ.toFunctor.Faithful)
    (hfin :
      letI : Fact (IsPredeformationCategory 𝓖.p) := ⟨h𝓖⟩
      letI : Fact (SchlessingerConditionS2
        (CategoryOfElements.π (isomorphismClasses 𝓖 h𝓖.cofibered))) := ⟨hS2𝓖⟩
      FiniteDimensional k (artinianTangentSpace Λ k (isomorphismClasses 𝓖 h𝓖.cofibered))) :
    letI : Fact (IsPredeformationCategory 𝓕.p) := ⟨h𝓕⟩
    letI : Fact (SchlessingerConditionS2
      (CategoryOfElements.π (isomorphismClasses 𝓕 h𝓕.cofibered))) := ⟨hS2𝓕⟩
    FiniteDimensional k (artinianTangentSpace Λ k (isomorphismClasses 𝓕 h𝓕.cofibered)) := by
  let : φ.toFunctor.Full := hfull
  let : φ.toFunctor.Faithful := hfaithful
  let : Fact (IsPredeformationCategory 𝓕.p) := ⟨h𝓕⟩
  let : Fact (IsPredeformationCategory 𝓖.p) := ⟨h𝓖⟩
  let : Fact (SchlessingerConditionS2
    (CategoryOfElements.π (isomorphismClasses 𝓕 h𝓕.cofibered))) := ⟨hS2𝓕⟩
  let : Fact (SchlessingerConditionS2
    (CategoryOfElements.π (isomorphismClasses 𝓖 h𝓖.cofibered))) := ⟨hS2𝓖⟩
  let : FiniteDimensional k (artinianTangentSpace Λ k
    (isomorphismClasses 𝓖 h𝓖.cofibered)) := hfin
  exact FiniteDimensional.of_injective
    (IsLinearMap.mk' _ (differential_isLinearMap 𝓕 𝓖 h𝓕 h𝓖 hS2𝓕 hS2𝓖 φ))
    (mapIsomorphismClasses_injective h𝓕.cofibered h𝓖.cofibered φ _)

/-- **The tangent space of the target of a morphism of predeformation categories is finite
dimensional as soon as that of the source is, provided the morphism is essentially surjective
on every fibre.** The differential is then `k`-linear by Stacks 06IJ and surjective. -/
theorem finiteDimensional_artinianTangentSpace_of_essSurj
    (𝓕 : BasedCategory.{v₁, u₁} (ArtinianLocalAlgCat.{u, w, w} Λ k))
    (𝓖 : BasedCategory.{v₂, u₂} (ArtinianLocalAlgCat.{u, w, w} Λ k))
    (h𝓕 : IsPredeformationCategory 𝓕.p) (h𝓖 : IsPredeformationCategory 𝓖.p)
    (hS2𝓕 : SchlessingerConditionS2
      (CategoryOfElements.π (isomorphismClasses 𝓕 h𝓕.cofibered)))
    (hS2𝓖 : SchlessingerConditionS2
      (CategoryOfElements.π (isomorphismClasses 𝓖 h𝓖.cofibered)))
    (φ : BasedFunctor 𝓕 𝓖)
    (hess : ∀ A : ArtinianLocalAlgCat.{u, w, w} Λ k, (fiberFunctor φ A).EssSurj)
    (hfin :
      letI : Fact (IsPredeformationCategory 𝓕.p) := ⟨h𝓕⟩
      letI : Fact (SchlessingerConditionS2
        (CategoryOfElements.π (isomorphismClasses 𝓕 h𝓕.cofibered))) := ⟨hS2𝓕⟩
      FiniteDimensional k (artinianTangentSpace Λ k (isomorphismClasses 𝓕 h𝓕.cofibered))) :
    letI : Fact (IsPredeformationCategory 𝓖.p) := ⟨h𝓖⟩
    letI : Fact (SchlessingerConditionS2
      (CategoryOfElements.π (isomorphismClasses 𝓖 h𝓖.cofibered))) := ⟨hS2𝓖⟩
    FiniteDimensional k (artinianTangentSpace Λ k (isomorphismClasses 𝓖 h𝓖.cofibered)) := by
  let : Fact (IsPredeformationCategory 𝓕.p) := ⟨h𝓕⟩
  let : Fact (IsPredeformationCategory 𝓖.p) := ⟨h𝓖⟩
  let : Fact (SchlessingerConditionS2
    (CategoryOfElements.π (isomorphismClasses 𝓕 h𝓕.cofibered))) := ⟨hS2𝓕⟩
  let : Fact (SchlessingerConditionS2
    (CategoryOfElements.π (isomorphismClasses 𝓖 h𝓖.cofibered))) := ⟨hS2𝓖⟩
  let : FiniteDimensional k (artinianTangentSpace Λ k
    (isomorphismClasses 𝓕 h𝓕.cofibered)) := hfin
  exact Module.Finite.of_surjective
    (IsLinearMap.mk' _ (differential_isLinearMap 𝓕 𝓖 h𝓕 h𝓖 hS2𝓕 hS2𝓖 φ))
    (mapIsomorphismClasses_surjective h𝓕.cofibered h𝓖.cofibered φ _ (hess _))

end Deformation

namespace Deformation.Examples.FiniteProjectiveRepresentation

open Deformation

universe u w m g

variable {Λ : Type u} {k : Type w} {Γ : Type g}
  [CommRing Λ] [Field k] [Algebra Λ k] [Group Γ] [TopologicalSpace Γ]

/-! ### Restriction of the action to a subgroup -/

/-- A finite projective representation of `Γ` over an Artinian local algebra, read as one of a
subgroup `H` in the presentation of Stacks 0D3J: the coefficient algebra and the module are
unchanged and the action is restricted. -/
public def restrictToSubgroup (H : Subgroup Γ)
    (X : FiniteProjectiveRepresentation.{u, w, w, m} Λ k Γ) :
    Deformation.RepresentationCategory.{u, w, w, m, g} Λ k ↥H where
  base := X.base
  carrier := X.carrier
  action := X.action.comp H.subtype

/-- A morphism of finite projective representations of `Γ`, read as one of the restrictions to
a subgroup `H`. -/
public def restrictToSubgroupHom (H : Subgroup Γ)
    {X Y : FiniteProjectiveRepresentation.{u, w, w, m} Λ k Γ}
    (f : FiniteProjectiveRepresentation.Hom X Y) :
    Deformation.RepresentationCategory.Hom
      (restrictToSubgroup H X) (restrictToSubgroup H Y) where
  base := f.base
  map := f.map
  map_smul := f.map_smul
  equivariant := fun h x => f.equivariant h.1 x
  isBaseChange := f.isBaseChange

/-- Restriction of the action to a subgroup, as a functor from the category of continuous
finite projective representations of `Γ` to the category of Stacks 0D3J for `H`. -/
public def restrictContinuousFunctor (H : Subgroup Γ) :
    (continuousObjects.{u, w, w, m} Λ k Γ).FullSubcategory ⥤
      Deformation.RepresentationCategory.{u, w, w, m, g} Λ k ↥H where
  obj X := restrictToSubgroup H X.obj
  map f := restrictToSubgroupHom H f.hom
  map_id _ := rfl
  map_comp _ _ := rfl

/-! ### Equivariance spreads from a dense subgroup -/

/-- **A map of continuous representations equivariant for a dense subgroup is equivariant.**
Both representations are locally constant, so the locus where the two composites agree is
closed; containing a dense subgroup, it is everything. -/
public theorem equivariant_of_dense_subgroup {H : Subgroup Γ} (hH : Dense (H : Set Γ))
    {X Y : FiniteProjectiveRepresentation.{u, w, w, m} Λ k Γ}
    (hX : IsContinuousRepresentation X.action) (hY : IsContinuousRepresentation Y.action)
    (f : X.carrier →+ Y.carrier)
    (hf : ∀ γ ∈ H, ∀ x, f (X.action γ x) = Y.action γ (f x))
    (γ : Γ) (x : X.carrier) : f (X.action γ x) = Y.action γ (f x) := by
  let : TopologicalSpace (X.carrier → Y.carrier) := ⊥
  have : DiscreteTopology (X.carrier → Y.carrier) :=
    discreteTopology_bot (X.carrier → Y.carrier)
  let : TopologicalSpace (LinearMap.GeneralLinearGroup X.base X.carrier) := ⊥
  have : DiscreteTopology (LinearMap.GeneralLinearGroup X.base X.carrier) :=
    discreteTopology_bot (LinearMap.GeneralLinearGroup X.base X.carrier)
  let : TopologicalSpace (LinearMap.GeneralLinearGroup Y.base Y.carrier) := ⊥
  have : DiscreteTopology (LinearMap.GeneralLinearGroup Y.base Y.carrier) :=
    discreteTopology_bot (LinearMap.GeneralLinearGroup Y.base Y.carrier)
  have hXc : Continuous X.action.asGroupHom := hX
  have hYc : Continuous Y.action.asGroupHom := hY
  exact congrFun (congrFun (Continuous.ext_on hH
    (f := fun δ z => f (X.action δ z)) (g := fun δ z => Y.action δ (f z))
    ((continuous_of_discreteTopology (f := fun u : LinearMap.GeneralLinearGroup X.base X.carrier =>
      fun z => f ((u : Module.End X.base X.carrier) z))).comp hXc)
    ((continuous_of_discreteTopology (f := fun u : LinearMap.GeneralLinearGroup Y.base Y.carrier =>
      fun z => (u : Module.End Y.base Y.carrier) (f z))).comp hYc)
    fun δ hδ => funext (hf δ hδ)) γ) x

/-- Restriction to a dense subgroup is full on continuous representations: the semilinear map
underlying a morphism of the restrictions is already `Γ`-equivariant. -/
public theorem full_restrictContinuousFunctor {H : Subgroup Γ} (hH : Dense (H : Set Γ)) :
    (restrictContinuousFunctor.{u, w, m} (Λ := Λ) (k := k) (Γ := Γ) H).Full where
  map_surjective {X Y} g :=
    ⟨ObjectProperty.homMk
      { base := g.base
        map := g.map
        map_smul := g.map_smul
        equivariant := equivariant_of_dense_subgroup hH X.property Y.property g.map
          (fun γ hγ x => g.equivariant ⟨γ, hγ⟩ x)
        isBaseChange := g.isBaseChange }, rfl⟩

/-- Restriction to a subgroup is faithful: a morphism of the category of Stacks 0D3J is
determined by its map of coefficient algebras and its semilinear map. -/
public theorem faithful_restrictContinuousFunctor (H : Subgroup Γ) :
    (restrictContinuousFunctor.{u, w, m} (Λ := Λ) (k := k) (Γ := Γ) H).Faithful where
  map_injective {X Y} f g h := by
    apply ObjectProperty.hom_ext
    exact FiniteProjectiveRepresentation.Hom.ext
      (congrArg (fun q : Deformation.RepresentationCategory.Hom
        (restrictToSubgroup H X.obj) (restrictToSubgroup H Y.obj) => q.base) h)
      (congrArg (fun q : Deformation.RepresentationCategory.Hom
        (restrictToSubgroup H X.obj) (restrictToSubgroup H Y.obj) => q.map) h)

/-! ### The induced morphism of deformation categories -/

variable (V : Type m) [AddCommGroup V] [Module k V] [Module.Finite k V]

/-- Restricting the action of the special-fibre object `(k, V, ρ₀)` to a subgroup `H` gives the
special-fibre object `(k, V, ρ₀|_H)` of the representation deformation category: the two
presentations have the same fields, so the comparison is the identity. -/
public def restrictSpecialFiberHom (H : Subgroup Γ) (ρ₀ : Representation k Γ V) :
    restrictToSubgroup H (specialFiber (Λ := Λ) V ρ₀) ⟶
      Deformation.RepresentationCategory.specialFiber (Λ := Λ) V (ρ₀.comp H.subtype) where
  base := 𝟙 _
  map := AddMonoidHom.id V
  map_smul := fun _ _ => rfl
  equivariant := fun _ _ => rfl
  isBaseChange := by
    change IsBaseChange k (LinearMap.id : V →ₗ[k] V)
    exact IsBaseChange.ofEquiv (LinearEquiv.refl k V)

/-- The inverse comparison of the two special-fibre objects. -/
public def restrictSpecialFiberInv (H : Subgroup Γ) (ρ₀ : Representation k Γ V) :
    Deformation.RepresentationCategory.specialFiber (Λ := Λ) V (ρ₀.comp H.subtype) ⟶
      restrictToSubgroup H (specialFiber (Λ := Λ) V ρ₀) where
  base := 𝟙 _
  map := AddMonoidHom.id V
  map_smul := fun _ _ => rfl
  equivariant := fun _ _ => rfl
  isBaseChange := by
    change IsBaseChange k (LinearMap.id : V →ₗ[k] V)
    exact IsBaseChange.ofEquiv (LinearEquiv.refl k V)

/-- The comparison of the two special-fibre objects is an isomorphism. -/
public instance isIso_restrictSpecialFiberHom (H : Subgroup Γ) (ρ₀ : Representation k Γ V) :
    IsIso (restrictSpecialFiberHom (Λ := Λ) V H ρ₀) :=
  ⟨⟨restrictSpecialFiberInv V H ρ₀,
    Deformation.RepresentationCategory.Hom.ext (Category.comp_id _) rfl,
    Deformation.RepresentationCategory.Hom.ext (Category.comp_id _) rfl⟩⟩

/-- **Restriction to a subgroup, as a morphism of deformation categories over `𝒞_Λ`**: it
carries a continuous deformation of `ρ₀` to a deformation of `ρ₀|_H` without changing the
coefficient algebra. -/
public def restrictContinuousBasedFunctor (H : Subgroup Γ) (ρ₀ : Representation k Γ V)
    (hρ₀ : IsContinuousRepresentation ρ₀) :
    BasedFunctor
      (BasedCategory.ofFunctor (Deformation.objectsOverFunctor
        (continuousProjection.{u, w, w, m} (Λ := Λ) (k := k) (Γ := Γ))
        (continuousSpecialFiber (Λ := Λ) V ρ₀ hρ₀)))
      (BasedCategory.ofFunctor
        (Deformation.deformationCategoryProjection (Λ := Λ) V (ρ₀.comp H.subtype))) where
  toFunctor :=
    Over.post (restrictContinuousFunctor.{u, w, m} (Λ := Λ) (k := k) (Γ := Γ) H) ⋙
      Over.map (X := restrictToSubgroup H (specialFiber (Λ := Λ) V ρ₀))
        (Y := Deformation.RepresentationCategory.specialFiber (Λ := Λ) V (ρ₀.comp H.subtype))
        (restrictSpecialFiberHom (Λ := Λ) V H ρ₀)
  w := rfl

/-- The restriction morphism to a dense subgroup is full. -/
public theorem full_restrictContinuousBasedFunctor {H : Subgroup Γ} (hH : Dense (H : Set Γ))
    (ρ₀ : Representation k Γ V) (hρ₀ : IsContinuousRepresentation ρ₀) :
    (restrictContinuousBasedFunctor (Λ := Λ) V H ρ₀ hρ₀).toFunctor.Full := by
  let : (restrictContinuousFunctor.{u, w, m} (Λ := Λ) (k := k) (Γ := Γ) H).Full :=
    full_restrictContinuousFunctor hH
  let : (restrictContinuousFunctor.{u, w, m} (Λ := Λ) (k := k) (Γ := Γ) H).Faithful :=
    faithful_restrictContinuousFunctor H
  show (Over.post (X := continuousSpecialFiber (Λ := Λ) V ρ₀ hρ₀)
    (restrictContinuousFunctor.{u, w, m} (Λ := Λ) (k := k) (Γ := Γ) H) ⋙
    Over.map (X := restrictToSubgroup H (specialFiber (Λ := Λ) V ρ₀))
    (Y := Deformation.RepresentationCategory.specialFiber (Λ := Λ) V (ρ₀.comp H.subtype))
    (restrictSpecialFiberHom (Λ := Λ) V H ρ₀)).Full
  let hpost : (Over.post (X := continuousSpecialFiber (Λ := Λ) V ρ₀ hρ₀)
    (restrictContinuousFunctor.{u, w, m} (Λ := Λ) (k := k) (Γ := Γ) H)).Full := inferInstance
  let hmap : (Over.map (X := restrictToSubgroup H (specialFiber (Λ := Λ) V ρ₀))
    (Y := Deformation.RepresentationCategory.specialFiber (Λ := Λ) V (ρ₀.comp H.subtype))
    (restrictSpecialFiberHom (Λ := Λ) V H ρ₀)).Full := inferInstance
  exact @Functor.Full.comp _ _ _ _ _ _ _ _ hpost hmap

/-- The restriction morphism to a subgroup is faithful. -/
public theorem faithful_restrictContinuousBasedFunctor (H : Subgroup Γ)
    (ρ₀ : Representation k Γ V) (hρ₀ : IsContinuousRepresentation ρ₀) :
    (restrictContinuousBasedFunctor (Λ := Λ) V H ρ₀ hρ₀).toFunctor.Faithful := by
  let : (restrictContinuousFunctor.{u, w, m} (Λ := Λ) (k := k) (Γ := Γ) H).Faithful :=
    faithful_restrictContinuousFunctor H
  show (Over.post (X := continuousSpecialFiber (Λ := Λ) V ρ₀ hρ₀)
    (restrictContinuousFunctor.{u, w, m} (Λ := Λ) (k := k) (Γ := Γ) H) ⋙
    Over.map (X := restrictToSubgroup H (specialFiber (Λ := Λ) V ρ₀))
    (Y := Deformation.RepresentationCategory.specialFiber (Λ := Λ) V (ρ₀.comp H.subtype))
    (restrictSpecialFiberHom (Λ := Λ) V H ρ₀)).Faithful
  let hpost : (Over.post (X := continuousSpecialFiber (Λ := Λ) V ρ₀ hρ₀)
    (restrictContinuousFunctor.{u, w, m} (Λ := Λ) (k := k) (Γ := Γ) H)).Faithful := inferInstance
  let hmap : (Over.map (X := restrictToSubgroup H (specialFiber (Λ := Λ) V ρ₀))
    (Y := Deformation.RepresentationCategory.specialFiber (Λ := Λ) V (ρ₀.comp H.subtype))
    (restrictSpecialFiberHom (Λ := Λ) V H ρ₀)).Faithful := inferInstance
  exact @Functor.Faithful.comp _ _ _ _ _ _ _ _ hpost hmap

end Deformation.Examples.FiniteProjectiveRepresentation

end
