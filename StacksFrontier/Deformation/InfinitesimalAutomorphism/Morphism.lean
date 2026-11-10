module

public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.CategoryTheory.Conj
public import StacksFrontier.Deformation.InfinitesimalAutomorphism.TangentVectorSpace

/-!
# Infinitesimal automorphisms under a morphism of cofibered categories

Let `φ : 𝓕 → 𝓖` be a morphism of categories cofibered in groupoids over `𝒞_Λ`, both satisfying
(RS), and let `x₀` be an object of `𝓕`. Applying `φ` to an infinitesimal
automorphism of a dual-number pushforward of `x₀` and transporting the result along the
canonical comparison of pushforwards produces an infinitesimal automorphism of a dual-number
pushforward of `φ(x₀)`. This file builds the resulting map and shows that it is `k`-linear for
the vector-space structures of Tag 06JV.

## Main definitions

* `Deformation.fiberFunctorOfComp`: the functor between fibres induced by a functor over the
  base.
* `Deformation.comparisonPushforward`, `Deformation.comparisonPushforwardInv`: the mutually
  inverse comparison maps between the chosen pushforward of `φ(x₀)` and the image of the
  chosen pushforward of `x₀`.
* `Deformation.inducedAutomorphismHom`: the resulting homomorphism of fibre automorphism
  groups.
* `Deformation.inducedInfinitesimalAutomorphismHom`: its restriction to infinitesimal
  automorphisms.
* `Deformation.inducedInfinitesimalFun`: the resulting map on tangent spaces at the identity.
* `Deformation.inducedInfinitesimalLinearMap`: **Stacks 07W6**, the induced `k`-linear map
  `Inf_{x₀}(𝓕) → Inf_{φ(x₀)}(𝓖)`.

## Main results

* `Deformation.comparisonPushforward_naturality`: the comparison is natural in the arrow out
  of the base.
* `Deformation.inducedAutomorphismHom_transportAut`: pushing an automorphism along `φ` commutes
  with transport between chosen pushforwards.
* `Deformation.inducedInfinitesimalLinearMap_apply`: the value of the induced map on an
  infinitesimal automorphism is the conjugate by the comparison of its image under `φ`.
* `Deformation.exists_inducedInfinitesimalLinearMap`: **Stacks 07W6** for a morphism presented
  as a functor commuting with the two projections.

## Implementation notes

The source projection is taken to be the composite of the morphism with the target projection.
A morphism of categories over `𝒞_Λ` is a functor `φ` together with an equality `φ ⋙ q = p` of
projections, and substituting that equality is exactly the normalization performed here; the
statement for a general `p` carrying the equality as a hypothesis is
`Deformation.exists_inducedInfinitesimalLinearMap`. Keeping the composite form means that the
dual numbers under the base of `x₀` and under the base of `φ(x₀)` are the same object, so no
transport along the equality appears in the construction.

Both comparison maps are produced from a universal property, rather than one of them as the
inverse of the other, so that each is visibly a morphism over the identity of the dual numbers.

Linearity is checked against the two properties that pin the vector-space structure of Tag
06JV: addition is composition of automorphisms, and the scalar action is transport along the
scaling of the infinitesimal coordinate. The induced map is a group homomorphism, which gives
additivity, and it commutes with transport, which gives homogeneity.

As in Tag 06JV, nothing is assumed about the base object of `x₀`: the vector-space structure
is that of the tangent space at the identity of the automorphism functor of `x₀`, which is the
group of infinitesimal automorphisms of its dual-number pushforward. The source's hypothesis
that `x₀` lies over the residue field is therefore not needed.

## References

* [Stacks Project, Tag 06GJ](https://stacks.math.columbia.edu/tag/06GJ)
* [Stacks Project, Tag 06J2](https://stacks.math.columbia.edu/tag/06J2)
* [Stacks Project, Tag 06JT](https://stacks.math.columbia.edu/tag/06JT)
* [Stacks Project, Tag 06JV](https://stacks.math.columbia.edu/tag/06JV)
* [Stacks Project, Tag 06JX](https://stacks.math.columbia.edu/tag/06JX)
* [Stacks Project, Tag 07W6](https://stacks.math.columbia.edu/tag/07W6)
-/

@[expose] public section

namespace Deformation

open CategoryTheory

universe u v w u₁ v₁ u₂ v₂ u₃ v₃

/-! ### Comparison of chosen pushforwards along a morphism -/

section Comparison

variable {F : Type u₁} [Category.{v₁} F] {G : Type u₂} [Category.{v₂} G]
  {C : Type u₃} [Category.{v₃} C] {q : G ⥤ C} (Φ : F ⥤ G)

/-- A morphism lifting an arrow of the base for the composite projection has its image
lifting the same arrow for the target projection. -/
public theorem isHomLift_map_of_comp {R S : C} {a b : F} (f : R ⟶ S) (φ : a ⟶ b)
    (h : (Φ ⋙ q).IsHomLift f φ) : q.IsHomLift f (Φ.map φ) :=
  let := h
  IsHomLift.of_fac' q f (Φ.map φ) (IsHomLift.domain_eq (Φ ⋙ q) f φ)
    (IsHomLift.codomain_eq (Φ ⋙ q) f φ) (IsHomLift.fac' (Φ ⋙ q) f φ)

/-- The converse of `Deformation.isHomLift_map_of_comp`: a morphism whose image under `Φ`
lifts an arrow of the base for the target projection already lifts the same arrow for the
composite projection. This needs no hypothesis on `Φ`, since the composite's object and arrow
maps are literally those of `Φ` followed by those of `q`. -/
public theorem isHomLift_of_comp_map {R S : C} {a b : F} (f : R ⟶ S) (φ : a ⟶ b)
    (h : q.IsHomLift f (Φ.map φ)) : (Φ ⋙ q).IsHomLift f φ :=
  let := h
  IsHomLift.of_fac' (Φ ⋙ q) f φ (IsHomLift.domain_eq q f (Φ.map φ))
    (IsHomLift.codomain_eq q f (Φ.map φ)) (IsHomLift.fac' q f (Φ.map φ))

/-- The functor between the fibres over a fixed object of the base induced by a functor
commuting with the projections. -/
public def fiberFunctorOfComp (S : C) : (Φ ⋙ q).Fiber S ⥤ q.Fiber S where
  obj z := ⟨Φ.obj z.1, z.2⟩
  map f := ⟨Φ.map f.val, isHomLift_map_of_comp Φ (𝟙 S) f.val f.2⟩
  map_id z := Subtype.ext (Φ.map_id z.1)
  map_comp f g := Subtype.ext (Φ.map_comp f.val g.val)

/-- The fibre functor induced by a faithful functor is itself faithful: its underlying map on
morphisms is `Φ.map` on the first component of the comparison subtype, and `Φ.map` is
injective. -/
public instance fiberFunctorOfComp_faithful [Φ.Faithful] (S : C) :
    (fiberFunctorOfComp (q := q) Φ S).Faithful where
  map_injective h := Subtype.ext (Φ.map_injective (congrArg Subtype.val h))

/-- The fibre functor induced by a full functor is itself full: a preimage of the ambient
morphism under `Φ` already lifts the identity for the composite projection, by
`Deformation.isHomLift_of_comp_map`. -/
public instance fiberFunctorOfComp_full [Φ.Full] (S : C) :
    (fiberFunctorOfComp (q := q) Φ S).Full where
  map_surjective {_z _w} e :=
    ⟨⟨Φ.preimage e.val, isHomLift_of_comp_map Φ (𝟙 S) (Φ.preimage e.val)
        ((Φ.map_preimage e.val).symm ▸ e.2)⟩, Subtype.ext (Φ.map_preimage e.val)⟩

variable {x₀ : F} (P : ChosenPushforwardsAt (Φ ⋙ q) x₀)
  (Q : ChosenPushforwardsAt q (Φ.obj x₀))

/-- The image of a chosen inclusion lifts the structure arrow of the undercategory object. -/
public theorem isHomLift_map_inclusion (U : Under ((Φ ⋙ q).obj x₀)) :
    q.IsHomLift U.hom (Φ.map (P.inclusion U)) :=
  isHomLift_map_of_comp Φ U.hom (P.inclusion U) (P.inclusion_cocartesian U).toIsHomLift

/-- The comparison map from the chosen pushforward of `Φ(x₀)` to the image of the chosen
pushforward of `x₀`: the unique vertical map compatible with the two inclusions. -/
public noncomputable def comparisonPushforward (U : Under ((Φ ⋙ q).obj x₀)) :
    (Q.obj U).1 ⟶ Φ.obj (P.obj U).1 :=
  letI := Q.inclusion_cocartesian U
  letI := isHomLift_map_inclusion Φ P U
  Functor.IsStronglyCocartesian.map q U.hom (Q.inclusion U) (Category.comp_id U.hom).symm
    (Φ.map (P.inclusion U))

/-- The comparison map lies over the identity of the target of the arrow. -/
public instance comparisonPushforward_isHomLift (U : Under ((Φ ⋙ q).obj x₀)) :
    q.IsHomLift (𝟙 U.right) (comparisonPushforward Φ P Q U) := by
  dsimp [comparisonPushforward]
  infer_instance

/-- The comparison map is compatible with the two inclusions. -/
@[reassoc]
public theorem inclusion_comp_comparisonPushforward (U : Under ((Φ ⋙ q).obj x₀)) :
    Q.inclusion U ≫ comparisonPushforward Φ P Q U = Φ.map (P.inclusion U) :=
  let := Q.inclusion_cocartesian U
  let := isHomLift_map_inclusion Φ P U
  Functor.IsStronglyCocartesian.fac q U.hom (Q.inclusion U) (Category.comp_id U.hom).symm
    (Φ.map (P.inclusion U))

/-- The comparison map in the other direction, from the image of the chosen pushforward of
`x₀` to the chosen pushforward of `Φ(x₀)`. -/
public noncomputable def comparisonPushforwardInv (hq : IsCofiberedInGroupoids q)
    (U : Under ((Φ ⋙ q).obj x₀)) : Φ.obj (P.obj U).1 ⟶ (Q.obj U).1 :=
  letI := isHomLift_map_inclusion Φ P U
  letI := isStronglyCocartesian_of_isCofiberedInGroupoids hq U.hom (Φ.map (P.inclusion U))
    (isHomLift_map_inclusion Φ P U)
  letI := (Q.inclusion_cocartesian U).toIsHomLift
  Functor.IsStronglyCocartesian.map q U.hom (Φ.map (P.inclusion U))
    (Category.comp_id U.hom).symm (Q.inclusion U)

/-- The second comparison map lies over the identity of the target of the arrow. -/
public instance comparisonPushforwardInv_isHomLift (hq : IsCofiberedInGroupoids q)
    (U : Under ((Φ ⋙ q).obj x₀)) :
    q.IsHomLift (𝟙 U.right) (comparisonPushforwardInv Φ P Q hq U) := by
  dsimp [comparisonPushforwardInv]
  infer_instance

/-- The second comparison map is compatible with the two inclusions. -/
@[reassoc]
public theorem map_inclusion_comp_comparisonPushforwardInv (hq : IsCofiberedInGroupoids q)
    (U : Under ((Φ ⋙ q).obj x₀)) :
    Φ.map (P.inclusion U) ≫ comparisonPushforwardInv Φ P Q hq U = Q.inclusion U :=
  let := isHomLift_map_inclusion Φ P U
  let := isStronglyCocartesian_of_isCofiberedInGroupoids hq U.hom (Φ.map (P.inclusion U))
    (isHomLift_map_inclusion Φ P U)
  let := (Q.inclusion_cocartesian U).toIsHomLift
  Functor.IsStronglyCocartesian.fac q U.hom (Φ.map (P.inclusion U))
    (Category.comp_id U.hom).symm (Q.inclusion U)

/-- The two comparison maps are inverse to each other. -/
@[simp]
public theorem comparisonPushforward_comp_inv (hq : IsCofiberedInGroupoids q)
    (U : Under ((Φ ⋙ q).obj x₀)) :
    comparisonPushforward Φ P Q U ≫ comparisonPushforwardInv Φ P Q hq U =
      𝟙 (Q.obj U).1 := by
  let := Q.inclusion_cocartesian U
  let : q.IsHomLift (𝟙 U.right) (𝟙 (Q.obj U).1) := IsHomLift.id (Q.obj U).2
  refine Functor.IsStronglyCocartesian.ext q U.hom (Q.inclusion U) (𝟙 U.right) ?_
  rw [← Category.assoc, inclusion_comp_comparisonPushforward,
    map_inclusion_comp_comparisonPushforwardInv, Category.comp_id]

/-- The two comparison maps are inverse to each other. -/
@[simp]
public theorem comparisonPushforwardInv_comp (hq : IsCofiberedInGroupoids q)
    (U : Under ((Φ ⋙ q).obj x₀)) :
    comparisonPushforwardInv Φ P Q hq U ≫ comparisonPushforward Φ P Q U =
      𝟙 (Φ.obj (P.obj U).1) := by
  let := isHomLift_map_inclusion Φ P U
  let := isStronglyCocartesian_of_isCofiberedInGroupoids hq U.hom (Φ.map (P.inclusion U))
    (isHomLift_map_inclusion Φ P U)
  let : q.IsHomLift (𝟙 U.right) (𝟙 (Φ.obj (P.obj U).1)) :=
    IsHomLift.id (IsHomLift.codomain_eq q U.hom (Φ.map (P.inclusion U)))
  refine Functor.IsStronglyCocartesian.ext q U.hom (Φ.map (P.inclusion U)) (𝟙 U.right) ?_
  rw [← Category.assoc, map_inclusion_comp_comparisonPushforwardInv,
    inclusion_comp_comparisonPushforward, Category.comp_id]

/-- The comparison map is natural in the arrow out of the base. -/
public theorem comparisonPushforward_naturality {U V : Under ((Φ ⋙ q).obj x₀)} (f : U ⟶ V) :
    comparisonPushforward Φ P Q U ≫ Φ.map (P.map f) =
      Q.map f ≫ comparisonPushforward Φ P Q V := by
  let := Q.inclusion_cocartesian U
  let : q.IsHomLift f.right (Φ.map (P.map f)) :=
    isHomLift_map_of_comp Φ f.right (P.map f) (P.map_isHomLift f)
  refine Functor.IsStronglyCocartesian.ext q U.hom (Q.inclusion U) f.right ?_
  rw [← Category.assoc, inclusion_comp_comparisonPushforward, ← Φ.map_comp, P.inclusion_map,
    ← Category.assoc, Q.inclusion_map, inclusion_comp_comparisonPushforward]

/-- The second comparison map is natural in the arrow out of the base. -/
public theorem comparisonPushforwardInv_naturality (hq : IsCofiberedInGroupoids q)
    {U V : Under ((Φ ⋙ q).obj x₀)} (f : U ⟶ V) :
    Φ.map (P.map f) ≫ comparisonPushforwardInv Φ P Q hq V =
      comparisonPushforwardInv Φ P Q hq U ≫ Q.map f := by
  calc
    Φ.map (P.map f) ≫ comparisonPushforwardInv Φ P Q hq V =
        (comparisonPushforwardInv Φ P Q hq U ≫ comparisonPushforward Φ P Q U) ≫
          Φ.map (P.map f) ≫ comparisonPushforwardInv Φ P Q hq V := by
      rw [comparisonPushforwardInv_comp, Category.id_comp]
    _ = comparisonPushforwardInv Φ P Q hq U ≫
        (comparisonPushforward Φ P Q U ≫ Φ.map (P.map f)) ≫
          comparisonPushforwardInv Φ P Q hq V := by
      simp only [Category.assoc]
    _ = comparisonPushforwardInv Φ P Q hq U ≫
        Q.map f ≫ comparisonPushforward Φ P Q V ≫
          comparisonPushforwardInv Φ P Q hq V := by
      rw [comparisonPushforward_naturality]
      simp only [Category.assoc]
    _ = comparisonPushforwardInv Φ P Q hq U ≫ Q.map f := by
      rw [comparisonPushforward_comp_inv, Category.comp_id]

/-- The comparison of pushforwards, as an isomorphism of the fibre over the arrow's target. -/
public noncomputable def comparisonPushforwardIso (hq : IsCofiberedInGroupoids q)
    (U : Under ((Φ ⋙ q).obj x₀)) :
    Q.obj U ≅ (fiberFunctorOfComp Φ U.right).obj (P.obj U) where
  hom := ⟨comparisonPushforward Φ P Q U, comparisonPushforward_isHomLift Φ P Q U⟩
  inv := ⟨comparisonPushforwardInv Φ P Q hq U, comparisonPushforwardInv_isHomLift Φ P Q hq U⟩
  hom_inv_id := Subtype.ext (comparisonPushforward_comp_inv Φ P Q hq U)
  inv_hom_id := Subtype.ext (comparisonPushforwardInv_comp Φ P Q hq U)

/-- The homomorphism of fibre automorphism groups induced by a morphism over the base:
apply the morphism and conjugate by the comparison of pushforwards. -/
public noncomputable def inducedAutomorphismHom (hq : IsCofiberedInGroupoids q)
    (U : Under ((Φ ⋙ q).obj x₀)) : Aut (P.obj U) →* Aut (Q.obj U) :=
  ((comparisonPushforwardIso Φ P Q hq U).symm.conjAut).toMonoidHom.comp
    ((fiberFunctorOfComp Φ U.right).mapAut (P.obj U))

/-- The automorphism induced by `Φ` is the conjugate by the comparison of the image
automorphism. -/
public theorem inducedAutomorphismHom_hom_val (hq : IsCofiberedInGroupoids q)
    (U : Under ((Φ ⋙ q).obj x₀)) (a : Aut (P.obj U)) :
    (inducedAutomorphismHom Φ P Q hq U a).asIso.hom.val =
      comparisonPushforward Φ P Q U ≫ Φ.map a.asIso.hom.val ≫
        comparisonPushforwardInv Φ P Q hq U := rfl

/-- Pushing an automorphism along `Φ` commutes with transport between chosen
pushforwards. -/
public theorem inducedAutomorphismHom_transportAut (hq : IsCofiberedInGroupoids q)
    {U V : Under ((Φ ⋙ q).obj x₀)} (f : U ⟶ V) (a : Aut (P.obj U)) :
    inducedAutomorphismHom Φ P Q hq V (P.transportAut f a) =
      Q.transportAut f (inducedAutomorphismHom Φ P Q hq U a) := by
  let := Q.map_cocartesian f
  let := (inducedAutomorphismHom Φ P Q hq V (P.transportAut f a)).asIso.hom.2
  let := (Q.transportAut f (inducedAutomorphismHom Φ P Q hq U a)).asIso.hom.2
  apply Aut.ext
  apply Iso.ext
  apply Subtype.ext
  refine Functor.IsStronglyCocartesian.ext q f.right (Q.map f) (𝟙 V.right) ?_
  change Q.map f ≫ comparisonPushforward Φ P Q V ≫
      Φ.map (P.transportHom f a) ≫ comparisonPushforwardInv Φ P Q hq V =
    Q.map f ≫ Q.transportHom f (inducedAutomorphismHom Φ P Q hq U a)
  calc
    Q.map f ≫ comparisonPushforward Φ P Q V ≫
        Φ.map (P.transportHom f a) ≫ comparisonPushforwardInv Φ P Q hq V =
        (Q.map f ≫ comparisonPushforward Φ P Q V) ≫
          Φ.map (P.transportHom f a) ≫ comparisonPushforwardInv Φ P Q hq V := by
      simp only [Category.assoc]
    _ = comparisonPushforward Φ P Q U ≫ Φ.map (P.map f) ≫
          Φ.map (P.transportHom f a) ≫ comparisonPushforwardInv Φ P Q hq V := by
      rw [← comparisonPushforward_naturality]
      simp only [Category.assoc]
    _ = comparisonPushforward Φ P Q U ≫
          (Φ.map (P.map f) ≫ Φ.map (P.transportHom f a)) ≫
            comparisonPushforwardInv Φ P Q hq V := by
      simp only [Category.assoc]
    _ = comparisonPushforward Φ P Q U ≫
          (Φ.map a.asIso.hom.val ≫ Φ.map (P.map f)) ≫
            comparisonPushforwardInv Φ P Q hq V := by
      rw [← Φ.map_comp, ← Φ.map_comp, P.map_transportHom]
    _ = comparisonPushforward Φ P Q U ≫ Φ.map a.asIso.hom.val ≫
          (Φ.map (P.map f) ≫ comparisonPushforwardInv Φ P Q hq V) := by
      simp only [Category.assoc]
    _ = comparisonPushforward Φ P Q U ≫ Φ.map a.asIso.hom.val ≫
          comparisonPushforwardInv Φ P Q hq U ≫ Q.map f := by
      rw [comparisonPushforwardInv_naturality]
    _ = (inducedAutomorphismHom Φ P Q hq U a).asIso.hom.val ≫ Q.map f := by
      rw [inducedAutomorphismHom_hom_val]
      simp only [Category.assoc]
    _ = Q.map f ≫ Q.transportHom f (inducedAutomorphismHom Φ P Q hq U a) :=
      (Q.map_transportHom f (inducedAutomorphismHom Φ P Q hq U a)).symm

/-- If `Φ` is full and faithful, the homomorphism of fibre automorphism groups it induces is
bijective: it factors as the (always bijective) `mapAut` of the induced fully faithful functor
between fibres, `Deformation.fiberFunctorOfComp_full`/`Deformation.fiberFunctorOfComp_faithful`,
followed by conjugation by the comparison isomorphism, which is a group isomorphism. -/
public theorem bijective_inducedAutomorphismHom (hq : IsCofiberedInGroupoids q) [Φ.Full]
    [Φ.Faithful] (U : Under ((Φ ⋙ q).obj x₀)) :
    Function.Bijective (inducedAutomorphismHom Φ P Q hq U) := by
  have hmapAut : Function.Bijective ((fiberFunctorOfComp Φ U.right).mapAut (P.obj U)) :=
    EquivLike.bijective
      (Functor.FullyFaithful.autMulEquivOfFullyFaithful
        (Functor.FullyFaithful.ofFullyFaithful (fiberFunctorOfComp Φ U.right)) (P.obj U))
  have hconjAut : Function.Bijective
      ((comparisonPushforwardIso Φ P Q hq U).symm.conjAut).toMonoidHom :=
    EquivLike.bijective (comparisonPushforwardIso Φ P Q hq U).symm.conjAut
  simpa [inducedAutomorphismHom] using hconjAut.comp hmapAut

end Comparison

/-! ### Composition of morphisms over the base -/

section Composition
universe u₄ v₄

variable {F : Type u₁} [Category.{v₁} F] {G : Type u₂} [Category.{v₂} G]
  {K : Type u₄} [Category.{v₄} K] {C : Type u₃} [Category.{v₃} C]
  (Φ : F ⥤ G) (Ψ : G ⥤ K) (r : K ⥤ C) {x₀ : F}
  (P : ChosenPushforwardsAt (Φ ⋙ Ψ ⋙ r) x₀) (Q : ChosenPushforwardsAt (Ψ ⋙ r) (Φ.obj x₀))
  (R : ChosenPushforwardsAt r (Ψ.obj (Φ.obj x₀)))

/-- The comparison map for a composite morphism factors through the inner comparison map
followed by the image of the outer one: compare at the inner level first, then push forward
and compare again at the outer level. Both sides are the unique vertical arrow over the
identity compatible with the chosen inclusion into `R`, by the universal property of the
strongly cocartesian arrow `R.inclusion`. -/
public theorem comparisonPushforward_comp (U : Under (((Φ ⋙ Ψ) ⋙ r).obj x₀)) :
    comparisonPushforward (Φ ⋙ Ψ) P R U =
      comparisonPushforward Ψ Q R U ≫ Ψ.map (comparisonPushforward Φ P Q U) := by
  let := R.inclusion_cocartesian U
  let := comparisonPushforward_isHomLift Ψ Q R U
  let : r.IsHomLift (𝟙 U.right) (Ψ.map (comparisonPushforward Φ P Q U)) :=
    isHomLift_map_of_comp Ψ (𝟙 U.right) (comparisonPushforward Φ P Q U)
      (comparisonPushforward_isHomLift Φ P Q U)
  refine Functor.IsStronglyCocartesian.ext r U.hom (R.inclusion U) (𝟙 U.right) ?_
  calc
    R.inclusion U ≫ comparisonPushforward (Φ ⋙ Ψ) P R U = (Φ ⋙ Ψ).map (P.inclusion U) :=
      inclusion_comp_comparisonPushforward (Φ ⋙ Ψ) P R U
    _ = Ψ.map (Φ.map (P.inclusion U)) := rfl
    _ = Ψ.map (Q.inclusion U ≫ comparisonPushforward Φ P Q U) := by
        rw [inclusion_comp_comparisonPushforward Φ P Q U]
    _ = Ψ.map (Q.inclusion U) ≫ Ψ.map (comparisonPushforward Φ P Q U) := Ψ.map_comp _ _
    _ = (R.inclusion U ≫ comparisonPushforward Ψ Q R U) ≫
          Ψ.map (comparisonPushforward Φ P Q U) := by
        rw [inclusion_comp_comparisonPushforward Ψ Q R U]
    _ = R.inclusion U ≫
          (comparisonPushforward Ψ Q R U ≫ Ψ.map (comparisonPushforward Φ P Q U)) :=
        Category.assoc _ _ _

/-- The second comparison map for a composite morphism factors, in the opposite order, through
the images of the two second comparison maps: this is the inverse statement to
`Deformation.comparisonPushforward_comp`, proved the same way from the universal property, now
read at the strongly cocartesian arrow `(Φ ⋙ Ψ).map (P.inclusion U)` supplied by `hr`. -/
public theorem comparisonPushforwardInv_of_comp (hcomp : IsCofiberedInGroupoids (Ψ ⋙ r))
    (hr : IsCofiberedInGroupoids r) (U : Under (((Φ ⋙ Ψ) ⋙ r).obj x₀)) :
    comparisonPushforwardInv (Φ ⋙ Ψ) P R hr U =
      Ψ.map (comparisonPushforwardInv Φ P Q hcomp U) ≫ comparisonPushforwardInv Ψ Q R hr U := by
  let := isStronglyCocartesian_of_isCofiberedInGroupoids hr U.hom
    ((Φ ⋙ Ψ).map (P.inclusion U)) (isHomLift_map_inclusion (Φ ⋙ Ψ) P U)
  let := comparisonPushforwardInv_isHomLift Ψ Q R hr U
  let : r.IsHomLift (𝟙 U.right) (Ψ.map (comparisonPushforwardInv Φ P Q hcomp U)) :=
    isHomLift_map_of_comp Ψ (𝟙 U.right) (comparisonPushforwardInv Φ P Q hcomp U)
      (comparisonPushforwardInv_isHomLift Φ P Q hcomp U)
  refine Functor.IsStronglyCocartesian.ext r U.hom ((Φ ⋙ Ψ).map (P.inclusion U)) (𝟙 U.right) ?_
  calc
    (Φ ⋙ Ψ).map (P.inclusion U) ≫ comparisonPushforwardInv (Φ ⋙ Ψ) P R hr U = R.inclusion U :=
      map_inclusion_comp_comparisonPushforwardInv (Φ ⋙ Ψ) P R hr U
    _ = Ψ.map (Q.inclusion U) ≫ comparisonPushforwardInv Ψ Q R hr U := by
        rw [map_inclusion_comp_comparisonPushforwardInv Ψ Q R hr U]
    _ = Ψ.map (Φ.map (P.inclusion U) ≫ comparisonPushforwardInv Φ P Q hcomp U) ≫
          comparisonPushforwardInv Ψ Q R hr U := by
        rw [map_inclusion_comp_comparisonPushforwardInv Φ P Q hcomp U]
    _ = (Ψ.map (Φ.map (P.inclusion U)) ≫ Ψ.map (comparisonPushforwardInv Φ P Q hcomp U)) ≫
          comparisonPushforwardInv Ψ Q R hr U := by rw [Ψ.map_comp]
    _ = Ψ.map (Φ.map (P.inclusion U)) ≫
          Ψ.map (comparisonPushforwardInv Φ P Q hcomp U) ≫
            comparisonPushforwardInv Ψ Q R hr U :=
        Category.assoc _ _ _
    _ = (Φ ⋙ Ψ).map (P.inclusion U) ≫
          (Ψ.map (comparisonPushforwardInv Φ P Q hcomp U) ≫
            comparisonPushforwardInv Ψ Q R hr U) := rfl

/-- The homomorphism of fibre automorphism groups induced by a composite morphism over the base
is the composite of the two induced homomorphisms: conjugating by the comparison for the
composite is the same as conjugating by the inner comparison and then by the image of the
outer one, which is exactly `Deformation.comparisonPushforward_comp` and
`Deformation.comparisonPushforwardInv_of_comp` read on the conjugated element. -/
public theorem inducedAutomorphismHom_comp (hcomp : IsCofiberedInGroupoids (Ψ ⋙ r))
    (hr : IsCofiberedInGroupoids r) (U : Under (((Φ ⋙ Ψ) ⋙ r).obj x₀)) (a : Aut (P.obj U)) :
    inducedAutomorphismHom (Φ ⋙ Ψ) P R hr U a =
      inducedAutomorphismHom Ψ Q R hr U (inducedAutomorphismHom Φ P Q hcomp U a) := by
  apply Aut.ext
  apply Iso.ext
  apply Subtype.ext
  rw [inducedAutomorphismHom_hom_val, inducedAutomorphismHom_hom_val,
    inducedAutomorphismHom_hom_val, comparisonPushforward_comp Φ Ψ r P Q R U,
    comparisonPushforwardInv_of_comp Φ Ψ r P Q R hcomp hr U, Functor.comp_map, Ψ.map_comp,
    Ψ.map_comp]
  simp only [Category.assoc]

end Composition

/-! ### The induced map on infinitesimal automorphisms -/

section Linear

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
  {F : Type u₁} [Category.{v₁} F] {G : Type u₂} [Category.{v₂} G]
  {q : G ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k} (Φ : F ⥤ G) {x₀ : F}
  (P : ChosenPushforwardsAt (Φ ⋙ q) x₀) (Q : ChosenPushforwardsAt q (Φ.obj x₀))

/-- The homomorphism of infinitesimal automorphism groups induced by a morphism over the
base. -/
public noncomputable def inducedInfinitesimalAutomorphismHom (hq : IsCofiberedInGroupoids q) :
    infinitesimalAutomorphismKernel P (tangentReduction (p := Φ ⋙ q) (x := x₀)) →*
      infinitesimalAutomorphismKernel Q (tangentReduction (p := Φ ⋙ q) (x := x₀)) where
  toFun a := ⟨inducedAutomorphismHom Φ P Q hq _ a.1, by
    rw [MonoidHom.mem_ker]
    change Q.transportAut (tangentReduction (p := Φ ⋙ q) (x := x₀))
      (inducedAutomorphismHom Φ P Q hq _ a.1) = 1
    rw [← inducedAutomorphismHom_transportAut Φ P Q hq
      (tangentReduction (p := Φ ⋙ q) (x := x₀)) a.1,
      show P.transportAut (tangentReduction (p := Φ ⋙ q) (x := x₀)) a.1 = 1 from
        MonoidHom.mem_ker.mp a.2, map_one]⟩
  map_one' := Subtype.ext (map_one (inducedAutomorphismHom Φ P Q hq _))
  map_mul' a b := Subtype.ext (map_mul (inducedAutomorphismHom Φ P Q hq _) a.1 b.1)

/-- If `Φ` is full and faithful, the homomorphism of infinitesimal automorphism groups it
induces is bijective. Injectivity is immediate from injectivity of
`Deformation.inducedAutomorphismHom` at the dual numbers, since the kernel's inclusion is
injective on the nose. For surjectivity, a preimage of a kernel element at the dual numbers
exists by surjectivity there; it lies in the kernel because its image under `transportAut`
to the special fibre has image (under the *injective* `inducedAutomorphismHom` there) equal to
the image of the identity, using the naturality `Deformation.inducedAutomorphismHom_transportAut`
along `Deformation.tangentReduction`. -/
public theorem bijective_inducedInfinitesimalAutomorphismHom (hq : IsCofiberedInGroupoids q)
    [Φ.Full] [Φ.Faithful] :
    Function.Bijective (inducedInfinitesimalAutomorphismHom Φ P Q hq) := by
  constructor
  · intro a b hab
    exact Subtype.ext ((bijective_inducedAutomorphismHom Φ P Q hq
      (dualNumbersUnder (p := Φ ⋙ q) (x := x₀))).1 (congrArg Subtype.val hab))
  · intro t
    obtain ⟨a, ha⟩ := (bijective_inducedAutomorphismHom Φ P Q hq
      (dualNumbersUnder (p := Φ ⋙ q) (x := x₀))).2 t.1
    have hmemP : a ∈ MonoidHom.ker
        (P.transportAutHom (tangentReduction (p := Φ ⋙ q) (x := x₀))) := by
      rw [MonoidHom.mem_ker]
      apply (bijective_inducedAutomorphismHom Φ P Q hq
        (specialFibreUnder (p := Φ ⋙ q) (x := x₀))).1
      rw [map_one]
      change inducedAutomorphismHom Φ P Q hq (specialFibreUnder (p := Φ ⋙ q) (x := x₀))
        (P.transportAut (tangentReduction (p := Φ ⋙ q) (x := x₀)) a) = 1
      rw [inducedAutomorphismHom_transportAut Φ P Q hq
        (tangentReduction (p := Φ ⋙ q) (x := x₀)) a, ha]
      exact MonoidHom.mem_ker.mp t.2
    exact ⟨⟨a, hmemP⟩, Subtype.ext ha⟩

/-- The underlying map of the induced map on infinitesimal automorphisms: read the tangent
vector as an infinitesimal automorphism, push it along `Φ`, and read the result back. -/
public noncomputable def inducedInfinitesimalFun (hq : IsCofiberedInGroupoids q) :
    localizedAutomorphismFunctorTangent P → localizedAutomorphismFunctorTangent Q := fun a =>
  (localizedTangentEquivKernel Q).symm
    (inducedInfinitesimalAutomorphismHom Φ P Q hq (localizedTangentEquivKernel P a))

/-- The infinitesimal automorphism attached to the image of a tangent vector. -/
public theorem localizedTangentEquivKernel_inducedInfinitesimalFun
    (hq : IsCofiberedInGroupoids q) (a : localizedAutomorphismFunctorTangent P) :
    localizedTangentEquivKernel Q (inducedInfinitesimalFun Φ P Q hq a) =
      inducedInfinitesimalAutomorphismHom Φ P Q hq (localizedTangentEquivKernel P a) :=
  Equiv.apply_symm_apply _ _

/-- The induced map on infinitesimal automorphisms is `k`-linear for the vector-space
structures of Tag 06JV. -/
public theorem isLinearMap_inducedInfinitesimalFun (hp : SatisfiesRS (Φ ⋙ q))
    (hq : SatisfiesRS q) :
    letI := naturalLocalizedTangentAddCommGroup P hp
    letI := naturalLocalizedTangentModule P hp
    letI := naturalLocalizedTangentAddCommGroup Q hq
    letI := naturalLocalizedTangentModule Q hq
    IsLinearMap k (inducedInfinitesimalFun Φ P Q hq.1) := by
  let := naturalLocalizedTangentAddCommGroup P hp
  let := naturalLocalizedTangentModule P hp
  let := naturalLocalizedTangentAddCommGroup Q hq
  let := naturalLocalizedTangentModule Q hq
  obtain ⟨haddP, hsmulP⟩ := naturalLocalizedTangentModule_spec P hp
  obtain ⟨haddQ, hsmulQ⟩ := naturalLocalizedTangentModule_spec Q hq
  constructor
  · intro a b
    apply (localizedTangentEquivKernel Q).injective
    rw [localizedTangentEquivKernel_inducedInfinitesimalFun, haddP, map_mul, haddQ,
      localizedTangentEquivKernel_inducedInfinitesimalFun,
      localizedTangentEquivKernel_inducedInfinitesimalFun]
    rfl
  · intro c a
    apply (localizedTangentEquivKernel Q).injective
    apply Subtype.ext
    rw [localizedTangentEquivKernel_inducedInfinitesimalFun, hsmulQ,
      localizedTangentEquivKernel_inducedInfinitesimalFun]
    change inducedAutomorphismHom Φ P Q hq.1 _ (localizedTangentEquivKernel P (c • a)).1 =
      Q.transportAut (tangentScaling c)
        (inducedAutomorphismHom Φ P Q hq.1 _ (localizedTangentEquivKernel P a).1)
    rw [hsmulP]
    exact inducedAutomorphismHom_transportAut Φ P Q hq.1 (tangentScaling c)
      (localizedTangentEquivKernel P a).1

/-- **Stacks Project, Tag 07W6.** A morphism of categories cofibered in groupoids over `𝒞_Λ`
satisfying (RS) induces a `k`-linear map on infinitesimal automorphisms at a point. -/
@[stacks 07W6 "the induced k-linear map, as a construction"]
public noncomputable def inducedInfinitesimalLinearMap (hp : SatisfiesRS (Φ ⋙ q))
    (hq : SatisfiesRS q) :
    letI := naturalLocalizedTangentAddCommGroup P hp
    letI := naturalLocalizedTangentModule P hp
    letI := naturalLocalizedTangentAddCommGroup Q hq
    letI := naturalLocalizedTangentModule Q hq
    localizedAutomorphismFunctorTangent P →ₗ[k] localizedAutomorphismFunctorTangent Q :=
  letI := naturalLocalizedTangentAddCommGroup P hp
  letI := naturalLocalizedTangentModule P hp
  letI := naturalLocalizedTangentAddCommGroup Q hq
  letI := naturalLocalizedTangentModule Q hq
  (isLinearMap_inducedInfinitesimalFun Φ P Q hp hq).mk' (inducedInfinitesimalFun Φ P Q hq.1)

/-- **Stacks Project, Tag 07W6.** The induced `k`-linear map sends an infinitesimal
automorphism to the conjugate by the comparison of pushforwards of its image under the
morphism. -/
public theorem inducedInfinitesimalLinearMap_apply (hp : SatisfiesRS (Φ ⋙ q))
    (hq : SatisfiesRS q) :
    letI := naturalLocalizedTangentAddCommGroup P hp
    letI := naturalLocalizedTangentModule P hp
    letI := naturalLocalizedTangentAddCommGroup Q hq
    letI := naturalLocalizedTangentModule Q hq
    ∀ a : localizedAutomorphismFunctorTangent P,
      (localizedTangentEquivKernel Q
          (inducedInfinitesimalLinearMap Φ P Q hp hq a)).1.asIso.hom.val =
        comparisonPushforward Φ P Q (dualNumbersUnder (p := Φ ⋙ q) (x := x₀)) ≫
          Φ.map (localizedTangentEquivKernel P a).1.asIso.hom.val ≫
            comparisonPushforwardInv Φ P Q hq.1
              (dualNumbersUnder (p := Φ ⋙ q) (x := x₀)) := by
  let := naturalLocalizedTangentAddCommGroup P hp
  let := naturalLocalizedTangentModule P hp
  let := naturalLocalizedTangentAddCommGroup Q hq
  let := naturalLocalizedTangentModule Q hq
  intro a
  change (localizedTangentEquivKernel Q (inducedInfinitesimalFun Φ P Q hq.1 a)).1.asIso.hom.val = _
  rw [localizedTangentEquivKernel_inducedInfinitesimalFun]
  exact inducedAutomorphismHom_hom_val Φ P Q hq.1 _ (localizedTangentEquivKernel P a).1

/-- **Stacks Project, Tag 07W6.** If `Φ` is full and faithful, the induced `k`-linear map on
infinitesimal automorphisms is bijective: its underlying map is the composite of the two
bijective identifications `Deformation.localizedTangentEquivKernel` with the bijective
`Deformation.inducedInfinitesimalAutomorphismHom` of
`Deformation.bijective_inducedInfinitesimalAutomorphismHom`. -/
public theorem bijective_inducedInfinitesimalLinearMap (hp : SatisfiesRS (Φ ⋙ q))
    (hq : SatisfiesRS q) [Φ.Full] [Φ.Faithful] :
    letI := naturalLocalizedTangentAddCommGroup P hp
    letI := naturalLocalizedTangentModule P hp
    letI := naturalLocalizedTangentAddCommGroup Q hq
    letI := naturalLocalizedTangentModule Q hq
    Function.Bijective (inducedInfinitesimalLinearMap Φ P Q hp hq) := by
  let := naturalLocalizedTangentAddCommGroup P hp
  let := naturalLocalizedTangentModule P hp
  let := naturalLocalizedTangentAddCommGroup Q hq
  let := naturalLocalizedTangentModule Q hq
  change Function.Bijective (inducedInfinitesimalFun Φ P Q hq.1)
  exact ((localizedTangentEquivKernel Q).symm.bijective.comp
    (bijective_inducedInfinitesimalAutomorphismHom Φ P Q hq.1)).comp
    (localizedTangentEquivKernel P).bijective

/-- **Stacks Project, Tag 07W6.** Presented with a morphism as a functor commuting with the
two projections: it induces a `k`-linear map on infinitesimal automorphisms, pinned by the
comparison of dual-number pushforwards. -/
@[stacks 07W6 "the morphism presented as a functor commuting with the two projections, with the
  map pinned by the dual-number comparison"]
public theorem exists_inducedInfinitesimalLinearMap
    {p : F ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k} (hw : Φ ⋙ q = p) (hp : SatisfiesRS p)
    (hq : SatisfiesRS q) (P : ChosenPushforwardsAt p x₀)
    (Q : ChosenPushforwardsAt q (Φ.obj x₀)) :
    letI := naturalLocalizedTangentAddCommGroup P hp
    letI := naturalLocalizedTangentModule P hp
    letI := naturalLocalizedTangentAddCommGroup Q hq
    letI := naturalLocalizedTangentModule Q hq
    ∃ T : localizedAutomorphismFunctorTangent P →ₗ[k] localizedAutomorphismFunctorTangent Q,
      ∃ H : (Q.obj (dualNumbersUnder (p := q) (x := Φ.obj x₀))).1 ⟶
          Φ.obj (P.obj (dualNumbersUnder (p := p) (x := x₀))).1,
        q.IsHomLift (𝟙 (dualNumbersUnder (p := q) (x := Φ.obj x₀)).right) H ∧
          Q.inclusion (dualNumbersUnder (p := q) (x := Φ.obj x₀)) ≫ H =
            Φ.map (P.inclusion (dualNumbersUnder (p := p) (x := x₀))) ∧
          ∀ a, (localizedTangentEquivKernel Q (T a)).1.asIso.hom.val ≫ H =
            H ≫ Φ.map (localizedTangentEquivKernel P a).1.asIso.hom.val := by
  subst hw
  refine ⟨inducedInfinitesimalLinearMap Φ P Q hp hq,
    comparisonPushforward Φ P Q (dualNumbersUnder (p := Φ ⋙ q) (x := x₀)),
    comparisonPushforward_isHomLift Φ P Q _,
    inclusion_comp_comparisonPushforward Φ P Q _, fun a => ?_⟩
  rw [inducedInfinitesimalLinearMap_apply Φ P Q hp hq a, Category.assoc, Category.assoc,
    comparisonPushforwardInv_comp, Category.comp_id]

end Linear

/-! ### Composition of the induced map on infinitesimal automorphisms -/

section LinearComposition
universe u₄ v₄

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
  {F : Type u₁} [Category.{v₁} F] {G : Type u₂} [Category.{v₂} G] {K : Type u₄} [Category.{v₄} K]
  (Φ : F ⥤ G) (Ψ : G ⥤ K) {x₀ : F} (r : K ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k)
  (P : ChosenPushforwardsAt (Φ ⋙ Ψ ⋙ r) x₀) (Q : ChosenPushforwardsAt (Ψ ⋙ r) (Φ.obj x₀))
  (R : ChosenPushforwardsAt r (Ψ.obj (Φ.obj x₀)))

set_option maxHeartbeats 1000000 in
-- unifying the induced automorphism homomorphisms over the composite `Φ ⋙ Ψ ⋙ r` is heavy
/-- The homomorphism of infinitesimal automorphism kernels induced by a composite morphism
over the base is the composite of the two induced homomorphisms: this is
`Deformation.inducedAutomorphismHom_comp` restricted to the infinitesimal kernel. -/
public theorem inducedInfinitesimalAutomorphismHom_comp
    (hcomp : IsCofiberedInGroupoids (Ψ ⋙ r)) (hr : IsCofiberedInGroupoids r)
    (a : infinitesimalAutomorphismKernel P (tangentReduction (p := Φ ⋙ Ψ ⋙ r) (x := x₀))) :
    (inducedInfinitesimalAutomorphismHom (Φ ⋙ Ψ) P R hr a).1 =
      (inducedInfinitesimalAutomorphismHom Ψ Q R hr
        (inducedInfinitesimalAutomorphismHom Φ P Q hcomp a)).1 := by
  apply Aut.ext
  apply Iso.ext
  apply Subtype.ext
  exact congrArg (fun b => b.asIso.hom.val) (inducedAutomorphismHom_comp Φ Ψ r P Q R hcomp hr
    (dualNumbersUnder (p := Φ ⋙ Ψ ⋙ r) (x := x₀)) a.1)

/-- The underlying map on infinitesimal automorphisms induced by a composite morphism over the
base is the composite of the two induced maps. -/
public theorem inducedInfinitesimalFun_comp
    (hcomp : IsCofiberedInGroupoids (Ψ ⋙ r)) (hr : IsCofiberedInGroupoids r)
    (a : localizedAutomorphismFunctorTangent P) :
    inducedInfinitesimalFun (Φ ⋙ Ψ) P R hr a =
      inducedInfinitesimalFun Ψ Q R hr (inducedInfinitesimalFun Φ P Q hcomp a) := by
  apply (localizedTangentEquivKernel R).injective
  have hL : localizedTangentEquivKernel R (inducedInfinitesimalFun (Φ ⋙ Ψ) P R hr a) =
      inducedInfinitesimalAutomorphismHom (Φ ⋙ Ψ) P R hr (localizedTangentEquivKernel P a) :=
    localizedTangentEquivKernel_inducedInfinitesimalFun (Φ ⋙ Ψ) P R hr a
  have hR1 : localizedTangentEquivKernel Q (inducedInfinitesimalFun Φ P Q hcomp a) =
      inducedInfinitesimalAutomorphismHom Φ P Q hcomp (localizedTangentEquivKernel P a) :=
    localizedTangentEquivKernel_inducedInfinitesimalFun Φ P Q hcomp a
  have hR2 : localizedTangentEquivKernel R
      (inducedInfinitesimalFun Ψ Q R hr (inducedInfinitesimalFun Φ P Q hcomp a)) =
      inducedInfinitesimalAutomorphismHom Ψ Q R hr
        (localizedTangentEquivKernel Q (inducedInfinitesimalFun Φ P Q hcomp a)) :=
    localizedTangentEquivKernel_inducedInfinitesimalFun Ψ Q R hr _
  rw [hL, hR2, hR1]
  exact Subtype.ext (inducedInfinitesimalAutomorphismHom_comp Φ Ψ r P Q R hcomp hr _)

/-- **The `Inf`-side composition law**, the analogue of `Deformation.tangentMapAt_comp`. The
`k`-linear map on infinitesimal automorphisms induced by a composite morphism over the base is
the composite of the two induced `k`-linear maps. -/
public theorem inducedInfinitesimalLinearMap_comp
    (hp : SatisfiesRS (Φ ⋙ Ψ ⋙ r)) (hq : SatisfiesRS (Ψ ⋙ r)) (hs : SatisfiesRS r) :
    letI := naturalLocalizedTangentAddCommGroup P hp
    letI := naturalLocalizedTangentModule P hp
    letI := naturalLocalizedTangentAddCommGroup Q hq
    letI := naturalLocalizedTangentModule Q hq
    letI := naturalLocalizedTangentAddCommGroup R hs
    letI := naturalLocalizedTangentModule R hs
    inducedInfinitesimalLinearMap (Φ ⋙ Ψ) P R hp hs =
      (inducedInfinitesimalLinearMap Ψ Q R hq hs).comp
        (inducedInfinitesimalLinearMap Φ P Q hp hq) := by
  let := naturalLocalizedTangentAddCommGroup P hp
  let := naturalLocalizedTangentModule P hp
  let := naturalLocalizedTangentAddCommGroup Q hq
  let := naturalLocalizedTangentModule Q hq
  let := naturalLocalizedTangentAddCommGroup R hs
  let := naturalLocalizedTangentModule R hs
  apply LinearMap.ext (R := k) (S := k) (M := localizedAutomorphismFunctorTangent P)
    (M₃ := localizedAutomorphismFunctorTangent R) (σ := RingHom.id k)
  intro a
  change inducedInfinitesimalFun (Φ ⋙ Ψ) P R hs.1 a = _
  rw [inducedInfinitesimalFun_comp Φ Ψ r P Q R hq.1 hs.1]
  rfl

end LinearComposition

end Deformation

end
