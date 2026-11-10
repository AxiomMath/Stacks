module

public import StacksFrontier.Deformation.Applications.TwoFibreProductSixTerm
public import StacksFrontier.Deformation.PredeformationTangent.DifferentialLinear

/-!
# The maps of the six-term exact sequence of a 2-fibre product

Part (2) of Tag 06L5: for `1`-morphisms `f : ℋ → ℱ` and `g : 𝒢 → ℱ` of deformation categories
over `𝒞_Λ` and an object `w₀` of `𝒲 = ℋ ×_ℱ 𝒢` over the residue field there is a six-term exact
sequence of `k`-vector spaces

`0 → Inf(𝒲) → Inf(ℋ) ⊕ Inf(𝒢) → Inf(ℱ) → T𝒲 → Tℋ ⊕ T𝒢 → Tℱ`.

This file constructs the four maps of the `T`-row, the three maps of the `Inf`-row, the zero of
the `T`-terms, and the boundary map `δ`.

## Main definitions

* `Deformation.associatedTangentLiftMap`: the `k`-linear map on the values of the canonical
  linear lift of the associated square-zero functor induced by a morphism of predeformation
  categories, at an arbitrary coordinate module. These are the four horizontal maps of the
  `T`-row. At the rank-one module this is the differential of Tag 06IJ.
* `Deformation.inducedInfinitesimalLinearMapOfEq`: Tag 07W6 with the equality of projections
  carried as a hypothesis rather than built into the source projection. These are the three
  horizontal maps of the `Inf`-row.
* `Deformation.squareZeroCrossUnder`: the square-zero extension by `M` read as an object under
  `A` whose underlying object of `𝒞_Λ` is the square-zero extension of `𝒞_Λ` itself.
* `Deformation.boundaryCompareFst`, `Deformation.boundaryCompareSnd`: the comparison
  isomorphisms `b'` and `c'` of the source.
* `Deformation.boundaryObject`, `Deformation.boundaryClass`, `Deformation.boundaryFun`: the
  boundary map `δ`, as the quadruple `(k[M], y'₀, z'₀, c' ∘ α ∘ b')` of the explicit
  description of the `2`-fibre product, as its isomorphism class, and as an element of the
  value of the linear lift of `𝒲`.

## Main results

* `Deformation.associatedTangentLift_classOf_eq_zero`: the zero of the `T`-terms, read on
  representatives — the class of any pushforward along the zero coordinate map vanishes.
* `Deformation.classOf_eq_iff`: two objects of a fibre have the same class exactly when they
  are isomorphic in that fibre.

## References

* [Stacks Project, Tag 06L5](https://stacks.math.columbia.edu/tag/06L5)
-/

@[expose] public section

namespace Deformation

/-! ### Classes in the associated functor -/

section ClassOf
open CategoryTheory CategoryTheory.Functor
universe u v u₁ v₁

variable {C : Type u} [Category.{v} C] (𝓕 : BasedCategory.{v₁, u₁} C)
  (h𝓕 : IsCofiberedInGroupoids 𝓕.p)

/-- Two objects of a fibre have the same associated isomorphism class exactly when they are
isomorphic in that fibre. -/
public theorem classOf_eq_iff {A : C} (x y : 𝓕.p.Fiber A) :
    classOf 𝓕 h𝓕 x = classOf 𝓕 h𝓕 y ↔ IsIsomorphic x y := by
  refine ⟨fun h => ?_, classOf_eq_of_isIsomorphic 𝓕 h𝓕 x y⟩
  have hx := classOf_eq 𝓕 h𝓕 x
  have hy := classOf_eq 𝓕 h𝓕 y
  have : Quotient.mk (isIsomorphicSetoid (𝓕.p.Fiber A)) x =
      Quotient.mk (isIsomorphicSetoid (𝓕.p.Fiber A)) y := by
    rw [← hx, ← hy, h]
  exact Quotient.exact this

end ClassOf

/-! ### Functoriality of the tangent-space lift -/

section TangentFunctoriality
open CategoryTheory
universe u v w u₁ v₁ u₂ v₂

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]

variable (𝓕 : BasedCategory.{v₁, u₁} (ArtinianLocalAlgCat.{u, max v w, w} Λ k))
  (𝓖 : BasedCategory.{v₂, u₂} (ArtinianLocalAlgCat.{u, max v w, w} Λ k))
  (h𝓕 : IsPredeformationCategory.{u, v, w} 𝓕.p)
  (h𝓖 : IsPredeformationCategory.{u, v, w} 𝓖.p)
  (hS2𝓕 : SchlessingerConditionS2
    (Functor.Elements.π (isomorphismClasses 𝓕 h𝓕.cofibered)))
  (hS2𝓖 : SchlessingerConditionS2
    (Functor.Elements.π (isomorphismClasses 𝓖 h𝓖.cofibered)))

/-- The value of the linear lift at a coordinate module has the isomorphism classes over the
square-zero extension by that module as underlying set. -/
public theorem associatedTangentLift_carrier (M : FGModuleCat.{max v w} k) :
    (((associatedTangentSpaceModuleStructure.{u, v, w} 𝓕 h𝓕 hS2𝓕).functor.obj M :
        ModuleCat.{u₁} k) : Type u₁) =
      (isomorphismClasses 𝓕 h𝓕.cofibered).obj
        ((squareZeroExtensionArtinian.{u, w, max v w} Λ k).obj M) :=
  congrArg (fun H : FGModuleCat.{max v w} k ⥤ Type u₁ => H.obj M)
    (associatedTangentSpaceModuleStructure.{u, v, w} 𝓕 h𝓕 hS2𝓕).forget_comp

/-- The functorial action of the linear lift at a coordinate module, read through the carrier
identification, is the action of the isomorphism-class functor. -/
private theorem associatedTangentLift_map_cast {M N : FGModuleCat.{max v w} k} (h : M ⟶ N)
    (z : (((associatedTangentSpaceModuleStructure.{u, v, w} 𝓕 h𝓕 hS2𝓕).functor.obj M :
      ModuleCat.{u₁} k) : Type u₁)) :
    cast (associatedTangentLift_carrier.{u, v, w} 𝓕 h𝓕 hS2𝓕 N)
        (((associatedTangentSpaceModuleStructure.{u, v, w} 𝓕 h𝓕 hS2𝓕).functor.map h) z) =
      (isomorphismClasses 𝓕 h𝓕.cofibered).map
        ((squareZeroExtensionArtinian.{u, w, max v w} Λ k).map h)
        (cast (associatedTangentLift_carrier.{u, v, w} 𝓕 h𝓕 hS2𝓕 M) z) :=
  moduleFunctor_map_cast k
    (associatedTangentSpaceModuleStructure.{u, v, w} 𝓕 h𝓕 hS2𝓕).functor
    (squareZeroExtensionArtinian.{u, w, max v w} Λ k ⋙ isomorphismClasses 𝓕 h𝓕.cofibered)
    (associatedTangentSpaceModuleStructure.{u, v, w} 𝓕 h𝓕 hS2𝓕).forget_comp h z

variable (φ : 𝓕 ⥤ᵇ 𝓖)

/-- The underlying map of the induced map on the values of the two linear lifts: read the
value as an isomorphism class, apply the morphism fibrewise, and read the result back. -/
public noncomputable def associatedTangentLiftFun (M : FGModuleCat.{max v w} k) :
    (((associatedTangentSpaceModuleStructure.{u, v, w} 𝓕 h𝓕 hS2𝓕).functor.obj M :
        ModuleCat.{u₁} k) : Type u₁) →
      (((associatedTangentSpaceModuleStructure.{u, v, w} 𝓖 h𝓖 hS2𝓖).functor.obj M :
        ModuleCat.{u₂} k) : Type u₂) := fun z =>
  cast (associatedTangentLift_carrier.{u, v, w} 𝓖 h𝓖 hS2𝓖 M).symm
    (mapIsomorphismClasses h𝓕.cofibered h𝓖.cofibered φ
      ((squareZeroExtensionArtinian.{u, w, max v w} Λ k).obj M)
      (cast (associatedTangentLift_carrier.{u, v, w} 𝓕 h𝓕 hS2𝓕 M) z))

/-- The induced map is natural in the coordinate module. -/
public theorem associatedTangentLiftFun_naturality {M N : FGModuleCat.{max v w} k} (h : M ⟶ N)
    (z : (((associatedTangentSpaceModuleStructure.{u, v, w} 𝓕 h𝓕 hS2𝓕).functor.obj M :
      ModuleCat.{u₁} k) : Type u₁)) :
    associatedTangentLiftFun.{u, v, w} 𝓕 𝓖 h𝓕 h𝓖 hS2𝓕 hS2𝓖 φ N
        (((associatedTangentSpaceModuleStructure.{u, v, w} 𝓕 h𝓕 hS2𝓕).functor.map h) z) =
      ((associatedTangentSpaceModuleStructure.{u, v, w} 𝓖 h𝓖 hS2𝓖).functor.map h)
        (associatedTangentLiftFun.{u, v, w} 𝓕 𝓖 h𝓕 h𝓖 hS2𝓕 hS2𝓖 φ M z) := by
  dsimp only [associatedTangentLiftFun]
  rw [associatedTangentLift_map_cast.{u, v, w} 𝓕 h𝓕 hS2𝓕 h z]
  have hnat := mapIsomorphismClasses_naturality h𝓕.cofibered h𝓖.cofibered φ
    ((squareZeroExtensionArtinian.{u, w, max v w} Λ k).map h)
    (cast (associatedTangentLift_carrier.{u, v, w} 𝓕 h𝓕 hS2𝓕 M) z)
  have hG := associatedTangentLift_map_cast.{u, v, w} 𝓖 h𝓖 hS2𝓖 h
    (cast (associatedTangentLift_carrier.{u, v, w} 𝓖 h𝓖 hS2𝓖 M).symm
      (mapIsomorphismClasses h𝓕.cofibered h𝓖.cofibered φ
        ((squareZeroExtensionArtinian.{u, w, max v w} Λ k).obj M)
        (cast (associatedTangentLift_carrier.{u, v, w} 𝓕 h𝓕 hS2𝓕 M) z)))
  rw [cast_symm_cancel] at hG
  refine (Equiv.cast (associatedTangentLift_carrier.{u, v, w} 𝓖 h𝓖 hS2𝓖 N)).injective ?_
  change cast (associatedTangentLift_carrier.{u, v, w} 𝓖 h𝓖 hS2𝓖 N)
      (cast (associatedTangentLift_carrier.{u, v, w} 𝓖 h𝓖 hS2𝓖 N).symm _) =
    cast (associatedTangentLift_carrier.{u, v, w} 𝓖 h𝓖 hS2𝓖 N) _
  rw [cast_symm_cancel, hG]
  exact hnat

/-- The induced map on the values of the two linear lifts is `k`-linear at every coordinate
module. -/
public theorem isLinearMap_associatedTangentLiftFun (M : FGModuleCat.{max v w} k) :
    IsLinearMap k (associatedTangentLiftFun.{u, v, w} 𝓕 𝓖 h𝓕 h𝓖 hS2𝓕 hS2𝓖 φ M) :=
  isLinearMap_of_natural_at k
    (associatedTangentSpaceModuleStructure.{u, v, w} 𝓕 h𝓕 hS2𝓕).functor
    (associatedTangentSpaceModuleStructure.{u, v, w} 𝓖 h𝓖 hS2𝓖).functor
    (associatedTangentLiftFun.{u, v, w} 𝓕 𝓖 h𝓕 h𝓖 hS2𝓕 hS2𝓖 φ)
    (fun h z => associatedTangentLiftFun_naturality.{u, v, w} 𝓕 𝓖 h𝓕 h𝓖 hS2𝓕 hS2𝓖 φ h z) M

/-- The `k`-linear map on the values of the canonical linear lifts of the associated square-zero
functors induced by a morphism of predeformation categories: Tag 06IJ at an arbitrary
coordinate module. -/
public noncomputable def associatedTangentLiftMap (M : FGModuleCat.{max v w} k) :
    (((associatedTangentSpaceModuleStructure.{u, v, w} 𝓕 h𝓕 hS2𝓕).functor.obj M :
        ModuleCat.{u₁} k) : Type u₁) →ₗ[k]
      (((associatedTangentSpaceModuleStructure.{u, v, w} 𝓖 h𝓖 hS2𝓖).functor.obj M :
        ModuleCat.{u₂} k) : Type u₂) :=
  (isLinearMap_associatedTangentLiftFun.{u, v, w} 𝓕 𝓖 h𝓕 h𝓖 hS2𝓕 hS2𝓖 φ M).mk'
    (associatedTangentLiftFun.{u, v, w} 𝓕 𝓖 h𝓕 h𝓖 hS2𝓕 hS2𝓖 φ M)

/-- The induced linear map sends the class of an object of the fibre to the class of its
image. -/
public theorem associatedTangentLiftMap_classOf (M : FGModuleCat.{max v w} k)
    (x : 𝓕.p.Fiber ((squareZeroExtensionArtinian.{u, w, max v w} Λ k).obj M)) :
    associatedTangentLiftMap.{u, v, w} 𝓕 𝓖 h𝓕 h𝓖 hS2𝓕 hS2𝓖 φ M
        (cast (associatedTangentLift_carrier.{u, v, w} 𝓕 h𝓕 hS2𝓕 M).symm
          (classOf 𝓕 h𝓕.cofibered x)) =
      cast (associatedTangentLift_carrier.{u, v, w} 𝓖 h𝓖 hS2𝓖 M).symm
        (classOf 𝓖 h𝓖.cofibered
          ((fiberFunctor φ ((squareZeroExtensionArtinian.{u, w, max v w} Λ k).obj M)).obj x)) := by
  change cast _ (mapIsomorphismClasses h𝓕.cofibered h𝓖.cofibered φ _ (cast _ (cast _ _))) = _
  rw [cast_symm_cancel, mapIsomorphismClasses_classOf]

/-! ### The zero of the tangent-space lift -/

/-- A class that is fixed by the zero coordinate map is the zero of the lift. -/
public theorem associatedTangentLift_eq_zero_of_map_zero_eq (M : FGModuleCat.{max v w} k)
    (z : (isomorphismClasses 𝓕 h𝓕.cofibered).obj
      ((squareZeroExtensionArtinian.{u, w, max v w} Λ k).obj M))
    (hz : (isomorphismClasses 𝓕 h𝓕.cofibered).map
        ((squareZeroExtensionArtinian.{u, w, max v w} Λ k).map (0 : M ⟶ M)) z = z) :
    cast (associatedTangentLift_carrier.{u, v, w} 𝓕 h𝓕 hS2𝓕 M).symm z = 0 := by
  have hcast := associatedTangentLift_map_cast.{u, v, w} 𝓕 h𝓕 hS2𝓕 (0 : M ⟶ M)
    (cast (associatedTangentLift_carrier.{u, v, w} 𝓕 h𝓕 hS2𝓕 M).symm z)
  rw [Functor.map_zero, cast_symm_cancel, hz] at hcast
  exact (congrArg (cast (associatedTangentLift_carrier.{u, v, w} 𝓕 h𝓕 hS2𝓕 M).symm)
    hcast.symm).trans (cast_symm_cancel _ _)

/-- Every class in the image of the zero coordinate map is the zero of the lift. -/
public theorem associatedTangentLift_map_zero_eq_zero (M : FGModuleCat.{max v w} k)
    (z : (isomorphismClasses 𝓕 h𝓕.cofibered).obj
      ((squareZeroExtensionArtinian.{u, w, max v w} Λ k).obj M)) :
    cast (associatedTangentLift_carrier.{u, v, w} 𝓕 h𝓕 hS2𝓕 M).symm
      ((isomorphismClasses 𝓕 h𝓕.cofibered).map
        ((squareZeroExtensionArtinian.{u, w, max v w} Λ k).map (0 : M ⟶ M)) z) = 0 := by
  refine associatedTangentLift_eq_zero_of_map_zero_eq.{u, v, w} 𝓕 h𝓕 hS2𝓕 M _ ?_
  rw [← Functor.map_comp_apply, ← Functor.map_comp,
    show (0 : M ⟶ M) ≫ (0 : M ⟶ M) = (0 : M ⟶ M) by simp]

/-- The class of any pushforward along the zero coordinate map is the zero of the lift. This
is the zero of the tangent space read on representatives: the pushforward of any deformation
along `k[M] → k → k[M]` is the trivial deformation. -/
public theorem associatedTangentLift_classOf_eq_zero (M : FGModuleCat.{max v w} k)
    (x x' : 𝓕.p.Fiber ((squareZeroExtensionArtinian.{u, w, max v w} Λ k).obj M))
    (a : x.1 ⟶ x'.1)
    [𝓕.p.IsHomLift ((squareZeroExtensionArtinian.{u, w, max v w} Λ k).map (0 : M ⟶ M)) a] :
    cast (associatedTangentLift_carrier.{u, v, w} 𝓕 h𝓕 hS2𝓕 M).symm
      (classOf 𝓕 h𝓕.cofibered x') = 0 := by
  rw [← map_classOf 𝓕 h𝓕.cofibered
    ((squareZeroExtensionArtinian.{u, w, max v w} Λ k).map (0 : M ⟶ M)) x x' a]
  exact associatedTangentLift_map_zero_eq_zero.{u, v, w} 𝓕 h𝓕 hS2𝓕 M _

end TangentFunctoriality

/-! ### Functoriality of infinitesimal automorphisms, with the projections compared -/

section InfinitesimalFunctoriality
open CategoryTheory
universe u v w u₁ v₁ u₂ v₂

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
  {F : Type u₁} [Category.{v₁} F] {G : Type u₂} [Category.{v₂} G]
  {q : G ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k}
  {p : F ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k}

/-- The `k`-linear map of Tag 07W6 on infinitesimal automorphisms induced by a morphism
presented as a functor commuting with the two projections: this is
`Deformation.inducedInfinitesimalLinearMap` with the equality of projections carried as a
hypothesis rather than built into the source projection. -/
public noncomputable def inducedInfinitesimalLinearMapOfEq (Φ : F ⥤ G) {x₀ : F}
    (hw : Φ ⋙ q = p) (hp : SatisfiesRS p) (hq : SatisfiesRS q)
    (P : ChosenPushforwardsAt p x₀) (Q : ChosenPushforwardsAt q (Φ.obj x₀)) :
    letI := naturalLocalizedTangentAddCommGroup P hp
    letI := naturalLocalizedTangentModule P hp
    letI := naturalLocalizedTangentAddCommGroup Q hq
    letI := naturalLocalizedTangentModule Q hq
    localizedAutomorphismFunctorTangent P →ₗ[k] localizedAutomorphismFunctorTangent Q := by
  subst hw
  exact inducedInfinitesimalLinearMap Φ P Q hp hq

/-- The induced map on infinitesimal automorphisms is conjugation by the comparison of
dual-number pushforwards: there is a vertical comparison arrow `H`, compatible with the two
chosen inclusions, which intertwines an infinitesimal automorphism with its image. -/
public theorem inducedInfinitesimalLinearMapOfEq_spec (Φ : F ⥤ G) {x₀ : F}
    (hw : Φ ⋙ q = p) (hp : SatisfiesRS p) (hq : SatisfiesRS q)
    (P : ChosenPushforwardsAt p x₀) (Q : ChosenPushforwardsAt q (Φ.obj x₀)) :
    letI := naturalLocalizedTangentAddCommGroup P hp
    letI := naturalLocalizedTangentModule P hp
    letI := naturalLocalizedTangentAddCommGroup Q hq
    letI := naturalLocalizedTangentModule Q hq
    ∃ H : (Q.obj (dualNumbersUnder (p := q) (x := Φ.obj x₀))).1 ⟶
        Φ.obj (P.obj (dualNumbersUnder (p := p) (x := x₀))).1,
      q.IsHomLift (𝟙 (dualNumbersUnder (p := q) (x := Φ.obj x₀)).right) H ∧
        Q.inclusion (dualNumbersUnder (p := q) (x := Φ.obj x₀)) ≫ H =
          Φ.map (P.inclusion (dualNumbersUnder (p := p) (x := x₀))) ∧
        ∀ a, (localizedTangentEquivKernel Q
            (inducedInfinitesimalLinearMapOfEq Φ hw hp hq P Q a)).1.asIso.hom.val ≫ H =
          H ≫ Φ.map (localizedTangentEquivKernel P a).1.asIso.hom.val := by
  subst hw
  refine ⟨comparisonPushforward Φ P Q (dualNumbersUnder (p := Φ ⋙ q) (x := x₀)),
    comparisonPushforward_isHomLift Φ P Q _,
    inclusion_comp_comparisonPushforward Φ P Q _, fun a => ?_⟩
  change (localizedTangentEquivKernel Q
    (inducedInfinitesimalLinearMap Φ P Q hp hq a)).1.asIso.hom.val ≫ _ = _
  rw [inducedInfinitesimalLinearMap_apply Φ P Q hp hq a]
  rw [Category.assoc, Category.assoc, comparisonPushforwardInv_comp, Category.comp_id]

/-- If `Φ` is full and faithful, the `k`-linear map of Tag 07W6 induced by a morphism presented
as a functor commuting with the two projections is bijective. -/
public theorem bijective_inducedInfinitesimalLinearMapOfEq (Φ : F ⥤ G) {x₀ : F}
    (hw : Φ ⋙ q = p) (hp : SatisfiesRS p) (hq : SatisfiesRS q)
    (P : ChosenPushforwardsAt p x₀) (Q : ChosenPushforwardsAt q (Φ.obj x₀))
    [Φ.Full] [Φ.Faithful] :
    letI := naturalLocalizedTangentAddCommGroup P hp
    letI := naturalLocalizedTangentModule P hp
    letI := naturalLocalizedTangentAddCommGroup Q hq
    letI := naturalLocalizedTangentModule Q hq
    Function.Bijective (inducedInfinitesimalLinearMapOfEq Φ hw hp hq P Q) := by
  subst hw
  exact bijective_inducedInfinitesimalLinearMap Φ P Q hp hq

end InfinitesimalFunctoriality

/-! ### Composition of the induced `Inf`-linear map, with the projections compared -/

section InfinitesimalFunctorialityComp
open CategoryTheory
universe u v w u₁ v₁ u₂ v₂ u₃ v₃

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
  {F : Type u₁} [Category.{v₁} F] {G : Type u₂} [Category.{v₂} G] {H : Type u₃} [Category.{v₃} H]
  {p : F ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k}
  {q : G ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k}
  {r : H ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k}

/-- The `k`-linear map on infinitesimal automorphisms induced by a composite morphism over the
base is the composite of the two induced `k`-linear maps. -/
public theorem inducedInfinitesimalLinearMapOfEq_comp (Φ : F ⥤ G) (Ψ : G ⥤ H) {x₀ : F}
    (hwΦ : Φ ⋙ q = p) (hwΨ : Ψ ⋙ r = q) (hp : SatisfiesRS p) (hq : SatisfiesRS q)
    (hr : SatisfiesRS r) (P : ChosenPushforwardsAt p x₀) (Q : ChosenPushforwardsAt q (Φ.obj x₀))
    (R : ChosenPushforwardsAt r (Ψ.obj (Φ.obj x₀))) :
    letI := naturalLocalizedTangentAddCommGroup P hp
    letI := naturalLocalizedTangentModule P hp
    letI := naturalLocalizedTangentAddCommGroup Q hq
    letI := naturalLocalizedTangentModule Q hq
    letI := naturalLocalizedTangentAddCommGroup R hr
    letI := naturalLocalizedTangentModule R hr
    inducedInfinitesimalLinearMapOfEq (Φ ⋙ Ψ)
        ((Functor.assoc Φ Ψ r).trans (by rw [hwΨ, hwΦ])) hp hr P R =
      (inducedInfinitesimalLinearMapOfEq Ψ hwΨ hq hr Q R).comp
        (inducedInfinitesimalLinearMapOfEq Φ hwΦ hp hq P Q) := by
  subst hwΦ
  subst hwΨ
  exact inducedInfinitesimalLinearMap_comp Φ Ψ r P Q R hp hq hr

end InfinitesimalFunctorialityComp

/-! ### The square-zero extension read on the nose in `𝒞_Λ` -/

section Cross
open CategoryTheory
universe u v w

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]

/-- The square-zero extension by `M`, read as an object under `A` whose underlying object of
`𝒞_Λ` is the square-zero extension of `𝒞_Λ` itself and not the one read as an algebra under
`A`. The structure arrow is that of `Deformation.squareZeroUnder` followed by
`Deformation.squareZeroCross`. -/
public noncomputable def squareZeroCrossUnder (A : ArtinianLocalAlgCat.{u, max v w, w} Λ k)
    (M : FGModuleCat.{max v w} k) : Under A :=
  Under.mk (((squareZeroAlgFunctor.{u, v, w} A).obj M).hom ≫ squareZeroCross.{u, v, w} A M)

/-- The underlying object of the re-based square-zero extension is the square-zero extension of
`𝒞_Λ` itself, on the nose. -/
public theorem squareZeroCrossUnder_right (A : ArtinianLocalAlgCat.{u, max v w, w} Λ k)
    (M : FGModuleCat.{max v w} k) :
    (squareZeroCrossUnder.{u, v, w} A M).right =
      (squareZeroExtensionArtinian.{u, w, max v w} Λ k).obj M := rfl

/-- The structure arrows of the re-based square-zero extensions over two *equal* bases agree
after the transport along that equality. -/
public theorem eqToHom_comp_squareZeroCrossUnder_hom
    {A A' : ArtinianLocalAlgCat.{u, max v w, w} Λ k} (h : A' = A)
    (M : FGModuleCat.{max v w} k) :
    eqToHom h ≫ (squareZeroCrossUnder.{u, v, w} A M).hom =
      (squareZeroCrossUnder.{u, v, w} A' M).hom := by
  cases h
  simp

/-- A linear map of coordinate modules, as an arrow between the re-based square-zero
extensions. Its underlying arrow of `𝒞_Λ` is the one of
`Deformation.squareZeroExtensionArtinian`, with no transport. -/
public noncomputable def squareZeroCrossUnderMap
    (A : ArtinianLocalAlgCat.{u, max v w, w} Λ k) {M N : FGModuleCat.{max v w} k} (h : M ⟶ N) :
    squareZeroCrossUnder.{u, v, w} A M ⟶ squareZeroCrossUnder.{u, v, w} A N :=
  Under.homMk ((squareZeroExtensionArtinian.{u, w, max v w} Λ k).map h) (by
    change (((squareZeroAlgFunctor.{u, v, w} A).obj M).hom ≫ squareZeroCross.{u, v, w} A M) ≫
      (squareZeroExtensionArtinian.{u, w, max v w} Λ k).map h =
        ((squareZeroAlgFunctor.{u, v, w} A).obj N).hom ≫ squareZeroCross.{u, v, w} A N
    rw [Category.assoc, ← squareZeroCross_naturality.{u, v, w} A h, ← Category.assoc,
      Under.w ((squareZeroAlgFunctor.{u, v, w} A).map h)])

/-- The comparison itself, as an isomorphism of objects under `A` from the square-zero
extension read as an algebra under `A` to the one read in `𝒞_Λ`. It is the identity on
carriers. -/
public noncomputable def squareZeroCrossUnderIso
    (A : ArtinianLocalAlgCat.{u, max v w, w} Λ k) (M : FGModuleCat.{max v w} k) :
    (squareZeroAlgFunctor.{u, v, w} A).obj M ≅ squareZeroCrossUnder.{u, v, w} A M :=
  Under.isoMk (@asIso _ _ _ _ (squareZeroCross.{u, v, w} A M)
    (isIso_squareZeroCross.{u, v, w} A M)) rfl

end Cross

/-! ### The boundary map of the six-term sequence -/

section Boundary
open CategoryTheory CategoryTheory.Functor
universe u v w u₁ v₁ u₂ v₂ u₃ v₃

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
  {H : Type u₁} [Category.{v₁} H] {G : Type u₂} [Category.{v₂} G] {F : Type u₃} [Category.{v₃} F]

-- The `implicit` transparency level of Lean 4.34 does not unfold the re-based square-zero
-- extension, so the two structure arrows below are comparable only once it does: both have
-- codomain `(squareZeroExtensionArtinian Λ k).obj M`, but only after unfolding.
attribute [local implicit_reducible] squareZeroCrossUnder

/-- The image under `g` of the chosen inclusion of `z₀`, preceded by the comparison
isomorphism of the base object `w₀`, lifts the structure arrow of the `ℋ`-side re-based
square-zero extension. -/
public theorem isHomLift_boundarySnd
    {pF : F ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k} (f : H ⥤ F) (g : G ⥤ F)
    {y₀ : H} {z₀ : G} (hzy : (g ⋙ pF).obj z₀ = (f ⋙ pF).obj y₀)
    {cmp : f.obj y₀ ≅ g.obj z₀}
    (hcmp : pF.IsHomLift (𝟙 ((f ⋙ pF).obj y₀)) cmp.hom)
    (PG : ChosenPushforwardsAt (g ⋙ pF) z₀) (M : FGModuleCat.{max v w} k) :
    pF.IsHomLift (squareZeroCrossUnder.{u, v, w} ((f ⋙ pF).obj y₀) M).hom
      (cmp.hom ≫ g.map
        (PG.inclusion (squareZeroCrossUnder.{u, v, w} ((g ⋙ pF).obj z₀) M))) := by
  have hc : pF.IsHomLift (eqToHom hzy.symm) cmp.hom := by
    let := hcmp
    refine IsHomLift.of_fac' pF _ cmp.hom rfl rfl ?_
    rw [IsHomLift.fac' pF (𝟙 ((f ⋙ pF).obj y₀)) cmp.hom]
    simp
  have hbase : (squareZeroCrossUnder.{u, v, w} ((f ⋙ pF).obj y₀) M).hom =
      eqToHom hzy.symm ≫ (squareZeroCrossUnder.{u, v, w} ((g ⋙ pF).obj z₀) M).hom := by
    rw [← eqToHom_comp_squareZeroCrossUnder_hom.{u, v, w} hzy M]
    simp only [eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  rw [hbase]
  let := hc
  let := isHomLift_map_inclusion g PG
    (squareZeroCrossUnder.{u, v, w} ((g ⋙ pF).obj z₀) M)
  exact IsHomLift.comp pF (eqToHom hzy.symm)
    (squareZeroCrossUnder.{u, v, w} ((g ⋙ pF).obj z₀) M).hom cmp.hom
    (g.map (PG.inclusion (squareZeroCrossUnder.{u, v, w} ((g ⋙ pF).obj z₀) M)))

/-- The image under `f` of the chosen inclusion of `y₀` is strongly cocartesian. -/
public theorem isStronglyCocartesian_boundaryFst
    {pF : F ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k} (f : H ⥤ F) {y₀ : H}
    (PH : ChosenPushforwardsAt (f ⋙ pF) y₀) (hcofF : IsCofiberedInGroupoids pF)
    (M : FGModuleCat.{max v w} k) :
    pF.IsStronglyCocartesian
      (squareZeroCrossUnder.{u, v, w} ((f ⋙ pF).obj y₀) M).hom
      (f.map (PH.inclusion (squareZeroCrossUnder.{u, v, w} ((f ⋙ pF).obj y₀) M))) :=
  isStronglyCocartesian_of_isCofiberedInGroupoids hcofF _ _
    (isHomLift_map_inclusion f PH (squareZeroCrossUnder.{u, v, w} ((f ⋙ pF).obj y₀) M))

/-- The comparison of two strongly cocartesian arrows over the same base arrow is vertical, in
both directions. -/
private theorem isHomLift_cocartesianCompare_hom_inv {F : Type u₃} [Category.{v₃} F]
    {C : Type u₂} [Category.{v₂} C] (p : F ⥤ C) {x b b' : F} {A B : C} (a : A ⟶ B)
    (u : x ⟶ b) (u' : x ⟶ b')
    [p.IsStronglyCocartesian a u] [p.IsStronglyCocartesian a u'] :
    p.IsHomLift (𝟙 B) (cocartesianCompare p a u u').hom ∧
      p.IsHomLift (𝟙 B) (cocartesianCompare p a u u').inv :=
  ⟨inferInstance, inferInstance⟩

/-- The comparison `b'` of the source: the chosen pushforward of `x₀ = f(y₀)` to the re-based
square-zero extension is vertically isomorphic to the image under `f` of the chosen
pushforward of `y₀`. Both are codomains of strongly cocartesian arrows out of `x₀` lifting the
same structure arrow, so `Deformation.cocartesianCompare` compares them. -/
public noncomputable def boundaryCompareFst
    {pF : F ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k} (f : H ⥤ F) {y₀ : H}
    (PH : ChosenPushforwardsAt (f ⋙ pF) y₀) (PF : ChosenPushforwardsAt pF (f.obj y₀))
    (hcofF : IsCofiberedInGroupoids pF) (M : FGModuleCat.{max v w} k) :
    (PF.obj (squareZeroCrossUnder.{u, v, w} ((f ⋙ pF).obj y₀) M)).1 ≅
      f.obj (PH.obj (squareZeroCrossUnder.{u, v, w} ((f ⋙ pF).obj y₀) M)).1 :=
  letI := PF.inclusion_cocartesian (squareZeroCrossUnder.{u, v, w} ((f ⋙ pF).obj y₀) M)
  letI := isStronglyCocartesian_boundaryFst.{u, v, w} f PH hcofF M
  cocartesianCompare pF (squareZeroCrossUnder.{u, v, w} ((f ⋙ pF).obj y₀) M).hom
    (PF.inclusion (squareZeroCrossUnder.{u, v, w} ((f ⋙ pF).obj y₀) M))
    (f.map (PH.inclusion (squareZeroCrossUnder.{u, v, w} ((f ⋙ pF).obj y₀) M)))

/-- The comparison `c'` of the source: the chosen pushforward of `x₀ = f(y₀)` to the re-based
square-zero extension is vertically isomorphic to the image under `g` of the chosen
pushforward of `z₀`, read through the comparison isomorphism of `w₀`. -/
public noncomputable def boundaryCompareSnd
    {pF : F ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k} (f : H ⥤ F) (g : G ⥤ F)
    {y₀ : H} {z₀ : G} (hzy : (g ⋙ pF).obj z₀ = (f ⋙ pF).obj y₀)
    {cmp : f.obj y₀ ≅ g.obj z₀}
    (hcmp : pF.IsHomLift (𝟙 ((f ⋙ pF).obj y₀)) cmp.hom)
    (PG : ChosenPushforwardsAt (g ⋙ pF) z₀) (PF : ChosenPushforwardsAt pF (f.obj y₀))
    (hcofF : IsCofiberedInGroupoids pF) (M : FGModuleCat.{max v w} k) :
    (PF.obj (squareZeroCrossUnder.{u, v, w} ((f ⋙ pF).obj y₀) M)).1 ≅
      g.obj (PG.obj (squareZeroCrossUnder.{u, v, w} ((g ⋙ pF).obj z₀) M)).1 :=
  letI := isStronglyCocartesian_of_isCofiberedInGroupoids hcofF
    (squareZeroCrossUnder.{u, v, w} ((f ⋙ pF).obj y₀) M).hom
    (cmp.hom ≫ g.map
      (PG.inclusion (squareZeroCrossUnder.{u, v, w} ((g ⋙ pF).obj z₀) M)))
    (isHomLift_boundarySnd.{u, v, w} f g hzy hcmp PG M)
  letI := PF.inclusion_cocartesian (squareZeroCrossUnder.{u, v, w} ((f ⋙ pF).obj y₀) M)
  cocartesianCompare pF (squareZeroCrossUnder.{u, v, w} ((f ⋙ pF).obj y₀) M).hom
    (PF.inclusion (squareZeroCrossUnder.{u, v, w} ((f ⋙ pF).obj y₀) M))
    (cmp.hom ≫ g.map
      (PG.inclusion (squareZeroCrossUnder.{u, v, w} ((g ⋙ pF).obj z₀) M)))

/-- The comparison `b'` is vertical, in both directions. -/
public theorem isHomLift_boundaryCompareFst
    {pF : F ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k} (f : H ⥤ F) {y₀ : H}
    (PH : ChosenPushforwardsAt (f ⋙ pF) y₀) (PF : ChosenPushforwardsAt pF (f.obj y₀))
    (hcofF : IsCofiberedInGroupoids pF) (M : FGModuleCat.{max v w} k) :
    pF.IsHomLift (𝟙 ((squareZeroExtensionArtinian.{u, w, max v w} Λ k).obj M))
        (boundaryCompareFst.{u, v, w} f PH PF hcofF M).hom ∧
      pF.IsHomLift (𝟙 ((squareZeroExtensionArtinian.{u, w, max v w} Λ k).obj M))
        (boundaryCompareFst.{u, v, w} f PH PF hcofF M).inv := by
  let := PF.inclusion_cocartesian (squareZeroCrossUnder.{u, v, w} ((f ⋙ pF).obj y₀) M)
  let := isStronglyCocartesian_boundaryFst.{u, v, w} f PH hcofF M
  exact isHomLift_cocartesianCompare_hom_inv pF _ _ _

/-- The comparison `c'` is vertical, in both directions. -/
public theorem isHomLift_boundaryCompareSnd
    {pF : F ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k} (f : H ⥤ F) (g : G ⥤ F)
    {y₀ : H} {z₀ : G} (hzy : (g ⋙ pF).obj z₀ = (f ⋙ pF).obj y₀)
    {cmp : f.obj y₀ ≅ g.obj z₀}
    (hcmp : pF.IsHomLift (𝟙 ((f ⋙ pF).obj y₀)) cmp.hom)
    (PG : ChosenPushforwardsAt (g ⋙ pF) z₀) (PF : ChosenPushforwardsAt pF (f.obj y₀))
    (hcofF : IsCofiberedInGroupoids pF) (M : FGModuleCat.{max v w} k) :
    pF.IsHomLift (𝟙 ((squareZeroExtensionArtinian.{u, w, max v w} Λ k).obj M))
        (boundaryCompareSnd.{u, v, w} f g hzy hcmp PG PF hcofF M).hom ∧
      pF.IsHomLift (𝟙 ((squareZeroExtensionArtinian.{u, w, max v w} Λ k).obj M))
        (boundaryCompareSnd.{u, v, w} f g hzy hcmp PG PF hcofF M).inv := by
  let := isStronglyCocartesian_of_isCofiberedInGroupoids hcofF _ _
    (isHomLift_boundarySnd.{u, v, w} f g hzy hcmp PG M)
  let := PF.inclusion_cocartesian (squareZeroCrossUnder.{u, v, w} ((f ⋙ pF).obj y₀) M)
  exact isHomLift_cocartesianCompare_hom_inv pF _ _ _

/-- The object the boundary map produces: for an automorphism `α` of the chosen pushforward
of `x₀ = f(y₀)` to the re-based square-zero extension by `M`, the quadruple
`(k[M], y'₀, z'₀, c' ∘ α ∘ b')` of the explicit description of the `2`-fibre product. This is
the source's `δ(α)`, and it lies over the square-zero extension `k[M]` of `𝒞_Λ` on the nose. -/
public noncomputable def boundaryObject
    {pF : F ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k} (f : H ⥤ F) (g : G ⥤ F)
    {y₀ : H} {z₀ : G} (hzy : (g ⋙ pF).obj z₀ = (f ⋙ pF).obj y₀)
    {cmp : f.obj y₀ ≅ g.obj z₀}
    (hcmp : pF.IsHomLift (𝟙 ((f ⋙ pF).obj y₀)) cmp.hom)
    (PH : ChosenPushforwardsAt (f ⋙ pF) y₀) (PG : ChosenPushforwardsAt (g ⋙ pF) z₀)
    (PF : ChosenPushforwardsAt pF (f.obj y₀)) (hcofF : IsCofiberedInGroupoids pF)
    (M : FGModuleCat.{max v w} k)
    (α : Aut (PF.obj (squareZeroCrossUnder.{u, v, w} ((f ⋙ pF).obj y₀) M))) :
    TwoFibreProductOver (f ⋙ pF) (g ⋙ pF) pF f g where
  base := (squareZeroExtensionArtinian.{u, w, max v w} Λ k).obj M
  x := (PH.obj (squareZeroCrossUnder.{u, v, w} ((f ⋙ pF).obj y₀) M)).1
  y := (PG.obj (squareZeroCrossUnder.{u, v, w} ((g ⋙ pF).obj z₀) M)).1
  hx := (PH.obj (squareZeroCrossUnder.{u, v, w} ((f ⋙ pF).obj y₀) M)).2
  hy := (PG.obj (squareZeroCrossUnder.{u, v, w} ((g ⋙ pF).obj z₀) M)).2
  iso := (boundaryCompareFst.{u, v, w} f PH PF hcofF M).symm ≪≫
    Functor.Fiber.fiberInclusion.mapIso α.asIso ≪≫
      boundaryCompareSnd.{u, v, w} f g hzy hcmp PG PF hcofF M
  vertical := by
    have h1 := (isHomLift_boundaryCompareFst.{u, v, w} f PH PF hcofF M).2
    have h2 := (isHomLift_boundaryCompareSnd.{u, v, w} f g hzy hcmp PG PF hcofF M).1
    have h3 : pF.IsHomLift (𝟙 ((squareZeroExtensionArtinian.{u, w, max v w} Λ k).obj M))
        (Functor.Fiber.fiberInclusion.map α.asIso.hom) := α.asIso.hom.2
    have h4 : pF.IsHomLift (𝟙 ((squareZeroExtensionArtinian.{u, w, max v w} Λ k).obj M))
        (Functor.Fiber.fiberInclusion.map α.asIso.hom ≫
          (boundaryCompareSnd.{u, v, w} f g hzy hcmp PG PF hcofF M).hom) :=
      @IsHomLift.comp_of_lift_id _ _ _ _ pF _ _ _ _ _ _ h3 h2
    exact @IsHomLift.comp_of_lift_id _ _ _ _ pF _ _ _ _ _ _ h1 h4

/-- The boundary map of the six-term sequence, at the level of isomorphism classes: the class in
`T𝒲` of the object `Deformation.boundaryObject`, i.e. of the quadruple
`(k[M], y'₀, z'₀, c' ∘ α ∘ b')`. -/
public noncomputable def boundaryClass
    {pF : F ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k} (f : H ⥤ F) (g : G ⥤ F)
    {y₀ : H} {z₀ : G} (hzy : (g ⋙ pF).obj z₀ = (f ⋙ pF).obj y₀)
    {cmp : f.obj y₀ ≅ g.obj z₀}
    (hcmp : pF.IsHomLift (𝟙 ((f ⋙ pF).obj y₀)) cmp.hom)
    (PH : ChosenPushforwardsAt (f ⋙ pF) y₀) (PG : ChosenPushforwardsAt (g ⋙ pF) z₀)
    (PF : ChosenPushforwardsAt pF (f.obj y₀)) (hcofF : IsCofiberedInGroupoids pF)
    (hcofW : IsCofiberedInGroupoids
      (TwoFibreProductOver.structureFunctor (f ⋙ pF) (g ⋙ pF) pF f g))
    (M : FGModuleCat.{max v w} k)
    (α : Aut (PF.obj (squareZeroCrossUnder.{u, v, w} ((f ⋙ pF).obj y₀) M))) :
    (isomorphismClasses (BasedCategory.ofFunctor
        (TwoFibreProductOver.structureFunctor (f ⋙ pF) (g ⋙ pF) pF f g)) hcofW).obj
      ((squareZeroExtensionArtinian.{u, w, max v w} Λ k).obj M) :=
  classOf _ hcofW ⟨boundaryObject.{u, v, w} f g hzy hcmp PH PG PF hcofF M α, rfl⟩

/-- The boundary map, read in the value of the canonical linear lift of the associated
square-zero functor of `𝒲` — that is, in `T𝒲` with its vector-space structure. -/
public noncomputable def boundaryFun
    {pF : F ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k} (f : H ⥤ F) (g : G ⥤ F)
    {y₀ : H} {z₀ : G} (hzy : (g ⋙ pF).obj z₀ = (f ⋙ pF).obj y₀)
    {cmp : f.obj y₀ ≅ g.obj z₀}
    (hcmp : pF.IsHomLift (𝟙 ((f ⋙ pF).obj y₀)) cmp.hom)
    (PH : ChosenPushforwardsAt (f ⋙ pF) y₀) (PG : ChosenPushforwardsAt (g ⋙ pF) z₀)
    (PF : ChosenPushforwardsAt pF (f.obj y₀)) (hcofF : IsCofiberedInGroupoids pF)
    (hpreW : IsPredeformationCategory.{u, v, w}
      (BasedCategory.ofFunctor
        (TwoFibreProductOver.structureFunctor (f ⋙ pF) (g ⋙ pF) pF f g)).p)
    (hS2W : SchlessingerConditionS2 (Functor.Elements.π (isomorphismClasses
      (BasedCategory.ofFunctor
        (TwoFibreProductOver.structureFunctor (f ⋙ pF) (g ⋙ pF) pF f g)) hpreW.cofibered)))
    (M : FGModuleCat.{max v w} k)
    (α : Aut (PF.obj (squareZeroCrossUnder.{u, v, w} ((f ⋙ pF).obj y₀) M))) :
    ↥((associatedTangentSpaceModuleStructure.{u, v, w} (BasedCategory.ofFunctor
      (TwoFibreProductOver.structureFunctor (f ⋙ pF) (g ⋙ pF) pF f g))
        hpreW hS2W).functor.obj M) :=
  cast (associatedTangentLift_carrier.{u, v, w} _ hpreW hS2W M).symm
    (boundaryClass.{u, v, w} f g hzy hcmp PH PG PF hcofF hpreW.cofibered M α)

end Boundary

end Deformation

end

