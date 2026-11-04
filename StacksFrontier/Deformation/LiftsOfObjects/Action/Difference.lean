module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Module.OppositeOfCommSemiring
public import StacksFrontier.Deformation.LiftsOfObjects.Action.LiftClassesFiber
public import StacksFrontier.Deformation.LiftsOfObjects.InfinitesimalDifference
public import StacksFrontier.Deformation.PredeformationTangent.DerivationMapLinear
public import StacksFrontier.Deformation.Schlessinger.AssociatedFunctor

/-!
# The infinitesimal difference of two lifts

Let `𝓕` be a deformation category over `𝒞_Λ`, let `f : A' ⟶ A` be a surjection whose kernel
`I` is annihilated by the maximal ideal of `A'`, and let `x` be an object of the fibre of `𝓕`
over `A`. Two lifts of `x` along `f` have a fibre product over `x`, a lift of `x` along
`A' ×_A A' → A`; pushing that fibre product forward along the infinitesimal difference map
`(a₁, a₂) ↦ (ā₁, a₂ - a₁)` gives an element of the associated functor of isomorphism classes
at the square-zero extension `k[I]`, hence — through the canonical tangent-space
identification — an element of `T𝓕 ⊗_k I`.

This file constructs that element and proves the two facts the free transitive action rests
on: the difference is additive in the module coordinate, and it satisfies the cocycle
identity `d(a,b) + d(b,c) = d(a,c)`.

## Main definitions

* `Deformation.tensorCoordinate`: the canonical identification of the associated functor at
  `k[V]` with `T𝓕 ⊗_k V`.
* `Deformation.differenceClass`: the class of the pushforward of the fibre product of two
  lifts along the infinitesimal difference map.
* `Deformation.squareZeroPair`: a pair of morphisms to square-zero extensions with equal
  residue coordinate, assembled into one morphism to the square-zero extension of the
  product.

## Main results

* `Deformation.tensorCoordinate_map_add`: the identification is additive in the morphism of
  vector spaces.
* `Deformation.differenceClass_representatives`: on representatives, the difference class is
  the pushforward of the class of their fibre product.
* `Deformation.difference_cocycle`: the cocycle identity.

## Implementation notes

The cocycle identity is proved by forming the triple fibre product `w` of `z₁₂` (the fibre
product of the first two lifts) with the third lift, mapping it to the three pairwise fibre
products, and comparing the three pushforwards there. The comparison is carried out in one
morphism `A' ×_A A' ⟶ k[I × I]` whose two coordinates are the pushforwards of `z₁₂` and
`z₂₃`, so that additivity of `tensorCoordinate` in the morphism argument gives the identity;
`squareZeroPair` is that assembly and `squareZeroPair_add` is the computation that its sum
coordinate is the pushforward of `z₁₃`.

`tensorCoordinate` is an `Equiv` rather than a `LinearEquiv` because the module structure on
the associated functor at `k[V]` is only available through the linear lift, and the only use
made of linearity is `tensorCoordinate_map_add`.

## References

* [Stacks Project, Tag 06JI](https://stacks.math.columbia.edu/tag/06JI)
-/

@[expose] public section

namespace Deformation

/-! ### The tangent-space coordinate of the associated functor -/

section
open CategoryTheory CategoryTheory.Limits IsLocalRing
universe u w uF vF

/-- The transport of the associated functor at the square-zero extension `k[V]` across the
defining equation of the canonical linear lift. The ascription is the point: stated at the
type `(isomorphismClasses 𝓕 _).obj (k[V])` rather than at the unfolded presentation of the
linear lift, it keeps every later goal type-correct without unfolding the square-zero
functor. -/
public noncomputable def tangentLiftCoord
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    (𝓕 : BasedCategory.{vF, uF} (ArtinianLocalAlgCat.{u, w, w} Λ k))
    (h𝓕 : IsDeformationCategory 𝓕.p)
    (hS2 : SchlessingerConditionS2
      (CategoryOfElements.π (isomorphismClasses 𝓕 h𝓕.predeformation.cofibered)))
    (V : FGModuleCat.{w} k) :
    (isomorphismClasses 𝓕 h𝓕.predeformation.cofibered).obj
        ((squareZeroExtensionArtinian Λ k).obj V) ≃
      (((associatedTangentSpaceModuleStructureUnlifted
        𝓕 h𝓕.predeformation hS2).functor.obj V : ModuleCat.{uF} k) : Type uF) :=
  Equiv.cast (congrArg (fun G : FGModuleCat.{w} k ⥤ Type uF => G.obj V)
    (associatedTangentSpaceModuleStructureUnlifted
      𝓕 h𝓕.predeformation hS2).forget_comp).symm

/-- The transport is natural in the vector space. -/
public lemma tangentLiftCoord_map
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    (𝓕 : BasedCategory.{vF, uF} (ArtinianLocalAlgCat.{u, w, w} Λ k))
    (h𝓕 : IsDeformationCategory 𝓕.p)
    (hS2 : SchlessingerConditionS2
      (CategoryOfElements.π (isomorphismClasses 𝓕 h𝓕.predeformation.cofibered)))
    {V₁ V₂ : FGModuleCat.{w} k} (h : V₁ ⟶ V₂)
    (y : (isomorphismClasses 𝓕 h𝓕.predeformation.cofibered).obj
      ((squareZeroExtensionArtinian Λ k).obj V₁)) :
    tangentLiftCoord 𝓕 h𝓕 hS2 V₂
        ((isomorphismClasses 𝓕 h𝓕.predeformation.cofibered).map
          ((squareZeroExtensionArtinian Λ k).map h) y) =
      ((associatedTangentSpaceModuleStructureUnlifted
          𝓕 h𝓕.predeformation hS2).functor.map h).hom
        (tangentLiftCoord 𝓕 h𝓕 hS2 V₁ y) :=
  functor_map_cast (R := k)
    (associatedTangentSpaceModuleStructureUnlifted 𝓕 h𝓕.predeformation hS2).forget_comp h y

/-- The canonical identification of the associated functor of isomorphism classes, evaluated
at the square-zero extension `k[V]`, with the tensor product of the tangent space with `V`. -/
public noncomputable def tensorCoordinate
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    (𝓕 : BasedCategory.{vF, uF} (ArtinianLocalAlgCat.{u, w, w} Λ k))
    (h𝓕 : IsDeformationCategory 𝓕.p) (V : FGModuleCat.{w} k) :
    let hS2 := schlessingerConditionS2_of_isIsomorphismClasses
      𝓕 h𝓕.predeformation.cofibered
      (schlessingerConditionS2_of_satisfiesRS h𝓕.satisfiesRS)
      (.inl h𝓕.predeformation)
    letI : Fact (IsPredeformationCategory 𝓕.p) := ⟨h𝓕.predeformation⟩
    letI : Fact (SchlessingerConditionS2
      (CategoryOfElements.π (isomorphismClasses 𝓕 h𝓕.predeformation.cofibered))) := ⟨hS2⟩
    (isomorphismClasses 𝓕 h𝓕.predeformation.cofibered).obj
      ((squareZeroExtensionArtinian Λ k).obj V) ≃
      TensorProduct k (artinianTangentSpace Λ k
        (isomorphismClasses 𝓕 h𝓕.predeformation.cofibered)) V := by
  intro hS2
  exact (tangentLiftCoord 𝓕 h𝓕 hS2 V).trans
    (associatedTangentSpaceFunctor_iso_tensorLeftUnlifted
      𝓕 h𝓕.predeformation hS2 V).toEquiv.symm

/-- The tangent-space coordinate is the inverse of the canonical tensor identification,
composed with the transport of the linear lift. -/
public lemma iso_tensorCoordinate
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    (𝓕 : BasedCategory.{vF, uF} (ArtinianLocalAlgCat.{u, w, w} Λ k))
    (h𝓕 : IsDeformationCategory 𝓕.p)
    (hS2 : SchlessingerConditionS2
      (CategoryOfElements.π (isomorphismClasses 𝓕 h𝓕.predeformation.cofibered)))
    (V : FGModuleCat.{w} k)
    (y : (isomorphismClasses 𝓕 h𝓕.predeformation.cofibered).obj
      ((squareZeroExtensionArtinian Λ k).obj V)) :
    associatedTangentSpaceFunctor_iso_tensorLeftUnlifted 𝓕 h𝓕.predeformation hS2 V
        (tensorCoordinate 𝓕 h𝓕 V y) = tangentLiftCoord 𝓕 h𝓕 hS2 V y :=
  (associatedTangentSpaceFunctor_iso_tensorLeftUnlifted
    𝓕 h𝓕.predeformation hS2 V).apply_symm_apply _

/-- The tangent-space coordinate is additive in the morphism of vector spaces along which the
class is pushed forward. -/
public lemma tensorCoordinate_map_add
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    (𝓕 : BasedCategory.{vF, uF} (ArtinianLocalAlgCat.{u, w, w} Λ k))
    (h𝓕 : IsDeformationCategory 𝓕.p)
    (hS2 : SchlessingerConditionS2
      (CategoryOfElements.π (isomorphismClasses 𝓕 h𝓕.predeformation.cofibered)))
    (V W : FGModuleCat.{w} k) (f g : V ⟶ W)
    (z : (isomorphismClasses 𝓕 h𝓕.predeformation.cofibered).obj
      ((squareZeroExtensionArtinian Λ k).obj V)) :
    tensorCoordinate 𝓕 h𝓕 W ((isomorphismClasses 𝓕 h𝓕.predeformation.cofibered).map
          ((squareZeroExtensionArtinian Λ k).map (f + g)) z) =
      tensorCoordinate 𝓕 h𝓕 W ((isomorphismClasses 𝓕 h𝓕.predeformation.cofibered).map
          ((squareZeroExtensionArtinian Λ k).map f) z) +
        tensorCoordinate 𝓕 h𝓕 W ((isomorphismClasses 𝓕 h𝓕.predeformation.cofibered).map
          ((squareZeroExtensionArtinian Λ k).map g) z) := by
  apply (associatedTangentSpaceFunctor_iso_tensorLeftUnlifted
    𝓕 h𝓕.predeformation hS2 W).injective
  rw [map_add, iso_tensorCoordinate, iso_tensorCoordinate, iso_tensorCoordinate,
    tangentLiftCoord_map, tangentLiftCoord_map, tangentLiftCoord_map,
    (associatedTangentSpaceModuleStructureUnlifted
      𝓕 h𝓕.predeformation hS2).functor.map_add]
  rfl

end

/-! ### The difference class of two lifts -/

section
open CategoryTheory CategoryTheory.Limits IsLocalRing
universe u w uF vF

/-- The class, in the associated functor of isomorphism classes at the target of the
infinitesimal difference map, of the pushforward of the fibre product of two lifts. -/
public noncomputable def differenceClass
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    (𝓕 : BasedCategory.{vF, uF} (ArtinianLocalAlgCat.{u, w, w} Λ k))
    (h𝓕 : IsDeformationCategory 𝓕.p)
    {A' A : ArtinianLocalAlgCat.{u, w, w} Λ k}
    (f : A' ⟶ A) (hf : Function.Surjective f.hom)
    (hann : ∀ a : A', a ∈ maximalIdeal A' →
      ∀ i : RingHom.ker f.hom.toRingHom, a * (i : A') = 0)
    (x : 𝓕.p.Fiber A) (a b : LiftClasses 𝓕.p f x) :
    (isomorphismClasses 𝓕 h𝓕.predeformation.cofibered).obj
      (infinitesimalDifferenceMap f hf hann).target :=
  let hP := ArtinianLocalAlgCat.isPullback_of_surjective f f (.inl hf)
  let E := Classical.choice (liftClassesProdEquivPullback 𝓕.p h𝓕.satisfiesRS
    hP.cone hP.isLimit (.inl hf) x)
  (isomorphismClasses 𝓕 h𝓕.predeformation.cofibered).map
    (infinitesimalDifferenceMap f hf hann).g
      (liftSourceClass 𝓕 h𝓕.predeformation.cofibered _ x (E.equiv (a, b)))

/-- On representatives, the difference class is the pushforward along the infinitesimal
difference map of the class of the fibre product of the two lifts. -/
public theorem differenceClass_representatives
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    (𝓕 : BasedCategory.{vF, uF} (ArtinianLocalAlgCat.{u, w, w} Λ k))
    (h𝓕 : IsDeformationCategory 𝓕.p)
    {A' A : ArtinianLocalAlgCat.{u, w, w} Λ k}
    (f : A' ⟶ A) (hf : Function.Surjective f.hom)
    (hann : ∀ a : A', a ∈ maximalIdeal A' →
      ∀ i : RingHom.ker f.hom.toRingHom, a * (i : A') = 0)
    (x : 𝓕.p.Fiber A) (a b : Lift 𝓕.p f x) :
    let hP := ArtinianLocalAlgCat.isPullback_of_surjective f f (.inl hf)
    ∃ z : Lift 𝓕.p (hP.cone.fst ≫ f) x,
      IsFiberProductOf hP.cone z a b ∧
      differenceClass 𝓕 h𝓕 f hf hann x (ThinSkeleton.mk a) (ThinSkeleton.mk b) =
        (isomorphismClasses 𝓕 h𝓕.predeformation.cofibered).map
          (infinitesimalDifferenceMap f hf hann).g
          (classOf 𝓕 h𝓕.predeformation.cofibered
            ((liftForgetFunctor 𝓕.p _ x).obj z)) := by
  let hP := ArtinianLocalAlgCat.isPullback_of_surjective f f (.inl hf)
  let E := Classical.choice (liftClassesProdEquivPullback 𝓕.p h𝓕.satisfiesRS
    hP.cone hP.isLimit (.inl hf) x)
  obtain ⟨z, hz, he⟩ := E.maps_pair_to_fiberProduct a b
  refine ⟨z, hz, ?_⟩
  dsimp only [differenceClass]
  rw [he]
  exact congrArg _ (liftSourceClass_mk 𝓕 h𝓕.predeformation.cofibered _ x z)

end

/-! ### Pairing two morphisms into square-zero extensions -/

section
open CategoryTheory IsLocalRing
universe u w

/-- The opposite scalar action on a finite-dimensional vector space, as used by the
square-zero extension functor. Named rather than anonymous so that two modules declaring it
cannot generate the same auto-generated constant. -/
local instance squareZeroPairModuleMulOpposite
    {k : Type w} [Field k] (V : FGModuleCat.{w} k) : Module kᵐᵒᵖ V :=
  Module.oppositeOfCommSemiring k V

/-- The two scalar actions on a finite-dimensional vector space agree. -/
local instance squareZeroPairIsCentralScalar
    {k : Type w} [Field k] (V : FGModuleCat.{w} k) : IsCentralScalar k V :=
  Module.isCentralScalar_oppositeOfCommSemiring k V

/-- The underlying algebra map of `k[φ]` is `TrivSqZeroExt.map φ`. -/
public lemma squareZeroExtensionArtinian_map_hom
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {V W : FGModuleCat.{w} k} (φ : V ⟶ W)
    (y : ((squareZeroExtensionArtinian Λ k).obj V : ArtinianLocalAlgCat.{u, w, w} Λ k)) :
    ((squareZeroExtensionArtinian Λ k).map φ).hom y =
      TrivSqZeroExt.map (R' := k) φ.hom.hom y := rfl

/-- The residue coordinate is unchanged by `k[φ]`. -/
public lemma squareZeroExtensionArtinian_map_fst
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {V W : FGModuleCat.{w} k} (φ : V ⟶ W)
    (y : ((squareZeroExtensionArtinian Λ k).obj V : ArtinianLocalAlgCat.{u, w, w} Λ k)) :
    (((squareZeroExtensionArtinian Λ k).map φ).hom y).fst = TrivSqZeroExt.fst y := by
  rw [squareZeroExtensionArtinian_map_hom]
  exact TrivSqZeroExt.fst_map _ _

/-- The module coordinate is carried by `φ` under `k[φ]`. -/
public lemma squareZeroExtensionArtinian_map_snd
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {V W : FGModuleCat.{w} k} (φ : V ⟶ W)
    (y : ((squareZeroExtensionArtinian Λ k).obj V : ArtinianLocalAlgCat.{u, w, w} Λ k)) :
    (((squareZeroExtensionArtinian Λ k).map φ).hom y).snd = φ.hom.hom (TrivSqZeroExt.snd y) := by
  rw [squareZeroExtensionArtinian_map_hom]
  exact TrivSqZeroExt.snd_map _ _

/-- Two morphisms of `𝒞_Λ` from a common source into square-zero extensions have the same
residue coordinate, so they assemble into one morphism into the square-zero extension of the
product of the two vector spaces. -/
public noncomputable def squareZeroPair
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {R : ArtinianLocalAlgCat.{u, w, w} Λ k} (V W : FGModuleCat.{w} k)
    (f : R ⟶ (squareZeroExtensionArtinian Λ k).obj V)
    (g : R ⟶ (squareZeroExtensionArtinian Λ k).obj W) :
    R ⟶ (squareZeroExtensionArtinian Λ k).obj (FGModuleCat.of k (V × W)) := by
  have hfst (r : R) : (f.hom r).fst = (g.hom r).fst :=
    (f.residue_comm r).trans (g.residue_comm r).symm
  letI : CommRing (TrivSqZeroExt k (V × W)) :=
    ((squareZeroExtensionArtinian Λ k).obj (FGModuleCat.of k (V × W))).commRing
  letI : Algebra Λ (TrivSqZeroExt k (V × W)) :=
    ((squareZeroExtensionArtinian Λ k).obj (FGModuleCat.of k (V × W))).algebra
  let h : R →ₐ[Λ] TrivSqZeroExt k (V × W) :=
    { toFun := fun r => ⟨(f.hom r).fst, ((f.hom r).snd, (g.hom r).snd)⟩
      map_one' := by
        apply TrivSqZeroExt.ext
        · exact congrArg (fun z : TrivSqZeroExt k V => z.fst) f.hom.map_one
        · exact Prod.ext (congrArg (fun z : TrivSqZeroExt k V => z.snd) f.hom.map_one)
            (congrArg (fun z : TrivSqZeroExt k W => z.snd) g.hom.map_one)
      map_mul' := by
        intro a b
        apply TrivSqZeroExt.ext
        · exact congrArg (fun z : TrivSqZeroExt k V => z.fst) (f.hom.map_mul a b)
        · apply Prod.ext
          · exact congrArg (fun z : TrivSqZeroExt k V => z.snd) (f.hom.map_mul a b)
          · change (g.hom (a * b)).snd =
              (f.hom a).fst • (g.hom b).snd + (f.hom b).fst • (g.hom a).snd
            rw [hfst a, hfst b]
            exact congrArg (fun z : TrivSqZeroExt k W => z.snd) (g.hom.map_mul a b)
      map_zero' := by
        apply TrivSqZeroExt.ext
        · exact congrArg (fun z : TrivSqZeroExt k V => z.fst) f.hom.map_zero
        · exact Prod.ext (congrArg (fun z : TrivSqZeroExt k V => z.snd) f.hom.map_zero)
            (congrArg (fun z : TrivSqZeroExt k W => z.snd) g.hom.map_zero)
      map_add' := by
        intro a b
        apply TrivSqZeroExt.ext
        · exact congrArg (fun z : TrivSqZeroExt k V => z.fst) (f.hom.map_add a b)
        · exact Prod.ext (congrArg (fun z : TrivSqZeroExt k V => z.snd) (f.hom.map_add a b))
            (congrArg (fun z : TrivSqZeroExt k W => z.snd) (g.hom.map_add a b))
      commutes' := by
        intro r
        apply TrivSqZeroExt.ext
        · exact congrArg (fun z : TrivSqZeroExt k V => z.fst) (f.hom.commutes r)
        · exact Prod.ext (congrArg (fun z : TrivSqZeroExt k V => z.snd) (f.hom.commutes r))
            (congrArg (fun z : TrivSqZeroExt k W => z.snd) (g.hom.commutes r)) }
  exact
    { hom := h
      isLocal := by
        constructor
        intro r hr
        apply f.isLocal.map_nonunit r
        apply TrivSqZeroExt.isUnit_iff_isUnit_fst.mpr
        exact (TrivSqZeroExt.isUnit_iff_isUnit_fst (x := h r)).mp hr
      residue_comm := fun r => f.residue_comm r }

/-- A morphism into a square-zero extension factors as the pair followed by `k[φ]` as soon as
its residue and module coordinates are those of the pair, transported along `φ`. -/
private theorem squareZeroPair_comp_map_eq
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {R : ArtinianLocalAlgCat.{u, w, w} Λ k} {V W : FGModuleCat.{w} k} (U : FGModuleCat.{w} k)
    (f : R ⟶ (squareZeroExtensionArtinian Λ k).obj V)
    (g : R ⟶ (squareZeroExtensionArtinian Λ k).obj W)
    (φ : FGModuleCat.of k (V × W) ⟶ U) (h : R ⟶ (squareZeroExtensionArtinian Λ k).obj U)
    (hfst : ∀ r : R, (h.hom r).fst = (f.hom r).fst)
    (hsnd : ∀ r : R, (h.hom r).snd = φ.hom.hom ((f.hom r).snd, (g.hom r).snd)) :
    squareZeroPair V W f g ≫ (squareZeroExtensionArtinian Λ k).map φ = h := by
  apply ArtinianLocalAlgCat.hom_ext
  apply AlgHom.ext
  intro r
  apply TrivSqZeroExt.ext
  · rw [ArtinianLocalAlgCat.comp_hom, AlgHom.comp_apply, squareZeroExtensionArtinian_map_fst,
      hfst]
    rfl
  · rw [ArtinianLocalAlgCat.comp_hom, AlgHom.comp_apply, squareZeroExtensionArtinian_map_snd,
      hsnd]
    rfl

/-- The first coordinate of the paired morphism is the first of the two morphisms. -/
public lemma squareZeroPair_fst
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {R : ArtinianLocalAlgCat.{u, w, w} Λ k} (V W : FGModuleCat.{w} k)
    (f : R ⟶ (squareZeroExtensionArtinian Λ k).obj V)
    (g : R ⟶ (squareZeroExtensionArtinian Λ k).obj W) :
    squareZeroPair V W f g ≫ (squareZeroExtensionArtinian Λ k).map
      (FGModuleCat.ofHom (LinearMap.fst k V W)) = f :=
  squareZeroPair_comp_map_eq _ f g _ f (fun _ => rfl) (fun _ => rfl)

/-- The second coordinate of the paired morphism is the second of the two morphisms. -/
public lemma squareZeroPair_snd
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {R : ArtinianLocalAlgCat.{u, w, w} Λ k} (V W : FGModuleCat.{w} k)
    (f : R ⟶ (squareZeroExtensionArtinian Λ k).obj V)
    (g : R ⟶ (squareZeroExtensionArtinian Λ k).obj W) :
    squareZeroPair V W f g ≫ (squareZeroExtensionArtinian Λ k).map
      (FGModuleCat.ofHom (LinearMap.snd k V W)) = g :=
  squareZeroPair_comp_map_eq _ f g _ g
    (fun r => (g.residue_comm r).trans (f.residue_comm r).symm) (fun _ => rfl)

/-- If a third morphism has module coordinate the sum of the module coordinates of two
others, then the sum of the two projections carries the paired morphism to it. -/
public lemma squareZeroPair_add
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {R : ArtinianLocalAlgCat.{u, w, w} Λ k} (V : FGModuleCat.{w} k)
    (f g h : R ⟶ (squareZeroExtensionArtinian Λ k).obj V)
    (hsnd : ∀ r : R, (h.hom r).snd = (f.hom r).snd + (g.hom r).snd) :
    squareZeroPair V V f g ≫ (squareZeroExtensionArtinian Λ k).map
      (FGModuleCat.ofHom (LinearMap.fst k V V) +
        FGModuleCat.ofHom (LinearMap.snd k V V)) = h :=
  squareZeroPair_comp_map_eq _ f g _ h
    (fun r => (h.residue_comm r).trans (f.residue_comm r).symm) hsnd

end

/-! ### The cocycle identity -/

section
open CategoryTheory CategoryTheory.Limits IsLocalRing
universe u w uF vF

/-- The infinitesimal differences of three lifts satisfy the cocycle identity. -/
public lemma difference_cocycle
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    (𝓕 : BasedCategory.{vF, uF} (ArtinianLocalAlgCat.{u, w, w} Λ k))
    (h𝓕 : IsDeformationCategory 𝓕.p)
    {A' A : ArtinianLocalAlgCat.{u, w, w} Λ k}
    (f : A' ⟶ A) (hf : Function.Surjective f.hom)
    (hann : ∀ a : A', a ∈ maximalIdeal A' →
      ∀ i : RingHom.ker f.hom.toRingHom, a * (i : A') = 0)
    (x : 𝓕.p.Fiber A) :
    letI : Module k (RingHom.ker f.hom.toRingHom) := kernelModule f hann
    letI : Module.Finite k (RingHom.ker f.hom.toRingHom) := kernelModule_finite f hann
    let V := FGModuleCat.of k (RingHom.ker f.hom.toRingHom)
    let d := fun a b => tensorCoordinate 𝓕 h𝓕 V (differenceClass 𝓕 h𝓕 f hf hann x a b)
    ∀ a b c : LiftClasses 𝓕.p f x, d a b + d b c = d a c := by
  classical
  let : Module k (RingHom.ker f.hom.toRingHom) := kernelModule f hann
  let : Module.Finite k (RingHom.ker f.hom.toRingHom) := kernelModule_finite f hann
  let hS2 := schlessingerConditionS2_of_isIsomorphismClasses
    𝓕 h𝓕.predeformation.cofibered
    (schlessingerConditionS2_of_satisfiesRS h𝓕.satisfiesRS)
    (.inl h𝓕.predeformation)
  let V := FGModuleCat.of k (RingHom.ker f.hom.toRingHom)
  let H := isomorphismClasses 𝓕 h𝓕.predeformation.cofibered
  let S := squareZeroExtensionArtinian Λ k
  let g := infinitesimalDifferenceMap f hf hann
  let hP := ArtinianLocalAlgCat.isPullback_of_surjective f f (.inl hf)
  let p₁ := ArtinianLocalAlgCat.pullbackFst_of_surjective f f (.inl hf)
  let p₂ := ArtinianLocalAlgCat.pullbackSnd_of_surjective f f (.inl hf)
  dsimp only
  intro a b c
  obtain ⟨a, rfl⟩ : ∃ a' : Lift 𝓕.p f x, ThinSkeleton.mk a' = a := Quotient.exists_rep a
  obtain ⟨b, rfl⟩ : ∃ b' : Lift 𝓕.p f x, ThinSkeleton.mk b' = b := Quotient.exists_rep b
  obtain ⟨c, rfl⟩ : ∃ c' : Lift 𝓕.p f x, ThinSkeleton.mk c' = c := Quotient.exists_rep c
  obtain ⟨z₁₂, ⟨r₁₂, r₂₁, hw₁₂, hr₁₂, hr₂₁, hf₁₂, hf₂₁, hl₁₂⟩, hd₁₂⟩ :=
    differenceClass_representatives 𝓕 h𝓕 f hf hann x a b
  obtain ⟨z₂₃, ⟨r₂₃, r₃₂, hw₂₃, hr₂₃, hr₃₂, hf₂₃, hf₃₂, hl₂₃⟩, hd₂₃⟩ :=
    differenceClass_representatives 𝓕 h𝓕 f hf hann x b c
  obtain ⟨z₁₃, ⟨r₁₃, r₃₁, hw₁₃, hr₁₃, hr₃₁, hf₁₃, hf₃₁, hl₁₃⟩, hd₁₃⟩ :=
    differenceClass_representatives 𝓕 h𝓕 f hf hann x a c
  have hr₁₂' : 𝓕.p.IsHomLift p₁ r₁₂ := hr₁₂
  have hr₂₁' : 𝓕.p.IsHomLift p₂ r₂₁ := hr₂₁
  have hr₂₃' : 𝓕.p.IsHomLift p₁ r₂₃ := hr₂₃
  have hr₃₂' : 𝓕.p.IsHomLift p₂ r₃₂ := hr₃₂
  have hr₁₃' : 𝓕.p.IsHomLift p₁ r₁₃ := hr₁₃
  have hr₃₁' : 𝓕.p.IsHomLift p₂ r₃₁ := hr₃₁
  let := hr₁₂'
  let := hr₂₁'
  let := hr₂₃'
  let := hr₃₂'
  let := hr₁₃'
  let := hr₃₁'
  have h₂₃ : IsPullback r₂₃ r₃₂ b.hom c.hom := ⟨⟨hw₂₃⟩, hl₂₃⟩
  have h₁₃ : IsPullback r₁₃ r₃₁ a.hom c.hom := ⟨⟨hw₁₃⟩, hl₁₃⟩
  let hR := ArtinianLocalAlgCat.isPullback_of_surjective (p₁ ≫ f) f (.inr hf)
  let s₁ := ArtinianLocalAlgCat.pullbackFst_of_surjective (p₁ ≫ f) f (.inr hf)
  let s₂ := ArtinianLocalAlgCat.pullbackSnd_of_surjective (p₁ ≫ f) f (.inr hf)
  let E := Classical.choice (liftClassesProdEquivPullback 𝓕.p h𝓕.satisfiesRS
    hR.cone hR.isLimit (.inr hf) x)
  obtain ⟨w, ⟨q₁, q₂, hw, hq₁, hq₂, hfq₁, hfq₂, hlw⟩, hew⟩ :=
    E.maps_pair_to_fiberProduct z₁₂ c
  have hq₁' : 𝓕.p.IsHomLift s₁ q₁ := hq₁
  have hq₂' : 𝓕.p.IsHomLift s₂ q₂ := hq₂
  let := hq₁'
  let := hq₂'
  have hb₂₃ : (s₁ ≫ p₂) ≫ f = s₂ ≫ f := by
    calc
      (s₁ ≫ p₂) ≫ f = s₁ ≫ (p₁ ≫ f) :=
        (Category.assoc s₁ p₂ f).trans (congrArg (s₁ ≫ ·) hP.w.symm)
      _ = s₂ ≫ f := hR.w
  have hb₁₃ : (s₁ ≫ p₁) ≫ f = s₂ ≫ f :=
    (Category.assoc s₁ p₁ f).trans hR.w
  have hw₂₃' : (q₁ ≫ r₂₁) ≫ b.hom = q₂ ≫ c.hom := by
    rw [Category.assoc, hf₂₁, hw]
  have hw₁₃' : (q₁ ≫ r₁₂) ≫ a.hom = q₂ ≫ c.hom := by
    rw [Category.assoc, hf₁₂, hw]
  have hq₂₃₁ : 𝓕.p.IsHomLift (hP.lift (s₁ ≫ p₂) s₂ hb₂₃ ≫ p₁)
      (h₂₃.lift (q₁ ≫ r₂₁) q₂ hw₂₃' ≫ r₂₃) := by
    rw [hP.lift_fst, h₂₃.lift_fst]
    exact CategoryTheory.IsHomLift.comp 𝓕.p s₁ p₂ q₁ r₂₁
  have hq₂₃₂ : 𝓕.p.IsHomLift (hP.lift (s₁ ≫ p₂) s₂ hb₂₃ ≫ p₂)
      (h₂₃.lift (q₁ ≫ r₂₁) q₂ hw₂₃' ≫ r₃₂) := by
    rw [hP.lift_snd, h₂₃.lift_snd]
    exact hq₂'
  have hq₁₃₁ : 𝓕.p.IsHomLift (hP.lift (s₁ ≫ p₁) s₂ hb₁₃ ≫ p₁)
      (h₁₃.lift (q₁ ≫ r₁₂) q₂ hw₁₃' ≫ r₁₃) := by
    rw [hP.lift_fst, h₁₃.lift_fst]
    exact CategoryTheory.IsHomLift.comp 𝓕.p s₁ p₁ q₁ r₁₂
  have hq₁₃₂ : 𝓕.p.IsHomLift (hP.lift (s₁ ≫ p₁) s₂ hb₁₃ ≫ p₂)
      (h₁₃.lift (q₁ ≫ r₁₂) q₂ hw₁₃' ≫ r₃₁) := by
    rw [hP.lift_snd, h₁₃.lift_snd]
    exact hq₂'
  let t₂₃ := hP.lift (s₁ ≫ p₂) s₂ hb₂₃
  let t₁₃ := hP.lift (s₁ ≫ p₁) s₂ hb₁₃
  let q₂₃ := h₂₃.lift (q₁ ≫ r₂₁) q₂ hw₂₃'
  let q₁₃ := h₁₃.lift (q₁ ≫ r₁₂) q₂ hw₁₃'
  have ht₂₃ : 𝓕.p.IsHomLift t₂₃ q₂₃ :=
    isHomLift_of_pullback_projections 𝓕.p hP r₂₃ r₃₂ hr₂₃' hr₃₂' t₂₃ q₂₃ hq₂₃₁ hq₂₃₂
  have ht₁₃ : 𝓕.p.IsHomLift t₁₃ q₁₃ :=
    isHomLift_of_pullback_projections 𝓕.p hP r₁₃ r₃₁ hr₁₃' hr₃₁' t₁₃ q₁₃ hq₁₃₁ hq₁₃₂
  let := ht₂₃
  let := ht₁₃
  let w₀ : 𝓕.p.Fiber (ArtinianLocalAlgCat.pullbackObj_of_surjective (p₁ ≫ f) f (.inr hf)) :=
    (liftForgetFunctor 𝓕.p _ x).obj w
  let z₁₂₀ := (liftForgetFunctor 𝓕.p _ x).obj z₁₂
  let z₂₃₀ := (liftForgetFunctor 𝓕.p _ x).obj z₂₃
  let z₁₃₀ := (liftForgetFunctor 𝓕.p _ x).obj z₁₃
  have hmap₁₂ : H.map s₁ (classOf 𝓕 h𝓕.predeformation.cofibered w₀) =
      classOf 𝓕 h𝓕.predeformation.cofibered z₁₂₀ :=
    map_classOf 𝓕 h𝓕.predeformation.cofibered s₁ w₀ z₁₂₀ q₁
  have hmap₂₃ : H.map t₂₃ (classOf 𝓕 h𝓕.predeformation.cofibered w₀) =
      classOf 𝓕 h𝓕.predeformation.cofibered z₂₃₀ :=
    map_classOf 𝓕 h𝓕.predeformation.cofibered t₂₃ w₀ z₂₃₀ q₂₃
  have hmap₁₃ : H.map t₁₃ (classOf 𝓕 h𝓕.predeformation.cofibered w₀) =
      classOf 𝓕 h𝓕.predeformation.cofibered z₁₃₀ :=
    map_classOf 𝓕 h𝓕.predeformation.cofibered t₁₃ w₀ z₁₃₀ q₁₃
  let j := squareZeroPair V V (s₁ ≫ g.g) (t₂₃ ≫ g.g)
  let π₁ : FGModuleCat.of k (V × V) ⟶ V := FGModuleCat.ofHom (LinearMap.fst k V V)
  let π₂ : FGModuleCat.of k (V × V) ⟶ V := FGModuleCat.ofHom (LinearMap.snd k V V)
  have hj₁ : j ≫ S.map π₁ = s₁ ≫ g.g := squareZeroPair_fst V V _ _
  have hj₂ : j ≫ S.map π₂ = t₂₃ ≫ g.g := squareZeroPair_snd V V _ _
  have hj₃ : j ≫ S.map (π₁ + π₂) = t₁₃ ≫ g.g := by
    apply squareZeroPair_add
    intro r
    apply Subtype.ext
    change p₂.hom (t₁₃.hom r) - p₁.hom (t₁₃.hom r) =
      (p₂.hom (s₁.hom r) - p₁.hom (s₁.hom r)) +
        (p₂.hom (t₂₃.hom r) - p₁.hom (t₂₃.hom r))
    have ev {B : ArtinianLocalAlgCat.{u, w, w} Λ k}
        {a b : ArtinianLocalAlgCat.pullbackObj_of_surjective (p₁ ≫ f) f (.inr hf) ⟶ B}
        (h : a = b) : a.hom r = b.hom r := congrArg (fun a => a.hom r) h
    have h₁ := ev (hP.lift_fst (s₁ ≫ p₁) s₂ hb₁₃)
    have h₂ := ev (hP.lift_snd (s₁ ≫ p₁) s₂ hb₁₃)
    have h₃ := ev (hP.lift_fst (s₁ ≫ p₂) s₂ hb₂₃)
    have h₄ := ev (hP.lift_snd (s₁ ≫ p₂) s₂ hb₂₃)
    dsimp only [ArtinianLocalAlgCat.comp_hom, AlgHom.comp_apply] at h₁ h₂ h₃ h₄
    change p₁.hom (t₁₃.hom r) = p₁.hom (s₁.hom r) at h₁
    change p₂.hom (t₁₃.hom r) = s₂.hom r at h₂
    change p₁.hom (t₂₃.hom r) = p₂.hom (s₁.hom r) at h₃
    change p₂.hom (t₂₃.hom r) = s₂.hom r at h₄
    rw [h₁, h₂, h₃, h₄]
    abel
  have hcomp {B D C : ArtinianLocalAlgCat.{u, w, w} Λ k}
      (u : B ⟶ D) (v : D ⟶ C) (z : H.obj B) : H.map v (H.map u z) = H.map (u ≫ v) z :=
    (ConcreteCategory.congr_hom (H.map_comp u v) z).symm
  let cw := classOf 𝓕 h𝓕.predeformation.cofibered w₀
  have hpush : ∀ (π : FGModuleCat.of k (V × V) ⟶ V)
      (t : ArtinianLocalAlgCat.pullbackObj_of_surjective (p₁ ≫ f) f (.inr hf) ⟶
        ArtinianLocalAlgCat.pullbackObj_of_surjective f f (.inl hf))
      (z₀ : 𝓕.p.Fiber (ArtinianLocalAlgCat.pullbackObj_of_surjective f f (.inl hf))),
      j ≫ S.map π = t ≫ g.g →
      H.map t cw = classOf 𝓕 h𝓕.predeformation.cofibered z₀ →
      H.map (S.map π) (H.map j cw) =
        H.map g.g (classOf 𝓕 h𝓕.predeformation.cofibered z₀) := by
    intro π t z₀ ht hz
    have e₁ : H.map (S.map π) (H.map j cw) = H.map (j ≫ S.map π) cw := hcomp j (S.map π) cw
    have e₂ : H.map (j ≫ S.map π) cw = H.map (t ≫ g.g) cw :=
      congrArg (fun m : ArtinianLocalAlgCat.pullbackObj_of_surjective (p₁ ≫ f) f (.inr hf) ⟶
        S.obj V => H.map m cw) ht
    have e₃ : H.map (t ≫ g.g) cw = H.map g.g (H.map t cw) := (hcomp t g.g cw).symm
    have e₄ : H.map g.g (H.map t cw) =
        H.map g.g (classOf 𝓕 h𝓕.predeformation.cofibered z₀) :=
      congrArg (fun y : H.obj (ArtinianLocalAlgCat.pullbackObj_of_surjective f f (.inl hf)) =>
        H.map g.g y) hz
    exact e₁.trans (e₂.trans (e₃.trans e₄))
  have hs₁ := hpush π₁ s₁ z₁₂₀ hj₁ hmap₁₂
  have hs₂ := hpush π₂ t₂₃ z₂₃₀ hj₂ hmap₂₃
  have hs₃ := hpush (π₁ + π₂) t₁₃ z₁₃₀ hj₃ hmap₁₃
  have hadd := tensorCoordinate_map_add 𝓕 h𝓕 hS2 (FGModuleCat.of k (V × V)) V π₁ π₂
    (H.map j cw)
  rw [hs₁, hs₂, hs₃] at hadd
  rw [hd₁₂, hd₂₃, hd₁₃]
  exact hadd.symm

end

end Deformation
