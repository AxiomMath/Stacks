module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Deformation.LiftsOfObjects.Action.DifferenceEquiv
public import StacksFrontier.Deformation.LiftsOfObjects.Action.PairTorsor

/-!
# The free transitive action of tangent vectors on lifts

Let `𝓕` be a deformation category over `𝒞_Λ`, let `f : A' → A` be a surjection of Artinian
local algebras whose kernel `I` is annihilated by the maximal ideal of `A'`, and let `x` be an
object of the fibre of `𝓕` over `A`. Then `T𝓕 ⊗_k I` acts on the set of isomorphism classes
of lifts of `x` along `f`, freely and transitively whenever that set is nonempty.

The action is not merely asserted to exist: it is pinned down by the infinitesimal difference
of its two lifts, and that difference is in turn pinned down as the canonical tangent
coordinate of the pushforward, along `(a₁, a₂) ↦ (ā₁, a₂ - a₁)`, of the fibre product of two
representative lifting arrows.

## Main definitions

* `Deformation.liftAction`: the additive action.
* `Deformation.liftDifference`: the infinitesimal difference of two classes of lifts.
* `Deformation.IsPushforwardDifference`: the specification of that difference by a cocartesian
  pushforward.

## Main results

* `Deformation.liftDifference_isPushforward`: the difference meets that specification.
* `Deformation.liftAction_difference`: the difference of a class from its translate is the
  translating vector, which fixes the action.
* `Deformation.liftAction_bijective`: from any fixed class, translation is a bijection onto
  all classes; equivalently the action is free and transitive.

## Implementation notes

The whole content is in `Deformation.tangentPairEquiv`, which replaces the second member of a
pair of lifts by the difference and records that the resulting bijection fixes the first
coordinate, vanishes on the diagonal and satisfies the cocycle identity. The action and its
pointwise bijectivity are then the formal consequences
`Deformation.addActionOfPairEquiv` and `Deformation.addActionOfPairEquiv_pointwiseBijective`.

Pointwise bijectivity, rather than a `AddTorsor` instance, is what is stated: it expresses
freeness and transitivity together without choosing a base lift, and it is vacuously available
when there is no lift at all.

## References

* [Stacks Project, Tag 06JI](https://stacks.math.columbia.edu/tag/06JI)
-/

@[expose] public section

namespace Deformation

section
open CategoryTheory CategoryTheory.Limits IsLocalRing
universe u w uF vF

/-- **Stacks Project, Tag 06JI.** The canonical additive action of tangent vectors tensored
with the infinitesimal kernel on the classes of lifts. -/
@[stacks 06JI "action", instance_reducible]
public noncomputable def liftAction
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    (𝓕 : BasedCategory.{vF, uF} (ArtinianLocalAlgCat.{u, w, w} Λ k))
    (h𝓕 : IsDeformationCategory 𝓕.p)
    {A' A : ArtinianLocalAlgCat.{u, w, w} Λ k}
    (f : A' ⟶ A) (hf : Function.Surjective f.hom)
    (hann : ∀ a : A', a ∈ maximalIdeal A' →
      ∀ i : RingHom.ker f.hom.toRingHom, a * (i : A') = 0)
    (x : 𝓕.p.Fiber A) :
    letI : Module k (RingHom.ker f.hom.toRingHom) := kernelModule f hann
    let hS2 := schlessingerConditionS2_of_isIsomorphismClasses
      𝓕 h𝓕.predeformation.cofibered
      (schlessingerConditionS2_of_satisfiesRS h𝓕.satisfiesRS)
      (.inl h𝓕.predeformation)
    letI : Fact (IsPredeformationCategory 𝓕.p) := ⟨h𝓕.predeformation⟩
    letI : Fact (SchlessingerConditionS2
      (Functor.Elements.π (isomorphismClasses 𝓕 h𝓕.predeformation.cofibered))) := ⟨hS2⟩
    AddAction
      (TensorProduct k
        (artinianTangentSpace Λ k
          (isomorphismClasses 𝓕 h𝓕.predeformation.cofibered))
        (RingHom.ker f.hom.toRingHom))
      (LiftClasses 𝓕.p f x) := by
  intro hS2
  letI : Module k (RingHom.ker f.hom.toRingHom) := kernelModule f hann
  letI : Module.Finite k (RingHom.ker f.hom.toRingHom) := kernelModule_finite f hann
  letI : Fact (IsPredeformationCategory 𝓕.p) := ⟨h𝓕.predeformation⟩
  letI : Fact (SchlessingerConditionS2
    (Functor.Elements.π (isomorphismClasses 𝓕 h𝓕.predeformation.cofibered))) := ⟨hS2⟩
  let E := tangentPairEquiv 𝓕 h𝓕 f hf hann x
  exact addActionOfPairEquiv E.1 E.2.1 E.2.2.1 E.2.2.2.1

/-- The tangent vector obtained by pushing the pair of lifts forward along
`Deformation.infinitesimalDifferenceMap`, then applying the tangent-space identification.
This is the source's map `g_*` on isomorphism classes. -/
public noncomputable def liftDifference
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    (𝓕 : BasedCategory.{vF, uF} (ArtinianLocalAlgCat.{u, w, w} Λ k))
    (h𝓕 : IsDeformationCategory 𝓕.p)
    {A' A : ArtinianLocalAlgCat.{u, w, w} Λ k}
    (f : A' ⟶ A) (hf : Function.Surjective f.hom)
    (hann : ∀ a : A', a ∈ maximalIdeal A' →
      ∀ i : RingHom.ker f.hom.toRingHom, a * (i : A') = 0)
    (x : 𝓕.p.Fiber A) :
    letI : Module k (RingHom.ker f.hom.toRingHom) := kernelModule f hann
    let hS2 := schlessingerConditionS2_of_isIsomorphismClasses
      𝓕 h𝓕.predeformation.cofibered
      (schlessingerConditionS2_of_satisfiesRS h𝓕.satisfiesRS)
      (.inl h𝓕.predeformation)
    letI : Fact (IsPredeformationCategory 𝓕.p) := ⟨h𝓕.predeformation⟩
    letI : Fact (SchlessingerConditionS2
      (Functor.Elements.π (isomorphismClasses 𝓕 h𝓕.predeformation.cofibered))) := ⟨hS2⟩
    LiftClasses 𝓕.p f x → LiftClasses 𝓕.p f x →
      TensorProduct k
        (artinianTangentSpace Λ k
          (isomorphismClasses 𝓕 h𝓕.predeformation.cofibered))
        (RingHom.ker f.hom.toRingHom) := by
  letI : Module k (RingHom.ker f.hom.toRingHom) := kernelModule f hann
  letI : Module.Finite k (RingHom.ker f.hom.toRingHom) := kernelModule_finite f hann
  exact fun a b => tensorCoordinate 𝓕 h𝓕 (FGModuleCat.of k (RingHom.ker f.hom.toRingHom))
    (differenceClass 𝓕 h𝓕 f hf hann x a b)

/-- A witness that a tangent vector is the image, under the canonical tangent equivalence, of
the pushforward along the infinitesimal difference map of the fibre product of two
representative lifts. -/
public def IsPushforwardDifference
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    (𝓕 : BasedCategory.{vF, uF} (ArtinianLocalAlgCat.{u, w, w} Λ k))
    (h𝓕 : IsDeformationCategory 𝓕.p)
    {A' A : ArtinianLocalAlgCat.{u, w, w} Λ k}
    (f : A' ⟶ A) (hf : Function.Surjective f.hom)
    (hann : ∀ a : A', a ∈ maximalIdeal A' →
      ∀ i : RingHom.ker f.hom.toRingHom, a * (i : A') = 0)
    (x : 𝓕.p.Fiber A) (a b : LiftClasses 𝓕.p f x)
    (t : letI : Module k (RingHom.ker f.hom.toRingHom) := kernelModule f hann
      letI : Fact (IsPredeformationCategory 𝓕.p) := ⟨h𝓕.predeformation⟩
      let hS2 := schlessingerConditionS2_of_isIsomorphismClasses
        𝓕 h𝓕.predeformation.cofibered
        (schlessingerConditionS2_of_satisfiesRS h𝓕.satisfiesRS)
        (.inl h𝓕.predeformation)
      letI : Fact (SchlessingerConditionS2
        (Functor.Elements.π (isomorphismClasses 𝓕 h𝓕.predeformation.cofibered))) := ⟨hS2⟩
      TensorProduct k
        (artinianTangentSpace Λ k
          (isomorphismClasses 𝓕 h𝓕.predeformation.cofibered))
        (RingHom.ker f.hom.toRingHom)) : Prop :=
  letI : Module k (RingHom.ker f.hom.toRingHom) := kernelModule f hann
  let hS2 := schlessingerConditionS2_of_isIsomorphismClasses
    𝓕 h𝓕.predeformation.cofibered
    (schlessingerConditionS2_of_satisfiesRS h𝓕.satisfiesRS)
    (.inl h𝓕.predeformation)
  letI : Fact (IsPredeformationCategory 𝓕.p) := ⟨h𝓕.predeformation⟩
  letI : Fact (SchlessingerConditionS2
    (Functor.Elements.π (isomorphismClasses 𝓕 h𝓕.predeformation.cofibered))) := ⟨hS2⟩
  let p₁ := ArtinianLocalAlgCat.pullbackFst_of_surjective f f (.inl hf)
  let p₂ := ArtinianLocalAlgCat.pullbackSnd_of_surjective f f (.inl hf)
  let g := infinitesimalDifferenceMap f hf hann
  ∃ (hfin : Module.Finite k (RingHom.ker f.hom.toRingHom)),
    letI : Module.Finite k (RingHom.ker f.hom.toRingHom) := hfin
    let V := FGModuleCat.of k (RingHom.ker f.hom.toRingHom)
    ∃ (htarget : g.target = (squareZeroExtensionArtinian Λ k).obj V)
      (a₀ b₀ : Lift 𝓕.p f x) (z : Lift 𝓕.p (p₁ ≫ f) x)
      (r₁ : z.obj ⟶ a₀.obj) (r₂ : z.obj ⟶ b₀.obj)
      (y : 𝓕.p.Fiber g.target) (q : z.obj ⟶ y.1),
      ThinSkeleton.mk a₀ = a ∧ ThinSkeleton.mk b₀ = b ∧
      𝓕.p.IsHomLift p₁ r₁ ∧ 𝓕.p.IsHomLift p₂ r₂ ∧
      r₁ ≫ a₀.hom = z.hom ∧ r₂ ≫ b₀.hom = z.hom ∧
      IsPullback r₁ r₂ a₀.hom b₀.hom ∧
      𝓕.p.IsHomLift g.g q ∧ 𝓕.p.IsCocartesian (𝓕.p.map q) q ∧
      t = (associatedTangentSpaceFunctor_iso_tensorLeftUnlifted
        𝓕 h𝓕.predeformation hS2 V).symm
          (tangentLiftCoord 𝓕 h𝓕 hS2 V
            ((isomorphismClasses 𝓕 h𝓕.predeformation.cofibered).map (eqToHom htarget)
              (classOf 𝓕 h𝓕.predeformation.cofibered y)))

/-- **Stacks Project, Tag 06JI.** The infinitesimal difference of any two lifts is exactly the
canonical tangent coordinate of the cocartesian pushforward of their fibre product along
`(a₁, a₂) ↦ (ā₁, a₂ - a₁)`. -/
@[stacks 06JI "difference is canonical pushforward"]
public theorem liftDifference_isPushforward
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    (𝓕 : BasedCategory.{vF, uF} (ArtinianLocalAlgCat.{u, w, w} Λ k))
    (h𝓕 : IsDeformationCategory 𝓕.p)
    {A' A : ArtinianLocalAlgCat.{u, w, w} Λ k}
    (f : A' ⟶ A) (hf : Function.Surjective f.hom)
    (hann : ∀ a : A', a ∈ maximalIdeal A' →
      ∀ i : RingHom.ker f.hom.toRingHom, a * (i : A') = 0)
    (x : 𝓕.p.Fiber A) :
    letI : Module k (RingHom.ker f.hom.toRingHom) := kernelModule f hann
    let hS2 := schlessingerConditionS2_of_isIsomorphismClasses
      𝓕 h𝓕.predeformation.cofibered
      (schlessingerConditionS2_of_satisfiesRS h𝓕.satisfiesRS)
      (.inl h𝓕.predeformation)
    letI : Fact (IsPredeformationCategory 𝓕.p) := ⟨h𝓕.predeformation⟩
    letI : Fact (SchlessingerConditionS2
      (Functor.Elements.π (isomorphismClasses 𝓕 h𝓕.predeformation.cofibered))) := ⟨hS2⟩
    ∀ a b : LiftClasses 𝓕.p f x,
      IsPushforwardDifference 𝓕 h𝓕 f hf hann x a b
        (liftDifference 𝓕 h𝓕 f hf hann x a b) := by
  classical
  intro hS2
  let : Module k (RingHom.ker f.hom.toRingHom) := kernelModule f hann
  let : Module.Finite k (RingHom.ker f.hom.toRingHom) := kernelModule_finite f hann
  let : Fact (IsPredeformationCategory 𝓕.p) := ⟨h𝓕.predeformation⟩
  let : Fact (SchlessingerConditionS2
    (Functor.Elements.π (isomorphismClasses 𝓕 h𝓕.predeformation.cofibered))) := ⟨hS2⟩
  intro a b
  obtain ⟨a₀, rfl⟩ : ∃ a' : Lift 𝓕.p f x, ThinSkeleton.mk a' = a := Quotient.exists_rep a
  obtain ⟨b₀, rfl⟩ : ∃ b' : Lift 𝓕.p f x, ThinSkeleton.mk b' = b := Quotient.exists_rep b
  obtain ⟨z, ⟨r₁, r₂, hw, hr₁, hr₂, h₁, h₂, hlim⟩, hz⟩ :=
    differenceClass_representatives 𝓕 h𝓕 f hf hann x a₀ b₀
  let g := infinitesimalDifferenceMap f hf hann
  let V := FGModuleCat.of k (RingHom.ker f.hom.toRingHom)
  have : 𝓕.p.IsHomLift
      (ArtinianLocalAlgCat.pullbackFst_of_surjective f f (.inl hf) ≫ f) z.hom := z.isHomLift
  obtain ⟨y, q, hy, hq⟩ := exists_pushforward_codomain h𝓕.predeformation.cofibered
    (CategoryTheory.IsHomLift.domain_eq 𝓕.p
      (ArtinianLocalAlgCat.pullbackFst_of_surjective f f (.inl hf) ≫ f) z.hom) g.g
  let := hq
  let y₀ : 𝓕.p.Fiber g.target := ⟨y, hy⟩
  have hdc : differenceClass 𝓕 h𝓕 f hf hann x (ThinSkeleton.mk a₀) (ThinSkeleton.mk b₀) =
      (isomorphismClasses 𝓕 h𝓕.predeformation.cofibered).map g.g
        (classOf 𝓕 h𝓕.predeformation.cofibered
          ((liftForgetFunctor 𝓕.p _ x).obj z)) := hz
  have hcl : differenceClass 𝓕 h𝓕 f hf hann x (ThinSkeleton.mk a₀) (ThinSkeleton.mk b₀) =
      classOf 𝓕 h𝓕.predeformation.cofibered y₀ :=
    hdc.trans (map_classOf 𝓕 h𝓕.predeformation.cofibered g.g
      ((liftForgetFunctor 𝓕.p _ x).obj z) y₀ q)
  have hid : (isomorphismClasses 𝓕 h𝓕.predeformation.cofibered).map
        (eqToHom (rfl : g.target = (squareZeroExtensionArtinian Λ k).obj V))
        (classOf 𝓕 h𝓕.predeformation.cofibered y₀) =
      classOf 𝓕 h𝓕.predeformation.cofibered y₀ := by
    rw [eqToHom_refl]
    exact ConcreteCategory.congr_hom
      ((isomorphismClasses 𝓕 h𝓕.predeformation.cofibered).map_id _) _
  refine ⟨kernelModule_finite f hann, rfl, a₀, b₀, z, r₁, r₂, y₀, q,
    rfl, rfl, hr₁, hr₂, h₁, h₂, ⟨⟨hw⟩, hlim⟩, hq, ?_, ?_⟩
  · let := isStronglyCocartesian_of_isCofiberedInGroupoids h𝓕.predeformation.cofibered
      (𝓕.p.map q) q (CategoryTheory.IsHomLift.map 𝓕.p q)
    infer_instance
  · apply (associatedTangentSpaceFunctor_iso_tensorLeftUnlifted
      𝓕 h𝓕.predeformation hS2 V).injective
    rw [LinearEquiv.apply_symm_apply]
    refine (iso_tensorCoordinate 𝓕 h𝓕 hS2 V
      (differenceClass 𝓕 h𝓕 f hf hann x (ThinSkeleton.mk a₀) (ThinSkeleton.mk b₀))).trans ?_
    exact congrArg (fun y => tangentLiftCoord 𝓕 h𝓕 hS2 V y) (hcl.trans hid.symm)

/-- **Stacks Project, Tag 06JI.** The action is the unique lift whose infinitesimal difference
from the given lift is the prescribed tangent vector. -/
@[stacks 06JI "difference characterization"]
public theorem liftAction_difference
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    (𝓕 : BasedCategory.{vF, uF} (ArtinianLocalAlgCat.{u, w, w} Λ k))
    (h𝓕 : IsDeformationCategory 𝓕.p)
    {A' A : ArtinianLocalAlgCat.{u, w, w} Λ k}
    (f : A' ⟶ A) (hf : Function.Surjective f.hom)
    (hann : ∀ a : A', a ∈ maximalIdeal A' →
      ∀ i : RingHom.ker f.hom.toRingHom, a * (i : A') = 0)
    (x : 𝓕.p.Fiber A) :
    letI : Module k (RingHom.ker f.hom.toRingHom) := kernelModule f hann
    let hS2 := schlessingerConditionS2_of_isIsomorphismClasses
      𝓕 h𝓕.predeformation.cofibered
      (schlessingerConditionS2_of_satisfiesRS h𝓕.satisfiesRS)
      (.inl h𝓕.predeformation)
    letI : Fact (IsPredeformationCategory 𝓕.p) := ⟨h𝓕.predeformation⟩
    letI : Fact (SchlessingerConditionS2
      (Functor.Elements.π (isomorphismClasses 𝓕 h𝓕.predeformation.cofibered))) := ⟨hS2⟩
    letI := liftAction 𝓕 h𝓕 f hf hann x
    ∀ (a : LiftClasses 𝓕.p f x)
      (t : TensorProduct k
        (artinianTangentSpace Λ k
          (isomorphismClasses 𝓕 h𝓕.predeformation.cofibered))
        (RingHom.ker f.hom.toRingHom)),
      liftDifference 𝓕 h𝓕 f hf hann x a (t +ᵥ a) = t := by
  intro hS2 a t
  let : Module k (RingHom.ker f.hom.toRingHom) := kernelModule f hann
  let : Module.Finite k (RingHom.ker f.hom.toRingHom) := kernelModule_finite f hann
  let : Fact (IsPredeformationCategory 𝓕.p) := ⟨h𝓕.predeformation⟩
  let : Fact (SchlessingerConditionS2
    (Functor.Elements.π (isomorphismClasses 𝓕 h𝓕.predeformation.cofibered))) := ⟨hS2⟩
  let E := tangentPairEquiv 𝓕 h𝓕 f hf hann x
  change tensorCoordinate 𝓕 h𝓕 _ (differenceClass 𝓕 h𝓕 f hf hann x a
    (E.1.symm (a, t)).2) = t
  exact (E.2.2.2.2 a (E.1.symm (a, t)).2).symm.trans
    (pairEquiv_inverse_difference E.1 E.2.1 a t)

/-- **Stacks Project, Tag 06JI.** From any fixed lift, addition of tangent vectors is a
bijection onto all isomorphism classes of lifts; equivalently, the action is free and
transitive. -/
@[stacks 06JI "free and transitive"]
public theorem liftAction_bijective
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    (𝓕 : BasedCategory.{vF, uF} (ArtinianLocalAlgCat.{u, w, w} Λ k))
    (h𝓕 : IsDeformationCategory 𝓕.p)
    {A' A : ArtinianLocalAlgCat.{u, w, w} Λ k}
    (f : A' ⟶ A) (hf : Function.Surjective f.hom)
    (hann : ∀ a : A', a ∈ maximalIdeal A' →
      ∀ i : RingHom.ker f.hom.toRingHom, a * (i : A') = 0)
    (x : 𝓕.p.Fiber A) :
    letI : Module k (RingHom.ker f.hom.toRingHom) := kernelModule f hann
    let hS2 := schlessingerConditionS2_of_isIsomorphismClasses
      𝓕 h𝓕.predeformation.cofibered
      (schlessingerConditionS2_of_satisfiesRS h𝓕.satisfiesRS)
      (.inl h𝓕.predeformation)
    letI : Fact (IsPredeformationCategory 𝓕.p) := ⟨h𝓕.predeformation⟩
    letI : Fact (SchlessingerConditionS2
      (Functor.Elements.π (isomorphismClasses 𝓕 h𝓕.predeformation.cofibered))) := ⟨hS2⟩
    letI := liftAction 𝓕 h𝓕 f hf hann x
    ∀ a : LiftClasses 𝓕.p f x,
      Function.Bijective
        (fun t : TensorProduct k
          (artinianTangentSpace Λ k
            (isomorphismClasses 𝓕 h𝓕.predeformation.cofibered))
          (RingHom.ker f.hom.toRingHom) => t +ᵥ a) := by
  intro hS2 a
  let : Module k (RingHom.ker f.hom.toRingHom) := kernelModule f hann
  let : Module.Finite k (RingHom.ker f.hom.toRingHom) := kernelModule_finite f hann
  let : Fact (IsPredeformationCategory 𝓕.p) := ⟨h𝓕.predeformation⟩
  let : Fact (SchlessingerConditionS2
    (Functor.Elements.π (isomorphismClasses 𝓕 h𝓕.predeformation.cofibered))) := ⟨hS2⟩
  let E := tangentPairEquiv 𝓕 h𝓕 f hf hann x
  exact addActionOfPairEquiv_pointwiseBijective E.1 E.2.1 a

end

end Deformation
