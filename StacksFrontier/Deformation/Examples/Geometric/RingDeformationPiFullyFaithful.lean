module

public import Mathlib.RingTheory.Idempotents
public import Mathlib.RingTheory.Localization.Away.Basic
public import StacksFrontier.Deformation.Examples.Geometric.RingDeformationPi

/-!
# The comparison functor into the deformations of a product ring is fully faithful

The comparison functor `∏ 𝓓_{R i} ⟶ 𝓓_{∏ R i}` of
`Deformation.Examples.piDeformationFunctor` is fully faithful. The reason is that a product ring
remembers its factors: the idempotents `e i = Pi.single i 1` cut `∏ R i` into the `R i`, and any
morphism of deformations of `∏ R i` must fix each `e i`. Indeed the difference between the image
of `e i` and `e i` lies in the kernel of the reduction to the special fibre, hence is nilpotent,
while it is also a difference of two idempotents; and two idempotents whose difference is
nilpotent are equal. A ring homomorphism between product rings which fixes every `e i` is a
product of homomorphisms of the factors, so a morphism of the product deformation splits
as a product of morphisms of the factors — which is fullness; and that splitting is determined
by the morphism, which is faithfulness.

This is the identification that lets a statement about the deformation category of a product ring
be read off at the product of the deformation categories of the factors. The source of
**Stacks 0DZF** passes between the two without comment, when it transports the chain of
comparisons along the decompositions `P^∧ = ∏ P^∧_{𝔪 i}` and `P^h = ∏ P^h_{𝔪 i}`.

## Main results

* `Deformation.Examples.piDeformationFunctor_full` and
  `Deformation.Examples.piDeformationFunctor_faithful`: the comparison functor
  `∏ 𝓓_{R i} ⟶ 𝓓_{∏ R i}` is full, respectively faithful.
* `Deformation.Examples.isIdempotentElem_pi_single_one`,
  `Deformation.Examples.isLocalization_pi_eval`: the idempotent `Pi.single i 1` of a product of
  rings, and the recognition of the `i`-th projection as the localization away from it.
* `Deformation.Examples.exists_piRingHom_of_map_single_one`: a ring homomorphism of product rings
  fixing each `Pi.single i 1` is a product of ring homomorphisms.
* `Deformation.Examples.isPushout_pi_eval` and `Deformation.Examples.isPushout_pi_component`: the
  square cut out of a product of rings by the `i`-th projection is a pushout square, and
  consequently a pushout square of products of rings restricts to one in each factor.

## Implementation notes

Fullness is proved by producing the preimage explicitly, in
`Deformation.Examples.exists_piDeformation_preimage`: the components of the splitting are
assembled into morphisms of flat algebras whose pushout condition is obtained from the pushout
condition of the given morphism by pasting on the localization square
`Deformation.Examples.isPushout_pi_eval`.

## References

* [Stacks Project, Tag 0DZF](https://stacks.math.columbia.edu/tag/0DZF)
* [Stacks Project, Tag 0DY1](https://stacks.math.columbia.edu/tag/0DY1)
-/

@[expose] public section

open CategoryTheory

universe u w uι

namespace Deformation.Examples

/-! ### The idempotents cutting a product ring into its factors -/

/-- **The element `Pi.single i 1` of a finite product of rings is idempotent.** -/
public theorem isIdempotentElem_pi_single_one
    {ι : Type uι} [DecidableEq ι] (R : ι → Type w) [∀ i, CommRing (R i)] (i : ι) :
    IsIdempotentElem (Pi.single i (1 : R i)) := by
  change Pi.single i (1 : R i) * Pi.single i (1 : R i) = _
  rw [← Pi.single_mul, one_mul]

/-- **The `i`-th projection of a product of rings is the localization away from the idempotent
`Pi.single i 1`.** -/
public theorem isLocalization_pi_eval
    {ι : Type uι} [DecidableEq ι] (R : ι → Type w) [∀ i, CommRing (R i)] (i : ι) :
    letI : Algebra (∀ j, R j) (R i) := (Pi.evalRingHom R i).toAlgebra
    IsLocalization.Away (Pi.single i (1 : R i)) (R i) := by
  let : Algebra (∀ j, R j) (R i) := (Pi.evalRingHom R i).toAlgebra
  refine IsLocalization.away_of_isIdempotentElem_of_mul (isIdempotentElem_pi_single_one R i)
    (fun x y => ?_) fun x => ⟨Pi.single i x, Pi.single_eq_same i x⟩
  change x i = y i ↔ _
  rw [← Pi.single_mul_left, ← Pi.single_mul_left, one_mul, one_mul]
  exact ⟨congrArg (Pi.single i), fun h => by simpa using congrFun h i⟩

/-- **A ring homomorphism between products of rings which fixes every idempotent
`Pi.single i 1` is a product of ring homomorphisms.** -/
public theorem exists_piRingHom_of_map_single_one
    {ι : Type uι} [DecidableEq ι] (R S : ι → Type w)
    [∀ i, CommRing (R i)] [∀ i, CommRing (S i)]
    (f : (∀ i, R i) →+* (∀ i, S i))
    (hf : ∀ i, f (Pi.single i 1) = Pi.single i 1) :
    ∃ g : ∀ i, R i →+* S i, ∀ x i, f x i = g i (x i) := by
  let g (i : ι) : R i →+* S i :=
    { toFun x := f (Pi.single i x) i
      map_one' := by simp [hf]
      map_mul' x y := by simp [Pi.single_mul, map_mul]
      map_zero' := by simp
      map_add' x y := by simp [Pi.single_add, map_add] }
  refine ⟨g, fun x i => ?_⟩
  change f x i = f (Pi.single i (x i)) i
  have h := congrFun (f.map_mul (Pi.single i 1) x) i
  rw [hf] at h
  simpa only [← Pi.single_mul_left, one_mul, Pi.mul_apply, Pi.single_eq_same] using h.symm

/-! ### The idempotents are fixed by every morphism of deformations -/

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]

/-- Every element of the kernel of the reduction of a deformation to its special fibre is
nilpotent: the kernel is contained in the ideal generated by the maximal ideal of the Artinian
base, and that ideal is nilpotent. -/
private theorem isNilpotent_of_mem_ker_specialFiberMap
    {R : Type w} [CommRing R] [Algebra k R]
    (X : ringDeformationCategory (Λ := Λ) (k := k) R)
    {x : X.left.fiber} (hx : x ∈ RingHom.ker X.hom.map.hom) : IsNilpotent x := by
  obtain ⟨n, hn⟩ :=
    (isArtinianRing_iff_isNilpotent_maximalIdeal X.left.base).mp inferInstance
  have hpow : (Ideal.map (algebraMap X.left.base X.left.fiber)
      (IsLocalRing.maximalIdeal X.left.base)) ^ n = 0 := by
    rw [← Ideal.map_pow, hn]
    simp
  exact ⟨n, Ideal.pow_eq_zero_of_mem hpow le_rfl
    (deformationSpecialFiber_ker_le_map_maximalIdeal X hx)⟩

/-- **Two idempotents of the fibre of a deformation with the same image in the special fibre are
equal**: their difference lies in the kernel of the reduction, hence is nilpotent, and two
idempotents with nilpotent difference agree. -/
private theorem eq_of_isIdempotentElem_of_specialFiberMap_eq
    {R : Type w} [CommRing R] [Algebra k R]
    (X : ringDeformationCategory (Λ := Λ) (k := k) R)
    {e₁ e₂ : X.left.fiber} (he₁ : IsIdempotentElem e₁) (he₂ : IsIdempotentElem e₂)
    (h : X.hom.map.hom e₁ = X.hom.map.hom e₂) : e₁ = e₂ := by
  refine eq_of_isNilpotent_sub_of_isIdempotentElem he₁ he₂
    (isNilpotent_of_mem_ker_specialFiberMap X (RingHom.mem_ker.mpr ?_))
  rw [map_sub, h, sub_self]

/-- A morphism of product deformations fixes each of the idempotents `Pi.single i 1`: the
difference of the image and the idempotent reduces to zero on the special fibre, hence is
nilpotent, and two idempotents whose difference is nilpotent are equal. -/
private theorem piDeformationHom_map_single_one
    {ι : Type w} [Finite ι] [DecidableEq ι]
    (R : ι → Type w) [∀ i, CommRing (R i)] [∀ i, Algebra k (R i)]
    {X Y : (piBasedCategory fun i => ringDeformationBasedCategory Λ k (R i)).obj}
    (f : (piDeformationFunctor R).obj X ⟶ (piDeformationFunctor R).obj Y) (i : ι) :
    f.left.map.hom (Pi.single (M := fun j => (X.x j).left.fiber) i 1) =
      Pi.single (M := fun j => (Y.x j).left.fiber) i 1 := by
  apply eq_of_isIdempotentElem_of_specialFiberMap_eq ((piDeformationFunctor R).obj Y)
    ((isIdempotentElem_pi_single_one (fun j => (X.x j).left.fiber) i).map f.left.map.hom)
    (isIdempotentElem_pi_single_one (fun j => (Y.x j).left.fiber) i)
  refine (deformationMorphism_map_comm f _).trans ?_
  funext j
  change (X.x j).hom.map.hom (Pi.single (M := fun j => (X.x j).left.fiber) i 1 j) =
    (Y.x j).hom.map.hom (Pi.single (M := fun j => (Y.x j).left.fiber) i 1 j)
  by_cases h : j = i
  · subst j
    simp
  · simp [Pi.single_eq_of_ne h]

/-! ### Restricting a pushout square of products of rings to a factor -/

/-- **The square cut out of a morphism of product rings by the `i`-th projections is a pushout
square**, because the projections are localizations away from corresponding idempotents. -/
public theorem isPushout_pi_eval
    {ι : Type w} (R S : ι → Type w)
    [∀ i, CommRing (R i)] [∀ i, CommRing (S i)] (g : ∀ i, R i →+* S i) (i : ι) :
    IsPushout (CommRingCat.ofHom (Pi.evalRingHom R i))
      (CommRingCat.ofHom (RingHom.pi fun j => (g j).comp (Pi.evalRingHom R j)))
      (CommRingCat.ofHom (g i)) (CommRingCat.ofHom (Pi.evalRingHom S i)) := by
  classical
  let f := RingHom.pi fun j => (g j).comp (Pi.evalRingHom R j)
  let : Algebra (∀ j, R j) (R i) := (Pi.evalRingHom R i).toAlgebra
  let : Algebra (∀ j, S j) (S i) := (Pi.evalRingHom S i).toAlgebra
  let := isLocalization_pi_eval R i
  have hf : f (Pi.single i 1) = Pi.single i 1 := by
    ext j
    by_cases h : j = i
    · subst j
      simp [f]
    · simp [f, Pi.single_eq_of_ne h]
  let : IsLocalization ((Submonoid.powers (Pi.single i (1 : R i))).map f) (S i) := by
    rw [Submonoid.map_powers, hf]
    exact isLocalization_pi_eval S i
  exact (CommRingCat.isPushout_of_isLocalization f (g i) (by ext x; rfl)
    (Submonoid.powers (Pi.single i (1 : R i)))).flip

/-- **A pushout square whose vertical sides are products of maps restricts to a pushout square in
each factor**, by pasting on the localization square of `isPushout_pi_eval`. -/
public theorem isPushout_pi_component
    {ι : Type w} {A B : Type w} [CommRing A] [CommRing B]
    {R S : ι → Type w} [∀ i, CommRing (R i)] [∀ i, CommRing (S i)]
    (f : A →+* B) (p : ∀ i, A →+* R i) (q : ∀ i, B →+* S i)
    (g : ∀ i, R i →+* S i)
    (h : IsPushout (CommRingCat.ofHom (RingHom.pi p)) (CommRingCat.ofHom f)
      (CommRingCat.ofHom (RingHom.pi fun i => (g i).comp (Pi.evalRingHom R i)))
      (CommRingCat.ofHom (RingHom.pi q))) (i : ι) :
    IsPushout (CommRingCat.ofHom (p i)) (CommRingCat.ofHom f)
      (CommRingCat.ofHom (g i)) (CommRingCat.ofHom (q i)) :=
  h.paste_horiz (isPushout_pi_eval R S g i)

/-! ### Full faithfulness -/

/-- Every morphism of product deformations is the product of a family of morphisms of the
factors. -/
private theorem exists_piDeformation_preimage
    {ι : Type w} [Finite ι]
    (R : ι → Type w) [∀ i, CommRing (R i)] [∀ i, Algebra k (R i)]
    {X Y : (piBasedCategory fun i => ringDeformationBasedCategory Λ k (R i)).obj}
    (f : (piDeformationFunctor R).obj X ⟶ (piDeformationFunctor R).obj Y) :
    ∃ g : X ⟶ Y, (piDeformationFunctor R).map g = f := by
  classical
  let q : (∀ i, (X.x i).left.fiber) →+* (∀ i, (Y.x i).left.fiber) := f.left.map.hom
  obtain ⟨g, hg⟩ := exists_piRingHom_of_map_single_one _ _ q
    (piDeformationHom_map_single_one R f)
  have hq : q = RingHom.pi fun i => (g i).comp (Pi.evalRingHom _ i) :=
    RingHom.ext fun x => funext (hg x)
  let p i : X.base →+* (X.x i).left.fiber :=
    @algebraMap X.base (X.x i).left.fiber _ _
      (flatAlgebraWithBase X.base (X.x i).left (X.hx i)).algebra
  let r i : Y.base →+* (Y.x i).left.fiber :=
    @algebraMap Y.base (Y.x i).left.fiber _ _
      (flatAlgebraWithBase Y.base (Y.x i).left (Y.hx i)).algebra
  have htotal : IsPushout (CommRingCat.ofHom (RingHom.pi p))
      (CommRingCat.ofHom f.left.base.hom.toRingHom)
      (CommRingCat.ofHom (RingHom.pi fun i => (g i).comp (Pi.evalRingHom _ i)))
      (CommRingCat.ofHom (RingHom.pi r)) := by
    rw [← hq]
    exact f.left.cartesian
  have hi i : IsPushout (CommRingCat.ofHom (p i))
      (CommRingCat.ofHom f.left.base.hom.toRingHom) (CommRingCat.ofHom (g i))
      (CommRingCat.ofHom (r i)) :=
    isPushout_pi_component _ p r g htotal i
  let t i : (X.x i).left ⟶ (Y.x i).left :=
    { base := eqToHom (X.hx i) ≫ f.left.base ≫ eqToHom (Y.hx i).symm
      map := CommRingCat.ofHom (g i)
      cartesian :=
        isPushout_of_base_eq (X.hx i) (Y.hx i) f.left.base (CommRingCat.ofHom (g i)) (hi i) }
  have hspecial i : t i ≫ (Y.x i).hom = (X.x i).hom := by
    apply FlatAlgebraCategory.Hom.ext
    · exact deformationBaseMap_unique _ _
    · ext x
      have h := congrFun (deformationMorphism_map_comm f
        (Pi.single (M := fun j => (X.x j).left.fiber) i x)) i
      change (Y.x i).hom.map.hom (q (Pi.single (M := fun j => (X.x j).left.fiber) i x) i) =
        (X.x i).hom.map.hom (Pi.single (M := fun j => (X.x j).left.fiber) i x i) at h
      change (Y.x i).hom.map.hom (g i x) = (X.x i).hom.map.hom x
      simpa only [hg, Pi.single_eq_same] using h
  refine ⟨⟨f.left.base, fun i => Over.homMk (t i) (hspecial i), fun i =>
    IsHomLift.of_fac' _ _ _ (X.hx i) (Y.hx i) rfl⟩, ?_⟩
  apply Over.OverMorphism.ext
  apply FlatAlgebraCategory.Hom.ext
  · rfl
  · apply CommRingCat.hom_ext
    apply RingHom.ext
    intro x
    funext i
    exact (hg x i).symm

/-- **The comparison functor from the product of the deformation categories of a finite family of
algebras to the deformation category of the product algebra is full.** A morphism of deformations
of `∏ R i` fixes the idempotents `Pi.single i 1`, hence is the product of its components. -/
public theorem piDeformationFunctor_full
    {ι : Type w} [Finite ι]
    (R : ι → Type w) [∀ i, CommRing (R i)] [∀ i, Algebra k (R i)] :
    (piDeformationFunctor (Λ := Λ) (k := k) R).toFunctor.Full :=
  ⟨fun f => exists_piDeformation_preimage R f⟩

/-- **The comparison functor from the product of the deformation categories of a finite family of
algebras to the deformation category of the product algebra is faithful.** Each component of a
morphism of the product is recovered from the product morphism by evaluating it on the elements
`Pi.single i x`. -/
public theorem piDeformationFunctor_faithful
    {ι : Type w} [Finite ι]
    (R : ι → Type w) [∀ i, CommRing (R i)] [∀ i, Algebra k (R i)] :
    (piDeformationFunctor (Λ := Λ) (k := k) R).toFunctor.Faithful := by
  classical
  constructor
  intro X Y f g h
  have hb : f.hbase = g.hbase := congrArg (fun t => t.left.base) h
  apply PiOver.Hom.ext' hb
  intro i
  apply Over.OverMorphism.ext
  apply FlatAlgebraCategory.Hom.ext
  · let p := (ringDeformationBasedCategory Λ k (R i)).p
    change p.map (f.component i) = p.map (g.component i)
    have hmap (t : X ⟶ Y) : p.map (t.component i) =
        eqToHom (X.hx i) ≫ t.hbase ≫ eqToHom (Y.hx i).symm :=
      have := t.hcomponent i
      IsHomLift.fac' p t.hbase (t.component i)
    rw [hmap f, hmap g, hb]
  · ext x
    have he := congrArg
      (fun t => t.left.map.hom (Pi.single (M := fun j => (X.x j).left.fiber) i x) i) h
    change (f.component i).left.map.hom
        (Pi.single (M := fun j => (X.x j).left.fiber) i x i) =
      (g.component i).left.map.hom
        (Pi.single (M := fun j => (X.x j).left.fiber) i x i) at he
    simpa only [Pi.single_eq_same] using he

end Deformation.Examples
