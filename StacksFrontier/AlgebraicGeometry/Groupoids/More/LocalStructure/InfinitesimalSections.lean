module

public import Mathlib.RingTheory.Ideal.Cotangent
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Groupoids.More.LocalStructure.LocalAlgebra

/-!
# Sections infinitesimally close to the unit, in the local model of a groupoid

Let `B` be an algebra over a commutative ring `A` carrying a retraction `B → A`, so that
`A → B → A` is the identity.  This is the first-order datum of a groupoid at an identity: `A` is
the local ring of the objects, `B` the local ring of the arrows at the identity, `A → B` the map
induced by the source and `B → A` the map induced by the unit, and `I = ker (B → A)` is the ideal
of the unit.

Fix moreover a square-zero ideal `K` of `A`; it is the conormal module of a first order
thickening `U₀ ⊆ U` of the objects.  An *infinitesimal section* is an `A`-algebra map
`δ : B → A` which agrees with the retraction modulo `K`: a section of the source which coincides
with the unit on `U₀`.  Such a `δ` carries `I` into `K`, kills `I²` because `K² = 0`, and is
determined by the induced `A`-linear map `I/I² → K` because `B = A ⊕ I`.  Conversely every
`A`-linear map `I/I² → K` arises this way, the multiplicativity of the resulting `δ` coming from
`K² = 0` again.  So the two are in bijection, which is the content of this file.

This is the local form, at a geometric point, of the bijection
`Hom_{𝒪_{U₀}}(e₀^*Ω_{R₀/U₀}, 𝒞_{U₀/U}) → Γ₀` of [Stacks Project, Tag 0CKE].  Here `I/I²` is the
first-order datum of the arrows at the identity, the stalk of the conormal module of the unit
section, and `K` is the stalk of `𝒞_{U₀/U}`, the ideal of `U₀` in `U` being square zero; the
group `Γ₀` of sections infinitesimally close to the unit is cut out on local rings by the two
conditions above.  It is the form in which [Stacks Project, Tag 0CKF] uses the bijection when
proving that it is a group isomorphism: there a section is read on stalks as a ring map
`δ : B → A` with `δ ∘ s = id` carrying `I` into `K`, and the corresponding derivation is
`δ - e`, determined by its restriction to `I`.

## Main definitions

* `Stacks.Groupoids.augmentationIdeal`: the ideal `I = ker (B → A)` of the unit.
* `Stacks.Groupoids.augmentationProj`: the projection of `B` onto `I` along the unit section.
* `Stacks.Groupoids.InfinitesimalSection`: an `A`-algebra map `B → A` agreeing with the
  retraction modulo `K`.
* `Stacks.Groupoids.cotangentHomOfSection`: the `A`-linear map `I/I² → K` induced by an
  infinitesimal section.
* `Stacks.Groupoids.cotangentDerivation`: the `K`-valued derivation `B → A` attached to an
  `A`-linear map `I/I² → K`.
* `Stacks.Groupoids.sectionOfCotangentHom`: the infinitesimal section `θ · e` attached to an
  `A`-linear map `θ : I/I² → K`.

## Main results

* `Stacks.Groupoids.infinitesimalSectionEquiv`: the bijection from `A`-linear maps `I/I² → K`
  to infinitesimal sections, the local form of the displayed bijection of
  [Stacks Project, Tag 0CKE].  The bijection of that equation itself, for a groupoid in
  algebraic spaces and a first order thickening, is
  `AlgebraicGeometry.GroupoidInAlgebraicSpaces.InfinitesimalSectionDifference.unitVAddEquiv`.
* `Stacks.Groupoids.toCotangent_augmentationProj_mul`: the Leibniz rule for the projection onto
  `I`, read in `I/I²`.
* `Stacks.Groupoids.isScalarTower_of_retraction`: the hypothesis `IsScalarTower A B A` used
  throughout says exactly that `B → A` retracts `A → B`.
* `Stacks.Groupoids.LocalGroupoidAlgebra.identityIdeal_eq_augmentationIdeal`: the ideal of the
  identity of a local groupoid algebra is the ideal of the unit above.

## Implementation notes

The retraction is carried by the pair of instances `[Algebra A B] [Algebra B A]` together with
`[IsScalarTower A B A]`, which by `isScalarTower_of_retraction` and
`algebraMap_algebraMap_self` is exactly the identity `(B → A) ∘ (A → B) = id`.  Keeping the two
maps as `algebraMap`s is what makes `I/I²` an `A`-module and `K` a `B`-module, so that the
`A`-linear maps `I/I² → K` of the source can be written with no transport; a formulation with
bare ring homomorphisms cannot name those module structures, since an instance may not depend on
a section variable.  `Stacks.Groupoids.LocalGroupoidAlgebra` of
[Stacks Project, Tag 0CK4] packages the same maps as `RingHom`s, and
`LocalGroupoidAlgebra.identityIdeal_eq_augmentationIdeal` identifies the two ideals of the unit.

An infinitesimal section is an `A`-algebra map rather than a ring map together with the equation
`δ ∘ s = id`: those are the same datum, `A`-algebra maps `B → A` being by definition the ring
maps that retract `A → B`.

`A`-linearity of a map `I/I² → K` is the `𝒪_{U₀}`-linearity of the source: `K` is killed by `K`,
so an `A`-linear map to `K` is automatically `A/K`-linear, and `A/K` is the local ring of `U₀`.

## References

* [Stacks Project, Tag 0CKE](https://stacks.math.columbia.edu/tag/0CKE)
* [Stacks Project, Tag 0CKB](https://stacks.math.columbia.edu/tag/0CKB)
* [Stacks Project, Tag 0CKF](https://stacks.math.columbia.edu/tag/0CKF)
* [Stacks Project, Tag 0CK4](https://stacks.math.columbia.edu/tag/0CK4)
* [Stacks Project, Tag 0CK9](https://stacks.math.columbia.edu/tag/0CK9)
-/

@[expose] public section

universe u v w

namespace Stacks.Groupoids

section Retraction

variable (A : Type u) {B : Type v} [CommRing A] [CommRing B] [Algebra A B] [Algebra B A]

/-- The ideal of the unit: the kernel of the retraction `B → A`.  For the local model of a
groupoid at an identity this is the ideal `I = ker(e : B → A)` of the identity. -/
@[sga "3 II 4.11.4", sga "3 VIIB 2.1", sga "3 VIIB 2.6"]
abbrev augmentationIdeal : Ideal B := RingHom.ker (algebraMap B A)

variable [IsScalarTower A B A]

/-- The retraction `B → A` undoes the structure map `A → B`.  This is the content of the
hypothesis `IsScalarTower A B A`. -/
theorem algebraMap_algebraMap_self (a : A) : algebraMap B A (algebraMap A B a) = a := by
  simpa using (IsScalarTower.algebraMap_apply A B A a).symm

/-- `IsScalarTower A B A` holds as soon as the structure map `B → A` retracts `A → B`; together
with `algebraMap_algebraMap_self` this shows the hypothesis is exactly that retraction
identity. -/
theorem isScalarTower_of_retraction {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    [Algebra A B] [Algebra B A] (h : ∀ a : A, algebraMap B A (algebraMap A B a) = a) :
    IsScalarTower A B A :=
  ⟨fun a b x => by
    simp only [Algebra.smul_def, map_mul, h, Algebra.algebraMap_self_apply]
    rw [mul_assoc]⟩

/-- Every element of `B` differs from the image of its retraction by an element of the ideal of
the unit: this is the decomposition `B = A ⊕ I`. -/
theorem sub_mem_augmentationIdeal (b : B) :
    b - algebraMap A B (algebraMap B A b) ∈ (augmentationIdeal A : Ideal B) := by
  change algebraMap B A (b - algebraMap A B (algebraMap B A b)) = 0
  rw [map_sub, algebraMap_algebraMap_self, sub_self]

/-- The projection of `B` onto the ideal of the unit along the unit section, that is, the
`I`-component of the decomposition `B = A ⊕ I`. -/
@[sga "3 VIIB 5.0" "partial"]
def augmentationProj (b : B) : ↥(augmentationIdeal A : Ideal B) :=
  ⟨b - algebraMap A B (algebraMap B A b), sub_mem_augmentationIdeal A b⟩

/-- The value of the projection onto the ideal of the unit. -/
@[simp] theorem augmentationProj_coe (b : B) :
    (augmentationProj A b : B) = b - algebraMap A B (algebraMap B A b) := rfl

/-- The projection onto the ideal of the unit is additive, hence kills `0`. -/
@[simp] theorem augmentationProj_zero : augmentationProj A (0 : B) = 0 := by
  apply Subtype.ext
  simp

/-- The unit of `B` lies in the image of `A`, so its projection vanishes. -/
@[simp] theorem augmentationProj_one : augmentationProj A (1 : B) = 0 := by
  apply Subtype.ext
  simp

/-- The projection onto the ideal of the unit kills the image of `A`. -/
@[simp] theorem augmentationProj_algebraMap (a : A) :
    augmentationProj A (algebraMap A B a) = 0 := by
  apply Subtype.ext
  simp [algebraMap_algebraMap_self]

/-- The projection onto the ideal of the unit is additive. -/
@[simp] theorem augmentationProj_add (b b' : B) :
    augmentationProj A (b + b') = augmentationProj A b + augmentationProj A b' := by
  apply Subtype.ext
  simp [sub_add_sub_comm]

/-- On the ideal of the unit the projection is the identity. -/
theorem augmentationProj_of_mem {x : B} (hx : x ∈ (augmentationIdeal A : Ideal B)) :
    augmentationProj A x = ⟨x, hx⟩ := by
  apply Subtype.ext
  change x - algebraMap A B (algebraMap B A x) = x
  rw [show algebraMap B A x = 0 from hx, map_zero, sub_zero]

/-- Scalar multiplication on `I/I²` factors through the retraction: the ideal of the unit acts
by zero, so an element of `B` acts through its image in `A`. -/
theorem smul_cotangent (b : B) (m : (augmentationIdeal A : Ideal B).Cotangent) :
    b • m = algebraMap B A b • m := by
  calc b • m = (algebraMap A B (algebraMap B A b) + (augmentationProj A b : B)) • m := by simp
    _ = algebraMap B A b • m := by
        rw [add_smul, Ideal.Cotangent.smul_eq_zero_of_mem (augmentationProj A b).2, add_zero,
          IsScalarTower.algebraMap_smul]

/-- The Leibniz rule for the projection onto the ideal of the unit, read in `I/I²`: the
projection of a product is the sum of the projections of the factors, each scaled by the
retraction of the other. -/
theorem toCotangent_augmentationProj_mul (b b' : B) :
    (augmentationIdeal A : Ideal B).toCotangent (augmentationProj A (b * b')) =
      algebraMap B A b • (augmentationIdeal A : Ideal B).toCotangent (augmentationProj A b') +
        algebraMap B A b' •
          (augmentationIdeal A : Ideal B).toCotangent (augmentationProj A b) := by
  have key : augmentationProj A (b * b') =
      b • augmentationProj A b' + b' • augmentationProj A b +
        (-(augmentationProj A b * augmentationProj A b')) := by
    apply Subtype.ext
    push_cast
    simp only [augmentationProj_coe, map_mul]
    ring
  have hz : (augmentationIdeal A : Ideal B).toCotangent
      (augmentationProj A b * augmentationProj A b') = 0 := by
    rw [Ideal.toCotangent_eq_zero, pow_two]
    exact Ideal.mul_mem_mul (augmentationProj A b).2 (augmentationProj A b').2
  rw [key, map_add, map_add, map_neg, hz, neg_zero, add_zero, map_smul, map_smul,
    smul_cotangent, smul_cotangent]

end Retraction

section Definition

variable (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B] [Algebra B A]
  (K : Ideal A)

/-- A section of the source infinitesimally close to the unit: an `A`-algebra map `B → A` which
agrees with the retraction modulo `K`.  In the local model of a groupoid at an identity these are
the elements of the group `Γ₀` of [Stacks Project, Tag 0CKB]. -/
abbrev InfinitesimalSection := {δ : B →ₐ[A] A // ∀ b, δ b - algebraMap B A b ∈ K}

end Definition

section Bijection

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B] [Algebra B A]
  [IsScalarTower A B A] {K : Ideal A}

/-- Two elements of a square-zero ideal multiply to zero. -/
theorem mul_eq_zero_of_sq_eq_bot (hK : K ^ 2 = ⊥) {x y : A} (hx : x ∈ K) (hy : y ∈ K) :
    x * y = 0 := by
  have h : x * y ∈ K ^ 2 := pow_two K ▸ Ideal.mul_mem_mul hx hy
  simpa [hK] using h

omit [IsScalarTower A B A] in
/-- An infinitesimal section carries the ideal of the unit into `K`, the retraction vanishing
there. -/
theorem InfinitesimalSection.map_mem (δ : InfinitesimalSection A B K) {x : B}
    (hx : x ∈ (augmentationIdeal A : Ideal B)) : δ.1 x ∈ K := by
  have h := δ.2 x
  rwa [show algebraMap B A x = 0 from hx, sub_zero] at h

/-- The restriction of an infinitesimal section to the ideal of the unit, as a `B`-linear map
into `K`.  It is `B`-linear and not merely `A`-linear because the difference between `δ` and the
retraction already lands in `K`, which annihilates the values of `δ` on the ideal. -/
def restrictToAugmentation (hK : K ^ 2 = ⊥) (δ : InfinitesimalSection A B K) :
    ↥(augmentationIdeal A : Ideal B) →ₗ[B] ↥K where
  toFun x := ⟨δ.1 x, δ.map_mem x.2⟩
  map_add' x y := Subtype.ext (map_add δ.1 _ _)
  map_smul' b x := by
    apply Subtype.ext
    simp only [RingHom.id_apply, SetLike.val_smul, Submodule.coe_smul_of_tower, Algebra.smul_def,
      Algebra.algebraMap_self_apply]
    have h2 : (δ.1 b - algebraMap B A b) * δ.1 (x : B) = 0 :=
      mul_eq_zero_of_sq_eq_bot hK (δ.2 b) (δ.map_mem x.2)
    rw [sub_mul, sub_eq_zero] at h2
    rw [map_mul, h2]

omit [IsScalarTower A B A] in
/-- The restriction of an infinitesimal section to the ideal of the unit kills `I²`, so it
factors through `I/I²`. -/
theorem restrictToAugmentation_ker_le (hK : K ^ 2 = ⊥) (δ : InfinitesimalSection A B K) :
    ((augmentationIdeal A : Ideal B) • ⊤ : Submodule B ↥(augmentationIdeal A : Ideal B)) ≤
      LinearMap.ker (restrictToAugmentation hK δ) := by
  refine Submodule.smul_le.mpr fun b hb x _ ↦ LinearMap.mem_ker.mpr (Subtype.ext ?_)
  change δ.1 (b * (x : B)) = 0
  rw [map_mul]
  exact mul_eq_zero_of_sq_eq_bot hK (δ.map_mem hb) (δ.map_mem x.2)

/-- The `A`-linear map `I/I² → K` induced by an infinitesimal section: on the class of `x` in the
ideal of the unit it is the value `δ x`. -/
noncomputable def cotangentHomOfSection (hK : K ^ 2 = ⊥) (δ : InfinitesimalSection A B K) :
    (augmentationIdeal A : Ideal B).Cotangent →ₗ[A] ↥K :=
  LinearMap.restrictScalars A
    (show (augmentationIdeal A : Ideal B).Cotangent →ₗ[B] ↥K from
      Submodule.liftQ _ (restrictToAugmentation hK δ) (restrictToAugmentation_ker_le hK δ))

/-- The map `I/I² → K` induced by an infinitesimal section is `δ` itself on the classes of
elements of the ideal of the unit. -/
@[simp] theorem cotangentHomOfSection_toCotangent (hK : K ^ 2 = ⊥)
    (δ : InfinitesimalSection A B K) (x : ↥(augmentationIdeal A : Ideal B)) :
    (cotangentHomOfSection hK δ ((augmentationIdeal A : Ideal B).toCotangent x) : A) =
      δ.1 (x : B) := by
  rfl

/-- The `K`-valued derivation `B → A` attached to an `A`-linear map `θ : I/I² → K`: the value at
`b` is `θ` applied to the class of the `I`-component of `b`. -/
def cotangentDerivation (θ : (augmentationIdeal A : Ideal B).Cotangent →ₗ[A] ↥K) (b : B) : A :=
  (θ ((augmentationIdeal A : Ideal B).toCotangent (augmentationProj A b)) : A)

/-- The derivation attached to `θ` takes values in `K`. -/
theorem cotangentDerivation_mem (θ : (augmentationIdeal A : Ideal B).Cotangent →ₗ[A] ↥K) (b : B) :
    cotangentDerivation θ b ∈ K :=
  (θ _).2

/-- The derivation attached to `θ` vanishes at `1`. -/
@[simp] theorem cotangentDerivation_one
    (θ : (augmentationIdeal A : Ideal B).Cotangent →ₗ[A] ↥K) :
    cotangentDerivation θ (1 : B) = 0 := by
  simp [cotangentDerivation]

/-- The derivation attached to `θ` vanishes on the image of `A`. -/
@[simp] theorem cotangentDerivation_algebraMap
    (θ : (augmentationIdeal A : Ideal B).Cotangent →ₗ[A] ↥K) (a : A) :
    cotangentDerivation θ (algebraMap A B a) = 0 := by
  simp [cotangentDerivation]

/-- The derivation attached to `θ` is additive. -/
@[simp] theorem cotangentDerivation_add
    (θ : (augmentationIdeal A : Ideal B).Cotangent →ₗ[A] ↥K) (b b' : B) :
    cotangentDerivation θ (b + b') = cotangentDerivation θ b + cotangentDerivation θ b' := by
  simp [cotangentDerivation]

/-- The Leibniz rule for the derivation attached to `θ`. -/
theorem cotangentDerivation_mul (θ : (augmentationIdeal A : Ideal B).Cotangent →ₗ[A] ↥K)
    (b b' : B) : cotangentDerivation θ (b * b') =
      algebraMap B A b * cotangentDerivation θ b' + algebraMap B A b' * cotangentDerivation θ b :=
  by
  simp only [cotangentDerivation, toCotangent_augmentationProj_mul, map_add]
  rw [← IsScalarTower.algebraMap_smul B (algebraMap B A b),
    ← IsScalarTower.algebraMap_smul B (algebraMap B A b')]
  simp [Algebra.smul_def]

/-- The infinitesimal section `θ · e` attached to an `A`-linear map `θ : I/I² → K`: the
retraction corrected by the derivation of `θ`.  This is the map of the displayed bijection of
[Stacks Project, Tag 0CKE], in the local model at a geometric point. -/
def sectionOfCotangentHom (hK : K ^ 2 = ⊥)
    (θ : (augmentationIdeal A : Ideal B).Cotangent →ₗ[A] ↥K) : InfinitesimalSection A B K :=
  ⟨{ toFun := fun b => algebraMap B A b + cotangentDerivation θ b
     map_one' := by simp
     map_zero' := by simp [cotangentDerivation]
     map_add' := fun b b' => by
       simp only [map_add, cotangentDerivation_add]
       ring
     map_mul' := fun b b' => by
       have hz : cotangentDerivation θ b * cotangentDerivation θ b' = 0 :=
         mul_eq_zero_of_sq_eq_bot hK (cotangentDerivation_mem θ b) (cotangentDerivation_mem θ b')
       simp only [map_mul, cotangentDerivation_mul]
       rw [add_mul, mul_add, mul_add, hz]
       ring
     commutes' := fun a => by
       simp [algebraMap_algebraMap_self] },
   fun b => by simpa using cotangentDerivation_mem θ b⟩

/-- The infinitesimal section attached to `θ` is the retraction plus the derivation of `θ`. -/
@[simp] theorem sectionOfCotangentHom_apply (hK : K ^ 2 = ⊥)
    (θ : (augmentationIdeal A : Ideal B).Cotangent →ₗ[A] ↥K) (b : B) :
    (sectionOfCotangentHom hK θ).1 b = algebraMap B A b + cotangentDerivation θ b := rfl

/-- **Stacks 0CKE in the local model.**  Let `A → B → A` be a retraction of commutative rings,
`I = ker (B → A)` the ideal of the unit, and `K` a square-zero ideal of `A`.  Then the map
`θ ↦ θ · e` is a bijection from the `A`-linear maps `I/I² → K` to the sections of the source
infinitesimally close to the unit.

With `A = 𝒪_{U, ū}` and `B = 𝒪_{R, e(ū)}` the local rings of a groupoid in algebraic spaces at a
geometric point, `I/I²` the stalk of the conormal module of the unit section and `K` the stalk
of the conormal module `𝒞_{U₀/U}` of a first order thickening, this is the local form of the
displayed bijection `Hom_{𝒪_{U₀}}(e₀^*Ω_{R₀/U₀}, 𝒞_{U₀/U}) → Γ₀` of
[Stacks Project, Tag 0CKE]. -/
noncomputable def infinitesimalSectionEquiv (hK : K ^ 2 = ⊥) :
    ((augmentationIdeal A : Ideal B).Cotangent →ₗ[A] ↥K) ≃ InfinitesimalSection A B K where
  toFun := sectionOfCotangentHom hK
  invFun := cotangentHomOfSection hK
  left_inv θ := by
    refine LinearMap.ext fun m => ?_
    obtain ⟨x, rfl⟩ := (augmentationIdeal A : Ideal B).toCotangent_surjective m
    apply Subtype.ext
    rw [cotangentHomOfSection_toCotangent, sectionOfCotangentHom_apply,
      show algebraMap B A (x : B) = 0 from x.2, zero_add, cotangentDerivation,
      augmentationProj_of_mem A x.2]
  right_inv δ := by
    apply Subtype.ext
    refine AlgHom.ext fun b => ?_
    rw [sectionOfCotangentHom_apply, cotangentDerivation, cotangentHomOfSection_toCotangent,
      augmentationProj_coe, map_sub, δ.1.commutes, Algebra.algebraMap_self_apply]
    ring

end Bijection

namespace LocalGroupoidAlgebra

variable {A : Type u} {B : Type v} {C : Type w} [CommRing A] [CommRing B] [CommRing C]
  [Algebra B A] (G : LocalGroupoidAlgebra A B C)

/-- The ideal of the identity of a local groupoid algebra is the ideal of the unit of the
retraction it carries. -/
theorem identityIdeal_eq_augmentationIdeal (h : (algebraMap B A : B →+* A) = G.identity) :
    G.identityIdeal = (augmentationIdeal A : Ideal B) :=
  congrArg RingHom.ker h.symm

end LocalGroupoidAlgebra

end Stacks.Groupoids

end
