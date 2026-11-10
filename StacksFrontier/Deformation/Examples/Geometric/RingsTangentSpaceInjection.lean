module

public import StacksFrontier.Algebra.Module.OppositeOfCommSemiring
public import StacksFrontier.Deformation.Examples.Geometric.RingsInfinitesimalAutomorphisms
public import StacksFrontier.Deformation.Examples.Geometric.RingsTangentSpaceLinear
public import StacksFrontier.Deformation.TangentSpace.FiniteDimensional

/-!
# The class of a deformation of an algebra over a square-zero base, naturally and injectively

Work in Stacks 0DY1 with `k` a field and `P` a `k`-algebra. A point of the deformation category
of `P` over the Artinian local algebra `k ⊕ V` of Stacks 06IB is a flat algebra `Q` over a base
`R`, together with a base-change square exhibiting `P` as `Q ⊗_R k`, whose base `R` *is*
`k ⊕ V` as an object of `𝒞_Λ`. By `Deformation.Examples.firstOrderExtension` such a point is a
square-zero extension of the `k`-algebra `P` by the `P`-module `P ⊗[k] V`, so **Stacks 0GPT**
attaches to it a class in `Ext¹_P(NL_{P/k}, P ⊗[k] V)`.

This file builds that class, shows it depends only on the isomorphism class of the point, proves
it natural in `V` against the receptacle `Deformation.Examples.naiveCotangentExtOneTensorFunctor`
and injective. Those are exactly the three data
`Deformation.finiteDimensional_artinianTangentSpace_of_natural_injection` asks for, so the
tangent space of the deformation category of `P` is finite-dimensional as soon as the receptacle
is finite-dimensional at the rank-one module, which is Stacks 0DY4(2). That application, and
Stacks 0ET4, are in `StacksFrontier/Deformation/Examples/Geometric/RingsHull.lean`.

Only the *forward* map of the tangent-space clause of Stacks 0DY3 is built here. The reverse
map — a flat `k ⊕ V`-algebra out of an arbitrary square-zero extension of `P` by `P ⊗[k] V`,
through Stacks 063Y — is what the full isomorphism `T𝓓_P ≅ Ext¹_P(NL_{P/k}, P)` needs, and it
is not needed for finite-dimensionality.

The base of a point of the fibre is only *equal* to `k ⊕ V` as an object of `𝒞_Λ`, never
identified with it by a chosen map, so the `k ⊕ V`-algebra structure on `Q` has to be
transported along a ring isomorphism `e : R ≃+* k ⊕ V` coming from that equality. The first
section does that transport abstractly, from a presentation `e` and its compatibility with the
two augmentations; the second deduces the naturality; the third, the injectivity; the last two
read a presentation off a point of the fibre and descend everything to isomorphism classes.

## Main definitions

* `Deformation.Examples.algebraOfBaseEquiv` and
  `Deformation.Examples.baseAlgebraOfBaseEquiv`: the `k ⊕ V`- and `k`-algebra structures
  transported to an algebra over a base presented as `k ⊕ V`.
* `Deformation.Examples.reductionOfBaseEquiv`: the structural map `Q → P` of the base-change
  square, as a `k`-algebra map for the transported structure.
* `Deformation.Examples.extClassOfBaseEquiv`: the class in `Ext¹_P(NL_{P/k}, P ⊗[k] V)` of a
  deformation of `P` whose base is presented as `k ⊕ V`.
* `Deformation.Examples.ringEquivOfEq`: an equality of objects of `𝒞_Λ`, read as a ring
  isomorphism of their carriers.
* `Deformation.Examples.fiberExtClass` and
  `Deformation.Examples.squareZeroFiberExtClass`: that class for a point of a fibre of the
  deformation category, for a given presentation of its base and for the canonical one.
* `Deformation.Examples.tangentExtClass`: the induced map on isomorphism classes, that is on
  the value at `V` of the set-valued functor `V ↦ 𝓕(k[V])` of Stacks 06IA.

## Main results

* `Deformation.Examples.flat_algebraOfBaseEquiv`,
  `Deformation.Examples.surjective_algebraMap_of_isPushout`,
  `Deformation.Examples.isFirstOrderReduction_reductionOfBaseEquiv` and
  `Deformation.Examples.mem_kerIdeal_smul_of_algebraMap_eq_zero`: the four hypotheses of
  `Deformation.Examples.firstOrderExtension`, deduced from the base-change square, the
  surjectivity of the augmentation `R → k` and the compatibility of the presentation with the
  two augmentations.
* `Deformation.Examples.extClassOfBaseEquiv_map` and
  `Deformation.Examples.fiberExtClass_map`: **Stacks 0GPV** in this setting — a morphism of
  deformations lying over the square-zero extension of a `k`-linear map `f : V → V'` carries
  the class of its source to the class of its target under
  `Ext¹_P(NL_{P/k}, P ⊗[k] V) → Ext¹_P(NL_{P/k}, P ⊗[k] V')`.
* `Deformation.Examples.squareZeroFiberExtClass_congr`: the class is invariant under
  isomorphism in a fibre. This is the case `f = id` of the previous item.
* `Deformation.Examples.exists_ringEquiv_of_extClassOfBaseEquiv_eq` and
  `Deformation.Examples.classOf_eq_of_squareZeroFiberExtClass_eq`: two deformations with the
  same class are isomorphic, by **Stacks 0GPT** followed by
  `Deformation.Examples.smul_of_compatible_algHom`.
* `Deformation.Examples.tangentExtClass_naturality` and
  `Deformation.Examples.tangentExtClass_injective`: the naturality and injectivity hypotheses
  of `Deformation.finiteDimensional_artinianTangentSpace_of_natural_injection`. Injectivity is
  proved at every `V`, not only at the rank-one module.

## Implementation notes

The transported algebra structures are taken as hypotheses in the first three sections, pinned
down by the compatibility `hQ` of the structural map with the presentation, rather than fixed to
`Deformation.Examples.algebraOfBaseEquiv`. This keeps the statements usable for the structures a
point of a fibre carries natively, and the two agree by
`Deformation.Examples.algebraMap_algebraOfBaseEquiv`.

Every claim about a point of a fibre is phrased through its own data — `fiberAug`, `fiberRed`
and the base-change square — so no element is ever chosen from an existence statement: the
instances a point carries are the `def`s `Deformation.Examples.fiberAugAlgebra`,
`Deformation.Examples.fiberRedAlgebra` and `Deformation.Examples.fiberBaseAlgebra`, introduced
by `letI` where they are needed.

The isomorphism-class quotient is handled by `Quotient.liftOn` through the carrier equality
`Deformation.isomorphismClasses_obj`, so `Deformation.Examples.tangentExtClass` is a genuine
function and not a choice of representative.

`CategoryTheory.BasedCategory.ofFunctor` is made locally `implicit_reducible`, as in
`StacksFrontier/Deformation/Formal/VersalObject/IsomorphismClasses.lean`: the category instance a
based category bundles and the ambient one are equal only up to unfolding that definition, and
instance search for `Functor.IsHomLift` has to see through it.

## References

* [Stacks Project, Tag 0DY1](https://stacks.math.columbia.edu/tag/0DY1)
* [Stacks Project, Tag 0DY3](https://stacks.math.columbia.edu/tag/0DY3)
* [Stacks Project, Tag 0GPT](https://stacks.math.columbia.edu/tag/0GPT)
* [Stacks Project, Tag 0GPV](https://stacks.math.columbia.edu/tag/0GPV)
* [Stacks Project, Tag 063Y](https://stacks.math.columbia.edu/tag/063Y)
-/
@[expose] public noncomputable section

open CategoryTheory TensorProduct TrivSqZeroExt Stacks.Deformation

universe u w

namespace Deformation.Examples

attribute [local instance] HasDerivedCategory.standard

attribute [local implicit_reducible] CategoryTheory.BasedCategory.ofFunctor

/-! ### Transporting a presentation of the base as a square-zero extension -/

section Transport

variable {k : Type w} [Field k] {V V' : Type w} [AddCommGroup V] [Module k V]
  [AddCommGroup V'] [Module k V']

local instance : Module kᵐᵒᵖ V :=
  Module.oppositeOfCommSemiring k V

local instance : IsCentralScalar k V := Module.isCentralScalar_oppositeOfCommSemiring k V

/-- The `k ⊕ V`-algebra structure on an algebra over a base presented as `k ⊕ V` by a ring
isomorphism: restriction of scalars along that isomorphism. -/
@[instance_reducible]
public def algebraOfBaseEquiv {R : Type w} [CommRing R] (Q : Type w) [CommRing Q]
    [Algebra R Q] (e : R ≃+* TrivSqZeroExt k V) : Algebra (TrivSqZeroExt k V) Q :=
  Algebra.compHom Q e.symm.toRingHom

/-- The `k`-algebra structure on an algebra over a base presented as `k ⊕ V`, through the
inclusion `k → k ⊕ V`. -/
@[instance_reducible]
public def baseAlgebraOfBaseEquiv {R : Type w} [CommRing R] (Q : Type w) [CommRing Q]
    [Algebra R Q] (e : R ≃+* TrivSqZeroExt k V) : Algebra k Q :=
  Algebra.compHom Q (e.symm.toRingHom.comp (algebraMap k (TrivSqZeroExt k V)))

/-- The two transported structures form a tower `k → k ⊕ V → Q`. -/
public theorem isScalarTower_baseAlgebraOfBaseEquiv {R : Type w} [CommRing R] (Q : Type w)
    [CommRing Q] [Algebra R Q] (e : R ≃+* TrivSqZeroExt k V) :
    letI := algebraOfBaseEquiv Q e
    letI := baseAlgebraOfBaseEquiv Q e
    IsScalarTower k (TrivSqZeroExt k V) Q :=
  letI := algebraOfBaseEquiv Q e
  letI := baseAlgebraOfBaseEquiv Q e
  IsScalarTower.of_algebraMap_eq fun _ ↦ rfl

/-- The transported structural map agrees with the original one through the presentation. -/
public theorem algebraMap_algebraOfBaseEquiv {R : Type w} [CommRing R] (Q : Type w)
    [CommRing Q] [Algebra R Q] (e : R ≃+* TrivSqZeroExt k V) (r : R) :
    letI := algebraOfBaseEquiv Q e
    algebraMap (TrivSqZeroExt k V) Q (e r) = algebraMap R Q r :=
  congrArg (algebraMap R Q) (e.symm_apply_apply r)

variable {P : Type w} [CommRing P] [Algebra k P] {R : Type w} [CommRing R]
  [Algebra R k] [Algebra R P] [IsScalarTower R k P]
  (Q : Type w) [CommRing Q] [Algebra R Q] [Algebra Q P] [IsScalarTower R Q P]
  [Algebra (TrivSqZeroExt k V) Q] [Algebra k Q] [IsScalarTower k (TrivSqZeroExt k V) Q]
  (e : R ≃+* TrivSqZeroExt k V)
  (hQ : ∀ r : R, algebraMap (TrivSqZeroExt k V) Q (e r) = algebraMap R Q r)
  (hρ : ∀ r : R, algebraMap R k r = (e r).fst)

/-- The `k ⊕ V`-algebra structure on the base of a deformation whose base is presented as
`k ⊕ V` by a ring isomorphism: restriction of scalars along that isomorphism. -/
@[instance_reducible]
public def selfAlgebraOfBaseEquiv {R : Type w} [CommRing R]
    (e : R ≃+* TrivSqZeroExt k V) : Algebra (TrivSqZeroExt k V) R :=
  Algebra.compHom R e.symm.toRingHom

/-- The base of a deformation presented as `k ⊕ V` is flat over `k ⊕ V`: the presentation is an
isomorphism, so the base is free of rank one. -/
public theorem flat_selfAlgebraOfBaseEquiv {R : Type w} [CommRing R]
    (e : R ≃+* TrivSqZeroExt k V) :
    letI := selfAlgebraOfBaseEquiv e
    Module.Flat (TrivSqZeroExt k V) R := by
  let := selfAlgebraOfBaseEquiv e
  refine Module.Flat.of_linearEquiv (M := TrivSqZeroExt k V) (N := R)
    { toFun := e
      map_add' := map_add e
      map_smul' := fun a r ↦ ?_
      invFun := e.symm
      left_inv := e.symm_apply_apply
      right_inv := e.apply_symm_apply }
  change e (e.symm a * r) = a * e r
  rw [map_mul, e.apply_symm_apply]

omit [Algebra R k] [Algebra k Q] [IsScalarTower k (TrivSqZeroExt k V) Q] in
include hQ in
/-- A presentation of the base as `k ⊕ V` compatible with the structural map of `Q` writes the
structural map of `Q` over `k ⊕ V` as that over `R`, read through the presentation. -/
public theorem algebraMap_eq_comp_symm :
    (algebraMap (TrivSqZeroExt k V) Q : TrivSqZeroExt k V →+* Q)
      = (algebraMap R Q).comp (e.symm : TrivSqZeroExt k V →+* R) :=
  RingHom.ext fun a ↦ by
    change algebraMap (TrivSqZeroExt k V) Q a = algebraMap R Q (e.symm a)
    rw [← hQ (e.symm a), e.apply_symm_apply]

omit [Algebra R k] [Algebra k Q] [IsScalarTower k (TrivSqZeroExt k V) Q] in
include hQ in
/-- A presentation of the base as `k ⊕ V` compatible with the structural maps makes `R` an
intermediate algebra of the tower `k ⊕ V → R → Q`. -/
public theorem isScalarTower_selfAlgebraOfBaseEquiv :
    letI := selfAlgebraOfBaseEquiv e
    IsScalarTower (TrivSqZeroExt k V) R Q := by
  let := selfAlgebraOfBaseEquiv e
  exact IsScalarTower.of_algebraMap_eq fun a ↦
    RingHom.congr_fun (algebraMap_eq_comp_symm Q e hQ) a

omit [Algebra R k] [Algebra k Q] [IsScalarTower k (TrivSqZeroExt k V) Q] in
include hQ in
/-- **A flat algebra over a base presented as `k ⊕ V` is flat over `k ⊕ V`.** This is the
flatness hypothesis of `Deformation.Examples.firstOrderExtension`. -/
public theorem flat_algebraOfBaseEquiv [Module.Flat R Q] :
    Module.Flat (TrivSqZeroExt k V) Q := by
  let := selfAlgebraOfBaseEquiv e
  let := isScalarTower_selfAlgebraOfBaseEquiv Q e hQ
  let := flat_selfAlgebraOfBaseEquiv (R := R) e
  exact Module.Flat.trans (TrivSqZeroExt k V) R Q

omit [Algebra R k] in
include hQ in
/-- The structural map of `Q` as a `k`-algebra factors through the base. -/
public theorem algebraMap_base_eq (c : k) :
    algebraMap k Q c = algebraMap R Q (e.symm (inl c)) := by
  rw [IsScalarTower.algebraMap_apply k (TrivSqZeroExt k V) Q, ← hQ (e.symm (inl c)),
    e.apply_symm_apply, algebraMap_eq_inl]

include hQ hρ in
/-- The reduction of a deformation whose base is presented as `k ⊕ V`, as a `k`-algebra map
`Q → P`: the underlying ring map is the structural map `Q → P` of the base-change square, and
`k`-linearity is the compatibility of the presentation with the two augmentations. -/
public def reductionOfBaseEquiv : Q →ₐ[k] P :=
  AlgHom.mk' (algebraMap Q P) fun c q ↦ by
    rw [Algebra.smul_def, Algebra.smul_def, map_mul]
    congr 1
    rw [algebraMap_base_eq Q e hQ, ← IsScalarTower.algebraMap_apply R Q P,
      IsScalarTower.algebraMap_apply R k P, hρ, e.apply_symm_apply, fst_inl]

@[simp]
public theorem reductionOfBaseEquiv_apply (q : Q) :
    reductionOfBaseEquiv Q e hQ hρ q = algebraMap Q P q := rfl

include hρ in
/-- The augmentation ideal of `k ⊕ V` corresponds to the augmentation ideal of the base under a
presentation compatible with the two augmentations. -/
public theorem map_symm_kerIdeal :
    (kerIdeal k V).map (e.symm : TrivSqZeroExt k V →+* R)
      = RingHom.ker (algebraMap R k) := by
  have h : RingHom.ker (algebraMap R k)
      = (kerIdeal k V).comap (e : R →+* TrivSqZeroExt k V) := by
    ext r
    simp only [RingHom.mem_ker, Ideal.mem_comap, kerIdeal]
    rw [hρ r]
    exact Iff.rfl
  rw [h]
  exact Ideal.map_symm e

include hQ hρ in
/-- **The reduction of a deformation over `k ⊕ V` is compatible with the augmentations.** This is
the hypothesis `IsFirstOrderReduction` of `Deformation.Examples.firstOrderExtension`. -/
public theorem isFirstOrderReduction_reductionOfBaseEquiv :
    IsFirstOrderReduction V (reductionOfBaseEquiv (P := P) Q e hQ hρ) := by
  intro a
  rw [reductionOfBaseEquiv_apply, RingHom.congr_fun (algebraMap_eq_comp_symm Q e hQ) a]
  change algebraMap Q P (algebraMap R Q (e.symm a)) = algebraMap k P a.fst
  rw [← IsScalarTower.algebraMap_apply R Q P, IsScalarTower.algebraMap_apply R k P, hρ,
    e.apply_symm_apply]

omit [Algebra k Q] in
/-- **The reduction of a deformation is surjective**, since `P` is the base change of `Q` along
the surjection `R → k`. -/
public theorem surjective_algebraMap_of_isPushout [Algebra.IsPushout R Q k P]
    (hsurj : Function.Surjective (algebraMap R k)) :
    Function.Surjective (algebraMap Q P) := by
  have h : ∀ q : Q, algebraMap Q P q = Algebra.IsPushout.equiv R Q k P
      (Algebra.TensorProduct.includeLeft (R := R) (S := R) (A := Q) (B := k) q) := by
    intro q
    change _ = Algebra.IsPushout.equiv R Q k P (q ⊗ₜ[R] (1 : k))
    rw [Algebra.IsPushout.equiv_tmul, map_one, mul_one]
  intro p
  obtain ⟨z, hz⟩ := (Algebra.IsPushout.equiv R Q k P).surjective p
  obtain ⟨q, rfl⟩ := Algebra.TensorProduct.includeLeft_surjective R Q hsurj z
  exact ⟨q, (h q).trans hz⟩

include hQ hρ in
/-- **The kernel of the reduction is the submodule generated by the augmentation ideal.** This
is the hypothesis `hker` of `Deformation.Examples.firstOrderExtension`: it comes from the
base-change square, which identifies the kernel of `Q → P` with the ideal generated by the
kernel of `R → k`. -/
public theorem mem_kerIdeal_smul_of_algebraMap_eq_zero [Algebra.IsPushout R Q k P]
    (hsurj : Function.Surjective (algebraMap R k)) (x : Q)
    (hx : reductionOfBaseEquiv (P := P) Q e hQ hρ x = 0) :
    x ∈ kerIdeal k V • (⊤ : Submodule (TrivSqZeroExt k V) Q) := by
  have hmem : x ∈ RingHom.ker (algebraMap Q P) := hx
  rw [ker_algebraMap_eq_map_ker_of_pushout R Q k P hsurj, ← map_symm_kerIdeal e hρ,
    Ideal.map_map, ← algebraMap_eq_comp_symm Q e hQ] at hmem
  have h : kerIdeal k V • (⊤ : Submodule (TrivSqZeroExt k V) Q)
      = Submodule.restrictScalars (TrivSqZeroExt k V)
          (Ideal.map (algebraMap (TrivSqZeroExt k V) Q) (kerIdeal k V)) :=
    Ideal.smul_top_eq_map (kerIdeal k V)
  rw [h]
  exact hmem

include hQ hρ in
/-- **The class of a deformation of `P` whose base is presented as `k ⊕ V`.** By
`Deformation.Examples.firstOrderExtension` such a deformation is a square-zero extension of the
`k`-algebra `P` by the `P`-module `P ⊗[k] V`, and this is its class in
`Ext¹_P(NL_{P/k}, P ⊗[k] V)` under **Stacks 0GPT**. -/
public def extClassOfBaseEquiv [Module.Flat R Q] [Algebra.IsPushout R Q k P]
    (hsurj : Function.Surjective (algebraMap R k)) :
    naiveCotangentExtOne k P (P ⊗[k] V) :=
  letI := flat_algebraOfBaseEquiv Q e hQ
  extClass (firstOrderExtension (V := V) (reductionOfBaseEquiv (P := P) Q e hQ hρ)
    (surjective_algebraMap_of_isPushout Q hsurj)
    (isFirstOrderReduction_reductionOfBaseEquiv Q e hQ hρ)
    (mem_kerIdeal_smul_of_algebraMap_eq_zero Q e hQ hρ hsurj))

end Transport

/-! ### Naturality of the class in the coefficient vector space -/

section TransportMap

variable {k : Type w} [Field k] {V V' : Type w} [AddCommGroup V] [Module k V]
  [AddCommGroup V'] [Module k V']

local instance : Module kᵐᵒᵖ V :=
  Module.oppositeOfCommSemiring k V

local instance : IsCentralScalar k V := Module.isCentralScalar_oppositeOfCommSemiring k V

variable {P : Type w} [CommRing P] [Algebra k P]
  {R : Type w} [CommRing R] [Algebra R k] [Algebra R P] [IsScalarTower R k P]
  {R'' : Type w} [CommRing R''] [Algebra R'' k] [Algebra R'' P] [IsScalarTower R'' k P]
  {Q : Type w} [CommRing Q] [Algebra R Q] [Algebra Q P] [IsScalarTower R Q P]
  [Algebra (TrivSqZeroExt k V) Q] [Algebra k Q] [IsScalarTower k (TrivSqZeroExt k V) Q]
  {Q'' : Type w} [CommRing Q''] [Algebra R'' Q''] [Algebra Q'' P] [IsScalarTower R'' Q'' P]
  [Algebra (TrivSqZeroExt k V') Q''] [Algebra k Q'']
  [IsScalarTower k (TrivSqZeroExt k V') Q'']
  (e : R ≃+* TrivSqZeroExt k V) (e'' : R'' ≃+* TrivSqZeroExt k V')
  (hQ : ∀ r : R, algebraMap (TrivSqZeroExt k V) Q (e r) = algebraMap R Q r)
  (hQ'' : ∀ r : R'', algebraMap (TrivSqZeroExt k V') Q'' (e'' r) = algebraMap R'' Q'' r)
  (hρ : ∀ r : R, algebraMap R k r = (e r).fst)
  (hρ'' : ∀ r : R'', algebraMap R'' k r = (e'' r).fst)

include hQ hρ hQ'' hρ'' in
/-- A ring map of deformations which lies over a ring map of the bases, and is compatible with
the reductions, induces the map on first Ext groups attached to the `k`-linear map of coefficient
vector spaces the base map realises. This is **Stacks 0GPV** for the trivial tower, in the form
`Deformation.Examples.extClass_firstOrderExtension` proves it, read through two presentations of
the bases as square-zero extensions. -/
public theorem extClassOfBaseEquiv_map [Module.Flat R Q] [Algebra.IsPushout R Q k P]
    [Module.Flat R'' Q''] [Algebra.IsPushout R'' Q'' k P]
    (hsurj : Function.Surjective (algebraMap R k))
    (hsurj'' : Function.Surjective (algebraMap R'' k))
    (b : R →+* R'') (g : Q →+* Q'')
    (hgbase : ∀ r : R, g (algebraMap R Q r) = algebraMap R'' Q'' (b r))
    (hgred : ∀ z : Q, algebraMap Q'' P (g z) = algebraMap Q P z)
    (f : V →ₗ[k] V') (hb : ∀ r : R, e'' (b r) = TrivSqZeroExt.map f (e r)) :
    extClassOfBaseEquiv Q'' e'' hQ'' hρ'' hsurj''
      = naiveCotangentExtOneMap k P (tensorRightMap P f)
        (extClassOfBaseEquiv Q e hQ hρ hsurj) := by
  let := flat_algebraOfBaseEquiv (R := R) Q e hQ
  let := flat_algebraOfBaseEquiv (R := R'') Q'' e'' hQ''
  have hgalg : ∀ a : TrivSqZeroExt k V,
      g (algebraMap (TrivSqZeroExt k V) Q a)
        = algebraMap (TrivSqZeroExt k V') Q'' (TrivSqZeroExt.map f a) := by
    intro a
    conv_lhs => rw [← e.apply_symm_apply a]
    rw [hQ, hgbase, ← hQ'' (b (e.symm a)), hb, e.apply_symm_apply]
  let h : Q →ₐ[k] Q'' := AlgHom.mk' g fun c q ↦ by
    rw [Algebra.smul_def, Algebra.smul_def, map_mul]
    congr 1
    rw [IsScalarTower.algebraMap_apply k (TrivSqZeroExt k V) Q, hgalg,
      (TrivSqZeroExt.map f).commutes c, IsScalarTower.algebraMap_apply k (TrivSqZeroExt k V') Q'']
  have hf : ∀ (v : V) (z : Q),
      g ((inr v : TrivSqZeroExt k V) • z) = (inr (f v) : TrivSqZeroExt k V') • g z := by
    intro v z
    have hv : TrivSqZeroExt.map f (inr v : TrivSqZeroExt k V) = (inr (f v) : TrivSqZeroExt k V') :=
      by simp [TrivSqZeroExt.map]
    rw [Algebra.smul_def, Algebra.smul_def, map_mul, hgalg, hv]
  exact extClass_firstOrderExtension (reductionOfBaseEquiv (P := P) Q e hQ hρ)
    (reductionOfBaseEquiv (P := P) Q'' e'' hQ'' hρ'')
    (surjective_algebraMap_of_isPushout Q hsurj)
    (surjective_algebraMap_of_isPushout Q'' hsurj'')
    (mem_kerIdeal_smul_of_algebraMap_eq_zero Q e hQ hρ hsurj)
    (mem_kerIdeal_smul_of_algebraMap_eq_zero Q'' e'' hQ'' hρ'' hsurj'')
    (isFirstOrderReduction_reductionOfBaseEquiv Q e hQ hρ)
    (isFirstOrderReduction_reductionOfBaseEquiv Q'' e'' hQ'' hρ'')
    h hgred f hf

end TransportMap

/-! ### The class of a point of a fibre of the deformation category -/

section Fiber

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
  {P : Type w} [CommRing P] [Algebra k P]
  {V V' : Type w} [AddCommGroup V] [Module k V] [AddCommGroup V'] [Module k V']

local instance : Module kᵐᵒᵖ V :=
  Module.oppositeOfCommSemiring k V

local instance : IsCentralScalar k V := Module.isCentralScalar_oppositeOfCommSemiring k V

/-- An equality of objects of `𝒞_Λ` read as a ring isomorphism of their carriers. The carrier,
its ring structure and its residue-field identification are all fields of the same structure, so
an equality of objects is the only comparison available between the carriers of two equal
objects. -/
public def ringEquivOfEq {A B : ArtinianLocalAlgCat.{u, w, w} Λ k} (h : A = B) :
    (A : Type w) ≃+* (B : Type w) := by
  subst h
  exact RingEquiv.refl _

/-- The isomorphism attached to a symmetric equality is the inverse one. -/
public theorem ringEquivOfEq_symm {A B : ArtinianLocalAlgCat.{u, w, w} Λ k} (h : A = B) :
    ringEquivOfEq h.symm = (ringEquivOfEq h).symm := by
  subst h
  rfl

/-- The isomorphisms attached to two equalities compose to the one attached to their
composite. -/
public theorem ringEquivOfEq_trans_apply {A B C : ArtinianLocalAlgCat.{u, w, w} Λ k}
    (h₁ : A = B) (h₂ : B = C) (a : A) :
    ringEquivOfEq h₂ (ringEquivOfEq h₁ a) = ringEquivOfEq (h₁.trans h₂) a := by
  subst h₁
  subst h₂
  rfl

/-- The transport morphism of an equality of objects acts as the induced ring isomorphism. -/
public theorem hom_eqToHom_apply {A B : ArtinianLocalAlgCat.{u, w, w} Λ k} (h : A = B)
    (a : A) : (eqToHom h).hom a = ringEquivOfEq h a := by
  subst h
  rfl

/-- The residue-field identifications of two equal objects agree through the induced ring
isomorphism. -/
public theorem residueEquiv_ringEquivOfEq {A B : ArtinianLocalAlgCat.{u, w, w} Λ k} (h : A = B)
    (a : A) :
    B.residueEquiv (IsLocalRing.residue B (ringEquivOfEq h a))
      = A.residueEquiv (IsLocalRing.residue A a) := by
  subst h
  rfl

variable {A : ArtinianLocalAlgCat.{u, w, w} Λ k}

/-- The augmentation of the base of a point of a fibre of the deformation category of `P`. -/
public abbrev fiberAug (x : (ringDeformationProjection Λ k P).Fiber A) :
    (x.1.left.base : Type w) →ₐ[Λ] k := x.1.hom.base.hom

/-- The reduction of a point of a fibre of the deformation category of `P`. -/
public abbrev fiberRed (x : (ringDeformationProjection Λ k P).Fiber A) :
    x.1.left.fiber →+* P := x.1.hom.map.hom

/-- The base-change square of a point of a fibre: its reduction carries the structural map of
the flat algebra to the structural map of `P` along the augmentation. -/
public theorem fiberRed_algebraMap (x : (ringDeformationProjection Λ k P).Fiber A)
    (r : (x.1.left.base : Type w)) :
    fiberRed x (algebraMap (x.1.left.base : Type w) x.1.left.fiber r)
      = algebraMap k P (fiberAug x r) := by
  exact ConcreteCategory.congr_hom x.1.hom.cartesian.w r

/-- The augmentation of the base of a point of a fibre is the residue map followed by the
chosen identification of the residue field with `k`. -/
public theorem fiberAug_eq_residueEquiv (x : (ringDeformationProjection Λ k P).Fiber A)
    (r : (x.1.left.base : Type w)) :
    fiberAug x r
      = x.1.left.base.residueEquiv (IsLocalRing.residue (x.1.left.base : Type w) r) := by
  have hc := x.1.hom.base.residue_comm r
  change (residueFieldBase Λ k).residueEquiv (IsLocalRing.residue k (fiberAug x r))
    = x.1.left.base.residueEquiv (IsLocalRing.residue (x.1.left.base : Type w) r) at hc
  rw [residueFieldBase_residueEquiv_residue] at hc
  exact hc

/-- **The augmentation of the base of a point of a fibre is surjective.** The base is an object
of `𝒞_Λ`, so its residue field is identified with `k`, and the augmentation is that
identification composed with the residue map. -/
public theorem fiberAug_surjective (x : (ringDeformationProjection Λ k P).Fiber A) :
    Function.Surjective (fiberAug x) := by
  intro z
  obtain ⟨r, hr⟩ := IsLocalRing.residue_surjective
    ((x.1.left.base.residueEquiv).symm z)
  refine ⟨r, ?_⟩
  rw [fiberAug_eq_residueEquiv, hr, x.1.left.base.residueEquiv.apply_symm_apply]

/-- The `k`-algebra structure on the base of a point of a fibre, through its augmentation. -/
@[instance_reducible]
public def fiberAugAlgebra (x : (ringDeformationProjection Λ k P).Fiber A) :
    Algebra (x.1.left.base : Type w) k :=
  (fiberAug x).toRingHom.toAlgebra

/-- The `P`-algebra structure on the flat algebra of a point of a fibre, through its
reduction. -/
@[instance_reducible]
public def fiberRedAlgebra (x : (ringDeformationProjection Λ k P).Fiber A) :
    Algebra x.1.left.fiber P :=
  (fiberRed x).toAlgebra

/-- The `P`-algebra structure on the base of a point of a fibre, through its augmentation and
the structural map of `P`. -/
@[instance_reducible]
public def fiberBaseAlgebra (x : (ringDeformationProjection Λ k P).Fiber A) :
    Algebra (x.1.left.base : Type w) P :=
  Algebra.compHom P (fiberAug x).toRingHom

/-- The base of a point of a fibre, its residue field and `P` form a tower. -/
public theorem fiber_isScalarTower_aug (x : (ringDeformationProjection Λ k P).Fiber A) :
    letI := fiberAugAlgebra x
    letI := fiberBaseAlgebra x
    IsScalarTower (x.1.left.base : Type w) k P :=
  letI := fiberAugAlgebra x
  letI := fiberBaseAlgebra x
  IsScalarTower.of_algebraMap_eq fun _ ↦ rfl

/-- The base of a point of a fibre, its flat algebra and `P` form a tower: this is the
commutativity of the base-change square. -/
public theorem fiber_isScalarTower_red (x : (ringDeformationProjection Λ k P).Fiber A) :
    letI := fiberRedAlgebra x
    letI := fiberBaseAlgebra x
    IsScalarTower (x.1.left.base : Type w) x.1.left.fiber P :=
  letI := fiberRedAlgebra x
  letI := fiberBaseAlgebra x
  IsScalarTower.of_algebraMap_eq fun r ↦ (fiberRed_algebraMap x r).symm

/-- **The base-change square of a point of a fibre is a pushout of algebras.** -/
public theorem fiber_isPushout (x : (ringDeformationProjection Λ k P).Fiber A) :
    letI := fiberAugAlgebra x
    letI := fiberRedAlgebra x
    letI := fiberBaseAlgebra x
    letI := fiber_isScalarTower_aug x
    letI := fiber_isScalarTower_red x
    Algebra.IsPushout (x.1.left.base : Type w) x.1.left.fiber k P := by
  let := fiberAugAlgebra x
  let := fiberRedAlgebra x
  let := fiberBaseAlgebra x
  let := fiber_isScalarTower_aug x
  let := fiber_isScalarTower_red x
  apply CommRingCat.isPushout_iff_isPushout.mp
  exact x.1.hom.cartesian

/-- **The class in `Ext¹_P(NL_{P/k}, P ⊗[k] V)` of a point of a fibre of the deformation
category whose base is presented as `k ⊕ V`.**

By `Deformation.Examples.firstOrderExtension` such a point is a square-zero extension of the
`k`-algebra `P` by the `P`-module `P ⊗[k] V`, and this is its class under **Stacks 0GPT**. The
presentation `e` of the base is data because the base of a point of the fibre over `k ⊕ V` is
only *equal* to `k ⊕ V` as an object of `𝒞_Λ`. -/
public def fiberExtClass (x : (ringDeformationProjection Λ k P).Fiber A)
    (e : (x.1.left.base : Type w) ≃+* TrivSqZeroExt k V)
    (hρ : ∀ r, fiberAug x r = (e r).fst) :
    naiveCotangentExtOne k P (P ⊗[k] V) :=
  letI := fiberAugAlgebra x
  letI := fiberRedAlgebra x
  letI := fiberBaseAlgebra x
  letI := fiber_isScalarTower_aug x
  letI := fiber_isScalarTower_red x
  letI := fiber_isPushout x
  letI := algebraOfBaseEquiv x.1.left.fiber e
  letI := baseAlgebraOfBaseEquiv x.1.left.fiber e
  letI := isScalarTower_baseAlgebraOfBaseEquiv x.1.left.fiber e
  extClassOfBaseEquiv (P := P) x.1.left.fiber e
    (algebraMap_algebraOfBaseEquiv x.1.left.fiber e) hρ (fiberAug_surjective x)

variable {B : ArtinianLocalAlgCat.{u, w, w} Λ k}

/-- A morphism of the deformation category carries the structural map of the flat algebra of its
source to that of its target: this is the commutativity of its base-change square. -/
public theorem fiberMap_algebraMap {x : (ringDeformationProjection Λ k P).Fiber A}
    {y : (ringDeformationProjection Λ k P).Fiber B} (φ : x.1 ⟶ y.1)
    (r : (x.1.left.base : Type w)) :
    φ.left.map.hom (algebraMap (x.1.left.base : Type w) x.1.left.fiber r)
      = algebraMap (y.1.left.base : Type w) y.1.left.fiber (φ.left.base.hom r) := by
  exact ConcreteCategory.congr_hom φ.left.cartesian.w r

/-- A morphism of the deformation category is compatible with the reductions to `P`. -/
public theorem fiberRed_fiberMap {x : (ringDeformationProjection Λ k P).Fiber A}
    {y : (ringDeformationProjection Λ k P).Fiber B} (φ : x.1 ⟶ y.1)
    (z : x.1.left.fiber) : fiberRed y (φ.left.map.hom z) = fiberRed x z := by
  have hh := congrArg
    (fun m : FlatAlgebraCategory.Hom x.1.left (residueFieldAlgebra (Λ := Λ) (k := k) P) ↦
      m.map.hom z) (Over.w φ)
  change fiberRed y (φ.left.map.hom z) = fiberRed x z at hh
  exact hh

/-- **The class of a point of a fibre is natural in the coefficient vector space.** A morphism
of the deformation category from a point over `k ⊕ V` to a point over `k ⊕ V'` whose base map is
the one induced by a `k`-linear map `f : V → V'` carries the class of its source to the class of
its target under `Ext¹_P(NL_{P/k}, P ⊗[k] V) → Ext¹_P(NL_{P/k}, P ⊗[k] V')`.

Both the invariance of the class under isomorphism in a fibre and its naturality in `V` are
instances of this statement: an isomorphism in a fibre is a morphism whose base map is the
identity, which is induced by `f = id`. -/
public theorem fiberExtClass_map {x : (ringDeformationProjection Λ k P).Fiber A}
    {y : (ringDeformationProjection Λ k P).Fiber B}
    (ex : (x.1.left.base : Type w) ≃+* TrivSqZeroExt k V)
    (ey : (y.1.left.base : Type w) ≃+* TrivSqZeroExt k V')
    (hρx : ∀ r, fiberAug x r = (ex r).fst) (hρy : ∀ r, fiberAug y r = (ey r).fst)
    (φ : x.1 ⟶ y.1) (f : V →ₗ[k] V')
    (hb : ∀ r, ey (φ.left.base.hom r) = TrivSqZeroExt.map f (ex r)) :
    fiberExtClass y ey hρy
      = naiveCotangentExtOneMap k P (tensorRightMap P f) (fiberExtClass x ex hρx) := by
  let := fiberAugAlgebra x
  let := fiberRedAlgebra x
  let := fiberBaseAlgebra x
  let := fiber_isScalarTower_aug x
  let := fiber_isScalarTower_red x
  let := fiber_isPushout x
  let := algebraOfBaseEquiv x.1.left.fiber ex
  let := baseAlgebraOfBaseEquiv x.1.left.fiber ex
  let := isScalarTower_baseAlgebraOfBaseEquiv x.1.left.fiber ex
  let := fiberAugAlgebra y
  let := fiberRedAlgebra y
  let := fiberBaseAlgebra y
  let := fiber_isScalarTower_aug y
  let := fiber_isScalarTower_red y
  let := fiber_isPushout y
  let := algebraOfBaseEquiv y.1.left.fiber ey
  let := baseAlgebraOfBaseEquiv y.1.left.fiber ey
  let := isScalarTower_baseAlgebraOfBaseEquiv y.1.left.fiber ey
  exact extClassOfBaseEquiv_map (P := P) ex ey
    (algebraMap_algebraOfBaseEquiv x.1.left.fiber ex)
    (algebraMap_algebraOfBaseEquiv y.1.left.fiber ey) hρx hρy
    (fiberAug_surjective x) (fiberAug_surjective y)
    φ.left.base.hom.toRingHom φ.left.map.hom (fiberMap_algebraMap φ) (fiberRed_fiberMap φ) f hb

/-! ### The class of a point of the fibre over a square-zero extension of `𝒞_Λ` -/

/-- The canonical presentation of the base of a point of the fibre over the square-zero
extension `k ⊕ V` of Stacks 06IB: that base *equals* `k ⊕ V` as an object of `𝒞_Λ`, and this is
the induced isomorphism of carriers. -/
public def fiberSquareZeroEquiv (W : FGModuleCat.{w} k)
    (x : (ringDeformationProjection Λ k P).Fiber ((squareZeroExtensionArtinian Λ k).obj W)) :
    (x.1.left.base : Type w) ≃+* TrivSqZeroExt k W.obj :=
  ringEquivOfEq x.2

/-- Under the canonical presentation, the augmentation of the base is the first projection. -/
public theorem fiberAug_fiberSquareZeroEquiv (W : FGModuleCat.{w} k)
    (x : (ringDeformationProjection Λ k P).Fiber ((squareZeroExtensionArtinian Λ k).obj W))
    (r : (x.1.left.base : Type w)) :
    fiberAug x r = (fiberSquareZeroEquiv W x r).fst :=
  (fiberAug_eq_residueEquiv x r).trans
    ((residueEquiv_ringEquivOfEq x.2 r).symm.trans
      (squareZeroExtensionArtinian_residue Λ k W (ringEquivOfEq x.2 r)))

/-- **The class of a point of the fibre over `k ⊕ V`**, for the canonical presentation of its
base. -/
public def squareZeroFiberExtClass (W : FGModuleCat.{w} k)
    (x : (ringDeformationProjection Λ k P).Fiber ((squareZeroExtensionArtinian Λ k).obj W)) :
    naiveCotangentExtOne k P (P ⊗[k] W.obj) :=
  fiberExtClass x (fiberSquareZeroEquiv W x) (fiberAug_fiberSquareZeroEquiv W x)

/-- A morphism of the deformation category lifting the square-zero extension of a `k`-linear
map `f : V → V'` has, under the canonical presentations of the two bases, the base map induced
by `f`. -/
public theorem fiberSquareZeroEquiv_base_hom {W W' : FGModuleCat.{w} k} (f : W ⟶ W')
    {x : (ringDeformationProjection Λ k P).Fiber ((squareZeroExtensionArtinian Λ k).obj W)}
    {y : (ringDeformationProjection Λ k P).Fiber ((squareZeroExtensionArtinian Λ k).obj W')}
    (φ : x.1 ⟶ y.1)
    [(ringDeformationProjection Λ k P).IsHomLift
      ((squareZeroExtensionArtinian Λ k).map f) φ] (r : (x.1.left.base : Type w)) :
    fiberSquareZeroEquiv W' y (φ.left.base.hom r)
      = TrivSqZeroExt.map f.hom.hom (fiberSquareZeroEquiv W x r) := by
  have hfac := IsHomLift.fac' (ringDeformationProjection Λ k P)
    ((squareZeroExtensionArtinian Λ k).map f) φ
  have hx := IsHomLift.domain_eq (ringDeformationProjection Λ k P)
    ((squareZeroExtensionArtinian Λ k).map f) φ
  have hy := IsHomLift.codomain_eq (ringDeformationProjection Λ k P)
    ((squareZeroExtensionArtinian Λ k).map f) φ
  have happ := congrArg (fun g : x.1.left.base ⟶ y.1.left.base ↦ g.hom r) hfac
  change φ.left.base.hom r
    = (eqToHom hy.symm).hom
      (((squareZeroExtensionArtinian Λ k).map f).hom ((eqToHom hx).hom r)) at happ
  rw [hom_eqToHom_apply, hom_eqToHom_apply] at happ
  change φ.left.base.hom r
    = ringEquivOfEq hy.symm (TrivSqZeroExt.map f.hom.hom (ringEquivOfEq hx r)) at happ
  rw [ringEquivOfEq_symm hy] at happ
  change fiberSquareZeroEquiv W' y (φ.left.base.hom r) = _
  rw [happ]
  exact (ringEquivOfEq hy).apply_symm_apply _

end Fiber

/-! ### Injectivity of the class on isomorphism classes of deformations -/

section Injectivity

variable {k : Type w} [Field k] {V : Type w} [AddCommGroup V] [Module k V]

local instance : Module kᵐᵒᵖ V :=
  Module.oppositeOfCommSemiring k V

local instance : IsCentralScalar k V := Module.isCentralScalar_oppositeOfCommSemiring k V

variable {P : Type w} [CommRing P] [Algebra k P]
  {R : Type w} [CommRing R] [Algebra R k] [Algebra R P] [IsScalarTower R k P]
  {R₂ : Type w} [CommRing R₂] [Algebra R₂ k] [Algebra R₂ P] [IsScalarTower R₂ k P]
  {Q : Type w} [CommRing Q] [Algebra R Q] [Algebra Q P] [IsScalarTower R Q P]
  [Algebra (TrivSqZeroExt k V) Q] [Algebra k Q] [IsScalarTower k (TrivSqZeroExt k V) Q]
  {Q₂ : Type w} [CommRing Q₂] [Algebra R₂ Q₂] [Algebra Q₂ P] [IsScalarTower R₂ Q₂ P]
  [Algebra (TrivSqZeroExt k V) Q₂] [Algebra k Q₂] [IsScalarTower k (TrivSqZeroExt k V) Q₂]
  (e : R ≃+* TrivSqZeroExt k V) (e₂ : R₂ ≃+* TrivSqZeroExt k V)
  (hQ : ∀ r : R, algebraMap (TrivSqZeroExt k V) Q (e r) = algebraMap R Q r)
  (hQ₂ : ∀ r : R₂, algebraMap (TrivSqZeroExt k V) Q₂ (e₂ r) = algebraMap R₂ Q₂ r)
  (hρ : ∀ r : R, algebraMap R k r = (e r).fst)
  (hρ₂ : ∀ r : R₂, algebraMap R₂ k r = (e₂ r).fst)

include hQ hρ hQ₂ hρ₂ in
/-- **Two deformations of `P` over `k ⊕ V` with the same class are isomorphic as
deformations.** By **Stacks 0GPT** equal classes mean that the associated square-zero extensions
are isomorphic, and by `Deformation.Examples.smul_of_compatible_algHom` an isomorphism of those
extensions is automatically `k ⊕ V`-linear, hence an isomorphism of the deformations: the
`k ⊕ V`-algebra structure of a first-order deformation is recoverable from its structure of
square-zero extension. -/
public theorem exists_ringEquiv_of_extClassOfBaseEquiv_eq [Module.Flat R Q]
    [Algebra.IsPushout R Q k P] [Module.Flat R₂ Q₂] [Algebra.IsPushout R₂ Q₂ k P]
    (hsurj : Function.Surjective (algebraMap R k))
    (hsurj₂ : Function.Surjective (algebraMap R₂ k))
    (heq : extClassOfBaseEquiv (P := P) Q e hQ hρ hsurj
      = extClassOfBaseEquiv (P := P) Q₂ e₂ hQ₂ hρ₂ hsurj₂) :
    ∃ g : Q ≃+* Q₂, (∀ z : Q, algebraMap Q₂ P (g z) = algebraMap Q P z) ∧
      ∀ (a : TrivSqZeroExt k V) (z : Q), g (a • z) = a • g z := by
  let := flat_algebraOfBaseEquiv (R := R) Q e hQ
  let := flat_algebraOfBaseEquiv (R := R₂) Q₂ e₂ hQ₂
  set π := reductionOfBaseEquiv (P := P) Q e hQ hρ with hπdef
  set π₂ := reductionOfBaseEquiv (P := P) Q₂ e₂ hQ₂ hρ₂ with hπ₂def
  have hπ : Function.Surjective π := surjective_algebraMap_of_isPushout Q hsurj
  have hπ₂ : Function.Surjective π₂ := surjective_algebraMap_of_isPushout Q₂ hsurj₂
  have hker := mem_kerIdeal_smul_of_algebraMap_eq_zero (P := P) Q e hQ hρ hsurj
  have hker₂ := mem_kerIdeal_smul_of_algebraMap_eq_zero (P := P) Q₂ e₂ hQ₂ hρ₂ hsurj₂
  have hπa := isFirstOrderReduction_reductionOfBaseEquiv (P := P) Q e hQ hρ
  have hπa₂ := isFirstOrderReduction_reductionOfBaseEquiv (P := P) Q₂ e₂ hQ₂ hρ₂
  have hcls : Quotient.mk (SquareZeroExtensionProblem.CompatibleExtension.isomorphicSetoid
        (algebraExtensionProblem k P (P ⊗[k] V))) (firstOrderExtension π hπ hπa hker)
      = Quotient.mk (SquareZeroExtensionProblem.CompatibleExtension.isomorphicSetoid
        (algebraExtensionProblem k P (P ⊗[k] V))) (firstOrderExtension π₂ hπ₂ hπa₂ hker₂) :=
    (squareZeroAlgebraExtensionClassesEquivExtOne k P (P ⊗[k] V)).injective heq
  obtain ⟨i⟩ := Quotient.exact hcls
  have hcomm : ∀ z : Q, π₂ (i.toAlgEquiv z) = π z := fun z ↦
    DFunLike.congr_fun i.toB_comm z
  have hkercomm : ∀ x : P ⊗[k] V, i.toAlgEquiv (firstOrderConormalHom π hπ x)
      = firstOrderConormalHom π₂ hπ₂ x := fun x ↦ i.kernelEquiv_comm x
  refine ⟨i.toAlgEquiv.toRingEquiv, hcomm, fun a z ↦ ?_⟩
  exact smul_of_compatible_algHom π hπ hker π₂ hπ₂ hker₂ i.toAlgEquiv.toAlgHom hcomm hkercomm a z


end Injectivity

/-! ### The natural family of maps out of the tangent-space set functor -/

section TangentMap

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
  {P : Type w} [CommRing P] [Algebra k P] {V : Type w} [AddCommGroup V] [Module k V]

local instance : Module kᵐᵒᵖ V :=
  Module.oppositeOfCommSemiring k V

local instance : IsCentralScalar k V := Module.isCentralScalar_oppositeOfCommSemiring k V

/-- The deformations of a `k`-algebra form a category cofibered in groupoids. -/
public theorem isCofiberedInGroupoids_ringDeformationProjection :
    IsCofiberedInGroupoids (ringDeformationProjection Λ k P) :=
  (ringDeformationCategory_isDeformationCategory (Λ := Λ) (k := k) P).predeformation.cofibered

/-- The deformations of the `k`-algebra `P` as a based category over `𝒞_Λ`. This is the `𝓕` of
Stacks 0ET4. -/
public abbrev ringDeformationBasedCategory (Λ : Type u) (k P : Type w) [CommRing Λ] [Field k]
    [Algebra Λ k] [CommRing P] [Algebra k P] :
    BasedCategory (ArtinianLocalAlgCat.{u, w, w} Λ k) :=
  BasedCategory.ofFunctor (ringDeformationProjection Λ k P)

/-- **The class of a point of a fibre over `k ⊕ V` only depends on its isomorphism class.** An
isomorphism in a fibre is a morphism of the deformation category lying over the identity of
`k ⊕ V`, which is the square-zero extension of the identity of `V`; so this is the case `f = id`
of `Deformation.Examples.fiberExtClass_map`. -/
public theorem squareZeroFiberExtClass_congr (W : FGModuleCat.{w} k)
    (a b : (ringDeformationProjection Λ k P).Fiber ((squareZeroExtensionArtinian Λ k).obj W))
    (hab : IsIsomorphic a b) :
    squareZeroFiberExtClass W a = squareZeroFiberExtClass W b := by
  obtain ⟨i⟩ := hab
  have h0 : (squareZeroExtensionArtinian Λ k).map (𝟙 W)
      = 𝟙 ((squareZeroExtensionArtinian Λ k).obj W) :=
    CategoryTheory.Functor.map_id _ W
  let : (ringDeformationProjection Λ k P).IsHomLift
      ((squareZeroExtensionArtinian Λ k).map (𝟙 W)) i.hom.val := by
    rw [h0]
    exact i.hom.2
  have h := fiberExtClass_map (P := P) (fiberSquareZeroEquiv W a) (fiberSquareZeroEquiv W b)
    (fiberAug_fiberSquareZeroEquiv W a) (fiberAug_fiberSquareZeroEquiv W b)
    i.hom.val ((𝟙 W : W ⟶ W).hom.hom) (fiberSquareZeroEquiv_base_hom (𝟙 W) i.hom.val)
  have h2 : squareZeroFiberExtClass W b = naiveCotangentExtOneMap k P
      (tensorRightMap P ((𝟙 W : W ⟶ W).hom.hom)) (squareZeroFiberExtClass W a) := h
  have hid : (((𝟙 W : W ⟶ W).hom.hom) : W.obj →ₗ[k] W.obj) = LinearMap.id := rfl
  rw [h2, hid, tensorRightMap_eq_id, naiveCotangentExtOneMap_id]

/-- **The class of an isomorphism class of deformations of `P` over `k ⊕ V`.** The value of the
set-valued functor `V ↦ 𝓕(k[V])` at `V` is the set of isomorphism classes of deformations of
`P` over `k ⊕ V`, and this is the map sending such a class to the class in
`Ext¹_P(NL_{P/k}, P ⊗[k] V)` of any representative, which is well defined by
`Deformation.Examples.squareZeroFiberExtClass_congr`. -/
public def tangentExtClass (W : FGModuleCat.{w} k)
    (z : (associatedTangentSpaceSetFunctor (ringDeformationBasedCategory Λ k P)
      isCofiberedInGroupoids_ringDeformationProjection).obj W) :
    naiveCotangentExtOne k P (P ⊗[k] W.obj) :=
  Quotient.liftOn
    (cast (isomorphismClasses_obj (ringDeformationBasedCategory Λ k P)
      isCofiberedInGroupoids_ringDeformationProjection
      ((squareZeroExtensionArtinian Λ k).obj W)) z)
    (squareZeroFiberExtClass W) (squareZeroFiberExtClass_congr W)

/-- The class of the isomorphism class of a point of the fibre is the class of that point. -/
public theorem tangentExtClass_classOf (W : FGModuleCat.{w} k)
    (x : (ringDeformationProjection Λ k P).Fiber
      ((squareZeroExtensionArtinian Λ k).obj W)) :
    tangentExtClass W (classOf (ringDeformationBasedCategory Λ k P)
      isCofiberedInGroupoids_ringDeformationProjection x) = squareZeroFiberExtClass W x := by
  change Quotient.liftOn (cast _ (classOf (ringDeformationBasedCategory Λ k P)
      isCofiberedInGroupoids_ringDeformationProjection x))
      (squareZeroFiberExtClass W) (squareZeroFiberExtClass_congr W) = _
  rw [classOf_eq (ringDeformationBasedCategory Λ k P)
    isCofiberedInGroupoids_ringDeformationProjection x]
  rfl

/-- **The family of classes is natural in the coefficient vector space.** This is the naturality
hypothesis of `Deformation.finiteDimensional_artinianTangentSpace_of_natural_injection` for the
receptacle `V ↦ Ext¹_P(NL_{P/k}, P ⊗[k] V)`. -/
public theorem tangentExtClass_naturality {W W' : FGModuleCat.{w} k} (f : W ⟶ W')
    (z : (associatedTangentSpaceSetFunctor (ringDeformationBasedCategory Λ k P)
      isCofiberedInGroupoids_ringDeformationProjection).obj W) :
    tangentExtClass W'
        ((associatedTangentSpaceSetFunctor (ringDeformationBasedCategory Λ k P)
          isCofiberedInGroupoids_ringDeformationProjection).map f z)
      = naiveCotangentExtOneMap k P (tensorRightMap P f.hom.hom) (tangentExtClass W z) := by
  obtain ⟨x, rfl⟩ := classOf_surjective (ringDeformationBasedCategory Λ k P)
    isCofiberedInGroupoids_ringDeformationProjection
    ((squareZeroExtensionArtinian Λ k).obj W) z
  obtain ⟨y₀, φ, hφ⟩ := exists_pushforward isCofiberedInGroupoids_ringDeformationProjection
    ((squareZeroExtensionArtinian Λ k).map f) x.1 x.2
  let : (ringDeformationBasedCategory Λ k P).p.IsHomLift
      ((squareZeroExtensionArtinian Λ k).map f) φ := hφ
  let : (ringDeformationProjection Λ k P).IsHomLift
      ((squareZeroExtensionArtinian Λ k).map f) φ := hφ
  let y : (ringDeformationProjection Λ k P).Fiber
      ((squareZeroExtensionArtinian Λ k).obj W') :=
    ⟨y₀, IsHomLift.codomain_eq (ringDeformationProjection Λ k P)
      ((squareZeroExtensionArtinian Λ k).map f) φ⟩
  have hmap : (associatedTangentSpaceSetFunctor (ringDeformationBasedCategory Λ k P)
      isCofiberedInGroupoids_ringDeformationProjection).map f
        (classOf (ringDeformationBasedCategory Λ k P)
          isCofiberedInGroupoids_ringDeformationProjection x)
      = classOf (ringDeformationBasedCategory Λ k P)
          isCofiberedInGroupoids_ringDeformationProjection y :=
    map_classOf (ringDeformationBasedCategory Λ k P)
      isCofiberedInGroupoids_ringDeformationProjection
      ((squareZeroExtensionArtinian Λ k).map f) x y φ
  have hkey : squareZeroFiberExtClass W' y
      = naiveCotangentExtOneMap k P (tensorRightMap P f.hom.hom)
        (squareZeroFiberExtClass W x) :=
    fiberExtClass_map (P := P) (fiberSquareZeroEquiv W x) (fiberSquareZeroEquiv W' y)
      (fiberAug_fiberSquareZeroEquiv W x) (fiberAug_fiberSquareZeroEquiv W' y)
      φ f.hom.hom (fiberSquareZeroEquiv_base_hom (x := x) (y := y) f φ)
  exact (congrArg (tangentExtClass W') hmap).trans
    ((tangentExtClass_classOf W' y).trans (hkey.trans
      (congrArg (fun t ↦ naiveCotangentExtOneMap k P (tensorRightMap P f.hom.hom) t)
        (tangentExtClass_classOf W x).symm)))

/-- The transport isomorphism of two points of the same fibre, read through the canonical
presentations of their bases, is the comparison of the two presentations. -/
public theorem fiberSquareZeroEquiv_eqToHom (W : FGModuleCat.{w} k)
    (x₁ x₂ : (ringDeformationProjection Λ k P).Fiber
      ((squareZeroExtensionArtinian Λ k).obj W))
    (r : (x₁.1.left.base : Type w)) :
    fiberSquareZeroEquiv W x₂ ((eqToHom (x₁.2.trans x₂.2.symm)).hom r)
      = fiberSquareZeroEquiv W x₁ r := by
  rw [hom_eqToHom_apply]
  exact ringEquivOfEq_trans_apply (x₁.2.trans x₂.2.symm) x₂.2 r

/-- **The class of a point of the fibre over `k ⊕ V` determines its isomorphism class.** Two
points with the same class have isomorphic associated square-zero extensions by **Stacks
0GPT**, that isomorphism is automatically `k ⊕ V`-linear by
`Deformation.Examples.smul_of_compatible_algHom`, and a `k ⊕ V`-linear ring isomorphism
compatible with the reductions is a morphism of the deformation category over the identity of
`k ⊕ V`: the base-change condition holds because both vertical maps of its square are
isomorphisms. -/
public theorem classOf_eq_of_squareZeroFiberExtClass_eq (W : FGModuleCat.{w} k)
    (x₁ x₂ : (ringDeformationProjection Λ k P).Fiber
      ((squareZeroExtensionArtinian Λ k).obj W))
    (heq : squareZeroFiberExtClass W x₁ = squareZeroFiberExtClass W x₂) :
    classOf (ringDeformationBasedCategory Λ k P)
        isCofiberedInGroupoids_ringDeformationProjection x₁
      = classOf (ringDeformationBasedCategory Λ k P)
        isCofiberedInGroupoids_ringDeformationProjection x₂ := by
  let := fiberAugAlgebra x₁
  let := fiberRedAlgebra x₁
  let := fiberBaseAlgebra x₁
  let := fiber_isScalarTower_aug x₁
  let := fiber_isScalarTower_red x₁
  let := fiber_isPushout x₁
  let := algebraOfBaseEquiv x₁.1.left.fiber (fiberSquareZeroEquiv W x₁)
  let := baseAlgebraOfBaseEquiv x₁.1.left.fiber (fiberSquareZeroEquiv W x₁)
  let := isScalarTower_baseAlgebraOfBaseEquiv x₁.1.left.fiber (fiberSquareZeroEquiv W x₁)
  let := fiberAugAlgebra x₂
  let := fiberRedAlgebra x₂
  let := fiberBaseAlgebra x₂
  let := fiber_isScalarTower_aug x₂
  let := fiber_isScalarTower_red x₂
  let := fiber_isPushout x₂
  let := algebraOfBaseEquiv x₂.1.left.fiber (fiberSquareZeroEquiv W x₂)
  let := baseAlgebraOfBaseEquiv x₂.1.left.fiber (fiberSquareZeroEquiv W x₂)
  let := isScalarTower_baseAlgebraOfBaseEquiv x₂.1.left.fiber (fiberSquareZeroEquiv W x₂)
  obtain ⟨g, hgred, hglin⟩ := exists_ringEquiv_of_extClassOfBaseEquiv_eq (P := P)
    (fiberSquareZeroEquiv W x₁) (fiberSquareZeroEquiv W x₂)
    (algebraMap_algebraOfBaseEquiv x₁.1.left.fiber (fiberSquareZeroEquiv W x₁))
    (algebraMap_algebraOfBaseEquiv x₂.1.left.fiber (fiberSquareZeroEquiv W x₂))
    (fiberAug_fiberSquareZeroEquiv W x₁) (fiberAug_fiberSquareZeroEquiv W x₂)
    (fiberAug_surjective x₁) (fiberAug_surjective x₂) heq
  have hstruct : ∀ r : (x₁.1.left.base : Type w),
      g (algebraMap (x₁.1.left.base : Type w) x₁.1.left.fiber r)
        = algebraMap (x₂.1.left.base : Type w) x₂.1.left.fiber
          ((eqToHom (x₁.2.trans x₂.2.symm)).hom r) := by
    intro r
    rw [← algebraMap_algebraOfBaseEquiv x₁.1.left.fiber (fiberSquareZeroEquiv W x₁) r,
      Algebra.algebraMap_eq_smul_one, hglin, map_one,
      ← Algebra.algebraMap_eq_smul_one, ← fiberSquareZeroEquiv_eqToHom W x₁ x₂ r,
      algebraMap_algebraOfBaseEquiv x₂.1.left.fiber (fiberSquareZeroEquiv W x₂)]
  let fhom : FlatAlgebraCategory.Hom x₁.1.left x₂.1.left :=
    { base := eqToHom (x₁.2.trans x₂.2.symm)
      map := CommRingCat.ofHom g.toRingHom
      cartesian := by
        have h0 : IsPushout (FlatAlgebraCategory.structureMap x₁.1.left) (𝟙 _) (𝟙 _)
            (FlatAlgebraCategory.structureMap x₁.1.left) := IsPushout.of_id_snd
        refine h0.of_iso (Iso.refl _) (Iso.refl _)
          (RingEquiv.toCommRingCatIso (ringEquivOfEq (x₁.2.trans x₂.2.symm)))
          (RingEquiv.toCommRingCatIso g) (by simp) ?_ (by ext y; rfl) ?_
        · ext r
          change ringEquivOfEq (x₁.2.trans x₂.2.symm) r
            = (eqToHom (x₁.2.trans x₂.2.symm)).hom r
          rw [hom_eqToHom_apply]
        · ext r
          exact (hstruct r).trans (congrArg
            (algebraMap (x₂.1.left.base : Type w) x₂.1.left.fiber)
            (hom_eqToHom_apply (x₁.2.trans x₂.2.symm) r)) }
  have hover : fhom ≫ x₂.1.hom = x₁.1.hom := by
    refine FlatAlgebraCategory.Hom.ext ?_ ?_
    · exact isTerminal_residueFieldBase.hom_ext _ _
    · ext z
      exact hgred z
  let φ : x₁.1 ⟶ x₂.1 := Over.homMk fhom hover
  have hlift : (ringDeformationProjection Λ k P).IsHomLift
      (𝟙 ((squareZeroExtensionArtinian Λ k).obj W)) φ := by
    refine IsHomLift.of_fac' _ _ _ x₁.2 x₂.2 ?_
    change (eqToHom (x₁.2.trans x₂.2.symm) :
      x₁.1.left.base ⟶ x₂.1.left.base) = eqToHom x₁.2 ≫ 𝟙 _ ≫ eqToHom x₂.2.symm
    simp
  let : (ringDeformationBasedCategory Λ k P).p.IsHomLift
      (𝟙 ((squareZeroExtensionArtinian Λ k).obj W)) φ := hlift
  have h := map_classOf (ringDeformationBasedCategory Λ k P)
    isCofiberedInGroupoids_ringDeformationProjection
    (𝟙 ((squareZeroExtensionArtinian Λ k).obj W)) x₁ x₂ φ
  simpa using h

/-- **The family of classes is injective at every coefficient vector space.** This is the
injectivity hypothesis of
`Deformation.finiteDimensional_artinianTangentSpace_of_natural_injection`, proved here for an
arbitrary `V` rather than only at the rank-one module. -/
public theorem tangentExtClass_injective (W : FGModuleCat.{w} k) :
    Function.Injective (tangentExtClass (Λ := Λ) (P := P) W) := by
  intro z₁ z₂ h
  obtain ⟨x₁, rfl⟩ := classOf_surjective (ringDeformationBasedCategory Λ k P)
    isCofiberedInGroupoids_ringDeformationProjection
    ((squareZeroExtensionArtinian Λ k).obj W) z₁
  obtain ⟨x₂, rfl⟩ := classOf_surjective (ringDeformationBasedCategory Λ k P)
    isCofiberedInGroupoids_ringDeformationProjection
    ((squareZeroExtensionArtinian Λ k).obj W) z₂
  refine classOf_eq_of_squareZeroFiberExtClass_eq W x₁ x₂ ?_
  rw [← tangentExtClass_classOf W x₁, ← tangentExtClass_classOf W x₂]
  exact h

end TangentMap

end Deformation.Examples

end
