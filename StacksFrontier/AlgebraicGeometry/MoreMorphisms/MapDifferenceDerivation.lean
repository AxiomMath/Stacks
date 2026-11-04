module

public import StacksFrontier.AlgebraicGeometry.Thickenings.Conormal
public import Mathlib.RingTheory.Derivation.Basic

/-!
# Infinitesimal deformations of maps: the difference of two lifts is a derivation

Let `S` be a scheme, let `i : X ⟶ X'` and `j : Y ⟶ Y'` be first-order thickenings over `S`, and
let `(a, a')` and `(b, b')` be two morphisms of thickenings `(X ⊂ X') ⟶ (Y ⊂ Y')` over `S`.
Suppose that `a = b` and that the two induced maps `a^*𝒞_{Y/Y'} ⟶ 𝒞_{X/X'}` of
[Stacks Project, Tag 01R4] agree. Then `(a')^♯ - (b')^♯` factors as
```
𝒪_{Y'} ⟶ 𝒪_Y --D--> a_*𝒞_{X/X'} ⟶ a_*𝒪_{X'}
```
with `D` an `𝒪_S`-derivation. This file proves that statement on global sections over affine
ambient schemes, which is the affine case of [Stacks Project, Tag 04FG]; the unrestricted
statement is `Stacks.Thickenings.firstOrderImmersionConormalSheafι_differenceDerivation_d`.

With `X'` and `Y'` affine the three sheaves in the factorization are the global-section rings
`Γ(Y', ⊤)`, `Γ(Y, ⊤)` and `Γ(X', ⊤)`, the conormal module of `i` is the ideal
`RingHom.ker i.appTop.hom`, the map `𝒪_{Y'} ⟶ 𝒪_Y` is `j.appTop`, the map
`𝒞_{X/X'} ⟶ 𝒪_{X'}` is the inclusion of that ideal, and the map of conormal modules of
[Stacks Project, Tag 01R4] is `Stacks.Thickenings.conormalMap`. So the factorization reads
```
D (j.appTop x) = a'.appTop x - b'.appTop x
```
inside `Γ(X', ⊤)`, with `D` a `Γ(S, ⊤)`-derivation of `Γ(Y, ⊤)` with values in the conormal
module.

## Main definitions

* `Stacks.Thickenings.appTopAlgebra`: the `Γ(S, ⊤)`-algebra structure on `Γ(T, ⊤)` induced by a
  morphism `T ⟶ S`, which is what makes `𝒪_S`-linearity of the derivation expressible.
* `Stacks.Thickenings.mapDifference`: the difference `a'.appTop x - b'.appTop x`, as a section of
  the defining ideal of `X ⊂ X'`.
* `Stacks.Thickenings.mapDifferenceDescent`: its descent along `j.appTop` to `Γ(Y, ⊤)`.
* `Stacks.Thickenings.mapDifferenceDerivation`: the derivation `D`.

## Main results

* `Stacks.Thickenings.mapDifference_eq_zero_of_mem_ker`: the difference kills the defining ideal
  of `Y ⊂ Y'`. This is where hypothesis (2) of the source is used, and it is what allows the
  difference to descend from `Γ(Y', ⊤)` to `Γ(Y, ⊤)`.
* `Stacks.Thickenings.mapDifferenceDerivation_appTop`: the factorization itself, the affine case
  of [Stacks Project, Tag 04FG].

## Implementation notes

The source's hypothesis (1), `a = b`, is imposed by writing both commutative squares over the
same `a : X ⟶ Y`: a morphism of thickenings `(b, b')` with `b = a` is exactly a `b'` with
`i ≫ b' = a ≫ j`. Hypothesis (2) is the equality of the two conormal maps
`Stacks.Thickenings.conormalMap hi hj comm_a` and `Stacks.Thickenings.conormalMap hi hj comm_b`,
which are maps of the same type precisely because hypothesis (1) has been imposed: the module
structures on the two conormal modules are read off `a` alone.

The derivation is constructed, not merely asserted to exist. Its underlying function is the
descent of `Stacks.Thickenings.mapDifference` through the ring isomorphism
`Γ(Y', ⊤) ⧸ RingHom.ker j.appTop.hom ≃+* Γ(Y, ⊤)` of
`RingHom.quotientKerEquivOfSurjective`, which is legitimate because
`Stacks.Thickenings.mapDifference_eq_zero_of_mem_ker` shows the difference is constant on the
fibres of `j.appTop`. The additivity, `Γ(S, ⊤)`-linearity and Leibniz rule are then checked on
the sections of the form `j.appTop x`, which exhaust `Γ(Y, ⊤)` since the thickening is a closed
immersion of an affine scheme. The Leibniz rule comes out of the square-zero condition on the
defining ideal of `i`: the product of two differences lies in the square of that ideal.

The module structures involved are not instances — they are produced from the first-order
thickening hypotheses by `Stacks.Smooth.thickeningKerModule` and
`Stacks.Thickenings.conormalModuleAlong` — so they are introduced by `letI` in the statements,
as in `Stacks.Thickenings.conormalMap`. Two different `letI`s give the conormal module its
`Γ(Y, ⊤)`-module structure, along `a`, and its `Γ(S, ⊤)`-module structure, along the structure
morphism `i ≫ p` of `X` over `S`.

This is the affine case only. The statement of [Stacks Project, Tag 04FG] for arbitrary,
not necessarily affine, `X'` and `Y'` — the difference of the two comorphisms of sheaves of rings
`𝒪_{Y'} ⟶ a_*𝒪_{X'}` factoring through `𝒪_{Y'} ⟶ 𝒪_Y` and through the subsheaf
`a_*𝒞_{X/X'} ⊆ a_*𝒪_{X'}` by an `𝒪_S`-derivation — is proved twice, by two unrelated routes.
One glues the computation of this file along the affine opens of `Y'`:
`Stacks.Thickenings.mapDifferenceSheaf` is the derivation and
`Stacks.Thickenings.mapDifferenceSheaf_app` the factorization. The other is
`Stacks.Thickenings.firstOrderImmersionConormalSheafι_differenceDerivation_d`, with the
`𝒪_S`-derivation `Stacks.Thickenings.differenceDerivation`, and does not use the affine case
proved here. Both read the conormal sheaf, as here, as the defining ideal of `i`, which for a
first-order thickening it is: the identification is `Stacks.Thickenings.firstOrderConormalIso`
and the inclusion `𝒞_{X/X'} ⟶ 𝒪_{X'}` is `Stacks.Thickenings.firstOrderConormalSheafι`, or its
reading through the conormal sheaf of [Stacks Project, Tag 01R2],
`Stacks.Thickenings.firstOrderImmersionConormalSheafι`.

The `### No @[stacks 04FG]` section that used to stand here named two pieces as missing before
the unrestricted statement could even be made: the identification of sheaves on a first-order
thickening `X'` of `X` with sheaves on `X`, and the compatibility of module pushforward along `a`
with it. **Both are needless**, and neither exists in the library. The second route states the
factorization with the inclusion `Stacks.Thickenings.firstOrderImmersionConormalSheafι` of the
conormal sheaf of `i` into `𝒪_{X'}`, which reads a conormal section over `a⁻¹j⁻¹V` as a section
of `𝒪_{X'}` over `(a')⁻¹V` with no identification of sheaves on `X` and `X'` at all; and it is
proved by descending the difference along the conormal sequence of `j`
([Stacks Project, Tag 01UZ]), whose right-hand end exhibits `Ω_{Y/S}` as a cokernel, so that no
section of `𝒪_Y` ever has to be lifted to `𝒪_{Y'}` by hand.

## References

* [Stacks Project, Tag 01R4](https://stacks.math.columbia.edu/tag/01R4)
* [Stacks Project, Tag 04EX](https://stacks.math.columbia.edu/tag/04EX)
* [Stacks Project, Tag 04FG](https://stacks.math.columbia.edu/tag/04FG)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace Stacks.Thickenings

/-! ### The algebra structure over the base -/

variable {S T X X' Y Y' : Scheme.{u}}

/-- The `Γ(S, ⊤)`-algebra structure on `Γ(T, ⊤)` induced by a morphism `f : T ⟶ S`. This is what
makes `𝒪_S`-linearity of a map out of `Γ(T, ⊤)` expressible on global sections. -/
@[instance_reducible]
noncomputable def appTopAlgebra (f : T ⟶ S) :
    Algebra Γ(S, (⊤ : S.Opens)) Γ(T, (⊤ : T.Opens)) :=
  f.appTop.hom.toAlgebra

/-- The structure map of `Stacks.Thickenings.appTopAlgebra` is `f.appTop`. -/
theorem algebraMap_appTopAlgebra (f : T ⟶ S) (r : Γ(S, (⊤ : S.Opens))) :
    letI := appTopAlgebra f
    algebraMap Γ(S, (⊤ : S.Opens)) Γ(T, (⊤ : T.Opens)) r = f.appTop.hom r :=
  rfl

/-! ### The square-zero defining ideal -/

/-- **The defining ideal of a first-order thickening is square-zero on sections.** The product of
two sections of the defining ideal of `i : X ⟶ X'`, with `X'` affine, vanishes. -/
theorem mul_eq_zero_of_mem_ker_appTop [IsAffine X'] {i : X ⟶ X'}
    (hi : IsFirstOrderThickening i) (u v : RingHom.ker i.appTop.hom) :
    (u : Γ(X', (⊤ : X'.Opens))) * (v : Γ(X', (⊤ : X'.Opens))) = 0 := by
  have hm : (u : Γ(X', (⊤ : X'.Opens))) * (v : Γ(X', (⊤ : X'.Opens)))
      ∈ RingHom.ker i.appTop.hom ^ 2 := by
    rw [pow_two]
    exact Ideal.mul_mem_mul u.2 v.2
  rw [Smooth.ker_appTop_sq_eq_bot hi] at hm
  simpa using hm

/-! ### The difference of two lifts -/

variable {i : X ⟶ X'} {j : Y ⟶ Y'} {a : X ⟶ Y} {a' b' : X' ⟶ Y'} {p : X' ⟶ S} {q : Y' ⟶ S}

/-- **The difference of two lifts of a map, on global sections.** Given two morphisms of
thickenings `(a, a')` and `(a, b')` from `i : X ⟶ X'` to `j : Y ⟶ Y'` with the same reduction
`a`, the difference `a'.appTop x - b'.appTop x` of the two comorphisms lies in the defining ideal
of `i`, because both comorphisms reduce to `a.appTop ∘ j.appTop`. -/
def mapDifference (comm_a : i ≫ a' = a ≫ j) (comm_b : i ≫ b' = a ≫ j)
    (x : Γ(Y', (⊤ : Y'.Opens))) : RingHom.ker i.appTop.hom :=
  ⟨a'.appTop.hom x - b'.appTop.hom x, by
    rw [RingHom.mem_ker, map_sub, appTop_comm_of_comm comm_a x, appTop_comm_of_comm comm_b x,
      sub_self]⟩

/-- The underlying section of `Stacks.Thickenings.mapDifference`. -/
@[simp]
theorem mapDifference_coe (comm_a : i ≫ a' = a ≫ j) (comm_b : i ≫ b' = a ≫ j)
    (x : Γ(Y', (⊤ : Y'.Opens))) :
    ((mapDifference comm_a comm_b x : RingHom.ker i.appTop.hom) : Γ(X', (⊤ : X'.Opens)))
      = a'.appTop.hom x - b'.appTop.hom x :=
  rfl

/-- `Stacks.Thickenings.mapDifference` is additive. -/
theorem mapDifference_add (comm_a : i ≫ a' = a ≫ j) (comm_b : i ≫ b' = a ≫ j)
    (x y : Γ(Y', (⊤ : Y'.Opens))) :
    mapDifference comm_a comm_b (x + y)
      = mapDifference comm_a comm_b x + mapDifference comm_a comm_b y :=
  Subtype.ext (by
    rw [mapDifference_coe, AddMemClass.coe_add, mapDifference_coe, mapDifference_coe, map_add,
      map_add]
    ring)

/-- `Stacks.Thickenings.mapDifference` takes differences to differences. -/
theorem mapDifference_sub (comm_a : i ≫ a' = a ≫ j) (comm_b : i ≫ b' = a ≫ j)
    (x y : Γ(Y', (⊤ : Y'.Opens))) :
    mapDifference comm_a comm_b (x - y)
      = mapDifference comm_a comm_b x - mapDifference comm_a comm_b y :=
  Subtype.ext (by
    rw [mapDifference_coe, AddSubgroupClass.coe_sub, mapDifference_coe, mapDifference_coe,
      map_sub, map_sub]
    ring)

/-- **Hypothesis (2) of the source makes the difference kill the defining ideal of `Y ⊂ Y'`.**
If the two maps of conormal modules induced by `(a, a')` and `(a, b')` agree — the affine form of
the hypothesis that the two maps `a^*𝒞_{Y/Y'} ⟶ 𝒞_{X/X'}` of [Stacks Project, Tag 01R4] are
equal — then `a'.appTop` and `b'.appTop` agree on the defining ideal of `j`. -/
theorem mapDifference_eq_zero_of_mem_ker [IsAffine X'] [IsAffine Y']
    (hi : IsFirstOrderThickening i) (hj : IsFirstOrderThickening j)
    (comm_a : i ≫ a' = a ≫ j) (comm_b : i ≫ b' = a ≫ j)
    (hC : conormalMap hi hj comm_a = conormalMap hi hj comm_b)
    {x : Γ(Y', (⊤ : Y'.Opens))} (hx : x ∈ RingHom.ker j.appTop.hom) :
    mapDifference comm_a comm_b x = 0 := by
  have h : ((conormalMap hi hj comm_a ⟨x, hx⟩ : RingHom.ker i.appTop.hom) :
        Γ(X', (⊤ : X'.Opens)))
      = ((conormalMap hi hj comm_b ⟨x, hx⟩ : RingHom.ker i.appTop.hom) :
        Γ(X', (⊤ : X'.Opens))) := by
    rw [hC]
  rw [conormalMap_apply hi hj comm_a, conormalMap_apply hi hj comm_b] at h
  refine Subtype.ext ?_
  rw [mapDifference_coe, h, sub_self, ZeroMemClass.coe_zero]

/-! ### The descent to the sections of the closed subscheme -/

/-- **The difference descends along `j.appTop`.** Since `Stacks.Thickenings.mapDifference` kills
the defining ideal of `j : Y ⟶ Y'`, it is constant on the fibres of the surjection
`j.appTop : Γ(Y', ⊤) ⟶ Γ(Y, ⊤)` and therefore descends to a map on `Γ(Y, ⊤)`. This is the map
`𝒪_Y ⟶ a_*𝒞_{X/X'}` of [Stacks Project, Tag 04FG] on global sections. -/
noncomputable def mapDifferenceDescent [IsAffine X'] [IsAffine Y']
    (hi : IsFirstOrderThickening i) (hj : IsFirstOrderThickening j)
    (comm_a : i ≫ a' = a ≫ j) (comm_b : i ≫ b' = a ≫ j)
    (hC : conormalMap hi hj comm_a = conormalMap hi hj comm_b) :
    Γ(Y, (⊤ : Y.Opens)) → RingHom.ker i.appTop.hom :=
  fun y ↦ Quotient.lift (mapDifference comm_a comm_b)
    (fun u v huv ↦ by
      have h := mapDifference_eq_zero_of_mem_ker hi hj comm_a comm_b hC
        ((Submodule.quotientRel_def _).mp huv)
      rw [mapDifference_sub] at h
      exact sub_eq_zero.mp h)
    ((RingHom.quotientKerEquivOfSurjective
      (Smooth.surjective_appTop_of_isFirstOrderThickening hj)).symm y)

/-- The descent of the difference recovers the difference: on a section of the form `j.appTop x`
the map `Stacks.Thickenings.mapDifferenceDescent` takes the value
`Stacks.Thickenings.mapDifference` at `x`. -/
theorem mapDifferenceDescent_appTop [IsAffine X'] [IsAffine Y']
    (hi : IsFirstOrderThickening i) (hj : IsFirstOrderThickening j)
    (comm_a : i ≫ a' = a ≫ j) (comm_b : i ≫ b' = a ≫ j)
    (hC : conormalMap hi hj comm_a = conormalMap hi hj comm_b)
    (x : Γ(Y', (⊤ : Y'.Opens))) :
    mapDifferenceDescent hi hj comm_a comm_b hC (j.appTop.hom x)
      = mapDifference comm_a comm_b x := by
  have hsurj := Smooth.surjective_appTop_of_isFirstOrderThickening hj
  have h : (RingHom.quotientKerEquivOfSurjective hsurj).symm (j.appTop.hom x)
      = Ideal.Quotient.mk (RingHom.ker j.appTop.hom) x := by
    rw [RingEquiv.symm_apply_eq]
    rfl
  simp only [mapDifferenceDescent, h]
  rfl

/-! ### The derivation -/

/-- The descent of the difference, as a `Γ(S, ⊤)`-linear map. This is the underlying linear map
of `Stacks.Thickenings.mapDifferenceDerivation`; `𝒪_S`-linearity is where the hypothesis that
the two morphisms of thickenings are morphisms over `S` enters. -/
noncomputable def mapDifferenceLinearMap [IsAffine X'] [IsAffine Y']
    (hi : IsFirstOrderThickening i) (hj : IsFirstOrderThickening j)
    (comm_a : i ≫ a' = a ≫ j) (comm_b : i ≫ b' = a ≫ j)
    (ha' : a' ≫ q = p) (hb' : b' ≫ q = p)
    (hC : conormalMap hi hj comm_a = conormalMap hi hj comm_b) :
    letI := appTopAlgebra (j ≫ q)
    letI := conormalModuleAlong hi (i ≫ p)
    Γ(Y, (⊤ : Y.Opens)) →ₗ[Γ(S, (⊤ : S.Opens))] RingHom.ker i.appTop.hom :=
  letI := appTopAlgebra (j ≫ q)
  letI := conormalModuleAlong hi (i ≫ p)
  have hsurj := Smooth.surjective_appTop_of_isFirstOrderThickening hj
  { toFun := mapDifferenceDescent hi hj comm_a comm_b hC
    map_add' := fun y z ↦ by
      obtain ⟨u, rfl⟩ := hsurj y
      obtain ⟨v, rfl⟩ := hsurj z
      rw [← map_add, mapDifferenceDescent_appTop, mapDifferenceDescent_appTop,
        mapDifferenceDescent_appTop, mapDifference_add]
    map_smul' := fun r y ↦ by
      obtain ⟨u, rfl⟩ := hsurj y
      have hr : r • j.appTop.hom u = j.appTop.hom (q.appTop.hom r * u) := by
        rw [map_mul, Algebra.smul_def, algebraMap_appTopAlgebra, appTop_comp_apply]
      have hA : a'.appTop.hom (q.appTop.hom r) = p.appTop.hom r := by
        rw [appTop_comp_apply, ha']
      have hB : b'.appTop.hom (q.appTop.hom r) = p.appTop.hom r := by
        rw [appTop_comp_apply, hb']
      rw [RingHom.id_apply, hr, mapDifferenceDescent_appTop, mapDifferenceDescent_appTop]
      refine Subtype.ext ?_
      rw [conormalModuleAlong_smul hi (i ≫ p) r (x := p.appTop.hom r)
          (appTop_comp_apply i p r), Submodule.coe_smul, smul_eq_mul, mapDifference_coe,
        mapDifference_coe, map_mul, map_mul, hA, hB]
      ring }

/-- The value of `Stacks.Thickenings.mapDifferenceLinearMap` on a section of the form
`j.appTop x` is the difference at `x`. -/
theorem mapDifferenceLinearMap_appTop [IsAffine X'] [IsAffine Y']
    (hi : IsFirstOrderThickening i) (hj : IsFirstOrderThickening j)
    (comm_a : i ≫ a' = a ≫ j) (comm_b : i ≫ b' = a ≫ j)
    (ha' : a' ≫ q = p) (hb' : b' ≫ q = p)
    (hC : conormalMap hi hj comm_a = conormalMap hi hj comm_b)
    (x : Γ(Y', (⊤ : Y'.Opens))) :
    letI := appTopAlgebra (j ≫ q)
    letI := conormalModuleAlong hi (i ≫ p)
    mapDifferenceLinearMap hi hj comm_a comm_b ha' hb' hC (j.appTop.hom x)
      = mapDifference comm_a comm_b x :=
  mapDifferenceDescent_appTop hi hj comm_a comm_b hC x

/-- **The difference of two infinitesimal deformations of a map is a derivation**, affine case of
[Stacks Project, Tag 04FG]. Let `i : X ⟶ X'` and `j : Y ⟶ Y'` be first-order thickenings with
`X'` and `Y'` affine, let `p : X' ⟶ S` and `q : Y' ⟶ S` make them thickenings over `S`, and let
`(a, a')` and `(a, b')` be two morphisms of thickenings over `S` with the same reduction `a` —
hypothesis (1) of the source. Assume the two induced maps of conormal modules agree — hypothesis
(2). Then the difference of the two comorphisms descends to a `Γ(S, ⊤)`-derivation of `Γ(Y, ⊤)`
with values in the conormal module of `i`.

The conormal module carries two module structures here: over `Γ(Y, ⊤)` along `a`, and over
`Γ(S, ⊤)` along the structure morphism `i ≫ p` of `X` over `S`. -/
@[stacks 04FG "affine case"]
noncomputable def mapDifferenceDerivation [IsAffine X'] [IsAffine Y']
    (hi : IsFirstOrderThickening i) (hj : IsFirstOrderThickening j)
    (comm_a : i ≫ a' = a ≫ j) (comm_b : i ≫ b' = a ≫ j)
    (ha' : a' ≫ q = p) (hb' : b' ≫ q = p)
    (hC : conormalMap hi hj comm_a = conormalMap hi hj comm_b) :
    letI := appTopAlgebra (j ≫ q)
    letI := conormalModuleAlong hi a
    letI := conormalModuleAlong hi (i ≫ p)
    Derivation Γ(S, (⊤ : S.Opens)) Γ(Y, (⊤ : Y.Opens)) (RingHom.ker i.appTop.hom) :=
  letI := appTopAlgebra (j ≫ q)
  letI := conormalModuleAlong hi a
  letI := conormalModuleAlong hi (i ≫ p)
  have hsurj := Smooth.surjective_appTop_of_isFirstOrderThickening hj
  { mapDifferenceLinearMap hi hj comm_a comm_b ha' hb' hC with
    map_one_eq_zero' := by
      have h : (1 : Γ(Y, (⊤ : Y.Opens))) = j.appTop.hom 1 := (map_one _).symm
      rw [h, mapDifferenceLinearMap_appTop]
      exact Subtype.ext (by rw [mapDifference_coe, map_one, map_one, sub_self,
        ZeroMemClass.coe_zero])
    leibniz' := fun y z ↦ by
      obtain ⟨u, rfl⟩ := hsurj y
      obtain ⟨v, rfl⟩ := hsurj z
      rw [← map_mul, mapDifferenceLinearMap_appTop, mapDifferenceLinearMap_appTop,
        mapDifferenceLinearMap_appTop]
      refine Subtype.ext ?_
      rw [AddMemClass.coe_add,
        conormalModuleAlong_smul hi a (j.appTop.hom u) (x := b'.appTop.hom u)
          (appTop_comm_of_comm comm_b u),
        conormalModuleAlong_smul hi a (j.appTop.hom v) (x := b'.appTop.hom v)
          (appTop_comm_of_comm comm_b v),
        Submodule.coe_smul, Submodule.coe_smul, smul_eq_mul, smul_eq_mul, mapDifference_coe,
        mapDifference_coe, mapDifference_coe, map_mul, map_mul]
      have hz := mul_eq_zero_of_mem_ker_appTop hi (mapDifference comm_a comm_b u)
        (mapDifference comm_a comm_b v)
      rw [mapDifference_coe, mapDifference_coe] at hz
      linear_combination hz }

/-- **The factorization of [Stacks Project, Tag 04FG], affine case.** The difference of the two
comorphisms `a'.appTop` and `b'.appTop` on `Γ(Y', ⊤)` is the composite
```
Γ(Y', ⊤) --j.appTop--> Γ(Y, ⊤) --D--> RingHom.ker i.appTop.hom ⊆ Γ(X', ⊤)
```
where `D` is the `Γ(S, ⊤)`-derivation `Stacks.Thickenings.mapDifferenceDerivation`. -/
@[stacks 04FG "affine case"]
theorem mapDifferenceDerivation_appTop [IsAffine X'] [IsAffine Y']
    (hi : IsFirstOrderThickening i) (hj : IsFirstOrderThickening j)
    (comm_a : i ≫ a' = a ≫ j) (comm_b : i ≫ b' = a ≫ j)
    (ha' : a' ≫ q = p) (hb' : b' ≫ q = p)
    (hC : conormalMap hi hj comm_a = conormalMap hi hj comm_b)
    (x : Γ(Y', (⊤ : Y'.Opens))) :
    letI := appTopAlgebra (j ≫ q)
    letI := conormalModuleAlong hi a
    letI := conormalModuleAlong hi (i ≫ p)
    ((mapDifferenceDerivation hi hj comm_a comm_b ha' hb' hC (j.appTop.hom x) :
        RingHom.ker i.appTop.hom) : Γ(X', (⊤ : X'.Opens)))
      = a'.appTop.hom x - b'.appTop.hom x :=
  congrArg Subtype.val (mapDifferenceLinearMap_appTop hi hj comm_a comm_b ha' hb' hC x)

end Stacks.Thickenings

end
