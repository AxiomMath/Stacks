module

public import StacksFrontier.Deformation.Artin.Obstruction.FieldBaseChangeTangent
public import StacksFrontier.Deformation.Artin.Obstruction.NaiveVersalityFieldBaseChange

/-!
# The tangent functor at a residue field, and the canonical element read there

Let `𝒳` be a category fibred in groupoids over the big fppf site of `S` satisfying (RS*), let
`x` be an object of `𝒳` over `Spec A`, let `k` be an `A`-algebra which is a field — the residue
field at a point of `Spec A` — and let `x₀ = x|_{Spec k}`. The trivial square-zero extension of
`A` by `k` is the fibre product

`A[k] = A ×_k k[k]`,

with the square-zero surjection `k[k] ⟶ k` on one side, so condition (RS*) identifies the
isomorphism classes of lifts of `x` over `Spec A[k]` with those of `x₀` over `Spec k[k]`.
Transported along the identifications `T_x(M) = Lift(x, A[M])` of the tangent functor of
Stacks 07Y9 this reads

`T_x(k) = T_{x₀}(k)`,

an identification of `k`-vector spaces, and composing with Stacks 0D18 —
`Deformation.Artin.tangentSpace_deformationCategory_linearEquiv`, which identifies `T_{x₀}(k)`
`k`-linearly with the tangent space of the deformation category `𝓕_{𝒳,k,x₀}` — it is the
sentence of Stacks 07YC that `T_x(k)` is the tangent space of `𝓕_{𝒳,k,x₀}`. The map on tangent
spaces of Stacks 07YC is then read there: a tangent vector of `Spec A` at the point, that is an
element of `Der_Λ(A, k) = Hom_A(Ω_{A/Λ}, k)` (Stacks 00RO, Mathlib's
`KaehlerDifferential.linearMapEquivDerivation`), is carried to `T_x(θ)(x_can)`.

The `k`-vector space structure of `T_x(k)` is the one the source's "the space `T_x(k)`" refers
to: the `A`-linear tangent functor of Stacks 07Y9 is evaluated at multiplication by a scalar on
the coefficient module `k`. That is `Deformation.Artin.tangentCoeffModule`, which puts a module
structure on the tangent module at *any* algebra coefficient, and it extends the ambient
`A`-module structure (`Deformation.Artin.residueTangentModule_algebraMap_smul`).

## Main definitions

* `Deformation.Artin.coeffMulLeft` — multiplication by a scalar of an algebra coefficient, as
  an endomorphism of it in the module category of the site.
* `Deformation.Artin.tangentCoeffModule` — the module structure the tangent functor puts on
  `T_x(R)` for an algebra coefficient `R`; `Deformation.Artin.residueTangentModule` is it at
  the residue field.
* `Deformation.Artin.coeffCompareProd` — the coefficient comparison at the product module,
  which is what reading the addition of the tangent modules across (RS*) needs.
* `Deformation.Artin.residueTangentEquiv` — the `k`-linear identification
  `T_x(k) = T_{x₀}(k)`.
* `Deformation.Artin.canonicalTangentMapRestrict` — the map on tangent spaces of Stacks 07YC
  read in `T_{x₀}(k)`: `θ ↦ T_x(θ)(x_can)`.

## Main results

* `Deformation.Artin.residueSquareZeroRing_isPullback` — the square `A[k] = A ×_k k[k]`.
* `Deformation.Artin.map_coeffMulLeft_self`,
  `Deformation.Artin.map_coeffMulLeft_algebraMap` — at the base ring's own coefficient module
  the structure of `tangentCoeffModule` is the ambient one, and in general it extends the
  ambient `A`-module structure.
* `Deformation.Artin.residueTangentBaseChange_map_add`,
  `Deformation.Artin.residueTangentBaseChange_map_smul` — the (RS*) comparison of tangent
  modules at the residue field is additive and respects the scalar action. These are what make
  `residueTangentEquiv` `k`-linear.
* `Deformation.Artin.liftEquiv_residueTangentEquiv` — the identification, read on lift classes,
  is the (RS*) comparison across that square.
* `Deformation.Artin.canonicalTangentMapRestrict_apply` — the value of the map on tangent
  spaces, before the identification, is the canonical element pushed along `θ`.

## Implementation notes

Nothing of the (RS*) input is reproved. The ring square is
`Deformation.Artin.squareZeroRingBaseMap_isPullback` at the residue map `A ⟶ k`, with the
comparison `Deformation.Artin.coeffCompare` of the two module structures that the `A`-algebra
`k` puts on itself as the semilinear bijection of coefficients; the comparison of lift classes
across it is `Deformation.Artin.canonicalFieldBaseChangeEquiv`, which is already that
instantiation of `Deformation.Artin.baseChangeLiftClassesEquiv`. What is added here is the
reading of that comparison on the tangent modules themselves rather than on lift classes, and
the value of the canonical element's tangent map there.

The restriction `x₀` is the chosen pullback of `x` along `Spec k ⟶ Spec A`, since that is the
object the (RS*) comparison lands over, and the structure morphism of `Spec k` is taken to be
the composite `Spec k ⟶ Spec A ⟶ S`, as in
`Deformation.Artin.canonicalFieldBaseChangeEquiv`.

The containments of `Spec A[k]`, `Spec k[k]` and `Spec k` in the chosen big fppf site are
hypotheses rather than consequences, as elsewhere in this development: they are size
conditions.

The source's standing hypotheses for this paragraph — `Λ` Noetherian, `Λ ⟶ A` of finite type,
`k` the residue field at a finite type point — are not needed for these statements and are not
imposed; they are what Stacks 0D18 needs in order to identify `T_{x₀}(k)` with the tangent
space of the deformation category.

That `Deformation.Artin.residueTangentEquiv` is `k`-linear rests on the naturality of the
(RS*) comparison in the coefficient-module pair,
`Deformation.Artin.tangentBaseChangeEquiv_map`: the scalar action is that naturality at
multiplication by a scalar, and additivity is
`Deformation.Artin.tangentBaseChangeEquiv_add`, the split-square argument of Stacks 06I6 run
with the square supplied on both sides at once — the product `k × k` on the left and `k ⊕ k`
over `k` on the right, compared by `Deformation.Artin.coeffCompareProd`.

What is still not delivered for this tag: that the map `θ ↦ T_x(θ)(x_can)` is the map on
tangent spaces *induced by the object `x` over `U`*, i.e. the tangent map of a morphism of
deformation functors `𝓕_{U,k,u₀} ⟶ 𝓕_{𝒳,k,x₀}`. That would need the morphism; the tree has no
deformation functor of the scheme `U` and no induced `1`-morphism.

## References

* [Stacks Project, Tag 07YC](https://stacks.math.columbia.edu/tag/07YC)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u v w

namespace Deformation.Artin

/-- The right `A`-action on a field `k` receiving `A` that the trivial square-zero extension
`A[k]` needs beside the left one. This is the action `Deformation.Artin.oppositeModule` puts on
`k` read as an object of `Mod_A`; it is named here because the coercion of `ModuleCat.of A k`
reduces to `k`, so instance search does not reach that instance at a concrete module. -/
local instance residueOpposite {A k : Type u} [CommRing A] [Field k] [Algebra A k] :
    Module Aᵐᵒᵖ k :=
  oppositeModule A (ModuleCat.of A k)

/-- Over a commutative ring the left and right actions on such a field agree. -/
local instance residueCentralScalar {A k : Type u} [CommRing A] [Field k] [Algebra A k] :
    IsCentralScalar A k :=
  centralScalar A (ModuleCat.of A k)

/-! ### The tangent module at an algebra coefficient -/

section CoeffModule

variable {A : Type u} [CommRing A] {R : Type u} [CommRing R] [Algebra A R]
  {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {toS : Spec (.of A) ⟶ S} {hA : B.Contains (Spec (.of A))}
  {X : Type v} [Category.{w} X] {p : X ⥤ BigFppfOver B S hS} {x : X}
  {hx : p.obj x = algebraOver A B S hS toS hA}

/-- Multiplication by a scalar of an `A`-algebra `R`, as an endomorphism of `R` in the module
category implicit in the chosen big site. -/
public def coeffMulLeft (hR : IsSiteModule A B (ModuleCat.of A R)) (r : R) :
    (⟨ModuleCat.of A R, hR⟩ : SiteModule A B) ⟶ ⟨ModuleCat.of A R, hR⟩ :=
  ObjectProperty.homMk (ModuleCat.ofHom (LinearMap.mulLeft A r))

/-- **The tangent module at an algebra coefficient is a module over that algebra.** For an
`A`-algebra `R` whose trivial square-zero extension lies in the chosen big site, the tangent
module `T_x(R)` carries an `R`-module structure: `r` acts as the value of the tangent functor
at multiplication by `r` on `R`. That this is a module structure is functoriality of the
tangent functor (`one_smul`, `mul_smul`) together with its additivity (`add_smul`,
`zero_smul`) and the `A`-linearity of each of its values (`smul_add`, `smul_zero`). -/
@[instance_reducible]
public def tangentCoeffModule (T : TangentFunctorData A B S hS toS hA p x hx)
    (hR : IsSiteModule A B (ModuleCat.of A R)) :
    Module R ((T.functor.obj (⟨ModuleCat.of A R, hR⟩ : SiteModule A B) :
      Type max (u + 1) v w)) where
  smul r z := T.functor.map (coeffMulLeft hR r) z
  one_smul z := by
    have h : coeffMulLeft hR (1 : R) = 𝟙 (⟨ModuleCat.of A R, hR⟩ : SiteModule A B) := by
      apply ObjectProperty.hom_ext
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro w
      simp [coeffMulLeft]
    change T.functor.map (coeffMulLeft hR (1 : R)) z = z
    rw [h, T.functor.map_id]
    rfl
  mul_smul r r' z := by
    have h : coeffMulLeft hR (r * r') = coeffMulLeft hR r' ≫ coeffMulLeft hR r := by
      apply ObjectProperty.hom_ext
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro w
      simp [coeffMulLeft]
    change T.functor.map (coeffMulLeft hR (r * r')) z =
      T.functor.map (coeffMulLeft hR r) (T.functor.map (coeffMulLeft hR r') z)
    rw [h, T.functor.map_comp]
    rfl
  smul_zero r := map_zero (T.functor.map (coeffMulLeft hR r)).hom
  smul_add r z z' := map_add (T.functor.map (coeffMulLeft hR r)).hom z z'
  add_smul r r' z := by
    have h : coeffMulLeft hR (r + r') = coeffMulLeft hR r + coeffMulLeft hR r' := by
      ext w
      exact add_mul r r' w
    change T.functor.map (coeffMulLeft hR (r + r')) z =
      T.functor.map (coeffMulLeft hR r) z + T.functor.map (coeffMulLeft hR r') z
    rw [h, T.functor.map_add]
    rfl
  zero_smul z := by
    have h : coeffMulLeft hR (0 : R) = 0 := by
      apply ObjectProperty.hom_ext
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro w
      simp [coeffMulLeft]
    change T.functor.map (coeffMulLeft hR (0 : R)) z = 0
    rw [h, T.functor.map_zero]
    rfl

/-- **The action of `Deformation.Artin.tangentCoeffModule` extends the ambient one.**
Multiplication by the image of `a : A` in `R` is `a • 𝟙`, so the `R`-action on `T_x(R)`
restricts along `A ⟶ R` to the `A`-module structure that `T_x(R)` carries as a value of the
`A`-linear tangent functor. -/
public theorem map_coeffMulLeft_algebraMap (T : TangentFunctorData A B S hS toS hA p x hx)
    (hR : IsSiteModule A B (ModuleCat.of A R)) (a : A)
    (z : (T.functor.obj (⟨ModuleCat.of A R, hR⟩ : SiteModule A B) :
      Type max (u + 1) v w)) :
    T.functor.map (coeffMulLeft hR (algebraMap A R a)) z = a • z := by
  have h : coeffMulLeft hR (algebraMap A R a) =
      a • 𝟙 (⟨ModuleCat.of A R, hR⟩ : SiteModule A B) := by
    ext w
    change algebraMap A R a * w = a • w
    rw [Algebra.smul_def]
  rw [h]
  simp

/-- At the base ring's own coefficient module the structure of
`Deformation.Artin.tangentCoeffModule` is the ambient one: multiplication by `r` on `R` is
`r • 𝟙`, and the tangent functor is `R`-linear. -/
public theorem map_coeffMulLeft_self {R : Type u} [CommRing R] {B : BigFppfSite.{u}}
    {S : Scheme.{u}} {hS : B.Contains S} {toS : Spec (.of R) ⟶ S}
    {hA : B.Contains (Spec (.of R))} {X : Type v} [Category.{w} X]
    {p : X ⥤ BigFppfOver B S hS} {x : X} {hx : p.obj x = algebraOver R B S hS toS hA}
    (T : TangentFunctorData R B S hS toS hA p x hx)
    (hR : IsSiteModule R B (ModuleCat.of R R)) (r : R)
    (z : (T.functor.obj (⟨ModuleCat.of R R, hR⟩ : SiteModule R B) :
      Type max (u + 1) v w)) :
    T.functor.map (coeffMulLeft hR r) z = r • z :=
  map_coeffMulLeft_algebraMap T hR r z

end CoeffModule

/-! ### The square `A[k] = A ×_k k[k]` -/

section ResidueSquare

open CategoryTheory.Limits

variable (A k : Type u) [CommRing A] [Field k] [Algebra A k]

/-- **Stacks 07YC: the square `A[k] = A ×_k k[k]`.** For a ring map `A ⟶ k` to a field, the
trivial square-zero extension `A[k]` is the fibre product of `A` and `k[k]` over `k`. The
orientation is the one in which condition (RS*) reads a square: the pullback corner is `A[k]`,
and the square-zero surjection is the projection `k[k] ⟶ k` appearing as the fourth map.

This is `Deformation.Artin.squareZeroRingBaseMap_isPullback` at the residue map, with
`Deformation.Artin.coeffCompare` — the identity of `k`, comparing the two module structures the
`A`-algebra `k` puts on itself — as the semilinear bijection of coefficients. -/
@[stacks 07YC "the fibre product `A[k] = A ×_k k[k]`"]
public theorem residueSquareZeroRing_isPullback :
    IsPullback (CommRingCat.ofHom (TrivSqZeroExt.fstHom A A (ModuleCat.of A k)).toRingHom)
      (CommRingCat.ofHom (squareZeroRingBaseMap (algebraMap A k) (coeffCompare A k)
        (coeffCompare_smul A k)))
      (CommRingCat.ofHom (algebraMap A k))
      (CommRingCat.ofHom (TrivSqZeroExt.fstHom k k (ModuleCat.of k k)).toRingHom) :=
  squareZeroRingBaseMap_isPullback (algebraMap A k) (coeffCompare A k)
    (coeffCompare_smul A k) (coeffCompare_bijective A k)

end ResidueSquare

/-! ### The tangent functor at the residue field -/

section ResidueTangent

variable (A k : Type u) [CommRing A] [Field k] [Algebra A k]
variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (toS : Spec (.of A) ⟶ S) (hA : B.Contains (Spec (.of A)))
variable {X : Type v} [Category.{w} X] (p : X ⥤ BigFppfOver B S hS) (x : X)
  (hx : p.obj x = algebraOver A B S hS toS hA)
  (hp : p.IsFiberedInGroupoids) (hRS : SatisfiesRSStar B S hS p hp)
  (hk : B.Contains (Spec (squareZeroRing A (ModuleCat.of A k))))
  (hAk : B.Contains (Spec (.of k)))
  (hkk : B.Contains (Spec (squareZeroRing k (ModuleCat.of k k))))

/-! #### The coefficient comparison at the product module -/

/-- The comparison of the two module structures that the `A`-algebra `k` puts on `k × k`, as
the identity on the underlying product. This is `Deformation.Artin.coeffCompare` at the product
of the coefficient module with itself, which is what reading the *addition* of the tangent
modules across the (RS\*) comparison needs. -/
public def coeffCompareProd :
    (((siteModuleProd A B hA (⟨ModuleCat.of A k, hk⟩ : SiteModule A B)
        ⟨ModuleCat.of A k, hk⟩).obj : Type u)) →+
      (((siteModuleProd k B hAk (⟨ModuleCat.of k k, hkk⟩ : SiteModule k B)
        ⟨ModuleCat.of k k, hkk⟩).obj : Type u)) :=
  AddMonoidHom.id (k × k)

/-- The comparison `Deformation.Artin.coeffCompareProd` is semilinear over the structure map
`A ⟶ k`, coordinatewise by `Algebra.smul_def` exactly as
`Deformation.Artin.coeffCompare_smul`. -/
public theorem coeffCompareProd_smul (a : A)
    (m : ((siteModuleProd A B hA (⟨ModuleCat.of A k, hk⟩ : SiteModule A B)
      ⟨ModuleCat.of A k, hk⟩).obj : Type u)) :
    coeffCompareProd A k B hA hk hAk hkk (a • m) =
      algebraMap A k a • coeffCompareProd A k B hA hk hAk hkk m := by
  change a • m = algebraMap A k a • m
  refine Prod.ext ?_ ?_
  · change a • m.1 = algebraMap A k a • m.1
    rw [Algebra.smul_def, smul_eq_mul]
  · change a • m.2 = algebraMap A k a • m.2
    rw [Algebra.smul_def, smul_eq_mul]

/-- The comparison `Deformation.Artin.coeffCompareProd` is bijective, being the identity. -/
public theorem coeffCompareProd_bijective :
    Function.Bijective (coeffCompareProd A k B hA hk hAk hkk) :=
  Function.bijective_id

/-! #### The `k`-vector space structure of `T_x(k)` -/

/-- **The `k`-vector space structure of `T_x(k)`.** A scalar `c` acts as the value of the
`A`-linear tangent functor of Stacks 07Y9 at multiplication by `c` on the coefficient module
`k`; this is the structure the source's "the space `T_x(k)`" refers to, and the one
`Deformation.Artin.tangentCoeffModule` attaches to the tangent module at any algebra
coefficient. -/
@[instance_reducible]
public def residueTangentModule :
    Module k ((tangentFunctor A B S hS toS hA p x hx hp hRS).functor.obj
      (⟨ModuleCat.of A k, hk⟩ : SiteModule A B) : Type max (u + 1) v w) :=
  tangentCoeffModule (tangentFunctor A B S hS toS hA p x hx hp hRS) hk

attribute [local instance] residueTangentModule

/-- The `k`-vector space structure of `T_x(k)` extends the `A`-module structure it carries as
a value of the `A`-linear tangent functor of Stacks 07Y9: the scalar `algebraMap A k a` acts as
`a` does. -/
public theorem residueTangentModule_algebraMap_smul (a : A)
    (z : ((tangentFunctor A B S hS toS hA p x hx hp hRS).functor.obj
      (⟨ModuleCat.of A k, hk⟩ : SiteModule A B) : Type max (u + 1) v w)) :
    algebraMap A k a • z = a • z :=
  map_coeffMulLeft_algebraMap (tangentFunctor A B S hS toS hA p x hx hp hRS) hk a z

/-- The (RS\*) comparison of tangent modules at the residue field respects the scalar action:
by `Deformation.Artin.tangentBaseChangeEquiv_map` at multiplication by `c` on either side —
the two are compatible with `Deformation.Artin.coeffCompare`, both being multiplication by `c`
on `k` — and then `Deformation.Artin.map_coeffMulLeft_self`, since on the `k`-side the
coefficient module is the base ring itself and the tangent functor is `k`-linear. -/
public theorem residueTangentBaseChange_map_smul (c : k)
    (z : ((tangentFunctor A B S hS toS hA p x hx hp hRS).functor.obj
      (⟨ModuleCat.of A k, hk⟩ : SiteModule A B) : Type max (u + 1) v w)) :
    letI : p.IsFibered := hp.isFibered
    tangentBaseChangeEquiv (algebraMap A k) B S hS toS
        (Spec.map (CommRingCat.ofHom (algebraMap A k)) ≫ toS) hA hAk rfl
        (⟨ModuleCat.of A k, hk⟩ : SiteModule A B) (⟨ModuleCat.of k k, hkk⟩ : SiteModule k B)
        (coeffCompare A k) (coeffCompare_smul A k) p hp hRS (coeffCompare_bijective A k) x hx
        (c • z) =
      c • tangentBaseChangeEquiv (algebraMap A k) B S hS toS
        (Spec.map (CommRingCat.ofHom (algebraMap A k)) ≫ toS) hA hAk rfl
        (⟨ModuleCat.of A k, hk⟩ : SiteModule A B) (⟨ModuleCat.of k k, hkk⟩ : SiteModule k B)
        (coeffCompare A k) (coeffCompare_smul A k) p hp hRS (coeffCompare_bijective A k) x hx
        z := by
  let : p.IsFibered := hp.isFibered
  have hmul : c • z = (tangentFunctor A B S hS toS hA p x hx hp hRS).functor.map
      (coeffMulLeft hk c) z := rfl
  rw [hmul, tangentBaseChangeEquiv_map (algebraMap A k) B S hS toS
    (Spec.map (CommRingCat.ofHom (algebraMap A k)) ≫ toS) hA hAk rfl
    (⟨ModuleCat.of A k, hk⟩ : SiteModule A B) (⟨ModuleCat.of A k, hk⟩ : SiteModule A B)
    (⟨ModuleCat.of k k, hkk⟩ : SiteModule k B) (⟨ModuleCat.of k k, hkk⟩ : SiteModule k B)
    (coeffCompare A k) (coeffCompare_smul A k) (coeffCompare A k) (coeffCompare_smul A k)
    (coeffMulLeft hk c) (coeffMulLeft hkk c) (fun _ => rfl) p hp hRS
    (coeffCompare_bijective A k) (coeffCompare_bijective A k) x hx]
  exact map_coeffMulLeft_self _ hkk c _

/-- The (RS\*) comparison of tangent modules at the residue field is additive: by
`Deformation.Artin.tangentBaseChangeEquiv_add` at the split square which
`Deformation.Artin.siteModuleProd` supplies on both sides at once, the two product modules
being compared by `Deformation.Artin.coeffCompareProd`. -/
public theorem residueTangentBaseChange_map_add
    (z z' : ((tangentFunctor A B S hS toS hA p x hx hp hRS).functor.obj
      (⟨ModuleCat.of A k, hk⟩ : SiteModule A B) : Type max (u + 1) v w)) :
    letI : p.IsFibered := hp.isFibered
    tangentBaseChangeEquiv (algebraMap A k) B S hS toS
        (Spec.map (CommRingCat.ofHom (algebraMap A k)) ≫ toS) hA hAk rfl
        (⟨ModuleCat.of A k, hk⟩ : SiteModule A B) (⟨ModuleCat.of k k, hkk⟩ : SiteModule k B)
        (coeffCompare A k) (coeffCompare_smul A k) p hp hRS (coeffCompare_bijective A k) x hx
        (z + z') =
      tangentBaseChangeEquiv (algebraMap A k) B S hS toS
        (Spec.map (CommRingCat.ofHom (algebraMap A k)) ≫ toS) hA hAk rfl
        (⟨ModuleCat.of A k, hk⟩ : SiteModule A B) (⟨ModuleCat.of k k, hkk⟩ : SiteModule k B)
        (coeffCompare A k) (coeffCompare_smul A k) p hp hRS (coeffCompare_bijective A k) x hx z +
        tangentBaseChangeEquiv (algebraMap A k) B S hS toS
        (Spec.map (CommRingCat.ofHom (algebraMap A k)) ≫ toS) hA hAk rfl
        (⟨ModuleCat.of A k, hk⟩ : SiteModule A B) (⟨ModuleCat.of k k, hkk⟩ : SiteModule k B)
        (coeffCompare A k) (coeffCompare_smul A k) p hp hRS (coeffCompare_bijective A k) x hx
        z' := by
  let : p.IsFibered := hp.isFibered
  exact tangentBaseChangeEquiv_add (algebraMap A k) B S hS toS
    (Spec.map (CommRingCat.ofHom (algebraMap A k)) ≫ toS) hA hAk rfl
    (⟨ModuleCat.of A k, hk⟩ : SiteModule A B) (⟨ModuleCat.of k k, hkk⟩ : SiteModule k B)
    (coeffCompare A k) (coeffCompare_smul A k) p hp hRS (coeffCompare_bijective A k) x hx
    (siteModuleProd A B hA (⟨ModuleCat.of A k, hk⟩ : SiteModule A B) ⟨ModuleCat.of A k, hk⟩)
    (siteModuleProd k B hAk (⟨ModuleCat.of k k, hkk⟩ : SiteModule k B) ⟨ModuleCat.of k k, hkk⟩)
    (coeffCompareProd A k B hA hk hAk hkk) (coeffCompareProd_smul A k B hA hk hAk hkk)
    (coeffCompareProd_bijective A k B hA hk hAk hkk)
    (siteModuleFst A B hA (⟨ModuleCat.of A k, hk⟩ : SiteModule A B) ⟨ModuleCat.of A k, hk⟩)
    (siteModuleSnd A B hA (⟨ModuleCat.of A k, hk⟩ : SiteModule A B) ⟨ModuleCat.of A k, hk⟩)
    (siteModuleInl A B hA (⟨ModuleCat.of A k, hk⟩ : SiteModule A B) ⟨ModuleCat.of A k, hk⟩)
    (siteModuleInr A B hA (⟨ModuleCat.of A k, hk⟩ : SiteModule A B) ⟨ModuleCat.of A k, hk⟩)
    (siteModuleFst k B hAk (⟨ModuleCat.of k k, hkk⟩ : SiteModule k B) ⟨ModuleCat.of k k, hkk⟩)
    (siteModuleSnd k B hAk (⟨ModuleCat.of k k, hkk⟩ : SiteModule k B) ⟨ModuleCat.of k k, hkk⟩)
    (siteModuleInl_comp_fst A B hA (⟨ModuleCat.of A k, hk⟩ : SiteModule A B)
      ⟨ModuleCat.of A k, hk⟩)
    (siteModuleInr_comp_snd A B hA (⟨ModuleCat.of A k, hk⟩ : SiteModule A B)
      ⟨ModuleCat.of A k, hk⟩)
    (siteModuleInr_comp_fst A B hA (⟨ModuleCat.of A k, hk⟩ : SiteModule A B)
      ⟨ModuleCat.of A k, hk⟩)
    (siteModuleInl_comp_snd A B hA (⟨ModuleCat.of A k, hk⟩ : SiteModule A B)
      ⟨ModuleCat.of A k, hk⟩)
    (fun _ => rfl) (fun _ => rfl) z z'

/-- **Stacks 07YC: `T_x(k)` is the tangent space at the residue field.** By (RS\*) and the
square `A[k] = A ×_k k[k]`, the tangent module `T_x(k)` of `x` at the coefficient module `k`
is the tangent module `T_{x₀}(k)` of the restriction `x₀ = x|_{Spec k}` at the rank-one
`k`-vector space, which by Stacks 0D18 is the tangent space of the deformation category
`𝓕_{𝒳,k,x₀}`.

This is an identification of `k`-vector spaces: on the left the structure
`Deformation.Artin.residueTangentModule` that the `A`-linear tangent functor of Stacks 07Y9
puts on its value at the algebra coefficient `k`, on the right the structure the rank-one
`k`-vector space gives the value of the tangent functor over `k`, which is the one Stacks 0D18
transports from the deformation category. Additivity is
`Deformation.Artin.residueTangentBaseChange_map_add` and the scalar action is
`Deformation.Artin.residueTangentBaseChange_map_smul`.

The identification itself is the (RS\*) comparison of lift classes
`Deformation.Artin.canonicalFieldBaseChangeEquiv` transported along the identifications
`T_x(M) = Lift(x, A[M])` of the tangent functor data of Stacks 07Y9 on both sides, which is
`Deformation.Artin.tangentBaseChangeEquiv` at the residue map. -/
@[stacks 07YC "`T_x(k)` is the tangent space of the deformation functor at the residue field"]
public def residueTangentEquiv :
    letI : p.IsFibered := hp.isFibered
    ((tangentFunctor A B S hS toS hA p x hx hp hRS).functor.obj
        (⟨ModuleCat.of A k, hk⟩ : SiteModule A B) : Type max (u + 1) v w) ≃ₗ[k]
      ((tangentFunctor k B S hS (Spec.map (CommRingCat.ofHom (algebraMap A k)) ≫ toS) hAk p
          (((Functor.chosenPullbacks p).pullbackFunctor
            (algebraOverMapOfRingHom (algebraMap A k) B S hS toS
              (Spec.map (CommRingCat.ofHom (algebraMap A k)) ≫ toS) hA hAk rfl)).obj
                ⟨x, hx⟩).1
          (((Functor.chosenPullbacks p).pullbackFunctor
            (algebraOverMapOfRingHom (algebraMap A k) B S hS toS
              (Spec.map (CommRingCat.ofHom (algebraMap A k)) ≫ toS) hA hAk rfl)).obj
                ⟨x, hx⟩).2
          hp hRS).functor.obj
        (⟨ModuleCat.of k k, hkk⟩ : SiteModule k B) : Type max (u + 1) v w) :=
  letI : p.IsFibered := hp.isFibered
  let e := tangentBaseChangeEquiv (algebraMap A k) B S hS toS
    (Spec.map (CommRingCat.ofHom (algebraMap A k)) ≫ toS) hA hAk rfl
    (⟨ModuleCat.of A k, hk⟩ : SiteModule A B) (⟨ModuleCat.of k k, hkk⟩ : SiteModule k B)
    (coeffCompare A k) (coeffCompare_smul A k) p hp hRS (coeffCompare_bijective A k) x hx
  { toFun := e
    map_add' := residueTangentBaseChange_map_add A k B S hS toS hA p x hx hp hRS hk hAk hkk
    map_smul' := residueTangentBaseChange_map_smul A k B S hS toS hA p x hx hp hRS hk hAk hkk
    invFun := e.symm
    left_inv := e.left_inv
    right_inv := e.right_inv }

/-- The identification `T_x(k) = T_{x₀}(k)` read on lift classes is the (RS\*) comparison
`Deformation.Artin.canonicalFieldBaseChangeEquiv` across the square `A[k] = A ×_k k[k]`: the
class of a lift of `x` over `Spec A[k]` goes to the class of the lift of `x₀` over `Spec k[k]`
that condition (RS\*) attaches to it. This pins `Deformation.Artin.residueTangentEquiv` down to
that comparison. -/
public theorem liftEquiv_residueTangentEquiv
    (z : letI : p.IsFibered := hp.isFibered
      ((tangentFunctor A B S hS toS hA p x hx hp hRS).functor.obj
        (⟨ModuleCat.of A k, hk⟩ : SiteModule A B) : Type max (u + 1) v w)) :
    letI : p.IsFibered := hp.isFibered
    (tangentFunctor k B S hS (Spec.map (CommRingCat.ofHom (algebraMap A k)) ≫ toS) hAk p
          (((Functor.chosenPullbacks p).pullbackFunctor
            (algebraOverMapOfRingHom (algebraMap A k) B S hS toS
              (Spec.map (CommRingCat.ofHom (algebraMap A k)) ≫ toS) hA hAk rfl)).obj
                ⟨x, hx⟩).1
          (((Functor.chosenPullbacks p).pullbackFunctor
            (algebraOverMapOfRingHom (algebraMap A k) B S hS toS
              (Spec.map (CommRingCat.ofHom (algebraMap A k)) ≫ toS) hA hAk rfl)).obj
                ⟨x, hx⟩).2
          hp hRS).liftEquiv (⟨ModuleCat.of k k, hkk⟩ : SiteModule k B)
        (residueTangentEquiv A k B S hS toS hA p x hx hp hRS hk hAk hkk z) =
      canonicalFieldBaseChangeEquiv A k B S hS toS hA p x hx hp hRS hk hAk hkk
        ((tangentFunctor A B S hS toS hA p x hx hp hRS).liftEquiv
          (⟨ModuleCat.of A k, hk⟩ : SiteModule A B) z) :=
  Equiv.apply_symm_apply _ _

end ResidueTangent

/-! ### The canonical element read at the residue field -/

section CanonicalTangent

variable (Λ A k : Type u) [CommRing Λ] [CommRing A] [Field k] [Algebra Λ A] [Algebra A k]
variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (toS : Spec (.of A) ⟶ S) (hA : B.Contains (Spec (.of A)))
variable {X : Type v} [Category.{w} X] (p : X ⥤ BigFppfOver B S hS) (x : X)
  (hx : p.obj x = algebraOver A B S hS toS hA)
  (hp : p.IsFiberedInGroupoids) (hRS : SatisfiesRSStar B S hS p hp)
  (hΩ : B.Contains (Spec (squareZeroRing A (differentialsModule Λ A))))
  (hk : B.Contains (Spec (squareZeroRing A (ModuleCat.of A k))))
  (hAk : B.Contains (Spec (.of k)))
  (hkk : B.Contains (Spec (squareZeroRing k (ModuleCat.of k k))))
  (baseMap : Spec (.of Λ) ⟶ S)
  (baseFactorization : Spec.map (CommRingCat.ofHom (algebraMap Λ A)) ≫ baseMap = toS)

include hΩ baseMap baseFactorization in
/-- **Stacks 07YC: the canonical element produces the map on tangent spaces.** A tangent vector
of `Spec A` at the point with residue field `k` — that is, an element of
`Der_Λ(A, k) = Hom_A(Ω_{A/Λ}, k)`, the identification being Stacks 00RO
(`KaehlerDifferential.linearMapEquivDerivation`) — is carried to `T_x(θ)(x_can)`, read in
`T_{x₀}(k)`, which is the tangent space `T𝓕_{𝒳,k,x₀}` by Stacks 0D18. -/
@[stacks 07YC "`θ ↦ T_x(θ)(x_can)` in `T_x(k) = T𝓕_{𝒳,k,x₀}`"]
public def canonicalTangentMapRestrict (θ : Ω[A⁄Λ] →ₗ[A] k) :
    letI : p.IsFibered := hp.isFibered
    ((tangentFunctor k B S hS (Spec.map (CommRingCat.ofHom (algebraMap A k)) ≫ toS) hAk p
        (((Functor.chosenPullbacks p).pullbackFunctor
          (algebraOverMapOfRingHom (algebraMap A k) B S hS toS
            (Spec.map (CommRingCat.ofHom (algebraMap A k)) ≫ toS) hA hAk rfl)).obj ⟨x, hx⟩).1
        (((Functor.chosenPullbacks p).pullbackFunctor
          (algebraOverMapOfRingHom (algebraMap A k) B S hS toS
            (Spec.map (CommRingCat.ofHom (algebraMap A k)) ≫ toS) hA hAk rfl)).obj ⟨x, hx⟩).2
        hp hRS).functor.obj
      (⟨ModuleCat.of k k, hkk⟩ : SiteModule k B) : Type max (u + 1) v w) :=
  residueTangentEquiv A k B S hS toS hA p x hx hp hRS hk hAk hkk
    (canonicalTangentMap Λ A k B S hS toS hA p x hx hp hRS hΩ hk baseMap baseFactorization θ)

include hΩ baseMap baseFactorization in
/-- The map on tangent spaces at the residue field is the canonical element pushed along `θ`,
read through the (RS\*) identification `T_x(k) = T_{x₀}(k)`. -/
public theorem canonicalTangentMapRestrict_apply (θ : Ω[A⁄Λ] →ₗ[A] k) :
    canonicalTangentMapRestrict Λ A k B S hS toS hA p x hx hp hRS hΩ hk hAk hkk baseMap
        baseFactorization θ =
      residueTangentEquiv A k B S hS toS hA p x hx hp hRS hk hAk hkk
        ((tangentFunctor A B S hS toS hA p x hx hp hRS).functor.map
          (⟨ModuleCat.ofHom θ⟩ : differentialsSiteModule Λ A B hΩ ⟶
            (⟨ModuleCat.of A k, hk⟩ : SiteModule A B))
          (canonicalDeformationElement Λ A B S hS toS hA p x hx hp hRS hΩ
            baseMap baseFactorization).element) :=
  rfl

end CanonicalTangent

end Deformation.Artin
