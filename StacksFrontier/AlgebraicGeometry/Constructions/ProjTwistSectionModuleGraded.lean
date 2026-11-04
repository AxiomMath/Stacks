module

public import Mathlib.Algebra.Module.GradedModule
public import StacksFrontier.Algebra.DirectSum.RangeGrading
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjTwistSectionModule
public import StacksFrontier.AlgebraicGeometry.ProjSheafFunctoriality.Basic
public import StacksFrontier.AlgebraicGeometry.ProjTwistTheta.Multiplication
public import StacksFrontier.AlgebraicGeometry.TwistMultTransport.Structural

/-!
# The graded `S`-module of twisted global sections on `Proj`

Let `S = ⨁_{d ≥ 0} 𝒮 d` be a nonnegatively graded ring, `X = Proj 𝒮`, and let `ℱ` be a sheaf of
`𝒪_X`-modules. The group

`⨁_{n ∈ ℤ} Γ(X, ℱ(n))`

of global sections of all twists of `ℱ` is an `S`-module, graded by the honest groups of global
sections: a homogeneous scalar `a` of degree `i` sends `Γ(X, ℱ(n))` to `Γ(X, ℱ(i + n))`.

The action is *not* obtained from a pairing of sections. It is obtained from a morphism of
sheaves. Multiplication by `a` is a degree-preserving map of graded `S`-modules `S(n) → S(i + n)`,
hence induces a morphism `𝒪_X(n) ⟶ 𝒪_X(i + n)` of the associated sheaves, and tensoring that with
the identity of `ℱ` gives `ℱ(n) ⟶ ℱ(i + n)`, because `ℱ(n)` is by definition `ℱ ⊗ 𝒪_X(n)`. Taking
global sections of those morphisms is the action.

## Main definitions

* `Stacks.AlgebraicGeometry.ProjTwistedSections.twistScalarSheafMap`: multiplication by a
  homogeneous scalar of degree `i`, as a morphism `𝒪_X(n) ⟶ 𝒪_X(k)` of twisting sheaves, for any
  `k` with `i + n = k`.
* `Stacks.AlgebraicGeometry.ProjTwistedSections.twistSheafScalarMap`: the same after tensoring
  with `ℱ`, a morphism `ℱ(n) ⟶ ℱ(k)`.
* `Stacks.AlgebraicGeometry.ProjTwistedSections.twistedSectionsComponent`: the group
  `Γ(X, ℱ(n))` of global sections of a single twist.
* `Stacks.AlgebraicGeometry.ProjTwistedSections.homogeneousScalarTwistedSections`: the action of a
  homogeneous scalar of degree `i` as a map `Γ(X, ℱ(n)) → Γ(X, ℱ(i + n))`.
* `Stacks.AlgebraicGeometry.ProjTwistedSections.twistedGlobalSectionsGrading`: the tautological
  grading of `⨁_{n ∈ ℤ} Γ(X, ℱ(n))`, the degree-`n` piece being the image of the `n`-th summand.
* `Stacks.AlgebraicGeometry.ProjTwistedSections.twistedGlobalSectionsDecomposition`: that family
  is an internal grading.
* `Stacks.AlgebraicGeometry.ProjTwistedSections.twistedSectionsGModule`: the resulting external
  graded-module structure of the family of section groups over the family `𝒮`.
* `Stacks.AlgebraicGeometry.ProjTwistedSections.TwistedGlobalSectionsModule`: the `S`-module
  structure on `⨁_{n ∈ ℤ} Γ(X, ℱ(n))` together with its compatibility with the gradings, bundled
  with the formula that characterizes it.
* `Stacks.AlgebraicGeometry.ProjTwistedSections.twistedGlobalSectionsModule`: that datum.
* `Stacks.AlgebraicGeometry.ProjTwistedSections.twistedGlobalSectionsAssociatedSheaf`: the sheaf
  on `Proj 𝒮` associated to `⨁_{n ∈ ℤ} Γ(X, ℱ(n))` as a graded `S`-module.

## Main results

* `Stacks.AlgebraicGeometry.ProjTwistedSections.twistScalarSheafMap_one`,
  `twistScalarSheafMap_mul`, `twistScalarSheafMap_add`, `twistScalarSheafMap_zero`: the unit,
  composition and biadditivity laws of multiplication by a homogeneous scalar, on the twisting
  sheaves.
* `Stacks.AlgebraicGeometry.ProjTwistedSections.twistSheafScalarMap_one`,
  `twistSheafScalarMap_mul`, `twistSheafScalarMap_add`, `twistSheafScalarMap_zero`: the same four
  laws after tensoring with `ℱ`.
* `Stacks.AlgebraicGeometry.ProjTwistedSections.homogeneousScalarTwistedSections_one`,
  `homogeneousScalarTwistedSections_mul`,
  `homogeneousScalarTwistedSections_add_right`,
  `homogeneousScalarTwistedSections_zero_right`,
  `homogeneousScalarTwistedSections_add_left`,
  `homogeneousScalarTwistedSections_zero_left`: the six laws of an external graded module, on
  global sections, with the degrees transported by `cast` rather than by the heterogeneous
  equality of `GradedMonoid`.
* `Stacks.AlgebraicGeometry.ProjTwistedSections.tensorSheafMap_id_add` and
  `tensorSheafMap_id_zero`: tensoring an identity with a sum, respectively with zero, of
  morphisms of sheaves of modules on a ringed space.

## Implementation notes

The twisted global sections `⨁_{n ∈ ℤ} Γ(X, ℱ(n))` are
`AlgebraicGeometry.ProjectiveSpectrum.Proj.twistedGlobalSections`, the group carrying the
biadditive pairing of Tag 03GK. What is added is the `S`-module structure, its grading, and their
compatibility, which is what the associated-sheaf construction of Tag 01M6 asks of a graded
module.

The action goes through a sheaf morphism rather than through the pairing of Tag 03GK because
that pairing is built from `twistSheafMultiplicationMap`, the morphism `𝒪(n) ⊗ ℱ(m) ⟶ ℱ(n + m)`
of Tag 03GJ, for which no unit or associativity law is available. Multiplication by a *fixed*
homogeneous scalar is `𝟙_ℱ` tensored with a morphism of twisting sheaves, and its unit and
composition laws reduce to the functor laws
`Stacks.AlgebraicGeometry.ProjSheafFunctoriality.associatedModuleSheafMap_id` and
`associatedModuleSheafMap_comp` together with the functoriality of the sheaf tensor product. The
two actions are not compared here.

`twistScalarSheafMap` and `twistSheafScalarMap` take the target degree `k` and a proof of
`i + n = k` rather than being stated at the degree `i + n`: the integer `0 + n` is not `n` by
reflexivity, so stated at `0 + n` the unit law would compare morphisms between syntactically
different gradings `twistGrading 𝒮 n` and `twistGrading 𝒮 (0 + n)`. The transport back to the
degrees `GradedMonoid` asks for happens once, at the level of sections, in
`cast_homogeneousScalarTwistedSections`; the unit and composition laws on sections are stated
through `cast`, and `Sigma.ext` together with `cast_heq` turns them into the heterogeneous
equalities the fields of `DirectSum.Gmodule` ask for.

The grading of the direct sum is the tautological one, `DirectSum.rangeGrading`, with the
decomposition instance `DirectSum.rangeGradingDecomposition`.

The module structure is packaged in a structure together with the equation characterizing it,
rather than exposed as a bare instance: a `Module S (⨁ n, Γ(X, ℱ(n)))` instance is not unique as
data, but it is unique once the action of a homogeneous scalar on a homogeneous section is
prescribed.

## References

* [Stacks Project, Tag 03GK](https://stacks.math.columbia.edu/tag/03GK)
* [Stacks Project, Tag 01M6](https://stacks.math.columbia.edu/tag/01M6)
* [Stacks Project, Tag 01MN](https://stacks.math.columbia.edu/tag/01MN)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace DirectSum
open AlgebraicGeometry.ProjectiveSpectrum.Proj
  (twistingSheaf twistSheafOfModules twistedGlobalSections twistGrading integerGrading
    associatedModuleSheaf)
open Stacks.AlgebraicGeometry.ProjSheafFunctoriality
  (associatedModuleSheafMap associatedModuleSheafMap_id associatedModuleSheafMap_comp)
open Stacks.SheafOfModules.TensorStalkRingedSpace
  (toTensorSheafSection tensorSheafMap_app_toTensorSheafSection)
open Stacks.AlgebraicGeometry.ProjTwistTheta (tensorSheaf_hom_ext)
open Stacks.AlgebraicGeometry.TwistMultTransport (tensorSheafMap_id tensorSheafMap_comp)
open scoped Stacks.GradedLocalization TensorProduct

namespace Stacks.AlgebraicGeometry.ProjTwistedSections

universe u w

attribute [local instance] ProjectiveSpectrum.isPrime
attribute [local instance_reducible] ProjectiveSpectrum.top
attribute [local implicit_reducible] TopCat.Sheaf sheafCompose AlgebraicGeometry.Proj

/-! ### Tensoring an identity with a sum of morphisms

Two facts about the tensor product of sheaves of modules on an arbitrary ringed space, both
checked on the images of pure tensors of sections. -/

/-- Tensoring an identity with the zero morphism gives the zero morphism. -/
public theorem tensorSheafMap_id_zero {X : RingedSpace.{u, u}}
    {A B B' : SheafOfModules.{u} (structureSheafRing X)} :
    ((Functor.uncurry.obj
        (Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X)).presheaf, ((X)).IsSheaf⟩)).map
      (((𝟙 A), (0 : B ⟶ B')) : (_, _) ⟶ (_, _))) = 0 := by
  refine tensorSheaf_hom_ext _ _ ?_
  intro U x y
  obtain ⟨U⟩ := U
  rw [tensorSheafMap_app_toTensorSheafSection X A B A B' (𝟙 A) (0 : B ⟶ B') U x y]
  show toTensorSheafSection X A B' (op U) (x ⊗ₜ (0 : B'.val.obj (op U))) = _
  rw [TensorProduct.tmul_zero]
  show ((Stacks.SheafOfModules.TensorStalkRingedSpace.sheafifyUnit X
    ((PresheafOfModules.tensorObj (O := (X).presheaf) (A.val) (B'.val)))).app
      (op U)).hom 0 = _
  rw [map_zero]
  rfl

/-- Tensoring an identity with a sum of morphisms gives the sum of the tensors. -/
public theorem tensorSheafMap_id_add {X : RingedSpace.{u, u}}
    {A B B' : SheafOfModules.{u} (structureSheafRing X)} (g g' : B ⟶ B') :
    ((Functor.uncurry.obj
        (Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X)).presheaf, ((X)).IsSheaf⟩)).map
      (((𝟙 A), (g + g')) : (_, _) ⟶ (_, _))) =
      ((Functor.uncurry.obj
          (Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X)).presheaf, ((X)).IsSheaf⟩)).map
        (((𝟙 A), g) : (_, _) ⟶ (_, _))) +
      ((Functor.uncurry.obj
          (Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X)).presheaf, ((X)).IsSheaf⟩)).map
        (((𝟙 A), g') : (_, _) ⟶ (_, _))) := by
  refine tensorSheaf_hom_ext _ _ ?_
  intro U x y
  obtain ⟨U⟩ := U
  have hR : ((((Functor.uncurry.obj
          (Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X)).presheaf, ((X)).IsSheaf⟩)).map
          (((𝟙 A), g) : (_, _) ⟶ (_, _))) +
        ((Functor.uncurry.obj
          (Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X)).presheaf, ((X)).IsSheaf⟩)).map
          (((𝟙 A), g') : (_, _) ⟶ (_, _)))).val.app (op U)).hom
        (toTensorSheafSection X A B (op U) (x ⊗ₜ y)) =
      ((((Functor.uncurry.obj
          (Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X)).presheaf, ((X)).IsSheaf⟩)).map
          (((𝟙 A), g) : (_, _) ⟶ (_, _)))).val.app (op U)).hom
          (toTensorSheafSection X A B (op U) (x ⊗ₜ y)) +
        ((((Functor.uncurry.obj
          (Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X)).presheaf, ((X)).IsSheaf⟩)).map
          (((𝟙 A), g') : (_, _) ⟶ (_, _)))).val.app (op U)).hom
          (toTensorSheafSection X A B (op U) (x ⊗ₜ y)) := rfl
  rw [hR, tensorSheafMap_app_toTensorSheafSection X A B A B' (𝟙 A) (g + g') U x y,
    tensorSheafMap_app_toTensorSheafSection X A B A B' (𝟙 A) g U x y,
    tensorSheafMap_app_toTensorSheafSection X A B A B' (𝟙 A) g' U x y]
  simp only [toTensorSheafSection, SheafOfModules.add_val, PresheafOfModules.add_app,
    ModuleCat.hom_add, LinearMap.add_apply, TensorProduct.tmul_add]
  exact map_add _ _ _

variable {S : Type u} {σ : Type w} [CommRing S] [SetLike σ S] [AddSubgroupClass σ S]
  (𝒮 : ℕ → σ) [GradedRing 𝒮]

variable (F : SheafOfModules.{u}
  ((sheafCompose (Opens.grothendieckTopology (ProjectiveSpectrum.top 𝒮))
    (forget₂ CommRingCat.{u} RingCat.{u})).obj
      (ProjectiveSpectrum.Proj.structureSheaf 𝒮)))

/-! ### Degree bookkeeping -/

/-- Shifting by the degree of the unit changes no degree: the integer `0 + n` is `n`. -/
public theorem twistedDegree_zero (n : ℤ) : ((0 : ℕ) : ℤ) + n = n := by simp

/-! ### Multiplication by a homogeneous scalar, as a morphism of twisting sheaves -/

/-- Multiplication by a homogeneous element of degree `i` carries the degree-`j` piece of the
shift `S(n)` into the degree-`j` piece of the shift `S(k)`, whenever `i + n = k`: both are
degree-`j + k` pieces of `S`. -/
public theorem homogeneousMul_mem_twistGrading (i : ℕ) (n k : ℤ) (hk : (i : ℤ) + n = k)
    (a : 𝒮 i) (j : ℤ) (m : S) (hm : m ∈ twistGrading (S := S) 𝒮 n j) :
    LinearMap.mul S S (a : S) m ∈ twistGrading (S := S) 𝒮 k j := by
  have h := SetLike.GradedSMul.smul_mem (A := 𝒮) (B := twistGrading (S := S) 𝒮 n) a.2 hm
  have hdeg : twistGrading (S := S) 𝒮 n ((i : ℕ) +ᵥ j) = twistGrading (S := S) 𝒮 k j := by
    show integerGrading (S := S) 𝒮 (((i : ℕ) +ᵥ j) + n) = integerGrading (S := S) 𝒮 (j + k)
    congr 1
    show (i : ℤ) + j + n = j + k
    omega
  rw [hdeg] at h
  simpa only [smul_eq_mul, LinearMap.mul_apply'] using h

/-- **Multiplication by a homogeneous scalar of degree `i`, as a morphism `𝒪(n) ⟶ 𝒪(k)`** of
twisting sheaves on `Proj 𝒮`, for a degree `k` with `i + n = k`: it is the associated-sheaf image
of the degree-preserving map `S(n) → S(k)` given by multiplication. -/
public noncomputable def twistScalarSheafMap (i : ℕ) (n k : ℤ) (hk : (i : ℤ) + n = k)
    (a : 𝒮 i) :
    twistingSheaf 𝒮 n ⟶ twistingSheaf 𝒮 k :=
  associatedModuleSheafMap 𝒮 (twistGrading (S := S) 𝒮 n) (twistGrading (S := S) 𝒮 k)
    (LinearMap.mul S S (a : S)) (homogeneousMul_mem_twistGrading 𝒮 i n k hk a)

/-- Multiplication by `a` is the associated-sheaf morphism of any degree-preserving linear map
equal to the multiplication map: the membership condition is a `Prop`. -/
private theorem twistScalarSheafMap_eq (i : ℕ) (n k : ℤ) (hk : (i : ℤ) + n = k) (a : 𝒮 i)
    (φ : S →ₗ[S] S) (h : LinearMap.mul S S (a : S) = φ)
    (hφ : ∀ (j : ℤ) (m : S), m ∈ twistGrading (S := S) 𝒮 n j →
      φ m ∈ twistGrading (S := S) 𝒮 k j) :
    twistScalarSheafMap 𝒮 i n k hk a =
      associatedModuleSheafMap 𝒮 (twistGrading (S := S) 𝒮 n) (twistGrading (S := S) 𝒮 k) φ hφ := by
  subst h
  rfl

/-- The associated-sheaf construction is additive in its degree-preserving linear map: on every
localized fibre it is `LocalizedModule.map`, which is linear in the map it localizes. -/
private theorem associatedModuleSheafMap_twist_add (n k : ℤ) (φ ψ : S →ₗ[S] S)
    (hφ : ∀ (j : ℤ) (m : S), m ∈ twistGrading (S := S) 𝒮 n j →
      φ m ∈ twistGrading (S := S) 𝒮 k j)
    (hψ : ∀ (j : ℤ) (m : S), m ∈ twistGrading (S := S) 𝒮 n j →
      ψ m ∈ twistGrading (S := S) 𝒮 k j)
    (hsum : ∀ (j : ℤ) (m : S), m ∈ twistGrading (S := S) 𝒮 n j →
      (φ + ψ) m ∈ twistGrading (S := S) 𝒮 k j) :
    associatedModuleSheafMap 𝒮 (twistGrading (S := S) 𝒮 n) (twistGrading (S := S) 𝒮 k)
        (φ + ψ) hsum =
      associatedModuleSheafMap 𝒮 (twistGrading (S := S) 𝒮 n) (twistGrading (S := S) 𝒮 k) φ hφ +
        associatedModuleSheafMap 𝒮 (twistGrading (S := S) 𝒮 n)
          (twistGrading (S := S) 𝒮 k) ψ hψ := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  ext s
  apply Subtype.ext
  funext x
  show LocalizedModule.map x.1.asHomogeneousIdeal.toIdeal.primeCompl (φ + ψ) (s.1 x) = _
  rw [map_add]
  rfl

/-- A homogeneous scalar of degree `0` whose underlying element is `1` acts as the identity of
`𝒪(n)`. -/
public theorem twistScalarSheafMap_one (n : ℤ) (a : 𝒮 0) (ha : (a : S) = 1) :
    twistScalarSheafMap 𝒮 0 n n (twistedDegree_zero n) a = 𝟙 (twistingSheaf 𝒮 n) :=
  (twistScalarSheafMap_eq 𝒮 0 n n (twistedDegree_zero n) a LinearMap.id
    (LinearMap.ext fun x => by simp [ha]) fun _ _ hm => hm).trans
      (associatedModuleSheafMap_id 𝒮 (twistGrading (S := S) 𝒮 n))

/-- A product of homogeneous scalars of degrees `i` and `j` acts as the composite of the two
morphisms of twisting sheaves. -/
public theorem twistScalarSheafMap_mul (i j : ℕ) (n k : ℤ)
    (hk : ((i + j : ℕ) : ℤ) + n = k) (hik : (i : ℤ) + ((j : ℤ) + n) = k)
    (a : 𝒮 i) (b : 𝒮 j) :
    twistScalarSheafMap 𝒮 (i + j) n k hk
        ⟨(a : S) * (b : S), SetLike.mul_mem_graded a.2 b.2⟩ =
      twistScalarSheafMap 𝒮 j n ((j : ℤ) + n) rfl b ≫
        twistScalarSheafMap 𝒮 i ((j : ℤ) + n) k hik a := by
  rw [twistScalarSheafMap_eq 𝒮 (i + j) n k hk _
    ((LinearMap.mul S S (a : S)).comp (LinearMap.mul S S (b : S)))
    (LinearMap.ext fun x => mul_assoc _ _ x)
    fun jj m hm => homogeneousMul_mem_twistGrading 𝒮 i ((j : ℤ) + n) k hik a jj _
      (homogeneousMul_mem_twistGrading 𝒮 j n ((j : ℤ) + n) rfl b jj m hm)]
  exact associatedModuleSheafMap_comp 𝒮 (twistGrading (S := S) 𝒮 n)
    (twistGrading (S := S) 𝒮 ((j : ℤ) + n)) (twistGrading (S := S) 𝒮 k)
    (LinearMap.mul S S (b : S)) (homogeneousMul_mem_twistGrading 𝒮 j n ((j : ℤ) + n) rfl b)
    (LinearMap.mul S S (a : S)) (homogeneousMul_mem_twistGrading 𝒮 i ((j : ℤ) + n) k hik a)

/-- Multiplication on twisting sheaves is additive in the homogeneous scalar. -/
public theorem twistScalarSheafMap_add (i : ℕ) (n k : ℤ) (hk : (i : ℤ) + n = k) (a b : 𝒮 i) :
    twistScalarSheafMap 𝒮 i n k hk (a + b) =
      twistScalarSheafMap 𝒮 i n k hk a + twistScalarSheafMap 𝒮 i n k hk b := by
  have ha := homogeneousMul_mem_twistGrading 𝒮 i n k hk a
  have hb := homogeneousMul_mem_twistGrading 𝒮 i n k hk b
  rw [twistScalarSheafMap_eq 𝒮 i n k hk (a + b)
    (LinearMap.mul S S (a : S) + LinearMap.mul S S (b : S))
    (map_add (LinearMap.mul S S) (a : S) (b : S))
    fun jj m hm => add_mem (ha jj m hm) (hb jj m hm)]
  exact associatedModuleSheafMap_twist_add 𝒮 n k _ _ ha hb _

/-- The zero homogeneous scalar acts on twisting sheaves as the zero morphism. -/
public theorem twistScalarSheafMap_zero (i : ℕ) (n k : ℤ) (hk : (i : ℤ) + n = k) :
    twistScalarSheafMap 𝒮 i n k hk 0 = 0 := by
  have h := twistScalarSheafMap_add 𝒮 i n k hk 0 0
  rwa [add_zero, left_eq_add] at h

/-! ### The same morphism after tensoring with `ℱ` -/

/-- **Multiplication by a homogeneous scalar of degree `i`, as a morphism `ℱ(n) ⟶ ℱ(k)`** of
twists of `ℱ`, for a degree `k` with `i + n = k`: it is the identity of `ℱ` tensored with the
corresponding morphism of twisting sheaves. -/
public noncomputable def twistSheafScalarMap (i : ℕ) (n k : ℤ) (hk : (i : ℤ) + n = k)
    (a : 𝒮 i) :
    twistSheafOfModules 𝒮 F n ⟶ twistSheafOfModules 𝒮 F k :=
  (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      (_root_.AlgebraicGeometry.ProjectiveSpectrum.Proj.structureSheaf 𝒮))).map
    (X := (F, twistingSheaf 𝒮 n)) (Y := (F, twistingSheaf 𝒮 k))
    ((𝟙 F), (twistScalarSheafMap 𝒮 i n k hk a))

/-- A homogeneous scalar of degree `0` whose underlying element is `1` acts as the identity of
`ℱ(n)`. -/
public theorem twistSheafScalarMap_one (n : ℤ) (a : 𝒮 0) (ha : (a : S) = 1) :
    twistSheafScalarMap 𝒮 F 0 n n (twistedDegree_zero n) a =
      𝟙 (twistSheafOfModules 𝒮 F n) := by
  unfold twistSheafScalarMap
  rw [twistScalarSheafMap_one 𝒮 n a ha]
  exact tensorSheafMap_id (AlgebraicGeometry.Proj 𝒮).toRingedSpace F (twistingSheaf 𝒮 n)

/-- A product of homogeneous scalars acts on `ℱ(n)` as the composite of the two morphisms. -/
public theorem twistSheafScalarMap_mul (i j : ℕ) (n k : ℤ)
    (hk : ((i + j : ℕ) : ℤ) + n = k) (hik : (i : ℤ) + ((j : ℤ) + n) = k)
    (a : 𝒮 i) (b : 𝒮 j) :
    twistSheafScalarMap 𝒮 F (i + j) n k hk
        ⟨(a : S) * (b : S), SetLike.mul_mem_graded a.2 b.2⟩ =
      twistSheafScalarMap 𝒮 F j n ((j : ℤ) + n) rfl b ≫
        twistSheafScalarMap 𝒮 F i ((j : ℤ) + n) k hik a := by
  unfold twistSheafScalarMap
  rw [twistScalarSheafMap_mul 𝒮 i j n k hk hik a b]
  let tensorFunctor := Functor.uncurry.obj
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      (_root_.AlgebraicGeometry.ProjectiveSpectrum.Proj.structureSheaf 𝒮))
  let firstMap : (F, twistingSheaf 𝒮 n) ⟶ (F, twistingSheaf 𝒮 ((j : ℤ) + n)) :=
    (𝟙 F, twistScalarSheafMap 𝒮 j n ((j : ℤ) + n) rfl b)
  let secondMap : (F, twistingSheaf 𝒮 ((j : ℤ) + n)) ⟶ (F, twistingSheaf 𝒮 k) :=
    (𝟙 F, twistScalarSheafMap 𝒮 i ((j : ℤ) + n) k hik a)
  refine (congrArg tensorFunctor.map ?_).trans (tensorFunctor.map_comp firstMap secondMap)
  exact Prod.ext (Category.comp_id (𝟙 F)).symm rfl

/-- Multiplication on twists of `ℱ` is additive in the homogeneous scalar. -/
public theorem twistSheafScalarMap_add (i : ℕ) (n k : ℤ) (hk : (i : ℤ) + n = k) (a b : 𝒮 i) :
    twistSheafScalarMap 𝒮 F i n k hk (a + b) =
      twistSheafScalarMap 𝒮 F i n k hk a + twistSheafScalarMap 𝒮 F i n k hk b := by
  unfold twistSheafScalarMap
  rw [twistScalarSheafMap_add 𝒮 i n k hk a b]
  exact tensorSheafMap_id_add (X := (AlgebraicGeometry.Proj 𝒮).toRingedSpace)
    (A := F) (B := twistingSheaf 𝒮 n) (B' := twistingSheaf 𝒮 k)
    (twistScalarSheafMap 𝒮 i n k hk a) (twistScalarSheafMap 𝒮 i n k hk b)

/-- The zero homogeneous scalar acts on twists of `ℱ` as the zero morphism. -/
public theorem twistSheafScalarMap_zero (i : ℕ) (n k : ℤ) (hk : (i : ℤ) + n = k) :
    twistSheafScalarMap 𝒮 F i n k hk 0 = 0 := by
  unfold twistSheafScalarMap
  rw [twistScalarSheafMap_zero 𝒮 i n k hk]
  exact tensorSheafMap_id_zero (X := (AlgebraicGeometry.Proj 𝒮).toRingedSpace)
    (A := F) (B := twistingSheaf 𝒮 n) (B' := twistingSheaf 𝒮 k)

/-! ### The action on global sections -/

/-- The degree-`n` component of the twisted global sections: the global sections of the `n`-th
twist of `ℱ`. -/
public abbrev twistedSectionsComponent (n : ℤ) : Type u :=
  (twistSheafOfModules 𝒮 F n).val.obj (op ⊤)

/-- Multiplication by a homogeneous element of degree `i` on global sections, as a map
`Γ(Proj 𝒮, ℱ(n)) → Γ(Proj 𝒮, ℱ(i + n))`: the global sections of the morphism
`twistSheafScalarMap`. -/
public noncomputable def homogeneousScalarTwistedSections (i : ℕ) (n : ℤ) (a : 𝒮 i) :
    twistedSectionsComponent 𝒮 F n → twistedSectionsComponent 𝒮 F ((i : ℤ) + n) :=
  fun s => ((twistSheafScalarMap 𝒮 F i n ((i : ℤ) + n) rfl a).val.app (op ⊤)).hom s

/-- Transporting the homogeneous scalar action along an equality of degrees `i + n = k` gives the
global sections of the morphism stated at the degree `k`. -/
public theorem cast_homogeneousScalarTwistedSections (i : ℕ) (n k : ℤ) (hk : (i : ℤ) + n = k)
    (a : 𝒮 i) (s : twistedSectionsComponent 𝒮 F n) :
    cast (congrArg (twistedSectionsComponent 𝒮 F) hk)
        (homogeneousScalarTwistedSections 𝒮 F i n a s) =
      ((twistSheafScalarMap 𝒮 F i n k hk a).val.app (op ⊤)).hom s := by
  cases hk
  rfl

/-- The homogeneous scalar action is additive in the section. -/
public theorem homogeneousScalarTwistedSections_add_right (i : ℕ) (n : ℤ) (a : 𝒮 i)
    (s t : twistedSectionsComponent 𝒮 F n) :
    homogeneousScalarTwistedSections 𝒮 F i n a (s + t) =
      homogeneousScalarTwistedSections 𝒮 F i n a s +
        homogeneousScalarTwistedSections 𝒮 F i n a t :=
  map_add ((twistSheafScalarMap 𝒮 F i n ((i : ℤ) + n) rfl a).val.app (op ⊤)).hom s t

/-- A homogeneous scalar sends the zero section to the zero section. -/
public theorem homogeneousScalarTwistedSections_zero_right (i : ℕ) (n : ℤ) (a : 𝒮 i) :
    homogeneousScalarTwistedSections 𝒮 F i n a (0 : twistedSectionsComponent 𝒮 F n) = 0 :=
  map_zero ((twistSheafScalarMap 𝒮 F i n ((i : ℤ) + n) rfl a).val.app (op ⊤)).hom

/-- The homogeneous scalar action is additive in the scalar. -/
public theorem homogeneousScalarTwistedSections_add_left (i : ℕ) (n : ℤ) (a b : 𝒮 i)
    (s : twistedSectionsComponent 𝒮 F n) :
    homogeneousScalarTwistedSections 𝒮 F i n (a + b) s =
      homogeneousScalarTwistedSections 𝒮 F i n a s +
        homogeneousScalarTwistedSections 𝒮 F i n b s := by
  show ((twistSheafScalarMap 𝒮 F i n ((i : ℤ) + n) rfl (a + b)).val.app (op ⊤)).hom s = _
  rw [twistSheafScalarMap_add 𝒮 F i n ((i : ℤ) + n) rfl a b]
  rfl

/-- The zero homogeneous scalar annihilates every twisted global section. -/
public theorem homogeneousScalarTwistedSections_zero_left (i : ℕ) (n : ℤ)
    (s : twistedSectionsComponent 𝒮 F n) :
    homogeneousScalarTwistedSections 𝒮 F i n 0 s = 0 := by
  show ((twistSheafScalarMap 𝒮 F i n ((i : ℤ) + n) rfl 0).val.app (op ⊤)).hom s = _
  rw [twistSheafScalarMap_zero 𝒮 F i n ((i : ℤ) + n) rfl]
  rfl

/-- A homogeneous scalar of degree `0` whose underlying element is `1` acts as the identity on
twisted global sections, after the degree `0 + n` is identified with `n`. -/
public theorem homogeneousScalarTwistedSections_one (n : ℤ) (a : 𝒮 0) (ha : (a : S) = 1)
    (s : twistedSectionsComponent 𝒮 F n) :
    cast (congrArg (twistedSectionsComponent 𝒮 F) (twistedDegree_zero n))
        (homogeneousScalarTwistedSections 𝒮 F 0 n a s) = s := by
  rw [cast_homogeneousScalarTwistedSections 𝒮 F 0 n n (twistedDegree_zero n) a s,
    twistSheafScalarMap_one 𝒮 F n a ha]
  rfl

/-- A product of homogeneous scalars of degrees `i` and `j` acts as the composite of the two
actions, after the degree `(i + j) + n` is identified with `i + (j + n)`. -/
public theorem homogeneousScalarTwistedSections_mul (i j : ℕ) (n : ℤ) (a : 𝒮 i) (b : 𝒮 j)
    (s : twistedSectionsComponent 𝒮 F n) :
    cast (congrArg (twistedSectionsComponent 𝒮 F)
          (show ((i + j : ℕ) : ℤ) + n = (i : ℤ) + ((j : ℤ) + n) by omega))
        (homogeneousScalarTwistedSections 𝒮 F (i + j) n
          ⟨(a : S) * (b : S), SetLike.mul_mem_graded a.2 b.2⟩ s) =
      homogeneousScalarTwistedSections 𝒮 F i ((j : ℤ) + n) a
        (homogeneousScalarTwistedSections 𝒮 F j n b s) := by
  rw [cast_homogeneousScalarTwistedSections 𝒮 F (i + j) n ((i : ℤ) + ((j : ℤ) + n))
      (by omega) ⟨(a : S) * (b : S), SetLike.mul_mem_graded a.2 b.2⟩ s,
    twistSheafScalarMap_mul 𝒮 F i j n ((i : ℤ) + ((j : ℤ) + n)) (by omega) rfl a b]
  rfl

/-! ### The grading, the external graded module, and the `S`-module -/

/-- The degree-`n` piece of the grading on twisted global sections: the image of the `n`-th
summand in the direct sum. -/
public def twistedGlobalSectionsGrading (n : ℤ) : Submodule ℤ (twistedGlobalSections 𝒮 F) :=
  DirectSum.rangeGrading ℤ (fun m => twistedSectionsComponent 𝒮 F m) n

/-- Every twisted global section decomposes uniquely into homogeneous parts. -/
public noncomputable instance twistedGlobalSectionsDecomposition :
    DirectSum.Decomposition (twistedGlobalSectionsGrading 𝒮 F) :=
  DirectSum.rangeGradingDecomposition ℤ (fun m => twistedSectionsComponent 𝒮 F m)

/-- The family of twisted global-section groups, with the homogeneous scalar action, is an
external graded module over the family of homogeneous pieces of `S`. -/
@[instance_reducible] public noncomputable def twistedSectionsGModule :
    DirectSum.Gmodule (fun i : ℕ => 𝒮 i) (fun n : ℤ => twistedSectionsComponent 𝒮 F n) := by
  classical
  refine {
    smul := fun {i n} a s => homogeneousScalarTwistedSections 𝒮 F i n a s
    one_smul := ?_
    mul_smul := ?_
    smul_add := fun {i n} a s t =>
      homogeneousScalarTwistedSections_add_right 𝒮 F i n a s t
    smul_zero := fun {i n} a => homogeneousScalarTwistedSections_zero_right 𝒮 F i n a
    add_smul := fun {i n} a b s =>
      homogeneousScalarTwistedSections_add_left 𝒮 F i n a b s
    zero_smul := fun {i n} s => homogeneousScalarTwistedSections_zero_left 𝒮 F i n s }
  · intro ⟨n, s⟩
    have hone : ((GradedMonoid.GOne.one (A := fun i : ℕ => 𝒮 i) : 𝒮 0) : S) = 1 := by
      simp only [SetLike.coe_gOne]
    exact Sigma.ext (twistedDegree_zero n)
      ((cast_heq (congrArg (twistedSectionsComponent 𝒮 F) (twistedDegree_zero n)) _).symm.trans
        (heq_of_eq (homogeneousScalarTwistedSections_one 𝒮 F n _ hone s)))
  · intro ⟨i, a⟩ ⟨j, b⟩ ⟨n, s⟩
    have hidx : ((i + j : ℕ) : ℤ) + n = (i : ℤ) + ((j : ℤ) + n) := by omega
    exact Sigma.ext hidx
      ((cast_heq (congrArg (twistedSectionsComponent 𝒮 F) hidx) _).symm.trans
        (heq_of_eq (homogeneousScalarTwistedSections_mul 𝒮 F i j n a b s)))

/-- The canonical `S`-module structure on the twisted global sections of `ℱ`, bundled with its
compatibility with the gradings of `S` and of the direct sum, and with the formula that
characterizes it: a homogeneous scalar of degree `i` carries the degree-`n` summand to the
degree-`i + n` summand by the global sections of the morphism `ℱ(n) ⟶ ℱ(i + n)` it induces. -/
public structure TwistedGlobalSectionsModule where
  /-- The `S`-module structure on `⨁ n, Γ(Proj 𝒮, ℱ(n))`. -/
  moduleInst : Module S (twistedGlobalSections 𝒮 F)
  /-- The action is compatible with the gradings of `S` and of the direct sum. -/
  gradedSMul : letI := moduleInst
    SetLike.GradedSMul 𝒮 (twistedGlobalSectionsGrading 𝒮 F)
  /-- A homogeneous scalar of degree `i` acts on the degree-`n` summand by the homogeneous scalar
  action on sections, landing in the degree-`i + n` summand. -/
  smul_homogeneous : letI := moduleInst
    ∀ (i : ℕ) (n : ℤ) (a : 𝒮 i) (s : twistedSectionsComponent 𝒮 F n),
      (a : S) • (DirectSum.of (fun m : ℤ => twistedSectionsComponent 𝒮 F m) n s :
          twistedGlobalSections 𝒮 F) =
        DirectSum.of (fun m : ℤ => twistedSectionsComponent 𝒮 F m) ((i : ℤ) + n)
          (homogeneousScalarTwistedSections 𝒮 F i n a s)

/-- The graded `S`-module `⨁_{n ∈ ℤ} Γ(Proj 𝒮, ℱ(n))` of twisted global sections: a homogeneous
scalar acts by the global sections of the morphism `ℱ(n) ⟶ ℱ(i + n)` induced by
multiplication. -/
public noncomputable def twistedGlobalSectionsModule : TwistedGlobalSectionsModule 𝒮 F := by
  classical
  let A : ℕ → Type _ := fun i => 𝒮 i
  let B : ℤ → Type _ := fun n => twistedSectionsComponent 𝒮 F n
  let R := ⨁ i, A i
  let T := twistedGlobalSections 𝒮 F
  letI : DirectSum.GCommRing A := inferInstance
  letI : DirectSum.Gmodule A B := twistedSectionsGModule 𝒮 F
  letI : Module R T := DirectSum.Gmodule.module A B
  let moduleInst : Module S T :=
    Module.compHom (M := T) (DirectSum.decomposeRingEquiv 𝒮).toRingHom
  let gradedSMul : letI := moduleInst
      SetLike.GradedSMul 𝒮 (twistedGlobalSectionsGrading 𝒮 F) := by
    let : Module S T := moduleInst
    refine ⟨?_⟩
    intro i n a b ha hb
    let a' : 𝒮 i := ⟨a, ha⟩
    obtain ⟨s, rfl⟩ := (DirectSum.mem_rangeGrading ℤ B n b).mp hb
    refine (DirectSum.mem_rangeGrading ℤ B ((i : ℤ) + n) _).mpr
      ⟨homogeneousScalarTwistedSections 𝒮 F i n a' s, ?_⟩
    change (DirectSum.decompose 𝒮 a) • DirectSum.of B n s =
      DirectSum.of B ((i : ℤ) + n) (homogeneousScalarTwistedSections 𝒮 F i n a' s)
    rw [DirectSum.decompose_of_mem 𝒮 ha, DirectSum.Gmodule.of_smul_of]
    rfl
  letI : Module S T := moduleInst
  refine ⟨moduleInst, gradedSMul, ?_⟩
  intro i n a s
  change (DirectSum.decompose 𝒮 (a : S)) • DirectSum.of B n s = _
  rw [DirectSum.decompose_coe 𝒮 a, DirectSum.Gmodule.of_smul_of]
  rfl

/-- The sheaf on `Proj 𝒮` associated to the graded `S`-module `⨁_{n ∈ ℤ} Γ(Proj 𝒮, ℱ(n))`, with
the module structure and graded action given by `D`. -/
public noncomputable def twistedGlobalSectionsAssociatedSheaf
    (D : TwistedGlobalSectionsModule 𝒮 F) :
    SheafOfModules.{u}
      ((sheafCompose (Opens.grothendieckTopology (ProjectiveSpectrum.top 𝒮))
        (forget₂ CommRingCat.{u} RingCat.{u})).obj
          (ProjectiveSpectrum.Proj.structureSheaf 𝒮)) :=
  letI := D.moduleInst
  letI := D.gradedSMul
  associatedModuleSheaf 𝒮 (twistedGlobalSectionsGrading 𝒮 F)

end Stacks.AlgebraicGeometry.ProjTwistedSections

end
