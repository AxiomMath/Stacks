module

public import Mathlib.Algebra.Module.GradedModule
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.DirectSum.ExternalGrading
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjTwistModuleMultiplication
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjTwistSectionComparison
public import StacksFrontier.AlgebraicGeometry.ProjStalkGlobalSections.Functoriality
public import StacksFrontier.AlgebraicGeometry.ProjTwistTheta.Multiplication

/-!
# The graded module of twisted global sections of a sheaf on `Proj`

Let `S = ⨁_{d ≥ 0} 𝒮 d` be a nonnegatively graded ring, `X = Proj 𝒮`, and `ℱ` a sheaf of
`𝒪_X`-modules. For `d ≥ 0` put `M_d = Γ(X, ℱ(d))`, where `ℱ(d) = ℱ ⊗ 𝒪_X(d)` is the `d`-th
twist. This file makes

`M = ⨁_{d ≥ 0} M_d`

a graded `S`-module, and forms the sheaf `M̃` on `X` associated to it.

The multiplication `S_e × M_d → M_{e+d}` is built as follows: a homogeneous element `a` of
degree `e` multiplies the local fractions of `𝒪_X(d)` into those of `𝒪_X(e+d)`, which is a
morphism `𝒪_X(d) ⟶ 𝒪_X(e+d)` of twisting sheaves, and tensoring it with `ℱ` gives
`ℱ(d) ⟶ ℱ(e+d)`, whose effect on global sections is the action. The module laws are the
functoriality and the additivity of those two constructions.

For `S = R[T₀, …, Tₘ]` graded by total degree, `X` is `ℙᵐ_R` and `M` is the graded
`R[T₀, …, Tₘ]`-module of the first assertion of Tag 03GM. No hypothesis on `ℱ` is needed for
that assertion, so it is stated for an arbitrary sheaf of modules rather than only for a
quasi-coherent one.

## Main definitions

* `Stacks.AlgebraicGeometry.ProjTwistSectionModule.mulLinearMap`: multiplication by a ring
  element, as a linear endomorphism of the regular module.
* `Stacks.AlgebraicGeometry.ProjTwistSectionModule.homogeneousMul`: multiplication by a
  homogeneous element of degree `e`, as a morphism `𝒪_X(d) ⟶ 𝒪_X(e + d)` of twisting sheaves.
* `Stacks.AlgebraicGeometry.ProjTwistSectionModule.twistMul`: the same, tensored with `ℱ`, as
  a morphism `ℱ(d) ⟶ ℱ(e + d)`.
* `Stacks.AlgebraicGeometry.ProjTwistSectionModule.twistSections`: the group `Γ(X, ℱ(d))`.
* `Stacks.AlgebraicGeometry.ProjTwistSectionModule.gsmul`: the action of a homogeneous element
  of degree `e` on `Γ(X, ℱ(d))`, landing in `Γ(X, ℱ(e + d))`.
* `Stacks.AlgebraicGeometry.ProjTwistSectionModule.twistSectionModule`: the direct sum
  `⨁_{d ≥ 0} Γ(X, ℱ(d))`, with its `S`-module structure `instModule`.
* `Stacks.AlgebraicGeometry.ProjTwistSectionModule.moduleGrading`: its grading by the
  integers, the negative pieces being trivial.
* `Stacks.AlgebraicGeometry.ProjTwistSectionModule.associatedTwistSectionSheaf`: the sheaf
  `M̃` on `X` associated to that graded module.
* `Stacks.AlgebraicGeometry.ProjTwistSectionModule.projectiveGrading`,
  `projectiveTwistSectionModule` and `projectiveAssociatedTwistSectionSheaf`: the three
  objects above for `X = ℙᵐ_R`.

## Main results

* `Stacks.AlgebraicGeometry.ProjTwistSectionModule.instGmodule`: the graded module laws for
  the action.
* `Stacks.AlgebraicGeometry.ProjTwistSectionModule.instDecomposition` and
  `Stacks.AlgebraicGeometry.ProjTwistSectionModule.instGradedSMul`: the integer grading is an
  internal grading of the direct sum, compatible with the grading of `S`. Together with
  `instModule` these are exactly the data that the sheaf associated to a graded module
  consumes, which is what lets `associatedTwistSectionSheaf` be formed.
* `Stacks.AlgebraicGeometry.ProjTwistSectionModule.homogeneousMul_one`,
  `homogeneousMul_mul`, `homogeneousMul_add_app` and `homogeneousMul_zero_app`: the unit,
  multiplicativity and additivity of multiplication on the twisting sheaves, and
  `twistMul_one`, `twistMul_mul`, `twistMul_add`, `twistMul_zero` after tensoring with `ℱ`.
* `Stacks.AlgebraicGeometry.ProjTwistSectionModule.smul_of`: the action of a homogeneous
  element of `S` on a homogeneous element of `M`.
* `Stacks.AlgebraicGeometry.ProjTwistSectionModule.existsUnique_hom_associatedTwistSectionSheaf`:
  comparison maps on the standard opens of the positive-degree homogeneous elements, compatible
  with restriction, glue to one and only one morphism `M̃ ⟶ ℱ`.

## Implementation notes

The summands are indexed by the natural numbers and the twists by the integers, so every degree
occurring in a twist is a cast `(d : ℕ) : ℤ`. Casts of `Int.ofNat` are definitionally additive,
which is why `twistMul` can be given a type whose target degree is `((e + d : ℕ) : ℤ)` while
being built from a morphism whose target degree is `(e : ℤ) + (d : ℤ)`. Degrees in `ℕ` are a
different matter — `0 + d` and `d` are not definitionally equal — so both `homogeneousMul` and
`gsmul` take their target degree as a *parameter* together with an equation pinning it down.
Every functoriality law then substitutes that equation, after which the two sides are
syntactically equal; this is what replaces a calculus of transports, and the unit and
associativity laws of `instGmodule`, which are equalities in `GradedMonoid`, are assembled from
`mk_eq` and `sectionCongr_gsmul` rather than from a cast.

The degree-preservation hypothesis of the associated-sheaf construction is a proposition, so
two of these morphisms with the same linear map are equal by proof irrelevance; that is
`twistSheafMap_congr`, out of which the unit and multiplicativity laws are read off the
corresponding laws of `mulLinearMap`.

Additivity is proved on pure tensors through the universal property of sheafification
(`Stacks.AlgebraicGeometry.ProjTwistTheta.tensorSheaf_hom_ext`) rather than from an additive
structure on the tensor product: the sheafified tensor product of this development carries no
`Additive` instance in either argument. The proofs are written as `Eq.trans` and `congrArg`
chains and not as rewrites: the three spellings of the tensor product that meet here agree only
definitionally, so a rewrite motive built at implicit transparency is not type-correct while
`exact` succeeds.

## What is not done

The *second* assertion of Tag 03GM, the canonical isomorphism `ℱ ≅ M̃` for `ℱ` quasi-coherent
on `ℙᵐ_R`, is not proved here. The sheaf `M̃` that the assertion compares with `ℱ` is
`associatedTwistSectionSheaf`, and `projectiveAssociatedTwistSectionSheaf` is its form on
`ℙᵐ_R`, so the statement can be written down.

Its local input is available. Writing a section of `M̃` over the standard chart `D₊(Tᵢ)` as a
fraction `m / Tᵢⁿ` and reading off the section `mᵢ` of `ℱ` with `m|_{D₊(Tᵢ)} = mᵢ ⊗ Tᵢⁿ` asks for
the map `Γ(W, ℱ) → Γ(W, ℱ(nd))`, `t ↦ t ⊗ (fⁿ)|_W`, to be *bijective* for an **arbitrary** sheaf
of modules `ℱ` on an open `W ⊆ D₊(f)` with `f` homogeneous of degree `d`, and that is
`Stacks.AlgebraicGeometry.ProjTwistRestriction.bijective_mulTrivSection`; that the section read
off does not depend on the fraction chosen is
`Stacks.AlgebraicGeometry.ProjTwistRestriction.eq_of_mulTrivSection_twistSheafScalarMap`,
whose multiplication on the twists is the one `twistMul` above is built from, by
`Stacks.AlgebraicGeometry.ProjTwistRestriction.homogeneousMul_eq_twistScalarSheafMap`.

The passage from the charts to `ℙᵐ_R` is *not* what is missing. Once the chart-by-chart maps are
in hand — as maps on the sections over the standard opens of the positive-degree homogeneous
elements, linear over the structure sheaf on each and compatible with restriction between them —
they assemble into one and only one morphism `M̃ ⟶ ℱ`, and that is
`existsUnique_hom_associatedTwistSectionSheaf` below. The rewriting of a fraction with
denominator a power of `Tᵢ` into one with denominator a power of `Tⱼ`, which the compatibility
asks for, is `ProjectiveSpectrum.exists_pow_eq_mul_of_basicOpen_le_degree`: it supplies the
scalar together with its degree, and needs no non-vanishing hypothesis.

The chart maps themselves are built in
`StacksFrontier/AlgebraicGeometry/TensorSectionNonvanishing/ProjTwistLocalComparison.lean`:
`Stacks.AlgebraicGeometry.ProjTwistLocalComparison.chartHom` is the comparison on `D₊(f)`,
`chartHom_restrict` its compatibility with restriction, and
`Stacks.AlgebraicGeometry.ProjTwistLocalComparison.comparison` the morphism `M̃ ⟶ ℱ` they glue
to. The linearity over `Γ(D₊(f), 𝒪)` is obtained there from the semilinearity of
`Stacks.SheafOfModules.degreeZeroLocalizationLiftOfDegree` over
`AlgebraicGeometry.Proj.awayToSection` and the surjectivity of that ring map,
`AlgebraicGeometry.ProjectiveSpectrum.Proj.surjective_awayToSection`.

What is missing is that the resulting morphism is an *isomorphism*, which is local bijectivity on
each chart; that is where quasi-coherence of `ℱ` enters, and it is the content of the omitted
injectivity and surjectivity arguments of the source. The shape in which it would be used is
`Stacks.AlgebraicGeometry.ProjQuasiCoherentRecovery.isIso_of_bijective_app_onBasis`, which
turns bijectivity on a basis into invertibility.

The action is the composite the source describes — the canonical map `𝒪(e) ⊗ ℱ(d) → ℱ(e+d)` of
Tag 03GJ, evaluated against the global section of `𝒪(e)` attached to `a` — but the identification
with `AlgebraicGeometry.ProjectiveSpectrum.Proj.twistSheafMultiplicationMap` is not proved here.
What is proved here is that the action built directly from multiplication on the twisting sheaves
satisfies the graded module laws, which is the assertion the tag makes.

**That identification is not blocked for want of a section formula.** Each structural
isomorphism of the sheafified tensor product has a section-level formula —
`Stacks.SheafOfModules.tensorSections_tensorMapAt`,
`tensorSections_leftUnitorAt`, `tensorSections_rightUnitorAt`, `tensorSections_braidingAt`,
`tensorSections_associatorAt` and `tensorSections_tensorProductIsoAt`, all in
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/TwistSectionRing.lean` — and Tag 03GJ's whole
composite *is* computed on a pure tensor of sections from them, by
`twistSheafMultiplicationMap_pureTensorSection` in
`StacksFrontier/AlgebraicGeometry/Constructions/ProjTwistSectionModule.lean`. The multiplication of
the twisting sheaves alone is computed pointwise there too, by
`Stacks.AlgebraicGeometry.ProjInvertibleLocus.twistMultiplicationMap_tmul`
(`StacksFrontier/AlgebraicGeometry/TwistTensor/Basic.lean`). What is absent is only the comparison
of the two composites, not any ingredient of either.

Equation 27.10.1.4, Tag 03GK, is the module structure of `⨁_{m ∈ ℤ} Γ(X, ℱ(m))` over the
section *ring* `⨁_{n ≥ 0} Γ(X, 𝒪_X(n))`. It is not needed here — the action built here is that of
`S` itself, obtained from `mulLinearMap` directly rather than by first mapping `S` to the section
ring — but it is formalized in the repository, as
`AlgebraicGeometry.ProjectiveSpectrum.Proj.twistedGlobalSectionsGmodule` and
`twistedGlobalSectionsModule` in
`StacksFrontier/AlgebraicGeometry/Constructions/ProjTwistSectionModule.lean`.

## References

* [Stacks Project, Tag 03GM](https://stacks.math.columbia.edu/tag/03GM)
* [Stacks Project, Tag 03GJ](https://stacks.math.columbia.edu/tag/03GJ)
* [Stacks Project, Tag 01MN](https://stacks.math.columbia.edu/tag/01MN)
-/
@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry DirectSum
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.AlgebraicGeometry.ProjSheafFunctoriality (associatedModuleSheafMap
  associatedModuleSheafMap_id associatedModuleSheafMap_comp)
open Stacks.AlgebraicGeometry.ProjStalkGlobalSections (associatedModuleSheafMap_app_apply)
open Stacks.SheafOfModules.TensorStalkRingedSpace (toTensorSheafSection
  tensorSheafMap_app_toTensorSheafSection)
open Stacks.AlgebraicGeometry.ProjTwistTheta (tensorSheaf_hom_ext)
open Stacks.AlgebraicGeometry.ProjTwistComparison (PositiveElem positiveBasicOpen
  existsUnique_hom_of_standardOpenHomData)
open scoped Stacks.GradedLocalization

namespace Stacks.AlgebraicGeometry.ProjTwistSectionModule

universe u w

attribute [local instance] ProjectiveSpectrum.isPrime
attribute [local implicit_reducible] TopCat.Sheaf sheafCompose
attribute [local instance_reducible] ProjectiveSpectrum.top

variable {S : Type u} {σ : Type w} [CommRing S] [SetLike σ S] [AddSubgroupClass σ S]
  (𝒮 : ℕ → σ) [GradedRing 𝒮]

/-! ### Multiplication by a ring element, as a linear endomorphism -/

/-- Multiplication by an element of a commutative ring, as a linear endomorphism of the regular
module. -/
def mulLinearMap (a : S) : S →ₗ[S] S where
  toFun x := a * x
  map_add' x y := mul_add a x y
  map_smul' c x := by
    change a * (c * x) = c * (a * x)
    ring

/-- Multiplication by `a` sends `x` to `a * x`. -/
@[simp] theorem mulLinearMap_apply (a x : S) : mulLinearMap a x = a * x := rfl

/-- Multiplication by `1` is the identity. -/
theorem mulLinearMap_one : mulLinearMap (1 : S) = LinearMap.id :=
  LinearMap.ext fun x => one_mul x

/-- Multiplication by `a * b` is the composite of multiplication by `b` and then by `a`. -/
theorem mulLinearMap_mul (a b : S) :
    mulLinearMap (a * b) = (mulLinearMap a).comp (mulLinearMap b) :=
  LinearMap.ext fun x => mul_assoc a b x

/-- Multiplication by `a + b` is the sum of multiplication by `a` and by `b`. -/
theorem mulLinearMap_add (a b : S) :
    mulLinearMap (a + b) = mulLinearMap a + mulLinearMap b :=
  LinearMap.ext fun x => add_mul a b x

/-- Multiplication by `0` is the zero map. -/
theorem mulLinearMap_zero : mulLinearMap (0 : S) = 0 :=
  LinearMap.ext fun x => zero_mul x

/-- Multiplication by a homogeneous element of degree `e` carries the degree-`i` piece of the
twist `S(d)` into the degree-`i` piece of the twist `S(e + d)`. -/
theorem mul_mem_twistGrading {e : ℕ} {a : S} (ha : a ∈ 𝒮 e) (d k : ℤ) (hk : k = (e : ℤ) + d) :
    ∀ (i : ℤ) (m : S), m ∈ twistGrading (S := S) 𝒮 d i →
      mulLinearMap a m ∈ twistGrading (S := S) 𝒮 k i := by
  subst hk
  intro i m hm
  simp only [twistGrading_apply, mulLinearMap_apply] at hm ⊢
  rcases lt_or_ge (i + d) 0 with h | h
  · rw [integerGrading_neg _ _ h] at hm
    rw [(Submodule.mem_bot ℤ).mp hm, mul_zero]
    exact zero_mem _
  · obtain ⟨j, hj⟩ : ∃ j : ℕ, (j : ℤ) = i + d := ⟨(i + d).toNat, by omega⟩
    rw [← hj, integerGrading_natCast, mem_homogeneousSubmodule] at hm
    have hmul : a * m ∈ 𝒮 (e + j) := SetLike.mul_mem_graded ha hm
    have hdeg : i + ((e : ℤ) + d) = ((e + j : ℕ) : ℤ) := by push_cast; omega
    rw [hdeg, integerGrading_natCast, mem_homogeneousSubmodule]
    exact hmul

/-! ### Multiplication on the twisting sheaves -/

/-- **Multiplication by a homogeneous element of degree `e`, as a morphism of twisting
sheaves** `𝒪_X(d) ⟶ 𝒪_X(e + d)` on `X = Proj 𝒮`: in every fibre it multiplies the local
fraction by `a`. The target degree is a parameter, pinned down by `hk`. -/
def homogeneousMul {e : ℕ} {a : S} (ha : a ∈ 𝒮 e) (d k : ℤ) (hk : k = (e : ℤ) + d) :
    twistingSheaf 𝒮 d ⟶ twistingSheaf 𝒮 k :=
  associatedModuleSheafMap 𝒮 (twistGrading (S := S) 𝒮 d) (twistGrading (S := S) 𝒮 k)
    (mulLinearMap a) (mul_mem_twistGrading 𝒮 ha d k hk)

/-- Two morphisms of associated sheaves induced by equal degree-preserving maps of the twists
agree: the degree-preservation hypothesis is a proposition, so it does not enter the
morphism. -/
theorem twistSheafMap_congr (d k : ℤ) (φ ψ : S →ₗ[S] S)
    (hφ : ∀ (i : ℤ) (m : S), m ∈ twistGrading (S := S) 𝒮 d i →
      φ m ∈ twistGrading (S := S) 𝒮 k i)
    (hψ : ∀ (i : ℤ) (m : S), m ∈ twistGrading (S := S) 𝒮 d i →
      ψ m ∈ twistGrading (S := S) 𝒮 k i)
    (h : φ = ψ) :
    associatedModuleSheafMap 𝒮 (twistGrading (S := S) 𝒮 d) (twistGrading (S := S) 𝒮 k) φ hφ =
      associatedModuleSheafMap 𝒮 (twistGrading (S := S) 𝒮 d) (twistGrading (S := S) 𝒮 k) ψ hψ := by
  subst h
  rfl

/-- Multiplication morphisms built from equal ring elements agree. -/
theorem homogeneousMul_congr {e f : ℕ} {a b : S} (ha : a ∈ 𝒮 e) (hb : b ∈ 𝒮 f)
    (d k : ℤ) (hk : k = (e : ℤ) + d) (hk' : k = (f : ℤ) + d) (hab : a = b) :
    homogeneousMul 𝒮 ha d k hk = homogeneousMul 𝒮 hb d k hk' := by
  subst hab
  rfl

/-- Multiplication by `1` is the identity morphism of the twisting sheaf. -/
theorem homogeneousMul_one (d : ℤ) (hk : d = ((0 : ℕ) : ℤ) + d) :
    homogeneousMul 𝒮 (SetLike.GradedOne.one_mem (A := 𝒮)) d d hk = 𝟙 (twistingSheaf 𝒮 d) :=
  (twistSheafMap_congr 𝒮 d d _ LinearMap.id _
      (fun _ _ hm => hm) mulLinearMap_one).trans
    (associatedModuleSheafMap_id 𝒮 (twistGrading (S := S) 𝒮 d))

/-- Multiplication by a product is the composite of the two multiplications. -/
theorem homogeneousMul_mul {e f : ℕ} {a b : S} (ha : a ∈ 𝒮 e) (hb : b ∈ 𝒮 f)
    (hab : a * b ∈ 𝒮 (e + f)) (d k l : ℤ) (hk : k = (f : ℤ) + d) (hl : l = (e : ℤ) + k)
    (hl' : l = ((e + f : ℕ) : ℤ) + d) :
    homogeneousMul 𝒮 hab d l hl' =
      homogeneousMul 𝒮 hb d k hk ≫ homogeneousMul 𝒮 ha k l hl :=
  (twistSheafMap_congr 𝒮 d l _ ((mulLinearMap a).comp (mulLinearMap b)) _
      (fun i m hm => mul_mem_twistGrading 𝒮 ha k l hl i _
        (mul_mem_twistGrading 𝒮 hb d k hk i m hm))
      (mulLinearMap_mul a b)).trans
    (associatedModuleSheafMap_comp 𝒮 (twistGrading (S := S) 𝒮 d) (twistGrading (S := S) 𝒮 k)
      (twistGrading (S := S) 𝒮 l) (mulLinearMap b) (mul_mem_twistGrading 𝒮 hb d k hk)
      (mulLinearMap a) (mul_mem_twistGrading 𝒮 ha k l hl))

/-- Multiplication by a sum of two homogeneous elements of the same degree is, on sections, the
sum of the two multiplications. -/
theorem homogeneousMul_add_app {e : ℕ} {a b : S} (ha : a ∈ 𝒮 e) (hb : b ∈ 𝒮 e)
    (hab : a + b ∈ 𝒮 e) (d k : ℤ) (hk : k = (e : ℤ) + d)
    (U : Opens (ProjectiveSpectrum.top 𝒮)) (s : (twistingSheaf 𝒮 d).val.obj (op U)) :
    ((homogeneousMul 𝒮 hab d k hk).val.app (op U)).hom s =
      ((homogeneousMul 𝒮 ha d k hk).val.app (op U)).hom s +
        ((homogeneousMul 𝒮 hb d k hk).val.app (op U)).hom s := by
  apply Subtype.ext
  funext x
  change (LocalizedModule.map _ (mulLinearMap (a + b))) (s.1 x) =
    (LocalizedModule.map _ (mulLinearMap a)) (s.1 x) +
      (LocalizedModule.map _ (mulLinearMap b)) (s.1 x)
  rw [mulLinearMap_add, map_add, LinearMap.add_apply]

/-- Multiplication by `0` is, on sections, the zero map. -/
theorem homogeneousMul_zero_app {e : ℕ} (h0 : (0 : S) ∈ 𝒮 e) (d k : ℤ) (hk : k = (e : ℤ) + d)
    (U : Opens (ProjectiveSpectrum.top 𝒮)) (s : (twistingSheaf 𝒮 d).val.obj (op U)) :
    ((homogeneousMul 𝒮 h0 d k hk).val.app (op U)).hom s = 0 := by
  apply Subtype.ext
  funext x
  change (LocalizedModule.map _ (mulLinearMap (0 : S))) (s.1 x) = 0
  rw [mulLinearMap_zero, map_zero, LinearMap.zero_apply]

/-! ### Multiplication on the twists of a sheaf of modules -/

variable (F : SheafOfModules.{u}
  ((sheafCompose (Opens.grothendieckTopology (ProjectiveSpectrum.top 𝒮))
    (forget₂ CommRingCat.{u} RingCat.{u})).obj (ProjectiveSpectrum.Proj.structureSheaf 𝒮)))

/-- **Multiplication by a homogeneous element of degree `e` on the twists of `ℱ`**, as a
morphism `ℱ(d) ⟶ ℱ(e + d)`: the multiplication morphism of the twisting sheaves, tensored
with `ℱ`. -/
def twistMul {e : ℕ} {a : S} (ha : a ∈ 𝒮 e) (d j : ℕ) (hj : j = e + d) :
    twistSheafOfModules 𝒮 F (d : ℤ) ⟶ twistSheafOfModules 𝒮 F (j : ℤ) :=
  ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
    (ProjectiveSpectrum.Proj.structureSheaf 𝒮)).obj F).map
      (homogeneousMul 𝒮 ha (d : ℤ) (j : ℤ) (by rw [hj]; push_cast; ring))

/-- The canonical map from the sections of the presheaf tensor product is additive. -/
theorem toTensorSheafSection_add
    (G H : SheafOfModules.{u}
      (structureSheafRing
        (AlgebraicGeometry.Proj 𝒮).toRingedSpace))
    (U : (Opens (AlgebraicGeometry.Proj 𝒮).toRingedSpace.carrier)ᵒᵖ)
    (t t' : TensorProduct ((AlgebraicGeometry.Proj 𝒮).toRingedSpace.presheaf.obj U)
      (G.val.obj U) (H.val.obj U)) :
    toTensorSheafSection (AlgebraicGeometry.Proj 𝒮).toRingedSpace G H U (t + t') =
      toTensorSheafSection (AlgebraicGeometry.Proj 𝒮).toRingedSpace G H U t +
        toTensorSheafSection (AlgebraicGeometry.Proj 𝒮).toRingedSpace G H U t' :=
  map_add _ t t'

/-- Multiplication by `1` is the identity morphism of the twist. -/
theorem twistMul_one (d : ℕ) (hj : d = 0 + d) :
    twistMul 𝒮 F (SetLike.GradedOne.one_mem (A := 𝒮)) d d hj = 𝟙 _ := by
  refine Eq.trans (congrArg
    (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        (ProjectiveSpectrum.Proj.structureSheaf 𝒮)).obj F).map
      (X := twistingSheaf 𝒮 (d : ℤ)) (Y := twistingSheaf 𝒮 (d : ℤ)))
    (homogeneousMul_one 𝒮 (d : ℤ) ?_)) ?_
  · push_cast
    ring
  · exact ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      (ProjectiveSpectrum.Proj.structureSheaf 𝒮)).obj F).map_id (twistingSheaf 𝒮 (d : ℤ))

/-- Multiplication by a product is the composite of the two multiplications. -/
theorem twistMul_mul {e f : ℕ} {a b : S} (ha : a ∈ 𝒮 e) (hb : b ∈ 𝒮 f)
    (hab : a * b ∈ 𝒮 (e + f)) (d j l : ℕ) (hj : j = f + d) (hl : l = e + j)
    (hl' : l = e + f + d) :
    twistMul 𝒮 F hab d l hl' = twistMul 𝒮 F hb d j hj ≫ twistMul 𝒮 F ha j l hl := by
  refine Eq.trans (congrArg
    (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        (ProjectiveSpectrum.Proj.structureSheaf 𝒮)).obj F).map
      (X := twistingSheaf 𝒮 (d : ℤ)) (Y := twistingSheaf 𝒮 (l : ℤ)))
    (homogeneousMul_mul 𝒮 ha hb hab (d : ℤ) (j : ℤ) (l : ℤ) ?_ ?_ ?_)) ?_
  · rw [hj]; push_cast; ring
  · rw [hl]; push_cast; ring
  · rw [hl']; push_cast; ring
  · exact ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      (ProjectiveSpectrum.Proj.structureSheaf 𝒮)).obj F).map_comp
      (homogeneousMul 𝒮 hb (d : ℤ) (j : ℤ) (by rw [hj]; push_cast; ring))
      (homogeneousMul 𝒮 ha (j : ℤ) (l : ℤ) (by rw [hl]; push_cast; ring))

/-- Tensoring with `ℱ` is an additive functor on sheaves of modules over the structure sheaf. -/
private theorem sheafTensor_obj_additive_structureSheaf :
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      (ProjectiveSpectrum.Proj.structureSheaf 𝒮)).obj F).Additive :=
  have : CategoryTheory.Limits.HasBinaryBiproducts (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (ProjectiveSpectrum.Proj.structureSheaf 𝒮))) :=
    CategoryTheory.Limits.HasBinaryBiproducts.of_hasBinaryProducts
  Stacks.SheafOfModules.Tensor.sheafTensor_obj_additive
    (ProjectiveSpectrum.Proj.structureSheaf 𝒮) F

/-- Multiplication by a sum of two homogeneous elements of the same degree is the sum of the
two multiplications. -/
theorem twistMul_add {e : ℕ} {a b : S} (ha : a ∈ 𝒮 e) (hb : b ∈ 𝒮 e) (hab : a + b ∈ 𝒮 e)
    (d j : ℕ) (hj : j = e + d) :
    twistMul 𝒮 F hab d j hj = twistMul 𝒮 F ha d j hj + twistMul 𝒮 F hb d j hj := by
  have hk : (j : ℤ) = (e : ℤ) + (d : ℤ) := by rw [hj]; push_cast; ring
  have hadd : homogeneousMul 𝒮 hab (d : ℤ) (j : ℤ) hk =
      homogeneousMul 𝒮 ha (d : ℤ) (j : ℤ) hk + homogeneousMul 𝒮 hb (d : ℤ) (j : ℤ) hk :=
    SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun U =>
      ModuleCat.hom_ext (LinearMap.ext fun s =>
        homogeneousMul_add_app 𝒮 ha hb hab (d : ℤ) (j : ℤ) hk U.unop s))
  have := sheafTensor_obj_additive_structureSheaf 𝒮 F
  exact (congrArg
    (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        (ProjectiveSpectrum.Proj.structureSheaf 𝒮)).obj F).map
      (X := twistingSheaf 𝒮 (d : ℤ)) (Y := twistingSheaf 𝒮 (j : ℤ))) hadd).trans
    (Functor.map_add _)

/-- Multiplication by `0` is the zero morphism. -/
theorem twistMul_zero {e : ℕ} (h0 : (0 : S) ∈ 𝒮 e) (d j : ℕ) (hj : j = e + d) :
    twistMul 𝒮 F h0 d j hj = 0 := by
  have hk : (j : ℤ) = (e : ℤ) + (d : ℤ) := by rw [hj]; push_cast; ring
  have hz : homogeneousMul 𝒮 h0 (d : ℤ) (j : ℤ) hk = 0 :=
    SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun U =>
      ModuleCat.hom_ext (LinearMap.ext fun s =>
        homogeneousMul_zero_app 𝒮 h0 (d : ℤ) (j : ℤ) hk U.unop s))
  have := sheafTensor_obj_additive_structureSheaf 𝒮 F
  exact (congrArg
    (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        (ProjectiveSpectrum.Proj.structureSheaf 𝒮)).obj F).map
      (X := twistingSheaf 𝒮 (d : ℤ)) (Y := twistingSheaf 𝒮 (j : ℤ))) hz).trans
    (Functor.map_zero _ _ _)

/-! ### The action on global sections -/

/-- **The degree-`d` piece of the graded module**: the global sections `Γ(X, ℱ(d))` of the
`d`-th twist of `ℱ`. -/
abbrev twistSections (d : ℕ) : Type u := (twistSheafOfModules 𝒮 F (d : ℤ)).val.obj (op ⊤)

/-- Reindexing a twisted global section along an equality of degrees. -/
def sectionCongr {d j : ℕ} (h : d = j) (s : twistSections 𝒮 F d) : twistSections 𝒮 F j := h ▸ s

/-- A reindexed section is the original one, as an element of the sigma type that
`GradedMonoid` uses for the unit and associativity laws. -/
theorem mk_eq {d j : ℕ} (h : d = j) (s : twistSections 𝒮 F d) :
    (⟨d, s⟩ : GradedMonoid (twistSections 𝒮 F)) = ⟨j, sectionCongr 𝒮 F h s⟩ := by
  subst h
  rfl

/-- **The action of a homogeneous element of degree `e` on `Γ(X, ℱ(d))`**, landing in
`Γ(X, ℱ(e + d))`: the effect on global sections of multiplication by that element. -/
def gsmul {e : ℕ} {a : S} (ha : a ∈ 𝒮 e) (d j : ℕ) (hj : j = e + d)
    (s : twistSections 𝒮 F d) : twistSections 𝒮 F j :=
  ((twistMul 𝒮 F ha d j hj).val.app (op ⊤)).hom s

/-- The action does not depend on which of two equal target degrees is used. -/
theorem sectionCongr_gsmul {e : ℕ} {a : S} (ha : a ∈ 𝒮 e) (d j j' : ℕ) (hj : j = e + d)
    (hj' : j' = e + d) (h : j = j') (s : twistSections 𝒮 F d) :
    sectionCongr 𝒮 F h (gsmul 𝒮 F ha d j hj s) = gsmul 𝒮 F ha d j' hj' s := by
  subst h
  rfl

/-- Equal morphisms of twists have equal effect on global sections. -/
private theorem app_top_hom_congr {d j : ℕ}
    {α β : twistSheafOfModules 𝒮 F (d : ℤ) ⟶ twistSheafOfModules 𝒮 F (j : ℤ)} (h : α = β)
    (s : twistSections 𝒮 F d) : (α.val.app (op ⊤)).hom s = (β.val.app (op ⊤)).hom s :=
  congrArg (fun α => (α.val.app (op ⊤)).hom s) h

/-- `1` acts as the identity. -/
theorem gsmul_one (d : ℕ) (hj : d = 0 + d) (s : twistSections 𝒮 F d) :
    gsmul 𝒮 F (SetLike.GradedOne.one_mem (A := 𝒮)) d d hj s = s :=
  app_top_hom_congr 𝒮 F (twistMul_one 𝒮 F d hj) s

/-- Acting by a product is acting twice. -/
theorem gsmul_mul {e f : ℕ} {a b : S} (ha : a ∈ 𝒮 e) (hb : b ∈ 𝒮 f) (hab : a * b ∈ 𝒮 (e + f))
    (d j l : ℕ) (hj : j = f + d) (hl : l = e + j) (hl' : l = e + f + d)
    (s : twistSections 𝒮 F d) :
    gsmul 𝒮 F hab d l hl' s = gsmul 𝒮 F ha j l hl (gsmul 𝒮 F hb d j hj s) :=
  app_top_hom_congr 𝒮 F (twistMul_mul 𝒮 F ha hb hab d j l hj hl hl') s

/-- The action is additive in the scalar. -/
theorem gsmul_add_left {e : ℕ} {a b : S} (ha : a ∈ 𝒮 e) (hb : b ∈ 𝒮 e) (hab : a + b ∈ 𝒮 e)
    (d j : ℕ) (hj : j = e + d) (s : twistSections 𝒮 F d) :
    gsmul 𝒮 F hab d j hj s = gsmul 𝒮 F ha d j hj s + gsmul 𝒮 F hb d j hj s :=
  app_top_hom_congr 𝒮 F (twistMul_add 𝒮 F ha hb hab d j hj) s

/-- The zero scalar annihilates every section. -/
theorem gsmul_zero_left {e : ℕ} (h0 : (0 : S) ∈ 𝒮 e) (d j : ℕ) (hj : j = e + d)
    (s : twistSections 𝒮 F d) : gsmul 𝒮 F h0 d j hj s = 0 :=
  app_top_hom_congr 𝒮 F (twistMul_zero 𝒮 F h0 d j hj) s

/-- The action is additive in the section. -/
theorem gsmul_add_right {e : ℕ} {a : S} (ha : a ∈ 𝒮 e) (d j : ℕ) (hj : j = e + d)
    (s t : twistSections 𝒮 F d) :
    gsmul 𝒮 F ha d j hj (s + t) = gsmul 𝒮 F ha d j hj s + gsmul 𝒮 F ha d j hj t :=
  map_add _ s t

/-- The action sends the zero section to the zero section. -/
theorem gsmul_zero_right {e : ℕ} {a : S} (ha : a ∈ 𝒮 e) (d j : ℕ) (hj : j = e + d) :
    gsmul 𝒮 F ha d j hj (0 : twistSections 𝒮 F d) = 0 :=
  map_zero _

/-! ### The graded module -/

/-- The homogeneous pieces of `S`, as a family of types. -/
abbrev gradedPieces : ℕ → Type u := fun e => 𝒮 e

/-- The homogeneous action, in the form that `DirectSum.Gmodule` asks for. -/
instance instGSMul : GradedMonoid.GSMul (gradedPieces 𝒮) (twistSections 𝒮 F) where
  smul {e d} a s := gsmul 𝒮 F a.2 d (e + d) rfl s

/-- The graded scalar multiplication of `a` of degree `e` on `s ∈ Γ(X, ℱ(d))` is `gsmul`, landing
in `Γ(X, ℱ(e + d))`. -/
theorem gSMul_def {e d : ℕ} (a : gradedPieces 𝒮 e) (s : twistSections 𝒮 F d) :
    GradedMonoid.GSMul.smul (A := gradedPieces 𝒮) (M := twistSections 𝒮 F) a s =
      gsmul 𝒮 F a.2 d (e + d) rfl s := rfl

/-- **The twisted global sections form a graded module over `S`**: the family
`d ↦ Γ(X, ℱ(d))` is a graded module over the family of homogeneous pieces of `S`, acted on by
the multiplication maps of the twists. -/
@[ega "II 8.14.5" "affine base, Γ_* module"]
instance instGmodule :
    DirectSum.Gmodule (gradedPieces 𝒮) (twistSections 𝒮 F) where
  one_smul b := by
    obtain ⟨d, s⟩ := b
    have h : d = 0 + d := (Nat.zero_add d).symm
    have hg : gsmul 𝒮 F (SetLike.GradedOne.one_mem (A := 𝒮)) d (0 + d) rfl s =
        sectionCongr 𝒮 F h s := by
      refine Eq.trans ?_ (congrArg (sectionCongr 𝒮 F h) (gsmul_one 𝒮 F d h s))
      exact (sectionCongr_gsmul 𝒮 F (SetLike.GradedOne.one_mem (A := 𝒮)) d d (0 + d)
        h rfl h s).symm
    refine Eq.trans (congrArg (fun t => (⟨0 + d, t⟩ : GradedMonoid (twistSections 𝒮 F))) hg) ?_
    exact (mk_eq 𝒮 F h s).symm
  mul_smul a a' b := by
    obtain ⟨e, x⟩ := a
    obtain ⟨f, y⟩ := a'
    obtain ⟨d, s⟩ := b
    have hab : (x : S) * (y : S) ∈ 𝒮 (e + f) := SetLike.mul_mem_graded x.2 y.2
    have h : e + f + d = e + (f + d) := Nat.add_assoc e f d
    have hl' : e + (f + d) = e + f + d := h.symm
    refine Eq.trans (mk_eq 𝒮 F h (gsmul 𝒮 F hab d (e + f + d) rfl s)) ?_
    refine congrArg (fun t => (⟨e + (f + d), t⟩ : GradedMonoid (twistSections 𝒮 F))) ?_
    refine Eq.trans (sectionCongr_gsmul 𝒮 F hab d (e + f + d) (e + (f + d)) rfl hl' h s) ?_
    exact gsmul_mul 𝒮 F x.2 y.2 hab d (f + d) (e + (f + d)) rfl rfl hl' s
  smul_add a s t := gsmul_add_right 𝒮 F a.2 _ _ rfl s t
  smul_zero a := gsmul_zero_right 𝒮 F a.2 _ _ rfl
  add_smul a a' s := gsmul_add_left 𝒮 F a.2 a'.2 (add_mem a.2 a'.2) _ _ rfl s
  zero_smul s := gsmul_zero_left 𝒮 F (zero_mem _) _ _ rfl s

/-- **The graded module of twisted global sections** `⨁_{d ≥ 0} Γ(X, ℱ(d))`. -/
abbrev twistSectionModule : Type u := ⨁ d : ℕ, twistSections 𝒮 F d

/-- The module structure of `⨁_{d ≥ 0} Γ(X, ℱ(d))` over the direct sum of the homogeneous pieces
of `S`. -/
instance instModuleDirectSum : Module (⨁ e : ℕ, gradedPieces 𝒮 e) (twistSectionModule 𝒮 F) :=
  DirectSum.Gmodule.module (gradedPieces 𝒮) (twistSections 𝒮 F)

/-- **The twisted global sections are a module over the graded ring `S`.** -/
instance instModule : Module S (twistSectionModule 𝒮 F) :=
  Module.compHom (M := twistSectionModule 𝒮 F) (DirectSum.decomposeRingEquiv 𝒮).toRingHom

/-- A homogeneous element of degree `e` acts on the summand of degree `d` through `gsmul`, landing
in the summand of degree `e + d`. -/
theorem of_smul_of {e d : ℕ} (a : gradedPieces 𝒮 e) (s : twistSections 𝒮 F d) :
    DirectSum.of (gradedPieces 𝒮) e a • DirectSum.of (twistSections 𝒮 F) d s =
      DirectSum.of (twistSections 𝒮 F) (e + d) (gsmul 𝒮 F a.2 d (e + d) rfl s) :=
  DirectSum.Gmodule.of_smul_of (gradedPieces 𝒮) (twistSections 𝒮 F) a s

/-- **The action of a homogeneous element of `S` on a homogeneous element of `M`.** -/
theorem smul_of {e d : ℕ} (a : gradedPieces 𝒮 e) (s : twistSections 𝒮 F d) :
    (a : S) • DirectSum.of (twistSections 𝒮 F) d s =
      DirectSum.of (twistSections 𝒮 F) (e + d) (gsmul 𝒮 F a.2 d (e + d) rfl s) := by
  refine Eq.trans ?_ (of_smul_of 𝒮 F a s)
  exact congrArg (fun r : ⨁ e : ℕ, gradedPieces 𝒮 e =>
    r • DirectSum.of (twistSections 𝒮 F) d s) (DirectSum.decompose_coe 𝒮 a)

/-! ### The integer grading -/

/-- **The grading of the twisted global sections by the integers**: the `d`-th summand in
degree `d ≥ 0`, and the trivial subgroup in negative degrees. -/
def moduleGrading : ℤ → AddSubgroup (twistSectionModule 𝒮 F)
  | .ofNat d => Stacks.ExternalGrading.summand (twistSections 𝒮 F) d
  | .negSucc _ => ⊥

/-- In a degree `d ≥ 0` the graded piece is the `d`-th summand. -/
theorem moduleGrading_natCast (d : ℕ) :
    moduleGrading 𝒮 F (d : ℤ) = Stacks.ExternalGrading.summand (twistSections 𝒮 F) d := rfl

/-- In a negative degree the graded piece is trivial. -/
theorem moduleGrading_negSucc (k : ℕ) : moduleGrading 𝒮 F (Int.negSucc k) = ⊥ := rfl

/-- A twisted global section of degree `d`, as an element of the degree-`d` graded piece. -/
def embedZ (d : ℕ) : twistSections 𝒮 F d →+ moduleGrading 𝒮 F (d : ℤ) where
  toFun s := ⟨DirectSum.of (twistSections 𝒮 F) d s, ⟨s, rfl⟩⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' s t := Subtype.ext (map_add _ s t)

/-- The image of `s` under `embedZ` is `s` in the degree-`d` summand. -/
@[simp] theorem embedZ_coe (d : ℕ) (s : twistSections 𝒮 F d) :
    ((embedZ 𝒮 F d s : moduleGrading 𝒮 F (d : ℤ)) : twistSectionModule 𝒮 F) =
      DirectSum.of (twistSections 𝒮 F) d s := rfl

/-- The componentwise decomposition into integer-graded pieces. -/
def decomposeZ : twistSectionModule 𝒮 F →+ ⨁ z : ℤ, moduleGrading 𝒮 F z :=
  DirectSum.toAddMonoid fun d =>
    (DirectSum.of (fun z : ℤ => (moduleGrading 𝒮 F z : Type u)) (d : ℤ)).comp (embedZ 𝒮 F d)

/-- The decomposition sends `s` in the degree-`d` summand to `embedZ s` in degree `(d : ℤ)`. -/
@[simp] theorem decomposeZ_of (d : ℕ) (s : twistSections 𝒮 F d) :
    decomposeZ 𝒮 F (DirectSum.of (twistSections 𝒮 F) d s) =
      DirectSum.of (fun z : ℤ => (moduleGrading 𝒮 F z : Type u)) (d : ℤ) (embedZ 𝒮 F d s) :=
  DirectSum.toAddMonoid_of _ _ _

/-- **The integer-graded pieces decompose the twisted global sections.** -/
instance instDecomposition : DirectSum.Decomposition (moduleGrading 𝒮 F) where
  decompose' := decomposeZ 𝒮 F
  left_inv x := by
    induction x using DirectSum.induction_on with
    | zero =>
        exact (congrArg (DirectSum.coeAddMonoidHom (moduleGrading 𝒮 F))
          (map_zero (decomposeZ 𝒮 F))).trans (map_zero _)
    | of d s =>
        refine Eq.trans (congrArg (DirectSum.coeAddMonoidHom (moduleGrading 𝒮 F))
          (decomposeZ_of 𝒮 F d s)) ?_
        exact (DirectSum.coeAddMonoidHom_of (moduleGrading 𝒮 F) (d : ℤ)
          (embedZ 𝒮 F d s)).trans (embedZ_coe 𝒮 F d s)
    | add x y hx hy =>
        exact ((congrArg (DirectSum.coeAddMonoidHom (moduleGrading 𝒮 F))
          (map_add (decomposeZ 𝒮 F) x y)).trans (map_add _ _ _)).trans
            (congrArg₂ (· + ·) hx hy)
  right_inv x := by
    induction x using DirectSum.induction_on with
    | zero => exact (congrArg (decomposeZ 𝒮 F) (map_zero _)).trans (map_zero _)
    | of z w =>
        refine Eq.trans (congrArg (decomposeZ 𝒮 F)
          (DirectSum.coeAddMonoidHom_of (moduleGrading 𝒮 F) z w)) ?_
        obtain ⟨d⟩ | ⟨k⟩ := z
        · obtain ⟨s, hs⟩ := w.2
          refine Eq.trans (congrArg (decomposeZ 𝒮 F) hs.symm) ?_
          refine Eq.trans (decomposeZ_of 𝒮 F d s) ?_
          exact congrArg (DirectSum.of (fun z : ℤ => (moduleGrading 𝒮 F z : Type u)) (d : ℤ))
            (Subtype.ext hs)
        · have hw : (w : twistSectionModule 𝒮 F) = 0 := AddSubgroup.mem_bot.mp w.2
          refine Eq.trans (congrArg (decomposeZ 𝒮 F) hw) ?_
          refine Eq.trans (map_zero (decomposeZ 𝒮 F)) ?_
          exact (map_zero (DirectSum.of (fun z : ℤ => (moduleGrading 𝒮 F z : Type u))
            (Int.negSucc k))).symm.trans (congrArg _ (Subtype.ext hw).symm)
    | add x y hx hy =>
        exact ((congrArg (decomposeZ 𝒮 F) (map_add _ x y)).trans (map_add _ _ _)).trans
          (congrArg₂ (· + ·) hx hy)

/-- **The grading of `S` acts on the grading of the twisted global sections**, at the action
`e +ᵥ z = e + z` of `ℕ` on `ℤ`. -/
instance instGradedSMul : SetLike.GradedSMul 𝒮 (moduleGrading 𝒮 F) where
  smul_mem := by
    intro e z a w ha hw
    obtain ⟨d⟩ | ⟨k⟩ := z
    · obtain ⟨s, rfl⟩ := hw
      refine Eq.mpr (congrArg (· ∈ moduleGrading 𝒮 F ((e : ℤ) + (d : ℤ)))
        (smul_of 𝒮 F ⟨a, ha⟩ s)) ?_
      exact ⟨gsmul 𝒮 F ha d (e + d) rfl s, rfl⟩
    · have hw0 : w = 0 := AddSubgroup.mem_bot.mp hw
      exact Eq.mpr (congrArg (· ∈ moduleGrading 𝒮 F ((e : ℤ) +ᵥ Int.negSucc k))
        ((congrArg (fun z => (a : S) • z) hw0).trans (smul_zero (a : S)))) (zero_mem _)

/-- **The sheaf `M̃` on `Proj 𝒮` associated to the graded module of twisted global sections.**
This is the sheaf that the second assertion of Tag 03GM compares with `ℱ`. -/
def associatedTwistSectionSheaf : SheafOfModules.{u}
    ((sheafCompose (Opens.grothendieckTopology (ProjectiveSpectrum.top 𝒮))
      (forget₂ CommRingCat.{u} RingCat.{u})).obj (ProjectiveSpectrum.Proj.structureSheaf 𝒮)) :=
  associatedModuleSheaf 𝒮 (moduleGrading 𝒮 F)

/-- **A morphism `M̃ ⟶ ℱ` glued from comparison maps on the standard opens, and its
uniqueness.** The second assertion of Tag 03GM compares `ℱ` with `M̃`, and this is the
globalization step of that comparison: a family `θ` of maps on the sections of `M̃` over the
standard opens `D₊(f)` of the positive-degree homogeneous elements, compatible with the
restriction maps between those opens, extends to one and only one morphism `M̃ ⟶ ℱ`.

No `stacks` attribute: the local maps `θ` are binders here, so this is the gluing principle for
the sheaf associated to an arbitrary graded module rather than the tag. Tag 03GM in full,
including that the canonical comparison is an *isomorphism*, is
`Stacks.AlgebraicGeometry.ProjTwistComparisonIso.gradedModule_and_isIso_comparison`. -/
theorem existsUnique_hom_associatedTwistSectionSheaf
    (θ : ∀ p : PositiveElem 𝒮,
      (associatedTwistSectionSheaf 𝒮 F).val.obj (op (positiveBasicOpen 𝒮 p)) ⟶
        F.val.obj (op (positiveBasicOpen 𝒮 p)))
    (hθ : ∀ (p q : PositiveElem 𝒮) (h : positiveBasicOpen 𝒮 q ≤ positiveBasicOpen 𝒮 p)
        (s : (associatedTwistSectionSheaf 𝒮 F).val.obj (op (positiveBasicOpen 𝒮 p))),
      θ q ((associatedTwistSectionSheaf 𝒮 F).val.map (homOfLE h).op s) =
        F.val.map (homOfLE h).op (θ p s)) :
    ∃! φ : associatedTwistSectionSheaf 𝒮 F ⟶ F,
      ∀ p : PositiveElem 𝒮, φ.val.app (op (positiveBasicOpen 𝒮 p)) = θ p :=
  existsUnique_hom_of_standardOpenHomData 𝒮 (moduleGrading 𝒮 F) F
    { app := θ, app_restrict := hθ }

/-! ### Projective space over a ring -/

section ProjectiveSpace

attribute [local instance] MvPolynomial.gradedAlgebra

variable (m : ℕ) (R : Type u) [CommRing R]

/-- The grading of `R[T₀, …, Tₘ]` by total degree; its homogeneous spectrum is `ℙᵐ_R`. -/
abbrev projectiveGrading : ℕ → Submodule R (MvPolynomial (Fin (m + 1)) R) :=
  MvPolynomial.homogeneousSubmodule (Fin (m + 1)) R

variable (G : SheafOfModules.{u}
  ((sheafCompose (Opens.grothendieckTopology (ProjectiveSpectrum.top (projectiveGrading m R)))
    (forget₂ CommRingCat.{u} RingCat.{u})).obj
      (ProjectiveSpectrum.Proj.structureSheaf (projectiveGrading m R))))

/-- **The graded `R[T₀, …, Tₘ]`-module `M = ⨁_{d ≥ 0} Γ(ℙᵐ_R, ℱ(d))` of Tag 03GM.** -/
abbrev projectiveTwistSectionModule : Type u := twistSectionModule (projectiveGrading m R) G

/-- **The sheaf `M̃` on `ℙᵐ_R` associated to the graded module of Tag 03GM.** -/
def projectiveAssociatedTwistSectionSheaf : SheafOfModules.{u}
    ((sheafCompose (Opens.grothendieckTopology (ProjectiveSpectrum.top (projectiveGrading m R)))
      (forget₂ CommRingCat.{u} RingCat.{u})).obj
        (ProjectiveSpectrum.Proj.structureSheaf (projectiveGrading m R))) :=
  associatedTwistSectionSheaf (projectiveGrading m R) G

end ProjectiveSpace

end Stacks.AlgebraicGeometry.ProjTwistSectionModule

end


