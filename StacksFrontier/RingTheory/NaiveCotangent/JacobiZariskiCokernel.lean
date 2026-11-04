module

public import StacksFrontier.RingTheory.NaiveCotangent.CompositionNullHomotopy
public import StacksFrontier.RingTheory.NaiveCotangent.JacobiZariskiPresentations
public import StacksFrontier.RingTheory.NaiveCotangent.SelfPresentationCotangentSpace

/-!
# The homotopy of Stacks 07VC induces an isomorphism onto a cokernel

Let `A ⟶ B ⟶ C` be ring maps and write `P = A[B] ⟶ B`, `N = A[C] ⟶ C` and `Q = B[C] ⟶ C` for
the three canonical presentations of Stacks 07BL, with conormal modules `I/I²`, `K/K²` and
`J/J²`.  The comparison `g : NL(N) ⟶ NL(Q)` is an isomorphism in degree `0` — both terms are
free on the variables indexed by `C`, which `g` fixes — so `H⁰` of the shifted cone of `g` is
the cokernel of `g` in degree `-1`, that is of

`K/K² ⟶ J/J²`.

This file proves that the homotopy of Stacks 07VC, `NaiveCotangent.towerNullHomotopy`, which
sends the basis element `d[b]` of `NL(P)^0` to the class of `[φ(b)] - b` in `J/J²`, induces an
**isomorphism**

`H₀(NL(P) ⊗_B C) ≅ (J/J²) / im (K/K² ⟶ J/J²)`.

That is the whole of the remaining input to the six-term exact sequence of Stacks 0E1Y: read at
a stalk it says that the canonical map `c` of that tag is an isomorphism on `H⁰`, which is what
produces the connecting map of the sequence.

## The argument

Write `h` for the base-changed homotopy `C ⊗_B NL(P)^0 ⟶ J/J²`
(`NaiveCotangent.towerNullHomotopyBaseChange`).  The two identities of Stacks 07VC say that
`h ∘ d = g₁ ∘ c₁₁` and `d ∘ h = g₀ ∘ c₁₀`, so `h` descends to the quotients
(`NaiveCotangent.towerCokernelMap`).  Everything else comes from the connecting map:

* `NaiveCotangent.connecting_nullHomotopy_mem_range` is the one new computation.  For a cycle
  `z ∈ J/J²` it produces a representative `x` of `δ z` with `z + h x ∈ im g₁`, where `δ` is the
  connecting map `NaiveCotangent.jacobiZariskiConnecting` of Stacks 00S2.  The proof is the
  homotopy of Stacks 00S1 (2) between the *two* morphisms of presentations
  `A[y_c, x_b] ⟶ B[y_c]` — the surjection `Algebra.Generators.ofComp`, which sends `x_b` to the
  coefficient `b`, and the one that factors through `A[C]`, which sends `x_b` to the variable
  `y_{φ(b)}` — evaluated on a zig-zag for `δ`.  Their difference on `x_b` is `b - [φ(b)]`, which
  is exactly minus the value of the homotopy of Stacks 07VC, so the homotopy of 00S1 (2) carried
  along `Algebra.Generators.toComp` *is* `-h`
  (`NaiveCotangent.towerCompSub_comp_cotangentSpaceMap_toComp`).
* Surjectivity then follows from exactness of 00S2 at `Ω_{C/A}` together with bijectivity of
  `g₀`, and injectivity from exactness at `C ⊗_B Ω_{B/A}` and at `H₁(NL_{C/B})`: both are
  `NaiveCotangent.jacobiZariski_sixTerm_exact_canonical`.

## Main definitions

* `NaiveCotangent.towerNullHomotopyBaseChange`: the homotopy of Stacks 07VC, base changed to `C`.
* `NaiveCotangent.towerCompHom`: the morphism of presentations `A[y_c, x_b] ⟶ A[C]` over `A`
  which sends `x_b` to the variable `y_{φ(b)}`.
* `NaiveCotangent.towerCokernelMap`: the induced map `H₀(NL(P) ⊗_B C) ⟶ coker (g^{-1})`.

## Main results

* `NaiveCotangent.towerNullHomotopyBaseChange_comp_d` and
  `NaiveCotangent.d_comp_towerNullHomotopyBaseChange`: the two identities of Stacks 07VC, base
  changed to `C`.
* `NaiveCotangent.bijective_cotangentSpaceMap_towerTopHom`: `g` is bijective in degree `0`.
* `NaiveCotangent.connecting_nullHomotopy_mem_range`: the compatibility of the homotopy with the
  connecting map of Stacks 00S2.
* `NaiveCotangent.surjective_towerCokernelMap` and
  `NaiveCotangent.injective_towerCokernelMap`, hence
  `NaiveCotangent.bijective_towerCokernelMap`: **the induced map is bijective.**

## References

* [Stacks Project, Tag 0E1Y](https://stacks.math.columbia.edu/tag/0E1Y), the consumer.
* [Stacks Project, Tag 00S2](https://stacks.math.columbia.edu/tag/00S2), the six-term sequence.
* [Stacks Project, Tag 00S1](https://stacks.math.columbia.edu/tag/00S1), part (2), the homotopy
  between two morphisms of presentations.
* [Stacks Project, Tag 07VC](https://stacks.math.columbia.edu/tag/07VC), the explicit homotopy.
-/

@[expose] public section

universe u₁ u₂ u₃

open Algebra Function MvPolynomial TensorProduct

namespace NaiveCotangent

variable (A : Type u₁) (B : Type u₂) (C : Type u₃) [CommRing A] [CommRing B] [CommRing C]
  [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]

/-! ### The three presentations and the maps between them -/

/-- The morphism of presentations `A[y_c, x_b] ⟶ A[C]` over `A` which sends the variable `y_c`
to `y_c` and the variable `x_b` to `y_{φ(b)}`.  Composed with
`NaiveCotangent.towerTopHom` it is the second of the two morphisms `A[y_c, x_b] ⟶ B[y_c]` whose
difference computes the homotopy of Stacks 07VC; the first is
`Algebra.Generators.ofComp`. -/
@[simps]
noncomputable def towerCompHom :
    ((Generators.self B C).comp (Generators.self A B)).Hom (Generators.self A C) where
  val i := X (((Generators.self B C).comp (Generators.self A B)).val i)
  aeval_val i := by simp

/-- The homotopy of Stacks 07VC, base changed to `C`: the `C`-linear map
`C ⊗_B (Ω_{A[B]/A} ⊗_{A[B]} B) ⟶ J/J²` sending `1 ⊗ d[b]` to the class of `[φ(b)] - b`. -/
noncomputable def towerNullHomotopyBaseChange :
    C ⊗[B] (Generators.self A B).toExtension.CotangentSpace →ₗ[C]
      (Generators.self B C).toExtension.Cotangent :=
  (Extension.Hom.sub
    ((towerTopHom A B C).toExtensionHom.comp (towerMidHom A B C).toExtensionHom)
    (towerConstHom A B C).toExtensionHom).liftBaseChange C

/-- The homotopy of Stacks 07VC, with the extension morphism of the composite spelled as a
composite of extension morphisms, which is the spelling `Algebra.Extension.Hom.sub`'s lemmas
produce. -/
theorem sub_apply_eq_towerNullHomotopy
    (x : (Generators.self A B).toExtension.CotangentSpace) :
    Extension.Hom.sub
        ((towerTopHom A B C).toExtensionHom.comp (towerMidHom A B C).toExtensionHom)
        (towerConstHom A B C).toExtensionHom x = towerNullHomotopy A B C x := by
  simp only [towerNullHomotopy, LinearMap.restrictScalars_apply,
    Generators.Hom.toExtensionHom_comp]

/-- The base changed homotopy sends `c ⊗ x` to `c • towerNullHomotopy A B C x`. -/
@[simp]
theorem towerNullHomotopyBaseChange_tmul (c : C)
    (x : (Generators.self A B).toExtension.CotangentSpace) :
    towerNullHomotopyBaseChange A B C (c ⊗ₜ x) = c • towerNullHomotopy A B C x := by
  rw [towerNullHomotopyBaseChange, LinearMap.liftBaseChange_tmul,
    sub_apply_eq_towerNullHomotopy]

/-- The base changed homotopy sends `1 ⊗ x` to `towerNullHomotopy A B C x`. -/
@[simp]
theorem towerNullHomotopyBaseChange_one_tmul
    (x : (Generators.self A B).toExtension.CotangentSpace) :
    towerNullHomotopyBaseChange A B C ((1 : C) ⊗ₜ x) = towerNullHomotopy A B C x := by
  rw [towerNullHomotopyBaseChange_tmul, one_smul]

/-- The comparison `c₁ : NL(P) ⊗_B C ⟶ NL(N)` of Stacks 0E1Y, over the canonical
presentations. -/
noncomputable abbrev towerBaseChangeMap :=
  nlExtensionBaseChangeMap (T := C) (towerMidHom A B C).toExtensionHom

/-- The comparison `g : NL(N) ⟶ NL(Q)` of Stacks 0E1Y, over the canonical presentations. -/
noncomputable abbrev towerRelMap :=
  nlExtensionOverMap (towerTopHom A B C).toExtensionHom

/-- The cokernel of `g` in degree `-1`, that is of `K/K² ⟶ J/J²`.  This is `H⁰` of the shifted
cone of `g`, by `CochainComplex.mappingCone.shiftedHomologyZeroIsoCokernel`. -/
noncomputable abbrev towerRelConormalCokernel :=
  (Generators.self B C).toExtension.Cotangent ⧸
    LinearMap.range (Extension.Cotangent.map (towerTopHom A B C).toExtensionHom)

/-! ### The two identities of Stacks 07VC, base changed -/

/-- The base change lift of the zero map is zero. -/
private theorem liftBaseChange_zero_eq_zero {M N : Type*} [AddCommGroup M] [AddCommGroup N]
    [Module B M] [Module B N] [Module C N] [IsScalarTower B C N] :
    LinearMap.liftBaseChange C (0 : M →ₗ[B] N) = 0 := by
  ext x; simp

/-- The degree `1` identity of Stacks 07VC, base changed: `h ∘ d = g₁ ∘ c₁₁`. -/
theorem towerNullHomotopyBaseChange_comp_d :
    towerNullHomotopyBaseChange A B C ∘ₗ
        ((Generators.self A B).toExtension.cotangentComplex.baseChange C) =
      Extension.Cotangent.map (towerTopHom A B C).toExtensionHom ∘ₗ
        (Extension.Cotangent.map (towerMidHom A B C).toExtensionHom).liftBaseChange C := by
  have h3 := sub_liftBaseChange_cotangentMap (T := C)
    ((towerTopHom A B C).toExtensionHom.comp (towerMidHom A B C).toExtensionHom)
    (towerConstHom A B C).toExtensionHom
  rw [← Generators.Hom.toExtensionHom_comp, cotangentMap_towerConstHom_eq_zero A B C,
    liftBaseChange_zero_eq_zero B C,
    sub_zero, Generators.Hom.toExtensionHom_comp, Extension.Cotangent.map_comp,
    ← LinearMap.liftBaseChange_comp] at h3
  exact h3.symm

/-- The degree `0` identity of Stacks 07VC, base changed: `d ∘ h = g₀ ∘ c₁₀`. -/
theorem d_comp_towerNullHomotopyBaseChange :
    (Generators.self B C).toExtension.cotangentComplex ∘ₗ
        towerNullHomotopyBaseChange A B C =
      Extension.CotangentSpace.map (towerTopHom A B C).toExtensionHom ∘ₗ
        (Extension.CotangentSpace.map (towerMidHom A B C).toExtensionHom).liftBaseChange C := by
  have h3 := sub_liftBaseChange_cotangentSpaceMap (T := C)
    ((towerTopHom A B C).toExtensionHom.comp (towerMidHom A B C).toExtensionHom)
    (towerConstHom A B C).toExtensionHom
  rw [cotangentSpaceMap_towerConstHom_eq_zero A B C,
    liftBaseChange_zero_eq_zero B C, sub_zero,
    Extension.CotangentSpace.map_comp, ← LinearMap.liftBaseChange_comp] at h3
  exact h3.symm

/-- The degree `0` identity of Stacks 07VC, base changed, read elementwise. -/
private theorem cotangentComplex_towerNullHomotopyBaseChange
    (n : C ⊗[B] (Generators.self A B).toExtension.CotangentSpace) :
    (Generators.self B C).toExtension.cotangentComplex (towerNullHomotopyBaseChange A B C n) =
      Extension.CotangentSpace.map (towerTopHom A B C).toExtensionHom
        ((Extension.CotangentSpace.map
          (towerMidHom A B C).toExtensionHom).liftBaseChange C n) :=
  DFunLike.congr_fun (d_comp_towerNullHomotopyBaseChange A B C) n

/-! ### `g` is bijective in degree `0` -/

/-- The ring map underlying `NaiveCotangent.towerTopHom` sends each variable `X t` to `X t`. -/
theorem toRingHom_towerTopHom_X (t : C) :
    (towerTopHom A B C).toExtensionHom.toRingHom (X t) = X t := by
  show (towerTopHom A B C).toAlgHom (X t) = X t
  rw [Generators.Hom.toAlgHom_X, towerTopHom_val]

/-- The map `g` in degree `0`, on cotangent spaces induced by `NaiveCotangent.towerTopHom`, is
bijective. -/
theorem bijective_cotangentSpaceMap_towerTopHom :
    Bijective (Extension.CotangentSpace.map (towerTopHom A B C).toExtensionHom) :=
  bijective_cotangentSpaceMap_self (towerTopHom A B C).toExtensionHom
    (toRingHom_towerTopHom_X A B C)

/-! ### The induced map on cokernels -/

/-- **The map `H₀(NL(P) ⊗_B C) ⟶ coker (g^{-1})` induced by the homotopy of Stacks 07VC.**
It is well defined because `h ∘ d = g₁ ∘ c₁₁`. -/
noncomputable def towerCokernelMap :
    (C ⊗[B] (Generators.self A B).toExtension.CotangentSpace) ⧸
        LinearMap.range ((Generators.self A B).toExtension.cotangentComplex.baseChange C) →ₗ[C]
      towerRelConormalCokernel A B C :=
  Submodule.liftQ _
    ((LinearMap.range
        (Extension.Cotangent.map (towerTopHom A B C).toExtensionHom)).mkQ ∘ₗ
      towerNullHomotopyBaseChange A B C) (by
      rintro y ⟨x, rfl⟩
      refine (Submodule.Quotient.mk_eq_zero _).2
        ⟨(Extension.Cotangent.map (towerMidHom A B C).toExtensionHom).liftBaseChange C x, ?_⟩
      exact (DFunLike.congr_fun (towerNullHomotopyBaseChange_comp_d A B C) x).symm)

/-- `NaiveCotangent.towerCokernelMap` sends the class of `x` to the class of
`towerNullHomotopyBaseChange A B C x`. -/
@[simp]
theorem towerCokernelMap_mkQ (x : C ⊗[B] (Generators.self A B).toExtension.CotangentSpace) :
    towerCokernelMap A B C ((LinearMap.range
        ((Generators.self A B).toExtension.cotangentComplex.baseChange C)).mkQ x) =
      (LinearMap.range
        (Extension.Cotangent.map (towerTopHom A B C).toExtensionHom)).mkQ
          (towerNullHomotopyBaseChange A B C x) :=
  rfl

/-! ### The homotopy of Stacks 00S1 (2) between the two morphisms `A[y_c, x_b] ⟶ B[y_c]` -/

/-- The surjection `A[y_c, x_b] ⟶ B[y_c]` of the proof of Stacks 00S2, which sends the variable
`x_b` to the *coefficient* `b`.  This is `Algebra.Generators.ofComp`. -/
noncomputable abbrev towerOfCompHom :=
  ((Generators.self B C).ofComp (Generators.self A B)).toExtensionHom

/-- The other morphism `A[y_c, x_b] ⟶ B[y_c]` of presentations of `C`, which sends the variable
`x_b` to the *variable* `y_{φ(b)}`: it factors through the canonical presentation `A[C]` of `C`
over `A`, so the chain map it induces factors through `NL(N)`. -/
noncomputable abbrev towerCompRelHom :=
  (towerTopHom A B C).toExtensionHom.comp (towerCompHom A B C).toExtensionHom

/-- `Algebra.Generators.toComp` carries the basis element `d[b]` to the basis element
`d x_b` of the cotangent space of the induced presentation `A[y_c, x_b]`. -/
theorem cotangentSpaceMap_toComp_cotangentSpaceBasis (b : B) :
    Extension.CotangentSpace.map
        ((Generators.self B C).toComp (Generators.self A B)).toExtensionHom
        ((Generators.self A B).cotangentSpaceBasis b) =
      ((Generators.self B C).comp (Generators.self A B)).cotangentSpaceBasis (Sum.inr b) := by
  have e₂ : (((Generators.self B C).toComp (Generators.self A B)).toExtensionHom).toAlgHom
      (X b) = X (Sum.inr b) := by
    show ((Generators.self B C).toComp (Generators.self A B)).toAlgHom (X b) = _
    rw [Generators.Hom.toAlgHom_X, Generators.toComp_val]
  rw [Generators.cotangentSpaceBasis_apply, Generators.cotangentSpaceBasis_apply]
  refine (Extension.CotangentSpace.map_tmul
    ((Generators.self B C).toComp (Generators.self A B)).toExtensionHom (1 : B) (X b)).trans ?_
  rw [map_one, e₂]
  rfl

/-- **The homotopy of Stacks 00S1 (2) between the two morphisms `A[y_c, x_b] ⟶ B[y_c]`, read on
the basis element `d x_b`, is minus the homotopy of Stacks 07VC on `d[b]`.**  The first morphism
sends `x_b` to the coefficient `b` and the second to the variable `y_{φ(b)}`, so their difference
is `b - [φ(b)]`, while the homotopy of Stacks 07VC sends `d[b]` to `[φ(b)] - b`. -/
theorem towerCompSub_cotangentSpaceBasis (b : B) :
    Extension.Hom.sub (towerOfCompHom A B C) (towerCompRelHom A B C)
        (((Generators.self B C).comp (Generators.self A B)).cotangentSpaceBasis
          (Sum.inr b)) =
      -(towerNullHomotopy A B C ((Generators.self A B).cotangentSpaceBasis b)) := by
  have h1 := (congrArg (Extension.Hom.sub (towerOfCompHom A B C) (towerCompRelHom A B C))
      (Generators.cotangentSpaceBasis_apply
        ((Generators.self B C).comp (Generators.self A B)) (Sum.inr b))).trans
    (Extension.Hom.sub_one_tmul (towerOfCompHom A B C) (towerCompRelHom A B C)
      (X (Sum.inr b)))
  have hof : (towerOfCompHom A B C).toAlgHom (X (Sum.inr b)) = MvPolynomial.C b := by
    show ((Generators.self B C).ofComp (Generators.self A B)).toAlgHom (X (Sum.inr b)) = _
    rw [Generators.Hom.toAlgHom_X, Generators.ofComp_val]
    rfl
  have hrel : (towerCompRelHom A B C).toAlgHom (X (Sum.inr b)) = X (algebraMap B C b) := by
    have e : (towerCompHom A B C).toAlgHom (X (Sum.inr b)) = X (algebraMap B C b) := by
      rw [Generators.Hom.toAlgHom_X, towerCompHom_val, Generators.comp_val]
      rfl
    show (towerTopHom A B C).toAlgHom ((towerCompHom A B C).toAlgHom (X (Sum.inr b))) = _
    rw [e, Generators.Hom.toAlgHom_X, towerTopHom_val]
  rw [h1, towerNullHomotopy_cotangentSpaceBasis, ← map_neg]
  refine congrArg Extension.Cotangent.mk (Subtype.ext ?_)
  show (towerOfCompHom A B C).toAlgHom (X (Sum.inr b)) -
      (towerCompRelHom A B C).toAlgHom (X (Sum.inr b)) =
    -(X (algebraMap B C b) - MvPolynomial.C b)
  rw [hof, hrel]
  exact (neg_sub (X (algebraMap B C b)) (MvPolynomial.C b)).symm

/-- **The homotopy of Stacks 00S1 (2), restricted along `Algebra.Generators.toComp`, is minus the
homotopy of Stacks 07VC.** -/
theorem towerCompSub_comp_cotangentSpaceMap_toComp :
    (Extension.Hom.sub (towerOfCompHom A B C) (towerCompRelHom A B C)).restrictScalars B ∘ₗ
        Extension.CotangentSpace.map
          ((Generators.self B C).toComp (Generators.self A B)).toExtensionHom =
      -(towerNullHomotopy A B C) :=
  (Generators.self A B).cotangentSpaceBasis.ext fun b ↦ by
    rw [LinearMap.coe_comp, comp_apply, LinearMap.restrictScalars_apply,
      cotangentSpaceMap_toComp_cotangentSpaceBasis A B C b,
      towerCompSub_cotangentSpaceBasis A B C b, LinearMap.neg_apply]

/-- `NaiveCotangent.towerCompSub_comp_cotangentSpaceMap_toComp`, base changed to `C` and read
elementwise. -/
theorem towerCompSub_liftBaseChange_apply
    (x : C ⊗[B] (Generators.self A B).toExtension.CotangentSpace) :
    Extension.Hom.sub (towerOfCompHom A B C) (towerCompRelHom A B C)
        ((Extension.CotangentSpace.map
          ((Generators.self B C).toComp (Generators.self A B)).toExtensionHom).liftBaseChange C
            x) =
      -(towerNullHomotopyBaseChange A B C x) := by
  have key := towerCompSub_comp_cotangentSpaceMap_toComp A B C
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul c m =>
    rw [LinearMap.liftBaseChange_tmul, map_smul, towerNullHomotopyBaseChange_tmul, ← smul_neg]
    refine congrArg (fun t ↦ c • t) ?_
    simpa using DFunLike.congr_fun key m
  | add u v hu hv => simp only [map_add, hu, hv, neg_add]

/-! ### The compatibility with the connecting map of Stacks 00S2 -/

/-- **The homotopy of Stacks 07VC against the connecting map of Stacks 00S2.**  For a cycle `z`
of `J/J²` there is a representative `x` of `δ z` with `z + h x` in the image of `K/K² ⟶ J/J²`.

This is the one computation that the comparison of `H⁰(NL_{B/A} ⊗_B C)` with `coker (g^{-1})`
needs, and it is where the explicit homotopy of Stacks 07VC enters: a zig-zag for `δ` consists of
a lift `y ∈ K_γ/K_γ²` of `z` along the surjection of `Algebra.Generators.ofComp` together with an
`x` whose image is `d y`, and the homotopy of Stacks 00S1 (2) between that surjection and the
morphism which factors through `A[C]` turns `z - (something in the image of K/K²)` into the value
of `-h` on `x`. -/
theorem connecting_nullHomotopy_mem_range
    (z : (Generators.self B C).toExtension.Cotangent)
    (hz : (Generators.self B C).toExtension.cotangentComplex z = 0) :
    ∃ x : C ⊗[B] (Generators.self A B).toExtension.CotangentSpace,
      jacobiZariskiConnecting (Generators.self B C) (Generators.self A B)
            ⟨z, LinearMap.mem_ker.mpr hz⟩ =
          (LinearMap.range
            ((Generators.self A B).toExtension.cotangentComplex.baseChange C)).mkQ x ∧
        z + towerNullHomotopyBaseChange A B C x ∈
          LinearMap.range (Extension.Cotangent.map (towerTopHom A B C).toExtensionHom) := by
  obtain ⟨y, x₀, hy, hx₀⟩ := exists_connecting_zigZag
    (nlToComp (Generators.self B C) (Generators.self A B))
    (nlOfComp (Generators.self B C) (Generators.self A B))
    (Generators.CotangentSpace.exact (Generators.self B C) (Generators.self A B))
    (Generators.Cotangent.surjective_map_ofComp (Generators.self B C) (Generators.self A B))
    ⟨z, LinearMap.mem_ker.mpr hz⟩
  obtain ⟨x, rfl⟩ : ∃ x : C ⊗[B] (Generators.self A B).toExtension.CotangentSpace, x = x₀ :=
    ⟨x₀, rfl⟩
  obtain ⟨y, rfl⟩ : ∃ y' : ((Generators.self B C).comp
      (Generators.self A B)).toExtension.Cotangent, y' = y := ⟨y, rfl⟩
  refine ⟨x, connecting_apply (nlToComp (Generators.self B C) (Generators.self A B))
    (nlOfComp (Generators.self B C) (Generators.self A B))
    (Generators.CotangentSpace.map_toComp_injective (Generators.self B C)
      (Generators.self A B))
    (Generators.CotangentSpace.exact (Generators.self B C) (Generators.self A B))
    (Generators.Cotangent.surjective_map_ofComp (Generators.self B C) (Generators.self A B))
    (Generators.Cotangent.exact (Generators.self B C) (Generators.self A B))
    ⟨z, LinearMap.mem_ker.mpr hz⟩ y hy x hx₀, ?_⟩
  -- The homotopy of Stacks 00S1 (2) between the two morphisms `A[y_c, x_b] ⟶ B[y_c]`.
  have hsub : Extension.Cotangent.map (towerOfCompHom A B C) y -
      Extension.Cotangent.map (towerCompRelHom A B C) y =
      Extension.Hom.sub (towerOfCompHom A B C) (towerCompRelHom A B C)
        (((Generators.self B C).comp (Generators.self A B)).toExtension.cotangentComplex y) :=
    DFunLike.congr_fun
      (Extension.Cotangent.map_sub_map (towerOfCompHom A B C) (towerCompRelHom A B C)) y
  -- The second leg of the zig-zag turns `d y` into the image of `x`.
  rw [show ((Generators.self B C).comp (Generators.self A B)).toExtension.cotangentComplex y =
      (Extension.CotangentSpace.map
        ((Generators.self B C).toComp (Generators.self A B)).toExtensionHom).liftBaseChange C x
    from hx₀.symm, towerCompSub_liftBaseChange_apply] at hsub
  -- The first leg turns the first term into `z`.
  rw [show Extension.Cotangent.map (towerOfCompHom A B C) y = z from hy] at hsub
  refine ⟨Extension.Cotangent.map (towerCompHom A B C).toExtensionHom y, ?_⟩
  have hmap : Extension.Cotangent.map (towerCompRelHom A B C) y =
      Extension.Cotangent.map (towerTopHom A B C).toExtensionHom
        (Extension.Cotangent.map (towerCompHom A B C).toExtensionHom y) :=
    DFunLike.congr_fun
      (Extension.Cotangent.map_comp
        (P := ((Generators.self B C).comp (Generators.self A B)).toExtension)
        (P' := (Generators.self A C).toExtension)
        (P'' := (Generators.self B C).toExtension)
        (towerCompHom A B C).toExtensionHom (towerTopHom A B C).toExtensionHom) y
  rw [← hmap]
  rw [sub_eq_iff_eq_add] at hsub
  rw [hsub]
  abel

/-! ### Bijectivity -/

/-- **The map induced by the homotopy of Stacks 07VC is surjective.**  Given `j ∈ J/J²`, its
differential is the image of some `l ∈ Ω_{A[C]/A} ⊗ C` because `g` is bijective in degree `0`;
exactness of Stacks 00S2 at `Ω_{C/A}` writes `l` as `c₁ n + d z`, so `j - h n - g z` is a cycle,
and `NaiveCotangent.connecting_nullHomotopy_mem_range` puts that cycle in the image of `h`
modulo the image of `g` in degree `-1`. -/
theorem surjective_towerCokernelMap : Surjective (towerCokernelMap A B C) := by
  intro q
  obtain ⟨j, rfl⟩ := Submodule.mkQ_surjective
    (LinearMap.range (Extension.Cotangent.map (towerTopHom A B C).toExtensionHom)) q
  obtain ⟨l, hl⟩ := (bijective_cotangentSpaceMap_towerTopHom A B C).surjective
    ((Generators.self B C).toExtension.cotangentComplex j)
  obtain ⟨n₀, w₀, hnw₀⟩ := exists_add_d_of_exact_onH₀ (towerBaseChangeMap A B C)
    (towerRelMap A B C)
    (jacobiZariski_sixTerm_exact_canonical (towerMidHom A B C).toExtensionHom
      (towerTopHom A B C).toExtensionHom).2.2.2.1 l ⟨j, hl.symm⟩
  obtain ⟨n, rfl⟩ : ∃ n : C ⊗[B] (Generators.self A B).toExtension.CotangentSpace, n = n₀ :=
    ⟨n₀, rfl⟩
  obtain ⟨w, rfl⟩ : ∃ w : (Generators.self A C).toExtension.Cotangent, w = w₀ := ⟨w₀, rfl⟩
  have hnw : (Extension.CotangentSpace.map
        (towerMidHom A B C).toExtensionHom).liftBaseChange C n +
      (Generators.self A C).toExtension.cotangentComplex w = l := hnw₀
  have hcyc : (Generators.self B C).toExtension.cotangentComplex
      (j - towerNullHomotopyBaseChange A B C n -
        Extension.Cotangent.map (towerTopHom A B C).toExtensionHom w) = 0 := by
    rw [map_sub, map_sub, ← hl, cotangentComplex_towerNullHomotopyBaseChange A B C n,
      ← Extension.CotangentSpace.map_cotangentComplex
        (towerTopHom A B C).toExtensionHom w,
      ← map_sub, ← map_sub, ← hnw]
    simp
  obtain ⟨x, -, v, hv⟩ := connecting_nullHomotopy_mem_range A B C _ hcyc
  refine ⟨(LinearMap.range
    ((Generators.self A B).toExtension.cotangentComplex.baseChange C)).mkQ (n - x), ?_⟩
  rw [towerCokernelMap_mkQ, map_sub, Submodule.mkQ_apply, Submodule.mkQ_apply,
    Submodule.Quotient.eq]
  refine ⟨-(v + w), ?_⟩
  rw [map_neg, map_add, hv]
  abel

/-- **The map induced by the homotopy of Stacks 07VC is injective.**  If `h n` lies in the image
of `g` in degree `-1` then `c₁ n` is a boundary, so exactness of Stacks 00S2 at
`C ⊗_B Ω_{B/A}` writes the class of `n` as `δ ζ`;
`NaiveCotangent.connecting_nullHomotopy_mem_range` then puts `ζ` itself in the image of `g` on
`H₁`, where exactness at `H₁(NL_{C/B})` makes `δ ζ` vanish. -/
theorem injective_towerCokernelMap : Injective (towerCokernelMap A B C) := by
  refine (injective_iff_map_eq_zero (towerCokernelMap A B C)).2 fun q hq ↦ ?_
  obtain ⟨n, rfl⟩ := Submodule.mkQ_surjective
    (LinearMap.range ((Generators.self A B).toExtension.cotangentComplex.baseChange C)) q
  rw [towerCokernelMap_mkQ, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hq
  obtain ⟨u, hu⟩ := hq
  have e3 : ∀ y, towerNullHomotopyBaseChange A B C
        (((Generators.self A B).toExtension.cotangentComplex.baseChange C) y) =
      Extension.Cotangent.map (towerTopHom A B C).toExtensionHom
        ((Extension.Cotangent.map (towerMidHom A B C).toExtensionHom).liftBaseChange C y) :=
    fun y ↦ DFunLike.congr_fun (towerNullHomotopyBaseChange_comp_d A B C) y
  -- `c₁ n` is the boundary of `u`.
  have h1 : (Extension.CotangentSpace.map
        (towerMidHom A B C).toExtensionHom).liftBaseChange C n =
      (Generators.self A C).toExtension.cotangentComplex u := by
    refine (bijective_cotangentSpaceMap_towerTopHom A B C).injective ?_
    rw [← cotangentComplex_towerNullHomotopyBaseChange A B C n, ← hu,
      Extension.CotangentSpace.map_cotangentComplex]
  -- Stacks 00S2, exactness at `C ⊗_B Ω_{B/A}`.
  obtain ⟨ζ, hζ⟩ := ((jacobiZariski_sixTerm_exact_canonical
      (towerMidHom A B C).toExtensionHom (towerTopHom A B C).toExtensionHom).2.2.1
    ((LinearMap.range
      ((Generators.self A B).toExtension.cotangentComplex.baseChange C)).mkQ n)).1
    ((onH₀_mkQ (towerBaseChangeMap A B C) n).trans
      ((Submodule.Quotient.mk_eq_zero _).2 ⟨u, h1.symm⟩))
  -- The cycle `ζ`, in the explicit spelling.
  obtain ⟨z, hzv⟩ : ∃ z : (Generators.self B C).toExtension.Cotangent,
      z = (ζ : (NL (Generators.self B C)).X₁) := ⟨_, rfl⟩
  have hz : (Generators.self B C).toExtension.cotangentComplex z = 0 := by
    rw [hzv]; exact LinearMap.mem_ker.mp ζ.2
  obtain ⟨x, hx, v, hv⟩ := connecting_nullHomotopy_mem_range A B C z hz
  have hζz : (⟨z, LinearMap.mem_ker.mpr hz⟩ : H₁ (NL (Generators.self B C))) = ζ :=
    Subtype.ext hzv
  -- `x` and `n` have the same class, so `h x` too lies in the image of `g` in degree `-1`.
  have hx' : jacobiZariskiConnecting (Generators.self B C) (Generators.self A B) ζ =
      (LinearMap.range
        ((Generators.self A B).toExtension.cotangentComplex.baseChange C)).mkQ x := hζz ▸ hx
  obtain ⟨t, ht⟩ := (Submodule.Quotient.eq _).1 (hζ.symm.trans hx')
  have hhx : towerNullHomotopyBaseChange A B C x ∈
      LinearMap.range (Extension.Cotangent.map (towerTopHom A B C).toExtensionHom) := by
    refine ⟨u - (Extension.Cotangent.map
      (towerMidHom A B C).toExtensionHom).liftBaseChange C t, ?_⟩
    rw [map_sub, hu, ← e3 t, ht, map_sub]
    abel
  -- Hence `z` itself lies in that image, and it is a cycle, so `ζ` is in the image on `H₁`.
  obtain ⟨y, hy⟩ := hhx
  obtain ⟨s, hs⟩ : z ∈ LinearMap.range
      (Extension.Cotangent.map (towerTopHom A B C).toExtensionHom) := by
    refine ⟨v - y, ?_⟩
    rw [map_sub, hv, hy]
    abel
  have hds : (Generators.self A C).toExtension.cotangentComplex s = 0 := by
    refine (bijective_cotangentSpaceMap_towerTopHom A B C).injective ?_
    rw [Extension.CotangentSpace.map_cotangentComplex, hs, hz, map_zero]
  have hζimage : ∃ ξ, (towerRelMap A B C).onH₁ ξ = ζ :=
    ⟨⟨s, LinearMap.mem_ker.mpr hds⟩, Subtype.ext (hs.trans hzv)⟩
  rw [← hζ]
  exact ((jacobiZariski_sixTerm_exact_canonical (towerMidHom A B C).toExtensionHom
    (towerTopHom A B C).toExtensionHom).2.1 ζ).2 hζimage

/-- **The homotopy of Stacks 07VC induces an isomorphism
`H₀(NL_{B/A} ⊗_B C) ≅ coker (K/K² ⟶ J/J²)`.**  This is the remaining input to the six-term exact
sequence of cohomology sheaves of Stacks 0E1Y: read at a stalk it says that the canonical map `c`
of that tag is an isomorphism on `H⁰`. -/
theorem bijective_towerCokernelMap : Bijective (towerCokernelMap A B C) :=
  ⟨injective_towerCokernelMap A B C, surjective_towerCokernelMap A B C⟩

end NaiveCotangent

end
