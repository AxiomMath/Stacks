module

public import StacksFrontier.Algebra.DirectSum.GradedSubmodule
public import StacksFrontier.Algebra.DGA.Abelian

/-! # The product of a family of differential graded modules

Let `(A, d)` be a differential graded algebra over a commutative ring `R` and let
`(f i)_{i ∈ ι}` be a family of right differential graded `A`-modules. This file constructs the
product `∏ᵢ f i` as a *named* object of `Mod_(A, d)` together with its projections, and proves
the two elementwise facts that characterise it: a point of the product is determined by its
components, and a family of components all homogeneous of one degree `n` is the family of
components of a point of degree `n`.

The product is **not** the product of the underlying right `A`-modules. The category is one of
graded modules, so the product is formed degreewise, `(∏ᵢ f i)ⁿ = ∏ᵢ (f i)ⁿ`, and its
underlying module is `⨁ₙ ∏ᵢ (f i)ⁿ`, which is in general a proper submodule of `∏ᵢ (f i).M` —
exactly the part of it with finite graded support.

## Main definitions

* `DifferentialGradedModule.product`: the product object, for an index type in `Type u`.
* `DifferentialGradedModule.product.π`: its projections.
* `DifferentialGradedModule.product.lift`: the lift of a family of maps into the factors.
* `DifferentialGradedModule.uliftProduct`: the product of a family indexed by a type in
  `Type 0` — in particular of a tower indexed by `ℕ` — with the same interface.

## Main results

* `DifferentialGradedModule.product.eq_of_π_eq` and
  `DifferentialGradedModule.product.eq_zero_of_π_eq_zero`: a point of the product is determined
  by its components.
* `DifferentialGradedModule.product.exists_mem_grading`: every family of components homogeneous
  of a common degree is realised by a point of that degree.
* `DifferentialGradedModule.product.mem_grading_iff`: a point is homogeneous of degree `n`
  exactly when each of its components is.
* `DifferentialGradedModule.product.π_lift` and `DifferentialGradedModule.product.hom_ext`: the
  categorical universal property, in `lift`/`ext` form.
* `DifferentialGradedModule.product.isLimit`: the fan of projections is a limit cone, which is
  what identifies `product f` with the abstract `∏ᶜ f`.

## Implementation notes

*Why a named object and not only a `HasProducts` instance.* `Mod_(A, d)` already has all
`Type u`-indexed products: `DifferentialGradedModule.instHasProducts` in
the Tag 09JJ development. But the object representing `∏ᶜ f` there is `private`
(and so is the second copy of the same construction in
`Module/HomotopyCategoryLimits.lean`), so nothing can be proved about `∏ᶜ f` elementwise —
neither that a given map onto it is surjective nor what its kernel is. The consumers of the
product in this chapter all reason elementwise: the telescope of Stacks 09KR needs joint
injectivity of the projections and degreewise joint surjectivity, which is the hypothesis shape
of `DifferentialGradedModule.exists_productLift` and
`DifferentialGradedModule.exists_homLift`. So the construction is repeated here *publicly*, and
the abstract limit is recovered from it by `product.isLimit`: `limit.isoLimitCone` then
identifies `∏ᶜ f` with `product f`, which is the only direction anyone needs — the computational
handle is the named object, the limit is a consequence.

*The index type lives in `Type u`, and that is forced.* `DifferentialGradedModule A` carries
`M : Type u` (see the Tag 09JJ development, which declares `universe u` only), while
the carrier of a product over `ι : Type v` is a submodule of `∀ i : ι, (f i).M : Type (max u v)`.
So a product indexed by a genuinely larger type is not an object of this category at all; this
is a limitation of the chapter's encoding, not of the construction, and it matches
`instHasProducts : HasProducts.{u}`. The index types that actually occur are of two kinds: the
graded pieces of a property-(I) filtration are products over an index type in `Type u`
(`DifferentialGradedModule.PropertyIFiltration.quotientIndex`), and the telescopes of Stacks
09KR and 09KU are products over `ℕ`. The second kind is served by `uliftProduct`, the product
over `ULift.{u} ι` for `ι : Type 0`, whose projections are indexed by `ι` itself. Note that
`ULift` is essential and `Shrink` would not do: `(ULift.up i).down` reduces to `i`, so
`product.π _ ⟨i⟩` already *has* type `uliftProduct f ⟶ f i`, whereas the corresponding
projection through `equivShrink` only has that type up to `Equiv.symm_apply_apply`, and a
transport there would make every elementwise statement a statement about a cast. The index type
is not pinned to `ℕ` because nothing in the construction uses more than its size.

*Transparency discipline.* The carrier `(product f).M` is equal to the honest submodule
`↥(productSubmodule f)` only by unfolding at default transparency, and instance search runs
below that. So every lemma about the carrier is stated at the honest type — `productSubmodule_ext`
and `mem_productPiece` quantify over `↥(productSubmodule f)` and `∀ i, (f i).M` — and the public
statements about `(product f).M` are discharged from them by plain application, which checks
definitional equality at default transparency. This is the pattern of
`DifferentialGradedModule.lof_comp_shift_d` in `Module/LeftOrthogonalAcyclic.lean`; see its
docstring.

## References

* [Stacks Project, Tag 09JJ](https://stacks.math.columbia.edu/tag/09JJ), where `Mod_(A, d)` is
  shown to be complete, and [Tag 09JR](https://stacks.math.columbia.edu/tag/09JR) for the
  products of its homotopy category.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace DifferentialGradedModule

universe u

variable {R : Type u} [CommRing R] {A : DifferentialGradedAlgebra R}

section Product

variable {ι : Type u} (f : ι → DifferentialGradedModule A)

/-! ### The underlying graded module -/

/-- The degree-`n` piece of the product, as an `R`-submodule of `∏ᵢ (f i).M`:
`Pⁿ = ∏ᵢ (f i).grading n`. -/
def productPiece (n : ℤ) : Submodule R (∀ i, (f i).M) :=
  Submodule.pi Set.univ fun i => (f i).grading n

/-- Membership in a degree-`n` piece of the product is membership componentwise. -/
theorem mem_productPiece {n : ℤ} (x : ∀ i, (f i).M) :
    x ∈ productPiece f n ↔ ∀ i, x i ∈ (f i).grading n := by
  simp [productPiece, Submodule.mem_pi]

/-- The `i`-th projection carries the degree-`m` piece of the product into `(f i)^m`. -/
theorem map_proj_productPiece (i : ι) (m : ℤ) :
    Submodule.map (LinearMap.proj i) (productPiece f m) ≤ (f i).grading m := by
  rintro _ ⟨x, hx, rfl⟩
  exact (mem_productPiece f x).1 hx i

/-- The degree-`n` pieces of the product are independent, because the gradings of the factors
are. -/
theorem productPiece_iSupIndep : iSupIndep (productPiece f) := by
  rw [iSupIndep_def]
  intro n
  rw [Submodule.disjoint_def]
  intro x hxn hxsup
  ext i
  have hgi : iSupIndep (f i).grading :=
    (DirectSum.Decomposition.isInternal (f i).grading).submodule_iSupIndep
  rw [iSupIndep_def] at hgi
  have hd := hgi n
  rw [Submodule.disjoint_def] at hd
  have hproj : x i ∈ ⨆ m, ⨆ (_ : m ≠ n), (f i).grading m := by
    have h : x i ∈ Submodule.map (LinearMap.proj i) (⨆ m, ⨆ (_ : m ≠ n), productPiece f m) :=
      ⟨x, hxsup, rfl⟩
    rw [Submodule.map_iSup] at h
    have hle : (⨆ m, Submodule.map (LinearMap.proj i) (⨆ (_ : m ≠ n), productPiece f m))
        ≤ ⨆ m, ⨆ (_ : m ≠ n), (f i).grading m := by
      refine iSup_le fun m => ?_
      rw [Submodule.map_iSup]
      exact iSup_le fun hm => le_trans (map_proj_productPiece f i m)
        (le_iSup₂ (f := fun m _ => (f i).grading m) m hm)
    exact hle h
  have := hd (x i) ((mem_productPiece f x).1 hxn i) hproj
  simpa using this

/-- Right multiplication by a homogeneous `a ∈ A.grading m` sends `Pⁿ` into `P^(n+m)`. -/
theorem smul_productPiece_homogeneous (n m : ℤ) (a : A.A) (ha : a ∈ A.grading m)
    (x : ∀ i, (f i).M) (hx : x ∈ productPiece f n) :
    (MulOpposite.op a) • x ∈ productPiece f (n + m) := by
  rw [mem_productPiece] at hx ⊢
  intro i
  have h : ((MulOpposite.op a) • x) i = (MulOpposite.op a) • (x i) := rfl
  rw [h]
  exact (f i).smul_mem n m (x i) a (hx i) ha

/-- An additive map sending each homogeneous piece `𝒜 n` into `P (d n)` sends every element, being
a finite sum of homogeneous ones, into `⨆ₙ P n`. -/
private theorem map_mem_iSup_of_decompose {R S M N : Type*} [Semiring R] [Semiring S]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module S N] (𝒜 : ℤ → Submodule R M)
    [DirectSum.Decomposition 𝒜] (F : M →+ N) (P : ℤ → Submodule S N) (d : ℤ → ℤ)
    (hF : ∀ n x, x ∈ 𝒜 n → F x ∈ P (d n)) (t : M) : F t ∈ ⨆ n, P n := by
  classical
  rw [← DirectSum.sum_support_decompose 𝒜 t, map_sum]
  exact Submodule.sum_mem _ fun n _ =>
    Submodule.mem_iSup_of_mem (d n) (hF n _ (DirectSum.decompose 𝒜 t n).2)

/-- Right multiplication by an arbitrary `a : A.A` sends `Pⁿ` into `⨆ₖ Pᵏ`, by decomposing `a`
into its homogeneous components. -/
theorem smul_productPiece_mem_iSup (n : ℤ) (a : A.A) (x : ∀ i, (f i).M)
    (hx : x ∈ productPiece f n) : (MulOpposite.op a) • x ∈ ⨆ k, productPiece f k :=
  map_mem_iSup_of_decompose A.grading
    (AddMonoidHom.mk' (fun a : A.A => (MulOpposite.op a) • x) fun _ _ => by
      rw [MulOpposite.op_add, add_smul])
    (productPiece f) (n + ·) (fun m b hb => smul_productPiece_homogeneous f n m b hb x hx) a

/-- The underlying module of the product, as an `Aᵐᵒᵖ`-submodule of `∏ᵢ (f i).M` with carrier
`⨆ₙ Pⁿ`: the elements of the cartesian product with finite graded support. -/
@[implicit_reducible]
def productSubmodule : Submodule (MulOpposite A.A) (∀ i, (f i).M) where
  carrier := {x | x ∈ ⨆ n, productPiece f n}
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq] at *
    exact (⨆ n, productPiece f n).add_mem ha hb
  zero_mem' := by
    simp only [Set.mem_ofPred_eq]
    exact (⨆ n, productPiece f n).zero_mem
  smul_mem' := by
    intro c x hx
    simp only [Set.mem_ofPred_eq] at *
    rw [show c • x = (MulOpposite.op c.unop) • x from rfl]
    induction hx using Submodule.iSup_induction' with
    | mem n y hy => exact smul_productPiece_mem_iSup f n c.unop y hy
    | zero => rw [smul_zero]; exact (⨆ n, productPiece f n).zero_mem
    | add a b _ _ iha ihb => rw [smul_add]; exact (⨆ n, productPiece f n).add_mem iha ihb

/-- The underlying module of the product, over `R`, is the supremum of the degree pieces. -/
theorem productSubmodule_restrictScalars :
    (productSubmodule f).restrictScalars R = ⨆ n, productPiece f n := by
  apply SetLike.coe_injective; rfl

/-- **A point of the product is determined by its components.** Stated at the honest carrier,
as the public `product.eq_of_π_eq` below is discharged from it by application. -/
theorem productSubmodule_ext {x y : ↥(productSubmodule f)}
    (h : ∀ i, (x : ∀ i, (f i).M) i = (y : ∀ i, (f i).M) i) : x = y :=
  Subtype.ext (funext h)

/-- The componentwise differential on `∏ᵢ (f i).M`. -/
noncomputable def productD₀ : (∀ i, (f i).M) →ₗ[R] (∀ i, (f i).M) :=
  LinearMap.pi fun i => ((f i).d).comp (LinearMap.proj i)

/-- The componentwise differential acts componentwise. -/
theorem productD₀_apply (x : ∀ i, (f i).M) (i : ι) : productD₀ f x i = (f i).d (x i) := by
  simp [productD₀, LinearMap.pi_apply]

/-- The componentwise differential sends `Pⁿ` into `P^(n+1)`. -/
theorem productD₀_productPiece (n : ℤ) (x : ∀ i, (f i).M) (hx : x ∈ productPiece f n) :
    productD₀ f x ∈ productPiece f (n + 1) := by
  rw [mem_productPiece] at hx ⊢
  intro i
  rw [productD₀_apply]
  exact (f i).d_mem n (x i) (hx i)

/-- The componentwise differential preserves the underlying module of the product. -/
theorem productD₀_mem (x : ∀ i, (f i).M) (hx : x ∈ (productSubmodule f).restrictScalars R) :
    productD₀ f x ∈ (productSubmodule f).restrictScalars R := by
  rw [productSubmodule_restrictScalars] at hx ⊢
  induction hx using Submodule.iSup_induction' with
  | mem n y hy =>
      apply Submodule.mem_iSup_of_mem (n + 1)
      exact productD₀_productPiece f n y hy
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add a b _ _ iha ihb => rw [map_add]; exact Submodule.add_mem _ iha ihb

/-- The grading on the product: the degree pieces `Pⁿ`, read inside the underlying module. -/
noncomputable def productGrading (n : ℤ) : Submodule R ↥(productSubmodule f) :=
  Submodule.inducedGrading (productPiece f) ((productSubmodule f).restrictScalars R) n

/-- Membership in the grading of the product is membership in a degree piece. -/
theorem mem_productGrading {n : ℤ} (x : ↥(productSubmodule f)) :
    x ∈ productGrading f n ↔ (x : ∀ i, (f i).M) ∈ productPiece f n := Iff.rfl

/-- The differential on the product. -/
noncomputable def productD : ↥(productSubmodule f) →ₗ[R] ↥(productSubmodule f) :=
  LinearMap.restrict (productD₀ f) (p := (productSubmodule f).restrictScalars R)
    (q := (productSubmodule f).restrictScalars R) fun x hx => productD₀_mem f x hx

/-! ### The product object and its projections -/

/-- **The product `∏ᵢ f i` of a family of differential graded modules**, formed degreewise:
`(∏ᵢ f i)ⁿ = ∏ᵢ (f i)ⁿ` and `∏ᵢ f i = ⨁ₙ ∏ᵢ (f i)ⁿ`, with the componentwise right `A`-action
and the componentwise differential. -/
@[implicit_reducible]
noncomputable def product : DifferentialGradedModule A where
  M := ↥(productSubmodule f)
  grading := productGrading f
  decomposition := by
    change DirectSum.Decomposition (productGrading f)
    unfold productGrading
    exact Submodule.inducedGrading.decompositionOfEqISup (productPiece f)
      (productPiece_iSupIndep f) ((productSubmodule f).restrictScalars R)
      (productSubmodule_restrictScalars f)
  smul_mem := by
    intro n m x a hx ha
    rw [mem_productGrading] at hx
    have hxv : (x : ∀ i, (f i).M) ∈ productPiece f n := hx
    rw [mem_productGrading]
    change (MulOpposite.op a • x : ∀ i, (f i).M) ∈ productPiece f (n + m)
    exact smul_productPiece_homogeneous f n m a ha x hxv
  d := productD f
  d_comp_d := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change (productD₀ f (productD₀ f (x : ∀ i, (f i).M)) : ∀ i, (f i).M)
      = ((0 : ↥(productSubmodule f)) : ∀ i, (f i).M)
    funext i
    rw [productD₀_apply, productD₀_apply]
    have hdd := LinearMap.congr_fun (f i).d_comp_d ((x : ∀ i, (f i).M) i)
    simpa using hdd
  d_mem := by
    intro n x hx
    rw [mem_productGrading] at hx
    have hxv : (x : ∀ i, (f i).M) ∈ productPiece f n := hx
    rw [mem_productGrading]
    change (productD₀ f (x : ∀ i, (f i).M)) ∈ productPiece f (n + 1)
    exact productD₀_productPiece f n x hxv
  leibniz := by
    intro n m x a hx ha
    rw [mem_productGrading] at hx
    have hxv : (x : ∀ i, (f i).M) ∈ productPiece f n := hx
    apply Subtype.ext
    change (productD₀ f (MulOpposite.op a • (x : ∀ i, (f i).M)) : ∀ i, (f i).M)
      = ((MulOpposite.op a) • (productD f x)
        + (n.negOnePow : ℤ) • ((MulOpposite.op (A.d a)) • x) : ↥(productSubmodule f))
    funext i
    have hxi : (x : ∀ i, (f i).M) i ∈ (f i).grading n := (mem_productPiece f x).1 hxv i
    have hle := (f i).leibniz n m ((x : ∀ i, (f i).M) i) a hxi ha
    change (f i).d (MulOpposite.op a • ((x : ∀ i, (f i).M) i))
      = (MulOpposite.op a) • ((f i).d ((x : ∀ i, (f i).M) i))
        + (n.negOnePow : ℤ) • ((MulOpposite.op (A.d a)) • ((x : ∀ i, (f i).M) i))
    exact hle

/-- The grading of the product object is the grading built above. Deliberately not a `simp`
lemma: rewriting with it replaces the bundled spelling by the carrier-level one and so defeats
`product.mem_grading_iff`. It is the escape hatch for a caller that really wants the carrier. -/
theorem product_grading : (product f).grading = productGrading f := rfl

/-- The differential of the product object is the componentwise one. Not a `simp` lemma, for the
reason given on `product_grading`. -/
theorem product_d : (product f).d = productD f := rfl

/-- The `i`-th projection `∏ⱼ f j ⟶ f i`. -/
noncomputable def product.π (i : ι) : product f ⟶ f i where
  toFun := (LinearMap.proj i).comp ((productSubmodule f).restrictScalars R).subtype
  map_smul := by intro x a; rfl
  map_grading := by
    intro n x hx
    have hx' : ((show ↥(productSubmodule f) from x) : ∀ i, (f i).M) ∈ productPiece f n := hx
    exact (mem_productPiece f _).1 hx' i
  map_d := by
    apply LinearMap.ext
    intro x
    rfl

/-- The `i`-th projection reads off the `i`-th coordinate. Stated at the honest carrier, and
deliberately not a `simp` lemma: it exposes the carrier, and in the `simp` set it fires before
`product.π_lift_apply` and leaves goals phrased in terms of `productSubmodule`. -/
theorem product.π_apply (i : ι) (x : ↥(productSubmodule f)) :
    (product.π f i).toFun x = (x : ∀ i, (f i).M) i := rfl

/-! ### The elementwise universal property -/

/-- **A point of the product is determined by its components.** -/
theorem product.eq_of_π_eq {x y : (product f).M}
    (h : ∀ i, (product.π f i).toFun x = (product.π f i).toFun y) : x = y :=
  productSubmodule_ext f h

/-- **The projections of the product are jointly injective.** This is the hypothesis `hsep` of
`DifferentialGradedModule.exists_productLift`, discharged for the product itself. -/
theorem product.eq_zero_of_π_eq_zero (y : (product f).M)
    (h : ∀ i, (product.π f i).toFun y = 0) : y = 0 :=
  product.eq_of_π_eq f fun i => (h i).trans (map_zero (product.π f i).toFun).symm

/-- **A point of the product is homogeneous of degree `n` exactly when all of its components
are.** -/
theorem product.mem_grading_iff {n : ℤ} (x : (product f).M) :
    x ∈ (product f).grading n ↔ ∀ i, (product.π f i).toFun x ∈ (f i).grading n := by
  refine ⟨fun hx i => (product.π f i).map_grading n x hx, fun h => ?_⟩
  exact (mem_productGrading f x).2 ((mem_productPiece f _).2 h)

/-- **The projections of the product are jointly surjective in each degree.** A family of
components all homogeneous of degree `n` is the family of components of a point of degree `n`.
This is the hypothesis `hlift` of `DifferentialGradedModule.exists_productLift`, discharged for
the product itself. -/
theorem product.exists_mem_grading (n : ℤ) (q : ∀ i, (f i).M)
    (hq : ∀ i, q i ∈ (f i).grading n) :
    ∃ y ∈ (product f).grading n, ∀ i, (product.π f i).toFun y = q i :=
  ⟨⟨q, Submodule.mem_iSup_of_mem n ((mem_productPiece f q).2 hq)⟩,
    (mem_productGrading f _).2 ((mem_productPiece f q).2 hq), fun _ => rfl⟩

/-! ### The categorical universal property -/

/-- A family of additive maps into the factors, all shifting degrees by a common amount `d`,
assembles into a function with values in the underlying module of the product: a point of the
source is a finite sum of homogeneous ones, so its image has finite graded support. -/
theorem pi_mem_productSubmodule {T : DifferentialGradedModule A} (g : ∀ i, T.M →+ (f i).M)
    (d : ℤ → ℤ) (hg : ∀ (i : ι) (n : ℤ) (x : T.M), x ∈ T.grading n → g i x ∈ (f i).grading (d n))
    (t : T.M) : (fun i => g i t) ∈ (productSubmodule f).restrictScalars R := by
  rw [productSubmodule_restrictScalars]
  exact map_mem_iSup_of_decompose T.grading (AddMonoidHom.pi g) (productPiece f) d
    (fun n x hx => (mem_productPiece f _).mpr fun i => hg i n x hx) t

/-- **The lift of a family of homomorphisms into the factors** to a homomorphism into the
product. -/
noncomputable def product.lift {T : DifferentialGradedModule A} (g : ∀ i, T ⟶ f i) :
    T ⟶ product f where
  toFun := LinearMap.codRestrict ((productSubmodule f).restrictScalars R)
    (LinearMap.pi fun i => (g i).toFun) fun t => pi_mem_productSubmodule f
      (fun i => (g i).toFun.toAddMonoidHom) id (fun i n x hx => (g i).map_grading n x hx) t
  map_smul x a := Subtype.ext <| funext fun i => (g i).map_smul x a
  map_grading n x hx := (mem_productPiece f _).mpr fun i => (g i).map_grading n x hx
  map_d := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    funext i
    change (g i).toFun (T.d x) = (f i).d ((g i).toFun x)
    have h := LinearMap.congr_fun (g i).map_d x
    simpa using h

/-- The lift followed by the `i`-th projection is the `i`-th map of the family. -/
@[simp] theorem product.π_lift {T : DifferentialGradedModule A} (g : ∀ i, T ⟶ f i) (i : ι) :
    product.lift f g ≫ product.π f i = g i :=
  Hom.ext rfl

/-- The `i`-th component of the lift at a point is the `i`-th map of the family at that point. -/
@[simp] theorem product.π_lift_apply {T : DifferentialGradedModule A} (g : ∀ i, T ⟶ f i) (i : ι)
    (x : T.M) : (product.π f i).toFun ((product.lift f g).toFun x) = (g i).toFun x := rfl

/-- **Two maps into the product agreeing on all projections are equal.** -/
theorem product.hom_ext {T : DifferentialGradedModule A} {a b : T ⟶ product f}
    (h : ∀ i, a ≫ product.π f i = b ≫ product.π f i) : a = b :=
  Hom.ext <| LinearMap.ext fun t =>
    productSubmodule_ext f fun i => LinearMap.congr_fun (congrArg Hom.toFun (h i)) t

/-- **The fan of projections exhibits `product f` as the categorical product.** Composed with
`CategoryTheory.Limits.limit.isoLimitCone`, this identifies the abstract `∏ᶜ f` of
`DifferentialGradedModule.instHasProducts` with `product f`. -/
noncomputable def product.isLimit : IsLimit (Fan.mk (product f) (product.π f)) :=
  Fan.IsLimit.mk _ (fun s => product.lift f fun i => s.proj i)
    (fun s i => product.π_lift f (fun i => s.proj i) i)
    fun _ _ hm => product.hom_ext f fun i => (hm i).trans (product.π_lift f _ i).symm

end Product

/-! ### Products indexed by a type in `Type 0`

A tower, such as the one appearing in the telescope of Stacks 09KR, is indexed by `ℕ`, which is
not a `Type u`. The product over `ULift.{u} ι` serves such a family with projections indexed by
`ι` itself, because `(ULift.up i).down` reduces to `i`. -/

section UliftProduct

variable {ι : Type} (f : ι → DifferentialGradedModule A)

/-- **The product `∏ᵢ f i` of a family indexed by a type in `Type 0`**, such as a tower indexed
by `ℕ`: the `Type u`-indexed product over `ULift.{u} ι`. -/
noncomputable def uliftProduct : DifferentialGradedModule A :=
  product fun j : ULift.{u} ι => f j.down

/-- The `i`-th projection of `uliftProduct f`. -/
noncomputable def uliftProduct.π (i : ι) : uliftProduct f ⟶ f i :=
  product.π (fun j : ULift.{u} ι => f j.down) ⟨i⟩

/-- A point of `uliftProduct f` is determined by its components. -/
theorem uliftProduct.eq_of_π_eq {x y : (uliftProduct f).M}
    (h : ∀ i, (uliftProduct.π f i).toFun x = (uliftProduct.π f i).toFun y) : x = y :=
  product.eq_of_π_eq _ fun j => h j.down

/-- The projections of `uliftProduct f` are jointly injective. -/
theorem uliftProduct.eq_zero_of_π_eq_zero (y : (uliftProduct f).M)
    (h : ∀ i, (uliftProduct.π f i).toFun y = 0) : y = 0 :=
  product.eq_zero_of_π_eq_zero _ y fun j => h j.down

/-- A point of `uliftProduct f` is homogeneous of degree `n` exactly when all of its components
are. -/
theorem uliftProduct.mem_grading_iff {n : ℤ} (x : (uliftProduct f).M) :
    x ∈ (uliftProduct f).grading n ↔ ∀ i, (uliftProduct.π f i).toFun x ∈ (f i).grading n :=
  (product.mem_grading_iff _ x).trans ⟨fun h i => h ⟨i⟩, fun h j => h j.down⟩

/-- The projections of `uliftProduct f` are jointly surjective in each degree. -/
theorem uliftProduct.exists_mem_grading (n : ℤ) (q : ∀ i, (f i).M)
    (hq : ∀ i, q i ∈ (f i).grading n) :
    ∃ y ∈ (uliftProduct f).grading n, ∀ i, (uliftProduct.π f i).toFun y = q i := by
  obtain ⟨y, hy, hπ⟩ :=
    product.exists_mem_grading (fun j : ULift.{u} ι => f j.down) n (fun j => q j.down)
      fun j => hq j.down
  exact ⟨y, hy, fun i => hπ ⟨i⟩⟩

/-- The lift of a family of homomorphisms into the factors of `uliftProduct f`. -/
noncomputable def uliftProduct.lift {T : DifferentialGradedModule A} (g : ∀ i, T ⟶ f i) :
    T ⟶ uliftProduct f :=
  product.lift (fun j : ULift.{u} ι => f j.down) fun j => g j.down

/-- The lift followed by the `i`-th projection of `uliftProduct f` is the `i`-th map. -/
@[simp] theorem uliftProduct.π_lift {T : DifferentialGradedModule A} (g : ∀ i, T ⟶ f i)
    (i : ι) : uliftProduct.lift f g ≫ uliftProduct.π f i = g i :=
  product.π_lift (fun j : ULift.{u} ι => f j.down) (fun j => g j.down) ⟨i⟩

/-- The `i`-th component of the lift into `uliftProduct f` at a point is the `i`-th map at that
point. -/
@[simp] theorem uliftProduct.π_lift_apply {T : DifferentialGradedModule A} (g : ∀ i, T ⟶ f i)
    (i : ι) (x : T.M) :
    (uliftProduct.π f i).toFun ((uliftProduct.lift f g).toFun x) = (g i).toFun x := rfl

/-- Two maps into `uliftProduct f` agreeing on all projections are equal. -/
theorem uliftProduct.hom_ext {T : DifferentialGradedModule A} {a b : T ⟶ uliftProduct f}
    (h : ∀ i, a ≫ uliftProduct.π f i = b ≫ uliftProduct.π f i) : a = b :=
  product.hom_ext _ fun j => h j.down

end UliftProduct

end DifferentialGradedModule

end
