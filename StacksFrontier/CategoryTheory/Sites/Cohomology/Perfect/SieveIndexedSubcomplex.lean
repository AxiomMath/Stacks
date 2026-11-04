module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.SieveIndexedSubcomplexGenerators
public import StacksFrontier.CategoryTheory.Sites.Modules.ExtensionByZeroGenerators

/-!
# The finitely generated subcomplex spanned by a closed set of arrow generators

Let `(C, J)` be a small site, `O` a sheaf of rings on it, and `P` a cochain complex of sheaves
of `O`-modules each of whose terms is presented as a direct sum of extensions by zero of the
structure sheaves of slices, `P^n = ⊕_{α ∈ I n} j_{U n α !} O_{U n α}`. Over an object `W` the
module `P^n(W)` carries the arrow generators of
`StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.SieveIndexedSpan`, indexed by
`Stacks.Sites.ExtensionByZero.GenIdx (U n) W`, and
`Stacks.Sites.ExtensionByZero.exists_sieve_closed_span` produces, over a covering sieve, a
finite graded set `S` of them closed under the differential.

This file builds the subcomplex those generators span. In degree `n` it is the image of the map

  `⊕_{k ∈ S n} j_{W!} O_W ⟶ P^n`

sending the tautological generator of the `k`-th summand to the `k`-th arrow generator; the
differential is the map of images induced by the commutative square whose top edge sends the
`k`-th summand to the combination of degree-`(n+1)` generators that the differential of the
`k`-th generator is, which is where closedness of `S` under the differential is consumed.

That is the object the source of Stacks 0FPV calls `𝒦^•`, and this file is the sieve-indexed
replacement for the ringed-space construction
`Stacks.Cohomology.LeftDualPerfect.subcomplex` of
`StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.ExtensionByZeroSubcomplex`.

## Main definitions

* `Stacks.Sites.ExtensionByZero.genSubcomplex` and
  `Stacks.Sites.ExtensionByZero.genSubcomplexι`: the subcomplex of a complex generated
  degreewise by an arbitrary family `g n : A n ⟶ P^n` admitting a lift of the differential,
  and its inclusion.
* `Stacks.Sites.ExtensionByZero.srcObj`: the sum of copies of `j_{W!} O_W` indexed by the
  generators of one degree.
* `Stacks.Sites.ExtensionByZero.gMap`: the map from that sum to the degree-`n` term of `P`
  carrying the summands to the chosen generators.
* `Stacks.Sites.ExtensionByZero.liftMap`: the lift of the differential to the sums.
* `Stacks.Sites.ExtensionByZero.subcomplex` and
  `Stacks.Sites.ExtensionByZero.subcomplexι`: **the subcomplex and its inclusion into `P`**,
  the `gMap`/`liftMap` instance of `genSubcomplex`.

## Main results

* `Stacks.Sites.ExtensionByZero.fromExtensionByZero_comp`: composing the map classified by a
  section with a morphism gives the map classified by the image of that section.
* `Stacks.Sites.ExtensionByZero.exists_coeff_of_inSpan`: membership in the span of a *finite*
  set of arrow generators has explicit coefficients.
* `Stacks.Sites.ExtensionByZero.mono_genSubcomplexι_f`: the inclusion is degreewise a
  monomorphism, so the complex really is a subcomplex of `P`.
* `Stacks.Sites.ExtensionByZero.exists_epi_srcObj`: each term is a quotient of a finite sum of
  copies of `j_{W!} O_W` — the sense in which the subcomplex is finitely generated.
* `Stacks.Sites.ExtensionByZero.isZero_subcomplex_X_of_eq_empty` and
  `Stacks.Sites.ExtensionByZero.isZero_subcomplex_X_of_isZero`: a degree carrying no generator,
  and a degree where `P` vanishes, carry the zero module; these are what bound the subcomplex
  below and above.
* `Stacks.Sites.ExtensionByZero.exists_lift_of_inSpan`: every section in the span of the
  generators of its degree lifts to the subcomplex.
* `Stacks.Sites.ExtensionByZero.exists_sieve_subcomplex`: **over a covering sieve, a
  degreewise-monomorphic finitely generated subcomplex of `P`, concentrated in the degrees
  where `P` is, through which the given sections factor.**

## Implementation notes

The construction is factored through `Stacks.Sites.ExtensionByZero.genSubcomplex`, which takes
the generating family `g n : A n ⟶ P^n` and a lift `lift n : A n ⟶ A (n + 1)` of the
differential as data. The hypothesis is only `lift n ≫ g (n + 1) = g n ≫ d`, and that is the
right generality rather than an abstraction for its own sake: the lift built here is not
itself a differential. Its coefficients are chosen one degree at a time, by `Classical.choose`
on a span membership, so nothing makes `liftMap` composed with itself zero and this file does
not claim it is; there is accordingly no chain map `A ⟶ P` whose degreewise image could be
taken. `Stacks.Sites.ExtensionByZero.genDiff_genDiff` recovers `d ∘ d = 0` on the images,
where `image.ι` is monic and `P`'s own `d ∘ d = 0` can be used. Step 6 of the source's proof
enlarges `𝒦^{m-1}` by the image of a homotopy component, which is again a family of this shape
with a different `A`, so it is a further instance of `genSubcomplex` and not a second
construction.

The library already contains one abstract degreewise-image subcomplex,
`Stacks.AlgebraicGeometry.ExtendBoundedComplex.subComplex` of
`StacksFrontier.AlgebraicGeometry.DerivedCoherent.ExtendBoundedComplex`, stated for an arbitrary
abelian category and used there for Stacks 0G48. It is not reused here, and the reason is
mathematical first and structural second.

It is a *different* object: its degree-`n` term is the image of `A^n ⊕ A^{n-1} ⟶ P^n`, the
second summand entering through the differential of `P`. That is a closed formula needing no
hypothesis — which is a real advantage, and worth recording, because it means a subcomplex of
`P` containing prescribed sections can be had on a site with no appeal to
`exists_sieve_closed_span` at all. What it costs is the count: the degree-`n` term is then
generated by `(S n).card + (S (n-1)).card` sections rather than `(S n).card`. The source's own
route supplies the closedness and keeps the smaller count, and `genSubcomplex` here is the
construction that consumes it. The two are not independent, though: that construction is this
shape instantiated at the generator object `A^n ⊕ A^{n-1}` with the lift
`biprod.desc biprod.inr 0`, which is the very square its `exists_image_hom` verifies. Unifying
them means promoting that file's `Abstract` section to a neutral homology module, which is a
refactor of a scheme-theoretic file and is not done here.

Structurally, importing it is not an import cycle — its in-repo closure contains nothing under
`StacksDraft.CategoryTheory.Sites.Cohomology` — but it is a layer inversion: that closure is
514 in-repo modules against this file's 30, so a `CategoryTheory.Sites` file would acquire 503
modules of scheme theory to reuse twenty lines of abelian-category formalities.

The index of the sum is `Fin (S n).card` rather than the subtype `{y // y ∈ S n}`, although
biproducts in this category are available at either shape. Two things are bought by the
numeral: `Stacks.Sites.ExtensionByZero.exists_epi_srcObj` and the conclusion of
`Stacks.Sites.ExtensionByZero.exists_sieve_subcomplex` can say "a sum of `r` copies" with no
existential over types carrying a `Finite` instance, and the enumeration
`Stacks.Sites.ExtensionByZero.srcIdx` is the same bookkeeping the ringed-space construction
uses, so the two developments stay comparable line by line. The cost is one extra rewrite with
`Equiv.sum_comp` in `Stacks.Sites.ExtensionByZero.gMap_sum_srcGen`.

`Stacks.Sites.ExtensionByZero.InSpan` is `Submodule.span` membership, which is what makes
`InSpan.res` short on a site; the subcomplex, on the other hand, needs the coefficients
themselves, and `Stacks.Sites.ExtensionByZero.exists_coeff_of_inSpan` extracts them. It is
proved by bounding the span by the range of the `O(W)`-linear map
`Stacks.Sites.ExtensionByZero.combine` that evaluates a family of coefficients on the
generators, rather than by `Submodule.mem_span_finset`: the spanning set is the image of
`S n` under `genSec`, and that image can identify two indices, so a sum indexed by the image
`Finset` is not a sum indexed by `S n`. Going through the range of `combine` indexes the sum
by `S n` from the start.

The differential is `CategoryTheory.Limits.image.map` of an `CategoryTheory.Arrow.homMk'`,
so the square it comes from is the only input and no `eqToHom` appears; `image.map_homMk'_ι`
is what identifies it on the nose with the differential of `P` under the inclusion.
`CategoryTheory.Abelian.hasFiniteBiproducts` is a local instance because Mathlib deliberately
does not make it global, exactly as in the ringed-space development and in the other files of
this library that take finite biproducts in an abelian category.

Everything is at a single universe `u` for site, ring and modules, as forced by the span
engine and by `StacksFrontier.CategoryTheory.Sites.Modules.ExtensionByZero`.

## References

* [Stacks Project, Tag 03EW](https://stacks.math.columbia.edu/tag/03EW)
* [Stacks Project, Tag 0FPV](https://stacks.math.columbia.edu/tag/0FPV)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace Stacks.Sites.ExtensionByZero

attribute [local instance] Abelian.hasFiniteBiproducts

variable {C : Type u} [SmallCategory.{u} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  (O : Sheaf J RingCat.{u})

/-- **Composing the map classified by a section with a morphism** gives the map classified by
the image of that section. This is the sieve-indexed counterpart of the ringed-space statement
`Stacks.Cohomology.LeftDualPerfect.homOfSection_comp`, and like it, it is proved by evaluating
both sides at the tautological generator, which determines a map out of `j_{W!} O_W` by
`SheafOfModules.bijective_val_app_gen`. -/
theorem fromExtensionByZero_comp {M N : SheafOfModules.{u} O} (W : C) (x : M.val.obj (op W))
    (φ : M ⟶ N) :
    SheafOfModules.fromExtensionByZero O M W x ≫ φ =
      SheafOfModules.fromExtensionByZero O N W (φ.val.app (op W) x) := by
  refine (SheafOfModules.bijective_val_app_gen O N W).1 ?_
  change (SheafOfModules.fromExtensionByZero O M W x ≫ φ).val.app (op W)
      (SheafOfModules.extensionByZeroGen O W) =
    (SheafOfModules.fromExtensionByZero O N W (φ.val.app (op W) x)).val.app (op W)
      (SheafOfModules.extensionByZeroGen O W)
  rw [SheafOfModules.fromExtensionByZero_val_app_gen]
  exact congrArg (φ.val.app (op W)) (SheafOfModules.fromExtensionByZero_val_app_gen O M W x)

section Generated

variable {O}

variable {P : CochainComplex (SheafOfModules.{u} O) ℤ} (A : ℤ → SheafOfModules.{u} O)
  (g : ∀ n : ℤ, A n ⟶ P.X n)

/-- **Each term of the generated subcomplex is a quotient of the corresponding generator
object.** -/
theorem exists_epi_image (n : ℤ) : ∃ π : A n ⟶ image (g n), Epi π :=
  ⟨factorThruImage (g n), inferInstance⟩

/-- A degree whose generator object vanishes carries the zero module. -/
theorem isZero_image_of_isZero_src (n : ℤ) (hn : IsZero (A n)) : IsZero (image (g n)) :=
  hn.of_epi (factorThruImage (g n))

/-- A degree where `P` vanishes carries the zero module. -/
theorem isZero_image_of_isZero_tgt (n : ℤ) (hn : IsZero (P.X n)) : IsZero (image (g n)) :=
  hn.of_mono (image.ι (g n))

variable {A g}

variable {lift : ∀ n : ℤ, A n ⟶ A (n + 1)}
  (hlift : ∀ n : ℤ, lift n ≫ g (n + 1) = g n ≫ P.d n (n + 1))

/-- The differential of the generated subcomplex, as a map of images. -/
def genDiff (n : ℤ) : image (g n) ⟶ image (g (n + 1)) :=
  image.map (Arrow.homMk' (lift n) (P.d n (n + 1)) (hlift n))

/-- The differential of the generated subcomplex commutes with the inclusions of the images into
`P`. -/
theorem genDiff_ι (n : ℤ) :
    genDiff hlift n ≫ image.ι (g (n + 1)) = image.ι (g n) ≫ P.d n (n + 1) :=
  image.map_homMk'_ι _

/-- Two consecutive differentials of the generated subcomplex compose to zero. -/
theorem genDiff_genDiff (n : ℤ) : genDiff hlift n ≫ genDiff hlift (n + 1) = 0 := by
  rw [← cancel_mono (image.ι (g (n + 1 + 1))), Category.assoc, genDiff_ι, ← Category.assoc,
    genDiff_ι, Category.assoc, HomologicalComplex.d_comp_d, comp_zero, zero_comp]

/-- **The subcomplex of `P` generated degreewise by a family `g` whose differential lifts.**
In degree `n` it is the image of `g n`, and the hypothesis is only that the differential of `P`
is covered on the sources: `lift` need not itself be a differential, and for the family this
file builds nothing makes `lift n ≫ lift (n + 1)` zero. -/
def genSubcomplex : CochainComplex (SheafOfModules.{u} O) ℤ :=
  CochainComplex.of (fun n => image (g n)) (genDiff hlift) (genDiff_genDiff hlift)

/-- The inclusion of the generated subcomplex. -/
def genSubcomplexι : genSubcomplex hlift ⟶ P where
  f n := image.ι (g n)
  comm' i j hij := by
    obtain rfl : i + 1 = j := hij
    exact (genDiff_ι hlift i).symm.trans (congrArg (· ≫ image.ι (g (i + 1)))
      (CochainComplex.of_d (fun n => image (g n)) (genDiff hlift) i).symm)

/-- The inclusion of the generated subcomplex is a monomorphism in each degree. -/
instance mono_genSubcomplexι_f (n : ℤ) : Mono ((genSubcomplexι hlift).f n) := by
  change Mono (image.ι (g n))
  infer_instance

/-- The degree-`n` term of the generated subcomplex is the image of `g n`. -/
theorem genSubcomplex_X (n : ℤ) : (genSubcomplex hlift).X n = image (g n) := rfl

/-- In degree `n` the inclusion of the generated subcomplex is the image inclusion of `g n`. -/
theorem genSubcomplexι_f (n : ℤ) : (genSubcomplexι hlift).f n = image.ι (g n) := rfl

/-- **A section in the image of `g n` on sections lifts to the generated subcomplex.** -/
theorem exists_lift_of_eq_app {n : ℤ} {W : C} {x : (P.X n).val.obj (op W)}
    {a : (A n).val.obj (op W)} (hx : (g n).val.app (op W) a = x) :
    ∃ y : ((genSubcomplex hlift).X n).val.obj (op W),
      ((genSubcomplexι hlift).f n).val.app (op W) y = x :=
  ⟨(factorThruImage (g n)).val.app (op W) a,
    (congrArg (fun φ => φ.val.app (op W) a) (image.fac (g n))).trans hx⟩

end Generated

section Coefficients

variable {I : Type u} (U : I → C)
  (c : Cofan fun α : I => (SheafOfModules.extensionByZero.{u, u, u, u} O (U α)).obj
    (SheafOfModules.unit (O.over (U α))))

/-- **The combination of the generators indexed by `T` with prescribed coefficients**, as an
`O(W)`-linear map in the coefficients. -/
def combine {W : C} (T : Finset (GenIdx U W)) :
    (GenIdx U W → ((O.obj.obj (op W) : RingCat.{u}) : Type u)) →ₗ[
      ((O.obj.obj (op W) : RingCat.{u}) : Type u)] c.pt.val.obj (op W) where
  toFun f := ∑ y ∈ T, f y • genSec O U c W y
  map_add' f g := by
    simp only [Pi.add_apply, add_smul]
    exact Finset.sum_add_distrib
  map_smul' r f := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.smul_sum, smul_smul]

/-- **Membership in the span of a finite set of arrow generators has explicit coefficients.**
On a space the span is defined by an explicit combination to begin with; here `InSpan` is
`Submodule.span` membership, and this is the extraction. -/
theorem exists_coeff_of_inSpan {W : C} {T : Finset (GenIdx U W)} {x : c.pt.val.obj (op W)}
    (hx : InSpan O U c W ↑T x) :
    ∃ f : GenIdx U W → ((O.obj.obj (op W) : RingCat.{u}) : Type u),
      x = ∑ y ∈ T, f y • genSec O U c W y := by
  classical
  have hle : Submodule.span ((O.obj.obj (op W) : RingCat.{u}) : Type u)
      (genSec O U c W '' ↑T) ≤ LinearMap.range (combine O U c T) := by
    rw [Submodule.span_le]
    rintro - ⟨y, hy, rfl⟩
    refine ⟨fun z => if z = y then 1 else 0, ?_⟩
    change ∑ z ∈ T, (if z = y then (1 : ((O.obj.obj (op W) : RingCat.{u}) : Type u)) else 0) •
      genSec O U c W z = genSec O U c W y
    rw [Finset.sum_eq_single_of_mem y hy fun z _ hz => by rw [ite_eq_right hz, zero_smul],
      ite_eq_left rfl, one_smul]
  obtain ⟨f, hf⟩ := hle hx
  exact ⟨f, hf.symm⟩

end Coefficients

variable (P : CochainComplex (SheafOfModules.{u} O) ℤ) {I : ℤ → Type u} (U : ∀ n, I n → C)
  (ιP : ∀ (n : ℤ) (α : I n), (SheafOfModules.extensionByZero.{u, u, u, u} O (U n α)).obj
    (SheafOfModules.unit (O.over (U n α))) ⟶ P.X n)
  (W : C) (S : ∀ n : ℤ, Finset (GenIdx (U n) W))

/-- **The sum of copies of `j_{W!} O_W` indexed by the generators of degree `n`.** -/
abbrev srcObj (n : ℤ) : SheafOfModules.{u} O :=
  ⨁ fun _ : Fin (S n).card => (SheafOfModules.extensionByZero.{u, u, u, u} O W).obj
    (SheafOfModules.unit (O.over W))

/-- **The enumeration of the generators of degree `n`.** -/
abbrev srcIdx (n : ℤ) (k : Fin (S n).card) : GenIdx (U n) W := ((S n).equivFin.symm k).1

/-- Each enumerated generator of degree `n` lies in `S n`. -/
theorem srcIdx_mem (n : ℤ) (k : Fin (S n).card) : srcIdx U W S n k ∈ S n :=
  ((S n).equivFin.symm k).2

/-- The enumeration of the generators of degree `n` is injective. -/
theorem srcIdx_injective (n : ℤ) : Function.Injective (srcIdx U W S n) := fun _ _ h =>
  (S n).equivFin.symm.injective (Subtype.ext h)

/-- **The map onto `P^n` from the sum of copies of `j_{W!} O_W`**, carrying the tautological
generator of the `k`-th summand to the `k`-th arrow generator. -/
def gMap (n : ℤ) : srcObj O U W S n ⟶ P.X n :=
  biproduct.desc fun k => SheafOfModules.fromExtensionByZero O (P.X n) W
    (genSec O (U n) (cofanP O P U ιP n) W (srcIdx U W S n k))

/-- The section of `srcObj` given by the tautological generator of the summand `k`. -/
abbrev srcGen (n : ℤ) (k : Fin (S n).card) : (srcObj O U W S n).val.obj (op W) :=
  (biproduct.ι (fun _ : Fin (S n).card =>
    (SheafOfModules.extensionByZero.{u, u, u, u} O W).obj
      (SheafOfModules.unit (O.over W))) k).val.app (op W)
    (SheafOfModules.extensionByZeroGen O W)

/-- `gMap` carries the tautological generator of the `k`-th summand to the `k`-th arrow
generator. -/
theorem gMap_srcGen (n : ℤ) (k : Fin (S n).card) :
    (gMap O P U ιP W S n).val.app (op W) (srcGen O U W S n k) =
      genSec O (U n) (cofanP O P U ιP n) W (srcIdx U W S n k) := by
  have h : biproduct.ι (fun _ : Fin (S n).card =>
      (SheafOfModules.extensionByZero.{u, u, u, u} O W).obj
        (SheafOfModules.unit (O.over W))) k ≫ gMap O P U ιP W S n =
      SheafOfModules.fromExtensionByZero O (P.X n) W
        (genSec O (U n) (cofanP O P U ιP n) W (srcIdx U W S n k)) := biproduct.ι_desc _ _
  exact (congrArg (fun φ => φ.val.app (op W) (SheafOfModules.extensionByZeroGen O W)) h).trans
    (SheafOfModules.fromExtensionByZero_val_app_gen O (P.X n) W _)

/-- `gMap` carries a combination of the tautological generators to the corresponding combination
of the arrow generators of degree `n`. -/
theorem gMap_sum_srcGen (n : ℤ)
    (f : GenIdx (U n) W → ((O.obj.obj (op W) : RingCat.{u}) : Type u)) :
    (gMap O P U ιP W S n).val.app (op W)
        (∑ k : Fin (S n).card, f (srcIdx U W S n k) • srcGen O U W S n k) =
      ∑ y ∈ S n, f y • genSec O (U n) (cofanP O P U ιP n) W y := by
  rw [map_sum,
    ← Finset.sum_coe_sort (S n) (fun y => f y • genSec O (U n) (cofanP O P U ιP n) W y),
    ← (S n).equivFin.symm.sum_comp]
  refine Fintype.sum_congr _ _ fun k => ?_
  rw [map_smul, gMap_srcGen]

/-- **With no generators in degree `n` the sum of copies of `j_{W!} O_W` is zero.** -/
theorem isZero_srcObj (n : ℤ) (hn : S n = ∅) : IsZero (srcObj O U W S n) := by
  have hempty : IsEmpty (Fin (S n).card) := by
    rw [hn, Finset.card_empty]
    infer_instance
  exact ⟨fun Y => ⟨⟨⟨0⟩, fun f => biproduct.hom_ext' _ _ fun k => hempty.elim k⟩⟩,
    fun Y => ⟨⟨⟨0⟩, fun f => biproduct.hom_ext _ _ fun k => hempty.elim k⟩⟩⟩

variable {O P U ιP W S}

variable (hd : ∀ n : ℤ, ∀ y ∈ S n,
  InSpan O (U (n + 1)) (cofanP O P U ιP (n + 1)) W ↑(S (n + 1))
    ((P.d n (n + 1)).val.app (op W) (genSec O (U n) (cofanP O P U ιP n) W y)))

/-- The coefficients of the differential of a generator in the generators of the next degree. -/
def coefD (n : ℤ) (k : Fin (S n).card) :
    GenIdx (U (n + 1)) W → ((O.obj.obj (op W) : RingCat.{u}) : Type u) :=
  Classical.choose (exists_coeff_of_inSpan O (U (n + 1)) (cofanP O P U ιP (n + 1))
    (hd n (srcIdx U W S n k) (srcIdx_mem U W S n k)))

/-- The differential of the `k`-th generator of degree `n` is the combination of the generators of
degree `n + 1` with coefficients `coefD hd n k`. -/
theorem coefD_spec (n : ℤ) (k : Fin (S n).card) :
    (P.d n (n + 1)).val.app (op W)
        (genSec O (U n) (cofanP O P U ιP n) W (srcIdx U W S n k)) =
      ∑ y ∈ S (n + 1), coefD hd n k y • genSec O (U (n + 1)) (cofanP O P U ιP (n + 1)) W y :=
  Classical.choose_spec (exists_coeff_of_inSpan O (U (n + 1)) (cofanP O P U ιP (n + 1))
    (hd n (srcIdx U W S n k) (srcIdx_mem U W S n k)))

/-- **The differential of the subcomplex, read on the sums of copies of `j_{W!} O_W`.** -/
def liftMap (n : ℤ) : srcObj O U W S n ⟶ srcObj O U W S (n + 1) :=
  biproduct.desc fun k => SheafOfModules.fromExtensionByZero O (srcObj O U W S (n + 1)) W
    (∑ l : Fin (S (n + 1)).card,
      coefD hd n k (srcIdx U W S (n + 1) l) • srcGen O U W S (n + 1) l)

/-- `liftMap` lifts the differential of `P` along `gMap`. -/
theorem liftMap_comm (n : ℤ) :
    liftMap hd n ≫ gMap O P U ιP W S (n + 1) = gMap O P U ιP W S n ≫ P.d n (n + 1) := by
  refine biproduct.hom_ext' _ _ fun k => ?_
  rw [liftMap, biproduct.ι_desc_assoc, fromExtensionByZero_comp, gMap_sum_srcGen, gMap,
    biproduct.ι_desc_assoc, fromExtensionByZero_comp, coefD_spec]

/-- **The subcomplex of `P` generated by the chosen arrow generators over `W`**: in degree `n`,
the image of the sum of copies of `j_{W!} O_W` indexed by the generators of degree `n`. This is
the object the proof of Stacks 0FPV calls `𝒦^•`. -/
abbrev subcomplex : CochainComplex (SheafOfModules.{u} O) ℤ := genSubcomplex (liftMap_comm hd)

/-- The inclusion of the subcomplex. -/
abbrev subcomplexι : subcomplex hd ⟶ P := genSubcomplexι (liftMap_comm hd)

/-- **Each term of the subcomplex is a quotient of a finite sum of copies of `j_{W!} O_W`.**
This is the sense in which the subcomplex is finitely generated, and it is all the source's
route asks of it: on a general site `j_{W!} O_W` restricted to the slice over `W` is free on
the *arrows* into `W`, so the term is not a direct summand of a finite free module and
`IsStrictlyPerfect` is unavailable for it. -/
theorem exists_epi_srcObj (n : ℤ) :
    ∃ π : srcObj O U W S n ⟶ (subcomplex hd).X n, Epi π :=
  exists_epi_image (srcObj O U W S) (gMap O P U ιP W S) n

/-- **A degree with no generators carries the zero module.** This is what bounds the
subcomplex below: the engine's set of generators is empty in degrees `< L`. -/
theorem isZero_subcomplex_X_of_eq_empty (n : ℤ) (hn : S n = ∅) :
    IsZero ((subcomplex hd).X n) :=
  isZero_image_of_isZero_src (srcObj O U W S) (gMap O P U ιP W S) n
    (isZero_srcObj O U W S n hn)

/-- **A degree where `P` vanishes carries the zero module.** This is what bounds the
subcomplex above, with no condition on where the generators live. -/
theorem isZero_subcomplex_X_of_isZero (n : ℤ) (hn : IsZero (P.X n)) :
    IsZero ((subcomplex hd).X n) :=
  isZero_image_of_isZero_tgt (srcObj O U W S) (gMap O P U ιP W S) n hn

/-- **Every section in the span of the generators of its degree lifts to the subcomplex.** -/
theorem exists_lift_of_inSpan {n : ℤ} {x : (P.X n).val.obj (op W)}
    (hx : InSpan O (U n) (cofanP O P U ιP n) W ↑(S n) x) :
    ∃ y : ((subcomplex hd).X n).val.obj (op W),
      ((subcomplexι hd).f n).val.app (op W) y = x := by
  obtain ⟨f, hf⟩ := exists_coeff_of_inSpan O (U n) (cofanP O P U ιP n) hx
  exact exists_lift_of_eq_app (liftMap_comm hd)
    ((gMap_sum_srcGen O P U ιP W S n f).trans hf.symm)

section Assembly

variable (O P U ιP)

variable [∀ n : ℤ, HasCoproduct fun α : I n =>
  (SheafOfModules.extensionByZero.{u, u, u, u} O (U n α)).obj
    (SheafOfModules.unit (O.over (U n α)))]

/-- **Over a covering sieve, a finitely generated subcomplex of `P` through which the given
sections factor.**

Over each member `W` of a covering sieve of `V` there is a cochain complex `K` and a
degreewise monomorphism `K ⟶ P`, each of whose terms is a quotient of a finite sum of copies
of `j_{W!} O_W`, which vanishes in the degrees `< L` and in the degrees where `P` vanishes, and
whose degree-`deg i` term carries a section mapping to the restriction of `s i`.

This is the object the proof of Stacks 0FPV calls `𝒦^•`, assembled from
`Stacks.Sites.ExtensionByZero.exists_sieve_closed_span`; it is the sieve-indexed replacement
for the ringed-space construction
`Stacks.Cohomology.LeftDualPerfect.subcomplex` over a shrunken open. -/
theorem exists_sieve_subcomplex (hc : ∀ n : ℤ, IsColimit (cofanP O P U ιP n)) (b L : ℤ)
    (hb : ∀ n : ℤ, b < n → IsZero (P.X n)) {V : C} {ι : Type*} (A : Finset ι) (deg : ι → ℤ)
    (hL : ∀ i ∈ A, L ≤ deg i) (s : ∀ i, (P.X (deg i)).val.obj (op V)) :
    ∃ T : Sieve V, T ∈ J V ∧ ∀ ⦃W : C⦄ (k : W ⟶ V), T k →
      ∃ (K : CochainComplex (SheafOfModules.{u} O) ℤ) (κ : K ⟶ P),
        (∀ n : ℤ, Mono (κ.f n)) ∧
        (∀ n : ℤ, ∃ (r : ℕ) (π : (⨁ fun _ : Fin r =>
          (SheafOfModules.extensionByZero.{u, u, u, u} O W).obj
            (SheafOfModules.unit (O.over W))) ⟶ K.X n), Epi π) ∧
        (∀ n : ℤ, n < L → IsZero (K.X n)) ∧
        (∀ n : ℤ, b < n → IsZero (K.X n)) ∧
        (∀ i ∈ A, ∃ t : (K.X (deg i)).val.obj (op W),
          (κ.f (deg i)).val.app (op W) t =
            (P.X (deg i)).val.restrictₛₗ k.op (s i)) := by
  obtain ⟨T, hT, hspec⟩ := exists_sieve_closed_span O P U ιP hc b L hb A deg hL s
  refine ⟨T, hT, fun {W} k hk => ?_⟩
  obtain ⟨S, hfin, hlow, hspan, hdS⟩ := hspec k hk
  have hcoe : ∀ n : ℤ, (↑((hfin n).toFinset) : Set (GenIdx (U n) W)) = S n :=
    fun n => (hfin n).coe_toFinset
  have hd : ∀ n : ℤ, ∀ y ∈ (hfin n).toFinset,
      InSpan O (U (n + 1)) (cofanP O P U ιP (n + 1)) W ↑((hfin (n + 1)).toFinset)
        ((P.d n (n + 1)).val.app (op W) (genSec O (U n) (cofanP O P U ιP n) W y)) := by
    intro n y hy
    rw [hcoe (n + 1)]
    exact hdS n y ((hfin n).mem_toFinset.1 hy)
  refine ⟨subcomplex hd, subcomplexι hd, fun n => inferInstance, fun n => ?_, fun n hn => ?_,
    fun n hn => ?_, fun i hi => ?_⟩
  · exact ⟨((hfin n).toFinset).card, exists_epi_srcObj hd n⟩
  · refine isZero_subcomplex_X_of_eq_empty hd n ?_
    rw [Set.Finite.toFinset_eq_empty]
    exact hlow n hn
  · exact isZero_subcomplex_X_of_isZero hd n (hb n hn)
  · refine exists_lift_of_inSpan hd ?_
    rw [hcoe (deg i)]
    exact hspan i hi

end Assembly

end Stacks.Sites.ExtensionByZero

end
