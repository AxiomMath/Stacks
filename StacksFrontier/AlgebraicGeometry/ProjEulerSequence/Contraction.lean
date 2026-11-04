module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.StalkEpiMono
public import StacksFrontier.AlgebraicGeometry.Divisors.ProjClosedSubschemeKernel
public import StacksFrontier.AlgebraicGeometry.ProjPolyChart.Cover
public import StacksFrontier.AlgebraicGeometry.ProjTrivialization.Basic
public import StacksFrontier.Homology.PseudoCoherentRelative.TildeFiniteFree

/-!
# The contraction map of the Euler sequence on projective space

Let `R` be a commutative ring, grade `R[T₀, …, Tₙ]` by total degree and write `X = Proj R[T]`
for projective `n`-space over `R`. Contraction with the coordinate `Tⱼ` is a morphism
`𝒪_X(-1) ⟶ 𝒪_X` of sheaves of modules, and the `n + 1` of them assemble into a morphism

`𝒪_X(-1)^{⊕ (n+1)} ⟶ 𝒪_X`

out of the direct sum, the row vector `(T₀, …, Tₙ)`. This file constructs that morphism and
proves it is an epimorphism; it is the surjection at the right-hand end of the Euler sequence.

Surjectivity is local and is witnessed by a splitting on each standard chart: on `D₊(Tᵢ)` the
element `Tᵢ` is invertible, so the `i`-th component of the row is already surjective there, the
preimage of a section being its quotient by `Tᵢ`. Since the charts `D₊(T₀), …, D₊(Tₙ)` cover
`X`, every section of `𝒪_X` is locally in the image.

## Main definitions

* `AlgebraicGeometry.ProjectiveSpectrum.Proj.twistMulLeftInt`: multiplication by a homogeneous
  element of degree `k`, as a morphism `𝒪(d) ⟶ 𝒪(k + d)` of twisting sheaves, with the source
  degree `d` an arbitrary integer.
* `Stacks.AlgebraicGeometry.ProjEulerSequence.contraction`: contraction with the coordinate
  `Tⱼ`, a morphism `𝒪_X(-1) ⟶ 𝒪_X`.
* `Stacks.AlgebraicGeometry.ProjEulerSequence.twistMinusOneFamily`: the constant family of
  `n + 1` copies of `𝒪_X(-1)`, whose direct sum is the source of the contraction.
* `Stacks.AlgebraicGeometry.ProjEulerSequence.eulerContraction`: the row `(T₀, …, Tₙ)`, a
  morphism `𝒪_X(-1)^{⊕ (n+1)} ⟶ 𝒪_X`.
* `Stacks.AlgebraicGeometry.ProjEulerSequence.invCoordSection`: the section `1 / Tᵢ` of
  `𝒪_X(-1)` over an open contained in `D₊(Tᵢ)`.
* `Stacks.AlgebraicGeometry.ProjEulerSequence.unitSection`: the unit section of `𝒪_X`.
* `Stacks.AlgebraicGeometry.ProjEulerSequence.eulerSection`: the local splitting over an open
  contained in `D₊(Tᵢ)`, the section of `𝒪_X(-1)^{⊕ (n+1)}` concentrated in the `i`-th summand
  with value `Tᵢ⁻¹`.

## Main results

* `AlgebraicGeometry.ProjectiveSpectrum.Proj.twistMulLeftInt_apply`: multiplication by `a` acts
  on a section fibrewise as the localization of multiplication by `a`.
* `AlgebraicGeometry.ProjectiveSpectrum.Proj.twistMulLeftInt_natCast`: at a nonnegative source
  degree it is `AlgebraicGeometry.ProjectiveSpectrum.Proj.twistMulLeft`.
* `AlgebraicGeometry.ProjectiveSpectrum.Proj.twistMulLeftInt_standardOpen`: on a standard open
  of positive degree it is multiplication by `a` in the localization.
* `Stacks.AlgebraicGeometry.ProjEulerSequence.contraction_apply`: contraction with `Tᵢ`
  multiplies the value of a section at each point by `Tᵢ`.
* `Stacks.AlgebraicGeometry.ProjEulerSequence.surjective_contraction_app`: over an open
  contained in `D₊(Tᵢ)`, contraction with `Tᵢ` is surjective on sections.
* `Stacks.AlgebraicGeometry.ProjEulerSequence.eulerContraction_app_biproduct_ι`: on sections,
  the contraction precomposed with the inclusion of the `i`-th summand is contraction with `Tᵢ`.
* `Stacks.AlgebraicGeometry.ProjEulerSequence.eulerContraction_app_eulerSection`: the
  contraction carries the local splitting to the unit section, so it is split on each chart.
* `Stacks.AlgebraicGeometry.ProjEulerSequence.epi_eulerContraction`: the contraction is an
  epimorphism.

## Implementation notes

`AlgebraicGeometry.ProjectiveSpectrum.Proj.twistMulLeft` takes its source degree in `ℕ`, so it
does not reach the degree `-1` that the Euler sequence needs;
`AlgebraicGeometry.ProjectiveSpectrum.Proj.twistMulLeftInt` is the same construction with the
source degree an integer, and `twistMulLeftInt_natCast` records that it extends the former.
Both are `Stacks.AlgebraicGeometry.ProjSheafFunctoriality.associatedModuleSheafMap` applied to
`LinearMap.mulLeft`, the degree side condition being
`AlgebraicGeometry.ProjectiveSpectrum.Proj.mul_mem_integerGrading`.

The direct sum is `CategoryTheory.Limits.biproduct`. `HasFiniteBiproducts` is not an instance for
sheaves of modules in Mathlib — `CategoryTheory.Abelian.hasFiniteBiproducts` is deliberately only
a local instance there — and the global instance
`Stacks.AffineTilde.hasFiniteBiproducts_modules` is stated for
`AlgebraicGeometry.Scheme.Modules`, which is a semireducible definition, so it is not found for
the sheaves of modules over
`Stacks.AlgebraicGeometry.ProjTrivialization.projRingSheaf` that the twisting sheaves are. It is
therefore supplied here as a `local instance` at that spelling, from
`CategoryTheory.Limits.HasFiniteBiproducts.of_hasFiniteProducts`. Working at the
`projRingSheaf` spelling rather than transporting the family to
`AlgebraicGeometry.Scheme.Modules` is what keeps the opens of the site spelled
`TopologicalSpace.Opens (AlgebraicGeometry.ProjectiveSpectrum.top 𝒮)`, which is the spelling
`AlgebraicGeometry.ProjectiveSpectrum.basicOpen` and the trivializations use; the two spellings
of the opens are definitionally equal but not interchangeable at the transparency `⊓` and the
epimorphy criterion elaborate at.

`invCoordSection` is built directly, as the fraction `1 / Tᵢ` with its local-fraction witness,
rather than taken from
`Stacks.AlgebraicGeometry.ProjTrivialization.trivializingSection`. The latter is indexed by the
degree `n * d` of the trivializing element `f ^ n`, so at `f = Tᵢ`, `d = 1` and `n = -1` its
degree argument reads `(-1) * ((1 : ℕ) : ℤ)`; reducing that to `-1` *and* projecting to the
sections of the twisting sheaf is a single unification that exhausts the heartbeat budget. Built
directly, every degree in the file is already a closed literal: contraction with `Tⱼ` is
`twistMulLeftInt` at `k = 1` and `d = -1`, whose target degree `((1 : ℕ) : ℤ) + (-1)` is
definitionally `0`, and no transport along an equality of degrees is needed anywhere.

For the same reason `contraction_apply` is stated with its section argument typed as
`AlgebraicGeometry.ProjectiveSpectrum.Proj.moduleSections` rather than as the sections of the
twisting sheaf: the two are definitionally equal, but with the latter spelling the coercion has
to be redone inside `rw`'s keyed matching at every use.

Epimorphy is proved from the section-level criterion
`Stacks.SheafOfModules.StalkEpiMono.epi_of_exists_sections`, not from a stalk computation. The
splitting is already available over a whole open `W ⊆ D₊(Tᵢ)`, so passing to germs would only
add work, and the stalk of the associated sheaf of a graded module is not described in this
library.

`eulerContraction_app_biproduct_ι` is proved in term mode, by `congrArg` along
`biproduct_ι_comp_eulerContraction`, rather than by rewriting with it. Rewriting replaces a
morphism whose source object is `twistMinusOneFamily R n i` by one whose source object is
`twistingSheaf 𝒮 (-1)`; the two are definitionally equal, but `rw` must build a motive in which
the section argument is retyped, and elaborating that motive does not terminate within the
heartbeat budget. Fixing the type of the morphism in the `congrArg` motive avoids the retyping
altogether.

## References

* [Stacks Project, Tag 0FMH](https://stacks.math.columbia.edu/tag/0FMH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpectrum.Proj

namespace AlgebraicGeometry.ProjectiveSpectrum.Proj

universe u w

attribute [local instance] ProjectiveSpectrum.isPrime
attribute [local implicit_reducible] TopCat.Sheaf sheafCompose
attribute [local instance_reducible] ProjectiveSpectrum.top

variable {S : Type u} [CommRing S] {σ : Type w} [SetLike σ S] [AddSubgroupClass σ S]
  (𝒮 : ℕ → σ) [GradedRing 𝒮]

/-- Multiplication by a homogeneous element `a` of degree `k`, as a morphism
`𝒪_{Proj 𝒮}(d) ⟶ 𝒪_{Proj 𝒮}(k + d)` of twisting sheaves, for an arbitrary integer degree `d`.
Multiplication by `a` raises the degree of a homogeneous element by `k`, so it is a
degree-preserving map of the graded modules `S(d) ⟶ S(k + d)`. -/
def twistMulLeftInt {k : ℕ} (a : 𝒮 k) (d : ℤ) :
    twistingSheaf 𝒮 d ⟶ twistingSheaf 𝒮 ((k : ℤ) + d) :=
  Stacks.AlgebraicGeometry.ProjSheafFunctoriality.associatedModuleSheafMap 𝒮
    (twistGrading (S := S) 𝒮 d) (twistGrading (S := S) 𝒮 ((k : ℤ) + d))
    (LinearMap.mulLeft S (a : S)) <| by
      intro j x hx
      have h := mul_mem_integerGrading 𝒮 a.2 (j := j + d) hx
      have he : (k : ℤ) + (j + d) = j + ((k : ℤ) + d) := by ring
      rw [he] at h
      exact h

/-- Multiplication by `a` acts on a section of `𝒪(d)` fibrewise, as the localization of
multiplication by `a` at each homogeneous prime. -/
theorem twistMulLeftInt_apply {k : ℕ} (a : 𝒮 k) (d : ℤ)
    (U : (Opens (ProjectiveSpectrum.top 𝒮))ᵒᵖ) (s : (twistingSheaf 𝒮 d).val.obj U)
    (x : U.unop) :
    ((twistMulLeftInt 𝒮 a d).val.app U s).1 x =
      LocalizedModule.map x.1.asHomogeneousIdeal.toIdeal.primeCompl
        (LinearMap.mulLeft S (a : S)) (s.1 x) :=
  rfl

/-- At a nonnegative source degree, multiplication by `a` in integer degrees is the map
`AlgebraicGeometry.ProjectiveSpectrum.Proj.twistMulLeft` already attached to natural-number
degrees. -/
theorem twistMulLeftInt_natCast {k : ℕ} (a : 𝒮 k) (m : ℕ) :
    twistMulLeftInt 𝒮 a (m : ℤ) = twistMulLeft 𝒮 a m :=
  rfl

/-- On a standard open `D₊(f)` of positive degree, multiplication by `a` is multiplication by
`a` in the localization `S_f`, read through the identification of the sections of `𝒪(d)` over
`D₊(f)` with the degree-zero part of `S(d)_f`. -/
theorem twistMulLeftInt_standardOpen {k : ℕ} (a : 𝒮 k) (d : ℤ) {f : S} {e : ℕ} (hf : f ∈ 𝒮 e)
    (he : 0 < e) (s : (twistingSheaf 𝒮 d).val.obj (op (ProjectiveSpectrum.basicOpen 𝒮 f))) :
    ((associatedModuleSheafStandardOpenEquiv 𝒮 (twistGrading (S := S) 𝒮 ((k : ℤ) + d)) hf he
          ((twistMulLeftInt 𝒮 a d).val.app _ s) :
        GradedModuleDegreeZeroLocalization 𝒮 (twistGrading (S := S) 𝒮 ((k : ℤ) + d)) f) :
          LocalizedModule.Away (R := S) f S) =
      LocalizedModule.map (Submonoid.powers f) (LinearMap.mulLeft S (a : S))
        (associatedModuleSheafStandardOpenEquiv 𝒮 (twistGrading (S := S) 𝒮 d) hf he s :
          GradedModuleDegreeZeroLocalization 𝒮 (twistGrading (S := S) 𝒮 d) f) :=
  Stacks.AlgebraicGeometry.ProjSheafFunctoriality.associatedModuleSheafMap_standardOpen 𝒮
    (twistGrading (S := S) 𝒮 d) (twistGrading (S := S) 𝒮 ((k : ℤ) + d))
    (LinearMap.mulLeft S (a : S)) _ hf he s

end AlgebraicGeometry.ProjectiveSpectrum.Proj

namespace Stacks.AlgebraicGeometry.ProjEulerSequence

universe u

open Stacks.AlgebraicGeometry.ProjPolyChart
open Stacks.AlgebraicGeometry.ProjTrivialization

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local implicit_reducible] TopCat.Sheaf sheafCompose
attribute [local instance_reducible] ProjectiveSpectrum.top

variable (R : Type u) [CommRing R] (n : ℕ)

/-- The homogeneous ideal of a point of `Proj R[T₀, …, Tₙ]` is prime. -/
local instance (x : ProjectiveSpectrum.top (polyGrading R n)) :
    x.asHomogeneousIdeal.toIdeal.IsPrime :=
  x.isPrime

/-- Multiplication by a ring element, read in a localization of the ring: the localization of
`LinearMap.mulLeft` is multiplication by the image of the element. -/
private theorem map_mulLeft_eq {A : Type u} [CommRing A] {P : Submonoid A} (a : A)
    (z : Localization P) :
    LocalizedModule.map P (LinearMap.mulLeft A a) z = Localization.mk a 1 * z := by
  induction z using Localization.induction_on with
  | H y =>
    show LocalizedModule.map P (LinearMap.mulLeft A a) (LocalizedModule.mk y.1 y.2) = _
    rw [LocalizedModule.map_mk, Localization.mk_mul]
    simp only [LinearMap.mulLeft_apply, one_mul]
    rfl

/-- An element of a submonoid times its inverse in the localization is `1`. -/
private theorem mk_mul_mk_one_self {A : Type u} [CommRing A] {P : Submonoid A} (a : A)
    (h : a ∈ P) : (Localization.mk a 1 : Localization P) * Localization.mk 1 ⟨a, h⟩ = 1 := by
  rw [Localization.mk_mul, mul_one, one_mul]
  exact Localization.mk_self (⟨a, h⟩ : P)

/-- **Contraction with the coordinate `Tⱼ`**: the morphism `𝒪_X(-1) ⟶ 𝒪_X` of sheaves of
modules on `X = Proj R[T₀, …, Tₙ]` given by multiplication by `Tⱼ`, which is homogeneous of
degree one. -/
def contraction (j : Fin (n + 1)) :
    twistingSheaf (polyGrading R n) (-1) ⟶ twistingSheaf (polyGrading R n) 0 :=
  twistMulLeftInt (polyGrading R n)
    (⟨MvPolynomial.X j, X_mem_one R n j⟩ : polyGrading R n 1) (-1)

/-- Contraction with `Tᵢ` multiplies the value of a section at each point by `Tᵢ`. -/
theorem contraction_apply (i : Fin (n + 1))
    (W : Opens (ProjectiveSpectrum.top (polyGrading R n)))
    (s : moduleSections (polyGrading R n) (twistGrading (polyGrading R n) (-1)) W) (x : W) :
    ((contraction R n i).val.app (op W) s).1 x =
      Localization.mk (MvPolynomial.X i : MvPolynomial (Fin (n + 1)) R) 1 * s.1 x := by
  have h : ((contraction R n i).val.app (op W) s).1 x =
      LocalizedModule.map x.1.asHomogeneousIdeal.toIdeal.primeCompl
        (LinearMap.mulLeft (MvPolynomial (Fin (n + 1)) R)
          (MvPolynomial.X i : MvPolynomial (Fin (n + 1)) R)) (s.1 x) := rfl
  rw [h, map_mulLeft_eq]

/-- The constant family of `n + 1` copies of `𝒪_X(-1)`, indexed by the coordinates of
`X = Proj R[T₀, …, Tₙ]`. Its direct sum is the source of the Euler contraction. -/
def twistMinusOneFamily : Fin (n + 1) → SheafOfModules.{u} (projRingSheaf (polyGrading R n)) :=
  fun _ => twistingSheaf (polyGrading R n) (-1)

/-- Applying a composite of morphisms of sheaves of modules to a section is applying the two
morphisms in turn. -/
private theorem comp_val_app
    {M N P : SheafOfModules.{u} (projRingSheaf (polyGrading R n))} (f : M ⟶ N) (g : N ⟶ P)
    (U : (Opens (ProjectiveSpectrum.top (polyGrading R n)))ᵒᵖ) (s : M.val.obj U) :
    (f ≫ g).val.app U s = g.val.app U (f.val.app U s) :=
  rfl

/-- **The Euler contraction** `𝒪_X(-1)^{⊕ (n+1)} ⟶ 𝒪_X` on `X = Proj R[T₀, …, Tₙ]`: the row
vector `(T₀, …, Tₙ)`, whose `j`-th component is contraction with the coordinate `Tⱼ`. -/
def eulerContraction :
    (⨁ twistMinusOneFamily R n) ⟶ twistingSheaf (polyGrading R n) 0 :=
  biproduct.desc fun j => contraction R n j

/-- The `j`-th component of the Euler contraction is contraction with the coordinate `Tⱼ`. -/
@[simp]
theorem biproduct_ι_comp_eulerContraction (j : Fin (n + 1)) :
    biproduct.ι (twistMinusOneFamily R n) j ≫ eulerContraction R n = contraction R n j :=
  biproduct.ι_desc _ _

/-- The section `1 / Tᵢ` of `𝒪_X(-1)` over an open contained in `D₊(Tᵢ)`. It makes sense there
because `Tᵢ` is invertible on `D₊(Tᵢ)`, and it is a section of `𝒪(-1)` rather than of `𝒪_X`
because its numerator has degree one less than its denominator. -/
def invCoordSection (i : Fin (n + 1))
    {W : Opens (ProjectiveSpectrum.top (polyGrading R n))}
    (hW : W ≤ ProjectiveSpectrum.basicOpen (polyGrading R n) (MvPolynomial.X i)) :
    moduleSections (polyGrading R n) (twistGrading (polyGrading R n) (-1)) W :=
  ⟨fun x => LocalizedModule.mk 1 ⟨MvPolynomial.X i, hW x.2⟩,
    fun x => ⟨W, x.2, 𝟙 _, 1, 1, MvPolynomial.X i,
      mem_integerGrading_natCast (polyGrading R n)
        (SetLike.one_mem_graded (polyGrading R n)),
      X_mem_one R n i, fun y => hW y.2, fun _ => rfl⟩⟩

/-- The unit section of `𝒪_X` over an open of `Proj R[T₀, …, Tₙ]`, with value `1` in every
local ring. -/
def unitSection (W : Opens (ProjectiveSpectrum.top (polyGrading R n))) :
    moduleSections (polyGrading R n) (twistGrading (polyGrading R n) 0) W :=
  ⟨fun _ => LocalizedModule.mk 1 1,
    fun x => ⟨W, x.2, 𝟙 _, 0, 1, 1,
      mem_integerGrading_natCast (polyGrading R n)
        (SetLike.one_mem_graded (polyGrading R n)),
      SetLike.one_mem_graded (polyGrading R n),
      fun y => y.1.isPrime.one_notMem, fun _ => rfl⟩⟩

/-- The unit section is `1` in every local ring. -/
theorem unitSection_apply (W : Opens (ProjectiveSpectrum.top (polyGrading R n)))
    (x : W) : (unitSection R n W).1 x = 1 :=
  Localization.mk_one

/-- **Contraction with `Tᵢ` carries `1 / Tᵢ` to `1`.** This is the identity that splits the
`i`-th component of the Euler contraction over `D₊(Tᵢ)`. -/
theorem contraction_app_invCoordSection (i : Fin (n + 1))
    {W : Opens (ProjectiveSpectrum.top (polyGrading R n))}
    (hW : W ≤ ProjectiveSpectrum.basicOpen (polyGrading R n) (MvPolynomial.X i)) :
    (contraction R n i).val.app (op W) (invCoordSection R n i hW) = unitSection R n W := by
  refine Subtype.ext (funext fun x => ?_)
  rw [contraction_apply]
  show Localization.mk (MvPolynomial.X i : MvPolynomial (Fin (n + 1)) R) 1 *
      Localization.mk 1 ⟨MvPolynomial.X i, hW x.2⟩ = Localization.mk 1 1
  exact (mk_mul_mk_one_self _ _).trans Localization.mk_one.symm

/-- Dividing a section of `𝒪_X` by `Tᵢ`, pointwise, on an open contained in `D₊(Tᵢ)`. -/
private def divFun (i : Fin (n + 1))
    {W : Opens (ProjectiveSpectrum.top (polyGrading R n))}
    (hW : W ≤ ProjectiveSpectrum.basicOpen (polyGrading R n) (MvPolynomial.X i))
    (s : moduleSections (polyGrading R n) (twistGrading (polyGrading R n) 0) W) (x : W) :
    ModuleFiber (M := MvPolynomial (Fin (n + 1)) R) (polyGrading R n) x.1 :=
  Localization.mk 1 ⟨MvPolynomial.X i, hW x.2⟩ * s.1 x

/-- Dividing a section of `𝒪_X` by `Tᵢ` gives a section of `𝒪_X(-1)`: a local fraction `m / v`
of `𝒪_X`, with `m` and `v` of the same degree `k`, becomes `m / (Tᵢ v)`, whose numerator has
degree one less than its denominator. -/
private theorem divFun_mem (i : Fin (n + 1))
    {W : Opens (ProjectiveSpectrum.top (polyGrading R n))}
    (hW : W ≤ ProjectiveSpectrum.basicOpen (polyGrading R n) (MvPolynomial.X i))
    (s : moduleSections (polyGrading R n) (twistGrading (polyGrading R n) 0) W) :
    divFun R n i hW s ∈
      moduleSections (polyGrading R n) (twistGrading (polyGrading R n) (-1)) W := by
  intro x
  obtain ⟨V, hxV, ιV, k, m, v, hm, hv, hnin, heq⟩ := s.2 x
  refine ⟨V, hxV, ιV, 1 + k, m, MvPolynomial.X i * v, ?_,
    SetLike.mul_mem_graded (X_mem_one R n i) hv,
    fun y => y.1.asHomogeneousIdeal.toIdeal.primeCompl.mul_mem (hW (ιV y).2) (hnin y),
    fun y => ?_⟩
  · have he : (((1 + k : ℕ) : ℤ) + (-1)) = ((k : ℤ) + 0) := by push_cast; ring
    show m ∈ integerGrading (polyGrading R n) (((1 + k : ℕ) : ℤ) + (-1))
    rw [he]
    exact hm
  · have hy : s.1 (ιV y) = Localization.mk m ⟨v, hnin y⟩ := heq y
    show Localization.mk 1 ⟨MvPolynomial.X i, hW (ιV y).2⟩ * s.1 (ιV y) = _
    rw [hy, Localization.mk_mul]
    exact Localization.mk_eq_mk_iff.mpr (Localization.r_of_eq (by simp))

/-- Over an open contained in `D₊(Tᵢ)`, contraction with `Tᵢ` is surjective on sections: the
preimage of a section `s` is `s / Tᵢ`. -/
theorem surjective_contraction_app (i : Fin (n + 1))
    {W : Opens (ProjectiveSpectrum.top (polyGrading R n))}
    (hW : W ≤ ProjectiveSpectrum.basicOpen (polyGrading R n) (MvPolynomial.X i)) :
    Function.Surjective ((contraction R n i).val.app (op W)) := by
  intro s
  refine ⟨⟨divFun R n i hW s, divFun_mem R n i hW s⟩, Subtype.ext (funext fun x => ?_)⟩
  rw [contraction_apply]
  show Localization.mk (MvPolynomial.X i : MvPolynomial (Fin (n + 1)) R) 1 *
      (Localization.mk 1 ⟨MvPolynomial.X i, hW x.2⟩ * s.1 x) = s.1 x
  rw [← mul_assoc, mk_mul_mk_one_self _ (hW x.2), one_mul]

/-- **The local splitting of the Euler contraction.** Over an open contained in `D₊(Tᵢ)`, the
section of `𝒪_X(-1)^{⊕ (n+1)}` concentrated in the `i`-th summand with value `1 / Tᵢ`. -/
def eulerSection (i : Fin (n + 1))
    {W : Opens (ProjectiveSpectrum.top (polyGrading R n))}
    (hW : W ≤ ProjectiveSpectrum.basicOpen (polyGrading R n) (MvPolynomial.X i)) :
    (⨁ twistMinusOneFamily R n).val.obj (op W) :=
  (biproduct.ι (twistMinusOneFamily R n) i).val.app (op W) (invCoordSection R n i hW)

/-- On sections, the Euler contraction precomposed with the inclusion of the `i`-th summand is
contraction with `Tᵢ`. -/
theorem eulerContraction_app_biproduct_ι (i : Fin (n + 1))
    (W : Opens (ProjectiveSpectrum.top (polyGrading R n)))
    (r : (twistingSheaf (polyGrading R n) (-1)).val.obj (op W)) :
    (eulerContraction R n).val.app (op W)
        ((biproduct.ι (twistMinusOneFamily R n) i).val.app (op W) r) =
      (contraction R n i).val.app (op W) r :=
  (comp_val_app R n (biproduct.ι (twistMinusOneFamily R n) i) (eulerContraction R n)
      (op W) r).symm.trans
    (congrArg (fun φ : twistMinusOneFamily R n i ⟶ twistingSheaf (polyGrading R n) 0 =>
        φ.val.app (op W) r) (biproduct_ι_comp_eulerContraction R n i))

/-- **The Euler contraction is split on each standard chart.** It carries the local splitting
over an open contained in `D₊(Tᵢ)` to the unit section of `𝒪_X`, because `Tᵢ · Tᵢ⁻¹ = 1`. -/
theorem eulerContraction_app_eulerSection (i : Fin (n + 1))
    {W : Opens (ProjectiveSpectrum.top (polyGrading R n))}
    (hW : W ≤ ProjectiveSpectrum.basicOpen (polyGrading R n) (MvPolynomial.X i)) :
    (eulerContraction R n).val.app (op W) (eulerSection R n i hW) = unitSection R n W :=
  (eulerContraction_app_biproduct_ι R n i W (invCoordSection R n i hW)).trans
    (contraction_app_invCoordSection R n i hW)

/-- Every point of `Proj R[T₀, …, Tₙ]` lies on one of the standard charts `D₊(Tᵢ)`: a
homogeneous prime not containing the irrelevant ideal omits some coordinate. -/
theorem exists_mem_basicOpen_X (x : ProjectiveSpectrum.top (polyGrading R n)) :
    ∃ i : Fin (n + 1),
      x ∈ ProjectiveSpectrum.basicOpen (polyGrading R n) (MvPolynomial.X i) := by
  have hx : x ∈ (⨆ i : Fin (n + 1),
      _root_.AlgebraicGeometry.Proj.basicOpen (polyGrading R n) (MvPolynomial.X i)) := by
    rw [iSup_basicOpen_X_eq_top]
    exact Opens.mem_top x
  obtain ⟨i, hi⟩ := Opens.mem_iSup.1 hx
  exact ⟨i, hi⟩

/-- **The Euler contraction is an epimorphism.** Every section of `𝒪_X` is locally in the image:
each point lies on some standard chart `D₊(Tᵢ)`, and on that chart contraction with `Tᵢ` — the
`i`-th component of the row — is already surjective, with inverse division by `Tᵢ`. -/
theorem epi_eulerContraction : Epi (eulerContraction R n) := by
  refine Stacks.SheafOfModules.StalkEpiMono.epi_of_exists_sections _ fun U t x hxU => ?_
  obtain ⟨i, hxi⟩ := exists_mem_basicOpen_X R n x
  refine ⟨U ⊓ ProjectiveSpectrum.basicOpen (polyGrading R n) (MvPolynomial.X i),
    inf_le_left, ⟨hxU, hxi⟩, ?_⟩
  obtain ⟨r, hr⟩ := surjective_contraction_app R n i (W := U ⊓
      ProjectiveSpectrum.basicOpen (polyGrading R n) (MvPolynomial.X i)) inf_le_right
    ((twistingSheaf (polyGrading R n) 0).val.map (homOfLE inf_le_left).op t)
  exact ⟨(biproduct.ι (twistMinusOneFamily R n) i).val.app
      (op (U ⊓ ProjectiveSpectrum.basicOpen (polyGrading R n) (MvPolynomial.X i))) r,
    (eulerContraction_app_biproduct_ι R n i
      (U ⊓ ProjectiveSpectrum.basicOpen (polyGrading R n) (MvPolynomial.X i)) r).trans hr⟩

end Stacks.AlgebraicGeometry.ProjEulerSequence

end
