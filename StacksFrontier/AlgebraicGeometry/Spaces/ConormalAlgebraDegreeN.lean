module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EpiLocallySurjective
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ULiftUnit
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionModuleEssentialImage
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalAlgebra
public import StacksFrontier.AlgebraicGeometry.Spaces.IdealPowerModule
public import StacksFrontier.CategoryTheory.Sites.ClosedImmersion.ConormalAlgebra

/-!
# The conormal algebra of a closed subspace of an algebraic space in every degree

Let `X` be an algebraic space over a scheme `S` contained in a big fppf site `B`, let `Z` be a
closed subspace of `X` with inclusion `i : Z ⟶ X`, and let `𝓘 ⊆ 𝒪_X` be its defining ideal
sheaf on the small étale site of `X`, the sheaf of ideals of Stacks 03MB.  The degree-`n` piece
of the conormal algebra of `Z` in `X` is the `𝒪_Z`-module `𝒞_{Z/X, n}` characterized by

`i_*𝒞_{Z/X, n} = 𝓘ⁿ/𝓘ⁿ⁺¹`.

This file proves that equation, in every degree, for the degree-`n` piece
`AlgebraicGeometry.Space.conormalAlgebraPiece` this development already constructs, namely the
inverse image `i^*(𝓘ⁿ)` of the `n`-th power of the defining ideal sheaf.

The argument is in three steps.  The product law `𝓘 · 𝓘ⁿ ⊆ 𝓘ⁿ⁺¹` makes `𝓘` annihilate the
quotient `𝓘ⁿ/𝓘ⁿ⁺¹`, so that quotient is a direct image along `i` by the essential-image clause
of Stacks 04CJ, part (3) — equivalently, the unit `𝓘ⁿ/𝓘ⁿ⁺¹ ⟶ i_*i^*(𝓘ⁿ/𝓘ⁿ⁺¹)` of the adjunction
of Stacks 03LU is an isomorphism.  The same product law makes the inverse image of the inclusion
`𝓘ⁿ⁺¹ ⟶ 𝓘ⁿ` vanish, because its adjunct is a map into an `𝓘`-annihilated module.  Inverse image
preserves cokernels, so `i^*(𝓘ⁿ/𝓘ⁿ⁺¹)` is the cokernel of a zero map out of `i^*(𝓘ⁿ⁺¹)`, that is
`i^*(𝓘ⁿ) = 𝒞_{Z/X, n}` itself.  Combining the two gives the equation.

The first two steps are statements about an arbitrary sheaf of ideals on an arbitrary site and are
proved there, in `Stacks.IdealPowerSheaf`.

## Main definitions

* `Stacks.IdealPowerSheaf.gradedPiece` and `Stacks.IdealPowerSheaf.gradedPieceπ`: the quotient
  `ℐⁿ/ℐⁿ⁺¹` of consecutive powers of a sheaf of ideals, and the projection onto it.
* `Stacks.IdealPowerSheaf.idealPowKer`: the sections of `ℐⁿ` killed by a morphism out of `ℐⁿ`,
  as a sheaf of ideals.  It is the submodule against which the inductive description of `ℐⁿ⁺¹` is
  tested.
* `AlgebraicGeometry.Space.definingIdealPowModule` and
  `AlgebraicGeometry.Space.definingIdealPowSuccHom`: the power `𝓘ⁿ` of the defining ideal sheaf of
  a closed subspace as an `𝒪_X`-module, and the inclusion `𝓘ⁿ⁺¹ ⟶ 𝓘ⁿ`.
* `AlgebraicGeometry.Space.conormalGradedPiece`: that quotient for the defining ideal sheaf of a
  closed subspace of an algebraic space.
* `AlgebraicGeometry.Space.pullbackConormalGradedPieceIso`: the identification
  `i^*(𝓘ⁿ/𝓘ⁿ⁺¹) ≅ 𝒞_{Z/X, n}`.
* `AlgebraicGeometry.Space.moduleUnitIsoOfEssImage` and
  `AlgebraicGeometry.Space.pushforwardIsoOfPullbackIso`: the unit of Stacks 03LU inverted at a
  module in the essential image of the direct image, and the identification `f_*C ≅ G` it gives
  from an identification `f^*G ≅ C`.  Both are general in the modules, for the reason in the
  implementation notes.
* `AlgebraicGeometry.Space.conormalAlgebraPiecePushforwardIso`: **Stacks 09RP**, the equation
  `i_*𝒞_{Z/X, n} = 𝓘ⁿ/𝓘ⁿ⁺¹`.
* `AlgebraicGeometry.Space.isoConormalAlgebraPiece`: the uniqueness that makes that equation an
  identification — any `𝒪_Z`-module whose direct image is `𝓘ⁿ/𝓘ⁿ⁺¹` is isomorphic to
  `𝒞_{Z/X, n}`.

## Main results

* `Stacks.IdealPowerSheaf.smul_mem_idealPow_succ'`: the product law `ℐ · ℐⁿ ⊆ ℐⁿ⁺¹` in every
  degree, including `n = 0`.
* `Stacks.IdealPowerSheaf.smul_gradedPiece_eq_zero`: a section of `ℐ` annihilates `ℐⁿ/ℐⁿ⁺¹`.
* `Stacks.IdealPowerSheaf.idealPowSuccHom_comp_eq_zero`: a morphism from `ℐⁿ` to a module
  annihilated by `ℐ` kills `ℐⁿ⁺¹`.
* `AlgebraicGeometry.Space.annihilatedByKerIdeal_conormalGradedPiece`,
  `AlgebraicGeometry.Space.essImage_modulePushforward_conormalGradedPiece` and
  `AlgebraicGeometry.Space.isIso_unit_conormalGradedPiece`: `𝓘` annihilates `𝓘ⁿ/𝓘ⁿ⁺¹`, so that
  quotient is a direct image along `i` and the unit of Stacks 03LU is invertible there.
* `AlgebraicGeometry.Space.modulePullback_map_idealPowSuccHom_eq_zero`:
  `i^*(𝓘ⁿ⁺¹ ⟶ 𝓘ⁿ) = 0`.
* `CategoryTheory.Adjunction.leftAdjoint_map_eq_zero_of_comp_unit_eq_zero`: the adjunction
  calculus behind it — a morphism whose composite with the unit vanishes has vanishing image
  under the left adjoint.

## Implementation notes

**Why the annihilation is proved through a covering.**  A section of the cokernel `ℐⁿ/ℐⁿ⁺¹` over
an object of the site need not be the image of a section of `ℐⁿ` over that object; the projection
is only an epimorphism, hence only locally surjective
(`Stacks.SheafOfModules.EpiMono.exists_covering_of_epi`).  So a section of `ℐ` is multiplied into
a lift over each arrow of a covering sieve, where the product law applies, and the resulting local
vanishing is promoted by separatedness
(`Stacks.SheafOfModules.eq_zero_of_locally_eq_zero`).

**Why `ℐⁿ⁺¹` is tested against a submodule rather than described locally.**
`Stacks.IdealPowerSheaf.idealPow` is defined as an infimum: `ℐⁿ⁺¹` is the *smallest* sheaf
submodule of `𝒪` containing every product of a section of `ℐ` with a section of `ℐⁿ`.  There is
therefore no local description of its sections to induct over, only the elimination rule
`sInf_le`, which asks for a sheaf submodule of `𝒪` closed under those products.  That submodule is
`Stacks.IdealPowerSheaf.idealPowKer`, the image in `𝒪` of the kernel of the given morphism out of
`ℐⁿ`; its locality is separatedness of the target, exactly as for
`CategoryTheory.SheafOfModules.Submodule.ker`.  The degree-zero case is separate, `ℐ¹ = ℐ` being a
branch of the recursion rather than an infimum, and is the observation that a section `a` of `ℐ`
is `a · 1` with `1` a section of `ℐ⁰ = 𝒪`.

**Why the inverse image of the inclusion vanishes.**  It is not the inverse image of a zero map:
the inclusion `𝓘ⁿ⁺¹ ⟶ 𝓘ⁿ` is a monomorphism.  What vanishes is its adjunct, the composite
`𝓘ⁿ⁺¹ ⟶ 𝓘ⁿ ⟶ i_*i^*(𝓘ⁿ)`, whose target is annihilated by `𝓘` because it is a direct image
(Stacks 04CJ, part (3)); the triangle identity of the adjunction then returns the inverse image
itself, and the inverse image carries the zero morphism to the zero morphism because it is a left
adjoint.

**Why the two steps are proved on an arbitrary site.**  Both are computations with sections, and on
the small étale site of an algebraic space the category of the site, its objects and the sections
of its structure sheaf each have two spellings that agree only after unfolding — which the
elaborator will not do at the transparency a rewrite's type-correctness check uses.  Stated for a
sheaf of ideals of an arbitrary sheaf of rings on an arbitrary site, nothing has to be unfolded,
and the statements then specialize to the defining ideal sheaf with no work.

**Why the inversion of the unit is done in a statement general in the module.**  This is the
discipline the implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/ConormalModuleFirstOrderIdeal.lean` record:
`AlgebraicGeometry.Space.modulePullbackAdjunction` and
`AlgebraicGeometry.Space.modulePushforward` are definitions over the small étale ringed site, and
every restatement of the type of one of their components costs a definitional unfolding of that
site, the more so when the module is a cokernel.  So
`AlgebraicGeometry.Space.moduleUnitIsoOfEssImage` and
`AlgebraicGeometry.Space.pushforwardIsoOfPullbackIso` take the closed immersion and the modules as
variables, where the terms are small, and Stacks 09RP is their instance — an application whose
arguments are checked with no unfolding.  The first is
`AlgebraicGeometry.Space.submoduleUnitIsoOfEssImage` with the submodule of `𝒪_X` generalized to a
module, which is what a quotient of two ideal powers needs.

## References

* [Stacks Project, Tag 09RP](https://stacks.math.columbia.edu/tag/09RP)
* [Stacks Project, Tag 09RN](https://stacks.math.columbia.edu/tag/09RN)
* [Stacks Project, Tag 03MB](https://stacks.math.columbia.edu/tag/03MB)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 04CJ](https://stacks.math.columbia.edu/tag/04CJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

attribute [local implicit_reducible] SheafOfModules.unit PresheafOfModules.unit

universe w v₁ u₁ u

namespace Stacks.IdealPowerSheaf

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w}}
  [HasSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  (I : (SheafOfModules.unit R).Submodule)

/-! ### The product law in every degree -/

omit [HasSheafify J AddCommGrpCat] [J.WEqualsLocallyBijective AddCommGrpCat] in
/-- Every section of the structure sheaf is a section of the zeroth power of a sheaf of ideals,
that power being the whole structure sheaf. -/
theorem mem_idealPow_zero (U : Cᵒᵖ) (m : (SheafOfModules.unit R).val.obj U) :
    m ∈ (idealPow I 0).obj U := by
  rw [idealPow_zero]
  exact Stacks.SheafOfModules.mem_top_obj m

omit [HasSheafify J AddCommGrpCat] [J.WEqualsLocallyBijective AddCommGrpCat] in
/-- **The product law `ℐ · ℐⁿ ⊆ ℐⁿ⁺¹` in every degree.**  For `n ≥ 1` this is
`Stacks.IdealPowerSheaf.smul_mem_idealPow_succ`; for `n = 0` it is
`Stacks.IdealPowerSheaf.smul_mem_idealPow_one`, which needs the sections of the structure sheaf to
commute. -/
theorem smul_mem_idealPow_succ' (hcomm : ∀ (V : Cᵒᵖ) (a b : R.obj.obj V), a * b = b * a) (n : ℕ)
    (U : Cᵒᵖ) (a : R.obj.obj U) (ha : a ∈ I.obj U)
    (m : (SheafOfModules.unit R).val.obj U) (hm : m ∈ (idealPow I n).obj U) :
    a • m ∈ (idealPow I (n + 1)).obj U := by
  cases n with
  | zero => exact smul_mem_idealPow_one I hcomm U a ha m
  | succ k => exact smul_mem_idealPow_succ I k U a ha m hm

/-! ### The graded piece `ℐⁿ/ℐⁿ⁺¹` -/

/-- **The degree-`n` graded piece `ℐⁿ/ℐⁿ⁺¹` of a sheaf of ideals**: the cokernel of the inclusion
of consecutive powers. -/
def gradedPiece (n : ℕ) : SheafOfModules.{w} R := cokernel (idealPowSuccHom I n)

/-- The projection `ℐⁿ ⟶ ℐⁿ/ℐⁿ⁺¹`. -/
def gradedPieceπ (n : ℕ) : (idealPow I n).toSheafOfModules ⟶ gradedPiece I n :=
  cokernel.π (idealPowSuccHom I n)

/-- The projection `ℐⁿ ⟶ ℐⁿ/ℐⁿ⁺¹` is an epimorphism. -/
instance epi_gradedPieceπ (n : ℕ) : Epi (gradedPieceπ I n) :=
  inferInstanceAs (Epi (cokernel.π _))

/-- The sections of `ℐⁿ⁺¹` die in `ℐⁿ/ℐⁿ⁺¹`. -/
theorem gradedPieceπ_idealPowSuccHom_apply (n : ℕ) (W : Cᵒᵖ)
    (y : (idealPow I (n + 1)).toSheafOfModules.val.obj W) :
    (gradedPieceπ I n).val.app W ((idealPowSuccHom I n).val.app W y) = 0 := by
  have h := congrArg
    (fun φ : (idealPow I (n + 1)).toSheafOfModules ⟶ gradedPiece I n => φ.val.app W y)
    (cokernel.condition (idealPowSuccHom I n))
  exact h

/-- **A section of `ℐ` annihilates `ℐⁿ/ℐⁿ⁺¹`.**

A section of the quotient is, over the arrows of a covering sieve, the image of a section of
`ℐⁿ`; multiplying that lift by the restricted section of `ℐ` lands in `ℐⁿ⁺¹` by the product law,
hence dies in the quotient.  The quotient is a sheaf, so the local vanishing is vanishing. -/
theorem smul_gradedPiece_eq_zero (hcomm : ∀ (V : Cᵒᵖ) (a b : R.obj.obj V), a * b = b * a)
    (n : ℕ) (U : Cᵒᵖ) (a : R.obj.obj U) (ha : a ∈ I.obj U)
    (m : (gradedPiece I n).val.obj U) : a • m = 0 := by
  obtain ⟨Sv, hSv, hlift⟩ := Stacks.SheafOfModules.EpiMono.exists_covering_of_epi
    (V := U.unop) (gradedPieceπ I n) m
  refine Stacks.SheafOfModules.eq_zero_of_locally_eq_zero _ hSv fun {V} g hg => ?_
  obtain ⟨t, ht⟩ : ∃ t : ↥((idealPow I n).obj (op V)),
      (gradedPieceπ I n).val.app (op V) t = (gradedPiece I n).val.map g.op m := hlift g hg
  have hb : R.obj.map g.op a ∈ I.obj (op V) := I.map_mem g.op ha
  have hmem := smul_mem_idealPow_succ' I hcomm n (op V) (R.obj.map g.op a) hb t.1 t.2
  have hsmul : R.obj.map g.op a • t =
      (idealPowSuccHom I n).val.app (op V) ⟨R.obj.map g.op a • t.1, hmem⟩ := Subtype.ext rfl
  have hlin : (gradedPieceπ I n).val.app (op V) (R.obj.map g.op a • t) =
      R.obj.map g.op a • (gradedPieceπ I n).val.app (op V) t :=
    ((gradedPieceπ I n).val.app (op V)).hom.map_smul _ t
  refine Eq.trans ((gradedPiece I n).val.map_smul g.op a m) ?_
  refine Eq.trans ((congrArg (fun y => R.obj.map g.op a • y) ht.symm).trans hlin.symm) ?_
  refine Eq.trans (congrArg (fun y => (gradedPieceπ I n).val.app (op V) y) hsmul) ?_
  exact gradedPieceπ_idealPowSuccHom_apply I n (op V) _

/-! ### A morphism out of `ℐⁿ` into an annihilated module kills `ℐⁿ⁺¹` -/

/-- **The sections of `ℐⁿ` killed by a morphism `h` out of `ℐⁿ`, as a sheaf of ideals.**  This is
the image in `𝒪` of the kernel of `h`; its membership condition is local because the target of `h`
is a sheaf, hence separated. -/
def idealPowKer (n : ℕ) {T : SheafOfModules.{w} R}
    (h : (idealPow I n).toSheafOfModules ⟶ T) : (SheafOfModules.unit R).Submodule where
  obj U :=
    { carrier := {x : (SheafOfModules.unit R).val.obj U |
        ∃ t : (idealPow I n).toSheafOfModules.val.obj U,
          (idealPow I n).ι.val.app U t = x ∧ h.val.app U t = 0}
      add_mem' := by
        rintro _ _ ⟨t, rfl, h1⟩ ⟨t', rfl, h2⟩
        refine ⟨t + t', map_add _ t t', ?_⟩
        refine Eq.trans (map_add ((h.val.app U).hom) t t') ?_
        rw [h1, h2, add_zero]
      zero_mem' := ⟨0, map_zero _, map_zero _⟩
      smul_mem' := by
        rintro c _ ⟨t, rfl, h1⟩
        refine ⟨c • t, ((idealPow I n).ι.val.app U).hom.map_smul c t, ?_⟩
        refine Eq.trans ((h.val.app U).hom.map_smul c t) ?_
        rw [h1, smul_zero] }
  map {U V} f := by
    rintro _ ⟨t, rfl, h1⟩
    refine ⟨(idealPow I n).toSheafOfModules.val.map f t,
      PresheafOfModules.naturality_apply (idealPow I n).ι.val f t, ?_⟩
    rw [PresheafOfModules.naturality_apply h.val f t, h1]
    exact map_zero _
  isSheaf {U} s hs := by
    have hsn : s ∈ (idealPow I n).obj U := by
      refine (idealPow I n).isSheaf s (J.superset_covering (fun V f hf => ?_) hs)
      obtain ⟨t, hts, _⟩ := hf
      have h2 : (idealPow I n).ι.val.app (op V) t ∈ (idealPow I n).obj (op V) := t.2
      rw [hts] at h2
      exact h2
    refine ⟨⟨s, hsn⟩, rfl, ?_⟩
    refine Stacks.SheafOfModules.eq_zero_of_locally_eq_zero _ hs fun {V} f hf => ?_
    obtain ⟨t, hts, htz⟩ := hf
    have h1 := PresheafOfModules.naturality_apply (idealPow I n).ι.val f.op
      (⟨s, hsn⟩ : (idealPow I n).toSheafOfModules.val.obj U)
    have hte : (idealPow I n).toSheafOfModules.val.map f.op
        (⟨s, hsn⟩ : (idealPow I n).toSheafOfModules.val.obj U) = t :=
      Subtype.ext (h1.trans hts.symm)
    rw [← PresheafOfModules.naturality_apply h.val f.op
      (⟨s, hsn⟩ : (idealPow I n).toSheafOfModules.val.obj U), hte]
    exact htz

omit [HasSheafify J AddCommGrpCat] [J.WEqualsLocallyBijective AddCommGrpCat] in
/-- **A morphism from `ℐⁿ` to a module annihilated by `ℐ` kills `ℐⁿ⁺¹`.**

For `n ≥ 1` this is the elimination rule of the infimum defining `ℐⁿ⁺¹`: a product of a section of
`ℐ` with a section of `ℐⁿ` is killed by `h`, because `h` is linear and its target is annihilated.
For `n = 0` the power `ℐ¹` is `ℐ` itself and the same computation applies to `a = a · 1`. -/
theorem idealPowSuccHom_comp_eq_zero
    (_hcomm : ∀ (V : Cᵒᵖ) (a b : R.obj.obj V), a * b = b * a) (n : ℕ)
    {T : SheafOfModules.{w} R}
    (hT : ∀ (U : Cᵒᵖ) (a : R.obj.obj U), a ∈ I.obj U → ∀ y : T.val.obj U, a • y = 0)
    (h : (idealPow I n).toSheafOfModules ⟶ T) :
    idealPowSuccHom I n ≫ h = 0 := by
  have key : ∀ (U : Cᵒᵖ) (a : R.obj.obj U), a ∈ I.obj U →
      ∀ m ∈ (idealPow I n).obj U, a • m ∈ (idealPowKer I n h).obj U := by
    intro U a ha m hm
    refine ⟨a • (⟨m, hm⟩ : (idealPow I n).toSheafOfModules.val.obj U), ?_, ?_⟩
    · exact ((idealPow I n).ι.val.app U).hom.map_smul a ⟨m, hm⟩
    · refine Eq.trans ((h.val.app U).hom.map_smul a ⟨m, hm⟩) ?_
      exact hT U a ha _
  have hle : idealPow I (n + 1) ≤ idealPowKer I n h := by
    cases n with
    | zero =>
        intro U a ha
        have hk := key U a ha ((1 : ToType (R.obj.obj U)) :
          (SheafOfModules.unit R).val.obj U) (mem_idealPow_zero I U _)
        rwa [unit_smul_eq_mul, mul_one] at hk
    | succ k =>
        refine sInf_le ?_
        intro U a ha m hm
        exact key U a ha m hm
  ext U x
  obtain ⟨t, hts, htz⟩ := _root_.SheafOfModules.Submodule.le_iff.1 hle U x.2
  have hx : (idealPowSuccHom I n).val.app U x = t := Subtype.ext hts.symm
  have hzero : h.val.app U ((idealPowSuccHom I n).val.app U x) = 0 := by
    rw [hx]
    exact htz
  exact hzero

end Stacks.IdealPowerSheaf

namespace CategoryTheory.Adjunction

variable {D : Type u₁} [Category.{v₁} D] {E : Type u} [Category.{w} E]
  [Limits.HasZeroMorphisms D] [Limits.HasZeroMorphisms E]

/-- **A morphism whose adjunct vanishes has vanishing image under the left adjoint.**  For an
adjunction `L ⊣ Rr` with `L` preserving the zero morphism, if `f ≫ η = 0` with `η` the unit at the
target of `f`, then `L.map f = 0`: the triangle identity recovers `L.map f` from that composite. -/
theorem leftAdjoint_map_eq_zero_of_comp_unit_eq_zero {L : D ⥤ E} {Rr : E ⥤ D} (adj : L ⊣ Rr)
    [L.PreservesZeroMorphisms] {A Bb : D} (f : A ⟶ Bb)
    (hf : f ≫ adj.unit.app Bb = 0) : L.map f = 0 := by
  have h1 : L.map f = L.map (f ≫ adj.unit.app Bb) ≫ adj.counit.app (L.obj Bb) := by
    rw [Functor.map_comp, Category.assoc, adj.left_triangle_components, Category.comp_id]
  rw [h1, hf, Functor.map_zero, Limits.zero_comp]

end CategoryTheory.Adjunction

namespace AlgebraicGeometry.Space

open Stacks.IdealPowerSheaf

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (X : AlgebraicSpaces B S hS) (Z : ClosedSubspaces B S hS X.1)

/-- A section of the defining ideal sheaf lies in the kernel ideal of the structure map of the
inclusion: the two are the same ideal of sections, the defining ideal at an étale chart being
defined as that kernel. -/
theorem mem_kerIdeal_structureSharp_subspaceInclusion (U : (SmallEtale B S hS X.1)ᵒᵖ)
    (a : ToType ((structureRingSheaf B S hS X).obj.obj U))
    (ha : a ∈ (definingIdealSheaf B S hS X Z).obj U) :
    a ∈ (SheafOfModules.kerIdeal
      (structureSharp B S hS (subspaceInclusion B S hS X Z))).obj U :=
  (SheafOfModules.mem_kerIdeal _ U a).2 ha

/-- The `n`-th power `𝓘ⁿ` of the defining ideal sheaf of a closed subspace, as an
`𝒪_X`-module. -/
def definingIdealPowModule (n : ℕ) : Modules.{u, u} B S hS X.1 X.2 :=
  (idealPow (definingIdealSheaf B S hS X Z) n).toSheafOfModules

/-- The inclusion `𝓘ⁿ⁺¹ ⟶ 𝓘ⁿ` of consecutive powers of the defining ideal sheaf. -/
def definingIdealPowSuccHom (n : ℕ) :
    definingIdealPowModule B S hS X Z (n + 1) ⟶ definingIdealPowModule B S hS X Z n :=
  idealPowSuccHom (definingIdealSheaf B S hS X Z) n

/-- **The degree-`n` graded piece `𝓘ⁿ/𝓘ⁿ⁺¹` of the defining ideal sheaf of a closed subspace**,
as an `𝒪_X`-module. -/
def conormalGradedPiece (n : ℕ) : Modules.{u, u} B S hS X.1 X.2 :=
  cokernel (definingIdealPowSuccHom B S hS X Z n)

/-- **The defining ideal sheaf annihilates `𝓘ⁿ/𝓘ⁿ⁺¹`.**  This is
`Stacks.IdealPowerSheaf.smul_gradedPiece_eq_zero` for the defining ideal sheaf, the sections of
the structure sheaf of an algebraic space commuting by
`AlgebraicGeometry.Space.structureRingSheaf_mul_comm`. -/
theorem annihilatedByKerIdeal_conormalGradedPiece (n : ℕ) :
    AnnihilatedByKerIdeal B S hS (subspaceInclusion B S hS X Z)
      (conormalGradedPiece B S hS X Z n) := fun U a ha m =>
  smul_gradedPiece_eq_zero (definingIdealSheaf B S hS X Z)
    (structureRingSheaf_mul_comm B S hS X) n U a
    ((SheafOfModules.mem_kerIdeal _ U a).1 ha) m

/-- **`𝓘ⁿ/𝓘ⁿ⁺¹` is a direct image along the inclusion of the closed subspace.**  It is
annihilated by the ideal cutting out the subspace, and for a closed immersion the essential image
of the direct image of modules is exactly the annihilated modules, which is the essential-image
clause of Stacks 04CJ, part (3). -/
theorem essImage_modulePushforward_conormalGradedPiece (n : ℕ) :
    (modulePushforward B S hS (subspaceInclusion B S hS X Z)).essImage
      (conormalGradedPiece B S hS X Z n) :=
  (essImage_modulePushforward_iff B S hS (subspaceInclusion B S hS X Z) Z.2.2 _).2
    (annihilatedByKerIdeal_conormalGradedPiece B S hS X Z n)

/-- **The unit `𝓘ⁿ/𝓘ⁿ⁺¹ ⟶ i_*i^*(𝓘ⁿ/𝓘ⁿ⁺¹)` of Stacks 03LU is an isomorphism.** -/
theorem isIso_unit_conormalGradedPiece (n : ℕ) :
    IsIso ((modulePullbackAdjunction B S hS (subspaceInclusion B S hS X Z)).unit.app
      (conormalGradedPiece B S hS X Z n)) :=
  (essImage_modulePushforward_iff_isIso_modulePullbackAdjunction_unit B S hS
    (subspaceInclusion B S hS X Z) Z.2.2 _).1
      (essImage_modulePushforward_conormalGradedPiece B S hS X Z n)

/-! ### The inverse image of the inclusion of consecutive powers vanishes -/

/-- **`i^*(𝓘ⁿ⁺¹ ⟶ 𝓘ⁿ) = 0`.**

The adjunct of the inverse image of the inclusion is the composite of the inclusion with the unit
`𝓘ⁿ ⟶ i_*i^*(𝓘ⁿ)`, whose target is annihilated by the ideal cutting out `Z` because it is a
direct image (Stacks 04CJ, part (3)); that composite vanishes by
`Stacks.IdealPowerSheaf.idealPowSuccHom_comp_eq_zero`.  The triangle identity of the adjunction of
Stacks 03LU recovers the inverse image from its adjunct, and the inverse image, being a left
adjoint, carries the zero morphism to the zero morphism. -/
theorem modulePullback_map_idealPowSuccHom_eq_zero (n : ℕ) :
    (modulePullback B S hS (subspaceInclusion B S hS X Z)).map
      (definingIdealPowSuccHom B S hS X Z n) = 0 := by
  have hadj := modulePullbackAdjunction B S hS (subspaceInclusion B S hS X Z)
  have : (modulePullback B S hS (subspaceInclusion B S hS X Z)).IsLeftAdjoint := ⟨_, ⟨hadj⟩⟩
  have hpz : (modulePullback B S hS (subspaceInclusion B S hS X Z)).PreservesZeroMorphisms :=
    inferInstance
  refine CategoryTheory.Adjunction.leftAdjoint_map_eq_zero_of_comp_unit_eq_zero hadj _ ?_
  exact idealPowSuccHom_comp_eq_zero (definingIdealSheaf B S hS X Z)
    (structureRingSheaf_mul_comm B S hS X) n
    (fun U a ha y => annihilatedByKerIdeal_modulePushforward B S hS
      (subspaceInclusion B S hS X Z) _ U a
      (mem_kerIdeal_structureSharp_subspaceInclusion B S hS X Z U a ha) y) _

/-- **`i^*(𝓘ⁿ/𝓘ⁿ⁺¹) ≅ 𝒞_{Z/X, n}`.**

Inverse image along a morphism of algebraic spaces preserves colimits, being a left adjoint, so it
carries the presentation of `𝓘ⁿ/𝓘ⁿ⁺¹` as a cokernel to a presentation of `i^*(𝓘ⁿ/𝓘ⁿ⁺¹)` as the
cokernel of `i^*(𝓘ⁿ⁺¹ ⟶ 𝓘ⁿ)`, which is the zero morphism by
`AlgebraicGeometry.Space.modulePullback_map_idealPowSuccHom_eq_zero`; the cokernel of a zero
morphism is its target, `i^*(𝓘ⁿ) = 𝒞_{Z/X, n}`. -/
def pullbackConormalGradedPieceIso (n : ℕ) :
    (modulePullback B S hS (subspaceInclusion B S hS X Z)).obj
        (conormalGradedPiece B S hS X Z n) ≅ conormalAlgebraPiece B S hS X Z n :=
  have hadj := modulePullbackAdjunction B S hS (subspaceInclusion B S hS X Z)
  have : (modulePullback B S hS (subspaceInclusion B S hS X Z)).IsLeftAdjoint := ⟨_, ⟨hadj⟩⟩
  have : PreservesColimits (modulePullback B S hS (subspaceInclusion B S hS X Z)) :=
    hadj.leftAdjoint_preservesColimits
  PreservesCokernel.iso (modulePullback B S hS (subspaceInclusion B S hS X Z))
      (definingIdealPowSuccHom B S hS X Z n) ≪≫
    cokernelIsoOfEq (modulePullback_map_idealPowSuccHom_eq_zero B S hS X Z n) ≪≫
    cokernelZeroIsoTarget

/-! ### Stacks 09RP -/

/-- **The unit of Stacks 03LU at a module in the essential image of the direct image, as an
isomorphism.**  For a closed immersion `f : W ⟶ X` of algebraic spaces the direct image of modules
is fully faithful (Stacks 04CJ, part (2)), so the unit of `f^* ⊣ f_*` is invertible at any module
in the essential image of `f_*`.

This is `AlgebraicGeometry.Space.submoduleUnitIsoOfEssImage` with the submodule of `𝒪_X` replaced
by an arbitrary `𝒪_X`-module, which is what a quotient of two ideal powers needs.  As there, the
statement is general in the module and the closed immersion, and the two objects are written in
the spelling the unit itself carries, so that no restatement of the type is needed; see the
implementation notes of this file. -/
def moduleUnitIsoOfEssImage {W : AlgebraicSpaces B S hS} (f : W ⟶ X)
    (hf : IsClosedImmersion B S hS f.hom) (G : Modules.{u, u} B S hS X.1 X.2)
    (h : (modulePushforward B S hS f).essImage G) :
    (𝟭 (Modules.{u, u} B S hS X.1 X.2)).obj G ≅
      (modulePullback B S hS f ⋙ modulePushforward B S hS f).obj G :=
  have hff := fullyFaithfulModulePushforward B S hS f hf
  have := hff.full
  have := hff.faithful
  @asIso _ _ _ _ _ ((modulePullbackAdjunction B S hS f).isIso_unit_app_iff_mem_essImage.2 h)

/-- **A module in the essential image of the direct image is the direct image of anything its
inverse image is isomorphic to.**  If `f_*G` is a direct image along the closed immersion `f` and
`f^*G ≅ C`, then `f_*C ≅ G`: apply the direct image to the isomorphism and invert the unit.

Like `AlgebraicGeometry.Space.moduleUnitIsoOfEssImage`, the statement is general in both modules,
so that its instances cost no unfolding of the small étale site. -/
def pushforwardIsoOfPullbackIso {W : AlgebraicSpaces B S hS} (f : W ⟶ X)
    (hf : IsClosedImmersion B S hS f.hom) (G : Modules.{u, u} B S hS X.1 X.2)
    (h : (modulePushforward B S hS f).essImage G) (Cc : Modules.{u, u} B S hS W.1 W.2)
    (e : (modulePullback B S hS f).obj G ≅ Cc) :
    (modulePushforward B S hS f).obj Cc ≅ G :=
  (modulePushforward B S hS f).mapIso e.symm ≪≫
    (moduleUnitIsoOfEssImage B S hS X f hf G h).symm

/-- **Stacks 09RP.**  For a closed subspace `Z` of an algebraic space `X` with inclusion `i` and
defining ideal sheaf `𝓘`, the direct image of the degree-`n` piece of the conormal algebra is the
degree-`n` graded piece of `𝓘`:

`i_*𝒞_{Z/X, n} = 𝓘ⁿ/𝓘ⁿ⁺¹`.

The degree-`n` piece is `AlgebraicGeometry.Space.conormalAlgebraPiece`, the inverse image
`i^*(𝓘ⁿ)` of Stacks 09RN; in degree one it is the conormal module of Stacks 04CN, and in degree
zero the inverse image of the structure sheaf of `X`.  The identification with `𝓘ⁿ/𝓘ⁿ⁺¹` is the
inverse of the unit of Stacks 03LU, transported along
`AlgebraicGeometry.Space.pullbackConormalGradedPieceIso`;
`AlgebraicGeometry.Space.isoConormalAlgebraPiece` records that it determines `𝒞_{Z/X, n}` up to
isomorphism, which is what makes the equation of the source an identification and not merely the
assertion that some module has that direct image. -/
@[stacks 09RP]
def conormalAlgebraPiecePushforwardIso (n : ℕ) :
    (modulePushforward B S hS (subspaceInclusion B S hS X Z)).obj
        (conormalAlgebraPiece B S hS X Z n) ≅ conormalGradedPiece B S hS X Z n :=
  pushforwardIsoOfPullbackIso B S hS X (subspaceInclusion B S hS X Z) Z.2.2
    (conormalGradedPiece B S hS X Z n)
    (essImage_modulePushforward_conormalGradedPiece B S hS X Z n)
    (conormalAlgebraPiece B S hS X Z n) (pullbackConormalGradedPieceIso B S hS X Z n)

/-- **The degree-`n` piece of the conormal algebra is determined by Stacks 09RP.**  An
`𝒪_Z`-module whose direct image along the inclusion is `𝓘ⁿ/𝓘ⁿ⁺¹` is isomorphic to `𝒞_{Z/X, n}`,
because the direct image of modules along a closed immersion is fully faithful (Stacks 04CJ,
part (2)).  This is the uniqueness clause behind the equality sign of the source.

The source introduces 76.6.1.1 by saying that `𝒞_{Z/X, n}` is "characterized by the property"
`i_*𝒞_{Z/X, n} = 𝓘ⁿ/𝓘ⁿ⁺¹`; this is that characterization, and it is what licenses reading
`AlgebraicGeometry.Space.conormalAlgebraPiecePushforwardIso` as the equality sign of the
source rather than as the weaker assertion that some module has that direct image. -/
@[stacks 09RP "the characterizing property 76.6.1.1 determines 𝒞_{Z/X, n} up to isomorphism"]
def isoConormalAlgebraPiece (n : ℕ) (Cc : Modules.{u, u} B S hS Z.1.toFunctor Z.2.1)
    (e : (modulePushforward B S hS (subspaceInclusion B S hS X Z)).obj Cc ≅
      conormalGradedPiece B S hS X Z n) :
    Cc ≅ conormalAlgebraPiece B S hS X Z n :=
  (fullyFaithfulModulePushforward B S hS (subspaceInclusion B S hS X Z) Z.2.2).preimageIso
    (e ≪≫ (conormalAlgebraPiecePushforwardIso B S hS X Z n).symm)

end AlgebraicGeometry.Space

end
