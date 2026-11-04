module

public import StacksFrontier.Algebra.DirectSum.GradedRingEquiv
public import StacksFrontier.AlgebraicGeometry.SheafSymmetricAlgebra.Free

/-!
# The graded ring of homogeneous sections of `Sym(𝒪_X^{n+1})` over an open is a polynomial ring

`StacksFrontier.AlgebraicGeometry.SheafSymmetricAlgebra.Free` identifies the sections of the
degree-`k` piece of `Sym(𝒪_X^ι)` over an open `U` with `Sym^k_{Γ(X, U)}(Γ(𝒪_X^ι, U))`, with the
unit and multiplication laws. **This file assembles those degreewise comparisons into an
isomorphism of graded rings onto the graded ring of homogeneous sections**, for `ι` a copy of
`Fin (n + 1)`, so that the source is a polynomial ring in `n + 1` variables graded by total
degree — the form the comparison with projective space consumes.

## Main definitions

* `Stacks.SymGraded.siteRing`: the structure-sheaf sections at an open, in the one spelling
  typeclass search accepts for everything involved. See the implementation notes.
* `Stacks.SymGraded.coordIndex`: `Fin (n + 1)` lifted into the module universe, which is where
  `SheafOfModules.free` needs its index.
* `Stacks.SymGraded.chartBasis`: the standard basis of `Γ(𝒪_X^{n+1}, U)`.
* `Stacks.SymGraded.chartPieceEquiv`: the degreewise comparison
  `Γ(X, U)[T]ₖ ≃+ Γ(Sym(𝒪_X^{n+1})ₖ, U)`.
* `Stacks.SymGraded.chartSectionsRingEquiv`: **`Γ(X, U)[T₀, …, Tₙ] ≃+* Γ(Sym(𝒪_X^{n+1}), U)`.**

## Main results

* `Stacks.SymGraded.resPiece_chartPieceEquiv`: **the degreewise comparison is natural in the
  open** on the monomial basis.
* `Stacks.SymGraded.resRingHom_chartSectionsRingEquiv_X`: **the homogeneous coordinates `Tⱼ` are
  natural in the open**, which is the naturality the comparison with projective space consumes,
  the integral polynomial ring being generated over `ℤ` by its variables.
* `Stacks.SymGraded.chartSectionsRingEquiv_C`: **the comparison carries a constant to the
  structure map**, so it is an isomorphism of `Γ(X, U)`-algebras. This is the degree-zero half,
  which identifies the `fst` leg of the chart comparison with projective space.

## Implementation notes

**The grading is taken on the polynomial ring, not on the symmetric algebra, and that is not a
matter of taste.** Assembling the degreewise comparisons with `SymPow.symmetricPower` as the
source grading makes `DirectSum.gradedCongrRingEquiv` diverge: its `DirectSum.GSemiring`
instance for the symmetric powers unfolds `SymmetricAlgebra`, which is a `RingCon` quotient of a
tensor algebra, and the unification does not terminate inside ten times the default heartbeat
budget. With `MvPolynomial.homogeneousSubmodule` as the source grading the same
application elaborates in seconds. The symmetric algebra is still present — it is what the
degreewise comparison goes through — but only inside proofs, never as the index of an instance
search.

**One spelling of the structure-sheaf sections, fixed once.** The same ring reaches this file in
three definitionally equal but not syntactically interchangeable spellings, and typeclass search
does not bridge them, because `CategoryTheory.Sheaf.toRingCat` is a plain `def`:
`PresheafOfModules.symPow` puts its sections over
`((sheafToPresheaf _ CommRingCat).obj X.sheaf ⋙ forget₂ CommRingCat RingCat).obj U`,
`(SheafOfModules.free ι).val` over `X.ringCatSheaf.obj.obj U`, and `sectionPieces` over
`Γ(X, U)`. `Stacks.SymGraded.siteRing` is the first, which is `Γ(X, U)` on the nose — same
carrier and same `CommRing` instance, both by `rfl` — and
`Stacks.SymGraded.module_sections_siteRing` bridges the second once and for all, and
`Stacks.SymGraded.module_moduleSections_siteRing` the third — the sections of an `𝒪_X`-module,
which Mathlib records as a module over the `CommRingCat`-valued `Γ(X, U)`. Both bridges carry
Mathlib's own instance bodies, so they are the same terms as the instances they bridge to and no
transport is needed when an equation crosses spellings.

## References

* [Stacks Project, Tag 01CG](https://stacks.math.columbia.edu/tag/01CG)
* [Stacks Project, Tag 01NN](https://stacks.math.columbia.edu/tag/01NN)
* [Stacks Project, Tag 01OE](https://stacks.math.columbia.edu/tag/01OE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open Stacks.AlgebraicGeometry.RelativeProjBridge
open scoped DirectSum

attribute [local instance] MvPolynomial.gradedAlgebra

namespace Stacks.SymGraded

universe u

variable {X : Scheme.{u}} (n : ℕ)

/-! ### The vocabulary, fixed once -/

/-- The sections of the structure sheaf at an open, in the spelling that
`PresheafOfModules.symPow` forces. Same carrier and same `CommRing` instance as `Γ(X, U.unop)`,
both by `rfl`. -/
abbrev siteRing (X : Scheme.{u}) (U : (Opens X.carrier)ᵒᵖ) : RingCat.{u} :=
  ((sheafToPresheaf (Opens.grothendieckTopology X.carrier) CommRingCat.{u}).obj X.sheaf ⋙
    forget₂ CommRingCat.{u} RingCat.{u}).obj U

/-- `Fin (n + 1)` in the module universe, which is where `SheafOfModules.free` needs its
index. -/
abbrev coordIndex (n : ℕ) : Type u := ULift.{u} (Fin (n + 1))

/-- **The one bridge.** The sections of `𝒪_X^{n+1}` over an open are a module over
`Stacks.SymGraded.siteRing`, which is the same ring as the one
`(SheafOfModules.free _).val` records them over, in a spelling typeclass search does not reach by
itself. -/
instance module_sections_siteRing (U : (Opens X.carrier)ᵒᵖ) :
    Module ↥(siteRing X U) ↥((freeModule (X := X) (coordIndex n)).val.obj U) :=
  inferInstanceAs (Module ↥(X.ringCatSheaf.obj.obj U)
    ↥((freeModule (X := X) (coordIndex n)).val.obj U))

/-- **The second bridge.** The sections of an `𝒪_X`-module over an open are a module over
`Stacks.SymGraded.siteRing`, which is the same ring as the `CommRingCat`-valued `Γ(X, U)` that
Mathlib's instance records them over.

The body is Mathlib's own — `(E.val.obj (op U)).isModule`, exactly the body of
`AlgebraicGeometry.Scheme.Modules.instModule` — so the two instances are the same term and an
equation proved in one spelling is accepted in the other. Without this bridge an expression as
simple as `r • A.one U`, with `r` a coefficient of the polynomial ring on the chart, does not
elaborate: `Stacks.SymGraded.siteRing` is the `RingCat`-valued forgetful image of `Γ(X, U)`, and
`CategoryTheory.sheafToPresheaf` and `CategoryTheory.sheafCompose` are plain `def`s, so instance
search — which unfolds only `@[reducible]` definitions — does not bridge the spellings on its
own. -/
instance module_moduleSections_siteRing (E : X.Modules) (U : X.Opens) :
    Module ↥(siteRing X (op U)) ↥Γ(E, U) := (E.val.obj (op U)).isModule

/-- The standard basis of the sections of `𝒪_X^{n+1}` over an open. -/
def chartBasis (U : (Opens X.carrier)ᵒᵖ) :
    Module.Basis (coordIndex n) ↥(siteRing X U)
      ↥((freeModule (X := X) (coordIndex n)).val.obj U) :=
  Stacks.SheafOfModules.freeCoordBasis X.ringCatSheaf.property U

/-! ### The degreewise comparison -/

/-- The underlying element of the inverse degreewise comparison with a polynomial ring. -/
theorem coe_symmetricPowerEquivHomogeneousSubmodule_symm (U : (Opens X.carrier)ᵒᵖ) (k : ℕ)
    (z : MvPolynomial.homogeneousSubmodule (coordIndex n) ↥(siteRing X U) k) :
    (((SymPow.symmetricPowerEquivHomogeneousSubmodule (chartBasis n U) k).symm z :
        SymPow.symmetricPower k ↥(siteRing X U)
          ↥((freeModule (X := X) (coordIndex n)).val.obj U)) :
        SymmetricAlgebra ↥(siteRing X U)
          ↥((freeModule (X := X) (coordIndex n)).val.obj U)) =
      (SymmetricAlgebra.equivMvPolynomial (chartBasis n U)).symm
        (z : MvPolynomial (coordIndex n) ↥(siteRing X U)) := by
  have h := SymPow.coe_symmetricPowerEquivHomogeneousSubmodule_apply (chartBasis n U) k
    ((SymPow.symmetricPowerEquivHomogeneousSubmodule (chartBasis n U) k).symm z)
  rw [LinearEquiv.apply_symm_apply] at h
  rw [h, AlgEquiv.symm_apply_apply]

/-- The same, with the additive-equivalence coercion that the assembled comparison applies. -/
theorem coe_symmetricPowerEquivHomogeneousSubmodule_symm_toEquiv
    (U : (Opens X.carrier)ᵒᵖ) (k : ℕ)
    (z : MvPolynomial.homogeneousSubmodule (coordIndex n) ↥(siteRing X U) k) :
    (((SymPow.symmetricPowerEquivHomogeneousSubmodule
          (chartBasis n U) k).symm.toAddEquiv.toEquiv z :
        SymPow.symmetricPower k ↥(siteRing X U)
          ↥((freeModule (X := X) (coordIndex n)).val.obj U)) :
        SymmetricAlgebra ↥(siteRing X U)
          ↥((freeModule (X := X) (coordIndex n)).val.obj U)) =
      (SymmetricAlgebra.equivMvPolynomial (chartBasis n U)).symm
        (z : MvPolynomial (coordIndex n) ↥(siteRing X U)) :=
  coe_symmetricPowerEquivHomogeneousSubmodule_symm n U k z

/-- **The degreewise comparison.** The degree-`k` homogeneous polynomials over `Γ(X, U)` are the
sections of the degree-`k` piece of `Sym(𝒪_X^{n+1})` over `U`. -/
abbrev chartPieceEquiv (U : X.Opens) (k : ℕ) :
    ↥(MvPolynomial.homogeneousSubmodule (coordIndex n) ↥(siteRing X (op U)) k) ≃+
      (freeSymGradedAlgebra (X := X) (coordIndex n)).sectionPieces U k :=
  ((SymPow.symmetricPowerEquivHomogeneousSubmodule (chartBasis n (op U)) k).symm.toAddEquiv).trans
    (freePieceEquiv (coordIndex n) k (op U)).toAddEquiv

/-! ### The graded ring of homogeneous sections -/

/-- The degreewise comparisons, assembled into a ring isomorphism of the direct sums. -/
def chartPieceRingEquiv (U : X.Opens) :
    (⨁ k : ℕ, ↥(MvPolynomial.homogeneousSubmodule (coordIndex n) ↥(siteRing X (op U)) k)) ≃+*
      (freeSymGradedAlgebra (X := X) (coordIndex n)).sectionRing U :=
  DirectSum.gradedCongrRingEquiv (fun k : ℕ => chartPieceEquiv n U k)
    (fun i j x y => by
      refine Eq.trans (congrArg (freePieceEquiv (coordIndex n) (i + j) (op U)) ?_)
        (freePieceEquiv_mul (coordIndex n) i j (op U) _ _)
      refine Subtype.ext ?_
      rw [coe_symmetricPowerEquivHomogeneousSubmodule_symm_toEquiv]
      change _ = _ * _
      rw [coe_symmetricPowerEquivHomogeneousSubmodule_symm_toEquiv,
        coe_symmetricPowerEquivHomogeneousSubmodule_symm_toEquiv, SetLike.coe_gMul, map_mul]
      rfl)

/-- **The graded ring of homogeneous sections of `Sym(𝒪_X^{n+1})` over an open is the polynomial
ring in `n + 1` variables over the sections of the structure sheaf.** -/
def chartSectionsRingEquiv (U : X.Opens) :
    MvPolynomial (coordIndex n) ↥(siteRing X (op U)) ≃+*
      (freeSymGradedAlgebra (X := X) (coordIndex n)).sectionRing U :=
  (DirectSum.decomposeRingEquiv
      (MvPolynomial.homogeneousSubmodule (coordIndex n) ↥(siteRing X (op U)))).trans
    (chartPieceRingEquiv n U)

/-- On the degree-`k` summand, `chartPieceRingEquiv` is the degreewise comparison
`chartPieceEquiv`. -/
theorem chartPieceRingEquiv_of (U : X.Opens) (k : ℕ)
    (z : MvPolynomial.homogeneousSubmodule (coordIndex n) ↥(siteRing X (op U)) k) :
    chartPieceRingEquiv n U (DirectSum.of _ k z) =
      DirectSum.of _ k (chartPieceEquiv n U k z) :=
  DirectSum.gradedCongr_of (fun k : ℕ => chartPieceEquiv n U k) k z

/-- `chartSectionsRingEquiv` sends a polynomial to the image under `chartPieceRingEquiv` of its
decomposition into homogeneous components. -/
theorem chartSectionsRingEquiv_apply (U : X.Opens)
    (x : MvPolynomial (coordIndex n) ↥(siteRing X (op U))) :
    chartSectionsRingEquiv n U x =
      chartPieceRingEquiv n U
        (DirectSum.decompose
          (MvPolynomial.homogeneousSubmodule (coordIndex n) ↥(siteRing X (op U))) x) :=
  rfl

/-- The comparison carries the degree-`k` homogeneous polynomials into the degree-`k` part of the
graded ring of homogeneous sections. -/
theorem chartSectionsRingEquiv_mem_grading (U : X.Opens) {k : ℕ}
    {x : MvPolynomial (coordIndex n) ↥(siteRing X (op U))}
    (hx : x ∈ MvPolynomial.homogeneousSubmodule (coordIndex n) ↥(siteRing X (op U)) k) :
    chartSectionsRingEquiv n U x ∈
      (freeSymGradedAlgebra (X := X) (coordIndex n)).grading U k := by
  rw [chartSectionsRingEquiv_apply, DirectSum.decompose_of_mem _ hx, chartPieceRingEquiv_of]
  exact SheafGradedAlgebra.of_mem_grading _ _ _

/-- The comparison on a homogeneous polynomial is the degreewise comparison, placed in its
degree. -/
private theorem chartSectionsRingEquiv_coe_aux (U : X.Opens) (k : ℕ)
    (z : MvPolynomial.homogeneousSubmodule (coordIndex n) ↥(siteRing X (op U)) k) :
    chartSectionsRingEquiv n U (z : MvPolynomial (coordIndex n) ↥(siteRing X (op U))) =
      DirectSum.of _ k (chartPieceEquiv n U k z) := by
  rw [chartSectionsRingEquiv_apply,
    DirectSum.decompose_coe
      (MvPolynomial.homogeneousSubmodule (coordIndex n) ↥(siteRing X (op U))) z,
    chartPieceRingEquiv_of]

/-- The inverse comparison carries the degree-`k` part of the graded ring of homogeneous sections
into the degree-`k` homogeneous polynomials. -/
theorem chartSectionsRingEquiv_symm_mem (U : X.Opens) {k : ℕ}
    {z : (freeSymGradedAlgebra (X := X) (coordIndex n)).sectionRing U}
    (hz : z ∈ (freeSymGradedAlgebra (X := X) (coordIndex n)).grading U k) :
    (chartSectionsRingEquiv n U).symm z ∈
      MvPolynomial.homogeneousSubmodule (coordIndex n) ↥(siteRing X (op U)) k := by
  obtain ⟨y, rfl⟩ := hz
  have h : chartSectionsRingEquiv n U
      ((chartPieceEquiv n U k).symm y : MvPolynomial (coordIndex n) ↥(siteRing X (op U))) =
      DirectSum.of _ k y := by
    rw [chartSectionsRingEquiv_coe_aux]
    exact congrArg (DirectSum.of _ k) ((chartPieceEquiv n U k).apply_symm_apply y)
  rw [← h, (chartSectionsRingEquiv n U).symm_apply_apply]
  exact ((chartPieceEquiv n U k).symm y).2

/-- **The chart comparison as a homomorphism of graded rings.** -/
def chartGradedHom (U : X.Opens) :
    MvPolynomial.homogeneousSubmodule (coordIndex n) ↥(siteRing X (op U)) →+*ᵍ
      (freeSymGradedAlgebra (X := X) (coordIndex n)).grading U where
  toRingHom := (chartSectionsRingEquiv n U).toRingHom
  map_mem hx := chartSectionsRingEquiv_mem_grading n U hx

/-- The inverse of `Stacks.SymGraded.chartGradedHom`. -/
def chartGradedInv (U : X.Opens) :
    (freeSymGradedAlgebra (X := X) (coordIndex n)).grading U →+*ᵍ
      MvPolynomial.homogeneousSubmodule (coordIndex n) ↥(siteRing X (op U)) where
  toRingHom := (chartSectionsRingEquiv n U).symm.toRingHom
  map_mem hz := chartSectionsRingEquiv_symm_mem n U hz

/-- `chartGradedHom` composed after `chartGradedInv` is the identity of the graded ring of
homogeneous sections. -/
theorem chartGradedHom_comp_inv (U : X.Opens) :
    (chartGradedHom n U).comp (chartGradedInv n U) =
      GradedRingHom.id ((freeSymGradedAlgebra (X := X) (coordIndex n)).grading U) :=
  GradedRingHom.ext fun z => (chartSectionsRingEquiv n U).apply_symm_apply z

/-- `chartGradedInv` composed after `chartGradedHom` is the identity of the graded polynomial
ring. -/
theorem chartGradedInv_comp_hom (U : X.Opens) :
    (chartGradedInv n U).comp (chartGradedHom n U) =
      GradedRingHom.id
        (MvPolynomial.homogeneousSubmodule (coordIndex n) ↥(siteRing X (op U))) :=
  GradedRingHom.ext fun x => (chartSectionsRingEquiv n U).symm_apply_apply x

/-! ### Naturality in the open -/

/-- The comparison on a homogeneous polynomial is the degreewise comparison, placed in its
degree. -/
theorem chartSectionsRingEquiv_coe (U : X.Opens) (k : ℕ)
    (z : MvPolynomial.homogeneousSubmodule (coordIndex n) ↥(siteRing X (op U)) k) :
    chartSectionsRingEquiv n U (z : MvPolynomial (coordIndex n) ↥(siteRing X (op U))) =
      DirectSum.of _ k (chartPieceEquiv n U k z) :=
  chartSectionsRingEquiv_coe_aux n U k z

/-- The degreewise comparison carries the monomial basis of the degree-`k` homogeneous
polynomials to the monomial basis of the sections of the degree-`k` symmetric power. -/
theorem chartPieceEquiv_basisHomogeneousSubmodule (k : ℕ) (U : X.Opens)
    (d : {d : coordIndex n →₀ ℕ | d.degree = k}) :
    chartPieceEquiv n U k
        (MvPolynomial.basisHomogeneousSubmodule (coordIndex n) ↥(siteRing X (op U)) k d) =
      freePieceEquiv (coordIndex n) k (op U)
        (Stacks.SheafOfModules.basisSymPowSections X.ringCatSheaf.property k (op U) d) :=
  rfl

/-- **The degreewise comparison is natural in the open on the monomial basis**: restriction of
homogeneous sections carries the section attached to a monomial over `V` to the one attached to
the same monomial over `U`.

Both inputs are already available: `Stacks.SymGraded.resPiece_freePieceEquiv` moves restriction
across the sheafification unit, and `Stacks.SheafOfModules.basisSymPowSections_map` says the
monomial basis of the sectionwise symmetric power is natural. -/
theorem resPiece_chartPieceEquiv (k : ℕ) {U V : X.Opens} (h : U ≤ V)
    (d : {d : coordIndex n →₀ ℕ | d.degree = k}) :
    (freeSymGradedAlgebra (X := X) (coordIndex n)).resPiece h k
        (chartPieceEquiv n V k
          (MvPolynomial.basisHomogeneousSubmodule (coordIndex n) ↥(siteRing X (op V)) k d)) =
      chartPieceEquiv n U k
        (MvPolynomial.basisHomogeneousSubmodule (coordIndex n) ↥(siteRing X (op U)) k d) :=
  ((congrArg ((freeSymGradedAlgebra (X := X) (coordIndex n)).resPiece h k)
      (chartPieceEquiv_basisHomogeneousSubmodule n k V d)).trans
    (resPiece_freePieceEquiv (coordIndex n) k h _)).trans
      ((congrArg (freePieceEquiv (coordIndex n) k (op U))
        (Stacks.SheafOfModules.basisSymPowSections_map X.ringCatSheaf.property k
          (homOfLE h).op d)).trans (chartPieceEquiv_basisHomogeneousSubmodule n k U d).symm)

/-- **The homogeneous coordinates are natural in the open.** Restriction of homogeneous sections
carries the section `Tⱼ` of `Sym(𝒪_X^{n+1})` over `V` to the section `Tⱼ` over `U`.

This is the whole naturality content the comparison with projective space needs: the integral
polynomial ring is generated over `ℤ` by its variables, so a homomorphism out of it is pinned by
its values on them. -/
theorem resRingHom_chartSectionsRingEquiv_X {U V : X.Opens} (h : U ≤ V) (j : coordIndex n) :
    (freeSymGradedAlgebra (X := X) (coordIndex n)).resRingHom h
        (chartSectionsRingEquiv n V (MvPolynomial.X j)) =
      chartSectionsRingEquiv n U (MvPolynomial.X j) := by
  have hj : (Finsupp.single j 1 : coordIndex n →₀ ℕ).degree = 1 := by simp
  have key : ∀ W : X.Opens,
      (MvPolynomial.basisHomogeneousSubmodule (coordIndex n) ↥(siteRing X (op W)) 1
        ⟨Finsupp.single j 1, hj⟩ : MvPolynomial (coordIndex n) ↥(siteRing X (op W))) =
        MvPolynomial.X j := fun W => by
    rw [MvPolynomial.coe_basisHomogeneousSubmodule_apply]
    simp [MvPolynomial.X]
  rw [← key V, ← key U, chartSectionsRingEquiv_coe, chartSectionsRingEquiv_coe,
    SheafGradedAlgebra.resRingHom_of, resPiece_chartPieceEquiv]

/-! ### The degree-zero part: the structure map -/

/-- **The sectionwise comparison takes a constant to the corresponding multiple of the unit.**
The inverse degreewise comparison in degree `0` carries the constant polynomial `C r` to
`r • 1`, and `1` is the sectionwise unit of `Sym(𝒪_X^{n+1})` over `U`. -/
theorem symmetricPowerEquivHomogeneousSubmodule_symm_C (U : X.Opens)
    (r : ↥(siteRing X (op U))) :
    (SymPow.symmetricPowerEquivHomogeneousSubmodule (chartBasis n (op U)) 0).symm
        ⟨MvPolynomial.C r,
          MvPolynomial.C_mem_homogeneousSubmodule_zero (coordIndex n) ↥(siteRing X (op U)) r⟩ =
      r • ((sitePresheafAlgebra (freeModule (X := X) (coordIndex n)).val).one.eval (op U)) :=
  Subtype.ext
    (by rw [SymPow.coe_symmetricPowerEquivHomogeneousSubmodule_symm_C (chartBasis n (op U)) r]; rfl)

/-- **The degreewise comparison in degree `0` takes a constant to the corresponding multiple of
the unit of `Sym(𝒪_X^{n+1})`.** -/
theorem chartPieceEquiv_zero_C (U : X.Opens) (r : ↥(siteRing X (op U))) :
    chartPieceEquiv n U 0
        ⟨MvPolynomial.C r,
          MvPolynomial.C_mem_homogeneousSubmodule_zero (coordIndex n) ↥(siteRing X (op U)) r⟩ =
      r • (freeSymGradedAlgebra (X := X) (coordIndex n)).one U :=
  (congrArg (freePieceEquiv (coordIndex n) 0 (op U))
      (symmetricPowerEquivHomogeneousSubmodule_symm_C n U r)).trans
    ((freePieceEquiv (coordIndex n) 0 (op U)).map_smul r _)

/-- **The degree-`0` half of the chart comparison: it is the structure map.** The comparison
`Γ(X, U)[T₀, …, Tₙ] ≃+* Γ(Sym(𝒪_X^{n+1}), U)` carries the constant polynomial `C r` to
`Stacks.AlgebraicGeometry.RelativeProjBridge.SheafGradedAlgebra.strHom` of `r`, so it is an
isomorphism of `Γ(X, U)`-algebras and not merely of graded rings.

This is what identifies the degree-zero structure map of the projective bundle with the
coefficient map of `Stacks.AlgebraicGeometry.ProjPolyChart.projCompare`, hence the `fst` leg of
that comparison. -/
theorem chartSectionsRingEquiv_C (U : X.Opens) (r : ↥(siteRing X (op U))) :
    chartSectionsRingEquiv n U (MvPolynomial.C r) =
      (freeSymGradedAlgebra (X := X) (coordIndex n)).strHom U r :=
  (chartSectionsRingEquiv_coe n U 0
        ⟨MvPolynomial.C r,
          MvPolynomial.C_mem_homogeneousSubmodule_zero (coordIndex n)
            ↥(siteRing X (op U)) r⟩).trans
    (congrArg (DirectSum.of _ 0) (chartPieceEquiv_zero_C n U r))

end Stacks.SymGraded

end
