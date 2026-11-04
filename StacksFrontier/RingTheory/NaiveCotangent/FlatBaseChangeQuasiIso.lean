module

public import StacksFrontier.RingTheory.NaiveCotangent.Defs
public import StacksFrontier.RingTheory.NaiveCotangent.BaseChange
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Flat base change for the naive cotangent complex is a quasi-isomorphism

A two-term chain complex of `T`-modules concentrated in homological degrees `1` and `0` is the
same datum as its differential `d : C₁ →ₗ[T] C₀`, and it admits two equivalent descriptions:
unbundled, by the differential itself, or bundled, as a `NaiveCotangent.TwoTerm T` carrying the
two modules and the map between them.  Flat base change for the naive cotangent complex is proved
in the unbundled description: for a flat ring map `R → R'`, with `S' = R' ⊗_R S`, the canonical
comparison
```
NL(α) ⊗_S S' ⟶ NL(α')
```
is an isomorphism of two-term complexes of `S'`-modules, and the canonical comparison
`NL_{S/R} ⊗_S S' ⟶ NL_{S'/R'}` of the *canonical* naive cotangent complexes is a homotopy
equivalence.  Homology, on the other hand, is defined in the bundled description:
`H₁ = ker d`, `H₀ = coker d`, and a chain map is a quasi-isomorphism when it induces bijections
on both.

This file connects the two.  A differential `d` is bundled as `FlatBaseChangeNL.twoTerm d`, an
unbundled chain map is bundled by `FlatBaseChangeNL.ChainMap.toTwoTermChainMap`, and the two
notions of equivalence are transported: an isomorphism of two-term complexes induces bijections
on `H₁` and `H₀` because the inverse isomorphism induces inverse maps on homology, and a homotopy
equivalence in the unbundled sense is a homotopy equivalence in the bundled sense, the two
degreewise homotopy identities `id - g ∘ f = h ∘ d` and `id - g ∘ f = d ∘ h` being the same
equations up to sign as the bundled `NaiveCotangent.Homotopic`.

Consequently flat base change for the naive cotangent complex is a quasi-isomorphism: the
comparison `NL(α) ⊗_S S' → NL(α')` and the comparison `NL_{S/R} ⊗_S S' → NL_{S'/R'}` both
induce isomorphisms `H₁(NL(α) ⊗_S S') ≅ H₁(NL(α'))` and `Ω_{S/R} ⊗_S S' ≅ Ω_{S'/R'}`.

## Main definitions

* `FlatBaseChangeNL.twoTerm`: a differential `d : C₁ →ₗ[T] C₀`, viewed as a bundled
  `NaiveCotangent.TwoTerm T`.
* `FlatBaseChangeNL.ChainMap.toTwoTermChainMap`: a chain map of two-term complexes, viewed as a
  `NaiveCotangent.ChainMap`.
* `FlatBaseChangeNL.TwoComplexEquiv.symm`: the inverse of an isomorphism of two-term complexes.

## Main results

* `FlatBaseChangeNL.TwoComplexEquiv.isQuasiIso`: an isomorphism of two-term complexes is a
  quasi-isomorphism.
* `FlatBaseChangeNL.HtpyEquiv.isHomotopyEquiv` and `FlatBaseChangeNL.HtpyEquiv.isQuasiIso`: a
  homotopy equivalence of two-term complexes is a homotopy equivalence in the sense of
  `NaiveCotangent.IsHomotopyEquiv`, hence a quasi-isomorphism.
* `FlatBaseChangeNL.statement2_isQuasiIso`: for a flat ring map `R → R'` and a presentation `α`
  of `S` over `R`, the canonical comparison `NL(α) ⊗_S S' → NL(α')` is a quasi-isomorphism, with
  degree-`1` component `cotComparison1` and degree-`0` component `cotComparison0`.
* `FlatBaseChangeNL.statement3_isQuasiIso`: for a flat ring map `R → R'`, the canonical
  comparison `NL_{S/R} ⊗_S S' → NL_{S'/R'}` is a quasi-isomorphism, with degree-`1` component
  `statement3_f1` and degree-`0` component `statement3_f0`.

## References

* [Stacks Project, Tag 00S4](https://stacks.math.columbia.edu/tag/00S4)
* [Stacks Project, Tag 00S1](https://stacks.math.columbia.edu/tag/00S1)
* [Stacks Project, Tag 07BN](https://stacks.math.columbia.edu/tag/07BN)
-/

@[expose] public section

open Algebra TensorProduct

namespace FlatBaseChangeNL

section Bundling

variable {T : Type*} [CommRing T] {C1 C0 : Type*} [AddCommGroup C1] [Module T C1]
  [AddCommGroup C0] [Module T C0]

/-- A two-term chain complex of `T`-modules concentrated in homological degrees `1` and `0`,
recorded unbundled by its differential `d : C₁ →ₗ[T] C₀`, viewed as the bundled two-term complex
`NaiveCotangent.TwoTerm T` with `C₁` in degree `1`, `C₀` in degree `0` and differential `d`. -/
def twoTerm (d : C1 →ₗ[T] C0) : NaiveCotangent.TwoTerm T where
  X₁ := C1
  X₀ := C0
  d := d

end Bundling

section Transport

variable {T : Type*} [CommRing T] {C1 C0 D1 D0 : Type*}
  [AddCommGroup C1] [Module T C1] [AddCommGroup C0] [Module T C0]
  [AddCommGroup D1] [Module T D1] [AddCommGroup D0] [Module T D0]
  {dC : C1 →ₗ[T] C0} {dD : D1 →ₗ[T] D0}

/-- A chain map `(f1, f0)` between the two-term complexes with differentials `dC` and `dD`,
viewed as a chain map between the bundled complexes `twoTerm dC` and `twoTerm dD`: the two
degree components and the commuting square `dD ∘ f1 = f0 ∘ dC` are the same data. -/
def ChainMap.toTwoTermChainMap (f : ChainMap dC dD) :
    NaiveCotangent.ChainMap (twoTerm dC) (twoTerm dD) where
  f₁ := f.f1
  f₀ := f.f0
  comm := f.comm

/-- Equal chain maps are homotopic, via the zero homotopy. -/
private theorem homotopic_of_eq {A B : NaiveCotangent.TwoTerm T} {p q : NaiveCotangent.ChainMap A B}
    (h : p = q) : NaiveCotangent.Homotopic p q := ⟨0, by simp [h], by simp [h]⟩

/-- An isomorphism of two-term complexes, viewed as a chain map by forgetting that its two
degree components are invertible. -/
def TwoComplexEquiv.toChainMap (e : TwoComplexEquiv dC dD) : ChainMap dC dD where
  f1 := (e.e1 : C1 →ₗ[T] D1)
  f0 := (e.e0 : C0 →ₗ[T] D0)
  comm := e.comm

/-- An isomorphism of two-term complexes, viewed as a chain map between the bundled complexes
`twoTerm dC` and `twoTerm dD`. -/
def TwoComplexEquiv.toTwoTermChainMap (e : TwoComplexEquiv dC dD) :
    NaiveCotangent.ChainMap (twoTerm dC) (twoTerm dD) :=
  e.toChainMap.toTwoTermChainMap

/-- The inverse of an isomorphism of two-term complexes: the degreewise inverse equivalences
`e1⁻¹` and `e0⁻¹` again commute with the differentials, `dC ∘ e1⁻¹ = e0⁻¹ ∘ dD`, as follows from
`dD ∘ e1 = e0 ∘ dC` by precomposing with `e1⁻¹` and postcomposing with `e0⁻¹`. -/
def TwoComplexEquiv.symm (e : TwoComplexEquiv dC dD) : TwoComplexEquiv dD dC where
  e1 := e.e1.symm
  e0 := e.e0.symm
  comm := by
    refine LinearMap.ext fun y => ?_
    have h := congrArg (fun m => m (e.e1.symm y)) e.comm
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.apply_symm_apply] at h
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe]
    rw [h, LinearEquiv.symm_apply_apply]

/-- **An isomorphism of two-term complexes is a quasi-isomorphism.**  If `e1 : C₁ ≃ D₁` and
`e0 : C₀ ≃ D₀` are linear equivalences with `dD ∘ e1 = e0 ∘ dC`, then the associated chain map
induces bijections on `H₁ = ker d` and on `H₀ = coker d`.  Indeed the inverse isomorphism
`(e1⁻¹, e0⁻¹)` is a chain map in the other direction whose composites with `(e1, e0)` are, in
both orders, the identity chain map; passing to homology, which is functorial and preserves
identities, gives two-sided inverses in each degree. -/
theorem TwoComplexEquiv.isQuasiIso (e : TwoComplexEquiv dC dD) :
    NaiveCotangent.IsQuasiIso e.toTwoTermChainMap := by
  refine NaiveCotangent.isQuasiIso_of_isHomotopyEquiv
    ⟨e.symm.toTwoTermChainMap, homotopic_of_eq (NaiveCotangent.ChainMap.ext ?_ ?_),
      homotopic_of_eq (NaiveCotangent.ChainMap.ext ?_ ?_)⟩ <;>
  exact LinearMap.ext fun x => by
    first
    | exact e.e1.symm_apply_apply x | exact e.e0.symm_apply_apply x
    | exact e.e1.apply_symm_apply x | exact e.e0.apply_symm_apply x

/-- **A homotopy equivalence of two-term complexes is a homotopy equivalence of the bundled
complexes.**  A `HtpyEquiv` records a chain map `f`, a chain map `g` back, and homotopies
`hC : C₀ → C₁`, `hD : D₀ → D₁` with `id - g ∘ f = hC ∘ dC` in degree `1`,
`id - g ∘ f = dC ∘ hC` in degree `0`, and symmetrically for `f ∘ g`.  These are exactly the
equations required by `NaiveCotangent.Homotopic` for the pairs `(g ∘ f, id)` and `(f ∘ g, id)`,
with homotopies `-hC` and `-hD`. -/
theorem HtpyEquiv.isHomotopyEquiv (he : HtpyEquiv dC dD) :
    NaiveCotangent.IsHomotopyEquiv he.toFun.toTwoTermChainMap := by
  have kC1 : he.invFun.f1 ∘ₗ he.toFun.f1 - LinearMap.id = (-he.hC) ∘ₗ dC := by
    rw [LinearMap.neg_comp, ← he.htpyC1]
    abel
  have kC0 : he.invFun.f0 ∘ₗ he.toFun.f0 - LinearMap.id = dC ∘ₗ (-he.hC) := by
    rw [LinearMap.comp_neg, ← he.htpyC0]
    abel
  have kD1 : he.toFun.f1 ∘ₗ he.invFun.f1 - LinearMap.id = (-he.hD) ∘ₗ dD := by
    rw [LinearMap.neg_comp, ← he.htpyD1]
    abel
  have kD0 : he.toFun.f0 ∘ₗ he.invFun.f0 - LinearMap.id = dD ∘ₗ (-he.hD) := by
    rw [LinearMap.comp_neg, ← he.htpyD0]
    abel
  exact ⟨he.invFun.toTwoTermChainMap, ⟨-he.hC, kC1, kC0⟩, ⟨-he.hD, kD1, kD0⟩⟩

/-- **A homotopy equivalence of two-term complexes is a quasi-isomorphism.**  Homotopic chain
maps agree on `H₁` and `H₀`, so a homotopy inverse induces a two-sided inverse on homology. -/
@[ega "III 6.1.4" "special case"]
theorem HtpyEquiv.isQuasiIso (he : HtpyEquiv dC dD) :
    NaiveCotangent.IsQuasiIso he.toFun.toTwoTermChainMap :=
  NaiveCotangent.isQuasiIso_of_isHomotopyEquiv he.isHomotopyEquiv

end Transport

section FlatBaseChange

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
variable (R' : Type*) [CommRing R'] [Algebra R R']

/-- **Flat base change for `NL(α)` is a quasi-isomorphism.**  Let `α : P → S` be a presentation
of the `R`-algebra `S`, let `R → R'` be flat, put `S' = R' ⊗_R S`, and let `α' : P' → S'` be the
base-changed presentation.  The canonical comparison `NL(α) ⊗_S S' → NL(α')` of two-term
complexes of `S'`-modules, with degree-`1` component `cotComparison1` and degree-`0` component
`cotComparison0`, induces isomorphisms on `H₁ = ker d` and on `H₀ = coker d`.  This is the
homological form of the isomorphism of complexes of `statement2_complex_iso`. -/
theorem statement2_isQuasiIso [Module.Flat R R'] (P : Algebra.Extension R S) :
    ∃ f : NaiveCotangent.ChainMap (twoTerm (cotDiffBaseChangeS R' P))
        (twoTerm (P.baseChange (T := R')).cotangentComplex),
      f.f₁ = cotComparison1 R' P ∧ f.f₀ = cotComparison0 R' P ∧ NaiveCotangent.IsQuasiIso f := by
  obtain ⟨iso, he1, he0⟩ := statement2_complex_iso R' P
  exact ⟨iso.toTwoTermChainMap, he1, he0, iso.isQuasiIso⟩

/-- **Flat base change for `NL_{S/R}` is a quasi-isomorphism.**  Let `R → R'` be flat and put
`S' = R' ⊗_R S`.  The canonical comparison `NL_{S/R} ⊗_S S' → NL_{S'/R'}` of the canonical naive
cotangent complexes, a chain map of two-term complexes of `S'`-modules with degree-`1` component
`statement3_f1` and degree-`0` component `statement3_f0`, induces isomorphisms on
`H₁ = ker d` and on `H₀ = coker d`; that is, `H₁(L_{S/R}) ⊗_S S' ≅ H₁(L_{S'/R'})` and
`Ω_{S/R} ⊗_S S' ≅ Ω_{S'/R'}`.  This is the homological form of the homotopy equivalence of
`statement3_homotopy_equiv`. -/
theorem statement3_isQuasiIso [Module.Flat R R'] :
    ∃ f : NaiveCotangent.ChainMap (twoTerm (nlCanDiffBaseChange (R := R) (S := S) R'))
        (twoTerm ((Algebra.Generators.self R' (R' ⊗[R] S)).toExtension).cotangentComplex),
      f.f₁ = statement3_f1 (R := R) (S := S) R' ∧
        f.f₀ = statement3_f0 (R := R) (S := S) R' ∧ NaiveCotangent.IsQuasiIso f := by
  obtain ⟨he, h1, h0⟩ := statement3_homotopy_equiv (R := R) (S := S) R'
  exact ⟨he.toFun.toTwoTermChainMap, h1, h0, he.isQuasiIso⟩

end FlatBaseChange

end FlatBaseChangeNL
