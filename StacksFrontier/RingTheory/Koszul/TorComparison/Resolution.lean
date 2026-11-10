module

public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Algebra.Homology.SingleHomology
public import Mathlib.LinearAlgebra.ExteriorPower.Basis
public import Mathlib.RingTheory.Flat.Basic
public import StacksFrontier.RingTheory.Koszul.Augmentation
public import StacksFrontier.RingTheory.Koszul.Regular
public import StacksFrontier.RingTheory.Koszul.Relations
public import StacksCore.Tactic.StacksAttribute

/-!
# The Koszul complex of a Koszul-regular sequence is a free resolution

Let `R` be a commutative ring and `f₁, …, f_r ∈ R`. The Koszul complex `K_•(f₁, …, f_r)` of
`StacksFrontier.RingTheory.Koszul.Defs` carries a canonical augmentation onto
`R ⧸ (f₁, …, f_r)` placed in degree `0`: in degree `0` it is the quotient map along
`⋀⁰(Rʳ) ≃ R`, and it kills the image of the degree-one differential because that image is
exactly the ideal `(f₁, …, f_r)`. Its degree-zero homology map is an isomorphism for every
sequence, so the augmentation is a quasi-isomorphism precisely when the higher Koszul homology
vanishes, that is, precisely when `f` is Koszul-regular.

Each term `⋀ⁿ(Rʳ)` of the Koszul complex is a finite free `R`-module, with the basis of wedges
of standard basis vectors. Hence for a Koszul-regular sequence the Koszul complex is a free —
in particular projective and flat — resolution of `R ⧸ (f₁, …, f_r)`, which is what makes it
compute `Tor_*^R(R ⧸ (f), -)`.

## Main definitions

* `Koszul.augZero`, `Koszul.augmentation`: the augmentation
  `K_•(f₁, …, f_r) ⟶ (R ⧸ (f₁, …, f_r))[0]` and its degree-zero component.
* `Koszul.quotRangeIso`: the concrete degree-zero opcycles, identified with `R ⧸ (f₁, …, f_r)`.

The identification `Koszul.homologyZeroIso : H₀(K_•(f)) ≅ R ⧸ (f₁, …, f_r)`, the computation
`Koszul.range_d_zero` of the image of the degree-zero differential, and
`Koszul.singleZeroHomology_fac` are in the module
`StacksDraft.AlgebraicGeometry.Intersection.ComputingIntersectionMultiplicities`
`.KoszulResolution`, which this module imports.

## Main results

* `Koszul.augmentation_quasiIso`: for a Koszul-regular sequence the augmentation is a
  quasi-isomorphism, i.e. the Koszul complex is a resolution of `R ⧸ (f₁, …, f_r)`.
* `Koszul.instFreeSeqComplexX`, `Koszul.instProjectiveSeqComplexX`,
  `Koszul.instFlatSeqComplexX`: the terms of the Koszul complex are free, hence projective and
  flat.

## References

* [Stacks Project, Tag 0623](https://stacks.math.columbia.edu/tag/0623)
* [Stacks Project, Tag 062E](https://stacks.math.columbia.edu/tag/062E)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace Koszul

variable {R : Type u} [CommRing R] {r : ℕ}

/-! ### Freeness of the terms -/

/-- Each term `⋀ⁿ(Rʳ)` of the Koszul complex of a sequence of length `r` is a free
`R`-module. -/
instance instFreeSeqComplexX (f : Fin r → R) (i : ℕ) :
    Module.Free R ((Koszul.seqComplex f).X i) :=
  inferInstanceAs (Module.Free R (⋀[R]^i (Fin r → R)))

/-- Each term of the Koszul complex is a projective object of `ModuleCat R`, being free. -/
instance instProjectiveSeqComplexX (f : Fin r → R) (i : ℕ) :
    Projective ((Koszul.seqComplex f).X i) :=
  inferInstanceAs (Projective (ModuleCat.of R (⋀[R]^i (Fin r → R))))

/-- Each term of the Koszul complex is a flat `R`-module, being free. -/
instance instFlatSeqComplexX (f : Fin r → R) (i : ℕ) :
    Module.Flat R ((Koszul.seqComplex f).X i) :=
  inferInstanceAs (Module.Flat R (⋀[R]^i (Fin r → R)))

/-! ### The augmentation -/

/-- The degree-zero component of the Koszul augmentation: the quotient map
`⋀⁰(Rʳ) ≃ R ↠ R ⧸ (f₁, …, f_r)`, read as a morphism out of `(K_•(f)).X 0`. -/
def augZero (f : Fin r → R) :
    (Koszul.seqComplex f).X 0 ⟶ ModuleCat.of R (R ⧸ Ideal.span (Set.range f)) :=
  ModuleCat.ofHom ((Ideal.span (Set.range f)).mkQ.comp
    (exteriorPower.zeroEquiv R (Fin r → R)).toLinearMap)

/-- The augmentation `K_•(f₁, …, f_r) ⟶ (R ⧸ (f₁, …, f_r))[0]`, given in degree `0` by the
quotient map `⋀⁰(Rʳ) ≃ R ↠ R ⧸ (f₁, …, f_r)`. -/
def augmentation (f : Fin r → R) :
    Koszul.seqComplex f ⟶
      (ChainComplex.single₀ (ModuleCat.{u} R)).obj
        (ModuleCat.of R (R ⧸ Ideal.span (Set.range f))) :=
  (ChainComplex.toSingle₀Equiv _ _).symm
    ⟨augZero f, by
      apply ModuleCat.hom_ext
      ext x
      change (⋀[R]^1 (Fin r → R)) at x
      change (Ideal.span (Set.range f)).mkQ
        (exteriorPower.zeroEquiv R (Fin r → R) (Koszul.d (Koszul.seqDual f) 0 x)) = 0
      rw [Koszul.zeroEquiv_d_zero, Koszul.seqDual_apply]
      exact Ideal.Quotient.eq_zero_iff_mem.2
        (Submodule.sum_mem _ fun i _ ↦
          Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩))⟩

/-- The degree-zero component of the Koszul augmentation `augmentation f` is `augZero f`. -/
theorem augmentation_f_zero (f : Fin r → R) :
    (augmentation f).f 0 = augZero f := by
  rw [augmentation, ChainComplex.toSingle₀Equiv_symm_apply_f_zero]

/-- The degree-one differential of the Koszul complex, read off the short complex that computes
`H₀`, is the degree-zero Koszul differential. -/
theorem sc'_f_hom (f : Fin r → R) :
    (((Koszul.seqComplex f).sc' 1 0 0).f).hom = Koszul.d (Koszul.seqDual f) 0 :=
  rfl

/-- The concrete degree-zero opcycles `⋀⁰(Rʳ) ⧸ im d₁` of the Koszul complex, identified with
`R ⧸ (f₁, …, f_r)` along `⋀⁰(Rʳ) ≃ R`. -/
def quotRangeIso (f : Fin r → R) :
    ModuleCat.of R (((Koszul.seqComplex f).sc' 1 0 0).X₂ ⧸
        LinearMap.range (((Koszul.seqComplex f).sc' 1 0 0).f).hom) ≅
      ModuleCat.of R (R ⧸ Ideal.span (Set.range f)) :=
  (Submodule.Quotient.equiv _ (Ideal.span (Set.range f))
    (exteriorPower.zeroEquiv R (Fin r → R)) (range_d_zero f)).toModuleIso

/-- The degree-zero opcycles of the Koszul complex, pushed through `H₀(K_•(f)) ≅ R ⧸ (f)`, is
the quotient map. -/
theorem opcyclesQuot_fac (f : Fin r → R) :
    (Koszul.seqComplex f).pOpcycles 0 ≫
        ((Koszul.seqComplex f).opcyclesIsoSc' 1 0 0
          (ChainComplex.prev ℕ 0) ChainComplex.next_nat_zero).hom ≫
        (((Koszul.seqComplex f).sc' 1 0 0).moduleCatOpcyclesIso).hom ≫ (quotRangeIso f).hom =
      augZero f := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  have h1 := congrArg
    (fun (h : (Koszul.seqComplex f).X 0 ⟶
        ((Koszul.seqComplex f).sc' 1 0 0).opcycles) => h.hom x)
    (HomologicalComplex.pOpcycles_opcyclesIsoSc'_hom (Koszul.seqComplex f) 1 0 0
      (ChainComplex.prev ℕ 0) ChainComplex.next_nat_zero)
  have h2 := ShortComplex.pOpcycles_comp_moduleCatOpcyclesIso_hom_apply
    ((Koszul.seqComplex f).sc' 1 0 0) x
  change (quotRangeIso f).hom.hom
      ((((Koszul.seqComplex f).sc' 1 0 0).moduleCatOpcyclesIso.hom).hom
        ((((Koszul.seqComplex f).opcyclesIsoSc' 1 0 0
            (ChainComplex.prev ℕ 0) ChainComplex.next_nat_zero).hom).hom
          (((Koszul.seqComplex f).pOpcycles 0).hom x))) = _
  rw [show (((Koszul.seqComplex f).opcyclesIsoSc' 1 0 0
        (ChainComplex.prev ℕ 0) ChainComplex.next_nat_zero).hom).hom
          (((Koszul.seqComplex f).pOpcycles 0).hom x)
      = ((((Koszul.seqComplex f).sc' 1 0 0).pOpcycles)).hom x from h1, h2]
  rfl

/-- The degree-zero homology map of the Koszul augmentation is an isomorphism, for every
sequence. -/
theorem augmentation_homologyMap_zero_isIso (f : Fin r → R) :
    IsIso (HomologicalComplex.homologyMap (augmentation f) 0) := by
  let K := Koszul.seqComplex f
  let Q := ModuleCat.of R (R ⧸ Ideal.span (Set.range f))
  let L := (ChainComplex.single₀ (ModuleCat.{u} R)).obj Q
  let α := augmentation f
  let V := HomologicalComplex.singleObjHomologySelfIso (ComplexShape.down ℕ) 0 Q
  have hmap : HomologicalComplex.homologyMap α 0 ≫ V.hom = (homologyZeroIso f).hom := by
    rw [← cancel_epi (K.isoHomologyι₀.inv), ← cancel_epi (K.pOpcycles 0),
      ChainComplex.isoHomologyι₀_inv_naturality_assoc, HomologicalComplex.p_opcyclesMap_assoc,
      ← Category.assoc (L.pOpcycles 0) (L.isoHomologyι₀.inv) V.hom, ← singleZeroHomology_fac Q,
      augmentation_f_zero]
    simp only [V, Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [show (HomologicalComplex.singleObjXSelf (ComplexShape.down ℕ) 0 Q).hom = 𝟙 Q from rfl]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change ⋀[R]^0 (Fin r → R) at x
    have hf := congrArg (fun (h : (Koszul.seqComplex f).X 0 ⟶ Q) => h.hom x)
      (homologyZeroIso_fac f)
    change (Ideal.span (Set.range f)).mkQ ((exteriorPower.zeroEquiv R (Fin r → R)) x) =
      (homologyZeroIso f).hom.hom
        ((Koszul.seqComplex f).isoHomologyι₀.inv.hom
          (((Koszul.seqComplex f).pOpcycles 0).hom x))
    dsimp only [Q] at hf
    exact hf.symm
  have hi : IsIso (HomologicalComplex.homologyMap α 0 ≫ V.hom) := by
    rw [hmap]
    infer_instance
  exact IsIso.of_isIso_comp_right _ V.hom

/-- **The Koszul complex of a Koszul-regular sequence is a resolution of the quotient.** The
augmentation `K_•(f₁, …, f_r) ⟶ (R ⧸ (f₁, …, f_r))[0]` is a quasi-isomorphism. -/
@[sga "6 VIII 1.4" "partial"]
theorem augmentation_quasiIso (f : Fin r → R) (hf : Koszul.IsKoszulRegular f) :
    QuasiIso (augmentation f) := by
  rw [quasiIso_iff]
  intro i
  rw [quasiIsoAt_iff_isIso_homologyMap]
  obtain rfl | hi := eq_or_ne i 0
  · exact augmentation_homologyMap_zero_isIso f
  · have hX : IsZero (((ChainComplex.single₀ (ModuleCat.{u} R)).obj
        (ModuleCat.of R (R ⧸ Ideal.span (Set.range f)))).X i) :=
      HomologicalComplex.isZero_single_obj_X _ 0 _ i hi
    have hH : IsZero (((ChainComplex.single₀ (ModuleCat.{u} R)).obj
        (ModuleCat.of R (R ⧸ Ideal.span (Set.range f)))).homology i) :=
      ((ChainComplex.single₀ (ModuleCat.{u} R)).obj
        (ModuleCat.of R (R ⧸ Ideal.span (Set.range f)))).sc i
        |>.isZero_homology_of_isZero_X₂ hX
    exact (hf i hi).isIso hH _

end Koszul

end
