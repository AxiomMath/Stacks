module

public import Mathlib.CategoryTheory.Abelian.Projective.Dimension
public import StacksFrontier.Algebra.Homology.Resolution.Defs.Comparison
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.Homology.Embedding.TruncGEHomology
import Mathlib.CategoryTheory.Abelian.Projective.Ext

@[expose] public section

/-!
# Projective dimension and finite resolutions by projectives

Let `X` be an object of an abelian category. If the terms of a projective resolution of `X` vanish
in degrees `≥ n`, then `X` has projective dimension `< n`. Conversely, if `X` has projective
dimension `≤ n`, then every projective resolution of `X` can be shortened to one of length `n`
whose terms are retracts of the terms of the original one: its canonical truncation, with the
`n`-th syzygy in degree `n`. For a module with a resolution by finite projective modules, this
compares Mathlib's `HasProjectiveDimensionLE` with finite resolutions by finite projective modules.

## Main definitions

* `ComplexShape.finDown n`: the chain-complex shape on `Fin (n + 1)`, the shape of a chain complex
  concentrated in degrees `0, …, n`.

## Main results

* `CategoryTheory.ProjectiveResolution.hasProjectiveDimensionLT_of_isZero`: a projective
  resolution whose terms vanish in degrees `≥ n` bounds the projective dimension by `< n`;
* `CategoryTheory.ProjectiveResolution.isSplitEpi_pOpcycles`: if `X` has projective dimension
  `≤ n`, the `n`-th syzygy of a projective resolution is a direct summand of its term in
  degree `n`;
* `CategoryTheory.ProjectiveResolution.exists_retract_and_isZero`: the shortened resolution;
* `ModuleResolution.hasProjectiveDimensionLE` and
  `ModuleResolution.exists_finite_projective_resolution_of_hasProjectiveDimensionLE`: the same for
  resolutions of modules, keeping track of finiteness.

## Implementation notes

Both directions compute `Ext` with a projective resolution
(`CategoryTheory.ProjectiveResolution.extMk` and its lemmas), and the shortened resolution is
Mathlib's canonical truncation `HomologicalComplex.truncGE` along the embedding `Fin.val` of
`ComplexShape.finDown n` into `ComplexShape.down ℕ`. Neither needs `HasProjectiveResolutions` or
a smallness assumption, and the module statements hold for any ring and modules in any universe.

Stacks 0CXC compares projective dimension with left resolutions by projective objects
(`CategoryTheory.hasProjectiveDimensionLE_tfae_leftResolution`), and Stacks 0CXE with finite
resolutions by finite projective modules over a Noetherian ring. Here a given resolution by finite
projective modules supplies finiteness, so no Noetherian hypothesis is needed.

## References

* [The Stacks Project, Tag 0CXC](https://stacks.math.columbia.edu/tag/0CXC)
* [The Stacks Project, Tag 0CXE](https://stacks.math.columbia.edu/tag/0CXE)
-/

open CategoryTheory Limits

universe v u

/-- The chain-complex shape on `Fin (N + 1)`: there is a differential `i ⟶ j` exactly when
`i = j + 1`. -/
public def ComplexShape.finDown (N : ℕ) : ComplexShape (Fin (N + 1)) where
  Rel i j := (j : ℕ) + 1 = i
  next_eq h h' := Fin.ext (by omega)
  prev_eq h h' := Fin.ext (by omega)

namespace CategoryTheory

/-- The degrees `0, …, n` of `ComplexShape.down ℕ`. -/
private def truncEmbedding (n : ℕ) : (ComplexShape.finDown n).Embedding (ComplexShape.down ℕ) :=
  .mk' _ _ Fin.val Fin.val_injective fun _ _ => Iff.rfl

private instance (n : ℕ) : (truncEmbedding n).IsTruncGE where
  rel' _ _ h := h
  mem_next {j k'} h := ⟨⟨k', by
    have : k' + 1 = (j : ℕ) := h
    omega⟩, rfl⟩

namespace ProjectiveResolution

variable {C : Type u} [Category.{v} C] [Abelian C] {X : C} (R : ProjectiveResolution X)

/-- If the terms of a projective resolution of `X` vanish in all degrees `≥ n`, then `X` has
projective dimension `< n`. -/
public theorem hasProjectiveDimensionLT_of_isZero (n : ℕ)
    (h : ∀ i, n ≤ i → IsZero (R.complex.X i)) : HasProjectiveDimensionLT X n := by
  let := HasExt.standard C
  refine HasProjectiveDimensionLT.mk fun i hi Y e => ?_
  obtain ⟨f, hf, rfl⟩ := R.extMk_surjective e (i + 1) rfl
  obtain rfl : f = 0 := (h i hi).eq_of_src _ _
  exact R.extMk_zero _ _

/-- **The `n`-th syzygy is projective.** If `X` has projective dimension `≤ n`, then for every
projective resolution of `X`, the projection of its term in degree `n` onto the cokernel of the
incoming differential is a split epimorphism: the `Ext`-class of degree `n + 1` of the projection
in degree `n + 1` vanishes, which splits the inclusion of the image of the differential. -/
public theorem isSplitEpi_pOpcycles (n : ℕ) [HasProjectiveDimensionLE X n] :
    IsSplitEpi (R.complex.pOpcycles n) := by
  let := HasExt.standard C
  obtain ⟨g, hg⟩ := (R.extMk_eq_zero_iff (R.complex.pOpcycles (n + 1)) (n + 2) rfl
    (R.complex.d_pOpcycles _ _) n rfl).1
      (Abelian.Ext.eq_zero_of_hasProjectiveDimensionLT _ (n + 1) le_rfl)
  have h0 : R.complex.fromOpcycles (n + 1) n ≫ R.complex.pOpcycles n = 0 := by
    rw [← cancel_epi (R.complex.pOpcycles (n + 1)), HomologicalComplex.p_fromOpcycles_assoc,
      HomologicalComplex.d_pOpcycles, comp_zero]
  refine .mk' ⟨R.complex.descOpcycles (𝟙 _ - g ≫ R.complex.fromOpcycles (n + 1) n) (n + 1)
    (ChainComplex.prev ℕ n) ?_, ?_⟩
  · rw [Preadditive.comp_sub, Category.comp_id, reassoc_of% hg,
      HomologicalComplex.p_fromOpcycles, sub_self]
  · rw [← cancel_epi (R.complex.pOpcycles n), HomologicalComplex.p_descOpcycles_assoc,
      Preadditive.sub_comp, Category.assoc, h0, comp_zero, sub_zero, Category.id_comp,
      Category.comp_id]

/-- **Shortening a projective resolution.** If `X` has projective dimension `≤ n`, then every
projective resolution of `X` can be replaced by one whose terms vanish above degree `n` and are
retracts of the terms of the original one. It is the canonical truncation
`HomologicalComplex.truncGE`, whose term in degree `n` is the `n`-th syzygy
(`CategoryTheory.ProjectiveResolution.isSplitEpi_pOpcycles`). -/
public theorem exists_retract_and_isZero (n : ℕ) [HasProjectiveDimensionLE X n] :
    ∃ R' : ProjectiveResolution X, (∀ i, Nonempty (Retract (R'.complex.X i) (R.complex.X i))) ∧
      ∀ i, n < i → IsZero (R'.complex.X i) := by
  let e := truncEmbedding n
  let S := (ChainComplex.single₀ C).obj X
  have : S.IsStrictlySupported e := ⟨fun i hi =>
    HomologicalComplex.isZero_single_obj_X _ _ _ _ fun h => hi ⟨0, n.succ_pos⟩ h.symm⟩
  obtain ⟨s⟩ := (R.isSplitEpi_pOpcycles n).exists_splitEpi
  have hzero : ∀ i, n < i → IsZero ((R.complex.truncGE e).X i) := fun i hi =>
    (R.complex.truncGE e).isZero_X_of_isStrictlySupported e i fun j h => by
      have : (j : ℕ) = i := h
      omega
  have hret (i : ℕ) : Nonempty (Retract ((R.complex.truncGE e).X i) (R.complex.X i)) := by
    rcases lt_trichotomy i n with hi | hi | hi
    · refine ⟨(R.complex.truncGEXIso e (i := ⟨i, by omega⟩) rfl ?_).retract⟩
      exact e.not_boundaryGE_next (j := ⟨i + 1, by omega⟩) rfl
    · subst hi
      refine ⟨(R.complex.truncGEXIsoOpcycles e (i := Fin.last i) rfl ?_).retract.trans
        ⟨s.section_, R.complex.pOpcycles i, s.id⟩⟩
      exact e.boundaryGE (i' := i + 1) rfl fun j h => by
        have : (j : ℕ) = i + 1 := h
        omega
    · exact ⟨(hzero i hi).retract _⟩
  refine ⟨{ complex := R.complex.truncGE e
            projective := fun i => (hret i).some.projective
            π := HomologicalComplex.truncGEMap R.π e ≫ inv (S.πTruncGE e)
            quasiIso := ?_ }, hret, hzero⟩
  have : QuasiIso (HomologicalComplex.truncGEMap R.π e) :=
    (HomologicalComplex.quasiIso_truncGEMap_iff _ _).2 fun _ _ _ => inferInstance
  infer_instance

end ProjectiveResolution

end CategoryTheory

namespace ModuleResolution

variable {R : Type u} [Ring R] {M : Type v} [AddCommGroup M] [Module R M]

/-- **A finite resolution by projective modules bounds the projective dimension.** If `M` has a
resolution by projective modules whose terms vanish above degree `d`, then `M` has projective
dimension `≤ d`. -/
public theorem hasProjectiveDimensionLE (F : ModuleResolution R M)
    (hF : ∀ i, Module.Projective R (F.complex.X i)) {d : ℕ}
    (hd : ∀ i, d < i → IsZero (F.complex.X i)) : HasProjectiveDimensionLE (ModuleCat.of R M) d :=
  have := F.quasiIso
  ProjectiveResolution.hasProjectiveDimensionLT_of_isZero
    { complex := F.complex
      projective := fun i => have := hF i; inferInstance
      π := F.π } (d + 1) hd

/-- **Shortening a resolution by finite projective modules.** If `M` has a resolution by finite
projective modules and projective dimension `≤ d`, then it has a resolution by finite projective
modules whose terms vanish above degree `d`. -/
public theorem exists_finite_projective_resolution_of_hasProjectiveDimensionLE
    (F : ModuleResolution R M)
    (hF : ∀ i, Module.Finite R (F.complex.X i) ∧ Module.Projective R (F.complex.X i)) {d : ℕ}
    (hd : HasProjectiveDimensionLE (ModuleCat.of R M) d) :
    ∃ G : ModuleResolution R M,
      (∀ i, Module.Finite R (G.complex.X i) ∧ Module.Projective R (G.complex.X i)) ∧
        ∀ i, d < i → IsZero (G.complex.X i) := by
  have := F.quasiIso
  obtain ⟨P, hP, hPd⟩ := ProjectiveResolution.exists_retract_and_isZero
    { complex := F.complex
      projective := fun i => have := (hF i).2; inferInstance
      π := F.π } d
  refine ⟨⟨P.complex, inferInstance, P.π, inferInstance⟩, fun i => ?_, hPd⟩
  obtain ⟨r⟩ := hP i
  have := (hF i).1
  have := (hF i).2
  have hr : r.r.hom.comp r.i.hom = LinearMap.id := congrArg ModuleCat.Hom.hom r.retract
  exact ⟨.of_surjective r.r.hom fun x => ⟨r.i.hom x, congr($hr x)⟩,
    .of_split r.i.hom r.r.hom hr⟩

end ModuleResolution
