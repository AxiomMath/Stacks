module

public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.Single
public import Mathlib.CategoryTheory.Abelian.Exact

/-!
# The brutal truncation of a bounded above cochain complex

Let `V` be an abelian category and let `K : CochainComplex V ℤ` be strictly supported in degrees
`≤ b`.  The only differential out of degree `b` lands in a zero object, so the identity of `K.X b`
defines a morphism of complexes from the complex concentrated in degree `b` with term `K.X b`
into `K`.  That morphism is a monomorphism, and its cokernel is the *brutal truncation*
`σ_{<b} K` of `K`: the complex obtained from `K` by replacing its top term by zero and keeping
all the lower terms and all the remaining differentials.

## Main definitions

* `CochainComplex.topSingleHom`: the morphism
  `(single V (ComplexShape.up ℤ) b).obj (K.X b) ⟶ K` given by the identity of `K.X b`.
* `CochainComplex.brutalTrunc`: the brutal truncation, defined as the cokernel of
  `CochainComplex.topSingleHom`.
* `CochainComplex.brutalTruncπ`: the projection `K ⟶ CochainComplex.brutalTrunc K b`.
* `CochainComplex.brutalTruncShortComplex`: the short complex
  `(single V (ComplexShape.up ℤ) b).obj (K.X b) ⟶ K ⟶ brutalTrunc K b`.

## Main results

* `CochainComplex.mono_topSingleHom`: `CochainComplex.topSingleHom` is a monomorphism.
* `CochainComplex.brutalTruncXIso` and `CochainComplex.isZero_brutalTrunc_X_self`: the brutal
  truncation has the same terms as `K` away from degree `b`, and a zero term in degree `b`.
* `CochainComplex.isStrictlyLE_brutalTrunc` and `CochainComplex.isStrictlyGE_brutalTrunc`: the
  brutal truncation is strictly supported in degrees `≤ b - 1`, and inherits any lower bound
  on the support of `K`.
* `CochainComplex.brutalTruncShortComplex_shortExact`: the brutal truncation short exact
  sequence.

## Implementation notes

The complex concentrated in a single degree is written throughout as
`HomologicalComplex.single V (ComplexShape.up ℤ) b`, which is the value at `b` of
`CochainComplex.singleFunctors V`; the two agree, so this is also
`(CochainComplex.singleFunctor V b).obj`.

Limits and colimits in `HomologicalComplex V c` are computed degreewise, and a short complex of
homological complexes is short exact exactly when it is short exact in each degree.  Both the
degreewise description of the terms of the truncation and its boundedness are therefore read off
from `HomologicalComplex.shortExact_iff_degreewise_shortExact`, rather than from an explicit
construction of the cokernel.
-/

@[expose] public noncomputable section

universe v u

open CategoryTheory Category Limits HomologicalComplex

namespace CochainComplex

variable {V : Type u} [Category.{v} V] [Abelian V] (K : CochainComplex V ℤ) (b : ℤ)
  [K.IsStrictlyLE b]

/-- The morphism from the complex concentrated in degree `b` with term `K.X b` into `K` given by
the identity of `K.X b`.  It is well defined because the differential of `K` out of degree `b`
lands in a zero object. -/
def topSingleHom : (single V (ComplexShape.up ℤ) b).obj (K.X b) ⟶ K :=
  mkHomFromSingle (𝟙 (K.X b)) fun k hk => by
    have hbk : b < k := by
      have h : b + 1 = k := hk
      omega
    exact (K.isZero_of_isStrictlyLE b k hbk).eq_of_tgt _ _

/-- In degree `b` the morphism `CochainComplex.topSingleHom` is the canonical identification of
the term of the single complex with `K.X b`. -/
@[simp]
lemma topSingleHom_f_self :
    (topSingleHom K b).f b = (singleObjXSelf (ComplexShape.up ℤ) b (K.X b)).hom := by
  simp [topSingleHom]

/-- Away from degree `b` the morphism `CochainComplex.topSingleHom` is zero, its source having a
zero term there. -/
@[simp]
lemma topSingleHom_f_of_ne (i : ℤ) (hi : i ≠ b) : (topSingleHom K b).f i = 0 :=
  (isZero_single_obj_X (ComplexShape.up ℤ) b (K.X b) i hi).eq_of_src _ _

/-- The morphism `CochainComplex.topSingleHom` is an isomorphism in degree `b`. -/
instance isIso_topSingleHom_f_self : IsIso ((topSingleHom K b).f b) := by
  rw [topSingleHom_f_self]
  infer_instance

/-- The morphism `CochainComplex.topSingleHom` is a monomorphism: in degree `b` it is an
isomorphism, and in every other degree its source is a zero object. -/
instance mono_topSingleHom : Mono (topSingleHom K b) := by
  refine mono_of_mono_f _ fun i => ?_
  by_cases hi : i = b
  · rw [hi]
    infer_instance
  · exact ⟨fun g h _ =>
      (isZero_single_obj_X (ComplexShape.up ℤ) b (K.X b) i hi).eq_of_tgt g h⟩

/-- The brutal truncation `σ_{<b} K` of a cochain complex `K` strictly supported in degrees
`≤ b`: the cokernel of the inclusion of the top term `CochainComplex.topSingleHom`. -/
def brutalTrunc : CochainComplex V ℤ := cokernel (topSingleHom K b)

/-- The canonical projection from `K` onto its brutal truncation. -/
def brutalTruncπ : K ⟶ brutalTrunc K b := cokernel.π (topSingleHom K b)

/-- The projection onto the brutal truncation is an epimorphism. -/
instance epi_brutalTruncπ : Epi (brutalTruncπ K b) :=
  inferInstanceAs (Epi (cokernel.π (topSingleHom K b)))

/-- The composition of the inclusion of the top term with the projection onto the brutal
truncation vanishes. -/
@[simp]
lemma topSingleHom_comp_brutalTruncπ :
    topSingleHom K b ≫ brutalTruncπ K b = 0 :=
  cokernel.condition (topSingleHom K b)

/-- The brutal truncation short exact sequence
`(single V (ComplexShape.up ℤ) b).obj (K.X b) ⟶ K ⟶ σ_{<b} K`. -/
def brutalTruncShortComplex : ShortComplex (CochainComplex V ℤ) :=
  ShortComplex.mk (topSingleHom K b) (brutalTruncπ K b) (topSingleHom_comp_brutalTruncπ K b)

/-- The first term of the brutal truncation short exact sequence is the complex concentrated in
degree `b` with term `K.X b`. -/
@[simp]
lemma brutalTruncShortComplex_X₁ :
    (brutalTruncShortComplex K b).X₁ = (single V (ComplexShape.up ℤ) b).obj (K.X b) := rfl

/-- The second term of the brutal truncation short exact sequence is `K`. -/
@[simp]
lemma brutalTruncShortComplex_X₂ : (brutalTruncShortComplex K b).X₂ = K := rfl

/-- The third term of the brutal truncation short exact sequence is the brutal truncation. -/
@[simp]
lemma brutalTruncShortComplex_X₃ :
    (brutalTruncShortComplex K b).X₃ = brutalTrunc K b := rfl

/-- The first map of the brutal truncation short exact sequence is the inclusion of the top
term. -/
@[simp]
lemma brutalTruncShortComplex_f :
    (brutalTruncShortComplex K b).f = topSingleHom K b := rfl

/-- The second map of the brutal truncation short exact sequence is the projection onto the
brutal truncation. -/
@[simp]
lemma brutalTruncShortComplex_g :
    (brutalTruncShortComplex K b).g = brutalTruncπ K b := rfl

/-- **The brutal truncation short exact sequence.**  The top term of a cochain complex strictly
supported in degrees `≤ b` sits inside it as a subcomplex with quotient the brutal
truncation. -/
theorem brutalTruncShortComplex_shortExact :
    (brutalTruncShortComplex K b).ShortExact where
  exact := ShortComplex.exact_cokernel (topSingleHom K b)
  mono_f := mono_topSingleHom K b
  epi_g := epi_brutalTruncπ K b

/-- The brutal truncation short exact sequence is short exact in each degree. -/
theorem brutalTruncShortComplex_map_eval_shortExact (i : ℤ) :
    ((brutalTruncShortComplex K b).map (eval V (ComplexShape.up ℤ) i)).ShortExact :=
  (HomologicalComplex.shortExact_iff_degreewise_shortExact _).1
    (brutalTruncShortComplex_shortExact K b) i

/-- Away from degree `b` the projection onto the brutal truncation is an isomorphism: in those
degrees the subcomplex `(single V (ComplexShape.up ℤ) b).obj (K.X b)` has a zero term. -/
theorem isIso_brutalTruncπ_f (i : ℤ) (hi : i ≠ b) : IsIso ((brutalTruncπ K b).f i) := by
  have hmono : Mono ((brutalTruncπ K b).f i) :=
    (brutalTruncShortComplex_map_eval_shortExact K b i).exact.mono_g
      (topSingleHom_f_of_ne K b i hi)
  exact isIso_of_mono_of_epi ((brutalTruncπ K b).f i)

/-- Away from degree `b` the brutal truncation has the same terms as `K`. -/
def brutalTruncXIso (i : ℤ) (hi : i ≠ b) : (brutalTrunc K b).X i ≅ K.X i :=
  haveI := isIso_brutalTruncπ_f K b i hi
  (asIso ((brutalTruncπ K b).f i)).symm

/-- The identification of the terms of the brutal truncation away from degree `b` is inverse to
the projection. -/
@[simp]
lemma brutalTruncXIso_inv (i : ℤ) (hi : i ≠ b) :
    (brutalTruncXIso K b i hi).inv = (brutalTruncπ K b).f i := rfl

/-- In degree `b` the projection onto the brutal truncation is zero. -/
@[simp]
lemma brutalTruncπ_f_self : (brutalTruncπ K b).f b = 0 := by
  rw [← cancel_epi ((topSingleHom K b).f b), comp_zero, ← HomologicalComplex.comp_f,
    topSingleHom_comp_brutalTruncπ, HomologicalComplex.zero_f]

/-- The brutal truncation has a zero term in degree `b`. -/
theorem isZero_brutalTrunc_X_self : IsZero ((brutalTrunc K b).X b) := by
  rw [IsZero.iff_id_eq_zero, ← cancel_epi ((brutalTruncπ K b).f b), comp_id, comp_zero,
    brutalTruncπ_f_self]

/-- The brutal truncation of a complex strictly supported in degrees `≤ b` is strictly supported
in degrees `≤ b - 1`. -/
instance isStrictlyLE_brutalTrunc : (brutalTrunc K b).IsStrictlyLE (b - 1) := by
  rw [isStrictlyLE_iff]
  intro i hi
  by_cases hib : i = b
  · rw [hib]
    exact isZero_brutalTrunc_X_self K b
  · exact (K.isZero_of_isStrictlyLE b i (by omega)).of_iso (brutalTruncXIso K b i hib)

/-- The brutal truncation inherits any lower bound on the support of `K`. -/
instance isStrictlyGE_brutalTrunc (a : ℤ) [K.IsStrictlyGE a] :
    (brutalTrunc K b).IsStrictlyGE a := by
  rw [isStrictlyGE_iff]
  intro i hi
  by_cases hib : i = b
  · rw [hib]
    exact isZero_brutalTrunc_X_self K b
  · exact (K.isZero_of_isStrictlyGE a i hi).of_iso (brutalTruncXIso K b i hib)

end CochainComplex

end
