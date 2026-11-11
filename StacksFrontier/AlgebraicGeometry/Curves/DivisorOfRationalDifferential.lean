module

public import Mathlib.FieldTheory.Perfect
public import StacksFrontier.AlgebraicGeometry.Chow.MeromorphicOrder.RationalDifferential
public import StacksFrontier.AlgebraicGeometry.Chow.Vocabulary.PrincipalCycle
public import StacksFrontier.AlgebraicGeometry.Curves.NonsingularProjectiveModel
public import StacksFrontier.AlgebraicGeometry.Curves.UniformizerDifferential
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.ClosedPointCodimension
public import StacksFrontier.AlgebraicGeometry.UnitsNormalProper.Hartogs
public import StacksFrontier.AlgebraicGeometry.Variety.JacobsonClosedPoints
public import StacksFrontier.RingTheory.Kaehler.UniformizerSpan
import StacksCore.Tactic.StacksAttribute

/-!
# The divisor of zeros and poles of a rational differential on a normal curve

Let `X` be a normal curve over a perfect field `k`, with function field identified with a field
`K` over `k`, and let `ω ∈ Ω[K⁄k]` be a nonzero rational differential. Then `ω` has exactly one
divisor of zeros and poles in the sense of `Stacks.Divisors.IsDivisorOfRationalDifferential`.

At a prime divisor `Z` with generic point `ξ`, the local ring `𝒪_{X,ξ}` is a discrete valuation
ring whose residue field is finite, hence separable, over `k`; so the differential of a
uniformizer spans the differentials of `𝒪_{X,ξ}` (Nakayama's lemma,
`KaehlerDifferential.span_D_eq_top_of_maximalIdeal_eq_span`) and, `K` being the fraction field of
`𝒪_{X,ξ}`, spans `Ω[K⁄k]` over `K`. Writing `ω = g · dt` for a uniformizer `t`, the order of
vanishing of `g` at `ξ` does not depend on `t`, because two uniformizers have differentials
differing by a unit of `𝒪_{X,ξ}`. These coefficients are locally finite: on an affine open
`U = Spec B` with `B` generated over `k` by `b₁, …, bₙ`, fix `b₀ ∈ B` with `d b₀ ≠ 0` and write
`ω = g₀ · d b₀` and `d bⱼ = rⱼ · d b₀`; at every prime divisor meeting `U` where all the `rⱼ` are
regular, `d b₀` generates the differentials of the local ring, so the coefficient there is the
order of `g₀`.

## Main results

* `AlgebraicGeometry.existsUnique_isDivisorOfRationalDifferential`: a nonzero rational
  differential on a normal curve over a perfect field has a unique divisor of zeros and poles.
* `AlgebraicGeometry.exists_isDivisorOfRationalDifferential_of_isCurve`: in particular it has one.

## Implementation notes

The `k`-algebra structures on the local rings, on the rings of sections over affine opens and on
the residue fields are the ones induced by the structure morphism through global sections, as
elsewhere in this development; compatibility of the identification `e : K ≃+* R(X)` with the base
field is the equation `he`, phrased with `AlgebraicGeometry.functionFieldAlgebra`.

## References

* [Stacks Project, Tag 09U0](https://stacks.math.columbia.edu/tag/09U0)
* [Stacks Project, Tag 0C1E](https://stacks.math.columbia.edu/tag/0C1E)
-/

@[expose] public noncomputable section

open CategoryTheory IsLocalRing Order TopologicalSpace Stacks.Divisors

universe u

namespace AlgebraicGeometry

section Stalk

variable {k : Type u} [Field k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k))

/-- The local ring at a point of a scheme locally of finite type over a field is essentially of
finite type over the field. -/
theorem essFiniteType_stalk_of_locallyOfFiniteType [LocallyOfFiniteType sX] (x : X) :
    letI : Algebra k (X.presheaf.stalk x) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ sX.appTop ≫ X.presheaf.germ ⊤ x trivial).hom.toAlgebra
    Algebra.EssFiniteType k (X.presheaf.stalk x) := by
  rw [← specFieldStalkIso_hom_comp_stalkMap sX x]
  let e := (specFieldStalkIso (sX x)).commRingCatIsoToRingEquiv
  change RingHom.EssFiniteType _
  exact RingHom.EssFiniteType.respectsIso.right _ e (LocallyOfFiniteType.stalkMap sX x)

/-- The generic point of a prime divisor of a curve is a closed point. -/
theorem isClosed_singleton_genericPoint_of_isCurve [IsCurve k sX] (Z : PrimeDivisor X) :
    IsClosed ({Z.genericPoint} : Set X) := by
  rw [← closure_subset_iff_isClosed]
  intro y hy
  by_contra hne
  have hsp : Z.genericPoint ⤳ y := specializes_iff_mem_closure.mpr hy
  have hlt : y < Z.genericPoint := lt_of_le_not_ge hsp fun h => hne (Specializes.antisymm h hsp).eq
  have h1 := coheight_add_one_le hlt
  rw [Z.coheight_genericPoint] at h1
  have h2 := coheight_le_topologicalKrullDim y
  rw [IsCurve.topologicalKrullDim_eq_one (k := k) (f := sX)] at h2
  have h3 : coheight y ≤ 1 := by exact_mod_cast h2
  have h4 := h1.trans h3
  norm_num at h4

end Stalk

section Curve

variable {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X] {sX : X ⟶ Spec (.of k)}
  {K : Type u} [Field K] [Algebra k K] {e : K ≃+* X.functionField}

/-- The ring map from the local ring at a point of an integral scheme to a field identified with
its function field. -/
def stalkToField (e : K ≃+* X.functionField) (x : X) :
    X.presheaf.stalk x →+* K :=
  e.symm.toRingHom.comp (algebraMap (X.presheaf.stalk x) X.functionField)

/-- Followed by the identification with the function field, `stalkToField` is the canonical map
from the local ring to the function field. -/
@[simp]
theorem apply_stalkToField (x : X) (u : X.presheaf.stalk x) :
    e (stalkToField e x u) = algebraMap (X.presheaf.stalk x) X.functionField u := by
  simp [stalkToField]

/-- The map from a local ring of an integral scheme to its function field is injective. -/
theorem stalkToField_injective (x : X) : Function.Injective (stalkToField e x) :=
  e.symm.injective.comp (IsFractionRing.injective (X.presheaf.stalk x) X.functionField)

/-- Every element of a field identified with a field of fractions of `R` is a quotient of
elements of the image of `R`. -/
theorem exists_mul_eq_of_isFractionRing {R F : Type*} [CommRing R] [IsDomain R] [Field F]
    [Algebra R F]
    [IsFractionRing R F] (e : K ≃+* F) (y : K) :
    ∃ a b : R, e.symm.toRingHom.comp (algebraMap R F) b ≠ 0 ∧
      y * e.symm.toRingHom.comp (algebraMap R F) b = e.symm.toRingHom.comp (algebraMap R F) a := by
  obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (A := R) (e y)
  have hb0 : algebraMap R F b ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
  refine ⟨a, b, by simpa using hb0, ?_⟩
  apply e.injective
  simp [← hab, div_mul_cancel₀ _ hb0]

variable [IsCurve k sX]

/-- The structure morphism gives compatible `k`-algebra structures on the local ring at a point
and on `K`. -/
theorem stalkToField_algebraMap
    (he : ∀ a : k,
      e (algebraMap k K a) = @algebraMap k X.functionField _ _ (functionFieldAlgebra k sX) a)
    (x : X) (a : k) :
    stalkToField e x
        (((Scheme.ΓSpecIso (.of k)).inv ≫ sX.appTop ≫ X.presheaf.germ ⊤ x trivial).hom a) =
      algebraMap k K a := by
  have : Nonempty (⊤ : X.Opens) := ⟨⟨genericPoint X, trivial⟩⟩
  apply e.injective
  rw [apply_stalkToField, he]
  exact X.algebraMap_germ_eq_germToFunctionField (U := ⊤) trivial _

/-- The structure morphism gives compatible `k`-algebra structures on the sections over a
nonempty open and on `K`. -/
theorem germToFunctionField_appLE
    (he : ∀ a : k,
      e (algebraMap k K a) = @algebraMap k X.functionField _ _ (functionFieldAlgebra k sX) a)
    (U : X.Opens) [Nonempty U] (a : k) :
    e.symm (X.germToFunctionField U
        (((Scheme.ΓSpecIso (.of k)).inv ≫ sX.appLE ⊤ U le_top).hom a)) =
      algebraMap k K a := by
  have : Nonempty (⊤ : X.Opens) := ⟨⟨genericPoint X, trivial⟩⟩
  apply e.injective
  rw [RingEquiv.apply_symm_apply, he]
  change _ = (X.presheaf.germ ⊤ _ _).hom (sX.appTop.hom ((Scheme.ΓSpecIso (.of k)).inv.hom a))
  rw [← X.presheaf.germ_res_apply (homOfLE le_top) (genericPoint X)]
  rfl

variable [PerfectField k]

/-- **The differential of a uniformizer spans.** At a prime divisor of a curve over a perfect
field, the differential in `Ω[K⁄k]` of every element `u` of the local ring is a multiple, by an
element of the local ring, of the differential of a generator `s` of the maximal ideal. -/
theorem exists_D_stalkToField_eq_smul
    (he : ∀ a : k,
      e (algebraMap k K a) = @algebraMap k X.functionField _ _ (functionFieldAlgebra k sX) a)
    (Z : PrimeDivisor X) {s : X.presheaf.stalk Z.genericPoint}
    (hs : maximalIdeal (X.presheaf.stalk Z.genericPoint) = Ideal.span {s})
    (u : X.presheaf.stalk Z.genericPoint) :
    ∃ h : X.presheaf.stalk Z.genericPoint,
      KaehlerDifferential.D k K (stalkToField e _ u) =
        stalkToField e _ h • KaehlerDifferential.D k K (stalkToField e _ s) := by
  let : Algebra k (X.presheaf.stalk Z.genericPoint) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ sX.appTop ≫
      X.presheaf.germ ⊤ Z.genericPoint trivial).hom.toAlgebra
  let : Algebra k (ResidueField (X.presheaf.stalk Z.genericPoint)) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ sX.appTop ≫ X.Γevaluation Z.genericPoint).hom.toAlgebra
  have : IsScalarTower k (X.presheaf.stalk Z.genericPoint)
      (ResidueField (X.presheaf.stalk Z.genericPoint)) :=
    IsScalarTower.of_algebraMap_eq' rfl
  have : Algebra.IsAlgebraic k (ResidueField (X.presheaf.stalk Z.genericPoint)) :=
    isAlgebraic_residueField_of_isClosed sX (isClosed_singleton_genericPoint_of_isCurve sX Z)
  have : Algebra.FormallyUnramified k (ResidueField (X.presheaf.stalk Z.genericPoint)) :=
    Algebra.FormallyUnramified.of_isSeparable k _
  have : Algebra.EssFiniteType k (X.presheaf.stalk Z.genericPoint) :=
    essFiniteType_stalk_of_locallyOfFiniteType sX Z.genericPoint
  exact KaehlerDifferential.exists_D_eq_smul_D_of_maximalIdeal_eq_span k _ K
    (stalkToField e Z.genericPoint) (stalkToField_algebraMap he Z.genericPoint) s hs u

/-- At a prime divisor of a curve over a perfect field, every rational differential is a
multiple of the differential of a generator `s` of the maximal ideal of the local ring. -/
theorem exists_eq_smul_D_stalkToField
    (he : ∀ a : k,
      e (algebraMap k K a) = @algebraMap k X.functionField _ _ (functionFieldAlgebra k sX) a)
    (Z : PrimeDivisor X) {s : X.presheaf.stalk Z.genericPoint}
    (hs : maximalIdeal (X.presheaf.stalk Z.genericPoint) = Ideal.span {s}) (v : Ω[K⁄k]) :
    ∃ c : K, v = c • KaehlerDifferential.D k K (stalkToField e _ s) := by
  have hW := KaehlerDifferential.eq_top_of_forall_D_mem (stalkToField e Z.genericPoint)
    (exists_mul_eq_of_isFractionRing e)
    (Submodule.span K {KaehlerDifferential.D k K (stalkToField e _ s)}) fun b => by
      obtain ⟨h, hh⟩ := exists_D_stalkToField_eq_smul he Z hs b
      rw [hh]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp (hW ▸ Submodule.mem_top : v ∈ _)
  exact ⟨c, hc.symm⟩

/-- On a curve over a perfect field with at least one prime divisor, the rational differentials
form a `K`-vector space spanned by any nonzero element. -/
theorem exists_eq_smul_of_ne_zero
    (he : ∀ a : k,
      e (algebraMap k K a) = @algebraMap k X.functionField _ _ (functionFieldAlgebra k sX) a)
    [IsLocallyNoetherian X] [IsNormal X] (Z : PrimeDivisor X) {w : Ω[K⁄k]} (hw : w ≠ 0)
    (v : Ω[K⁄k]) : ∃ c : K, v = c • w := by
  have := Stacks.AlgebraicGeometry.UnitsNormalProper.isDiscreteValuationRing_stalk
    Z.coheight_genericPoint
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (X.presheaf.stalk Z.genericPoint)
  have hs := (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ
  obtain ⟨a, ha⟩ := exists_eq_smul_D_stalkToField he Z hs v
  obtain ⟨b, hb⟩ := exists_eq_smul_D_stalkToField he Z hs w
  have hb0 : b ≠ 0 := by
    rintro rfl
    exact hw (by rw [hb, zero_smul])
  exact ⟨a * b⁻¹, by rw [ha, hb, smul_smul, mul_assoc, inv_mul_cancel₀ hb0, mul_one]⟩

end Curve

section Order

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]

/-- The order of vanishing at a prime divisor of the image of an irreducible element of the
local ring is one. -/
theorem ord_algebraMap_eq_one_of_irreducible (Z : PrimeDivisor X)
    {ϖ : X.presheaf.stalk Z.genericPoint} (hϖ : Irreducible ϖ) :
    X.ord (algebraMap _ X.functionField ϖ) Z.genericPoint = 1 := by
  have := Stacks.AlgebraicGeometry.UnitsNormalProper.isDiscreteValuationRing_stalk
    Z.coheight_genericPoint
  have : Ring.KrullDimLE 1 (X.presheaf.stalk Z.genericPoint) :=
    krullDimLE_of_coheight_le Z.coheight_genericPoint.le
  have hne : algebraMap _ X.functionField ϖ ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr hϖ.ne_zero
  rw [Scheme.ord_eq_iff Z.coheight_genericPoint hne]
  exact Ring.ordFrac_irreducible hϖ

/-- The order of vanishing at a prime divisor of the image of a unit of the local ring is zero. -/
theorem ord_algebraMap_eq_zero_of_isUnit (Z : PrimeDivisor X)
    {c : X.presheaf.stalk Z.genericPoint} (hc : IsUnit c) :
    X.ord (algebraMap _ X.functionField c) Z.genericPoint = 0 := by
  have : Ring.KrullDimLE 1 (X.presheaf.stalk Z.genericPoint) :=
    krullDimLE_of_coheight_le Z.coheight_genericPoint.le
  have hne : algebraMap _ X.functionField c ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr hc.ne_zero
  rw [Scheme.ord_eq_iff Z.coheight_genericPoint hne]
  exact Ring.ordFrac_of_isUnit hc

/-- A rational function of order one at a prime divisor is the image of a generator of the
maximal ideal of the local ring. -/
theorem exists_maximalIdeal_eq_span_of_ord_eq_one (Z : PrimeDivisor X) {f : X.functionField}
    (hf : X.ord f Z.genericPoint = 1) :
    ∃ s : X.presheaf.stalk Z.genericPoint,
      maximalIdeal (X.presheaf.stalk Z.genericPoint) = Ideal.span {s} ∧
        algebraMap _ X.functionField s = f := by
  have := Stacks.AlgebraicGeometry.UnitsNormalProper.isDiscreteValuationRing_stalk
    Z.coheight_genericPoint
  have : Ring.KrullDimLE 1 (X.presheaf.stalk Z.genericPoint) :=
    krullDimLE_of_coheight_le Z.coheight_genericPoint.le
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (X.presheaf.stalk Z.genericPoint)
  have hf0 : f ≠ 0 := by
    rintro rfl
    simp at hf
  have hϖ1 := ord_algebraMap_eq_one_of_irreducible Z hϖ
  have hϖ0 : algebraMap _ X.functionField ϖ ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr hϖ.ne_zero
  rw [Scheme.ord_eq_iff Z.coheight_genericPoint hϖ0] at hϖ1
  rw [Scheme.ord_eq_iff Z.coheight_genericPoint hf0] at hf
  obtain ⟨v, hv⟩ := Ring.associated_of_ordFrac_eq (R := X.presheaf.stalk Z.genericPoint) _ _
    (hϖ1.trans hf.symm)
  refine ⟨v * ϖ, (IsDiscreteValuationRing.irreducible_iff_uniformizer _).mp
    ((irreducible_units_mul v).mpr hϖ), ?_⟩
  rw [← hv, Units.smul_def, Algebra.smul_def, map_mul]

/-- A rational function of order zero at a prime divisor is the image of an element of the local
ring. -/
theorem exists_algebraMap_eq_of_ord_eq_zero (Z : PrimeDivisor X) {f : X.functionField}
    (hf : X.ord f Z.genericPoint = 0) :
    ∃ h : X.presheaf.stalk Z.genericPoint, algebraMap _ X.functionField h = f := by
  rcases eq_or_ne f 0 with rfl | hf0
  · exact ⟨0, map_zero _⟩
  obtain ⟨a, -, ha⟩ :=
    Stacks.AlgebraicGeometry.UnitsNormalProper.exists_isUnit_of_ord_eq_zero
      Z.coheight_genericPoint hf0 hf
  exact ⟨a, ha⟩

end Order

section Divisor

variable {k : Type u} [Field k] [PerfectField k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
  [IsCurve k sX] [IsNormal X] [IsLocallyNoetherian X]
  {K : Type u} [Field K] [Algebra k K] {e : K ≃+* X.functionField}

/-- At every prime divisor, a rational differential is a multiple of the differential of a
rational function of order one. -/
theorem exists_ord_eq_one_eq_smul_D
    (he : ∀ a : k,
      e (algebraMap k K a) = @algebraMap k X.functionField _ _ (functionFieldAlgebra k sX) a)
    (Z : PrimeDivisor X) (ω : Ω[K⁄k]) :
    ∃ t g : K, X.ord (e t) Z.genericPoint = 1 ∧ ω = g • KaehlerDifferential.D k K t := by
  have := Stacks.AlgebraicGeometry.UnitsNormalProper.isDiscreteValuationRing_stalk
    Z.coheight_genericPoint
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (X.presheaf.stalk Z.genericPoint)
  have hs := (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ
  obtain ⟨g, hg⟩ := exists_eq_smul_D_stalkToField he Z hs ω
  exact ⟨_, g, by rw [apply_stalkToField]; exact ord_algebraMap_eq_one_of_irreducible Z hϖ, hg⟩

/-- **The coefficient does not depend on the uniformizer.** If `ω = g · dt = g' · dt'` with `t`
and `t'` of order one at a prime divisor `Z`, then `g` and `g'` have the same order at `Z`. -/
theorem ord_eq_of_eq_smul_D
    (he : ∀ a : k,
      e (algebraMap k K a) = @algebraMap k X.functionField _ _ (functionFieldAlgebra k sX) a)
    {ω : Ω[K⁄k]} (hω : ω ≠ 0) (Z : PrimeDivisor X) {t t' g g' : K}
    (ht : X.ord (e t) Z.genericPoint = 1) (ht' : X.ord (e t') Z.genericPoint = 1)
    (hg : ω = g • KaehlerDifferential.D k K t) (hg' : ω = g' • KaehlerDifferential.D k K t') :
    X.ord (e g) Z.genericPoint = X.ord (e g') Z.genericPoint := by
  obtain ⟨s, hs, hst⟩ := exists_maximalIdeal_eq_span_of_ord_eq_one Z ht
  obtain ⟨s', hs', hst'⟩ := exists_maximalIdeal_eq_span_of_ord_eq_one Z ht'
  have hts : stalkToField e Z.genericPoint s = t := e.injective (by rw [apply_stalkToField, hst])
  have hts' : stalkToField e Z.genericPoint s' = t' :=
    e.injective (by rw [apply_stalkToField, hst'])
  obtain ⟨h, hh⟩ := exists_D_stalkToField_eq_smul he Z hs' s
  obtain ⟨h', hh'⟩ := exists_D_stalkToField_eq_smul he Z hs s'
  rw [hts, hts'] at hh hh'
  have hdt : KaehlerDifferential.D k K t ≠ 0 := by
    rintro h0
    exact hω (by rw [hg, h0, smul_zero])
  have hdt' : KaehlerDifferential.D k K t' ≠ 0 := by
    rintro h0
    exact hω (by rw [hg', h0, smul_zero])
  have hunit : h * h' = 1 := by
    apply stalkToField_injective (e := e) Z.genericPoint
    apply smul_left_injective K hdt'
    change (stalkToField e _ (h * h')) • KaehlerDifferential.D k K t' =
      (stalkToField e _ 1) • KaehlerDifferential.D k K t'
    rw [map_mul, map_one, one_smul, mul_comm, mul_smul, ← hh, ← hh']
  have hg0 : g ≠ 0 := by
    rintro rfl
    exact hω (by rw [hg, zero_smul])
  have hgg : g * stalkToField e Z.genericPoint h = g' := by
    apply smul_left_injective K hdt'
    simp only [mul_smul, ← hh, ← hg, ← hg']
  have hu := IsUnit.of_mul_eq_one h' hunit
  rw [← hgg, e.map_mul, apply_stalkToField, Scheme.ord_mul (RingEquiv.map_ne_zero_iff e |>.mpr hg0)
    ((map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr hu.ne_zero),
    ord_algebraMap_eq_zero_of_isUnit Z hu, add_zero]

/-- **Uniformizers on an affine chart.** Let `U` be an affine open containing the generic point
of a prime divisor `Z`, let `S` generate its ring of sections over `k`, and let `b₀` be a section
whose differential is nonzero. If `d b = r b · d b₀` for every `b ∈ S`, with each `r b` of order
zero at `Z`, then `d b₀` is a unit multiple of `dt` for every `t` of order one at `Z`. -/
theorem exists_isUnit_D_eq_smul_D
    (he : ∀ a : k,
      e (algebraMap k K a) = @algebraMap k X.functionField _ _ (functionFieldAlgebra k sX) a)
    (Z : PrimeDivisor X) {U : X.Opens} (hU : IsAffineOpen U) (hZU : Z.genericPoint ∈ U)
    [Nonempty U] (S : Set Γ(X, U))
    (hS : letI : Algebra k Γ(X, U) :=
        ((Scheme.ΓSpecIso (.of k)).inv ≫ sX.appLE ⊤ U le_top).hom.toAlgebra
      Algebra.adjoin k S = ⊤)
    (b₀ : Γ(X, U)) (r : Γ(X, U) → K)
    (hr : ∀ b ∈ S, KaehlerDifferential.D k K (e.symm (X.germToFunctionField U b)) =
      r b • KaehlerDifferential.D k K (e.symm (X.germToFunctionField U b₀)))
    (hr0 : ∀ b ∈ S, X.ord (e (r b)) Z.genericPoint = 0)
    (hb₀ : KaehlerDifferential.D k K (e.symm (X.germToFunctionField U b₀)) ≠ 0)
    {t : K} (ht : X.ord (e t) Z.genericPoint = 1) :
    ∃ c : X.presheaf.stalk Z.genericPoint, IsUnit c ∧
      KaehlerDifferential.D k K (e.symm (X.germToFunctionField U b₀)) =
        stalkToField e _ c • KaehlerDifferential.D k K t := by
  let : Algebra k Γ(X, U) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ sX.appLE ⊤ U le_top).hom.toAlgebra
  set w := KaehlerDifferential.D k K (e.symm (X.germToFunctionField U b₀))
  let ι := stalkToField e Z.genericPoint
  let ρ := (X.presheaf.germ U Z.genericPoint hZU).hom
  have hιρ : ∀ b, ι (ρ b) = e.symm (X.germToFunctionField U b) := fun b => by
    apply e.injective
    simp only [ι, ρ, apply_stalkToField, RingEquiv.apply_symm_apply,
      Scheme.algebraMap_germ_eq_germToFunctionField]
  let P : X.presheaf.stalk Z.genericPoint → Prop := fun o =>
    ∃ h, KaehlerDifferential.D k K (ι o) = ι h • w
  have hPmul : ∀ o₁ o₂, P o₁ → P o₂ → P (o₁ * o₂) := by
    rintro o₁ o₂ ⟨h₁, hh₁⟩ ⟨h₂, hh₂⟩
    refine ⟨o₁ * h₂ + o₂ * h₁, ?_⟩
    rw [map_mul, Derivation.leibniz, hh₁, hh₂, smul_smul, smul_smul, ← add_smul, map_add,
      map_mul, map_mul]
  have hPB : ∀ b, P (ρ b) := by
    intro b
    have hb : b ∈ Algebra.adjoin k S := hS ▸ Algebra.mem_top
    induction hb using Algebra.adjoin_induction with
    | mem b hb =>
      obtain ⟨h, hh⟩ := exists_algebraMap_eq_of_ord_eq_zero Z (hr0 b hb)
      refine ⟨h, ?_⟩
      rw [hιρ, hr b hb]
      congr 1
      apply e.injective
      simp only [ι, apply_stalkToField, hh]
    | algebraMap a =>
      refine ⟨0, ?_⟩
      rw [hιρ, RingHom.algebraMap_toAlgebra, germToFunctionField_appLE he,
        Derivation.map_algebraMap, map_zero, zero_smul]
    | add b₁ b₂ _ _ h₁ h₂ =>
      obtain ⟨h₁', hh₁⟩ := h₁
      obtain ⟨h₂', hh₂⟩ := h₂
      exact ⟨h₁' + h₂', by rw [map_add, map_add, map_add, hh₁, hh₂, map_add, add_smul]⟩
    | mul b₁ b₂ _ _ h₁ h₂ =>
      rw [map_mul]
      exact hPmul _ _ h₁ h₂
  have hPinv : ∀ o o', o * o' = 1 → P o → P o' := by
    rintro o o' hoo ⟨h, hh⟩
    refine ⟨-(o' * o' * h), ?_⟩
    have h0 : KaehlerDifferential.D k K (ι (o * o')) = 0 := by
      rw [hoo, map_one, Derivation.map_one_eq_zero]
    rw [map_mul, Derivation.leibniz, hh, add_comm] at h0
    have hιoo : ι o' * ι o = 1 := by rw [← map_mul, mul_comm, hoo, map_one]
    calc KaehlerDifferential.D k K (ι o')
        = (ι o' * ι o) • KaehlerDifferential.D k K (ι o') := by rw [hιoo, one_smul]
      _ = ι o' • (ι o • KaehlerDifferential.D k K (ι o')) := mul_smul _ _ _
      _ = ι o' • -(ι o' • ι h • w) := by rw [eq_neg_of_add_eq_zero_right h0]
      _ = ι (-(o' * o' * h)) • w := by
        rw [map_neg, map_mul, map_mul, smul_neg, neg_smul, smul_smul, smul_smul, mul_assoc]
  have hPall : ∀ o, P o := by
    intro o
    let := TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨Z.genericPoint, hZU⟩ : U)
    have := hU.isLocalization_stalk ⟨Z.genericPoint, hZU⟩
    obtain ⟨⟨b, m⟩, hbm⟩ :=
      IsLocalization.surj (hU.primeIdealOf ⟨Z.genericPoint, hZU⟩).asIdeal.primeCompl o
    obtain ⟨μ, hμ⟩ := IsLocalization.map_units (X.presheaf.stalk Z.genericPoint) m
    have hρ : ∀ b', algebraMap Γ(X, U) (X.presheaf.stalk Z.genericPoint) b' = ρ b' := fun _ => rfl
    rw [hρ, hρ] at hbm
    rw [hρ] at hμ
    have ho : o = ρ b * ↑μ⁻¹ := by
      rw [← hbm, ← hμ, mul_assoc, Units.mul_inv, mul_one]
    rw [ho]
    exact hPmul _ _ (hPB b) (hPinv _ _ (by rw [← hμ, Units.mul_inv]) (hPB m))
  obtain ⟨s, hs, hst⟩ := exists_maximalIdeal_eq_span_of_ord_eq_one Z ht
  have hts : ι s = t := e.injective (by simp only [ι, apply_stalkToField, hst])
  obtain ⟨h₁, hh₁⟩ := hPall s
  obtain ⟨c, hc⟩ := exists_D_stalkToField_eq_smul he Z hs (ρ b₀)
  rw [hιρ] at hc
  have hc1 : c * h₁ = 1 := by
    apply stalkToField_injective (e := e) Z.genericPoint
    apply smul_left_injective K hb₀
    change ι (c * h₁) • w = ι 1 • w
    rw [map_one, one_smul, map_mul, mul_smul, ← hh₁]
    exact hc.symm
  refine ⟨c, IsUnit.of_mul_eq_one h₁ hc1, ?_⟩
  rw [← hts]
  exact hc

/-- **Local finiteness.** A coefficient family on the prime divisors of a normal curve over a
perfect field that is computed, at each prime divisor, from every presentation `ω = g · dt` of a
nonzero rational differential with `t` of order one, is a Weil divisor. -/
theorem mem_weilDivisor_of_isDivisorOfRationalDifferential
    (he : ∀ a : k,
      e (algebraMap k K a) = @algebraMap k X.functionField _ _ (functionFieldAlgebra k sX) a)
    {ω : Ω[K⁄k]} (hω : ω ≠ 0) (n : PrimeDivisor X → ℤ)
    (hn : ∀ (Z : PrimeDivisor X) (t g : K), X.ord (e t) Z.genericPoint = 1 →
      ω = g • KaehlerDifferential.D k K t → n Z = X.ord (e g) Z.genericPoint) :
    n ∈ WeilDivisor X := by
  apply mem_weilDivisor_of_forall_exists_open
  intro x
  rcases isEmpty_or_nonempty (PrimeDivisor X) with hX | ⟨⟨Z₀⟩⟩
  · exact ⟨Set.univ, isOpen_univ, trivial, Set.toFinite _⟩
  obtain ⟨U, hU, hxU, -⟩ :=
    exists_isAffineOpen_mem_and_subset (show x ∈ (⊤ : X.Opens) from trivial)
  have : Nonempty U := ⟨⟨x, hxU⟩⟩
  let : Algebra k Γ(X, U) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ sX.appLE ⊤ U le_top).hom.toAlgebra
  have hftA : RingHom.FiniteType (algebraMap k Γ(X, U)) := by
    change (((Scheme.ΓSpecIso (.of k)).inv ≫ sX.appLE ⊤ U le_top).hom).FiniteType
    exact (sX.finiteType_appLE (isAffineOpen_top _) hU le_top).comp
      (RingHom.FiniteType.of_surjective _
        (Scheme.ΓSpecIso (.of k)).symm.commRingCatIsoToRingEquiv.surjective)
  have : Algebra.FiniteType k Γ(X, U) := RingHom.finiteType_algebraMap.mp hftA
  obtain ⟨S, hS⟩ := Algebra.FiniteType.out (R := k) (A := Γ(X, U))
  have := functionField_isFractionRing_of_isAffineOpen X U hU
  obtain ⟨b₀, hb₀⟩ : ∃ b₀ : Γ(X, U),
      KaehlerDifferential.D k K (e.symm (X.germToFunctionField U b₀)) ≠ 0 := by
    by_contra! h
    have hbot := KaehlerDifferential.eq_top_of_forall_D_mem
      (e.symm.toRingHom.comp (algebraMap Γ(X, U) X.functionField))
      (exists_mul_eq_of_isFractionRing e) (⊥ : Submodule K Ω[K⁄k]) fun b => by
        rw [Submodule.mem_bot]
        exact h b
    exact hω ((Submodule.mem_bot K).mp (hbot ▸ Submodule.mem_top))
  have h1d := exists_eq_smul_of_ne_zero he Z₀ hb₀
  obtain ⟨g₀, hg₀⟩ := h1d ω
  choose r hr using fun b : Γ(X, U) =>
    h1d (KaehlerDifferential.D k K (e.symm (X.germToFunctionField U b)))
  obtain ⟨V₀, hV₀, hfin₀⟩ := Stacks.Chow.locallyFiniteSupport_ord X (e g₀) x
  choose V hV hfin using fun b : S => Stacks.Chow.locallyFiniteSupport_ord X (e (r b)) x
  have hT : (U : Set X) ∩ V₀ ∩ ⋂ b, V b ∈ nhds x :=
    Filter.inter_mem (Filter.inter_mem (U.isOpen.mem_nhds hxU) hV₀) (Filter.iInter_mem.mpr hV)
  obtain ⟨W, hWT, hWo, hxW⟩ := mem_nhds_iff.mp hT
  refine ⟨W, hWo, hxW, ?_⟩
  have hfinU : (V₀ ∩ Function.support (X.ord (e g₀)) ∪
      ⋃ b, V b ∩ Function.support (X.ord (e (r b)))).Finite :=
    hfin₀.union (Set.finite_iUnion hfin)
  refine (hfinU.preimage PrimeDivisor.genericPoint_injective.injOn).subset ?_
  rintro Z ⟨hZW, hnZ⟩
  obtain ⟨⟨hZU, hZV₀⟩, hZV⟩ := hWT hZW
  rw [Set.mem_iInter] at hZV
  by_contra hnot
  simp only [Set.mem_preimage, Set.mem_union, Set.mem_inter_iff, Function.mem_support,
    Set.mem_iUnion, not_or, not_exists, not_and, not_not] at hnot
  obtain ⟨h0, hr0⟩ := hnot
  obtain ⟨t, g, ht, hg⟩ := exists_ord_eq_one_eq_smul_D he Z ω
  obtain ⟨c, hc, hcw⟩ := exists_isUnit_D_eq_smul_D he Z hU hZU (S : Set Γ(X, U)) hS b₀ r
    (fun b _ => hr b) (fun b hb => hr0 ⟨b, hb⟩ (hZV ⟨b, hb⟩)) hb₀ ht
  have hg₀0 : g₀ ≠ 0 := by
    rintro rfl
    exact hω (by rw [hg₀, zero_smul])
  apply hnZ
  have hωc : ω = (g₀ * stalkToField e _ c) • KaehlerDifferential.D k K t := by
    rw [hg₀, hcw, smul_smul]
  rw [hn Z t _ ht hωc, e.map_mul, apply_stalkToField,
    Scheme.ord_mul (RingEquiv.map_ne_zero_iff e |>.mpr hg₀0)
      ((map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr hc.ne_zero), h0 hZV₀,
    ord_algebraMap_eq_zero_of_isUnit Z hc, add_zero]

/-- **Stacks 09U0.** A nonzero rational differential `ω` on a normal curve over a perfect field
has a unique divisor of zeros and poles: there is exactly one Weil divisor whose coefficient at
every prime divisor `Z` is the order of vanishing at `Z` of `g`, for every presentation
`ω = g · dt` with `t` of order one at `Z`. -/
@[stacks 09U0 "the divisor of zeros and poles of ω exists and is unique on a normal curve"]
theorem existsUnique_isDivisorOfRationalDifferential
    (k : Type u) [Field k] [PerfectField k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k))
    [IsCurve k sX] [IsNormal X] [IsLocallyNoetherian X]
    {K : Type u} [Field K] [Algebra k K] (e : K ≃+* X.functionField)
    (he : ∀ a : k,
      e (algebraMap k K a) = @algebraMap k X.functionField _ _ (functionFieldAlgebra k sX) a)
    (ω : Ω[K⁄k]) (hω : ω ≠ 0) :
    ∃! D : WeilDivisor X, IsDivisorOfRationalDifferential X e ω D := by
  choose t g ht hg using fun Z : PrimeDivisor X => exists_ord_eq_one_eq_smul_D he Z ω
  let n : PrimeDivisor X → ℤ := fun Z => X.ord (e (g Z)) Z.genericPoint
  have hn : ∀ (Z : PrimeDivisor X) (t' g' : K), X.ord (e t') Z.genericPoint = 1 →
      ω = g' • KaehlerDifferential.D k K t' → n Z = X.ord (e g') Z.genericPoint :=
    fun Z _ _ ht' hg' => ord_eq_of_eq_smul_D he hω Z (ht Z) ht' (hg Z) hg'
  refine ⟨⟨n, mem_weilDivisor_of_isDivisorOfRationalDifferential he hω n hn⟩, hn, ?_⟩
  intro D hD
  apply Subtype.ext
  funext Z
  exact hD Z (t Z) (g Z) (ht Z) (hg Z)

/-- **Stacks 09U0.** A nonzero rational differential on a normal curve over a perfect field has
a divisor of zeros and poles. -/
@[stacks 09U0 "the divisor of zeros and poles of ω exists on a normal curve"]
theorem exists_isDivisorOfRationalDifferential_of_isCurve
    (k : Type u) [Field k] [PerfectField k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k))
    [IsCurve k sX] [IsNormal X] [IsLocallyNoetherian X]
    {K : Type u} [Field K] [Algebra k K] (e : K ≃+* X.functionField)
    (he : ∀ a : k,
      e (algebraMap k K a) = @algebraMap k X.functionField _ _ (functionFieldAlgebra k sX) a)
    (ω : Ω[K⁄k]) (hω : ω ≠ 0) :
    ∃ D : WeilDivisor X, IsDivisorOfRationalDifferential X e ω D :=
  (existsUnique_isDivisorOfRationalDifferential k sX e he ω hω).exists

end Divisor

end AlgebraicGeometry

end
