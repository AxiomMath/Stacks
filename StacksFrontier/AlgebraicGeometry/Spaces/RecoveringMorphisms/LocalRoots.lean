module

public import Mathlib.RingTheory.Etale.StandardEtale
public import StacksFrontier.AlgebraicGeometry.Size.FiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartBaseChangeAlmostCocontinuous
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleStalkExactness

/-!
# Roots of standard étale polynomials exist étale locally on the small étale site

Let `F` be a presheaf on the big fppf site of `S` and `U` an affine étale chart of `F`.  For a
standard étale pair `(f, g)` over `A = Γ(U, 𝒪_U)` — a monic `f` and a `g` such that `f'` is
invertible in `A[X]_g/(f)` — whose standard étale algebra `A' = A[X][Y]/(f, Yg - 1)` is
faithfully surjective on spectra, the chart `Spec A' ⟶ U` covers `U` and carries a root of `f`
at which `g` is invertible.  So roots of such polynomials exist étale locally; this is the
étale-local form of the henselian property of the structure sheaf.

## Main definitions

* `AlgebraicGeometry.Space.rootSieve`: the sieve of étale charts over `U` on which `f` has a
  root at which `g` is invertible.
* `AlgebraicGeometry.Space.standardEtaleChart`: the étale chart `Spec A' ⟶ U`.

## Main results

* `AlgebraicGeometry.Space.rootSieve_mem_topology`: the sieve of étale charts over `U`
  on which the restriction of `f` has a root at which the restriction of `g` is invertible is a
  covering sieve.

## References

* [Stacks Project, Tag 04KL](https://stacks.math.columbia.edu/tag/04KL)
* [Stacks Project, Tag 04GX](https://stacks.math.columbia.edu/tag/04GX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Polynomial

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- The restriction of global functions along a morphism of étale charts. -/
abbrev chartFunctionRes {U W : SmallEtale B S hS F} (i : W ⟶ U) :
    Γ((BigFppfOver.toScheme B S hS).obj U.obj.left, ⊤) ⟶
      Γ((BigFppfOver.toScheme B S hS).obj W.obj.left, ⊤) :=
  ((BigFppfOver.toScheme B S hS).map i.hom.left).appTop

/-- The sieve of étale charts over `U` on which the restrictions of `f` and `g` admit a root of
`f` at which `g` is invertible. -/
def rootSieve (U : SmallEtale B S hS F)
    (f g : Γ((BigFppfOver.toScheme B S hS).obj U.obj.left, ⊤)[X]) :
    Sieve U where
  arrows W i := ∃ a, (f.map (chartFunctionRes B S hS i).hom).eval a = 0 ∧
    IsUnit ((g.map (chartFunctionRes B S hS i).hom).eval a)
  downward_closed {W W'} i hi j := by
    obtain ⟨a, ha, hu⟩ := hi
    have hc : chartFunctionRes B S hS (j ≫ i) =
        chartFunctionRes B S hS i ≫ chartFunctionRes B S hS j := by
      simp [chartFunctionRes]
    refine ⟨(chartFunctionRes B S hS j).hom a, ?_, ?_⟩
    · rw [hc, CommRingCat.hom_comp, ← Polynomial.map_map, Polynomial.eval_map_apply, ha,
        map_zero]
    · rw [hc, CommRingCat.hom_comp, ← Polynomial.map_map, Polynomial.eval_map_apply]
      exact hu.map _

section StandardEtale

variable (U : SmallEtale B S hS F) [IsAffine ((BigFppfOver.toScheme B S hS).obj U.obj.left)]
  (P : StandardEtalePair Γ((BigFppfOver.toScheme B S hS).obj U.obj.left, ⊤))

/-- The morphism of schemes `Spec A' ⟶ U` of the standard étale algebra of `P`. -/
abbrev standardEtaleSchemeHom :
    Spec (CommRingCat.of P.Ring) ⟶ (BigFppfOver.toScheme B S hS).obj U.obj.left :=
  Spec.map (CommRingCat.ofHom (algebraMap _ P.Ring)) ≫
    ((BigFppfOver.toScheme B S hS).obj U.obj.left).isoSpec.inv

/-- The morphism `Spec A' ⟶ U` of the standard étale algebra of `P` is étale. -/
instance etale_standardEtaleSchemeHom : Etale (standardEtaleSchemeHom B S hS U P) := by
  have : Etale (Spec.map (CommRingCat.ofHom (algebraMap
      Γ((BigFppfOver.toScheme B S hS).obj U.obj.left, ⊤) P.Ring))) :=
    (HasRingHomProperty.Spec_iff (P := @Etale)).2 (RingHom.etale_algebraMap.mpr inferInstance)
  infer_instance

/-- The spectrum of the standard étale algebra is an object of the site. -/
theorem contains_spec_standardEtale : B.Contains (Spec (CommRingCat.of P.Ring)) :=
  (Scheme.size_le_of_locallyOfFiniteType (standardEtaleSchemeHom B S hS U P)).trans_lt
    U.obj.left.left.property

/-- **The standard étale chart** `Spec A' ⟶ U` of a standard étale pair over the global functions
of an affine étale chart `U`. -/
abbrev standardEtaleChart : SmallEtale B S hS F :=
  chartOfEtaleSchemeHom B S hS U (contains_spec_standardEtale B S hS U P)
    (standardEtaleSchemeHom B S hS U P) inferInstance

/-- The morphism of étale charts from the standard étale chart to `U`. -/
abbrev standardEtaleChartMap : standardEtaleChart B S hS U P ⟶ U :=
  chartOfEtaleSchemeHomMap B S hS U (contains_spec_standardEtale B S hS U P)
    (standardEtaleSchemeHom B S hS U P) inferInstance

/-- Restriction of global functions from `U` to the standard étale chart is the structure map of
the standard étale algebra, read through `Γ(Spec A', ⊤) ≅ A'`. -/
theorem chartFunctionRes_standardEtaleChartMap :
    chartFunctionRes B S hS (standardEtaleChartMap B S hS U P) =
      CommRingCat.ofHom (algebraMap _ P.Ring) ≫ (Scheme.ΓSpecIso (CommRingCat.of P.Ring)).inv := by
  show (standardEtaleSchemeHom B S hS U P).appTop = _
  have h : ((BigFppfOver.toScheme B S hS).obj U.obj.left).isoSpec.inv.appTop ≫
      (Scheme.ΓSpecIso Γ((BigFppfOver.toScheme B S hS).obj U.obj.left, ⊤)).hom =
        CategoryStruct.id _ := by
    simp only [Scheme.isoSpec, asIso_inv, Scheme.Hom.inv_appTop, Scheme.toSpecΓ_appTop,
      IsIso.inv_hom_id]
  rw [Scheme.Hom.comp_appTop, Scheme.ΓSpecIso_inv_naturality]
  exact congrArg (· ≫ _) ((Iso.comp_hom_eq_id _).1 h)

/-- The underlying scheme of the standard étale chart is `Spec A'`. -/
theorem toScheme_standardEtaleChart :
    (BigFppfOver.toScheme B S hS).obj (standardEtaleChart B S hS U P).obj.left =
      Spec (CommRingCat.of P.Ring) := rfl

/-- The root of `f` on the standard étale chart: the image of the variable `X` of `A'`. -/
def standardEtaleRoot :
    Γ((BigFppfOver.toScheme B S hS).obj (standardEtaleChart B S hS U P).obj.left, ⊤) :=
  (Scheme.ΓSpecIso (CommRingCat.of P.Ring)).inv.hom P.X

/-- Evaluating at `standardEtaleRoot` the restriction of a polynomial `q` over `A` to the
standard étale chart gives the image of `q(X)` in `A'`, read through `Γ(Spec A', ⊤) ≅ A'`. -/
theorem eval_standardEtaleRoot (q : Γ((BigFppfOver.toScheme B S hS).obj U.obj.left, ⊤)[X]) :
    (q.map (chartFunctionRes B S hS (standardEtaleChartMap B S hS U P)).hom).eval
      (standardEtaleRoot B S hS U P) =
      (Scheme.ΓSpecIso (CommRingCat.of P.Ring)).inv.hom (Polynomial.aeval P.X q) := by
  have hρ : (chartFunctionRes B S hS (standardEtaleChartMap B S hS U P)).hom =
      (Scheme.ΓSpecIso (CommRingCat.of P.Ring)).inv.hom.comp (algebraMap _ P.Ring) :=
    congrArg CommRingCat.Hom.hom (chartFunctionRes_standardEtaleChartMap B S hS U P)
  rw [Polynomial.eval_map]
  exact (congrArg (fun φ ↦ Polynomial.eval₂ φ (standardEtaleRoot B S hS U P) q) hρ).trans
    (Polynomial.hom_eval₂ q (algebraMap _ P.Ring)
      (Scheme.ΓSpecIso (CommRingCat.of P.Ring)).inv.hom P.X).symm

/-- The standard étale chart lies in the root sieve of `(f, g)`: the image of the variable `X`
of `A'` is a root of `f` at which `g` is invertible. -/
theorem rootSieve_standardEtaleChartMap :
    (rootSieve B S hS U P.f P.g).arrows (standardEtaleChartMap B S hS U P) :=
  ⟨standardEtaleRoot B S hS U P, by rw [eval_standardEtaleRoot, P.hasMap_X.1, map_zero]; rfl,
    by rw [eval_standardEtaleRoot]; exact P.hasMap_X.2.map _⟩

/-- **Roots of a standard étale pair exist étale locally.** If the standard étale algebra of `P`
is surjective on spectra over the affine étale chart `U`, then the root sieve of `(f, g)` is a
covering sieve of `U`. -/
theorem rootSieve_mem_topology
    (hsurj : Function.Surjective (standardEtaleSchemeHom B S hS U P).base) :
    rootSieve B S hS U P.f P.g ∈ SmallEtale.topology B S hS F U := by
  refine smallEtale_sieve_of_pointwise_covering B S hS F U _ fun z ↦ ?_
  obtain ⟨z', hz'⟩ := hsurj z
  exact ⟨standardEtaleChart B S hS U P, standardEtaleChartMap B S hS U P,
    rootSieve_standardEtaleChartMap B S hS U P, z', hz'⟩

end StandardEtale

end AlgebraicGeometry.Space
