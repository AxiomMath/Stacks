module

public import StacksFrontier.AlgebraicGeometry.Spaces.RecoveringMorphisms.LocalRoots
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleLocallyRinged
public import StacksFrontier.AlgebraicGeometry.Spaces.StrictTransformLocalGenerators
public import StacksFrontier.RingTheory.Henselian.StrictlyHenselianOfStandardEtaleRoots

/-!
# The structure sheaf of the small étale site is locally local and locally henselian

Let `Z` be an algebraic space and `𝒪` the structure sheaf of its small étale site.  This file
proves two sectionwise statements about `𝒪`, in the form in which the proof of Stacks 04KL
consumes them to see that the stalk of `𝒪` at any point of the small étale topos of `Z` is a
strictly henselian local ring:

* every section is, on a covering, either a unit or has unit complement;
* for a monic `f` and a `g` over the sections on a chart `W`, if for some unit `c` the image of
  `g f'` in `K[X]/(f)` is non-nilpotent for every map to a field `K` not killing `c`, then on a
  covering of `W` the polynomial `f` acquires a root at which `g f'` is invertible.

The second is the étale-local form of Hensel's lemma: on an affine piece of `W` the standard
étale algebra `A[X]_{g f'}/(f)` is surjective on spectra, by
`StandardEtalePair.comap_surjective_of_not_isNilpotent`, so its chart covers the piece and carries
the root (`AlgebraicGeometry.Space.rootSieve_mem_topology`).

## Main results

* `AlgebraicGeometry.Space.structureSheaf_locallyEitherUnit`
* `AlgebraicGeometry.Space.structureSheaf_exists_root`

## References

* [Stacks Project, Tag 04KL](https://stacks.math.columbia.edu/tag/04KL)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Polynomial

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- Mapping `g f'` along a composite of ring maps, in two steps. -/
private theorem map_mul_derivative_map {A A' K : Type*} [CommRing A] [CommRing A'] [CommRing K]
    (ρ : A →+* A') (ψ : A' →+* K) (f g : A[X]) :
    ((g.map ρ) * derivative (f.map ρ)).map ψ = (g * derivative f).map (ψ.comp ρ) := by
  rw [Polynomial.derivative_map, ← Polynomial.map_mul, Polynomial.map_map]

/-- **Roots of standard étale polynomials exist étale locally on an affine chart.** -/
theorem rootSieve_mem_topology_of_isAffine {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (U : SmallEtale B S hS F) [IsAffine ((BigFppfOver.toScheme B S hS).obj U.obj.left)]
    (f g : Γ((BigFppfOver.toScheme B S hS).obj U.obj.left, ⊤)[X]) (hf : f.Monic)
    (c : Γ((BigFppfOver.toScheme B S hS).obj U.obj.left, ⊤)) (hc : IsUnit c)
    (h : ∀ (K : Type u) [Field K] (ψ : Γ((BigFppfOver.toScheme B S hS).obj U.obj.left, ⊤) →+* K),
      ψ c ≠ 0 → ¬ IsNilpotent (AdjoinRoot.mk (f.map ψ) ((g * derivative f).map ψ))) :
    rootSieve B S hS U f (g * derivative f) ∈ SmallEtale.topology B S hS F U := by
  let P : StandardEtalePair Γ((BigFppfOver.toScheme B S hS).obj U.obj.left, ⊤) :=
    ⟨f, hf, g * derivative f, ⟨g, 0, 1, by ring⟩⟩
  have : Surjective (Spec.map (CommRingCat.ofHom
      (algebraMap Γ((BigFppfOver.toScheme B S hS).obj U.obj.left, ⊤) P.Ring))) :=
    ⟨P.comap_surjective_of_not_isNilpotent fun p _ ↦
      h p.ResidueField _ (hc.map (algebraMap _ p.ResidueField)).ne_zero⟩
  exact rootSieve_mem_topology B S hS U P
    (Surjective.surj (f := standardEtaleSchemeHom B S hS U P))

/-- Restriction of global functions along a composite of morphisms of étale charts. -/
theorem chartFunctionRes_comp {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {U W W' : SmallEtale B S hS F}
    (j : W ⟶ U) (k : W' ⟶ W) :
    chartFunctionRes B S hS (k ≫ j) = chartFunctionRes B S hS j ≫ chartFunctionRes B S hS k := by
  simp [chartFunctionRes, Scheme.Hom.comp_appTop]

/-- The root sieve of `(f, g f')` pulled back along a morphism of charts contains the root sieve
of the restrictions. -/
theorem rootSieve_le_pullback {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {U W : SmallEtale B S hS F}
    (j : W ⟶ U) (f g : Γ((BigFppfOver.toScheme B S hS).obj U.obj.left, ⊤)[X]) :
    rootSieve B S hS W (f.map (chartFunctionRes B S hS j).hom)
        (g.map (chartFunctionRes B S hS j).hom *
          derivative (f.map (chartFunctionRes B S hS j).hom)) ≤
      (rootSieve B S hS U f (g * derivative f)).pullback j := by
  intro W' k ⟨a, ha, hu⟩
  refine ⟨a, ?_, ?_⟩
  · rwa [chartFunctionRes_comp, CommRingCat.hom_comp, ← Polynomial.map_map]
  · rwa [chartFunctionRes_comp, CommRingCat.hom_comp, ← Polynomial.map_map, Polynomial.map_mul,
      ← Polynomial.derivative_map]

variable (Z : AlgebraicSpaces B S hS)

/-- Restriction in the structure sheaf of the small étale ringed topos is restriction of global
functions of the chart schemes. -/
theorem structureSheaf_map_eq_chartFunctionRes {W W' : SmallEtale B S hS Z.1} (i : W' ⟶ W) :
    (smallEtaleRingedTopos B S hS Z).O.obj.map i.op = chartFunctionRes B S hS i :=
  rfl

/-- **Sections of the structure sheaf are locally units or of unit complement.** -/
theorem structureSheaf_locallyEitherUnit (W : SmallEtale B S hS Z.1)
    (a : (smallEtaleRingedTopos B S hS Z).O.obj.obj (op W)) :
    ∃ T : Sieve W, T ∈ SmallEtale.topology B S hS Z.1 W ∧ ∀ ⦃W'⦄ (i : W' ⟶ W), T i →
      IsUnit (((smallEtaleRingedTopos B S hS Z).O.obj.map i.op) a) ∨
        IsUnit (((smallEtaleRingedTopos B S hS Z).O.obj.map i.op) (1 - a)) :=
  locallyEitherUnit_structureSheaf' B S hS Z.1 W a

/-- **Étale-local roots for the structure sheaf.** Let `W` be an étale chart of `Z`, `f` a monic
polynomial and `g` a polynomial over `Γ(W, 𝒪)`, and `c` a unit of `Γ(W, 𝒪)` such that the image
of `g f'` in `K[X]/(f)` is not nilpotent for every map `ψ` to a field with `ψ c ≠ 0`.  Then on a
covering of `W` the restriction of `f` has a root at which that of `g f'` is invertible. -/
theorem structureSheaf_exists_root (W : SmallEtale B S hS Z.1)
    (f g : ((smallEtaleRingedTopos B S hS Z).O.obj.obj (op W))[X]) (hf : f.Monic)
    (c : (smallEtaleRingedTopos B S hS Z).O.obj.obj (op W)) (hc : IsUnit c)
    (h : ∀ (K : Type u) [Field K]
      (ψ : (smallEtaleRingedTopos B S hS Z).O.obj.obj (op W) →+* K), ψ c ≠ 0 →
        ¬ IsNilpotent (AdjoinRoot.mk (f.map ψ) ((g * derivative f).map ψ))) :
    ∃ T : Sieve W, T ∈ SmallEtale.topology B S hS Z.1 W ∧ ∀ ⦃W'⦄ (i : W' ⟶ W), T i →
      ∃ a, (f.map ((smallEtaleRingedTopos B S hS Z).O.obj.map i.op).hom).eval a = 0 ∧
        IsUnit (((g * derivative f).map
          ((smallEtaleRingedTopos B S hS Z).O.obj.map i.op).hom).eval a) := by
  refine ⟨rootSieve B S hS W f (g * derivative f), ?_, fun W' i hi ↦ hi⟩
  refine (SmallEtale.topology B S hS Z.1).transitive
    (generate_isAffine_mem_topology B S hS Z.1 W) _ ?_
  rintro W'' _ ⟨W', k, j, hj, rfl⟩
  rw [Sieve.pullback_comp]
  refine (SmallEtale.topology B S hS Z.1).pullback_stable k ?_
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj W'.obj.left) := hj
  refine (SmallEtale.topology B S hS Z.1).superset_covering (rootSieve_le_pullback j f g)
    (rootSieve_mem_topology_of_isAffine W' _ _ (hf.map (chartFunctionRes B S hS j).hom) _
      (hc.map (chartFunctionRes B S hS j).hom) fun K _ ψ hψ ↦ ?_)
  have hp : (f.map (chartFunctionRes B S hS j).hom).map ψ =
      f.map (ψ.comp (chartFunctionRes B S hS j).hom) :=
    Polynomial.map_map _ _ _
  have he : ((g.map (chartFunctionRes B S hS j).hom) *
      derivative (f.map (chartFunctionRes B S hS j).hom)).map ψ =
      (g * derivative f).map (ψ.comp (chartFunctionRes B S hS j).hom) :=
    map_mul_derivative_map _ _ f g
  rw [hp, he]
  exact h K (ψ.comp (chartFunctionRes B S hS j).hom) hψ

end AlgebraicGeometry.Space
