module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import StacksFrontier.AlgebraicGeometry.Morphisms.Etale.Basic
public import StacksFrontier.AlgebraicGeometry.Pullback.AffineOpens
public import StacksFrontier.RingTheory.Unramified.LocusBaseChangeAtPrime
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The unramified locus of a base change

Let
```
X' → X
↓    ↓
Y' → Y
```
be a cartesian diagram of schemes with `f : X ⟶ Y` locally of finite type, and let `f' : X' ⟶ Y'`
be the base-changed morphism. This file proves that a point of `X'` is a point of
unramifiedness of `f'` precisely when its image in `X` is a point of unramifiedness of `f`.

## Main results

* `AlgebraicGeometry.unramifiedAt_iff_of_isPullback`: unramifiedness of a morphism at a point is
  unchanged by base change, in both directions.

## Implementation notes

Both sides are read on an affine chart. Unramifiedness at a point is formal unramifiedness of the
stalk map there, which is chart-independent
(`AlgebraicGeometry.formallyUnramified_stalkMap_iff`): one direction of that is formal, and the
other shrinks an affine chart to a basic open on which the map of sections becomes unramified,
which is where the finite type hypothesis is used. A cartesian square of schemes induces a
pushout square on the sections over compatible affine opens
(`AlgebraicGeometry.algebra_isPushout_appLE_of_isPullback`), the affine open of the source of the
base change being `g' ⁻¹ᵁ U ⊓ f' ⁻¹ᵁ V'`, and the whole content is then the commutative algebra
of `Algebra.isUnramifiedAt_iff_isUnramifiedAt_of_isPushout`.

No flatness, affineness, Noetherian or finite presentation hypothesis is needed, and local
finite type of the base-changed morphism is not assumed: it follows from the square by
`CategoryTheory.MorphismProperty.IsStableUnderBaseChange.of_isPullback`.

## References

* [Stacks Project, Tag 0475](https://stacks.math.columbia.edu/tag/0475)
* [Stacks Project, Tag 02G4](https://stacks.math.columbia.edu/tag/02G4)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- Every point of `X` lies in an affine open mapping into an affine open of `Y`. -/
private lemma exists_isAffineOpen_le_preimage {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X) :
    ∃ (V : Y.Opens) (_ : IsAffineOpen V) (U : X.Opens) (_ : IsAffineOpen U),
      x ∈ U ∧ U ≤ f ⁻¹ᵁ V ∧ f x ∈ V := by
  obtain ⟨V, hV, hfxV, -⟩ := exists_isAffineOpen_mem_and_subset (x := f x) (U := ⊤) trivial
  obtain ⟨U, hU, hxU, hUV⟩ := exists_isAffineOpen_mem_and_subset (U := f ⁻¹ᵁ V) hfxV
  exact ⟨V, hV, U, hU, hxU, hUV, hfxV⟩

/-- **Unramifiedness at a point is formal unramifiedness of the stalk map.** For a morphism
locally of finite type, the existence of an affine chart with an unramified map of sections is
equivalent to the chart-independent condition that the stalk map be formally unramified. -/
private lemma unramifiedAt_iff_formallyUnramified_stalkMap {X Y : Scheme.{u}} (f : X ⟶ Y)
    [LocallyOfFiniteType f] (x : X) :
    UnramifiedAt f x ↔ (f.stalkMap x).hom.FormallyUnramified := by
  constructor
  · rintro ⟨U, hU, hxU, V, hV, e, halg⟩
    let _ : Algebra Γ(Y, V) Γ(X, U) := (f.appLE V U e).hom.toAlgebra
    have _ : Algebra.FormallyUnramified Γ(Y, V) Γ(X, U) := halg.formallyUnramified
    exact (formallyUnramified_stalkMap_iff V hV U hU e hxU).mpr
      (Algebra.FormallyUnramified.comp Γ(Y, V) Γ(X, U) _)
  · intro hstalk
    obtain ⟨V, hV, U, hU, hxU, hUV, -⟩ := exists_isAffineOpen_le_preimage f x
    let _ : Algebra Γ(Y, V) Γ(X, U) := (f.appLE V U hUV).hom.toAlgebra
    have _ : Algebra.FiniteType Γ(Y, V) Γ(X, U) :=
      RingHom.finiteType_algebraMap.mp (f.finiteType_appLE hV hU hUV)
    have _ : Algebra.IsUnramifiedAt Γ(Y, V) (hU.primeIdealOf ⟨x, hxU⟩).asIdeal :=
      (formallyUnramified_stalkMap_iff V hV U hU hUV hxU).mp hstalk
    obtain ⟨r, hr, hur⟩ := Algebra.exists_unramified_of_isUnramifiedAt
      (R := Γ(Y, V)) (hU.primeIdealOf ⟨x, hxU⟩).asIdeal
    have hrle : X.basicOpen r ≤ f ⁻¹ᵁ V := (X.basicOpen_le r).trans hUV
    refine ⟨X.basicOpen r, hU.basicOpen r, ?_, V, hV, hrle, ?_⟩
    · change (⟨x, hxU⟩ : U).1 ∈ X.basicOpen r
      rw [← hU.fromSpec_primeIdealOf ⟨x, hxU⟩]
      exact (hU.fromSpec_preimage_basicOpen r).ge hr
    · let _ : Algebra Γ(Y, V) Γ(X, X.basicOpen r) :=
        (f.appLE V (X.basicOpen r) hrle).hom.toAlgebra
      have _ : IsLocalization.Away r Γ(X, X.basicOpen r) := hU.isLocalization_basicOpen r
      have _ : IsScalarTower Γ(Y, V) Γ(X, U) Γ(X, X.basicOpen r) := by
        refine IsScalarTower.of_algebraMap_eq' ?_
        simp only [RingHom.algebraMap_toAlgebra]
        exact (CommRingCat.hom_ext_iff.mp
          (f.appLE_map hUV (homOfLE (X.basicOpen_le r)).op)).symm
      have _ : Algebra.Unramified Γ(Y, V) (Localization.Away r) := hur
      exact Algebra.Unramified.of_equiv
        ((IsLocalization.algEquiv (.powers r) (Localization.Away r)
          Γ(X, X.basicOpen r)).restrictScalars Γ(Y, V))

/-- **Stacks Project, Tag 0475, the base-change half, pointwise.** Let
```
X' → X
↓    ↓
Y' → Y
```
be a cartesian diagram of schemes with `f : X ⟶ Y` locally of finite type, and let
`f' : X' ⟶ Y'` be the base change of `f` along `g : Y' ⟶ Y`. A point `x'` of `X'` is a point of
unramifiedness of `f'` if and only if its image `g' x'` in `X` is a point of unramifiedness
of `f`. -/
@[stacks 0475 "base change of the unramified locus", sga "1 I 3.5" "more general"]
theorem unramifiedAt_iff_of_isPullback {X' X Y' Y : Scheme.{u}}
    {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (sq : IsPullback g' f' f g) [LocallyOfFiniteType f] (x' : X') :
    UnramifiedAt f (g'.base x') ↔ UnramifiedAt f' x' := by
  have _ : LocallyOfFiniteType f' :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback sq ‹LocallyOfFiniteType f›
  have hbase : g (f' x') = f (g' x') := by
    simpa only [Scheme.Hom.comp_apply] using (congrArg (fun k : X' ⟶ Y ↦ k x') sq.w).symm
  -- affine charts: `V ∋ f (g' x')` in `Y`, `U ∋ g' x'` in `X` over `V`, `V' ∋ f' x'` in `Y'`
  -- over `V`, and the affine open `U' = g' ⁻¹ᵁ U ⊓ f' ⁻¹ᵁ V'` of `X'` containing `x'`
  obtain ⟨V, hV, U, hU, hxU, hUV, hfxV⟩ := exists_isAffineOpen_le_preimage f (g' x')
  have hfx'V : f' x' ∈ g ⁻¹' (V : Set Y) := by rwa [Set.mem_preimage, hbase]
  obtain ⟨_, ⟨V', hV', rfl⟩, hfx'V', hV'V⟩ :=
    Y'.isBasis_affineOpens.exists_subset_of_mem_open hfx'V (V.2.preimage g.continuous)
  have hU' : IsAffineOpen (g' ⁻¹ᵁ U ⊓ f' ⁻¹ᵁ V') :=
    IsAffineOpen.inf_preimage_of_isPullback sq hV hU hUV hV' hV'V rfl
  have hxU' : x' ∈ g' ⁻¹ᵁ U ⊓ f' ⁻¹ᵁ V' := ⟨hxU, hfx'V'⟩
  have e₁ : g' ⁻¹ᵁ U ⊓ f' ⁻¹ᵁ V' ≤ g' ⁻¹ᵁ U := inf_le_left
  have e₂ : g' ⁻¹ᵁ U ⊓ f' ⁻¹ᵁ V' ≤ f' ⁻¹ᵁ V' := inf_le_right
  -- the ring data of the chart
  algebraize [(f.appLE V U hUV).hom, (g.appLE V V' hV'V).hom,
    (g'.appLE U (g' ⁻¹ᵁ U ⊓ f' ⁻¹ᵁ V') e₁).hom,
    (f'.appLE V' (g' ⁻¹ᵁ U ⊓ f' ⁻¹ᵁ V') e₂).hom]
  let _ : Algebra Γ(Y, V) Γ(X', g' ⁻¹ᵁ U ⊓ f' ⁻¹ᵁ V') :=
    ((f'.appLE V' (g' ⁻¹ᵁ U ⊓ f' ⁻¹ᵁ V') e₂).hom.comp (g.appLE V V' hV'V).hom).toAlgebra
  have _ : IsScalarTower Γ(Y, V) Γ(Y', V') Γ(X', g' ⁻¹ᵁ U ⊓ f' ⁻¹ᵁ V') :=
    IsScalarTower.of_algebraMap_eq' rfl
  have _ : IsScalarTower Γ(Y, V) Γ(X, U) Γ(X', g' ⁻¹ᵁ U ⊓ f' ⁻¹ᵁ V') := by
    refine IsScalarTower.of_algebraMap_eq' ?_
    simp only [RingHom.algebraMap_toAlgebra]
    exact (congrArg CommRingCat.Hom.hom (isPushout_appLE_of_isPullback sq hV hU hUV hV' hV'V
      (U' := g' ⁻¹ᵁ U ⊓ f' ⁻¹ᵁ V') rfl).w).symm
  have hpo : Algebra.IsPushout Γ(Y, V) Γ(Y', V') Γ(X, U)
      Γ(X', g' ⁻¹ᵁ U ⊓ f' ⁻¹ᵁ V') :=
    algebra_isPushout_appLE_of_isPullback sq hV hU hUV hV' hV'V rfl
      (fun _ ↦ rfl) (fun _ ↦ rfl) (fun _ ↦ rfl) (fun _ ↦ rfl)
  have _ : Algebra.IsPushout Γ(Y, V) Γ(X, U) Γ(Y', V')
      Γ(X', g' ⁻¹ᵁ U ⊓ f' ⁻¹ᵁ V') := hpo.symm
  have _ : Algebra.FiniteType Γ(Y, V) Γ(X, U) :=
    RingHom.finiteType_algebraMap.mp (f.finiteType_appLE hV hU hUV)
  -- the primes of the chart, and their correspondence
  have _ : (hU'.primeIdealOf ⟨x', hxU'⟩).asIdeal.LiesOver
      (hU.primeIdealOf ⟨g' x', hxU⟩).asIdeal :=
    ⟨congr($(IsAffineOpen.comap_primeIdealOf_appLE U hU _ hU' e₁ hxU').1).symm⟩
  rw [unramifiedAt_iff_formallyUnramified_stalkMap f (g' x'),
    unramifiedAt_iff_formallyUnramified_stalkMap f' x',
    formallyUnramified_stalkMap_iff V hV U hU hUV hxU,
    formallyUnramified_stalkMap_iff V' hV' _ hU' e₂ hxU']
  exact Algebra.isUnramifiedAt_iff_isUnramifiedAt_of_isPushout Γ(Y, V) Γ(X, U) Γ(Y', V')
    Γ(X', g' ⁻¹ᵁ U ⊓ f' ⁻¹ᵁ V') (hU.primeIdealOf ⟨g' x', hxU⟩).asIdeal
    (hU'.primeIdealOf ⟨x', hxU'⟩).asIdeal

end AlgebraicGeometry

end
