module

public import Mathlib.Algebra.Category.Ring.Constructions
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import StacksFrontier.RingTheory.Smooth.LocusBaseChangeAtPrime
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The smooth locus of a base change

Let
```
X' → X
↓    ↓
S' → S
```
be a cartesian diagram of schemes and let `W ⊆ X`, `W' ⊆ X'` be the open subschemes of points
where `X → S`, respectively `X' → S'`, is smooth. This file proves that `W'` is the inverse image
of `W` as soon as `X → S` is locally of finite presentation and, in addition, either `X → S` is
flat or `S' → S` is flat.

## Main results

* `AlgebraicGeometry.Scheme.Hom.smoothLocus_eq_preimage_of_isPullback`: the smooth locus of the
  base-changed morphism is the inverse image of the smooth locus.

## Implementation notes

Both hypotheses are read on an affine chart and the whole content is the commutative algebra of
`Algebra.isSmoothAt_iff_isSmoothAt_of_isPushout_of_flat`: smoothness at a point is smoothness of
the ring map at the corresponding prime
(`AlgebraicGeometry.formallySmooth_stalkMap_iff`), and a cartesian square of schemes induces a
pushout square on the sections over compatible affine opens. The affine open of the fibre product
used for this is `g' ⁻¹ᵁ U ⊓ f' ⁻¹ᵁ V'`, which is affine because it is the vertex of a cartesian
square of affine schemes.

The instance `AlgebraicGeometry.LocallyOfFinitePresentation` on the base-changed morphism is a
hypothesis rather than being produced inside the statement; it always holds, being
`CategoryTheory.MorphismProperty.IsStableUnderBaseChange.of_isPullback` applied to the square,
and a consumer has to introduce it in order to write down the smooth locus of that morphism at
all.

## References

* [Stacks Project, Tag 02V4](https://stacks.math.columbia.edu/tag/02V4), the set of points where
  the fibres are smooth, under base change.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

universe u

section Affine

variable {S X T P : Scheme.{u}} {f : X ⟶ S} {g : T ⟶ S} {a : P ⟶ X} {b : P ⟶ T}

/-- **A cartesian square of schemes is a pushout square on the sections over affine opens.**
Given a cartesian square with vertices `P`, `X`, `T`, `S`, an affine open `U` of the base `S` and
affine opens `V` of `X` and `W` of `T` lying over it, the open `Q = a ⁻¹ᵁ V ⊓ b ⁻¹ᵁ W` of `P` is
affine and the four rings of sections form a pushout square. -/
private lemma isAffineOpen_and_isPushout_appLE_of_isPullback (hp : IsPullback a b f g)
    {U : S.Opens} (hU : IsAffineOpen U) {V : X.Opens} (hV : IsAffineOpen V)
    {W : T.Opens} (hW : IsAffineOpen W) (hVU : V ≤ f ⁻¹ᵁ U) (hWU : W ≤ g ⁻¹ᵁ U) :
    IsAffineOpen (a ⁻¹ᵁ V ⊓ b ⁻¹ᵁ W) ∧
      IsPushout (f.appLE U V hVU) (g.appLE U W hWU)
        (a.appLE V (a ⁻¹ᵁ V ⊓ b ⁻¹ᵁ W) inf_le_left)
        (b.appLE W (a ⁻¹ᵁ V ⊓ b ⁻¹ᵁ W) inf_le_right) := by
  have _ : IsAffine U.toScheme := hU
  have _ : IsAffine V.toScheme := hV
  have _ : IsAffine W.toScheme := hW
  have hpb := Scheme.Hom.isPullback_resLE hp hWU hVU rfl
  have _ : IsAffine (a ⁻¹ᵁ V ⊓ b ⁻¹ᵁ W).toScheme := IsAffine.of_isPullback hpb
  exact ⟨‹IsAffine (a ⁻¹ᵁ V ⊓ b ⁻¹ᵁ W).toScheme›, (isPushout_appTop_of_isPullback hpb).of_iso
    U.topIso V.topIso W.topIso (a ⁻¹ᵁ V ⊓ b ⁻¹ᵁ W).topIso
    (arrowResLEAppIso f U V hVU).hom.w.symm
    (arrowResLEAppIso g U W hWU).hom.w.symm
    (arrowResLEAppIso a V _ inf_le_left).hom.w.symm
    (arrowResLEAppIso b W _ inf_le_right).hom.w.symm⟩

end Affine

variable {X S S' X' : Scheme.{u}}

/-- **The smooth locus of a base change is the inverse image of the smooth locus.** Let
```
X' → X
↓    ↓
S' → S
```
be a cartesian diagram of schemes, with `f : X ⟶ S` locally of finite presentation. Assume that
`f` is flat, or that `g : S' ⟶ S` is flat. Then the open subscheme of `X'` where the base-changed
morphism `f' : X' ⟶ S'` is smooth is the inverse image under `g' : X' ⟶ X` of the open subscheme
of `X` where `f` is smooth.

**Stacks Project, Tag 02V4.** Both of its cases are covered, the first by flatness of `f` and
the second by flatness of `g`. -/
@[stacks 02V4,
  ega "IV 17.7.2" "(ii)",
  ega "IV 17.7.4" "(v)",
  ega "IV 17.7.1" "(ii) smooth",
  sga "1 II 4.13" "special case",
  sga "3 VIB 2.5" "special case",
  sga "3 VIB 3.10" "special case",
  sga "3 X 8.9" "partial"]
theorem Scheme.Hom.smoothLocus_eq_preimage_of_isPullback {f : X ⟶ S} {g : S' ⟶ S} {f' : X' ⟶ S'}
    {g' : X' ⟶ X} [LocallyOfFinitePresentation f] [LocallyOfFinitePresentation f']
    (sq : IsPullback g' f' f g) (hflat : Flat f ∨ Flat g) :
    f'.smoothLocus = g' ⁻¹ᵁ f.smoothLocus := by
  ext x'
  change x' ∈ f'.smoothLocus ↔ g' x' ∈ f.smoothLocus
  have hbase : g (f' x') = f (g' x') := by
    simpa only [Scheme.Hom.comp_apply] using (congrArg (fun k : X' ⟶ S ↦ k x') sq.w).symm
  -- affine charts: `V ∋ f (g' x')` in `S`, `U ∋ g' x'` in `X` over `V`, `V' ∋ f' x'` in `S'`
  -- over `V`, and the affine open `U' = g' ⁻¹ᵁ U ⊓ f' ⁻¹ᵁ V'` of `X'` containing `x'`
  obtain ⟨_, ⟨V, hV, rfl⟩, hfxV, -⟩ :=
    S.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f (g' x'))) isOpen_univ
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUV⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hfxV (V.2.preimage f.continuous)
  have hfx'V : f' x' ∈ g ⁻¹' (V : Set S) := by rwa [Set.mem_preimage, hbase]
  obtain ⟨_, ⟨V', hV', rfl⟩, hfx'V', hV'V⟩ :=
    S'.isBasis_affineOpens.exists_subset_of_mem_open hfx'V (V.2.preimage g.continuous)
  obtain ⟨hU', hpo⟩ := isAffineOpen_and_isPushout_appLE_of_isPullback sq hV hU hV' hUV hV'V
  have hxU' : x' ∈ g' ⁻¹ᵁ U ⊓ f' ⁻¹ᵁ V' := ⟨hxU, hfx'V'⟩
  have e₁ : g' ⁻¹ᵁ U ⊓ f' ⁻¹ᵁ V' ≤ g' ⁻¹ᵁ U := inf_le_left
  have e₂ : g' ⁻¹ᵁ U ⊓ f' ⁻¹ᵁ V' ≤ f' ⁻¹ᵁ V' := inf_le_right
  -- the ring data of the chart
  have hfpLE := f.finitePresentation_appLE hV hU hUV
  algebraize [(f.appLE V U hUV).hom, (g.appLE V V' hV'V).hom,
    (g'.appLE U (g' ⁻¹ᵁ U ⊓ f' ⁻¹ᵁ V') e₁).hom,
    (f'.appLE V' (g' ⁻¹ᵁ U ⊓ f' ⁻¹ᵁ V') e₂).hom]
  let _ : Algebra Γ(S, V) Γ(X', g' ⁻¹ᵁ U ⊓ f' ⁻¹ᵁ V') :=
    ((f'.appLE V' (g' ⁻¹ᵁ U ⊓ f' ⁻¹ᵁ V') e₂).hom.comp (g.appLE V V' hV'V).hom).toAlgebra
  have htow₁ : IsScalarTower Γ(S, V) Γ(S', V') Γ(X', g' ⁻¹ᵁ U ⊓ f' ⁻¹ᵁ V') :=
    IsScalarTower.of_algebraMap_eq' rfl
  have htow₂ : IsScalarTower Γ(S, V) Γ(X, U) Γ(X', g' ⁻¹ᵁ U ⊓ f' ⁻¹ᵁ V') := by
    refine IsScalarTower.of_algebraMap_eq' ?_
    simp only [RingHom.algebraMap_toAlgebra]
    exact (congrArg CommRingCat.Hom.hom hpo.w).symm
  have halg : Algebra.IsPushout Γ(S, V) Γ(X, U) Γ(S', V')
      Γ(X', g' ⁻¹ᵁ U ⊓ f' ⁻¹ᵁ V') := by
    refine CommRingCat.isPushout_iff_isPushout.mp ?_
    simpa only [RingHom.algebraMap_toAlgebra, CommRingCat.ofHom_hom] using hpo
  -- the primes of the chart, and their correspondence
  have hlies : (hU'.primeIdealOf ⟨x', hxU'⟩).asIdeal.LiesOver
      (hU.primeIdealOf ⟨g' x', hxU⟩).asIdeal :=
    ⟨congr($(IsAffineOpen.comap_primeIdealOf_appLE U hU _ hU' e₁ hxU').1).symm⟩
  -- the flatness hypothesis, read on the chart
  have hflat' : Module.Flat Γ(S, V) Γ(X, U) ∨ Module.Flat Γ(S, V) Γ(S', V') := by
    rcases hflat with h | h
    · exact .inl (RingHom.flat_algebraMap_iff.mp (h.flat_appLE hV hU hUV))
    · exact .inr (RingHom.flat_algebraMap_iff.mp (h.flat_appLE hV hV' hV'V))
  rw [Scheme.Hom.mem_smoothLocus, Scheme.Hom.mem_smoothLocus,
    AlgebraicGeometry.formallySmooth_stalkMap_iff V hV U hU hUV hxU,
    AlgebraicGeometry.formallySmooth_stalkMap_iff V' hV' _ hU' e₂ hxU']
  exact (Algebra.isSmoothAt_iff_isSmoothAt_of_isPushout_of_flat Γ(S, V) Γ(X, U) Γ(S', V')
    Γ(X', g' ⁻¹ᵁ U ⊓ f' ⁻¹ᵁ V') hflat' (hU.primeIdealOf ⟨g' x', hxU⟩).asIdeal
    (hU'.primeIdealOf ⟨x', hxU'⟩).asIdeal).symm

end AlgebraicGeometry

end
