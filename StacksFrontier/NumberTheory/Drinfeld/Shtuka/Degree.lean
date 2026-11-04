/-
Copyright (c) 2026 the Stacks project formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import StacksFrontier.NumberTheory.Drinfeld.Shtuka.BaseChange
public import StacksFrontier.AlgebraicGeometry.Curves.PrescribedLowCohomologyFieldExtension
public import StacksFrontier.AlgebraicGeometry.EulerCharIso.Basic
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.DegreeAdditivityUnconditional

/-!
# Degrees on geometric fibres and Harder–Narasimhan bounds for shtukas

Let `X` be a proper curve over the finite field `k` and `Ω` a field extension of `k`. The product
`X ×_k Spec Ω` is the base change `X_Ω`, a proper scheme of dimension at most one over `Ω`
(`AlgebraicGeometry.topologicalKrullDim_pullback_le_one`), so a finite locally free module of
constant rank on it has a degree, `AlgebraicGeometry.curveDegree`.

The moduli of rank-`2` shtukas is not of finite type; Drinfeld cuts it into open pieces of finite
type by bounding the Harder–Narasimhan polygon of the bundle `E`. For a rank-`2` bundle on a
geometric fibre the polygon is governed by the maximal degree of a rank-one subbundle: the shtuka
is *`μ`-bounded* when every rank-one subbundle `L ⊂ E` with locally free quotient satisfies
`2 deg L - deg E ≤ μ`. A shtuka over an arbitrary base `S` is `μ`-bounded when all its base
changes to geometric points `Spec Ω ⟶ S`, `Ω` algebraically closed, are. These are the open
substacks `Sht^{≤μ}` exhausting the moduli.

## Main definitions

* `Stacks.Drinfeld.Shtuka.geometricPoint` — `Spec Ω` as a scheme over `k`.
* `Stacks.Drinfeld.Shtuka.fibreDegree` — the degree of a vector bundle on `X ×_k Spec Ω`.
* `Stacks.Drinfeld.Shtuka.IsBoundedAtPoint` — the Harder–Narasimhan bound for a rank-`2` shtuka
  over `Spec Ω`.
* `Stacks.Drinfeld.Shtuka.IsHarderNarasimhanBounded` — the Harder–Narasimhan bound for a rank-`2`
  shtuka over a scheme `S`, at all geometric points.

## Main results

* `Stacks.Drinfeld.Shtuka.topologicalKrullDim_product_geometricPoint_le_one` — `dim X_Ω ≤ 1`.
* `Stacks.Drinfeld.Shtuka.fibreDegree_eq_of_iso`, `fibreDegree_add_of_shortExact` — the degree is
  an isomorphism invariant and additive in short exact sequences.
* `Stacks.Drinfeld.Shtuka.isBoundedAtPoint_iff_quotient` — the bound reads
  `deg L - deg (E / L) ≤ μ`.
* `Stacks.Drinfeld.Shtuka.IsBoundedAtPoint.of_iso` — the bound is invariant under isomorphisms
  of shtukas.
* `Stacks.Drinfeld.Shtuka.IsHarderNarasimhanBounded.baseChange` — the bound over `S` is stable
  under base change.

## References

* V. G. Drinfeld, *Cohomology of compactified manifolds of modules of F-sheaves of rank 2*,
  J. Soviet Math. 46 (1989), §2.
* L. Lafforgue, *Chtoucas de Drinfeld et correspondance de Langlands*, Invent. Math. 147 (2002),
  §I.2.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Drinfeld.Shtuka

variable {k : Type u} [Field k] (Ω : Type u) [Field Ω] [Algebra k Ω]

variable (k) in
/-- The spectrum of a field extension `Ω` of `k`, as a scheme over `k`. -/
abbrev geometricPoint : Over (Spec (.of k)) :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k Ω)))

variable (X : Over (Spec (.of k)))

/-- **The base change `X_Ω` of a curve has dimension at most one.** -/
theorem topologicalKrullDim_product_geometricPoint_le_one [IsCurve k X.hom] :
    topologicalKrullDim (product X (geometricPoint k Ω)) ≤ 1 :=
  topologicalKrullDim_pullback_le_one k Ω X.hom

/-- The structure morphism `X_Ω ⟶ Spec Ω`. -/
abbrev fibreStructureMap : product X (geometricPoint k Ω) ⟶ Spec (.of Ω) :=
  pullback.snd X.hom (geometricPoint k Ω).hom

/-- If `X` is proper over `k`, then `X_Ω ⟶ Spec Ω` is proper. -/
instance [IsProper X.hom] : IsProper (fibreStructureMap Ω X) :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsProper)
    (IsPullback.of_hasPullback X.hom (geometricPoint k Ω).hom) ‹_›

variable [IsCurve k X.hom] [IsProper X.hom]

/-- **The degree of a vector bundle on the geometric fibre** `X_Ω`: the degree
`χ(E) - rank · χ(𝒪)` over `Ω`. -/
def fibreDegree (E : (product X (geometricPoint k Ω)).Modules) (r : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r] : ℤ :=
  curveDegree Ω (fibreStructureMap Ω X) (topologicalKrullDim_product_geometricPoint_le_one Ω X)
    E r

variable {Ω X}

/-- The degree on the geometric fibre is an isomorphism invariant. -/
theorem fibreDegree_eq_of_iso {E E' : (product X (geometricPoint k Ω)).Modules} (r : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r]
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E' r] (e : E ≅ E') :
    fibreDegree Ω X E r = fibreDegree Ω X E' r :=
  curveDegree_eq_of_iso _ _ _ r e

/-- **The degree on the geometric fibre is additive** in short exact sequences of vector
bundles. -/
theorem fibreDegree_add_of_shortExact (S : ShortComplex (product X (geometricPoint k Ω)).Modules)
    (hS : S.ShortExact) (r₁ r₂ r₃ : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} S.X₁ r₁]
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} S.X₂ r₂]
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} S.X₃ r₃] :
    fibreDegree Ω X S.X₂ r₂ = fibreDegree Ω X S.X₁ r₁ + fibreDegree Ω X S.X₃ r₃ :=
  curveDegree_add_of_shortExact_of_isProper Ω _ _ S hS r₁ r₂ r₃

/-- The short exact sequence `0 ⟶ L ⟶ E ⟶ E / L ⟶ 0` of a monomorphism. -/
theorem shortExact_cokernel {Y : Scheme.{u}} {L E : Y.Modules} (ι : L ⟶ E) [Mono ι] :
    (ShortComplex.mk ι (cokernel.π ι) (cokernel.condition ι)).ShortExact where
  exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel ι)

variable {p f : ℕ} [Fact p.Prime] [Fintype k] [CharP k p] {hcard : Fintype.card k = p ^ f}

/-- **The Harder–Narasimhan bound at a geometric point.** A rank-`2` shtuka over `Spec Ω` is
`μ`-bounded when every rank-one subbundle `L ⊂ E` with locally free quotient `E / L` of rank
one satisfies `2 deg L - deg E ≤ μ`. -/
def IsBoundedAtPoint (μ : ℤ) (𝓔 : Shtuka p f hcard X (geometricPoint k Ω) 2) : Prop :=
  haveI := 𝓔.isFiniteLocallyFreeOfRank_E
  ∀ (L : (product X (geometricPoint k Ω)).Modules) (ι : L ⟶ 𝓔.E) [Mono ι]
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} L 1]
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (cokernel ι : (product X (geometricPoint k Ω)).Modules) 1],
    2 * fibreDegree Ω X L 1 - fibreDegree Ω X 𝓔.E 2 ≤ μ

/-- **The Harder–Narasimhan bound reads `deg L - deg (E / L) ≤ μ`**, by additivity of the
degree along `0 ⟶ L ⟶ E ⟶ E / L ⟶ 0`. -/
theorem isBoundedAtPoint_iff_quotient (μ : ℤ) (𝓔 : Shtuka p f hcard X (geometricPoint k Ω) 2) :
    IsBoundedAtPoint μ 𝓔 ↔
      ∀ (L : (product X (geometricPoint k Ω)).Modules) (ι : L ⟶ 𝓔.E) [Mono ι]
        [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} L 1]
        [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (cokernel ι : (product X (geometricPoint k Ω)).Modules) 1],
        fibreDegree Ω X L 1 - fibreDegree Ω X (cokernel ι) 1 ≤ μ := by
  have := 𝓔.isFiniteLocallyFreeOfRank_E
  constructor <;> intro hb L ι _ _ _ <;>
  · have h := fibreDegree_add_of_shortExact _ (shortExact_cokernel ι) 1 2 1
    dsimp only at h
    linarith [hb L ι]

/-- **The Harder–Narasimhan bound is invariant under isomorphisms of shtukas.** -/
theorem IsBoundedAtPoint.of_iso {μ : ℤ} {𝓔 𝓕 : Shtuka p f hcard X (geometricPoint k Ω) 2}
    (e : 𝓔 ≅ 𝓕) (h : IsBoundedAtPoint μ 𝓔) : IsBoundedAtPoint μ 𝓕 := by
  have := 𝓔.isFiniteLocallyFreeOfRank_E
  have := 𝓕.isFiniteLocallyFreeOfRank_E
  intro L ι _ _ _
  let eE : 𝓔.E ≅ 𝓕.E := (forget p f hcard X _ 2).mapIso e
  have : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (cokernel (ι ≫ eE.inv) : (product X (geometricPoint k Ω)).Modules) 1 :=
    SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso (cokernelCompIsIso ι eE.inv).symm ‹_›
  have := h L (ι ≫ eE.inv)
  rwa [fibreDegree_eq_of_iso 2 eE] at this

variable [IsSeparated X.hom]

/-- **The Harder–Narasimhan bound** for a rank-`2` shtuka over a scheme `S` over `k`: its base
change to every geometric point `Spec Ω ⟶ S` (`Ω` algebraically closed) is `μ`-bounded. These
conditions cut out the open substacks `Sht^{≤μ}` of finite type exhausting the moduli. -/
def IsHarderNarasimhanBounded (μ : ℤ) {S : Over (Spec (.of k))} (𝓔 : Shtuka p f hcard X S 2) :
    Prop :=
  ∀ (Ω : Type u) [Field Ω] [Algebra k Ω] [IsAlgClosed Ω] (x : geometricPoint k Ω ⟶ S),
    IsBoundedAtPoint μ (𝓔.baseChange x)

/-- **The Harder–Narasimhan bound is stable under base change**: a geometric point of `S'` is,
through `g : S' ⟶ S`, a geometric point of `S`, and the two base changes are isomorphic
(`Stacks.Drinfeld.Shtuka.baseChangeCompIso`). -/
theorem IsHarderNarasimhanBounded.baseChange {μ : ℤ} {S S' : Over (Spec (.of k))}
    {𝓔 : Shtuka p f hcard X S 2} (h : IsHarderNarasimhanBounded μ 𝓔) (g : S' ⟶ S) :
    IsHarderNarasimhanBounded μ (𝓔.baseChange g) := fun Ω _ _ _ x =>
  (h Ω (x ≫ g)).of_iso (baseChangeCompIso x g 𝓔)

end Stacks.Drinfeld.Shtuka
