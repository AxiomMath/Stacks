module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Different.TheDifferent.EffectiveCartier
public import StacksFrontier.AlgebraicGeometry.Discriminant.DualizingModuleInvertibility
public import StacksFrontier.AlgebraicGeometry.Discriminant.DualizingModuleQuasiFiniteSyntomic
public import StacksFrontier.AlgebraicGeometry.Duality.GorensteinMorphisms.Fibres
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizingModuleExistence0BVG
public import StacksFrontier.AlgebraicGeometry.Duality.GorensteinSchemes.StructureSheafDualizing
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Fibre
public import StacksFrontier.RingTheory.Dualizing.GorensteinLocalization

/-!
# The relative dualizing module of a quasi-finite Gorenstein morphism is invertible

Let `f : Y ⟶ X` be a quasi-finite Gorenstein morphism of Noetherian schemes.  This file derives
invertibility of the relative dualizing module `ω_{Y/X}` from the Gorenstein hypothesis, which
is the implication (2) ⟹ (3) of [Stacks, Tag 0C16], and from it every part of
[Stacks, Tag 0C17]: the different `𝔇_f` and the closed subscheme `R ⊆ Y` it cuts out are locally
principal, `𝔇_f` is the Noether different on affine charts, `R` commutes with base change, the
norm of `R` is the discriminant when `f` is finite, and `R` is an effective Cartier divisor with
`𝒪_Y(R) ≅ ω_{Y/X}` when `f` is étale at the associated points of `Y`.

## Main results

* `Stacks.Discriminant.dualizingModule_invertible_of_isGorensteinRing`: the relative dualizing
  module of a finite Gorenstein algebra over a field is invertible.
* `Stacks.Discriminant.dualizingModule_invertible_of_isGorensteinRing_fibers`: the relative
  dualizing module of a quasi-finite flat algebra all of whose residue-field fibres are
  Gorenstein is invertible.
* `Stacks.Discriminant.isInvertible_of_isGorenstein`: **[Stacks, Tag 0C16], (1) ⟹ (3)**, that
  `ω_{Y/X}` is an invertible `𝒪_Y`-module for a quasi-finite Gorenstein morphism.
* `Stacks.Discriminant.isGorensteinRing_fibers_of_dualizingModule_invertible` and
  `Stacks.Discriminant.isGorenstein_fiber_of_isInvertible`: the converse, (3) ⟹ (2) of
  [Stacks, Tag 0C16], that a flat quasi-finite morphism with invertible `ω_{Y/X}` has Gorenstein
  fibres.
* `Stacks.Discriminant.isGorenstein_tfae`: **[Stacks, Tag 0C16]**, the equivalence of the four
  conditions, with `ω_{Y/X}` the canonical `Stacks.Discriminant.relativeDualizingModuleData f`.
* `Stacks.Discriminant.exists_affineOpens_different_isPrincipal_of_isGorenstein`,
  `Stacks.Discriminant.isLocallyPrincipal_differentIdealSheaf_of_isGorenstein`,
  `Stacks.Discriminant.different_sections_eq_noetherDifferent_of_isGorenstein`,
  `Stacks.Discriminant.isIso_different_baseChange_of_isGorenstein`,
  `Stacks.Discriminant.discriminantIdeal_eq_normIdealSheaf_differentIdealSheaf_of_isGorenstein`
  and `Stacks.Discriminant.isEffectiveCartierDivisor_and_invertibleSheafIso_of_isGorenstein`:
  parts (1) to (6) of [Stacks, Tag 0C17] for a quasi-finite Gorenstein morphism, flatness and
  invertibility of `ω_{Y/X}` being consequences of Gorensteinness.

## Implementation notes

The chain is the source's second proof of [Stacks, Tag 0C16].  Invertibility of `ω_{Y/X}` is
chartwise (`Stacks.Discriminant.isInvertible_iff_exists_chart_dualizingModule_invertible`), and
on a chart it is a fibrewise condition ([Stacks, Tag 0DWK]), so what is needed is that the
relative dualizing module `ω_{(κ(p) ⊗_A B)/κ(p)}` of a fibre is invertible.  A fibre of a
quasi-finite algebra over a field is finite, its dualizing module is the linear dual
`Hom_{κ(p)}(κ(p) ⊗_A B, κ(p))`, and for a Gorenstein ring that dual is invertible
(`Stacks.Discriminant.invertible_dual_of_isGorensteinRing`, which is [Stacks, Tag 0DW9] read
through `Dualizing.isGorensteinRing_iff_isInvertible_canonical`).  A fibre that is the zero ring
has no primes, so Gorensteinness is vacuous there and invertibility is the degenerate
`Stacks.Discriminant.module_invertible_of_subsingleton`.

The Gorenstein hypothesis is consumed through
`Stacks.Discriminant.algEquivFiberSections`, which identifies the fibre ring `κ(p) ⊗_A B` of a
chart with the sections of the scheme-theoretic fibre `Y_x` over its affine open
`f.fiberι x ⁻¹ᵁ V`; Gorensteinness of the scheme `Y_x` then gives Gorensteinness of that ring by
`Stacks.Duality.isGorensteinRing_sections`.  Flatness of `f` is derived from the Gorenstein
hypothesis by [Stacks, Tag 0C05].

The converse runs the same chain backwards: invertibility of `ω_{B/A}` passes to the fibres by
[Stacks, Tag 0DWK], and a finite algebra over a field with invertible dual is Gorenstein
(`Stacks.Discriminant.isGorensteinRing_of_invertible_dual`, [Stacks, Tag 0DW9 (1)(a)] read
backwards); the local rings of the scheme-theoretic fibre are localizations of the fibre rings of
the charts.  Flatness in (4) globalizes because flatness is local on the source and the target.

## References

* [Stacks Project, Tag 0C17](https://stacks.math.columbia.edu/tag/0C17)
* [Stacks Project, Tag 0C16](https://stacks.math.columbia.edu/tag/0C16)
* [Stacks Project, Tag 0C05](https://stacks.math.columbia.edu/tag/0C05)
* [Stacks Project, Tag 0DWK](https://stacks.math.columbia.edu/tag/0DWK)
* [Stacks Project, Tag 0DW9](https://stacks.math.columbia.edu/tag/0DW9)
* [Stacks Project, Tag 0BWA](https://stacks.math.columbia.edu/tag/0BWA)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open RingedSpaceModuleAdjunction
open scoped AlgebraicGeometry TensorProduct

universe u v w

namespace Stacks.Discriminant

attribute [local instance] algebraDualModule

/-! ### The dualizing module of a Gorenstein algebra over a field -/

/-- **The relative dualizing module of a finite Gorenstein algebra over a field is
invertible.**  For a field `k` and a finite Gorenstein `k`-algebra `B`, the relative dualizing
module `ω_{B/k}` computed from any finite-open factorization of `k → B` is an invertible
`B`-module.

The dualizing module of the trivial factorization is the linear dual `Hom_k(B, k)`, and for a
Gorenstein ring that dual is invertible. -/
theorem dualizingModule_invertible_of_isGorensteinRing {k : Type u} {B : Type v}
    [Field k] [CommRing B] [Algebra k B] [Module.Finite k B] [IsNoetherianRing B]
    (F : FiniteOpenFactorization.{u, v, w} k B) (hG : Dualizing.IsGorensteinRing B) :
    Module.Invertible B (dualizingModule F) := by
  rcases subsingleton_or_nontrivial B with _ | _
  · exact module_invertible_of_subsingleton _ _
  · let : Module.Invertible B (Module.Dual k B) := invertible_dual_of_isGorensteinRing hG
    exact Module.Invertible.congr
      ((dualizingModuleEquiv F (selfFactorization k B)).trans selfFactorizationDualEquiv).symm

/-- **A quasi-finite flat algebra with Gorenstein fibres has invertible relative dualizing
module.**  Let `A → B` be a quasi-finite flat homomorphism of Noetherian rings of finite type.
If the fibre `κ(p) ⊗_A B` is a Gorenstein ring for every prime `p` of `A`, then the relative
dualizing module `ω_{B/A}` is an invertible `B`-module.

Invertibility of `ω_{B/A}` is the fibrewise condition of [Stacks, Tag 0DWK], and a fibre of a
quasi-finite algebra over a field is finite. -/
theorem dualizingModule_invertible_of_isGorensteinRing_fibers {A : Type u} {B : Type v}
    [CommRing A] [CommRing B] [Algebra A B] [IsNoetherianRing A] [IsNoetherianRing B]
    [Algebra.FiniteType A B] [Algebra.QuasiFinite A B] [Module.Flat A B]
    (F : FiniteOpenFactorization.{u, v, w} A B)
    (hG : ∀ p : PrimeSpectrum A, Dualizing.IsGorensteinRing (p.asIdeal.Fiber B)) :
    Module.Invertible B (dualizingModule F) :=
  (dualizingModule_invertible_iff_fibers F).mpr fun p G =>
    dualizingModule_invertible_of_isGorensteinRing G (hG p)

/-- **A quasi-finite flat algebra with invertible relative dualizing module has Gorenstein
fibres.**  Let `A → B` be a quasi-finite flat homomorphism of Noetherian rings of finite type.
If the relative dualizing module `ω_{B/A}` is an invertible `B`-module, then the fibre
`κ(p) ⊗_A B` is a Gorenstein ring for every prime `p` of `A`.

Invertibility passes to the fibres by [Stacks, Tag 0DWK]; the fibre is finite over `κ(p)`, its
dualizing module is the linear dual `Hom_{κ(p)}(κ(p) ⊗_A B, κ(p))`, and a finite algebra over a
field with invertible dual is Gorenstein. -/
theorem isGorensteinRing_fibers_of_dualizingModule_invertible {A : Type u} {B : Type v}
    [CommRing A] [CommRing B] [Algebra A B] [IsNoetherianRing A] [IsNoetherianRing B]
    [Algebra.FiniteType A B] [Algebra.QuasiFinite A B] [Module.Flat A B]
    (F : FiniteOpenFactorization.{u, v, v} A B) [Module.Invertible B (dualizingModule F)]
    (p : PrimeSpectrum A) : Dualizing.IsGorensteinRing (p.asIdeal.Fiber B) := by
  let : Algebra p.asIdeal.ResidueField (p.asIdeal.Fiber B) := Algebra.TensorProduct.leftAlgebra
  rcases subsingleton_or_nontrivial (p.asIdeal.Fiber B) with _ | _
  · intro q hq
    exact (hq.ne_top (Subsingleton.elim q ⊤)).elim
  · have := (dualizingModule_invertible_iff_fibers F).mp inferInstance p
      (selfFactorization p.asIdeal.ResidueField (p.asIdeal.Fiber B))
    have : Module.Invertible (p.asIdeal.Fiber B)
        (Module.Dual p.asIdeal.ResidueField (p.asIdeal.Fiber B)) :=
      Module.Invertible.congr selfFactorizationDualEquiv
    exact isGorensteinRing_of_invertible_dual (k := p.asIdeal.ResidueField)

/-! ### Invertibility of `ω_{Y/X}` for a Gorenstein morphism -/

/-- The Noetherian, finite type and quasi-finite hypotheses on the ring map of a chart of `f`. -/
private theorem chart_algebra_props {X Y : Scheme.{u}} (f : Y ⟶ X)
    [IsNoetherian X] [IsNoetherian Y] [LocallyOfFiniteType f] [LocallyQuasiFinite f]
    (U : X.affineOpens) (V : Y.affineOpens)
    (hVU : V.1 ≤ f ⁻¹ᵁ U.1) :
    letI : Algebra Γ(X, U.1) Γ(Y, V.1) := (f.appLE U.1 V.1 hVU).hom.toAlgebra
    IsNoetherianRing Γ(X, U.1) ∧ IsNoetherianRing Γ(Y, V.1) ∧
      Algebra.FiniteType Γ(X, U.1) Γ(Y, V.1) ∧ Algebra.QuasiFinite Γ(X, U.1) Γ(Y, V.1) :=
  ⟨IsLocallyNoetherian.component_noetherian U, IsLocallyNoetherian.component_noetherian V,
    f.finiteType_appLE U.2 V.2 hVU, LocallyQuasiFinite.quasiFinite_appLE U.2 V.2 hVU⟩

section Schemes

variable {X Y : Scheme.{u}} (f : Y ⟶ X)
  [IsNoetherian X] [IsNoetherian Y]
  [LocallyOfFiniteType f] [QuasiCompact f] [LocallyQuasiFinite f]

/-- The fibre ring of a chart of `f` over a prime of the base is Gorenstein as soon as the
scheme-theoretic fibre of `f` through that prime is a Gorenstein scheme. -/
theorem isGorensteinRing_fiber_chart [Flat f]
    (hG : ∀ x : X, AlgebraicGeometry.IsGorenstein (f.fiber x))
    (U : X.affineOpens) (V : Y.affineOpens) (hVU : V.1 ≤ f ⁻¹ᵁ U.1)
    (p : PrimeSpectrum Γ(X, U.1)) :
    letI : Algebra Γ(X, U.1) Γ(Y, V.1) := (f.appLE U.1 V.1 hVU).hom.toAlgebra
    letI : IsNoetherianRing (p.asIdeal.Fiber Γ(Y, V.1)) := by
      let : IsNoetherianRing Γ(X, U.1) := IsLocallyNoetherian.component_noetherian U
      let : IsNoetherianRing Γ(Y, V.1) := IsLocallyNoetherian.component_noetherian V
      let : Algebra.FiniteType Γ(X, U.1) Γ(Y, V.1) := f.finiteType_appLE U.2 V.2 hVU
      let : Algebra.QuasiFinite Γ(X, U.1) Γ(Y, V.1) :=
        LocallyQuasiFinite.quasiFinite_appLE U.2 V.2 hVU
      infer_instance
    Dualizing.IsGorensteinRing (p.asIdeal.Fiber Γ(Y, V.1)) := by
  let : Algebra Γ(X, U.1) Γ(Y, V.1) := (f.appLE U.1 V.1 hVU).hom.toAlgebra
  obtain ⟨_, _, _, _⟩ := chart_algebra_props f U V hVU
  let : Algebra Γ(Y, V.1) (p.asIdeal.Fiber Γ(Y, V.1)) := Algebra.TensorProduct.rightAlgebra
  let x := U.2.fromSpec p
  let W : (f.fiber x).affineOpens :=
    ⟨f.fiberι x ⁻¹ᵁ V.1, isAffineOpen_fiber_preimage f U V hVU x (U.2.range_fromSpec.le ⟨p, rfl⟩)⟩
  let : AlgebraicGeometry.IsGorenstein (f.fiber x) := hG x
  let : IsNoetherianRing Γ(f.fiber x, W.1) := IsLocallyNoetherian.component_noetherian W
  let : Algebra Γ(Y, V.1) Γ(f.fiber x, W.1) :=
    ((f.fiberι x).appLE V.1 (f.fiberι x ⁻¹ᵁ V.1) le_rfl).hom.toAlgebra
  exact Dualizing.isGorensteinRing_of_ringEquiv
    (algEquivFiberSections f U V hVU p).symm.toRingEquiv
    (Stacks.Duality.isGorensteinRing_sections W.1 W.2)

/-- **[Stacks, Tag 0C16], (2) implies (3).** For a quasi-finite flat morphism of Noetherian
schemes whose fibres are Gorenstein schemes, the relative dualizing module `ω_{Y/X}` is an
invertible `𝒪_Y`-module.

Invertibility is the chartwise condition (4) of the same tag, and on a chart it is the fibrewise
condition of [Stacks, Tag 0DWK]; the fibre ring of a chart is the ring of sections of the
scheme-theoretic fibre over an affine open, hence Gorenstein. -/
@[stacks 0C16 "(2) implies (3)"]
theorem isInvertible_of_isGorenstein_fiber [Flat f] (ω : RelativeDualizingModuleData f)
    (hG : ∀ x : X, AlgebraicGeometry.IsGorenstein (f.fiber x)) :
    Stacks.SheafOfModules.IsInvertible Y.presheaf
      (structureSheafRing Y.toRingedSpace).property ω.sheaf := by
  refine (isInvertible_iff_exists_chart_dualizingModule_invertible ω).mpr fun y => ?_
  obtain ⟨U, V, hVU, hyV⟩ := exists_chart (f := f) y
  refine ⟨U, V, hVU, hyV, fun F => ?_⟩
  let : Algebra Γ(X, U.1) Γ(Y, V.1) := (f.appLE U.1 V.1 hVU).hom.toAlgebra
  obtain ⟨_, _, _, _⟩ := chart_algebra_props f U V hVU
  let : Module.Flat Γ(X, U.1) Γ(Y, V.1) := f.flat_appLE U.2 V.2 hVU
  exact dualizingModule_invertible_of_isGorensteinRing_fibers F
    (isGorensteinRing_fiber_chart f hG U V hVU)

/-- **[Stacks, Tag 0C16], (1) implies (3).** The relative dualizing module of a quasi-finite
Gorenstein morphism of Noetherian schemes is an invertible `𝒪_Y`-module.

Gorensteinness of the morphism is flatness together with Gorensteinness of the fibres, by
[Stacks, Tag 0C05]. -/
@[stacks 0C16 "(1) implies (3)"]
theorem isInvertible_of_isGorenstein (hF : ∀ x : X, IsLocallyNoetherian (f.fiber x))
    (hGor : Scheme.Hom.IsGorenstein f hF) (ω : RelativeDualizingModuleData f) :
    letI : Flat f := ((Scheme.Hom.isGorenstein_iff_flat_and_isGorenstein_fiber f hF).mp hGor).1
    Stacks.SheafOfModules.IsInvertible Y.presheaf
      (structureSheafRing Y.toRingedSpace).property ω.sheaf := by
  obtain ⟨hflat, hfib⟩ := (Scheme.Hom.isGorenstein_iff_flat_and_isGorenstein_fiber f hF).mp hGor
  let : Flat f := hflat
  exact isInvertible_of_isGorenstein_fiber f ω hfib

/-- A quasi-finite Gorenstein morphism is flat, and its relative dualizing module is invertible. -/
private theorem flat_and_isInvertible_of_isGorenstein
    (hGor : Scheme.Hom.IsGorenstein f (isLocallyNoetherian_fiber_of_locallyOfFiniteType f))
    (ω : RelativeDualizingModuleData f) :
    Flat f ∧ Stacks.SheafOfModules.IsInvertible Y.presheaf
      (structureSheafRing Y.toRingedSpace).property ω.sheaf :=
  ⟨((Scheme.Hom.isGorenstein_iff_flat_and_isGorenstein_fiber f _).mp hGor).1,
    isInvertible_of_isGorenstein f _ hGor ω⟩

/-- **[Stacks, Tag 0C16], (3) implies (2).** The fibres of a flat quasi-finite morphism of
Noetherian schemes with invertible relative dualizing module `ω_{Y/X}` are Gorenstein schemes.

Invertibility of `ω_{Y/X}` is invertibility of `ω_{B/A}` on every affine chart, which makes the
fibre rings `κ(p) ⊗_A B` Gorenstein; these are the rings of sections of the scheme-theoretic
fibres over an affine open cover, and the local rings of the fibres are their localizations. -/
theorem isGorenstein_fiber_of_isInvertible [Flat f] (ω : RelativeDualizingModuleData f)
    [Stacks.SheafOfModules.IsInvertible Y.presheaf
      (structureSheafRing Y.toRingedSpace).property ω.sheaf]
    (x : X) : AlgebraicGeometry.IsGorenstein (f.fiber x) := by
  refine (AlgebraicGeometry.isGorenstein_iff _).mpr
    ⟨isLocallyNoetherian_fiber_of_locallyOfFiniteType f x, fun z => ?_⟩
  have hz : f (f.fiberι x z) = x := (f.fiberHomeo x z).property
  obtain ⟨U, V, hVU, hyV⟩ := exists_chart (f := f) (f.fiberι x z)
  have hxU : x ∈ U.1 := by
    have h : f (f.fiberι x z) ∈ U.1 := hVU hyV
    rwa [hz] at h
  obtain ⟨p, rfl⟩ : ∃ p : PrimeSpectrum Γ(X, U.1), U.2.fromSpec p = x :=
    ⟨_, U.2.fromSpec_primeIdealOf ⟨x, hxU⟩⟩
  let : Algebra Γ(X, U.1) Γ(Y, V.1) := (f.appLE U.1 V.1 hVU).hom.toAlgebra
  obtain ⟨_, _, _, _⟩ := chart_algebra_props f U V hVU
  let : Module.Flat Γ(X, U.1) Γ(Y, V.1) := f.flat_appLE U.2 V.2 hVU
  let : Algebra Γ(Y, V.1) (p.asIdeal.Fiber Γ(Y, V.1)) := Algebra.TensorProduct.rightAlgebra
  obtain ⟨F⟩ := nonempty_relativeDualizingChartFactorization f U V hVU
  let := module_invertible_dualizingModule ω U V hVU F
  have hfib := isGorensteinRing_fibers_of_dualizingModule_invertible F p
  let W : (f.fiber (U.2.fromSpec p)).affineOpens :=
    ⟨f.fiberι (U.2.fromSpec p) ⁻¹ᵁ V.1,
      isAffineOpen_fiber_preimage f U V hVU _ (U.2.range_fromSpec.le ⟨p, rfl⟩)⟩
  let : IsLocallyNoetherian (f.fiber (U.2.fromSpec p)) :=
    isLocallyNoetherian_fiber_of_locallyOfFiniteType f _
  let : IsNoetherianRing Γ(f.fiber (U.2.fromSpec p), W.1) :=
    IsLocallyNoetherian.component_noetherian W
  let : Algebra Γ(Y, V.1) Γ(f.fiber (U.2.fromSpec p), W.1) :=
    ((f.fiberι (U.2.fromSpec p)).appLE V.1 W.1 le_rfl).hom.toAlgebra
  have hW : Dualizing.IsGorensteinRing Γ(f.fiber (U.2.fromSpec p), W.1) :=
    Dualizing.isGorensteinRing_of_ringEquiv (algEquivFiberSections f U V hVU p).toRingEquiv hfib
  let z' : W.1 := ⟨z, hyV⟩
  let q := (W.2.primeIdealOf z').asIdeal
  let : Algebra Γ(f.fiber (U.2.fromSpec p), W.1) ((f.fiber (U.2.fromSpec p)).presheaf.stalk z) :=
    (f.fiber (U.2.fromSpec p)).presheaf.algebra_section_stalk z'
  let : IsLocalization.AtPrime ((f.fiber (U.2.fromSpec p)).presheaf.stalk z) q :=
    W.2.isLocalization_stalk z'
  exact (Stacks.Duality.isGorensteinLocalRing_ringEquiv_iff
    (IsLocalization.algEquiv q.primeCompl ((f.fiber (U.2.fromSpec p)).presheaf.stalk z)
      (Localization.AtPrime q)).toRingEquiv).mpr (hW q)

/-- **[Stacks, Tag 0C16].** For a quasi-finite morphism `f : Y ⟶ X` of Noetherian schemes the
following are equivalent:
1. `f` is Gorenstein;
2. `f` is flat and its fibres are Gorenstein;
3. `f` is flat and the relative dualizing module `ω_{Y/X}` of [Stacks, Tag 0BVG] is an
   invertible `𝒪_Y`-module;
4. every point of `Y` has an affine open neighbourhood `V = Spec B` lying over an affine open
   `U = Spec A` of `X` such that `A → B` is flat and `ω_{B/A}` is an invertible `B`-module.

The module `ω_{Y/X}` is the canonical one, `Stacks.Discriminant.relativeDualizingModuleData f`;
the algebraic relative dualizing module `ω_{B/A}` is computed from a finite-open factorization of
`A → B`, and every such factorization gives an invertible module. -/
@[stacks 0C16]
theorem isGorenstein_tfae :
    List.TFAE [
      Scheme.Hom.IsGorenstein f (isLocallyNoetherian_fiber_of_locallyOfFiniteType f),
      Flat f ∧ ∀ x : X, AlgebraicGeometry.IsGorenstein (f.fiber x),
      Flat f ∧ Stacks.SheafOfModules.IsInvertible Y.presheaf
        (structureSheafRing Y.toRingedSpace).property (relativeDualizingModuleData f).sheaf,
      ∀ y : Y, ∃ (U : X.affineOpens) (V : Y.affineOpens) (hVU : V.1 ≤ f ⁻¹ᵁ U.1), y ∈ V.1 ∧
        letI : Algebra Γ(X, U.1) Γ(Y, V.1) := (f.appLE U V hVU).hom.toAlgebra
        Module.Flat Γ(X, U.1) Γ(Y, V.1) ∧
          ∀ F : FiniteOpenFactorization.{u, u, u} Γ(X, U.1) Γ(Y, V.1),
            Module.Invertible Γ(Y, V.1) (dualizingModule F)] := by
  tfae_have 1 ↔ 2 := Scheme.Hom.isGorenstein_iff_flat_and_isGorenstein_fiber f _
  tfae_have 2 → 3 := fun ⟨hfl, hG⟩ =>
    ⟨hfl, let := hfl; isInvertible_of_isGorenstein_fiber f _ hG⟩
  tfae_have 3 → 2 := fun ⟨hfl, hinv⟩ =>
    ⟨hfl, let := hfl; let := hinv
      isGorenstein_fiber_of_isInvertible f (relativeDualizingModuleData f)⟩
  tfae_have 3 → 4 := by
    rintro ⟨hfl, hinv⟩ y
    obtain ⟨U, V, hVU, hyV, hF⟩ :=
      (isInvertible_iff_exists_chart_dualizingModule_invertible
        (relativeDualizingModuleData f)).mp hinv y
    exact ⟨U, V, hVU, hyV, f.flat_appLE U.2 V.2 hVU, hF⟩
  tfae_have 4 → 3 := by
    intro h
    refine ⟨(HasRingHomProperty.iff_exists_appLE (P := @Flat)
      (RingHom.Flat.stableUnderComposition.stableUnderCompositionWithLocalizationAway
        RingHom.Flat.holdsForLocalizationAway).left).mpr fun y => ?_, ?_⟩
    · obtain ⟨U, V, hVU, hyV, hfl, -⟩ := h y
      exact ⟨U, V, hyV, hVU, hfl⟩
    · exact (isInvertible_iff_exists_chart_dualizingModule_invertible
        (relativeDualizingModuleData f)).mpr fun y => by
          obtain ⟨U, V, hVU, hyV, -, hF⟩ := h y
          exact ⟨U, V, hVU, hyV, hF⟩
  tfae_finish

end Schemes

/-! ### Tag 0C17 for a quasi-finite Gorenstein morphism -/

section Different

variable {X Y : Scheme.{u}} (f : Y ⟶ X)
  [IsNoetherian X] [IsNoetherian Y]
  [LocallyOfFiniteType f] [QuasiCompact f] [LocallyQuasiFinite f]
  (hGor : Scheme.Hom.IsGorenstein f (isLocallyNoetherian_fiber_of_locallyOfFiniteType f))

/-- **[Stacks, Tag 0C17 (1)].** The different of a quasi-finite Gorenstein morphism of Noetherian
schemes is a locally principal ideal: every point of `Y` has an affine open neighbourhood
`V = Spec B` on which the ideal of sections of `𝔇_f` is generated by a single element of `B`. -/
@[stacks 0C17 "(1)"]
theorem exists_affineOpens_different_isPrincipal_of_isGorenstein
    (ω : RelativeDualizingModuleData f) :
    letI : Flat f := ((Scheme.Hom.isGorenstein_iff_flat_and_isGorenstein_fiber f _).mp hGor).1
    ∀ (τ : RelativeTraceSection ω) (y : Y),
      ∃ V : Y.affineOpens, y ∈ (V : Set Y) ∧
        (show Ideal Γ(Y, V.1) from (different ω τ).toSubmodule.obj (op V.1)).IsPrincipal := by
  obtain ⟨_, _⟩ := flat_and_isInvertible_of_isGorenstein f hGor ω
  exact fun τ y => exists_affineOpens_different_isPrincipal ω τ y

/-- **[Stacks, Tag 0C17 (2)].** The closed subscheme `R ⊆ Y` cut out by the different of a
quasi-finite Gorenstein morphism of Noetherian schemes is a locally principal closed
subscheme. -/
@[stacks 0C17 "(2)"]
theorem isLocallyPrincipal_differentIdealSheaf_of_isGorenstein
    (ω : RelativeDualizingModuleData f) :
    letI : Flat f := ((Scheme.Hom.isGorenstein_iff_flat_and_isGorenstein_fiber f _).mp hGor).1
    ∀ τ : RelativeTraceSection ω,
      Stacks.Divisors.IsLocallyPrincipal (differentIdealSheaf ω τ) := by
  obtain ⟨_, _⟩ := flat_and_isInvertible_of_isGorenstein f hGor ω
  exact fun τ => isLocallyPrincipal_differentIdealSheaf ω τ

/-- **[Stacks, Tag 0C17 (3)].** On affine opens `V = Spec B ⊆ Y` and `U = Spec A ⊆ X` with
`f(V) ⊆ U`, the different of a quasi-finite Gorenstein morphism of Noetherian schemes is the
Noether different of `B` over `A`. -/
@[stacks 0C17 "(3)"]
theorem different_sections_eq_noetherDifferent_of_isGorenstein
    (ω : RelativeDualizingModuleData f) (U : X.affineOpens) (V : Y.affineOpens)
    (hVU : V.1 ≤ f ⁻¹ᵁ U.1) :
    letI : Flat f := ((Scheme.Hom.isGorenstein_iff_flat_and_isGorenstein_fiber f _).mp hGor).1
    letI : Algebra Γ(X, U.1) Γ(Y, V.1) := (f.appLE U V hVU).hom.toAlgebra
    letI : IsNoetherianRing Γ(X, U.1) := IsLocallyNoetherian.component_noetherian U
    letI : IsNoetherianRing Γ(Y, V.1) := IsLocallyNoetherian.component_noetherian V
    letI : Module.Flat Γ(X, U.1) Γ(Y, V.1) :=
      RingHom.flat_algebraMap_iff.mp (f.flat_appLE U.2 V.2 hVU)
    letI : Algebra.QuasiFinite Γ(X, U.1) Γ(Y, V.1) :=
      RingHom.quasiFinite_algebraMap.mp (LocallyQuasiFinite.quasiFinite_appLE U.2 V.2 hVU)
    ∀ τ : RelativeTraceSection ω,
      (show Ideal Γ(Y, V.1) from (different ω τ).toSubmodule.obj (op V.1)) =
        noetherDifferent Γ(X, U.1) Γ(Y, V.1) := by
  obtain ⟨_, _⟩ := flat_and_isInvertible_of_isGorenstein f hGor ω
  exact fun τ => different_sections_eq_noetherDifferent_of_isInvertible ω τ U V hVU

/-- **[Stacks, Tag 0C17 (6)].** If a quasi-finite Gorenstein morphism of Noetherian schemes is
étale at the associated points of `Y`, then the closed subscheme `R ⊆ Y` cut out by the different
is an effective Cartier divisor, and there is exactly one isomorphism `𝒪_Y(R) ≅ ω_{Y/X}` carrying
the canonical section `1_R` to the trace element `τ_{Y/X}`.

Gorensteinness makes `f` flat and `ω_{Y/X}` invertible, which is the situation of
[Stacks, Tag 0BWA (3)]. -/
@[stacks 0C17 "(6)"]
theorem isEffectiveCartierDivisor_and_invertibleSheafIso_of_isGorenstein
    (ω : RelativeDualizingModuleData f)
    (hét : ∀ y ∈ Stacks.Divisors.schemeAssociatedPoints Y, EtaleAt f y) :
    letI : Flat f := ((Scheme.Hom.isGorenstein_iff_flat_and_isGorenstein_fiber f _).mp hGor).1
    ∀ τ : RelativeTraceSection ω,
      Stacks.Divisors.IsEffectiveCartierDivisor (differentIdealSheaf ω τ) ∧
        ∃! e : Stacks.Divisors.invertibleSheaf' (differentIdealSheaf ω τ) ≅ ω.sheaf,
          Scheme.Modules.Hom.app e.hom ⊤
            ((Stacks.Divisors.canonicalSection' (differentIdealSheaf ω τ)).eval (op ⊤)) =
              τ.sect := by
  obtain ⟨_, _⟩ := flat_and_isInvertible_of_isGorenstein f hGor ω
  exact fun τ => ⟨isEffectiveCartierDivisor_differentIdealSheaf ω τ hét,
    existsUnique_invertibleSheafIso_differentIdealSheaf ω τ hét⟩

end Different

/-! ### The norm of `R` for a finite Gorenstein morphism -/

section NormOfDifferent

variable {X Y : Scheme.{u}} (f : Y ⟶ X) [IsNoetherian X] [IsNoetherian Y] [IsFinite f]
  (hGor : Scheme.Hom.IsGorenstein f (isLocallyNoetherian_fiber_of_locallyOfFiniteType f))

/-- **[Stacks, Tag 0C17 (5)].** If a finite Gorenstein morphism of Noetherian schemes has
relative dualizing module `ω_{Y/X}` and trace element `τ_{Y/X}`, then the norm of the closed
subscheme `R ⊆ Y` cut out by the different is the discriminant `D_f`: as ideal sheaves on `X`,
`Norm_f(𝔇_f)` is the discriminant ideal sheaf.

Gorensteinness makes `f` flat and `ω_{Y/X}` invertible, which is the situation of
[Stacks, Tag 0BWA (2)]. -/
@[stacks 0C17 "(5)"]
theorem discriminantIdeal_eq_normIdealSheaf_differentIdealSheaf_of_isGorenstein
    (ω : RelativeDualizingModuleData f) :
    letI : Flat f := ((Scheme.Hom.isGorenstein_iff_flat_and_isGorenstein_fiber f _).mp hGor).1
    letI : Stacks.Morphisms.IsFiniteLocallyFree f :=
      (Stacks.Morphisms.isFiniteLocallyFree_iff_isFinite_flat_of_isLocallyNoetherian f).mpr
        ⟨inferInstance, inferInstance⟩
    ∀ τ : RelativeTraceSection ω,
      discriminantIdeal f = Stacks.Norm.normIdealSheaf f (differentIdealSheaf ω τ) := by
  obtain ⟨_, _⟩ := flat_and_isInvertible_of_isGorenstein f hGor ω
  exact fun τ => discriminantIdeal_eq_normIdealSheaf_differentIdealSheaf ω τ

end NormOfDifferent

/-! ### Base change -/

section BaseChangeGorenstein

variable {X X' Y : Scheme.{u}} (f : Y ⟶ X) (g : X' ⟶ X)
  [IsNoetherian X] [IsNoetherian X'] [IsNoetherian Y]
  [LocallyOfFiniteType f] [QuasiCompact f] [LocallyQuasiFinite f]
  (hGor : Scheme.Hom.IsGorenstein f (isLocallyNoetherian_fiber_of_locallyOfFiniteType f))

/-- **[Stacks, Tag 0C17 (4)].** Formation of the closed subscheme `R ⊆ Y` cut out by the
different of a quasi-finite Gorenstein morphism of Noetherian schemes commutes with base change
along an arbitrary morphism `g : X' ⟶ X`: the closed immersion `R' ⟶ R ×_Y Y'` induced by
`Y' ⟶ Y` is an isomorphism.

Gorensteinness makes `ω_{Y/X}` invertible, which is the case of [Stacks, Tag 0BW7] in which the
inverse image of the different is the different of the base change with no flatness hypothesis
on `g`. -/
@[stacks 0C17 "(4)"]
theorem isIso_different_baseChange_of_isGorenstein {R R' : Scheme.{u}}
    (ω : RelativeDualizingModuleData f) (i : R ⟶ Y) [IsClosedImmersion i] :
    letI : Flat f := ((Scheme.Hom.isGorenstein_iff_flat_and_isGorenstein_fiber f _).mp hGor).1
    ∀ (τ : RelativeTraceSection ω) (ω' : RelativeDualizingModuleData (pullback.snd f g))
      (τ' : RelativeTraceSection ω') (i' : R' ⟶ pullback f g) [IsClosedImmersion i'],
      i.ker = differentIdealSheaf ω τ → i'.ker = differentIdealSheaf ω' τ' →
      ∀ (k : R' ⟶ R) (hk : k ≫ i = i' ≫ pullback.fst f g), IsIso (pullback.lift k i' hk) := by
  obtain ⟨_, _⟩ := flat_and_isInvertible_of_isGorenstein f hGor ω
  exact fun τ ω' τ' i' _ hi hi' k hk =>
    isIso_different_baseChange_of_gorenstein f g ω τ ω' τ' i i' hi hi' k hk

end BaseChangeGorenstein

end Stacks.Discriminant

end
