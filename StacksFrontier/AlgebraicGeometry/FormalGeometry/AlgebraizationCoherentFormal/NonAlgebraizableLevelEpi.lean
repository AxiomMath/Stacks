module

public import Mathlib.CategoryTheory.Functor.OfSequence
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EpiLocallySurjective
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AlgebraizationCoherentFormal.NonAlgebraizableLevelTransition
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The transition maps of the non-algebraizable example are epimorphisms

For `A = k[x,y][[t]]` the family `(𝓛ₙ)` of [Stacks, Tag 0EHE] has transition maps
`Stacks.Algebraization.NonAlgebraizableExample.levelTransition`, from `𝓛ₙ₊₁` to the direct image
of `𝓛ₙ` along the closed immersion of punctured spectra
`Spec(A/tⁿA) ∩ U ⟶ Spec(A/t^{n+1}A) ∩ U`. This file proves that those maps are epimorphisms, and
transports both the maps and that conclusion to the single category `U.Modules` in which a
`Stacks.Coherent.CoherentAdicSystems` lives.

## Main definitions

* `Stacks.Algebraization.NonAlgebraizableExample.levelPushforwardIso` — the identification of the
  direct image along `Spec(A/tⁿA) ∩ U ⟶ Spec(A/t^{n+1}A) ∩ U` followed by the one along the
  structure map of level `n + 1` with the direct image along the structure map of level `n`.
* `Stacks.Algebraization.NonAlgebraizableExample.levelTransitionOnOpen` — the transition map
  `𝓛ₙ₊₁ ⟶ 𝓛ₙ` of the system as a morphism of modules on `U`.
* `Stacks.Algebraization.NonAlgebraizableExample.ambientBasicOpen` — the basic open `D(h)` of
  `Spec(A)`, as an open of `U`.
* `Stacks.Algebraization.NonAlgebraizableExample.levelSystem` — the family `(𝓛ₙ)` as a diagram
  `ℕᵒᵖ ⥤ U.Modules`, the shape an object of `Coh(U, I𝒪_U)` is a diagram of, indexed so that the
  `n`-th term is `𝓛ₙ₊₁`.

## Main results

* `Stacks.Algebraization.NonAlgebraizableExample.epi_levelTransition` — the transition map
  `𝓛ₙ₊₁ ⟶ (𝓛ₙ)` is an epimorphism.
* `Stacks.Algebraization.NonAlgebraizableExample.levelOpenMap_comp_levelStructureMap` — the
  closed immersions of punctured spectra are compatible with the structure maps to `U`.
* `Stacks.Algebraization.NonAlgebraizableExample.epi_levelTransitionOnOpen` — the transition map
  of the system, read on `U`, is an epimorphism.
* `Stacks.Algebraization.NonAlgebraizableExample.epi_levelSystem_map_succ` — the same for the
  maps of the diagram.

## References

* [Stacks Project, Tag 0EHE](https://stacks.math.columbia.edu/tag/0EHE)
* [Stacks Project, Tag 01AH](https://stacks.math.columbia.edu/tag/01AH)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme

/-- Restricting `f` to opens `V ≤ U` carries the part of an open `O` lying over `U` to the part
of `f ⁻¹ᵁ O` lying over `V`. -/
public theorem Hom.resLE_preimage_preimage_ι {X Y : Scheme.{u}} (f : X ⟶ Y) {U : Y.Opens}
    {V : X.Opens} (e : V ≤ f ⁻¹ᵁ U) (O : Y.Opens) :
    f.resLE U V e ⁻¹ᵁ (U.ι ⁻¹ᵁ O) = V.ι ⁻¹ᵁ (f ⁻¹ᵁ O) := by
  have htop : V.ι ⁻¹ᵁ (f ⁻¹ᵁ U) = ⊤ :=
    top_le_iff.mp ((Scheme.Opens.ι_preimage_self V).ge.trans (V.ι.preimage_mono e))
  rw [Scheme.Hom.resLE_preimage, Scheme.Hom.image_preimage_eq_opensRange_inf,
    Scheme.Opens.opensRange_ι, Scheme.Hom.preimage_inf, Scheme.Hom.preimage_inf, htop,
    top_inf_eq]

/-- **The restriction of a closed immersion to an open and its whole preimage is a closed
immersion**: for `f ⁻¹ᵁ U = V`, the restriction `f.resLE U V` is a closed immersion. -/
@[ega "I 4.2.4" "(b): necessity"]
public theorem Hom.isClosedImmersion_resLE {X Y : Scheme.{u}} (f : X ⟶ Y) [IsClosedImmersion f]
    {U : Y.Opens} {V : X.Opens} (h : f ⁻¹ᵁ U = V) :
    IsClosedImmersion (f.resLE U V h.ge) := by
  subst h
  rw [Scheme.Hom.resLE_eq_morphismRestrict]
  exact IsZariskiLocalAtTarget.restrict (P := @IsClosedImmersion) inferInstance U

/-- A morphism of modules is surjective on the sections over the empty open: the ring of
functions there is the zero ring, so every module over it vanishes. -/
public theorem Modules.Hom.surjective_app_of_eq_bot {X : Scheme.{u}} {M N : X.Modules}
    (f : M ⟶ N) {V : X.Opens} (hV : V = ⊥) : Function.Surjective (f.app V) := by
  subst hV
  have : Subsingleton Γ(N, (⊥ : X.Opens)) := Module.subsingleton Γ(X, (⊥ : X.Opens)) _
  exact fun _ => ⟨0, Subsingleton.elim _ _⟩

end AlgebraicGeometry.Scheme

namespace Stacks.Algebraization.NonAlgebraizableExample

variable (k : Type u) [Field k]

/-! ### The closed immersion of level schemes -/

/-- The reduction `Spec(A/tⁿA) ⟶ Spec(A/t^{n+1}A)` is a closed immersion, being the spectrum of
a surjection. -/
public instance isClosedImmersion_levelSchemeMap (n : ℕ) :
    IsClosedImmersion (levelSchemeMap k n) :=
  IsClosedImmersion.spec_of_surjective _
    (Ideal.Quotient.factor_surjective (Ideal.pow_le_pow_right (Nat.le_succ n)))

/-- The map `Spec(A/tⁿA) ∩ U ⟶ Spec(A/t^{n+1}A) ∩ U` of punctured spectra is a closed
immersion. -/
public instance isClosedImmersion_levelOpenMap (n : ℕ) :
    IsClosedImmersion (levelOpenMap k n) :=
  Scheme.Hom.isClosedImmersion_resLE (levelSchemeMap k n) (preimage_levelOpen k n)

/-! ### The transition map upstairs is an epimorphism -/

/-- The preimage of the `i`-th member of the two-chart family of level `n + 1` is the `i`-th
member of the two-chart family of level `n`. -/
public theorem preimage_twoChartFamily (n : ℕ) (i : ULift.{u} Bool) :
    levelOpenMap k n ⁻¹ᵁ Stacks.SheafOfModules.twoChartFamily
        (levelChart k (xVar k) (n + 1)) (levelChart k (yVar k) (n + 1)) i =
      Stacks.SheafOfModules.twoChartFamily (levelChart k (xVar k) n) (levelChart k (yVar k) n) i :=
  (congrFun (Stacks.SheafOfModules.twoChartFamily_eq_preimage (levelOpenMap k n)
    (preimage_levelChart k (xVar k) n (le_sup_left : chartOpen k (xVar k) (n + 1) ≤ _))
    (preimage_levelChart k (yVar k) n (le_sup_right : chartOpen k (yVar k) (n + 1) ≤ _))) i).symm

/-- The transition map `𝓛ₙ₊₁ ⟶ (𝓛ₙ)` is surjective on the sections over every affine open
contained in one of the two charts. -/
@[stacks 0EHE "L_(n+1) -> L_n is surjective on sections over an affine open of a chart"]
public theorem surjective_app_levelTransition (a : ℕ → PlaneRing k) (φ : ℕ → ℕ) (n : ℕ)
    (i : ULift.{u} Bool) {V : (levelOpen k (n + 1)).toScheme.Opens}
    (hV : V ≤ Stacks.SheafOfModules.twoChartFamily
      (levelChart k (xVar k) (n + 1)) (levelChart k (yVar k) (n + 1)) i)
    (hVa : IsAffineOpen V) :
    Function.Surjective ((levelTransition k a φ n).val.app (op V)) := by
  have hV' : levelOpenMap k n ⁻¹ᵁ V ≤ Stacks.SheafOfModules.twoChartFamily
      (levelChart k (xVar k) n) (levelChart k (yVar k) n) i :=
    ((levelOpenMap k n).preimage_mono hV).trans (preimage_twoChartFamily k n i).le
  intro t
  obtain ⟨r, hr⟩ := (levelOpenMap k n).app_surjective V hVa
    ((Stacks.SheafOfModules.twoChartCocycle
      (levelOverlapUnit k a φ n)).chartLinearEquiv i hV' t)
  refine ⟨(Stacks.SheafOfModules.twoChartCocycle
    (levelOverlapUnit k a φ (n + 1))).chartLinearEquiv i hV |>.symm r, ?_⟩
  have hkey := chartLinearEquiv_levelTransition k a φ n i hV hV'
    ((Stacks.SheafOfModules.twoChartCocycle
      (levelOverlapUnit k a φ (n + 1))).chartLinearEquiv i hV |>.symm r)
  rw [LinearEquiv.apply_symm_apply] at hkey
  exact (Stacks.SheafOfModules.twoChartCocycle
    (levelOverlapUnit k a φ n)).chartLinearEquiv i hV' |>.injective (hkey.trans hr)

/-- The transition map `𝓛ₙ₊₁ ⟶ (𝓛ₙ)` of the system is an epimorphism of modules on the
punctured spectrum of `A/t^{n+1}A`. -/
@[stacks 0EHE "the transition map L_(n+1) -> L_n is an epimorphism"]
public theorem epi_levelTransition (a : ℕ → PlaneRing k) (φ : ℕ → ℕ) (n : ℕ) :
    Epi (levelTransition k a φ n) := by
  refine Stacks.SheafOfModules.EpiMono.epi_of_isLocallySurjective _ ⟨fun {W} s => ?_⟩
  rw [Opens.mem_grothendieckTopology]
  intro x hx
  obtain ⟨i, hxi⟩ : ∃ i, x ∈ Stacks.SheafOfModules.twoChartFamily
      (levelChart k (xVar k) (n + 1)) (levelChart k (yVar k) (n + 1)) i := by
    rcases sup_levelChart k (n + 1) (show x ∈ (⊤ : (levelOpen k (n + 1)).toScheme.Opens) from
      trivial) with h | h
    exacts [⟨⟨false⟩, h⟩, ⟨⟨true⟩, h⟩]
  obtain ⟨V, hVa, hxV, hVle⟩ := Opens.isBasis_iff_nbhd.mp
    ((levelOpen k (n + 1)).toScheme.isBasis_affineOpens)
    (show x ∈ W ⊓ Stacks.SheafOfModules.twoChartFamily
      (levelChart k (xVar k) (n + 1)) (levelChart k (yVar k) (n + 1)) i from ⟨hx, hxi⟩)
  exact ⟨V, homOfLE (hVle.trans inf_le_left), surjective_app_levelTransition k a φ n i
    (hVle.trans inf_le_right) hVa _, hxV⟩

/-! ### The transition map of the system on `U` -/

/-- The reduction `Spec(A/tⁿA) ⟶ Spec(A/t^{n+1}A)` followed by the structure map of level
`n + 1` is the structure map of level `n`. -/
public theorem levelSchemeMap_comp_levelToAmbient (n : ℕ) :
    levelSchemeMap k n ≫ levelToAmbient k (n + 1) = levelToAmbient k n := by
  rw [← Spec.map_comp]
  rfl

/-- The closed immersion of the punctured spectrum of `A/tⁿA` in that of `A/t^{n+1}A`, followed by
the structure map of level `n + 1` to `U`, is the structure map of level `n`. -/
@[stacks 0EHE "the closed immersions of punctured spectra are compatible with the maps to U"]
public theorem levelOpenMap_comp_levelStructureMap (n : ℕ) :
    levelOpenMap k n ≫ levelStructureMap k (n + 1) = levelStructureMap k n := by
  refine (Scheme.Hom.resLE_comp_resLE _ _ _ _).trans ?_
  congr 1
  exact levelSchemeMap_comp_levelToAmbient k n

/-- Taking the direct image along the closed immersion of punctured spectra and then along the
structure map of level `n + 1` is taking it along the structure map of level `n`. -/
public def levelPushforwardIso (n : ℕ) :
    Scheme.Modules.pushforward (levelOpenMap k n) ⋙
        Scheme.Modules.pushforward (levelStructureMap k (n + 1)) ≅
      Scheme.Modules.pushforward (levelStructureMap k n) :=
  Scheme.Modules.pushforwardComp (levelOpenMap k n) (levelStructureMap k (n + 1)) ≪≫
    Scheme.Modules.pushforwardCongr (levelOpenMap_comp_levelStructureMap k n)

/-- The transition map `𝓛ₙ₊₁ ⟶ 𝓛ₙ` of the system as a morphism of modules on the punctured
spectrum `U` of `A`: the direct image along the structure map of level `n + 1` of
`Stacks.Algebraization.NonAlgebraizableExample.levelTransition`, read through
`Stacks.Algebraization.NonAlgebraizableExample.levelPushforwardIso`. -/
@[stacks 0EHE "the transition map L_(n+1) -> L_n of the system, as modules on U"]
public def levelTransitionOnOpen (a : ℕ → PlaneRing k) (φ : ℕ → ℕ) (n : ℕ) :
    levelModuleOnOpen k a φ (n + 1) ⟶ levelModuleOnOpen k a φ n :=
  (Scheme.Modules.pushforward (levelStructureMap k (n + 1))).map (levelTransition k a φ n) ≫
    (levelPushforwardIso k n).hom.app (levelModule k a φ n)

/-- On the sections over an open of `U` the transition map of the system is the transition map
upstairs, over the preimage of that open, followed by the identification of the direct images. -/
public theorem app_levelTransitionOnOpen (a : ℕ → PlaneRing k) (φ : ℕ → ℕ) (n : ℕ)
    (W : (situation k).U.toScheme.Opens) :
    (levelTransitionOnOpen k a φ n).app W =
      (levelTransition k a φ n).app (levelStructureMap k (n + 1) ⁻¹ᵁ W) ≫
        ((levelPushforwardIso k n).hom.app (levelModule k a φ n)).app W := rfl

/-- If the transition map upstairs is surjective on the sections over the preimage of an open of
`U`, then the transition map of the system is surjective on the sections over that open. -/
public theorem surjective_app_levelTransitionOnOpen (a : ℕ → PlaneRing k) (φ : ℕ → ℕ) (n : ℕ)
    (W : (situation k).U.toScheme.Opens)
    (hW : Function.Surjective
      ((levelTransition k a φ n).app (levelStructureMap k (n + 1) ⁻¹ᵁ W))) :
    Function.Surjective ((levelTransitionOnOpen k a φ n).app W) := by
  have hiso : Function.Surjective
      (((levelPushforwardIso k n).hom.app (levelModule k a φ n)).app W) :=
    (ConcreteCategory.bijective_of_isIso _).2
  rw [app_levelTransitionOnOpen]
  intro t
  obtain ⟨u, hu⟩ := hiso t
  obtain ⟨v, hv⟩ := hW u
  refine ⟨v, (ConcreteCategory.comp_apply _ _ v).trans ?_⟩
  rw [hv]
  exact hu

/-! ### The basic opens of `Spec(A)` inside `U` -/

/-- The basic open `D(h)` of `Spec(A)`, as an open of the punctured spectrum `U` of `A`. -/
public abbrev ambientBasicOpen (h : AmbientRing k) : (situation k).U.toScheme.Opens :=
  (situation k).U.ι ⁻¹ᵁ PrimeSpectrum.basicOpen h

/-- The preimage of the basic open `D(h)` of `Spec(A)` under the structure map of level `n` is
the basic open `D(h̄)` of `Spec(A/tⁿA)`. -/
public theorem preimage_levelToAmbient_basicOpen (h : AmbientRing k) (m : ℕ) :
    levelToAmbient k m ⁻¹ᵁ PrimeSpectrum.basicOpen h = chartOpen k h m := rfl

/-- A basic open `D(h̄)` of `Spec(A/tⁿA)` whose `D(h)` lies in `U` lies in the punctured spectrum
of `A/tⁿA`. -/
public theorem chartOpen_le_levelOpen (h : AmbientRing k) (m : ℕ)
    (hh : PrimeSpectrum.basicOpen h ≤ (situation k).U) :
    chartOpen k h m ≤ levelOpen k m :=
  (preimage_levelToAmbient_basicOpen k h m).ge.trans
    (((levelToAmbient k m).preimage_mono hh).trans (preimage_U_levelToAmbient k m).le)

/-- The preimage of `D(h)` under the structure map `Spec(A/tⁿA) ∩ U ⟶ U` is the chart `D(h̄)` of
the punctured spectrum of `A/tⁿA`. -/
@[stacks 0EHE "the preimage of D(h) in the punctured spectrum of A/t^n A is D(h)"]
public theorem preimage_levelStructureMap_ambientBasicOpen (h : AmbientRing k) (m : ℕ) :
    levelStructureMap k m ⁻¹ᵁ ambientBasicOpen k h = levelChart k h m :=
  Scheme.Hom.resLE_preimage_preimage_ι (levelToAmbient k m)
    (preimage_U_levelToAmbient k m).ge (PrimeSpectrum.basicOpen h)

/-- A chart `D(h̄)` of the punctured spectrum of `A/tⁿA` whose `D(h)` lies in `U` is affine. -/
public theorem isAffineOpen_levelChart (h : AmbientRing k) (m : ℕ)
    (hh : PrimeSpectrum.basicOpen h ≤ (situation k).U) :
    IsAffineOpen (levelChart k h m) :=
  (IsAffineOpen.Spec_basicOpen (levelElt k h m)).preimage_of_isOpenImmersion
    (levelOpen k m).ι ((chartOpen_le_levelOpen k h m hh).trans
      (Scheme.Opens.opensRange_ι (levelOpen k m)).ge)

/-- The basic opens `D(h)` of `Spec(A)`, restricted to `U`, are a basis of the topology of `U`. -/
public theorem exists_ambientBasicOpen_nbhd {W : (situation k).U.toScheme.Opens}
    {x : (situation k).U.toScheme} (hx : x ∈ W) :
    ∃ h : AmbientRing k, x ∈ ambientBasicOpen k h ∧ ambientBasicOpen k h ≤ W := by
  have hW : (situation k).U.ι ⁻¹ᵁ ((situation k).U.ι ''ᵁ W) = W :=
    Scheme.Hom.preimage_image_eq _ _
  have hxim : (x.val : (situation k).X) ∈ (situation k).U.ι ''ᵁ W := hW.ge hx
  obtain ⟨D, ⟨r, rfl⟩, hxD, hDO⟩ := Opens.isBasis_iff_nbhd.mp
    (PrimeSpectrum.isBasis_basic_opens (R := AmbientRing k)) hxim
  exact ⟨r, hxD, fun z hz => hW.le (hDO hz)⟩

/-- Each of `D(x)`, `D(y)` and `D(t)` lies in the punctured spectrum `U` of `A`. -/
public theorem basicOpen_le_U {g : AmbientRing k}
    (hg : g ∈ ({xVar k, yVar k, tVar k} : Set (AmbientRing k))) :
    PrimeSpectrum.basicOpen g ≤ (situation k).U :=
  fun _ hp hmem => hp (hmem (Ideal.subset_span hg))

/-- The punctured spectrum `U` of `A` is covered by `D(x)`, `D(y)` and `D(t)`. -/
@[stacks 0EHE "U is covered by D(x), D(y) and D(t)"]
public theorem exists_mem_basicOpen_of_mem_U (p : (situation k).X)
    (hp : p ∈ (situation k).U) :
    p ∈ PrimeSpectrum.basicOpen (xVar k) ∨ p ∈ PrimeSpectrum.basicOpen (yVar k) ∨
      p ∈ PrimeSpectrum.basicOpen (tVar k) := by
  rcases Classical.em (xVar k ∈ p.asIdeal) with hx | hx
  · rcases Classical.em (yVar k ∈ p.asIdeal) with hy | hy
    · rcases Classical.em (tVar k ∈ p.asIdeal) with ht | ht
      · refine absurd (Ideal.span_le.mpr ?_) hp
        rintro z (rfl | rfl | rfl)
        exacts [hx, hy, ht]
      · exact Or.inr (Or.inr ht)
    · exact Or.inr (Or.inl hy)
  · exact Or.inl hx

/-- The chart of a product is inside the chart of either factor. -/
public theorem levelChart_mul_le (h g : AmbientRing k) (m : ℕ) :
    levelChart k (h * g) m ≤ levelChart k g m :=
  (levelOpen k m).ι.preimage_mono (by
    rw [chartOpen, levelElt, map_mul]
    exact PrimeSpectrum.basicOpen_mul_le_right _ _)

/-- The chart of a multiple of `t` is empty in `Spec(A/tⁿA)`, the image of `t` there being
nilpotent. -/
public theorem levelChart_mul_tVar_eq_bot (h : AmbientRing k) (m : ℕ) :
    levelChart k (h * tVar k) m = ⊥ :=
  le_bot_iff.mp ((levelChart_mul_le k h (tVar k) m).trans
    ((levelOpen k m).ι.preimage_mono
      ((PrimeSpectrum.basicOpen_eq_bot_iff _).mpr (isNilpotent_mk_tVar k m)).le))

/-- A point of `D(h)` which also lies in `D(g)` lies in `D(hg)`. -/
public theorem mem_ambientBasicOpen_mul {h g : AmbientRing k} {x : (situation k).U.toScheme}
    (hxh : x ∈ ambientBasicOpen k h)
    (hxg : (x.val : (situation k).X) ∈ PrimeSpectrum.basicOpen g) :
    x ∈ ambientBasicOpen k (h * g) :=
  (situation k).U.ι.preimage_mono (PrimeSpectrum.basicOpen_mul h g).ge ⟨hxh, hxg⟩

/-- The transition map of the system is surjective on the sections over `D(hg)` whenever `D(g)`
lies in `U` and the chart of `g` lies in the `i`-th of the two charts. -/
public theorem surjective_app_levelTransitionOnOpen_chart (a : ℕ → PlaneRing k) (φ : ℕ → ℕ)
    (n : ℕ) (h g : AmbientRing k) (i : ULift.{u} Bool)
    (hg : PrimeSpectrum.basicOpen g ≤ (situation k).U)
    (hchart : levelChart k g (n + 1) ≤ Stacks.SheafOfModules.twoChartFamily
      (levelChart k (xVar k) (n + 1)) (levelChart k (yVar k) (n + 1)) i) :
    Function.Surjective ((levelTransitionOnOpen k a φ n).app (ambientBasicOpen k (h * g))) := by
  refine surjective_app_levelTransitionOnOpen k a φ n _ ?_
  rw [preimage_levelStructureMap_ambientBasicOpen]
  exact surjective_app_levelTransition k a φ n i
    ((levelChart_mul_le k h g (n + 1)).trans hchart)
    (isAffineOpen_levelChart k (h * g) (n + 1)
      ((PrimeSpectrum.basicOpen_mul_le_right h g).trans hg))

/-- The transition map `𝓛ₙ₊₁ ⟶ 𝓛ₙ` of the system, read as a morphism of modules on the punctured
spectrum `U` of `A`, is an epimorphism. -/
@[stacks 0EHE "the transition map of the system on U is an epimorphism"]
public theorem epi_levelTransitionOnOpen (a : ℕ → PlaneRing k) (φ : ℕ → ℕ) (n : ℕ) :
    Epi (levelTransitionOnOpen k a φ n) := by
  refine Stacks.SheafOfModules.EpiMono.epi_of_isLocallySurjective _ ⟨fun {W} s => ?_⟩
  rw [Opens.mem_grothendieckTopology]
  intro x hx
  obtain ⟨h, hxh, hhW⟩ := exists_ambientBasicOpen_nbhd k hx
  rcases exists_mem_basicOpen_of_mem_U k x.val x.2 with hc | hc | hc
  · exact ⟨ambientBasicOpen k (h * xVar k),
      homOfLE (((situation k).U.ι.preimage_mono
        (PrimeSpectrum.basicOpen_mul_le_left h (xVar k))).trans hhW),
      surjective_app_levelTransitionOnOpen_chart k a φ n h (xVar k) ⟨false⟩
        (basicOpen_le_U k (Set.mem_insert _ _)) le_rfl _,
      mem_ambientBasicOpen_mul k hxh hc⟩
  · exact ⟨ambientBasicOpen k (h * yVar k),
      homOfLE (((situation k).U.ι.preimage_mono
        (PrimeSpectrum.basicOpen_mul_le_left h (yVar k))).trans hhW),
      surjective_app_levelTransitionOnOpen_chart k a φ n h (yVar k) ⟨true⟩
        (basicOpen_le_U k (Set.mem_insert_of_mem _ (Set.mem_insert _ _))) le_rfl _,
      mem_ambientBasicOpen_mul k hxh hc⟩
  · exact ⟨ambientBasicOpen k (h * tVar k),
      homOfLE (((situation k).U.ι.preimage_mono
        (PrimeSpectrum.basicOpen_mul_le_left h (tVar k))).trans hhW),
      surjective_app_levelTransitionOnOpen k a φ n _
        (Scheme.Modules.Hom.surjective_app_of_eq_bot _
          ((preimage_levelStructureMap_ambientBasicOpen k (h * tVar k) (n + 1)).trans
            (levelChart_mul_tVar_eq_bot k h (n + 1)))) _,
      mem_ambientBasicOpen_mul k hxh hc⟩

/-! ### The system as a diagram over `ℕᵒᵖ` -/

/-- The family `(𝓛ₙ)` as an inverse system of modules on the punctured spectrum `U` of `A`,
assembled from the transition maps
`Stacks.Algebraization.NonAlgebraizableExample.levelTransitionOnOpen`. Its `n`-th term is
`𝓛ₙ₊₁`, the module on the punctured spectrum of `A/t^{n+1}A`, matching the indexing of
`Stacks.Coherent.IsCoherentAdicSystem`. -/
@[stacks 0EHE "the system (L_n) as a diagram over the opposite of the naturals"]
public def levelSystem (a : ℕ → PlaneRing k) (φ : ℕ → ℕ) :
    ℕᵒᵖ ⥤ (situation k).U.toScheme.Modules :=
  Functor.ofOpSequence (X := fun n => levelModuleOnOpen k a φ (n + 1))
    (fun n => levelTransitionOnOpen k a φ (n + 1))

/-- The `n`-th term of the system is `𝓛ₙ₊₁`, pushed forward to `U`. -/
public theorem levelSystem_obj (a : ℕ → PlaneRing k) (φ : ℕ → ℕ) (n : ℕ) :
    (levelSystem k a φ).obj (op n) = levelModuleOnOpen k a φ (n + 1) := rfl

/-- The map of the system from its `(n + 1)`-st term to its `n`-th one is the transition map
`𝓛ₙ₊₂ ⟶ 𝓛ₙ₊₁`. -/
public theorem levelSystem_map_succ (a : ℕ → PlaneRing k) (φ : ℕ → ℕ) (n : ℕ) :
    (levelSystem k a φ).map (homOfLE (Nat.le_succ n)).op = levelTransitionOnOpen k a φ (n + 1) :=
  Functor.ofOpSequence_map_homOfLE_succ _ n

/-- The maps of the system from its `(n + 1)`-st term to its `n`-th one are epimorphisms. -/
@[stacks 0EHE "the maps of the system (L_n) from level n+1 to level n are epimorphisms"]
public theorem epi_levelSystem_map_succ (a : ℕ → PlaneRing k) (φ : ℕ → ℕ) (n : ℕ) :
    Epi ((levelSystem k a φ).map (homOfLE (Nat.le_succ n)).op) := by
  rw [levelSystem_map_succ]
  exact epi_levelTransitionOnOpen k a φ (n + 1)

end Stacks.Algebraization.NonAlgebraizableExample

end
