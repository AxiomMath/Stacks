module

public import Mathlib.RingTheory.AdicCompletion.RingHom
public import Mathlib.RingTheory.Etale.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.AdicQuotientSystemOfCompleteLocal
public import StacksFrontier.AlgebraicGeometry.FormalSpace.PullbackChartCover
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RepresentableSource
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RigSurjective
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RigSurjectiveCriterion
public import StacksFrontier.AlgebraicGeometry.FormalSpace.SetTheoreticColimit
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Surjective
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Types
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringSieveSurjective
public import StacksFrontier.CategoryTheory.Sites.Density
public import StacksFrontier.CategoryTheory.Sites.QuasiCompact.LocallySurjectiveTransfer
public import StacksFrontier.CategoryTheory.Sites.Representable.SheafifiedYonedaSubcanonical
public import StacksFrontier.RingTheory.AdicCompletion.DvrValuedPoints
public import StacksFrontier.Topology.Algebra.AdicTopology.CompletionOver
public import StacksFrontier.Topology.Algebra.AdicTopology.WeaklyAdmissibleAdic
import StacksFrontier.AlgebraicGeometry.FormalSpace.RigFlatComposition

/-!
# A surjective étale morphism of formal algebraic spaces is rig-surjective

Let `S` be a scheme contained in a big fppf site `B`. A morphism `f : X ⟶ Y` of locally
Noetherian formal algebraic spaces over `S` which is representable by algebraic spaces, étale
and surjective is rig-surjective (**Stacks 0AQU**). This file carries the ingredients of the
source's proof; the statement itself is
`AlgebraicGeometry.FormalSpace.isRigSurjective_of_isSurjective_of_isRepresentableEtale` and
`AlgebraicGeometry.FormalSpace.isRigSurjective_of_isRepresentableEtale_of_isSurjective'`, the
latter assembling the ingredients below.

The source's proof runs as follows. An adic point `p : Spf R ⟶ Y` out of the formal spectrum
of a complete discrete valuation ring is base changed to `Z = Spf R ×_Y X`, whose projection to
`Spf R` is again representable by algebraic spaces, étale and surjective. The formal spectrum of
`R` has a point — the spectrum of the residue field is one of its quotient stages — so `Z` has
one too, and hence so does one chart `V ⟶ Z` of `Z`. That chart is an affine formal algebraic
space whose composite to `Spf R` is representable and étale, so the essential-surjectivity
clause of Stacks 0AN8 writes it as `Spf A^∧` for an étale `R`-algebra `A`; the chart has a point,
so `A^∧ ≠ 0`, so `A ⧸ m_R A ≠ 0` and `A` has a maximal ideal over `m_R`. Localizing there gives a
Noetherian local ring, flat and local over `R`, which maps to an extension `R ⊂ R'` of complete
discrete valuation rings. The resulting `A → R'` extends continuously to `A^∧ → R'`, and `Spf` of
that map, composed with `Spf A^∧ ≅ V ⟶ Z ⟶ X`, is the lift the definition of rig-surjectivity
asks for.

## Main definitions

* `AlgebraicGeometry.FormalSpace.IsEssentiallySurjectiveSpf`: the essential-surjectivity clause
  of **Stacks 0AN8**, which this library does not carry — see below.

## Main results

* `exists_isAdicComplete_isDiscreteValuationRing_of_etale`: the commutative-algebra step of
  Stacks 0AQU. An étale algebra over a discrete valuation ring whose reduction modulo the
  maximal ideal is nonzero maps to a complete discrete valuation ring extension of the base.
* `exists_continuous_ringHom_completionOver`: a ring map to a local ring complete for its
  maximal-adic topology, carrying the defining ideal of the base into the maximal ideal,
  extends continuously to the completion over the base.
* `map_ne_top_of_nontrivial_completionOver`: a nontrivial completion over an adic base forces
  the extension of the defining ideal to be proper.

## Implementation notes

### The essential-surjectivity clause of Stacks 0AN8

`AlgebraicGeometry.FormalSpace.IsEssentiallySurjectiveSpf` is the
essential-surjectivity half of the equivalence of categories of **Stacks 0AN8**: a
representable étale morphism from an affine formal algebraic space to `Spf R` is `Spf` of
`R → A^∧` for an étale `R`-algebra `A`. The two declarations this library tags with Stacks 0AN8,
`TopologicalRing.etale_quotientMap_weakIdealOfDefinition` and
`TopologicalRing.CompletionOver.etale_quotientMap_canonicalMap`, carry only the first step of
its proof, and their tag comments exclude essential surjectivity by name. The other half of the
equivalence, full faithfulness of `Spf`, is Stacks 0AN0 and is available as
`AlgebraicGeometry.FormalSpace.existsUnique_continuousHom_formalSpectrumMap_eq`; it is not
needed here, because the morphism out of `Spf R'` is built from a ring map rather than
recognised from a morphism.

### Stacks 0AP2 is not used

The source obtains the complete discrete valuation ring `R'` by localizing `A` at a maximal
ideal over `m_R`, noting that the localization is a discrete valuation ring (Stacks 0AP2) and
completing it (Stacks 0AP1). This file instead feeds the localization — a Noetherian local ring,
flat and local over `R` — to
`exists_isAdicComplete_isDiscreteValuationRing_of_flat`, which reaches the same conclusion
through going down, Stacks 00PH and Stacks 0AP1. That is a generalization of the source's step,
not a weakening: it does not need the localization to be a discrete valuation ring.

### Nonemptiness

The source's "`Z` is nonempty, pick a nonempty affine formal algebraic space `V` and an étale
morphism `V → Z`" is rendered through points of `StacksDraft.AlgebraicGeometry.Spaces`
`LargeValuedPoints`: a point of a sheaf is a section over a field spectrum of the site, the
charts of a formal algebraic space are jointly surjective, and
`CategoryTheory.Sheaf.isLocallySurjective_sigmaDesc_iff` (Stacks 00WI) puts the section of `Z`
locally in a single chart. The passage back from a point of the chart to nontriviality of `A^∧`
runs the same way through the quotient stages of `Spf A^∧`, using that the big fppf topology is
subcanonical so that a section of a stage is a morphism of the site.

## References

* [Stacks Project, Tag 0AN0](https://stacks.math.columbia.edu/tag/0AN0)
* [Stacks Project, Tag 0AN8](https://stacks.math.columbia.edu/tag/0AN8)
* [Stacks Project, Tag 0AP1](https://stacks.math.columbia.edu/tag/0AP1)
* [Stacks Project, Tag 0AP2](https://stacks.math.columbia.edu/tag/0AP2)
* [Stacks Project, Tag 0AQQ](https://stacks.math.columbia.edu/tag/0AQQ)
* [Stacks Project, Tag 0AQU](https://stacks.math.columbia.edu/tag/0AQU)
-/

@[expose] public noncomputable section

open Cardinal

universe u

/-- An étale algebra `A` over a discrete valuation ring `R` whose reduction modulo the maximal
ideal of `R` is nonzero admits a local `R`-algebra map to a complete discrete valuation ring
extension of `R`.

A maximal ideal `m` of `A` containing `m_R A` contracts to `m_R`, which is nonzero, so the
localization `A_m` is a Noetherian local ring, flat and local over `R`; this is the input of
`exists_isAdicComplete_isDiscreteValuationRing_of_flat`. -/
theorem exists_isAdicComplete_isDiscreteValuationRing_of_etale
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (A : Type u) [CommRing A] [Algebra R A] [Algebra.Etale R A]
    (hA : (IsLocalRing.maximalIdeal R).map (algebraMap R A) ≠ ⊤)
    (kappa : Cardinal.{u}) (hk : ℵ₀ < kappa) (hsl : IsStrongPrelimit kappa)
    (hAcard : #A < kappa) :
    ∃ (W : Type u) (_ : CommRing W) (_ : IsDomain W) (_ : IsDiscreteValuationRing W)
      (_ : Algebra R W) (_ : IsDiscreteValuationRing.IsExtension R W)
      (_ : IsAdicComplete (IsLocalRing.maximalIdeal W) W)
      (g : A →+* W), g.comp (algebraMap R A) = algebraMap R W ∧ #W < kappa := by
  obtain ⟨m, hmmax, hmle⟩ := Ideal.exists_le_maximal _ hA
  have hmprime : m.IsPrime := hmmax.isPrime
  have hcomap : IsLocalRing.maximalIdeal R ≤ m.comap (algebraMap R A) :=
    Ideal.map_le_iff_le_comap.mp hmle
  have hAnoeth : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing R A
  have hloc : IsLocalHom (algebraMap R (Localization.AtPrime m)) := by
    refine ⟨fun r hr => ?_⟩
    rw [IsScalarTower.algebraMap_apply R A (Localization.AtPrime m)] at hr
    have hnot : algebraMap R A r ∉ m :=
      (IsLocalization.AtPrime.isUnit_to_map_iff (Localization.AtPrime m) m _).mp hr
    rw [← IsLocalRing.notMem_maximalIdeal]
    exact fun hmem => hnot (hcomap hmem)
  have hsmooth : Algebra.Smooth R A := inferInstance
  have hflatA : Module.Flat R A := inferInstance
  have hflat : Module.Flat R (Localization.AtPrime m) :=
    Module.Flat.trans R A (Localization.AtPrime m)
  obtain ⟨W, hWring, hWdom, hWdvr, hRW, hWext, hWcomplete, g, -, hWcard⟩ :=
    exists_isAdicComplete_isDiscreteValuationRing_of_flat R (Localization.AtPrime m) kappa hk hsl
      ((Cardinal.mk_le_of_isLocalization m.primeCompl (Localization.AtPrime m)).trans_lt
        (max_lt hk hAcard))
  refine ⟨W, hWring, hWdom, hWdvr, hRW, hWext, hWcomplete,
    g.toRingHom.comp (algebraMap A (Localization.AtPrime m)), ?_, hWcard⟩
  ext r
  change g (algebraMap A (Localization.AtPrime m) (algebraMap R A r)) = algebraMap R W r
  rw [← IsScalarTower.algebraMap_apply R A (Localization.AtPrime m)]
  exact g.commutes r

/-- An algebra of finite type is no bigger than its base: it is a quotient of a polynomial ring
in finitely many variables over the base. -/
theorem Cardinal.mk_le_max_aleph0_of_finiteType (R : Type u) [CommRing R] (A : Type u)
    [CommRing A] [Algebra R A] [h : Algebra.FiniteType R A] : #A ≤ max ℵ₀ #R := by
  obtain ⟨ι, hfin, φ, hφ⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial'.mp h
  refine (Cardinal.mk_le_of_surjective hφ).trans (MvPolynomial.cardinalMk_le_max.trans ?_)
  have hι : #ι ≤ ℵ₀ := (Cardinal.lt_aleph0_of_finite ι).le
  simp only [max_le_iff]
  exact ⟨⟨le_max_right _ _, hι.trans (le_max_left _ _)⟩, le_max_left _ _⟩

section Lift

open TopologicalRing TopologicalRing.CompletionOver

variable {R : Type u} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
  {A : Type u} [CommRing A]
  {W : Type u} [CommRing W] [IsLocalRing W]

/-- The weak ideal of definition `I ^ (n + 1)` of a ring with the `I`-adic topology. -/
private def powIndex {I : Ideal R} (hRadic : IsAdic I) (n : ℕ) :
    WeakIdealOfDefinitionIndex R :=
  ⟨I ^ (n + 1), TopologicalRing.isWeakIdealOfDefinition_pow_of_isAdic hRadic n⟩

/-- The extension to `A` of the `(n+1)`-st power of the defining ideal is carried by `g` into
the `n`-th power of the maximal ideal of `W`. -/
private theorem stageLe {I : Ideal R} (hRadic : IsAdic I) (f : R →+* A) (g : A →+* W)
    (hgle : (I.map f).map g ≤ IsLocalRing.maximalIdeal W) (n : ℕ) :
    extendedIdeal f (powIndex hRadic n) ≤
      Ideal.comap g (IsLocalRing.maximalIdeal W ^ n) := by
  refine Ideal.map_le_iff_le_comap.mp ?_
  have h1 : I.map (g.comp f) ≤ IsLocalRing.maximalIdeal W := by rwa [← Ideal.map_map]
  calc ((I ^ (n + 1)).map f).map g = (I ^ (n + 1)).map (g.comp f) := by rw [Ideal.map_map]
    _ = (I.map (g.comp f)) ^ (n + 1) := Ideal.map_pow _ _ _
    _ ≤ IsLocalRing.maximalIdeal W ^ (n + 1) := pow_le_pow_left' h1 _
    _ ≤ IsLocalRing.maximalIdeal W ^ n := Ideal.pow_le_pow_right (Nat.le_succ n)

/-- The `n`-th stage of a ring map to a local ring whose maximal ideal receives the defining
ideal of the source. -/
private def stageHom {I : Ideal R} (hRadic : IsAdic I) (f : R →+* A) (g : A →+* W)
    (hgle : (I.map f).map g ≤ IsLocalRing.maximalIdeal W) (n : ℕ) :
    CompletionOver f →+* W ⧸ IsLocalRing.maximalIdeal W ^ n :=
  (Ideal.quotientMap (IsLocalRing.maximalIdeal W ^ n) g
    (stageLe hRadic f g hgle n)).comp (projection f (powIndex hRadic n))

private theorem stageHom_apply {I : Ideal R} (hRadic : IsAdic I) (f : R →+* A) (g : A →+* W)
    (hgle : (I.map f).map g ≤ IsLocalRing.maximalIdeal W) (n : ℕ) (x : CompletionOver f) :
    stageHom hRadic f g hgle n x =
      Ideal.quotientMap (IsLocalRing.maximalIdeal W ^ n) g (stageLe hRadic f g hgle n)
        (projection f (powIndex hRadic n) x) := rfl

/-- A ring map `g : A → W` to a local ring complete for its maximal-adic topology which carries
the defining ideal of the source `R` of `f : R → A` into the maximal ideal extends, continuously
and uniquely, to the completion `A^∧` of `A` over `R`.

The stages `A ⧸ I^{n+1}A → W ⧸ m_W^n` of `g` form a compatible family, which the universal
property of `m_W`-adic completeness lifts to `A^∧ → W`; continuity holds because the preimage
of `m_W^n` contains the open kernel of the projection of `A^∧` to its `I^{n+1}`-stage. -/
theorem exists_continuous_ringHom_completionOver [TopologicalSpace W] [IsTopologicalRing W]
    [IsAdicComplete (IsLocalRing.maximalIdeal W) W] {I : Ideal R} (hRadic : IsAdic I)
    (hWadic : IsAdic (IsLocalRing.maximalIdeal W)) (f : R →+* A) (g : A →+* W)
    (hgle : (I.map f).map g ≤ IsLocalRing.maximalIdeal W) :
    ∃ G : CompletionOver f →+* W, Continuous G ∧ G.comp (ofTarget f) = g := by
  have hcompat : ∀ {m n : ℕ} (hle : m ≤ n),
      (Ideal.Quotient.factorPow (IsLocalRing.maximalIdeal W) hle).comp
        (stageHom hRadic f g hgle n) = stageHom hRadic f g hgle m := by
    intro m n hle
    have hJ : ((powIndex hRadic n).1 : Ideal R) ≤ (powIndex hRadic m).1 :=
      Ideal.pow_le_pow_right (Nat.succ_le_succ hle)
    ext x
    have hx : transitionMap f hJ (projection f (powIndex hRadic n) x) =
        projection f (powIndex hRadic m) x := x.2 _ _ hJ
    rw [RingHom.comp_apply, stageHom_apply, stageHom_apply, ← hx]
    obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (projection f (powIndex hRadic n) x)
    rw [← ha]
    rw [Ideal.quotientMap_mk, Ideal.Quotient.factor_mk]
    change Ideal.Quotient.mk _ (g a) = _
    rw [Ideal.Quotient.factor_mk, Ideal.quotientMap_mk]
  set G := IsAdicComplete.liftRingHom (IsLocalRing.maximalIdeal W)
    (stageHom hRadic f g hgle) hcompat with hGdef
  refine ⟨G, ?_, ?_⟩
  · refine continuous_of_continuousAt_zero G ?_
    rw [ContinuousAt, map_zero]
    refine hWadic.hasBasis_nhds_zero.tendsto_right_iff.mpr fun n _ => ?_
    refine Filter.eventually_of_mem
      ((isOpen_ker_projection f (powIndex hRadic n)).mem_nhds
        (Ideal.zero_mem (RingHom.ker (projection f (powIndex hRadic n))))) fun x hx => ?_
    have hx0 : projection f (powIndex hRadic n) x = 0 := hx
    have hmk := IsAdicComplete.mk_liftRingHom (IsLocalRing.maximalIdeal W)
      (stageHom hRadic f g hgle) hcompat n x
    rw [show stageHom hRadic f g hgle n x = 0 by
      rw [stageHom_apply, hx0, map_zero]] at hmk
    exact Ideal.Quotient.eq_zero_iff_mem.mp hmk
  · have hfam : ∀ {m n : ℕ} (hle : m ≤ n),
        (Ideal.Quotient.factorPow (IsLocalRing.maximalIdeal W) hle).comp
          ((Ideal.Quotient.mk (IsLocalRing.maximalIdeal W ^ n)).comp g) =
        (Ideal.Quotient.mk (IsLocalRing.maximalIdeal W ^ m)).comp g := by
      intro m n hle
      ext a
      exact Ideal.Quotient.factor_mk (Ideal.pow_le_pow_right hle) (g a)
    rw [IsAdicComplete.eq_liftRingHom (IsLocalRing.maximalIdeal W) _ hfam g (fun _ => rfl)]
    refine IsAdicComplete.eq_liftRingHom (IsLocalRing.maximalIdeal W) _ hfam _ fun n => ?_
    ext a
    have h1 := IsAdicComplete.mk_liftRingHom (IsLocalRing.maximalIdeal W)
      (stageHom hRadic f g hgle) hcompat n (ofTarget f a)
    rw [RingHom.comp_apply, RingHom.comp_apply, ← hGdef] at *
    rw [h1, stageHom_apply, projection_ofTarget, Ideal.quotientMap_mk]
    rfl

end Lift

section Geometry

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.FormalSpace

namespace AlgebraicGeometry.FormalSpace

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A covering sieve of an object of the big fppf category over `S` whose underlying scheme has
a point has a member whose own underlying scheme has a point: a covering sieve meets every
prescribed point of its base. -/
private theorem exists_nonempty_mem_of_mem_topology {T : BigFppfOver B S hS}
    (t : (BigFppfOver.toScheme B S hS).obj T) {Sv : Sieve T}
    (hSv : Sv ∈ BigFppfOver.topology B S hS T) :
    ∃ (W : BigFppfOver B S hS) (g : W ⟶ T), Sv g ∧
      Nonempty ((BigFppfOver.toScheme B S hS).obj W) := by
  obtain ⟨V, g, hg, hmem⟩ := BigFppfOver.exists_mem_range_of_mem_topology B S hS hSv t
  obtain ⟨w, -⟩ := hmem
  exact ⟨V, g, hg, ⟨w⟩⟩

/-- An object of the big fppf category over `S` whose sheafified representable has a section
over an object with a point has itself a point: the big fppf topology is subcanonical, so the
section is a morphism of the site. -/
private theorem nonempty_of_section_sheafifiedYoneda {U T : BigFppfOver B S hS}
    (t : (BigFppfOver.toScheme B S hS).obj T)
    (s : ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj U).obj.obj
      (Opposite.op T)) :
    Nonempty ((BigFppfOver.toScheme B S hS).obj U) := by
  let _ : B.topology.Subcanonical := BigFppfSite.subcanonical_topology B
  let _ : (BigFppfOver.topology B S hS).Subcanonical := inferInstance
  have hmor : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj T ⟶
      (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj U :=
    (Sheaf.sectionEquiv (BigFppfOver.topology B S hS)).symm s
  have hg : T ⟶ U :=
    Sheaf.representingHom (C := BigFppfOver B S hS) (J := BigFppfOver.topology B S hS) hmor
  exact ⟨((BigFppfOver.toScheme B S hS).map hg).base t⟩

/-- The formal spectrum of a local ring carrying its maximal-adic topology has a point: the
quotient stage attached to the maximal ideal is the spectrum of the residue field, a field
spectrum of the site over `S`, and the inclusion of that stage is a section over it. -/
private theorem nonempty_section_stage
    {R : Type u} [CommRing R] [TopologicalSpace R] (D : QuotientSystem B S hS R)
    (J : { I : Ideal R // TopologicalRing.IsWeakIdealOfDefinition I }) :
    Nonempty ((formalSpectrum D).obj.obj
      (Opposite.op ((BigAffineFppf.inclusion B S hS).obj (D.stage J)))) :=
  ⟨Sheaf.sectionEquiv (C := BigFppfOver B S hS)
    (X := (BigAffineFppf.inclusion B S hS).obj (D.stage J)) (F := formalSpectrum D)
    (BigFppfOver.topology B S hS) (formalSpectrumInclusion D J)⟩

/-- The formal spectrum of a local ring carrying its maximal-adic topology has a point: the
quotient stage attached to the maximal ideal is the spectrum of the residue field, which is a
field spectrum of the site over `S`, and the inclusion of that stage is a section over it. -/
private theorem nonempty_pointsULift_formalSpectrum
    {R : Type u} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [IsLocalRing R]
    (hRadic : _root_.IsAdic (IsLocalRing.maximalIdeal R)) (D : QuotientSystem B S hS R) :
    Nonempty (Space.pointsULift.{u + 1} B S hS (formalSpectrum D).obj) := by
  classical
  let J : { I : Ideal R // TopologicalRing.IsWeakIdealOfDefinition I } :=
    ⟨IsLocalRing.maximalIdeal R, TopologicalRing.isWeakIdealOfDefinition_of_isAdic hRadic⟩
  obtain ⟨s⟩ := nonempty_section_stage B S hS D J
  exact ⟨Space.FieldValuedPointULift.class B S hS (formalSpectrum D).obj
    { carrier := R ⧸ IsLocalRing.maximalIdeal R
      field := Ideal.Quotient.field (IsLocalRing.maximalIdeal R)
      contained := D.inSite J
      toBase := D.overS J
      value := s }⟩

attribute [local instance] sheaf_hasColimits

/-- A sheaf with a point which is covered by a family of morphisms has a member of that family
with a section over an object of the site whose underlying scheme has a point.

A point of the sheaf is a section over a field spectrum; Stacks 00WI puts that section, locally,
in the image of a single member of the family, and the covering sieve witnessing this has a
member whose underlying scheme meets the closed point of the field spectrum. -/
private theorem exists_section_of_pointsULift_of_isLocallySurjective
    {Z : FppfSheaf B S hS} {ι : Type (u + 1)} {V : ι → FppfSheaf B S hS} (a : ∀ i, V i ⟶ Z)
    (ha : Sheaf.IsLocallySurjective (Limits.Sigma.desc a))
    (hZ : Nonempty (Space.pointsULift.{u + 1} B S hS Z.obj)) :
    ∃ (i : ι) (W : BigFppfOver B S hS), Nonempty ((BigFppfOver.toScheme B S hS).obj W) ∧
      Nonempty ((V i).obj.obj (Opposite.op W)) := by
  obtain ⟨z⟩ := hZ
  induction z using Quot.ind with
  | _ q => ?_
  obtain ⟨Sv, hSv, hcov⟩ := (Sheaf.isLocallySurjective_sigmaDesc_iff a).1 ha q.value
  obtain ⟨W, g, hg, hWne⟩ := exists_nonempty_mem_of_mem_topology B S hS
    (T := q.siteObject B S hS Z.obj) (IsLocalRing.closedPoint q.carrier) hSv
  obtain ⟨i, t, -⟩ := hcov g hg
  exact ⟨i, W, hWne, ⟨t⟩⟩

/-- A quotient system over `S` whose formal spectrum has a section over an object of the site
whose underlying scheme has a point is a system on a nontrivial ring.

The quotient stages cover the formal spectrum, so the section lies locally in one of them; that
stage is the spectrum of a quotient of the ring and has a point, hence the quotient — and so the
ring — is nontrivial. -/
private theorem nontrivial_of_section_formalSpectrum
    {A : Type u} [CommRing A] [TopologicalSpace A] (E : QuotientSystem B S hS A)
    {T : BigFppfOver B S hS} (t : (BigFppfOver.toScheme B S hS).obj T)
    (s : (formalSpectrum E).obj.obj (Opposite.op T)) : Nontrivial A := by
  classical
  set ι := ULift.{u + 1, u}
    (OrderDual { I : Ideal A // TopologicalRing.IsWeakIdealOfDefinition I }) with hι
  set G : ι → FppfSheaf B S hS := fun j => (formalSpectrumDiagram E).obj j.down with hG
  set c : ∀ j, G j ⟶ formalSpectrum E := fun j => formalSpectrumInclusion E j.down with hc
  have hls : Sheaf.IsLocallySurjective (Limits.Sigma.desc c) := by
    rw [Sheaf.isLocallySurjective_iff_epi]
    refine ⟨fun {Q} f₁ f₂ h => Limits.colimit.hom_ext fun K => ?_⟩
    have hK : c (ULift.up K) ≫ f₁ = c (ULift.up K) ≫ f₂ := by
      rw [← Limits.Sigma.ι_comp_desc c (ULift.up K), Category.assoc, Category.assoc, h]
    exact hK
  obtain ⟨Sv, hSv, hcov⟩ := (Sheaf.isLocallySurjective_sigmaDesc_iff c).1 hls s
  obtain ⟨W, g, hg, ⟨w⟩⟩ := exists_nonempty_mem_of_mem_topology B S hS t hSv
  obtain ⟨j, x, -⟩ := hcov g hg
  obtain ⟨p⟩ := nonempty_of_section_sheafifiedYoneda B S hS
    (U := (BigAffineFppf.inclusion B S hS).obj (E.stage j.down)) w x
  have hp : Nontrivial (A ⧸ (j.down : { I : Ideal A //
      TopologicalRing.IsWeakIdealOfDefinition I }).1) := PrimeSpectrum.nontrivial p
  refine ⟨?_⟩
  obtain ⟨x, y, hxy⟩ := hp.exists_pair_ne
  obtain ⟨x', rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨y', rfl⟩ := Ideal.Quotient.mk_surjective y
  exact ⟨x', y', fun h => hxy (congrArg _ h)⟩

end AlgebraicGeometry.FormalSpace

end Geometry

section Nontriviality

open AlgebraicGeometry AlgebraicGeometry.FormalSpace

/-- A ring map out of a ring with the `I`-adic topology whose extension of `I` is everything has
a trivial completion: every quotient stage is then trivial, and the completion is a subring of
their product. -/
theorem map_ne_top_of_nontrivial_completionOver
    {R : Type u} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] {A : Type u}
    [CommRing A] {I : Ideal R} (hRadic : _root_.IsAdic I) (f : R →+* A)
    (h : Nontrivial (TopologicalRing.CompletionOver f)) : I.map f ≠ ⊤ := by
  intro htop
  have hstage : ∀ J : TopologicalRing.WeakIdealOfDefinitionIndex R,
      Subsingleton (A ⧸ TopologicalRing.extendedIdeal f J) := by
    intro J
    obtain ⟨n, hn⟩ := exists_pow_le_of_isWeakIdealOfDefinition hRadic J
    have htopJ : TopologicalRing.extendedIdeal f J = ⊤ := by
      refine top_le_iff.mp ?_
      calc (⊤ : Ideal A) = (I.map f) ^ n := by rw [htop, Ideal.top_pow]
        _ = (I ^ n).map f := (Ideal.map_pow _ _ _).symm
        _ ≤ TopologicalRing.extendedIdeal f J := Ideal.map_mono hn
    rw [htopJ]
    exact Ideal.Quotient.subsingleton_iff.mpr rfl
  have hsub : Subsingleton (TopologicalRing.CompletionOver f) :=
    ⟨fun x y => Subtype.ext (funext fun J => (hstage J).elim _ _)⟩
  obtain ⟨x, y, hxy⟩ := h.exists_pair_ne
  exact hxy (hsub.elim x y)

end Nontriviality

section Main

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry.FormalSpace

attribute [local instance] sheaf_hasColimits

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Two continuous maps over the base with the same underlying ring map are equal. -/
private theorem continuousHom_ext {A C : Type u} [CommRing A] [CommRing C] [TopologicalSpace A]
    [TopologicalSpace C] {D : QuotientSystem B S hS A} {E : QuotientSystem B S hS C}
    {g g' : ContinuousHom D E} (h : g.toRingHom = g'.toRingHom) : g = g' := by
  cases g
  cases g'
  cases h
  rfl

/-- **The essential-surjectivity clause of Stacks 0AN8.** For a McQuillan affine formal
algebraic space `Spf R` over `S`, every affine formal algebraic space `V` over `S` carrying a
morphism `V ⟶ Spf R` which is representable by algebraic spaces and étale is `Spf` of the
completion `A^∧` of an étale `R`-algebra `A`, compatibly with the morphisms to `Spf R`.

This is the half of the equivalence of categories of Stacks 0AN8 which this library does not
carry: the two declarations tagged with Stacks 0AN8,
`TopologicalRing.etale_quotientMap_weakIdealOfDefinition` and
`TopologicalRing.CompletionOver.etale_quotientMap_canonicalMap`, carry only the first step of
its proof and their tag comments exclude essential surjectivity by name. The other half, full
faithfulness of `Spf`, is Stacks 0AN0 and is available as
`AlgebraicGeometry.FormalSpace.existsUnique_continuousHom_formalSpectrumMap_eq`. -/
abbrev IsEssentiallySurjectiveSpf : Prop :=
  ∀ (R : Type u) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [IsLinearTopology R R]
    (hR : TopologicalRing.IsWeaklyAdmissible R) (_hRcard : #R < B.cutoff)
    (D : QuotientSystem B S hS R)
    (V : FppfSheaf B S hS) (v : V ⟶ formalSpectrum D),
    IsAffineFormalAlgebraicSpace B S hS V → IsRepresentableEtale B S hS v →
      ∃ (A : Type u) (_ : CommRing A) (_ : Algebra R A) (_ : Algebra.Etale R A)
        (E : QuotientSystem B S hS (TopologicalRing.CompletionOver (algebraMap R A)))
        (c : ContinuousHom D E) (ε : V ≅ formalSpectrum E),
        c.toRingHom = TopologicalRing.CompletionOver.canonicalMap (algebraMap R A) ∧
          ε.hom ≫ formalSpectrumMap hR c = v

end AlgebraicGeometry.FormalSpace

end Main

end
