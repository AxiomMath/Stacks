module

public import Mathlib.CategoryTheory.Functor.Derived.RightDerivedCommShift
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.RingTheory.Finiteness.Cardinality
public import Mathlib.RingTheory.Finiteness.Finsupp
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPushforwardModules.HasSheafComposeForget
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSite
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorInjective
public import StacksFrontier.Algebra.Homology.SpectralSequence.AbutsTo
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.FiniteTorDimension
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.InverseImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.ArithmeticFrobeniusInverse
public import StacksFrontier.AlgebraicGeometry.Morphisms.Projective.Basic
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.Defs
public import StacksFrontier.Homology.Perfect.FiniteTorDimension
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPushforwardModules.HasSheafComposeForget

/-!
# Perfectness of the étale cohomology of a projective curve

Let `k` be a field, let `X` be a projective curve over `k`, let `Λ` be a finite ring and let `K`
be an object of `D_ctf(X_étale, Λ)`. Then the derived global sections `RΓ(X_k̄, K)` of the
restriction of `K` to the geometric fibre `X_k̄ = X ×_{Spec k} Spec k̄` form a perfect complex of
`Λ`-modules. This is proved here as
`Stacks.EtaleCohomology.CurveGlobalSections.isPerfect`, from the three inputs the source uses:
the hypercohomology spectral sequence `H^i(X_k̄, H^j(K)) ⇒ H^{i+j}(RΓ(X_k̄, K))`, the finiteness
of the étale cohomology of a constructible sheaf, and the projection formula
`N ⊗ᴸ[Λ] RΓ(X_k̄, K) = RΓ(X_k̄, N ⊗ᴸ[Λ] K)`.

## Main definitions

* `Stacks.EtaleCohomology.SmallEtaleModuleSheaf` and
  `Stacks.EtaleCohomology.smallEtaleModulePullback` — sheaves of `Λ`-modules on the small étale
  site of an object of a big étale site, and their inverse image along a morphism.
* `Stacks.EtaleCohomology.smallEtaleModuleGlobalSections`,
  `Stacks.EtaleCohomology.smallEtaleModuleDerivedGlobalSections` and
  `Stacks.EtaleCohomology.smallEtaleModuleCohomology` — global sections of a sheaf of
  `Λ`-modules on a small étale site, their right derived functor on bounded below derived
  categories, and the resulting étale cohomology modules.
* `Stacks.EtaleCohomology.HasHypercohomologySpectralSequence` — the hypercohomology spectral
  sequence of a bounded below complex of sheaves of `Λ`-modules on a small étale site: a
  spectral sequence whose second page is `H^i(Z, H^j(M))` and which abuts to
  `H^{i+j}(RΓ(Z, M))`.
* `Stacks.EtaleCohomology.HasFiniteConstructibleCohomology` — finiteness of every étale
  cohomology module of every constructible sheaf of `Λ`-modules.
* `Stacks.EtaleCohomology.HasFiniteEtaleCohomologicalDimension` — vanishing of étale cohomology
  outside a range of degrees independent of the sheaf.
* `Stacks.EtaleCohomology.HasConstructibleDerivedPullback` — constructibility of the cohomology
  sheaves is inherited by the derived inverse image.
* `Stacks.EtaleCohomology.CurveGlobalSections.HasGeometricTwisting` — the projection formula
  for the twists `N ⊗ᴸ[Λ] K` of a constructible complex of finite Tor dimension by a right
  `Λ`-module, together with the range of degrees in which the cohomology sheaves of those can be
  nonzero.

## Main results

* `Stacks.EtaleCohomology.isZero_smallEtaleModuleCohomology_of_isZero` — the étale cohomology
  of a sheaf which is zero is zero.
* `Stacks.EtaleCohomology.isZero_homology_of_abutsTo` and
  `Stacks.EtaleCohomology.finite_homology_of_abutsTo` — the two consequences of convergence of a
  spectral sequence of `Λ`-modules used below: a graded object it abuts to vanishes, resp. is
  finite, in a degree in which the starting page does.
* `Stacks.EtaleCohomology.CurveGlobalSections.exists_isZero_homology` and
  `Stacks.EtaleCohomology.CurveGlobalSections.exists_isZero_homology_of_hasGeometricTwisting` —
  `RΓ(X_k̄, K)` is bounded.
* `Stacks.EtaleCohomology.CurveGlobalSections.finite_homology` — its cohomology modules are
  finite.
* `Stacks.EtaleCohomology.CurveGlobalSections.hasFiniteTorDimension` — it has finite Tor
  dimension.
* `Stacks.EtaleCohomology.CurveGlobalSections.isPerfect` — it is perfect, by the criterion of
  Tag 03TO.
* `Stacks.EtaleCohomology.hasConstructibleDerivedPullback` — the carried constructibility of a
  derived inverse image, discharged in the module universe in which Tag 095Y is available.

## Implementation notes

The curve lives in a big étale site `B`, the coefficients are sheaves of `Λ`-modules on the
small étale site of an object of `B`, and `D_ctf(X_étale, Λ)` is
`Stacks.EtaleCohomology.ConstructibleFiniteTorDerivedCategory`, which forces `Λ` commutative; a
finite commutative ring is Noetherian, so no hypothesis beyond finiteness is added. Derived
global sections are the right derived functor of sections over the final object of the small
étale site, in the same idiom, so no comparison between two étale sites is needed.

The geometric fibre is supplied as an object `Y` of `B` together with an isomorphism of `Y` with
`Stacks.Frobenius.fieldBaseChange` over `X`, which pins it down; likewise the restriction of `K`
to `Y` is supplied as a bounded below object `Kbar` together with an isomorphism with the
derived inverse image of `K`. Neither is free.

The inputs of the source are carried as hypotheses, each quantified over all the objects it
speaks about rather than over the single complex in the conclusion:

* the hypercohomology spectral sequence, quantified over every bounded below complex of sheaves
  of `Λ`-modules, resp. of abelian groups, on the geometric fibre. Its library form,
  `Stacks.Cohomology.FilteredComplex.exists_boundedBelowHypercohomologySpectralSequence`, is
  stated for sheaves of modules on a ringed space, with no comparison to the small étale site
  available;
* finiteness of the étale cohomology of a constructible sheaf, quantified over every
  constructible sheaf of `Λ`-modules on the geometric fibre;
* vanishing of the étale cohomology of an arbitrary sheaf outside a range of degrees, quantified
  over every sheaf of abelian groups, resp. of `Λ`-modules, on the geometric fibre. The library's
  `AlgebraicGeometry.Scheme.etaleCohomologicalDimension` is stated for `Scheme.smallEtaleTopology`
  with coefficients in abelian groups, again with no comparison to this idiom;
* constructibility of a derived inverse image, quantified over every morphism of the big étale
  site and every complex with constructible cohomology sheaves. This one is available, as
  `Stacks.EtaleCohomology.isConstructible_derivedPullback`, whenever the universe of the module
  sections contains the universe of the small étale sites, and
  `Stacks.EtaleCohomology.hasConstructibleDerivedPullback` discharges it there; the statements
  below leave the module universe free, so they carry it;
* the projection formula with the Tor window, quantified over every object of
  `D_ctf(X_étale, Λ)`, every bounded below representative of its restriction to the geometric
  fibre and every right `Λ`-module.

The three claims of the source — boundedness, finiteness of the cohomology modules and finite
Tor dimension — are *derived* from those inputs, and perfectness then follows from the criterion
of Tag 03TO. The curve and projectivity hypotheses do not enter the derivation: they are what
makes the carried inputs true, the source deducing from them the finite cohomological dimension
of `X_k̄` and the finiteness of the cohomology of a constructible sheaf on it.

The twists `N ⊗ᴸ[Λ] K` are complexes of sheaves of abelian groups, so their derived global
sections are taken with coefficient ring `ℤ`; the spectral sequence and the cohomological
dimension are therefore carried both for `Λ` and for `ℤ`. The derived tensor product of a right
`Λ`-module with an object of `D(Λ)` is the parameter
`StacksDraft.Perfect.BalancedDerivedTensoring`, carried here because the projection formula in
`hTwisting` is stated relative to it. Tags 03TN and 03TO are also available parameter-free, at
the term `StacksDraft.Perfect.balancedDerivedTensoring`, and
`StacksDraft.Perfect.hasFiniteTorDimension_iff_of_balancedDerivedTensoring` shows that the
reading of finite Tor dimension does not depend on which parameter is used.

The ring, module and derived-category universes are independent.

## References

* [Stacks Project, Tag 03TV](https://stacks.math.columbia.edu/tag/03TV)
* [Stacks Project, Tag 03TO](https://stacks.math.columbia.edu/tag/03TO)
* [Stacks Project, Tag 03TN](https://stacks.math.columbia.edu/tag/03TN)
* [Stacks Project, Tag 03TQ](https://stacks.math.columbia.edu/tag/03TQ)
* [Stacks Project, Tag 03SB](https://stacks.math.columbia.edu/tag/03SB)
* [Stacks Project, Tag 0BKM](https://stacks.math.columbia.edu/tag/0BKM)
* [Stacks Project, Tag 095Y](https://stacks.math.columbia.edu/tag/095Y)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.SpectralSequence AlgebraicGeometry
open Opposite

universe u w r d

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

/-! ### Two consequences of the convergence of a spectral sequence of modules -/

section Abutment

variable {Λ : Type r} [Ring Λ]

/-- The cohomology of a complex of `Λ`-modules over a finite ring is finite in a degree whose
term is finite: it is a quotient of a submodule of that term. -/
private lemma finite_homologicalComplex_homology [Finite Λ] {ι : Type*} {c : ComplexShape ι}
    (K : HomologicalComplex (ModuleCat.{w} Λ) c) (j : ι) (h : Module.Finite Λ (K.X j)) :
    Module.Finite Λ (K.homology j) := by
  rw [Module.finite_iff_finite] at h ⊢
  have hcycles : Finite (K.cycles j) :=
    Finite.of_injective _ ((ModuleCat.mono_iff_injective (K.iCycles j)).mp inferInstance)
  exact Finite.of_surjective _ ((ModuleCat.epi_iff_surjective (K.homologyπ j)).mp inferInstance)

/-- Every page of a spectral sequence of modules over a finite ring is finite at a position at
which the starting page is: the next page is the homology of the current one. -/
private lemma finite_page [Finite Λ] {r₀ : ℤ}
    (E : CohomologicalSpectralSequence (ModuleCat.{w} Λ) r₀) (pq : ℤ × ℤ)
    (h : Module.Finite Λ ((E.page r₀ le_rfl).X pq)) (s : ℤ) (hs : r₀ ≤ s) :
    Module.Finite Λ ((E.page s hs).X pq) := by
  induction s, hs using Int.leInduction with
  | base => exact h
  | succ m hm ih =>
    have := finite_homologicalComplex_homology (E.page m hm) pq ih
    exact Module.Finite.equiv (E.iso m (m + 1) pq rfl hm).toLinearEquiv

/-- The infinity page of a spectral sequence of modules over a finite ring is finite at a
position at which the starting page is and at which the pages stabilise. -/
private lemma finite_pageInfinity [Finite Λ] {r₀ : ℤ}
    (E : CohomologicalSpectralSequence (ModuleCat.{w} Λ) r₀) (pq : ℤ × ℤ)
    [E.HasPageInfinityAt pq] (h : Module.Finite Λ ((E.page r₀ le_rfl).X pq)) :
    Module.Finite Λ (E.pageInfinity pq) := by
  have hmono : E.HasEdgeMonoAtFrom pq (E.rMin pq) := ⟨E.rToMin_LE_rMin pq⟩
  have hepi : E.HasEdgeEpiAtFrom pq (E.rMin pq) := ⟨E.rFromMin_LE_rMin pq⟩
  have := finite_page E pq h (E.rMin pq) (E.LE_rMin pq)
  exact Module.Finite.equiv (E.pageInfinityIso pq (E.rMin pq)).symm.toLinearEquiv

/-- An object whose largest subobject is its smallest one is zero. -/
private lemma isZero_of_top_eq_bot {C : Type*} [Category* C] [Abelian C] {Z : C}
    (h : (⊤ : Subobject Z) = ⊥) : IsZero Z :=
  IsZero.of_iso (isZero_zero C)
    ((asIso (⊤ : Subobject Z).arrow).symm ≪≫ Subobject.underlying.mapIso (eqToIso h) ≪≫
      Subobject.botCoeIsoZero)

/-- A finite extension of a module over a finite ring by a finite one is finite. -/
private lemma finite_of_mono_cokernel {A A' : ModuleCat.{w} Λ} (i : A ⟶ A') [Mono i]
    (hA : Module.Finite Λ A) (hQ : Module.Finite Λ ((cokernel i : ModuleCat.{w} Λ))) :
    Module.Finite Λ A' := by
  have := hA
  have := hQ
  have hex : (ShortComplex.mk i (cokernel.π i) (cokernel.condition i)).Exact :=
    ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel i)
  rw [ShortComplex.moduleCat_exact_iff] at hex
  refine Module.Finite.of_exact (f := i.hom) (g := (cokernel.π i).hom) (fun x => ?_) ?_
  · refine ⟨fun hx => hex x hx, ?_⟩
    rintro ⟨y, rfl⟩
    exact congrArg (fun φ : A ⟶ cokernel i => φ y) (cokernel.condition i)
  · exact (ModuleCat.epi_iff_surjective (cokernel.π i)).mp inferInstance

/-- **A graded object vanishes in a degree in which the starting page of a spectral sequence
abutting to it vanishes.** The infinity page then vanishes in that total degree, so every step
of the finite filtration of the abutment is an equality, and the filtration runs from the whole
object to the zero subobject. -/
theorem isZero_homology_of_abutsTo {C : Type*} [Category* C] [Abelian C] {r₀ : ℤ}
    (E : CohomologicalSpectralSequence C r₀) (H : ℤ → C) (hE : SpectralSequence.AbutsTo E H)
    (n : ℤ) (hz : ∀ p : ℤ, IsZero ((E.page r₀ le_rfl).X (p, n - p))) : IsZero (H n) := by
  obtain ⟨hinf, F, hF, hbounds, hgr⟩ := hE
  have hinfzero : ∀ p : ℤ, IsZero (E.pageInfinity (p, n - p)) := by
    intro p
    have hpi := hinf p (n - p)
    have hmono : E.HasEdgeMonoAtFrom (p, n - p) (E.rMin (p, n - p)) := ⟨E.rToMin_LE_rMin _⟩
    have hepi : E.HasEdgeEpiAtFrom (p, n - p) (E.rMin (p, n - p)) := ⟨E.rFromMin_LE_rMin _⟩
    exact IsZero.of_iso (E.isZero_page_of_le le_rfl (p, n - p) (hz p) (E.rMin (p, n - p))
        (E.LE_rMin _) (E.LE_rMin _))
      (E.pageInfinityIso (p, n - p) (E.rMin (p, n - p)))
  have hstep₀ : ∀ m p q : ℤ, m = p + q → IsZero (E.pageInfinity (p, q)) →
      F m (p + 1) = F m p := by
    intro m p q hm hzz
    subst hm
    exact Subobject.eq_of_isZero_cokernel_ofLE (hF (p + q) (by omega))
      (hzz.of_iso (hgr p q).some.symm)
  have hstep : ∀ p : ℤ, F n (p + 1) = F n p := fun p =>
    hstep₀ n p (n - p) (by omega) (hinfzero p)
  obtain ⟨a, b, hab, hta, hbb⟩ := hbounds n
  have hconst : ∀ p : ℤ, a ≤ p → F n p = F n a := by
    intro p hp
    induction p, hp using Int.leInduction with
    | base => rfl
    | succ m hm ih => rw [hstep m, ih]
  exact isZero_of_top_eq_bot (by rw [← hta, ← hbb, hconst b hab])

/-- **A graded object of finite modules is finite in a degree in which the starting page of a
spectral sequence abutting to it is finite.** The infinity page is then finite in that total
degree, and the abutment is a finite iterated extension of those terms. -/
theorem finite_homology_of_abutsTo [Finite Λ] {r₀ : ℤ}
    (E : CohomologicalSpectralSequence (ModuleCat.{w} Λ) r₀) (H : ℤ → ModuleCat.{w} Λ)
    (hE : SpectralSequence.AbutsTo E H) (n : ℤ)
    (hfin : ∀ p : ℤ, Module.Finite Λ ((E.page r₀ le_rfl).X (p, n - p))) :
    Module.Finite Λ (H n) := by
  obtain ⟨hinf, F, hF, hbounds, hgr⟩ := hE
  have hinffin : ∀ p : ℤ, Module.Finite Λ (E.pageInfinity (p, n - p)) := by
    intro p
    have hpi := hinf p (n - p)
    exact finite_pageInfinity E (p, n - p) (hfin p)
  have hgrfin₀ : ∀ m p q : ℤ, m = p + q → Module.Finite Λ (E.pageInfinity (p, q)) →
      ∀ h : F m (p + 1) ≤ F m p,
        Module.Finite Λ ((cokernel (Subobject.ofLE (F m (p + 1)) (F m p) h) :
          ModuleCat.{w} Λ)) := by
    intro m p q hm hff h
    subst hm
    exact Module.Finite.equiv (M := E.pageInfinity (p, q)) (hgr p q).some.toLinearEquiv
  have hgrfin : ∀ (p q : ℤ), q = p + 1 → ∀ h : F n q ≤ F n p,
      Module.Finite Λ ((cokernel (Subobject.ofLE (F n q) (F n p) h) : ModuleCat.{w} Λ)) := by
    intro p q hq h
    subst hq
    exact hgrfin₀ n p (n - p) (by omega) (hinffin p) h
  obtain ⟨a, b, hab, hta, hbb⟩ := hbounds n
  have hbot : Module.Finite Λ ((F n b : ModuleCat.{w} Λ)) := by
    rw [Module.finite_iff_finite]
    have : Subsingleton ((F n b : ModuleCat.{w} Λ)) :=
      ModuleCat.isZero_iff_subsingleton.mp (IsZero.of_iso (isZero_zero _)
        (Subobject.underlying.mapIso (eqToIso hbb) ≪≫ Subobject.botCoeIsoZero))
    infer_instance
  have hdown : ∀ p : ℤ, p ≤ b → Module.Finite Λ ((F n p : ModuleCat.{w} Λ)) := by
    intro p hp
    induction p, hp using Int.leInductionDown with
    | base => exact hbot
    | pred m hm ih =>
      exact finite_of_mono_cokernel _ ih (hgrfin (m - 1) m (by omega) (hF n (by omega)))
  have htop := hdown a hab
  rw [hta] at htop
  exact Module.Finite.equiv (M := ((⊤ : Subobject (H n)) : ModuleCat.{w} Λ))
    (asIso (⊤ : Subobject (H n)).arrow).toLinearEquiv

end Abutment

/-! ### Derived global sections on a small étale site -/

section Sections

variable (B : BigEtaleSite.{u}) (Λ : Type r) [Ring Λ]

/-- Sheaves of `Λ`-modules on the small étale site of an object of a big étale site. -/
abbrev SmallEtaleModuleSheaf (Z : B.Scheme) : Type _ :=
  Sheaf (SmallEtale.topology B Z.obj Z.property) (ModuleCat.{w} Λ)

/-- Global sections of a sheaf of `Λ`-modules on the small étale site of `Z`: its sections over
the final object `Z / Z` of that site. -/
abbrev smallEtaleModuleGlobalSections (Z : B.Scheme) :
    SmallEtaleModuleSheaf.{u, w, r} B Λ Z ⥤ ModuleCat.{w} Λ :=
  (sheafSections (SmallEtale.topology B Z.obj Z.property) (ModuleCat.{w} Λ)).obj
    (op (SmallEtale.final B Z.obj Z.property))

/-- Global sections on a small étale site are additive in the sheaf. -/
instance smallEtaleModuleGlobalSections_additive (Z : B.Scheme) :
    (smallEtaleModuleGlobalSections.{u, w, r} B Λ Z).Additive where
  map_add := by intros; rfl

variable [∀ Z : B.Scheme, HasSheafify (SmallEtale.topology B Z.obj Z.property) (ModuleCat.{w} Λ)]
  [∀ Z : B.Scheme, EnoughInjectives (SmallEtaleModuleSheaf.{u, w, r} B Λ Z)]

/-- The derived global sections `RΓ(Z, -)` of sheaves of `Λ`-modules on the small étale site of
`Z`, on bounded below derived categories. -/
abbrev smallEtaleModuleDerivedGlobalSections (Z : B.Scheme) :
    DerivedCategory.Plus (SmallEtaleModuleSheaf.{u, w, r} B Λ Z) ⥤
      DerivedCategory.Plus (ModuleCat.{w} Λ) :=
  (smallEtaleModuleGlobalSections.{u, w, r} B Λ Z).rightDerivedFunctorPlus

/-- The étale cohomology `H^i(Z, -)` of sheaves of `Λ`-modules: the `i`-th right derived functor
of global sections on the small étale site of `Z`. -/
abbrev smallEtaleModuleCohomology (Z : B.Scheme) (i : ℤ) :
    SmallEtaleModuleSheaf.{u, w, r} B Λ Z ⥤ ModuleCat.{w} Λ :=
  (smallEtaleModuleGlobalSections.{u, w, r} B Λ Z).rightDerivedPlus i

/-- The derived global sections of a sheaf of `Λ`-modules form a triangulated functor, so they
commute with shifts. -/
@[instance_reducible]
private def rightDerivedGlobalSectionsCommShift (Z : B.Scheme) :
    (smallEtaleModuleDerivedGlobalSections.{u, w, r} B Λ Z).CommShift ℤ :=
  Functor.IsRightDerivedFunctor.commShift _
    (smallEtaleModuleGlobalSections.{u, w, r} B Λ Z).rightDerivedFunctorPlusUnith
    (HomotopyCategory.Plus.quasiIso (SmallEtaleModuleSheaf.{u, w, r} B Λ Z)) ℤ

attribute [local instance] rightDerivedGlobalSectionsCommShift

/-- The unit of the derived global sections commutes with shifts. -/
private lemma rightDerivedGlobalSectionsUnit_commShift (Z : B.Scheme) :
    NatTrans.CommShift
      (smallEtaleModuleGlobalSections.{u, w, r} B Λ Z).rightDerivedFunctorPlusUnith ℤ :=
  Functor.IsRightDerivedFunctor.natTrans_commShift _
    (smallEtaleModuleGlobalSections.{u, w, r} B Λ Z).rightDerivedFunctorPlusUnith
    (HomotopyCategory.Plus.quasiIso (SmallEtaleModuleSheaf.{u, w, r} B Λ Z)) ℤ

attribute [local instance] rightDerivedGlobalSectionsUnit_commShift

/-- Derived global sections are an exact functor of triangulated categories. -/
private lemma rightDerivedGlobalSections_isTriangulated (Z : B.Scheme) :
    (smallEtaleModuleDerivedGlobalSections.{u, w, r} B Λ Z).IsTriangulated :=
  Functor.isTriangulated_of_isRightDerivedFunctor_mapHomotopyCategoryPlus _ _
    (smallEtaleModuleGlobalSections.{u, w, r} B Λ Z).rightDerivedFunctorPlusUnith

attribute [local instance] rightDerivedGlobalSections_isTriangulated

/-- Étale cohomology is an additive functor of the sheaf. -/
instance smallEtaleModuleCohomology_additive (Z : B.Scheme) (i : ℤ) :
    (smallEtaleModuleCohomology.{u, w, r} B Λ Z i).Additive := by
  unfold smallEtaleModuleCohomology CategoryTheory.Functor.rightDerivedPlus
  infer_instance

/-- The étale cohomology of a sheaf which is zero is zero. -/
theorem isZero_smallEtaleModuleCohomology_of_isZero (Z : B.Scheme) (i : ℤ)
    {F : SmallEtaleModuleSheaf.{u, w, r} B Λ Z} (hF : IsZero F) :
    IsZero ((smallEtaleModuleCohomology.{u, w, r} B Λ Z i).obj F) :=
  Functor.map_isZero _ hF

/-- **The hypercohomology spectral sequence on a small étale site.** For every bounded below
complex `M` of sheaves of `Λ`-modules on the small étale site of `Z` there is a cohomological
spectral sequence, starting at page two, whose second page is the étale cohomology
`H^i(Z, H^j(M))` of the cohomology sheaves of `M` and which abuts to the graded family
`n ↦ H^n(RΓ(Z, M))`.

This is the assertion of [Stacks, Tag 0BKM] in this idiom. -/
def HasHypercohomologySpectralSequence (Z : B.Scheme) : Prop :=
  ∀ M : DerivedCategory.Plus (SmallEtaleModuleSheaf.{u, w, r} B Λ Z),
    ∃ E : CohomologicalSpectralSequence (ModuleCat.{w} Λ) 2,
      (∀ i j : ℤ, Nonempty ((E.page 2 le_rfl).X (i, j) ≅
        (smallEtaleModuleCohomology.{u, w, r} B Λ Z i).obj
          ((DerivedCategory.Plus.homologyFunctor
            (SmallEtaleModuleSheaf.{u, w, r} B Λ Z) j).obj M))) ∧
      SpectralSequence.AbutsTo E (fun n =>
        (DerivedCategory.Plus.homologyFunctor (ModuleCat.{w} Λ) n).obj
          ((smallEtaleModuleDerivedGlobalSections.{u, w, r} B Λ Z).obj M))

/-- **Finite cohomological dimension.** The étale cohomology of every sheaf of `Λ`-modules on
the small étale site of `Z` vanishes outside a range of degrees `[0, dim]` independent of the
sheaf. -/
def HasFiniteEtaleCohomologicalDimension (Z : B.Scheme) : Prop :=
  ∃ dim : ℕ, ∀ (F : SmallEtaleModuleSheaf.{u, w, r} B Λ Z) (i : ℤ),
    i ∉ Set.Icc (0 : ℤ) (dim : ℤ) →
      IsZero ((smallEtaleModuleCohomology.{u, w, r} B Λ Z i).obj F)

namespace CurveGlobalSections

variable (Y : B.Scheme)

/-- The cohomology of `RΓ(Y, M)` vanishes outside `[a, b + dim]` when the cohomology sheaves of `M`
vanish outside `[a, b]`, the étale cohomology vanishes outside `[0, dim]` and the hypercohomology
spectral sequence of `M` exists. -/
private theorem isZero_homology_derivedGlobalSections
    (hSS : HasHypercohomologySpectralSequence.{u, w, r} B Λ Y) (dim : ℕ)
    (hdim : ∀ (F : SmallEtaleModuleSheaf.{u, w, r} B Λ Y) (i : ℤ), i ∉ Set.Icc (0 : ℤ) (dim : ℤ) →
      IsZero ((smallEtaleModuleCohomology.{u, w, r} B Λ Y i).obj F))
    (M : DerivedCategory.Plus (SmallEtaleModuleSheaf.{u, w, r} B Λ Y)) (a b : ℤ)
    (hM : ∀ j : ℤ, j ∉ Set.Icc a b → IsZero ((DerivedCategory.Plus.homologyFunctor
      (SmallEtaleModuleSheaf.{u, w, r} B Λ Y) j).obj M))
    (n : ℤ) (hn : n ∉ Set.Icc a (b + dim)) :
    IsZero ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{w} Λ) n).obj
      ((smallEtaleModuleDerivedGlobalSections.{u, w, r} B Λ Y).obj M)) := by
  obtain ⟨E, hE₂, habuts⟩ := hSS M
  refine isZero_homology_of_abutsTo E _ habuts n fun p => ?_
  refine IsZero.of_iso ?_ (hE₂ p (n - p)).some
  by_cases hp : p ∈ Set.Icc (0 : ℤ) (dim : ℤ)
  · refine isZero_smallEtaleModuleCohomology_of_isZero B Λ Y p (hM (n - p) ?_)
    simp only [Set.mem_Icc] at hn hp ⊢
    omega
  · exact hdim _ p hp

/-- **Boundedness of `RΓ(X_k̄, K)`.** Only finitely many terms of the second page of the
hypercohomology spectral sequence of `Kbar` are nonzero: the cohomology sheaves of `Kbar` vanish
outside `[a, b]` and the étale cohomology of any sheaf vanishes above the cohomological
dimension. So the cohomology of the abutment vanishes outside a range of degrees. -/
theorem exists_isZero_homology (hSS : HasHypercohomologySpectralSequence.{u, w, r} B Λ Y)
    (hDim : HasFiniteEtaleCohomologicalDimension.{u, w, r} B Λ Y)
    (Kbar : DerivedCategory.Plus (SmallEtaleModuleSheaf.{u, w, r} B Λ Y)) (a b : ℤ)
    (hKbar : ∀ j : ℤ, j ∉ Set.Icc a b → IsZero ((DerivedCategory.Plus.homologyFunctor
      (SmallEtaleModuleSheaf.{u, w, r} B Λ Y) j).obj Kbar)) :
    ∃ c e : ℤ, ∀ n : ℤ, n ∉ Set.Icc c e →
      IsZero ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{w} Λ) n).obj
        ((smallEtaleModuleDerivedGlobalSections.{u, w, r} B Λ Y).obj Kbar)) := by
  obtain ⟨dim, hdim⟩ := hDim
  exact ⟨a, b + dim, isZero_homology_derivedGlobalSections B Λ Y hSS dim hdim Kbar a b hKbar⟩


end CurveGlobalSections

end Sections

/-! ### Constructibility and the derived inverse image -/

section Constructible

variable (B : BigEtaleSite.{u}) (Λ : Type r) [CommRing Λ] [IsNoetherianRing Λ]
  [∀ (S T : B.Scheme) (g : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B g).sheafPushforwardContinuous (ModuleCat.{w} Λ)
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
  [∀ (T : B.Scheme) (V : SmallEtale B T.obj T.property),
    HasWeakSheafify ((SmallEtale.topology B T.obj T.property).over V) (ModuleCat.{w} Λ)]
  [∀ Z : B.Scheme, HasSheafify (SmallEtale.topology B Z.obj Z.property) (ModuleCat.{w} Λ)]
  [∀ Z : B.Scheme, EnoughInjectives (SmallEtaleModuleSheaf.{u, w, r} B Λ Z)]

/-- **Finiteness of the étale cohomology of a constructible sheaf.** Every étale cohomology
module of every constructible sheaf of `Λ`-modules on the small étale site of `Z` is a finite
`Λ`-module.

This is the assertion of [Stacks, Tag 03SB] in this idiom. -/
def HasFiniteConstructibleCohomology (Z : B.Scheme) : Prop :=
  ∀ F : SmallEtaleModuleSheaf.{u, w, r} B Λ Z, IsConstructibleModuleSheaf B Z Λ F →
    ∀ i : ℤ, Module.Finite Λ ((smallEtaleModuleCohomology.{u, w, r} B Λ Z i).obj F)

/-- The inverse image of sheaves of `Λ`-modules along a morphism of the big étale site, on the
small étale sites. -/
abbrev smallEtaleModulePullback {S T : B.Scheme} (g : T ⟶ S) :
    SmallEtaleModuleSheaf.{u, w, r} B Λ S ⥤ SmallEtaleModuleSheaf.{u, w, r} B Λ T :=
  (AlgebraicGeometry.smallEtaleBaseChange B g).sheafPullback (ModuleCat.{w} Λ)
    (SmallEtale.topology B S.obj S.property) (SmallEtale.topology B T.obj T.property)

variable [∀ (S T : B.Scheme) (g : T ⟶ S), (smallEtaleModulePullback.{u, w, r} B Λ g).Additive]
  [∀ (S T : B.Scheme) (g : T ⟶ S),
    PreservesFiniteLimits (smallEtaleModulePullback.{u, w, r} B Λ g)]
  [∀ (S T : B.Scheme) (g : T ⟶ S),
    PreservesFiniteColimits (smallEtaleModulePullback.{u, w, r} B Λ g)]

/-- **Constructibility is inherited by the derived inverse image.** A complex with
constructible cohomology sheaves on the small étale site of `S` has constructible cohomology
sheaves after derived inverse image along any morphism `T ⟶ S` of the big étale site.

This is [Stacks, Tag 09YU] in this idiom. It is available in this development, as
`Stacks.EtaleCohomology.isConstructible_derivedPullback`, only when the universe of the module
sections contains the universe of the small étale sites, which the statement below does not
assume; `Stacks.EtaleCohomology.hasConstructibleDerivedPullback` discharges it in that case. -/
def HasConstructibleDerivedPullback : Prop :=
  ∀ (S T : B.Scheme) (g : T ⟶ S)
    (M : DerivedCategory (SmallEtaleModuleSheaf.{u, w, r} B Λ S))
    (N : DerivedCategory (SmallEtaleModuleSheaf.{u, w, r} B Λ T)),
    Nonempty (N ≅ (smallEtaleModulePullback.{u, w, r} B Λ g).mapDerivedCategory.obj M) →
      IsConstructible B S Λ M → IsConstructible B T Λ N

end Constructible

/-! ### Constructibility of a derived inverse image, where it is available -/

section ConstructiblePullbackAvailable

attribute [local instance] preservesFiniteLimits_smallEtaleSheafPullback_moduleCat
  preservesFiniteColimits_smallEtaleSheafPullback_moduleCat
  additive_smallEtaleSheafPullback_moduleCat

variable (B : BigEtaleSite.{u}) (Λ : Type r) [CommRing Λ]
  [∀ (S T : B.Scheme) (g : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B g).sheafPushforwardContinuous
      (ModuleCat.{max (u + 1) w} Λ)
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
  [∀ (T : B.Scheme) (V : SmallEtale B T.obj T.property),
    HasWeakSheafify ((SmallEtale.topology B T.obj T.property).over V)
      (ModuleCat.{max (u + 1) w} Λ)]
  [∀ Z : B.Scheme,
    HasSheafify (SmallEtale.topology B Z.obj Z.property) (ModuleCat.{max (u + 1) w} Λ)]

/-- **Tag 095Y discharges the constructibility of a derived inverse image.** When the module
sections live in a universe containing the universe of the small étale sites, the derived
inverse image of a complex with constructible cohomology sheaves has constructible cohomology
sheaves, by `Stacks.EtaleCohomology.isConstructible_derivedPullback`. -/
theorem hasConstructibleDerivedPullback :
    HasConstructibleDerivedPullback.{u, max (u + 1) w, r} B Λ := by
  rintro S T g M N ⟨e⟩ hM i
  exact AlgebraicGeometry.isConstructibleModuleSheaf_congr B Λ T
    ((DerivedCategory.homologyFunctor _ i).mapIso e).symm
    (isConstructible_derivedPullback B Λ g M hM i)

end ConstructiblePullbackAvailable

/-! ### Finiteness of the cohomology modules -/

section FiniteCoefficients

variable (B : BigEtaleSite.{u}) (Λ : Type r) [CommRing Λ] [Finite Λ]
  [∀ (S T : B.Scheme) (g : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B g).sheafPushforwardContinuous (ModuleCat.{w} Λ)
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
  [∀ (T : B.Scheme) (V : SmallEtale B T.obj T.property),
    HasWeakSheafify ((SmallEtale.topology B T.obj T.property).over V) (ModuleCat.{w} Λ)]
  [∀ Z : B.Scheme, HasSheafify (SmallEtale.topology B Z.obj Z.property) (ModuleCat.{w} Λ)]
  [∀ Z : B.Scheme, EnoughInjectives (SmallEtaleModuleSheaf.{u, w, r} B Λ Z)]

namespace CurveGlobalSections

variable (Y : B.Scheme)

/-- **Finiteness of the cohomology modules of `RΓ(X_k̄, K)`.** The second page of the
hypercohomology spectral sequence of `Kbar` consists of the étale cohomology modules of the
cohomology sheaves of `Kbar`, which are constructible, so every term of that page is a finite
`Λ`-module; the cohomology of the abutment is therefore finite as well. -/
theorem finite_homology (hSS : HasHypercohomologySpectralSequence.{u, w, r} B Λ Y)
    (hFin : HasFiniteConstructibleCohomology.{u, w, r} B Λ Y)
    (Kbar : DerivedCategory.Plus (SmallEtaleModuleSheaf.{u, w, r} B Λ Y))
    (hKbar : ∀ j : ℤ, IsConstructibleModuleSheaf B Y Λ
      ((DerivedCategory.Plus.homologyFunctor
        (SmallEtaleModuleSheaf.{u, w, r} B Λ Y) j).obj Kbar))
    (n : ℤ) :
    Module.Finite Λ ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{w} Λ) n).obj
      ((smallEtaleModuleDerivedGlobalSections.{u, w, r} B Λ Y).obj Kbar)) := by
  obtain ⟨E, hE₂, habuts⟩ := hSS Kbar
  refine finite_homology_of_abutsTo E _ habuts n fun p => ?_
  have := hFin _ (hKbar (n - p)) p
  exact Module.Finite.equiv (hE₂ p (n - p)).some.symm.toLinearEquiv


end CurveGlobalSections

end FiniteCoefficients

/-! ### Finite Tor dimension -/

section Twists

variable (B : BigEtaleSite.{u}) (Λ : Type r) [Ring Λ]
  [∀ Z : B.Scheme, HasSheafify (SmallEtale.topology B Z.obj Z.property) (ModuleCat.{w} Λ)]
  [∀ Z : B.Scheme, EnoughInjectives (SmallEtaleModuleSheaf.{u, w, r} B Λ Z)]
  [∀ Z : B.Scheme, HasSheafify (SmallEtale.topology B Z.obj Z.property) (ModuleCat.{w} ℤ)]
  [∀ Z : B.Scheme, EnoughInjectives (SmallEtaleModuleSheaf.{u, w, 0} B ℤ Z)]

namespace CurveGlobalSections

variable (Y : B.Scheme)

/-- **Finite Tor dimension of `RΓ(X_k̄, K)`.** The projection formula identifies
`N ⊗ᴸ[Λ] RΓ(X_k̄, K)` with `RΓ(X_k̄, N ⊗ᴸ[Λ] K)`, and the hypercohomology spectral sequence of
the twist `N ⊗ᴸ[Λ] K` has only finitely many nonzero terms, in a range of degrees independent of
`N`: the cohomology sheaves of the twist vanish outside `[a, b]` and the étale cohomology of any
sheaf of abelian groups vanishes above the cohomological dimension. -/
theorem hasFiniteTorDimension (hSSZ : HasHypercohomologySpectralSequence.{u, w, 0} B ℤ Y)
    (hDimZ : HasFiniteEtaleCohomologicalDimension.{u, w, 0} B ℤ Y)
    (Dt : StacksDraft.Perfect.BalancedDerivedTensoring.{r, w} Λ)
    (Kbar : DerivedCategory.Plus (SmallEtaleModuleSheaf.{u, w, r} B Λ Y))
    (twist : ModuleCat.{w} (MulOpposite Λ) →
      DerivedCategory.Plus (SmallEtaleModuleSheaf.{u, w, 0} B ℤ Y)) (a b : ℤ)
    (htwist : ∀ (N : ModuleCat.{w} (MulOpposite Λ)) (j : ℤ), j ∉ Set.Icc a b →
      IsZero ((DerivedCategory.Plus.homologyFunctor
        (SmallEtaleModuleSheaf.{u, w, 0} B ℤ Y) j).obj (twist N)))
    (hformula : ∀ N : ModuleCat.{w} (MulOpposite Λ),
      Nonempty ((Dt.derived.obj N).obj (DerivedCategory.Plus.ι.obj
          ((smallEtaleModuleDerivedGlobalSections.{u, w, r} B Λ Y).obj Kbar)) ≅
        DerivedCategory.Plus.ι.obj
          ((smallEtaleModuleDerivedGlobalSections.{u, w, 0} B ℤ Y).obj (twist N)))) :
    StacksDraft.Perfect.HasFiniteTorDimension Dt
      (DerivedCategory.Plus.ι.obj
        ((smallEtaleModuleDerivedGlobalSections.{u, w, r} B Λ Y).obj Kbar)) := by
  obtain ⟨dim, hdim⟩ := hDimZ
  refine ⟨a, b + dim, fun N i hi => ?_⟩
  refine IsZero.of_iso ?_
    ((DerivedCategory.homologyFunctor (ModuleCat.{w} ℤ) i).mapIso (hformula N).some)
  exact isZero_homology_derivedGlobalSections B ℤ Y hSSZ dim hdim (twist N) a b (htwist N) i hi

end CurveGlobalSections

end Twists

/-! ### Tag 03TV -/

namespace CurveGlobalSections

section Main

attribute [local instance] GrothendieckTopology.hasSheafify_addCommGrpCat
  AlgebraicGeometry.SheafOfModules.wEqualsLocallyBijective_addCommGrpCat
  Stacks.hasSheafCompose_forget₂_commRingCat
  AlgebraicGeometry.RingedSite.sliceHasSheafify
  AlgebraicGeometry.RingedSite.sliceWEqualsLocallyBijective
  AlgebraicGeometry.RingedSite.sliceRestrictionPreservesFiniteLimits
  AlgebraicGeometry.RingedSite.sliceRestrictionPreservesFiniteColimits

variable (B : BigEtaleSite.{u}) (X : B.Scheme) (Λ : Type r) [CommRing Λ] [Finite Λ]
  [∀ (S T : B.Scheme) (g : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B g).sheafPushforwardContinuous (ModuleCat.{w} Λ)
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
  [∀ (T : B.Scheme) (V : SmallEtale B T.obj T.property),
    HasWeakSheafify ((SmallEtale.topology B T.obj T.property).over V) (ModuleCat.{w} Λ)]
  [∀ Z : B.Scheme, HasSheafify (SmallEtale.topology B Z.obj Z.property) (ModuleCat.{w} Λ)]
  [∀ Z : B.Scheme, EnoughInjectives (SmallEtaleModuleSheaf.{u, w, r} B Λ Z)]
  [∀ Z : B.Scheme, HasSheafify (SmallEtale.topology B Z.obj Z.property) (ModuleCat.{w} ℤ)]
  [∀ Z : B.Scheme, EnoughInjectives (SmallEtaleModuleSheaf.{u, w, 0} B ℤ Z)]
  [∀ (S T : B.Scheme) (g : T ⟶ S), (smallEtaleModulePullback.{u, w, r} B Λ g).Additive]
  [∀ (S T : B.Scheme) (g : T ⟶ S),
    PreservesFiniteLimits (smallEtaleModulePullback.{u, w, r} B Λ g)]
  [∀ (S T : B.Scheme) (g : T ⟶ S),
    PreservesFiniteColimits (smallEtaleModulePullback.{u, w, r} B Λ g)]
  [HasDerivedCategory.{d} (RingedSite.Modules.{u + 1, u, max (u + 1) w r}
    (constantCoefficientRingedSite.{u, w, r} B X Λ))]
  [hSliceDerived : ∀ U : (constantCoefficientRingedSite.{u, w, r} B X Λ).C,
    HasDerivedCategory.{d} (RingedSite.Modules.{u + 1, u, max (u + 1) w r}
      ((constantCoefficientRingedSite.{u, w, r} B X Λ).over U))]
  [∀ U : (constantCoefficientRingedSite.{u, w, r} B X Λ).C,
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, max (u + 1) w r, max (u + 1) w r,
      max (u + 1) w r}
      ((constantCoefficientRingedSite.{u, w, r} B X Λ).over U).O).Additive]
  [∀ (U : (constantCoefficientRingedSite.{u, w, r} B X Λ).C) M,
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, max (u + 1) w r, max (u + 1) w r,
      max (u + 1) w r}
      ((constantCoefficientRingedSite.{u, w, r} B X Λ).over U).O).obj M).Additive]
  [∀ (U : (constantCoefficientRingedSite.{u, w, r} B X Λ).C)
    (K L : CochainComplex (RingedSite.Modules.{u + 1, u, max (u + 1) w r}
      ((constantCoefficientRingedSite.{u, w, r} B X Λ).over U)) ℤ),
    HomologicalComplex.HasMapBifunctor K L
      (Stacks.SheafOfModules.Tensor.sheafTensor
        ((constantCoefficientRingedSite.{u, w, r} B X Λ).over U).O) (ComplexShape.up ℤ)]

attribute [local instance] Stacks.SheafOfModules.DerivedTensorProduct.sliceDerived
  Stacks.SheafOfModules.DerivedTensorProduct.sliceTensorAdditive
  Stacks.SheafOfModules.DerivedTensorProduct.sliceTensorObjAdditive
  Stacks.SheafOfModules.DerivedTensorProduct.sliceHasMapBifunctor
  AlgebraicGeometry.RingedSite.sliceHasDerivedCategory

variable (T : ∀ U : (constantCoefficientRingedSite.{u, w, r} B X Λ).C,
    Stacks.SheafOfModules.DerivedTensorProduct.{u + 1, u, max (u + 1) w r, d}
      ((constantCoefficientRingedSite.{u, w, r} B X Λ).over U))

/-- **The projection formula and the finite Tor dimension of a constructible complex.** For
every object `K` of `D_ctf(X_étale, Λ)` and every bounded below complex `M` of sheaves of
`Λ`-modules on the small étale site of `Y` representing the derived inverse image of `K` along
`f : Y ⟶ X`, there is a family of bounded below complexes `N ⊗ᴸ[Λ] M` of sheaves of abelian
groups indexed by the right `Λ`-modules `N`, a range of degrees `[a, b]` outside of which the
cohomology sheaves of `M` and of all its twists `N ⊗ᴸ[Λ] M` vanish, and the projection formula

  `N ⊗ᴸ[Λ] RΓ(Y, M) = RΓ(Y, N ⊗ᴸ[Λ] M)`.

The range of degrees is the boundedness of `K` together with its finite Tor dimension, and it is
independent of `N`; the derived tensor product of a right `Λ`-module with an object of `D(Λ)` is
measured against `Dt`. -/
def HasGeometricTwisting (Y : B.Scheme) (f : Y ⟶ X)
    (Dt : StacksDraft.Perfect.BalancedDerivedTensoring.{r, w} Λ) : Prop :=
  ∀ (K : ConstructibleFiniteTorDerivedCategory.{u, w, r, d} B X Λ T)
    (M : DerivedCategory.Plus (SmallEtaleModuleSheaf.{u, w, r} B Λ Y)),
    Nonempty (DerivedCategory.Plus.ι.obj M ≅
      (smallEtaleModulePullback.{u, w, r} B Λ f).mapDerivedCategory.obj K.obj.obj) →
    ∃ (twist : ModuleCat.{w} (MulOpposite Λ) →
        DerivedCategory.Plus (SmallEtaleModuleSheaf.{u, w, 0} B ℤ Y)) (a b : ℤ),
      (∀ j : ℤ, j ∉ Set.Icc a b → IsZero ((DerivedCategory.Plus.homologyFunctor
        (SmallEtaleModuleSheaf.{u, w, r} B Λ Y) j).obj M)) ∧
      (∀ (N : ModuleCat.{w} (MulOpposite Λ)) (j : ℤ), j ∉ Set.Icc a b →
        IsZero ((DerivedCategory.Plus.homologyFunctor
          (SmallEtaleModuleSheaf.{u, w, 0} B ℤ Y) j).obj (twist N))) ∧
      ∀ N : ModuleCat.{w} (MulOpposite Λ),
        Nonempty ((Dt.derived.obj N).obj (DerivedCategory.Plus.ι.obj
            ((smallEtaleModuleDerivedGlobalSections.{u, w, r} B Λ Y).obj M)) ≅
          DerivedCategory.Plus.ι.obj
            ((smallEtaleModuleDerivedGlobalSections.{u, w, 0} B ℤ Y).obj (twist N)))

omit [Finite Λ] in
/-- **Boundedness of `RΓ(X_k̄, K)` from the carried inputs.** The window of degrees in which the
cohomology sheaves of the restriction of `K` to the geometric fibre can be nonzero is the first
clause of `Stacks.EtaleCohomology.CurveGlobalSections.HasGeometricTwisting`; together with the
hypercohomology spectral sequence and the cohomological dimension it bounds the degrees in which
the cohomology modules of `RΓ(X_k̄, K)` can be nonzero. -/
theorem exists_isZero_homology_of_hasGeometricTwisting (Y : B.Scheme) (f : Y ⟶ X)
    (Dt : StacksDraft.Perfect.BalancedDerivedTensoring.{r, w} Λ)
    (hSS : HasHypercohomologySpectralSequence.{u, w, r} B Λ Y)
    (hDim : HasFiniteEtaleCohomologicalDimension.{u, w, r} B Λ Y)
    (hTwisting : HasGeometricTwisting.{u, w, r, d} B X Λ T Y f Dt)
    (K : ConstructibleFiniteTorDerivedCategory.{u, w, r, d} B X Λ T)
    (Kbar : DerivedCategory.Plus (SmallEtaleModuleSheaf.{u, w, r} B Λ Y))
    (eKbar : Nonempty (DerivedCategory.Plus.ι.obj Kbar ≅
      (smallEtaleModulePullback.{u, w, r} B Λ f).mapDerivedCategory.obj K.obj.obj)) :
    ∃ c e : ℤ, ∀ n : ℤ, n ∉ Set.Icc c e →
      IsZero ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{w} Λ) n).obj
        ((smallEtaleModuleDerivedGlobalSections.{u, w, r} B Λ Y).obj Kbar)) := by
  obtain ⟨twist, a, b, hwindow, -, -⟩ := hTwisting K Kbar eKbar
  exact exists_isZero_homology B Λ Y hSS hDim Kbar a b hwindow

/-- **Stacks 03TV.** Let `k` be a field, let `X` be a projective curve over `k`, let `Λ` be a
finite commutative ring and let `K` be an object of `D_ctf(X_étale, Λ)`. Then the derived global
sections `RΓ(X_k̄, K)` of the restriction of `K` to the geometric fibre
`X_k̄ = X ×_{Spec k} Spec k̄` form a perfect complex of `Λ`-modules.

The geometric fibre is the object `Y` of the big étale site, pinned down by `_hbase`, and the
restriction of `K` to it is the bounded below complex `Kbar`, pinned down by `eKbar`. The proof
is the one of the source: the hypercohomology spectral sequence `hSS` together with the
finiteness `hFin` of the étale cohomology of a constructible sheaf gives finiteness of the
cohomology modules, the projection formula contained in `hTwisting` together with the
hypercohomology spectral sequence `hSSZ` and the cohomological dimension `hDimZ` gives finite
Tor dimension, and the criterion of Tag 03TO concludes. -/
@[stacks 03TV "from the hypercohomology spectral sequences `hSS` and `hSSZ`, the finiteness \
`hFin` of the étale cohomology of a constructible sheaf, the cohomological dimension `hDimZ`, \
the constructibility `hPullback` of a derived inverse image, and the projection formula with \
the Tor window `hTwisting`"]
theorem isPerfect (Y : B.Scheme) (f : Y ⟶ X)
    (Dt : StacksDraft.Perfect.BalancedDerivedTensoring.{r, w} Λ)
    (hSS : HasHypercohomologySpectralSequence.{u, w, r} B Λ Y)
    (hSSZ : HasHypercohomologySpectralSequence.{u, w, 0} B ℤ Y)
    (hFin : HasFiniteConstructibleCohomology.{u, w, r} B Λ Y)
    (hDimZ : HasFiniteEtaleCohomologicalDimension.{u, w, 0} B ℤ Y)
    (hPullback : HasConstructibleDerivedPullback.{u, w, r} B Λ)
    (hTwisting : HasGeometricTwisting.{u, w, r, d} B X Λ T Y f Dt)
    {k : Type u} [Field k] (gk : X.obj ⟶ Spec (CommRingCat.of k))
    (_hcurve : IsCurve k gk) (_hprojective : IsProjective gk)
    (_hbase : ∃ e : Y.obj ≅ Stacks.Frobenius.fieldBaseChange (Over.mk gk) (AlgebraicClosure k),
      B.inclusion.map f = e.hom ≫ pullback.fst gk
        (Stacks.Frobenius.specAlgebraMap k (AlgebraicClosure k)))
    (K : ConstructibleFiniteTorDerivedCategory.{u, w, r, d} B X Λ T)
    (Kbar : DerivedCategory.Plus (SmallEtaleModuleSheaf.{u, w, r} B Λ Y))
    (eKbar : Nonempty (DerivedCategory.Plus.ι.obj Kbar ≅
      (smallEtaleModulePullback.{u, w, r} B Λ f).mapDerivedCategory.obj K.obj.obj)) :
    StacksDraft.Perfect.IsPerfect
      (DerivedCategory.Plus.ι.obj
        ((smallEtaleModuleDerivedGlobalSections.{u, w, r} B Λ Y).obj Kbar)) := by
  obtain ⟨twist, a, b, -, htwist, hformula⟩ := hTwisting K Kbar eKbar
  have hcb := hPullback X Y f K.obj.obj (DerivedCategory.Plus.ι.obj Kbar) eKbar K.obj.property
  exact (StacksDraft.Perfect.isPerfect_iff_hasFiniteTorDimension_and_finite_homology Dt _).mpr
    ⟨hasFiniteTorDimension B Λ Y hSSZ hDimZ Dt Kbar twist a b htwist hformula,
      fun n => finite_homology B Λ Y hSS hFin Kbar hcb n⟩

end Main

end CurveGlobalSections

end Stacks.EtaleCohomology

end
