module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.OpenClosedPointReduction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.RationalPointsDegreeOne
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CanonicalFrobeniusAdditivity
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.ClosedImmersionFrobeniusTraceInvariance
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CompactSupportFrobeniusRestrictScalars
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.InducedCompactification
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The open and closed dévissage of the trace formula, in any dimension

Let `k` be a finite field, `X` a scheme over `k` with a compactification `j : X ⟶ X̄` over `k`,
`j_U : U ⟶ X` an open immersion and `i : Z ⟶ X` a closed immersion onto its complement.  The
compactification of `X` induces compactifications of `U` (the composite `j ∘ j_U`) and of `Z`
(the scheme-theoretic image of `j ∘ i`).  For a bounded below complex `K` of sheaves of
`Λ`-modules on `X`, with the cohomologies with compact support of `K|_U` and `K|_Z` perfect,

`Tr(π^* | RΓ_c(X_k̄, K)) = Tr(π^* | RΓ_c(U_k̄, K|_U)) + Tr(π^* | RΓ_c(Z_k̄, K|_Z))`,

each side computed through the induced compactification, and `RΓ_c(X_k̄, K)` is perfect.  This is
Step 1 of the proof of [Stacks, Tag 03UG] for an arbitrary closed subscheme, and it is the
dévissage step of the trace formula in any dimension, [Stacks, Tag 03UI] (1).

## Main results

* `Stacks.EtaleCohomology.perfectDerivedTrace_frobeniusRestrictionCohomologyEndo_eq_of_iso` —
  the canonical Frobenius trace is invariant under isomorphism of the coefficient complex.
* `Stacks.EtaleCohomology.canonicalCompactSupportLefschetzNumber_extensionByZero_eq` —
  `T''(X, j_{U!} L) = T''(U, L)`.
* `Stacks.EtaleCohomology.canonicalCompactSupportLefschetzNumber_directImage_eq` —
  `T''(X, i_* M) = T''(Z, M)`.
* `Stacks.EtaleCohomology.canonicalCompactSupportLefschetzNumber_eq_add_openClosed` — the
  dévissage.

## References

* [Stacks Project, Tag 03UG](https://stacks.math.columbia.edu/tag/03UG), Step 1.
* [Stacks Project, Tag 03UI](https://stacks.math.columbia.edu/tag/03UI), item (1).
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open CategoryTheory.FilteredDerived Stacks.Frobenius

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

section Iso

variable (Λ : Type) [Ring Λ] {k : Type u} [Field k] [Fintype k] (Y : Over (Spec (.of k)))
  (kbar : Type u) [Field kbar] [Algebra k kbar] (p q : ℕ) [Fact p.Prime] [CharP k p]
  (hcard : Fintype.card k = p ^ q)

/-- The cohomology `RΓ(Y_k̄, C|_{Y_k̄})` of an isomorphic complex is isomorphic. -/
def frobeniusRestrictionCohomologyIso {N₁ N₂ : CochainComplex.Plus (EtaleModules.{u, 0} Λ Y.left)}
    (e : N₁ ≅ N₂) :
    (etaleModuleDerivedGlobalSections.{u, 0} Λ (Spec (.of kbar))).obj
        ((etaleModuleDerivedDirectImage.{u, 0} Λ (pullback.snd Y.hom (specAlgebraMap k kbar))).obj
          (fieldBaseChangeRestriction.{u, 0} Λ Y kbar N₁)) ≅
      (etaleModuleDerivedGlobalSections.{u, 0} Λ (Spec (.of kbar))).obj
        ((etaleModuleDerivedDirectImage.{u, 0} Λ (pullback.snd Y.hom (specAlgebraMap k kbar))).obj
          (fieldBaseChangeRestriction.{u, 0} Λ Y kbar N₂)) :=
  (etaleModuleDerivedGlobalSections.{u, 0} Λ (Spec (.of kbar))).mapIso
    ((etaleModuleDerivedDirectImage.{u, 0} Λ (pullback.snd Y.hom (specAlgebraMap k kbar))).mapIso
      ((fieldBaseChangeRestrictionFunctor.{u, 0} Λ Y kbar).mapIso e))

omit [Fintype k] in
/-- Perfectness of `RΓ(Y_k̄, C|_{Y_k̄})` only depends on `C` up to isomorphism. -/
theorem isPerfect_frobeniusRestriction_of_iso
    {N₁ N₂ : CochainComplex.Plus (EtaleModules.{u, 0} Λ Y.left)} (e : N₁ ≅ N₂)
    (h : StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj
      ((etaleModuleDerivedGlobalSections.{u, 0} Λ (Spec (.of kbar))).obj
        ((etaleModuleDerivedDirectImage.{u, 0} Λ (pullback.snd Y.hom (specAlgebraMap k kbar))).obj
          (fieldBaseChangeRestriction.{u, 0} Λ Y kbar N₁))))) :
    StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj
      ((etaleModuleDerivedGlobalSections.{u, 0} Λ (Spec (.of kbar))).obj
        ((etaleModuleDerivedDirectImage.{u, 0} Λ (pullback.snd Y.hom (specAlgebraMap k kbar))).obj
          (fieldBaseChangeRestriction.{u, 0} Λ Y kbar N₂)))) :=
  StacksDraft.Perfect.isPerfect_of_iso
    (DerivedCategory.Plus.ι.mapIso (frobeniusRestrictionCohomologyIso Λ Y kbar e)).symm h

/-- **The canonical Frobenius trace is invariant under isomorphism of the coefficient
complex**: the canonical endomorphism is natural in the complex. -/
theorem perfectDerivedTrace_frobeniusRestrictionCohomologyEndo_eq_of_iso
    {N₁ N₂ : CochainComplex.Plus (EtaleModules.{u, 0} Λ Y.left)} (e : N₁ ≅ N₂)
    (h₁ : StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj
      ((etaleModuleDerivedGlobalSections.{u, 0} Λ (Spec (.of kbar))).obj
        ((etaleModuleDerivedDirectImage.{u, 0} Λ (pullback.snd Y.hom (specAlgebraMap k kbar))).obj
          (fieldBaseChangeRestriction.{u, 0} Λ Y kbar N₁)))))
    (h₂ : StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj
      ((etaleModuleDerivedGlobalSections.{u, 0} Λ (Spec (.of kbar))).obj
        ((etaleModuleDerivedDirectImage.{u, 0} Λ (pullback.snd Y.hom (specAlgebraMap k kbar))).obj
          (fieldBaseChangeRestriction.{u, 0} Λ Y kbar N₂))))) :
    perfectDerivedTrace Λ ⟨_, h₁⟩ (DerivedCategory.Plus.ι.map
        (frobeniusRestrictionCohomologyEndo.{u, 0} Λ Y kbar p q hcard N₁)) =
      perfectDerivedTrace Λ ⟨_, h₂⟩ (DerivedCategory.Plus.ι.map
        (frobeniusRestrictionCohomologyEndo.{u, 0} Λ Y kbar p q hcard N₂)) := by
  refine perfectDerivedTrace_congr Λ _ _
    (DerivedCategory.Plus.ι.mapIso (frobeniusRestrictionCohomologyIso Λ Y kbar e)) _ _ ?_
  rw [Functor.mapIso_hom, ← Functor.map_comp, ← Functor.map_comp]
  congr 1
  exact (frobeniusRestrictionCohomologyEndo_naturality (Λ := Λ) Y kbar p q hcard e.hom).symm

end Iso

section Pieces

variable (Λ : Type) [Ring Λ] {k : Type u} [Field k] [Fintype k] {X : Scheme.{u}}
  {f : X ⟶ Spec (.of k)} (j : CompactificationOf (Over.mk f))
  (kbar : Type u) [Field kbar] [Algebra k kbar] (p q : ℕ) [Fact p.Prime] [CharP k p]
  (hcard : Fintype.card k = p ^ q)

/-- A natural isomorphism of functors between categories of sheaves induces an isomorphism of
the bounded below complexes obtained by applying them degreewise. -/
def mapCochainComplexPlusIsoOfNatIso {A B : Type*} [Category* A] [Category* B]
    [Abelian A] [Abelian B] {F G : A ⥤ B} [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteLimits G] (α : F ≅ G)
    (L : CochainComplex.Plus A) :
    F.mapCochainComplexPlus.obj L ≅ G.mapCochainComplexPlus.obj L :=
  (CochainComplex.Plus.fullyFaithfulι B).preimageIso
    (HomologicalComplex.Hom.isoOfComponents (fun n => α.app (L.obj.X n))
      (fun a b _ => (α.hom.naturality (L.obj.d a b)).symm))

variable {U : Scheme.{u}} (jU : U ⟶ X) [IsOpenImmersion jU]

/-- `j_! (j_{U!} L) ≅ (j ∘ j_U)_! L`, degreewise. -/
def extensionByZeroRestrictOpenComplexIso (L : CochainComplex.Plus (EtaleModules.{u, 0} Λ U)) :
    (etaleModuleExtensionByZero.{u, 0} Λ j.immersion).mapCochainComplexPlus.obj
        ((etaleModuleExtensionByZero.{u, 0} Λ jU).mapCochainComplexPlus.obj L) ≅
      (etaleModuleExtensionByZero.{u, 0} Λ (j.restrictOpen jU).immersion).mapCochainComplexPlus.obj
        L :=
  (CochainComplex.Plus.fullyFaithfulι _).preimageIso
    (HomologicalComplex.Hom.isoOfComponents
      (fun n => ((etaleModuleExtensionByZeroCompIso.{u, 0} Λ jU j.immersion).app (L.obj.X n)).symm)
      (fun a b _ => ((etaleModuleExtensionByZeroCompIso.{u, 0} Λ jU j.immersion).inv.naturality
        (L.obj.d a b)).symm))

/-- **`T''(X, j_{U!} L) = T''(U, L)`**: the cohomology with compact support of `X` through `j` of
the extension by zero of `L` is that of `U` through the induced compactification `j ∘ j_U`,
compatibly with the canonical Frobenius. -/
theorem canonicalCompactSupportLefschetzNumber_extensionByZero_eq [Finite Λ]
    (L : CochainComplex.Plus (EtaleModules.{u, 0} Λ U))
    (hX : StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj
      (compactSupportFrobeniusCohomology.{u, 0} Λ f j kbar
        ((etaleModuleExtensionByZero.{u, 0} Λ jU).mapCochainComplexPlus.obj L))))
    (hU : StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj
      (compactSupportFrobeniusCohomology.{u, 0} Λ (jU ≫ f) (j.restrictOpen jU) kbar L))) :
    canonicalCompactSupportLefschetzNumber.{u, 0} Λ f j kbar p q hcard
        ((etaleModuleExtensionByZero.{u, 0} Λ jU).mapCochainComplexPlus.obj L) hX =
      canonicalCompactSupportLefschetzNumber.{u, 0} Λ (jU ≫ f) (j.restrictOpen jU) kbar p q hcard
        L hU :=
  perfectDerivedTrace_frobeniusRestrictionCohomologyEndo_eq_of_iso Λ (Over.mk j.toBase) kbar p q
    hcard (extensionByZeroRestrictOpenComplexIso Λ j jU L) hX hU

omit [Fintype k] in
/-- Perfectness of `RΓ_c` transports between `j_{U!} L` on `X` and `L` on `U`. -/
theorem isPerfect_compactSupport_extensionByZero_iff
    (L : CochainComplex.Plus (EtaleModules.{u, 0} Λ U)) :
    StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj
      (compactSupportFrobeniusCohomology.{u, 0} Λ f j kbar
        ((etaleModuleExtensionByZero.{u, 0} Λ jU).mapCochainComplexPlus.obj L))) ↔
    StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj
      (compactSupportFrobeniusCohomology.{u, 0} Λ (jU ≫ f) (j.restrictOpen jU) kbar L)) :=
  ⟨isPerfect_frobeniusRestriction_of_iso Λ (Over.mk j.toBase) kbar
      (extensionByZeroRestrictOpenComplexIso Λ j jU L),
    isPerfect_frobeniusRestriction_of_iso Λ (Over.mk j.toBase) kbar
      (extensionByZeroRestrictOpenComplexIso Λ j jU L).symm⟩

end Pieces

section Closed

variable (Λ : Type) [Ring Λ] {k : Type u} [Field k] [Fintype k] {X : Scheme.{u}}
  {f : X ⟶ Spec (.of k)} [QuasiCompact f] (j : CompactificationOf (Over.mk f))
  (kbar : Type u) [Field kbar] [Algebra k kbar] (p q : ℕ) [Fact p.Prime] [CharP k p]
  (hcard : Fintype.card k = p ^ q) {Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]

/-- The closed immersion `Z̄ ⟶ X̄` of the compactification induced on `Z`, as a morphism over
`k`, is a closed immersion. -/
instance : IsClosedImmersion (Over.homMk (j.closedSpaceι i) rfl :
    Over.mk (j.restrictClosed i).toBase ⟶ Over.mk j.toBase).left :=
  inferInstanceAs (IsClosedImmersion (j.closedSpaceι i))

/-- `j_! (i_* M) ≅ ι_* (t_! M)`, degreewise, for the compactification `t : Z ⟶ Z̄` induced on
`Z` and the closed immersion `ι : Z̄ ⟶ X̄`. -/
def extensionByZeroRestrictClosedComplexIso (M : CochainComplex.Plus (EtaleModules.{u, 0} Λ Z)) :
    (etaleModuleExtensionByZero.{u, 0} Λ j.immersion).mapCochainComplexPlus.obj
        ((etaleModuleDirectImage.{u, 0} Λ i).mapCochainComplexPlus.obj M) ≅
      (etaleModuleDirectImage.{u, 0} Λ (j.closedSpaceι i)).mapCochainComplexPlus.obj
        ((etaleModuleExtensionByZero.{u, 0} Λ
          (j.restrictClosed i).immersion).mapCochainComplexPlus.obj M) :=
  (CochainComplex.Plus.fullyFaithfulι _).preimageIso
    (HomologicalComplex.Hom.isoOfComponents
      (fun n => (etaleModuleExtensionByZeroDirectImageIso.{u, 0} Λ i (j.closedImmersion i).toImage
        j.immersion (j.closedSpaceι i) (j.isPullback_restrictClosed i)).app (M.obj.X n))
      (fun a b _ => ((etaleModuleExtensionByZeroDirectImageIso.{u, 0} Λ i
        (j.closedImmersion i).toImage j.immersion (j.closedSpaceι i)
        (j.isPullback_restrictClosed i)).hom.naturality (M.obj.d a b)).symm))

/-- **`T''(X, i_* M) = T''(Z, M)`**: the cohomology with compact support of `X` through `j` of a
direct image from the closed subscheme `Z` is that of `Z` through the induced compactification,
compatibly with the canonical Frobenius. -/
theorem canonicalCompactSupportLefschetzNumber_directImage_eq [Finite Λ]
    (M : CochainComplex.Plus (EtaleModules.{u, 0} Λ Z))
    (hX : StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj
      (compactSupportFrobeniusCohomology.{u, 0} Λ f j kbar
        ((etaleModuleDirectImage.{u, 0} Λ i).mapCochainComplexPlus.obj M))))
    (hZ : StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj
      (compactSupportFrobeniusCohomology.{u, 0} Λ (i ≫ f) (j.restrictClosed i) kbar M))) :
    canonicalCompactSupportLefschetzNumber.{u, 0} Λ f j kbar p q hcard
        ((etaleModuleDirectImage.{u, 0} Λ i).mapCochainComplexPlus.obj M) hX =
      canonicalCompactSupportLefschetzNumber.{u, 0} Λ (i ≫ f) (j.restrictClosed i) kbar p q hcard
        M hZ := by
  have hY := isPerfect_frobeniusRestriction_of_iso Λ (Over.mk j.toBase) kbar
    (extensionByZeroRestrictClosedComplexIso Λ j i M) hX
  exact (perfectDerivedTrace_frobeniusRestrictionCohomologyEndo_eq_of_iso Λ (Over.mk j.toBase)
    kbar p q hcard (extensionByZeroRestrictClosedComplexIso Λ j i M) hX hY).trans
    (perfectDerivedTrace_frobeniusRestrictionCohomologyEndo_directImage Λ
      (Over.homMk (j.closedSpaceι i) rfl : Over.mk (j.restrictClosed i).toBase ⟶ Over.mk j.toBase)
      p q hcard kbar _ hY hZ)

/-- Perfectness of `RΓ_c` transports between `i_* M` on `X` and `M` on `Z`. -/
theorem isPerfect_compactSupport_directImage_iff
    (M : CochainComplex.Plus (EtaleModules.{u, 0} Λ Z)) :
    StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj
      (compactSupportFrobeniusCohomology.{u, 0} Λ f j kbar
        ((etaleModuleDirectImage.{u, 0} Λ i).mapCochainComplexPlus.obj M))) ↔
    StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj
      (compactSupportFrobeniusCohomology.{u, 0} Λ (i ≫ f) (j.restrictClosed i) kbar M)) := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · exact (isPerfect_frobeniusRestriction_directImage_iff Λ (Over.homMk (j.closedSpaceι i) rfl :
        Over.mk (j.restrictClosed i).toBase ⟶ Over.mk j.toBase) kbar _).1
      (isPerfect_frobeniusRestriction_of_iso Λ (Over.mk j.toBase) kbar
        (extensionByZeroRestrictClosedComplexIso Λ j i M) h)
  · exact isPerfect_frobeniusRestriction_of_iso Λ (Over.mk j.toBase) kbar
      (extensionByZeroRestrictClosedComplexIso Λ j i M).symm
      ((isPerfect_frobeniusRestriction_directImage_iff Λ (Over.homMk (j.closedSpaceι i) rfl :
        Over.mk (j.restrictClosed i).toBase ⟶ Over.mk j.toBase) kbar _).2 h)

end Closed

section Devissage

variable (Λ : Type) [Ring Λ] {k : Type u} [Field k] [Fintype k] {X : Scheme.{u}}
  {f : X ⟶ Spec (.of k)} [QuasiCompact f] (j : CompactificationOf (Over.mk f))
  (kbar : Type u) [Field kbar] [Algebra k kbar] (p q : ℕ) [Fact p.Prime] [CharP k p]
  (hcard : Fintype.card k = p ^ q) {U Z : Scheme.{u}} (jU : U ⟶ X) [IsOpenImmersion jU]
  (i : Z ⟶ X) [IsClosedImmersion i] (hij : Set.range jU.base = (Set.range i.base)ᶜ)

include hij in
/-- **The open and closed dévissage of `T''`, in any dimension.**  For an open immersion
`j_U : U ⟶ X` with closed complement `i : Z ⟶ X`, a compactification `j` of `X` over `k`, and a
bounded below complex `K` on `X` such that `RΓ_c(U_k̄, K|_U)` and `RΓ_c(Z_k̄, K|_Z)` (through the
induced compactifications) are perfect, `RΓ_c(X_k̄, K)` is perfect and

`T''(X, K) = T''(U, K|_U) + T''(Z, K|_Z)`. -/
@[sga "4½ Rapport 5.13" "First equality of 5.13 B"]
theorem canonicalCompactSupportLefschetzNumber_eq_add_openClosed [Finite Λ]
    (K : CochainComplex.Plus (EtaleModules.{u, 0} Λ X))
    (hU : StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj
      (compactSupportFrobeniusCohomology.{u, 0} Λ (jU ≫ f) (j.restrictOpen jU) kbar
        ((etaleModuleRestriction.{u, 0} Λ jU).mapCochainComplexPlus.obj K))))
    (hZ : StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj
      (compactSupportFrobeniusCohomology.{u, 0} Λ (i ≫ f) (j.restrictClosed i) kbar
        ((etaleModuleInverseImage.{u, 0} Λ i).mapCochainComplexPlus.obj K)))) :
    ∃ hX : StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj
        (compactSupportFrobeniusCohomology.{u, 0} Λ f j kbar K)),
      canonicalCompactSupportLefschetzNumber.{u, 0} Λ f j kbar p q hcard K hX =
        canonicalCompactSupportLefschetzNumber.{u, 0} Λ (jU ≫ f) (j.restrictOpen jU) kbar p q
            hcard ((etaleModuleRestriction.{u, 0} Λ jU).mapCochainComplexPlus.obj K) hU +
          canonicalCompactSupportLefschetzNumber.{u, 0} Λ (i ≫ f) (j.restrictClosed i) kbar p q
            hcard ((etaleModuleInverseImage.{u, 0} Λ i).mapCochainComplexPlus.obj K) hZ := by
  have hS := openClosedCochainShortComplex_shortExact Λ i jU hij K.obj
  have hp₁ := (isPerfect_compactSupport_extensionByZero_iff Λ j kbar jU
    ((etaleModuleRestriction.{u, 0} Λ jU).mapCochainComplexPlus.obj K)).2 hU
  have hp₃ := (isPerfect_compactSupport_directImage_iff Λ j kbar i
    ((etaleModuleInverseImage.{u, 0} Λ i).mapCochainComplexPlus.obj K)).2 hZ
  have h₁ := ((etaleModuleExtensionByZero.{u, 0} Λ jU).mapCochainComplexPlus.obj
    ((etaleModuleRestriction.{u, 0} Λ jU).mapCochainComplexPlus.obj K)).property
  have h₃ := ((etaleModuleDirectImage.{u, 0} Λ i).mapCochainComplexPlus.obj
    ((etaleModuleInverseImage.{u, 0} Λ i).mapCochainComplexPlus.obj K)).property
  have hX := isPerfect_compactSupportFrobeniusCohomology_X₂ Λ f j kbar hS h₁ K.property h₃ hp₁ hp₃
  refine ⟨hX, ?_⟩
  exact (canonicalCompactSupportLefschetzNumber_X₂_eq_add Λ f j kbar p q hcard hS h₁ K.property h₃
    hp₁ hX hp₃).trans <| congrArg₂ (· + ·)
    (canonicalCompactSupportLefschetzNumber_extensionByZero_eq Λ j kbar p q hcard jU _ hp₁ hU)
    (canonicalCompactSupportLefschetzNumber_directImage_eq Λ j kbar p q hcard i _ hp₃ hZ)

end Devissage

section Local

variable (Λ : Type) [Ring Λ] {k : Type u} [Field k] [Fintype k]
  (kbar : Type u) [Field kbar] [IsAlgClosed kbar] [Algebra k kbar] (p q : ℕ) [Fact p.Prime]
  [CharP kbar p] (hcard : Fintype.card k = p ^ q)

/-- The restriction-inverse-image isomorphism commutes with the differentials. -/
private theorem inverseImage_restriction_d_comm {X U : Scheme.{u}} (jU : U ⟶ X)
    [IsOpenImmersion jU] (K : CochainComplex.Plus (EtaleModules.{u, 0} Λ X)) :
    ∀ a b, ((etaleModuleInverseImage.{u, 0} Λ jU).mapCochainComplexPlus.obj K).obj.d a b ≫
      ((etaleModuleInverseImageRestrictionIso.{u, 0} Λ jU).app (K.obj.X b)).hom =
      ((etaleModuleInverseImageRestrictionIso.{u, 0} Λ jU).app (K.obj.X a)).hom ≫
        ((etaleModuleRestriction.{u, 0} Λ jU).mapCochainComplexPlus.obj K).obj.d a b :=
  fun a b => (etaleModuleInverseImageRestrictionIso.{u, 0} Λ jU).hom.naturality (K.obj.d a b)

/-- **The local datum at a rational point is unchanged by restriction to an open**: for an open
immersion `j_U : U ⟶ X` and `x = x' ≫ j_U`, the stalk of `K|_U` at `x'` is that of `K` at `x`,
with the same geometric Frobenius. -/
theorem stalkTrace_restriction {X U : Scheme.{u}} (jU : U ⟶ X) [IsOpenImmersion jU]
    (x' : Spec (.of k) ⟶ U) (K : CochainComplex.Plus (EtaleModules.{u, 0} Λ X))
    (hX : StacksDraft.Perfect.IsPerfect
      (DerivedCategory.Q.obj (rationalPointStalkComplex.{u, 0} Λ kbar (x' ≫ jU) K))) :
    ∃ hU : StacksDraft.Perfect.IsPerfect (DerivedCategory.Q.obj (rationalPointStalkComplex.{u, 0}
        Λ kbar x' ((etaleModuleRestriction.{u, 0} Λ jU).mapCochainComplexPlus.obj K))),
      perfectDerivedTrace Λ ⟨_, hU⟩ (DerivedCategory.Q.map (rationalPointStalkFrobenius.{u, 0} Λ
          kbar p q hcard x' ((etaleModuleRestriction.{u, 0} Λ jU).mapCochainComplexPlus.obj K))) =
        perfectDerivedTrace Λ ⟨_, hX⟩ (DerivedCategory.Q.map
          (rationalPointStalkFrobenius.{u, 0} Λ kbar p q hcard (x' ≫ jU) K)) := by
  have hI := StacksDraft.Perfect.isPerfect_of_iso
    (DerivedCategory.Q.mapIso (inverseImageStalkComplexIso Λ jU kbar x' (x' ≫ jU) rfl K)) hX
  have hU := StacksDraft.Perfect.isPerfect_of_iso (DerivedCategory.Q.mapIso
    (rationalPointStalkComplexMapIso Λ kbar x'
      (M' := (etaleModuleRestriction.{u, 0} Λ jU).mapCochainComplexPlus.obj K) _
      (inverseImage_restriction_d_comm Λ jU K))).symm hI
  exact ⟨hU, ((perfectDerivedTrace_rationalPointStalkFrobenius_congr Λ kbar p q hcard x'
    (M' := (etaleModuleRestriction.{u, 0} Λ jU).mapCochainComplexPlus.obj K) _
      (inverseImage_restriction_d_comm Λ jU K) hI hU).symm.trans
    (perfectDerivedTrace_rationalPointStalkFrobenius_inverseImage Λ jU kbar x' (x' ≫ jU) rfl p q
      hcard K hI hX))⟩

/-- **The local datum at a rational point is unchanged by inverse image**: for a morphism
`g : X' ⟶ X` and `x = x' ≫ g`, the stalk of `g^{-1} K` at `x'` is that of `K` at `x`, with the
same geometric Frobenius. -/
theorem stalkTrace_inverseImage {X X' : Scheme.{u}} (g : X' ⟶ X)
    (x' : Spec (.of k) ⟶ X') (K : CochainComplex.Plus (EtaleModules.{u, 0} Λ X))
    (hX : StacksDraft.Perfect.IsPerfect
      (DerivedCategory.Q.obj (rationalPointStalkComplex.{u, 0} Λ kbar (x' ≫ g) K))) :
    ∃ hX' : StacksDraft.Perfect.IsPerfect (DerivedCategory.Q.obj (rationalPointStalkComplex.{u, 0}
        Λ kbar x' ((etaleModuleInverseImage.{u, 0} Λ g).mapCochainComplexPlus.obj K))),
      perfectDerivedTrace Λ ⟨_, hX'⟩ (DerivedCategory.Q.map (rationalPointStalkFrobenius.{u, 0} Λ
          kbar p q hcard x' ((etaleModuleInverseImage.{u, 0} Λ g).mapCochainComplexPlus.obj K))) =
        perfectDerivedTrace Λ ⟨_, hX⟩ (DerivedCategory.Q.map
          (rationalPointStalkFrobenius.{u, 0} Λ kbar p q hcard (x' ≫ g) K)) := by
  have hI := StacksDraft.Perfect.isPerfect_of_iso
    (DerivedCategory.Q.mapIso (inverseImageStalkComplexIso Λ g kbar x' (x' ≫ g) rfl K)) hX
  exact ⟨hI, perfectDerivedTrace_rationalPointStalkFrobenius_inverseImage Λ g kbar x' (x' ≫ g) rfl
    p q hcard K hI hX⟩

omit [Fintype k] in
/-- The converse transport of perfectness of a stalk along restriction to an open. -/
theorem isPerfect_stalk_of_restriction {X U : Scheme.{u}} (jU : U ⟶ X) [IsOpenImmersion jU]
    (x' : Spec (.of k) ⟶ U) (K : CochainComplex.Plus (EtaleModules.{u, 0} Λ X))
    (hU : StacksDraft.Perfect.IsPerfect (DerivedCategory.Q.obj (rationalPointStalkComplex.{u, 0}
        Λ kbar x' ((etaleModuleRestriction.{u, 0} Λ jU).mapCochainComplexPlus.obj K)))) :
    StacksDraft.Perfect.IsPerfect
      (DerivedCategory.Q.obj (rationalPointStalkComplex.{u, 0} Λ kbar (x' ≫ jU) K)) := by
  exact StacksDraft.Perfect.isPerfect_of_iso
    (DerivedCategory.Q.mapIso (inverseImageStalkComplexIso Λ jU kbar x' (x' ≫ jU) rfl K)).symm
    (StacksDraft.Perfect.isPerfect_of_iso (DerivedCategory.Q.mapIso
      (rationalPointStalkComplexMapIso Λ kbar x'
      (M' := (etaleModuleRestriction.{u, 0} Λ jU).mapCochainComplexPlus.obj K) _
      (inverseImage_restriction_d_comm Λ jU K))) hU)

omit [Fintype k] in
/-- The converse transport of perfectness of a stalk along an inverse image. -/
theorem isPerfect_stalk_of_inverseImage {X X' : Scheme.{u}} (g : X' ⟶ X)
    (x' : Spec (.of k) ⟶ X') (K : CochainComplex.Plus (EtaleModules.{u, 0} Λ X))
    (hX' : StacksDraft.Perfect.IsPerfect (DerivedCategory.Q.obj (rationalPointStalkComplex.{u, 0}
        Λ kbar x' ((etaleModuleInverseImage.{u, 0} Λ g).mapCochainComplexPlus.obj K)))) :
    StacksDraft.Perfect.IsPerfect
      (DerivedCategory.Q.obj (rationalPointStalkComplex.{u, 0} Λ kbar (x' ≫ g) K)) :=
  StacksDraft.Perfect.isPerfect_of_iso
    (DerivedCategory.Q.mapIso (inverseImageStalkComplexIso Λ g kbar x' (x' ≫ g) rfl K)).symm hX'

end Local

section Formula

variable (Λ : Type) [Ring Λ] [Finite Λ] {k : Type u} [Field k] [Fintype k]
  (kbar : Type u) [Field kbar] [IsAlgClosed kbar] [Algebra k kbar] (p q : ℕ) [Fact p.Prime]
  [CharP k p] [CharP kbar p] (hcard : Fintype.card k = p ^ q)

/-- **The trace formula for `(X, j, K)`**: `RΓ_c(X_k̄, K)` (through the compactification `j`) and
the stalks of `K` at the rational points are perfect, and

`Tr(π_X^* | RΓ_c(X_k̄, K)) = ∑_{x ∈ X(k)} Tr(π_x | K_x̄)`

in `Λ^natural`, for the canonical actions. -/
def CanonicalTraceFormula {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    (j : CompactificationOf (Over.mk f)) (K : CochainComplex.Plus (EtaleModules.{u, 0} Λ X)) :
    Prop :=
  ∃ (hX : StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj
      (compactSupportFrobeniusCohomology.{u, 0} Λ f j kbar K)))
    (hs : ∀ x : rationalPoints f, StacksDraft.Perfect.IsPerfect
      (DerivedCategory.Q.obj (rationalPointStalkComplex.{u, 0} Λ kbar x.1 K))),
    canonicalCompactSupportLefschetzNumber.{u, 0} Λ f j kbar p q hcard K hX =
      ∑ᶠ x : rationalPoints f, perfectDerivedTrace Λ ⟨_, hs x⟩
        (DerivedCategory.Q.map (rationalPointStalkFrobenius.{u, 0} Λ kbar p q hcard x.1 K))

variable {X : Scheme.{u}} {f : X ⟶ Spec (.of k)} [QuasiCompact f] [LocallyOfFiniteType f]
  (j : CompactificationOf (Over.mk f)) {U Z : Scheme.{u}} (jU : U ⟶ X) [IsOpenImmersion jU]
  (i : Z ⟶ X) [IsClosedImmersion i] (hij : Set.range jU.base = (Set.range i.base)ᶜ)

include hij in
/-- **The open and closed dévissage of the trace formula, in any dimension.**  If the trace
formula holds for `K|_U` on the open `U` and for `K|_Z` on its closed complement `Z`, through the
compactifications induced by `j`, then it holds for `K` on `X` through `j`. -/
theorem canonicalTraceFormula_of_openClosed (K : CochainComplex.Plus (EtaleModules.{u, 0} Λ X))
    (hU : CanonicalTraceFormula Λ kbar p q hcard (jU ≫ f) (j.restrictOpen jU)
      ((etaleModuleRestriction.{u, 0} Λ jU).mapCochainComplexPlus.obj K))
    (hZ : CanonicalTraceFormula Λ kbar p q hcard (i ≫ f) (j.restrictClosed i)
      ((etaleModuleInverseImage.{u, 0} Λ i).mapCochainComplexPlus.obj K)) :
    CanonicalTraceFormula Λ kbar p q hcard f j K := by
  classical
  obtain ⟨hUp, hUs, hUe⟩ := hU
  obtain ⟨hZp, hZs, hZe⟩ := hZ
  obtain ⟨hX, hXe⟩ := canonicalCompactSupportLefschetzNumber_eq_add_openClosed Λ j kbar p q
    hcard jU i hij K hUp hZp
  let E := rationalPointsEquivSum f i jU hij (fU := jU ≫ f) (fZ := i ≫ f) rfl rfl
  have hs : ∀ x : rationalPoints f, StacksDraft.Perfect.IsPerfect
      (DerivedCategory.Q.obj (rationalPointStalkComplex.{u, 0} Λ kbar x.1 K)) := by
    intro x
    obtain ⟨y, rfl⟩ := E.surjective x
    rcases y with y | y
    · exact isPerfect_stalk_of_restriction Λ kbar jU y.1 K (hUs y)
    · exact isPerfect_stalk_of_inverseImage Λ kbar i y.1 K (hZs y)
  refine ⟨hX, hs, ?_⟩
  have : Finite (rationalPoints f) := finite_rationalPoints f
  have : Finite (rationalPoints (jU ≫ f) ⊕ rationalPoints (i ≫ f)) := Finite.of_equiv _ E.symm
  have : Finite (rationalPoints (jU ≫ f)) :=
    Finite.of_injective (β := rationalPoints (jU ≫ f) ⊕ rationalPoints (i ≫ f)) _
      Sum.inl_injective
  have : Finite (rationalPoints (i ≫ f)) :=
    Finite.of_injective (β := rationalPoints (jU ≫ f) ⊕ rationalPoints (i ≫ f)) _
      Sum.inr_injective
  let := Fintype.ofFinite (rationalPoints (jU ≫ f))
  let := Fintype.ofFinite (rationalPoints (i ≫ f))
  rw [hXe, hUe, hZe, ← finsum_comp_equiv E, finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype,
    finsum_eq_sum_of_fintype, Fintype.sum_sum_type]
  congr 1
  · refine Fintype.sum_congr _ _ fun y => ?_
    obtain ⟨h', he⟩ := stalkTrace_restriction Λ kbar p q hcard jU y.1 K (hs (E (Sum.inl y)))
    exact (perfectDerivedTrace_congr Λ _ _ (Iso.refl _) _ _ (by simp)).trans he
  · refine Fintype.sum_congr _ _ fun y => ?_
    obtain ⟨h', he⟩ := stalkTrace_inverseImage Λ kbar p q hcard i y.1 K (hs (E (Sum.inr y)))
    exact (perfectDerivedTrace_congr Λ _ _ (Iso.refl _) _ _ (by simp)).trans he

end Formula

end Stacks.EtaleCohomology

end
