module

public import StacksFrontier.AlgebraicGeometry.AmplePredicateBridge.Basic
public import StacksFrontier.AlgebraicGeometry.Divisors.AmpleFamilyRegular
public import StacksFrontier.AlgebraicGeometry.InvertibleDual.SectionIdeal
public import StacksFrontier.AlgebraicGeometry.NonvanishingAffineIntersection.Basic
public import StacksFrontier.AlgebraicGeometry.Perfect.ResolutionPropertyAmpleFamily
public import StacksFrontier.AlgebraicGeometry.Perfect.ResolutionPropertyIdealCovering
public import StacksFrontier.AlgebraicGeometry.Perfect.ResolutionPropertyIdealCoveringSubstantial
public import StacksFrontier.AlgebraicGeometry.Perfect.ResolutionPropertyRegular
public import StacksFrontier.AlgebraicGeometry.ProjRepresentsF1.TwistPowers
public import StacksFrontier.AlgebraicGeometry.Properties.ExtendFiniteType.QuasiCompactOpenIdeal
import StacksCore.Tactic.EgaSgaAttribute

/-!
# An ample family of invertible modules and the resolution property

Let `X` be a scheme carrying an ample family of invertible modules in the sense of
`AlgebraicGeometry.Scheme.IsAmpleFamily` ([Stacks, Tag 0FXR]).  Then `X` is quasi-separated, it
admits a finite affine open covering together with finite type quasi-coherent sheaves of ideals
cutting out the complements of its members, which is hypothesis (1) and (2) of
[Stacks, Tag 0F89], and it has the resolution property, which is [Stacks, Tag 0GMM].

## Main results

* `AlgebraicGeometry.Scheme.IsAmpleFamily.quasiSeparatedSpace`: **a scheme with an ample family
  of invertible modules is quasi-separated.**
* `AlgebraicGeometry.Scheme.IsAmpleFamily.exists_isIdealAffineCovering`: such a scheme carries
  the data `AlgebraicGeometry.IsIdealAffineCovering`, the hypotheses of [Stacks, Tag 0F89].
* `AlgebraicGeometry.Scheme.IsAmpleFamily.hasResolutionProperty`: **[Stacks, Tag 0GMM]**, a scheme
  with an ample family of invertible modules has the resolution property.
* `AlgebraicGeometry.IsRegular.hasResolutionProperty`: **[Stacks, Tag 0F8A]**, a quasi-compact
  regular scheme with affine diagonal has the resolution property.

## The argument

Quasi-compactness is a field of `AlgebraicGeometry.Scheme.IsAmpleFamily`, and
`AlgebraicGeometry.Scheme.exists_finite_affine_nonvanishing_cover` turns the pointwise condition
into a finite covering `X = U 0 ∪ ⋯ ∪ U (m - 1)` by affine opens, each the nonvanishing locus of
a global section of a positive tensor power of a member of the family.  Those tensor powers are
invertible (`Stacks.AlgebraicGeometry.ProjRepresentsF1.isInvertible_tensorPowerNat`), so
[Stacks, Tag 01PV] — `Stacks.NonvanishingAffineIntersection.isAffineOpen_inf_nonvanishingOpen` —
makes every intersection `U k ⊓ U l` affine, hence quasi-compact, and [Stacks, Tag 01KO] in the
form of Mathlib's `AlgebraicGeometry.Scheme.quasiSeparatedSpace_of_isOpenCover` gives
quasi-separatedness.  With `X` quasi-compact and quasi-separated, [Stacks, Tag 01PH] in the form
`AlgebraicGeometry.exists_isFiniteType_idealSheafData_support_eq_compl` produces for each `U k` a
finite type quasi-coherent sheaf of ideals whose vanishing locus is its complement.

For [Stacks, Tag 0GMM] the ideals are instead those cut out by the sections themselves: the
ideal attached to a global section `s` of an invertible module `M` is the image of evaluation
at `s`, `AlgebraicGeometry.Scheme.Modules.evalGlobalHom : M^∨ ⟶ 𝒪_X`.  Its source is
invertible, hence finite locally free
(`AlgebraicGeometry.Scheme.Modules.isFiniteLocallyFree_dual`), and its vanishing locus is the
complement of `X_s`
(`AlgebraicGeometry.Scheme.Modules.coe_support_idealSheafDataOfHom_evalGlobalHom`).  The
covering by the `X_s` with these ideals is fed to the substantial direction of
[Stacks, Tag 0F89] in the form
`AlgebraicGeometry.hasResolutionProperty_of_coe_support_idealSheafDataOfHom`.

## Implementation notes

**Two spellings of the nonvanishing locus meet here.**  `AlgebraicGeometry.Scheme.IsAmpleFamily`
is stated over `AlgebraicGeometry.Scheme.nonvanishingSet`, the ringed-space locus of a section in
the sense of `PresheafOfModules.sections`, while [Stacks, Tag 01PV] is stated over
`Stacks.NonvanishingOpen.nonvanishingOpen`, the bundled open attached to a section over `⊤`.
`AlgebraicGeometry.Scheme.IsAmpleFamily.nonvanishingSet_eq_coe_nonvanishingOpen` identifies them;
it is `Stacks.AmplePredicateBridge.coe_nonvanishingOpen_eval` read through the definitional
equality `AlgebraicGeometry.Scheme.nonvanishingSet_eq`.

## References

* [Stacks Project, Tag 0F89](https://stacks.math.columbia.edu/tag/0F89)
* [Stacks Project, Tag 0F8A](https://stacks.math.columbia.edu/tag/0F8A)
* [Stacks Project, Tag 0FXR](https://stacks.math.columbia.edu/tag/0FXR)
* [Stacks Project, Tag 0GMM](https://stacks.math.columbia.edu/tag/0GMM)
* [Stacks Project, Tag 01PV](https://stacks.math.columbia.edu/tag/01PV)
* [Stacks Project, Tag 01PH](https://stacks.math.columbia.edu/tag/01PH)
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite

universe u v

namespace AlgebraicGeometry.Scheme.IsAmpleFamily

variable {ι : Type v} {X : Scheme.{u}} {L : ι → X.Modules}

/-- Every tensor power of a member of an ample family of invertible modules is invertible. -/
theorem isInvertibleModule_tensorPow (hL : X.IsAmpleFamily L) (i : ι) (n : ℕ) :
    Stacks.Ample.IsInvertibleModule X (X.tensorPow (L i) n) :=
  (Stacks.InvertiblePullback.stacksIsInvertible_iff_algebraicGeometryIsInvertible
    X.presheaf X.ringCatSheaf.2 _).mp
      (Stacks.AlgebraicGeometry.ProjRepresentsF1.isInvertible_tensorPowerNat (L i)
        (hL.isInvertible i) n)

/-- The nonvanishing locus of a global section of an invertible module on a scheme is the open
subset of [Stacks, Tag 01CY] attached to the section it takes over `⊤`. -/
theorem nonvanishingSet_eq_coe_nonvanishingOpen (M : X.Modules)
    [Stacks.Ample.IsInvertibleModule X M] (s : M.sections) :
    X.nonvanishingSet M s =
      (Stacks.NonvanishingOpen.nonvanishingOpen X M (s.eval (op ⊤)) : Set X) :=
  Stacks.AmplePredicateBridge.coe_nonvanishingOpen_eval X M s

/-- An open subset equal to the nonvanishing locus of a section is the open subset attached to the
section it takes over `⊤`. -/
private theorem coe_eq_coe_nonvanishingOpen {M : X.Modules} [Stacks.Ample.IsInvertibleModule X M]
    {s : M.sections} {U : X.Opens} (h : (U : Set X) = X.nonvanishingSet M s) :
    (U : Set X) = (Stacks.NonvanishingOpen.nonvanishingOpen X M (s.eval (op ⊤)) : Set X) :=
  h.trans (nonvanishingSet_eq_coe_nonvanishingOpen _ _)

/-- **A scheme carrying an ample family of invertible modules is quasi-separated.** The members
of the finite affine covering it supplies are nonvanishing loci of sections of invertible
modules, so their pairwise intersections are affine by [Stacks, Tag 01PV]. -/
theorem quasiSeparatedSpace (hL : X.IsAmpleFamily L) : QuasiSeparatedSpace X := by
  obtain ⟨m, i, n, U, s, hcover, hdata⟩ :=
    AlgebraicGeometry.Scheme.exists_finite_affine_nonvanishing_cover X L hL
  refine Scheme.quasiSeparatedSpace_of_isOpenCover U hcover (fun k => (hdata k).2.1) ?_
  intro k l
  have hinv := hL.isInvertibleModule_tensorPow (i l) (n l)
  have hinter : (U k : Set X) ∩ (U l : Set X) =
      ((U k ⊓ Stacks.NonvanishingOpen.nonvanishingOpen X (X.tensorPow (L (i l)) (n l))
        ((s l).eval (op ⊤)) : X.Opens) : Set X) := by
    rw [coe_eq_coe_nonvanishingOpen (hdata l).2.2]
    rfl
  rw [hinter]
  exact (Stacks.NonvanishingAffineIntersection.isAffineOpen_inf_nonvanishingOpen
    (X.tensorPow (L (i l)) (n l)) ((s l).eval (op ⊤)) (hdata k).2.1).isCompact

/-- **The hypotheses of [Stacks, Tag 0F89] on a scheme with an ample family of invertible
modules.** Such a scheme has a finite affine open covering, and the complement of each member is
the vanishing locus of a finite type quasi-coherent sheaf of ideals. -/
theorem exists_isIdealAffineCovering (hL : X.IsAmpleFamily L) :
    ∃ (m : ℕ) (U : Fin m → X.Opens) (J : Fin m → X.IdealSheafData),
      IsIdealAffineCovering X U J := by
  have hcompact : CompactSpace X := hL.compactSpace
  have hqs : QuasiSeparatedSpace X := hL.quasiSeparatedSpace
  obtain ⟨m, i, n, U, s, hcover, hdata⟩ :=
    AlgebraicGeometry.Scheme.exists_finite_affine_nonvanishing_cover X L hL
  choose J hJft hJsupport using fun k : Fin m =>
    exists_isFiniteType_idealSheafData_support_eq_compl (U k) (hdata k).2.1.isCompact
  exact ⟨m, U, J, isIdealAffineCovering_of_isFiniteType U J (fun k => (hdata k).2.1)
    hcover.iSup_eq_top (fun k V => hJft k V) hJsupport⟩

end AlgebraicGeometry.Scheme.IsAmpleFamily

namespace AlgebraicGeometry

open Stacks.AlgebraicGeometry.IdealPowerColimit

/-- **The substantial direction of [Stacks, Tag 0F89].** A scheme carrying a finite affine open
covering and finite type quasi-coherent sheaves of ideals whose vanishing loci are the
complements of its members has the resolution property as soon as each of those ideals is the
quotient of a finite locally free module.

This is the converse of
`AlgebraicGeometry.exists_isFiniteLocallyFree_epi_of_isIdealAffineCovering`, which is the
direction of Tag 0F89 that this development proves.  It is stated for all schemes at once, so
that assuming it is assuming the machinery of Tag 0F89 rather than the resolution property of
any particular scheme. -/
abbrev IdealCoveringImpliesResolutionProperty : Prop :=
  ∀ (X : Scheme.{u}) (m : ℕ) (U : Fin m → X.Opens) (I : Fin m → X.IdealSheafData),
    IsIdealAffineCovering X U I →
    (∀ j, ∃ (E : X.Modules)
      (_ : SheafOfModules.IsFiniteLocallyFree (R := X.ringCatSheaf) E)
      (q : E ⟶ idealPow (I j) 1), Epi q) →
    HasResolutionProperty X

/-- **The sheaf of ideals cut out by a global section of an invertible module.** For a global
section `s` of an invertible `𝒪_X`-module `M` there is a quasi-coherent sheaf of ideals which
is of finite type, is the quotient of a finite locally free module, and whose vanishing locus
is the complement of the nonvanishing locus `X_s`.

It is the image of `s : M^∨ ⟶ 𝒪_X`, a quotient of the invertible — hence finite locally free —
module `M^∨`; it is of finite type because `M^∨` is, and it is the unit ideal exactly at the
points where `s` generates `M`, which are the points of `X_s`.  This is the construction with
which [Stacks, Tag 0GMM] enters [Stacks, Tag 0F89]. -/
abbrev ExistsSectionImageIdeal : Prop :=
  ∀ (X : Scheme.{u}) (M : X.Modules), Stacks.Ample.IsInvertibleModule X M →
    ∀ s : M.sections, ∃ I : X.IdealSheafData,
      ((I.support : Set X) = (X.nonvanishingSet M s)ᶜ) ∧ (idealPow I 1).IsFiniteType ∧
        ∃ (E : X.Modules)
          (_ : SheafOfModules.IsFiniteLocallyFree (R := X.ringCatSheaf) E)
          (q : E ⟶ idealPow I 1), Epi q

/-- **[Stacks, Tag 0GMM].** A scheme carrying an ample family of invertible modules has the
resolution property.

The ample family supplies a finite covering of `X` by affine opens `U k = X_{s k}`, the
nonvanishing loci of global sections `s k` of positive tensor powers `M k` of members of the
family.  The image of evaluation at `s k`, a morphism `M k ^∨ ⟶ 𝒪_X` out of the invertible,
hence finite locally free, dual, is a finite type quasi-coherent sheaf of ideals whose vanishing
locus is the complement of `U k`, and it is a quotient of `M k ^∨`.  The substantial direction
of [Stacks, Tag 0F89] then gives the resolution property. -/
@[stacks 0GMM, ega "III 7.7.9" "(ii)"]
theorem Scheme.IsAmpleFamily.hasResolutionProperty {ι : Type v} {X : Scheme.{u}}
    {L : ι → X.Modules} (hL : X.IsAmpleFamily L) : HasResolutionProperty X := by
  obtain ⟨m, i, n, U, s, hcover, hdata⟩ :=
    AlgebraicGeometry.Scheme.exists_finite_affine_nonvanishing_cover X L hL
  have hinv := fun k => hL.isInvertibleModule_tensorPow (i k) (n k)
  refine hasResolutionProperty_of_coe_support_idealSheafDataOfHom U
    (fun k => Scheme.Modules.dual (X.tensorPow (L (i k)) (n k)))
    (fun k => have := hinv k; Scheme.Modules.isFiniteLocallyFree_dual _)
    (fun k => Scheme.Modules.evalGlobalHom _ ((s k).eval (op ⊤)))
    (fun k => have := hinv k; inferInstance)
    (fun k => (hdata k).2.1) hcover.iSup_eq_top (fun k => ?_)
  have := hinv k
  refine (Scheme.Modules.coe_support_idealSheafDataOfHom_evalGlobalHom _ _).trans ?_
  rw [IsAmpleFamily.coe_eq_coe_nonvanishingOpen (hdata k).2.2]
  rfl

/-- **[Stacks, Tag 0F8A].** A quasi-compact regular scheme with affine diagonal has the resolution
property.

Quasi-compactness is `CompactSpace X`, the affine diagonal is
`IsAffineHom (pullback.diagonal (terminal.from X))`, and regularity is
`AlgebraicGeometry.IsRegular` ([Stacks, Tag 02IS]); these are exactly the conditions of the
source.

The proof is the one of `StacksFrontier/AlgebraicGeometry/Perfect/ResolutionPropertyRegular.lean`:
regularity gives Noetherianness and unique
factorization in the local rings, a regular scheme is normal so every point lies in a dense affine
open, [Stacks, Tag 0EGJ] cuts out the complement of each of those by an effective Cartier divisor,
quasi-compactness makes the covering finite, and
`AlgebraicGeometry.hasResolutionProperty_of_isNoetherian_of_isEffectiveCartierDivisor` concludes.
-/
@[stacks 0F8A, sga "3 VIB 13.3" "more general"]
theorem IsRegular.hasResolutionProperty (X : Scheme.{u}) [CompactSpace X]
    [IsAffineHom
      (CategoryTheory.Limits.pullback.diagonal (CategoryTheory.Limits.terminal.from X))]
    (hX : IsRegular X) : HasResolutionProperty X := by
  classical
  have hreg := ((isRegular_tfae X).out 1 2).mp hX
  have : IsLocallyNoetherian X := hreg.1
  have : IsNoetherian X := ⟨⟩
  have hUFD : ∀ y : X, UniqueFactorizationMonoid (X.presheaf.stalk y) := fun y =>
    have := hreg.2 y
    IsRegularLocalRing.uniqueFactorizationMonoid _
  choose U hUaff hUdense hUmem using
    exists_isAffineOpen_dense_mem_of_isNormal X (isNormal_of_isRegular X hX)
  choose D hDeff hDsupp using fun x : X =>
    exists_effectiveCartierDivisor_compl_affineOpen X (U x) (hUaff x) (hUdense x)
      fun y _ => hUFD y
  have hcov : (Set.univ : Set X) ⊆ ⋃ x, (U x : Set X) :=
    fun x _ => Set.mem_iUnion.mpr ⟨x, hUmem x⟩
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x : X => (U x : Set X))
    (fun x => (U x).isOpen) hcov
  let ξ : Fin t.card → X := fun k => (t.equivFin.symm k).1
  refine hasResolutionProperty_of_isNoetherian_of_isEffectiveCartierDivisor
    (fun k => U (ξ k)) (fun k => D (ξ k)) (fun k => hUaff (ξ k)) ?_ (fun k => hDeff (ξ k))
    (fun k => hDsupp (ξ k))
  refine le_antisymm (iSup_le fun _ => le_top) ?_
  intro x _
  obtain ⟨y, hy, hxy⟩ : ∃ y ∈ t, x ∈ (U y : Set X) := by
    simpa only [Set.mem_iUnion, Finset.mem_coe, exists_prop] using ht (Set.mem_univ x)
  exact Opens.mem_iSup.mpr ⟨t.equivFin ⟨y, hy⟩, by simpa [ξ] using hxy⟩

/-- A scheme carrying an ample family of invertible modules has the resolution property, given
the statement `AlgebraicGeometry.IdealCoveringImpliesResolutionProperty` (`h0F89`) and the
statement `AlgebraicGeometry.ExistsSectionImageIdeal` (`hideal`).

The covering of `X` comes from the ample family, through
`AlgebraicGeometry.Scheme.exists_finite_affine_nonvanishing_cover`; `hideal` supplies for the
sections cutting out its members finite type ideals with the required vanishing loci, each a
quotient of a finite locally free module, and `h0F89` concludes.  Without `h0F89` and `hideal`
this is `AlgebraicGeometry.Scheme.IsAmpleFamily.hasResolutionProperty`. -/
theorem hasResolutionProperty_of_isAmpleFamily
    (h0F89 : IdealCoveringImpliesResolutionProperty.{u})
    (hideal : ExistsSectionImageIdeal.{u}) {ι : Type v} {X : Scheme.{u}}
    {L : ι → X.Modules} (hL : X.IsAmpleFamily L) : HasResolutionProperty X := by
  obtain ⟨m, i, n, U, s, hcover, hdata⟩ :=
    AlgebraicGeometry.Scheme.exists_finite_affine_nonvanishing_cover X L hL
  choose J hJsupport hJft hJquot using fun k : Fin m =>
    hideal X (X.tensorPow (L (i k)) (n k))
      (hL.isInvertibleModule_tensorPow (i k) (n k)) (s k)
  refine h0F89 X m U J ⟨fun k => (hdata k).2.1, hcover.iSup_eq_top, hJft, fun k => ?_⟩ hJquot
  rw [hJsupport k, (hdata k).2.2]

/-- A quasi-compact regular scheme with affine diagonal has the resolution property, given the
statements `AlgebraicGeometry.IdealCoveringImpliesResolutionProperty` (`h0F89`) and
`AlgebraicGeometry.ExistsSectionImageIdeal` (`hideal`).

Such a scheme carries an ample family of invertible modules
(`AlgebraicGeometry.exists_isAmpleFamily_of_isRegular`), to which
`AlgebraicGeometry.hasResolutionProperty_of_isAmpleFamily` applies.  Without `h0F89` and
`hideal` this is `AlgebraicGeometry.IsRegular.hasResolutionProperty`. -/
theorem hasResolutionProperty_of_isRegular
    (h0F89 : IdealCoveringImpliesResolutionProperty.{u})
    (hideal : ExistsSectionImageIdeal.{u}) (X : Scheme.{u}) [CompactSpace X]
    [IsAffineHom
      (CategoryTheory.Limits.pullback.diagonal (CategoryTheory.Limits.terminal.from X))]
    (hX : IsRegular X) : HasResolutionProperty X := by
  obtain ⟨_, _, hL⟩ := exists_isAmpleFamily_of_isRegular X hX
  exact hasResolutionProperty_of_isAmpleFamily h0F89 hideal hL

end AlgebraicGeometry

end
