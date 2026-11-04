module

public import StacksFrontier.AlgebraicGeometry.Divisors.SectionContractionPairing
public import StacksFrontier.AlgebraicGeometry.Spaces.CanonicalSectionRegular
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedSubspaceFromQuasicoherentIdeal
public import StacksFrontier.AlgebraicGeometry.Spaces.InvertibleQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.ZeroSchemeOfCanonicalSection
public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentCokernels

/-!
# A regular section cuts out a unique effective Cartier divisor, and the bijection of Stacks 0847

Let `X` be an algebraic space over a scheme `S`.  For an effective Cartier divisor `D ⊆ X` the
canonical section `1_D` of `𝒪_X(D)` is a regular section, which is part (1) of Stacks 0847 and
is `AlgebraicGeometry.Space.canonicalSection_isRegular`.  This file proves the converse
direction, part (2) of the same tag: a regular global section `s` of an invertible
`𝒪_X`-module `L` cuts out a *unique* effective Cartier divisor `D = Z(s) ⊆ X`, carrying a
*unique* isomorphism `𝒪_X(D) ≅ L` which takes the canonical section `1_D` to `s`.  Part (3), the
assertion that the two constructions `D ↦ (𝒪_X(D), 1_D)` and `(L, s) ↦ Z(s)` are mutually
inverse, follows at once and is proved here too.

## Main results

* `AlgebraicGeometry.Space.exists_unique_isEffectiveCartierDivisor_iso_canonicalSectionHom_comp`
  is **Stacks 0847, part (2)**.
* `AlgebraicGeometry.Space.effectiveCartierDivisor_regularSectionPair_mutuallyInverse` is
  **Stacks 0847, part (3)**.

## Implementation notes

Contracting the inverse `L^{⊗ -1}` with `s` gives a morphism `L^{⊗ -1} ⟶ 𝒪_X`, and it is a
monomorphism exactly because `s` is regular: tensoring by the invertible module `L^{⊗ -1}` is an
autoequivalence of `𝒪_X`-modules, and it carries multiplication by `s` to this contraction up to
the unit and braiding constraints.  This is
`Stacks.SheafOfModules.Invertible.mono_sectionContraction`, and no local trivialization of `L`
enters, exactly as none enters in the proof of part (1).

A monomorphism of sheaves of modules is an isomorphism onto its image subsheaf, so the image of
the contraction is a sheaf of ideals of `𝒪_X` isomorphic to `L^{⊗ -1}`.  It is therefore
invertible, hence finite locally free of rank one, hence quasi-coherent, and so by the
surjectivity half of Stacks 03MB it is the defining ideal sheaf `𝓘_D` of a closed subspace
`D ⊆ X`.  Invertibility of `𝓘_D` is precisely the assertion that `D` is an effective Cartier
divisor.

The isomorphism `𝒪_X(D) ≅ L` is then the one matching the two pairings against `𝓘_D`: the
evaluation pairing `𝒪_X(D) ⊗ 𝓘_D ≅ 𝒪_X` of Stacks 0841, and the pairing `L ⊗ 𝓘_D ≅ 𝒪_X` which
contracts the second factor into `L^{⊗ -1}` and evaluates.  Two modules paired against one
invertible module are isomorphic compatibly with the pairings, and the isomorphism carries `1_D`
to `s` because both sections curry to the inclusion `𝓘_D ⟶ 𝒪_X` — the canonical section by
`AlgebraicGeometry.Space.tensorPairing_canonicalSection_tmul`, and `s` because the identification
of `𝓘_D` with `L^{⊗ -1}` carries that inclusion to contraction with `s`, which
`Stacks.SheafOfModules.Invertible.sectionContraction_app` evaluates on the sections.  This is
`Stacks.SheafOfModules.Invertible.exists_iso_of_sectionContraction_eq`, and it is used in place
of `Stacks.SheafOfModules.Invertible.isoOfTensorUnit`, which cancels a tensor
factor with no statement about the sections it matches.

The two uniqueness clauses are
`AlgebraicGeometry.Space.eq_zeroScheme_of_canonicalSectionHom_comp` and
`AlgebraicGeometry.Space.iso_eq_of_canonicalSectionHom_comp_eq`, and the first of them also
identifies the divisor produced here as the zero scheme `Z(s)` of Stacks 0845.

The bare existence half of part (2) is
`AlgebraicGeometry.Space.exists_isEffectiveCartierDivisor_associatedInvertibleSheaf_iso` in
`StacksFrontier.AlgebraicGeometry.Spaces.RegularSectionEffectiveCartier`; this module adds the two
uniqueness clauses, the identification of the divisor with `Z(s)`, and part (3), which need the
zero scheme of Stacks 0845 and its comparison with the canonical section.

## References

* [Stacks Project, Tag 0847](https://stacks.math.columbia.edu/tag/0847)
* [Stacks Project, Tag 0841](https://stacks.math.columbia.edu/tag/0841)
* [Stacks Project, Tag 0843](https://stacks.math.columbia.edu/tag/0843)
* [Stacks Project, Tag 0845](https://stacks.math.columbia.edu/tag/0845)
* [Stacks Project, Tag 083B](https://stacks.math.columbia.edu/tag/083B)
* [Stacks Project, Tag 03MB](https://stacks.math.columbia.edu/tag/03MB)
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory Opposite
open Stacks.SheafOfModules.Invertible
open Stacks.SheafOfModules.TensorSheafification

namespace AlgebraicGeometry.Space

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (X : AlgebraicSpaces B S hS)

/-- **The closed subspace cut out by a regular section, with its defining ideal identified with
`L^{⊗ -1}`.**  Contraction with a regular global section `s` of an invertible `𝒪_X`-module `L` is
a monomorphism `L^{⊗ -1} ⟶ 𝒪_X`, so it identifies `L^{⊗ -1}` with its image, a quasi-coherent
sheaf of ideals of `𝒪_X`, which by Stacks 03MB is the defining ideal sheaf of a closed subspace
`D ⊆ X`.  The identification carries the inclusion `𝓘_D ⟶ 𝒪_X` to the contraction, which is what
later pins down the section matched by the isomorphism `𝒪_X(D) ≅ L`. -/
private theorem exists_iso_idealSheaf_inverseSheaf
    (L : SheafOfModules.{u} (structureRingSheaf B S hS X))
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible (structureCommRings B S hS X)
      (structureRingSheaf B S hS X).property L)
    (s : L.sections) (hmono : Mono (L.unitHomEquiv.symm s)) :
    ∃ (D : ClosedSubspaces B S hS X.1) (_ : IsEffectiveCartierDivisor B S hS X D)
      (h₀ : idealSheafOfModules B S hS X D ≅
        inverseSheaf (structureCommRings B S hS X) (structureRingSheaf B S hS X).property L),
      h₀.hom ≫ sectionContraction (structureCommRings B S hS X)
          (structureRingSheaf B S hS X).property L s = (definingIdealSheaf B S hS X D).ι := by
  have := hL
  have hinvinv : AlgebraicGeometry.SheafOfModules.IsInvertible (structureCommRings B S hS X)
      (structureRingSheaf B S hS X).property (inverseSheaf (structureCommRings B S hS X)
        (structureRingSheaf B S hS X).property L) :=
    inverseSheaf_isInvertible (structureCommRings B S hS X)
      (structureRingSheaf B S hS X).property L
  have := hinvinv
  have hqcinv : (inverseSheaf (structureCommRings B S hS X)
      (structureRingSheaf B S hS X).property L).IsQuasicoherentOnSite :=
    isQuasicoherentOnSite_of_isInvertible B S hS X _ hinvinv
  have hqc : (sectionIdealSubmodule (structureCommRings B S hS X)
      (structureRingSheaf B S hS X).property L s).toSheafOfModules.IsQuasicoherentOnSite :=
    SheafOfModules.IsQuasicoherentOnSite.of_iso
      (inverseSheafIsoSectionIdeal (structureCommRings B S hS X)
        (structureRingSheaf B S hS X).property L s hmono) hqcinv
  obtain ⟨D, hDN⟩ := exists_definingIdealSheaf_eq_of_isQuasicoherentOnSite B S hS X
    (sectionIdealSubmodule (structureCommRings B S hS X)
      (structureRingSheaf B S hS X).property L s) hqc
  have key : ∀ (T : (SheafOfModules.unit (structureRingSheaf B S hS X)).Submodule),
      definingIdealSheaf B S hS X D = T →
      ∀ e : inverseSheaf (structureCommRings B S hS X)
        (structureRingSheaf B S hS X).property L ≅ T.toSheafOfModules,
      e.hom ≫ T.ι = sectionContraction (structureCommRings B S hS X)
          (structureRingSheaf B S hS X).property L s →
      ∃ (_ : IsEffectiveCartierDivisor B S hS X D)
        (h₀ : idealSheafOfModules B S hS X D ≅ inverseSheaf (structureCommRings B S hS X)
          (structureRingSheaf B S hS X).property L),
        h₀.hom ≫ sectionContraction (structureCommRings B S hS X)
          (structureRingSheaf B S hS X).property L s = (definingIdealSheaf B S hS X D).ι := by
    intro T hTe e he
    subst hTe
    refine ⟨isInvertible_of_iso (structureCommRings B S hS X)
      (structureRingSheaf B S hS X).property e, e.symm, ?_⟩
    refine Eq.trans (congrArg (fun z => e.symm.hom ≫ z) he.symm) ?_
    exact e.inv_hom_id_assoc _
  exact ⟨D, key _ hDN
    (inverseSheafIsoSectionIdeal (structureCommRings B S hS X)
      (structureRingSheaf B S hS X).property L s hmono)
    (inverseSheafIsoSectionIdeal_hom_ι (structureCommRings B S hS X)
      (structureRingSheaf B S hS X).property L s hmono)⟩

/-- **Stacks 0847, part (2).**  Let `X` be an algebraic space over a scheme `S` and let `L` be an
invertible `𝒪_X`-module with a regular global section `s`.  Then there is a *unique* effective
Cartier divisor `D ⊆ X`, namely the zero scheme `Z(s)` of Stacks 0845, carrying a *unique*
isomorphism `𝒪_X(D) ≅ L` which takes the canonical section `1_D` of `𝒪_X(D)` to `s`.

Contraction with `s` is a monomorphism `L^{⊗ -1} ⟶ 𝒪_X` whose image is a quasi-coherent sheaf of
ideals isomorphic to `L^{⊗ -1}`; by Stacks 03MB that sheaf of ideals is the defining ideal sheaf
`𝓘_D` of a closed subspace `D`, which is therefore an effective Cartier divisor.  The
identification of `𝓘_D` with `L^{⊗ -1}` carries the inclusion `𝓘_D ⟶ 𝒪_X` to contraction with
`s`, so the pairing `L ⊗ 𝓘_D ≅ 𝒪_X` it induces curries `s` to that inclusion, exactly as the
evaluation pairing `𝒪_X(D) ⊗ 𝓘_D ≅ 𝒪_X` curries `1_D`; the isomorphism matching the two pairings
therefore carries `1_D` to `s`.  Uniqueness of the divisor is
`AlgebraicGeometry.Space.eq_zeroScheme_of_canonicalSectionHom_comp`, which also identifies it as
`Z(s)`, and uniqueness of the isomorphism is
`AlgebraicGeometry.Space.iso_eq_of_canonicalSectionHom_comp_eq`. -/
@[stacks 0847 "part (2): a regular global section of an invertible module cuts out a unique \
effective Cartier divisor, the zero scheme of the section, carrying a unique isomorphism from \
its associated invertible sheaf to the module which takes the canonical section to the given \
section; with no assumed inputs"]
theorem exists_unique_isEffectiveCartierDivisor_iso_canonicalSectionHom_comp
    (L : SheafOfModules.{u} (structureRingSheaf B S hS X))
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible (structureCommRings B S hS X)
      (structureRingSheaf B S hS X).property L)
    (s : L.sections)
    (hs : AlgebraicGeometry.IsRegularSection (structureCommRings B S hS X)
      (structureRingSheaf B S hS X).property s) :
    ∃ (D : ClosedSubspaces B S hS X.1) (hD : IsEffectiveCartierDivisor B S hS X D)
      (i : associatedInvertibleSheaf B S hS X D hD ≅ L),
      D = zeroScheme B S hS X L s ∧
      canonicalSectionHom B S hS X D hD ≫ i.hom = L.unitHomEquiv.symm s ∧
      (∀ (D' : ClosedSubspaces B S hS X.1) (hD' : IsEffectiveCartierDivisor B S hS X D')
          (i' : associatedInvertibleSheaf B S hS X D' hD' ≅ L),
        canonicalSectionHom B S hS X D' hD' ≫ i'.hom = L.unitHomEquiv.symm s → D' = D) ∧
      ∀ i' : associatedInvertibleSheaf B S hS X D hD ≅ L,
        canonicalSectionHom B S hS X D hD ≫ i'.hom = L.unitHomEquiv.symm s → i' = i := by
  have := hL
  have hmono : Mono (L.unitHomEquiv.symm s) := hs
  obtain ⟨D, hD, h0, hincl⟩ := exists_iso_idealSheaf_inverseSheaf B S hS X L hL s hmono
  have hDinv : AlgebraicGeometry.SheafOfModules.IsInvertible (structureCommRings B S hS X)
      (structureRingSheaf B S hS X).property (idealSheafOfModules B S hS X D) := hD
  have := hDinv
  obtain ⟨i, hi⟩ := Stacks.SheafOfModules.Invertible.exists_iso_of_sectionContraction_eq
    (structureCommRings B S hS X) (structureRingSheaf B S hS X).property L
    (idealSheafOfModules B S hS X D) (associatedInvertibleSheaf B S hS X D hD)
    (definingIdealSheaf B S hS X D).ι s h0 hincl
    (associatedInvertibleSheafEvaluation B S hS X D hD) (canonicalSection B S hS X D hD)
    (tensorPairing_canonicalSection_tmul B S hS X D hD)
  have hcomp : canonicalSectionHom B S hS X D hD ≫ i.hom = L.unitHomEquiv.symm s :=
    (SheafOfModules.unitHomEquiv_symm_comp (canonicalSection B S hS X D hD) i.hom).trans
      (congrArg L.unitHomEquiv.symm hi)
  have hDz : D = zeroScheme B S hS X L s :=
    eq_zeroScheme_of_canonicalSectionHom_comp B S hS X D hD L s i hcomp
  exact ⟨D, hD, i, hDz, hcomp,
    fun D' hD' i' hi' =>
      (eq_zeroScheme_of_canonicalSectionHom_comp B S hS X D' hD' L s i' hi').trans hDz.symm,
    fun i' hi' => iso_eq_of_canonicalSectionHom_comp_eq B S hS X D hD L s i' i hi' hcomp⟩

/-- **Stacks 0847, part (3).**  The constructions `D ↦ (𝒪_X(D), 1_D)` and `(L, s) ↦ Z(s)` are
mutually inverse, so they are a bijection between the effective Cartier divisors on `X` and the
pairs consisting of an invertible `𝒪_X`-module and a regular global section of it, taken up to
isomorphism of pairs.

The first conjunct is that `D ↦ (𝒪_X(D), 1_D)` lands in such pairs — `𝒪_X(D)` is invertible by
Stacks 0841 and `1_D` is regular by part (1) — and that the round trip
`D ↦ (𝒪_X(D), 1_D) ↦ Z(1_D)` is the identity, which is
`AlgebraicGeometry.Space.zeroScheme_canonicalSection_eq`.  The second is that `(L, s) ↦ Z(s)`
lands in the effective Cartier divisors and that the round trip
`(L, s) ↦ Z(s) ↦ (𝒪_X(Z(s)), 1_{Z(s)})` returns `(L, s)` itself: there is an isomorphism
`𝒪_X(Z(s)) ≅ L` carrying the canonical section to `s`, which is part (2).  The third is that
`(L, s) ↦ Z(s)` is constant on isomorphism classes of pairs,
`AlgebraicGeometry.Space.zeroScheme_eq_of_iso`, which is what makes it a map out of them. -/
@[stacks 0847 "part (3): the constructions D ↦ (𝒪_X(D), 1_D) and (L, s) ↦ Z(s) are mutually \
inverse, hence a bijection between the effective Cartier divisors and the pairs of an \
invertible module with a regular global section taken up to isomorphism; with no assumed inputs"]
theorem effectiveCartierDivisor_regularSectionPair_mutuallyInverse :
    (∀ (D : ClosedSubspaces B S hS X.1) (hD : IsEffectiveCartierDivisor B S hS X D),
        AlgebraicGeometry.SheafOfModules.IsInvertible (structureCommRings B S hS X)
            (structureRingSheaf B S hS X).property (associatedInvertibleSheaf B S hS X D hD) ∧
          AlgebraicGeometry.IsRegularSection (structureCommRings B S hS X)
            (structureRingSheaf B S hS X).property (canonicalSection B S hS X D hD) ∧
          zeroScheme B S hS X (associatedInvertibleSheaf B S hS X D hD)
            (canonicalSection B S hS X D hD) = D) ∧
      (∀ (L : SheafOfModules.{u} (structureRingSheaf B S hS X)),
        AlgebraicGeometry.SheafOfModules.IsInvertible (structureCommRings B S hS X)
          (structureRingSheaf B S hS X).property L → ∀ (s : L.sections),
        AlgebraicGeometry.IsRegularSection (structureCommRings B S hS X)
          (structureRingSheaf B S hS X).property s →
        ∃ (hZ : IsEffectiveCartierDivisor B S hS X (zeroScheme B S hS X L s))
          (i : associatedInvertibleSheaf B S hS X (zeroScheme B S hS X L s) hZ ≅ L),
          canonicalSectionHom B S hS X (zeroScheme B S hS X L s) hZ ≫ i.hom =
            L.unitHomEquiv.symm s) ∧
      ∀ (L L' : SheafOfModules.{u} (structureRingSheaf B S hS X)) (s : L.sections)
        (s' : L'.sections) (i : L ≅ L'), SheafOfModules.sectionsMap i.hom s = s' →
        zeroScheme B S hS X L s = zeroScheme B S hS X L' s' := by
  refine ⟨fun D hD => ⟨associatedInvertibleSheaf_isInvertible B S hS X D hD,
    canonicalSection_isRegular B S hS X D hD, zeroScheme_canonicalSection_eq B S hS X D hD⟩,
    fun L hL s hs => ?_, zeroScheme_eq_of_iso B S hS X⟩
  obtain ⟨D, hD, i, hDz, hcomp, -, -⟩ :=
    exists_unique_isEffectiveCartierDivisor_iso_canonicalSectionHom_comp B S hS X L hL s hs
  subst hDz
  exact ⟨hD, i, hcomp⟩

end AlgebraicGeometry.Space

end
