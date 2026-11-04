module

public import StacksFrontier.AlgebraicGeometry.Crystalline.CrystalDeRhamComplex
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.CrystalVanishingHypotheses
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.LevelFormsCosimplicialIso
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.RestrictedSiteSections

/-!
# The vanishing clause of [Stacks, Tag 07LM] from the transport of its coefficients

Fix a global crystalline situation `(p, (S, I, γ), X)` of [Stacks, Tag 07MF].  The vanishing
clause of [Stacks, Tag 07LM], at the generality [Stacks, Tag 07LN] gives it, is
`Crystalline.GlobalCrystallineSituation.SmallSite.Vanishing07LM`:
`Ru_{X/S, *}(F ⊗_{𝒪_{X/S}} Ω^i_{X/S}) = 0` for `i > 0` and any sheaf of `𝒪_{X/S}`-modules `F`
satisfying conditions (1) and (2) of [Stacks, Tag 07JN].

The proposition `SmallSite.Transport07LMForms` says that for affine opens `V ⊆ X` and `W ⊆ S`
with `V` mapping into `W`, the restriction to `Cris(V/S|_W)` of `F ⊗_{𝒪_{X/S}} Ω^i_{X/S}` is the
corresponding sheaf `F' ⊗_{𝒪_{V/S|_W}} Ω^i_{V/S|_W}` of a sheaf of `𝒪_{V/S|_W}`-modules `F'`
which again satisfies conditions (1) and (2) of [Stacks, Tag 07JN].  This file derives the
vanishing clause from it, using the local-to-global criterion [Stacks, Tag 072W], the
identification [Stacks, Tag 07KL] of the sections of `u_{X/S, *}` over an affine open with the
cohomology of the restricted site, and [Stacks, Tag 07LF].

## Main definitions

Everything lives in the namespace `Crystalline.GlobalCrystallineSituation`.

* `SmallSite.Transport07LMForms` — the transport of the coefficients of the vanishing clause
  along `smallExtend`, as a proposition.

## Main results

* `isAffine_restrict_X` and `isAffine_restrict_S` — for `V` and `W` affine opens the restricted
  situation has affine thickened space and affine divided power base.
* `SmallSite.vanishing07LM_of_transport07LMForms` — **the vanishing clause of
  [Stacks, Tag 07LM] from the transport of its coefficients.**
* `SmallSite.isZero_derivedZariskiDirectImage_tensorDifferentialFormsSheaf_of_vanishing07LM` —
  the specialisation of that clause to a crystal in quasi-coherent modules.
* `SmallSite.vanishing07LMForms_of_vanishing07LM` — the specialisation of that clause to
  `F = 𝒪_{X/S}`.
* `SmallSite.isIso_derivedZariskiDirectImage_crysDeRhamTruncation_of_transport07LMForms` — **the
  leading assertion of [Stacks, Tag 07LM] at `F = 𝒪_{X/S}` from the transport**: the truncation
  map `(𝒪_{X/S} → Ω¹_{X/S} → ⋯) ⟶ 𝒪_{X/S}[0]` becomes an isomorphism after `Ru_{X/S, *}`.

## References

* [Stacks Project, Tag 072W](https://stacks.math.columbia.edu/tag/072W)
* [Stacks Project, Tag 07JN](https://stacks.math.columbia.edu/tag/07JN)
* [Stacks Project, Tag 07KL](https://stacks.math.columbia.edu/tag/07KL)
* [Stacks Project, Tag 07LF](https://stacks.math.columbia.edu/tag/07LF)
* [Stacks Project, Tag 07LM](https://stacks.math.columbia.edu/tag/07LM)
* [Stacks Project, Tag 07LN](https://stacks.math.columbia.edu/tag/07LN)
* [Stacks Project, Tag 07MF](https://stacks.math.columbia.edu/tag/07MF)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe w w' u

noncomputable section

namespace Crystalline.GlobalCrystallineSituation

variable (S : GlobalCrystallineSituation.{u}) (W : S.S.scheme.Opens) (V : S.X.Opens)
  (hVW : V ≤ sourceToBase S ⁻¹ᵁ W)

/-- **The thickened space of a restricted situation is affine when the open is.** -/
theorem isAffine_restrict_X (hV : IsAffineOpen V) : IsAffine (restrict S W V hVW).X := hV

/-- **The divided power base of a restricted situation is affine when the open is.** -/
theorem isAffine_restrict_S (hW : IsAffineOpen W) :
    IsAffine (restrict S W V hVW).S.scheme := hW

namespace SmallSite

section Transport

variable [HasDerivedCategory.{w} (Sheaf (smallTopology S) AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{w'} (Sheaf (opensTopology S) AddCommGrpCat.{u + 1})]

/-- **The transport of the coefficients of the vanishing clause of [Stacks, Tag 07LM] along
`smallExtend`.**  For every pair of opens `W ⊆ S`, `V ⊆ X` with the image of `V` inside `W`, for
both opens affine, for every sheaf of `𝒪_{X/S}`-modules `F` satisfying conditions (1) and (2) of
[Stacks, Tag 07JN] and every degree `i`, the restriction of `F ⊗_{𝒪_{X/S}} Ω^i_{X/S}` to
`Cris(V/S|_W)` is the corresponding sheaf of the restricted situation, for a sheaf of
`𝒪_{V/S|_W}`-modules which again satisfies the two conditions. -/
def Transport07LMForms : Prop :=
  ∀ (W : S.S.scheme.Opens) (V : S.X.Opens) (hVW : V ≤ sourceToBase S ⁻¹ᵁ W),
    IsAffineOpen W → IsAffineOpen V →
    ∀ F : SheafOfModules.{u} (structureSheaf S), IsLocallyQuasiCoherent F →
      CohomologyRestriction.IsSurjectiveComparison F.val → ∀ i : ℕ,
        ∃ F' : SheafOfModules.{u} (structureSheaf (restrict S W V hVW)),
          IsLocallyQuasiCoherent F' ∧
            CohomologyRestriction.IsSurjectiveComparison F'.val ∧
            Nonempty ((smallExtendAbelianRestriction S W V hVW).obj
                (tensorDifferentialFormsSheaf F i) ≅
              tensorDifferentialFormsSheaf F' i)

/-- **The vanishing clause of [Stacks, Tag 07LM] from the transport of its coefficients**:
`Transport07LMForms S` implies `Vanishing07LM S`. -/
theorem vanishing07LM_of_transport07LMForms (htr : Transport07LMForms S) : Vanishing07LM S := by
  refine vanishing07LM_of_isZero_rightDerived_zariskiDirectImageSections S
    fun F hqc hsurj i hi p V hV ↦ ?_
  obtain ⟨hVaff, W, hWaff, hVW⟩ := hV
  refine isZero_rightDerived_zariskiDirectImageSections_of_isZero S W V hVW p _ ?_
  obtain ⟨F', hqc', hsurj', ⟨e⟩⟩ := htr W V hVW hWaff hVaff F hqc hsurj i
  refine IsZero.of_iso ?_ ((Functor.rightDerived (globalSections (restrict S W V hVW)) p).mapIso e)
  exact (vanishing07LF_iff_isZero_rightDerivedGlobalSections (restrict S W V hVW)).1
    (vanishing07LF (restrict S W V hVW)) (isAffine_restrict_X S W V hVW hVaff)
    (isAffine_restrict_S S W V hVW hWaff) F' hqc' hsurj' i p hi

/-- **The second clause of [Stacks, Tag 07LM] for a crystal in quasi-coherent modules, from the
clause at the generality of [Stacks, Tag 07LN]**: for `F` a crystal in quasi-coherent
`𝒪_{X/S}`-modules and `i > 0`,

`Ru_{X/S, *}(F ⊗_{𝒪_{X/S}} Ω^i_{X/S}) = 0`. -/
theorem isZero_derivedZariskiDirectImage_tensorDifferentialFormsSheaf_of_vanishing07LM
    (hV : Vanishing07LM S) (F : SheafOfModules.{u} (structureSheaf S))
    (hF : F.IsQuasicoherentOnSite) (i : ℕ) (hi : 0 < i) :
    IsZero ((derivedZariskiDirectImage S).obj (tensorDifferentialFormsSheaf F i)) :=
  hV F (satisfiesVanishingHypotheses_of_isQuasicoherentOnSite F hF).1
    (satisfiesVanishingHypotheses_of_isQuasicoherentOnSite F hF).2 i hi

/-- **`𝒪_{X/S} ⊗_{𝒪_{X/S}} Ω^i_{X/S} = Ω^i_{X/S}` on abelian sheaves**: the sheafification of the
left unitor `tensorDifferentialFormsUnitIso`. -/
def tensorDifferentialFormsSheafUnitIso (i : ℕ) :
    tensorDifferentialFormsSheaf (SheafOfModules.unit (structureSheaf S)) i ≅
      (crysAbelianSheafification S).obj (modulePresheaf S (crysDifferentialForms S i)) :=
  (crysAbelianSheafification S).mapIso
    ((PresheafOfModules.toPresheaf _).mapIso (tensorDifferentialFormsUnitIso S i))

/-- **The vanishing clause of [Stacks, Tag 07LM] at `F = 𝒪_{X/S}` follows from the clause at the
generality of [Stacks, Tag 07LN]**: `Vanishing07LM S` implies `Vanishing07LMForms S`. -/
theorem vanishing07LMForms_of_vanishing07LM (hV : Vanishing07LM S) : Vanishing07LMForms S := by
  intro i hi
  obtain ⟨hqc, hsurj⟩ := satisfiesVanishingHypotheses_of_isQuasicoherentOnSite
    (SheafOfModules.unit (structureSheaf S)) inferInstance
  exact IsZero.of_iso (hV (SheafOfModules.unit (structureSheaf S)) hqc hsurj i hi)
    ((derivedZariskiDirectImage S).mapIso (tensorDifferentialFormsSheafUnitIso S i)).symm

/-- **The leading assertion of [Stacks, Tag 07LM] at `F = 𝒪_{X/S}`, from the transport of the
coefficients alone.**  The truncation map

`(𝒪_{X/S} → Ω¹_{X/S} → Ω²_{X/S} → ⋯) ⟶ 𝒪_{X/S}[0]`

becomes an isomorphism in `D⁺(Ab(X_Zar))` after `Ru_{X/S, *}`. -/
theorem isIso_derivedZariskiDirectImage_crysDeRhamTruncation_of_transport07LMForms
    (htr : Transport07LMForms S) :
    IsIso ((derivedZariskiDirectImageFunctor S).map
      (DerivedCategory.Plus.Qh.map
        ((HomotopyCategory.Plus.quotient _).map (crysDeRhamPlusTruncation S)))) :=
  isIso_derivedZariskiDirectImageFunctor_map_crysDeRhamTruncation S
    (vanishing07LMForms_of_vanishing07LM S (vanishing07LM_of_transport07LMForms S htr))

end Transport

end SmallSite

end Crystalline.GlobalCrystallineSituation

end

end
