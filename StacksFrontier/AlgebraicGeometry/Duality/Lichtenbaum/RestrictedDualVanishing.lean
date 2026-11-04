module

public import StacksFrontier.AlgebraicGeometry.Duality.CompactSupportDuality.CompactSupportCohomology
public import StacksFrontier.AlgebraicGeometry.Duality.Lichtenbaum.TopCompactSupport
public import StacksFrontier.AlgebraicGeometry.Duality.OpenImmersion.SheafHomSchemeOpenComplexModel
public import StacksFrontier.AlgebraicGeometry.Properties.ExtendFiniteType.Basic
public import StacksFrontier.AlgebraicGeometry.CoherentOfFiniteType

/-!
# `H^{-d}_c(U, R𝓗om(F, ω_U^•))` vanishes for a non-proper open of a proper variety

Let `X` be an integral scheme proper over a field `k` with `dim X = d`, let `U ⊆ X` be an open with
`U ≠ X`, and let `F` be a coherent `𝒪_U`-module. With `ω_U^• = p^!𝒪_{Spec k}` for
`p : U ⟶ Spec k` and `H^{-d}_c` computed at the compactification `U ⊆ X`, this file proves

`H^{-d}_c(U, R𝓗om(F, ω_U^•)) = 0`,

which is what the proof of [Stacks, Tag 0G5E] feeds into the duality of [Stacks, Tag 0G5A].

## Main definitions

* `Stacks.Duality.Lichtenbaum.restrictDerivedDualIntoIso`: `R𝓗om(L, ω)|_V ≅ R𝓗om(L|_V, ω|_V)` for
  an open `V`, at the standard model ([Stacks, Tag 08DL]).

## Main results

* `Stacks.Duality.Lichtenbaum.subsingleton_compactSupportCohomology_of_iso_derivedDualInto`.

## Implementation notes

`F` is extended to a coherent `𝒪_X`-module `G` ([Stacks, Tag 0G41]), and `R𝓗om(F, ω_U^•)` is
identified with `R𝓗om(G, ω_X^•)|_U`, using `ω_U^• ≅ ω_X^•|_U`
(`AlgebraicGeometry.standardUpperShriekDualizingComplexIso`) and the compatibility of `R𝓗om`
with restriction to opens. The vanishing is then
`Stacks.Duality.Lichtenbaum.subsingleton_degreeZeroCompactSupport_shift_boundedCoherentDuality`.
The object `R𝓗om(F, ω_U^•)` of `D^b_{Coh}(𝒪_U)` enters only through an isomorphism of its
underlying object, so the statement applies to any packaging of it.

## References

* [Stacks Project, Tag 0G5E](https://stacks.math.columbia.edu/tag/0G5E)
* [Stacks Project, Tag 0G41](https://stacks.math.columbia.edu/tag/0G41)
* [Stacks Project, Tag 08DL](https://stacks.math.columbia.edu/tag/08DL)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace Stacks.Duality.Lichtenbaum

open _root_.AlgebraicGeometry

variable {k : Type u} [Field k] {X : Scheme.{u}} (q : X ⟶ Spec (.of k)) [IsProper q]

/-- **Restriction to an open commutes with `R𝓗om(-, ω)`** ([Stacks, Tag 08DL]), at the standard
model: `R𝓗om(L, ω)|_V ≅ R𝓗om(L|_V, ω|_V)`. This is
`Stacks.SheafOfModules.derivedSheafHomSchemeRestrictionIso` with its exactness instances for the
restriction to the slice site supplied. -/
def restrictDerivedDualIntoIso (V : X.Opens)
    (ω L : @DerivedCategory X.Modules _ _ (HasDerivedCategory.standard X.Modules)) :
    (@Functor.mapDerivedCategory _ _ _ (HasDerivedCategory.standard X.Modules) _ _ _
        (HasDerivedCategory.standard V.toScheme.Modules) (Scheme.Modules.restrictFunctor V.ι) _ _
        _).obj (RingedSite.derivedDualInto (Stacks.SheafOfModules.ringedSite X.sheaf) ω L) ≅
      RingedSite.derivedDualInto (Stacks.SheafOfModules.ringedSite V.toScheme.sheaf)
        ((@Functor.mapDerivedCategory _ _ _ (HasDerivedCategory.standard X.Modules) _ _ _
          (HasDerivedCategory.standard V.toScheme.Modules) (Scheme.Modules.restrictFunctor V.ι) _
            _ _).obj ω)
        ((@Functor.mapDerivedCategory _ _ _ (HasDerivedCategory.standard X.Modules) _ _ _
          (HasDerivedCategory.standard V.toScheme.Modules) (Scheme.Modules.restrictFunctor V.ι) _
            _ _).obj L) :=
  let _ := Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteLimits
    (R := X.ringCatSheaf) V
  let _ := Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteColimits
    (R := X.ringCatSheaf) V
  Stacks.SheafOfModules.derivedSheafHomSchemeRestrictionIso V L ω

/-- **`H^{-d}_c(U, R𝓗om(F, ω_U^•)) = 0` for `U ≠ X` open in a proper variety `X` of dimension
`d`.** Here `F` is a coherent `𝒪_U`-module, `ω_U^• = p^!𝒪_{Spec k}` for `p : U ⟶ Spec k`
(`AlgebraicGeometry.standardUpperShriekDualizingComplex`), `L` is any object of
`D^b_{Coh}(𝒪_U)` with underlying object `R𝓗om(F, ω_U^•)`, and `H^{-d}_c` is computed at the
compactification `U ⊆ X`. This is the vanishing of [Stacks, Tag 0G5E] in the form in which
[Stacks, Tag 0G5A] consumes it. Extend `F` to a coherent `𝒪_X`-module `G` ([Stacks, Tag 0G41]);
then `R𝓗om(F, ω_U^•) = R𝓗om(G, ω_X^•)|_U` since `ω_U^• = ω_X^•|_U` and `R𝓗om` commutes with
restriction to opens ([Stacks, Tag 08DL]), and
`Stacks.Duality.Lichtenbaum.subsingleton_degreeZeroCompactSupport_shift_boundedCoherentDuality`
applies. -/
theorem subsingleton_compactSupportCohomology_of_iso_derivedDualInto [IsIntegral X] (d : ℕ)
    (hd : topologicalKrullDim X = d) (V : X.Opens) (hV : ((V : Set X)ᶜ).Nonempty)
    (F : V.toScheme.Modules) (hF : F.IsCoherent) :
    letI := LocallyOfFiniteType.isLocallyNoetherian q
    letI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace q
    letI : IsNoetherian X := ⟨⟩
    ∀ (L : BoundedCoherentDerived V), Nonempty (L.obj ≅ RingedSite.derivedDualInto
        (Stacks.SheafOfModules.ringedSite V.toScheme.sheaf)
        (standardUpperShriekDualizingComplex (V.ι ≫ q)
          (_root_.AlgebraicGeometry.openCompactification q V))
        ((@DerivedCategory.singleFunctor V.toScheme.Modules _ _
          (HasDerivedCategory.standard V.toScheme.Modules) 0).obj F)) →
      Subsingleton (compactSupportCohomology
        (_root_.AlgebraicGeometry.openCompactification q V) L (-(d : ℤ))) := by
  let := LocallyOfFiniteType.isLocallyNoetherian q
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace q
  let : IsNoetherian X := ⟨⟩
  intro L ⟨eL⟩
  have := hF
  have : F.IsQuasicoherent := isQuasicoherent_of_isCoherent F
  have : F.IsFiniteType := hF.isFiniteType
  obtain ⟨G, hGq, hGf, ⟨eG⟩⟩ := exists_finiteTypeQuasicoherent_extension V
    (NoetherianSpace.isCompact _) F
  have hG : G.IsCoherent :=
    Stacks.AlgebraicGeometry.CoherentOfFiniteType.isCoherent_of_isQuasicoherent_of_isFiniteType G
  have hsub := subsingleton_degreeZeroCompactSupport_shift_boundedCoherentDuality q d hd G hG V hV
  let := HasDerivedCategory.standard X.Modules
  let := HasDerivedCategory.standard V.toScheme.Modules
  let K : BoundedCoherentDerived X :=
    (boundedCoherentDuality X (isDualizingComplex_standardRelativeDualizingComplex q)).obj
      (op ⟨(DerivedCategory.singleFunctor X.Modules 0).obj G,
        derivedCategoryBBounded_singleFunctor_obj X G hG⟩)
  let R := (Scheme.Modules.restrictFunctor V.ι).mapDerivedCategory
  let eF0 : R.obj ((DerivedCategory.singleFunctor X.Modules 0).obj G) ≅
      (DerivedCategory.singleFunctor V.toScheme.Modules 0).obj F :=
    ((Scheme.Modules.restrictFunctor V.ι).mapDerivedCategorySingleFunctor 0).app G ≪≫
      (DerivedCategory.singleFunctor V.toScheme.Modules 0).mapIso eG
  let e3 : RingedSite.derivedDualInto (Stacks.SheafOfModules.ringedSite V.toScheme.sheaf)
        (standardUpperShriekDualizingComplex (V.ι ≫ q)
          (_root_.AlgebraicGeometry.openCompactification q V))
        ((DerivedCategory.singleFunctor V.toScheme.Modules 0).obj F) ≅ R.obj K.obj :=
    ((Stacks.SheafOfModules.derivedSheafHom V.toScheme.sheaf).mapIso
        eF0.op).app _ ≪≫
      ((Stacks.SheafOfModules.derivedSheafHom V.toScheme.sheaf).obj
        (op (R.obj ((DerivedCategory.singleFunctor X.Modules 0).obj G)))).mapIso
          (standardUpperShriekDualizingComplexIso (V.ι ≫ q)
            (_root_.AlgebraicGeometry.openCompactification q V)) ≪≫
      (restrictDerivedDualIntoIso V (standardRelativeDualizingComplex q)
        ((DerivedCategory.singleFunctor X.Modules 0).obj G)).symm
  let E : L⟦-(d : ℤ)⟧ ≅ (restrictBoundedCoherentLift V.ι).obj (K⟦-(d : ℤ)⟧) :=
    ObjectProperty.isoMk _ (((boundedCoherentDerived V).ι.commShiftIso (-(d : ℤ))).app L ≪≫
      (shiftFunctor _ (-(d : ℤ))).mapIso (eL ≪≫ e3) ≪≫
      ((R.commShiftIso (-(d : ℤ))).app K.obj).symm ≪≫
      R.mapIso (((boundedCoherentDerived X).ι.commShiftIso (-(d : ℤ))).app K).symm)
  rw [compactSupportCohomology_openCompactification]
  exact (Iso.homCongr (Iso.refl _)
    ((CompactificationData.ofOpenImmersion V.ι q).shriekImage.mapIso E)).subsingleton

end Stacks.Duality.Lichtenbaum

end
