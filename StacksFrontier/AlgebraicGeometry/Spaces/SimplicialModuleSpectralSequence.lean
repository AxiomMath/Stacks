module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.RingedToposHomPullbackSpectralSequence
public import StacksFrontier.AlgebraicGeometry.Spaces.SimplicialSmallEtaleStrictDegree

/-!
# The spectral sequence of a module pulled back to a simplicial algebraic space

Let `U` be a simplicial algebraic space over a scheme `S` with an augmentation `a : U → X`, and
`a : (Sh(U_étale), 𝒪_U) ⟶ (Sh(X_étale), 𝒪_X)` the morphism of ringed topoi of Section 0DE7, with
components `a_p : (Sh(U_{p, étale}), 𝒪_{U_p}) ⟶ (Sh(X_étale), 𝒪_X)`, the morphisms of ringed
topoi of the morphisms `a_p : U_p → X` of algebraic spaces. For an `𝒪_X`-module `𝓕` with
pullbacks `𝓕_p = a_p^*𝓕` to `U_{p, étale}`, there is a spectral sequence, functorial in `𝓕`, with
first page

`E_1^{p,q} = H^q_ét(U_p, 𝓕_p)`,

converging to `H^{p+q}_ét(U, a^*𝓕)`. It converges to `H^{p+q}_ét(X, 𝓕)` as soon as
`𝓕 ⟶ Ra_*(a^*𝓕)` is an isomorphism.

The spectral sequence is that of Stacks 0D7E for `a^*𝓕`.

## Main definitions

* `AlgebraicGeometry.Space.SimplicialSpacesEtaleSite.moduleSpectralSequence`: the spectral
  sequence, as a functor of the `𝒪_X`-module `𝓕`.
* `AlgebraicGeometry.Space.SimplicialSpacesEtaleSite.moduleSpectralSequencePageOneIso`: its first
  page `E_1^{p,q} = H^q_ét(U_p, a_p^*𝓕)`, naturally in `𝓕`.
* `AlgebraicGeometry.Space.SimplicialSpacesEtaleSite.strictComponentAugmentationTwoIso`: the
  augmentation read on the strict component of degree `p` is `a_p`.
* `AlgebraicGeometry.Space.SimplicialSpacesEtaleSite.rightDerivedStrictPullbackIso`: the
  cohomology of the pullback of `𝓕` to the strict total site is `H^n_ét(U, a^*𝓕)`.

## Main results

* `AlgebraicGeometry.Space.SimplicialSpacesEtaleSite.isZero_moduleSpectralSequence_pageOne`: the
  first page vanishes outside the first quadrant.
* `AlgebraicGeometry.Space.SimplicialSpacesEtaleSite.moduleSpectralSequence_abutsTo_of_isIso_unit`:
  convergence to `H^{p+q}_ét(X, 𝓕)` when the unit `𝓕 ⟶ a_*a^*𝓕` is invertible and the higher
  direct images of `a^*𝓕` vanish.

## Implementation notes

The site `U_{spaces, étale}` of Section 0DE7 is not the total site of a strict simplicial site,
base change being functorial only up to canonical isomorphism. It is equivalent, as a ringed
site, to the total site of the strict components
(`AlgebraicGeometry.Space.SimplicialSpacesEtaleSite.strictSituation`), whose components are
equivalent to the `U_{p, spaces, étale}`. The spectral sequence of Stacks 0D7E is taken there,
for the pullback of `𝓕` along the augmentation read on the strict total site, and its first page
and abutment are carried back along these equivalences of ringed topoi.

Cohomology of a sheaf of modules is the right derived functor, in Mathlib's sense, of global
sections of the underlying abelian sheaf, `AlgebraicGeometry.RingedTopos.moduleGlobalSections`.

## References

* [Stacks Project, Tag 0DE7](https://stacks.math.columbia.edu/tag/0DE7)
* [Stacks Project, Tag 0D7E](https://stacks.math.columbia.edu/tag/0D7E)
* [Stacks Project, Tag 0DHH](https://stacks.math.columbia.edu/tag/0DHH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped Simplicial

universe u

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck
  Stacks.Cohomology.SiteModules.moduleSheavesEnoughInjectives

namespace AlgebraicGeometry.Space.SimplicialSpacesEtaleSite

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {U : SimplicialObject (AlgebraicSpaces B S hS)} {X : AlgebraicSpaces B S hS}
  (a : U ⟶ (Functor.const _).obj X)

/-- **The spectral sequence of a module pulled back to a simplicial algebraic space**
`a : U → X`, as a functor of the `𝒪_X`-module `𝓕`: the spectral sequence of Stacks 0D7E for the
pullback of `𝓕` to the total site of the strict components of `U_{spaces, étale}`. -/
@[stacks 0DHH "the spectral sequence"]
def moduleSpectralSequence :
    SheafOfModules.{u + 1} (Stacks.SheafOfModules.Tensor.ringSheaf
        (spacesEtaleRingedTopos B S hS X).O) ⥤
      CohomologicalSpectralSequence AddCommGrpCat.{u + 1} 1 :=
  SimplicialSiteSituation.ringedToposHomPullbackSpectralSequence (strictSituation U)
    (strictStructureSheaf U) (strictAugmentationRingedToposHom a)

/-- **The augmentation read on a strict component is the augmentation of that degree**:
`(b ∘ g_p) ∘ realize_p ≅ a_p` as morphisms of ringed topoi
`(Sh((U_p)_{spaces, étale}), 𝒪_{U_p}) ⟶ (Sh(X_{spaces, étale}), 𝒪_X)`, where `b` is the
augmentation read on the strict total site, `g_p` the component morphism of Stacks 0D72 and
`realize_p` the equivalence of the strict component with `(U_p)_{spaces, étale}`. -/
def strictComponentAugmentationTwoIso (p : SimplexCategory) :
    RingedToposHom.TwoIso (A := spacesEtaleRingedTopos B S hS (U.obj (op p)))
      (B := spacesEtaleRingedTopos B S hS X)
      (RingedToposHom.comp (X := spacesEtaleRingedTopos B S hS (U.obj (op p)))
        (Y := (strictSituation U).componentRingedTopos (strictStructureSheaf U) p)
        (Z := spacesEtaleRingedTopos B S hS X)
        (RingedToposHom.comp
          (X := (strictSituation U).componentRingedTopos (strictStructureSheaf U) p)
          (Y := strictRingedTopos U) (Z := spacesEtaleRingedTopos B S hS X)
          (strictAugmentationRingedToposHom a)
          ((strictSituation U).componentRingedToposHom (strictStructureSheaf U) p))
        (strictComponentRingedToposHom U p))
      (spacesEtaleRingedToposHom (Z₂ := X) (a.app (op p))) :=
  (RingedToposHom.TwoIso.associator (strictComponentRingedToposHom U p)
      ((strictSituation U).componentRingedToposHom (strictStructureSheaf U) p)
      (strictAugmentationRingedToposHom a)).symm.trans
    ((RingedToposHom.TwoIso.whiskerRight (strictDegreeTwoIso U p).symm
        (strictAugmentationRingedToposHom a)).trans
      ((RingedToposHom.TwoIso.associator (degreeRingedToposHom U p) (strictRingedToposHom U)
          (strictAugmentationRingedToposHom a)).trans
        ((RingedToposHom.TwoIso.whiskerLeft (degreeRingedToposHom U p)
            (strictAugmentationTwoIso a)).trans
          (augmentationDegreeTwoIso a p))))

/-- **`E_1^{p,q} = H^q_ét(U_p, a_p^*𝓕)`**, naturally in the `𝒪_X`-module `𝓕`, where `a_p^*` is
the pullback of modules along the morphism of ringed topoi
`(Sh((U_p)_{spaces, étale}), 𝒪_{U_p}) ⟶ (Sh(X_{spaces, étale}), 𝒪_X)` of `a_p : U_p → X`. -/
@[stacks 0DHH "its first page `E_1^{p,q} = H^q_ét(U_p, 𝓕_p)`"]
def moduleSpectralSequencePageOneIso (p q : ℕ) :
    moduleSpectralSequence a ⋙
        (CategoryTheory.SpectralSequence.pageFunctor AddCommGrpCat.{u + 1} _ 1 1 le_rfl ⋙
          HomologicalComplex.eval AddCommGrpCat.{u + 1} _ ((p : ℤ), (q : ℤ))) ≅
      (spacesEtaleRingedToposHom (Z₂ := X) (a.app (op ⦋p⦌))).toModulesHom.pullbackModules ⋙
        (spacesEtaleRingedTopos B S hS (U.obj (op ⦋p⦌))).moduleGlobalSections.rightDerived q :=
  SimplicialSiteSituation.ringedToposHomPullbackSpectralSequencePageOneIso (strictSituation U)
      (strictStructureSheaf U) (strictAugmentationRingedToposHom a) p q ≪≫
    Functor.isoWhiskerLeft _
      (RingedToposHom.rightDerivedModuleGlobalSectionsPullbackIsoOfIsEquivalence
        (strictComponentRingedToposHom U ⦋p⦌) q) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      ((RingedToposHom.pullbackModulesCompIso (strictComponentRingedToposHom U ⦋p⦌)
          (RingedToposHom.comp
            (X := (strictSituation U).componentRingedTopos (strictStructureSheaf U) ⦋p⦌)
            (Y := strictRingedTopos U) (Z := spacesEtaleRingedTopos B S hS X)
            (strictAugmentationRingedToposHom a)
            ((strictSituation U).componentRingedToposHom (strictStructureSheaf U) ⦋p⦌))).symm ≪≫
        (strictComponentAugmentationTwoIso a ⦋p⦌).pullbackModulesIso) _

/-- The first page of `moduleSpectralSequence` vanishes outside the first quadrant. -/
theorem isZero_moduleSpectralSequence_pageOne
    (F : SheafOfModules.{u + 1} (Stacks.SheafOfModules.Tensor.ringSheaf
      (spacesEtaleRingedTopos B S hS X).O))
    (p q : ℤ) (h : p < 0 ∨ q < 0) :
    IsZero ((((moduleSpectralSequence a).obj F).page 1 le_rfl).X (p, q)) :=
  SimplicialSiteSituation.isZero_ringedToposHomPullbackSpectralSequence_page_one
    (strictSituation U) (strictStructureSheaf U) (strictAugmentationRingedToposHom a) F p q h

/-- **`H^n_ét(U, a^*𝓕)` is the cohomology of the pullback of `𝓕` to the strict total site**:
the comparison of `U_{spaces, étale}` with the total site of its strict components is an
equivalence of ringed topoi, through which the augmentation read on the strict total site is
the augmentation of `U`. -/
def rightDerivedStrictPullbackIso
    (F : SheafOfModules.{u + 1} (Stacks.SheafOfModules.Tensor.ringSheaf
      (spacesEtaleRingedTopos B S hS X).O)) (n : ℕ) :
    ((strictRingedTopos U).moduleGlobalSections.rightDerived n).obj
        ((strictAugmentationRingedToposHom a).toModulesHom.pullbackModules.obj F) ≅
      ((ringedTopos U).moduleGlobalSections.rightDerived n).obj
        ((augmentationRingedToposHom a).toModulesHom.pullbackModules.obj F) :=
  ((strictRingedToposHom U).rightDerivedModuleGlobalSectionsPullbackIsoOfIsEquivalence n).app _ ≪≫
    ((ringedTopos U).moduleGlobalSections.rightDerived n).mapIso
      (((RingedToposHom.pullbackModulesCompIso (strictRingedToposHom U)
          (strictAugmentationRingedToposHom a)).app F).symm ≪≫
        (strictAugmentationTwoIso a).pullbackModulesIso.app F)

/-- **Convergence under cohomological descent.** If the unit `𝓕 ⟶ a_*a^*𝓕` is invertible and
the higher direct images of `a^*𝓕` along `a : (Sh(U_étale), 𝒪_U) ⟶ (Sh(X_étale), 𝒪_X)` vanish,
that is if `𝓕 ⟶ Ra_*(a^*𝓕)` is an isomorphism, then `moduleSpectralSequence` of `𝓕` converges to
`H^{p+q}_ét(X, 𝓕)`. -/
theorem moduleSpectralSequence_abutsTo_of_isIso_unit
    (F : SheafOfModules.{u + 1} (Stacks.SheafOfModules.Tensor.ringSheaf
      (spacesEtaleRingedTopos B S hS X).O))
    (hunit : IsIso ((RingedToposHom.pullbackAdjPushforwardModules
      (augmentationRingedToposHom a)).unit.app F))
    (hvanish : haveI := RingedToposHom.pushforwardModules_additive (augmentationRingedToposHom a)
      ∀ q, 0 < q → IsZero
        (((augmentationRingedToposHom a).pushforwardModules.rightDerived q).obj
          ((augmentationRingedToposHom a).toModulesHom.pullbackModules.obj F))) :
    CategoryTheory.SpectralSequence.AbutsTo ((moduleSpectralSequence a).obj F)
      (fun n => if 0 ≤ n then
        ((spacesEtaleRingedTopos B S hS X).moduleGlobalSections.rightDerived n.toNat).obj F
        else AddCommGrpCat.of PUnit.{u + 2}) :=
  (SimplicialSiteSituation.abutsTo_ringedToposHomPullbackSpectralSequence_total
    (strictSituation U) (strictStructureSheaf U) (strictAugmentationRingedToposHom a)
    F).of_nonempty_iso fun n => by
    split_ifs
    · exact ⟨rightDerivedStrictPullbackIso a F n.toNat ≪≫
        ((augmentationRingedToposHom a).rightDerivedModuleGlobalSectionsPullbackIso F hunit
          hvanish n.toNat).symm⟩
    · exact ⟨Iso.refl _⟩

end AlgebraicGeometry.Space.SimplicialSpacesEtaleSite

end
