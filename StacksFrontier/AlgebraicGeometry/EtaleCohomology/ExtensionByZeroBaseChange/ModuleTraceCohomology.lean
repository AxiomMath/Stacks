module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZeroBaseChange.ModuleTraceDegreeSmallEtale
public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateModules.AdequatorVanishing
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.IntegralCohomologicalDimension
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactlySupportedCohomologyZero
public import StacksCore.Tactic.StacksAttribute

/-!
# The méthode de la trace on étale cohomology

Let `f : Y ⟶ X` be finite étale of constant degree `d` and let `F` be a sheaf of `Λ`-modules on
`X_étale` on which multiplication by `d` is an isomorphism. Section 03SH of the Stacks project
observes that `H^n(X, F) ⟶ H^n(Y, f⁻¹ F)` is then injective: through the identification
`H^n(Y, f⁻¹ F) = H^n(X, f_* f⁻¹ F)` (the higher direct images along the finite `f` vanish), the
map is induced by the restriction `F ⟶ f_* f⁻¹ F`, which has a left inverse, the trace divided by
`d`. In particular `H^q(Y, f⁻¹ F) = 0` implies `H^q(X, F) = 0`.

## Main results

* `Stacks.EtaleCohomology.etaleModuleCohomologyDirectImageIsoOfIsIntegralHom`:
  `H^n(X, f_* G) ≅ H^n(Y, G)` for an integral morphism `f : Y ⟶ X`.
* `Stacks.EtaleCohomology.mono_etaleModuleCohomology_map_unit_of_finiteEtale`: the map
  `H^n(X, F) ⟶ H^n(Y, f⁻¹ F)` is a monomorphism.
* `Stacks.EtaleCohomology.isZero_etaleModuleCohomology_of_finiteEtale`: the vanishing transfer.

## References

* [Stacks Project, Tag 03SH](https://stacks.math.columbia.edu/tag/03SH)
* [Stacks Project, Tag 03QP](https://stacks.math.columbia.edu/tag/03QP)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u r

namespace Stacks.EtaleCohomology

variable (Λ : Type r) [Ring Λ]

/-- **`H^n(X, f_* G) = H^n(Y, G)` for an integral morphism `f : Y ⟶ X`**, on sheaves of
`Λ`-modules: `f_*` is exact (Tag 03QP) and preserves injectives, and global sections on `X` of
`f_* G` are global sections of `G`. So the image under `f_*` of an injective resolution of `G` is
an injective resolution of `f_* G`, on which global sections over `X` are global sections over
`Y` of the resolution of `G`. -/
def etaleModuleCohomologyDirectImageIsoOfIsIntegralHom {Z W : Scheme.{u}} (ι : Z ⟶ W)
    [IsIntegralHom ι] (n : ℕ) (G : EtaleModules.{u, r} Λ Z) :
    ((etaleModuleGlobalSections.{u, r} Λ W).rightDerived n).obj
        ((etaleModuleDirectImage.{u, r} Λ ι).obj G) ≅
      ((etaleModuleGlobalSections.{u, r} Λ Z).rightDerived n).obj G :=
  have hex := etaleModuleDirectImage_exact_of_isIntegralHom Λ ι
  have : PreservesFiniteLimits (etaleModuleDirectImage.{u, r} Λ ι) :=
    ((exactFunctor_iff _).1 hex).1
  have : PreservesFiniteColimits (etaleModuleDirectImage.{u, r} Λ ι) :=
    ((exactFunctor_iff _).1 hex).2
  have : (etaleModuleDirectImage.{u, r} Λ ι).PreservesHomology :=
    Functor.preservesHomologyOfExact _
  let I := injectiveResolution G
  let J := Stacks.Adequate.mapInjectiveResolution (etaleModuleDirectImage.{u, r} Λ ι) I
  J.isoRightDerivedObj (etaleModuleGlobalSections.{u, r} Λ W) n ≪≫
    (HomologicalComplex.homologyFunctor _ _ n).mapIso
      ((Functor.mapHomologicalComplexCompIso (etaleModuleGlobalSectionsDirectImageIso ι Λ)
        (ComplexShape.up ℕ)).app I.cocomplex) ≪≫
    (I.isoRightDerivedObj (etaleModuleGlobalSections.{u, r} Λ Z) n).symm

variable {S T : Scheme.{u}} (f : T ⟶ S) [IsFinite f] [Etale f] (d : ℕ)
  [Stacks.Morphisms.IsFiniteLocallyFreeOfRank f d] (F : EtaleModules.{u, r} Λ S)

/-- **Stacks 03SH, the méthode de la trace.** For `f : T ⟶ S` finite étale of degree `d` and a
sheaf of `Λ`-modules `F` on which multiplication by `d` is an isomorphism, the map
`H^n(S, F) ⟶ H^n(T, f⁻¹ F)` — induced by the restriction `F ⟶ f_* f⁻¹ F`, followed by the
identification `H^n(S, f_* f⁻¹ F) = H^n(T, f⁻¹ F)` — is injective: the restriction has a left
inverse, the trace divided by `d`. -/
@[stacks 03SH "the méthode de la trace: H^n(X, F) → H^n(Y, f⁻¹F) is injective when \
multiplication by the degree is an isomorphism of F", sga "5 IIIB 3.2" "partial"]
theorem mono_etaleModuleCohomology_map_unit_of_finiteEtale [IsIso (d • 𝟙 F)] (n : ℕ) :
    Mono (((etaleModuleGlobalSections.{u, r} Λ S).rightDerived n).map
        ((etaleModuleInverseImageAdj.{u, r} Λ f).unit.app F) ≫
      (etaleModuleCohomologyDirectImageIsoOfIsIntegralHom Λ f n
        ((etaleModuleInverseImage.{u, r} Λ f).obj F)).hom) := by
  obtain ⟨r, hr⟩ := exists_etaleModule_unit_comp_eq_id_of_isIso_nsmul Λ f d F
  have : IsSplitMono (((etaleModuleGlobalSections.{u, r} Λ S).rightDerived n).map
      ((etaleModuleInverseImageAdj.{u, r} Λ f).unit.app F)) :=
    ⟨⟨⟨((etaleModuleGlobalSections.{u, r} Λ S).rightDerived n).map r, by
      rw [← Functor.map_comp, hr]
      exact CategoryTheory.Functor.map_id _ _⟩⟩⟩
  infer_instance

/-- **Stacks 03SH, the vanishing consequence of the méthode de la trace.** For `f : T ⟶ S` finite
étale of degree `d` and a sheaf of `Λ`-modules `F` on which multiplication by `d` is an
isomorphism, `H^q(T, f⁻¹ F) = 0` implies `H^q(S, F) = 0`. -/
@[stacks 03SH "if H^q(Y, f⁻¹F) = 0 then H^q(X, F) = 0, when multiplication by the degree is an \
isomorphism of F"]
theorem isZero_etaleModuleCohomology_of_finiteEtale [IsIso (d • 𝟙 F)] (q : ℕ)
    (h : IsZero (((etaleModuleGlobalSections.{u, r} Λ T).rightDerived q).obj
      ((etaleModuleInverseImage.{u, r} Λ f).obj F))) :
    IsZero (((etaleModuleGlobalSections.{u, r} Λ S).rightDerived q).obj F) :=
  have := mono_etaleModuleCohomology_map_unit_of_finiteEtale Λ f d F q
  IsZero.of_mono (((etaleModuleGlobalSections.{u, r} Λ S).rightDerived q).map
      ((etaleModuleInverseImageAdj.{u, r} Λ f).unit.app F) ≫
    (etaleModuleCohomologyDirectImageIsoOfIsIntegralHom Λ f q
      ((etaleModuleInverseImage.{u, r} Λ f).obj F)).hom) h

end Stacks.EtaleCohomology

end
