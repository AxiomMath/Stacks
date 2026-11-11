module

public import StacksFrontier.AlgebraicGeometry.Spaces.HigherDirectImageLeray
public import StacksFrontier.AlgebraicGeometry.Spaces.InjectivePushforwardAcyclicity
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ProperSupportCoherentPushforward
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Acyclicity.TotallyAcyclicShortExactLargeSite
public import StacksFrontier.Algebra.Homology.DerivedCategory.AcyclicObjects

/-!
# Higher direct images along a composite whose first factor has no higher direct images

Let `a : X₁ ⟶ X₂` and `b : X₂ ⟶ Y` be morphisms of algebraic spaces and `𝓝` an
`𝒪_{X₁}`-module with `R^q a_*𝓝 = 0` for `q > 0`. Then `R^p b_*(a_*𝓝) ≅ R^p (a ≫ b)_*𝓝` for every
`p`: the degeneration of the relative Leray spectral sequence of Stacks 0734 for the pair
`(a, b)`, proved without spectral sequences.

## Main results

* `AlgebraicGeometry.Space.isTotallyAcyclic_toSheaf_of_injective`: the abelian sheaf underlying an
  injective `𝒪_X`-module is totally acyclic.
* `AlgebraicGeometry.Space.acyclic_modulePushforward_of_isTotallyAcyclic`: **Stacks 0731 (4) for
  algebraic spaces**, a module with totally acyclic underlying abelian sheaf is acyclic for
  `b_*`.
* `AlgebraicGeometry.Space.modulePushforwardRightDerivedCompIso`: the identification above.
* `AlgebraicGeometry.Space.higherDirectImageCompOfAcyclic`: every morphism has the property
  `AlgebraicGeometry.Space.HigherDirectImageCompOfAcyclic` (the step of Stacks 0734 used by
  Stacks 08GC).

## Implementation notes

The library's Stacks 0731 (4) and Stacks 0734 are stated for ringed topoi with all three universes
equal; the small étale ringed topos of an algebraic space has its objects one universe higher.
The proof here follows `Stacks.Cohomology.rightAcyclic_pushforwardModules_of_isTotallyAcyclic`:
totally acyclic modules are adapted to `b_*` (Stacks 05T8), injectives being totally acyclic by the
any-size Stacks 03FD input `Stacks.Cohomology.ObjectSections.ext_eq_zero_of_isTorsionFree`, and
`b_*` keeping a short exact sequence with totally acyclic kernel exact because the sequence splits
on underlying sheaves of sets. The direct image of an injective module is totally acyclic by
Stacks 072Z (`AlgebraicGeometry.Space.isTotallyAcyclic_modulePushforward_of_injective`), so
`Stacks.RightDerivedComp.objIsoOfAcyclicImage` applies to `(a ≫ b)_* ≅ a_* ⋙ b_*`.

## References

* [Stacks Project, Tag 0734](https://stacks.math.columbia.edu/tag/0734)
* [Stacks Project, Tag 0731](https://stacks.math.columbia.edu/tag/0731)
* [Stacks Project, Tag 072Z](https://stacks.math.columbia.edu/tag/072Z)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Stacks.Topos.AbelianPushforward

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

attribute [local instance 5000] SheafOfModules.instAbelian

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

attribute [local instance] AlgebraicGeometry.Space.enoughInjectives_sheaf_smallEtale
  AlgebraicGeometry.Space.hasExt_sheaf_smallEtale
  AlgebraicGeometry.Space.enoughInjectives_sheaf_smallEtaleRingedSite
  AlgebraicGeometry.Space.hasExt_sheaf_smallEtaleRingedSite

variable {B S hS} {X Y Z : AlgebraicSpaces B S hS}

/-- **The abelian sheaf underlying an injective `𝒪_X`-module is totally acyclic**, on the small
étale site, whose objects need not form a small type. -/
theorem isTotallyAcyclic_toSheaf_of_injective (I : Modules.{u, u} B S hS X.1 X.2) [Injective I] :
    Stacks.Cohomology.IsTotallyAcyclic (smallEtaleRingedSite B S hS X.1 X.2).J
      ((SheafOfModules.toSheaf _).obj I) := by
  intro K p hp
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hp)
  -- the free abelian sheaf on `K` is the sheafification of a sectionwise flat presheaf
  have hK := ModuleSheafCohomology.isTorsionFree_sheafify (smallEtaleRingedSite B S hS X.1 X.2).J
    (K.obj ⋙ AddCommGrpCat.free)
    (fun V ↦ by
      change Module.IsTorsionFree ℤ (FreeAbelianGroup (K.obj.obj V))
      exact Module.Flat.isTorsionFree)
  refine ⟨fun a b => ?_⟩
  rw [Stacks.Cohomology.ObjectSections.ext_eq_zero_of_isTorsionFree _ _ I _ hK n a,
    Stacks.Cohomology.ObjectSections.ext_eq_zero_of_isTorsionFree _ _ I _ hK n b]

/-- The direct image of a short exact sequence of `𝒪_X`-modules whose kernel has totally acyclic
underlying abelian sheaf is short exact. -/
theorem shortExact_map_modulePushforward (f : X ⟶ Y)
    (Sc : ShortComplex (Modules.{u, u} B S hS X.1 X.2)) (hSc : Sc.ShortExact)
    (h₁ : Stacks.Cohomology.IsTotallyAcyclic (smallEtaleRingedSite B S hS X.1 X.2).J
      ((SheafOfModules.toSheaf _).obj Sc.X₁)) :
    (Sc.map (modulePushforward B S hS f)).ShortExact := by
  have := modulePushforward_additive B S hS f
  obtain ⟨hexact, hmono⟩ :=
    (Functor.preservesFiniteLimits_iff_forall_exact_map_and_mono
      (modulePushforward B S hS f)).mp inferInstance Sc hSc
  obtain ⟨hsplit⟩ := Stacks.Cohomology.splitEpi_moduleSheafFunctor_general
    (smallEtaleRingedSite B S hS X.1 X.2).J
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)
    Sc hSc h₁
  have h₃ : Epi ((abelianPushforward (smallEtaleRingedSite B S hS X.1 X.2).J
      (smallToposMorphismTypeU B S hS f)).map ((SheafOfModules.toSheaf _).map Sc.g)) :=
    (sheafCompose (smallEtaleRingedSite B S hS Y.1 Y.2).J
      (forget AddCommGrpCat.{u})).epi_of_epi_map
        (hsplit.map (smallToposMorphismTypeU B S hS f).pushforward).epi
  have h₄ : Epi ((SheafOfModules.toSheaf _).map ((modulePushforward B S hS f).map Sc.g)) := by
    change Epi ((modulePushforward B S hS f ⋙ SheafOfModules.toSheaf _).map Sc.g)
    rw [← NatIso.naturality_2 (modulePushforwardToSheafIso B S hS f) Sc.g]
    exact epi_comp' (IsIso.epi_of_iso _) (epi_comp' h₃ (IsIso.epi_of_iso _))
  exact ShortComplex.ShortExact.mk' hexact hmono
    ((SheafOfModules.toSheaf _).epi_of_epi_map h₄)

/-- **Stacks 0731 (4) for algebraic spaces.** An `𝒪_X`-module whose underlying abelian sheaf is
totally acyclic is acyclic for the direct image along any morphism of algebraic spaces. -/
theorem acyclic_modulePushforward_of_isTotallyAcyclic (f : X ⟶ Y)
    (N : Modules.{u, u} B S hS X.1 X.2)
    (hN : Stacks.Cohomology.IsTotallyAcyclic (smallEtaleRingedSite B S hS X.1 X.2).J
      ((SheafOfModules.toSheaf _).obj N)) :
    have := enoughInjectives_modules B S hS X.1 X.2
    Stacks.RightDerivedComp.acyclic (modulePushforward B S hS f) N := by
  have := enoughInjectives_modules B S hS X.1 X.2
  have := modulePushforward_additive B S hS f
  let _ := HasDerivedCategory.standard (Modules.{u, u} B S hS X.1 X.2)
  let _ := HasDerivedCategory.standard (Modules.{u, u} B S hS Y.1 Y.2)
  have : ((modulePushforward B S hS f).mapHomotopyCategoryPlus ⋙
      DerivedCategory.Plus.Qh).HasRightDerivedFunctor
        (HomotopyCategory.Plus.quasiIso (Modules.{u, u} B S hS X.1 X.2)) :=
    have := HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso
      ((modulePushforward B S hS f).mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh)
    inferInstance
  refine (Stacks.RightDerivedComp.rightAcyclic_iff_acyclic (modulePushforward B S hS f) N).1 ?_
  refine Functor.le_rightAcyclic (modulePushforward B S hS f)
    (fun M => Stacks.Cohomology.IsTotallyAcyclic (smallEtaleRingedSite B S hS X.1 X.2).J
      ((SheafOfModules.toSheaf _).obj M))
    (fun M => ⟨Injective.under M, isTotallyAcyclic_toSheaf_of_injective (Injective.under M),
      Injective.ι M, inferInstance⟩)
    (fun Sc hSc h₁ h₂ => ⟨Stacks.Cohomology.isTotallyAcyclic_of_shortExact_general _
        (hSc.map_of_exact (SheafOfModules.toSheaf _)) h₁ h₂,
      shortExact_map_modulePushforward f Sc hSc h₁⟩) N hN

/-- **The degeneration of the relative Leray spectral sequence (Stacks 0734) for a first factor
without higher direct images.** For `a : X ⟶ Y`, `b : Y ⟶ Z` and an `𝒪_X`-module `𝓝` with
`R^q a_*𝓝 = 0` for every `q > 0`, `R^p (a ≫ b)_*𝓝 ≅ R^p b_*(a_*𝓝)` in every degree. -/
def modulePushforwardRightDerivedCompIso (a : X ⟶ Y) (b : Y ⟶ Z)
    (N : Modules.{u, u} B S hS X.1 X.2)
    (hN : ∀ q, 0 < q →
      have := hasInjectiveResolutions_modules B S hS X.1 X.2
      IsZero (((modulePushforward B S hS a).rightDerived q).obj N)) (p : ℕ) :
    have := hasInjectiveResolutions_modules B S hS X.1 X.2
    have := hasInjectiveResolutions_modules B S hS Y.1 Y.2
    ((modulePushforward B S hS (a ≫ b)).rightDerived p).obj N ≅
      ((modulePushforward B S hS b).rightDerived p).obj ((modulePushforward B S hS a).obj N) :=
  have := hasInjectiveResolutions_modules B S hS X.1 X.2
  have := hasInjectiveResolutions_modules B S hS Y.1 Y.2
  have := enoughInjectives_modules B S hS Y.1 Y.2
  have := modulePushforward_additive B S hS a
  have := modulePushforward_additive B S hS b
  have := modulePushforward_additive B S hS (a ≫ b)
  (Functor.rightDerivedIsoOfNatIso (modulePushforwardCompIso B S hS a b).symm p).app N ≪≫
    Stacks.RightDerivedComp.objIsoOfAcyclicImage (modulePushforward B S hS a)
      (modulePushforward B S hS b) hN
      (fun I hI =>
        have := hI
        acyclic_modulePushforward_of_isTotallyAcyclic b _
          (isTotallyAcyclic_modulePushforward_of_injective B S hS a I)) p

/-- **The hypothesis `h0734` of Stacks 08GC holds for every morphism of algebraic spaces.** -/
theorem higherDirectImageCompOfAcyclic (f : X ⟶ Y) : HigherDirectImageCompOfAcyclic B S hS f :=
  fun _ i _ G hG p => ⟨(modulePushforwardRightDerivedCompIso i f G hG p).symm⟩

end AlgebraicGeometry.Space

end
