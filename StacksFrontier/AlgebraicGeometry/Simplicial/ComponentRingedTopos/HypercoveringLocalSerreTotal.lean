module

public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.HypercoveringSummandModules
public import StacksFrontier.CategoryTheory.Abelian.SerreClass.WeakInverseImage
public import StacksFrontier.CategoryTheory.Sites.Cohomology.CohomologicalDescent.HypercoveringUnboundedLocalSerre
public import StacksFrontier.CategoryTheory.Sites.Cohomology.CohomologicalDescent.LocalSerreFamily
public import StacksFrontier.CategoryTheory.Sites.Simplicial.HypercoveringDescent

/-!
# The class `A_total` of a local family of weak Serre subcategories on a hypercovering

Let `(C, O_C)` be a ringed site and `A_U ⊂ Mod(O_U)` a family of weak Serre subcategories
satisfying conditions 0DC2, 0DC3 and 0DC4 (a `LocalSerreFamily`), and let `A ⊂ Mod(O_C)` be the
modules whose restriction to every `C/U` lies in `A_U`. For a hypercovering `K` with
`K_n = {U_{n,i}}` the source attaches to the degree-`n` component the class
`A_{K_n} = ∏_i A_{U_{n,i}} ⊂ Mod(O_n)`, and to the total ringed site `((C/K)_total, O)` of
Remark 0D9W the class `A_total` of cartesian `O`-modules `F` with `F_n ∈ A_{K_n}` for all `n`.

This file defines these classes and proves the first two steps of the proof of Stacks 0DC7:
`A_total` is a weak Serre subcategory, and `a^*` identifies `A` with `A_total`: it carries `A`
into `A_total`, and every object of `A_total` is `a^*` of an object of `A`.

## Main definitions

* `Stacks.CategoryTheory.Hypercovering.componentLocalSerre`: the class `A_{K_n}`.
* `Stacks.CategoryTheory.Hypercovering.totalLocalSerre`: the class `A_total`.

## Main results

* `Stacks.CategoryTheory.Hypercovering.isWeakSerreClass_totalLocalSerre`: `A_total` is a weak
  Serre subcategory of `Mod(O)`.
* `Stacks.CategoryTheory.Hypercovering.totalLocalSerre_pullbackModules`: `a^*` carries `A` into
  `A_total`.
* `Stacks.CategoryTheory.Hypercovering.exists_pullbackModules_iso_of_totalLocalSerre`: every
  object of `A_total` is `a^*M` for some `M` in `A`. This is the covering argument of the
  source: `K_0` covers the final object, so every `U` has a covering `{U_j ⟶ U}` with maps
  `U_j ⟶ U_{0, τ(j)}`, along which the restriction of `M` is a restriction of a component of
  `F_0`; conditions 0DC2 and 0DC3 conclude.

## References

* [Stacks Project, Tag 0DC7](https://stacks.math.columbia.edu/tag/0DC7)
* [Stacks Project, Tag 0DC2](https://stacks.math.columbia.edu/tag/0DC2)
* [Stacks Project, Tag 0DC3](https://stacks.math.columbia.edu/tag/0DC3)
* [Stacks Project, Tag 0D9Z](https://stacks.math.columbia.edu/tag/0D9Z)
* [Stacks Project, Tag 0D7J](https://stacks.math.columbia.edu/tag/0D7J)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open CategoryTheory.SimplicialSiteSituation CategoryTheory.SimplicialSemiRepresentable
open Stacks.Cohomology.CohomologicalDescent
open scoped ZeroObject

universe u

namespace CategoryTheory.ObjectProperty

variable {C : Type*} [Category* C] [Abelian C] {ι : Type*} {D : ι → Type*} [∀ i, Category* (D i)]
  [∀ i, Abelian (D i)] (Q : ∀ i, ObjectProperty (D i)) [∀ i, (Q i).IsWeakSerreClass]
  (F : ∀ i, C ⥤ D i) [∀ i, (F i).PreservesZeroMorphisms] [∀ i, PreservesFiniteLimits (F i)]
  [∀ i, PreservesFiniteColimits (F i)]

/-- The objects `X` with `Q_i (F_i X)` for every `i`. -/
def forallInverseImage : ObjectProperty C := fun X ↦ ∀ i, Q i ((F i).obj X)

/-- **An intersection of inverse images of weak Serre classes under exact functors is a weak
Serre class**: the objects `X` with `Q_i (F_i X)` for every `i`. Each closure condition is checked
one index at a time, where it is the corresponding condition of the inverse image of `Q_i`. -/
theorem isWeakSerreClass_forall_inverseImage :
    (forallInverseImage Q F).IsWeakSerreClass := by
  have : (forallInverseImage Q F).IsClosedUnderIsomorphisms :=
    { of_iso := fun e h i ↦ ((Q i).inverseImage (F i)).prop_of_iso e (h i) }
  have : (forallInverseImage Q F).ContainsZero :=
    ⟨0, isZero_zero _, fun i ↦ ((Q i).inverseImage (F i)).prop_of_isZero (isZero_zero _)⟩
  have : (forallInverseImage Q F).IsClosedUnderKernels :=
    { kernels_le := by
        rintro _ ⟨f, k, hk, hf⟩ i
        exact ((Q i).inverseImage (F i)).prop_of_isLimit_kernelFork hk (hf.1 i) (hf.2 i) }
  have : (forallInverseImage Q F).IsClosedUnderCokernels :=
    { cokernels_le := by
        rintro _ ⟨f, k, hk, hf⟩ i
        exact ((Q i).inverseImage (F i)).prop_of_isColimit_cokernelCofork hk (hf.1 i) (hf.2 i) }
  have : (forallInverseImage Q F).IsClosedUnderExtensions :=
    { prop_X₂_of_shortExact := fun hS h₁ h₃ i ↦
        ((Q i).inverseImage (F i)).prop_X₂_of_shortExact hS (h₁ i) (h₃ i) }
  exact {}

end CategoryTheory.ObjectProperty

namespace Stacks.CategoryTheory.Hypercovering

attribute [local instance]
  CategoryTheory.SimplicialSiteSituation.objectModuleDescentHasWeakSheafifyTotal
  CategoryTheory.SimplicialSiteSituation.objectModuleDescentWEqualsLocallyBijectiveTotal
  CategoryTheory.SimplicialSiteSituation.objectModuleDescentHasWeakSheafifyComponent

variable {C : Type u} [SmallCategory C] [HasEqualizers C] [HasPullbacks C] (J : Pretopology C)
  (H : HypercoveringOfTerminal.{u, u} J) (OC : Sheaf J.toGrothendieck CommRingCat.{u})
  (T : LocalSerreFamily.{u} (pretopologyRingedSite J OC))

/-- **The class `A_{K_n} = ∏_i A_{U_{n,i}}` of the source**: the `O_n`-modules on the degree-`n`
component all of whose components `G_i` on the summands `C/U_{n,i}` lie in `A_{U_{n,i}}`. -/
def componentLocalSerre (n : SimplexCategory) :
    ObjectProperty (SheafOfModules.{u} (componentRingSheaf (hypercoveringSituation J H)
      ((hypercoveringSituation J H).totalRingSheaf (hypercoveringRingedAugmentation J H OC).O)
      n)) :=
  fun G ↦ ∀ i, T.A _ ((hypercoveringSummandRestriction J H OC n i).obj G)

/-- **The class `A_total` of Stacks 0DC7**: the cartesian `O`-modules `F` on the total site
whose restriction `F_n` to the degree-`n` component lies in `A_{K_n}` for every `n`. -/
abbrev totalLocalSerre :
    ObjectProperty (SheafOfModules.{u}
      ((hypercoveringSituation J H).totalRingSheaf (hypercoveringRingedAugmentation J H OC).O)) :=
  cartesianDegreewiseModules (hypercoveringSituation J H) (hypercoveringRingedAugmentation J H OC).O
    (componentLocalSerre J H OC T)

/-- Restriction of `O_n`-modules to a summand is exact, being restriction of scalars along an
isomorphism followed by the summand restriction of Stacks 0D9U. -/
instance hypercoveringSummandRestriction_preservesFiniteLimits (n : SimplexCategory)
    (i : (H.toSimplicialObject.obj (op n)).I) :
    PreservesFiniteLimits (hypercoveringSummandRestriction J H OC n i) := by
  let e := Stacks.Sheaves.RingedPoint.restrictScalarsEquivalenceOfIso
    (((componentFunctor (hypercoveringSituation J H) n).sheafPushforwardContinuous RingCat.{u}
      ((hypercoveringSituation J H).componentTopology n)
      (hypercoveringSituation J H).totalTopology).mapIso (hypercoveringStructureRingIso J H OC))
  have : PreservesLimitsOfSize.{0, 0} e.functor := e.symm.toAdjunction.rightAdjoint_preservesLimits
  exact @comp_preservesFiniteLimits _ _ _ _ _ _ e.functor
    (summandRestriction (pretopologyRingedSite J OC) H.toSimplicialObject n i)
    (PreservesLimitsOfSize.preservesFiniteLimits _)
    (summandRestriction_preservesFiniteLimits (pretopologyRingedSite J OC)
      H.toSimplicialObject n i)

/-- Restriction of `O_n`-modules to a summand is right exact. -/
instance hypercoveringSummandRestriction_preservesFiniteColimits (n : SimplexCategory)
    (i : (H.toSimplicialObject.obj (op n)).I) :
    PreservesFiniteColimits (hypercoveringSummandRestriction J H OC n i) := by
  let e := Stacks.Sheaves.RingedPoint.restrictScalarsEquivalenceOfIso
    (((componentFunctor (hypercoveringSituation J H) n).sheafPushforwardContinuous RingCat.{u}
      ((hypercoveringSituation J H).componentTopology n)
      (hypercoveringSituation J H).totalTopology).mapIso (hypercoveringStructureRingIso J H OC))
  have : PreservesColimitsOfSize.{0, 0} e.functor := e.toAdjunction.leftAdjoint_preservesColimits
  exact @comp_preservesFiniteColimits _ _ _ _ _ _ e.functor
    (summandRestriction (pretopologyRingedSite J OC) H.toSimplicialObject n i)
    (PreservesColimitsOfSize.preservesFiniteColimits _)
    (summandRestriction_preservesFiniteColimits (pretopologyRingedSite J OC)
      H.toSimplicialObject n i)

/-- Restriction of `O_n`-modules to a summand preserves zero morphisms. -/
instance hypercoveringSummandRestriction_preservesZeroMorphisms (n : SimplexCategory)
    (i : (H.toSimplicialObject.obj (op n)).I) :
    (hypercoveringSummandRestriction J H OC n i).PreservesZeroMorphisms :=
  haveI : (hypercoveringSummandRestriction J H OC n i).Additive := ⟨fun {_ _ _ _} ↦ rfl⟩
  inferInstance

/-- **`A_{K_n}` is a weak Serre subcategory of `Mod(O_n)`**, the summand restrictions being exact
and each `A_{U_{n,i}}` a weak Serre subcategory. -/
theorem isWeakSerreClass_componentLocalSerre (n : SimplexCategory) :
    (componentLocalSerre J H OC T n).IsWeakSerreClass := by
  have := fun i : (H.toSimplicialObject.obj (op n)).I ↦
    T.weakSerre ((H.toSimplicialObject.obj (op n)).obj i)
  exact ObjectProperty.isWeakSerreClass_forall_inverseImage
    (fun i ↦ T.A ((H.toSimplicialObject.obj (op n)).obj i))
    (fun i ↦ hypercoveringSummandRestriction J H OC n i)

/-- **Stacks 0DC7, `A_total` is a weak Serre subcategory of `Mod(O)`.** The cartesian
`O`-modules are a weak Serre subcategory by Stacks 0D7J (2) — its hypothesis holds because
`O = a⁻¹O_C` is cartesian (Stacks 0D9W), so the structure maps of the face transitions are
invertible and pullback along them is exact — and the degreewise conditions are inverse images of
the weak Serre subcategories `A_{K_n}` under the exact restrictions `g_n^*`. -/
theorem isWeakSerreClass_totalLocalSerre : (totalLocalSerre J H OC T).IsWeakSerreClass :=
  isWeakSerreClass_cartesianDegreewiseModules (hypercoveringSituation J H)
    (hypercoveringRingedAugmentation J H OC).O _
    (fun _ i ↦
      have := (hypercoveringSituation J H).isIso_transitionRingedToposHom_fSharpInverseImage
        (hypercoveringRingedAugmentation J H OC).O
        (RingedAugmentation.isCartesianSheaf_underlyingO (hypercoveringRingedAugmentation J H OC))
        (SimplexCategory.δ i)
      RingedToposHom.pullbackModules_preservesFiniteLimits_of_isIso_fSharp
        ((hypercoveringSituation J H).transitionRingedToposHom
          (hypercoveringRingedAugmentation J H OC).O (SimplexCategory.δ i)))
    (isWeakSerreClass_componentLocalSerre J H OC T)

/-- **`a^*` carries `A` into `A_total`.** `a^*M` is cartesian (Stacks 0D7H (3)), and the `i`-th
component of `(a^*M)_n` is `M|_{U_{n,i}}`, which lies in `A_{U_{n,i}}` when `M` lies in `A`. -/
theorem totalLocalSerre_pullbackModules
    (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf OC))
    (hM : LocalSerreFamily.globalProperty _ T M) :
    totalLocalSerre J H OC T
      ((hypercoveringRingedAugmentation J H
        OC).totalRingedHom.toModulesHom.pullbackModules.obj M) :=
  ⟨((hypercoveringSituation J H).isModuleFiberTransitionIso_iff_isCartesianModule
      (hypercoveringRingedAugmentation J H OC).O _).1
      (isCartesianModule_pullbackModules_hypercovering J H OC M),
    fun n i ↦
      have := T.weakSerre ((H.toSimplicialObject.obj (op n)).obj i)
      (T.A _).prop_of_iso (hypercoveringSummandRestrictionPullbackIso J H OC n i M).symm
        (hM _)⟩

/-- The family of all arrows of a sieve, as a covering family whose generated sieve is the
sieve. -/
def preZeroHypercoverOfSieve {X : C} (S : Sieve X) : PreZeroHypercover.{u} X :=
  ⟨Σ V : C, {f : V ⟶ X // S f}, fun p ↦ p.1, fun p ↦ p.2.1⟩

omit [HasEqualizers C] [HasPullbacks C] in
/-- The sieve generated by the family of all arrows of a sieve `S` is `S`. -/
theorem preZeroHypercoverOfSieve_sieve₀ {X : C} (S : Sieve X) :
    (preZeroHypercoverOfSieve S).sieve₀ = S := by
  refine le_antisymm ?_ ?_
  · rintro V f ⟨W, h, g, ⟨p⟩, rfl⟩
    exact S.downward_closed p.2.2 h
  · intro V f hf
    exact ⟨V, 𝟙 V, f, .mk (⟨V, ⟨f, hf⟩⟩ : Σ V : C, {f : V ⟶ X // S f}), by simp⟩

/-- **Every object of `A_total` is `a^*` of an object of `A`.** A cartesian `O`-module `F` is
`a^*M` by Stacks 0D9Z. To see that `M` lies in `A`, take an object `U` of `C`: since `K` is a
hypercovering, `U` has a covering `{U_j ⟶ U}` whose members admit morphisms
`φ_j : U_j ⟶ U_{0, τ(j)}` (`degreeZeroSieve_mem`). The restriction of `M` to `C/U_j` is the
restriction along `φ_j` of `M|_{U_{0, τ(j)}}`, which is the `τ(j)`-th component of `F_0` and so
lies in `A_{U_{0, τ(j)}}`; by 0DC2 it lies in `A_{U_j}`, and by 0DC3 `M|_U` lies in `A_U`. -/
theorem exists_pullbackModules_iso_of_totalLocalSerre
    (F : SheafOfModules.{u}
      ((hypercoveringSituation J H).totalRingSheaf (hypercoveringRingedAugmentation J H OC).O))
    (hF : totalLocalSerre J H OC T F) :
    ∃ M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf OC),
      LocalSerreFamily.globalProperty _ T M ∧
      Nonempty ((hypercoveringRingedAugmentation J H
        OC).totalRingedHom.toModulesHom.pullbackModules.obj M ≅ F) := by
  obtain ⟨M, ⟨e⟩⟩ := essImage_pullbackModules_of_hypercoveringCartesianModules J H OC F
    (((hypercoveringSituation J H).isModuleFiberTransitionIso_iff_isCartesianModule
      (hypercoveringRingedAugmentation J H OC).O F).2 hF.1)
  refine ⟨M, fun U ↦ ?_, ⟨e⟩⟩
  have hU := degreeZeroSieve_mem J H U
  rw [← preZeroHypercoverOfSieve_sieve₀ (degreeZeroSieve H.toSimplicialObject U)] at hU
  refine (T.locality U _ hU _).2 fun p ↦ ?_
  obtain ⟨j, ⟨φ⟩⟩ := p.2.2
  have := T.weakSerre p.1
  have h0 := T.restriction φ _ (hF.2 (SimplexCategory.mk 0) j)
  refine (T.A p.1).prop_of_iso ?_ h0
  exact (SheafOfModules.overMap _ φ).mapIso
      ((hypercoveringSummandRestriction J H OC _ j).mapIso
        ((componentModuleRestriction (hypercoveringSituation J H) _ _).mapIso e.symm) ≪≫
      hypercoveringSummandRestrictionPullbackIso J H OC _ j M) ≪≫
    (SheafOfModules.overFunctorMap (Stacks.SheafOfModules.Tensor.ringSheaf OC) φ).app M ≪≫
    ((SheafOfModules.overFunctorMap (Stacks.SheafOfModules.Tensor.ringSheaf OC) p.2.1).app M).symm

end Stacks.CategoryTheory.Hypercovering

end
