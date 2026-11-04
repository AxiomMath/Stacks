module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToSheafColimits
public import StacksFrontier.Algebra.Homology.MapHomologicalComplexExactness
public import StacksFrontier.CategoryTheory.Sites.Cohomology.FibredCategory.ModuleDerivedLowerShriek
public import
  StacksFrontier.CategoryTheory.Sites.Cohomology.FibredCategory.ModuleLowerShriekForgetSquare
public import StacksFrontier.CategoryTheory.Sites.Cohomology.FibredCategory.MorphismLowerShriekAcyclic
public import
  StacksFrontier.CategoryTheory.Sites.Cohomology.FibredCategory.ProjectionModuleDerivedLowerShriek
import StacksCore.Tactic.StacksAttribute

/-!
# The acyclicity statement of Stacks 07AC for sheaves of modules in Situation 08PA

Let `u : C' ⥤ C` be a 1-morphism of fibred categories over a ringed site `(D, O_D)`, as in the
standing data of Stacks 08PA, and let `g` be the induced morphism of ringed topoi. This file
discharges the acyclicity statement `MorphismSituation.ModuleLowerShriekAcyclic` of Stacks 07AC
for `g_!` on sheaves of modules, so that **Stacks 08PC part (3) for sheaves of modules** — the
existence of `Lg_! : D(O_{C'}) ⥤ D(O_C)` and its adjunction with `g^*` — holds with no hypothesis
beyond Situation 08PA.

The argument is the one of the proof of Stacks 08PC: by part (2)
(`MorphismSituation.moduleLowerShriekForgetIso`) the underlying abelian sheaves of `g_!` are
computed by `g_!^{Ab}`, so it suffices that `g_!^{Ab}` carries a bounded above acyclic complex
whose terms are direct sums of the abelian sheaves `j_{U'!} O_{U'}` to an acyclic complex. By
`CategoryTheory.Adjunction.map_acyclic_of_extAcyclic` that is the vanishing

`Ext^n(j_{U'!} O_{U'}, g^{-1} I) = 0`, `n ≥ 1`, `I` an injective abelian sheaf on `C`,

which is the step of the source's proof computing `L(g')^{Ab}_! O_{U'}`. It is proved by the
dimension shift of `Stacks.Cohomology.subsingleton_ext_leftAdjoint_obj` against the restriction
along the cartesian lifts at `U'`, exactly as the vanishing for `j_{U'!} ℤ_{U'}` in
`MorphismLowerShriekAcyclic.lean`: `O_{U'}` is the inverse image of the structure sheaf of the
base slice, so `j_{U'!} O_{U'}` is a value of the left adjoint of that restriction.

## Main definitions

* `Stacks.Sites.FibredCategory.MorphismSituation.sourceCartesianLiftRestrictionAdjunction`:
  `j_{U'!} ∘ (π'_{U'})^{-1}` is left adjoint to the restriction along the cartesian lifts at `U'`.
* `Stacks.Sites.FibredCategory.MorphismSituation.toSheafExtensionByZeroUnitIso`: the abelian sheaf
  underlying `j_{U'!} O_{U'}` is `j_{U'!} (π'_{U'})^{-1}` of the structure sheaf of the base slice.

## Main results

* `Stacks.Sites.FibredCategory.MorphismSituation.extAcyclic_extensionByZero_inverseImage`:
  Stacks 0D6X along `u` for `j_{U'!} (π'_{U'})^{-1} Z`.
* `MorphismSituation.extAcyclic_toSheaf_of_isSumOfExtensionByZeroUnits`, in the namespace
  `Stacks.Sites.FibredCategory`: direct sums of the `j_{U'!} O_{U'}` are `Ext`-acyclic for
  `g_!^{Ab} ⊣ g^{-1}`.
* `Stacks.Sites.FibredCategory.MorphismSituation.moduleLowerShriekAcyclic`: the acyclicity
  statement of Stacks 07AC for `g_!` on sheaves of modules.
* `MorphismSituation.hasPointwiseLeftDerivedModuleLowerShriekUnconditional` and
  `MorphismSituation.derivedModuleLowerShriekAdjunctionUnconditional`, in the namespace
  `Stacks.Sites.FibredCategory`: **Stacks 08PC part (3) for sheaves of modules**.

## References

* [Stacks Project, Tag 08PC](https://stacks.math.columbia.edu/tag/08PC)
* [Stacks Project, Tag 07AC](https://stacks.math.columbia.edu/tag/07AC)
* [Stacks Project, Tag 0D6X](https://stacks.math.columbia.edu/tag/0D6X)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.Sites.FibredCategory.MorphismSituation

universe u₀ u₁ u₂ v₀ v₁ v₂ w

variable (S : MorphismSituation.{u₀, u₁, u₂, v₀, v₁, v₂, max w u₀ u₁ u₂ v₀ v₁ v₂})

/-- The adjunction whose right adjoint is the restriction along the cartesian lifts at `U'`: the
inverse image along the localized source projection `π'_{U'}`, followed by extension by zero along
`C'/U' ⥤ C'`, is left adjoint to `MorphismSituation.morphismLiftRestriction S U'`. -/
def sourceCartesianLiftRestrictionAdjunction (U' : S.source) :
    (sourceSliceProjection S U').sheafPushforwardContinuous
        AddCommGrpCat.{max w u₀ u₁ u₂ v₀ v₁ v₂} (S.sourceTopology.over U')
        (S.base.J.over (S.p.obj (S.u.obj U'))) ⋙
      (Over.forget U').sheafPullback AddCommGrpCat.{max w u₀ u₁ u₂ v₀ v₁ v₂}
        (S.sourceTopology.over U') S.sourceTopology ⊣
    morphismLiftRestriction S U' :=
  have := sourceSliceProjection_isContinuous S U'
  have := sourceSliceCartesianSection_isContinuous S U'
  have : (S.sourceTopology.over U').WEqualsLocallyBijective
      AddCommGrpCat.{max w u₀ u₁ u₂ v₀ v₁ v₂} :=
    Stacks.Cohomology.SiteModules.site_wEqualsLocallyBijective_addCommGrp.{max u₂ v₂, v₂,
      max w u₀ u₁ u₂ v₀ v₁ v₂} (J := S.sourceTopology.over U')
  ((sourceSliceCartesianSection_adjunction S U').sheafPushforwardAdjunction
      AddCommGrpCat.{max w u₀ u₁ u₂ v₀ v₁ v₂}
      (J := S.sourceTopology.over U') (K := S.base.J.over (S.p.obj (S.u.obj U')))).comp
    ((Over.forget U').sheafAdjunctionContinuous AddCommGrpCat.{max w u₀ u₁ u₂ v₀ v₁ v₂}
      (S.sourceTopology.over U') S.sourceTopology)

/-- **Stacks 0D6X along a 1-morphism of fibred categories, for the extension by zero of an
inverse image from the base slice.** For an abelian sheaf `Z` on the base slice `D/p(u(U'))`,
`Ext^n(j_{U'!} (π'_{U'})^{-1} Z, g^{-1} I) = 0` for every injective abelian sheaf `I` on `C`
and every `n ≥ 1`.

`j_{U'!} (π'_{U'})^{-1} Z` is the value at `Z` of the left adjoint of the restriction along the
cartesian lifts at `U'` (`sourceCartesianLiftRestrictionAdjunction`), which is exact, preserves
injectives and carries `g^{-1} I` to an injective sheaf (Stacks 08PB,
`morphismLiftRestrictionInverseImageIso`); so dimension shifting
(`Stacks.Cohomology.subsingleton_ext_leftAdjoint_obj`) applies. -/
theorem extAcyclic_extensionByZero_inverseImage (U' : S.source)
    (Z : Sheaf (S.base.J.over (S.p.obj (S.u.obj U'))) AddCommGrpCat.{max w u₀ u₁ u₂ v₀ v₁ v₂}) :
    S.abelianLowerShriekAdjunction.extAcyclic
      (((sourceSliceProjection S U').sheafPushforwardContinuous
          AddCommGrpCat.{max w u₀ u₁ u₂ v₀ v₁ v₂} (S.sourceTopology.over U')
          (S.base.J.over (S.p.obj (S.u.obj U'))) ⋙
        (Over.forget U').sheafPullback AddCommGrpCat.{max w u₀ u₁ u₂ v₀ v₁ v₂}
          (S.sourceTopology.over U') S.sourceTopology).obj Z) := by
  intro I hI n hn
  let A := AddCommGrpCat.{max w u₀ u₁ u₂ v₀ v₁ v₂}
  have : ∀ V : S.base.C, HasSheafify (S.base.J.over V) A := fun V =>
    hasSheafify_addCommGrpCat.{max u₀ v₀, v₀, max w u₀ u₁ u₂ v₀ v₁ v₂} (S.base.J.over V)
  have := sourceSliceCartesianSection_isContinuous S U'
  obtain ⟨h₁, h₂, h₃⟩ := morphismLiftRestriction_exact S U'
  obtain ⟨-, -, h₃'⟩ := (totalSituation S).cartesianLiftRestriction_exact (S.u.obj U')
  have hRI : Injective ((morphismLiftRestriction S U').obj
      (S.abelianInverseImage.obj I)) :=
    Injective.of_iso ((morphismLiftRestrictionInverseImageIso S U').app I).symm
      (((totalSituation S).cartesianLiftRestriction (S.u.obj U')).injective_obj I)
  have hadd₁ : (S.sourceTopology.overPullback A U').Additive :=
    CategoryTheory.Functor.additive_sheafPushforwardContinuous (Over.forget U')
      (S.sourceTopology.over U') S.sourceTopology A
  have : (morphismLiftRestriction S U').PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_of_additive _
  exact Stacks.Cohomology.subsingleton_ext_leftAdjoint_obj (morphismLiftRestriction S U')
    (S.sourceCartesianLiftRestrictionAdjunction U') Z n hn _ hRI

attribute [local instance] hasWeakSheafify_sourceTopology hasWeakSheafify_totalTopology
  wEqualsLocallyBijective_sourceTopology wEqualsLocallyBijective_totalTopology

section ExtensionByZeroUnit

attribute [local instance] Stacks.SheafOfModules.siteHasSheafify
  Stacks.SheafOfModules.siteWEqualsLocallyBijective

/-- **The abelian sheaf underlying `j_{U'!} O_{U'}` is a value of the left adjoint of the
restriction along the cartesian lifts at `U'`.** Forgetting the module structure commutes with
extension by zero along a localization morphism
(`Stacks.SheafOfModules.lowerShriekForgetOverForgetIso`), and the abelian sheaf underlying
`O_{U'}` is the inverse image along the localized source projection of the abelian sheaf
underlying the structure sheaf of the base slice
(`MorphismSituation.sourceStructureRingSheafRestrictionIso`). -/
def toSheafExtensionByZeroUnitIso (U' : S.source) :
    (SheafOfModules.toSheaf.{max w u₀ u₁ u₂ v₀ v₁ v₂} S.sourceModuleRing).obj
        (Cohomology.DerivedLowerShriek.extensionByZeroUnit S.sourceModuleRing U') ≅
      ((Over.forget U').sheafPullback AddCommGrpCat.{max w u₀ u₁ u₂ v₀ v₁ v₂}
          (S.sourceTopology.over U') S.sourceTopology).obj
        (((sourceSliceProjection S U').sheafPushforwardContinuous
            AddCommGrpCat.{max w u₀ u₁ u₂ v₀ v₁ v₂} (S.sourceTopology.over U')
            (S.base.J.over (S.p.obj (S.u.obj U')))).obj
          ((sheafCompose (S.base.J.over (S.p.obj (S.u.obj U')))
              (forget₂ RingCat.{max w u₀ u₁ u₂ v₀ v₁ v₂}
                AddCommGrpCat.{max w u₀ u₁ u₂ v₀ v₁ v₂})).obj
            ((S.base.J.overPullback RingCat.{max w u₀ u₁ u₂ v₀ v₁ v₂}
                (S.p.obj (S.u.obj U'))).obj
              (Stacks.SheafOfModules.Tensor.ringSheaf S.baseTopos.O)))) :=
  ((Stacks.SheafOfModules.lowerShriekForgetOverForgetIso.{max w u₀ u₁ u₂ v₀ v₁ v₂}
      S.sourceTopology
      (Stacks.SheafOfModules.Tensor.ringSheaf (S.sourceTopos S.pi').O :
        Sheaf S.sourceTopology RingCat.{max w u₀ u₁ u₂ v₀ v₁ v₂}) U').app
      (SheafOfModules.unit _)).symm ≪≫
    ((Over.forget U').sheafPullback AddCommGrpCat.{max w u₀ u₁ u₂ v₀ v₁ v₂}
        (S.sourceTopology.over U') S.sourceTopology).mapIso
      ((sheafCompose (S.sourceTopology.over U')
          (forget₂ RingCat.{max w u₀ u₁ u₂ v₀ v₁ v₂}
            AddCommGrpCat.{max w u₀ u₁ u₂ v₀ v₁ v₂})).mapIso
        ((S.sourceTopology.overPullback RingCat.{max w u₀ u₁ u₂ v₀ v₁ v₂} U').mapIso
          S.sourceStructureRingSheafRestrictionIso))

/-- **`j_{U'!} O_{U'}` is acyclic for `g_!^{Ab}`.** The abelian sheaf underlying the extension by
zero of the structure sheaf of `C'/U'` has vanishing `Ext^n(-, g^{-1} I)` for every injective
abelian sheaf `I` on `C` and every `n ≥ 1`: by `toSheafExtensionByZeroUnitIso` it is the
extension by zero of an inverse image from the base slice, where
`extAcyclic_extensionByZero_inverseImage` applies. -/
theorem extAcyclic_toSheaf_extensionByZeroUnit (U' : S.source) :
    S.abelianLowerShriekAdjunction.extAcyclic
      ((SheafOfModules.toSheaf.{max w u₀ u₁ u₂ v₀ v₁ v₂} S.sourceModuleRing).obj
        (Cohomology.DerivedLowerShriek.extensionByZeroUnit S.sourceModuleRing U')) :=
  S.abelianLowerShriekAdjunction.extAcyclic_of_iso (S.toSheafExtensionByZeroUnitIso U').symm
    (S.extAcyclic_extensionByZero_inverseImage U' _)

end ExtensionByZeroUnit

/-- `forget : Mod(O_{C'}) ⥤ Ab(C')`, with its target spelled at the inherited topology
`S.sourceTopology`, which is where `g_!^{Ab}` is defined. -/
def sourceModuleForget : SheafOfModules.{max w u₀ u₁ u₂ v₀ v₁ v₂} S.sourceModuleRing ⥤
    Sheaf S.sourceTopology AddCommGrpCat.{max w u₀ u₁ u₂ v₀ v₁ v₂} :=
  SheafOfModules.toSheaf _

/-- `forget : Mod(O_C) ⥤ Ab(C)`, with its target spelled at the inherited topology
`S.totalTopology`. -/
def totalModuleForget : SheafOfModules.{max w u₀ u₁ u₂ v₀ v₁ v₂} S.totalModuleRing ⥤
    Sheaf S.totalTopology AddCommGrpCat.{max w u₀ u₁ u₂ v₀ v₁ v₂} :=
  SheafOfModules.toSheaf _

/-- The forgetful functor `Mod(O_{C'}) ⥤ Ab(C')` is additive. -/
instance sourceModuleForget_additive : S.sourceModuleForget.Additive :=
  inferInstanceAs (SheafOfModules.toSheaf _).Additive

/-- The forgetful functor `Mod(O_C) ⥤ Ab(C)` is additive. -/
instance totalModuleForget_additive : S.totalModuleForget.Additive :=
  inferInstanceAs (SheafOfModules.toSheaf _).Additive

/-- The forgetful functor `Mod(O_{C'}) ⥤ Ab(C')` is faithful. -/
instance sourceModuleForget_faithful : S.sourceModuleForget.Faithful :=
  inferInstanceAs (SheafOfModules.toSheaf _).Faithful

/-- The forgetful functor `Mod(O_C) ⥤ Ab(C)` is faithful. -/
instance totalModuleForget_faithful : S.totalModuleForget.Faithful :=
  inferInstanceAs (SheafOfModules.toSheaf _).Faithful

/-- The forgetful functor `Mod(O_{C'}) ⥤ Ab(C')` preserves finite limits. -/
instance sourceModuleForget_preservesFiniteLimits :
    PreservesFiniteLimits S.sourceModuleForget :=
  inferInstanceAs (PreservesFiniteLimits (SheafOfModules.toSheaf S.sourceModuleRing))

/-- The forgetful functor `Mod(O_C) ⥤ Ab(C)` preserves finite limits. -/
instance totalModuleForget_preservesFiniteLimits :
    PreservesFiniteLimits S.totalModuleForget :=
  inferInstanceAs (PreservesFiniteLimits (SheafOfModules.toSheaf S.totalModuleRing))

/-- The forgetful functor `Mod(O_{C'}) ⥤ Ab(C')` preserves finite colimits. -/
instance sourceModuleForget_preservesFiniteColimits :
    PreservesFiniteColimits S.sourceModuleForget :=
  Stacks.SheafOfModules.instPreservesFiniteColimitsToSheaf S.sourceModuleRing

/-- The forgetful functor `Mod(O_C) ⥤ Ab(C)` preserves finite colimits. -/
instance totalModuleForget_preservesFiniteColimits :
    PreservesFiniteColimits S.totalModuleForget :=
  Stacks.SheafOfModules.instPreservesFiniteColimitsToSheaf S.totalModuleRing

/-- `g_!^{Ab}` preserves zero morphisms, being additive. -/
instance (priority := high) abelianLowerShriek_preservesZeroMorphisms :
    S.abelianLowerShriek.PreservesZeroMorphisms :=
  Functor.preservesZeroMorphisms_of_additive _

/-- `g_!^{Ab}` preserves finite colimits, being a left adjoint. -/
instance (priority := high) abelianLowerShriek_preservesFiniteColimits :
    PreservesFiniteColimits S.abelianLowerShriek :=
  have : PreservesColimitsOfSize.{0, 0} S.abelianLowerShriek :=
    have : PreservesColimitsOfSize.{max w u₀ u₁ u₂ v₀ v₁ v₂, max w u₀ u₁ u₂ v₀ v₁ v₂}
        S.abelianLowerShriek := S.abelianLowerShriekAdjunction.leftAdjoint_preservesColimits
    preservesColimitsOfSize_shrink _
  PreservesColimitsOfSize.preservesFiniteColimits _

/-- **Stacks 08PC part (2)**, `moduleLowerShriekForgetIso`, with the two forgetful functors
spelled at the inherited topologies. -/
def moduleLowerShriekForgetIsoInherited :
    S.moduleLowerShriek ⋙ S.totalModuleForget ≅ S.sourceModuleForget ⋙ S.abelianLowerShriek :=
  S.moduleLowerShriekForgetIso

/-- **Direct sums of the `j_{U'!} O_{U'}` are acyclic for `g_!^{Ab}`.** The forgetful functor
commutes with direct sums (`SheafOfModules.preservesColimitsOfShape_toSheaf`), and the
`Ext`-acyclic class is closed under direct sums and isomorphisms. -/
theorem extAcyclic_toSheaf_of_isSumOfExtensionByZeroUnits
    (M : SheafOfModules.{max w u₀ u₁ u₂ v₀ v₁ v₂} S.sourceModuleRing)
    (hM : Cohomology.DerivedLowerShriek.IsSumOfExtensionByZeroUnits S.sourceModuleRing M) :
    S.abelianLowerShriekAdjunction.extAcyclic (S.sourceModuleForget.obj M) := by
  obtain ⟨ι, U, ⟨eM⟩⟩ := hM
  let A := AddCommGrpCat.{max w u₀ u₁ u₂ v₀ v₁ v₂}
  let Y : ι → SheafOfModules.{max w u₀ u₁ u₂ v₀ v₁ v₂} S.sourceModuleRing := fun i =>
    Cohomology.DerivedLowerShriek.extensionByZeroUnit S.sourceModuleRing (U i)
  let X : ι → Sheaf S.sourceTopology A := fun i => S.sourceModuleForget.obj (Y i)
  have : HasColimitsOfShape (Discrete ι) (Sheaf S.sourceTopology A) :=
    Stacks.Cohomology.DerivedLowerShriek.hasColimitsOfShape_discrete_sheafAb S.sourceTopology ι
  have : HasColimit (Discrete.functor X) := HasColimitsOfShape.has_colimit _
  have : PreservesColimitsOfShape (Discrete ι) S.sourceModuleForget :=
    SheafOfModules.preservesColimitsOfShape_toSheaf _
  exact S.abelianLowerShriekAdjunction.extAcyclic_of_iso
    ((PreservesCoproduct.iso S.sourceModuleForget Y).symm ≪≫ S.sourceModuleForget.mapIso eM)
    (S.abelianLowerShriekAdjunction.extAcyclic_coproduct X fun i =>
      S.extAcyclic_toSheaf_extensionByZeroUnit (U i))

/-- **The acyclicity statement of Stacks 07AC for `g_!` on sheaves of modules, in Situation
08PA.** Lower shriek along the 1-morphism of fibred categories carries every bounded above
acyclic complex of `O_{C'}`-modules whose terms are direct sums of the `j_{U'!} O_{U'}` to an
acyclic complex.

Forgetting the module structure is exact and faithful, so it detects acyclicity, and by Stacks
08PC part (2) (`moduleLowerShriekForgetIso`) the underlying complex of abelian sheaves of
`g_! L` is `g_!^{Ab}` of the underlying complex of `L`. That complex is bounded above and
acyclic with terms direct sums of the abelian sheaves `j_{U'!} O_{U'}`, which are `Ext`-acyclic
for `g_!^{Ab} ⊣ g^{-1}` by `extAcyclic_toSheaf_of_isSumOfExtensionByZeroUnits`; so
`CategoryTheory.Adjunction.map_acyclic_of_extAcyclic` concludes. -/
theorem moduleLowerShriekAcyclic : S.ModuleLowerShriekAcyclic := by
  intro a L hLE hLP hLac
  let K : CochainComplex (Sheaf S.sourceTopology AddCommGrpCat.{max w u₀ u₁ u₂ v₀ v₁ v₂}) ℤ :=
    (S.sourceModuleForget.mapHomologicalComplex (ComplexShape.up ℤ)).obj L
  have hKLE : K.IsStrictlyLE a :=
    (CochainComplex.isStrictlyLE_mapHomologicalComplex_obj_iff L S.sourceModuleForget a).2 hLE
  have hK : K.Acyclic :=
    (HomologicalComplex.acyclic_map_iff_of_preservesHomology L S.sourceModuleForget).2 hLac
  have hA := S.abelianLowerShriekAdjunction.map_acyclic_of_extAcyclic K a hK
    fun n => S.extAcyclic_toSheaf_of_isSumOfExtensionByZeroUnits (L.X n) (hLP n)
  let e := (NatIso.mapHomologicalComplex S.moduleLowerShriekForgetIsoInherited
    (ComplexShape.up ℤ)).app L
  exact (HomologicalComplex.acyclic_map_iff_of_preservesHomology _ S.totalModuleForget).1
    fun i => (exactAt_iff_of_quasiIsoAt e.inv i).1 (hA i)

section Derived

attribute [local instance] HasDerivedCategory.standard

/-- **Stacks 08PC part (3) for sheaves of modules, existence.** Degreewise `g_!`, followed by the
localization of the homotopy category of `Mod(O_C)`, has a pointwise left derived functor along
the localization of the homotopy category of `Mod(O_{C'})`; that is, `Lg_! : D(O_{C'}) ⥤ D(O_C)`
exists. This is `MorphismSituation.hasPointwiseLeftDerivedModuleLowerShriek` with the acyclicity
statement of Stacks 07AC supplied by `moduleLowerShriekAcyclic`. -/
@[stacks 08PC "part (3), modules: existence of `Lg_! : D(O_{C'}) ⥤ D(O_C)`"]
instance hasPointwiseLeftDerivedModuleLowerShriekUnconditional :
    (S.moduleLowerShriekOnHomotopy ⋙ DerivedCategory.Qh).HasPointwiseLeftDerivedFunctor
      S.moduleSourceQuasiIso :=
  S.hasPointwiseLeftDerivedModuleLowerShriek S.moduleLowerShriekAcyclic

/-- **Stacks 08PC part (3) for sheaves of modules, the adjunction.** The unbounded left derived
lower-shriek functor `Lg_! : D(O_{C'}) ⥤ D(O_C)` is left adjoint to `g^* = g^{-1}` on the
unbounded derived categories. This is `MorphismSituation.derivedModuleLowerShriekAdjunction`
(Stacks 09T5) with the acyclicity statement of Stacks 07AC supplied by
`moduleLowerShriekAcyclic`; nothing beyond Situation 08PA is assumed. -/
@[stacks 08PC "part (3), modules: the adjunction `Lg_! ⊣ g^*`"]
def derivedModuleLowerShriekAdjunctionUnconditional :
    S.derivedModuleLowerShriek ⊣ S.derivedModuleInverseImage :=
  S.derivedModuleLowerShriekAdjunction S.moduleLowerShriekAcyclic

end Derived

end Stacks.Sites.FibredCategory.MorphismSituation

end
