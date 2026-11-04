module

public import StacksFrontier.AlgebraicGeometry.Cohomology.InjectiveQcoh.ChartBaseChangeAcyclicity
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FppfEtaleComparison.ModuleHigherVanishing
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartsHaveEnoughObjects
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineHigherPushforwardVanishing
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSpacePresentedSections
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleModulePullbackInjectives
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePushforwardGlobalSections
public import StacksFrontier.AlgebraicGeometry.Spaces.StructureSharpBaseChange
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Modules.GlobalSectionsInitialForget

/-!
# Stacks 072W for the direct image of modules along a morphism of algebraic spaces

Let `π : 𝒜 ⥤ Mod(𝒪_𝒟)` be an additive functor from an abelian category with enough injectives.
Then `R^p π F = 0` as soon as every object of `𝒟` carries a covering family whose members `W`
have vanishing degree-`p` derived sections `R^p (π(-)(W))` at `F`.  For
`π = AlgebraicGeometry.Space.modulePushforward f` those derived sections are the cohomology
`H^p(V ×_Y X, -)` of the chart base change, which makes `R^p f_*ℳ` vanish as soon as that
cohomology does on an affine étale chart covering of each chart of `Y`.

## Main results

* `Stacks.Cohomology.SectionsDirectImageOnACover.isZero_rightDerived_of_presieve`: the criterion
  for a pushforward described by its sections.
* `AlgebraicGeometry.Space.isZero_rightDerived_evaluation_modulePushforward`: the derived sections
  of `f_*ℳ` over an étale chart `V` of `Y` vanish with `H^p(V ×_Y X, ℳ)`.
* `AlgebraicGeometry.Space.chartLocalCohomologyDetectsHigherDirectImage`: Stacks 072W read for
  `AlgebraicGeometry.Space.modulePushforward`, in the vanishing form carried as a hypothesis by
  `StacksFrontier/AlgebraicGeometry/Cohomology/InjectiveQcoh/ChartBaseChangeAcyclicity.lean`.
* `AlgebraicGeometry.Space.isZero_rightDerived_modulePushforward_injective_isNoetherian`:
  **Stacks 09TL, part (2)**, with no carried input.

## Implementation notes

*Why the criterion is stated for an abstract `π`.*  The proof of Stacks 072W uses only the
formula `(f_*G)(V) = G(u V)` for the sections of the direct image, so it applies verbatim to any
additive functor into sheaves of modules once its presheaf of sections is named: a continuous
functor of sites is not needed.  That matters here because
`AlgebraicGeometry.Space.modulePushforward` is not a site pushforward — it is restriction of
scalars along the structure map of Stacks 03G8 applied to the spaces-étale direct image
conjugated by the comparison equivalence of Stacks 03G1 — and the identification of the two is
unavailable: the comparison restriction is an equivalence only for coefficient categories
carrying the limits of `CategoryTheory.Functor.IsDenseSubsite`, which `RingCat.{u}`, the
coefficients of the structure sheaf, does not.

*How the sections of `f_*` are computed.*  Not through that identification but geometrically.
Sections over an étale chart `V` of `Y` are global sections of the restriction to the chart
space of `V`, the identity chart being terminal there
(`AlgebraicGeometry.Space.isTerminalIdEtaleChart`); the restriction of `f_*` to that chart space
is the direct image along the base change `V ×_Y X ⟶ V` (Stacks 03LX,
`AlgebraicGeometry.Space.modulePushforwardEtaleBaseChangeIso`); and global sections are
unchanged by a direct image
(`AlgebraicGeometry.Space.globalSectionsModulePushforwardIso`).  Each of the three is
unconditional and none of them needs `f` to be representable, which is what makes the result
available at the binders of Stacks 09TL.  Passing to right derived functors uses that étale
restriction is exact and preserves injectives (Stacks 03F3, part (1), as
`AlgebraicGeometry.Space.preservesInjectiveObjects_etaleModulePullback`), so that
`CategoryTheory.Functor.rightDerived` may be moved past it.

*The affine charts.*  The covering family at a chart `V` of `Y` is a family of affine étale
charts of `V`, from `AlgebraicGeometry.Space.hasEnoughObjects_isAffineChart`; affineness is used
only by the input of the criterion, which is Stacks 09TL, part (1) at the chart base change.

*Two spellings of one module of sections.*  The sections of a module over the chart `V` of `Y`
and its sections over the identity chart of the chart space of `V` are the same module over the
same ring, but the ring has two spellings, so the two `CategoryTheory.ModuleCat` categories are
equal only after unfolding.  `CategoryTheory.Functor.associator` is therefore used wherever two
composites differ by associativity — matching them by unification instead exhausts the
heartbeats — and the additivity of the composite is supplied at the spelling that
`CategoryTheory.Functor.rightDerived` asks for, namely with its
`CategoryTheory.Preadditive` arguments written as `CategoryTheory.Abelian.toPreadditive`, as in
`StacksFrontier/AlgebraicGeometry/Spaces/AffineHigherPushforwardVanishingUnconditional.lean`.

## References

* [Stacks Project, Tag 072W](https://stacks.math.columbia.edu/tag/072W)
* [Stacks Project, Tag 09TL](https://stacks.math.columbia.edu/tag/09TL)
* [Stacks Project, Tag 03LX](https://stacks.math.columbia.edu/tag/03LX)
* [Stacks Project, Tag 03F3](https://stacks.math.columbia.edu/tag/03F3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Cohomology.SiteModules

attribute [local instance 5000] SheafOfModules.instAbelian

/-- The right derived functor of `F ⋙ G` vanishes at `X` iff `G` of that of `F` does, when `G`
preserves homology. -/
private theorem isZero_rightDerived_comp_iff {A B E : Type*} [Category A] [Category B]
    [Category E] [Abelian A] [Abelian B] [Abelian E] [HasInjectiveResolutions A]
    (F : A ⥤ B) [F.Additive] (G : B ⥤ E) [G.Additive] [G.PreservesHomology]
    [(F ⋙ G).Additive] (p : ℕ) (X : A) :
    IsZero (((F ⋙ G).rightDerived p).obj X) ↔ IsZero (G.obj ((F.rightDerived p).obj X)) := by
  obtain ⟨e⟩ := rightDerived_comp_iso_of_preservesHomology F G p X
  exact ⟨fun h ↦ h.of_iso e, fun h ↦ h.of_iso e.symm⟩

namespace Stacks.Cohomology.SectionsDirectImageOnACover

universe v₁ u₁ uRing uMod

variable {Dsite : Type u₁} [Category.{v₁} Dsite] {J𝒟 : GrothendieckTopology Dsite}
  (O𝒟 : Sheaf J𝒟 RingCat.{uRing})
  [HasSheafify J𝒟 AddCommGrpCat.{uMod}]
  [J𝒟.WEqualsLocallyBijective AddCommGrpCat.{uMod}]
  [J𝒟.HasSheafCompose (forget AddCommGrpCat.{uMod})]
  {A : Type*} [Category* A] [Abelian A] [HasInjectiveResolutions A]
  (π : A ⥤ SheafOfModules.{uMod} O𝒟) [π.Additive]

/-- The presheaf of sections of `π`: the functor `F ↦ (V ↦ (π F)(V))`. -/
abbrev sectionsFunctor : A ⥤ PresheafOfModules.{uMod} O𝒟.obj :=
  π ⋙ SheafOfModules.forget O𝒟

/-- `π` is the sheafification of its presheaf of sections: the underlying presheaf of a sheaf of
modules is already a sheaf, so the counit of
`CategoryTheory.PresheafOfModules.sheafificationAdjunction` at the identity is an
isomorphism. -/
def isoSectionsFunctorCompSheafification :
    π ≅ sectionsFunctor O𝒟 π ⋙ PresheafOfModules.sheafification (𝟙 O𝒟.obj) := by
  haveI cI : (SheafOfModules.forget O𝒟 ⋙ PresheafOfModules.restrictScalars (𝟙 O𝒟.obj)) ⋙
      PresheafOfModules.sheafification (𝟙 O𝒟.obj) ≅ 𝟭 (SheafOfModules O𝒟) :=
    asIso (PresheafOfModules.sheafificationAdjunction (𝟙 O𝒟.obj)).counit
  refine π.rightUnitor.symm ≪≫ π.isoWhiskerLeft cI.symm ≪≫ ?_
  exact Iso.refl _

/-- **A higher direct image vanishes if its derived sections vanish on a covering family.**  Let
`π : 𝒜 ⥤ Mod(𝒪_𝒟)` be additive.  If every object `V` of `𝒟` carries a covering presieve all of
whose members `W` have `R^p (π(-)(W))` vanishing at `F`, then `R^p π F = 0`.

This is Stacks 072W, by the proof of
`Stacks.Cohomology.HigherDirectImage.higherDirectImage_iso_sheafify_cohomologyPresheaf`: `π` is
the sheafification of its presheaf of sections and sheafification is exact, so `R^p π F` is the
sheafification of the presheaf `V ↦ R^p (π(-)(V)) F`, which the hypothesis makes locally zero.
Only the sections of `π` enter, so no continuous functor of sites is involved. -/
theorem isZero_rightDerived_of_presieve (p : ℕ) (F : A)
    (h : ∀ V : Dsite, ∃ R : Presieve V, Sieve.generate R ∈ J𝒟 V ∧
      ∀ ⦃W : Dsite⦄ (g : W ⟶ V), R g →
        IsZero (((sectionsFunctor O𝒟 π ⋙
          PresheafOfModules.evaluation O𝒟.obj (op W)).rightDerived p).obj F)) :
    IsZero ((π.rightDerived p).obj F) := by
  have hhom : (PresheafOfModules.sheafification (𝟙 O𝒟.obj)).PreservesHomology :=
    sheafification_preservesHomology O𝒟
  have hadd : (PresheafOfModules.sheafification (𝟙 O𝒟.obj)).Additive :=
    sheafification_additive O𝒟
  have e0 := (Stacks.Cohomology.CompositeRightDerived.rightDerivedNatIso
    (isoSectionsFunctorCompSheafification O𝒟 π) p).app F
  obtain ⟨e1⟩ := rightDerived_comp_iso_of_preservesHomology (sectionsFunctor O𝒟 π)
    (PresheafOfModules.sheafification (𝟙 O𝒟.obj)) p F
  refine IsZero.of_iso ?_ (e0 ≪≫ e1.symm)
  refine Stacks.Cohomology.ModuleDirectImageOnACover.isZero_moduleSheafification_of_locallyZero
    O𝒟 _ (fun V x ↦ ?_)
  obtain ⟨R, hgen, hvan⟩ := h V
  refine J𝒟.superset_covering ((Sieve.generate_le_iff R _).mpr (fun W g hg ↦ ?_)) hgen
  have hz : IsZero ((PresheafOfModules.evaluation O𝒟.obj (op W)).obj
      (((sectionsFunctor O𝒟 π).rightDerived p).obj F)) :=
    (isZero_rightDerived_comp_iff (sectionsFunctor O𝒟 π) _ p F).mp (hvan g hg)
  have hsub : Subsingleton
      (ToType ((((sectionsFunctor O𝒟 π).rightDerived p).obj F).presheaf.obj (op W))) :=
    ModuleCat.isZero_iff_subsingleton.mp hz
  exact Subsingleton.elim _ _

end Stacks.Cohomology.SectionsDirectImageOnACover

namespace AlgebraicGeometry.Space

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y : AlgebraicSpaces B S hS}

attribute [local instance] hasInjectiveResolutions_modules enoughInjectives_modules
  modulePushforward_additive etaleModulePullback_additive
  preservesFiniteLimits_etaleModulePullback preservesFiniteColimits_etaleModulePullback
  preservesInjectiveObjects_etaleModulePullback

/-! ### The derived sections of a direct image over the terminal chart of a chart space -/

/-- The identity chart of the chart space of an étale chart `V` of `Y`, read in the opposite of
the small étale site, is an initial object.  This is
`AlgebraicGeometry.Space.isTerminalIdEtaleChart` in the opposite category. -/
def isInitialOpIdEtaleChart (V : SmallEtale B S hS Y.1) :
    IsInitial (op (idEtaleChart B S hS ((SmallEtale.toOver B S hS Y.1).obj V))) :=
  IsInitial.ofUniqueHom
    (fun W ↦ ((isTerminalIdEtaleChart B S hS
      ((SmallEtale.toOver B S hS Y.1).obj V)).from W.unop).op)
    (fun _ _m ↦ Quiver.Hom.unop_inj ((isTerminalIdEtaleChart B S hS
      ((SmallEtale.toOver B S hS Y.1).obj V)).hom_ext _ _))

/-- The structure sheaf of the chart space of an étale chart `V` of `Y`, in the spaces-étale
spelling of that chart space which the base change of `f` to `V` uses. -/
abbrev chartBaseRingSheaf (V : SmallEtale B S hS Y.1) :=
  Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS
    ((SpacesEtale.toSpaces B S hS Y).obj ((comparisonFunctor B S hS Y).obj V)).1
    ((SpacesEtale.toSpaces B S hS Y).obj ((comparisonFunctor B S hS Y).obj V)).2).O

/-- The derived sections, over the terminal chart of the chart space of `V`, of the direct image
along the base change of `f` to `V`. -/
abbrev chartBaseChangeTerminalSections (f : X ⟶ Y) (V : SmallEtale B S hS Y.1) :
    Modules.{u, u} B S hS (chartBaseChangeSpace B S hS f V).1
        (chartBaseChangeSpace B S hS f V).2 ⥤
      ModuleCat.{u} ((chartBaseRingSheaf B S hS V).obj.obj
        (op (idEtaleChart B S hS ((SmallEtale.toOver B S hS Y.1).obj V)))) :=
  modulePushforward B S hS (chartBaseChangeProjection B S hS f V) ⋙
    SheafOfModules.evaluation.{u} (chartBaseRingSheaf B S hS V)
      (op (idEtaleChart B S hS ((SmallEtale.toOver B S hS Y.1).obj V)))

/-- **The degree-`p` derived sections of `f'_*𝒩` over the terminal chart of the chart space of an
étale chart `V` of `Y` vanish with `H^p(V ×_Y X, 𝒩)`**, for `f'` the base change of `f` to `V`.

Global sections of a module on the chart space are its sections over the identity chart, which is
terminal there, and a direct image does not change global sections
(`AlgebraicGeometry.Space.globalSectionsModulePushforwardIso`); both identifications are natural
in the module, so they pass to right derived functors. -/
theorem isZero_rightDerived_chartBaseChangeTerminalSections (f : X ⟶ Y)
    (V : SmallEtale B S hS Y.1) (p : ℕ)
    (N : Modules.{u, u} B S hS (chartBaseChangeSpace B S hS f V).1
      (chartBaseChangeSpace B S hS f V).2)
    (h : IsZero (((globalSectionsFunctor.{u + 1, u, u, u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS
        (chartBaseChangeSpace B S hS f V).1
        (chartBaseChangeSpace B S hS f V).2).O)).rightDerived p).obj N)) :
    IsZero (((chartBaseChangeTerminalSections B S hS f V).rightDerived p).obj N) := by
  have e : chartBaseChangeTerminalSections B S hS f V ⋙
      (forget₂ (ModuleCat.{u} ((chartBaseRingSheaf B S hS V).obj.obj
          (op (idEtaleChart B S hS ((SmallEtale.toOver B S hS Y.1).obj V)))))
        AddCommGrpCat.{u} ⋙ AddCommGrpCat.uliftFunctor.{u + 1, u}) ≅
      globalSectionsAb B S hS (chartBaseChangeSpace B S hS f V) :=
    Functor.associator (modulePushforward B S hS (chartBaseChangeProjection B S hS f V))
        (SheafOfModules.evaluation.{u} (chartBaseRingSheaf B S hS V)
          (op (idEtaleChart B S hS ((SmallEtale.toOver B S hS Y.1).obj V)))) _ ≪≫
      Functor.isoWhiskerLeft (modulePushforward B S hS (chartBaseChangeProjection B S hS f V))
        (globalSectionsFunctorForgetIsoEvaluation (chartBaseRingSheaf B S hS V)
          (op (idEtaleChart B S hS ((SmallEtale.toOver B S hS Y.1).obj V)))
          (isInitialOpIdEtaleChart B S hS V)).symm ≪≫
      globalSectionsModulePushforwardIso B S hS (chartBaseChangeProjection B S hS f V)
  have d3 := (Stacks.Cohomology.CompositeRightDerived.rightDerivedNatIso e p).app N
  have hz := (isZero_rightDerived_comp_iff _ _ p N).mp
    (((isZero_rightDerived_comp_iff _ (forget₂ _ AddCommGrpCat.{u + 1}) p N).mpr
      (Functor.map_isZero _ h)).of_iso d3)
  refine (IsZero.iff_id_eq_zero _).mpr (Functor.map_injective
    (forget₂ (ModuleCat.{u} ((chartBaseRingSheaf B S hS V).obj.obj
        (op (idEtaleChart B S hS ((SmallEtale.toOver B S hS Y.1).obj V)))))
      AddCommGrpCat.{u} ⋙ AddCommGrpCat.uliftFunctor.{u + 1, u}) ?_)
  exact (CategoryTheory.Functor.map_id _ _).trans
    (((IsZero.iff_id_eq_zero _).mp hz).trans (CategoryTheory.Functor.map_zero _ _ _).symm)

/-! ### Stacks 072W for the direct image of modules along a morphism of algebraic spaces -/

/-- **The degree-`p` derived sections of `f_*ℳ` over an étale chart `V` of `Y` vanish with
`H^p(V ×_Y X, ℳ)`.**

The restriction of `f_*` to the chart space of `V` is the direct image along the base change of
`f` to `V`, by Stacks 03LX; the sections of a restriction over the identity chart are the
sections over `V`; and étale restriction is exact and preserves injectives, so the right derived
functor may be moved past it. -/
theorem isZero_rightDerived_evaluation_modulePushforward (f : X ⟶ Y)
    (V : SmallEtale B S hS Y.1) (p : ℕ) (M : Modules.{u, u} B S hS X.1 X.2)
    (h : IsZero (((globalSectionsFunctor.{u + 1, u, u, u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS
        (chartBaseChangeSpace B S hS f V).1
        (chartBaseChangeSpace B S hS f V).2).O)).rightDerived p).obj
      ((etaleModulePullback B S hS (chartBaseChangeInclusion B S hS f V)
        (isEtale_chartBaseChangeInclusion B S hS f V)).obj M))) :
    IsZero (((modulePushforward B S hS f ⋙ SheafOfModules.evaluation.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O)
      (op V)).rightDerived p).obj M) := by
  have hadd : @Functor.Additive (Modules.{u, u} B S hS X.1 X.2)
      (ModuleCat.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS Y.1 Y.2).O).obj.obj (op V))) _ _
      Abelian.toPreadditive Abelian.toPreadditive
      (etaleModulePullback.{u, u} B S hS (chartBaseChangeInclusion B S hS f V)
        (isEtale_chartBaseChangeInclusion B S hS f V) ⋙
        chartBaseChangeTerminalSections B S hS f V) :=
    inferInstanceAs ((etaleModulePullback.{u, u} B S hS (chartBaseChangeInclusion B S hS f V)
      (isEtale_chartBaseChangeInclusion B S hS f V) ⋙
      chartBaseChangeTerminalSections B S hS f V).Additive)
  have eB : modulePushforward B S hS f ⋙ SheafOfModules.evaluation.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O)
        (op V) ≅
      etaleModulePullback.{u, u} B S hS (chartBaseChangeInclusion B S hS f V)
          (isEtale_chartBaseChangeInclusion B S hS f V) ⋙
        chartBaseChangeTerminalSections B S hS f V :=
    (Functor.associator (modulePushforward B S hS f)
        (etaleModulePullback B S hS (chartToSpace B S hS Y V)
          (isEtale_chartToSpace B S hS Y V))
        (SheafOfModules.evaluation.{u} (chartBaseRingSheaf B S hS V)
          (op (idEtaleChart B S hS ((SmallEtale.toOver B S hS Y.1).obj V))))).symm ≪≫
      (Functor.isoWhiskerRight (modulePushforwardEtaleBaseChangeIso B S hS
          (chartBaseChangeInclusion B S hS f V) (chartBaseChangeProjection B S hS f V) f
          (chartToSpace B S hS Y V) (isPullback_chartBaseChangeInclusion B S hS f V)
          (isEtale_chartToSpace B S hS Y V)) _).symm ≪≫
      Functor.associator (etaleModulePullback B S hS (chartBaseChangeInclusion B S hS f V)
          (isEtale_chartBaseChangeInclusion B S hS f V))
        (modulePushforward B S hS (chartBaseChangeProjection B S hS f V)) _
  refine ((isZero_rightDerived_chartBaseChangeTerminalSections B S hS f V p _ h).of_iso
    ((Stacks.Cohomology.CompositeRightDerived.rightDerivedNatIso eB p).app M ≪≫
      (Stacks.Cohomology.CompositeRightDerived.compRightDerivedNatIso
        (etaleModulePullback B S hS (chartBaseChangeInclusion B S hS f V)
          (isEtale_chartBaseChangeInclusion B S hS f V))
        (chartBaseChangeTerminalSections B S hS f V) p).app M))

/-- **Stacks 072W for `AlgebraicGeometry.Space.modulePushforward`**, in its vanishing form:
`R^p f_*ℳ = 0` as soon as `H^p(V ×_Y X, ℳ) = 0` for every affine étale scheme chart `V` of `Y`.

The derived sections of `f_*ℳ` over a chart `V` of `Y` are `H^p(V ×_Y X, ℳ)` by
`AlgebraicGeometry.Space.isZero_rightDerived_evaluation_modulePushforward`, and the affine étale
charts of `V` are a covering family of it
(`AlgebraicGeometry.Space.hasEnoughObjects_isAffineChart`), so
`Stacks.Cohomology.SectionsDirectImageOnACover.isZero_rightDerived_of_presieve` applies. -/
theorem chartLocalCohomologyDetectsHigherDirectImage (p : ℕ) :
    ChartLocalCohomologyDetectsHigherDirectImage B S hS p := by
  intro X' Y' f M hvan
  refine Stacks.Cohomology.SectionsDirectImageOnACover.isZero_rightDerived_of_presieve
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y'.1 Y'.2).O)
    (modulePushforward B S hS f) p M.obj (fun V ↦ ?_)
  obtain ⟨I, Ui, k, hcov, haff⟩ := hasEnoughObjects_isAffineChart B S hS Y'.1 V
  refine ⟨Presieve.ofArrows Ui k, hcov, ?_⟩
  rintro W m ⟨i⟩
  refine (isZero_rightDerived_evaluation_modulePushforward B S hS f (Ui i) p M.obj
    (hvan (Ui i) (haff i))).of_iso
    ((Stacks.Cohomology.CompositeRightDerived.rightDerivedNatIso
      (Functor.associator (modulePushforward B S hS f)
        (SheafOfModules.forget.{u}
          (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y'.1 Y'.2).O))
        (PresheafOfModules.evaluation.{u}
          (Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedSite B S hS Y'.1 Y'.2).O).obj (op (Ui i)))) p).app M.obj)

/-! ### Stacks 09TL, part (2) -/

/-- **Stacks 09TL, part (2).**  Let `X` be a Noetherian algebraic space over a scheme `S`, let
`𝒥` be an injective object of `QCoh(𝒪_X)` and let `f : X ⟶ Y` be a morphism of algebraic spaces
with `Y` quasi-separated.  Then `R^p f_*𝒥 = 0` for `p > 0`.

This is
`AlgebraicGeometry.Space.isZero_rightDerived_modulePushforward_of_injective_of_isNoetherian`
with its input `hdetect` discharged by
`AlgebraicGeometry.Space.chartLocalCohomologyDetectsHigherDirectImage`. -/
@[stacks 09TL "part (2)"]
theorem isZero_rightDerived_modulePushforward_injective_isNoetherian
    (hZ : B.Contains (⊤_ Scheme.{u})) {X Y : AlgebraicSpaces B S hS}
    (hX : IsNoetherian B S hS hZ X.1)
    (hYqs : IsAbsolutelyQuasiSeparated B S hS hZ Y.1)
    (J : QuasicoherentSheaves.{u, u} B S hS X.1 X.2) [Injective J]
    (f : X ⟶ Y) (p : ℕ) (hp : 0 < p) :
    IsZero (((modulePushforward B S hS f).rightDerived p).obj J.obj) :=
  isZero_rightDerived_modulePushforward_of_injective_of_isNoetherian B S hS hZ hX hYqs J f p hp
    (chartLocalCohomologyDetectsHigherDirectImage B S hS p)

end AlgebraicGeometry.Space

end
