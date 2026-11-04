module

public import StacksFrontier.Algebra.Homology.HomotopyCategory.ExactFunctorHomology
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FppfEtaleComparison.ModuleHigherVanishing
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineBaseChangeChart
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartCohomologyVanishing
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartsHaveEnoughObjects
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineHigherPushforwardVanishing
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineHigherPushforwardVanishingUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.DerivedFunctorUpperBoundGeneralTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.DerivedModulePushforward
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePushforwardChartComparison
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedSections.SheafificationOfTheCohomologyPresheaf
public import StacksFrontier.Homology.DerivedIndexing.Basic
public import StacksFrontier.Topology.Sheaves.Cohomology.CechOfPresheavesOfModules.TermFunctorExactness

/-!
# Upper cohomological bounds for the derived direct image along an affine morphism of spaces

Let `f : X ⟶ Y` be an affine morphism of algebraic spaces over a scheme `S` contained in a big
fppf site `B`, and let `E` be an object of `D(𝒪_X)` whose cohomology sheaves are quasi-coherent
on the small étale site.  If `E` lives in degrees `≤ b`, then so does `Rf_*E`.

## Main results

* `AlgebraicGeometry.Space.isLE_derivedModulePushforward_obj_of_isAffineHom` — **[Stacks,
  Tag 08D5] part (2) for an affine morphism of algebraic spaces, with `N = 1`:**
  `(Rf_*E).IsLE b` when `E.IsLE b`.

## Implementation notes

**No `@[stacks 08D5]` attribute is placed.** Tag 08D5 is a statement about *schemes* and has
three parts: its hypothesis is that `f` be quasi-compact and quasi-separated, with an integer
`N = N(X, Y, f)` produced by [Stacks, Tag 01XJ]; part (1) asserts that `Rf_*` carries
`D_QCoh(𝒪_X)` into `D_QCoh(𝒪_Y)` and part (3) that the bound of part (2) survives an arbitrary
base change.  What is proved here is part (2) for an *affine* morphism of *algebraic spaces*,
where `N = 1`.  The scheme-side analogue of this file, with the same qualification, is
`AlgebraicGeometry.isLE_derivedPushforward_obj_of_isAffineHom` in
`StacksFrontier/AlgebraicGeometry/QuasiCoherent/Coherator/AffinePushforwardBounds.lean`.  That is
the case the comparison square of [Stacks, Tag 08GY] needs, and it is a strictly weaker
statement than the tag; neither part (1) nor part (3) is available on the spaces side, so no
covering set of 08D5 is claimed here.

**Why the scheme-side route does not port.** The scheme proof concludes from [Stacks, Tag 0D66]
that `H^i(Rf_*E)` is the sheafification of `V ↦ H^i(f⁻¹V, E)` and then kills that presheaf on
the basis of affine opens.  The site-level form of that input,
`Stacks.Cohomology.UnboundedHigherDirectImageOnSites.cohomologySheavesOfTheDerivedDirectImage`
([Stacks, Tag 0D6I]), is stated for `AlgebraicGeometry.RingedSite.{u, u, u}` — all three
universes equal — while the small étale ringed site of an algebraic space is
`AlgebraicGeometry.RingedSite.{u + 1, u, u}`, its objects living one universe above its
morphisms and its structure rings.  The sheafification step is therefore run by hand, out of the
universe-general `Stacks.Cohomology.SiteCohomologyPresheaf.homotopySheafificationHomologyIso`
([Stacks, Tag 0BKV]) and
`Stacks.Cohomology.ModuleDirectImageOnACover.isZero_moduleSheafification_of_locallyZero`.

**Why the target-generalized engine is not applied to `Rf_*` itself.**
`AlgebraicGeometry.Space.isLE_rightDerivedFunctor_obj_of_isZero_rightDerivedPlus` would give the
bound in one step at target `AlgebraicGeometry.Space.Modules`, fed by [Stacks, Tag 073H].  It
cannot be used there: it asks for `CategoryTheory.Limits.HasExactLimitsOfShape (Discrete ℕ)` on
the target, which is Grothendieck's AB4*, and a countable product of epimorphisms of
sheaves need not be an epimorphism — as
`StacksFrontier/Homology/DerivedCategory/KInjectiveProducts.lean` records.  The engine is used
instead at target `CategoryTheory.ModuleCat`, where AB4* does hold, for the sections over a
single affine étale chart; the passage from those charts to the sheaf `H^i(Rf_*E)` is the
sheafification argument.

**The shape of the argument.** Present `E` as `Q(L)` and take a K-injective resolution `L ⟶ I`
(`AlgebraicGeometry.Space.exists_quasiIso_isKInjective_modules`).  Then `Rf_*E ≅ Q(f_*I)`,
because the derivation unit of any right derived functor of `f_*` is invertible on a K-injective
complex (`AlgebraicGeometry.Space.isIso_app_of_isKInjective_modulePushforward`), so the claim is
the vanishing of the homology *of the complex of sheaves* `f_*I` in degrees `> b`.  That
homology is the sheafification of the homology of the underlying complex of presheaves, whose
sections over an étale chart `V` of `Y` are — on the nose, `f_*` being restriction of sections
along small-chart base change followed by a restriction of scalars
(`AlgebraicGeometry.Space.modulePushforwardChartIso`) — the sections of `I` over `V ×_Y X`.  The
affine charts cover (`AlgebraicGeometry.Space.hasEnoughObjects_isAffineChart`), base change
carries an affine chart to an affine chart
(`AlgebraicGeometry.Space.isAffine_smallBaseChange_obj`), and over an affine chart the engine
with `N = 1` — fed by
`AlgebraicGeometry.Space.isZero_rightDerived_evaluation_of_isAffineChart` — gives
`RΓ(V ×_Y X, E).IsLE b`.

**The local instance attributes carry the universe discipline** of the neighbouring files on the
small étale modules of an algebraic space: `CategoryTheory.SheafOfModules.instAbelian` is
raised, and the universe-pinned homological instances at module universe `u` are made local, so
that instance search does not commit to the module-universe-`max u v r w` instances of
`StacksFrontier/CategoryTheory/Sites/Cohomology/Modules/CohomologyOfModules.lean`.
`AlgebraicGeometry.Space.modulePushforward_additive` is raised for the same reason, and the
additivity of `AlgebraicGeometry.Space.smallBaseChangeModulePushforward` — a `def`, which
instance search does not unfold — is re-enabled from
`StacksFrontier/AlgebraicGeometry/Spaces/AffineHigherPushforwardVanishingUnconditional.lean`.
`CategoryTheory.IsGrothendieckAbelian.enoughInjectives` is deliberately *not* raised: a sibling
file found that it makes elaboration stick on `u + 1 =?= max (u + 1) ?u`.

## References

* [Stacks Project, Tag 08D5](https://stacks.math.columbia.edu/tag/08D5)
* [Stacks Project, Tag 08D4](https://stacks.math.columbia.edu/tag/08D4)
* [Stacks Project, Tag 08F7](https://stacks.math.columbia.edu/tag/08F7)
* [Stacks Project, Tag 073H](https://stacks.math.columbia.edu/tag/073H)
* [Stacks Project, Tag 070K](https://stacks.math.columbia.edu/tag/070K)
* [Stacks Project, Tag 0BKV](https://stacks.math.columbia.edu/tag/0BKV)
* [Stacks Project, Tag 08GY](https://stacks.math.columbia.edu/tag/08GY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

attribute [local instance 5000] SheafOfModules.instAbelian

attribute [local instance] AlgebraicGeometry.Space.isContinuous_smallBaseChange

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] hasProductsOfShape_nat_modules_ringUniverse
attribute [local instance] enoughInjectives_modules_ringUniverse
attribute [local instance] isGrothendieckAbelian_modules_ringUniverse
attribute [local instance 5000] modulePushforward_additive
attribute [local instance] additive_smallBaseChangeModulePushforward
attribute [local instance] additive_smallBaseChangeModulePushforward_modules

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)

/-! ### A K-injective resolution computes the bound of [Stacks, Tag 08D4] part (3) -/

/-- **The complex of `G`-images of a K-injective resolution has no homology above the bound.**
Let `G` be an additive functor from the `𝒪_X`-modules of an algebraic space to an abelian
category with exact countable products, let `G` preserve countable products and let its higher
right derived functors vanish on quasi-coherent modules in every degree `≥ 1`.  If `E` is an
object of `D_QCoh(𝒪_X)` living in degrees `≤ b` and `I` is a K-injective complex representing
`E`, then the complex `G(I)` has no homology in degrees `> b`.

Two inputs are joined.  `I` being K-injective, the derivation unit of the chosen total right
derived functor `RG` is invertible at `I` ([Stacks, Tag 070K], through the K-injective criterion
`hasPointwiseRightDerivedFunctor_and_isIso_app_of_exists_quasiIso_isKInjective` of
`CategoryTheory.Functor`, fed by
`AlgebraicGeometry.Space.exists_quasiIso_isKInjective_modules`), so `RG(E) ≅ Q(G(I))`;
and `RG(E)` lives in degrees `≤ b + 1 - 1 = b` by
`AlgebraicGeometry.Space.isLE_rightDerivedFunctor_obj_of_isZero_rightDerivedPlus`, the upper
bound of [Stacks, Tag 08D4] part (3) at an arbitrary abelian target, with `N = 1`. -/
private theorem isZero_homology_mapHomologicalComplex_obj_of_isKInjective
    {T : Type*} [Category* T] [Abelian T] [HasDerivedCategory T]
    [HasProductsOfShape ℕ T] [HasExactLimitsOfShape (Discrete ℕ) T]
    (G : Modules.{u, u} B S hS F hF ⥤ T) [G.Additive]
    [PreservesLimitsOfShape (Discrete ℕ) G]
    (hvan : ∀ M : Modules.{u, u} B S hS F hF, M.IsQuasicoherentOnSite →
      ∀ p : ℤ, (1 : ℤ) ≤ p → IsZero ((G.rightDerivedPlus p).obj M))
    (E : DerivedCategory (Modules.{u, u} B S hS F hF))
    (hcoh : ∀ j : ℤ, ((DerivedCategory.homologyFunctor
      (Modules.{u, u} B S hS F hF) j).obj E).IsQuasicoherentOnSite)
    (b : ℤ) (hE : E.IsLE b) (I : CochainComplex (Modules.{u, u} B S hS F hF) ℤ)
    (hI : I.IsKInjective) (eQ : DerivedCategory.Q.obj I ≅ E) (i : ℤ) (hi : b < i) :
    IsZero (((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj I).homology i) := by
  have hkey :=
    Functor.hasPointwiseRightDerivedFunctor_and_isIso_app_of_exists_quasiIso_isKInjective
      (G.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
      (exists_quasiIso_isKInjective_modules B S hS F hF)
  have := hkey.1
  have : (G.mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh).HasRightDerivedFunctor
      (HomotopyCategory.quasiIso (Modules.{u, u} B S hS F hF) (ComplexShape.up ℤ)) :=
    Functor.hasRightDerivedFunctor_of_hasPointwiseRightDerivedFunctor _ _
  have hbound := isLE_rightDerivedFunctor_obj_of_isZero_rightDerivedPlus B S hS F hF G
    ((G.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).totalRightDerived
      DerivedCategory.Qh
      (HomotopyCategory.quasiIso (Modules.{u, u} B S hS F hF) (ComplexShape.up ℤ)))
    ((G.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).totalRightDerivedUnit
      DerivedCategory.Qh
      (HomotopyCategory.quasiIso (Modules.{u, u} B S hS F hF) (ComplexShape.up ℤ)))
    1 hvan E hcoh b hE
  have hbound' : (((G.mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh).totalRightDerived DerivedCategory.Qh
      (HomotopyCategory.quasiIso (Modules.{u, u} B S hS F hF)
        (ComplexShape.up ℤ))).obj E).IsLE b := by
    simpa using hbound
  have hzero := DerivedCategory.isZero_of_isLE
    (((G.mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh).totalRightDerived DerivedCategory.Qh
      (HomotopyCategory.quasiIso (Modules.{u, u} B S hS F hF)
        (ComplexShape.up ℤ))).obj E) b i hi
  have hiso := hkey.2 DerivedCategory.Qh
    ((G.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).totalRightDerived
      DerivedCategory.Qh
      (HomotopyCategory.quasiIso (Modules.{u, u} B S hS F hF) (ComplexShape.up ℤ)))
    ((G.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).totalRightDerivedUnit
      DerivedCategory.Qh
      (HomotopyCategory.quasiIso (Modules.{u, u} B S hS F hF) (ComplexShape.up ℤ))) I hI
  refine IsZero.of_iso hzero
    (((DerivedCategory.homologyFunctorFactors T i).app _).symm ≪≫
      (DerivedCategory.homologyFunctor T i).mapIso ?_)
  refine ((DerivedCategory.quotientCompQhIso T).app
    ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj I)).symm ≪≫ ?_
  refine (@asIso _ _ _ _ _ hiso) ≪≫ ?_
  exact ((G.mapHomotopyCategory (ComplexShape.up ℤ) ⋙
    DerivedCategory.Qh).totalRightDerived DerivedCategory.Qh
      (HomotopyCategory.quasiIso (Modules.{u, u} B S hS F hF)
        (ComplexShape.up ℤ))).mapIso
    ((DerivedCategory.quotientCompQhIso (Modules.{u, u} B S hS F hF)).app I ≪≫ eQ)

/-- **The complex of sections of a K-injective resolution over an affine étale chart has no
homology above the bound.**  This is the previous statement at
`G := Γ(W, -) : Mod(𝒪_X) ⥤ Mod(𝒪_X(W))` for `W` an étale chart of `X` whose underlying scheme
is affine: sections over an object of a site preserve countable products, a module category has
exact countable products, and the vanishing of the higher right derived functors in degrees
`≥ 1` is `AlgebraicGeometry.Space.isZero_rightDerived_evaluation_of_isAffineChart`, read in the
`ℤ`-indexed convention by `Stacks.DerivedIndexing.isZero_rightDerivedPlus_obj_iff`. -/
private theorem isZero_homology_evaluationComplex_of_isAffineChart
    (E : DerivedCategory (Modules.{u, u} B S hS F hF))
    (hcoh : ∀ j : ℤ, ((DerivedCategory.homologyFunctor
      (Modules.{u, u} B S hS F hF) j).obj E).IsQuasicoherentOnSite)
    (b : ℤ) (hE : E.IsLE b) (I : CochainComplex (Modules.{u, u} B S hS F hF) ℤ)
    (hI : I.IsKInjective) (eQ : DerivedCategory.Q.obj I ≅ E)
    (W : SmallEtale B S hS F) (hW : IsAffineChart B S hS F W)
    (i : ℤ) (hi : b < i) :
    IsZero ((((SheafOfModules.evaluation
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O)
      (op W)).mapHomologicalComplex (ComplexShape.up ℤ)).obj I).homology i) := by
  have : PreservesLimitsOfShape (Discrete ℕ)
      (SheafOfModules.evaluation (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS F hF).O)
        (op W)) := SheafOfModules.evaluationPreservesLimitsOfShape _ _ _
  refine isZero_homology_mapHomologicalComplex_obj_of_isKInjective B S hS F hF _
    (fun M hM p hp ↦ ?_) E hcoh b hE I hI eQ i hi
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, p = (n : ℤ) := ⟨p.toNat, (Int.toNat_of_nonneg (by omega)).symm⟩
  refine (Stacks.DerivedIndexing.isZero_rightDerivedPlus_obj_iff _
    (rfl : ((n : ℕ) : ℤ) = ((n : ℕ) : ℤ)) M).2 ?_
  exact isZero_rightDerived_evaluation_of_isAffineChart B S hS F hF M hM W hW n (by omega)

/-! ### The sections of the direct image over an étale chart -/

section Pushforward

variable {X Y : AlgebraicSpaces B S hS}

/-- **The sections over an étale chart `W` of `Y` of the base-change direct image of a complex
are its sections over `W ×_Y X`.**  For a representable `f`,
`AlgebraicGeometry.Space.smallBaseChangeModulePushforward` is
`CategoryTheory.SheafOfModules.pushforward` along small-chart base change, so taking the
underlying presheaf of a complex of direct images and evaluating at `W` is evaluating at
`W ×_Y X` followed by restriction of scalars along `f♯`.  Both sides are the same complex of
`𝒪_Y(W)`-modules, on the nose; this is the degreewise form of
`Stacks.Cohomology.SheafifiedHigherDirectImage.pushforward_forget_eq`.

It is recorded as a lemma of its own rather than used as a conversion because the two spellings
are identified only by unfolding the direct image, which exhausts the elaborator's budget when
that happens inside a larger goal. -/
private theorem evaluation_mapHomologicalComplex_smallBaseChangeModulePushforward (f : X ⟶ Y)
    (hrep : yoneda.relativelyRepresentable f.hom)
    (I : CochainComplex (Modules.{u, u} B S hS X.1 X.2) ℤ)
    (W : SmallEtale B S hS Y.1) :
    ((PresheafOfModules.evaluation
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O).obj
      (op W)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      (((SheafOfModules.forget
        (Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B S hS Y.1 Y.2).O)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj
        (((smallBaseChangeModulePushforward.{u, u} B S hS f hrep).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj I)) =
      ((ModuleCat.restrictScalars.{u}
        ((smallBaseChangeSharp B S hS f hrep).hom.app (op W)).hom).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj
        (((SheafOfModules.evaluation
          (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)
          (op ((smallBaseChange B S hS f hrep).obj W))).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj I) := rfl

/-- The homology of a complex vanishes after applying an exact functor iff the exact functor
kills the homology of the original complex. -/
private theorem isZero_homology_map_iff {C D : Type*} [Category* C] [Category* D] [Abelian C]
    [Abelian D] (E : C ⥤ D) [E.Additive] [PreservesFiniteLimits E] [PreservesFiniteColimits E]
    {K : CochainComplex C ℤ} (i : ℤ) :
    IsZero (((E.mapHomologicalComplex (ComplexShape.up ℤ)).obj K).homology i) ↔
      IsZero (E.obj (K.homology i)) :=
  ((Stacks.Homology.exactHomologyIso E i).app K).isZero_iff

/-- **The presheaf-level cohomology of `f_*I` dies over an affine étale chart.**  Let
`f : X ⟶ Y` be a representable affine morphism, let `W` be an étale chart of `Y` whose
underlying scheme is affine, and let `I` be a K-injective complex representing an object `E` of
`D_QCoh(𝒪_X)` living in degrees `≤ b`.  Then the `𝒪_Y(W)`-module of sections over `W` of the
degree-`i` homology of the underlying complex of presheaves of `f_*I` vanishes for `i > b`, the
direct image being taken along small-chart base change.

Evaluation of presheaves of modules and restriction of scalars are both exact, so they commute
with the homology of a complex (`Stacks.Homology.exactHomologyIso`); the sections of `f_*I` over
`W` are the sections of `I` over the base-changed chart `W ×_Y X`
(`AlgebraicGeometry.Space.evaluation_mapHomologicalComplex_smallBaseChangeModulePushforward`),
which is again an affine chart by
`AlgebraicGeometry.Space.isAffine_smallBaseChange_obj`, and there the bound is
`AlgebraicGeometry.Space.isZero_homology_evaluationComplex_of_isAffineChart`. -/
private theorem isZero_evaluation_homology_smallBaseChangeModulePushforward (f : X ⟶ Y)
    (hrep : yoneda.relativelyRepresentable f.hom) (hf : IsAffineHom B S hS f.hom)
    (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (hcoh : ∀ j : ℤ, ((DerivedCategory.homologyFunctor
      (Modules.{u, u} B S hS X.1 X.2) j).obj E).IsQuasicoherentOnSite)
    (b : ℤ) (hE : E.IsLE b) (I : CochainComplex (Modules.{u, u} B S hS X.1 X.2) ℤ)
    (hI : I.IsKInjective) (eQ : DerivedCategory.Q.obj I ≅ E)
    (W : SmallEtale B S hS Y.1) (hW : IsAffineChart B S hS Y.1 W)
    (i : ℤ) (hi : b < i) :
    IsZero ((PresheafOfModules.evaluation
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS Y.1 Y.2).O).obj (op W)).obj
      ((((SheafOfModules.forget
        (Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B S hS Y.1 Y.2).O)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj
        (((smallBaseChangeModulePushforward.{u, u} B S hS f hrep).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj I)).homology i)) := by
  have : PreservesFiniteLimits (ModuleCat.restrictScalars.{u}
      ((smallBaseChangeSharp B S hS f hrep).hom.app (op W)).hom) :=
    ⟨fun _ _ _ ↦ ⟨fun {_} ↦ inferInstance⟩⟩
  have : PreservesFiniteColimits (ModuleCat.restrictScalars.{u}
      ((smallBaseChangeSharp B S hS f hrep).hom.app (op W)).hom) :=
    ⟨fun _ _ _ ↦ ⟨fun {_} ↦ inferInstance⟩⟩
  have hvan := isZero_homology_evaluationComplex_of_isAffineChart B S hS X.1 X.2 E hcoh b hE
    I hI eQ ((smallBaseChange B S hS f hrep).obj W)
    (isAffine_smallBaseChange_obj B S hS f hrep hf W hW) i hi
  refine (isZero_homology_map_iff _ i).1 ?_
  rw [evaluation_mapHomologicalComplex_smallBaseChangeModulePushforward B S hS f hrep I W]
  exact (isZero_homology_map_iff (ModuleCat.restrictScalars.{u}
    ((smallBaseChangeSharp B S hS f hrep).hom.app (op W)).hom) i).2 (Functor.map_isZero _ hvan)

/-- **The same vanishing for the direct image of [Stacks, Tag 03LU].**  For an affine `f` the
direct image `AlgebraicGeometry.Space.modulePushforward` is isomorphic to the base-change direct
image by `AlgebraicGeometry.Space.modulePushforwardChartIso`, affineness supplying
representability through `AlgebraicGeometry.Space.relativelyRepresentable_of_isAffineHom`.  The
comparison is applied degreewise, its compatibility with the differentials being naturality. -/
private theorem isZero_evaluation_homology_modulePushforward (f : X ⟶ Y)
    (hf : IsAffineHom B S hS f.hom)
    (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (hcoh : ∀ j : ℤ, ((DerivedCategory.homologyFunctor
      (Modules.{u, u} B S hS X.1 X.2) j).obj E).IsQuasicoherentOnSite)
    (b : ℤ) (hE : E.IsLE b) (I : CochainComplex (Modules.{u, u} B S hS X.1 X.2) ℤ)
    (hI : I.IsKInjective) (eQ : DerivedCategory.Q.obj I ≅ E)
    (W : SmallEtale B S hS Y.1) (hW : IsAffineChart B S hS Y.1 W)
    (i : ℤ) (hi : b < i) :
    IsZero ((PresheafOfModules.evaluation
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS Y.1 Y.2).O).obj (op W)).obj
      ((((SheafOfModules.forget
        (Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B S hS Y.1 Y.2).O)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj
        (((modulePushforward B S hS f).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj I)).homology i)) := by
  have hrep := relativelyRepresentable_of_isAffineHom B S hS f hf
  have : (modulePushforward B S hS f).PreservesZeroMorphisms := inferInstance
  have : (smallBaseChangeModulePushforward.{u, u} B S hS f hrep).PreservesZeroMorphisms :=
    inferInstance
  have ecx : ((modulePushforward B S hS f).mapHomologicalComplex (ComplexShape.up ℤ)).obj I ≅
      ((smallBaseChangeModulePushforward.{u, u} B S hS f hrep).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj I :=
    HomologicalComplex.Hom.isoOfComponents
      (fun n ↦ (modulePushforwardChartIso B S hS f hrep).app (I.X n))
      (fun n m _ ↦ ((modulePushforwardChartIso B S hS f hrep).hom.naturality (I.d n m)).symm)
  exact IsZero.of_iso (isZero_evaluation_homology_smallBaseChangeModulePushforward B S hS f hrep
      hf E hcoh b hE I hI eQ W hW i hi)
    ((PresheafOfModules.evaluation
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS Y.1 Y.2).O).obj (op W)).mapIso
      ((HomologicalComplex.homologyFunctor
        (PresheafOfModules.{u}
          (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O).obj)
        (ComplexShape.up ℤ) i).mapIso
        (((SheafOfModules.forget
          (Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedSite B S hS Y.1 Y.2).O)).mapHomologicalComplex
          (ComplexShape.up ℤ)).mapIso ecx)))

/-! ### Sheafifying the presheaf-level cohomology -/

/-- **The sheafification of the presheaf-level cohomology of `f_*I` vanishes above the bound.**
Every étale chart of `Y` is covered by affine charts
(`AlgebraicGeometry.Space.hasEnoughObjects_isAffineChart`), and over each of those the sections
of the degree-`i` presheaf cohomology of `f_*I` vanish for `i > b` by
`AlgebraicGeometry.Space.isZero_evaluation_homology_modulePushforward`.  So every section dies
on a covering sieve, and
`Stacks.Cohomology.ModuleDirectImageOnACover.isZero_moduleSheafification_of_locallyZero` kills
the sheafification.  The covering family is a *presieve*: a family of affine charts is almost
never downward closed. -/
private theorem isZero_sheafification_homology_modulePushforward (f : X ⟶ Y)
    (hf : IsAffineHom B S hS f.hom)
    (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (hcoh : ∀ j : ℤ, ((DerivedCategory.homologyFunctor
      (Modules.{u, u} B S hS X.1 X.2) j).obj E).IsQuasicoherentOnSite)
    (b : ℤ) (hE : E.IsLE b) (I : CochainComplex (Modules.{u, u} B S hS X.1 X.2) ℤ)
    (hI : I.IsKInjective) (eQ : DerivedCategory.Q.obj I ≅ E) (i : ℤ) (hi : b < i) :
    IsZero ((PresheafOfModules.sheafification
      (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O).obj)).obj
      ((((SheafOfModules.forget
        (Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B S hS Y.1 Y.2).O)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj
        (((modulePushforward B S hS f).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj I)).homology i)) := by
  refine Stacks.Cohomology.ModuleDirectImageOnACover.isZero_moduleSheafification_of_locallyZero
    (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B S hS Y.1 Y.2).O) _ (fun V x ↦ ?_)
  have hsub : ∀ W' : SmallEtale B S hS Y.1, IsAffineChart B S hS Y.1 W' →
      Subsingleton (ToType (((((SheafOfModules.forget
        (Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B S hS Y.1 Y.2).O)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj
        (((modulePushforward B S hS f).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj I)).homology i).presheaf.obj (op W'))) :=
    fun W' hW' ↦ ModuleCat.isZero_iff_subsingleton.mp
      (isZero_evaluation_homology_modulePushforward B S hS f hf E hcoh b hE I hI eQ W' hW' i hi)
  obtain ⟨ι, Ui, gi, hcov, haffchart⟩ := hasEnoughObjects_isAffineChart B S hS Y.1 V
  refine (SmallEtale.topology B S hS Y.1).superset_covering
    ((Sieve.generate_le_iff (Presieve.ofArrows Ui gi) _).mpr ?_) hcov
  rintro W k ⟨idx⟩
  have := hsub (Ui idx) (haffchart idx)
  exact Subsingleton.elim _ _

/-- **The complex of sheaves `f_*I` has no homology above the bound.**  The degree-`i` homology
sheaf of a complex of sheaves of modules is the sheafification of the degree-`i` homology of the
underlying complex of presheaves, which is
`Stacks.Cohomology.SiteCohomologyPresheaf.homotopySheafificationHomologyIso` — the underived half
of [Stacks, Tag 0BKV], stated at a ringed site with independent universes for its objects, its
morphisms and its structure rings, which is what the small étale ringed site of an algebraic
space needs.  That sheafification vanishes by
`AlgebraicGeometry.Space.isZero_sheafification_homology_modulePushforward`. -/
private theorem isZero_homology_mapHomologicalComplex_modulePushforward (f : X ⟶ Y)
    (hf : IsAffineHom B S hS f.hom)
    (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (hcoh : ∀ j : ℤ, ((DerivedCategory.homologyFunctor
      (Modules.{u, u} B S hS X.1 X.2) j).obj E).IsQuasicoherentOnSite)
    (b : ℤ) (hE : E.IsLE b) (I : CochainComplex (Modules.{u, u} B S hS X.1 X.2) ℤ)
    (hI : I.IsKInjective) (eQ : DerivedCategory.Q.obj I ≅ E) (i : ℤ) (hi : b < i) :
    IsZero ((((modulePushforward B S hS f).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj I).homology i) := by
  refine IsZero.of_iso ?_ ((HomotopyCategory.homologyFunctorFactors
    (Modules.{u, u} B S hS Y.1 Y.2) (ComplexShape.up ℤ) i).app
    (((modulePushforward B S hS f).mapHomologicalComplex (ComplexShape.up ℤ)).obj I)).symm
  refine IsZero.of_iso ?_
    ((Stacks.Cohomology.SiteCohomologyPresheaf.homotopySheafificationHomologyIso
      (smallEtaleRingedSite B S hS Y.1 Y.2) i).app
      ((HomotopyCategory.quotient (Modules.{u, u} B S hS Y.1 Y.2) (ComplexShape.up ℤ)).obj
        (((modulePushforward B S hS f).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj I))).symm
  refine IsZero.of_iso (isZero_sheafification_homology_modulePushforward B S hS f hf E hcoh b hE
    I hI eQ i hi) ((PresheafOfModules.sheafification
      (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS Y.1 Y.2).O).obj)).mapIso ?_)
  exact (DerivedCategory.homologyFunctorFactorsh
      (PresheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B S hS Y.1 Y.2).O).obj) i).app _ ≪≫
    (HomotopyCategory.homologyFunctorFactors
      (PresheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O).obj)
      (ComplexShape.up ℤ) i).app
      (((SheafOfModules.forget
        (Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B S hS Y.1 Y.2).O)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj
        (((modulePushforward B S hS f).mapHomologicalComplex (ComplexShape.up ℤ)).obj I))

/-! ### The bound on the derived direct image -/

/-- **[Stacks, Tag 08D5] part (2) for an affine morphism of algebraic spaces, with `N = 1`.**
Let `f : X ⟶ Y` be an affine morphism of algebraic spaces over a scheme `S` contained in a big
fppf site `B`, let `(Rf, α)` be a right derived functor of the direct image of `𝒪`-modules of
[Stacks, Tag 03LU] on the whole unbounded derived category, and let `E` be an object of
`D(𝒪_X)` whose cohomology sheaves are quasi-coherent on the small étale site.  If `E` lives in
degrees `≤ b`, then `Rf_*E` lives in degrees `≤ b`.

Such a pair `(Rf, α)` exists for every morphism of algebraic spaces, by
`AlgebraicGeometry.Space.hasRightDerivedFunctor_modulePushforward`; stating the bound against a
binder is what lets a caller use the derived direct image it already has.

Present `E` as `Q(L)` and resolve `L` by a K-injective complex
(`AlgebraicGeometry.Space.exists_quasiIso_isKInjective_modules`).  Then `α` is invertible there
(`AlgebraicGeometry.Space.isIso_app_of_isKInjective_modulePushforward`), so `Rf_*E ≅ Q(f_*I)`,
and the claim is the vanishing of the homology of the complex of sheaves `f_*I` in degrees
`> b`, which is
`AlgebraicGeometry.Space.isZero_homology_mapHomologicalComplex_modulePushforward`.

The bound is the one the source gives for `N = 1`, and no degree is lost: the direct image along
an affine morphism has no higher cohomology on quasi-coherent modules ([Stacks, Tag 073H]).  No
`stacks` attribute is placed; see the implementation notes of this file. -/
theorem isLE_derivedModulePushforward_obj_of_isAffineHom (f : X ⟶ Y)
    (hf : IsAffineHom B S hS f.hom)
    (Rf : DerivedCategory (Modules.{u, u} B S hS X.1 X.2) ⥤
      DerivedCategory (Modules.{u, u} B S hS Y.1 Y.2))
    (α : (modulePushforward B S hS f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ Rf)
    [Rf.IsRightDerivedFunctor α
      (HomotopyCategory.quasiIso (Modules.{u, u} B S hS X.1 X.2) (ComplexShape.up ℤ))]
    (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (hcoh : ∀ i : ℤ, ((DerivedCategory.homologyFunctor
      (Modules.{u, u} B S hS X.1 X.2) i).obj E).IsQuasicoherentOnSite)
    (b : ℤ) (hE : E.IsLE b) : (Rf.obj E).IsLE b := by
  obtain ⟨I, s, hI, hs⟩ := exists_quasiIso_isKInjective_modules B S hS X.1 X.2
    (DerivedCategory.Q.objPreimage E)
  have : IsIso (DerivedCategory.Q.map s) := by
    rw [DerivedCategory.isIso_Q_map_iff_quasiIso]
    exact hs
  have eQ : DerivedCategory.Q.obj I ≅ E :=
    (asIso (DerivedCategory.Q.map s)).symm ≪≫ DerivedCategory.Q.objObjPreimageIso E
  have hiso := isIso_app_of_isKInjective_modulePushforward B S hS f DerivedCategory.Qh Rf α I hI
  rw [DerivedCategory.isLE_iff]
  intro i hi
  have hz := IsZero.of_iso (isZero_homology_mapHomologicalComplex_modulePushforward B S hS f hf E
      hcoh b hE I hI eQ i hi)
    ((DerivedCategory.homologyFunctorFactors (Modules.{u, u} B S hS Y.1 Y.2) i).app
      (((modulePushforward B S hS f).mapHomologicalComplex (ComplexShape.up ℤ)).obj I))
  refine IsZero.of_iso hz ((DerivedCategory.homologyFunctor
    (Modules.{u, u} B S hS Y.1 Y.2) i).mapIso ?_)
  refine (Rf.mapIso eQ).symm ≪≫ ?_
  refine (Rf.mapIso ((DerivedCategory.quotientCompQhIso
    (Modules.{u, u} B S hS X.1 X.2)).app I)).symm ≪≫ ?_
  exact (@asIso _ _ _ _ _ hiso).symm ≪≫
    (DerivedCategory.quotientCompQhIso (Modules.{u, u} B S hS Y.1 Y.2)).app
      (((modulePushforward B S hS f).mapHomologicalComplex (ComplexShape.up ℤ)).obj I)

end Pushforward

end AlgebraicGeometry.Space

end
