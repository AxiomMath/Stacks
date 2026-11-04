module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import StacksFrontier.CategoryTheory.Localization.LeftDerivedByResolutions
public import StacksFrontier.Homology.KFlat.Flat
public import StacksFrontier.Homology.KFlat.Iso
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.ExtensionByZeroBaseChange
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.KFlatResolvingDatum
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.Unconditional
public import StacksFrontier.Topology.Sheaves.Cohomology.KFlat.PullbackFromTheStalkCriterion
public import StacksFrontier.Topology.Sheaves.OpenImmersion.ModuleExtensionByZeroExact

/-!
# Derived base change of extension by zero along a morphism of ringed spaces

Let `f : (X, 𝒪_X) ⟶ (Y, 𝒪_Y)` be a morphism of ringed spaces, let `U` be an open subspace of
`Y` and let `U' = f^{-1}U`.  Write `G_Y = j_{U,!}j_U^*` and `G_X = j_{U',!}j_{U'}^*` for the
functors which cut a sheaf of modules down to the open subspace and extend it back by zero.
Both are exact, so each induces a functor on derived categories, and the underived base change
isomorphism `G_Y ⋙ f^* ≅ f^* ⋙ G_X` of
`Stacks.Cohomology.ExtensionByZeroBaseChange.modulePullbackExtensionRestrictionIso` descends to
an isomorphism

`D(G_Y) ⋙ Lf^* ≅ Lf^* ⋙ D(G_X)`

of functors `D(𝒪_Y) ⟶ D(𝒪_X)`, with no flatness hypothesis on `f`.

The single mathematical input is that `G_Y` preserves K-flatness, which is what makes
`D(G_Y) ⋙ Lf^*` a left derived functor of `K(G_Y) ⋙ K(f^*)`: K-flatness is stalkwise
(Stacks 06YB), the stalk complex of `G_Y K` agrees with that of `K` inside `U` and vanishes
outside it, so stalkwise K-flatness transfers.

## Derived-category model

Every statement below mentioning a derived category sits at
`CategoryTheory.HasDerivedCategory.standard`, seated as a local instance, which is the model
the Stacks 0DI7 development uses.  It is *not* the locally small model
`Stacks.Duality.derivedPullback` / `AlgebraicGeometry.Scheme.Modules.hasDerivedCategory` of
`StacksFrontier.Homology.DerivedCategory.LocallySmall`: the two models give equivalent but
unequal categories, so nothing here says anything about that one.  The statements of part one
(`kFlatComplex_extensionRestriction`, `isKFlat_extensionRestriction`) mention no derived
category and are model-independent.

## Main results

* `Stacks.Cohomology.ExtensionByZeroBaseChangeDerived.kFlatComplex_extensionRestriction` and
  `Stacks.Cohomology.ExtensionByZeroBaseChangeDerived.isKFlat_extensionRestriction`:
  **`j_{U,!}j_U^*` preserves K-flat complexes**, on cochain complexes and on the unbounded
  homotopy category respectively.
* `Stacks.Cohomology.ExtensionByZeroBaseChangeDerived.derivedPullbackExtensionRestrictionIso`:
  the derived base change isomorphism `D(G_Y) ⋙ Lf^* ≅ Lf^* ⋙ D(G_X)`.
* `derivedPullbackExtensionRestrictionIso_hom_comparison` in the same namespace: the
  isomorphism is the unique one compatible with the two canonical comparisons of the derived
  pullback and with the underived base change isomorphism.

## Implementation notes

*Where the two sides come from.*  `Lf^* ⋙ D(G_X)` is a left derived functor of
`K(f^*) ⋙ D(G_X)` for formal reasons, by
`CategoryTheory.LeftDerivedByResolutions.isLeftDerivedFunctor_postcomp_of_resolutions`
(`StacksFrontier/CategoryTheory/Localization/LeftDerivedByResolutions.lean`, not Mathlib): a
functor derived by resolutions stays derived after postcomposition.  `D(G_Y) ⋙ Lf^*` is a left
derived functor of `K(G_Y) ⋙ K(f^*)` by
`CategoryTheory.LeftDerivedByResolutions.isLeftDerivedFunctor_of_isIso_on_resolutions` in the
same file, taken at the K-flat class, and *that* is where K-flatness of `G_Y K` is consumed:
both its hypotheses — that the underived composite inverts the quasi-isomorphisms between
K-flat complexes, and that its comparison is invertible on them — need `G_Y K` to be K-flat
when `K` is.  The isomorphism is then `CategoryTheory.Functor.leftDerivedNatIso` at the
underived base change, and its characterisation is
`CategoryTheory.Functor.leftDerivedNatTrans_fac`.

*What the compatibility says.*  The underived statement
`Stacks.Cohomology.ExtensionByZeroBaseChange.modulePullbackExtensionRestrictionIso_hom_counit`
pins the underived isomorphism down by the counits `j_!j^* ⟶ 𝟭`.  At the derived level the
counits are replaced by the canonical comparisons `Q ⋙ L? ⟶ K(?)` of the two left derived
functors, and `derivedPullbackExtensionRestrictionIso_hom_comparison` is the resulting
characterisation: it pins the derived isomorphism down relative to the underived one, which is
itself pinned down by the counits.  A statement about an induced counit
`D(j_{U',!}j_{U'}^*) ⟶ 𝟭` is *not* proved here: no such transformation is constructed in this
file.  This is not because `CategoryTheory.Functor.mapDerivedCategory` lacks an action on
natural transformations; it has one — `CategoryTheory.NatTrans.mapDerivedCategory`
(`StacksFrontier/AlgebraicGeometry/Perfect/Approximation/OpenSubscheme.lean`, with its API in
`StacksFrontier/CategoryTheory/Localization/NatTransMapDerivedCategory.lean`).  Whoever wants the
induced counit here has that action available; it is only the construction at this particular
adjunction that is absent.

*Exactness of restriction.*  `j^*` has adjoints on both sides — `j_! ⊣ j^* ⊣ j_*`
(`ExtensionByZeroModules.openImmersionTriple`) — so it preserves all limits and all colimits.
The two resulting instances are seated here because they are otherwise available only as a
`private lemma`.

*K-flatness spellings.*  `Stacks.Cohomology.KFlatDerivedPullback.KFlatComplex` is
`CochainComplex.KFlatBifunctor.KFlat` at the tensor product of sheaves of modules, while the
stalk criterion `Stacks.SheafOfModules.KFlatStalkCriterion.kFlat_iff_stalkwise` is stated for
`Stacks.SheafOfModules.KFlat.KFlat`; the two are the same proposition
(`Stacks.SheafOfModules.KFlat.kFlat_iff_kFlatBifunctor` is `Iff.rfl`), and likewise
`structureSheafRing Y` and `Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf`
are equal by `rfl` but invisibly so.  Every crossing below therefore happens in term position,
where the conversion check runs at default transparency, and never by `rw`.

*No Stacks tag.*  There is no Stacks numbering for base change of `j_!` on a ringed space.
Tag 03S6 is the small-étale-site statement and already sits on
`AlgebraicGeometry.moduleExtensionByZeroBaseChangeIso`, Tag 08HA on
`AlgebraicGeometry.Space.isIso_restrictExtensionByZeroMap` and Tag 00AB on
`ExtensionByZeroModules.full_and_faithful_and_essImage_jShriek`.

## References

* [Stacks Project, Tag 00AB](https://stacks.math.columbia.edu/tag/00AB)
* [Stacks Project, Tag 064K](https://stacks.math.columbia.edu/tag/064K)
* [Stacks Project, Tag 06XZ](https://stacks.math.columbia.edu/tag/06XZ)
* [Stacks Project, Tag 06YB](https://stacks.math.columbia.edu/tag/06YB)
* [Stacks Project, Tag 06YJ](https://stacks.math.columbia.edu/tag/06YJ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open RingedSpaceModuleAdjunction ExtensionByZeroModules
open Stacks.Cohomology.ExtensionByZeroBaseChange
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces

universe u

-- `ExtensionByZeroModules.jStar_preservesFiniteLimits` and `jStar_preservesFiniteColimits`
-- used to be declared here. They are general facts about the adjoint triple `j_! ⊣ j^* ⊣ j_*`
-- that have nothing to do with base change, and they are now hosted once, at the same fully
-- qualified names, in the common ancestor
-- `StacksFrontier.Topology.Sheaves.OpenImmersion.ModuleExtensionByZeroExact` (publicly imported
-- above), next to the corresponding `jShriek` instances.

namespace Stacks.Cohomology.ExtensionByZeroBaseChangeDerived

/-! ### A recognition principle for K-flatness of a complex of modules

Transport of K-flatness along an isomorphism of complexes is the general fact
`CochainComplex.KFlat.of_iso`, kept with `CochainComplex.KFlat` itself. -/

/-- A cochain complex of modules all of whose terms are zero objects is K-flat: it is bounded
above and its terms, being subsingletons, are free and hence flat, so Stacks 064K applies. -/
theorem kFlat_of_forall_isZero {R : Type u} [CommRing R]
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (h : ∀ i, IsZero (K.X i)) : K.KFlat := by
  have hLE : K.IsStrictlyLE 0 := ⟨fun i _ => h i⟩
  have hflat : ∀ n : ℤ, Module.Flat R (K.X n) := by
    intro n
    have : Subsingleton (K.X n) := by
      rw [← ModuleCat.isZero_iff_subsingleton]; exact h n
    infer_instance
  exact CochainComplex.KFlat.kFlat_of_flat.{u, u} K 0

/-! ### `j_{W,!}j_W^*` preserves K-flat complexes -/

section KFlat

variable {Y : RingedSpace.{u, u}} (W : Opens Y.carrier)

/-- The counit of `j_{W,!} ⊣ j_W^*` applied in each degree: a morphism of cochain complexes
`j_{W,!}j_W^*K ⟶ K`. -/
def extensionRestrictionComplexCounit
    (K : CochainComplex (SheafOfModules.{u} (structureSheafRing Y)) ℤ) :
    ((jStar W (structureSheafRing Y) ⋙ jShriek W (structureSheafRing Y)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj K ⟶ K where
  f i := (jShriekAdjunction W (structureSheafRing Y)).counit.app (K.X i)
  comm' i j _ := ((jShriekAdjunction W (structureSheafRing Y)).counit.naturality (K.d i j)).symm

/-- Inside `W` the degreewise counit `j_{W,!}j_W^*K ⟶ K` is invertible on module stalks: the
counit becomes invertible after `j_W^*`, hence on every stalk inside `W`. -/
lemma isIso_stalkMap_extensionRestrictionComplexCounit
    (K : CochainComplex (SheafOfModules.{u} (structureSheafRing Y)) ℤ)
    (x : Y.carrier) (hx : x ∈ W) (i : ℤ) :
    IsIso ((AlgebraicGeometry.SheafOfModules.stalkFunctor (structureSheafRing Y) x).map
      ((extensionRestrictionComplexCounit W K).f i)) :=
  (isIso_stalkMap_iff (structureSheafRing Y) x _).2
    (isIso_stalk_of_isIso_jStar_map (structureSheafRing Y) W _
      (isIso_jStar_map_counit (structureSheafRing Y) W (K.X i)) x hx)

/-- At a point of `W` the stalk complex of `j_{W,!}j_W^*K` is the stalk complex of `K`. -/
def stalkComplexExtensionRestrictionIso
    (K : CochainComplex (SheafOfModules.{u} (structureSheafRing Y)) ℤ) (x : Y.carrier)
    (hx : x ∈ W) :
    AlgebraicGeometry.SheafOfModules.stalkComplex Y.sheaf x
        (((jStar W (structureSheafRing Y) ⋙ jShriek W (structureSheafRing Y)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj K) ≅
      AlgebraicGeometry.SheafOfModules.stalkComplex Y.sheaf x K :=
  HomologicalComplex.Hom.isoOfComponents
    (fun i => @asIso _ _ _ _ _ (isIso_stalkMap_extensionRestrictionComplexCounit W K x hx i))
    (fun i j hij =>
      (((AlgebraicGeometry.SheafOfModules.stalkFunctor (structureSheafRing Y)
        x).mapHomologicalComplex (ComplexShape.up ℤ)).map
          (extensionRestrictionComplexCounit W K)).comm' i j hij)

/-- Outside `W` every term of the stalk complex of `j_{W,!}j_W^*K` is a zero object, by
Stacks 00AB. -/
lemma isZero_stalkObj_extensionRestriction
    (K : CochainComplex (SheafOfModules.{u} (structureSheafRing Y)) ℤ) (x : Y.carrier) (hx : x ∉ W)
    (i : ℤ) :
    IsZero ((AlgebraicGeometry.SheafOfModules.stalkComplex Y.sheaf x
      (((jStar W (structureSheafRing Y) ⋙ jShriek W (structureSheafRing Y)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj K)).X i) :=
  (isZero_stalkObj_iff (structureSheafRing Y) x _).2
    (isZero_stalk_jShriek W (structureSheafRing Y) ((jStar W (structureSheafRing Y)).obj (K.X i))
      x hx)

/-- **Extension by zero of a restriction preserves K-flatness.**  If `K` is a K-flat complex
of `𝒪_Y`-modules then so is `j_{W,!}j_W^*K`.

K-flatness is stalkwise (Stacks 06YB), the stalk complex of `j_{W,!}j_W^*K` is that of `K` at a
point of `W` and is degreewise zero elsewhere, and a degreewise zero complex is K-flat. -/
theorem kFlatComplex_extensionRestriction
    (K : CochainComplex (SheafOfModules.{u} (structureSheafRing Y)) ℤ)
    (hK : Stacks.Cohomology.KFlatDerivedPullback.KFlatComplex Y K) :
    Stacks.Cohomology.KFlatDerivedPullback.KFlatComplex Y
      (((jStar W (structureSheafRing Y) ⋙ jShriek W (structureSheafRing Y)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj K) := by
  have hst : AlgebraicGeometry.SheafOfModules.KFlatStalkwise Y.sheaf K :=
    (Stacks.SheafOfModules.KFlatStalkCriterion.kFlat_iff_stalkwise Y.sheaf K).1 hK
  refine (Stacks.SheafOfModules.KFlatStalkCriterion.kFlat_iff_stalkwise Y.sheaf _).2 ?_
  intro x
  let := StacksDraft.StalkTensor.commRing_stalk_ringSheaf Y.sheaf x
  by_cases hx : x ∈ W
  · exact CochainComplex.KFlat.of_iso (stalkComplexExtensionRestrictionIso W K x hx).symm (hst x)
  · exact kFlat_of_forall_isZero _ fun i => isZero_stalkObj_extensionRestriction W K x hx i

/-- `kFlatComplex_extensionRestriction` as a statement about the K-flat class on the unbounded
homotopy category: `K(j_{W,!}j_W^*)` preserves `Stacks.Cohomology.KFlatDerivedPullback.IsKFlat`.
This is the form the resolving-class criterion for a left derived functor consumes. -/
theorem isKFlat_extensionRestriction
    (K : HomotopyCategory (SheafOfModules.{u} (structureSheafRing Y)) (ComplexShape.up ℤ))
    (hK : Stacks.Cohomology.KFlatDerivedPullback.IsKFlat Y K) :
    Stacks.Cohomology.KFlatDerivedPullback.IsKFlat Y
      (((jStar W (structureSheafRing Y) ⋙ jShriek W (structureSheafRing Y)).mapHomotopyCategory
        (ComplexShape.up ℤ)).obj K) :=
  kFlatComplex_extensionRestriction W K.as hK

end KFlat

/-! ### The derived base change isomorphism -/

attribute [local instance] HasDerivedCategory.standard

section Derived

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y) (U : Opens Y.carrier)

/-- `K(j_{W,!}j_W^*)` carries quasi-isomorphisms of the homotopy category to
quasi-isomorphisms, because `j_{W,!}j_W^*` is exact. -/
lemma quasiIso_mapHomotopyCategory_extensionRestriction {Y : RingedSpace.{u, u}}
    (U : Opens Y.carrier)
    {K M : HomotopyCategory (SheafOfModules.{u} (structureSheafRing Y)) (ComplexShape.up ℤ)}
    (s : K ⟶ M)
    (hs : HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing Y))
      (ComplexShape.up ℤ) s) :
    HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing Y)) (ComplexShape.up ℤ)
      (((jStar U (structureSheafRing Y) ⋙ jShriek U (structureSheafRing Y)).mapHomotopyCategory
        (ComplexShape.up ℤ)).map s) := by
  rw [← DerivedCategory.isIso_Qh_map_iff]
  have h1 : IsIso (DerivedCategory.Qh.map s) :=
    Localization.inverts DerivedCategory.Qh
      (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing Y)) (ComplexShape.up ℤ))
      s hs
  have h2 : IsIso ((DerivedCategory.Qh ⋙
      (jStar U (structureSheafRing Y) ⋙
        jShriek U (structureSheafRing Y)).mapDerivedCategory).map s) := by
    dsimp only [Functor.comp_map]
    infer_instance
  exact (NatIso.isIso_map_iff
    (jStar U (structureSheafRing Y) ⋙
      jShriek U (structureSheafRing Y)).mapDerivedCategoryFactorsh s).1 h2

/-- The underived base change isomorphism read on the homotopy category of `𝒪_Y`-modules:
`K(j_{U,!}j_U^*) ⋙ K(f^*) ≅ K(f^*) ⋙ D(j_{U',!}j_{U'}^*)`, the target of the second factor
being pushed past the localization `Q` by
`CategoryTheory.Functor.mapDerivedCategoryFactorsh`. -/
def extensionRestrictionHomotopyPullbackIso :
    (jStar U (structureSheafRing Y) ⋙ jShriek U (structureSheafRing Y)).mapHomotopyCategory
          (ComplexShape.up ℤ) ⋙
        pullbackOnHomotopy f ≅
      pullbackOnHomotopy f ⋙
        (jStar ((Opens.map f.hom.base).obj U) (structureSheafRing X) ⋙
          jShriek ((Opens.map f.hom.base).obj U) (structureSheafRing X)).mapDerivedCategory :=
  (Functor.associator _ _ DerivedCategory.Qh).symm ≪≫
    Functor.isoWhiskerRight
      (Functor.mapHomotopyCategoryCompIso (modulePullbackExtensionRestrictionIso f U)
          (ComplexShape.up ℤ) ≪≫
        (Functor.mapHomotopyCategoryCompIso (Iso.refl (modulePullback f ⋙
          (jStar ((Opens.map f.hom.base).obj U) (structureSheafRing X) ⋙
            jShriek ((Opens.map f.hom.base).obj U) (structureSheafRing X))))
          (ComplexShape.up ℤ)).symm) DerivedCategory.Qh ≪≫
    Functor.associator _ _ DerivedCategory.Qh ≪≫
    Functor.isoWhiskerLeft _
      (jStar ((Opens.map f.hom.base).obj U) (structureSheafRing X) ⋙
        jShriek ((Opens.map f.hom.base).obj U)
          (structureSheafRing X)).mapDerivedCategoryFactorsh.symm ≪≫
    (Functor.associator _ DerivedCategory.Qh _).symm

/-- The canonical comparison exhibiting `D(j_{U,!}j_U^*) ⋙ Lf^*` as a left derived functor of
`K(j_{U,!}j_U^*) ⋙ K(f^*)`: push `Q` past `D(j_{U,!}j_U^*)`, then apply the comparison of
`Lf^*`. -/
def derivedExtensionRestrictionPullbackComparison :
    DerivedCategory.Qh ⋙
        ((jStar U (structureSheafRing Y) ⋙ jShriek U (structureSheafRing Y)).mapDerivedCategory ⋙
          derivedPullback f) ⟶
      (jStar U (structureSheafRing Y) ⋙ jShriek U (structureSheafRing Y)).mapHomotopyCategory
          (ComplexShape.up ℤ) ⋙ pullbackOnHomotopy f :=
  (Functor.associator DerivedCategory.Qh _ (derivedPullback f)).inv ≫
    Functor.whiskerRight
      (jStar U (structureSheafRing Y) ⋙
        jShriek U (structureSheafRing Y)).mapDerivedCategoryFactorsh.hom
      (derivedPullback f) ≫
    (Functor.associator _ DerivedCategory.Qh (derivedPullback f)).hom ≫
    Functor.whiskerLeft _ (derivedPullbackComparison f)

/-- The value of `derivedExtensionRestrictionPullbackComparison` at an object, written as a
composite of two maps: the two associators contribute identities. -/
theorem derivedExtensionRestrictionPullbackComparison_app
    (K : HomotopyCategory (SheafOfModules.{u} (structureSheafRing Y)) (ComplexShape.up ℤ)) :
    (derivedExtensionRestrictionPullbackComparison f U).app K =
      (derivedPullback f).map
          ((jStar U (structureSheafRing Y) ⋙
            jShriek U (structureSheafRing Y)).mapDerivedCategoryFactorsh.hom.app K) ≫
        (derivedPullbackComparison f).app
          (((jStar U (structureSheafRing Y) ⋙ jShriek U (structureSheafRing Y)).mapHomotopyCategory
            (ComplexShape.up ℤ)).obj K) := by
  simp [derivedExtensionRestrictionPullbackComparison]

/-- **`D(j_{U,!}j_U^*) ⋙ Lf^*` is a left derived functor of `K(j_{U,!}j_U^*) ⋙ K(f^*)`.**

This is the step that consumes preservation of K-flatness by `j_{U,!}j_U^*`, in both
hypotheses of the resolving-class criterion: the underived composite inverts a
quasi-isomorphism between K-flat complexes because `j_{U,!}j_U^*` carries it to a
quasi-isomorphism between K-flat complexes, and the comparison is invertible on a K-flat
complex because a K-flat complex computes `Lf^*`. -/
instance isLeftDerivedFunctor_derivedExtensionRestrictionPullback :
    ((jStar U (structureSheafRing Y) ⋙ jShriek U (structureSheafRing Y)).mapDerivedCategory ⋙
        derivedPullback f).IsLeftDerivedFunctor
      (derivedExtensionRestrictionPullbackComparison f U)
      (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing Y))
        (ComplexShape.up ℤ)) := by
  refine LeftDerivedByResolutions.isLeftDerivedFunctor_of_isIso_on_resolutions
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing Y)) (ComplexShape.up ℤ))
    (Stacks.Cohomology.KFlatDerivedPullback.IsKFlat Y)
    (fun N => by
      obtain ⟨K, hK, s, hs⟩ :=
        Stacks.Cohomology.KFlatDerivedPullback.hasResolutions_isKFlat Y N
      exact ⟨K, hK, s, hs⟩)
    _ (fun {K M} s hs hK hM => ?_) DerivedCategory.Qh _
    (derivedExtensionRestrictionPullbackComparison f U) (fun K hK => ?_)
  · exact pullbackInvertsQuasiIso_isKFlat f _
      (quasiIso_mapHomotopyCategory_extensionRestriction U s hs)
      (isKFlat_extensionRestriction U K hK) (isKFlat_extensionRestriction U M hM)
  · rw [derivedExtensionRestrictionPullbackComparison_app]
    have h2 : IsIso ((derivedPullbackComparison f).app
        (((jStar U (structureSheafRing Y) ⋙ jShriek U (structureSheafRing Y)).mapHomotopyCategory
          (ComplexShape.up ℤ)).obj K)) :=
      Stacks.Cohomology.KFlatDerivedPullback.isIso_derivedPullbackComparison_app_of_kFlat f
        (((jStar U (structureSheafRing Y) ⋙ jShriek U (structureSheafRing Y)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj K.as)
        (kFlatComplex_extensionRestriction U K.as hK)
    infer_instance

/-- The canonical comparison exhibiting `Lf^* ⋙ D(j_{U',!}j_{U'}^*)` as a left derived functor
of `K(f^*) ⋙ D(j_{U',!}j_{U'}^*)`: the comparison of `Lf^*`, postcomposed with
`D(j_{U',!}j_{U'}^*)`. -/
def derivedPullbackExtensionRestrictionComparison :
    DerivedCategory.Qh ⋙ (derivedPullback f ⋙
        (jStar ((Opens.map f.hom.base).obj U) (structureSheafRing X) ⋙
          jShriek ((Opens.map f.hom.base).obj U) (structureSheafRing X)).mapDerivedCategory) ⟶
      pullbackOnHomotopy f ⋙
        (jStar ((Opens.map f.hom.base).obj U) (structureSheafRing X) ⋙
          jShriek ((Opens.map f.hom.base).obj U) (structureSheafRing X)).mapDerivedCategory :=
  (Functor.associator DerivedCategory.Qh (derivedPullback f) _).inv ≫
    Functor.whiskerRight (derivedPullbackComparison f) _

/-- **`Lf^* ⋙ D(j_{U',!}j_{U'}^*)` is a left derived functor of
`K(f^*) ⋙ D(j_{U',!}j_{U'}^*)`.**  No new input: a functor derived by resolutions stays a
derived functor after postcomposition with an arbitrary functor, and the K-flat complexes are
a resolving datum for `f^*`. -/
instance isLeftDerivedFunctor_derivedPullbackExtensionRestriction :
    (derivedPullback f ⋙
        (jStar ((Opens.map f.hom.base).obj U) (structureSheafRing X) ⋙
          jShriek ((Opens.map f.hom.base).obj U)
            (structureSheafRing X)).mapDerivedCategory).IsLeftDerivedFunctor
      (derivedPullbackExtensionRestrictionComparison f U)
      (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing Y)) (ComplexShape.up ℤ)) :=
  LeftDerivedByResolutions.isLeftDerivedFunctor_postcomp_of_resolutions
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing Y)) (ComplexShape.up ℤ))
    (Stacks.Cohomology.KFlatDerivedPullback.IsKFlat Y)
    (fun N => by
      obtain ⟨K, hK, s, hs⟩ :=
        Stacks.Cohomology.KFlatDerivedPullback.hasResolutions_isKFlat Y N
      exact ⟨K, hK, s, hs⟩)
    (pullbackOnHomotopy f) (fun s hs hK hM => pullbackInvertsQuasiIso_isKFlat f s hs hK hM)
    DerivedCategory.Qh (derivedPullback f) (derivedPullbackComparison f) _

/-- **Derived base change for extension by zero of a restriction.**  For `f : X ⟶ Y` a
morphism of ringed spaces, `U` an open subspace of `Y` and `U' = f^{-1}U`, there is an
isomorphism of functors `D(𝒪_Y) ⟶ D(𝒪_X)`

`D(j_{U,!}j_U^*) ⋙ Lf^* ≅ Lf^* ⋙ D(j_{U',!}j_{U'}^*)`,

needing no flatness of `f`.  Both sides are left derived functors of the two sides of the
underived base change isomorphism, so the universal property produces the isomorphism. -/
def derivedPullbackExtensionRestrictionIso :
    (jStar U (structureSheafRing Y) ⋙ jShriek U (structureSheafRing Y)).mapDerivedCategory ⋙
        derivedPullback f ≅
      derivedPullback f ⋙
        (jStar ((Opens.map f.hom.base).obj U) (structureSheafRing X) ⋙
          jShriek ((Opens.map f.hom.base).obj U) (structureSheafRing X)).mapDerivedCategory :=
  Functor.leftDerivedNatIso _ _ (derivedExtensionRestrictionPullbackComparison f U)
    (derivedPullbackExtensionRestrictionComparison f U)
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing Y)) (ComplexShape.up ℤ))
    (extensionRestrictionHomotopyPullbackIso f U)

/-- **The derived base change isomorphism is compatible with the two canonical comparisons.**
Whiskering it with the localization `Q` and following with the comparison of
`Lf^* ⋙ D(j_{U',!}j_{U'}^*)` gives the comparison of `D(j_{U,!}j_U^*) ⋙ Lf^*` followed by the
underived base change isomorphism.  This determines the isomorphism uniquely, and is the
derived counterpart of
`Stacks.Cohomology.ExtensionByZeroBaseChange.modulePullbackExtensionRestrictionIso_hom_counit`,
which is what fixes the underived isomorphism appearing on the right. -/
theorem derivedPullbackExtensionRestrictionIso_hom_comparison :
    Functor.whiskerLeft DerivedCategory.Qh
          (derivedPullbackExtensionRestrictionIso f U).hom ≫
        derivedPullbackExtensionRestrictionComparison f U =
      derivedExtensionRestrictionPullbackComparison f U ≫
        (extensionRestrictionHomotopyPullbackIso f U).hom :=
  Functor.leftDerivedNatTrans_fac _ _
    (derivedExtensionRestrictionPullbackComparison f U)
    (derivedPullbackExtensionRestrictionComparison f U)
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing Y)) (ComplexShape.up ℤ))
    (extensionRestrictionHomotopyPullbackIso f U).hom

end Derived

end Stacks.Cohomology.ExtensionByZeroBaseChangeDerived

end
