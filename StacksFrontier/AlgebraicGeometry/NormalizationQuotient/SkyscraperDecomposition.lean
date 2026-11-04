module

public import Mathlib.Algebra.Category.ModuleCat.Stalk
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import Mathlib.CategoryTheory.Preadditive.FunctorCategory
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.Topology.Sheaves.Abelian
public import Mathlib.Topology.Sheaves.Limits
public import StacksFrontier.AlgebraicGeometry.NormalizationQuotient.Skyscraper
public import StacksFrontier.Topology.Sheaves.RingedSpace.ModulePullbackStalkAdjunction

/-!
# A module supported on a closed discrete set is a direct sum of skyscrapers

Let `X` be a scheme, let `Z ⊆ X` be a closed subset carrying the discrete topology and let `M`
be an `𝒪_X`-module whose stalks vanish off `Z`.  Then `M` is the direct sum of the skyscrapers of
its stalks at the points of `Z`.  This is the sheaf-theoretic content of
[Stacks, Tag 0C1R](https://stacks.math.columbia.edu/tag/0C1R)(2), where `Z` is the singular locus
of a reduced one-dimensional Nagata scheme and `M` is the normalization quotient.

The comparison map is built in presheaves of modules, where coproducts and products are both
computed open set by open set: the germ maps `M → sky_z(M_z)` assemble into
`M → ∏_{z ∈ Z} sky_z(M_z)`, and the canonical `∐ → ∏` compares that with the coproduct.  Both
are checked to be isomorphisms one stalk at a time, using that the discreteness of `Z` gives
every point of `X` a neighbourhood meeting `Z` at most once: over such a neighbourhood all but
one of the skyscrapers vanish, so the biproduct comparison is an isomorphism there even though
`Z` may be infinite and the biproduct therefore not finite.  Sheafification preserves coproducts
and stalks, which transports the conclusion to sheaves of modules.

## Main results

* `sheaf_iso_coproduct_skyscraper_of_closed_discrete_support`.

## Implementation notes

The conclusion is `Nonempty (M ≅ ∐ …)` rather than a chosen isomorphism, since the isomorphism
is assembled from a sheafification and is not canonical in any sense the statement could pin.

The germ map into the skyscraper is not built here: it is the stalk/skyscraper adjunction
`RingedSpaceModuleAdjunction.moduleStalkSkyscraperHomEquiv`, applied to the identity map of the
stalk.  That adjunction also supplies the stalkwise inverse, since it sends the germ map back to
the identity, so the fact that the germ map is an isomorphism on the stalk at `x` needs no germ
computation at all.

Two habits keep the remaining goals inside one spelling of each object.  First, no functor is
bound by `let`: `rw` matches syntactically, so a `let`-bound functor hides `Functor.map_comp`
from it.  Second, where a goal mixes an object reached through `X.ringCatSheaf` with the same
object reached through `OXModule.ringSheaf X.toRingedSpace`, `Functor.map_comp` is applied as a
term rather than by `rw`, and the two `IsIso` hypotheses of a composite are fed to
`IsIso.comp_isIso'` rather than left to instance search.  Both of those compare the arguments of
one `Functor.map` application against each other instead of against a pattern, which is what a
unifier respecting transparency can still do: the definitions it would otherwise have to unfold
are the `getColimitCocone` of a stalk, which the module system does not expose, so no
reducibility attribute can reach them.  With the germ map taken from the adjunction and these
two habits, the file needs neither `implicit_reducible` nor
`backward.isDefEq.respectTransparency false`.

## References

* [Stacks Project, Tag 0C1R](https://stacks.math.columbia.edu/tag/0C1R)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open AlgebraicGeometry

universe u

namespace Stacks.AlgebraicGeometry.NormalizationQuotient

variable {X : Scheme.{u}} (M : X.Modules) (x : X)

/-- The canonical morphism of presheaves of modules from `M` to the skyscraper of its stalk at
`x`: the stalk/skyscraper adjunction of `moduleStalkSkyscraperHomEquiv` applied to the identity
map of the stalk, so that over an open set containing `x` it is the germ map. -/
private noncomputable def moduleToSkyscraperPOM :
    M.val ⟶ OXModule.skyscraperPOM x (OXModule.stalk M x) :=
  RingedSpaceModuleAdjunction.moduleSkyscraperMapFromStalk X.toRingedSpace x M.val
    (OXModule.stalk M x) (CategoryStruct.id (OXModule.stalk M x))

/-- The germ map to the skyscraper of the stalk is an isomorphism on the stalk at that point:
the adjunction sends it back to the identity of the stalk, so composing it with the canonical
identification of the skyscraper's stalk is the identity. -/
private theorem stalk_map_moduleToSkyscraperPOM_isIso :
    IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
      ((PresheafOfModules.toPresheaf _).map (moduleToSkyscraperPOM M x))) := by
  have hadj := (RingedSpaceModuleAdjunction.moduleStalkSkyscraperHomEquiv X.toRingedSpace x
    M.val (OXModule.stalk M x)).left_inv (CategoryStruct.id (OXModule.stalk M x))
  have he (a : ↑(TopCat.Presheaf.stalk M.val.presheaf x)) :
      (OXModule.sheafify_skyscraperPOM_stalkIso_skyscraper x (OXModule.stalk M x)).hom
          ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
            ((PresheafOfModules.toPresheaf _).map (moduleToSkyscraperPOM M x)) a) = a :=
    ConcreteCategory.congr_hom hadj a
  have hbij := ConcreteCategory.bijective_of_isIso
    (OXModule.sheafify_skyscraperPOM_stalkIso_skyscraper x (OXModule.stalk M x)).hom
  refine (ConcreteCategory.isIso_iff_bijective _).2 ⟨fun a b h => ?_, fun b => ?_⟩
  · exact (he a).symm.trans ((congrArg
      (OXModule.sheafify_skyscraperPOM_stalkIso_skyscraper x (OXModule.stalk M x)).hom h).trans
      (he b))
  · exact ⟨(OXModule.sheafify_skyscraperPOM_stalkIso_skyscraper x (OXModule.stalk M x)).hom b,
      hbij.injective (he _)⟩

/-- The unit of sheafification from a presheaf of modules is an isomorphism on every stalk. -/
private theorem stalk_map_sheafifyUnitPshMap_isIso (P : PresheafOfModules.{u} X.ringCatSheaf.obj)
    (x : X) : IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
      (OXModule.sheafifyUnitPshMap P)) :=
  (ConcreteCategory.isIso_iff_bijective _).2 (OXModule.sheafifyStalkLinearEquiv x P).bijective

/-- Sheafification sends a map of presheaves of modules that is an isomorphism on every stalk
to an isomorphism. -/
private theorem sheafify_map_isIso_of_stalk_map_isIso
    {P Q : PresheafOfModules.{u} X.ringCatSheaf.obj} (f : P ⟶ Q)
    (h : ∀ x : X, IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
      ((PresheafOfModules.toPresheaf _).map f))) :
    IsIso (OXModule.sheafify.map f) := by
  refine module_isIso_of_stalk_map_isIso _ fun x => ?_
  have _ := stalk_map_sheafifyUnitPshMap_isIso P x
  have hQ := stalk_map_sheafifyUnitPshMap_isIso Q x
  refine IsIso.of_isIso_fac_left
    (f := (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
      (OXModule.sheafifyUnitPshMap P))
    (hh := IsIso.comp_isIso' (h x) hQ) ?_
  have hnat : OXModule.sheafifyUnitPshMap P ≫
        (PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map (OXModule.sheafify.map f).val =
      (PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map f ≫ OXModule.sheafifyUnitPshMap Q :=
    (CategoryTheory.toSheafify_naturality _ _).symm
  refine Eq.trans ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map_comp _ _).symm ?_
  exact Eq.trans (congrArg (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map hnat)
    ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map_comp _ _)

/-- A module on a scheme whose stalks vanish outside a closed discrete subset `Z` is the
coproduct of the skyscrapers of its stalks at the points of `Z`. -/
public theorem sheaf_iso_coproduct_skyscraper_of_closed_discrete_support (Z : Set X)
    (hZ : IsClosed Z) [DiscreteTopology Z]
    (hM : ∀ y ∉ Z, IsZero (OXModule.stalk M y)) :
    Nonempty (M ≅ ∐ fun z : Z => skyscraperModule X z.1 (OXModule.stalk M z.1)) := by
  classical
  let _ : HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u} :=
    hasSheafifyEssentiallySmallSite _ _
  let _ : (Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u} :=
    GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall _
  let _ : HasColimitsOfSize.{u, u} X.Modules := inferInstance
  let S : Z → PresheafOfModules.{u} X.ringCatSheaf.obj :=
    fun z => OXModule.skyscraperPOM z.1 (OXModule.stalk M z.1)
  let f : M.val ⟶ ∏ᶜ S := Pi.lift fun z => moduleToSkyscraperPOM M z.1
  have hz (V : X.Opens) (z : Z) (hzV : z.1 ∉ V) :
      IsZero (((PresheafOfModules.evaluation X.ringCatSheaf.obj (op V)) ⋙
        forget₂ (ModuleCat (X.ringCatSheaf.obj.obj (op V))) AddCommGrpCat).obj (S z)) :=
    Functor.map_isZero (forget₂ (ModuleCat (X.ringCatSheaf.obj.obj (op V))) AddCommGrpCat)
      (skyscraperPOM_obj_isZero_of_not_mem z.1 (OXModule.stalk M z.1) V hzV)
  have hc (y : X) : IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat y).map
      ((PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map (Sigma.desc (Pi.ι S)))) := by
    obtain ⟨U, hyU, hU⟩ := exists_open_meets_closed_discrete_at_most_one Z hZ y
    refine stalk_map_isIso_of_locally_isIso _ y U hyU fun V hVU hyV => ?_
    refine map_coproductToProduct_isIso S (PresheafOfModules.evaluation X.ringCatSheaf.obj
      (op V) ⋙ forget₂ (ModuleCat (X.ringCatSheaf.obj.obj (op V))) AddCommGrpCat)
      fun i j hi hj => ?_
    have hiV : i.1 ∈ V := by_contra fun h => hi (hz V i h)
    have hjV : j.1 ∈ V := by_contra fun h => hj (hz V j h)
    exact Subtype.ext ((hU i.1 i.2 (hVU hiV)).trans (hU j.1 j.2 (hVU hjV)).symm)
  have hf (y : X) : IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat y).map
      ((PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map f)) := by
    obtain ⟨U, hyU, hU⟩ := exists_open_meets_closed_discrete_at_most_one Z hZ y
    by_cases hyZ : y ∈ Z
    · have hp : IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat y).map
          ((PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map (Pi.π S ⟨y, hyZ⟩))) := by
        refine stalk_map_isIso_of_locally_isIso _ y U hyU fun V hVU hyV => ?_
        refine isIso_fan_π_of_isZero _ (isLimitOfPreserves
          (PresheafOfModules.evaluation X.ringCatSheaf.obj (op V) ⋙
            forget₂ (ModuleCat (X.ringCatSheaf.obj.obj (op V))) AddCommGrpCat)
          (limit.isLimit (Discrete.functor S))) ⟨y, hyZ⟩ fun j hj => ?_
        exact hz V j fun hjV => hj (Subtype.ext (hU j.1 j.2 (hVU hjV)))
      have heq : (TopCat.Presheaf.stalkFunctor AddCommGrpCat y).map
            ((PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map f) ≫
          (TopCat.Presheaf.stalkFunctor AddCommGrpCat y).map
            ((PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map (Pi.π S ⟨y, hyZ⟩)) =
          (TopCat.Presheaf.stalkFunctor AddCommGrpCat y).map
            ((PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map
              (moduleToSkyscraperPOM M y)) := by
        rw [← Functor.map_comp, ← Functor.map_comp]
        exact congrArg (fun w => (TopCat.Presheaf.stalkFunctor AddCommGrpCat y).map
          ((PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map w)) (limit.lift_π _ _)
      have _ := hp
      have _ := stalk_map_moduleToSkyscraperPOM_isIso M y
      exact IsIso.of_isIso_fac_right heq
    · have hP : IsZero (TopCat.Presheaf.stalk
          ((PresheafOfModules.toPresheaf X.ringCatSheaf.obj).obj (∏ᶜ S)) y) := by
        refine stalk_isZero_of_locally_isZero _ y U hyU fun V hVU hyV => ?_
        refine IsLimit.isZero_pt (isLimitOfPreserves
          (PresheafOfModules.evaluation X.ringCatSheaf.obj (op V) ⋙
            forget₂ (ModuleCat (X.ringCatSheaf.obj.obj (op V))) AddCommGrpCat)
          (limit.isLimit (Discrete.functor S)))
          ((Functor.isZero_iff _).2 fun ⟨j⟩ => ?_)
        exact hz V j fun hjV => hyZ ((hU j.1 j.2 (hVU hjV)) ▸ j.2)
      have hMy : IsZero (TopCat.Presheaf.stalk M.val.presheaf y) :=
        AddCommGrpCat.isZero_iff_subsingleton.mpr
          (ModuleCat.isZero_iff_subsingleton.mp (hM y hyZ))
      exact hMy.isIso hP _
  let g : M ⟶ OXModule.sheafify.obj (∏ᶜ S) := ⟨f ≫ OXModule.sheafifyUnitHom (∏ᶜ S)⟩
  have hgiso : IsIso g := by
    refine module_isIso_of_stalk_map_isIso _ fun y => ?_
    have hu := stalk_map_sheafifyUnitPshMap_isIso (∏ᶜ S) y
    have hco := (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} y).map_comp
      ((PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map f)
      (OXModule.sheafifyUnitPshMap (∏ᶜ S))
    exact (congrArg IsIso hco).mpr (IsIso.comp_isIso' (hf y) hu)
  have _ : IsIso (OXModule.sheafify.map (Sigma.desc (Pi.ι S))) :=
    sheafify_map_isIso_of_stalk_map_isIso _ hc
  have _ : PreservesColimitsOfSize.{u, u} (OXModule.sheafify (X := X.toRingedSpace)) := by
    dsimp [OXModule.sheafify]
    infer_instance
  have _ : HasCoproduct (fun z : Z =>
      (OXModule.sheafify : PresheafOfModules.{u} X.ringCatSheaf.obj ⥤ X.Modules).obj (S z)) :=
    inferInstanceAs (HasCoproduct (fun z : Z =>
      skyscraperModule X z.1 (OXModule.stalk M z.1)))
  have _ := hgiso
  exact ⟨asIso g ≪≫ (asIso (OXModule.sheafify.map (Sigma.desc (Pi.ι S)))).symm ≪≫
    PreservesCoproduct.iso
      (OXModule.sheafify : PresheafOfModules.{u} X.ringCatSheaf.obj ⥤ X.Modules) S⟩

end Stacks.AlgebraicGeometry.NormalizationQuotient

end
