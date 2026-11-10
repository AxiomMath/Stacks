module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposLowerShriekUnit
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorAnnihilation
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionAnnihilatedModuleSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionModuleEssentialImage
public import StacksFrontier.AlgebraicGeometry.Spaces.ComplexesWithSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackGeometricFibre
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModuleStalkConservative
public import StacksFrontier.AlgebraicGeometry.Spaces.TensorPushforwardStalkCriterion
public import StacksFrontier.AlgebraicGeometry.Spaces.WeaklyAssociatedSupport

/-!
# The unit of `i⁻¹ ⊣ i_*` on sheaves of modules, for a closed immersion

Let `i : Z ⟶ X` be a closed immersion of algebraic spaces over a scheme `S` and let `𝒜` be a
sheaf of commutative rings on the small étale site of `X`. For a sheaf of `𝒜`-modules `N` the
adjunction of Stacks 03D4 between the inverse image of Stacks 03D2 and the direct image of
Stacks 03D3 has a unit `N ⟶ i_*i⁻¹N`, and this file proves that it is an isomorphism as soon as
`N` has exactly one section over every étale chart of `X` whose points avoid the point set of
`Z` — in particular whenever `N` is a tensor product one of whose factors is a direct image
along `i`.

The argument is stalkwise, as in
`StacksFrontier/AlgebraicGeometry/Spaces/ClosedImmersionModuleEssentialImage.lean`, which runs it
for the *structure* sheaf: geometric fibres detect isomorphisms of sheaves of modules over an
arbitrary sheaf of rings (part of Stacks 04K5,
`AlgebraicGeometry.Space.isIso_of_isIso_geometricModuleStalk`), a geometric point of `X` whose
image lies in the point set of `Z` lifts to `Z`
(`AlgebraicGeometry.Space.exists_geometricPoint_map_eq_of_mem_range`), and the two cases are
settled separately: over `Z` the unit is invertible on the fibre because the counit is, and off
`Z` both fibres have one element.

## Main results

* `AlgebraicGeometry.Space.subsingleton_sheafModuleFiber_of_subsingleton_sections`: a sheaf of
  modules with one section over every chart avoiding `Z` has a one-element fibre at every
  geometric point of `X` outside `Z`.
* `AlgebraicGeometry.Space.subsingleton_sections_directImageModules_of_chartPreimage_eq_empty`:
  a direct image along `i` has one section over such a chart.
* `AlgebraicGeometry.Space.isIso_sheafModuleFiber_map_inverseImageUnit`: the unit is invertible
  on the fibre at the image of a geometric point of `Z`.
* `AlgebraicGeometry.Space.isIso_inverseImageAdjDirectImageModules_unit_of_subsingleton_sections`:
  the unit is an isomorphism.
* `Stacks.SheafOfModules.subsingleton_tensorSheafBifunctor_obj_of_subsingleton_sections`: on an
  arbitrary site, a tensor product sheaf one of whose factors has only the zero section below an
  object has only the zero section over that object. This is what supplies the hypothesis of the
  previous statement at the source `𝓕 ⊗_𝒜 f_*𝓖` of the canonical map of Stacks 04G0.
* `AlgebraicGeometry.Space.chartPreimage_eq_empty_of_hom`: a chart below one avoiding `Z` avoids
  `Z` too, which is what makes that hypothesis checkable.

## Implementation notes

The sheaf of rings is arbitrary throughout, which is what Stacks 04G0 needs and what the
structure-sheaf argument of
`AlgebraicGeometry.Space.essImage_modulePushforward_of_annihilatedByKerIdeal` does not provide:
there the hypothesis is annihilation by the ideal `ker(i♯) ⊆ 𝒪_X`, which has no analogue for a
`φ : 𝒜 ⟶ i_{small,*}ℬ` that is not assumed surjective. What replaces it is the weaker and purely
sectionwise hypothesis used here, and it is available for exactly the modules Stacks 04G0 needs
it for: a direct image along `i` has no nonzero section over a chart whose base change along `i`
is empty, because such a chart is covered by the empty sieve.

The passage from "one section over every chart avoiding `Z`" to "one-element fibre off `Z`" goes
through the support of Stacks 04KA: the first hypothesis bounds the support by the point set of
`Z` (`AlgebraicGeometry.Space.supportOfSheaf_subset_range_of_subsingleton_sections`, which is
already stated for an arbitrary abelian sheaf), so the set-valued stalk off `Z` is a
subsingleton, and `AlgebraicGeometry.Space.subsingleton_moduleStalkLarge_of_subsingleton_stalkSet`
together with `Stacks.moduleStalkLargeFiberAddEquiv` carries that to the fibre of
`Stacks.sheafModuleFiber`, the form the conservativity statement consumes. Both of those are
stated for an arbitrary sheaf of commutative rings.

For a tensor product the hypothesis is not checked on sections of the tensor product sheaf
directly — those are sections of a sheafification — but through
`Stacks.SheafOfModules.smul_tensorSheafBifunctor_eq_zero`: the unit section of the structure
sheaf annihilates the direct-image factor over every chart below one avoiding `Z`, hence
annihilates the tensor product there, hence that tensor product has one section there. That step
is stated for an arbitrary site, which is where it is cheap; writing the `Subsingleton` of the
sections of a *concrete* tensor product sheaf on the small étale site makes the elaborator unfold
the sheafification and exhausts it, so the concrete instance is left to the consumer, whose
expected type is already instantiated.

## References

* [Stacks Project, Tag 03D2](https://stacks.math.columbia.edu/tag/03D2)
* [Stacks Project, Tag 03D3](https://stacks.math.columbia.edu/tag/03D3)
* [Stacks Project, Tag 03D4](https://stacks.math.columbia.edu/tag/03D4)
* [Stacks Project, Tag 04E5](https://stacks.math.columbia.edu/tag/04E5)
* [Stacks Project, Tag 04G0](https://stacks.math.columbia.edu/tag/04G0)
* [Stacks Project, Tag 04K2](https://stacks.math.columbia.edu/tag/04K2)
* [Stacks Project, Tag 04K5](https://stacks.math.columbia.edu/tag/04K5)
* [Stacks Project, Tag 04KA](https://stacks.math.columbia.edu/tag/04KA)
* [Stacks Project, Tag 0DK1](https://stacks.math.columbia.edu/tag/0DK1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.SheafOfModules Stacks.Sheaves.RingedToposModules
open Stacks.Sheaves.StalkInverseImage Stacks.Sheaves.ToposPushforward

attribute [local instance] FinallySmall.preservesColimitsOfShape_of_isFiltered

universe v' u' u m

namespace Stacks.SheafOfModules

section AbstractTensor

variable {C : Type u'} [Category.{v'} C] (J : GrothendieckTopology C)
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify J AddCommGrpCat.{u}]
  {Osharp : Sheaf J CommRingCat.{u}}

/-- **A tensor product sheaf one of whose factors has only the zero section below an object has
only the zero section over that object.** If every section of `N` over an object mapping to `U`
is zero then the unit section of the structure sheaf annihilates `N` there, hence by
`Stacks.SheafOfModules.smul_tensorSheafBifunctor_eq_zero` it annihilates `M ⊗ N` over `U`, and a
module on which the unit section acts as zero is a subsingleton.

It is stated for an arbitrary site because that is where it is cheap: the scalar action on the
sections of a direct image of sheaves of modules along the morphism of small étale topoi is
several definitions deep, and writing a `•` at that spelling exhausts the elaborator. Here no
such unfolding is needed, and the small étale instance below is a plain application. -/
theorem subsingleton_tensorSheafBifunctor_obj_of_subsingleton_sections
    (M N : _root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Osharp)) (U : Cᵒᵖ)
    (hN : ∀ V : Cᵒᵖ, (U ⟶ V) → Subsingleton (N.val.obj V)) :
    Subsingleton ((((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor Osharp))).obj
      (M, N)).val.obj U) :=
  subsingleton_obj_of_one_smul_eq_zero _ U fun s ↦
    smul_tensorSheafBifunctor_eq_zero J M N U 1 (fun g _ ↦ (hN _ g).elim _ _) s

end AbstractTensor

end Stacks.SheafOfModules

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {Z X : AlgebraicSpaces B S hS}

/-! ### The fibre off the closed subspace -/

/-- The colimit of a presheaf of sets over the elements of the geometric fibre is the set-valued
stalk at the geometric point, for values in any universe. -/
private def fiberColimitEquivStalkSet.{w} (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (x : GeometricPoint B S hS F) (P : (SmallEtale B S hS F)ᵒᵖ ⥤ Type w) :
    ((Functor.Elements.π (geometricFiber B S hS F x)).op ⋙ P).ColimitType ≃ stalkSet x P where
  toFun := Quot.map
    (fun a => ⟨op ((fiberElementsToNeighborhood B S hS F x).obj a.1.unop), a.2⟩)
    (by
      rintro ⟨j, a⟩ ⟨k, b⟩ ⟨f, h⟩
      exact ⟨((fiberElementsToNeighborhood B S hS F x).map f.unop).op, h⟩)
  invFun := Quot.map
    (fun a => ⟨op ((neighborhoodToFiberElements B S hS F x).obj a.1.unop), a.2⟩)
    (by
      rintro ⟨j, a⟩ ⟨k, b⟩ ⟨f, h⟩
      exact ⟨((neighborhoodToFiberElements B S hS F x).map f.unop).op, h⟩)
  left_inv a := by
    induction a using Quot.inductionOn
    rfl
  right_inv a := by
    induction a using Quot.inductionOn
    rfl

/-- **A sheaf of modules whose underlying set-valued stalk at a geometric point is a subsingleton
has a subsingleton module stalk at the corresponding point of the small étale site.** The sheaf
of commutative rings is arbitrary: the argument compares two colimits of the same sections and
never uses the ring. The private `moduleStalkLarge_subsingleton_of_stalkSet` of
`StacksFrontier/AlgebraicGeometry/Spaces/WeaklyAssociatedSupport.lean` is the case of the
structure sheaf. -/
theorem subsingleton_moduleStalkLarge_of_subsingleton_stalkSet
    (X : AlgebraicSpaces B S hS) (x : GeometricPoint B S hS X.1)
    (O : Sheaf (SmallEtale.topology B S hS X.1) CommRingCat.{u})
    (F : SheafOfModules.{m} (Stacks.commRingSheafToRingSheaf.{u, u + 1, u} O))
    (h : Subsingleton
      (stalkSet x (((SheafOfModules.toSheaf _).obj F).obj ⋙ forget AddCommGrpCat.{m}))) :
    Subsingleton (Stacks.moduleStalkLarge (etaleSitePoint B S hS X.1 x X.2) O F) := by
  classical
  let p := etaleSitePoint B S hS X.1 x X.2
  have hp : p.fiber = geometricFiber B S hS X.1 x := etaleSitePoint_fiber B S hS X.1 x X.2
  let D := FinallySmall.FilteredFinalModel.{u} (p.fiber.Elementsᵒᵖ)
  let J : D ⥤ p.fiber.Elementsᵒᵖ := FinallySmall.fromFilteredFinalModel _
  let P0 := F.val.presheaf
  let P := P0 ⋙ AddCommGrpCat.uliftFunctor.{u} ⋙ forget AddCommGrpCat
  let G := (Functor.Elements.π p.fiber).op ⋙ P0 ⋙ AddCommGrpCat.uliftFunctor.{u}
  let GType := (Functor.Elements.π p.fiber).op ⋙ P
  let _ : HasColimit G := Functor.Final.hasColimit_of_comp J
  let up : stalkSet x (P0 ⋙ forget AddCommGrpCat.{m}) → stalkSet x P :=
    Quot.map (fun a => by
        dsimp [SmallEtaleNeighborhood.sections, AddCommGrpCat.uliftFunctor] at a ⊢
        exact ⟨a.1, ULift.up.{u, m} a.2⟩)
      (by
        rintro ⟨j, a⟩ ⟨k, b⟩ ⟨f, h⟩
        exact ⟨f, congrArg ULift.up h⟩)
  have hup : Function.Surjective up := by
    intro a
    induction a using Quot.inductionOn with
    | h a => exact ⟨Quot.mk _ ⟨a.1, a.2.down⟩, rfl⟩
  have : Subsingleton (stalkSet x (P0 ⋙ forget AddCommGrpCat.{m})) := h
  have hStalk : Subsingleton (stalkSet x P) := hup.subsingleton
  let e : GType.ColimitType ≃ stalkSet x P := by
    change ((Functor.Elements.π p.fiber).op ⋙ P).ColimitType ≃ _
    rw [hp]
    exact fiberColimitEquivStalkSet B S hS X.1 x P
  let cG := colimit.cocone G
  have hι (j : p.fiber.Elementsᵒᵖ) (a : G.obj j) : cG.ι.app j a = 0 := by
    have hq : GType.ιColimitType j a = GType.ιColimitType j (0 : G.obj j) :=
      e.injective (Subsingleton.elim _ _)
    obtain ⟨k, f, g, hfg⟩ :=
      (Functor.ιColimitType_eq_iff_of_isFiltered (F := GType) a (0 : G.obj j)).mp hq
    calc
      cG.ι.app j a = cG.ι.app k (G.map f a) := by simp
      _ = cG.ι.app k (G.map g (0 : G.obj j)) := congrArg _ hfg
      _ = 0 := by simp
  have hId : (𝟙 cG.pt : cG.pt ⟶ cG.pt) = 0 := colimit.hom_ext fun j ↦ by
    ext a
    change cG.ι.app j a = 0
    exact hι j a
  exact ((forget AddCommGrpCat).mapIso
      (Functor.Final.colimitIso J G)).toEquiv.subsingleton_congr.mpr
    (AddCommGrpCat.subsingleton_of_isZero ((IsZero.iff_id_eq_zero cG.pt).mpr hId))

/-- **A sheaf of modules with one section over every chart avoiding `Z` has a one-element fibre
at every geometric point outside `Z`.** The sheaf of commutative rings is arbitrary.

The hypothesis bounds the support of the underlying abelian sheaf by the point set of `Z`
(Stacks 04KA), so the set-valued stalk at a geometric point outside that set is a subsingleton,
and the two comparisons of that stalk with the fibre of `Stacks.sheafModuleFiber` carry the
conclusion over. -/
theorem subsingleton_sheafModuleFiber_of_subsingleton_sections (i : Z ⟶ X)
    (hi : IsClosedImmersion B S hS i.hom)
    (𝒜 : Sheaf (SmallEtale.topology B S hS X.1) CommRingCat.{u})
    (M : SheafOfModules.{u} (Stacks.commRingSheafToRingSheaf.{u, u + 1, u} 𝒜))
    (hM : ∀ W : SmallEtale B S hS X.1, chartPreimage B S hS i W = ∅ →
      Subsingleton (M.val.obj (op W)))
    (x : GeometricPoint B S hS X.1)
    (hx : x.image ∉ Set.range (pointsMap B S hS Z.1 i.hom)) :
    Subsingleton ((Stacks.sheafModuleFiber (etaleSitePoint B S hS X.1 x X.2)
      (Stacks.commRingSheafToRingSheaf.{u, u + 1, u} 𝒜)).obj M) := by
  have hsupp := supportOfSheaf_subset_range_of_subsingleton_sections B S hS i hi
    ((SheafOfModules.toSheaf _).obj M) hM
  have hst : Subsingleton (stalkSet x
      (((SheafOfModules.toSheaf _).obj M).obj ⋙ forget AddCommGrpCat.{u})) := by
    by_contra hns
    exact hx (hsupp ⟨x, rfl, hns⟩)
  have := subsingleton_moduleStalkLarge_of_subsingleton_stalkSet B S hS X x 𝒜 M hst
  exact ⟨fun _ _ ↦ (Stacks.moduleStalkLargeFiberAddEquiv (etaleSitePoint B S hS X.1 x X.2)
    𝒜 M).symm.injective (Subsingleton.elim _ _)⟩

/-- **A direct image along a closed immersion has one section over a chart whose points avoid the
point set of the closed subspace.** Its sections there are the sections of the original module
over the base-changed chart, which is covered by the empty sieve. -/
theorem subsingleton_sections_directImageModules_of_chartPreimage_eq_empty (i : Z ⟶ X)
    (hi : yoneda.relativelyRepresentable i.hom)
    (𝒜 : Sheaf (SmallEtale.topology B S hS X.1) RingCat.{u})
    (P : SheafOfModules.{u} (inverseImageRingSheaf (smallToposMorphismTypeU B S hS i) 𝒜))
    (W : SmallEtale B S hS X.1) (hW : chartPreimage B S hS i W = ∅) :
    Subsingleton
      (((directImageModules (smallToposMorphismTypeU B S hS i) 𝒜).obj P).val.obj (op W)) :=
  subsingleton_smallEtaleDirectImage_sections_of_isEmpty B S hS i hi
    ((Sheaf.moduleSheafFunctor
      (inverseImageRingSheaf (smallToposMorphismTypeU B S hS i) 𝒜)).obj P) W
    (isEmpty_smallBaseChange_of_disjoint_range B S hS i hi W hW)

/-! ### The fibre over the closed subspace -/

/-- **The unit of the adjunction of Stacks 03D4 is invertible on the fibre at the image of a
geometric point of the closed subspace.** No hypothesis on the module enters.

Part (4) of Stacks 04K2 for sheaves of modules
(`Stacks.Sheaves.StalkInverseImage.stalkNatIso`, at the datum
`AlgebraicGeometry.Space.smallEtaleInverseImageFiberIso`) identifies the fibre at the image point
with the fibre of the inverse image at the point itself; its naturality turns the fibre of the
unit into the fibre of `i⁻¹(η)`, which the triangle identity makes a section of the fibre of the
counit, and the counit is invertible for a closed immersion. -/
theorem isIso_sheafModuleFiber_map_inverseImageUnit (i : Z ⟶ X)
    (hi : IsClosedImmersion B S hS i.hom)
    (𝒜 : Sheaf (SmallEtale.topology B S hS X.1) RingCat.{u})
    (N : SheafOfModules.{u} 𝒜) (z : GeometricPoint B S hS Z.1) :
    IsIso ((Stacks.sheafModuleFiber
        (etaleSitePoint B S hS X.1 (geometricPointMap i.hom z) X.2) 𝒜).map
      ((inverseImageAdjDirectImageModules (smallToposMorphismTypeU B S hS i) 𝒜).unit.app N)) := by
  have hff := fullyFaithfulSmallEtalePushforwardOfIsClosedImmersion B S hS i hi
  have := hff.full
  have := hff.faithful
  have hcounit := isIso_inverseImageAdjDirectImageModules_counit
    (smallToposMorphismTypeU B S hS i) 𝒜
  have h1 : IsIso ((inverseImageModules (smallToposMorphismTypeU B S hS i) 𝒜).map
      ((inverseImageAdjDirectImageModules (smallToposMorphismTypeU B S hS i) 𝒜).unit.app N)) :=
    Stacks.isIso_leftAdjoint_map_unit_app _ N (NatIso.isIso_app_of_isIso _ _)
  exact Stacks.isIso_map_of_natIso_of_isIso
    (stalkNatIso (smallToposMorphismTypeU B S hS i) 𝒜 (etaleSitePoint B S hS Z.1 z Z.2)
      (etaleSitePoint B S hS X.1 (geometricPointMap i.hom z) X.2)
      (smallEtaleInverseImageFiberIso B S hS i z)).symm _
    (Stacks.isIso_functor_map
      (Stacks.sheafModuleFiber (etaleSitePoint B S hS Z.1 z Z.2)
            (inverseImageRingSheaf (smallToposMorphismTypeU B S hS i) 𝒜) ⋙
          ModuleCat.restrictScalars
            (stalkRingEquiv (smallToposMorphismTypeU B S hS i) 𝒜
              (etaleSitePoint B S hS Z.1 z Z.2)
              (etaleSitePoint B S hS X.1 (geometricPointMap i.hom z) X.2)
              (smallEtaleInverseImageFiberIso B S hS i z)).toRingHom) _ h1)

/-! ### The unit -/

/-- **The unit of the adjunction of Stacks 03D4 is an isomorphism at a sheaf of modules with one
section over every chart avoiding the closed subspace.** The sheaf of commutative rings is
arbitrary.

Geometric fibres detect isomorphisms; over the closed subspace the previous statement applies, and
outside it both the module and its round trip through the direct image have one-element fibres —
the module by hypothesis and the round trip because a direct image has one section over such a
chart. -/
theorem isIso_inverseImageAdjDirectImageModules_unit_of_subsingleton_sections (i : Z ⟶ X)
    (hi : IsClosedImmersion B S hS i.hom)
    (𝒜 : Sheaf (SmallEtale.topology B S hS X.1) CommRingCat.{u})
    (N : SheafOfModules.{u} (Stacks.commRingSheafToRingSheaf.{u, u + 1, u} 𝒜))
    (hN : ∀ W : SmallEtale B S hS X.1, chartPreimage B S hS i W = ∅ →
      Subsingleton (N.val.obj (op W))) :
    IsIso ((inverseImageAdjDirectImageModules (smallToposMorphismTypeU B S hS i)
      (Stacks.commRingSheafToRingSheaf.{u, u + 1, u} 𝒜)).unit.app N) := by
  refine isIso_of_isIso_geometricModuleStalk B S hS X.1 X.2
    (Stacks.commRingSheafToRingSheaf.{u, u + 1, u} 𝒜) _ fun x ↦ ?_
  by_cases hx : x.image ∈ Set.range (pointsMap B S hS Z.1 i.hom)
  · obtain ⟨z, rfl⟩ := exists_geometricPoint_map_eq_of_mem_range B S hS i hi x hx
    exact isIso_sheafModuleFiber_map_inverseImageUnit B S hS i hi _ N z
  · exact Stacks.isIso_of_subsingleton
      (subsingleton_sheafModuleFiber_of_subsingleton_sections B S hS i hi 𝒜 N hN x hx)
      (subsingleton_sheafModuleFiber_of_subsingleton_sections B S hS i hi 𝒜 _
        (fun W hW ↦ subsingleton_sections_directImageModules_of_chartPreimage_eq_empty
          B S hS i hi.rep _ _ W hW) x hx) _

/-! ### The tensor product with a direct image -/

/-- **A chart below one whose points avoid the point set of the closed subspace avoids it too.**
This is `AlgebraicGeometry.Space.chartPreimage_subset_preimage` read for an empty target. -/
theorem chartPreimage_eq_empty_of_hom (i : Z ⟶ X) {V W : SmallEtale B S hS X.1} (g : V ⟶ W)
    (hW : chartPreimage B S hS i W = ∅) : chartPreimage B S hS i V = ∅ :=
  Set.eq_empty_iff_forall_notMem.2 fun _ ht ↦
    Set.eq_empty_iff_forall_notMem.1 hW _ (chartPreimage_subset_preimage B S hS i g ht)

end AlgebraicGeometry.Space

end
