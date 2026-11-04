module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.NaiveCotangentBaseChangePresentationComparison
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.MapDifferenceDiagonalSheaf
public import StacksFrontier.CategoryTheory.Adjunction.Mates
public import StacksFrontier.Cotangent.SheavesOfRings.NaiveComparisonArrow

/-!
# `H^{-1}` of the base change map of `NL` and the map of conormal sheaves

Let `i : X ⟶ P`, `i' : X' ⟶ P'` be immersions, `h : P ⟶ Y`, `h' : P' ⟶ Y'` formally smooth, and
`i' ≫ p = g' ≫ i`, `p ≫ h = h' ≫ g` commutative squares.  By [Stacks Project, Tag 0FV4]
`H^{-1}((g')^*NL_{X/Y})` and `H^{-1}(NL_{X'/Y'})` are the kernels of the pulled-back first arrow
`(g')^*𝒞_{X/P} ⟶ (g')^*i^*Ω_{P/Y}` and of the first arrow `𝒞_{X'/P'} ⟶ i'^*Ω_{P'/Y'}` of the
conormal sequences of [Stacks Project, Tag 01UZ].  This file proves that through these
identifications the map induced on `H^{-1}` by the base change map `(g')^*NL_{X/Y} ⟶ NL_{X'/Y'}`
of [Stacks Project, Tag 0FV5] is the restriction of the map `(g')^*𝒞_{X/P} ⟶ 𝒞_{X'/P'}` of
[Stacks Project, Tag 01R4] (`homologyMap_negOne_baseChangeMapOfComparison`), and deduces that the
kernel of `H^{-1}` of the base change map is the kernel of that restriction
(`kernelHomologyMapNegOneBaseChangeIso`).  This is the first step of the proof of
[Stacks Project, Tag 0FV9].

Both identifications are zig-zags through the naive cotangent complexes of the polynomial
presentations of `𝒪_X` and `𝒪_{X'}` on the sections of `i⁻¹𝒪_P` and `i'⁻¹𝒪_{P'}`, compared in
degree `-1` by `Stacks.NaiveCotangentPulledImmersion.pulledPresentationNegOne`, which computes
the base change map (`pulledPresentationNegOne_comp_presentationToNaiveCotangent`).  What is
left is the identity `pulledPresentationNegOne_comp_conormal`: read on the conormal sheaves of
the immersions, the comparison of the presentations is the map of [Stacks Project, Tag 01R4].
It is proved in two halves.

* `pulledPresentationNegOne_comp_towerConormalMap`: on the conormal sheaves of the presentations
  `i⁻¹𝒪_P ⟶ 𝒪_X` and `i'⁻¹𝒪_{P'} ⟶ 𝒪_{X'}`, the comparison is the map induced by the comparison
  of the middle rings `g'⁻¹i⁻¹𝒪_P ⟶ i'⁻¹𝒪_{P'}`.  On classes of polynomial relations this is the
  ring identity `presentationRingComparison_comp_canonicalPresentation`, whose coefficient part
  is the compatibility `inverseImageFirstRingMap_comp_middleRingComparison` of the
  comparisons of the base rings and of the middle rings; it needs `p ≫ h = h' ≫ g`.
* `immersionConormalSheafMap_comp_conormalComparison`: under the comparison
  `𝒞_{X/P} ≅ I/I²` of [Stacks Project, Tag 0FV2], degree `-1`, the map induced by the middle
  rings is the map of [Stacks Project, Tag 01R4].  Both carry the class of a function `r`
  vanishing on `X` to the class of `p^♯ r`.

The ring identities are checked on sections in the image of the units of the inverse-image
adjunctions, which determine maps out of inverse images
(`Stacks.SheafifyStalk.pullback_hom_ext_unitApp`); on these
the canonical comparisons of iterated inverse images are restrictions
(`Stacks.SheafifyStalk.pullbackSquareComparison_unitApp`,
`Stacks.SheafOfModules.inverseImageCompIso_inv_unitApp`).

## Main definitions

* `Stacks.NaiveCotangentPulledImmersion.towerConormalMap`: the comparison of the polynomial
  presentation with the presentation `i⁻¹𝒪_P ⟶ 𝒪_X`, in degree `-1`.
* `Stacks.NaiveCotangentPulledImmersion.pulledMiddleConormalMap`: the map of conormal sheaves
  induced by the comparison of the middle rings.
* `Stacks.NaiveCotangentPulledImmersion.kernelHomologyMapNegOneBaseChangeIso`: the kernel of
  `H^{-1}` of the base change map is the kernel of the restricted map of conormal sheaves.

## Main results

* `Stacks.NaiveCotangentPulledImmersion.twoStepPullbackAdjunction_unit_val_app`: the unit of
  `RingedSpaceModuleAdjunction.twoStepPullbackAdjunction` on sections.
* `Stacks.NaiveCotangentPulledImmersion.inverseImageFirstRingMap_comp_middleRingComparison`:
  the comparisons of the base and middle rings of the two towers are compatible.
* `Stacks.Conormal.Sites.conormalComparison_conormalClass`: the comparison `𝒞_{X/P} ⟶ I/I²` on
  the class of a vanishing function.
* `Stacks.NaiveCotangentPulledImmersion.pulledPresentationNegOne_comp_conormal`: the comparison of
  the pulled-back presentations, read on the conormal sheaves of the immersions.
* `Stacks.NaiveCotangentPulledImmersion.homologyMap_negOne_baseChangeMapOfComparison`: `H^{-1}` of
  the base change map is the restriction of the map of conormal sheaves.

## Implementation notes

The square `p ≫ h = h' ≫ g` is a hypothesis of `pulledPresentationNegOne_comp_conormal` and is
needed: the coefficients of the polynomial presentations are compared through `g`, the variables
through `p`, and without it the class of `r - [h^♯ r]` would be sent to the class of
`h'^♯ g^♯ r - p^♯ h^♯ r`, which need not vanish.  In the base change of a factorization it is the
commutativity of the pullback square.

The unit of `RingedSpaceModuleAdjunction.twoStepPullbackAdjunction` is behind a transport along
`RingedSpaceModuleAdjunction.modulePushforward_eq`; its values are read off those of
`twoStepCompAdjunction` through a heterogeneous equality, the sections of the two direct images
being the same type.  As in the neighbouring files, the categorical bookkeeping across the two
spellings of the category of sheaves of modules is done in bare categories
(`comp_conormal_eq_of_parts`, `comp_comp_eq_of_degreewise`, `kernelIsoOfConjComp`) and applied
with `exact`.

## References

* [Stacks Project, Tag 0FV9](https://stacks.math.columbia.edu/tag/0FV9)
* [Stacks Project, Tag 0FV4](https://stacks.math.columbia.edu/tag/0FV4)
* [Stacks Project, Tag 0FV5](https://stacks.math.columbia.edu/tag/0FV5)
* [Stacks Project, Tag 0FV2](https://stacks.math.columbia.edu/tag/0FV2)
* [Stacks Project, Tag 01R4](https://stacks.math.columbia.edu/tag/01R4)
* [Stacks Project, Tag 01UZ](https://stacks.math.columbia.edu/tag/01UZ)
-/

@[expose] public section

universe u

noncomputable section

section TwoStepUnit

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits RingedSpaceModuleAdjunction
open TopologicalSpace Opposite Stacks.SheafOfModules Stacks.Sites.FreeAlgebra Stacks.Sites.Conormal
open AlgebraicGeometry.SheafOfModules (underlyingRingHomOfSite inverseImageRingHom)
open Stacks.NaiveCotangentSixTermSequence (ringedSpaceHom)
open Stacks.Sheaves.RingedSpaceDifferentials (inverseImageSheaf inverseImageStructureMap)

namespace Stacks.NaiveCotangentPulledImmersion

/-- The unit of an adjunction transported along an equality of right adjoints has, on sections,
the values of the unit it was transported from. -/
theorem unit_val_app_eqMpr_heq {T T' : TopCat.{u}}
    {B : CategoryTheory.Sheaf (Opens.grothendieckTopology T) RingCat.{u}}
    {B' : CategoryTheory.Sheaf (Opens.grothendieckTopology T') RingCat.{u}}
    {F : _root_.SheafOfModules.{u} B ⥤ _root_.SheafOfModules.{u} B'}
    {G G' : _root_.SheafOfModules.{u} B' ⥤ _root_.SheafOfModules.{u} B}
    (h : G = G') (adj : F ⊣ G') (e : (F ⊣ G) = (F ⊣ G')) (M : _root_.SheafOfModules.{u} B)
    (U : (Opens T)ᵒᵖ) (x : M.val.obj U) :
    HEq (((Eq.mpr e adj).unit.app M).val.app U x) ((adj.unit.app M).val.app U x) := by
  subst h
  rfl

variable {X X' : RingedSpace.{u, u}} (g' : X' ⟶ X)

/-- `RingedSpaceModuleAdjunction.twoStepPullbackAdjunction` is `twoStepCompAdjunction`
transported along `RingedSpaceModuleAdjunction.modulePushforward_eq`. -/
theorem twoStepPullbackAdjunction_eq :
    twoStepPullbackAdjunction g' =
      Eq.mpr (congrArg (fun K => twoStepPullback g' ⊣ K) (modulePushforward_eq g'))
        (twoStepCompAdjunction g') := rfl

/-- **The unit of `twoStepPullbackAdjunction` on sections** is the unit of
`twoStepCompAdjunction`, whose values are explicit. -/
theorem twoStepPullbackAdjunction_unit_val_app
    (M : _root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (J := Opens.grothendieckTopology X.carrier) X.sheaf)) (U : (Opens X.carrier)ᵒᵖ)
    (x : M.val.obj U) :
    ((twoStepPullbackAdjunction g').unit.app M).val.app U x =
      ((twoStepCompAdjunction g').unit.app M).val.app U x :=
  eq_of_heq (unit_val_app_eqMpr_heq (modulePushforward_eq g') (twoStepCompAdjunction g')
    (congrArg (fun K => twoStepPullback g' ⊣ K) (modulePushforward_eq g')) M U x)

/-- The transpose along `twoStepPullbackAdjunction` of a map out of the two-step pullback, on
sections: it is the map applied to the image under the unit of `twoStepCompAdjunction`. -/
theorem twoStepPullbackAdjunction_homEquiv_val_app
    (M : _root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (J := Opens.grothendieckTopology X.carrier) X.sheaf))
    (N : _root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (J := Opens.grothendieckTopology X'.carrier) X'.sheaf))
    (z : (twoStepPullback g').obj M ⟶ N) (U : (Opens X.carrier)ᵒᵖ) (x : M.val.obj U) :
    ((twoStepPullbackAdjunction g').homEquiv M N z).val.app U x =
      z.val.app ((Opens.map g'.hom.base).op.obj U)
        (((twoStepCompAdjunction g').unit.app M).val.app U x) :=
  (congrArg (fun t => t.val.app U x) ((twoStepPullbackAdjunction g').homEquiv_unit M N z)).trans
    (congrArg (z.val.app ((Opens.map g'.hom.base).op.obj U)).hom
      (twoStepPullbackAdjunction_unit_val_app g' M U x))

end Stacks.NaiveCotangentPulledImmersion

end TwoStepUnit

section UnitSections

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open TopologicalSpace Opposite
open Stacks.SheafOfModules (ringedSpaceStructureMap inverseImageBaseRing inverseImageMiddleRing
  inverseImageFirstRingMap)
open Stacks.Sheaves.RingedSpaceDifferentials (inverseImageSheaf structureSheafMap sheafAdjunction
  homEquiv_inverseImageStructureMap)

namespace Stacks.SheafifyStalk

/-- The unit of `f⁻¹ ⊣ f_*` on a section. -/
abbrev unitApp {X Y : TopCat.{u}} (f : X ⟶ Y) (F : TopCat.Sheaf CommRingCat.{u} Y)
    (W : Opens Y) (y : ToType (F.obj.obj (op W))) :
    ToType (((TopCat.Sheaf.pullback CommRingCat.{u} f).obj F).obj.obj
      (op ((Opens.map f).obj W))) :=
  ((((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} f).unit.app F).hom.app
    (op W)).hom y)

/-- Morphisms out of an inverse image are determined by their values on unit sections. -/
theorem pullback_hom_ext_unitApp {X Y : TopCat.{u}} (f : X ⟶ Y)
    {F : TopCat.Sheaf CommRingCat.{u} Y} {N : TopCat.Sheaf CommRingCat.{u} X}
    {φ ψ : (TopCat.Sheaf.pullback CommRingCat.{u} f).obj F ⟶ N}
    (H : ∀ (W : Opens Y) (y : ToType (F.obj.obj (op W))),
      (φ.hom.app (op ((Opens.map f).obj W))).hom (unitApp f F W y) =
        (ψ.hom.app (op ((Opens.map f).obj W))).hom (unitApp f F W y)) :
    φ = ψ := by
  apply ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} f).homEquiv F N).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  refine Sheaf.hom_ext (NatTrans.ext (funext fun W => ?_))
  refine CommRingCat.hom_ext (RingHom.ext fun y => ?_)
  exact H W.unop y

/-- The inverse image of a morphism of sheaves on unit sections. -/
theorem pullback_map_unitApp {X Y : TopCat.{u}} (f : X ⟶ Y) {F G : TopCat.Sheaf CommRingCat.{u} Y}
    (ψ : F ⟶ G) (W : Opens Y) (y : ToType (F.obj.obj (op W))) :
    ((((TopCat.Sheaf.pullback CommRingCat.{u} f).map ψ).hom.app (op ((Opens.map f).obj W))).hom
        (unitApp f F W y)) = unitApp f G W ((ψ.hom.app (op W)).hom y) :=
  (congrArg (fun φ : F ⟶ (TopCat.Sheaf.pushforward CommRingCat.{u} f).obj
      ((TopCat.Sheaf.pullback CommRingCat.{u} f).obj G) => (φ.hom.app (op W)).hom y)
    ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} f).unit.naturality ψ)).symm

/-- Morphisms out of a triple inverse image are determined by their values on triply unit
sections. -/
theorem pullback_pullback_pullback_hom_ext_unitApp {X' X P Y : TopCat.{u}} (a : X' ⟶ X)
    (b : X ⟶ P) (c : P ⟶ Y) {F : TopCat.Sheaf CommRingCat.{u} Y}
    {N : TopCat.Sheaf CommRingCat.{u} X'}
    {φ ψ : (TopCat.Sheaf.pullback CommRingCat.{u} a).obj ((TopCat.Sheaf.pullback CommRingCat.{u}
      b).obj ((TopCat.Sheaf.pullback CommRingCat.{u} c).obj F)) ⟶ N}
    (H : ∀ (W : Opens Y) (y : ToType (F.obj.obj (op W))),
      (φ.hom.app (op ((Opens.map a).obj ((Opens.map b).obj ((Opens.map c).obj W))))).hom
          (unitApp a _ _ (unitApp b _ _ (unitApp c F W y))) =
        (ψ.hom.app (op ((Opens.map a).obj ((Opens.map b).obj ((Opens.map c).obj W))))).hom
          (unitApp a _ _ (unitApp b _ _ (unitApp c F W y)))) :
    φ = ψ := by
  apply ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} a).homEquiv _ N).injective
  apply ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} b).homEquiv _ _).injective
  refine pullback_hom_ext_unitApp c (fun W y => ?_)
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, Adjunction.homEquiv_unit,
    Adjunction.homEquiv_unit]
  exact H W y

/-- A transport of a direct image along an equality of continuous maps acts on sections as the
restriction along the corresponding equality of preimages. -/
theorem eqToHom_pushforward_app {X' Y : TopCat.{u}} {m m' : X' ⟶ Y} (e : m = m')
    (N : TopCat.Sheaf CommRingCat.{u} X') (W : Opens Y)
    (x : ToType (N.obj.obj (op ((Opens.map m').obj W)))) :
    ((eqToHom (congrArg (fun k : X' ⟶ Y => (TopCat.Sheaf.pushforward CommRingCat.{u} k).obj N)
        e).symm).hom.app (op W)).hom x =
      (N.obj.map (eqToHom (congrArg (fun k : X' ⟶ Y => op ((Opens.map k).obj W)) e).symm)).hom
        x := by
  subst e
  simp only [eqToHom_refl, CategoryTheory.Functor.map_id]
  rfl

/-- **The canonical comparison of a commutative square on doubly unit sections**: it is the
restriction along the equality of the two preimages. -/
theorem pullbackSquareComparison_unitApp {X' X Y' Y : TopCat.{u}} (p : X' ⟶ X) (q : X ⟶ Y)
    (r : X' ⟶ Y') (s : Y' ⟶ Y) (w : p ≫ q = r ≫ s) (F : TopCat.Sheaf CommRingCat.{u} Y)
    (W : Opens Y) (y : ToType (F.obj.obj (op W))) :
    ((pullbackSquareComparison CommRingCat.{u} p q r s w F).hom.app
        (op ((Opens.map p).obj ((Opens.map q).obj W)))).hom
        (unitApp p _ _ (unitApp q F W y)) =
      (((TopCat.Sheaf.pullback CommRingCat.{u} r).obj
          ((TopCat.Sheaf.pullback CommRingCat.{u} s).obj F)).obj.map
          (eqToHom (congrArg (fun k : X' ⟶ Y => op ((Opens.map k).obj W)) w).symm)).hom
        (unitApp r _ _ (unitApp s F W y)) := by
  have h := congrArg (fun φ : F ⟶ (TopCat.Sheaf.pushforward CommRingCat.{u} q).obj
      ((TopCat.Sheaf.pushforward CommRingCat.{u} p).obj
        ((TopCat.Sheaf.pullback CommRingCat.{u} r).obj
          ((TopCat.Sheaf.pullback CommRingCat.{u} s).obj F))) => (φ.hom.app (op W)).hom y)
    (homEquiv_pullbackSquareComparison CommRingCat.{u} p q r s w F)
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit] at h
  exact h.trans (eqToHom_pushforward_app w _ W _)

end Stacks.SheafifyStalk

namespace Stacks.NaiveCotangentFlatBaseChange

open Stacks.SheafifyStalk (unitApp)

variable {X' X S' S : RingedSpace.{u, u}} (g' : X' ⟶ X) (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S)
  (w : g' ≫ f = f' ≫ g)

/-- The structure map of a morphism of ringed spaces on a unit section is the map on
sections. -/
theorem ringedSpaceStructureMap_unitApp (h : S' ⟶ S) (W : Opens S.carrier)
    (y : ToType (S.sheaf.obj.obj (op W))) :
    ((ringedSpaceStructureMap h).hom.app (op ((Opens.map h.hom.base).obj W))).hom
        (unitApp h.hom.base S.sheaf W y) = (h.hom.c.app (op W)).hom y :=
  congrArg (fun φ : S.sheaf ⟶ (TopCat.Sheaf.pushforward CommRingCat.{u} h.hom.base).obj S'.sheaf =>
    (φ.hom.app (op W)).hom y) (Stacks.SheafOfModules.unit_comp_map_ringedSpaceStructureMap h)

/-- **The canonical base-ring comparison on doubly unit sections**: it carries the image of a
section `y` of `𝒪_S` in `g'⁻¹f⁻¹𝒪_S` to the image of `g^♯ y` in `f'⁻¹𝒪_{S'}`, restricted along
the equality of the two preimages. -/
theorem baseRingComparisonRingedSpace_unitApp (W : Opens S.carrier)
    (y : ToType (S.sheaf.obj.obj (op W))) :
    ((baseRingComparisonRingedSpace g' f f' g w).hom.app
        (op ((Opens.map g'.hom.base).obj ((Opens.map f.hom.base).obj W)))).hom
        (unitApp g'.hom.base _ _ (unitApp f.hom.base S.sheaf W y)) =
      ((inverseImageSheaf f').obj.map (eqToHom (congrArg (fun k : X'.carrier ⟶ S.carrier =>
          op ((Opens.map k).obj W)) (congrArg (fun t : X' ⟶ S => t.hom.base) w)).symm)).hom
        (unitApp f'.hom.base S'.sheaf ((Opens.map g.hom.base).obj W)
          ((g.hom.c.app (op W)).hom y)) := by
  have h1 := Stacks.SheafifyStalk.pullbackSquareComparison_unitApp g'.hom.base f.hom.base
    f'.hom.base g.hom.base (congrArg (fun t : X' ⟶ S => t.hom.base) w) S.sheaf W y
  refine (congrArg (((inverseImageFirstRingMap f' g).hom.app _).hom) h1).trans ?_
  refine (NatTrans.naturality_apply (inverseImageFirstRingMap f' g).hom _ _).trans ?_
  refine congrArg (((inverseImageSheaf f').obj.map _).hom) ?_
  refine (Stacks.SheafifyStalk.pullback_map_unitApp f'.hom.base (ringedSpaceStructureMap g)
    ((Opens.map g.hom.base).obj W) _).trans ?_
  exact congrArg (unitApp f'.hom.base S'.sheaf ((Opens.map g.hom.base).obj W))
    (ringedSpaceStructureMap_unitApp g W y)

end Stacks.NaiveCotangentFlatBaseChange

namespace Stacks.SheafOfModules

open Stacks.SheafifyStalk (unitApp)

variable {X Y Z : RingedSpace.{u, u}} (f : X ⟶ Y) (g : Y ⟶ Z)

/-- The comparison `(g ∘ f)⁻¹𝒪_Z ⟶ f⁻¹g⁻¹𝒪_Z`, inverted, on doubly unit sections. -/
theorem inverseImageCompIso_inv_unitApp (W : Opens Z.carrier)
    (y : ToType (Z.sheaf.obj.obj (op W))) :
    ((inverseImageCompIso f g).inv.hom.app
        (op ((Opens.map f.hom.base).obj ((Opens.map g.hom.base).obj W)))).hom
        (unitApp f.hom.base _ _ (unitApp g.hom.base Z.sheaf W y)) =
      unitApp (f ≫ g).hom.base Z.sheaf W y := by
  have h := congrArg (fun φ : Z.sheaf ⟶ (TopCat.Sheaf.pushforward CommRingCat.{u}
      (f ≫ g).hom.base).obj (inverseImageSheaf (f ≫ g)) => (φ.hom.app (op W)).hom y)
    (Adjunction.unit_leftAdjointUniq_hom_app
      ((Stacks.Sheaves.RingedSpaceDifferentials.sheafAdjunction g).comp
        (Stacks.Sheaves.RingedSpaceDifferentials.sheafAdjunction f))
      (Stacks.Sheaves.RingedSpaceDifferentials.sheafAdjunction (f ≫ g)) Z.sheaf)
  rw [Adjunction.comp_unit_app] at h
  exact h

/-- The comparison `(g ∘ f)⁻¹𝒪_Z ⟶ f⁻¹g⁻¹𝒪_Z` on unit sections. -/
theorem inverseImageCompIso_hom_unitApp (W : Opens Z.carrier)
    (y : ToType (Z.sheaf.obj.obj (op W))) :
    ((inverseImageCompIso f g).hom.hom.app (op ((Opens.map (f ≫ g).hom.base).obj W))).hom
        (unitApp (f ≫ g).hom.base Z.sheaf W y) =
      unitApp f.hom.base _ _ (unitApp g.hom.base Z.sheaf W y) := by
  refine (congrArg (((inverseImageCompIso f g).hom.hom.app _).hom)
    (inverseImageCompIso_inv_unitApp f g W y)).symm.trans ?_
  exact congrArg (fun φ : inverseImageBaseRing f g ⟶ inverseImageBaseRing f g =>
    (φ.hom.app (op ((Opens.map f.hom.base).obj ((Opens.map g.hom.base).obj W)))).hom
      (unitApp f.hom.base _ _ (unitApp g.hom.base Z.sheaf W y)))
    (inverseImageCompIso f g).inv_hom_id

end Stacks.SheafOfModules

end UnitSections

section SitesComparison

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits RingedSpaceModuleAdjunction
open TopologicalSpace Opposite

namespace Stacks.Conormal.Sites

variable {Z X : Scheme.{u}} (i : Z ⟶ X)

/-- The image in `(i⁻¹𝒪_X)(V)` of a section `r` of `𝒪_X` over `U ⊇ i(V)`. -/
abbrev unitSection (U : X.Opens) {V : Z.Opens} (hV : V ≤ i ⁻¹ᵁ U) (r : Γ(X, U)) :
    ToType ((invSheaf i).obj.obj (op V)) :=
  ((invSheaf i).obj.map (homOfLE hV).op).hom
    ((((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} i.base).unit.app
      X.sheaf).hom.app (op U)).hom r)

/-- The structural homomorphism `i⁻¹𝒪_X ⟶ 𝒪_Z` on the image of a section `r` of `𝒪_X` is the
restriction of `i^♯ r`. -/
theorem structHom_unitSection (U : X.Opens) {V : Z.Opens} (hV : V ≤ i ⁻¹ᵁ U) (r : Γ(X, U)) :
    ((structHom i).hom.app (op V)).hom (unitSection i U hV r) =
      (Z.presheaf.map (homOfLE hV).op).hom ((i.app U).hom r) := by
  refine (NatTrans.naturality_apply (structHom i).hom (homOfLE hV).op _).trans ?_
  exact congrArg (Z.presheaf.map (homOfLE hV).op).hom
    (congrArg (fun φ => φ.hom r)
      (Stacks.AlgebraPullbackQcoh.germ_comp_inverseImageStructureMap i U))

/-- The image of a section killed by `i` lies in the kernel ideal of the structural
homomorphism. -/
theorem unitSection_mem (U : X.Opens) {V : Z.Opens} (hV : V ≤ i ⁻¹ᵁ U) (r : Γ(X, U))
    (hr : (i.app U).hom r = 0) :
    unitSection i U hV r ∈ Stacks.Sites.Conormal.kernelIdeal (structHom i).hom (op V) :=
  (structHom_unitSection i U hV r).trans
    ((congrArg (Z.presheaf.map (homOfLE hV).op).hom hr).trans (map_zero _))

variable [IsImmersion i]
  {R : CategoryTheory.Sheaf (siteJ Z) CommRingCat.{u}} (a : R ⟶ invSheaf i)

/-- The restriction to `V ≤ L⁻¹(ι⁻¹U)` of the section of the kernel ideal attached to
`idealSectionOf i U r hr` is the unit section of `r`. -/
theorem map_kernelSection_idealSectionOf (U : X.Opens) {V : Z.Opens} (hV : V ≤ i ⁻¹ᵁ U)
    (r : Γ(X, U)) (hr : (i.app U).hom r = 0) :
    ((invSheaf i).obj.map (homOfLE (Stacks.Conormal.le_liftCoborder_preimage i U hV)).op).hom
        (kernelSection i (i.coborderRange.ι ⁻¹ᵁ U) (Stacks.Conormal.idealSectionOf i U r hr)).1 =
      unitSection i U hV r := by
  have h1 : (kernelSection i (i.coborderRange.ι ⁻¹ᵁ U)
      (Stacks.Conormal.idealSectionOf i U r hr)).1 =
      (coborderUnit i (i.coborderRange.ι ⁻¹ᵁ U)).hom ((i.coborderRange.ι.app U).hom r) :=
    congrArg (coborderUnit i (i.coborderRange.ι ⁻¹ᵁ U)).hom
      (Stacks.Conormal.kernelι_idealSectionOf i U r hr)
  have h2 := NatTrans.naturality_apply
    ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} i.base).unit.app X.sheaf).hom
    (homOfLE (x := i.coborderRange.ι ''ᵁ i.coborderRange.ι ⁻¹ᵁ U) (y := U)
      (Set.image_preimage_subset _ _)).op r
  refine (congrArg _ h1).trans ?_
  refine (congrArg (fun t => ((invSheaf i).obj.map
    (homOfLE (Stacks.Conormal.le_liftCoborder_preimage i U hV)).op).hom
      (((invSheaf i).obj.map (eqToHom (i.liftCoborder_preimage
        (i.coborderRange.ι ⁻¹ᵁ U))).op).hom t)) h2).trans ?_
  refine (congrArg _ (ConcreteCategory.comp_apply _ _ _).symm).trans ?_
  refine (ConcreteCategory.comp_apply _ _ _).symm.trans ?_
  have key : ∀ {a b c d : (Opens Z.carrier)ᵒᵖ} (f1 : a ⟶ b) (f2 : b ⟶ c) (f3 : c ⟶ d)
      (f : a ⟶ d), ((invSheaf i).obj.map f1 ≫ (invSheaf i).obj.map f2) ≫
        (invSheaf i).obj.map f3 = (invSheaf i).obj.map f := by
    intro a b c d f1 f2 f3 f
    rw [← Functor.map_comp, ← Functor.map_comp]
    exact congrArg _ (Subsingleton.elim _ _)
  exact congrArg (fun φ : (invSheaf i).obj.obj (op (i ⁻¹ᵁ U)) ⟶ (invSheaf i).obj.obj (op V) =>
    φ.hom ((((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} i.base).unit.app
      X.sheaf).hom.app (op U)).hom r)) (key _ _ _ _)

/-- **The conormal comparison on the class of a vanishing function**: it is the sites-level
conormal class of the image of the function in `i⁻¹𝒪_X`. -/
theorem conormalComparison_conormalClass (U : X.Opens) {V : Z.Opens} (hV : V ≤ i ⁻¹ᵁ U)
    (r : Γ(X, U)) (hr : (i.app U).hom r = 0) :
    (conormalComparison i).val.app (op V) (Stacks.Conormal.conormalClass i U hV r hr) =
      Stacks.Sites.Conormal.conormalClass.{u, u, u, u} (siteJ Z) R (invSheaf i) (structSheaf Z)
        a (structHom i) (op V) ⟨unitSection i U hV r, unitSection_mem i U hV r hr⟩ := by
  refine (PresheafOfModules.naturality_apply (conormalComparison i).val
    (homOfLE (Stacks.Conormal.le_liftCoborder_preimage i U hV)).op _).trans ?_
  refine (congrArg ((sitesConormalSheaf i).val.map
    (homOfLE (Stacks.Conormal.le_liftCoborder_preimage i U hV)).op)
    (conormalComparison_unit i (i.coborderRange.ι ⁻¹ᵁ U)
      (Stacks.Conormal.idealSectionOf i U r hr))).trans ?_
  exact (Stacks.Sites.Conormal.conormalClass_map (siteJ Z) R (invSheaf i) (structSheaf Z) a
    (structHom i) (homOfLE (Stacks.Conormal.le_liftCoborder_preimage i U hV)).op _ _
    (map_kernelSection_idealSectionOf i U hV r hr).symm).symm

end Stacks.Conormal.Sites

end SitesComparison

section TowerRings

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open TopologicalSpace Opposite
open Stacks.SheafOfModules (ringedSpaceStructureMap inverseImageBaseRing inverseImageMiddleRing
  inverseImageFirstRingMap)
open Stacks.Sheaves.RingedSpaceDifferentials (inverseImageSheaf structureSheafMap sheafAdjunction
  homEquiv_inverseImageStructureMap)
open Stacks.NaiveCotangentSixTermSequence (ringedSpaceHom)
open Stacks.SheafifyStalk (unitApp)

namespace Stacks.NaiveCotangentPulledImmersion

/-- Two morphisms of ringed spaces which are equal give the same unit section, up to
restriction. -/
theorem map_unitApp_c_congr {X' P' Y : RingedSpace.{u, u}} (i' : X' ⟶ P') {m m' : P' ⟶ Y}
    (e : m = m') (W : Opens Y.carrier) (y : ToType (Y.sheaf.obj.obj (op W)))
    {V : (Opens X'.carrier)ᵒᵖ}
    (f : op ((Opens.map i'.hom.base).obj ((Opens.map m.hom.base).obj W)) ⟶ V)
    (f' : op ((Opens.map i'.hom.base).obj ((Opens.map m'.hom.base).obj W)) ⟶ V) :
    ((inverseImageSheaf i').obj.map f).hom
        (unitApp i'.hom.base P'.sheaf _ ((m.hom.c.app (op W)).hom y)) =
      ((inverseImageSheaf i').obj.map f').hom
        (unitApp i'.hom.base P'.sheaf _ ((m'.hom.c.app (op W)).hom y)) := by
  subst e
  rw [Subsingleton.elim f f']

variable {X P Y X' P' Y' : Scheme.{u}} (i : X ⟶ P) (h : P ⟶ Y) (i' : X' ⟶ P') (h' : P' ⟶ Y')
  (g' : X' ⟶ X) (p : P' ⟶ P) (g : Y' ⟶ Y)

/-- **The two comparisons of the towers are compatible** when the square of ambient schemes
commutes: the base ring `i⁻¹h⁻¹𝒪_Y`, mapped into the middle ring `i⁻¹𝒪_P` and then compared with
`i'⁻¹𝒪_{P'}`, is the base ring compared with `i'⁻¹h'⁻¹𝒪_{Y'}` and then mapped into `i'⁻¹𝒪_{P'}`. -/
theorem inverseImageFirstRingMap_comp_middleRingComparison (hip : i' ≫ p = g' ≫ i)
    (w : g' ≫ (i ≫ h) = (i' ≫ h') ≫ g) (hph : p ≫ h = h' ≫ g) :
    (TopCat.Sheaf.pullback CommRingCat.{u} g'.base).map
        (inverseImageFirstRingMap (ringedSpaceHom i) (ringedSpaceHom h)) ≫
      middleRingComparison i i' g' p hip =
    baseRingTowerComparison i h i' h' g' g w ≫
      inverseImageFirstRingMap (ringedSpaceHom i') (ringedSpaceHom h') := by
  refine Stacks.SheafifyStalk.pullback_pullback_pullback_hom_ext_unitApp g'.base i.base h.base
    (fun W y => ?_)
  -- the left-hand side
  have L1 := Stacks.SheafifyStalk.pullback_map_unitApp g'.base
    (inverseImageFirstRingMap (ringedSpaceHom i) (ringedSpaceHom h)) _
    (unitApp i.base _ _ (unitApp h.base Y.sheaf W y))
  have L2 := Stacks.SheafifyStalk.pullback_map_unitApp i.base
    (ringedSpaceStructureMap (ringedSpaceHom h)) _ (unitApp h.base Y.sheaf W y)
  have L3 := Stacks.NaiveCotangentFlatBaseChange.ringedSpaceStructureMap_unitApp
    (ringedSpaceHom h) W y
  have L4 := Stacks.NaiveCotangentFlatBaseChange.baseRingComparisonRingedSpace_unitApp
    (ringedSpaceHom g') (ringedSpaceHom i) (ringedSpaceHom i') (ringedSpaceHom p)
    (congrArg (fun t : X' ⟶ P => t.toLRSHom.toShHom) hip.symm) _ ((h.c.app (op W)).hom y)
  have R1 := Stacks.SheafifyStalk.pullback_map_unitApp g'.base
    (Stacks.SheafOfModules.inverseImageCompIso (ringedSpaceHom i) (ringedSpaceHom h)).inv _
    (unitApp i.base _ _ (unitApp h.base Y.sheaf W y))
  have R2 := Stacks.SheafOfModules.inverseImageCompIso_inv_unitApp (ringedSpaceHom i)
    (ringedSpaceHom h) W y
  have R3 := Stacks.NaiveCotangentFlatBaseChange.baseRingComparisonRingedSpace_unitApp
    (ringedSpaceHom g') (ringedSpaceHom (i ≫ h)) (ringedSpaceHom (i' ≫ h')) (ringedSpaceHom g)
    (congrArg (fun t : X' ⟶ Y => t.toLRSHom.toShHom) w) W y
  have R5 := Stacks.SheafOfModules.inverseImageCompIso_hom_unitApp (ringedSpaceHom i')
    (ringedSpaceHom h')
    ((Opens.map g.base).obj W) ((g.c.app (op W)).hom y)
  have R7 := Stacks.SheafifyStalk.pullback_map_unitApp i'.base
    (ringedSpaceStructureMap (ringedSpaceHom h')) _
    (unitApp h'.base Y'.sheaf _ ((g.c.app (op W)).hom y))
  have R8 := Stacks.NaiveCotangentFlatBaseChange.ringedSpaceStructureMap_unitApp
    (ringedSpaceHom h') ((Opens.map g.base).obj W) ((g.c.app (op W)).hom y)
  refine ((congrArg ((middleRingComparison i i' g' p hip).hom.app _).hom
      (L1.trans (congrArg (unitApp g'.base _ _) (L2.trans
        (congrArg (unitApp i.base _ _) L3))))).trans L4).trans ?_
  refine Eq.symm ((congrArg ((inverseImageFirstRingMap (ringedSpaceHom i')
      (ringedSpaceHom h')).hom.app _).hom (congrArg ((Stacks.SheafOfModules.inverseImageCompIso
      (ringedSpaceHom i')
      (ringedSpaceHom h')).hom.hom.app _).hom (congrArg
        ((AlgebraicGeometry.BaseChangeStalk.baseRingComparison (i ≫ h) (i' ≫ h') g' g w).hom.app
          _).hom (R1.trans (congrArg (unitApp g'.base _ _) R2))))).trans ?_)
  refine (congrArg ((inverseImageFirstRingMap (ringedSpaceHom i')
      (ringedSpaceHom h')).hom.app _).hom ((congrArg ((Stacks.SheafOfModules.inverseImageCompIso
        (ringedSpaceHom i') (ringedSpaceHom h')).hom.hom.app _).hom R3).trans
      ((NatTrans.naturality_apply (Stacks.SheafOfModules.inverseImageCompIso
        (ringedSpaceHom i') (ringedSpaceHom h')).hom.hom _ _).trans
        (congrArg (((inverseImageBaseRing (ringedSpaceHom i') (ringedSpaceHom h')).obj.map
          _).hom) R5)))).trans ?_
  refine ((NatTrans.naturality_apply (inverseImageFirstRingMap (ringedSpaceHom i')
      (ringedSpaceHom h')).hom _ _).trans (congrArg (((inverseImageSheaf
        (ringedSpaceHom i')).obj.map _).hom)
          (R7.trans (congrArg (unitApp i'.base _ _) R8)))).trans ?_
  exact map_unitApp_c_congr (ringedSpaceHom i')
    (m := ringedSpaceHom h' ≫ ringedSpaceHom g) (m' := ringedSpaceHom p ≫ ringedSpaceHom h)
    (congrArg (fun t : P' ⟶ Y => t.toLRSHom.toShHom) hph.symm) W y _ _
/-- `inverseImageFirstRingMap_comp_middleRingComparison`, transposed. -/
theorem inverseImageFirstRingMap_comp_middleRingMap (hip : i' ≫ p = g' ≫ i)
    (w : g' ≫ (i ≫ h) = (i' ≫ h') ≫ g) (hph : p ≫ h = h' ≫ g) :
    inverseImageFirstRingMap (ringedSpaceHom i) (ringedSpaceHom h) ≫ middleRingMap i i' g' p hip =
      baseRingTowerMap i h i' h' g' g w ≫ (TopCat.Sheaf.pushforward CommRingCat.{u} g'.base).map
        (inverseImageFirstRingMap (ringedSpaceHom i') (ringedSpaceHom h')) := by
  refine ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u}
    g'.base).homEquiv_naturality_left _ _).symm.trans ?_
  refine Eq.trans ?_ ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u}
    g'.base).homEquiv_naturality_right _ _)
  exact congrArg _
    (inverseImageFirstRingMap_comp_middleRingComparison i h i' h' g' p g hip w hph)

open Stacks.Sites.FreeAlgebra in
/-- **The morphism of polynomial presentations of the two towers lies over the comparison of
the middle rings**: evaluating the variables of a polynomial over `i⁻¹h⁻¹𝒪_Y` in the sections of
`i⁻¹𝒪_P` and comparing with `i'⁻¹𝒪_{P'}` is the same as mapping it to a polynomial over
`i'⁻¹h'⁻¹𝒪_{Y'}` and evaluating there. -/
theorem presentationRingComparison_comp_canonicalPresentation [IsImmersion i] [IsImmersion i']
    (hip : i' ≫ p = g' ≫ i)
    (w : g' ≫ (i ≫ h) = (i' ≫ h') ≫ g) (hph : p ≫ h = h' ≫ g) :
    presentationRingComparison i h i' h' g' p g hip w ≫
        canonicalPresentation (Opens.grothendieckTopology X'.toRingedSpace.carrier)
          (inverseImageBaseRing (ringedSpaceHom i') (ringedSpaceHom h'))
          (inverseImageMiddleRing (ringedSpaceHom i'))
          (inverseImageFirstRingMap (ringedSpaceHom i') (ringedSpaceHom h')) =
      (TopCat.Sheaf.pullback CommRingCat.{u} g'.base).map
          (canonicalPresentation (Opens.grothendieckTopology X.toRingedSpace.carrier)
            (inverseImageBaseRing (ringedSpaceHom i) (ringedSpaceHom h))
            (inverseImageMiddleRing (ringedSpaceHom i))
            (inverseImageFirstRingMap (ringedSpaceHom i) (ringedSpaceHom h))) ≫
        middleRingComparison i i' g' p hip := by
  apply ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u}
    g'.base).homEquiv _ _).injective
  refine ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u}
    g'.base).homEquiv_naturality_right _ _).trans ?_
  refine Eq.trans ?_ ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u}
    g'.base).homEquiv_naturality_left _ _).symm
  refine (congrArg (fun t => t ≫ _) (Equiv.apply_symm_apply _ _)).trans ?_
  refine freeAlgebraSheaf_hom_ext _ _ _ _ ?_ ?_
  · exact coeff_comp_eq_of_parts (TopCat.Sheaf.pushforward CommRingCat.{u} g'.base) _ _ _ _ _ _ _
      (freeAlgebraSheafCoefficientMap_comp_desc _ _ _ _ _ _) _
      (canonicalPresentation_comp_coefficientMap _ _ _ _) _
      (canonicalPresentation_comp_coefficientMap _ _ _ _)
      (inverseImageFirstRingMap_comp_middleRingMap i h i' h' g' p g hip w hph).symm
  · refine var_comp_eq_of_parts
      (sheafToPresheaf _ CommRingCat.{u} ⋙ (Functor.whiskeringRight _ _ _).obj
        (forget CommRingCat.{u}))
      (TopCat.Sheaf.pushforward CommRingCat.{u} g'.base) _ _ _ _ _ _ _
      (freeAlgebraSheafVariable_comp_desc _ _ _ _ _ _) _
      ((Functor.whiskerLeft_comp _ _ _).symm.trans (congrArg (Functor.whiskerLeft _)
        (Stacks.Sites.FreeAlgebra.freeAlgebraSheafVariable_comp_canonicalPresentation.{u}
          (Opens.grothendieckTopology X'.toRingedSpace.carrier)
          (inverseImageBaseRing (ringedSpaceHom i') (ringedSpaceHom h'))
          (inverseImageMiddleRing (ringedSpaceHom i'))
          (inverseImageFirstRingMap (ringedSpaceHom i') (ringedSpaceHom h')))))
      _ (Stacks.Sites.FreeAlgebra.freeAlgebraSheafVariable_comp_canonicalPresentation.{u}
          (Opens.grothendieckTopology X.toRingedSpace.carrier)
          (inverseImageBaseRing (ringedSpaceHom i) (ringedSpaceHom h))
          (inverseImageMiddleRing (ringedSpaceHom i))
          (inverseImageFirstRingMap (ringedSpaceHom i) (ringedSpaceHom h))) ?_
    exact (congrArg (_ ≫ ·) (Functor.whiskerLeft_id' _)).trans
      ((Category.comp_id _).trans (Category.id_comp _).symm)

end Stacks.NaiveCotangentPulledImmersion

end TowerRings

section TowerConormal

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits RingedSpaceModuleAdjunction
open TopologicalSpace Opposite Stacks.SheafOfModules Stacks.Sites.FreeAlgebra Stacks.Sites.Conormal
open AlgebraicGeometry.SheafOfModules (underlyingRingHomOfSite inverseImageRingHom)
open Stacks.NaiveCotangentSixTermSequence (ringedSpaceHom)
open Stacks.Sheaves.RingedSpaceDifferentials (inverseImageSheaf inverseImageStructureMap)
open Stacks.SheafifyStalk (unitApp)

namespace Stacks.NaiveCotangentPulledImmersion

variable {X P Y X' P' Y' : Scheme.{u}} (i : X ⟶ P) (h : P ⟶ Y) (i' : X' ⟶ P') (h' : P' ⟶ Y')
  (g' : X' ⟶ X) (p : P' ⟶ P) (g : Y' ⟶ Y) [IsImmersion i] [IsImmersion i']

/-- The degree `-1` component of the comparison of the polynomial presentation with the
presentation `i⁻¹𝒪_P ⟶ 𝒪_X`, landing in the conormal sheaf of the latter. -/
abbrev towerConormalMap :=
  (Stacks.NaiveCotangentTower.schemeTowerComparison i h).f (-1) ≫
    eqToHom (towerNaiveCotangentComplex_X_negOne
      (inverseImageBaseRing (ringedSpaceHom i) (ringedSpaceHom h))
      (inverseImageMiddleRing (ringedSpaceHom i)) X.toRingedSpace.sheaf
      (inverseImageFirstRingMap (ringedSpaceHom i) (ringedSpaceHom h))
      (ringedSpaceStructureMap (ringedSpaceHom i)))

/-- `towerConormalMap` on the class of a polynomial relation: the class of its evaluation in
`i⁻¹𝒪_P`. -/
theorem towerConormalMap_conormalClassX (U : (Opens X.carrier)ᵒᵖ)
    (s : kernelIdeal (towerPresentation i h).hom U) :
    (towerConormalMap i h).val.app U
        (conormalClassX (towerCoefficientMap i h) (towerPresentation i h)
          (towerPresentationComplex_X_negOne i h) U s) =
      conormalClass.{u, u, u, u} (Opens.grothendieckTopology X.toRingedSpace.carrier)
        (inverseImageBaseRing (ringedSpaceHom i) (ringedSpaceHom h))
        (inverseImageMiddleRing (ringedSpaceHom i)) X.toRingedSpace.sheaf
        (inverseImageFirstRingMap (ringedSpaceHom i) (ringedSpaceHom h))
        (ringedSpaceStructureMap (ringedSpaceHom i)) U
        ⟨((canonicalPresentation (Opens.grothendieckTopology X.toRingedSpace.carrier)
            (inverseImageBaseRing (ringedSpaceHom i) (ringedSpaceHom h))
            (inverseImageMiddleRing (ringedSpaceHom i))
            (inverseImageFirstRingMap (ringedSpaceHom i) (ringedSpaceHom h))).hom.app U).hom s.1,
          kernelIdeal_le_comap (towerPresentation i h).hom
            (ringedSpaceStructureMap (ringedSpaceHom i)).hom
            (canonicalPresentation (Opens.grothendieckTopology X.toRingedSpace.carrier)
              (inverseImageBaseRing (ringedSpaceHom i) (ringedSpaceHom h))
              (inverseImageMiddleRing (ringedSpaceHom i))
              (inverseImageFirstRingMap (ringedSpaceHom i) (ringedSpaceHom h))).hom
            (hom_of_comp_eq (canonicalPresentation_comp_eq_presentation
              (inverseImageBaseRing (ringedSpaceHom i) (ringedSpaceHom h))
              (inverseImageMiddleRing (ringedSpaceHom i)) X.toRingedSpace.sheaf
              (inverseImageFirstRingMap (ringedSpaceHom i) (ringedSpaceHom h))
              (ringedSpaceStructureMap (ringedSpaceHom i)))) U s.2⟩ := by
  have hm := towerFacComparison_f_negOne
    (inverseImageBaseRing (ringedSpaceHom i) (ringedSpaceHom h)) X.toRingedSpace.sheaf
    (freeAlgebraSheaf (Opens.grothendieckTopology X.toRingedSpace.carrier)
      (inverseImageBaseRing (ringedSpaceHom i) (ringedSpaceHom h))
      (underlyingPresheaf (Opens.grothendieckTopology X.toRingedSpace.carrier)
        (inverseImageMiddleRing (ringedSpaceHom i))))
    (inverseImageMiddleRing (ringedSpaceHom i)) (towerCoefficientMap i h)
    (inverseImageFirstRingMap (ringedSpaceHom i) (ringedSpaceHom h)) (towerPresentation i h)
    (ringedSpaceStructureMap (ringedSpaceHom i))
    (canonicalPresentation (Opens.grothendieckTopology X.toRingedSpace.carrier)
      (inverseImageBaseRing (ringedSpaceHom i) (ringedSpaceHom h))
      (inverseImageMiddleRing (ringedSpaceHom i))
      (inverseImageFirstRingMap (ringedSpaceHom i) (ringedSpaceHom h)))
    (canonicalPresentation_comp_eq_presentation _ _ _ _ _)
    (canonicalPresentation_comp_coefficientMap _ _ _ _)
  have hc := conormalSheafMapOfFac_conormalClass.{u, u, u, u}
    (Opens.grothendieckTopology X.toRingedSpace.carrier)
    (inverseImageBaseRing (ringedSpaceHom i) (ringedSpaceHom h)) X.toRingedSpace.sheaf
    (freeAlgebraSheaf (Opens.grothendieckTopology X.toRingedSpace.carrier)
      (inverseImageBaseRing (ringedSpaceHom i) (ringedSpaceHom h))
      (underlyingPresheaf (Opens.grothendieckTopology X.toRingedSpace.carrier)
        (inverseImageMiddleRing (ringedSpaceHom i))))
    (inverseImageMiddleRing (ringedSpaceHom i)) (towerCoefficientMap i h)
    (inverseImageFirstRingMap (ringedSpaceHom i) (ringedSpaceHom h)) (towerPresentation i h)
    (ringedSpaceStructureMap (ringedSpaceHom i))
    (canonicalPresentation (Opens.grothendieckTopology X.toRingedSpace.carrier)
      (inverseImageBaseRing (ringedSpaceHom i) (ringedSpaceHom h))
      (inverseImageMiddleRing (ringedSpaceHom i))
      (inverseImageFirstRingMap (ringedSpaceHom i) (ringedSpaceHom h)))
    (canonicalPresentation_comp_eq_presentation _ _ _ _ _) U s
  have h1 := map_conormalClassX (towerCoefficientMap i h) (towerPresentation i h)
    (inverseImageFirstRingMap (ringedSpaceHom i) (ringedSpaceHom h))
    (ringedSpaceStructureMap (ringedSpaceHom i)) (towerPresentationComplex_X_negOne i h)
    (towerNaiveCotangentComplex_X_negOne
      (inverseImageBaseRing (ringedSpaceHom i) (ringedSpaceHom h))
      (inverseImageMiddleRing (ringedSpaceHom i)) X.toRingedSpace.sheaf
      (inverseImageFirstRingMap (ringedSpaceHom i) (ringedSpaceHom h))
      (ringedSpaceStructureMap (ringedSpaceHom i)))
    ((Stacks.NaiveCotangentTower.schemeTowerComparison i h).f (-1)) _ hm U s _ hc
  exact (congrArg _ h1).trans (eqToHom_val_app_conormalClassX _ _ _ _ _)

/-- The map `g'^*(i⁻¹𝒪_P-conormal) ⟶ (i'⁻¹𝒪_{P'}-conormal)` of the sites-level conormal sheaves
of the presentations `i⁻¹𝒪_P ⟶ 𝒪_X` and `i'⁻¹𝒪_{P'} ⟶ 𝒪_{X'}`, induced by the comparison of
the middle rings. -/
abbrev pulledMiddleConormalMap (hip : i' ≫ p = g' ≫ i) :=
  pulledConormalSheafMap g'.toLRSHom.toShHom (ringedSpaceStructureMap (ringedSpaceHom i))
    (ringedSpaceStructureMap (ringedSpaceHom i')) (middleRingComparison i i' g' p hip)
    (middleRingComparison_comp i i' g' p hip).symm

/-- The map `pulledMiddleConormalMap` on the two-step pullback of the image under a map `φ` of
a class `x`, when `φ x` is the conormal class of a section `t`: it is the conormal class of any
section `s'` equal to the image of `t` under the comparison of the middle rings. -/
private theorem pulledMiddleConormalMap_map_unit_conormalClass (hip : i' ≫ p = g' ≫ i)
    {M : _} (φ : M ⟶ conormalSheaf.{u, u, u, u} (Opens.grothendieckTopology X.toRingedSpace.carrier)
      (inverseImageMiddleRing (ringedSpaceHom i)) X.toRingedSpace.sheaf
      (ringedSpaceStructureMap (ringedSpaceHom i)))
    {R₁ R₂ : TopCat.Sheaf CommRingCat.{u} _} (a₁ : R₁ ⟶ inverseImageMiddleRing (ringedSpaceHom i))
    (a₂ : R₂ ⟶ inverseImageMiddleRing (ringedSpaceHom i')) (U : (Opens X.carrier)ᵒᵖ)
    (x : M.val.obj U) (t : kernelIdeal (ringedSpaceStructureMap (ringedSpaceHom i)).hom U)
    (hx : φ.val.app U x = conormalClass.{u, u, u, u}
      (Opens.grothendieckTopology X.toRingedSpace.carrier) R₁
      (inverseImageMiddleRing (ringedSpaceHom i)) X.toRingedSpace.sheaf a₁
      (ringedSpaceStructureMap (ringedSpaceHom i)) U t)
    (s' : kernelIdeal (ringedSpaceStructureMap (ringedSpaceHom i')).hom
      ((Opens.map g'.base).op.obj U))
    (hs : s'.1 = ((middleRingComparison i i' g' p hip).hom.app _).hom
      (unitApp g'.base _ U.unop t.1)) :
    (pulledMiddleConormalMap i i' g' p hip).val.app ((Opens.map g'.base).op.obj U)
        (((twoStepPullback g'.toLRSHom.toShHom).map φ).val.app ((Opens.map g'.base).op.obj U)
          (((twoStepCompAdjunction g'.toLRSHom.toShHom).unit.app M).val.app U x)) =
      conormalClass.{u, u, u, u} (Opens.grothendieckTopology X'.toRingedSpace.carrier) R₂
        (inverseImageMiddleRing (ringedSpaceHom i')) X'.toRingedSpace.sheaf a₂
        (ringedSpaceStructureMap (ringedSpaceHom i')) _ s' :=
  (congrArg ((pulledMiddleConormalMap i i' g' p hip).val.app _).hom
    ((twoStepPullback_map_unit_val_app g'.toLRSHom.toShHom φ U _).trans
      (congrArg (((twoStepCompAdjunction g'.toLRSHom.toShHom).unit.app _).val.app U).hom hx))).trans
    ((pulledConormalSheafMap_unit_conormalClass g'.toLRSHom.toShHom
      (ringedSpaceStructureMap (ringedSpaceHom i)) (ringedSpaceStructureMap (ringedSpaceHom i'))
      (middleRingComparison i i' g' p hip) (middleRingComparison_comp i i' g' p hip).symm _ a₁
      _ a₂ U t).trans (congrArg (conormalClass.{u, u, u, u} _ _ _ _ _ _ _) (Subtype.ext hs.symm)))

/-- **(C1) The comparison of the pulled-back polynomial presentations, read on the conormal
sheaves of the presentations by the middle rings.** -/
theorem pulledPresentationNegOne_comp_towerConormalMap (hip : i' ≫ p = g' ≫ i)
    (w : g' ≫ (i ≫ h) = (i' ≫ h') ≫ g) (hph : p ≫ h = h' ≫ g) :
    pulledPresentationNegOne i h i' h' g' p g hip w ≫ towerConormalMap i' h' =
      (twoStepPullback g'.toLRSHom.toShHom).map (towerConormalMap i h) ≫
        pulledMiddleConormalMap i i' g' p hip := by
  refine twoStepPullback_hom_ext_conormalClassX g'.toLRSHom.toShHom (towerCoefficientMap i h)
    (towerPresentation i h) (towerPresentationComplex_X_negOne i h) (fun U s => ?_)
  refine ((congrArg ((towerConormalMap i' h').val.app _).hom
    (pulledPresentationNegOne_unit_conormalClassX i h i' h' g' p g hip w U s)).trans
    (towerConormalMap_conormalClassX i' h' _ _)).trans
    (pulledMiddleConormalMap_map_unit_conormalClass i i' g' p hip (towerConormalMap i h) _ _ U _ _
      (towerConormalMap_conormalClassX i h U s) _ ?_).symm
  have e1 := congrArg (fun φ => (φ.hom.app ((Opens.map g'.base).op.obj U)).hom
      (unitApp g'.base _ U.unop s.1))
    (presentationRingComparison_comp_canonicalPresentation i h i' h' g' p g hip w hph)
  exact e1.trans (congrArg ((middleRingComparison i i' g' p hip).hom.app _).hom
    (Stacks.SheafifyStalk.pullback_map_unitApp g'.base _ U.unop s.1))

end Stacks.NaiveCotangentPulledImmersion

namespace Stacks.NaiveCotangentPulledImmersion

/-- Cancelling the two isomorphisms an isomorphism was transported along, in a bare category. -/
theorem comp_trans_symm_trans_symm_hom {C : Type*} [Category C] {A B M D E : C} (x : A ⟶ B)
    (a : B ≅ M) (b : D ≅ M) (c : E ≅ D) :
    (x ≫ (a ≪≫ b.symm ≪≫ c.symm).hom) ≫ c.hom ≫ b.hom = x ≫ a.hom := by
  simp

variable {X P Y : Scheme.{u}} (i : X ⟶ P) (h : P ⟶ Y) [IsImmersion i]

/-- The isomorphism `(I/I² ⟶ 𝒪_X ⊗ Ω) ≅ (𝒞_{X/P} ⟶ i^*Ω_{P/Y})` of [Stacks Project, Tag 0FV4] in
degree `-1`, read on the conormal sheaves: it is the conormal comparison of
`Stacks.Conormal.Sites.sitesConormalSheafIsoConormalSheaf`. -/
theorem towerIso_hom_f_negOne :
    (towerIso i h).hom.f (-1) ≫
        (Stacks.ConormalSequenceRight.conormalDifferentialComplexXIsoNegOne i h).hom ≫
        (Stacks.Conormal.DefiningIdealBridge.conormalSheafBridge i).hom =
      eqToHom (towerNaiveCotangentComplex_X_negOne
        (inverseImageBaseRing (ringedSpaceHom i) (ringedSpaceHom h))
        (inverseImageMiddleRing (ringedSpaceHom i)) X.toRingedSpace.sheaf
        (inverseImageFirstRingMap (ringedSpaceHom i) (ringedSpaceHom h))
        (ringedSpaceStructureMap (ringedSpaceHom i))) ≫
        (Stacks.Conormal.Sites.sitesConormalSheafIsoConormalSheaf i).hom := by
  have key : (towerIso i h).hom.f (-1) = eqToHom (towerNaiveCotangentComplex_X_negOne
        (inverseImageBaseRing (ringedSpaceHom i) (ringedSpaceHom h))
        (inverseImageMiddleRing (ringedSpaceHom i)) X.toRingedSpace.sheaf
        (inverseImageFirstRingMap (ringedSpaceHom i) (ringedSpaceHom h))
        (ringedSpaceStructureMap (ringedSpaceHom i))) ≫
      (Stacks.Conormal.Sites.sitesConormalSheafIsoConormalSheaf i ≪≫
        (Stacks.Conormal.DefiningIdealBridge.conormalSheafBridge i).symm ≪≫
        (Stacks.ConormalSequenceRight.conormalDifferentialComplexXIsoNegOne i h).symm).hom :=
    by
    simp only [towerIso, Stacks.NaiveCotangentConormalAssembly.towerComplexIso,
      HomologicalComplex.doubleIsoOfIsZero, asIso_hom]
    exact HomologicalComplex.mkHomFromDouble_f₀ _ _ _ _ _ _
  refine (congrArg (· ≫ _) key).trans ?_
  exact comp_trans_symm_trans_symm_hom _ _ _ _

end Stacks.NaiveCotangentPulledImmersion

end TowerConormal

section ConormalBaseChange

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits RingedSpaceModuleAdjunction
open TopologicalSpace Opposite Stacks.SheafOfModules Stacks.Sites.FreeAlgebra Stacks.Sites.Conormal
open AlgebraicGeometry.SheafOfModules (underlyingRingHomOfSite inverseImageRingHom)
open Stacks.NaiveCotangentSixTermSequence (ringedSpaceHom)
open Stacks.Sheaves.RingedSpaceDifferentials (inverseImageSheaf inverseImageStructureMap)
open Stacks.SheafifyStalk (unitApp)

namespace Stacks.Conormal

variable {Z X : Scheme.{u}} (i : Z ⟶ X) [IsImmersion i]

/-- **Maps out of the conormal sheaf are determined by the classes of vanishing functions.** -/
theorem hom_ext_conormalClass {N : Z.Modules} {a b : (conormalSheaf i : Z.Modules) ⟶ N}
    (h : ∀ (A : X.Opens) (r : Γ(X, A)) (hr : (i.app A).hom r = 0),
      a.val.app (op (i ⁻¹ᵁ A)) (conormalClass i A (le_refl _) r hr) =
        b.val.app (op (i ⁻¹ᵁ A)) (conormalClass i A (le_refl _) r hr)) :
    a = b := by
  refine Stacks.ConormalSequenceRight.hom_ext_canonicalConormalQuotientMap i
    (fun A y z hz => congrArg _ ?_)
  have hc := (conormalClass_eq_canonicalConormalQuotientMap i A (le_refl _) _
    (Stacks.Conormal.AffineCotangent.Sections.app_idealSheaf_section_eq_zero i A y) y rfl).trans
    (conormalSheaf_map_self i (le_refl _) _)
  exact (congrArg (a.val.app (op (i ⁻¹ᵁ A))) hc).symm.trans
    ((h A _ _).trans (congrArg (b.val.app (op (i ⁻¹ᵁ A))) hc))

end Stacks.Conormal

namespace Stacks.NaiveCotangentPulledImmersion

variable {X P X' P' : Scheme.{u}} (i : X ⟶ P) (i' : X' ⟶ P') (g' : X' ⟶ X) (p : P' ⟶ P)
  [IsImmersion i] [IsImmersion i']

omit [IsImmersion i] [IsImmersion i'] in
/-- **The comparison of the middle rings on unit sections**: it carries the image in
`g'⁻¹i⁻¹𝒪_P` of a section `r` of `𝒪_P` to the image of `p^♯ r` in `i'⁻¹𝒪_{P'}`. -/
theorem middleRingComparison_unitSection (hip : i' ≫ p = g' ≫ i) (A : P.Opens) (r : Γ(P, A)) :
    ((middleRingComparison i i' g' p hip).hom.app (op (g' ⁻¹ᵁ (i ⁻¹ᵁ A)))).hom
        (unitApp g'.base _ (i ⁻¹ᵁ A) (Stacks.Conormal.Sites.unitSection i A (le_refl _) r)) =
      Stacks.Conormal.Sites.unitSection i' (p ⁻¹ᵁ A)
        (Stacks.Immersion.preimage_le_preimage_of_square hip.symm (i ⁻¹ᵁ A) A le_rfl)
        ((p.app A).hom r) := by
  have h0 : Stacks.Conormal.Sites.unitSection i A (le_refl _) r = unitApp i.base P.sheaf A r := by
    refine (congrArg (fun φ => ((Stacks.Conormal.Sites.invSheaf i).obj.map φ).hom
      (unitApp i.base P.sheaf A r)) (Subsingleton.elim _ (𝟙 _))).trans ?_
    exact congrArg (fun φ => φ.hom (unitApp i.base P.sheaf A r))
      ((Stacks.Conormal.Sites.invSheaf i).obj.map_id _)
  refine (congrArg (fun t => ((middleRingComparison i i' g' p hip).hom.app
    (op (g' ⁻¹ᵁ (i ⁻¹ᵁ A)))).hom (unitApp g'.base _ (i ⁻¹ᵁ A) t)) h0).trans ?_
  refine (Stacks.NaiveCotangentFlatBaseChange.baseRingComparisonRingedSpace_unitApp
    (ringedSpaceHom g') (ringedSpaceHom i) (ringedSpaceHom i') (ringedSpaceHom p)
    (congrArg (fun t : X' ⟶ P => t.toLRSHom.toShHom) hip.symm) A r).trans ?_
  exact congrArg (fun φ => ((Stacks.Conormal.Sites.invSheaf i').obj.map φ).hom _)
    (Subsingleton.elim _ _)

/-- **(C2) The conormal comparisons and base change**: the map `(g')^*𝒞_{X/P} ⟶ 𝒞_{X'/P'}` of
[Stacks Project, Tag 01R4] followed by the comparison for `i'` is the pullback of the comparison
`𝒞_{X/P} ⟶ I/I²` for `i` followed by the map of sites-level conormal sheaves induced by the
middle rings. -/
theorem immersionConormalSheafMap_comp_conormalComparison (hip : i' ≫ p = g' ≫ i) :
    (Stacks.Immersion.immersionConormalSheafMap i' i g' p
          (Stacks.Immersion.toShHom_square hip) ≫
        Stacks.Conormal.Sites.conormalComparison i' :
        (modulePullback g'.toLRSHom.toShHom).obj (Stacks.Conormal.conormalSheaf i) ⟶ _) =
      (modulePullbackIsoTwoStep g'.toLRSHom.toShHom).hom.app (Stacks.Conormal.conormalSheaf i) ≫
        (twoStepPullback g'.toLRSHom.toShHom).map (Stacks.Conormal.Sites.conormalComparison i) ≫
        pulledMiddleConormalMap i i' g' p hip := by
  apply ((modulePullbackPushforwardAdjunction g'.toLRSHom.toShHom).homEquiv _ _).injective
  refine Eq.trans ?_ (CategoryTheory.Adjunction.homEquiv_leftAdjointUniq_hom_app_comp _ _ _).symm
  refine ((modulePullbackPushforwardAdjunction
    g'.toLRSHom.toShHom).homEquiv_naturality_right _ _).trans ?_
  refine Stacks.Conormal.hom_ext_conormalClass i (fun A r hr => ?_)
  have hC := Stacks.Immersion.preimage_le_preimage_of_square hip.symm (i ⁻¹ᵁ A) A le_rfl
  have L := Stacks.Conormal.conormalClass_immersionConormalSheafMap_app i' i g' p hip A
    (i ⁻¹ᵁ A) (le_refl _) hC r hr
  refine ((congrArg ((Stacks.Conormal.Sites.conormalComparison i').val.app _).hom L).trans
    (Stacks.Conormal.Sites.conormalComparison_conormalClass i'
      (𝟙 (Stacks.Conormal.Sites.invSheaf i')) (p ⁻¹ᵁ A) hC _ _)).trans ?_
  refine Eq.trans ?_ (twoStepPullbackAdjunction_homEquiv_val_app g'.toLRSHom.toShHom _ _
    ((twoStepPullback g'.toLRSHom.toShHom).map (Stacks.Conormal.Sites.conormalComparison i) ≫
        pulledMiddleConormalMap i i' g' p hip) _ _).symm
  refine Eq.trans ?_ (comp_val_app _ _ _ _).symm
  exact (pulledMiddleConormalMap_map_unit_conormalClass i i' g' p hip
    (Stacks.Conormal.Sites.conormalComparison i) _ _ _ _ _
    (Stacks.Conormal.Sites.conormalComparison_conormalClass i
      (𝟙 (Stacks.Conormal.Sites.invSheaf i)) A (le_refl _) r hr) _
    (middleRingComparison_unitSection i i' g' p hip A r).symm).symm

end Stacks.NaiveCotangentPulledImmersion

end ConormalBaseChange

section Assembly

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits RingedSpaceModuleAdjunction
open TopologicalSpace Opposite Stacks.SheafOfModules Stacks.Sites.FreeAlgebra Stacks.Sites.Conormal
open AlgebraicGeometry.SheafOfModules (underlyingRingHomOfSite inverseImageRingHom)
open Stacks.NaiveCotangentSixTermSequence (ringedSpaceHom)

namespace Stacks.NaiveCotangentPulledImmersion

/-- The bookkeeping of `pulledPresentationNegOne_comp_conormal`, in bare categories. -/
theorem comp_conormal_eq_of_parts {𝒜 ℬ : Type*} [Category 𝒜] [Category ℬ] (F G : 𝒜 ⥤ ℬ)
    (e : G ≅ F) {Q W₁ K D C S : 𝒜} (t : Q ⟶ W₁) (u : W₁ ⟶ K) (cd : K ⟶ D) (br : D ⟶ C)
    (eq : W₁ ⟶ S) (σ : S ≅ C) (hT : u ≫ cd ≫ br = eq ≫ σ.hom)
    {Q' W₁' K' D' C' S' : ℬ} (Φ : F.obj Q ⟶ Q') (t' : Q' ⟶ W₁') (u' : W₁' ⟶ K') (cd' : K' ⟶ D')
    (br' : D' ⟶ C') (eq' : W₁' ⟶ S') (σ' : S' ≅ C') (hT' : u' ≫ cd' ≫ br' = eq' ≫ σ'.hom)
    (π : F.obj S ⟶ S') (c : G.obj C ⟶ C')
    (h₁ : Φ ≫ t' ≫ eq' = F.map (t ≫ eq) ≫ π)
    (h₂ : c ≫ σ'.inv = e.hom.app C ≫ F.map σ.inv ≫ π) :
    Φ ≫ (t' ≫ u') ≫ cd' ≫ br' = F.map (t ≫ u) ≫ F.map cd ≫ e.inv.app D ≫ G.map br ≫ c := by
  have hc : c = e.hom.app C ≫ F.map σ.inv ≫ π ≫ σ'.hom := by
    rw [← reassoc_of% h₂, Iso.inv_hom_id, Category.comp_id]
  have hn : e.inv.app D ≫ G.map br = F.map br ≫ e.inv.app C := (e.inv.naturality br).symm
  have ht : (t ≫ u) ≫ cd ≫ br ≫ σ.inv = t ≫ eq := by
    rw [Category.assoc, reassoc_of% hT, Iso.hom_inv_id, Category.comp_id]
  rw [reassoc_of% hn, hc, Iso.inv_hom_id_app_assoc]
  calc Φ ≫ (t' ≫ u') ≫ cd' ≫ br' = (Φ ≫ t' ≫ eq') ≫ σ'.hom := by
        rw [Category.assoc t', hT']; simp only [Category.assoc]
    _ = F.map (t ≫ eq) ≫ π ≫ σ'.hom := by rw [h₁, Category.assoc]
    _ = _ := by rw [← ht]; simp only [Functor.map_comp, Category.assoc]

variable {X P Y X' P' Y' : Scheme.{u}} (i : X ⟶ P) (h : P ⟶ Y) (i' : X' ⟶ P') (h' : P' ⟶ Y')
  (g' : X' ⟶ X) (p : P' ⟶ P) (g : Y' ⟶ Y) [IsImmersion i] [IsImmersion i']

/-- **The comparison of the pulled-back polynomial presentations, read on the conormal sheaves
of the immersions.**  For commutative squares `i' ≫ p = g' ≫ i` and `p ≫ h = h' ≫ g`, the degree
`-1` comparison of the polynomial presentations of `𝒪_{X'}` and of the pullback of that of `𝒪_X`,
followed by the comparison with `𝒞_{X'/P'}`, is the pullback of the comparison with `𝒞_{X/P}`
followed by the map `(g')^*𝒞_{X/P} ⟶ 𝒞_{X'/P'}` of [Stacks Project, Tag 01R4]. -/
theorem pulledPresentationNegOne_comp_conormal (hip : i' ≫ p = g' ≫ i)
    (w : g' ≫ (i ≫ h) = (i' ≫ h') ≫ g) (hph : p ≫ h = h' ≫ g) :
    pulledPresentationNegOne i h i' h' g' p g hip w ≫
      (Stacks.NaiveCotangentTower.schemeTowerComparison i' h' ≫ (towerIso i' h').hom).f (-1) ≫
      (Stacks.ConormalSequenceRight.conormalDifferentialComplexXIsoNegOne i' h').hom ≫
      (Stacks.Conormal.DefiningIdealBridge.conormalSheafBridge i').hom =
    ((pulledComplexFunctor g'.toLRSHom.toShHom).map
          (Stacks.NaiveCotangentTower.schemeTowerComparison i h ≫ (towerIso i h).hom)).f (-1) ≫
        (twoStepPullback g'.toLRSHom.toShHom).map
          (Stacks.ConormalSequenceRight.conormalDifferentialComplexXIsoNegOne i h).hom ≫
        (modulePullbackIsoTwoStep g'.toLRSHom.toShHom).inv.app _ ≫
        (modulePullback g'.toLRSHom.toShHom).map
          (Stacks.Conormal.DefiningIdealBridge.conormalSheafBridge i).hom ≫
        Stacks.Immersion.immersionConormalSheafMap i' i g' p
          (Stacks.Immersion.toShHom_square hip) :=
  comp_conormal_eq_of_parts (twoStepPullback g'.toLRSHom.toShHom)
    (modulePullback g'.toLRSHom.toShHom) (modulePullbackIsoTwoStep g'.toLRSHom.toShHom)
    ((Stacks.NaiveCotangentTower.schemeTowerComparison i h).f (-1)) ((towerIso i h).hom.f (-1))
    (Stacks.ConormalSequenceRight.conormalDifferentialComplexXIsoNegOne i h).hom
    (Stacks.Conormal.DefiningIdealBridge.conormalSheafBridge i).hom _
    (Stacks.Conormal.Sites.sitesConormalSheafIsoConormalSheaf i) (towerIso_hom_f_negOne i h)
    (pulledPresentationNegOne i h i' h' g' p g hip w)
    ((Stacks.NaiveCotangentTower.schemeTowerComparison i' h').f (-1)) ((towerIso i' h').hom.f (-1))
    (Stacks.ConormalSequenceRight.conormalDifferentialComplexXIsoNegOne i' h').hom
    (Stacks.Conormal.DefiningIdealBridge.conormalSheafBridge i').hom _
    (Stacks.Conormal.Sites.sitesConormalSheafIsoConormalSheaf i') (towerIso_hom_f_negOne i' h')
    (pulledMiddleConormalMap i i' g' p hip) _
    (pulledPresentationNegOne_comp_towerConormalMap i h i' h' g' p g hip w hph)
    (immersionConormalSheafMap_comp_conormalComparison i i' g' p hip)

end Stacks.NaiveCotangentPulledImmersion

end Assembly

section HomologyNegOne

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits RingedSpaceModuleAdjunction
open TopologicalSpace Opposite Stacks.SheafOfModules Stacks.Sites.FreeAlgebra Stacks.Sites.Conormal
open AlgebraicGeometry.SheafOfModules (underlyingRingHomOfSite inverseImageRingHom)
open Stacks.NaiveCotangentSixTermSequence (ringedSpaceHom)
open Stacks.NaiveCotangentFlatBaseChange

namespace Stacks.NaiveCotangentPulledImmersion

/-- The bookkeeping of `homologyMap_negOne_baseChangeMapOfComparison`, in a bare category. -/
theorem comp_comp_eq_of_degreewise {C : Type*} [Category C] {A B B' D E E' G : C} (a : A ⟶ B')
    (b : B' ⟶ B) (ψ : A ⟶ B) (hψ : ψ = a ≫ b) (q : B ⟶ D) (ι : D ⟶ E) (ι₀ : A ⟶ E')
    (φ : E' ⟶ E) (hd : ψ ≫ q ≫ ι = ι₀ ≫ φ) (x : E ⟶ G) (y : E' ⟶ G) (hc : φ ≫ x = y) :
    (a ≫ b) ≫ q ≫ ι ≫ x = ι₀ ≫ y := by
  rw [← hψ, ← hc, ← Category.assoc ι₀, ← hd]
  simp only [Category.assoc]

variable {X P Y X' P' Y' : Scheme.{u}} (i : X ⟶ P) (h : P ⟶ Y) (i' : X' ⟶ P') (h' : P' ⟶ Y')
  (g' : X' ⟶ X) (p : P' ⟶ P) (g : Y' ⟶ Y) [IsImmersion i] [IsImmersion i']

/-- **`H^{-1}` of the base change map of `NL` is the restriction of the map of conormal
sheaves** ([Stacks Project, Tag 0FV9], first step of the proof). For `f = i ≫ h` and
`f' = i' ≫ h'` with `i`, `i'` immersions and `h`, `h'` formally smooth, and commutative squares
`i' ≫ p = g' ≫ i`, `p ≫ h = h' ≫ g`, the map induced on `H^{-1}` by the base change map
`(g')^*NL_{X/Y} ⟶ NL_{X'/Y'}` of [Stacks Project, Tag 0FV5], read through the identifications
`H^{-1}((g')^*NL_{X/Y}) ≅ Ker((g')^*δ)` and `H^{-1}(NL_{X'/Y'}) ≅ Ker δ'` of
[Stacks Project, Tag 0FV4], is the restriction of the map `(g')^*𝒞_{X/P} ⟶ 𝒞_{X'/P'}` of
[Stacks Project, Tag 01R4]. -/
theorem homologyMap_negOne_baseChangeMapOfComparison (hip : i' ≫ p = g' ≫ i)
    (w : g' ≫ (i ≫ h) = (i' ≫ h') ≫ g) (hph : p ≫ h = h' ≫ g)
    (hg : Stacks.Smooth.FormallySmoothScheme h) (hg' : Stacks.Smooth.FormallySmoothScheme h') :
    (pulledComplexHomologyNegOneIso i h g' (i ≫ h) rfl hg ≪≫
        kernelTwoStepPullbackIso i h g').inv ≫
      HomologicalComplex.homologyMap (baseChangeMapOfComparison (i ≫ h) (i' ≫ h') g'
        (AlgebraicGeometry.BaseChangeStalk.baseRingComparison (i ≫ h) (i' ≫ h') g' g w)
        (AlgebraicGeometry.BaseChangeStalk.baseRingComparison_comp (i ≫ h) (i' ≫ h') g' g w))
        (-1) ≫
      (naiveCotangentHomologyNegOneIso i' h' rfl hg').hom ≫
      kernel.ι (Stacks.ConormalSequenceRight.conormalDifferential i' h') =
    kernel.ι ((modulePullback g'.toLRSHom.toShHom).map
        ((Stacks.Conormal.DefiningIdealBridge.conormalSheafBridge i).inv ≫
          Stacks.ConormalSequenceRight.conormalDifferential i h)) ≫
      Stacks.Immersion.immersionConormalSheafMap i' i g' p
        (Stacks.Immersion.toShHom_square hip) ≫
      (Stacks.Conormal.DefiningIdealBridge.conormalSheafBridge i').inv := by
  refine (homologyMap_negOne_comp_eq_iff i h i' h' g' p hg hg' _ hip).2 ?_
  exact comp_comp_eq_of_degreewise _ _ _ (HomologicalComplex.homologyMap_comp _ _ (-1)) _ _ _ _
    (homologyMap_inv_homologyNegOneι_eq_of_degreewise
      (isZero_pulled_presentationComplex_X_negTwo i h g')
      (AlgebraicGeometry.Scheme.naiveCotangentComplex_isZero_X (i' ≫ h') (-2) (by decide)
        (by decide))
      (isZero_presentationComplex_X_negTwo i' h') _ (presentationToNaiveCotangent i' h')
      (pulledPresentationNegOne i h i' h' g' p g hip w)
      (pulledPresentationZero i h i' h' g' p g hip w)
      (pulledPresentationNegOne_comp_d i h i' h' g' p g hip w)
      (pulledPresentationNegOne_comp_presentationToNaiveCotangent i h i' h' g' p g hip w))
    _ _ (pulledPresentationNegOne_comp_conormal i h i' h' g' p g hip w hph)

end Stacks.NaiveCotangentPulledImmersion

namespace Stacks.NaiveCotangentPulledImmersion

variable {X P Y X' P' Y' : Scheme.{u}} (i : X ⟶ P) (h : P ⟶ Y) (i' : X' ⟶ P') (h' : P' ⟶ Y')
  (g' : X' ⟶ X) (p : P' ⟶ P) (g : Y' ⟶ Y) [IsImmersion i] [IsImmersion i']

universe v w in
/-- The kernel of a morphism which, read through isomorphisms of its source and target and
followed by a monomorphism, is a morphism followed by an isomorphism, in a bare category. -/
def kernelIsoOfConjComp {C : Type w} [Category.{v} C] [Abelian C] {H₁ H₂ K₁ E F D : C}
    (H : H₁ ⟶ H₂) (A : H₁ ≅ K₁) (δ : E ⟶ F) (B : H₂ ≅ kernel δ) (c : K₁ ⟶ D)
    (b : D ≅ E) (hE : A.inv ≫ H ≫ B.hom ≫ kernel.ι δ = c ≫ b.hom) : kernel H ≅ kernel c :=
  kernelIsoOfEq (show H = A.hom ≫ (A.inv ≫ H ≫ B.hom) ≫ B.inv by simp) ≪≫
    kernelConjIso _ _ _ ≪≫ (kernelCompMono _ (kernel.ι δ)).symm ≪≫
    kernelIsoOfEq (show (A.inv ≫ H ≫ B.hom) ≫ kernel.ι δ = c ≫ b.hom by
      simpa only [Category.assoc] using hE) ≪≫
    kernelCompMono _ _

/-- **The kernel of `H^{-1}` of the base change map of `NL`** is the kernel of the map
`(g')^*𝒞_{X/P} ⟶ 𝒞_{X'/P'}` of [Stacks Project, Tag 01R4] restricted to the kernel of the
pulled-back first arrow, for `f = i ≫ h` and `f' = i' ≫ h'`. -/
def kernelHomologyMapNegOneBaseChangeIso {f : X ⟶ Y} {f' : X' ⟶ Y'} (hf : i ≫ h = f)
    (hf' : i' ≫ h' = f') (hip : i' ≫ p = g' ≫ i) (w : g' ≫ f = f' ≫ g) (hph : p ≫ h = h' ≫ g)
    (hg : Stacks.Smooth.FormallySmoothScheme h) (hg' : Stacks.Smooth.FormallySmoothScheme h') :
    kernel (HomologicalComplex.homologyMap (baseChangeMapOfComparison f f' g'
        (AlgebraicGeometry.BaseChangeStalk.baseRingComparison f f' g' g w)
        (AlgebraicGeometry.BaseChangeStalk.baseRingComparison_comp f f' g' g w)) (-1)) ≅
      kernel (kernel.ι ((modulePullback g'.toLRSHom.toShHom).map
          ((Stacks.Conormal.DefiningIdealBridge.conormalSheafBridge i).inv ≫
            Stacks.ConormalSequenceRight.conormalDifferential i h)) ≫
        Stacks.Immersion.immersionConormalSheafMap i' i g' p
          (Stacks.Immersion.toShHom_square hip)) := by
  subst hf hf'
  exact kernelIsoOfConjComp _ (pulledComplexHomologyNegOneIso i h g' (i ≫ h) rfl hg ≪≫
      kernelTwoStepPullbackIso i h g') (Stacks.ConormalSequenceRight.conormalDifferential i' h')
    (naiveCotangentHomologyNegOneIso i' h' rfl hg')
    _ (Stacks.Conormal.DefiningIdealBridge.conormalSheafBridge i').symm
    (homologyMap_negOne_baseChangeMapOfComparison i h i' h' g' p g hip w hph hg hg')

end Stacks.NaiveCotangentPulledImmersion

end HomologyNegOne

end
