module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.CategoryTheory.Abelian.Exact
public import Mathlib.Geometry.RingedSpace.Stalks
public import Mathlib.Topology.Sheaves.Sheafify
public import StacksFrontier.AlgebraicGeometry.Topologies.InverseImageRingedSpace
public import StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.ClosedSubsetPullbackRightExact
public import StacksFrontier.Topology.Sheaves.Functors.Module.SemilinearStalk
public import StacksFrontier.Topology.Sheaves.Modules.StalkExactness
public import StacksFrontier.Topology.Sheaves.RingedSpace.StalkModulePullback
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Left exactness of module pullback, and the `pullbackExact` obligation of Tag 0AEF part (2)

`Stacks.Cohomology.SupportedComplexes.pullbackExact_of_preservesFiniteLimits` reduced the
`exactFunctor` obligation of Tag 0AEF part (2) to left exactness of
`RingedSpaceModuleAdjunction.modulePullback` along the inclusion of a closed subset, the colimit
half being free for every morphism of ringed spaces.
This file discharges the remaining half, and does so for an arbitrary continuous map.

The route is stalkwise, and nothing about sections is used — `modulePullback f` is *defined* as
the abstract left adjoint of `modulePushforward f`, so no section formula is available. What is
available is `Stacks.RingedSpace.stalkModulePullbackFunctorIso` (Stacks 0098), which identifies
`f^* ⋙ (-)_x` with `(-)_{f x} ⋙ (𝒪_{X,x} ⊗_{𝒪_{Y,f(x)}} -)`; the stalk functor on sheaves of
modules is exact, and base change along the germ map is exact as soon as that germ map is
*invertible*. Monomorphisms of sheaves of modules are detected on stalks, so `f^*` preserves
monomorphisms, and a right-exact additive functor preserving monomorphisms is exact.

For `f = AlgebraicGeometry.RingedSpace.inverseImageProjection X i` the germ map *is* invertible:
the structure sheaf of the source is `i⁻¹𝒪_X`, so the germ map is the stalkwise comparison
`𝒪_{X,i z} ⟶ (i⁻¹𝒪_X)_z`, which is an isomorphism. This is the content the Stacks Project
records as "`i^{-1}𝒪_X = 𝒪_X|_Z`, so `i^* = i^{-1}` is exact", and it needs no hypothesis on `i`
at all — in particular `IsClosed Z` is not used anywhere below.

## Main results

* `AlgebraicGeometry.SheafOfModules.mono_of_stalk_mono`: a morphism of sheaves of modules whose
  every stalk map is a monomorphism is a monomorphism.
* `Stacks.RingedSpace.preservesFiniteLimits_stalkBaseChange`: base change along an invertible
  germ map is exact.
* `Stacks.RingedSpace.isIso_stalkRingMap_of_isIso_stalkMap`: the `RingCat`-valued germ map of a
  morphism of ringed spaces is invertible as soon as the `CommRingCat`-valued stalk map of the
  underlying morphism of presheafed spaces is.
* `AlgebraicGeometry.RingedSpace.isIso_stalkMap_inverseImageProjection` and
  `AlgebraicGeometry.RingedSpace.isIso_stalkRingMap_inverseImageProjection`: the germ maps of the
  canonical morphism `(Z, i⁻¹𝒪_X) ⟶ (X, 𝒪_X)` are isomorphisms.
* `RingedSpaceModuleAdjunction.preservesFiniteLimits_modulePullback_of_isIso_stalkRingMap`: **a
  morphism of ringed spaces all of whose germ maps are invertible has exact module pullback.**
* `RingedSpaceModuleAdjunction.exactFunctor_inverseImageModulePullback`: restriction of sheaves
  of modules to an inverse-image ringed space is exact.
* `Stacks.Cohomology.SupportedComplexes.pullbackExact`: the `pullbackExact` obligation of Tag 0AEF
  part (2),
  unconditionally.

## Implementation notes

Three spelling crossings are isolated here, each in a single declaration, because `rw` matches at
`instances` transparency and cannot see through a project `def`.

`Stacks.RingedSpace.stalkRingMap` is stated for the `RingCat`-valued structure sheaf
`structureSheafRing`, while the stalk comparison for the inverse image is naturally a statement
about the `CommRingCat`-valued `X.presheaf`. `ringStalkCommIso` is `SemilinearStalk.commStalkIso`
restated at the `structureSheafRing` spelling — the only place the two meet — and
`stalkRingMap_comp_ringStalkCommIso` then identifies the two germ maps by a single computation on
germs, where both are given by `r ↦` the germ of `f^♯ r`.

The stalk comparison for the inverse image is proved against `PresheafedSpace.Hom.stalkMap`,
whose target is spelled `(inverseImage X i).presheaf.stalk z` with `z : Z`; the carrier of
`inverseImage X i` is `Z` by definition but not at `instances` transparency, so every `rw` whose
motive crosses that point is rejected with a type error that mentions the two carriers. The
germ-level chain `germ_inverseImageStalkIso_inv` is therefore written in term mode throughout
(`Eq.trans`, `congrArg`, `Category.assoc _ _ _`), which elaborates at default transparency.

`AlgebraicGeometry.RingedSpace.inverseImageProjection`'s structure map is the unit of the
*sheaf*-level adjunction `TopCat.Sheaf.pullbackPushforwardAdjunction`, whose left adjoint is the
abstract one; the stalk comparison needs the *presheaf*-level unit followed by sheafification.
`CategoryTheory.Adjunction.unit_leftAdjointUniq_hom_app` bridges the two, and
`inverseImageProjection_c_eq` records the resulting sections-level identity. This is the same
bookkeeping as in
`StacksFrontier/AlgebraicGeometry/ProEtale/WLocal/InverseImageStructureSheaf.lean`,
where it is carried out for locally ringed spaces with a general adjoint structure map; here the
adjoint structure map is the identity, so only the unit identity survives.

## References

* [Stacks Project, Tag 0AEF](https://stacks.math.columbia.edu/tag/0AEF)
* [Stacks Project, Tag 0098](https://stacks.math.columbia.edu/tag/0098)
* [Stacks Project, Tag 01AJ](https://stacks.math.columbia.edu/tag/01AJ)
* [Stacks Project, Tag 01AX](https://stacks.math.columbia.edu/tag/01AX)
* [Stacks Project, Tag 0096](https://stacks.math.columbia.edu/tag/0096)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction

universe u

namespace AlgebraicGeometry.SheafOfModules

/-- **Monomorphisms of sheaves of modules are detected on stalks.** The underlying sheaf of
abelian groups detects monomorphisms (`SheafOfModules.toSheaf` is faithful), and for abelian
sheaves this is `TopCat.Presheaf.mono_iff_stalk_mono`. -/
theorem mono_of_stalk_mono {X : TopCat.{u}}
    (O : CategoryTheory.Sheaf (Opens.grothendieckTopology X) RingCat.{u})
    {M N : _root_.SheafOfModules.{u} O} (g : M ⟶ N)
    (h : ∀ x, Mono ((stalkFunctor O x).map g)) : Mono g :=
  (_root_.SheafOfModules.toSheaf O).mono_of_mono_map <|
    (TopCat.Presheaf.mono_iff_stalk_mono _).mpr fun x =>
      (AddCommGrpCat.mono_iff_injective _).mpr ((ModuleCat.mono_iff_injective _).mp (h x))

end AlgebraicGeometry.SheafOfModules

namespace CategoryTheory.Functor

/-- A functor preserving finite limits preserves monomorphisms: a monomorphism is a morphism
whose self-pullback is trivial, and the cospan is a finite shape. -/
theorem preservesMonomorphisms_of_preservesFiniteLimits
    {C D : Type*} [Category* C] [Category* D] (F : C ⥤ D) [PreservesFiniteLimits F] :
    F.PreservesMonomorphisms :=
  ⟨fun g _ => preserves_mono_of_preservesLimit F g⟩

end CategoryTheory.Functor

namespace Stacks.RingedSpace

/-- `SemilinearStalk.commStalkIso` restated at the `structureSheafRing`
spelling: the `RingCat`-valued stalk of the structure sheaf is the `CommRingCat`-valued one.

This is the single declaration in which the two spellings of the structure sheaf meet. -/
noncomputable def ringStalkCommIso (X : AlgebraicGeometry.RingedSpace.{u, u}) (x : X.carrier) :
    TopCat.Presheaf.stalk (C := RingCat.{u}) (structureSheafRing X).obj x ≅
      (forget₂ CommRingCat.{u} RingCat.{u}).obj (X.presheaf.stalk x) :=
  SemilinearStalk.commStalkIso X.presheaf x

/-- `ringStalkCommIso` sends the germ of a section `r` of `structureSheafRing X` on `V` to the germ
of `r` in the stalk of `X.presheaf`. -/
theorem ringStalkCommIso_germ (X : AlgebraicGeometry.RingedSpace.{u, u}) (x : X.carrier)
    (V : Opens X.carrier) (hV : x ∈ V) (r : (structureSheafRing X).obj.obj (op V)) :
    (ringStalkCommIso X x).hom.hom
        ((TopCat.Presheaf.germ (C := RingCat.{u}) (structureSheafRing X).obj V x hV).hom r) =
      (X.presheaf.germ V x hV).hom r :=
  SemilinearStalk.commStalkRingEquiv_germ X.presheaf x V hV r

variable {X Y : AlgebraicGeometry.RingedSpace.{u, u}} (f : X ⟶ Y) (x : X.carrier)

/-- **The two germ maps of a morphism of ringed spaces agree.** `stalkRingMap f x` is the
`CommRingCat`-valued `PresheafedSpace.Hom.stalkMap` of the underlying morphism of presheafed
spaces, read through `ringStalkCommIso`. Both send the germ of `r` to the germ of `f^♯ r`. -/
theorem stalkRingMap_comp_ringStalkCommIso :
    stalkRingMap f x ≫ (ringStalkCommIso X x).hom =
      (ringStalkCommIso Y (f.hom.base x)).hom ≫
        (forget₂ CommRingCat.{u} RingCat.{u}).map (f.hom.stalkMap x) := by
  apply TopCat.Presheaf.stalk_hom_ext
  intro V hV
  apply ConcreteCategory.ext_apply
  intro r
  have h3 : (ringStalkCommIso X x).hom.hom
      ((TopCat.Presheaf.germ (C := RingCat.{u}) (structureSheafRing X).obj
          ((opensMap f).obj V) x hV).hom
        ((structureSheafHom f).hom.app (op V) r)) =
      (X.presheaf.germ ((opensMap f).obj V) x hV).hom ((f.hom.c.app (op V)).hom r) :=
    ringStalkCommIso_germ X x ((opensMap f).obj V) hV _
  change (ringStalkCommIso X x).hom.hom
      ((stalkRingMap f x).hom
        ((TopCat.Presheaf.germ (C := RingCat.{u}) (structureSheafRing Y).obj V
          (f.hom.base x) hV).hom r)) =
    (f.hom.stalkMap x).hom ((ringStalkCommIso Y (f.hom.base x)).hom.hom
      ((TopCat.Presheaf.germ (C := RingCat.{u}) (structureSheafRing Y).obj V
        (f.hom.base x) hV).hom r))
  rw [stalkRingMap_germ f x V hV r, ringStalkCommIso_germ Y (f.hom.base x) V hV r, h3]
  exact (AlgebraicGeometry.PresheafedSpace.stalkMap_germ_apply f.hom V x hV r).symm

/-- The `RingCat`-valued germ map is invertible as soon as the `CommRingCat`-valued stalk map of
the underlying morphism of presheafed spaces is. -/
theorem isIso_stalkRingMap_of_isIso_stalkMap (h : IsIso (f.hom.stalkMap x)) :
    IsIso (stalkRingMap f x) := by
  rw [show stalkRingMap f x = (ringStalkCommIso Y (f.hom.base x)).hom ≫
      (forget₂ CommRingCat.{u} RingCat.{u}).map (f.hom.stalkMap x) ≫
        (ringStalkCommIso X x).inv by
    rw [← Category.assoc, ← stalkRingMap_comp_ringStalkCommIso f x, Category.assoc,
      Iso.hom_inv_id, Category.comp_id]]
  infer_instance

/-- **Base change along an invertible germ map is exact.** `stalkBaseChange f x` is
`ModuleCat.extendScalars` of the germ map, left adjoint to `ModuleCat.restrictScalars`; when the
germ map is invertible the latter is an equivalence, so the former is its inverse. -/
theorem preservesFiniteLimits_stalkBaseChange (h : IsIso (stalkRingMap f x)) :
    PreservesFiniteLimits (stalkBaseChange f x) := by
  let := structureStalkCommRing Y (f.hom.base x)
  let := structureStalkCommRing X x
  let e : _ ≃+* _ := (@asIso _ _ _ _ _ h).ringCatIsoToRingEquiv
  have hres : (ModuleCat.restrictScalars.{u, u, u} (stalkRingMap f x).hom).IsEquivalence :=
    ModuleCat.restrictScalars_isEquivalence_of_ringEquiv e
  let F := ModuleCat.restrictScalars.{u, u, u} (stalkRingMap f x).hom
  exact preservesFiniteLimits_of_natIso
    ((ModuleCat.extendRestrictScalarsAdj.{u, u, u} (stalkRingMap f x).hom).leftAdjointUniq
      F.asEquivalence.symm.toAdjunction).symm

end Stacks.RingedSpace

namespace RingedSpaceModuleAdjunction

variable {X Y : AlgebraicGeometry.RingedSpace.{u, u}} (f : X ⟶ Y)

/-- **Module pullback preserves monomorphisms when every germ map of `f` is invertible.**
Monomorphisms are detected on stalks, and on stalks `f^*` is the stalk at `f x` followed by base
change along the germ map (Stacks 0098) — the first factor exact, the second exact by
invertibility. -/
theorem preservesMonomorphisms_modulePullback_of_isIso_stalkRingMap
    (h : ∀ x : X.carrier, IsIso (Stacks.RingedSpace.stalkRingMap f x)) :
    (modulePullback f).PreservesMonomorphisms := by
  constructor
  intro M N g _
  apply AlgebraicGeometry.SheafOfModules.mono_of_stalk_mono
  intro x
  have : PreservesFiniteLimits (Stacks.RingedSpace.stalkBaseChange f x) :=
    Stacks.RingedSpace.preservesFiniteLimits_stalkBaseChange f x (h x)
  have : (AlgebraicGeometry.SheafOfModules.stalkFunctor (structureSheafRing Y)
      (f.hom.base x)).PreservesMonomorphisms :=
    Functor.preservesMonomorphisms_of_preservesFiniteLimits _
  have : (Stacks.RingedSpace.stalkBaseChange f x).PreservesMonomorphisms :=
    Functor.preservesMonomorphisms_of_preservesFiniteLimits _
  have : (modulePullback f ⋙
      AlgebraicGeometry.SheafOfModules.stalkFunctor (structureSheafRing X)
        x).PreservesMonomorphisms :=
    Functor.PreservesMonomorphisms.of_iso
      (Stacks.RingedSpace.stalkModulePullbackFunctorIso f x).symm
  exact (modulePullback f ⋙
    AlgebraicGeometry.SheafOfModules.stalkFunctor (structureSheafRing X) x).map_mono g

/-- **Module pullback is left exact when every germ map of `f` is invertible.** Right exactness
is unconditional (`preservesColimits_modulePullback`), so with monomorphisms preserved the
functor preserves homology, hence finite limits. -/
theorem preservesFiniteLimits_modulePullback_of_isIso_stalkRingMap
    (h : ∀ x : X.carrier, IsIso (Stacks.RingedSpace.stalkRingMap f x)) :
    PreservesFiniteLimits (modulePullback f) := by
  have := preservesMonomorphisms_modulePullback_of_isIso_stalkRingMap f h
  have : PreservesColimits (modulePullback f) := preservesColimits_modulePullback f
  have : ∀ {A B : _root_.SheafOfModules.{u} (structureSheafRing Y)} (u : A ⟶ B),
      PreservesColimit (parallelPair u 0) (modulePullback f) := fun _ => inferInstance
  have : (modulePullback f).PreservesHomology :=
    Functor.preservesHomology_of_preservesMonos_and_cokernels _
  exact Functor.preservesFiniteLimits_of_preservesHomology _

end RingedSpaceModuleAdjunction

namespace AlgebraicGeometry.RingedSpace

variable (X : AlgebraicGeometry.RingedSpace.{u, u}) {Z : TopCat.{u}} (i : Z ⟶ X.carrier)

/-- The presheaf-level inverse image of the structure sheaf, before sheafification. -/
noncomputable abbrev presheafInverseImage : TopCat.Presheaf CommRingCat.{u} Z :=
  (TopCat.Presheaf.pullback CommRingCat.{u} i).obj X.presheaf

/-- The sheafification map of the presheaf-level inverse image of the structure sheaf. -/
noncomputable abbrev toSheafifyInverseImage : presheafInverseImage X i ⟶
    ((presheafToSheaf (Opens.grothendieckTopology Z) CommRingCat.{u}).obj
      (presheafInverseImage X i)).obj :=
  CategoryTheory.toSheafify (Opens.grothendieckTopology Z) (presheafInverseImage X i)

/-- Mathlib's comparison between the abstract sheaf pullback and the sheafification of the
presheaf pullback. -/
noncomputable abbrev sheafPullbackIsoSheafify := TopCat.Sheaf.pullbackIso CommRingCat.{u} i

/-- The canonical map from the presheaf-level inverse image of `𝒪_X` to the structure sheaf
`i⁻¹𝒪_X` of the inverse-image ringed space: sheafify, then transport along Mathlib's comparison
with the abstract sheaf pullback. -/
noncomputable def presheafInverseImageToStructureSheaf :
    presheafInverseImage X i ⟶ (inverseImage X i).presheaf :=
  toSheafifyInverseImage X i ≫
    (TopCat.Sheaf.forget CommRingCat.{u} Z).map
      ((sheafPullbackIsoSheafify X i).inv.app X.sheaf)

/-- **The stalk of `i⁻¹𝒪_X` at `z` is the stalk of `𝒪_X` at `i z`.** Sheafification does not
change stalks, and `TopCat.Presheaf.stalkPullbackIso` computes the stalk of the presheaf-level
inverse image. -/
noncomputable def inverseImageStalkIso (z : Z) :
    TopCat.Presheaf.stalk (inverseImage X i).presheaf z ≅
      TopCat.Presheaf.stalk X.presheaf (i z) := by
  have hunit : IsIso ((TopCat.Presheaf.stalkFunctor CommRingCat.{u} z).map
      (toSheafifyInverseImage X i)) :=
    TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso z CommRingCat.{u} _
  exact (TopCat.Presheaf.stalkFunctor CommRingCat.{u} z).mapIso
      ((TopCat.Sheaf.forget CommRingCat.{u} Z).mapIso
        ((sheafPullbackIsoSheafify X i).app X.sheaf)) ≪≫
    (@asIso _ _ _ _ _ hunit).symm ≪≫
      (TopCat.Presheaf.stalkPullbackIso CommRingCat.{u} i X.presheaf z).symm

/-- The inverse of `inverseImageStalkIso X i z` is the composite of
`TopCat.Presheaf.stalkPullbackHom`, the stalk of the sheafification unit, and the stalk of the
comparison `sheafPullbackIsoSheafify X i`. -/
theorem inverseImageStalkIso_inv (z : Z) :
    (inverseImageStalkIso X i z).inv =
      TopCat.Presheaf.stalkPullbackHom CommRingCat.{u} i X.presheaf z ≫
        (TopCat.Presheaf.stalkFunctor CommRingCat.{u} z).map (toSheafifyInverseImage X i) ≫
          (TopCat.Presheaf.stalkFunctor CommRingCat.{u} z).map
            ((TopCat.Sheaf.forget CommRingCat.{u} Z).map
              ((sheafPullbackIsoSheafify X i).inv.app X.sheaf)) :=
  rfl

/-- The adjunction `i⁻¹ ⊣ i_*` on sheaves of commutative rings, with the abstract left adjoint:
this is the one whose unit is the structure map of `inverseImageProjection`. -/
noncomputable abbrev sheafInverseImageAdjunction :=
  TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} i

/-- The same adjunction with the left adjoint built as "left Kan extension, then sheafify": this
is the one whose unit is visibly the presheaf-level unit followed by sheafification. -/
noncomputable abbrev sheafInverseImageAdjunctionSheafify :=
  CategoryTheory.Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (TopologicalSpace.Opens.map i) CommRingCat.{u}
      (Opens.grothendieckTopology X.carrier) (Opens.grothendieckTopology Z)

/-- The two adjunctions have the same right adjoint, so their units differ by the canonical
isomorphism of left adjoints. -/
theorem sheafInverseImageAdjunction_unit_eq :
    (sheafInverseImageAdjunctionSheafify X i).unit.app X.sheaf ≫
        (TopCat.Sheaf.pushforward CommRingCat.{u} i).map
          ((sheafPullbackIsoSheafify X i).inv.app X.sheaf) =
      (sheafInverseImageAdjunction X i).unit.app X.sheaf := by
  have hUnitRel : (sheafInverseImageAdjunction X i).unit.app X.sheaf ≫
      (TopCat.Sheaf.pushforward CommRingCat.{u} i).map
        ((sheafPullbackIsoSheafify X i).hom.app X.sheaf) =
      (sheafInverseImageAdjunctionSheafify X i).unit.app X.sheaf :=
    CategoryTheory.Adjunction.unit_leftAdjointUniq_hom_app (sheafInverseImageAdjunction X i)
      (sheafInverseImageAdjunctionSheafify X i) X.sheaf
  have hmap : (TopCat.Sheaf.pushforward CommRingCat.{u} i).map
        ((sheafPullbackIsoSheafify X i).hom.app X.sheaf) ≫
      (TopCat.Sheaf.pushforward CommRingCat.{u} i).map
        ((sheafPullbackIsoSheafify X i).inv.app X.sheaf) = 𝟙 _ := by
    rw [← CategoryTheory.Functor.map_comp, (sheafPullbackIsoSheafify X i).hom_inv_id_app,
      CategoryTheory.Functor.map_id]
  have hswap : (sheafInverseImageAdjunctionSheafify X i).unit.app X.sheaf ≫
      (TopCat.Sheaf.pushforward CommRingCat.{u} i).map
        ((sheafPullbackIsoSheafify X i).inv.app X.sheaf) =
      ((sheafInverseImageAdjunction X i).unit.app X.sheaf ≫
        (TopCat.Sheaf.pushforward CommRingCat.{u} i).map
          ((sheafPullbackIsoSheafify X i).hom.app X.sheaf)) ≫
        (TopCat.Sheaf.pushforward CommRingCat.{u} i).map
          ((sheafPullbackIsoSheafify X i).inv.app X.sheaf) :=
    congrArg (fun t => t ≫ (TopCat.Sheaf.pushforward CommRingCat.{u} i).map
      ((sheafPullbackIsoSheafify X i).inv.app X.sheaf)) hUnitRel.symm
  refine hswap.trans ?_
  rw [Category.assoc, hmap]
  exact Category.comp_id _

/-- **Sections form of the structure map of `inverseImageProjection`:** on an open `U` it is the
presheaf-level adjunction unit followed by `presheafInverseImageToStructureSheaf`. -/
theorem inverseImageProjection_c_eq (U : Opens X.carrier) :
    ((TopCat.Presheaf.pullbackPushforwardAdjunction CommRingCat.{u} i).unit.app
        X.presheaf).app (op U) ≫
      (presheafInverseImageToStructureSheaf X i).app
        (op ((TopologicalSpace.Opens.map i).obj U)) =
      (inverseImageProjection X i).hom.c.app (op U) :=
  congrArg (fun t => ((TopCat.Sheaf.forget CommRingCat.{u} X.carrier).map t).app (op U))
    (sheafInverseImageAdjunction_unit_eq X i)

/-- The germ-level identity behind `isIso_stalkMap_inverseImageProjection`.

Written in term mode on purpose: the two sides live in
`X.presheaf.obj (op U) ⟶ (inverseImage X i).presheaf.stalk z`, whose target needs the carrier of
`inverseImage X i` to be `Z` — true by definition, false at `instances` transparency, so every
`rw` whose motive abstracts across it is rejected. -/
theorem germ_inverseImageStalkIso_inv (z : Z) (U : Opens X.carrier) (hU : i z ∈ U) :
    X.presheaf.germ U (i z) hU ≫ (inverseImageStalkIso X i z).inv =
      X.presheaf.germ U (i z) hU ≫ (inverseImageProjection X i).hom.stalkMap z := by
  have hMap : z ∈ (TopologicalSpace.Opens.map i).obj U := hU
  have hpsi : (TopCat.Presheaf.stalkFunctor CommRingCat.{u} z).map
        (toSheafifyInverseImage X i) ≫
      (TopCat.Presheaf.stalkFunctor CommRingCat.{u} z).map
        ((TopCat.Sheaf.forget CommRingCat.{u} Z).map
          ((sheafPullbackIsoSheafify X i).inv.app X.sheaf)) =
      (TopCat.Presheaf.stalkFunctor CommRingCat.{u} z).map
        (presheafInverseImageToStructureSheaf X i) :=
    (CategoryTheory.Functor.map_comp _ _ _).symm
  have hcinv : (inverseImageStalkIso X i z).inv =
      TopCat.Presheaf.stalkPullbackHom CommRingCat.{u} i X.presheaf z ≫
        (TopCat.Presheaf.stalkFunctor CommRingCat.{u} z).map
          (presheafInverseImageToStructureSheaf X i) :=
    (inverseImageStalkIso_inv X i z).trans
      (congrArg (fun t => TopCat.Presheaf.stalkPullbackHom CommRingCat.{u} i X.presheaf z ≫ t)
        hpsi)
  have e1 := TopCat.Presheaf.germ_stalkPullbackHom_assoc CommRingCat.{u} i X.presheaf z U hU
    ((TopCat.Presheaf.stalkFunctor CommRingCat.{u} z).map
      (presheafInverseImageToStructureSheaf X i))
  have e2 := TopCat.Presheaf.stalkFunctor_map_germ ((TopologicalSpace.Opens.map i).obj U) z hMap
    (presheafInverseImageToStructureSheaf X i)
  have e3 := inverseImageProjection_c_eq X i U
  have e4 := AlgebraicGeometry.PresheafedSpace.stalkMap_germ
    (inverseImageProjection X i).hom U z hU
  exact (congrArg (fun t => X.presheaf.germ U (i z) hU ≫ t) hcinv).trans
    (e1.trans
      ((congrArg (fun t => ((TopCat.Presheaf.pullbackPushforwardAdjunction
          CommRingCat.{u} i).unit.app X.presheaf).app (op U) ≫ t) e2).trans
        ((Category.assoc _ _ _).symm.trans
          ((congrArg (fun t => t ≫ (inverseImage X i).presheaf.germ
              ((TopologicalSpace.Opens.map i).obj U) z hMap) e3).trans e4.symm))))

/-- **The stalk maps of `(Z, i⁻¹𝒪_X) ⟶ (X, 𝒪_X)` are isomorphisms**, for every continuous map
`i`. This is the Stacks Project's "`i^{-1}𝒪_X = 𝒪_X|_Z`". -/
theorem isIso_stalkMap_inverseImageProjection (z : Z) :
    IsIso ((inverseImageProjection X i).hom.stalkMap z) := by
  have e : (inverseImageStalkIso X i z).inv =
      (inverseImageProjection X i).hom.stalkMap z :=
    TopCat.Presheaf.stalk_hom_ext _ (fun U hU => germ_inverseImageStalkIso_inv X i z U hU)
  rw [← e]
  exact (inverseImageStalkIso X i z).isIso_inv

/-- The `RingCat`-valued germ maps of `(Z, i⁻¹𝒪_X) ⟶ (X, 𝒪_X)` are isomorphisms. -/
theorem isIso_stalkRingMap_inverseImageProjection (z : Z) :
    IsIso (Stacks.RingedSpace.stalkRingMap (inverseImageProjection X i) z) :=
  Stacks.RingedSpace.isIso_stalkRingMap_of_isIso_stalkMap
    (X := inverseImage X i) (Y := X) (inverseImageProjection X i) z
    (isIso_stalkMap_inverseImageProjection X i z)

end AlgebraicGeometry.RingedSpace

namespace RingedSpaceModuleAdjunction

/-- **Restriction of sheaves of modules to an inverse-image ringed space is left exact.** No
hypothesis on the continuous map `i` is needed: the structure sheaf of the source is `i⁻¹𝒪_X`, so
every germ map is an isomorphism and no base change takes place. -/
@[sga "4 IV 13.7" "special case"]
theorem preservesFiniteLimits_inverseImageModulePullback
    (X : AlgebraicGeometry.RingedSpace.{u, u}) {Z : TopCat.{u}} (i : Z ⟶ X.carrier) :
    PreservesFiniteLimits (AlgebraicGeometry.RingedSpace.inverseImageModulePullback X i) :=
  preservesFiniteLimits_modulePullback_of_isIso_stalkRingMap _
    (AlgebraicGeometry.RingedSpace.isIso_stalkRingMap_inverseImageProjection X i)

/-- **Restriction of sheaves of modules to an inverse-image ringed space is exact.** -/
theorem exactFunctor_inverseImageModulePullback
    (X : AlgebraicGeometry.RingedSpace.{u, u}) {Z : TopCat.{u}} (i : Z ⟶ X.carrier) :
    exactFunctor (_root_.SheafOfModules.{u} (structureSheafRing X))
      (_root_.SheafOfModules.{u}
        (structureSheafRing (AlgebraicGeometry.RingedSpace.inverseImage X i)))
      (AlgebraicGeometry.RingedSpace.inverseImageModulePullback X i) :=
  exactFunctor_modulePullback_of_preservesFiniteLimits _
    (preservesFiniteLimits_inverseImageModulePullback X i)

end RingedSpaceModuleAdjunction

namespace Stacks.Cohomology.SupportedComplexes

open RingedSpaceModuleAdjunction

/-- **Pullback of sheaves of modules along the inclusion of a closed subset is left exact.** -/
theorem preservesFiniteLimits_modulePullback_closedSubsetInclusion
    (X : AlgebraicGeometry.RingedSpace.{u, u}) (Z : Set X.carrier) :
    PreservesFiniteLimits (modulePullback (closedSubsetInclusion X Z)) :=
  preservesFiniteLimits_inverseImageModulePullback X
    (ClosedImmersionSheaves.closedSubsetInclusion Z)

/-- **The `pullbackExact` obligation of Tag 0AEF part (2), unconditionally.** Pullback of sheaves
of modules along the inclusion of a closed subset is an exact functor.

`IsClosed Z` is not used: the structure sheaf of `closedSubsetRingedSpace X Z` is the inverse
image `i⁻¹𝒪_X`, so `i^*` involves no base change for any subset at all. -/
theorem pullbackExact (X : AlgebraicGeometry.RingedSpace.{u, u}) (Z : Set X.carrier) :
    exactFunctor (_root_.SheafOfModules.{u} (structureSheafRing X))
      (_root_.SheafOfModules.{u} (structureSheafRing (closedSubsetRingedSpace X Z)))
      (modulePullback (closedSubsetInclusion X Z)) :=
  pullbackExact_of_preservesFiniteLimits X Z
    (preservesFiniteLimits_modulePullback_closedSubsetInclusion X Z)

end Stacks.Cohomology.SupportedComplexes

end
