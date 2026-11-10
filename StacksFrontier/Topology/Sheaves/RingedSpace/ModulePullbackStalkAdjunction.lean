module

public import StacksFrontier.Topology.Sheaves.RingedSpace.ModulePullbackStalk
public import StacksFrontier.Topology.Sheaves.Functors.Module.RingedSpace
public import StacksFrontier.Topology.Sheaves.Cohomology.KFlat.FlatModuleSheavesAndStalks

/-!
# The stalks of the adjunction-defined pullback of a sheaf of modules

Let `(f, f^\sharp) : (X, O_X) → (Y, O_Y)` be a morphism of ringed spaces and let `G` be a
sheaf of `O_Y`-modules.  For every `x : X` the stalk of the pullback `f^*G` is the base
change of the stalk of `G` along the induced map of local rings:

  `(f^*G)_x = G_{f(x)} ⊗_{O_{Y,f(x)}} O_{X,x}`

as `O_{X,x}`-modules, the tensor product being taken along
`f^\sharp_x : O_{Y,f(x)} → O_{X,x}`.

Here `f^*G` is the pullback *defined by the adjunction*
`modulePullbackPushforwardAdjunction`, rather than by the explicit tensor formula.

## Main definitions

* `RingedSpaceModuleAdjunction.moduleStalkSkyscraperHomEquiv`: taking the stalk at `x` is left
  adjoint to the skyscraper presheaf of modules at `x`.

## Main results

* `RingedSpaceModuleAdjunction.exists_modulePullbackStalkLinearEquiv`: the stalk formula,
  together with its canonical identification — the linear equivalence carries the germ of
  the adjunction unit applied to a section `s` to the pure tensor `1 ⊗ germ s`.

## Implementation notes

* The Stacks Project writes the formula with `=`; it is a canonical isomorphism, and we
  produce an `O_{X,x}`-linear equivalence.
* The existence statement bundles the equivalence with its characterisation on unit
  germs, so the characterisation concerns the same equivalence whose existence is
  asserted rather than an independently chosen one.
* The structure ring sits on the left of the tensor product, giving the usual left-factor
  module action, and the adjunction-defined pullback uses a single universe for spaces,
  rings and modules.
* The declarations making up the stalk/skyscraper adjunction are `public`:
  `stalkFunctor_map_germ_smul`, `moduleStalkMap`, `moduleStalkMap_germ`,
  `skyscraperUnderlyingIso`, `skyscraperUnderlyingIso_hom_app_leg`,
  `moduleSkyscraperMapFromStalk`, `moduleSkyscraperMapToStalk`,
  `moduleSkyscraperMapToStalk_underlying` and `moduleStalkSkyscraperHomEquiv`. The other
  intermediate constructions are `private`, since the formula itself is stated in terms of
  the pullback adjunction only.

## References

* [Stacks Project, Tag 0098](https://stacks.math.columbia.edu/tag/0098)
-/

@[expose] public section

open CategoryTheory TopologicalSpace Limits Opposite

namespace RingedSpaceModuleAdjunction

open AlgebraicGeometry

universe u

/-- The stalk map of a morphism of module presheaves is compatible with the action of the
germ of a ring section on the germ of a module section over the same open set. -/
theorem stalkFunctor_map_germ_smul {T : TopCat.{u}}
    (R : T.Presheaf CommRingCat.{u})
    {M N : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat.{u} RingCat.{u})}
    (φ : M ⟶ N) (x : T) (W : Opens T) (hW : x ∈ W)
    (a : R.obj (op W)) (b : M.obj (op W)) :
    ConcreteCategory.hom ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
        ((PresheafOfModules.toPresheaf _).map φ))
        (TopCat.Presheaf.germ R W x hW a • TopCat.Presheaf.germ M.presheaf W x hW b) =
      TopCat.Presheaf.germ R W x hW a •
        TopCat.Presheaf.germ N.presheaf W x hW (φ.app (op W) b) := by
  have eM : TopCat.Presheaf.germ M.presheaf W x hW (a • b) =
      TopCat.Presheaf.germ R W x hW a • TopCat.Presheaf.germ M.presheaf W x hW b :=
    PresheafOfModules.germ_smul (R := R) M x W hW a b
  have eStalk : ConcreteCategory.hom ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
        ((PresheafOfModules.toPresheaf _).map φ))
        (TopCat.Presheaf.germ M.presheaf W x hW (a • b)) =
      TopCat.Presheaf.germ N.presheaf W x hW (φ.app (op W) (a • b)) :=
    TopCat.Presheaf.stalkFunctor_map_germ_apply W x hW
      ((PresheafOfModules.toPresheaf _).map φ) (a • b)
  have eApp : φ.app (op W) (a • b) = a • φ.app (op W) b :=
    map_smul (φ.app (op W)).hom a b
  have eN : TopCat.Presheaf.germ N.presheaf W x hW (a • φ.app (op W) b) =
      TopCat.Presheaf.germ R W x hW a •
        TopCat.Presheaf.germ N.presheaf W x hW (φ.app (op W) b) :=
    PresheafOfModules.germ_smul (R := R) N x W hW a (φ.app (op W) b)
  rw [← eM, eStalk, eApp, eN]

/-- A morphism of module presheaves induces a linear map on stalks. -/
noncomputable def moduleStalkMap {T : TopCat.{u}}
    (R : T.Presheaf CommRingCat.{u})
    {M N : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat.{u} RingCat.{u})}
    (φ : M ⟶ N) (x : T) :
    (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) M.presheaf x)
      →ₗ[R.stalk x] (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) N.presheaf x) where
  toFun := (ConcreteCategory.hom ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
    ((PresheafOfModules.toPresheaf _).map φ)))
  map_add' a b := map_add _ a b
  map_smul' r m := by
    obtain ⟨U, hU, s, rfl⟩ := TopCat.Presheaf.exists_germ_eq M.presheaf m
    obtain ⟨V, hV, t, rfl⟩ := TopCat.Presheaf.exists_germ_eq R r
    simp only [RingHom.id_apply]
    set W : Opens T := U ⊓ V
    have hW : x ∈ W := ⟨hU, hV⟩
    let : Module (R.obj (op W)) (M.presheaf.obj (op W)) :=
      inferInstanceAs (Module ((R ⋙ forget₂ CommRingCat.{u} RingCat.{u}).obj (op W))
        (M.obj (op W)))
    set iU : W ⟶ U := homOfLE inf_le_left
    set iV : W ⟶ V := homOfLE inf_le_right
    rw [← TopCat.Presheaf.germ_res_apply M.presheaf iU x hW s,
      ← TopCat.Presheaf.germ_res_apply R iV x hW t]
    refine Eq.trans (stalkFunctor_map_germ_smul R φ x W hW (R.map iV.op t)
      (M.presheaf.map iU.op s)) ?_
    exact congrArg (fun z : TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) N.presheaf x =>
      TopCat.Presheaf.germ R W x hW (R.map iV.op t) • z)
      (TopCat.Presheaf.stalkFunctor_map_germ_apply W x hW
        ((PresheafOfModules.toPresheaf _).map φ) (M.presheaf.map iU.op s)).symm

/-- The stalk map of a module morphism acts on a germ by applying the
morphism to its section. -/
theorem moduleStalkMap_germ {T : TopCat.{u}}
    (R : T.Presheaf CommRingCat.{u})
    {M N : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat.{u} RingCat.{u})}
    (φ : M ⟶ N) (x : T) (U : Opens T) (hx : x ∈ U) (s : M.obj (op U)) :
    moduleStalkMap R φ x (TopCat.Presheaf.germ M.presheaf U x hx s) =
      TopCat.Presheaf.germ N.presheaf U x hx (φ.app (op U) s) :=
  TopCat.Presheaf.stalkFunctor_map_germ_apply U x hx
    ((PresheafOfModules.toPresheaf _).map φ) s

/-- An isomorphism of module sheaves induces a linear equivalence on stalks. -/
private noncomputable def moduleStalkEquivOfIso {T : TopCat.{u}}
    (R : T.Presheaf CommRingCat.{u})
    {M N : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat.{u} RingCat.{u})}
    (e : M ≅ N) (x : T) :
    (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) M.presheaf x)
      ≃ₗ[R.stalk x] (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) N.presheaf x) := by
  let e' := (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).mapIso
    ((PresheafOfModules.toPresheaf _).mapIso e)
  exact AddEquiv.toLinearEquiv e'.addCommGroupIsoToAddEquiv
    (fun c z => (moduleStalkMap R e.hom x).map_smul c z)

/-- Sheafification of module presheaves over the structure sheaf leaves stalks
linearly unchanged. -/
private noncomputable def sheafificationStalkEquiv {X : RingedSpace.{u, u}}
    (P : PresheafOfModules.{u} (X.presheaf ⋙ forget₂ CommRingCat RingCat)) (x : X) :
    let Q' : PresheafOfModules (X.presheaf ⋙ forget₂ CommRingCat RingCat) :=
      ((PresheafOfModules.sheafification (𝟙 (structureSheafRing X).obj)).obj P).val
    (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) P.presheaf x)
      ≃ₗ[X.presheaf.stalk x]
        (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) Q'.presheaf x) := by
  let η := (PresheafOfModules.sheafificationAdjunction (𝟙 (structureSheafRing X).obj)).unit.app P
  let L := moduleStalkMap X.presheaf η x
  have hiso : IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
      ((PresheafOfModules.toPresheaf _).map η)) := by
    change IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
      (CategoryTheory.toSheafify (Opens.grothendieckTopology X.carrier) P.presheaf))
    exact TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso x AddCommGrpCat.{u} _
  apply LinearEquiv.ofBijective L
  change Function.Bijective ⇑(ConcreteCategory.hom
    ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
      ((PresheafOfModules.toPresheaf _).map η)))
  exact CategoryTheory.ConcreteCategory.bijective_of_isIso _

/-- The sheafification stalk equivalence is the map induced by its unit. -/
private theorem sheafificationStalkEquiv_unit_germ {X : RingedSpace.{u, u}}
    (P : PresheafOfModules.{u} (X.presheaf ⋙ forget₂ CommRingCat RingCat))
    (x : X) (U : Opens X.carrier) (hx : x ∈ U) (s : P.obj (op U)) :
    let Q' : PresheafOfModules (X.presheaf ⋙ forget₂ CommRingCat RingCat) :=
      ((PresheafOfModules.sheafification (𝟙 (structureSheafRing X).obj)).obj P).val
    let η := (PresheafOfModules.sheafificationAdjunction (𝟙 (structureSheafRing X).obj)).unit.app P
    sheafificationStalkEquiv P x (TopCat.Presheaf.germ P.presheaf U x hx s) =
      TopCat.Presheaf.germ Q'.presheaf U x hx (η.app (op U) s) :=
  moduleStalkMap_germ X.presheaf
    ((PresheafOfModules.sheafificationAdjunction (𝟙 (structureSheafRing X).obj)).unit.app P)
    x U hx s

/-- Compare the adjunction-defined pullback with Mathlib's explicit construction:
presheaf pullback followed by sheafification. -/
private noncomputable def modulePullbackComparison {X Y : RingedSpace.{u, u}}
    (f : X ⟶ Y) (G : SheafOfModules.{u} (structureSheafRing Y)) :
    letI : (PresheafOfModules.pushforward (structureSheafHom f).hom).IsRightAdjoint :=
      PresheafOfModules.instIsRightAdjointPushforward _
    (modulePullback f).obj G ≅
      ((SheafOfModules.forget (structureSheafRing Y) ⋙
        PresheafOfModules.pullback (structureSheafHom f).hom ⋙
        PresheafOfModules.sheafification (R₀ := (structureSheafRing X).obj)
          (𝟙 (structureSheafRing X).obj)).obj G) := by
  letI : (PresheafOfModules.pushforward (structureSheafHom f).hom).IsRightAdjoint :=
    PresheafOfModules.instIsRightAdjointPushforward _
  letI : (SheafOfModules.pushforward (structureSheafHom f)).IsRightAdjoint :=
    modulePushforward_isRightAdjoint f
  exact (SheafOfModules.pullbackIso (structureSheafHom f)).app G

/-- The linear equivalence of stalks induced by `modulePullbackComparison`. -/
private noncomputable def modulePullbackComparison_stalk {X Y : RingedSpace.{u, u}}
    (f : X ⟶ Y) (G : SheafOfModules.{u} (structureSheafRing Y)) (x : X) :
    letI : (PresheafOfModules.pushforward (structureSheafHom f).hom).IsRightAdjoint :=
      PresheafOfModules.instIsRightAdjointPushforward _
    letI : Presheaf.IsLocallyInjective (Opens.grothendieckTopology X.carrier)
        (𝟙 (structureSheafRing X).obj) := inferInstance
    letI : Presheaf.IsLocallySurjective (Opens.grothendieckTopology X.carrier)
        (𝟙 (structureSheafRing X).obj) := inferInstance
    let P' : PresheafOfModules (X.presheaf ⋙ forget₂ CommRingCat RingCat) :=
      ((modulePullback f).obj G).val
    let Q' : PresheafOfModules (X.presheaf ⋙ forget₂ CommRingCat RingCat) :=
      ((SheafOfModules.forget (structureSheafRing Y) ⋙
      PresheafOfModules.pullback (structureSheafHom f).hom ⋙
      PresheafOfModules.sheafification (𝟙 (structureSheafRing X).obj)).obj G).val
    (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) P'.presheaf x)
      ≃ₗ[X.presheaf.stalk x]
        (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) Q'.presheaf x) := by
  letI : (PresheafOfModules.pushforward (structureSheafHom f).hom).IsRightAdjoint :=
    PresheafOfModules.instIsRightAdjointPushforward _
  letI : Presheaf.IsLocallyInjective (Opens.grothendieckTopology X.carrier)
      (𝟙 (structureSheafRing X).obj) := inferInstance
  letI : Presheaf.IsLocallySurjective (Opens.grothendieckTopology X.carrier)
      (𝟙 (structureSheafRing X).obj) := inferInstance
  exact moduleStalkEquivOfIso X.presheaf
    ((SheafOfModules.forget (structureSheafRing X)).mapIso (modulePullbackComparison f G)) x

/-- The comparison takes the abstract adjunction unit to the unit of the
presheaf-pullback/sheafification construction. -/
private theorem modulePullbackComparison_unit {X Y : RingedSpace.{u, u}}
    (f : X ⟶ Y) (G : SheafOfModules.{u} (structureSheafRing Y)) :
    letI : (PresheafOfModules.pushforward (structureSheafHom f).hom).IsRightAdjoint :=
      PresheafOfModules.instIsRightAdjointPushforward _
    (modulePullbackPushforwardAdjunction f).unit.app G ≫
        (modulePushforward f).map (modulePullbackComparison f G).hom =
      (SheafOfModules.PullbackConstruction.adjunction (structureSheafHom f)).unit.app G := by
  let : (PresheafOfModules.pushforward (structureSheafHom f).hom).IsRightAdjoint :=
    PresheafOfModules.instIsRightAdjointPushforward _
  let : (SheafOfModules.pushforward (structureSheafHom f)).IsRightAdjoint :=
    modulePushforward_isRightAdjoint f
  exact Adjunction.unit_leftAdjointUniq_hom_app
    (SheafOfModules.pullbackPushforwardAdjunction (structureSheafHom f))
    (SheafOfModules.PullbackConstruction.adjunction (structureSheafHom f)) G

/-- On sections, the construction unit is the presheaf pullback unit followed by
the sheafification unit. -/
private theorem construction_unit_app {X Y : RingedSpace.{u, u}}
    (f : X ⟶ Y) (G : SheafOfModules.{u} (structureSheafRing Y))
    (V : Opens Y.carrier) (s : G.val.obj (op V)) :
    letI : (PresheafOfModules.pushforward (structureSheafHom f).hom).IsRightAdjoint :=
      PresheafOfModules.instIsRightAdjointPushforward _
    (((SheafOfModules.PullbackConstruction.adjunction (structureSheafHom f)).unit.app G).val.app
      (op V)) s =
    ((PresheafOfModules.sheafificationAdjunction (𝟙 (structureSheafRing X).obj)).unit.app
      ((PresheafOfModules.pullback (structureSheafHom f).hom).obj G.val)).app
        (op ((opensMap f).obj V))
      (((PresheafOfModules.pullbackPushforwardAdjunction (structureSheafHom f).hom).unit.app
        G.val).app (op V) s) := by
  let : (PresheafOfModules.pushforward (structureSheafHom f).hom).IsRightAdjoint :=
    PresheafOfModules.instIsRightAdjointPushforward _
  rfl

/-- The comparison sends each unit section to the sheafification of the
presheaf-pullback unit section. -/
private theorem modulePullbackComparison_unit_app {X Y : RingedSpace.{u, u}}
    (f : X ⟶ Y) (G : SheafOfModules.{u} (structureSheafRing Y))
    (V : Opens Y.carrier) (s : G.val.obj (op V)) :
    letI : (PresheafOfModules.pushforward (structureSheafHom f).hom).IsRightAdjoint :=
      PresheafOfModules.instIsRightAdjointPushforward _
    ((modulePullbackComparison f G).hom.val.app (op ((opensMap f).obj V)))
      (((modulePullbackPushforwardAdjunction f).unit.app G).val.app (op V) s) =
    ((PresheafOfModules.sheafificationAdjunction (𝟙 (structureSheafRing X).obj)).unit.app
      ((PresheafOfModules.pullback (structureSheafHom f).hom).obj G.val)).app
        (op ((opensMap f).obj V))
      (((PresheafOfModules.pullbackPushforwardAdjunction (structureSheafHom f).hom).unit.app
        G.val).app (op V) s) := by
  let : (PresheafOfModules.pushforward (structureSheafHom f).hom).IsRightAdjoint :=
    PresheafOfModules.instIsRightAdjointPushforward _
  rw [← construction_unit_app f G V s]
  have h := modulePullbackComparison_unit f G
  have h' := congrArg (fun q => q.val.app (op V) s) h
  exact h'

/-- The stalk comparison takes unit germs to the germs of the two construction
units. -/
private theorem modulePullbackComparison_unit_germ {X Y : RingedSpace.{u, u}}
    (f : X ⟶ Y) (G : SheafOfModules.{u} (structureSheafRing Y)) (x : X)
    (V : Opens Y.carrier) (hx : f.hom.base x ∈ V) (s : G.val.obj (op V)) :
    letI : (PresheafOfModules.pushforward (structureSheafHom f).hom).IsRightAdjoint :=
      PresheafOfModules.instIsRightAdjointPushforward _
    letI : Presheaf.IsLocallyInjective (Opens.grothendieckTopology X.carrier)
        (𝟙 (structureSheafRing X).obj) := inferInstance
    letI : Presheaf.IsLocallySurjective (Opens.grothendieckTopology X.carrier)
        (𝟙 (structureSheafRing X).obj) := inferInstance
    let P' : PresheafOfModules (X.presheaf ⋙ forget₂ CommRingCat RingCat) :=
      ((modulePullback f).obj G).val
    let M : PresheafOfModules (X.presheaf ⋙ forget₂ CommRingCat RingCat) :=
      (PresheafOfModules.pullback (structureSheafHom f).hom).obj G.val
    let Q' : PresheafOfModules (X.presheaf ⋙ forget₂ CommRingCat RingCat) :=
      ((PresheafOfModules.sheafification (𝟙 (structureSheafRing X).obj)).obj M).val
    let η := (PresheafOfModules.sheafificationAdjunction (𝟙 (structureSheafRing X).obj)).unit.app M
    (modulePullbackComparison_stalk f G x)
      (TopCat.Presheaf.germ P'.presheaf ((opensMap f).obj V) x hx
        (((modulePullbackPushforwardAdjunction f).unit.app G).val.app (op V) s)) =
      TopCat.Presheaf.germ Q'.presheaf ((opensMap f).obj V) x hx
        (η.app (op ((opensMap f).obj V))
          (((PresheafOfModules.pullbackPushforwardAdjunction
            (structureSheafHom f).hom).unit.app G.val).app (op V) s)) := by
  let : (PresheafOfModules.pushforward (structureSheafHom f).hom).IsRightAdjoint :=
    PresheafOfModules.instIsRightAdjointPushforward _
  let : Presheaf.IsLocallyInjective (Opens.grothendieckTopology X.carrier)
      (𝟙 (structureSheafRing X).obj) := inferInstance
  let : Presheaf.IsLocallySurjective (Opens.grothendieckTopology X.carrier)
      (𝟙 (structureSheafRing X).obj) := inferInstance
  change (ConcreteCategory.hom ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
      ((PresheafOfModules.toPresheaf _).map (modulePullbackComparison f G).hom.val)))
    (TopCat.Presheaf.germ ((modulePullback f).obj G).val.presheaf
      ((opensMap f).obj V) x hx
      (((modulePullbackPushforwardAdjunction f).unit.app G).val.app (op V) s)) = _
  refine Eq.trans (TopCat.Presheaf.stalkFunctor_map_germ_apply ((opensMap f).obj V) x hx
    ((PresheafOfModules.toPresheaf _).map (modulePullbackComparison f G).hom.val)
    (((modulePullbackPushforwardAdjunction f).unit.app G).val.app (op V) s)) ?_
  congr 1
  exact modulePullbackComparison_unit_app f G V s

/-- The map on underlying stalks induced by the presheaf pullback unit. -/
private noncomputable def presheafPullbackUnitStalkMap
    {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
    (G : SheafOfModules.{u} (structureSheafRing Y)) (x : X) :
    letI : (PresheafOfModules.pushforward (structureSheafHom f).hom).IsRightAdjoint :=
      PresheafOfModules.instIsRightAdjointPushforward _
    let M : PresheafOfModules (X.presheaf ⋙ forget₂ CommRingCat RingCat) :=
      (PresheafOfModules.pullback (structureSheafHom f).hom).obj G.val
    ↑(TopCat.Presheaf.stalk G.val.presheaf (f.hom.base x)) →+
      ↑(TopCat.Presheaf.stalk M.presheaf x) := by
  letI : (PresheafOfModules.pushforward (structureSheafHom f).hom).IsRightAdjoint :=
    PresheafOfModules.instIsRightAdjointPushforward _
  let M : PresheafOfModules (X.presheaf ⋙ forget₂ CommRingCat RingCat) :=
    (PresheafOfModules.pullback (structureSheafHom f).hom).obj G.val
  let η := (PresheafOfModules.pullbackPushforwardAdjunction
      (structureSheafHom f).hom).unit.app G.val
  exact (TopCat.Presheaf.stalkPushforward AddCommGrpCat.{u} f.hom.base M.presheaf x).hom.comp
    (((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (f.hom.base x)).map
      ((PresheafOfModules.toPresheaf _).map η)).hom)

/-- The map induced by the presheaf pullback unit on a germ. -/
private theorem presheafPullbackUnitStalkMap_germ
    {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
    (G : SheafOfModules.{u} (structureSheafRing Y)) (x : X)
    (V : Opens Y.carrier) (hx : f.hom.base x ∈ V) (s : G.val.obj (op V)) :
    letI : (PresheafOfModules.pushforward (structureSheafHom f).hom).IsRightAdjoint :=
      PresheafOfModules.instIsRightAdjointPushforward _
    let M : PresheafOfModules (X.presheaf ⋙ forget₂ CommRingCat RingCat) :=
      (PresheafOfModules.pullback (structureSheafHom f).hom).obj G.val
    presheafPullbackUnitStalkMap f G x
      (TopCat.Presheaf.germ G.val.presheaf V (f.hom.base x) hx s) =
      TopCat.Presheaf.germ M.presheaf ((opensMap f).obj V) x hx
        (((PresheafOfModules.pullbackPushforwardAdjunction
          (structureSheafHom f).hom).unit.app G.val).app (op V) s) := by
  let : (PresheafOfModules.pushforward (structureSheafHom f).hom).IsRightAdjoint :=
    PresheafOfModules.instIsRightAdjointPushforward _
  let M : PresheafOfModules (X.presheaf ⋙ forget₂ CommRingCat RingCat) :=
    (PresheafOfModules.pullback (structureSheafHom f).hom).obj G.val
  let η := (PresheafOfModules.pullbackPushforwardAdjunction
      (structureSheafHom f).hom).unit.app G.val
  change (TopCat.Presheaf.stalkPushforward AddCommGrpCat.{u} f.hom.base M.presheaf x)
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (f.hom.base x)).map
        ((PresheafOfModules.toPresheaf _).map η)
          (TopCat.Presheaf.germ G.val.presheaf V (f.hom.base x) hx s)) = _
  refine Eq.trans (congrArg (fun z : TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
      ((PresheafOfModules.pushforward (structureSheafHom f).hom).obj M).presheaf
      (f.hom.base x) =>
    ConcreteCategory.hom (TopCat.Presheaf.stalkPushforward AddCommGrpCat.{u} f.hom.base
      M.presheaf x) z)
    (TopCat.Presheaf.stalkFunctor_map_germ_apply V (f.hom.base x) hx
      ((PresheafOfModules.toPresheaf _).map η) s)) ?_
  exact TopCat.Presheaf.stalkPushforward_germ_apply AddCommGrpCat.{u}
    f.hom.base M.presheaf V x hx
    (η.app (op V) s)

/-- The pullback unit is semilinear on stalks along the structure map. -/
private noncomputable def presheafPullbackUnitStalkSemilinear
    {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
    (G : SheafOfModules.{u} (structureSheafRing Y)) (x : X) :
    letI : (PresheafOfModules.pushforward (structureSheafHom f).hom).IsRightAdjoint :=
      PresheafOfModules.instIsRightAdjointPushforward _
    let G' : PresheafOfModules (Y.presheaf ⋙ forget₂ CommRingCat RingCat) := G.val
    let M : PresheafOfModules (X.presheaf ⋙ forget₂ CommRingCat RingCat) :=
      (PresheafOfModules.pullback (structureSheafHom f).hom).obj G.val
    ↑(TopCat.Presheaf.stalk G'.presheaf (f.hom.base x)) →ₛₗ[(f.hom.stalkMap x).hom]
      ↑(TopCat.Presheaf.stalk M.presheaf x) := by
  letI : (PresheafOfModules.pushforward (structureSheafHom f).hom).IsRightAdjoint :=
    PresheafOfModules.instIsRightAdjointPushforward _
  let G' : PresheafOfModules (Y.presheaf ⋙ forget₂ CommRingCat RingCat) := G.val
  let M : PresheafOfModules (X.presheaf ⋙ forget₂ CommRingCat RingCat) :=
    (PresheafOfModules.pullback (structureSheafHom f).hom).obj G.val
  letI : Module (Y.presheaf.stalk (f.hom.base x))
      ↑(TopCat.Presheaf.stalk G'.presheaf (f.hom.base x)) := inferInstance
  letI : Module (X.presheaf.stalk x)
      ↑(TopCat.Presheaf.stalk M.presheaf x) := inferInstance
  let η := (PresheafOfModules.pullbackPushforwardAdjunction
      (structureSheafHom f).hom).unit.app G.val
  refine { presheafPullbackUnitStalkMap f G x with map_smul' := ?_ }
  intro r m
  obtain ⟨U, hU, s, hs⟩ := TopCat.Presheaf.exists_germ_eq G.val.presheaf m
  obtain ⟨V, hV, a, hr⟩ := TopCat.Presheaf.exists_germ_eq Y.presheaf r
  rw [← hs, ← hr]
  set W : Opens Y.carrier := U ⊓ V
  have hW : f.hom.base x ∈ W := ⟨hU, hV⟩
  let iU : W ⟶ U := homOfLE inf_le_left
  let iV : W ⟶ V := homOfLE inf_le_right
  let G' : PresheafOfModules (Y.presheaf ⋙ forget₂ CommRingCat RingCat) := G.val
  let : Module (Y.presheaf.obj (op W)) (G'.presheaf.obj (op W)) :=
    inferInstanceAs (Module ((Y.presheaf ⋙ forget₂ CommRingCat RingCat).obj (op W))
      (G'.obj (op W)))
  rw [← TopCat.Presheaf.germ_res_apply G.val.presheaf iU (f.hom.base x) hW s,
    ← TopCat.Presheaf.germ_res_apply Y.presheaf iV (f.hom.base x) hW a]
  refine Eq.trans (congrArg
    (fun z : ↑(TopCat.Presheaf.stalk G'.presheaf (f.hom.base x)) =>
      presheafPullbackUnitStalkMap f G x z)
    (PresheafOfModules.germ_smul (R := Y.presheaf) G' (f.hom.base x) W hW
      (Y.presheaf.map iV.op a) (G'.presheaf.map iU.op s)).symm) ?_
  have hsmul := (η.app (op W)).hom.map_smul
    (Y.presheaf.map iV.op a) (G'.presheaf.map iU.op s)
  have hgerm := PresheafOfModules.germ_smul (R := X.presheaf) M x ((opensMap f).obj W) hW
    (f.hom.c.app (op W) (Y.presheaf.map iV.op a))
    ((η.app (op W)).hom (G'.presheaf.map iU.op s))
  refine Eq.trans (presheafPullbackUnitStalkMap_germ f G x W hW
    ((Y.presheaf.map iV.op a) • (G'.presheaf.map iU.op s))) ?_
  refine Eq.trans (congrArg
    (fun z : ToType (M.presheaf.obj (op ((opensMap f).obj W))) =>
      TopCat.Presheaf.germ M.presheaf ((opensMap f).obj W) x hW z) hsmul) ?_
  refine Eq.trans hgerm ?_
  refine Eq.trans (congrArg
    (fun z : ↑(X.presheaf.stalk x) =>
      z • TopCat.Presheaf.germ M.presheaf ((opensMap f).obj W) x hW
        ((η.app (op W)).hom (G'.presheaf.map iU.op s)))
    (PresheafedSpace.stalkMap_germ_apply f.hom W x hW (Y.presheaf.map iV.op a)).symm) ?_
  exact congrArg
    (fun z : ↑(TopCat.Presheaf.stalk M.presheaf x) =>
      (f.hom.stalkMap x).hom
        (Y.presheaf.germ W (f.hom.base x) hW (Y.presheaf.map iV.op a)) • z)
    (presheafPullbackUnitStalkMap_germ f G x W hW (G'.presheaf.map iU.op s)).symm

/-- The canonical extension-of-scalars map into the presheaf pullback stalk. -/
private noncomputable def presheafPullbackTensorToStalk
    {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
    (G : SheafOfModules.{u} (structureSheafRing Y)) (x : X) :
    letI : (PresheafOfModules.pushforward (structureSheafHom f).hom).IsRightAdjoint :=
      PresheafOfModules.instIsRightAdjointPushforward _
    let G' : PresheafOfModules (Y.presheaf ⋙ forget₂ CommRingCat RingCat) := G.val
    let M : PresheafOfModules (X.presheaf ⋙ forget₂ CommRingCat RingCat) :=
      (PresheafOfModules.pullback (structureSheafHom f).hom).obj G.val
    letI : Algebra (Y.presheaf.stalk (f.hom.base x)) (X.presheaf.stalk x) :=
      (f.hom.stalkMap x).hom.toAlgebra
    TensorProduct (Y.presheaf.stalk (f.hom.base x)) (X.presheaf.stalk x)
        ↑(TopCat.Presheaf.stalk G'.presheaf (f.hom.base x))
      →ₗ[X.presheaf.stalk x] ↑(TopCat.Presheaf.stalk M.presheaf x) := by
  letI : (PresheafOfModules.pushforward (structureSheafHom f).hom).IsRightAdjoint :=
    PresheafOfModules.instIsRightAdjointPushforward _
  let G' : PresheafOfModules (Y.presheaf ⋙ forget₂ CommRingCat RingCat) := G.val
  let M : PresheafOfModules (X.presheaf ⋙ forget₂ CommRingCat RingCat) :=
    (PresheafOfModules.pullback (structureSheafHom f).hom).obj G.val
  letI : Algebra (Y.presheaf.stalk (f.hom.base x)) (X.presheaf.stalk x) :=
    (f.hom.stalkMap x).hom.toAlgebra
  letI : Module (Y.presheaf.stalk (f.hom.base x))
      ↑(TopCat.Presheaf.stalk G'.presheaf (f.hom.base x)) := inferInstance
  letI : Module (X.presheaf.stalk x) ↑(TopCat.Presheaf.stalk M.presheaf x) := inferInstance
  letI : Module (X.presheaf.stalk x)
      ↑(TopCat.Presheaf.stalk
        ((PresheafOfModules.pullback (structureSheafHom f).hom).obj G.val).presheaf x) :=
    inferInstanceAs (Module (X.presheaf.stalk x)
      ↑(TopCat.Presheaf.stalk M.presheaf x))
  letI : Module (Y.presheaf.stalk (f.hom.base x))
      ↑(TopCat.Presheaf.stalk M.presheaf x) :=
    Module.compHom _ (f.hom.stalkMap x).hom
  letI : IsScalarTower (Y.presheaf.stalk (f.hom.base x)) (X.presheaf.stalk x)
      ↑(TopCat.Presheaf.stalk M.presheaf x) := IsScalarTower.of_compHom _ _ _
  letI : SMulCommClass (Y.presheaf.stalk (f.hom.base x)) (X.presheaf.stalk x)
      ↑(TopCat.Presheaf.stalk M.presheaf x) :=
    ⟨fun a b z => by change ((f.hom.stalkMap x).hom a) • b • z =
      b • ((f.hom.stalkMap x).hom a) • z; exact smul_comm _ _ _⟩
  let j := presheafPullbackUnitStalkSemilinear f G x
  let b : (X.presheaf.stalk x) →ₗ[X.presheaf.stalk x]
      ↑(TopCat.Presheaf.stalk G'.presheaf (f.hom.base x)) →ₗ[Y.presheaf.stalk (f.hom.base x)]
        ↑(TopCat.Presheaf.stalk M.presheaf x) :=
    { toFun := fun a =>
        { toFun := fun m => a • j m
          map_add' := by intro m n; simp [map_add, smul_add]
          map_smul' := by
            intro r m
            change a • j (r • m) = r • a • j m
            have hj : j (r • m) = (f.hom.stalkMap x).hom r • j m :=
              j.map_smulₛₗ r m
            rw [hj]
            exact smul_comm _ _ _ }
      map_add' := by intro a b; ext m; simp [add_smul]
      map_smul' := by intro a b; ext m; simp [mul_smul] }
  exact TensorProduct.AlgebraTensorModule.lift (P := ↑(TopCat.Presheaf.stalk M.presheaf x)) b

/-- The extension-of-scalars map sends a pure tensor of a germ to the unit germ. -/
private theorem presheafPullbackTensorToStalk_one_tmul
    {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
    (G : SheafOfModules.{u} (structureSheafRing Y)) (x : X)
    (V : Opens Y.carrier) (hx : f.hom.base x ∈ V) (s : G.val.obj (op V)) :
    letI : (PresheafOfModules.pushforward (structureSheafHom f).hom).IsRightAdjoint :=
      PresheafOfModules.instIsRightAdjointPushforward _
    let G' : PresheafOfModules (Y.presheaf ⋙ forget₂ CommRingCat RingCat) := G.val
    let M : PresheafOfModules (X.presheaf ⋙ forget₂ CommRingCat RingCat) :=
      (PresheafOfModules.pullback (structureSheafHom f).hom).obj G.val
    letI : Algebra (Y.presheaf.stalk (f.hom.base x)) (X.presheaf.stalk x) :=
      (f.hom.stalkMap x).hom.toAlgebra
    letI : Module (Y.presheaf.stalk (f.hom.base x))
        ↑(TopCat.Presheaf.stalk G'.presheaf (f.hom.base x)) := inferInstance
    letI : Module (X.presheaf.stalk x)
        ↑(TopCat.Presheaf.stalk M.presheaf x) := inferInstance
    presheafPullbackTensorToStalk f G x
      ((1 : X.presheaf.stalk x) ⊗ₜ[Y.presheaf.stalk (f.hom.base x)]
        TopCat.Presheaf.germ G'.presheaf V (f.hom.base x) hx s) =
      TopCat.Presheaf.germ M.presheaf ((opensMap f).obj V) x hx
        (((PresheafOfModules.pullbackPushforwardAdjunction
          (structureSheafHom f).hom).unit.app G.val).app (op V) s) := by
  let : (PresheafOfModules.pushforward (structureSheafHom f).hom).IsRightAdjoint :=
    PresheafOfModules.instIsRightAdjointPushforward _
  let G' : PresheafOfModules (Y.presheaf ⋙ forget₂ CommRingCat RingCat) := G.val
  let M : PresheafOfModules (X.presheaf ⋙ forget₂ CommRingCat RingCat) :=
    (PresheafOfModules.pullback (structureSheafHom f).hom).obj G.val
  let : Algebra (Y.presheaf.stalk (f.hom.base x)) (X.presheaf.stalk x) :=
    (f.hom.stalkMap x).hom.toAlgebra
  let : Module (X.presheaf.stalk x) ↑(TopCat.Presheaf.stalk M.presheaf x) := inferInstance
  let : Module (Y.presheaf.stalk (f.hom.base x))
      ↑(TopCat.Presheaf.stalk G'.presheaf (f.hom.base x)) := inferInstance
  let : Module (Y.presheaf.stalk (f.hom.base x))
      ↑(TopCat.Presheaf.stalk M.presheaf x) :=
    Module.compHom _ (f.hom.stalkMap x).hom
  let : IsScalarTower (Y.presheaf.stalk (f.hom.base x)) (X.presheaf.stalk x)
      ↑(TopCat.Presheaf.stalk M.presheaf x) := IsScalarTower.of_compHom _ _ _
  exact (one_smul (X.presheaf.stalk x)
    (presheafPullbackUnitStalkSemilinear f G x
      (TopCat.Presheaf.germ G'.presheaf V (f.hom.base x) hx s))).trans
    (presheafPullbackUnitStalkMap_germ f G x V hx s)

/-! ### The skyscraper presheaf of modules is right adjoint to the stalk -/

/-- Membership of the point `x` in an open set, made decidable by classical choice. -/
noncomputable local instance skyscraperMembershipDecidable
    (X : RingedSpace.{u, u}) (x : X) :
    ∀ U : Opens X.carrier, Decidable (x ∈ U) := fun _ => Classical.propDecidable _

/-- The underlying presheaf of abelian groups of the skyscraper presheaf of `O_X`-modules at
`x` with value `N` is Mathlib's skyscraper presheaf on the underlying group of `N`: over an
open set containing `x` both are `N`, and over any other open set both are terminal. -/
noncomputable def skyscraperUnderlyingIso (X : RingedSpace.{u, u}) (x : X)
    [∀ U : Opens X.carrier, Decidable (x ∈ U)]
    (N : ModuleCat.{u} (X.presheaf.stalk x)) :
    (OXModule.skyscraperPOM x N).presheaf ≅
      skyscraperPresheaf x
        ((forget₂ (ModuleCat (X.presheaf.stalk x)) AddCommGrpCat).obj N) := by
  classical
  refine NatIso.ofComponents (fun U => ?_) ?_
  · by_cases hx : x ∈ U.unop
    · have hp := OXModule.skyscraperPOM_presheaf_obj_eq x N U hx
      have hq : (skyscraperPresheaf x
          ((forget₂ (ModuleCat _) AddCommGrpCat).obj N)).obj U = AddCommGrpCat.of (↑N) := by
        simp [skyscraperPresheaf, hx]
      exact eqToIso (hp.trans hq.symm)
    · have hP : IsTerminal ((OXModule.skyscraperPOM x N).presheaf.obj U) := by
        change IsTerminal ((forget₂ (ModuleCat _) AddCommGrpCat).obj
          (OXModule.skyscraperObj x N U))
        rw [OXModule.skyscraperObj, dite_eq_right hx]
        change IsTerminal (AddCommGrpCat.of PUnit)
        letI : ∀ Y : AddCommGrpCat, Unique (Y ⟶ AddCommGrpCat.of PUnit) := fun Y =>
          { default := AddCommGrpCat.ofHom (0 : (↑Y) →+ PUnit)
            uniq := fun f => by ext y }
        exact IsTerminal.ofUnique _
      have hQ : IsTerminal ((skyscraperPresheaf x
          ((forget₂ (ModuleCat _) AddCommGrpCat).obj N)).obj U) := by
        simpa [skyscraperPresheaf, hx] using
          (terminalIsTerminal (C := AddCommGrpCat))
      exact hP.uniqueUpToIso hQ
  · intro U V i
    by_cases hxV : x ∈ V.unop
    · have hxU : x ∈ U.unop := (leOfHom i.unop) hxV
      simp only [dite_eq_left hxV, dite_eq_left hxU]
      rw [OXModule.skyscraperPOM_presheaf_map_eq x N i hxV]
      simp only [ModuleCat.forget₂_obj, eqToHom_trans, eqToIso.hom, skyscraperPresheaf_map,
        dite_eq_left hxV]
      exact (eqToHom_trans _ _).symm
    · have hQ : IsTerminal ((skyscraperPresheaf x
          ((forget₂ (ModuleCat _) AddCommGrpCat).obj N)).obj V) := by
        simpa [skyscraperPresheaf, hxV] using
          (terminalIsTerminal (C := AddCommGrpCat))
      simp only [dite_eq_right hxV]
      apply hQ.hom_ext

/-- Over an open containing `x`, the comparison with Mathlib's skyscraper presheaf followed
by the identification of the skyscraper value with `N` is the canonical identification of the
value of the skyscraper presheaf of modules with `N`. -/
theorem skyscraperUnderlyingIso_hom_app_leg (X : RingedSpace.{u, u}) (x : X)
    (N : ModuleCat.{u} (X.presheaf.stalk x)) (U : (Opens X.carrier)ᵒᵖ) (hx : x ∈ U.unop) :
    (skyscraperUnderlyingIso X x N).hom.app U ≫ eqToHom (ite_eq_left hx) =
      eqToHom (OXModule.skyscraperPOM_presheaf_obj_eq x N U hx) := by
  classical
  simp only [ModuleCat.forget₂_obj, skyscraperUnderlyingIso, Functor.comp_obj,
    CommRingCat.forgetToRingCat_obj, op_unop, id_eq, eq_mpr_eq_cast, cast_cast,
    NatIso.ofComponents_hom_app, hx, ↓reduceDIte, eqToIso.hom]
  exact eqToHom_trans _ _

/-- The morphism of presheaves of modules `P ⟶ skyscraperPOM x N` corresponding under the
stalk/skyscraper adjunction to an `O_{X,x}`-linear map out of the stalk of `P` at `x`: over an
open set containing `x` it is the given map precomposed with the germ. -/
noncomputable def moduleSkyscraperMapFromStalk (X : RingedSpace.{u, u}) (x : X)
    (P : PresheafOfModules.{u} (X.presheaf ⋙ forget₂ CommRingCat RingCat))
    (N : ModuleCat.{u} (X.presheaf.stalk x))
    (g : ModuleCat.of (X.presheaf.stalk x)
      ↑(TopCat.Presheaf.stalk P.presheaf x) ⟶ N) :
    P ⟶ OXModule.skyscraperPOM x N := by
  classical
  let gA := (forget₂ (ModuleCat (X.presheaf.stalk x)) AddCommGrpCat).map g
  let psh := StalkSkyscraperPresheafAdjunctionAuxs.toSkyscraperPresheaf x gA ≫
    (skyscraperUnderlyingIso X x N).inv
  refine PresheafOfModules.homMk psh ?_
  intro U r m
  let : Module ((X.presheaf ⋙ forget₂ CommRingCat RingCat).obj U)
      ((OXModule.skyscraperPOM x N).presheaf.obj U) :=
    inferInstanceAs (Module ((OXModule.ringSheaf X).obj.obj U)
      ((OXModule.skyscraperPOM x N).obj U))
  by_cases hx : x ∈ U.unop
  · let e := eqToHom (OXModule.skyscraperPOM_presheaf_obj_eq x N U hx)
    have hhom : (skyscraperUnderlyingIso X x N).hom.app U ≫ eqToHom (ite_eq_left hx) = e :=
      skyscraperUnderlyingIso_hom_app_leg X x N U hx
    have hinv : (skyscraperUnderlyingIso X x N).inv.app U ≫ e = eqToHom (ite_eq_left hx) := by
      rw [← hhom, ← Category.assoc, ← NatTrans.comp_app, Iso.inv_hom_id, NatTrans.id_app,
        Category.id_comp]
      rfl
    have hcat : psh.app U ≫ e =
        TopCat.Presheaf.germ P.presheaf U.unop x hx ≫ gA := by
      change (StalkSkyscraperPresheafAdjunctionAuxs.toSkyscraperPresheaf x gA).app U ≫
        (skyscraperUnderlyingIso X x N).inv.app U ≫ e = _
      rw [hinv]
      refine (StalkSkyscraperPresheafAdjunctionAuxs.germ_fromStalk x
        (StalkSkyscraperPresheafAdjunctionAuxs.toSkyscraperPresheaf x gA)
        U.unop hx).symm.trans ?_
      exact congrArg (fun z : TopCat.Presheaf.stalk P.presheaf x ⟶
          (forget₂ (ModuleCat (X.presheaf.stalk x)) AddCommGrpCat).obj N =>
        TopCat.Presheaf.germ P.presheaf U.unop x hx ≫ z)
        (StalkSkyscraperPresheafAdjunctionAuxs.fromStalk_to_skyscraper x gA)
    have he (m : P.obj U) : e ((psh.app U) m) =
        g.hom (TopCat.Presheaf.germ P.presheaf U.unop x hx m) :=
      ConcreteCategory.congr_hom hcat m
    apply (ConcreteCategory.bijective_of_isIso e).injective
    change e ((psh.app U) (r • m)) = e (r • (psh.app U) m)
    have h1 : e ((psh.app U) (r • m)) =
        (ConcreteCategory.hom (X.presheaf.germ U.unop x hx)) r •
          g.hom (TopCat.Presheaf.germ P.presheaf U.unop x hx m) :=
      (he (r • m)).trans
        ((congrArg (fun z : ↑(TopCat.Presheaf.stalk P.presheaf x) => g.hom z)
          (PresheafOfModules.germ_smul (R := X.presheaf) P x U.unop hx r m)).trans
          (map_smul g.hom _ _))
    have h2 : e (r • (psh.app U) m) =
        (ConcreteCategory.hom (X.presheaf.germ U.unop x hx)) r •
          g.hom (TopCat.Presheaf.germ P.presheaf U.unop x hx m) :=
      (OXModule.skyscraperPOM_leg_smul x N U hx r ((psh.app U) m)).trans
        (congrArg (fun z : (↑N : Type u) =>
          (ConcreteCategory.hom (X.presheaf.germ U.unop x hx)) r • z) (he m))
    exact h1.trans h2.symm
  · have : Subsingleton (↑(OXModule.skyscraperObj x N U)) := by
      rw [OXModule.skyscraperObj, dite_eq_right hx]
      infer_instance
    exact this.elim _ _

/-- The `O_{X,x}`-linear map out of the stalk of `P` at `x` corresponding under the
stalk/skyscraper adjunction to a morphism of presheaves of modules `P ⟶ skyscraperPOM x N`:
the induced map of stalks, followed by the identification of the skyscraper's stalk with `N`.
-/
noncomputable def moduleSkyscraperMapToStalk (X : RingedSpace.{u, u}) (x : X)
    (P : PresheafOfModules.{u} (X.presheaf ⋙ forget₂ CommRingCat RingCat))
    (N : ModuleCat.{u} (X.presheaf.stalk x))
    (g : P ⟶ OXModule.skyscraperPOM x N) :
    ModuleCat.of (X.presheaf.stalk x)
      ↑(TopCat.Presheaf.stalk P.presheaf x) ⟶ N :=
  ModuleCat.ofHom
    ((OXModule.sheafify_skyscraperPOM_stalkIso_skyscraper x N).hom.hom.comp
      (moduleStalkMap X.presheaf g x))

/-- The stalk map of a morphism into a skyscraper, followed by the identification of the
skyscraper's stalk with `N`, sends a germ to the image of its section. -/
private theorem skyscraper_stalkIso_moduleStalkMap_germ (X : RingedSpace.{u, u}) (x : X)
    (P : PresheafOfModules.{u} (X.presheaf ⋙ forget₂ CommRingCat RingCat))
    (N : ModuleCat.{u} (X.presheaf.stalk x)) (g : P ⟶ OXModule.skyscraperPOM x N)
    (U : Opens X.carrier) (hx : x ∈ U) (m : P.obj (op U)) :
    OXModule.sheafify_skyscraperPOM_stalkIso_skyscraper_addEquiv x N
      (moduleStalkMap X.presheaf g x (TopCat.Presheaf.germ P.presheaf U x hx m)) =
    ConcreteCategory.hom (eqToHom (OXModule.skyscraperPOM_presheaf_obj_eq x N (op U) hx))
      (g.app (op U) m) := by
  exact (congrArg (OXModule.sheafify_skyscraperPOM_stalkIso_skyscraper_addEquiv x N)
    (moduleStalkMap_germ X.presheaf g x U hx m)).trans
    (OXModule.sheafify_skyscraperPOM_stalkIso_skyscraper_addEquiv_germ x N (op U) hx _)

/-- On underlying abelian groups, `moduleSkyscraperMapToStalk` is Mathlib's stalk/skyscraper
adjunction map applied to the morphism of presheaves of abelian groups underlying `g`,
composed with the comparison of the two descriptions of the skyscraper. -/
theorem moduleSkyscraperMapToStalk_underlying (X : RingedSpace.{u, u}) (x : X)
    (P : PresheafOfModules.{u} (X.presheaf ⋙ forget₂ CommRingCat RingCat))
    (N : ModuleCat.{u} (X.presheaf.stalk x))
    (g : P ⟶ OXModule.skyscraperPOM x N) :
    (forget₂ (ModuleCat (X.presheaf.stalk x)) AddCommGrpCat).map
      (moduleSkyscraperMapToStalk X x P N g) =
    StalkSkyscraperPresheafAdjunctionAuxs.fromStalk x
      ((PresheafOfModules.toPresheaf _).map g ≫
        (skyscraperUnderlyingIso X x N).hom) := by
  classical
  apply TopCat.Presheaf.stalk_hom_ext
  intro U hx
  apply AddCommGrpCat.hom_ext
  ext m
  change (OXModule.sheafify_skyscraperPOM_stalkIso_skyscraper_addEquiv x N)
    (moduleStalkMap X.presheaf g x
      (TopCat.Presheaf.germ P.presheaf U x hx m)) = _
  refine Eq.trans (skyscraper_stalkIso_moduleStalkMap_germ X x P N g U hx m) ?_
  refine Eq.trans ?_ (ConcreteCategory.congr_hom
    (StalkSkyscraperPresheafAdjunctionAuxs.germ_fromStalk x
      ((PresheafOfModules.toPresheaf (X.presheaf ⋙ forget₂ CommRingCat RingCat)).map g ≫
        (skyscraperUnderlyingIso X x N).hom) U hx) m).symm
  exact (ConcreteCategory.congr_hom
    (skyscraperUnderlyingIso_hom_app_leg X x N (op U) hx) (g.app (op U) m)).symm

/-- Taking the stalk at `x` is left adjoint to the skyscraper presheaf of modules at `x`:
`O_{X,x}`-linear maps out of the stalk of `P` correspond bijectively to morphisms of
presheaves of modules from `P` into the skyscraper with value `N`. -/
noncomputable def moduleStalkSkyscraperHomEquiv (X : RingedSpace.{u, u}) (x : X)
    (P : PresheafOfModules.{u} (X.presheaf ⋙ forget₂ CommRingCat RingCat))
    (N : ModuleCat.{u} (X.presheaf.stalk x)) :
    (ModuleCat.of (X.presheaf.stalk x)
      ↑(TopCat.Presheaf.stalk P.presheaf x) ⟶ N) ≃
      (P ⟶ OXModule.skyscraperPOM x N) where
  toFun := moduleSkyscraperMapFromStalk X x P N
  invFun := moduleSkyscraperMapToStalk X x P N
  left_inv g := by
    classical
    apply (forget₂ (ModuleCat (X.presheaf.stalk x)) AddCommGrpCat).map_injective
    rw [moduleSkyscraperMapToStalk_underlying]
    change StalkSkyscraperPresheafAdjunctionAuxs.fromStalk x
      ((StalkSkyscraperPresheafAdjunctionAuxs.toSkyscraperPresheaf x
        ((forget₂ (ModuleCat (X.presheaf.stalk x)) AddCommGrpCat).map g) ≫
        (skyscraperUnderlyingIso X x N).inv) ≫
        (skyscraperUnderlyingIso X x N).hom) = _
    rw [Category.assoc, Iso.inv_hom_id, Category.comp_id,
      StalkSkyscraperPresheafAdjunctionAuxs.fromStalk_to_skyscraper]
  right_inv g := by
    classical
    apply (PresheafOfModules.toPresheaf _).map_injective
    change StalkSkyscraperPresheafAdjunctionAuxs.toSkyscraperPresheaf x
      ((forget₂ (ModuleCat (X.presheaf.stalk x)) AddCommGrpCat).map
        (moduleSkyscraperMapToStalk X x P N g)) ≫
          (skyscraperUnderlyingIso X x N).inv = _
    refine Eq.trans (congrArg (fun z : TopCat.Presheaf.stalk P.presheaf x ⟶
        (forget₂ (ModuleCat (X.presheaf.stalk x)) AddCommGrpCat).obj N =>
      StalkSkyscraperPresheafAdjunctionAuxs.toSkyscraperPresheaf x z ≫
        (skyscraperUnderlyingIso X x N).inv)
      (moduleSkyscraperMapToStalk_underlying X x P N g)) ?_
    refine Eq.trans (congrArg (fun z : P.presheaf ⟶ skyscraperPresheaf x
        ((forget₂ (ModuleCat (X.presheaf.stalk x)) AddCommGrpCat).obj N) =>
      z ≫ (skyscraperUnderlyingIso X x N).inv)
      (StalkSkyscraperPresheafAdjunctionAuxs.to_skyscraper_fromStalk x
        ((PresheafOfModules.toPresheaf (X.presheaf ⋙ forget₂ CommRingCat RingCat)).map g ≫
          (skyscraperUnderlyingIso X x N).hom))) ?_
    exact (Category.assoc _ _ _).trans
      ((congrArg (fun z : (OXModule.skyscraperPOM x N).presheaf ⟶
          (OXModule.skyscraperPOM x N).presheaf =>
        (PresheafOfModules.toPresheaf (X.presheaf ⋙ forget₂ CommRingCat RingCat)).map g ≫ z)
        (skyscraperUnderlyingIso X x N).hom_inv_id).trans (Category.comp_id _))

/-- Any two composites of canonical identifications of equal objects with the same source
and target agree, since the equalities they transport along are themselves unique.  This is
the commutativity of a square all four of whose edges are such identifications. -/
private theorem eqToHom_square_comm {C : Type*} [Category C] {A A₁ A₂ B B₁ B₂ : C}
    (p : A = A₁) (p' : A₁ = A₂) (p'' : A₂ = B)
    (q : A = B₁) (q' : B₁ = B₂) (q'' : B₂ = B) :
    eqToHom p ≫ eqToHom p' ≫ eqToHom p'' = (eqToHom q ≫ eqToHom q') ≫ eqToHom q'' := by
  cases p; cases p'; cases p''; cases q; cases q'
  simp

/-- Over an open set not containing `x`, the skyscraper presheaf of modules at `x` is terminal. -/
private noncomputable def isTerminal_skyscraperPOM_presheaf_obj (X : RingedSpace.{u, u}) (x : X)
    (N : ModuleCat.{u} (X.presheaf.stalk x)) (U : (Opens X.carrier)ᵒᵖ) (hx : x ∉ U.unop) :
    IsTerminal ((OXModule.skyscraperPOM x N).presheaf.obj U) := by
  change IsTerminal ((forget₂ (ModuleCat _) AddCommGrpCat).obj (OXModule.skyscraperObj x N U))
  rw [OXModule.skyscraperObj, dite_eq_right hx]
  change IsTerminal (AddCommGrpCat.of PUnit)
  letI : ∀ Y : AddCommGrpCat, Unique (Y ⟶ AddCommGrpCat.of PUnit) := fun Y =>
    { default := AddCommGrpCat.ofHom (0 : (↑Y) →+ PUnit)
      uniq := fun f => by ext y }
  exact IsTerminal.ofUnique _

/-- On underlying presheaves of abelian groups, the pushforward along `f` of the skyscraper at
`x` with value `N` is the skyscraper at `f x` with value `N`: an open set of `Y` contains
`f x` exactly when its preimage contains `x`. -/
private noncomputable def skyscraperPushforwardUnderlyingIso
    {X Y : RingedSpace.{u, u}} (f : X ⟶ Y) (x : X)
    (N : ModuleCat.{u} (X.presheaf.stalk x)) :
    ((PresheafOfModules.pushforward (structureSheafHom f).hom).obj
      (OXModule.skyscraperPOM x N)).presheaf ≅
      (OXModule.skyscraperPOM (f.hom.base x)
        ((ModuleCat.restrictScalars (f.hom.stalkMap x).hom).obj N)).presheaf := by
  classical
  let y := f.hom.base x
  let N' := (ModuleCat.restrictScalars (f.hom.stalkMap x).hom).obj N
  refine NatIso.ofComponents (fun V => ?_) ?_
  · by_cases hy : y ∈ V.unop
    · have hx : x ∈ (opensMap f).obj V.unop := hy
      let eS := eqToIso (OXModule.skyscraperPOM_presheaf_obj_eq x N
        (op ((opensMap f).obj V.unop)) hx)
      let eT := eqToIso (OXModule.skyscraperPOM_presheaf_obj_eq y N' V hy)
      exact eS ≪≫ eT.symm
    · have hx : x ∉ (opensMap f).obj V.unop := hy
      have hS : IsTerminal (((PresheafOfModules.pushforward
          (structureSheafHom f).hom).obj (OXModule.skyscraperPOM x N)).presheaf.obj V) :=
        isTerminal_skyscraperPOM_presheaf_obj X x N (op ((opensMap f).obj V.unop)) hx
      exact hS.uniqueUpToIso (isTerminal_skyscraperPOM_presheaf_obj Y y N' V hy)
  · intro V W i
    by_cases hyW : y ∈ W.unop
    · have hyV : y ∈ V.unop := (leOfHom i.unop) hyW
      have hxW : x ∈ (opensMap f).obj W.unop := hyW
      have hxV : x ∈ (opensMap f).obj V.unop := hyV
      simp only [dite_eq_left hyW, dite_eq_left hyV]
      change (OXModule.skyscraperPOM x N).presheaf.map
          ((opensMap f).map i.unop).op ≫ _ =
        _ ≫ (OXModule.skyscraperPOM y N').presheaf.map i
      rw [OXModule.skyscraperPOM_presheaf_map_eq x N
        ((opensMap f).map i.unop).op hxW,
        OXModule.skyscraperPOM_presheaf_map_eq y N' i hyW]
      simp only [eqToHom_trans, ObjectProperty.ι_obj]
      exact eqToHom_square_comm (C := AddCommGrpCat.{u}) _
        (OXModule.skyscraperPOM_presheaf_obj_eq x N (op ((opensMap f).obj W.unop)) hxW)
        (OXModule.skyscraperPOM_presheaf_obj_eq y N' W hyW).symm
        (OXModule.skyscraperPOM_presheaf_obj_eq x N (op ((opensMap f).obj V.unop)) hxV)
        (OXModule.skyscraperPOM_presheaf_obj_eq y N' V hyV).symm _
    · apply (isTerminal_skyscraperPOM_presheaf_obj Y y N' W hyW).hom_ext

/-- Over an open set containing `f x`, `skyscraperPushforwardUnderlyingIso` is the composite of the
canonical identifications of both sides with `N`. -/
private theorem skyscraperPushforwardUnderlyingIso_hom_app_apply
    {X Y : RingedSpace.{u, u}} (f : X ⟶ Y) (x : X) (N : ModuleCat.{u} (X.presheaf.stalk x))
    (V : (Opens Y.carrier)ᵒᵖ) (hy : f.hom.base x ∈ V.unop)
    (z : ↑(((PresheafOfModules.pushforward (structureSheafHom f).hom).obj
      (OXModule.skyscraperPOM x N)).presheaf.obj V)) :
    ConcreteCategory.hom (eqToHom (OXModule.skyscraperPOM_presheaf_obj_eq (f.hom.base x)
        ((ModuleCat.restrictScalars (f.hom.stalkMap x).hom).obj N) V hy))
      ((skyscraperPushforwardUnderlyingIso f x N).hom.app V z) =
    ConcreteCategory.hom (eqToHom (OXModule.skyscraperPOM_presheaf_obj_eq x N
      (op ((opensMap f).obj V.unop)) hy)) z := by
  have hcomponent : (skyscraperPushforwardUnderlyingIso f x N).hom.app V =
      (eqToIso (OXModule.skyscraperPOM_presheaf_obj_eq x N
        (op ((opensMap f).obj V.unop)) hy) ≪≫
      (eqToIso (OXModule.skyscraperPOM_presheaf_obj_eq (f.hom.base x)
        ((ModuleCat.restrictScalars (f.hom.stalkMap x).hom).obj N) V hy)).symm).hom := by
    simp only [skyscraperPushforwardUnderlyingIso, NatIso.ofComponents, dite_eq_left hy]
    rfl
  rw [hcomponent]
  exact Iso.inv_hom_id_apply (eqToIso (OXModule.skyscraperPOM_presheaf_obj_eq (f.hom.base x)
    ((ModuleCat.restrictScalars (f.hom.stalkMap x).hom).obj N) V hy)) _

/-- The morphism of presheaves of modules underlying `skyscraperPushforwardUnderlyingIso`. -/
private noncomputable def skyscraperPushforwardMap
    {X Y : RingedSpace.{u, u}} (f : X ⟶ Y) (x : X)
    (N : ModuleCat.{u} (X.presheaf.stalk x)) :
    (PresheafOfModules.pushforward (structureSheafHom f).hom).obj
      (OXModule.skyscraperPOM x N) ⟶
      OXModule.skyscraperPOM (f.hom.base x)
        ((ModuleCat.restrictScalars (f.hom.stalkMap x).hom).obj N) := by
  classical
  refine PresheafOfModules.homMk (skyscraperPushforwardUnderlyingIso f x N).hom ?_
  intro V r n
  by_cases hy : f.hom.base x ∈ V.unop
  · let U : Opens X.carrier := (opensMap f).obj V.unop
    have hx : x ∈ U := hy
    let N' := (ModuleCat.restrictScalars (f.hom.stalkMap x).hom).obj N
    let eS := eqToHom (OXModule.skyscraperPOM_presheaf_obj_eq x N (op U) hx)
    let eT := eqToHom
      (OXModule.skyscraperPOM_presheaf_obj_eq (f.hom.base x) N' V hy)
    apply (ConcreteCategory.bijective_of_isIso eT).injective
    have hcmp := skyscraperPushforwardUnderlyingIso_hom_app_apply f x N V hy
    have hleg := OXModule.skyscraperPOM_leg_smul (f.hom.base x) N' V hy r
      ((skyscraperPushforwardUnderlyingIso f x N).hom.app V n)
    have hsmul := congrArg (fun m : (↑N' : Type u) =>
      (Y.presheaf.germ V.unop (f.hom.base x) hy).hom r • m) (hcmp n)
    have hlegX := OXModule.skyscraperPOM_leg_smul x N (op U) hx
      ((f.hom.c.app V).hom r) n
    have hstalk := PresheafedSpace.stalkMap_germ_apply f.hom V.unop x hy r
    have hscalar := congrArg
      (fun s : (↑(X.presheaf.stalk x) : Type u) => s • eS n) hstalk
    exact ((hcmp (r • n)).trans (hlegX.trans hscalar.symm)).trans (hleg.trans hsmul).symm
  · have hzero : Subsingleton
        (↑(OXModule.skyscraperObj (f.hom.base x)
          ((ModuleCat.restrictScalars (f.hom.stalkMap x).hom).obj N) V)) := by
      rw [OXModule.skyscraperObj, dite_eq_right hy]
      infer_instance
    exact hzero.elim _ _

/-- The pushforward along `f` of the skyscraper at `x` with value `N` is isomorphic, as a
presheaf of `O_Y`-modules, to the skyscraper at `f x` with value `N` regarded as an
`O_{Y,f(x)}`-module by restriction of scalars along the map of stalks. -/
private noncomputable def skyscraperPushforwardIso
    {X Y : RingedSpace.{u, u}} (f : X ⟶ Y) (x : X)
    (N : ModuleCat.{u} (X.presheaf.stalk x)) :
    (PresheafOfModules.pushforward (structureSheafHom f).hom).obj
      (OXModule.skyscraperPOM x N) ≅
      OXModule.skyscraperPOM (f.hom.base x)
        ((ModuleCat.restrictScalars (f.hom.stalkMap x).hom).obj N) := by
  let α := skyscraperPushforwardMap f x N
  have h (V : (Opens Y.carrier)ᵒᵖ) : IsIso (α.app V) := by
    rw [ConcreteCategory.isIso_iff_bijective]
    exact (ConcreteCategory.bijective_of_isIso
      ((skyscraperPushforwardUnderlyingIso f x N).hom.app V))
  letI (V : (Opens Y.carrier)ᵒᵖ) : IsIso (α.app V) := h V
  refine PresheafOfModules.isoMk (fun V => asIso (α.app V)) ?_
  intro V W i
  exact α.naturality i

/-- `O_{X,x}`-linear maps out of the stalk at `x` of the presheaf pullback of `G` correspond
bijectively to `O_{X,x}`-linear maps out of the extension of scalars of the stalk of `G` at
`f x`.  This is the composite of the stalk/skyscraper adjunction on `X`, the presheaf
pullback/pushforward adjunction, the skyscraper pushforward comparison, the stalk/skyscraper
adjunction on `Y`, and extension/restriction of scalars. -/
private noncomputable def presheafPullbackStalkHomEquiv
    {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
    (G : SheafOfModules.{u} (structureSheafRing Y)) (x : X)
    (N : ModuleCat.{u} (X.presheaf.stalk x)) :
    letI : (PresheafOfModules.pushforward (structureSheafHom f).hom).IsRightAdjoint :=
      PresheafOfModules.instIsRightAdjointPushforward _
    let M' : PresheafOfModules (X.presheaf ⋙ forget₂ CommRingCat RingCat) :=
      (PresheafOfModules.pullback (structureSheafHom f).hom).obj G.val
    let G' : PresheafOfModules (Y.presheaf ⋙ forget₂ CommRingCat RingCat) := G.val
    (ModuleCat.of (X.presheaf.stalk x)
      ↑(TopCat.Presheaf.stalk M'.presheaf x) ⟶ N) ≃
    ((ModuleCat.extendScalars (f.hom.stalkMap x).hom).obj
      (ModuleCat.of (Y.presheaf.stalk (f.hom.base x))
        ↑(TopCat.Presheaf.stalk G'.presheaf (f.hom.base x))) ⟶ N) := by
  classical
  letI : (PresheafOfModules.pushforward (structureSheafHom f).hom).IsRightAdjoint :=
    PresheafOfModules.instIsRightAdjointPushforward _
  let M' : PresheafOfModules (X.presheaf ⋙ forget₂ CommRingCat RingCat) :=
    (PresheafOfModules.pullback (structureSheafHom f).hom).obj G.val
  let G' : PresheafOfModules (Y.presheaf ⋙ forget₂ CommRingCat RingCat) := G.val
  let N' : ModuleCat (Y.presheaf.stalk (f.hom.base x)) :=
    (ModuleCat.restrictScalars (f.hom.stalkMap x).hom).obj N
  let e₁ := moduleStalkSkyscraperHomEquiv X x M' N
  let e₂ := (PresheafOfModules.pullbackPushforwardAdjunction
    (structureSheafHom f).hom).homEquiv G.val (OXModule.skyscraperPOM x N)
  let e₃ : (G.val ⟶ (PresheafOfModules.pushforward
      (structureSheafHom f).hom).obj (OXModule.skyscraperPOM x N)) ≃
      (G.val ⟶ OXModule.skyscraperPOM (f.hom.base x) N') :=
    (skyscraperPushforwardIso f x N).homToEquiv
  let e₄ := (moduleStalkSkyscraperHomEquiv Y (f.hom.base x) G' N').symm
  let e₅ : (ModuleCat.of (Y.presheaf.stalk (f.hom.base x))
      ↑(TopCat.Presheaf.stalk G'.presheaf (f.hom.base x)) ⟶ N') ≃
      ((ModuleCat.extendScalars (f.hom.stalkMap x).hom).obj
        (ModuleCat.of (Y.presheaf.stalk (f.hom.base x))
          ↑(TopCat.Presheaf.stalk G'.presheaf (f.hom.base x))) ⟶ N) :=
    (ModuleCat.ExtendRestrictScalarsAdj.homEquiv
      (f.hom.stalkMap x).hom).symm
  exact e₁.trans (e₂.trans (e₃.trans (e₄.trans e₅)))

/-- The correspondence `presheafPullbackStalkHomEquiv` sends the pure tensor of `1` with the
germ of a section `s` to the value of the given map on the germ of the presheaf pullback unit
applied to `s`. -/
private theorem presheafPullbackStalkHomEquiv_one_tmul
    {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
    (G : SheafOfModules.{u} (structureSheafRing Y)) (x : X)
    (N : ModuleCat.{u} (X.presheaf.stalk x))
    (V : Opens Y.carrier) (hx : f.hom.base x ∈ V) (s : G.val.obj (op V)) :
    letI : (PresheafOfModules.pushforward (structureSheafHom f).hom).IsRightAdjoint :=
      PresheafOfModules.instIsRightAdjointPushforward _
    let G' : PresheafOfModules (Y.presheaf ⋙ forget₂ CommRingCat RingCat) := G.val
    let M' : PresheafOfModules (X.presheaf ⋙ forget₂ CommRingCat RingCat) :=
      (PresheafOfModules.pullback (structureSheafHom f).hom).obj G.val
    letI : Module (Y.presheaf.stalk (f.hom.base x))
      ↑(TopCat.Presheaf.stalk G'.presheaf (f.hom.base x)) := inferInstance
    letI : Algebra (Y.presheaf.stalk (f.hom.base x)) (X.presheaf.stalk x) :=
      (f.hom.stalkMap x).hom.toAlgebra
    ∀ g : ModuleCat.of (X.presheaf.stalk x)
      ↑(TopCat.Presheaf.stalk M'.presheaf x) ⟶ N,
    (presheafPullbackStalkHomEquiv f G x N g)
      ((1 : X.presheaf.stalk x) ⊗ₜ[Y.presheaf.stalk (f.hom.base x)]
        TopCat.Presheaf.germ G'.presheaf V (f.hom.base x) hx s) =
    g (TopCat.Presheaf.germ
      M'.presheaf
        ((opensMap f).obj V) x hx
        (((PresheafOfModules.pullbackPushforwardAdjunction
          (structureSheafHom f).hom).unit.app G.val).app (op V) s)) := by
  classical
  dsimp only
  intro g
  let : (PresheafOfModules.pushforward (structureSheafHom f).hom).IsRightAdjoint :=
    PresheafOfModules.instIsRightAdjointPushforward _
  let : Algebra (Y.presheaf.stalk (f.hom.base x)) (X.presheaf.stalk x) :=
    (f.hom.stalkMap x).hom.toAlgebra
  rw [← ModuleCat.extendRestrictScalarsAdj_homEquiv_apply]
  have hq : (presheafPullbackStalkHomEquiv f G x N) g =
      (ModuleCat.ExtendRestrictScalarsAdj.homEquiv (f.hom.stalkMap x).hom).symm
        ((moduleStalkSkyscraperHomEquiv Y (f.hom.base x) G.val
          ((ModuleCat.restrictScalars (f.hom.stalkMap x).hom).obj N)).symm
          ((skyscraperPushforwardIso f x N).homToEquiv
            (((PresheafOfModules.pullbackPushforwardAdjunction
              (structureSheafHom f).hom).homEquiv G.val (OXModule.skyscraperPOM x N))
              (moduleSkyscraperMapFromStalk X x
                ((PresheafOfModules.pullback (structureSheafHom f).hom).obj G.val) N g)))) := by
    rfl
  rw [hq]
  change (((ModuleCat.ExtendRestrictScalarsAdj.homEquiv
      (f.hom.stalkMap x).hom) ((ModuleCat.ExtendRestrictScalarsAdj.homEquiv
      (f.hom.stalkMap x).hom).symm
        ((moduleStalkSkyscraperHomEquiv Y (f.hom.base x) G.val
          ((ModuleCat.restrictScalars (f.hom.stalkMap x).hom).obj N)).symm
          ((skyscraperPushforwardIso f x N).homToEquiv
            (((PresheafOfModules.pullbackPushforwardAdjunction
              (structureSheafHom f).hom).homEquiv G.val (OXModule.skyscraperPOM x N))
              (moduleSkyscraperMapFromStalk X x
                ((PresheafOfModules.pullback (structureSheafHom f).hom).obj G.val) N g))))))
      (TopCat.Presheaf.germ G.val.presheaf V (f.hom.base x) hx s)) = _
  rw [Equiv.apply_symm_apply]
  let M' : PresheafOfModules (X.presheaf ⋙ forget₂ CommRingCat RingCat) :=
    (PresheafOfModules.pullback (structureSheafHom f).hom).obj G.val
  let N' : ModuleCat (Y.presheaf.stalk (f.hom.base x)) :=
    (ModuleCat.restrictScalars (f.hom.stalkMap x).hom).obj N
  let h := moduleSkyscraperMapFromStalk X x M' N g
  let k := ((PresheafOfModules.pullbackPushforwardAdjunction
    (structureSheafHom f).hom).homEquiv G.val (OXModule.skyscraperPOM x N)) h
  let l := (skyscraperPushforwardIso f x N).homToEquiv k
  change (moduleSkyscraperMapToStalk Y (f.hom.base x) G.val N' l)
    (TopCat.Presheaf.germ G.val.presheaf V (f.hom.base x) hx s) = _
  change (OXModule.sheafify_skyscraperPOM_stalkIso_skyscraper_addEquiv
    (f.hom.base x) N')
    (moduleStalkMap Y.presheaf l (f.hom.base x)
      (TopCat.Presheaf.germ G.val.presheaf V (f.hom.base x) hx s)) = _
  refine Eq.trans (skyscraper_stalkIso_moduleStalkMap_germ Y (f.hom.base x) G.val N' l
    V hx s) ?_
  let U : Opens X.carrier := (opensMap f).obj V
  have hxU : x ∈ U := hx
  let eS := eqToHom (OXModule.skyscraperPOM_presheaf_obj_eq x N (op U) hxU)
  let eT := eqToHom (OXModule.skyscraperPOM_presheaf_obj_eq
    (f.hom.base x) N' (op V) hx)
  change eT (l.app (op V) s) = _
  have hl : eT (l.app (op V) s) = eS (k.app (op V) s) :=
    skyscraperPushforwardUnderlyingIso_hom_app_apply f x N (op V) hx (k.app (op V) s)
  rw [hl]
  let η := (PresheafOfModules.pullbackPushforwardAdjunction
    (structureSheafHom f).hom).unit.app G.val
  have hk : k.app (op V) s = h.app (op U) (η.app (op V) s) :=
    congrArg (fun q : G.val ⟶ (PresheafOfModules.pushforward (structureSheafHom f).hom).obj
        (OXModule.skyscraperPOM x N) => q.app (op V) s)
      ((PresheafOfModules.pullbackPushforwardAdjunction
        (structureSheafHom f).hom).homEquiv_unit G.val (OXModule.skyscraperPOM x N) h)
  rw [hk]
  have hh (t : M'.obj (op U)) : eS (h.app (op U) t) =
      g (TopCat.Presheaf.germ M'.presheaf U x hxU t) := by
    have hinv : moduleSkyscraperMapToStalk X x M' N h = g :=
      (moduleStalkSkyscraperHomEquiv X x M' N).symm_apply_apply g
    refine Eq.trans ?_ (ConcreteCategory.congr_hom hinv
      (TopCat.Presheaf.germ M'.presheaf U x hxU t))
    exact (skyscraper_stalkIso_moduleStalkMap_germ X x M' N h U hxU t).symm
  exact hh (η.app (op V) s)

/-- The canonical extension-of-scalars map, as a morphism of `O_{X,x}`-modules, from the base
change of the stalk of `G` at `f x` to the stalk at `x` of the presheaf pullback of `G`. -/
private noncomputable def presheafPullbackTensorHom
    {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
    (G : SheafOfModules.{u} (structureSheafRing Y)) (x : X) :
    letI : (PresheafOfModules.pushforward (structureSheafHom f).hom).IsRightAdjoint :=
      PresheafOfModules.instIsRightAdjointPushforward _
    let G' : PresheafOfModules (Y.presheaf ⋙ forget₂ CommRingCat RingCat) := G.val
    let M' : PresheafOfModules (X.presheaf ⋙ forget₂ CommRingCat RingCat) :=
      (PresheafOfModules.pullback (structureSheafHom f).hom).obj G.val
    (ModuleCat.extendScalars (f.hom.stalkMap x).hom).obj
      (ModuleCat.of (Y.presheaf.stalk (f.hom.base x))
        ↑(TopCat.Presheaf.stalk G'.presheaf (f.hom.base x))) ⟶
      ModuleCat.of (X.presheaf.stalk x) ↑(TopCat.Presheaf.stalk M'.presheaf x) := by
  letI : (PresheafOfModules.pushforward (structureSheafHom f).hom).IsRightAdjoint :=
    PresheafOfModules.instIsRightAdjointPushforward _
  letI : Algebra (Y.presheaf.stalk (f.hom.base x)) (X.presheaf.stalk x) :=
    (f.hom.stalkMap x).hom.toAlgebra
  let G' : PresheafOfModules (Y.presheaf ⋙ forget₂ CommRingCat RingCat) := G.val
  let M' : PresheafOfModules (X.presheaf ⋙ forget₂ CommRingCat RingCat) :=
    (PresheafOfModules.pullback (structureSheafHom f).hom).obj G.val
  change ModuleCat.of (X.presheaf.stalk x)
      (TensorProduct (Y.presheaf.stalk (f.hom.base x)) (X.presheaf.stalk x)
        ↑(TopCat.Presheaf.stalk G'.presheaf (f.hom.base x))) ⟶
    ModuleCat.of (X.presheaf.stalk x) ↑(TopCat.Presheaf.stalk M'.presheaf x)
  exact ModuleCat.ofHom (presheafPullbackTensorToStalk f G x)

/-- The stalk of the presheaf pullback is extension of scalars, by a linear equivalence sending
the germ of the adjunction-unit image of every section to a pure tensor of `1`. -/
private noncomputable def PresheafPullbackStalkBridge {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
    (G : SheafOfModules.{u} (structureSheafRing Y)) (x : X) : Prop :=
  letI : (PresheafOfModules.pushforward (structureSheafHom f).hom).IsRightAdjoint :=
    PresheafOfModules.instIsRightAdjointPushforward _
  let M' : PresheafOfModules (X.presheaf ⋙ forget₂ CommRingCat RingCat) :=
    (PresheafOfModules.pullback (structureSheafHom f).hom).obj G.val
  let G' : PresheafOfModules (Y.presheaf ⋙ forget₂ CommRingCat RingCat) := G.val
  letI : Algebra (Y.presheaf.stalk (f.hom.base x)) (X.presheaf.stalk x) :=
    (f.hom.stalkMap x).hom.toAlgebra
  ∃ e : ↑(TopCat.Presheaf.stalk M'.presheaf x) ≃ₗ[X.presheaf.stalk x]
      TensorProduct (Y.presheaf.stalk (f.hom.base x)) (X.presheaf.stalk x)
        ↑(TopCat.Presheaf.stalk G'.presheaf (f.hom.base x)),
    ∀ (V : Opens Y.carrier) (hx : f.hom.base x ∈ V) (s : G.val.obj (op V)),
      e (TopCat.Presheaf.germ M'.presheaf ((opensMap f).obj V) x hx
          (((PresheafOfModules.pullbackPushforwardAdjunction
            (structureSheafHom f).hom).unit.app G.val).app (op V) s)) =
        (1 : X.presheaf.stalk x) ⊗ₜ[Y.presheaf.stalk (f.hom.base x)]
          TopCat.Presheaf.germ G'.presheaf V (f.hom.base x) hx s

/-- `PresheafPullbackStalkBridge` implies the stalk formula for the adjunction-defined pullback
`modulePullback`. -/
private theorem exists_modulePullbackStalkLinearEquiv_of_bridge
    {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
    (G : SheafOfModules.{u} (structureSheafRing Y)) (x : X)
    (h : PresheafPullbackStalkBridge f G x) :
    let G' : PresheafOfModules (Y.presheaf ⋙ forget₂ CommRingCat RingCat) := G.val
    let P' : PresheafOfModules (X.presheaf ⋙ forget₂ CommRingCat RingCat) :=
      ((modulePullback f).obj G).val
    letI : Algebra (Y.presheaf.stalk (f.hom.base x)) (X.presheaf.stalk x) :=
      (f.hom.stalkMap x).hom.toAlgebra
    ∃ e : ↑(TopCat.Presheaf.stalk P'.presheaf x) ≃ₗ[X.presheaf.stalk x]
        TensorProduct (Y.presheaf.stalk (f.hom.base x)) (X.presheaf.stalk x)
          ↑(TopCat.Presheaf.stalk G'.presheaf (f.hom.base x)),
      ∀ (V : Opens Y.carrier) (hx : f.hom.base x ∈ V) (s : G.val.obj (op V)),
        e (TopCat.Presheaf.germ P'.presheaf ((opensMap f).obj V) x hx
            (((modulePullbackPushforwardAdjunction f).unit.app G).val.app (op V) s)) =
          (1 : X.presheaf.stalk x) ⊗ₜ[Y.presheaf.stalk (f.hom.base x)]
            TopCat.Presheaf.germ G'.presheaf V (f.hom.base x) hx s := by
  let : (PresheafOfModules.pushforward (structureSheafHom f).hom).IsRightAdjoint :=
    PresheafOfModules.instIsRightAdjointPushforward _
  let : Presheaf.IsLocallyInjective (Opens.grothendieckTopology X.carrier)
      (𝟙 (structureSheafRing X).obj) := inferInstance
  let : Presheaf.IsLocallySurjective (Opens.grothendieckTopology X.carrier)
      (𝟙 (structureSheafRing X).obj) := inferInstance
  let : Algebra (Y.presheaf.stalk (f.hom.base x)) (X.presheaf.stalk x) :=
    (f.hom.stalkMap x).hom.toAlgebra
  obtain ⟨e, he⟩ := h
  let M' : PresheafOfModules (X.presheaf ⋙ forget₂ CommRingCat RingCat) :=
    (PresheafOfModules.pullback (structureSheafHom f).hom).obj G.val
  refine ⟨((modulePullbackComparison_stalk f G x).trans
      (sheafificationStalkEquiv M' x).symm).trans e, ?_⟩
  intro V hx s
  change e ((sheafificationStalkEquiv M' x).symm
    ((modulePullbackComparison_stalk f G x)
      (TopCat.Presheaf.germ ((modulePullback f).obj G).val.presheaf
        ((opensMap f).obj V) x hx
        (((modulePullbackPushforwardAdjunction f).unit.app G).val.app (op V) s)))) = _
  have hc := congrArg (sheafificationStalkEquiv M' x).symm
    (modulePullbackComparison_unit_germ f G x V hx s)
  have hs := congrArg (sheafificationStalkEquiv M' x).symm
    (sheafificationStalkEquiv_unit_germ M' x ((opensMap f).obj V) hx
      (((PresheafOfModules.pullbackPushforwardAdjunction
        (structureSheafHom f).hom).unit.app G.val).app (op V) s))
  have hstep := hc.trans hs.symm
  simp only [LinearEquiv.symm_apply_apply] at hstep
  exact (congrArg e hstep).trans (he V hx s)

/-- The stalk of the pullback is extension of scalars along the structure map on stalks,
by a linear equivalence sending the germ of the adjunction-unit image of every section
to the pure tensor of `1` with its original germ. -/
@[stacks 0098]
lemma exists_modulePullbackStalkLinearEquiv {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
    (G : SheafOfModules.{u} (structureSheafRing Y)) (x : X) :
    let G' : PresheafOfModules (Y.presheaf ⋙ forget₂ CommRingCat RingCat) := G.val
    let P' : PresheafOfModules (X.presheaf ⋙ forget₂ CommRingCat RingCat) :=
      ((modulePullback f).obj G).val
    letI : Algebra (Y.presheaf.stalk (f.hom.base x)) (X.presheaf.stalk x) :=
      (f.hom.stalkMap x).hom.toAlgebra
    ∃ e : ↑(TopCat.Presheaf.stalk P'.presheaf x) ≃ₗ[X.presheaf.stalk x]
        TensorProduct (Y.presheaf.stalk (f.hom.base x)) (X.presheaf.stalk x)
          ↑(TopCat.Presheaf.stalk G'.presheaf (f.hom.base x)),
      ∀ (V : Opens Y.carrier) (hx : f.hom.base x ∈ V) (s : G.val.obj (op V)),
        e (TopCat.Presheaf.germ P'.presheaf ((opensMap f).obj V) x hx
            (((modulePullbackPushforwardAdjunction f).unit.app G).val.app (op V) s)) =
          (1 : X.presheaf.stalk x) ⊗ₜ[Y.presheaf.stalk (f.hom.base x)]
            TopCat.Presheaf.germ G'.presheaf V (f.hom.base x) hx s :=
  exists_modulePullbackStalkLinearEquiv_of_bridge f G x (by
    show PresheafPullbackStalkBridge f G x
    classical
    let : (PresheafOfModules.pushforward (structureSheafHom f).hom).IsRightAdjoint :=
      PresheafOfModules.instIsRightAdjointPushforward _
    let : Algebra (Y.presheaf.stalk (f.hom.base x)) (X.presheaf.stalk x) :=
      (f.hom.stalkMap x).hom.toAlgebra
    let G' : PresheafOfModules (Y.presheaf ⋙ forget₂ CommRingCat RingCat) := G.val
    let M' : PresheafOfModules (X.presheaf ⋙ forget₂ CommRingCat RingCat) :=
      (PresheafOfModules.pullback (structureSheafHom f).hom).obj G.val
    let : Module (Y.presheaf.stalk (f.hom.base x))
        ↑(TopCat.Presheaf.stalk G'.presheaf (f.hom.base x)) := inferInstance
    let : Module (X.presheaf.stalk x)
        ↑(TopCat.Presheaf.stalk M'.presheaf x) := inferInstance
    let T : ModuleCat (X.presheaf.stalk x) :=
      (ModuleCat.extendScalars (f.hom.stalkMap x).hom).obj
        (ModuleCat.of (Y.presheaf.stalk (f.hom.base x))
          ↑(TopCat.Presheaf.stalk G'.presheaf (f.hom.base x)))
    let S : ModuleCat (X.presheaf.stalk x) :=
      ModuleCat.of (X.presheaf.stalk x) ↑(TopCat.Presheaf.stalk M'.presheaf x)
    let k : T ⟶ S := presheafPullbackTensorHom f G x
    have hk (N : ModuleCat (X.presheaf.stalk x)) (g : S ⟶ N) :
        presheafPullbackStalkHomEquiv f G x N g = k ≫ g := by
      let : Module (Y.presheaf.stalk (f.hom.base x)) N :=
        Module.compHom N (f.hom.stalkMap x).hom
      let : IsScalarTower (Y.presheaf.stalk (f.hom.base x))
          (X.presheaf.stalk x) N := IsScalarTower.of_compHom _ _ _
      let : Module (Y.presheaf.stalk (f.hom.base x)) (X.presheaf.stalk x) :=
        Module.compHom _ (f.hom.stalkMap x).hom
      let : IsScalarTower (Y.presheaf.stalk (f.hom.base x))
          (X.presheaf.stalk x) (X.presheaf.stalk x) := IsScalarTower.of_compHom _ _ _
      let : IsScalarTower (Y.presheaf.stalk (f.hom.base x))
          (X.presheaf.stalk x)
          ↑((ModuleCat.restrictScalars (f.hom.stalkMap x).hom).obj
            (ModuleCat.of (X.presheaf.stalk x) (X.presheaf.stalk x))) :=
        IsScalarTower.of_compHom _ _ _
      apply ModuleCat.hom_ext
      apply TensorProduct.AlgebraTensorModule.ext
      intro a m
      change X.presheaf.stalk x at a
      obtain ⟨V, hx, s, rfl⟩ := TopCat.Presheaf.exists_germ_eq G'.presheaf m
      have hA {Z : Type u} [AddCommGroup Z] [Module (X.presheaf.stalk x) Z]
          (φ : TensorProduct (Y.presheaf.stalk (f.hom.base x)) (X.presheaf.stalk x)
            ↑(TopCat.Presheaf.stalk G'.presheaf (f.hom.base x)) →ₗ[X.presheaf.stalk x] Z) :
          φ (a ⊗ₜ[Y.presheaf.stalk (f.hom.base x)]
            TopCat.Presheaf.germ G'.presheaf V (f.hom.base x) hx s) =
          a • φ ((1 : X.presheaf.stalk x) ⊗ₜ[Y.presheaf.stalk (f.hom.base x)]
            TopCat.Presheaf.germ G'.presheaf V (f.hom.base x) hx s) := by
        rw [← map_smul, TensorProduct.smul_tmul']
        simp
      change ((presheafPullbackStalkHomEquiv f G x N g).hom)
        (a ⊗ₜ[Y.presheaf.stalk (f.hom.base x)]
          TopCat.Presheaf.germ G'.presheaf V (f.hom.base x) hx s) =
        g.hom ((presheafPullbackTensorToStalk f G x)
          (a ⊗ₜ[Y.presheaf.stalk (f.hom.base x)]
            TopCat.Presheaf.germ G'.presheaf V (f.hom.base x) hx s))
      have hpsiOne : (presheafPullbackTensorToStalk f G x)
            ((1 : X.presheaf.stalk x) ⊗ₜ[Y.presheaf.stalk (f.hom.base x)]
              TopCat.Presheaf.germ G'.presheaf V (f.hom.base x) hx s) =
          TopCat.Presheaf.germ M'.presheaf ((opensMap f).obj V) x hx
            (((PresheafOfModules.pullbackPushforwardAdjunction
              (structureSheafHom f).hom).unit.app G.val).app (op V) s) :=
        presheafPullbackTensorToStalk_one_tmul f G x V hx s
      have hphiOne : (presheafPullbackStalkHomEquiv f G x N g).hom
            ((1 : X.presheaf.stalk x) ⊗ₜ[Y.presheaf.stalk (f.hom.base x)]
              TopCat.Presheaf.germ G'.presheaf V (f.hom.base x) hx s) =
          g.hom (TopCat.Presheaf.germ M'.presheaf ((opensMap f).obj V) x hx
            (((PresheafOfModules.pullbackPushforwardAdjunction
              (structureSheafHom f).hom).unit.app G.val).app (op V) s)) :=
        presheafPullbackStalkHomEquiv_one_tmul f G x N V hx s g
      exact (hA (presheafPullbackStalkHomEquiv f G x N g).hom).trans
        ((congrArg (fun z : ↑N => a • z) hphiOne).trans
          ((map_smul g.hom a _).symm.trans (congrArg g.hom
            ((hA (presheafPullbackTensorToStalk f G x)).trans
              (congrArg (fun z : ↑(TopCat.Presheaf.stalk M'.presheaf x) => a • z)
                hpsiOne))).symm))
    have hki : IsIso k := by
      apply isIso_of_coyoneda_map_bijective
      intro N
      have hfun : (fun (g : S ⟶ N) => k ≫ g) =
          (presheafPullbackStalkHomEquiv f G x N) := by
        funext g
        exact (hk N g).symm
      rw [hfun]
      exact (presheafPullbackStalkHomEquiv f G x N).bijective
    let : IsIso k := hki
    let e := (asIso k).symm.toLinearEquiv
    refine ⟨e, ?_⟩
    intro V hx s
    change (asIso k).inv
      (TopCat.Presheaf.germ M'.presheaf ((opensMap f).obj V) x hx
        (((PresheafOfModules.pullbackPushforwardAdjunction
          (structureSheafHom f).hom).unit.app G.val).app (op V) s)) = _
    rw [← presheafPullbackTensorToStalk_one_tmul f G x V hx s]
    exact (asIso k).hom_inv_id_apply _)

end RingedSpaceModuleAdjunction
