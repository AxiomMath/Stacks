module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.CategoryTheory.Limits.Shapes.Countable
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Geometry.RingedSpace.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Pullback and pushforward of sheaves of modules on ringed spaces

Let `(f, f^♯) : (X, 𝒪_X) ⟶ (Y, 𝒪_Y)` be a morphism of ringed spaces, that is, a continuous
map `f : X ⟶ Y` together with a map of sheaves of rings `f^♯ : 𝒪_Y ⟶ f_* 𝒪_X` on `Y`.
Pushing a sheaf of `𝒪_X`-modules `F` forward along `f` produces the sheaf of `𝒪_Y`-modules
`V ↦ F(f⁻¹ V)`, and pulling a sheaf of `𝒪_Y`-modules `G` back produces
`f^* G = f^{-1} G ⊗_{f^{-1} 𝒪_Y} 𝒪_X`. The pullback `f^*` is left adjoint to `f_*`, that is,
there is a bijection `Hom_{𝒪_X}(f^* G, F) ≃ Hom_{𝒪_Y}(G, f_* F)` natural in both variables.
Both functors are additive. The ringed spaces and the sheaves of modules all live in one
universe `u`.

## Main definitions

* `structureSheafRing`: the structure sheaf of a ringed space, as a sheaf of rings on its opens.
* `RingedSpaceModuleAdjunction.ModuleSheaves`: the category of sheaves of modules over the
  structure sheaf of a ringed space.
* `RingedSpaceModuleAdjunction.structureSheafHom`: the map `f^♯`, as a morphism from
  `structureSheafRing Y` to the pushforward of `structureSheafRing X`.
* `RingedSpaceModuleAdjunction.modulePushforward`: the pushforward functor `f_*`.
* `RingedSpaceModuleAdjunction.modulePullback`: the pullback functor `f^*`.
* `RingedSpaceModuleAdjunction.modulePullbackPushforwardAdjunction`: the adjunction
  `f^* ⊣ f_*`.
* `RingedSpaceModuleAdjunction.homEquiv`: the bijection
  `Hom_{𝒪_X}(f^* G, F) ≃ Hom_{𝒪_Y}(G, f_* F)`.
* `RingedSpaceModuleAdjunction.modulePullbackObjUnitIso`: the isomorphism `f^* 𝒪_Y ≅ 𝒪_X`.
* `RingedSpaceModuleAdjunction.modulePullbackObjFreeIso`: the isomorphism
  `f^* (𝒪_Y^{(I)}) ≅ 𝒪_X^{(I)}`.

## Main results

* `RingedSpaceModuleAdjunction.pushforward_structureSheafHom_isRightAdjoint`: the pushforward
  along a morphism of ringed spaces admits a left adjoint.
* `RingedSpaceModuleAdjunction.modulePushforward_additive` and
  `RingedSpaceModuleAdjunction.modulePullback_additive`: `f_*` and `f^*` are additive.

## References

* [Stacks Project, Tag 0096](https://stacks.math.columbia.edu/tag/0096)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace Functor

universe u

/-- The structure sheaf `𝒪_X` of a ringed space, postcomposed with `forget₂ CommRingCat RingCat`:
a sheaf of rings for the open-cover topology on `Opens X`. -/
@[instance_reducible] noncomputable def structureSheafRing (X : RingedSpace.{u, u}) :
    Sheaf (Opens.grothendieckTopology X.carrier) RingCat.{u} :=
  ⟨(⟨X.presheaf, X.IsSheaf⟩ :
      Sheaf (Opens.grothendieckTopology X.carrier) CommRingCat.{u}).obj ⋙
        forget₂ CommRingCat RingCat,
    (Presheaf.isSheaf_iff_isSheaf_comp _ X.presheaf (forget₂ CommRingCat RingCat)).mp X.IsSheaf⟩

namespace RingedSpaceModuleAdjunction

/-- The category of sheaves of modules over the structure sheaf of a ringed space. -/
noncomputable abbrev ModuleSheaves (X : RingedSpace.{u, u}) :=
  SheafOfModules.{u} (structureSheafRing X)

/-- `ModuleSheaves X` is `SheafOfModules.{u} (structureSheafRing X)`. -/
theorem moduleSheaves_eq (X : RingedSpace.{u, u}) :
    ModuleSheaves X = SheafOfModules.{u} (structureSheafRing X) :=
  rfl

/-- The `CategoryTheory.Category` instance on `ModuleSheaves X` is the one on
`SheafOfModules.{u} (structureSheafRing X)`. -/
theorem moduleSheaves_instCategory_eq (X : RingedSpace.{u, u}) :
    (inferInstance : Category (ModuleSheaves X)) =
      (inferInstance : Category (SheafOfModules.{u} (structureSheafRing X))) :=
  rfl

section
variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)

/-- The inverse-image functor on opens induced by the underlying continuous map of a
morphism of ringed spaces: `Opens Y ⥤ Opens X`. -/
@[sga "4 III 1.9.1" "special case"]
noncomputable abbrev opensMap : Opens Y.carrier ⥤ Opens X.carrier :=
  Opens.map f.hom.base

/-- Continuity of `opensMap f` between the Grothendieck topologies on `Opens Y` and
`Opens X`. -/
@[sga "4 III 1.9.1" "continuity of f^{-1}", sga "4 IV 4.1.1" "partial"]
instance opensMap_isContinuous :
    (opensMap f).IsContinuous (Opens.grothendieckTopology Y.carrier)
      (Opens.grothendieckTopology X.carrier) :=
  instIsContinuousOpensCarrierMapGrothendieckTopology _

/-- The component `f^♯ : 𝒪_Y ⟶ f_* 𝒪_X` of a morphism of ringed spaces, read as a morphism
of sheaves of `RingCat`-valued rings on `Y` whose target is the pushforward of
`structureSheafRing X` along the continuous functor `opensMap f`. -/
noncomputable def structureSheafHom : structureSheafRing Y ⟶
    ((opensMap f).sheafPushforwardContinuous RingCat.{u}
        (Opens.grothendieckTopology Y.carrier)
        (Opens.grothendieckTopology X.carrier)).obj (structureSheafRing X) :=
  ObjectProperty.homMk (whiskerRight f.hom.c (forget₂ CommRingCat RingCat))

/-- Pushforward of sheaves of modules along a morphism of ringed spaces,
`f_* : Mod(𝒪_X) ⥤ Mod(𝒪_Y)`, given on sections by `(f_* F)(V) = F(f⁻¹ V)`, with the
`𝒪_Y`-module structure restricted along `f^♯`. -/
@[stacks 0095 "(1)",
  stacks 0096,
  ega "0 4.2.1" "Ψ_* functor",
  sga "4 Vbis 1.3.6" "ringed spaces, φ_*",
  ega "0 12.2.1",
  sga "3 VIIA 1.1" "more general",
  sga "4 IV 13.2.1" "special case",
  sga "4 V 5.0" "special case"]
noncomputable def modulePushforward :
    SheafOfModules.{u} (structureSheafRing X) ⥤ SheafOfModules.{u} (structureSheafRing Y) :=
  SheafOfModules.pushforward (structureSheafHom f)

end

/-- Pushforward of sheaves of modules along a morphism of ringed spaces is additive. -/
instance modulePushforward_additive {X Y : RingedSpace.{u, u}} (f : X ⟶ Y) :
    (modulePushforward f).Additive where
  map_add := rfl

/-- The pushforward functor `f_* : Mod(𝒪_X) ⥤ Mod(𝒪_Y)` along a morphism `f` of ringed
spaces, in the form `SheafOfModules.pushforward (structureSheafHom f)`, admits a left adjoint. -/
@[ega "0 4.4.3" "partial", sga "4 Vbis 1.3.6" "partial", sga "6 VI 2.3.1" "partial"]
instance pushforward_structureSheafHom_isRightAdjoint {X Y : RingedSpace.{u, u}} (f : X ⟶ Y) :
    (SheafOfModules.pushforward.{u} (structureSheafHom f)).IsRightAdjoint :=
  haveI : (PresheafOfModules.pushforward.{u} (structureSheafHom f).hom).IsRightAdjoint :=
    PresheafOfModules.instIsRightAdjointPushforward _
  SheafOfModules.instIsRightAdjointPushforward (structureSheafHom f)

/-- The pushforward functor `f_* : Mod(𝒪_X) ⥤ Mod(𝒪_Y)` along a morphism `f` of ringed
spaces admits a left adjoint, stated for `modulePushforward f`. -/
@[ega "0 4.2.1" "more general", sga "4 Vbis 1.3.6" "partial", sga "6 VI 2.3.1" "partial"]
theorem modulePushforward_isRightAdjoint {X Y : RingedSpace.{u, u}} (f : X ⟶ Y) :
    (modulePushforward f).IsRightAdjoint :=
  pushforward_structureSheafHom_isRightAdjoint f

/-- Pullback of sheaves of modules along a morphism of ringed spaces,
`f^* : Mod(𝒪_Y) ⥤ Mod(𝒪_X)`: the left adjoint of `f_*`. -/
@[stacks 0096,
  sga "4 IV 13.2.2" "ringed space, comm O",
  sga "4 IV 13.2" "u^* for ringed spaces",
  sga "4 Vbis 1.3.6" "ringed spaces, φ^*",
  sga "4 XVII 4.1" "ringed spaces",
  ega "0 4.3.1",
  sga "3 III 0.1.4" "more general",
  sga "6 IV 2.6" "special case",
  sga "6 VI 2.3.1" "more general"]
noncomputable def modulePullback {X Y : RingedSpace.{u, u}} (f : X ⟶ Y) :
    SheafOfModules.{u} (structureSheafRing Y) ⥤ SheafOfModules.{u} (structureSheafRing X) :=
  letI : (SheafOfModules.pushforward (structureSheafHom f)).IsRightAdjoint :=
    modulePushforward_isRightAdjoint f
  SheafOfModules.pullback (structureSheafHom f)

/-- The adjunction `f^* ⊣ f_*` between the categories of sheaves of modules on the ringed
spaces `Y` and `X`. -/
@[stacks 0096,
  sga "4 IV 13.4" "a), ringed spaces",
  sga "4 Vbis 1.3.6" "ringed spaces",
  ega "0 4.4.3" "partial",
  ega "III 7.7.9" "more general",
  sga "3 I 4.6.4" "more general",
  sga "4 IV 14.2" "special case",
  sga "6 VI 2.3.1" "more general"]
noncomputable def modulePullbackPushforwardAdjunction {X Y : RingedSpace.{u, u}} (f : X ⟶ Y) :
    modulePullback f ⊣ modulePushforward f :=
  letI : (SheafOfModules.pushforward (structureSheafHom f)).IsRightAdjoint :=
    modulePushforward_isRightAdjoint f
  SheafOfModules.pullbackPushforwardAdjunction (structureSheafHom f)

/-- Pullback of sheaves of modules along a morphism of ringed spaces is additive. -/
noncomputable instance modulePullback_additive {X Y : RingedSpace.{u, u}} (f : X ⟶ Y) :
    (modulePullback f).Additive :=
  (modulePullbackPushforwardAdjunction f).left_adjoint_additive

/-- The bijection of hom-sets `Hom_{𝒪_X}(f^* G, F) ≃ Hom_{𝒪_Y}(G, f_* F)` given by the
adjunction `f^* ⊣ f_*`, natural in both `F` and `G`. -/
@[stacks 0096,
  sga "4 IV 13.4" "a), ringed spaces",
  sga "4 Vbis 1.3.6" "ringed spaces",
  ega "0 4.4.3" "partial",
  ega "III 7.7.9" "more general",
  sga "3 I 4.6.4" "more general",
  sga "3 VIB 11.4" "(†)",
  sga "6 VI 2.3.1" "partial"]
noncomputable def homEquiv {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
    (F : SheafOfModules.{u} (structureSheafRing X))
    (G : SheafOfModules.{u} (structureSheafRing Y)) :
    ((modulePullback f).obj G ⟶ F) ≃ (G ⟶ (modulePushforward f).obj F) :=
  (modulePullbackPushforwardAdjunction f).homEquiv G F

/-- The pullback of the structure sheaf is the structure sheaf, `f^* 𝒪_Y ≅ 𝒪_X`, by the
morphism `SheafOfModules.pullbackObjUnitToUnit` adjoint to `f^♯ : 𝒪_Y ⟶ f_* 𝒪_X`. -/
noncomputable def modulePullbackObjUnitIso {X Y : RingedSpace.{u, u}} (f : X ⟶ Y) :
    (modulePullback f).obj (SheafOfModules.unit (structureSheafRing Y)) ≅
      SheafOfModules.unit (structureSheafRing X) :=
  haveI : (opensMap f).Final := CategoryTheory.final_of_representablyFlat _
  (asIso (SheafOfModules.pullbackObjUnitToUnit.{u} (structureSheafHom f)) :
    (SheafOfModules.pullback (structureSheafHom f)).obj
      (SheafOfModules.unit (structureSheafRing Y)) ≅
      SheafOfModules.unit (structureSheafRing X))

/-- The pullback of a free sheaf of modules is free on the same index type,
`f^* (𝒪_Y^{(I)}) ≅ 𝒪_X^{(I)}`. -/
noncomputable def modulePullbackObjFreeIso {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
    (I : Type u) :
    (modulePullback f).obj (SheafOfModules.free I) ≅ SheafOfModules.free I :=
  haveI : (opensMap f).Final := CategoryTheory.final_of_representablyFlat _
  (SheafOfModules.pullbackObjFreeIso.{u} (structureSheafHom f) I :
    (SheafOfModules.pullback (structureSheafHom f)).obj (SheafOfModules.free I) ≅
      SheafOfModules.free I)

/-- The preimages of a cover of the target by open sets form a cover of the source. -/
lemma coversTop_preimage {X Y : RingedSpace.{u, u}} (f : X ⟶ Y) {I : Type u}
    (V : I → Opens (Y : TopCat)) (hV : (Opens.grothendieckTopology (Y : TopCat)).CoversTop V) :
    (Opens.grothendieckTopology (X : TopCat)).CoversTop
      (fun i : ULift I => (Opens.map f.hom.base).obj (V i.down)) := by
  apply (Opens.coversTop_iff (X : Type u) (fun i : ULift I =>
    (Opens.map f.hom.base).obj (V i.down))).2
  have hcover : TopologicalSpace.IsOpenCover V := (Opens.coversTop_iff (Y : Type u) V).1 hV
  change iSup (fun i : ULift I => (Opens.map f.hom.base).obj (V i.down)) = ⊤
  ext x
  simp only [Opens.coe_iSup, Set.mem_iUnion, Opens.coe_top, Set.mem_univ, iff_true]
  obtain ⟨i, hi⟩ := hcover.exists_mem (f.hom.base x)
  exact ⟨ULift.up i, by simpa [Opens.map] using hi⟩

end RingedSpaceModuleAdjunction
