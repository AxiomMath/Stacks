module

public import StacksFrontier.AlgebraicGeometry.Crystalline.BigSite.ChangeBaseConnectedLimits
public import StacksFrontier.AlgebraicGeometry.Crystalline.BigSite.FibreProduct
public import StacksFrontier.AlgebraicGeometry.Crystalline.ChangeBaseBigCohomology
public import StacksFrontier.AlgebraicGeometry.Crystalline.FCrystal
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.ChangeBaseQuasicoherentCrystal
public import StacksFrontier.CategoryTheory.Sites.Modules.OverFunctorExact
public import StacksFrontier.CategoryTheory.Sites.SlicePost.Continuous

/-!
# Change of divided power base preserves crystals in finite locally free modules

Let `u = changeBase S S' f g h : CRIS(X/S) ⥤ CRIS(Y/S')` be change of divided power base
[Stacks, Tag 07IC] along a morphism of divided power schemes `f : S ⟶ S'` and a morphism
`g : X ⟶ Y` over it.  The pullback of sheaves of modules along `u` is restriction along `u`
(`Crystalline.GlobalCrystallineSituation.changeBaseModulePullback`), and this file proves that it
carries crystals in finite locally free modules, [Stacks, Tag 07IU], to crystals in finite locally
free modules.

Quasi-coherence is carried by
`Crystalline.GlobalCrystallineSituation.isQuasicoherentOnSite_changeBaseModulePullback`.  Finite
local freeness is a condition of the shape "every object has a covering on whose members the
module is of a given kind", and it is carried by restriction along a continuous and cocontinuous
functor of sites with an isomorphism of structure sheaves: a covering of an object `A` of
`CRIS(X/S)` is obtained from a covering of `u(A)` by cocontinuity, and on the members the module is
carried by restriction along the localized functor `Over.post u`, which is continuous because
`CRIS(X/S)` has fibre products and `u` preserves them.  The structure map is the identity, change
of base leaving the ambient divided power scheme of an object untouched.

## Main results

* `SheafOfModules.isFiniteFree_pushforward` — a finite free module restricts to a finite free
  module along an isomorphism of structure sheaves.
* `SheafOfModules.isFiniteLocallyFreeOnSite_pushforward` — finite local freeness is carried by
  restriction along a continuous cocontinuous functor of sites and an isomorphism of structure
  sheaves.
* `...GlobalCrystallineSituation.IsFiniteLocallyFreeQuasicoherentCrystal.changeBaseModulePullback`
  — **the pullback along change of divided power base of a crystal in finite locally free modules
  is a crystal in finite locally free modules.**
* `Crystalline.GlobalCrystallineSituation.changeBaseModulePullback_obj_val_obj` and
  `Crystalline.GlobalCrystallineSituation.changeBaseBigModulePullback_obj_val_obj` — the value of
  the pullback at an object `(U, T, δ)` is the value of the module at the image of `(U, T, δ)`.

## References

* [Stacks Project, Tag 07IC](https://stacks.math.columbia.edu/tag/07IC)
* [Stacks Project, Tag 07IU](https://stacks.math.columbia.edu/tag/07IU)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe w u₁ v₁ u₂ v₂ u

namespace SheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  {R : Sheaf J RingCat.{w}} {S : Sheaf K RingCat.{w}}

/-- **The unit comparison of restriction along an isomorphism of structure sheaves is an
isomorphism.** -/
theorem isIso_unitToPushforwardObjUnit_of_isIso {G : D ⥤ C} [G.IsContinuous K J]
    (φ : S ⟶ (G.sheafPushforwardContinuous RingCat.{w} K J).obj R) [IsIso φ] :
    IsIso (SheafOfModules.unitToPushforwardObjUnit φ) := by
  have : IsIso ((sheafToPresheaf K AddCommGrpCat.{w}).map
      ((SheafOfModules.toSheaf S).map (SheafOfModules.unitToPushforwardObjUnit φ))) := by
    show IsIso (Functor.whiskerRight φ.hom (forget₂ RingCat.{w} AddCommGrpCat.{w}))
    infer_instance
  have : IsIso ((SheafOfModules.toSheaf S).map (SheafOfModules.unitToPushforwardObjUnit φ)) :=
    isIso_of_reflects_iso _ (sheafToPresheaf K AddCommGrpCat.{w})
  exact isIso_of_reflects_iso _ (SheafOfModules.toSheaf S)

/-- **A finite free sheaf of modules restricts to a finite free sheaf of modules along an
isomorphism of structure sheaves.**  A finite coproduct of copies of the structure sheaf is a
finite biproduct, restriction is additive and so preserves it, and it carries the structure sheaf
to the structure sheaf because the structure map is an isomorphism. -/
theorem isFiniteFree_pushforward {G : D ⥤ C} [G.IsContinuous K J]
    (φ : S ⟶ (G.sheafPushforwardContinuous RingCat.{w} K J).obj R) [IsIso φ]
    (M : SheafOfModules.{w} R) (hM : IsFiniteFree R M) :
    IsFiniteFree S ((SheafOfModules.pushforward.{w} φ).obj M) := by
  obtain ⟨n, ι, ⟨hc⟩⟩ := (isFiniteFree_iff_exists_isColimit R M).mp hM
  have := isIso_unitToPushforwardObjUnit_of_isIso φ
  let H := SheafOfModules.pushforward.{w} φ
  let e := asIso (SheafOfModules.unitToPushforwardObjUnit φ)
  have hH : IsColimit (Cofan.mk (H.obj M) fun i ↦ H.map (ι i)) :=
    (isBilimitOfPreserves H (biconeIsBilimitOfColimitCoconeOfIsColimit hc)).isColimit
  refine (isFiniteFree_iff_exists_isColimit _ _).mpr ⟨n, fun i ↦ e.hom ≫ H.map (ι i), ⟨?_⟩⟩
  refine Cofan.IsColimit.mk _ (fun s ↦ Cofan.IsColimit.desc hH (fun i ↦ e.inv ≫ s.inj i))
    (fun s i ↦ ?_) (fun s m hm ↦ ?_)
  · show (e.hom ≫ H.map (ι i)) ≫ _ = _
    have hi := Cofan.IsColimit.fac hH (fun i ↦ e.inv ≫ s.inj i) i
    change H.map (ι i) ≫ _ = _ at hi
    rw [Category.assoc, hi, Iso.hom_inv_id_assoc]
  · refine Cofan.IsColimit.hom_ext hH _ _ fun i ↦ ?_
    have hi : (e.hom ≫ H.map (ι i)) ≫ m = s.inj i := hm i
    rw [Cofan.IsColimit.fac]
    show H.map (ι i) ≫ m = _
    simpa only [Category.assoc, Iso.inv_hom_id_assoc] using congrArg (fun k ↦ e.inv ≫ k) hi

/-- **Finite local freeness is carried by restriction along a continuous cocontinuous functor of
sites and an isomorphism of structure sheaves.**  A covering of an object `X` of `D` is produced
from a covering of `G(X)` by cocontinuity, and on its members the module is the restriction along
the localized functor of the module over a member of the covering of `G(X)`. -/
theorem isFiniteLocallyFreeOnSite_pushforward {C D : Type u₁} [Category.{v₁} C]
    [Category.{v₁} D] {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {R : Sheaf J RingCat.{w}} {S : Sheaf K RingCat.{w}} (G : D ⥤ C) [G.IsContinuous K J]
    [G.IsCocontinuous K J]
    [∀ X, (Over.post (X := X) G).IsContinuous (K.over X) (J.over (G.obj X))]
    (φ : S ⟶ (G.sheafPushforwardContinuous RingCat.{w} K J).obj R) [IsIso φ]
    (M : SheafOfModules.{w} R) (hM : IsFiniteLocallyFreeOnSite M) :
    IsFiniteLocallyFreeOnSite ((SheafOfModules.pushforward.{w} φ).obj M) := by
  intro X
  obtain ⟨I, V, f, hcover, hV⟩ := hM (G.obj X)
  let L := Σ (Y : D), (Y ⟶ X) × (Σ i : I, G.obj Y ⟶ V i)
  refine ⟨L, fun l ↦ l.1, fun l ↦ l.2.1, ?_, fun l ↦ ?_⟩
  · refine K.superset_covering (fun Y g hg ↦ ?_) (G.cover_lift K J hcover)
    obtain ⟨i, a, -⟩ := (Sieve.mem_ofArrows_iff V f (G.map g)).mp hg
    exact Sieve.ofArrows_mk (fun l : L ↦ l.1) (fun l ↦ l.2.1) ⟨Y, g, i, a⟩
  · let G' := Over.post (X := l.1) G ⋙ Over.map l.2.2.2
    let ψ : S.over l.1 ⟶
        (G'.sheafPushforwardContinuous RingCat.{w} (K.over l.1)
          (J.over (V l.2.2.1))).obj (R.over (V l.2.2.1)) :=
      ((Over.forget l.1).sheafPushforwardContinuous RingCat.{w} (K.over l.1) K).map φ
    have : IsIso ψ := Functor.map_isIso _ φ
    exact isFiniteFree_pushforward ψ (M.over (V l.2.2.1)) (hV l.2.2.1)

end SheafOfModules

namespace Crystalline.GlobalCrystallineSituation

variable (S S' : GlobalCrystallineSituation.{u}) (f : S.S ⟶ S'.S) (g : S.X ⟶ S'.X)
  (h : S.toClosedFiber ≫ DividedPowerScheme.closedFiberMap f = g ≫ S'.toClosedFiber)

/-- The comparison map of structure sheaves for change of divided power base is an isomorphism, it
being the identity. -/
instance isIso_changeBaseStructureHom : IsIso (changeBaseStructureHom S S' f g h) :=
  inferInstanceAs (IsIso (𝟙 (crystallineStructureSheaf S)))

/-- **Change of divided power base preserves fibre products**, a cospan being a connected
diagram. -/
instance changeBase_preservesLimitsOfShape_walkingCospan :
    PreservesLimitsOfShape WalkingCospan (changeBase S S' f g h) :=
  changeBase_preservesLimitsOfShape _

/-- **The localizations of change of divided power base are continuous**: `CRIS(X/S)` has fibre
products and change of base preserves them. -/
instance changeBase_overPost_isContinuous (A : Thickening S) :
    (Over.post (X := A) (changeBase S S' f g h)).IsContinuous ((topology S).over A)
      ((topology S').over ((changeBase S S' f g h).obj A)) :=
  Functor.isContinuous_overPost_of_preservesPullbacks _ _ _ A

/-- **The value of the pullback along change of divided power base at an object is the value of
the module at the image of the object.** -/
theorem changeBaseModulePullback_obj_val_obj
    (N : SheafOfModules.{u} (crystallineStructureSheaf S')) (A : Thickening S) :
    ((changeBaseModulePullback S S' f g h).obj N).val.obj (op A) =
      N.val.obj (op ((changeBase S S' f g h).obj A)) := rfl

/-- **The restriction maps of the pullback along change of divided power base are those of the
module at the images of the morphisms.** -/
theorem changeBaseModulePullback_obj_val_map
    (N : SheafOfModules.{u} (crystallineStructureSheaf S')) {A B : Thickening S} (k : A ⟶ B)
    (x : ((changeBaseModulePullback S S' f g h).obj N).val.obj (op B)) :
    ((changeBaseModulePullback S S' f g h).obj N).val.map k.op x =
      N.val.map ((changeBase S S' f g h).map k).op x := rfl

/-- **The value of the pullback along change of divided power base at the module universe of the
cohomology at an object is the value of the module at the image of the object.** -/
theorem changeBaseBigModulePullback_obj_val_obj (N : SmallSite.BigModuleSheaf S')
    (A : Thickening S) :
    ((changeBaseBigModulePullback S S' f g h).obj N).val.obj (op A) =
      N.val.obj (op ((changeBase S S' f g h).obj A)) := rfl

/-- **The pullback along change of divided power base of a finite locally free sheaf of modules is
finite locally free.** -/
theorem isFiniteLocallyFreeOnSite_changeBaseModulePullback
    (N : SheafOfModules.{u} (crystallineStructureSheaf S'))
    (hN : SheafOfModules.IsFiniteLocallyFreeOnSite N) :
    SheafOfModules.IsFiniteLocallyFreeOnSite ((changeBaseModulePullback S S' f g h).obj N) :=
  SheafOfModules.isFiniteLocallyFreeOnSite_pushforward (changeBase S S' f g h)
    (changeBaseStructureHom S S' f g h) N hN

variable {S S' f g h} in
/-- **The pullback along change of divided power base of a crystal in finite locally free modules
is a crystal in finite locally free modules**, [Stacks, Tag 07IU]: both quasi-coherence and finite
local freeness are carried by restriction along change of base. -/
theorem IsFiniteLocallyFreeQuasicoherentCrystal.changeBaseModulePullback
    {N : SheafOfModules.{u} (crystallineStructureSheaf S')}
    (hN : IsFiniteLocallyFreeQuasicoherentCrystal N) :
    IsFiniteLocallyFreeQuasicoherentCrystal
      ((GlobalCrystallineSituation.changeBaseModulePullback S S' f g h).obj N) where
  isQuasicoherentOnSite :=
    isQuasicoherentOnSite_changeBaseModulePullback f g h N hN.isQuasicoherentOnSite
  isFiniteLocallyFree :=
    isFiniteLocallyFreeOnSite_changeBaseModulePullback S S' f g h N hN.isFiniteLocallyFree

end Crystalline.GlobalCrystallineSituation
