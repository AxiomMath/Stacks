module

public import StacksFrontier.AlgebraicGeometry.PicardFibreTrivial.FibreNeighbourhood
public import StacksFrontier.AlgebraicGeometry.AffineBaseChange.StructureSheaf
public import StacksFrontier.AlgebraicGeometry.PicSurjectiveFinite.Basic
public import StacksFrontier.AlgebraicGeometry.ProjectionFormula.Locality
public import StacksFrontier.AlgebraicGeometry.Variety.EulerChar.Cohomology
import StacksCore.Tactic.StacksAttribute

/-!
# Invertible modules along a proper morphism with `f_* 𝒪_X = 𝒪_Y`

Let `f : X ⟶ Y` be a proper morphism onto a Noetherian scheme with `f_* 𝒪_X = 𝒪_Y`, whose fibres
have dimension at most one and satisfy `H¹(X_y, 𝒪_{X_y}) = 0`. [Stacks, Tag 0E24] says that
`f^* : Pic(Y) ⟶ Pic(X)` is a bijection onto the subgroup of classes of invertible modules
trivial on every fibre. This file proves it.

* **Injectivity.** For an invertible `𝒪_Y`-module `𝒩` the unit `𝒩 ⟶ f_* f^* 𝒩` is an
  isomorphism, because it is one for `𝒩 = 𝒪_Y` (that is `f_* 𝒪_X = 𝒪_Y`) and invertibility of
  the unit is local on `Y` (`Stacks.PicardFibreTrivial.isIso_unit_app_of_isInvertible`). This
  is the projection formula of the source in the case it uses.
* **The image is trivial on the fibres**, since `f^* 𝒩` restricted to `X_y` is pulled back from
  `Spec κ(y)`, over which `𝒩` is trivial.
* **Every invertible module trivial on the fibres is in the image.** Such an `ℒ` is trivial on
  `f⁻¹(V)` for a neighbourhood `V` of every closed point
  (`Stacks.PicardFibreTrivial.exists_restrict_iso_unit_of_fiber`, which is where the theorem on
  formal functions enters), hence of every point, `Y` being quasi-compact. Since `f` is an
  isomorphism on the sections over every open, the transition functions of `ℒ` on such a cover
  descend to `Y` (`Stacks.PicFinite.exists_isInvertible_modulePullback_iso_of_forall_isIso_app` at
  `V = Y`), and `ℒ` is the pullback of the glued module.

## Main results

* `Stacks.PicardFibreTrivial.isIso_unit_app_of_isInvertible`: the unit `𝒩 ⟶ f_* f^* 𝒩`.
* `Stacks.PicardFibreTrivial.nonempty_iso_of_pullback_iso`: injectivity of `f^*`.
* `Stacks.PicardFibreTrivial.nonempty_fiber_pullback_iso_unit`: `f^* 𝒩` is trivial on every
  fibre.
* `Stacks.PicardFibreTrivial.exists_pullback_iso_of_forall_fiber`: the converse.
* `Stacks.PicardFibreTrivial.pullback_injective_and_exists_pullback_iso_iff`:
  **[Stacks, Tag 0E24]**.

## References

* [Stacks Project, Tag 0E24](https://stacks.math.columbia.edu/tag/0E24)
* [Stacks Project, Tag 01E8](https://stacks.math.columbia.edu/tag/01E8)
* [Stacks Project, Tag 02OD](https://stacks.math.columbia.edu/tag/02OD)
* [Stacks Project, Tag 0C0T](https://stacks.math.columbia.edu/tag/0C0T)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace

universe u

namespace Stacks.PicardFibreTrivial

variable {X Y : Scheme.{u}}

/-! ### The unit `𝒩 ⟶ f_* f^* 𝒩` -/

/-- The unit of `f^* ⊣ f_*`. -/
abbrev unitPP (f : X ⟶ Y) :
    𝟭 Y.Modules ⟶ Scheme.Modules.pullback f ⋙ Scheme.Modules.pushforward f :=
  (Scheme.Modules.pullbackPushforwardAdjunction f).unit

/-- **The unit at the structure sheaf is an isomorphism when `f_* 𝒪_X = 𝒪_Y`.** -/
theorem isIso_unit_app_unit (f : X ⟶ Y) (hO : ∀ W : Y.Opens, IsIso (f.app W)) :
    IsIso ((unitPP f).app (SheafOfModules.unit Y.ringCatSheaf)) := by
  have hs : IsIso (Stacks.AlgebraicGeometry.AffineBaseChange.structureUnitHom f) := by
    rw [Scheme.Modules.Hom.isIso_iff_isIso_app]
    intro W
    rw [ConcreteCategory.isIso_iff_bijective]
    exact ConcreteCategory.bijective_of_isIso (f.app W)
  rw [← Stacks.AlgebraicGeometry.AffineBaseChange.unit_comp_map_pullbackUnitIso f] at hs
  exact @IsIso.of_isIso_comp_right _ _ _ _ _ _ _
    ((Scheme.Modules.pushforward f).mapIso
      (Stacks.AlgebraicGeometry.AffineBaseChange.pullbackUnitIso f)).isIso_hom hs

open Stacks.AffineProjectionFormula in
/-- **The unit `𝒩 ⟶ f_* f^* 𝒩` is an isomorphism for every invertible `𝒪_Y`-module `𝒩`**, when
`f` is an isomorphism on the sections over every open, that is, when `f_* 𝒪_X = 𝒪_Y`. Being an
isomorphism is local on `Y`, and over an open `V` on which `𝒩` is trivial the question is
moved to `𝒩 = 𝒪_Y` along the units of the restriction adjunction, which become invertible
over `V`. This is the projection formula [Stacks, Tag 01E8] in the case the proof of
[Stacks, Tag 0E24] uses. -/
theorem isIso_unit_app_of_isInvertible (f : X ⟶ Y) (hO : ∀ W : Y.Opens, IsIso (f.app W))
    (M : Y.Modules)
    [Stacks.SheafOfModules.IsInvertible Y.presheaf
      (structureSheafRing Y.toRingedSpace).property M] :
    IsIso ((unitPP f).app M) := by
  obtain ⟨U, hU, he⟩ := Stacks.Modules.exists_restrict_iso_unit_of_isInvertible M
  refine Stacks.AlgebraicGeometry.AffineBaseChange.isIso_of_isIso_restrict _ U hU fun i => ?_
  obtain ⟨e⟩ := he i
  let R := Scheme.Modules.restrictFunctor (U i).ι
  let β := Functor.whiskerRight (unitPP f) R
  have key : ∀ {A B : Y.Modules} (k : A ⟶ B), IsIso (R.map k) →
      (IsIso (β.app A) ↔ IsIso (β.app B)) := by
    intro A B k hk
    refine isIso_natTrans_app_iff_of_isIso_map β k hk ?_
    have hk' : IsIso ((Scheme.Modules.pullback (U i).ι).map k) :=
      isIso_functor_map_of_natIso (Scheme.Modules.restrictFunctorIsoPullback (U i).ι).symm k hk
    exact isIso_functor_map_of_natIso (Scheme.Modules.restrictFunctorIsoPullback (U i).ι) _
      (isIso_pullback_pushforward_map f (U i) _ (isIso_pullback_pullback_map f (U i) k hk'))
  have hunit : ∀ A : Y.Modules,
      IsIso (R.map ((Scheme.Modules.restrictAdjunction (U i).ι).unit.app A)) := fun A =>
    isIso_map_unit_of_isIso_counit (Scheme.Modules.restrictAdjunction (U i).ι) A inferInstance
  have h0 : IsIso (β.app (SheafOfModules.unit Y.ringCatSheaf)) := by
    have := isIso_unit_app_unit f hO
    exact (R.mapIso (asIso ((unitPP f).app (SheafOfModules.unit Y.ringCatSheaf)))).isIso_hom
  exact (key _ (hunit M)).2 ((key _ (R.mapIso ((Scheme.Modules.pushforward (U i).ι).mapIso
    (e ≪≫ (Scheme.Modules.restrictUnitIso (U i).ι).symm))).isIso_hom).2
    ((key _ (hunit (SheafOfModules.unit Y.ringCatSheaf))).1 h0))

/-! ### Injectivity, and the image -/

/-- **`f^*` is injective on invertible modules** when `f_* 𝒪_X = 𝒪_Y`: an invertible `𝒩` is
recovered as `f_* f^* 𝒩`. -/
theorem nonempty_iso_of_pullback_iso (f : X ⟶ Y) (hO : ∀ W : Y.Opens, IsIso (f.app W))
    (M N : Y.Modules)
    [Stacks.SheafOfModules.IsInvertible Y.presheaf (structureSheafRing Y.toRingedSpace).property M]
    [Stacks.SheafOfModules.IsInvertible Y.presheaf (structureSheafRing Y.toRingedSpace).property N]
    (e : (Scheme.Modules.pullback f).obj M ≅ (Scheme.Modules.pullback f).obj N) :
    Nonempty (M ≅ N) := by
  have := isIso_unit_app_of_isInvertible f hO M
  have := isIso_unit_app_of_isInvertible f hO N
  exact ⟨asIso ((unitPP f).app M) ≪≫ (Scheme.Modules.pushforward f).mapIso e ≪≫
    (asIso ((unitPP f).app N)).symm⟩

/-- **The pullback of an invertible module is trivial on every fibre**: on `X_y` it is pulled
back from `Spec κ(y)`, which maps into an open over which the module is trivial. -/
theorem nonempty_fiber_pullback_iso_unit (f : X ⟶ Y) (M : Y.Modules)
    [Stacks.SheafOfModules.IsInvertible Y.presheaf (structureSheafRing Y.toRingedSpace).property M]
    (y : Y) :
    Nonempty ((Scheme.Modules.pullback (f.fiberι y)).obj ((Scheme.Modules.pullback f).obj M) ≅
      SheafOfModules.unit (f.fiber y).ringCatSheaf) := by
  obtain ⟨U, hU, he⟩ := Stacks.Modules.exists_restrict_iso_unit_of_isInvertible M
  obtain ⟨z, hz⟩ := TopologicalSpace.Opens.mem_iSup.mp
    (show y ∈ ⨆ z, U z from hU.symm ▸ Set.mem_univ y)
  obtain ⟨e⟩ := he z
  have hs : Set.range (Y.fromSpecResidueField y) ⊆ Set.range (U z).ι := by
    rw [Scheme.range_fromSpecResidueField, Scheme.Opens.range_ι]
    exact Set.singleton_subset_iff.2 hz
  let w := f.fiberToSpecResidueField y ≫ IsOpenImmersion.lift (U z).ι (Y.fromSpecResidueField y) hs
  have hw : f.fiberι y ≫ f = w ≫ (U z).ι := by
    rw [Scheme.Hom.fiber_fac, Category.assoc, IsOpenImmersion.lift_fac]
  exact ⟨(Scheme.Modules.pullbackComp (f.fiberι y) f).app M ≪≫
    (Scheme.Modules.pullbackCongr hw).app M ≪≫
    ((Scheme.Modules.pullbackComp w (U z).ι).app M).symm ≪≫
    (Scheme.Modules.pullback w).mapIso
      (((Scheme.Modules.restrictFunctorIsoPullback (U z).ι).app M).symm ≪≫ e) ≪≫
    Stacks.AlgebraicGeometry.AffineBaseChange.pullbackUnitIso w⟩

/-- **An invertible module trivial on every fibre is a pullback.** Let `f : X ⟶ Y` be proper
onto a Noetherian scheme with `f_* 𝒪_X = 𝒪_Y`, with fibres of dimension at most one and
`H¹(X_y, 𝒪_{X_y}) = 0`. An invertible `𝒪_X`-module `ℒ` with `ℒ|_{X_y} ≅ 𝒪_{X_y}` for every `y`
is `f^* 𝒩` for an invertible `𝒪_Y`-module `𝒩`. -/
theorem exists_pullback_iso_of_forall_fiber (f : X ⟶ Y) [IsProper f] [IsNoetherian Y]
    (hO : ∀ W : Y.Opens, IsIso (f.app W))
    (hdim : ∀ y : Y, topologicalKrullDim (f.fiber y) ≤ 1)
    (hH1 : ∀ y : Y,
      IsZero ((coh (f.fiber y) 1).obj (SheafOfModules.unit (f.fiber y).ringCatSheaf)))
    (L : X.Modules)
    [Stacks.SheafOfModules.IsInvertible X.presheaf (structureSheafRing X.toRingedSpace).property L]
    (hL : ∀ y : Y, Nonempty ((Scheme.Modules.pullback (f.fiberι y)).obj L ≅
      SheafOfModules.unit (f.fiber y).ringCatSheaf)) :
    ∃ M : Y.Modules,
      Stacks.SheafOfModules.IsInvertible Y.presheaf
          (structureSheafRing Y.toRingedSpace).property M ∧
        Nonempty ((Scheme.Modules.pullback f).obj M ≅ L) := by
  -- `ℒ` is trivial near every point: near the closed points by the theorem on formal
  -- functions, and the points where it is trivial nearby form an open set.
  have hcov : Stacks.Divisors.HasTrivializingTargetCover f L := by
    let S : Set Y := {y | ∃ V : Y.Opens, y ∈ V ∧ Nonempty (L.restrict (f ⁻¹ᵁ V).ι ≅
      SheafOfModules.unit (f ⁻¹ᵁ V).toScheme.ringCatSheaf)}
    have hSopen : IsOpen S := isOpen_iff_forall_mem_open.2 fun y ⟨V, hyV, e⟩ =>
      ⟨V, fun z hz => ⟨V, hz, e⟩, V.isOpen, hyV⟩
    have hS : S = Set.univ := by
      by_contra hne
      obtain ⟨y, hyS, hycl⟩ :=
        hSopen.isClosed_compl.exists_closed_singleton (Set.nonempty_compl.2 hne)
      exact hyS (exists_restrict_iso_unit_of_fiber f y hycl (hdim y) (hH1 y) L (hL y).some)
    exact fun y => (hS.symm ▸ Set.mem_univ y : y ∈ S)
  -- The transition functions descend, `f` being an isomorphism on sections.
  have : DiscreteTopology ((⊤ : Y.Opens)ᶜ : Set Y) :=
    ⟨eq_bot_of_singletons_open fun x => (x.2 (Set.mem_univ x.1)).elim⟩
  exact Stacks.PicFinite.exists_isInvertible_modulePullback_iso_of_forall_isIso_app f ⊤
    (fun W _ => hO W) L hcov

/-! ### The theorem -/

/-- **Stacks Project, Tag 0E24.** Let `f : X ⟶ Y` be a proper morphism onto a Noetherian scheme
such that `f_* 𝒪_X = 𝒪_Y`, such that the fibres of `f` have dimension at most one, and such
that `H¹(X_y, 𝒪_{X_y}) = 0` for every `y ∈ Y`. Then `f^* : Pic(Y) ⟶ Pic(X)` is a bijection
onto the subgroup of classes of invertible `𝒪_X`-modules `ℒ` with `ℒ|_{X_y} ≅ 𝒪_{X_y}` for all
`y ∈ Y`: on isomorphism classes of invertible modules `f^*` is injective, and an invertible `ℒ`
is isomorphic to a pullback `f^* 𝒩` of an invertible `𝒪_Y`-module exactly when it is trivial on
every fibre.

The source also asks for `X` to be Noetherian; that follows from the other hypotheses (`f` is
proper over a Noetherian base) and is not needed. -/
@[stacks 0E24]
theorem pullback_injective_and_exists_pullback_iso_iff (f : X ⟶ Y) [IsProper f] [IsNoetherian Y]
    (hO : IsIso (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom))
    (hdim : ∀ y : Y, topologicalKrullDim (f.fiber y) ≤ 1)
    (hH1 : ∀ y : Y, IsZero (cohomologyOverField (Y.residueField y) (f.fiberToSpecResidueField y)
      (SheafOfModules.unit (f.fiber y).ringCatSheaf) 1)) :
    (∀ M N : Y.Modules,
      Stacks.SheafOfModules.IsInvertible Y.presheaf
        (structureSheafRing Y.toRingedSpace).property M →
      Stacks.SheafOfModules.IsInvertible Y.presheaf
        (structureSheafRing Y.toRingedSpace).property N →
      Nonempty ((Scheme.Modules.pullback f).obj M ≅ (Scheme.Modules.pullback f).obj N) →
      Nonempty (M ≅ N)) ∧
    ∀ L : X.Modules,
      Stacks.SheafOfModules.IsInvertible X.presheaf
        (structureSheafRing X.toRingedSpace).property L →
      ((∃ M : Y.Modules,
          Stacks.SheafOfModules.IsInvertible Y.presheaf
            (structureSheafRing Y.toRingedSpace).property M ∧
          Nonempty ((Scheme.Modules.pullback f).obj M ≅ L)) ↔
        ∀ y : Y, Nonempty ((Scheme.Modules.pullback (f.fiberι y)).obj L ≅
          SheafOfModules.unit (f.fiber y).ringCatSheaf)) := by
  have hO' : ∀ W : Y.Opens, IsIso (f.app W) := fun W =>
    (ConcreteCategory.isIso_iff_bijective _).mpr (ConcreteCategory.bijective_of_isIso
      (((Scheme.Modules.toPresheaf Y).mapIso
        (@asIso _ _ _ _ _ (show IsIso (C := Y.Modules)
          (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom) from hO))).app
        (op W)).hom)
  have hH1' : ∀ y : Y,
      IsZero ((coh (f.fiber y) 1).obj (SheafOfModules.unit (f.fiber y).ringCatSheaf)) :=
    fun y => ModuleCat.isZero_iff_subsingleton.mpr
      (@ModuleCat.subsingleton_of_isZero (Y.residueField y) _ _ (hH1 y))
  refine ⟨fun M N hM hN ⟨e⟩ => nonempty_iso_of_pullback_iso f hO' M N e, fun L hL => ⟨?_, ?_⟩⟩
  · rintro ⟨M, hM, ⟨e⟩⟩ y
    obtain ⟨e'⟩ := nonempty_fiber_pullback_iso_unit f M y
    exact ⟨((Scheme.Modules.pullback (f.fiberι y)).mapIso e).symm ≪≫ e'⟩
  · exact exists_pullback_iso_of_forall_fiber f hO' hdim hH1' L

end Stacks.PicardFibreTrivial

end
