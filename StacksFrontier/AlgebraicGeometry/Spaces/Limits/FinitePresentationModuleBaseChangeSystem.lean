module

public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.FinitePresentationModuleLimitSpace
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineHomTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.MapDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactEtaleLocalTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactSupport

/-!
# Systems of base changes along a limit of algebraic spaces

Let `D` be a cofiltered inverse system of algebraic spaces with affine transition morphisms and
let `r : R ⟶ D i` be a morphism of algebraic spaces into a stage.  The base changes
`R_j = D j ×_{D i} R` of the later stages form again such a system, indexed by `Over i`, whose
limit is the base change `(lim D) ×_{D i} R`. This file records that system and proves the
faithfulness clause of Stacks 07V7 for it, phrased for morphisms of inverse images of two
modules on `D i` along `r`.

## Main definitions

* `AlgebraicGeometry.Space.stageBaseChangeSystem`: the system `j ↦ D j ×_{D i} R`.

## Main results

* `AlgebraicGeometry.Space.siteContainsBaseChangeLimits_stageBaseChangeSystem` and
  `AlgebraicGeometry.Space.hasSiteLimit_stageBaseChangeSystem`: the system of base changes
  inherits the standing hypothesis `AlgebraicGeometry.Space.HasSiteLimit`, its charts being
  charts of the original system (`AlgebraicGeometry.Space.stageBaseChangeChartIso`).
* `AlgebraicGeometry.Space.eventually_map_eq_of_baseChange`: the faithfulness clause
  for a system of base changes.

## References

* [Stacks Project, Tag 07V7](https://stacks.math.columbia.edu/tag/07V7)
* [Stacks Project, Tag 07SF](https://stacks.math.columbia.edu/tag/07SF)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Cardinal

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

set_option synthInstance.maxHeartbeats 400000 in
/-- Pullbacks of presheaves on the big fppf site over `S` (instance search times out without
this shortcut). -/
local instance hasPullbacks_presheaf_FinitePresentationModuleBaseChangeSystem :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := inferInstance

/-- Pullbacks of presheaves on the big fppf site over `S`, as a high-priority shortcut. -/
local instance (priority := high) hasPullback_presheaf_FinitePresentationModuleBaseChangeSystem
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

/-- The morphisms of a slice category are no more numerous than those of the category. -/
theorem mk_over_hom_lt {I : Type u} [Category.{u} I] {κ : Cardinal.{u}}
    (hhom : ∀ j j' : I, #(j ⟶ j') < κ) {i : I} (a b : Over i) : #(a ⟶ b) < κ :=
  (Cardinal.mk_le_of_injective (f := fun g : a ⟶ b => g.left)
    (fun _ _ h => Over.OverMorphism.ext h)).trans_lt (hhom _ _)

section System

variable {I : Type u} [Category.{u} I] (D : I ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (i : I)
  {R : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (r : R ⟶ D.obj i)

/-- The system of base changes `j ↦ D j ×_{D i} R` of the stages above `i` along `r`. -/
noncomputable abbrev stageBaseChangeSystem : Over i ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u :=
  (Over.post (X := i) D ⋙ Over.pullback r) ⋙ Over.forget R

/-- The projection of a member of the system of base changes to its stage. -/
noncomputable def stageBaseChangeSystemFst (j : Over i) :
    (stageBaseChangeSystem B S hS D i r).obj j ⟶ D.obj j.left :=
  pullback.fst (D.map j.hom) r

/-- The projection of a member of the system of base changes to `R`. -/
noncomputable def stageBaseChangeSystemSnd (j : Over i) :
    (stageBaseChangeSystem B S hS D i r).obj j ⟶ R :=
  pullback.snd (D.map j.hom) r

/-- Each member `D j ×_{D i} R` of the system of base changes, with its two projections, is a
pullback of `D j ⟶ D i` along `r`. -/
theorem isPullback_stageBaseChangeSystem (j : Over i) :
    IsPullback (stageBaseChangeSystemFst B S hS D i r j) (stageBaseChangeSystemSnd B S hS D i r j)
      (D.map j.hom) r :=
  IsPullback.of_hasPullback _ _

/-- The transition morphisms of the system of base changes commute with the projections to the
stages of `D`. -/
theorem stageBaseChangeSystem_map_comp_fst {j k : Over i} (g : j ⟶ k) :
    (stageBaseChangeSystem B S hS D i r).map g ≫ stageBaseChangeSystemFst B S hS D i r k =
      stageBaseChangeSystemFst B S hS D i r j ≫ D.map g.left := by
  dsimp [stageBaseChangeSystemFst, Over.pullback, Over.post]
  exact pullback.lift_fst _ _ _

/-- The transition morphisms of the system of base changes commute with the projections to `R`. -/
theorem stageBaseChangeSystem_map_comp_snd {j k : Over i} (g : j ⟶ k) :
    (stageBaseChangeSystem B S hS D i r).map g ≫ stageBaseChangeSystemSnd B S hS D i r k =
      stageBaseChangeSystemSnd B S hS D i r j := by
  dsimp [stageBaseChangeSystemSnd, Over.pullback, Over.post]
  exact pullback.lift_snd _ _ _

/-- A transition morphism of the system of base changes is a base change of the corresponding
transition morphism of `D`. -/
theorem isPullback_stageBaseChangeSystem_map {j k : Over i} (g : j ⟶ k) :
    IsPullback ((stageBaseChangeSystem B S hS D i r).map g)
      (stageBaseChangeSystemFst B S hS D i r j) (stageBaseChangeSystemFst B S hS D i r k)
      (D.map g.left) := by
  refine IsPullback.of_right ?_ (stageBaseChangeSystem_map_comp_fst B S hS D i r g)
    (isPullback_stageBaseChangeSystem B S hS D i r k).flip
  have h := (isPullback_stageBaseChangeSystem B S hS D i r j).flip
  rw [stageBaseChangeSystem_map_comp_snd]
  convert h using 2
  rw [← D.map_comp, Over.w g]

/-- The transition morphisms of the system of base changes are affine. -/
theorem isAffineHom_stageBaseChangeSystem_map
    (hAffine : ∀ {i j : I} (f : i ⟶ j), IsAffineHom B S hS (D.map f)) {j k : Over i}
    (g : j ⟶ k) : IsAffineHom B S hS ((stageBaseChangeSystem B S hS D i r).map g) :=
  IsAffineHom.of_isPullback (isPullback_stageBaseChangeSystem_map B S hS D i r g).flip (hAffine _)

/-- The canonical cone on the system of base changes, with vertex the base change of the limit,
is compatible with the projections to `R`. -/
theorem baseChangeCone_π_comp_snd (j : Over i) :
    ((Over.forget R).mapCone ((Over.pullback r).mapCone ((limit.cone D).overPost i))).π.app j ≫
        stageBaseChangeSystemSnd B S hS D i r j = pullback.snd (limit.π D i) r := by
  dsimp [stageBaseChangeSystemSnd, Over.pullback, Over.post, Cone.overPost]
  simp only [Over.homMk_left, pullback.lift_snd]

/-- **The charts of a system of base changes are charts of the original system.** A chart
`D'_k ×_{D'_j} U₀` of the system `D' = stageBaseChangeSystem D i r` at a stage `j` and an affine
point `f₀ : U₀ ⟶ D'_j` is the chart `D_{k} ×_{D_j} U₀` of `D` at the point `f₀ ≫ (D'_j ⟶ D_j)`,
naturally in `k`, the index categories being identified by
`CategoryTheory.Over.iteratedSliceEquiv`. -/
noncomputable def stageBaseChangeChartIso
    (hAffine : ∀ {i j : I} (f : i ⟶ j), IsAffineHom B S hS (D.map f)) (j : Over i)
    {U₀ : BigAffineFppf B S hS}
    {f₀ : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj U₀) ⟶
      (stageBaseChangeSystem B S hS D i r).obj j}
    (C : AffineChartSystem B S hS j (stageBaseChangeSystem B S hS D i r) U₀ f₀) :
    C.siteDiagram ≅ (Over.iteratedSliceEquiv j).functor ⋙
      (affineChartSystem B S hS j.left D U₀ (f₀ ≫ stageBaseChangeSystemFst B S hS D i r j)
        hAffine).siteDiagram :=
  let C' := affineChartSystem B S hS j.left D U₀ (f₀ ≫ stageBaseChangeSystemFst B S hS D i r j)
    hAffine
  let P : ∀ k : Over j, IsPullback (C.stageMap k ≫ stageBaseChangeSystemFst B S hS D i r k.left)
      (C.baseMap k) (D.map k.hom.left) (f₀ ≫ stageBaseChangeSystemFst B S hS D i r j) :=
    fun k => (C.isPullback k).paste_horiz
      (isPullback_stageBaseChangeSystem_map B S hS D i r k.hom).flip
  let e : ∀ k : Over j, (C.siteDiagram ⋙ yoneda).obj k ≅
      (C'.siteDiagram ⋙ yoneda).obj ((Over.iteratedSliceEquiv j).functor.obj k) :=
    fun k => (P k).isoIsPullback _ _ (C'.isPullback ((Over.iteratedSliceEquiv j).functor.obj k))
  have he₁ : ∀ k : Over j, (e k).hom ≫ C'.stageMap ((Over.iteratedSliceEquiv j).functor.obj k) =
      C.stageMap k ≫ stageBaseChangeSystemFst B S hS D i r k.left :=
    fun k => IsPullback.isoIsPullback_hom_fst _ _ _ _
  have he₂ : ∀ k : Over j, (e k).hom ≫ C'.baseMap ((Over.iteratedSliceEquiv j).functor.obj k) =
      C.baseMap k :=
    fun k => IsPullback.isoIsPullback_hom_snd _ _ _ _
  NatIso.ofComponents (fun k => yoneda.preimageIso (e k)) (by
    intro k k' m
    apply yoneda.map_injective
    rw [Functor.map_comp, Functor.map_comp, Functor.preimageIso_hom, Functor.preimageIso_hom,
      Functor.map_preimage, Functor.map_preimage]
    change yoneda.map (C.siteDiagram.map m) ≫ (e k').hom =
      (e k).hom ≫ yoneda.map (C'.siteDiagram.map ((Over.iteratedSliceEquiv j).functor.map m))
    apply (C'.isPullback ((Over.iteratedSliceEquiv j).functor.obj k')).hom_ext
    · have h1 : yoneda.map (C.siteDiagram.map m) ≫ C.stageMap k' ≫
          stageBaseChangeSystemFst B S hS D i r k'.left =
          C.stageMap k ≫ stageBaseChangeSystemFst B S hS D i r k.left ≫ D.map m.left.left := by
        rw [← Category.assoc, ← C.stageMap_comp_map m, Category.assoc,
          stageBaseChangeSystem_map_comp_fst]
      rw [Category.assoc, Category.assoc, he₁ k', ← C'.stageMap_comp_map,
        ← Category.assoc (e k).hom, he₁ k]
      exact h1.trans (Category.assoc _ _ _).symm
    · rw [Category.assoc, Category.assoc, he₂ k', C'.map_baseMap, he₂ k, C.map_baseMap])

/-- **A system of base changes inherits the condition that the charts have their limits inside
the site**: its charts are charts of the original system. -/
theorem siteContainsBaseChangeLimits_stageBaseChangeSystem [IsCofiltered I]
    (hAffine : ∀ {i j : I} (f : i ⟶ j), IsAffineHom B S hS (D.map f))
    (hL : SiteContainsBaseChangeLimits B S hS D) :
    SiteContainsBaseChangeLimits B S hS (stageBaseChangeSystem B S hS D i r) :=
  (siteContainsBaseChangeLimits_iff _).2 fun j U₀ _ C =>
    exists_isLimit_contains_of_iso (Over.iteratedSliceEquiv j)
      (Functor.isoWhiskerRight (stageBaseChangeChartIso B S hS D i r hAffine j C)
        (BigFppfOver.toScheme B S hS) ≪≫ Functor.associator _ _ _)
      ((siteContainsBaseChangeLimits_iff D).1 hL j.left U₀ _ _)

end System

/-! ### Faithfulness -/

section Faithfulness

variable {I : Type u} [Category.{u} I] [IsCofiltered I] (D : I ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
  (hL : HasSiteLimit B S hS D) (hD : ∀ i, IsAlgebraicSpace B S hS (D.obj i))

variable {i : I} (R : AlgebraicSpaces B S hS) (r : R ⟶ stageAlgebraicSpace B S hS D hD i)

omit [IsCofiltered I] in
/-- The members of the system of base changes along `r` are algebraic spaces. -/
theorem isAlgebraicSpace_stageBaseChangeSystem (j : Over i) :
    IsAlgebraicSpace B S hS ((stageBaseChangeSystem B S hS D i r.hom).obj j) :=
  isAlgebraicSpace_pullback B S hS _ _ (hD j.left) R.2 (hD i)

include hL in
/-- The system of base changes along `r` has its limit inside the site: the limit is the base
change of the limit of `D`, an algebraic space, and the charts are charts of `D`. -/
theorem hasSiteLimit_stageBaseChangeSystem :
    HasSiteLimit B S hS (stageBaseChangeSystem B S hS D i r.hom) :=
  ⟨fun g => isAffineHom_stageBaseChangeSystem_map B S hS D i r.hom hL.1 g,
    IsAlgebraicSpace.of_iso (isAlgebraicSpace_pullback B S hS _ _ hL.2.1 R.2 (hD i))
      ((isLimitPullbackLimitOverPost B S hS D i r.hom).conePointUniqueUpToIso
        (limit.isLimit _)),
    siteContainsBaseChangeLimits_stageBaseChangeSystem B S hS D i r.hom hL.1 hL.2.2⟩

/-- The projection of a member of the system of base changes to `R`. -/
noncomputable def stageBaseChangeSpaceSnd (j : Over i) :
    stageAlgebraicSpace B S hS (stageBaseChangeSystem B S hS D i r.hom)
      (isAlgebraicSpace_stageBaseChangeSystem B S hS D hD R r) j ⟶ R :=
  ObjectProperty.homMk (stageBaseChangeSystemSnd B S hS D i r.hom j)

/-- The base change of the limit along `r`, as an algebraic space. -/
noncomputable abbrev limitBaseChangeSpace : AlgebraicSpaces B S hS :=
  ⟨pullback (limit.π D i) r.hom, isAlgebraicSpace_pullback B S hS _ _
    (limitSpace B S hS D hL).2 R.2 (hD i)⟩

/-- The projection of the base change of the limit to `R`. -/
noncomputable def limitBaseChangeSnd :
    limitBaseChangeSpace B S hS D hL hD R r ⟶ R :=
  ObjectProperty.homMk (pullback.snd (limit.π D i) r.hom)

/-- The projection of the base change of the limit to the limit. -/
noncomputable def limitBaseChangeFst :
    limitBaseChangeSpace B S hS D hL hD R r ⟶
      limitSpace B S hS D hL :=
  ObjectProperty.homMk (pullback.fst (limit.π D i) r.hom)

omit [IsCofiltered I] in
/-- The square formed by the two projections of the base change of the limit along `r` commutes. -/
theorem limitBaseChangeFst_comp :
    limitBaseChangeFst B S hS D hL hD R r ≫
        limitSpaceProjection B S hS D hL hD i =
      limitBaseChangeSnd B S hS D hL hD R r ≫ r :=
  ObjectProperty.hom_ext _ pullback.condition

/-- The isomorphism of the chosen limit of the system of base changes with the base change of the
limit. -/
noncomputable def limitBaseChangeSystemIso :
    limitSpace B S hS (stageBaseChangeSystem B S hS D i r.hom)
        (hasSiteLimit_stageBaseChangeSystem B S hS D hL hD R r) ⟶
      limitBaseChangeSpace B S hS D hL hD R r :=
  ObjectProperty.homMk ((limit.isLimit _).conePointUniqueUpToIso
    (isLimitPullbackLimitOverPost B S hS D i r.hom)).hom

/-- The isomorphism `limitBaseChangeSystemIso` is compatible with the projections to `R`. -/
theorem limitBaseChangeSystemIso_comp_snd (j : Over i) :
    limitBaseChangeSystemIso B S hS D hL hD R r ≫
        limitBaseChangeSnd B S hS D hL hD R r =
      limitSpaceProjection B S hS (stageBaseChangeSystem B S hS D i r.hom)
          (hasSiteLimit_stageBaseChangeSystem B S hS D hL hD R r)
          (isAlgebraicSpace_stageBaseChangeSystem B S hS D hD R r) j ≫
        stageBaseChangeSpaceSnd B S hS D hD R r j := by
  apply ObjectProperty.hom_ext
  show ((limit.isLimit _).conePointUniqueUpToIso
      (isLimitPullbackLimitOverPost B S hS D i r.hom)).hom ≫ pullback.snd (limit.π D i) r.hom =
    limit.π (stageBaseChangeSystem B S hS D i r.hom) j ≫ stageBaseChangeSystemSnd B S hS D i r.hom j
  rw [← baseChangeCone_π_comp_snd B S hS D i r.hom j, ← Category.assoc,
    IsLimit.conePointUniqueUpToIso_hom_comp]
  rfl

omit [IsCofiltered I] in
/-- Inverse images along a composite: two morphisms with equal inverse images along a composite
have equal iterated inverse images. -/
theorem map_map_eq_of_map_comp_eq {X Y Z : AlgebraicSpaces B S hS} (f : X ⟶ Y) (g : Y ⟶ Z)
    {M N : Modules.{u, u} B S hS Z.1 Z.2} {x y : M ⟶ N}
    (h : (modulePullback B S hS (f ≫ g)).map x = (modulePullback B S hS (f ≫ g)).map y) :
    (modulePullback B S hS f).map ((modulePullback B S hS g).map x) =
      (modulePullback B S hS f).map ((modulePullback B S hS g).map y) :=
  Stacks.AlgebraicGeometry.ModuleLimits.map_eq_of_natIso
    (modulePullbackCompIso B S hS f g).symm h

omit [IsCofiltered I] in
/-- Inverse images along a composite: two morphisms with equal iterated inverse images have equal
inverse images along the composite. -/
theorem map_comp_eq_of_map_map_eq {X Y Z : AlgebraicSpaces B S hS} (f : X ⟶ Y) (g : Y ⟶ Z)
    {M N : Modules.{u, u} B S hS Z.1 Z.2} {x y : M ⟶ N}
    (h : (modulePullback B S hS f).map ((modulePullback B S hS g).map x) =
      (modulePullback B S hS f).map ((modulePullback B S hS g).map y)) :
    (modulePullback B S hS (f ≫ g)).map x = (modulePullback B S hS (f ≫ g)).map y :=
  Stacks.AlgebraicGeometry.ModuleLimits.map_eq_of_natIso (modulePullbackCompIso B S hS f g) h

/-- **The faithfulness clause of Stacks 07V7 for a system of base changes.**  Let `r : R ⟶ X_i`
be a morphism from a quasi-compact algebraic space and let `x, y : r^*M ⟶ r^*N` be two
morphisms of inverse images of finitely presented `𝒪_{X_i}`-modules.  If their inverse images to
the base change `X ×_{X_i} R` of the limit agree, then so do their inverse images to the base
change `X_j ×_{X_i} R` of some later stage. -/
theorem eventually_map_eq_of_baseChange (hRqc : IsQuasiCompactSpace B S hS R.1)
    {M N : Modules.{u, u} B S hS (stageAlgebraicSpace B S hS D hD i).1
      (stageAlgebraicSpace B S hS D hD i).2}
    (hM : M.IsFinitePresentationOnSite) (hN : N.IsFinitePresentationOnSite)
    (x y : (modulePullback B S hS r).obj M ⟶ (modulePullback B S hS r).obj N)
    (h : (modulePullback B S hS (limitBaseChangeSnd B S hS D hL hD R r)).map x =
      (modulePullback B S hS (limitBaseChangeSnd B S hS D hL hD R r)).map y) :
    ∃ j : Over i,
      (modulePullback B S hS (stageBaseChangeSpaceSnd B S hS D hD R r j)).map x =
        (modulePullback B S hS (stageBaseChangeSpaceSnd B S hS D hD R r j)).map y := by
  have hqc : IsQuasiCompactSpace B S hS
      ((stageBaseChangeSystem B S hS D i r.hom).obj (Over.mk (𝟙 i))) := by
    have hP : IsPullback (pullback.fst (D.map (𝟙 i)) r.hom) (pullback.snd (D.map (𝟙 i)) r.hom)
        (𝟙 _) r.hom := by
      simpa only [D.map_id] using IsPullback.of_hasPullback (D.map (𝟙 i)) r.hom
    exact isQuasiCompactSpace_of_iso B S hS
      (hP.isoIsPullback _ _ (IsPullback.id_vert r.hom)).symm hRqc
  have h1 := map_comp_eq_of_map_map_eq B S hS
    (limitBaseChangeSystemIso B S hS D hL hD R r)
    (limitBaseChangeSnd B S hS D hL hD R r) (x := x) (y := y) (by rw [h])
  rw [limitBaseChangeSystemIso_comp_snd B S hS D hL hD R r (Over.mk (𝟙 i))]
    at h1
  have h2 := map_map_eq_of_map_comp_eq B S hS _ _ h1
  obtain ⟨k, e, hk⟩ := eventually_eq_of_modulePullback_limitSpaceProjection_eq B S hS _
    (hasSiteLimit_stageBaseChangeSystem B S hS D hL hD R r)
    (isAlgebraicSpace_stageBaseChangeSystem B S hS D hD R r) (Over.mk (𝟙 i)) hqc
    _ _ (isFinitePresentationOnSite_modulePullback B S hS _ _
      (isFinitePresentationOnSite_modulePullback B S hS r M hM))
    (isFinitePresentationOnSite_modulePullback B S hS _ _
      (isFinitePresentationOnSite_modulePullback B S hS r N hN)) _ _ h2
  refine ⟨k, ?_⟩
  have he : stageTransition B S hS _ (isAlgebraicSpace_stageBaseChangeSystem B S hS D hD R r) e ≫
      stageBaseChangeSpaceSnd B S hS D hD R r (Over.mk (𝟙 i)) =
      stageBaseChangeSpaceSnd B S hS D hD R r k :=
    ObjectProperty.hom_ext _ (stageBaseChangeSystem_map_comp_snd B S hS D i r.hom e)
  have h3 := map_comp_eq_of_map_map_eq B S hS _ _ hk
  rw [he] at h3
  exact h3

end Faithfulness

end AlgebraicGeometry.Space

end
