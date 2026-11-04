module

public import Mathlib.Algebra.Category.ModuleCat.Descent
public import Mathlib.Algebra.Category.ModuleCat.Products
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import Mathlib.Algebra.DirectSum.Finsupp
public import Mathlib.RingTheory.Finiteness.Finsupp
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.CoherentSite
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.IdealTorsionFree
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackStalkColimit
public import StacksFrontier.AlgebraicGeometry.AffineQcohPushforward.Basic
public import StacksFrontier.AlgebraicGeometry.Descent.FlatBaseChangeComparison
public import StacksFrontier.AlgebraicGeometry.FlatBaseChangeCohomology.AffineDegreeZero.Modules
public import StacksFrontier.AlgebraicGeometry.Morphisms.Support.FiniteType
public import StacksFrontier.AlgebraicGeometry.Pullback.StalkFromSpecStalk
public import StacksFrontier.Topology.OpensMapFinal
public import StacksFrontier.Topology.Sheaves.Modules.Quasicoherent

/-!
# The counit of `f^* ⊣ f_*` over the local scheme at a point of the base

Let `f : X ⟶ S` be quasi-compact and quasi-separated with `𝒪_S = f_*𝒪_X`, let `s` be a point of
`S`, and suppose the pullback of a quasi-coherent `𝒪_X`-module `ℰ` to `X ×_S Spec 𝒪_{S,s}` is
free and of finite type. This file proves that the counit `f^*f_*ℰ ⟶ ℰ` is then an isomorphism
on stalks at every point of `X` lying over a generization of `s`. It is the step of the proof of
[Stacks, Tag 0EXG] that the source attributes to flat base change, [Stacks, Tag 02KH].

## Main results

* `AlgebraicGeometry.VectorBundleCodimensionOne.isIso_unit_app_unit_of_isIso_c`: `𝒪_S = f_*𝒪_X`
  makes the unit of `f^* ⊣ f_*` invertible at `𝒪_S`.
* `AlgebraicGeometry.VectorBundleCodimensionOne.isIso_unit_app_unit_of_isPullback`: that
  survives a flat base change.
* `AlgebraicGeometry.VectorBundleCodimensionOne.isIso_pullback_map_counit_of_isPullback`: the
  pullback of the counit along the top of a flat base-change square is invertible once the
  counit of the base change is.
* `AlgebraicGeometry.VectorBundleCodimensionOne.isIso_counit_app_of_iso_free`: the counit is
  invertible at a free module of finite rank once the unit is invertible at `𝒪_S`.
* `AlgebraicGeometry.VectorBundleCodimensionOne.finite_of_isFiniteType_free`: a free module of
  finite type on a nonempty scheme has a finite index set.
* `AlgebraicGeometry.VectorBundleCodimensionOne.isIso_stalk_of_isIso_pullback_map`: a morphism
  whose pullback along a flat morphism is invertible is invertible on stalks along its image.
* `AlgebraicGeometry.VectorBundleCodimensionOne.isIso_stalk_counit_of_iso_free`: the result.

## Implementation notes

`AlgebraicGeometry.Scheme.Modules` is a type synonym for sheaves of modules over
`X.ringCatSheaf`, and the two category instances agree only after unfolding it. Objects built
from Mathlib's `SheafOfModules` API are therefore given their `Scheme.Modules` type explicitly
before being rewritten with, and the instance `(SheafOfModules.pushforward φ).IsRightAdjoint`
that this API asks for is supplied from `Scheme.Modules.pullbackPushforwardAdjunction`.

## References

* [Stacks Project, Tag 02KH](https://stacks.math.columbia.edu/tag/02KH)
* [Stacks Project, Tag 0098](https://stacks.math.columbia.edu/tag/0098)
* [Stacks Project, Tag 01J7](https://stacks.math.columbia.edu/tag/01J7)
* [Stacks Project, Tag 0EXG](https://stacks.math.columbia.edu/tag/0EXG)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry.VectorBundleCodimensionOne

/-- The pushforward of sheaves of modules along `f` is a right adjoint. -/
private instance isRightAdjoint_pushforward_toRingCatSheafHom {X S : Scheme.{u}} (f : X ⟶ S) :
    (SheafOfModules.pushforward.{u} f.toRingCatSheafHom).IsRightAdjoint :=
  (Scheme.Modules.pullbackPushforwardAdjunction f).isRightAdjoint

private instance final_opens_map_base {X S : Scheme.{u}} (f : X ⟶ S) : (Opens.map f.base).Final :=
  Stacks.Topology.final_opensMap _

/-- The unit of `f^* ⊣ f_*` at the structure sheaf is invertible when the comparison map
`𝒪_S ⟶ f_*𝒪_X` is. -/
theorem isIso_unit_app_unit_of_isIso_c {X S : Scheme.{u}} (f : X ⟶ S)
    (hO : IsIso f.toLRSHom.toHom.c) :
    IsIso ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app
      (SheafOfModules.unit S.ringCatSheaf)) := by
  let O : S.Modules := SheafOfModules.unit S.ringCatSheaf
  let OX : X.Modules := SheafOfModules.unit X.ringCatSheaf
  let t : O ⟶ (Scheme.Modules.pushforward f).obj OX :=
    SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom
  have hunitTo : IsIso t := by
    rw [Scheme.Modules.Hom.isIso_iff_isIso_app]
    intro U
    have : IsIso (f.app U) := NatIso.isIso_app_of_isIso f.toLRSHom.toHom.c (op U)
    rw [ConcreteCategory.isIso_iff_bijective]
    exact (ConcreteCategory.isIso_iff_bijective (f.app U)).mp inferInstance
  let q : (Scheme.Modules.pullback f).obj O ⟶ OX :=
    SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom
  have heq : (Scheme.Modules.pullbackPushforwardAdjunction f).unit.app O ≫
      (Scheme.Modules.pushforward f).map q = t :=
    (Adjunction.homEquiv_unit _ _ _ _).symm.trans
      (SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit _)
  have : IsIso q := SheafOfModules.instIsIsoPullbackObjUnitToUnitOfFinal _
  have : IsIso ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app O ≫
      (Scheme.Modules.pushforward f).map q) := by
    rwa [heq]
  exact IsIso.of_isIso_comp_right _ ((Scheme.Modules.pushforward f).map q)

section BaseChange

variable {X S X' S' : Scheme.{u}} {f : X ⟶ S} {g : S' ⟶ S} {g' : X' ⟶ X} {f' : X' ⟶ S'}

/-- Invertibility of the unit at the structure sheaf passes along a flat base change. -/
theorem isIso_unit_app_unit_of_isPullback (H : IsPullback g' f' f g) [Flat g]
    [QuasiCompact f] [QuasiSeparated f]
    (h : IsIso ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app
      (SheafOfModules.unit S.ringCatSheaf))) :
    IsIso ((Scheme.Modules.pullbackPushforwardAdjunction f').unit.app
      (SheafOfModules.unit S'.ringCatSheaf)) := by
  let O : S.Modules := SheafOfModules.unit S.ringCatSheaf
  have : ((Scheme.Modules.pullback f).obj O).IsQuasicoherent :=
    @SheafOfModules.modulePullback_isQuasicoherent _ _ f.toLRSHom.toShHom O
      (Stacks.AlgebraicGeometry.AffineQcohPushforward.isQuasicoherent_unit S)
  have hbc := Stacks.AlgebraicGeometry.FlatBaseChangeCohomology.isIso_baseChangeNatTrans_of_flat
    H ((Scheme.Modules.pullback f).obj O)
  have key := Stacks.Modules.map_unit_comp_baseChangeNatTrans_app H.w O
  have : IsIso ((Scheme.Modules.pullbackPushforwardAdjunction f').unit.app
        ((Scheme.Modules.pullback g).obj O) ≫
      (Scheme.Modules.pushforward f').map
        ((Stacks.Modules.pullbackSquareIso f f' g g' H.w).hom.app O)) := by
    rw [← key]
    infer_instance
  have hu : IsIso ((Scheme.Modules.pullbackPushforwardAdjunction f').unit.app
      ((Scheme.Modules.pullback g).obj O)) :=
    IsIso.of_isIso_comp_right _ ((Scheme.Modules.pushforward f').map
      ((Stacks.Modules.pullbackSquareIso f f' g g' H.w).hom.app O))
  let q : (Scheme.Modules.pullback g).obj O ⟶ SheafOfModules.unit S'.ringCatSheaf :=
    SheafOfModules.pullbackObjUnitToUnit g.toRingCatSheafHom
  have : IsIso q := SheafOfModules.instIsIsoPullbackObjUnitToUnitOfFinal _
  exact (NatTrans.isIso_app_iff_of_iso (Scheme.Modules.pullbackPushforwardAdjunction f').unit
    (asIso q)).mp hu

/-- The counit of `f^* ⊣ f_*` at `ℰ` becomes invertible after pulling back along `g'` as soon as
the counit of the base change `f'` is invertible at the pullback of `ℰ`; this is flat base change
in degree zero, Tag 02KH. -/
theorem isIso_pullback_map_counit_of_isPullback (H : IsPullback g' f' f g) [Flat g]
    [QuasiCompact f] [QuasiSeparated f] (E : X.Modules) [E.IsQuasicoherent]
    (h : IsIso ((Scheme.Modules.pullbackPushforwardAdjunction f').counit.app
      ((Scheme.Modules.pullback g').obj E))) :
    IsIso ((Scheme.Modules.pullback g').map
      ((Scheme.Modules.pullbackPushforwardAdjunction f).counit.app E)) := by
  have hbc :=
    Stacks.AlgebraicGeometry.FlatBaseChangeCohomology.isIso_baseChangeNatTrans_of_flat H E
  have key := Stacks.Modules.pullback_map_baseChangeNatTrans_app_comp_counit H.w E
  have : IsIso ((Stacks.Modules.pullbackSquareIso f f' g g' H.w).hom.app
        ((Scheme.Modules.pushforward f).obj E) ≫
      (Scheme.Modules.pullback g').map
        ((Scheme.Modules.pullbackPushforwardAdjunction f).counit.app E)) := by
    rw [← key]
    infer_instance
  exact IsIso.of_isIso_comp_left
    ((Stacks.Modules.pullbackSquareIso f f' g g' H.w).hom.app
      ((Scheme.Modules.pushforward f).obj E)) _

end BaseChange

/-- If the unit of `f^* ⊣ f_*` is invertible at the structure sheaf, then the counit is
invertible at every module isomorphic to a free module of finite rank. -/
theorem isIso_counit_app_of_iso_free {X S : Scheme.{u}} (f : X ⟶ S)
    (h : IsIso ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app
      (SheafOfModules.unit S.ringCatSheaf)))
    (E : X.Modules) (I : Type u) [Finite I] (e : E ≅ SheafOfModules.free I) :
    IsIso ((Scheme.Modules.pullbackPushforwardAdjunction f).counit.app E) := by
  let adj := Scheme.Modules.pullbackPushforwardAdjunction f
  let K : Discrete I ⥤ S.Modules :=
    Discrete.functor (fun _ : I => SheafOfModules.unit S.ringCatSheaf)
  have (i : Discrete I) : IsIso ((K.whiskerLeft adj.unit).app i) := h
  have : IsIso (K.whiskerLeft adj.unit) := NatIso.isIso_of_isIso_app _
  let F : S.Modules := SheafOfModules.free I
  have hunit : IsIso (adj.unit.app F) :=
    isIso_app_coconePt_of_preservesColimit K adj.unit
      (SheafOfModules.freeCofan I) (SheafOfModules.isColimitFreeCofan I)
  have hcounit : IsIso (adj.counit.app ((Scheme.Modules.pullback f).obj F)) := by
    rw [← adj.inv_map_unit]
    infer_instance
  let e' : (Scheme.Modules.pullback f).obj F ≅ SheafOfModules.free I :=
    SheafOfModules.pullbackObjFreeIso f.toRingCatSheafHom I
  exact (NatTrans.isIso_app_iff_of_iso adj.counit (e ≪≫ e'.symm)).mpr hcounit

/-- A finitely generated module of finitely supported functions with values in a nonzero module
has a finite index type. -/
theorem finite_of_moduleFinite_finsupp {R N I : Type*} [Semiring R] [AddCommMonoid N]
    [Module R N] [Nontrivial N] [Module.Finite R (I →₀ N)] : Finite I := by
  classical
  obtain ⟨t, ht⟩ := Module.Finite.fg_top (R := R) (M := I →₀ N)
  have hs : (⋃ a ∈ (t : Set (I →₀ N)), (a.support : Set I)) = Set.univ := by
    refine Set.eq_univ_iff_forall.mpr fun i => ?_
    obtain ⟨n, hn⟩ := exists_ne (0 : N)
    have hmem : Finsupp.single i n ∈ Submodule.span R (t : Set (I →₀ N)) := by
      rw [ht]
      trivial
    have h := Finsupp.span_le_supported_biUnion_support (R := R) (t : Set (I →₀ N)) hmem
    exact ((Finsupp.mem_supported R _).mp h) (by simpa using hn)
  exact Set.finite_univ_iff.mp
    (hs ▸ t.finite_toSet.biUnion (fun a _ => a.support.finite_toSet))

/-- A free module `𝒪_X^{(I)}` of finite type on a scheme with a point has a finite index set: its
stalk at that point is `𝒪_{X,x}^{(I)}`, which is finitely generated only for finite `I`. -/
theorem finite_of_isFiniteType_free {X : Scheme.{u}} (x : X) (I : Type u)
    (hI : (SheafOfModules.free (R := X.ringCatSheaf) I).IsFiniteType) : Finite I := by
  classical
  let R := X.presheaf.stalk x
  let Fs := Stacks.ModuleSkyscraper.modulesStalkFunctor X x
  let U : X.Modules := SheafOfModules.unit X.ringCatSheaf
  let N := Fs.obj U
  let e : Fs.obj (∐ fun _ : I => U) ≅ ModuleCat.of R (DirectSum I fun _ => N) :=
    PreservesCoproduct.iso Fs (fun _ : I => U) ≪≫ ModuleCat.coprodIsoDirectSum _
  have hfin : Module.Finite R (Fs.obj (∐ fun _ : I => U)) :=
    SheafOfModules.finite_stalk X.sheaf (SheafOfModules.free I) x
  have : Module.Finite R (DirectSum I fun _ => N) := Module.Finite.equiv e.toLinearEquiv
  have : Module.Finite R (I →₀ N) := Module.Finite.equiv (finsuppLEquivDirectSum R N I).symm
  have : Nontrivial N :=
    (Stacks.IdealTorsion.unitStalkLinearEquiv X.toRingedSpace x).symm.injective.nontrivial
  exact finite_of_moduleFinite_finsupp (R := R) (N := N)

/-- A morphism of modules whose pullback along a flat morphism `g` is invertible is invertible on
stalks at the points of the image of `g`: the stalk of the pullback is the base change of the
stalk along the flat local homomorphism of local rings, which is faithfully flat. -/
theorem isIso_stalk_of_isIso_pullback_map {X Y : Scheme.{u}} (g : Y ⟶ X) [Flat g]
    {F G : X.Modules} (φ : F ⟶ G) (h : IsIso ((Scheme.Modules.pullback g).map φ)) (y : Y) :
    IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (g y)).map
      ((PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map φ.val)) := by
  let Fx := Stacks.ModuleSkyscraper.modulesStalkFunctor X (g y)
  let Fy := Stacks.ModuleSkyscraper.modulesStalkFunctor Y y
  have h2 : IsIso ((ModuleCat.extendScalars.{_, _, u} (g.stalkMap y).hom).map (Fx.map φ)) :=
    (NatIso.isIso_map_iff (Stacks.ModuleSkyscraper.pullbackStalkIso g y) φ).mpr
      (inferInstanceAs (IsIso (Fy.map ((Scheme.Modules.pullback g).map φ))))
  have hff : (g.stalkMap y).hom.FaithfullyFlat := by
    algebraize [(g.stalkMap y).hom]
    have : Module.FaithfullyFlat (X.presheaf.stalk (g y)) (Y.presheaf.stalk y) :=
      @Module.FaithfullyFlat.of_flat_of_isLocalHom _ _ _ _ _ _ _
        (Flat.stalkMap g y) (g.toLRSHom.prop y)
    exact ‹RingHom.FaithfullyFlat _›
  have := ModuleCat.reflectsIsomorphisms_extendScalars_of_faithfullyFlat hff
  have h3 : IsIso (Fx.map φ) :=
    isIso_of_reflects_iso _ (ModuleCat.extendScalars.{_, _, u} (g.stalkMap y).hom)
  rwa [ConcreteCategory.isIso_iff_bijective] at h3 ⊢

/-- **The counit over a point where `ℰ` is free on the local base.** Let `f : X ⟶ S` be
quasi-compact and quasi-separated with `𝒪_S = f_*𝒪_X`, let `s` be a point of `S` and suppose the
pullback of `ℰ` to `X ×_S Spec 𝒪_{S,s}` is free and of finite type. Then the counit
`f^*f_*ℰ ⟶ ℰ` is an isomorphism on stalks at every point `x` of `X` with `f x ⤳ s`.

By flat base change along `Spec 𝒪_{S,s} ⟶ S` (Tag 02KH in degree zero) the pullback of the counit
to `X ×_S Spec 𝒪_{S,s}` is the counit of the base-changed family at the pullback of `ℰ`, which is
invertible because that pullback is free of finite rank and `𝒪 = f_*𝒪` survives the base change.
The points of `X ×_S Spec 𝒪_{S,s}` lie over the points of `X` mapping to generizations of `s`
(Tag 01J7), and the stalk there of the pulled-back counit is the faithfully flat base change of
the stalk of the counit. -/
theorem isIso_stalk_counit_of_iso_free {X S : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f]
    [QuasiSeparated f] (hO : IsIso f.toLRSHom.toHom.c) (E : X.Modules) [E.IsQuasicoherent]
    (s : S) (I : Type u)
    (e : (Scheme.Modules.pullback (pullback.fst f (S.fromSpecStalk s))).obj E ≅
      SheafOfModules.free I)
    (hfin : ((Scheme.Modules.pullback (pullback.fst f (S.fromSpecStalk s))).obj E).IsFiniteType)
    (x : X) (hx : f x ⤳ s) :
    IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
      ((PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map
        ((Scheme.Modules.pullbackPushforwardAdjunction f).counit.app E).val)) := by
  let g := S.fromSpecStalk s
  have H : IsPullback (pullback.fst f g) (pullback.snd f g) f g := IsPullback.of_hasPullback f g
  have : Flat g := flat_fromSpecStalk S s
  obtain ⟨t, ht⟩ : f x ∈ Set.range g := by
    rwa [Scheme.range_fromSpecStalk]
  obtain ⟨x', hx', -⟩ := Scheme.Pullback.exists_preimage_pullback (f := f) (g := g) x t ht.symm
  have : Finite I := finite_of_isFiniteType_free x' I
    (Stacks.SheafOfModules.Site.isFiniteType_of_iso
      (R := (pullback f g).ringCatSheaf) e hfin)
  have hu := isIso_unit_app_unit_of_isPullback H (isIso_unit_app_unit_of_isIso_c f hO)
  have hc := isIso_counit_app_of_iso_free (pullback.snd f g) hu _ I e
  have hp := isIso_pullback_map_counit_of_isPullback H E hc
  have := isIso_stalk_of_isIso_pullback_map (pullback.fst f g) _ hp x'
  rwa [hx'] at this

end AlgebraicGeometry.VectorBundleCodimensionOne

end
