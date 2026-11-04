module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ThickeningPushoutModuleGluing
public import StacksFrontier.AlgebraicGeometry.FiberRank.FlatFibreFiniteFree
public import StacksFrontier.AlgebraicGeometry.Flatness.WeaklyAssociatedTensorPullback
public import StacksFrontier.AlgebraicGeometry.Divisors.RegularSectionAssociatedPoints
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.StalkwiseInvertibleDescent

/-!
# A module flat over a pushout along a thickening is invertible as soon as its restriction is

Let `i : X ⟶ X'` be a thickening, `f : X ⟶ Y` an affine morphism, `Y' = Y ⨿_X X'` the pushout
of [Stacks Project, Tag 07RT], `g : V' ⟶ Y'` flat and locally of finite presentation, and `M` an
`𝒪_{V'}`-module of finite presentation, flat over `Y'`, whose restriction to `V = Y ×_{Y'} V'` is
invertible. Then `M` is invertible. This is the "small point" of the proof of
[Stacks Project, Tag 0D44]: it is the argument of the source, by
[Stacks Project, Tag 080Q] and the observation that the fibres of `V' ⟶ Y'` are the fibres of
`V ⟶ Y`.

## The proof

At a point `x'` of `V'` over `s' ∈ Y'`:

* the point `Spec κ(s') ⟶ Y'` factors through the thickening `Y ⟶ Y'`
  (`Stacks.Pushout.exists_comp_eq_fromSpecResidueField`), so the fibre of `V ⟶ V' ⟶ Y'` over
  `s'` is the fibre of `V' ⟶ Y'` (`Stacks.Pushout.isIso_fiberHom_targetRestriction`), and the
  restriction of `M` to the fibre of `V' ⟶ Y'` is invertible;
* the fibrewise criterion of flatness (Stacks Tag 039C, the local engine of Tag 080Q) then makes
  the stalk `M_{x'}` flat, hence free of finite rank, over `𝒪_{V',x'}`;
* its rank is one, because its base change to `𝒪_{V,x}` for a point `x` of `V` over `x'` is the
  stalk of the restriction of `M` to `V`, which is free of rank one;
* a module of finite presentation all of whose stalks are invertible is invertible.

## Main results

* `Stacks.Pushout.isInvertible_of_isInvertible_pullback_targetRestriction`.

## References

* [Stacks Project, Tag 039C](https://stacks.math.columbia.edu/tag/039C)
* [Stacks Project, Tag 080Q](https://stacks.math.columbia.edu/tag/080Q)
* [Stacks Project, Tag 0D44](https://stacks.math.columbia.edu/tag/0D44)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.Pushout

open Stacks.Thickenings

/-- The residue field map of a closed immersion is an isomorphism. -/
theorem isIso_residueFieldMap_of_isClosedImmersion {S P : Scheme.{u}} (j : S ⟶ P)
    [IsClosedImmersion j] (s : S) : IsIso (j.residueFieldMap s) := by
  rw [ConcreteCategory.isIso_iff_bijective]
  refine ⟨(j.residueFieldMap s).hom.injective, fun b ↦ ?_⟩
  obtain ⟨c, rfl⟩ := S.residue_surjective s b
  obtain ⟨a, rfl⟩ := j.stalkMap_surjective s c
  exact ⟨P.residue (j s) a, congrArg (fun k ↦ k.hom a) (Scheme.residue_residueFieldMap j s)⟩

/-- **A point of the target of a surjective closed immersion factors through it.** -/
theorem exists_comp_eq_fromSpecResidueField {S P : Scheme.{u}} (j : S ⟶ P)
    [IsClosedImmersion j] (hj : Function.Surjective j) (s' : P) :
    ∃ l : Spec (P.residueField s') ⟶ S, l ≫ j = P.fromSpecResidueField s' := by
  obtain ⟨s, rfl⟩ := hj s'
  have := isIso_residueFieldMap_of_isClosedImmersion j s
  refine ⟨inv (Spec.map (j.residueFieldMap s)) ≫ S.fromSpecResidueField s, ?_⟩
  rw [Category.assoc, ← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField,
    IsIso.inv_hom_id_assoc]

/-- **The fibres of a base change along a surjective closed immersion are the fibres.** For a
surjective closed immersion `j : S ⟶ P` and any `g : V' ⟶ P`, the comparison of the fibre of
`S ×_P V' ⟶ V' ⟶ P` over a point `s'` of `P` with the fibre of `g` over `s'` is an isomorphism:
`Spec κ(s') ⟶ P` factors through `j`, so the fibre of `g` already maps to `S ×_P V'`. -/
theorem isIso_fiberHom_pullback_snd {S P V' : Scheme.{u}} (j : S ⟶ P) [IsClosedImmersion j]
    (hj : Function.Surjective j) (g : V' ⟶ P) (s' : P) :
    IsIso (Stacks.Flatness.fiberHom (pullback.snd j g) g s') := by
  obtain ⟨l, hl⟩ := exists_comp_eq_fromSpecResidueField j hj s'
  let σ : g.fiber s' ⟶ pullback j g :=
    pullback.lift (g.fiberToSpecResidueField s' ≫ l) (g.fiberι s')
      (by rw [Category.assoc, hl, Scheme.Hom.fiber_fac])
  have hσ : σ ≫ pullback.snd j g = g.fiberι s' := pullback.lift_snd _ _ _
  have hP := Stacks.Flatness.isPullback_fiberHom (pullback.snd j g) g s'
  have : IsClosedImmersion (pullback.snd j g) :=
    MorphismProperty.of_isPullback (IsPullback.of_hasPullback j g) inferInstance
  have : IsClosedImmersion (Stacks.Flatness.fiberHom (pullback.snd j g) g s') :=
    MorphismProperty.of_isPullback hP.flip inferInstance
  have : IsSplitEpi (Stacks.Flatness.fiberHom (pullback.snd j g) g s') :=
    IsSplitEpi.mk' ⟨hP.lift (𝟙 _) σ (by rw [Category.id_comp, hσ]), hP.lift_fst _ _ _⟩
  exact isIso_of_mono_of_isSplitEpi _

/-- A module isomorphic to the pullback of an invertible module is invertible. -/
private theorem isInvertible_of_iso_pullback {A B : Scheme.{u}} (ψ : A ⟶ B) (N : B.Modules)
    (P : A.Modules) (e : (Scheme.Modules.pullback ψ).obj N ≅ P)
    [AlgebraicGeometry.SheafOfModules.IsInvertible B.presheaf B.ringCatSheaf.2 N] :
    AlgebraicGeometry.SheafOfModules.IsInvertible A.presheaf A.ringCatSheaf.2 P :=
  have : AlgebraicGeometry.SheafOfModules.IsInvertible A.presheaf A.ringCatSheaf.2
      ((Scheme.Modules.pullback ψ).obj N) :=
    Stacks.RingedSpace.algebraicGeometryIsInvertible_modulePullback ψ.toLRSHom.toShHom _
  Stacks.SheafOfModules.isInvertible_of_iso _ _ e

/-- The pullback of an invertible module along an isomorphism detects invertibility. -/
theorem isInvertible_of_isInvertible_pullback_of_isIso {A B : Scheme.{u}} (φ : A ⟶ B) [IsIso φ]
    (N : B.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible A.presheaf A.ringCatSheaf.2
      ((Scheme.Modules.pullback φ).obj N)] :
    AlgebraicGeometry.SheafOfModules.IsInvertible B.presheaf B.ringCatSheaf.2 N :=
  isInvertible_of_iso_pullback (inv φ) _ N
    ((Scheme.Modules.pullbackComp (inv φ) φ).app N ≪≫
      (Scheme.Modules.pullbackCongr (IsIso.inv_hom_id φ)).app N ≪≫
        (Scheme.Modules.pullbackId B).app N)

/-- **The restriction to a fibre is invertible as soon as the restriction to a surjective closed
subscheme of the base is.** For a surjective closed immersion `j : S ⟶ P`, a morphism
`g : V' ⟶ P` and a module `M` on `V'` whose pullback to `S ×_P V'` is invertible, the
restriction of `M` to every fibre of `g` is invertible. -/
theorem isInvertible_pullback_fiberι {S P V' : Scheme.{u}} (j : S ⟶ P) [IsClosedImmersion j]
    (hj : Function.Surjective j) (g : V' ⟶ P) (s' : P) (M : V'.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible (pullback j g).presheaf
      (pullback j g).ringCatSheaf.2 ((Scheme.Modules.pullback (pullback.snd j g)).obj M)] :
    AlgebraicGeometry.SheafOfModules.IsInvertible (g.fiber s').presheaf
      (g.fiber s').ringCatSheaf.2 ((Scheme.Modules.pullback (g.fiberι s')).obj M) := by
  have := isIso_fiberHom_pullback_snd j hj g s'
  let φ := Stacks.Flatness.fiberHom (pullback.snd j g) g s'
  have : AlgebraicGeometry.SheafOfModules.IsInvertible
      ((pullback.snd j g ≫ g).fiber s').presheaf ((pullback.snd j g ≫ g).fiber s').ringCatSheaf.2
      ((Scheme.Modules.pullback φ).obj ((Scheme.Modules.pullback (g.fiberι s')).obj M)) :=
    isInvertible_of_iso_pullback ((pullback.snd j g ≫ g).fiberι s') _ _
      ((Scheme.Modules.pullbackComp ((pullback.snd j g ≫ g).fiberι s')
          (pullback.snd j g)).app M ≪≫
        (Scheme.Modules.pullbackCongr (Stacks.Flatness.fiberHom_fiberι _ g s')).symm.app M ≪≫
          ((Scheme.Modules.pullbackComp φ (g.fiberι s')).app M).symm)
  exact isInvertible_of_isInvertible_pullback_of_isIso φ _

/-- A free module of finite rank whose base change to a nontrivial algebra is free of rank one is
invertible. -/
theorem invertible_of_free_of_linearEquiv_baseChange {R S N : Type*} [CommRing R] [CommRing S]
    [Algebra R S] [Nontrivial S] [AddCommGroup N] [Module R N] [Module.Free R N]
    [Module.Finite R N] (e : S ≃ₗ[S] TensorProduct R S N) : Module.Invertible R N := by
  have := (algebraMap R S).domain_nontrivial
  have hrank : Module.finrank R N = 1 := by
    rw [← Module.finrank_baseChange (R := S), ← e.finrank_eq, Module.finrank_self]
  exact Module.Invertible.congr
    ((Module.finBasisOfFinrankEq _ _ hrank).equivFun.trans
      (LinearEquiv.funUnique (Fin 1) _ _)).symm

/-- **A module flat over the base and invertible on a surjective closed subscheme is invertible**
(the "small point" of Stacks 0D44, by Stacks 080Q). Let `j : S ⟶ P` be a surjective closed
immersion, `g : V' ⟶ P` locally of finite presentation, and `M` an `𝒪_{V'}`-module of finite
presentation, flat over `P`, whose pullback to `S ×_P V'` is invertible. Then `M` is invertible. -/
theorem isInvertible_of_isInvertible_pullback_snd {S P V' : Scheme.{u}} (j : S ⟶ P)
    [IsClosedImmersion j] (hj : Function.Surjective j) (g : V' ⟶ P)
    [LocallyOfFinitePresentation g] (M : V'.Modules) [M.IsFinitePresentation]
    (hflat : IsFlatOver g.toLRSHom.toShHom M)
    [AlgebraicGeometry.SheafOfModules.IsInvertible (pullback j g).presheaf
      (pullback j g).ringCatSheaf.2 ((Scheme.Modules.pullback (pullback.snd j g)).obj M)] :
    AlgebraicGeometry.SheafOfModules.IsInvertible V'.presheaf V'.ringCatSheaf.2 M := by
  have hfp : _root_.SheafOfModules.IsFinitePresentation
      (R := structureSheafRing V'.toRingedSpace) M := ‹M.IsFinitePresentation›
  refine Stacks.SheafOfModules.stalkwiseInvertibleDescent V'.toRingedSpace M hfp fun x' ↦ ?_
  let := Stacks.Flatness.stalkModule M x'
  have : Surjective j := ⟨hj⟩
  have : Surjective (pullback.snd j g) :=
    MorphismProperty.of_isPullback (IsPullback.of_hasPullback j g) inferInstance
  obtain ⟨x, hx⟩ := (pullback.snd j g).surjective x'
  -- the stalk of the restriction to `S ×_P V'` is a base change of `M_{x'}`, and is free of rank
  -- one
  let : Algebra (V'.presheaf.stalk x') ((pullback j g).presheaf.stalk x) :=
    (((pullback.snd j g).stalkMap x).hom.comp
      (V'.presheaf.stalkCongr (.of_eq hx.symm)).hom.hom).toAlgebra
  obtain ⟨e₁⟩ := Stacks.Divisors.exists_modulePullbackStalkLinearEquiv_of_eq
    (pullback.snd j g) M x x' hx
  have : AlgebraicGeometry.SheafOfModules.IsInvertible (pullback j g).sheaf.obj
      (pullback j g).ringCatSheaf.property
      ((Scheme.Modules.pullback (pullback.snd j g)).obj M) := ‹_›
  obtain ⟨e₂⟩ := Stacks.Divisors.nonempty_stalk_linearEquiv_of_isInvertible
    ((Scheme.Modules.pullback (pullback.snd j g)).obj M) x
  let e := e₂.symm.trans e₁
  have : IsLocalRing (V'.presheaf.stalk x') := V'.isLocalRing x'
  have : IsLocalRing ((pullback j g).presheaf.stalk x) := (pullback j g).isLocalRing x
  have hnz : ∃ a : TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) M.val.presheaf x', a ≠ 0 := by
    by_contra hn
    push Not at hn
    have : Subsingleton (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) M.val.presheaf x') :=
      ⟨fun a b ↦ by rw [hn a, hn b]⟩
    exact (not_subsingleton ((pullback j g).presheaf.stalk x)) e.toEquiv.subsingleton
  have := isInvertible_pullback_fiberι j hj g (g x') M
  have hF := (flatQuasicoherent_of_isInvertible (𝟙 (g.fiber (g x')))
    ((Scheme.Modules.pullback (g.fiberι (g x'))).obj M)).2
  have hfiber := (AlgebraicGeometry.isFlatOverAt_id_iff
    ((Scheme.Modules.pullback (g.fiberι (g x'))).obj M) (g.asFiber x')).mp (hF _)
  have hflatN := AlgebraicGeometry.Scheme.Modules.flat_stalk_of_isFlatOverAt_of_flat_fiber_stalk
    g M x' hnz (hflat x') hfiber
  have : _root_.SheafOfModules.IsFiniteType.{u, u, u} M :=
    _root_.SheafOfModules.instIsFiniteTypeOfIsFinitePresentation M
  have hfin : Module.Finite (V'.presheaf.stalk x')
      (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) M.val.presheaf x') :=
    _root_.SheafOfModules.finite_stalk V'.sheaf M x'
  have : Module.Free (V'.presheaf.stalk x')
      (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) M.val.presheaf x') :=
    Module.free_of_flat_of_isLocalRing
  exact invertible_of_free_of_linearEquiv_baseChange (R := V'.presheaf.stalk x')
    (N := TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) M.val.presheaf x') e

end Stacks.Pushout

end
