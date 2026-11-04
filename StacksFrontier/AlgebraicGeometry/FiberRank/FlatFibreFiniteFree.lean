module

public import Mathlib.RingTheory.LocalRing.Module
public import StacksFrontier.AlgebraicGeometry.Modules.FiniteLocallyFreeDescent.FlatFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Morphisms.FinitePresentationPoint
public import StacksFrontier.AlgebraicGeometry.Morphisms.Flat.FibrewiseFiber
public import StacksFrontier.AlgebraicGeometry.Morphisms.Flat.IsoTransport
public import StacksFrontier.AlgebraicGeometry.Morphisms.FlatMorphisms.PullbackFlatness
import StacksCore.Tactic.StacksAttribute

/-!
# A module flat over the base with flat fibre stalk is finite free near the point

Let `f : X ⟶ S` be a morphism of finite presentation, let `F` be a finitely presented
`𝒪_X`-module and let `x` be a point of `X`. If `F` is flat over `S` at `x` and the stalk at `x`
of the restriction of `F` to the fibre `X_{f(x)}` is a flat module over the local ring of that
fibre, then `F` is free of finite rank on an open neighbourhood of `x`. This is Stacks Tag 080Q.

The two hypotheses are exactly condition (1) of the fibrewise criterion for flatness
(Stacks Tag 039C) for the pair `𝟙 X, f`, whose condition (2) at the identity is flatness of the
stalk `F_x` over `𝒪_{X,x}`. A finite flat module over a local ring is free
(Stacks Tag 00NZ), and a finitely presented module with a free stalk of finite rank is free on a
neighbourhood (Stacks Tag 0B8J).

## Main results

* `AlgebraicGeometry.isFlatOverAt_id_iff`: flatness of a module over the identity morphism of a
  ringed space at a point is flatness of its stalk over the local ring at that point.
* `AlgebraicGeometry.Scheme.Modules.flat_stalk_of_isFlatOverAt_of_flat_fiber_stalk`: the
  fibrewise criterion at the identity, giving flatness of the stalk.
* `AlgebraicGeometry.Scheme.Modules.exists_iso_free_over_of_flat_over_at_of_flat_fiber_stalk`:
  **Stacks Tag 080Q.**

## Implementation notes

Instantiating Stacks Tag 039C at `𝟙 X` means comparing the fibre of `𝟙 X ≫ f` with the fibre of
`f`. The comparison morphism is `Stacks.Flatness.fiberHom (𝟙 X) f (f x)`, an isomorphism because
it is the base change of `𝟙 X` along the inclusion of the fibre; flatness of the fibre module
crosses it by the pointwise form of Stacks Tag 02JZ, and the resulting identification of
pullbacks is the composite of `Scheme.Modules.pullbackComp` with `Scheme.Modules.pullbackCongr`,
along which flatness travels by `AlgebraicGeometry.isFlatOverAt_iff_of_moduleIso`.

The subsingleton stalk is treated separately only because Stacks Tag 039C assumes a nonzero
stalk; a zero stalk is free of rank `0`, which is what the trivialisation consumes.

## References

* [Stacks Project, Tag 080Q](https://stacks.math.columbia.edu/tag/080Q)
* [Stacks Project, Tag 039C](https://stacks.math.columbia.edu/tag/039C)
* [Stacks Project, Tag 00NZ](https://stacks.math.columbia.edu/tag/00NZ)
* [Stacks Project, Tag 0B8J](https://stacks.math.columbia.edu/tag/0B8J)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open RingedSpaceModuleAdjunction

universe u

namespace AlgebraicGeometry

/-- Flatness of an `𝒪_X`-module over the identity morphism of a ringed space at a point is
flatness of its stalk there over the local ring of the space, the scalars being restricted
along the identity. -/
theorem isFlatOverAt_id_iff {X : RingedSpace.{u}} (F : SheafOfModules.{u} (structureSheafRing X))
    (x : X) :
    AlgebraicGeometry.IsFlatOverAt (𝟙 X) F x ↔
      letI := Stacks.Flatness.stalkModule F x
      Module.Flat (ToType (X.presheaf.stalk x))
        (ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) F.val.presheaf x)) := by
  let : Module (ToType (X.presheaf.stalk x))
      (ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) F.val.presheaf x)) :=
    Stacks.Flatness.stalkModule F x
  have hstalk : ((𝟙 X : X ⟶ X).hom.stalkMap x).hom = RingHom.id _ := by simp; rfl
  change
      (let := Module.compHom
          (ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) F.val.presheaf x))
          ((𝟙 X : X ⟶ X).hom.stalkMap x).hom
       Module.Flat (ToType (X.presheaf.stalk ((𝟙 X : X ⟶ X).hom.base x)))
         (ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) F.val.presheaf x))) ↔ _
  rw [hstalk]
  exact Iff.rfl

end AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules

/-- The morphism `X_{f(x)} ⟶ X_{f(x)}` comparing the fibre of `𝟙 X ≫ f` with the fibre of `f` is
an isomorphism: it is the base change of `𝟙 X` along the inclusion of the fibre of `f`. -/
theorem isIso_fiberHom_id {X S : Scheme.{u}} (f : X ⟶ S) (s : S) :
    IsIso (Stacks.Flatness.fiberHom (𝟙 X) f s) := by
  have h : IsPullback (Stacks.Flatness.fiberHom (𝟙 X) f s) ((𝟙 X ≫ f).fiberι s)
      (f.fiberι s) (𝟙 X) := by
    refine IsPullback.of_right ?_ (Limits.pullback.lift_fst ..)
      (IsPullback.of_hasPullback f (S.fromSpecResidueField s)).flip
    change IsPullback (Stacks.Flatness.fiberHom (𝟙 X) f s ≫ f.fiberToSpecResidueField s)
      ((𝟙 X ≫ f).fiberι s) (S.fromSpecResidueField s) (𝟙 X ≫ f)
    rw [show Stacks.Flatness.fiberHom (𝟙 X) f s ≫ f.fiberToSpecResidueField s =
        (𝟙 X ≫ f).fiberToSpecResidueField s from Limits.pullback.lift_snd ..]
    exact (IsPullback.of_hasPullback (𝟙 X ≫ f) (S.fromSpecResidueField s)).flip
  exact h.isIso_fst_of_isIso

/-- **Stacks Project, Tag 039C at the identity.** A finitely presented `𝒪_X`-module with nonzero
stalk at `x` which is flat over `S` at `x` and whose restriction to the fibre of `f` through `x`
has flat stalk there is a flat `𝒪_{X,x}`-module. -/
theorem flat_stalk_of_isFlatOverAt_of_flat_fiber_stalk {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFinitePresentation f] (F : X.Modules) [F.IsFinitePresentation] (x : X)
    (hx : ∃ a : TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) F.val.presheaf x, a ≠ 0)
    (hflat : AlgebraicGeometry.IsFlatOverAt (Scheme.Hom.toLRSHom f).toShHom F x)
    (hfiber :
      letI := Stacks.Flatness.stalkModule
        ((Scheme.Modules.pullback (f.fiberι (f x))).obj F) (f.asFiber x)
      Module.Flat (ToType ((f.fiber (f x)).presheaf.stalk (f.asFiber x)))
        (ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
          ((Scheme.Modules.pullback (f.fiberι (f x))).obj F).val.presheaf (f.asFiber x)))) :
    letI := Stacks.Flatness.stalkModule F x
    Module.Flat (ToType (X.presheaf.stalk x))
      (ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) F.val.presheaf x)) := by
  have hinc : Stacks.Flatness.fiberHom (𝟙 X) f (f x) ≫ f.fiberι (f x) =
      (𝟙 X ≫ f).fiberι (f x) := by
    rw [show Stacks.Flatness.fiberHom (𝟙 X) f (f x) ≫ f.fiberι (f x) =
        (𝟙 X ≫ f).fiberι (f x) ≫ 𝟙 X from Limits.pullback.lift_fst .., Category.comp_id]
  have hiso : IsIso (Stacks.Flatness.fiberHom (𝟙 X) f (f x)) := isIso_fiberHom_id f (f x)
  have hflatHom : Flat (Stacks.Flatness.fiberHom (𝟙 X) f (f x)) := by
    have : IsOpenImmersion (Stacks.Flatness.fiberHom (𝟙 X) f (f x)) := inferInstance
    infer_instance
  have hpoint : (Stacks.Flatness.fiberHom (𝟙 X) f (f x)) ((𝟙 X ≫ f).asFiber x) =
      f.asFiber x := by
    apply (f.fiberι (f x)).isEmbedding.injective
    have h1 : (f.fiberι (f x)) ((Stacks.Flatness.fiberHom (𝟙 X) f (f x))
          ((𝟙 X ≫ f).asFiber x)) =
        (Stacks.Flatness.fiberHom (𝟙 X) f (f x) ≫ f.fiberι (f x)) ((𝟙 X ≫ f).asFiber x) := rfl
    rw [h1, hinc, Scheme.Hom.fiberι_asFiber f x]
    exact Scheme.Hom.fiberι_asFiber (𝟙 X ≫ f) x
  have hbase : Stacks.Flatness.IsFlatOverBaseAndFiberAt (𝟙 X) f F x := by
    refine ⟨?_, ?_⟩
    · show AlgebraicGeometry.IsFlatOverAt (Scheme.Hom.toLRSHom (𝟙 X ≫ f)).toShHom F x
      rw [Category.id_comp]
      exact hflat
    · change AlgebraicGeometry.IsFlatOverAt
        (Scheme.Hom.toLRSHom (Stacks.Flatness.fiberHom (𝟙 X) f (f x))).toShHom
        ((modulePullback (Scheme.Hom.toLRSHom ((𝟙 X ≫ f).fiberι (f x))).toShHom).obj F)
        ((𝟙 X ≫ f).asFiber x)
      have hmodIso : (Scheme.Modules.pullback (Stacks.Flatness.fiberHom (𝟙 X) f (f x))).obj
            ((Scheme.Modules.pullback (f.fiberι (f x))).obj F) ≅
          (Scheme.Modules.pullback ((𝟙 X ≫ f).fiberι (f x))).obj F :=
        ((Scheme.Modules.pullbackComp (Stacks.Flatness.fiberHom (𝟙 X) f (f x))
          (f.fiberι (f x))).app F) ≪≫ ((Scheme.Modules.pullbackCongr hinc).app F)
      have key := AlgebraicGeometry.isFlatOverAt_iff_modulePullback_isFlatOverAt
        (Stacks.Flatness.fiberHom (𝟙 X) f (f x)) (𝟙 (f.fiber (f x)))
        ((Scheme.Modules.pullback (f.fiberι (f x))).obj F) ((𝟙 X ≫ f).asFiber x)
        ((Flat.iff_flat_stalkMap (Stacks.Flatness.fiberHom (𝟙 X) f (f x))).mp hflatHom
          ((𝟙 X ≫ f).asFiber x))
      have hL : AlgebraicGeometry.IsFlatOverAt
          (Scheme.Hom.toLRSHom (𝟙 (f.fiber (f x)))).toShHom
          ((Scheme.Modules.pullback (f.fiberι (f x))).obj F)
          ((Stacks.Flatness.fiberHom (𝟙 X) f (f x)).base ((𝟙 X ≫ f).asFiber x)) := by
        rw [hpoint]
        exact (AlgebraicGeometry.isFlatOverAt_id_iff
          ((Scheme.Modules.pullback (f.fiberι (f x))).obj F) (f.asFiber x)).mpr hfiber
      have hR := key.mp hL
      rw [Category.comp_id] at hR
      exact (AlgebraicGeometry.isFlatOverAt_iff_of_moduleIso _ hmodIso
        ((𝟙 X ≫ f).asFiber x)).mp hR
  have hfpRS : _root_.SheafOfModules.IsFinitePresentation
      (R := structureSheafRing X.toRingedSpace) F := ‹F.IsFinitePresentation›
  have hmid := (Stacks.Flatness.isFlatOverBaseAndFiberAt_iff (𝟙 X) f F x hx).mp hbase
  refine (AlgebraicGeometry.isFlatOverAt_id_iff F x).mp ?_
  have hid : AlgebraicGeometry.IsFlatOverAt (Scheme.Hom.toLRSHom (𝟙 X)).toShHom F x := hmid.2
  exact hid

/-- **Stacks Project, Tag 080Q.** Let `f : X ⟶ S` be a morphism of finite presentation and let
`F` be a finitely presented `𝒪_X`-module. If `F` is flat over `S` at `x` and the stalk at `x` of
the restriction of `F` to the fibre of `f` through `x` is a flat module over the local ring of
that fibre, then `F` is free of finite rank on an open neighbourhood of `x`. -/
@[stacks 080Q]
theorem exists_iso_free_over_of_flat_over_at_of_flat_fiber_stalk {X S : Scheme.{u}} (f : X ⟶ S)
    (hf : AlgebraicGeometry.FinitePresentation f) (F : X.Modules) [F.IsFinitePresentation]
    (x : X)
    (hflat : AlgebraicGeometry.IsFlatOverAt (Scheme.Hom.toLRSHom f).toShHom F x)
    (hfiber :
      letI := Stacks.Flatness.stalkModule
        ((Scheme.Modules.pullback (f.fiberι (f x))).obj F) (f.asFiber x)
      Module.Flat (ToType ((f.fiber (f x)).presheaf.stalk (f.asFiber x)))
        (ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
          ((Scheme.Modules.pullback (f.fiberι (f x))).obj F).val.presheaf (f.asFiber x)))) :
    ∃ U : X.Opens, x ∈ U ∧ ∃ n : ℕ,
      Nonempty (F.over U ≅ SheafOfModules.free (ULift.{u} (Fin n))) := by
  classical
  have hfp : _root_.SheafOfModules.IsFinitePresentation.{u, u, u} F := ‹_›
  have : LocallyOfFinitePresentation f := hf.locallyOfFinitePresentation
  let : Module (ToType (X.presheaf.stalk x))
      (ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) F.val.presheaf x)) :=
    Stacks.Flatness.stalkModule F x
  have : _root_.SheafOfModules.IsFiniteType.{u, u, u} F :=
    _root_.SheafOfModules.instIsFiniteTypeOfIsFinitePresentation F
  have hfin : Module.Finite (ToType (X.presheaf.stalk x))
      (ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) F.val.presheaf x)) :=
    _root_.SheafOfModules.finite_stalk X.sheaf F x
  have : IsLocalRing (ToType (X.presheaf.stalk x)) := X.isLocalRing x
  have hfree : Module.Free (ToType (X.presheaf.stalk x))
      (ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) F.val.presheaf x)) := by
    by_cases hzero : Subsingleton
        (ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) F.val.presheaf x))
    · have := hzero
      exact Module.Free.of_subsingleton _ _
    · have hx : ∃ a : TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) F.val.presheaf x,
          a ≠ 0 := by
        by_contra hn
        push Not at hn
        exact hzero ⟨fun a b => by rw [hn a, hn b]⟩
      have : Module.Flat (ToType (X.presheaf.stalk x))
          (ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) F.val.presheaf x)) :=
        flat_stalk_of_isFlatOverAt_of_flat_fiber_stalk f F x hx hflat hfiber
      exact Module.free_of_flat_of_isLocalRing
  obtain ⟨n, hn⟩ :=
    AlgebraicGeometry.SheafOfModules.nonempty_stalk_linearEquiv_finsupp F x hfree hfin
  obtain ⟨U, hxU, hiso⟩ :=
    Stacks.SheafOfModules.exists_iso_free_over_of_stalk_iso_free F hfp x n hn
  exact ⟨U, hxU, n, hiso⟩

end AlgebraicGeometry.Scheme.Modules

end
