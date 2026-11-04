module

public import Mathlib.CategoryTheory.ObjectProperty.Small
public import Mathlib.CategoryTheory.Skeletal
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.Algebraic.QuasiCoherentFiniteType
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.FiniteTypeStack
public import StacksFrontier.CategoryTheory.Sites.Descent.IsStack
public import StacksFrontier.CategoryTheory.Sites.Descent.IsStack.FiberIso

/-!
# The small stack of finitely generated quasi-coherent modules

Stacks 04U4 makes the projection `p_fg` from the finite-type quasi-coherent modules to the big
fppf site over `S` a stack, but a fibre of that projection has a proper class of objects: the
modules on a fixed scheme form a type one universe up. This file cuts the category down to a
subcategory `QCoh_fg,small` that keeps exactly one object per isomorphism class in each fibre,
and proves of **that construction** the two clauses of Stacks 04U6 — the inclusion is fully
faithful and essentially surjective, and the restricted projection is again a stack — together
with the smallness that is the point of the cut.

The construction is explicit, not chosen out of an existence statement: the retained objects are
the images under `CategoryTheory.fromSkeleton` of the skeleton of a fibre, i.e. the canonical
representatives of the isomorphism classes of the fibres. This is the Lean form of the source's
`Ob(S) ∩ V_α` of Stacks 03ZZ, with Mathlib's choice of a representative per isomorphism class in
place of the least level of the von Neumann hierarchy that meets every class.

## Main definitions

* `CategoryTheory.Functor.FiberSkeletal`: the objects of the source of a functor that are the
  canonical representative of an isomorphism class of a fibre.
* `Stacks.QCoh.FiniteTypeSmall` and `Stacks.QCoh.finiteTypeSmallProjection`:
  `QCoh_fg,small` and `p_fg,small`.

## Main results

* `CategoryTheory.Functor.isoOverId_fiberSkeletal`: every object is isomorphic, in its own
  fibre, to a retained one — the one statement from which essential surjectivity and both
  conditions of Stacks 04TU follow.
* `CategoryTheory.Functor.small_fiber_fiberSkeletal`: the retained objects over a fixed base
  object form a set as soon as the isomorphism classes of that fibre do.
* `Stacks.QCoh.small_skeleton_fiber_finiteTypeProjection`: the fibres of `p_fg` have only
  set-many isomorphism classes, which is Stacks 04U5 transported to a fibre.
* `Stacks.QCoh.fullyFaithful_ι_finiteTypeSmall`,
  `Stacks.QCoh.essSurj_ι_finiteTypeSmall` and
  `Stacks.QCoh.small_fiber_finiteTypeSmallProjection`: **Stacks 04U6**, together with
  `Stacks.QCoh.isStack_finiteTypeSmallProjection_unconditional` (in
  `StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.FiniteTypeSmallStackUnconditional`).
* `Stacks.QCoh.isStack_finiteTypeSmallProjection`: the stack clause granted Stacks 03YM, a
  hypothesis that is not needed, kept for its callers.
* `Stacks.QCoh.exists_finiteTypeSmall`: the bundled existential restating the source, a
  corollary of the explicit construction.

## Implementation notes

Smallness is stated fibrewise, as `Small.{u}` of each fibre of the restricted projection, and
this is forced rather than chosen. In the source `Ob(QCoh_fg,small)` is a set because `Ob(C)` is
one; here the base is `AlgebraicGeometry.BigFppfOver`, whose objects are a `Type (u + 1)` and are
only essentially `u`-small (`AlgebraicGeometry.Stack.essentiallySmall_bigFppfOver`), a scheme
having `u`-many relabellings of its carrier. Essential surjectivity together with condition (1)
of the stack clause produces a retained object over *every* base object, so `Small.{u}` of the
whole retained subcategory would entail `Small.{u}` of `BigFppfOver` and is unavailable, while
`Small.{u + 1}` is vacuous. The fibrewise bound is the cut itself: the ambient fibre over `T` is
a `Type (u + 1)`-sized collection of modules on `T`, and `Small.{u}` of the retained fibre says
that one representative per isomorphism class was kept there, which is what Stacks 04U5 makes
possible. `CategoryTheory.Functor.IsStack.exists_small_fullSubcategory` states the same shape for
an abstract stack, existentially and under the stronger hypothesis that the whole source be
essentially small; the construction here needs only the fibrewise hypothesis, which is condition
(4) of Stacks 03ZZ on the nose.

`Stacks.QCoh.isStack_finiteTypeSmallProjection` and `Stacks.QCoh.exists_finiteTypeSmall` take
Stacks 03YM, that the projection from *all* quasi-coherent modules is a stack, as an argument,
and go through `Stacks.QCoh.isStack_finiteTypeProjection`. That statement is
`Stacks.QCoh.projection_isStack`, proved in a module this file does not import; downstream, the
stack clause of Stacks 04U6 is `Stacks.QCoh.isStack_finiteTypeSmallProjection_unconditional`,
with nothing assumed.

Conditions (1) and (3) of Stacks 04TU need no separate verification: both ask that an object be
isomorphic over an identity to one of the subcategory, and
`CategoryTheory.Functor.isoOverId_fiberSkeletal` says that of every object of the ambient
category, so `CategoryTheory.Functor.IsStack.fullSubcategory` applies at once.

## References

* [Stacks Project, Tag 04U6](https://stacks.math.columbia.edu/tag/04U6)
* [Stacks Project, Tag 03ZZ](https://stacks.math.columbia.edu/tag/03ZZ)
* [Stacks Project, Tag 04TU](https://stacks.math.columbia.edu/tag/04TU)
* [Stacks Project, Tag 04U4](https://stacks.math.columbia.edu/tag/04U4)
* [Stacks Project, Tag 04U5](https://stacks.math.columbia.edu/tag/04U5)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

namespace CategoryTheory

universe w v₁ v₂ u₁ u₂

namespace Functor

variable {𝒮 : Type u₁} [Category.{v₁} 𝒮] {𝒳 : Type u₂} [Category.{v₂} 𝒳]

/-- The canonical representative of the isomorphism class `Q` of the fibre of `p` over `T`, read
as an object of the source of `p`. -/
noncomputable abbrev fiberSkeletonRepr (p : 𝒳 ⥤ 𝒮) (T : 𝒮) (Q : Skeleton (p.Fiber T)) : 𝒳 :=
  ((fromSkeleton (p.Fiber T)).obj Q).1

/-- **The skeletal subcategory of a functor.** An object of `𝒳` is retained exactly when it is
the canonical representative, supplied by `CategoryTheory.fromSkeleton`, of an isomorphism class
of some fibre of `p`. Since a fibre of `p` over `T` has only objects `x` with `p.obj x = T`, the
base object `T` in the definition is forced to be `p.obj x`.

This is the explicit subcategory of Stacks 03ZZ: one object per isomorphism class per fibre. -/
def FiberSkeletal (p : 𝒳 ⥤ 𝒮) : ObjectProperty 𝒳 :=
  fun x ↦ ∃ (T : 𝒮) (Q : Skeleton (p.Fiber T)), fiberSkeletonRepr p T Q = x

/-- A retained object lies over the base object whose fibre's isomorphism class it represents. -/
lemma obj_fiberSkeletonRepr (p : 𝒳 ⥤ 𝒮) (T : 𝒮) (Q : Skeleton (p.Fiber T)) :
    p.obj (fiberSkeletonRepr p T Q) = T :=
  ((fromSkeleton (p.Fiber T)).obj Q).2

/-- **Every object is isomorphic in its own fibre to a retained one.** The isomorphism is the one
`CategoryTheory.fromSkeletonToSkeletonIso` provides inside the fibre, so it lies over an
identity. This single statement gives essential surjectivity of the inclusion and both
conditions (1) and (3) of Stacks 04TU. -/
lemma isoOverId_fiberSkeletal (p : 𝒳 ⥤ 𝒮) (x : 𝒳) : IsoOverId p (FiberSkeletal p) x := by
  let xf : p.Fiber (p.obj x) := Fiber.mk rfl
  let e : (fromSkeleton (p.Fiber (p.obj x))).obj (toSkeleton xf) ≅ xf :=
    fromSkeletonToSkeletonIso xf
  have h1 : e.inv.1 ≫ e.hom.1 = 𝟙 x := Fiber.fiberInclusion.congr_map e.inv_hom_id
  have h2 : e.hom.1 ≫ e.inv.1 = 𝟙 (fiberSkeletonRepr p (p.obj x) (toSkeleton xf)) :=
    Fiber.fiberInclusion.congr_map e.hom_inv_id
  exact ⟨fiberSkeletonRepr p (p.obj x) (toSkeleton xf),
    ⟨p.obj x, toSkeleton xf, rfl⟩, ⟨e.inv.1, e.hom.1, h1, h2⟩, e.inv.2⟩

/-- A retained object lying over `T` *is* the canonical representative of its own isomorphism
class in the fibre over `T`: the base object recorded by its membership is `p.obj x`, hence
`T`. -/
lemma fromSkeleton_toSkeleton_of_fiberSkeletal (p : 𝒳 ⥤ 𝒮) {T : 𝒮} {x : 𝒳}
    (hx : FiberSkeletal p x) (h : p.obj x = T) :
    (fromSkeleton (p.Fiber T)).obj (toSkeleton (Fiber.mk h)) = Fiber.mk h := by
  obtain ⟨T', Q, hQ⟩ := hx
  have hT' : p.obj x = T' := by
    rw [← hQ]
    exact obj_fiberSkeletonRepr p T' Q
  have hTT : T' = T := hT'.symm.trans h
  subst hTT
  have hEq : (Fiber.mk h : p.Fiber T') = (fromSkeleton (p.Fiber T')).obj Q :=
    Fiber.fiberInclusion_obj_inj hQ.symm
  rw [hEq, toSkeleton_fromSkeleton_obj]

/-- **The retained objects over a fixed base object form a set**, as soon as the isomorphism
classes of the fibre there do: a retained object of the fibre over `T` is recovered from its own
isomorphism class by `CategoryTheory.fromSkeleton`. -/
lemma small_fiber_fiberSkeletal (p : 𝒳 ⥤ 𝒮) (T : 𝒮) [Small.{w} (Skeleton (p.Fiber T))] :
    Small.{w} ((restrict p (FiberSkeletal p)).Fiber T) := by
  have hbase (z : (restrict p (FiberSkeletal p)).Fiber T) : p.obj z.1.1 = T := z.2
  refine small_of_injective (f := fun z : (restrict p (FiberSkeletal p)).Fiber T ↦
    toSkeleton (Fiber.mk (hbase z))) ?_
  intro z z' hz
  have hz' : toSkeleton (Fiber.mk (hbase z)) = toSkeleton (Fiber.mk (hbase z')) := hz
  have h1 := fromSkeleton_toSkeleton_of_fiberSkeletal p z.1.2 (hbase z)
  have h2 := fromSkeleton_toSkeleton_of_fiberSkeletal p z'.1.2 (hbase z')
  have hval : (Fiber.mk (hbase z) : p.Fiber T) = Fiber.mk (hbase z') :=
    h1.symm.trans ((congrArg (fromSkeleton (p.Fiber T)).obj hz').trans h2)
  have hobj : z.1.1 = z'.1.1 := congrArg (fun a : p.Fiber T ↦ a.1) hval
  exact Fiber.fiberInclusion_obj_inj (ObjectProperty.FullSubcategory.ext hobj)

/-- **The inclusion of the skeletal subcategory is essentially surjective**, by
`CategoryTheory.Functor.isoOverId_fiberSkeletal`. It is fully faithful because the subcategory is
full, which is `CategoryTheory.ObjectProperty.fullyFaithfulι`. -/
lemma essSurj_ι_fiberSkeletal (p : 𝒳 ⥤ 𝒮) : (FiberSkeletal p).ι.EssSurj where
  mem_essImage x := by
    obtain ⟨y, hy, e, -⟩ := isoOverId_fiberSkeletal p x
    exact ⟨⟨y, hy⟩, ⟨e.symm⟩⟩

/-- **The skeletal subcategory of a stack is a stack.** Conditions (1) and (3) of Stacks 04TU
hold because every object of the ambient category is isomorphic over an identity to a retained
one, `CategoryTheory.Functor.isoOverId_fiberSkeletal`; condition (2) is fullness. -/
theorem IsStack.fiberSkeletal (p : 𝒳 ⥤ 𝒮) (J : GrothendieckTopology 𝒮) (hp : p.IsStack J) :
    (restrict p (FiberSkeletal p)).IsStack J := by
  refine IsStack.fullSubcategory p J hp (FiberSkeletal p) ?_ ?_
  · intro _ _ y _ _ _ _ _
    exact isoOverId_fiberSkeletal p y
  · intro _ _ _ _ _ x _
    exact isoOverId_fiberSkeletal p x.1

end Functor

end CategoryTheory

namespace Stacks.QCoh

universe u

variable (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- An isomorphism of quasi-coherent modules on the underlying scheme of `T` is an isomorphism of
the corresponding quasi-coherent pairs lying over the identity of `T`: the `f`-map description of
a hom of Stacks 04U2 turns it into an arrow with base `𝟙 T` whose pullback comparison is an
isomorphism, and Stacks 04U3 makes such an arrow strongly cartesian over an isomorphism, hence an
isomorphism. -/
private theorem exists_isoOverBase (T : AlgebraicGeometry.BigFppfOver B S hS)
    (M N : ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj T).Modules)
    (hM : M.IsQuasicoherent) (hN : N.IsQuasicoherent) (e : M ≅ N) :
    ∃ f : (⟨T, M, hM⟩ : Object B S hS) ≅ ⟨T, N, hN⟩,
      (projection (B := B) (S := S) (hS := hS)).IsHomLift (𝟙 T) f.hom := by
  classical
  let X := (AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj T
  let A : Object B S hS := ⟨T, M, hM⟩
  let C : Object B S hS := ⟨T, N, hN⟩
  have g : (Object.schemeMap (A := A) (C := C) (𝟙 T) : X ⟶ X) = 𝟙 X :=
    (AlgebraicGeometry.BigFppfOver.toScheme B S hS).map_id T
  let α : ((Scheme.Modules.pullback (Object.schemeMap (A := A) (C := C) (𝟙 T))).obj N) ≅ M :=
    (Scheme.Modules.pullbackCongr g).app N ≪≫ (Scheme.Modules.pullbackId X).app N ≪≫ e.symm
  let m : A ⟶ C := (homEquivPullbackHom A C).symm ⟨𝟙 T, α.hom⟩
  let d := Classical.choice (exists_categoryData (B := B) (S := S) (hS := hS))
  let p := projection (B := B) (S := S) (hS := hS)
  have hraw : (Equiv.cast (d.hom_type A C) m).1 = 𝟙 T := by
    simp [m, homEquivPullbackHom, Equiv.sigmaCongrRight_symm]
  have hpmap : p.map m =
      eqToHom (d.projection_obj A) ≫ (𝟙 T) ≫ eqToHom (d.projection_obj C).symm := by
    show d.projection.map m = _
    rw [d.projection_map, hraw]
  have hmIso : IsIso m := by
    have hsc := (isStronglyCartesian_iff m).2
      (show IsIso ((homEquivPullbackHom A C m).2) from by
        dsimp only [m]
        rw [Equiv.apply_symm_apply]
        infer_instance)
    have : IsIso (p.map m) := by
      change IsIso (d.projection.map m)
      rw [d.projection_map, hraw]
      infer_instance
    exact Functor.IsStronglyCartesian.isIso_of_base_isIso p (p.map m) m
  let : IsIso m := hmIso
  exact ⟨asIso m,
    IsHomLift.of_fac' p (𝟙 T) m (d.projection_obj A) (d.projection_obj C) hpmap⟩

/-- **The fibres of `p_fg` have only set-many isomorphism classes.** A fibre over `T` is the
category of finite-type quasi-coherent modules on the underlying scheme of `T`, and Stacks 04U5
provides a set of representatives of their isomorphism classes there; `exists_isoOverBase`
transports each identification into the fibre.

This is condition (4) of Stacks 03ZZ for the projection of Stacks 04U4, and it is what makes the
cut below possible. -/
theorem small_skeleton_fiber_finiteTypeProjection (T : AlgebraicGeometry.BigFppfOver B S hS) :
    Small.{u} (Skeleton ((finiteTypeProjection B S hS).Fiber T)) := by
  classical
  let X := (AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj T
  let R : ObjectProperty X.Modules := fun M ↦ M.IsFiniteType ∧ M.IsQuasicoherent
  let : ObjectProperty.EssentiallySmall.{u} R :=
    Stacks.SheafOfModules.essentiallySmall_isFiniteType_and_isQuasicoherent
      X.toLocallyRingedSpace.toRingedSpace
  obtain ⟨Q, hQ, hle, hcover⟩ := ObjectProperty.EssentiallySmall.exists_small_le R
  let : ObjectProperty.Small.{u} Q := hQ
  let p := finiteTypeProjection B S hS
  let d := Classical.choice (exists_categoryData (B := B) (S := S) (hS := hS))
  let a (i : Subtype Q) : FiniteType B S hS := ⟨⟨T, i.1, (hle i.1 i.2).2⟩, (hle i.1 i.2).1⟩
  let f (i : Subtype Q) : p.Fiber T := ⟨a i, d.projection_obj (a i).1⟩
  have hcover' (x : p.Fiber T) : ∃ i : Subtype Q, Nonempty (x ≅ f i) := by
    rcases x with ⟨⟨⟨U, M, hqc⟩, hft⟩, hx⟩
    have hUT : U = T :=
      (d.projection_obj (⟨U, M, hqc⟩ : Object B S hS)).symm.trans hx
    subst hUT
    obtain ⟨N, hN, ⟨e⟩⟩ := hcover M ⟨hft, hqc⟩
    let i : Subtype Q := ⟨N, hN⟩
    obtain ⟨e', he'⟩ := exists_isoOverBase B S hS U M N hqc (hle N hN).2 e
    let e'' : (⟨⟨U, M, hqc⟩, hft⟩ : FiniteType B S hS) ≅ a i :=
      (isFiniteType B S hS).isoMk e'
    have he'' : p.IsHomLift (𝟙 U) e''.hom := by
      have h : (projection (B := B) (S := S) (hS := hS)).IsHomLift (𝟙 U)
          ((isFiniteType B S hS).ι.map e''.hom) := he'
      exact (Functor.isHomLift_restrict_iff (projection (B := B) (S := S) (hS := hS))
        (isFiniteType B S hS) (𝟙 U) e''.hom).2 h
    exact ⟨i, ⟨Functor.Fiber.isoMk e'' he''⟩⟩
  refine small_of_surjective (f := fun i : Subtype Q ↦ toSkeleton (f i)) ?_
  intro Z
  obtain ⟨i, ⟨ee⟩⟩ := hcover' ((fromSkeleton (p.Fiber T)).obj Z)
  exact ⟨i, (congr_toSkeleton_of_iso ee).symm.trans (toSkeleton_fromSkeleton_obj Z)⟩

/-- `QCoh_fg,small`: the subcategory of the finite-type quasi-coherent modules over `S` keeping,
in each fibre of `p_fg`, the canonical representative of each isomorphism class. -/
noncomputable abbrev FiniteTypeSmall : ObjectProperty (FiniteType B S hS) :=
  Functor.FiberSkeletal (finiteTypeProjection B S hS)

/-- `p_fg,small`: the restriction of the projection of Stacks 04U4 to `QCoh_fg,small`. The base
site is unchanged. -/
noncomputable abbrev finiteTypeSmallProjection :
    (FiniteTypeSmall B S hS).FullSubcategory ⥤ AlgebraicGeometry.BigFppfOver B S hS :=
  Functor.restrict (finiteTypeProjection B S hS) (FiniteTypeSmall B S hS)

/-- **Stacks 04U6, smallness.** `QCoh_fg,small` is small: its objects over each object of the
base site form a set. The ambient fibre is not set-sized, so this is the content of the cut; see
the implementation notes for why the bound is fibrewise. -/
@[stacks 04U6 "the selected subcategory is small: its objects over each object of the big fppf \
site over S form a set"]
theorem small_fiber_finiteTypeSmallProjection (T : AlgebraicGeometry.BigFppfOver B S hS) :
    Small.{u} ((finiteTypeSmallProjection B S hS).Fiber T) :=
  have := small_skeleton_fiber_finiteTypeProjection B S hS T
  Functor.small_fiber_fiberSkeletal (finiteTypeProjection B S hS) T

/-- **Stacks 04U6 (1), first half.** The inclusion `QCoh_fg,small → QCoh_fg` is fully faithful,
the subcategory being full. -/
@[stacks 04U6 "clause (1), first half: the inclusion functor is fully faithful"]
noncomputable def fullyFaithful_ι_finiteTypeSmall :
    (FiniteTypeSmall B S hS).ι.FullyFaithful :=
  ObjectProperty.fullyFaithfulι _

/-- **Stacks 04U6 (1), second half.** The inclusion `QCoh_fg,small → QCoh_fg` is essentially
surjective: a canonical representative of its own isomorphism class was kept in every fibre. -/
@[stacks 04U6 "clause (1), second half: the inclusion functor is essentially surjective"]
theorem essSurj_ι_finiteTypeSmall : (FiniteTypeSmall B S hS).ι.EssSurj :=
  Functor.essSurj_ι_fiberSkeletal (finiteTypeProjection B S hS)

/-- `p_fg,small` turns `QCoh_fg,small` into a stack over the big fppf site of `S`, granted
Stacks 03YM as `hp`. The hypothesis is not needed: it is `Stacks.QCoh.projection_isStack`, and
Stacks 04U6 (2) without it is `Stacks.QCoh.isStack_finiteTypeSmallProjection_unconditional`;
this form is kept for its callers. -/
theorem isStack_finiteTypeSmallProjection
    (hp : Functor.IsStack (projection (B := B) (S := S) (hS := hS))
      (AlgebraicGeometry.BigFppfOver.topology B S hS)) :
    Functor.IsStack (finiteTypeSmallProjection B S hS)
      (AlgebraicGeometry.BigFppfOver.topology B S hS) :=
  Functor.IsStack.fiberSkeletal (finiteTypeProjection B S hS) _
    (isStack_finiteTypeProjection B S hS hp)

/-- **Stacks 04U6**, as the source words it: there *exists* a subcategory of `QCoh_fg` which is
small, whose inclusion is fully faithful and essentially surjective, and whose projection makes
it a stack over the big fppf site of `S`. A corollary of the explicit `FiniteTypeSmall`, which is
the object the source's proof constructs. -/
theorem exists_finiteTypeSmall
    (hp : Functor.IsStack (projection (B := B) (S := S) (hS := hS))
      (AlgebraicGeometry.BigFppfOver.topology B S hS)) :
    ∃ P : ObjectProperty (FiniteType B S hS),
      (∀ T : AlgebraicGeometry.BigFppfOver B S hS,
          Small.{u} ((Functor.restrict (finiteTypeProjection B S hS) P).Fiber T)) ∧
        P.ι.EssSurj ∧
        Functor.IsStack (Functor.restrict (finiteTypeProjection B S hS) P)
          (AlgebraicGeometry.BigFppfOver.topology B S hS) :=
  ⟨FiniteTypeSmall B S hS, small_fiber_finiteTypeSmallProjection B S hS,
    essSurj_ι_finiteTypeSmall B S hS, isStack_finiteTypeSmallProjection B S hS hp⟩

end Stacks.QCoh

end
