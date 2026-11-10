module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InvertibleEquivalence
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackMonoidalSheaf
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SliceRestrictionMonoidal

/-!
# The pullback of sheaves of modules along a continuous functor of sites is additive and monoidal

`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackMonoidal`,
`...PullbackMonoidalSheaf` and `...PullbackGradedAlgebra` prove that the pullback of sheaves of
modules along a morphism of **ringed spaces** is an additive strong monoidal functor. This file
proves the same statements for `CategoryTheory.SheafOfModules.pullback` along a **continuous
functor of sites**, which is the generality the functoriality of sheaves of graded and
differential graded algebras needs.

Nothing here is a new argument: the ringed-space proofs factor through machinery which is already
site-level — `PresheafOfModules.pullbackOplaxMonoidal`, `Stacks.PullbackColimit`'s concrete model
of the presheaf pullback, `Stacks.PullbackTensor.pullbackTensorIso` (the comparison of Tag 01CD
for a functor of sites), `Stacks.SheafOfModules.monoidalCategory` (Tag 01CA on a site), and
Mathlib's `SheafOfModules.sheafificationCompPullback`. What was stated only for spaces is the
*gluing*: the identification of the oplax tensorator with that comparison, and the localization
transport that turns it into a monoidal structure on sheaves. Both are redone here with the
ringed space replaced by a site.

## Main results

* `Stacks.PullbackMonoidalSite.pullback_additive`: `f^*` is additive, as a left adjoint between
  preadditive categories with binary biproducts. This holds in full generality — no smallness,
  flatness or finality hypothesis.
* `Stacks.PullbackMonoidalSite.pullbackTensorIso_hom_pullbackAdjUnit_tmul` and
  `delta_eq_pullbackTensorIso`: **the oplax tensorator of the presheaf-level pullback is the
  canonical comparison of Tag 01CD**, read on the pullback-unit image of a pure tensor.
* `Stacks.PullbackMonoidalSite.presheafPullbackMonoidal`: the presheaf-level pullback is strong
  monoidal. Its unit is invertible by `PresheafOfModules.isIso_eta` (whence `[F.Final]`) and its
  tensorator by the previous item (whence `[RepresentablyFlat F]`, which is what makes the index
  category of the colimit filtered).
* `Stacks.PullbackMonoidalSite.pullbackMonoidal`: **the pullback of sheaves of modules along a
  continuous functor of sites is strong monoidal** for `Stacks.SheafOfModules.monoidalCategory`,
  the localization of the objectwise tensor product along sheafification.
* `Stacks.PullbackMonoidalSite.pullbackStrictMonoidal` and `pullbackMonoidalStrict`: the same for
  `Stacks.SheafOfModules.Strict.monoidalCategory`, whose tensor product is the tensor product
  sheaf of Tag 01CA on the nose. This is the structure `Stacks.TensorSheafWorld.monoidalCategory`
  carries, so it is the one the graded-algebra files consume.

## Implementation notes

**Hypotheses.** The monoidal statements are for `C` and `D` small in one universe `u`, with the
sheaves of rings and the module sections at a free universe `w` subject to `[UnivLE.{u, w}]`,
and assume `[RepresentablyFlat F]` and `[F.Final]`. The smallness and `UnivLE` come from
`Stacks.PullbackTensor.pullbackTensorIso`, which is stated for `[SmallCategory C]`
`[SmallCategory D]` and needs the index category of the colimit computing the pullback to be
`u`-small; representable flatness is what makes that tensor product commute with the colimit,
and finality is what makes the oplax unit invertible. `Stacks.PullbackColimit` records why the
two sites must share a universe and why the rings and the modules must share one. For
`F = Stacks.RingedSpace.opensMap f` all of this holds at `w := u`, so the ringed-space instances
are the special case. The additivity statement is in the general variable block and shares none
of this.

`isRightAdjoint_presheafPushforward` is `Stacks.PullbackColimit.isRightAdjoint_pushforward`
rather than Mathlib's `PresheafOfModules.instIsRightAdjointPushforward`: the latter exists only
for module sections in the sites' own universe.

**Two spellings of the monoidal structure.** `pullbackStrict` is the pullback read as a composite
`𝟭 ⋙ f^* ⋙ 𝟭` through the type synonym carrying the localized structure, exactly as
`Stacks.PullbackGradedAlgebra.pullbackStrictMonoidal` does for a ringed space. Ascribing the
composite's monoidality directly to `SheafOfModules.pullback` is rejected by the kernel here —
the auxiliary proof terms are generalized over the section variables at the composite's type and
then checked at the ascribed one — so the composite is named (`pullbackStrict`, an `abbrev`,
hence reducible), its monoidality proved there, and `pullbackMonoidalStrict` transports along the
*equation* `pullbackStrict_eq`, which is `rfl`.

**`PresheafOfModules.tensorObj` is written out** in
`pullbackTensorIso_hom_pullbackAdjUnit_tmul`: with `SliceRestrictionMonoidal` imported, the bare
name elaborates to a form that the rewrite pattern no longer matches.

## References

* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
-/

@[expose] public section

universe v v₁ v₂ u₁ u₂ w u

open CategoryTheory Limits Functor

namespace Stacks.PullbackMonoidalSite

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D} {F : C ⥤ D}
  {S : Sheaf J RingCat.{u}} {R : Sheaf K RingCat.{u}}
  [Functor.IsContinuous F J K]
  (φ : S ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj R)
  [(SheafOfModules.pushforward.{v} φ).IsRightAdjoint]
  [HasSheafify J AddCommGrpCat.{v}] [J.WEqualsLocallyBijective AddCommGrpCat.{v}]
  [HasSheafify K AddCommGrpCat.{v}] [K.WEqualsLocallyBijective AddCommGrpCat.{v}]

/-- **The pullback of sheaves of modules along a continuous functor of sites is additive.** -/
instance pullback_additive : (SheafOfModules.pullback.{v} φ).Additive :=
  letI : PreservesBinaryBiproducts (SheafOfModules.pullback.{v} φ) :=
    preservesBinaryBiproducts_of_preservesBinaryCoproducts _
  Functor.additive_of_preservesBinaryBiproducts _

/-! ### The presheaf-level pullback along a functor of sites is monoidal -/

section Presheaf

-- The `_root_` prefix is load-bearing. This file is inside `namespace Stacks`, the import closure
-- also contains a namespace `Stacks.PresheafOfModules`, and `open` prefers the enclosing
-- namespace: a bare `open PresheafOfModules` silently opens that one instead, after which the
-- root-namespace names used below (`Hom.app`, `pullbackAdjUnit`) are unknown identifiers.
open _root_.PresheafOfModules Stacks.PullbackModel Stacks.PullbackColimit Stacks.PullbackTensor
open scoped TensorProduct MonoidalCategory ChangeOfRings

variable {C : Type u} [SmallCategory C] {D : Type u} [SmallCategory D] {F : C ⥤ D}
  {S : Cᵒᵖ ⥤ CommRingCat.{w}} {R : Dᵒᵖ ⥤ CommRingCat.{w}} (α : S ⟶ F.op ⋙ R)
  [hUL : UnivLE.{u, w}]

include hUL

/-- The index object of the filtered colimit computing the pullback at which the unit of the
adjunction lives: the identity arrow on `F.op.obj U`. -/
noncomputable abbrev unitArrow (U : Cᵒᵖ) : CostructuredArrow F.op (F.op.obj U) :=
  CostructuredArrow.mk (𝟙 (F.op.obj U))

/-- The germ description of `PresheafOfModules.pullbackAdjUnit` through the concrete model of
the pullback. -/
lemma pullbackIso_hom_pullbackAdjUnit
    (M : PresheafOfModules.{w} (S ⋙ forget₂ CommRingCat RingCat)) (U : Cᵒᵖ) (m : M.obj U) :
    Hom.app ((Stacks.PullbackColimit.pullbackIso α).hom.app M) (F.op.obj U)
        (pullbackAdjUnit (toRingCatPullback α) M U m) =
      germ F R ((extendScalars α).obj M) (unitArrow U) 1 (tmul (α.app U).hom 1 m) := by
  have h := Adjunction.unit_leftAdjointUniq_hom_app
    (PresheafOfModules.pullbackPushforwardAdjunction.{w} (toRingCatPullback α))
    (Stacks.PullbackColimit.modelAdjunction α) M
  exact PresheafOfModules.hom_congr_apply' h U m

/-- The inverse of the model comparison carries the model unit germ back to
`PresheafOfModules.pullbackAdjUnit`. -/
lemma pullbackIso_inv_germ
    (M : PresheafOfModules.{w} (S ⋙ forget₂ CommRingCat RingCat)) (U : Cᵒᵖ) (m : M.obj U) :
    Hom.app ((Stacks.PullbackColimit.pullbackIso α).inv.app M) (F.op.obj U)
        (germ F R ((extendScalars α).obj M) (unitArrow U) 1 (tmul (α.app U).hom 1 m)) =
      pullbackAdjUnit (toRingCatPullback α) M U m := by
  rw [← pullbackIso_hom_pullbackAdjUnit α M U m]
  exact PresheafOfModules.hom_congr_apply'
    ((Stacks.PullbackColimit.pullbackIso α).hom_inv_id_app M) (F.op.obj U) _

variable [RepresentablyFlat F]

/-- **The presheaf-level pullback comparison of Tag 01CD along a functor of sites is
canonical**: it carries the unit image of a pure tensor to the pure tensor of the unit
images. -/
lemma pullbackTensorIso_hom_pullbackAdjUnit_tmul
    (M N : PresheafOfModules.{w} (S ⋙ forget₂ CommRingCat RingCat)) (U : Cᵒᵖ)
    (x : M.obj U) (y : N.obj U) :
    Hom.app ((Stacks.PullbackTensor.pullbackTensorIso α).hom.app (M, N)) (F.op.obj U)
        (pullbackAdjUnit (toRingCatPullback α) (PresheafOfModules.tensorObj M N) U (x ⊗ₜ y)) =
      (pullbackAdjUnit (toRingCatPullback α) M U x ⊗ₜ
          pullbackAdjUnit (toRingCatPullback α) N U y :
        (tensorObj ((PresheafOfModules.pullback.{w} (toRingCatPullback α)).obj M)
          ((PresheafOfModules.pullback.{w} (toRingCatPullback α)).obj N)).obj (F.op.obj U)) := by
  change Hom.app
    ((Functor.uncurry.obj (_root_.PresheafOfModules.tensorBifunctor.{u, u, w, w, w} R)).map
      (X := ((colimitPullback F R).obj ((extendScalars α).obj M),
        (colimitPullback F R).obj ((extendScalars α).obj N)))
      (Y := ((PresheafOfModules.pullback.{w} (toRingCatPullback α)).obj M,
        (PresheafOfModules.pullback.{w} (toRingCatPullback α)).obj N))
      (((Stacks.PullbackColimit.pullbackIso α).inv.app M),
        ((Stacks.PullbackColimit.pullbackIso α).inv.app N))) (F.op.obj U)
      (Hom.app (objTensorIso F R ((extendScalars α).obj M)
          ((extendScalars α).obj N)).hom (F.op.obj U)
        (Hom.app ((colimitPullback F R).map
            (extendScalarsTensorObjIso α M N).hom) (F.op.obj U)
          (Hom.app ((Stacks.PullbackColimit.pullbackIso α).hom.app
              (PresheafOfModules.tensorObj M N)) (F.op.obj U)
            (pullbackAdjUnit (toRingCatPullback α)
              (PresheafOfModules.tensorObj M N) U (x ⊗ₜ y))))) = _
  refine (_root_.PresheafOfModules.hom_congr_apply'
    (_root_.PresheafOfModules.tensorBifunctor_uncurry_map (O := R)
      ((Stacks.PullbackColimit.pullbackIso α).inv.app M)
      ((Stacks.PullbackColimit.pullbackIso α).inv.app N)) (F.op.obj U) _).trans ?_
  rw [pullbackIso_hom_pullbackAdjUnit α (PresheafOfModules.tensorObj M N) U (x ⊗ₜ y)]
  rw [colimitPullback_map_germ_one F R (extendScalarsTensorObjIso α M N).hom (unitArrow U)
      (tmul (α.app U).hom 1 (x ⊗ₜ y) :
        ((extendScalars α).obj (PresheafOfModules.tensorObj M N)).obj U)]
  change Hom.app (tensorHom ((Stacks.PullbackColimit.pullbackIso α).inv.app M)
        ((Stacks.PullbackColimit.pullbackIso α).inv.app N)) (F.op.obj U)
      (Hom.app (objTensorIso F R ((extendScalars α).obj M)
          ((extendScalars α).obj N)).hom (F.op.obj U)
        (germTmul F R ((extendScalars α).obj M) ((extendScalars α).obj N) (F.op.obj U)
          (unitArrow U) 1 (tmul (α.app U).hom 1 x) (tmul (α.app U).hom 1 y))) = _
  rw [objTensorIso_hom_germTmul F R ((extendScalars α).obj M) ((extendScalars α).obj N)
      (F.op.obj U) (unitArrow U) 1 (tmul (α.app U).hom 1 x) (tmul (α.app U).hom 1 y)]
  change Hom.app (tensorHom ((Stacks.PullbackColimit.pullbackIso α).inv.app M)
        ((Stacks.PullbackColimit.pullbackIso α).inv.app N)) (F.op.obj U)
      (germ F R ((extendScalars α).obj M) (unitArrow U) 1 (tmul (α.app U).hom 1 x) ⊗ₜ
        germ F R ((extendScalars α).obj N) (unitArrow U) 1 (tmul (α.app U).hom 1 y)) = _
  erw [tensorHom_tmul ((Stacks.PullbackColimit.pullbackIso α).inv.app M)
      ((Stacks.PullbackColimit.pullbackIso α).inv.app N) (F.op.obj U) _ _,
    pullbackIso_inv_germ, pullbackIso_inv_germ]

/-- **The oplax tensorator of the presheaf-level pullback along a functor of sites is the
canonical comparison of Tag 01CD.** -/
theorem delta_eq_pullbackTensorIso
    (M N : PresheafOfModules.{w} (S ⋙ forget₂ CommRingCat RingCat)) :
    Functor.OplaxMonoidal.δ
        (self := PresheafOfModules.pullbackOplaxMonoidal (toRingCatPullback α))
        (PresheafOfModules.pullback.{w} (toRingCatPullback α)) M N =
      (Stacks.PullbackTensor.pullbackTensorIso α).hom.app (M, N) := by
  refine PresheafOfModules.pullback_tensor_hom_ext _ fun U x y ↦ ?_
  refine Eq.trans (PresheafOfModules.delta_pullbackAdjUnit_tmul _ M N U x y) ?_
  exact (pullbackTensorIso_hom_pullbackAdjUnit_tmul α M N U x y).symm

/-- The oplax tensorator of the presheaf-level pullback along a functor of sites is an
isomorphism. -/
instance isIso_delta (M N : PresheafOfModules.{w} (S ⋙ forget₂ CommRingCat RingCat)) :
    IsIso (Functor.OplaxMonoidal.δ
      (self := PresheafOfModules.pullbackOplaxMonoidal (toRingCatPullback α))
      (PresheafOfModules.pullback.{w} (toRingCatPullback α)) M N) := by
  rw [delta_eq_pullbackTensorIso]
  exact inferInstanceAs (IsIso ((Stacks.PullbackTensor.pullbackTensorIso α).app (M, N)).hom)

/-- **The pullback of presheaves of modules along a functor of sites is a monoidal functor**,
with tensorator the canonical comparison of Tag 01CD. -/
@[instance_reducible]
noncomputable def presheafPullbackMonoidal [F.Final] :
    (PresheafOfModules.pullback.{w} (toRingCatPullback α)).Monoidal :=
  letI := PresheafOfModules.pullbackOplaxMonoidal (toRingCatPullback α)
  Functor.Monoidal.ofOplaxMonoidal _

/-- The tensorator of `presheafPullbackMonoidal` is the oplax one, hence by
`delta_eq_pullbackTensorIso` the canonical comparison of Tag 01CD. -/
theorem presheafPullbackMonoidal_delta [F.Final]
    (M N : PresheafOfModules.{w} (S ⋙ forget₂ CommRingCat RingCat)) :
    Functor.OplaxMonoidal.δ (self := (presheafPullbackMonoidal α).toOplaxMonoidal)
        (PresheafOfModules.pullback.{w} (toRingCatPullback α)) M N =
      (Stacks.PullbackTensor.pullbackTensorIso α).hom.app (M, N) :=
  delta_eq_pullbackTensorIso α M N

end Presheaf

/-! ### The sheaf-level pullback along a continuous functor of sites is monoidal -/

section Sheaf

open _root_.PresheafOfModules Stacks.PullbackModel Stacks.PullbackColimit Stacks.PullbackTensor
open MonoidalCategory Localization
open Stacks.SheafOfModules.TensorSheafification

variable {C : Type u} [SmallCategory C] {D : Type u} [SmallCategory D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  {F : C ⥤ D} [Functor.IsContinuous F J K] [RepresentablyFlat F] [F.Final]
  {O : Cᵒᵖ ⥤ CommRingCat.{w}} {P : Dᵒᵖ ⥤ CommRingCat.{w}} (α : O ⟶ F.op ⋙ P)
  (hO : Presheaf.IsSheaf J (structureRingPresheaf O))
  (hP : Presheaf.IsSheaf K (structureRingPresheaf P))
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]
  [K.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify K AddCommGrpCat.{w}]
  [hUL : UnivLE.{u, w}]

include hUL

attribute [local instance] Stacks.SheafOfModules.monoidalCategory

/-- `α`, read as a morphism of sheaves of not necessarily commutative rings
`O ⟶ F_* P` on the site `(C, J)`. This is the datum `SheafOfModules.pullback` consumes. -/
noncomputable def sheafRingHom :
    structureSheaf O hO ⟶
      (F.sheafPushforwardContinuous RingCat.{w} J K).obj (structureSheaf P hP) :=
  ObjectProperty.homMk (toRingCatPullback α)

/-- The presheaf-level pullback along `α`, followed by sheafification on the target site. -/
noncomputable abbrev sheafifiedPresheafPullback :
    PresheafOfModules.{w} (structureRingPresheaf O) ⥤
      SheafOfModules.{w} (structureSheaf P hP) :=
  PresheafOfModules.pullback.{w} (toRingCatPullback α) ⋙
    Stacks.SheafOfModules.sheafifyFunctor P hP

/-- The presheaf-level pullback followed by sheafification is monoidal, as a composite of
`presheafPullbackMonoidal` with the monoidal localization functor on the target site. -/
@[instance_reducible]
noncomputable def sheafifiedPresheafPullbackMonoidal :
    (sheafifiedPresheafPullback α hP).Monoidal :=
  letI := presheafPullbackMonoidal α
  letI := Stacks.SheafOfModules.sheafifyFunctor_monoidal P hP
  inferInstance

attribute [local instance] sheafifiedPresheafPullbackMonoidal

/-- The presheaf-level pushforward along `sheafRingHom α hO hP` is a right adjoint. Instance
search does not see through `ObjectProperty.homMk`, so this one-step instantiation of Mathlib's
instance is what makes the lifting isomorphism below elaborate. -/
instance isRightAdjoint_presheafPushforward :
    (PresheafOfModules.pushforward.{w} (sheafRingHom α hO hP).hom).IsRightAdjoint :=
  Stacks.PullbackColimit.isRightAdjoint_pushforward α

variable [(SheafOfModules.pushforward.{w} (sheafRingHom α hO hP)).IsRightAdjoint]

/-- **Pullback of modules commutes with sheafification** — Mathlib's
`SheafOfModules.sheafificationCompPullback`, retyped at the spellings used here. -/
noncomputable abbrev liftingIso :
    Stacks.SheafOfModules.sheafifyFunctor O hO ⋙
        SheafOfModules.pullback.{w} (sheafRingHom α hO hP) ≅
      sheafifiedPresheafPullback α hP :=
  SheafOfModules.sheafificationCompPullback.{w} (sheafRingHom α hO hP)

/-- The sheaf-level pullback lifts the presheaf-level pullback followed by sheafification,
along sheafification on the source site. -/
noncomputable instance lifting :
    Localization.Lifting (Stacks.SheafOfModules.sheafifyFunctor O hO)
      (Stacks.SheafOfModules.localIso (J := J) O) (sheafifiedPresheafPullback α hP)
      (SheafOfModules.pullback.{w} (sheafRingHom α hO hP)) :=
  ⟨liftingIso α hO hP⟩

/-- **The pullback of sheaves of modules along a continuous functor of sites is a monoidal
functor**, for the monoidal structure `Stacks.SheafOfModules.monoidalCategory` of Tag 01CA on
each side. -/
@[instance_reducible]
noncomputable def pullbackMonoidal :
    (SheafOfModules.pullback.{w} (sheafRingHom α hO hP)).Monoidal :=
  letI := Stacks.SheafOfModules.sheafifyFunctor_monoidal O hO
  Localization.Monoidal.functorMonoidalOfComp
    (Stacks.SheafOfModules.sheafifyFunctor O hO) (Stacks.SheafOfModules.localIso (J := J) O)
    (SheafOfModules.pullback.{w} (sheafRingHom α hO hP)) (sheafifiedPresheafPullback α hP)

/-! ### The pullback is monoidal for the strict spelling of Tag 01CA -/

section Strict

open Stacks.SheafOfModules.SliceRestriction Stacks.SheafOfModules.Strict

/-- `SheafOfModules.pullback`, retyped between the two type synonyms carrying the localized
monoidal structures. -/
noncomputable abbrev pullbackLocalized :
    localizedSrc O hO ⥤ localizedSrc P hP :=
  SheafOfModules.pullback.{w} (sheafRingHom α hO hP)

/-- `pullbackMonoidal`, read at the type-synonym spelling. -/
@[instance_reducible]
noncomputable def pullbackLocalizedMonoidal : (pullbackLocalized α hO hP).Monoidal :=
  pullbackMonoidal α hO hP

attribute [local instance] Stacks.SheafOfModules.Strict.monoidalCategory

/-- The pullback of sheaves of modules, read between the two spellings carrying the *strict*
monoidal structure of Tag 01CA, as the composite of three functors each of which is monoidal:
the identity into the localized spelling, the pullback, and the identity back. It is
`SheafOfModules.pullback (sheafRingHom α hO hP)` (`pullbackStrict_eq`). -/
noncomputable abbrev pullbackStrict :
    SheafOfModules.{w} (structureSheaf O hO) ⥤ SheafOfModules.{w} (structureSheaf P hP) :=
  toLocalizedMonoidal O hO ⋙ pullbackLocalized α hO hP ⋙ fromLocalizedMonoidal P hP

omit [RepresentablyFlat F] [F.Final] hUL in
/-- `pullbackStrict` is the pullback functor itself: the two outer factors are identities. -/
theorem pullbackStrict_eq :
    pullbackStrict α hO hP = SheafOfModules.pullback.{w} (sheafRingHom α hO hP) :=
  rfl

/-- **The pullback of sheaves of modules along a continuous functor of sites is a monoidal
functor for the strict monoidal structure of Tag 01CA**, whose tensor product is the tensor
product sheaf `Stacks.SheafOfModules.Tensor.sheafTensor` on the nose. This is the
structure `Stacks.TensorSheafWorld.monoidalCategory` carries.

`pullbackMonoidal` is monoidal for the *localized* structure, whose tensor product is only
isomorphic to the tensor product sheaf. The identity functor between the two spellings is
monoidal in both directions, so this is a composite of three monoidal functors. -/
@[instance_reducible]
noncomputable def pullbackStrictMonoidal : (pullbackStrict α hO hP).Monoidal :=
  letI := pullbackLocalizedMonoidal α hO hP
  letI := toLocalizedMonoidalMonoidal O hO
  letI := fromLocalizedMonoidalMonoidal P hP
  inferInstance

/-- **`pullbackStrictMonoidal` at the spelling `SheafOfModules.pullback`**, which is the one a
consumer writes. The two functors are equal by `pullbackStrict_eq`. -/
@[instance_reducible]
noncomputable def pullbackMonoidalStrict :
    (SheafOfModules.pullback.{w} (sheafRingHom α hO hP)).Monoidal :=
  pullbackStrict_eq α hO hP ▸ pullbackStrictMonoidal α hO hP

end Strict

end Sheaf

end Stacks.PullbackMonoidalSite

end
