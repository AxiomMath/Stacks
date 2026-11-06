module

public import Mathlib.Tactic.TFAE
public import StacksFrontier.AlgebraicGeometry.Descent.RelativeGluingOverBasis
public import StacksFrontier.AlgebraicGeometry.Topologies.ExtendingFunctorsAffineFiniteTypeTests
public import StacksFrontier.AlgebraicGeometry.Topologies.ExtendingFunctorsCoveringSheaf
public import StacksFrontier.AlgebraicGeometry.Topologies.ExtendingFunctorsNoetherianFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Topologies.ExtendingFunctorsStandardAffineDescent
public import StacksFrontier.AlgebraicGeometry.Topologies.ExtendingFunctorsZariskiComparison
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Representability detected on the affine Noetherian test objects

Let `S` be a locally Noetherian scheme, let `τ` be one of the five topologies of
`AlgebraicGeometry.CoveringTopology` and let `F'`, `G'` be limit preserving sheaves on
`(Sch/S)_τ`. For a transformation `a' : F' ⟶ G'`, write `a` for its restriction to the full
subcategory `(Noetherian/S)` of locally Noetherian objects. This file proves the implication
(3) ⇒ (1) of Stacks 0GE5: if `a` is representable at every test object which is affine of finite
type over `S` and maps into an affine open of `S`, then `a'` is representable. Together with the
two implications of
`StacksFrontier.AlgebraicGeometry.Topologies.ExtendingFunctorsNoetherianRepresentable` this closes
the source's list of equivalent conditions.

## Main definitions

* `AlgebraicGeometry.ExtendingFunctors.GluingOpens`: the opens of an object of `Sch/S` which, as
  objects of `Sch/S`, are affine and lie over an affine open of `S`. They form a basis of its
  topology, over which the source glues the representing objects.
* `AlgebraicGeometry.ExtendingFunctors.LocalRepData`: a representing object of the fibre product
  over each member of that basis, with its projection and its section of `F'`.
* `AlgebraicGeometry.ExtendingFunctors.LocalRepData.gluedOver`: the object of `Sch/S` glued out of
  them by Stacks 01LH.

## Main results

* `AlgebraicGeometry.ExtendingFunctors.exists_isPullback_of_isAffineOverAffineOpen`: the affine
  case of the implication (3) ⇒ (1).
* `AlgebraicGeometry.ExtendingFunctors.LocalRepData.exists_isPullback_of_localRepData`: the glued
  object represents the fibre product.
* `relativelyRepresentable_of_isRepresentableOnAffineFiniteType`, in the namespace
  `AlgebraicGeometry.ExtendingFunctors`: **Stacks 0GE5, implication (3) ⇒ (1)**.
* `AlgebraicGeometry.ExtendingFunctors.relativelyRepresentable_tfae`: **Stacks 0GE5**, the three
  criteria assembled into the source's list of equivalent conditions.

## Implementation notes

The source's proof is run as it stands, in two steps.

*The affine case.* An affine object `W` lying over an affine open `U` of `S` is written as a
directed inverse limit of objects of the subcategory of finite presentation over `U` by
`AlgebraicGeometry.ExtendingFunctors.exists_lfpPresentation_finitePresentation`; these stages are
test objects of criterion (3) by
`AlgebraicGeometry.ExtendingFunctors.isAffineFiniteTypeOverAffineOpen_of_finitePresentation`, and
the limit condition on `G'` factors the given section of `G'` over `W` through one of them.
Criterion (3) represents the fibre product over that stage by an object `X` of the subcategory,
which is locally of finite presentation over `S` by Stacks 0GE4 because the fibre product, being a
fibre product of functors with the limit condition, has the limit condition itself. The
identification of the fibre product of `F'` and the stage over `G'` with the functor of points of
`X` is the pointwise uniqueness
`AlgebraicGeometry.ExtendingFunctors.isIso_of_bijective_subcategory` of the extension of Stacks
0EUW: both functors are Zariski sheaves with the limit condition, and the canonical transformation
between them is bijective at every object of the subcategory because both squares are Cartesian
there. Finally the fibre product over `W` is the base change of the fibre product over the stage
along the projection `W ⟶ V`, which is a Cartesian square of functors of points because
`CategoryTheory.uliftYoneda` preserves pullbacks.

*The general case.* The representing objects over the members of the basis glue by Stacks 01LH, in
the form `AlgebraicGeometry.Scheme.BasisGluingData`: the restriction morphism attached to an
inclusion of basis members is produced by the universal property of the fibre product over the
larger one, read through the full faithfulness of `CategoryTheory.uliftYoneda`, which also makes
the restriction squares Cartesian and the cocycle condition automatic. The local sections of `F'`
glue because `F'` is a Zariski sheaf; the compatibility on an overlap of two charts is checked
locally, every point of the overlap having a neighbourhood lying in a third chart, through which
both morphisms then factor. That the glued object represents the fibre product is checked at every
object `A` of `Sch/S`: the opens of `A` lying over the members of the basis cover `A`, over each of
them a morphism to the glued object exists and is unique because the chart identifies the local
representing object with the part of the glued object lying over the corresponding basis member,
and the two local statements glue because the functor of points of the glued object is a Zariski
sheaf.

No closure property of a site is involved: the ambient category is all of `Over S`, so the glued
object is an object of it whatever the sizes of the glued pieces.

| Stacks tag | library name |
|---|---|
| Tag 001X | `CategoryTheory.Functor.relativelyRepresentable` |
| Tag 01LH | `AlgebraicGeometry.Scheme.BasisGluingData.exists_isPullback_res_comp` |
| Tag 0EUW | `AlgebraicGeometry.ExtendingFunctors.exists_unique_extension` |
| Tag 0GE3 | `AlgebraicGeometry.ExtendingFunctors.IsLocallyNoetherianOver` |
| Tag 0GE4 | `locallyOfFinitePresentation_of_preservesAffineLimitsOnSubcategory` |

## References

* [Stacks Project, Tag 0GE5](https://stacks.math.columbia.edu/tag/0GE5)
* [Stacks Project, Tag 0GE4](https://stacks.math.columbia.edu/tag/0GE4)
* [Stacks Project, Tag 0EUW](https://stacks.math.columbia.edu/tag/0EUW)
* [Stacks Project, Tag 01LH](https://stacks.math.columbia.edu/tag/01LH)
-/
@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ExtendingFunctors

universe w u

variable {S : Scheme.{u}}

/-! ### Two Cartesian squares of sets over one cospan -/

section TypePullback

universe v

variable {A A' B K E : Type v} {p : A ⟶ B} {q : A ⟶ K} {p' : A' ⟶ B} {q' : A' ⟶ K}
  {f : B ⟶ E} {g : K ⟶ E}

/-- A map between the upper left corners of two Cartesian squares of sets over the same cospan
which is compatible with both projections is bijective. -/
theorem bijective_of_isPullback_of_isPullback (h : IsPullback p q f g) (h' : IsPullback p' q' f g)
    (θ : A ⟶ A') (hp : ∀ a, p' (θ a) = p a) (hq : ∀ a, q' (θ a) = q a) :
    Function.Bijective θ := by
  refine ⟨fun a b hab => Types.ext_of_isPullback h ?_ ?_, fun t => ?_⟩
  · rw [← hp a, ← hp b, hab]
  · rw [← hq a, ← hq b, hab]
  · obtain ⟨a, ha₁, ha₂⟩ :=
      Types.exists_of_isPullback h (p' t) (q' t) (types_congr_hom h'.w t)
    exact ⟨a, Types.ext_of_isPullback h' (by rw [hp a, ha₁]) (by rw [hq a, ha₂])⟩

end TypePullback

/-! ### A Cartesian square on the subcategory read on `Sch/S` -/

/-- **A Cartesian square on a full subcategory is the restriction of a square on `Sch/S`.** If the
two right-hand corners of the square are the restrictions of functors on `Sch/S` and the two
left-hand corners are the functors of points of objects of the subcategory, then the restriction
of the square assembled from the same data on `Sch/S` is again Cartesian. -/
theorem isPullback_whiskerLeft_of_isPullback_subcategory {P : ObjectProperty (Over S)}
    {F' G' : (Over S)ᵒᵖ ⥤ Type (max w (u + 1))} (a' : F' ⟶ G')
    {X V : P.FullSubcategory} (snd : X ⟶ V)
    (x : F'.obj (op X.obj)) (ξ : G'.obj (op V.obj))
    (hpb : IsPullback
      ((uliftYonedaEquiv.{max w (u + 1)} (X := X) (F := P.ι.op ⋙ F')).symm x)
      ((uliftYoneda.{max w (u + 1)}).map snd) (Functor.whiskerLeft P.ι.op a')
      ((uliftYonedaEquiv.{max w (u + 1)} (X := V) (F := P.ι.op ⋙ G')).symm ξ)) :
    IsPullback (Functor.whiskerLeft P.ι.op (uliftYonedaEquiv.{max w (u + 1)}.symm x))
      (Functor.whiskerLeft P.ι.op ((uliftYoneda.{max w (u + 1)}).map (P.ι.map snd)))
      (Functor.whiskerLeft P.ι.op a')
      (Functor.whiskerLeft P.ι.op (uliftYonedaEquiv.{max w (u + 1)}.symm ξ)) := by
  refine hpb.of_iso (uliftYonedaIotaIso.{max w (u + 1), u, u + 1} P X).symm (Iso.refl _)
    (uliftYonedaIotaIso.{max w (u + 1), u, u + 1} P V).symm (Iso.refl _) ?_ ?_ ?_ ?_
  · ext Z m
    simp [uliftYonedaIotaIso]
  · ext Z m
    simp [uliftYonedaIotaIso]
  · ext Z m
    simp
  · ext Z m
    simp [uliftYonedaIotaIso]

/-! ### The affine case of the implication (3) ⇒ (1) -/

/-- Precomposing the transformation attached to a section `t` with the functor of points of `f`
gives the transformation attached to the pullback of `t` along `f`. -/
private theorem map_comp_uliftYonedaEquiv_symm {F : (Over S)ᵒᵖ ⥤ Type (max w (u + 1))}
    {X Y : Over S} (f : X ⟶ Y) (t : F.obj (op Y)) :
    (uliftYoneda.{max w (u + 1)}).map f ≫ uliftYonedaEquiv.symm t
      = uliftYonedaEquiv.symm (F.map f.op t) :=
  (uliftYonedaEquiv_symm_map.{max w (u + 1)} f.op t).symm

/-- **The affine case of the implication (3) ⇒ (1) of Stacks 0GE5.** Let `S` be a locally
Noetherian scheme and let `a' : F' ⟶ G'` be a transformation of functors on `Sch/S` which are
Zariski sheaves and take directed inverse limits of affine schemes over `S` to filtered colimits.
If the restriction of `a'` to the locally Noetherian objects is representable at every test object
which is affine of finite type over `S` and maps into an affine open of `S`, then for every affine
object `W` of `Sch/S` lying over an affine open of `S` and every section of `G'` over `W` the
fibre product of `F'` and `W` over `G'` is represented by an object of `Sch/S`. -/
theorem exists_isPullback_of_isAffineOverAffineOpen [IsLocallyNoetherian S]
    {F' G' : (Over S)ᵒᵖ ⥤ Type (max w (u + 1))} {a' : F' ⟶ G'}
    (haF' : IsZariskiSheaf F') (haG' : IsZariskiSheaf G')
    (hbF' : PreservesAffineLimits F') (hbG' : PreservesAffineLimits G')
    (h3 : IsRepresentableOnAffineFiniteType.{w}
      (Functor.whiskerLeft (IsLocallyNoetherianOver (S := S)).ι.op a'))
    (W : Over S) (hW : IsAffineOverAffineOpen W) (ξ : G'.obj (op W)) :
    ∃ (U' : Over S) (snd' : U' ⟶ W) (fst' : (uliftYoneda.{max w (u + 1)}).obj U' ⟶ F'),
      IsPullback fst' ((uliftYoneda.{max w (u + 1)}).map snd') a'
        ((uliftYonedaEquiv.{max w (u + 1)} (X := W) (F := G')).symm ξ) := by
  obtain ⟨Λ, _, _, _, D, π, hlim, U, g, haff, hgfac, hgfp⟩ :=
    exists_lfpPresentation_finitePresentation
      (hasFinitePresentationAffines_isLocallyNoetherianOver (S := S)) W hW
  obtain ⟨hcolG⟩ :=
    hbG' Λ (D ⋙ (lfpPart (IsLocallyNoetherianOver (S := S))).ι) haff (Cone.mk W π) hlim
  obtain ⟨l, y, hy⟩ := exists_map_eq_of_isColimit_op G'
    (D ⋙ (lfpPart (IsLocallyNoetherianOver (S := S))).ι) (Cone.mk W π) hcolG ξ
  -- the stage of the presentation through which the section factors, as a test object
  let V : (lfpPart (IsLocallyNoetherianOver (S := S))).FullSubcategory := D.obj (op l)
  let Vp : (IsLocallyNoetherianOver (S := S)).FullSubcategory := ⟨V.obj, V.property.1⟩
  have hVlfp : LocallyOfFinitePresentation V.obj.hom := V.property.2
  have hVtest : IsAffineFiniteTypeOverAffineOpen Vp.obj :=
    isAffineFiniteTypeOverAffineOpen_of_finitePresentation (haff (op l)) U (g (op l))
      (hgfac (op l)) (hgfp (op l))
  obtain ⟨Xs, snd, fst, hpb⟩ := h3 Vp hVtest
    ((uliftYonedaEquiv.{max w (u + 1)} (X := Vp)
      (F := (IsLocallyNoetherianOver (S := S)).ι.op ⋙ G')).symm y)
  obtain ⟨x, rfl⟩ := (uliftYonedaEquiv.{max w (u + 1)} (X := Xs)
    (F := (IsLocallyNoetherianOver (S := S)).ι.op ⋙ F')).symm.surjective fst
  -- Stacks 0GE4: the representing object is locally of finite presentation over `S`
  have hXslfp : LocallyOfFinitePresentation Xs.obj.hom :=
    locallyOfFinitePresentation_of_preservesAffineLimitsOnSubcategory Xs
      (preservesAffineLimitsOnSubcategory_of_isPullback hpb
        (preservesAffineLimitsOnSubcategory_of_preservesAffineLimits hbF')
        (preservesAffineLimitsOnSubcategory_uliftYoneda Vp)
        (preservesAffineLimitsOnSubcategory_of_preservesAffineLimits hbG'))
  have hwhisk := isPullback_whiskerLeft_of_isPullback_subcategory a' snd x y hpb
  -- the same data read on `Sch/S`
  let sndV : Xs.obj ⟶ V.obj := (IsLocallyNoetherianOver (S := S)).ι.map snd
  let fst' : (uliftYoneda.{max w (u + 1)}).obj Xs.obj ⟶ F' :=
    (uliftYonedaEquiv.{max w (u + 1)} (X := Xs.obj) (F := F')).symm x
  let gV : (uliftYoneda.{max w (u + 1)}).obj V.obj ⟶ G' :=
    (uliftYonedaEquiv.{max w (u + 1)} (X := V.obj) (F := G')).symm y
  have hcomm : fst' ≫ a' = (uliftYoneda.{max w (u + 1)}).map sndV ≫ gV := by
    have hx : a'.app (op Xs.obj) x = G'.map sndV.op y := by
      simpa [fst', sndV] using app_apply_comm hpb (op Xs) (ULift.up (𝟙 Xs))
    rw [map_comp_uliftYonedaEquiv_symm, ← hx]
    exact uliftYonedaEquiv_symm_comp (F := F') x a'
  have hpbP : IsPullback (pullback.fst a' gV) (pullback.snd a' gV) a' gV :=
    IsPullback.of_hasPullback a' gV
  let θ : (uliftYoneda.{max w (u + 1)}).obj Xs.obj ⟶ pullback a' gV :=
    pullback.lift fst' ((uliftYoneda.{max w (u + 1)}).map sndV) hcomm
  have hθ : ∀ Z : Over S, IsLocallyNoetherianOver (S := S) Z →
      Function.Bijective (θ.app (op Z)) := by
    intro Z hZ
    refine bijective_of_isPullback_of_isPullback
      (isPullback_app hwhisk (op (⟨Z, hZ⟩ :
        (IsLocallyNoetherianOver (S := S)).FullSubcategory)))
      (isPullback_app hpbP (op Z)) (θ.app (op Z)) (fun a => ?_) (fun a => ?_)
    · exact types_congr_hom (NatTrans.congr_app
        (pullback.lift_fst fst' ((uliftYoneda.{max w (u + 1)}).map sndV) hcomm) (op Z)) a
    · exact types_congr_hom (NatTrans.congr_app
        (pullback.lift_snd fst' ((uliftYoneda.{max w (u + 1)}).map sndV) hcomm) (op Z)) a
  have : IsIso θ :=
    isIso_of_bijective_subcategory hasFinitePresentationAffines_isLocallyNoetherianOver
      (isZariskiSheaf_uliftYoneda Xs.obj)
      (isZariskiSheaf_of_isPullback hpbP haF' (isZariskiSheaf_uliftYoneda V.obj) haG')
      (preservesAffineLimits_uliftYoneda Xs.obj)
      (preservesAffineLimits_of_isPullback hpbP hbF'
        (preservesAffineLimits_uliftYoneda V.obj) hbG')
      θ hθ
  have hsq : IsPullback fst' ((uliftYoneda.{max w (u + 1)}).map sndV) a' gV :=
    IsPullback.of_iso_pullback ⟨hcomm⟩ (asIso θ) (pullback.lift_fst _ _ _)
      (pullback.lift_snd _ _ _)
  -- the fibre product over `W` is the base change of the fibre product over the stage
  have hξ : (uliftYonedaEquiv.{max w (u + 1)} (X := W) (F := G')).symm ξ
      = (uliftYoneda.{max w (u + 1)}).map (π.app (op l)) ≫ gV := by
    rw [map_comp_uliftYonedaEquiv_symm, hy]
  refine ⟨pullback sndV (π.app (op l)), pullback.snd sndV (π.app (op l)),
    (uliftYoneda.{max w (u + 1)}).map (pullback.fst sndV (π.app (op l))) ≫ fst', ?_⟩
  rw [hξ]
  exact ((IsPullback.of_hasPullback sndV (π.app (op l))).map
    (uliftYoneda.{max w (u + 1)})).paste_horiz hsq

/-! ### Recognizing a Cartesian square of functors on `Sch/S` -/

/-- **A square of functors which has the universal property of a fibre product at every object is
Cartesian.** -/
theorem isPullback_of_forall_existsUnique
    {A B K E : (Over S)ᵒᵖ ⥤ Type (max w (u + 1))} {p : A ⟶ B} {q : A ⟶ K} {f : B ⟶ E} {g : K ⟶ E}
    (hw : p ≫ f = q ≫ g)
    (h : ∀ (Z : (Over S)ᵒᵖ) (b : B.obj Z) (c : K.obj Z), f.app Z b = g.app Z c →
      ∃! a : A.obj Z, p.app Z a = b ∧ q.app Z a = c) :
    IsPullback p q f g := by
  have hpbP : IsPullback (pullback.fst f g) (pullback.snd f g) f g :=
    IsPullback.of_hasPullback f g
  have hp : ∀ (Z : (Over S)ᵒᵖ) (a : A.obj Z),
      (pullback.fst f g).app Z ((pullback.lift p q hw).app Z a) = p.app Z a :=
    fun Z a => types_congr_hom (NatTrans.congr_app (pullback.lift_fst p q hw) Z) a
  have hq : ∀ (Z : (Over S)ᵒᵖ) (a : A.obj Z),
      (pullback.snd f g).app Z ((pullback.lift p q hw).app Z a) = q.app Z a :=
    fun Z a => types_congr_hom (NatTrans.congr_app (pullback.lift_snd p q hw) Z) a
  have hiso : ∀ Z : (Over S)ᵒᵖ, IsIso ((pullback.lift p q hw).app Z) := by
    intro Z
    rw [CategoryTheory.isIso_iff_bijective]
    refine ⟨fun a a' haa' => ?_, fun t => ?_⟩
    · refine (h Z (p.app Z a) (q.app Z a)
        (types_congr_hom (NatTrans.congr_app hw Z) a)).unique ⟨rfl, rfl⟩ ⟨?_, ?_⟩
      · rw [← hp Z a', ← haa', hp Z a]
      · rw [← hq Z a', ← haa', hq Z a]
    · obtain ⟨a, ⟨ha₁, ha₂⟩, -⟩ := h Z ((pullback.fst f g).app Z t)
        ((pullback.snd f g).app Z t) (types_congr_hom (NatTrans.congr_app hpbP.w Z) t)
      exact ⟨a, Types.ext_of_isPullback (isPullback_app hpbP Z)
        (by rw [hp Z a, ha₁]) (by rw [hq Z a, ha₂])⟩
  have : IsIso (pullback.lift p q hw) := NatIso.isIso_of_isIso_app _
  exact IsPullback.of_iso_pullback ⟨hw⟩ (asIso (pullback.lift p q hw))
    (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)

/-! ### Open subobjects of an object of `Sch/S`, continued -/

/-- The inclusions of open subobjects compose: for `V ≤ W ≤ Y`, including `V` in `W` and then `W`
in `Y` is the inclusion of `V` in `Y`. -/
@[simp]
lemma overOpenLE_comp_overOpenLE (X : Over S) {V W Y : X.left.Opens} (h₁ : V ≤ W) (h₂ : W ≤ Y) :
    overOpenLE X h₁ ≫ overOpenLE X h₂ = overOpenLE X (h₁.trans h₂) := by
  apply Over.OverMorphism.ext
  simp

/-- The restriction of a morphism of `Sch/S` to the part of its source lying over an open of its
target. -/
@[implicit_reducible]
noncomputable def overOpenRestrict {A T : Over S} (m : A ⟶ T) (V : T.left.Opens) :
    overOpen A (m.left ⁻¹ᵁ V) ⟶ overOpen T V :=
  Over.homMk (m.left.resLE V (m.left ⁻¹ᵁ V) le_rfl) (by
    simp only [overOpen_hom]
    rw [← Category.assoc, Scheme.Hom.resLE_comp_ι, Category.assoc, Over.w m])

/-- The restriction of `m` over `V`, followed by the inclusion of `V` into `T`, is the inclusion of
the preimage of `V` into `A` followed by `m`. -/
@[simp]
lemma overOpenRestrict_comp_overOpenι {A T : Over S} (m : A ⟶ T) (V : T.left.Opens) :
    overOpenRestrict m V ≫ overOpenι T V = overOpenι A (m.left ⁻¹ᵁ V) ≫ m := by
  refine Over.OverMorphism.ext ?_
  rw [Over.comp_left, Over.comp_left, overOpenι_left, overOpenι_left]
  exact Scheme.Hom.resLE_comp_ι m.left _

/-- The section of `G'` over an open subobject of `T` cut out by a section over `T`, read as a
transformation out of the functor of points of that open subobject. -/
noncomputable def baseHom {G' : (Over S)ᵒᵖ ⥤ Type (max w (u + 1))} {T : Over S}
    (ξ : G'.obj (op T)) (V : T.left.Opens) :
    (uliftYoneda.{max w (u + 1)}).obj (overOpen T V) ⟶ G' :=
  (uliftYonedaEquiv.{max w (u + 1)} (X := overOpen T V) (F := G')).symm
    (G'.map (overOpenι T V).op ξ)

/-- For `V ≤ W`, the transformation attached to `ξ` over `W`, precomposed with the inclusion of
`V` into `W`, is the transformation attached to `ξ` over `V`. -/
lemma map_comp_baseHom {G' : (Over S)ᵒᵖ ⥤ Type (max w (u + 1))} {T : Over S}
    (ξ : G'.obj (op T)) {V W : T.left.Opens} (h : V ≤ W) :
    (uliftYoneda.{max w (u + 1)}).map (overOpenLE T h) ≫ baseHom.{w} ξ W = baseHom.{w} ξ V := by
  rw [baseHom, baseHom, map_comp_uliftYonedaEquiv_symm, ← Functor.map_comp_apply, ← op_comp,
    overOpenLE_comp_overOpenι]

/-! ### The local data glued by the implication (3) ⇒ (1) -/

/-- The opens of an object `T` of `Sch/S` which, as objects of `Sch/S`, are affine and lie over an
affine open of `S`. They form a basis of the topology of `T`, over which Stacks 0GE5 glues the
representing objects of the fibre products. -/
def GluingOpens (T : Over S) : Set T.left.Opens :=
  {V | IsAffineOverAffineOpen (overOpen T V)}

/-- The opens `AlgebraicGeometry.ExtendingFunctors.GluingOpens T` form a basis of the topology of
`T`. -/
theorem isBasis_gluingOpens (T : Over S) :
    TopologicalSpace.Opens.IsBasis (GluingOpens T) :=
  isBasis_isAffineOverAffineOpen T

/-- The local data out of which the implication (3) ⇒ (1) of Stacks 0GE5 glues a representing
object: over each member of the basis `AlgebraicGeometry.ExtendingFunctors.GluingOpens` an object
of `Sch/S` representing the fibre product of `F'` and that member over `G'`, given by its
projection to the member and its section of `F'`. -/
structure LocalRepData {F' G' : (Over S)ᵒᵖ ⥤ Type (max w (u + 1))} (a' : F' ⟶ G')
    (T : Over S) (ξ : G'.obj (op T)) where
  /-- The representing object over a member of the basis. -/
  obj : GluingOpens T → Over S
  /-- Its projection to the member of the basis. -/
  proj (V : GluingOpens T) : obj V ⟶ overOpen T V.1
  /-- Its section of `F'`. -/
  sectionF (V : GluingOpens T) : F'.obj (op (obj V))
  /-- The square it forms is Cartesian. -/
  isPullback (V : GluingOpens T) :
    IsPullback ((uliftYonedaEquiv.{max w (u + 1)} (X := obj V) (F := F')).symm (sectionF V))
      ((uliftYoneda.{max w (u + 1)}).map (proj V)) a' (baseHom.{w} ξ V.1)

namespace LocalRepData

variable {F' G' : (Over S)ᵒᵖ ⥤ Type (max w (u + 1))} {a' : F' ⟶ G'} {T : Over S}
  {ξ : G'.obj (op T)} (L : LocalRepData.{w} a' T ξ)

/-- The section of `F'` over a local representing object, read as a transformation. -/
noncomputable def sectionHom (V : GluingOpens T) :
    (uliftYoneda.{max w (u + 1)}).obj (L.obj V) ⟶ F' :=
  (uliftYonedaEquiv.{max w (u + 1)} (X := L.obj V) (F := F')).symm (L.sectionF V)

/-- The square of a local representing object is Cartesian, stated with `sectionHom`. -/
lemma isPullback' (V : GluingOpens T) :
    IsPullback (L.sectionHom V) ((uliftYoneda.{max w (u + 1)}).map (L.proj V)) a'
      (baseHom.{w} ξ V.1) :=
  L.isPullback V

/-- The transformation out of the functor of points of the local representing object over `V`
into that of the one over `U`, for `V ≤ U`, produced by the universal property over `U`. -/
noncomputable def resHom {V U : GluingOpens T} (h : V.1 ≤ U.1) :
    (uliftYoneda.{max w (u + 1)}).obj (L.obj V) ⟶ (uliftYoneda.{max w (u + 1)}).obj (L.obj U) :=
  (L.isPullback' U).lift (L.sectionHom V)
    ((uliftYoneda.{max w (u + 1)}).map (L.proj V) ≫
      (uliftYoneda.{max w (u + 1)}).map (overOpenLE T h))
    (by rw [Category.assoc, map_comp_baseHom ξ h]; exact (L.isPullback' V).w)

/-- The restriction morphism of the gluing datum: the local representing object over `V` is the
part of the one over `U` lying over `V`, for `V ≤ U` in the basis. -/
noncomputable def res {V U : GluingOpens T} (h : V.1 ≤ U.1) : L.obj V ⟶ L.obj U :=
  (uliftYoneda.{max w (u + 1)}).preimage (L.resHom h)

/-- On functors of points, the restriction morphism `res h` is `resHom h`. -/
@[simp]
lemma map_res {V U : GluingOpens T} (h : V.1 ≤ U.1) :
    (uliftYoneda.{max w (u + 1)}).map (L.res h) = L.resHom h :=
  Functor.map_preimage _ _

/-- The transformation `resHom h` is compatible with the sections of `F'`. -/
lemma resHom_comp_sectionHom {V U : GluingOpens T} (h : V.1 ≤ U.1) :
    L.resHom h ≫ L.sectionHom U = L.sectionHom V :=
  (L.isPullback' U).lift_fst _ _ _

/-- The transformation `resHom h` is compatible with the projections to the members of the basis
and the inclusion of `V` into `U`. -/
lemma resHom_comp_map_proj {V U : GluingOpens T} (h : V.1 ≤ U.1) :
    L.resHom h ≫ (uliftYoneda.{max w (u + 1)}).map (L.proj U) =
      (uliftYoneda.{max w (u + 1)}).map (L.proj V) ≫
        (uliftYoneda.{max w (u + 1)}).map (overOpenLE T h) :=
  (L.isPullback' U).lift_snd _ _ _

/-- The restriction morphism `res h` lies over the inclusion of `V` into `U`. -/
lemma res_comp_proj {V U : GluingOpens T} (h : V.1 ≤ U.1) :
    L.res h ≫ L.proj U = L.proj V ≫ overOpenLE T h := by
  refine (uliftYoneda.{max w (u + 1)}).map_injective ?_
  rw [Functor.map_comp, Functor.map_comp, map_res]
  exact L.resHom_comp_map_proj h

/-- The section of `F'` over `U` pulls back along `res h` to the section of `F'` over `V`. -/
lemma map_res_sectionF {V U : GluingOpens T} (h : V.1 ≤ U.1) :
    F'.map (L.res h).op (L.sectionF U) = L.sectionF V := by
  refine (uliftYonedaEquiv.{max w (u + 1)} (X := L.obj V) (F := F')).symm.injective ?_
  rw [← map_comp_uliftYonedaEquiv_symm, ← sectionHom, ← sectionHom, map_res,
    L.resHom_comp_sectionHom h]

/-- The local representing object over `V` is the pullback of the one over `U` along the inclusion
of `V` into `U`, with `res h` as the comparison morphism. -/
lemma isPullback_res {V U : GluingOpens T} (h : V.1 ≤ U.1) :
    IsPullback (L.res h) (L.proj V) (L.proj U) (overOpenLE T h) := by
  refine IsPullback.of_map_of_faithful (uliftYoneda.{max w (u + 1)}) ?_
  rw [map_res]
  refine IsPullback.of_right ?_ (L.resHom_comp_map_proj h) (L.isPullback' U)
  rw [L.resHom_comp_sectionHom h, map_comp_baseHom ξ h]
  exact L.isPullback' V

/-- The restriction morphisms are transitive: for `W ≤ V ≤ U`, restricting from `W` to `U` is
restricting from `W` to `V` and then from `V` to `U`. -/
lemma res_trans {W V U : GluingOpens T} (hWV : W.1 ≤ V.1) (hVU : V.1 ≤ U.1) :
    L.res (hWV.trans hVU) = L.res hWV ≫ L.res hVU := by
  refine (uliftYoneda.{max w (u + 1)}).map_injective ?_
  rw [Functor.map_comp, map_res, map_res, map_res]
  refine (L.isPullback' U).hom_ext ?_ ?_
  · rw [L.resHom_comp_sectionHom, Category.assoc, L.resHom_comp_sectionHom,
      L.resHom_comp_sectionHom]
  · rw [L.resHom_comp_map_proj, Category.assoc, L.resHom_comp_map_proj, ← Category.assoc,
      L.resHom_comp_map_proj, Category.assoc, ← Functor.map_comp, ← Functor.map_comp,
      overOpenLE_comp_overOpenLE, Functor.map_comp]

/-- The gluing datum over the basis of `T` assembled from the local representing objects. -/
@[implicit_reducible]
noncomputable def gluingData : Scheme.BasisGluingData T.left (GluingOpens T) where
  obj V := (L.obj V).left
  proj V := (L.proj V).left
  res h := (L.res h).left
  isPullback_res h := (L.isPullback_res h).map (Over.forget S)
  res_trans hWV hVU := by rw [L.res_trans hWV hVU, Over.comp_left]

/-! ### The glued object -/

/-- The scheme glued from the local representing objects, by Stacks 01LH. -/
@[implicit_reducible]
noncomputable def glued : Scheme.{u} :=
  L.gluingData.glued (isBasis_gluingOpens T)

/-- Its structure morphism to the underlying scheme of `T`. -/
@[implicit_reducible]
noncomputable def toT : L.glued ⟶ T.left :=
  L.gluingData.toBase (isBasis_gluingOpens T)

/-- The glued object, read as an object of `Sch/S`. -/
@[implicit_reducible]
noncomputable def gluedOver : Over S := Over.mk (L.toT ≫ T.hom)

/-- The structure morphism of `gluedOver` is `toT` followed by the structure morphism of `T`. -/
@[simp]
lemma gluedOver_hom : L.gluedOver.hom = L.toT ≫ T.hom := rfl

/-- The structure morphism of the glued object to `T`, as a morphism of `Sch/S`. -/
@[implicit_reducible]
noncomputable def toOver : L.gluedOver ⟶ T := Over.homMk L.toT

/-- The underlying morphism of schemes of `toOver` is `toT`. -/
@[simp]
lemma toOver_left : L.toOver.left = L.toT := rfl

/-- The chart of the glued object attached to a member of the basis, as a morphism of
`Sch/S`. -/
@[implicit_reducible]
noncomputable def chartOver (V : GluingOpens T) : L.obj V ⟶ L.gluedOver :=
  Over.homMk (L.gluingData.chart (isBasis_gluingOpens T) V) (by
    have hw : (L.proj V).left ≫ V.1.ι
        = L.gluingData.chart (isBasis_gluingOpens T) V ≫ L.toT :=
      (L.gluingData.isPullback_proj_chart (isBasis_gluingOpens T) V).w
    rw [gluedOver_hom, ← Category.assoc, ← hw, Category.assoc]
    exact Over.w (L.proj V))

/-- The underlying morphism of schemes of `chartOver V` is the chart of the gluing datum. -/
@[simp]
lemma chartOver_left (V : GluingOpens T) :
    (L.chartOver V).left = L.gluingData.chart (isBasis_gluingOpens T) V := rfl

/-- **The chart identifies the local representing object with the part of the glued object lying
over the corresponding member of the basis.** -/
lemma isPullback_chartOver (V : GluingOpens T) :
    IsPullback (L.proj V) (L.chartOver V) (overOpenι T V.1) L.toOver :=
  IsPullback.of_map_of_faithful (Over.forget S)
    (L.gluingData.isPullback_proj_chart (isBasis_gluingOpens T) V)

/-- The Cartesian square `isPullback_chartOver` on underlying schemes. -/
lemma isPullback_chartOver_left (V : GluingOpens T) :
    IsPullback (L.proj V).left (L.chartOver V).left (overOpenι T V.1).left L.toOver.left :=
  (L.isPullback_chartOver V).map (Over.forget S)

/-- The chart over `V` followed by the morphism to `T` is the projection to `V` followed by the
inclusion of `V` into `T`. -/
lemma chartOver_comp_toOver (V : GluingOpens T) :
    L.chartOver V ≫ L.toOver = L.proj V ≫ overOpenι T V.1 :=
  ((L.isPullback_chartOver V).w).symm

/-- Each chart of the glued object is an open immersion. -/
instance isOpenImmersion_chartOver (V : GluingOpens T) :
    IsOpenImmersion (L.chartOver V).left := by
  have hι : IsOpenImmersion (overOpenι T V.1).left := by
    rw [overOpenι_left]
    infer_instance
  exact MorphismProperty.of_isPullback (L.isPullback_chartOver_left V) hι

/-- The charts are compatible with the restriction morphisms: for `V ≤ U`, `res h` followed by
the chart over `U` is the chart over `V`. -/
lemma res_comp_chartOver {V U : GluingOpens T} (h : V.1 ≤ U.1) :
    L.res h ≫ L.chartOver U = L.chartOver V := by
  refine Over.OverMorphism.ext ?_
  rw [Over.comp_left]
  exact L.gluingData.res_comp_chart (isBasis_gluingOpens T) h

/-- The open subobject of the glued object which is the image of a chart. -/
@[implicit_reducible]
noncomputable def chartRange (V : GluingOpens T) : L.gluedOver.left.Opens :=
  (L.chartOver V).left.opensRange

/-- A point in the image of a morphism factoring through the chart over `V` lies in
`chartRange V`. -/
lemma mem_chartRange_apply {V : GluingOpens T} {A : Over S} (k : A ⟶ L.obj V) (z : A.left) :
    (k ≫ L.chartOver V).left z ∈ L.chartRange V := by
  refine ⟨k.left z, ?_⟩
  rw [Over.comp_left]
  exact (Scheme.Hom.comp_apply k.left (L.chartOver V).left z).symm

/-- A point of `chartRange V` maps into `V` under the morphism to `T`. -/
lemma toOver_mem_of_mem_chartRange {V : GluingOpens T} {z : L.gluedOver.left}
    (hz : z ∈ L.chartRange V) : L.toOver.left z ∈ V.1 := by
  obtain ⟨y, rfl⟩ := hz
  have h := congrArg Over.Hom.left (L.chartOver_comp_toOver V)
  rw [Over.comp_left, Over.comp_left] at h
  rw [← Scheme.Hom.comp_apply, h, Scheme.Hom.comp_apply]
  exact ((L.proj V).left y).2

/-- A point of the glued object which maps into `V` under the morphism to `T` lies in
`chartRange V`. -/
lemma mem_chartRange_of_toOver_mem (V : GluingOpens T) (z : L.gluedOver.left)
    (hz : L.toOver.left z ∈ V.1) : z ∈ L.chartRange V := by
  obtain ⟨y, -, hy⟩ := Scheme.exists_preimage_of_isPullback
    (L.isPullback_chartOver_left V) ⟨L.toOver.left z, hz⟩ z rfl
  exact ⟨y, hy⟩

/-- The images of the charts cover the glued object. -/
lemma iSup_chartRange : ⨆ V : GluingOpens T, L.chartRange V = ⊤ := by
  refine le_antisymm le_top fun z _ => ?_
  obtain ⟨V, hV, hmem, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp
    (isBasis_gluingOpens T) (U := ⊤) (TopologicalSpace.Opens.mem_top (L.toOver.left z))
  exact TopologicalSpace.Opens.mem_iSup.mpr
    ⟨⟨V, hV⟩, L.mem_chartRange_of_toOver_mem ⟨V, hV⟩ z hmem⟩

/-! ### Compatibility of the local sections of `F'` -/

/-- A morphism to the glued object whose underlying map has range inside the image of the chart
over `V` factors through that chart. -/
private lemma exists_comp_chartOver_eq {A : Over S} (V : GluingOpens T) (p : A ⟶ L.gluedOver)
    (hr : Set.range (⇑p.left) ⊆ Set.range (⇑(L.chartOver V).left)) :
    ∃ q : A ⟶ L.obj V, q ≫ L.chartOver V = p := by
  refine ⟨Over.homMk (IsOpenImmersion.lift (L.chartOver V).left p.left hr) ?_, ?_⟩
  · have h1 : (L.obj V).hom = (L.chartOver V).left ≫ L.gluedOver.hom :=
      (Over.w (L.chartOver V)).symm
    rw [h1, ← Category.assoc, IsOpenImmersion.lift_fac]
    exact Over.w p
  · refine Over.OverMorphism.ext ?_
    rw [Over.comp_left]
    exact IsOpenImmersion.lift_fac _ _ hr

/-- Over an open of `A` whose image in the glued object lies in the chart of `W`, two morphisms
into the local representing objects which become equal in the glued object both factor through
the local representing object over `W`, so the two sections of `F'` pull back to the same
section. -/
private lemma sectionF_compat_aux {A : Over S} {V U W : GluingOpens T}
    (α : A ⟶ L.obj V) (β : A ⟶ L.obj U) (hαβ : α ≫ L.chartOver V = β ≫ L.chartOver U)
    (hWV : W.1 ≤ V.1) (hWU : W.1 ≤ U.1) (O : A.left.Opens)
    (hO : ∀ y : O, (α ≫ L.chartOver V).left y.1 ∈ L.chartRange W) :
    F'.map (overOpenι A O).op (F'.map α.op (L.sectionF V))
      = F'.map (overOpenι A O).op (F'.map β.op (L.sectionF U)) := by
  have hr : Set.range (⇑(overOpenι A O ≫ α ≫ L.chartOver V).left)
      ⊆ Set.range (⇑(L.chartOver W).left) := by
    rintro _ ⟨y, rfl⟩
    exact hO y
  obtain ⟨δ, hδ⟩ := L.exists_comp_chartOver_eq W (overOpenι A O ≫ α ≫ L.chartOver V) hr
  have hcancel : ∀ {X : GluingOpens T} {k l : overOpen A O ⟶ L.obj X},
      k ≫ L.chartOver X = l ≫ L.chartOver X → k = l := fun {X} {k l} =>
    have := Over.mono_of_mono_left (L.chartOver X)
    (cancel_mono (L.chartOver X)).mp
  have hα : overOpenι A O ≫ α = δ ≫ L.res hWV := by
    refine hcancel ?_
    rw [Category.assoc, Category.assoc, L.res_comp_chartOver, hδ]
  have hβ : overOpenι A O ≫ β = δ ≫ L.res hWU := by
    refine hcancel ?_
    rw [Category.assoc, Category.assoc, L.res_comp_chartOver, hδ, ← hαβ]
  rw [← Functor.map_comp_apply, ← op_comp, ← Functor.map_comp_apply, ← op_comp, hα, hβ,
    op_comp, Functor.map_comp_apply, op_comp, Functor.map_comp_apply, L.map_res_sectionF,
    L.map_res_sectionF]

/-- **Two local sections of `F'` agree wherever the two charts agree.** Given morphisms into two
local representing objects which become equal in the glued object, the two sections of `F'` pull
back to the same section of `F'`: every point of the source has a neighbourhood over which both
morphisms factor through one and the same local representing object, and `F'` is a Zariski
sheaf. -/
lemma sectionF_compat (haF' : IsZariskiSheaf F') {A : Over S} {V U : GluingOpens T}
    (α : A ⟶ L.obj V) (β : A ⟶ L.obj U)
    (hαβ : α ≫ L.chartOver V = β ≫ L.chartOver U) :
    F'.map α.op (L.sectionF V) = F'.map β.op (L.sectionF U) := by
  classical
  have hpt : ∀ z : A.left, ∃ W : GluingOpens T, W.1 ≤ V.1 ⊓ U.1 ∧
      (α ≫ L.chartOver V).left z ∈ L.chartRange W := by
    intro z
    have hV : L.toOver.left ((α ≫ L.chartOver V).left z) ∈ V.1 :=
      L.toOver_mem_of_mem_chartRange (L.mem_chartRange_apply α z)
    have hU : L.toOver.left ((α ≫ L.chartOver V).left z) ∈ U.1 := by
      rw [hαβ]
      exact L.toOver_mem_of_mem_chartRange (L.mem_chartRange_apply β z)
    obtain ⟨W, hW, hmem, hle⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp
      (isBasis_gluingOpens T) (show L.toOver.left ((α ≫ L.chartOver V).left z) ∈ V.1 ⊓ U.1
        from ⟨hV, hU⟩)
    exact ⟨⟨W, hW⟩, hle, L.mem_chartRange_of_toOver_mem ⟨W, hW⟩ _ hmem⟩
  choose Wz hWz hmemz using hpt
  refine zariskiSheaf_ext haF'
    (fun z : A.left => (α ≫ L.chartOver V).left ⁻¹ᵁ L.chartRange (Wz z))
    (le_antisymm le_top fun z _ => TopologicalSpace.Opens.mem_iSup.mpr ⟨z, hmemz z⟩) _ _
    fun z => ?_
  exact L.sectionF_compat_aux α β hαβ ((hWz z).trans inf_le_left)
    ((hWz z).trans inf_le_right) _ fun y => y.2

/-! ### The glued section of `F'` -/

/-- **The local sections of `F'` glue to a section over the glued object.** The local sections
agree on the overlaps of the charts by
`AlgebraicGeometry.ExtendingFunctors.LocalRepData.sectionF_compat`, and `F'` is a Zariski
sheaf. -/
lemma exists_sectionGlued (haF' : IsZariskiSheaf F') :
    ∃ x : F'.obj (op L.gluedOver), ∀ V : GluingOpens T,
      F'.map (L.chartOver V).op x = L.sectionF V := by
  have hcompat : ∀ V U : GluingOpens T,
      F'.map (overOpenLE L.gluedOver (inf_le_left :
          (L.chartOver V).left.opensRange ⊓ (L.chartOver U).left.opensRange ≤
            (L.chartOver V).left.opensRange)).op
        (F'.map ((overOpenIso (L.chartOver V)).inv).op (L.sectionF V))
      = F'.map (overOpenLE L.gluedOver (inf_le_right :
          (L.chartOver V).left.opensRange ⊓ (L.chartOver U).left.opensRange ≤
            (L.chartOver U).left.opensRange)).op
        (F'.map ((overOpenIso (L.chartOver U)).inv).op (L.sectionF U)) := by
    intro V U
    rw [← Functor.map_comp_apply, ← op_comp, ← Functor.map_comp_apply, ← op_comp]
    refine L.sectionF_compat haF' _ _ ?_
    rw [Category.assoc, Category.assoc, overOpenIso_inv_comp, overOpenIso_inv_comp,
      overOpenLE_comp_overOpenι, overOpenLE_comp_overOpenι]
  obtain ⟨x, hx, -⟩ := haF' L.gluedOver (GluingOpens T)
    (fun V => (L.chartOver V).left.opensRange) L.iSup_chartRange _ hcompat
  refine ⟨x, fun V => ?_⟩
  have hmor : (overOpenIso (L.chartOver V)).hom
      ≫ overOpenι L.gluedOver ((L.chartOver V).left.opensRange) = L.chartOver V := by
    rw [← overOpenIso_inv_comp (L.chartOver V), ← Category.assoc, Iso.hom_inv_id,
      Category.id_comp]
  have h := congrArg (F'.map ((overOpenIso (L.chartOver V)).hom).op) (hx V)
  rw [← Functor.map_comp_apply, ← op_comp, ← Functor.map_comp_apply, ← op_comp, hmor,
    Iso.hom_inv_id, op_id, Functor.map_id_apply] at h
  exact h

/-- The image under `a'` of the section of `F'` over the local representing object over `V` is
the pullback along its projection of the restriction of `ξ` to `V`. -/
lemma app_sectionF (V : GluingOpens T) :
    a'.app (op (L.obj V)) (L.sectionF V)
      = G'.map (L.proj V).op (G'.map (overOpenι T V.1).op ξ) := by
  simpa [sectionHom, baseHom] using
    app_apply_comm (L.isPullback' V) (op (L.obj V)) (ULift.up (𝟙 (L.obj V)))

/-- Two sections of a Zariski sheaf over the glued object which agree on every chart are
equal. -/
lemma ext_of_map_chartOver {M : (Over S)ᵒᵖ ⥤ Type (max w (u + 1))} (haM : IsZariskiSheaf M)
    {t t' : M.obj (op L.gluedOver)}
    (h : ∀ V : GluingOpens T, M.map (L.chartOver V).op t = M.map (L.chartOver V).op t') :
    t = t' := by
  refine zariskiSheaf_ext haM (fun V : GluingOpens T => (L.chartOver V).left.opensRange)
    L.iSup_chartRange t t' fun V => ?_
  rw [← overOpenIso_inv_comp (L.chartOver V), op_comp, Functor.map_comp_apply,
    Functor.map_comp_apply, h V]

/-! ### Morphisms to the glued object over a member of the basis -/

section OverBasis

variable {xF : F'.obj (op L.gluedOver)}

/-- **Existence of a morphism to the glued object, over a member of the basis.** A section of `F'`
over an object lying over a member of the basis which lifts the given section of `G'` comes from a
morphism to the glued object. -/
lemma exists_hom_over_basis
    (hxF : ∀ V : GluingOpens T, F'.map (L.chartOver V).op xF = L.sectionF V)
    {A' : Over S} (V : GluingOpens T) (k : A' ⟶ overOpen T V.1) (xb : F'.obj (op A'))
    (hb : a'.app (op A') xb = G'.map k.op (G'.map (overOpenι T V.1).op ξ)) :
    ∃ n : A' ⟶ L.gluedOver, F'.map n.op xF = xb ∧ n ≫ L.toOver = k ≫ overOpenι T V.1 := by
  obtain ⟨t₀, ht₁, ht₂⟩ := Types.exists_of_isPullback
    (isPullback_app (L.isPullback' V) (op A')) xb (ULift.up k) (by simpa [baseHom] using hb)
  have hk : t₀.down ≫ L.proj V = k := by simpa using congrArg ULift.down ht₂
  refine ⟨t₀.down ≫ L.chartOver V, ?_, ?_⟩
  · rw [op_comp, Functor.map_comp_apply, hxF V]
    simpa [sectionHom] using ht₁
  · rw [Category.assoc, L.chartOver_comp_toOver, ← Category.assoc, hk]

/-- **Uniqueness of a morphism to the glued object, over a member of the basis.** -/
lemma eq_of_hom_over_basis
    (hxF : ∀ V : GluingOpens T, F'.map (L.chartOver V).op xF = L.sectionF V)
    {A' : Over S} (V : GluingOpens T) (k : A' ⟶ overOpen T V.1) (xb : F'.obj (op A'))
    {n n' : A' ⟶ L.gluedOver}
    (hn₁ : F'.map n.op xF = xb) (hn₂ : n ≫ L.toOver = k ≫ overOpenι T V.1)
    (hn₁' : F'.map n'.op xF = xb) (hn₂' : n' ≫ L.toOver = k ≫ overOpenι T V.1) :
    n = n' := by
  have hfactor : ∀ p : A' ⟶ L.gluedOver, p ≫ L.toOver = k ≫ overOpenι T V.1 →
      ∃ q : A' ⟶ L.obj V, q ≫ L.chartOver V = p := by
    intro p hp
    have hrange : Set.range (⇑p.left) ⊆ Set.range (⇑(L.chartOver V).left) := by
      rintro _ ⟨y, rfl⟩
      refine L.mem_chartRange_of_toOver_mem V (p.left y) ?_
      have h := congrArg Over.Hom.left hp
      rw [Over.comp_left, Over.comp_left, overOpenι_left] at h
      rw [← Scheme.Hom.comp_apply, h, Scheme.Hom.comp_apply]
      exact (k.left y).2
    exact L.exists_comp_chartOver_eq V p hrange
  have hmono : ∀ {c c' : A' ⟶ overOpen T V.1},
      c ≫ overOpenι T V.1 = c' ≫ overOpenι T V.1 → c = c' := by
    intro c c' hcc'
    refine Over.OverMorphism.ext ?_
    have h := congrArg Over.Hom.left hcc'
    rw [Over.comp_left, Over.comp_left, overOpenι_left] at h
    exact (cancel_mono V.1.ι).mp h
  have hqk : ∀ {p : A' ⟶ L.gluedOver} {q : A' ⟶ L.obj V}, q ≫ L.chartOver V = p →
      p ≫ L.toOver = k ≫ overOpenι T V.1 → q ≫ L.proj V = k := by
    intro p q hqp hp
    refine hmono ?_
    rw [Category.assoc, ← L.chartOver_comp_toOver, ← Category.assoc, hqp, hp]
  have hqF : ∀ {p : A' ⟶ L.gluedOver} {q : A' ⟶ L.obj V}, q ≫ L.chartOver V = p →
      F'.map p.op xF = xb → F'.map q.op (L.sectionF V) = xb := by
    intro p q hqp hp
    rw [← hxF V, ← Functor.map_comp_apply, ← op_comp, hqp]
    exact hp
  obtain ⟨q, hq⟩ := hfactor n hn₂
  obtain ⟨q', hq'⟩ := hfactor n' hn₂'
  have h1 : (L.sectionHom V).app (op A') (ULift.up q)
      = (L.sectionHom V).app (op A') (ULift.up q') := by
    simpa [sectionHom] using (hqF hq hn₁).trans (hqF hq' hn₁').symm
  have h2 : ((uliftYoneda.{max w (u + 1)}).map (L.proj V)).app (op A') (ULift.up q)
      = ((uliftYoneda.{max w (u + 1)}).map (L.proj V)).app (op A') (ULift.up q') :=
    congrArg ULift.up ((hqk hq hn₂).trans (hqk hq' hn₂').symm)
  have hqq' : (ULift.up q : ((uliftYoneda.{max w (u + 1)}).obj (L.obj V)).obj (op A'))
      = ULift.up q' :=
    Types.ext_of_isPullback (isPullback_app (L.isPullback' V) (op A')) h1 h2
  rw [← hq, ← hq']
  exact congrArg (fun r => r ≫ L.chartOver V) (congrArg ULift.down hqq')

/-! ### The implication (3) ⇒ (1) once the local data is given -/

/-- The opens `AlgebraicGeometry.ExtendingFunctors.GluingOpens T` cover `T`. -/
lemma iSup_gluingOpens : ⨆ V : GluingOpens T, (V.1 : T.left.Opens) = ⊤ :=
  le_antisymm le_top fun z _ => by
    obtain ⟨V, hV, hmem, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp
      (isBasis_gluingOpens T) (U := ⊤) (TopologicalSpace.Opens.mem_top z)
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨V, hV⟩, hmem⟩

/-- **The glued object represents the fibre product.** For every object `A'` of `Sch/S`, every
section of `F'` over `A'` and every morphism `A' ⟶ T` compatible with the given section of `G'`
there is exactly one morphism `A' ⟶ X` to the glued object inducing them: the morphism is
constructed over each member of the basis and glued, both constructions being unique. -/
lemma existsUnique_hom_gluedOver (haF' : IsZariskiSheaf F')
    (hxF : ∀ V : GluingOpens T, F'.map (L.chartOver V).op xF = L.sectionF V)
    (A' : Over S) (xb : F'.obj (op A')) (m : A' ⟶ T)
    (hb : a'.app (op A') xb = G'.map m.op ξ) :
    ∃! n : A' ⟶ L.gluedOver, F'.map n.op xF = xb ∧ n ≫ L.toOver = m := by
  classical
  have hcov : ⨆ V : GluingOpens T, m.left ⁻¹ᵁ (V.1 : T.left.Opens) = ⊤ := by
    rw [← Scheme.Hom.preimage_iSup, iSup_gluingOpens, Scheme.Hom.preimage_top]
  have hlocb : ∀ V : GluingOpens T,
      a'.app (op (overOpen A' (m.left ⁻¹ᵁ V.1)))
          (F'.map (overOpenι A' (m.left ⁻¹ᵁ V.1)).op xb)
        = G'.map (overOpenRestrict m V.1).op (G'.map (overOpenι T V.1).op ξ) := by
    intro V
    rw [← Functor.map_comp_apply, ← op_comp, overOpenRestrict_comp_overOpenι, op_comp,
      Functor.map_comp_apply, ← hb,
      ← NatTrans.naturality_apply a' (overOpenι A' (m.left ⁻¹ᵁ V.1)).op]
  choose n hn₁ hn₂ using fun V : GluingOpens T =>
    L.exists_hom_over_basis hxF V (overOpenRestrict m V.1)
      (F'.map (overOpenι A' (m.left ⁻¹ᵁ V.1)).op xb) (hlocb V)
  -- the local morphisms agree on the overlaps
  have hagree : ∀ V U : GluingOpens T,
      overOpenLE A' (inf_le_left : m.left ⁻¹ᵁ V.1 ⊓ m.left ⁻¹ᵁ U.1 ≤ m.left ⁻¹ᵁ V.1) ≫ n V
        = overOpenLE A' (inf_le_right : m.left ⁻¹ᵁ V.1 ⊓ m.left ⁻¹ᵁ U.1 ≤ m.left ⁻¹ᵁ U.1)
            ≫ n U := by
    intro V U
    refine L.eq_of_hom_over_basis hxF V
      (overOpenLE A' (inf_le_left : m.left ⁻¹ᵁ V.1 ⊓ m.left ⁻¹ᵁ U.1 ≤ m.left ⁻¹ᵁ V.1)
        ≫ overOpenRestrict m V.1)
      (F'.map (overOpenι A' (m.left ⁻¹ᵁ V.1 ⊓ m.left ⁻¹ᵁ U.1)).op xb) ?_ ?_ ?_ ?_
    · rw [op_comp, Functor.map_comp_apply, hn₁ V, ← Functor.map_comp_apply, ← op_comp,
        overOpenLE_comp_overOpenι]
    · rw [Category.assoc, hn₂ V, Category.assoc]
    · rw [op_comp, Functor.map_comp_apply, hn₁ U, ← Functor.map_comp_apply, ← op_comp,
        overOpenLE_comp_overOpenι]
    · rw [Category.assoc, hn₂ U, Category.assoc, overOpenRestrict_comp_overOpenι,
        overOpenRestrict_comp_overOpenι, ← Category.assoc, ← Category.assoc,
        overOpenLE_comp_overOpenι, overOpenLE_comp_overOpenι]
  obtain ⟨nn, hnn, -⟩ := isZariskiSheaf_uliftYoneda.{w} L.gluedOver A' (GluingOpens T)
    (fun V => m.left ⁻¹ᵁ (V.1 : T.left.Opens)) hcov (fun V => ULift.up (n V)) (by
      intro V U
      exact congrArg ULift.up (hagree V U))
  have hnnV : ∀ V : GluingOpens T, overOpenι A' (m.left ⁻¹ᵁ V.1) ≫ nn.down = n V :=
    fun V => congrArg ULift.down (hnn V)
  refine ⟨nn.down, ⟨?_, ?_⟩, ?_⟩
  · refine zariskiSheaf_ext haF' (fun V : GluingOpens T => m.left ⁻¹ᵁ (V.1 : T.left.Opens))
      hcov _ _ fun V => ?_
    rw [← Functor.map_comp_apply, ← op_comp, hnnV V, hn₁ V]
  · have hstep : ∀ V : GluingOpens T,
        ((uliftYoneda.{max w (u + 1)}).obj T).map (overOpenι A' (m.left ⁻¹ᵁ V.1)).op
            (ULift.up (nn.down ≫ L.toOver))
          = ((uliftYoneda.{max w (u + 1)}).obj T).map (overOpenι A' (m.left ⁻¹ᵁ V.1)).op
            (ULift.up m) := by
      intro V
      have h : overOpenι A' (m.left ⁻¹ᵁ V.1) ≫ nn.down ≫ L.toOver
          = overOpenι A' (m.left ⁻¹ᵁ V.1) ≫ m := by
        rw [← Category.assoc, hnnV V, hn₂ V, overOpenRestrict_comp_overOpenι]
      exact congrArg ULift.up h
    exact congrArg ULift.down (zariskiSheaf_ext (isZariskiSheaf_uliftYoneda.{w} T)
      (X := A') (fun V : GluingOpens T => m.left ⁻¹ᵁ (V.1 : T.left.Opens)) hcov
      (ULift.up (nn.down ≫ L.toOver)) (ULift.up m) hstep)
  · intro p hp
    have hstep : ∀ V : GluingOpens T,
        ((uliftYoneda.{max w (u + 1)}).obj L.gluedOver).map
            (overOpenι A' (m.left ⁻¹ᵁ V.1)).op (ULift.up p)
          = ((uliftYoneda.{max w (u + 1)}).obj L.gluedOver).map
            (overOpenι A' (m.left ⁻¹ᵁ V.1)).op (ULift.up nn.down) := by
      intro V
      have h : overOpenι A' (m.left ⁻¹ᵁ V.1) ≫ p
          = overOpenι A' (m.left ⁻¹ᵁ V.1) ≫ nn.down := by
        refine L.eq_of_hom_over_basis hxF V (overOpenRestrict m V.1)
          (F'.map (overOpenι A' (m.left ⁻¹ᵁ V.1)).op xb) ?_ ?_ ?_ ?_
        · rw [op_comp, Functor.map_comp_apply, hp.1]
        · rw [Category.assoc, hp.2, overOpenRestrict_comp_overOpenι]
        · rw [hnnV V]
          exact hn₁ V
        · rw [hnnV V]
          exact hn₂ V
      exact congrArg ULift.up h
    exact congrArg ULift.down (zariskiSheaf_ext
      (isZariskiSheaf_uliftYoneda.{w} L.gluedOver)
      (X := A') (fun V : GluingOpens T => m.left ⁻¹ᵁ (V.1 : T.left.Opens)) hcov
      (ULift.up p) (ULift.up nn.down) hstep)

end OverBasis

include L in
/-- **The implication (3) ⇒ (1) of Stacks 0GE5 once the local data is given.** The glued object
represents the fibre product of `F'` and `T` over `G'`. -/
theorem exists_isPullback_of_localRepData (haF' : IsZariskiSheaf F') (haG' : IsZariskiSheaf G') :
    ∃ (X : Over S) (f : X ⟶ T) (fst : (uliftYoneda.{max w (u + 1)}).obj X ⟶ F'),
      IsPullback fst ((uliftYoneda.{max w (u + 1)}).map f) a'
        ((uliftYonedaEquiv.{max w (u + 1)} (X := T) (F := G')).symm ξ) := by
  obtain ⟨xF, hxF⟩ := L.exists_sectionGlued haF'
  refine ⟨L.gluedOver, L.toOver,
    (uliftYonedaEquiv.{max w (u + 1)} (X := L.gluedOver) (F := F')).symm xF, ?_⟩
  have hcomm : a'.app (op L.gluedOver) xF = G'.map L.toOver.op ξ := by
    refine L.ext_of_map_chartOver haG' fun V => ?_
    rw [← NatTrans.naturality_apply a' (L.chartOver V).op, hxF V, L.app_sectionF V,
      ← Functor.map_comp_apply, ← op_comp, ← Functor.map_comp_apply, ← op_comp,
      L.chartOver_comp_toOver]
  have hw : (uliftYonedaEquiv.{max w (u + 1)} (X := L.gluedOver) (F := F')).symm xF ≫ a'
      = (uliftYoneda.{max w (u + 1)}).map L.toOver
        ≫ (uliftYonedaEquiv.{max w (u + 1)} (X := T) (F := G')).symm ξ := by
    rw [uliftYonedaEquiv_symm_comp, map_comp_uliftYonedaEquiv_symm]
    exact congrArg uliftYonedaEquiv.symm hcomm
  refine isPullback_of_forall_existsUnique hw ?_
  intro Z b c hbc
  obtain ⟨A'⟩ := Z
  obtain ⟨m⟩ := c
  obtain ⟨p, ⟨hp₁, hp₂⟩, hpu⟩ :=
    L.existsUnique_hom_gluedOver haF' hxF A' b m (by simpa using hbc)
  refine ⟨ULift.up p, ⟨by simpa using hp₁, congrArg ULift.up hp₂⟩, fun a ha => ?_⟩
  exact congrArg ULift.up (hpu a.down ⟨by simpa using ha.1, congrArg ULift.down ha.2⟩)

end LocalRepData

/-! ### Stacks 0GE5, the implication (3) ⇒ (1) -/

/-- **Criterion (3) of Stacks 0GE5 provides the local data of the gluing.** Over every member of
the basis of opens of `T` which are affine and lie over an affine open of `S`, the fibre product
of `F'` and that member over `G'` is representable by the affine case
`AlgebraicGeometry.ExtendingFunctors.exists_isPullback_of_isAffineOverAffineOpen`. -/
theorem nonempty_localRepData [IsLocallyNoetherian S]
    {F' G' : (Over S)ᵒᵖ ⥤ Type (max w (u + 1))} {a' : F' ⟶ G'}
    (haF' : IsZariskiSheaf F') (haG' : IsZariskiSheaf G')
    (hbF' : PreservesAffineLimits F') (hbG' : PreservesAffineLimits G')
    (h3 : IsRepresentableOnAffineFiniteType.{w}
      (Functor.whiskerLeft (IsLocallyNoetherianOver (S := S)).ι.op a'))
    (T : Over S) (ξ : G'.obj (op T)) : Nonempty (LocalRepData.{w} a' T ξ) := by
  classical
  choose X s fst hpb using fun V : GluingOpens T =>
    exists_isPullback_of_isAffineOverAffineOpen haF' haG' hbF' hbG' h3 (overOpen T V.1) V.2
      (G'.map (overOpenι T V.1).op ξ)
  refine ⟨{ obj := X
            proj := s
            sectionF := fun V => uliftYonedaEquiv (fst V)
            isPullback := fun V => ?_ }⟩
  rw [Equiv.symm_apply_apply]
  exact hpb V

/-- **Stacks 0GE5, implication (3) ⇒ (1).** Let `S` be a locally Noetherian scheme, let `τ` be one
of the five topologies — Zariski, étale, smooth, syntomic and fppf — and let `F'`, `G'` be limit
preserving sheaves on `(Sch/S)_τ`. If the restriction `a` of a transformation `a' : F' ⟶ G'` to the
locally Noetherian objects over `S` is representable at every test object which is affine of finite
type over `S` and maps into an affine open of `S`, then `a'` itself is representable, in the sense
of Categories Definition 001X.

For an arbitrary object `T` of `Sch/S` and a section of `G'` over it, the fibre product is
represented over every member of the basis of opens of `T` which are affine and lie over an affine
open of `S`; those representing objects glue by Stacks 01LH, the local sections of `F'` glue
because `F'` is a Zariski sheaf, and the glued object has the universal property of the fibre
product at every object of `Sch/S`, both the existence and the uniqueness being local on that
object. -/
@[stacks 0GE5 "implication (3) ⇒ (1)", sga "3 XI 3.4" "special case"]
theorem relativelyRepresentable_of_isRepresentableOnAffineFiniteType
    (τ : CoveringTopology) [IsLocallyNoetherian S]
    {F' G' : (Over S)ᵒᵖ ⥤ Type (max w (u + 1))} (a' : F' ⟶ G')
    (hF' : IsLimitPreservingSheaf τ F') (hG' : IsLimitPreservingSheaf τ G')
    (h3 : IsRepresentableOnAffineFiniteType.{w}
      (Functor.whiskerLeft (IsLocallyNoetherianOver (S := S)).ι.op a')) :
    (uliftYoneda.{max w (u + 1)}).relativelyRepresentable a' := by
  intro T g
  obtain ⟨ξ, rfl⟩ := (uliftYonedaEquiv.{max w (u + 1)} (X := T) (F := G')).symm.surjective g
  obtain ⟨L⟩ := nonempty_localRepData (isZariskiSheaf_of_isCoveringSheaf τ hF'.1)
    (isZariskiSheaf_of_isCoveringSheaf τ hG'.1) hF'.2 hG'.2 h3 T ξ
  exact L.exists_isPullback_of_localRepData (isZariskiSheaf_of_isCoveringSheaf τ hF'.1)
    (isZariskiSheaf_of_isCoveringSheaf τ hG'.1)

/-- **Stacks 0GE5.** Let `S` be a locally Noetherian scheme, let `τ` be one of the five
topologies — Zariski, étale, smooth, syntomic and fppf — and let `F'`, `G'` be limit preserving
sheaves on `(Sch/S)_τ`. For a transformation `a' : F' ⟶ G'` with restriction `a` to the full
subcategory of locally Noetherian objects over `S`, the following are equivalent:

1. `a'` is representable;
2. `a` is representable;
3. `a` is representable at every test object which is affine of finite type over `S` and maps into
   an affine open of `S`. -/
@[stacks 0GE5]
theorem relativelyRepresentable_tfae (τ : CoveringTopology) [IsLocallyNoetherian S]
    {F' G' : (Over S)ᵒᵖ ⥤ Type (max w (u + 1))} (a' : F' ⟶ G')
    (hF' : IsLimitPreservingSheaf τ F') (hG' : IsLimitPreservingSheaf τ G') :
    List.TFAE
      [(uliftYoneda.{max w (u + 1)}).relativelyRepresentable a',
       (uliftYoneda.{max w (u + 1)}).relativelyRepresentable
         (Functor.whiskerLeft (IsLocallyNoetherianOver (S := S)).ι.op a'),
       IsRepresentableOnAffineFiniteType.{w}
         (Functor.whiskerLeft (IsLocallyNoetherianOver (S := S)).ι.op a')] := by
  tfae_have 1 → 2 := fun h =>
    relativelyRepresentable_restriction_of_limitPreservingSheaf τ a' hF' hG' h
  tfae_have 2 → 3 := fun h => isRepresentableOnAffineFiniteType_of_relativelyRepresentable h
  tfae_have 3 → 1 := fun h =>
    relativelyRepresentable_of_isRepresentableOnAffineFiniteType τ a' hF' hG' h
  tfae_finish

end AlgebraicGeometry.ExtendingFunctors

end
