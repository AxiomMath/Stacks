module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RestrictRanAdjunction

/-!
# The direct image of modules along a cocontinuous functor is a right adjoint

Let `w : X ⥤ Y` be a cocontinuous functor of sites, let `O_Y` be a sheaf of rings on `Y` and let
`O_X` be a sheaf of rings on `X` presented as the sheafification of the restricted presheaf of
rings by a locally bijective `α : w^{-1}O_Y ⟶ O_X`. This file produces the adjunction

  `restriction of modules along w, sheafified ⊣ {}_sw`

on sheaves of modules, where the right-hand side is
`Stacks.SheafOfModules.pushforwardCocontinuous` for the direct-image form of the structure map.

`Stacks.SheafOfModules.RestrictRan.sheafAdjunction` already does this for a functor that is
*continuous* as well as cocontinuous, where restriction of a sheaf of modules is again a sheaf of
modules and no sheafification is needed. Without continuity the restriction of a sheaf need not be
a sheaf, so the left adjoint is restriction of the underlying presheaf of modules followed by
sheafification; the right adjoint is unchanged, because the right Kan extension of a sheaf is a
sheaf for a merely cocontinuous functor (`CategoryTheory.ran_isSheaf_of_isCocontinuous`, which is
what `pushforwardCocontinuous` is built on).

## Main definitions

* `Stacks.SheafOfModules.RestrictRan.ranFsharp`: the direct-image form `O_Y ⟶ {}_sw O_X` of the
  structure map, namely the adjunct of `α` under the right-Kan-extension adjunction, and
  `…sheafRanFsharp`, the same read as a morphism of sheaves of rings.
* `Stacks.SheafOfModules.RestrictRan.cocontinuousSheafAdjunction`: **the adjunction.**

## Main results

* `Stacks.SheafOfModules.RestrictRan.homEquiv_app_comp_ranπ_apply_type` and
  `…_apply_ring`: the defining property of the adjunct, read on a section rather than as an
  equality of morphisms. That is the form in which it meets the identifications of transported
  scalar actions, which are equations between sections.
* `Stacks.SheafOfModules.RestrictRan.ranSMul_restrictScalars`: the two readings of the scalar
  action on the direct image agree — the one cut out by the unit structure map from the
  `w^{-1}O_Y`-action obtained by restricting scalars along `α`, and the one cut out directly by
  `ranFsharp`.
* `Stacks.SheafOfModules.RestrictRan.ranPushforwardRestrictScalarsIso`: consequently restricting
  scalars along `α` and taking the direct image of presheaves of modules over the unit structure
  map is the direct image over `ranFsharp`.

## Implementation notes

The adjunction is `CategoryTheory.Adjunction.restrictFullyFaithful` applied to the composite of
the presheaf-level adjunction `Stacks.SheafOfModules.RestrictRan.adjunction` with Mathlib's
`CategoryTheory.PresheafOfModules.sheafificationAdjunction` at `α`, along the forgetful functor
from sheaves of modules to presheaves of modules on the source and the identity on the target.
Mathlib's sheafification functor at a general `α` already performs the change of rings, so no
separate extension of scalars appears here; a call site that has extension of scalars followed by
sheafification at an identity structure map — which is the same left adjoint, differently
presented — meets this statement through uniqueness of left adjoints.

The comparison of the two right adjoints is the whole content. Both are the right Kan extension of
the underlying presheaf of abelian groups, so the comparison is the identity there, and what has
to be checked is that the two scalar actions agree. Each is determined by its behaviour on the
legs of the limit cone computing the extension (`Stacks.SheafOfModules.ranSMul_π`), and there one
is multiplication by the image of the section under the restriction map of `O_Y` followed by `α`,
the other by its image under `ranFsharp` followed by the leg for `O_X`; those agree by
`Stacks.SheafOfModules.RestrictRan.homEquiv_app_comp_ranπ`, which is exactly the defining property
of the adjunct.

With the scalar actions identified, the comparison is `CategoryTheory.PresheafOfModules.homMk` at
the identity natural transformation, and it is an isomorphism because
`CategoryTheory.PresheafOfModules.toPresheaf` reflects isomorphisms and sends it to an identity.
This route is taken rather than building the isomorphism objectwise in `ModuleCat`: there the
obligation `hom ≫ inv = 𝟙` is a `rfl` whose kernel check at these concrete types does not
terminate, the same budget problem recorded in the implementation notes of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/DirectImageRestrictScalars.lean`.

## References

* [Stacks Project, Tag 00XO](https://stacks.math.columbia.edu/tag/00XO)
* [Stacks Project, Tag 0797](https://stacks.math.columbia.edu/tag/0797)
* [Stacks Project, Tag 0D72](https://stacks.math.columbia.edu/tag/0D72)
* [Stacks Project, Tag 0FN3](https://stacks.math.columbia.edu/tag/0FN3)
-/

@[expose] public noncomputable section

open CategoryTheory Limits Opposite

universe v r v₁ u₁ v₂ u₂

namespace Stacks.SheafOfModules.RestrictRan

/-- **The defining property of the adjunct, elementwise at `Type`.** This is
`Stacks.SheafOfModules.RestrictRan.homEquiv_app_comp_ranπ` read on a section. -/
lemma homEquiv_app_comp_ranπ_apply_type {A' : Type u₁} [Category.{v₁} A']
    {B' : Type u₂} [Category.{v₂} B'] (L : A' ⥤ B')
    [∀ N : A' ⥤ Type r, L.HasPointwiseRightKanExtension N]
    {G : B' ⥤ Type r} {F : A' ⥤ Type r} (α : L ⋙ G ⟶ F) (b : B')
    (j : StructuredArrow b L) (x : G.obj b) :
    ranπ L F b j ((((L.ranAdjunction (Type r)).homEquiv G F) α).app b x) =
      α.app j.right (G.map j.hom x) := by
  simpa using ConcreteCategory.congr_hom (homEquiv_app_comp_ranπ L α b j) x

/-- **The defining property of the adjunct, elementwise at `RingCat`.** This is
`Stacks.SheafOfModules.RestrictRan.homEquiv_app_comp_ranπ` read on a section. -/
lemma homEquiv_app_comp_ranπ_apply_ring {A' : Type u₁} [Category.{v₁} A']
    {B' : Type u₂} [Category.{v₂} B'] (L : A' ⥤ B')
    [∀ N : A' ⥤ RingCat.{r}, L.HasPointwiseRightKanExtension N]
    {G : B' ⥤ RingCat.{r}} {F : A' ⥤ RingCat.{r}} (α : L ⋙ G ⟶ F) (b : B')
    (j : StructuredArrow b L) (x : G.obj b) :
    (ranπ L F b j).hom (((((L.ranAdjunction RingCat.{r}).homEquiv G F) α).app b).hom x) =
      (α.app j.right).hom ((G.map j.hom).hom x) := by
  simpa using ConcreteCategory.congr_hom (homEquiv_app_comp_ranπ L α b j) x

/-- **The defining property of the adjunct, elementwise at `AddCommGrpCat`.** This is
`Stacks.SheafOfModules.RestrictRan.homEquiv_app_comp_ranπ` read on a section. It is the reading
the direct image of *modules* needs: the module structure of
`Stacks.SheafOfModules.ranPushforward` sits on the right Kan extension at `AddCommGrpCat`, so the
adjunct of a morphism of presheaves of modules out of a restriction is, on underlying presheaves,
the adjunct taken there. -/
lemma homEquiv_app_comp_ranπ_apply_addCommGrp {A' : Type u₁} [Category.{v₁} A']
    {B' : Type u₂} [Category.{v₂} B'] (L : A' ⥤ B')
    [∀ N : A' ⥤ AddCommGrpCat.{r}, L.HasPointwiseRightKanExtension N]
    {G : B' ⥤ AddCommGrpCat.{r}} {F : A' ⥤ AddCommGrpCat.{r}} (α : L ⋙ G ⟶ F) (b : B')
    (j : StructuredArrow b L) (x : G.obj b) :
    (ranπ L F b j).hom
        (((((L.ranAdjunction AddCommGrpCat.{r}).homEquiv G F) α).app b).hom x) =
      (α.app j.right).hom ((G.map j.hom).hom x) := by
  simpa using ConcreteCategory.congr_hom (homEquiv_app_comp_ranπ L α b j) x

section Presheaf

variable {X : Type u₁} [Category.{v₁} X] {Y : Type u₂} [Category.{v₂} Y] (w : X ⥤ Y)
  {T : Yᵒᵖ ⥤ RingCat.{r}} {S : Xᵒᵖ ⥤ RingCat.{r}}
  [∀ F : Xᵒᵖ ⥤ RingCat.{r}, w.op.HasPointwiseRightKanExtension F]
  [∀ F : Xᵒᵖ ⥤ AddCommGrpCat.{v}, w.op.HasPointwiseRightKanExtension F]
  (α : w.op ⋙ T ⟶ S)

/-- **The direct-image form of the structure map.** Given `α : w^{-1}O_Y ⟶ O_X` on presheaves of
rings, this is its adjunct `O_Y ⟶ {}_sw O_X` under the right-Kan-extension adjunction. -/
abbrev ranFsharp : T ⟶ w.op.ran.obj S :=
  (w.op.ranAdjunction RingCat.{r}).homEquiv T S α

omit [∀ F : Xᵒᵖ ⥤ AddCommGrpCat.{v}, w.op.HasPointwiseRightKanExtension F] in
/-- For the direct-image form of a structure map, the ring map attached to `(U, ψ : V ⟶ w.op(U))`
is the restriction map of the presheaf of rings along `ψ` followed by `α`. -/
lemma scalarπ_ranFsharp (V : Yᵒᵖ) (j : StructuredArrow V w.op) :
    scalarπ w (ranFsharp w α) V j = T.map j.hom ≫ α.app j.right :=
  homEquiv_app_comp_ranπ w.op α V j

variable (M : PresheafOfModules.{v} S)

/-- **The two scalar actions on the direct image agree.** Restricting the scalars of `M` along
`α` and letting the unit structure map cut out the `O_Y`-action gives the same endomorphism of the
right Kan extension as letting `ranFsharp` cut it out of the `O_X`-action: the two agree on every
leg of the limit cone, where both are multiplication by the image of the section under the
restriction map of `O_Y` followed by `α`. -/
lemma ranSMul_restrictScalars (V : Yᵒᵖ) (r : T.obj V) :
    ranSMul w (unitRingHom w (T := T)) ((PresheafOfModules.restrictScalars α).obj M) V r =
      ranSMul w (ranFsharp w α) M V r := by
  refine ran_hom_ext w.op M.presheaf (fun j => ?_)
  have h : scalarπ w (unitRingHom w (T := T)) V j ≫ α.app j.right =
      scalarπ w (ranFsharp w α) V j :=
    (congrArg (fun g => g ≫ α.app j.right) (scalarπ_unitRingHom w V j)).trans
      (scalarπ_ranFsharp w α V j).symm
  have hs : smulPresheaf ((PresheafOfModules.restrictScalars α).obj M) j.right
        ((scalarπ w (unitRingHom w (T := T)) V j).hom r) =
      smulPresheaf M j.right ((scalarπ w (ranFsharp w α) V j).hom r) :=
    congrArg (fun s => smulPresheaf M j.right s)
      (congrArg (fun g : T.obj V ⟶ S.obj j.right => RingCat.Hom.hom g r) h)
  exact (ranSMul_π w (unitRingHom w (T := T))
      ((PresheafOfModules.restrictScalars α).obj M) V r j).trans
    ((congrArg (fun g => ranπ w.op M.presheaf V j ≫ g) hs).trans
      (ranSMul_π w (ranFsharp w α) M V r j).symm)

/-- The comparison of the two readings of the direct image of a presheaf of modules: the identity
on underlying presheaves of abelian groups, which is linear by `ranSMul_restrictScalars`. -/
def ranPushforwardRestrictScalarsHom :
    (ranPushforward.{v} w (unitRingHom w (T := T))).obj
        ((PresheafOfModules.restrictScalars α).obj M) ⟶
      (ranPushforward.{v} w (ranFsharp w α)).obj M :=
  PresheafOfModules.homMk (𝟙 (w.op.ran.obj M.presheaf))
    (fun V r m => ConcreteCategory.congr_hom (ranSMul_restrictScalars w α M V r) m)

/-- The comparison at one presheaf of modules is an isomorphism: the forgetful functor to
presheaves of abelian groups reflects isomorphisms and sends it to an identity. -/
def ranPushforwardRestrictScalarsObjIso :
    (ranPushforward.{v} w (unitRingHom w (T := T))).obj
        ((PresheafOfModules.restrictScalars α).obj M) ≅
      (ranPushforward.{v} w (ranFsharp w α)).obj M := by
  haveI : IsIso ((PresheafOfModules.toPresheaf T).map
      (ranPushforwardRestrictScalarsHom w α M)) :=
    inferInstanceAs (IsIso (𝟙 (w.op.ran.obj M.presheaf)))
  haveI := isIso_of_reflects_iso (ranPushforwardRestrictScalarsHom w α M)
    (PresheafOfModules.toPresheaf T)
  exact asIso (ranPushforwardRestrictScalarsHom w α M)

/-- **Restricting scalars along `α` and taking the direct image over the unit structure map is
the direct image over `ranFsharp`.** -/
def ranPushforwardRestrictScalarsIso :
    PresheafOfModules.restrictScalars α ⋙ ranPushforward.{v} w (unitRingHom w (T := T)) ≅
      ranPushforward.{v} w (ranFsharp w α) :=
  NatIso.ofComponents (fun M => ranPushforwardRestrictScalarsObjIso w α M)
    (fun _ => (PresheafOfModules.toPresheaf T).map_injective rfl)

end Presheaf

section Sheaf

variable {X : Type u₁} [Category.{v₁} X] {Y : Type u₂} [Category.{v₂} Y] (w : X ⥤ Y)
  (JX : GrothendieckTopology X) (JY : GrothendieckTopology Y) [w.IsCocontinuous JX JY]
  (OY : Sheaf JY RingCat.{r}) (OX : Sheaf JX RingCat.{r}) (α : w.op ⋙ OY.obj ⟶ OX.obj)
  [∀ F : Xᵒᵖ ⥤ RingCat.{r}, w.op.HasPointwiseRightKanExtension F]
  [∀ F : Xᵒᵖ ⥤ AddCommGrpCat.{v}, w.op.HasPointwiseRightKanExtension F]
  [CategoryTheory.Presheaf.IsLocallyInjective JX α]
  [CategoryTheory.Presheaf.IsLocallySurjective JX α]
  [JX.WEqualsLocallyBijective AddCommGrpCat.{v}] [HasWeakSheafify JX AddCommGrpCat.{v}]

/-- The direct-image form of the structure map, read as a morphism of sheaves of rings
`O_Y ⟶ {}_sw O_X`. -/
def sheafRanFsharp : OY ⟶ (w.sheafPushforwardCocontinuous RingCat.{r} JX JY).obj OX :=
  ⟨ranFsharp w α⟩

/-- **Restriction of sheaves of modules along a cocontinuous functor of sites, sheafified, is
left adjoint to the direct image.** The left adjoint takes a sheaf of `O_Y`-modules to the
sheafification of the restriction of its underlying presheaf of modules; the right adjoint is
`Stacks.SheafOfModules.pushforwardCocontinuous` over the direct-image form of the structure map.

No continuity of `w` is assumed. This is the shape in which the direct-sum formula of Stacks 0D72
is available in case (B) of the simplicial-site situation, where the transitions are cocontinuous
only. -/
def cocontinuousSheafAdjunction :
    _root_.SheafOfModules.forget.{v} OY ⋙ PresheafOfModules.pushforward₀.{v} w OY.obj ⋙
        PresheafOfModules.sheafification.{v} α ⊣
      pushforwardCocontinuous.{v} w (sheafRanFsharp w JX JY OY OX α) :=
  Adjunction.restrictFullyFaithful
    ((adjunction.{v} w OY.obj).comp (PresheafOfModules.sheafificationAdjunction.{v} α))
    (_root_.SheafOfModules.fullyFaithfulForget.{v} OY)
    (Functor.FullyFaithful.id _)
    (Functor.rightUnitor _).symm
    ((Functor.leftUnitor _).trans
      (Functor.isoWhiskerLeft (_root_.SheafOfModules.forget.{v} OX)
        (ranPushforwardRestrictScalarsIso.{v} w α)))

end Sheaf

end Stacks.SheafOfModules.RestrictRan

end
