module

public import StacksCore.CategoryTheory.Pullback
public import StacksFrontier.AlgebraicGeometry.Limits.SurjectiveFinitePresentationCriterion
public import StacksFrontier.AlgebraicGeometry.Topologies.ExtendingFunctorsRestrictionFullness
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Representability of a transformation detected on the Noetherian site

Let `S` be a locally Noetherian scheme, let `τ` be one of the five topologies of
`AlgebraicGeometry.CoveringTopology` and let `F'`, `G'` be limit preserving sheaves on
`(Sch/S)_τ`. For a transformation `a' : F' ⟶ G'`, write `a` for its restriction to the full
subcategory `(Noetherian/S)` of locally Noetherian objects. Stacks 0GE5 asserts that the
following are equivalent:

1. `a'` is representable, in the sense of Categories Definition 001X, namely
   `CategoryTheory.Functor.relativelyRepresentable` along the Yoneda embedding of `Sch/S`;
2. `a` is representable along the Yoneda embedding of `(Noetherian/S)`, i.e. for every object
   `V` of `(Noetherian/S)` and every map `V ⟶ G` the fibre product `F ×_G V` is representable
   by an object of `(Noetherian/S)`;
3. the same, but only for `V` affine of finite type over `S` mapping into an affine open of `S`.

## Main definitions

* `AlgebraicGeometry.ExtendingFunctors.IsAffineFiniteTypeOverAffineOpen`: the test objects of
  criterion (3).
* `AlgebraicGeometry.ExtendingFunctors.IsRepresentableOnAffineFiniteType`: criterion (3).
* `AlgebraicGeometry.ExtendingFunctors.uliftYonedaIotaIso`: restriction along the inclusion of a
  full subcategory carries the presheaf represented by an object of the subcategory to the
  presheaf represented by that object in the subcategory.

## Main results

* `AlgebraicGeometry.ExtendingFunctors.locallyOfFinitePresentation_of_isPullback_uliftYoneda`:
  if a fibre product of limit preserving presheaves over a representable is itself represented,
  the projection to that representable is locally of finite presentation. This is the content of
  Limits of Spaces Lemma 0GDY and Limits Proposition 01ZC in the vocabulary of `Sch/S` and
  `AlgebraicGeometry.ExtendingFunctors.PreservesAffineLimits`.
* `AlgebraicGeometry.ExtendingFunctors.relativelyRepresentable_restriction`: implication
  (1) ⇒ (2), using only limit preservation of `F'` and `G'`.
* `AlgebraicGeometry.ExtendingFunctors.relativelyRepresentable_restriction_of_limitPreservingSheaf`:
  **Stacks 0GE5, (1) ⇒ (2)**, in the shape of the source.
* `AlgebraicGeometry.ExtendingFunctors.isRepresentableOnAffineFiniteType_of_relativelyRepresentable`
  is **Stacks 0GE5, (2) ⇒ (3)**.

## Implementation notes

The ambient category is `Over S` and the Noetherian site is
`AlgebraicGeometry.ExtendingFunctors.IsLocallyNoetherianOver`, the encoding of Stacks 0GE3; the
hypothesis "limit preserving and sheaves" of the source is
`AlgebraicGeometry.ExtendingFunctors.IsLimitPreservingSheaf`, which carries the topology `τ` as a
parameter, so all five topologies are covered at once. The restriction of `a'` is the whiskering
`Functor.whiskerLeft P.ι.op a'`, which is literally the restriction rather than an identification
up to isomorphism.

Representability is `CategoryTheory.Functor.relativelyRepresentable` along `uliftYoneda` rather
than along `yoneda`: the presheaves of Stacks 0GE3 take values in `Type (max w (u + 1))` while the
hom universe of `Over S` is `u`, and `CategoryTheory.uliftYoneda` is the Yoneda embedding with its
values lifted into the larger universe. The index universe `w` of the values is a free variable,
so the statements below imply every instance of themselves.

Implication (1) ⇒ (2) is the source's: the representing object of `F' ×_{G'} V` has locally of
finite presentation projection to `V`, hence is locally Noetherian when `V` is. The finite
presentation step needs the limit criterion of Stacks 01ZC tested on *directed* inverse systems,
because that is the shape in which
`AlgebraicGeometry.ExtendingFunctors.PreservesAffineLimits` supplies limit preservation; that is
the criterion of Stacks 0CM0,
`AlgebraicGeometry.locallyOfFinitePresentation_of_directedAffineLimit_surjective`.

Only limit preservation of `F'` and `G'` is used, not the sheaf condition and not the topology;
`relativelyRepresentable_restriction` records that sharper statement and the tagged theorem is its
specialisation to the hypotheses of the source.

| Stacks tag | library name |
|---|---|
| Tag 001X | `CategoryTheory.Functor.relativelyRepresentable` |
| Tag 0GE3 | `AlgebraicGeometry.ExtendingFunctors.IsLocallyNoetherianOver` |
| Tag 0CM0 | `AlgebraicGeometry.locallyOfFinitePresentation_of_directedAffineLimit_surjective` |

## References

* [Stacks Project, Tag 0GE5](https://stacks.math.columbia.edu/tag/0GE5)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ExtendingFunctors

universe w u v

variable {S : Scheme.{u}}

/-! ### Elements of a pullback of sets -/

/-- A cartesian square of sets exhibits its upper left corner as the set of compatible pairs:
for every pair of elements of the two other corners with the same image in the fourth, there is
a unique element of the upper left corner restricting to both. -/
private theorem exists_unique_of_isPullback_types {A B C E : Type v}
    {p : A ⟶ B} {q : A ⟶ C} {f : B ⟶ E} {g : C ⟶ E} (h : IsPullback p q f g)
    (b : B) (c : C) (hbc : f b = g c) : ∃! a : A, p a = b ∧ q a = c := by
  have hcomm : homOfElement b ≫ f = homOfElement c ≫ g := by
    ext _
    exact hbc
  have hfst := h.lift_fst (homOfElement b) (homOfElement c) hcomm
  have hsnd := h.lift_snd (homOfElement b) (homOfElement c) hcomm
  refine ⟨h.lift (homOfElement b) (homOfElement c) hcomm PUnit.unit, ⟨?_, ?_⟩, ?_⟩
  · exact types_congr_hom hfst PUnit.unit
  · exact types_congr_hom hsnd PUnit.unit
  · rintro a ⟨ha1, ha2⟩
    have hEq : homOfElement a = h.lift (homOfElement b) (homOfElement c) hcomm := by
      refine h.hom_ext ?_ ?_
      · rw [hfst]
        ext _
        exact ha1
      · rw [hsnd]
        ext _
        exact ha2
    exact types_congr_hom hEq PUnit.unit

/-! ### Descending a section along a directed limit -/

/-- Let `a' : F' ⟶ G'` be a transformation of limit preserving presheaves on `Sch/S`, let
`ξ` be a section of `G'` over `V` and let `c` be the limit of a directed inverse system `D` of
affine schemes over `S` equipped with compatible maps `κ` to `V`. A section of `F'` over `c.pt`
lifting the pullback of `ξ` descends to a section of `F'` over some stage of the system lifting
the pullback of `ξ` there.

Surjectivity of the comparison map for `F'` puts the section at some stage; the two sections of
`G'` which must agree there do agree after the limit, so injectivity of the comparison map for
`G'` — in the form of the description of equality in a filtered colimit of sets — makes them
agree at a later stage. -/
private theorem exists_stage_lift
    {F' G' : (Over S)ᵒᵖ ⥤ Type (max w (u + 1))} (a' : F' ⟶ G')
    (hF' : PreservesAffineLimits F') (hG' : PreservesAffineLimits G')
    {V : Over S} (ξ : G'.obj (op V))
    {Λ : Type u} [PartialOrder Λ] [Nonempty Λ] [IsDirectedOrder Λ]
    {D : Λᵒᵖ ⥤ Over S} (haff : ∀ l, IsAffine (D.obj l).left)
    {c : Cone D} (hc : IsLimit c)
    (κ : D ⟶ (Functor.const Λᵒᵖ).obj V) {κ₀ : c.pt ⟶ V}
    (hκ : ∀ l, c.π.app l ≫ κ.app l = κ₀)
    (x : F'.obj (op c.pt)) (hx : a'.app (op c.pt) x = G'.map κ₀.op ξ) :
    ∃ (l : Λᵒᵖ) (y : F'.obj (op (D.obj l))),
      a'.app (op (D.obj l)) y = G'.map (κ.app l).op ξ ∧
        F'.map (c.π.app l).op y = x := by
  obtain ⟨hcolF⟩ := hF' Λ D haff c hc
  obtain ⟨hcolG⟩ := hG' Λ D haff c hc
  obtain ⟨j, y, hy⟩ := Types.jointly_surjective_of_isColimit hcolF x
  have hy' : F'.map (c.π.app j.unop).op y = x := hy
  have hL : G'.map (c.π.app j.unop).op (a'.app (op (D.obj j.unop)) y)
      = G'.map κ₀.op ξ := by
    rw [← NatTrans.naturality_apply a' (c.π.app j.unop).op y, hy']
    exact hx
  have hR : G'.map (c.π.app j.unop).op (G'.map (κ.app j.unop).op ξ)
      = G'.map κ₀.op ξ := by
    rw [← Functor.map_comp_apply, ← op_comp, hκ j.unop]
  have himg : (G'.mapCocone c.op).ι.app j (a'.app (op (D.obj j.unop)) y) =
      (G'.mapCocone c.op).ι.app j (G'.map (κ.app j.unop).op ξ) := hL.trans hR.symm
  obtain ⟨k, f, g, hfg⟩ :=
    (Types.FilteredColimit.isColimit_eq_iff (D.op ⋙ G') hcolG).1 himg
  have hfg' : f = g := Subsingleton.elim f g
  subst hfg'
  have hnat : D.map f.unop ≫ κ.app j.unop = κ.app k.unop := by
    simp
  refine ⟨k.unop, F'.map (D.map f.unop).op y, ?_, ?_⟩
  · rw [NatTrans.naturality_apply a' (D.map f.unop).op y]
    have hstep : G'.map (D.map f.unop).op (a'.app (op (D.obj j.unop)) y) =
        G'.map (D.map f.unop).op (G'.map (κ.app j.unop).op ξ) := hfg
    rw [hstep, ← Functor.map_comp_apply, ← op_comp, hnat]
  · rw [← Functor.map_comp_apply, ← op_comp, c.w f.unop]
    exact hy'

/-! ### The representing object of a fibre product -/

/-- **A representable fibre product of limit preserving presheaves is of finite presentation over
its base.** If the fibre product of a transformation `a'` of limit preserving presheaves on
`Sch/S` with the presheaf represented by `V` is represented by `U'`, then the projection
`U' ⟶ V` is locally of finite presentation.

This is the step of the proof of Stacks 0GE5 which appeals to Limits of Spaces Lemma 0GDY
and Limits Proposition 01ZC. A morphism to `U'` out of the limit of a directed inverse system of
affine schemes over `V` is a section of `F'` lifting the section of `G'` classified by the given
map `V ⟶ G'`, so `AlgebraicGeometry.ExtendingFunctors.exists_stage_lift` descends it to a stage,
and the uniqueness in the cartesian square over the limit shows the descended morphism is a
factorisation of the original one. -/
@[sga "3 XI 3.2" "partial"]
theorem locallyOfFinitePresentation_of_isPullback_uliftYoneda
    {F' G' : (Over S)ᵒᵖ ⥤ Type (max w (u + 1))} {a' : F' ⟶ G'}
    (hF' : PreservesAffineLimits F') (hG' : PreservesAffineLimits G')
    {V U' : Over S} {snd' : U' ⟶ V}
    {fst' : (uliftYoneda.{max w (u + 1)}).obj U' ⟶ F'}
    {g' : (uliftYoneda.{max w (u + 1)}).obj V ⟶ G'}
    (hpb : IsPullback fst' ((uliftYoneda.{max w (u + 1)}).map snd') a' g') :
    LocallyOfFinitePresentation snd'.left := by
  obtain ⟨ξ, rfl⟩ :=
    (uliftYonedaEquiv.{max w (u + 1), u, u + 1}
      (C := Over S) (X := V) (F := G')).symm.surjective g'
  have hg'app : ∀ (Z : Over S) (m : Z ⟶ V),
      (uliftYonedaEquiv.{max w (u + 1), u, u + 1}.symm ξ).app (op Z) (ULift.up m)
        = G'.map m.op ξ := by
    intro Z m
    simp
  refine locallyOfFinitePresentation_of_directedAffineLimit_surjective snd'.left ?_
  intro Λ _ _ _ D₀ c₀ hc₀ haff g
  have hconn : IsConnected Λᵒᵖ := IsCofiltered.isConnected _
  have hpres : PreservesLimitsOfShape Λᵒᵖ (Over.map V.hom) := by
    have : PreservesLimitsOfShape Λᵒᵖ (Over.map V.hom ⋙ Over.forget S) :=
      preservesLimitsOfShape_of_natIso (Over.mapForget V.hom).symm
    exact preservesLimitsOfShape_of_reflects_of_preserves
      (Over.map V.hom) (Over.forget S)
  let D : Λᵒᵖ ⥤ Over S := D₀ ⋙ Over.map V.hom
  let c : Cone D := (Over.map V.hom).mapCone c₀
  have hclim : IsLimit c := isLimitOfPreserves (Over.map V.hom) hc₀
  have haffD : ∀ l, IsAffine (D.obj l).left := haff
  let κ : D ⟶ (Functor.const Λᵒᵖ).obj V :=
    { app := fun l => Over.homMk (D₀.obj l).hom
      naturality := by
        intro l m φ
        apply Over.OverMorphism.ext
        change (D₀.map φ).left ≫ (D₀.obj m).hom = (D₀.obj l).hom ≫ 𝟙 V.left
        rw [Category.comp_id]
        exact (D₀.map φ).w }
  have hκ₀w : c₀.pt.hom ≫ V.hom = c.pt.hom := rfl
  let κ₀ : c.pt ⟶ V := Over.homMk c₀.pt.hom hκ₀w
  have hκ : ∀ l, c.π.app l ≫ κ.app l = κ₀ := by
    intro l
    apply Over.OverMorphism.ext
    change (c₀.π.app l).left ≫ (D₀.obj l).hom = c₀.pt.hom
    exact (c₀.π.app l).w
  have hUhom : snd'.left ≫ V.hom = U'.hom := snd'.w
  have hgw : g.left ≫ snd'.left = c₀.pt.hom := g.w
  have hhw : g.left ≫ U'.hom = c.pt.hom := by
    rw [← hUhom, ← Category.assoc, hgw]
    exact hκ₀w
  let h : c.pt ⟶ U' := Over.homMk g.left hhw
  have hhsnd : h ≫ snd' = κ₀ := by
    apply Over.OverMorphism.ext
    exact hgw
  have hw : a'.app (op c.pt) (fst'.app (op c.pt) (ULift.up h)) =
      (uliftYonedaEquiv.{max w (u + 1), u, u + 1}.symm ξ).app (op c.pt)
        (((uliftYoneda.{max w (u + 1)}).map snd').app (op c.pt) (ULift.up h)) :=
    types_congr_hom (NatTrans.congr_app hpb.w (op c.pt)) (ULift.up h)
  have hmapsnd : ((uliftYoneda.{max w (u + 1)}).map snd').app (op c.pt) (ULift.up h) =
      ULift.up κ₀ := by
    simp [hhsnd]
  have hx : a'.app (op c.pt) (fst'.app (op c.pt) (ULift.up h)) =
      G'.map κ₀.op ξ := by
    rw [hw, hmapsnd, hg'app c.pt κ₀]
  obtain ⟨l, y, hy1, hy2⟩ :=
    exists_stage_lift a' hF' hG' ξ haffD hclim κ hκ _ hx
  have hpt := hpb.map ((evaluation (Over S)ᵒᵖ (Type (max w (u + 1)))).obj (op (D.obj l)))
  have hcompat : a'.app (op (D.obj l)) y =
      (uliftYonedaEquiv.{max w (u + 1), u, u + 1}.symm ξ).app (op (D.obj l))
        (ULift.up (κ.app l)) := by
    rw [hy1, hg'app (D.obj l) (κ.app l)]
  obtain ⟨ut, ⟨hut1, hut2⟩, -⟩ :=
    exists_unique_of_isPullback_types hpt y (ULift.up (κ.app l)) hcompat
  have hut1' : fst'.app (op (D.obj l)) ut = y := hut1
  have hut2' : ut.down ≫ snd' = κ.app l := congrArg ULift.down hut2
  have hleftw : ut.down.left ≫ snd'.left = (D₀.obj l).hom :=
    congrArg Over.Hom.left hut2'
  refine ⟨l, Over.homMk ut.down.left hleftw, ?_⟩
  have hpt0 := hpb.map ((evaluation (Over S)ᵒᵖ (Type (max w (u + 1)))).obj (op c.pt))
  obtain ⟨z, -, huniq⟩ :=
    exists_unique_of_isPullback_types hpt0 _ (ULift.up κ₀) hx
  have hstep : (ULift.up (c.π.app l ≫ ut.down) :
      ((uliftYoneda.{max w (u + 1)}).obj U').obj (op c.pt)) =
      ((uliftYoneda.{max w (u + 1)}).obj U').map (c.π.app l).op ut := by
    simp
  have hnatfst := NatTrans.naturality_apply fst' (c.π.app l).op ut
  have hA1 : fst'.app (op c.pt) (ULift.up (c.π.app l ≫ ut.down)) =
      fst'.app (op c.pt) (ULift.up h) := by
    rw [hstep]
    refine Eq.trans hnatfst ?_
    rw [hut1']
    exact hy2
  have hA2 : ((uliftYoneda.{max w (u + 1)}).map snd').app (op c.pt)
      (ULift.up (c.π.app l ≫ ut.down)) = ULift.up κ₀ := by
    simp [hut2', hκ l]
  have hB2 := hmapsnd
  have hA : (ULift.up (c.π.app l ≫ ut.down) :
      ((uliftYoneda.{max w (u + 1)}).obj U').obj (op c.pt)) = ULift.up h := by
    rw [huniq _ ⟨hA1, hA2⟩, huniq _ ⟨rfl, hB2⟩]
  have hdown : c.π.app l ≫ ut.down = h := congrArg ULift.down hA
  have hleft : (c.π.app l ≫ ut.down).left = h.left := congrArg Over.Hom.left hdown
  apply Over.OverMorphism.ext
  exact hleft

/-! ### Restriction to a full subcategory and the Yoneda embedding -/

section FullSubcategoryYoneda

universe w₁ v₁ u₁

/-- Restriction along the inclusion of a full subcategory identifies the presheaf on the
subcategory represented by one of its objects with the restriction of the presheaf on the
ambient category represented by the same object. -/
@[sga "3 I 1.1.1" "Hom_C(T"]
def uliftYonedaIotaIso {C : Type u₁} [Category.{v₁} C] (P : ObjectProperty C)
    (W : P.FullSubcategory) :
    P.ι.op ⋙ (uliftYoneda.{w₁}).obj W.obj ≅ (uliftYoneda.{w₁}).obj W :=
  NatIso.ofComponents
    (fun _ => Equiv.toIso
      { toFun := fun e => ULift.up (ObjectProperty.homMk e.down)
        invFun := fun e => ULift.up e.down.hom
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl })
    (by
      intro Z Z' f
      ext x
      rfl)

end FullSubcategoryYoneda

/-! ### The criteria of Stacks 0GE5 -/

/-- The test objects of criterion (3) of Stacks 0GE5: the objects of `Sch/S` which are affine, of
finite type over `S`, and map into an affine open of `S`. Being affine, such an object is of
finite type over `S` exactly when its structure morphism is locally of finite type. -/
def IsAffineFiniteTypeOverAffineOpen : ObjectProperty (Over S) :=
  fun X => IsAffineOverAffineOpen X ∧ LocallyOfFiniteType X.hom

/-- Criterion (3) of Stacks 0GE5: `CategoryTheory.Functor.relativelyRepresentable` along the
Yoneda embedding of the full subcategory, written out with the test object restricted to be
affine of finite type over `S` and to map into an affine open of `S`. -/
def IsRepresentableOnAffineFiniteType {P : ObjectProperty (Over S)}
    {F G : P.FullSubcategoryᵒᵖ ⥤ Type (max w (u + 1))} (a : F ⟶ G) : Prop :=
  ∀ V : P.FullSubcategory, IsAffineFiniteTypeOverAffineOpen V.obj →
    ∀ g : (uliftYoneda.{max w (u + 1)}).obj V ⟶ G,
      ∃ (W : P.FullSubcategory) (snd : W ⟶ V)
        (fst : (uliftYoneda.{max w (u + 1)}).obj W ⟶ F),
        IsPullback fst ((uliftYoneda.{max w (u + 1)}).map snd) a g

/-! ### Stacks 0GE5 -/

/-- **Implication (1) ⇒ (2) of Stacks 0GE5, needing only limit preservation.** If a
transformation `a'` of limit preserving presheaves on `Sch/S` is representable, then so is its
restriction to the locally Noetherian objects.

Given a locally Noetherian object `V` and a section of the restriction of `G'` over it, the given
representability produces an object `U'` of `Sch/S` representing the fibre product. Its
projection to `V` is locally of finite presentation by
`AlgebraicGeometry.ExtendingFunctors.locallyOfFinitePresentation_of_isPullback_uliftYoneda`,
hence locally of finite type, so `U'` is locally Noetherian and is an object of the subcategory.
Restriction preserves the cartesian square, because limits of presheaves are computed
pointwise. -/
theorem relativelyRepresentable_restriction
    [IsLocallyNoetherian S]
    {F' G' : (Over S)ᵒᵖ ⥤ Type (max w (u + 1))} {a' : F' ⟶ G'}
    (hF' : PreservesAffineLimits F') (hG' : PreservesAffineLimits G')
    (h1 : (uliftYoneda.{max w (u + 1)}).relativelyRepresentable a') :
    (uliftYoneda.{max w (u + 1)}).relativelyRepresentable
      (Functor.whiskerLeft (IsLocallyNoetherianOver (S := S)).ι.op a') := by
  intro V g
  obtain ⟨ξ, rfl⟩ := (uliftYonedaEquiv.{max w (u + 1), u, u + 1}
      (C := (IsLocallyNoetherianOver (S := S)).FullSubcategory) (X := V)
      (F := (IsLocallyNoetherianOver (S := S)).ι.op ⋙ G')).symm.surjective g
  have hVN : IsLocallyNoetherian V.obj.left := V.property
  obtain ⟨U', snd', fst', hpb⟩ :=
    h1 (uliftYonedaEquiv.{max w (u + 1), u, u + 1}.symm
      (show G'.obj (op V.obj) from ξ))
  have hlfp : LocallyOfFinitePresentation snd'.left :=
    locallyOfFinitePresentation_of_isPullback_uliftYoneda hF' hG' hpb
  have hlft : LocallyOfFiniteType snd'.left := inferInstance
  have hNoeth : IsLocallyNoetherian U'.left :=
    LocallyOfFiniteType.isLocallyNoetherian snd'.left
  refine ⟨⟨U', hNoeth⟩, ObjectProperty.homMk snd',
    (uliftYonedaIotaIso.{max w (u + 1), u, u + 1} (IsLocallyNoetherianOver (S := S))
      ⟨U', hNoeth⟩).inv ≫
      Functor.whiskerLeft (IsLocallyNoetherianOver (S := S)).ι.op fst', ?_⟩
  have hmap := hpb.map ((Functor.whiskeringLeft _ _ _).obj
    (IsLocallyNoetherianOver (S := S)).ι.op)
  refine hmap.of_iso (uliftYonedaIotaIso.{max w (u + 1), u, u + 1}
      (IsLocallyNoetherianOver (S := S)) ⟨U', hNoeth⟩) (Iso.refl _)
    (uliftYonedaIotaIso.{max w (u + 1), u, u + 1} (IsLocallyNoetherianOver (S := S)) V)
    (Iso.refl _) ?_ ?_ ?_ ?_
  · simp
  · ext Z x
    rfl
  · simp
  · ext Z x
    rfl

/-- **Stacks 0GE5, implication (1) ⇒ (2).** Let `S` be a locally Noetherian scheme, let `τ` be
one of the five topologies — Zariski, étale, smooth, syntomic and fppf — and let `F'`, `G'` be
limit preserving sheaves on `(Sch/S)_τ`. If a transformation `a' : F' ⟶ G'` is representable, in
the sense of Categories Definition 001X, then so is its restriction `a` to the full subcategory of
locally Noetherian objects: for every locally Noetherian object `V` over `S` and every map
`V ⟶ G` the fibre product `F ×_G V` is represented by a locally Noetherian object over `S`.

Only limit preservation of `F'` and `G'` enters the proof; the sheaf condition and the topology
are carried because the source states them, and the sharper statement is
`AlgebraicGeometry.ExtendingFunctors.relativelyRepresentable_restriction`. -/
@[stacks 0GE5 "implication (1) ⇒ (2)"]
theorem relativelyRepresentable_restriction_of_limitPreservingSheaf
    (τ : CoveringTopology) [IsLocallyNoetherian S]
    {F' G' : (Over S)ᵒᵖ ⥤ Type (max w (u + 1))} (a' : F' ⟶ G')
    (hF' : IsLimitPreservingSheaf τ F') (hG' : IsLimitPreservingSheaf τ G')
    (h1 : (uliftYoneda.{max w (u + 1)}).relativelyRepresentable a') :
    (uliftYoneda.{max w (u + 1)}).relativelyRepresentable
      (Functor.whiskerLeft (IsLocallyNoetherianOver (S := S)).ι.op a') :=
  relativelyRepresentable_restriction hF'.2 hG'.2 h1

/-- **Stacks 0GE5, implication (2) ⇒ (3).** If the restriction of `a'` to the locally Noetherian
objects over `S` is representable, then it is representable at every test object which is affine
of finite type over `S` and maps into an affine open of `S`: criterion (3) is criterion (2) with
its test object restricted. -/
@[stacks 0GE5 "implication (2) ⇒ (3)"]
theorem isRepresentableOnAffineFiniteType_of_relativelyRepresentable
    {P : ObjectProperty (Over S)}
    {F G : P.FullSubcategoryᵒᵖ ⥤ Type (max w (u + 1))} {a : F ⟶ G}
    (h : (uliftYoneda.{max w (u + 1)}).relativelyRepresentable a) :
    IsRepresentableOnAffineFiniteType.{w} a :=
  fun _ _ g => h g

end AlgebraicGeometry.ExtendingFunctors

end
