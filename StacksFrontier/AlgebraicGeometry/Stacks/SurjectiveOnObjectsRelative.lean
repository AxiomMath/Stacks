module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeProperty
public import StacksFrontier.AlgebraicGeometry.Stacks.SurjectiveOnObjects
public import StacksFrontier.CategoryTheory.FiberedCategory.PairIsoClassPresheaf

/-!
# Surjectivity on objects is the relative surjectivity of Stacks 03YK (Stacks 06D7)

A 1-morphism `p : 𝒳 ⟶ 𝒴` of categories fibred in groupoids over the big fppf site of `S` which is
representable by algebraic spaces carries two a priori different surjectivity conditions. Stacks
06D4 asks that every object of `𝒴` lying over the spectrum of a field acquire a lift to `𝒳` after
a field extension; Stacks 03YK, applied to surjectivity of morphisms of algebraic spaces, asks
that the algebraic space representing the base change of `p` along every scheme-valued point of
`𝒴` have surjective structure morphism. Stacks 06D7 says the two agree.

Both directions compare a *section* of the representing algebraic space over a field object with
an *object* of the 2-fibre product over that field object, and the comparison is the equivalence
over the base supplied by representability. In the forward direction a field-valued point of the
representing presheaf is produced from a lift of the chosen object; in the backward direction the
canonical slice section `p𝒴.chosenPullbacks.sliceFunctor` turns an object of `𝒴` over `U` into a
morphism `(Sch/U) ⥤ 𝒴` to which representability applies, and a field-valued point of the
representing presheaf is turned back into a lift.

## Main results

* `AlgebraicGeometry.Stack.isSurjectiveOnObjects_iff_isRelativelySurjective`: **Stacks 06D7**.

## Implementation notes

The relative condition is `AlgebraicGeometry.Stack.HasRelativeProperty` at
`AlgebraicGeometry.Space.surjectiveMorphismProperty`, whose two instance arguments — stability
under base change (Stacks 03MH) and locality at the target for the fppf precoverage (Stacks 041Q
through the comparison of Stacks 0DFQ) — are already instances in
`AlgebraicGeometry/Spaces/SurjectiveFpqcLocalAtTarget.lean`.

The passage between an algebraic space over `U` and an algebraic space over `S` with a morphism
to the representable space of `U` is `AlgebraicGeometry.spacesOverSmallerBaseFunctor` (Stacks
04SG), and the two facts used about it are that forgetting the structural morphism gives the
lower-shriek extension, `AlgebraicGeometry.spacesOverSmallerBaseFunctorForgetIso`, and that the
structural morphism reads off the factorization,
`AlgebraicGeometry.spacesOverSmallerBaseFunctor_hom_app_forgetIso_inv_app`.

## References

* [Stacks Project, Tag 06D7](https://stacks.math.columbia.edu/tag/06D7)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Stack

universe u v w

/-- The canonical section `(Sch/U) ⥤ 𝒴` of a category fibred in groupoids determined by an object
`y` of `𝒴` over `U`, built from the chosen pullbacks of `𝒴` along the iterated-slice
identification of the big fppf site of `U` with the slice of that of `S` over `U`. -/
private noncomputable def sliceSectionOfObject
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {𝒴 : CatFiberedInGroupoids.{u, v, u + 1, w} (BigFppfOver B S hS)}
    (U : BigFppfOver B S hS) (y : 𝒴.val.obj) (hy : 𝒴.val.p.obj y = U) :
    BigFppfOver B U.left.1 U.left.2 ⥤ 𝒴.val.obj :=
  letI : 𝒴.val.p.IsFibered := 𝒴.isFiberedInGroupoids.isFibered
  (Over.iteratedSliceEquiv U).inverse ⋙ 𝒴.val.p.chosenPullbacks.sliceFunctor ⟨y, hy⟩

/-- `AlgebraicGeometry.Stack.sliceSectionOfObject` is a section: composing it with the structure
functor of `𝒴` gives the structure functor of the big fppf site of `U` over that of `S`. -/
private theorem sliceSectionOfObject_comp
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {𝒴 : CatFiberedInGroupoids.{u, v, u + 1, w} (BigFppfOver B S hS)}
    (U : BigFppfOver B S hS) (y : 𝒴.val.obj) (hy : 𝒴.val.p.obj y = U) :
    sliceSectionOfObject B S hS U y hy ⋙ 𝒴.val.p = Over.map U.hom := by
  let : 𝒴.val.p.IsFibered := 𝒴.isFiberedInGroupoids.isFibered
  let c := 𝒴.val.p.chosenPullbacks
  let y₀ : 𝒴.val.p.Fiber U := ⟨y, hy⟩
  show (Over.iteratedSliceEquiv U).inverse ⋙ c.sliceFunctor y₀ ⋙ 𝒴.val.p = _
  calc
    _ = (Over.iteratedSliceEquiv U).inverse ⋙ Over.forget U := by
      rw [← Functor.assoc]
      exact congrArg ((Over.iteratedSliceEquiv U).inverse ⋙ ·)
        (Functor.ChoiceOfPullbacks.sliceFunctor_comp c y₀)
    _ = Over.map U.hom := Over.iteratedSliceBackward_forget U

/-- Surjectivity of the map on points of Stacks 03BU, read on field-valued representatives: the
induced map is surjective exactly when every field-valued point of the target is dominated by the
image of one of the source. -/
private theorem pointsMap_surjective_iff_fieldPoint_lift
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (α : F ⟶ G) :
    Function.Surjective (Space.pointsMap B S hS F α) ↔
      ∀ q : Space.FieldValuedPoint B S hS G,
        ∃ p : Space.FieldValuedPoint B S hS F,
          Space.FieldValuedPoint.HasCommonExtension B S hS G
            (Space.FieldValuedPoint.map B S hS F α p) q := by
  constructor
  · intro h q
    obtain ⟨p, hp⟩ := h (q.class B S hS G)
    obtain ⟨p, rfl⟩ := Quot.exists_rep p
    exact ⟨p, (Space.FieldValuedPoint.class_eq_class_iff B S hS G _ _).mp hp⟩
  · intro h q
    refine Quot.inductionOn q fun q => ?_
    obtain ⟨p, hp⟩ := h q
    exact ⟨p.class B S hS F,
      (Space.pointsMap_class B S hS F α p).trans
        (Space.FieldValuedPoint.class_eq_class_of_hasCommonExtension B S hS G hp)⟩

/-- Being a field object only depends on the underlying scheme of an object of a big fppf site. -/
private theorem isFieldObject_of_left_eq
    (B : BigFppfSite.{u}) {S S' : Scheme.{u}} {hS : B.Contains S} {hS' : B.Contains S'}
    {W : BigFppfOver B S hS} {V : BigFppfOver B S' hS'} (h : W.left = V.left)
    (hW : IsFieldObject B S hS W) : IsFieldObject B S' hS' V := by
  obtain ⟨k, hk, e⟩ := hW
  refine ⟨k, hk, ?_⟩
  change Nonempty (B.inclusion.obj W.left ≅ _) at e
  change Nonempty (B.inclusion.obj V.left ≅ _)
  rwa [← h]

/-- A field object of the big fppf site of `S` is the site object of a field-valued point of the
presheaf it represents, and the corresponding object of the big fppf site of that field object is
again a field object. -/
private theorem fieldPoint_of_isFieldObject
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (U : BigFppfOver B S hS) (hU : IsFieldObject B S hS U) :
    ∃ (q : Space.FieldValuedPoint B S hS (yoneda.obj (Over.mk U.hom)))
      (V : BigFppfOver B U.left.1 U.left.2),
      q.siteObject.left = V.left ∧
      IsFieldObject B S hS q.siteObject ∧
      IsFieldObject B U.left.1 U.left.2 V := by
  obtain ⟨k, hk, ⟨e⟩⟩ := hU
  let : Field k := hk
  have hK : B.Contains (Spec (.of k)) := by
    show (Spec (.of k)).size < B.cutoff
    rw [← Scheme.size_congr e]
    exact U.left.2
  let e' : B.obj hK ≅ U.left := B.inclusion.preimageIso e.symm
  let q : Space.FieldValuedPoint B S hS (yoneda.obj (Over.mk U.hom)) := {
    carrier := k
    field := hk
    contained := hK
    toBase := B.inclusion.map (e'.hom ≫ U.hom)
    value := Over.homMk e'.hom (by rfl) }
  exact ⟨q, Over.mk e'.hom, rfl, ⟨q.carrier, q.field, ⟨Iso.refl _⟩⟩,
    k, hk, ⟨Iso.refl _⟩⟩

/-- A section of an algebraic space over `U` on a field object of the big fppf site of `U` gives a
field-valued point of the associated algebraic space over `S`, whose image under the structural
morphism to the representable space of `U` is the restriction of the tautological point. -/
private theorem pointsMap_surjective_fiberSection
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (U : BigFppfOver B S hS)
    (F : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
    (hF : IsAlgebraicSpace B U.left.1 U.left.2 F)
    (V : BigFppfOver B U.left.1 U.left.2)
    (hV : IsFieldObject B U.left.1 U.left.2 V)
    (s : F.obj (Opposite.op V)) :
    ∃ p : Space.FieldValuedPoint B S hS
        ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨F, hF⟩).1.left,
      ∃ q : Space.FieldValuedPoint B S hS (yoneda.obj (Over.mk U.hom)),
        ∃ q₀ : Space.FieldValuedPoint B S hS
            (yoneda.obj (Over.mk (V.hom ≫ U.hom))),
          Space.pointsMap B S hS
            ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨F, hF⟩).1.left
            ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨F, hF⟩).1.hom
            (p.class B S hS _) = q.class B S hS _ ∧
          q = Space.FieldValuedPoint.map B S hS
            (yoneda.obj (Over.mk (V.hom ≫ U.hom)))
            (yoneda.map (Over.homMk V.hom (by rfl))) q₀ := by
  classical
  let X : AlgebraicSpaces B U.left.1 U.left.2 := ⟨F, hF⟩
  let Fy := (spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj X
  let i := (spacesOverSmallerBaseFunctorForgetIso B U.left.1 S U.left.2 hS U.hom).app X
  let W : BigFppfOver B S hS := Over.mk (V.hom ≫ U.hom)
  have hW : IsFieldObject B S hS W := isFieldObject_of_left_eq B (W := V) rfl hV
  obtain ⟨q₀, -, -, -, -⟩ := fieldPoint_of_isFieldObject B S hS W hW
  let V' : BigFppfOver B U.left.1 U.left.2 := Over.mk (q₀.value.left ≫ V.hom)
  let g : V' ⟶ V := Over.homMk q₀.value.left (by rfl)
  let W' : BigFppfOver B S hS := Over.mk (V'.hom ≫ U.hom)
  have hhom : W'.hom = q₀.siteObject.hom := by
    calc
      W'.hom = q₀.value.left ≫ (V.hom ≫ U.hom) := by simp [W', V']
      _ = q₀.siteObject.hom := Over.w q₀.value
  let t : ((OverShriek.relocalizePresheafFunctor U.hom).obj F).obj
      (Opposite.op q₀.siteObject) := ⟨⟨V'.hom, F.map g.op s⟩, hhom⟩
  let p : Space.FieldValuedPoint B S hS Fy.1.left := {
    carrier := q₀.carrier
    field := q₀.field
    contained := q₀.contained
    toBase := q₀.toBase
    value := i.inv.app (Opposite.op q₀.siteObject) t }
  let α : yoneda.obj W ⟶ yoneda.obj (Over.mk U.hom) :=
    yoneda.map (Over.homMk V.hom (by rfl))
  let q := Space.FieldValuedPoint.map B S hS (yoneda.obj W) α q₀
  refine ⟨p, q, q₀, ?_, rfl⟩
  have hvalue : Fy.1.hom.app (Opposite.op p.siteObject) p.value = q.value := by
    show Fy.1.hom.app (Opposite.op q₀.siteObject)
        (i.inv.app (Opposite.op q₀.siteObject) t) =
      α.app (Opposite.op q₀.siteObject) q₀.value
    have hcompat' :
      Fy.1.hom.app (Opposite.op q₀.siteObject)
          (i.inv.app (Opposite.op q₀.siteObject) t) =
        Over.homMk V'.hom hhom := by
      convert spacesOverSmallerBaseFunctor_hom_app_forgetIso_inv_app
        B U.left.1 S U.left.2 hS U.hom X (Opposite.op q₀.siteObject) t using 1
      exact Over.OverMorphism.ext (by rfl)
    calc
      _ = Over.homMk V'.hom hhom := hcompat'
      _ = q.value := by
        show Over.homMk V'.hom _ = q₀.value ≫ Over.homMk V.hom _
        apply Over.OverMorphism.ext
        rfl
  rw [Space.pointsMap_class]
  exact (Space.FieldValuedPoint.class_eq_class_iff B S hS (yoneda.obj (Over.mk U.hom))
    (Space.FieldValuedPoint.map B S hS Fy.1.left Fy.1.hom p) q).2
    ⟨q, ⟨𝟙 q.siteObject, (Category.id_comp _).trans hvalue⟩,
      Space.FieldValuedPoint.dominates_refl B S hS (yoneda.obj (Over.mk U.hom)) q⟩

/-- A section of the presheaf representing the 2-fibre product names an object of that 2-fibre
product lying over the same object of the site. -/
private theorem equivalenceOver_section_has_fiberProduct_object
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (U : BigFppfOver B S hS)
    {𝒳 𝒴 : CatFiberedInGroupoids.{u, v, u + 1, w} (BigFppfOver B S hS)}
    (p : 𝒳 ⟶ 𝒴)
    (y : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒴.val.obj)
    (F : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
    (e : StacksRepresentableCFG.EquivalenceOver
      (TwoFibreProductOver.fst (Over.map U.hom) 𝒳.val.p 𝒴.val.p y
        (CatFiberedInGroupoids.homFunctor p))
      (presheafOfCategories (F ⋙ typeToCat)).p)
    (V : BigFppfOver B U.left.1 U.left.2)
    (s : F.obj (Opposite.op V)) :
    ∃ z : TwoFibreProductOver (Over.map U.hom) 𝒳.val.p 𝒴.val.p y
        (CatFiberedInGroupoids.homFunctor p),
      (TwoFibreProductOver.fst (Over.map U.hom) 𝒳.val.p 𝒴.val.p y
        (CatFiberedInGroupoids.homFunctor p)).obj z = V ∧
      Nonempty (e.hom.functor.obj z ≅
        (PresheafOfCategories.objEquiv (F ⋙ typeToCat)).symm
          ⟨V, Discrete.mk s⟩) := by
  let z' := (PresheafOfCategories.objEquiv (F ⋙ typeToCat)).symm ⟨V, Discrete.mk s⟩
  exact ⟨e.inv.functor.obj z', congrArg (fun G => G.obj z') e.inv.w, ⟨e.counitIso.app z'⟩⟩

/-- An object of the 2-fibre product names a section of the presheaf representing it, over the
object of the site it lies above. -/
private theorem equivalenceOver_fiberProduct_object_has_section
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (U : BigFppfOver B S hS)
    {𝒳 𝒴 : CatFiberedInGroupoids.{u, v, u + 1, w} (BigFppfOver B S hS)}
    (p : 𝒳 ⟶ 𝒴)
    (y : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒴.val.obj)
    (F : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
    (e : StacksRepresentableCFG.EquivalenceOver
      (TwoFibreProductOver.fst (Over.map U.hom) 𝒳.val.p 𝒴.val.p y
        (CatFiberedInGroupoids.homFunctor p))
      (presheafOfCategories (F ⋙ typeToCat)).p)
    (z : TwoFibreProductOver (Over.map U.hom) 𝒳.val.p 𝒴.val.p y
      (CatFiberedInGroupoids.homFunctor p)) :
    ∃ (V : BigFppfOver B U.left.1 U.left.2) (s : F.obj (Opposite.op V)),
      HEq (e.hom.functor.obj z).fiber (Discrete.mk s) ∧
      (TwoFibreProductOver.fst (Over.map U.hom) 𝒳.val.p 𝒴.val.p y
        (CatFiberedInGroupoids.homFunctor p)).obj z = V := by
  let t := e.hom.functor.obj z
  refine ⟨t.base, t.fiber.as, HEq.rfl, ?_⟩
  have h := congrArg (fun G => G.obj z) e.hom.w
  change t.base = _ at h
  exact h.symm

/-- From a section of the representing algebraic space over a field object of the big fppf site of
`U`, produce a field object of the big fppf site of `S`, an object of `𝒳` above it and a morphism
of `𝒴` to the chosen object `y`. -/
private theorem sourceLift_of_relativeSection
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {𝒳 𝒴 : CatFiberedInGroupoids.{u, v, u + 1, w} (BigFppfOver B S hS)}
    (p : 𝒳 ⟶ 𝒴) (U : BigFppfOver B S hS)
    (y : 𝒴.val.obj) (hy : 𝒴.val.p.obj y = U)
    (F : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
    (e : StacksRepresentableCFG.EquivalenceOver
      (TwoFibreProductOver.fst (Over.map U.hom) 𝒳.val.p 𝒴.val.p
        (sliceSectionOfObject B S hS U y hy) (CatFiberedInGroupoids.homFunctor p))
      (presheafOfCategories (F ⋙ typeToCat)).p)
    (V : BigFppfOver B U.left.1 U.left.2)
    (hV : IsFieldObject B U.left.1 U.left.2 V)
    (s : F.obj (Opposite.op V)) :
    ∃ (W : BigFppfOver B S hS),
      IsFieldObject B S hS W ∧
      ∃ (f : W ⟶ U) (x : 𝒳.val.obj),
        𝒳.val.p.obj x = W ∧
        ∃ α : (CatFiberedInGroupoids.homFunctor p).obj x ⟶ y, 𝒴.val.p.IsHomLift f α := by
  classical
  obtain ⟨z, hzbase, hsection⟩ :=
    equivalenceOver_section_has_fiberProduct_object B S hS U p
      (sliceSectionOfObject B S hS U y hy) F e V s
  have hVbase : z.x = V := hzbase
  have hzfield : IsFieldObject B U.left.1 U.left.2 z.x := hVbase.symm ▸ hV
  let V' : Over U := (Over.iteratedSliceEquiv U).inverse.obj z.x
  let a : V' ⟶ Over.mk (𝟙 U) := Over.mkIdTerminal.from V'
  let W : BigFppfOver B S hS := (Over.forget U).obj V'
  let f : W ⟶ U := (Over.forget U).map a
  have hWbase : W = (Over.map U.hom).obj z.x := by
    show (Over.forget U).obj ((Over.iteratedSliceEquiv U).inverse.obj z.x) = _
    exact congrArg (fun G => G.obj z.x) (Over.iteratedSliceBackward_forget U)
  have hzW : z.base = W := z.hx.symm.trans hWbase.symm
  have hx : 𝒳.val.p.obj z.y = W := z.hy.trans hzW
  have hW : IsFieldObject B S hS W :=
    isFieldObject_of_left_eq B (congrArg (·.left) hWbase).symm hzfield
  let : 𝒴.val.p.IsFibered := 𝒴.isFiberedInGroupoids.isFibered
  let c := 𝒴.val.p.chosenPullbacks
  let y₀ : 𝒴.val.p.Fiber U := ⟨y, hy⟩
  let : 𝒴.val.p.IsHomLift (𝟙 z.base) z.iso.hom := z.vertical
  let : IsIso z.iso.hom := z.iso.isIso_hom
  have hInvBase : 𝒴.val.p.IsHomLift (𝟙 z.base) z.iso.inv :=
    (IsIso.eq_inv_of_hom_inv_id z.iso.hom_inv_id).symm ▸
      IsHomLift.lift_id_inv_isIso 𝒴.val.p z.base z.iso.hom
  have hInv : 𝒴.val.p.IsHomLift (𝟙 W) z.iso.inv := by
    have hdom : 𝒴.val.p.obj ((CatFiberedInGroupoids.homFunctor p).obj z.y) = W :=
      (IsHomLift.domain_eq 𝒴.val.p (𝟙 z.base) z.iso.inv).trans hzW
    have hcod : 𝒴.val.p.obj ((sliceSectionOfObject B S hS U y hy).obj z.x) = W :=
      (IsHomLift.codomain_eq 𝒴.val.p (𝟙 z.base) z.iso.inv).trans hzW
    apply IsHomLift.of_fac' 𝒴.val.p (𝟙 W) z.iso.inv hdom hcod
    simpa [hdom, hcod] using (IsHomLift.fac' 𝒴.val.p (𝟙 z.base) z.iso.inv)
  have hCart : 𝒴.val.p.IsHomLift f ((c.sliceFunctor y₀).map a) :=
    Functor.ChoiceOfPullbacks.sliceFunctor_map_isHomLift c y₀ a
  let β := c.map (𝟙 U) y₀
  have hβ : 𝒴.val.p.IsHomLift (𝟙 U) β := (c.isStronglyCartesian (𝟙 U) y₀).toIsHomLift
  let α : (CatFiberedInGroupoids.homFunctor p).obj z.y ⟶ y :=
    (z.iso.inv ≫ (c.sliceFunctor y₀).map a) ≫ β
  have hα : 𝒴.val.p.IsHomLift f α := by
    have hfirst : 𝒴.val.p.IsHomLift f (z.iso.inv ≫ (c.sliceFunctor y₀).map a) :=
      @IsHomLift.comp_lift_id_left' _ _ _ _ 𝒴.val.p _ _ _ W
        z.iso.inv hInv _ _ f ((c.sliceFunctor y₀).map a) hCart
    exact @IsHomLift.comp_lift_id_right' _ _ _ _ 𝒴.val.p _ _ _ _ _ f
      (z.iso.inv ≫ (c.sliceFunctor y₀).map a) hfirst U β hβ
  exact ⟨W, hW, f, z.y, hx, α, hα⟩

/-- A lift of an object of `𝒴` through `p` over a morphism of the big fppf site of `U` names an
object of the 2-fibre product of `p` with that section of `𝒴`. -/
private theorem fiberProductObject_of_lift
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (U : BigFppfOver B S hS)
    {𝒳 𝒴 : CatFiberedInGroupoids.{u, v, u + 1, w} (BigFppfOver B S hS)}
    (p : 𝒳 ⟶ 𝒴)
    (y : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒴.val.obj)
    (hy : y ⋙ 𝒴.val.p = Over.map U.hom)
    {V W : BigFppfOver B U.left.1 U.left.2}
    (f : V ⟶ W) (x : 𝒳.val.obj)
    (hx : 𝒳.val.p.obj x = (Over.map U.hom).obj V)
    (α : (CatFiberedInGroupoids.homFunctor p).obj x ⟶ y.obj W)
    (hα : 𝒴.val.p.IsHomLift ((Over.map U.hom).map f) α) :
    ∃ z : TwoFibreProductOver (Over.map U.hom) 𝒳.val.p 𝒴.val.p y
        (CatFiberedInGroupoids.homFunctor p),
      z.base = (Over.map U.hom).obj V ∧ z.x = V ∧ z.y = x := by
  let : 𝒴.val.p.IsFiberedInGroupoids := 𝒴.isFiberedInGroupoids
  let : 𝒴.val.p.IsFibered := 𝒴.isFiberedInGroupoids.isFibered
  let fS := (Over.map U.hom).map f
  let b := y.map f
  let yM : BasedFunctor (BasedCategory.ofFunctor (Over.map U.hom)) 𝒴.val := ⟨y, hy⟩
  let : (BasedCategory.ofFunctor (Over.map U.hom)).p.IsHomLift fS f := by
    show (Over.map U.hom).IsHomLift ((Over.map U.hom).map f) f
    infer_instance
  have hb : 𝒴.val.p.IsHomLift fS b := BasedFunctor.preserves_isHomLift yM fS f
  let : 𝒴.val.p.IsHomLift fS α := hα
  let : 𝒴.val.p.IsStronglyCartesian fS b :=
    𝒴.isFiberedInGroupoids.isStronglyCartesian_homLift fS b
  let : 𝒴.val.p.IsStronglyCartesian fS α :=
    𝒴.isFiberedInGroupoids.isStronglyCartesian_homLift fS α
  have hbase : fS = (Iso.refl ((Over.map U.hom).obj V)).hom ≫ fS := by simp
  let e : (CatFiberedInGroupoids.homFunctor p).obj x ≅ y.obj V :=
    Functor.IsStronglyCartesian.domainIsoOfBaseIso 𝒴.val.p hbase b α
  exact ⟨{
    base := (Over.map U.hom).obj V
    x := V
    y := x
    hx := rfl
    hy := hx
    iso := e.symm
    vertical :=
      Functor.IsStronglyCartesian.domainUniqueUpToIso_hom_isHomLift 𝒴.val.p hbase b α },
    rfl, rfl, rfl⟩

/-- **Stacks 06D7.** A 1-morphism of categories fibred in groupoids over the big fppf site of `S`
which is representable by algebraic spaces is surjective on objects in the sense of Stacks 06D4
exactly when it has the relative property of Stacks 03YK for surjectivity of morphisms of
algebraic spaces. -/
@[stacks 06D7]
theorem isSurjectiveOnObjects_iff_isRelativelySurjective
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {𝒳 𝒴 : CatFiberedInGroupoids.{u, v, u + 1, w} (BigFppfOver B S hS)}
    (p : 𝒳 ⟶ 𝒴) (hp : IsRepresentableByAlgebraicSpaces B S hS p.hom) :
    IsSurjectiveOnObjects B S hS 𝒳.val.p 𝒴.val.p (CatFiberedInGroupoids.homFunctor p) ↔
      HasRelativeProperty B S hS (Space.surjectiveMorphismProperty B S hS) p hp := by
  constructor
  · intro h U y hy F hF hEquiv
    classical
    let Fy := (spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨F, hF⟩
    show Function.Surjective (Space.pointsMap B S hS Fy.1.left Fy.1.hom)
    rw [pointsMap_surjective_iff_fieldPoint_lift]
    intro q
    let V : BigFppfOver B U.left.1 U.left.2 := Over.mk q.value.left
    have htarget : 𝒴.val.p.obj (y.obj V) = (Over.map U.hom).obj V :=
      congrArg (fun g : _ ⥤ _ => g.obj V) hy
    have hqV : IsFieldObject B S hS ((Over.map U.hom).obj V) :=
      ⟨q.carrier, q.field, ⟨Iso.refl _⟩⟩
    obtain ⟨W, hW, f, x, hx, β, hβ⟩ := h ((Over.map U.hom).obj V) hqV (y.obj V) htarget
    rcases hEquiv with ⟨e⟩
    let V' : BigFppfOver B U.left.1 U.left.2 := Over.mk (f.left ≫ V.hom)
    let f' : V' ⟶ V := Over.homMk f.left (by rfl)
    have hbaseV' : (Over.map U.hom).obj V' = W := by
      refine CostructuredArrow.obj_ext _ _ (by rfl) ?_
      show W.hom = (f.left ≫ V.hom) ≫ U.hom
      calc
        W.hom = f.left ≫ ((Over.map U.hom).obj V).hom := (Over.w f).symm
        _ = (f.left ≫ V.hom) ≫ U.hom := by simp [Category.assoc]
    have hmapf : (Over.map U.hom).map f' = eqToHom hbaseV' ≫ f := by
      apply Over.OverMorphism.ext
      simp [f']
    have hx' : 𝒳.val.p.obj x = (Over.map U.hom).obj V' := hbaseV'.symm ▸ hx
    have hβ' : 𝒴.val.p.IsHomLift ((Over.map U.hom).map f') β :=
      hmapf.symm ▸ (by
        let : 𝒴.val.p.IsHomLift f β := hβ
        infer_instance)
    obtain ⟨z, -, hzV, -⟩ := fiberProductObject_of_lift
      B S hS U p y hy (V := V') (W := V) f' x hx' β hβ'
    obtain ⟨Vsec, s, -, hzsec⟩ :=
      equivalenceOver_fiberProduct_object_has_section B S hS U p y F e z
    have hV' : IsFieldObject B U.left.1 U.left.2 V' := isFieldObject_of_left_eq B rfl hW
    have hVeq : V' = Vsec := hzV.symm.trans hzsec
    have hVsec : IsFieldObject B U.left.1 U.left.2 Vsec := hVeq ▸ hV'
    cases hVeq
    obtain ⟨p₀, q', q₀, hpoints, hq'⟩ :=
      pointsMap_surjective_fiberSection B S hS U F hF V' hVsec s
    have hq'q : Space.FieldValuedPoint.HasCommonExtension B S hS
        (yoneda.obj (Over.mk U.hom)) q' q := by
      rw [hq']
      refine ⟨Space.FieldValuedPoint.map B S hS
        (yoneda.obj (Over.mk (V'.hom ≫ U.hom)))
        (yoneda.map (Over.homMk V'.hom (by rfl))) q₀,
        Space.FieldValuedPoint.dominates_refl B S hS _ _, ?_⟩
      let g : (Space.FieldValuedPoint.map B S hS
        (yoneda.obj (Over.mk (V'.hom ≫ U.hom)))
          (yoneda.map (Over.homMk V'.hom (by rfl))) q₀).siteObject ⟶ q.siteObject :=
        Over.homMk (q₀.value.left ≫ f.left) (by
          have hqbase : q.value.left ≫ U.hom = q.siteObject.hom := Over.w q.value
          have hq₀base : q₀.value.left ≫ (V'.hom ≫ U.hom) = q₀.siteObject.hom :=
            Over.w q₀.value
          calc
            (q₀.value.left ≫ f.left) ≫ q.siteObject.hom =
                q₀.value.left ≫ (f.left ≫ (q.value.left ≫ U.hom)) := by
              rw [← hqbase]
              simp [Category.assoc]
            _ = q₀.value.left ≫ (V'.hom ≫ U.hom) := by simp [V, V', Category.assoc]
            _ = q₀.siteObject.hom := hq₀base)
      refine ⟨g, ?_⟩
      show (yoneda.obj (Over.mk U.hom)).map g.op q.value =
        (Space.FieldValuedPoint.map B S hS
          (yoneda.obj (Over.mk (V'.hom ≫ U.hom)))
          (yoneda.map (Over.homMk V'.hom (by rfl))) q₀).value
      apply Over.OverMorphism.ext
      rfl
    have hpq' : Space.FieldValuedPoint.HasCommonExtension B S hS
        (yoneda.obj (Over.mk U.hom))
        (Space.FieldValuedPoint.map B S hS Fy.1.left Fy.1.hom p₀) q' := by
      apply (Space.FieldValuedPoint.class_eq_class_iff B S hS
        (yoneda.obj (Over.mk U.hom))
        (Space.FieldValuedPoint.map B S hS Fy.1.left Fy.1.hom p₀) q').mp
      simpa [Space.pointsMap_class] using hpoints
    exact ⟨p₀, Space.FieldValuedPoint.hasCommonExtension_trans
      B S hS (yoneda.obj (Over.mk U.hom)) hpq' hq'q⟩
  · intro hr U hU y hy
    let ycan := sliceSectionOfObject B S hS U y hy
    have hycan : ycan ⋙ 𝒴.val.p = Over.map U.hom := sliceSectionOfObject_comp B S hS U y hy
    obtain ⟨F, hF, he⟩ := hp U ycan hycan
    let Fy := (spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨F, hF⟩
    have hsurj := hr U ycan hycan F hF he
    change Function.Surjective (Space.pointsMap B S hS Fy.1.left Fy.1.hom) at hsurj
    obtain ⟨q, _, _, _, _⟩ := fieldPoint_of_isFieldObject B S hS U hU
    obtain ⟨p₀, _⟩ := (pointsMap_surjective_iff_fieldPoint_lift B S hS Fy.1.hom).mp hsurj q
    let i := (spacesOverSmallerBaseFunctorForgetIso B U.left.1 S U.left.2 hS U.hom).app
      ⟨F, hF⟩
    let t := i.hom.app (Opposite.op p₀.siteObject) p₀.value
    let V : BigFppfOver B U.left.1 U.left.2 := Over.mk t.1.1
    let s : F.obj (Opposite.op V) := t.1.2
    have hV : IsFieldObject B U.left.1 U.left.2 V := ⟨p₀.carrier, p₀.field, ⟨Iso.refl _⟩⟩
    rcases he with ⟨e⟩
    exact sourceLift_of_relativeSection B S hS p U y hy F e V hV s

end AlgebraicGeometry.Stack

end
