module

public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
public import Mathlib.CategoryTheory.Sites.Pullback
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.FiberedCategory.ChoiceOfPullbacks
public import StacksFrontier.CategoryTheory.Sites.Cohomology.FibredCategory.RingedToposOfAFibredCategory

/-!
# The lower shriek of an abelian sheaf on a fibred category as a fibrewise colimit

Let `p : C ⥤ D` be a fibred category over the underlying site of a ringed site `(D, O_D)`, give
`C` the topology it inherits from `D`, and let `π : Sh(C) ⟶ Sh(D)` be the induced morphism of
topoi. For an abelian sheaf `F` on `C` the sheaf `π_!F` is the sheaf associated to the presheaf

```
V ↦ colim_{(C_V)ᵒᵖ} F|_{C_V},
```

the colimit being taken over the opposite of the fibre of `p` at `V`. The restriction map along
`h : V' ⟶ V` is induced by restricting `F` along a cartesian lift of `h`.

The reason is that the fibre is final in the comma category computing the pointwise left Kan
extension of `F` along `p.op`: a cartesian lift of the structure arrow of a costructured arrow
`p.obj X ⟶ V` produces a morphism into the fibre, and any two such are connected because a
cartesian arrow factors every competitor uniquely.

## Main definitions

* `Stacks.Sites.FibredCategory.fiberOpToCostructuredArrow`: the inclusion of the opposite fibre
  at `V` into the costructured-arrow category of `p.op` at `op V`.
* `Stacks.Sites.FibredCategory.fiberColimitIso`: the identification of the value at `V` of the
  left Kan extension of `F` along `p.op` with the colimit over the opposite fibre.
* `Stacks.Sites.FibredCategory.FiberwiseColimitFormula`: the fibrewise presheaf, its colimit
  comparisons, the description of its restriction maps by cartesian lifts, and the comparison of
  its sheafification with the lower shriek.

## Main results

* `Stacks.Sites.FibredCategory.final_fiberOpToCostructuredArrow`: the opposite fibre of a fibred
  category is final in the costructured-arrow category.
* `Stacks.Sites.FibredCategory.fiberwiseColimitFormula`: the fibrewise-colimit presentation of
  the lower shriek exists.

## Implementation notes

The lower shriek is Mathlib's `CategoryTheory.Functor.sheafPullbackConstruction.sheafPullback`,
which is by construction the left Kan extension along `p.op` followed by sheafification, so the
last field of `FiberwiseColimitFormula` is an identity once the presheaf functor is taken to be
`p.op.lan`. The formula is stated as a natural isomorphism of functors rather than object by
object, so it is natural in the abelian sheaf, and the restriction maps are pinned by the chosen
cartesian lifts of `CategoryTheory.Functor.chosenPullbacks` rather than merely asserted to exist.

`CategoryTheory.Functor.Fiber` and `CategoryTheory.Functor.Fiber.fiberInclusion` are plain
`def`s, so a goal about the structure arrow of an object of a fibre, or about the lift of a
morphism, is not type-correct at `implicit` transparency and instance search refuses it; they are
therefore made locally `implicit_reducible`, as is `fiberOpToCostructuredArrow` itself, whose
values have to be recognised as costructured arrows built from `eqToHom`.

## References

* [Stacks Project, Tag 08PE](https://stacks.math.columbia.edu/tag/08PE)
* [Stacks Project, Tag 08P8](https://stacks.math.columbia.edu/tag/08P8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace Stacks.Sites.FibredCategory

universe uD vD uC vC w

attribute [local implicit_reducible] Functor.Fiber Functor.Fiber.fiberInclusion

section Finality

variable {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]

/-- The canonical inclusion of the opposite fibre of `p` at `V` into the costructured-arrow
category computing the pointwise left Kan extension along `p.op`: an object of the fibre is an
object `x` of `C` together with an identification `p.obj x = V`, which is in particular a
morphism `p.op.obj (op x) ⟶ op V`. -/
@[implicit_reducible]
def fiberOpToCostructuredArrow (p : C ⥤ D) (V : D) :
    (p.Fiber V)ᵒᵖ ⥤ CostructuredArrow p.op (op V) where
  obj x := CostructuredArrow.mk (eqToHom (congrArg op x.unop.2))
  map f := CostructuredArrow.homMk (op (Functor.Fiber.fiberInclusion.map f.unop)) (by
    apply Quiver.Hom.unop_inj
    simp only [Functor.op_map, unop_comp, Quiver.Hom.unop_op]
    change _ ≫ p.map (Functor.Fiber.fiberInclusion.map f.unop) = _
    rw [IsHomLift.fac' p (𝟙 V) (Functor.Fiber.fiberInclusion.map f.unop)]; simp)
  map_id x := by apply CostructuredArrow.hom_ext; apply Quiver.Hom.unop_inj; simp
  map_comp f g := by apply CostructuredArrow.hom_ext; apply Quiver.Hom.unop_inj; simp

/-- Projecting the inclusion of the opposite fibre back to `Cᵒᵖ` gives the opposite of the
ordinary inclusion of the fibre. -/
def fiberOpToCostructuredArrowCompProj (p : C ⥤ D) (V : D) :
    fiberOpToCostructuredArrow p V ⋙ CostructuredArrow.proj p.op (op V) ≅
      (Functor.Fiber.fiberInclusion (p := p) (S := V)).op :=
  Iso.refl _

/-- **The opposite fibre of a fibred category is final** in the costructured-arrow category used
to compute the pointwise left Kan extension along `p.op`.

A costructured arrow `z` is a morphism `b : V ⟶ p.obj z.left`; a cartesian lift of `b` places `z`
over an object of the fibre, and the universal property of that lift connects any two objects
over `z`, so the comma category of objects over `z` is connected. -/
instance final_fiberOpToCostructuredArrow (p : C ⥤ D) [p.IsFibered] (V : D) :
    (fiberOpToCostructuredArrow p V).Final := by
  constructor
  intro z
  let b := z.hom.unop
  let x : p.Fiber (p.obj z.left.unop) := ⟨z.left.unop, rfl⟩
  let y : p.Fiber V := (Functor.chosenPullbacks p).obj b x
  let cart : y.1 ⟶ z.left.unop := (Functor.chosenPullbacks p).map b x
  let : p.IsStronglyCartesian b cart := (Functor.chosenPullbacks p).isStronglyCartesian b x
  let η : z ⟶ (fiberOpToCostructuredArrow p V).obj (Opposite.op y) :=
    CostructuredArrow.homMk (op cart) (by
      apply Quiver.Hom.unop_inj
      simp only [Functor.op_map, unop_comp, Quiver.Hom.unop_op]
      simpa [fiberOpToCostructuredArrow] using (IsHomLift.fac p b cart).symm)
  let t : StructuredArrow z (fiberOpToCostructuredArrow p V) := StructuredArrow.mk η
  let : Nonempty (StructuredArrow z (fiberOpToCostructuredArrow p V)) := ⟨t⟩
  apply zigzag_isConnected
  intro a a'
  have pathToT : ∀ a : StructuredArrow z (fiberOpToCostructuredArrow p V), Zigzag t a := by
    intro a
    let q : a.right.unop.1 ⟶ z.left.unop := a.hom.left.unop
    have hbase : eqToHom a.right.unop.2.symm ≫ p.map q = b := by
      simpa [q, b, fiberOpToCostructuredArrow, Functor.op_map, unop_comp,
        Quiver.Hom.unop_op] using congrArg Quiver.Hom.unop (CostructuredArrow.w a.hom)
    have hmap : p.map q = eqToHom a.right.unop.2 ≫ b := by
      rw [← hbase, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
    let : p.IsHomLift (eqToHom a.right.unop.2 ≫ b) q := by rw [← hmap]; infer_instance
    let β : a.right.unop.1 ⟶ y.1 := Functor.IsStronglyCartesian.map p b cart hmap q
    let : p.IsHomLift (𝟙 V) β :=
      (IsHomLift.lift_eqToHom_comp_iff p (𝟙 V) β a.right.unop.2).mp (by
        simpa using (Functor.IsStronglyCartesian.map_isHomLift p b cart hmap q))
    let γ : a.right.unop ⟶ y := Functor.Fiber.homMk p V β
    exact Zigzag.of_hom (StructuredArrow.homMk (op γ) (by
      apply CostructuredArrow.hom_ext
      apply Quiver.Hom.unop_inj
      change β ≫ cart = q
      exact Functor.IsStronglyCartesian.fac p b cart hmap q))
  exact (pathToT a).symm.trans (pathToT a')

end Finality

variable (s : FibredCategorySituation.{uD, vD, uC, vC, w})

/-- The value at `V` of the left Kan extension of `F` along `p.op` is the colimit of `F` over the
opposite fibre at `V`, the fibre being final in the costructured-arrow category. -/
def fiberColimitIso (F : s.Cᵒᵖ ⥤ AddCommGrpCat.{max w uD vD uC vC}) (V : s.base.C) :
    (s.p.op.lan.obj F).obj (op V) ≅
      colimit ((Functor.Fiber.fiberInclusion (p := s.p) (S := V)).op ⋙ F) :=
  Functor.leftKanExtensionObjIsoColimit s.p.op F (op V) ≪≫
    (Functor.Final.colimitIso (fiberOpToCostructuredArrow s.p V)
      (CostructuredArrow.proj s.p.op (op V) ⋙ F)).symm ≪≫
    HasColimit.isoOfNatIso (Functor.associator (fiberOpToCostructuredArrow s.p V)
      (CostructuredArrow.proj s.p.op (op V)) F).symm ≪≫
    HasColimit.isoOfNatIso
      (Functor.isoWhiskerRight (fiberOpToCostructuredArrowCompProj s.p V) F)

/-- The inverse comparison carries the generator of the fibre colimit at `x` to the unit of the
Kan extension followed by the map induced by the structure arrow of `x`. -/
theorem ι_fiberColimitIso_inv (F : s.Cᵒᵖ ⥤ AddCommGrpCat.{max w uD vD uC vC}) (V : s.base.C)
    (x : s.p.Fiber V) :
    colimit.ι ((Functor.Fiber.fiberInclusion (p := s.p) (S := V)).op ⋙ F)
        (Opposite.op x) ≫ (fiberColimitIso s F V).inv =
      (s.p.op.leftKanExtensionUnit F).app (op x.1) ≫
        (s.p.op.leftKanExtension F).map
          ((fiberOpToCostructuredArrow s.p V).obj (Opposite.op x)).hom := by
  let J := fiberOpToCostructuredArrow s.p V
  let P := CostructuredArrow.proj s.p.op (op V)
  let w := Functor.isoWhiskerRight (fiberOpToCostructuredArrowCompProj s.p V) F
  let a := Functor.associator J P F
  let e := Functor.Final.colimitIso J (P ⋙ F)
  let iw := HasColimit.isoOfNatIso w
  let ia := HasColimit.isoOfNatIso a
  let k := Functor.leftKanExtensionObjIsoColimit s.p.op F (op V)
  show colimit.ι (Functor.Fiber.fiberInclusion.op ⋙ F) (op x) ≫
      (k ≪≫ e.symm ≪≫ ia.symm ≪≫ iw).inv =
    (s.p.op.leftKanExtensionUnit F).app (op x.1) ≫
      (s.p.op.leftKanExtension F).map (J.obj (op x)).hom
  rw [Iso.trans_inv, Iso.trans_inv, Iso.trans_inv]
  simp only [← Category.assoc]
  rw [HasColimit.isoOfNatIso_ι_inv]
  simp only [Functor.comp_obj, Functor.op_obj, fiberOpToCostructuredArrow,
    CostructuredArrow.mk_left, CostructuredArrow.proj_obj, fiberOpToCostructuredArrowCompProj,
    Functor.isoWhiskerRight_refl, Iso.refl_inv, NatTrans.id_app, Category.id_comp, Iso.symm_inv,
    Category.assoc, CostructuredArrow.mk_hom_eq_self, P, w, J]
  simp only [← Category.assoc]
  rw [HasColimit.isoOfNatIso_ι_hom, Functor.associator_hom_app]
  have hid : (𝟙 (((J ⋙ P) ⋙ F).obj (op x))) ≫
      colimit.ι (J ⋙ P ⋙ F) (op x) = colimit.ι (J ⋙ P ⋙ F) (op x) := by cat_disch
  rw [hid, Functor.Final.ι_colimitIso_hom, Functor.ι_leftKanExtensionObjIsoColimit_inv]
  rfl

/-- The fibrewise-colimit formula for the lower shriek on abelian sheaves. `presheafFunctor` is
the presheaf whose value at `V` is the colimit over the opposite fibre, `comparison` identifies
its values with those colimits, `restriction` characterizes its restriction maps by the chosen
cartesian lifts, and `sheafIso` identifies its sheafification with the lower shriek. -/
structure FiberwiseColimitFormula
    [HasWeakSheafify s.base.J AddCommGrpCat.{max w uD vD uC vC}] where
  /-- The presheaf of fibrewise colimits, as a functor of the coefficient presheaf. -/
  presheafFunctor : (s.Cᵒᵖ ⥤ AddCommGrpCat.{max w uD vD uC vC}) ⥤
    (s.base.Cᵒᵖ ⥤ AddCommGrpCat.{max w uD vD uC vC})
  /-- Its value at `V` is the colimit over the opposite fibre at `V`. -/
  comparison (F : s.Cᵒᵖ ⥤ AddCommGrpCat.{max w uD vD uC vC}) (V : s.base.C) :
    (presheafFunctor.obj F).obj (op V) ≅ colimit
      ((Functor.Fiber.fiberInclusion (p := s.p) (S := V)).op ⋙ F)
  /-- The comparison is natural in the coefficients. -/
  comparison_naturality (F G : s.Cᵒᵖ ⥤ AddCommGrpCat.{max w uD vD uC vC})
      (α : F ⟶ G) (V : s.base.C) :
    (presheafFunctor.map α).app (op V) ≫ (comparison G V).hom =
      (comparison F V).hom ≫ colim.map (Functor.whiskerLeft
        (Functor.Fiber.fiberInclusion (p := s.p) (S := V)).op α)
  /-- Its restriction map along `h : V' ⟶ V` sends the generator at `x` to the generator at the
  chosen pullback of `x`, composed with restriction of `F` along the chosen cartesian lift. -/
  restriction (F : s.Cᵒᵖ ⥤ AddCommGrpCat.{max w uD vD uC vC}) {V V' : s.base.C}
      (h : V' ⟶ V) (x : s.p.Fiber V) :
    colimit.ι ((Functor.Fiber.fiberInclusion (p := s.p) (S := V)).op ⋙ F) (op x) ≫
        (comparison F V).inv ≫ (presheafFunctor.obj F).map h.op ≫ (comparison F V').hom =
      F.map (.op ((Functor.chosenPullbacks s.p).map h x)) ≫
        colimit.ι ((Functor.Fiber.fiberInclusion (p := s.p) (S := V')).op ⋙ F)
          (.op ((Functor.chosenPullbacks s.p).obj h x))
  /-- The lower shriek is the sheafification of the fibrewise presheaf. -/
  sheafIso :
    Functor.sheafPullbackConstruction.sheafPullback s.p
        AddCommGrpCat.{max w uD vD uC vC} s.topology s.base.J ≅
      sheafToPresheaf s.topology AddCommGrpCat.{max w uD vD uC vC} ⋙ presheafFunctor ⋙
        presheafToSheaf s.base.J AddCommGrpCat.{max w uD vD uC vC}

/-- The comparison `fiberColimitIso` is natural in the coefficient presheaf. -/
theorem fiberColimitIso_hom_naturality (F G : s.Cᵒᵖ ⥤ AddCommGrpCat.{max w uD vD uC vC})
    (α : F ⟶ G) (V : s.base.C) :
    (s.p.op.lan.map α).app (op V) ≫ (fiberColimitIso s G V).hom =
      (fiberColimitIso s F V).hom ≫ colim.map (Functor.whiskerLeft
        (Functor.Fiber.fiberInclusion (p := s.p) (S := V)).op α) := by
  rw [← cancel_epi (fiberColimitIso s F V).inv, ← cancel_mono (fiberColimitIso s G V).inv]
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id, Iso.inv_hom_id_assoc]
  apply colimit.hom_ext
  intro x
  rw [colim_map, ι_colimMap_assoc, ← Category.assoc, ι_fiberColimitIso_inv,
    ι_fiberColimitIso_inv]
  have hunit := congr_app (s.p.op.lanUnit.naturality α) (op x.unop.1)
  have hnat := (s.p.op.lan.map α).naturality
    ((fiberOpToCostructuredArrow s.p V).obj (op x.unop)).hom
  dsimp [Functor.lan, Functor.lanUnit] at hunit hnat ⊢
  rw [Category.assoc, hnat, ← Category.assoc]
  erw [← hunit]
  rfl

/-- Restricting the unit of the Kan extension at `x` along `h` agrees with restricting `F` along
the chosen cartesian lift of `h` and then taking the unit at the chosen pullback of `x`. -/
theorem leftKanExtensionUnit_comp_map_chosenPullbacks
    (F : s.Cᵒᵖ ⥤ AddCommGrpCat.{max w uD vD uC vC}) {V V' : s.base.C} (h : V' ⟶ V)
    (x : s.p.Fiber V) :
    (s.p.op.leftKanExtensionUnit F).app (op x.1) ≫ (s.p.op.leftKanExtension F).map
        (((fiberOpToCostructuredArrow s.p V).obj (op x)).hom ≫ h.op) =
      F.map (op ((Functor.chosenPullbacks s.p).map h x)) ≫
        (s.p.op.leftKanExtensionUnit F).app (op ((Functor.chosenPullbacks s.p).obj h x).1) ≫
          (s.p.op.leftKanExtension F).map ((fiberOpToCostructuredArrow s.p V').obj
            (op ((Functor.chosenPullbacks s.p).obj h x))).hom := by
  let y := (Functor.chosenPullbacks s.p).obj h x
  let cart := (Functor.chosenPullbacks s.p).map h x
  let _ : s.p.IsStronglyCartesian h cart := (Functor.chosenPullbacks s.p).isStronglyCartesian h x
  let P := CostructuredArrow.proj s.p.op (op V')
  let xArr := (fiberOpToCostructuredArrow s.p V).obj (op x)
  let yArr := (fiberOpToCostructuredArrow s.p V').obj (op y)
  let ext := CostructuredArrow.mk (xArr.hom ≫ h.op)
  let liftMor : ext ⟶ yArr := CostructuredArrow.homMk (op cart) (by
    apply Quiver.Hom.unop_inj
    have hfac : eqToHom y.2.symm ≫ s.p.map cart = h ≫ eqToHom x.2.symm := by
      rw [IsHomLift.fac' s.p h cart, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
    simpa [yArr, ext, xArr, fiberOpToCostructuredArrow, Functor.op_map,
      unop_comp, Quiver.Hom.unop_op, eqToHom_unop] using hfac)
  have hcol : F.map (op cart) ≫ colimit.ι (P ⋙ F) yArr = colimit.ι (P ⋙ F) ext := by
    simpa [P, yArr, ext, xArr, liftMor, fiberOpToCostructuredArrow] using
      (colimit.w (P ⋙ F) liftMor)
  have hix : Functor.Fiber.fiberInclusion.1 x = x.1 := rfl
  have hk := congrArg (fun k => k ≫
    (s.p.op.leftKanExtensionObjIsoColimit F (op V')).inv) hcol
  have hcart' :
      (s.p.op.leftKanExtensionUnit F).app (op x.1) ≫
          (s.p.op.leftKanExtension F).map (xArr.hom ≫ h.op) =
        (s.p.op.leftKanExtensionUnit F).app (op x.1) ≫
          (s.p.op.leftKanExtension F).map (s.p.map cart).op ≫
            (s.p.op.leftKanExtension F).map yArr.hom := by
    convert hk.symm using 1 <;>
      simp [Category.assoc, Functor.ι_leftKanExtensionObjIsoColimit_inv,
        P, yArr, ext, xArr, fiberOpToCostructuredArrow, hix] <;> rfl
  have hunit : (s.p.op.leftKanExtensionUnit F).app (op x.1) ≫
      (s.p.op.leftKanExtension F).map (s.p.map cart).op =
      F.map (op cart) ≫ (s.p.op.leftKanExtensionUnit F).app (op y.1) :=
    ((s.p.op.leftKanExtensionUnit F).naturality cart.op).symm
  refine hcart'.trans ?_
  conv_rhs => rw [← Category.assoc]
  rw [← hunit]
  cat_disch

/-- The restriction maps of the left Kan extension along `p.op`, read through `fiberColimitIso`,
are induced by the chosen cartesian lifts. -/
theorem ι_fiberColimitIso_inv_lan_map_hom (F : s.Cᵒᵖ ⥤ AddCommGrpCat.{max w uD vD uC vC})
    {V V' : s.base.C} (h : V' ⟶ V) (x : s.p.Fiber V) :
    colimit.ι ((Functor.Fiber.fiberInclusion (p := s.p) (S := V)).op ⋙ F) (op x) ≫
        (fiberColimitIso s F V).inv ≫ (s.p.op.lan.obj F).map h.op ≫
          (fiberColimitIso s F V').hom =
      F.map (.op ((Functor.chosenPullbacks s.p).map h x)) ≫
        colimit.ι ((Functor.Fiber.fiberInclusion (p := s.p) (S := V')).op ⋙ F)
          (.op ((Functor.chosenPullbacks s.p).obj h x)) := by
  let y := (Functor.chosenPullbacks s.p).obj h x
  let cart := (Functor.chosenPullbacks s.p).map h x
  apply (cancel_mono (fiberColimitIso s F V').inv).mp
  simp only [Category.assoc, Iso.hom_inv_id]
  show (colimit.ι ((Functor.Fiber.fiberInclusion (p := s.p) (S := V)).op ⋙ F)
      (op x) ≫ (fiberColimitIso s F V).inv) ≫
      (s.p.op.lan.obj F).map h.op =
    F.map (op cart) ≫
      (colimit.ι ((Functor.Fiber.fiberInclusion (p := s.p) (S := V')).op ⋙ F)
        (op y) ≫ (fiberColimitIso s F V').inv)
  rw [ι_fiberColimitIso_inv s F V x, ι_fiberColimitIso_inv s F V' y]
  dsimp [Functor.lan]
  rw [Category.assoc, ← (s.p.op.leftKanExtension F).map_comp]
  convert leftKanExtensionUnit_comp_map_chosenPullbacks s F h x using 1

/-- **Stacks 08PE.** The lower shriek of an abelian sheaf along the projection of a fibred
category is the sheaf associated to the presheaf of fibrewise colimits, with restriction maps
induced by the chosen cartesian lifts. -/
@[stacks 08PE]
def fiberwiseColimitFormula
    [HasWeakSheafify s.base.J AddCommGrpCat.{max w uD vD uC vC}] :
    FiberwiseColimitFormula s :=
  ⟨s.p.op.lan, fiberColimitIso s, fiberColimitIso_hom_naturality s,
    ι_fiberColimitIso_inv_lan_map_hom s, by
      dsimp [Functor.sheafPullbackConstruction.sheafPullback]
      exact Iso.refl _⟩

end Stacks.Sites.FibredCategory

end
