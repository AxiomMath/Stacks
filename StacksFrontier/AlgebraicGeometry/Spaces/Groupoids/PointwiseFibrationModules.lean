module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.PointwiseFibrationArrows
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.ModulePullbackTwoMorphism
public import StacksFrontier.CategoryTheory.Sites.SheafOfSurjectiveCocontinuous

/-!
# Modules on the pointwise groupoid fibration as descent data on the object space

Let `G = (U, R, s, t, c)` be a groupoid in algebraic spaces and let `P = [U/_pR]` be its pointwise
groupoid fibration.  The category of the object space `𝒮_U` (Stacks 0458) has the same objects as
`P`, and `P` has in addition, for every `T`-point `r` of `R`, a morphism `(T, s(r)) ⟶ (T, t(r))`
over the identity of `T`.  So a module on `P` is a module `M` on `𝒮_U` together with, for every
such `r`, a map `M(T, t(r)) ⟶ M(T, s(r))`: a morphism `β : t^*M ⟶ s^*M` of modules on `𝒮_R`,
subject to a unit and a cocycle condition.  This file sets up that dictionary.

## Main definitions

* `AlgebraicGeometry.Stack.PointwiseDescentDatum`: a module on `𝒮_U` with a descent morphism
  `β : t^*M ⟶ s^*M` satisfying the unit and cocycle conditions on `T`-points.
* `AlgebraicGeometry.Stack.PointwiseDescentDatum.presheaf`: the presheaf of abelian groups on `P`
  it defines.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

namespace AlgebraicGeometry.Stack

universe u

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
  {B : AlgebraicSpaces C S hS} (G : GroupoidInAlgebraicSpaces C S hS B)

/-- The structure sheaf of rings of the category of the object space of `G`. -/
abbrev objRing := ringStructureSheafCore C S hS (fibredCategory C S hS G.objects.obj).val.p
  (fibredCategory C S hS G.objects.obj).property C.topology le_rfl

/-- The structure sheaf of rings of the category of the arrow space of `G`. -/
abbrev arrRing := ringStructureSheafCore C S hS (fibredCategory C S hS G.arrows.obj).val.p
  (fibredCategory C S hS G.arrows.obj).property C.topology le_rfl

/-- The structure sheaf of rings of the pointwise groupoid fibration of `G`. -/
abbrev pointwiseRing := ringStructureSheafCore C S hS
  (presheafOfGroupoids (evaluationGroupoidFunctor G.toGroupoidInFunctors)).p
  (isFiberedInGroupoids_presheafOfGroupoids _) C.topology le_rfl

/-- Inverse image of modules along the target `t : 𝒮_R ⟶ 𝒮_U` (Stacks 06WE). -/
abbrev targetPullback : SheafOfModules.{u} (objRing G) ⥤ SheafOfModules.{u} (arrRing G) :=
  modulePullback C S hS (fibredCategory C S hS G.arrows.obj).val.p
    (fibredCategory C S hS G.objects.obj).val.p (fibredCategory C S hS G.arrows.obj).property
    (fibredCategory C S hS G.objects.obj).property (quotientStackTargetLeg G)
    (associatedMap C S hS G.target.hom).1.hom.w C.topology le_rfl

/-- Inverse image of modules along the source `s : 𝒮_R ⟶ 𝒮_U` (Stacks 06WE). -/
abbrev sourcePullback : SheafOfModules.{u} (objRing G) ⥤ SheafOfModules.{u} (arrRing G) :=
  modulePullback C S hS (fibredCategory C S hS G.arrows.obj).val.p
    (fibredCategory C S hS G.objects.obj).val.p (fibredCategory C S hS G.arrows.obj).property
    (fibredCategory C S hS G.objects.obj).property (quotientStackSourceLeg G)
    (associatedMap C S hS G.source.hom).1.hom.w C.topology le_rfl

variable {G}

/-- The component of a descent morphism `β : t^*M ⟶ s^*M` at a `T`-point `r` of `R`, as a map
`M(T, t(r)) ⟶ M(T, s(r))` of abelian groups. -/
def descComp {M : SheafOfModules.{u} (objRing G)}
    (β : (targetPullback G).obj M ⟶ (sourcePullback G).obj M) (T : BigFppfOver C S hS)
    (r : G.arrows.obj.obj (op T)) :
    M.val.presheaf.obj (op (objPt G T (G.target.hom.app (op T) r))) ⟶
      M.val.presheaf.obj (op (objPt G T (G.source.hom.app (op T) r))) :=
  ((PresheafOfModules.toPresheaf _).map β.val).app (op ⟨T, ⟨r⟩⟩)

/-- The component `descComp β T r` evaluated at a section `m` is the component of `β` at the
object `(T, r)` of the category of the arrow space, evaluated at `m`. -/
theorem descComp_apply {M : SheafOfModules.{u} (objRing G)}
    (β : (targetPullback G).obj M ⟶ (sourcePullback G).obj M) (T : BigFppfOver C S hS)
    (r : G.arrows.obj.obj (op T)) (m) :
    descComp β T r m = β.val.app (op ⟨T, ⟨r⟩⟩) m := rfl

variable (G) in
/-- The source of the identity arrow at a `T`-point `a` of `U` is `a`. -/
theorem source_identity (T : BigFppfOver C S hS) (a : G.toGroupoidInFunctors.Evaluation (op T)) :
    G.source.hom.app (op T) (G.toGroupoidInFunctors.identity (op T) a) = a :=
  (G.toGroupoidInFunctors.evaluationArrowEquiv (op T) a a (𝟙 a)).2.1

variable (G) in
/-- The target of the identity arrow at a `T`-point `a` of `U` is `a`. -/
theorem target_identity (T : BigFppfOver C S hS) (a : G.toGroupoidInFunctors.Evaluation (op T)) :
    G.target.hom.app (op T) (G.toGroupoidInFunctors.identity (op T) a) = a :=
  (G.toGroupoidInFunctors.evaluationArrowEquiv (op T) a a (𝟙 a)).2.2

variable (G) in
/-- The composite `c(a, b)` of composable `T`-points of `R` has the source of `b` and the target
of `a`. -/
private theorem source_target_compose (T : BigFppfOver C S hS) (a b : G.arrows.obj.obj (op T))
    (h : G.source.hom.app (op T) a = G.target.hom.app (op T) b) :
    G.source.hom.app (op T) (G.toGroupoidInFunctors.compose (op T) a b h) =
        G.source.hom.app (op T) b ∧
      G.target.hom.app (op T) (G.toGroupoidInFunctors.compose (op T) a b h) =
        G.target.hom.app (op T) a := by
  let := G.toGroupoidInFunctors.evaluationGroupoid (op T)
  let f := (G.toGroupoidInFunctors.evaluationArrowEquiv (op T) (G.source.hom.app (op T) b)
    (G.target.hom.app (op T) b)).symm ⟨b, rfl, rfl⟩
  let g := (G.toGroupoidInFunctors.evaluationArrowEquiv (op T) (G.target.hom.app (op T) b)
    (G.target.hom.app (op T) a)).symm ⟨a, h, rfl⟩
  have hc : (G.toGroupoidInFunctors.evaluationArrowEquiv (op T) _ _ (f ≫ g)).1 =
      G.toGroupoidInFunctors.compose (op T) a b h :=
    (Deformation.GroupoidInFunctors.evaluationArrowEquiv_comp _ _ _ _).trans
      (compose_congr' G _ _ _ (congrArg Subtype.val (Equiv.apply_symm_apply _ _))
        (congrArg Subtype.val (Equiv.apply_symm_apply _ _)))
  exact ⟨(congrArg (G.source.hom.app (op T)) hc).symm.trans
    (G.toGroupoidInFunctors.evaluationArrowEquiv (op T) _ _ (f ≫ g)).2.1,
    (congrArg (G.target.hom.app (op T)) hc).symm.trans
    (G.toGroupoidInFunctors.evaluationArrowEquiv (op T) _ _ (f ≫ g)).2.2⟩

variable (G) in
/-- The source of the composite `c(a, b)` of composable `T`-points of `R` is the source of `b`. -/
theorem source_compose (T : BigFppfOver C S hS) (a b : G.arrows.obj.obj (op T))
    (h : G.source.hom.app (op T) a = G.target.hom.app (op T) b) :
    G.source.hom.app (op T) (G.toGroupoidInFunctors.compose (op T) a b h) =
      G.source.hom.app (op T) b :=
  (source_target_compose G T a b h).1

variable (G) in
/-- The target of the composite `c(a, b)` of composable `T`-points of `R` is the target of `a`. -/
theorem target_compose (T : BigFppfOver C S hS) (a b : G.arrows.obj.obj (op T))
    (h : G.source.hom.app (op T) a = G.target.hom.app (op T) b) :
    G.target.hom.app (op T) (G.toGroupoidInFunctors.compose (op T) a b h) =
      G.target.hom.app (op T) a :=
  (source_target_compose G T a b h).2

/-- Transport of sections of a module on the object space along an equality of points. -/
def ptTransport (M : SheafOfModules.{u} (objRing G)) {T : BigFppfOver C S hS}
    {a a' : G.objects.obj.obj (op T)} (h : a = a') :
    M.val.presheaf.obj (op (objPt G T a')) ⟶ M.val.presheaf.obj (op (objPt G T a)) :=
  M.val.presheaf.map (eqToHom (congrArg (objPt G T) h)).op

/-- Transport along a reflexivity proof is the identity. -/
@[simp]
theorem ptTransport_rfl (M : SheafOfModules.{u} (objRing G)) {T : BigFppfOver C S hS}
    (a : G.objects.obj.obj (op T)) : ptTransport M (rfl : a = a) = 𝟙 _ := by
  simp [ptTransport]

/-- Transport along `h'` followed by transport along `h` is transport along `h.trans h'`. -/
@[reassoc (attr := simp)]
theorem ptTransport_trans (M : SheafOfModules.{u} (objRing G)) {T : BigFppfOver C S hS}
    {a a' a'' : G.objects.obj.obj (op T)} (h : a = a') (h' : a' = a'') :
    ptTransport M h' ≫ ptTransport M h = ptTransport M (h.trans h') := by
  subst h h'
  simp

variable (G) in
/-- **A descent datum on the object space of `G`**: a sheaf of modules `M` on `𝒮_U` with a
morphism `β : t^*M ⟶ s^*M` of modules on `𝒮_R` which is the identity at unit arrows and takes
composites to composites.  These are exactly the modules on the pointwise groupoid fibration. -/
structure PointwiseDescentDatum where
  /-- The underlying module on the object space. -/
  M : SheafOfModules.{u} (objRing G)
  /-- The descent morphism. -/
  β : (targetPullback G).obj M ⟶ (sourcePullback G).obj M
  /-- The unit condition. -/
  unit (T : BigFppfOver C S hS) (a : G.objects.obj.obj (op T)) :
    descComp β T (G.toGroupoidInFunctors.identity (op T) a) =
      ptTransport M ((source_identity G T a).trans (target_identity G T a).symm)
  /-- The cocycle condition. -/
  cocycle (T : BigFppfOver C S hS) (a b : G.arrows.obj.obj (op T))
    (h : G.source.hom.app (op T) a = G.target.hom.app (op T) b) :
    descComp β T (G.toGroupoidInFunctors.compose (op T) a b h) =
      ptTransport M (target_compose G T a b h).symm ≫ descComp β T a ≫ ptTransport M h.symm ≫
        descComp β T b ≫ ptTransport M (source_compose G T a b h)

variable (G)

/-- The inclusion of the object space into the pointwise groupoid fibration commutes with the
projections to `BigFppfOver C S hS`. -/
theorem pointwiseObjectInclusion_comp_p :
    pointwiseObjectInclusion G ⋙
        (presheafOfGroupoids (evaluationGroupoidFunctor G.toGroupoidInFunctors)).p =
      (fibredCategory C S hS G.objects.obj).val.p := rfl

/-- Restriction of modules on the pointwise groupoid fibration to the object space. -/
abbrev objectRestriction : SheafOfModules.{u} (pointwiseRing G) ⥤ SheafOfModules.{u} (objRing G) :=
  modulePullback C S hS (fibredCategory C S hS G.objects.obj).val.p
    (presheafOfGroupoids (evaluationGroupoidFunctor G.toGroupoidInFunctors)).p
    (fibredCategory C S hS G.objects.obj).property (isFiberedInGroupoids_presheafOfGroupoids _)
    (pointwiseObjectInclusion G) (pointwiseObjectInclusion_comp_p G) C.topology le_rfl

variable {G}

/-- An `objHom` over an identity is the transport along the equality of points it records. -/
theorem objHom_id_eq_eqToHom {T : BigFppfOver C S hS} {a a' : G.objects.obj.obj (op T)}
    (e : G.objects.obj.map (𝟙 T).op a' = a) :
    objHom (𝟙 T) e = eqToHom (congrArg (objPt G T)
      (e.symm.trans (G.objects.obj.map_id_apply _ _))) := by
  apply objFib_hom_ext
  obtain rfl : a = a' := e.symm.trans (G.objects.obj.map_id_apply _ _)
  rfl

/-- The restriction map of a module on the object space along an `objHom` over an identity is the
transport along the equality of points it records. -/
theorem map_objHom_id (M : SheafOfModules.{u} (objRing G)) {T : BigFppfOver C S hS}
    {a a' : G.objects.obj.obj (op T)} (e : G.objects.obj.map (𝟙 T).op a' = a) :
    M.val.presheaf.map (objHom (𝟙 T) e).op =
      ptTransport M (e.symm.trans (G.objects.obj.map_id_apply _ _)) := by
  rw [objHom_id_eq_eqToHom]
  rfl

/-- The morphism `(T, R.map h r) ⟶ (T', r)` of the category of the arrow space over
`h : T ⟶ T'`. -/
def arrHom {T T' : BigFppfOver C S hS} (h : T ⟶ T') (r : G.arrows.obj.obj (op T')) :
    (⟨T, ⟨G.arrows.obj.map h.op r⟩⟩ : (fibredCategory C S hS G.arrows.obj).val.obj) ⟶
      ⟨T', ⟨r⟩⟩ :=
  ⟨h, eqToHom rfl⟩

/-- **Naturality of a descent morphism in the test object.** -/
theorem descComp_naturality {M : SheafOfModules.{u} (objRing G)}
    (β : (targetPullback G).obj M ⟶ (sourcePullback G).obj M) {T T' : BigFppfOver C S hS}
    (h : T ⟶ T') (r : G.arrows.obj.obj (op T')) :
    M.val.presheaf.map (objHom h (NatTrans.naturality_apply G.target.hom h.op r).symm).op ≫
        descComp β T (G.arrows.obj.map h.op r) =
      descComp β T' r ≫
        M.val.presheaf.map (objHom h (NatTrans.naturality_apply G.source.hom h.op r).symm).op :=
  ((PresheafOfModules.toPresheaf _).map β.val).naturality (arrHom h r).op

/-- The step of the restriction map of the module attached to a descent datum along a morphism
`(h, r)`: restriction along `h`, then the component of `β` at `r`, then transport. -/
def descStep {M : SheafOfModules.{u} (objRing G)}
    (β : (targetPullback G).obj M ⟶ (sourcePullback G).obj M) {T T' : BigFppfOver C S hS}
    (h : T ⟶ T') (a' : G.objects.obj.obj (op T')) (a : G.objects.obj.obj (op T))
    (r : G.arrows.obj.obj (op T)) (et : G.objects.obj.map h.op a' = G.target.hom.app (op T) r)
    (es : G.source.hom.app (op T) r = a) :
    M.val.presheaf.obj (op (objPt G T' a')) ⟶ M.val.presheaf.obj (op (objPt G T a)) :=
  M.val.presheaf.map (objHom h et).op ≫ descComp β T r ≫ ptTransport M es.symm

/-- `descStep β h a' a r et es` depends only on `r`, not on the equality proofs `et` and `es`. -/
theorem descStep_congr {M : SheafOfModules.{u} (objRing G)}
    (β : (targetPullback G).obj M ⟶ (sourcePullback G).obj M) {T T' : BigFppfOver C S hS}
    (h : T ⟶ T') (a' : G.objects.obj.obj (op T')) (a : G.objects.obj.obj (op T))
    {r r' : G.arrows.obj.obj (op T)} (hr : r = r')
    (et : G.objects.obj.map h.op a' = G.target.hom.app (op T) r)
    (es : G.source.hom.app (op T) r = a)
    (et' : G.objects.obj.map h.op a' = G.target.hom.app (op T) r')
    (es' : G.source.hom.app (op T) r' = a) :
    descStep β h a' a r et es = descStep β h a' a r' et' es' := by
  subst hr
  rfl

/-- The restriction map along a morphism of the pointwise groupoid fibration of the presheaf
attached to a descent datum. -/
def glueMap (D : PointwiseDescentDatum G) {x y : PointwiseFibration G} (m : x ⟶ y) :
    D.M.val.presheaf.obj (op (objPt G y.base y.fiber)) ⟶
      D.M.val.presheaf.obj (op (objPt G x.base x.fiber)) :=
  descStep D.β m.base y.fiber x.fiber (pointwiseArrow G m) (target_pointwiseArrow G m).symm
    (source_pointwiseArrow G m)

/-- The glued restriction map along an identity morphism is the identity. -/
theorem glueMap_id (D : PointwiseDescentDatum G) (x : PointwiseFibration G) :
    glueMap D (𝟙 x) = 𝟙 _ := by
  unfold glueMap
  refine (descStep_congr D.β (𝟙 x.base) _ _ (pointwiseArrow_id G x) _ _
    ((G.objects.obj.map_id_apply _ _).trans (target_identity G _ _).symm)
    (source_identity G _ _)).trans ?_
  unfold descStep
  refine (whisker_eq _ (eq_whisker (D.unit _ _) _)).trans ?_
  refine (eq_whisker (map_objHom_id D.M _) _).trans ?_
  refine (ptTransport_trans_assoc D.M _ _ _).trans ?_
  exact (ptTransport_trans D.M _ _).trans (ptTransport_rfl _ _)

/-- The base of the morphism `eqToHom h` of the category of the object space is `eqToHom` of the
induced equality of bases. -/
theorem objFib_eqToHom_base {X Y : ObjFib G} (h : X = Y) :
    (eqToHom h).base = eqToHom (congrArg Pseudofunctor.CoGrothendieck.base h) := by
  subst h
  rfl

/-- Two composites of restriction maps of a module on the object space along morphisms with
equal composite bases agree. -/
theorem map_comp_map_eq (M : SheafOfModules.{u} (objRing G)) {X Y Y' Z : ObjFib G}
    (f : X ⟶ Y) (g : Y ⟶ Z) (f' : X ⟶ Y') (g' : Y' ⟶ Z) (h : f.base ≫ g.base = f'.base ≫ g'.base) :
    M.val.presheaf.map g.op ≫ M.val.presheaf.map f.op =
      M.val.presheaf.map g'.op ≫ M.val.presheaf.map f'.op := by
  rw [← Functor.map_comp, ← Functor.map_comp, ← op_comp, ← op_comp,
    objFib_hom_ext (f ≫ g) (f' ≫ g') h]

/-- A composite of two restriction maps of a module on the object space equals the restriction map
along a morphism with the same composite base. -/
theorem map_comp_map_eq_map (M : SheafOfModules.{u} (objRing G)) {X Y Z : ObjFib G}
    (f : X ⟶ Y) (g : Y ⟶ Z) (k : X ⟶ Z) (h : f.base ≫ g.base = k.base) :
    M.val.presheaf.map g.op ≫ M.val.presheaf.map f.op = M.val.presheaf.map k.op := by
  rw [← Functor.map_comp, ← op_comp, objFib_hom_ext (f ≫ g) k h]

/-- The glued restriction map along a composite `m ≫ m'` is the composite of the glued restriction
maps along `m'` and `m`. -/
theorem glueMap_comp (D : PointwiseDescentDatum G) {x y z : PointwiseFibration G} (m : x ⟶ y)
    (m' : y ⟶ z) : glueMap D (m ≫ m') = glueMap D m' ≫ glueMap D m := by
  set h := m.base
  set h' := m'.base
  set r := pointwiseArrow G m
  set r' := pointwiseArrow G m'
  have w : G.source.hom.app (op x.base) (G.arrows.obj.map h.op r') =
      G.target.hom.app (op x.base) r :=
    ((NatTrans.naturality_apply G.source.hom h.op r').trans (congrArg
      (G.objects.obj.map h.op) (source_pointwiseArrow G m'))).trans (target_pointwiseArrow G m).symm
  have hq : pointwiseArrow G (m ≫ m') =
      G.toGroupoidInFunctors.compose (op x.base) (G.arrows.obj.map h.op r') r w :=
    pointwiseArrow_comp_eq_compose G m m'
  have et : G.objects.obj.map (h ≫ h').op z.fiber = G.target.hom.app (op x.base)
      (G.toGroupoidInFunctors.compose (op x.base) (G.arrows.obj.map h.op r') r w) :=
    (target_pointwiseArrow G (m ≫ m')).symm.trans (congrArg (G.target.hom.app (op x.base)) hq)
  have es : G.source.hom.app (op x.base)
      (G.toGroupoidInFunctors.compose (op x.base) (G.arrows.obj.map h.op r') r w) = x.fiber :=
    (congrArg (G.source.hom.app (op x.base)) hq).symm.trans (source_pointwiseArrow G (m ≫ m'))
  refine (descStep_congr D.β _ _ _ hq _ _ et es).trans ?_
  unfold descStep glueMap
  refine (whisker_eq _ (eq_whisker (D.cocycle _ _ _ w) _)).trans ?_
  have nt : G.objects.obj.map h.op (G.target.hom.app (op y.base) r') =
      G.target.hom.app (op x.base) (G.arrows.obj.map h.op r') :=
    (NatTrans.naturality_apply G.target.hom h.op r').symm
  have ns : G.objects.obj.map h.op (G.source.hom.app (op y.base) r') =
      G.source.hom.app (op x.base) (G.arrows.obj.map h.op r') :=
    (NatTrans.naturality_apply G.source.hom h.op r').symm
  have A : ∀ {W} (k : D.M.val.presheaf.obj (op (objPt G x.base
      (G.target.hom.app (op x.base) (G.arrows.obj.map h.op r')))) ⟶ W),
      D.M.val.presheaf.map (objHom (h ≫ h') et).op ≫
        ptTransport D.M (target_compose G _ _ _ w).symm ≫ k =
      D.M.val.presheaf.map (objHom h' (target_pointwiseArrow G m').symm).op ≫
        D.M.val.presheaf.map (objHom h nt).op ≫ k := by
    intro W k
    rw [← Category.assoc, ← Category.assoc]; congr 1
    exact map_comp_map_eq D.M _ _ _ _ (by
      simp only [objFib_eqToHom_base, eqToHom_refl, Category.id_comp]; rfl)
  have Cc : ∀ {W} (k : D.M.val.presheaf.obj (op (objPt G x.base
      (G.target.hom.app (op x.base) r))) ⟶ W),
      D.M.val.presheaf.map (objHom h ns).op ≫ ptTransport D.M w.symm ≫ k =
      ptTransport D.M (source_pointwiseArrow G m').symm ≫
        D.M.val.presheaf.map (objHom h (target_pointwiseArrow G m).symm).op ≫ k := by
    intro W k
    rw [← Category.assoc, ← Category.assoc]; congr 1
    exact map_comp_map_eq D.M _ _ _ _ (by
      simp only [objFib_eqToHom_base, eqToHom_refl, Category.id_comp, Category.comp_id]; rfl)
  simp only [Category.assoc]
  rw [A, reassoc_of% (descComp_naturality D.β h r'), Cc]
  exact whisker_eq _ (whisker_eq _ (whisker_eq _ (whisker_eq _ (whisker_eq _
    (ptTransport_trans D.M _ _)))))

/-- The presheaf of abelian groups on the pointwise groupoid fibration attached to a descent
datum: the sections over `(T, a)` are those of `M` over `(T, a)`, and the restriction along a
morphism `(h, r)` is restriction along `h` followed by the component of `β` at `r`. -/
def PointwiseDescentDatum.presheaf (D : PointwiseDescentDatum G) :
    (PointwiseFibration G)ᵒᵖ ⥤ Ab.{u} where
  obj x := D.M.val.presheaf.obj (op (objPt G x.unop.base x.unop.fiber))
  map m := glueMap D m.unop
  map_id x := glueMap_id D x.unop
  map_comp m m' := glueMap_comp D m'.unop m.unop

/-- The sections of the module attached to a descent datum are modules over the structure
sheaf of the pointwise groupoid fibration. -/
instance PointwiseDescentDatum.presheafModule (D : PointwiseDescentDatum G)
    (x : (PointwiseFibration G)ᵒᵖ) :
    Module ((pointwiseRing G).obj.obj x) (D.presheaf.obj x) :=
  (D.M.val.obj (op (objPt G x.unop.base x.unop.fiber))).isModule

/-- The sections of the underlying abelian presheaf of a presheaf of modules are modules. -/
abbrev presheafObjModule {R : (ObjFib G)ᵒᵖ ⥤ RingCat.{u}} (M : PresheafOfModules.{u} R)
    (X : (ObjFib G)ᵒᵖ) : Module (R.obj X) (M.presheaf.obj X) :=
  (M.obj X).isModule

attribute [local instance] presheafObjModule

/-- Transport along an equality of points is linear over the structure sheaf of rings. -/
theorem ptTransport_smul (M : SheafOfModules.{u} (objRing G)) {T : BigFppfOver C S hS}
    {a a' : G.objects.obj.obj (op T)} (h : a = a') (c : (objRing G).obj.obj (op (objPt G T a')))
    (v : M.val.presheaf.obj (op (objPt G T a'))) :
    ptTransport M h (c • v) =
      (show (objRing G).obj.obj (op (objPt G T a)) from c) •
        ptTransport M h v := by
  subst h
  simp
  rfl

/-- The component of a descent morphism at a `T`-point of `R` is linear over the structure sheaf
of rings. -/
theorem descComp_smul {M : SheafOfModules.{u} (objRing G)}
    (β : (targetPullback G).obj M ⟶ (sourcePullback G).obj M) (T : BigFppfOver C S hS)
    (r : G.arrows.obj.obj (op T))
    (c : (objRing G).obj.obj (op (objPt G T (G.target.hom.app (op T) r))))
    (v : M.val.presheaf.obj (op (objPt G T (G.target.hom.app (op T) r)))) :
    descComp β T r (c • v) =
      (show (objRing G).obj.obj (op (objPt G T (G.source.hom.app (op T) r))) from c) •
        descComp β T r v :=
  (β.val.app (op ⟨T, ⟨r⟩⟩)).hom.map_smul c v

/-- `descStep β h a' a r et es` is semilinear with respect to the restriction map of the structure
sheaf of rings along `objHom h et`. -/
theorem descStep_smul {M : SheafOfModules.{u} (objRing G)}
    (β : (targetPullback G).obj M ⟶ (sourcePullback G).obj M) {T T' : BigFppfOver C S hS}
    (h : T ⟶ T') (a' : G.objects.obj.obj (op T')) (a : G.objects.obj.obj (op T))
    (r : G.arrows.obj.obj (op T)) (et : G.objects.obj.map h.op a' = G.target.hom.app (op T) r)
    (es : G.source.hom.app (op T) r = a) (c : (objRing G).obj.obj (op (objPt G T' a')))
    (v : M.val.presheaf.obj (op (objPt G T' a'))) :
    descStep β h a' a r et es (c • v) =
      (show (objRing G).obj.obj (op (objPt G T a)) from (objRing G).obj.map (objHom h et).op c) •
        descStep β h a' a r et es v := by
  unfold descStep
  simp only [ConcreteCategory.comp_apply]
  refine (congrArg (fun z => ptTransport M es.symm (descComp β T r z))
    (M.val.map_smul (objHom h et).op c v)).trans ?_
  exact (congrArg (ptTransport M es.symm) (descComp_smul β T r _ _)).trans
    (ptTransport_smul M es.symm _ _)

/-- The presheaf of modules on the pointwise groupoid fibration attached to a descent datum. -/
def PointwiseDescentDatum.presheafOfModules (D : PointwiseDescentDatum G) :
    PresheafOfModules.{u} (pointwiseRing G).obj :=
  PresheafOfModules.ofPresheaf D.presheaf (fun {_ _} f c v =>
    descStep_smul D.β f.unop.base _ _ _ (target_pointwiseArrow G f.unop).symm
      (source_pointwiseArrow G f.unop) c v)

/-- **On the image of the object space the glued restriction maps are those of `M`.** -/
theorem glueMap_pointwiseObjectInclusion (D : PointwiseDescentDatum G) {X Y : ObjFib G}
    (g : X ⟶ Y) :
    glueMap D ((pointwiseObjectInclusion G).map g) = D.M.val.presheaf.map g.op := by
  unfold glueMap
  refine (descStep_congr D.β g.base _ _ (pointwiseArrow_pointwiseObjectInclusion_map G g) _ _
    ((target_pointwiseArrow G ((pointwiseObjectInclusion G).map g)).symm.trans
      (by rw [pointwiseArrow_pointwiseObjectInclusion_map]; rfl))
    (source_identity G _ _)).trans ?_
  unfold descStep
  refine (whisker_eq _ (eq_whisker (D.unit _ _) _)).trans ?_
  refine (whisker_eq _ (ptTransport_trans D.M _ _)).trans ?_
  unfold ptTransport
  exact map_comp_map_eq_map D.M _ _ _ (by
    rw [objFib_eqToHom_base, eqToHom_refl, Category.id_comp]; rfl)

/-- A morphism of the pointwise groupoid fibration over an identity is an isomorphism. -/
theorem isIso_vertHom (T : BigFppfOver C S hS) {a b : G.objects.obj.obj (op T)}
    (r : G.arrows.obj.obj (op T)) (hs : G.source.hom.app (op T) r = a)
    (ht : G.target.hom.app (op T) r = b) : IsIso (vertHom G T r hs ht) := by
  have hsc := (isFiberedInGroupoids_presheafOfGroupoids
    (evaluationGroupoidFunctor G.toGroupoidInFunctors)).isStronglyCartesian (vertHom G T r hs ht)
  have : IsIso ((presheafOfGroupoids (evaluationGroupoidFunctor G.toGroupoidInFunctors)).p.map
      (vertHom G T r hs ht)) := by
    show IsIso (𝟙 T)
    infer_instance
  exact Functor.IsStronglyCartesian.isIso_of_base_isIso
    (presheafOfGroupoids (evaluationGroupoidFunctor G.toGroupoidInFunctors)).p
    ((presheafOfGroupoids (evaluationGroupoidFunctor G.toGroupoidInFunctors)).p.map
      (vertHom G T r hs ht)) (vertHom G T r hs ht)

/-- A functor `f` between categories fibred in groupoids over `BigFppfOver C S hS` commuting with
the projections is continuous and cocontinuous for the two associated fppf topologies. -/
private theorem isContinuous_and_isCocontinuous_associatedTopology {𝒳 : Type*} [Category 𝒳]
    {𝒴 : Type*} [Category 𝒴] (p : 𝒳 ⥤ BigFppfOver C S hS) (q : 𝒴 ⥤ BigFppfOver C S hS)
    (hp : p.IsFiberedInGroupoids) (hq : q.IsFiberedInGroupoids) (f : 𝒳 ⥤ 𝒴) (hf : f ⋙ q = p) :
    f.IsContinuous (associatedTopology C S hS p C.topology)
        (associatedTopology C S hS q C.topology) ∧
      f.IsCocontinuous (associatedTopology C S hS p C.topology)
        (associatedTopology C S hS q C.topology) := by
  have := hp.isFibered
  have := hq.isFibered
  exact (hq.isFibredOneMorphism hf).isContinuous_and_isCocontinuous_inheritedTopology
    (C.topology.over (C.obj hS))

variable (G) in
/-- The inclusion of the object space into the pointwise groupoid fibration is cocontinuous for
the two associated fppf topologies. -/
theorem isCocontinuous_pointwiseObjectInclusion :
    (pointwiseObjectInclusion G).IsCocontinuous
      (associatedTopology C S hS (fibredCategory C S hS G.objects.obj).val.p C.topology)
      (associatedTopology C S hS
        (presheafOfGroupoids (evaluationGroupoidFunctor G.toGroupoidInFunctors)).p C.topology) := by
  exact (isContinuous_and_isCocontinuous_associatedTopology _ _
    (fibredCategory C S hS G.objects.obj).property (isFiberedInGroupoids_presheafOfGroupoids _)
    (pointwiseObjectInclusion G) (pointwiseObjectInclusion_comp_p G)).2

/-- **The presheaf attached to a descent datum is an fppf sheaf**: its restriction to the object
space is the sheaf `M`, and every morphism into an object of the pointwise fibration is a
morphism over an identity — an isomorphism — followed by the image of a morphism of the object
space. -/
theorem PointwiseDescentDatum.isSheaf_presheaf (D : PointwiseDescentDatum G) :
    Presheaf.IsSheaf (associatedTopology C S hS
      (presheafOfGroupoids (evaluationGroupoidFunctor G.toGroupoidInFunctors)).p C.topology)
      D.presheaf := by
  have := isCocontinuous_pointwiseObjectInclusion G
  refine Presheaf.isSheaf_of_isSheaf_comp_of_factor' (J₀ := associatedTopology C S hS
    (fibredCategory C S hS G.objects.obj).val.p C.topology) (pointwiseObjectInclusion G) D.presheaf
    (fun X => ⟨objPt G X.base X.fiber, rfl⟩) (fun {Y X₀} f => ?_) ?_
  · exact ⟨objPt G Y.base (G.objects.obj.map f.base.op X₀.fiber.as),
      vertHom G Y.base (pointwiseArrow G f) (source_pointwiseArrow G f)
        (target_pointwiseArrow G f), objHom f.base rfl, isIso_vertHom _ _ _ _,
      vertHom_comp_objHom G f⟩
  · have e : (pointwiseObjectInclusion G).op ⋙ D.presheaf ≅ D.M.val.presheaf :=
      NatIso.ofComponents (fun X => Iso.refl _) (fun {X Y} g => by
        simp only [Iso.refl_hom]
        exact glueMap_pointwiseObjectInclusion D g.unop)
    exact (Presheaf.isSheaf_of_iso_iff e).2 D.M.isSheaf

variable (G) in
/-- The canonical 2-morphism `x ∘ s ⟶ x ∘ t` from the arrow space to the pointwise groupoid
fibration: at a `T`-point `r` of `R` it is the morphism `(T, s(r)) ⟶ (T, t(r))` over the
identity whose arrow is `r`. -/
def pointwiseTwoArrow : quotientStackSourceLeg G ⋙ pointwiseObjectInclusion G ⟶
    quotientStackTargetLeg G ⋙ pointwiseObjectInclusion G where
  app x := vertHom G x.base x.fiber.as rfl rfl
  naturality {x x'} g := by
    have hx : x.fiber.as = G.arrows.obj.map g.base.op x'.fiber.as := Discrete.eq_of_hom g.fiber
    apply pointwiseArrow_hom_ext
    · change g.base ≫ 𝟙 _ = 𝟙 _ ≫ g.base
      rw [Category.comp_id, Category.id_comp]
    · refine (pointwiseArrow_comp_eq_compose G _ _).trans ?_
      refine Eq.trans ?_ (pointwiseArrow_comp_eq_compose G _ _).symm
      have l1 : G.arrows.obj.map ((pointwiseObjectInclusion G).map
          ((quotientStackSourceLeg G).map g)).base.op
          (pointwiseArrow G (vertHom G x'.base x'.fiber.as rfl rfl)) =
          G.arrows.obj.map g.base.op x'.fiber.as :=
        congrArg (G.arrows.obj.map g.base.op) (pointwiseArrow_vertHom G _ _ _ _)
      have r1 : G.arrows.obj.map (vertHom G x.base x.fiber.as rfl rfl).base.op
          (pointwiseArrow G ((pointwiseObjectInclusion G).map ((quotientStackTargetLeg G).map g))) =
          G.toGroupoidInFunctors.identity (op x.base) (G.target.hom.app (op x.base) x.fiber.as) :=
        (G.arrows.obj.map_id_apply _ _).trans
          (pointwiseArrow_pointwiseObjectInclusion_map G ((quotientStackTargetLeg G).map g))
      have r2 : pointwiseArrow G (vertHom G x.base x.fiber.as rfl rfl) = x.fiber.as :=
        pointwiseArrow_vertHom G _ _ _ _
      have w1 : G.source.hom.app (op x.base) (G.arrows.obj.map g.base.op x'.fiber.as) =
          G.target.hom.app (op x.base) (G.toGroupoidInFunctors.identity (op x.base)
            (G.source.hom.app (op x.base) x.fiber.as)) := by
        rw [← hx]
        exact (target_identity G _ _).symm
      have w2 : G.source.hom.app (op x.base) (G.toGroupoidInFunctors.identity (op x.base)
            (G.target.hom.app (op x.base) x.fiber.as)) = G.target.hom.app (op x.base) x.fiber.as :=
        source_identity G _ _
      refine (compose_congr' G _ _ w1 l1
        (pointwiseArrow_pointwiseObjectInclusion_map G ((quotientStackSourceLeg G).map g))).trans ?_
      refine Eq.trans ?_ (compose_congr' G _ _ w2 r1 r2).symm
      refine (compose_identity_right G _ _ (by rw [← hx]) _).trans ?_
      exact hx.symm.trans (compose_identity_left G _ _ rfl _).symm

variable (G) in
/-- Each component of `pointwiseTwoArrow G` lies over an identity morphism. -/
theorem pointwiseTwoArrow_isHomLift (x : (fibredCategory C S hS G.arrows.obj).val.obj) :
    (presheafOfGroupoids (evaluationGroupoidFunctor G.toGroupoidInFunctors)).p.IsHomLift
      (𝟙 ((fibredCategory C S hS G.arrows.obj).val.p.obj x)) ((pointwiseTwoArrow G).app x) :=
  IsHomLift.of_fac _ _ _ rfl rfl (by simp; rfl)

variable (G) in
/-- The composite `𝒮_R ⟶ 𝒮_U ⟶ [U/_pR]` through the source commutes with the projections to
`BigFppfOver C S hS`. -/
theorem sourceLeg_comp_p :
    (quotientStackSourceLeg G ⋙ pointwiseObjectInclusion G) ⋙
        (presheafOfGroupoids (evaluationGroupoidFunctor G.toGroupoidInFunctors)).p =
      (fibredCategory C S hS G.arrows.obj).val.p :=
  (associatedMap C S hS G.source.hom).1.hom.w

variable (G) in
/-- The composite `𝒮_R ⟶ 𝒮_U ⟶ [U/_pR]` through the target commutes with the projections to
`BigFppfOver C S hS`. -/
theorem targetLeg_comp_p :
    (quotientStackTargetLeg G ⋙ pointwiseObjectInclusion G) ⋙
        (presheafOfGroupoids (evaluationGroupoidFunctor G.toGroupoidInFunctors)).p =
      (fibredCategory C S hS G.arrows.obj).val.p :=
  (associatedMap C S hS G.target.hom).1.hom.w

variable (G) in
/-- The underlying abelian presheaf of `t^*` of the restriction of `N` to the object space is that
of `N` composed with `𝒮_R ⟶ 𝒮_U ⟶ [U/_pR]` through the target. -/
theorem targetPullback_objectRestriction_presheaf (N : SheafOfModules.{u} (pointwiseRing G)) :
    ((targetPullback G).obj ((objectRestriction G).obj N)).val.presheaf =
      (quotientStackTargetLeg G ⋙ pointwiseObjectInclusion G).op ⋙ N.val.presheaf := by
  rw [modulePullback_obj_val_presheaf, modulePullback_obj_val_presheaf]
  rfl

variable (G) in
/-- The underlying abelian presheaf of `s^*` of the restriction of `N` to the object space is that
of `N` composed with `𝒮_R ⟶ 𝒮_U ⟶ [U/_pR]` through the source. -/
theorem sourcePullback_objectRestriction_presheaf (N : SheafOfModules.{u} (pointwiseRing G)) :
    ((sourcePullback G).obj ((objectRestriction G).obj N)).val.presheaf =
      (quotientStackSourceLeg G ⋙ pointwiseObjectInclusion G).op ⋙ N.val.presheaf := by
  rw [modulePullback_obj_val_presheaf, modulePullback_obj_val_presheaf]
  rfl

variable (G) in
/-- The module-level comparison of Stacks 06TM attached to the canonical 2-arrow, between the
inverse images along the two composites `𝒮_R ⟶ 𝒮_U ⟶ [U/_pR]`. -/
def pointwiseTwoArrowIso :
    modulePullback C S hS (fibredCategory C S hS G.arrows.obj).val.p
        (presheafOfGroupoids (evaluationGroupoidFunctor G.toGroupoidInFunctors)).p
        (fibredCategory C S hS G.arrows.obj).property (isFiberedInGroupoids_presheafOfGroupoids _)
        (quotientStackTargetLeg G ⋙ pointwiseObjectInclusion G) (targetLeg_comp_p G)
        C.topology le_rfl ≅
      modulePullback C S hS (fibredCategory C S hS G.arrows.obj).val.p
        (presheafOfGroupoids (evaluationGroupoidFunctor G.toGroupoidInFunctors)).p
        (fibredCategory C S hS G.arrows.obj).property (isFiberedInGroupoids_presheafOfGroupoids _)
        (quotientStackSourceLeg G ⋙ pointwiseObjectInclusion G) (sourceLeg_comp_p G)
        C.topology le_rfl :=
  modulePullbackTwoMorphismIso C S hS (fibredCategory C S hS G.arrows.obj).val.p
    (presheafOfGroupoids (evaluationGroupoidFunctor G.toGroupoidInFunctors)).p
    (fibredCategory C S hS G.arrows.obj).property (isFiberedInGroupoids_presheafOfGroupoids _)
    (sourceLeg_comp_p G) (targetLeg_comp_p G) (pointwiseTwoArrow G)
    (pointwiseTwoArrow_isHomLift G) C.topology le_rfl

/-- A functor `f` between categories fibred in groupoids over `BigFppfOver C S hS` commuting with
the projections is continuous for the two associated fppf topologies. -/
theorem isContinuous_associatedTopology {𝒳 : Type*} [Category 𝒳] {𝒴 : Type*} [Category 𝒴]
    (p : 𝒳 ⥤ BigFppfOver C S hS) (q : 𝒴 ⥤ BigFppfOver C S hS) (hp : p.IsFiberedInGroupoids)
    (hq : q.IsFiberedInGroupoids) (f : 𝒳 ⥤ 𝒴) (hf : f ⋙ q = p) :
    f.IsContinuous (associatedTopology C S hS p C.topology)
      (associatedTopology C S hS q C.topology) := by
  exact (isContinuous_and_isCocontinuous_associatedTopology p q hp hq f hf).1

variable (G) in
/-- Restricting to the object space and then pulling back along the target is pulling back along
the composite. -/
def objectRestrictionTargetIso :
    objectRestriction G ⋙ targetPullback G ≅
      modulePullback C S hS (fibredCategory C S hS G.arrows.obj).val.p
        (presheafOfGroupoids (evaluationGroupoidFunctor G.toGroupoidInFunctors)).p
        (fibredCategory C S hS G.arrows.obj).property (isFiberedInGroupoids_presheafOfGroupoids _)
        (quotientStackTargetLeg G ⋙ pointwiseObjectInclusion G) (targetLeg_comp_p G)
        C.topology le_rfl := by
  haveI := isContinuous_associatedTopology _ _ (fibredCategory C S hS G.arrows.obj).property
    (fibredCategory C S hS G.objects.obj).property (quotientStackTargetLeg G)
    (associatedMap C S hS G.target.hom).1.hom.w
  haveI := isContinuous_associatedTopology _ _ (fibredCategory C S hS G.objects.obj).property
    (isFiberedInGroupoids_presheafOfGroupoids _) (pointwiseObjectInclusion G)
    (pointwiseObjectInclusion_comp_p G)
  haveI := isContinuous_associatedTopology _ _ (fibredCategory C S hS G.arrows.obj).property
    (isFiberedInGroupoids_presheafOfGroupoids _)
    (quotientStackTargetLeg G ⋙ pointwiseObjectInclusion G) (targetLeg_comp_p G)
  refine SheafOfModules.pushforwardComp _ _ ≪≫ SheafOfModules.pushforwardCongr ?_
  apply Sheaf.hom_ext
  ext X c
  simp
  rfl

variable (G) in
/-- Restricting to the object space and then pulling back along the source is pulling back along
the composite. -/
def objectRestrictionSourceIso :
    objectRestriction G ⋙ sourcePullback G ≅
      modulePullback C S hS (fibredCategory C S hS G.arrows.obj).val.p
        (presheafOfGroupoids (evaluationGroupoidFunctor G.toGroupoidInFunctors)).p
        (fibredCategory C S hS G.arrows.obj).property (isFiberedInGroupoids_presheafOfGroupoids _)
        (quotientStackSourceLeg G ⋙ pointwiseObjectInclusion G) (sourceLeg_comp_p G)
        C.topology le_rfl := by
  haveI := isContinuous_associatedTopology _ _ (fibredCategory C S hS G.arrows.obj).property
    (fibredCategory C S hS G.objects.obj).property (quotientStackSourceLeg G)
    (associatedMap C S hS G.source.hom).1.hom.w
  haveI := isContinuous_associatedTopology _ _ (fibredCategory C S hS G.objects.obj).property
    (isFiberedInGroupoids_presheafOfGroupoids _) (pointwiseObjectInclusion G)
    (pointwiseObjectInclusion_comp_p G)
  haveI := isContinuous_associatedTopology _ _ (fibredCategory C S hS G.arrows.obj).property
    (isFiberedInGroupoids_presheafOfGroupoids _)
    (quotientStackSourceLeg G ⋙ pointwiseObjectInclusion G) (sourceLeg_comp_p G)
  refine SheafOfModules.pushforwardComp _ _ ≪≫ SheafOfModules.pushforwardCongr ?_
  apply Sheaf.hom_ext
  ext X c
  simp
  rfl

variable (G) in
/-- The descent morphism of the restriction of a module on the pointwise groupoid fibration to
the object space: the module-level comparison of Stacks 06TM attached to the canonical
2-arrow. -/
def restrictionTransition (N : SheafOfModules.{u} (pointwiseRing G)) :
    (targetPullback G).obj ((objectRestriction G).obj N) ⟶
      (sourcePullback G).obj ((objectRestriction G).obj N) :=
  (objectRestrictionTargetIso G).hom.app N ≫ (pointwiseTwoArrowIso G).hom.app N ≫
    (objectRestrictionSourceIso G).inv.app N

/-- The components of `objectRestrictionTargetIso G` act as the identity on sections. -/
theorem objectRestrictionTargetIso_hom_app_val_app (N : SheafOfModules.{u} (pointwiseRing G))
    (X) (m) : ((objectRestrictionTargetIso G).hom.app N).val.app X m = m := rfl

/-- The components of the inverse of `objectRestrictionSourceIso G` act as the identity on
sections. -/
theorem objectRestrictionSourceIso_inv_app_val_app (N : SheafOfModules.{u} (pointwiseRing G))
    (X) (m) : ((objectRestrictionSourceIso G).inv.app N).val.app X m = m := rfl

/-- The underlying morphism of abelian presheaves of a component of `objectRestrictionTargetIso G`
is the identity at every object. -/
theorem objectRestrictionTargetIso_hom_app (N : SheafOfModules.{u} (pointwiseRing G)) (X) :
    ((PresheafOfModules.toPresheaf (arrRing G).obj).map
      ((objectRestrictionTargetIso G).hom.app N).val).app X = 𝟙 _ := rfl

/-- The underlying morphism of abelian presheaves of a component of the inverse of
`objectRestrictionSourceIso G` is the identity at every object. -/
theorem objectRestrictionSourceIso_inv_app (N : SheafOfModules.{u} (pointwiseRing G)) (X) :
    ((PresheafOfModules.toPresheaf (arrRing G).obj).map
      ((objectRestrictionSourceIso G).inv.app N).val).app X = 𝟙 _ := rfl

/-- At an object `X` of the category of the arrow space, the underlying morphism of abelian
groups of a component of `pointwiseTwoArrowIso G` is the restriction map of `N` along the
component of `pointwiseTwoArrow G` at `X`. -/
theorem pointwiseTwoArrowIso_hom_app (N : SheafOfModules.{u} (pointwiseRing G)) (X) :
    ((PresheafOfModules.toPresheaf (arrRing G).obj).map
      ((pointwiseTwoArrowIso G).hom.app N).val).app X =
      N.val.presheaf.map ((pointwiseTwoArrow G).app X.unop).op := rfl

/-- The component of `restrictionTransition G N` at a `T`-point `r` of `R` sends a section `m` to
its restriction along the morphism `(T, s(r)) ⟶ (T, t(r))` with arrow `r`. -/
theorem descComp_restrictionTransition_apply (N : SheafOfModules.{u} (pointwiseRing G))
    (T : BigFppfOver C S hS) (r : G.arrows.obj.obj (op T))
    (m : N.val.presheaf.obj (op ⟨T, G.target.hom.app (op T) r⟩)) :
    descComp (restrictionTransition G N) T r m = N.val.presheaf.map (vertHom G T r rfl rfl).op m :=
  rfl

/-- The component of `restrictionTransition G N` at a `T`-point `r` of `R` is the restriction map
of `N` along the morphism `(T, s(r)) ⟶ (T, t(r))` with arrow `r`. -/
theorem descComp_restrictionTransition (N : SheafOfModules.{u} (pointwiseRing G))
    (T : BigFppfOver C S hS) (r : G.arrows.obj.obj (op T)) :
    descComp (restrictionTransition G N) T r = N.val.presheaf.map (vertHom G T r rfl rfl).op :=
  AddCommGrpCat.ext fun m => descComp_restrictionTransition_apply N T r m

/-- The restriction maps of the restriction of `N` to the object space are those of `N` along the
image morphisms in the pointwise groupoid fibration. -/
theorem objectRestriction_map (N : SheafOfModules.{u} (pointwiseRing G)) {X Y : ObjFib G}
    (g : X ⟶ Y) :
    ((objectRestriction G).obj N).val.presheaf.map g.op =
      N.val.presheaf.map ((pointwiseObjectInclusion G).map g).op := rfl

/-- Transport in the restriction of `N` to the object space is the restriction map of `N` along
the corresponding `eqToHom` of the pointwise groupoid fibration. -/
theorem ptTransport_objectRestriction (N : SheafOfModules.{u} (pointwiseRing G))
    {T : BigFppfOver C S hS} {a a' : G.objects.obj.obj (op T)} (h : a = a') :
    ptTransport ((objectRestriction G).obj N) h =
      N.val.presheaf.map (eqToHom (congrArg (fun z => (⟨T, z⟩ : PointwiseFibration G)) h)).op := by
  unfold ptTransport
  rw [objectRestriction_map, eqToHom_map]
  rfl

namespace PointwiseDescentDatum

/-- A morphism of descent data: a morphism of the underlying modules commuting with the descent
morphisms. -/
@[ext]
structure Hom (D D' : PointwiseDescentDatum G) where
  /-- The underlying morphism of modules on the object space. -/
  hom : D.M ⟶ D'.M
  /-- Compatibility with the descent morphisms. -/
  comm : D.β ≫ (sourcePullback G).map hom = (targetPullback G).map hom ≫ D'.β

/-- The category of descent data on the object space of `G`. -/
instance : Category (PointwiseDescentDatum G) where
  Hom := Hom
  id D := ⟨𝟙 D.M, by simp⟩
  comp f g := ⟨f.hom ≫ g.hom, by
    rw [Functor.map_comp, Functor.map_comp, ← Category.assoc, f.comm, Category.assoc, g.comm,
      ← Category.assoc]⟩
  id_comp f := Hom.ext (Category.id_comp _)
  comp_id f := Hom.ext (Category.comp_id _)
  assoc f g h := Hom.ext (Category.assoc _ _ _)

/-- The underlying morphism of modules of the identity of a descent datum is the identity. -/
@[simp]
theorem id_hom (D : PointwiseDescentDatum G) : Hom.hom (𝟙 D) = 𝟙 D.M := rfl

/-- The underlying morphism of modules of a composite is the composite of the underlying
morphisms. -/
@[simp]
theorem comp_hom {D D' D'' : PointwiseDescentDatum G} (f : D ⟶ D') (g : D' ⟶ D'') :
    Hom.hom (f ≫ g) = f.hom ≫ g.hom := rfl

/-- Two morphisms of descent data with the same underlying morphism of modules are equal. -/
@[ext]
theorem hom_ext {D D' : PointwiseDescentDatum G} {f g : D ⟶ D'} (h : f.hom = g.hom) : f = g :=
  Hom.ext h

/-- The forgetful functor to modules on the object space. -/
@[simps]
def forget : PointwiseDescentDatum G ⥤ SheafOfModules.{u} (objRing G) where
  obj D := D.M
  map f := f.hom

variable (G) in
/-- The descent data whose underlying module is quasi-coherent on the object space
(Stacks 06WG). -/
abbrev qcoh : ObjectProperty (PointwiseDescentDatum G) := fun D => D.M.IsQuasicoherentOnSite

end PointwiseDescentDatum

end AlgebraicGeometry.Stack

end
