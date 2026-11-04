module

public import StacksFrontier.AlgebraicGeometry.Descent.BigHRingSheafSystemOpens
public import StacksFrontier.Topology.Sheaves.Modules.ModuleGlueing.Basic

/-!
# Gluing a descent datum along a family of opens, for a system of sheaves of rings
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace AlgebraicGeometry.BigHOver.RingSheafSystem

universe u

variable {B : BigHSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {𝓡 : RingSheafSystem B S hS}
  {U : BigHOver B S hS} {ι : Type u} {W : ι → ((toScheme B S hS).obj U).Opens}
  (D : 𝓡.modulePseudofunctor.DescentData (fun i => opensι B S hS (W i)))

/-- The gluing morphisms of a descent datum along a family of opens are compatible with passing
to a smaller open. -/
lemma hom_restrict {P P' : ((toScheme B S hS).obj U).Opens} (hP' : P' ≤ P) (i j : ι)
    (hi : P ≤ W i) (hj : P ≤ W j) :
    D.hom (opensι B S hS P') (opensHom B S hS (hP'.trans hi)) (opensHom B S hS (hP'.trans hj))
        (opensHom_opensι B S hS _) (opensHom_opensι B S hS _) =
      𝓡.compHom (opensHom B S hS hi) (opensHom B S hS hP') (opensHom B S hS (hP'.trans hi))
          (opensHom_comp_opensHom hP' hi) (D.obj i) ≫
        (𝓡.pull (opensHom B S hS hP').op).map (D.hom (opensι B S hS P) (opensHom B S hS hi)
          (opensHom B S hS hj) (opensHom_opensι B S hS hi) (opensHom_opensι B S hS hj)) ≫
        𝓡.compInv (opensHom B S hS hj) (opensHom B S hS hP') (opensHom B S hS (hP'.trans hj))
          (opensHom_comp_opensHom hP' hj) (D.obj j) :=
  𝓡.eq_compHom_of_pullHom_eq _ _ _ _ _ _ _ _ _
    (D.pullHom_hom (opensHom B S hS hP') (opensι B S hS P) (opensι B S hS P')
      (opensHom_opensι B S hS hP') (opensHom B S hS hi) (opensHom B S hS hj)
      (opensHom_opensι B S hS hi) (opensHom_opensι B S hS hj) _ _
      (opensHom_comp_opensHom hP' hi) (opensHom_comp_opensHom hP' hj))

/-- The `i`-th component of a descent datum along a family of opens, typed as a sheaf of
modules. -/
def dobj (i : ι) : SheafOfModules.{u} (𝓡.ring (opensObj B S hS (W i))) := D.obj i

/-- The gluing morphism of a descent datum along a family of opens over an open `P` contained in
two members, typed through extension of scalars. -/
def dhom {P : ((toScheme B S hS).obj U).Opens} (i j : ι) (hi : P ≤ W i) (hj : P ≤ W j) :
    (𝓡.pull (opensHom B S hS hi).op).obj (dobj D i) ⟶
      (𝓡.pull (opensHom B S hS hj).op).obj (dobj D j) :=
  D.hom (opensι B S hS P) (opensHom B S hS hi) (opensHom B S hS hj)
    (opensHom_opensι B S hS hi) (opensHom_opensι B S hS hj)

/-- The gluing morphisms of a descent datum along a family of opens are compatible with passing
to a smaller open, typed through extension of scalars. -/
lemma dhom_restrict {P P' : ((toScheme B S hS).obj U).Opens} (hP' : P' ≤ P) (i j : ι)
    (hi : P ≤ W i) (hj : P ≤ W j) :
    dhom D i j (hP'.trans hi) (hP'.trans hj) =
      𝓡.compHom (opensHom B S hS hi) (opensHom B S hS hP') (opensHom B S hS (hP'.trans hi))
          (opensHom_comp_opensHom hP' hi) (dobj D i) ≫
        (𝓡.pull (opensHom B S hS hP').op).map (dhom D i j hi hj) ≫
        𝓡.compInv (opensHom B S hS hj) (opensHom B S hS hP') (opensHom B S hS (hP'.trans hj))
          (opensHom_comp_opensHom hP' hj) (dobj D j) :=
  𝓡.eq_compHom_of_pullHom_eq _ _ _ _ _ _ _ (dhom D i j hi hj) _
    (D.pullHom_hom (opensHom B S hS hP') (opensι B S hS P) (opensι B S hS P')
      (opensHom_opensι B S hS hP') (opensHom B S hS hi) (opensHom B S hS hj)
      (opensHom_opensι B S hS hi) (opensHom_opensι B S hS hj) _ _
      (opensHom_comp_opensHom hP' hi) (opensHom_comp_opensHom hP' hj))

/-- The comparison, for opens `P' ≤ P ≤ W i`, between the pushforwards from `P` and from `P'`
of the restrictions of the `i`-th component of a descent datum. -/
abbrev rho (i : ι) {P P' : ((toScheme B S hS).obj U).Opens} (hP' : P' ≤ P) (hi : P ≤ W i) :
    (𝓡.push (opensι B S hS P)).obj ((𝓡.pull (opensHom B S hS hi).op).obj (dobj D i)) ⟶
      (𝓡.push (opensι B S hS P')).obj
        ((𝓡.pull (opensHom B S hS (hP'.trans hi)).op).obj (dobj D i)) :=
  𝓡.rhoG (opensHom B S hS hi) (opensHom B S hS hP') (opensHom B S hS (hP'.trans hi))
    (opensHom_comp_opensHom hP' hi) (opensι B S hS P) (opensι B S hS P')
    (opensHom_opensι B S hS hP') (dobj D i)

/-- **The comparison between nested opens intertwines the gluing morphisms.** -/
lemma push_map_hom_rho {P P' : ((toScheme B S hS).obj U).Opens} (hP' : P' ≤ P) (i j : ι)
    (hi : P ≤ W i) (hj : P ≤ W j) :
    (𝓡.push (opensι B S hS P)).map (dhom D i j hi hj) ≫
        𝓡.rhoG (opensHom B S hS hj) (opensHom B S hS hP') (opensHom B S hS (hP'.trans hj))
          (opensHom_comp_opensHom hP' hj) (opensι B S hS P) (opensι B S hS P')
          (opensHom_opensι B S hS hP') (dobj D j) =
      𝓡.rhoG (opensHom B S hS hi) (opensHom B S hS hP') (opensHom B S hS (hP'.trans hi))
          (opensHom_comp_opensHom hP' hi) (opensι B S hS P) (opensι B S hS P')
          (opensHom_opensι B S hS hP') (dobj D i) ≫
        (𝓡.push (opensι B S hS P')).map (dhom D i j (hP'.trans hi) (hP'.trans hj)) := by
  have key := 𝓡.push_map_rhoG (opensHom B S hS hi) (opensHom B S hS hj) (opensHom B S hS hP')
    (opensHom B S hS (hP'.trans hi)) (opensHom B S hS (hP'.trans hj))
    (opensHom_comp_opensHom hP' hi) (opensHom_comp_opensHom hP' hj) (opensι B S hS P)
    (opensι B S hS P') (opensHom_opensι B S hS hP') (dhom D i j hi hj)
  rwa [← dhom_restrict D hP' i j hi hj] at key

/-- The cocycle condition for the gluing morphisms over an open. -/
lemma dhom_comp {P : ((toScheme B S hS).obj U).Opens} (i j k : ι) (hi : P ≤ W i)
    (hj : P ≤ W j) (hk : P ≤ W k) :
    dhom D i j hi hj ≫ dhom D j k hj hk = dhom D i k hi hk :=
  (𝓡.modulePseudofunctor_comp _ _).symm.trans (D.hom_comp _ _ _ _ _ _ _)

/-- The gluing morphism from a member to itself is the identity. -/
lemma dhom_self {P : ((toScheme B S hS).obj U).Opens} (i : ι) (hi : P ≤ W i) :
    dhom D i i hi hi = 𝟙 _ :=
  D.hom_self _ _ (opensHom_opensι B S hS hi)

/-- The gluing morphism over an open is an isomorphism, with inverse the gluing morphism in the
opposite direction. -/
instance {P : ((toScheme B S hS).obj U).Opens} (i j : ι) (hi : P ≤ W i) (hj : P ≤ W j) :
    IsIso (dhom D i j hi hj) :=
  ⟨⟨dhom D j i hj hi, (dhom_comp D i j i hi hj hi).trans (dhom_self D i hi),
    (dhom_comp D j i j hj hi hj).trans (dhom_self D j hj)⟩⟩

/-- The `i`-th member of a descent datum along a family of opens, pushed forward to the ambient
object. -/
abbrev member (i : ι) : SheafOfModules.{u} (𝓡.ring U) :=
  (𝓡.push (opensι B S hS (W i))).obj (dobj D i)

/-- The comparison of the `i`-th member with the pushforward from an open `P ≤ W i` of the
restriction of the `j`-th component, through the gluing morphism over `P`. -/
def glueMap (i j : ι) {P : ((toScheme B S hS).obj U).Opens} (hi : P ≤ W i) (hj : P ≤ W j) :
    (𝓡.push (opensι B S hS (W i))).obj (dobj D i) ⟶
      (𝓡.push (opensι B S hS P)).obj ((𝓡.pull (opensHom B S hS hj).op).obj (dobj D j)) :=
  𝓡.etaG (opensHom B S hS hi) (opensι B S hS (W i)) (opensι B S hS P)
      (opensHom_opensι B S hS hi) (dobj D i) ≫
    (𝓡.push (opensι B S hS P)).map (dhom D i j hi hj)

/-- The comparison of a member with itself through an open `P ≤ W j` is the unit comparison
`AlgebraicGeometry.BigHOver.RingSheafSystem.etaG`, since the gluing morphism is the identity. -/
lemma glueMap_self (j : ι) {P : ((toScheme B S hS).obj U).Opens} (hj : P ≤ W j) :
    glueMap D j j hj hj = 𝓡.etaG (opensHom B S hS hj) (opensι B S hS (W j)) (opensι B S hS P)
      (opensHom_opensι B S hS hj) (dobj D j) := by
  rw [glueMap, dhom_self, CategoryTheory.Functor.map_id, Category.comp_id]

variable {D}

/-- If the units of `𝓡` are bijective, the comparison map
`AlgebraicGeometry.BigHOver.RingSheafSystem.glueMap` is bijective on sections over every open
`V ≤ P`. -/
lemma bijective_glueMap (h𝓡 : 𝓡.UnitBijective) (i j : ι) {P : ((toScheme B S hS).obj U).Opens}
    (hi : P ≤ W i) (hj : P ≤ W j) (V : ((toScheme B S hS).obj U).Opens) (hV : V ≤ P) :
    Function.Bijective ((glueMap D i j hi hj).val.app (op V)) := by
  rw [glueMap, coe_app_comp]
  exact (bijective_app_of_isIso _ _).comp (bijective_etaG_opensHom h𝓡 hi (dobj D i) V hV)

/-- **The comparison maps between nested opens.** For `P' ≤ P`, the comparison over `P'` is the
comparison over `P` followed by the comparison of pushforwards from `P` and `P'`. -/
lemma glueMap_comp_rhoG (i j : ι) {P P' : ((toScheme B S hS).obj U).Opens} (hP' : P' ≤ P)
    (hi : P ≤ W i) (hj : P ≤ W j) :
    glueMap D i j hi hj ≫ 𝓡.rhoG (opensHom B S hS hj) (opensHom B S hS hP')
        (opensHom B S hS (hP'.trans hj)) (opensHom_comp_opensHom hP' hj) (opensι B S hS P)
        (opensι B S hS P') (opensHom_opensι B S hS hP') (dobj D j) =
      glueMap D i j (hP'.trans hi) (hP'.trans hj) := by
  rw [glueMap, Category.assoc, push_map_hom_rho D hP' i j hi hj, ← Category.assoc,
    𝓡.etaG_comp_rhoG (opensHom B S hS hi) (opensHom B S hS hP') (opensHom B S hS (hP'.trans hi))
      (opensHom_comp_opensHom hP' hi) (opensι B S hS (W i)) (opensι B S hS P) (opensι B S hS P')
      (opensHom_opensι B S hS hi) (opensHom_opensι B S hS _) (opensHom_opensι B S hS hP')]
  rfl

variable (D) in
/-- The comparison through `j` followed by the gluing morphism from `j` to `k` is the comparison
through `k`. -/
lemma glueMap_comp_dhom (i j k : ι) {P : ((toScheme B S hS).obj U).Opens} (hi : P ≤ W i)
    (hj : P ≤ W j) (hk : P ≤ W k) :
    glueMap D i j hi hj ≫ (𝓡.push (opensι B S hS P)).map (dhom D j k hj hk) =
      glueMap D i k hi hk := by
  rw [glueMap, glueMap, Category.assoc, ← Functor.map_comp, dhom_comp]

/-- The transition of the glueing datum over an open `V` contained in an open `P` below two
members: the unique section whose comparison with `P` agrees with the comparison through the
gluing morphism. -/
def transP (h𝓡 : 𝓡.UnitBijective) (i j : ι) {P : ((toScheme B S hS).obj U).Opens}
    (hi : P ≤ W i) (hj : P ≤ W j) (V : ((toScheme B S hS).obj U).Opens) (hV : V ≤ P) :
    ((member D i).val.obj (op V)) ≃ₗ[ToType ((𝓡.ring U).obj.obj (op V))]
      ((member D j).val.obj (op V)) :=
  (LinearEquiv.ofBijective ((glueMap D i j hi hj).val.app (op V)).hom
      (bijective_glueMap h𝓡 i j hi hj V hV)).trans
    (LinearEquiv.ofBijective ((glueMap D j j hj hj).val.app (op V)).hom
      (bijective_glueMap h𝓡 j j hj hj V hV)).symm

/-- The defining property of `AlgebraicGeometry.BigHOver.RingSheafSystem.transP`. -/
lemma glueMap_transP (h𝓡 : 𝓡.UnitBijective) (i j : ι) {P : ((toScheme B S hS).obj U).Opens}
    (hi : P ≤ W i) (hj : P ≤ W j) (V : ((toScheme B S hS).obj U).Opens) (hV : V ≤ P)
    (s : ToType ((member D i).val.obj (op V))) :
    (glueMap D j j hj hj).val.app (op V) (transP h𝓡 i j hi hj V hV s) =
      (glueMap D i j hi hj).val.app (op V) s :=
  (LinearEquiv.ofBijective ((glueMap D j j hj hj).val.app (op V)).hom
    (bijective_glueMap h𝓡 j j hj hj V hV)).apply_symm_apply _

/-- The transition over `V` does not depend on the open `P ⊇ V` it is computed through: shrinking
`P` to `P' ⊇ V` gives the same transition. -/
lemma transP_eq_of_le (h𝓡 : 𝓡.UnitBijective) (i j : ι) {P P' : ((toScheme B S hS).obj U).Opens}
    (hP' : P' ≤ P) (hi : P ≤ W i) (hj : P ≤ W j) (V : ((toScheme B S hS).obj U).Opens)
    (hV : V ≤ P') (s : ToType ((member D i).val.obj (op V))) :
    transP h𝓡 i j hi hj V (hV.trans hP') s =
      transP h𝓡 i j (hP'.trans hi) (hP'.trans hj) V hV s := by
  apply (bijective_glueMap h𝓡 j j (hP'.trans hj) (hP'.trans hj) V hV).1
  exact (app_comp_eq_of_app_eq _ (glueMap_comp_rhoG (D := D) i j hP' hi hj)
    (glueMap_comp_rhoG (D := D) j j hP' hj hj) s _
    (glueMap_transP h𝓡 i j hi hj V (hV.trans hP') s)).trans
    (glueMap_transP h𝓡 i j (hP'.trans hi) (hP'.trans hj) V hV s).symm

/-- The transition `AlgebraicGeometry.BigHOver.RingSheafSystem.transP` commutes with restriction
of sections from `V` to `V' ≤ V`. -/
lemma transP_naturality (h𝓡 : 𝓡.UnitBijective) (i j : ι) {P : ((toScheme B S hS).obj U).Opens}
    (hi : P ≤ W i) (hj : P ≤ W j) {V V' : ((toScheme B S hS).obj U).Opens} (hV : V ≤ P)
    (hV' : V' ≤ V) (s : ToType ((member D i).val.obj (op V))) :
    transP h𝓡 i j hi hj V' (hV'.trans hV) ((member D i).val.map (homOfLE hV').op s) =
      (member D j).val.map (homOfLE hV').op (transP h𝓡 i j hi hj V hV s) := by
  apply (bijective_glueMap h𝓡 j j hj hj V' (hV'.trans hV)).1
  exact (glueMap_transP h𝓡 i j hi hj V' (hV'.trans hV) _).trans
    ((PresheafOfModules.naturality_apply (glueMap D i j hi hj).val (homOfLE hV').op s).trans
      ((congrArg _ (glueMap_transP h𝓡 i j hi hj V hV s).symm).trans
        (PresheafOfModules.naturality_apply (glueMap D j j hj hj).val (homOfLE hV').op _).symm))

/-- The cocycle condition for the transitions over a common open `P`: the transition from `i` to
`j` followed by the one from `j` to `k` is the transition from `i` to `k`. -/
lemma transP_transP (h𝓡 : 𝓡.UnitBijective) (i j k : ι) {P : ((toScheme B S hS).obj U).Opens}
    (hi : P ≤ W i) (hj : P ≤ W j) (hk : P ≤ W k) (V : ((toScheme B S hS).obj U).Opens)
    (hV : V ≤ P) (s : ToType ((member D i).val.obj (op V))) :
    transP h𝓡 j k hj hk V hV (transP h𝓡 i j hi hj V hV s) = transP h𝓡 i k hi hk V hV s := by
  apply (bijective_glueMap h𝓡 k k hk hk V hV).1
  have e1 := coe_app_congr (glueMap_comp_dhom D j j k hj hj hk) (op V)
  have e2 := coe_app_congr (glueMap_comp_dhom D i j k hi hj hk) (op V)
  rw [coe_app_comp] at e1 e2
  rw [glueMap_transP, glueMap_transP, ← e1, ← e2, Function.comp_apply, Function.comp_apply,
    glueMap_transP]

variable (D) in
/-- The comparison of the glueing datum over an open `V` below two members: the transition
`AlgebraicGeometry.BigHOver.RingSheafSystem.transP` through their intersection. -/
def glueTrans (h𝓡 : 𝓡.UnitBijective) (i j : ι) {V : ((toScheme B S hS).obj U).Opens}
    (hi : V ≤ W i) (hj : V ≤ W j) :
    ((member D i).val.obj (op V)) ≃ₗ[ToType ((𝓡.ring U).obj.obj (op V))]
      ((member D j).val.obj (op V)) :=
  transP h𝓡 i j inf_le_left inf_le_right V (le_inf hi hj)

/-- The comparison `AlgebraicGeometry.BigHOver.RingSheafSystem.glueTrans` commutes with
restriction of sections from `V` to `V' ≤ V`. -/
lemma glueTrans_map (h𝓡 : 𝓡.UnitBijective) (i j : ι) {V V' : ((toScheme B S hS).obj U).Opens}
    (hi : V ≤ W i) (hj : V ≤ W j) (hV' : V' ≤ V) (s : ToType ((member D i).val.obj (op V))) :
    glueTrans D h𝓡 i j (hV'.trans hi) (hV'.trans hj) ((member D i).val.map (homOfLE hV').op s) =
      (member D j).val.map (homOfLE hV').op (glueTrans D h𝓡 i j hi hj s) :=
  transP_naturality h𝓡 i j inf_le_left inf_le_right (le_inf hi hj) hV' s

/-- The cocycle condition for the comparisons
`AlgebraicGeometry.BigHOver.RingSheafSystem.glueTrans`. -/
lemma glueTrans_trans (h𝓡 : 𝓡.UnitBijective) (i j k : ι) {V : ((toScheme B S hS).obj U).Opens}
    (hi : V ≤ W i) (hj : V ≤ W j) (hk : V ≤ W k) (s : ToType ((member D i).val.obj (op V))) :
    glueTrans D h𝓡 j k hj hk (glueTrans D h𝓡 i j hi hj s) = glueTrans D h𝓡 i k hi hk s := by
  simp only [glueTrans]
  rw [transP_eq_of_le h𝓡 i j (le_inf hi hj) inf_le_left inf_le_right V le_rfl,
    transP_eq_of_le h𝓡 j k (le_inf hj hk) inf_le_left inf_le_right V le_rfl,
    transP_eq_of_le h𝓡 i k (le_inf hi hk) inf_le_left inf_le_right V le_rfl]
  exact transP_transP h𝓡 i j k _ _ _ V le_rfl s

variable (D) in
/-- **The glueing datum of a descent datum along a family of opens**, in the sense of
Stacks 00AM: the members are the pushed-forward components, and the comparisons are
`AlgebraicGeometry.BigHOver.RingSheafSystem.glueTrans`. -/
noncomputable abbrev glueData (h𝓡 : 𝓡.UnitBijective) :
    Stacks.SheafOfModules.OModuleGlueData (𝓡.ring U) W :=
  Stacks.SheafOfModules.OModuleGlueData.ofModules (fun i => member D i)
    (fun i j _ hi hj => glueTrans D h𝓡 i j hi hj)
    (fun i j _ _ hi hj hV' s => glueTrans_map h𝓡 i j hi hj hV' s)
    (fun i j k _ hi hj hk s => glueTrans_trans h𝓡 i j k hi hj hk s)

end AlgebraicGeometry.BigHOver.RingSheafSystem
