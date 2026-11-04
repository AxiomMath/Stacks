module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposTwoIsoPullbackCoherence
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposTwoMorphismModulesMap
import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.SpacesEtaleModelPointTensorCocycle

/-!
# A pasting identity of pullbacks of sheaves of modules, read on direct images

Consider morphisms of ringed topoi forming the diagram

```
  E_n --x--> E_m
   |  \       |  \
  sc_n  d_n  sc_m  d_m
   v     \    v     \
  C_n --f--> C_m     T --e--> T_s --b--> Z
   \ g_n      \ g_m          ^
    `----------`-------------'
```

with a 2-morphism `τ : g_n ⟶ g_m ∘ f` (Stacks 04IC) and 2-isomorphisms `e ∘ d_k ≅ g_k ∘ sc_k`,
`b ∘ e ≅ a`, `a ∘ d_k ≅ a_k`, `f ∘ sc_n ≅ sc_m ∘ x` and `a_m ∘ x ≅ a_n`. For functors `R_k`
isomorphic to `g_k^*` and a transformation `t : R_m ⋙ f^* ⟶ R_n` which is the transition of `τ`
read through these isomorphisms, the two ways of comparing `sc_n^* f^* R_m b^*` with `a_n^*` agree
as soon as the corresponding identity of direct images holds on sheaves of sets.

## Main results

* `AlgebraicGeometry.RingedToposHom.pullbackModules_transitionPaste_eq`: the pasting identity.

## Implementation notes

The identity of pullbacks is reduced, by injectivity of conjugation of transformations between
left adjoints (`CategoryTheory.conjugateEquiv`), to the identity of direct images, which holds on
underlying sheaves of sets where both sides are composites of the given 2-cells.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Sheaves.RingedToposModules

-- The universe-polymorphic abelian structures on sheaves of modules, imported with
-- `CategoryTheory.Adjunction.comp_assoc_eq`, leave the universe constraints here stuck.
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

namespace AlgebraicGeometry.RingedToposHom

universe v u w

variable {En Em Cn Cm Ts T Zt : RingedTopos.{v, u, w}}
  [En.J.HasSheafCompose (forget RingCat.{w})] [Em.J.HasSheafCompose (forget RingCat.{w})]
  [Cn.J.HasSheafCompose (forget RingCat.{w})] [Cm.J.HasSheafCompose (forget RingCat.{w})]
  [Ts.J.HasSheafCompose (forget RingCat.{w})] [T.J.HasSheafCompose (forget RingCat.{w})]
  [Zt.J.HasSheafCompose (forget RingCat.{w})]
  [En.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Em.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Cn.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Cm.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Ts.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [T.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Zt.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [En.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Em.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Cn.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Cm.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Ts.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [T.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Zt.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [HasWeakSheafify En.J AddCommGrpCat.{w}] [En.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify Em.J AddCommGrpCat.{w}] [Em.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify Cn.J AddCommGrpCat.{w}] [Cn.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify Cm.J AddCommGrpCat.{w}] [Cm.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify Ts.J AddCommGrpCat.{w}] [Ts.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify T.J AddCommGrpCat.{w}] [T.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify Zt.J AddCommGrpCat.{w}] [Zt.J.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- The conjugate of the inverse of the pullback isomorphism of a 2-isomorphism is its
direct-image isomorphism. -/
theorem TwoIso.conjugateEquiv_pullbackModulesIso_inv {f g : RingedToposHom En Cn}
    (s : TwoIso f g) :
    conjugateEquiv (pullbackAdjPushforwardModules f) (pullbackAdjPushforwardModules g)
        s.pullbackModulesIso.inv = s.pushforwardModulesIso.hom := by
  have h := conjugateEquiv_comm (adj₁ := pullbackAdjPushforwardModules g)
    (adj₂ := pullbackAdjPushforwardModules f) s.pullbackModulesIso.inv_hom_id
  rw [TwoIso.conjugateEquiv_pullbackModulesIso_hom] at h
  exact (cancel_epi s.pushforwardModulesIso.inv).1
    (h.trans s.pushforwardModulesIso.inv_hom_id.symm)


omit [HasWeakSheafify Cn.J AddCommGrpCat.{w}] [Cn.J.WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- The conjugate of a 2-morphism's transformation of pullbacks is its transformation of direct
images. -/
theorem TwoMorphism.conjugateEquiv_pullbackAdj_pullbackModulesMap {f g : RingedToposHom En Cn}
    (t : TwoMorphism f g) :
    conjugateEquiv (pullbackAdjPushforwardModules f) (pullbackAdjPushforwardModules g)
        t.pullbackModulesMap = t.pushforwardModulesMap :=
  (conjugateEquiv _ _).apply_symm_apply _

/-- The degreewise comparison `g^* ⋙ sc^* ⟶ e^* ⋙ d^*` of a 2-isomorphism `e ∘ d ≅ g ∘ sc`,
as the mate of the corresponding comparison of direct images. -/
theorem pullbackModules_squareComparison_eq (sc : RingedToposHom En Cn)
    (g : RingedToposHom Cn Ts) (d : RingedToposHom En T) (e : RingedToposHom T Ts)
    (I : TwoIso (e.comp d) (g.comp sc)) :
    (pullbackModulesCompIso sc g).inv ≫ I.pullbackModulesIso.inv ≫
        (pullbackModulesCompIso d e).hom =
      (conjugateEquiv ((pullbackAdjPushforwardModules e).comp (pullbackAdjPushforwardModules d))
        ((pullbackAdjPushforwardModules g).comp (pullbackAdjPushforwardModules sc))).symm
        ((pushforwardModulesCompIso d e).inv ≫ I.pushforwardModulesIso.hom ≫
          (pushforwardModulesCompIso sc g).hom) := by
  rw [Equiv.eq_symm_apply, ← conjugateEquiv_comp _ (pullbackAdjPushforwardModules (g.comp sc)),
    ← conjugateEquiv_comp _ (pullbackAdjPushforwardModules (e.comp d)),
    conjugateEquiv_pullbackModulesCompIso_hom, TwoIso.conjugateEquiv_pullbackModulesIso_inv,
    conjugateEquiv_pullbackModulesCompIso_inv, Category.assoc]

/-- A 2-isomorphism `s : g ∘ f ≅ h` read as `g^* ⋙ f^* ⟶ h^*`, as a mate. -/
theorem pullbackModules_compTwoIso_eq (f : RingedToposHom En T) (g : RingedToposHom T Zt)
    (h : RingedToposHom En Zt) (s : TwoIso (g.comp f) h) :
    (pullbackModulesCompIso f g).inv ≫ s.pullbackModulesIso.hom =
      (conjugateEquiv (pullbackAdjPushforwardModules h)
        ((pullbackAdjPushforwardModules g).comp (pullbackAdjPushforwardModules f))).symm
        (s.pushforwardModulesIso.inv ≫ (pushforwardModulesCompIso f g).hom) := by
  rw [Equiv.eq_symm_apply, ← conjugateEquiv_comp _ (pullbackAdjPushforwardModules (g.comp f)),
    TwoIso.conjugateEquiv_pullbackModulesIso_hom, conjugateEquiv_pullbackModulesCompIso_inv]


/-- A 2-isomorphism `s : g ∘ sc ≅ e ∘ d` read as `g^* ⋙ sc^* ⟶ e^* ⋙ d^*`, as a mate. -/
theorem pullbackModules_squareComparison_hom_eq (sc : RingedToposHom En Cn)
    (g : RingedToposHom Cn Ts) (d : RingedToposHom En T) (e : RingedToposHom T Ts)
    (I : TwoIso (g.comp sc) (e.comp d)) :
    (pullbackModulesCompIso sc g).inv ≫ I.pullbackModulesIso.hom ≫
        (pullbackModulesCompIso d e).hom =
      (conjugateEquiv ((pullbackAdjPushforwardModules e).comp (pullbackAdjPushforwardModules d))
        ((pullbackAdjPushforwardModules g).comp (pullbackAdjPushforwardModules sc))).symm
        ((pushforwardModulesCompIso d e).inv ≫ I.pushforwardModulesIso.inv ≫
          (pushforwardModulesCompIso sc g).hom) := by
  rw [Equiv.eq_symm_apply, ← conjugateEquiv_comp _ (pullbackAdjPushforwardModules (g.comp sc)),
    ← conjugateEquiv_comp _ (pullbackAdjPushforwardModules (e.comp d)),
    conjugateEquiv_pullbackModulesCompIso_hom, TwoIso.conjugateEquiv_pullbackModulesIso_hom,
    conjugateEquiv_pullbackModulesCompIso_inv, Category.assoc]

omit [HasWeakSheafify Ts.J AddCommGrpCat.{w}] [Ts.J.WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- The transition `g_m^* ⋙ f^* ⟶ g_n^*` of a 2-morphism `τ : g_n ⟶ g_m ∘ f`, as a mate. -/
theorem pullbackModules_twoMorphismComp_eq (f : RingedToposHom En Cn) (g : RingedToposHom Cn Ts)
    (h : RingedToposHom En Ts) (τ : TwoMorphism h (g.comp f)) :
    (pullbackModulesCompIso f g).inv ≫ τ.pullbackModulesMap =
      (conjugateEquiv (pullbackAdjPushforwardModules h)
        ((pullbackAdjPushforwardModules g).comp (pullbackAdjPushforwardModules f))).symm
        (τ.pushforwardModulesMap ≫ (pushforwardModulesCompIso f g).hom) := by
  rw [Equiv.eq_symm_apply, ← conjugateEquiv_comp _ (pullbackAdjPushforwardModules (g.comp f)),
    TwoMorphism.conjugateEquiv_pullbackAdj_pullbackModulesMap,
    conjugateEquiv_pullbackModulesCompIso_inv]

/-- The comparison `b^* ⋙ g^* ⋙ sc^* ⟶ a^*` assembled from `e ∘ d ≅ g ∘ sc`, `b ∘ e ≅ aug` and
`aug ∘ d ≅ a`, as a mate. -/
theorem pullbackModules_degreeComparison_eq (sc : RingedToposHom En Cn)
    (g : RingedToposHom Cn Ts) (d : RingedToposHom En T) (e : RingedToposHom T Ts)
    (b : RingedToposHom Ts Zt) (aug : RingedToposHom T Zt) (a : RingedToposHom En Zt)
    (I : TwoIso (e.comp d) (g.comp sc)) (sA : TwoIso (b.comp e) aug) (sD : TwoIso (aug.comp d) a) :
    Functor.whiskerLeft b.toModulesHom.pullbackModules ((pullbackModulesCompIso sc g).inv ≫
        I.pullbackModulesIso.inv ≫ (pullbackModulesCompIso d e).hom) ≫
      Functor.whiskerRight ((pullbackModulesCompIso e b).inv ≫ sA.pullbackModulesIso.hom)
        d.toModulesHom.pullbackModules ≫
      (pullbackModulesCompIso d aug).inv ≫ sD.pullbackModulesIso.hom =
    (conjugateEquiv (pullbackAdjPushforwardModules a)
      ((pullbackAdjPushforwardModules b).comp
        ((pullbackAdjPushforwardModules g).comp (pullbackAdjPushforwardModules sc)))).symm
      ((sD.pushforwardModulesIso.inv ≫ (pushforwardModulesCompIso d aug).hom) ≫
        Functor.whiskerLeft (pushforwardModules d)
          (sA.pushforwardModulesIso.inv ≫ (pushforwardModulesCompIso e b).hom) ≫
        Functor.whiskerRight ((pushforwardModulesCompIso d e).inv ≫ I.pushforwardModulesIso.hom ≫
          (pushforwardModulesCompIso sc g).hom) (pushforwardModules b)) := by
  have h1 : Functor.whiskerLeft b.toModulesHom.pullbackModules ((pullbackModulesCompIso sc g).inv ≫
        I.pullbackModulesIso.inv ≫ (pullbackModulesCompIso d e).hom) =
      (conjugateEquiv ((pullbackAdjPushforwardModules b).comp
          ((pullbackAdjPushforwardModules e).comp (pullbackAdjPushforwardModules d)))
        ((pullbackAdjPushforwardModules b).comp
          ((pullbackAdjPushforwardModules g).comp (pullbackAdjPushforwardModules sc)))).symm
        (Functor.whiskerRight ((pushforwardModulesCompIso d e).inv ≫ I.pushforwardModulesIso.hom ≫
          (pushforwardModulesCompIso sc g).hom) (pushforwardModules b)) := by
    rw [pullbackModules_squareComparison_eq, Equiv.eq_symm_apply, conjugateEquiv_whiskerLeft,
      Equiv.apply_symm_apply]
  have h2 : Functor.whiskerRight ((pullbackModulesCompIso e b).inv ≫ sA.pullbackModulesIso.hom)
        d.toModulesHom.pullbackModules =
      (conjugateEquiv ((pullbackAdjPushforwardModules aug).comp (pullbackAdjPushforwardModules d))
        ((pullbackAdjPushforwardModules b).comp
          ((pullbackAdjPushforwardModules e).comp (pullbackAdjPushforwardModules d)))).symm
        (Functor.whiskerLeft (pushforwardModules d)
          (sA.pushforwardModulesIso.inv ≫ (pushforwardModulesCompIso e b).hom)) := by
    rw [pullbackModules_compTwoIso_eq, Equiv.eq_symm_apply,
      ← Adjunction.comp_assoc_eq, conjugateEquiv_whiskerRight, Equiv.apply_symm_apply]
  rw [h1, h2, pullbackModules_compTwoIso_eq d aug a sD, conjugateEquiv_symm_comp,
    conjugateEquiv_symm_comp, Category.assoc]


section Underlying

omit [HasWeakSheafify En.J AddCommGrpCat.{w}] [En.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify Em.J AddCommGrpCat.{w}] [Em.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify Cn.J AddCommGrpCat.{w}] [Cn.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify Ts.J AddCommGrpCat.{w}] [Ts.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify T.J AddCommGrpCat.{w}] [T.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify Zt.J AddCommGrpCat.{w}] [Zt.J.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- On underlying sheaves of sets, `s_*⁻¹` followed by the composition isomorphism is the inverse
of the 2-isomorphism `s : g ∘ f ≅ h`. -/
theorem moduleSheafFunctor_map_pushforwardModulesIso_inv_comp_compIso_hom_app
    (f : RingedToposHom En Cn) (g : RingedToposHom Cn Ts) (h : RingedToposHom En Ts)
    (s : TwoIso (g.comp f) h) (M : En.Modules) :
    (Sheaf.moduleSheafFunctor ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Ts.J)) Ts.O)).map
        ((s.pushforwardModulesIso.inv ≫ (pushforwardModulesCompIso f g).hom).app M) =
      s.e.inv.app
        (Sheaf.moduleSheaf ((Stacks.SheafOfModules.Tensor.ringSheaf (J := En.J)) En.O) M) :=
  Sheaf.hom_ext_sections fun _ _ ↦ rfl

/-- On underlying sheaves of sets, the direct-image comparison of `I : e ∘ d ≅ g ∘ sc` read
between composites, after `b_*`, is `b_*` of the 2-isomorphism. -/
theorem moduleSheafFunctor_map_pushforwardModules_map_squareComparison_app
    (sc : RingedToposHom En Cn) (g : RingedToposHom Cn Ts) (d : RingedToposHom En T)
    (e : RingedToposHom T Ts) (b : RingedToposHom Ts Zt) (I : TwoIso (e.comp d) (g.comp sc))
    (M : En.Modules) :
    (Sheaf.moduleSheafFunctor ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Zt.J)) Zt.O)).map
        ((pushforwardModules b).map (((pushforwardModulesCompIso d e).inv ≫
          I.pushforwardModulesIso.hom ≫ (pushforwardModulesCompIso sc g).hom).app M)) =
      b.toToposHom.pushforward.map
        (I.e.hom.app
          (Sheaf.moduleSheaf ((Stacks.SheafOfModules.Tensor.ringSheaf (J := En.J)) En.O) M)) :=
  Sheaf.hom_ext_sections fun _ _ ↦ rfl

/-- On underlying sheaves of sets, the direct-image transformation of `τ : h ⟶ g ∘ f` read into
the composite, after `b_*`, is `b_*` of the 2-morphism. -/
theorem moduleSheafFunctor_map_pushforwardModules_map_twoMorphismComp_app
    (f : RingedToposHom En Cn) (g : RingedToposHom Cn Ts) (h : RingedToposHom En Ts)
    (b : RingedToposHom Ts Zt) (τ : TwoMorphism h (g.comp f)) (M : En.Modules) :
    (Sheaf.moduleSheafFunctor ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Zt.J)) Zt.O)).map
        ((pushforwardModules b).map ((τ.pushforwardModulesMap ≫
          (pushforwardModulesCompIso f g).hom).app M)) =
      b.toToposHom.pushforward.map
        (τ.t.app
          (Sheaf.moduleSheaf ((Stacks.SheafOfModules.Tensor.ringSheaf (J := En.J)) En.O) M)) :=
  Sheaf.hom_ext_sections fun _ _ ↦ rfl

omit [T.J.HasSheafCompose (forget AddCommGrpCat.{w})] in
/-- On underlying sheaves of sets, the inverse direct-image comparison of `s : g ∘ sc ≅ e ∘ d`
read between composites, after `g'_*` and `b_*`, is `b_* g'_*` of the inverse of `s`. -/
theorem moduleSheafFunctor_map_pushforwardModules_comp_map_squareComparison_inv_app
    (sc : RingedToposHom En Cn) (g : RingedToposHom Cn Ts) (d : RingedToposHom En Em)
    (e : RingedToposHom Em Ts) (g' : RingedToposHom Ts T) (b : RingedToposHom T Zt)
    (s : TwoIso (g.comp sc) (e.comp d)) (M : En.Modules) :
    (Sheaf.moduleSheafFunctor ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Zt.J)) Zt.O)).map
        ((pushforwardModules g' ⋙ pushforwardModules b).map
          (((pushforwardModulesCompIso d e).inv ≫
            s.pushforwardModulesIso.inv ≫ (pushforwardModulesCompIso sc g).hom).app M)) =
      b.toToposHom.pushforward.map (g'.toToposHom.pushforward.map
        (s.e.inv.app
          (Sheaf.moduleSheaf ((Stacks.SheafOfModules.Tensor.ringSheaf (J := En.J)) En.O) M))) :=
  Sheaf.hom_ext_sections fun _ _ ↦ rfl

end Underlying

section Paste

variable (scn : RingedToposHom En Cn) (scm : RingedToposHom Em Cm) (gn : RingedToposHom Cn Ts)
  (gm : RingedToposHom Cm Ts) (f : RingedToposHom Cn Cm) (x : RingedToposHom En Em)
  (dn : RingedToposHom En T) (dm : RingedToposHom Em T) (e : RingedToposHom T Ts)
  (b : RingedToposHom Ts Zt) (aug : RingedToposHom T Zt) (an : RingedToposHom En Zt)
  (am : RingedToposHom Em Zt) (τ : TwoMorphism gn (gm.comp f))
  (In : TwoIso (e.comp dn) (gn.comp scn)) (Im : TwoIso (e.comp dm) (gm.comp scm))
  (sA : TwoIso (b.comp e) aug) (sDn : TwoIso (aug.comp dn) an) (sDm : TwoIso (aug.comp dm) am)
  (sT : TwoIso (f.comp scn) (scm.comp x)) (sX : TwoIso (am.comp x) an)

omit [Cm.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Ts.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Zt.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [HasWeakSheafify En.J AddCommGrpCat.{w}] [En.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify Em.J AddCommGrpCat.{w}] [Em.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify Cn.J AddCommGrpCat.{w}] [Cn.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify Cm.J AddCommGrpCat.{w}] [Cm.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify Ts.J AddCommGrpCat.{w}] [Ts.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify T.J AddCommGrpCat.{w}] [T.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify Zt.J AddCommGrpCat.{w}] [Zt.J.WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- The identity of direct images of sheaves of sets, at underlying sheaves of modules. -/
theorem transitionPaste_underlying
    (hS : ∀ G : Sheaf En.J (Type w),
      sDn.e.inv.app G ≫ sA.e.inv.app (dn.toToposHom.pushforward.obj G) ≫
          b.toToposHom.pushforward.map (In.e.hom.app G) ≫
          b.toToposHom.pushforward.map (τ.t.app (scn.toToposHom.pushforward.obj G)) =
        sX.e.inv.app G ≫ sDm.e.inv.app (x.toToposHom.pushforward.obj G) ≫
          sA.e.inv.app (dm.toToposHom.pushforward.obj (x.toToposHom.pushforward.obj G)) ≫
          b.toToposHom.pushforward.map (Im.e.hom.app (x.toToposHom.pushforward.obj G)) ≫
          b.toToposHom.pushforward.map (gm.toToposHom.pushforward.map (sT.e.inv.app G))) :
    ∀ M : En.Modules,
      sDn.e.inv.app
            (Sheaf.moduleSheaf ((Stacks.SheafOfModules.Tensor.ringSheaf (J := En.J)) En.O) M) ≫
          sA.e.inv.app (Sheaf.moduleSheaf ((Stacks.SheafOfModules.Tensor.ringSheaf (J := T.J)) T.O)
            (dn.pushforwardModules.obj M)) ≫
          b.toToposHom.pushforward.map (In.e.hom.app
            (Sheaf.moduleSheaf ((Stacks.SheafOfModules.Tensor.ringSheaf (J := En.J)) En.O) M)) ≫
          b.toToposHom.pushforward.map (τ.t.app
            (Sheaf.moduleSheaf ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Cn.J)) Cn.O)
              (scn.pushforwardModules.obj M))) =
        sX.e.inv.app
            (Sheaf.moduleSheaf ((Stacks.SheafOfModules.Tensor.ringSheaf (J := En.J)) En.O) M) ≫
          sDm.e.inv.app
            (Sheaf.moduleSheaf ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Em.J)) Em.O)
              (x.pushforwardModules.obj M)) ≫
          sA.e.inv.app (Sheaf.moduleSheaf ((Stacks.SheafOfModules.Tensor.ringSheaf (J := T.J)) T.O)
            (dm.pushforwardModules.obj (x.pushforwardModules.obj M))) ≫
          b.toToposHom.pushforward.map (Im.e.hom.app
            (Sheaf.moduleSheaf ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Em.J)) Em.O)
              (x.pushforwardModules.obj M))) ≫
          b.toToposHom.pushforward.map (gm.toToposHom.pushforward.map (sT.e.inv.app
            (Sheaf.moduleSheaf ((Stacks.SheafOfModules.Tensor.ringSheaf (J := En.J)) En.O) M))) :=
  fun _ ↦ hS _

omit [HasWeakSheafify En.J AddCommGrpCat.{w}] [En.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify Em.J AddCommGrpCat.{w}] [Em.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify Cn.J AddCommGrpCat.{w}] [Cn.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify Cm.J AddCommGrpCat.{w}] [Cm.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify Ts.J AddCommGrpCat.{w}] [Ts.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify T.J AddCommGrpCat.{w}] [T.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify Zt.J AddCommGrpCat.{w}] [Zt.J.WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- **The pasting identity on direct images of sheaves of modules**, from the corresponding
identity of direct images of sheaves of sets `hS`. -/
theorem pushforwardModules_transitionPaste_eq
    (hS : ∀ G : Sheaf En.J (Type w),
      sDn.e.inv.app G ≫ sA.e.inv.app (dn.toToposHom.pushforward.obj G) ≫
          b.toToposHom.pushforward.map (In.e.hom.app G) ≫
          b.toToposHom.pushforward.map (τ.t.app (scn.toToposHom.pushforward.obj G)) =
        sX.e.inv.app G ≫ sDm.e.inv.app (x.toToposHom.pushforward.obj G) ≫
          sA.e.inv.app (dm.toToposHom.pushforward.obj (x.toToposHom.pushforward.obj G)) ≫
          b.toToposHom.pushforward.map (Im.e.hom.app (x.toToposHom.pushforward.obj G)) ≫
          b.toToposHom.pushforward.map (gm.toToposHom.pushforward.map (sT.e.inv.app G))) :
    ((sDn.pushforwardModulesIso.inv ≫ (pushforwardModulesCompIso dn aug).hom) ≫
        Functor.whiskerLeft (pushforwardModules dn)
          (sA.pushforwardModulesIso.inv ≫ (pushforwardModulesCompIso e b).hom) ≫
        Functor.whiskerRight ((pushforwardModulesCompIso dn e).inv ≫ In.pushforwardModulesIso.hom ≫
          (pushforwardModulesCompIso scn gn).hom) (pushforwardModules b)) ≫
      Functor.whiskerRight (Functor.whiskerLeft (pushforwardModules scn)
        (τ.pushforwardModulesMap ≫ (pushforwardModulesCompIso f gm).hom)) (pushforwardModules b) =
    ((sX.pushforwardModulesIso.inv ≫ (pushforwardModulesCompIso x am).hom) ≫
      Functor.whiskerLeft (pushforwardModules x)
        ((sDm.pushforwardModulesIso.inv ≫ (pushforwardModulesCompIso dm aug).hom) ≫
          Functor.whiskerLeft (pushforwardModules dm)
            (sA.pushforwardModulesIso.inv ≫ (pushforwardModulesCompIso e b).hom) ≫
          Functor.whiskerRight ((pushforwardModulesCompIso dm e).inv ≫
            Im.pushforwardModulesIso.hom ≫ (pushforwardModulesCompIso scm gm).hom)
            (pushforwardModules b))) ≫
      Functor.whiskerRight ((pushforwardModulesCompIso x scm).inv ≫ sT.pushforwardModulesIso.inv ≫
        (pushforwardModulesCompIso scn f).hom) (pushforwardModules gm ⋙ pushforwardModules b) := by
  generalize hνn : sDn.pushforwardModulesIso.inv ≫ (pushforwardModulesCompIso dn aug).hom = νn
  generalize hε : sA.pushforwardModulesIso.inv ≫ (pushforwardModulesCompIso e b).hom = ε
  generalize hρn : (pushforwardModulesCompIso dn e).inv ≫ In.pushforwardModulesIso.hom ≫
    (pushforwardModulesCompIso scn gn).hom = ρn
  generalize hμ : τ.pushforwardModulesMap ≫ (pushforwardModulesCompIso f gm).hom = μ
  generalize hθ : sX.pushforwardModulesIso.inv ≫ (pushforwardModulesCompIso x am).hom = θ
  generalize hνm : sDm.pushforwardModulesIso.inv ≫ (pushforwardModulesCompIso dm aug).hom = νm
  generalize hρm : (pushforwardModulesCompIso dm e).inv ≫ Im.pushforwardModulesIso.hom ≫
    (pushforwardModulesCompIso scm gm).hom = ρm
  generalize hβ : (pushforwardModulesCompIso x scm).inv ≫ sT.pushforwardModulesIso.inv ≫
    (pushforwardModulesCompIso scn f).hom = β
  refine NatTrans.ext (funext fun M => hom_ext_moduleSheafFunctor ?_)
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.map_comp, Category.assoc]
  subst hνn hε hρn hμ hθ hνm hρm hβ
  simp only [moduleSheafFunctor_map_pushforwardModules_comp_map_squareComparison_inv_app,
    moduleSheafFunctor_map_pushforwardModulesIso_inv_comp_compIso_hom_app,
    moduleSheafFunctor_map_pushforwardModules_map_squareComparison_app,
    moduleSheafFunctor_map_pushforwardModules_map_twoMorphismComp_app]
  exact transitionPaste_underlying scn scm gn gm f x dn dm e b aug an am τ In Im sA sDn sDm sT sX
    hS M

/-- **The pasting identity, as an identity of transformations of pullbacks**, from the
corresponding identity of direct images of sheaves of sets `hS`. -/
theorem pullbackModules_transitionPaste_natTrans
    (hS : ∀ G : Sheaf En.J (Type w),
      sDn.e.inv.app G ≫ sA.e.inv.app (dn.toToposHom.pushforward.obj G) ≫
          b.toToposHom.pushforward.map (In.e.hom.app G) ≫
          b.toToposHom.pushforward.map (τ.t.app (scn.toToposHom.pushforward.obj G)) =
        sX.e.inv.app G ≫ sDm.e.inv.app (x.toToposHom.pushforward.obj G) ≫
          sA.e.inv.app (dm.toToposHom.pushforward.obj (x.toToposHom.pushforward.obj G)) ≫
          b.toToposHom.pushforward.map (Im.e.hom.app (x.toToposHom.pushforward.obj G)) ≫
          b.toToposHom.pushforward.map (gm.toToposHom.pushforward.map (sT.e.inv.app G))) :
    Functor.whiskerLeft b.toModulesHom.pullbackModules (Functor.whiskerRight
        ((pullbackModulesCompIso f gm).inv ≫ τ.pullbackModulesMap)
          scn.toModulesHom.pullbackModules) ≫
      (Functor.whiskerLeft b.toModulesHom.pullbackModules ((pullbackModulesCompIso scn gn).inv ≫
          In.pullbackModulesIso.inv ≫ (pullbackModulesCompIso dn e).hom) ≫
        Functor.whiskerRight ((pullbackModulesCompIso e b).inv ≫ sA.pullbackModulesIso.hom)
          dn.toModulesHom.pullbackModules ≫
        (pullbackModulesCompIso dn aug).inv ≫ sDn.pullbackModulesIso.hom) =
    Functor.whiskerLeft (b.toModulesHom.pullbackModules ⋙ gm.toModulesHom.pullbackModules)
        ((pullbackModulesCompIso scn f).inv ≫ sT.pullbackModulesIso.hom ≫
          (pullbackModulesCompIso x scm).hom) ≫
      Functor.whiskerRight (Functor.whiskerLeft b.toModulesHom.pullbackModules
          ((pullbackModulesCompIso scm gm).inv ≫ Im.pullbackModulesIso.inv ≫
            (pullbackModulesCompIso dm e).hom) ≫
        Functor.whiskerRight ((pullbackModulesCompIso e b).inv ≫ sA.pullbackModulesIso.hom)
          dm.toModulesHom.pullbackModules ≫
        (pullbackModulesCompIso dm aug).inv ≫ sDm.pullbackModulesIso.hom)
        x.toModulesHom.pullbackModules ≫
      (pullbackModulesCompIso x am).inv ≫ sX.pullbackModulesIso.hom := by
  have hα : Functor.whiskerLeft b.toModulesHom.pullbackModules (Functor.whiskerRight
        ((pullbackModulesCompIso f gm).inv ≫ τ.pullbackModulesMap)
          scn.toModulesHom.pullbackModules) =
      (conjugateEquiv ((pullbackAdjPushforwardModules b).comp
          ((pullbackAdjPushforwardModules gn).comp (pullbackAdjPushforwardModules scn)))
        ((pullbackAdjPushforwardModules b).comp ((pullbackAdjPushforwardModules gm).comp
          ((pullbackAdjPushforwardModules f).comp (pullbackAdjPushforwardModules scn))))).symm
        (Functor.whiskerRight (Functor.whiskerLeft (pushforwardModules scn)
          (τ.pushforwardModulesMap ≫ (pushforwardModulesCompIso f gm).hom))
          (pushforwardModules b)) := by
    rw [pullbackModules_twoMorphismComp_eq, Equiv.eq_symm_apply,
      ← Adjunction.comp_assoc_eq (pullbackAdjPushforwardModules gm)
        (pullbackAdjPushforwardModules f) (pullbackAdjPushforwardModules scn),
      conjugateEquiv_whiskerLeft, conjugateEquiv_whiskerRight, Equiv.apply_symm_apply]
  have hβ : Functor.whiskerLeft (b.toModulesHom.pullbackModules ⋙ gm.toModulesHom.pullbackModules)
        ((pullbackModulesCompIso scn f).inv ≫ sT.pullbackModulesIso.hom ≫
          (pullbackModulesCompIso x scm).hom) =
      (conjugateEquiv ((pullbackAdjPushforwardModules b).comp
          ((pullbackAdjPushforwardModules gm).comp
            ((pullbackAdjPushforwardModules scm).comp (pullbackAdjPushforwardModules x))))
        ((pullbackAdjPushforwardModules b).comp ((pullbackAdjPushforwardModules gm).comp
          ((pullbackAdjPushforwardModules f).comp (pullbackAdjPushforwardModules scn))))).symm
        (Functor.whiskerRight ((pushforwardModulesCompIso x scm).inv ≫
          sT.pushforwardModulesIso.inv ≫ (pushforwardModulesCompIso scn f).hom)
          (pushforwardModules gm ⋙ pushforwardModules b)) := by
    rw [pullbackModules_squareComparison_hom_eq, Equiv.eq_symm_apply,
      ← Adjunction.comp_assoc_eq (pullbackAdjPushforwardModules b)
        (pullbackAdjPushforwardModules gm) _,
      ← Adjunction.comp_assoc_eq (pullbackAdjPushforwardModules b)
        (pullbackAdjPushforwardModules gm) _,
      conjugateEquiv_whiskerLeft, Equiv.apply_symm_apply]
  have hγ : Functor.whiskerRight (Functor.whiskerLeft b.toModulesHom.pullbackModules
          ((pullbackModulesCompIso scm gm).inv ≫ Im.pullbackModulesIso.inv ≫
            (pullbackModulesCompIso dm e).hom) ≫
        Functor.whiskerRight ((pullbackModulesCompIso e b).inv ≫ sA.pullbackModulesIso.hom)
          dm.toModulesHom.pullbackModules ≫
        (pullbackModulesCompIso dm aug).inv ≫ sDm.pullbackModulesIso.hom)
        x.toModulesHom.pullbackModules =
      (conjugateEquiv ((pullbackAdjPushforwardModules am).comp (pullbackAdjPushforwardModules x))
        ((pullbackAdjPushforwardModules b).comp ((pullbackAdjPushforwardModules gm).comp
          ((pullbackAdjPushforwardModules scm).comp (pullbackAdjPushforwardModules x))))).symm
        (Functor.whiskerLeft (pushforwardModules x)
          ((sDm.pushforwardModulesIso.inv ≫ (pushforwardModulesCompIso dm aug).hom) ≫
            Functor.whiskerLeft (pushforwardModules dm)
              (sA.pushforwardModulesIso.inv ≫ (pushforwardModulesCompIso e b).hom) ≫
            Functor.whiskerRight ((pushforwardModulesCompIso dm e).inv ≫
              Im.pushforwardModulesIso.hom ≫ (pushforwardModulesCompIso scm gm).hom)
              (pushforwardModules b))) := by
    rw [pullbackModules_degreeComparison_eq, Equiv.eq_symm_apply,
      ← Adjunction.comp_assoc_eq (pullbackAdjPushforwardModules gm)
        (pullbackAdjPushforwardModules scm) (pullbackAdjPushforwardModules x),
      ← Adjunction.comp_assoc_eq (pullbackAdjPushforwardModules b)
        ((pullbackAdjPushforwardModules gm).comp (pullbackAdjPushforwardModules scm))
        (pullbackAdjPushforwardModules x),
      conjugateEquiv_whiskerRight, Equiv.apply_symm_apply]
  rw [hα, pullbackModules_degreeComparison_eq, hβ, hγ, pullbackModules_compTwoIso_eq x am an sX,
    conjugateEquiv_symm_comp, conjugateEquiv_symm_comp, conjugateEquiv_symm_comp]
  refine congrArg (conjugateEquiv _ _).symm ?_
  exact pushforwardModules_transitionPaste_eq scn scm gn gm f x dn dm e b aug an am τ In Im sA sDn
    sDm sT sX hS

/-- **The pasting identity of pullbacks of sheaves of modules.** Let `R_k` be functors with
`g_k^* ≅ R_k` and `t : R_m ⋙ f^* ⟶ R_n` the transition of `τ` read through these isomorphisms.
Then, at every `F`, the transition `sc_n^* t` at `b^*F` read through the comparisons of degree `n`
is the comparison `sc_n^* f^* ⟶ x^* sc_m^*` followed by `x^*` of the comparison of degree `m` and
by `a_m ∘ x ≅ a_n`, as soon as the corresponding identity `hS` of direct images of sheaves of sets
holds. -/
theorem pullbackModules_transitionPaste_eq
    (hS : ∀ G : Sheaf En.J (Type w),
      sDn.e.inv.app G ≫ sA.e.inv.app (dn.toToposHom.pushforward.obj G) ≫
          b.toToposHom.pushforward.map (In.e.hom.app G) ≫
          b.toToposHom.pushforward.map (τ.t.app (scn.toToposHom.pushforward.obj G)) =
        sX.e.inv.app G ≫ sDm.e.inv.app (x.toToposHom.pushforward.obj G) ≫
          sA.e.inv.app (dm.toToposHom.pushforward.obj (x.toToposHom.pushforward.obj G)) ≫
          b.toToposHom.pushforward.map (Im.e.hom.app (x.toToposHom.pushforward.obj G)) ≫
          b.toToposHom.pushforward.map (gm.toToposHom.pushforward.map (sT.e.inv.app G)))
    {Rm : Ts.Modules ⥤ Cm.Modules} {Rn : Ts.Modules ⥤ Cn.Modules}
    (cprm : gm.toModulesHom.pullbackModules ≅ Rm) (cprn : gn.toModulesHom.pullbackModules ≅ Rn)
    (t : Rm ⋙ f.toModulesHom.pullbackModules ⟶ Rn)
    (ht : ∀ M, t.app M = f.toModulesHom.pullbackModules.map (cprm.inv.app M) ≫
      ((pullbackModulesCompIso f gm).inv ≫ τ.pullbackModulesMap).app M ≫ cprn.hom.app M)
    (F : Zt.Modules) :
    scn.toModulesHom.pullbackModules.map (t.app (b.toModulesHom.pullbackModules.obj F)) ≫
        (Functor.whiskerRight cprn.inv scn.toModulesHom.pullbackModules ≫
          (pullbackModulesCompIso scn gn).inv ≫ In.pullbackModulesIso.inv ≫
          (pullbackModulesCompIso dn e).hom).app (b.toModulesHom.pullbackModules.obj F) ≫
        dn.toModulesHom.pullbackModules.map
          (((pullbackModulesCompIso e b).inv ≫ sA.pullbackModulesIso.hom).app F) ≫
        ((pullbackModulesCompIso dn aug).inv ≫ sDn.pullbackModulesIso.hom).app F =
      ((pullbackModulesCompIso scn f).inv ≫ sT.pullbackModulesIso.hom ≫
          (pullbackModulesCompIso x scm).hom).app (Rm.obj (b.toModulesHom.pullbackModules.obj F)) ≫
        x.toModulesHom.pullbackModules.map
          ((Functor.whiskerRight cprm.inv scm.toModulesHom.pullbackModules ≫
            (pullbackModulesCompIso scm gm).inv ≫ Im.pullbackModulesIso.inv ≫
            (pullbackModulesCompIso dm e).hom).app (b.toModulesHom.pullbackModules.obj F) ≫
          dm.toModulesHom.pullbackModules.map
            (((pullbackModulesCompIso e b).inv ≫ sA.pullbackModulesIso.hom).app F) ≫
          ((pullbackModulesCompIso dm aug).inv ≫ sDm.pullbackModulesIso.hom).app F) ≫
        ((pullbackModulesCompIso x am).inv ≫ sX.pullbackModulesIso.hom).app F := by
  have key := NatTrans.congr_app (pullbackModules_transitionPaste_natTrans scn scm gn gm f x dn dm
    e b aug an am τ In Im sA sDn sDm sT sX hS) F
  have hn := ((pullbackModulesCompIso scn f).inv ≫ sT.pullbackModulesIso.hom ≫
    (pullbackModulesCompIso x scm).hom).naturality
      (cprm.inv.app (b.toModulesHom.pullbackModules.obj F))
  rw [ht]
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.map_comp, Category.assoc, Functor.comp_map] at key hn ⊢
  have hc : scn.toModulesHom.pullbackModules.map
        (cprn.hom.app (b.toModulesHom.pullbackModules.obj F)) ≫
      scn.toModulesHom.pullbackModules.map (cprn.inv.app (b.toModulesHom.pullbackModules.obj F)) =
        𝟙 _ := by
    rw [← Functor.map_comp, Iso.hom_inv_id_app, CategoryTheory.Functor.map_id]
  rw [← reassoc_of% hn, reassoc_of% hc, key]
  rfl

end Paste

end AlgebraicGeometry.RingedToposHom

end
