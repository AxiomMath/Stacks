module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedCone

/-!
# Morphisms out of the cone on the identity

Let `R` be a sheaf of rings on a site and let `A` be a sheaf of differential graded
`R`-algebras. Regarding `A` as a right differential graded module over itself, morphisms from
the cone of the identity of that module into a right differential graded `A`-module `M` are the
same thing as a pair of global sections of `M`, one in degree zero and one in degree minus one,
the first being the differential of the second.

## Main definitions

* `SheafOfModules.DifferentialGradedModule.regularModule` regards a sheaf of differential graded
  algebras as a right differential graded module over itself.
* `SheafOfModules.DifferentialGradedModule.identityCone` is the cone of the identity of the
  regular right module.

## Main results

* `SheafOfModules.DifferentialGradedModule.coneIdentity_hom_equiv_sections` identifies morphisms
  out of the cone of the identity with pairs of global sections in degrees zero and minus one
  related by the differential.

## Implementation notes

The cone used is the one of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/DifferentialGradedCone.lean`, whose degree-`n`
piece splits as the shifted source followed by the target. So for the identity of the regular
module the unit in degree minus one sits in the *first* summand and the unit in degree zero in
the *second*, and the equivalence is specified by evaluating a morphism on those two canonical
sections over every object of the site. A morphism out of the cone is determined by its values
there because the two sections generate the cone over the algebra, which is the content of the
private `coneLeft_generated`, `coneRight_generated` and `cone_hom_ext`.

In the other direction, a pair of sections `(x, y)` with `x = d y` is turned into a morphism by
multiplying: the cochain `actionCochain` of right multiplication by a global section is a
cochain of the degree of that section, its differential is right multiplication by the
differential of the section, and the mapping cone's own description of morphisms out of it
(`CochainComplex.mappingCone.desc`) assembles the two into a morphism of complexes. That the
assembled map respects the action of `A` is checked one summand at a time through the cone's
`action_first` and `action_second`.

The base is an arbitrary sheaf of rings on an arbitrary site rather than the structure sheaf of
a ringed site, and the universes of the site, the ring and the algebra pieces are independent;
a ringed site `X` is the case `R := X.ringSheaf`. The module universe is the algebra universe,
since the regular module's pieces are the algebra's own.

## References

* [Stacks Project, Tag 0FS8](https://stacks.math.columbia.edu/tag/0FS8)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe t a v u

namespace SheafOfModules

namespace DifferentialGradedModule

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}



/-- A differential graded algebra, acting on itself on the right. -/
def regularModule (A : DifferentialGradedAlgebra.{t, a} R) :
    DifferentialGradedModule.{t, a, a} A where
  complex := A.complex
  mul n m := {
    app := (A.mul n m).app
    map_smul_left := (A.mul n m).map_smul_left
    map_smul_right := (A.mul n m).map_smul_right
    naturality := (A.mul n m).naturality }
  mul_assoc := A.mul_assoc
  mul_one := A.mul_one
  leibniz := A.leibniz

/-- The cone on the identity of the regular right module. -/
noncomputable abbrev identityCone (A : DifferentialGradedAlgebra.{t, a} R) :
    DifferentialGradedModule.{t, a, a} A :=
  cone (𝟙 (regularModule A))

private def actionMapApp {A : DifferentialGradedAlgebra.{t, a} R}
    {M : DifferentialGradedModule.{t, a, a} A} {k n : ℤ}
    (z : (M.complex.X k).sections) (U : Cᵒᵖ) :
    (A.complex.X n).val.obj U ⟶ (M.complex.X (k + n)).val.obj U :=
  ModuleCat.ofHom {
    toFun := fun a => (M.mul k n).app U (z.eval U) a
    map_add' := by intro a b; simp
    map_smul' := by
      intro r a
      exact (M.mul k n).map_smul_right U r (z.eval U) a
    }

private def actionMap {A : DifferentialGradedAlgebra.{t, a} R}
    {M : DifferentialGradedModule.{t, a, a} A} {k n : ℤ}
    (z : (M.complex.X k).sections) :
    (A.complex.X n).val ⟶ (M.complex.X (k + n)).val := by
  refine { app := actionMapApp z, naturality := ?_ }
  intro U V f
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  simp only [ModuleCat.comp_apply, ModuleCat.restrictScalars.map_apply]
  dsimp [actionMapApp]
  change (M.mul k n).app V (z.eval V) ((A.complex.X n).val.map f a) =
    (M.complex.X (k + n)).val.map f ((M.mul k n).app U (z.eval U) a)
  rw [(M.mul k n).naturality f (z.eval U) a]
  have hz : (M.complex.X k).val.map f (z.eval U) = z.eval V :=
    z.property f
  rw [hz]

private def actSheaf {A : DifferentialGradedAlgebra.{t, a} R}
    {M : DifferentialGradedModule.{t, a, a} A} {k n : ℤ}
    (z : (M.complex.X k).sections) : A.complex.X n ⟶ M.complex.X (k+n) :=
  ⟨actionMap z⟩

private def actionCochain {A : DifferentialGradedAlgebra.{t, a} R}
    {M : DifferentialGradedModule.{t, a, a} A} {k : ℤ} (z : (M.complex.X k).sections) :
    CochainComplex.HomComplex.Cochain A.complex M.complex k :=
  CochainComplex.HomComplex.Cochain.mk fun p q h =>
    actSheaf z ≫ eqToHom (congrArg M.complex.X (by omega))

private theorem eqToHom_sheaf_app_apply {F G : SheafOfModules.{a} R} (h : F = G) (U : Cᵒᵖ)
    (x : F.val.obj U) :
    ((eqToHom h).val.app U).hom x = h ▸ x := by
  cases h
  rfl

private theorem cast_comp {α : Sort _} {P : α → Sort _} {i j k : α}
    (hij : i = j) (hjk : j = k) (h : i = k) (x : P i) :
    hjk ▸ (hij ▸ x) = h ▸ x := by
  subst h
  cases hij
  cases hjk
  rfl

private theorem cast_irrel {α : Sort _} {P : α → Sort _} {i j : α}
    (h₁ h₂ : i = j) (x : P i) : h₁ ▸ x = h₂ ▸ x := by
  cases h₁
  cases h₂
  rfl

private theorem eqRec_module_apply {A : DifferentialGradedAlgebra.{t, a} R}
    {M : DifferentialGradedModule.{t, a, a} A} {U : Cᵒᵖ} {i j : ℤ}
    (h : i = j) (z : (M.complex.X i).val.obj U) :
    Eq.rec (motive := fun k _ => (M.complex.X i).val.obj U →
      (M.complex.X k).val.obj U) id h z = h ▸ z := by
  cases h
  rfl

private theorem cast_module_degree {A : DifferentialGradedAlgebra.{t, a} R}
    {M : DifferentialGradedModule.{t, a, a} A} {U : Cᵒᵖ} {i j : ℤ}
    (h : i = j) (z : (M.complex.X i).val.obj U) :
    h ▸ z = congrArg M.complex.X h ▸ z := by
  cases h
  rfl

private theorem actionCochain_delta {A : DifferentialGradedAlgebra.{t, a} R}
    {M : DifferentialGradedModule.{t, a, a} A}
    (y : (M.complex.X (-1)).sections) (x : (M.complex.X 0).sections)
    (h : ∀ U, (M.complex.d (-1) 0).val.app U (y.eval U) = x.eval U) :
    CochainComplex.HomComplex.δ (-1) 0 (actionCochain y) = actionCochain x := by
  apply CochainComplex.HomComplex.Cochain.ext₀
  intro p
  rw [CochainComplex.HomComplex.δ_v (-1) 0 (by omega) (actionCochain y)
    p p (add_zero p) (p - 1) (p + 1) (by omega) (by omega)]
  ext U a
  simp only [CochainComplex.HomComplex.Cochain.mk_v,
    actionCochain, actSheaf, actionMap, actionMapApp,
    SheafOfModules.comp_val, PresheafOfModules.comp_app,
    ModuleCat.comp_apply]
  simp only [Int.reduceNeg, Category.assoc, ComplexShape.up_Rel, neg_add_cancel_comm,
    sub_add_cancel, HomologicalComplex.eqToHom_comp_d, Int.negOnePow_zero, one_smul, add_val,
    comp_val, PresheafOfModules.add_app, PresheafOfModules.comp_app, ModuleCat.hom_add,
    ModuleCat.hom_comp, LinearMap.add_apply, LinearMap.coe_comp, Function.comp_apply,
    ConcreteCategory.hom_ofHom, LinearMap.coe_mk, AddHom.coe_mk]
  have hM := M.leibniz (-1) p U (y.eval U) a
  have hd : (M.complex.d (-1) (-1 + 1)).val.app U (y.eval U) = x.eval U := by
    convert h U <;> norm_num
  rw [hd] at hM
  let hi : p = (-1 : ℤ) + p + 1 := by omega
  let e : M.complex.X p ⟶ M.complex.X ((-1 : ℤ) + p + 1) :=
    eqToHom (congrArg M.complex.X hi)
  let ei : M.complex.X ((-1 : ℤ) + p + 1) ⟶ M.complex.X p :=
    eqToHom (congrArg M.complex.X hi).symm
  have hcat : e ≫ ei = 𝟙 _ := by simp [e, ei]
  have hcatVal : e.val ≫ ei.val = 𝟙 ((M.complex.X p).val) := congrArg (fun f => f.val) hcat
  have hleft : Function.LeftInverse
      ((ModuleCat.Hom.hom (ei.val.app U))) ((ModuleCat.Hom.hom (e.val.app U))) := by
    intro z
    show ModuleCat.Hom.hom ((e.val ≫ ei.val).app U) z = z
    rw [hcatVal]
    simp
  have he : Function.Injective ((e.val.app U).hom) := hleft.injective
  have hD : M.complex.d (-1 + p) p ≫ e = M.complex.d (-1 + p) (-1 + p + 1) := by
    simp [e]
  have hDpoint (z : (M.complex.X (-1 + p)).val.obj U) :
      ((e.val.app U).hom) (((M.complex.d (-1 + p) p).val.app U).hom z) =
        ((M.complex.d (-1 + p) (-1 + p + 1)).val.app U).hom z := by
    have hh := congrArg (fun f => (f.val.app U).hom z) hD
    simpa [PresheafOfModules.comp_app, ModuleCat.comp_apply] using hh
  have hDcast (z : (M.complex.X (-1 + p)).val.obj U) :
      (congrArg M.complex.X hi) ▸ (((M.complex.d (-1 + p) p).val.app U).hom z) =
        ((M.complex.d (-1 + p) (-1 + p + 1)).val.app U).hom z := by
    have hh := hDpoint z
    simpa [e, eqToHom_sheaf_app_apply] using hh
  have hEqFun {i j : ℤ} (hh : i = j) (z : (M.complex.X i).val.obj U) :
      Eq.rec (motive := fun q _ => (M.complex.X i).val.obj U → (M.complex.X q).val.obj U)
        id hh z ≍ z := by
    cases hh
    rfl
  have hM' :
      (M.complex.d (-1 + p) (-1 + p + 1)).val.app U
          ((M.mul (-1) p).app U (y.eval U) a) +
        gradedCast (fun q => (M.complex.X q).val.obj U)
          (add_assoc (-1) p 1).symm
          ((M.mul (-1) (p + 1)).app U (y.eval U)
            ((A.complex.d p (p + 1)).val.app U a)) =
      gradedCast (fun q => (M.complex.X q).val.obj U)
        (add_right_comm (-1) 1 p)
        ((M.mul 0 p).app U (x.eval U) a) := by
    rw [hM]
    norm_num [gradedCast, Int.negOnePow]
    have hn : (-1 : ℤ) + 1 = 0 := by norm_num
    cases hn
    rfl
  have hneg : (-1 : ℤ) + 1 = 0 := by norm_num
  cases hneg
  apply he
  dsimp [actionMapApp]
  have h1 := hDpoint (((M.mul (-1) p).app U (y.eval U)) a)
  rw [map_add, h1]
  convert hM' using 1
  all_goals have hp1 : (-1 : ℤ) + p + 1 = p := by omega
  all_goals have hp2 : (-1 : ℤ) + (p + 1) = p := by omega
  all_goals simp only [hp1, hp2] at *
  all_goals try dsimp [e]
  all_goals simp only [eqToHom_sheaf_app_apply]
  all_goals try ring_nf at *
  all_goals dsimp [eqToHom_sheaf_app_apply, gradedCast]
  all_goals try simp only [Int.reduceNeg, add_right_inj]
  all_goals generalize_proofs _ hobj₂ hobj₁ hdeg
  all_goals rw [eqRec_module_apply hdeg]
  all_goals
    calc
      _ = (congrArg M.complex.X hdeg) ▸ _ :=
        cast_comp (P := fun F : SheafOfModules R => F.val.obj U)
          hobj₂ hobj₁ (congrArg M.complex.X hdeg) _
      _ = _ := (cast_module_degree hdeg _).symm

private noncomputable def actionCochainReg {A : DifferentialGradedAlgebra.{t, a} R}
    {M : DifferentialGradedModule.{t, a, a} A} {k : ℤ}
    (z : (M.complex.X k).sections) :
    CochainComplex.HomComplex.Cochain (regularModule A).complex M.complex k :=
  actionCochain z

private theorem regularModule_complex_eq {A : DifferentialGradedAlgebra.{t, a} R} :
    A.complex = (regularModule A).complex := rfl

private theorem actionCochainReg_v {A : DifferentialGradedAlgebra.{t, a} R}
    {M : DifferentialGradedModule.{t, a, a} A} {k : ℤ}
    (he : A.complex = (regularModule A).complex)
    (z : (M.complex.X k).sections) (p q : ℤ) (hpq : p + k = q) :
    (actionCochainReg z).v p q hpq =
      eqToHom (congrArg (fun C : CochainComplex (SheafOfModules R) ℤ => C.X p)
        he).symm ≫
        actSheaf z ≫ eqToHom (congrArg M.complex.X (by omega)) := by
  cases he
  rfl

private theorem actionCochainReg_delta {A : DifferentialGradedAlgebra.{t, a} R}
    {M : DifferentialGradedModule.{t, a, a} A}
    (y : (M.complex.X (-1)).sections) (x : (M.complex.X 0).sections)
    (h : ∀ U, (M.complex.d (-1) 0).val.app U (y.eval U) = x.eval U) :
    CochainComplex.HomComplex.δ (-1) 0 (actionCochainReg y) = actionCochainReg x := by
  have he : A.complex = (regularModule A).complex := rfl
  cases he
  exact actionCochain_delta y x h

private theorem heq_to_eq_sheaf_cast {F G : SheafOfModules.{a} R} {U : Cᵒᵖ}
    {x : F.val.obj U} {y : G.val.obj U} (h : HEq x y) (e : F = G) :
    x = e ▸ y := by
  cases e
  exact eq_of_heq h

private theorem module_mul_cast_left {A : DifferentialGradedAlgebra.{t, a} R}
    {M : DifferentialGradedModule.{t, a, a} A} {U : Cᵒᵖ}
    {i j m : ℤ} (e : i = j) (z : (M.complex.X i).val.obj U)
    (a : (A.complex.X m).val.obj U) :
    (congrArg M.complex.X (congrArg (fun k : ℤ => k + m) e) ▸
        ((M.mul i m).app U z a)) =
      ((M.mul j m).app U (e ▸ z)) a := by
  cases e
  rfl

private theorem module_mul_cast_right {A : DifferentialGradedAlgebra.{t, a} R}
    {M : DifferentialGradedModule.{t, a, a} A} {U : Cᵒᵖ}
    {k i j : ℤ} (e : i = j) (x : (M.complex.X k).val.obj U)
    (a : (A.complex.X i).val.obj U) :
    (congrArg M.complex.X (congrArg (fun q : ℤ => k + q) e) ▸
        ((M.mul k i).app U x a)) =
      ((M.mul k j).app U x ((congrArg A.complex.X e) ▸ a)) := by
  cases e
  rfl

private theorem action_assoc_shifted {A : DifferentialGradedAlgebra.{t, a} R}
    {M : DifferentialGradedModule.{t, a, a} A}
    (y : (M.complex.X (-1)).sections) (n m : ℤ) (U : Cᵒᵖ)
    (z : (A.complex.X (n + 1)).val.obj U) (a : (A.complex.X m).val.obj U) :
    (congrArg M.complex.X (by omega : -1 + (n + m + 1) = n + m)) ▸
        ((M.mul (-1) (n + m + 1)).app U (y.eval U)
          ((congrArg A.complex.X (by omega : (n + 1) + m = n + m + 1)) ▸
            ((A.mul (n + 1) m).app U z a))) =
      ((M.mul n m).app U
        ((congrArg M.complex.X (by omega : -1 + (n + 1) = n)) ▸
          ((M.mul (-1) (n + 1)).app U (y.eval U) z))) a := by
  let eA : (n + 1) + m = n + m + 1 := by omega
  let eInner : -1 + (n + 1) = n := by omega
  let eOut : -1 + (n + m + 1) = n + m := by omega
  let eShift : -1 + ((n + 1) + m) = -1 + (n + m + 1) := by omega
  let eAssoc : (-1 + (n + 1)) + m = n + m := by omega
  let eLeftOut : -1 + ((n + 1) + m) = n + m := by omega
  let aCast := congrArg A.complex.X eA
  let innerCast := congrArg M.complex.X eInner
  let outCast := congrArg M.complex.X eOut
  let shiftCast := congrArg M.complex.X eShift
  let assocCast := congrArg M.complex.X eAssoc
  let leftOutCast := congrArg M.complex.X eLeftOut
  have h := M.mul_assoc (-1) (n + 1) m U (y.eval U) z a
  have hObj : M.complex.X (-1 + ((n + 1) + m)) =
      M.complex.X ((-1 + (n + 1)) + m) := congrArg M.complex.X (by omega)
  have hEq := heq_to_eq_sheaf_cast h.symm hObj
  calc
    _ = outCast ▸ (shiftCast ▸
          ((M.mul (-1) ((n + 1) + m)).app U (y.eval U)
            ((A.mul (n + 1) m).app U z a))) := by
      have hR := module_mul_cast_right eA (y.eval U) ((A.mul (n + 1) m).app U z a)
      exact congrArg (fun w => outCast ▸ w) hR.symm
    _ = leftOutCast ▸
          (((M.mul (-1) ((n + 1) + m)).app U (y.eval U))
            ((A.mul (n + 1) m).app U z a)) :=
      cast_comp (P := fun F : SheafOfModules R => F.val.obj U)
        shiftCast outCast leftOutCast _
    _ = leftOutCast ▸ (hObj ▸
          (((M.mul ((-1) + (n + 1)) m).app U
            ((M.mul (-1) (n + 1)).app U (y.eval U) z)) a)) :=
      congrArg (fun w => leftOutCast ▸ w) hEq
    _ = assocCast ▸
          (((M.mul ((-1) + (n + 1)) m).app U
            ((M.mul (-1) (n + 1)).app U (y.eval U) z)) a) :=
      cast_comp (P := fun F : SheafOfModules R => F.val.obj U)
        hObj.symm leftOutCast assocCast _
    _ = ((M.mul n m).app U (innerCast ▸
          ((M.mul (-1) (n + 1)).app U (y.eval U) z))) a := by
      let degreeCast := congrArg M.complex.X
        (congrArg (fun k : ℤ => k + m) eInner)
      calc
        assocCast ▸
            (((M.mul ((-1) + (n + 1)) m).app U
              ((M.mul (-1) (n + 1)).app U (y.eval U) z)) a) =
            degreeCast ▸
              (((M.mul ((-1) + (n + 1)) m).app U
                ((M.mul (-1) (n + 1)).app U (y.eval U) z)) a) :=
          cast_irrel
            (P := fun F : SheafOfModules R => F.val.obj U)
            assocCast degreeCast _
        _ = ((M.mul n m).app U
              (eInner ▸ ((M.mul (-1) (n + 1)).app U (y.eval U) z))) a :=
          module_mul_cast_left eInner ((M.mul (-1) (n + 1)).app U (y.eval U) z) a
        _ = ((M.mul n m).app U
              (innerCast ▸ ((M.mul (-1) (n + 1)).app U (y.eval U) z))) a := by
          have hc := cast_module_degree eInner
            ((M.mul (-1) (n + 1)).app U (y.eval U) z)
          exact congrArg (fun w => ((M.mul n m).app U w) a) hc

private theorem action_assoc_zero {A : DifferentialGradedAlgebra.{t, a} R}
    {M : DifferentialGradedModule.{t, a, a} A}
    (x : (M.complex.X 0).sections) (n m : ℤ) (U : Cᵒᵖ)
    (z : (A.complex.X n).val.obj U) (a : (A.complex.X m).val.obj U) :
    (congrArg M.complex.X (Int.zero_add (n + m))) ▸
        ((M.mul 0 (n + m)).app U (x.eval U) ((A.mul n m).app U z a)) =
      ((M.mul n m).app U
        ((Int.zero_add n) ▸ ((M.mul 0 n).app U (x.eval U) z))) a := by
  have h := M.mul_assoc 0 n m U (x.eval U) z a
  have hObj : M.complex.X (0 + (n + m)) = M.complex.X ((0 + n) + m) :=
    congrArg M.complex.X (by omega)
  have hEq := heq_to_eq_sheaf_cast h.symm hObj
  have hRight : M.complex.X ((0 + n) + m) = M.complex.X (n + m) :=
    congrArg M.complex.X (by omega)
  calc
    _ = (congrArg M.complex.X (Int.zero_add (n + m))) ▸
          (hObj ▸ (((M.mul (0 + n) m).app U
            ((M.mul 0 n).app U (x.eval U) z)) a)) :=
      congrArg (fun w => (congrArg M.complex.X (Int.zero_add (n + m))) ▸ w) hEq
    _ = hRight ▸ (((M.mul (0 + n) m).app U
          ((M.mul 0 n).app U (x.eval U) z)) a) :=
      cast_comp (P := fun F : SheafOfModules R => F.val.obj U)
        hObj.symm (congrArg M.complex.X (Int.zero_add (n + m))) hRight _
    _ = _ := by
      have h0n : (0 : ℤ) + n = n := by omega
      simpa [cast_irrel] using
        (module_mul_cast_left h0n ((M.mul 0 n).app U (x.eval U) z) a)

private noncomputable def actionCocycleReg {A : DifferentialGradedAlgebra.{t, a} R}
    {M : DifferentialGradedModule.{t, a, a} A}
    (y : (M.complex.X (-1)).sections) (x : (M.complex.X 0).sections)
    (h : ∀ U, (M.complex.d (-1) 0).val.app U (y.eval U) = x.eval U) :
    CochainComplex.HomComplex.Cocycle (regularModule A).complex M.complex 0 := by
  have hd := actionCochainReg_delta y x h
  have hz := CochainComplex.HomComplex.δ_δ (-1) 0 1 (actionCochainReg y)
  rw [hd] at hz
  exact CochainComplex.HomComplex.Cocycle.mk (actionCochainReg x) 1 (zero_add 1) hz

private theorem actionCone_desc_condition {A : DifferentialGradedAlgebra.{t, a} R}
    {M : DifferentialGradedModule.{t, a, a} A}
    (y : (M.complex.X (-1)).sections) (x : (M.complex.X 0).sections)
    (h : ∀ U, (M.complex.d (-1) 0).val.app U (y.eval U) = x.eval U) :
    CochainComplex.HomComplex.δ (-1) 0 (actionCochainReg y) =
      CochainComplex.HomComplex.Cochain.ofHom
        ((𝟙 (regularModule A) : regularModule A ⟶ regularModule A).toHomologicalComplex ≫
          (actionCocycleReg y x h).homOf) := by
  let β := CochainComplex.HomComplex.Cocycle.homOf (actionCocycleReg y x h)
  rw [actionCochainReg_delta y x h]
  rw [CochainComplex.HomComplex.Cochain.ofHom_comp]
  symm
  show (CochainComplex.HomComplex.Cochain.ofHom
      (𝟙 ((regularModule A).complex))).comp
      (CochainComplex.HomComplex.Cochain.ofHom β) (zero_add 0) = _
  rw [CochainComplex.HomComplex.Cochain.id_comp]
  exact CochainComplex.HomComplex.Cocycle.cochain_ofHom_homOf_eq_coe
    (actionCocycleReg y x h)

private noncomputable def actionConeComplexMap {A : DifferentialGradedAlgebra.{t, a} R}
    {M : DifferentialGradedModule.{t, a, a} A}
    (y : (M.complex.X (-1)).sections) (x : (M.complex.X 0).sections)
    (h : ∀ U, (M.complex.d (-1) 0).val.app U (y.eval U) = x.eval U) :
    CochainComplex.mappingCone
        ((𝟙 (regularModule A) : regularModule A ⟶ regularModule A).toHomologicalComplex) ⟶
      M.complex :=
  CochainComplex.mappingCone.desc _ (actionCochainReg y)
    (actionCocycleReg y x h).homOf (actionCone_desc_condition y x h)

private noncomputable def actionConeHomOfPackage {A : DifferentialGradedAlgebra.{t, a} R}
    {M : DifferentialGradedModule.{t, a, a} A}
    (P : ConePackage (𝟙 (regularModule A)))
    (y : (M.complex.X (-1)).sections) (x : (M.complex.X 0).sections)
    (h : ∀ U, (M.complex.d (-1) 0).val.app U (y.eval U) = x.eval U) :
    P.cone ⟶ M := by
  let C := P
  change C.cone ⟶ M
  rcases C with ⟨N, incl, proj, hcomplex, componentIso, componentIso_eq,
    action_first, action_second, incl_complex, proj_complex⟩
  rcases N with ⟨K, mul, mul_assoc, mul_one, leibniz⟩
  cases hcomplex
  refine ⟨actionConeComplexMap y x h, ?_⟩
  intro n m U z a
  have hIso (i : ℤ) : componentIso i =
      HomologicalComplex.homotopyCofiber.XIsoBiprod
        ((𝟙 (regularModule A) : regularModule A ⟶ regularModule A).toHomologicalComplex)
        i (i + 1) (by simp) := eq_of_heq (componentIso_eq i)
  have hfst (i : ℤ) :
      HomologicalComplex.homotopyCofiber.fstX
          ((𝟙 (regularModule A) : regularModule A ⟶ regularModule A).toHomologicalComplex)
          i (i + 1) (by simp) = (componentIso i).hom ≫ biprod.fst := by
    rw [hIso i]
    rfl
  have hsndGen (i j : ℤ) (hij : (ComplexShape.up ℤ).Rel i j) :
      HomologicalComplex.homotopyCofiber.sndX
          ((𝟙 (regularModule A) : regularModule A ⟶ regularModule A).toHomologicalComplex)
          i =
        (HomologicalComplex.homotopyCofiber.XIsoBiprod
          ((𝟙 (regularModule A) : regularModule A ⟶ regularModule A).toHomologicalComplex)
          i j hij).hom ≫ biprod.snd := by
    let c := ComplexShape.up ℤ
    have hi : c.Rel i (c.next i) := (c.next_eq' hij).symm ▸ hij
    rw [HomologicalComplex.homotopyCofiber.sndX, dite_eq_left hi]
    obtain rfl := c.next_eq' hij
    rfl
  have hsnd (i : ℤ) :
      HomologicalComplex.homotopyCofiber.sndX
          ((𝟙 (regularModule A) : regularModule A ⟶ regularModule A).toHomologicalComplex)
          i = (componentIso i).hom ≫ biprod.snd := by
    let c := ComplexShape.up ℤ
    have hrel : c.Rel i (i + 1) := by
      dsimp [c, ComplexShape.up, ComplexShape.up']
    rw [hIso i]
    exact hsndGen i (i + 1) hrel
  have hfstApp (i : ℤ) :
      (HomologicalComplex.homotopyCofiber.fstX
        ((𝟙 (regularModule A) : regularModule A ⟶ regularModule A).toHomologicalComplex)
        i (i + 1) (by simp)).val.app U =
      ((componentIso i).hom ≫ biprod.fst).val.app U := by
    rw [hfst i]
  have hsndApp (i : ℤ) :
      (HomologicalComplex.homotopyCofiber.sndX
        ((𝟙 (regularModule A) : regularModule A ⟶ regularModule A).toHomologicalComplex)
        i).val.app U = ((componentIso i).hom ≫ biprod.snd).val.app U := by
    rw [hsnd i]
  simp only [actionConeComplexMap,
    CochainComplex.mappingCone.desc_f]
  dsimp [CochainComplex.mappingCone.fst, CochainComplex.mappingCone.snd]
  simp only [CochainComplex.HomComplex.Cocycle.mk_coe]
  simp only [PresheafOfModules.comp_app]
  have hfirst' : HEq
      (((HomologicalComplex.homotopyCofiber.fstX
        ((𝟙 (regularModule A) : regularModule A ⟶ regularModule A).toHomologicalComplex)
        (n + m) (n + m + 1) (by simp)).val.app U)
        ((mul n m).app U z a))
      (((regularModule A).mul (n + 1) m).app U
        (((HomologicalComplex.homotopyCofiber.fstX
          ((𝟙 (regularModule A) : regularModule A ⟶ regularModule A).toHomologicalComplex)
          n (n + 1) (by simp)).val.app U) z) a) := by
    rw [hfstApp (n + m), hfstApp n]
    exact action_first n m U z a
  have hsecond' := action_second n m U z a
  have hdegree : (n + 1) + m = n + m + 1 := by omega
  have hdegreeSheaf :
      (regularModule A).complex.X (n + m + 1) =
        (regularModule A).complex.X ((n + 1) + m) :=
    congrArg (regularModule A).complex.X hdegree.symm
  have hfirstEq :
      (((HomologicalComplex.homotopyCofiber.fstX
        ((𝟙 (regularModule A) : regularModule A ⟶ regularModule A).toHomologicalComplex)
        (n + m) (n + m + 1) (by simp)).val.app U)
        ((mul n m).app U z a)) =
        hdegreeSheaf ▸ (((regularModule A).mul (n + 1) m).app U
        (((HomologicalComplex.homotopyCofiber.fstX
          ((𝟙 (regularModule A) : regularModule A ⟶ regularModule A).toHomologicalComplex)
          n (n + 1) (by simp)).val.app U) z) a) :=
    heq_to_eq_sheaf_cast hfirst' hdegreeSheaf
  clear hfirst'
  have hfirstEq' := by simpa only [hfstApp] using hfirstEq
  simp only [CochainComplex.HomComplex.Cocycle.homOf_f]
  dsimp only [CochainComplex.HomComplex.Cochain.v,
    CochainComplex.HomComplex.Cochain.mk]
  simp only [hfstApp]
  let αNm := ((componentIso (n + m)).hom ≫ biprod.fst).val.app U ≫
    ((actionCochainReg y).v (n + m + 1) (n + m) (by omega)).val.app U
  let βNm :=
    (HomologicalComplex.homotopyCofiber.sndX
      ((𝟙 (regularModule A) : regularModule A ⟶ regularModule A).toHomologicalComplex)
      (n + m)).val.app U ≫ ((actionCocycleReg y x h).homOf.f (n + m)).val.app U
  let αN := ((componentIso n).hom ≫ biprod.fst).val.app U ≫
    ((actionCochainReg y).v (n + 1) n (by omega)).val.app U
  let βN :=
    (HomologicalComplex.homotopyCofiber.sndX
      ((𝟙 (regularModule A) : regularModule A ⟶ regularModule A).toHomologicalComplex)
      n).val.app U ≫ ((actionCocycleReg y x h).homOf.f n).val.app U
  have hsecondEq :
      (HomologicalComplex.homotopyCofiber.sndX
        ((𝟙 (regularModule A) : regularModule A ⟶ regularModule A).toHomologicalComplex)
        (n + m)).val.app U ((mul n m).app U z a) =
      ((regularModule A).mul n m).app U
        ((ModuleCat.Hom.hom ((HomologicalComplex.homotopyCofiber.sndX
          ((𝟙 (regularModule A) : regularModule A ⟶ regularModule A).toHomologicalComplex)
          n).val.app U)) z) a := by
    simpa only [hsndApp] using hsecond'
  change (ModuleCat.Hom.hom (αNm + βNm) (((mul n m).app U z) a)) =
    (M.mul n m).app U (ModuleCat.Hom.hom (αN + βN) z) a
  simp only [ModuleCat.hom_add, ModuleCat.hom_comp,
    αNm, βNm, αN, βN]
  simp only [LinearMap.add_apply, LinearMap.comp_apply]
  rw [hfirstEq', hsecondEq]
  simp only [CochainComplex.HomComplex.Cocycle.homOf_f, actionCocycleReg,
    CochainComplex.HomComplex.Cocycle.mk_coe]
  rw [actionCochainReg_v regularModule_complex_eq
      y (n + m + 1) (n + m) (by omega),
    actionCochainReg_v regularModule_complex_eq
      y (n + 1) n (by omega),
    actionCochainReg_v regularModule_complex_eq
      x (n + m) (n + m) (by omega),
    actionCochainReg_v regularModule_complex_eq
      x n n (by omega)]
  simp only [SheafOfModules.comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply]
  simp only [eqToHom_sheaf_app_apply, Int.reduceNeg, map_add, AddMonoidHom.add_apply]
  congr 1
  · let z₁ := (ModuleCat.Hom.hom ((biprod.fst :
      (regularModule A).complex.X (n + 1) ⊞ (regularModule A).complex.X n ⟶
        (regularModule A).complex.X (n + 1)).val.app U))
      ((ModuleCat.Hom.hom ((componentIso n).hom.val.app U)) z)
    convert (action_assoc_shifted y n m U z₁ a) using 1 <;>
      simp only [Int.reduceNeg, actSheaf, actionMap, actionMapApp,
        ConcreteCategory.hom_ofHom, regularModule, LinearMap.coe_mk, AddHom.coe_mk, z₁]
    all_goals
      apply eq_of_heq
      rfl
  · let z₀ := (ModuleCat.Hom.hom ((HomologicalComplex.homotopyCofiber.sndX
        ((𝟙 (regularModule A) : regularModule A ⟶ regularModule A).toHomologicalComplex)
        n).val.app U)) z
    convert (action_assoc_zero x n m U z₀ a) using 1 <;>
      simp only [actSheaf, actionMap, actionMapApp, ConcreteCategory.hom_ofHom,
        regularModule, LinearMap.coe_mk, AddHom.coe_mk, cast_module_degree, z₀]
    all_goals
      apply eq_of_heq
      rfl

private noncomputable abbrev actionConeHom {A : DifferentialGradedAlgebra.{t, a} R}
    {M : DifferentialGradedModule.{t, a, a} A}
    (y : (M.complex.X (-1)).sections) (x : (M.complex.X 0).sections)
    (h : ∀ U, (M.complex.d (-1) 0).val.app U (y.eval U) = x.eval U) :
    identityCone A ⟶ M :=
  actionConeHomOfPackage (conePackage (𝟙 (regularModule A))) y x h

private noncomputable def coneEvalZero {A : DifferentialGradedAlgebra.{t, a} R}
    {M : DifferentialGradedModule.{t, a, a} A} (f : identityCone A ⟶ M) :
    (M.complex.X 0).sections :=
  PresheafOfModules.sectionsMap
    (((biprod.inr : (regularModule A).complex.X 0 ⟶
        (regularModule A).complex.X 1 ⊞ (regularModule A).complex.X 0).val ≫
      ((conePackage (𝟙 (regularModule A))).componentIso 0).inv.val) ≫
      (f.toHomologicalComplex.f 0).val)
    A.one

private noncomputable def coneEvalMinusOne {A : DifferentialGradedAlgebra.{t, a} R}
    {M : DifferentialGradedModule.{t, a, a} A} (f : identityCone A ⟶ M) :
    (M.complex.X (-1)).sections :=
  PresheafOfModules.sectionsMap
    (((biprod.inl : (regularModule A).complex.X 0 ⟶
        (regularModule A).complex.X 0 ⊞ (regularModule A).complex.X (-1)).val ≫
      ((conePackage (𝟙 (regularModule A))).componentIso (-1)).inv.val) ≫
      (f.toHomologicalComplex.f (-1)).val)
    A.one

private theorem coneEvalZero_eval {A : DifferentialGradedAlgebra.{t, a} R}
    {M : DifferentialGradedModule.{t, a, a} A} (f : identityCone A ⟶ M)
    (U : Cᵒᵖ) :
    (coneEvalZero f).eval U =
      (f.toHomologicalComplex.f 0).val.app U
        (((conePackage (𝟙 (regularModule A))).componentIso 0).inv.val.app U
          ((biprod.inr : (regularModule A).complex.X 0 ⟶
              (regularModule A).complex.X 1 ⊞ (regularModule A).complex.X 0).val.app U
            (A.one.eval U))) := by
  simp [coneEvalZero, PresheafOfModules.sectionsMap]

private theorem coneEvalMinusOne_eval {A : DifferentialGradedAlgebra.{t, a} R}
    {M : DifferentialGradedModule.{t, a, a} A} (f : identityCone A ⟶ M)
    (U : Cᵒᵖ) :
    (coneEvalMinusOne f).eval U =
      (f.toHomologicalComplex.f (-1)).val.app U
        (((conePackage (𝟙 (regularModule A))).componentIso (-1)).inv.val.app U
          ((biprod.inl : (regularModule A).complex.X 0 ⟶
              (regularModule A).complex.X 0 ⊞ (regularModule A).complex.X (-1)).val.app U
            (A.one.eval U))) := by
  simp [coneEvalMinusOne, PresheafOfModules.sectionsMap]

private alias d_one_eq_zero := SheafOfModules.DifferentialGradedAlgebra.one_closed

private noncomputable def coneLeft {A : DifferentialGradedAlgebra.{t, a} R}
    (P : ConePackage (𝟙 (regularModule A))) (n : ℤ) :
    A.complex.X (n + 1) ⟶ P.cone.complex.X n :=
  biprod.inl ≫ (P.componentIso n).inv

private noncomputable def coneRight {A : DifferentialGradedAlgebra.{t, a} R}
    (P : ConePackage (𝟙 (regularModule A))) (n : ℤ) :
    A.complex.X n ⟶ P.cone.complex.X n :=
  biprod.inr ≫ (P.componentIso n).inv

private theorem coneLeft_d {A : DifferentialGradedAlgebra.{t, a} R}
    (P : ConePackage (𝟙 (regularModule A))) :
    coneLeft P (-1) ≫ P.cone.complex.d (-1) 0 =
      coneRight P 0 - A.complex.d 0 1 ≫ coneLeft P 0 := by
  rcases P with ⟨⟨K, mul, assoc, one, leibniz⟩, incl, proj, hc, ci, hi, af, as, hic, hpc⟩
  cases hc
  have hi' : ∀ n : ℤ, ci n = HomologicalComplex.homotopyCofiber.XIsoBiprod
      (𝟙 (regularModule A) : regularModule A ⟶ regularModule A).toHomologicalComplex
        n (n + 1) (by simp) :=
    fun n => eq_of_heq (hi n)
  simp only [coneLeft, coneRight, hi']
  show (biprod.inl ≫ (HomologicalComplex.homotopyCofiber.XIsoBiprod
        (𝟙 (regularModule A) : regularModule A ⟶ regularModule A).toHomologicalComplex
          (-1) (-1 + 1) (by simp)).inv) ≫
      HomologicalComplex.homotopyCofiber.d
        (𝟙 (regularModule A) : regularModule A ⟶ regularModule A).toHomologicalComplex
        (-1) 0 =
    biprod.inr ≫ (HomologicalComplex.homotopyCofiber.XIsoBiprod
        (𝟙 (regularModule A) : regularModule A ⟶ regularModule A).toHomologicalComplex
          0 (0 + 1) (by simp)).inv -
      (regularModule A).complex.d 0 1 ≫ biprod.inl ≫
        (HomologicalComplex.homotopyCofiber.XIsoBiprod
          (𝟙 (regularModule A) : regularModule A ⟶ regularModule A).toHomologicalComplex
          0 (0 + 1) (by simp)).inv
  simp only [HomologicalComplex.homotopyCofiber.inr_XIsoBiprod_inv]
  have hid : (𝟙 (regularModule A) : regularModule A ⟶ regularModule A).toHomologicalComplex.f 0 =
      𝟙 _ := rfl
  have h := HomologicalComplex.homotopyCofiber.inlX_d
    ((𝟙 (regularModule A) : regularModule A ⟶ regularModule A).toHomologicalComplex)
    (-1) 0 1 (by simp) (by simp)
  simp only [hid, Category.id_comp, HomologicalComplex.homotopyCofiber.inlX] at h
  rw [sub_eq_add_neg, ← Preadditive.neg_comp, Preadditive.neg_comp, Category.assoc]
  exact h.trans (add_comm _ _)

private theorem coneEval_d {A : DifferentialGradedAlgebra.{t, a} R}
    {M : DifferentialGradedModule.{t, a, a} A} (f : identityCone A ⟶ M)
    (U : Cᵒᵖ) :
    (coneEvalZero f).eval U =
      (M.complex.d (-1) 0).val.app U ((coneEvalMinusOne f).eval U) := by
  let P := conePackage (𝟙 (regularModule A))
  have hd := congrArg (fun t => (t.val.app U) (A.one.eval U)) (coneLeft_d P)
  change (P.cone.complex.d (-1) 0).val.app U
    ((coneLeft P (-1)).val.app U (A.one.eval U)) =
    (coneRight P 0).val.app U (A.one.eval U) -
      (coneLeft P 0).val.app U ((A.complex.d 0 1).val.app U (A.one.eval U)) at hd
  rw [d_one_eq_zero, map_zero, sub_zero] at hd
  have hf := congrArg (fun t => (t.val.app U)
    ((coneLeft P (-1)).val.app U (A.one.eval U))) (f.toHomologicalComplex.comm (-1) 0)
  simp only [SheafOfModules.comp_val, PresheafOfModules.comp_app,
    ModuleCat.comp_apply] at hf
  rw [hd] at hf
  exact hf.symm

private theorem actionConeHom_left {A : DifferentialGradedAlgebra.{t, a} R}
    {M : DifferentialGradedModule.{t, a, a} A}
    (P : ConePackage (𝟙 (regularModule A)))
    (y : (M.complex.X (-1)).sections) (x : (M.complex.X 0).sections)
    (h : ∀ U, (M.complex.d (-1) 0).val.app U (y.eval U) = x.eval U) (n : ℤ) :
    coneLeft (P) n ≫
      (actionConeHomOfPackage P y x h).toHomologicalComplex.f n =
        (actionCochain y).v (n + 1) n (by omega) := by
  unfold actionConeHomOfPackage
  rcases P with ⟨⟨K, mul, assoc, one, leibniz⟩, incl, proj, hc, ci, hi, af, as, hic, hpc⟩
  cases hc
  have hi' := eq_of_heq (hi n)
  simp only [coneLeft, hi']
  show (CochainComplex.mappingCone.inl
    ((𝟙 (regularModule A) : regularModule A ⟶ regularModule A).toHomologicalComplex)).v
      (n + 1) n (by omega) ≫ _ = _
  dsimp only [actionConeComplexMap]
  simp only [id_eq, CochainComplex.mappingCone.inl_v_desc_f]
  rfl

private theorem actionConeHom_right {A : DifferentialGradedAlgebra.{t, a} R}
    {M : DifferentialGradedModule.{t, a, a} A}
    (P : ConePackage (𝟙 (regularModule A)))
    (y : (M.complex.X (-1)).sections) (x : (M.complex.X 0).sections)
    (h : ∀ U, (M.complex.d (-1) 0).val.app U (y.eval U) = x.eval U) (n : ℤ) :
    coneRight (P) n ≫
      (actionConeHomOfPackage P y x h).toHomologicalComplex.f n =
        (actionCochain x).v n n (by omega) := by
  unfold actionConeHomOfPackage
  rcases P with ⟨⟨K, mul, assoc, one, leibniz⟩, incl, proj, hc, ci, hi, af, as, hic, hpc⟩
  cases hc
  have hi' : ci n = HomologicalComplex.homotopyCofiber.XIsoBiprod
      (𝟙 (regularModule A) : regularModule A ⟶ regularModule A).toHomologicalComplex
        n (n + 1) (by simp) := eq_of_heq (hi n)
  simp only [coneRight, hi']
  show (biprod.inr ≫ (HomologicalComplex.homotopyCofiber.XIsoBiprod
        (𝟙 (regularModule A) : regularModule A ⟶ regularModule A).toHomologicalComplex
          n (n + 1) (by simp)).inv) ≫ _ = _
  simp only [HomologicalComplex.homotopyCofiber.inr_XIsoBiprod_inv]
  show (CochainComplex.mappingCone.inr
    ((𝟙 (regularModule A) : regularModule A ⟶ regularModule A).toHomologicalComplex)).f n ≫ _ = _
  dsimp only [actionConeComplexMap]
  simp only [id_eq, CochainComplex.mappingCone.inr_f_desc_f]
  rfl

private theorem actionConeHom_eval {A : DifferentialGradedAlgebra.{t, a} R}
    {M : DifferentialGradedModule.{t, a, a} A}
    (y : (M.complex.X (-1)).sections) (x : (M.complex.X 0).sections)
    (h : ∀ U, (M.complex.d (-1) 0).val.app U (y.eval U) = x.eval U) :
    coneEvalZero (actionConeHom y x h) = x ∧
      coneEvalMinusOne (actionConeHom y x h) = y := by
  constructor
  · apply PresheafOfModules.sections_ext
    intro U
    have he := congrArg (fun t => (t.val.app U) (A.one.eval U))
      (actionConeHom_right (conePackage (𝟙 (regularModule A))) y x h 0)
    show (coneEvalZero (actionConeHom y x h)).eval U = x.eval U
    rw [show (coneEvalZero (actionConeHom y x h)).eval U = _ from he]
    exact eq_of_heq (M.mul_one 0 U (x.eval U))
  · apply PresheafOfModules.sections_ext
    intro U
    have he := congrArg (fun t : A.complex.X 0 ⟶ M.complex.X (-1) => (t.val.app U) (A.one.eval U))
      (actionConeHom_left (conePackage (𝟙 (regularModule A))) y x h (-1))
    show (coneEvalMinusOne (actionConeHom y x h)).eval U = y.eval U
    rw [show (coneEvalMinusOne (actionConeHom y x h)).eval U = _ from he]
    exact eq_of_heq (M.mul_one (-1) U (y.eval U))

private theorem cone_point_ext {A : DifferentialGradedAlgebra.{t, a} R}
    (P : ConePackage (𝟙 (regularModule A))) (n : ℤ) (U : Cᵒᵖ)
    (a b : (P.cone.complex.X n).val.obj U)
    (h₁ : ((P.componentIso n).hom ≫ biprod.fst).val.app U a =
      ((P.componentIso n).hom ≫ biprod.fst).val.app U b)
    (h₂ : ((P.componentIso n).hom ≫ biprod.snd).val.app U a =
      ((P.componentIso n).hom ≫ biprod.snd).val.app U b) : a = b := by
  have ht : ((P.componentIso n).hom ≫ biprod.fst) ≫ coneLeft P n +
      ((P.componentIso n).hom ≫ biprod.snd) ≫ coneRight P n = 𝟙 _ := by
    calc
      _ = (P.componentIso n).hom ≫
          (biprod.fst ≫ biprod.inl + biprod.snd ≫ biprod.inr) ≫
          (P.componentIso n).inv := by
        simp only [coneLeft, coneRight, Preadditive.add_comp, Preadditive.comp_add,
          Category.assoc]
        rfl
      _ = _ := by simp [biprod.total]
  have he (z : (P.cone.complex.X n).val.obj U) :
      (coneLeft P n).val.app U
        (((P.componentIso n).hom ≫ biprod.fst).val.app U z) +
        (coneRight P n).val.app U
        (((P.componentIso n).hom ≫ biprod.snd).val.app U z) = z :=
    congrArg (fun t => (t.val.app U) z) ht
  have ha := he a
  have hb := he b
  rw [h₁, h₂] at ha
  exact ha.symm.trans hb

private theorem cone_point_heq {A : DifferentialGradedAlgebra.{t, a} R}
    (P : ConePackage (𝟙 (regularModule A))) {n m : ℤ} (hnm : n = m) (U : Cᵒᵖ)
    (a : (P.cone.complex.X n).val.obj U) (b : (P.cone.complex.X m).val.obj U)
    (h₁ : HEq (((P.componentIso n).hom ≫ biprod.fst).val.app U a)
      (((P.componentIso m).hom ≫ biprod.fst).val.app U b))
    (h₂ : HEq (((P.componentIso n).hom ≫ biprod.snd).val.app U a)
      (((P.componentIso m).hom ≫ biprod.snd).val.app U b)) : HEq a b := by
  subst m
  exact heq_of_eq (cone_point_ext P n U a b (eq_of_heq h₁) (eq_of_heq h₂))

/-- Equal morphisms of sheaves of modules have equal values on sections. -/
private theorem hom_app_congr {F G : SheafOfModules.{a} R} {f g : F ⟶ G} (h : f = g) (U : Cᵒᵖ)
    (x : F.val.obj U) : f.val.app U x = g.val.app U x := by
  rw [h]

private theorem coneLeft_components {A : DifferentialGradedAlgebra.{t, a} R}
    (P : ConePackage (𝟙 (regularModule A))) (n : ℤ) (U : Cᵒᵖ)
    (a : (A.complex.X (n + 1)).val.obj U) :
    ((P.componentIso n).hom ≫ biprod.fst).val.app U ((coneLeft P n).val.app U a) = a ∧
    ((P.componentIso n).hom ≫ biprod.snd).val.app U ((coneLeft P n).val.app U a) = 0 :=
  ⟨hom_app_congr (f := coneLeft P n ≫ (P.componentIso n).hom ≫ biprod.fst) (g := 𝟙 _)
    (by change (biprod.inl ≫ (P.componentIso n).inv) ≫ (P.componentIso n).hom ≫
        biprod.fst = 𝟙 _; simp) U a,
    hom_app_congr (f := coneLeft P n ≫ (P.componentIso n).hom ≫ biprod.snd) (g := 0)
    (by change (biprod.inl ≫ (P.componentIso n).inv) ≫ (P.componentIso n).hom ≫
        biprod.snd = 0; simp) U a⟩

private theorem coneRight_components {A : DifferentialGradedAlgebra.{t, a} R}
    (P : ConePackage (𝟙 (regularModule A))) (n : ℤ) (U : Cᵒᵖ)
    (a : (A.complex.X n).val.obj U) :
    ((P.componentIso n).hom ≫ biprod.fst).val.app U ((coneRight P n).val.app U a) = 0 ∧
    ((P.componentIso n).hom ≫ biprod.snd).val.app U ((coneRight P n).val.app U a) = a :=
  ⟨hom_app_congr (f := coneRight P n ≫ (P.componentIso n).hom ≫ biprod.fst) (g := 0)
    (by change (biprod.inr ≫ (P.componentIso n).inv) ≫ (P.componentIso n).hom ≫
        biprod.fst = 0; simp) U a,
    hom_app_congr (f := coneRight P n ≫ (P.componentIso n).hom ≫ biprod.snd) (g := 𝟙 _)
    (by change (biprod.inr ≫ (P.componentIso n).inv) ≫ (P.componentIso n).hom ≫
        biprod.snd = 𝟙 _; simp) U a⟩

private theorem coneLeft_generated {A : DifferentialGradedAlgebra.{t, a} R}
    (P : ConePackage (𝟙 (regularModule A))) (n : ℤ) (U : Cᵒᵖ)
    (a : (A.complex.X (n + 1)).val.obj U) :
    HEq ((P.cone.mul (-1) (n + 1)).app U
      ((coneLeft P (-1)).val.app U (A.one.eval U)) a)
      ((coneLeft P n).val.app U a) := by
  have hc := coneLeft_components P (-1) U
  apply cone_point_heq P (by omega) U
  · have h := P.action_first (-1) (n + 1) U
      ((coneLeft P (-1)).val.app U (A.one.eval U)) a
    rw [(hc (A.one.eval U)).1] at h
    exact h.trans ((A.one_mul (n + 1) U a).trans
      (heq_of_eq (coneLeft_components P n U a).1.symm))
  · have h := P.action_second (-1) (n + 1) U
      ((coneLeft P (-1)).val.app U (A.one.eval U)) a
    rw [(hc (A.one.eval U)).2] at h
    simp only [map_zero, AddMonoidHom.zero_apply] at h
    rw [h, (coneLeft_components P n U a).2]
    rw [show -1 + (n + 1) = n by omega]

private theorem coneRight_generated {A : DifferentialGradedAlgebra.{t, a} R}
    (P : ConePackage (𝟙 (regularModule A))) (n : ℤ) (U : Cᵒᵖ)
    (a : (A.complex.X n).val.obj U) :
    HEq ((P.cone.mul 0 n).app U
      ((coneRight P 0).val.app U (A.one.eval U)) a)
      ((coneRight P n).val.app U a) := by
  apply cone_point_heq P (zero_add n) U
  · have h := P.action_first 0 n U
      ((coneRight P 0).val.app U (A.one.eval U)) a
    rw [(coneRight_components P 0 U (A.one.eval U)).1] at h
    simp only [map_zero, AddMonoidHom.zero_apply] at h
    rw [(coneRight_components P n U a).1]
    have hh : (0 : ((regularModule A).complex.X (0 + 1 + n)).val.obj U) ≍
        (0 : ((regularModule A).complex.X (n + 1)).val.obj U) := by
      rw [show (0 : ℤ) + 1 + n = n + 1 by omega]
    exact h.trans hh
  · have h := P.action_second 0 n U
      ((coneRight P 0).val.app U (A.one.eval U)) a
    rw [(coneRight_components P 0 U (A.one.eval U)).2] at h
    exact h.heq.trans ((A.one_mul n U a).trans
      (heq_of_eq (coneRight_components P n U a).2.symm))

private theorem hom_app_heq {A : DifferentialGradedAlgebra.{t, a} R}
    {N M : DifferentialGradedModule.{t, a, a} A}
    (f : N ⟶ M) {n m : ℤ} (hnm : n = m) (U : Cᵒᵖ)
    {a : (N.complex.X n).val.obj U} {b : (N.complex.X m).val.obj U}
    (h : HEq a b) : HEq ((f.toHomologicalComplex.f n).val.app U a)
      ((f.toHomologicalComplex.f m).val.app U b) := by
  subst m
  rw [eq_of_heq h]

/-- Two morphisms of modules agreeing on a section agree on the elements it generates. -/
private theorem hom_eq_of_generated {A : DifferentialGradedAlgebra.{t, a} R}
    {N M : DifferentialGradedModule.{t, a, a} A} (f g : N ⟶ M) {j i n : ℤ} (hn : j + i = n)
    (U : Cᵒᵖ) {z : (N.complex.X j).val.obj U} {a : (A.complex.X i).val.obj U}
    {w : (N.complex.X n).val.obj U} (hz : (f.toHomologicalComplex.f j).val.app U z =
      (g.toHomologicalComplex.f j).val.app U z) (hw : HEq ((N.mul j i).app U z a) w) :
    (f.toHomologicalComplex.f n).val.app U w = (g.toHomologicalComplex.f n).val.app U w := by
  have hf := hom_app_heq f hn U hw
  have hg := hom_app_heq g hn U hw
  rw [f.map_mul, hz] at hf
  rw [g.map_mul] at hg
  exact eq_of_heq (hf.symm.trans hg)

private theorem cone_hom_ext {A : DifferentialGradedAlgebra.{t, a} R}
    {M : DifferentialGradedModule.{t, a, a} A}
    (P : ConePackage (𝟙 (regularModule A))) (f g : P.cone ⟶ M)
    (h₀ : ∀ U, (f.toHomologicalComplex.f 0).val.app U
      ((coneRight P 0).val.app U (A.one.eval U)) =
      (g.toHomologicalComplex.f 0).val.app U
      ((coneRight P 0).val.app U (A.one.eval U)))
    (h₁ : ∀ U, (f.toHomologicalComplex.f (-1)).val.app U
      ((coneLeft P (-1)).val.app U (A.one.eval U)) =
      (g.toHomologicalComplex.f (-1)).val.app U
      ((coneLeft P (-1)).val.app U (A.one.eval U))) : f = g := by
  apply DifferentialGradedModule.Hom.ext
  intro n
  apply (cancel_epi (P.componentIso n).inv).mp
  apply biprod.hom_ext'
  · change coneLeft P n ≫ f.toHomologicalComplex.f n =
      coneLeft P n ≫ g.toHomologicalComplex.f n
    ext U a
    exact hom_eq_of_generated f g (by omega) U (h₁ U) (coneLeft_generated P n U a)
  · change coneRight P n ≫ f.toHomologicalComplex.f n =
      coneRight P n ≫ g.toHomologicalComplex.f n
    ext U a
    exact hom_eq_of_generated f g (zero_add n) U (h₀ U) (coneRight_generated P n U a)

/-- A morphism from the identity cone is uniquely specified by a pair of global
sections `(x,y)` with `x = d y`; the equivalence evaluates at the canonical
unit elements in degrees zero and minus one. -/
@[stacks 0FS8]
theorem coneIdentity_hom_equiv_sections (A : DifferentialGradedAlgebra.{t, a} R)
    (M : DifferentialGradedModule.{t, a, a} A) :
    ∃ e : (identityCone A ⟶ M) ≃
        { p : (M.complex.X 0).sections × (M.complex.X (-1)).sections //
          ∀ U : Cᵒᵖ,
            p.1.eval U =
              (M.complex.d (-1) 0).val.app U (p.2.eval U) },
      ∀ (f : identityCone A ⟶ M) (U : Cᵒᵖ),
        (e f).1.1.eval U =
          (f.toHomologicalComplex.f 0).val.app U
            (((conePackage (𝟙 (regularModule A))).componentIso 0).inv.val.app U
              ((biprod.inr : (regularModule A).complex.X 0 ⟶
                  (regularModule A).complex.X 1 ⊞ (regularModule A).complex.X 0).val.app U
                (A.one.eval U))) ∧
        (e f).1.2.eval U =
          (f.toHomologicalComplex.f (-1)).val.app U
            (((conePackage (𝟙 (regularModule A))).componentIso (-1)).inv.val.app U
              ((biprod.inl : (regularModule A).complex.X 0 ⟶
                  (regularModule A).complex.X 0 ⊞ (regularModule A).complex.X (-1)).val.app U
                (A.one.eval U))) := by
  refine ⟨{
    toFun := fun f => ⟨(coneEvalZero f, coneEvalMinusOne f), coneEval_d f⟩
    invFun := fun p => actionConeHom p.1.2 p.1.1 (fun U => (p.2 U).symm)
    left_inv := ?_
    right_inv := ?_ }, fun f U => ⟨coneEvalZero_eval f U, coneEvalMinusOne_eval f U⟩⟩
  · intro f
    apply cone_hom_ext (conePackage (𝟙 (regularModule A)))
    · intro U
      show (coneEvalZero (actionConeHom (coneEvalMinusOne f) (coneEvalZero f)
        (fun U => (coneEval_d f U).symm))).eval U = (coneEvalZero f).eval U
      rw [(actionConeHom_eval _ _ _).1]
    · intro U
      show (coneEvalMinusOne (actionConeHom (coneEvalMinusOne f) (coneEvalZero f)
        (fun U => (coneEval_d f U).symm))).eval U = (coneEvalMinusOne f).eval U
      rw [(actionConeHom_eval _ _ _).2]
  · intro p
    exact Subtype.ext (Prod.ext (actionConeHom_eval p.1.2 p.1.1 _).1
      (actionConeHom_eval p.1.2 p.1.1 _).2)


end DifferentialGradedModule

end SheafOfModules
