module

public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplex
public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Adjunction.Unique
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseRightDerived
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Monoidal.LargeUniverse
public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedLimits
public import StacksFrontier.Algebra.Homology.KFlat
public import StacksFrontier.Homology.ExtendScalars.Flat
public import StacksFrontier.Homology.HomComplex.Basic
public import StacksFrontier.Homology.HomComplex.DerivedAdjunction
public import StacksFrontier.Homology.HomComplex.DerivedInternalHom
public import StacksFrontier.Homology.KFlat.LargeUniverse
public import StacksFrontier.Homology.TensorComplex.ExactFunctor
public import StacksFrontier.Homology.Tor.DerivedChangeOfRings
public import StacksFrontier.Homology.Tor.DerivedChangeOfRingsAdjunction
public import StacksFrontier.Homology.Tor.DerivedTensor
public import StacksFrontier.Homology.TorAmplitude.Comparison
public import StacksFrontier.Algebra.Homology.PseudoCoherent
public import StacksFrontier.Homology.HomComplex.Currying
public import StacksFrontier.Homology.HomComplex.DerivedTensorHom
public import StacksFrontier.Homology.HomComplex.Evaluation.TensorHom
public import StacksFrontier.Homology.KFlat.Flat
public import StacksFrontier.Homology.KFlat.Resolution
public import StacksFrontier.Homology.KFlat.ScalarBaseChange
public import StacksFrontier.Homology.Perfect.Defs
public import StacksFrontier.Homology.PseudoCoherent.Basic
public import StacksFrontier.Homology.TensorComplex.Monoidal
public import StacksFrontier.Homology.TorAmplitude.KFlatRepresentative
public import StacksFrontier.Homology.TensorComplex.TensorUnitIso
public import StacksFrontier.Homology.HomComplex.RHom.BaseChange.ProjectionFormula
import all StacksFrontier.Homology.HomComplex.RHom.BaseChange.BaseChangeMap
import all StacksFrontier.Homology.HomComplex.RHom.BaseChange.ProjectionFormula

/-!
# Base change and tensor--Hom adjunction on Hom complexes

The base-change map on Hom complexes along `f : R → A` and its projection compatibility, the
naturality of the canonical Hom model, the chain-level tensor--Hom adjunction for Hom complexes,
and its scalar-extension form `Stacks.DerivedHom.BaseChangeIso.tensorExtendScalarsIso`.
-/

open StacksDraft.DerivedHom.Construction (KInjectiveObjects Q_map_surjective_of_isKInjective
    postcomp_bijective postcomp_quasiIso_of_homotopyEquivalence precomp_bijective
    precomp_quasiIso_of_homotopyEquivalence)

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CochainComplex CochainComplex.HomComplex StacksDraft.DerivedHom

namespace Stacks.DerivedHom.BaseChangeIso

universe uR uA uM

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] RingHomInvPair.of_ringEquiv RingHomInvPair.of_ringEquiv_symm

open scoped TensorProduct ChangeOfRings

open DiagonalModel

section HomComplexBaseChange

open CochainComplex CochainComplex.HomComplex
open scoped TensorProduct ChangeOfRings

set_option backward.isDefEq.respectTransparency false

variable {R : Type uR} {A : Type uA} [CommRing R] [CommRing A] (f : R →+* A)

/-- Extension of scalars along `f` is an additive functor. -/
local instance : (ModuleCat.extendScalars.{uR, uA, uM} f).Additive := by
  let := f.toAlgebra
  constructor
  intro X Y a b
  apply ModuleCat.ExtendScalars.hom_ext
  intro x
  change (1 : A) ⊗ₜ[R,f] (a x + b x) =
    (1 : A) ⊗ₜ[R,f] a x + (1 : A) ⊗ₜ[R,f] b x
  exact TensorProduct.tmul_add _ _ _

/-- Extending the coefficients of a homogeneous map is linear over the source ring. -/
private def extendCochainLinearMap
    (K L : CochainComplex (ModuleCat.{max uR uA uM} R) ℤ) (n : ℤ) :
    Cochain K L n →ₗ[R]
      (ModuleCat.restrictScalars.{max uR uA uM, uR, uA} f).obj
        (ModuleCat.of A (Cochain ((CochainComplex.extendScalarsLarge.{uM, uR, uA} f).obj K)
          ((CochainComplex.extendScalarsLarge.{uM, uR, uA} f).obj L) n)) where
  toFun z := z.map (ModuleCat.extendScalars.{uR, uA, max uR uA uM} f)
  map_add' z w := Cochain.map_add z w _
  map_smul' r z := by
    apply Cochain.ext
    intro p q hpq
    apply ModuleCat.ExtendScalars.hom_ext
    intro x
    change (1 : A) ⊗ₜ[R,f] (r • (z.v p q hpq) x) =
      f r • ((1 : A) ⊗ₜ[R,f] (z.v p q hpq) x)
    let := f.toAlgebra
    rw [TensorProduct.tmul_smul, ← algebraMap_smul A r]
    rfl

/-- The coefficient map from the Hom complex commutes with its differential. -/
private def homComplexExtendScalarsMap
    (K L : CochainComplex (ModuleCat.{max uR uA uM} R) ℤ) :
    HomComplexR R K L ⟶ (CochainComplex.restrictScalarsLarge.{uM, uR, uA} f).obj
      (HomComplexR A ((CochainComplex.extendScalarsLarge.{uM, uR, uA} f).obj K)
        ((CochainComplex.extendScalarsLarge.{uM, uR, uA} f).obj L)) where
  f n := ModuleCat.ofHom
    (Y := (ModuleCat.restrictScalars.{max uR uA uM, uR, uA} f).obj
      ((HomComplexR A ((CochainComplex.extendScalarsLarge.{uM, uR, uA} f).obj K)
        ((CochainComplex.extendScalarsLarge.{uM, uR, uA} f).obj L)).X n))
    (extendCochainLinearMap.{uR, uA, uM} f K L n)
  comm' n m _ := ModuleCat.hom_ext (LinearMap.ext fun z ↦
    δ_map n m z (ModuleCat.extendScalars.{uR, uA, max uR uA uM} f))

/-- Scalar extension of Hom complexes is the adjoint of extension of coefficients. -/
private def homComplexBaseChange
    (K L : CochainComplex (ModuleCat.{max uR uA uM} R) ℤ) :
    (CochainComplex.extendScalarsLarge.{uM, uR, uA} f).obj (HomComplexR R K L) ⟶
      HomComplexR A ((CochainComplex.extendScalarsLarge.{uM, uR, uA} f).obj K)
        ((CochainComplex.extendScalarsLarge.{uM, uR, uA} f).obj L) :=
  (((ModuleCat.extendRestrictScalarsAdj.{max uR uM, uR, uA} f).mapHomologicalComplex
    (.up ℤ)).homEquiv _ _).symm (homComplexExtendScalarsMap.{uR, uA, uM} f K L)

/-- On a tensor with scalar one, base change extends each component of the cochain. -/
private lemma homComplexBaseChange_f_one_tmul
    (K L : CochainComplex (ModuleCat.{max uR uA uM} R) ℤ)
    (n : ℤ) (z : Cochain K L n) :
    (homComplexBaseChange.{uR, uA, uM} f K L).f n ((1 : A) ⊗ₜ[R,f] z) =
      z.map (ModuleCat.extendScalars.{uR, uA, max uR uA uM} f) :=
  congrArg (fun g => g.f n z)
    ((((ModuleCat.extendRestrictScalarsAdj.{max uR uM, uR, uA} f).mapHomologicalComplex
      (.up ℤ)).homEquiv _ _).apply_symm_apply (homComplexExtendScalarsMap.{uR, uA, uM} f K L))

/-- The base-change map sends a pure tensor to the scalar multiple of the extended cochain. -/
private lemma homComplexBaseChange_f_tmul
    (K L : CochainComplex (ModuleCat.{max uR uA uM} R) ℤ)
    (n : ℤ) (a : A) (z : Cochain K L n) :
    (homComplexBaseChange.{uR, uA, uM} f K L).f n (a ⊗ₜ[R,f] z) =
      a • z.map (ModuleCat.extendScalars.{uR, uA, max uR uA uM} f) := by
  rw [show a ⊗ₜ[R,f] z = a • ((1 : A) ⊗ₜ[R,f] z :
      (ModuleCat.extendScalars f).obj (ModuleCat.of R (Cochain K L n))) from by
    change a ⊗ₜ[R,f] z = (a * 1) ⊗ₜ[R,f] z
    rw [mul_one]]
  exact ((homComplexBaseChange.{uR, uA, uM} f K L).f n).hom.map_smul a
    ((1 : A) ⊗ₜ[R,f] z) |>.trans (congrArg (a • ·)
      (homComplexBaseChange_f_one_tmul.{uR, uA, uM} f K L n z))

/-- On homogeneous tensors, base change is the usual scalar-extension evaluation. -/
private lemma homComplexBaseChange_f_tmul_v
    (K L : CochainComplex (ModuleCat.{max uR uA uM} R) ℤ)
    (n : ℤ) (a b : A) (z : Cochain K L n)
    (p q : ℤ) (hpq : p + n = q) (x : K.X p) :
    (((homComplexBaseChange.{uR, uA, uM} f K L).f n (a ⊗ₜ[R,f] z)).v p q hpq)
        (b ⊗ₜ[R,f] x) =
      (a * b) ⊗ₜ[R,f] (z.v p q hpq) x := by
  rw [homComplexBaseChange_f_tmul]
  change a • ((ModuleCat.extendScalars f).map (z.v p q hpq) (b ⊗ₜ[R,f] x)) = _
  rw [ModuleCat.ExtendScalars.map_tmul, ModuleCat.ExtendScalars.smul_tmul]

/-- The scalar-adjunction comparison sends the base-changed cochain to tensor evaluation. -/
private lemma homComplexChangeOfRingsMap_baseChange_f_tmul
    (K L I : CochainComplex (ModuleCat.{max uR uA uM} R) ℤ)
    (J : CochainComplex (ModuleCat.{max uR uA uM} A) ℤ)
    (j : (CochainComplex.extendScalarsLarge.{uM, uR, uA} f).obj L ⟶ J)
    (q : (CochainComplex.restrictScalarsLarge.{uM, uR, uA} f).obj J ⟶ I)
    (n : ℤ) (a : A) (z : Cochain K L n) (p r : ℤ) (hpr : p + n = r)
    (x : K.X p) :
    (((Stacks.DerivedHom.BaseChange.homComplexChangeOfRingsMap.{uR, uA, uM} f K J I q).f n
      ((Stacks.HomComplex.TensorHomMap.postcomp A _ _ J j).f n
        ((homComplexBaseChange.{uR, uA, uM} f K L).f n (a ⊗ₜ[R,f] z)))).v p r hpr) x =
      q.f r (j.f r (a ⊗ₜ[R,f] (z.v p r hpr) x)) := by
  rw [Stacks.DerivedHom.BaseChange.homComplexChangeOfRingsMap_f_apply]
  rw [ModuleCat.comp_apply, ModuleCat.extendRestrictScalarsAdj_homEquiv_apply]
  change q.f r (((((homComplexBaseChange.{uR, uA, uM} f K L).f n
    (a ⊗ₜ[R,f] z)).comp (Cochain.ofHom j) (add_zero n)).v p r hpr)
      ((1 : A) ⊗ₜ[R,f] x)) = _
  rw [Cochain.comp_zero_cochain_v, Cochain.ofHom_v, ModuleCat.comp_apply,
    homComplexBaseChange_f_tmul_v, mul_one]

end HomComplexBaseChange

section HomComplexProjection

universe u

open CategoryTheory.MonoidalCategory CochainComplex CochainComplex.HomComplex
open scoped TensorProduct ChangeOfRings

set_option backward.isDefEq.respectTransparency false

/-- The scalar-extension comparison of Hom complexes is the tensor--Hom diagonal
under the termwise projection formula. -/
private lemma homComplexBaseChange_projection
    {R A : Type u} [CommRing R] [CommRing A] (f : R →+* A)
    (K L I : CochainComplex (ModuleCat.{u} R) ℤ)
    (J : CochainComplex (ModuleCat.{u} A) ℤ)
    (j : (CochainComplex.extendScalarsLarge f).obj L ⟶ J)
    (q : (CochainComplex.restrictScalarsLarge f).obj J ⟶ I) :
    let B := (CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj
      ((ModuleCat.restrictScalars f).obj (ModuleCat.of A A))
    (CochainComplex.restrictScalarsLarge f).map
        (homComplexBaseChange f K L ≫
          Stacks.HomComplex.TensorHomMap.postcomp A _ _ J j) ≫
        Stacks.DerivedHom.BaseChange.homComplexChangeOfRingsMap f K J I q =
      (extensionRestrictionComplexIso f).hom.app (HomComplexR R K L) ≫
        Stacks.HomComplex.TensorHomComparison.theta B L K ≫
        Stacks.HomComplex.TensorHomMap.postcomp R K (B ⊗ L) I
          ((extensionRestrictionComplexIso f).inv.app L ≫
            (CochainComplex.restrictScalarsLarge f).map j ≫ q) := by
  let B := (CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj
    ((ModuleCat.restrictScalars f).obj (ModuleCat.of A A))
  ext n : 1
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro a z
  change A at a
  change Cochain K L n at z
  apply Cochain.ext
  intro p r hpr
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change (((Stacks.DerivedHom.BaseChange.homComplexChangeOfRingsMap f K J I q).f n
      ((Stacks.HomComplex.TensorHomMap.postcomp A _ _ J j).f n
        ((homComplexBaseChange f K L).f n (a ⊗ₜ[R,f] z)))).v p r hpr) x = _
  rw [homComplexChangeOfRingsMap_baseChange_f_tmul]
  simp only [HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply]
  rw [extensionRestrictionComplexIso_hom_app_f]
  change _ = (((Stacks.HomComplex.TensorHomMap.postcomp R K (B ⊗ L) I
    ((extensionRestrictionComplexIso f).inv.app L ≫
      (CochainComplex.restrictScalarsLarge f).map j ≫ q)).f n
      ((Stacks.HomComplex.TensorHomComparison.theta B L K).f n
        ((HomologicalComplex.ιTensorObj B (HomComplexR R K L) 0 n n (zero_add n))
          (TensorProduct.tmul R (show B.X 0 from a) z)))).v p r hpr) x
  change _ = ((((Stacks.HomComplex.TensorHomComparison.theta B L K).f n _).comp
    (Cochain.ofHom ((extensionRestrictionComplexIso f).inv.app L ≫
      (CochainComplex.restrictScalarsLarge f).map j ≫ q)) (add_zero n)).v p r hpr) x
  rw [Cochain.comp_zero_cochain_v, Cochain.ofHom_v, ModuleCat.comp_apply]
  change _ = ((extensionRestrictionComplexIso f).inv.app L ≫
    (CochainComplex.restrictScalarsLarge f).map j ≫ q).f r
      (((Stacks.HomComplex.TensorHomComparison.thetaDeg B L K n)
        ((HomologicalComplex.ιTensorObj B (HomComplexR R K L) 0 n n (zero_add n))
          (TensorProduct.tmul R (show B.X 0 from a) z))).v p r hpr x)
  rw [Stacks.HomComplex.TensorHomComparison.theta_apply]
  simp only [Stacks.HomComplex.TensorHomComparison.canonicalC_apply]
  have he := congrArg (fun g => g.f r (a ⊗ₜ[R,f] (z.v p r hpr) x))
    ((extensionRestrictionComplexIso f).app L).hom_inv_id
  rw [HomologicalComplex.comp_f, ModuleCat.comp_apply, Iso.app_hom,
    extensionRestrictionComplexIso_hom_app_f] at he
  change ((extensionRestrictionComplexIso f).inv.app L).f r
    ((HomologicalComplex.ιTensorObj B L 0 r r (zero_add r))
      (TensorProduct.tmul R (show B.X 0 from a) ((z.v p r hpr) x))) =
    a ⊗ₜ[R,f] (z.v p r hpr) x at he
  have he' (s : ℤ) (h0 : 0 + s = r) (hp : p + n = s) :
      ((extensionRestrictionComplexIso f).inv.app L).f r
        ((HomologicalComplex.ιTensorObj B L 0 s r h0)
          (TensorProduct.tmul R (show B.X 0 from a) ((z.v p s hp) x))) =
        a ⊗ₜ[R,f] (z.v p r hpr) x := by
    have hs : s = r := by simpa using h0
    cases hs
    exact he
  simp only [HomologicalComplex.comp_f, ModuleCat.comp_apply]
  apply congrArg (fun y => q.f r (j.f r y))
  exact (he' (r - 0) (by omega) (by omega)).symm

end HomComplexProjection

section HomModelComparison

universe u

set_option backward.isDefEq.respectTransparency false in
/-- The canonical Hom model respects maps of both chosen representatives. -/
private theorem homModelIso_naturality
    {R : Type u} [CommRing R] {X X' Y Y' : DerivedCategory (ModuleCat.{u} R)}
    {K K' I I' : CochainComplex (ModuleCat.{u} R) ℤ} [I.IsKInjective] [I'.IsKInjective]
    (eK : X ≅ DerivedCategory.Q.obj K) (eK' : X' ≅ DerivedCategory.Q.obj K')
    (eI : Y ≅ DerivedCategory.Q.obj I) (eI' : Y' ≅ DerivedCategory.Q.obj I')
    (a : K' ⟶ K) (b : I ⟶ I') (g : X' ⟶ X) (h : Y ⟶ Y')
    (hg : g ≫ eK.hom = eK'.hom ≫ DerivedCategory.Q.map a)
    (hh : h ≫ eI'.hom = eI.hom ≫ DerivedCategory.Q.map b) :
    (_root_.StacksDraft.DerivedHom.DerivedInternalHom.Model.hom R).map (CategoryTheory.Prod.mkHom
      g.op h) ≫
      (Stacks.DerivedHom.BaseChange.homModelIso K' I' eK' eI').hom =
    (Stacks.DerivedHom.BaseChange.homModelIso K I eK eI).hom ≫
      DerivedCategory.Q.map ((StacksDraft.DerivedHom.Model.homComplexFunctor R).map
        (CategoryTheory.Prod.mkHom a.op b)) := by
  have hg' : eK'.inv ≫ g = DerivedCategory.Q.map a ≫ eK.inv := by
    apply (cancel_mono eK.hom).1
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [hg, Iso.inv_hom_id_assoc]
  dsimp only [Stacks.DerivedHom.BaseChange.homModelIso, Iso.trans_hom, Functor.mapIso_hom]
  rw [← Functor.map_comp_assoc]
  have hp : (g.op, h) ≫ (eK'.symm.op.prod eI').hom =
      (eK.symm.op.prod eI).hom ≫ ((DerivedCategory.Q.map a).op, DerivedCategory.Q.map b) :=
    Prod.ext (congrArg Quiver.Hom.op hg') hh
  rw [hp, Functor.map_comp_assoc]
  simpa only [Category.assoc, _root_.StacksDraft.DerivedHom.DerivedInternalHom.Model.hom,
    Stacks.DerivedHom.ScalarTransportedInternalHom.Model.homComplexIso,
      StacksDraft.DerivedHom.Model.homComplexFunctor,
    CategoryTheory.Prod.mkHom, Quiver.Hom.unop_op] using
    congrArg (fun z => (_root_.StacksDraft.DerivedHom.DerivedInternalHom.Model.hom R).map
    (eK.symm.op.prod eI).hom ≫ z)
    ((_root_.StacksDraft.DerivedHom.DerivedInternalHom.Model.adjunction R).homIso_naturality a b)

end HomModelComparison

section ComplexAdjunction

universe u

open CochainComplex HomComplex CategoryTheory.MonoidalCategory
open scoped TensorProduct

set_option backward.isDefEq.respectTransparency false

private abbrev chainTranspose {R : Type u} [CommRing R]
    {K L I : CochainComplex (ModuleCat.{u} R) ℤ} (h : K ⊗ L ⟶ I) :=
  Stacks.HomComplex.TensorHomMap.Phi R K L ≫ Stacks.HomComplex.TensorHomMap.postcomp R L (K ⊗ L) I h

private lemma chainTranspose_apply {R : Type u} [CommRing R]
    {K L I : CochainComplex (ModuleCat.{u} R) ℤ}
    (h : K ⊗ L ⟶ I) (r s t : ℤ) (hrs : s + r = t) (x : K.X r) (y : L.X s) :
    ((((chainTranspose h).f r).hom x).v s t hrs).hom y =
      (h.f t).hom ((HomologicalComplex.ιTensorObj K L r s t (by omega)).hom
        (x ⊗ₜ[R] y)) := by
  change (((Stacks.HomComplex.TensorHomMap.Phiv R K L r x).comp (Cochain.ofHom h) (add_zero r)).v s
    t hrs).hom y = _
  rw [Cochain.comp_v _ _ _ s t t hrs (add_zero t), Cochain.ofHom_v]
  exact congrArg (h.f t).hom (Phiv_v_apply R K L r x s t hrs y)

private lemma ofHom_homComplex_apply {R : Type u} [CommRing R]
    {K L I : CochainComplex (ModuleCat.{u} R) ℤ} (f : K ⟶ HomComplexR R L I)
    (r q s t : ℤ) (hrq : r + 0 = q) (hqt : s + q = t) (x : K.X r) (y : L.X s) :
    ((((Cochain.ofHom f).v r q hrq).hom x).v s t hqt).hom y =
      (((f.f r).hom x).v s t (by omega)).hom y := by
  simp only [add_zero] at hrq
  cases hrq
  rw [Cochain.ofHom_v]

private lemma curry_chainTranspose {R : Type u} [CommRing R]
    {K L I : CochainComplex (ModuleCat.{u} R) ℤ}
    (h : K ⊗ L ⟶ I) :
    ((Stacks.HomComplex.Currying.curryIso K L I).hom.f 0).hom
      (Cochain.ofHom (chainTranspose h)) = Cochain.ofHom h := by
  apply Cochain.ext₀
  intro t
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro r s hrs
  change r + s = t at hrs
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro x y
  change ((((Stacks.HomComplex.Currying.curryIso K L I).hom.f 0).hom
    (Cochain.ofHom (chainTranspose h))).v t t (add_zero t)).hom
      ((HomologicalComplex.ιTensorObj K L r s t hrs).hom (x ⊗ₜ[R] y)) = _
  rw [curryIso_zero_apply]
  rw [ofHom_homComplex_apply]
  exact chainTranspose_apply h r s t (by omega) x y

private def chainUntranspose {R : Type u} [CommRing R] {K L I : CochainComplex (ModuleCat.{u} R) ℤ}
    (f : K ⟶ HomComplexR R L I) : K ⊗ L ⟶ I :=
  Cocycle.homOf (StacksDraft.DerivedHom.Construction.homCocyclesMap
      (Stacks.HomComplex.Currying.curryIso K L I).hom 0
    (Cocycle.ofHom f))

private lemma chainTranspose_untranspose {R : Type u} [CommRing R]
    {K L I : CochainComplex (ModuleCat.{u} R) ℤ}
    (f : K ⟶ HomComplexR R L I) : chainTranspose (chainUntranspose f) = f := by
  apply Cochain.ofHom_injective
  apply (ConcreteCategory.bijective_of_isIso
    ((HomologicalComplex.eval _ _ 0).map (Stacks.HomComplex.Currying.curryIso K L I).hom)).injective
  change ((Stacks.HomComplex.Currying.curryIso K L I).hom.f 0).hom
    (Cochain.ofHom (chainTranspose (chainUntranspose f))) = _
  rw [curry_chainTranspose]
  exact Cocycle.cochain_ofHom_homOf_eq_coe _

private lemma chainUntranspose_apply {R : Type u} [CommRing R]
    {K L I : CochainComplex (ModuleCat.{u} R) ℤ}
    (f : K ⟶ HomComplexR R L I) (r s t : ℤ) (hrs : r + s = t)
    (x : K.X r) (y : L.X s) :
    ((chainUntranspose f).f t).hom
      ((HomologicalComplex.ιTensorObj K L r s t hrs).hom (x ⊗ₜ[R] y)) =
      (((f.f r).hom x).v s t (by omega)).hom y := by
  rw [← chainTranspose_apply (chainUntranspose f) r s t (by omega) x y,
    chainTranspose_untranspose]

private lemma chainTranspose_injective {R : Type u} [CommRing R]
    {P L I : CochainComplex (ModuleCat.{u} R) ℤ} :
    Function.Injective (chainTranspose : (P ⊗ L ⟶ I) → _) := by
  intro a b h
  apply Cochain.ofHom_injective
  rw [← curry_chainTranspose a, ← curry_chainTranspose b, h]


/-- Transposition identifies chain maps out of a tensor product with chain maps
into the Hom complex. -/
private def chainHomEquiv {R : Type u} [CommRing R]
    (K L I : CochainComplex (ModuleCat.{u} R) ℤ) :
    (K ⊗ L ⟶ I) ≃ (K ⟶ HomComplexR R L I) where
  toFun := chainTranspose
  invFun := chainUntranspose
  left_inv h := chainTranspose_injective (chainTranspose_untranspose (chainTranspose h))
  right_inv := chainTranspose_untranspose

private lemma homComplexFunctor_map_apply {R : Type u} [CommRing R]
    {K K' I I' : CochainComplex (ModuleCat.{u} R) ℤ} (f : K' ⟶ K) (g : I ⟶ I') (n : ℤ)
    (z : Cochain K I n) (p q : ℤ) (hpq : p + n = q) (x : K'.X p) :
    (((((StacksDraft.DerivedHom.Model.homComplexFunctor R).map
      (show (Opposite.op K, I) ⟶ (Opposite.op K', I') from (f.op, g))).f n).hom z).v
        p q hpq).hom x =
      (g.f q).hom ((z.v p q hpq).hom ((f.f p).hom x)) := by
  change ((((Cochain.ofHom f).comp z (zero_add n)).comp
    (Cochain.ofHom g) (add_zero n)).v p q hpq).hom x = _
  simp only [Cochain.comp_zero_cochain_v, Cochain.zero_cochain_comp_v, Cochain.ofHom_v]
  rfl

/-- The Hom-complex functor acts on a map of targets by postcomposition. -/
private lemma homComplexFunctor_map_id_apply {R : Type u} [CommRing R]
    {K I I' : CochainComplex (ModuleCat.{u} R) ℤ} (g : I ⟶ I') (n : ℤ)
    (z : Cochain K I n) (p q : ℤ) (hpq : p + n = q) (x : K.X p) :
    (((((StacksDraft.DerivedHom.Model.homComplexFunctor R).map
      (show (Opposite.op K, I) ⟶ (Opposite.op K, I') from (𝟙 _, g))).f n).hom z).v
        p q hpq).hom x = (g.f q).hom ((z.v p q hpq).hom x) := by
  simpa using homComplexFunctor_map_apply (𝟙 K) g n z p q hpq x

/-- Chain maps into a Hom complex are equal when they agree on all components of all values. -/
private lemma hom_ext_homComplex {R : Type u} [CommRing R]
    {K L I : CochainComplex (ModuleCat.{u} R) ℤ} {φ ψ : K ⟶ HomComplexR R L I}
    (h : ∀ (n : ℤ) (x : K.X n) (p q : ℤ) (hpq : p + n = q) (y : L.X p),
      (((φ.f n).hom x).v p q hpq).hom y = (((ψ.f n).hom x).v p q hpq).hom y) : φ = ψ := by
  ext n : 1
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply Cochain.ext
  intro p q hpq
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  exact h n x p q hpq

private lemma chainTranspose_naturality {R : Type u} [CommRing R]
    {K K' L L' I I' : CochainComplex (ModuleCat.{u} R) ℤ} (f : K' ⟶ K) (g : L' ⟶ L) (h : I ⟶ I')
    (a : K ⊗ L ⟶ I) :
    chainTranspose ((f ⊗ₘ g) ≫ a ≫ h) =
      f ≫ chainTranspose a ≫ (StacksDraft.DerivedHom.Model.homComplexFunctor R).map
        (show (Opposite.op L, I) ⟶ (Opposite.op L', I') from (g.op, h)) := by
  apply hom_ext_homComplex
  intro n x p q hpq y
  change ((((chainTranspose ((f ⊗ₘ g) ≫ a ≫ h)).f n).hom x).v p q hpq).hom y =
    (((((StacksDraft.DerivedHom.Model.homComplexFunctor R).map
        (show (Opposite.op L, I) ⟶ (Opposite.op L', I') from (g.op, h))).f n).hom
      (((chainTranspose a).f n).hom ((f.f n).hom x))).v p q hpq).hom y
  rw [chainTranspose_apply, homComplexFunctor_map_apply, chainTranspose_apply]
  change (h.f q).hom ((a.f q).hom (((f ⊗ₘ g).f q).hom
      ((HomologicalComplex.ιTensorObj K' L' n p q (by omega)).hom (x ⊗ₜ[R] y)))) = _
  congr 2
  change ((HomologicalComplex.ιTensorObj K' L' n p q (by omega) ≫
    (f ⊗ₘ g).f q).hom (x ⊗ₜ[R] y)) = _
  rw [CochainComplex.ιTensorObj_tensorHom]
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
  rfl


/-- Tensoring with a complex is left adjoint to its Hom-complex functor. -/
private def tensorHomComplexAdjunction {R : Type u} [CommRing R]
    (K : CochainComplex (ModuleCat.{u} R) ℤ) :
    tensorRight K ⊣ (Functor.curry.obj (StacksDraft.DerivedHom.Model.homComplexFunctor R)).obj
      (Opposite.op K) :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun P I => chainHomEquiv P K I
      homEquiv_naturality_left_symm := by
        intro P P' I f g
        apply chainTranspose_injective
        change chainTranspose (chainUntranspose (f ≫ g)) =
          chainTranspose ((f ▷ K) ≫ chainUntranspose g)
        rw [chainTranspose_untranspose]
        have h := chainTranspose_naturality f (𝟙 K) (𝟙 I) (chainUntranspose g)
        have hi : (StacksDraft.DerivedHom.Model.homComplexFunctor R).map
            (show (Opposite.op K, I) ⟶ (Opposite.op K, I) from (𝟙 _, 𝟙 _)) = 𝟙 _ :=
          (StacksDraft.DerivedHom.Model.homComplexFunctor R).map_id _
        simp only [Category.comp_id, chainTranspose_untranspose, op_id, tensorHom_id] at h
        rw [hi] at h
        erw [Category.comp_id] at h
        exact h.symm
      homEquiv_naturality_right := by
        intro P I I' f g
        change chainTranspose (f ≫ g) = chainTranspose f ≫
          (StacksDraft.DerivedHom.Model.homComplexFunctor R).map
            (show (Opposite.op K, I) ⟶ (Opposite.op K, I') from (𝟙 _, g))
        have h := chainTranspose_naturality (𝟙 P) (𝟙 K) g f
        simpa only [chainHomEquiv, id_tensorHom_id, Category.id_comp, op_id,
          Functor.curry_obj_obj_map, CategoryTheory.Prod.mkHom, Equiv.coe_fn_mk] using h }

/-- The degreewise scalar adjunction on Hom complexes. -/
private abbrev homComplexScalarAdjunction {R A : Type u} [CommRing R] [CommRing A]
    (f : R →+* A) (K : CochainComplex (ModuleCat.{u} R) ℤ)
    (J : CochainComplex (ModuleCat.{u} A) ℤ) :=
  Stacks.DerivedHom.BaseChange.homComplexChangeOfRingsMap.{u, u, u} f K J
    ((CochainComplex.restrictScalarsLarge f).obj J) (𝟙 _)

/-- The scalar-adjunction map on a homogeneous cochain is the termwise adjunction. -/
private lemma homComplexScalarAdjunction_f_apply
    {R A : Type u} [CommRing R] [CommRing A] (f : R →+* A)
    (K : CochainComplex (ModuleCat.{u} R) ℤ)
    (J : CochainComplex (ModuleCat.{u} A) ℤ) (n : ℤ)
    (z : Cochain ((CochainComplex.extendScalarsLarge f).obj K) J n)
    (p r : ℤ) (hpr : p + n = r) :
    (((homComplexScalarAdjunction f K J).f n) z).v p r hpr =
      (ModuleCat.extendRestrictScalarsAdj f).homEquiv (K.X p) (J.X r) (z.v p r hpr) := by
  rw [Stacks.DerivedHom.BaseChange.homComplexChangeOfRingsMap_f_apply]
  simp only [HomologicalComplex.id_f]
  erw [Category.comp_id]

/-- The scalar adjunction is an isomorphism in every degree of the Hom complex. -/
@[sga "4 XVII 1.1.12" "special case"]
private lemma isIso_homComplexScalarAdjunction
    {R A : Type u} [CommRing R] [CommRing A] (f : R →+* A)
    (K : CochainComplex (ModuleCat.{u} R) ℤ)
    (J : CochainComplex (ModuleCat.{u} A) ℤ) :
    IsIso (homComplexScalarAdjunction f K J) := by
  have (n : ℤ) : Function.Bijective ((homComplexScalarAdjunction f K J).f n) := by
    constructor
    · intro z w h
      apply Cochain.ext
      intro p r hpr
      apply ((ModuleCat.extendRestrictScalarsAdj f).homEquiv (K.X p) (J.X r)).injective
      rw [← homComplexScalarAdjunction_f_apply f K J n z p r hpr,
        ← homComplexScalarAdjunction_f_apply f K J n w p r hpr, h]
    · intro z
      refine ⟨Cochain.mk (fun p r hpr =>
        ((ModuleCat.extendRestrictScalarsAdj f).homEquiv (K.X p) (J.X r)).symm
          (z.v p r hpr)), ?_⟩
      apply Cochain.ext
      intro p r hpr
      rw [homComplexScalarAdjunction_f_apply]
      exact Equiv.apply_symm_apply _ _
  have (n : ℤ) : IsIso ((homComplexScalarAdjunction f K J).f n) :=
    (ConcreteCategory.isIso_iff_bijective _).2 (this n)
  exact HomologicalComplex.Hom.isIso_of_components _


/-- The Hom-complex scalar adjunction is natural in its target. -/
private lemma homComplexScalarAdjunction_naturality
    {R A : Type u} [CommRing R] [CommRing A] (f : R →+* A)
    (K : CochainComplex (ModuleCat.{u} R) ℤ)
    {J J' : CochainComplex (ModuleCat.{u} A) ℤ} (g : J ⟶ J') :
    (CochainComplex.restrictScalarsLarge f).map
        ((StacksDraft.DerivedHom.Model.homComplexFunctor A).map
          (show (Opposite.op ((CochainComplex.extendScalarsLarge f).obj K), J) ⟶
            (Opposite.op ((CochainComplex.extendScalarsLarge f).obj K), J') from (𝟙 _, g))) ≫
      homComplexScalarAdjunction f K J' =
    homComplexScalarAdjunction f K J ≫
      (StacksDraft.DerivedHom.Model.homComplexFunctor R).map
        (show (Opposite.op K, (CochainComplex.restrictScalarsLarge f).obj J) ⟶
          (Opposite.op K, (CochainComplex.restrictScalarsLarge f).obj J') from
            (𝟙 _, (CochainComplex.restrictScalarsLarge f).map g)) := by
  let := f.toAlgebra
  apply hom_ext_homComplex
  intro n z p q hpq x
  change Cochain ((CochainComplex.extendScalarsLarge f).obj K) J n at z
  change (((homComplexScalarAdjunction f K J').f n
      (((StacksDraft.DerivedHom.Model.homComplexFunctor A).map
        (show (Opposite.op ((CochainComplex.extendScalarsLarge f).obj K), J) ⟶
          (Opposite.op ((CochainComplex.extendScalarsLarge f).obj K), J') from (𝟙 _, g))).f n z)).v
            p q hpq).hom x = _
  rw [homComplexScalarAdjunction_f_apply]
  simp only
  erw [homComplexFunctor_map_id_apply g n z p q hpq]
  change _ = (((((StacksDraft.DerivedHom.Model.homComplexFunctor R).map
      (show (Opposite.op K, (CochainComplex.restrictScalarsLarge f).obj J) ⟶
        (Opposite.op K, (CochainComplex.restrictScalarsLarge f).obj J') from
          (𝟙 _, (CochainComplex.restrictScalarsLarge f).map g))).f n).hom
      ((homComplexScalarAdjunction f K J).f n z)).v p q hpq).hom x
  erw [homComplexFunctor_map_id_apply _ n _ p q hpq]
  simp only [homComplexScalarAdjunction_f_apply]
  rfl

/-- The scalar adjunction identifies the two Hom-complex functors. -/
private def homComplexScalarAdjunctionIso
    {R A : Type u} [CommRing R] [CommRing A] (f : R →+* A)
    (K : CochainComplex (ModuleCat.{u} R) ℤ) :
    (Functor.curry.obj (StacksDraft.DerivedHom.Model.homComplexFunctor A)).obj
        (Opposite.op ((CochainComplex.extendScalarsLarge f).obj K)) ⋙
          CochainComplex.restrictScalarsLarge f ≅
      CochainComplex.restrictScalarsLarge f ⋙
        (Functor.curry.obj (StacksDraft.DerivedHom.Model.homComplexFunctor R)).obj (Opposite.op K)
          := by
  have (J : CochainComplex (ModuleCat.{u} A) ℤ) := isIso_homComplexScalarAdjunction f K J
  exact NatIso.ofComponents (fun J => asIso (homComplexScalarAdjunction f K J))
    (fun g => homComplexScalarAdjunction_naturality f K g)

/-- **The chain-level comparison of the two tensor products across a ring map.**  Extension of
scalars along `f : R → A` commutes with tensoring complexes; at a complex `P` of `R`-modules the
component is the canonical map

`(P ⊗_R K) ⊗_R A ⟶ (P ⊗_R A) ⊗_A (K ⊗_R A)`,

pinned on pure tensors by
`Stacks.DerivedHom.BaseChangeIso.tensorExtendScalarsIso_hom_app_f_one_tmul`.

This is the tensor side of the change-of-rings comparison, against which the Hom-side map
`Stacks.DerivedHom.BaseChange.homComplexChangeOfRingsMap` is compared in
`Stacks.DerivedHom.BaseChangeIso.homComplexChangeOfRingsMap_uncurry`. -/
@[no_expose]
def tensorExtendScalarsIso
    {R A : Type u} [CommRing R] [CommRing A] (f : R →+* A)
    (K : CochainComplex (ModuleCat.{u} R) ℤ) :
    tensorRight K ⋙ CochainComplex.extendScalarsLarge f ≅
      CochainComplex.extendScalarsLarge f ⋙ tensorRight ((CochainComplex.extendScalarsLarge f).obj
        K) := by
  let a := (ModuleCat.extendRestrictScalarsAdj.{u, u, u} f).mapHomologicalComplex (.up ℤ)
  exact ((tensorHomComplexAdjunction K).comp a).leftAdjointUniq
    ((a.comp (tensorHomComplexAdjunction ((CochainComplex.extendScalarsLarge f).obj
      K))).ofNatIsoRight
      (homComplexScalarAdjunctionIso f K))


/-- Tensor compatibility is normalized by the scalar and tensor--Hom adjunctions. -/
private lemma tensorExtendScalarsIso_homEquiv
    {R A : Type u} [CommRing R] [CommRing A] (f : R →+* A)
    (P K : CochainComplex (ModuleCat.{u} R) ℤ)
    (J : CochainComplex (ModuleCat.{u} A) ℤ)
    (g : (CochainComplex.extendScalarsLarge f).obj P ⊗ (CochainComplex.extendScalarsLarge f).obj K ⟶
      J) :
    chainTranspose
        (((ModuleCat.extendRestrictScalarsAdj.{u, u, u} f).mapHomologicalComplex (.up ℤ)).homEquiv
          (P ⊗ K) J ((tensorExtendScalarsIso f K).hom.app P ≫ g)) =
      (((ModuleCat.extendRestrictScalarsAdj.{u, u, u} f).mapHomologicalComplex (.up ℤ)).homEquiv
        P (HomComplexR A ((CochainComplex.extendScalarsLarge f).obj K) J) (chainTranspose g)) ≫
          homComplexScalarAdjunction f K J := by
  let a := (ModuleCat.extendRestrictScalarsAdj.{u, u, u} f).mapHomologicalComplex (.up ℤ)
  let b := (tensorHomComplexAdjunction K).comp a
  let c := (a.comp (tensorHomComplexAdjunction ((CochainComplex.extendScalarsLarge f).obj
    K))).ofNatIsoRight
    (homComplexScalarAdjunctionIso f K)
  have h : b.homEquiv _ _ ((b.leftAdjointUniq c).hom.app P ≫ g) = c.homEquiv _ _ g := by
    rw [b.homEquiv_naturality_right, Adjunction.homEquiv_leftAdjointUniq_hom_app,
      Adjunction.homEquiv_unit]
    rfl
  simp only [b, c, a, Adjunction.comp_homEquiv,
    Adjunction.homEquiv_ofNatIsoRight_apply, tensorHomComplexAdjunction,
    Adjunction.mkOfHomEquiv_homEquiv, chainHomEquiv,
    homComplexScalarAdjunctionIso,
    NatIso.ofComponents_hom_app, asIso_hom] at h
  exact h


/-- **The tensor-side comparison on pure tensors.**  `tensorExtendScalarsIso` extends both factors
by the scalar unit: `1 ⊗ (x ⊗ y) ↦ (1 ⊗ x) ⊗ (1 ⊗ y)`.  Since the source is generated over `A` by
the elements `1 ⊗ z` with `z` a pure tensor, this pins the comparison outright. -/
lemma tensorExtendScalarsIso_hom_app_f_one_tmul
    {R A : Type u} [CommRing R] [CommRing A] (f : R →+* A)
    (P K : CochainComplex (ModuleCat.{u} R) ℤ)
    (r s n : ℤ) (hrs : r + s = n) (x : P.X r) (y : K.X s) :
    letI := f.toAlgebra
    (((tensorExtendScalarsIso f K).hom.app P).f n).hom
        ((1 : A) ⊗ₜ[R] (HomologicalComplex.ιTensorObj P K r s n hrs).hom (x ⊗ₜ[R] y)) =
      (HomologicalComplex.ιTensorObj ((CochainComplex.extendScalarsLarge f).obj P)
        ((CochainComplex.extendScalarsLarge f).obj K) r s n hrs).hom
        (((1 : A) ⊗ₜ[R] x) ⊗ₜ[A] ((1 : A) ⊗ₜ[R] y)) := by
  let := f.toAlgebra
  let J := (CochainComplex.extendScalarsLarge f).obj P ⊗ (CochainComplex.extendScalarsLarge f).obj K
  have h := tensorExtendScalarsIso_homEquiv f P K J (𝟙 J)
  erw [Category.comp_id] at h
  have h' := congrArg (fun w : P ⟶ HomComplexR R K ((CochainComplex.restrictScalarsLarge f).obj J)
    =>
    (((w.f r).hom x).v s n (by omega)).hom y) h
  rw [chainTranspose_apply] at h'
  change (((tensorExtendScalarsIso f K).hom.app P).f n).hom
      ((1 : A) ⊗ₜ[R] (HomologicalComplex.ιTensorObj P K r s n hrs).hom (x ⊗ₜ[R] y)) =
    (((homComplexScalarAdjunction f K J).f r
      ((chainTranspose (𝟙 J)).f r ((1 : A) ⊗ₜ[R] x))).v s n (by omega)).hom y at h'
  erw [homComplexScalarAdjunction_f_apply,
    ModuleCat.extendRestrictScalarsAdj_homEquiv_apply, chainTranspose_apply] at h'
  exact h'


end ComplexAdjunction

end Stacks.DerivedHom.BaseChangeIso

end
