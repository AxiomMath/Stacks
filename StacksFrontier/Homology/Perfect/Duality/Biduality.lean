module

public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexSingle
public import Mathlib.Algebra.Homology.SingleHomology
public import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
public import StacksFrontier.Algebra.Homology.KoszulSymmetric
public import StacksFrontier.Homology.HomComplex.ProjectiveRHom
public import StacksFrontier.Homology.KFlat.Flat
public import StacksFrontier.Homology.KFlat.Resolution
public import StacksFrontier.Homology.LeftDual
public import StacksFrontier.Homology.Perfect.Basic
public import StacksFrontier.Homology.Perfect.Duality.DerivedDual
import StacksCore.Tactic.StacksAttribute

/-!
# Biduality for perfect complexes

Let `A` be a ring and let `K` be a perfect object of `D(A)`. This file proves that the canonical
biduality morphism `StacksDraft.Perfect.biduality K : K ⟶ (Kᵛ)ᵛ` is an isomorphism, one of the
conclusions of [stacks 07VI].

## Main results

* `StacksDraft.Perfect.biduality_isIso`: for a perfect `K`, biduality is an isomorphism.

## Implementation notes

The proof chooses a bounded representative `P` of `K` with finite projective terms and identifies
`RHom(P, L)` with the Hom complex `Hom^•(P, L)` (the bifunctor form of [stacks 0A66],
`StacksDraft.DerivedHom.projectiveHomComparison`). Under this identification the biduality
morphism becomes the chain-level biduality map, whose last factor is the chain evaluation map of
[stacks 0A60], and that map is termwise the classical biduality of finite projective modules.
The comparison of derived transposes with chain-level ones (the `uncurryComplex` lemmas) is
shared with `StacksFrontier.Homology.Perfect.Duality.TensorHom`.

## References

* [Stacks Project, Tag 07VI](https://stacks.math.columbia.edu/tag/07VI)
* [Stacks Project, Tag 0A66](https://stacks.math.columbia.edu/tag/0A66)
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory CochainComplex CochainComplex.HomComplex
  HomologicalComplex

universe u v w

namespace StacksDraft.Perfect

open StacksDraft.DerivedHom Stacks.HomComplex.MonoidalClosed

variable {R : Type u} [CommRing R]
  [HasDerivedCategory.{w} (ModuleCat.{max u v} (ULift.{v} R))]

/-! ## The chain-level model of the biduality morphism -/

/-- The canonical map from the tensor unit to its Hom complex of endomorphisms. -/
private def unitToEndComplex :
    unitComplex (R := R) ⟶
      CochainComplex.HomComplexR (ULift.{v} R)
        (unitComplex (R := R)) (unitComplex (R := R)) :=
  Stacks.HomComplex.TensorHomMap.Phi (ULift.{v} R) (unitComplex (R := R)) (unitComplex (R := R)) ≫
    Stacks.HomComplex.TensorHomComparison.HomCxMap (unitComplex (R := R)) (unitComplex (R := R))
      (unitComplex (R := R) ⊗ unitComplex (R := R)) (unitComplex (R := R))
      (𝟙 (unitComplex (R := R))) (ρ_ (unitComplex (R := R))).hom

/-- The chain-level biduality map: its last factor is the chain evaluation map
of [stacks 0A60]. -/
private def bidualityComplex (P : CochainComplex (ModuleCat.{max u v} (ULift.{v} R)) ℤ) :
    P ⟶ CochainComplex.HomComplexR (ULift.{v} R)
      (CochainComplex.HomComplexR (ULift.{v} R) P (unitComplex (R := R)))
        (unitComplex (R := R)) :=
  (λ_ P).inv ≫ (unitToEndComplex (R := R) ▷ P) ≫
    ChainEvaluation.chainEvaluation P (unitComplex (R := R)) (unitComplex (R := R))

set_option backward.isDefEq.respectTransparency false in
private theorem biduality_natural
    {K K' : DerivedCategory (ModuleCat.{max u v} (ULift.{v} R))} (f : K ⟶ K') :
    f ≫ biduality K' = biduality K ≫
      (derivedHomData (R := R)).hom.map
        (((derivedHomData (R := R)).hom.map (f.op, 𝟙 (unitObject (R := R)))).op,
          𝟙 (unitObject (R := R))) := by
  let D := derivedHomData (R := R)
  apply (D.homEquiv K (derivedDual K') (unitObject (R := R))).injective
  rw [D.homEquiv_naturality_left, D.homEquiv_dinaturality]
  simp only [biduality, D, AddEquiv.apply_symm_apply]
  rw [D.tensorSwap_naturality_assoc, D.tensorSwap_naturality_assoc,
    D.evaluation_naturality_left]


section ModelComparison

set_option backward.isDefEq.respectTransparency.types false

variable {S : Type u} [CommRing S]

set_option backward.isDefEq.respectTransparency false


/-- The transpose of `f : A ⟶ Hom^•(P, M)`: the adjunction of [stacks 0A5Y]. -/
noncomputable abbrev uncurryComplex
    {A P M : CochainComplex (ModuleCat S) ℤ} (f : A ⟶ HomComplexR S P M) :
    A ⊗ P ⟶ M :=
  Stacks.HomComplex.MonoidalClosed.tensorHomEquiv A P M f

theorem uncurryComplex_apply
    {A P M : CochainComplex (ModuleCat S) ℤ} (f : A ⟶ HomComplexR S P M)
    (r s t : ℤ) (h : r + s = t) (x : A.X r) (y : P.X s) :
    (uncurryComplex f).f t ((ιTensorObj A P r s t h).hom (x ⊗ₜ[S] y)) =
      (((f.f r).hom x).v s t (by omega)).hom y := by
  show (((((Stacks.HomComplex.Currying.curryIso A P M).hom.f 0).hom
    (Cochain.ofHom f)).v t t (add_zero t)).hom
      ((ιTensorObj A P r s t h).hom (x ⊗ₜ[S] y))) = _
  have he := Stacks.HomComplex.Currying.curryIso_hom_apply A P M 0 r s t t h (add_zero t)
    (Cochain.ofHom f) x y
  have hf (q : ℤ) (hq : r + 0 = q) (hst : s + q = t) :
      ((((Cochain.ofHom f).v r q hq).hom x).v s t hst).hom y =
        (((f.f r).hom x).v s t (by omega)).hom y := by
    have hqr : q = r := by omega
    subst hqr
    rw [Cochain.ofHom_v]
  exact he.trans (hf (r + 0) rfl (by omega))

private theorem transpose_uncurryComplex
    {A P M : CochainComplex (ModuleCat S) ℤ} (f : A ⟶ HomComplexR S P M) :
    Stacks.HomComplex.TensorHomMap.Phi S A P ≫ Stacks.HomComplex.TensorHomMap.postcomp S P (A ⊗ P) M
      (uncurryComplex f) = f := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply Cochain.ext
  intro r t hrt
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro y
  show (((Stacks.HomComplex.TensorHomMap.Phiv S A P n x).comp
    (Cochain.ofHom (uncurryComplex f)) (add_zero n)).v r t hrt).hom y = _
  rw [Cochain.comp_zero_cochain_v, Cochain.ofHom_v]
  show (uncurryComplex f).f t ((Stacks.HomComplex.TensorHomMap.Phiv S A P n x).v r t hrt y) = _
  rw [phiv_v_apply]
  exact uncurryComplex_apply f n r t (by omega) x y

private theorem transpose_postcomp
    (A P M N : CochainComplex (ModuleCat S) ℤ) (h : A ⊗ P ⟶ M) (j : M ⟶ N) :
    (Stacks.HomComplex.TensorHomMap.Phi S A P ≫ Stacks.HomComplex.TensorHomMap.postcomp S P (A ⊗ P)
      M h) ≫
        Stacks.HomComplex.TensorHomComparison.HomCxMap P P M N (𝟙 P) j =
      Stacks.HomComplex.TensorHomMap.Phi S A P ≫ Stacks.HomComplex.TensorHomMap.postcomp S P (A ⊗ P)
        N (h ≫ j) := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  apply Cochain.ext
  intro p q hpq
  show (((Cochain.ofHom (𝟙 P)).comp
    (((Stacks.HomComplex.TensorHomMap.Phiv S A P n a).comp (Cochain.ofHom h) (add_zero n)).comp
      (Cochain.ofHom j) (add_zero n)) (zero_add n)).v p q hpq) =
    (((Stacks.HomComplex.TensorHomMap.Phiv S A P n a).comp (Cochain.ofHom (h ≫ j))
      (add_zero n)).v p q hpq)
  simp only [Cochain.comp_zero_cochain_v, Cochain.zero_cochain_comp_v,
    Cochain.ofHom_v, HomologicalComplex.id_f, HomologicalComplex.comp_f,
    Category.id_comp, Category.assoc]

variable [HasDerivedCategory.{w} (ModuleCat.{u} S)]

private theorem homEquiv_projective_model
    (A P M : CochainComplex (ModuleCat S) ℤ) (b : ℤ) [P.IsStrictlyLE b]
    [∀ n, Module.Projective S (P.X n)] (hP : P.KFlat) (h : A ⊗ P ⟶ M) :
    let D := derivedHomAdjunction (R := S)
    let p := projectiveHomComparison (R := S)
    D.homEquiv (DerivedCategory.Q.obj A) (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj M)
      (DerivedCategory.Q.map (Stacks.HomComplex.TensorHomMap.Phi S A P ≫
        Stacks.HomComplex.TensorHomMap.postcomp S P (A ⊗ P) M h) ≫ (p.iso P M b).inv) =
      (D.tensorIso A P hP).hom ≫ DerivedCategory.Q.map h := by
  intro D p
  obtain ⟨I, j, hj, hI⟩ := CochainComplex.exists_quasiIso_isKInjective M
  have : I.IsKInjective := hI
  have : QuasiIso j := hj
  have : IsIso (DerivedCategory.Q.map j) := inferInstance
  apply (cancel_mono (DerivedCategory.Q.map j)).mp
  rw [← D.homEquiv_naturality_right]
  have hc := p.resolution_comparison P M I b j
  change (p.iso P M b).hom ≫ _ = D.hom.map _ ≫ (D.homIso P I).hom at hc
  have hc' := congrArg (fun f => (p.iso P M b).inv ≫ f ≫ (D.homIso P I).inv) hc
  simp only [Iso.inv_hom_id_assoc, Category.assoc, Iso.hom_inv_id, Category.comp_id] at hc'
  rw [Category.assoc, ← hc', ← Category.assoc, ← Functor.map_comp,
    transpose_postcomp]
  have he := congrArg (D.homEquiv (DerivedCategory.Q.obj A)
    (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj I))
    (D.homEquiv_symm_map_eq A P I hP (h ≫ j))
  rw [AddEquiv.apply_symm_apply] at he
  simpa only [DerivedHomData.homIso, DerivedHomData.tensorIso,
    Functor.map_comp, Category.assoc] using he.symm

theorem homEquiv_uncurryComplex
    (A P M : CochainComplex (ModuleCat S) ℤ) (b : ℤ) [P.IsStrictlyLE b]
    [∀ n, Module.Projective S (P.X n)] (hP : P.KFlat) (f : A ⟶ HomComplexR S P M) :
    let D := derivedHomAdjunction (R := S)
    let p := projectiveHomComparison (R := S)
    D.homEquiv (DerivedCategory.Q.obj A) (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj M)
      (DerivedCategory.Q.map f ≫ (p.iso P M b).inv) =
      (D.tensorIso A P hP).hom ≫ DerivedCategory.Q.map (uncurryComplex f) := by
  simpa only [transpose_uncurryComplex] using
    homEquiv_projective_model A P M b hP (uncurryComplex f)

private theorem biduality_model_of_uncurry
    (P M : CochainComplex (ModuleCat S) ℤ) (b c : ℤ)
    [P.IsStrictlyLE b] [∀ n, Module.Projective S (P.X n)]
    [(HomComplexR S P M).IsStrictlyLE c]
    [∀ n, Module.Projective S ((HomComplexR S P M).X n)]
    (hP : P.KFlat) (hE : (HomComplexR S P M).KFlat)
    (f : P ⟶ HomComplexR S (HomComplexR S P M) M)
    (hf : uncurryComplex f = (Model.complexSwap S P (HomComplexR S P M)).hom ≫
      uncurryComplex (𝟙 (HomComplexR S P M))) :
    let D := derivedHomAdjunction (R := S)
    let p := projectiveHomComparison (R := S)
    let α := (p.iso P M b).hom
    DerivedCategory.Q.map f ≫ (p.iso (HomComplexR S P M) M c).inv ≫
      D.hom.map (α.op, 𝟙 (DerivedCategory.Q.obj M)) =
      (D.homEquiv (DerivedCategory.Q.obj P)
        (D.hom.obj (Opposite.op (DerivedCategory.Q.obj P), DerivedCategory.Q.obj M))
        (DerivedCategory.Q.obj M)).symm
          ((D.tensorSwap (DerivedCategory.Q.obj P)
            (D.hom.obj (Opposite.op (DerivedCategory.Q.obj P), DerivedCategory.Q.obj M))).hom ≫
            D.evaluation (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj M)) := by
  intro D p α
  let E := HomComplexR S P M
  apply (D.homEquiv _ _ _).injective
  rw [AddEquiv.apply_symm_apply, ← Category.assoc, D.homEquiv_dinaturality,
    homEquiv_uncurryComplex P E M c hE f, hf, Functor.map_comp]
  have hs := D.tensorSwap_comparison P E hP hE
  change (D.tensorSwap (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj E)).hom ≫
    (D.tensorIso E P hP).hom = (D.tensorIso P E hE).hom ≫
      DerivedCategory.Q.map (Model.complexSwap S P E).hom at hs
  rw [← reassoc_of% hs, D.tensorSwap_naturality_assoc]
  apply (cancel_epi (D.tensorSwap (DerivedCategory.Q.obj P)
    (D.hom.obj (Opposite.op (DerivedCategory.Q.obj P), DerivedCategory.Q.obj M))).hom).mpr
  have he := homEquiv_uncurryComplex E P M b hP (𝟙 E)
  dsimp only at he
  rw [CategoryTheory.Functor.map_id, Category.id_comp] at he
  change D.homEquiv _ _ _ (p.iso P M b).inv =
    (D.tensorIso E P hP).hom ≫ DerivedCategory.Q.map (uncurryComplex (𝟙 E)) at he
  rw [← he, ← D.homEquiv_naturality_left]
  simp only [α, Iso.hom_inv_id]
  rfl

omit [HasDerivedCategory.{w} (ModuleCat.{u} S)] in
private theorem leftUnitor_inv_f_apply (P : CochainComplex (ModuleCat S) ℤ)
    (n : ℤ) (x : P.X n) :
    (λ_ P).inv.f n x =
      (ιTensorObj (𝟙_ _) P 0 n n (zero_add n)).hom
        (((singleObjXSelf (ComplexShape.up ℤ) 0 (ModuleCat.of S S)).inv.hom (1 : S)) ⊗ₜ[S] x) := by
  show (leftUnitor' P).inv n x = _
  rw [leftUnitor'_inv]
  simp only [ModuleCat.comp_apply, ModuleCat.MonoidalCategory.leftUnitor_inv_apply,
    ModuleCat.MonoidalCategory.whiskerRight_apply]
  rfl

omit [HasDerivedCategory.{w} (ModuleCat.{u} S)] in
private theorem rightUnitor_inv_f_apply (P : CochainComplex (ModuleCat S) ℤ)
    (n : ℤ) (x : P.X n) :
    (ρ_ P).inv.f n x =
      (ιTensorObj P (𝟙_ _) n 0 n (add_zero n)).hom
        (x ⊗ₜ[S] ((singleObjXSelf (ComplexShape.up ℤ) 0 (ModuleCat.of S S)).inv.hom (1 : S))) := by
  show (rightUnitor' P).inv n x = _
  rw [rightUnitor'_inv]
  simp only [ModuleCat.comp_apply, ModuleCat.MonoidalCategory.rightUnitor_inv_apply,
    ModuleCat.MonoidalCategory.whiskerLeft_apply]
  rfl

end ModelComparison

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

omit [HasDerivedCategory.{w} (ModuleCat.{max u v} (ULift.{v} R))] in
private theorem unitToEndComplex_apply
    (x : (unitComplex (R := R)).X 0) :
    let e := singleObjXSelf (ComplexShape.up ℤ) 0 (ModuleCat.of (ULift.{v} R) (ULift.{v} R))
    ((((unitToEndComplex (R := R)).f 0).hom (e.inv.hom 1)).v 0 0 (by omega)).hom x = x := by
  intro e
  show (((Cochain.ofHom (𝟙 (unitComplex (R := R)))).comp
    ((Stacks.HomComplex.TensorHomMap.Phiv (ULift.{v} R) (unitComplex (R := R)) (unitComplex (R :=
      R)) 0
      (e.inv.hom 1)).comp (Cochain.ofHom (ρ_ (unitComplex (R := R))).hom) (add_zero 0))
        (zero_add 0)).v 0 0 (by omega)).hom x = x
  rw [Cochain.zero_cochain_comp_v, Cochain.ofHom_v, HomologicalComplex.id_f,
    Category.id_comp, Cochain.comp_zero_cochain_v, Cochain.ofHom_v]
  show (ρ_ (unitComplex (R := R))).hom.f 0
    ((Stacks.HomComplex.TensorHomMap.Phiv (ULift.{v} R) (unitComplex (R := R)) (unitComplex (R :=
      R)) 0
      (e.inv.hom 1)).v 0 0 (by omega) x) = x
  rw [phiv_v_apply]
  have he := rightUnitor_inv_f_apply (unitComplex (R := R)) 0 (e.inv.hom 1)
  have hi := ConcreteCategory.congr_hom
    (HomologicalComplex.congr_hom (ρ_ (unitComplex (R := R))).inv_hom_id 0) (e.inv.hom 1)
  simp only [HomologicalComplex.comp_f, HomologicalComplex.id_f,
    ModuleCat.comp_apply, ModuleCat.id_apply] at hi
  rw [he] at hi
  obtain ⟨r, rfl⟩ := (show Function.Surjective e.inv.hom from
    (ConcreteCategory.bijective_of_isIso e.inv).surjective) x
  have hr : e.inv.hom r = r • e.inv.hom 1 := by
    simpa only [smul_eq_mul, mul_one] using (e.inv.hom.map_smul r (1 : ULift.{v} R))
  rw [hr, TensorProduct.tmul_smul, map_smul]
  rw [map_smul]
  show r • (ρ_ (unitComplex (R := R))).hom.f 0
    ((ιTensorObj (unitComplex (R := R)) (unitComplex (R := R)) 0 0 0 _).hom
      (e.inv.hom 1 ⊗ₜ[ULift.{v} R] e.inv.hom 1)) = _
  rw [hi]


omit [HasDerivedCategory.{w} (ModuleCat.{max u v} (ULift.{v} R))] in
private theorem bidualityComplex_apply
    (P : CochainComplex (ModuleCat.{max u v} (ULift.{v} R)) ℤ)
    (n : ℤ) (x : P.X n) (ψ : Cochain P (unitComplex (R := R)) (-n)) :
    ((((bidualityComplex P).f n).hom x).v (-n) 0 (by omega)).hom ψ =
      n.negOnePow • (ψ.v n 0 (by omega)).hom x := by
  let S := ULift.{v} R
  let U := unitComplex (R := R)
  let e := singleObjXSelf (ComplexShape.up ℤ) 0 (ModuleCat.of S S)
  let one : U.X 0 := e.inv.hom 1
  let φ : Cochain U U 0 := ((unitToEndComplex (R := R)).f 0).hom one
  show ((((ChainEvaluation.chainEvaluation P U U).f n).hom
    (((unitToEndComplex (R := R) ▷ P).f n).hom ((λ_ P).inv.f n x))).v
      (-n) 0 (by omega)).hom ψ = _
  rw [leftUnitor_inv_f_apply]
  have ht := CochainComplex.ιTensorObj_whiskerRight (K := U) (L := HomComplexR S U U)
    (unitToEndComplex (R := R)) P 0 n n (zero_add n)
  have ht' := ConcreteCategory.congr_hom ht (one ⊗ₜ[S] x)
  simp only [ModuleCat.comp_apply] at ht'
  show ((((ChainEvaluation.chainEvaluation P U U).f n).hom
    (((unitToEndComplex (R := R) ▷ P).f n).hom
      ((ιTensorObj U P 0 n n (zero_add n)).hom (one ⊗ₜ[S] x)))).v (-n) 0 _).hom ψ = _
  erw [ht']
  refine Eq.trans (ChainEvaluation.chainEvaluation_tmul P U U 0 n n (-n) 0 0
    (zero_add n) (by omega) (by omega) (by omega) φ x ψ) ?_
  simp only [neg_zero, zero_mul, add_zero]
  exact congrArg (fun y : U.X 0 => (n.negOnePow : ℤˣ) • y)
    (unitToEndComplex_apply ((ψ.v n 0 (by omega)).hom x))


/-- `StacksDraft.DerivedHom.Construction.complexSwap_apply`, with the component of the symmetry
applied as a function rather than through `ModuleCat.Hom.hom`: the spelling the rewrites below
need. -/
theorem complexSwap_apply
    {S : Type u} [CommRing S] (P E : CochainComplex (ModuleCat S) ℤ)
    (p q n : ℤ) (h : p + q = n) (x : P.X p) (y : E.X q) :
    (Model.complexSwap S P E).hom.f n
      ((ιTensorObj P E p q n h).hom (x ⊗ₜ[S] y)) =
      (p * q).negOnePow •
        (ιTensorObj E P q p n (by omega)).hom (y ⊗ₜ[S] x) :=
  StacksDraft.DerivedHom.Construction.complexSwap_apply P E p q n h x y


omit [HasDerivedCategory.{w} (ModuleCat.{max u v} (ULift.{v} R))] in
private theorem uncurryComplex_bidualityComplex
    (P : CochainComplex (ModuleCat.{max u v} (ULift.{v} R)) ℤ) :
    uncurryComplex (bidualityComplex P) =
      (Model.complexSwap (ULift.{v} R) P
        (HomComplexR (ULift.{v} R) P (unitComplex (R := R)))).hom ≫
          uncurryComplex (𝟙 (HomComplexR (ULift.{v} R) P (unitComplex (R := R)))) := by
  apply HomologicalComplex.Hom.ext
  funext n
  by_cases hn : n = 0
  · subst n
    apply HomologicalComplex.mapBifunctor.hom_ext
    intro p q hpq
    have hq : q = -p := by change p + q = 0 at hpq; omega
    subst q
    apply ModuleCat.hom_ext
    apply TensorProduct.ext
    apply LinearMap.ext
    intro x
    apply LinearMap.ext
    intro ψ
    show (uncurryComplex (bidualityComplex P)).f 0
      ((ιTensorObj P _ p (-p) 0 _).hom (x ⊗ₜ[ULift.{v} R] ψ)) = _
    rw [uncurryComplex_apply, bidualityComplex_apply]
    show _ = (uncurryComplex (𝟙 _)).f 0
      ((Model.complexSwap (ULift.{v} R) P _).hom.f 0
        ((ιTensorObj P _ p (-p) 0 _).hom (x ⊗ₜ[ULift.{v} R] ψ)))
    rw [complexSwap_apply]
    simp only [Units.smul_def, map_zsmul]
    rw [uncurryComplex_apply]
    simp only [HomologicalComplex.id_f, ModuleCat.id_apply, mul_neg, Int.negOnePow_neg,
      Int.negOnePow_mul_self]
  · exact (isZero_single_obj_X (ComplexShape.up ℤ) 0
      (ModuleCat.of (ULift.{v} R) (ULift.{v} R)) n hn).eq_of_tgt _ _

private theorem biduality_representation
    (K : DerivedCategory (ModuleCat.{max u v} (ULift.{v} R)))
    (P : CochainComplex (ModuleCat.{max u v} (ULift.{v} R)) ℤ) (a b : ℤ)
    [P.IsStrictlyGE a] [P.IsStrictlyLE b]
    [∀ n, Module.Finite (ULift.{v} R) (P.X n)]
    [∀ n, Module.Projective (ULift.{v} R) (P.X n)]
    (i : K ≅ DerivedCategory.Q.obj P) :
    let E := HomComplexR (ULift.{v} R) P (unitComplex (R := R))
    let D := derivedHomData (R := R)
    let p := projectiveHomComparisonULift (R := R)
    let α := D.hom.map (i.inv.op, 𝟙 (unitObject (R := R))) ≫
      (p.iso P (unitComplex (R := R)) b).hom
    ∃ (aE bE : ℤ) (_hGE : E.IsStrictlyGE aE) (hLE : E.IsStrictlyLE bE)
      (_hFinite : ∀ n, Module.Finite (ULift.{v} R) (E.X n))
      (hProjective : ∀ n, Module.Projective (ULift.{v} R) (E.X n)),
      letI := hLE
      letI := hProjective
      i.hom ≫ DerivedCategory.Q.map (bidualityComplex P) ≫
        (p.iso E (unitComplex (R := R)) bE).inv ≫
          D.hom.map (α.op, 𝟙 (unitObject (R := R))) = biduality K := by
  intro E D p α
  obtain ⟨hEa, hEb⟩ := homComplex_unit_bounded P a b
  have hEf : ∀ n, Module.Finite (ULift.{v} R) (E.X n) :=
    fun n => (homComplex_unit_finite_projective P n).1
  have hEp : ∀ n, Module.Projective (ULift.{v} R) (E.X n) :=
    fun n => (homComplex_unit_finite_projective P n).2
  refine ⟨-b, -a, hEa, hEb, hEf, hEp, ?_⟩
  have hP : P.KFlat := kFlatOfFlat P b
  have hE : E.KFlat := kFlatOfFlat E (-a)
  have hm := biduality_model_of_uncurry P (unitComplex (R := R)) b (-a) hP hE
    (bidualityComplex P) (uncurryComplex_bidualityComplex P)
  change DerivedCategory.Q.map (bidualityComplex P) ≫
    (p.iso E (unitComplex (R := R)) (-a)).inv ≫
      D.hom.map ((p.iso P (unitComplex (R := R)) b).hom.op,
        𝟙 (unitObject (R := R))) = biduality (DerivedCategory.Q.obj P) at hm
  have ht := D.hom.map_comp
    (show (Opposite.op (DerivedCategory.Q.obj E), unitObject (R := R)) ⟶
        (Opposite.op (derivedDual (DerivedCategory.Q.obj P)), unitObject (R := R)) from
      ((p.iso P (unitComplex (R := R)) b).hom.op, 𝟙 (unitObject (R := R))))
    (show (Opposite.op (derivedDual (DerivedCategory.Q.obj P)), unitObject (R := R)) ⟶
        (Opposite.op (derivedDual K), unitObject (R := R)) from
      ((D.hom.map (i.inv.op, 𝟙 (unitObject (R := R)))).op, 𝟙 (unitObject (R := R))))
  dsimp only at ht
  simp only [CategoryTheory.prod_comp, Category.id_comp, ← op_comp] at ht
  change D.hom.map (show (Opposite.op (DerivedCategory.Q.obj E), unitObject (R := R)) ⟶
    (Opposite.op (derivedDual K), unitObject (R := R)) from
      (α.op, 𝟙 (unitObject (R := R)))) = _ at ht
  rw [ht]
  rw [reassoc_of% hm, ← biduality_natural i.inv]
  simp

private theorem exists_cochainSingleEquiv
    {S : Type u} [CommRing S] (P : CochainComplex (ModuleCat S) ℤ)
    (n m : ℤ) (h : m + n = 0) :
    ∃ e : Cochain P (𝟙_ _) n ≃ₗ[S] Module.Dual S (P.X m),
      ∀ z x, e z x = (singleObjXSelf (ComplexShape.up ℤ) 0 (ModuleCat.of S S)).hom.hom
        ((z.v m 0 h).hom x) := by
  have hm : m = -n := by omega
  subst hm
  exact ⟨cochainSingleEquiv P (ModuleCat.of S S) n, fun _ _ => rfl⟩

omit [HasDerivedCategory.{w} (ModuleCat.{max u v} (ULift.{v} R))] in
private theorem bidualityComplex_isIso
    (P : CochainComplex (ModuleCat.{max u v} (ULift.{v} R)) ℤ)
    [∀ n, Module.Finite (ULift.{v} R) (P.X n)]
    [∀ n, Module.Projective (ULift.{v} R) (P.X n)] :
    IsIso (bidualityComplex P) := by
  have hn (n : ℤ) : IsIso ((bidualityComplex P).f n) := by
    let S := ULift.{v} R
    let E := HomComplexR S P (unitComplex (R := R))
    obtain ⟨eP, heP⟩ := exists_cochainSingleEquiv P (-n) n (by omega)
    obtain ⟨eE, heE⟩ := exists_cochainSingleEquiv E n (-n) (by omega)
    let e := (Module.evalEquiv S (P.X n)).trans eP.dualMap
    have hh : (fun x : P.X n => eE (((bidualityComplex P).f n).hom x)) =
        fun x => n.negOnePow • e x := by
      funext x
      apply LinearMap.ext
      intro ψ
      rw [heE]
      rw [bidualityComplex_apply]
      simp only [Units.smul_def, map_zsmul]
      show (n.negOnePow : ℤ) •
        (singleObjXSelf (ComplexShape.up ℤ) 0 (ModuleCat.of S S)).hom.hom
          ((ψ.v n 0 _).hom x) = (n.negOnePow : ℤ) • (eP ψ) x
      exact congrArg ((n.negOnePow : ℤ) • ·) (heP ψ x).symm
    have hb := (MulAction.toPerm (β := Module.Dual S (E.X (-n))) n.negOnePow).bijective.comp
      e.bijective
    change Function.Bijective (fun x => n.negOnePow • e x) at hb
    rw [← hh] at hb
    apply (ConcreteCategory.isIso_iff_bijective _).mpr
    exact (Function.Bijective.of_comp_iff' eE.bijective _).mp hb
  exact HomologicalComplex.Hom.isIso_of_components _

theorem biduality_isIso
    (K : DerivedCategory (ModuleCat.{max u v} (ULift.{v} R)))
    (hK : IsPerfect K) : IsIso (biduality K) := by
  obtain ⟨P, a, b, hPa, hPb, hPf, hPp, ⟨i⟩⟩ := hK
  have := hPa
  have := hPb
  have := hPf
  have := hPp
  obtain ⟨aE, bE, hEa, hEb, hEf, hEp, he⟩ := biduality_representation K P a b i
  have := hEb
  have := hEp
  have := bidualityComplex_isIso P
  let D := derivedHomData (R := R)
  let p := projectiveHomComparisonULift (R := R)
  let α := D.hom.mapIso (i.symm.op.prod (Iso.refl (unitObject (R := R)))) ≪≫
    p.iso P (unitComplex (R := R)) b
  have : IsIso (show (Opposite.op (DerivedCategory.Q.obj
      (HomComplexR (ULift.{v} R) P (unitComplex (R := R)))), unitObject (R := R)) ⟶
      (Opposite.op (derivedDual K), unitObject (R := R)) from
      (α.hom.op, 𝟙 (unitObject (R := R)))) :=
    (isIso_prod_iff _ _).mpr ⟨inferInstance, inferInstance⟩
  rw [← he]
  show IsIso (i.hom ≫ DerivedCategory.Q.map (bidualityComplex P) ≫
    (p.iso (HomComplexR (ULift.{v} R) P (unitComplex (R := R)))
      (unitComplex (R := R)) bE).inv ≫
      D.hom.map (show (Opposite.op (DerivedCategory.Q.obj
          (HomComplexR (ULift.{v} R) P (unitComplex (R := R)))), unitObject (R := R)) ⟶
          (Opposite.op (derivedDual K), unitObject (R := R)) from
        (α.hom.op, 𝟙 (unitObject (R := R)))))
  infer_instance

end StacksDraft.Perfect

end
