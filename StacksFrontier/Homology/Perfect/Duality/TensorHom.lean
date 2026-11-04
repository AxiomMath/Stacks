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
public import StacksFrontier.Homology.Perfect.Duality.Biduality
import StacksCore.Tactic.StacksAttribute

/-!
# The tensor--Hom comparison for perfect complexes, and Stacks 07VI

Let `A` be a ring and let `K` be a perfect object of `D(A)`. This file proves that the canonical
comparison `L ⊗_A^L Kᵛ ⟶ RHom_A(K, L)` is an isomorphism functorially in `L` and that `Kᵛ` is
perfect, and assembles the conclusions of [stacks 07VI].

## Main definitions

* `StacksDraft.Perfect.PerfectDerivedDuality`: the conjunction of the four conclusions of
  [stacks 07VI] for a single object.

## Main results

* `StacksDraft.Perfect.isPerfect_derivedDual_and_naturalIsos` ([stacks 07VI]): for a perfect `K`,
  the derived dual is perfect, biduality is an isomorphism, the tensor--Hom comparison is an
  isomorphism natural in the target, and `H⁰(L ⊗^L Kᵛ) ≃+ Ext⁰(K, L)` functorially.

## Implementation notes

The degree-zero clause is the only one phrased existentially, as [stacks 07VI] phrases it; the
family of isomorphisms is the one of `StacksDraft.Perfect.exists_extZeroEquiv_of`.

The proof follows the source: choose a bounded representative `P` of `K` with finite projective
terms, identify `RHom(P, L)` with the Hom complex `Hom^•(P, L)` for every `L` (the bifunctor form
of [stacks 0A66], `StacksDraft.DerivedHom.projectiveHomComparison`), and check the canonical map
on those representatives, where it becomes a chain-level map. That step uses the left duals of
[stacks 0FNK]: a bounded complex of finite projectives is a left dual in the monoidal category of
complexes, and the chain-level tensor--Hom map is then an isomorphism because both functors are
right adjoint to tensoring with `P`.

`backward.isDefEq.respectTransparency` is relaxed in places, because the summand inclusions of
total tensor complexes are definitionally coproduct inclusions indexed by a subtype of `ℤ × ℤ`,
and the comparisons must be seen through that packaging.

## References

* [Stacks Project, Tag 07VI](https://stacks.math.columbia.edu/tag/07VI)
* [Stacks Project, Tag 0A66](https://stacks.math.columbia.edu/tag/0A66)
* [Stacks Project, Tag 0FNK](https://stacks.math.columbia.edu/tag/0FNK)
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory CochainComplex CochainComplex.HomComplex
  HomologicalComplex

universe u v w

namespace StacksDraft.Perfect

open StacksDraft.DerivedHom Stacks.HomComplex.MonoidalClosed

/-! ## K-flat resolutions -/

section KFlatInputs

variable {R : Type u} [CommRing R]

/-- [stacks 06Y4] read at a module universe equal to the ring's: every cochain complex of modules
admits a termwise surjective quasi-isomorphism from a K-flat complex with flat terms. -/
private theorem existsKFlatResolution
    (M : CochainComplex (ModuleCat.{max u v} (ULift.{v} R)) ℤ) :
    ∃ (K : CochainComplex (ModuleCat.{max u v} (ULift.{v} R)) ℤ) (f : K ⟶ M),
      K.KFlat ∧ (∀ n : ℤ, Module.Flat (ULift.{v} R) (K.X n)) ∧ QuasiIso f ∧
        ∀ n : ℤ, Function.Surjective (f.f n).hom := by
  obtain ⟨K, f, hK, hflat, hqis, hsurj⟩ :=
    CochainComplex.KFlat.exists_kFlat_resolution.{max u v, max u v} M
  exact ⟨K, f, hK, hflat, hqis, hsurj⟩

end KFlatInputs

variable {R : Type u} [CommRing R]
  [HasDerivedCategory.{w} (ModuleCat.{max u v} (ULift.{v} R))]

/-! ## The chain-level model of the tensor--Hom comparison -/

/-- The chain-level comparison `L ⊗ Hom^•(P, A) ⟶ Hom^•(P, L)`. -/
private def tensorHomComplex
    (P L : CochainComplex (ModuleCat.{max u v} (ULift.{v} R)) ℤ) :
    L ⊗ CochainComplex.HomComplexR (ULift.{v} R) P (unitComplex (R := R)) ⟶
      CochainComplex.HomComplexR (ULift.{v} R) P L :=
  Stacks.HomComplex.TensorHomComparison.theta L (unitComplex (R := R)) P ≫
    Stacks.HomComplex.TensorHomComparison.HomCxMap P P (L ⊗ unitComplex (R := R)) L (𝟙 P) (ρ_ L).hom

/-! ## Naturality of the tensor--Hom comparison, and perfectness of the dual -/

/-- The adjunct of `tensorDualHom K L` is the evaluation composite defining it. -/
private theorem homEquiv_tensorDualHom
    (K L : DerivedCategory (ModuleCat.{max u v} (ULift.{v} R))) :
    (derivedHomData (R := R)).homEquiv _ K L (tensorDualHom K L) =
      ((derivedHomData (R := R)).tensorAssoc L (derivedDual K) K).hom ≫
        (derivedHomData (R := R)).tensor.map (𝟙 L,
          (derivedHomData (R := R)).evaluation K (unitObject (R := R))) ≫
          ((derivedHomData (R := R)).tensorSwap L (unitObject (R := R))).hom ≫
            ((derivedHomData (R := R)).tensorUnitLeft L).hom :=
  AddEquiv.apply_symm_apply _ _

set_option backward.isDefEq.respectTransparency false in
private theorem tensorHom_natural
    (K : DerivedCategory (ModuleCat.{max u v} (ULift.{v} R)))
    {L L' : DerivedCategory (ModuleCat.{max u v} (ULift.{v} R))} (f : L ⟶ L') :
    (derivedHomData (R := R)).tensor.map (f, 𝟙 (derivedDual K)) ≫ tensorDualHom K L' =
      tensorDualHom K L ≫ (derivedHomData (R := R)).hom.map (𝟙 (Opposite.op K), f) := by
  apply ((derivedHomData (R := R)).homEquiv _ K L').injective
  rw [(derivedHomData (R := R)).homEquiv_naturality_left,
    (derivedHomData (R := R)).homEquiv_naturality_right,
    homEquiv_tensorDualHom, homEquiv_tensorDualHom]
  rw [DerivedHomAdjunction.tensorAssoc_naturality_assoc, DerivedHomAdjunction.tensor_map_id]
  simp only [Category.assoc, DerivedHomAdjunction.tensor_map_comp_assoc, Category.id_comp,
    Category.comp_id]
  have h := DerivedHomAdjunction.tensor_map_comp (derivedHomData (R := R)).toDerivedHomAdjunction
    (𝟙 L) ((derivedHomData (R := R)).evaluation K (unitObject (R := R))) f
    (𝟙 (unitObject (R := R)))
  simp only [Category.id_comp, Category.comp_id] at h
  rw [← h]
  simp only [Category.assoc]
  rw [DerivedHomAdjunction.tensorSwap_naturality_assoc, DerivedHomData.tensorUnitLeft_naturality]

set_option backward.isDefEq.respectTransparency false in
private theorem isPerfect_derivedDual
    (K : DerivedCategory (ModuleCat.{max u v} (ULift.{v} R)))
    (hK : IsPerfect K) : IsPerfect (derivedDual K) := by
  obtain ⟨P, a, b, hPa, hPb, hPf, hPp, ⟨i⟩⟩ := hK
  have := hPa
  have := hPb
  have := hPf
  have := hPp
  let E := HomComplexR (ULift.{v} R) P (unitComplex (R := R))
  obtain ⟨hEa, hEb⟩ := homComplex_unit_bounded P a b
  refine ⟨E, -b, -a, hEa, hEb,
    fun n => (homComplex_unit_finite_projective P n).1,
    fun n => (homComplex_unit_finite_projective P n).2, ?_⟩
  let D := derivedHomData (R := R)
  let p := projectiveHomComparisonULift (R := R)
  exact ⟨D.hom.mapIso (i.symm.op.prod (Iso.refl (unitObject (R := R)))) ≪≫
    p.iso P (unitComplex (R := R)) b⟩


section ModelComparison

set_option backward.isDefEq.respectTransparency.types false

variable {S : Type u} [CommRing S]

set_option backward.isDefEq.respectTransparency false

private theorem tensorHomEquiv_eq_uncurry
    (A P M : CochainComplex (ModuleCat S) ℤ) (f : A ⟶ HomComplexR S P M) :
    Stacks.HomComplex.MonoidalClosed.tensorHomEquiv A P M f = uncurryComplex f := rfl

end ModelComparison

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem tensorHom_natural_left
    {K K' : DerivedCategory (ModuleCat.{max u v} (ULift.{v} R))} (f : K ⟶ K')
    (L : DerivedCategory (ModuleCat.{max u v} (ULift.{v} R))) :
    let D := derivedHomData (R := R)
    D.tensor.map (𝟙 L, D.hom.map (f.op, 𝟙 (unitObject (R := R)))) ≫ tensorDualHom K L =
      tensorDualHom K' L ≫ D.hom.map (f.op, 𝟙 L) := by
  dsimp only
  apply ((derivedHomData (R := R)).homEquiv _ K L).injective
  rw [(derivedHomData (R := R)).homEquiv_naturality_left,
    (derivedHomData (R := R)).homEquiv_dinaturality, homEquiv_tensorDualHom,
    homEquiv_tensorDualHom]
  rw [DerivedHomAdjunction.tensorAssoc_naturality_assoc]
  have ha := (derivedHomData (R := R)).tensorAssoc_naturality (𝟙 L) (𝟙 (derivedDual K')) f
  rw [DerivedHomAdjunction.tensor_map_id] at ha
  rw [reassoc_of% ha]
  simp only [DerivedHomAdjunction.tensor_map_comp_assoc, Category.id_comp]
  rw [DerivedHomAdjunction.evaluation_naturality_left]

omit [HasDerivedCategory.{w} (ModuleCat.{max u v} (ULift.{v} R))] in
private theorem tensorHomComplex_apply
    (P L : CochainComplex (ModuleCat.{max u v} (ULift.{v} R)) ℤ)
    (n p q : ℤ) (hpq : p + q = n) (x : L.X p)
    (φ : Cochain P (unitComplex (R := R)) q)
    (a b : ℤ) (hab : a + n = b) (m : P.X a) :
    ((((tensorHomComplex P L).f n).hom
      ((ιTensorObj L (HomComplexR (ULift.{v} R) P (unitComplex (R := R)))
        p q n hpq).hom (x ⊗ₜ[ULift.{v} R] φ))).v a b hab).hom m =
      (ρ_ L).hom.f b ((ιTensorObj L (unitComplex (R := R))
        p (b - p) b (by omega)).hom
          (x ⊗ₜ[ULift.{v} R] (φ.v a (b-p) (by omega)).hom m)) := by
  show ((Stacks.HomComplex.TensorHomComparison.HomCxMapDeg P P (L ⊗ unitComplex (R := R)) L
    (𝟙 P) (ρ_ L).hom n
      (((Stacks.HomComplex.TensorHomComparison.theta L (unitComplex (R := R)) P).f n).hom
        ((ιTensorObj L (HomComplexR (ULift.{v} R) P (unitComplex (R := R)))
          p q n hpq).hom (x ⊗ₜ[ULift.{v} R] φ)))).v a b hab).hom m = _
  rw [Stacks.HomComplex.TensorHomComparison.HomCxMapDeg_v, HomologicalComplex.id_f,
    Category.id_comp]
  show (ρ_ L).hom.f b
    ((((Stacks.HomComplex.TensorHomComparison.thetaDeg L (unitComplex (R := R)) P n).hom
      ((ιTensorObj L (HomComplexR (ULift.{v} R) P (unitComplex (R := R)))
        p q n hpq).hom (x ⊗ₜ[ULift.{v} R] φ))).v a b hab).hom m) = _
  rw [Stacks.HomComplex.TensorHomComparison.theta_apply]
  rfl

omit [HasDerivedCategory.{w} (ModuleCat.{max u v} (ULift.{v} R))] in
private theorem uncurry_tensorHomComplex
    (P L : CochainComplex (ModuleCat.{max u v} (ULift.{v} R)) ℤ) :
    let E := HomComplexR (ULift.{v} R) P (unitComplex (R := R))
    uncurryComplex (tensorHomComplex P L) =
      (α_ L E P).hom ≫ (L ◁ uncurryComplex (𝟙 E)) ≫ (ρ_ L).hom := by
  intro E
  apply HomologicalComplex.hom_ext
  intro n
  apply GradedObject.Monoidal.tensorObj₃'_ext
  intro p q r h
  have ha := GradedObject.Monoidal.ιTensorObj₃'_associator_hom
    L.X E.X P.X p q r n h
  change GradedObject.Monoidal.ιTensorObj₃' L.X E.X P.X p q r n h ≫
    (α_ L E P).hom.f n = (α_ (L.X p) (E.X q) (P.X r)).hom ≫
      GradedObject.Monoidal.ιTensorObj₃ L.X E.X P.X p q r n h at ha
  show _ = GradedObject.Monoidal.ιTensorObj₃' L.X E.X P.X p q r n h ≫
    (α_ L E P).hom.f n ≫ (L ◁ uncurryComplex (𝟙 E)).f n ≫ (ρ_ L).hom.f n
  rw [reassoc_of% ha]
  rw [GradedObject.Monoidal.ιTensorObj₃_eq L.X E.X P.X p q r n h (q+r) rfl,
    GradedObject.Monoidal.ιTensorObj₃'_eq L.X E.X P.X p q r n h (p+q) rfl]
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro z m
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add z z' hz hz' =>
    simpa only [TensorProduct.add_tmul, map_add] using congrArg₂ (· + ·) hz hz'
  | tmul x φ =>
    show (uncurryComplex (tensorHomComplex P L)).f n
      ((ιTensorObj (L ⊗ E) P (p+q) r n h).hom
        ((ιTensorObj L E p q (p+q) rfl).hom (x ⊗ₜ[ULift.{v} R] φ)
          ⊗ₜ[ULift.{v} R] m)) = _
    rw [uncurryComplex_apply, tensorHomComplex_apply]
    have hw := ConcreteCategory.congr_hom
      (CochainComplex.ιTensorObj_whiskerLeft L (L := E ⊗ P) (M := unitComplex (R := R))
        (uncurryComplex (𝟙 E)) p (q+r) n (by omega))
      (x ⊗ₜ[ULift.{v} R]
        (ιTensorObj E P q r (q+r) rfl).hom (φ ⊗ₜ[ULift.{v} R] m))
    simp only [ModuleCat.comp_apply, ModuleCat.MonoidalCategory.whiskerLeft_apply] at hw
    show _ = (ρ_ L).hom.f n
      ((L ◁ uncurryComplex (𝟙 E)).f n
        ((ιTensorObj L (E ⊗ P) p (q+r) n (by omega)).hom
          (x ⊗ₜ[ULift.{v} R]
            (ιTensorObj E P q r (q+r) rfl).hom (φ ⊗ₜ[ULift.{v} R] m))))
    erw [hw]
    rw [uncurryComplex_apply]
    have hv (s : ℤ) (hs : p + s = n) (hrs : r + q = s) :
        (ρ_ L).hom.f n ((ιTensorObj L (unitComplex (R := R)) p s n hs).hom
          (x ⊗ₜ[ULift.{v} R] (φ.v r s hrs).hom m)) =
        (ρ_ L).hom.f n ((ιTensorObj L (unitComplex (R := R)) p (q+r) n
          (by omega)).hom (x ⊗ₜ[ULift.{v} R] (φ.v r (q+r) (by omega)).hom m)) := by
      have hs' : s = q+r := by omega
      subst hs'
      rfl
    exact hv (n-p) (by omega) (by omega)

omit [HasDerivedCategory.{w} (ModuleCat.{max u v} (ULift.{v} R))] in
private theorem tensorHomComplex_isIso_of_exactPairing
    (P N L : CochainComplex (ModuleCat.{max u v} (ULift.{v} R)) ℤ)
    [ExactPairing P N] : IsIso (tensorHomComplex P L) := by
  let a := tensorRightAdjunction P N
  let b := CochainComplex.LeftDual.tensorHomAdjunction P
  let e := a.rightAdjointUniq b
  let E := HomComplexR (ULift.{v} R) P (unitComplex (R := R))
  let i : N ≅ E := (λ_ N).symm ≪≫ e.app (unitComplex (R := R))
  have he (X : CochainComplex (ModuleCat.{max u v} (ULift.{v} R)) ℤ) :
      uncurryComplex (e.hom.app X) =
        (α_ X N P).hom ≫ (X ◁ ε_ P N) ≫ (ρ_ X).hom := by
    have h := Adjunction.homEquiv_symm_rightAdjointUniq_hom_app a b X
    change ((CochainComplex.LeftDual.tensorHomAdjunction P).homEquiv (X ⊗ N) X).symm
      (e.hom.app X) = a.counit.app X at h
    rw [CochainComplex.LeftDual.tensorHomAdjunction, Adjunction.mkOfHomEquiv_homEquiv] at h
    change uncurryComplex (e.hom.app X) = a.counit.app X at h
    rw [h]
    show (𝟙 (X ⊗ N) ▷ P) ≫ _ = _
    rw [id_whiskerRight, Category.id_comp]
    rfl
  have hn {A B M : CochainComplex (ModuleCat.{max u v} (ULift.{v} R)) ℤ}
      (f : A ⟶ B) (g : B ⟶ HomComplexR (ULift.{v} R) P M) :
      uncurryComplex (f ≫ g) = (f ▷ P) ≫ uncurryComplex g := by
    simpa only [tensorHomEquiv_eq_uncurry] using tensorHomEquiv_naturality_left f g
  have hi : (i.hom ▷ P) ≫ uncurryComplex (𝟙 E) = ε_ P N := by
    rw [← hn, Category.comp_id]
    show uncurryComplex ((λ_ N).inv ≫ e.hom.app (unitComplex (R := R))) = _
    rw [hn, he]
    monoidal
  have hf : (L ◁ i.hom) ≫ tensorHomComplex P L = e.hom.app L := by
    apply (tensorHomEquiv (L ⊗ N) P L).injective
    simp only [tensorHomEquiv_eq_uncurry]
    rw [hn, uncurry_tensorHomComplex, he]
    rw [associator_naturality_middle_assoc, ← whiskerLeft_comp_assoc, hi]
  have hf' : tensorHomComplex P L = (L ◁ i.inv) ≫ e.hom.app L := by
    rw [← hf]
    simp only [← whiskerLeft_comp_assoc, Iso.inv_hom_id, whiskerLeft_id, Category.id_comp]
  rw [hf']
  infer_instance

omit [HasDerivedCategory.{w} (ModuleCat.{max u v} (ULift.{v} R))] in
private theorem tensorHomComplex_isIso
    (P L : CochainComplex (ModuleCat.{max u v} (ULift.{v} R)) ℤ)
    (lower upper : ℤ) [P.IsStrictlyGE lower] [P.IsStrictlyLE upper]
    [∀ n, Module.Finite (ULift.{v} R) (P.X n)]
    [∀ n, Module.Projective (ULift.{v} R) (P.X n)] :
    IsIso (tensorHomComplex P L) := by
  obtain ⟨N, pairing, _⟩ :=
    (CochainComplex.LeftDual.exactPairing_iff_bounded_finiteProjective (ULift.{v} R)).2 P
      ⟨lower, upper, inferInstance, inferInstance⟩ (fun _ => ⟨inferInstance, inferInstance⟩)
  let := pairing
  exact tensorHomComplex_isIso_of_exactPairing P N L

private theorem tensorUnitRight_comparison
    (L : CochainComplex (ModuleCat.{max u v} (ULift.{v} R)) ℤ) (hL : L.KFlat) :
    let D := derivedHomData (R := R)
    (D.tensorSwap (DerivedCategory.Q.obj L) (unitObject (R := R))).hom ≫
      (D.tensorUnitLeft (DerivedCategory.Q.obj L)).hom =
        (D.tensorIso L (unitComplex (R := R))
          DerivedHomData.unit_kFlat).hom ≫ DerivedCategory.Q.map (ρ_ L).hom := by
  intro D
  rw [← D.tensorUnitLeft_comparison L hL, ← Category.assoc]
  have h := D.tensorSwap_comparison L (unitComplex (R := R)) hL
    DerivedHomData.unit_kFlat
  change (D.tensorSwap (DerivedCategory.Q.obj L) (unitObject (R := R))).hom ≫
    (D.tensorIso (unitComplex (R := R)) L hL).hom =
      (D.tensorIso L (unitComplex (R := R)) DerivedHomData.unit_kFlat).hom ≫
        DerivedCategory.Q.map
          (Model.complexSwap (ULift.{v} R) L (unitComplex (R := R))).hom at h
  rw [h, Category.assoc, ← Functor.map_comp]
  congr 2
  let := CochainComplex.Koszul.koszulSymmetric (ULift.{v} R)
  exact braiding_leftUnitor L


private theorem evaluation_projective_model
    (representative : CochainComplex (ModuleCat.{max u v} (ULift.{v} R)) ℤ)
    (upper : ℤ) [representative.IsStrictlyLE upper]
    [∀ degree, Module.Projective (ULift.{v} R) (representative.X degree)]
    (representativeFlat : representative.KFlat) :
    let dual := HomComplexR (ULift.{v} R) representative (unitComplex (R := R))
    let data := derivedHomData (R := R)
    let model := projectiveHomComparisonULift (R := R)
    data.tensor.map ((model.iso representative (unitComplex (R := R)) upper).hom,
        𝟙 (DerivedCategory.Q.obj representative)) ≫
      (data.tensorIso dual representative representativeFlat).hom ≫
      DerivedCategory.Q.map (uncurryComplex (𝟙 dual)) =
        data.evaluation (DerivedCategory.Q.obj representative) (unitObject (R := R)) := by
  intro dual data model
  have comparison := homEquiv_uncurryComplex dual representative (unitComplex (R := R))
    upper representativeFlat (𝟙 dual)
  dsimp only at comparison
  rw [CategoryTheory.Functor.map_id, Category.id_comp] at comparison
  rw [← comparison, ← data.homEquiv_naturality_left]
  show data.homEquiv _ _ _
      ((model.iso representative (unitComplex (R := R)) upper).hom ≫
        (model.iso representative (unitComplex (R := R)) upper).inv) =
    data.homEquiv _ _ _ (𝟙 _)
  rw [Iso.hom_inv_id]

set_option backward.isDefEq.respectTransparency false in
private theorem tensorHom_projective_model_flat
    (representative target : CochainComplex (ModuleCat.{max u v} (ULift.{v} R)) ℤ)
    (upper : ℤ) [representative.IsStrictlyLE upper]
    [∀ degree, Module.Projective (ULift.{v} R) (representative.X degree)]
    (representativeFlat : representative.KFlat) (targetFlat : target.KFlat)
    (dualFlat : (HomComplexR (ULift.{v} R) representative (unitComplex (R := R))).KFlat) :
    let dual := HomComplexR (ULift.{v} R) representative (unitComplex (R := R))
    let data := derivedHomData (R := R)
    let model := projectiveHomComparisonULift (R := R)
    data.tensor.map (𝟙 (DerivedCategory.Q.obj target),
        (model.iso representative (unitComplex (R := R)) upper).hom) ≫
      (data.tensorIso target dual dualFlat).hom ≫
      DerivedCategory.Q.map (tensorHomComplex representative target) ≫
      (model.iso representative target upper).inv =
        tensorDualHom (DerivedCategory.Q.obj representative) (DerivedCategory.Q.obj target) := by
  intro dual data model
  have productFlat : (dual ⊗ representative).KFlat := by
    intro acyclic acyclicProof
    exact HomologicalComplex.Acyclic.of_iso (α_ acyclic dual representative)
      (representativeFlat (acyclic ⊗ dual) (dualFlat acyclic acyclicProof))
  have associator := derivedHomAdjunction_tensorAssoc_comparison
    target dual representative targetFlat dualFlat representativeFlat productFlat
  have naturality := data.tensorIso_naturality (𝟙 target) (uncurryComplex (𝟙 dual))
    productFlat DerivedHomData.unit_kFlat
  simp only [CategoryTheory.Functor.map_id, id_tensorHom] at naturality
  apply (data.homEquiv _ _ _).injective
  rw [data.homEquiv_naturality_left, data.homEquiv_naturality_left,
    homEquiv_uncurryComplex (target ⊗ dual) representative target upper representativeFlat,
    uncurry_tensorHomComplex, Functor.map_comp, Functor.map_comp]
  simp only [tensorDualHom, data, AddEquiv.apply_symm_apply]
  rw [← reassoc_of% associator]
  rw [data.tensorAssoc_naturality_assoc]
  rw [← reassoc_of% naturality]
  rw [← tensorUnitRight_comparison target targetFlat]
  congr 1
  rw [← Category.assoc, ← Category.assoc, data.tensor_map_comp, data.tensor_map_comp]
  have evaluation := evaluation_projective_model representative upper representativeFlat
  dsimp only at evaluation
  simpa only [data, model, dual, Category.assoc, Category.id_comp] using
    congrArg (fun (morphism : data.tensor.obj
      (derivedDual (DerivedCategory.Q.obj representative), DerivedCategory.Q.obj representative) ⟶
      unitObject (R := R)) => data.tensor.map
      (show (DerivedCategory.Q.obj target, data.tensor.obj
        (derivedDual (DerivedCategory.Q.obj representative),
          DerivedCategory.Q.obj representative)) ⟶
        (DerivedCategory.Q.obj target, unitObject (R := R)) from
        (𝟙 (DerivedCategory.Q.obj target), morphism)) ≫
      (data.tensorSwap (DerivedCategory.Q.obj target) (unitObject (R := R))).hom ≫
      (data.tensorUnitLeft (DerivedCategory.Q.obj target)).hom)
      evaluation

omit [HasDerivedCategory.{w} (ModuleCat.{max u v} (ULift.{v} R))] in
set_option backward.isDefEq.respectTransparency false in
private theorem tensorHomComplex_naturality_target
    (representative : CochainComplex (ModuleCat.{max u v} (ULift.{v} R)) ℤ)
    {target target' : CochainComplex (ModuleCat.{max u v} (ULift.{v} R)) ℤ}
    (morphism : target ⟶ target') :
    (morphism ▷ HomComplexR (ULift.{v} R) representative (unitComplex (R := R))) ≫
      tensorHomComplex representative target' =
    tensorHomComplex representative target ≫
      Stacks.HomComplex.TensorHomComparison.HomCxMap representative representative target target'
        (𝟙 representative) morphism := by
  have mapEquality :
      Stacks.HomComplex.TensorHomComparison.HomCxMap representative representative target target' (𝟙
        representative) morphism =
        Stacks.HomComplex.TensorHomMap.postcomp (ULift.{v} R) representative target target' morphism
          := by
    ext degree element
    show (Cochain.ofHom (𝟙 representative)).comp
      (element.comp (Cochain.ofHom morphism) (add_zero degree)) (zero_add degree) =
      element.comp (Cochain.ofHom morphism) (add_zero degree)
    rw [Cochain.id_comp]
  rw [mapEquality]
  apply (tensorHomEquiv _ representative target').injective
  rw [tensorHomEquiv_naturality_left, tensorHomEquiv_naturality_right]
  simp only [tensorHomEquiv_eq_uncurry, uncurry_tensorHomComplex]
  simp only [associator_naturality_left_assoc]
  simp only [Category.assoc]
  rw [← whisker_exchange_assoc, rightUnitor_naturality]

set_option backward.isDefEq.respectTransparency false in
private theorem tensorHom_projective_model
    (representative target : CochainComplex (ModuleCat.{max u v} (ULift.{v} R)) ℤ)
    (upper : ℤ) [representative.IsStrictlyLE upper]
    [∀ degree, Module.Projective (ULift.{v} R) (representative.X degree)]
    (representativeFlat : representative.KFlat)
    (dualFlat : (HomComplexR (ULift.{v} R) representative (unitComplex (R := R))).KFlat) :
    let dual := HomComplexR (ULift.{v} R) representative (unitComplex (R := R))
    let data := derivedHomData (R := R)
    let model := projectiveHomComparisonULift (R := R)
    data.tensor.map (𝟙 (DerivedCategory.Q.obj target),
        (model.iso representative (unitComplex (R := R)) upper).hom) ≫
      (data.tensorIso target dual dualFlat).hom ≫
      DerivedCategory.Q.map (tensorHomComplex representative target) ≫
      (model.iso representative target upper).inv =
        tensorDualHom (DerivedCategory.Q.obj representative) (DerivedCategory.Q.obj target) := by
  intro dual data model
  obtain ⟨cover, resolution, coverFlat, _, resolutionQuasiIso, _⟩ :=
    existsKFlatResolution target
  have : QuasiIso resolution := resolutionQuasiIso
  let coverIso := asIso (DerivedCategory.Q.map resolution)
  let sourceIso := data.tensor.mapIso
    (coverIso.prod (Iso.refl (derivedDual (DerivedCategory.Q.obj representative))))
  apply (cancel_epi sourceIso.hom).mp
  show data.tensor.map
      (show (DerivedCategory.Q.obj cover, derivedDual (DerivedCategory.Q.obj representative)) ⟶
        (DerivedCategory.Q.obj target, derivedDual (DerivedCategory.Q.obj representative)) from
        (DerivedCategory.Q.map resolution, 𝟙 _)) ≫ _ =
    data.tensor.map
      (show (DerivedCategory.Q.obj cover, derivedDual (DerivedCategory.Q.obj representative)) ⟶
        (DerivedCategory.Q.obj target, derivedDual (DerivedCategory.Q.obj representative)) from
        (DerivedCategory.Q.map resolution, 𝟙 _)) ≫ _
  rw [tensorHom_natural]
  have exchange :
      data.tensor.map
        (show (DerivedCategory.Q.obj cover, derivedDual (DerivedCategory.Q.obj representative)) ⟶
          (DerivedCategory.Q.obj target, derivedDual (DerivedCategory.Q.obj representative)) from
          (DerivedCategory.Q.map resolution, 𝟙 _)) ≫
        data.tensor.map
          (show (DerivedCategory.Q.obj target, derivedDual (DerivedCategory.Q.obj representative)) ⟶
            (DerivedCategory.Q.obj target, DerivedCategory.Q.obj dual) from
            (𝟙 _, (model.iso representative (unitComplex (R := R)) upper).hom)) =
      data.tensor.map
        (show (DerivedCategory.Q.obj cover, derivedDual (DerivedCategory.Q.obj representative)) ⟶
          (DerivedCategory.Q.obj cover, DerivedCategory.Q.obj dual) from
          (𝟙 _, (model.iso representative (unitComplex (R := R)) upper).hom)) ≫
        data.tensor.map
          (show (DerivedCategory.Q.obj cover, DerivedCategory.Q.obj dual) ⟶
            (DerivedCategory.Q.obj target, DerivedCategory.Q.obj dual) from
            (DerivedCategory.Q.map resolution, 𝟙 (DerivedCategory.Q.obj dual))) := by
    simp only [dual, data.tensor_map_comp, Category.id_comp, Category.comp_id]
  rw [reassoc_of% exchange]
  have tensorNaturality := data.tensorIso_naturality resolution (𝟙 dual) dualFlat dualFlat
  simp only [CategoryTheory.Functor.map_id, tensorHom_id] at tensorNaturality
  rw [reassoc_of% tensorNaturality, ← Functor.map_comp_assoc,
    tensorHomComplex_naturality_target, Functor.map_comp, Category.assoc]
  have homNaturality := model.naturality representative representative cover target
    upper upper (𝟙 representative) resolution
  simp only [CategoryTheory.Functor.map_id, op_id] at homNaturality
  have inverseNaturality := congrArg
    (fun morphism => (model.iso representative cover upper).inv ≫ morphism ≫
      (model.iso representative target upper).inv) homNaturality
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id,
    Iso.inv_hom_id_assoc] at inverseNaturality
  rw [← inverseNaturality]
  have modelComparison := tensorHom_projective_model_flat representative cover upper
    representativeFlat coverFlat dualFlat
  dsimp only at modelComparison
  rw [← modelComparison]
  simp only [data, model, dual, Category.assoc]

set_option backward.isDefEq.respectTransparency false in
private theorem tensorHom_representation
    (object : DerivedCategory (ModuleCat.{max u v} (ULift.{v} R)))
    (representative target : CochainComplex (ModuleCat.{max u v} (ULift.{v} R)) ℤ)
    (lower upper : ℤ) [representative.IsStrictlyGE lower] [representative.IsStrictlyLE upper]
    [∀ degree, Module.Finite (ULift.{v} R) (representative.X degree)]
    [∀ degree, Module.Projective (ULift.{v} R) (representative.X degree)]
    (representation : object ≅ DerivedCategory.Q.obj representative) :
    let dual := HomComplexR (ULift.{v} R) representative (unitComplex (R := R))
    let data := derivedHomData (R := R)
    let model := projectiveHomComparisonULift (R := R)
    let comparison := data.hom.map (representation.inv.op, 𝟙 (unitObject (R := R))) ≫
      (model.iso representative (unitComplex (R := R)) upper).hom
    ∃ dualFlat : dual.KFlat,
      data.tensor.map (𝟙 (DerivedCategory.Q.obj target), comparison) ≫
        (data.tensorIso target dual dualFlat).hom ≫
        DerivedCategory.Q.map (tensorHomComplex representative target) ≫
        (model.iso representative target upper).inv ≫
        data.hom.map (representation.hom.op, 𝟙 (DerivedCategory.Q.obj target)) =
          tensorDualHom object (DerivedCategory.Q.obj target) := by
  intro dual data model comparison
  obtain ⟨dualLower, dualUpper⟩ := homComplex_unit_bounded representative lower upper
  have dualProjective : ∀ degree, Module.Projective (ULift.{v} R) (dual.X degree) :=
    fun degree => (homComplex_unit_finite_projective representative degree).2
  have representativeFlat : representative.KFlat := kFlatOfFlat representative upper
  have dualFlat : dual.KFlat := kFlatOfFlat dual (-lower)
  refine ⟨dualFlat, ?_⟩
  let sourceDualIso := data.hom.mapIso
    (representation.symm.op.prod (Iso.refl (unitObject (R := R))))
  have expansion := data.tensor_map_comp (𝟙 (DerivedCategory.Q.obj target)) sourceDualIso.hom
    (𝟙 (DerivedCategory.Q.obj target)) (model.iso representative (unitComplex (R := R)) upper).hom
  rw [Category.id_comp] at expansion
  dsimp only [sourceDualIso] at expansion
  dsimp only [comparison]
  erw [← reassoc_of% expansion]
  have modelComparison := tensorHom_projective_model representative target upper
    representativeFlat dualFlat
  dsimp only at modelComparison
  rw [reassoc_of% modelComparison, ← tensorHom_natural_left representation.hom]
  rw [← Category.assoc, data.tensor_map_comp]
  show data.tensor.map
      (show (DerivedCategory.Q.obj target, derivedDual object) ⟶
        (DerivedCategory.Q.obj target, derivedDual object) from
        (𝟙 (DerivedCategory.Q.obj target) ≫ 𝟙 (DerivedCategory.Q.obj target),
          sourceDualIso.hom ≫ sourceDualIso.inv)) ≫
    tensorDualHom object (DerivedCategory.Q.obj target) = _
  rw [Iso.hom_inv_id, Category.id_comp, data.tensor_map_id, Category.id_comp]

set_option backward.isDefEq.respectTransparency false in
private theorem tensorHom_isIso
    (object target : DerivedCategory (ModuleCat.{max u v} (ULift.{v} R)))
    (perfect : IsPerfect object) : IsIso (tensorDualHom object target) := by
  obtain ⟨representative, lower, upper, lowerBound, upperBound, finiteTerms,
    projectiveTerms, ⟨representation⟩⟩ := perfect
  have := lowerBound
  have := upperBound
  have := finiteTerms
  have := projectiveTerms
  let targetComplex := DerivedCategory.Q.objPreimage target
  let targetIso := DerivedCategory.Q.objObjPreimageIso target
  obtain ⟨dualFlat, modelEquality⟩ :=
    tensorHom_representation object representative targetComplex lower upper representation
  have := tensorHomComplex_isIso representative targetComplex lower upper
  let data := derivedHomData (R := R)
  let model := projectiveHomComparisonULift (R := R)
  let dualIso := data.hom.mapIso
    (representation.symm.op.prod (Iso.refl (unitObject (R := R)))) ≪≫
      model.iso representative (unitComplex (R := R)) upper
  let frontIso := data.tensor.mapIso ((Iso.refl (DerivedCategory.Q.obj targetComplex)).prod dualIso)
  let backIso := data.hom.mapIso
    (representation.op.prod (Iso.refl (DerivedCategory.Q.obj targetComplex)))
  change frontIso.hom ≫ (data.tensorIso targetComplex
      (HomComplexR (ULift.{v} R) representative (unitComplex (R := R))) dualFlat).hom ≫
      DerivedCategory.Q.map (tensorHomComplex representative targetComplex) ≫
      (model.iso representative targetComplex upper).inv ≫ backIso.hom =
        tensorDualHom object (DerivedCategory.Q.obj targetComplex) at modelEquality
  have modelIsIso : IsIso (tensorDualHom object (DerivedCategory.Q.obj targetComplex)) := by
    rw [← modelEquality]
    infer_instance
  let tensorTargetIso := data.tensor.mapIso (targetIso.prod (Iso.refl (derivedDual object)))
  let homTargetIso := data.hom.mapIso ((Iso.refl (Opposite.op object)).prod targetIso)
  have naturality := tensorHom_natural object targetIso.hom
  change tensorTargetIso.hom ≫ tensorDualHom object target =
    tensorDualHom object (DerivedCategory.Q.obj targetComplex) ≫ homTargetIso.hom at naturality
  have : IsIso (tensorTargetIso.hom ≫ tensorDualHom object target) := by
    rw [naturality]
    infer_instance
  exact IsIso.of_isIso_comp_left tensorTargetIso.hom _

/-! ## The statement of Stacks 07VI -/

/-- The conclusions of [stacks 07VI] for a single object `K` of `D(A)`: the derived dual is
perfect, the canonical biduality morphism is an isomorphism, the canonical tensor--Hom
comparison is an isomorphism naturally in its target, and in degree zero that comparison
identifies the homology of `L ⊗ᴸ Kᵛ` with `Ext⁰(K, L)`, functorially in `L`. -/
structure PerfectDerivedDuality
    (K : DerivedCategory (ModuleCat.{max u v} (ULift.{v} R))) : Prop where
  /-- The derived dual is perfect. -/
  dual_isPerfect : IsPerfect (derivedDual K)
  /-- The canonical biduality morphism `K ⟶ (Kᵛ)ᵛ` is an isomorphism. -/
  biduality_isIso : IsIso (biduality K)
  /-- Every component of the canonical comparison `L ⊗ᴸ Kᵛ ⟶ RHom(K, L)` is an isomorphism. -/
  tensorDualHom_isIso (L : DerivedCategory (ModuleCat.{max u v} (ULift.{v} R))) :
    IsIso (tensorDualHom K L)
  /-- The tensor--Hom comparison is natural in its target. -/
  tensorDualHom_naturality
      {L L' : DerivedCategory (ModuleCat.{max u v} (ULift.{v} R))} (f : L ⟶ L') :
    (derivedHomData (R := R)).tensor.map (f, 𝟙 (derivedDual K)) ≫ tensorDualHom K L' =
      tensorDualHom K L ≫ (derivedHomData (R := R)).hom.map (𝟙 (Opposite.op K), f)
  /-- Degree zero: there are isomorphisms `H⁰(L ⊗ᴸ Kᵛ) ≃+ Ext⁰(K, L)`, natural in `L`. -/
  exists_extZeroEquiv :
    ∃ e : ∀ L : DerivedCategory (ModuleCat.{max u v} (ULift.{v} R)),
        ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} (ULift.{v} R)) 0).obj
            ((derivedHomData (R := R)).tensor.obj (L, derivedDual K)) :
          Type (max u v)) ≃+ (K ⟶ L),
      ∀ {L L' : DerivedCategory (ModuleCat.{max u v} (ULift.{v} R))} (f : L ⟶ L')
        (a : (DerivedCategory.homologyFunctor (ModuleCat.{max u v} (ULift.{v} R)) 0).obj
          ((derivedHomData (R := R)).tensor.obj (L, derivedDual K))),
        e L' ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} (ULift.{v} R)) 0).map
            ((derivedHomData (R := R)).tensor.map (f, 𝟙 (derivedDual K))) a) = e L a ≫ f

/-- **Stacks 07VI.** Let `A` be a ring and let `K` be a perfect object of `D(A)`. Then the derived
dual `Kᵛ = RHom_A(K, A)` is perfect, the canonical morphism `K ⟶ (Kᵛ)ᵛ` is an isomorphism, the
canonical comparison `L ⊗_A^L Kᵛ ⟶ RHom_A(K, L)` is an isomorphism functorially in `L`, and
`H⁰(L ⊗_A^L Kᵛ) = Ext⁰_A(K, L)` functorially in `L`. -/
@[stacks 07VI, sga "6 I 7.7" "affine case", sga "6 I 7.3" "affine (ring) case"]
theorem isPerfect_derivedDual_and_naturalIsos
    (K : DerivedCategory (ModuleCat.{max u v} (ULift.{v} R))) (hK : IsPerfect K) :
    PerfectDerivedDuality K :=
  { dual_isPerfect := isPerfect_derivedDual K hK
    biduality_isIso := biduality_isIso K hK
    tensorDualHom_isIso := fun L => tensorHom_isIso K L hK
    tensorDualHom_naturality := fun f => tensorHom_natural K f
    exists_extZeroEquiv :=
      exists_extZeroEquiv_of K (fun L => tensorHom_isIso K L hK)
        (fun f => tensorHom_natural K f) }

end StacksDraft.Perfect

end
