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
import StacksCore.Tactic.StacksAttribute

/-!
# The derived dual of a complex of modules

Let `A` be a ring. This file defines the derived dual `Kᵛ = RHom_A(K, A)` of an object `K` of
`D(A)` and the two canonical morphisms of [stacks 07VI], proves the preliminary facts about
complexes used to study them, and identifies degree-zero homology with morphisms from the unit,
which gives the degree-zero clause of [stacks 07VI] once the tensor--Hom comparison is known to be
invertible.

## Main definitions

* `StacksDraft.Perfect.derivedDual`: the derived dual `RHom_A(K, A)`, for the canonical derived
  tensor--Hom adjunction of [stacks 0A63].
* `StacksDraft.Perfect.biduality`: the canonical morphism `K ⟶ (Kᵛ)ᵛ`, the transpose of the
  evaluation pairing after interchanging the tensor factors.
* `StacksDraft.Perfect.tensorDualHom`: the canonical comparison `L ⊗^L Kᵛ ⟶ RHom(K, L)`.

## Main results

* `StacksDraft.Perfect.single_derived_homology_bijective`: for a projective object `P` placed in
  degree `n`, morphisms from it to `X` in the derived category are morphisms `P ⟶ Hⁿ(X)`.
* `StacksDraft.Perfect.exists_extZeroEquiv_of`: if the tensor--Hom comparison is invertible and
  natural in its target, then `H⁰(L ⊗^L Kᵛ) ≃+ Ext⁰(K, L)` functorially in `L`.

## Implementation notes

Both canonical morphisms are *definitions* built from the fixed adjunction
`StacksDraft.DerivedHom.derivedHomAdjunctionULift` of [stacks 0A63] -- the biduality morphism is
the transpose of evaluation after the symmetry, and the tensor--Hom comparison is the transpose of
evaluation of the dual -- so [stacks 07VI] asserts that the canonical maps are invertible, not
merely that some isomorphisms exist.

Mathlib's monoidal category of modules forces the ring and module universes to agree, so -- as in
[stacks 0A63] -- the statement is phrased over `ULift.{v} R`, whose universe `max u v` also
accommodates the modules; the ring universe, the module enlargement and the derived-morphism
universe stay independent.

The degree-zero clause is the only one phrased existentially, as [stacks 07VI] phrases it. The
family of isomorphisms produced here is the homology of the tensor--Hom comparison followed by the
degree-zero identification `Hom_{D(A)}(A[0], RHom(K, L)) ≃+ Hom_{D(A)}(K, L)` of the adjunction,
composed with the canonical identification of `H⁰(X)` with `Hom_{D(A)}(A[0], X)`.

## References

* [Stacks Project, Tag 07VI](https://stacks.math.columbia.edu/tag/07VI)
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory CochainComplex CochainComplex.HomComplex
  HomologicalComplex

universe u v w

namespace StacksDraft.Perfect

open StacksDraft.DerivedHom Stacks.HomComplex.MonoidalClosed

section Homology

variable {C : Type u} [Category.{v} C] [Abelian C]

set_option backward.isDefEq.respectTransparency false

private theorem single_homology_surjective (P : C) [Projective P]
    (L : CochainComplex C ℤ) (n : ℤ) (h : P ⟶ L.homology n) :
    ∃ f : (single C (ComplexShape.up ℤ) n).obj P ⟶ L,
      (singleObjHomologySelfIso (ComplexShape.up ℤ) n P).inv ≫ homologyMap f n = h := by
  let z := Projective.factorThru h (L.homologyπ n)
  let f := mkHomFromSingle (z ≫ L.iCycles n) (by simp)
  refine ⟨f, ?_⟩
  rw [← singleObjCyclesSelfIso_inv_homologyπ, Category.assoc, homologyπ_naturality]
  have he : (singleObjCyclesSelfIso (ComplexShape.up ℤ) n P).inv ≫ cyclesMap f n = z := by
    apply (cancel_mono (L.iCycles n)).mp
    rw [Category.assoc, cyclesMap_i]
    dsimp only [f]
    rw [mkHomFromSingle_f]
    simp
  rw [← Category.assoc, he]
  exact Projective.factorThru_comp _ _

private theorem single_homology_zero (P : C) [Projective P]
    (L : CochainComplex C ℤ) (n : ℤ)
    (f : (single C (ComplexShape.up ℤ) n).obj P ⟶ L)
    (hf : homologyMap f n = 0) : Nonempty (Homotopy f 0) := by
  let z := (singleObjCyclesSelfIso (ComplexShape.up ℤ) n P).inv ≫ cyclesMap f n
  have hz : z ≫ L.homologyπ n = 0 := by
    dsimp [z]
    rw [Category.assoc, ← homologyπ_naturality, hf, Limits.comp_zero, Limits.comp_zero]
  obtain ⟨A, π, hπ, x, hx⟩ :=
    (L.comp_homologyπ_eq_zero_iff_up_to_refinements (n - 1) n (by simp) z).mp hz
  let k := Projective.factorThru (𝟙 P) π ≫ x
  have hk : k ≫ L.d (n - 1) n =
      (singleObjXSelf (ComplexShape.up ℤ) n P).inv ≫ f.f n := by
    calc
      _ = (Projective.factorThru (𝟙 P) π ≫ x ≫ L.toCycles (n-1) n) ≫ L.iCycles n := by simp [k]
      _ = z ≫ L.iCycles n := by rw [← hx]; simp
      _ = _ := by simp [z]
  refine ⟨(Cochain.equivHomotopy f 0).symm ⟨
    Cochain.single ((singleObjXSelf (ComplexShape.up ℤ) n P).hom ≫ k) (-1), ?_⟩⟩
  rw [Cochain.ofHom_zero, add_zero,
    Cochain.δ_single _ (-1) 0 (by decide) (n-1) n (by omega) (by omega)]
  simp only [single_obj_d, Limits.zero_comp, Cochain.single_zero, smul_zero, add_zero,
    Category.assoc, hk, Iso.hom_inv_id_assoc]
  funext T
  by_cases hi : T.p = n
  · have hT : T = ⟨n, n, add_zero n⟩ := by
      rcases T with ⟨i, j, hij⟩
      dsimp at hi
      have hj : j = n := by omega
      cases hi
      cases hj
      rfl
    subst T
    exact (Cochain.ofHom_v f n).trans
      (Cochain.single_v (f.f n) 0 (add_zero n)).symm
  · exact (isZero_single_obj_X (ComplexShape.up ℤ) n P T.p hi).eq_of_src _ _

private theorem Q_map_surjective_of_isKProjective [HasDerivedCategory.{w} C]
    (P L : CochainComplex C ℤ) [P.IsKProjective] :
    Function.Surjective (DerivedCategory.Q.map (X := P) (Y := L)) := by
  intro f
  let e := DerivedCategory.quotientCompQhIso C
  obtain ⟨g, hg⟩ := (CochainComplex.IsKProjective.Qh_map_bijective P
    ((HomotopyCategory.quotient C _).obj L)).surjective
      (e.hom.app P ≫ f ≫ e.inv.app L)
  obtain ⟨g, rfl⟩ := (HomotopyCategory.quotient C _).map_surjective g
  refine ⟨g, ?_⟩
  apply (cancel_epi (e.hom.app P)).mp
  rw [← DerivedCategory.quotientCompQhIso_hom_naturality, hg]
  simp [e]


private theorem single_derived_homology_bijective_model [HasDerivedCategory.{w} C]
    (P : C) [Projective P] (L : CochainComplex C ℤ) (n : ℤ) :
    let U := (single C (ComplexShape.up ℤ) n).obj P
    let H := DerivedCategory.homologyFunctor C n
    let e := (DerivedCategory.homologyFunctorFactors C n).app U ≪≫
      singleObjHomologySelfIso (ComplexShape.up ℤ) n P
    Function.Bijective (fun f : DerivedCategory.Q.obj U ⟶ DerivedCategory.Q.obj L =>
      e.inv ≫ H.map f) := by
  intro U H e
  have : CochainComplex.IsKProjective U := CochainComplex.isKProjective_of_projective U n
  let F := DerivedCategory.homologyFunctorFactors C n
  have nat (g : U ⟶ L) : H.map (DerivedCategory.Q.map g) ≫ F.hom.app L =
      F.hom.app U ≫ homologyMap g n := F.hom.naturality g
  constructor
  · intro f g hfg
    apply sub_eq_zero.mp
    obtain ⟨k, hk⟩ := Q_map_surjective_of_isKProjective U L (f - g)
    have hzero : H.map (DerivedCategory.Q.map k) = 0 := by
      rw [hk, Functor.map_sub]
      exact sub_eq_zero.mpr ((cancel_epi e.inv).mp hfg)
    have hkzero : homologyMap k n = 0 := by
      apply (cancel_epi (F.hom.app U)).mp
      rw [Limits.comp_zero]
      have hh := nat k
      rw [hzero, Limits.zero_comp] at hh
      exact hh.symm
    obtain ⟨ht⟩ := single_homology_zero P L n k hkzero
    rw [← hk, DerivedCategory.Q_map_eq_of_homotopy C ht, Functor.map_zero]
  · intro h
    obtain ⟨f, hf⟩ := single_homology_surjective P L n (h ≫ F.hom.app L)
    refine ⟨DerivedCategory.Q.map f, ?_⟩
    apply (cancel_mono (F.hom.app L)).mp
    rw [Category.assoc]
    rw [nat f]
    simpa [e, F, Category.assoc] using hf

/-- Let `P` be a projective object of `C` and `U` the complex with `P` in degree `n` and zero
elsewhere. For every object `X` of the derived category, taking `n`-th cohomology and
identifying `Hⁿ(U)` with `P` is a bijection from morphisms `U ⟶ X` in the derived category to
morphisms `P ⟶ Hⁿ(X)`. -/
theorem single_derived_homology_bijective [HasDerivedCategory.{w} C]
    (P : C) [Projective P] (X : DerivedCategory C) (n : ℤ) :
    let U := (single C (ComplexShape.up ℤ) n).obj P
    let H := DerivedCategory.homologyFunctor C n
    let e := (DerivedCategory.homologyFunctorFactors C n).app U ≪≫
      singleObjHomologySelfIso (ComplexShape.up ℤ) n P
    Function.Bijective (fun f : DerivedCategory.Q.obj U ⟶ X => e.inv ≫ H.map f) := by
  intro U H e
  let L := DerivedCategory.Q.objPreimage X
  let i := DerivedCategory.Q.objObjPreimageIso X
  have h₁ := (Iso.homCongr (Iso.refl (DerivedCategory.Q.obj U)) i.symm).bijective
  have h₂ := single_derived_homology_bijective_model P L n
  have h₃ := (Iso.homCongr (Iso.refl P) (H.mapIso i)).bijective
  have hh := h₃.comp (h₂.comp h₁)
  convert hh using 1
  ext f
  simp [Iso.homCongr, Functor.map_comp, Category.assoc, e, U, H]


end Homology

section Complexes

variable {R : Type u} [CommRing R]

set_option backward.isDefEq.respectTransparency false

def cochainSingleEquiv (P : CochainComplex (ModuleCat R) ℤ)
    (A : ModuleCat R) (n : ℤ) :
    Cochain P ((single (ModuleCat R) (ComplexShape.up ℤ) 0).obj A) n ≃ₗ[R]
      (P.X (-n) →ₗ[R] A) := by
  let e := singleObjXSelf (ComplexShape.up ℤ) 0 A
  refine { toFun := fun z => e.hom.hom.comp (z.v (-n) 0 (by omega)).hom
           invFun := fun f => Cochain.single (ModuleCat.ofHom f ≫ e.inv) n
           left_inv := ?_
           right_inv := ?_
           map_add' := ?_
           map_smul' := ?_ }
  · intro z z'
    simp only [Cochain.add_v, ModuleCat.hom_add, LinearMap.comp_add]
  · intro r z
    simp only [Cochain.smul_v, ModuleCat.hom_smul, LinearMap.comp_smul, RingHom.id_apply]
  · intro z
    apply Cochain.ext
    intro p q hpq
    by_cases hq : q = 0
    · rcases hq with rfl
      have hp : p = -n := by omega
      rcases hp with rfl
      simp only [Cochain.single_v]
      change (z.v (-n) 0 _) ≫ e.hom ≫ e.inv = _
      simp
    · exact (isZero_single_obj_X (ComplexShape.up ℤ) 0 A q hq).eq_of_tgt _ _
  · intro f
    simp only [Cochain.single_v]
    exact LinearMap.ext fun x => ConcreteCategory.congr_hom e.inv_hom_id (f x)

theorem homComplex_unit_finite_projective (P : CochainComplex (ModuleCat R) ℤ)
    [∀ i, Module.Finite R (P.X i)] [∀ i, Module.Projective R (P.X i)] (n : ℤ) :
    Module.Finite R ((HomComplexR R P (𝟙_ _)).X n) ∧
      Module.Projective R ((HomComplexR R P (𝟙_ _)).X n) := by
  let e := cochainSingleEquiv P (ModuleCat.of R R) n
  exact ⟨Module.Finite.equiv e.symm, Module.Projective.of_equiv e.symm⟩

private theorem homComplex_unit_isZero (P : CochainComplex (ModuleCat R) ℤ)
    (n : ℤ) (h : CategoryTheory.Limits.IsZero (P.X (-n))) :
    CategoryTheory.Limits.IsZero ((HomComplexR R P (𝟙_ _)).X n) := by
  let e := cochainSingleEquiv P (ModuleCat.of R R) n
  have : Subsingleton (P.X (-n)) := ModuleCat.subsingleton_of_isZero h
  have : Subsingleton ((HomComplexR R P (𝟙_ _)).X n) := e.injective.subsingleton
  exact ModuleCat.isZero_of_subsingleton _

theorem homComplex_unit_bounded (P : CochainComplex (ModuleCat R) ℤ)
    (a b : ℤ) [P.IsStrictlyGE a] [P.IsStrictlyLE b] :
    (HomComplexR R P (𝟙_ _)).IsStrictlyGE (-b) ∧
      (HomComplexR R P (𝟙_ _)).IsStrictlyLE (-a) := by
  constructor
  · rw [CochainComplex.isStrictlyGE_iff]
    intro n hn
    exact homComplex_unit_isZero P n (P.isZero_of_isStrictlyLE b (-n) (by omega))
  · rw [CochainComplex.isStrictlyLE_iff]
    intro n hn
    exact homComplex_unit_isZero P n (P.isZero_of_isStrictlyGE a (-n) (by omega))
end Complexes

/-! ## Inputs on K-flatness and the degree-zero comparison -/

section KFlatInputs

variable {R : Type u} [CommRing R]

/-- [stacks 064K] read at a module universe equal to the ring's: a bounded above cochain complex
of flat modules is K-flat. -/
theorem kFlatOfFlat
    (P : CochainComplex (ModuleCat.{max u v} (ULift.{v} R)) ℤ) (d : ℤ) [P.IsStrictlyLE d]
    [∀ n : ℤ, Module.Flat (ULift.{v} R) (P.X n)] : P.KFlat :=
  CochainComplex.KFlat.kFlat_of_flat.{max u v, max u v} P d

end KFlatInputs

/-! ## The derived dual and the two canonical morphisms -/

variable {R : Type u} [CommRing R]
  [HasDerivedCategory.{w} (ModuleCat.{max u v} (ULift.{v} R))]

/-- The tensor unit of cochain complexes: the ring, placed in degree zero. -/
abbrev unitComplex : CochainComplex (ModuleCat.{max u v} (ULift.{v} R)) ℤ :=
  𝟙_ (CochainComplex (ModuleCat.{max u v} (ULift.{v} R)) ℤ)

/-- The tensor unit of the derived category, the image of `unitComplex` under localization. -/
abbrev unitObject : DerivedCategory (ModuleCat.{max u v} (ULift.{v} R)) :=
  DerivedCategory.Q.obj (unitComplex (R := R))

/-- The canonical derived tensor--Hom adjunction of [stacks 0A63], in an independently chosen
module universe. -/
abbrev derivedHomData : DerivedHomData (ULift.{v} R) :=
  derivedHomAdjunctionULift

/-- The derived dual `Kᵛ = RHom(K, A)`, for the fixed derived-Hom construction
of [stacks 0A63]. -/
abbrev derivedDual (K : DerivedCategory (ModuleCat.{max u v} (ULift.{v} R))) :
    DerivedCategory (ModuleCat.{max u v} (ULift.{v} R)) :=
  (derivedHomData (R := R)).hom.obj (Opposite.op K, unitObject (R := R))

/-- The canonical map from an object to its double derived dual. It is the transpose of
evaluation after interchanging the two tensor factors. -/
def biduality (K : DerivedCategory (ModuleCat.{max u v} (ULift.{v} R))) :
    K ⟶ derivedDual (derivedDual K) :=
  let D := derivedHomData (R := R)
  (D.homEquiv K (derivedDual K) (unitObject (R := R))).symm
    ((D.tensorSwap K (derivedDual K)).hom ≫ D.evaluation K (unitObject (R := R)))

/-- The canonical comparison `L ⊗ᴸ Kᵛ ⟶ RHom(K, L)`. It is the transpose of evaluation of the
dual on `K`, followed by the tensor unit constraint. -/
def tensorDualHom (K L : DerivedCategory (ModuleCat.{max u v} (ULift.{v} R))) :
    (derivedHomData (R := R)).tensor.obj (L, derivedDual K) ⟶
      (derivedHomData (R := R)).hom.obj (Opposite.op K, L) :=
  let D := derivedHomData (R := R)
  (D.homEquiv (D.tensor.obj (L, derivedDual K)) K L).symm
    ((D.tensorAssoc L (derivedDual K) K).hom ≫
      D.tensor.map (𝟙 L, D.evaluation K (unitObject (R := R))) ≫
      (D.tensorSwap L (unitObject (R := R))).hom ≫ (D.tensorUnitLeft L).hom)

/-! ## The degree-zero identification of homology with morphisms from the unit -/

/-- The canonical class `1 ∈ H⁰(A[0])`. -/
private def unitHomologyClass :
    (DerivedCategory.homologyFunctor
      (ModuleCat.{max u v} (ULift.{v} R)) 0).obj (unitObject (R := R)) :=
  (DerivedCategory.homologyFunctorFactors
      (ModuleCat.{max u v} (ULift.{v} R)) 0).inv.app (unitComplex (R := R))
    ((HomologicalComplex.homologyFunctorSingleIso
      (ModuleCat.{max u v} (ULift.{v} R)) (ComplexShape.up ℤ) 0).inv.app
        (ModuleCat.of (ULift.{v} R) (ULift.{v} R)) (1 : ULift.{v} R))

/-- The canonical map `Hom_D(A[0],X) → H⁰(X)`, obtained by applying homology to a
derived morphism and evaluating it on the class of `1`.  Stacks 064B says this map is
bijective. -/
private def unitToHomology (X : DerivedCategory (ModuleCat.{max u v} (ULift.{v} R))) :
    (unitObject (R := R) ⟶ X) →+
      ((DerivedCategory.homologyFunctor
        (ModuleCat.{max u v} (ULift.{v} R)) 0).obj X : Type (max u v)) where
  toFun f := (DerivedCategory.homologyFunctor (ModuleCat.{max u v} (ULift.{v} R)) 0).map f
    (unitHomologyClass (R := R))
  map_zero' := by
    change ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} (ULift.{v} R)) 0).map
      (0 : unitObject (R := R) ⟶ X)) (unitHomologyClass (R := R)) = 0
    rw [Functor.map_zero]
    rfl
  map_add' f g := by
    change ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} (ULift.{v} R)) 0).map (f + g))
      (unitHomologyClass (R := R)) = _
    rw [Functor.map_add]
    rfl

set_option backward.isDefEq.respectTransparency false in
private theorem unitToHomology_bijective
    (X : DerivedCategory (ModuleCat.{max u v} (ULift.{v} R))) :
    Function.Bijective (unitToHomology X) := by
  let S := ULift.{v} R
  let M := (DerivedCategory.homologyFunctor (ModuleCat S) 0).obj X
  have h := single_derived_homology_bijective (ModuleCat.of S S) X 0
  have h' := ((LinearMap.ringLmapEquivSelf S S M).bijective.comp
    (ModuleCat.homLinearEquiv (M := ModuleCat.of S S) (N := M) (S := S)).bijective).comp h
  convert h' using 1
  funext f
  rfl

/-! ## The degree-zero clause -/

/-- An isomorphism of derived objects induces an additive isomorphism on degree-zero homology. -/
private def homologyZeroAddEquivOfIso
    {X Y : DerivedCategory (ModuleCat.{max u v} (ULift.{v} R))} (i : X ≅ Y) :
    ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} (ULift.{v} R)) 0).obj X :
        Type (max u v)) ≃+
      ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} (ULift.{v} R)) 0).obj Y :
        Type (max u v)) where
  toFun :=
    ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} (ULift.{v} R)) 0).mapIso i).hom
  invFun :=
    ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} (ULift.{v} R)) 0).mapIso i).inv
  left_inv a := ConcreteCategory.congr_hom
    ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} (ULift.{v} R)) 0).mapIso
      i).hom_inv_id a
  right_inv a := ConcreteCategory.congr_hom
    ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} (ULift.{v} R)) 0).mapIso
      i).inv_hom_id a
  map_add' a b :=
    (((DerivedCategory.homologyFunctor (ModuleCat.{max u v} (ULift.{v} R)) 0).mapIso
      i).hom).hom.map_add a b

/-- The canonical identification `H⁰(X) ≃+ Hom_{D(A)}(A[0], X)`, the inverse of the fixed
comparison map. -/
private def homologyUnitEquiv (X : DerivedCategory (ModuleCat.{max u v} (ULift.{v} R))) :
    ((DerivedCategory.homologyFunctor
        (ModuleCat.{max u v} (ULift.{v} R)) 0).obj X : Type (max u v)) ≃+
      (unitObject (R := R) ⟶ X) :=
  (AddEquiv.ofBijective (unitToHomology X) (unitToHomology_bijective X)).symm

private theorem homologyUnitEquiv_naturality
    {X Y : DerivedCategory (ModuleCat.{max u v} (ULift.{v} R))} (f : X ⟶ Y)
    (a : (DerivedCategory.homologyFunctor (ModuleCat.{max u v} (ULift.{v} R)) 0).obj X) :
    homologyUnitEquiv (R := R) Y ((DerivedCategory.homologyFunctor
      (ModuleCat.{max u v} (ULift.{v} R)) 0).map f a) =
      homologyUnitEquiv (R := R) X a ≫ f := by
  apply (unitToHomology_bijective Y).injective
  rw [homologyUnitEquiv, AddEquiv.ofBijective_apply_symm_apply]
  show _ = (DerivedCategory.homologyFunctor (ModuleCat.{max u v} (ULift.{v} R)) 0).map
    (homologyUnitEquiv (R := R) X a ≫ f) (unitHomologyClass (R := R))
  rw [Functor.map_comp_apply]
  exact congrArg ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} (ULift.{v} R)) 0).map f)
    (AddEquiv.apply_symm_apply
      (AddEquiv.ofBijective (unitToHomology X) (unitToHomology_bijective X)) a).symm

/-- The degree-zero derived-Hom/Ext comparison `H⁰(RHom(K, L)) ≃+ Ext⁰(K, L)`. -/
private def derivedHomologyExtEquiv
    (K L : DerivedCategory (ModuleCat.{max u v} (ULift.{v} R))) :
    ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} (ULift.{v} R)) 0).obj
        ((derivedHomData (R := R)).hom.obj (Opposite.op K, L)) : Type (max u v)) ≃+
      (K ⟶ L) :=
  (homologyUnitEquiv _).trans ((derivedHomData (R := R)).homZeroEquiv K L)

private theorem derivedHomologyExtEquiv_naturality
    (K : DerivedCategory (ModuleCat.{max u v} (ULift.{v} R)))
    {L L' : DerivedCategory (ModuleCat.{max u v} (ULift.{v} R))} (f : L ⟶ L')
    (a : (DerivedCategory.homologyFunctor (ModuleCat.{max u v} (ULift.{v} R)) 0).obj
      ((derivedHomData (R := R)).hom.obj (Opposite.op K, L))) :
    derivedHomologyExtEquiv K L'
        ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} (ULift.{v} R)) 0).map
      ((derivedHomData (R := R)).hom.map (𝟙 (Opposite.op K), f)) a) =
      derivedHomologyExtEquiv K L a ≫ f := by
  simp only [derivedHomologyExtEquiv, AddEquiv.trans_apply]
  rw [homologyUnitEquiv_naturality]
  let D := derivedHomData (R := R)
  let b := homologyUnitEquiv (R := R) (D.hom.obj (Opposite.op K, L)) a
  show (D.tensorUnitLeft K).inv ≫
      D.homEquiv (unitObject (R := R)) K L'
        (b ≫ D.hom.map (𝟙 (Opposite.op K), f)) =
    ((D.tensorUnitLeft K).inv ≫ D.homEquiv (unitObject (R := R)) K L b) ≫ f
  rw [D.homEquiv_naturality_right]
  simp only [Category.assoc]

/-- The degree-zero comparison `H⁰(L ⊗ᴸ Kᵛ) ≃+ Ext⁰(K, L)` induced by an invertible
tensor--Hom comparison. -/
private def extZeroEquivOf
    (K L : DerivedCategory (ModuleCat.{max u v} (ULift.{v} R)))
    (h : IsIso (tensorDualHom K L)) :
    ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} (ULift.{v} R)) 0).obj
        ((derivedHomData (R := R)).tensor.obj (L, derivedDual K)) : Type (max u v)) ≃+
      (K ⟶ L) :=
  letI := h
  (homologyZeroAddEquivOfIso (asIso (tensorDualHom K L))).trans (derivedHomologyExtEquiv K L)

theorem exists_extZeroEquiv_of
    (K : DerivedCategory (ModuleCat.{max u v} (ULift.{v} R)))
    (hIso : ∀ L : DerivedCategory (ModuleCat.{max u v} (ULift.{v} R)),
      IsIso (tensorDualHom K L))
    (hNat : ∀ {L L' : DerivedCategory (ModuleCat.{max u v} (ULift.{v} R))} (f : L ⟶ L'),
      (derivedHomData (R := R)).tensor.map (f, 𝟙 (derivedDual K)) ≫ tensorDualHom K L' =
        tensorDualHom K L ≫ (derivedHomData (R := R)).hom.map (𝟙 (Opposite.op K), f)) :
    ∃ e : ∀ L : DerivedCategory (ModuleCat.{max u v} (ULift.{v} R)),
        ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} (ULift.{v} R)) 0).obj
            ((derivedHomData (R := R)).tensor.obj (L, derivedDual K)) :
          Type (max u v)) ≃+ (K ⟶ L),
      ∀ {L L' : DerivedCategory (ModuleCat.{max u v} (ULift.{v} R))} (f : L ⟶ L')
        (a : (DerivedCategory.homologyFunctor (ModuleCat.{max u v} (ULift.{v} R)) 0).obj
          ((derivedHomData (R := R)).tensor.obj (L, derivedDual K))),
        e L' ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} (ULift.{v} R)) 0).map
            ((derivedHomData (R := R)).tensor.map (f, 𝟙 (derivedDual K))) a) = e L a ≫ f := by
  refine ⟨fun L => extZeroEquivOf K L (hIso L), fun {L L'} f a => ?_⟩
  show derivedHomologyExtEquiv K L'
      ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} (ULift.{v} R)) 0).map
        (tensorDualHom K L')
        ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} (ULift.{v} R)) 0).map
          ((derivedHomData (R := R)).tensor.map (f, 𝟙 (derivedDual K))) a)) =
    derivedHomologyExtEquiv K L
      ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} (ULift.{v} R)) 0).map
        (tensorDualHom K L) a) ≫ f
  rw [← Functor.map_comp_apply, hNat, Functor.map_comp_apply]
  exact derivedHomologyExtEquiv_naturality K f _

end StacksDraft.Perfect

end
