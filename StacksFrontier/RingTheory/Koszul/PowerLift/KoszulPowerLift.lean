module

public import StacksFrontier.Algebra.Homology.DerivedCategory.ProjectiveCorepresents
public import StacksFrontier.Homology.DerivedComplete.AdicKoszulPowerDefs
import all StacksFrontier.RingTheory.Koszul.PowerLift.KoszulTorsion

@[expose] public noncomputable section

/-!
# Lifting a degree-zero class along a Koszul complex on powers

Let `A` be a commutative ring, let `f₁, …, f_r ∈ A` and let `E` be an object of `D(A)` whose
cohomology modules in the degrees `-r + 1, …, 0` are `f_i`-power torsion for every `i`. Then
every morphism `s : A[0] ⟶ E` factors through the canonical map
`A[0] ⟶ K(f₁^{e+1}, …, f_r^{e+1})` for some exponent `e`.

The proof is an induction on the length of the sequence. The Koszul complex of a sequence of
length `r + 1` is the mapping cone of multiplication by its last entry on the Koszul complex of
the first `r` entries ([Stacks, Tag 0629]); so a lift over the shorter complex extends over the
longer one as soon as multiplication by that entry annihilates it, and
`Stacks.Koszul.PowerLift.homPowerTorsion_koszul` says some power of it does. Raising the common
exponent past that power is what makes the obstruction vanish *on the nose* rather than only up
to a power, and that is the whole content of the lemma.

The map produced by the cone is a priori only *some* morphism `A[0] ⟶ K`, not the canonical one
of [Stacks, Tag 0BKC]. It is identified with a multiple of the canonical one by
`Stacks.Koszul.PowerLift.exists_smul_koszulPowerUnit`: the Koszul complex lives in nonpositive
degrees with `A` in degree `0`, so `Hom_{D(A)}(A[0], K)` is the cyclic module `H⁰(K)` generated
by the canonical map, and *every* morphism out of `A[0]` is an `A`-multiple of it. This is what
removes the need to compare the cone presentation with the canonical augmentation.

## Main results

* `Stacks.Koszul.PowerLift.exists_smul_koszulPowerUnit` — every morphism from `A[0]` into a
  Koszul power complex is an `A`-multiple of the canonical one.
* `Stacks.Koszul.PowerLift.exists_koszulPower_lift_koszulCochain` — **[Stacks, Tag 08E3] over a
  ring, at an arbitrary derived category of `A`-modules**: a degree-zero class of a complex with
  power-torsion cohomology in the relevant range factors through a Koszul complex on positive
  powers of the sequence.
* `Stacks.Koszul.PowerLift.exists_koszulPower_lift` — the same statement with the target read as
  a term of `AdicKoszul.canonicalKoszulPowerSystem`, which is available only at
  `CategoryTheory.HasDerivedCategory.standard`.

## Implementation notes

Everything except the last theorem carries a free `[HasDerivedCategory.{w} (ModuleCat.{u} A)]`
binder, so [Stacks, Tag 08E3] is available here at the locally small model
`ModuleCat.hasDerivedCategory` (`StacksFrontier/AlgebraicGeometry/DerivedTilde/Basic.lean`), where
the morphisms of `D(A)` are in `Type u`, as well as at the standard one. This matters because
[Stacks, Tag 09IR] and [Stacks, Tag 0A9A] need Brown representability, hence coproducts of the
derived category at its own morphism universe, which the standard model of `D(ModuleCat A)` does
not have; and a statement proved only at the standard model says nothing about another one, the
two derived categories being merely equivalent and not equal. It is also the model at which the
affine comparison `D(A) ≌ D_QCoh(𝒪_{Spec A})` of [Stacks, Tag 06Z0] is stated, in
`AlgebraicGeometry.derivedGlobalSectionsQuasicoherent`.

Three results this file rests on used to bake the standard model into their types, and all three
are now stated at a free model binder of their own, each proof having turned out to use only
model-agnostic Mathlib:
`StrongGeneration.derived_single_map_eq_zero`
(`StacksFrontier/Homology/DerivedCategory/StrongGenerator.lean`) uses `DerivedCategory.Q.objPreimage`,
`DerivedCategory.quotientCompQhIso` and `CochainComplex.IsKProjective.Qh_map_bijective`;
`PrincipalTorsionTower.homologyFunctor_map_Q_smul_id`
(`StacksFrontier/Homology/DerivedComplete/PrincipalTorsionTower.lean`) uses
`DerivedCategory.homologyFunctorFactors` and a statement about cochain complexes; and
`KoszulTensorVanishing.koszul_empty_iso_single`
(`StacksFrontier/Homology/DerivedComplete/KoszulTensorVanishing.lean`) is the image under
`DerivedCategory.Q` of an isomorphism of cochain complexes. The three files still pin the
standard model at file level for their other declarations; only these three carry a binder.

The one spelling that cannot be freed is `AdicKoszul.canonicalKoszulPowerSystem`, defined in
`StacksFrontier/Homology/DerivedComplete/AdicKoszulPowerDefs.lean` under a file-level local instance
of the standard model, so the model is in its type with no instance argument to supply. That is
why the Koszul power complex is written out as
`DerivedCategory.Q.obj ((ComplexShape.embeddingDownNat.extendFunctor _).obj (Koszul.seqComplex
(fun i ↦ f i ^ (e + 1))))` in the free-model statement; the two agree at the standard model, where
`exists_koszulPower_lift` records the system form. `AdicKoszul.koszulPowerUnit` itself is a
morphism of cochain complexes and mentions no derived category, so it needs no restatement.

With `pp.explicit` on, `HasDerivedCategory.standard` occurs 0 times in the
types of `exists_koszulPower_lift_koszulCochain`, `exists_smul_koszulPowerUnit` and
`homPowerTorsion_koszul`, each carrying exactly one free `HasDerivedCategory` binder instead; it
occurs 76 times in that of `exists_koszulPower_lift`, by design.

Everything else used here was already model-free: the triangle calculus of
`StacksFrontier/RingTheory/Koszul/PowerLift/HomTorsion.lean`, the Koszul cone of
[Stacks, Tag 0629], `DerivedCategory.mappingCone_triangle_distinguished`, and
`DerivedCategory.homologyFromSingleLinearEquiv`.

The hypothesis on `E` is the algebraic form of the geometric hypothesis of [Stacks, Tag 08E3],
that the cohomology sheaves of `E` vanish on the union of the principal opens `D(f_i)` in the
degrees `-r + 1, …, 0`: vanishing on `D(f_i)` of a quasi-coherent sheaf is the statement that
every element of the corresponding module is annihilated by a power of `f_i`.

## References

* [Stacks Project, Tag 08E3](https://stacks.math.columbia.edu/tag/08E3)
* [Stacks Project, Tag 0629](https://stacks.math.columbia.edu/tag/0629)
* [Stacks Project, Tag 0BKC](https://stacks.math.columbia.edu/tag/0BKC)
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped ExteriorAlgebra

universe u w

namespace Stacks.Koszul.PowerLift

variable {A : Type u} [CommRing A]

/-! ### The canonical map from the ring, in degree zero -/

/-- The canonical map `A ⟶ K(f^{n+1})` of [Stacks, Tag 0BKC] sends `a` to `a` times the unit of
the exterior algebra in degree zero. -/
private theorem koszulPowerUnitChain_f_zero_apply {r : ℕ} (f : Fin r → A) (n : ℕ) (a : A) :
    (AdicKoszul.koszulPowerUnitChain f n).f 0 a =
      a • (⟨ExteriorAlgebra.ιMulti A 0 (fun i ↦ Fin.elim0 i),
        Koszul.ιMulti_mem 0 (fun i ↦ Fin.elim0 i)⟩ : ⋀[A]^0 (Fin r → A)) :=
  (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec
    (Classical.choose_spec (_root_.koszulPowerComplexes_form_inverseSystem f))))).2.2.2.2.2.1 n a

/-- The canonical maps `A ⟶ K(f^{n+1})` are compatible with the transition maps of the
Koszul power system. -/
private theorem koszulPowerUnitChain_transition {r : ℕ} (f : Fin r → A) (m n : ℕ) (h : n ≤ m) :
    AdicKoszul.koszulPowerUnitChain f m ≫ AdicKoszul.koszulPowerTransition f m n h =
      AdicKoszul.koszulPowerUnitChain f n :=
  (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec
    (Classical.choose_spec
      (_root_.koszulPowerComplexes_form_inverseSystem f))))).2.2.2.2.2.2.1 m n h

/-- The canonical map `A ⟶ K(f^{n+1})` is surjective in degree zero: the zeroth exterior power
is free of rank one on the unit. -/
private theorem epi_koszulPowerUnitChain_f_zero {r : ℕ} (f : Fin r → A) (n : ℕ) :
    Epi ((AdicKoszul.koszulPowerUnitChain f n).f 0) := by
  rw [ModuleCat.epi_iff_surjective]
  intro x
  refine ⟨exteriorPower.zeroEquiv A (Fin r → A) x, ?_⟩
  have hx := koszulPowerUnitChain_f_zero_apply f n (exteriorPower.zeroEquiv A (Fin r → A) x)
  refine hx.trans ?_
  apply (exteriorPower.zeroEquiv A (Fin r → A)).injective
  rw [map_smul]
  change (exteriorPower.zeroEquiv A (Fin r → A) x) •
      (exteriorPower.zeroEquiv A (Fin r → A))
        (exteriorPower.ιMulti A 0 (fun i ↦ Fin.elim0 i)) = _
  rw [exteriorPower.zeroEquiv_ιMulti, smul_eq_mul, mul_one]

/-! ### Morphisms out of the ring in degree zero -/

/-- `CategoryTheory.epi_comp` with both epimorphism assumptions taken as explicit arguments, so
that it can be applied without instance search. -/
private theorem epi_comp' {C : Type*} [Category C] {X Y Z : C} (g : X ⟶ Y) (h : Y ⟶ Z)
    (hg : Epi g) (hh : Epi h) : Epi (g ≫ h) :=
  @epi_comp _ _ _ _ _ _ hg _ hh

/-- The forward map of an isomorphism is an epimorphism, with the isomorphism explicit. -/
private theorem epi_iso_hom {C : Type*} [Category C] {X Y : C} (e : X ≅ Y) : Epi e.hom :=
  IsIso.epi_of_iso _

/-- The backward map of an isomorphism is an epimorphism, with the isomorphism explicit. -/
private theorem epi_iso_inv {C : Type*} [Category C] {X Y : C} (e : X ≅ Y) : Epi e.inv :=
  IsIso.epi_of_iso _

/-- A component of the backward natural transformation of an isomorphism of functors is an
epimorphism, with the isomorphism explicit. -/
private theorem epi_natIso_inv_app {C D : Type*} [Category C] [Category D] {F G : C ⥤ D}
    (e : F ≅ G) (X : C) : Epi (e.inv.app X) :=
  IsIso.epi_of_iso _

/-- The embedding `n ↦ -n` of nonnegative homological degrees into cohomological degrees sends
`0` to `0`. Spelled as a lemma rather than `rfl` so that the terms built from it stay
type-correct at reducible transparency. -/
private theorem embeddingDownNat_f_zero : ComplexShape.embeddingDownNat.f 0 = 0 := by
  simp only [ComplexShape.embeddingDownNat_f, CharP.cast_eq_zero, neg_zero]

/-- A morphism out of the single complex `A[0]` of cochain complexes is determined by its
component in degree zero. -/
private theorem hom_from_single_ext {Y : CochainComplex (ModuleCat.{u} A) ℤ}
    (φ ψ : ((CochainComplex.singleFunctors (ModuleCat.{u} A)).functor 0).obj
        (ModuleCat.of A A) ⟶ Y)
    (h : φ.f 0 = ψ.f 0) : φ = ψ := by
  refine HomologicalComplex.hom_ext _ _ fun i => ?_
  by_cases hi : i = 0
  · subst hi; exact h
  · exact (HomologicalComplex.isZero_single_obj_X _ _ _ _ hi).eq_of_src _ _

/-- The target of the canonical map is zero in degree one, the Koszul complex being supported in
nonpositive degrees. -/
private theorem isZero_koszulPowerCochain_X_one {r : ℕ} (g : Fin r → A) :
    IsZero (((ComplexShape.embeddingDownNat.extendFunctor (ModuleCat.{u} A)).obj
      (Koszul.seqComplex g)).X 1) := by
  apply HomologicalComplex.isZero_extend_X (Koszul.seqComplex g)
    ComplexShape.embeddingDownNat 1
  intro j
  change -(j : ℤ) ≠ 1
  omega

/-- The identification of the degree-zero term of the extended Koszul complex with the
degree-zero term of the Koszul complex itself, written with the extension spelled as the value of
`ComplexShape.Embedding.extendFunctor`, which is the spelling the Koszul power system uses. -/
private def koszulCochainXZeroIso {r : ℕ} (g : Fin r → A) :
    ((ComplexShape.embeddingDownNat.extendFunctor (ModuleCat.{u} A)).obj
        (Koszul.seqComplex g)).X 0 ≅ (Koszul.seqComplex g).X 0 :=
  HomologicalComplex.extendXIso (Koszul.seqComplex g) ComplexShape.embeddingDownNat
    (i := 0) (i' := 0) embeddingDownNat_f_zero

/-- The chain-level map `A ⟶ K(f^{n+1})` of [Stacks, Tag 0BKC] read with source the ring itself.
Naming it isolates the identification of `A` with the degree-zero term of the single complex,
which is an equality of definitions and not of syntax. -/
private def koszulPowerUnitZero {r : ℕ} (f : Fin r → A) (n : ℕ) :
    (((CochainComplex.singleFunctors (ModuleCat.{u} A)).functor 0).obj (ModuleCat.of A A)).X 0 ⟶
      (Koszul.seqComplex (fun i ↦ f i ^ (n + 1))).X 0 :=
  (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (ModuleCat.of A A)).hom ≫
    (AdicKoszul.koszulPowerUnitChain f n).f 0

/-- `Stacks.Koszul.PowerLift.koszulPowerUnitZero` is surjective. -/
private theorem epi_koszulPowerUnitZero {r : ℕ} (f : Fin r → A) (n : ℕ) :
    Epi (koszulPowerUnitZero f n) :=
  epi_comp' _ _ (epi_iso_hom _) (epi_koszulPowerUnitChain_f_zero f n)

/-- `Stacks.Koszul.PowerLift.koszulPowerUnitZero` is compatible with the transition maps. -/
private theorem koszulPowerUnitZero_transition {r : ℕ} (f : Fin r → A) (m n : ℕ) (h : n ≤ m) :
    koszulPowerUnitZero f m ≫ (AdicKoszul.koszulPowerTransition f m n h).f 0 =
      koszulPowerUnitZero f n :=
  (Category.assoc _ _ _).trans
    (congrArg (fun z ↦
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (ModuleCat.of A A)).hom ≫ z)
      (((HomologicalComplex.comp_f (AdicKoszul.koszulPowerUnitChain f m)
            (AdicKoszul.koszulPowerTransition f m n h) 0).symm.trans
        (congrArg (fun ψ ↦ HomologicalComplex.Hom.f ψ 0)
          (koszulPowerUnitChain_transition f m n h)))))

/-- The degree-zero component of the canonical map `A[0] ⟶ K(f^{n+1})` of cochain complexes. -/
private theorem koszulPowerUnit_f_zero {r : ℕ} (f : Fin r → A) (n : ℕ) :
    (AdicKoszul.koszulPowerUnit f n).f 0 =
      koszulPowerUnitZero f n ≫ (koszulCochainXZeroIso (fun i ↦ f i ^ (n + 1))).inv :=
  (HomologicalComplex.mkHomFromSingle_f _ _).trans (Category.assoc _ _ _).symm

/-- The canonical map `A[0] ⟶ K(f^{n+1})` is surjective in degree zero. -/
private theorem epi_koszulPowerUnit_f_zero {r : ℕ} (f : Fin r → A) (n : ℕ) :
    Epi ((AdicKoszul.koszulPowerUnit f n).f 0) := by
  rw [koszulPowerUnit_f_zero]
  exact epi_comp' _ _ (epi_koszulPowerUnitZero f n) (epi_iso_inv _)

/-- **The canonical map is surjective on degree-zero cohomology.** The Koszul complex is
supported in nonpositive degrees, so its degree-zero cohomology is a quotient of its degree-zero
term, and the canonical map is already surjective there. -/
private theorem epi_homologyMap_koszulPowerUnit {r : ℕ} (f : Fin r → A) (n : ℕ) :
    Epi (HomologicalComplex.homologyMap (AdicKoszul.koszulPowerUnit f n) 0) := by
  set S := ((CochainComplex.singleFunctors (ModuleCat.{u} A)).functor 0).obj
    (ModuleCat.of A A) with hS
  set Y := (ComplexShape.embeddingDownNat.extendFunctor (ModuleCat.{u} A)).obj
    (Koszul.seqComplex (fun i ↦ f i ^ (n + 1))) with hY
  have hnext : (ComplexShape.up ℤ).next 0 = 1 := by simp only [CochainComplex.next, zero_add]
  have hdY : Y.d 0 1 = 0 := (isZero_koszulPowerCochain_X_one _).eq_of_tgt _ _
  have hdS : S.d 0 1 = 0 := by
    rw [hS]; exact HomologicalComplex.single_obj_d _ _ _ _ _
  have hSiso : IsIso (S.iCycles 0) := HomologicalComplex.isIso_iCycles S 0 1 hnext hdS
  have hYiso : IsIso (Y.iCycles 0) := HomologicalComplex.isIso_iCycles Y 0 1 hnext hdY
  have hcyc : Epi (HomologicalComplex.cyclesMap (AdicKoszul.koszulPowerUnit f n) 0) := by
    have hfac : HomologicalComplex.cyclesMap (AdicKoszul.koszulPowerUnit f n) 0 =
        (S.iCycles 0 ≫ (AdicKoszul.koszulPowerUnit f n).f 0) ≫ inv (Y.iCycles 0) := by
      rw [← HomologicalComplex.cyclesMap_i, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
    rw [hfac]
    have := epi_koszulPowerUnit_f_zero f n
    infer_instance
  have hcomp : Epi (S.homologyπ 0 ≫
      HomologicalComplex.homologyMap (AdicKoszul.koszulPowerUnit f n) 0) := by
    rw [HomologicalComplex.homologyπ_naturality]
    infer_instance
  exact epi_of_epi (S.homologyπ 0) _

section FreeModel

variable [HasDerivedCategory.{w} (ModuleCat.{u} A)]

/-- **The canonical map is surjective on degree-zero cohomology of the derived category.** -/
private theorem epi_derivedHomologyMap_koszulPowerUnit {r : ℕ} (f : Fin r → A) (n : ℕ) :
    Epi ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).map
      (DerivedCategory.Q.map (AdicKoszul.koszulPowerUnit f n))) := by
  have hepi : Epi ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).map
      (DerivedCategory.Q.map (AdicKoszul.koszulPowerUnit f n)) ≫
      (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} A) 0).hom.app
        ((ComplexShape.embeddingDownNat.extendFunctor (ModuleCat.{u} A)).obj
          (Koszul.seqComplex (fun i ↦ f i ^ (n + 1))))) := by
    rw [DerivedCategory.homologyFunctorFactors_hom_naturality]
    exact epi_comp' _ _ (IsIso.epi_of_iso _) (epi_homologyMap_koszulPowerUnit f n)
  have hfac : (DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).map
      (DerivedCategory.Q.map (AdicKoszul.koszulPowerUnit f n)) =
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).map
          (DerivedCategory.Q.map (AdicKoszul.koszulPowerUnit f n)) ≫
        (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} A) 0).hom.app
          ((ComplexShape.embeddingDownNat.extendFunctor (ModuleCat.{u} A)).obj
            (Koszul.seqComplex (fun i ↦ f i ^ (n + 1))))) ≫
      inv ((DerivedCategory.homologyFunctorFactors (ModuleCat.{u} A) 0).hom.app
        ((ComplexShape.embeddingDownNat.extendFunctor (ModuleCat.{u} A)).obj
          (Koszul.seqComplex (fun i ↦ f i ^ (n + 1))))) := by
    rw [Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  rw [hfac]
  exact epi_comp' _ _ hepi (IsIso.epi_of_iso _)

/-- **Every morphism from `A[0]` to a Koszul power complex is a multiple of the canonical one.**
The Koszul complex of `f^{n+1}` is supported in nonpositive degrees with `A` in degree `0`, so
`Hom_{D(A)}(A[0], K)` is `H⁰(K)`, a cyclic `A`-module generated by the canonical map of
[Stacks, Tag 0BKC]. -/
public theorem exists_smul_koszulPowerUnit {r : ℕ} (f : Fin r → A) (n : ℕ)
    (w : DerivedCategory.Q.obj
        (((CochainComplex.singleFunctors (ModuleCat.{u} A)).functor 0).obj
          (ModuleCat.of A A)) ⟶
      DerivedCategory.Q.obj
        ((ComplexShape.embeddingDownNat.extendFunctor (ModuleCat.{u} A)).obj
          (Koszul.seqComplex (fun i ↦ f i ^ (n + 1))))) :
    ∃ c : A, w = c • DerivedCategory.Q.map (AdicKoszul.koszulPowerUnit f n) := by
  set U := DerivedCategory.Q.map (AdicKoszul.koszulPowerUnit f n) with hU
  set L := DerivedCategory.homologyFromSingleLinearEquiv (ModuleCat.of A A)
    (DerivedCategory.Q.obj
      ((ComplexShape.embeddingDownNat.extendFunctor (ModuleCat.{u} A)).obj
        (Koszul.seqComplex (fun i ↦ f i ^ (n + 1))))) 0 A with hL
  have hepi : Epi (L U) := by
    rw [hL, DerivedCategory.homologyFromSingleLinearEquiv_apply]
    exact epi_comp' _ _ (epi_natIso_inv_app _ _) (epi_derivedHomologyMap_koszulPowerUnit f n)
  obtain ⟨c, hc⟩ := (ModuleCat.epi_iff_surjective (L U)).1 hepi
    ((ConcreteCategory.hom (L w)) (1 : A))
  refine ⟨c, L.injective ?_⟩
  rw [map_smul]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  have hone : ∀ (N : ModuleCat.{u} A) (φ : ModuleCat.of A A ⟶ N) (y : A),
      (ConcreteCategory.hom φ) y = y • (ConcreteCategory.hom φ) (1 : A) := fun N φ y ↦ by
    simpa using (map_smul (ConcreteCategory.hom φ) y (1 : A))
  have h1 := hone _ (L w) x
  have h2 := hone _ (L U) c
  have h3 := hone _ (L U) x
  change (ConcreteCategory.hom (L w)) x = (ConcreteCategory.hom (c • L U)) x
  rw [h1, ← hc, h2]
  change _ = c • (ConcreteCategory.hom (L U)) x
  rw [h3, smul_comm]

/-! ### The induction -/

/-- For the empty sequence the Koszul power complex is the ring in degree zero. This repackages
`KoszulTensorVanishing.koszul_empty_iso_single` with its source and target written in the
spelling used by `AdicKoszul.koszulPowerUnit`. -/
private theorem exists_iso_koszulPowerCochain_single (f : Fin 0 → A) (n : ℕ) :
    Nonempty (DerivedCategory.Q.obj
        ((ComplexShape.embeddingDownNat.extendFunctor (ModuleCat.{u} A)).obj
          (Koszul.seqComplex (fun i ↦ f i ^ (n + 1)))) ≅
      DerivedCategory.Q.obj
        (((CochainComplex.singleFunctors (ModuleCat.{u} A)).functor 0).obj
          (ModuleCat.of A A))) :=
  ⟨KoszulTensorVanishing.koszul_empty_iso_single (fun i ↦ f i ^ (n + 1))⟩

omit [HasDerivedCategory.{w} (ModuleCat.{u} A)] in
/-- The sequence of `(e+1)`-st powers of an appended sequence is the appending of the powers. -/
private theorem snoc_pow {r : ℕ} (f : Fin r → A) (a : A) (e : ℕ) :
    Fin.snoc (fun i : Fin r ↦ f i ^ (e + 1)) (a ^ (e + 1)) =
      fun i ↦ (Fin.snoc f a : Fin (r + 1) → A) i ^ (e + 1) := by
  funext i
  refine Fin.lastCases ?_ (fun j ↦ ?_) i <;> simp only [Fin.snoc_last, Fin.snoc_castSucc]

/-- Raising the exponent of a lift along the canonical maps of the Koszul power system. -/
private theorem exists_lift_of_le {r : ℕ} (f : Fin r → A)
    {E : DerivedCategory (ModuleCat.{u} A)}
    {s : DerivedCategory.Q.obj
      (((CochainComplex.singleFunctors (ModuleCat.{u} A)).functor 0).obj
        (ModuleCat.of A A)) ⟶ E} {n : ℕ}
    (t : DerivedCategory.Q.obj
      ((ComplexShape.embeddingDownNat.extendFunctor (ModuleCat.{u} A)).obj
        (Koszul.seqComplex (fun i ↦ f i ^ (n + 1)))) ⟶ E)
    (ht : s = DerivedCategory.Q.map (AdicKoszul.koszulPowerUnit f n) ≫ t)
    (m : ℕ) (hm : n ≤ m) :
    ∃ t' : DerivedCategory.Q.obj
      ((ComplexShape.embeddingDownNat.extendFunctor (ModuleCat.{u} A)).obj
        (Koszul.seqComplex (fun i ↦ f i ^ (m + 1)))) ⟶ E,
      s = DerivedCategory.Q.map (AdicKoszul.koszulPowerUnit f m) ≫ t' ∧
        ∀ b : A, ∀ k : ℕ, b ^ k • t = 0 → b ^ k • t' = 0 := by
  refine ⟨DerivedCategory.Q.map ((ComplexShape.embeddingDownNat.extendFunctor
    (ModuleCat.{u} A)).map (AdicKoszul.koszulPowerTransition f m n hm)) ≫ t, ?_, ?_⟩
  · rw [ht, ← Category.assoc, ← DerivedCategory.Q.map_comp]
    congr 2
    refine hom_from_single_ext _ _ ?_
    have hτ : ((ComplexShape.embeddingDownNat.extendFunctor (ModuleCat.{u} A)).map
          (AdicKoszul.koszulPowerTransition f m n hm)).f 0 =
        (koszulCochainXZeroIso (fun i ↦ f i ^ (m + 1))).hom ≫
          (AdicKoszul.koszulPowerTransition f m n hm).f 0 ≫
          (koszulCochainXZeroIso (fun i ↦ f i ^ (n + 1))).inv :=
      HomologicalComplex.extendMap_f _ ComplexShape.embeddingDownNat (i := 0) (i' := 0)
        embeddingDownNat_f_zero
    rw [HomologicalComplex.comp_f, koszulPowerUnit_f_zero, koszulPowerUnit_f_zero, hτ]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    rw [← Category.assoc (koszulPowerUnitZero f m), koszulPowerUnitZero_transition f m n hm]
  · intro b k hk
    rw [← Linear.comp_smul, hk, comp_zero]

/-- `DerivedCategory.Q` is `A`-linear, so it sends a scalar multiple of an identity to the
scalar multiple of an identity. -/
private theorem Q_map_smul_id (K : CochainComplex (ModuleCat.{u} A) ℤ) (b : A) :
    DerivedCategory.Q.map (b • 𝟙 K) = b • 𝟙 (DerivedCategory.Q.obj K) := by
  rw [Functor.Linear.map_smul, CategoryTheory.Functor.map_id]

/-- A morphism out of the middle vertex of a distinguished triangle which is killed by the first
morphism factors through any object isomorphic to the third vertex. Stated for an abstract
pretriangulated category, so that the reassociation is carried out where the objects are opaque
variables. -/
private theorem exists_factor_of_iso_obj₃ {C : Type*} [Category C] [Preadditive C]
    [HasZeroObject C] [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    (T : Triangle C) (hT : T ∈ distTriang C) {X E : C} (ε : X ≅ T.obj₃)
    (t : T.obj₂ ⟶ E) (ht : T.mor₁ ≫ t = 0) :
    ∃ (ι : T.obj₂ ⟶ X) (u : X ⟶ E), t = ι ≫ u := by
  obtain ⟨w, hw⟩ := T.yoneda_exact₂ hT t ht
  refine ⟨T.mor₂ ≫ ε.inv, ε.hom ≫ w, ?_⟩
  rwa [Category.assoc, Iso.inv_hom_id_assoc]

/-- **The lifting step, from [Stacks, Tag 0629].** In `D(A)` the Koszul complex on the
`(e+1)`-st powers of `Fin.snoc g a` is the cone of multiplication by `a ^ (e+1)` on the Koszul
complex on the `(e+1)`-st powers of `g`. Consequently a morphism out of the latter which is
annihilated by `a ^ (e+1)` factors through the former. -/
private theorem exists_factor_koszulPower_snoc {r : ℕ} (g : Fin r → A) (a : A) (e : ℕ)
    {E : DerivedCategory (ModuleCat.{u} A)}
    (t : DerivedCategory.Q.obj ((ComplexShape.embeddingDownNat.extendFunctor
        (ModuleCat.{u} A)).obj (Koszul.seqComplex (fun i ↦ g i ^ (e + 1)))) ⟶ E)
    (ht : (a ^ (e + 1)) • t = 0) :
    ∃ (ι : DerivedCategory.Q.obj ((ComplexShape.embeddingDownNat.extendFunctor
            (ModuleCat.{u} A)).obj (Koszul.seqComplex (fun i ↦ g i ^ (e + 1)))) ⟶
          DerivedCategory.Q.obj ((ComplexShape.embeddingDownNat.extendFunctor
            (ModuleCat.{u} A)).obj (Koszul.seqComplex
              (fun i ↦ (Fin.snoc g a : Fin (r + 1) → A) i ^ (e + 1)))))
        (u : DerivedCategory.Q.obj ((ComplexShape.embeddingDownNat.extendFunctor
            (ModuleCat.{u} A)).obj (Koszul.seqComplex
              (fun i ↦ (Fin.snoc g a : Fin (r + 1) → A) i ^ (e + 1)))) ⟶ E),
      t = ι ≫ u := by
  obtain ⟨ε₀⟩ := exists_iso_koszulCochain_snoc (fun i : Fin r ↦ g i ^ (e + 1)) (a ^ (e + 1))
  rw [snoc_pow g a e] at ε₀
  have hdist := DerivedCategory.mappingCone_triangle_distinguished
    ((a ^ (e + 1)) • 𝟙 ((ComplexShape.embeddingDownNat.extendFunctor (ModuleCat.{u} A)).obj
      (Koszul.seqComplex (fun i : Fin r ↦ g i ^ (e + 1)))))
  obtain ⟨ε⟩ : Nonempty (DerivedCategory.Q.obj ((ComplexShape.embeddingDownNat.extendFunctor
          (ModuleCat.{u} A)).obj (Koszul.seqComplex
            (fun i ↦ (Fin.snoc g a : Fin (r + 1) → A) i ^ (e + 1)))) ≅
      (DerivedCategory.Q.mapTriangle.obj (CochainComplex.mappingCone.triangle
        ((a ^ (e + 1)) • 𝟙 ((ComplexShape.embeddingDownNat.extendFunctor
          (ModuleCat.{u} A)).obj (Koszul.seqComplex
            (fun i : Fin r ↦ g i ^ (e + 1))))))).obj₃) :=
    ⟨DerivedCategory.Q.mapIso ε₀⟩
  have hmor : (DerivedCategory.Q.mapTriangle.obj (CochainComplex.mappingCone.triangle
      ((a ^ (e + 1)) • 𝟙 ((ComplexShape.embeddingDownNat.extendFunctor (ModuleCat.{u} A)).obj
        (Koszul.seqComplex (fun i : Fin r ↦ g i ^ (e + 1))))))).mor₁ ≫ t = 0 := by
    change DerivedCategory.Q.map ((a ^ (e + 1)) • 𝟙
      ((ComplexShape.embeddingDownNat.extendFunctor (ModuleCat.{u} A)).obj
        (Koszul.seqComplex (fun i : Fin r ↦ g i ^ (e + 1))))) ≫ t = 0
    rw [Q_map_smul_id, Linear.smul_comp, Category.id_comp, ht]
  exact exists_factor_of_iso_obj₃ _ hdist ε t hmor

/-- The inductive core of [Stacks, Tag 08E3]: a degree-zero class of `E` factors through a
Koszul complex on a common positive power of the sequence. -/
private theorem exists_koszulPower_lift_aux (E : DerivedCategory (ModuleCat.{u} A)) :
    ∀ (r : ℕ) (f : Fin r → A),
      (∀ i : Fin r, ∀ n : ℤ, -(r : ℤ) + 1 ≤ n → n ≤ 0 →
        ∀ x : (DerivedCategory.homologyFunctor (ModuleCat.{u} A) n).obj E,
          ∃ k : ℕ, f i ^ k • x = 0) →
      ∀ s : DerivedCategory.Q.obj
        (((CochainComplex.singleFunctors (ModuleCat.{u} A)).functor 0).obj
          (ModuleCat.of A A)) ⟶ E,
      ∃ e : ℕ, ∃ t : DerivedCategory.Q.obj
          ((ComplexShape.embeddingDownNat.extendFunctor (ModuleCat.{u} A)).obj
            (Koszul.seqComplex (fun i ↦ f i ^ (e + 1)))) ⟶ E,
        s = DerivedCategory.Q.map (AdicKoszul.koszulPowerUnit f e) ≫ t := by
  intro r
  induction r with
  | zero =>
    intro f _ s
    obtain ⟨θ⟩ := exists_iso_koszulPowerCochain_single f 0
    obtain ⟨c, hc⟩ := exists_smul_koszulPowerUnit f 0 θ.inv
    refine ⟨0, θ.hom ≫ (c • s), ?_⟩
    have hid : c • (DerivedCategory.Q.map (AdicKoszul.koszulPowerUnit f 0) ≫ θ.hom) = 𝟙 _ := by
      rw [← Linear.smul_comp, ← hc, Iso.inv_hom_id]
    rw [Linear.comp_smul, Linear.comp_smul, ← Category.assoc, ← Linear.smul_comp, hid,
      Category.id_comp]
  | succ r ih =>
    intro f hE s
    -- write the sequence as a shorter sequence with a last entry appended
    obtain ⟨g, a, rfl⟩ : ∃ (g : Fin r → A) (a : A), f = Fin.snoc g a :=
      ⟨Fin.init f, f (Fin.last r), (Fin.snoc_init_self f).symm⟩
    -- the induction hypothesis for the shorter sequence
    obtain ⟨e₀, t₀, ht₀⟩ := ih g
      (fun i m hm₁ hm₂ x ↦ by
        have h := hE i.castSucc m (by push_cast; omega) hm₂ x
        rwa [Fin.snoc_castSucc] at h) s
    -- some power of the last entry annihilates the lift
    obtain ⟨k, hk⟩ := homPowerTorsion_koszul a E (fun i : Fin r ↦ g i ^ (e₀ + 1))
      (fun m hm₁ hm₂ x ↦ by
        have h := hE (Fin.last r) m (by push_cast; omega) hm₂ x
        rwa [Fin.snoc_last] at h) t₀
    -- raise the exponent past that power
    obtain ⟨t₁, ht₁, hzero⟩ := exists_lift_of_le g t₀ ht₀ (max e₀ k) (le_max_left _ _)
    have hak : a ^ (max e₀ k + 1) • t₁ = 0 := by
      have h0 : a ^ k • t₁ = 0 := hzero a k hk
      have hpow : a ^ (max e₀ k + 1) = a ^ (max e₀ k + 1 - k) * a ^ k := by
        rw [← pow_add,
          Nat.sub_add_cancel (le_trans (le_max_right e₀ k) (Nat.le_succ (max e₀ k)))]
      rw [hpow, mul_smul, h0, smul_zero]
    -- the lift extends over the cone, which is the longer Koszul complex
    obtain ⟨ι, v, hv⟩ := exists_factor_koszulPower_snoc g a (max e₀ k) t₁ hak
    -- the resulting map out of `A[0]` is a multiple of the canonical one
    obtain ⟨c, hc⟩ := exists_smul_koszulPowerUnit (Fin.snoc g a) (max e₀ k)
      (DerivedCategory.Q.map (AdicKoszul.koszulPowerUnit g (max e₀ k)) ≫ ι)
    refine ⟨max e₀ k, c • v, ?_⟩
    rwa [Linear.comp_smul, ← Linear.smul_comp, ← hc, Category.assoc, ← hv]

/-- **[Stacks, Tag 08E3] over a ring, at an arbitrary derived category of `A`-modules.** Let `A`
be a commutative ring, `f₁, …, f_r ∈ A` and `E` an object of `D(A)` such that every element of
`Hⁿ(E)` is annihilated by a power of `f_i`, for every `i` and every `n` with `-r + 1 ≤ n ≤ 0`.
Then every morphism `s : A[0] ⟶ E` factors through the canonical map
`A[0] ⟶ K(f₁^{e+1}, …, f_r^{e+1})` of [Stacks, Tag 0BKC], for some exponent `e`.

Geometrically `E` is a complex with quasi-coherent cohomology on `Spec A` whose cohomology
sheaves vanish on the union `U = ⋃ᵢ D(f_i)` in the degrees `-r + 1, …, 0`, and the conclusion
says a global section of `E` comes from the Koszul complex on a sufficiently high power of the
sequence cutting out the complement of `U`.

The Koszul power complex is written out as the localization of the extended Koszul complex rather
than as a term of `AdicKoszul.canonicalKoszulPowerSystem`, which is the one spelling that would
force a model: that system is defined under a file-level local instance of
`CategoryTheory.HasDerivedCategory.standard`, so the model is baked into its type and no free
binder can reach it. The two statements agree at the standard model, where
`Stacks.Koszul.PowerLift.exists_koszulPower_lift` records the system form. -/
public theorem exists_koszulPower_lift_koszulCochain {r : ℕ} (f : Fin r → A)
    (E : DerivedCategory (ModuleCat.{u} A))
    (hE : ∀ i : Fin r, ∀ n : ℤ, -(r : ℤ) + 1 ≤ n → n ≤ 0 →
      ∀ x : (DerivedCategory.homologyFunctor (ModuleCat.{u} A) n).obj E,
        ∃ k : ℕ, f i ^ k • x = 0)
    (s : DerivedCategory.Q.obj
      (((CochainComplex.singleFunctors (ModuleCat.{u} A)).functor 0).obj
        (ModuleCat.of A A)) ⟶ E) :
    ∃ e : ℕ, ∃ t : DerivedCategory.Q.obj
        ((ComplexShape.embeddingDownNat.extendFunctor (ModuleCat.{u} A)).obj
          (Koszul.seqComplex (fun i ↦ f i ^ (e + 1)))) ⟶ E,
      s = DerivedCategory.Q.map (AdicKoszul.koszulPowerUnit f e) ≫ t :=
  exists_koszulPower_lift_aux E r f hE s

end FreeModel

section Standard

attribute [local instance] HasDerivedCategory.standard

/-- **[Stacks, Tag 08E3] over a ring**, with the target read as a term of the canonical Koszul
power system `AdicKoszul.canonicalKoszulPowerSystem`. That system is defined at
`CategoryTheory.HasDerivedCategory.standard`, so this form of the statement is available only at
that model; `Stacks.Koszul.PowerLift.exists_koszulPower_lift_koszulCochain` is the same result at
an arbitrary one. -/
@[stacks 08E3]
public theorem exists_koszulPower_lift {r : ℕ} (f : Fin r → A)
    (E : DerivedCategory (ModuleCat.{u} A))
    (hE : ∀ i : Fin r, ∀ n : ℤ, -(r : ℤ) + 1 ≤ n → n ≤ 0 →
      ∀ x : (DerivedCategory.homologyFunctor (ModuleCat.{u} A) n).obj E,
        ∃ k : ℕ, f i ^ k • x = 0)
    (s : DerivedCategory.Q.obj
      (((CochainComplex.singleFunctors (ModuleCat.{u} A)).functor 0).obj
        (ModuleCat.of A A)) ⟶ E) :
    ∃ e : ℕ, ∃ t : (AdicKoszul.canonicalKoszulPowerSystem f).obj ⟨e⟩ ⟶ E,
      s = DerivedCategory.Q.map (AdicKoszul.koszulPowerUnit f e) ≫ t :=
  exists_koszulPower_lift_aux E r f hE s

end Standard

end Stacks.Koszul.PowerLift

end
