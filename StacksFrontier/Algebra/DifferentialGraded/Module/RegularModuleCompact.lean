module

public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedCategoryCoproducts
public import StacksFrontier.Algebra.DifferentialGraded.Module.RegularModuleCohomology
public import StacksFrontier.CategoryTheory.Triangulated.CompactObjects

/-! # The regular module is a compact object of the derived category

Let `(A, d)` be a differential graded algebra over a commutative ring `R`, regarded as a right
differential graded module over itself. Its image in the derived category `D(A, d)` is a compact
object: for every family `Fᵢ`, `i ∈ I`, of objects of `D(A, d)` the canonical map
$$\bigoplus\nolimits_i \Hom_{D(A, d)}(A, F_i) \longrightarrow
\Hom_{D(A, d)}(A, \coprod\nolimits_i F_i)$$
is bijective, so a morphism from `A` into a direct sum factors through a finite subsum in exactly
one way.

## Main definitions

* `DifferentialGradedModule.rightMulHom`: right multiplication by a cocycle of degree zero, as a
  homomorphism of differential graded modules out of the regular module.

## Main results

* `DifferentialGradedModule.hom_ext_toFun_one`: a homomorphism out of the regular module is
  determined by its value at the unit.
* `DifferentialGradedModule.exists_eq_sum_comp_directSumInj`: a homomorphism from the regular
  module into a direct sum of differential graded modules is a finite sum of homomorphisms into
  the summands, composed with the coprojections.
* `DifferentialGradedModule.isCompactObject_q_regularModule`: the image of the regular module in
  `D(A, d)` is a compact object.

## Implementation notes

*The three reductions.* Compactness of an object `K` is the bijectivity of the maps
`⨁ᵢ (K ⟶ Fᵢ) → (K ⟶ ∐ᵢ Fᵢ)` for arbitrary families of objects of `D(A, d)`. Three steps bring
that to a statement about homomorphisms of differential graded modules.

First the family is replaced by one of the shape `Nᵢ ↦ Q(Nᵢ)` with `Nᵢ` a differential graded
module: the localization functor is essentially surjective, and the homotopy category is a
quotient category, so every object of `D(A, d)` is isomorphic to the image of a module. The
image of the concrete direct sum `DifferentialGradedModule.directSumObj` is then a direct sum in
`D(A, d)` by Tag 09QI, and bijectivity of the test map is invariant under an isomorphism
of the family and of its vertex (`CategoryTheory.bijective_cofanMap_of_iso`), so it suffices to
test the cofan of coprojections of `⨁ᵢ Nᵢ`.

Second that test map splits into its two halves, and only one of them is about the regular
module. Injectivity is formal: the test map of *any* colimit cofan is injective
(`CategoryTheory.injective_cofanMap`), which Tag 09QI again supplies.

Third, surjectivity is moved from `D(A, d)` to `K(A, d)` and computed there. Every shift of the
regular module is orthogonal on the left to the acyclic modules (Tag 09K1), so localizing at the
quasi-isomorphisms does not change the morphisms out of it; this is
`DifferentialGradedModule.quasiIsomorphismsQ_map_bijective_regularModule`, which is already
stated for an arbitrary target, and a morphism of `K(A, d)` is the homotopy class of a
homomorphism. What is left is the computation of the homomorphisms out of the regular module: a
homomorphism `A ⟶ N` is right multiplication by its value at `1`, which is a cocycle of degree
zero because `d 1 = 0`, and conversely right multiplication by such a cocycle is a homomorphism;
in a direct sum that value has finite support, so the homomorphism is the corresponding finite
sum of homomorphisms into the summands.

As everywhere in this chapter's differential graded interface, the base ring, the algebra and the
modules all live in a single universe `u`, and the index type of a direct sum is taken in that
universe as well, so compactness is tested against exactly the families whose direct sums the
chapter provides.

*No tag.* The chapter uses the compactness of the regular module — it is how hypothesis (1) of
[Stacks, Tag 09R9] reads for the regular bimodule — but states it nowhere as a result of its own,
so no `@[stacks ...]` attribute appears below.

## References

* [Stacks Project, Tag 07LS](https://stacks.math.columbia.edu/tag/07LS) for compactness,
  [Tag 09QI](https://stacks.math.columbia.edu/tag/09QI) for the direct sums of `D(A, d)`, and
  [Tag 09K1](https://stacks.math.columbia.edu/tag/09K1) for the morphisms out of the regular
  module.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped DirectSum

universe u

namespace DifferentialGradedModule

variable {R : Type u} [CommRing R] {A : DifferentialGradedAlgebra R}

/-! ### Homomorphisms out of the regular module -/

section Regular

variable {M : DifferentialGradedModule A}

/-- Right multiplication by a cocycle `x` of degree zero of a right differential graded module
`M`, as a homomorphism `A ⟶ M` of differential graded modules out of the regular module. -/
def rightMulHom (x : M.M) (hx : x ∈ M.grading 0) (hdx : M.d x = 0) : regularModule A ⟶ M where
  toFun :=
    { toFun := fun a => MulOpposite.op a • x
      map_add' := fun a b => by rw [MulOpposite.op_add, add_smul]
      map_smul' := fun r a => by
        change MulOpposite.op (r • a) • x = r • (MulOpposite.op a • x)
        rw [MulOpposite.op_smul, smul_assoc] }
  map_smul b a := by
    have h : (MulOpposite.op a • b : A.A) = b * a := by
      simp only [MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op]
    change MulOpposite.op (MulOpposite.op a • b : A.A) • x
      = MulOpposite.op a • (MulOpposite.op b • x)
    rw [h, MulOpposite.op_mul, mul_smul]
  map_grading n b hb := by
    have hb' : b ∈ A.grading n := hb
    change MulOpposite.op b • x ∈ M.grading n
    simpa only [zero_add] using M.smul_mem 0 n x b hx hb'
  map_d := LinearMap.ext fun b => by
    change MulOpposite.op (A.d b) • x = M.d (MulOpposite.op b • x)
    rw [M.leibniz_apply 0 x hx b, hdx, smul_zero, zero_add, Int.negOnePow_zero, Units.val_one,
      one_smul]

/-- Right multiplication acts by right multiplication. -/
@[simp] theorem rightMulHom_toFun_apply (x : M.M) (hx : x ∈ M.grading 0) (hdx : M.d x = 0)
    (a : A.A) : (rightMulHom x hx hdx).toFun a = MulOpposite.op a • x :=
  rfl

/-- Right multiplication by `x` sends the unit to `x`. -/
@[simp] theorem rightMulHom_toFun_one (x : M.M) (hx : x ∈ M.grading 0) (hdx : M.d x = 0) :
    (rightMulHom x hx hdx).toFun (1 : A.A) = x := by
  rw [rightMulHom_toFun_apply, MulOpposite.op_one, one_smul]

/-- A homomorphism out of the regular module is right multiplication by its value at the
unit. -/
theorem toFun_eq_op_smul_toFun_one (f : regularModule A ⟶ M) (a : A.A) :
    f.toFun a = MulOpposite.op a • f.toFun (1 : A.A) := by
  simpa only [MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op, one_mul] using
    f.map_smul (1 : A.A) a

/-- Two homomorphisms out of the regular module agreeing at the unit are equal. -/
theorem hom_ext_toFun_one {f g : regularModule A ⟶ M}
    (h : f.toFun (1 : A.A) = g.toFun (1 : A.A)) : f = g :=
  Hom.ext (LinearMap.ext fun a => by
    rw [toFun_eq_op_smul_toFun_one f a, toFun_eq_op_smul_toFun_one g a, h])

/-- The value at the unit of a homomorphism out of the regular module is homogeneous of degree
zero. -/
theorem toFun_one_mem_grading (f : regularModule A ⟶ M) : f.toFun (1 : A.A) ∈ M.grading 0 :=
  f.map_grading 0 (1 : A.A) (SetLike.one_mem_graded A.grading)

/-- The value at the unit of a homomorphism out of the regular module is a cocycle. -/
theorem d_toFun_one (f : regularModule A ⟶ M) : M.d (f.toFun (1 : A.A)) = 0 := by
  have h : f.toFun (A.d (1 : A.A)) = M.d (f.toFun (1 : A.A)) :=
    LinearMap.congr_fun f.map_d (1 : A.A)
  rw [← h, A.d_one, map_zero]

/-- Evaluation at the unit, as an additive map on the homomorphisms out of the regular
module. -/
def evalAtOne (M : DifferentialGradedModule A) : (regularModule A ⟶ M) →+ M.M where
  toFun f := f.toFun (1 : A.A)
  map_zero' := by rw [Hom.hom_zero_toFun, LinearMap.zero_apply]
  map_add' f g := by rw [Hom.hom_add_toFun, LinearMap.add_apply]

/-- The value at the unit of a finite sum of homomorphisms out of the regular module. -/
theorem toFun_one_sum {ι : Type*} (s : Finset ι) (f : ι → (regularModule A ⟶ M)) :
    (∑ i ∈ s, f i).toFun (1 : A.A) = ∑ i ∈ s, (f i).toFun (1 : A.A) :=
  map_sum (evalAtOne M) f s

end Regular

/-! ### Homomorphisms from the regular module into a direct sum -/

section DirectSum

variable {ι : Type u} [DecidableEq ι] (N : ι → DifferentialGradedModule A)

/-- **A homomorphism from the regular module into a direct sum factors through a finite
subsum.** It is a finite sum of homomorphisms into the summands, composed with the
coprojections. -/
theorem exists_eq_sum_comp_directSumInj (g : regularModule A ⟶ directSumObj N) :
    ∃ (s : Finset ι) (h : ∀ i, regularModule A ⟶ N i),
      g = ∑ i ∈ s, h i ≫ directSumInj N i := by
  classical
  obtain ⟨v, hv⟩ : ∃ v : ⨁ i, (N i).M, g.toFun (1 : A.A) = v := ⟨_, rfl⟩
  have hmem : ∀ i, v i ∈ (N i).grading 0 := hv ▸ toFun_one_mem_grading g
  have hd : ∀ i, (N i).d (v i) = 0 := by
    intro i
    have h0 : directSumD N (g.toFun (1 : A.A)) = 0 := d_toFun_one g
    rw [hv] at h0
    rw [← directSumD_apply N v i, h0, DirectSum.zero_apply]
  refine ⟨DFinsupp.support v, fun i => rightMulHom (v i) (hmem i) (hd i), hom_ext_toFun_one ?_⟩
  rw [toFun_one_sum, hv]
  refine (DirectSum.sum_support_of v).symm.trans (Finset.sum_congr rfl fun i _ => ?_)
  rw [Hom.comp_toFun_apply, rightMulHom_toFun_one, directSumInj_toFun_apply,
    DirectSum.lof_eq_of]

end DirectSum

/-! ### Compactness of the regular module -/

section Compact

/-- The canonical functor from differential graded modules to the derived category: the quotient
by homotopy followed by the localization at the quasi-isomorphisms. -/
private abbrev toDerived (A : DifferentialGradedAlgebra R) :
    DifferentialGradedModule A ⥤ derivedCategory' A :=
  toHomotopyCategory A ⋙ (quasiIsomorphisms' A).Q

variable (A : DifferentialGradedAlgebra R) {ι : Type u} [DecidableEq ι]
  (N : ι → DifferentialGradedModule A)

/-- The images in `D(A, d)` of the coprojections of `⨁ᵢ Nᵢ` exhibit the image of `⨁ᵢ Nᵢ` as a
direct sum: **Tag 09QI**. -/
private def isColimitCofanDerived :
    IsColimit (Cofan.mk ((toDerived A).obj (directSumObj N))
      fun i => (toDerived A).map (directSumInj N i)) :=
  isColimitCofanMkObjOfIsColimit (toDerived A) N (directSumInj N) (isColimit_directSumObj N)

/-- Every morphism of `D(A, d)` from the regular module into the image of `⨁ᵢ Nᵢ` is the image of
a finite sum of morphisms into the images of the summands. -/
private theorem surjective_cofanMap_directSumInj :
    Function.Surjective (cofanMap ((toDerived A).obj (regularModule A))
      fun i => (toDerived A).map (directSumInj N i)) := by
  classical
  intro Ψ
  obtain ⟨ψ, hψ⟩ := (quasiIsomorphismsQ_map_bijective_regularModule A
    ((toHomotopyCategory A).obj (directSumObj N))).2 Ψ
  obtain ⟨g, rfl⟩ : ∃ g : regularModule A ⟶ directSumObj N,
      (toHomotopyCategory A).map g = ψ := by
    induction ψ using Quot.inductionOn with
    | _ g => exact ⟨g, rfl⟩
  obtain ⟨s, h, hsum⟩ := exists_eq_sum_comp_directSumInj N g
  refine ⟨∑ i ∈ s, DirectSum.of _ i ((toDerived A).map (h i)), ?_⟩
  rw [map_sum]
  simp only [cofanMap_of, ← Functor.map_comp]
  rw [← Functor.map_sum, ← hsum]
  exact hψ

/-- The canonical map `⨁ᵢ Hom(A, Q(Nᵢ)) → Hom(A, Q(⨁ᵢ Nᵢ))` is bijective. -/
private theorem bijective_cofanMap_directSumInj :
    Function.Bijective (cofanMap ((toDerived A).obj (regularModule A))
      fun i => (toDerived A).map (directSumInj N i)) :=
  ⟨injective_cofanMap _ _ (isColimitCofanDerived A N),
    surjective_cofanMap_directSumInj A N⟩

/-- The canonical map `⨁ᵢ Hom(A, Fᵢ) → Hom(A, ∐ᵢ Fᵢ)` is bijective for a family of objects of
`D(A, d)` presented as the images of a family of differential graded modules. -/
private theorem bijective_cofanMap_sigmaι_of_iso (F : ι → derivedCategory' A) [HasCoproduct F]
    (e : ∀ i, (toDerived A).obj (N i) ≅ F i) :
    Function.Bijective
      (cofanMap ((toDerived A).obj (regularModule A)) (Limits.Sigma.ι F)) :=
  bijective_cofanMap_of_iso _ (fun i => (toDerived A).map (directSumInj N i))
    (Limits.Sigma.ι F) e
    ((isColimitCofanDerived A N).coconePointsIsoOfNatIso (coproductIsCoproduct F)
      (Discrete.natIso fun i => e i.as))
    (fun i => (isColimitCofanDerived A N).comp_coconePointsIsoOfNatIso_hom
      (coproductIsCoproduct F) (Discrete.natIso fun i => e i.as) ⟨i⟩)
    (bijective_cofanMap_directSumInj A N)

/-- **The regular module is a compact object of the derived category.** Let `(A, d)` be a
differential graded algebra over a commutative ring `R`. The image of the regular module `A` in
`D(A, d)` is a compact object: for every family `Fᵢ` of objects of `D(A, d)` indexed by a type of
the ambient universe the canonical map `⨁ᵢ Hom(A, Fᵢ) → Hom(A, ∐ᵢ Fᵢ)` is bijective. -/
instance isCompactObject_q_regularModule :
    IsCompactObject.{u}
      ((toHomotopyCategory A ⋙ (quasiIsomorphisms' A).Q).obj (regularModule A)) where
  bijective_toAddMonoid_rightComp_sigmaι F :=
    bijective_cofanMap_sigmaι_of_iso A
      (fun i => ((quasiIsomorphisms' A).Q.objPreimage (F i)).as) F
      (fun i => (quasiIsomorphisms' A).Q.objObjPreimageIso (F i))

end Compact

end DifferentialGradedModule

end
