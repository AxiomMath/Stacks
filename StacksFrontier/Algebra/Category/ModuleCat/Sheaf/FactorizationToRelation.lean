module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPullbackFactorizationSheaf
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatRelations

/-! # Reading a finite-free factorization as the relation it factors

Let `(C, J)` be a site, `R` a sheaf of rings on it whose sections commute, and `M` a sheaf of
`R`-modules.  A rank-`l` factorization of `n` sections — `n` coefficients `a`, `l` generators `t`
and an `l × n` matrix `B` with `∑ᵢ Bₖᵢ aᵢ = 0` for every `k` — determines the `n`-term relation
whose coefficients are the `aᵢ` and whose elements are the `∑ₖ Bₖᵢ • tₖ`; that it *is* a
relation is the matrix condition, reassociated.

This file builds that morphism of sheaves of sets,

`factorizationToRelation : factorizationSheaf R M n l ⟶ relationSheaf R M n`,

and proves that it commutes with the inverse image along a left exact functor between categories
of sheaves of sets.  The two halves of Stacks 08FC part (2) — the relations and the
factorizations — are thereby both carried along the inverse image, compatibly, which is what
Stacks 05VD needs.

## Main definitions

* `Stacks.Sheaves.RelationSheaf.factorizationToRelationAmbient`: the morphism of ambient products
  `Rⁿ ⨯ (Mˡ ⨯ (Rⁿ)ˡ) ⟶ Rⁿ ⨯ Mⁿ` keeping the coefficients and exhibiting the elements.
* `Stacks.Sheaves.RelationSheaf.factorizationToRelation`: the morphism of sheaves of sets.

## Main results

* `Stacks.Sheaves.RelationSheaf.factorizationToRelation_comp_relationIota`: the underlying
  generalized element of the relation a factorization factors.
* `Stacks.Sheaves.ToposPullback.inv_comp_map_toRelationAmbient` and
  `factorizationSheafComparison_comp_factorizationToRelation`: **the inverse image of
  `factorizationToRelation` is `factorizationToRelation` of the inverse images**, conjugated by
  the two comparison morphisms, at the level of the ambient products and then of the sheaves.

## Implementation notes

**Commutativity of the sections of `R` is a hypothesis, not an instance**, exactly as in
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatRelations`: the matrix condition contracts the
matrix on the left while the relation contracts the coefficients on the left, and the two are
interchanged by `Stacks.SheafOfModules.sum_sum_mul_smul`, which takes commutativity as an
argument for the reason recorded there.  A sheaf of commutative rings supplies the hypothesis
through `CategoryTheory.Sheaf.hom_mul_comm`.

**The whole computation happens among generalized elements of shape `factorizationSheaf R M n l`,
not of shape the ambient product.**  The matrix condition is only available after composing with
`factorizationIota` — it is the equalizer condition — so the morphism whose contraction has to be
shown to vanish is `factorizationIota ≫ factorizationToRelationAmbient`, and the rewriting is
done on its composites with the projections.

**The inverse-image square is checked after composing with `Φ.map relationIota`**, which is a
monomorphism because `relationIota` is one and `Φ` is left exact.  The resulting identity between
morphisms into `Φ (Rⁿ ⨯ Mⁿ)` is then checked against the projections of that product, which the
comparison isomorphism of
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPullbackRelationSheaf` identifies with the
inverse images of `relationCoeff` and `relationElt`.

## References

* [Stacks Project, Tag 08FC](https://stacks.math.columbia.edu/tag/08FC)
* [Stacks Project, Tag 05VD](https://stacks.math.columbia.edu/tag/05VD)
* [Stacks Project, Tag 03D2](https://stacks.math.columbia.edu/tag/03D2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite CategoryTheory.Sheaf

universe w v u

namespace Stacks.Sheaves.RelationSheaf

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget RingCat.{w})] [J.HasSheafCompose (forget AddCommGrpCat.{w})]
  (R : Sheaf J RingCat.{w}) (M : SheafOfModules.{w} R) (n l : ℕ)

/-- The morphism of ambient products underlying `factorizationToRelation`: a factorization is
sent to the pair consisting of its coefficients and of the elements `∑ₖ Bₖᵢ • tₖ` it exhibits. -/
def factorizationToRelationAmbient :
    factorizationAmbient R M n l ⟶ relationAmbient R M n :=
  Limits.prod.lift (Limits.Pi.lift (factorizationCoeff R M n l))
    (Limits.Pi.lift (factorizationElt R M n l))

/-- The `i`-th coefficient of the relation a factorization factors is the `i`-th coefficient of
the factorization. -/
lemma factorizationToRelationAmbient_comp_relationCoeff (i : Fin n) :
    factorizationToRelationAmbient R M n l ≫ relationCoeff R M n i =
      factorizationCoeff R M n l i := by
  simp [factorizationToRelationAmbient, relationCoeff]

/-- The `i`-th element of the relation a factorization factors is `∑ₖ Bₖᵢ • tₖ`. -/
lemma factorizationToRelationAmbient_comp_relationElt (i : Fin n) :
    factorizationToRelationAmbient R M n l ≫ relationElt R M n i =
      factorizationElt R M n l i := by
  simp [factorizationToRelationAmbient, relationElt]

variable (hc : ∀ (X : Cᵒᵖ) (x y : (sectionsFunctor J X).obj (ringSheaf R)), x * y = y * x)

include hc in
/-- **The relation a factorization factors is a relation.**  The contraction of the coefficients
against the exhibited elements vanishes on the sheaf of factorizations, by the matrix condition
reassociated. -/
theorem factorizationIota_comp_toRelationAmbient_comp_relationContract :
    (factorizationIota R M n l ≫ factorizationToRelationAmbient R M n l) ≫
        relationContract R M n = 0 := by
  refine (comp_hom_sum Finset.univ (factorizationIota R M n l ≫
    factorizationToRelationAmbient R M n l)
    (fun i : Fin n => relationCoeff R M n i • relationElt R M n i)).trans ?_
  have hterm : ∀ i : Fin n,
      (factorizationIota R M n l ≫ factorizationToRelationAmbient R M n l) ≫
          (relationCoeff R M n i • relationElt R M n i) =
        (factorizationIota R M n l ≫ factorizationCoeff R M n l i) •
          ∑ k : Fin l, (factorizationIota R M n l ≫ factorizationMatrix R M n l k i) •
            (factorizationIota R M n l ≫ factorizationGen R M n l k) := by
    intro i
    refine (comp_hom_smul _ _ _).trans ?_
    refine congrArg₂ (fun (r : factorizationSheaf R M n l ⟶ ringSheaf R)
        (x : factorizationSheaf R M n l ⟶ moduleSheaf R M) => r • x) ?_ ?_
    · refine (Category.assoc _ _ _).trans ?_
      exact congrArg (fun m => factorizationIota R M n l ≫ m)
        (factorizationToRelationAmbient_comp_relationCoeff R M n l i)
    · refine (Category.assoc _ _ _).trans ?_
      refine Eq.trans (congrArg (fun m => factorizationIota R M n l ≫ m)
        (factorizationToRelationAmbient_comp_relationElt R M n l i)) ?_
      refine (comp_hom_sum Finset.univ (factorizationIota R M n l)
        (fun k : Fin l => factorizationMatrix R M n l k i •
          factorizationGen R M n l k)).trans ?_
      exact Finset.sum_congr rfl fun k _ => comp_hom_smul _ _ _
  refine Eq.trans (Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => hterm i) ?_
  refine Eq.trans (Stacks.SheafOfModules.sum_sum_mul_smul
    (hom_mul_comm hc)
    (fun k i => factorizationIota R M n l ≫ factorizationMatrix R M n l k i)
    (fun i => factorizationIota R M n l ≫ factorizationCoeff R M n l i)
    (fun k => factorizationIota R M n l ≫ factorizationGen R M n l k)).symm ?_
  refine Finset.sum_eq_zero fun k _ => ?_
  have hrow : ∑ i : Fin n, (factorizationIota R M n l ≫ factorizationMatrix R M n l k i) *
      (factorizationIota R M n l ≫ factorizationCoeff R M n l i) = 0 := by
    refine Eq.trans ?_ (factorizationIota_comp_factorizationRow R M n l k)
    refine Eq.trans ?_ (comp_hom_ringSum Finset.univ (factorizationIota R M n l)
      (fun i : Fin n => factorizationMatrix R M n l k i *
        factorizationCoeff R M n l i)).symm
    exact Finset.sum_congr rfl fun i _ => (comp_hom_mul _ _ _).symm
  rw [hrow, zero_smul]

include hc in
/-- **Reading a finite-free factorization as the relation it factors**, as a morphism of sheaves
of sets. -/
def factorizationToRelation : factorizationSheaf R M n l ⟶ relationSheaf R M n :=
  relationLift R M n (factorizationIota R M n l ≫ factorizationToRelationAmbient R M n l)
    (factorizationIota_comp_toRelationAmbient_comp_relationContract R M n l hc)

/-- The generalized element of `Rⁿ ⨯ Mⁿ` underlying the relation a factorization factors. -/
lemma factorizationToRelation_comp_relationIota :
    factorizationToRelation R M n l hc ≫ relationIota R M n =
      factorizationIota R M n l ≫ factorizationToRelationAmbient R M n l :=
  relationLift_comp_relationIota R M n _ _

end Stacks.Sheaves.RelationSheaf

/-! ## The inverse image of the factorization-to-relation morphism -/

namespace Stacks.Sheaves.ToposPullback

open Stacks.Sheaves.RelationSheaf

universe ww ww' vv uu vv' uu'

variable {C : Type uu} [Category.{vv} C] {D : Type uu'} [Category.{vv'} D]
  (J : GrothendieckTopology C) {K : GrothendieckTopology D}
  [J.HasSheafCompose (forget RingCat.{ww})] [K.HasSheafCompose (forget RingCat.{ww'})]
  [J.HasSheafCompose (forget AddCommGrpCat.{ww})]
  [K.HasSheafCompose (forget AddCommGrpCat.{ww'})]
  (Φ : Sheaf K (Type ww') ⥤ Sheaf J (Type ww)) [PreservesFiniteProducts Φ]
  (R : Sheaf K RingCat.{ww'}) (M : SheafOfModules.{ww'} R) (n l : ℕ)

/-- **The two ambient comparisons intertwine the two factorization-to-relation morphisms of
ambient products.**  Checked by `hom_ext_map_relationAmbient`: both sides have the same
coefficients and the same exhibited elements, by the two projection lemmas on each side. -/
theorem inv_comp_map_toRelationAmbient :
    (factorizationAmbientComparison J Φ R M n l).inv ≫
        Φ.map (factorizationToRelationAmbient R M n l) =
      factorizationToRelationAmbient (pullbackRingSheaf J Φ R)
          (pullbackModuleObj J Φ R M) n l ≫
        (relationAmbientComparison J Φ R M n).inv := by
  refine hom_ext_map_relationAmbient J Φ R M n (fun i => ?_) (fun i => ?_)
  · have hL : ((factorizationAmbientComparison J Φ R M n l).inv ≫
        Φ.map (factorizationToRelationAmbient R M n l)) ≫ Φ.map (relationCoeff R M n i) =
          factorizationCoeff (pullbackRingSheaf J Φ R)
            (pullbackModuleObj J Φ R M) n l i := by
      refine (Category.assoc _ _ _).trans ?_
      refine Eq.trans (congrArg
        (fun m => (factorizationAmbientComparison J Φ R M n l).inv ≫ m)
        ((Φ.map_comp _ _).symm.trans (congrArg Φ.map
          (factorizationToRelationAmbient_comp_relationCoeff R M n l i)))) ?_
      exact factorizationAmbientComparison_inv_comp_map_factorizationCoeff J Φ R M n l i
    have hR : (factorizationToRelationAmbient (pullbackRingSheaf J Φ R)
          (pullbackModuleObj J Φ R M) n l ≫
        (relationAmbientComparison J Φ R M n).inv) ≫ Φ.map (relationCoeff R M n i) =
          factorizationCoeff (pullbackRingSheaf J Φ R)
            (pullbackModuleObj J Φ R M) n l i := by
      refine (Category.assoc _ _ _).trans ?_
      refine Eq.trans (congrArg (fun m => factorizationToRelationAmbient
        (pullbackRingSheaf J Φ R) (pullbackModuleObj J Φ R M) n l ≫ m)
        (relationAmbientComparison_inv_comp_map_relationCoeff J Φ R M n i)) ?_
      exact factorizationToRelationAmbient_comp_relationCoeff
        (pullbackRingSheaf J Φ R) (pullbackModuleObj J Φ R M) n l i
    exact hL.trans hR.symm
  · have hL : ((factorizationAmbientComparison J Φ R M n l).inv ≫
        Φ.map (factorizationToRelationAmbient R M n l)) ≫ Φ.map (relationElt R M n i) =
          factorizationElt (pullbackRingSheaf J Φ R)
            (pullbackModuleObj J Φ R M) n l i := by
      refine (Category.assoc _ _ _).trans ?_
      refine Eq.trans (congrArg
        (fun m => (factorizationAmbientComparison J Φ R M n l).inv ≫ m)
        ((Φ.map_comp _ _).symm.trans (congrArg Φ.map
          (factorizationToRelationAmbient_comp_relationElt R M n l i)))) ?_
      exact inverseImageModuleElt_factorizationElt J Φ R M n l i
    have hR : (factorizationToRelationAmbient (pullbackRingSheaf J Φ R)
          (pullbackModuleObj J Φ R M) n l ≫
        (relationAmbientComparison J Φ R M n).inv) ≫ Φ.map (relationElt R M n i) =
          factorizationElt (pullbackRingSheaf J Φ R)
            (pullbackModuleObj J Φ R M) n l i := by
      refine (Category.assoc _ _ _).trans ?_
      refine Eq.trans (congrArg (fun m => factorizationToRelationAmbient
        (pullbackRingSheaf J Φ R) (pullbackModuleObj J Φ R M) n l ≫ m)
        (relationAmbientComparison_inv_comp_map_relationElt J Φ R M n i)) ?_
      exact factorizationToRelationAmbient_comp_relationElt
        (pullbackRingSheaf J Φ R) (pullbackModuleObj J Φ R M) n l i
    exact hL.trans hR.symm

/-- The `hom` form of `inv_comp_map_toRelationAmbient`. -/
theorem hom_comp_toRelationAmbient :
    (factorizationAmbientComparison J Φ R M n l).hom ≫
        factorizationToRelationAmbient (pullbackRingSheaf J Φ R)
          (pullbackModuleObj J Φ R M) n l =
      Φ.map (factorizationToRelationAmbient R M n l) ≫
        (relationAmbientComparison J Φ R M n).hom := by
  have h₂ : Φ.map (factorizationToRelationAmbient R M n l) =
      (factorizationAmbientComparison J Φ R M n l).hom ≫
        (factorizationToRelationAmbient (pullbackRingSheaf J Φ R)
            (pullbackModuleObj J Φ R M) n l ≫
          (relationAmbientComparison J Φ R M n).inv) :=
    (Iso.inv_comp_eq _).1 (inv_comp_map_toRelationAmbient J Φ R M n l)
  have hstep : ((factorizationAmbientComparison J Φ R M n l).hom ≫
        (factorizationToRelationAmbient (pullbackRingSheaf J Φ R)
            (pullbackModuleObj J Φ R M) n l ≫
          (relationAmbientComparison J Φ R M n).inv)) ≫
        (relationAmbientComparison J Φ R M n).hom =
      (factorizationAmbientComparison J Φ R M n l).hom ≫
        factorizationToRelationAmbient (pullbackRingSheaf J Φ R)
          (pullbackModuleObj J Φ R M) n l := by
    refine (Category.assoc _ _ _).trans ?_
    refine congrArg (fun m => (factorizationAmbientComparison J Φ R M n l).hom ≫ m) ?_
    refine (Category.assoc _ _ _).trans ?_
    refine Eq.trans (congrArg (fun m => factorizationToRelationAmbient
      (pullbackRingSheaf J Φ R) (pullbackModuleObj J Φ R M) n l ≫ m)
      (relationAmbientComparison J Φ R M n).inv_hom_id) ?_
    exact Category.comp_id _
  exact ((congrArg (fun m => m ≫ (relationAmbientComparison J Φ R M n).hom) h₂).trans
    hstep).symm

variable (hc : ∀ (Y : Dᵒᵖ) (x y : (sectionsFunctor K Y).obj (ringSheaf R)), x * y = y * x)

include hc in
/-- **The inverse image of the factorization-to-relation morphism is the
factorization-to-relation morphism of the inverse images.**  Both sides are checked after
composing with the monomorphism `relationIota` of the inverse-image data, where the identity
reduces to `hom_comp_toRelationAmbient`. -/
theorem factorizationSheafComparison_comp_factorizationToRelation
    [PreservesFiniteLimits Φ] :
    factorizationSheafComparison J Φ R M n l ≫
        factorizationToRelation (pullbackRingSheaf J Φ R) (pullbackModuleObj J Φ R M) n l
          (pullback_sections_mul_comm J Φ hc) =
      Φ.map (factorizationToRelation R M n l hc) ≫
        (relationSheafIsoPullback J Φ R M n).inv := by
  refine (cancel_mono (relationIota (pullbackRingSheaf J Φ R)
    (pullbackModuleObj J Φ R M) n)).1 ?_
  have hL : (factorizationSheafComparison J Φ R M n l ≫
        factorizationToRelation (pullbackRingSheaf J Φ R) (pullbackModuleObj J Φ R M) n l
          (pullback_sections_mul_comm J Φ hc)) ≫
        relationIota (pullbackRingSheaf J Φ R) (pullbackModuleObj J Φ R M) n =
      Φ.map (factorizationIota R M n l) ≫
        ((factorizationAmbientComparison J Φ R M n l).hom ≫
          factorizationToRelationAmbient (pullbackRingSheaf J Φ R)
            (pullbackModuleObj J Φ R M) n l) := by
    refine (Category.assoc _ _ _).trans ?_
    refine Eq.trans (congrArg (fun m => factorizationSheafComparison J Φ R M n l ≫ m)
      (factorizationToRelation_comp_relationIota (pullbackRingSheaf J Φ R)
        (pullbackModuleObj J Φ R M) n l (pullback_sections_mul_comm J Φ hc))) ?_
    refine (Category.assoc _ _ _).symm.trans ?_
    refine Eq.trans (congrArg (fun m => m ≫ factorizationToRelationAmbient
      (pullbackRingSheaf J Φ R) (pullbackModuleObj J Φ R M) n l)
      (factorizationSheafComparison_comp_factorizationIota J Φ R M n l)) ?_
    exact Category.assoc _ _ _
  have hR : (Φ.map (factorizationToRelation R M n l hc) ≫
        (relationSheafIsoPullback J Φ R M n).inv) ≫
        relationIota (pullbackRingSheaf J Φ R) (pullbackModuleObj J Φ R M) n =
      Φ.map (factorizationIota R M n l) ≫
        (Φ.map (factorizationToRelationAmbient R M n l) ≫
          (relationAmbientComparison J Φ R M n).hom) := by
    refine (Category.assoc _ _ _).trans ?_
    refine Eq.trans (congrArg (fun m => Φ.map (factorizationToRelation R M n l hc) ≫ m)
      (relationSheafIsoPullback_inv_comp_relationIota J Φ R M n)) ?_
    refine (Category.assoc _ _ _).symm.trans ?_
    refine Eq.trans (congrArg (fun m => m ≫ (relationAmbientComparison J Φ R M n).hom)
      ((Φ.map_comp _ _).symm.trans (congrArg Φ.map
        (factorizationToRelation_comp_relationIota R M n l hc)))) ?_
    refine Eq.trans (congrArg (fun m => m ≫ (relationAmbientComparison J Φ R M n).hom)
      (Φ.map_comp _ _)) ?_
    exact Category.assoc _ _ _
  refine hL.trans (Eq.trans ?_ hR.symm)
  exact congrArg (fun m => Φ.map (factorizationIota R M n l) ≫ m)
    (hom_comp_toRelationAmbient J Φ R M n l)

end Stacks.Sheaves.ToposPullback

end
