module

public import StacksFrontier.CategoryTheory.Sites.CechComplexAlternatingHomotopy
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.FirstCocycles

/-!
# The explicit Čech cochain complex is the Čech complex

Let `U : ι → C` be a family of objects and `P` an abelian presheaf. The explicit Čech cochain
complex `cechCochainComplex P U` of
`StacksFrontier/CategoryTheory/Sites/CechComplexAlternatingHomotopy.lean`, built from the groups
`CechCochain P U n` of functions on tuples, is the model in which [Stacks, Tag 01FJ],
[Stacks, Tag 01FK] and [Stacks, Tag 01FM] are proved there. It is isomorphic to
`CategoryTheory.cechComplexFunctor`, the Čech complex of the Čech nerve of `∐ i, U i ⟶ ⊤_ C`,
whose degreewise description is `StacksFrontier/CategoryTheory/Sites/CechComplex.lean`.
Consequently [Stacks, Tag 01FM] holds for `cechComplexFunctor`.

All names are in the namespace `Stacks.CategoryTheory.CechComplex.Alternating`; `π`, `lift`,
`isLimitFan` and `d_comp_π` are in `Stacks.CategoryTheory.CechComplex`.

## Main definitions

* `toCechCochain` and `ofCechCochain`: the two comparison maps in a single degree; the second is
  `lift` of the evaluation maps, the first reads off the components with `π`.
* `cechCochainXIso`: the two comparison maps are mutually inverse.
* `cechCochainComplexIso`: the explicit Čech cochain complex of a family is isomorphic to the
  Čech complex of that family.
* `cechAltHomotopyEquivCechComplex`, `cechOrdHomotopyEquivCechComplex`: [Stacks, Tag 01FM] in
  the `cechComplexFunctor` model: the alternating and the ordered Čech complexes of a family of
  subterminal objects are homotopy equivalent to `cechComplexFunctor`.
* `cechCochainComplexOrdHomologyIsoCechComplex`: the ordered Čech complex of a family of
  subterminal objects has the cohomology of `cechComplexFunctor` in every degree.

## Main results

* `cechDiff_comp_ofCechCochain`: the comparison commutes with the differentials.

## Implementation notes

The coefficient presheaf takes values in `AddCommGrpCat.{max w w'}` rather than
`AddCommGrpCat.{w'}`. The complexes of the alternating theory live in `AddCommGrpCat.{max w w'}`,
a cochain being a function on a `Type w` of tuples, while `cechComplexFunctor` needs
`Limits.HasProducts.{w}` of the coefficient category, which `AddCommGrpCat.{w'}` has only for
`w ≤ w'`. Taking `w' := max w w'` recovers the general case.

## References

* [Stacks Project, Tag 01FG](https://stacks.math.columbia.edu/tag/01FG)
* [Stacks Project, Tag 01FK](https://stacks.math.columbia.edu/tag/01FK)
* [Stacks Project, Tag 01FM](https://stacks.math.columbia.edu/tag/01FM)
-/
@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe w w' v u

noncomputable section

namespace Stacks.CategoryTheory.CechComplex.Alternating

variable {C : Type u} [Category.{v} C] [HasFiniteProducts C] {ι : Type w} [LinearOrder ι]
  (P : Cᵒᵖ ⥤ AddCommGrpCat.{max w w'}) (U : ι → C)

/-! ### The comparison in a single degree -/

/-- **Reading a degree-`n` term of the Čech complex as a cochain**: its component at the tuple
`t` is the projection `π` onto the factor over `inter U t`. -/
def toCechCochain (n : ℕ) :
    ((cechComplexFunctor U).obj P).X n ⟶ AddCommGrpCat.of (Alternating.CechCochain P U n) :=
  AddCommGrpCat.ofHom
    { toFun := fun s t => (π U P n t).hom s
      map_zero' := by funext t; exact (π U P n t).hom.map_zero
      map_add' := fun a b => by funext t; exact (π U P n t).hom.map_add a b }

/-- **Reading a cochain as a degree-`n` term of the Čech complex**: the universal map into the
product whose component at `t` is evaluation at `t`. -/
def ofCechCochain (n : ℕ) :
    AddCommGrpCat.of (Alternating.CechCochain P U n) ⟶ ((cechComplexFunctor U).obj P).X n :=
  lift U P fun t => AddCommGrpCat.ofHom (Pi.evalAddMonoidHom _ t)

omit [LinearOrder ι] in
/-- The projection at the tuple `t` of the image of a cochain is evaluation at `t`. -/
@[reassoc]
theorem ofCechCochain_comp_π (n : ℕ) (t : Fin (n + 1) → ι) :
    ofCechCochain P U n ≫ π U P n t = AddCommGrpCat.ofHom (Pi.evalAddMonoidHom _ t) :=
  lift_comp_π U P _ t

omit [LinearOrder ι] in
/-- The component of `ofCechCochain P U n s` at the tuple `t` is `s t`. -/
theorem π_ofCechCochain (n : ℕ) (t : Fin (n + 1) → ι) (s : Alternating.CechCochain P U n) :
    (π U P n t).hom ((ofCechCochain P U n).hom s) = s t := by
  rw [← CategoryTheory.comp_apply, ofCechCochain_comp_π]
  rfl

omit [LinearOrder ι] in
/-- Reading a cochain into the Čech complex and back off it is the identity. -/
theorem ofCechCochain_comp_toCechCochain (n : ℕ) :
    ofCechCochain P U n ≫ toCechCochain P U n = 𝟙 _ :=
  AddCommGrpCat.hom_ext <| AddMonoidHom.ext fun s => funext fun t => π_ofCechCochain P U n t s

omit [LinearOrder ι] in
/-- Reading a degree-`n` term off as a cochain and back into the Čech complex is the identity. -/
theorem toCechCochain_comp_ofCechCochain (n : ℕ) :
    toCechCochain P U n ≫ ofCechCochain P U n = 𝟙 _ := by
  refine hom_ext U P fun t => ?_
  rw [Category.assoc, ofCechCochain_comp_π, Category.id_comp]
  rfl

/-- **The degree-`n` term of the Čech complex of a family is the group of Čech `n`-cochains.**
This is `isLimitFan` read as an isomorphism onto the group of functions on tuples. -/
def cechCochainXIso (n : ℕ) :
    AddCommGrpCat.of (Alternating.CechCochain P U n) ≅ ((cechComplexFunctor U).obj P).X n where
  hom := ofCechCochain P U n
  inv := toCechCochain P U n
  hom_inv_id := ofCechCochain_comp_toCechCochain P U n
  inv_hom_id := toCechCochain_comp_ofCechCochain P U n

/-! ### The comparison commutes with the differentials -/

omit [LinearOrder ι] in
/-- **The comparison commutes with the differentials**: `ofCechCochain` carries the differential
`cechDiff` of the explicit cochain complex to the differential of the Čech complex. -/
theorem cechDiff_comp_ofCechCochain (n : ℕ) :
    AddCommGrpCat.ofHom (Alternating.cechDiff P U n) ≫ ofCechCochain P U (n + 1) =
      ofCechCochain P U n ≫ ((cechComplexFunctor U).obj P).d n (n + 1) := by
  refine hom_ext U P fun t => ?_
  rw [Category.assoc, ofCechCochain_comp_π, Category.assoc, d_comp_π,
    Preadditive.comp_sum]
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro s
  rw [Stacks.CechSite.hom_sum_apply Finset.univ
    (fun j : Fin (n + 2) => ofCechCochain P U n ≫
      ((-1 : ℤ) ^ (j : ℕ) • (π U P n (t ∘ j.succAbove) ≫
        P.map (interMap U t j.succAbove).op)))]
  change ∑ j : Fin (n + 2), (-1 : ℤ) ^ (j : ℕ) •
      tres P U (Fin.succAbove j) t (s (t ∘ Fin.succAbove j)) = _
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Preadditive.comp_zsmul, ← Category.assoc, ofCechCochain_comp_π]
  rfl

/-- **The explicit Čech cochain complex of a family is isomorphic to the Čech complex of that
family** `CategoryTheory.cechComplexFunctor`, degreewise by `cechCochainXIso`. The explicit
complex is the model in which [Stacks, Tag 01FJ], [Stacks, Tag 01FK] and [Stacks, Tag 01FM] are
proved. -/
def cechCochainComplexIso : cechCochainComplex P U ≅ (cechComplexFunctor U).obj P :=
  HomologicalComplex.Hom.isoOfComponents (fun p => cechCochainXIso P U p)
    (fun i j hij => by
      obtain rfl : j = i + 1 := hij.symm
      rw [cechCochainComplex_d]
      exact (cechDiff_comp_ofCechCochain P U i).symm)

/-! ### [Stacks, Tag 01FM] in the `cechComplexFunctor` model -/

/-- **[Stacks, Tag 01FM] in the `cechComplexFunctor` model.** The alternating Čech cochain
complex of a family of subterminal objects is homotopy equivalent to the Čech complex of the
family. -/
@[stacks 01FM "in the cechComplexFunctor model"]
def cechAltHomotopyEquivCechComplex (hU : ∀ i, IsSubterminal (U i)) :
    HomotopyEquiv (cechCochainComplexAlt P U hU) ((cechComplexFunctor U).obj P) :=
  (cechAltInclusionHomotopyEquiv P U hU).trans
    (HomotopyEquiv.ofIso (cechCochainComplexIso P U))

/-- **The ordered Čech complex of a family of subterminal objects is homotopy equivalent to the
Čech complex of the family.** [Stacks, Tag 01FK] (2) and [Stacks, Tag 01FM], in the
`cechComplexFunctor` model. -/
def cechOrdHomotopyEquivCechComplex (hU : ∀ i, IsSubterminal (U i)) :
    HomotopyEquiv (cechCochainComplexOrd P U) ((cechComplexFunctor U).obj P) :=
  (cechOrdHomotopyEquiv P U hU).trans (HomotopyEquiv.ofIso (cechCochainComplexIso P U))

/-- **The ordered Čech complex of a family of subterminal objects has the cohomology of the Čech
complex of the family, in every degree.** This is the step that the proof of
[Stacks, Tag 07MN] leaves as "insert future reference here". -/
def cechCochainComplexOrdHomologyIsoCechComplex (hU : ∀ i, IsSubterminal (U i)) (j : ℕ)
    [(cechCochainComplexOrd P U).HasHomology j]
    [((cechComplexFunctor U).obj P).HasHomology j] :
    (cechCochainComplexOrd P U).homology j ≅ ((cechComplexFunctor U).obj P).homology j :=
  (cechOrdHomotopyEquivCechComplex P U hU).toHomologyIso j

end Stacks.CategoryTheory.CechComplex.Alternating

end

end
