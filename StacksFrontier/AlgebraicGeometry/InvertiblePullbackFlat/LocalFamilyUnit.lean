module

public import StacksFrontier.AlgebraicGeometry.InvertiblePullbackFlat.LocalFamilyAssembly
public import StacksFrontier.AlgebraicGeometry.InvertiblePullbackFlat.MultiplierUnitRatio

/-!
# The uniqueness sentence of Tag 0BD7 for a family built on arbitrary opens

The penultimate paragraph of [Stacks, Tag 0BD7] says of its multipliers that they are *unique up
to a unit of `𝒪_{Y, y}`*. `Stacks.InvertiblePullback.exists_isUnit_mul_germ_eq_of_`
`isPullMeromorphicFamily` proves that for a family whose sections live on the preimages
`φ^{-1}(A i)`. The family the paragraph actually produces does not: its sections live on opens
`V i` of `X` cut out by where `φ^*(g_i) s` happens to be regular, which is the shape of
`Stacks.InvertiblePullback.IsPullMeromorphicFamilyOn`.

Nothing in the argument needs the preimage. It is run on the intersection of the two generating
loci, an open contained in `V i ⊓ V j`, and the preimage enters only as an upper bound for that
intersection. This file carries the two steps over.

## Main results

* `Stacks.InvertiblePullback.restrict_pullback_eq_mul_of_isPullMeromorphicFamilyOn`: a relation
  between two members of the family on a common open of `V i` and `V j` is a relation between
  the pullbacks of their multipliers there.
* `Stacks.InvertiblePullback.exists_isUnit_mul_germ_eq_of_isPullMeromorphicFamilyOn`: hence the
  source's sentence — at a point where both members generate, the germs of the two multipliers
  at its image differ by a unit of `𝒪_{Y, φ(x)}`.

## Implementation notes

The tag is **withheld**: the family is a hypothesis here, and it is exhibited in
`StacksFrontier/AlgebraicGeometry/InvertiblePullbackFlat/LocalFamilyCover.lean`.

What these two results do *not* give is the hypothesis `hagree` of
`StacksFrontier/AlgebraicGeometry/InvertiblePullbackFlat/ChartSaturation.lean`. The route from a
unit germ to `hagree`,
`Stacks.InvertiblePullback.forall_mem_generatingLocus_iff_of_exists_base_germ_unit`, wants the
relation between the two sections on a whole preimage `φ^{-1}(A) ≤ V i ⊓ V j`, and a `V i` cut
out by regularity need contain no preimage at all. For a family on arbitrary opens `hagree` is
in fact false — two members with one multiplier, on nested opens, have nested loci, which differ
along a fibre leaving the smaller open.

What rules that counterexample out is the extra clause
`Stacks.InvertiblePullback.IsMaximalPullMeromorphicFamilyOn`, that each `V i` is the *largest*
open of `φ^{-1}(A i)` on which the product is regular: nested opens with one multiplier are then
equal. `hagree` is derived from it in
`StacksFrontier/AlgebraicGeometry/InvertiblePullbackFlat/LocalFamilyAgreement.lean`, and the germ
relation this file produces is the input to that derivation.

## References

* [Stacks Project, Tag 0BD7](https://stacks.math.columbia.edu/tag/0BD7)
* [Stacks Project, Tag 02OT](https://stacks.math.columbia.edu/tag/02OT)
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
open Stacks.Meromorphic

universe u

namespace Stacks.InvertiblePullback

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f]
    (L : _root_.SheafOfModules.{u} (_root_.structureSheafRing X.toRingedSpace))
    (s : MeromorphicSection X.sheaf L)
    {ι : Type*} {A : ι → Y.Opens} {V : ι → Opens X.toRingedSpace.carrier}
    (hVA : ∀ i, (V i : X.Opens) ≤ (f ⁻¹ᵁ A i : X.Opens))
    (g : ∀ i, (totalQuotientSheafAsModule Y).val.obj (op (A i)))
    (t : ∀ i, L.val.obj (op (V i)))

include hVA in
/-- **A relation between the sections is a relation between the multipliers.** As
`Stacks.InvertiblePullback.restrict_pullback_eq_mul_of_isPullMeromorphicFamily`, for a family
whose members live on arbitrary opens `V i` of the preimages. -/
theorem restrict_pullback_eq_mul_of_isPullMeromorphicFamilyOn
    (hs : IsRegularMeromorphicSection X.sheaf L s)
    (ht : IsPullMeromorphicFamilyOn f L s hVA g t)
    (i j : ι) {W : Opens X.toRingedSpace.carrier} (hWi : W ≤ V i) (hWj : W ≤ V j)
    (c : X.presheaf.obj (op W))
    (hc : L.val.restrictₛₗ (homOfLE hWi).op (t i)
      = c • L.val.restrictₛₗ (homOfLE hWj).op (t j)) :
    ((Stacks.Sheaves.Differentials.ringSheaf (J := Opens.grothendieckTopology X)
        X.totalQuotientSheaf).obj.map (homOfLE (hWi.trans (hVA i))).op).hom
          (((Scheme.ringSheafPullbackOfFlat f).hom.app (op (A i))).hom (g i))
      = ((toTotalQuotientRingSheaf X).hom.app (op W)).hom c *
        ((Stacks.Sheaves.Differentials.ringSheaf (J := Opens.grothendieckTopology X)
          X.totalQuotientSheaf).obj.map (homOfLE (hWj.trans (hVA j))).op).hom
            (((Scheme.ringSheafPullbackOfFlat f).hom.app (op (A j))).hom (g j)) := by
  have key : ∀ (k : ι) (hWk : W ≤ V k),
      (((meromorphicSectionSheaf X.sheaf L).unitHomEquiv.symm s).val.app (op W)).hom
          (((Stacks.Sheaves.Differentials.ringSheaf (J := Opens.grothendieckTopology X)
            X.totalQuotientSheaf).obj.map (homOfLE (hWk.trans (hVA k))).op).hom
              (((Scheme.ringSheafPullbackOfFlat f).hom.app (op (A k))).hom (g k)))
        = (((toMeromorphicSectionSheafAsModule X L).val.app (op W)).hom
            (L.val.restrictₛₗ (homOfLE hWk).op (t k)) :
              ↑((meromorphicSectionSheaf X.sheaf L).val.obj (op W))) := by
    intro k hWk
    have hsplit : (meromorphicSectionSheaf X.sheaf L).val.restrictₛₗ
          (homOfLE (hWk.trans (hVA k))).op
          ((pullbackMeromorphicMul f L s).val.app (op (A k)) (g k))
        = (meromorphicSectionSheafAsModule X L).val.restrictₛₗ (homOfLE hWk).op
            ((meromorphicSectionSheafAsModule X L).val.restrictₛₗ (homOfLE (hVA k)).op
              ((pullbackMeromorphicMul f L s).val.app (op (A k)) (g k))) :=
      (meromorphicSectionSheaf X.sheaf L).val.map_comp_apply
        (homOfLE (hVA k)).op (homOfLE hWk).op _
    rw [← restrict_pullbackMeromorphicMul_val_app f L s (A k) (hWk.trans (hVA k)) (g k), hsplit,
      ht k]
    exact (PresheafOfModules.naturality_apply (toMeromorphicSectionSheafAsModule X L).val
      (homOfLE hWk).op (t k)).symm
  have hlin : ∀ (y : ↑(L.val.obj (op W)))
      (v : ↑((meromorphicSectionSheaf X.sheaf L).val.obj (op W))),
      ((toMeromorphicSectionSheafAsModule X L).val.app (op W)).hom y = v →
      ((toMeromorphicSectionSheafAsModule X L).val.app (op W)).hom (c • y)
        = ((toTotalQuotientRingSheaf X).hom.app (op W)).hom c • v := by
    rintro y v rfl
    exact LinearMap.map_smul ((toMeromorphicSectionSheafAsModule X L).val.app (op W)).hom c y
  have hmul : ∀ (z : ↑((Stacks.Sheaves.Differentials.ringSheaf
        (J := Opens.grothendieckTopology X) X.totalQuotientSheaf).obj.obj (op W)))
      (v : ↑((meromorphicSectionSheaf X.sheaf L).val.obj (op W))),
      (((meromorphicSectionSheaf X.sheaf L).unitHomEquiv.symm s).val.app (op W)).hom z = v →
      (((meromorphicSectionSheaf X.sheaf L).unitHomEquiv.symm s).val.app (op W)).hom
          (((toTotalQuotientRingSheaf X).hom.app (op W)).hom c * z)
        = ((toTotalQuotientRingSheaf X).hom.app (op W)).hom c • v := by
    rintro z v rfl
    rw [← smul_eq_mul]
    exact map_smul _ _ _
  have hstep := hlin (L.val.restrictₛₗ (homOfLE hWj).op (t j)) _ rfl
  exact CategoryTheory.SheafOfModules.app_injective_of_mono hs (op W)
    (((key i hWi).trans (congrArg (fun y =>
        ((toMeromorphicSectionSheafAsModule X L).val.app (op W)).hom y) hc)).trans
      (hstep.trans (hmul _ _ (key j hWj)).symm))

include hVA in
/-- **The uniqueness clause of [Stacks, Tag 0BD7] on the local ring of the base.** As
`Stacks.InvertiblePullback.exists_isUnit_mul_germ_eq_of_isPullMeromorphicFamily`, for a family
whose members live on arbitrary opens `V i` of the preimages. -/
theorem exists_isUnit_mul_germ_eq_of_isPullMeromorphicFamilyOn
    [IsIntegral X] [IsIntegral Y]
    (hs : IsRegularMeromorphicSection X.sheaf L s)
    (ht : IsPullMeromorphicFamilyOn f L s hVA g t)
    (i j : ι) {W : Opens X.toRingedSpace.carrier} {x : X} (hxW : x ∈ W)
    (hWi : W ≤ V i) (hWj : W ≤ V j)
    (c : X.presheaf.obj (op W)) (hcu : IsUnit c)
    (hc : L.val.restrictₛₗ (homOfLE hWi).op (t i)
      = c • L.val.restrictₛₗ (homOfLE hWj).op (t j))
    (hxi : f.base x ∈ A i) (hxj : f.base x ∈ A j) :
    ∃ v : ↑(Y.presheaf.stalk (f.base x)), IsUnit v ∧
      Y.totalQuotientSheaf.presheaf.germ (A i) (f.base x) hxi (g i)
        = toTotalQuotientStalk Y (f.base x) v *
          Y.totalQuotientSheaf.presheaf.germ (A j) (f.base x) hxj (g j) := by
  have hpull : ∀ (k : ι) (hWk : W ≤ (f ⁻¹ᵁ A k : X.Opens)) (hxk : f.base x ∈ A k),
      X.totalQuotientSheaf.presheaf.germ W x hxW
          (((Stacks.Sheaves.Differentials.ringSheaf (J := Opens.grothendieckTopology X)
            X.totalQuotientSheaf).obj.map (homOfLE hWk).op).hom
              (((Scheme.ringSheafPullbackOfFlat f).hom.app (op (A k))).hom (g k)))
        = totalQuotientStalkMap f x
            (Y.totalQuotientSheaf.presheaf.germ (A k) (f.base x) hxk (g k)) := by
    intro k hWk hxk
    rw [totalQuotientStalkMap_germ f x (A k) hxk (g k)]
    exact TopCat.Presheaf.germ_res_apply X.totalQuotientSheaf.presheaf (homOfLE hWk) x hxW _
  have hkappa : X.totalQuotientSheaf.presheaf.germ W x hxW
        (((toTotalQuotientRingSheaf X).hom.app (op W)).hom c)
      = toTotalQuotientStalk X x (X.presheaf.germ W x hxW c) :=
    (TopCat.Presheaf.stalkFunctor_map_germ_apply W x hxW X.toTotalQuotientSheaf.hom c).symm
  have hgerm : totalQuotientStalkMap f x
        (Y.totalQuotientSheaf.presheaf.germ (A i) (f.base x) hxi (g i))
      = toTotalQuotientStalk X x (X.presheaf.germ W x hxW c) *
        totalQuotientStalkMap f x
          (Y.totalQuotientSheaf.presheaf.germ (A j) (f.base x) hxj (g j)) := by
    rw [← hpull i (hWi.trans (hVA i)) hxi, ← hpull j (hWj.trans (hVA j)) hxj, ← hkappa]
    exact (congrArg (ConcreteCategory.hom (X.totalQuotientSheaf.presheaf.germ W x hxW))
        (restrict_pullback_eq_mul_of_isPullMeromorphicFamilyOn f L s hVA g t hs ht
          i j hWi hWj c hc)).trans
      (map_mul (ConcreteCategory.hom (X.totalQuotientSheaf.presheaf.germ W x hxW)) _ _)
  obtain ⟨p, q, d, hd, hpd, hqd⟩ := exists_mul_toTotalQuotientStalk_eq₂ Y (f.base x)
    (Y.totalQuotientSheaf.presheaf.germ (A i) (f.base x) hxi (g i))
    (Y.totalQuotientSheaf.presheaf.germ (A j) (f.base x) hxj (g j))
  have hK : ∀ (a : ↑(Y.totalQuotientSheaf.presheaf.stalk (f.base x)))
      (e r : ↑(Y.presheaf.stalk (f.base x))),
      a * toTotalQuotientStalk Y (f.base x) e = toTotalQuotientStalk Y (f.base x) r →
      totalQuotientStalkMap f x a * toTotalQuotientStalk X x ((f.stalkMap x).hom e)
        = toTotalQuotientStalk X x ((f.stalkMap x).hom r) := by
    intro a e r h
    rw [← totalQuotientStalkMap_toTotalQuotientStalk f x e,
      ← totalQuotientStalkMap_toTotalQuotientStalk f x r,
      ← map_mul (totalQuotientStalkMap f x), h]
  have hPi := hK _ d p hpd
  have hPj := hK _ d q hqd
  have hnum : toTotalQuotientStalk X x ((f.stalkMap x).hom p)
      = toTotalQuotientStalk X x
          (ConcreteCategory.hom (X.presheaf.germ W x hxW) c * (f.stalkMap x).hom q) := by
    rw [map_mul (toTotalQuotientStalk X x), ← hPj, ← hPi, hgerm, mul_assoc]
  obtain ⟨v, hv, hvpq⟩ := exists_isUnit_mul_eq_of_isUnit_stalkMap f x p q
    (hcu.map (ConcreteCategory.hom (X.presheaf.germ W x hxW)))
    (toTotalQuotientStalk_injective X x hnum)
  exact ⟨v, hv, eq_mul_of_numerator_eq_mul Y (f.base x) hd hpd hqd hvpq⟩

end Stacks.InvertiblePullback

end
