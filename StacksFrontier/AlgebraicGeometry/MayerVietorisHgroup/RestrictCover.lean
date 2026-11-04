module

public import StacksFrontier.AlgebraicGeometry.MayerVietorisHgroup.AmbientOpen
public import StacksFrontier.Algebra.Homology.DerivedDeltaOfShortComplexHom

/-!
# Restricting a Mayer--Vietoris cover to a smaller ambient open

Let `X` be a topological space, `O` a sheaf of rings on `X`, and let `U ⊔ V = W` and
`U' ⊔ V' = W'` be two pairs of opens covering their ambient open, the second contained in the
first: `W' ≤ W`, `U' ≤ U` and `V' ≤ V`. The Mayer--Vietoris sequence of
`StacksFrontier/AlgebraicGeometry/MayerVietorisHgroup/AmbientOpen.lean` exists for both, and the
restriction maps relate them. This file proves that the restriction maps commute with the
**connecting** morphisms:

`Hⁿ(U ⊓ V,F) ⟶ Hⁿ(U' ⊓ V',F) ⟶ Hⁿ⁺¹(W',F)  =  Hⁿ(U ⊓ V,F) ⟶ Hⁿ⁺¹(W,F) ⟶ Hⁿ⁺¹(W',F)`.

For the two non-connecting maps the corresponding statement is immediate, since those maps are
themselves restriction maps (`Stacks.Cohomology.AmbientMayerVietoris.ambientFirst_eq` and
`Stacks.Cohomology.AbsoluteMayerVietoris.mvSecond_eq`) and restriction is transitive. The
connecting morphisms of the two sequences are built from two *different* short complexes of
sections functors, and the module docstring of `AmbientOpen.lean` records that nothing there
compares them; this file supplies the comparison.

## Main definitions

* `Stacks.Cohomology.AmbientMayerVietoris.restrictCoverMiddle`: the middle component of the
  morphism of short complexes, the pair of the restrictions `Γ(U,-) ⟶ Γ(U',-)` and
  `Γ(V,-) ⟶ Γ(V',-)`.

## Main results

* `Stacks.Cohomology.AmbientMayerVietoris.ambientDelta_restrict` and
  `Stacks.Cohomology.AmbientMayerVietoris.ambientDelta_restrict_apply`: **the connecting morphism
  commutes with restriction of the cover**, as natural transformations and on classes.
* `Stacks.Cohomology.AmbientMayerVietoris.ambientDelta_restrict_inf`: the special case of the
  cover `U ⊓ T`, `V ⊓ T` of `W ⊓ T` cut out by a third open `T`, which is the shape in which the
  Mayer--Vietoris induction of [Stacks, Tag 09MR] uses it, with `T` the nonvanishing open of a
  section of an invertible module.

## Implementation notes

The whole content is that the three restriction maps form a morphism of the two Mayer--Vietoris
short complexes of sections functors, after which
`CategoryTheory.rightDerivedDelta_comp_of_hom` applies. Both squares of that morphism reduce to
transitivity of restriction, `Stacks.Cohomology.AmbientMayerVietoris.secRestrict_comp`: the two
composites it produces are restrictions along two proofs of one and the same inequality of opens,
hence the same term.

The derived map of a restriction natural transformation **is** `Hrestrict` by definition, so no
identification of the outer maps is needed.

## References

* [Stacks Project, Tag 01EB](https://stacks.math.columbia.edu/tag/01EB)
* [Stacks Project, Tag 09MR](https://stacks.math.columbia.edu/tag/09MR)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.Cohomology.RestrictionCover

universe u

namespace Stacks.Cohomology.AmbientMayerVietoris

attribute [local instance 2000] CategoryTheory.Abelian.hasBinaryBiproducts
attribute [local instance]
  CategoryTheory.Limits.preservesBinaryBiproducts_of_preservesBinaryProducts

variable {X : TopCat.{u}} (O : Sheaf (Opens.grothendieckTopology X) RingCat.{u})

section ShortComplexHom

variable (W U V W' U' V' : Opens X) (hU : U ≤ W) (hV : V ≤ W) (hU' : U' ≤ W') (hV' : V' ≤ W')
  (hWW' : W' ≤ W) (hUU' : U' ≤ U) (hVV' : V' ≤ V)

/-- **The middle component of the morphism of Mayer--Vietoris short complexes**, the pair of the
restrictions of the two members of the cover. -/
def restrictCoverMiddle :
    secF O U ⊞ secF O V ⟶ secF O U' ⊞ secF O V' :=
  biprod.map (secRestrict O hUU') (secRestrict O hVV')

include hUU' hVV' in
/-- **The square of the morphism of short complexes at the first map**: restricting from `W` to
the cover and then to the smaller cover is restricting from `W` to `W'` and then to the smaller
cover. -/
theorem ambientToCover_comp_restrictCoverMiddle :
    ambientToCover O W U V hU hV ≫ restrictCoverMiddle O U V U' V' hUU' hVV' =
      secRestrict O hWW' ≫ ambientToCover O W' U' V' hU' hV' := by
  refine biprod.hom_ext _ _ ?_ ?_ <;>
    simp only [ambientToCover, restrictCoverMiddle, Category.assoc, biprod.map_fst,
      biprod.map_snd, biprod.lift_fst_assoc, biprod.lift_snd_assoc, biprod.lift_fst,
      biprod.lift_snd, secRestrict_comp]

include hUU' hVV' in
/-- **The square of the morphism of short complexes at the second map**: the difference of the
two restrictions to the intersection is compatible with restricting the cover. -/
theorem restrictCoverMiddle_comp_ambientToIntersection
    (hI : U' ⊓ V' ≤ U ⊓ V) :
    ambientToIntersection O U V ≫ secRestrict O hI =
      restrictCoverMiddle O U V U' V' hUU' hVV' ≫ ambientToIntersection O U' V' := by
  refine biprod.hom_ext' _ _ ?_ ?_ <;>
    simp only [ambientToIntersection, restrictCoverMiddle, biprod.inl_desc_assoc,
      biprod.inr_desc_assoc, biprod.inl_map_assoc, biprod.inr_map_assoc, biprod.inl_desc,
      biprod.inr_desc, Preadditive.neg_comp,
      Preadditive.comp_neg, secRestrict_comp]

end ShortComplexHom

section Hgroup

variable [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [EnoughInjectives (SheafOfModules.{u} O)]

/-- **Restriction on cohomology is transitive**, as a natural transformation: it is the right
derivation of the transitivity of restriction on sections. -/
theorem hrestrictNT_comp {T U W : Opens X} (h₁ : U ≤ W) (h₂ : T ≤ U) (n : ℕ) :
    HrestrictNT O h₁ n ≫ HrestrictNT O h₂ n = HrestrictNT O (h₂.trans h₁) n := by
  unfold HrestrictNT
  rw [← NatTrans.rightDerived_comp, secRestrict_comp]

/-- **Restriction on cohomology is transitive**, on the group of a single sheaf. -/
theorem hrestrict_comp {T U W : Opens X} (h₁ : U ≤ W) (h₂ : T ≤ U) (n : ℕ)
    (F : SheafOfModules.{u} O) :
    Hrestrict O h₁ n F ≫ Hrestrict O h₂ n F = Hrestrict O (h₂.trans h₁) n F := by
  unfold Hrestrict
  rw [← NatTrans.comp_app, hrestrictNT_comp]

/-- **Restriction on cohomology is transitive**, read on a class.  The composite inequality is an
explicit argument: restriction depends only on the two opens, so any proof of it will do. -/
theorem hrestrict_comp_apply {T U W : Opens X} (h₁ : U ≤ W) (h₂ : T ≤ U) (h : T ≤ W) (n : ℕ)
    (F : SheafOfModules.{u} O) (x : (Hgroup O W n F : Type u)) :
    Hrestrict O h₂ n F (Hrestrict O h₁ n F x) = Hrestrict O h n F x := by
  have h' := congrArg (fun m : Hgroup O W n F ⟶ Hgroup O T n F => m x)
    (hrestrict_comp O h₁ h₂ n F)
  simpa [AddCommGrpCat.comp_apply] using h'

/-- **A class vanishing on an open vanishes on every smaller open.** -/
theorem hrestrict_eq_zero_of_restrict_eq_zero {T U W : Opens X} (h₁ : U ≤ W) (h₂ : T ≤ U)
    (h : T ≤ W) (n : ℕ) (F : SheafOfModules.{u} O) {x : (Hgroup O W n F : Type u)}
    (hx : Hrestrict O h₁ n F x = 0) : Hrestrict O h n F x = 0 := by
  rw [← hrestrict_comp_apply O h₁ h₂ h n F x, hx, map_zero]

variable (W U V W' U' V' : Opens X) (hU : U ≤ W) (hV : V ≤ W) (hU' : U' ≤ W') (hV' : V' ≤ W')
  (hUV : U ⊔ V = W) (hU'V' : U' ⊔ V' = W')
  (hWW' : W' ≤ W) (hUU' : U' ≤ U) (hVV' : V' ≤ V)

include hU hV hU' hV' hUV hU'V' hUU' hVV' in
/-- **The Mayer--Vietoris connecting morphism commutes with restriction of the cover.** For two
covers `U ⊔ V = W` and `U' ⊔ V' = W'` with `W' ≤ W`, `U' ≤ U` and `V' ≤ V`, the square

`Hⁿ(U ⊓ V,-) ⟶ Hⁿ(U' ⊓ V',-) ⟶ Hⁿ⁺¹(W',-)`,  `Hⁿ(U ⊓ V,-) ⟶ Hⁿ⁺¹(W,-) ⟶ Hⁿ⁺¹(W',-)`

commutes.  Together with
`Stacks.Cohomology.AmbientMayerVietoris.ambientFirst_eq` and
`Stacks.Cohomology.AbsoluteMayerVietoris.mvSecond_eq`, which exhibit the other two maps of the
sequence as restriction maps, this makes the restriction maps a morphism of the two
Mayer--Vietoris long exact sequences. -/
theorem ambientDelta_restrict (hI : U' ⊓ V' ≤ U ⊓ V) (n : ℕ) :
    HrestrictNT O hI n ≫ ambientDelta O W' U' V' hU' hV' hU'V' n =
      ambientDelta O W U V hU hV hUV n ≫ HrestrictNT O hWW' (n + 1) :=
  CategoryTheory.rightDerivedDelta_comp_of_hom
    (ambientToCover O W U V hU hV) (ambientToIntersection O U V)
    (ambientToCover_comp_ambientToIntersection O W U V hU hV)
    (fun M hM => ambientShortExact_on_injectives O W U V hU hV hUV M hM)
    (ambientToCover O W' U' V' hU' hV') (ambientToIntersection O U' V')
    (ambientToCover_comp_ambientToIntersection O W' U' V' hU' hV')
    (fun M hM => ambientShortExact_on_injectives O W' U' V' hU' hV' hU'V' M hM)
    (secRestrict O hWW') (restrictCoverMiddle O U V U' V' hUU' hVV') (secRestrict O hI)
    (ambientToCover_comp_restrictCoverMiddle O W U V W' U' V' hU hV hU' hV' hWW' hUU' hVV')
    (restrictCoverMiddle_comp_ambientToIntersection O U V U' V' hUU' hVV' hI) n

include hU hV hU' hV' hUV hU'V' hUU' hVV' in
/-- **The Mayer--Vietoris connecting morphism commutes with restriction of the cover**, read on a
class. -/
theorem ambientDelta_restrict_apply (hI : U' ⊓ V' ≤ U ⊓ V) (n : ℕ) (G : SheafOfModules.{u} O)
    (θ : (Hgroup O (U ⊓ V) n G : Type u)) :
    (ambientDelta O W' U' V' hU' hV' hU'V' n).app G (Hrestrict O hI n G θ) =
      Hrestrict O hWW' (n + 1) G ((ambientDelta O W U V hU hV hUV n).app G θ) := by
  have h := congrArg (fun t : Hfunctor O (U ⊓ V) n ⟶ Hfunctor O W' (n + 1) => t.app G θ)
    (ambientDelta_restrict O W U V W' U' V' hU hV hU' hV' hUV hU'V' hWW' hUU' hVV' hI n)
  simpa [Hrestrict, AddCommGrpCat.comp_apply] using h

include hU hV hUV in
/-- **The Mayer--Vietoris connecting morphism commutes with cutting the cover by a third open.**
For a cover `U ⊔ V = W` and any open `T`, the opens `U ⊓ T` and `V ⊓ T` cover `W ⊓ T`, and the
restriction maps to the cut cover commute with the connecting morphisms.  This is the form in
which the Mayer--Vietoris induction of [Stacks, Tag 09MR] uses the comparison, with `T` the
nonvanishing open of a global section of an invertible module. -/
theorem ambientDelta_restrict_inf (T : Opens X) (n : ℕ) :
    HrestrictNT O (inf_le_inf (inf_le_left : U ⊓ T ≤ U) (inf_le_left : V ⊓ T ≤ V)) n ≫
        ambientDelta O (W ⊓ T) (U ⊓ T) (V ⊓ T) (inf_le_inf_right T hU) (inf_le_inf_right T hV)
          (by rw [← inf_sup_right, hUV]) n =
      ambientDelta O W U V hU hV hUV n ≫ HrestrictNT O (inf_le_left : W ⊓ T ≤ W) (n + 1) :=
  ambientDelta_restrict O W U V (W ⊓ T) (U ⊓ T) (V ⊓ T) hU hV (inf_le_inf_right T hU)
    (inf_le_inf_right T hV) hUV (by rw [← inf_sup_right, hUV]) inf_le_left inf_le_left
    inf_le_left _ n

end Hgroup

end Stacks.Cohomology.AmbientMayerVietoris

end
