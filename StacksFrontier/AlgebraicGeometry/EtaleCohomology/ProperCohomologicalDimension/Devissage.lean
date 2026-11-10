module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.Torsion.TorsionCohomologySingle
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BlowUpSquare.LongExactSequence
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Torsion.DerivedCategoryOfTorsionSheaves

/-!
# Dévissage of étale cohomology along a square that is an isomorphism off a closed set

Consider a cartesian square of schemes
```
E --j--> X'
|π       |b
v        v
Z --i--> X
```
with `i` a closed immersion, `b` an isomorphism over the open complement of `Z`, and such that
cohomology commutes with base change for `b` (for instance `b` proper, by the proper base change
theorem, [Stacks, Tag 095T]). For a torsion abelian sheaf `F` on `X_étale` the Mayer–Vietoris
long exact sequence of [Stacks, Tag 0EW3]
`H^p(E, F|_E) ⟶ H^{p+1}(X, F) ⟶ H^{p+1}(X', F|_{X'}) × H^{p+1}(Z, F|_Z)`
shows that `H^{p+1}(X, F) = 0` as soon as the three outer groups vanish. This is the step used
three times in the proof of [Stacks, Tag 095U]: for the normalization of a reduced scheme, for
the closure of the graph of a rational function, and for a decomposition into open and closed
pieces.

## Main results

* `Stacks.EtaleCohomology.subsingleton_sheafH_iff_etaleDerivedCohomology`: Mathlib's
  `Sheaf.H F p` vanishes exactly when `H^p(X, F[0]) = Hom(ℤ_X[-p], F[0])` does.
* `Stacks.EtaleCohomology.subsingleton_sheafH_of_isPullback_of_cohomologyCommutesWithBaseChange`:
  the dévissage above.

## References

* [Stacks Project, Tag 0EW3](https://stacks.math.columbia.edu/tag/0EW3)
* [Stacks Project, Tag 095U](https://stacks.math.columbia.edu/tag/095U)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace Stacks.EtaleCohomology

/-- **Sheaf cohomology is étale cohomology of the sheaf placed in degree `0`.** For an abelian
sheaf `F` on `X_étale`, Mathlib's `Sheaf.H F p = Ext^p(ℤ_X, F)` vanishes exactly when
`H^p(X, F[0]) = Hom(ℤ_X[-p], F[0])` does. -/
theorem subsingleton_sheafH_iff_etaleDerivedCohomology (X : Scheme.{u})
    [HasExt.{max (u + 1) v} (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) (p : ℕ) :
    Subsingleton (Sheaf.H.{max (u + 1) v} F p) ↔
      Subsingleton (etaleDerivedCohomology.{u, v} X p
        ((DerivedCategory.singleFunctor _ 0).obj F)) :=
  (Abelian.Ext.homEquiv).subsingleton_congr.trans
    (etaleDerivedCohomologyEquivShiftedHom.{u, v} X p _).toEquiv.subsingleton_congr.symm

/-- The cohomology of the derived inverse image of a sheaf placed in degree `0` is the
cohomology of the inverse image sheaf. -/
theorem subsingleton_sheafH_inverseImage_iff_etaleDerivedCohomology {X Y : Scheme.{u}}
    (f : Y ⟶ X)
    [HasExt.{max (u + 1) v} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) (p : ℕ) :
    Subsingleton (Sheaf.H.{max (u + 1) v} ((etaleAbelianInverseImage.{u, v} f).obj F) p) ↔
      Subsingleton (etaleDerivedCohomology.{u, v} Y p
        ((etaleAbelianDerivedInverseImage.{u, v} f).obj
          ((DerivedCategory.singleFunctor _ 0).obj F))) :=
  (subsingleton_sheafH_iff_etaleDerivedCohomology.{u, v} Y _ p).trans
    ((Iso.homCongr (Iso.refl _)
      (((etaleAbelianInverseImage.{u, v} f).mapDerivedCategorySingleFunctor 0).app
        F)).subsingleton_congr.symm)

/-- **Dévissage along a square that is an isomorphism off a closed set** ([Stacks, Tag 0EW3]).
Let
```
E --j--> X'
|π       |b
v        v
Z --i--> X
```
be a cartesian square of schemes with `i` a closed immersion, `o : U ⟶ X` an open immersion onto
the complement of `Z`, `b` an isomorphism over `U`, and suppose cohomology commutes with base
change for `b`. For a torsion abelian sheaf `F` on `X_étale`, if `H^p(E, F|_E)`,
`H^{p+1}(X', F|_{X'})` and `H^{p+1}(Z, F|_Z)` vanish, then so does `H^{p+1}(X, F)`. -/
theorem subsingleton_sheafH_of_isPullback_of_cohomologyCommutesWithBaseChange
    [∀ S : Scheme.{u},
      HasExt.{max (u + 1) v} (Sheaf S.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]
    {X Z X' E : Scheme.{u}} (i : Z ⟶ X) (b : X' ⟶ X) (j : E ⟶ X') (π : E ⟶ Z)
    [IsClosedImmersion i] {U U' : Scheme.{u}} (o : U ⟶ X) [IsOpenImmersion o]
    (hio : Set.range o.base = (Set.range i.base)ᶜ) (sq : IsPullback j π b i)
    (o' : U' ⟶ X') (bU : U' ⟶ U) (sqU : IsPullback o' bU b o) [IsIso bU]
    (hb : CohomologyCommutesWithBaseChange.{u, v} b)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})
    (hF : Stacks.Torsion.torsionSheafProperty X.smallEtaleTopology F) (p : ℕ)
    (hE : Subsingleton (Sheaf.H.{max (u + 1) v}
      ((etaleAbelianInverseImage.{u, v} (j ≫ b)).obj F) p))
    (hX' : Subsingleton (Sheaf.H.{max (u + 1) v}
      ((etaleAbelianInverseImage.{u, v} b).obj F) (p + 1)))
    (hZ : Subsingleton (Sheaf.H.{max (u + 1) v}
      ((etaleAbelianInverseImage.{u, v} i).obj F) (p + 1))) :
    Subsingleton (Sheaf.H.{max (u + 1) v} F (p + 1)) := by
  let K := (DerivedCategory.singleFunctor (Sheaf X.smallEtaleTopology
    AddCommGrpCat.{max (u + 1) v}) 0).obj F
  have hKge : K.IsGE 0 := by
    change ((DerivedCategory.singleFunctor _ 0).obj F).IsGE 0
    infer_instance
  obtain ⟨δ, hδ⟩ :=
    exists_longExactSequence_of_isPullback_of_cohomologyCommutesWithBaseChange.{u, v}
      i b j π (j ≫ b) sq.w rfl o hio sq o' bU sqU hb K 0 hKge
      (Stacks.Torsion.torsionCohomologyProperty_singleFunctor _ F hF)
  have hE' := (subsingleton_sheafH_inverseImage_iff_etaleDerivedCohomology.{u, v} (j ≫ b) F
    p).1 hE
  have hX'' := (subsingleton_sheafH_inverseImage_iff_etaleDerivedCohomology.{u, v} b F
    (p + 1)).1 hX'
  have hZ' := (subsingleton_sheafH_inverseImage_iff_etaleDerivedCohomology.{u, v} i F
    (p + 1)).1 hZ
  rw [subsingleton_sheafH_iff_etaleDerivedCohomology.{u, v} X F (p + 1)]
  refine ⟨fun x y ↦ ?_⟩
  suffices h : ∀ z : etaleDerivedCohomology.{u, v} X ((p + 1 : ℕ) : ℤ) K, z = 0 by
    rw [h x, h y]
  intro z
  have hex := (hδ (p : ℤ)).2.2
  have hz : z ∈ Set.range (δ (p : ℤ)) := by
    refine (hex (z : etaleDerivedCohomology.{u, v} X ((p : ℤ) + 1) K)).1 ?_
    exact Prod.ext (hX''.allEq _ _) (hZ'.allEq _ _)
  obtain ⟨w, hw⟩ := hz
  rw [← hw, Subsingleton.elim w 0, map_zero]

end Stacks.EtaleCohomology

end
