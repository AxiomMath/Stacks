module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import StacksFrontier.Homology.Injectives.KInjective.RightAdjointOfExact
public import StacksFrontier.Homology.Injectives.KInjective.RightDerivedCriterion

/-!
# Transporting an unbounded right derived functor across an equivalence of abelian categories

Let `u : A ⥤ B` be an additive equivalence of Grothendieck abelian categories and let
`F : K(B) ⥤ H` be a functor on the homotopy category of `ℤ`-indexed cochain complexes in `B`
with a right derived functor `RF : D(B) ⥤ H`. Then `u.mapHomotopyCategory (.up ℤ) ⋙ F` has

`u.mapDerivedCategory ⋙ RF : D(A) ⥤ H`

as a right derived functor, so the value of the derived functor at an object `P` of `D(A)` is the
value of `RF` at the object `u(P)` of `D(B)`. Applied to `F = G.mapHomotopyCategory (.up ℤ) ⋙ Qh`
for an additive `G : B ⥤ E`, this says that the unbounded hypercohomology `R(u ⋙ G)` computed in
`A` is the unbounded hypercohomology `RG` computed in `B` after applying `u`, degreewise as well
as in the derived category.

This is the *pre*composition statement. The *post*composition one — deriving `F` and then
applying the functor an exact `G` induces on derived categories derives `F ⋙ G` — is
`Stacks.Cohomology.SiteCohomologyPresheaf.totalRightDerivedMapDerivedCategoryIso`, and nothing of
it is reused here: the two have no common content beyond the uniqueness of right derived functors.

The nearest existing statement is the base-change square
`Stacks.Cohomology.UnboundedComplexes.derivedBaseChangeIso`: for exact `α : A ⥤ A'`,
`β : B ⥤ B'` and additive `F : A ⥤ B`, `F' : A' ⥤ B'` with `α ⋙ F' ≅ F ⋙ β` and `α` preserving
K-injectivity, `Dα ⋙ RF' ≅ RF ⋙ Dβ`. That is not what is proved here, and this file does not
reduce to it: there `F'` is an additive functor *between abelian categories* and `RF'` lands in a
derived category, whereas the theorem below is for an arbitrary functor `F : K(B) ⥤ H` into an
arbitrary category `H` — the generality the hypercohomology groups of a site, or any other
non-derived-category target, are stated at. Conversely the base-change square is not an instance
of this one: it moves the target along `β` as well. The hypercohomology comparison at the end is
in the overlap, and is derived from the theorem below rather than from the square, which in the
degenerate case `β = 𝟭` carries a spurious `(𝟭 E).mapDerivedCategory` and demands a second right
derived functor, with its unit, as input.

## The proof

A candidate right derived functor is recognised by its unit being invertible at every K-injective
complex (`Stacks.Injectives.rightDerived_of_kInjective_units`), K-injective resolutions existing
over a Grothendieck abelian category. The unit here, `mapDerivedCategoryCompUnit`, is the unit
`α` of `RF` read at `u`-images, corrected by `CategoryTheory.Functor.mapDerivedCategoryFactorsh`,
which is the identification of `u.mapDerivedCategory` as the functor induced by
`u.mapHomotopyCategory`. At a K-injective `I` its first factor is `α` at the complex
`(u.mapHomologicalComplex (.up ℤ)).obj I`, which is again K-injective because `u` is an exact
equivalence (`Stacks.Injectives.isKInjective_mapHomologicalComplex_of_isEquivalence`, Tag 070G
for an equivalence), so `α` is invertible there; the second factor is `RF` applied to an
isomorphism. That is the whole argument, and it is where the hypothesis that `u` is an
equivalence, rather than merely exact, is used.

## Main definitions

* `Stacks.Injectives.mapDerivedCategoryCompUnit`: the candidate unit
  `u.mapHomotopyCategory (.up ℤ) ⋙ F ⟶ Qh ⋙ (u.mapDerivedCategory ⋙ RF)`.
* `Stacks.Injectives.totalRightDerivedPrecompIso`: the comparison
  `R(u.mapHomotopyCategory (.up ℤ) ⋙ F) ≅ u.mapDerivedCategory ⋙ RF`.
* `Stacks.Injectives.totalRightDerivedPrecompObjIso`: that comparison at an object of `D(A)`,
  which is the object-level transport.
* `Stacks.Injectives.mapHomotopyCategoryPrecompSourceIso`: the underived comparison of the two
  functors `K(A) ⥤ D(E)` attached to `G : B ⥤ E`.
* `Stacks.Injectives.derivedPrecompIso`: the comparison
  `R(u ⋙ G) ≅ u.mapDerivedCategory ⋙ RG` of unbounded derived functors.

## Main results

* `Stacks.Injectives.isRightDerivedFunctor_mapDerivedCategory_comp`:
  `u.mapDerivedCategory ⋙ RF` is a right derived functor of `u.mapHomotopyCategory (.up ℤ) ⋙ F`.
* `Stacks.Injectives.derivedPrecompObjIso` and `Stacks.Injectives.homologyDerivedPrecompObjIso`:
  the object-level transport, in the derived category of `E` and on each hypercohomology group.

## Implementation notes

The existence of the right derived functors is carried as instance arguments rather than deduced
from the Grothendieck hypotheses, so that no second copy of
`Stacks.Cohomology.Localization.hasRightDerivedFunctorOfGrothendieck` — the instance producing
them from functorial K-injective resolutions — is introduced here; a consumer that has imported
it needs to supply nothing. `IsGrothendieckAbelian` is needed for both categories all the same:
in `A` because the K-injective criterion for recognising a derived functor runs over K-injective
resolutions there, and in `B` because the invertibility of `α` at a K-injective complex is itself
that criterion on the other side.

Both categories carry their own universe for the `Hom`-sets of the derived category, as
`CategoryTheory.Functor.mapDerivedCategory` allows; the equivalence `u` relates the categories,
not the choices of derived category.

The functor `G` of the hypercohomology section is only assumed additive, and `E` only abelian with
a chosen derived category: nothing about `G` beyond additivity enters, since the comparison is
made between the two right derived functors and not computed.

## References

* [Stacks Project, Tag 070G](https://stacks.math.columbia.edu/tag/070G)
* [Stacks Project, Tag 070K](https://stacks.math.columbia.edu/tag/070K)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v₁ v₂ vE vH u₁ u₂ uE uH w₁ w₂ wD₁ wD₂ wE

namespace Stacks.Injectives

variable {A : Type u₁} [Category.{v₁} A] [Abelian A] [IsGrothendieckAbelian.{w₁, v₁, u₁} A]
  [HasDerivedCategory.{wD₁} A]
  {B : Type u₂} [Category.{v₂} B] [Abelian B] [IsGrothendieckAbelian.{w₂, v₂, u₂} B]
  [HasDerivedCategory.{wD₂} B]
  {H : Type uH} [Category.{vH} H]
  (u : A ⥤ B) [u.Additive] [u.IsEquivalence]

/-! ### The transported unit -/

/-- The candidate unit exhibiting `u.mapDerivedCategory ⋙ RF` as a right derived functor of
`u.mapHomotopyCategory (.up ℤ) ⋙ F`: the unit `α` of `RF`, read at the `u`-images, followed by
`RF` applied to the identification `CategoryTheory.Functor.mapDerivedCategoryFactorsh` of
`u.mapDerivedCategory` as the functor induced by `u.mapHomotopyCategory (.up ℤ)`. -/
public def mapDerivedCategoryCompUnit (F : HomotopyCategory B (ComplexShape.up ℤ) ⥤ H)
    (RF : DerivedCategory B ⥤ H) (α : F ⟶ DerivedCategory.Qh ⋙ RF) :
    u.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ F ⟶
      DerivedCategory.Qh ⋙ (u.mapDerivedCategory ⋙ RF) :=
  Functor.whiskerLeft (u.mapHomotopyCategory (ComplexShape.up ℤ)) α ≫
    (Functor.associator (u.mapHomotopyCategory (ComplexShape.up ℤ))
      DerivedCategory.Qh RF).inv ≫
    Functor.whiskerRight u.mapDerivedCategoryFactorsh.inv RF ≫
    (Functor.associator DerivedCategory.Qh u.mapDerivedCategory RF).hom

omit [IsGrothendieckAbelian.{w₁, v₁, u₁} A] [IsGrothendieckAbelian.{w₂, v₂, u₂} B] in
/-- The two factors of `Stacks.Injectives.mapDerivedCategoryCompUnit`, the associators being
identities. -/
@[simp]
public lemma mapDerivedCategoryCompUnit_app (F : HomotopyCategory B (ComplexShape.up ℤ) ⥤ H)
    (RF : DerivedCategory B ⥤ H) (α : F ⟶ DerivedCategory.Qh ⋙ RF)
    (K : HomotopyCategory A (ComplexShape.up ℤ)) :
    (mapDerivedCategoryCompUnit u F RF α).app K =
      α.app ((u.mapHomotopyCategory (ComplexShape.up ℤ)).obj K) ≫
        RF.map (u.mapDerivedCategoryFactorsh.inv.app K) := by
  simp [mapDerivedCategoryCompUnit]

/-! ### The transport -/

/-- **An unbounded right derived functor transports across an additive equivalence of
Grothendieck abelian categories.** If `RF` is a right derived functor of `F : K(B) ⥤ H` with unit
`α`, then `u.mapDerivedCategory ⋙ RF` is a right derived functor of
`u.mapHomotopyCategory (.up ℤ) ⋙ F`, with the unit
`Stacks.Injectives.mapDerivedCategoryCompUnit`.

The candidate unit is invertible at every K-injective complex `I` of `A`: its first factor is `α`
at `(u.mapHomologicalComplex (.up ℤ)).obj I`, which is K-injective because `u` is an exact
equivalence, and its second factor is `RF` applied to an isomorphism. By [Stacks, Tag 070K] that
makes it a right derived functor. -/
public theorem isRightDerivedFunctor_mapDerivedCategory_comp
    (F : HomotopyCategory B (ComplexShape.up ℤ) ⥤ H) (RF : DerivedCategory B ⥤ H)
    (α : F ⟶ DerivedCategory.Qh ⋙ RF)
    [RF.IsRightDerivedFunctor α (HomotopyCategory.quasiIso B (ComplexShape.up ℤ))]
    [(u.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ F).HasRightDerivedFunctor
      (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))] :
    (u.mapDerivedCategory ⋙ RF).IsRightDerivedFunctor (mapDerivedCategoryCompUnit u F RF α)
      (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) := by
  refine rightDerived_of_kInjective_units _ _ _ (fun I _ ↦ ?_)
  have : CochainComplex.IsKInjective
      ((u.mapHomologicalComplex (ComplexShape.up ℤ)).obj I) :=
    isKInjective_mapHomologicalComplex_of_isEquivalence u I
  have hα : IsIso (α.app ((u.mapHomotopyCategory (ComplexShape.up ℤ)).obj
      ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj I))) :=
    rightDerivedUnit_isIso_at_kInjective F RF α
      ((u.mapHomologicalComplex (ComplexShape.up ℤ)).obj I)
  rw [mapDerivedCategoryCompUnit_app]
  exact IsIso.comp_isIso' hα
    (RF.mapIso (u.mapDerivedCategoryFactorsh.symm.app _)).isIso_hom

/-- **The comparison of the two unbounded right derived functors.** The right derived functor of
`u.mapHomotopyCategory (.up ℤ) ⋙ F` is `u.mapDerivedCategory ⋙ RF`, by uniqueness of right
derived functors. -/
public def totalRightDerivedPrecompIso
    (F : HomotopyCategory B (ComplexShape.up ℤ) ⥤ H) (RF : DerivedCategory B ⥤ H)
    (α : F ⟶ DerivedCategory.Qh ⋙ RF)
    [RF.IsRightDerivedFunctor α (HomotopyCategory.quasiIso B (ComplexShape.up ℤ))]
    [(u.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ F).HasRightDerivedFunctor
      (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))] :
    (u.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ F).totalRightDerived DerivedCategory.Qh
        (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) ≅
      u.mapDerivedCategory ⋙ RF :=
  have := isRightDerivedFunctor_mapDerivedCategory_comp u F RF α
  Functor.rightDerivedNatIso
    ((u.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ F).totalRightDerived DerivedCategory.Qh
      (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)))
    (u.mapDerivedCategory ⋙ RF)
    ((u.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ F).totalRightDerivedUnit DerivedCategory.Qh
      (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)))
    (mapDerivedCategoryCompUnit u F RF α)
    (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) (Iso.refl _)

/-- **The object-level transport of an unbounded right derived functor across the equivalence**:
at every object `P` of `D(A)`, the right derived functor of `u.mapHomotopyCategory (.up ℤ) ⋙ F`
takes the value that `RF` takes at `u(P)`. -/
public def totalRightDerivedPrecompObjIso
    (F : HomotopyCategory B (ComplexShape.up ℤ) ⥤ H) (RF : DerivedCategory B ⥤ H)
    (α : F ⟶ DerivedCategory.Qh ⋙ RF)
    [RF.IsRightDerivedFunctor α (HomotopyCategory.quasiIso B (ComplexShape.up ℤ))]
    [(u.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ F).HasRightDerivedFunctor
      (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))]
    (P : DerivedCategory A) :
    ((u.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ F).totalRightDerived DerivedCategory.Qh
        (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))).obj P ≅
      RF.obj (u.mapDerivedCategory.obj P) :=
  (totalRightDerivedPrecompIso u F RF α).app P

/-! ### Hypercohomology -/

section Hypercohomology

variable {E : Type uE} [Category.{vE} E] [Abelian E] [HasDerivedCategory.{wE} E]
  (G : B ⥤ E) [G.Additive]

/-- The underived comparison behind the transport of hypercohomology: taking `G`-images
degreewise after `u`-images degreewise, and localizing, is taking `(u ⋙ G)`-images degreewise and
localizing. It is `CategoryTheory.Functor.mapHomotopyCategoryCompIso` at the identity
`u ⋙ G ≅ u ⋙ G`. -/
public def mapHomotopyCategoryPrecompSourceIso :
    u.mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        (G.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh) ≅
      (u ⋙ G).mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh :=
  (Functor.associator (u.mapHomotopyCategory (ComplexShape.up ℤ))
      (G.mapHomotopyCategory (ComplexShape.up ℤ)) DerivedCategory.Qh).symm ≪≫
    Functor.isoWhiskerRight
      (Functor.mapHomotopyCategoryCompIso (Iso.refl (u ⋙ G)) (ComplexShape.up ℤ))
      DerivedCategory.Qh

variable [(G.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).HasRightDerivedFunctor
    (HomotopyCategory.quasiIso B (ComplexShape.up ℤ))]
  [((u ⋙ G).mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).HasRightDerivedFunctor
    (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))]

omit [IsGrothendieckAbelian.{w₁, v₁, u₁} A] [HasDerivedCategory.{wD₁} A]
  [IsGrothendieckAbelian.{w₂, v₂, u₂} B] [HasDerivedCategory.{wD₂} B] [u.IsEquivalence]
  [(G.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).HasRightDerivedFunctor
    (HomotopyCategory.quasiIso B (ComplexShape.up ℤ))] in
/-- Deriving the degreewise `u`-images followed by the degreewise `G`-images is possible as soon
as deriving the degreewise `(u ⋙ G)`-images is: the two functors on `K(A)` are isomorphic. -/
public lemma hasRightDerivedFunctor_mapHomotopyCategory_comp :
    (u.mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        (G.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)).HasRightDerivedFunctor
      (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) :=
  (Functor.hasRightDerivedFunctor_iff_of_iso (mapHomotopyCategoryPrecompSourceIso u G)
    (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))).2 inferInstance

attribute [local instance] hasRightDerivedFunctor_mapHomotopyCategory_comp

/-- **The unbounded hypercohomology of `u ⋙ G` on `A` is the unbounded hypercohomology of `G` on
`B`, after applying `u`.** Both are right derived functors of isomorphic functors on `K(A)`: the
left-hand side derives the degreewise `(u ⋙ G)`-images, and `u.mapDerivedCategory ⋙ RG` derives
the degreewise `u`-images followed by the degreewise `G`-images by
`Stacks.Injectives.isRightDerivedFunctor_mapDerivedCategory_comp`. -/
public def derivedPrecompIso :
    ((u ⋙ G).mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).totalRightDerived
        DerivedCategory.Qh (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) ≅
      u.mapDerivedCategory ⋙
        (G.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).totalRightDerived
          DerivedCategory.Qh (HomotopyCategory.quasiIso B (ComplexShape.up ℤ)) :=
  Functor.rightDerivedNatIso
    (((u ⋙ G).mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).totalRightDerived
      DerivedCategory.Qh (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)))
    ((u.mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        (G.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)).totalRightDerived
      DerivedCategory.Qh (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)))
    (((u ⋙ G).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh).totalRightDerivedUnit DerivedCategory.Qh
        (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)))
    ((u.mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        (G.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)).totalRightDerivedUnit
      DerivedCategory.Qh (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)))
    (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))
    (mapHomotopyCategoryPrecompSourceIso u G).symm ≪≫
  totalRightDerivedPrecompIso u (G.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
    ((G.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).totalRightDerived
      DerivedCategory.Qh (HomotopyCategory.quasiIso B (ComplexShape.up ℤ)))
    ((G.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).totalRightDerivedUnit
      DerivedCategory.Qh (HomotopyCategory.quasiIso B (ComplexShape.up ℤ)))

/-- **The object-level transport of the unbounded derived functor across the equivalence**: the
unbounded hypercohomology of an object `P` of `D(A)` relative to `u ⋙ G` is the unbounded
hypercohomology of `u(P)` relative to `G`. -/
public def derivedPrecompObjIso (P : DerivedCategory A) :
    (((u ⋙ G).mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).totalRightDerived
        DerivedCategory.Qh (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))).obj P ≅
      ((G.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).totalRightDerived
        DerivedCategory.Qh
          (HomotopyCategory.quasiIso B (ComplexShape.up ℤ))).obj
            (u.mapDerivedCategory.obj P) :=
  (derivedPrecompIso u G).app P

/-- **Hypercohomology computed in `A` agrees with hypercohomology computed in `B` after applying
`u`**, in every degree: the degree-`q` cohomology of the unbounded derived functor of `u ⋙ G` at
`P` is the degree-`q` cohomology of the unbounded derived functor of `G` at `u(P)`. -/
public def homologyDerivedPrecompObjIso (P : DerivedCategory A) (q : ℤ) :
    (DerivedCategory.homologyFunctor E q).obj
        ((((u ⋙ G).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
          DerivedCategory.Qh).totalRightDerived DerivedCategory.Qh
            (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))).obj P) ≅
      (DerivedCategory.homologyFunctor E q).obj
        (((G.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).totalRightDerived
          DerivedCategory.Qh (HomotopyCategory.quasiIso B (ComplexShape.up ℤ))).obj
            (u.mapDerivedCategory.obj P)) :=
  (DerivedCategory.homologyFunctor E q).mapIso (derivedPrecompObjIso u G P)

end Hypercohomology

end Stacks.Injectives

end
