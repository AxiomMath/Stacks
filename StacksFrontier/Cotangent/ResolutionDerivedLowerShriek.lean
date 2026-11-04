module

public import StacksFrontier.Algebra.Homology.DerivedCategory.LeftDerivedPrecomposition
public import StacksFrontier.AlgebraicTopology.SimplicialObject.CopowerHomotopy
public import StacksFrontier.CategoryTheory.Sites.Cohomology.CategoryHomology.RepresentableAcyclicity
public import
  StacksFrontier.CategoryTheory.Sites.Cohomology.ChaoticSite.DerivedColimitByPointResolutionAbelian
public import StacksFrontier.Cotangent.ResolutionPointCriterion
import StacksCore.Tactic.StacksAttribute

/-!
# Derived lower shriek on the site of polynomial algebras, computed by a resolution

Let `A → B` be a ring map, let `C = C_{B/A}` be the site of Tag 08PR — the opposite of the
category of polynomial `A`-algebras augmented to `B`, with the chaotic topology — and let
`π : (Sh(C), B̲) → (Sh(*), B)` be as there. Let `ε : P_• → B` be a resolution of `B` over `A`:
each `P_n` is a polynomial algebra over `A` and `ε` is a trivial Kan fibration of underlying
simplicial sets; the standard resolution is one (Tag 08QI). Then

`Lπ_!(ℱ) = ℱ(P_•, ε)` in `D(Ab)`, resp. `D(B)`,

functorially in `ℱ` in `Ab(C)`, resp. `Mod(B̲)`. This file proves that statement on the site
`C_{B/A}` itself, `CommAlgCat.polynomialSite`, with no restriction on the number of variables.

## The statement

The topology of `C_{B/A}` is chaotic (`CommAlgCat.polynomialTopology_eq_bot`), so every presheaf
is a sheaf: `Ab(C)` is the category of abelian-group-valued diagrams on `Cᵒᵖ`, and `Mod(B̲)` is
the category of diagrams of `B`-modules. `π_!` followed by the sections at the point is the
colimit over `Cᵒᵖ` (Tag 08PF), and `Lπ_!` is its total left derived functor on the unbounded
derived category, `CommAlgCat.polynomialDerivedLowerShriek`, which exists because diagrams on
`C_{B/A}` have enough projectives. `ℱ(P_•, ε)` is the simplicial object obtained by evaluating
`ℱ` on the cosimplicial object `(P_•, ε)` of `C_{B/A}` (`CommAlgCat.resolutionCosimplicialObject`);
its Moore complex, placed in cohomological degrees `≤ 0`, is `CommAlgCat.polynomialMooreCochain`.

**Universes.** The objects of `C_{B/A}` live in `Type (u + 1)` and its morphisms in `Type u`
when `A` and `B` do. A colimit over `Cᵒᵖ` therefore exists for coefficients in `Type (u + 1)`,
and that is the coefficient universe used: abelian groups `AddCommGrpCat.{u + 1}` and modules
`ModuleCat.{u + 1}` over `ULift.{u + 1} B`, the ring on the point of `π` in
`CommAlgCat.polynomialRingedPoint`.

## The proof

The source applies the criterion of Tag 08Q9 (Lemma 08PS), whose hypothesis — every simplicial
set `Mor_C((P_•, ε), W)` is homotopy equivalent to a point — is
`CommAlgCat.exists_homotopyEquivalences_resolutionMor`, proved there from Tags 08NN, 08NR and
08NS; for the standard resolution the trivial Kan fibration is Tag 08QI, itself proved from
Tags 08ND, 08P2 and 08P1. The derived form of the criterion, natural in `ℱ`, is
`Stacks.ChaoticSite.ModuleValued.mooreCochainNatIsoDerivedColimit` and its abelian twin; they are
stated for a small category, and are applied here to `CategoryTheory.AsSmall` of `C_{B/A}`, the
same category with its morphism sets lifted to `Type (u + 1)`, which is equivalent to it:

* the point-resolution hypothesis passes to `AsSmall` because lifting a simplicial set along
  `uliftFunctor` preserves homotopy equivalences (`Stacks.ChaoticSite.isPointResolution_comp_up`);
* restricting a diagram along `AsSmall.down` does not change the simplicial object `ℱ(P_•, ε)`;
* `Lπ_!` on `C_{B/A}` and on `AsSmall` agree on objects placed in degree zero, naturally:
  restriction along `AsSmall.down` is an exact equivalence, so it preserves projectives, and it
  commutes with the colimit; this is `Stacks.Homology.singleLeftDerivedPrecompIso`.

So the model only carries the comparison; the statements are about `C_{B/A}`.

## Main definitions

* `CommAlgCat.polynomialDerivedLowerShriek`: `Lπ_! : D(C_{B/A}) ⥤ D`, the total left derived
  functor of the colimit over the index category of diagrams on `C_{B/A}`.
* `CommAlgCat.polynomialMooreCochain`: the extended Moore complex of `ℱ(U_•)`.
* `CommAlgCat.resolutionAbelianDerivedLowerShriekIso`,
  `CommAlgCat.resolutionModuleDerivedLowerShriekIso`: `Lπ_!(ℱ) = ℱ(P_•, ε)` for a resolution.
* `CommAlgCat.standardResolutionAbelianDerivedLowerShriekIso`,
  `CommAlgCat.standardResolutionModuleDerivedLowerShriekIso`: **Tag 08PT**.

## References

* [Stacks Project, Tag 08PT](https://stacks.math.columbia.edu/tag/08PT)
* [Stacks Project, Tag 08PS](https://stacks.math.columbia.edu/tag/08PS)
* [Stacks Project, Tag 08PR](https://stacks.math.columbia.edu/tag/08PR)
* [Stacks Project, Tag 08Q9](https://stacks.math.columbia.edu/tag/08Q9)
* [Stacks Project, Tag 08QI](https://stacks.math.columbia.edu/tag/08QI)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicTopology

namespace Stacks.ChaoticSite

universe w v u₁

/-- **The point-resolution hypothesis of Tag 08Q9 passes to the small model.** Let `C` be a
category, not necessarily small, and `U_•` a cosimplicial object of `C` such that every simplicial
set `Mor_C(U_•, W)` is homotopy equivalent to a point. Then `U_•`, read in
`CategoryTheory.AsSmall C`, is a point resolution: the morphism sets of the small model are those
of `C` lifted along `uliftFunctor`, and lifting preserves homotopy equivalences of simplicial
sets. -/
theorem isPointResolution_comp_up {C : Type u₁} [Category.{v} C] (U : CosimplicialObject C)
    (h : ∀ W : C, ∃ f : U.op ⋙ yoneda.obj W ⟶ (Functor.const SimplexCategoryᵒᵖ).obj PUnit.{v + 1},
      SimplicialObject.homotopyEquivalences (Type v) f) :
    IsPointResolution (U ⋙ (AsSmall.up : C ⥤ AsSmall.{w} C)) := by
  intro W
  obtain ⟨f, hf⟩ := h (ULift.down W)
  let α : (U ⋙ (AsSmall.up : C ⥤ AsSmall.{w} C)).op ⋙ yoneda.obj W ≅
      (U.op ⋙ yoneda.obj (ULift.down W)) ⋙ uliftFunctor.{max w u₁, v} :=
    NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => rfl)
  let β : (Functor.const SimplexCategoryᵒᵖ).obj PUnit.{v + 1} ⋙ uliftFunctor.{max w u₁, v} ≅
      (Functor.const SimplexCategoryᵒᵖ).obj PUnit :=
    NatIso.ofComponents (fun _ => Equiv.toIso
      { toFun := fun _ => PUnit.unit
        invFun := fun _ => ULift.up PUnit.unit
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }) (fun _ => rfl)
  exact ⟨α.hom ≫ ((SimplicialObject.whiskering _ _).obj uliftFunctor).map f ≫ β.hom,
    SimplicialObject.homotopyEquivalences_iso_comp_iso α _ β
      (SimplicialObject.homotopyEquivalences_whiskering_map _ hf)⟩

end Stacks.ChaoticSite

namespace CommAlgCat

open Stacks.CategoryHomology

universe u

attribute [local instance] HasDerivedCategory.standard

variable (A : Type u) [CommRing A] (B : CommAlgCat.{u} A)

/-! ### Derived lower shriek on `C_{B/A}` -/

section DerivedLowerShriek

variable (D : Type*) [Category* D] [Abelian D] [HasColimitsOfShape (polynomialSite A B)ᵒᵖ D]
  [EnoughProjectives ((polynomialSite A B)ᵒᵖ ⥤ D)] [HasColimitsOfShape ℕ D]
  [HasExactColimitsOfShape ℕ D]

/-- **The colimit over the index category of diagrams on `C_{B/A}` has a total left derived
functor** on the unbounded derived category, defined at every object: Tag 0794 at the class of
projective objects. -/
theorem polynomialColim_hasPointwiseLeftDerivedFunctor :
    ((colim : ((polynomialSite A B)ᵒᵖ ⥤ D) ⥤ D).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh).HasPointwiseLeftDerivedFunctor
      (HomotopyCategory.quasiIso ((polynomialSite A B)ᵒᵖ ⥤ D) (ComplexShape.up ℤ)) :=
  hasPointwiseLeftDerivedFunctor_of_enoughProjectives (colim : ((polynomialSite A B)ᵒᵖ ⥤ D) ⥤ D)

/-- **`Lπ_!` for the morphism `π` of Tag 08PR**: the total left derived functor of the colimit
over the index category of diagrams on `C_{B/A}`, which is `π_!` followed by the sections at the
point (Tag 08PF), every presheaf on `C_{B/A}` being a sheaf. -/
def polynomialDerivedLowerShriek :
    DerivedCategory ((polynomialSite A B)ᵒᵖ ⥤ D) ⥤ DerivedCategory D :=
  have := polynomialColim_hasPointwiseLeftDerivedFunctor A B D
  ((colim : ((polynomialSite A B)ᵒᵖ ⥤ D) ⥤ D).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
    DerivedCategory.Qh).totalLeftDerived DerivedCategory.Qh
      (HomotopyCategory.quasiIso ((polynomialSite A B)ᵒᵖ ⥤ D) (ComplexShape.up ℤ))

/-- The comparison transformation exhibiting `CommAlgCat.polynomialDerivedLowerShriek` as a left
derived functor of the colimit. -/
def polynomialDerivedLowerShriekCounit :
    DerivedCategory.Qh ⋙ polynomialDerivedLowerShriek A B D ⟶
      (colim : ((polynomialSite A B)ᵒᵖ ⥤ D) ⥤ D).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh :=
  have := polynomialColim_hasPointwiseLeftDerivedFunctor A B D
  ((colim : ((polynomialSite A B)ᵒᵖ ⥤ D) ⥤ D).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
    DerivedCategory.Qh).totalLeftDerivedCounit DerivedCategory.Qh
      (HomotopyCategory.quasiIso ((polynomialSite A B)ᵒᵖ ⥤ D) (ComplexShape.up ℤ))

/-- `CommAlgCat.polynomialDerivedLowerShriek` is a left derived functor of the colimit, with
comparison `CommAlgCat.polynomialDerivedLowerShriekCounit`. -/
theorem polynomialDerivedLowerShriek_isLeftDerivedFunctor :
    (polynomialDerivedLowerShriek A B D).IsLeftDerivedFunctor
      (polynomialDerivedLowerShriekCounit A B D)
      (HomotopyCategory.quasiIso ((polynomialSite A B)ᵒᵖ ⥤ D) (ComplexShape.up ℤ)) := by
  have := polynomialColim_hasPointwiseLeftDerivedFunctor A B D
  dsimp [polynomialDerivedLowerShriek, polynomialDerivedLowerShriekCounit]
  infer_instance

end DerivedLowerShriek

/-! ### The comparison with the small model -/

section SmallModel

/-- The equivalence between diagrams on `C_{B/A}` and diagrams on its small model
`CategoryTheory.AsSmall`, given by restriction along `AsSmall.down`. -/
abbrev polynomialDiagramAsSmallEquivalence (D : Type*) [Category* D] :
    ((polynomialSite A B)ᵒᵖ ⥤ D) ≌ ((AsSmall.{u} (polynomialSite A B))ᵒᵖ ⥤ D) :=
  (AsSmall.equiv (C := polynomialSite A B)).op.congrLeft

/-- Diagrams of abelian groups on `C_{B/A}` have enough projectives: they are equivalent to the
diagrams on the small model, which do. -/
instance polynomialAbelianDiagramsEnoughProjectives :
    EnoughProjectives ((polynomialSite A B)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}) :=
  have : EnoughProjectives ((AsSmall.{u} (polynomialSite A B))ᵒᵖ ⥤ AddCommGrpCat.{u + 1}) :=
    presheafEnoughProjectives.{u + 1, u + 1} (AsSmall.{u} (polynomialSite A B))
  (Equivalence.enoughProjectives_iff (polynomialDiagramAsSmallEquivalence A B _)).mpr this

/-- Diagrams of `B`-modules on `C_{B/A}` have enough projectives: they are equivalent to the
diagrams on the small model, which do. -/
instance polynomialModuleDiagramsEnoughProjectives :
    EnoughProjectives ((polynomialSite A B)ᵒᵖ ⥤ ModuleCat.{u + 1} (ULift.{u + 1} (B : Type u))) :=
  have : EnoughProjectives
      ((AsSmall.{u} (polynomialSite A B))ᵒᵖ ⥤ ModuleCat.{u + 1} (ULift.{u + 1} (B : Type u))) :=
    moduleDiagramsEnoughProjectives (AsSmall.{u} (polynomialSite A B))
      (ULift.{u + 1} (B : Type u))
  (Equivalence.enoughProjectives_iff (polynomialDiagramAsSmallEquivalence A B _)).mpr this

/-- Countable filtered colimits of `B`-modules in `Type (u + 1)` are exact: the instance
`Stacks.CategoryHomology.hasExactColimitsOfShapeNatModuleCat` with its universes fixed, which
instance search cannot do on its own. -/
instance hasExactColimitsOfShapeNat_moduleCatULift :
    HasExactColimitsOfShape ℕ (ModuleCat.{u + 1} (ULift.{u + 1} (B : Type u))) :=
  hasExactColimitsOfShapeNatModuleCat.{u + 1, u + 1} (ULift.{u + 1} (B : Type u))

end SmallModel

/-! ### `Lπ_!(ℱ) = ℱ(P_•, ε)` -/

section Resolution

/-- **The complex `ℱ(U_•)`** for a cosimplicial object `U_•` of `C_{B/A}`: the Moore complex of
the simplicial object obtained by evaluating a diagram `ℱ` on `U_•`, read as a cochain complex
over `ℤ` with the simplicial degree `n` in cohomological degree `-n`, functorially in `ℱ`. -/
abbrev polynomialMooreCochain (U : CosimplicialObject (polynomialSite A B)) (D : Type*)
    [Category* D] [Abelian D] : ((polynomialSite A B)ᵒᵖ ⥤ D) ⥤ CochainComplex D ℤ :=
  (Functor.whiskeringLeft SimplexCategoryᵒᵖ (polynomialSite A B)ᵒᵖ D).obj U.op ⋙
    alternatingFaceMapComplex D ⋙ (ComplexShape.embeddingUpIntLE (0 : ℤ)).extendFunctor D

variable {A B} {P : SimplicialObject (CommAlgCat.{u} A)}
  (ε : P ⟶ (SimplicialObject.const (CommAlgCat.{u} A)).obj B)
  (hP : ∀ n, IsPolynomialAlgebra A (P.obj n))
  (hε : SSet.trivialKanFibrations (Functor.whiskerRight ε (forget (CommAlgCat.{u} A))))

include hε in
/-- The cosimplicial object of a resolution, read in the small model of `C_{B/A}`, is a point
resolution: this is Tag 08PS's computation of `Mor_C((P_•, ε), W)` transported to the model. -/
theorem isPointResolution_resolutionCosimplicialObject_comp_up :
    Stacks.ChaoticSite.IsPointResolution
      (resolutionCosimplicialObject ε hP ⋙
        (AsSmall.up : polynomialSite A B ⥤ AsSmall.{u} (polynomialSite A B))) :=
  Stacks.ChaoticSite.isPointResolution_comp_up _
    (exists_homotopyEquivalences_resolutionMor ε hP hε)

/-- **`Lπ_!(ℱ) = ℱ(P_•, ε)` in `D(Ab)`, functorially in `ℱ` in `Ab(C)`, for a resolution.** Let
`ε : P_• ⟶ B` be an augmentation of a simplicial `A`-algebra whose terms are polynomial algebras
over `A` and which is a trivial Kan fibration of underlying simplicial sets. Then for every
abelian sheaf `ℱ` on the site `C_{B/A}` of Tag 08PR — every abelian presheaf, the topology being
chaotic — the extended Moore complex of `ℱ(P_•, ε)` is `Lπ_!(ℱ)` in the derived category of
abelian groups, naturally in `ℱ`. -/
def resolutionAbelianDerivedLowerShriekIso :
    polynomialMooreCochain A B (resolutionCosimplicialObject ε hP) AddCommGrpCat.{u + 1} ⋙
        DerivedCategory.Q ≅
      HomologicalComplex.single ((polynomialSite A B)ᵒᵖ ⥤ AddCommGrpCat.{u + 1})
          (ComplexShape.up ℤ) 0 ⋙ DerivedCategory.Q ⋙
        polynomialDerivedLowerShriek A B AddCommGrpCat.{u + 1} :=
  have := polynomialColim_hasPointwiseLeftDerivedFunctor A B AddCommGrpCat.{u + 1}
  have := polynomialDerivedLowerShriek_isLeftDerivedFunctor A B AddCommGrpCat.{u + 1}
  have := colim_hasPointwiseLeftDerivedFunctor (AsSmall.{u} (polynomialSite A B))
    AddCommGrpCat.{u + 1}
  have := totalDerivedColimit_isLeftDerivedFunctor (AsSmall.{u} (polynomialSite A B))
    AddCommGrpCat.{u + 1}
  have : ((Functor.whiskeringLeft _ _ AddCommGrpCat.{u + 1}).obj
      (AsSmall.down : AsSmall.{u} (polynomialSite A B) ⥤ _).op).IsEquivalence :=
    (polynomialDiagramAsSmallEquivalence A B AddCommGrpCat.{u + 1}).isEquivalence_functor
  have : (AsSmall.down : AsSmall.{u} (polynomialSite A B) ⥤ _).op.IsEquivalence :=
    (AsSmall.equiv (C := polynomialSite A B)).op.isEquivalence_inverse
  Functor.isoWhiskerLeft ((Functor.whiskeringLeft _ _ AddCommGrpCat.{u + 1}).obj
      (AsSmall.down : AsSmall.{u} (polynomialSite A B) ⥤ _).op)
      (Stacks.ChaoticSite.AbelianValued.mooreCochainNatIsoDerivedColimit _
        (isPointResolution_resolutionCosimplicialObject_comp_up ε hP hε)) ≪≫
    Stacks.Homology.singleLeftDerivedPrecompIso
      ((Functor.whiskeringLeft _ _ AddCommGrpCat.{u + 1}).obj
        (AsSmall.down : AsSmall.{u} (polynomialSite A B) ⥤ _).op)
      (Functor.Final.colimIso (AsSmall.down : AsSmall.{u} (polynomialSite A B) ⥤ _).op)
      (polynomialDerivedLowerShriek A B AddCommGrpCat.{u + 1})
      (polynomialDerivedLowerShriekCounit A B AddCommGrpCat.{u + 1})
      (totalDerivedColimit (AsSmall.{u} (polynomialSite A B)) AddCommGrpCat.{u + 1})
      (totalDerivedColimitCounit (AsSmall.{u} (polynomialSite A B)) AddCommGrpCat.{u + 1})

/-- **`Lπ_!(ℱ) = ℱ(P_•, ε)` in `D(B)`, functorially in `ℱ` in `Mod(B̲)`, for a resolution.** Let
`ε : P_• ⟶ B` be an augmentation of a simplicial `A`-algebra whose terms are polynomial algebras
over `A` and which is a trivial Kan fibration of underlying simplicial sets. Then for every sheaf
of `B̲`-modules `ℱ` on the site `C_{B/A}` of Tag 08PR — every diagram of `B`-modules, the topology
being chaotic — the extended Moore complex of the simplicial `B`-module `ℱ(P_•, ε)` is `Lπ_!(ℱ)`
in the derived category of `B`-modules, naturally in `ℱ`. -/
def resolutionModuleDerivedLowerShriekIso :
    polynomialMooreCochain A B (resolutionCosimplicialObject ε hP)
        (ModuleCat.{u + 1} (ULift.{u + 1} (B : Type u))) ⋙ DerivedCategory.Q ≅
      HomologicalComplex.single
          ((polynomialSite A B)ᵒᵖ ⥤ ModuleCat.{u + 1} (ULift.{u + 1} (B : Type u)))
          (ComplexShape.up ℤ) 0 ⋙ DerivedCategory.Q ⋙
        polynomialDerivedLowerShriek A B (ModuleCat.{u + 1} (ULift.{u + 1} (B : Type u))) :=
  have := polynomialColim_hasPointwiseLeftDerivedFunctor A B
    (ModuleCat.{u + 1} (ULift.{u + 1} (B : Type u)))
  have := polynomialDerivedLowerShriek_isLeftDerivedFunctor A B
    (ModuleCat.{u + 1} (ULift.{u + 1} (B : Type u)))
  have := colim_hasPointwiseLeftDerivedFunctor (AsSmall.{u} (polynomialSite A B))
    (ModuleCat.{u + 1} (ULift.{u + 1} (B : Type u)))
  have := totalDerivedColimit_isLeftDerivedFunctor (AsSmall.{u} (polynomialSite A B))
    (ModuleCat.{u + 1} (ULift.{u + 1} (B : Type u)))
  have : ((Functor.whiskeringLeft _ _ (ModuleCat.{u + 1} (ULift.{u + 1} (B : Type u)))).obj
      (AsSmall.down : AsSmall.{u} (polynomialSite A B) ⥤ _).op).IsEquivalence :=
    (polynomialDiagramAsSmallEquivalence A B
      (ModuleCat.{u + 1} (ULift.{u + 1} (B : Type u)))).isEquivalence_functor
  have : (AsSmall.down : AsSmall.{u} (polynomialSite A B) ⥤ _).op.IsEquivalence :=
    (AsSmall.equiv (C := polynomialSite A B)).op.isEquivalence_inverse
  Functor.isoWhiskerLeft
      ((Functor.whiskeringLeft _ _ (ModuleCat.{u + 1} (ULift.{u + 1} (B : Type u)))).obj
        (AsSmall.down : AsSmall.{u} (polynomialSite A B) ⥤ _).op)
      (Stacks.ChaoticSite.ModuleValued.mooreCochainNatIsoDerivedColimit
        (B := ULift.{u + 1} (B : Type u)) _
        (isPointResolution_resolutionCosimplicialObject_comp_up ε hP hε)) ≪≫
    Stacks.Homology.singleLeftDerivedPrecompIso
      ((Functor.whiskeringLeft _ _ (ModuleCat.{u + 1} (ULift.{u + 1} (B : Type u)))).obj
        (AsSmall.down : AsSmall.{u} (polynomialSite A B) ⥤ _).op)
      (Functor.Final.colimIso (AsSmall.down : AsSmall.{u} (polynomialSite A B) ⥤ _).op)
      (polynomialDerivedLowerShriek A B (ModuleCat.{u + 1} (ULift.{u + 1} (B : Type u))))
      (polynomialDerivedLowerShriekCounit A B (ModuleCat.{u + 1} (ULift.{u + 1} (B : Type u))))
      (totalDerivedColimit (AsSmall.{u} (polynomialSite A B))
        (ModuleCat.{u + 1} (ULift.{u + 1} (B : Type u))))
      (totalDerivedColimitCounit (AsSmall.{u} (polynomialSite A B))
        (ModuleCat.{u + 1} (ULift.{u + 1} (B : Type u))))

end Resolution

/-! ### The standard resolution: Tag 08PT -/

section Standard

/-- **Stacks 08PT, in `D(Ab)`.** Let `A → B` be a ring map and let `ε : P_• → B` be the standard
resolution of `B` over `A`. Let `π` be as in Tag 08PR. Then

`Lπ_!(ℱ) = ℱ(P_•, ε)` in `D(Ab)`, functorially in `ℱ` in `Ab(C)`.

Here `C = C_{B/A}` is the site of Tag 08PR (`CommAlgCat.polynomialSite`), whose topology is chaotic
so that `Ab(C)` is the category of abelian presheaves on it, with coefficients in
`Type (u + 1)`, the universe in which colimits over `C` exist; `Lπ_!` is
`CommAlgCat.polynomialDerivedLowerShriek`; and `ℱ(P_•, ε)` is the extended Moore complex of
the simplicial abelian group obtained by evaluating `ℱ` on the cosimplicial object of `C` given
by the standard resolution. The standard resolution satisfies the hypotheses of Tag 08PS by
Tag 08QI: its terms are polynomial algebras, and its augmentation is a homotopy equivalence of
underlying simplicial sets (Tag 08ND), hence a quasi-isomorphism of associated complexes
(Tag 08P2), hence a trivial Kan fibration (Tag 08P1). -/
@[stacks 08PT "`Lπ_!(ℱ) = ℱ(P_•, ε)` in `D(Ab)` functorially in `ℱ` in `Ab(C)`, on the site \
  `C_{B/A}` of 08PR, with coefficients in the universe above that of `A` and `B`"]
def standardResolutionAbelianDerivedLowerShriekIso :
    polynomialMooreCochain A B
        (resolutionCosimplicialObject (standardResolution.{u, u} A B).hom
          (standardResolution_isResolution.{u, u} A B).isPolynomialAlgebra)
        AddCommGrpCat.{u + 1} ⋙ DerivedCategory.Q ≅
      HomologicalComplex.single ((polynomialSite A B)ᵒᵖ ⥤ AddCommGrpCat.{u + 1})
          (ComplexShape.up ℤ) 0 ⋙ DerivedCategory.Q ⋙
        polynomialDerivedLowerShriek A B AddCommGrpCat.{u + 1} :=
  resolutionAbelianDerivedLowerShriekIso _ _
    (standardResolution_isResolution.{u, u} A B).trivialKanFibration

/-- **Stacks 08PT, in `D(B)`.** Let `A → B` be a ring map and let `ε : P_• → B` be the standard
resolution of `B` over `A`. Let `π` be as in Tag 08PR. Then

`Lπ_!(ℱ) = ℱ(P_•, ε)` in `D(B)`, functorially in `ℱ` in `Mod(B̲)`.

Here `C = C_{B/A}` is the site of Tag 08PR (`CommAlgCat.polynomialSite`), whose topology is chaotic
so that a `B̲`-module is a diagram of `B`-modules on it, with sections in `Type (u + 1)`, the
universe in which colimits over `C` exist, `B` being lifted to that universe as the ring on the
point of `π` is; `Lπ_!` is `CommAlgCat.polynomialDerivedLowerShriek`; and `ℱ(P_•, ε)` is the
extended Moore complex of the simplicial `B`-module obtained by evaluating `ℱ` on the
cosimplicial object of `C` given by the standard resolution. The standard resolution satisfies
the hypotheses of Tag 08PS by Tag 08QI, as recorded at
`CommAlgCat.standardResolutionAbelianDerivedLowerShriekIso`. -/
@[stacks 08PT "`Lπ_!(ℱ) = ℱ(P_•, ε)` in `D(B)` functorially in `ℱ` in `Mod(B̲)`, on the site \
  `C_{B/A}` of 08PR, with module sections in the universe above that of `A` and `B`"]
def standardResolutionModuleDerivedLowerShriekIso :
    polynomialMooreCochain A B
        (resolutionCosimplicialObject (standardResolution.{u, u} A B).hom
          (standardResolution_isResolution.{u, u} A B).isPolynomialAlgebra)
        (ModuleCat.{u + 1} (ULift.{u + 1} (B : Type u))) ⋙ DerivedCategory.Q ≅
      HomologicalComplex.single
          ((polynomialSite A B)ᵒᵖ ⥤ ModuleCat.{u + 1} (ULift.{u + 1} (B : Type u)))
          (ComplexShape.up ℤ) 0 ⋙ DerivedCategory.Q ⋙
        polynomialDerivedLowerShriek A B (ModuleCat.{u + 1} (ULift.{u + 1} (B : Type u))) :=
  resolutionModuleDerivedLowerShriekIso _ _
    (standardResolution_isResolution.{u, u} A B).trivialKanFibration

end Standard

end CommAlgCat
