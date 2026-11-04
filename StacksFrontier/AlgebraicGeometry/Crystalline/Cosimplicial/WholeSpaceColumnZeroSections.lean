module

public import StacksFrontier.Algebra.Homology.RestrictScalarsHomology
public import StacksFrontier.AlgebraicGeometry.CechPushforwardComplex.Basic
public import StacksFrontier.AlgebraicGeometry.Crystalline.Cosimplicial.WholeSpaceCosimplicialModule
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.AffineCosimplicialSystem

/-!
# The column `a = 0` of the double complex of [Stacks, Tag 07LG]

Let `ℱ` be a crystal in quasi-coherent `𝒪_{X/S}`-modules and let
`M(•) : b ↦ M(b) = lim_e Γ((X, T(b)_e, δ(b)), ℱ)` be the cosimplicial module
`wholeSpaceCosimplicialModule` over the completed cosimplicial envelope `D̂(*)`. After the lift to
the universe of the crystalline cohomology, `M(•)` is isomorphic as a cosimplicial abelian group to
`cosimplicialSections`, the cosimplicial module of [Stacks, Proposition 60.20.1, Tag 07JN]. Hence
the cohomology of the Moore complex of the column `a = 0` of the double complex
`K^{a,b} = M(b) ⊗̂_{D(b)} Ω^a_{D(b)}` of [Stacks, Proposition 60.21.3, Tag 07LG] is the cohomology
of the complex `M(0) → M(1) → M(2) → ⋯`, which is `sectionsComplex`.

## Main definitions

* `wholeSpaceSectionsCone`: `M(n)` with its projections, as a cone over the inverse system
  `wholeSpaceSectionSystem` of sections over the levels.
* `wholeSpaceSectionsConeIsLimit`: this cone is a limit cone.
* `wholeSpaceSectionsLimitIso`: the limit of the sections over the levels is `M(n)`.
* `wholeSpaceCarrierSectionsIso`: the isomorphism of cosimplicial abelian groups between `M(•)`,
  lifted, and `cosimplicialSections`.
* `wholeSpaceMooreComplexSectionsIso`: the Moore complex of `M(•)`, lifted, is `sectionsComplex`.
* `wholeSpaceMooreHomologySectionsIso`: the homology of the Moore complex of `M(•)`, lifted, is
  the homology of `sectionsComplex`.
* `wholeSpaceColumnZeroSectionsHomologyIso`: the homology of the Moore complex of the column
  `a = 0`, lifted, is the homology of `sectionsComplex`.

## What this does and does not do to [Stacks, Tag 07LG]

This module is the hypothesis `hcolumn0` of [Stacks, Tag 07LG] for a general crystal, and **no
`@[stacks …]` attribute is placed.** [Stacks, Tag 07LG] is
`...SmallSite.crystalPairDeRhamComplex_computesCohomology` of
`SmallSite/CrystalDeRhamComputesCohomology.lean`. What falls here is one of the hypotheses of the
reduction `...SmallSite.computes07LG_of_doubleComplexSmall_of_edges`, namely `hcolumn0`, for the
cosimplicial module of a general crystal. The others (the double complex `K` itself, the
acyclicity `hcolumns` of the columns, and the rowwise comparison `rowTarget`, `rowComparison`,
`hrows`) are untouched. The hypothesis `hcolumn0` is stated as a consequence of
`...SmallSite.IsCrystalLevelQuotient`, and that antecedent is not used in
`wholeSpaceColumnZeroSectionsHomologyIso`: the crystal property enters the carriers rather than
this comparison, through the `p`-adic completeness of each `M(b)` that
`...SmallSite.wholeSpaceSectionsIsAdicComplete` supplies.

## References

* [Stacks Project, Proposition 60.21.3, Tag 07LG](https://stacks.math.columbia.edu/tag/07LG)
* [Stacks Project, Proposition 60.20.1, Tag 07JN](https://stacks.math.columbia.edu/tag/07JN)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite AlgebraicGeometry Simplicial CategoryTheory.Limits

universe u

namespace Crystalline.GlobalCrystallineSituation.SmallSite

open Crystalline

variable {S : GlobalCrystallineSituation.{u}} (hp : IsNilpotent (S.p : Γ(S.X, ⊤)))
  [WholeSpacePresentation S hp]
  [IsAffine S.X] [IsAffine S.S.scheme] (Fc : QuasiCoherentCrystal S)

/-- The inverse system `e ↦ Γ((X, T(n)_e, δ(n)), ℱ)` of sections over the levels in cosimplicial
degree `n`, whose limit is the degree-`n` term of the cosimplicial module of
[Stacks, Proposition 60.20.1, Tag 07JN]. -/
abbrev wholeSpaceSectionSystem (n : SimplexCategory) : ℕᵒᵖ ⥤ AddCommGrpCat.{u + 1} :=
  (sectionSystem (wholeSpaceSystem S hp) (abelianSheaf Fc.obj).obj).obj n

/-- Every component of the zero element of `M(n)` is zero. -/
@[simp] theorem wholeSpaceSectionsVal_zero {n : SimplexCategory} (e : ℕ) :
    wholeSpaceSectionsVal hp Fc (0 : wholeSpaceSections hp Fc n) e = 0 := rfl

/-- The projection of `M(n)` to the sections over the level `j`, lifted to the universe of the
crystalline cohomology. -/
def wholeSpaceSectionsConeπ (n : SimplexCategory) (j : ℕᵒᵖ) :
    AddCommGrpCat.of (ULift.{u + 1} (wholeSpaceSections hp Fc n)) ⟶
      (wholeSpaceSectionSystem hp Fc n).obj j :=
  AddCommGrpCat.ofHom
    { toFun := fun x ↦ ULift.up (wholeSpaceSectionsVal hp Fc x.down j.unop)
      map_zero' := rfl
      map_add' := fun _ _ ↦ rfl }

/-- `M(n)`, lifted, with its projections `wholeSpaceSectionsConeπ`, as a cone over the inverse
system `wholeSpaceSectionSystem` of sections over the levels. -/
def wholeSpaceSectionsCone (n : SimplexCategory) : Cone (wholeSpaceSectionSystem hp Fc n) where
  pt := AddCommGrpCat.of (ULift.{u + 1} (wholeSpaceSections hp Fc n))
  π :=
    { app := wholeSpaceSectionsConeπ hp Fc n
      naturality := fun _j _j' h ↦ AddCommGrpCat.ext fun x ↦
        ULift.ext _ _ (wholeSpaceSectionsVal_restrict hp Fc x.down h.unop).symm }

/-- The morphism from the point of a cone over `wholeSpaceSectionSystem` to `M(n)` sending an
element to the compatible family of its images under the projections of the cone. -/
def wholeSpaceSectionsConeLift (n : SimplexCategory)
    (s : Cone (wholeSpaceSectionSystem hp Fc n)) :
    s.pt ⟶ (wholeSpaceSectionsCone hp Fc n).pt :=
  AddCommGrpCat.ofHom
    { toFun := fun y ↦ ULift.up (wholeSpaceSectionsMk hp Fc
        (fun e ↦ (s.π.app (op e) y).down)
        (fun {_e _e'} h ↦ congrArg ULift.down
          (congrFun (congrArg (fun g ↦ (ConcreteCategory.hom g : s.pt → _)) (s.w h.op)) y)))
      map_zero' := ULift.ext _ _ (wholeSpaceSectionsVal_injective hp Fc fun e ↦
        congrArg ULift.down (map_zero (ConcreteCategory.hom (s.π.app (op e)))))
      map_add' := fun y z ↦ ULift.ext _ _ (wholeSpaceSectionsVal_injective hp Fc fun e ↦
        congrArg ULift.down (map_add (ConcreteCategory.hom (s.π.app (op e))) y z)) }

/-- The lift of a cone has the components of the cone. -/
theorem wholeSpaceSectionsVal_coneLift (n : SimplexCategory)
    (s : Cone (wholeSpaceSectionSystem hp Fc n)) (y : s.pt) (e : ℕ) :
    wholeSpaceSectionsVal hp Fc
        (ULift.down (ConcreteCategory.hom (wholeSpaceSectionsConeLift hp Fc n s) y)) e =
      ULift.down (ConcreteCategory.hom (s.π.app (op e)) y) := rfl

/-- `M(n)`, with its projections, is the limit of the sections over the levels:
`wholeSpaceSectionsCone` is a limit cone. -/
def wholeSpaceSectionsConeIsLimit (n : SimplexCategory) :
    IsLimit (wholeSpaceSectionsCone hp Fc n) where
  lift := wholeSpaceSectionsConeLift hp Fc n
  fac _ _ := AddCommGrpCat.ext fun _ ↦ rfl
  uniq s m hm := AddCommGrpCat.ext fun y ↦ ULift.ext _ _
    (wholeSpaceSectionsVal_injective hp Fc fun e ↦ by
      rw [wholeSpaceSectionsVal_coneLift]
      exact congrArg ULift.down
        (congrFun (congrArg (fun g ↦ (ConcreteCategory.hom g : s.pt → _)) (hm (op e))) y))

/-- The limit of `wholeSpaceSectionSystem`, the degree-`n` term of the cosimplicial module of
[Stacks, Tag 07JN], is isomorphic to `M(n)`, lifted. -/
def wholeSpaceSectionsLimitIso (n : SimplexCategory) :
    limit (wholeSpaceSectionSystem hp Fc n) ≅
      AddCommGrpCat.of (ULift.{u + 1} (wholeSpaceSections hp Fc n)) :=
  IsLimit.conePointUniqueUpToIso (limit.isLimit _) (wholeSpaceSectionsConeIsLimit hp Fc n)

/-- The degree-`n` component of the isomorphism between `M(•)`, lifted, and
`cosimplicialSections`: the inverse of `wholeSpaceSectionsLimitIso`. -/
def wholeSpaceCarrierSectionsIsoApp (n : SimplexCategory) :
    ((wholeSpaceCosimplicialModule hp Fc).carrierCosimplicialSmall ⋙
        AddCommGrpCat.uliftFunctor.{u + 1, u}).obj n ≅
      (cosimplicialSections (wholeSpaceSystem S hp) (abelianSheaf Fc.obj).obj).obj n :=
  (wholeSpaceSectionsLimitIso hp Fc n).symm

/-- The forward map of `wholeSpaceCarrierSectionsIsoApp` followed by the limit projection to the
level `j` is the projection `wholeSpaceSectionsConeπ` of `M(n)` to that level. -/
theorem wholeSpaceCarrierSectionsIsoApp_hom_π (n : SimplexCategory) (j : ℕᵒᵖ) :
    (wholeSpaceCarrierSectionsIsoApp hp Fc n).hom ≫ limit.π (wholeSpaceSectionSystem hp Fc n) j =
      (wholeSpaceSectionsCone hp Fc n).π.app j :=
  limit.conePointUniqueUpToIso_inv_comp (wholeSpaceSectionsConeIsLimit hp Fc n) j

/-- The components of the identification read from the limit side. -/
theorem wholeSpaceSectionsVal_limitIso_hom (n : SimplexCategory)
    (z : ↑(limit (wholeSpaceSectionSystem hp Fc n))) (e : ℕ) :
    wholeSpaceSectionsVal hp Fc
        (ULift.down (ConcreteCategory.hom (wholeSpaceSectionsLimitIso hp Fc n).hom z)) e =
      ULift.down (ConcreteCategory.hom
        (limit.π (wholeSpaceSectionSystem hp Fc n) (op e)) z) :=
  congrArg ULift.down (ConcreteCategory.congr_hom
    (IsLimit.conePointUniqueUpToIso_hom_comp (limit.isLimit _)
      (wholeSpaceSectionsConeIsLimit hp Fc n) (op e)) z)

/-- The components of the identification read from the side of `M(n)`. -/
theorem wholeSpaceSectionsLimitIso_inv_π (n : SimplexCategory)
    (x : ULift.{u + 1} (wholeSpaceSections hp Fc n)) (e : ℕ) :
    ConcreteCategory.hom (limit.π (wholeSpaceSectionSystem hp Fc n) (op e))
        (ConcreteCategory.hom (wholeSpaceSectionsLimitIso hp Fc n).inv x) =
      ULift.up (wholeSpaceSectionsVal hp Fc x.down e) :=
  ConcreteCategory.congr_hom
    (limit.conePointUniqueUpToIso_inv_comp (wholeSpaceSectionsConeIsLimit hp Fc n) (op e)) x

/-- The cosimplicial map of the limits is the cosimplicial map of the levels. -/
theorem wholeSpaceSectionSystem_limMap_π {m n : SimplexCategory} (φ : m ⟶ n) (j : ℕᵒᵖ)
    (z : ↑(limit (wholeSpaceSectionSystem hp Fc m))) :
    ConcreteCategory.hom (limit.π (wholeSpaceSectionSystem hp Fc n) j)
        (ConcreteCategory.hom
          (limMap ((sectionSystem (wholeSpaceSystem S hp) (abelianSheaf Fc.obj).obj).map φ)) z) =
      ConcreteCategory.hom
        (((sectionSystem (wholeSpaceSystem S hp) (abelianSheaf Fc.obj).obj).map φ).app j)
        (ConcreteCategory.hom (limit.π (wholeSpaceSectionSystem hp Fc m) j) z) :=
  ConcreteCategory.congr_hom
    (limMap_π ((sectionSystem (wholeSpaceSystem S hp) (abelianSheaf Fc.obj).obj).map φ) j) z

/-- The cosimplicial module `M(•)` built from the crystal, lifted to the universe of the
crystalline cohomology, is isomorphic as a cosimplicial abelian group to `cosimplicialSections`,
the cosimplicial module of [Stacks, Proposition 60.20.1, Tag 07JN]. In each degree it is the
inverse of `wholeSpaceSectionsLimitIso`. -/
def wholeSpaceCarrierSectionsIso :
    (wholeSpaceCosimplicialModule hp Fc).carrierCosimplicialSmall ⋙
        AddCommGrpCat.uliftFunctor.{u + 1, u} ≅
      cosimplicialSections (wholeSpaceSystem S hp) (abelianSheaf Fc.obj).obj :=
  NatIso.ofComponents (fun n ↦ wholeSpaceCarrierSectionsIsoApp hp Fc n) (fun {m n} φ ↦ by
    rw [← Iso.eq_comp_inv]
    refine AddCommGrpCat.ext fun x ↦ ULift.ext _ _
      (wholeSpaceSectionsVal_injective hp Fc fun e ↦ ?_)
    change wholeSpaceSectionsVal hp Fc (wholeSpaceSectionsTrans hp Fc φ x.down) e =
      wholeSpaceSectionsVal hp Fc (ULift.down (ConcreteCategory.hom
        (wholeSpaceSectionsLimitIso hp Fc n).hom
          (ConcreteCategory.hom
            (limMap ((sectionSystem (wholeSpaceSystem S hp)
              (abelianSheaf Fc.obj).obj).map φ))
            (ConcreteCategory.hom (wholeSpaceSectionsLimitIso hp Fc m).inv x)))) e
    have hx := wholeSpaceSectionsLimitIso_inv_π hp Fc m x e
    rw [wholeSpaceSectionsVal_limitIso_hom, wholeSpaceSectionSystem_limMap_π, hx]
    rfl)

/-! ### The Moore complex of `M(•)` -/

/-- The composite of two universe lifts of abelian groups is isomorphic to the single lift. -/
def addCommGrpUliftFunctorCompIso :
    AddCommGrpCat.uliftFunctor.{u, u} ⋙ AddCommGrpCat.uliftFunctor.{u + 1, u} ≅
      AddCommGrpCat.uliftFunctor.{u + 1, u} :=
  NatIso.ofComponents
    (fun _ ↦ AddEquiv.toAddCommGrpIso
      { toFun := fun x ↦ ULift.up x.down.down
        invFun := fun x ↦ ULift.up (ULift.up x.down)
        left_inv := fun _ ↦ rfl
        right_inv := fun _ ↦ rfl
        map_add' := fun _ _ ↦ rfl })
    (fun _ ↦ rfl)

/-- The Moore complex of `M(•)`, lifted to the universe of the crystalline cohomology, is
isomorphic to `sectionsComplex`, the complex `M(0) → M(1) → M(2) → ⋯` of
[Stacks, Proposition 60.20.1, Tag 07JN]. -/
def wholeSpaceMooreComplexSectionsIso :
    (AddCommGrpCat.uliftFunctor.{u + 1, u}.mapHomologicalComplex (ComplexShape.up ℕ)).obj
        ((AlgebraicTopology.alternatingCofaceMapComplex AddCommGrpCat.{u}).obj
          (wholeSpaceCosimplicialModule hp Fc).carrierCosimplicial) ≅
      sectionsComplex (wholeSpaceSystem S hp) (abelianSheaf Fc.obj).obj :=
  (Stacks.CechPushforward.alternatingCofaceMapComplexCompMapHomologicalComplexIso
      AddCommGrpCat.uliftFunctor.{u + 1, u}).app
        (wholeSpaceCosimplicialModule hp Fc).carrierCosimplicial ≪≫
    (AlgebraicTopology.alternatingCofaceMapComplex AddCommGrpCat.{u + 1}).mapIso
      (Functor.isoWhiskerLeft
          (wholeSpaceCosimplicialModule hp Fc).carrierCosimplicialSmall
          addCommGrpUliftFunctorCompIso ≪≫
        wholeSpaceCarrierSectionsIso hp Fc)

/-- The universe lift of the `j`-th homology of the Moore complex of `M(•)` is isomorphic to the
`j`-th homology of `sectionsComplex`, the complex `M(0) → M(1) → M(2) → ⋯` of
[Stacks, Proposition 60.20.1, Tag 07JN]. -/
def wholeSpaceMooreHomologySectionsIso (j : ℕ) :
    AddCommGrpCat.uliftFunctor.{u + 1, u}.obj
        (((AlgebraicTopology.alternatingCofaceMapComplex AddCommGrpCat.{u}).obj
          (wholeSpaceCosimplicialModule hp Fc).carrierCosimplicial).homology j) ≅
      (sectionsComplex (wholeSpaceSystem S hp) (abelianSheaf Fc.obj).obj).homology j :=
  (Stacks.Homology.RestrictScalars.mapHomologicalComplexHomologyIso
      AddCommGrpCat.uliftFunctor.{u + 1, u}
      ((AlgebraicTopology.alternatingCofaceMapComplex AddCommGrpCat.{u}).obj
        (wholeSpaceCosimplicialModule hp Fc).carrierCosimplicial) j).symm ≪≫
    (HomologicalComplex.homologyFunctor AddCommGrpCat.{u + 1} (ComplexShape.up ℕ) j).mapIso
      (wholeSpaceMooreComplexSectionsIso hp Fc)

/-- For every crystal in quasi-coherent `𝒪_{X/S}`-modules, the universe lift of the `j`-th
cohomology of the Moore complex of the column `a = 0` of the double complex
`K^{a,b} = M(b) ⊗̂_{D(b)} Ω^a_{D(b)}` of [Stacks, Proposition 60.21.3, Tag 07LG] is isomorphic to
the `j`-th cohomology of `sectionsComplex`, the complex `M(0) → M(1) → M(2) → ⋯` of
[Stacks, Proposition 60.20.1, Tag 07JN]. -/
def wholeSpaceColumnZeroSectionsHomologyIso (j : ℕ) :
    AddCommGrpCat.uliftFunctor.{u + 1, u}.obj
        (((AlgebraicTopology.alternatingCofaceMapComplex AddCommGrpCat.{u}).obj
          ((wholeSpaceCosimplicialModule hp Fc).column 0)).homology j) ≅
      (sectionsComplex (wholeSpaceSystem S hp) (abelianSheaf Fc.obj).obj).homology j :=
  AddCommGrpCat.uliftFunctor.{u + 1, u}.mapIso
      (wholeSpaceMooreHomologyColumnZeroIso hp Fc j) ≪≫
    wholeSpaceMooreHomologySectionsIso hp Fc j

end Crystalline.GlobalCrystallineSituation.SmallSite

end
