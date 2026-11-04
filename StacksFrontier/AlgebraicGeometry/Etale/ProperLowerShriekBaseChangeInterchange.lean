module

public import StacksFrontier.AlgebraicGeometry.Etale.ProperLowerShriekBaseChangeHorizontal

import StacksCore.Tactic.StacksAttribute

/-!
# Interchange of the base change maps `l_! ∘ Rf'_* ⟶ Rf_* ∘ k_!` in a three-by-three diagram

Consider a commutative diagram of a big étale site
```
X'' --k'--> X' --k--> X
 |          |         |
 f''        f'        f
 v          v         v
Y'' --l'--> Y' --l--> Y
 |          |         |
 g''        g'        g
 v          v         v
Z'' --m'--> Z' --m--> Z
```
with proper vertical arrows and separated, locally quasi-finite horizontal arrows, with squares
```
A B
C D
```
and write `γ_A, γ_B, γ_C, γ_D` for the maps of [Stacks, Tag 0F7B] of the four squares
(`AlgebraicGeometry.SmallEtale.properBaseChangeMap`). There are a priori two transformations
`m_! ∘ m'_! ∘ Rg''_* ∘ Rf''_* ⟶ Rg_* ∘ Rf_* ∘ k_! ∘ k'_!`, namely
`γ_B ∘ γ_D ∘ γ_A ∘ γ_C = γ_{B+D} ∘ γ_{A+C}` and `γ_B ∘ γ_A ∘ γ_D ∘ γ_C = γ_{A+B} ∘ γ_{C+D}`
(the identifications with the maps of the rectangles being [Stacks, Tag 0F7C] and
[Stacks, Tag 0F7D]). [Stacks, Tag 0F7E] observes that they are equal.

## Main results

* `AlgebraicGeometry.SmallEtale.properBaseChangeMap_interchange`: the two composites of the
  four square maps agree; this is the naturality of `γ_D` applied to `γ_A`, the squares `A` and
  `D` meeting in a single point.
* `AlgebraicGeometry.SmallEtale.properBaseChangeMap_rectangle_interchange`: the two composites
  `γ_{B+D} ∘ γ_{A+C}` and `γ_{A+B} ∘ γ_{C+D}` of the maps of the rectangles agree, after
  `R(g ∘ f)_* = Rg_* ∘ Rf_*` and `(l ∘ l')_! = l_! ∘ l'_!`.

## References

* [Stacks Project, Tag 0F7E](https://stacks.math.columbia.edu/tag/0F7E)
* [Stacks Project, Tag 0F7B](https://stacks.math.columbia.edu/tag/0F7B)
* [Stacks Project, Tag 0F7C](https://stacks.math.columbia.edu/tag/0F7C)
* [Stacks Project, Tag 0F7D](https://stacks.math.columbia.edu/tag/0F7D)
* [Stacks Project, Tag 003F](https://stacks.math.columbia.edu/tag/003F)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w u

namespace AlgebraicGeometry.SmallEtale

open Stacks.DerivedBaseChange

variable (B : BigEtaleSite.{u}) (Λ : Type u) [Ring Λ]
  {X'' X' X Y'' Y' Y Z'' Z' Z : B.Scheme}

/-- **[Stacks, Tag 0F7E], for the maps of the four squares.** Consider a commutative diagram of a
big étale site
```
X'' --k'--> X' --k--> X
 |          |         |
 f''        f'        f
 v          v         v
Y'' --l'--> Y' --l--> Y
 |          |         |
 g''        g'        g
 v          v         v
Z'' --m'--> Z' --m--> Z
```
whose vertical arrows are proper and whose horizontal arrows are separated and locally
quasi-finite, label its squares `A B / C D`, and let `Λ` be a ring. With `γ_A, γ_B, γ_C, γ_D`
the maps of [Stacks, Tag 0F7B] for the squares
(`γ_A : l'_! ∘ Rf''_* ⟶ Rf'_* ∘ k'_!`, `γ_B : l_! ∘ Rf'_* ⟶ Rf_* ∘ k_!`,
`γ_C : m'_! ∘ Rg''_* ⟶ Rg'_* ∘ l'_!`, `γ_D : m_! ∘ Rg'_* ⟶ Rg_* ∘ l_!`), the two transformations
`m_! ∘ m'_! ∘ Rg''_* ∘ Rf''_* ⟶ Rg_* ∘ Rf_* ∘ k_! ∘ k'_!`
```
γ_B ∘ γ_D ∘ γ_A ∘ γ_C   and   γ_B ∘ γ_A ∘ γ_D ∘ γ_C
```
(composites of whiskerings, as in Categories, Section 003D) agree, here at every object `K` of
`D(X''_étale, Λ)`. The squares `A` and `D` meet in a single point, and the identity is the
naturality of `γ_D` with respect to `γ_A` (Categories, Lemma 003F). It holds for every choice of
the six right derived functors of the direct images. -/
@[stacks 0F7E "the two composites of the maps of the four squares"]
theorem properBaseChangeMap_interchange
    (k' : X'' ⟶ X') (k : X' ⟶ X) (l' : Y'' ⟶ Y') (l : Y' ⟶ Y) (m' : Z'' ⟶ Z') (m : Z' ⟶ Z)
    (f'' : X'' ⟶ Y'') (f' : X' ⟶ Y') (f : X ⟶ Y)
    (g'' : Y'' ⟶ Z'') (g' : Y' ⟶ Z') (g : Y ⟶ Z)
    (wA : k' ≫ f' = f'' ≫ l') (wB : k ≫ f = f' ≫ l)
    (wC : l' ≫ g' = g'' ≫ m') (wD : l ≫ g = g' ≫ m)
    [IsProper (B.inclusion.map f'')] [IsProper (B.inclusion.map f')]
    [IsProper (B.inclusion.map f)]
    [IsProper (B.inclusion.map g'')] [IsProper (B.inclusion.map g')]
    [IsProper (B.inclusion.map g)]
    [IsSeparated (B.inclusion.map k')] [LocallyQuasiFinite (B.inclusion.map k')]
    [LocallyOfFiniteType (B.inclusion.map k')]
    [IsSeparated (B.inclusion.map k)] [LocallyQuasiFinite (B.inclusion.map k)]
    [LocallyOfFiniteType (B.inclusion.map k)]
    [IsSeparated (B.inclusion.map l')] [LocallyQuasiFinite (B.inclusion.map l')]
    [LocallyOfFiniteType (B.inclusion.map l')]
    [IsSeparated (B.inclusion.map l)] [LocallyQuasiFinite (B.inclusion.map l)]
    [LocallyOfFiniteType (B.inclusion.map l)]
    [IsSeparated (B.inclusion.map m')] [LocallyQuasiFinite (B.inclusion.map m')]
    [LocallyOfFiniteType (B.inclusion.map m')]
    [IsSeparated (B.inclusion.map m)] [LocallyQuasiFinite (B.inclusion.map m)]
    [LocallyOfFiniteType (B.inclusion.map m)]
    [HasDerivedCategory.{w} (ModuleSheaf.{u, u, u} B X'' Λ)]
    [HasDerivedCategory.{w} (ModuleSheaf.{u, u, u} B X' Λ)]
    [HasDerivedCategory.{w} (ModuleSheaf.{u, u, u} B X Λ)]
    [HasDerivedCategory.{w} (ModuleSheaf.{u, u, u} B Y'' Λ)]
    [HasDerivedCategory.{w} (ModuleSheaf.{u, u, u} B Y' Λ)]
    [HasDerivedCategory.{w} (ModuleSheaf.{u, u, u} B Y Λ)]
    [HasDerivedCategory.{w} (ModuleSheaf.{u, u, u} B Z'' Λ)]
    [HasDerivedCategory.{w} (ModuleSheaf.{u, u, u} B Z' Λ)]
    [HasDerivedCategory.{w} (ModuleSheaf.{u, u, u} B Z Λ)]
    (RF'' : DerivedCategory (ModuleSheaf.{u, u, u} B X'' Λ) ⥤
      DerivedCategory (ModuleSheaf.{u, u, u} B Y'' Λ))
    (αF'' : (etaleModuleLift B Λ (etalePushforward.{u, u + 1} B f'')).mapHomotopyCategory
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RF'')
    (RF' : DerivedCategory (ModuleSheaf.{u, u, u} B X' Λ) ⥤
      DerivedCategory (ModuleSheaf.{u, u, u} B Y' Λ))
    (αF' : (etaleModuleLift B Λ (etalePushforward.{u, u + 1} B f')).mapHomotopyCategory
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RF')
    (RF : DerivedCategory (ModuleSheaf.{u, u, u} B X Λ) ⥤
      DerivedCategory (ModuleSheaf.{u, u, u} B Y Λ))
    (αF : (etaleModuleLift B Λ (etalePushforward.{u, u + 1} B f)).mapHomotopyCategory
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RF)
    (RG'' : DerivedCategory (ModuleSheaf.{u, u, u} B Y'' Λ) ⥤
      DerivedCategory (ModuleSheaf.{u, u, u} B Z'' Λ))
    (αG'' : (etaleModuleLift B Λ (etalePushforward.{u, u + 1} B g'')).mapHomotopyCategory
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RG'')
    (RG' : DerivedCategory (ModuleSheaf.{u, u, u} B Y' Λ) ⥤
      DerivedCategory (ModuleSheaf.{u, u, u} B Z' Λ))
    (αG' : (etaleModuleLift B Λ (etalePushforward.{u, u + 1} B g')).mapHomotopyCategory
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RG')
    (RG : DerivedCategory (ModuleSheaf.{u, u, u} B Y Λ) ⥤
      DerivedCategory (ModuleSheaf.{u, u, u} B Z Λ))
    (αG : (etaleModuleLift B Λ (etalePushforward.{u, u + 1} B g)).mapHomotopyCategory
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RG)
    [RF''.IsRightDerivedFunctor αF''
      (HomotopyCategory.quasiIso (ModuleSheaf.{u, u, u} B X'' Λ) (ComplexShape.up ℤ))]
    [RF'.IsRightDerivedFunctor αF'
      (HomotopyCategory.quasiIso (ModuleSheaf.{u, u, u} B X' Λ) (ComplexShape.up ℤ))]
    [RG''.IsRightDerivedFunctor αG''
      (HomotopyCategory.quasiIso (ModuleSheaf.{u, u, u} B Y'' Λ) (ComplexShape.up ℤ))]
    [RG'.IsRightDerivedFunctor αG'
      (HomotopyCategory.quasiIso (ModuleSheaf.{u, u, u} B Y' Λ) (ComplexShape.up ℤ))]
    (K : DerivedCategory (ModuleSheaf.{u, u, u} B X'' Λ)) :
    (etaleModuleLift B Λ (fShriekFunctor.{u, u} B m)).mapDerivedCategory.map
        ((properBaseChangeMap B Λ l' g'' g' m' wC RG'' αG'' RG' αG').app (RF''.obj K)) ≫
      (etaleModuleLift B Λ (fShriekFunctor.{u, u} B m)).mapDerivedCategory.map
        (RG'.map ((properBaseChangeMap B Λ k' f'' f' l' wA RF'' αF'' RF' αF').app K)) ≫
      (properBaseChangeMap B Λ l g' g m wD RG' αG' RG αG).app
        (RF'.obj ((etaleModuleLift B Λ (fShriekFunctor.{u, u} B k')).mapDerivedCategory.obj K)) ≫
      RG.map ((properBaseChangeMap B Λ k f' f l wB RF' αF' RF αF).app
        ((etaleModuleLift B Λ (fShriekFunctor.{u, u} B k')).mapDerivedCategory.obj K)) =
    (etaleModuleLift B Λ (fShriekFunctor.{u, u} B m)).mapDerivedCategory.map
        ((properBaseChangeMap B Λ l' g'' g' m' wC RG'' αG'' RG' αG').app (RF''.obj K)) ≫
      (properBaseChangeMap B Λ l g' g m wD RG' αG' RG αG).app
        ((etaleModuleLift B Λ (fShriekFunctor.{u, u} B l')).mapDerivedCategory.obj
          (RF''.obj K)) ≫
      RG.map ((etaleModuleLift B Λ (fShriekFunctor.{u, u} B l)).mapDerivedCategory.map
        ((properBaseChangeMap B Λ k' f'' f' l' wA RF'' αF'' RF' αF').app K)) ≫
      RG.map ((properBaseChangeMap B Λ k f' f l wB RF' αF' RF αF).app
        ((etaleModuleLift B Λ (fShriekFunctor.{u, u} B k')).mapDerivedCategory.obj K)) := by
  have h := (properBaseChangeMap B Λ l g' g m wD RG' αG' RG αG).naturality
    ((properBaseChangeMap B Λ k' f'' f' l' wA RF'' αF'' RF' αF').app K)
  simp only [Functor.comp_map] at h
  rw [reassoc_of% h]

/-- **[Stacks, Tag 0F7E], for the maps of the rectangles.** In the situation of
`AlgebraicGeometry.SmallEtale.properBaseChangeMap_interchange`, consider moreover right derived
functors `R(g'' ∘ f'')_*`, `R(g' ∘ f')_*`, `R(g ∘ f)_*` of the direct images along the vertical
composites, and the maps of [Stacks, Tag 0F7B] for the four rectangles
```
γ_{A+B} : (l ∘ l')_! ∘ Rf''_* ⟶ Rf_* ∘ (k ∘ k')_!
γ_{C+D} : (m ∘ m')_! ∘ Rg''_* ⟶ Rg_* ∘ (l ∘ l')_!
γ_{A+C} : m'_! ∘ R(g'' ∘ f'')_* ⟶ R(g' ∘ f')_* ∘ k'_!
γ_{B+D} : m_! ∘ R(g' ∘ f')_* ⟶ R(g ∘ f)_* ∘ k_!
```
written, as the source does, through `R(g ∘ f)_* = Rg_* ∘ Rf_*` (the canonical comparisons of
[Stacks, Tag 05T2], isomorphisms by
`AlgebraicGeometry.SmallEtale.isIso_compComparison_etalePushforwardMod`) and
`(l ∘ l')_! = l_! ∘ l'_!` (Stacks 0F50,
`AlgebraicGeometry.SmallEtale.etaleModuleLiftFShriekCompIso`, on derived categories by
`CategoryTheory.Functor.mapDerivedCategoryCompIso`). Then the two transformations
`m_! ∘ m'_! ∘ Rg''_* ∘ Rf''_* ⟶ Rg_* ∘ Rf_* ∘ k_! ∘ k'_!`
```
γ_{B+D} ∘ γ_{A+C}   and   γ_{A+B} ∘ γ_{C+D}
```
agree, here at every object `K` of `D(X''_étale, Λ)`. By [Stacks, Tag 0F7C]
(`AlgebraicGeometry.SmallEtale.properBaseChangeMap_rectangle_eq_comp`) and [Stacks, Tag 0F7D]
(`AlgebraicGeometry.SmallEtale.properBaseChangeMap_horizontal_paste`) these are
`γ_B ∘ γ_D ∘ γ_A ∘ γ_C` and `γ_B ∘ γ_A ∘ γ_D ∘ γ_C`, which agree by
`AlgebraicGeometry.SmallEtale.properBaseChangeMap_interchange`. It holds for every choice of the
nine right derived functors. -/
@[stacks 0F7E "the two composites of the maps of the rectangles"]
theorem properBaseChangeMap_rectangle_interchange
    (k' : X'' ⟶ X') (k : X' ⟶ X) (l' : Y'' ⟶ Y') (l : Y' ⟶ Y) (m' : Z'' ⟶ Z') (m : Z' ⟶ Z)
    (f'' : X'' ⟶ Y'') (f' : X' ⟶ Y') (f : X ⟶ Y)
    (g'' : Y'' ⟶ Z'') (g' : Y' ⟶ Z') (g : Y ⟶ Z)
    (wA : k' ≫ f' = f'' ≫ l') (wB : k ≫ f = f' ≫ l)
    (wC : l' ≫ g' = g'' ≫ m') (wD : l ≫ g = g' ≫ m)
    [IsProper (B.inclusion.map f'')] [IsProper (B.inclusion.map f')]
    [IsProper (B.inclusion.map f)]
    [IsProper (B.inclusion.map g'')] [IsProper (B.inclusion.map g')]
    [IsProper (B.inclusion.map g)]
    [IsSeparated (B.inclusion.map k')] [LocallyQuasiFinite (B.inclusion.map k')]
    [LocallyOfFiniteType (B.inclusion.map k')]
    [IsSeparated (B.inclusion.map k)] [LocallyQuasiFinite (B.inclusion.map k)]
    [LocallyOfFiniteType (B.inclusion.map k)]
    [IsSeparated (B.inclusion.map l')] [LocallyQuasiFinite (B.inclusion.map l')]
    [LocallyOfFiniteType (B.inclusion.map l')]
    [IsSeparated (B.inclusion.map l)] [LocallyQuasiFinite (B.inclusion.map l)]
    [LocallyOfFiniteType (B.inclusion.map l)]
    [IsSeparated (B.inclusion.map m')] [LocallyQuasiFinite (B.inclusion.map m')]
    [LocallyOfFiniteType (B.inclusion.map m')]
    [IsSeparated (B.inclusion.map m)] [LocallyQuasiFinite (B.inclusion.map m)]
    [LocallyOfFiniteType (B.inclusion.map m)]
    [HasDerivedCategory.{w} (ModuleSheaf.{u, u, u} B X'' Λ)]
    [HasDerivedCategory.{w} (ModuleSheaf.{u, u, u} B X' Λ)]
    [HasDerivedCategory.{w} (ModuleSheaf.{u, u, u} B X Λ)]
    [HasDerivedCategory.{w} (ModuleSheaf.{u, u, u} B Y'' Λ)]
    [HasDerivedCategory.{w} (ModuleSheaf.{u, u, u} B Y' Λ)]
    [HasDerivedCategory.{w} (ModuleSheaf.{u, u, u} B Y Λ)]
    [HasDerivedCategory.{w} (ModuleSheaf.{u, u, u} B Z'' Λ)]
    [HasDerivedCategory.{w} (ModuleSheaf.{u, u, u} B Z' Λ)]
    [HasDerivedCategory.{w} (ModuleSheaf.{u, u, u} B Z Λ)]
    (RF'' : DerivedCategory (ModuleSheaf.{u, u, u} B X'' Λ) ⥤
      DerivedCategory (ModuleSheaf.{u, u, u} B Y'' Λ))
    (αF'' : (etaleModuleLift B Λ (etalePushforward.{u, u + 1} B f'')).mapHomotopyCategory
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RF'')
    (RF' : DerivedCategory (ModuleSheaf.{u, u, u} B X' Λ) ⥤
      DerivedCategory (ModuleSheaf.{u, u, u} B Y' Λ))
    (αF' : (etaleModuleLift B Λ (etalePushforward.{u, u + 1} B f')).mapHomotopyCategory
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RF')
    (RF : DerivedCategory (ModuleSheaf.{u, u, u} B X Λ) ⥤
      DerivedCategory (ModuleSheaf.{u, u, u} B Y Λ))
    (αF : (etaleModuleLift B Λ (etalePushforward.{u, u + 1} B f)).mapHomotopyCategory
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RF)
    (RG'' : DerivedCategory (ModuleSheaf.{u, u, u} B Y'' Λ) ⥤
      DerivedCategory (ModuleSheaf.{u, u, u} B Z'' Λ))
    (αG'' : (etaleModuleLift B Λ (etalePushforward.{u, u + 1} B g'')).mapHomotopyCategory
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RG'')
    (RG' : DerivedCategory (ModuleSheaf.{u, u, u} B Y' Λ) ⥤
      DerivedCategory (ModuleSheaf.{u, u, u} B Z' Λ))
    (αG' : (etaleModuleLift B Λ (etalePushforward.{u, u + 1} B g')).mapHomotopyCategory
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RG')
    (RG : DerivedCategory (ModuleSheaf.{u, u, u} B Y Λ) ⥤
      DerivedCategory (ModuleSheaf.{u, u, u} B Z Λ))
    (αG : (etaleModuleLift B Λ (etalePushforward.{u, u + 1} B g)).mapHomotopyCategory
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RG)
    (RP'' : DerivedCategory (ModuleSheaf.{u, u, u} B X'' Λ) ⥤
      DerivedCategory (ModuleSheaf.{u, u, u} B Z'' Λ))
    (αP'' : (etaleModuleLift B Λ (etalePushforward.{u, u + 1} B (f'' ≫ g''))).mapHomotopyCategory
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RP'')
    (RP' : DerivedCategory (ModuleSheaf.{u, u, u} B X' Λ) ⥤
      DerivedCategory (ModuleSheaf.{u, u, u} B Z' Λ))
    (αP' : (etaleModuleLift B Λ (etalePushforward.{u, u + 1} B (f' ≫ g'))).mapHomotopyCategory
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RP')
    (RP : DerivedCategory (ModuleSheaf.{u, u, u} B X Λ) ⥤
      DerivedCategory (ModuleSheaf.{u, u, u} B Z Λ))
    (αP : (etaleModuleLift B Λ (etalePushforward.{u, u + 1} B (f ≫ g))).mapHomotopyCategory
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RP)
    [RF''.IsRightDerivedFunctor αF''
      (HomotopyCategory.quasiIso (ModuleSheaf.{u, u, u} B X'' Λ) (ComplexShape.up ℤ))]
    [RF'.IsRightDerivedFunctor αF'
      (HomotopyCategory.quasiIso (ModuleSheaf.{u, u, u} B X' Λ) (ComplexShape.up ℤ))]
    [RG''.IsRightDerivedFunctor αG''
      (HomotopyCategory.quasiIso (ModuleSheaf.{u, u, u} B Y'' Λ) (ComplexShape.up ℤ))]
    [RG'.IsRightDerivedFunctor αG'
      (HomotopyCategory.quasiIso (ModuleSheaf.{u, u, u} B Y' Λ) (ComplexShape.up ℤ))]
    [RF.IsRightDerivedFunctor αF
      (HomotopyCategory.quasiIso (ModuleSheaf.{u, u, u} B X Λ) (ComplexShape.up ℤ))]
    [RG.IsRightDerivedFunctor αG
      (HomotopyCategory.quasiIso (ModuleSheaf.{u, u, u} B Y Λ) (ComplexShape.up ℤ))]
    [RP''.IsRightDerivedFunctor αP''
      (HomotopyCategory.quasiIso (ModuleSheaf.{u, u, u} B X'' Λ) (ComplexShape.up ℤ))]
    [RP'.IsRightDerivedFunctor αP'
      (HomotopyCategory.quasiIso (ModuleSheaf.{u, u, u} B X' Λ) (ComplexShape.up ℤ))]
    [RP.IsRightDerivedFunctor αP
      (HomotopyCategory.quasiIso (ModuleSheaf.{u, u, u} B X Λ) (ComplexShape.up ℤ))]
    (K : DerivedCategory (ModuleSheaf.{u, u, u} B X'' Λ)) :
    haveI := isIso_compComparison_etalePushforwardMod B Λ f'' g'' αF'' αG'' αP''
    haveI := isIso_compComparison_etalePushforwardMod B Λ f' g' αF' αG' αP'
    (etaleModuleLift B Λ (fShriekFunctor.{u, u} B m)).mapDerivedCategory.map
        ((Functor.whiskerRight (inv (compComparison
            (HomotopyCategory.quasiIso (ModuleSheaf.{u, u, u} B X'' Λ) (ComplexShape.up ℤ))
            αF'' αG'' αP'' (Functor.mapHomotopyCategoryCompIso
              (etalePushforwardModCompIso B Λ f'' g'') (ComplexShape.up ℤ))))
            (etaleModuleLift B Λ (fShriekFunctor.{u, u} B m')).mapDerivedCategory ≫
          properBaseChangeMap B Λ k' (f'' ≫ g'') (f' ≫ g') m' (rectangle_comm B wA wC)
            RP'' αP'' RP' αP' ≫
          Functor.whiskerLeft (etaleModuleLift B Λ (fShriekFunctor.{u, u} B k')).mapDerivedCategory
            (compComparison
              (HomotopyCategory.quasiIso (ModuleSheaf.{u, u, u} B X' Λ) (ComplexShape.up ℤ))
              αF' αG' αP' (Functor.mapHomotopyCategoryCompIso
                (etalePushforwardModCompIso B Λ f' g') (ComplexShape.up ℤ)))).app K) ≫
      (Functor.whiskerRight (inv (compComparison
            (HomotopyCategory.quasiIso (ModuleSheaf.{u, u, u} B X' Λ) (ComplexShape.up ℤ))
            αF' αG' αP' (Functor.mapHomotopyCategoryCompIso
              (etalePushforwardModCompIso B Λ f' g') (ComplexShape.up ℤ))))
            (etaleModuleLift B Λ (fShriekFunctor.{u, u} B m)).mapDerivedCategory ≫
          properBaseChangeMap B Λ k (f' ≫ g') (f ≫ g) m (rectangle_comm B wB wD)
            RP' αP' RP αP ≫
          Functor.whiskerLeft (etaleModuleLift B Λ (fShriekFunctor.{u, u} B k)).mapDerivedCategory
            (compComparison
              (HomotopyCategory.quasiIso (ModuleSheaf.{u, u, u} B X Λ) (ComplexShape.up ℤ))
              αF αG αP (Functor.mapHomotopyCategoryCompIso
                (etalePushforwardModCompIso B Λ f g) (ComplexShape.up ℤ)))).app
        ((etaleModuleLift B Λ (fShriekFunctor.{u, u} B k')).mapDerivedCategory.obj K) =
    (Functor.whiskerLeft RG'' (Functor.mapDerivedCategoryCompIso
            (etaleModuleLiftFShriekCompIso B Λ m' m (m' ≫ m) rfl)).hom ≫
          properBaseChangeMap B Λ (l' ≫ l) g'' g (m' ≫ m) (rectangle_comm_horizontal B wC wD)
            RG'' αG'' RG αG ≫
          Functor.whiskerRight (Functor.mapDerivedCategoryCompIso
            (etaleModuleLiftFShriekCompIso B Λ l' l (l' ≫ l) rfl)).inv RG).app (RF''.obj K) ≫
      RG.map ((Functor.whiskerLeft RF'' (Functor.mapDerivedCategoryCompIso
            (etaleModuleLiftFShriekCompIso B Λ l' l (l' ≫ l) rfl)).hom ≫
          properBaseChangeMap B Λ (k' ≫ k) f'' f (l' ≫ l) (rectangle_comm_horizontal B wA wB)
            RF'' αF'' RF αF ≫
          Functor.whiskerRight (Functor.mapDerivedCategoryCompIso
            (etaleModuleLiftFShriekCompIso B Λ k' k (k' ≫ k) rfl)).inv RF).app K) := by
  rw [properBaseChangeMap_rectangle_eq_comp B Λ k' f'' f' l' g'' g' m' wA wC RF'' αF'' RF' αF'
      RG'' αG'' RG' αG' RP'' αP'' RP' αP',
    properBaseChangeMap_rectangle_eq_comp B Λ k f' f l g' g m wB wD RF' αF' RF αF
      RG' αG' RG αG RP' αP' RP αP,
    properBaseChangeMap_horizontal_paste B Λ l' l g'' g' g m' m wC wD RG'' αG'' RG' αG' RG αG,
    properBaseChangeMap_horizontal_paste B Λ k' k f'' f' f l' l wA wB RF'' αF'' RF' αF' RF αF]
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp, Category.comp_id,
    Category.assoc, Iso.hom_inv_id_app_assoc, CategoryTheory.Functor.map_comp]
  rw [← Functor.map_comp_assoc RG ((Functor.mapDerivedCategoryCompIso
      (etaleModuleLiftFShriekCompIso B Λ l' l (l' ≫ l) rfl)).hom.app (RF''.obj K)),
    Iso.hom_inv_id_app, CategoryTheory.Functor.map_id, Category.id_comp,
    ← Functor.map_comp RG (RF.map ((Functor.mapDerivedCategoryCompIso
      (etaleModuleLiftFShriekCompIso B Λ k' k (k' ≫ k) rfl)).hom.app K)),
    ← Functor.map_comp RF, Iso.hom_inv_id_app, CategoryTheory.Functor.map_id,
    CategoryTheory.Functor.map_id]
  simpa only [Functor.comp_obj, Category.comp_id] using
    properBaseChangeMap_interchange B Λ k' k l' l m' m f'' f' f g'' g' g wA wB wC wD
      RF'' αF'' RF' αF' RF αF RG'' αG'' RG' αG' RG αG K

end AlgebraicGeometry.SmallEtale

end
