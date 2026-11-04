module

public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.EdgeCompatPreimageRestrict
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.LerayOpenSubschemeDerived
public import StacksFrontier.Homology.DerivedCategory.MapHomologyIso

/-!
# Factor (2) of the base-change comparison: the comparison of the two models of `Rg_*` carried across

Factor (2) of the `ψ` side's [Stacks, Tag 089W], as
`Stacks.Cohomology.AffineComparison.cohomologyIsoPushforward_inv_eq_lerayComparison` prints it, is
the degree-`n` cohomology of `Stacks.Cohomology.DerivedSectionsLeray.derivedSectionsOverOpen` of
the open subscheme `f⁻¹V` at `⊤`, applied to a comparison `c` of the two models of `Rg_*`. The
first leading factor of the other side of the match is `(derivedPreimageSections f V).map c` — the **same** comparison read
in the ambient model, as derived sections over `f⁻¹V` of `X` over `Γ(S, V)`. This file carries the
one into the other.

The passage is **naturality and nothing else**: the comparison is carried across the derived
open-subscheme crossing `…TopDegreeBaseChange.openSubschemeSectionsComparison` and across the
model comparison `Stacks.EdgeCompat.preimageSectionsModelComparison (f ∣_ V) ⊤`, and each of the
two restrictions of scalars the open-subscheme reading carries contributes only a conjugation by
`StacksDraft.DerivedCategoryHomology.mapDerivedCategoryHomologyIso`. No new transformation is
built, nothing is inverted, and no `rightDerivedDesc` is taken.

## Main results

* `…TopDegreeBaseChange.homologyFunctor_map_derivedPreimageSections_map_comp_eq` — **factor (2)'s
  match.** For a morphism of schemes `f : X ⟶ S`, an open `V ⊆ S`, a degree `n` and an arbitrary
  morphism `c : K ⟶ L` of `D(𝒪_X)`,

  > the degree-`n` cohomology of `(derivedPreimageSections f V).map c`, then of the
  > open-subscheme crossing at `L`, then of the model comparison at `L` under the restriction of
  > scalars along `AlgebraicGeometry.Scheme.Opens.topIso`

  is

  > the same two crossings at `K`, then the restriction of scalars along `topIso` applied — past
  > `Hⁿ` — to the restriction of scalars along `(f ∣_ V)^♯` applied to the degree-`n` cohomology
  > of `derivedSectionsOverOpen (f⁻¹V : Scheme) ((opensMap (f ∣_ V)).obj ⊤)` at the restriction
  > of `c`, which is factor (2) itself.

  **Nothing is assumed** of `f`, of `V`, of `c` or of `n` — no affineness, no quasi-compactness,
  no quasi-separatedness, no boundedness and no quasi-coherence.

## Implementation notes

*Both halves are one general brick each.* `StacksDraft.DerivedCategoryHomology`
`.homologyFunctor_map_comp_eq_of_square` reads a commuting square whose vertical edges are an exact
functor on derived categories in degree `n`; it is applied once, at the restriction of scalars
along `topIso`, with the square supplied by the two crossings' own naturality. The inner layer is
`…DerivedCategoryHomology.homologyFunctor_map_mapDerivedCategory_map`, the same naturality solved
for the cohomology of the image. Neither brick assumes anything beyond exactness.

*The two crossings are composed before the brick is applied, and the square is written out.* The
brick's `q` is an explicit morphism, so the square is supplied as
`(openSubschemeSectionsComparison f V ≫ whiskered model comparison).naturality c` **with its type
given**: left to unification the composite functor's `Q.map c` spelling is what appears, and the
inner conjugation then cannot be substituted for it. The statement presents the two crossings
separately, which is how a chase meets them, and the private `split_app_two` reassociates the two
readings — `Functor.map_comp` and the inner substitution are applied at variables of abstract
categories, because at the concrete terms `rw` is an `isDefEq` timeout and `simp only` fails
silently.

*No `@[stacks …]` attribute is placed.* [Stacks, Tag 089W] carries its own where it is proved, and
conclusion (c) of [Stacks, Tag 0EX3] is proved elsewhere, as
`…TopDegreeBaseChange.isIso_topDirectImageBaseChangeMap` (`BaseChangeTopDegreeConclusion.lean`), by
a route that does not use this file.

## References

* [Stacks Project, Tag 0EX3](https://stacks.math.columbia.edu/tag/0EX3)
* [Stacks Project, Tag 089W](https://stacks.math.columbia.edu/tag/089W)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction (opensMap)
open Stacks.Cohomology.DerivedSectionsLeray (derivedPreimageSections derivedSectionsOverOpen)
open Stacks.EdgeCompat (preimageRestrictScalars preimageSectionsModelComparison)
open StacksDraft.DerivedCategoryHomology

universe u

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance] RingedSpaceModuleAdjunction.preservesLimits_modulePushforward
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

namespace Stacks.AlgebraicGeometry.TopDegreeBaseChange

/-- **An equation of composites with both of its functor applications split.** From
`H.map m ≫ H.map (xL ≫ yL) = H.map (xK ≫ yK) ≫ Ψ` one gets the four factors read separately. At
variables of abstract categories: `Functor.map_comp` is applied here rather than by
`simp only` at the concrete hypothesis, where it fails silently. -/
private theorem split_app_two {C D : Type*} [Category* C] [Category* D] (H : C ⥤ D)
    {A B₁ B₂ B₃ P₁ P₂ : C}
    {m : A ⟶ B₁} {xL : B₁ ⟶ B₂} {yL : B₂ ⟶ B₃}
    {xK : A ⟶ P₁} {yK : P₁ ⟶ P₂} {Ψ : H.obj P₂ ⟶ H.obj B₃}
    (h : H.map m ≫ H.map (xL ≫ yL) = H.map (xK ≫ yK) ≫ Ψ) :
    H.map m ≫ H.map xL ≫ H.map yL = H.map xK ≫ H.map yK ≫ Ψ := by
  rw [H.map_comp, H.map_comp, Category.assoc] at h
  exact h

/-- **The same with the hypothesis's inner cohomology map replaced by a conjugate.** The
substitution `hw` is performed at variables of abstract categories, where it is a one-step rewrite
of a bound morphism; at the concrete terms the same `rw` is a `isDefEq` timeout. -/
private theorem split_app_two_of_map {C D E : Type*} [Category* C] [Category* D] [Category* E]
    (H : C ⥤ D) (T : E ⥤ D)
    {A B₁ B₂ B₃ P₁ P₂ : C} {W₁ W₂ : E}
    {m : A ⟶ B₁} {xL : B₁ ⟶ B₂} {yL : B₂ ⟶ B₃}
    {xK : A ⟶ P₁} {yK : P₁ ⟶ P₂}
    {a : H.obj P₂ ⟶ T.obj W₁} {b : T.obj W₂ ⟶ H.obj B₃}
    {w w' : W₁ ⟶ W₂} (hw : w = w')
    (h : H.map m ≫ H.map (xL ≫ yL) = H.map (xK ≫ yK) ≫ a ≫ T.map w ≫ b) :
    H.map m ≫ H.map xL ≫ H.map yL = H.map xK ≫ H.map yK ≫ a ≫ T.map w' ≫ b := by
  rw [hw] at h
  exact split_app_two H h

variable {X S : Scheme.{u}} (f : X ⟶ S) (V : S.Opens)

/-- **Factor (2) of the base-change comparison of [Stacks, Tag 0EX3] (c).** For a morphism of schemes
`f : X ⟶ S`, an open `V ⊆ S`, a degree `n` and an arbitrary morphism `c : K ⟶ L` of `D(𝒪_X)`, the
degree-`n` cohomology of `(derivedPreimageSections f V).map c` — the first leading factor of the other side,
the comparison of the two models of the inner derived pushforward read in the ambient model —
followed by the open-subscheme crossing
`…TopDegreeBaseChange.openSubschemeSectionsComparison f V` at `L` and by
`Stacks.EdgeCompat.preimageSectionsModelComparison (f ∣_ V) ⊤` at the restriction of `L`, is the
same two crossings at `K` followed by **factor (2)** — the degree-`n` cohomology of
`…DerivedSectionsLeray.derivedSectionsOverOpen (f⁻¹V : Scheme) ((opensMap (f ∣_ V)).obj ⊤)`
applied to the restriction of `c` — read under the two restrictions of scalars, each crossed past
`Hⁿ` by `StacksDraft.DerivedCategoryHomology.mapDerivedCategoryHomologyIso`.

This is the naturality of the two crossings and nothing more: no transformation is built, nothing
is inverted, and no `rightDerivedDesc` is taken. **Nothing is assumed** of `f`, of `V`, of `c` or
of `n`. -/
theorem homologyFunctor_map_derivedPreimageSections_map_comp_eq (n : ℤ)
    {K L : DerivedCategory (SheafOfModules.{u} (structureSheafRing X.toRingedSpace))}
    (c : K ⟶ L) :
    (DerivedCategory.homologyFunctor
            (ModuleCat.{u} ((structureSheafRing S.toRingedSpace).obj.obj (op V))) n).map
          ((derivedPreimageSections f.toLRSHom.toShHom V).map c) ≫
        (DerivedCategory.homologyFunctor
              (ModuleCat.{u} ((structureSheafRing S.toRingedSpace).obj.obj (op V))) n).map
            ((openSubschemeSectionsComparison f V).app L) ≫
          (DerivedCategory.homologyFunctor
                (ModuleCat.{u} ((structureSheafRing S.toRingedSpace).obj.obj (op V))) n).map
              ((ModuleCat.restrictScalars
                  (Scheme.Opens.topIso V).inv.hom).mapDerivedCategory.map
                ((preimageSectionsModelComparison (f ∣_ V).toLRSHom.toShHom ⊤).app
                  ((openSubschemeRestriction f V).mapDerivedCategory.obj L))) =
      (DerivedCategory.homologyFunctor
            (ModuleCat.{u} ((structureSheafRing S.toRingedSpace).obj.obj (op V))) n).map
          ((openSubschemeSectionsComparison f V).app K) ≫
        (DerivedCategory.homologyFunctor
              (ModuleCat.{u} ((structureSheafRing S.toRingedSpace).obj.obj (op V))) n).map
            ((ModuleCat.restrictScalars
                (Scheme.Opens.topIso V).inv.hom).mapDerivedCategory.map
              ((preimageSectionsModelComparison (f ∣_ V).toLRSHom.toShHom ⊤).app
                ((openSubschemeRestriction f V).mapDerivedCategory.obj K))) ≫
          (mapDerivedCategoryHomologyIso
              (ModuleCat.restrictScalars (Scheme.Opens.topIso V).inv.hom) n).hom.app
              ((preimageRestrictScalars
                  (f ∣_ V).toLRSHom.toShHom ⊤).mapDerivedCategory.obj
                ((derivedSectionsOverOpen (f ⁻¹ᵁ V : Scheme).toRingedSpace
                    ((opensMap (f ∣_ V).toLRSHom.toShHom).obj ⊤)).obj
                  ((openSubschemeRestriction f V).mapDerivedCategory.obj K))) ≫
            (ModuleCat.restrictScalars (Scheme.Opens.topIso V).inv.hom).map
                ((mapDerivedCategoryHomologyIso
                    (preimageRestrictScalars (f ∣_ V).toLRSHom.toShHom ⊤) n).hom.app
                    ((derivedSectionsOverOpen (f ⁻¹ᵁ V : Scheme).toRingedSpace
                        ((opensMap (f ∣_ V).toLRSHom.toShHom).obj ⊤)).obj
                      ((openSubschemeRestriction f V).mapDerivedCategory.obj K)) ≫
                  (preimageRestrictScalars (f ∣_ V).toLRSHom.toShHom ⊤).map
                      ((DerivedCategory.homologyFunctor
                        (ModuleCat.{u} ((structureSheafRing
                          (f ⁻¹ᵁ V : Scheme).toRingedSpace).obj.obj
                            (op ((opensMap (f ∣_ V).toLRSHom.toShHom).obj ⊤)))) n).map
                        ((derivedSectionsOverOpen (f ⁻¹ᵁ V : Scheme).toRingedSpace
                            ((opensMap (f ∣_ V).toLRSHom.toShHom).obj ⊤)).map
                          ((openSubschemeRestriction f V).mapDerivedCategory.map c))) ≫
                    (mapDerivedCategoryHomologyIso
                      (preimageRestrictScalars (f ∣_ V).toLRSHom.toShHom ⊤) n).inv.app
                      ((derivedSectionsOverOpen (f ⁻¹ᵁ V : Scheme).toRingedSpace
                          ((opensMap (f ∣_ V).toLRSHom.toShHom).obj ⊤)).obj
                        ((openSubschemeRestriction f V).mapDerivedCategory.obj L))) ≫
              (mapDerivedCategoryHomologyIso
                (ModuleCat.restrictScalars (Scheme.Opens.topIso V).inv.hom) n).inv.app
                ((preimageRestrictScalars
                    (f ∣_ V).toLRSHom.toShHom ⊤).mapDerivedCategory.obj
                  ((derivedSectionsOverOpen (f ⁻¹ᵁ V : Scheme).toRingedSpace
                      ((opensMap (f ∣_ V).toLRSHom.toShHom).obj ⊤)).obj
                    ((openSubschemeRestriction f V).mapDerivedCategory.obj L))) := by
  have hsq : (derivedPreimageSections f.toLRSHom.toShHom V).map c ≫
        ((openSubschemeSectionsComparison f V).app L ≫
          (ModuleCat.restrictScalars
              (Scheme.Opens.topIso V).inv.hom).mapDerivedCategory.map
            ((preimageSectionsModelComparison (f ∣_ V).toLRSHom.toShHom ⊤).app
              ((openSubschemeRestriction f V).mapDerivedCategory.obj L))) =
      ((openSubschemeSectionsComparison f V).app K ≫
          (ModuleCat.restrictScalars
              (Scheme.Opens.topIso V).inv.hom).mapDerivedCategory.map
            ((preimageSectionsModelComparison (f ∣_ V).toLRSHom.toShHom ⊤).app
              ((openSubschemeRestriction f V).mapDerivedCategory.obj K))) ≫
        (ModuleCat.restrictScalars
            (Scheme.Opens.topIso V).inv.hom).mapDerivedCategory.map
          ((preimageRestrictScalars
              (f ∣_ V).toLRSHom.toShHom ⊤).mapDerivedCategory.map
            ((derivedSectionsOverOpen (f ⁻¹ᵁ V : Scheme).toRingedSpace
                ((opensMap (f ∣_ V).toLRSHom.toShHom).obj ⊤)).map
              ((openSubschemeRestriction f V).mapDerivedCategory.map c))) :=
    (openSubschemeSectionsComparison f V ≫
      Functor.whiskerRight
        (Functor.whiskerLeft (openSubschemeRestriction f V).mapDerivedCategory
          (preimageSectionsModelComparison (f ∣_ V).toLRSHom.toShHom ⊤))
        (ModuleCat.restrictScalars
          (Scheme.Opens.topIso V).inv.hom).mapDerivedCategory).naturality c
  exact split_app_two_of_map _ _
    (homologyFunctor_map_mapDerivedCategory_map
      (preimageRestrictScalars (f ∣_ V).toLRSHom.toShHom ⊤) n
      ((derivedSectionsOverOpen (f ⁻¹ᵁ V : Scheme).toRingedSpace
          ((opensMap (f ∣_ V).toLRSHom.toShHom).obj ⊤)).map
        ((openSubschemeRestriction f V).mapDerivedCategory.map c)))
    (homologyFunctor_map_comp_eq_of_square
      (ModuleCat.restrictScalars (Scheme.Opens.topIso V).inv.hom) n hsq)

end Stacks.AlgebraicGeometry.TopDegreeBaseChange

end
