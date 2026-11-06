module

public import StacksCore.Tactic.StacksAttribute
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.HenselianRings.StrictHenselizationStalkSections
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SpecializationMapAndFibres

/-!
# The specialization map is pullback by the morphism of strict henselizations

Let `S` be a scheme, `s` a geometric point of `S`, `p : Spec(𝒪^{sh}_{S,s}) ⟶ S` the structure
morphism of the strict henselization at `s`, and `t` a geometric point of
`Spec(𝒪^{sh}_{S,s})`. The specialization morphism of strict henselizations

`c : Spec(𝒪^{sh}_{S,t ≫ p}) ⟶ Spec(𝒪^{sh}_{S,s})`

is the unique morphism over `S` carrying the canonical geometric point of its source to `t`.
This file proves that pullback of sections along `c` is the specialization map, both on abelian
sheaves and on the unbounded derived category: under the identifications of a geometric stalk
with the sections of the inverse image over the strict henselization at that point, the
specialization map `sp : F_s ⟶ F_{t ≫ p}` is restriction of sections along `c`, and the
specialization map on derived stalks `sp : K_s ⟶ K_{t ≫ p}` is restriction of unbounded derived
global sections along `c`.

## Main results

* `AlgebraicGeometry.etaleStalkToSectionsAb_id_comp_sectionsRestrictionAb_specializationMorphism`
  — the identification `F_s = Γ(Spec(𝒪^{sh}_{S,s}), p⁻¹F)`, followed by restriction of sections
  along `c`, is the specialization map followed by the identification
  `F_{t ≫ p} = Γ(Spec(𝒪^{sh}_{S,t ≫ p}), p⁻¹F)`.
* `AlgebraicGeometry.vanishingCyclesMap_id_comp_derivedSectionsRestriction_specializationMorphism`
  — the same on unbounded derived categories, with `RΓ` in place of `Γ`.
* `AlgebraicGeometry.existsUnique_specializationMorphism_and_specialization_eq_pullback` —
  **Tag 0GJ4**, the whole remark: the existence and uniqueness of `c`, the invertibility of the
  identifications of stalks with sections over the strict henselizations (on sheaves and on the
  unbounded derived category), and the two identifications of `sp` with pullback by `c`.

## Implementation notes

*The statement on abelian sheaves.* Both sides are maps out of the stalk at `s`, which is the
colimit of the sections over the étale neighbourhoods of `s`, so it suffices to compare them on
a germ. There both sides are restriction of the section along a morphism
`Spec(𝒪^{sh}_{S,t ≫ p}) ⟶ W` into the étale neighbourhood, and the two morphisms coincide by
`AlgebraicGeometry.specializationMorphism_comp_neighborhoodLift`: `c` carries the canonical
morphism from the strict henselization at `s` into `W` to the canonical morphism from the strict
henselization at `t ≫ p` into `W` at the specialized lift. That compatibility holds by the
uniqueness of those morphisms, the strict henselization being the initial étale neighbourhood.

*The statement on derived categories.* The statement on abelian sheaves is the only input. Both
sides are transformations out of the degreewise action of the stalk functor at `s`, which is
exact and hence a right derived functor of its own action on homotopy categories, so a
transformation out of it is determined by its factorization through
`CategoryTheory.Functor.mapDerivedCategoryFactorsh`. The left-hand side is an instance of
`Stacks.DerivedFunctor.whiskerLeft_compIso_eq_exactDerivedDesc`, whose factorizations are
`AlgebraicGeometry.vanishingCyclesMap_fac_app` and
`Stacks.EtaleCohomology.smallEtaleDerivedGlobalSectionsRestriction_fac_app`; the right-hand side
is an instance of `Stacks.DerivedFunctor.natTrans_comp_eq_exactDerivedDesc`, proved here, whose
input is the degreewise description `AlgebraicGeometry.smallEtaleDerivedSpecializationStalkAb_app`
of the specialization map on derived stalks. Both descend transformations on abelian sheaves, so
the two agree as soon as those do. No boundedness of the complex enters, as the source says.

*The equality signs.* The two identifications are the canonical maps
`AlgebraicGeometry.etaleStalkToSectionsAb` and `AlgebraicGeometry.vanishingCyclesMap` at the
identity of the respective strict henselization, and the whole remark asserts that they are
isomorphisms: `AlgebraicGeometry.isIso_etaleStalkToSectionsAb_id` and
`AlgebraicGeometry.isIso_vanishingCyclesMap_id`. As the source says, this holds because global
sections over a strictly henselian scheme are exact and are the stalk at the closed geometric
point (`AlgebraicGeometry.isIso_strictHenselizationSectionsToStalkAb`), so no boundedness of `K`
enters; the stalk of the inverse image at that point is the stalk at `s` by Stacks 03Q1.

## References

* [Stacks Project, Tag 0GJ4](https://stacks.math.columbia.edu/tag/0GJ4)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme Stacks.EtaleCohomology

universe u

namespace Stacks.DerivedFunctor

universe w₁ w₂ w₃ v₁ v₂ v₃ u₁ u₂ u₃

/-- **Precomposing a descent with a transformation of the source.** For exact functors `F` and
`F'` out of an abelian category, a transformation `σ : F ⟶ F'`, a transformation
`τ : F' ⟶ G ⋙ H` and the unit `η` of a right derived functor `RH` of `H`, a transformation `σD`
on unbounded derived categories acting degreewise as `σ` followed by the descent of `τ` is the
descent of `σ ≫ τ`.

Both are transformations out of `F.mapDerivedCategory`, which is a right derived functor of the
action of `F` on homotopy categories, so they agree as soon as their factorizations through
`CategoryTheory.Functor.mapDerivedCategoryFactorsh` do; there the statement is that the
degreewise action of `σ ≫ τ` is that of `σ` followed by that of `τ`, which is
`Stacks.DerivedFunctor.mapHomotopyCategoryOfComp_comp_left`. -/
public theorem natTrans_comp_eq_exactDerivedDesc
    {A₁ : Type u₁} [Category.{v₁} A₁] [Abelian A₁] [HasDerivedCategory.{w₁} A₁]
    {A₂ : Type u₂} [Category.{v₂} A₂] [Abelian A₂] [HasDerivedCategory.{w₂} A₂]
    {A₃ : Type u₃} [Category.{v₃} A₃] [Abelian A₃] [HasDerivedCategory.{w₃} A₃]
    (F F' : A₁ ⥤ A₃) [F.Additive] [F'.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits F'] [PreservesFiniteColimits F']
    (G : A₁ ⥤ A₂) [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (H : A₂ ⥤ A₃) [H.Additive] (RH : DerivedCategory A₂ ⥤ DerivedCategory A₃)
    (η : H.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ RH)
    (σ : F ⟶ F') (τ : F' ⟶ G ⋙ H)
    (σD : F.mapDerivedCategory ⟶ F'.mapDerivedCategory)
    (hσ : ∀ W, σD.app (DerivedCategory.Qh.obj W) =
      F.mapDerivedCategoryFactorsh.hom.app W ≫
        DerivedCategory.Qh.map
            ((NatTrans.mapHomotopyCategory σ (ComplexShape.up ℤ)).app W) ≫
          F'.mapDerivedCategoryFactorsh.inv.app W) :
    σD ≫ exactDerivedDesc F' G H RH η τ = exactDerivedDesc F G H RH η (σ ≫ τ) := by
  refine Functor.rightDerived_ext F.mapDerivedCategory F.mapDerivedCategoryFactorsh.inv
    (HomotopyCategory.quasiIso A₁ (ComplexShape.up ℤ)) _ _ _
    (NatTrans.ext (funext fun J => ?_))
  show F.mapDerivedCategoryFactorsh.inv.app J ≫
      (σD ≫ exactDerivedDesc F' G H RH η τ).app (DerivedCategory.Qh.obj J) =
    F.mapDerivedCategoryFactorsh.inv.app J ≫
      (exactDerivedDesc F G H RH η (σ ≫ τ)).app (DerivedCategory.Qh.obj J)
  rw [NatTrans.comp_app, hσ J, exactDerivedDesc_fac_app F G H RH η (σ ≫ τ) J,
    mapHomotopyCategoryOfComp_comp_left F F' G H σ τ J]
  simp only [Category.assoc]
  rw [Iso.inv_hom_id_app_assoc, exactDerivedDesc_fac_app F' G H RH η τ J,
    Functor.map_comp]
  simp only [Category.assoc]

end Stacks.DerivedFunctor

namespace AlgebraicGeometry

/-! ### Restriction of sections along a morphism over the base, whiskered -/

/-- Restriction of global sections of an inverse image along a morphism of schemes over the base,
written as a whiskering followed by the composition isomorphism for inverse images: the form in
which the descent lemmas for unbounded derived categories take it. -/
theorem smallEtaleSectionsRestrictionAb_eq_whiskerLeft {Z T T' : Scheme.{u}} (g : T ⟶ Z)
    (c : T' ⟶ T) (g' : T' ⟶ Z) (hc : c ≫ g = g') :
    smallEtaleSectionsRestrictionAb g c g' hc =
      Functor.whiskerLeft (smallEtalePullbackAb g) (smallEtaleGlobalSectionsRestrictionAb c) ≫
        (Functor.associator (smallEtalePullbackAb g) (smallEtalePullbackAb c)
            (Sheaf.Γ (smallEtaleTopology T') Ab.{u + 1})).inv ≫
          Functor.whiskerRight (smallEtalePullbackAbCompIso c g ≪≫
              eqToIso (congrArg (fun m : T' ⟶ Z => smallEtalePullbackAb m) hc)).hom
            (Sheaf.Γ (smallEtaleTopology T') Ab.{u + 1}) := by
  refine NatTrans.ext (funext fun F => ?_)
  simp [smallEtaleSectionsRestrictionAb]

/-! ### The specialization map as pullback by the specialization morphism -/

section Specialization

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (s : GeometricPoint S)
  (t : GeometricPoint (strictHenselization B S hS s))

/-- The specialization morphism of strict henselizations lies over `S`, written with both
structure morphisms read as composites with the identity, which is the form the restriction of
sections of an inverse image takes its hypothesis in. -/
theorem specializationMorphism_id_comp :
    specializationMorphism B S hS s t ≫
        𝟙 (strictHenselization B S hS s) ≫ strictHenselizationToBase B S hS s =
      𝟙 (strictHenselization B S hS (t.map (strictHenselizationToBase B S hS s))) ≫
        strictHenselizationToBase B S hS (t.map (strictHenselizationToBase B S hS s)) :=
  ((congrArg (fun y : strictHenselization B S hS s ⟶ S =>
          specializationMorphism B S hS s t ≫ y)
        (Category.id_comp (strictHenselizationToBase B S hS s))).trans
      (specializationMorphism_comp B S hS s t)).trans
    (Category.id_comp _).symm

/-- **Stacks 0GJ4, the displayed description of `sp` on abelian sheaves.** Let `S` be a scheme,
`s` a geometric point of `S`, `p : Spec(𝒪^{sh}_{S,s}) ⟶ S` the structure morphism of the strict
henselization at `s`, and `t` a geometric point of `Spec(𝒪^{sh}_{S,s})`. Then the identification
`F_s = Γ(Spec(𝒪^{sh}_{S,s}), p⁻¹F)`, followed by restriction of sections along
the specialization morphism `c : Spec(𝒪^{sh}_{S,t ≫ p}) ⟶ Spec(𝒪^{sh}_{S,s})`, is the
specialization map `sp : F_s ⟶ F_{t ≫ p}` followed by the identification
`F_{t ≫ p} = Γ(Spec(𝒪^{sh}_{S,t ≫ p}), p⁻¹F)`.

This is the source's description of `sp` as pullback by `c`. The two identifications are
`AlgebraicGeometry.etaleStalkToSectionsAb` at the identity of the respective strict
henselization, which are isomorphisms by `AlgebraicGeometry.isIso_etaleStalkToSectionsAb_id`. -/
theorem etaleStalkToSectionsAb_id_comp_sectionsRestrictionAb_specializationMorphism :
    etaleStalkToSectionsAb B S hS s (𝟙 (strictHenselization B S hS s)) ≫
        smallEtaleSectionsRestrictionAb
          (𝟙 (strictHenselization B S hS s) ≫ strictHenselizationToBase B S hS s)
          (specializationMorphism B S hS s t)
          (𝟙 (strictHenselization B S hS (t.map (strictHenselizationToBase B S hS s))) ≫
            strictHenselizationToBase B S hS (t.map (strictHenselizationToBase B S hS s)))
          (specializationMorphism_id_comp B S hS s t) =
      smallEtaleSpecializationStalkAb B S hS s t ≫
        etaleStalkToSectionsAb B S hS (t.map (strictHenselizationToBase B S hS s))
          (𝟙 (strictHenselization B S hS
            (t.map (strictHenselizationToBase B S hS s)))) := by
  ext F : 2
  refine smallEtaleStalkAb_hom_ext s.hom F fun W v => ?_
  have hcr : specializationMorphism B S hS s t ≫
      𝟙 (strictHenselization B S hS s) ≫
        strictHenselizationNeighborhoodLift B S hS s W v =
      𝟙 (strictHenselization B S hS (t.map (strictHenselizationToBase B S hS s))) ≫
        strictHenselizationNeighborhoodLift B S hS
          (t.map (strictHenselizationToBase B S hS s)) W
          (specializationEtaleNeighborhoodLift B S hS s t W v) := by
    rw [Category.id_comp, Category.id_comp]
    exact specializationMorphism_comp_neighborhoodLift B S hS s t W v
  have hmain := congrArg (fun σ => NatTrans.app σ F)
    (smallEtaleSectionsPullbackAb_comp_sectionsRestrictionAb
      (𝟙 (strictHenselization B S hS s) ≫ strictHenselizationToBase B S hS s) W
      (specializationMorphism B S hS s t)
      (𝟙 (strictHenselization B S hS (t.map (strictHenselizationToBase B S hS s))) ≫
        strictHenselizationToBase B S hS (t.map (strictHenselizationToBase B S hS s)))
      (𝟙 (strictHenselization B S hS s) ≫
        strictHenselizationNeighborhoodLift B S hS s W v)
      (by rw [Category.assoc, strictHenselizationNeighborhoodLift_comp])
      (specializationMorphism_id_comp B S hS s t)
      (𝟙 (strictHenselization B S hS (t.map (strictHenselizationToBase B S hS s))) ≫
        strictHenselizationNeighborhoodLift B S hS
          (t.map (strictHenselizationToBase B S hS s)) W
          (specializationEtaleNeighborhoodLift B S hS s t W v))
      (by rw [Category.assoc, strictHenselizationNeighborhoodLift_comp])
      hcr)
  refine ((Category.assoc _ _ _).symm.trans ?_).trans (Category.assoc _ _ _)
  rw [etaleStalkToSectionsAb_toPresheafFiber, smallEtaleSpecializationStalkAb_toPresheafFiber]
  exact hmain.trans
    (etaleStalkToSectionsAb_toPresheafFiber B S hS
      (t.map (strictHenselizationToBase B S hS s))
      (𝟙 (strictHenselization B S hS (t.map (strictHenselizationToBase B S hS s)))) F W
      (specializationEtaleNeighborhoodLift B S hS s t W v)).symm

/-- The description of `sp` as pullback by the specialization morphism, with the restriction of
sections written as a whiskering: the form the descent to unbounded derived categories takes. -/
theorem etaleStalkToSectionsAb_id_comp_whiskerLeft_specializationMorphism :
    etaleStalkToSectionsAb B S hS s (𝟙 (strictHenselization B S hS s)) ≫
        Functor.whiskerLeft
            (smallEtalePullbackAb
              (𝟙 (strictHenselization B S hS s) ≫ strictHenselizationToBase B S hS s))
            (smallEtaleGlobalSectionsRestrictionAb (specializationMorphism B S hS s t)) ≫
          (Functor.associator
              (smallEtalePullbackAb
                (𝟙 (strictHenselization B S hS s) ≫ strictHenselizationToBase B S hS s))
              (smallEtalePullbackAb (specializationMorphism B S hS s t))
              (Sheaf.Γ (smallEtaleTopology (strictHenselization B S hS
                (t.map (strictHenselizationToBase B S hS s)))) Ab.{u + 1})).inv ≫
            Functor.whiskerRight (smallEtalePullbackAbCompIso
                  (specializationMorphism B S hS s t)
                  (𝟙 (strictHenselization B S hS s) ≫
                    strictHenselizationToBase B S hS s) ≪≫
                eqToIso (congrArg
                  (fun m : strictHenselization B S hS
                      (t.map (strictHenselizationToBase B S hS s)) ⟶ S =>
                    smallEtalePullbackAb m)
                  (specializationMorphism_id_comp B S hS s t))).hom
              (Sheaf.Γ (smallEtaleTopology (strictHenselization B S hS
                (t.map (strictHenselizationToBase B S hS s)))) Ab.{u + 1}) =
      smallEtaleSpecializationStalkAb B S hS s t ≫
        etaleStalkToSectionsAb B S hS (t.map (strictHenselizationToBase B S hS s))
          (𝟙 (strictHenselization B S hS
            (t.map (strictHenselizationToBase B S hS s)))) := by
  rw [← smallEtaleSectionsRestrictionAb_eq_whiskerLeft]
  exact etaleStalkToSectionsAb_id_comp_sectionsRestrictionAb_specializationMorphism B S hS s t

end Specialization

/-! ### The specialization map on unbounded derived categories -/

section Derived

attribute [local instance] HasDerivedCategory.standard

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (s : GeometricPoint S)
  (t : GeometricPoint (strictHenselization B S hS s))
  [((Sheaf.Γ (smallEtaleTopology (strictHenselization B S hS s))
        Ab.{u + 1}).mapHomotopyCategory (.up ℤ) ⋙
      DerivedCategory.Qh).HasRightDerivedFunctor
      (HomotopyCategory.quasiIso
        (Sheaf (smallEtaleTopology (strictHenselization B S hS s)) Ab.{u + 1}) (.up ℤ))]
  [((Sheaf.Γ (smallEtaleTopology (strictHenselization B S hS
          (t.map (strictHenselizationToBase B S hS s))))
        Ab.{u + 1}).mapHomotopyCategory (.up ℤ) ⋙
      DerivedCategory.Qh).HasRightDerivedFunctor
      (HomotopyCategory.quasiIso
        (Sheaf (smallEtaleTopology (strictHenselization B S hS
          (t.map (strictHenselizationToBase B S hS s)))) Ab.{u + 1}) (.up ℤ))]

/-- **Stacks 0GJ4, the displayed description of `sp` on the unbounded derived category.** For an
object `K` of the unbounded derived category of abelian sheaves on the small étale site of `S`,
the identification `K_s = RΓ(Spec(𝒪^{sh}_{S,s}), p⁻¹K)`, followed by restriction of unbounded
derived global sections along the specialization morphism
`c : Spec(𝒪^{sh}_{S,t ≫ p}) ⟶ Spec(𝒪^{sh}_{S,s})`, is the specialization map on derived stalks
`sp : K_s ⟶ K_{t ≫ p}` followed by the identification
`K_{t ≫ p} = RΓ(Spec(𝒪^{sh}_{S,t ≫ p}), p⁻¹K)`.

This is the source's assertion that the same procedure computes `sp` for objects of
`D(S_étale)`, with `RΓ` in place of `Γ`. The complex is unbounded: both sides are
transformations out of the degreewise action of the exact stalk functor, which is a right
derived functor of its own action on homotopy categories, so the statement on abelian sheaves
determines them. -/
theorem vanishingCyclesMap_id_comp_derivedSectionsRestriction_specializationMorphism :
    vanishingCyclesMap B S hS s (𝟙 (strictHenselization B S hS s)) ≫
        Functor.whiskerLeft
            (smallEtaleDerivedPullbackAb
              (𝟙 (strictHenselization B S hS s) ≫ strictHenselizationToBase B S hS s))
            (smallEtaleDerivedGlobalSectionsRestriction
              (specializationMorphism B S hS s t)) ≫
          (Functor.associator
              (smallEtaleDerivedPullbackAb
                (𝟙 (strictHenselization B S hS s) ≫ strictHenselizationToBase B S hS s))
              (smallEtaleDerivedPullbackAb (specializationMorphism B S hS s t))
              (smallEtaleDerivedGlobalSections (strictHenselization B S hS
                (t.map (strictHenselizationToBase B S hS s))))).inv ≫
            Functor.whiskerRight (Functor.mapDerivedCategoryCompIsoOfCompIso
                (smallEtalePullbackAbCompIso (specializationMorphism B S hS s t)
                    (𝟙 (strictHenselization B S hS s) ≫
                      strictHenselizationToBase B S hS s) ≪≫
                  eqToIso (congrArg
                    (fun m : strictHenselization B S hS
                        (t.map (strictHenselizationToBase B S hS s)) ⟶ S =>
                      smallEtalePullbackAb m)
                    (specializationMorphism_id_comp B S hS s t)))).hom
              (smallEtaleDerivedGlobalSections (strictHenselization B S hS
                (t.map (strictHenselizationToBase B S hS s)))) =
      smallEtaleDerivedSpecializationStalkAb B S hS s t ≫
        vanishingCyclesMap B S hS (t.map (strictHenselizationToBase B S hS s))
          (𝟙 (strictHenselization B S hS
            (t.map (strictHenselizationToBase B S hS s)))) := by
  rw [Stacks.DerivedFunctor.whiskerLeft_compIso_eq_exactDerivedDesc
      (smallEtaleStalkAb s.hom) _
      (Sheaf.Γ (smallEtaleTopology (strictHenselization B S hS
        (t.map (strictHenselizationToBase B S hS s)))) Ab.{u + 1})
      (smallEtaleDerivedGlobalSections (strictHenselization B S hS
        (t.map (strictHenselizationToBase B S hS s))))
      (smallEtaleDerivedGlobalSectionsUnit (strictHenselization B S hS
        (t.map (strictHenselizationToBase B S hS s))))
      (smallEtalePullbackAb
        (𝟙 (strictHenselization B S hS s) ≫ strictHenselizationToBase B S hS s))
      (Sheaf.Γ (smallEtaleTopology (strictHenselization B S hS s)) Ab.{u + 1})
      (smallEtalePullbackAb (specializationMorphism B S hS s t))
      (smallEtaleDerivedGlobalSections (strictHenselization B S hS s))
      (smallEtaleDerivedGlobalSectionsUnit (strictHenselization B S hS s)) _
      (etaleStalkToSectionsAb B S hS s (𝟙 (strictHenselization B S hS s)))
      (smallEtaleGlobalSectionsRestrictionAb (specializationMorphism B S hS s t))
      (vanishingCyclesMap B S hS s (𝟙 (strictHenselization B S hS s)))
      (smallEtaleDerivedGlobalSectionsRestriction (specializationMorphism B S hS s t))
      (vanishingCyclesMap_fac_app B S hS s (𝟙 (strictHenselization B S hS s)))
      (smallEtaleDerivedGlobalSectionsRestriction_fac_app
        (specializationMorphism B S hS s t)),
    etaleStalkToSectionsAb_id_comp_whiskerLeft_specializationMorphism B S hS s t,
    ← Stacks.DerivedFunctor.natTrans_comp_eq_exactDerivedDesc
      (smallEtaleStalkAb s.hom)
      (smallEtaleStalkAb (t.map (strictHenselizationToBase B S hS s)).hom) _ _ _ _
      (smallEtaleSpecializationStalkAb B S hS s t)
      (etaleStalkToSectionsAb B S hS (t.map (strictHenselizationToBase B S hS s))
        (𝟙 (strictHenselization B S hS
          (t.map (strictHenselizationToBase B S hS s)))))
      (smallEtaleDerivedSpecializationStalkAb B S hS s t)
      (smallEtaleDerivedSpecializationStalkAb_app B S hS s t)]
  rfl

end Derived

/-! ### The whole remark -/

section WholeTag

attribute [local instance] HasDerivedCategory.standard

/-- **Stacks 0GJ4.** Let `S` be a scheme, `s` a geometric point of `S`, and `t` a geometric
point of the strict henselization `Spec(𝒪^{sh}_{S,s})`, with structure morphism
`p : Spec(𝒪^{sh}_{S,s}) ⟶ S`.

1. There is exactly one morphism `c : Spec(𝒪^{sh}_{S,t ≫ p}) ⟶ Spec(𝒪^{sh}_{S,s})` over `S`
   compatible with the given morphism `t` to `Spec(𝒪^{sh}_{S,s})` and the canonical geometric
   point of `Spec(𝒪^{sh}_{S,t ≫ p})`.
2. Taking global sections of abelian sheaves over the strictly henselian schemes
   `Spec(𝒪^{sh}_{S,s})` and `Spec(𝒪^{sh}_{S,t ≫ p})` is exact, and is the same as taking stalks
   at their canonical geometric points (lying over `s` and over `t ≫ p`). This is the source's
   reason that the equality signs below are valid.
3. For abelian sheaves `F` on the small étale site of `S`, the identifications
   `F_s = Γ(Spec(𝒪^{sh}_{S,s}), p⁻¹F)` and `F_{t ≫ p} = Γ(Spec(𝒪^{sh}_{S,t ≫ p}), p⁻¹F)` are
   isomorphisms, and the specialization map `sp : F_s ⟶ F_{t ≫ p}` is pullback by `c`: the
   first identification followed by restriction of sections along `c` is `sp` followed by the
   second identification.
4. The same holds for objects `K` of the unbounded derived category `D(S_étale)`, with `RΓ` in
   place of `Γ` and the specialization map on derived stalks in place of `sp`: both
   identifications `K_s = RΓ(Spec(𝒪^{sh}_{S,s}), K)` and
   `K_{t ≫ p} = RΓ(Spec(𝒪^{sh}_{S,t ≫ p}), K)` are isomorphisms, and `sp` is pullback by `c`.

Part (1) is `AlgebraicGeometry.existsUnique_specializationMorphism`; part (2) is
`AlgebraicGeometry.preservesFiniteColimits_smallEtaleGlobalSections_strictHenselization` and
`AlgebraicGeometry.isIso_strictHenselizationSectionsToStalkAb`; the invertibility in (3) and
(4) is `AlgebraicGeometry.isIso_etaleStalkToSectionsAb_id` and
`AlgebraicGeometry.isIso_vanishingCyclesMap_id`, the source's reason that global sections over a
strictly henselian scheme are exact and are the stalk at the closed point; the equations are
`AlgebraicGeometry.etaleStalkToSectionsAb_id_comp_sectionsRestrictionAb_specializationMorphism`
and
`AlgebraicGeometry.vanishingCyclesMap_id_comp_derivedSectionsRestriction_specializationMorphism`.
The derivability instances that unbounded derived global sections on the two strict
henselizations are formed with are bound inside part (4); they hold for every scheme
(`Stacks.EtaleCohomology.smallEtaleGlobalSectionsAb_hasRightDerivedFunctor`), and part (4) is
proved for every choice of them. -/
@[stacks 0GJ4 "the whole remark: (1) the unique existence of `c`; (2) global sections over the \
two strictly henselian schemes are exact and are stalks at their closed geometric points; (3) on \
abelian sheaves, the identifications of the stalks at `s` and at `t ≫ p` with the sections over \
the two strict henselizations are isomorphisms, and `sp` is pullback by `c`; (4) the same on the \
unbounded derived category, with `RΓ`. The big etale site `B` with `hS` is a size device, not a \
source hypothesis."]
public theorem existsUnique_specializationMorphism_and_specialization_eq_pullback
    (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (s : GeometricPoint S)
    (t : GeometricPoint (strictHenselization B S hS s)) :
    (∃! c : strictHenselization B S hS (t.map (strictHenselizationToBase B S hS s)) ⟶
        strictHenselization B S hS s,
        c ≫ strictHenselizationToBase B S hS s =
            strictHenselizationToBase B S hS
              (t.map (strictHenselizationToBase B S hS s)) ∧
          geometricPointToStrictHenselization B S hS
              (t.map (strictHenselizationToBase B S hS s)) ≫ c = t.hom) ∧
      (PreservesFiniteColimits
          (Sheaf.Γ (smallEtaleTopology (strictHenselization B S hS s)) Ab.{u + 1}) ∧
        PreservesFiniteColimits (Sheaf.Γ (smallEtaleTopology (strictHenselization B S hS
          (t.map (strictHenselizationToBase B S hS s)))) Ab.{u + 1}) ∧
        IsIso (strictHenselizationSectionsToStalkAb B S hS s) ∧
        IsIso (strictHenselizationSectionsToStalkAb B S hS
          (t.map (strictHenselizationToBase B S hS s)))) ∧
      (IsIso (etaleStalkToSectionsAb B S hS s (𝟙 (strictHenselization B S hS s))) ∧
        IsIso (etaleStalkToSectionsAb B S hS (t.map (strictHenselizationToBase B S hS s))
          (𝟙 (strictHenselization B S hS (t.map (strictHenselizationToBase B S hS s))))) ∧
        etaleStalkToSectionsAb B S hS s (𝟙 (strictHenselization B S hS s)) ≫
            smallEtaleSectionsRestrictionAb
              (𝟙 (strictHenselization B S hS s) ≫ strictHenselizationToBase B S hS s)
              (specializationMorphism B S hS s t)
              (𝟙 (strictHenselization B S hS
                  (t.map (strictHenselizationToBase B S hS s))) ≫
                strictHenselizationToBase B S hS
                  (t.map (strictHenselizationToBase B S hS s)))
              (specializationMorphism_id_comp B S hS s t) =
          smallEtaleSpecializationStalkAb B S hS s t ≫
            etaleStalkToSectionsAb B S hS (t.map (strictHenselizationToBase B S hS s))
              (𝟙 (strictHenselization B S hS
                (t.map (strictHenselizationToBase B S hS s))))) ∧
        ∀ [((Sheaf.Γ (smallEtaleTopology (strictHenselization B S hS s))
                Ab.{u + 1}).mapHomotopyCategory (.up ℤ) ⋙
              DerivedCategory.Qh).HasRightDerivedFunctor
              (HomotopyCategory.quasiIso
                (Sheaf (smallEtaleTopology (strictHenselization B S hS s))
                  Ab.{u + 1}) (.up ℤ))]
            [((Sheaf.Γ (smallEtaleTopology (strictHenselization B S hS
                    (t.map (strictHenselizationToBase B S hS s))))
                  Ab.{u + 1}).mapHomotopyCategory (.up ℤ) ⋙
                DerivedCategory.Qh).HasRightDerivedFunctor
                (HomotopyCategory.quasiIso
                  (Sheaf (smallEtaleTopology (strictHenselization B S hS
                    (t.map (strictHenselizationToBase B S hS s)))) Ab.{u + 1}) (.up ℤ))],
          IsIso (vanishingCyclesMap B S hS s (𝟙 (strictHenselization B S hS s))) ∧
          IsIso (vanishingCyclesMap B S hS (t.map (strictHenselizationToBase B S hS s))
            (𝟙 (strictHenselization B S hS (t.map (strictHenselizationToBase B S hS s))))) ∧
          vanishingCyclesMap B S hS s (𝟙 (strictHenselization B S hS s)) ≫
              Functor.whiskerLeft
                  (smallEtaleDerivedPullbackAb
                    (𝟙 (strictHenselization B S hS s) ≫
                      strictHenselizationToBase B S hS s))
                  (smallEtaleDerivedGlobalSectionsRestriction
                    (specializationMorphism B S hS s t)) ≫
                (Functor.associator
                    (smallEtaleDerivedPullbackAb
                      (𝟙 (strictHenselization B S hS s) ≫
                        strictHenselizationToBase B S hS s))
                    (smallEtaleDerivedPullbackAb (specializationMorphism B S hS s t))
                    (smallEtaleDerivedGlobalSections (strictHenselization B S hS
                      (t.map (strictHenselizationToBase B S hS s))))).inv ≫
                  Functor.whiskerRight (Functor.mapDerivedCategoryCompIsoOfCompIso
                      (smallEtalePullbackAbCompIso (specializationMorphism B S hS s t)
                          (𝟙 (strictHenselization B S hS s) ≫
                            strictHenselizationToBase B S hS s) ≪≫
                        eqToIso (congrArg
                          (fun m : strictHenselization B S hS
                              (t.map (strictHenselizationToBase B S hS s)) ⟶ S =>
                            smallEtalePullbackAb m)
                          (specializationMorphism_id_comp B S hS s t)))).hom
                    (smallEtaleDerivedGlobalSections (strictHenselization B S hS
                      (t.map (strictHenselizationToBase B S hS s)))) =
            smallEtaleDerivedSpecializationStalkAb B S hS s t ≫
              vanishingCyclesMap B S hS (t.map (strictHenselizationToBase B S hS s))
                (𝟙 (strictHenselization B S hS
                  (t.map (strictHenselizationToBase B S hS s)))) :=
  ⟨existsUnique_specializationMorphism B S hS s t,
    ⟨preservesFiniteColimits_smallEtaleGlobalSections_strictHenselization B S hS s,
      preservesFiniteColimits_smallEtaleGlobalSections_strictHenselization B S hS
        (t.map (strictHenselizationToBase B S hS s)),
      isIso_strictHenselizationSectionsToStalkAb B S hS s,
      isIso_strictHenselizationSectionsToStalkAb B S hS
        (t.map (strictHenselizationToBase B S hS s))⟩,
    ⟨isIso_etaleStalkToSectionsAb_id B S hS s,
      isIso_etaleStalkToSectionsAb_id B S hS (t.map (strictHenselizationToBase B S hS s)),
      etaleStalkToSectionsAb_id_comp_sectionsRestrictionAb_specializationMorphism B S hS s t⟩,
    ⟨isIso_vanishingCyclesMap_id B S hS s,
      isIso_vanishingCyclesMap_id B S hS (t.map (strictHenselizationToBase B S hS s)),
      vanishingCyclesMap_id_comp_derivedSectionsRestriction_specializationMorphism B S hS s t⟩⟩

end WholeTag

end AlgebraicGeometry

end
