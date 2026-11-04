module

public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.LiftedSmallEtaleSheafInvComposition
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SmallEtaleRestrictionFinalComparison
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.SmallEtalePullbackSections

/-!
# Sections of the Stacks 06WC pullback at the final object (Stacks 076T)

`AlgebraicGeometry.Stack.liftedSmallEtaleSheafInv_comp` is the composition law for factors 2, 3
and 4 of the identification of sections `AlgebraicGeometry.Stack.liftedSectionsIso` of
**Stacks 076T**, proved unconditionally at the level of sheaves of modules on the small étale
site. `AlgebraicGeometry.Stack.LiftedSectionsFactorFourSquareStandIn` is the same law read on
*sections over the final object* of that site, which is the form the cocycle condition consumes.
This file is the passage between the two.

The obstruction it crosses is that the Stacks 06WC pullback of presheaves of modules is a left
adjoint: nothing computes its sections over any object, let alone over the final object, and the
only general statement about them is the generation bound
`CategoryTheory.PresheafOfModules.mem_pullbackUnitSubmodule`. What this file does instead is to
produce the one map *into* those sections that the adjunction supplies —
`AlgebraicGeometry.Stack.smallEtaleFinalPullbackUnit` — and show that every composite out of the
pullback which the Stacks 076T chain meets is determined on it, with no formula required.

## The two steps

`AlgebraicGeometry.Stack.smallEtaleFinalPullbackUnit_comp` is the general statement: for a
morphism `u` of presheaves of modules below `z` and a morphism `d` out of the pullback of its
target, the pullback of `u` followed by `d`, read through the unit at the final object, is `u`
read there followed by the *mate* of `d` and one restriction map. No formula for the sections of
the pullback appears on either side.

Specializing `d` to the comparison map `c_ψ` of **Stacks 06WC** makes the mate the comparison of
**Stacks 06W2** — `AlgebraicGeometry.Stack.restrictModulePullbackComparison_adjunct` — and
`AlgebraicGeometry.Stack.restrictionPushforwardComparison_app_final` evaluates *that* at the final
object as restriction of `F` along `ψ`. The two final objects involved are the final object of
the small étale site of the scheme below `z'` and the base change along `ψ` of the final object
below `z`; the latter is again a final object by
`AlgebraicGeometry.SmallEtale.smallEtaleBaseChange_finalIsTerminal`, so the canonical arrow
`AlgebraicGeometry.Stack.finalToBaseChangeFinal` between them cancels the one
`AlgebraicGeometry.Stack.restrictToSmallEtaleFinalIso_inv_comp_comparison` leaves behind.

## What is still missing for the stand-in

The square of `AlgebraicGeometry.Stack.LiftedSectionsFactorFourSquareStandIn` needs two further
compatibilities, neither of which is here: naturality of
`AlgebraicGeometry.SmallEtale.associatedModulePresheafIso` in the module, which is
`AlgebraicGeometry.SmallEtale.associatedModulePresheafIso_hom_naturality_module`, and a
compatibility on sections between the base-change identification
`AlgebraicGeometry.Stack.associatedModuleObjSmallEtaleBaseChangeIso` of **Stacks 03LC (1)** and
`Stacks.Sites.quasiCoherentPresheafBaseChangeIso` of **Stacks 03DS**, which is stated, and still
unproved, as `AlgebraicGeometry.Stack.AssociatedModuleBaseChangeFinalSectionsCompat` in
`StacksFrontier/AlgebraicGeometry/Stacks/Quasicoherent/LiftedSectionsFactorFourReduction.lean`.

## Main definitions

* `AlgebraicGeometry.Stack.finalToBaseChangeFinal`: the canonical arrow from the final object of
  the small étale site below `z'` to the base change of the final object below `z`.
* `AlgebraicGeometry.Stack.smallEtaleFinalPullbackUnit`: pulling a section over the final object
  back along `ψ`.

## Main results

* `AlgebraicGeometry.Stack.restrictToSmallEtaleFinalIso_inv_comp_comparison_final` and
  `AlgebraicGeometry.Stack.restrictionPushforwardComparison_app_final`: **the comparison map of
  Stacks 06W2 between the two final objects is restriction along the arrow.**
* `AlgebraicGeometry.Stack.smallEtaleFinalPullbackUnit_comp`: **sections of a map out of the
  Stacks 06WC pullback, at the final object.**
* `AlgebraicGeometry.Stack.smallEtaleFinalPullbackUnit_comp_comparison`: the same with the map
  taken to be the comparison `c_ψ`, where the answer is restriction of `F` along `ψ`.
* `AlgebraicGeometry.Stack.unit_comp_map_sheafifiedFactor` and
  `AlgebraicGeometry.Stack.smallEtaleFinalPullbackUnit_comp_sheafifiedFactor`: **the same for the
  sheafified factors 3 and 4**, which is the shape the Stacks 076T chain is built in.

## References

* [Stacks Project, Tag 076T](https://stacks.math.columbia.edu/tag/076T)
* [Stacks Project, Tag 06W2](https://stacks.math.columbia.edu/tag/06W2)
* [Stacks Project, Tag 06WC](https://stacks.math.columbia.edu/tag/06WC)
* [Stacks Project, Tag 075D](https://stacks.math.columbia.edu/tag/075D)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite

universe u v w

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
  (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type v} [Category.{w} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)
  (τ : GrothendieckTopology B.Schemes) (hτ : τ ≤ B.topology)
  {z' z : 𝒳} (ψ : z' ⟶ z)

attribute [local irreducible] AlgebraicGeometry.smallEtaleBaseChange CategoryTheory.Over.post
  AlgebraicGeometry.Stack.baseStructureSheaf AlgebraicGeometry.Stack.baseRingStructureSheaf

/-- The arrow of the small étale site of the scheme below `z'` from its final object to the base
change along `ψ` of the final object of the small étale site of the scheme below `z`: that base
change is again a final object, so this is the unique such arrow. -/
public noncomputable def finalToBaseChangeFinal :
    smallEtaleFinal B E h S hS p z' ⟶
      (smallEtaleBaseChange E (smallEtaleBaseMorphism B E h S hS p ψ)).obj
        (smallEtaleFinal B E h S hS p z) :=
  (smallEtaleBaseChange_finalIsTerminal E (smallEtaleBaseMorphism B E h S hS p ψ)).from _

/-- **Pulling a section over the final object back along `ψ`.**  For a presheaf of modules `M`
on the small étale site of the scheme below `z`, the map which sends a section of `M` over the
final object `W / W` to a section over the final object `W' / W'` of the Stacks 06WC pullback of
`M`: the unit of the pullback--direct image adjunction along `a_{small}^♯`, followed by
restriction along `AlgebraicGeometry.Stack.finalToBaseChangeFinal`.

Nothing in this development computes the sections of the Stacks 06WC pullback — it is a left
adjoint, and `CategoryTheory.PresheafOfModules.mem_pullbackUnitSubmodule` is the only general
statement about them.  This map is not a computation of them either; it is the one map *into*
them that the adjunction supplies, and the two statements below say it is enough: every composite
out of the pullback that the Stacks 076T chain meets is determined on it. -/
public noncomputable def smallEtaleFinalPullbackUnit
    (M : PresheafOfModules.{u} (SmallEtale.structureSheaf E (p.obj z).left.1
      (contains_base B E h S hS p z)).obj) :
    M.presheaf.obj (op (smallEtaleFinal B E h S hS p z)) ⟶
      ((PresheafOfModules.pullback.{u}
        (smallEtaleStructureComparison B E h S hS p hp ψ τ hτ)).obj M).presheaf.obj
        (op (smallEtaleFinal B E h S hS p z')) :=
  (show M.presheaf.obj (op (smallEtaleFinal B E h S hS p z)) ⟶
      ((PresheafOfModules.pullback.{u}
        (smallEtaleStructureComparison B E h S hS p hp ψ τ hτ)).obj M).presheaf.obj
        (op ((smallEtaleBaseChange E (smallEtaleBaseMorphism B E h S hS p ψ)).obj
          (smallEtaleFinal B E h S hS p z))) from
    ((PresheafOfModules.toPresheaf _).map
        ((PresheafOfModules.pullbackPushforwardAdjunction.{u}
          (smallEtaleStructureComparison B E h S hS p hp ψ τ hτ)).unit.app M)).app
      (op (smallEtaleFinal B E h S hS p z))) ≫
    ((PresheafOfModules.pullback.{u}
      (smallEtaleStructureComparison B E h S hS p hp ψ τ hτ)).obj M).presheaf.map
      (finalToBaseChangeFinal B E h S hS p ψ).op

/-- **The comparison map of Stacks 06W2 between the two final objects is restriction along the
arrow.**  `AlgebraicGeometry.Stack.restrictToSmallEtaleFinalIso_inv_comp_comparison` leaves a
restriction along the canonical arrow from the base change of the final object; composing with
`AlgebraicGeometry.Stack.finalToBaseChangeFinal` cancels it, both arrows being arrows between
final objects of the small étale site of the scheme below `z'`. -/
public theorem restrictToSmallEtaleFinalIso_inv_comp_comparison_final {A : Type*} [Category A]
    (G : 𝒳ᵒᵖ ⥤ A) :
    (restrictToSmallEtaleFinalIso B E h S hS p hp z G).inv ≫
        (restrictionPushforwardComparison B E h S hS p hp ψ G).app
          (op (smallEtaleFinal B E h S hS p z)) ≫
          (restrictToSmallEtale B E h S hS p hp z' G).map
            (finalToBaseChangeFinal B E h S hS p ψ).op =
      G.map ψ.op ≫ (restrictToSmallEtaleFinalIso B E h S hS p hp z' G).inv := by
  have hid : (restrictToSmallEtale B E h S hS p hp z' G).map
          ((SmallEtale.finalIsTerminal E (p.obj z').left.1
            (contains_base B E h S hS p z')).from
              ((smallEtaleBaseChange E (smallEtaleBaseMorphism B E h S hS p ψ)).obj
                (smallEtaleFinal B E h S hS p z))).op ≫
        (restrictToSmallEtale B E h S hS p hp z' G).map
          (finalToBaseChangeFinal B E h S hS p ψ).op =
      𝟙 _ := by
    rw [← Functor.map_comp, ← op_comp,
      show finalToBaseChangeFinal B E h S hS p ψ ≫
          (SmallEtale.finalIsTerminal E (p.obj z').left.1
            (contains_base B E h S hS p z')).from
              ((smallEtaleBaseChange E (smallEtaleBaseMorphism B E h S hS p ψ)).obj
                (smallEtaleFinal B E h S hS p z)) =
            𝟙 (smallEtaleFinal B E h S hS p z') from
        (SmallEtale.finalIsTerminal E (p.obj z').left.1
          (contains_base B E h S hS p z')).hom_ext _ _,
      op_id]
    exact (restrictToSmallEtale B E h S hS p hp z' G).map_id _
  rw [← Category.assoc, restrictToSmallEtaleFinalIso_inv_comp_comparison]
  simp only [Category.assoc]
  rw [hid, Category.comp_id]

/-- The category algebra of `AlgebraicGeometry.Stack.smallEtaleFinalPullbackUnit_comp`, with
every object and arrow abstract: `h1` and `h2` are the two naturality squares and `h3` the
naturality of the unit.

Stating it abstractly keeps the application a single `exact`.  The sections of the direct image
of a presheaf of modules over an object are the sections of that presheaf over the base change of
the object, definitionally but not syntactically, and the chain changes from one spelling to the
other at each of the three junctions. -/
private theorem final_pullback_algebra {C : Type*} [Category C]
    {O₁ O₂ O₃ O₄ O₅ O₆ O₇ O₈ : C}
    (n1 : O₁ ⟶ O₂) (r : O₂ ⟶ O₃) (pu' : O₃ ⟶ O₄) (dd' : O₄ ⟶ O₅)
    (pu'' : O₂ ⟶ O₆) (r2 : O₆ ⟶ O₄) (dd'' : O₆ ⟶ O₇) (pr : O₇ ⟶ O₅)
    (u' : O₁ ⟶ O₈) (n2 : O₈ ⟶ O₆)
    (h1 : r ≫ pu' = pu'' ≫ r2) (h2 : r2 ≫ dd' = dd'' ≫ pr) (h3 : n1 ≫ pu'' = u' ≫ n2) :
    (n1 ≫ r) ≫ pu' ≫ dd' = u' ≫ (n2 ≫ dd'') ≫ pr := by
  rw [Category.assoc, ← Category.assoc r pu' dd', h1, Category.assoc, h2,
    ← Category.assoc n1 pu'', h3]
  simp only [Category.assoc]

/-- **Sections of a map out of the Stacks 06WC pullback, at the final object.**  Let `u : M ⟶ N`
be a morphism of presheaves of modules on the small étale site of the scheme below `z` and let
`d` be a morphism out of the Stacks 06WC pullback of `N`.  Then the Stacks 06WC pullback of `u`
followed by `d`, read on sections over the final object through
`AlgebraicGeometry.Stack.smallEtaleFinalPullbackUnit`, is `u` over the final object followed by
the *mate* of `d` there and a restriction.

This is what replaces a formula for the sections of the pullback: the left-hand side mentions
the pullback, the right-hand side does not.  Both naturality squares and the naturality of the
unit of `CategoryTheory.PresheafOfModules.pullbackPushforwardAdjunction` are used, and nothing
else; in particular neither `u` nor `d` is assumed invertible. -/
public theorem smallEtaleFinalPullbackUnit_comp
    (M N : PresheafOfModules.{u} (SmallEtale.structureSheaf E (p.obj z).left.1
      (contains_base B E h S hS p z)).obj)
    (P : PresheafOfModules.{u} (SmallEtale.structureSheaf E (p.obj z').left.1
      (contains_base B E h S hS p z')).obj)
    (u : M ⟶ N)
    (d : (PresheafOfModules.pullback.{u}
      (smallEtaleStructureComparison B E h S hS p hp ψ τ hτ)).obj N ⟶ P) :
    smallEtaleFinalPullbackUnit B E h S hS p hp τ hτ ψ M ≫
        ((PresheafOfModules.toPresheaf _).map
          ((PresheafOfModules.pullback.{u}
            (smallEtaleStructureComparison B E h S hS p hp ψ τ hτ)).map u ≫ d)).app
            (op (smallEtaleFinal B E h S hS p z')) =
      ((PresheafOfModules.toPresheaf _).map u).app (op (smallEtaleFinal B E h S hS p z)) ≫
        (show N.presheaf.obj (op (smallEtaleFinal B E h S hS p z)) ⟶
            P.presheaf.obj (op ((smallEtaleBaseChange E
              (smallEtaleBaseMorphism B E h S hS p ψ)).obj
                (smallEtaleFinal B E h S hS p z))) from
          ((PresheafOfModules.toPresheaf _).map
            ((PresheafOfModules.pullbackPushforwardAdjunction.{u}
              (smallEtaleStructureComparison B E h S hS p hp ψ τ hτ)).homEquiv _ _ d)).app
                (op (smallEtaleFinal B E h S hS p z))) ≫
          P.presheaf.map (finalToBaseChangeFinal B E h S hS p ψ).op := by
  have h3 := congrArg
    (fun α => ((PresheafOfModules.toPresheaf _).map α).app (op (smallEtaleFinal B E h S hS p z)))
    ((PresheafOfModules.pullbackPushforwardAdjunction.{u}
      (smallEtaleStructureComparison B E h S hS p hp ψ τ hτ)).unit.naturality u)
  simp only [Adjunction.homEquiv_unit, Functor.map_comp, NatTrans.comp_app] at h3 ⊢
  unfold smallEtaleFinalPullbackUnit
  exact final_pullback_algebra _ _ _ _ _ _ _ _ _ _
    (((PresheafOfModules.toPresheaf _).map
      ((PresheafOfModules.pullback.{u}
        (smallEtaleStructureComparison B E h S hS p hp ψ τ hτ)).map u)).naturality
      (finalToBaseChangeFinal B E h S hS p ψ).op)
    (((PresheafOfModules.toPresheaf _).map d).naturality
      (finalToBaseChangeFinal B E h S hS p ψ).op)
    h3.symm

/-- `AlgebraicGeometry.Stack.restrictToSmallEtaleFinalIso_inv_comp_comparison_final` with the
identification at `z` moved to the other side. -/
public theorem restrictionPushforwardComparison_app_final {A : Type*} [Category A] (G : 𝒳ᵒᵖ ⥤ A) :
    (restrictionPushforwardComparison B E h S hS p hp ψ G).app
          (op (smallEtaleFinal B E h S hS p z)) ≫
        (restrictToSmallEtale B E h S hS p hp z' G).map
          (finalToBaseChangeFinal B E h S hS p ψ).op =
      (restrictToSmallEtaleFinalIso B E h S hS p hp z G).hom ≫
        G.map ψ.op ≫ (restrictToSmallEtaleFinalIso B E h S hS p hp z' G).inv :=
  (Iso.inv_comp_eq (restrictToSmallEtaleFinalIso B E h S hS p hp z G)).1
    (restrictToSmallEtaleFinalIso_inv_comp_comparison_final B E h S hS p hp ψ G)

/-- **Sections at the final object of the Stacks 06WC pullback followed by the comparison map
`c_ψ` are restriction of `F` along `ψ`.**  Reading
`AlgebraicGeometry.Stack.smallEtaleFinalPullbackUnit` and then the Stacks 06WC pullback of `u`
followed by `c_ψ` is reading `u` over the final object and then `F(ψ)`, conjugated by
`AlgebraicGeometry.Stack.restrictModuleToSmallEtaleFinalIso` at both ends.

`AlgebraicGeometry.Stack.smallEtaleFinalPullbackUnit_comp` turns the left-hand side into the mate
of `c_ψ`, which is the comparison of **Stacks 06W2** by
`AlgebraicGeometry.Stack.restrictModulePullbackComparison_adjunct`, and
`AlgebraicGeometry.Stack.restrictionPushforwardComparison_app_final` evaluates that at the final
object. -/
public theorem smallEtaleFinalPullbackUnit_comp_comparison
    (F : PresheafOfModules.{u} (ringStructureSheafCore B S hS p hp τ hτ).obj)
    (M : PresheafOfModules.{u} (SmallEtale.structureSheaf E (p.obj z).left.1
      (contains_base B E h S hS p z)).obj)
    (u : M ⟶ restrictModuleToSmallEtale B E h S hS p hp z τ hτ F) :
    smallEtaleFinalPullbackUnit B E h S hS p hp τ hτ ψ M ≫
        ((PresheafOfModules.toPresheaf _).map
          ((PresheafOfModules.pullback.{u}
            (smallEtaleStructureComparison B E h S hS p hp ψ τ hτ)).map u ≫
            restrictModulePullbackComparison B E h S hS p hp ψ τ hτ F)).app
            (op (smallEtaleFinal B E h S hS p z')) =
      ((PresheafOfModules.toPresheaf _).map u).app (op (smallEtaleFinal B E h S hS p z)) ≫
        (restrictModuleToSmallEtaleFinalIso B E h S hS p hp z τ hτ F).hom ≫
          F.presheaf.map ψ.op ≫
            (restrictModuleToSmallEtaleFinalIso B E h S hS p hp z' τ hτ F).inv := by
  rw [smallEtaleFinalPullbackUnit_comp B E h S hS p hp τ hτ ψ M _ _ u
    (restrictModulePullbackComparison B E h S hS p hp ψ τ hτ F),
    restrictModulePullbackComparison_adjunct]
  exact congrArg
    (fun t => ((PresheafOfModules.toPresheaf _).map u).app
      (op (smallEtaleFinal B E h S hS p z)) ≫ t)
    (restrictionPushforwardComparison_app_final B E h S hS p hp ψ F.presheaf)

/-- The adjunct `AlgebraicGeometry.Stack.sheafifiedRestrictComparison` of the comparison map
`c_ψ` of **Stacks 06WC** is characterized by its transpose: precomposing with the unit of
`CategoryTheory.PresheafOfModules.sheafificationAdjunction` returns `c_ψ`. -/
public theorem unit_comp_map_sheafifiedRestrictComparison
    (F : PresheafOfModules.{u} (ringStructureSheafCore B S hS p hp (etaleTopology B)
      (etaleTopology_le_topology B)).obj)
    (hMz' : Presheaf.IsSheaf (SmallEtale.topology E (p.obj z').left.1
        (contains_base B E h S hS p z'))
      (restrictModuleToSmallEtale B E h S hS p hp z' (etaleTopology B)
        (etaleTopology_le_topology B) F).presheaf) :
    (PresheafOfModules.sheafificationAdjunction
          (𝟙 (SmallEtale.structureSheaf E (p.obj z').left.1
            (contains_base B E h S hS p z')).obj)).unit.app
          ((PresheafOfModules.pullback.{u}
            (smallEtaleStructureComparison B E h S hS p hp ψ (etaleTopology B)
              (etaleTopology_le_topology B))).obj
            (restrictModuleToSmallEtale B E h S hS p hp z (etaleTopology B)
              (etaleTopology_le_topology B) F)) ≫
        (SheafOfModules.forget _ ⋙ PresheafOfModules.restrictScalars (𝟙 _)).map
          (sheafifiedRestrictComparison B E h S hS p hp F ψ hMz') =
      restrictModulePullbackComparison B E h S hS p hp ψ (etaleTopology B)
        (etaleTopology_le_topology B) F :=
  ((PresheafOfModules.sheafificationAdjunction
    (𝟙 (SmallEtale.structureSheaf E (p.obj z').left.1
      (contains_base B E h S hS p z')).obj)).homEquiv_unit _ _ _).symm.trans
    (Equiv.apply_symm_apply _ _)

/-- The category algebra of `AlgebraicGeometry.Stack.unit_comp_map_sheafifiedFactor`, with every
object and arrow abstract: a map out of a sheafification, precomposed with the sheafification
unit, is read off the naturality of that unit and the adjunct characterization of the second
factor. -/
private theorem sheafified_factor_algebra {C : Type*} [Category C] {O₁ O₂ O₃ O₄ O₅ : C}
    (etaP : O₁ ⟶ O₂) (sv : O₂ ⟶ O₃) (rw' : O₃ ⟶ O₄) (v : O₁ ⟶ O₅)
    (etaQ : O₅ ⟶ O₃) (c : O₅ ⟶ O₄)
    (hnat : v ≫ etaQ = etaP ≫ sv) (hadj : etaQ ≫ rw' = c) :
    etaP ≫ sv ≫ rw' = v ≫ c := by
  rw [← Category.assoc, ← hnat, Category.assoc, hadj]

variable (F : PresheafOfModules.{u} (ringStructureSheafCore B S hS p hp (etaleTopology B)
  (etaleTopology_le_topology B)).obj)

/-- **Factors 3 and 4 of the Stacks 076T identification, transposed.**  The sheafified Stacks
06WC pullback of `u` followed by `AlgebraicGeometry.Stack.sheafifiedRestrictComparison`, both
morphisms of *sheaves* of modules, is determined by its composite with the sheafification unit,
and that composite is the Stacks 06WC pullback of `u` followed by the comparison map `c_ψ` —
with no sheafification left in it.

The middle factor is spelled as a sheafification of a pullback of presheaves of modules rather
than as `AlgebraicGeometry.Stack.sheafifiedPullbackComparison`, exactly as
`AlgebraicGeometry.Stack.liftedSmallEtaleSheafInv_eq` spells it: the two are definitionally equal,
but the functor spelling records the object of the composite in a form which does not elaborate
against `AlgebraicGeometry.Stack.sheafifiedRestrictComparison`. -/
public theorem unit_comp_map_sheafifiedFactor
    (hMz' : Presheaf.IsSheaf (SmallEtale.topology E (p.obj z').left.1
        (contains_base B E h S hS p z'))
      (restrictModuleToSmallEtale B E h S hS p hp z' (etaleTopology B)
        (etaleTopology_le_topology B) F).presheaf)
    (M : PresheafOfModules.{u} (SmallEtale.structureSheaf E (p.obj z).left.1
      (contains_base B E h S hS p z)).obj)
    (u : M ⟶ restrictModuleToSmallEtale B E h S hS p hp z (etaleTopology B)
      (etaleTopology_le_topology B) F) :
    (PresheafOfModules.sheafificationAdjunction
          (𝟙 (SmallEtale.structureSheaf E (p.obj z').left.1
            (contains_base B E h S hS p z')).obj)).unit.app
          ((PresheafOfModules.pullback.{u}
            (smallEtaleStructureComparison B E h S hS p hp ψ (etaleTopology B)
              (etaleTopology_le_topology B))).obj M) ≫
        (SheafOfModules.forget _ ⋙ PresheafOfModules.restrictScalars (𝟙 _)).map
          ((PresheafOfModules.sheafification
                (𝟙 (SmallEtale.structureSheaf E (p.obj z').left.1
                  (contains_base B E h S hS p z')).obj)).map
              ((PresheafOfModules.pullback.{u}
                (smallEtaleStructureComparison B E h S hS p hp ψ (etaleTopology B)
                  (etaleTopology_le_topology B))).map u) ≫
            sheafifiedRestrictComparison B E h S hS p hp F ψ hMz') =
      (PresheafOfModules.pullback.{u}
            (smallEtaleStructureComparison B E h S hS p hp ψ (etaleTopology B)
              (etaleTopology_le_topology B))).map u ≫
        restrictModulePullbackComparison B E h S hS p hp ψ (etaleTopology B)
          (etaleTopology_le_topology B) F := by
  rw [Functor.map_comp]
  exact sheafified_factor_algebra _ _ _ _ _ _
    ((PresheafOfModules.sheafificationAdjunction
      (𝟙 (SmallEtale.structureSheaf E (p.obj z').left.1
        (contains_base B E h S hS p z')).obj)).unit.naturality
      ((PresheafOfModules.pullback.{u}
        (smallEtaleStructureComparison B E h S hS p hp ψ (etaleTopology B)
          (etaleTopology_le_topology B))).map u))
    (unit_comp_map_sheafifiedRestrictComparison B E h S hS p hp ψ F hMz')

/-- **Sections of a sheafified Stacks 06WC pullback at the final object, for the Stacks 076T
chain.**  For a morphism `u` of presheaves of modules from `M` to the small étale restriction of
`F` at `z` — the underlying morphism of presheaves of
`AlgebraicGeometry.Stack.liftedSmallEtaleSheafInv` being such a `u` — the sheafified Stacks 06WC
pullback of `u` followed by the adjunct of `c_ψ`, read on sections over the final object of the
small étale site of the scheme below `z'` through
`AlgebraicGeometry.Stack.smallEtaleFinalPullbackUnit` and the sheafification unit, is `u` over
the final object below `z` followed by restriction of `F` along `ψ`.

This is the passage from the composition law for factors 2, 3 and 4 of
`AlgebraicGeometry.Stack.liftedSectionsIso`, which
`AlgebraicGeometry.Stack.liftedSmallEtaleSheafInv_comp` has at the level of sheaves of modules, to
sections over the final object, which is the form
`AlgebraicGeometry.Stack.LiftedSectionsFactorFourSquareStandIn` is stated in. -/
public theorem smallEtaleFinalPullbackUnit_comp_sheafifiedFactor
    (hMz' : Presheaf.IsSheaf (SmallEtale.topology E (p.obj z').left.1
        (contains_base B E h S hS p z'))
      (restrictModuleToSmallEtale B E h S hS p hp z' (etaleTopology B)
        (etaleTopology_le_topology B) F).presheaf)
    (M : PresheafOfModules.{u} (SmallEtale.structureSheaf E (p.obj z).left.1
      (contains_base B E h S hS p z)).obj)
    (u : M ⟶ restrictModuleToSmallEtale B E h S hS p hp z (etaleTopology B)
      (etaleTopology_le_topology B) F) :
    smallEtaleFinalPullbackUnit B E h S hS p hp (etaleTopology B)
          (etaleTopology_le_topology B) ψ M ≫
        ((PresheafOfModules.toPresheaf _).map
          ((PresheafOfModules.sheafificationAdjunction
                (𝟙 (SmallEtale.structureSheaf E (p.obj z').left.1
                  (contains_base B E h S hS p z')).obj)).unit.app
              ((PresheafOfModules.pullback.{u}
                (smallEtaleStructureComparison B E h S hS p hp ψ (etaleTopology B)
                  (etaleTopology_le_topology B))).obj M) ≫
            (SheafOfModules.forget _ ⋙ PresheafOfModules.restrictScalars (𝟙 _)).map
              ((PresheafOfModules.sheafification
                    (𝟙 (SmallEtale.structureSheaf E (p.obj z').left.1
                      (contains_base B E h S hS p z')).obj)).map
                  ((PresheafOfModules.pullback.{u}
                    (smallEtaleStructureComparison B E h S hS p hp ψ (etaleTopology B)
                      (etaleTopology_le_topology B))).map u) ≫
                sheafifiedRestrictComparison B E h S hS p hp F ψ hMz'))).app
            (op (smallEtaleFinal B E h S hS p z')) =
      ((PresheafOfModules.toPresheaf _).map u).app (op (smallEtaleFinal B E h S hS p z)) ≫
        (restrictModuleToSmallEtaleFinalIso B E h S hS p hp z (etaleTopology B)
            (etaleTopology_le_topology B) F).hom ≫
          F.presheaf.map ψ.op ≫
            (restrictModuleToSmallEtaleFinalIso B E h S hS p hp z' (etaleTopology B)
              (etaleTopology_le_topology B) F).inv := by
  rw [unit_comp_map_sheafifiedFactor B E h S hS p hp ψ F hMz' M u]
  exact smallEtaleFinalPullbackUnit_comp_comparison B E h S hS p hp (etaleTopology B)
    (etaleTopology_le_topology B) ψ F M u

end AlgebraicGeometry.Stack

end
