module

public import StacksFrontier.Algebra.Homology.DerivedCategory.ExactCompositionQhComparison
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.RestrictionOfDerivedSections

/-! # Restriction in the open of the K-injective comparison of Tag 0D5W

Let `f : X ⟶ Y` be a morphism of ringed spaces, let `V' ⊆ V` be opens of `Y` and let `ρ` be the
restriction map `Γ(V, 𝒪_Y) ⟶ Γ(V', 𝒪_Y)`.  For a K-injective complex `W` of sheaves of
`𝒪_X`-modules, `Stacks.Cohomology.UnboundedHigherDirectImage.preimageSectionsKInjectiveIso`
identifies the class of the complex of sections over `f⁻¹ V` with `RΓ(f⁻¹ V, W)`.  This file
proves that this identification is compatible with restriction to `V'`: the square formed by the
two comparisons, the termwise restriction of sections
`Stacks.Cohomology.DerivedSectionsLeray.preimageSectionsRestrict` and the derived restriction
`Stacks.Cohomology.DerivedSectionsLeray.derivedPreimageSectionsRestrict` commutes, the right-hand
column being read through restriction of scalars along `ρ` on derived categories.

This is the second of the three layers of the restriction compatibility of
`Stacks.Cohomology.UnboundedHigherDirectImage.derivedPreimageHomPresheafValueEquiv`; see the
section *What is granted, and why* of
`StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.UniquenessOfASolution`, and the section
*Where the layer-2 square stands* of
`StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.RestrictionOfDerivedSections`, whose
remaining obstruction this file removes.

## Main results

* `Stacks.Cohomology.DerivedSectionsLeray.preimageSectionsKInjectiveIso_restrict`: the square.

## Implementation notes

Both comparisons are written out through
`Stacks.Cohomology.DerivedSectionsLeray.preimageSectionsKInjectiveIso_hom`.  The last leg of the
left-hand side is pushed past the derived restriction by the naturality of
`derivedPreimageSectionsRestrict` along `DerivedCategory.quotientCompQhIso`, and the unit that is
then exposed is absorbed by `derivedPreimageSectionsRestrict_fac_app`; after expanding
`preimageSectionsRestrictUnit` what is left is an identity among the canonical comparisons alone,
in which neither derived sections nor the restriction maps appear.  Its content is the inverse
form of `Stacks.DerivedFunctor.mapDerivedCategoryFactorsh_hom_app_comp_quotientCompQhIso`.

*Why every step is a named lemma.*  Three legs of the two comparisons are morphisms between two
spellings of one object — `HomotopyCategory.quotient ⋙ F.mapHomotopyCategory` applied to a
complex and `F.mapHomologicalComplex ⋙ HomotopyCategory.quotient` applied to it — and they are
identities.  The two spellings are definitionally equal but not interchangeable by a rewriting
tactic here: `HomologicalComplexUpToQuasiIso.Qh` is not exposed, so the crossing is invisible at
the transparency at which `rw`, `simp only` and `dsimp only` re-check the goal, and in particular
`Category.id_comp` does not fire once such a leg has been replaced by an identity.  What does
cross it is `rfl` and `exact`.  So each step of the argument is stated as a lemma in which every
object and morphism is a variable and applied by `exact`: the crossing is then a single
definitional unification instead of a keyed rewrite.  The identity among canonical comparisons is
stated for an arbitrary pair of additive functors and an arbitrary exact one, where it is cheap,
and the concrete square is an instance of it.

## References

* [Stacks Project, Tag 0D5W](https://stacks.math.columbia.edu/tag/0D5W)
* [Stacks Project, Tag 0D68](https://stacks.math.columbia.edu/tag/0D68)

Tags covered: none.  This is a step of a proof, not a clause of a tag statement.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction

namespace Stacks.Cohomology.DerivedSectionsLeray

universe u

attribute [local instance] HasDerivedCategory.standard
  Stacks.Cohomology.HypercohomologyEdge.restrictScalars_preservesFiniteLimits
  Stacks.Cohomology.HypercohomologyEdge.restrictScalars_preservesFiniteColimits

/-! ### Bookkeeping

The composition and associativity steps of the argument, each with every object and morphism a
variable, so that the definitional crossings described in the module documentation are paid by a
single unification when the lemma is applied.
-/

/-- A leg equal to the identity may be dropped. -/
private theorem comp_eq_of_eq_id {C : Type*} [Category C] {P R : C} {b : P ⟶ P} (r : P ⟶ R)
    (hb : b = 𝟙 P) : b ≫ r = r :=
  (congrArg (fun t => t ≫ r) hb).trans (Category.id_comp r)

/-- Transferring a three-fold composite across a square in its first two legs and a square in
its last two. -/
private theorem assoc_transfer {C : Type*} [Category C] {P Q R T U M : C}
    (x : P ⟶ Q) (y : Q ⟶ R) (z : R ⟶ T) (p : P ⟶ U) (q : U ⟶ R) (r : U ⟶ M) (s : M ⟶ T)
    (h₁ : p ≫ q = x ≫ y) (h₂ : q ≫ z = r ≫ s) : x ≫ y ≫ z = p ≫ r ≫ s := by
  rw [← Category.assoc, ← h₁, Category.assoc, h₂]

/-- A composite of three legs whose middle one is the identity is the composite of the other
two. -/
private theorem eq_comp_id_comp {C : Type*} [Category C] {P Q : C} {x : P ⟶ Q} {O : C}
    (a : P ⟶ O) {b : O ⟶ O} (r : O ⟶ Q) (hx : x = a ≫ b ≫ r) (hb : b = 𝟙 O) : x = a ≫ r :=
  hx.trans (congrArg (fun t => a ≫ t) (comp_eq_of_eq_id r hb))

/-- Composing a factorization `x ≫ v = t` with a square `y ≫ z = v ≫ w`. -/
private theorem comp_fac {C : Type*} [Category C] {O₁ O₂ O₃ O₄ O₅ : C}
    {x : O₁ ⟶ O₂} {y : O₂ ⟶ O₃} {z : O₃ ⟶ O₄} {v : O₂ ⟶ O₅} {w : O₅ ⟶ O₄} {t : O₁ ⟶ O₅}
    (h₁ : y ≫ z = v ≫ w) (h₂ : x ≫ v = t) : x ≫ y ≫ z = t ≫ w := by
  rw [h₁, ← Category.assoc, h₂]

/-- The image under a functor of a composite of three legs. -/
private theorem map_comp₃ {C D : Type*} [Category C] [Category D] (H : C ⥤ D)
    {O₁ O₂ O₃ O₄ : C} {x : O₁ ⟶ O₄} {a : O₁ ⟶ O₂} {b : O₂ ⟶ O₃} {c : O₃ ⟶ O₄}
    (h : x = a ≫ b ≫ c) : H.map x = H.map a ≫ H.map b ≫ H.map c := by
  rw [h, H.map_comp, H.map_comp]

/-- **The shape of the final assembly.**  `hB` is the square for the unit, `hU` expands the
transformation prescribing the derived restriction into its four legs, and `hD` is the identity
among the canonical comparisons; together they give the square. -/
private theorem assemble {C : Type*} [Category C] {O₁ O₂ O₃ O₄ O₅ O₆ O₇ O₈ O₉ Oa Ob : C}
    (P : O₁ ⟶ O₂) (cU : O₂ ⟶ O₃) (d : O₃ ⟶ O₄) (Rm : O₄ ⟶ O₅) (t : O₂ ⟶ O₉)
    (u1 : O₂ ⟶ O₆) (u2 : O₆ ⟶ O₇) (u3 : O₇ ⟶ O₈) (u4 : O₈ ⟶ O₉) (md : O₉ ⟶ O₅)
    (nu : O₁ ⟶ Oa) (fi : Oa ⟶ Ob) (mp : Ob ⟶ O₈)
    (hB : cU ≫ d ≫ Rm = t ≫ md) (hU : t = u1 ≫ u2 ≫ u3 ≫ u4)
    (hD : P ≫ u1 ≫ u2 ≫ u3 = nu ≫ fi ≫ mp) :
    (P ≫ cU ≫ d) ≫ Rm = nu ≫ fi ≫ mp ≫ u4 ≫ md := by
  rw [Category.assoc, Category.assoc, hB, hU]
  simp only [Category.assoc]
  rw [reassoc_of% hD]

section Generic

variable {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
  [HasDerivedCategory A] [HasDerivedCategory B]
  (E : A ⥤ B) [E.Additive] [PreservesFiniteLimits E] [PreservesFiniteColimits E]

/-- **The identity among the canonical comparisons, in the direction this square needs.**  The
inverse form of `Stacks.DerivedFunctor.mapDerivedCategoryFactorsh_hom_app_comp_quotientCompQhIso`:
both sides there are composites of isomorphisms, so inverting the two composites exchanges the
factorization through the homotopy category for the factorization through complexes. -/
private theorem factorsh_inv_app_quotient_obj (K : CochainComplex A ℤ) :
    (DerivedCategory.quotientCompQhIso B).inv.app
          ((E.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ≫
        E.mapDerivedCategoryFactorsh.inv.app
          ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K) =
      E.mapDerivedCategoryFactors.inv.app K ≫
        E.mapDerivedCategory.map ((DerivedCategory.quotientCompQhIso A).inv.app K) :=
  congrArg (fun i => Iso.inv i)
    (show E.mapDerivedCategoryFactorsh.app
            ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K) ≪≫
          (DerivedCategory.quotientCompQhIso B).app
            ((E.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) =
        E.mapDerivedCategory.mapIso ((DerivedCategory.quotientCompQhIso A).app K) ≪≫
          E.mapDerivedCategoryFactors.app K from
      Iso.ext
        (Stacks.DerivedFunctor.mapDerivedCategoryFactorsh_hom_app_comp_quotientCompQhIso E K))

end Generic

section IdentityLeg

/-- `DerivedCategory.Qh` sends an endomorphism that is the identity to the identity. -/
private theorem Qh_map_eq_id_of_eq_id {B : Type*} [Category B] [Abelian B] [HasDerivedCategory B]
    {Z : HomotopyCategory B (ComplexShape.up ℤ)} {g : Z ⟶ Z} (h : g = 𝟙 Z) :
    DerivedCategory.Qh.map g = 𝟙 (DerivedCategory.Qh.obj Z) :=
  (congrArg (fun t => DerivedCategory.Qh.map t) h).trans (DerivedCategory.Qh.map_id _)

variable {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
  [HasDerivedCategory B] (E : A ⥤ B) [E.Additive]

/-- **A leg of the comparison of Tag 0D5W that contributes nothing.**
`CategoryTheory.Functor.mapHomotopyCategoryFactors` is `CategoryTheory.Quotient.lift.isLift`,
whose components are identities, so its image under the localization of the homotopy category is
an identity. -/
private theorem Qh_map_mapHomotopyCategoryFactors_inv_app (K : CochainComplex A ℤ) :
    DerivedCategory.Qh.map ((E.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).inv.app K) =
      𝟙 (DerivedCategory.Qh.obj ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj
        ((E.mapHomologicalComplex (ComplexShape.up ℤ)).obj K))) :=
  Qh_map_eq_id_of_eq_id rfl

end IdentityLeg

section Square

variable {S A A' : Type*} [Category S] [Category A] [Category A']
  [Abelian S] [Abelian A] [Abelian A']
  [HasDerivedCategory S] [HasDerivedCategory A] [HasDerivedCategory A']
  (F : S ⥤ A) (F' : S ⥤ A') (G : A' ⥤ A) [F.Additive] [F'.Additive] [G.Additive]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  (τ : F ⟶ F' ⋙ G) (W : CochainComplex S ℤ)

omit [HasDerivedCategory S] in
/-- **The identity among the canonical comparisons that the square reduces to.**  For additive
`F : S ⥤ A` and `F' : S ⥤ A'`, an exact additive `G : A' ⥤ A` and a transformation
`τ : F ⟶ F' ⋙ G`, the three legs of the transformation prescribing a derived restriction —
the termwise `τ` on the homotopy category, the comparison of the degreewise actions of `F' ⋙ G`
and of `F'` followed by `G`, and the factorization of `G.mapDerivedCategory` through the homotopy
category — compose with the comparison of the two localizations at `F(W)` to the termwise `τ` on
complexes followed by the factorization of `G.mapDerivedCategory` through complexes.

Neither derived sections nor any restriction map occurs here: this is the whole content of
`preimageSectionsKInjectiveIso_restrict` beyond the universal property of the derived functor. -/
private theorem restrict_canonical_square :
    (DerivedCategory.quotientCompQhIso A).inv.app
          ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj W) ≫
        DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory τ (ComplexShape.up ℤ)).app
            ((HomotopyCategory.quotient S (ComplexShape.up ℤ)).obj W)) ≫
          DerivedCategory.Qh.map ((Functor.mapHomotopyCategoryCompIso (Iso.refl (F' ⋙ G))
                (ComplexShape.up ℤ)).inv.app
              ((HomotopyCategory.quotient S (ComplexShape.up ℤ)).obj W)) ≫
            G.mapDerivedCategoryFactorsh.inv.app
              ((F'.mapHomotopyCategory (ComplexShape.up ℤ)).obj
                ((HomotopyCategory.quotient S (ComplexShape.up ℤ)).obj W)) =
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex τ (ComplexShape.up ℤ)).app W) ≫
        G.mapDerivedCategoryFactors.inv.app
            ((F'.mapHomologicalComplex (ComplexShape.up ℤ)).obj W) ≫
          G.mapDerivedCategory.map ((DerivedCategory.quotientCompQhIso A').inv.app
            ((F'.mapHomologicalComplex (ComplexShape.up ℤ)).obj W)) := by
  have hu2 : DerivedCategory.Qh.map ((Functor.mapHomotopyCategoryCompIso (Iso.refl (F' ⋙ G))
          (ComplexShape.up ℤ)).inv.app
        ((HomotopyCategory.quotient S (ComplexShape.up ℤ)).obj W)) =
      𝟙 (DerivedCategory.Qh.obj ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj
        (((F' ⋙ G).mapHomologicalComplex (ComplexShape.up ℤ)).obj W))) :=
    Qh_map_eq_id_of_eq_id rfl
  have hid : DerivedCategory.Qh.map ((Functor.mapHomotopyCategoryCompIso (Iso.refl (F' ⋙ G))
            (ComplexShape.up ℤ)).inv.app
          ((HomotopyCategory.quotient S (ComplexShape.up ℤ)).obj W)) ≫
        G.mapDerivedCategoryFactorsh.inv.app
          ((F'.mapHomotopyCategory (ComplexShape.up ℤ)).obj
            ((HomotopyCategory.quotient S (ComplexShape.up ℤ)).obj W)) =
      G.mapDerivedCategoryFactorsh.inv.app
        ((F'.mapHomotopyCategory (ComplexShape.up ℤ)).obj
          ((HomotopyCategory.quotient S (ComplexShape.up ℤ)).obj W)) :=
    comp_eq_of_eq_id _ hu2
  have hnat : DerivedCategory.Q.map
          ((NatTrans.mapHomologicalComplex τ (ComplexShape.up ℤ)).app W) ≫
        (DerivedCategory.quotientCompQhIso A).inv.app
          (((F' ⋙ G).mapHomologicalComplex (ComplexShape.up ℤ)).obj W) =
      (DerivedCategory.quotientCompQhIso A).inv.app
          ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj W) ≫
        DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory τ (ComplexShape.up ℤ)).app
          ((HomotopyCategory.quotient S (ComplexShape.up ℤ)).obj W)) :=
    (DerivedCategory.quotientCompQhIso A).inv.naturality _
  have hfh : (DerivedCategory.quotientCompQhIso A).inv.app
          (((F' ⋙ G).mapHomologicalComplex (ComplexShape.up ℤ)).obj W) ≫
        G.mapDerivedCategoryFactorsh.inv.app
          ((F'.mapHomotopyCategory (ComplexShape.up ℤ)).obj
            ((HomotopyCategory.quotient S (ComplexShape.up ℤ)).obj W)) =
      G.mapDerivedCategoryFactors.inv.app ((F'.mapHomologicalComplex (ComplexShape.up ℤ)).obj W) ≫
        G.mapDerivedCategory.map ((DerivedCategory.quotientCompQhIso A').inv.app
          ((F'.mapHomologicalComplex (ComplexShape.up ℤ)).obj W)) :=
    factorsh_inv_app_quotient_obj G ((F'.mapHomologicalComplex (ComplexShape.up ℤ)).obj W)
  rw [hid]
  exact assoc_transfer _ _ _ _ _ _ _ hnat hfh

end Square

variable {X Y : RingedSpace.{u, u}}

/-- **The comparison of Tag 0D5W at a K-injective complex, in normal form.**
`Stacks.Cohomology.DerivedSectionsLeray.preimageSectionsKInjectiveIso_hom` with the leg that is
an identity removed, leaving the comparison of the two localizations, the unit of `RΓ(f⁻¹ V, -)`
and the image of that comparison. -/
private theorem preimageSectionsKInjectiveIso_hom_eq (f : X ⟶ Y) (V₀ : Opens Y.carrier)
    (W : CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ) (hW : W.IsKInjective) :
    (Stacks.Cohomology.UnboundedHigherDirectImage.preimageSectionsKInjectiveIso f V₀ W hW).hom =
      (DerivedCategory.quotientCompQhIso
            (ModuleCat.{u} ((structureSheafRing Y).obj.obj (op V₀)))).inv.app
          (((preimageSections f V₀).mapHomologicalComplex (ComplexShape.up ℤ)).obj W) ≫
        (derivedPreimageSectionsUnit f V₀).app
            ((HomotopyCategory.quotient (SheafOfModules.{u} (structureSheafRing X))
              (ComplexShape.up ℤ)).obj W) ≫
          (derivedPreimageSections f V₀).map
            ((DerivedCategory.quotientCompQhIso
              (SheafOfModules.{u} (structureSheafRing X))).hom.app W) :=
  eq_comp_id_comp _ _ (preimageSectionsKInjectiveIso_hom f V₀ W hW)
    (Qh_map_mapHomotopyCategoryFactors_inv_app (preimageSections f V₀) W)

/-- `Stacks.Cohomology.DerivedSectionsLeray.preimageSectionsRestrictUnit` at an object of the
homotopy category, as the composite of its four legs.  It holds by `rfl`. -/
private theorem preimageSectionsRestrictUnit_app (f : X ⟶ Y) {V V' : Opens Y.carrier}
    (hV : V' ≤ V)
    (Z : HomotopyCategory (SheafOfModules.{u} (structureSheafRing X)) (ComplexShape.up ℤ)) :
    (preimageSectionsRestrictUnit f hV).app Z =
      DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory (preimageSectionsRestrict f hV)
          (ComplexShape.up ℤ)).app Z) ≫
        DerivedCategory.Qh.map ((Functor.mapHomotopyCategoryCompIso
            (Iso.refl (preimageSections f V' ⋙
              ModuleCat.restrictScalars ((structureSheafRing Y).obj.map hV.hom.op).hom))
            (ComplexShape.up ℤ)).inv.app Z) ≫
          (ModuleCat.restrictScalars
                ((structureSheafRing Y).obj.map hV.hom.op).hom).mapDerivedCategoryFactorsh.inv.app
              (((preimageSections f V').mapHomotopyCategory (ComplexShape.up ℤ)).obj Z) ≫
            (restrictScalarsDerived Y hV).map ((derivedPreimageSectionsUnit f V').app Z) :=
  rfl

/-- **The derived restriction, composed with the unit of `RΓ(f⁻¹ V, -)` at a quotient object.**
The naturality of `derivedPreimageSectionsRestrict` along `DerivedCategory.quotientCompQhIso`
moves the last leg of the comparison of Tag 0D5W past the derived restriction, and
`derivedPreimageSectionsRestrict_fac_app` then absorbs the unit. -/
private theorem derivedPreimageSectionsUnit_comp_restrict (f : X ⟶ Y)
    {V V' : Opens Y.carrier} (hV : V' ≤ V)
    (W : CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ) :
    (derivedPreimageSectionsUnit f V).app
          ((HomotopyCategory.quotient (SheafOfModules.{u} (structureSheafRing X))
            (ComplexShape.up ℤ)).obj W) ≫
        (derivedPreimageSections f V).map
            ((DerivedCategory.quotientCompQhIso
              (SheafOfModules.{u} (structureSheafRing X))).hom.app W) ≫
          (derivedPreimageSectionsRestrict f hV).app (DerivedCategory.Q.obj W) =
      (preimageSectionsRestrictUnit f hV).app
          ((HomotopyCategory.quotient (SheafOfModules.{u} (structureSheafRing X))
            (ComplexShape.up ℤ)).obj W) ≫
        (restrictScalarsDerived Y hV).map ((derivedPreimageSections f V').map
          ((DerivedCategory.quotientCompQhIso
            (SheafOfModules.{u} (structureSheafRing X))).hom.app W)) :=
  comp_fac
    ((derivedPreimageSectionsRestrict f hV).naturality
      ((DerivedCategory.quotientCompQhIso (SheafOfModules.{u} (structureSheafRing X))).hom.app W))
    (derivedPreimageSectionsRestrict_fac_app f hV _)

/-- **Restriction in the open of the comparison of Tag 0D5W at a K-injective complex.**  For
`V' ≤ V` and a K-injective complex `W` of sheaves of `𝒪_X`-modules, the identification of the
class of the complex of sections over `f⁻¹ V` with `RΓ(f⁻¹ V, W)` carries the termwise
restriction of sections to the derived restriction, both read as morphisms into restriction of
scalars along `ρ : Γ(V, 𝒪_Y) ⟶ Γ(V', 𝒪_Y)`.

The comparison `CategoryTheory.Functor.mapDerivedCategoryFactors` enters through its inverse: it
runs `Q ⋙ Res_ρ.mapDerivedCategory ≅ Res_ρ.mapHomologicalComplex ⋙ Q`, and this square needs the
other direction.

This is a step of the proof of the restriction compatibility of
`Stacks.Cohomology.UnboundedHigherDirectImage.derivedPreimageHomPresheafValueEquiv`, not a clause
of a tag statement, and so carries no tag attribute. -/
theorem preimageSectionsKInjectiveIso_restrict (f : X ⟶ Y) {V V' : Opens Y.carrier} (hV : V' ≤ V)
    (W : CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ) (hW : W.IsKInjective) :
    (Stacks.Cohomology.UnboundedHigherDirectImage.preimageSectionsKInjectiveIso f V W hW).hom ≫
        (derivedPreimageSectionsRestrict f hV).app (DerivedCategory.Q.obj W) =
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex (preimageSectionsRestrict f hV)
            (ComplexShape.up ℤ)).app W) ≫
        (ModuleCat.restrictScalars
              ((structureSheafRing Y).obj.map hV.hom.op).hom).mapDerivedCategoryFactors.inv.app
            (((preimageSections f V').mapHomologicalComplex (ComplexShape.up ℤ)).obj W) ≫
          (restrictScalarsDerived Y hV).map
            (Stacks.Cohomology.UnboundedHigherDirectImage.preimageSectionsKInjectiveIso
              f V' W hW).hom := by
  rw [preimageSectionsKInjectiveIso_hom_eq f V W hW,
    map_comp₃ (restrictScalarsDerived Y hV) (preimageSectionsKInjectiveIso_hom_eq f V' W hW)]
  exact assemble _ _ _ _ _ _ _ _ _ _ _ _ _
    (derivedPreimageSectionsUnit_comp_restrict f hV W)
    (preimageSectionsRestrictUnit_app f hV _)
    (restrict_canonical_square (preimageSections f V) (preimageSections f V')
      (ModuleCat.restrictScalars ((structureSheafRing Y).obj.map hV.hom.op).hom)
      (preimageSectionsRestrict f hV) W)

end Stacks.Cohomology.DerivedSectionsLeray

end
