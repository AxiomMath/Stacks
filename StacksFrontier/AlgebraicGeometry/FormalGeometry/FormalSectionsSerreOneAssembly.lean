module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.ComplementFormalFunctions
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.ComplementQuotientTower
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.FormalSectionsSerreOneRealization
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.QuotientRestriction
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.SectionsOffVanishing
public import StacksFrontier.Homology.DerivedComplete.NormalizedDerivedLimitMilnor

/-!
# Threading Stacks 0BLX through to the comparison map of Stacks 0EG2

`Stacks.Algebraization.CompletedComplementIsFormalSections` — Stacks 0BLX in the shape the proof
of Stacks 0EIF consumes — asserts that the derived `I`-adic completion of `RΓ(V, M̃)` is a derived
limit of the tower `n ↦ RΓ(V, (M/IⁿM)^~)` on `V = Spec(A) ∖ V(J)`, with normalized projections.
Its Milnor sequence therefore surjects `H⁰(RΓ(V, M̃)^∧)` onto `lim H⁰(RΓ(V, (M/IⁿM)^~))`.

This file builds the identification that turns that surjection into the realization statement of
Stacks 0EIF: it identifies the tower `n ↦ H⁰(RΓ(V, (M/IⁿM)^~))` of `A`-modules with the tower
`Stacks.Algebraization.formalSections` of abelian groups whose limit
`Stacks.Algebraization.comparisonAt` maps into, compatibly with the reduction maps on both sides.

## The two seams, and that neither is where it was recorded to be

The route note of
`StacksFrontier.AlgebraicGeometry.FormalGeometry.FormalSectionsSerreOneRealization` records one
seam:
`comparisonAt` and `Stacks.Algebraization.sectionsNearVanishing` are valued in `Ab` while
`Stacks.Algebraization.sectionsOffVanishingIso` is an isomorphism of `A`-modules, with the
`U`-side and `Spec A`-side `A`-module structures not identified by `rfl` because
`AlgebraicGeometry.Scheme.Modules.restrictFunctor` goes through an unexposed `appIso.inv`.

**That seam does not have to be crossed, and no `appIso.inv` has to be exposed.** The obstruction
is real for the `A`-module structures and irrelevant here, because the comparison map is a map of
abelian groups: after `forget₂ (ModuleCat A) Ab` the two descriptions are *equal*, not merely
isomorphic, and `Stacks.Algebraization.assemblySectionsIso` and
`Stacks.Algebraization.assemblyTowerIso` use that equality by `rfl`.

The seam that is real is a different one, and it is not recorded anywhere: the two spellings
`Stacks.LocalCohomology.complementTilde` and `Stacks.Algebraization.restrictedTildeFunctor` of
`M̃|_U` are definitionally equal but expensive to unify, so a statement mixing them exhausts the
elaborator's budget. `Stacks.Algebraization.complementTilde_eq_restrictedTildeFunctor_obj` records
the equality once, and everything here is stated in the second spelling.

## Main definitions

* `Stacks.Algebraization.quotientTowerAt` — the tower `n ↦ Γ(V, F / Iⁿ F)` of sections over one
  neighbourhood of the formal locus.
* `Stacks.Algebraization.complementHomologyZeroSectionsNatIso`,
  `Stacks.Algebraization.complementSectionsOffVanishingIso` — degree-zero cohomology of derived
  sections on `V`, as the sections of `M̃|_U` over the open `U ∖ V(J)` of `U`, naturally in the
  module.
* `Stacks.Algebraization.assemblyTowerIso` — **the tower comparison**: the tower
  `n ↦ H⁰(RΓ(V, (M/IⁿM)^~))` is `Stacks.Algebraization.formalSections`.
* `Stacks.Algebraization.assemblySectionsIso` — the comparison at the cone point.

## Main results

* `Stacks.Algebraization.formalSectionsResIso` — restriction identifies
  `Stacks.Algebraization.formalSections` with the sections over a single neighbourhood. This is
  what makes the passage from sections over `V` to sections over `U` free, and it is the
  isomorphism `Stacks.Algebraization.resNearVanishing` that `Stacks.Algebraization.comparisonAt`
  already inverts.
* `Stacks.Algebraization.adicProj_comp_adicQuotientSystemRestrictedTildeIso_sections` — **the
  tower comparison is normalized against the reduction maps**, which is what lets the Milnor
  comparison map be identified with `comparisonAt` rather than merely compared with it.
* `Stacks.Algebraization.assemblySectionsIso_hom_comp_formalSectionsCone_π` — **the commuting
  square**: the cone-point comparison carries the level-`n` leg of
  `Stacks.Algebraization.formalSectionsCone` to the map induced by `M ⟶ M/IⁿM`, read through the
  tower comparison. This is what identifies the Milnor comparison map with
  `Stacks.Algebraization.comparisonAt` rather than merely comparing the two.
* `Stacks.Algebraization.forget₂_sectionsOffVanishingFunctor_map` — the two readings of a map on
  sections over `V` are *equal* after `forget₂ (ModuleCat A) Ab`.
* `Stacks.Algebraization.surjective_of_isIso_square` — transport of surjectivity along a commuting
  square of isomorphisms.

## References

* [Stacks Project, Tag 0EIF](https://stacks.math.columbia.edu/tag/0EIF)
* [Stacks Project, Tag 0EG2](https://stacks.math.columbia.edu/tag/0EG2)
* [Stacks Project, Tag 0BLX](https://stacks.math.columbia.edu/tag/0BLX)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.Algebraization

open Stacks.LocalCohomology

/-! ### Transport of surjectivity along a commuting square of isomorphisms -/

/-- Surjectivity transports along a commuting square whose vertical maps are isomorphisms. -/
public theorem surjective_of_isIso_square {X Y X' Y' : Ab.{u}} (f : X ⟶ Y) (g : X' ⟶ Y')
    (u : X ≅ X') (v : Y ≅ Y') (hcomm : f ≫ v.hom = u.hom ≫ g)
    (hf : Function.Surjective (ConcreteCategory.hom f)) :
    Function.Surjective (ConcreteCategory.hom g) := by
  intro y'
  obtain ⟨x, hx⟩ := hf (ConcreteCategory.hom v.inv y')
  refine ⟨ConcreteCategory.hom u.hom x, ?_⟩
  have hsq := ConcreteCategory.congr_hom hcomm x
  simp only [ConcreteCategory.comp_apply] at hsq
  rw [← hsq, hx]
  exact ConcreteCategory.congr_hom v.inv_hom_id y'

/-! ### Reassociation across a normalized bridge

The two lemmas here do the associativity bookkeeping of the commuting square at the end of this
file. They are stated over an abstract category on purpose: the square mixes the two spellings
`Stacks.LocalCohomology.complementTilde` and `Stacks.Algebraization.restrictedTildeFunctor` of
`M̃|_U`, which are definitionally equal but not syntactically so, and `rewrite` abstracts a motive
that is then rejected at `implicit` transparency. Instantiating an abstract identity is a plain
application and crosses that seam for free. -/

/-- If `h ≫ g = α ≫ t` and `t` factors through an isomorphism as `p ≫ e.hom`, then
`α ≫ p = h ≫ g ≫ e.inv`. -/
private theorem comp_eq_comp_comp_inv_of_comp_hom {C : Type*} [Category C] {W X Y Z T : C}
    {α : W ⟶ X} {p : X ⟶ Y} {h : W ⟶ T} {g : T ⟶ Z} {t : X ⟶ Z} (e : Y ≅ Z)
    (h₁ : h ≫ g = α ≫ t) (h₂ : p ≫ e.hom = t) :
    α ≫ p = h ≫ g ≫ e.inv := by
  rw [← Category.assoc, h₁, ← h₂, Category.assoc, Category.assoc, e.hom_inv_id,
    Category.comp_id]

/-- A square commuting as `α ≫ p = h ≫ g ≫ δ` still commutes after both legs are followed by
one further map. -/
private theorem comp_comp_eq_of_comp_eq {C : Type*} [Category C] {W X Y Z T V : C}
    {α : W ⟶ X} {p : X ⟶ Y} {h : W ⟶ T} {g : T ⟶ Z} {δ : Z ⟶ Y} (r : Y ⟶ V)
    (k : α ≫ p = h ≫ g ≫ δ) :
    α ≫ p ≫ r = h ≫ g ≫ δ ≫ r := by
  rw [← Category.assoc, k, Category.assoc, Category.assoc]

/-! ### The inverse system of sections on one neighbourhood -/

variable (A : Type u) [CommRing A] (I a : Ideal A)
  (F : (complementZeroLocus A a : Scheme).Modules)

/-- The inverse system `n ↦ Γ(V, F / Iⁿ F)` of sections of the ideal-power quotients over a single
neighbourhood `V` of the formal locus. For `V = ⊤` this is `Stacks.Algebraization.formalSections`,
and restriction identifies the two for every `V`. -/
public def quotientTowerAt (V : OpensNearVanishing A I a) : ℕᵒᵖ ⥤ Ab.{u} :=
  quotientSystemNearVanishing A I a F ⋙
    Scheme.Modules.toPresheaf _ ⋙ (CategoryTheory.evaluation _ Ab.{u}).obj (op V.openSet)

/-- **Restriction identifies the formal sections with the sections on a single neighbourhood.**
Each component is `Stacks.Algebraization.resNearVanishing`, an isomorphism because `F / Iⁿ F`
vanishes off the formal locus. -/
public def formalSectionsResIso (V : OpensNearVanishing A I a) :
    formalSections A I a F ≅ quotientTowerAt A I a F V :=
  NatIso.ofComponents
    (fun n => @asIso _ _ _ _ (resNearVanishing A I a F V n)
      (isIso_quotientSystemNearVanishing_res A I a F V n.unop))
    (fun h => formalSections_map_comp_resNearVanishing A I a F V h)

/-- The components of `Stacks.Algebraization.formalSectionsResIso` are the restriction maps. -/
public theorem formalSectionsResIso_hom_app (V : OpensNearVanishing A I a) (n : ℕᵒᵖ) :
    (formalSectionsResIso A I a F V).hom.app n = resNearVanishing A I a F V n :=
  rfl

/-! ### Degree-zero cohomology of derived sections, read on the open `U ∖ V(J)` of `U` -/

section Sections

variable {A}
variable {J : Ideal A} {hJ : J.FG} (D : LocalizationTriangleData.{u, u} A J hJ)

/-- **Degree-zero cohomology of derived sections on `V` is the sections of the associated sheaf
on `V`**, as an isomorphism of functors. This is
`Stacks.Algebraization.complementCohomologyZeroEquivSections` with its naturality, packaged. -/
public def complementHomologyZeroSectionsNatIso :
    D.complement ⋙ DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0 ≅
      complementSectionsFunctor A J :=
  NatIso.ofComponents
    (fun N => (complementCohomologyZeroEquivSections D N).toModuleIso)
    (fun g => ModuleCat.hom_ext (LinearMap.ext fun x =>
      complementCohomologyZeroEquivSections_naturality D g x))

/-- **Degree-zero cohomology of derived sections on `V = Spec A ∖ V(J)`, read inside
`U = Spec A ∖ V(𝔞)`.** For `J ⊆ 𝔞` the open `V` appears as `U ∖ V(J)`, and this identifies
`H⁰(RΓ(V, Ñ))` with the sections of `Ñ|_U` over that open, naturally in `N`. -/
public def complementSectionsOffVanishingIso (a : Ideal A) (hle : J ≤ a) :
    D.complement ⋙ DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0 ≅
      AlgebraicGeometry.tilde.functor (CommRingCat.of A) ⋙ sectionsOffVanishingFunctor J a :=
  complementHomologyZeroSectionsNatIso D ≪≫
    (Functor.isoWhiskerLeft (AlgebraicGeometry.tilde.functor (CommRingCat.of A))
      (sectionsOffVanishingNatIso J a hle)).symm

end Sections

/-! ### The tower comparison at a neighbourhood cut out by `J` -/

section Assembly

variable (S : AlgebraizationSituation.{u}) (J : Ideal S.A) (hJa : J ≤ S.a)
  (M : ModuleCat.{u} S.A)
  (D : LocalizationTriangleData.{u, u} S.A J J.fg_of_isNoetherianRing)
  (hV : PrimeSpectrum.zeroLocus (J : Set S.A) ∩ PrimeSpectrum.zeroLocus (S.I : Set S.A) =
    PrimeSpectrum.zeroLocus (S.a : Set S.A) ∩ PrimeSpectrum.zeroLocus (S.I : Set S.A))

/-- **The two spellings of `M̃|_U` agree.** `Stacks.LocalCohomology.complementTilde`, which the
comparison map of Stacks 0EG2 is stated against, and
`Stacks.Algebraization.restrictedTildeFunctor`, which the tower bridge of
`StacksFrontier.AlgebraicGeometry.FormalGeometry.ComplementQuotientTower` is stated against, are the
same sheaf of modules.

The equality is definitional — `Stacks.LocalCohomology.restrictFunctor_eq` and
`Stacks.LocalCohomology.associatedSheaf_eq_tilde` are both `rfl` — but checking it unfolds
sheafification, so it is recorded once here and rewritten with, rather than left to unification
inside statements that mix the two spellings. -/
public theorem complementTilde_eq_restrictedTildeFunctor_obj :
    (complementTilde S.A S.a M : (complementZeroLocus S.A S.a : Scheme).Modules) =
      (restrictedTildeFunctor S).obj M :=
  rfl

/-- The neighbourhood of the formal locus cut out by `J`, namely the open `U ∖ V(J)` of `U`. -/
public abbrev opensOffVanishingNearVanishing : OpensNearVanishing S.A S.I S.a :=
  opensNearVanishingOfInterEq S.I S.a J hV

/-- **The tower comparison.** The tower `n ↦ H⁰(RΓ(V, (M/IⁿM)^~))` of degree-zero cohomology of
derived sections on `V = Spec A ∖ V(J)` is the tower `Stacks.Algebraization.formalSections` whose
limit the comparison map of Stacks 0EG2 lands in.

It is the composite of three identifications: degree-zero cohomology of derived sections is
sections, by `Stacks.Algebraization.complementSectionsOffVanishingIso`; the tower of sheafified
module quotients is the sheaf tower of ideal-power quotients, by
`Stacks.Algebraization.adicQuotientSystemRestrictedTildeIso`; and sections over `V` are sections
over `U`, by `Stacks.Algebraization.formalSectionsResIso`. -/
public def assemblyTowerIso :
    (idealPowerQuotientTower.{u, u} S.I M ⋙ D.complement ⋙
        DerivedCategory.homologyFunctor (ModuleCat.{u} S.A) 0) ⋙
      forget₂ (ModuleCat S.A) Ab.{u} ≅
    formalSections S.A S.I S.a ((restrictedTildeFunctor S).obj M) :=
  Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft (idealPowerQuotientTower.{u, u} S.I M)
        (complementSectionsOffVanishingIso D S.a hJa)) (forget₂ (ModuleCat S.A) Ab.{u}) ≪≫
    (Functor.isoWhiskerRight
      (adicQuotientSystemRestrictedTildeIso S M (idealSheafNearVanishing_eq_idealOnOpen S))
      (Scheme.Modules.toPresheaf _ ⋙ (CategoryTheory.evaluation _ Ab.{u}).obj
        (op (opensOffVanishingNearVanishing S J hV).openSet))).symm ≪≫
    (formalSectionsResIso S.A S.I S.a ((restrictedTildeFunctor S).obj M)
      (opensOffVanishingNearVanishing S J hV)).symm

/-- **The cone-point comparison.** Degree-zero cohomology of the derived sections of `M̃` on
`V = Spec A ∖ V(J)` is the group of sections of `M̃|_U` over `V`, read as the open `U ∖ V(J)`
of `U`. -/
public def assemblySectionsIso :=
  (forget₂ (ModuleCat S.A) Ab.{u}).mapIso
    ((complementSectionsOffVanishingIso D S.a hJa).app M)

/-- **The tower comparison is normalized against the reduction maps.** On sections over an open
`W` of `U`, the bridge from the sheaf tower of ideal-power quotients to the sheafified module
quotients carries the quotient projection `M̃|_U ⟶ (M̃|_U)/Iⁿ(M̃|_U)` to the sheafification of
`M ⟶ M/IⁿM`. This is
`Stacks.Algebraization.cokernel_π_comp_adicQuotientSystemRestrictedTildeIso` evaluated at `W`. -/
public theorem adicProj_comp_adicQuotientSystemRestrictedTildeIso_sections (n : ℕᵒᵖ)
    (W : (complementZeroLocus S.A S.a : Scheme).Opens) :
    (Scheme.Modules.toPresheaf _ ⋙
          (CategoryTheory.evaluation _ Ab.{u}).obj (op W)).map
        (adicProj (idealSheafNearVanishing S.A S.I S.a)
          ((restrictedTildeFunctor S).obj M) n) ≫
      (Scheme.Modules.toPresheaf _ ⋙
          (CategoryTheory.evaluation _ Ab.{u}).obj (op W)).map
        ((adicQuotientSystemRestrictedTildeIso S M
          (idealSheafNearVanishing_eq_idealOnOpen S)).hom.app n) =
    (Scheme.Modules.toPresheaf _ ⋙
        (CategoryTheory.evaluation _ Ab.{u}).obj (op W)).map
      ((restrictedTildeFunctor S).map ((idealPowerQuotientCone.{u, u} S.I M).π.app n)) :=
  ((Scheme.Modules.toPresheaf (complementZeroLocus S.A S.a : Scheme) ⋙
      (CategoryTheory.evaluation _ Ab.{u}).obj (op W)).map_comp _ _).symm.trans
    (congrArg (Scheme.Modules.toPresheaf (complementZeroLocus S.A S.a : Scheme) ⋙
        (CategoryTheory.evaluation _ Ab.{u}).obj (op W)).map
      (cokernel_π_comp_adicQuotientSystemRestrictedTildeIso S M
        (idealSheafNearVanishing_eq_idealOnOpen S) n))

/-! ### The commuting square -/

/-- The cone-point comparison is the degree-zero sections comparison, forgotten to `Ab`. -/
public theorem assemblySectionsIso_hom :
    (assemblySectionsIso S J hJa M D).hom =
      (forget₂ (ModuleCat S.A) Ab.{u}).map
        ((complementSectionsOffVanishingIso D S.a hJa).app M).hom :=
  rfl

/-- The inverse of the restriction isomorphism from sections over all of `U` to sections over the
neighbourhood `U ∖ V(J)`, for the sheaf tower of `M̃|_U`. It is the last factor of the tower
comparison and the factor `Stacks.Algebraization.comparisonAt` already inverts, named once so that
the two cancel without the isomorphism instance being resynthesized. -/
public def assemblyResInv (n : ℕᵒᵖ) :
    (quotientTowerAt S.A S.I S.a ((restrictedTildeFunctor S).obj M)
        (opensOffVanishingNearVanishing S J hV)).obj n ⟶
      (formalSections S.A S.I S.a ((restrictedTildeFunctor S).obj M)).obj n :=
  @inv _ _ _ _
    (resNearVanishing S.A S.I S.a ((restrictedTildeFunctor S).obj M)
      (opensOffVanishingNearVanishing S J hV) n)
    (isIso_quotientSystemNearVanishing_res S.A S.I S.a ((restrictedTildeFunctor S).obj M)
      (opensOffVanishingNearVanishing S J hV) n.unop)

/-- The components of the tower comparison, as the composite of the three identifications it is
built from. -/
public theorem assemblyTowerIso_hom_app (n : ℕᵒᵖ) :
    (assemblyTowerIso S J hJa M D hV).hom.app n =
      (forget₂ (ModuleCat S.A) Ab.{u}).map
          ((complementSectionsOffVanishingIso D S.a hJa).app
            ((idealPowerQuotientTower.{u, u} S.I M).obj n)).hom ≫
        (Scheme.Modules.toPresheaf _ ⋙ (CategoryTheory.evaluation _ Ab.{u}).obj
              (op (opensOffVanishingNearVanishing S J hV).openSet)).map
            ((adicQuotientSystemRestrictedTildeIso S M
              (idealSheafNearVanishing_eq_idealOnOpen S)).inv.app n) ≫
          assemblyResInv S J M hV n :=
  rfl

/-- The level-`n` map of the cone `Stacks.Algebraization.formalSectionsCone` on the neighbourhood
`U ∖ V(J)`: the quotient projection read on sections over that open, then the inverse restriction
isomorphism. -/
public theorem formalSectionsCone_π_app_eq (n : ℕᵒᵖ) :
    (formalSectionsCone S.A S.I S.a ((restrictedTildeFunctor S).obj M)
        (opensOffVanishingNearVanishing S J hV)).π.app n =
      (Scheme.Modules.toPresheaf _ ⋙ (CategoryTheory.evaluation _ Ab.{u}).obj
            (op (opensOffVanishingNearVanishing S J hV).openSet)).map
          (adicProj (idealSheafNearVanishing S.A S.I S.a)
            ((restrictedTildeFunctor S).obj M) n) ≫
        assemblyResInv S J M hV n :=
  rfl

/-- **The two readings of a map on sections over `V` agree.** On the open `U ∖ V(J)` of `U`, the
sections of the restricted sheafification `M̃|_U` and the sections of `M̃` over the image of that
open carry the same abelian group and the same induced map: the `A`-module structures differ by an
unexposed `appIso`, and `forget₂ (ModuleCat A) Ab` forgets exactly that. -/
public theorem forget₂_sectionsOffVanishingFunctor_map {M N : ModuleCat.{u} S.A} (η : M ⟶ N) :
    (forget₂ (ModuleCat S.A) Ab.{u}).map
        ((AlgebraicGeometry.tilde.functor (CommRingCat.of S.A) ⋙
          sectionsOffVanishingFunctor J S.a).map η) =
      (Scheme.Modules.toPresheaf _ ⋙ (CategoryTheory.evaluation _ Ab.{u}).obj
          (op (opensOffVanishingNearVanishing S J hV).openSet)).map
        ((restrictedTildeFunctor S).map η) :=
  rfl

/-- **The commuting square, before the restriction isomorphism is inverted.** The cone-point
comparison followed by the quotient projection on sections over `V` is the map induced by
`M ⟶ M/IⁿM`, followed by the cone-point comparison at `M/IⁿM` and the tower bridge.

This is naturality of `Stacks.Algebraization.complementSectionsOffVanishingIso` at `M ⟶ M/IⁿM`,
then the normalization
`Stacks.Algebraization.adicProj_comp_adicQuotientSystemRestrictedTildeIso_sections` on the open
`U ∖ V(J)`. -/
public theorem assemblySectionsIso_hom_comp_adicProj_sections (n : ℕᵒᵖ) :
    (forget₂ (ModuleCat S.A) Ab.{u}).map
          ((complementSectionsOffVanishingIso D S.a hJa).app M).hom ≫
        (Scheme.Modules.toPresheaf _ ⋙ (CategoryTheory.evaluation _ Ab.{u}).obj
              (op (opensOffVanishingNearVanishing S J hV).openSet)).map
          (adicProj (idealSheafNearVanishing S.A S.I S.a)
            ((restrictedTildeFunctor S).obj M) n) =
      (forget₂ (ModuleCat S.A) Ab.{u}).map
          ((DerivedCategory.homologyFunctor (ModuleCat.{u} S.A) 0).map
            (D.complement.map ((idealPowerQuotientCone.{u, u} S.I M).π.app n))) ≫
        (forget₂ (ModuleCat S.A) Ab.{u}).map
            ((complementSectionsOffVanishingIso D S.a hJa).app
              ((idealPowerQuotientTower.{u, u} S.I M).obj n)).hom ≫
          (Scheme.Modules.toPresheaf _ ⋙ (CategoryTheory.evaluation _ Ab.{u}).obj
                (op (opensOffVanishingNearVanishing S J hV).openSet)).map
            ((adicQuotientSystemRestrictedTildeIso S M
              (idealSheafNearVanishing_eq_idealOnOpen S)).inv.app n) :=
  comp_eq_comp_comp_inv_of_comp_hom
    ((Scheme.Modules.toPresheaf (complementZeroLocus S.A S.a : Scheme) ⋙
      (CategoryTheory.evaluation _ Ab.{u}).obj
        (op (opensOffVanishingNearVanishing S J hV).openSet)).mapIso
      ((adicQuotientSystemRestrictedTildeIso S M
        (idealSheafNearVanishing_eq_idealOnOpen S)).app n))
    (((forget₂ (ModuleCat S.A) Ab.{u}).map_comp _ _).symm.trans
      ((congrArg (forget₂ (ModuleCat S.A) Ab.{u}).map
          ((complementSectionsOffVanishingIso D S.a hJa).hom.naturality
            ((idealPowerQuotientCone.{u, u} S.I M).π.app n))).trans
        ((forget₂ (ModuleCat S.A) Ab.{u}).map_comp _ _)))
    ((adicProj_comp_adicQuotientSystemRestrictedTildeIso_sections S M n
        (opensOffVanishingNearVanishing S J hV).openSet).trans
      (forget₂_sectionsOffVanishingFunctor_map S J hV
        ((idealPowerQuotientCone.{u, u} S.I M).π.app n)).symm)

/-- **The commuting square.** The cone-point comparison carries the reduction map of
`Stacks.Algebraization.formalSectionsCone` — reduce modulo `Iⁿ` on `V`, then extend to all of
`U` — to the map `H⁰(RΓ(V, M̃)) ⟶ H⁰(RΓ(V, (M/IⁿM)^~))` induced by `M ⟶ M/IⁿM`, read through the
tower comparison.

This is what identifies the Milnor comparison map of
`Stacks.Algebraization.CompletedComplementIsFormalSections` with
`Stacks.Algebraization.comparisonAt` rather than merely comparing the two: the square's two
horizontal maps are the level-`n` components of the two cones, and its two vertical maps are
isomorphisms.

The proof is naturality of `Stacks.Algebraization.complementSectionsOffVanishingIso` at
`M ⟶ M/IⁿM` followed by the normalization
`Stacks.Algebraization.adicProj_comp_adicQuotientSystemRestrictedTildeIso_sections`; the inverse
restriction isomorphism built into `formalSectionsCone` is the last factor of the tower
comparison, so it cancels on both sides without being inspected. -/
public theorem assemblySectionsIso_hom_comp_formalSectionsCone_π (n : ℕᵒᵖ) :
    (assemblySectionsIso S J hJa M D).hom ≫
        (formalSectionsCone S.A S.I S.a ((restrictedTildeFunctor S).obj M)
          (opensOffVanishingNearVanishing S J hV)).π.app n =
      (forget₂ (ModuleCat S.A) Ab.{u}).map
          ((DerivedCategory.homologyFunctor (ModuleCat.{u} S.A) 0).map
            (D.complement.map ((idealPowerQuotientCone.{u, u} S.I M).π.app n))) ≫
        (assemblyTowerIso S J hJa M D hV).hom.app n :=
  comp_comp_eq_of_comp_eq (assemblyResInv S J M hV n)
    (assemblySectionsIso_hom_comp_adicProj_sections S J hJa M D hV n)

end Assembly

end Stacks.Algebraization

end
