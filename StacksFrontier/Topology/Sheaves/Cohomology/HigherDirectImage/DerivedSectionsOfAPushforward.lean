module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.EnoughInjectives
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.SheafOfModules
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.CategoryTheory.Limits.Preserves.Finite
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Homology.DerivedCategory.CompositionComparisonIso
public import StacksFrontier.Algebra.Homology.DerivedCategory.CompositionOfRightDerivedFunctors
public import StacksFrontier.Topology.Sheaves.Cohomology.CechAcyclicity.PushforwardOfAnInjective
public import StacksFrontier.Topology.Sheaves.Functors.Module.RingedSpace

/-!
# Derived sections and pushforward

For a morphism of ringed spaces, derived sections over an open commute with derived
pushforward after restricting scalars along the induced map on sections of the structure
sheaves.

## Main definitions

* `sectionsRestrictionIso` identifies sections of a pushforward with sections on the inverse
  image by the identity on sections.
* `rightDerivedSectionsRestrictionIso` is the natural isomorphism expressing the commutative
  square of bounded-below derived categories.

## Main results

* `rightDerivedSectionsRestrictionIso_hom_app` characterizes the isomorphism by compatibility
  with the derived-functor units and the identity on underived sections.

## Implementation notes

An open `V` of the target is sent by `opensMap f` to its inverse image in the source.
`rightDerivedSectionsRestrictionIso` gives the general square; taking `V = ⊤` gives the
global-sections square. Its characterization uses the homotopy-category units, so it applies
to every bounded-below complex, in particular to every injective resolution.

Both vertical arrows of the square are the right derived functors of the corresponding
underived functors, with their canonical comparisons, rather than arbitrary isomorphic
functors. The square is assembled from two instances of [Stacks, Tag 015M]
(`CategoryTheory.Functor.isIso_iff_rightAcyclic_obj_injective`), one for each of the two
composites. Along the top and right side the acyclicity input is that restriction of scalars
is exact, so that every module is right acyclic for it (`rightAcyclic_restrictScalars`);
along the left and bottom side it is that the pushforward of an injective module has acyclic
sections, which is part (2) of [Stacks, Tag 01EX]
(`Stacks.Cohomology.PushforwardAcyclic.pushforward_injective_rightAcyclic`). The two
canonical isomorphisms have for sources the right derived functors of the two underived
composites, which agree only up to the isomorphism `sectionsRestrictionIso` between them, so
the middle of the square is the isomorphism of right derived functors that it induces
(`CategoryTheory.Functor.rightDerivedNatIso`).

`squareIso` and `squareIso_hom_app` record this assembly for an arbitrary commutative square
of additive functors, and the two results about ringed spaces are the instance of it at hand.
Stating the assembly abstractly is also what keeps the file free of compiler options: the
concrete statements name the four functors directly rather than through local `let`
abbreviations, so that typechecking them needs no definitional unfolding of the pushforward
of the structure sheaf — the source of restriction of scalars is
`Γ(V, (opensMap f)_* 𝒪_X)`, and that it is `Γ(f⁻¹V, 𝒪_X)` is true by unfolding
`Functor.sheafPushforwardContinuous`, which instance search does not do.

## References

* [Stacks Project, Tag 01EZ](https://stacks.math.columbia.edu/tag/01EZ)
* [Stacks Project, Tag 01EX](https://stacks.math.columbia.edu/tag/01EX)
* [Stacks Project, Tag 015M](https://stacks.math.columbia.edu/tag/015M)
* [Stacks Project, Tag 05T2](https://stacks.math.columbia.edu/tag/05T2)
* [Stacks Project, Tag 05T8](https://stacks.math.columbia.edu/tag/05T8)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace Stacks.Cohomology.DerivedPushforwardSections

attribute [local instance] HasDerivedCategory.standard

/-! ### The canonical comparison for a composite of right derived functors -/

section Composition

-- As in `StacksFrontier.Algebra.Homology.DerivedCategory.CompositionOfRightDerivedFunctors`:
-- this section mentions `Functor.rightDerivedFunctorPlus` throughout, so the cheap instance
-- that gets pointwise right derivability from `EnoughInjectives` is given precedence over the
-- one that would embark on proving termwise injectivity of an unknown complex.
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

variable {A B C : Type*} [Category* A] [Category* B] [Category* C]
  [Abelian A] [Abelian B] [Abelian C]
  [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C]
  (F : A ⥤ B) (G : B ⥤ C) [F.Additive] [G.Additive]
  [EnoughInjectives A] [EnoughInjectives B]

-- The canonical comparison itself is `CategoryTheory.Functor.rightDerivedFunctorPlusComp`
-- ([Stacks, Tag 05T2]), with its unit `Functor.rightComparisonUnit` and its characterising
-- factorizations `Functor.rightDerivedFunctorPlusComp_fac` and
-- `Functor.rightDerivedFunctorPlusComp_fac_app`, none of which needs an acyclicity hypothesis.
-- What this section adds is its invertibility under `hFG` ([Stacks, Tag 015M]), which is a
-- weaker hypothesis than the `F.PreservesInjectiveObjects` that
-- `Functor.isIso_rightDerivedFunctorPlusComp` and `Functor.rightDerivedFunctorPlusCompIso`
-- are stated under.

variable (hFG : ∀ I : A, Injective I → G.rightAcyclic (F.obj I))

include hFG in
/-- **[Stacks, Tag 015M].** If `F` carries the injective objects of `𝒜` to objects that are
right acyclic for `G`, the canonical map `R(G ∘ F) ⟶ RG ∘ RF` of [Stacks, Tag 05T2],
`CategoryTheory.Functor.rightDerivedFunctorPlusComp`, is an isomorphism. This is the direction
of the criterion `CategoryTheory.Functor.isIso_iff_rightAcyclic_obj_injective` complementary to
`CategoryTheory.Functor.isIso_rightDerivedFunctorPlusComp`, which draws the same conclusion
from the stronger hypothesis that `F` preserve injective objects. -/
theorem isIso_compComparison : IsIso (Functor.rightDerivedFunctorPlusComp F G) :=
  (Functor.isIso_iff_rightAcyclic_obj_injective F G _
    (Functor.rightDerivedFunctorPlusComp_fac F G)).2 hFG

/-- The canonical isomorphism `R(G ∘ F) ≅ RG ∘ RF` of [Stacks, Tag 015M], under the
acyclicity hypothesis `hFG`. Its `hom` is the canonical map of [Stacks, Tag 05T2], so it is
the same isomorphism as `CategoryTheory.Functor.rightDerivedFunctorPlusCompIso` wherever the
stronger hypothesis `F.PreservesInjectiveObjects` of that one holds as well. -/
noncomputable def compIso :
    (F ⋙ G).rightDerivedFunctorPlus ≅
      F.rightDerivedFunctorPlus ⋙ G.rightDerivedFunctorPlus :=
  haveI := isIso_compComparison F G hFG
  asIso (Functor.rightDerivedFunctorPlusComp F G)

/-- `compIso` is the canonical map. Recorded separately because `asIso` is not reducible, so
that `rw` cannot see through it; rewriting with it is what makes the factorization
`CategoryTheory.Functor.rightDerivedFunctorPlusComp_fac_app` available for `compIso`. -/
theorem compIso_hom :
    (compIso F G hFG).hom = Functor.rightDerivedFunctorPlusComp F G := rfl

end Composition

/-! ### The derived square attached to a commutative square of additive functors -/

section Square

attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

variable {A B C D : Type*} [Category* A] [Category* B] [Category* C] [Category* D]
  [Abelian A] [Abelian B] [Abelian C] [Abelian D]
  [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C] [HasDerivedCategory D]
  [EnoughInjectives A] [EnoughInjectives B] [EnoughInjectives C]
  (F₁ : A ⥤ B) (G₁ : B ⥤ D) (F₂ : A ⥤ C) (G₂ : C ⥤ D)
  [F₁.Additive] [G₁.Additive] [F₂.Additive] [G₂.Additive]
  (e : F₁ ⋙ G₁ ≅ F₂ ⋙ G₂)

/-- The isomorphism of functors `K⁺(𝒜) ⥤ D⁺(𝒟)` that a commutative square `e` induces
between the two underived composites, after passing to the derived category of the target. -/
noncomputable def squareUnitIso :
    (F₁ ⋙ G₁).mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh ≅
      (F₂ ⋙ G₂).mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh :=
  Functor.isoWhiskerRight
    ((Functor.mapHomotopyCategoryPlusCompIso (Iso.refl (F₁ ⋙ G₁))).symm.trans
      (Functor.mapHomotopyCategoryPlusCompIso (F := F₁) (G := G₁) e))
    DerivedCategory.Plus.Qh

omit [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C]
  [EnoughInjectives A] [EnoughInjectives B] [EnoughInjectives C] in
/-- The component of `squareUnitIso` at a bounded-below complex. -/
theorem squareUnitIso_hom_app (K : HomotopyCategory.Plus A) :
    (squareUnitIso F₁ G₁ F₂ G₂ e).hom.app K =
      DerivedCategory.Plus.Qh.map
        ((Functor.mapHomotopyCategoryPlusCompIso (Iso.refl (F₁ ⋙ G₁))).inv.app K ≫
          (Functor.mapHomotopyCategoryPlusCompIso (F := F₁) (G := G₁) e).hom.app K) :=
  rfl

variable (h₁ : ∀ I : A, Injective I → G₁.rightAcyclic (F₁.obj I))
  (h₂ : ∀ I : A, Injective I → G₂.rightAcyclic (F₂.obj I))

/-- **The derived square.** Given a commutative square `e : F₁ ⋙ G₁ ≅ F₂ ⋙ G₂` of additive
functors in which `F₁` carries injectives to `G₁`-acyclic objects and `F₂` carries injectives
to `G₂`-acyclic objects, the square of bounded-below right derived functors commutes:
`RF₁ ⋙ RG₁ ≅ RF₂ ⋙ RG₂`. It is the composite of the inverse of the canonical isomorphism
`R(G₁ ∘ F₁) ≅ RG₁ ∘ RF₁`, the isomorphism of right derived functors induced by `e`, and the
canonical isomorphism `R(G₂ ∘ F₂) ≅ RG₂ ∘ RF₂`. -/
noncomputable def squareIso :
    F₁.rightDerivedFunctorPlus ⋙ G₁.rightDerivedFunctorPlus ≅
      F₂.rightDerivedFunctorPlus ⋙ G₂.rightDerivedFunctorPlus :=
  (compIso F₁ G₁ h₁).symm.trans
    ((Functor.rightDerivedNatIso
        (F₁ ⋙ G₁).rightDerivedFunctorPlus (F₂ ⋙ G₂).rightDerivedFunctorPlus
        (F₁ ⋙ G₁).rightDerivedFunctorPlusUnit (F₂ ⋙ G₂).rightDerivedFunctorPlusUnit
        (HomotopyCategory.Plus.quasiIso A)
        (squareUnitIso F₁ G₁ F₂ G₂ e)).trans (compIso F₂ G₂ h₂))

/-- **The derived square is the canonical one.** Composed with the units of `RG₁` and of
`RF₁`, `squareIso` is the comparison through the other side of the square: the image of `e`
under the localization, followed by the units of `RG₂` and of `RF₂`. Since the units of
`R(G₁ ∘ F₁)` and `R(G₂ ∘ F₂)` determine both canonical isomorphisms and the induced
isomorphism of right derived functors, this equation determines `squareIso`. -/
theorem squareIso_hom_app (K : HomotopyCategory.Plus A) :
    G₁.rightDerivedFunctorPlusUnit.app (F₁.mapHomotopyCategoryPlus.obj K) ≫
        G₁.rightDerivedFunctorPlus.map (F₁.rightDerivedFunctorPlusUnit.app K) ≫
        (squareIso F₁ G₁ F₂ G₂ e h₁ h₂).hom.app (DerivedCategory.Plus.Qh.obj K) =
      DerivedCategory.Plus.Qh.map
          ((Functor.mapHomotopyCategoryPlusCompIso (F := F₁) (G := G₁) e).hom.app K ≫
            (Functor.mapHomotopyCategoryPlusCompIso (Iso.refl (F₂ ⋙ G₂))).inv.app K) ≫
        G₂.rightDerivedFunctorPlusUnit.app (F₂.mapHomotopyCategoryPlus.obj K) ≫
        G₂.rightDerivedFunctorPlus.map (F₂.rightDerivedFunctorPlusUnit.app K) := by
  -- The factorizations pinning the two canonical isomorphisms, read on `compIso` through
  -- `compIso_hom`; `Functor.rightDerivedFunctorPlusComp_fac_app` needs no acyclicity
  -- hypothesis, so this is the only place `h₁` and `h₂` enter.
  have fac₁ := Functor.rightDerivedFunctorPlusComp_fac_app F₁ G₁ K
  have fac₂ := Functor.rightDerivedFunctorPlusComp_fac_app F₂ G₂ K
  rw [← compIso_hom F₁ G₁ h₁] at fac₁
  rw [← compIso_hom F₂ G₂ h₂] at fac₂
  -- Precomposing with the coherence isomorphism is injective, and brings both sides into the
  -- shape of those factorizations.
  rw [← cancel_epi (DerivedCategory.Plus.Qh.map
    ((Functor.mapHomotopyCategoryPlusCompIso (Iso.refl (F₁ ⋙ G₁))).inv.app K))]
  simp only [squareIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.rightDerivedNatIso_hom]
  rw [← reassoc_of% fac₁, Iso.hom_inv_id_app_assoc,
    Functor.rightDerivedNatTrans_app_assoc, fac₂, squareUnitIso_hom_app]
  simp only [Functor.map_comp, Category.assoc]

end Square

/-! ### Restriction of scalars is exact -/

section RestrictScalars

attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

/-- Restriction of scalars along a ring homomorphism is exact, so every module is right
acyclic for it: the class of all objects is adapted to it in the sense of
[Stacks, Tag 05T8]. -/
theorem rightAcyclic_restrictScalars {R S : Type u} [Ring R] [Ring S] (g : R →+* S)
    (M : ModuleCat.{u} S) : (ModuleCat.restrictScalars.{u} g).rightAcyclic M := by
  have : PreservesFiniteLimits (ModuleCat.restrictScalars.{u} g) :=
    ⟨fun _ _ _ => ⟨fun {_} => inferInstance⟩⟩
  exact Functor.le_rightAcyclic _ ⊤ (fun N => ⟨N, trivial, 𝟙 N, inferInstance⟩)
    (fun _ hS _ _ => ⟨trivial, hS.map_of_exact _⟩) M trivial

end RestrictScalars

/-! ### Additivity of the pushforward of modules -/

section PushforwardAdditive

/-- Pushforward of modules along a morphism of ringed spaces is a right adjoint. -/
local instance modulePushforwardIsRightAdjoint {X Y : RingedSpace.{u, u}} (f : X ⟶ Y) :
    (RingedSpaceModuleAdjunction.modulePushforward f).IsRightAdjoint :=
  RingedSpaceModuleAdjunction.modulePushforward_isRightAdjoint f

attribute [local instance] Limits.preservesBinaryBiproducts_of_preservesBinaryProducts

/-- Pushforward of modules along a morphism of ringed spaces is additive: being a right
adjoint it preserves products, hence binary biproducts. -/
theorem modulePushforward_additive {X Y : RingedSpace.{u, u}} (f : X ⟶ Y) :
    (RingedSpaceModuleAdjunction.modulePushforward f).Additive :=
  Functor.additive_of_preservesBinaryBiproducts _

end PushforwardAdditive

/-! ### Derived sections and pushforward for a morphism of ringed spaces -/

section RingedSpace

attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

-- Seated from `PushforwardOfAnInjective`, not restated; inside this section, since a local
-- attribute reverts at its `end`. The `Abelian` one is a memoising shortcut: without it the goal
-- inside the `HasRightDerivedFunctor` elaboration exhausts its 20000-heartbeat budget.
attribute [local instance]
  Stacks.Cohomology.PushforwardAcyclic.sheafOfModules_abelian

/-- Pushforward of modules along a morphism of ringed spaces is additive: being a right
adjoint it preserves products, hence binary biproducts. -/
local instance modulePushforwardAdditive {X Y : RingedSpace.{u, u}} (f : X ⟶ Y) :
    (RingedSpaceModuleAdjunction.modulePushforward f).Additive :=
  modulePushforward_additive f

/-- Restriction of scalars along the structure morphism is additive, stated with the source
category spelled as the target of sections over `f⁻¹V`. The `Mathlib` instance spells it as
`Γ(V, (opensMap f)_* 𝒪_X)` instead; the two agree only after unfolding
`Functor.sheafPushforwardContinuous`, which instance search does not do, so the square below
needs this form. -/
local instance restrictScalarsSectionsAdditive {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
    (V : Opens Y.carrier) :
    @Functor.Additive
      (ModuleCat.{u} ((structureSheafRing X).obj.obj
        (op ((RingedSpaceModuleAdjunction.opensMap f).obj V))))
      (ModuleCat.{u} ((structureSheafRing Y).obj.obj (op V)))
      _ _ _ _
      (ModuleCat.restrictScalars.{u}
        ((RingedSpaceModuleAdjunction.structureSheafHom f).hom.app (op V)).hom) :=
  ⟨by intros; rfl⟩

/-- Sections of a pushforward are sections on the inverse image, with scalars restricted
along the structure morphism. The identification is the identity on sections. -/
@[simps! hom_app inv_app]
noncomputable def sectionsRestrictionIso
    {X Y : RingedSpace.{u, u}} (f : X ⟶ Y) (V : Opens Y.carrier) :
    SheafOfModules.evaluation (structureSheafRing X)
          (op ((RingedSpaceModuleAdjunction.opensMap f).obj V)) ⋙
        ModuleCat.restrictScalars
          ((RingedSpaceModuleAdjunction.structureSheafHom f).hom.app (op V)).hom
      ≅
    RingedSpaceModuleAdjunction.modulePushforward f ⋙
      SheafOfModules.evaluation (structureSheafRing Y) (op V) :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (by intros; rfl)

/-- The pushforward of an injective module has right acyclic sections over every open: this
is part (2) of [Stacks, Tag 01EX], in the form the derived square takes as input. -/
theorem rightAcyclic_modulePushforward_obj {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
    (V : Opens Y.carrier)
    (I : SheafOfModules.{u} (structureSheafRing X)) (hI : Injective I) :
    (SheafOfModules.evaluation (structureSheafRing Y) (op V)).rightAcyclic
      ((RingedSpaceModuleAdjunction.modulePushforward f).obj I) :=
  have : Injective I := hI
  Stacks.Cohomology.PushforwardAcyclic.pushforward_injective_rightAcyclic f I V

/-- **Stacks 01EZ.** For a morphism `f : X ⟶ Y` of ringed spaces and an open `V` of `Y`,
let `U = f⁻¹(V)`. The composite of derived sections over `U` with derived restriction of
scalars along `Γ(V, 𝒪_Y) → Γ(U, 𝒪_X)` is naturally isomorphic to the composite of
derived pushforward along `f` with derived sections over `V`. Thus the corresponding square of
bounded-below derived categories commutes. -/
@[stacks 01EZ "the natural isomorphism"]
public noncomputable def rightDerivedSectionsRestrictionIso
    {X Y : RingedSpace.{u, u}} (f : X ⟶ Y) (V : Opens Y.carrier) :
    (SheafOfModules.evaluation (structureSheafRing X)
          (op ((RingedSpaceModuleAdjunction.opensMap f).obj V))).rightDerivedFunctorPlus ⋙
        (ModuleCat.restrictScalars
          ((RingedSpaceModuleAdjunction.structureSheafHom f).hom.app
            (op V)).hom).rightDerivedFunctorPlus
      ≅
    (RingedSpaceModuleAdjunction.modulePushforward f).rightDerivedFunctorPlus ⋙
      (SheafOfModules.evaluation (structureSheafRing Y)
        (op V)).rightDerivedFunctorPlus :=
  squareIso (SheafOfModules.evaluation (structureSheafRing X)
      (op ((RingedSpaceModuleAdjunction.opensMap f).obj V)))
    (ModuleCat.restrictScalars
      ((RingedSpaceModuleAdjunction.structureSheafHom f).hom.app (op V)).hom)
    (RingedSpaceModuleAdjunction.modulePushforward f)
    (SheafOfModules.evaluation (structureSheafRing Y) (op V))
    (sectionsRestrictionIso f V)
    (fun _ _ => rightAcyclic_restrictScalars _ _)
    (rightAcyclic_modulePushforward_obj f V)

/-- The derived comparison is induced by the identity on underived sections: its
composite with the two derived-functor units is the comparison through pushforward.
This equation fixes the canonical isomorphism, including its normalization on degree-zero
cohomology. -/
@[stacks 01EZ "compatibility with the derived-functor units",
  stacks 01F0 "the comparison is induced by the identity on underived sections"]
theorem rightDerivedSectionsRestrictionIso_hom_app
    {X Y : RingedSpace.{u, u}} (f : X ⟶ Y) (V : Opens Y.carrier)
    (K : HomotopyCategory.Plus
      (SheafOfModules.{u} (structureSheafRing X))) :
    (ModuleCat.restrictScalars.{u}
        ((RingedSpaceModuleAdjunction.structureSheafHom f).hom.app
          (op V)).hom).rightDerivedFunctorPlusUnit.app
        ((SheafOfModules.evaluation.{u} (structureSheafRing X)
          (op ((RingedSpaceModuleAdjunction.opensMap f).obj V))).mapHomotopyCategoryPlus.obj
            K) ≫
        (ModuleCat.restrictScalars.{u}
          ((RingedSpaceModuleAdjunction.structureSheafHom f).hom.app
            (op V)).hom).rightDerivedFunctorPlus.map
          ((SheafOfModules.evaluation.{u} (structureSheafRing X)
            (op ((RingedSpaceModuleAdjunction.opensMap f).obj
              V))).rightDerivedFunctorPlusUnit.app K) ≫
        (rightDerivedSectionsRestrictionIso f V).hom.app (DerivedCategory.Plus.Qh.obj K) =
      DerivedCategory.Plus.Qh.map
          ((Functor.mapHomotopyCategoryPlusCompIso
              (F := SheafOfModules.evaluation.{u} (structureSheafRing X)
                (op ((RingedSpaceModuleAdjunction.opensMap f).obj V)))
              (G := ModuleCat.restrictScalars.{u}
                ((RingedSpaceModuleAdjunction.structureSheafHom f).hom.app (op V)).hom)
              (sectionsRestrictionIso f V)).hom.app K ≫
            (Functor.mapHomotopyCategoryPlusCompIso (Iso.refl
              (RingedSpaceModuleAdjunction.modulePushforward f ⋙
                SheafOfModules.evaluation.{u} (structureSheafRing Y)
                  (op V)))).inv.app K) ≫
        (SheafOfModules.evaluation.{u} (structureSheafRing Y)
          (op V)).rightDerivedFunctorPlusUnit.app
          ((RingedSpaceModuleAdjunction.modulePushforward f).mapHomotopyCategoryPlus.obj K) ≫
        (SheafOfModules.evaluation.{u} (structureSheafRing Y)
          (op V)).rightDerivedFunctorPlus.map
          ((RingedSpaceModuleAdjunction.modulePushforward f).rightDerivedFunctorPlusUnit.app
            K) :=
  squareIso_hom_app _ _ _ _ (sectionsRestrictionIso f V)
    (fun _ _ => rightAcyclic_restrictScalars _ _) (rightAcyclic_modulePushforward_obj f V) K

end RingedSpace

end Stacks.Cohomology.DerivedPushforwardSections

end
