module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.AssociatedSheafIsos
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExtensionByZeroUnitULift
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafificationTensor
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ULiftUnit
public import StacksFrontier.CategoryTheory.Sites.Modules.NaiveCotangentInverseImageComplex

/-!
# The naive cotangent complex and the universe of the sections of its modules

Let `a : A ⟶ B` be a homomorphism of sheaves of commutative rings on a site `(C, J)`. The naive
cotangent complex `NL_{B/A}` of Stacks 08TW is a complex of sheaves of `B`-modules whose sections
lie in a universe `max w u v z`, where `w` is the universe of the sections of the rings, `u, v`
are the universes of the site and `z` is a free parameter. This file shows that raising `z` to
`max z t` is the same as applying the universe lift
`Stacks.SheafOfModules.moduleULift` of sheaves of modules to the complex:

`moduleULift (NL_{B/A} at z) ≅ NL_{B/A} at max z t`.

The terms of the conormal sequence are sheafifications of objectwise constructions lifted to the
universe of the sections, and sheafification commutes with the universe lift
(`PresheafOfModules.isIso_sheafifyULiftHom`).

## Main definitions

* `Stacks.Sites.Conormal.liftModulesULiftIso`: lifting the sections to `max w u v z t` is lifting
  them to `max w u v z` and then by `ULift.{t}`.
* `Stacks.Sites.Conormal.sheafifyLiftModulesULiftIso`: the sheafification of the lift to
  `max w u v z t` is the universe lift of the sheafification of the lift to `max w u v z`,
  naturally (`Stacks.Sites.Conormal.sheafifyLiftModulesULiftIso_naturality`).
* `Stacks.SheafOfModules.naiveCotangentComplexModuleULiftIso`: the comparison of the naive
  cotangent complexes.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe t v u w z

namespace Stacks.Sites.Conormal

variable {C : Type u} [Category.{v} C]

section Lift

variable (S : Cᵒᵖ ⥤ RingCat.{w})

/-- Lifting the sections of a presheaf of modules to `max w u v z t` is lifting them to
`max w u v z` and then by `ULift.{t}`. -/
noncomputable def liftModulesULiftIso (M : PresheafOfModules.{w} S) :
    (liftModules.{v, u, w, max z t} S).obj M ≅
      PresheafOfModules.uliftObj.{_, _, _, _, t} ((liftModules.{v, u, w, z} S).obj M) :=
  PresheafOfModules.isoMk
    (fun X => (ULift.moduleEquiv.trans (ULift.moduleEquiv.trans ULift.moduleEquiv).symm :
      ULift.{max u v z t} (M.obj X) ≃ₗ[S.obj X]
        ULift.{t} (ULift.{max u v z} (M.obj X))).toModuleIso)
    (fun _ _ _ => rfl)

/-- `Stacks.Sites.Conormal.liftModulesULiftIso` is natural. -/
@[reassoc]
theorem liftModulesULiftIso_naturality {M M' : PresheafOfModules.{w} S} (f : M ⟶ M') :
    (liftModules.{v, u, w, max z t} S).map f ≫ (liftModulesULiftIso.{t, v, u, w, z} S M').hom =
      (liftModulesULiftIso.{t, v, u, w, z} S M).hom ≫
        PresheafOfModules.uliftMap.{_, _, _, _, t} ((liftModules.{v, u, w, z} S).map f) :=
  rfl

end Lift

/-- Sheafification of presheaves of abelian groups with sections in `Type z` exists on an
essentially `z`-small site. -/
local instance {J : GrothendieckTopology C} [EssentiallySmall.{z} C] :
    HasSheafify J AddCommGrpCat.{z} :=
  AlgebraicGeometry.SheafOfModules.siteHasSheafify (J := J)

/-- On an essentially `z`-small site, sheafification of presheaves of abelian groups with
sections in `Type z` inverts exactly the locally bijective morphisms. -/
local instance {J : GrothendieckTopology C} [EssentiallySmall.{z} C] :
    J.WEqualsLocallyBijective AddCommGrpCat.{z} :=
  AlgebraicGeometry.SheafOfModules.siteWEqualsLocallyBijective (J := J)

section Sheafify

variable {J : GrothendieckTopology C} {S : Cᵒᵖ ⥤ RingCat.{w}} {R : Sheaf J RingCat.{w}}
  (α : S ⟶ R.obj) [Presheaf.IsLocallyInjective J α] [Presheaf.IsLocallySurjective J α]

/-- **Sheafification commutes with raising the universe of the lifted sections**: the
sheafification of the lift of `M` to `max w u v z t` is the universe lift of the sheafification
of its lift to `max w u v z`. -/
noncomputable def sheafifyLiftModulesULiftIso (M : PresheafOfModules.{w} S) :
    (PresheafOfModules.sheafification.{max w u v z t} α).obj
        ((liftModules.{v, u, w, max z t} S).obj M) ≅
      (Stacks.SheafOfModules.moduleULift.{t, max w u v z} R).obj
        ((PresheafOfModules.sheafification.{max w u v z} α).obj
          ((liftModules.{v, u, w, z} S).obj M)) :=
  (PresheafOfModules.sheafification.{max w u v z t} α).mapIso
      (liftModulesULiftIso.{t, v, u, w, z} S M) ≪≫
    @asIso _ _ _ _ (PresheafOfModules.sheafifyULiftHom.{_, _, _, _, t} α
      ((liftModules.{v, u, w, z} S).obj M))
      (PresheafOfModules.isIso_sheafifyULiftHom.{_, _, _, _, t} α
        ((liftModules.{v, u, w, z} S).obj M))

/-- `Stacks.Sites.Conormal.sheafifyLiftModulesULiftIso` is natural. -/
theorem sheafifyLiftModulesULiftIso_naturality {M M' : PresheafOfModules.{w} S} (f : M ⟶ M') :
    (PresheafOfModules.sheafification.{max w u v z t} α).map
        ((liftModules.{v, u, w, max z t} S).map f) ≫
        (sheafifyLiftModulesULiftIso.{t, v, u, w, z} α M').hom =
      (sheafifyLiftModulesULiftIso.{t, v, u, w, z} α M).hom ≫
        (Stacks.SheafOfModules.moduleULift.{t, max w u v z} R).map
          ((PresheafOfModules.sheafification.{max w u v z} α).map
            ((liftModules.{v, u, w, z} S).map f)) := by
  refine PresheafOfModules.sheafification_hom_ext.{v, u, w, max w u v z t} ?_
  let L := liftModules.{v, u, w, z} S
  let L' := liftModules.{v, u, w, max z t} S
  let F := SheafOfModules.forget.{max w u v z} R ⋙
    PresheafOfModules.restrictScalars.{max w u v z} α
  let F' := SheafOfModules.forget.{max w u v z t} R ⋙
    PresheafOfModules.restrictScalars.{max w u v z t} α
  let η := (PresheafOfModules.sheafificationAdjunction.{max w u v z} α).unit
  let η' := (PresheafOfModules.sheafificationAdjunction.{max w u v z t} α).unit
  have key : ∀ N : PresheafOfModules.{max w u v z} S,
      η'.app (PresheafOfModules.uliftObj.{_, _, _, _, t} N) ≫
          F'.map (PresheafOfModules.sheafifyULiftHom.{_, _, _, _, t} α N) =
        PresheafOfModules.uliftMap.{_, _, _, _, t} (η.app N) := fun N =>
    PresheafOfModules.sheafificationAdjunction_unit_comp_homEquiv_symm.{v, u, w, max w u v z t}
      α _
  have e₂ : ∀ {N N' : PresheafOfModules.{max w u v z t} S} (g : N ⟶ N'),
      η'.app N ≫ F'.map ((PresheafOfModules.sheafification.{max w u v z t} α).map g) =
        g ≫ η'.app N' := fun g => (η'.naturality g).symm
  have e₁ : ∀ N : PresheafOfModules.{w} S,
      η'.app (L'.obj N) ≫ F'.map ((sheafifyLiftModulesULiftIso.{t, v, u, w, z} α N).hom) =
        (liftModulesULiftIso.{t, v, u, w, z} S N).hom ≫
          PresheafOfModules.uliftMap.{_, _, _, _, t} (η.app (L.obj N)) := by
    intro N
    change η'.app (L'.obj N) ≫ F'.map ((PresheafOfModules.sheafification.{max w u v z t} α).map
        (liftModulesULiftIso.{t, v, u, w, z} S N).hom ≫
        PresheafOfModules.sheafifyULiftHom.{_, _, _, _, t} α (L.obj N)) = _
    rw [F'.map_comp, ← Category.assoc, e₂ _]
    exact (Category.assoc _ _ _).trans (congrArg (_ ≫ ·) (key (L.obj N)))
  have e₃ : η.app (L.obj M) ≫ F.map ((PresheafOfModules.sheafification.{max w u v z} α).map
      (L.map f)) = L.map f ≫ η.app (L.obj M') := (η.naturality _).symm
  have lhs : η'.app (L'.obj M) ≫
      F'.map ((PresheafOfModules.sheafification.{max w u v z t} α).map (L'.map f) ≫
        (sheafifyLiftModulesULiftIso.{t, v, u, w, z} α M').hom) =
      L'.map f ≫ (liftModulesULiftIso.{t, v, u, w, z} S M').hom ≫
        PresheafOfModules.uliftMap.{_, _, _, _, t} (η.app (L.obj M')) := by
    rw [F'.map_comp, reassoc_of% (e₂ (L'.map f)), e₁]
    rfl
  have rhs : η'.app (L'.obj M) ≫ F'.map ((sheafifyLiftModulesULiftIso.{t, v, u, w, z} α M).hom ≫
      (Stacks.SheafOfModules.moduleULift.{t, max w u v z} R).map
        ((PresheafOfModules.sheafification.{max w u v z} α).map (L.map f))) =
      (liftModulesULiftIso.{t, v, u, w, z} S M).hom ≫
        PresheafOfModules.uliftMap.{_, _, _, _, t} (L.map f ≫ η.app (L.obj M')) := by
    rw [F'.map_comp, reassoc_of% e₁, ← e₃]
    rfl
  exact lhs.trans rhs.symm

end Sheafify

section Sheaves

variable (J : GrothendieckTopology C) [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  (R A B : Sheaf J CommRingCat.{w}) (a : R ⟶ A) (φ : A ⟶ B) [Presheaf.IsLocallySurjective J φ.hom]

/-- **The conormal sequence at `max z t` is the universe lift of the conormal sequence at `z`**:
its three terms are sheafifications of the same objectwise constructions, and sheafification
commutes with the universe lift. -/
noncomputable def conormalSequenceModuleULiftIso :
    conormalSequence.{v, u, w, max z t} J R A B a φ ≅
      (conormalSequence.{v, u, w, z} J R A B a φ).map
        (Stacks.SheafOfModules.moduleULift.{t, max w u v z}
          (Stacks.SheafOfModules.Tensor.ringSheaf B)) :=
  ShortComplex.isoMk
    (sheafifyLiftModulesULiftIso.{t, v, u, w, z} (quotientToRingSheaf J A B φ) _)
    (sheafifyLiftModulesULiftIso.{t, v, u, w, z} (quotientToRingSheaf J A B φ) _)
    (sheafifyLiftModulesULiftIso.{t, v, u, w, z} (quotientToRingSheaf J A B φ) _)
    (sheafifyLiftModulesULiftIso_naturality.{t, v, u, w, z} (quotientToRingSheaf J A B φ)
      (conormalToTensor φ.hom a.hom)).symm
    (sheafifyLiftModulesULiftIso_naturality.{t, v, u, w, z} (quotientToRingSheaf J A B φ)
      (tensorToDifferentials φ.hom a.hom)).symm

end Sheaves

end Stacks.Sites.Conormal

namespace Stacks.SheafOfModules

open Stacks.Sites.Conormal Stacks.Sites.FreeAlgebra

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasWeakSheafify J CommRingCat.{w}] [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  (A B : Sheaf J CommRingCat.{w}) (a : A ⟶ B)

/-- **The naive cotangent complex at `max z t` is the universe lift of the naive cotangent
complex at `z`**: `moduleULift NL_{B/A} ≅ NL_{B/A}`, as an isomorphism of two-term complexes of
sheaves of `B`-modules with sections in `max w u v z t`. -/
noncomputable def naiveCotangentComplexModuleULiftIso :
    ((moduleULift.{t, max w u v z} (Tensor.ringSheaf B)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (naiveCotangentComplex.{v, u, w, z} J A B a) ≅
      naiveCotangentComplex.{v, u, w, max z t} J A B a := by
  letI : HasZeroObject (_root_.SheafOfModules.{max w u v z} (Tensor.ringSheaf B)) :=
    hasZeroObject_of_hasTerminal_object
  letI : HasZeroObject (_root_.SheafOfModules.{max w u v z t} (Tensor.ringSheaf B)) :=
    hasZeroObject_of_hasTerminal_object
  haveI : Presheaf.IsLocallySurjective J (canonicalPresentation J A B a).hom :=
    canonicalPresentation_isLocallySurjective J A B a
  let E := conormalSequenceModuleULiftIso.{t, v, u, w, z} J A
    (freeAlgebraSheaf J A (underlyingPresheaf J B)) B
    (freeAlgebraSheafCoefficientMap J A (underlyingPresheaf J B)) (canonicalPresentation J A B a)
  refine HomologicalComplex.isoFromMapDouble
    (moduleULift.{t, max w u v z} (Tensor.ringSheaf B))
    (canonicalConormalSequence.{v, u, w, z} J A B a).f
    (show (ComplexShape.up ℤ).Rel (-1) 0 from by decide) (by decide)
    ((ShortComplex.π₁.mapIso E).symm ≪≫
      (naiveCotangentComplexXNegOneIso.{u, v, w, max z t} J A B a).symm)
    ((ShortComplex.π₂.mapIso E).symm ≪≫
      (naiveCotangentComplexXZeroIso.{u, v, w, max z t} J A B a).symm) ?_ ?_ ?_
  · rw [naiveCotangentComplex_d_negOne_zero_iso.{u, v, w, max z t} J A B a]
    have k : (ShortComplex.π₁.mapIso E).inv ≫
          (canonicalConormalSequence.{v, u, w, max z t} J A B a).f =
        (moduleULift.{t, max w u v z} (Tensor.ringSheaf B)).map
          (canonicalConormalSequence.{v, u, w, z} J A B a).f ≫ (ShortComplex.π₂.mapIso E).inv :=
      E.inv.comm₁₂
    change (ShortComplex.π₁.mapIso E).inv ≫
        (naiveCotangentComplexXNegOneIso.{u, v, w, max z t} J A B a).inv ≫
          ((naiveCotangentComplexXNegOneIso.{u, v, w, max z t} J A B a).hom ≫
            (canonicalConormalSequence.{v, u, w, max z t} J A B a).f ≫
              (naiveCotangentComplexXZeroIso.{u, v, w, max z t} J A B a).inv) =
      (moduleULift.{t, max w u v z} (Tensor.ringSheaf B)).map
          (canonicalConormalSequence.{v, u, w, z} J A B a).f ≫
        (ShortComplex.π₂.mapIso E).inv ≫
          (naiveCotangentComplexXZeroIso.{u, v, w, max z t} J A B a).inv
    exact (congrArg (fun x => (ShortComplex.π₁.mapIso E).inv ≫ x)
      (Iso.inv_hom_id_assoc (naiveCotangentComplexXNegOneIso.{u, v, w, max z t} J A B a) _)).trans
      ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) k).trans (Category.assoc _ _ _)))
  · intro k _
    rw [naiveCotangentComplex_d_zero_eq_zero.{u, v, w, max z t} J A B a k, Limits.comp_zero]
  · intro k h₀ h₁
    exact naiveCotangentComplex_isZero_X.{v, u, w, max z t} J A B a k h₀ h₁

end Stacks.SheafOfModules

end
