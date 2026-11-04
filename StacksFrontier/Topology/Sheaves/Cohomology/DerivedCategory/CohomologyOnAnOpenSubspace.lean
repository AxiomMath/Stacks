module

public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.SheafOfModules
public import StacksFrontier.Algebra.Homology.DerivedCategory.Basic
public import StacksFrontier.Algebra.Homology.DerivedCategory.KInjective
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Localization.RestrictionOfModules
public import StacksFrontier.Algebra.Homology.DerivedCategory.KInjectiveLocalization
public import StacksFrontier.Homology.Injectives.KInjective.FunctorialResolution
public import StacksFrontier.Topology.Sheaves.Cohomology.ExtensionByZero.RestrictionOfKInjectives
public import StacksFrontier.CategoryTheory.Sites.Modules.Colimits
public import StacksFrontier.CategoryTheory.Sites.Modules.GrothendieckAbelian
public import StacksFrontier.Topology.Sheaves.Modules.Exactness
public import StacksFrontier.Topology.Sheaves.OpenImmersion.ModuleExtensionByZero
import StacksCore.Tactic.StacksAttribute

/-!
# Cohomology of an open subspace

Let `X` be a ringed space and `U` an open subspace. For `K` in the unbounded derived
category `D(O_X)` we have `H^p(U, K) = H^p(U, K|_U)`: restricting an object of the derived
category to an open subspace does not change its cohomology over that open.

The proof is the universal property of the right derived functor, applied twice. Sections
over `U` factor as restriction to `U` followed by global sections on the open subspace
`U` -- that is `sectionsRestrictionIso`, an isomorphism of underived functors, since both
sides evaluate the sheaf at `U` and only the ring acting on the result differs, by the
identity. Deriving the two sides gives two right derived functors of one and the same
functor on the homotopy category, hence a canonical isomorphism between them, provided the
comparison transformation is invertible. It is checked to be invertible on K-injective
complexes, where each of the two derived units is invertible separately -- for the inner
one because restriction to an open subspace preserves K-injectivity (Tag 08BS) -- and
K-injective complexes suffice, because every complex of modules on a ringed space admits a
quasi-isomorphism into one (Tag 079P, the category of modules being Grothendieck abelian).

## Main definitions

* `Stacks.Cohomology.OpenSubspace.sectionsOnOpen`: sections over an open `U`, with the
  module structure forgotten.
* `Stacks.Cohomology.OpenSubspace.sectionsOnOpenSubspace`: global sections on the open
  subspace `U`, with the module structure forgotten.
* `Stacks.Cohomology.OpenSubspace.derivedSectionsOnOpen`: unbounded derived sections over
  an open.
* `Stacks.Cohomology.OpenSubspace.derivedRestriction`: unbounded derived restriction to an
  open subspace.
* `Stacks.Cohomology.OpenSubspace.derivedSectionsOnOpenSubspace`: unbounded derived global
  sections on the open subspace.

## Main results

* `Stacks.Cohomology.OpenSubspace.cohomologyOnOpenIsoRestriction` (Tag 0D5V): degree-`p`
  cohomology over an open agrees naturally with degree-`p` cohomology after restriction to
  that open subspace.
* `Stacks.Cohomology.Localization.rightDerived_of_kInjectives` and
  `Stacks.Cohomology.Localization.derivedUnit_isIsoOnKInjective`: the two
  reduction-to-K-injectives steps, stated for an arbitrary Grothendieck abelian category.

## Implementation notes

The natural module structures on sections are forgotten, so that the two derived functors
being compared land in `D(AddCommGrpCat)`. The result is stated, for each degree, as a
natural isomorphism of cohomology functors: its component at `K` is precisely the
identification `H^p(U, K) = H^p(U, K|_U)` of the source, while the functor-level statement
also records its naturality in `K`.

The three total right derived functors exist by
`Stacks.Cohomology.Localization.hasRightDerivedFunctorOfGrothendieck`, the categories of modules
involved being Grothendieck abelian.
`Stacks.Cohomology.Localization.rightDerived_of_kInjectives` exhibits the composite along the
other side of the square as a right derived functor, inside the proof.

The three derived categories involved — those of `O`-modules, of `O|_U`-modules and of
abelian groups — are taken at arbitrary, independently chosen `HasDerivedCategory`
instances. Nothing below needs a particular model: the only inputs are the universal
property of a right derived functor and the fact that every complex of modules on a ringed
space admits a quasi-isomorphism into a K-injective one. Choosing the standard model here
instead would bake it into the types of `derivedSectionsOnOpen` and of the comparison
itself, and a statement proved at the standard model says nothing about the locally small
model of Tag 079Q, which is where the morphisms of `D(O_X)` are small enough for derived
limits and Brown representability.

`sectionsRestrictionIso` is built with `eqToIso` on the equality of opens
`(TopCat.Presheaf.imF U).obj ⊤ = U`, because the two functors agree on the nose once that
equality is used; its naturality is then `CategoryTheory.eqToHom_naturality` for the
corresponding family of maps on sections.

## References

* [Stacks Project, Tag 0D5V](https://stacks.math.columbia.edu/tag/0D5V)
* [Stacks Project, Tag 079P](https://stacks.math.columbia.edu/tag/079P)
* [Stacks Project, Tag 08BS](https://stacks.math.columbia.edu/tag/08BS)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace
open ExtensionByZeroModules

universe wX wU wG u v₁ v₂

namespace Stacks.Cohomology.OpenSubspace

/-- Sections of a sheaf of modules over `U`, with the module structure forgotten. -/
public abbrev sectionsOnOpen {X : TopCat.{u}}
    (O : Sheaf (Opens.grothendieckTopology X) RingCat.{u}) (U : Opens X) :
    SheafOfModules.{u} O ⥤ AddCommGrpCat.{u} :=
  SheafOfModules.evaluation O (op U) ⋙
    forget₂ (ModuleCat.{u} (O.obj.obj (op U))) AddCommGrpCat.{u}

/-- Global sections on the open subspace `U`, with the module structure forgotten. -/
public abbrev sectionsOnOpenSubspace {X : TopCat.{u}}
    (O : Sheaf (Opens.grothendieckTopology X) RingCat.{u}) (U : Opens X) :
    SheafOfModules.{u} (resRing U O) ⥤ AddCommGrpCat.{u} :=
  SheafOfModules.evaluation (resRing U O) (op ⊤) ⋙
    forget₂ (ModuleCat.{u} ((resRing U O).obj.obj (op ⊤))) AddCommGrpCat.{u}

/-- Sections over `U`, with the module structure forgotten, form an additive functor. -/
public instance sectionsOnOpen_additive {X : TopCat.{u}}
    (O : Sheaf (Opens.grothendieckTopology X) RingCat.{u}) (U : Opens X) :
    (sectionsOnOpen O U).Additive where
  map_add := rfl

/-- Global sections on the open subspace `U`, with the module structure forgotten, form an
additive functor. -/
public instance sectionsOnOpenSubspace_additive {X : TopCat.{u}}
    (O : Sheaf (Opens.grothendieckTopology X) RingCat.{u}) (U : Opens X) :
    (sectionsOnOpenSubspace O U).Additive where
  map_add := rfl

/-- The homotopy-category functor whose right derived functor is sections over `U`. -/
public abbrev homotopySectionsOnOpen {X : TopCat.{u}}
    (O : Sheaf (Opens.grothendieckTopology X) RingCat.{u}) (U : Opens X)
    [HasDerivedCategory.{wG} AddCommGrpCat.{u}] :
    HomotopyCategory (SheafOfModules.{u} O) (ComplexShape.up ℤ) ⥤
      DerivedCategory AddCommGrpCat.{u} :=
  (sectionsOnOpen O U).mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh

/-- The homotopy-category functor whose right derived functor is restriction to `U`. -/
public abbrev homotopyRestriction {X : TopCat.{u}}
    (O : Sheaf (Opens.grothendieckTopology X) RingCat.{u}) (U : Opens X)
    [HasDerivedCategory.{wU} (SheafOfModules.{u} (resRing U O))] :
    HomotopyCategory (SheafOfModules.{u} O) (ComplexShape.up ℤ) ⥤
      DerivedCategory (SheafOfModules.{u} (resRing U O)) :=
  (jStar U O).mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh

/-- The homotopy-category functor whose right derived functor is global sections on `U`. -/
public abbrev homotopySectionsOnOpenSubspace {X : TopCat.{u}}
    (O : Sheaf (Opens.grothendieckTopology X) RingCat.{u}) (U : Opens X)
    [HasDerivedCategory.{wG} AddCommGrpCat.{u}] :
    HomotopyCategory (SheafOfModules.{u} (resRing U O)) (ComplexShape.up ℤ) ⥤
      DerivedCategory AddCommGrpCat.{u} :=
  (sectionsOnOpenSubspace O U).mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh

/-- **Every functor out of the homotopy category of `O`-modules on a space has a total right
derived functor.** Sheaves of `O`-modules are Grothendieck abelian, so every complex of them
receives a quasi-isomorphism from a K-injective one, and that is all the existence of the total
right derived functor needs. -/
public theorem hasRightDerivedFunctor_of_moduleKInjectives {X : TopCat.{u}}
    (O : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
    {C : Type v₁} [Category.{v₂} C]
    (S : HomotopyCategory (SheafOfModules.{u} O) (ComplexShape.up ℤ) ⥤ C) :
    S.HasRightDerivedFunctor
      (HomotopyCategory.quasiIso (SheafOfModules.{u} O) (ComplexShape.up ℤ)) := by
  have : IsGrothendieckAbelian.{u} (SheafOfModules.{u} O) :=
    Stacks.SheafOfModules.sheafModulesGrothendieck _ O
  have : S.HasPointwiseRightDerivedFunctor
      (HomotopyCategory.quasiIso (SheafOfModules.{u} O) (ComplexShape.up ℤ)) :=
    (Functor.hasPointwiseRightDerivedFunctor_and_isIso_app_of_exists_quasiIso_isKInjective.{
      u, v₂, v₁, u + 1, v₁, u + 1} S
      (Stacks.Cohomology.Localization.enoughKInjectives (C := SheafOfModules.{u} O))).1
  exact Functor.hasRightDerivedFunctor_of_hasPointwiseRightDerivedFunctor S _

/-- Unbounded derived sections over `U`. -/
public abbrev derivedSectionsOnOpen {X : TopCat.{u}}
    (O : Sheaf (Opens.grothendieckTopology X) RingCat.{u}) (U : Opens X)
    [HasDerivedCategory.{wX} (SheafOfModules.{u} O)]
    [HasDerivedCategory.{wG} AddCommGrpCat.{u}] :
    DerivedCategory (SheafOfModules.{u} O) ⥤ DerivedCategory AddCommGrpCat.{u} :=
  (homotopySectionsOnOpen O U).totalRightDerived DerivedCategory.Qh
    (HomotopyCategory.quasiIso (SheafOfModules.{u} O) (ComplexShape.up ℤ))

/-- Unbounded derived restriction to `U`. -/
public abbrev derivedRestriction {X : TopCat.{u}}
    (O : Sheaf (Opens.grothendieckTopology X) RingCat.{u}) (U : Opens X)
    [HasDerivedCategory.{wX} (SheafOfModules.{u} O)]
    [HasDerivedCategory.{wU} (SheafOfModules.{u} (resRing U O))] :
    DerivedCategory (SheafOfModules.{u} O) ⥤
      DerivedCategory (SheafOfModules.{u} (resRing U O)) :=
  (homotopyRestriction O U).totalRightDerived DerivedCategory.Qh
    (HomotopyCategory.quasiIso (SheafOfModules.{u} O) (ComplexShape.up ℤ))

/-- Unbounded derived global sections on the open subspace `U`. -/
public abbrev derivedSectionsOnOpenSubspace {X : TopCat.{u}}
    (O : Sheaf (Opens.grothendieckTopology X) RingCat.{u}) (U : Opens X)
    [HasDerivedCategory.{wU} (SheafOfModules.{u} (resRing U O))]
    [HasDerivedCategory.{wG} AddCommGrpCat.{u}] :
    DerivedCategory (SheafOfModules.{u} (resRing U O)) ⥤ DerivedCategory AddCommGrpCat.{u} :=
  (homotopySectionsOnOpenSubspace O U).totalRightDerived DerivedCategory.Qh
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (resRing U O)) (ComplexShape.up ℤ))

/-- Sections over `U` agree with restriction to the open subspace `U` followed by its global
sections, both with the module structure forgotten. -/
noncomputable def sectionsRestrictionIso {X : TopCat.{u}}
    (O : Sheaf (Opens.grothendieckTopology X) RingCat.{u}) (U : Opens X) :
    sectionsOnOpen O U ≅ jStar U O ⋙ sectionsOnOpenSubspace O U := by
  have hU : (TopCat.Presheaf.imF U).obj (⊤ : Opens (Usp U)) = U := by
    apply Opens.ext
    change (Subtype.val '' Set.univ : Set X) = (U : Set X)
    rw [Set.image_univ, Subtype.range_coe]
  refine NatIso.ofComponents (fun M => ?_) ?_
  · let V : Opens X := (TopCat.Presheaf.imF U).obj (⊤ : Opens (Usp U))
    have eU : (forget₂ (ModuleCat.{u} (O.obj.obj (op U))) AddCommGrpCat.{u}).obj
        (M.val.obj (op U)) = (forget₂ (ModuleCat.{u} (O.obj.obj (op V)))
        AddCommGrpCat.{u}).obj (M.val.obj (op V)) :=
      congrArg (fun W : Opens X => (forget₂ (ModuleCat.{u} (O.obj.obj (op W)))
        AddCommGrpCat.{u}).obj (M.val.obj (op W))) hU.symm
    have hsc :
        (forget₂ (ModuleCat.{u} ((resRing U O).obj.obj (op (⊤ : Opens (Usp U)))))
          AddCommGrpCat.{u}).obj (((jStar U O).obj M).val.obj
            (op (⊤ : Opens (Usp U)))) =
        (forget₂ (ModuleCat.{u} ((resRing U O).obj.obj
          (op (⊤ : Opens (Usp U))))) AddCommGrpCat.{u}).obj
          ((ModuleCat.restrictScalars ((𝟙 (resRing U O) : resRing U O ⟶
            resRing U O).hom.app (op (⊤ : Opens (Usp U)))).hom).obj
              (M.val.obj (op V))) := by rfl
    apply eqToIso
    dsimp [sectionsOnOpen, sectionsOnOpenSubspace, ExtensionByZeroModules.jStar,
      SheafOfModules.pushforward, SheafOfModules.evaluation, SheafOfModules.forget,
      PresheafOfModules.pushforward, PresheafOfModules.restrictScalars,
      PresheafOfModules.restrictScalarsObj, PresheafOfModules.pushforward₀,
      PresheafOfModules.pushforward₀Obj, PresheafOfModules.evaluation_obj,
      Functor.sheafPushforwardContinuous_obj_obj_obj]
    exact eU.trans hsc
  · intro M N f
    let z : ∀ V : Opens X,
        (forget₂ (ModuleCat.{u} (O.obj.obj (op V))) AddCommGrpCat.{u}).obj
            ((ModuleCat.restrictScalars (RingHom.id _)).obj (M.val.obj (op V))) ⟶
          (forget₂ (ModuleCat.{u} (O.obj.obj (op V))) AddCommGrpCat.{u}).obj
            ((ModuleCat.restrictScalars (RingHom.id _)).obj (N.val.obj (op V))) :=
      fun V => (forget₂ (ModuleCat.{u} (O.obj.obj (op V))) AddCommGrpCat.{u}).map
        ((ModuleCat.restrictScalars (RingHom.id _)).map (f.val.app (op V)))
    convert CategoryTheory.eqToHom_naturality z hU.symm using 1 <;> rfl

open Stacks.Cohomology.Localization (enoughKInjectives derivedUnit_isIsoOnKInjective
  natTrans_isIso_of_kInjectives rightDerived_of_kInjectives)

/-- Degree-`p` cohomology over an open agrees naturally with degree-`p` cohomology after
restriction to that open.  The component at `K` is the isomorphism
`H^p(U, K) ≅ H^p(U, K|_U)`. -/
@[stacks 0D5V "`H^p(U, K) ≅ H^p(U, K|_U)`, natural in `K` in `D(O_X)`, for every open `U` of a \
ringed space `X` and every degree `p`"]
public noncomputable def cohomologyOnOpenIsoRestriction {X : TopCat.{u}}
    (O : Sheaf (Opens.grothendieckTopology X) RingCat.{u}) (U : Opens X)
    [HasDerivedCategory.{wX} (SheafOfModules.{u} O)]
    [HasDerivedCategory.{wU} (SheafOfModules.{u} (resRing U O))]
    [HasDerivedCategory.{wG} AddCommGrpCat.{u}] (p : ℤ) :
    derivedSectionsOnOpen O U ⋙ DerivedCategory.homologyFunctor AddCommGrpCat.{u} p ≅
      derivedRestriction O U ⋙ derivedSectionsOnOpenSubspace O U ⋙
        DerivedCategory.homologyFunctor AddCommGrpCat.{u} p :=
  by
    let c := ComplexShape.up ℤ
    let jHC := (jStar U O).mapHomotopyCategory c
    let qX : HomotopyCategory (SheafOfModules.{u} O) c ⥤
        DerivedCategory (SheafOfModules.{u} O) := DerivedCategory.Qh
    let qU : HomotopyCategory (SheafOfModules.{u} (resRing U O)) c ⥤
        DerivedCategory (SheafOfModules.{u} (resRing U O)) := DerivedCategory.Qh
    let qAb : HomotopyCategory AddCommGrpCat.{u} c ⥤
        DerivedCategory AddCommGrpCat.{u} := DerivedCategory.Qh
    let γU := (homotopySectionsOnOpenSubspace O U).totalRightDerivedUnit qU
      (HomotopyCategory.quasiIso (SheafOfModules.{u} (resRing U O)) c)
    let γR := (homotopyRestriction O U).totalRightDerivedUnit qX
      (HomotopyCategory.quasiIso (SheafOfModules.{u} O) c)
    let hs := (Functor.mapHomotopyCategoryCompIso (sectionsRestrictionIso O U).symm c).symm
    let hsec : homotopySectionsOnOpen O U ≅ jHC ⋙ homotopySectionsOnOpenSubspace O U := by
      change (sectionsOnOpen O U).mapHomotopyCategory c ⋙ qAb ≅
        jHC ⋙ ((sectionsOnOpenSubspace O U).mapHomotopyCategory c ⋙ qAb)
      exact Functor.isoWhiskerRight hs qAb ≪≫ Functor.associator _ _ _
    let α : homotopySectionsOnOpen O U ⟶
        qX ⋙ (derivedRestriction O U ⋙ derivedSectionsOnOpenSubspace O U) :=
      hsec.hom ≫
        Functor.whiskerLeft jHC γU ≫
        (Functor.associator jHC qU (derivedSectionsOnOpenSubspace O U)).inv ≫
        Functor.whiskerRight γR (derivedSectionsOnOpenSubspace O U) ≫
        (Functor.associator _ _ _).hom
    have hα : ∀ (I : CochainComplex (SheafOfModules.{u} O) ℤ) [I.IsKInjective],
        IsIso (α.app ((HomotopyCategory.quotient (SheafOfModules.{u} O) c).obj I)) := by
      intro I hI
      let I' : CochainComplex (SheafOfModules.{u} (resRing U O)) ℤ :=
        ((jStar U O).mapHomologicalComplex c).obj I
      let _ : I'.IsKInjective := inferInstance
      let _ := derivedUnit_isIsoOnKInjective (homotopyRestriction O U)
        (derivedRestriction O U) γR I
      let _ := derivedUnit_isIsoOnKInjective (homotopySectionsOnOpenSubspace O U)
        (derivedSectionsOnOpenSubspace O U) γU I'
      have hU' : IsIso (γU.app (jHC.obj
          ((HomotopyCategory.quotient (SheafOfModules.{u} O) c).obj I))) := by
        change IsIso (γU.app
          ((HomotopyCategory.quotient (SheafOfModules.{u} (resRing U O)) c).obj I'))
        infer_instance
      let _ := hU'
      dsimp [α]
      infer_instance
    letI := rightDerived_of_kInjectives (homotopySectionsOnOpen O U)
      (derivedRestriction O U ⋙ derivedSectionsOnOpenSubspace O U) α hα
    let e := Functor.rightDerivedNatIso (derivedSectionsOnOpen O U)
      (derivedRestriction O U ⋙ derivedSectionsOnOpenSubspace O U)
      ((homotopySectionsOnOpen O U).totalRightDerivedUnit qX
        (HomotopyCategory.quasiIso (SheafOfModules.{u} O) c)) α
      (HomotopyCategory.quasiIso (SheafOfModules.{u} O) c) (Iso.refl _)
    exact Functor.isoWhiskerRight e (DerivedCategory.homologyFunctor AddCommGrpCat.{u} p)

end Stacks.Cohomology.OpenSubspace
