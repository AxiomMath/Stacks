module

public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.ModulePseudoFamily
public import StacksFrontier.CategoryTheory.Adjunction.LeftAdjointCompIsoHomEquiv

/-!
# Descent of sheaves of modules on a simplicial site

Let `S` be a simplicial-site situation and `O` a sheaf of commutative rings on its total site.
Stacks 09WF describes the sheaves on the total site by their restrictions to the components and
the transitions between them. This file supplies the two halves of that description for sheaves
of `O`-modules which Stacks 07TH needs.

* A family of morphisms between the restrictions of two sheaves of `O`-modules, compatible with
  the transitions, comes from a morphism of sheaves of `O`-modules
  (`CategoryTheory.SimplicialSiteSituation.totalModuleHomOfFamily`).
* A cartesian system of the family of modules on the components comes from a cartesian sheaf of
  `O`-modules on the total site.

## Main definitions

* `CategoryTheory.SimplicialSiteSituation.totalModuleHomOfFamily`: the morphism of sheaves of
  `O`-modules assembled from a compatible family of morphisms of their restrictions.

## Main results

* `CategoryTheory.SimplicialSiteSituation.componentModuleMap_totalModuleHomOfFamily`: the
  assembled morphism restricts to the given family.

## Implementation notes

The morphism of underlying sheaves of sets is assembled by
`CategoryTheory.SimplicialSiteSituation.totalHomOfFamily` of Stacks 09WF, which takes its family in
direct-image form; the family of morphisms of modules is compatible with the transitions of
modules, which are the mates of the direct-image transitions, so its underlying family is
compatible with the direct-image transitions of sheaves of sets. That the assembled morphism is
additive and linear is checked on sections over an object of the total category, which is the
image of an object of the component of its own degree; there the morphism is the given morphism
of modules of that component.

## References

* [Stacks Project, Tag 09WF](https://stacks.math.columbia.edu/tag/09WF)
* [Stacks Project, Tag 07TH](https://stacks.math.columbia.edu/tag/07TH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Stacks.Sheaves.RingedToposModules
open scoped Simplicial

universe u

namespace CategoryTheory.SimplicialSiteSituation

variable (S : SimplicialSiteSituation.{u}) (O : Sheaf S.totalTopology CommRingCat.{u})

/-! ### Restriction along an arrow of the total category, through the transition -/

/-- Restriction of a sheaf on the total site along an arrow from an object of degree `n` to an
object of degree `m` factors, naturally in the sheaf, through the direct-image transition of
Stacks 09WF along the simplex map `m ⟶ n` under the arrow, followed by a map out of the sections
of the direct image which depends only on the restriction to degree `n`. -/
theorem exists_restrictTransition_factorization {m n : SimplexCategory} {U : S.component n}
    {V : S.component m} (g : (S.inclusion n).obj U ⟶ (S.inclusion m).obj V) :
    ∃ (φ : m ⟶ n) (ε : (S.transitionMorphism φ).pushforward ⋙
        Sheaf.sectionsFunctor (S.componentTopology m) (op V) ⟶
          Sheaf.sectionsFunctor (S.componentTopology n) (op U)),
      ∀ H : Sheaf S.totalTopology (Type u),
        H.obj.map g.op = ((S.restrictTransition φ).app H).hom.app (op V) ≫
          ε.app ((S.restrict n).obj H) := by
  rcases S with ⟨C | C⟩
  · obtain ⟨b, k⟩ := g
    refine ⟨b.unop, { app := fun K => K.obj.map k.op
                      naturality := fun K K' α => (α.hom.naturality k.op).symm }, fun H => ?_⟩
    exact (restrictTransition_inl_arrow C b.unop H k).symm
  · obtain ⟨b, f⟩ := g
    refine ⟨b.unop,
      { app := fun K => ((C.underlying.map b).toFunctor.op.ran.obj K.obj).map f.op ≫
          (((C.underlying.map b).toFunctor.op.ranAdjunction (Type u)).counit.app K.obj).app
            (op U)
        naturality := fun K K' α => ?_ }, fun H => ?_⟩
    · have h₁ := ((C.underlying.map b).toFunctor.op.ran.map α.hom).naturality f.op
      have h₂ : ((C.underlying.map b).toFunctor.op.ran.map α.hom).app
            (op ((C.underlying.map b).toFunctor.obj U)) ≫
          (((C.underlying.map b).toFunctor.op.ranAdjunction (Type u)).counit.app K'.obj).app
            (op U) =
          (((C.underlying.map b).toFunctor.op.ranAdjunction (Type u)).counit.app K.obj).app
            (op U) ≫ α.hom.app (op U) :=
        NatTrans.congr_app
          (((C.underlying.map b).toFunctor.op.ranAdjunction (Type u)).counit.naturality α.hom)
          (op U)
      exact ((Category.assoc _ _ _).symm.trans ((h₁ =≫ _).symm.trans
        ((Category.assoc _ _ _).trans ((_ ≫= h₂).trans (Category.assoc _ _ _).symm))))
    · have h₁ := restrictTransition_inr_arrow C b.unop H f
      have h₃ : ((((C.underlying.map b.unop.op).toFunctor.op.ranAdjunction (Type u)).homEquiv
            _ _).symm ((restrictTransition ⟨Sum.inr C⟩ b.unop).app H).hom).app (op U) =
          ((restrictTransition ⟨Sum.inr C⟩ b.unop).app H).hom.app
              (op ((C.underlying.map b).toFunctor.obj U)) ≫
            (((C.underlying.map b).toFunctor.op.ranAdjunction (Type u)).counit.app
              ((restrict ⟨Sum.inr C⟩ n).obj H).obj).app (op U) :=
        NatTrans.congr_app (Adjunction.homEquiv_counit _ _ _ _) (op U)
      have h₂ := ((restrictTransition ⟨Sum.inr C⟩ b.unop).app H).hom.naturality f.op
      refine h₁.symm.trans ((congrArg (fun t =>
        H.obj.map ((Grothendieck.ι C.underlying (op m)).map f).op ≫ t) h₃).trans ?_)
      exact (Category.assoc _ _ _).symm.trans ((h₂ =≫ _).trans (Category.assoc _ _ _))

/-! ### Morphisms from compatible families -/

section HomOfFamily

variable {M N : SheafOfModules.{u} (S.totalRingSheaf O)}
  (β : ∀ n : SimplexCategory, S.componentModule O M n ⟶ S.componentModule O N n)
  (hβ : ∀ {m n : SimplexCategory} (φ : m ⟶ n),
    (S.componentModulePullback O φ).map (β m) ≫ S.componentTransition O N φ =
      S.componentTransition O M φ ≫ β n)

include hβ in
/-- A family of morphisms of restrictions compatible with the transitions of modules is
compatible with the direct-image transitions of modules. -/
theorem restrictTransitionModulesApp_naturality_of_family {m n : SimplexCategory} (φ : m ⟶ n) :
    β m ≫ S.restrictTransitionModulesApp O φ N =
      S.restrictTransitionModulesApp O φ M ≫
        (S.transitionRingedToposHom O φ).pushforwardModules.map (β n) := by
  rw [← S.fiberTransitionModules_adj O φ N, ← S.fiberTransitionModules_adj O φ M]
  exact Adjunction.homEquiv_naturality_left_square _ _ _ _ _ (hβ φ)

/-- The family of morphisms of underlying sheaves of sets of a family of morphisms of
restrictions, read between the restrictions of the underlying sheaves of sets. -/
def underlyingFamily (n : SimplexCategory) :
    (S.restrict n).obj (Sheaf.moduleSheaf.{u, u, u} (S.totalRingSheaf O) M) ⟶
      (S.restrict n).obj (Sheaf.moduleSheaf.{u, u, u} (S.totalRingSheaf O) N) :=
  (Sheaf.moduleSheafFunctor.{u, u, u} (S.componentRingSheaf (S.totalRingSheaf O) n)).map (β n)

include hβ in
/-- The underlying family of a family of morphisms of restrictions compatible with the
transitions of modules is compatible with the direct-image transitions of sheaves of sets. -/
theorem restrictTransition_naturality_of_family {m n : SimplexCategory} (φ : m ⟶ n) :
    S.underlyingFamily O β m ≫
        (S.restrictTransition φ).app (Sheaf.moduleSheaf.{u, u, u} (S.totalRingSheaf O) N) =
      (S.restrictTransition φ).app (Sheaf.moduleSheaf.{u, u, u} (S.totalRingSheaf O) M) ≫
        (S.transitionMorphism φ).pushforward.map (S.underlyingFamily O β n) :=
  Sheaf.hom_ext_sections fun X z => congrArg (fun t => t.hom.app X z)
    (congrArg (Sheaf.moduleSheafFunctor.{u, u, u} (S.componentRingSheaf (S.totalRingSheaf O) m)).map
      (S.restrictTransitionModulesApp_naturality_of_family O β hβ φ))

/-- **Stacks 09WF for sheaves of modules, on morphisms.** The morphism of sheaves of `O`-modules
assembled from a family of morphisms of their restrictions compatible with the transitions. -/
def totalModuleHomOfFamily : M ⟶ N :=
  ofSheafHom.{u, u, u}
    (S.totalHomOfFamily
      (S.underlyingFamily O β)
      (fun φ => S.restrictTransition_naturality_of_family O β hβ φ))
    (fun X x y => by
      obtain ⟨X⟩ := X
      obtain ⟨n, U, rfl⟩ : ∃ n U, (S.inclusion n).obj U = X :=
        ⟨_, _, S.inclusion_obj_totalObjFibre X⟩
      have key : ∀ z, (Sheaf.sectionsFunctor S.totalTopology (op ((S.inclusion n).obj U))).map
            (S.totalHomOfFamily (S.underlyingFamily O β)
              (fun φ => S.restrictTransition_naturality_of_family O β hβ φ)) z =
          ((β n).val.app (op U)).hom z := fun z =>
        congrArg (fun t : (S.restrict n).obj (Sheaf.moduleSheaf.{u, u, u} (S.totalRingSheaf O) M) ⟶
            (S.restrict n).obj (Sheaf.moduleSheaf.{u, u, u} (S.totalRingSheaf O) N) =>
              t.hom.app (op U) z)
          (S.restrict_map_totalHomOfFamily (S.underlyingFamily O β)
            (fun φ => S.restrictTransition_naturality_of_family O β hβ φ) n)
      rw [key, key, key]
      exact map_add ((β n).val.app (op U)).hom x y)
    (fun X r x => by
      obtain ⟨X⟩ := X
      obtain ⟨n, U, rfl⟩ : ∃ n U, (S.inclusion n).obj U = X :=
        ⟨_, _, S.inclusion_obj_totalObjFibre X⟩
      have key : ∀ z, (Sheaf.sectionsFunctor S.totalTopology (op ((S.inclusion n).obj U))).map
            (S.totalHomOfFamily (S.underlyingFamily O β)
              (fun φ => S.restrictTransition_naturality_of_family O β hβ φ)) z =
          ((β n).val.app (op U)).hom z := fun z =>
        congrArg (fun t : (S.restrict n).obj (Sheaf.moduleSheaf.{u, u, u} (S.totalRingSheaf O) M) ⟶
            (S.restrict n).obj (Sheaf.moduleSheaf.{u, u, u} (S.totalRingSheaf O) N) =>
              t.hom.app (op U) z)
          (S.restrict_map_totalHomOfFamily (S.underlyingFamily O β)
            (fun φ => S.restrictTransition_naturality_of_family O β hβ φ) n)
      rw [key, key]
      exact ((β n).val.app (op U)).hom.map_smul r x)

/-- The morphism assembled from a compatible family restricts to that family. -/
theorem componentModuleMap_totalModuleHomOfFamily (n : SimplexCategory) :
    S.componentModuleMap O (S.totalModuleHomOfFamily O β hβ) n = β n := by
  apply hom_ext_moduleSheafFunctor
  exact S.restrict_map_totalHomOfFamily (S.underlyingFamily O β)
    (fun φ => S.restrictTransition_naturality_of_family O β hβ φ) n

end HomOfFamily

end CategoryTheory.SimplicialSiteSituation

end
