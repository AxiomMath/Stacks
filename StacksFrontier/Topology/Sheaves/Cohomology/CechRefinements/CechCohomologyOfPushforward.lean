module

public import StacksFrontier.Topology.Sheaves.Cohomology.CechRefinements.ModuleComplexRefinementMap
public import
  StacksFrontier.Topology.Sheaves.Cohomology.CechAcyclicity.PushforwardOfAnInjectiveCechVanishing
public import StacksFrontier.Topology.Sheaves.Cohomology.CechOfSheavesOfModules.InjectiveVanishing

/-!
# Module-valued Čech cohomology from the Čech cohomology of the underlying abelian sheaf

The Čech complex of a cover `U` of an open `V` with coefficients in a sheaf of modules `F` is
built in [Stacks, Tag 01EP] over the slice category of opens over `V`, with values modules over
the ring of sections `R(V)`.  Forgetting the module structure identifies it with the Čech
complex of the family `U` of opens of the space with coefficients in the presheaf of abelian
groups underlying `F`: the two differ only by the identification of a product in the slice over
`V` with the corresponding intersection of opens.  Consequently a vanishing statement about the
Čech cohomology of the underlying abelian sheaf transports to the module-valued Čech complex.

This is the input [Stacks, Tag 01FD] needs about the pushforward of an injective module: part
(1) of [Stacks, Tag 01EX] is available for the underlying abelian sheaf, and the acyclicity
hypothesis of the Čech-to-derived-sections comparison is about the module-valued complex.

## Main definitions

* `Stacks.Cohomology.CechRefinement.cechComplexForgetIso`: the module-valued Čech complex of a
  cover, with its module structure forgotten, is the Čech complex of the same family of opens
  with coefficients in the underlying presheaf of abelian groups.

## Main results

* `Stacks.CategoryTheory.CechComplex.isIso_refinementMap_of_isIso`: a Čech refinement map along
  a reindexing by the identity is invertible as soon as it is invertible on each intersection.
* `Stacks.Cohomology.CechRefinement.isZero_cechComplexNat_homology_of_isZero_presheaf`: vanishing
  of the Čech cohomology of the underlying abelian sheaf gives vanishing of the module-valued
  Čech cohomology.
* `Stacks.Cohomology.CechRefinement.isZero_cechComplexNat_homology_pushforward_injective`:
  part (1) of [Stacks, Tag 01EX] for the module-valued Čech complex.

## Implementation notes

The comparison is assembled from two pieces that are already available:
`Stacks.CategoryTheory.CechComplex.coefficientsIso`, which commutes an additive product
preserving functor past the Čech complex, and
`Stacks.CategoryTheory.CechComplex.refinementMap` for the functor `Over.forget V`, the identity
reindexing of the index type and the restriction maps coming from
`Stacks.Cohomology.CechSheaf.inter_coverObject_left`.  The latter maps are isomorphisms, so the
refinement map is an isomorphism; that criterion is recorded here in the generality of
`refinementMap`.

The statement of `refinementMap` composes the reindexing with the selected tuple, so its
degreewise formula mentions `id ∘ x` rather than `x`.  The two are definitionally equal, so the
formula is restated once, by type ascription, in the spelling the rest of the argument rewrites
with; this avoids reassociating under a non-syntactic index.

## References

* [Stacks Project, Tag 01FD](https://stacks.math.columbia.edu/tag/01FD)
* [Stacks Project, Tag 01EP](https://stacks.math.columbia.edu/tag/01EP)
* [Stacks Project, Tag 01EX](https://stacks.math.columbia.edu/tag/01EX)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.Cohomology.CechSheaf (SectionRing coverObject sectionsPresheaf cechComplex
  inter_coverObject_left)
open Stacks.Cohomology.CechDerived (cechComplexNatFunctor)

universe vA vC vD uA uC uD uI u

namespace Stacks.CategoryTheory.CechComplex

/-! ### A refinement map that is an isomorphism -/

section RefinementIso

variable {C : Type uC} [Category.{vC} C] [HasFiniteProducts C] [Quiver.IsThin C]
  {D : Type uD} [Category.{vD} D] [HasFiniteProducts D]
  {A : Type uA} [Category.{vA} A] [Preadditive A] [HasProducts.{uI} A]
  {I : Type uI} (U : I → C) (V : I → D) (T : D ⥤ C)
  (P : Cᵒᵖ ⥤ A) (Q : Dᵒᵖ ⥤ A) (η : Q ⟶ T.op ⋙ P)
  (r : ∀ (n : ℕ) (x : Fin (n + 1) → I), inter U x ⟶ T.obj (inter V x))

/-- The degreewise formula for a refinement map along the identity reindexing, with the index
tuple written as `x` rather than as `id ∘ x`. -/
theorem refinementMap_id_comp_π (n : ℕ) (x : Fin (n + 1) → I) :
    (refinementMap U V T P Q η id r).f n ≫ π U P n x =
      π V Q n x ≫ η.app (op (inter V x)) ≫ P.map (r n x).op :=
  refinementMap_comp_π U V T P Q η id r n x

/-- **A Čech refinement map along the identity reindexing is an isomorphism as soon as it is one
on each intersection.**  This is the criterion under which [Stacks, Tag 01FD] identifies the
module-valued Čech complex of a cover with the Čech complex of the underlying presheaf of
abelian groups. -/
theorem isIso_refinementMap_of_isIso
    (h : ∀ (n : ℕ) (x : Fin (n + 1) → I),
      IsIso (η.app (op (inter V x)) ≫ P.map (r n x).op)) :
    IsIso (refinementMap U V T P Q η id r) := by
  have hcomp : ∀ n : ℕ, IsIso ((refinementMap U V T P Q η id r).f n) := by
    intro n
    refine ⟨lift V Q (fun z ↦ π U P n z ≫
      CategoryTheory.inv (η.app (op (inter V z)) ≫ P.map (r n z).op)), ?_, ?_⟩
    · refine hom_ext V Q fun y ↦ ?_
      rw [Category.assoc, lift_comp_π, ← Category.assoc, refinementMap_id_comp_π, Category.assoc,
        IsIso.hom_inv_id, Category.comp_id, Category.id_comp]
    · refine hom_ext U P fun y ↦ ?_
      rw [Category.assoc, refinementMap_id_comp_π, ← Category.assoc, lift_comp_π, Category.assoc,
        IsIso.inv_hom_id, Category.comp_id, Category.id_comp]
  exact HomologicalComplex.Hom.isIso_of_components _

end RefinementIso

end Stacks.CategoryTheory.CechComplex

namespace Stacks.Cohomology.CechRefinement

open Stacks.CategoryTheory.CechComplex

/-! ### Forgetting the module structure on the Čech complex of a cover -/

section Forget

variable {X : Type u} [TopologicalSpace X]
  (O : Sheaf (Opens.grothendieckTopology X) RingCat.{u}) {I : Type u}
  (V : Opens X) (U : I → Opens X) (hU : V = ⨆ i, U i) (F : SheafOfModules.{u} O)

/-- The forgetful functor from `R(V)`-modules to abelian groups. -/
abbrev forgetSections : ModuleCat.{u} (SectionRing O V) ⥤ AddCommGrpCat.{u} :=
  forget₂ (ModuleCat.{u} (SectionRing O V)) AddCommGrpCat.{u}

/-- **The sections of a sheaf of modules over an open of the slice over `V` are the sections of
its underlying abelian sheaf over the underlying open.**  Both sides carry the same underlying
abelian group, so the comparison is the identity. -/
def forgetSectionsUnit :
    sectionsPresheaf V F ⋙ forgetSections O V ⟶
      (Over.forget V).op ⋙ F.val.presheaf where
  app _ := 𝟙 _

/-- The restriction map from an intersection of members of the cover to the open underlying the
corresponding product in the slice over `V`: the two opens are equal. -/
def interCoverHom (n : ℕ) (x : Fin (n + 1) → I) :
    inter U x ⟶ (Over.forget V).obj (inter (coverObject U hU) x) :=
  eqToHom (inter_coverObject_left V U hU x).symm

/-- The map `interCoverHom V U hU n x` is an isomorphism. -/
instance isIso_interCoverHom (n : ℕ) (x : Fin (n + 1) → I) :
    IsIso (interCoverHom V U hU n x) := by
  dsimp only [interCoverHom]
  infer_instance

/-- The comparison of coefficients is the identity, so it drops out of the composite that the
degreewise refinement map is built from.  Stated as the composite rather than as a formula for
the component alone, because the two spellings of the identity's object are definitionally but
not syntactically equal. -/
theorem forgetSectionsUnit_app_comp_map (n : ℕ) (x : Fin (n + 1) → I) :
    (forgetSectionsUnit O V F).app (op (inter (coverObject U hU) x)) ≫
        F.val.presheaf.map (interCoverHom V U hU n x).op =
      F.val.presheaf.map (interCoverHom V U hU n x).op :=
  Category.id_comp _

/-- **The refinement map comparing the Čech complex of the cover read in the slice over `V`
with the Čech complex of the family of opens.**  This is the identification of
[Stacks, Tag 01EP] with the Čech complex of a family of opens that [Stacks, Tag 01FD] uses to
import vanishing statements about the underlying abelian sheaf. -/
def forgetRefinementMap :
    (CategoryTheory.cechComplexFunctor (coverObject U hU)).obj
        (sectionsPresheaf V F ⋙ forgetSections O V) ⟶
      (CategoryTheory.cechComplexFunctor U).obj F.val.presheaf :=
  refinementMap U (coverObject U hU) (Over.forget V) F.val.presheaf
    (sectionsPresheaf V F ⋙ forgetSections O V) (forgetSectionsUnit O V F) id
    (interCoverHom V U hU)

/-- The refinement map `forgetRefinementMap O V U hU F` is an isomorphism of complexes. -/
instance isIso_forgetRefinementMap : IsIso (forgetRefinementMap O V U hU F) :=
  isIso_refinementMap_of_isIso _ _ _ _ _ _ _ fun n x ↦ by
    rw [forgetSectionsUnit_app_comp_map]
    exact CategoryTheory.Functor.map_isIso F.val.presheaf (interCoverHom V U hU n x).op

/-- **The module-valued Čech complex of a cover, with its module structure forgotten, is the
Čech complex of the underlying presheaf of abelian groups.** -/
def cechComplexForgetIso :
    ((forgetSections O V).mapHomologicalComplex (ComplexShape.up ℕ)).obj
        ((cechComplexNatFunctor O V U hU).obj F) ≅
      (CategoryTheory.cechComplexFunctor U).obj F.val.presheaf :=
  coefficientsIso (coverObject U hU) (sectionsPresheaf V F) (forgetSections O V) ≪≫
    asIso (forgetRefinementMap O V U hU F)

/-- **Vanishing of the Čech cohomology of the underlying abelian sheaf gives vanishing of the
module-valued Čech cohomology.**  The forgetful functor is exact and faithful, so it detects
the vanishing, and `cechComplexForgetIso` identifies the two complexes. -/
theorem isZero_cechComplexNat_homology_of_isZero_presheaf (p : ℕ)
    (hp : IsZero (((CategoryTheory.cechComplexFunctor U).obj F.val.presheaf).homology p)) :
    IsZero (((cechComplexNatFunctor O V U hU).obj F).homology p) := by
  have hz : IsZero ((((forgetSections O V).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj ((cechComplexNatFunctor O V U hU).obj F)).homology p) :=
    hp.of_iso ((HomologicalComplex.homologyFunctor AddCommGrpCat.{u}
      (ComplexShape.up ℕ) p).mapIso (cechComplexForgetIso O V U hU F))
  have hz' : IsZero ((forgetSections O V).obj
      (((cechComplexNatFunctor O V U hU).obj F).homology p)) :=
    hz.of_iso ((((cechComplexNatFunctor O V U hU).obj F).sc p).mapHomologyIso
      (forgetSections O V)).symm
  refine (IsZero.iff_id_eq_zero _).2 ?_
  refine (forgetSections O V).map_injective ?_
  rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_zero]
  exact hz'.eq_of_src _ _

end Forget

/-! ### The pushforward of an injective module -/

section Pushforward

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
  (J : SheafOfModules.{u} (structureSheafRing X)) [Injective J]
  {I : Type u} (V : I → Opens Y.carrier) (hV : (⊤ : Opens Y.carrier) = ⨆ i, V i)

/-- **Part (1) of [Stacks, Tag 01EX] for the module-valued Čech complex.**  The positive-degree
module-valued Čech cohomology of the pushforward of an injective module vanishes.  This is the
acyclicity hypothesis under which [Stacks, Tag 01FD] compares the Čech complex of a cover of
`Y` with the derived global sections of a pushforward. -/
theorem isZero_cechComplexNat_homology_pushforward_injective (p : ℕ) (hp : 0 < p) :
    IsZero ((((cechComplexNatFunctor (structureSheafRing Y) ⊤ V hV)).obj
      ((RingedSpaceModuleAdjunction.modulePushforward f).obj J)).homology p) :=
  isZero_cechComplexNat_homology_of_isZero_presheaf _ _ _ _ _ p
    (Stacks.Cohomology.PushforwardAcyclic.pushforward_injective_cechCohomology_isZero
      f J V p hp)

end Pushforward

end Stacks.Cohomology.CechRefinement

end
