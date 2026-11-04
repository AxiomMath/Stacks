module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.FiniteEtaleExt
public import StacksFrontier.CategoryTheory.Sites.Point.FreeSheafFiber
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.ConstantSheafInverseImage
public import Mathlib.CategoryTheory.Sites.Adjunction
public import Mathlib.CategoryTheory.Sites.Subcanonical
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.SmallEtaleInverseImageRepresentable

/-!
# The free sheaf of modules on a representable sheaf of sets

Let `X` be a scheme and `Λ` a ring. Sheafifying the free module on the sections of a sheaf of
sets `P` on the small étale site of `X` gives the free sheaf of `Λ`-modules `Λ[P]`, left adjoint
to the underlying sheaf of sets (`Stacks.EtaleCohomology.etaleModuleFreeAdj`). When `P` is the
sheaf represented by a finite étale `V ⟶ X` with structure morphism `π`, both `Λ[P]` and the
direct image `π_* Λ_V` corepresent the functor `F ↦ F(V)` — the second because `π_*` is left
adjoint to restriction for a finite étale `π`
(`Stacks.EtaleCohomology.etaleModuleDirectImageRestrictionAdj`) — so they are isomorphic
(`Stacks.EtaleCohomology.etaleModuleFreeIsoDirectImage`).

This is how the cohomology of the free sheaf on a torsor is computed on the cover that represents
it: `Hⁿ(X, Λ[P]) ≅ Hⁿ(X, π_* Λ_V) ≅ Hⁿ(V, Λ)`.

## Main definitions

* `Stacks.EtaleCohomology.etaleModuleFree`, `Stacks.EtaleCohomology.etaleModuleFreeAdj`: the
  free sheaf of modules on a sheaf of sets, and its adjunction.
* `Stacks.EtaleCohomology.etaleModuleFreeCorepresentation`,
  `Stacks.EtaleCohomology.etaleModuleDirectImageCorepresentation`: the two corepresentations of
  `F ↦ F(V)`.
* `Stacks.EtaleCohomology.etaleModuleFreeIsoDirectImage`: `Λ[P] ≅ π_* Λ_V`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

namespace Stacks.EtaleCohomology

variable (Λ : Type) [CommRing Λ]

variable (X : Scheme.{u})

/-- **The free sheaf of `Λ`-modules** on a sheaf of sets on the small étale site of `X`: the
sheafification of the free module on its sections. -/
abbrev etaleModuleFree :
    Sheaf X.smallEtaleTopology (Type (u + 1)) ⥤ EtaleModules.{u, 0} Λ X :=
  Sheaf.composeAndSheafify X.smallEtaleTopology (ModuleCat.freeSplit.{u + 1, 0} Λ)

/-- The free sheaf of modules is left adjoint to the underlying sheaf of sets. -/
def etaleModuleFreeAdj :
    etaleModuleFree Λ X ⊣ sheafCompose X.smallEtaleTopology (forget (ModuleCat.{u + 1} Λ)) :=
  Sheaf.adjunction X.smallEtaleTopology (ModuleCat.freeSplitAdj.{u + 1} Λ)

/-- **Yoneda for a representable sheaf of sets**: maps out of the sheaf represented by `V` are
sections over `V`, naturally in the target. -/
def uliftYonedaCorepresentation (V : X.Etale) :
    coyoneda.obj (op (X.smallEtaleTopology.uliftYoneda.{u + 1}.obj V)) ≅
      sheafToPresheaf X.smallEtaleTopology (Type (u + 1)) ⋙
        (evaluation _ _).obj (op V) :=
  NatIso.ofComponents (fun F => (X.smallEtaleTopology.uliftYonedaEquiv.{u + 1}).toIso)
    (fun {F G} g => by
      ext f
      rfl)

/-- **The free sheaf of modules on the sheaf represented by `V` corepresents sections over `V`.**
-/
def etaleModuleFreeCorepresentation (P : Sheaf X.smallEtaleTopology (Type (u + 1)))
    (V : X.Etale) (e : P ≅ X.smallEtaleTopology.uliftYoneda.{u + 1}.obj V) :
    coyoneda.obj (op ((etaleModuleFree Λ X).obj P)) ≅
      sheafToPresheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ) ⋙
        (evaluation _ _).obj (op V) ⋙ forget (ModuleCat.{u + 1} Λ) :=
  (Adjunction.compCoyonedaIso (etaleModuleFreeAdj Λ X)).app (op P) ≪≫
    Functor.isoWhiskerLeft (sheafCompose X.smallEtaleTopology (forget (ModuleCat.{u + 1} Λ)))
      ((coyoneda.mapIso e.op).symm ≪≫ uliftYonedaCorepresentation X V)

/-- Maps out of the free module `Λ` (on `ULift Λ`) are elements, naturally in the target. -/
def moduleULiftCorepresentation :
    coyoneda.obj (op (ModuleCat.of Λ (ULift.{u + 1} Λ))) ≅ forget (ModuleCat.{u + 1} Λ) :=
  NatIso.ofComponents
    (fun N =>
      (Stacks.Cohomology.GlobalSections.moduleULiftHomAddEquiv.{0, u + 1} Λ N).toEquiv.toIso)
    (fun {N N'} g => by
      ext f
      rfl)

variable {X}

/-- Composition with the structure morphism of `V` sends the final object of the small étale
site of `V` to `V`. -/
def smallEtaleComposeEtaleSiteTerminalIso (V : X.Etale) :
    letI : Etale V.hom := V.prop
    (Scheme.Etale.smallEtaleCompose V.hom).obj (etaleSiteTerminal V.left) ≅ V :=
  letI : Etale V.hom := V.prop
  MorphismProperty.Over.isoMk (Iso.refl _) (by
    rw [Scheme.Etale.smallEtaleCompose_obj_hom]
    change 𝟙 _ ≫ V.hom = 𝟙 _ ≫ V.hom
    rfl)

/-- **The direct image of the constant sheaf along a finite étale `V ⟶ X` corepresents sections
over `V`**: `π_*` is left adjoint to restriction along `π`, the constant sheaf corepresents
global sections, and restriction followed by global sections is sections over `V`. -/
def etaleModuleDirectImageCorepresentation (V : X.Etale) [IsFinite V.hom] :
    letI : Etale V.hom := V.prop
    coyoneda.obj (op ((etaleModuleDirectImage.{u, 0} Λ V.hom).obj
        (Stacks.Cohomology.GlobalSections.constantModuleSheaf.{0} Λ
          V.left.smallEtaleTopology))) ≅
      sheafToPresheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ) ⋙
        (evaluation _ _).obj (op V) ⋙ forget (ModuleCat.{u + 1} Λ) :=
  letI : Etale V.hom := V.prop
  (Adjunction.compCoyonedaIso (etaleModuleDirectImageRestrictionAdj.{u, 0} Λ V.hom)).app
      (op _) ≪≫
    Functor.isoWhiskerLeft (etaleModuleRestriction.{u, 0} Λ V.hom)
      ((Adjunction.compCoyonedaIso (constantSheafAdj V.left.smallEtaleTopology
          (ModuleCat.{u + 1} Λ) (etaleSiteTerminalIsTerminal V.left))).app
          (op (ModuleCat.of Λ (ULift.{u + 1} Λ))) ≪≫
        Functor.isoWhiskerLeft _ (moduleULiftCorepresentation.{u} Λ)) ≪≫
    (NatIso.ofComponents
      (fun F => (forget (ModuleCat.{u + 1} Λ)).mapIso
        (F.obj.mapIso (smallEtaleComposeEtaleSiteTerminalIso V).op))
      (fun {F G} g => by
        ext x
        exact (NatTrans.naturality_apply g.hom
          (smallEtaleComposeEtaleSiteTerminalIso V).hom.op x).symm) :
      etaleModuleRestriction.{u, 0} Λ V.hom ⋙
          (sheafSections V.left.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
            (op (etaleSiteTerminal V.left)) ⋙ forget (ModuleCat.{u + 1} Λ) ≅
        sheafToPresheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ) ⋙
          (evaluation _ _).obj (op V) ⋙ forget (ModuleCat.{u + 1} Λ))

/-- **The free sheaf of modules on a torsor represented by a finite étale `V ⟶ X` is the direct
image of the constant sheaf**: `Λ[P] ≅ π_* Λ_V`, both corepresenting sections over `V`. -/
def etaleModuleFreeIsoDirectImage (P : Sheaf X.smallEtaleTopology (Type (u + 1)))
    (V : X.Etale) [IsFinite V.hom] (e : P ≅ X.smallEtaleTopology.uliftYoneda.{u + 1}.obj V) :
    letI : Etale V.hom := V.prop
    (etaleModuleFree Λ X).obj P ≅ (etaleModuleDirectImage.{u, 0} Λ V.hom).obj
        (Stacks.Cohomology.GlobalSections.constantModuleSheaf.{0} Λ V.left.smallEtaleTopology) :=
  (Coyoneda.fullyFaithful.preimageIso
    (etaleModuleFreeCorepresentation Λ X P V e ≪≫
      (etaleModuleDirectImageCorepresentation Λ V).symm)).unop.symm

end Stacks.EtaleCohomology

end
