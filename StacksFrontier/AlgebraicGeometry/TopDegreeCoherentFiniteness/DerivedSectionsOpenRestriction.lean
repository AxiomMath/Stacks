module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.RightDerivedSheafToPresheafNaturality
public import StacksFrontier.Topology.Sheaves.Cohomology.ModuleComparison.CompatibilityWithRestriction
public import StacksFrontier.Topology.Sheaves.Cohomology.Vanishing.SpectralSpaces
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedFunctors.ForgetfulInclusionCohomologyPresheaf

/-!
# Restriction to an open in the top degree, for derived sections

[Stacks, Tag 0A3G] clause (2) says that on a spectral space of dimension at most `d` the
restriction `H^d(X, F) ⟶ H^d(U, F)` to a quasi-compact open is surjective. The library has it
for Mathlib's `Ext`-theoretic cohomology presheaf
(`Stacks.CohomologyVanishing.surjective_cohomologyPresheaf_map_top_of_topologicalKrullDim_le`).
This file transports it to the restriction maps of right-derived sections, for abelian sheaves
and for sheaves of modules, along comparisons that are natural in the open:

* the right-derived functors of the inclusion of abelian sheaves into presheaves are the
  cohomology presheaves (`Stacks.Cohomology.rightDerivedSheafToPresheafIso`, Stacks 03AY), and
  evaluating them at an open is deriving sections there;
* for a sheaf of modules, derived module sections forget to derived abelian sections compatibly
  with restriction (`Stacks.Cohomology.ModuleComparison.sectionsComparisonIso_naturality`).
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace Stacks.TopDegreeRestriction

open Stacks.Cohomology.ModuleComparison

section Abelian

variable {X : Type u} [TopologicalSpace X]

/-- The functor of sections over an open `U` on abelian sheaves is additive. -/
local instance sheafSections_additive' (U : Opens X) :
    ((sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj (op U)).Additive where
  map_add := by intros; rfl

/-- Evaluating the right-derived functors of the inclusion of abelian sheaves into presheaves at
an open is deriving sections over that open, compatibly with restriction. -/
theorem rightDerivedCompIso_evaluation_naturality {U V : Opens X} (h : U ≤ V) (p : ℕ)
    (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :
    (((sheafToPresheaf _ AddCommGrpCat.{u}).rightDerived p).obj F).map (homOfLE h).op ≫
        (Stacks.Cohomology.DerivedForget.rightDerivedCompIso
          (sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
          ((evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj (op U)) p).hom.app F =
      (Stacks.Cohomology.DerivedForget.rightDerivedCompIso
          (sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
          ((evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj (op V)) p).hom.app F ≫
        (NatTrans.rightDerived (sectionsRestriction (Opens.grothendieckTopology X)
          (homOfLE h)) p).app F := by
  let EV := (evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj (op V)
  let EU := (evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj (op U)
  let α : EV ⟶ EU := (evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).map (homOfLE h).op
  have : EV.PreservesHomology := EV.preservesHomologyOfExact
  have : EU.PreservesHomology := EU.preservesHomologyOfExact
  change α.app (((sheafToPresheaf _ AddCommGrpCat.{u}).rightDerived p).obj F) ≫
      (Stacks.Cohomology.DerivedForget.rightDerivedCompIso
        (sheafToPresheaf _ AddCommGrpCat.{u}) EU p).hom.app F =
    (Stacks.Cohomology.DerivedForget.rightDerivedCompIso
        (sheafToPresheaf _ AddCommGrpCat.{u}) EV p).hom.app F ≫
      (NatTrans.rightDerived (Functor.whiskerLeft (sheafToPresheaf _ AddCommGrpCat.{u}) α) p).app F
  unfold Stacks.Cohomology.DerivedForget.rightDerivedCompIso
  dsimp [NatTrans.rightDerived, NatTrans.rightDerivedToHomotopyCategory]
  let K := ((sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).mapHomologicalComplex
    (ComplexShape.up ℕ)).obj
    ((injectiveResolutions (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})).obj F).as
  unfold Functor.rightDerived Functor.rightDerivedToHomotopyCategory
  simp only [Functor.comp_obj]
  unfold HomotopyCategory.homologyFunctor
  change α.app (K.sc p).homology ≫ ((K.sc p).mapHomologyIso EU).inv =
    ((K.sc p).mapHomologyIso EV).inv ≫
      ShortComplex.homologyMap ((K.sc p).mapNatTrans α)
  simp only [NatTrans.app_homology, Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- **[Stacks, Tag 0A3G] clause (2) for right-derived sections of abelian sheaves.** On a spectral
space of dimension at most `d`, the restriction of the `d`-th right-derived sections of an abelian
sheaf `F` from `X` to a quasi-compact open `U` is surjective. -/
theorem surjective_rightDerived_sectionsRestriction [SpectralSpace X]
    [HasExt.{u} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})]
    (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) (d : ℕ)
    (hdim : topologicalKrullDim X ≤ (d : WithBot ℕ∞)) (U : Opens X)
    (hU : IsCompact (U : Set X)) :
    Function.Surjective ((NatTrans.rightDerived (sectionsRestriction
      (Opens.grothendieckTopology X) (homOfLE (show U ≤ ⊤ from le_top))) d).app F) := by
  have hsurj :=
    Stacks.CohomologyVanishing.surjective_cohomologyPresheaf_map_top_of_topologicalKrullDim_le
      F d hdim U hU
  let P := ((sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).rightDerived d).obj F
  let e := (Stacks.Cohomology.rightDerivedSheafToPresheafIso (Opens.grothendieckTopology X) d).app F
  have hP : Function.Surjective (P.map (homOfLE (show U ≤ ⊤ from le_top)).op) := by
    intro y
    obtain ⟨x, hx⟩ := hsurj (e.hom.app (op U) y)
    refine ⟨e.inv.app (op ⊤) x, ?_⟩
    apply (ConcreteCategory.bijective_of_isIso (e.hom.app (op U))).1
    have hn := ConcreteCategory.congr_hom (e.hom.naturality (homOfLE (show U ≤ ⊤ from le_top)).op)
      (e.inv.app (op ⊤) x)
    have hx' : e.hom.app (op ⊤) (e.inv.app (op ⊤) x) = x := (e.app (op ⊤)).inv_hom_id_apply x
    refine hn.trans ?_
    change ((Sheaf.cohomologyPresheafFunctor _ d).obj F).map _ (e.hom.app _ (e.inv.app _ x)) = _
    rwa [hx']
  have hnat := rightDerivedCompIso_evaluation_naturality (X := X) (show U ≤ ⊤ from le_top) d F
  let eU := (Stacks.Cohomology.DerivedForget.rightDerivedCompIso
    (sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    ((evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj (op U)) d).app F
  let eT := (Stacks.Cohomology.DerivedForget.rightDerivedCompIso
    (sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    ((evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj (op ⊤)) d).app F
  intro y
  obtain ⟨x, hx⟩ := hP (eU.inv y)
  refine ⟨eT.hom x, ?_⟩
  refine (ConcreteCategory.congr_hom hnat x).symm.trans ?_
  change eU.hom (P.map _ x) = y
  rw [hx]
  exact eU.inv_hom_id_apply y

end Abelian

section Modules

variable {X : Type u} [TopologicalSpace X] (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u})

/-- **[Stacks, Tag 0A3G] clause (2) for cohomology of sheaves of modules.** On a spectral space of
dimension at most `d`, restriction `H^d(X, G) ⟶ H^d(U, G)` to a quasi-compact open is
surjective, for every sheaf of modules `G`. -/
theorem surjective_hrestrict_of_topologicalKrullDim_le [SpectralSpace X]
    [HasExt.{u} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})]
    (G : SheafOfModules.{u} R) (d : ℕ) (hdim : topologicalKrullDim X ≤ (d : WithBot ℕ∞))
    (U : Opens X) (hU : IsCompact (U : Set X)) :
    Function.Surjective (Hrestrict R (show U ≤ ⊤ from le_top) d G) := by
  have key := Stacks.Cohomology.ModuleComparison.sectionsComparisonIso_naturality
    (Opens.grothendieckTopology X) R (homOfLE (show U ≤ ⊤ from le_top)) d
  have hab := surjective_rightDerived_sectionsRestriction
    ((SheafOfModules.toSheaf R).obj G) d hdim U hU
  let eU := (ModuleSheafCohomology.sectionsComparisonIso (Opens.grothendieckTopology X) R U d).app G
  let eT := (ModuleSheafCohomology.sectionsComparisonIso (Opens.grothendieckTopology X) R ⊤ d).app G
  intro y
  obtain ⟨x, hx⟩ := hab (eU.hom y)
  refine ⟨eT.inv x, ?_⟩
  apply (ConcreteCategory.bijective_of_isIso eU.hom).1
  refine (ConcreteCategory.congr_hom (NatTrans.congr_app key G) (eT.inv x)).trans ?_
  change (NatTrans.rightDerived (sectionsRestriction (Opens.grothendieckTopology X)
    (homOfLE (show U ≤ ⊤ from le_top))) d).app _ (eT.hom (eT.inv x)) = _
  rwa [eT.inv_hom_id_apply]

end Modules

end Stacks.TopDegreeRestriction

end
