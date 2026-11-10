module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleModuleInverseImage
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocallyConstantSerreClass
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ModuleSheafSideConditions
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.RepresentableSheaves
public import StacksFrontier.CategoryTheory.Sites.Continuous.PullbackOfSheafifiedYoneda
public import StacksFrontier.CategoryTheory.Sites.PullbackSheafComposeNatIso
public import StacksFrontier.CategoryTheory.Sites.Representable.SheafifiedYonedaSubcanonical

/-!
# Sections of the inverse image of a represented sheaf

Let `g : X' ⟶ X` be a morphism of schemes and `F` a sheaf of `Λ`-modules on the small étale site of
`X` whose underlying sheaf of sets is represented by a section `ε ∈ F(V)`: the map `h^#_V ⟶ F♭`
corresponding to `ε` is an isomorphism. This file shows that the pulled back section
`u(ε) ∈ (g⁻¹F)(g⁻¹V)`, `u` the unit of `g⁻¹ ⊣ g_*`, represents the underlying sheaf of sets of
`g⁻¹F`, so that every section of `g⁻¹F` over an étale `X'`-scheme `W'` is the restriction of `u(ε)`
along a unique morphism `W' ⟶ g⁻¹V`.

## Main definitions

* `Stacks.EtaleCohomology.etaleModuleInverseImageForgetIso` — `g⁻¹(F♭) ≅ (g⁻¹F)♭`: inverse image
  commutes with passing to the underlying sheaves of sets.
* `Stacks.EtaleCohomology.moduleUnitSection` — the pulled back section `u(ε)`.

## Main results

* `CategoryTheory.Sheaf.isIso_sectionEquiv_symm_iff` — a section represents a sheaf of sets exactly
  when it corepresents evaluation at its object.
* `Stacks.EtaleCohomology.isIso_sectionEquiv_symm_moduleUnitSection` — pulled back representing
  sections represent.
* `Stacks.EtaleCohomology.bijective_map_moduleUnitSection` — sections of `g⁻¹F` are restrictions of
  `u(ε)` along unique morphisms.

## Implementation notes

The comparison `g⁻¹(F♭) ≅ (g⁻¹F)♭` is `CategoryTheory.Functor.sheafPullbackSheafComposeIso` for the
forgetful functor; it is characterized by carrying the unit to the unit, which is what moves `ε`.
The inverse image of a sheafified representable is the sheafified representable of the base change
(`CategoryTheory.Sheaf.sheafPullbackSheafifiedYonedaIso`), and the small étale site is
subcanonical (`AlgebraicGeometry.Scheme.smallEtaleTopology_subcanonical`), which turns sections of
`h^#_{g⁻¹V}` into morphisms.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry

universe u

namespace CategoryTheory.Sheaf

universe v' u'

/-- **A section represents a sheaf of sets exactly when it corepresents evaluation at its
object.** For a section `e` of a sheaf of sets `G` over `V`, the map `h^#_V ⟶ G` corresponding to
`e` is an isomorphism if and only if, for every sheaf of sets `K`, the morphisms `G ⟶ K` are
determined by, and determine arbitrarily, the image of `e`. -/
theorem isIso_sectionEquiv_symm_iff {C : Type u'} [Category.{v'} C] (J : GrothendieckTopology C)
    [HasWeakSheafify J (Type max u' v')] (G : Sheaf J (Type max u' v')) {V : C}
    (e : G.obj.obj (op V)) :
    IsIso ((sectionEquiv J).symm e) ↔
      ∀ K : Sheaf J (Type max u' v'), Function.Bijective (fun φ : G ⟶ K => φ.hom.app (op V) e) := by
  rw [isIso_iff_coyoneda_map_bijective]
  have key : ∀ K : Sheaf J (Type max u' v'), (fun φ : G ⟶ K => φ.hom.app (op V) e) =
      (sectionEquiv J) ∘ (fun φ : G ⟶ K => (sectionEquiv J).symm e ≫ φ) := by
    intro K
    funext φ
    rw [Function.comp_apply, sectionEquiv_comp, Equiv.apply_symm_apply]
  exact forall_congr' fun K => by
    rw [key K]
    exact (Function.Bijective.of_comp_iff' (Equiv.bijective _) _).symm

end CategoryTheory.Sheaf

namespace Stacks.EtaleCohomology

variable (Λ : Type) [Ring Λ] {X X' : Scheme.{u}} (g : X' ⟶ X)

/-- Sheafification of presheaves of `Λ`-modules on the small étale site, at the coefficient
universe `u + 1` (the instance `Stacks.EtaleCohomology.etaleModules_hasSheafify` with its ring
universe fixed, so that unification does not have to solve `u + 1 = max (u + 1) ?r`). -/
local instance etaleModules_hasSheafify_zero (X : Scheme.{u}) :
    HasSheafify X.smallEtaleTopology (ModuleCat.{u + 1} Λ) :=
  etaleModules_hasSheafify.{u, 0} Λ X

/-- The sheaf of sets underlying a sheaf of `Λ`-modules on the small étale site. -/
abbrev etaleModuleUnderlyingSets (X : Scheme.{u}) :
    EtaleModules.{u, 0} Λ X ⥤ Sheaf X.smallEtaleTopology (Type (u + 1)) :=
  sheafCompose X.smallEtaleTopology (forget (ModuleCat.{u + 1} Λ))

/-- The forgetful functor from `Λ`-modules preserves the colimits computing the left Kan
extension along the opposite of small étale base change: those indexing categories are
filtered. -/
theorem preservesColimitsOfShape_costructuredArrow_forget (Z : (X'.Etale)ᵒᵖ) :
    PreservesColimitsOfShape (CostructuredArrow (smallEtaleBaseChange g).op Z)
      (forget (ModuleCat.{u + 1} Λ)) := by
  have : IsFiltered (CostructuredArrow (smallEtaleBaseChange g).op Z) :=
    IsFiltered.of_equivalence
      (structuredArrowOpEquivalence (smallEtaleBaseChange g) (Opposite.unop Z))
  have : PreservesColimitsOfSize.{u, u + 1}
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}) :=
    ModuleCat.forget₂PreservesColimitsOfSize.{u + 1, 0, u, u + 1} Λ
  have : PreservesFilteredColimitsOfSize.{u, u + 1} (forget AddCommGrpCat.{u + 1}) :=
    preservesFilteredColimitsOfSize_of_univLE.{u + 1, u + 1, u, u + 1} _
  exact inferInstanceAs (PreservesColimitsOfShape
    (CostructuredArrow (smallEtaleBaseChange g).op Z)
    (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1} ⋙ forget AddCommGrpCat.{u + 1}))

/-- **Inverse image commutes with passing to the underlying sheaves of sets**: the comparison
`f⁻¹(F♭) ⟶ (f⁻¹F)♭` adjoint to the unit, an isomorphism. -/
def etaleModuleInverseImageForgetIso (F : EtaleModules.{u, 0} Λ X) :
    ((smallEtaleBaseChange g).sheafPullback (Type (u + 1)) X.smallEtaleTopology
      X'.smallEtaleTopology).obj ((etaleModuleUnderlyingSets Λ X).obj F) ≅
      (etaleModuleUnderlyingSets Λ X').obj ((etaleModuleInverseImage.{u, 0} Λ g).obj F) :=
  haveI := Stacks.ConstantSheaf.preservesSheafification_forget_moduleCat.{u, u + 1, 0, 0}
    X'.smallEtaleTopology Λ
  haveI := preservesColimitsOfShape_costructuredArrow_forget Λ g
  (smallEtaleBaseChange g).sheafPullbackSheafComposeIso (ModuleCat.{u + 1} Λ)
    X.smallEtaleTopology X'.smallEtaleTopology (forget (ModuleCat.{u + 1} Λ)) F

/-- Inverse image of sheaves of sets along a morphism of schemes, for the small étale sites. -/
abbrev etaleTypeInverseImage :
    Sheaf X.smallEtaleTopology (Type (u + 1)) ⥤ Sheaf X'.smallEtaleTopology (Type (u + 1)) :=
  (smallEtaleBaseChange g).sheafPullback (Type (u + 1)) X.smallEtaleTopology
    X'.smallEtaleTopology

/-- `g⁻¹ ⊣ g_*` for sheaves of sets on the small étale sites. -/
abbrev etaleTypeInverseImageAdj :=
  (smallEtaleBaseChange g).sheafAdjunctionContinuous (Type (u + 1)) X.smallEtaleTopology
    X'.smallEtaleTopology

/-- The section `u(e)` of `g⁻¹G` over `g⁻¹V` pulled back from a section `e` of `G` over `V` by the
unit of `g⁻¹ ⊣ g_*`. -/
abbrev typeUnitSection (G : Sheaf X.smallEtaleTopology (Type (u + 1))) {V : X.Etale}
    (e : G.obj.obj (op V)) :
    ((etaleTypeInverseImage g).obj G).obj.obj (op ((smallEtaleBaseChange g).obj V)) :=
  Sheaf.pushforwardSectionsEquiv (smallEtaleBaseChange g) X.smallEtaleTopology
    X'.smallEtaleTopology _ V (((etaleTypeInverseImageAdj g).unit.app G).hom.app (op V) e)

/-- **The pulled back section, as a map out of a sheafified representable.** For a section `e` of
a sheaf of sets `G` over `V`, the map `h^#_{g⁻¹V} ⟶ g⁻¹G` corresponding to the section `u(e)`
pulled back by the unit of `g⁻¹ ⊣ g_*` is `g⁻¹` of the map `h^#_V ⟶ G` corresponding to `e`,
through `g⁻¹ h^#_V ≅ h^#_{g⁻¹V}`. -/
theorem sectionEquiv_symm_typeUnit (G : Sheaf X.smallEtaleTopology (Type (u + 1))) {V : X.Etale}
    (e : G.obj.obj (op V)) :
    (Sheaf.sectionEquiv X'.smallEtaleTopology).symm (typeUnitSection g G e) =
      (Sheaf.sheafPullbackSheafifiedYonedaIso (smallEtaleBaseChange g) X.smallEtaleTopology
          X'.smallEtaleTopology V).inv ≫
        (etaleTypeInverseImage g).map ((Sheaf.sectionEquiv X.smallEtaleTopology).symm e) := by
  refine (Equiv.symm_apply_eq _).2 ?_
  have h := Sheaf.sheafPullbackSheafifiedYonedaIso_hom_comp (smallEtaleBaseChange g)
    X.smallEtaleTopology X'.smallEtaleTopology V ((etaleTypeInverseImage g).obj G)
    ((Sheaf.sheafPullbackSheafifiedYonedaIso (smallEtaleBaseChange g) X.smallEtaleTopology
          X'.smallEtaleTopology V).inv ≫
        (etaleTypeInverseImage g).map ((Sheaf.sectionEquiv X.smallEtaleTopology).symm e))
  rw [Iso.hom_inv_id_assoc] at h
  refine Eq.trans ?_ h
  have h1 : (etaleTypeInverseImageAdj g).homEquiv _ _
      ((etaleTypeInverseImage g).map ((Sheaf.sectionEquiv X.smallEtaleTopology).symm e)) =
      (Sheaf.sectionEquiv X.smallEtaleTopology).symm e ≫
        (etaleTypeInverseImageAdj g).unit.app G := by
    rw [Adjunction.homEquiv_unit]
    exact ((etaleTypeInverseImageAdj g).unit.naturality _).symm
  change _ = Sheaf.sectionEquiv X.smallEtaleTopology ((etaleTypeInverseImageAdj g).homEquiv _ _
    ((etaleTypeInverseImage g).map ((Sheaf.sectionEquiv X.smallEtaleTopology).symm e)))
  rw [h1, Sheaf.sectionEquiv_comp, Equiv.apply_symm_apply]
  rfl

/-- A section of a sheaf of `Λ`-modules, read as a section of its underlying sheaf of sets. -/
abbrev forgetSection {X : Scheme.{u}} (F : EtaleModules.{u, 0} Λ X) {V : X.Etale}
    (ε : F.obj.obj (op V)) : ((etaleModuleUnderlyingSets Λ X).obj F).obj.obj (op V) :=
  ε

/-- The section `u(ε)` of `g⁻¹F` over `g⁻¹V` pulled back from a section `ε` of a sheaf of
`Λ`-modules `F` over `V` by the unit of `g⁻¹ ⊣ g_*`. -/
abbrev moduleUnitSection (F : EtaleModules.{u, 0} Λ X) {V : X.Etale} (ε : F.obj.obj (op V)) :
    ((etaleModuleInverseImage.{u, 0} Λ g).obj F).obj.obj (op ((smallEtaleBaseChange g).obj V)) :=
  ((etaleModuleInverseImageAdj.{u, 0} Λ g).unit.app F).hom.app (op V) ε

/-- **The comparison `g⁻¹(F♭) ≅ (g⁻¹F)♭` carries the pulled back section of the sheaf of sets to
the pulled back section of the sheaf of modules.** -/
theorem etaleModuleInverseImageForgetIso_hom_typeUnitSection (F : EtaleModules.{u, 0} Λ X)
    {V : X.Etale} (ε : F.obj.obj (op V)) :
    (etaleModuleInverseImageForgetIso Λ g F).hom.hom.app (op ((smallEtaleBaseChange g).obj V))
        (typeUnitSection g ((etaleModuleUnderlyingSets Λ X).obj F) (forgetSection Λ F ε)) =
      forgetSection Λ _ (moduleUnitSection Λ g F ε) := by
  have := Stacks.ConstantSheaf.preservesSheafification_forget_moduleCat.{u, u + 1, 0, 0}
    X'.smallEtaleTopology Λ
  have := preservesColimitsOfShape_costructuredArrow_forget Λ g
  exact congrArg (fun φ => φ.hom.app (op V) ε)
    ((smallEtaleBaseChange g).unit_comp_pushforward_map_sheafPullbackSheafComposeHom
      (ModuleCat.{u + 1} Λ) X.smallEtaleTopology X'.smallEtaleTopology
      (forget (ModuleCat.{u + 1} Λ)) F)

/-- **Pulling back a representing section.** If a section `ε` of a sheaf of `Λ`-modules `F` over
`V` represents the underlying sheaf of sets, in the sense that the corresponding map
`h^#_V ⟶ F♭` is an isomorphism, then the pulled back section `u(ε)` of `g⁻¹F` over `g⁻¹V`
represents the underlying sheaf of sets of `g⁻¹F`. -/
theorem isIso_sectionEquiv_symm_moduleUnitSection (F : EtaleModules.{u, 0} Λ X) {V : X.Etale}
    (ε : F.obj.obj (op V))
    (hε : IsIso ((Sheaf.sectionEquiv X.smallEtaleTopology).symm (forgetSection Λ F ε))) :
    IsIso ((Sheaf.sectionEquiv X'.smallEtaleTopology).symm
      (forgetSection Λ _ (moduleUnitSection Λ g F ε))) := by
  rw [← etaleModuleInverseImageForgetIso_hom_typeUnitSection, Sheaf.sectionEquiv_symm_comp,
    sectionEquiv_symm_typeUnit]
  have : IsIso ((etaleTypeInverseImage g).map
      ((Sheaf.sectionEquiv X.smallEtaleTopology).symm (forgetSection Λ F ε))) :=
    Functor.map_isIso _ _
  exact IsIso.comp_isIso' (IsIso.comp_isIso' (Iso.isIso_inv _) this) (Iso.isIso_hom _)

/-- **Sections of a sheaf of sets represented by a section.** On the small étale site, which is
subcanonical, if the map `h^#_V ⟶ G` corresponding to a section `e` of `G` over `V` is an
isomorphism, then every section of `G` over any `W` is the restriction of `e` along a unique
morphism `W ⟶ V`. -/
theorem bijective_map_of_isIso_sectionEquiv_symm {Y : Scheme.{u}}
    (G : Sheaf Y.smallEtaleTopology (Type (u + 1))) {V : Y.Etale} (e : G.obj.obj (op V))
    (he : IsIso ((Sheaf.sectionEquiv Y.smallEtaleTopology).symm e)) (W : Y.Etale) :
    Function.Bijective (fun t : W ⟶ V => G.obj.map t.op e) := by
  set φ := (Sheaf.sectionEquiv Y.smallEtaleTopology).symm e
  have hf : (fun t : W ⟶ V => G.obj.map t.op e) =
      (φ.hom.app (op W)) ∘ (Sheaf.sectionEquiv Y.smallEtaleTopology) ∘
        (Sheaf.sheafifiedYoneda Y.smallEtaleTopology).map := by
    funext t
    rw [Function.comp_apply, Function.comp_apply, ← Sheaf.sectionEquiv_comp,
      Sheaf.sectionEquiv_map_comp, Equiv.apply_symm_apply]
  rw [hf]
  refine Function.Bijective.comp ?_ (Function.Bijective.comp (Equiv.bijective _)
    ((Sheaf.fullyFaithfulSheafifiedYoneda Y.smallEtaleTopology).map_bijective W V))
  exact (isIso_iff_bijective _).mp inferInstance

/-- **Sections of the inverse image of a represented sheaf.** If a section `ε` of a sheaf of
`Λ`-modules `F` over `V` represents the underlying sheaf of sets of `F`, then every section of
`g⁻¹F` over any étale `X'`-scheme `W'` is the restriction of the pulled back section `u(ε)` along
a unique morphism `W' ⟶ g⁻¹V`. -/
theorem bijective_map_moduleUnitSection (F : EtaleModules.{u, 0} Λ X) {V : X.Etale}
    (ε : F.obj.obj (op V))
    (hε : IsIso ((Sheaf.sectionEquiv X.smallEtaleTopology).symm (forgetSection Λ F ε)))
    (W' : X'.Etale) :
    Function.Bijective (fun t : W' ⟶ (smallEtaleBaseChange g).obj V =>
      ((etaleModuleInverseImage.{u, 0} Λ g).obj F).obj.map t.op (moduleUnitSection Λ g F ε)) :=
  bijective_map_of_isIso_sectionEquiv_symm _ _
    (isIso_sectionEquiv_symm_moduleUnitSection Λ g F ε hε) W'

end Stacks.EtaleCohomology

end
