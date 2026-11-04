module

public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeDualizingComplexCech
public import StacksFrontier.AlgebraicGeometry.Spaces.SimplicialSmallEtaleStrictCocyclePair
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigEtaleSpaceSiteOfBigFppf
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigFppfCechHypercoveringEtale
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SpacesEtaleDerivedModuleLiftFullyFaithful
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SpacesEtaleDerivedModuleLiftPullbackCocycle
public import StacksFrontier.CategoryTheory.Functor.CocycleTransportComparison
public import StacksFrontier.CategoryTheory.Shift.HomShiftVanishingOfFull
public meta import StacksFrontier.Tactic.HEqCongr

/-!
# Transport of a derived cocycle to the spaces-étale sites

Let `U` be a simplicial algebraic space whose face maps are étale and relatively representable
(for instance `n ↦ V_n ×_Y X` for the Čech nerve `V` of an étale, relatively representable
`b₀ : V₀ ⟶ Y`). An object `ω` of `D(𝒪_{U_0})` on the small étale site with an isomorphism
`α : L U(δ¹₁)^* ω ≅ L U(δ¹₀)^* ω` satisfying the cocycle condition on `U_2` is transported along
the derived transport `ι` to the spaces-étale sites, where the gluing of Stacks 0DLA takes place:
`ι ω` and `N_{δ¹₁}⁻¹ ≫ ι α ≫ N_{δ¹₀}`, `N_g : ι(Lg^*K) ≅ Lg^*(ιK)`, satisfy the cocycle condition
there.

## Main definitions

* `smallEtaleDerivedModulePullbackCompToSpacesEtaleDerivedModulesIso`:
  `ι(Lg^*K) ≅ Lg^*(ιK)` for `g` étale, on the algebraic spaces of a big fppf site.

## Main results

* `smallEtaleDerivedModulePullbackCompToSpacesEtaleDerivedModulesIso_pasteIso`:
  compatibility with the compositors at a factorization of simplex maps.
* `spacesEtaleDerivedCocycle_toSpacesEtaleDerivedModules`: the transported cocycle condition.
* `exists_spacesEtaleDerivedCocycle_cechOverPullback`: the descent datum of a relative dualizing
  complex on a Čech hypercovering, on the spaces-étale sites.
* `hom_shift_eq_zero_cechOverPullback`: its pullbacks to the terms of the hypercovering have no
  negative self-extensions.

## Implementation notes

The compositors `Q_{ij}` are combined in pairs in separate declarations before the cocycle
condition is assembled (`CategoryTheory.comp_inv_app_eq_of_comparison`): instantiating all six
compatibilities in one declaration exceeds the kernel's budget.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial

universe u

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck
-- The universe-polymorphic sheafification instances of the cotangent complex (imported through
-- the small-étale duality files) leave universe constraints of the spaces-étale sites stuck.
attribute [-instance] CategoryTheory.Sheaf.hasSheafifyAddCommGrpCat
  CategoryTheory.Sheaf.wEqualsLocallyBijectiveAddCommGrpCat

namespace AlgebraicGeometry.BigFppfSpaceSite

attribute [local instance 5000] SheafOfModules.instAbelian
-- No global `HasDerivedCategory` instance applies to modules on the small étale sites; at low
-- priority the standard model chooses nothing where a global one exists.
attribute [local instance low] HasDerivedCategory.standard
attribute [local instance 5000] Space.SmallEtale.instHasSheafify
  Space.SmallEtale.instWEqualsLocallyBijective
attribute [local instance] Space.etaleModulePullback_additive
  Space.preservesFiniteLimits_etaleModulePullback Space.preservesFiniteColimits_etaleModulePullback

open Space.SimplicialSpacesEtaleSite Stacks.Cohomology.DerivedPullbackOfToposHom

variable {S : Scheme.{u}} (T : BigFppfSpaceSite S)

/-- **`ι(Lg^*K) ≅ Lg^*(ιK)` for `g` étale**, on the algebraic spaces of a big fppf site `T`: the
isomorphism `BigEtaleSpaceSite.smallEtaleDerivedModulePullbackCompToSpacesEtaleDerivedModulesIso`
for the big étale site `T.bigEtaleSpaceSite` on the same algebraic spaces. -/
def smallEtaleDerivedModulePullbackCompToSpacesEtaleDerivedModulesIso {X Y : T.Spaces}
    (g : Y ⟶ X) (hg : Space.IsEtale T.schemeSite S T.scheme_mem g.hom) :
    letI := Space.spacesEtaleHasDerivedCategory T.schemeSite S T.scheme_mem X
    letI := Space.spacesEtaleHasDerivedCategory T.schemeSite S T.scheme_mem Y
    Space.smallEtaleDerivedModulePullback T.schemeSite S T.scheme_mem g ⋙
        Space.toSpacesEtaleDerivedModules T.schemeSite S T.scheme_mem Y ≅
      Space.toSpacesEtaleDerivedModules T.schemeSite S T.scheme_mem X ⋙
        derivedPullback (X := Space.spacesEtaleRingedTopos T.schemeSite S T.scheme_mem Y)
          (Y := Space.spacesEtaleRingedTopos T.schemeSite S T.scheme_mem X)
          (spacesEtaleRingedToposHom g) :=
  BigEtaleSpaceSite.smallEtaleDerivedModulePullbackCompToSpacesEtaleDerivedModulesIso
    T.bigEtaleSpaceSite g hg

variable {T}

/-- **`ι(Lg^*K) ≅ Lg^*(ιK)` is compatible with composition**: for étale, relatively
representable `g : Z ⟶ Y` and `f : Y ⟶ X`, `ι` of the compositor `Lf^* ⋙ Lg^* ≅ L(g ≫ f)^*` on
the small étale sites, followed by `ι(L(g ≫ f)^*K) ≅ L(g ≫ f)^*(ιK)`, is
`ι(Lg^*Lf^*K) ≅ Lg^*Lf^*(ιK)` followed by the compositor on the spaces-étale sites. -/
theorem smallEtaleDerivedModulePullbackCompToSpacesEtaleDerivedModulesIso_comp
    {X Y Z : T.Spaces} (g : Z ⟶ Y) (f : Y ⟶ X)
    (hf : etaleRepresentable T f) (hg : etaleRepresentable T g)
    (hgf : etaleRepresentable T (g ≫ f))
    (K : DerivedCategory (Space.Modules.{u, u} T.schemeSite S T.scheme_mem X.1 X.2)) :
    letI := Space.spacesEtaleHasDerivedCategory T.schemeSite S T.scheme_mem X
    letI := Space.spacesEtaleHasDerivedCategory T.schemeSite S T.scheme_mem Y
    letI := Space.spacesEtaleHasDerivedCategory T.schemeSite S T.scheme_mem Z
    (Space.toSpacesEtaleDerivedModules T.schemeSite S T.scheme_mem Z).map
        ((Space.smallEtaleDerivedModulePullbackCompIso T.schemeSite S T.scheme_mem g f).hom.app K) ≫
      (smallEtaleDerivedModulePullbackCompToSpacesEtaleDerivedModulesIso T (g ≫ f) hgf.1).hom.app K
          =
    (smallEtaleDerivedModulePullbackCompToSpacesEtaleDerivedModulesIso T g hg.1).hom.app
        ((Space.smallEtaleDerivedModulePullback T.schemeSite S T.scheme_mem f).obj K) ≫
      (derivedPullback (X := Space.spacesEtaleRingedTopos T.schemeSite S T.scheme_mem Z)
          (Y := Space.spacesEtaleRingedTopos T.schemeSite S T.scheme_mem Y)
          (spacesEtaleRingedToposHom g)).map
        ((smallEtaleDerivedModulePullbackCompToSpacesEtaleDerivedModulesIso T f hf.1).hom.app K) ≫
      (Space.spacesEtaleDerivedPullbackCompIsoSpacesEtaleRingedToposHomComp g f).hom.app
        ((Space.toSpacesEtaleDerivedModules T.schemeSite S T.scheme_mem X).obj K) :=
  BigEtaleSpaceSite.smallEtaleDerivedModulePullbackCompToSpacesEtaleDerivedModulesIso_comp
    T.bigEtaleSpaceSite f g hf.1 hg.1 hgf.1 hf.2 hg.2 hgf.2 K

/-- **`ι(Lg^*K) ≅ Lg^*(ιK)` is compatible with composition, read at a factorization.** For étale,
relatively representable `g : Z ⟶ Y`, `f : Y ⟶ X` and `k = g ≫ f`, `ι` of the compositor
`Lf^* ⋙ Lg^* ≅ Lk^*` on the small étale sites, followed by `ι(Lk^*K) ≅ Lk^*(ιK)`, is
`ι(Lg^*Lf^*K) ≅ Lg^*Lf^*(ιK)` followed by the compositor on the spaces-étale sites. -/
theorem smallEtaleDerivedModulePullbackCompToSpacesEtaleDerivedModulesIso_comp_congr
    {X Y Z : T.Spaces} (g : Z ⟶ Y) (f : Y ⟶ X) (k : Z ⟶ X) (hk : g ≫ f = k)
    (hf : etaleRepresentable T f) (hg : etaleRepresentable T g) (hk' : etaleRepresentable T k)
    (K : DerivedCategory (Space.Modules.{u, u} T.schemeSite S T.scheme_mem X.1 X.2)) :
    letI := Space.spacesEtaleHasDerivedCategory T.schemeSite S T.scheme_mem X
    letI := Space.spacesEtaleHasDerivedCategory T.schemeSite S T.scheme_mem Y
    letI := Space.spacesEtaleHasDerivedCategory T.schemeSite S T.scheme_mem Z
    (Space.toSpacesEtaleDerivedModules T.schemeSite S T.scheme_mem Z).map
        ((Space.smallEtaleDerivedModulePullbackCompIso T.schemeSite S T.scheme_mem g f ≪≫
          Space.smallEtaleDerivedModulePullbackCongr T.schemeSite S T.scheme_mem hk).hom.app K) ≫
      (smallEtaleDerivedModulePullbackCompToSpacesEtaleDerivedModulesIso T k hk'.1).hom.app K =
    (smallEtaleDerivedModulePullbackCompToSpacesEtaleDerivedModulesIso T g hg.1).hom.app
        ((Space.smallEtaleDerivedModulePullback T.schemeSite S T.scheme_mem f).obj K) ≫
      (derivedPullback (X := Space.spacesEtaleRingedTopos T.schemeSite S T.scheme_mem Z)
          (Y := Space.spacesEtaleRingedTopos T.schemeSite S T.scheme_mem Y)
          (spacesEtaleRingedToposHom g)).map
        ((smallEtaleDerivedModulePullbackCompToSpacesEtaleDerivedModulesIso T f hf.1).hom.app K) ≫
      (Space.spacesEtaleDerivedPullbackCompIsoSpacesEtaleRingedToposHomComp g f ≪≫
        Stacks.Cohomology.DerivedBaseChangeOfToposHom.derivedPullbackCongr.{u + 1, u + 1, u + 1,
          u + 1, u + 1, u + 1} (X' := Space.spacesEtaleRingedTopos T.schemeSite S T.scheme_mem Z)
          (Y := Space.spacesEtaleRingedTopos T.schemeSite S T.scheme_mem X)
          (congrArg spacesEtaleRingedToposHom hk)).hom.app
        ((Space.toSpacesEtaleDerivedModules T.schemeSite S T.scheme_mem X).obj K) := by
  subst hk
  simpa only [Space.smallEtaleDerivedModulePullbackCongr,
    Stacks.Cohomology.DerivedBaseChangeOfToposHom.derivedPullbackCongr, eqToIso_refl,
    Iso.trans_refl] using
    smallEtaleDerivedModulePullbackCompToSpacesEtaleDerivedModulesIso_comp g f hf hg hk' K

/-- `ι(Lg^*K) ≅ Lg^*(ιK)` is compatible with the compositors at a factorization `ψ ≫ φ = v` of
simplex maps, for a simplicial algebraic space with étale, relatively representable structure
maps. -/
theorem smallEtaleDerivedModulePullbackCompToSpacesEtaleDerivedModulesIso_pasteIso
    (U : SimplicialObject T.Spaces) {l m n : SimplexCategory} (ψ : l ⟶ m) (φ : m ⟶ n)
    (v : l ⟶ n) (h : ψ ≫ φ = v) (hψ : etaleRepresentable T (U.map ψ.op))
    (hφ : etaleRepresentable T (U.map φ.op)) (hv : etaleRepresentable T (U.map v.op))
    (K : DerivedCategory (Space.Modules.{u, u} T.schemeSite S T.scheme_mem (U.obj (op l)).1
      (U.obj (op l)).2)) :
    letI := Space.spacesEtaleHasDerivedCategory T.schemeSite S T.scheme_mem (U.obj (op l))
    letI := Space.spacesEtaleHasDerivedCategory T.schemeSite S T.scheme_mem (U.obj (op m))
    letI := Space.spacesEtaleHasDerivedCategory T.schemeSite S T.scheme_mem (U.obj (op n))
    (Space.toSpacesEtaleDerivedModules T.schemeSite S T.scheme_mem (U.obj (op n))).map
        ((Space.smallEtaleDerivedModulePullbackCompIso T.schemeSite S T.scheme_mem (U.map φ.op)
          (U.map ψ.op) ≪≫ Space.smallEtaleDerivedModulePullbackCongr T.schemeSite S T.scheme_mem
            (map_op_comp_map_op_of_eq U ψ φ v h)).hom.app K) ≫
      (smallEtaleDerivedModulePullbackCompToSpacesEtaleDerivedModulesIso T (U.map v.op)
        hv.1).hom.app K =
    (smallEtaleDerivedModulePullbackCompToSpacesEtaleDerivedModulesIso T (U.map φ.op) hφ.1).hom.app
        ((Space.smallEtaleDerivedModulePullback T.schemeSite S T.scheme_mem (U.map ψ.op)).obj K) ≫
      (derivedPullback (X := Space.spacesEtaleRingedTopos T.schemeSite S T.scheme_mem (U.obj (op
          n)))
          (Y := Space.spacesEtaleRingedTopos T.schemeSite S T.scheme_mem (U.obj (op m)))
          (spacesEtaleRingedToposHom (U.map φ.op))).map
        ((smallEtaleDerivedModulePullbackCompToSpacesEtaleDerivedModulesIso T (U.map ψ.op)
          hψ.1).hom.app K) ≫
      (spacesEtaleDerivedPasteIso U ψ φ v h).hom.app
        ((Space.toSpacesEtaleDerivedModules T.schemeSite S T.scheme_mem (U.obj (op l))).obj K) := by
  have key := smallEtaleDerivedModulePullbackCompToSpacesEtaleDerivedModulesIso_comp_congr
    (U.map φ.op) (U.map ψ.op) (U.map v.op) (map_op_comp_map_op_of_eq U ψ φ v h) hψ hφ hv K
  exact eq_of_heq (HEq.trans (by heq_congr) (HEq.trans (heq_of_eq key) (by heq_congr)))

/-- Composites of face maps of a simplicial algebraic space with étale, relatively representable
face maps are étale and relatively representable. -/
theorem etaleRepresentable_map_op_of_comp_eq (U : SimplicialObject T.Spaces) {l m n :
    SimplexCategory}
    (ψ : l ⟶ m) (φ : m ⟶ n) (v : l ⟶ n) (h : ψ ≫ φ = v) (hψ : etaleRepresentable T (U.map ψ.op))
    (hφ : etaleRepresentable T (U.map φ.op)) : etaleRepresentable T (U.map v.op) := by
  rw [← map_op_comp_map_op_of_eq U ψ φ v h]
  exact MorphismProperty.comp_mem _ _ _ hφ hψ

/-- The compatibility `..._pasteIso`, with étaleness of the composite deduced from the factors. -/
private theorem paste_iso_of_comp_eq (U : SimplicialObject T.Spaces) {l m n : SimplexCategory}
    (ψ : l ⟶ m) (φ : m ⟶ n) (v : l ⟶ n) (h : ψ ≫ φ = v) (hψ : etaleRepresentable T (U.map ψ.op))
    (hφ : etaleRepresentable T (U.map φ.op))
    (K : DerivedCategory (Space.Modules.{u, u} T.schemeSite S T.scheme_mem (U.obj (op l)).1
      (U.obj (op l)).2)) :
    type_of% (smallEtaleDerivedModulePullbackCompToSpacesEtaleDerivedModulesIso_pasteIso U ψ φ v
      h hψ hφ (etaleRepresentable_map_op_of_comp_eq U ψ φ v h hψ hφ) K) :=
  smallEtaleDerivedModulePullbackCompToSpacesEtaleDerivedModulesIso_pasteIso U ψ φ v h hψ hφ
    (etaleRepresentable_map_op_of_comp_eq U ψ φ v h hψ hφ) K

/-- The compositors to the vertex `0` of `U_2`, read through `ι`: `Q_{11} ≫ Q_{12}⁻¹` at `ι ω`. -/
theorem spacesEtaleDerivedPasteIso_comp_inv_app_vertex_zero (U : SimplicialObject T.Spaces)
    (hU : ∀ (n : ℕ) (i : Fin (n + 2)), etaleRepresentable T (U.map (SimplexCategory.δ i).op))
    (ω : DerivedCategory (Space.Modules.{u, u} T.schemeSite S T.scheme_mem (U.obj (op ⦋0⦌)).1
      (U.obj (op ⦋0⦌)).2)) :
    type_of% (CategoryTheory.comp_inv_app_eq_of_comparison
      (smallEtaleDerivedModulePullbackCompToSpacesEtaleDerivedModulesIso_pasteIso U
        (SimplexCategory.δ (1 : Fin 2)) (SimplexCategory.δ (1 : Fin 3)) _
            SimplexCategory.delta_one_comp_delta_one
        (hU 0 1) (hU 1 1) (etaleRepresentable_map_op_of_comp_eq U _ _ _
            SimplexCategory.delta_one_comp_delta_one
          (hU 0 1) (hU 1 1)) ω)
      (smallEtaleDerivedModulePullbackCompToSpacesEtaleDerivedModulesIso_pasteIso U
        (SimplexCategory.δ (1 : Fin 2)) (SimplexCategory.δ (2 : Fin 3)) _
            SimplexCategory.delta_one_comp_delta_two
        (hU 0 1) (hU 1 2) (etaleRepresentable_map_op_of_comp_eq U _ _ _
            SimplexCategory.delta_one_comp_delta_two
          (hU 0 1) (hU 1 2)) ω)) :=
  CategoryTheory.comp_inv_app_eq_of_comparison
      (paste_iso_of_comp_eq U _ _ _
        SimplexCategory.delta_one_comp_delta_one (hU 0 1) (hU 1 1) ω)
      (paste_iso_of_comp_eq U _ _ _
        SimplexCategory.delta_one_comp_delta_two (hU 0 1) (hU 1 2) ω)

/-- The compositors to the vertex `1` of `U_2`, read through `ι`: `Q_{02} ≫ Q_{10}⁻¹` at `ι ω`. -/
theorem spacesEtaleDerivedPasteIso_comp_inv_app_vertex_one (U : SimplicialObject T.Spaces)
    (hU : ∀ (n : ℕ) (i : Fin (n + 2)), etaleRepresentable T (U.map (SimplexCategory.δ i).op))
    (ω : DerivedCategory (Space.Modules.{u, u} T.schemeSite S T.scheme_mem (U.obj (op ⦋0⦌)).1
      (U.obj (op ⦋0⦌)).2)) :
    type_of% (CategoryTheory.comp_inv_app_eq_of_comparison
      (smallEtaleDerivedModulePullbackCompToSpacesEtaleDerivedModulesIso_pasteIso U
        (SimplexCategory.δ (0 : Fin 2)) (SimplexCategory.δ (2 : Fin 3)) _
            SimplexCategory.delta_zero_comp_delta_two
        (hU 0 0) (hU 1 2) (etaleRepresentable_map_op_of_comp_eq U _ _ _
            SimplexCategory.delta_zero_comp_delta_two
          (hU 0 0) (hU 1 2)) ω)
      (smallEtaleDerivedModulePullbackCompToSpacesEtaleDerivedModulesIso_pasteIso U
        (SimplexCategory.δ (1 : Fin 2)) (SimplexCategory.δ (0 : Fin 3)) _
            SimplexCategory.delta_one_comp_delta_zero
        (hU 0 1) (hU 1 0) (etaleRepresentable_map_op_of_comp_eq U _ _ _
            SimplexCategory.delta_one_comp_delta_zero
          (hU 0 1) (hU 1 0)) ω)) :=
  CategoryTheory.comp_inv_app_eq_of_comparison
      (paste_iso_of_comp_eq U _ _ _
        SimplexCategory.delta_zero_comp_delta_two (hU 0 0) (hU 1 2) ω)
      (paste_iso_of_comp_eq U _ _ _
        SimplexCategory.delta_one_comp_delta_zero (hU 0 1) (hU 1 0) ω)

/-- The compositors to the vertex `2` of `U_2`, read through `ι`: `Q_{00} ≫ Q_{01}⁻¹` at `ι ω`. -/
theorem spacesEtaleDerivedPasteIso_comp_inv_app_vertex_two (U : SimplicialObject T.Spaces)
    (hU : ∀ (n : ℕ) (i : Fin (n + 2)), etaleRepresentable T (U.map (SimplexCategory.δ i).op))
    (ω : DerivedCategory (Space.Modules.{u, u} T.schemeSite S T.scheme_mem (U.obj (op ⦋0⦌)).1
      (U.obj (op ⦋0⦌)).2)) :
    type_of% (CategoryTheory.comp_inv_app_eq_of_comparison
      (smallEtaleDerivedModulePullbackCompToSpacesEtaleDerivedModulesIso_pasteIso U
        (SimplexCategory.δ (0 : Fin 2)) (SimplexCategory.δ (0 : Fin 3)) _
            SimplexCategory.delta_zero_comp_delta_zero
        (hU 0 0) (hU 1 0) (etaleRepresentable_map_op_of_comp_eq U _ _ _
            SimplexCategory.delta_zero_comp_delta_zero
          (hU 0 0) (hU 1 0)) ω)
      (smallEtaleDerivedModulePullbackCompToSpacesEtaleDerivedModulesIso_pasteIso U
        (SimplexCategory.δ (0 : Fin 2)) (SimplexCategory.δ (1 : Fin 3)) _
            SimplexCategory.delta_zero_comp_delta_one
        (hU 0 0) (hU 1 1) (etaleRepresentable_map_op_of_comp_eq U _ _ _
            SimplexCategory.delta_zero_comp_delta_one
          (hU 0 0) (hU 1 1)) ω)) :=
  CategoryTheory.comp_inv_app_eq_of_comparison
      (paste_iso_of_comp_eq U _ _ _
        SimplexCategory.delta_zero_comp_delta_zero (hU 0 0) (hU 1 0) ω)
      (paste_iso_of_comp_eq U _ _ _
        SimplexCategory.delta_zero_comp_delta_one (hU 0 0) (hU 1 1) ω)

/-- **A cocycle on the small étale sites gives a cocycle on the spaces-étale sites.** Let `U` be
a simplicial algebraic space whose face maps are étale and relatively representable,
`ω ∈ D(𝒪_{U_0})` and `α : L U(δ¹₁)^* ω ≅ L U(δ¹₀)^* ω` with the cocycle condition on `U_2`. Then
`ι ω` and `N_{δ¹₁}⁻¹ ≫ ι α ≫ N_{δ¹₀}`, `N_g : ι(Lg^*K) ≅ Lg^*(ιK)`, satisfy the cocycle condition
on the spaces-étale sites. -/
theorem spacesEtaleDerivedCocycle_toSpacesEtaleDerivedModules (U : SimplicialObject T.Spaces)
    (hU : ∀ (n : ℕ) (i : Fin (n + 2)), etaleRepresentable T (U.map (SimplexCategory.δ i).op))
    (ω : DerivedCategory (Space.Modules.{u, u} T.schemeSite S T.scheme_mem (U.obj (op ⦋0⦌)).1
      (U.obj (op ⦋0⦌)).2))
    (α : (Space.smallEtaleDerivedModulePullback T.schemeSite S T.scheme_mem
          (U.map (SimplexCategory.δ (1 : Fin 2)).op)).obj ω ≅
        (Space.smallEtaleDerivedModulePullback T.schemeSite S T.scheme_mem
          (U.map (SimplexCategory.δ (0 : Fin 2)).op)).obj ω)
    (hα : (Space.smallEtaleDerivedModulePullback T.schemeSite S T.scheme_mem
          (U.map (Quiver.Hom.op (X := ⦋0 + 1⦌) (SimplexCategory.δ (1 : Fin 3))))).map α.hom =
      (Space.smallEtaleDerivedModulePullbackCompIso T.schemeSite S T.scheme_mem
          (U.map (Quiver.Hom.op (X := ⦋0 + 1⦌) (SimplexCategory.δ (1 : Fin 3)))) (U.map
              (SimplexCategory.δ (1 : Fin 2)).op) ≪≫
        Space.smallEtaleDerivedModulePullbackCongr T.schemeSite S T.scheme_mem
          (map_op_comp_map_op_of_eq U (SimplexCategory.δ (1 : Fin 2))
            (SimplexCategory.δ (1 : Fin 3)) _ SimplexCategory.delta_one_comp_delta_one)).hom.app ω ≫
      (Space.smallEtaleDerivedModulePullbackCompIso T.schemeSite S T.scheme_mem
          (U.map (Quiver.Hom.op (X := ⦋0 + 1⦌) (SimplexCategory.δ (2 : Fin 3)))) (U.map
              (SimplexCategory.δ (1 : Fin 2)).op) ≪≫
        Space.smallEtaleDerivedModulePullbackCongr T.schemeSite S T.scheme_mem
          (map_op_comp_map_op_of_eq U (SimplexCategory.δ (1 : Fin 2))
            (SimplexCategory.δ (2 : Fin 3)) _ SimplexCategory.delta_one_comp_delta_two)).inv.app ω ≫
      (Space.smallEtaleDerivedModulePullback T.schemeSite S T.scheme_mem
          (U.map (Quiver.Hom.op (X := ⦋0 + 1⦌) (SimplexCategory.δ (2 : Fin 3))))).map α.hom ≫
      (Space.smallEtaleDerivedModulePullbackCompIso T.schemeSite S T.scheme_mem
          (U.map (Quiver.Hom.op (X := ⦋0 + 1⦌) (SimplexCategory.δ (2 : Fin 3)))) (U.map
              (SimplexCategory.δ (0 : Fin 2)).op) ≪≫
        Space.smallEtaleDerivedModulePullbackCongr T.schemeSite S T.scheme_mem
          (map_op_comp_map_op_of_eq U (SimplexCategory.δ (0 : Fin 2))
            (SimplexCategory.δ (2 : Fin 3)) _ SimplexCategory.delta_zero_comp_delta_two)).hom.app ω
                ≫
      (Space.smallEtaleDerivedModulePullbackCompIso T.schemeSite S T.scheme_mem
          (U.map (Quiver.Hom.op (X := ⦋0 + 1⦌) (SimplexCategory.δ (0 : Fin 3)))) (U.map
              (SimplexCategory.δ (1 : Fin 2)).op) ≪≫
        Space.smallEtaleDerivedModulePullbackCongr T.schemeSite S T.scheme_mem
          (map_op_comp_map_op_of_eq U (SimplexCategory.δ (1 : Fin 2))
            (SimplexCategory.δ (0 : Fin 3)) _ SimplexCategory.delta_one_comp_delta_zero)).inv.app ω
                ≫
      (Space.smallEtaleDerivedModulePullback T.schemeSite S T.scheme_mem
          (U.map (Quiver.Hom.op (X := ⦋0 + 1⦌) (SimplexCategory.δ (0 : Fin 3))))).map α.hom ≫
      (Space.smallEtaleDerivedModulePullbackCompIso T.schemeSite S T.scheme_mem
          (U.map (Quiver.Hom.op (X := ⦋0 + 1⦌) (SimplexCategory.δ (0 : Fin 3)))) (U.map
              (SimplexCategory.δ (0 : Fin 2)).op) ≪≫
        Space.smallEtaleDerivedModulePullbackCongr T.schemeSite S T.scheme_mem
          (map_op_comp_map_op_of_eq U (SimplexCategory.δ (0 : Fin 2))
            (SimplexCategory.δ (0 : Fin 3)) _ SimplexCategory.delta_zero_comp_delta_zero)).hom.app
                ω ≫
      (Space.smallEtaleDerivedModulePullbackCompIso T.schemeSite S T.scheme_mem
          (U.map (Quiver.Hom.op (X := ⦋0 + 1⦌) (SimplexCategory.δ (1 : Fin 3)))) (U.map
              (SimplexCategory.δ (0 : Fin 2)).op) ≪≫
        Space.smallEtaleDerivedModulePullbackCongr T.schemeSite S T.scheme_mem
          (map_op_comp_map_op_of_eq U (SimplexCategory.δ (0 : Fin 2))
            (SimplexCategory.δ (1 : Fin 3)) _ SimplexCategory.delta_zero_comp_delta_one)).inv.app
                ω) :
    SpacesEtaleDerivedCocycle U
      ((Space.toSpacesEtaleDerivedModules T.schemeSite S T.scheme_mem _).obj ω)
      (((smallEtaleDerivedModulePullbackCompToSpacesEtaleDerivedModulesIso T _ (hU 0 1).1).app
          ω).symm ≪≫
        (Space.toSpacesEtaleDerivedModules T.schemeSite S T.scheme_mem _).mapIso α ≪≫
        (smallEtaleDerivedModulePullbackCompToSpacesEtaleDerivedModulesIso T _ (hU 0 0).1).app
          ω) := by
  refine ⟨?_⟩
  have key := CategoryTheory.cocycle_of_comparison
    (spacesEtaleDerivedPasteIso_comp_inv_app_vertex_zero U hU ω)
    (spacesEtaleDerivedPasteIso_comp_inv_app_vertex_one U hU ω)
    (spacesEtaleDerivedPasteIso_comp_inv_app_vertex_two U hU ω) α
    (eq_of_heq (HEq.trans (by heq_congr) (HEq.trans (heq_of_eq hα) (by heq_congr))))
    (((smallEtaleDerivedModulePullbackCompToSpacesEtaleDerivedModulesIso T _ (hU 0 1).1).app
          ω).symm ≪≫
        (Space.toSpacesEtaleDerivedModules T.schemeSite S T.scheme_mem _).mapIso α ≪≫
        (smallEtaleDerivedModulePullbackCompToSpacesEtaleDerivedModulesIso T _ (hU 0 0).1).app
          ω) rfl
  exact eq_of_heq (HEq.trans (by heq_congr) (HEq.trans (heq_of_eq key) (by heq_congr)))

/-- **The descent datum of Stacks 0E61 on the spaces-étale sites.** Let `D₀` be a relative
dualizing complex on `f_0 : U_0 ⟶ V_0`, for the Čech nerve `V` of an étale, relatively
representable `b₀ : V₀ ⟶ Y` and `U_n = V_n ×_Y X`. There is an isomorphism `α` of pairs between
the two base changes of `D₀` to `U_1` (Stacks 0E5Z), and `ι ω_0` with
`N_{δ¹₁}⁻¹ ≫ ι α ≫ N_{δ¹₀}` satisfies the cocycle condition on the spaces-étale sites of the
simplicial algebraic space `U`. -/
theorem exists_spacesEtaleDerivedCocycle_cechOverPullback
    (hZ : T.schemeSite.Contains (⊤_ Scheme.{u})) {V₀ Y X : T.Spaces} (b₀ : V₀ ⟶ Y) (f : X ⟶ Y)
    (hb₀ : etaleRepresentable T b₀)
    (hf : Space.IsProper T.schemeSite S T.scheme_mem f.hom)
    (hfl : Space.IsFlat T.schemeSite S T.scheme_mem f.hom)
    (hfp : Space.IsFinitePresentation T.schemeSite S T.scheme_mem f.hom)
    (D₀ : Space.RelativeDualizingComplex hZ (cechOverPullbackFst b₀ f (op ⦋0⦌))
      (isProper_cechOverPullbackFst b₀ f hf _) (isFlat_cechOverPullbackFst b₀ f hfl _)
      (isFinitePresentation_cechOverPullbackFst b₀ f hfp _)) :
    ∃ α : (Space.smallEtaleDerivedModulePullback T.schemeSite S T.scheme_mem
          ((cechOverPullback b₀ f).map (SimplexCategory.δ (1 : Fin 2)).op).left).obj D₀.ω ≅
        (Space.smallEtaleDerivedModulePullback T.schemeSite S T.scheme_mem
          ((cechOverPullback b₀ f).map (SimplexCategory.δ (0 : Fin 2)).op).left).obj D₀.ω,
      (Space.derivedModulePushforward T.schemeSite S T.scheme_mem
          (cechOverPullbackFst b₀ f (op ⦋1⦌))).map α.hom ≫
        (D₀.baseChange (isPullback_cechOverPullback_map b₀ f
          (SimplexCategory.δ (0 : Fin 2)).op)).τ =
        (D₀.baseChange (isPullback_cechOverPullback_map b₀ f
          (SimplexCategory.δ (1 : Fin 2)).op)).τ ∧
      SpacesEtaleDerivedCocycle (cechOverPullback b₀ f ⋙ Over.forget X)
        ((Space.toSpacesEtaleDerivedModules T.schemeSite S T.scheme_mem
          ((cechOverPullback b₀ f ⋙ Over.forget X).obj (op ⦋0⦌))).obj D₀.ω)
        (((smallEtaleDerivedModulePullbackCompToSpacesEtaleDerivedModulesIso T _
            (etaleRepresentable_cechOverPullback_delta b₀ f hb₀ 0 1).1).app D₀.ω).symm ≪≫
          (Space.toSpacesEtaleDerivedModules T.schemeSite S T.scheme_mem
            ((cechOverPullback b₀ f ⋙ Over.forget X).obj (op ⦋1⦌))).mapIso α ≪≫
          (smallEtaleDerivedModulePullbackCompToSpacesEtaleDerivedModulesIso T _
            (etaleRepresentable_cechOverPullback_delta b₀ f hb₀ 0 0).1).app D₀.ω) := by
  have h3 := exists_iso_cocycle_cechOverPullback b₀ f hZ hf hfl hfp D₀
  exact ⟨h3.choose, h3.choose_spec.1, spacesEtaleDerivedCocycle_toSpacesEtaleDerivedModules
    (cechOverPullback b₀ f ⋙ Over.forget X) (etaleRepresentable_cechOverPullback_delta b₀ f hb₀)
    D₀.ω h3.choose (eq_of_heq (HEq.trans (by heq_congr) (HEq.trans (heq_of_eq h3.choose_spec.2)
      (by heq_congr))))⟩

/-- **The negative self-extensions of the descent datum of Stacks 0E61 vanish**: for the
pullbacks `K_n = L(f_{τⁿₙ})^*(ι ω_0)` of `ι ω_0` to the terms of `U` (the input of Stacks 0DLA),
`Hom(K_n, K_n[i]) = 0` for `i < 0`. Indeed `K_n ≅ ι(L(f_{τⁿₙ})^* ω_0)`, `ι` is bijective on
morphisms into `D_QCoh` and commutes with shifts, and `L(f_{τⁿₙ})^* ω_0` is a relative
dualizing complex (Stacks 0E6C), which has no negative self-extensions (Stacks 0E5Y). -/
theorem hom_shift_eq_zero_cechOverPullback
    (hZ : T.schemeSite.Contains (⊤_ Scheme.{u})) {V₀ Y X : T.Spaces} (b₀ : V₀ ⟶ Y) (f : X ⟶ Y)
    (hb₀ : etaleRepresentable T b₀)
    (hf : Space.IsProper T.schemeSite S T.scheme_mem f.hom)
    (hfl : Space.IsFlat T.schemeSite S T.scheme_mem f.hom)
    (hfp : Space.IsFinitePresentation T.schemeSite S T.scheme_mem f.hom)
    (D₀ : Space.RelativeDualizingComplex hZ (cechOverPullbackFst b₀ f (op ⦋0⦌))
      (isProper_cechOverPullbackFst b₀ f hf _) (isFlat_cechOverPullbackFst b₀ f hfl _)
      (isFinitePresentation_cechOverPullbackFst b₀ f hfp _)) (n : ℕ) (i : ℤ) (hi : i < 0)
    (g : (derivedPullback (spacesEtaleRingedToposHom ((cechOverPullback b₀ f ⋙ Over.forget X).map
          (SimplexCategory.const ⦋0⦌ ⦋n⦌ (Fin.last n)).op))).obj
          ((Space.toSpacesEtaleDerivedModules T.schemeSite S T.scheme_mem
            ((cechOverPullback b₀ f ⋙ Over.forget X).obj (op ⦋0⦌))).obj D₀.ω) ⟶
        (shiftFunctor (@DerivedCategory (SheafOfModules.{u + 1}
          (Stacks.SheafOfModules.Tensor.ringSheaf (Space.spacesEtaleRingedTopos T.schemeSite S
            T.scheme_mem ((cechOverPullback b₀ f ⋙ Over.forget X).obj (op ⦋n⦌))).O)) _ _
          (HasDerivedCategory.standard _)) i).obj
          ((derivedPullback (spacesEtaleRingedToposHom ((cechOverPullback b₀ f ⋙
            Over.forget X).map (SimplexCategory.const ⦋0⦌ ⦋n⦌ (Fin.last n)).op))).obj
            ((Space.toSpacesEtaleDerivedModules T.schemeSite S T.scheme_mem
              ((cechOverPullback b₀ f ⋙ Over.forget X).obj (op ⦋0⦌))).obj D₀.ω))) :
    g = 0 := by
  let := Space.spacesEtaleHasDerivedCategory T.schemeSite S T.scheme_mem
    ((cechOverPullback b₀ f ⋙ Over.forget X).obj (op ⦋n⦌))
  have hτ := etaleRepresentable_cechOverPullback_const_last b₀ f hb₀ n
  let D := D₀.baseChange (isPullback_cechOverPullback_map b₀ f
    (SimplexCategory.const ⦋0⦌ ⦋n⦌ (Fin.last n)).op)
  let A : DerivedCategory (Space.Modules.{u, u} T.schemeSite S T.scheme_mem
      ((cechOverPullback b₀ f ⋙ Over.forget X).obj (op ⦋n⦌)).1
      ((cechOverPullback b₀ f ⋙ Over.forget X).obj (op ⦋n⦌)).2) :=
    (Space.smallEtaleDerivedModulePullback T.schemeSite S T.scheme_mem
      ((cechOverPullback b₀ f ⋙ Over.forget X).map
        (SimplexCategory.const ⦋0⦌ ⦋n⦌ (Fin.last n)).op)).obj D₀.ω
  exact Functor.eq_zero_of_hom_shift_eq_zero_of_surjective
    (Space.toSpacesEtaleDerivedModules T.schemeSite S T.scheme_mem
      ((cechOverPullback b₀ f ⋙ Over.forget X).obj (op ⦋n⦌)))
    ((smallEtaleDerivedModulePullbackCompToSpacesEtaleDerivedModulesIso T _ hτ.1).app D₀.ω)
    ((smallEtaleDerivedModulePullbackCompToSpacesEtaleDerivedModulesIso T _ hτ.1).app D₀.ω) i
    (Space.bijective_toSpacesEtaleDerivedModules_map T.schemeSite S T.scheme_mem _ A (A⟦i⟧)
      (Space.qcohDerived_shift A i D.toRelativeDualizingPair.qcohDerived_ω)).2
    (D.hom_shift_eq_zero i hi) g

end AlgebraicGeometry.BigFppfSpaceSite

end
