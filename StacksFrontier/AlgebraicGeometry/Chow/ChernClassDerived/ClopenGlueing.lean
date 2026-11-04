module

public import Mathlib.Algebra.Homology.DerivedCategory.Fractions
public import StacksFrontier.Algebra.Homology.DerivedCategory.KInjective
public import StacksFrontier.AlgebraicGeometry.AffineBaseChange.Basic
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.LocalizedChernData
public import StacksFrontier.AlgebraicGeometry.Chow.ClopenDecomposition.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteLocallyFree.Local
public import StacksFrontier.AlgebraicGeometry.Perfect.PseudoCoherentComplex.RestrictHomology
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.OpenImmersionRestriction
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.FiniteFreeRepresentation

/-!
# Glueing locally bounded complexes of finite locally free modules along a clopen decomposition

Let `Y` be a scheme with a decomposition `Y = ∐ᵢ Uᵢ` into open and closed subschemes, and let `K`
be an object of `D(𝒪_Y)`. If on every piece the restriction `K|_{Uᵢ}` is represented by a
bounded complex `Pᵢ` of finite locally free `𝒪_{Uᵢ}`-modules, then `K` itself is represented by
a locally bounded complex of finite locally free `𝒪_Y`-modules. This is the glueing step, left
to the reader in the source ("small detail omitted"), of the proof of clause (3) of
[Stacks, Tag 0GUE]: there the envelope is a disjoint union `∐ X'ᵢ` of schemes over each of
which the derived pullback of a perfect object is a bounded complex.

## Main results

* `Stacks.Chow.ClopenGlueing.quasiIso_of_forall_quasiIso_moduleRestriction`: a morphism of
  complexes of `𝒪_Y`-modules is a quasi-isomorphism as soon as its restrictions to the members
  of an open covering are.
* `Stacks.Chow.ClopenGlueing.quasiIso_piMap_pushforward`,
  `Stacks.Chow.ClopenGlueing.quasiIso_piLift_unit`: the product of pushforwards preserves
  quasi-isomorphisms, and a complex is quasi-isomorphic to the product of the pushforwards of its
  restrictions.
* `Stacks.Chow.ClopenGlueing.nonempty_iso_Q_pi_pushforward`: `K` is isomorphic in `D(𝒪_Y)` to
  the product `∏ᵢ jᵢ_* Pᵢ` of the pushforwards of the complexes on the pieces.
* `Stacks.Chow.ClopenGlueing.isLocallyBoundedFiniteLocallyFree_pi_pushforward`: that product is
  a locally bounded complex of finite locally free modules.
* `Stacks.Chow.ClopenGlueing.exists_isLocallyBoundedFiniteLocallyFree_iso`: hence `K` is
  represented by such a complex.

## Implementation notes

An isomorphism `K|_{Uᵢ} ≅ Pᵢ` in the derived category is a roof `K'|_{Uᵢ} ⟶ Cᵢ ⟵ Pᵢ` of
quasi-isomorphisms of complexes (`DerivedCategory.left_fac`), where `K'` is any complex
representing `K`. The roofs are glued by taking products of pushforwards: the adjunction
`(-)|_{Uᵢ} ⊣ jᵢ_*` gives `K' ⟶ ∏ᵢ jᵢ_* Cᵢ`, and functoriality gives
`∏ᵢ jᵢ_* Pᵢ ⟶ ∏ᵢ jᵢ_* Cᵢ`. Both are quasi-isomorphisms because quasi-isomorphisms are detected
on an open covering and because the restriction of `∏ᵢ jᵢ_* Mᵢ` to `U_m` is `M_m`: restriction
preserves products, `j_m_*` is fully faithful, and `(jᵢ_* Mᵢ)|_{U_m} = 0` for `i ≠ m` since the
pieces are disjoint.

The complexes on the pieces are written over the ringed space `restrictToOpen Y U`, which is the
open subscheme `U` definitionally, and pushforward is taken along
`Stacks.Cohomology.HigherDirectImage.openSubspaceInclusion`, so that the restriction functor
`Stacks.Cohomology.HigherDirectImage.moduleRestriction` and the pushforward have matching
categories on the nose; the adjunction between them is
`Stacks.Cohomology.RelativeMayerVietoris.moduleRestrictionAdjunction`.

## References

* [Stacks Project, Tag 0GUE](https://stacks.math.columbia.edu/tag/0GUE)
* [Stacks Project, Tag 05QI](https://stacks.math.columbia.edu/tag/05QI)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.Cohomology.HigherDirectImage RingedSpaceModuleAdjunction
open Stacks.Cohomology.RelativeMayerVietoris (moduleRestrictionAdjunction)

universe u

namespace Stacks.Chow.ClopenGlueing

/-! ### Quasi-isomorphisms detected by a family of exact functors -/

/-- A morphism of cochain complexes is a quasi-isomorphism as soon as its images under a family of
exact functors which jointly reflect isomorphisms are quasi-isomorphisms: the image of each
homology map is the homology map of the image. -/
theorem quasiIso_of_forall_quasiIso_map {A : Type*} [Category A] [Abelian A] {I : Type*}
    {B : I → Type*} [∀ k, Category (B k)] [∀ k, Abelian (B k)] (F : ∀ k, A ⥤ B k)
    [∀ k, (F k).Additive] [∀ k, (F k).PreservesHomology]
    (hF : ∀ {M N : A} (f : M ⟶ N), (∀ k, IsIso ((F k).map f)) → IsIso f)
    {K L : CochainComplex A ℤ} (φ : K ⟶ L)
    (h : ∀ k, QuasiIso (((F k).mapHomologicalComplex (ComplexShape.up ℤ)).map φ)) :
    QuasiIso φ := by
  rw [quasiIso_iff]
  intro i
  rw [quasiIsoAt_iff]
  let S := HomologicalComplex.shortComplexFunctor A (ComplexShape.up ℤ) i
  let γ : ShortComplex.LeftHomologyMapData (S.map φ) (S.obj K).leftHomologyData
      (S.obj L).leftHomologyData := default
  rw [γ.quasiIso_iff]
  refine hF γ.φH fun k => ?_
  have hk := (h k).quasiIsoAt i
  rw [quasiIsoAt_iff] at hk
  have hk' : ShortComplex.QuasiIso ((F k).mapShortComplex.map (S.map φ)) := hk
  rwa [(γ.map (F k)).quasiIso_iff, ShortComplex.LeftHomologyMapData.map_φH] at hk'

/-- In a product whose factors other than the `m`-th are zero, the projection onto the `m`-th
factor is an isomorphism. -/
theorem isIso_π_of_isZero {C : Type*} [Category C] [HasZeroMorphisms C] {ι : Type*}
    (F : ι → C) [HasProduct F] (m : ι) (h : ∀ k, k ≠ m → IsZero (F k)) :
    IsIso (Pi.π F m) := by
  classical
  refine ⟨Pi.lift fun k => if hk : k = m then eqToHom (by rw [hk]) else 0, ?_, by simp⟩
  ext k
  by_cases hk : k = m
  · subst hk
    simp
  · exact (h k hk).eq_of_tgt _ _

/-! ### Restriction to an open and pushforward from it -/

variable {Y : Scheme.{u}}

local notation "ρ[" U "]" => moduleRestriction Y.toRingedSpace U
local notation "ψ[" U "]" => modulePushforward (openSubspaceInclusion Y.toRingedSpace U)

/-- Pushforward along the inclusion of an open subspace is additive. This is
`RingedSpaceModuleAdjunction.modulePushforward_additive`, recorded at the inclusion
`openSubspaceInclusion Y U`: instance search does not find the general instance there, because
the inclusion is a morphism of sheafed spaces typed as one of ringed spaces. -/
instance additive_modulePushforward_openSubspaceInclusion (V : Y.Opens) : (ψ[V]).Additive :=
  modulePushforward_additive _

/-- The restriction to `U` of the pushforward of a module from an open `V` disjoint from `U` is
zero: its sections over an open of `U` are the sections of the module over an open of `V` with
no points. -/
theorem isZero_restriction_pushforward_of_disjoint {U V : Y.Opens} (h : Disjoint U V)
    (M : (V : Scheme.{u}).Modules) :
    IsZero ((moduleRestriction Y.toRingedSpace U).obj
      ((ψ[V]).obj M)) := by
  refine (IsZero.iff_id_eq_zero _).2 ?_
  ext W s
  show s = 0
  refine (show TopCat.Presheaf.IsSheaf M.val.presheaf from M.isSheaf).section_ext
    (s := s) (t := 0) ?_
  intro x hx
  exfalso
  obtain ⟨w, -, hwx⟩ := hx
  have hxU : x.1 ∈ U := by
    have hw : w.1 = x.1 := hwx
    rw [← hw]
    exact w.2
  exact (Set.disjoint_left.mp (Opens.coe_disjoint.mpr h)) hxU x.2

/-- The counit of the adjunction between restriction to an open and pushforward from it is an
isomorphism: restricting the pushforward recovers the module. -/
instance isIso_moduleRestrictionAdjunction_counit (U : Y.Opens) :
    IsIso (moduleRestrictionAdjunction Y.toRingedSpace U).counit :=
  (moduleRestrictionAdjunction Y.toRingedSpace U).isIso_counit_of_iso
    (ExtensionByZeroModules.jStarPushIso U (structureSheafRing Y.toRingedSpace))

/-- Invertibility of a morphism of `𝒪_Y`-modules can be tested on the members of an open
covering. -/
theorem isIso_of_forall_isIso_moduleRestriction {I : Type u} (U : I → Y.Opens)
    (hU : iSup U = ⊤) {M N : Y.Modules} (f : M ⟶ N)
    (h : ∀ k, IsIso ((ρ[U k]).map f)) : IsIso f :=
  Stacks.AlgebraicGeometry.AffineBaseChange.isIso_of_isIso_restrict f U hU fun k =>
    (NatIso.isIso_map_iff
      (Stacks.AlgebraicGeometry.PerfectCohomology.restrictModulesIsoRestrict Y (U k)) f).mp (h k)

/-- Restriction to an open is exact: it is a right adjoint, and a left adjoint of the
pushforward. -/
instance preservesHomology_moduleRestriction (U : Y.Opens) : (ρ[U]).PreservesHomology := by
  have : PreservesColimitsOfSize.{u, u} (ρ[U]) :=
    (moduleRestrictionAdjunction Y.toRingedSpace U).leftAdjoint_preservesColimits
  have : PreservesFiniteColimits (ρ[U]) := inferInstance
  have : PreservesFiniteLimits (ρ[U]) := inferInstance
  infer_instance

/-- **Quasi-isomorphisms are local.** A morphism of complexes of `𝒪_Y`-modules whose
restrictions to the members of an open covering are quasi-isomorphisms is a
quasi-isomorphism. -/
theorem quasiIso_of_forall_quasiIso_moduleRestriction {I : Type u} (U : I → Y.Opens)
    (hU : iSup U = ⊤)
    {A B : CochainComplex (SheafOfModules.{u} (structureSheafRing Y.toRingedSpace)) ℤ} (φ : A ⟶ B)
    (h : ∀ k, QuasiIso (((ρ[U k]).mapHomologicalComplex (ComplexShape.up ℤ)).map φ)) :
    QuasiIso φ :=
  quasiIso_of_forall_quasiIso_map (fun k => ρ[U k])
    (fun f hf => isIso_of_forall_isIso_moduleRestriction U hU f hf) φ h

/-! ### Glueing along a clopen decomposition -/

attribute [local instance 10000] HasDerivedCategory.standard

variable {I : Type u} (U : I → Y.Opens)

/-- On a clopen decomposition, restricting a product of pushforwards from the pieces to the
`m`-th piece, the projection onto the `m`-th factor becomes an isomorphism: the other factors
restrict to zero. -/
theorem isIso_map_π_pushforward (hU : IsClopenDecomposition U)
    (C : ∀ k, CochainComplex (SheafOfModules.{u}
      (structureSheafRing (restrictToOpen Y.toRingedSpace (U k)))) ℤ) (m : I) :
    IsIso (((ρ[U m]).mapHomologicalComplex (ComplexShape.up ℤ)).map
      (Pi.π (fun k => ((ψ[U k]).mapHomologicalComplex (ComplexShape.up ℤ)).obj (C k)) m)) := by
  let G := (ρ[U m]).mapHomologicalComplex (ComplexShape.up ℤ)
  let f := fun k => ((ψ[U k]).mapHomologicalComplex (ComplexShape.up ℤ)).obj (C k)
  have : PreservesLimitsOfShape (Discrete I) G := by
    apply HomologicalComplex.preservesLimitsOfShape_of_eval
    intro i
    let e : G ⋙ HomologicalComplex.eval _ (ComplexShape.up ℤ) i ≅
        HomologicalComplex.eval _ (ComplexShape.up ℤ) i ⋙ ρ[U m] :=
      NatIso.ofComponents (fun _ => Iso.refl _) (by intros; simp [G])
    exact preservesLimitsOfShape_of_natIso e.symm
  rw [← piComparison_comp_π G f m]
  have : IsIso (Pi.π (fun k => G.obj (f k)) m) := by
    refine isIso_π_of_isZero _ m fun k hk => ?_
    refine (IsZero.iff_id_eq_zero _).2 (HomologicalComplex.hom_ext _ _ fun n => ?_)
    exact (isZero_restriction_pushforward_of_disjoint (hU.disjoint m k (Ne.symm hk))
      ((C k).X n)).eq_of_src _ _
  infer_instance
/-- The adjunction `ρ ⊣ ψ` degreewise on cochain complexes. -/
abbrev restrictionAdjunctionComplex (V : Y.Opens) :
    (ρ[V]).mapHomologicalComplex (ComplexShape.up ℤ) ⊣
      (ψ[V]).mapHomologicalComplex (ComplexShape.up ℤ) :=
  (show ρ[V] ⊣ ψ[V] from moduleRestrictionAdjunction Y.toRingedSpace V).mapHomologicalComplex
    (ComplexShape.up ℤ)

/-- The counit of the degreewise adjunction is an isomorphism, degree by degree. -/
instance isIso_restrictionAdjunctionComplex_counit (V : Y.Opens) :
    IsIso (restrictionAdjunctionComplex V).counit := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro M
  have : ∀ n, IsIso (((restrictionAdjunctionComplex V).counit.app M).f n) := fun n => by
    exact NatIso.isIso_app_of_isIso (moduleRestrictionAdjunction Y.toRingedSpace V).counit (M.X n)
  exact HomologicalComplex.Hom.isIso_of_components _
local notation "ρC[" V "]" => Functor.mapHomologicalComplex (ρ[V]) (ComplexShape.up ℤ)
local notation "ψC[" V "]" => Functor.mapHomologicalComplex (ψ[V]) (ComplexShape.up ℤ)
local notation "adj[" V "]" => restrictionAdjunctionComplex V

/-- The comparison of the restriction of `∏ᵢ jᵢ_* Mᵢ` to `U_m` with `M_m`: the restricted
projection followed by the counit is an isomorphism. -/
theorem isIso_map_π_comp_counit (hU : IsClopenDecomposition U)
    (M : ∀ k, CochainComplex (SheafOfModules.{u}
      (structureSheafRing (restrictToOpen Y.toRingedSpace (U k)))) ℤ) (m : I) :
    IsIso ((ρC[U m]).map (Pi.π (fun k => (ψC[U k]).obj (M k)) m) ≫
      (adj[U m]).counit.app (M m)) := by
  have := isIso_map_π_pushforward U hU M m
  have : IsIso ((adj[U m]).counit.app (M m)) :=
    NatIso.isIso_app_of_isIso (restrictionAdjunctionComplex (U m)).counit (M m)
  infer_instance

/-- A map `f` into a product of pushforwards is a quasi-isomorphism after restriction to the `m`-th
piece as soon as its `m`-th component, followed by the counit, is. -/
private theorem quasiIso_map_of_quasiIso_map_comp_π_counit (hU : IsClopenDecomposition U)
    {N : ∀ k, CochainComplex (SheafOfModules.{u}
      (structureSheafRing (restrictToOpen Y.toRingedSpace (U k)))) ℤ}
    {A : CochainComplex (SheafOfModules.{u} (structureSheafRing Y.toRingedSpace)) ℤ}
    (f : A ⟶ ∏ᶜ fun k => (ψC[U k]).obj (N k)) (m : I)
    (h : QuasiIso ((ρC[U m]).map (f ≫ Pi.π (fun k => (ψC[U k]).obj (N k)) m) ≫
      (adj[U m]).counit.app (N m))) : QuasiIso ((ρC[U m]).map f) := by
  have := isIso_map_π_comp_counit U hU N m
  rw [Functor.map_comp, Category.assoc] at h
  exact (quasiIso_iff_comp_right _ _).1 h

/-- On a clopen decomposition, the product of the pushforwards of a family of
quasi-isomorphisms on the pieces is a quasi-isomorphism: on the `m`-th piece it is the `m`-th
member of the family. -/
theorem quasiIso_piMap_pushforward (hU : IsClopenDecomposition U)
    {P C : ∀ k, CochainComplex (SheafOfModules.{u}
      (structureSheafRing (restrictToOpen Y.toRingedSpace (U k)))) ℤ}
    (s : ∀ k, P k ⟶ C k) (hs : ∀ k, QuasiIso (s k)) :
    QuasiIso (Limits.Pi.map fun k => (ψC[U k]).map (s k)) := by
  refine quasiIso_of_forall_quasiIso_moduleRestriction U hU.iSup_eq_top _ fun m => ?_
  refine quasiIso_map_of_quasiIso_map_comp_π_counit U hU _ m ?_
  have := isIso_map_π_comp_counit U hU P m
  have := hs m
  rw [Limits.Pi.map_π, Functor.map_comp, Category.assoc]
  erw [(adj[U m]).counit.naturality (s m)]
  rw [← Category.assoc, Functor.id_map]
  infer_instance

/-- On a clopen decomposition, a complex `A` of `𝒪_Y`-modules maps quasi-isomorphically to the
product of the pushforwards of its restrictions to the pieces, by the units of the adjunctions
between restriction and pushforward. -/
theorem quasiIso_piLift_unit (hU : IsClopenDecomposition U)
    (A : CochainComplex (SheafOfModules.{u} (structureSheafRing Y.toRingedSpace)) ℤ) :
    QuasiIso (Pi.lift fun k => (adj[U k]).unit.app A) := by
  refine quasiIso_of_forall_quasiIso_moduleRestriction U hU.iSup_eq_top _ fun m => ?_
  refine quasiIso_map_of_quasiIso_map_comp_π_counit U hU _ m ?_
  have hl : (Pi.lift fun k => (adj[U k]).unit.app A) ≫
      Pi.π (fun k => (ψC[U k]).obj ((ρC[U k]).obj A)) m = (adj[U m]).unit.app A :=
    Pi.lift_π _ _
  rw [hl, (adj[U m]).left_triangle_components A]
  exact (inferInstance : QuasiIso (𝟙 ((ρC[U m]).obj A)))

open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces in
/-- **Glueing along a clopen decomposition.** If the derived restriction of `K ∈ D(𝒪_Y)` to each
piece `Uᵢ` of a decomposition of `Y` into open and closed subschemes is isomorphic to a complex
`Pᵢ`, then `K` is isomorphic to the product `∏ᵢ jᵢ_* Pᵢ` of their pushforwards. -/
theorem nonempty_iso_Q_pi_pushforward (hU : IsClopenDecomposition U)
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y.toRingedSpace)))
    (P : ∀ k, CochainComplex (SheafOfModules.{u}
      (structureSheafRing (restrictToOpen Y.toRingedSpace (U k)))) ℤ)
    (e : ∀ k, (derivedPullback (U k).ι.toLRSHom.toShHom).obj K ≅ DerivedCategory.Q.obj (P k)) :
    Nonempty (K ≅ DerivedCategory.Q.obj (∏ᶜ fun k => (ψC[U k]).obj (P k))) := by
  classical
  obtain ⟨A, ⟨eA⟩⟩ : ∃ A : CochainComplex (SheafOfModules.{u}
      (structureSheafRing Y.toRingedSpace)) ℤ, Nonempty (DerivedCategory.Q.obj A ≅ K) :=
    ⟨_, ⟨DerivedCategory.Q.objObjPreimageIso K⟩⟩
  have φ : ∀ k, DerivedCategory.Q.obj ((ρC[U k]).obj A) ≅ DerivedCategory.Q.obj (P k) := fun k =>
    ((ρ[U k]).mapDerivedCategoryFactors.app A).symm ≪≫
      (Stacks.Cohomology.DerivedOpenImmersion.derivedPullbackModuleRestrictionIso
        Y.toRingedSpace (U k)).symm.app (DerivedCategory.Q.obj A) ≪≫
      (derivedPullback (U k).ι.toLRSHom.toShHom).mapIso eA ≪≫ e k
  choose C g s hs hfac using fun k => DerivedCategory.left_fac
    (C := SheafOfModules.{u} (structureSheafRing (restrictToOpen Y.toRingedSpace (U k)))) (φ k).hom
  have hg : ∀ k, QuasiIso (g k) := fun k => by
    rw [← DerivedCategory.isIso_Q_map_iff_quasiIso]
    have h : DerivedCategory.Q.map (g k) = (φ k).hom ≫ DerivedCategory.Q.map (s k) := by
      rw [hfac k]; simp
    rw [h]
    infer_instance
  have hs' : ∀ k, QuasiIso (s k) := fun k =>
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ (s k)).1 (hs k)
  let α : A ⟶ ∏ᶜ fun k => (ψC[U k]).obj (C k) :=
    Pi.lift fun k => (adj[U k]).homEquiv _ _ (g k)
  let β : (∏ᶜ fun k => (ψC[U k]).obj (P k)) ⟶ ∏ᶜ fun k => (ψC[U k]).obj (C k) :=
    Limits.Pi.map fun k => (ψC[U k]).map (s k)
  have hα : QuasiIso α := by
    have e : α = (Pi.lift fun k => (adj[U k]).unit.app A) ≫
        Limits.Pi.map fun k => (ψC[U k]).map (g k) :=
      Pi.hom_ext _ _ fun k => by simp [α, Adjunction.homEquiv_unit]
    have := quasiIso_piLift_unit U hU A
    have := quasiIso_piMap_pushforward U hU g hg
    rw [e]
    infer_instance
  have hβ : QuasiIso β := quasiIso_piMap_pushforward U hU s hs'
  have : IsIso (DerivedCategory.Q.map α) := by
    rw [DerivedCategory.isIso_Q_map_iff_quasiIso]; exact hα
  have : IsIso (DerivedCategory.Q.map β) := by
    rw [DerivedCategory.isIso_Q_map_iff_quasiIso]; exact hβ
  exact ⟨eA.symm ≪≫ asIso (DerivedCategory.Q.map α) ≪≫ (asIso (DerivedCategory.Q.map β)).symm⟩

/-- The restriction of the glued complex to a piece is the complex given there. -/
noncomputable def restrictPiPushforwardIso (hU : IsClopenDecomposition U)
    (P : ∀ k, CochainComplex (SheafOfModules.{u}
      (structureSheafRing (restrictToOpen Y.toRingedSpace (U k)))) ℤ) (m : I) :
    (ρC[U m]).obj (∏ᶜ fun k => (ψC[U k]).obj (P k)) ≅ P m :=
  have := isIso_map_π_comp_counit U hU P m
  asIso ((ρC[U m]).map (Pi.π (fun k => (ψC[U k]).obj (P k)) m) ≫ (adj[U m]).counit.app (P m))

/-- On a clopen decomposition, the product of the pushforwards of bounded complexes of finite
locally free modules on the pieces is a locally bounded complex of finite locally free
`𝒪_Y`-modules: on each piece it is the complex given there. -/
theorem isLocallyBoundedFiniteLocallyFree_pi_pushforward (hU : IsClopenDecomposition U)
    (P : ∀ k, CochainComplex (U k : Scheme.{u}).Modules ℤ)
    (hflf : ∀ k n, SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (R := StrictlyPerfect.structureSheafOfRings (U k : Scheme.{u}).toRingedSpace) ((P k).X n))
    (hbd : ∀ k, ∃ lo hi : ℤ, ∀ n, (n < lo ∨ hi < n) → IsZero ((P k).X n)) :
    IsLocallyBoundedFiniteLocallyFree (X := Y.toRingedSpace)
      (∏ᶜ fun k => (ψC[U k]).obj (P k)) := by
  refine ⟨fun n => ?_, fun y => ?_⟩
  · refine Stacks.Modules.isFiniteLocallyFree_localGenerators_of_iSup_eq_top _ U hU.iSup_eq_top
      fun k => ?_
    exact AlgebraicGeometry.RingedSpace.isFiniteLocallyFree_of_iso
      (((Stacks.AlgebraicGeometry.PerfectCohomology.restrictModulesIsoRestrict Y (U k)).app
        _).symm ≪≫
        (HomologicalComplex.eval _ (ComplexShape.up ℤ) n).mapIso
          (restrictPiPushforwardIso U hU P k)) (hflf k n)
  · obtain ⟨lo, hi, h⟩ := hbd (hU.index y)
    refine ⟨U (hU.index y), hU.mem_index y, lo, hi, fun n hn => ?_⟩
    exact (h n hn).of_iso ((HomologicalComplex.eval _ (ComplexShape.up ℤ) n).mapIso
      (restrictPiPushforwardIso U hU P (hU.index y)))

open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces in
/-- **Glueing bounded complexes of finite locally free modules along a clopen decomposition.** If
the derived restriction of `K ∈ D(𝒪_Y)` to each piece of a decomposition of `Y` into open and
closed subschemes is represented by a bounded complex of finite locally free modules, then `K`
is represented by a locally bounded complex of finite locally free `𝒪_Y`-modules. -/
theorem exists_isLocallyBoundedFiniteLocallyFree_iso (hU : IsClopenDecomposition U)
    (K : DerivedCategory Y.Modules) (P : ∀ k, CochainComplex (U k : Scheme.{u}).Modules ℤ)
    (hflf : ∀ k n, SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (R := StrictlyPerfect.structureSheafOfRings (U k : Scheme.{u}).toRingedSpace) ((P k).X n))
    (hbd : ∀ k, ∃ lo hi : ℤ, ∀ n, (n < lo ∨ hi < n) → IsZero ((P k).X n))
    (e : ∀ k, (derivedPullback (U k).ι.toLRSHom.toShHom).obj K ≅ DerivedCategory.Q.obj (P k)) :
    ∃ Q : CochainComplex Y.Modules ℤ, IsLocallyBoundedFiniteLocallyFree Q ∧
      Nonempty (K ≅ DerivedCategory.Q.obj Q) := by
  obtain ⟨eK⟩ := nonempty_iso_Q_pi_pushforward U hU K P e
  exact ⟨_, isLocallyBoundedFiniteLocallyFree_pi_pushforward U hU P hflf hbd, ⟨eK⟩⟩

end Stacks.Chow.ClopenGlueing

end
