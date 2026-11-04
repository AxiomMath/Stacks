module

public import StacksFrontier.Topology.Sheaves.Cohomology.InvertibleDerivedIdempotentSplitting
public import StacksFrontier.Topology.Sheaves.Modules.AssociatedSheaf.FreeRetract
public import StacksFrontier.Topology.Sheaves.Modules.AssociatedSheaf.Tensor
public import StacksFrontier.Homology.DerivedCategory.Monoidal.InvertibleRingKunneth
public import StacksFrontier.Topology.Sheaves.Cohomology.StrictlyPerfect.LocalNullHomotopy
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.AssociatedSheafScalarNormalisation

/-!
# The sheaf associated to a module over the global sections, and scalars

Let `(Y, 𝒪_Y)` be a ringed space and `R = Γ(Y, 𝒪_Y)`. Construction (3) of Stacks 01BH, the
functor `ℱ : Mod(R) ⥤ Mod(𝒪_Y)` left adjoint to global sections, is `R`-linear: it carries
multiplication by `r ∈ R` on a module to multiplication by the global section `r`. If `N` is an
invertible `R`-module, no nonzero local section of `𝒪_Y` annihilates `ℱ_N`.

## References

* [Stacks Project, Tag 01BH](https://stacks.math.columbia.edu/tag/01BH)
* [Stacks Project, Tag 0FPG](https://stacks.math.columbia.edu/tag/0FPG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
open Stacks.SheafOfModules.DerivedMonoidal Stacks.AssociatedSheaf StrictlyPerfect

universe u

namespace Stacks.Cohomology.InvertibleDerived

variable (Y : RingedSpace.{u, u})

/-- The ring of global sections of `𝒪_Y`. -/
public abbrev GlobalRing : Type u := Y.presheaf.obj (op ⊤)

/-- Construction (3) of Stacks 01BH over the global sections. -/
public abbrev assocF : ModuleCat.{u} (GlobalRing Y) ⥤ SheafOfModules.{u} (structureSheafRing Y) :=
  associatedSheafFunctor.{u, u} Y (RingHom.id (GlobalRing Y))

/-- Global sections over the global sections. -/
public abbrev gammaF : SheafOfModules.{u} (structureSheafRing Y) ⥤ ModuleCat.{u} (GlobalRing Y) :=
  globalSectionsFunctor.{u, u} Y (RingHom.id (GlobalRing Y))

/-- The adjunction `ℱ ⊣ Γ` of Stacks 01BH (4). -/
public abbrev assocAdj : assocF Y ⊣ gammaF Y :=
  associatedSheafAdjunction.{u, u} Y (RingHom.id (GlobalRing Y))

open DerivedCategory.Invertible in
/-- **Global sections carry multiplication by a global section to multiplication by a scalar.** -/
public theorem gammaF_map_smulHom (F : Mod Y.sheaf)
    (s : GlobalRing Y) :
    (gammaF Y).map (smulHom s F) = (scalarNatTrans s).app ((gammaF Y).obj F) := by
  ext y
  rfl

open DerivedCategory.Invertible in
/-- **Construction (3) of Stacks 01BH is linear over the global sections.** -/
public theorem assocF_map_scalarNatTrans (N : ModuleCat.{u} (GlobalRing Y)) (r : GlobalRing Y) :
    (assocF Y).map ((scalarNatTrans r).app N) = smulHom r ((assocF Y).obj N) := by
  apply ((assocAdj Y).homEquiv N _).injective
  refine ((assocAdj Y).homEquiv_unit _ _ _).trans
    (Eq.trans ?_ ((assocAdj Y).homEquiv_unit _ _ _).symm)
  exact (((assocAdj Y).unit.naturality ((scalarNatTrans r).app N)).symm).trans
    ((scalarNatTrans_naturality r ((assocAdj Y).unit.app N)).trans
      (congrArg ((assocAdj Y).unit.app N ≫ ·) (gammaF_map_smulHom Y _ r).symm))

/-- **A direct summand of a finite free module is the sheaf associated to its global sections.** -/
public theorem isIso_assocAdj_counit (F : OXMod.{u, u} Y) (hF : IsDirectSummandOfFiniteFree F) :
    IsIso ((assocAdj Y).counit.app F) := by
  obtain ⟨n, ⟨ρ⟩⟩ := (isDirectSummandOfFiniteFree_iff_retract F).mp hF
  exact isIso_counit_of_retract_free Y (ULift.{u} (Fin n)) F
    (ρ.trans (Retract.ofIso (StrictlyPerfect.finiteFreeIsoFree Y n)))

/-- A complex of direct summands of finite free modules is the complex associated to its complex
of global sections. -/
public def assocGammaIso (E : CochainComplex (OXMod.{u, u} Y) ℤ)
    (hE : ∀ i, IsDirectSummandOfFiniteFree (E.X i)) :
    ((assocF Y).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      (((gammaF Y).mapHomologicalComplex (ComplexShape.up ℤ)).obj E) ≅ E :=
  HomologicalComplex.Hom.isoOfComponents
    (fun i => haveI := isIso_assocAdj_counit Y (E.X i) (hE i)
      asIso ((assocAdj Y).counit.app (E.X i)))
    (fun i j _ => ((assocAdj Y).counit.naturality (E.d i j)).symm)

/-- The unit of an adjunction is an isomorphism at a retract of an object where it is one. -/
public theorem isIso_unit_of_retract {C D : Type*} [Category* C] [Category* D] {Lf : C ⥤ D}
    {Gf : D ⥤ C} (adj : Lf ⊣ Gf) {A B : C} (ρ : Retract A B) [IsIso (adj.unit.app B)] :
    IsIso (adj.unit.app A) := by
  have h1 : adj.unit.app A ≫ (Lf ⋙ Gf).map ρ.i = ρ.i ≫ adj.unit.app B :=
    (adj.unit.naturality ρ.i).symm
  have h2 : ρ.r ≫ adj.unit.app A = adj.unit.app B ≫ (Lf ⋙ Gf).map ρ.r :=
    adj.unit.naturality ρ.r
  refine ⟨(Lf ⋙ Gf).map ρ.i ≫ inv (adj.unit.app B) ≫ ρ.r, ?_, ?_⟩
  · rw [← Category.assoc, h1, Category.assoc, IsIso.hom_inv_id_assoc, ρ.retract]
    rfl
  · rw [Category.assoc, Category.assoc, h2, IsIso.inv_hom_id_assoc, ← Functor.map_comp, ρ.retract,
      CategoryTheory.Functor.map_id]

/-- **The unit of `ℱ ⊣ Γ` is an isomorphism at a finite projective module.** -/
public theorem isIso_assocAdj_unit (N : ModuleCat.{u} (GlobalRing Y))
    [Module.Finite (GlobalRing Y) N] [Module.Projective (GlobalRing Y) N] :
    IsIso ((assocAdj Y).unit.app N) := by
  obtain ⟨n, f, g, -, -, hfg⟩ := Module.Finite.exists_comp_eq_id_of_projective (GlobalRing Y) N
  let eL : (ULift.{u} (Fin n) →₀ GlobalRing Y) ≃ₗ[GlobalRing Y] (Fin n → GlobalRing Y) :=
    (Finsupp.linearEquivFunOnFinite (GlobalRing Y) (GlobalRing Y) (ULift.{u} (Fin n))).trans
      (LinearEquiv.funCongrLeft (GlobalRing Y) (GlobalRing Y) Equiv.ulift.symm)
  have := isIso_unit_free Y (ULift.{u} (Fin n))
  let ρ : Retract N ((ModuleCat.free (GlobalRing Y)).obj (ULift.{u} (Fin n))) :=
    ⟨ModuleCat.ofHom (eL.symm.toLinearMap ∘ₗ g), ModuleCat.ofHom (f ∘ₗ eL.toLinearMap), by
      refine ModuleCat.hom_ext (LinearMap.ext fun m => ?_)
      exact (congrArg f (eL.apply_symm_apply (g m))).trans (LinearMap.congr_fun hfg m)⟩
  exact isIso_unit_of_retract (assocAdj Y) ρ

end Stacks.Cohomology.InvertibleDerived

end
