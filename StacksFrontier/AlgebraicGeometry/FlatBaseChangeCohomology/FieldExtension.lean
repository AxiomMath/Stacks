module

public import Mathlib.Algebra.Field.Equiv
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.LocalDescentRefine
public import StacksFrontier.AlgebraicGeometry.Modules.AlternatingCechModuleBaseRing
public import StacksFrontier.AlgebraicGeometry.Modules.QuasicoherentPullbackScheme
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpaceBaseChange.CechComparison
public import StacksFrontier.AlgebraicGeometry.TwistCohomologyFiniteness.Basic
public import StacksFrontier.AlgebraicGeometry.Variety.EulerChar.FieldExtension

/-!
# The dimension of cohomology under extension of the ground field

For a scheme `X` separated and quasi-compact over a field `k`, a quasi-coherent `𝒪_X`-module `ℱ`
and an extension `k'/k`, the cohomology of the base change satisfies

`dim_{k'} Hⁿ(X_{k'}, ℱ_{k'}) = dim_k Hⁿ(X, ℱ)` for every `n`.

This is the dimension consequence of [Stacks, Tag 02KH] part (2) over a field.

## Main results

* `AlgebraicGeometry.finrank_cohomologyOverField_baseChange_field_of_quasiCompact`: the statement
  for a separated quasi-compact morphism to `Spec k`.
* `AlgebraicGeometry.finrank_cohomologyOverField_baseChange_field`: the same for a proper
  morphism.

## References

* [Stacks Project, Tag 02KG](https://stacks.math.columbia.edu/tag/02KG)
* [Stacks Project, Tag 02KH](https://stacks.math.columbia.edu/tag/02KH)
* [Stacks Project, Tag 01XD](https://stacks.math.columbia.edu/tag/01XD)
* [Stacks Project, Tag 08AB](https://stacks.math.columbia.edu/tag/08AB)
-/

@[expose] public noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry
open Stacks.Cohomology.CechSheaf (cechComplex)
open Stacks.AlgebraicGeometry.SectionsBaseChange (baseRestrictScalars baseExtendScalars
  flat_appLE_Spec_map preservesHomology_baseChange cechBaseChangeIsoOfPreimage
  top_eq_iSup_preimage le_preimage_top)

namespace AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard

/-! ### Dimension under change of rings -/

/-- Restriction of scalars along a ring isomorphism does not change the dimension. -/
private theorem finrank_restrictScalars_ringEquiv {R S : Type*} [Ring R] [Ring S]
    (e : R ≃+* S) (M : ModuleCat.{u} S) :
    Module.finrank R ((ModuleCat.restrictScalars e.toRingHom).obj M) = Module.finrank S M :=
  congrArg Cardinal.toNat (rank_eq_of_equiv_equiv e (AddEquiv.refl M) e.bijective fun _ _ => rfl)

/-- Extension of scalars along a ring map does not change the dimension of a free module. -/
private theorem finrank_extendScalars {R S : Type u} [CommRing R] [CommRing S]
    [StrongRankCondition R] [StrongRankCondition S] (φ : R →+* S) (M : ModuleCat.{u} R)
    [Module.Free R M] :
    Module.finrank S ((ModuleCat.extendScalars.{u, u, u} φ).obj M) = Module.finrank R M := by
  let := φ.toAlgebra
  exact Module.finrank_baseChange

/-- The ring of global sections of the spectrum of a field is a field. -/
@[instance_reducible]
private def fieldSectionRing (k : Type u) [Field k] : Field Γ(Spec (.of k), ⊤) :=
  ((Scheme.ΓSpecIso (.of k)).commRingCatIsoToRingEquiv.toMulEquiv.isField
    (Field.toIsField k)).toField

/-! ### A cover with affine finite intersections -/

/-- **A scheme quasi-compact and separated over an affine base has a finite cover by affine opens
all of whose nonempty finite intersections are affine.** -/
private theorem exists_finite_affineOpen_cover_inter {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsSeparated f] [QuasiCompact f] :
    ∃ (ι : Type u) (_ : Finite ι) (U : ι → X.Opens), (⊤ : X.Opens) = ⨆ i, U i ∧
      ∀ (r : ℕ) (s : Fin (r + 1) → ι), IsAffineOpen (⨅ j, U (s j)) := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  obtain ⟨ι, hι, V, hVaff, hVcov⟩ :=
    Stacks.AlgebraicGeometry.ModuleLimits.exists_finite_affineOpen_cover X
  have : IsSeparated (terminal.from X) := by
    rw [show terminal.from X = f ≫ terminal.from (Spec (CommRingCat.of k)) from
      terminal.hom_ext _ _]
    infer_instance
  exact ⟨ι, hι, V, le_antisymm (fun x _ => TopologicalSpace.Opens.mem_iSup.2 (hVcov x)) le_top,
    fun r s => IsAffineOpen.iInf fun j => hVaff (s j)⟩

/-! ### Homology commutes with the two change-of-rings functors -/

/-- **Base change of a complex over an affine base commutes with homology when the base ring map
is flat.** -/
private def homologyBaseChangeIso {S T X : Scheme.{u}} (iX : X ⟶ S) (q : T ⟶ S)
    (hq : RingHom.Flat (q.appLE ⊤ ⊤ (le_preimage_top q ⊤)).hom)
    (K : CochainComplex (ModuleCat.{u} Γ(X, ⊤)) ℕ) (p : ℕ) :
    (((baseRestrictScalars iX ⋙ baseExtendScalars q).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj K).homology p ≅
      (baseRestrictScalars iX ⋙ baseExtendScalars q).obj (K.homology p) :=
  have := preservesHomology_baseChange iX q hq
  (K.sc p).mapHomologyIso (baseRestrictScalars iX ⋙ baseExtendScalars q)

/-- **Restriction of scalars commutes with homology.** -/
private def homologyRestrictIso {T Y : Scheme.{u}} (kY : Y ⟶ T)
    (K : CochainComplex (ModuleCat.{u} Γ(Y, ⊤)) ℕ) (p : ℕ) :
    (((baseRestrictScalars kY).mapHomologicalComplex (ComplexShape.up ℕ)).obj K).homology p ≅
      (baseRestrictScalars kY).obj (K.homology p) :=
  have := Stacks.Cohomology.CechAcyclic.preservesHomology_restrictScalars
    (kY.appLE ⊤ ⊤ (le_preimage_top kY ⊤)).hom
  (K.sc p).mapHomologyIso (baseRestrictScalars kY)

/-! ### The Čech presentation of the cohomology over the ring of sections of the base -/

/-- **The dimension of the cohomology over `k` is the dimension over `Γ(Spec k, ⊤)` of the Čech
homology.** -/
private theorem finrank_cohomologyOverField_cech (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) {I : Type u} (Ui : I → X.Opens) (hU : (⊤ : X.Opens) = ⨆ i, Ui i)
    (haffine : ∀ (r : ℕ) (s : Fin (r + 1) → I), IsAffineOpen (⨅ j, Ui (s j)))
    (F : X.Modules) [F.IsQuasicoherent] (p : ℕ) :
    Module.finrank k (cohomologyOverField k f F p) =
      Module.finrank Γ(Spec (.of k), ⊤)
        ((baseRestrictScalars f).obj
          ((cechComplex.{u, u, u, u} (⊤ : X.Opens) Ui hU F).homology p)) := by
  let e : k ≃+* Γ(Spec (.of k), ⊤) :=
    (Scheme.ΓSpecIso (.of k)).symm.commRingCatIsoToRingEquiv
  rw [← finrank_restrictScalars_ringEquiv e
    ((baseRestrictScalars f).obj ((cechComplex.{u, u, u, u} (⊤ : X.Opens) Ui hU F).homology p))]
  refine Iso.toLinearEquiv ?_ |>.finrank_eq
  exact cohomologyOverFieldCechHomologyIso k f Ui hU haffine F p ≪≫
    ModuleCat.restrictScalarsComp'App e.toRingHom
      (f.appLE ⊤ ⊤ (le_preimage_top f ⊤)).hom
      (cohomologyOverFieldSectionRingHom k f) (by ext x; rfl) _

/-! ### [Stacks, Tag 02KH] part (2) for an extension of the ground field -/

/-- **The dimension of cohomology is unchanged by extension of the ground field**, for a scheme
separated and quasi-compact over the field and a quasi-coherent module on it. This is the
dimension consequence of [Stacks, Tag 02KH] part (2), in every degree. -/
theorem finrank_cohomologyOverField_baseChange_field_of_quasiCompact
    (k k' : Type u) [Field k] [Field k'] [Algebra k k']
    {X' X : Scheme.{u}} (g' : X' ⟶ X) (f' : X' ⟶ Spec (.of k')) (f : X ⟶ Spec (.of k))
    (h : IsPullback g' f' f (Spec.map (CommRingCat.ofHom (algebraMap k k'))))
    [IsSeparated f] [QuasiCompact f] (F : X.Modules) [F.IsQuasicoherent] (n : ℕ) :
    Module.finrank k' (cohomologyOverField k' f' ((Scheme.Modules.pullback g').obj F) n) =
      Module.finrank k (cohomologyOverField k f F n) := by
  obtain ⟨ι, hι, U, hU, hUaff⟩ := exists_finite_affineOpen_cover_inter f
  have hU' : (⊤ : X'.Opens) = ⨆ i, g' ⁻¹ᵁ U i := top_eq_iSup_preimage U hU g'
  have hU'aff : ∀ (r : ℕ) (s : Fin (r + 1) → ι), IsAffineOpen (⨅ j, g' ⁻¹ᵁ U (s j)) := by
    intro r s
    rw [← Stacks.ProjectiveCohomology.preimage_iInf g' fun j => U (s j)]
    exact Stacks.Cech.isAffineOpen_preimage_of_isPullback (algebraMap k k') f f' g' h (hUaff r s)
  have hflat : RingHom.Flat
      ((Spec.map (CommRingCat.ofHom (algebraMap k k'))).appLE ⊤ ⊤
        (le_preimage_top (Spec.map (CommRingCat.ofHom (algebraMap k k'))) ⊤)).hom :=
    flat_appLE_Spec_map (CommRingCat.ofHom (algebraMap k k'))
      (RingHom.flat_algebraMap_iff.2 inferInstance)
  have i1 := homologyBaseChangeIso f (Spec.map (CommRingCat.ofHom (algebraMap k k'))) hflat
    (cechComplex.{u, u, u, u} (⊤ : X.Opens) U hU F) n
  have i2 := (HomologicalComplex.homologyFunctor _ (ComplexShape.up ℕ) n).mapIso
    (cechBaseChangeIsoOfPreimage h F U hU (fun {m} x => hUaff m x)
      (fun i => g' ⁻¹ᵁ U i) (fun _ => rfl) hU')
  have i3 := homologyRestrictIso f'
    (cechComplex.{u, u, u, u} (⊤ : X'.Opens) (fun i => g' ⁻¹ᵁ U i) hU'
      ((Scheme.Modules.pullback g').obj F)) n
  let := fieldSectionRing k
  let := fieldSectionRing k'
  refine (finrank_cohomologyOverField_cech k' f' (fun i => g' ⁻¹ᵁ U i) hU' hU'aff
    ((Scheme.Modules.pullback g').obj F) n).trans
      (Eq.trans ?_ (finrank_cohomologyOverField_cech k f U hU hUaff F n).symm)
  exact (i1.symm ≪≫ i2 ≪≫ i3).toLinearEquiv.finrank_eq.symm.trans (finrank_extendScalars _ _)

/-- **[Stacks, Tag 02KH] part (2) for a field extension.** For a proper scheme over a field and a
quasi-coherent module on it, the dimension of cohomology in every degree is unchanged by
extension of the ground field. -/
theorem finrank_cohomologyOverField_baseChange_field
    (k k' : Type u) [Field k] [Field k'] [Algebra k k']
    {X' X : Scheme.{u}} (g' : X' ⟶ X) (f' : X' ⟶ Spec (.of k')) (f : X ⟶ Spec (.of k))
    (h : IsPullback g' f' f (Spec.map (CommRingCat.ofHom (algebraMap k k')))) [IsProper f]
    (F : X.Modules) [F.IsQuasicoherent] (n : ℕ) :
    Module.finrank k' (cohomologyOverField k' f' ((Scheme.Modules.pullback g').obj F) n) =
      Module.finrank k (cohomologyOverField k f F n) :=
  finrank_cohomologyOverField_baseChange_field_of_quasiCompact k k' g' f' f h F n

end AlgebraicGeometry

end
