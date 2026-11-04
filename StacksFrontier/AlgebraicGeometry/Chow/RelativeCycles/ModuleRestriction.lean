module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.StalkLinearEquiv
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatShortExactSequence
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.AssociatedToModule
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.Restriction
public import StacksFrontier.AlgebraicGeometry.Perfect.SupportPullback.Basic
public import StacksCore.Tactic.StacksAttribute

/-!
# Restriction of the family of cycles associated to a module

Let `f : X ⟶ S` be locally of finite type, let `F` be a quasi-coherent `𝒪_X`-module of finite
type whose support on every fibre of `f` has dimension at most `r`, and let `U ⊆ X` and `V ⊆ S`
be open subschemes with `f(U) ⊆ V`. Restricting `F` to `U` leaves the hypothesis intact — the
fibre `U_t` is an open subscheme of `X_{i t}` and the support of `F|_U` on it is the inverse
image of the support of `F` on `X_{i t}` — and the family of cycles associated to `F|_U` is the
restriction to `U/V` of the family associated to `F`.

Coefficientwise this says that the multiplicity of `F` is unchanged by restriction to an open
subscheme and that the relative dimension of a point of `U_t` over `κ(t)` equals the relative
dimension of its image in `X_{i t}` over `κ(i t)`.

## Main results

* `Stacks.Chow.sheafMultiplicity_eq_of_iso` — multiplicity is an isomorphism invariant.
* `Stacks.Chow.sheafMultiplicity_pullback_of_isOpenImmersion` — pulling back along an open
  immersion changes no multiplicity.
* `Stacks.Chow.supp_pullback_fiberι_restrict` — the fibrewise support of the restricted module
  is the inverse image of the fibrewise support of the original one.
* `Stacks.Chow.supportDimension_le_of_openRestriction` — the dimension bound on the fibrewise
  supports survives restriction to open subschemes.
* `Stacks.Chow.familyAssociatedToModule_openRestriction` — the restriction of the family
  associated to a module is the family associated to the restricted module.

## Implementation notes

The two fibres `U_t` and `X_{i t}` are compared by `AlgebraicGeometry.restrictedFiberMap`, the open
immersion of fibres attached to the commutative square, and the two modules on `U_t` obtained by
pulling `F` back in the two possible orders are compared by the pullback-composition isomorphism;
multiplicity is then transported along that isomorphism rather than recomputed. The structure
morphisms of the two fibres lie over the isomorphism `Spec κ(t) ≅ Spec κ(i t)` induced by `i`, so
the comparison of relative dimensions is
`Stacks.Chow.relativeDimension_eq_of_openImmersion_over_iso` and no transcendence degree is
computed here.

The stalk of a module of finite type pulled back along an open immersion is the base change of
the original stalk along the induced isomorphism of local rings (Tag 0098), and extension of
scalars along a surjection does not change length; that is the whole content of the invariance
of multiplicity.

## References

* [Stacks Project, Tag 0H4R](https://stacks.math.columbia.edu/tag/0H4R)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

/-! ### A dimension bound for preimages -/

/-- The inverse image of a subset under an inducing map has dimension at most that of the
subset: the induced map of subspaces is again inducing.

This is a statement of general topology, with no scheme and no field in it, and its home is
beside `topologicalKrullDim_le_of_subset` in `StacksFrontier.Topology.Dimension.Krull`; a copy
there would also absorb the same one-line step as it is open-coded in
`Stacks.Chow.supportDimension_le_of_baseChange` and in
`Stacks.Chow.topologicalKrullDim_supp_pullback_le`. -/
private theorem topologicalKrullDim_preimage_le {A B : Type u} [TopologicalSpace A]
    [TopologicalSpace B] {e : A → B} (he : Topology.IsInducing e) (T : Set B) :
    topologicalKrullDim (e ⁻¹' T) ≤ topologicalKrullDim T :=
  ((he.comp Topology.IsInducing.subtypeVal).codRestrict
    fun x : e ⁻¹' T => x.2).topologicalKrullDim_le

/-! ### Multiplicity under isomorphisms and open pullbacks -/

/-- Isomorphic modules have the same multiplicity at every point: their stalks are isomorphic as
modules over the stalk of the structure sheaf, and length is an isomorphism invariant. -/
theorem sheafMultiplicity_eq_of_iso {X : Scheme.{u}} {M N : X.Modules} (e : M ≅ N) (x : X) :
    sheafMultiplicity M x = sheafMultiplicity N x :=
  let := SheafOfModules.FlatShortExact.stalkModule (X := X.toRingedSpace) M x
  let := SheafOfModules.FlatShortExact.stalkModule (X := X.toRingedSpace) N x
  congrArg (fun n : ℕ∞ => (n.toNat : ℤ))
    (SheafOfModules.FlatShortExact.stalkLinearEquivOfIso e x).length_eq

/-- Pulling back along an open immersion does not change the multiplicity: the stalk of the
pullback is the base change of the stalk along the isomorphism of local rings induced by the
open immersion, and extension of scalars along an isomorphism changes no length. -/
theorem sheafMultiplicity_pullback_of_isOpenImmersion {A B : Scheme.{u}} (g : A ⟶ B)
    [IsOpenImmersion g] (F : B.Modules) (x : A) :
    sheafMultiplicity ((Scheme.Modules.pullback g).obj F) x = sheafMultiplicity F (g x) := by
  let R := B.presheaf.stalk (g x)
  let S := A.presheaf.stalk x
  let M := TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) F.val.presheaf (g x)
  let N := TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
    ((Scheme.Modules.pullback g).obj F).val.presheaf x
  let : Module R M :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      F.val (g x)
  let : Module S N :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      ((Scheme.Modules.pullback g).obj F).val x
  have : IsIso (g.stalkMap x) := (IsOpenImmersion.iff_isIso_stalkMap.mp ‹_›).2 x
  let ρ : R ≃+* S := (asIso (g.stalkMap x)).commRingCatIsoToRingEquiv
  let : Algebra R S := ρ.toRingHom.toAlgebra
  let : Module S M := Module.compHom M ρ.symm.toRingHom
  let : IsScalarTower R S M := ⟨fun r s m => by
    change ρ.symm (ρ r * s) • m = r • (ρ.symm s • m)
    rw [map_mul, RingEquiv.symm_apply_apply, mul_smul]⟩
  let : TensorProduct.CompatibleSMul R S S M :=
    TensorProduct.CompatibleSMul.of_algebraMap_surjective
      (R := R) (A := S) (M := S) (N := M) ρ.surjective
  obtain ⟨ePull, -⟩ := RingedSpaceModuleAdjunction.exists_modulePullbackStalkLinearEquiv
    g.toLRSHom.toShHom F x
  let e : N ≃ₗ[S] TensorProduct R S M := ePull
  have hlenPull : Module.length S N = Module.length S (TensorProduct R S M) := e.length_eq
  have hlenScalars : Module.length R M = Module.length S M :=
    Module.length_eq_of_surjective (S := R) (R := S) (M := M) ρ.surjective
  change ((Module.length S N).toNat : ℤ) = ((Module.length R M).toNat : ℤ)
  exact congrArg (fun n : ℕ∞ => (n.toNat : ℤ))
    (hlenPull.trans ((TensorProduct.lidOfCompatibleSMul R S M).length_eq.trans hlenScalars.symm))

/-! ### The fibrewise support and multiplicity of a restricted module -/

/-- The support of the module restricted to `U` on the fibre of `fU` over `t` is the inverse
image, along the canonical open immersion of fibres, of the support of the original module on
the fibre of `f` over `i t`. -/
theorem supp_pullback_fiberι_restrict {X S U V : Scheme.{u}} (f : X ⟶ S) (fU : U ⟶ V)
    (j : U ⟶ X) [IsOpenImmersion j] (i : V ⟶ S) (h : j ≫ f = fU ≫ i) (F : X.Modules)
    [F.IsFiniteType] (t : V) :
    SheafOfModules.supp ((Scheme.Modules.pullback (fU.fiberι t)).obj
        ((Scheme.Modules.pullback j).obj F)) =
      (restrictedFiberMap f fU j i h t) ⁻¹'
        SheafOfModules.supp ((Scheme.Modules.pullback (f.fiberι (i t))).obj F) := by
  have hpoint : ∀ y : fU.fiber t,
      f.fiberι (i t) (restrictedFiberMap f fU j i h t y) = j (fU.fiberι t y) := fun y => by
    simpa only [Scheme.Hom.comp_apply] using
      congrArg (fun q : fU.fiber t ⟶ X => q y) (restrictedFiberMap_fiberι f fU j i h t)
  rw [SheafOfModules.supp_pullback, SheafOfModules.supp_pullback, SheafOfModules.supp_pullback]
  ext y
  simp only [Set.mem_preimage, hpoint]

/-- The fibre map of a square of open immersions is an open immersion, as an instance. -/
private instance isOpenImmersion_restrictedFiberMap {X S U V : Scheme.{u}} (f : X ⟶ S)
    (fU : U ⟶ V) (j : U ⟶ X) [IsOpenImmersion j] (i : V ⟶ S) [IsOpenImmersion i]
    (h : j ≫ f = fU ≫ i) (t : V) : IsOpenImmersion (restrictedFiberMap f fU j i h t) :=
  restrictedFiberMap_isOpenImmersion f fU j i h t

/-- Comparison of the two ways of pulling a module back to the fibre of the restricted morphism
over `t`: restricting to `U` and then pulling back to the fibre of `fU`, or pulling back to the
fibre of `f` over `i t` and then along the canonical map of fibres. -/
private def fiberPullbackIso {X S U V : Scheme.{u}} (f : X ⟶ S) (fU : U ⟶ V) (j : U ⟶ X)
    (i : V ⟶ S) (h : j ≫ f = fU ≫ i) (F : X.Modules) (t : V) :
    (Scheme.Modules.pullback (fU.fiberι t)).obj ((Scheme.Modules.pullback j).obj F) ≅
      (Scheme.Modules.pullback (restrictedFiberMap f fU j i h t)).obj
        ((Scheme.Modules.pullback (f.fiberι (i t))).obj F) :=
  (Scheme.Modules.pullbackComp (fU.fiberι t) j).app F ≪≫
    (Scheme.Modules.pullbackCongr (restrictedFiberMap_fiberι f fU j i h t).symm).app F ≪≫
      ((Scheme.Modules.pullbackComp (restrictedFiberMap f fU j i h t)
        (f.fiberι (i t))).app F).symm

/-- The multiplicity of the restricted module at a point of a fibre of `fU` is the multiplicity
of the original module at the image point in the corresponding fibre of `f`. -/
theorem sheafMultiplicity_pullback_fiberι_restrict {X S U V : Scheme.{u}} (f : X ⟶ S)
    (fU : U ⟶ V) (j : U ⟶ X) [IsOpenImmersion j] (i : V ⟶ S) [IsOpenImmersion i]
    (h : j ≫ f = fU ≫ i) (F : X.Modules) (t : V) (x : fU.fiber t) :
    sheafMultiplicity ((Scheme.Modules.pullback (fU.fiberι t)).obj
          ((Scheme.Modules.pullback j).obj F)) x =
      sheafMultiplicity ((Scheme.Modules.pullback (f.fiberι (i t))).obj F)
        (restrictedFiberMap f fU j i h t x) :=
  (sheafMultiplicity_eq_of_iso (fiberPullbackIso f fU j i h F t) x).trans
    (sheafMultiplicity_pullback_of_isOpenImmersion (restrictedFiberMap f fU j i h t) _ x)

/-! ### Restriction of the associated family -/

/-- **Stacks Project, Tag 0H4R.** The dimension bound on the fibrewise supports of a
quasi-coherent module of finite type survives restriction of both the source and the base to
compatible open subschemes: the support on the fibre of `fU` over `t` is the inverse image of
the support on the fibre of `f` over `i t` along an open immersion of fibres. -/
@[stacks 0H4R "module_restriction: dimension bound"]
theorem supportDimension_le_of_openRestriction {X S U V : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] (fU : U ⟶ V) [LocallyOfFiniteType fU] (j : U ⟶ X)
    [IsOpenImmersion j] (i : V ⟶ S) [IsOpenImmersion i] (h : j ≫ f = fU ≫ i) (F : X.Modules)
    [F.IsFiniteType] [F.IsQuasicoherent] (r : ℕ)
    (hdim : ∀ s : S, topologicalKrullDim
      (SheafOfModules.supp ((Scheme.Modules.pullback (f.fiberι s)).obj F)) ≤ (r : WithBot ℕ∞)) :
    ∀ t : V, topologicalKrullDim
      (SheafOfModules.supp ((Scheme.Modules.pullback (fU.fiberι t)).obj
        ((Scheme.Modules.pullback j).obj F))) ≤ (r : WithBot ℕ∞) := by
  intro t
  rw [supp_pullback_fiberι_restrict f fU j i h F t]
  exact (topologicalKrullDim_preimage_le
    (restrictedFiberMap f fU j i h t).isEmbedding.isInducing _).trans (hdim (i t))

/-- **Stacks Project, Tag 0H4R.** The restriction to `U/V` of the family of cycles associated to
a quasi-coherent module of finite type is the family associated to the module restricted to `U`.
Coefficientwise: restriction preserves the multiplicity of the module and the relative dimension
of a point of the fibre, and the support of the restricted module on a fibre of `fU` is the
inverse image of the support of the original one. -/
@[stacks 0H4R "module_restriction"]
theorem familyAssociatedToModule_openRestriction {X S U V : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] (fU : U ⟶ V) [LocallyOfFiniteType fU] (j : U ⟶ X)
    [IsOpenImmersion j] (i : V ⟶ S) [IsOpenImmersion i] (h : j ≫ f = fU ≫ i) (F : X.Modules)
    [F.IsFiniteType] [F.IsQuasicoherent] (r : ℕ)
    (hdim : ∀ s : S, topologicalKrullDim
      (SheafOfModules.supp ((Scheme.Modules.pullback (f.fiberι s)).obj F)) ≤ (r : WithBot ℕ∞)) :
    (restrictedFamily f fU j i h r (familyAssociatedToModule f F r hdim)).1 =
      familyAssociatedToModule fU ((Scheme.Modules.pullback j).obj F) r
        (supportDimension_le_of_openRestriction f fU j i h F r hdim) := by
  classical
  funext t
  apply Subtype.ext
  ext x
  have : IsIso (i.residueFieldMap t) := by
    have : IsIso (i.stalkMap t) :=
      (IsOpenImmersion.iff_isIso_stalkMap.mp (inferInstance : IsOpenImmersion i)).2 t
    exact (IsLocalRing.ResidueField.mapEquiv
      (asIso (i.stalkMap t)).commRingCatIsoToRingEquiv).toCommRingCatIso.isIso_hom
  let g := restrictedFiberMap f fU j i h t
  let sX := fU.fiberToSpecResidueField t
  let sY := f.fiberToSpecResidueField (i t)
  let Cx := fieldChowSituation (V.residueField t)
  let Cy := fieldChowSituation (S.residueField (i t))
  let M := (Scheme.Modules.pullback (f.fiberι (i t))).obj F
  let N := (Scheme.Modules.pullback (fU.fiberι t)).obj ((Scheme.Modules.pullback j).obj F)
  let eRes := asIso (Spec.map (i.residueFieldMap t))
  have hδ : ∀ z : fU.fiber t,
      Cx.dimensionFunction (sX z) = Cy.dimensionFunction (eRes.hom (sX z)) := by
    intro z
    rw [fieldChowSituation_dimensionFunction_eq_zero,
      fieldChowSituation_dimensionFunction_eq_zero]
  have hdimRel := relativeDimension_eq_of_openImmersion_over_iso g sX sY eRes
    (restrictedFiberMap_comp_fiberToSpecResidueField f fU j i h t).symm
    Cx.dimensionFunction Cy.dimensionFunction hδ x
  have hsupp : x ∈ SheafOfModules.supp N ↔ g x ∈ SheafOfModules.supp M := by
    rw [supp_pullback_fiberι_restrict f fU j i h F t]
    exact Set.mem_preimage
  have hmult : sheafMultiplicity N x = sheafMultiplicity M (g x) :=
    sheafMultiplicity_pullback_fiberι_restrict f fU j i h F t x
  calc
    ((restrictedFamily f fU j i h r (familyAssociatedToModule f F r hdim)).1 t :
          AlgebraicCycle (fU.fiber t) ℤ) x =
        (familyAssociatedToModule f F r hdim (i t) :
          AlgebraicCycle (f.fiber (i t)) ℤ) (g x) :=
      (restrictedFamily f fU j i h r (familyAssociatedToModule f F r hdim)).2 t x
    _ = (cycleAssociatedToCoherentSheaf Cy sY M (r : ℤ)
        (fiberModule_schemeDeltaDimension_le f F r hdim (i t))).1 (g x) :=
      congrArg (fun c : CycleGroup Cy sY (r : ℤ) => c.1 (g x))
        (familyAssociatedToModule_apply f F r hdim (i t))
    _ = (cycleAssociatedToCoherentSheaf Cx sX N (r : ℤ)
        (fiberModule_schemeDeltaDimension_le fU ((Scheme.Modules.pullback j).obj F) r
          (supportDimension_le_of_openRestriction f fU j i h F r hdim) t)).1 x := by
      rw [cycleAssociatedToCoherentSheaf_apply, cycleAssociatedToCoherentSheaf_apply]
      simp [hsupp, hmult, hdimRel]
    _ = (familyAssociatedToModule fU ((Scheme.Modules.pullback j).obj F) r
          (supportDimension_le_of_openRestriction f fU j i h F r hdim) t :
          AlgebraicCycle (fU.fiber t) ℤ) x :=
      (congrArg (fun c : CycleGroup Cx sX (r : ℤ) => c.1 x)
        (familyAssociatedToModule_apply fU ((Scheme.Modules.pullback j).obj F) r
          (supportDimension_le_of_openRestriction f fU j i h F r hdim) t)).symm

end Stacks.Chow

end
