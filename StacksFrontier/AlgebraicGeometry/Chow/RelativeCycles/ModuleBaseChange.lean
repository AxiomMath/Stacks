module

public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.Composition
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.ModuleRestriction
public import StacksCore.Tactic.StacksAttribute

/-!
# Base change of the family of cycles associated to a module

Let `f : X ⟶ S` be locally of finite type, let `F` be a quasi-coherent `𝒪_X`-module of finite
type whose support on every fibre of `f` has dimension at most `r`, and let `g : S' ⟶ S` be a
morphism which induces an isomorphism on every residue field. Write `F'` for the pullback of `F`
to `X ×_S S'`. The fibre of `X ×_S S' ⟶ S'` over a point `t` is then isomorphic to the fibre of
`f` over `g t`, the support of `F'` on the former is the inverse image of the support of `F` on
the latter, so the dimension bound survives the base change, and the family of cycles associated
to `F'` is the base change of the family associated to `F`.

Coefficientwise this says that the multiplicity of `F` and the relative dimension of a point of
the fibre are both unchanged by the base change: the comparison map of fibres is an isomorphism
of schemes over the isomorphism `Spec κ(t) ≅ Spec κ(g t)`.

## Main results

* `Stacks.Chow.supp_pullback_fiberι_baseChange` — the fibrewise support of the base-changed
  module is the inverse image of the fibrewise support of the original one.
* `Stacks.Chow.sheafMultiplicity_pullback_fiberι_baseChange` — the base change changes no
  fibrewise multiplicity.
* `Stacks.Chow.supportDimension_le_of_baseChange` — the dimension bound on the fibrewise
  supports survives the base change.
* `Stacks.Chow.familyAssociatedToModule_baseChange` — the base change of the family associated
  to a module is the family associated to the base-changed module.

## Implementation notes

The two fibres are compared by `AlgebraicGeometry.restrictedFiberMap` applied to the pullback
square, where it is the comparison morphism `AlgebraicGeometry.baseChangeFiberMap` and so an
isomorphism by `AlgebraicGeometry.isIso_baseChangeFiberMap`, hence an open immersion;
the two modules on the fibre of the base change obtained by pulling `F` back in the two possible
orders are compared by the pullback-composition isomorphism, and multiplicity is transported
along that isomorphism rather than recomputed. The structure morphisms of the two fibres lie over
the isomorphism `Spec κ(t) ≅ Spec κ(g t)` induced by `g`, so the comparison of relative
dimensions is `Stacks.Chow.relativeDimension_eq_of_openImmersion_over_iso` and no transcendence
degree is computed here.

Only base change along a morphism that is an isomorphism on residue fields is treated, which is
the case in which no extension of the ground field enters and the base change of a family of
cycles is the fibrewise transport `Stacks.Chow.baseChangeFamilyOfResidueIso`.

## References

* [Stacks Project, Tag 0H4R](https://stacks.math.columbia.edu/tag/0H4R)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

variable {X S S' : Scheme.{u}}

/-! ### The module on a fibre of a base change -/

/-- The support of the base-changed module on the fibre of `X ×_S S' ⟶ S'` over `t` is the
inverse image, along the canonical map of fibres, of the support of the original module on the
fibre of `f` over `g t`. -/
theorem supp_pullback_fiberι_baseChange (f : X ⟶ S) (g : S' ⟶ S) (F : X.Modules)
    [F.IsFiniteType] (t : S') :
    SheafOfModules.supp ((Scheme.Modules.pullback ((pullback.snd f g).fiberι t)).obj
        ((Scheme.Modules.pullback (pullback.fst f g)).obj F)) =
      restrictedFiberMap f (pullback.snd f g) (pullback.fst f g) g pullback.condition t ⁻¹'
        SheafOfModules.supp ((Scheme.Modules.pullback (f.fiberι (g t))).obj F) := by
  have hpoint : ∀ y : (pullback.snd f g).fiber t,
      f.fiberι (g t) (restrictedFiberMap f (pullback.snd f g) (pullback.fst f g) g
          pullback.condition t y) =
        pullback.fst f g ((pullback.snd f g).fiberι t y) := fun y => by
    simpa only [Scheme.Hom.comp_apply] using
      congrArg (fun q : (pullback.snd f g).fiber t ⟶ X => q y)
        (restrictedFiberMap_fiberι f (pullback.snd f g) (pullback.fst f g) g
          pullback.condition t)
  rw [SheafOfModules.supp_pullback, SheafOfModules.supp_pullback, SheafOfModules.supp_pullback]
  ext y
  simp only [Set.mem_preimage]
  exact Iff.of_eq (congrArg (fun z : X => z ∈ SheafOfModules.supp F) (hpoint y).symm)

/-- The comparison map of fibres of a pullback square is an isomorphism when `g` is an
isomorphism on the residue field at `t`. -/
private theorem isIso_restrictedFiberMap_baseChange (f : X ⟶ S) [LocallyOfFiniteType f]
    (g : S' ⟶ S) (t : S') (hres : IsIso (g.residueFieldMap t)) :
    IsIso (restrictedFiberMap f (pullback.snd f g) (pullback.fst f g) g pullback.condition t) :=
  @AlgebraicGeometry.isIso_baseChangeFiberMap _ _ _ f g t hres

/-- The multiplicity of the base-changed module at a point of a fibre of `X ×_S S' ⟶ S'` is the
multiplicity of the original module at the image point in the corresponding fibre of `f`, the
map of fibres being an isomorphism when the base morphism is an isomorphism on the residue field
at the point in question. -/
theorem sheafMultiplicity_pullback_fiberι_baseChange (f : X ⟶ S) [LocallyOfFiniteType f]
    (g : S' ⟶ S) (F : X.Modules) (t : S') (hres : IsIso (g.residueFieldMap t))
    (x : (pullback.snd f g).fiber t) :
    sheafMultiplicity ((Scheme.Modules.pullback ((pullback.snd f g).fiberι t)).obj
          ((Scheme.Modules.pullback (pullback.fst f g)).obj F)) x =
      sheafMultiplicity ((Scheme.Modules.pullback (f.fiberι (g t))).obj F)
        (restrictedFiberMap f (pullback.snd f g) (pullback.fst f g) g pullback.condition t x) := by
  have := isIso_restrictedFiberMap_baseChange f g t hres
  have e : (Scheme.Modules.pullback ((pullback.snd f g).fiberι t)).obj
        ((Scheme.Modules.pullback (pullback.fst f g)).obj F) ≅
      (Scheme.Modules.pullback (restrictedFiberMap f (pullback.snd f g) (pullback.fst f g) g
          pullback.condition t)).obj ((Scheme.Modules.pullback (f.fiberι (g t))).obj F) :=
    (Scheme.Modules.pullbackComp ((pullback.snd f g).fiberι t) (pullback.fst f g)).app F ≪≫
      (Scheme.Modules.pullbackCongr (restrictedFiberMap_fiberι f (pullback.snd f g)
          (pullback.fst f g) g pullback.condition t).symm).app F ≪≫
        ((Scheme.Modules.pullbackComp (restrictedFiberMap f (pullback.snd f g)
          (pullback.fst f g) g pullback.condition t) (f.fiberι (g t))).app F).symm
  exact (sheafMultiplicity_eq_of_iso e x).trans
    (sheafMultiplicity_pullback_of_isOpenImmersion _ _ x)

/-! ### Base change of the associated family -/

/-- **Stacks Project, Tag 0H4R.** The dimension bound on the fibrewise supports of a
quasi-coherent module of finite type survives base change along a morphism that induces an
isomorphism on every residue field: the support on the fibre over `t` is the inverse image of the
support on the fibre over `g t` along an isomorphism of fibres. -/
@[stacks 0H4R "module_base_change, residue-field-isomorphism case: dimension bound"]
theorem supportDimension_le_of_baseChange (f : X ⟶ S) [LocallyOfFiniteType f] (g : S' ⟶ S)
    (hres : ∀ t : S', IsIso (g.residueFieldMap t)) (F : X.Modules) [F.IsFiniteType] (r : ℕ)
    (hdim : ∀ s : S, topologicalKrullDim
      (SheafOfModules.supp ((Scheme.Modules.pullback (f.fiberι s)).obj F)) ≤ (r : WithBot ℕ∞)) :
    ∀ t : S', topologicalKrullDim
      (SheafOfModules.supp ((Scheme.Modules.pullback ((pullback.snd f g).fiberι t)).obj
        ((Scheme.Modules.pullback (pullback.fst f g)).obj F))) ≤ (r : WithBot ℕ∞) := by
  intro t
  have := isIso_restrictedFiberMap_baseChange f g t (hres t)
  rw [supp_pullback_fiberι_baseChange f g F t]
  refine le_trans ?_ (hdim (g t))
  exact ((((restrictedFiberMap f (pullback.snd f g) (pullback.fst f g) g
    pullback.condition t).isEmbedding.isInducing).comp
      Topology.IsInducing.subtypeVal).codRestrict fun y => y.2).topologicalKrullDim_le

/-- **Stacks Project, Tag 0H4R.** Base change along a morphism `g` that induces an isomorphism on
every residue field carries the family of cycles associated to a quasi-coherent module of finite
type to the family associated to the base-changed module. Coefficientwise: the base change
preserves the multiplicity of the module and the relative dimension of a point of the fibre, and
the support of the base-changed module on a fibre over `t` is the inverse image of the support of
the original one on the fibre over `g t`. -/
@[stacks 0H4R "module_base_change, residue-field-isomorphism case"]
theorem familyAssociatedToModule_baseChange (f : X ⟶ S) [LocallyOfFiniteType f] (g : S' ⟶ S)
    (hres : ∀ t : S', IsIso (g.residueFieldMap t)) (F : X.Modules) [F.IsFiniteType]
    [F.IsQuasicoherent] (r : ℕ)
    (hdim : ∀ s : S, topologicalKrullDim
      (SheafOfModules.supp ((Scheme.Modules.pullback (f.fiberι s)).obj F)) ≤ (r : WithBot ℕ∞)) :
    baseChangeFamilyOfResidueIso f g hres r (familyAssociatedToModule f F r hdim) =
      familyAssociatedToModule (pullback.snd f g)
        ((Scheme.Modules.pullback (pullback.fst f g)).obj F) r
        (supportDimension_le_of_baseChange f g hres F r hdim) := by
  classical
  funext t
  apply Subtype.ext
  ext x
  have := isIso_restrictedFiberMap_baseChange f g t (hres t)
  have hresIso : IsIso (Spec.map (g.residueFieldMap t)) :=
    have : IsIso (g.residueFieldMap t) := hres t
    inferInstance
  let m := restrictedFiberMap f (pullback.snd f g) (pullback.fst f g) g pullback.condition t
  let sX := (pullback.snd f g).fiberToSpecResidueField t
  let sY := f.fiberToSpecResidueField (g t)
  let Cx := fieldChowSituation (S'.residueField t)
  let Cy := fieldChowSituation (S.residueField (g t))
  let M := (Scheme.Modules.pullback (f.fiberι (g t))).obj F
  let N := (Scheme.Modules.pullback ((pullback.snd f g).fiberι t)).obj
    ((Scheme.Modules.pullback (pullback.fst f g)).obj F)
  let eRes := asIso (Spec.map (g.residueFieldMap t))
  have hδ : ∀ z : (pullback.snd f g).fiber t,
      Cx.dimensionFunction (sX z) = Cy.dimensionFunction (eRes.hom (sX z)) := by
    intro z
    rw [fieldChowSituation_dimensionFunction_eq_zero,
      fieldChowSituation_dimensionFunction_eq_zero]
  have hdimRel := relativeDimension_eq_of_openImmersion_over_iso m sX sY eRes
    (restrictedFiberMap_comp_fiberToSpecResidueField f (pullback.snd f g) (pullback.fst f g) g
      pullback.condition t).symm Cx.dimensionFunction Cy.dimensionFunction hδ x
  have hsupp : x ∈ SheafOfModules.supp N ↔ m x ∈ SheafOfModules.supp M := by
    rw [supp_pullback_fiberι_baseChange f g F t]
    exact Set.mem_preimage
  have hmult : sheafMultiplicity N x = sheafMultiplicity M (m x) :=
    sheafMultiplicity_pullback_fiberι_baseChange f g F t (hres t) x
  calc
    (baseChangeFamilyOfResidueIso f g hres r (familyAssociatedToModule f F r hdim) t :
          AlgebraicCycle ((pullback.snd f g).fiber t) ℤ) x =
        (familyAssociatedToModule f F r hdim (g t) :
          AlgebraicCycle (f.fiber (g t)) ℤ) (m x) :=
      baseChangeFamilyOfResidueIso_apply f g hres r (familyAssociatedToModule f F r hdim) t x
    _ = (cycleAssociatedToCoherentSheaf Cy sY M (r : ℤ)
        (fiberModule_schemeDeltaDimension_le f F r hdim (g t))).1 (m x) :=
      congrArg (fun c : CycleGroup Cy sY (r : ℤ) => c.1 (m x))
        (familyAssociatedToModule_apply f F r hdim (g t))
    _ = (cycleAssociatedToCoherentSheaf Cx sX N (r : ℤ)
        (fiberModule_schemeDeltaDimension_le (pullback.snd f g)
          ((Scheme.Modules.pullback (pullback.fst f g)).obj F) r
          (supportDimension_le_of_baseChange f g hres F r hdim) t)).1 x := by
      rw [cycleAssociatedToCoherentSheaf_apply, cycleAssociatedToCoherentSheaf_apply]
      simp [hsupp, hmult, hdimRel]
    _ = (familyAssociatedToModule (pullback.snd f g)
          ((Scheme.Modules.pullback (pullback.fst f g)).obj F) r
          (supportDimension_le_of_baseChange f g hres F r hdim) t :
          AlgebraicCycle ((pullback.snd f g).fiber t) ℤ) x :=
      (congrArg (fun c : CycleGroup Cx sX (r : ℤ) => c.1 x)
        (familyAssociatedToModule_apply (pullback.snd f g)
          ((Scheme.Modules.pullback (pullback.fst f g)).obj F) r
          (supportDimension_le_of_baseChange f g hres F r hdim) t)).symm

end Stacks.Chow

end
