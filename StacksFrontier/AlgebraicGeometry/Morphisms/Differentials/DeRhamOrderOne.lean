module

public import StacksFrontier.AlgebraicGeometry.DeRham.SchemeComplex
public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.DifferentialOperators
public import StacksFrontier.Topology.Sheaves.Modules.DeRhamDifferentialOperator

/-!
# The de Rham differentials on a scheme are differential operators of order one over the base

Let `a : X ⟶ S` be a morphism of schemes. The differential operators on `X/S` are taken relative
to `AlgebraicGeometry.Scheme.Hom.relativeStructureSheafMap a`, the structural map of *sheaves of
rings* `a⁻¹𝒪_S ⟶ 𝒪_X` obtained by forming the inverse image in `RingCat`, whereas the relative de
Rham complex is built over `AlgebraicGeometry.inverseImageStructureMap a`, the structural map of
*sheaves of commutative rings*. This file compares the two and deduces that each de Rham
differential `d : Ω^p_{X/S} ⟶ Ω^{p+1}_{X/S}` is a differential operator of order at most one
relative to the first of them.

## Main definitions

* `AlgebraicGeometry.Scheme.Hom.inverseImageRingCatComparison`: the canonical map from the
  inverse image of `𝒪_S` formed in `RingCat` to the sheaf of rings underlying the inverse image
  formed in `CommRingCat`.

## Main results

* `DiffOp.isGlobalDiffOpOfOrder_comp_structureMap`: an operator of order at most `k` relative to
  `φ` has order at most `k` relative to `ψ ≫ φ`; linearity over a ring of scalars implies
  linearity over any ring mapping to it.
* `AlgebraicGeometry.Scheme.Hom.inverseImageRingCatComparison_comp`: the comparison composed with
  the structural map of commutative rings is the structural map of rings, so the two structural
  maps have the same scalars.
* `AlgebraicGeometry.Scheme.Hom.deRhamGlobalOp_isGlobalDiffOpOfOrder_one`: **each de Rham
  differential of a morphism of schemes is a differential operator of order at most one on `X/S`.**

## References

* [Stacks Project, Tag 0G3Y](https://stacks.math.columbia.edu/tag/0G3Y)
* [Stacks Project, Tag 0G3Z](https://stacks.math.columbia.edu/tag/0G3Z)
* [Stacks Project, Tag 0G44](https://stacks.math.columbia.edu/tag/0G44)
* [Stacks Project, Tag 0FKQ](https://stacks.math.columbia.edu/tag/0FKQ)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace DiffOp

variable {C : Type*} [Category C] {J : GrothendieckTopology C} {O₀ O₁ O₂ : Sheaf J RingCat}

/-- The scalars of a composite of morphisms of sheaves of rings are the scalars of the second
map applied to the scalars of the first. -/
theorem sectionRingHom_comp (ψ : O₀ ⟶ O₁) (φ : O₁ ⟶ O₂) (Z : Cᵒᵖ) (r : O₀.obj.obj Z) :
    sectionRingHom (ψ ≫ φ) Z r = sectionRingHom φ Z (sectionRingHom ψ Z r) := rfl

/-- **An operator of order at most `k` relative to `φ` has order at most `k` relative to
`ψ ≫ φ`.** -/
theorem isDiffOpOfOrder_comp_structureMap (ψ : O₀ ⟶ O₁) (φ : O₁ ⟶ O₂) :
    ∀ (k : ℕ) {F G : SheafOfModules O₂} {U : C} (D : RawOp F G U),
      IsDiffOpOfOrder φ k D → IsDiffOpOfOrder (ψ ≫ φ) k D
  | 0, _, _, _, _, hD => hD
  | (_ + 1), _, _, _, _, hD =>
      ⟨hD.1, fun Y r s => hD.2.1 Y (sectionRingHom ψ _ r) s,
        fun Y g => isDiffOpOfOrder_comp_structureMap ψ φ _ _ (hD.2.2 Y g)⟩

/-- **A global operator of order at most `k` relative to `φ` has order at most `k` relative to
`ψ ≫ φ`.** -/
theorem isGlobalDiffOpOfOrder_comp_structureMap (ψ : O₀ ⟶ O₁) (φ : O₁ ⟶ O₂) (k : ℕ)
    {F G : SheafOfModules O₂} (D : GlobalOp F G)
    (hD : IsGlobalDiffOpOfOrder φ k D) : IsGlobalDiffOpOfOrder (ψ ≫ φ) k D :=
  fun U => isDiffOpOfOrder_comp_structureMap ψ φ k _ (hD U)

end DiffOp

namespace AlgebraicGeometry.Scheme.Hom

variable {X S : Scheme.{u}} (a : X ⟶ S)

/-- **The structure-sheaf component `a^♯` of a morphism of schemes factors through the unit of
the inverse-image adjunction** followed by the direct image of the structural map
`a⁻¹𝒪_S ⟶ 𝒪_X`. -/
theorem unit_comp_pushforward_inverseImageStructureMap :
    (TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} a.base).unit.app S.sheaf ≫
        (TopCat.Sheaf.pushforward CommRingCat.{u} a.base).map (inverseImageStructureMap a) =
      (⟨a.c⟩ : S.sheaf ⟶ (TopCat.Sheaf.pushforward CommRingCat.{u} a.base).obj X.sheaf) :=
  (Adjunction.homEquiv_unit
      (TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} a.base)
      S.sheaf X.sheaf (inverseImageStructureMap a)).symm.trans
    (Equiv.apply_symm_apply _ _)

/-- Forgetting the commutativity of the rings commutes with the direct image, so it carries the
structural map `a⁻¹𝒪_S ⟶ 𝒪_X` of commutative rings to the one of rings. -/
private theorem forget_pushforward_map_inverseImageStructureMap :
    (sheafCompose (Opens.grothendieckTopology (S : TopCat))
          (forget₂ CommRingCat.{u} RingCat.{u})).map
        ((TopCat.Sheaf.pushforward CommRingCat.{u} a.base).map (inverseImageStructureMap a)) =
      (TopCat.Sheaf.pushforward RingCat.{u} a.base).map
        (SheafOfModules.underlyingRingHom (φ := inverseImageStructureMap a)) := rfl

/-- Forgetting the commutativity of the rings carries `a^♯` to the morphism of sheaves of rings
attached to `a`. -/
private theorem forget_structureSheafHom :
    (sheafCompose (Opens.grothendieckTopology (S : TopCat))
          (forget₂ CommRingCat.{u} RingCat.{u})).map
        (⟨a.c⟩ : S.sheaf ⟶ (TopCat.Sheaf.pushforward CommRingCat.{u} a.base).obj X.sheaf) =
      a.toRingCatSheafHom := rfl

/-- The factorization of `unit_comp_pushforward_inverseImageStructureMap`, read in `RingCat`. -/
private theorem forget_unit_comp_underlyingRingHom :
    (sheafCompose (Opens.grothendieckTopology (S : TopCat))
            (forget₂ CommRingCat.{u} RingCat.{u})).map
          ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} a.base).unit.app S.sheaf) ≫
        (TopCat.Sheaf.pushforward RingCat.{u} a.base).map
          (SheafOfModules.underlyingRingHom (φ := inverseImageStructureMap a)) =
      a.toRingCatSheafHom :=
  (congrArg (fun z => (sheafCompose (Opens.grothendieckTopology (S : TopCat))
          (forget₂ CommRingCat.{u} RingCat.{u})).map
        ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} a.base).unit.app S.sheaf) ≫ z)
      (forget_pushforward_map_inverseImageStructureMap a).symm).trans
    (((sheafCompose (Opens.grothendieckTopology (S : TopCat))
          (forget₂ CommRingCat.{u} RingCat.{u})).map_comp _ _).symm.trans
      ((congrArg (fun z => (sheafCompose (Opens.grothendieckTopology (S : TopCat))
            (forget₂ CommRingCat.{u} RingCat.{u})).map z)
          (unit_comp_pushforward_inverseImageStructureMap a)).trans
        (forget_structureSheafHom a)))

/-- **The comparison `a⁻¹𝒪_S ⟶ a⁻¹𝒪_S`** between the inverse image of the structure sheaf of `S`
formed in `RingCat` and the sheaf of rings underlying the inverse image formed in `CommRingCat`:
the map adjoint to the unit of the `CommRingCat` adjunction, read in `RingCat`. -/
noncomputable def inverseImageRingCatComparison :
    (TopCat.Sheaf.pullback RingCat.{u} a.base).obj S.ringCatSheaf ⟶
      SheafOfModules.underlyingRingSheaf
        ((TopCat.Sheaf.pullback CommRingCat.{u} a.base).obj S.sheaf) :=
  ((TopCat.Sheaf.pullbackPushforwardAdjunction RingCat.{u} a.base).homEquiv
      S.ringCatSheaf
      (SheafOfModules.underlyingRingSheaf
        ((TopCat.Sheaf.pullback CommRingCat.{u} a.base).obj S.sheaf))).symm
    ((sheafCompose (Opens.grothendieckTopology (S : TopCat))
        (forget₂ CommRingCat.{u} RingCat.{u})).map
      ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} a.base).unit.app S.sheaf))

/-- **The two structural maps of a morphism of schemes agree up to the comparison of the two
inverse images.** Hence a local section of `𝒪_X` which is a scalar for
`AlgebraicGeometry.Scheme.Hom.relativeStructureSheafMap` is a scalar for
`AlgebraicGeometry.inverseImageStructureMap`. -/
theorem inverseImageRingCatComparison_comp :
    inverseImageRingCatComparison a ≫
        SheafOfModules.underlyingRingHom (φ := inverseImageStructureMap a) =
      a.relativeStructureSheafMap :=
  (Adjunction.homEquiv_naturality_right_symm
      (TopCat.Sheaf.pullbackPushforwardAdjunction RingCat.{u} a.base)
      (X := S.ringCatSheaf)
      (Y := SheafOfModules.underlyingRingSheaf
        ((TopCat.Sheaf.pullback CommRingCat.{u} a.base).obj S.sheaf))
      (Y' := X.ringCatSheaf)
      ((sheafCompose (Opens.grothendieckTopology (S : TopCat))
          (forget₂ CommRingCat.{u} RingCat.{u})).map
        ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} a.base).unit.app S.sheaf))
      (SheafOfModules.underlyingRingHom (φ := inverseImageStructureMap a))).symm.trans
    (congrArg (fun z =>
        ((TopCat.Sheaf.pullbackPushforwardAdjunction RingCat.{u} a.base).homEquiv
          S.ringCatSheaf X.ringCatSheaf).symm z) (forget_unit_comp_underlyingRingHom a))

/-- **The degree-`p` de Rham differential of a morphism of schemes `a : X ⟶ S` is a differential
operator of order at most one on `X/S`**, that is, relative to the structural map
`a⁻¹𝒪_S ⟶ 𝒪_X` of sheaves of rings. -/
theorem deRhamGlobalOp_isGlobalDiffOpOfOrder_one (p : ℕ) :
    DiffOp.IsGlobalDiffOpOfOrder a.relativeStructureSheafMap 1
      (SheafOfModules.deRhamGlobalOp (deRhamAlgebras a) p) :=
  Eq.mp
    (congrArg (fun φ => DiffOp.IsGlobalDiffOpOfOrder φ 1
        (SheafOfModules.deRhamGlobalOp (deRhamAlgebras a) p))
      (inverseImageRingCatComparison_comp a))
    (DiffOp.isGlobalDiffOpOfOrder_comp_structureMap (inverseImageRingCatComparison a)
      (SheafOfModules.underlyingRingHom (φ := inverseImageStructureMap a)) 1 _
      (SheafOfModules.deRhamDifferentialHom_isGlobalDiffOpOfOrder_one (deRhamAlgebras a) p))

end AlgebraicGeometry.Scheme.Hom

end
