module

public import StacksFrontier.AlgebraicGeometry.Quot.SquareZeroTowerLimit
public import StacksFrontier.AlgebraicGeometry.Quot.SquareZeroTowerProblem
public import StacksFrontier.AlgebraicGeometry.Spaces.ThickenedBasePushoutQcqs

/-!
# The thickened base maps to the limit of the tower of structure sheaves

In the situation of `AlgebraicGeometry.ProperFlatFibre.towerProblem` — the extension problem over
`f : X₀ ⟶ Y₀ ⊂ Y = Spec(lim Rₙ)`, `i : Y₀ ⟶ Y` — every `Xₙ` maps to `Y` through
`Xₙ ⟶ Yₙ ⟶ Y`, and `aₙ : X₀ ⟶ Xₙ` followed by it is `f ≫ i`. The inverse images of the structure
maps give compatible maps `(f ≫ i)⁻¹𝒪_Y ⟶ aₙ⁻¹𝒪_{Xₙ} = Aₙ` (Stacks 03G8), hence a map to
`𝒜 = lim Aₙ`; it lies over the reductions to `𝒪_{X₀}`. Through `(f ≫ i)⁻¹𝒪_Y ≅ f⁻¹i⁻¹𝒪_Y`, this is
the map from the inverse image of the thickened base of the problem to `𝒜` that makes `𝒜` a
candidate solution, as in the body of the proof of [Stacks Project, Tag 0D3X].

## Main definitions

* `AlgebraicGeometry.ProperFlatFibre.towerLimitBaseCone`: the cone `(f ≫ i)⁻¹𝒪_Y ⟶ Aₙ`.
* `AlgebraicGeometry.ProperFlatFibre.towerProblemLimitBaseMap`: the map from the inverse image of
  the thickened base of `towerProblem` to `𝒜 = lim Aₙ`.

## Main results

* `AlgebraicGeometry.ProperFlatFibre.towerProblemLimitBaseMap_reduction`: it lies over the
  reductions.

## References

* [Stacks Project, Tag 0D3X](https://stacks.math.columbia.edu/tag/0D3X)
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {W X Y : AlgebraicSpaces B S hS}

/-- The maps `u'⁻¹𝒪_Y ⟶ u⁻¹𝒪_X` for `u ≫ h = u'` depend only on `h`, not on the proof. -/
theorem inverseImageStructureSheafMapOfEq_congr {u' : W ⟶ Y} (u : W ⟶ X) {h h' : X ⟶ Y}
    (hh : h = h') (e : u ≫ h = u') (e' : u ≫ h' = u') :
    inverseImageStructureSheafMapOfEq B S hS u h e =
      inverseImageStructureSheafMapOfEq B S hS u h' e' := by
  subst hh
  rfl

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.ProperFlatFibre

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  (ξ : ℕ ⥤ CartesianProperFlatSpaces B S hS)
  (c : Cocone (ξ ⋙ cartesianProperFlatProjection B S hS))

/-- The morphism `Xₙ ⟶ Yₙ ⟶ Y` to the vertex of the cocone of the bases. -/
abbrev towerLimitStructureMap (n : ℕ) : towerSpace ξ n ⟶ schemeSpace c.pt :=
  towerStructureMap ξ n ≫ schemeSpaceMap (c.ι.app n)

/-- The maps `Xₙ ⟶ Y` are compatible with the transition morphisms. -/
theorem towerTransition_comp_towerLimitStructureMap {m n : ℕ} (k : m ⟶ n) :
    towerTransition ξ k ≫ towerLimitStructureMap ξ c n = towerLimitStructureMap ξ c m := by
  rw [← Category.assoc, (isPullback_towerTransition ξ k).w, Category.assoc]
  refine congrArg (towerStructureMap ξ m ≫ ·) ?_
  exact ((schemeSpaceFunctor B S hS).map_comp _ _).symm.trans
    (congrArg (schemeSpaceFunctor B S hS).map (c.w k))

/-- `aₙ : X₀ ⟶ Xₙ` followed by `Xₙ ⟶ Y` is `X₀ ⟶ Y₀ ⟶ Y`. -/
theorem towerInclusion_comp_towerLimitStructureMap (n : ℕ) :
    towerInclusion ξ n ≫ towerLimitStructureMap ξ c n =
      towerStructureMap ξ 0 ≫ schemeSpaceMap (c.ι.app 0) :=
  towerTransition_comp_towerLimitStructureMap ξ c _

/-- The map `(f ≫ i)⁻¹𝒪_Y ⟶ aₙ⁻¹𝒪_{Xₙ} = Aₙ`. -/
def towerLimitBaseMapApp (n : ℕ) :
    Space.inverseImageStructureSheaf B S hS (towerStructureMap ξ 0 ≫ schemeSpaceMap (c.ι.app 0)) ⟶
      (towerRingSystem ξ).obj (op n) :=
  Space.inverseImageStructureSheafMapOfEq B S hS (towerInclusion ξ n) (towerLimitStructureMap ξ c n)
    (towerInclusion_comp_towerLimitStructureMap ξ c n)

/-- The maps `(f ≫ i)⁻¹𝒪_Y ⟶ Aₙ` are compatible with the transition maps `Aₙ₊₁ ⟶ Aₙ`. -/
theorem towerLimitBaseMapApp_naturality (n : ℕ) :
    towerLimitBaseMapApp ξ c (n + 1) ≫ (towerRingSystem ξ).map (homOfLE (Nat.le_succ n)).op =
      towerLimitBaseMapApp ξ c n :=
  (congrArg (towerLimitBaseMapApp ξ c (n + 1) ≫ ·) (towerRingSystem_map_succ ξ n)).trans
    ((Space.inverseImageStructureSheafMapOfEq_comp B S hS (towerInclusion ξ n)
      (towerTransition ξ (homOfLE (Nat.le_succ n))) (towerLimitStructureMap ξ c (n + 1))
      (towerInclusion_comp_towerTransition ξ n)
      (towerInclusion_comp_towerLimitStructureMap ξ c (n + 1))).trans
    (Space.inverseImageStructureSheafMapOfEq_congr B S hS _
      (towerTransition_comp_towerLimitStructureMap ξ c _) _ _))

/-- **The cone `(f ≫ i)⁻¹𝒪_Y ⟶ Aₙ`** over the tower of structure sheaves on `X₀`. -/
def towerLimitBaseCone : Cone (towerRingSystem ξ) where
  pt := Space.inverseImageStructureSheaf B S hS (towerStructureMap ξ 0 ≫ schemeSpaceMap (c.ι.app 0))
  π := NatTrans.ofOpSequence (fun n => towerLimitBaseMapApp ξ c n) fun n =>
    (Category.id_comp _).trans (towerLimitBaseMapApp_naturality ξ c n).symm

/-- The induced map `(f ≫ i)⁻¹𝒪_Y ⟶ 𝒜 = lim Aₙ`. -/
abbrev towerLimitBaseLift :
    Space.inverseImageStructureSheaf B S hS (towerStructureMap ξ 0 ≫ schemeSpaceMap (c.ι.app 0)) ⟶
      towerRingLimit ξ :=
  limit.lift (towerRingSystem ξ) (towerLimitBaseCone ξ c)

/-- The map `(f ≫ i)⁻¹𝒪_Y ⟶ 𝒜` followed by the reduction `𝒜 ⟶ 𝒪_{X₀}` is `(f ≫ i)^♯`. -/
@[reassoc]
theorem towerLimitBaseLift_comp_towerRingLimitReduction :
    towerLimitBaseLift ξ c ≫ towerRingLimitReduction ξ =
      Space.structureSharpInverseImage B S hS
        (towerStructureMap ξ 0 ≫ schemeSpaceMap (c.ι.app 0)) := by
  refine (limit.lift_π_assoc (towerLimitBaseCone ξ c) (op 0) _).trans ?_
  exact Space.inverseImageStructureSheafMapOfEq_comp_structureSharpInverseImage B S hS _ _
    (towerInclusion_comp_towerLimitStructureMap ξ c 0)

variable {Λ : Type u} [CommRing Λ] {R : ℕᵒᵖ ⥤ CommAlgCat.{u} Λ}
  (hsurj : ∀ {i j : ℕᵒᵖ} (f : i ⟶ j), Function.Surjective (R.map f).hom)
  (hsq : ∀ {i j : ℕᵒᵖ} (f : i ⟶ j), RingHom.ker (R.map f).hom.toRingHom ^ 2 = ⊥)
  (e : ∀ n : ℕ, (BigFppfOver.toScheme B S hS).obj (towerBase ξ n) ≅
    Spec (.of (R.obj (.op n))))
  (cR : Cone R) (hcR : IsLimit cR)
  (eLimit : (BigFppfOver.toScheme B S hS).obj c.pt ≅ Spec (.of cR.pt))
  (hc : ∀ n : ℕ, (BigFppfOver.toScheme B S hS).map (c.ι.app n) ≫ eLimit.hom =
    (e n).hom ≫ Scheme.Spec.map (CommRingCat.ofHom (cR.π.app (.op n)).hom.toRingHom).op)

/-- **The map from the inverse image of the thickened base of `towerProblem` to `𝒜 = lim Aₙ`**:
`f⁻¹i⁻¹𝒪_Y ≅ (f ≫ i)⁻¹𝒪_Y ⟶ 𝒜`. -/
def towerProblemLimitBaseMap :
    (Stacks.Sheaves.ToposPushforward.inverseImageCommRingFunctor
        (towerProblem ξ hsurj hsq e cR hcR c eLimit hc).f.toToposHom).obj
      (towerProblem ξ hsurj hsq e cR hcR c eLimit hc).baseExtension ⟶ towerRingLimit ξ :=
  (Space.thickenedBaseIso B S hS (towerStructureMap ξ 0) (schemeSpaceMap (c.ι.app 0))
      (towerProblemBaseIso ξ hsurj hsq e cR hcR c eLimit hc)).inv ≫
    towerLimitBaseLift ξ c

/-- **The map to `𝒜` lies over the reductions**: followed by `𝒜 ⟶ 𝒪_{X₀}` it is the inverse image
of the base reduction followed by `f^♯`. -/
theorem towerProblemLimitBaseMap_reduction :
    towerProblemLimitBaseMap ξ c hsurj hsq e cR hcR eLimit hc ≫ towerRingLimitReduction ξ =
      (Stacks.Sheaves.ToposPushforward.inverseImageCommRingFunctor
          (towerProblem ξ hsurj hsq e cR hcR c eLimit hc).f.toToposHom).map
          (towerProblem ξ hsurj hsq e cR hcR c eLimit hc).baseReduction ≫
        (towerProblem ξ hsurj hsq e cR hcR c eLimit hc).f.fSharpInverseImage := by
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (_ ≫ ·) (towerLimitBaseLift_comp_towerRingLimitReduction ξ c)).trans ?_
  exact (Iso.inv_comp_eq _).2 (Space.thickenedBaseIso_hom_comp B S hS (towerStructureMap ξ 0)
    (schemeSpaceMap (c.ι.app 0)) (towerProblemBaseIso ξ hsurj hsq e cR hcR c eLimit hc) _
    (towerProblemBaseIso_hom_comp_fSharpInverseImage ξ hsurj hsq e cR hcR c eLimit hc)).symm

end AlgebraicGeometry.ProperFlatFibre

end
