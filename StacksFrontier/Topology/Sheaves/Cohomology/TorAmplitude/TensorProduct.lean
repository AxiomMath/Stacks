module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatColimits
public import StacksFrontier.Algebra.Homology.TotalComplexQuasiIso
public import StacksFrontier.CategoryTheory.Sites.Modules.Gate18.FlatTensorProduct
public import StacksFrontier.Topology.Sheaves.Cohomology.TorAmplitude.BoundedFlatRepresentative

/-!
# Tor amplitudes add under the derived tensor product

On a ringed space, if `K` has Tor amplitude in `[a, b]` and `L` has Tor amplitude in `[c, d]`,
then `K ⊗^L_{O_X} L` has Tor amplitude in `[a + c, b + d]`.

## Main results

* `Stacks.Cohomology.TorAmplitude.Tensor.hasTorAmplitude_derivedTensor`: **Tag 09J4.** Tor
  amplitude bounds add.
* `Stacks.Cohomology.TorAmplitude.Tensor.isFlat_total`: every term of the total complex of a
  double complex of flat `O_X`-modules is flat.

## Implementation notes

The direct sums indexing the terms of a total complex are indexed by a subtype of `ℤ × ℤ`,
which lives in `Type 0`, whereas Tag 05NG is stated for an index type in the universe of the
sections; `isFlat_coproduct_of_smallIndex` reindexes along `Equiv.ulift`.

The statement carries no hypothesis `a ≤ b` or `c ≤ d`. For degenerate intervals Tor amplitude
in `[a, b]` says that *every* cohomology sheaf of every derived tensor product vanishes.

## References

* [Stacks Project, Tag 09J4](https://stacks.math.columbia.edu/tag/09J4)
* [Stacks Project, Tag 08CI](https://stacks.math.columbia.edu/tag/08CI)
* [Stacks Project, Tag 0G6Q](https://stacks.math.columbia.edu/tag/0G6Q)
* [Stacks Project, Tag 05NG](https://stacks.math.columbia.edu/tag/05NG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open StrictlyPerfect AlgebraicGeometry.RingedSpace.KFlatDerivedPullback

namespace Stacks.Cohomology.TorAmplitude.Tensor

universe u d

variable {X : RingedSpace.{u, u}}

/-- A direct sum of flat `O_X`-modules indexed by a type in the lowest universe is flat. -/
theorem isFlat_coproduct_of_smallIndex {ι : Type} (F : ι → Modules X) [HasCoproduct F]
    (hF : ∀ i, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := X.sheaf) (F i)) :
    AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := X.sheaf) (∐ F) := by
  let G : ULift.{u} ι → Modules X := fun i => F i.down
  let _ : HasCoproduct G :=
    hasCoproduct_of_equiv_of_iso F G Equiv.ulift (fun _ => Iso.refl _)
  refine BoundedFlatRepresentative.isFlat_of_iso
    (X := X) (M := ∐ G) ?_
    (Stacks.SheafOfModules.FlatColimits.isFlat_coproduct (O := X.sheaf) G
      (fun i => hF i.down))
  exact
    { hom := Sigma.desc fun i => Sigma.ι F i.down
      inv := Sigma.desc fun i => Sigma.ι G (ULift.up i)
      hom_inv_id := by apply colimit.hom_ext; rintro ⟨i⟩; simp [G]
      inv_hom_id := by apply colimit.hom_ext; rintro ⟨i⟩; simp [G] }

/-- Every term of the total complex of a double complex of flat `O_X`-modules is flat. -/
theorem isFlat_total
    (Z : HomologicalComplex₂ (Modules X) (ComplexShape.up ℤ) (ComplexShape.up ℤ))
    [Z.HasTotal (ComplexShape.up ℤ)]
    (hflat : ∀ p q, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u}
      (O := X.sheaf) ((Z.X p).X q))
    (i : ℤ) :
    AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := X.sheaf)
      ((Z.total (ComplexShape.up ℤ)).X i) :=
  isFlat_coproduct_of_smallIndex _ (fun j => hflat j.val.1 j.val.2)

/-- If every `Z^{p, q}` with `p ∉ [a, b]` or `q ∉ [c, d]` is zero, then `Tot(Z)^i` is zero for
`i ∉ [a + c, b + d]`. -/
theorem isZero_total_X_of_support {C : Type*} [Category C] [Preadditive C] [HasZeroObject C]
    (Z : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ))
    [Z.HasTotal (ComplexShape.up ℤ)] (a b c d i : ℤ)
    (hzero : ∀ p q, p ∉ Set.Icc a b ∨ q ∉ Set.Icc c d → IsZero ((Z.X p).X q))
    (hi : i ∉ Set.Icc (a + c) (b + d)) :
    IsZero ((Z.total (ComplexShape.up ℤ)).X i) := by
  refine StacksDraft.TotalComplexQuasiIso.isZero_cofan_pt _
    (Z.toGradedObject.isColimitCofanMapObj _ i) ?_
  rintro ⟨⟨p, q⟩, hpq⟩
  have hpq' : p + q = i := by simpa using hpq
  refine hzero p q (not_and_or.mp fun hh => hi (Set.mem_Icc.mpr ?_))
  obtain ⟨hp, hq⟩ := hh
  obtain ⟨hp₁, hp₂⟩ := Set.mem_Icc.mp hp
  obtain ⟨hq₁, hq₂⟩ := Set.mem_Icc.mp hq
  constructor <;> omega

section Derived

variable [HasDerivedCategory.{d} (OXMod.{u} X)]

-- `HasDerivedCategory` at the spelling of Stacks 06YU: the type is `OXMod X` by `rfl`, but
-- `structureSheafOfRings` is not reducible, so an instance proved at one spelling does not fire
-- at the other.
attribute [local instance] _root_.Stacks.Cohomology.TorAmplitude.hasDerivedCategoryModules

/-- For `a ≤ b` and `c ≤ d`, the derived tensor product of objects of Tor amplitude in `[a, b]` and
`[c, d]` has Tor amplitude in `[a + c, b + d]`. -/
theorem hasTorAmplitude_derivedTensor_of_le (K L : DerivedCategory (Modules X))
    (a b c d : ℤ) (hab : a ≤ b) (hcd : c ≤ d)
    (hK : HasTorAmplitude X K a b)
    (hL : HasTorAmplitude X L c d) :
    HasTorAmplitude X
      (((derTensor X).tensor.obj K).obj L) (a + c) (b + d) := by
  classical
  obtain ⟨A, hAflat, hAzero, ⟨eA⟩⟩ :=
    (BoundedFlatRepresentative.hasTorAmplitude_iff_exists_flat_representative
      K a b hab).mp hK
  obtain ⟨B, hBflat, hBzero, ⟨eB⟩⟩ :=
    (BoundedFlatRepresentative.hasTorAmplitude_iff_exists_flat_representative
      L c d hcd).mp hL
  have hle : ∀ (E : CochainComplex (Modules X) ℤ) (m n : ℤ),
      (∀ i, i ∉ Set.Icc m n → IsZero (E.X i)) → E.IsStrictlyLE n := fun E m n hz => by
    rw [CochainComplex.isStrictlyLE_iff]
    exact fun i hi => hz i (by simp only [Set.mem_Icc]; omega)
  have hAkflat := kFlat_of_boundedAbove_of_flat X A ⟨b, hle A a b hAzero⟩ hAflat
  have hBkflat := kFlat_of_boundedAbove_of_flat X B ⟨d, hle B c d hBzero⟩ hBflat
  let Z : HomologicalComplex₂ (Modules X) (ComplexShape.up ℤ) (ComplexShape.up ℤ) :=
    Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf
      |>.mapBifunctorHomologicalComplex (ComplexShape.up ℤ) (ComplexShape.up ℤ)
      |>.obj A |>.obj B
  have htermflat : ∀ p q, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u}
      (O := X.sheaf) ((Z.X p).X q) := fun p q =>
    Stacks.SheafOfModules.FlatTensor.isFlat_tensor (A.X p) (B.X q) (hAflat p) (hBflat q)
  have hZzero : ∀ p q, p ∉ Set.Icc a b ∨ q ∉ Set.Icc c d → IsZero ((Z.X p).X q) := by
    rintro p q (hp | hq)
    · exact Functor.map_isZero
        ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf).flip.obj (B.X q))
        (hAzero p hp)
    · exact Functor.map_isZero
        ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf).obj (A.X p))
        (hBzero q hq)
  refine (BoundedFlatRepresentative.hasTorAmplitude_iff_exists_flat_representative
      _ (a + c) (b + d) (by omega)).2
    ⟨Z.total (ComplexShape.up ℤ), isFlat_total Z htermflat,
      fun i hi => isZero_total_X_of_support Z a b c d i hZzero hi, ⟨?_⟩⟩
  exact ((derTensor X).comparison A B hAkflat hBkflat).symm ≪≫
    ((derTensor X).tensor.mapIso eA).app
      (DerivedCategory.Q.obj B) ≪≫
    ((derTensor X).tensor.obj K).mapIso eB

/-- Tor amplitude in an empty interval `[a, b]` implies Tor amplitude in every interval. -/
private theorem hasTorAmplitude_of_lt {K : DerivedCategory (Modules X)} {a b : ℤ} (h : b < a)
    (hK : HasTorAmplitude X K a b) (a' b' : ℤ) : HasTorAmplitude X K a' b' :=
  fun G j _ => hK G j fun hj => by simp only [Set.mem_Icc] at hj; omega

/-- If `K` has Tor amplitude in `[a, b]` and `L` has Tor amplitude in `[c, d]`, then
`K ⊗^L_{O_X} L` has Tor amplitude in `[a + c, b + d]`. -/
@[stacks 09J4]
theorem hasTorAmplitude_derivedTensor (K L : DerivedCategory (Modules X)) (a b c d : ℤ)
    (hK : HasTorAmplitude X K a b)
    (hL : HasTorAmplitude X L c d) :
    HasTorAmplitude X
      (((derTensor X).tensor.obj K).obj L) (a + c) (b + d) := by
  by_cases hab : a ≤ b
  · by_cases hcd : c ≤ d
    · exact hasTorAmplitude_derivedTensor_of_le K L a b c d hab hcd hK hL
    · intro F i hi
      exact hasTorAmplitude_derivedTensor_of_le K L a b (i - b - 1) (i - b - 1) hab le_rfl
        hK (hasTorAmplitude_of_lt (by omega) hL _ _) F i (by simp only [Set.mem_Icc]; omega)
  · intro F i hi
    have hK' := hasTorAmplitude_of_lt (by omega) hK
    by_cases hcd : c ≤ d
    · exact hasTorAmplitude_derivedTensor_of_le K L (i - d - 1) (i - d - 1) c d le_rfl hcd
        (hK' _ _) hL F i (by simp only [Set.mem_Icc]; omega)
    · exact hasTorAmplitude_derivedTensor_of_le K L (i + 1) (i + 1) 0 0 le_rfl le_rfl
        (hK' _ _) (hasTorAmplitude_of_lt (by omega) hL _ _) F i
        (by simp only [Set.mem_Icc]; omega)

end Derived

end Stacks.Cohomology.TorAmplitude.Tensor

end
