module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.AmpleLocalGeneration.FromExtension
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.Sheaf
public import StacksFrontier.AlgebraicGeometry.InvertibleRankOneScheme.Basic
public import StacksFrontier.AlgebraicGeometry.Perfect.ResolutionProperty
public import StacksFrontier.AlgebraicGeometry.ResolutionsAndBounds.FiniteLocallyFreeBiprod

/-!
# The resolution property from an ample invertible module

A scheme carrying an ample invertible module has the resolution property: every finite type
quasi-coherent module on it is a quotient of a finite locally free module.

## Main results

* `AlgebraicGeometry.SheafOfModules.isFiniteLocallyFree_of_isBilimit_const`: a finite direct sum
  of copies of a finite locally free module is finite locally free.
* `AlgebraicGeometry.hasResolutionProperty_of_isAmple`: a scheme carrying an ample invertible
  module has the resolution property.

## Implementation notes

Biproducts and coproducts are ascribed to `AlgebraicGeometry.Scheme.Modules X` throughout. The
category of sheaves of modules over `X.ringCatSheaf` carries a second, structure-copied category
instance under that name, and `AlgebraicGeometry.SheafOfModules.isFiniteLocallyFree_biprod` is
stated for the first while `AlgebraicGeometry.HasResolutionProperty` is stated for the second;
without the ascription the two spellings of a direct sum are definitionally equal but not
syntactically so, and instance search for the biproduct fails.

## References

* [Stacks Project, Tag 0F87](https://stacks.math.columbia.edu/tag/0F87)
* [Stacks Project, Tag 0F86](https://stacks.math.columbia.edu/tag/0F86)
* [Stacks Project, Tag 01Q3](https://stacks.math.columbia.edu/tag/01Q3)
* [Stacks Project, Tag 01PS](https://stacks.math.columbia.edu/tag/01PS)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry Stacks.Ample

universe u

namespace AlgebraicGeometry.SheafOfModules

variable {X : Scheme.{u}}

/-- A finite family of copies of one module on `X` has a biproduct. -/
noncomputable local instance hasBiproductConst {ι : Type u} [Finite ι] (M : X.Modules) :
    HasBiproduct (fun _ : ι => M) := HasBiproduct.of_hasCoproduct _

/-- Modules on `X` have binary biproducts. -/
noncomputable local instance hasBinaryBiproducts : HasBinaryBiproducts X.Modules :=
  HasBinaryBiproducts.of_hasBinaryProducts

/-- A direct sum of copies of `M` indexed by `Option β` is the direct sum of `M` and the direct
sum of copies of `M` indexed by `β`, the summand at `none` being split off. -/
private noncomputable def biproductOptionIso {β : Type u} [Finite β] (M : X.Modules) :
    (⨁ fun _ : Option β => M : X.Modules) ≅ M ⊞ (⨁ fun _ : β => M : X.Modules) where
  hom := biproduct.desc fun o =>
    o.elim biprod.inl fun b => biproduct.ι (fun _ : β => M) b ≫ biprod.inr
  inv := biprod.desc (biproduct.ι (fun _ : Option β => M) none)
    (biproduct.desc fun b => biproduct.ι (fun _ : Option β => M) (some b))
  hom_inv_id := by
    refine biproduct.hom_ext' _ _ ?_
    rintro (_ | b) <;> simp
  inv_hom_id := biprod.hom_ext' _ _ (by simp) (biproduct.hom_ext' _ _ fun b => by simp)

/-- If a coproduct of copies of a module `M` is finite locally free, so is the biproduct. -/
private theorem isFiniteLocallyFree_biproduct_const {β : Type u} [Finite β] (M : X.Modules)
    (h : IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf)
      (∐ fun _ : β => M : X.Modules)) :
    IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf)
      (⨁ fun _ : β => M : X.Modules) :=
  IsFiniteLocallyFree.of_iso (h := h) (biproduct.isoCoproduct _).symm

/-- If a coproduct of copies of a finite locally free module `M` indexed by
`β` is finite locally free, so is the one indexed by `Option β`. -/
private theorem isFiniteLocallyFree_sigma_const_option {β : Type u} [Finite β] (M : X.Modules)
    [IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) M]
    (h : IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf)
      (∐ fun _ : β => M : X.Modules)) :
    IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf)
      (∐ fun _ : Option β => M : X.Modules) := by
  have := isFiniteLocallyFree_biproduct_const M h
  have h₂ := isFiniteLocallyFree_biprod (X := X) M (⨁ fun _ : β => M : X.Modules)
  have h₃ : IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf)
      (⨁ fun _ : Option β => M : X.Modules) :=
    IsFiniteLocallyFree.of_iso (h := h₂) (biproductOptionIso M).symm
  exact IsFiniteLocallyFree.of_iso (h := h₃) (biproduct.isoCoproduct _)

/-- A coproduct of finitely many copies of a finite locally free module is finite locally
free. -/
private theorem isFiniteLocallyFree_sigma_const (M : X.Modules)
    [IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) M] (ι : Type u) [Finite ι] :
    IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) (∐ fun _ : ι => M : X.Modules) := by
  refine Finite.induction_empty_option
    (P := fun α : Type u => IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf)
      (∐ fun _ : α => M : X.Modules)) ?_ ?_ ?_ ι
  · intro α β e h
    exact IsFiniteLocallyFree.of_iso (h := h) (Sigma.whiskerEquiv e (fun _ => Iso.refl M))
  · have hz : IsZero (∐ fun _ : PEmpty.{u + 1} => M : X.Modules) :=
      (IsZero.iff_id_eq_zero _).mpr (Sigma.hom_ext _ _ (fun b => b.elim))
    exact Stacks.Perfect.BoundedLocallyFreeComplexes.finiteLocallyFree_of_isZero X _ hz
  · intro α _ h
    exact isFiniteLocallyFree_sigma_const_option M h

/-- A finite direct sum of copies of a finite locally free module, presented as the point of a
bilimit bicone, is finite locally free. -/
theorem isFiniteLocallyFree_of_isBilimit_const {ι : Type u} [hfin : Finite ι] (M : X.Modules)
    [hM : IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) M]
    {b : Bicone (fun _ : ι => M)} (hb : b.IsBilimit) :
    IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) b.pt := by
  exact IsFiniteLocallyFree.of_iso
    (h := isFiniteLocallyFree_biproduct_const M (isFiniteLocallyFree_sigma_const M ι))
    (biproduct.uniqueUpToIso (fun _ : ι => M) hb).symm

end AlgebraicGeometry.SheafOfModules

namespace AlgebraicGeometry

/-- A scheme carrying an ample invertible module has the resolution property: every finite type
quasi-coherent module on it is a quotient of a finite locally free module. -/
@[stacks 0F87]
theorem hasResolutionProperty_of_isAmple {X : Scheme.{u}} (L : X.Modules)
    [IsInvertibleModule X L] (hL : IsAmple X L) : HasResolutionProperty X := by
  refine ⟨fun F _ _ => ?_⟩
  obtain ⟨-, hquot⟩ :=
    Stacks.AmpleLocalGeneration.quasiSeparatedSpace_and_exists_epi_biproduct_of_isAmple L hL
  obtain ⟨n, ι, hfin, -, b, hb, p, hp⟩ := hquot F inferInstance inferInstance
  refine ⟨b.pt, ?_, p, hp⟩
  have hrank := Stacks.InvertibleRankOneScheme.isFiniteLocallyFreeOfRank_one_of_isInvertibleModule
    X (tensorPowModule X L (-n))
  have hflf : SheafOfModules.IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf)
      (tensorPowModule X L (-n)) :=
    SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree
      (M := tensorPowModule X L (-n)) (r := 1) (hM := hrank)
  exact SheafOfModules.isFiniteLocallyFree_of_isBilimit_const (hfin := hfin) _ (hM := hflf) hb

end AlgebraicGeometry

end
