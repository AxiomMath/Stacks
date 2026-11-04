module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocallyFreePowers
public import StacksFrontier.AlgebraicGeometry.Modules.FiniteLocallyFree
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The symmetric powers of a finite locally free sheaf of modules are finite locally free

Let `(C, J)` be a site, `O♯` a sheaf of commutative rings on it and `F` a sheaf of modules over
the underlying sheaf of rings which is *finite* locally free, meaning that it admits a
trivialising covering whose index types are finite. Then each `Symⁿ F` is again finite locally
free. No rank is assumed: the index types may have different cardinalities over different
members of the covering.

## Main results

* `Stacks.SheafOfModules.isFiniteLocallyFree_symmetricPower`: the degree-`n` symmetric power of
  a finite locally free sheaf of modules is finite locally free.

## References

* [Stacks Project, Tag 01C6](https://stacks.math.columbia.edu/tag/01C6)
* [Stacks Project, Tag 01CK](https://stacks.math.columbia.edu/tag/01CK)
-/

@[expose] public section

open CategoryTheory

universe v u₁ u

namespace Stacks.SheafOfModules

variable {C : Type u₁} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  {Osharp : Sheaf J CommRingCat.{u}}
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify J AddCommGrpCat.{u}]
  [∀ U : C, (J.over U).HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ U : C, HasWeakSheafify (J.over U) AddCommGrpCat.{u}]
  {F : _root_.SheafOfModules.{u} (Sheaf.toRingCat J Osharp)}

/-- The degree-`n` symmetric power of a finite locally free sheaf of modules is finite locally
free. -/
@[ega "II 1.7.7" "special case"]
theorem isFiniteLocallyFree_symmetricPower
    (A : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras J F) (n : ℕ)
    (hF : Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, v, u₁} F) :
    Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, v, u₁} (A.symmetricPower n) := by
  classical
  obtain ⟨q, hq, hft⟩ := hF.exists_isFiniteLocallyFreeData
  have E : ∀ i : q.I, (A.symmetricPower n).over (q.X i) ≅
      _root_.SheafOfModules.free (R := (Sheaf.toRingCat J Osharp).over (q.X i))
        ↥{d : (q.generators i).I →₀ ℕ | d.degree = n} := fun i =>
    have : IsIso (q.generators i).π := hq.isIso i
    symmetricPowerOverFreeIsoOfIsoFree A (q.X i) n ((q.generators i).I)
      (asIso (q.generators i).π).symm
  refine ⟨⟨q.I, q.X, q.coversTop, fun i =>
      (_root_.SheafOfModules.free.generatingSections
        ↥{d : (q.generators i).I →₀ ℕ | d.degree = n}).ofEpi (E i).inv⟩, ?_, ?_⟩
  · constructor
    intro i
    show IsIso ((_root_.SheafOfModules.free.generatingSections
      ↥{d : (q.generators i).I →₀ ℕ | d.degree = n}).ofEpi (E i).inv).π
    have h0 : IsIso (_root_.SheafOfModules.free.generatingSections
        (R := (Sheaf.toRingCat J Osharp).over (q.X i))
        ↥{d : (q.generators i).I →₀ ℕ | d.degree = n}).π := by
      rw [_root_.SheafOfModules.free.generatingSections_π]
      exact IsIso.id _
    rw [_root_.SheafOfModules.GeneratingSections.ofEpi_π]
    exact @IsIso.comp_isIso _ _ _ _ _ _ _ h0 inferInstance
  · constructor
    intro i
    have : Finite ((q.generators i).I) := (hft.isFiniteType i).finite
    exact ⟨(inferInstance : Finite ↥{d : (q.generators i).I →₀ ℕ | d.degree = n})⟩

end Stacks.SheafOfModules

end
