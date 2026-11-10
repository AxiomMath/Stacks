module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SlicePowerRestriction
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FreePowerArbitraryIndex
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FreePowerSheafify
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.AlgebraBundleStalk
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SymmetricAlgebraConstruction.Scheme
public import StacksFrontier.Topology.Sheaves.Modules.LocallyFree
public import Mathlib.AlgebraicGeometry.Modules.Sheaf

/-!
# Symmetric powers of a finite locally free module

Every homogeneous piece of a symmetric algebra of a finite locally free sheaf of modules is
finite locally free: a covering trivialising `F` with finite index types `γ i` trivialises
`Symⁿ F` with index types the degree-`n` multidegrees in `γ i`.

## Main results

* `AlgebraicGeometry.SheafOfModules.isFiniteLocallyFree_piece_of_isSymmetricAlgebra`
* `AlgebraicGeometry.SheafOfModules.isFiniteLocallyFree_symmetricAlgebra_piece`: the case of
  `Sym(F)` on a scheme.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u₁ u

namespace AlgebraicGeometry.SheafOfModules

section Site

variable {C : Type u₁} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  {Osharp : Sheaf J CommRingCat.{u}}
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify J AddCommGrpCat.{u}]
  [∀ U : C, (J.over U).HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ U : C, HasWeakSheafify (J.over U) AddCommGrpCat.{u}]
  {F : _root_.SheafOfModules.{u} (Sheaf.toRingCat J Osharp)}

/-- **Every homogeneous piece of a symmetric algebra of a finite locally free sheaf of modules is
finite locally free.** -/
theorem isFiniteLocallyFree_piece_of_isSymmetricAlgebra
    (A : _root_.SheafOfModules.GradedAlgebra.{u, u} (Sheaf.toRingCat J Osharp))
    (gen : F ⟶ A.piece 1) (hA : _root_.SheafOfModules.GradedAlgebra.IsSymmetricAlgebra A gen)
    (n : ℕ) [hF : IsFiniteLocallyFree.{u, v, u₁} F] :
    IsFiniteLocallyFree.{u, v, u₁} (A.piece (n : ℤ)) := by
  classical
  obtain ⟨q, hfree, hfin⟩ := hF.exists_isFiniteLocallyFreeData
  have E : ∀ i : q.I, (A.piece (n : ℤ)).over (q.X i) ≅
      _root_.SheafOfModules.free (R := (Sheaf.toRingCat J Osharp).over (q.X i))
        {d : (q.generators i).I →₀ ℕ | d.degree = n} := fun i =>
    have : IsIso (q.generators i).π := hfree.isIso i
    let B := _root_.SheafOfModules.algebras (Osharp := Osharp.over (q.X i)) (J.over (q.X i))
      (show _root_.SheafOfModules.{u} (Sheaf.toRingCat (J.over (q.X i)) (Osharp.over (q.X i)))
        from F.over (q.X i))
    (Stacks.SheafOfModules.symmetricPowerOverIso F (q.X i) n A gen hA B.symmetric
        B.symmetricGenerator B.symmetric_isSymmetricAlgebra).trans
      (Stacks.SheafOfModules.symmetricPowerFreeIsoOfIsoAnyIndex (J.over (q.X i))
        ((q.generators i).I) n B (asIso (q.generators i).π).symm)
  have hfinite : ∀ i : q.I, Finite {d : (q.generators i).I →₀ ℕ | d.degree = n} := fun i =>
    have : Finite ((q.generators i).I) := (hfin.isFiniteType i).finite
    inferInstance
  refine ⟨⟨⟨q.I, q.X, q.coversTop, fun i =>
      (_root_.SheafOfModules.free.generatingSections
        {d : (q.generators i).I →₀ ℕ | d.degree = n}).ofEpi (E i).inv⟩, ?_, ?_⟩⟩
  · constructor
    intro i
    change IsIso ((_root_.SheafOfModules.free.generatingSections
      {d : (q.generators i).I →₀ ℕ | d.degree = n}).ofEpi (E i).inv).π
    have h0 : IsIso (_root_.SheafOfModules.free.generatingSections
        (R := (Sheaf.toRingCat J Osharp).over (q.X i))
        {d : (q.generators i).I →₀ ℕ | d.degree = n}).π := by
      rw [_root_.SheafOfModules.free.generatingSections_π]
      exact IsIso.id _
    rw [_root_.SheafOfModules.GeneratingSections.ofEpi_π]
    exact @IsIso.comp_isIso _ _ _ _ _ _ _ h0 inferInstance
  · constructor
    intro i
    exact ⟨hfinite i⟩

end Site

/-- **Every homogeneous piece of `Sym(F)` of a finite locally free module on a scheme is finite
locally free.** -/
theorem isFiniteLocallyFree_symmetricAlgebra_piece {X : Scheme.{u}} (F : X.Modules)
    [hF : IsFiniteLocallyFree.{u, u, u} F] (n : ℕ) :
    IsFiniteLocallyFree.{u, u, u} ((Scheme.Modules.symmetricAlgebra X F).piece (n : ℤ)) :=
  have : IsFiniteLocallyFree.{u, u, u}
      (R := Sheaf.toRingCat (Opens.grothendieckTopology X) X.sheaf) F := hF
  isFiniteLocallyFree_piece_of_isSymmetricAlgebra (J := Opens.grothendieckTopology X)
    (Osharp := X.sheaf) (Scheme.Modules.symmetricAlgebra X F)
    (Scheme.Modules.symmetricAlgebraGen X F)
    (Scheme.Modules.isSymmetricAlgebra_symmetricAlgebra X F) n

end AlgebraicGeometry.SheafOfModules
