module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocallyFreeOfIntRank
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatColimits
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatRetract
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.UnitEndomorphisms
public import StacksFrontier.CategoryTheory.Preadditive.RetractsOfFiniteFree
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Slice.FlatLocality
public import StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.ConeOfAMorphism
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TorAmplitude.FlatRepresentative

/-!
# Finite free, finite locally free and retract-of-free sheaves of modules are flat

Let `(C, O)` be a ringed site, with the universes of its objects, of its morphisms and of the
sections of its structure sheaf independent. A free `O`-module is flat, a retract of a finite free
`O`-module is flat, and a sheaf of modules which is locally free of finite rank is flat.

## Main results

* `Stacks.SheafOfModules.isFlat_of_isRetractOfFiniteFree`: retracts of finite free modules
  are flat.
* `Stacks.SheafOfModules.isFlat_free_of_anyIndex`: a free module on any set is flat.
* `Stacks.SheafOfModules.isFlat_of_isLocallyFreeData` and
  `Stacks.SheafOfModules.isFlat_of_isFiniteLocallyFreeOfIntRank`: a sheaf of modules with locally
  free local generators indexed by finite sets is flat.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u v w

namespace Stacks.SheafOfModules

attribute [local instance] Stacks.hasSheafCompose_forget₂_commRingCat

variable {Y : RingedSite.{u, v, w}}
  [HasSheafify Y.J AddCommGrpCat.{w}]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- **A free `O`-module is flat.** -/
theorem isFlat_free_of_anyIndex (I : Type w) :
    AlgebraicGeometry.SheafOfModules.IsFlat.{v, u, w, w} (O := Y.O)
      (_root_.SheafOfModules.free (R := Stacks.SheafOfModules.Tensor.ringSheaf Y.O) I) :=
  FlatColimits.isFlat_coproduct
    (fun _ : I => _root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
    fun _ => DerivedTensorProduct.isFlat_unit

/-- **A retract of a finite biproduct of copies of `O` is flat.** -/
theorem isFlat_of_isRetractOfFiniteFree (F : RingedSite.Modules.{u, v, w} Y)
    (hF : IsRetractOfFiniteFree
      (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) F) :
    AlgebraicGeometry.SheafOfModules.IsFlat.{v, u, w, w} (O := Y.O) F := by
  obtain ⟨n, i, r, hir⟩ := hF
  exact FlatRetract.isFlat_of_retract Y.O i r hir <| FlatRetract.isFlat_of_iso Y.O
    ((Sigma.reindex Equiv.ulift.symm _).symm ≪≫ (biproduct.isoCoproduct _).symm)
    (isFlat_free_of_anyIndex (ULift.{w} (Fin n)))

variable [∀ U : Y.C, HasSheafify (Y.J.over U) AddCommGrpCat.{w}]
  [∀ U : Y.C, (Y.J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]

attribute [local instance] sliceHasSheafify sliceWEqualsLocallyBijective

/-- **A sheaf of modules which is locally free of finite rank is flat.** -/
theorem isFlat_of_isLocallyFreeData (M : RingedSite.Modules.{u, v, w} Y)
    (q : _root_.SheafOfModules.LocalGeneratorsData.{u} M) [q.IsLocallyFreeData]
    (hq : ∀ i, Finite (q.generators i).I) :
    AlgebraicGeometry.SheafOfModules.IsFlat.{v, u, w, w} (O := Y.O) M := by
  refine isFlat_of_coversTop q.coversTop M fun i => ?_
  have := hq i
  exact FlatRetract.isFlat_of_iso (Y.over (q.X i)).O
    (@asIso _ _ _ _ (q.generators i).π ((inferInstance : q.IsLocallyFreeData).isIso i))
    (isFlat_free_of_anyIndex (Y := Y.over (q.X i)) (q.generators i).I)

/-- **A sheaf of modules which is finite locally free of an integer rank is flat.** -/
theorem isFlat_of_isFiniteLocallyFreeOfIntRank (M : RingedSite.Modules.{u, v, w} Y) {r : ℤ}
    (hM : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfIntRank.{w, v, u} M r) :
    AlgebraicGeometry.SheafOfModules.IsFlat.{v, u, w, w} (O := Y.O) M := by
  obtain ⟨q, hq, hn⟩ := hM
  exact isFlat_of_isLocallyFreeData M q fun i => by
    obtain ⟨n, -, ⟨e⟩⟩ := hn i
    exact Finite.of_equiv _ e.symm

end Stacks.SheafOfModules

end
