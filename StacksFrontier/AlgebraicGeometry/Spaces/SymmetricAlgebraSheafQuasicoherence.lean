module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafifiedDirectSum
public import StacksFrontier.AlgebraicGeometry.Spaces.AlgebraSheafUnderlyingModule
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDirectSums
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentImpliesCartesian
public import StacksFrontier.AlgebraicGeometry.Spaces.SymmetricAlgebraSheafMap

/-!
# Quasi-coherence of the symmetric algebra sheaf on an algebraic space

`AlgebraicGeometry.Space.symmetricAlgebraSheaf` sends a sheaf of modules `ℱ` on the small étale
site of an algebraic space `W` to the sheaf of commutative `𝒪_W`-algebras `Sym(ℱ)`. This file
reduces its quasi-coherence, Stacks 01CL for `Sym`, to the quasi-coherence of the individual
pieces `Symⁿ(ℱ)` in the degrees `n ≥ 0`: the module underlying `Sym(ℱ)` is the coproduct
`∐_{n ∈ ℤ} Symⁿ(ℱ)`, the pieces in negative degrees are zero, and on the small étale site of an
algebraic space a coproduct of quasi-coherent modules, over an index type of any universe, is
quasi-coherent, since there quasi-coherence is equivalent to the base change criterion of
Stacks 03DX(2).

## Main definitions

* `AlgebraicGeometry.Space.symRingUnit`: the sheafification unit of the ungraded realization of
  `Sym(ℱ)`, as a morphism of presheaves of rings into the sections of its algebra sheaf.
* `AlgebraicGeometry.Space.symDirectSumIsoUnderlyingModule`: the module underlying the algebra
  sheaf `Sym(ℱ)` is the sheafification of the objectwise direct sum of the homogeneous pieces of
  the graded `Sym(ℱ)`.
* `AlgebraicGeometry.Space.symCoprodIsoUnderlyingModule`: the module underlying the algebra
  sheaf `Sym(ℱ)` is the coproduct `∐_{n ∈ ℤ} Symⁿ(ℱ)` of the homogeneous pieces.

## Main results

* `AlgebraicGeometry.Space.isQuasicoherentOnSite_of_isZero`: a zero `𝒪_X`-module is
  quasi-coherent.
* `AlgebraicGeometry.Space.isZero_symmetricAlgebra_piece_of_neg` and
  `isQuasicoherentOnSite_symmetricAlgebra_piece_of_neg`: the pieces of `Sym(ℱ)` in negative
  degrees are zero, hence quasi-coherent.
* `AlgebraicGeometry.Space.isQuasicoherentOnSite_coprod_symmetricAlgebra_piece`: the coproduct
  `∐_{n ∈ ℤ} Symⁿ(ℱ)` is quasi-coherent once every piece of non-negative degree is.
* `AlgebraicGeometry.Space.isQuasicoherent_symmetricAlgebraSheaf_of_pieces`: the algebra sheaf
  `Sym(ℱ)` is quasi-coherent once every piece `Symⁿ(ℱ)`, `n ≥ 0`, is.

## Implementation notes

### The coproduct half of Stacks 01CL on the small étale site

Stacks 01CL opens by warning that an infinite direct sum of quasi-coherent modules need not be
quasi-coherent, and the scheme-level development accordingly asks for one covering family
presenting every homogeneous piece at once
(`SheafOfModules.TensorExteriorSymmetricAlgebras.isQuasicoherent_symmetricAlgebraSheaf`).  On the
small étale site of an algebraic space that uniformity is not needed, because the direct-sum
clause of Stacks 03M1 is available there outright: quasi-coherence is *equivalent* to the base
change criterion, by
`AlgebraicGeometry.Space.SmallEtale.isQuasicoherentOnSite_iff_isCartesianOnAffineCharts`, which
is Stacks 03DX(2) and carries no hypothesis, and cartesianness on affine charts passes to a
coproduct over an index type of any universe.  That is
`AlgebraicGeometry.Space.isQuasicoherentOnSite_sigma_of_h03DX`, and no refinement of coverings
is involved, so the `ℤ`-indexed coproduct is as good as a finite one.

### The identification of the underlying module

This is assembled from `Stacks.GradedAlgebra.directSumIsoUnderlyingModule`, which presents the
module underlying an ungraded realization as the sheafification of the objectwise direct sum of
the homogeneous pieces, and `Stacks.sheafifyDirectSumIso`, which identifies that sheafification
with the coproduct.  The ungraded realization of a graded algebra *is* the sheafification of its
total presheaf (`Stacks.GradedAlgebra.totalSheaf`), and the commutative lift of
`AlgebraicGeometry.Space.gradedAlgebraSheaf` keeps the carrier, so
`AlgebraicGeometry.Space.AlgebraSheaf.ringSheafOfSite (symmetricAlgebraSheaf B S hS W F)` is the
ungraded sheaf of `AlgebraicGeometry.Space.symmetricAlgebra` on the nose and the comparison
morphism `AlgebraicGeometry.Space.symRingUnit` is the sheafification unit itself; its
compatibility with the structure maps is therefore `rfl`.  Correspondingly the local injectivity
and local surjectivity of that unit are read off
`CategoryTheory.GrothendieckTopology.W_toSheafify` at `RingCat` directly, with no detour through
`CommRingCat`.

## References

* [Stacks Project, Tag 01CK](https://stacks.math.columbia.edu/tag/01CK)
* [Stacks Project, Tag 01CL](https://stacks.math.columbia.edu/tag/01CL)
* [Stacks Project, Tag 01CJ](https://stacks.math.columbia.edu/tag/01CJ)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 03M1](https://stacks.math.columbia.edu/tag/03M1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

/-! ### A zero module is quasi-coherent -/

section Zero

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hX : IsAlgebraicSpace B S hS X)

/-- A zero `𝒪_X`-module on the small étale site of an algebraic space is quasi-coherent.

A zero object is the coproduct of the empty family, and a coproduct of quasi-coherent modules is
quasi-coherent there by
`AlgebraicGeometry.Space.isQuasicoherentOnSite_of_isColimit_cofan_of_h03DX`, whose hypothesis is
Stacks 03DX(2) and holds with nothing assumed.  The index type of that statement is free, so the
empty family in the universe of the site is allowed. -/
theorem isQuasicoherentOnSite_of_isZero {M : Modules.{u, u} B S hS X hX} (h : IsZero M) :
    M.IsQuasicoherentOnSite :=
  isQuasicoherentOnSite_of_isColimit_cofan_of_h03DX B S hS X hX
    (SmallEtale.isQuasicoherentOnSite_iff_isCartesianOnAffineCharts B S hS X hX)
    (Cofan.mk (f := fun _ : PEmpty.{u + 1} => M) M fun i => i.elim)
    (Cofan.IsColimit.mk _ (fun s => h.to_ s.pt) (fun _ i => i.elim)
      fun _ _ _ => h.eq_of_src _ _)
    fun i => i.elim

end Zero

/-! ### The negative-degree pieces of `Sym(ℱ)` -/

section Sym

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (W : AlgebraicSpaces B S hS) (F : SheafOfModules.{u} (structureRingSheaf B S hS W))

/-- Coproducts of presheaves of modules on the small étale site, supplied directly: instance
search for them times out. -/
private instance (priority := high) hasColimitsOfShape_discrete_symAlgSheafQcoh (J : Type) :
    HasColimitsOfShape (Discrete J) (PresheafOfModules.{u} (structureRingSheaf B S hS W).obj) :=
  PresheafOfModules.hasColimitsOfShape _ _

private instance (priority := high) hasCoproduct_piece_symAlgSheafQcoh :
    HasCoproduct fun n : ℤ => (symmetricAlgebra B S hS W F).piece n :=
  inferInstance

/-- `Sym(ℱ)` has no nonzero piece in a negative degree.  This is
`PresheafOfModules.isZero_symmetricAlgebraSheafify_piece` instantiated at the small étale site of
an algebraic space. -/
theorem isZero_symmetricAlgebra_piece_of_neg (n : ℤ) (hn : n < 0) :
    IsZero ((symmetricAlgebra B S hS W F).piece n) :=
  @PresheafOfModules.isZero_symmetricAlgebraSheafify_piece.{u, u + 1, u, u} _ _
    (SmallEtale.topology B S hS W.1) (structureSheaf B S hS W.1 W.2).obj
    (structureRingSheaf B S hS W) (𝟙 _) (isLocallyInjective_id_structureRingSheaf B S hS W)
    (isLocallySurjective_id_structureRingSheaf B S hS W)
    (wEqualsLocallyBijective_smallEtale B S hS W) (hasWeakSheafify_smallEtale B S hS W) F.val
    n hn

/-- The pieces of `Sym(ℱ)` in negative degrees are quasi-coherent, being zero. -/
theorem isQuasicoherentOnSite_symmetricAlgebra_piece_of_neg (n : ℤ) (hn : n < 0) :
    ((symmetricAlgebra B S hS W F).piece n).IsQuasicoherentOnSite :=
  isQuasicoherentOnSite_of_isZero B S hS W.1 W.2
    (isZero_symmetricAlgebra_piece_of_neg B S hS W F n hn)

/-- Quasi-coherence of every piece of `Sym(ℱ)` in a non-negative degree gives it in every
integer degree: the remaining degrees are negative, where the piece is zero. -/
theorem isQuasicoherentOnSite_symmetricAlgebra_piece
    (h : ∀ k : ℕ, ((symmetricAlgebra B S hS W F).piece (k : ℤ)).IsQuasicoherentOnSite)
    (n : ℤ) : ((symmetricAlgebra B S hS W F).piece n).IsQuasicoherentOnSite := by
  rcases lt_or_ge n 0 with hn | hn
  · exact isQuasicoherentOnSite_symmetricAlgebra_piece_of_neg B S hS W F n hn
  · obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hn
    exact h k

/-! ### The module underlying `Sym(ℱ)` -/

/-- The sheafification unit of the ungraded realization of `Sym(ℱ)`, read as a morphism of
presheaves of rings into the sections of the algebra sheaf `Sym(ℱ)`.  The commutative lift of
`AlgebraicGeometry.Space.gradedAlgebraSheaf` keeps the carrier, so the target is the ungraded
sheaf of the graded `Sym(ℱ)` on the nose. -/
def symRingUnit :
    (symmetricAlgebra B S hS W F).toPresheafGradedAlgebra.totalPresheaf ⟶
      (AlgebraSheaf.ringSheafOfSite (symmetricAlgebraSheaf B S hS W F)).obj :=
  Stacks.GradedAlgebra.toTotalSheaf (symmetricAlgebra B S hS W F).toPresheafGradedAlgebra
    (SmallEtale.topology B S hS W.1)

/-- The sheafification unit of the ungraded realization of `Sym(ℱ)` is compatible with the
structure map of the graded algebra and the structure morphism of its algebra sheaf. -/
theorem structureHom_comp_symRingUnit :
    (symmetricAlgebra B S hS W F).toPresheafGradedAlgebra.structureHom ≫
        symRingUnit B S hS W F =
      (AlgebraSheaf.structureMapOfSite (symmetricAlgebraSheaf B S hS W F)).hom :=
  rfl

/-- The sheafification unit of the ungraded realization of `Sym(ℱ)` is a local equivalence. -/
private theorem w_symRingUnit :
    (SmallEtale.topology B S hS W.1).W (symRingUnit B S hS W F) :=
  (SmallEtale.topology B S hS W.1).W_toSheafify
    (symmetricAlgebra B S hS W F).toPresheafGradedAlgebra.totalPresheaf

/-- The sheafification unit of the ungraded realization of `Sym(ℱ)` is locally injective: on the
small étale site the local equivalences of presheaves of rings are the locally bijective
morphisms. -/
theorem isLocallyInjective_symRingUnit :
    Presheaf.IsLocallyInjective (SmallEtale.topology B S hS W.1) (symRingUnit B S hS W F) :=
  GrothendieckTopology.W.isLocallyInjective (CA := fun R : RingCat.{u} => ToType R)
    (w_symRingUnit B S hS W F)

/-- The sheafification unit of the ungraded realization of `Sym(ℱ)` is locally surjective. -/
theorem isLocallySurjective_symRingUnit :
    Presheaf.IsLocallySurjective (SmallEtale.topology B S hS W.1) (symRingUnit B S hS W F) :=
  GrothendieckTopology.W.isLocallySurjective (CA := fun R : RingCat.{u} => ToType R)
    (w_symRingUnit B S hS W F)

/-- The module underlying the algebra sheaf `Sym(ℱ)` is the sheafification of the objectwise
direct sum of the homogeneous pieces of the graded `Sym(ℱ)`. -/
def symDirectSumIsoUnderlyingModule :
    ((PresheafOfModules.sheafification (𝟙 (structureRingSheaf B S hS W).obj) :
          PresheafOfModules.{u} (structureRingSheaf B S hS W).obj ⥤
            SheafOfModules.{u} (structureRingSheaf B S hS W)).obj
        (Stacks.directSum fun n : ℤ => ((symmetricAlgebra B S hS W F).piece n).val)) ≅
      AlgebraSheaf.underlyingModule (symmetricAlgebraSheaf B S hS W F) :=
  Stacks.GradedAlgebra.directSumIsoUnderlyingModule
      (symmetricAlgebra B S hS W F).toPresheafGradedAlgebra
      (AlgebraSheaf.structureMapOfSite (symmetricAlgebraSheaf B S hS W F))
      (symRingUnit B S hS W F) (structureHom_comp_symRingUnit B S hS W F)
      (isLocallyInjective_symRingUnit B S hS W F)
      (isLocallySurjective_symRingUnit B S hS W F) ≪≫
    eqToIso (AlgebraSheaf.underlyingModule_eq_restrictScalars
      (symmetricAlgebraSheaf B S hS W F)).symm

set_option synthInstance.maxHeartbeats 400000 in
-- instance synthesis for the coproduct `∐` of the pieces of `Sym(ℱ)` over the étale site is slow
/-- The module underlying the algebra sheaf `Sym(ℱ)` is the coproduct `∐_{n ∈ ℤ} Symⁿ(ℱ)` of the
homogeneous pieces of the graded `Sym(ℱ)`. -/
def symCoprodIsoUnderlyingModule :
    (∐ fun n : ℤ => (symmetricAlgebra B S hS W F).piece n) ≅
      AlgebraSheaf.underlyingModule (symmetricAlgebraSheaf B S hS W F) :=
  (Stacks.sheafifyDirectSumIso fun n : ℤ => (symmetricAlgebra B S hS W F).piece n).symm ≪≫
    symDirectSumIsoUnderlyingModule B S hS W F

/-! ### Quasi-coherence -/

set_option synthInstance.maxHeartbeats 400000 in
-- instance synthesis for the coproduct `∐` of the pieces of `Sym(ℱ)` over the étale site is slow
/-- The coproduct `∐_{n ∈ ℤ} Symⁿ(ℱ)` is quasi-coherent once every piece of `Sym(ℱ)` in a
non-negative degree is.

No uniformity of the covering families across the degrees is needed, unlike at the scheme level:
on the small étale site of an algebraic space quasi-coherence is equivalent to the base change
criterion, by Stacks 03DX(2), and that criterion passes to a coproduct over an index type of any
universe.  See the implementation notes. -/
theorem isQuasicoherentOnSite_coprod_symmetricAlgebra_piece
    (h : ∀ k : ℕ, ((symmetricAlgebra B S hS W F).piece (k : ℤ)).IsQuasicoherentOnSite) :
    (∐ fun n : ℤ => (symmetricAlgebra B S hS W F).piece n).IsQuasicoherentOnSite :=
  isQuasicoherentOnSite_sigma_of_h03DX B S hS W.1 W.2
    (SmallEtale.isQuasicoherentOnSite_iff_isCartesianOnAffineCharts B S hS W.1 W.2) _
    (isQuasicoherentOnSite_symmetricAlgebra_piece B S hS W F h)

/-- The algebra sheaf `Sym(ℱ)` on an algebraic space is quasi-coherent once every piece
`Symⁿ(ℱ)`, `n ≥ 0`, is.

This is the reduction of Stacks 01CL for `Sym` at the small étale site of an algebraic space to
its per-degree statement: the module underlying `Sym(ℱ)` is the coproduct of the pieces, the
pieces in negative degrees are zero, and the coproduct of quasi-coherent modules is
quasi-coherent there with nothing assumed. -/
theorem isQuasicoherent_symmetricAlgebraSheaf_of_pieces
    (h : ∀ k : ℕ, ((symmetricAlgebra B S hS W F).piece (k : ℤ)).IsQuasicoherentOnSite) :
    AlgebraSheaf.IsQuasicoherent (symmetricAlgebraSheaf B S hS W F) :=
  SheafOfModules.IsQuasicoherentOnSite.of_iso (symCoprodIsoUnderlyingModule B S hS W F)
    (isQuasicoherentOnSite_coprod_symmetricAlgebra_piece B S hS W F h)

end Sym

end AlgebraicGeometry.Space

end
