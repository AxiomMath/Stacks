module

public import StacksFrontier.AlgebraicGeometry.AffineQcohPushforward.Colimits
public import StacksFrontier.AlgebraicGeometry.AmpleTwistAcyclicity.FreeTensorTwist
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedModuleAbelian
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorCoproductRight

/-!
# The homogeneous pieces of a degreewise direct sum of graded modules

Each homogeneous piece of `SheafOfModules.GradedModule.directSum` is a coproduct of the
corresponding pieces of the summands — that is
`SheafOfModules.GradedModule.directSumPieceIsColimit`, which exhibits it as the point of a
colimit cofan rather than as `∐` itself, the direct sum being formed by sheafification. This
file reads the two properties the middle term of the dévissage of part (2) of
[Stacks, Tag 0897] has to have off that cofan.

Quasi-coherence needs nothing but the cofan: quasi-coherence of modules on a scheme is stable
under colimits of every shape
(`Stacks.AlgebraicGeometry.QuasicoherentColimits.isQuasicoherent_of_isColimit`), and a cofan is
a cocone over a discrete category.

Acyclicity of the twists needs the index type to be *finite*, and it needs the coproduct to be
moved across the twist. Tensoring in the left variable commutes with colimits
(`Stacks.SheafOfModules.Strict.preservesColimit_sheafTensorFlip`), so the twist of the piece is
again the point of a colimit cocone over a discrete diagram, whose objects are the twists of the
pieces of the summands; and an additive functor kills the point of such a cocone when it kills
its objects. Finiteness enters only in that last step, for the reason given at
`Stacks.AlgebraicGeometry.AmpleTwistAcyclicity.isZero_obj_sigma_of_isZero`: the unrestricted
statement would need cohomology to commute with arbitrary direct sums, which carries the
quasi-compactness hypotheses of [Stacks, Tag 01FF].

## Main results

* `Stacks.Coherent.isQuasicoherent_directSum_piece` — **the pieces of a degreewise direct sum of
  graded modules with quasi-coherent pieces are quasi-coherent.**
* `Stacks.Coherent.isZero_obj_of_isColimit_discrete` — **an additive functor kills the point of a
  colimit cocone over a finite discrete diagram whose objects it kills.**
* `Stacks.Coherent.isZero_Hgroup_directSum_piece_tensorModules` — **a twist of a piece of a
  finite degreewise direct sum is acyclic as soon as the corresponding twists of the summands
  are.**

## Implementation notes

`Stacks.AlgebraicGeometry.AmpleTwistAcyclicity.isZero_obj_sigma_of_isZero` is the same statement
as `Stacks.Coherent.isZero_obj_of_isColimit_discrete` with the colimit cocone specialised to `∐`.
The generalisation is what makes it usable here: the image of the cofan under the twisting
functor is a cocone over the *composite* diagram, and identifying it with a coproduct would need
a comparison isomorphism — which exhausts the heartbeat budget,
`AlgebraicGeometry.Scheme.Modules` being a `def` whose category instance does not agree with that
of `SheafOfModules` at reducible transparency.

The twisting functor is `(Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf).flip.obj T`, whose
value on an `𝒪_X`-module is `Stacks.RelativeVeryAmple.tensorModules X - T` definitionally; this
is the same ascription `Stacks.AlgebraicGeometry.AmpleTwistAcyclicity.freeTensorModulesIso`
makes, and it is what lets a colimit-preservation statement about the functor be read as a
statement about the tensor product sheaf.

## References

* [Stacks Project, Tag 0897](https://stacks.math.columbia.edu/tag/0897)
* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
* [Stacks Project, Tag 01E3](https://stacks.math.columbia.edu/tag/01E3)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.RelativeVeryAmple (tensorModules)

universe u

namespace Stacks.Coherent

variable {X : Scheme.{u}} {P : SheafOfModules.GradedAlgebra.{u, u} X.ringCatSheaf} {K : Type u}
  (M : K → SheafOfModules.GradedModule.{u, u, u} P)

/-- **The homogeneous pieces of a degreewise direct sum of graded modules with quasi-coherent
pieces are quasi-coherent.** The piece is the point of the colimit cofan
`SheafOfModules.GradedModule.directSumPieceIsColimit`, and quasi-coherence on a scheme is stable
under colimits. -/
public theorem isQuasicoherent_directSum_piece
    (h : ∀ (k : K) (n : ℤ), ((M k).piece n).IsQuasicoherent) (n : ℤ) :
    ((SheafOfModules.GradedModule.directSum M).piece n).IsQuasicoherent :=
  Stacks.AlgebraicGeometry.QuasicoherentColimits.isQuasicoherent_of_isColimit
    (D := Discrete.functor fun k => (M k).piece n) (fun k => h k.as n)
    (SheafOfModules.GradedModule.directSumPieceIsColimit M n)

/-- **An additive functor kills the point of a colimit cocone over a finite discrete diagram
whose objects it kills.**

A colimit cocone over a discrete diagram splits: the projections `pᵢ` obtained from the
universal property satisfy `∑ᵢ pᵢ ≫ ιᵢ = 𝟙`, an identity of morphisms out of the colimit. An
additive functor carries it to `∑ᵢ G(pᵢ) ≫ G(ιᵢ) = 𝟙`, and each summand factors through a zero
object; so the identity of the image is zero.

This is `Stacks.AlgebraicGeometry.AmpleTwistAcyclicity.isZero_obj_sigma_of_isZero` with the
coproduct replaced by an arbitrary colimit cocone, which is what makes it applicable to the image
of a cofan under a colimit-preserving functor: that image is a cocone over the *composite*
diagram, and identifying it with a coproduct would need a comparison isomorphism the argument
does not use. Nothing is required of `G` beyond additivity — in particular no preservation of
colimits. -/
public theorem isZero_obj_of_isColimit_discrete {C : Type*} [Category C] [Preadditive C]
    {D : Type*} [Category D] [Preadditive D] {ι : Type*} [Finite ι] {F : Discrete ι ⥤ C}
    {c : Cocone F} (hc : IsColimit c) (G : C ⥤ D) [G.Additive]
    (h : ∀ i : Discrete ι, IsZero (G.obj (F.obj i))) :
    IsZero (G.obj c.pt) := by
  classical
  have := Fintype.ofFinite ι
  have : Fintype (Discrete ι) := Fintype.ofEquiv ι discreteEquiv.symm
  set p : ∀ i : Discrete ι, c.pt ⟶ F.obj i := fun i => hc.desc
    { pt := F.obj i
      ι := Discrete.natTrans fun j => if hj : j = i then eqToHom (congrArg F.obj hj) else 0 }
    with hp
  have hfac : ∀ j i : Discrete ι, c.ι.app j ≫ p i =
      if hj : j = i then eqToHom (congrArg F.obj hj) else 0 := fun j i =>
    hc.fac _ j
  have htot : (∑ i : Discrete ι, p i ≫ c.ι.app i) = 𝟙 c.pt := by
    refine hc.hom_ext fun j => ?_
    have hL : c.ι.app j ≫ (∑ i : Discrete ι, p i ≫ c.ι.app i) = c.ι.app j := by
      rw [Preadditive.comp_sum]
      refine (Finset.sum_eq_single j (fun i _ hi => ?_) (fun hj => ?_)).trans ?_
      · rw [← Category.assoc, hfac, dite_eq_right (Ne.symm hi), zero_comp]
      · exact absurd (Finset.mem_univ j) hj
      · rw [← Category.assoc, hfac, dite_eq_left rfl]
        simp
    exact hL.trans (Category.comp_id _).symm
  refine (IsZero.iff_id_eq_zero (G.obj c.pt)).2 ?_
  rw [← G.map_id, ← htot, G.map_sum]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [G.map_comp, (h i).eq_of_tgt (G.map (p i)) 0, zero_comp]

/-- **A twist of a homogeneous piece of a finite degreewise direct sum is acyclic as soon as the
corresponding twists of the summands are.**

The twisting functor `- ⊗ T` preserves the colimit cofan exhibiting the piece as a coproduct
(`Stacks.SheafOfModules.Strict.preservesColimit_sheafTensorFlip`), so the twist of the piece is
the point of a colimit cocone whose objects are the twists of the pieces of the summands; and
cohomology over an open is additive
(`Stacks.Cohomology.DirectSum.additive_Hfunctor`), so
`Stacks.Coherent.isZero_obj_of_isColimit_discrete` applies. No comparison with `∐` intervenes.

Finiteness of the index type is what the additivity argument needs; the unrestricted statement
would need cohomology to commute with arbitrary direct sums, which carries the
quasi-compactness hypotheses of [Stacks, Tag 01FF]. -/
public theorem isZero_Hgroup_directSum_piece_tensorModules [Finite K] (T : X.Modules) (p : ℕ)
    (n : ℤ) (h : ∀ k, IsZero (Hgroup X.ringCatSheaf ⊤ p (tensorModules X ((M k).piece n) T))) :
    IsZero (Hgroup X.ringCatSheaf ⊤ p
      (tensorModules X ((SheafOfModules.GradedModule.directSum M).piece n) T)) := by
  have hP : PreservesColimit (Discrete.functor fun k => (M k).piece n)
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf).flip.obj T) :=
    Stacks.SheafOfModules.Strict.preservesColimit_sheafTensorFlip X.sheaf
      (Discrete.functor fun k => (M k).piece n) T
  exact @isZero_obj_of_isColimit_discrete _ _ _ _ _ _ _ _ _ _
    (hP.preserves (SheafOfModules.GradedModule.directSumPieceIsColimit M n)).some
    (Hfunctor X.ringCatSheaf ⊤ p) (Stacks.Cohomology.DirectSum.additive_Hfunctor X.ringCatSheaf ⊤ p)
    fun k => h k.as

end Stacks.Coherent

end
