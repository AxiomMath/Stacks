module

public import StacksFrontier.AlgebraicGeometry.Blowup.Basic
public import StacksFrontier.AlgebraicGeometry.ProjTrivialization.Basic
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocallyTrivialInvertible.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The twists on `Proj` of a ring generated in degree one

Let `𝒮` be a nonnegatively graded ring which is generated in degree one over its degree-zero
part. Then the standard opens `D₊(f)` for `f` homogeneous of degree one cover `Proj 𝒮`, each
of them is affine, and every twisting sheaf `𝒪(n)` is trivial on each of them. Consequently
every `𝒪(n)` is finite locally free of rank one on the whole of `Proj 𝒮`.

The Rees algebra of an ideal `I ⊆ R` is generated in degree one, so all of this applies to the
affine blowup `Stacks.Blowup.blowUpSpec I = Proj (Stacks.Blowup.reesGrading I)`.

## Main results

* `Stacks.AlgebraicGeometry.ProjDegreeOne.iSup_basicOpen_degreeOne_eq_top`: the standard opens
  of the degree-one elements cover `Proj 𝒮`.
* `Stacks.AlgebraicGeometry.ProjDegreeOne.coversTop_basicOpen_degreeOne`: the same, as a
  covering of the terminal object of the site of opens.
* `Stacks.AlgebraicGeometry.ProjDegreeOne.isAffineOpen_basicOpen_degreeOne`: each of those
  standard opens is affine.
* `Stacks.AlgebraicGeometry.ProjDegreeOne.isLocallyTrivial_twistingSheaf`: every twisting sheaf
  `𝒪(n)` is trivial on each member of that covering.
* `Stacks.AlgebraicGeometry.ProjDegreeOne.isFiniteLocallyFreeOfRank_one_twistingSheaf`: every
  twisting sheaf `𝒪(n)` is finite locally free of rank one.
* `Stacks.AlgebraicGeometry.ProjDegreeOne.isInvertible_twistingSheaf`: every twisting sheaf
  `𝒪(n)` is invertible.
* `Stacks.Blowup.iSup_basicOpen_reesGrading_one_eq_top`,
  `Stacks.Blowup.isFiniteLocallyFreeOfRank_one_blowUpTwist` and
  `Stacks.Blowup.isInvertible_blowUpTwist`: the same statements for the affine blowup.

## Implementation notes

The covering statement is Mathlib's `AlgebraicGeometry.Proj.iSup_basicOpen_eq_top'`, which asks
for the degree-one elements to generate `𝒮` as an algebra over `𝒮 0`. What the Rees algebra
comes with (`Stacks.Blowup.adjoin_reesGrading_one_eq_top`) is generation over the *base ring*
`R`, which is a copy of `reesGrading I 0` but not that submodule on the nose; moving between the
two bases is `Stacks.Algebra.adjoin_eq_top_of_isScalarTower`. Routing through
`Subalgebra.restrictScalars` instead makes the kernel time out on the
`Algebra (reesGrading I 0) (reesAlgebra I)` instance.

The local trivializations are those of
`Stacks.AlgebraicGeometry.ProjTrivialization.twistingSheafOverBasicOpenIsoUnit`, which
trivializes `𝒪(n d)` on `D₊(f)` for `f` of degree `d`. At `d = 1` the exponent `n * (1 : ℕ)`
has to be rewritten to `n`; it is not syntactically `n`, and the sheaf appears in the type of
the isomorphism, so the rewriting is done with `▸` on the isomorphism rather than inside a
proof.

## References

* [Stacks Project, Tag 01MS](https://stacks.math.columbia.edu/tag/01MS)
* [Stacks Project, Tag 01MU](https://stacks.math.columbia.edu/tag/01MU)
* [Stacks Project, Tag 0B8M](https://stacks.math.columbia.edu/tag/0B8M)
* [Stacks Project, Tag 02NS](https://stacks.math.columbia.edu/tag/02NS)
-/


@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite
open AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.AlgebraicGeometry.ProjTrivialization (projRingSheaf
  twistingSheafOverBasicOpenIsoUnit)

universe u w

namespace Stacks.Algebra

/-- Generation as an algebra passes up a scalar tower: if `s` generates `A` over `R` and the
structure map `R → A` factors through `B`, then `s` generates `A` over `B` as well. -/
public theorem adjoin_eq_top_of_isScalarTower {R B A : Type*} [CommRing R] [CommRing B]
    [CommRing A] [Algebra R B] [Algebra B A] [Algebra R A] [IsScalarTower R B A] (s : Set A)
    (h : Algebra.adjoin R s = ⊤) : Algebra.adjoin B s = ⊤ := by
  refine top_unique fun x _ ↦ ?_
  have key : ∀ y ∈ Algebra.adjoin R s, y ∈ Algebra.adjoin B s := by
    intro y hy
    induction hy using Algebra.adjoin_induction with
    | mem y hy => exact Algebra.subset_adjoin hy
    | algebraMap r =>
        rw [IsScalarTower.algebraMap_apply R B A r]
        exact Subalgebra.algebraMap_mem _ _
    | add y z _ _ hy hz => exact add_mem hy hz
    | mul y z _ _ hy hz => exact mul_mem hy hz
  exact key x (h.ge Algebra.mem_top)

end Stacks.Algebra

namespace Stacks.AlgebraicGeometry.ProjDegreeOne

variable {S : Type u} [CommRing S] {σ : Type w} [SetLike σ S] [AddSubgroupClass σ S]
  (𝒮 : ℕ → σ) [GradedRing 𝒮]

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose
  Stacks.SheafOfModules.TensorSheafification.structureSheaf
attribute [local instance_reducible] ProjectiveSpectrum.top

/-- A homogeneous element of degree one has affine standard open. -/
public theorem isAffineOpen_basicOpen_degreeOne (f : S) (hf : f ∈ 𝒮 1) :
    IsAffineOpen (Proj.basicOpen 𝒮 f) :=
  Proj.isAffineOpen_basicOpen 𝒮 f hf one_pos

/-- **The standard opens of the degree-one elements cover `Proj 𝒮`** when `𝒮` is generated in
degree one over its degree-zero part. -/
public theorem iSup_basicOpen_degreeOne_eq_top
    (h : Algebra.adjoin (𝒮 0) ((𝒮 1 : Set S)) = ⊤) :
    ⨆ f : 𝒮 1, Proj.basicOpen 𝒮 (f : S) = ⊤ := by
  refine Proj.iSup_basicOpen_eq_top' 𝒮 (fun f : 𝒮 1 ↦ (f : S)) (fun f ↦ ⟨1, f.2⟩) ?_
  convert h using 2
  ext x
  simp

/-- The covering of the terminal object of the site of opens of `Proj 𝒮` by the standard opens
of the degree-one elements. -/
public theorem coversTop_basicOpen_degreeOne
    (h : Algebra.adjoin (𝒮 0) ((𝒮 1 : Set S)) = ⊤) :
    (Opens.grothendieckTopology (ProjectiveSpectrum.top 𝒮)).CoversTop
      (fun f : 𝒮 1 ↦ ProjectiveSpectrum.basicOpen 𝒮 (f : S)) :=
  (Opens.coversTop_iff _ _).mpr
    (TopologicalSpace.IsOpenCover.mk (iSup_basicOpen_degreeOne_eq_top 𝒮 h))

/-- The trivialization of `𝒪(n)` on the standard open of a degree-one element: the
trivialization `twistingSheafOverBasicOpenIsoUnit` at `d = 1`, with the exponent `n * (1 : ℕ)`
rewritten to `n`. -/
@[ega "II 3.2.5" "special case"]
public def twistingSheafOverBasicOpenDegreeOneIsoUnit (f : S) (hf : f ∈ 𝒮 1) (n : ℤ) :
    (twistingSheaf 𝒮 n).over (ProjectiveSpectrum.basicOpen 𝒮 f) ≅
      SheafOfModules.unit ((projRingSheaf 𝒮).over (ProjectiveSpectrum.basicOpen 𝒮 f)) :=
  (show n * ((1 : ℕ) : ℤ) = n by simp) ▸ twistingSheafOverBasicOpenIsoUnit 𝒮 hf n

/-- **Every twisting sheaf on `Proj 𝒮` is locally trivial** when `𝒮` is generated in degree one
over its degree-zero part. -/
public theorem isLocallyTrivial_twistingSheaf
    (h : Algebra.adjoin (𝒮 0) ((𝒮 1 : Set S)) = ⊤) (n : ℤ) :
    Stacks.SheafOfModules.Invertible.IsLocallyTrivial (twistingSheaf 𝒮 n) :=
  ⟨↥(𝒮 1), fun f ↦ ProjectiveSpectrum.basicOpen 𝒮 (f : S),
    coversTop_basicOpen_degreeOne 𝒮 h,
    fun f ↦ ⟨twistingSheafOverBasicOpenDegreeOneIsoUnit 𝒮 (f : S) f.2 n⟩⟩

/-- **Every twisting sheaf on `Proj 𝒮` is finite locally free of rank one** when `𝒮` is
generated in degree one over its degree-zero part. -/
public theorem isFiniteLocallyFreeOfRank_one_twistingSheaf
    (h : Algebra.adjoin (𝒮 0) ((𝒮 1 : Set S)) = ⊤) (n : ℤ) :
    Stacks.SheafOfModules.Invertible.IsFiniteLocallyFreeOfRank
      (C := Opens (ProjectiveSpectrum.top 𝒮))
      (J := Opens.grothendieckTopology (ProjectiveSpectrum.top 𝒮))
      (R := projRingSheaf 𝒮) (twistingSheaf 𝒮 n) 1 :=
  have := isLocallyTrivial_twistingSheaf 𝒮 h n
  Stacks.SheafOfModules.Invertible.isFiniteLocallyFreeOfRank_one_of_isLocallyTrivial
    (C := Opens (ProjectiveSpectrum.top 𝒮))
    (J := Opens.grothendieckTopology (ProjectiveSpectrum.top 𝒮))
    (R := projRingSheaf 𝒮) (twistingSheaf 𝒮 n)

/-- **Every twisting sheaf on `Proj 𝒮` is invertible** when `𝒮` is generated in degree one over
its degree-zero part. -/
public theorem isInvertible_twistingSheaf
    (h : Algebra.adjoin (𝒮 0) ((𝒮 1 : Set S)) = ⊤) (n : ℤ) :
    Stacks.SheafOfModules.IsInvertible
      (ProjectiveSpectrum.Proj.structureSheaf 𝒮).obj (projRingSheaf 𝒮).property
      (twistingSheaf 𝒮 n) :=
  Stacks.SheafOfModules.isInvertible_of_coversTop_iso_unit _ _ _
    (coversTop_basicOpen_degreeOne 𝒮 h)
    (fun f ↦ twistingSheafOverBasicOpenDegreeOneIsoUnit 𝒮 (f : S) f.2 n)

end Stacks.AlgebraicGeometry.ProjDegreeOne

namespace Stacks.Blowup

open Stacks.AlgebraicGeometry.ProjDegreeOne

variable {R : Type u} [CommRing R] (I : Ideal R)

/-- The standard opens of the degree-one elements of the Rees algebra cover the affine blowup
`Stacks.Blowup.blowUpSpec I`. -/
public theorem iSup_basicOpen_reesGrading_one_eq_top :
    ⨆ f : reesGrading I 1, Proj.basicOpen (reesGrading I) (f : reesAlgebra I) = ⊤ :=
  iSup_basicOpen_degreeOne_eq_top _ (adjoin_reesGradingZero_reesGrading_one_eq_top I)

/-- **Every twist on the affine blowup is finite locally free of rank one**: every twisting sheaf
`𝒪(n)` on `Stacks.Blowup.blowUpSpec I` is finite locally free of rank one. -/
public theorem isFiniteLocallyFreeOfRank_one_blowUpTwist (n : ℤ) :
    Stacks.SheafOfModules.Invertible.IsFiniteLocallyFreeOfRank
      (C := Opens (ProjectiveSpectrum.top (reesGrading I)))
      (J := Opens.grothendieckTopology (ProjectiveSpectrum.top (reesGrading I)))
      (R := projRingSheaf (reesGrading I)) (twistingSheaf (reesGrading I) n) 1 :=
  isFiniteLocallyFreeOfRank_one_twistingSheaf _ (adjoin_reesGradingZero_reesGrading_one_eq_top I) n

/-- **Every twist on the affine blowup is invertible**: every twisting sheaf `𝒪(n)` on
`Stacks.Blowup.blowUpSpec I` is invertible. -/
public theorem isInvertible_blowUpTwist (n : ℤ) :
    Stacks.SheafOfModules.IsInvertible
      (ProjectiveSpectrum.Proj.structureSheaf (reesGrading I)).obj
      (projRingSheaf (reesGrading I)).property (twistingSheaf (reesGrading I) n) :=
  isInvertible_twistingSheaf _ (adjoin_reesGradingZero_reesGrading_one_eq_top I) n

end Stacks.Blowup

end
