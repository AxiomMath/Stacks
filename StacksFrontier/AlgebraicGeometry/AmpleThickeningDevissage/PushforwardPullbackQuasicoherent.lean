module

public import StacksFrontier.AlgebraicGeometry.AffinePushforward.Basic
public import StacksFrontier.AlgebraicGeometry.AmpleThickeningDevissage.GradedUnitUngraded
public import StacksFrontier.AlgebraicGeometry.Constructions.GradedAlgebraSheafQuasicoherent
public import StacksFrontier.Topology.Sheaves.Modules.Quasicoherent

/-!
# `v_* v^* A` is quasi-coherent, degreewise and as an ungraded algebra sheaf

Let `v : V ⟶ X` be a closed immersion of schemes and `A` a sheaf of graded `𝒪_X`-algebras.  This
file proves that `v_* v^* A` — `Stacks.AmpleThickeningDevissage.pushforwardPullbackGradedAlgebra`,
the right-hand term of the graded square-zero extension
`0 → ⨁_m 𝓘 · A_m → ⨁_m A_m → ⨁_m v_* v^* A_m → 0` of [Stacks Project, Tag 09MS] — vanishes in
the degrees where `A` does and is quasi-coherent in the degrees where `A` is, and draws the
conclusion `Stacks.RelativeSpec.isQuasicoherent_gradedAlgebraSheaf` asks for: its ungraded
realization is a quasi-coherent sheaf of commutative `𝒪_X`-algebras.

Both degreewise facts are one application each of a theorem of the library.  The pieces are
`v_* v^* A_n` **by `rfl`** (`…pushforwardPullbackGradedAlgebra_piece`), the inverse image of a
quasi-coherent module is quasi-coherent ([Stacks Project, Tag 01BG], at the ringed-space spelling
`AlgebraicGeometry.SheafOfModules.modulePullback_isQuasicoherent`), and the direct image along an
affine morphism of a quasi-coherent module is quasi-coherent
(`Stacks.AlgebraicGeometry.AffinePushforward.pushforward_isQuasicoherent_of_isAffineHom`), a closed
immersion being affine.

## Main results

* `Stacks.AmpleThickeningDevissage.isZero_pushforwardPullbackGradedAlgebra_piece`: `v_* v^* A_n`
  is a zero module wherever `A_n` is.
* `Stacks.AmpleThickeningDevissage.isQuasicoherent_pushforwardPullbackGradedAlgebra_piece`:
  **`v_* v^* A_n` is quasi-coherent** whenever `A_n` is, for a closed immersion.
* `Stacks.AmpleThickeningDevissage.isQuasicoherent_coprod_pushforwardPullbackGradedAlgebra`:
  **`⨁_{m ≥ 0} v_* v^* A_m` is quasi-coherent.**
* `Stacks.AmpleThickeningDevissage.isQuasicoherent_gradedAlgebraSheaf_pushforwardPullback`:
  **the ungraded realization of `v_* v^* A` is a quasi-coherent algebra sheaf**, which is the
  hypothesis the right-hand term of the graded square-zero extension owed.
* `Stacks.AmpleThickeningDevissage.isQuasicoherent_gradedAlgebraSheaf_pushforwardPullback_symmetricAlgebra`:
  the same at `A = Sym(L)`, where the degreewise quasi-coherence and the vanishing in negative
  degrees are theorems (`AlgebraicGeometry.Scheme.Modules.isQuasicoherent_symmetricAlgebra_piece`
  and `AlgebraicGeometry.Scheme.Modules.isZero_symmetricAlgebra_piece`) rather than hypotheses.

## Implementation notes

**The two spellings of pushforward and pullback are one.**  The homogeneous pieces of
`pushforwardPullbackGradedAlgebra` are written with
`RingedSpaceModuleAdjunction.pushforwardFunctor` and `…pullbackFunctor` at
`v.toLRSHom.toShHom`, while the quasi-coherence and additivity instances that apply are registered
for Mathlib's `AlgebraicGeometry.Scheme.Modules.pushforward` and `…pullback`.  The two are
definitionally equal (`Stacks.ProjectionFormula.modulePushforward_eq_schemePushforward`,
`Stacks.ProjectionFormula.modulePullback_eq_schemePullback`, both `rfl`), so no transport is
needed; but `AlgebraicGeometry.Scheme.Modules` is a `def` over `SheafOfModules X.ringCatSheaf`
with its own `Category` instance, so the instances registered at one spelling are invisible to
instance search at the other, exactly as recorded in
`StacksFrontier/AlgebraicGeometry/Modules/SubmoduleKernel.lean`.  Everything below therefore names
its instances explicitly and states its conclusion at the `piece` spelling, where the consumers
read it.  In particular `rw [IsZero.iff_id_eq_zero]` is not usable on a goal about
`SheafOfModules X.ringCatSheaf`: that goal is not type-correct at the `implicit` transparency
`rw` builds its motive at.  `CategoryTheory.Functor.map_isZero` at the `Scheme.Modules` spelling
is, and is used instead.

**Quasi-coherence is hypothesized only in the nonnegative degrees.**  That is all the coproduct
over `ℕ` uses, and it is all a symmetric algebra supplies as a theorem; a hypothesis over every
integer degree would have to be discharged, in the negative degrees, from the vanishing of the
piece.

**No `stacks` attribute is attached.**  Nothing here states a clause of a tag at the tag's own
hypotheses: these are [Stacks Project, Tag 01BG] and [Stacks Project, Tag 01S8] applied to one
family of modules, and the attributes for those sit where they are proved.

## References

* [Stacks Project, Tag 09MS](https://stacks.math.columbia.edu/tag/09MS)
* [Stacks Project, Tag 01BG](https://stacks.math.columbia.edu/tag/01BG)
* [Stacks Project, Tag 01S8](https://stacks.math.columbia.edu/tag/01S8)
* [Stacks Project, Tag 01CK](https://stacks.math.columbia.edu/tag/01CK)
* [Stacks Project, Tag 01CL](https://stacks.math.columbia.edu/tag/01CL)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
open RingedSpaceModuleAdjunction Stacks.RingedSpace Stacks.RelativeSpec

universe u

namespace Stacks.AmpleThickeningDevissage

variable {V X : Scheme.{u}} (v : V ⟶ X)
  (A : SheafOfModules.GradedAlgebra.{u, u} X.ringCatSheaf)

/-- **`v_* v^* A_n` is a zero module wherever `A_n` is.**  Pullback and pushforward of sheaves of
modules along a morphism of schemes are additive, so they carry an identity that is zero to an
identity that is zero. -/
theorem isZero_pushforwardPullbackGradedAlgebra_piece (n : ℤ) (h : IsZero (A.piece n)) :
    IsZero ((pushforwardPullbackGradedAlgebra v A).piece n) :=
  Functor.map_isZero (Scheme.Modules.pushforward v)
    (Functor.map_isZero (Scheme.Modules.pullback v) h)

/-- **`v_* v^* A_n` is quasi-coherent** whenever `A_n` is, for a closed immersion of schemes.

The piece is `v_*(v^* A_n)` by `rfl`
(`Stacks.AmpleThickeningDevissage.pushforwardPullbackGradedAlgebra_piece`); the inverse image of a
quasi-coherent module is quasi-coherent by [Stacks Project, Tag 01BG], and the direct image of a
quasi-coherent module along an affine morphism is quasi-coherent, a closed immersion being
affine. -/
theorem isQuasicoherent_pushforwardPullbackGradedAlgebra_piece [IsClosedImmersion v] (n : ℤ)
    (hA : (A.piece n).IsQuasicoherent) :
    ((pushforwardPullbackGradedAlgebra v A).piece n).IsQuasicoherent :=
  @Stacks.AlgebraicGeometry.AffinePushforward.pushforward_isQuasicoherent_of_isAffineHom
    _ _ v ((Scheme.Modules.pullback v).obj (A.piece n)) inferInstance
    (@AlgebraicGeometry.SheafOfModules.modulePullback_isQuasicoherent
      _ _ v.toLRSHom.toShHom (A.piece n) hA)

/-- **`⨁_{m ≥ 0} v_* v^* A_m` is quasi-coherent** whenever every nonnegative piece of `A` is.
Each summand is quasi-coherent by
`Stacks.AmpleThickeningDevissage.isQuasicoherent_pushforwardPullbackGradedAlgebra_piece`, and
quasi-coherent modules on a scheme are stable under colimits
(`Stacks.AlgebraicGeometry.QuasicoherentColimits.isQuasicoherent_colimit`).

This is the datum `Stacks.RelativeSpec.isQuasicoherent_gradedAlgebraSheaf` takes of the right-hand
term of the graded square-zero extension of [Stacks Project, Tag 09MS]. -/
theorem isQuasicoherent_coprod_pushforwardPullbackGradedAlgebra [IsClosedImmersion v]
    (hA : ∀ n : ℕ, (A.piece (n : ℤ)).IsQuasicoherent) :
    (∐ fun n : ℕ => (pushforwardPullbackGradedAlgebra v A).piece (n : ℤ)).IsQuasicoherent :=
  Stacks.AlgebraicGeometry.QuasicoherentColimits.isQuasicoherent_colimit
    (Discrete.functor fun n : ℕ =>
      (((pushforwardPullbackGradedAlgebra v A).piece (n : ℤ)) : X.Modules))
    fun k => isQuasicoherent_pushforwardPullbackGradedAlgebra_piece v A (k.as : ℤ) (hA k.as)

/-- **The ungraded realization of `v_* v^* A` is a quasi-coherent sheaf of commutative
`𝒪_X`-algebras**, for a closed immersion of schemes and a sheaf of graded algebras that vanishes
in negative degrees and is quasi-coherent in the nonnegative ones.

This is the quasi-coherence of the right-hand term of the graded sequence
`0 → ⨁_m 𝓘 · A_m → ⨁_m A_m → ⨁_m v_* v^* A_m → 0` of [Stacks Project, Tag 09MS], in the ungraded
spelling `Stacks.RelativeSpec.gradedAlgebraSheaf`. -/
theorem isQuasicoherent_gradedAlgebraSheaf_pushforwardPullback [IsClosedImmersion v]
    (hc : ∀ (i j : ℤ) (W : (Opens ↥X)ᵒᵖ) (x : (A.piece i).val.obj W)
      (y : (A.piece j).val.obj W), HEq ((A.mul i j).app W x y) ((A.mul j i).app W y x))
    (hA : ∀ n : ℕ, (A.piece (n : ℤ)).IsQuasicoherent)
    (hzero : ∀ n : ℤ, n < 0 → IsZero (A.piece n)) :
    AlgebraSheaf.IsQuasicoherent (gradedAlgebraSheaf X (pushforwardPullbackGradedAlgebra v A)
      (pushforwardPullbackGradedAlgebra_mul_comm v A hc)) :=
  isQuasicoherent_gradedAlgebraSheaf X (pushforwardPullbackGradedAlgebra v A) _
    (fun n hn => isZero_pushforwardPullbackGradedAlgebra_piece v A n (hzero n hn))
    (isQuasicoherent_coprod_pushforwardPullbackGradedAlgebra v A hA)

/-- **The ungraded realization of `v_* v^* Sym(L)` is a quasi-coherent sheaf of commutative
`𝒪_X`-algebras**, with no hypothesis beyond quasi-coherence of `L`: the symmetric algebra vanishes
in negative degrees (`AlgebraicGeometry.Scheme.Modules.isZero_symmetricAlgebra_piece`) and its
nonnegative pieces are quasi-coherent
(`AlgebraicGeometry.Scheme.Modules.isQuasicoherent_symmetricAlgebra_piece`, the degreewise half of
[Stacks Project, Tag 01CL]).

At an invertible `L` the pieces are the tensor powers `L^{⊗ m}`
(`Stacks.PowerFamilyBridge.symmetricPieceIsoTensorPowModule`), so this is the quasi-coherence of
`⨁_{m ≥ 0} v_* v^* L^{⊗ m}` — the right-hand term of the graded square-zero extension of
[Stacks Project, Tag 09MS]. -/
theorem isQuasicoherent_gradedAlgebraSheaf_pushforwardPullback_symmetricAlgebra
    [IsClosedImmersion v] (L : X.Modules) [L.IsQuasicoherent] :
    AlgebraSheaf.IsQuasicoherent (gradedAlgebraSheaf X
      (pushforwardPullbackGradedAlgebra v (Scheme.Modules.symmetricAlgebra X L))
      (pushforwardPullbackGradedAlgebra_mul_comm v (Scheme.Modules.symmetricAlgebra X L)
        (Scheme.Modules.symmetricAlgebra_mul_comm X L))) :=
  isQuasicoherent_gradedAlgebraSheaf_pushforwardPullback v (Scheme.Modules.symmetricAlgebra X L)
    (Scheme.Modules.symmetricAlgebra_mul_comm X L)
    (fun n => Scheme.Modules.isQuasicoherent_symmetricAlgebra_piece X L n)
    (fun n hn => Scheme.Modules.isZero_symmetricAlgebra_piece X L n hn)

end Stacks.AmpleThickeningDevissage

end
