module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.Duals.DualComplexAsTheHomComplex
public import StacksFrontier.Algebra.Homology.InternalHomComplexSingleCollapse

/-!
# The degreewise duality on the candidate dual complex

Let `(C, 𝒪)` be a ringed site and `ℱ^•` a complex of `𝒪`-modules. The complex that
[Stacks, Tag 0FP9] calls `𝒢^• = SheafHom^•(ℱ^•, 𝒪)` is available unconditionally as the internal
hom into the unit, `(ihom ℱ^•).obj (𝟙_)`, for
`Stacks.SheafOfModules.Strict.monoidalClosedCochainComplex`. This file equips that complex with
its degreewise duality:

`ℱ^n` and `𝒢^{-n}` are an exact pairing, for every `n`, as soon as `ℱ^n` is locally a direct
summand of a finite free `𝒪`-module — which is the tag's own termwise hypothesis.

That datum is exactly the argument `p` of `CochainComplex.exactPairingOfDegreewiseOfChainMaps`,
at the complex `𝒢^•` the tag names.

## Relation to `homComplexUnitIsoDualSheafX`

`Stacks.SheafOfModules.Strict.homComplexUnitIsoDualSheafX` identifies `𝒢^{-n}` with the dual
sheaf of [Stacks, Tag 0FNY], but it takes an `ExactPairing` of the *complexes* as a hypothesis —
which is the conclusion of [Stacks, Tag 0FP9], so it cannot be used in a proof of it. The
identification below assumes no pairing of complexes: the degree collapse is unconditional, and
the comparison with the dual sheaf is paid for with the tag's termwise hypothesis alone.

## Main results

* `Stacks.SheafOfModules.Strict.ihomUnitXIso`: **unconditional** — the degree `-n` term of
  `𝒢^•` is the internal hom `SheafHom(ℱ^n, 𝒪)` of `Mod(𝒪)`, with no hypothesis on `ℱ^•`.
* `Stacks.SheafOfModules.Strict.exactPairingIhomUnit`: the internal hom into the unit is a left
  dual of `ℱ^n`, from the tag's termwise hypothesis.
* `Stacks.SheafOfModules.Strict.ihomUnitXIsoDualSheaf`: `𝒢^{-n} ≅ SheafHom(ℱ^n, 𝒪)` in the
  [Stacks, Tag 0FNY] spelling `Stacks.SheafOfModules.dualSheaf`, from the same hypothesis.
* `Stacks.SheafOfModules.Strict.exactPairingIhomComplexX`: the degreewise pairing read off
  `𝒢^•` itself — the datum `CochainComplex.exactPairingOfDegreewiseOfChainMaps` consumes.

## Implementation notes

**The two realisations of the internal hom.** `(ihom F).obj G` for `strictMonoidalClosed` and
`Stacks.SheafOfModules.sheafHom 𝒪 h𝒪 F G` are *not* definitionally equal, so `ihomUnitXIso`
cannot be pushed through to `dualSheaf` for free. What bridges them is uniqueness of duals:
`CategoryTheory.rightDualIsoIhomUnit` identifies any left dual of `F` with `(ihom F).obj (𝟙_)`,
and the dual sheaf is one by [Stacks, Tag 0FNY]. That is why `ihomUnitXIsoDualSheaf` carries the
termwise hypothesis while `ihomUnitXIso` does not.

**Instance spellings.** The pairing of [Stacks, Tag 0FNY] is stated over
`Stacks.SheafOfModules.Strict.monoidalCategory 𝒪 h𝒪`, which is (in the namespace
`Stacks.SheafOfModules`) `Strict.monoidalCategory R.obj (Tensor.ringSheaf R).property` only
after unfolding an `instance_reducible` definition — a step instance search does not take. Each
`letI` below therefore carries an explicit type ascription in the
`Stacks.SheafOfModules.Strict.monoidalCategory` spelling; without it the `ExactPairing` argument
of `rightDualIsoIhomUnit` fails to synthesize.

## References

* [Stacks Project, Tag 0FP9](https://stacks.math.columbia.edu/tag/0FP9)
* [Stacks Project, Tag 0FNY](https://stacks.math.columbia.edu/tag/0FNY)
* [Stacks Project, Tag 0FPA](https://stacks.math.columbia.edu/tag/0FPA)
-/

@[expose] public section

open CategoryTheory Limits MonoidalCategory GradedObject

noncomputable section

universe v u

namespace Stacks.SheafOfModules.Strict

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasWeakSheafify J AddCommGrpCat.{max u v}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
  (R : Sheaf J CommRingCat.{max u v})

/-- **The terms of the candidate dual complex, unconditionally.** The degree `-n` term of
`𝒢^• = (ihom ℱ^•).obj (𝟙_)` is the internal hom `SheafHom(ℱ^n, 𝒪)` of `Mod(𝒪)`.

Nothing is assumed: the unit complex is concentrated in degree zero, so of the product over `p`
of `SheafHom(ℱ^p, 𝟙_^{p-n})` only the factor at `p = n` survives. -/
def ihomUnitXIso (K : CochainComplex (Mod R) ℤ) (n : ℤ) :
    letI : MonoidalCategory (_root_.SheafOfModules.{max u v}
        (Stacks.SheafOfModules.Tensor.ringSheaf R)) :=
      Stacks.SheafOfModules.Strict.monoidalCategory R.obj
        (Stacks.SheafOfModules.Tensor.ringSheaf R).property
    letI := strictMonoidalClosed R
    letI := monoidalCategoryCochainComplex R
    letI := monoidalClosedCochainComplex R
    ((ihom K).obj (𝟙_ (CochainComplex (Mod R) ℤ))).X (-n) ≅
      (ihom (K.X n)).obj (𝟙_ (Mod R)) :=
  letI : MonoidalCategory (_root_.SheafOfModules.{max u v}
      (Stacks.SheafOfModules.Tensor.ringSheaf R)) :=
    Stacks.SheafOfModules.Strict.monoidalCategory R.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf R).property
  letI : MonoidalPreadditive (Mod R) := monoidalPreadditiveRingSheaf R
  letI := strictMonoidalClosed R
  CochainComplex.internalHomXSingleIso K (𝟙_ (Mod R)) n

variable [∀ V : C, HasWeakSheafify (J.over V) AddCommGrpCat.{max u v}]
  [∀ V : C, (J.over V).WEqualsLocallyBijective AddCommGrpCat.{max u v}]

/-- **The internal hom into the unit is a left dual.** If `F` is locally a direct summand of a
finite free `𝒪`-module, then `SheafHom(F, 𝒪)` in the internal-hom spelling is a left dual of `F`.

The dual sheaf of [Stacks, Tag 0FNY] is one such dual, and uniqueness of duals transports the
pairing onto the internal hom. -/
@[instance_reducible]
def exactPairingIhomUnit (F : Mod R)
    (hF : IsLocallyDirectSummandOfFiniteFree R.obj (isSheaf_ringSheaf R) F) :
    letI : MonoidalCategory (_root_.SheafOfModules.{max u v}
        (Stacks.SheafOfModules.Tensor.ringSheaf R)) :=
      Stacks.SheafOfModules.Strict.monoidalCategory R.obj
        (Stacks.SheafOfModules.Tensor.ringSheaf R).property
    letI := strictMonoidalClosed R
    ExactPairing F ((ihom F).obj (𝟙_ (Mod R))) :=
  letI : MonoidalCategory (_root_.SheafOfModules.{max u v}
      (Stacks.SheafOfModules.Tensor.ringSheaf R)) :=
    Stacks.SheafOfModules.Strict.monoidalCategory R.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf R).property
  letI : SymmetricCategory (Mod R) :=
    Stacks.SheafOfModules.Strict.symmetricCategory R.obj (isSheaf_ringSheaf R)
  letI := strictMonoidalClosed R
  letI : ExactPairing F
      (dualSheaf R.obj (isSheaf_ringSheaf R) F) :=
    exactPairingDualSheafOfLocalSummand R.obj (isSheaf_ringSheaf R) F hF
  exactPairingCongrRight
    (rightDualIsoIhomUnit F (dualSheaf R.obj (isSheaf_ringSheaf R) F)).symm

/-- **The terms of the candidate dual complex are the dual sheaves of [Stacks, Tag 0FNY].**
`𝒢^{-n} ≅ SheafHom(ℱ^n, 𝒪)`, with the right-hand side in the `Stacks.SheafOfModules.dualSheaf`
spelling that carries the degreewise pairings.

Unlike `Stacks.SheafOfModules.Strict.homComplexUnitIsoDualSheafX`, no pairing of the complexes is
assumed — only the tag's own termwise hypothesis on `ℱ^n`. -/
def ihomUnitXIsoDualSheaf (K : CochainComplex (Mod R) ℤ) (n : ℤ)
    (hK : IsLocallyDirectSummandOfFiniteFree R.obj (isSheaf_ringSheaf R) (K.X n)) :
    letI : MonoidalCategory (_root_.SheafOfModules.{max u v}
        (Stacks.SheafOfModules.Tensor.ringSheaf R)) :=
      Stacks.SheafOfModules.Strict.monoidalCategory R.obj
        (Stacks.SheafOfModules.Tensor.ringSheaf R).property
    letI := monoidalCategoryCochainComplex R
    letI := monoidalClosedCochainComplex R
    ((ihom K).obj (𝟙_ (CochainComplex (Mod R) ℤ))).X (-n) ≅
      dualSheaf R.obj (isSheaf_ringSheaf R) (K.X n) :=
  letI : MonoidalCategory (_root_.SheafOfModules.{max u v}
      (Stacks.SheafOfModules.Tensor.ringSheaf R)) :=
    Stacks.SheafOfModules.Strict.monoidalCategory R.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf R).property
  letI : SymmetricCategory (Mod R) :=
    Stacks.SheafOfModules.Strict.symmetricCategory R.obj (isSheaf_ringSheaf R)
  letI := strictMonoidalClosed R
  letI : ExactPairing (K.X n)
      (dualSheaf R.obj (isSheaf_ringSheaf R) (K.X n)) :=
    exactPairingDualSheafOfLocalSummand R.obj (isSheaf_ringSheaf R) (K.X n) hK
  (ihomUnitXIso R K n).trans
    (rightDualIsoIhomUnit (K.X n) (dualSheaf R.obj (isSheaf_ringSheaf R) (K.X n))).symm

/-- **The degreewise duality on the candidate dual complex.** For every `n`, the degree `-n`
term of `𝒢^• = (ihom ℱ^•).obj (𝟙_)` is a left dual of `ℱ^n`, as soon as `ℱ^n` is locally a direct
summand of a finite free `𝒪`-module.

This is the datum `p` of `CochainComplex.exactPairingOfDegreewiseOfChainMaps` at `L := 𝒢^•`,
the complex [Stacks, Tag 0FP9] names. -/
@[instance_reducible]
def exactPairingIhomComplexX (K : CochainComplex (Mod R) ℤ) (n : ℤ)
    (hK : IsLocallyDirectSummandOfFiniteFree R.obj (isSheaf_ringSheaf R) (K.X n)) :
    letI : MonoidalCategory (_root_.SheafOfModules.{max u v}
        (Stacks.SheafOfModules.Tensor.ringSheaf R)) :=
      Stacks.SheafOfModules.Strict.monoidalCategory R.obj
        (Stacks.SheafOfModules.Tensor.ringSheaf R).property
    letI := monoidalCategoryCochainComplex R
    letI := monoidalClosedCochainComplex R
    ExactPairing (K.X n)
      (((ihom K).obj (𝟙_ (CochainComplex (Mod R) ℤ))).X (-n)) :=
  letI : MonoidalCategory (_root_.SheafOfModules.{max u v}
      (Stacks.SheafOfModules.Tensor.ringSheaf R)) :=
    Stacks.SheafOfModules.Strict.monoidalCategory R.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf R).property
  letI : MonoidalPreadditive (Mod R) := monoidalPreadditiveRingSheaf R
  letI := strictMonoidalClosed R
  letI := exactPairingIhomUnit R (K.X n) hK
  exactPairingCongrRight (ihomUnitXIso R K n)

end Stacks.SheafOfModules.Strict

end

end
