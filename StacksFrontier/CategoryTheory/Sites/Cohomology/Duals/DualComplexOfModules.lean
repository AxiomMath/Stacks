module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LeftDualRingedSite
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.MonoidalStrictColimits
public import StacksFrontier.Algebra.Homology.SignedDualComplex
import StacksCore.Tactic.StacksAttribute

/-!
# The dual complex of a complex of modules on a ringed site

Let `(C, 𝒪)` be a ringed site and let `ℱ^•` be a complex of `𝒪`-modules each of whose terms is,
locally on the site, a direct summand of a finite free `𝒪`-module. This file builds the complex

`𝒢^• = SheafHom^•(ℱ^•, 𝒪)`, `𝒢^j = SheafHom(ℱ^{-j}, 𝒪)`,

of [Stacks, Tag 0FPR] — its differential the signed transpose of the differential of `ℱ^•` — and
shows that `𝒢^•`, together with `η = ∑ ηₙ` and `ε = ∑ εₙ`, is a left dual of `ℱ^•` in the
monoidal category of complexes of `𝒪`-modules of [Stacks, Tag 0FPQ], for a complex supported in
finitely many degrees.

The indexing is the one [Stacks, Tag 0FPR] fixes: the degree-`j` term of the dual is the dual
sheaf of the degree-`-j` term of `ℱ^•`, so that `ηₙ : 𝒪 ⟶ ℱ^n ⊗ 𝒢^{-n}` and
`εₙ : 𝒢^{-n} ⊗ ℱ^n ⟶ 𝒪` are the coevaluation and the evaluation of [Stacks, Tag 0FNY] at the
term `ℱ^n`. In degree zero the Hom complex of [Stacks, Tag 0A8X] into the structure sheaf placed
in degree zero is `∏_{j = p + q} SheafHom(ℱ^{-q}, 𝒪^p) = SheafHom(ℱ^{-j}, 𝒪)`, the single
surviving factor, which is the term taken here.

## Main definitions

* `Stacks.SheafOfModules.Strict.dualComplexX`: the degree-`j` term `SheafHom(ℱ^{-j}, 𝒪)`.
* `Stacks.SheafOfModules.Strict.dualComplexPairing`: the pairing of [Stacks, Tag 0FNY] at the
  term `ℱ^i`, placed in degree `j` of the dual complex for `i + j = 0`.
* `Stacks.SheafOfModules.Strict.dualComplex`: **the dual complex `𝒢^•`**, with the signed
  transpose `d_𝒢^j = -(-1)^j (d_ℱ^{-j-1})^∨` as differential.

## Main results

* `Stacks.SheafOfModules.Strict.exactPairingDualComplex`: **[Stacks, Tag 0FPR] for a complex of
  bounded support** — `𝒢^•` with `η = ∑ ηₙ` and `ε = ∑ εₙ` is a left dual of `ℱ^•`.
* `Stacks.SheafOfModules.Strict.dualComplex_X` and
  `Stacks.SheafOfModules.Strict.dualComplex_d`: the terms and the differential of `𝒢^•`.

## Implementation notes

**Where the work is.** The assembly of the sums and the two triangle identities for them is
`CochainComplex.exactPairingOfSignedTranspose`, and the construction of a complex out of a
family of degreewise duals is `CochainComplex.dualComplex`; both are abstract, for any monoidal
preadditive category with the graded-monoidal hypotheses. What this file supplies is the family:
the dual sheaves of the terms with the pairings of [Stacks, Tag 0FNY], indexed so that the
degree-`j` term of the dual pairs with the degree-`-j` term of `ℱ^•`. The index flip is
discharged by `subst` against the equation `i + j = 0` that
`CochainComplex.dualComplex` asks its family of pairings to carry.

**Which spelling of the monoidal structure.** `Stacks.SheafOfModules.Strict.monoidalCategory` on
`Mod(𝒪)` and `monoidalCategoryCochainComplex` on complexes, the pair over which the converse
statements of [Stacks, Tag 0FPA] and [Stacks, Tag 0FPS] are already stated, so that the two
directions are about one monoidal category. The pairing of [Stacks, Tag 0FNY] is stated for
`Strict.monoidalCategory`; as in
`StacksFrontier/CategoryTheory/Sites/Cohomology/Duals/TermsOfADualComplexOfModules.lean` it is
ascribed at the `Stacks.SheafOfModules.Strict.monoidalCategory` spelling, the definitional equality
crossing at the `:=`.

**The tag's own hypothesis.** [Stacks, Tag 0FPR] assumes only that every object of the site has
a covering on whose members `ℱ^•` is strictly perfect, which gives the local finiteness of the
terms used here but boundedness only *locally*; the support hypothesis below is a single global
finite set of degrees. Removing it means making sense of `η = ∑ ηₙ` as a locally finite sum, and
that is done in
`StacksFrontier/CategoryTheory/Sites/Cohomology/Duals/LeftDualOfALocallyStrictlyPerfectComplex.lean`:
the degree-zero part of `ℱ^• ⊗ 𝒢^•` is a coproduct of locally finitely many nonzero summands,
hence also their product, so `η` is produced from its components. The statement below is the
globally bounded case, which needs none of that. The local boundedness of a complex that *has* a
left dual is the converse direction,
`Stacks.SheafOfModules.Strict.isLocallyBounded_of_exactPairing`.

## References

* [Stacks Project, Tag 0FPR](https://stacks.math.columbia.edu/tag/0FPR)
* [Stacks Project, Tag 0FNY](https://stacks.math.columbia.edu/tag/0FNY)
* [Stacks Project, Tag 0FNK](https://stacks.math.columbia.edu/tag/0FNK)
* [Stacks Project, Tag 0A8X](https://stacks.math.columbia.edu/tag/0A8X)
* [Stacks Project, Tag 0FPQ](https://stacks.math.columbia.edu/tag/0FPQ)
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
  [HasSheafify J AddCommGrpCat.{max u v}]
  [∀ V : C, HasWeakSheafify (J.over V) AddCommGrpCat.{max u v}]
  [∀ V : C, (J.over V).WEqualsLocallyBijective AddCommGrpCat.{max u v}]
  (F : CochainComplex (Mod R) ℤ)

/-- The degree-`j` term of the dual complex of [Stacks, Tag 0FPR]: the dual sheaf
`SheafHom(ℱ^{-j}, 𝒪)` of the term of `ℱ^•` in the *opposite* degree. -/
abbrev dualComplexX (j : ℤ) : Mod R := dualSheaf R.obj (isSheaf_ringSheaf R) (F.X (-j))

variable (hF : ∀ n : ℤ, IsLocallyDirectSummandOfFiniteFree R.obj (isSheaf_ringSheaf R) (F.X n))

/-- **The degreewise pairings of [Stacks, Tag 0FPR], indexed by the two degrees.** For
`i + j = 0` the degree-`j` term `SheafHom(ℱ^{-j}, 𝒪)` of the dual complex is a left dual of the
term `ℱ^i`, with the coevaluation `ηᵢ` and evaluation `εᵢ` of [Stacks, Tag 0FNY].

Carrying the two degrees separately is what performs the index flip: a consumer which, like the
dual complex, is indexed by `j` reads the pairing off at `i = -j`. -/
@[instance_reducible]
def dualComplexPairing (i j : ℤ) (h : i + j = 0) :
    letI : MonoidalCategory (_root_.SheafOfModules.{max u v}
        (Stacks.SheafOfModules.Tensor.ringSheaf R)) :=
      Stacks.SheafOfModules.Strict.monoidalCategory R.obj
        (Stacks.SheafOfModules.Tensor.ringSheaf R).property
    ExactPairing (F.X i) (dualComplexX R F j) := by
  obtain rfl : i = -j := by omega
  exact exactPairingDualSheafOfLocalSummand R.obj (isSheaf_ringSheaf R) (F.X (-j)) (hF (-j))

/-- **The dual complex `𝒢^• = SheafHom^•(ℱ^•, 𝒪)` of [Stacks, Tag 0FPR].** Its degree-`j` term
is the dual sheaf `SheafHom(ℱ^{-j}, 𝒪)` of [Stacks, Tag 0FNY], and its differential is the
signed transpose `d_𝒢^j = -(-1)^j (d_ℱ^{-j-1})^∨`, the sign convention of [Stacks, Tag 0FNK]. -/
@[stacks 0FPR "the construction of the complex `𝒢^• = SheafHom^•(ℱ^•, 𝒪)`: its degree-`j` term \
is the dual sheaf `SheafHom(ℱ^{-j}, 𝒪)` of Tag 0FNY — the single surviving factor of the \
degree-`j` term of the Hom complex of Tag 0A8X into `𝒪` placed in degree zero — and its \
differential is the signed transpose `d_𝒢^j = -(-1)^j (d_ℱ^{-j-1})^∨` of Tag 0FNK. The \
remaining assertion of the tag, that `𝒢^•` with `η = ∑ ηₙ` and `ε = ∑ εₙ` is a left dual of \
`ℱ^•`, is `Stacks.SheafOfModules.Strict.exactPairingDualComplex`, and under the tag's OWN hypothesis \
`Stacks.SheafOfModules.Strict.exactPairingDualComplexOfLocallyStrictlyPerfect`. Only the \
termwise half of the tag's hypothesis is assumed here; the same complex under the tag's OWN \
hypothesis is `Stacks.SheafOfModules.Strict.dualComplexOfLocallyStrictlyPerfect`",
  sga "4 XVII 1.1.6" "special case"]
def dualComplex : CochainComplex (Mod R) ℤ :=
  letI : MonoidalCategory (_root_.SheafOfModules.{max u v}
      (Stacks.SheafOfModules.Tensor.ringSheaf R)) :=
    Stacks.SheafOfModules.Strict.monoidalCategory R.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf R).property
  letI : MonoidalPreadditive (Mod R) := monoidalPreadditiveRingSheaf R
  CochainComplex.dualComplex F (dualComplexX R F) (dualComplexPairing R F hF)

omit [HasSheafify J AddCommGrpCat] in
/-- The terms of the dual complex are the dual sheaves of the terms of `ℱ^•` in the opposite
degrees. -/
theorem dualComplex_X (j : ℤ) :
    (dualComplex R F hF).X j = dualSheaf R.obj (isSheaf_ringSheaf R) (F.X (-j)) := rfl

omit [HasSheafify J AddCommGrpCat] in
/-- **The differential of the dual complex is the signed transpose.** From degree `-(n+1)` to
degree `-n` it is `(-1)^n` times the right adjoint mate of `d_ℱ^n : ℱ^n ⟶ ℱ^{n+1}`. -/
theorem dualComplex_d (n : ℤ) :
    letI : MonoidalCategory (_root_.SheafOfModules.{max u v}
        (Stacks.SheafOfModules.Tensor.ringSheaf R)) :=
      Stacks.SheafOfModules.Strict.monoidalCategory R.obj
        (Stacks.SheafOfModules.Tensor.ringSheaf R).property
    letI : MonoidalPreadditive (Mod R) := monoidalPreadditiveRingSheaf R
    (dualComplex R F hF).d (-(n + 1)) (-n) =
      CochainComplex.signedTransposeAt F (dualComplexX R F) (dualComplexPairing R F hF) n :=
  let : MonoidalCategory (_root_.SheafOfModules.{max u v}
      (Stacks.SheafOfModules.Tensor.ringSheaf R)) :=
    Stacks.SheafOfModules.Strict.monoidalCategory R.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf R).property
  let : MonoidalPreadditive (Mod R) := monoidalPreadditiveRingSheaf R
  CochainComplex.dualComplex_d F (dualComplexX R F) (dualComplexPairing R F hF) n

/-- **[Stacks, Tag 0FPR] for a complex of bounded support.** Let `ℱ^•` be a complex of
`𝒪`-modules each of whose terms is, locally on the site, a direct summand of a finite free
`𝒪`-module, and suppose `ℱ^•` vanishes outside a finite set `s` of degrees. Then the complex
`𝒢^• = SheafHom^•(ℱ^•, 𝒪)`, together with `η = ∑ ηₙ` and `ε = ∑ εₙ` assembled from the
coevaluations and evaluations of [Stacks, Tag 0FNY], is a left dual of `ℱ^•` in the monoidal
category of complexes of `𝒪`-modules of [Stacks, Tag 0FPQ]: both triangle identities hold. -/
@[stacks 0FPR "the left-dual assertion: `𝒢^•` with `η = ∑ ηₙ` and `ε = ∑ εₙ`, the \
coevaluations and evaluations of Tag 0FNY at the terms, satisfies the two triangle identities \
of Tag 0FFP in the monoidal category of complexes of Tag 0FPQ. The complex `𝒢^•` is \
`Stacks.SheafOfModules.Strict.dualComplex`, whose terms and signed-transpose differential are \
`dualComplex_X` and `dualComplex_d`. NOT under the tag's own hypothesis: that every object has \
a covering on which `ℱ^•` is strictly perfect gives the termwise local finiteness assumed \
here, but boundedness only locally, whereas `s` is one global finite set of degrees. The same \
conclusion under the tag's own hypothesis, with `η = ∑ ηₙ` made sense of as a locally finite \
sum, is `Stacks.SheafOfModules.Strict.exactPairingDualComplexOfLocallyStrictlyPerfect`; the \
converse local boundedness is \
`Stacks.SheafOfModules.Strict.isLocallyBounded_of_exactPairing`", instance_reducible]
def exactPairingDualComplex (s : Finset ℤ) (hb : ∀ m, m ∉ s → IsZero (F.X m)) :
    @ExactPairing _ _ (monoidalCategoryCochainComplex R) F (dualComplex R F hF) :=
  letI : MonoidalCategory (_root_.SheafOfModules.{max u v}
      (Stacks.SheafOfModules.Tensor.ringSheaf R)) :=
    Stacks.SheafOfModules.Strict.monoidalCategory R.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf R).property
  letI : MonoidalPreadditive (Mod R) := monoidalPreadditiveRingSheaf R
  letI : ∀ X₁ : Mod R, PreservesColimit (Functor.empty.{0} (Mod R))
      ((curriedTensor (Mod R)).obj X₁) := fun X₁ => preservesColimit_tensorLeft R _ X₁
  letI : ∀ X₂ : Mod R, PreservesColimit (Functor.empty.{0} (Mod R))
      ((curriedTensor (Mod R)).flip.obj X₂) := fun X₂ => preservesColimit_tensorRight R _ X₂
  letI : ∀ X₁ X₂ X₃ : GradedObject ℤ (Mod R),
      GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃ := hasGoodTensor₁₂Tensor R
  letI : ∀ X₁ X₂ X₃ : GradedObject ℤ (Mod R),
      GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃ := hasGoodTensorTensor₂₃ R
  letI : ∀ X₁ X₂ X₃ X₄ : GradedObject ℤ (Mod R),
      GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄ := hasTensor₄ObjExt R
  CochainComplex.exactPairingDualComplex F (dualComplexX R F) (dualComplexPairing R F hF) s hb

end Stacks.SheafOfModules.Strict

end

end
