module

public import StacksFrontier.Cotangent.SheavesOfRings.RingedToposNaiveExtComparison
public import StacksFrontier.Deformation.AlgebraExtension.ExtClass
public import StacksFrontier.Deformation.ToposThickening.SplitBaseSolutionAlgebraExtension

/-!
# The class of a solution over a split base thickening

Let `S` be a square-zero extension problem of ringed topoi (Stacks 08UF) over `f : X ⟶ B`, with
base thickening `𝒪_{B'} ⟶ 𝒪_B` split by a ring map `s : 𝒪_B ⟶ 𝒪_{B'}`, and with prescribed
module `𝒢`. A solution `𝒪'` is then an extension `0 → 𝒢 → 𝒪' → 𝒪_X → 0` of `f⁻¹𝒪_B`-algebras
(`...RingedToposExtensionProblem.toSplitAlgebraExtension`), so it has a class in
`Ext¹(NL_{X/B}, 𝒢)` (Stacks 0GQ5), which is `Ext¹(L_{X/B}, 𝒢)` (Stacks 08V2). This is the
tangent class of Remark 0D1P: for the trivial thickening `A ⟶ A[M]`, split by the constants, it
identifies the deformations of `X` over `A[M]` with `Ext¹(L_{X/A}, 𝒪_X ⊗_A M)`.

## Main definitions

* `...RingedToposExtensionProblem.splitNaiveClass`: the class of a solution in
  `Ext¹(NL_{X/B}, 𝒢)`.
* `...RingedToposExtensionProblem.splitCotangentClass`: the class of a solution in
  `Ext¹(L_{X/B}, 𝒢)`.
* `...RingedToposExtensionProblem.splitSolutionClassesEquivCotangentExt`: the bijection of the
  isomorphism classes of solutions with `Ext¹(L_{X/B}, 𝒢)`.

## References

* [Stacks Project, Tag 08UF](https://stacks.math.columbia.edu/tag/08UF)
* [Stacks Project, Tag 0GQ5](https://stacks.math.columbia.edu/tag/0GQ5)
* [Stacks Project, Tag 08V2](https://stacks.math.columbia.edu/tag/08V2)
* [Stacks Project, Remark 0D1P](https://stacks.math.columbia.edu/tag/0D1P)
-/

@[expose] public noncomputable section

open CategoryTheory
open AlgebraicGeometry (RingedTopos RingedToposHom)

universe t u v' u'

namespace Deformation.ToposThickening.RingedToposExtensionProblem

variable {X : RingedTopos.{u, u, u}} {B : RingedTopos.{v', u', u}}
  [X.J.HasSheafCompose (forget RingCat.{u})] [B.J.HasSheafCompose (forget RingCat.{u})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [B.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasWeakSheafify X.J CommRingCat.{u}] [X.J.WEqualsLocallyBijective CommRingCat.{u}]
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [X.J.HasSheafCompose (forget CommRingCat.{u})] [(forget CommRingCat.{u}).ReflectsIsomorphisms]
  [HasDerivedCategory.{t} (Sheaf.targetModules.{u, u, u} X.J X.O)]
  (S : RingedToposExtensionProblem X B)
  (s : B.O ⟶ S.baseExtension) (hs : s ≫ S.baseReduction = 𝟙 B.O)

/-- **The class of a solution over a split base in `Ext¹(NL_{X/B}, 𝒢)`**: the class
(Stacks 0GQ5) of the solution, read through the section `s` as an extension of
`f⁻¹𝒪_B`-algebras. -/
def splitNaiveClass (P : S.CompatibleFirstOrderThickening) :
    S.f.naiveCotangentExt (targetG.{u, u, u} S) 1 :=
  AlgebraExtension.extClass (toSplitAlgebraExtension S s hs P)

/-- **The class of a solution over a split base in `Ext¹(L_{X/B}, 𝒢)`**: `splitNaiveClass` read on
the cotangent complex through `Ext¹(NL_{X/B}, 𝒢) = Ext¹(L_{X/B}, 𝒢)` (Stacks 08V2). -/
def splitCotangentClass (P : S.CompatibleFirstOrderThickening) :
    S.f.cotangentExt (targetG.{u, u, u} S) 1 :=
  S.f.naiveExtOneEquiv _ (S.splitNaiveClass s hs P)

omit [HasWeakSheafify X.J CommRingCat.{u}] [X.J.HasSheafCompose (forget CommRingCat.{u})]
  [(forget CommRingCat.{u}).ReflectsIsomorphisms] in
/-- `splitCotangentClass` is `splitNaiveClass` precomposed with the canonical map
`L_{X/B} ⟶ NL_{X/B}`. -/
theorem splitCotangentClass_eq (P : S.CompatibleFirstOrderThickening) :
    S.splitCotangentClass s hs P =
      DerivedCategory.Q.map S.f.canonicalNaiveComparison ≫ S.splitNaiveClass s hs P :=
  S.f.naiveExtOneEquiv_apply _ _

/-- **The tangent classes over a split base thickening.** A section `s` of the base thickening
identifies the isomorphism classes of solutions of `S` with `Ext¹(L_{X/B}, 𝒢)`: a solution is an
extension of `f⁻¹𝒪_B`-algebras through `s`, these are classified by `Ext¹(NL_{X/B}, 𝒢)`
(Stacks 0GQ5), and `Ext¹(NL_{X/B}, 𝒢) = Ext¹(L_{X/B}, 𝒢)` (Stacks 08V2). -/
def splitSolutionClassesEquivCotangentExt :
    CompatibleFirstOrderThickening.IsomorphismClasses S ≃
      S.f.cotangentExt (targetG.{u, u, u} S) 1 :=
  (solutionClassesEquivSplitAlgebraExtensionClasses S s hs).trans
    ((AlgebraExtension.extClassEquiv S.f.fSharpInverseImage S.G).trans
      (S.f.naiveExtOneEquiv _).toEquiv)

/-- `splitSolutionClassesEquivCotangentExt` sends the isomorphism class of a solution `P` to
`splitCotangentClass P`. -/
@[simp]
theorem splitSolutionClassesEquivCotangentExt_mk (P : S.CompatibleFirstOrderThickening) :
    S.splitSolutionClassesEquivCotangentExt s hs (Quotient.mk _ P) =
      S.splitCotangentClass s hs P :=
  rfl

end Deformation.ToposThickening.RingedToposExtensionProblem

end
