module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.LimitPerfectObjectsInterColimSituation
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.LimitPerfectObjectsUnconditionalInterComparison

/-!
# The comparison isomorphism over the intersection, with its colimit hypotheses discharged

`AlgebraicGeometry.Space.exists_interStageIso_of_isColim` and
`…exists_interStageIso_projHom_of_isColim` produce the pair `(c, hfac)` of the
elementary-distinguished-square step of the essential surjectivity half of Stacks 09RJ from four
`CategoryTheory.PullbackData.LimitSystem.IsColim` hypotheses on the system of intersections, in
the argument orders `(X,Y)`, `(Y,X)`, `(X,X)`, `(Y,Y)`.  **This file discharges all four**, by
`…isColim_canonicalPullbackData_edsPreimageInterLimitSystem_of_pseudoCoherent`
of `LimitPerfectObjectsInterColimSituation.lean`, for the system of intersections of the base
changes along the system of base changes of a Situation 0DKU.

The four orders cost six hypotheses on the two objects rather than three: each of `X` and `Y` has
to be pseudo-coherent (as the first argument), in `D_QCoh` and of locally finite Tor dimension
(as the second).

## Main results

* `Space.RelativeDescentSituation.exists_interStageIso_projHom_of_pseudoCoherent`: the stage `j`
  and the isomorphism `c`, with the compatibility written with
  `CategoryTheory.PullbackData.LimitSystem.projHom`.
* `Space.RelativeDescentSituation.exists_interStageIso_of_pseudoCoherent`: the same, with the
  compatibility written as the conjugation by
  `AlgebraicGeometry.Space.edsBridgeInterComp` — the shape
  `AlgebraicGeometry.Space.exists_glue_isPerfect_derivedPullback_iso_of_factorHom` takes.

## What is assumed

Nothing beyond what
`…RelativeDescentSituation.isColim_edsPreimageInterLimitSystem_of_pseudoCoherent`
assumes; see "What is assumed" in `LimitPerfectObjectsInterColimSituation.lean`.  In particular
the system over `W_b` is the system of base changes of a Situation 0DKU, which is where its limit
property comes from, and the intersection of the square over `X₀` is assumed of finite
presentation over `X₀`.

## References

* [Stacks Project, Lemma 75.24.3 (Tag 09RJ)](https://stacks.math.columbia.edu/tag/09RJ)
* [Stacks Project, Lemma 75.24.2 (Tag 09RI)](https://stacks.math.columbia.edu/tag/09RI)
* [Stacks Project, Situation 0DKU](https://stacks.math.columbia.edu/tag/0DKU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Space

universe u

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance 2000] SheafOfModules.instAbelian
attribute [local instance 3000] Abelian.toPreadditive

namespace RelativeDescentSituation

attribute [local instance] isDirected_laterIndex

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {hZ : B.Contains (⊤_ Scheme.{u})} {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
  (D : RelativeDescentSituation B S hS hZ I)
  {W₀ : AlgebraicSpaces B S hS} {V₀ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
  {U₀ : Subfunctor W₀.1} {f₀ : V₀ ⟶ W₀.1}
  (hsq : IsElementaryDistinguishedSquare B S hS W₀.2 U₀ f₀)
  (pb : D.initialSource ⟶ W₀)

/-- **The comparison isomorphism over the intersection, with no colimit hypothesis left.**  Let
`(U₀ ⊆ W₀, V₀ ⟶ W₀)` be an elementary distinguished square, let `D` be a Situation 0DKU indexed
by a directed preorder `I` in the universe of the site with fewer elements than the cofinality of
the site's size cutoff, let `p_b : X₀ ⟶ W₀` be a morphism, and let the intersection `P_b` of the
square over `X₀` be of finite presentation over `X₀`.  Let `X` and `Y` be objects of `D(𝒪_{P_b})`
which are both pseudo-coherent, both in `D_QCoh(𝒪_{P_b})` and both of locally finite Tor
dimension along `P_b ⟶ Y_0`, and let `α : Ls^*X ≅ E` and `β : Ls^*Y ≅ E` be isomorphisms with a
common object `E` over the intersection at the vertex.  Then there are a stage `j` and an
isomorphism `c : Lt_j^*X ≅ Lt_j^*Y` whose image under
`CategoryTheory.PullbackData.LimitSystem.projHom` is `β⁻¹ ∘ α`.

This is `AlgebraicGeometry.Space.exists_interStageIso_projHom_of_isColim` with its four colimit
hypotheses discharged in the four argument orders. -/
theorem exists_interStageIso_projHom_of_pseudoCoherent
    (hfp : IsFinitePresentation B S hS (edsInterHom B S hS (edsPreimage hsq pb)).hom)
    (hI : Cardinal.mk I < B.cutoff.ord.cof)
    (X Y : derivedModules B S hS (edsInter B S hS (edsPreimage hsq pb)))
    (hXpc : IsPseudoCoherentObject X) (hYpc : IsPseudoCoherentObject Y)
    (hXqc : IsInQuasicoherentDerived (edsInter B S hS (edsPreimage hsq pb)) X)
    (hYqc : IsInQuasicoherentDerived (edsInter B S hS (edsPreimage hsq pb)) Y)
    (hXTor : HasLocallyFiniteTorDimensionAlong
      (edsInterHom B S hS (edsPreimage hsq pb) ≫ D.initialStructure) X)
    (hYTor : HasLocallyFiniteTorDimensionAlong
      (edsInterHom B S hS (edsPreimage hsq pb) ≫ D.initialStructure) Y)
    (E : derivedModules B S hS
      (edsPreimageInterLimitSystem hsq pb D.sourceLimitSystem).limit)
    (α : ((canonicalPullbackData B S hS).pull
        (edsPreimageInterLimitSystem hsq pb D.sourceLimitSystem).limitToBase).obj X ≅ E)
    (β : ((canonicalPullbackData B S hS).pull
        (edsPreimageInterLimitSystem hsq pb D.sourceLimitSystem).limitToBase).obj Y ≅ E) :
    ∃ (j : D.LaterIndex) (c : ((canonicalPullbackData B S hS).pull
        ((edsPreimageInterLimitSystem hsq pb D.sourceLimitSystem).toBase j)).obj X ≅
      ((canonicalPullbackData B S hS).pull
        ((edsPreimageInterLimitSystem hsq pb D.sourceLimitSystem).toBase j)).obj Y),
      (edsPreimageInterLimitSystem hsq pb D.sourceLimitSystem).projHom
          (canonicalPullbackData B S hS) X Y j c.hom = α.hom ≫ β.inv := by
  have h := D.isColim_canonicalPullbackData_edsPreimageInterLimitSystem_of_pseudoCoherent
    hsq pb hfp hI
  exact exists_interStageIso_projHom_of_isColim hsq pb D.sourceLimitSystem X Y
    (h X Y hXpc hYqc hYTor) (h Y X hYpc hXqc hXTor) (h X X hXpc hXqc hXTor)
    (h Y Y hYpc hYqc hYTor) E α β

/-- **The pair `(c, hfac)` of the elementary-distinguished-square step of Stacks 09RJ, with no
colimit hypothesis left.**  The hypotheses are those of
`AlgebraicGeometry.Space.RelativeDescentSituation.exists_interStageIso_projHom_of_pseudoCoherent`;
the conclusion is the same stage `j` and isomorphism `c`, with the compatibility written as the
conjugation of `c` by `AlgebraicGeometry.Space.edsBridgeInterComp` — the identification of the
factorisation `r_P ≫ t_P = s_P` of the maps of intersections — at the source and at the target.

This is `AlgebraicGeometry.Space.exists_interStageIso_of_isColim` with its four colimit
hypotheses discharged, and so is exactly the pair that
`AlgebraicGeometry.Space.exists_glue_isPerfect_derivedPullback_iso_of_factorHom` takes as input,
with `X` read as `A_b|_{P_b}` and `Y` as `Bo_b|_{P_b}`. -/
theorem exists_interStageIso_of_pseudoCoherent
    (hfp : IsFinitePresentation B S hS (edsInterHom B S hS (edsPreimage hsq pb)).hom)
    (hI : Cardinal.mk I < B.cutoff.ord.cof)
    (X Y : derivedModules B S hS (edsInter B S hS (edsPreimage hsq pb)))
    (hXpc : IsPseudoCoherentObject X) (hYpc : IsPseudoCoherentObject Y)
    (hXqc : IsInQuasicoherentDerived (edsInter B S hS (edsPreimage hsq pb)) X)
    (hYqc : IsInQuasicoherentDerived (edsInter B S hS (edsPreimage hsq pb)) Y)
    (hXTor : HasLocallyFiniteTorDimensionAlong
      (edsInterHom B S hS (edsPreimage hsq pb) ≫ D.initialStructure) X)
    (hYTor : HasLocallyFiniteTorDimensionAlong
      (edsInterHom B S hS (edsPreimage hsq pb) ≫ D.initialStructure) Y)
    (E : derivedModules B S hS
      (edsPreimageInterLimitSystem hsq pb D.sourceLimitSystem).limit)
    (α : ((canonicalPullbackData B S hS).pull
        (edsPreimageInterLimitSystem hsq pb D.sourceLimitSystem).limitToBase).obj X ≅ E)
    (β : ((canonicalPullbackData B S hS).pull
        (edsPreimageInterLimitSystem hsq pb D.sourceLimitSystem).limitToBase).obj Y ≅ E) :
    ∃ (j : D.LaterIndex) (c : ((canonicalPullbackData B S hS).pull
        ((edsPreimageInterLimitSystem hsq pb D.sourceLimitSystem).toBase j)).obj X ≅
      ((canonicalPullbackData B S hS).pull
        ((edsPreimageInterLimitSystem hsq pb D.sourceLimitSystem).toBase j)).obj Y),
      ((edsBridgeInterComp hsq pb (D.sourceLimitSystem.toBase j ≫ pb)
            (D.sourceLimitSystem.limitToBase ≫ pb) (D.sourceLimitSystem.toBase j)
            (D.sourceLimitSystem.proj j) rfl
            (by rw [← Category.assoc, D.sourceLimitSystem.proj_toBase j])
            D.sourceLimitSystem.limitToBase
            (D.sourceLimitSystem.proj_toBase j).symm rfl).app X).inv ≫
          (smallEtaleDerivedModulePullback B S hS (edsPreimageInterMap hsq
            (D.sourceLimitSystem.toBase j ≫ pb) (D.sourceLimitSystem.limitToBase ≫ pb)
            (D.sourceLimitSystem.proj j)
            (by rw [← Category.assoc, D.sourceLimitSystem.proj_toBase j]))).map c.hom ≫
          ((edsBridgeInterComp hsq pb (D.sourceLimitSystem.toBase j ≫ pb)
            (D.sourceLimitSystem.limitToBase ≫ pb) (D.sourceLimitSystem.toBase j)
            (D.sourceLimitSystem.proj j) rfl
            (by rw [← Category.assoc, D.sourceLimitSystem.proj_toBase j])
            D.sourceLimitSystem.limitToBase
            (D.sourceLimitSystem.proj_toBase j).symm rfl).app Y).hom =
        α.hom ≫ β.inv := by
  have h := D.isColim_canonicalPullbackData_edsPreimageInterLimitSystem_of_pseudoCoherent
    hsq pb hfp hI
  exact exists_interStageIso_of_isColim hsq pb D.sourceLimitSystem X Y
    (h X Y hXpc hYqc hYTor) (h Y X hYpc hXqc hXTor) (h X X hXpc hXqc hXTor)
    (h Y Y hYpc hYqc hYTor) E α β

end RelativeDescentSituation

end AlgebraicGeometry.Space

end
