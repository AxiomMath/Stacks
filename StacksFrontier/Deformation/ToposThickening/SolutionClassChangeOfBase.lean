module

public import StacksFrontier.Cotangent.SheavesOfRings.NaiveComparisonChangeOfBase
public import StacksFrontier.Deformation.AlgebraExtension.BaseRestriction
public import StacksFrontier.Deformation.ToposThickening.CanonicalObstructionBoundary
public import StacksFrontier.Deformation.ToposThickening.ObstructionBaseClassCoefficient
public import StacksFrontier.Deformation.ToposThickening.SolutionNaiveClassSign

/-!
# The class of a solution under the change of base `f⁻¹𝒪_{B'} ⟶ f⁻¹𝒪_B`

Let `S` be a square-zero extension problem of ringed topoi (Stacks 08UF), with thickened base
`f⁻¹𝒪_{B'} ⟶ f⁻¹𝒪_B ⟶ 𝒪`, and let `Q` be a solution: an extension `0 → 𝒢 → 𝒪' → 𝒪 → 0` of
`f⁻¹𝒪_{B'}`-algebras. Let `E₁` be an extension `0 → 𝒢₁ → 𝒪'₁ → 𝒪 → 0` of `f⁻¹𝒪_B`-algebras and
`h : 𝒪' ⟶ 𝒪'₁` a map over `𝒪`, under `f⁻¹𝒪_{B'}` (through `f⁻¹𝒪_{B'} ⟶ f⁻¹𝒪_B`), inducing
`π : 𝒢 ⟶ 𝒢₁` on the kernels. Then the class of `Q` in `Ext¹(L_{𝒪/f⁻¹𝒪_{B'}}, 𝒢)` pushed along `π`
is the pullback along the change of base `L_{𝒪/f⁻¹𝒪_{B'}} ⟶ L_{𝒪/f⁻¹𝒪_B}` of minus the class of
`E₁` in `Ext¹(L_{𝒪/f⁻¹𝒪_B}, 𝒢₁)`.

In the deformation theory of an algebraic space over a short exact sequence of thickenings
`A₃' → A₂' → A₁'` of `A` (condition (iv) of [Stacks, Tag 07YY], [Stacks, Remark 0D1P]), `Q` is a
lift over `A₂'` read over `A₃'`, `E₁` its restriction to `A₁' = A[I₁]` read through the splitting
`A → A₁'` as an extension of `f⁻¹𝒪_A`-algebras, and the statement is the square `(h₂)` of
`RingedToposExtensionProblem.canonicalObstructionClass_eq_comp_singleδ`.

The proof is a chain of four steps.

* `b ≫ (−cmp ≫ ε(E₁)) = −(cmp₀ ≫ NL(b) ≫ ε(E₁))`: the change of base commutes with the canonical
  maps `L ⟶ NL` (`CategoryTheory.Sheaf.towerCotangentChangeOfBase_comp_canonicalNaiveComparison`).
* `= −(cmp₀ ≫ ε(E₁|_{f⁻¹𝒪_{B'}}))` (`Deformation.AlgebraExtension.extClass_restrictAlong`).
* `= −(cmp₀ ≫ ε(Q) ≫ π[1])`: `h` is a morphism of extensions of `f⁻¹𝒪_{B'}`-algebras along `π`
  (`Deformation.AlgebraExtension.extClass_mapAlong`).
* `= cmp₀ ≫ o(Q) ≫ π[1]`: the sign (`solutionNaiveClass_eq_neg_extClass`).

## Main results

* `Deformation.AlgebraExtension.canonicalNaiveComparison_comp_extClass_of_hom`: `(B3)`, the
  class of an extension of algebras along a morphism of extensions, over two equal structure maps.
* `...RingedToposExtensionProblem.towerCotangentChangeOfBase_comp_neg_extClass`: the square
  `(h₂)`.
* `...RingedToposExtensionProblem.canonicalObstructionClass_eq_neg_extClass_comp_singleδ`: with
  `(h₁)`, the obstruction class of `S` is the boundary of minus the class of `E₁`, for a
  solution of `S` with target changed along the first map of a short exact sequence
  `0 → 𝒢 → 𝒢₂ → 𝒢₁ → 0`.

## References

* [Stacks Project, Tag 07YY](https://stacks.math.columbia.edu/tag/07YY)
* [Stacks Project, Tag 0GQ5](https://stacks.math.columbia.edu/tag/0GQ5)
* [Stacks Project, Tag 08SZ](https://stacks.math.columbia.edu/tag/08SZ)
* [Stacks Project, Remark 0D1P](https://stacks.math.columbia.edu/tag/0D1P)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry (RingedTopos RingedToposHom)
open Stacks.Sheaves.Differentials (underlyingRingSheaf)
open Stacks.Sheaves.ToposPushforward (inverseImageCommRingFunctor)

universe t u v' u' w'

namespace Deformation.AlgebraExtension

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] [HasWeakSheafify J CommRingCat.{u}]
  [J.WEqualsLocallyBijective CommRingCat.{u}] [HasSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [J.HasSheafCompose (forget CommRingCat.{u})]
  [(forget CommRingCat.{u}).ReflectsIsomorphisms]
  {A O : Sheaf J CommRingCat.{u}}
  [HasDerivedCategory.{t} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O))]
  {M N : SheafOfModules.{u} (underlyingRingSheaf O)}

/-- **`(B3)`: the class of an extension of algebras along a morphism of extensions**, over two
equal structure maps `a = a' : 𝒜 ⟶ 𝒪`. Let `P` be an extension of `𝒜`-algebras by `ℳ` over `a`,
`R` one by `𝒩` over `a'`, and `h : 𝒪'_P ⟶ 𝒪'_R` a map over `𝒪`, under `𝒜`, inducing `φ` on the
kernels. Then the class of `R`, read on `L_{𝒪/𝒜}` through the canonical map `L ⟶ NL`, is that of
`P` pushed along `φ`, read through the identification `L_{𝒪/𝒜}(a') = L_{𝒪/𝒜}(a)`. -/
theorem canonicalNaiveComparison_comp_extClass_of_hom {a a' : A ⟶ O} (ha : a = a')
    (P : AlgebraExtension a M) (R : AlgebraExtension a' N) (φ : M ⟶ N)
    (h : P.extension ⟶ R.extension) (hred : h ≫ R.reduction = P.reduction)
    (halg : P.algebraMap ≫ h = R.algebraMap)
    (hker : ∀ (U : Cᵒᵖ) (m : M.val.obj U),
      h.hom.app U (P.incl m) = R.incl ((φ.val.app U m) : N.val.obj U)) :
    DerivedCategory.Q.map (Sheaf.canonicalNaiveComparison.{u, u, u} J a') ≫ extClass R =
      DerivedCategory.Q.map (eqToHom (congrArg (Sheaf.cotangentComplex.{u, u, u} J) ha.symm)) ≫
        DerivedCategory.Q.map (Sheaf.canonicalNaiveComparison.{u, u, u} J a) ≫
          extOneMap φ (extClass P) := by
  subst ha
  rw [eqToHom_refl, CategoryTheory.Functor.map_id, Category.id_comp]
  exact congrArg (_ ≫ ·) (extClass_mapAlong ⟨h, hred, halg, hker⟩)

end Deformation.AlgebraExtension

namespace Deformation.ToposThickening.RingedToposExtensionProblem

variable {X : RingedTopos.{u, u, u}} {B : RingedTopos.{v', u', w'}}
  [X.J.HasSheafCompose (forget RingCat.{u})] [B.J.HasSheafCompose (forget RingCat.{w'})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [B.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [HasWeakSheafify X.J CommRingCat.{u}] [X.J.WEqualsLocallyBijective CommRingCat.{u}]
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [X.J.HasSheafCompose (forget CommRingCat.{u})] [(forget CommRingCat.{u}).ReflectsIsomorphisms]
  [HasDerivedCategory.{t} (Sheaf.targetModules.{u, u, u} X.J X.O)]
  (S : RingedToposExtensionProblem X B)

/-- **`(h₂)`: the class of a solution against an extension over the reduced base.** Let `Q` be a
solution of `S`, `E₁` an extension of `f⁻¹𝒪_B`-algebras by `𝒢₁`, and `h : 𝒪'_Q ⟶ 𝒪'_{E₁}` a map
over `𝒪`, under `f⁻¹𝒪_{B'}` (through `f⁻¹𝒪_{B'} ⟶ f⁻¹𝒪_B`), inducing `π : 𝒢 ⟶ 𝒢₁` on the
kernels. Then the class of `Q` pushed along `π` is the pullback along the change of base of minus
the class of `E₁` on `L_{𝒪/f⁻¹𝒪_B}`. -/
theorem towerCotangentChangeOfBase_comp_neg_extClass (Q : S.CompatibleFirstOrderThickening)
    {G₁ : SheafOfModules.{u} ((sheafCompose X.J (forget₂ CommRingCat.{u} RingCat.{u})).obj X.O)}
    (E₁ : AlgebraExtension (J := X.J) S.f.fSharpInverseImage G₁) (π : S.G ⟶ G₁)
    (h : Q.extension ⟶ E₁.extension) (hred : h ≫ E₁.reduction = Q.reduction)
    (halg : Q.baseMap ≫ h = S.baseReductionInverseImage ≫ E₁.algebraMap)
    (hker : ∀ (U : X.Cᵒᵖ) (m : S.G.val.obj U),
      h.hom.app U (Q.kernelInclusion.val.app U m) = E₁.incl ((π.val.app U m) : G₁.val.obj U)) :
    DerivedCategory.Q.map (Sheaf.towerCotangentChangeOfBase.{u, u, u} X.J
        S.baseReductionInverseImage S.f.fSharpInverseImage) ≫
        (-(DerivedCategory.Q.map (Sheaf.canonicalNaiveComparison.{u, u, u} X.J
            S.f.fSharpInverseImage) ≫ AlgebraExtension.extClass E₁)) =
      S.solutionCotangentClass Q ≫ ((DerivedCategory.singleFunctor _ 0).map π)⟦(1 : ℤ)⟧' := by
  let Q' := (S.solutionEquivSquareZero Q).1
  have hB3 := AlgebraExtension.canonicalNaiveComparison_comp_extClass_of_hom
    S.toThickenedBase_fSharpInverseImage (S.thickenedAlgebraExtension Q')
    (E₁.restrictAlong S.baseReductionInverseImage) π h hred
    (by
      show Q.baseMap ≫ h = S.baseReductionInverseImage ≫ E₁.algebraMap
      exact halg)
    hker
  have hB1 := AlgebraExtension.extClass_restrictAlong S.baseReductionInverseImage E₁
  have e₁ : DerivedCategory.Q.map (Sheaf.towerCotangentChangeOfBase.{u, u, u} X.J
        S.baseReductionInverseImage S.f.fSharpInverseImage) ≫
        (-(DerivedCategory.Q.map (Sheaf.canonicalNaiveComparison.{u, u, u} X.J
            S.f.fSharpInverseImage) ≫ AlgebraExtension.extClass E₁)) =
      -(DerivedCategory.Q.map (Sheaf.canonicalNaiveComparison.{u, u, u} X.J
          (S.baseReductionInverseImage ≫ S.f.fSharpInverseImage)) ≫
        AlgebraExtension.extClass (E₁.restrictAlong S.baseReductionInverseImage)) := by
    rw [Preadditive.comp_neg, ← Functor.map_comp_assoc,
      Sheaf.towerCotangentChangeOfBase_comp_canonicalNaiveComparison, Functor.map_comp,
      Category.assoc, hB1]
  refine e₁.trans ((congrArg Neg.neg hB3).trans ?_)
  rw [solutionCotangentClass, solutionNaiveClass_eq_neg_extClass]
  have key : ∀ {P₁ P₂ P₃ P₄ P₅ : DerivedCategory (Sheaf.targetModules.{u, u, u} X.J X.O)}
      (a : P₁ ⟶ P₂) (b : P₂ ⟶ P₃) (c : P₃ ⟶ P₄) (d : P₄ ⟶ P₅),
      -(a ≫ b ≫ c ≫ d) = (a ≫ b ≫ (-c)) ≫ d := by
    intros
    simp only [Preadditive.comp_neg, Preadditive.neg_comp, Category.assoc]
  exact key _ _ _ _

/-- **The obstruction class of `S` is the boundary of a class over the reduced base.** Let
`0 → 𝒢 → 𝒢₂ → 𝒢₁ → 0` be a short exact sequence of `𝒪`-modules starting at the target module of
`S`, `Q` a solution of `S` with target changed to `𝒢₂` (`S.mapTarget k`), `E₁` an extension of
`f⁻¹𝒪_B`-algebras by `𝒢₁`, and `h : 𝒪'_Q ⟶ 𝒪'_{E₁}` a map over `𝒪`, under `f⁻¹𝒪_{B'}`, inducing
`π` on the kernels. Then the obstruction class `o(S)` of Tag 08V5 is the image of
`−(cmp ≫ ε(E₁)) ∈ Ext¹(L_{𝒪/f⁻¹𝒪_B}, 𝒢₁)` under the connecting map of the short exact sequence.
This is condition (iv) of [Stacks, Tag 07YY] at the level of extension problems. -/
theorem canonicalObstructionClass_eq_neg_extClass_comp_singleδ
    {G₂ G₁ : SheafOfModules.{u} ((sheafCompose X.J (forget₂ CommRingCat.{u} RingCat.{u})).obj X.O)}
    (k : S.G ⟶ G₂) (π : G₂ ⟶ G₁) (hzero : k ≫ π = 0)
    (hSq : (ShortComplex.mk (C := Sheaf.targetModules.{u, u, u} X.J X.O) k π hzero).ShortExact)
    (Q : (S.mapTarget k).CompatibleFirstOrderThickening)
    (E₁ : AlgebraExtension (J := X.J) S.f.fSharpInverseImage G₁)
    (h : Q.extension ⟶ E₁.extension) (hred : h ≫ E₁.reduction = Q.reduction)
    (halg : Q.baseMap ≫ h = S.baseReductionInverseImage ≫ E₁.algebraMap)
    (hker : ∀ (U : X.Cᵒᵖ) (m : G₂.val.obj U),
      h.hom.app U (Q.kernelInclusion.val.app U m) = E₁.incl ((π.val.app U m) : G₁.val.obj U)) :
    S.canonicalObstructionClass =
      ShiftedHom.comp (a := (1 : ℤ))
        (-(DerivedCategory.Q.map (Sheaf.canonicalNaiveComparison.{u, u, u} X.J
            S.f.fSharpInverseImage) ≫ AlgebraExtension.extClass E₁))
        hSq.singleδ (show (1 : ℤ) + 1 = 2 by norm_num) :=
  S.canonicalObstructionClass_eq_comp_singleδ k π hzero hSq
    ((S.mapTarget k).solutionCotangentClass Q) _
    (S.towerCotangentBaseChange_comp_solutionCotangentClass_mapTarget k Q)
    ((S.mapTarget k).towerCotangentChangeOfBase_comp_neg_extClass Q E₁ π h hred halg hker)

end Deformation.ToposThickening.RingedToposExtensionProblem

end
