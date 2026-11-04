module

public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjPoint.AlgebraicSpace
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjPoint.AlgebraHom
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjPoint.PullbackSituation
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjPoint.RestrictionDatum
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjPoint.ShrinkComparison

/-!
# The restrictions of `g^*𝒜` to the scheme points of `X'`

In Situation 0849 let `g : X' ⟶ X` be a morphism of algebraic spaces and let `g^*𝒜` be the
pulled-back algebra (`AlgebraicGeometry.Space.RelativeProjSituation.pullback`).  For a scheme
point `f : T ⟶ X'` the restriction `f^*(g^*𝒜)` of `g^*𝒜` to `T` and the restriction
`(g ∘ f)^*𝒜` of `𝒜` are canonically isomorphic sheaves of graded algebras on `T`; this is the
identification `(g ∘ f')^*𝒜^{(d)} = (f')^*(g^*𝒜)^{(d)}` on which the proof of Stacks 085C rests.
This file constructs that isomorphism and proves that it is compatible with the comparisons
`τ^*(f^*𝒜) ≅ (f ∘ τ)^*𝒜` of the restriction data of Stacks 084A on both sides, which is what makes
it an isomorphism of restriction data.

## Main definitions

* `AlgebraicGeometry.Space.pointPullbackHom`: the comparison `f^*(g^*𝒜) ⟶ (g ∘ f)^*𝒜` on the small
  étale site of a scheme point: the adjoint transpose of the restriction map
  `g^*𝒜 ⟶ f_*((g ∘ f)^*𝒜)`.
* `AlgebraicGeometry.Space.pullbackPointHom`: for a graded algebra `𝒜'` on `X'` identified with
  `g^*𝒜`, the comparison of its restriction to `f` with the restriction of `𝒜` to `g ∘ f`, read on
  the Zariski opens of `T`; for `𝒜'` the re-presented algebra of `s.pullback g` it compares the
  algebras of the restriction data of `s.pullback g` and of `s`.

## Main results

* `AlgebraicGeometry.Space.pointPullbackHom_comp_gradedPullRestriction`: the comparison commutes
  with the restriction maps along a morphism of test objects.
* `AlgebraicGeometry.Space.pointComparison_square`: an étale-level square of restriction maps
  gives the square of the comparisons `τ^*(f^*𝒜) ⟶ (f ∘ τ)^*𝒜`.
* `AlgebraicGeometry.Space.pullbackPointHom_comparison_app`: **the comparison is compatible with
  the comparisons of the two restriction data.**
* `AlgebraicGeometry.Space.isIso_pullbackPointHom_app`: it is an isomorphism in every degree.

## References

* [Stacks Project, Tag 085C](https://stacks.math.columbia.edu/tag/085C)
* [Stacks Project, Tag 084A](https://stacks.math.columbia.edu/tag/084A)
* [Stacks Project, Tag 0FQX](https://stacks.math.columbia.edu/tag/0FQX)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite
open Stacks.Sheaves.GradedAlgebraEssentiallySmall (gradedPull gradedPush gradedAdj)
open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf (situationAlgebra)

universe u m

namespace CategoryTheory.Adjunction

/-- **The transposed units along a composite commute with the transposed units along a further
morphism.**  For adjunctions `a_g`, `a_p`, `a_q`, `a_{p'}`, `a_{q'}` and comparisons of right
adjoints `R_p ⋙ R_g ≅ R_q`, `R_φ ⋙ R_p ≅ R_{p'}`, `R_{p'} ⋙ R_g ≅ R_{q'}`, `R_φ ⋙ R_q ≅ R_{q'}`
satisfying the associativity law, the transpose along `a_p` of the transposed unit for
`R_p ⋙ R_g ≅ R_q`, followed by the transposed unit for `R_φ ⋙ R_q ≅ R_{q'}`, is the transposed
unit for `R_φ ⋙ R_p ≅ R_{p'}` followed by `R_φ` of the transpose along `a_{p'}` of the transposed
unit for `R_{p'} ⋙ R_g ≅ R_{q'}`.  This is `CategoryTheory.Adjunction.unitTranspose_comp`
transposed along `a_p`. -/
theorem homEquiv_symm_unitTranspose_comp {C₀ C₁ C₂ C₃ : Type*} [Category* C₀] [Category* C₁]
    [Category* C₂] [Category* C₃] {Lg : C₀ ⥤ C₁} {Rg : C₁ ⥤ C₀} {Lp : C₁ ⥤ C₂} {Rp : C₂ ⥤ C₁}
    {Lq : C₀ ⥤ C₂} {Rq : C₂ ⥤ C₀} {Lp' : C₁ ⥤ C₃} {Rp' : C₃ ⥤ C₁} {Lq' : C₀ ⥤ C₃}
    {Rq' : C₃ ⥤ C₀} (Rφ : C₃ ⥤ C₂) (ag : Lg ⊣ Rg) (ap : Lp ⊣ Rp) (aq : Lq ⊣ Rq)
    (ap' : Lp' ⊣ Rp') (aq' : Lq' ⊣ Rq') (epg : Rp ⋙ Rg ≅ Rq) (eφp : Rφ ⋙ Rp ≅ Rp')
    (ep'g : Rp' ⋙ Rg ≅ Rq') (eφq : Rφ ⋙ Rq ≅ Rq')
    (h : Functor.isoWhiskerLeft Rφ epg ≪≫ eφq =
      (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight eφp _ ≪≫ ep'g) (A : C₀) :
    (ap.homEquiv _ _).symm (unitTranspose ag aq Rp epg A) ≫ unitTranspose aq aq' Rφ eφq A =
      unitTranspose ap ap' Rφ eφp (Lg.obj A) ≫
        Rφ.map ((ap'.homEquiv _ _).symm (unitTranspose ag aq' Rp' ep'g A)) := by
  have hc' := congrArg (ap.homEquiv _ _).symm
    (unitTranspose_comp Rp Rφ Rp' ag aq aq' epg eφp ep'g eφq h A)
  rw [homEquiv_naturality_right_symm] at hc'
  rw [← hc']
  have hu : ap'.unit.app (Lg.obj A) ≫ Rp'.map ((ap'.homEquiv _ _).symm
      (unitTranspose ag aq' Rp' ep'g A)) = unitTranspose ag aq' Rp' ep'g A :=
    (ap'.homEquiv_unit _ _ _).symm.trans (Equiv.apply_symm_apply _ _)
  have hn := eφp.inv.naturality ((ap'.homEquiv _ _).symm (unitTranspose ag aq' Rp' ep'g A))
  simp only [Functor.comp_map] at hn
  conv_lhs => rw [← hu, Category.assoc, hn, ← Category.assoc, homEquiv_naturality_right_symm]
  rfl

/-- **Transposes of a natural square.**  For an adjunction `L ⊣ G`, functors `P`, `Q`, `M` and a
natural transformation `Z : M ⋙ P ⟶ Q ⋙ G`, morphisms `r₁ : a₁ ⟶ M b₁` and `r₂ : a₂ ⟶ M b₂` whose
square with `x : a₁ ⟶ a₂` and `M y` commutes give transposes of `P r ≫ Z` whose square with
`L (P x)` and `Q y` commutes. -/
theorem homEquiv_symm_square {C D E E' : Type*} [Category* C] [Category* D] [Category* E]
    [Category* E'] {L : C ⥤ D} {G : D ⥤ C} (adj : L ⊣ G) (P : E ⥤ C) (Q : E' ⥤ D) (M : E' ⥤ E)
    (Z : M ⋙ P ⟶ Q ⋙ G) {a₁ a₂ : E} {b₁ b₂ : E'} (x : a₁ ⟶ a₂) (y : b₁ ⟶ b₂)
    (r₁ : a₁ ⟶ M.obj b₁) (r₂ : a₂ ⟶ M.obj b₂) (h : x ≫ r₂ = r₁ ≫ M.map y)
    (c₁ : L.obj (P.obj a₁) ⟶ Q.obj b₁) (c₂ : L.obj (P.obj a₂) ⟶ Q.obj b₂)
    (hc₁ : c₁ = (adj.homEquiv _ _).symm (P.map r₁ ≫ Z.app b₁))
    (hc₂ : c₂ = (adj.homEquiv _ _).symm (P.map r₂ ≫ Z.app b₂)) :
    L.map (P.map x) ≫ c₂ = c₁ ≫ Q.map y := by
  subst hc₁ hc₂
  rw [← homEquiv_naturality_left_symm, ← homEquiv_naturality_right_symm, ← Category.assoc,
    ← P.map_comp, h, P.map_comp, Category.assoc, Category.assoc]
  congr 2
  exact Z.naturality y

/-- If `x ≫ c = c' ≫ y` with `c` and `c'` invertible, then `c'⁻¹ ≫ x = y ≫ c⁻¹`. -/
theorem _root_.CategoryTheory.inv_comp_eq_comp_inv_of_comp_eq {C : Type*} [Category* C]
    {a b c₀ d : C} {x : a ⟶ b} {c : b ⟶ d} {c' : a ⟶ c₀} {y : c₀ ⟶ d} [IsIso c] [IsIso c']
    (h : x ≫ c = c' ≫ y) : inv c' ≫ x = y ≫ inv c := by
  rw [IsIso.inv_comp_eq, ← Category.assoc, ← h, Category.assoc, IsIso.hom_inv_id,
    Category.comp_id]

/-- Two commuting squares paste: if `σ ≫ r₂ = r₃ ≫ M σ'` and `c ≫ r = r₂ ≫ M c'`, then
`(σ ≫ c) ≫ r = r₃ ≫ M (σ' ≫ c')`. -/
theorem _root_.CategoryTheory.comp_comp_eq_of_squares {C D : Type*} [Category* C] [Category* D]
    (M : D ⥤ C) {a b c₀ : C} {a' b' c₀' : D} {σ : a ⟶ b} {c : b ⟶ c₀} {r : c₀ ⟶ M.obj c₀'}
    {r₂ : b ⟶ M.obj b'} {r₃ : a ⟶ M.obj a'} {σ' : a' ⟶ b'} {c' : b' ⟶ c₀'}
    (hσ : σ ≫ r₂ = r₃ ≫ M.map σ') (hc : c ≫ r = r₂ ≫ M.map c') :
    (σ ≫ c) ≫ r = r₃ ≫ M.map (σ' ≫ c') := by
  rw [Category.assoc, hc, ← Category.assoc, hσ, Category.assoc, Functor.map_comp]

/-- Rewriting the two outer morphisms of a commuting square along equalities. -/
theorem _root_.CategoryTheory.map_comp_eq_comp_of_eq {C D : Type*} [Category* C] [Category* D]
    (L : C ⥤ D) {a a' : C} {b b' : D} {x x' : a ⟶ a'} {c₁ : L.obj a ⟶ b} {c₂ : L.obj a' ⟶ b'}
    {y y' : b ⟶ b'} (hx : x = x') (hy : y = y') (h : L.map x' ≫ c₂ = c₁ ≫ y') :
    L.map x ≫ c₂ = c₁ ≫ y := by
  subst hx hy
  exact h

end CategoryTheory.Adjunction

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

section Etale

variable {X X' P P' : AlgebraicSpaces B S hS}

/-- **The transposed restriction maps along a composite `p ≫ g` commute with the restriction
maps along `φ`.**  Writing `c_p : p^*(g^*𝒜) ⟶ (p ≫ g)^*𝒜` for the adjoint transpose of the
restriction map along `p`, the square
`c_p ≫ (restriction along φ of 𝒜) = (restriction along φ of g^*𝒜) ≫ φ_* c_{φ ≫ p}` commutes.
This is the cocycle law `AlgebraicGeometry.Space.gradedPullRestriction_comp`, transposed along
`p^* ⊣ p_*`. -/
theorem homEquiv_symm_gradedPullRestriction_comp (φ : P' ⟶ P) (p : P ⟶ X') (p' : P' ⟶ X')
    (g : X' ⟶ X) (q : P ⟶ X) (q' : P' ⟶ X) (hp : φ ≫ p = p') (hq : p ≫ g = q)
    (hq' : p' ≫ g = q') (hφq : φ ≫ q = q')
    (A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf B S hS X)) :
    ((gradedAdj (X := smallEtaleRingedTopos B S hS P) (Y := smallEtaleRingedTopos B S hS X')
        (smallEtaleRingedToposHom B S hS p)).homEquiv _ _).symm
        (gradedPullRestriction p g q hq A) ≫ gradedPullRestriction φ q q' hφq A =
      gradedPullRestriction φ p p' hp
          ((gradedPull (X := smallEtaleRingedTopos B S hS X') (Y := smallEtaleRingedTopos B S hS X)
            (smallEtaleRingedToposHom B S hS g)).obj A) ≫
        (gradedPush (X := smallEtaleRingedTopos B S hS P') (Y := smallEtaleRingedTopos B S hS P)
          (smallEtaleRingedToposHom B S hS φ)).map
          (((gradedAdj (X := smallEtaleRingedTopos B S hS P') (Y := smallEtaleRingedTopos B S hS X')
            (smallEtaleRingedToposHom B S hS p')).homEquiv _ _).symm
            (gradedPullRestriction p' g q' hq' A)) := by
  subst hp hq hq'
  exact Adjunction.homEquiv_symm_unitTranspose_comp _ _ _ _ _ _ _ _ _ _
    (gradedAlgebraPushforwardCompIso_assoc B S hS φ p g) A

end Etale

section Point

variable {X X' : AlgebraicSpaces B S hS}

/-- **The comparison `f^*(g^*𝒜) ⟶ (g ∘ f)^*𝒜`** on the small étale site of a scheme point
`f : T ⟶ X'`: the adjoint transpose, along `f^* ⊣ f_*`, of the restriction map
`g^*𝒜 ⟶ f_*((g ∘ f)^*𝒜)`.  It is an isomorphism in every degree
(`AlgebraicGeometry.Space.isIso_gradedPullRestriction_transpose_app`). -/
def pointPullbackHom (g : X' ⟶ X)
    (A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf B S hS X))
    (T : BigFppfOver B S hS) (f : yoneda.obj T ⟶ X'.1) :
    etalePointAlgebra ((gradedPull (X := smallEtaleRingedTopos B S hS X')
        (Y := smallEtaleRingedTopos B S hS X) (smallEtaleRingedToposHom B S hS g)).obj A) T f ⟶
      etalePointAlgebra A T (f ≫ g.hom) :=
  ((gradedAdj (X := smallEtaleRingedTopos B S hS (yonedaSpace B S hS T))
      (Y := smallEtaleRingedTopos B S hS X')
      (smallEtaleRingedToposHom B S hS (pointHom f))).homEquiv _ _).symm
    (gradedPullRestriction (pointHom f) g (pointHom (f ≫ g.hom)) rfl A)

/-- The comparison is an isomorphism in every degree. -/
instance isIso_pointPullbackHom_app (g : X' ⟶ X)
    (A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf B S hS X))
    (T : BigFppfOver B S hS) (f : yoneda.obj T ⟶ X'.1) (n : ℤ) :
    IsIso ((pointPullbackHom g A T f).app n) :=
  isIso_gradedPullRestriction_transpose_app (pointHom f) g (pointHom (f ≫ g.hom)) rfl A n

/-- **The comparison commutes with the restriction maps along a morphism of test objects.** -/
theorem pointPullbackHom_comp_gradedPullRestriction (g : X' ⟶ X)
    (A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf B S hS X))
    {T T' : BigFppfOver B S hS} (τ : T' ⟶ T) (f : yoneda.obj T ⟶ X'.1)
    (f' : yoneda.obj T' ⟶ X'.1) (hf : yoneda.map τ ≫ f = f') :
    pointPullbackHom g A T f ≫ gradedPullRestriction (representedSpaceMap B S hS τ)
        (pointHom (f ≫ g.hom)) (pointHom (f' ≫ g.hom))
        (pointHom_comp τ (by rw [← hf, Category.assoc])) A =
      gradedPullRestriction (representedSpaceMap B S hS τ) (pointHom f) (pointHom f')
          (pointHom_comp τ hf) _ ≫
        (gradedPush (X := smallEtaleRingedTopos B S hS (yonedaSpace B S hS T'))
          (Y := smallEtaleRingedTopos B S hS (yonedaSpace B S hS T))
          (smallEtaleRingedToposHom B S hS (representedSpaceMap B S hS τ))).map
          (pointPullbackHom g A T' f') :=
  homEquiv_symm_gradedPullRestriction_comp (representedSpaceMap B S hS τ) (pointHom f)
    (pointHom f') g (pointHom (f ≫ g.hom)) (pointHom (f' ≫ g.hom)) (pointHom_comp τ hf) rfl rfl
    _ A

end Point

section Square

variable {X₁ X₂ : AlgebraicSpaces B S hS}

open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf (ringedSpaceHom)

/-- **An étale-level square of restriction maps gives the square of the comparisons
`τ^*(f^*𝒜) ⟶ (f ∘ τ)^*𝒜`.**  For graded algebras `A₁` on `X₁` and `A₂` on `X₂`, scheme points
`f₁, f₁'` of `X₁` and `f₂, f₂'` of `X₂` over `τ : T' ⟶ T`, and homomorphisms `x` at `T` and `y`
at `T'` between the étale restrictions which commute with the restriction maps along `τ`, the
Zariski readings of `x` and `y` commute with the comparisons of the two restriction data. -/
theorem pointComparison_square (A₁ : SheafOfModules.GradedAlgebra.{u, u}
      (structureRingSheaf B S hS X₁))
    (A₂ : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf B S hS X₂))
    {T T' : BigFppfOver B S hS} (τ : T' ⟶ T) (f₁ : yoneda.obj T ⟶ X₁.1)
    (f₁' : yoneda.obj T' ⟶ X₁.1) (hf₁ : yoneda.map τ ≫ f₁ = f₁') (f₂ : yoneda.obj T ⟶ X₂.1)
    (f₂' : yoneda.obj T' ⟶ X₂.1) (hf₂ : yoneda.map τ ≫ f₂ = f₂')
    (x : etalePointAlgebra A₁ T f₁ ⟶ etalePointAlgebra A₂ T f₂)
    (y : etalePointAlgebra A₁ T' f₁' ⟶ etalePointAlgebra A₂ T' f₂')
    (h : x ≫ gradedPullRestriction (representedSpaceMap B S hS τ) (pointHom f₂) (pointHom f₂')
        (pointHom_comp τ hf₂) A₂ =
      gradedPullRestriction (representedSpaceMap B S hS τ) (pointHom f₁) (pointHom f₁')
          (pointHom_comp τ hf₁) A₁ ≫
        (gradedPush (X := smallEtaleRingedTopos B S hS (yonedaSpace B S hS T'))
          (Y := smallEtaleRingedTopos B S hS (yonedaSpace B S hS T))
          (smallEtaleRingedToposHom B S hS (representedSpaceMap B S hS τ))).map y) (n : ℤ) :
    (Stacks.RingedSpace.pullbackFunctor (ringedSpaceHom ((BigFppfOver.toScheme B S hS).map τ))).map
        ((SheafOfModules.pushforward (selfOpensStructureMap B S hS T)).map (x.app n)) ≫
      (pointComparison A₂ τ f₂ f₂' hf₂).app n =
    (pointComparison A₁ τ f₁ f₁' hf₁).app n ≫
      (SheafOfModules.pushforward (selfOpensStructureMap B S hS T')).map (y.app n) := by
  let adj := Stacks.RingedSpace.pullbackAdjunction
    (ringedSpaceHom ((BigFppfOver.toScheme B S hS).map τ))
  have e : ∀ {X : AlgebraicSpaces B S hS} (A : SheafOfModules.GradedAlgebra.{u, u}
      (structureRingSheaf B S hS X)) (f : yoneda.obj T ⟶ X.1) (f' : yoneda.obj T' ⟶ X.1)
      (hf : yoneda.map τ ≫ f = f'), (pointComparison A τ f f' hf).app n = (adj.homEquiv _ _).symm
      ((SheafOfModules.pushforward (selfOpensStructureMap B S hS T)).map
          (gradedPullRestrictionApp (representedSpaceMap B S hS τ) (pointHom f) (pointHom f')
            (pointHom_comp τ hf) A n) ≫
        (zariskiDirectImageNatTrans τ).app ((etalePointAlgebra A T' f').piece n)) :=
    fun _ _ _ _ => rfl
  exact Adjunction.homEquiv_symm_square adj _ _ _ (zariskiDirectImageNatTrans τ)
    (x.app n) (y.app n) _ _ (congrArg (fun k => SheafOfModules.GradedAlgebra.Hom.app k n) h) _ _
    (e A₁ f₁ f₁' hf₁) (e A₂ f₂ f₂' hf₂)

/-- `AlgebraicGeometry.Space.pointComparison_square`, with the Zariski readings of `x` and `y`
written as homomorphisms of sheaves of graded algebras. -/
theorem pointComparison_square_unitalHom (A₁ : SheafOfModules.GradedAlgebra.{u, u}
      (structureRingSheaf B S hS X₁))
    (A₂ : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf B S hS X₂))
    {T T' : BigFppfOver B S hS} (τ : T' ⟶ T) (f₁ : yoneda.obj T ⟶ X₁.1)
    (f₁' : yoneda.obj T' ⟶ X₁.1) (hf₁ : yoneda.map τ ≫ f₁ = f₁') (f₂ : yoneda.obj T ⟶ X₂.1)
    (f₂' : yoneda.obj T' ⟶ X₂.1) (hf₂ : yoneda.map τ ≫ f₂ = f₂')
    (x : etalePointAlgebra A₁ T f₁ ⟶ etalePointAlgebra A₂ T f₂)
    (y : etalePointAlgebra A₁ T' f₁' ⟶ etalePointAlgebra A₂ T' f₂')
    (h : x ≫ gradedPullRestriction (representedSpaceMap B S hS τ) (pointHom f₂) (pointHom f₂')
        (pointHom_comp τ hf₂) A₂ =
      gradedPullRestriction (representedSpaceMap B S hS τ) (pointHom f₁) (pointHom f₁')
          (pointHom_comp τ hf₁) A₁ ≫
        (gradedPush (X := smallEtaleRingedTopos B S hS (yonedaSpace B S hS T'))
          (Y := smallEtaleRingedTopos B S hS (yonedaSpace B S hS T))
          (smallEtaleRingedToposHom B S hS (representedSpaceMap B S hS τ))).map y) (n : ℤ)
    (x₀ : SheafOfModules.GradedAlgebra.UnitalHom (zariskiReading T (etalePointAlgebra A₁ T f₁))
      (zariskiReading T (etalePointAlgebra A₂ T f₂)))
    (y₀ : SheafOfModules.GradedAlgebra.UnitalHom (zariskiReading T' (etalePointAlgebra A₁ T' f₁'))
      (zariskiReading T' (etalePointAlgebra A₂ T' f₂')))
    (hx : x₀.app n = (SheafOfModules.pushforward (selfOpensStructureMap B S hS T)).map (x.app n))
    (hy : y₀.app n = (SheafOfModules.pushforward (selfOpensStructureMap B S hS T')).map (y.app n)) :
    (Stacks.RingedSpace.pullbackFunctor (ringedSpaceHom ((BigFppfOver.toScheme B S hS).map τ))).map
        (x₀.app n) ≫ (pointComparison A₂ τ f₂ f₂' hf₂).app n =
    (pointComparison A₁ τ f₁ f₁' hf₁).app n ≫ y₀.app n := by
  rw [hx, hy]
  exact pointComparison_square A₁ A₂ τ f₁ f₁' hf₁ f₂ f₂' hf₂ x y h n

end Square

section Comparison

variable {X X' : AlgebraicSpaces B S hS} (g : X' ⟶ X)
  (A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf B S hS X))
  {A' : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf B S hS X')}
  (σ : A' ≅ (gradedPull (X := smallEtaleRingedTopos B S hS X')
    (Y := smallEtaleRingedTopos B S hS X) (smallEtaleRingedToposHom B S hS g)).obj A)

/-- **The comparison of the restrictions of `𝒜'` and of `𝒜`**, before the Zariski reading, for a
graded algebra `𝒜'` on `X'` identified with `g^*𝒜` by `σ`: at a scheme point `f : T ⟶ X'`, the
étale restriction of `𝒜'` at `f` is identified with that of `g^*𝒜` (`σ`), and then with the étale
restriction of `𝒜` at `g ∘ f` (`AlgebraicGeometry.Space.pointPullbackHom`). -/
def pullbackEtalePointHom (T : BigFppfOver B S hS)
    (f : yoneda.obj T ⟶ X'.1) :
    etalePointAlgebra A' T f ⟶ etalePointAlgebra A T (f ≫ g.hom) :=
  (gradedPull (X := smallEtaleRingedTopos B S hS
      (yonedaSpace B S hS T))
    (Y := smallEtaleRingedTopos B S hS X')
    (smallEtaleRingedToposHom B S hS (pointHom f))).map
      σ.hom ≫ pointPullbackHom g A T f

/-- **The étale-level comparison commutes with the restriction maps** along a morphism of test
objects: the identification of the re-presented algebra with `g^*𝒜` is natural, and the
comparison `f^*(g^*𝒜) ⟶ (g ∘ f)^*𝒜` commutes with restriction by
`AlgebraicGeometry.Space.pointPullbackHom_comp_gradedPullRestriction`. -/
theorem pullbackEtalePointHom_comp_gradedPullRestriction
    {T T' : BigFppfOver B S hS} (τ : T' ⟶ T) (f : yoneda.obj T ⟶ X'.1)
    (hτ : yoneda.map τ ≫ f ≫ g.hom = (yoneda.map τ ≫ f) ≫ g.hom) :
    pullbackEtalePointHom g A σ T f ≫ gradedPullRestriction
        (representedSpaceMap B S hS τ) (pointHom (f ≫ g.hom))
        (pointHom ((yoneda.map τ ≫ f) ≫ g.hom)) (pointHom_comp τ hτ) A =
      gradedPullRestriction (representedSpaceMap B S hS τ) (pointHom f)
          (pointHom (yoneda.map τ ≫ f)) (pointHom_comp τ rfl) A' ≫
        (gradedPush (X := smallEtaleRingedTopos B S hS
            (yonedaSpace B S hS T'))
          (Y := smallEtaleRingedTopos B S hS
            (yonedaSpace B S hS T))
          (smallEtaleRingedToposHom B S hS
            (representedSpaceMap B S hS τ))).map
          (pullbackEtalePointHom g A σ T' (yoneda.map τ ≫ f)) :=
  comp_comp_eq_of_squares _
    (gradedPullRestriction_naturality (representedSpaceMap B S hS τ)
      (pointHom f) (pointHom (yoneda.map τ ≫ f)) (pointHom_comp τ rfl) σ.hom)
    (pointPullbackHom_comp_gradedPullRestriction g A τ f (yoneda.map τ ≫ f) rfl)

/-- The étale-level comparison is an isomorphism in every degree. -/
theorem isIso_pullbackEtalePointHom_app (T : BigFppfOver B S hS)
    (f : yoneda.obj T ⟶ X'.1) (n : ℤ) : IsIso ((pullbackEtalePointHom g A σ T f).app n) :=
  IsIso.comp_isIso'
    (SheafOfModules.GradedAlgebra.isIso_hom_app
      ((gradedPull (X := smallEtaleRingedTopos B S hS (yonedaSpace B S hS T))
        (Y := smallEtaleRingedTopos B S hS X')
        (smallEtaleRingedToposHom B S hS (pointHom f))).mapIso σ) n)
    (isIso_pointPullbackHom_app g A T f n)

/-- **The comparison of the restriction of `𝒜' ≅ g^*𝒜` to a scheme point `f : T ⟶ X'` with the
restriction of `𝒜` to `g ∘ f`**, as sheaves of graded algebras on the scheme of `T`: the Zariski
reading of `AlgebraicGeometry.Space.pullbackEtalePointHom`. -/
def pullbackPointHom (T : BigFppfOver B S hS) (f : yoneda.obj T ⟶ X'.1) :
    SheafOfModules.GradedAlgebra.UnitalHom
      (zariskiReading T (etalePointAlgebra A' T f))
      (zariskiReading T (etalePointAlgebra A T (f ≫ g.hom))) :=
  haveI := isContinuous_selfOpensFunctor B S hS T
  @SheafOfModules.GradedAlgebra.UnitalHom.ofHomOfIsIso _ _ _ _ _ _
    (SheafOfModules.GradedAlgebra.Hom.pushforward
      (selfOpensStructureMap B S hS T) (pullbackEtalePointHom g A σ T f))
    (@Functor.map_isIso _ _ _ _ _ _ (SheafOfModules.pushforward
      (selfOpensStructureMap B S hS T)) _
      (isIso_pullbackEtalePointHom_app g A σ T f 0))

/-- In degree `n`, `pullbackPointHom` is the pushforward to the Zariski site of `T` of the degree
`n` component of `pullbackEtalePointHom`. -/
theorem pullbackPointHom_app (T : BigFppfOver B S hS)
    (f : yoneda.obj T ⟶ X'.1) (n : ℤ) :
    haveI := isContinuous_selfOpensFunctor B S hS T
    (pullbackPointHom g A σ T f).app n =
      (SheafOfModules.pushforward (selfOpensStructureMap B S hS T)).map
        ((pullbackEtalePointHom g A σ T f).app n) :=
  rfl

/-- **The comparison is an isomorphism in every degree.** -/
instance isIso_pullbackPointHom_app (T : BigFppfOver B S hS)
    (f : yoneda.obj T ⟶ X'.1) (n : ℤ) : IsIso ((pullbackPointHom g A σ T f).app n) :=
  haveI := isContinuous_selfOpensFunctor B S hS T
  @Functor.map_isIso _ _ _ _ _ _ (SheafOfModules.pushforward
    (selfOpensStructureMap B S hS T)) _
    (isIso_pullbackEtalePointHom_app g A σ T f n)

/-- **The comparison is compatible with the comparisons of the restriction data of Stacks 084A
on both sides**, degreewise: for a morphism `τ : T' ⟶ T` of test objects, the inverse image along
`τ` of the comparison at `T`, followed by the comparison `τ^*((g ∘ f)^*𝒜) ⟶ (g ∘ f ∘ τ)^*𝒜` of
the restriction datum of `𝒜`, is the comparison `τ^*(f^*(g^*𝒜)) ⟶ (f ∘ τ)^*(g^*𝒜)` of the
restriction datum of `g^*𝒜` followed by the comparison at `T'`. -/
theorem pullbackPointHom_comparison_app {T T' : BigFppfOver B S hS}
    (τ : T' ⟶ T) (f : yoneda.obj T ⟶ X'.1)
    (hτ : yoneda.map τ ≫ f ≫ g.hom = (yoneda.map τ ≫ f) ≫ g.hom) (n : ℤ) :
    (Stacks.RingedSpace.pullbackFunctor
        (Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.ringedSpaceHom
          ((BigFppfOver.toScheme B S hS).map τ))).map
        ((pullbackPointHom g A σ T f).app n) ≫
      (pointComparison A τ (f ≫ g.hom) ((yoneda.map τ ≫ f) ≫ g.hom) hτ).app n =
    (pointComparison A' τ f (yoneda.map τ ≫ f) rfl).app n ≫
      (pullbackPointHom g A σ T' (yoneda.map τ ≫ f)).app n :=
  pointComparison_square_unitalHom A' A τ f
    (yoneda.map τ ≫ f) rfl (f ≫ g.hom) ((yoneda.map τ ≫ f) ≫ g.hom) hτ
    (pullbackEtalePointHom g A σ T f) (pullbackEtalePointHom g A σ T' (yoneda.map τ ≫ f))
    (pullbackEtalePointHom_comp_gradedPullRestriction g A σ τ f hτ) n _ _
    (pullbackPointHom_app g A σ T f n) (pullbackPointHom_app g A σ T' _ n)

/-- **The comparison is compatible with the restriction maps of the two restriction data**, as
an equation of unital homomorphisms: the restriction map `(f ∘ τ)^*(g^*𝒜) ⟶ τ^*(f^*(g^*𝒜))` (the
inverse of the comparison of `AlgebraicGeometry.Space.pointComparison`) followed by the inverse
image of the comparison at `T`, is the comparison at `T'` followed by the restriction map
`(g ∘ f ∘ τ)^*𝒜 ⟶ τ^*((g ∘ f)^*𝒜)`. -/
theorem pullbackPointHom_restrict (hA : ∀ n, (A.piece n).IsQuasicoherentOnSite)
    (hA' : ∀ n, (A'.piece n).IsQuasicoherentOnSite) {T T' : BigFppfOver B S hS} (τ : T' ⟶ T)
    (f : yoneda.obj T ⟶ X'.1) (hτ : yoneda.map τ ≫ f ≫ g.hom = (yoneda.map τ ≫ f) ≫ g.hom) :
    haveI : ∀ n, IsIso ((@SheafOfModules.GradedAlgebra.UnitalHom.ofHomOfIsIso _ _ _ _ _ _
        (pointComparison A' τ f (yoneda.map τ ≫ f) rfl)
        (isIso_pointComparison_app A' hA' τ f _ rfl 0)).app n) :=
      fun n => isIso_pointComparison_app A' hA' τ f _ rfl n
    haveI : ∀ n, IsIso ((@SheafOfModules.GradedAlgebra.UnitalHom.ofHomOfIsIso _ _ _ _ _ _
        (pointComparison A τ (f ≫ g.hom) ((yoneda.map τ ≫ f) ≫ g.hom) hτ)
        (isIso_pointComparison_app A hA τ _ _ hτ 0)).app n) :=
      fun n => isIso_pointComparison_app A hA τ _ _ hτ n
    (@SheafOfModules.GradedAlgebra.UnitalHom.ofHomOfIsIso _ _ _ _ _ _
        (pointComparison A' τ f (yoneda.map τ ≫ f) rfl)
        (isIso_pointComparison_app A' hA' τ f _ rfl 0)).inverse.comp
        (Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.baseAlgebraMapHom
          ((BigFppfOver.toScheme B S hS).map τ) (pullbackPointHom g A σ T f)) =
      (pullbackPointHom g A σ T' (yoneda.map τ ≫ f)).comp
        (@SheafOfModules.GradedAlgebra.UnitalHom.ofHomOfIsIso _ _ _ _ _ _
          (pointComparison A τ (f ≫ g.hom) ((yoneda.map τ ≫ f) ≫ g.hom) hτ)
          (isIso_pointComparison_app A hA τ _ _ hτ 0)).inverse := by
  refine SheafOfModules.GradedAlgebra.UnitalHom.ext fun n => ?_
  exact @inv_comp_eq_comp_inv_of_comp_eq _ _ _ _ _ _ _ _ _ _
    (isIso_pointComparison_app A hA τ _ _ hτ n) (isIso_pointComparison_app A' hA' τ f _ rfl n)
    (pullbackPointHom_comparison_app g A σ τ f hτ n)

end Comparison

end AlgebraicGeometry.Space

end
