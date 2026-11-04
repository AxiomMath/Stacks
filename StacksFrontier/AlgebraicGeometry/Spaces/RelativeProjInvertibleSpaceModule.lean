module

public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjInvertibleSpace
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjInvertibleSquareUnital
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjPoint.ZariskiReadingLaurent
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjPoint.PullbackPointAlgebra
public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.QuadrupleUnique

/-!
# Stacks 0D2Z for a real pair `(ℒ, ψ)` on an algebraic space

Let `f : X ⟶ Y` be a morphism of algebraic spaces towards the algebraic space `Y` of
Situation 0849, `ℒ` an invertible `𝒪_X`-module on the small étale site of `X` and
`ψ : f^*𝒜 ⟶ ⨁_{n ∈ ℤ} ℒ^{⊗ n}` a unital homomorphism of sheaves of graded algebras on the small
étale site of `X`. This file restricts `(ℒ, ψ)` to the scheme points of `X`, producing the datum
`AlgebraicGeometry.Space.RelativeProjSituation.InvertibleTwistingRestriction` through which
Stacks 0D2Z is formalized for `X` an algebraic space, and restates the open subspace `U(ψ)`, the
morphism `r_{ℒ,ψ}`, clause (2) and clause (3) for the pair `(ℒ, ψ)` itself.

At a scheme point `x : T ⟶ X` the restriction of `ℒ` is the Zariski reading `x^*ℒ` of its
étale pullback (`AlgebraicGeometry.Space.pointLine`), and the restriction of `ψ` is the composite
`(f ∘ x)^*𝒜 ≅ x^*(f^*𝒜) ⟶ x^*(⨁ ℒ^{⊗ n}) ≅ ⨁ (x^*ℒ)^{⊗ n}` of the comparison of
`AlgebraicGeometry.Space.pullbackPointHom`, the restriction of `ψ` and the identification of the
restricted Laurent algebra (`AlgebraicGeometry.Space.pointLaurentHom`). Along a morphism
`τ : T' ⟶ T` of test schemes the identification `τ^*(x^*ℒ) ≅ (x ∘ τ)^*ℒ` is the degree-one
component of the comparison of the restricted Laurent algebras; a homomorphism between Laurent
algebras is determined by its degree-one component, which makes the comparison the Laurent
algebra map of that identification, and so `(x ∘ τ)^*ψ` is the pullback of `x^*ψ`.

## Main definitions

* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.laurentPullbackGradedHom`: the comparison
  `g^*(⨁ ℒ^{⊗ n}) ⟶ ⨁ (g^*ℒ)^{⊗ n}` as a homomorphism of sheaves of graded algebras.
* `AlgebraicGeometry.Space.pointLineIso`: the identification `τ^*(x^*ℒ) ≅ (x ∘ τ)^*ℒ`.
* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.isoOfLaurentHom`: the isomorphism of invertible
  modules read off the degree-one component of a homomorphism of their Laurent algebras.
* `AlgebraicGeometry.Space.pointPsi`: the restriction `x^*ψ`.
* `AlgebraicGeometry.Space.RelativeProjSituation.pointTwisting`: `x^*ψ` as the map of a quadruple.
* `AlgebraicGeometry.Space.RelativeProjSituation.InvertibleTwistingRestriction.ofUnitalHom`:
  **the restriction datum of a pair `(ℒ, ψ)` on the algebraic space `X`.**

## Main results

* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.laurentHom_app_eq_congrIso_inv`: a homomorphism
  of Laurent algebras with invertible degree-one component is the Laurent algebra map of the
  isomorphism it induces.
* `AlgebraicGeometry.Space.pointComparison_comp_pointLaurentHom_app`: the identifications of the
  restricted Laurent algebras are compatible with the restriction maps.
* `AlgebraicGeometry.Space.pointComparison_comp_pointPsi_app`: `(x ∘ τ)^*ψ` is the pullback of
  `x^*ψ`.
* `AlgebraicGeometry.Space.RelativeProjSituation.pointTwisting_map`: the same, for the maps of the
  quadruples.
* The statements of Stacks 0D2Z for the pair `(ℒ, ψ)`, in the namespace
  `AlgebraicGeometry.Space.RelativeProjSituation.InvertibleTwistingRestriction`:
  `isOpenSubspace_locus_ofUnitalHom`, `invertibleMorphism_comp_π_ofUnitalHom`,
  `mem_locus_ofUnitalHom_of_epi` (2)(a), `factor_invertibleMorphism_ofUnitalHom_of_epi` (2)(b),
  `eq_invertibleMorphism_ofUnitalHom` (characterized by (2)) and
  `invertibleMorphism_baseChange_square_ofUnitalHom` (3).

`θ` and clause (1) for `X` an algebraic space are not stated here: they need the twists
`𝒪_P(d)` on the algebraic space `P = Proj_Y(𝒜)` (Stacks 084D).

## References

* [Stacks Project, Tag 0D2Z](https://stacks.math.columbia.edu/tag/0D2Z)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
* [Stacks Project, Tag 084A](https://stacks.math.columbia.edu/tag/084A)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
open AlgebraicGeometry
open Stacks.RingedSpace
open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf

universe u m

namespace Stacks.AlgebraicGeometry.RelativeProjQcohSheaf

attribute [local instance] Stacks.PullbackGradedAlgebra.monoidalCategory

variable {T' T : Scheme.{u}} (g : T' ⟶ T)
  (L : SheafOfModules.{u} (structureRingSheaf T.toRingedSpace))
  [Stacks.SheafOfModules.IsInvertible T.toRingedSpace.presheaf (isSheafStruct T) L]

/-- The comparison `g^*(ℒ^{⊗ n}) ≅ (g^*ℒ)^{⊗ n}` of the integral tensor powers commutes with the
multiplications of `g^*(⨁ ℒ^{⊗ n})` and of `⨁ (g^*ℒ)^{⊗ n}`. -/
theorem mulSheaf_baseAlgebra_laurent_comp_laurentPullback (i j : ℤ) :
    (baseAlgebra g (laurent L)).mulSheaf i j ≫ laurentPullback g L (i + j) =
      (laurentPullback g L i ⊗ₘ laurentPullback g L j) ≫
        (laurent ((pullbackFunctor (ringedSpaceHom g)).obj L)).mulSheaf i j := by
  have h := Stacks.RingedSpace.mulSheaf_pullbackGradedAlgebra (ringedSpaceHom g) (laurent L) i j
  refine (congrArg (fun z => z ≫ laurentPullback g L (i + j)) h).trans ?_
  rw [laurent_mulSheaf_eq, laurent_mulSheaf_eq]
  exact (Category.assoc _ _ _).trans ((congrArg (fun z => inv
    (Stacks.PullbackTensorCoherence.pullbackTensorComparison (ringedSpaceHom g)
      ((laurent L).piece i) ((laurent L).piece j)) ≫ z) (laurentPullback_mul g L i j).symm).trans
    (IsIso.inv_hom_id_assoc _ _))

/-- **The comparison `g^*(⨁ ℒ^{⊗ n}) ⟶ ⨁ (g^*ℒ)^{⊗ n}` of Tag 01CU, as a homomorphism of sheaves
of graded algebras**: degreewise the comparison of the integral tensor powers. -/
def laurentPullbackGradedHom :
    baseAlgebra g (laurent L) ⟶ laurent ((pullbackFunctor (ringedSpaceHom g)).obj L) :=
  homOfMulSheaf _ _ (fun n => laurentPullback g L n)
    (mulSheaf_baseAlgebra_laurent_comp_laurentPullback g L)

/-- The degree-`n` component of `laurentPullbackGradedHom g L` is the comparison of the `n`-th
integral tensor powers. -/
@[simp] theorem laurentPullbackGradedHom_app (n : ℤ) :
    (laurentPullbackGradedHom g L).app n = laurentPullback g L n := rfl

section LaurentHom

variable {T : Scheme.{u}} {L L' : SheafOfModules.{u} (structureRingSheaf T.toRingedSpace)}
  [Stacks.SheafOfModules.IsInvertible T.toRingedSpace.presheaf (isSheafStruct T) L]
  [Stacks.SheafOfModules.IsInvertible T.toRingedSpace.presheaf (isSheafStruct T) L']

/-- The inverse of the comparison of degree-one pieces induced by `e : L ≅ L'` is `e⁻¹`, read
through the identifications `L^{⊗ 1} = L` and `L'^{⊗ 1} = L'`. -/
theorem LaurentCongr.congrIso_inv_comp_oneIsoL (e : L ≅ L') :
    (LaurentCongr.congrIso e 1).inv ≫ (LaurentPullback.oneIsoL L).hom =
      (LaurentPullback.oneIsoL L').hom ≫ e.inv := by
  rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv]
  exact LaurentCongr.congrIso_oneIso e

/-- **The isomorphism of invertible modules read off the degree-one component of a homomorphism
of their Laurent algebras**, when that component is invertible. -/
def isoOfLaurentHom (γ : laurent L' ⟶ laurent L) [hγ : IsIso (γ.app 1)] : L ≅ L' :=
  ((LaurentPullback.oneIsoL L').symm ≪≫ asIso (γ.app 1) ≪≫ LaurentPullback.oneIsoL L).symm

/-- **A homomorphism of Laurent algebras whose degree-one component is invertible is the Laurent
algebra map of the isomorphism it induces on degree one**, in every integral degree (Tag 01CU:
the Laurent algebra is generated by its degree-one piece and its inverse). -/
theorem laurentHom_app_eq_congrIso_inv (γ : laurent L' ⟶ laurent L) [hγ : IsIso (γ.app 1)]
    (n : ℤ) :
    γ.app n = (LaurentCongr.congrIso (isoOfLaurentHom γ) n).inv := by
  refine laurent_app_eq_of_app_one (e := (isoOfLaurentHom γ).symm)
    (γ' := (LaurentAlgebraCongr.laurentCongrIso (isoOfLaurentHom γ)).inv) ?_ ?_ n
  · simp [isoOfLaurentHom]
  · exact LaurentCongr.congrIso_inv_comp_oneIsoL (isoOfLaurentHom γ)

end LaurentHom

end Stacks.AlgebraicGeometry.RelativeProjQcohSheaf

namespace CategoryTheory

/-- Solving `(a⁻¹ ≫ b⁻¹ ≫ c) ≫ d = e⁻¹` for `b ≫ a`. -/
theorem comp_eq_comp_comp_hom_of_inv_comp_eq {C : Type*} [Category* C] {P R Q M M' : C}
    (b : P ⟶ R) (a : R ⟶ M') [ha : IsIso a] [hb : IsIso b] (c : P ⟶ Q) (d : Q ⟶ M)
    (e : M ≅ M') (h : (inv a ≫ inv b ≫ c) ≫ d = e.inv) : b ≫ a = c ≫ d ≫ e.hom := by
  simp only [Category.assoc] at h
  rw [IsIso.inv_comp_eq, IsIso.inv_comp_eq] at h
  rw [← Category.assoc c, h]
  simp

/-- **Transporting a restriction across three commuting squares.** For a functor `F`, isomorphisms
`P`, `P'`, morphisms `ψ`, `λ`, `ψ'`, `λ'` and comparisons `c_A`, `c_B`, `c_L` such that the three
squares commute, `c_A ≫ P'⁻¹ ≫ ψ' ≫ λ' = F(P⁻¹ ≫ ψ ≫ λ) ≫ r`. -/
theorem comp_inv_comp_comp_eq_map_comp {C D : Type*} [Category* C] [Category* D] (F : C ⥤ D)
    {b a l m : C} {b' a' l' m' : D} (Pinv : b ⟶ a) (ψ : a ⟶ l) (lam : l ⟶ m)
    (Pinv' : b' ⟶ a') (ψ' : a' ⟶ l') (lam' : l' ⟶ m') (cA : F.obj b ⟶ b')
    (cB : F.obj a ⟶ a') (cL : F.obj l ⟶ l') (r : F.obj m ⟶ m')
    (hP : cA ≫ Pinv' = F.map Pinv ≫ cB) (hb : cB ≫ ψ' = F.map ψ ≫ cL)
    (hc : cL ≫ lam' = F.map lam ≫ r) :
    cA ≫ Pinv' ≫ ψ' ≫ lam' = F.map (Pinv ≫ ψ ≫ lam) ≫ r := by
  rw [Functor.map_comp, Functor.map_comp]
  simp only [Category.assoc]
  rw [← hc, ← reassoc_of% hb, reassoc_of% hP]

/-- `comp_inv_comp_comp_eq_map_comp`, for two morphisms given as such composites. -/
theorem comp_eq_map_comp_of_eq_comp {C D : Type*} [Category* C] [Category* D] (F : C ⥤ D)
    {b a l m : C} {b' a' l' m' : D} {Ψ : b ⟶ m} {Pinv : b ⟶ a} {ψ : a ⟶ l} {lam : l ⟶ m}
    (hΨ : Ψ = Pinv ≫ ψ ≫ lam) {Ψ' : b' ⟶ m'} {Pinv' : b' ⟶ a'} {ψ' : a' ⟶ l'} {lam' : l' ⟶ m'}
    (hΨ' : Ψ' = Pinv' ≫ ψ' ≫ lam') {cA : F.obj b ⟶ b'} {cB : F.obj a ⟶ a'} {cL : F.obj l ⟶ l'}
    {r : F.obj m ⟶ m'} (hP : cA ≫ Pinv' = F.map Pinv ≫ cB) (hb : cB ≫ ψ' = F.map ψ ≫ cL)
    (hc : cL ≫ lam' = F.map lam ≫ r) :
    cA ≫ Ψ' = F.map Ψ ≫ r := by
  subst hΨ hΨ'
  exact comp_inv_comp_comp_eq_map_comp F _ _ _ _ _ _ _ _ _ _ hP hb hc

/-- Inverting the two vertical maps of a square `F(P) ≫ c_A = c_B ≫ P'`. -/
theorem comp_inv_eq_map_inv_comp {C D : Type*} [Category* C] [Category* D] (F : C ⥤ D)
    {a b : C} {a' b' : D} (P : a ⟶ b) [hPi : IsIso P] (P' : a' ⟶ b') [hP'i : IsIso P']
    (cA : F.obj b ⟶ b') (cB : F.obj a ⟶ a') (hP : F.map P ≫ cA = cB ≫ P') :
    cA ≫ inv P' = F.map (inv P) ≫ cB := by
  rw [Functor.map_inv, IsIso.eq_inv_comp, ← Category.assoc, hP, Category.assoc, IsIso.hom_inv_id,
    Category.comp_id]

end CategoryTheory

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X : AlgebraicSpaces B S hS}
  (L : SheafOfModules.{u}
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS X).O))
  [hL : Stacks.SheafOfModules.IsInvertible (smallEtaleRingedTopos B S hS X).O.obj
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS X).O).property L]

/-- The integral tensor powers of an invertible `𝒪_X`-module on the small étale site of an
algebraic space are quasi-coherent. -/
theorem isQuasicoherentOnSite_laurentAlgebra_piece_of_isInvertible (n : ℤ) :
    ((Stacks.SheafOfModules.TensorPower.laurentAlgebra (smallEtaleRingedTopos B S hS X).O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS X).O).property
        L).piece n).IsQuasicoherentOnSite :=
  isQuasicoherentOnSite_of_isInvertible B S hS X _
    ((@Stacks.SheafOfModules.TensorPower.isInvertible_tensorPower _ _ _
      (smallEtaleRingedTopos B S hS X).O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS X).O).property _ _ L hL
        n).toAlgebraicGeometry _ _ _)

/-- `AlgebraicGeometry.Space.isInvertible_pointLine`, at the spelling of the scheme of `T` through
`AlgebraicGeometry.BigFppfOver.toScheme`. -/
instance isInvertible_pointLine_toScheme (T : BigFppfOver B S hS) (x : yoneda.obj T ⟶ X.1) :
    Stacks.SheafOfModules.IsInvertible ((BigFppfOver.toScheme B S hS).obj T).toRingedSpace.presheaf
      (isSheafStruct _) (pointLine B S hS L T x) :=
  isInvertible_pointLine B S hS L T x

variable {T T' : BigFppfOver B S hS} (τ : T' ⟶ T) (x : yoneda.obj T ⟶ X.1)

/-- The pullback of the restriction of `ℒ` along a morphism of test objects is invertible. -/
instance isInvertible_pullback_pointLine :
    Stacks.SheafOfModules.IsInvertible (chartScheme (idEtaleChart B S hS T')).toRingedSpace.presheaf
      (isSheafStruct _)
      ((pullbackFunctor (ringedSpaceHom ((BigFppfOver.toScheme B S hS).map τ))).obj
        (pointLine B S hS L T x)) :=
  Stacks.PullbackMonoidalSheaf.isInvertible_pullbackFunctor_obj
    (ringedSpaceHom ((BigFppfOver.toScheme B S hS).map τ)) (pointLine B S hS L T x)

/-- The comparison of the restrictions of the Laurent algebra of `ℒ` along a morphism of test
objects is an isomorphism in every degree. -/
instance isIso_pointComparison_laurentAlgebra_app (n : ℤ) :
    IsIso ((pointComparison (Stacks.SheafOfModules.TensorPower.laurentAlgebra
      (smallEtaleRingedTopos B S hS X).O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS X).O).property L)
        τ x (yoneda.map τ ≫ x) rfl).app n) :=
  isIso_pointComparison_app _ (isQuasicoherentOnSite_laurentAlgebra_piece_of_isInvertible L) τ x _
    rfl n

/-- The comparison `τ^*(x^*(⨁ ℒ^{⊗ n})) ⟶ (x ∘ τ)^*(⨁ ℒ^{⊗ n})` of the restrictions of the
Laurent algebra of `ℒ`, as a unital homomorphism. -/
def pointLaurentComparison :
    SheafOfModules.GradedAlgebra.UnitalHom
      (baseAlgebra ((BigFppfOver.toScheme B S hS).map τ)
        (zariskiReading T (etalePointAlgebra (Stacks.SheafOfModules.TensorPower.laurentAlgebra
          (smallEtaleRingedTopos B S hS X).O.obj
          (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS X).O).property L)
            T x)))
      (zariskiReading T' (etalePointAlgebra (Stacks.SheafOfModules.TensorPower.laurentAlgebra
          (smallEtaleRingedTopos B S hS X).O.obj
          (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS X).O).property L)
            T' (yoneda.map τ ≫ x))) :=
  SheafOfModules.GradedAlgebra.UnitalHom.ofHomOfIsIso (pointComparison _ τ x _ rfl)

/-- Each degree component of `pointLaurentComparison L τ x` is an isomorphism. -/
instance isIso_pointLaurentComparison_app (n : ℤ) :
    IsIso ((pointLaurentComparison L τ x).app n) :=
  isIso_pointComparison_laurentAlgebra_app L τ x n

/-- `AlgebraicGeometry.Space.isIso_pointLaurentHom_app`, as an instance. -/
instance instIsIso_pointLaurentHom_app (T : BigFppfOver B S hS) (x : yoneda.obj T ⟶ X.1) (n : ℤ) :
    IsIso ((pointLaurentHom B S hS L T x).app n) :=
  isIso_pointLaurentHom_app B S hS L T x n

/-- **The comparison of the Laurent algebras of the restrictions of `ℒ` along `τ : T' ⟶ T`**,
`⨁ ((x ∘ τ)^*ℒ)^{⊗ n} ⟶ ⨁ (τ^*(x^*ℒ))^{⊗ n}`: the inverse of the identification of the
restricted Laurent algebra at `x ∘ τ`, the inverse of the comparison of the restrictions, the
pullback of the identification at `x`, and the comparison of the tensor powers. -/
def pointLineComparison :
    laurent (pointLine B S hS L T' (yoneda.map τ ≫ x)) ⟶
      laurent ((pullbackFunctor (ringedSpaceHom ((BigFppfOver.toScheme B S hS).map τ))).obj
        (pointLine B S hS L T x)) :=
  ((pointLaurentHom B S hS L T' (yoneda.map τ ≫ x)).inverse.comp
      ((pointLaurentComparison L τ x).inverse.comp
        (baseAlgebraMapHom ((BigFppfOver.toScheme B S hS).map τ)
          (pointLaurentHom B S hS L T x)))).toHom ≫
    laurentPullbackGradedHom ((BigFppfOver.toScheme B S hS).map τ) (pointLine B S hS L T x)

/-- The pullback of the restriction of `ℒ`, at the spelling of the scheme of `T'` through
`AlgebraicGeometry.BigFppfOver.toScheme`. -/
instance isInvertible_pullback_pointLine_toScheme :
    Stacks.SheafOfModules.IsInvertible ((BigFppfOver.toScheme B S hS).obj T').toRingedSpace.presheaf
      (isSheafStruct _)
      ((pullbackFunctor (ringedSpaceHom ((BigFppfOver.toScheme B S hS).map τ))).obj
        (pointLine B S hS L T x)) :=
  isInvertible_pullback_pointLine L τ x

/-- `pointLineComparison` is an isomorphism in every degree. -/
instance isIso_pointLineComparison_app (n : ℤ) : IsIso ((pointLineComparison L τ x).app n) := by
  have i1 : IsIso ((pointLaurentHom B S hS L T' (yoneda.map τ ≫ x)).inverse.app n) :=
    @IsIso.inv_isIso _ _ _ _ _ (isIso_pointLaurentHom_app B S hS L T' _ n)
  have i2 : IsIso ((pointLaurentComparison L τ x).inverse.app n) :=
    @IsIso.inv_isIso _ _ _ _ _ (isIso_pointComparison_laurentAlgebra_app L τ x n)
  have i3 : IsIso ((baseAlgebraMapHom ((BigFppfOver.toScheme B S hS).map τ)
      (pointLaurentHom B S hS L T x)).app n) :=
    @Functor.map_isIso _ _ _ _ _ _ (pullbackFunctor _) _ (isIso_pointLaurentHom_app B S hS L T x n)
  have i4 : IsIso ((laurentPullbackGradedHom ((BigFppfOver.toScheme B S hS).map τ)
      (pointLine B S hS L T x)).app n) := isIso_laurentPullback _ _ _
  exact @IsIso.comp_isIso _ _ _ _ _ _ _ (@IsIso.comp_isIso _ _ _ _ _ _ _ i1
    (@IsIso.comp_isIso _ _ _ _ _ _ _ i2 i3)) i4

/-- **The identification `τ^*(x^*ℒ) ≅ (x ∘ τ)^*ℒ` of the restrictions of `ℒ` along a morphism
`τ : T' ⟶ T` of test objects**: the degree-one component of `pointLineComparison`. -/
def pointLineIso :
    (pullbackFunctor (ringedSpaceHom ((BigFppfOver.toScheme B S hS).map τ))).obj
      (pointLine B S hS L T x) ≅ pointLine B S hS L T' (yoneda.map τ ≫ x) :=
  isoOfLaurentHom (pointLineComparison L τ x) (hγ := isIso_pointLineComparison_app L τ x 1)

/-- **The identifications of the restricted Laurent algebras are compatible with the restriction
maps**: along `τ : T' ⟶ T`, the comparison of the restrictions of `⨁ ℒ^{⊗ n}` followed by the
identification at `x ∘ τ` is the pullback of the identification at `x`, followed by the
comparison of the tensor powers and the Laurent algebra map of `pointLineIso`. -/
theorem pointComparison_comp_pointLaurentHom_app (n : ℤ) :
    (pointLaurentComparison L τ x).app n ≫ (pointLaurentHom B S hS L T' (yoneda.map τ ≫ x)).app n =
      (pullbackFunctor (ringedSpaceHom ((BigFppfOver.toScheme B S hS).map τ))).map
          ((pointLaurentHom B S hS L T x).app n) ≫
        laurentPullback ((BigFppfOver.toScheme B S hS).map τ) (pointLine B S hS L T x) n ≫
          (LaurentCongr.congrIso (pointLineIso L τ x) n).hom := by
  have hγ := laurentHom_app_eq_congrIso_inv (pointLineComparison L τ x)
    (hγ := isIso_pointLineComparison_app L τ x 1) n
  have h2 := comp_eq_comp_comp_hom_of_inv_comp_eq
    (ha := isIso_pointLaurentHom_app B S hS L T' (yoneda.map τ ≫ x) n)
    (hb := isIso_pointComparison_laurentAlgebra_app L τ x n)
    ((pointLaurentComparison L τ x).app n) ((pointLaurentHom B S hS L T' (yoneda.map τ ≫ x)).app n)
    ((pullbackFunctor (ringedSpaceHom ((BigFppfOver.toScheme B S hS).map τ))).map
          ((pointLaurentHom B S hS L T x).app n))
    (laurentPullback ((BigFppfOver.toScheme B S hS).map τ) (pointLine B S hS L T x) n)
    (LaurentCongr.congrIso (pointLineIso L τ x) n)
  exact h2 hγ

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.Space

open Stacks.Sheaves.GradedAlgebraEssentiallySmall (gradedPull)

section Psi

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X Y : AlgebraicSpaces B S hS}
  (f : X ⟶ Y) (A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf B S hS Y))
  (L : SheafOfModules.{u}
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS X).O))
  [hL : Stacks.SheafOfModules.IsInvertible (smallEtaleRingedTopos B S hS X).O.obj
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS X).O).property L]
  (ψ : SheafOfModules.GradedAlgebra.UnitalHom
    ((gradedPull (X := smallEtaleRingedTopos B S hS X) (Y := smallEtaleRingedTopos B S hS Y)
      (smallEtaleRingedToposHom B S hS f)).obj A)
    (Stacks.SheafOfModules.TensorPower.laurentAlgebra (smallEtaleRingedTopos B S hS X).O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS X).O).property L))

/-- **The restriction `x^*ψ : (f ∘ x)^*𝒜 ⟶ ⨁ (x^*ℒ)^{⊗ n}` of `ψ : f^*𝒜 ⟶ ⨁ ℒ^{⊗ n}` to a scheme
point `x : T ⟶ X`**: the comparison `(f ∘ x)^*𝒜 ≅ x^*(f^*𝒜)` of
`AlgebraicGeometry.Space.pullbackPointHom`, the restriction of `ψ`
(`AlgebraicGeometry.Space.pointAlgebraHom`) and the identification
`x^*(⨁ ℒ^{⊗ n}) ≅ ⨁ (x^*ℒ)^{⊗ n}` (`AlgebraicGeometry.Space.pointLaurentHom`). -/
def pointPsi (T : BigFppfOver B S hS) (x : yoneda.obj T ⟶ X.1) :
    SheafOfModules.GradedAlgebra.UnitalHom
      (zariskiReading T (etalePointAlgebra A T (x ≫ f.hom)))
      (laurent (pointLine B S hS L T x)) :=
  ((pullbackPointHom f A (Iso.refl _) T x).inverse
      (inst := fun n => isIso_pullbackPointHom_app f A (Iso.refl _) T x n)).comp
    ((pointAlgebraHom ψ T x).comp (pointLaurentHom B S hS L T x))

/-- The components of `pointPsi`. -/
theorem pointPsi_app (T : BigFppfOver B S hS) (x : yoneda.obj T ⟶ X.1) (n : ℤ) :
    (pointPsi f A L ψ T x).app n =
      @inv _ _ _ _ ((pullbackPointHom f A (Iso.refl _) T x).app n)
          (isIso_pullbackPointHom_app f A (Iso.refl _) T x n) ≫
        (pointAlgebraHom ψ T x).toHom.app n ≫ (pointLaurentHom B S hS L T x).app n :=
  rfl

/-- The pullback of the components of `pointPsi`. -/
theorem map_pointPsi_app {T T' : BigFppfOver B S hS} (τ : T' ⟶ T) (x : yoneda.obj T ⟶ X.1)
    (n : ℤ) :
    (pullbackFunctor (ringedSpaceHom ((BigFppfOver.toScheme B S hS).map τ))).map
        ((pointPsi f A L ψ T x).app n) =
      (pullbackFunctor (ringedSpaceHom ((BigFppfOver.toScheme B S hS).map τ))).map
        (@inv _ _ _ _ ((pullbackPointHom f A (Iso.refl _) T x).app n)
          (isIso_pullbackPointHom_app f A (Iso.refl _) T x n) ≫
        (pointAlgebraHom ψ T x).toHom.app n ≫ (pointLaurentHom B S hS L T x).app n) :=
  rfl

/-- The comparison `(f ∘ x)^*𝒜 ≅ x^*(f^*𝒜)` of the restrictions commutes with the comparisons of
the two restriction data along a morphism `τ : T' ⟶ T` of test objects, in inverted form. -/
theorem pointComparison_comp_inv_pullbackPointHom_app {T T' : BigFppfOver B S hS}
    (τ : T' ⟶ T) (x : yoneda.obj T ⟶ X.1)
    (hτ : yoneda.map τ ≫ x ≫ f.hom = (yoneda.map τ ≫ x) ≫ f.hom) (n : ℤ) :
    (pointComparison A τ (x ≫ f.hom) ((yoneda.map τ ≫ x) ≫ f.hom) hτ).app n ≫
        @inv _ _ _ _ ((pullbackPointHom f A (Iso.refl _) T' (yoneda.map τ ≫ x)).app n)
          (isIso_pullbackPointHom_app f A (Iso.refl _) T' (yoneda.map τ ≫ x) n) =
      (pullbackFunctor (ringedSpaceHom ((BigFppfOver.toScheme B S hS).map τ))).map
          (@inv _ _ _ _ ((pullbackPointHom f A (Iso.refl _) T x).app n)
            (isIso_pullbackPointHom_app f A (Iso.refl _) T x n)) ≫
        (pointComparison ((gradedPull (X := smallEtaleRingedTopos B S hS X)
          (Y := smallEtaleRingedTopos B S hS Y) (smallEtaleRingedToposHom B S hS f)).obj A)
            τ x (yoneda.map τ ≫ x) rfl).app n :=
  comp_inv_eq_map_inv_comp (hPi := isIso_pullbackPointHom_app f A (Iso.refl _) T x n)
    (hP'i := isIso_pullbackPointHom_app f A (Iso.refl _) T' (yoneda.map τ ≫ x) n) _ _ _ _ _
    (pullbackPointHom_comparison_app f A (Iso.refl _) τ x hτ n)

/-- **`(x ∘ τ)^*ψ` is the pullback of `x^*ψ`**: along a morphism `τ : T' ⟶ T` of test objects,
the comparison `τ^*((f ∘ x)^*𝒜) ⟶ (f ∘ x ∘ τ)^*𝒜` followed by the restriction of `ψ` at `x ∘ τ`
is the pullback of the restriction at `x`, followed by the comparison of the tensor powers and
the Laurent algebra map of the identification `τ^*(x^*ℒ) ≅ (x ∘ τ)^*ℒ`. -/
theorem pointComparison_comp_pointPsi_app {T T' : BigFppfOver B S hS}
    (τ : T' ⟶ T) (x : yoneda.obj T ⟶ X.1)
    (hτ : yoneda.map τ ≫ x ≫ f.hom = (yoneda.map τ ≫ x) ≫ f.hom) (n : ℤ) :
    (pointComparison A τ (x ≫ f.hom) ((yoneda.map τ ≫ x) ≫ f.hom) hτ).app n ≫
        (pointPsi f A L ψ T' (yoneda.map τ ≫ x)).app n =
      (pullbackFunctor (ringedSpaceHom ((BigFppfOver.toScheme B S hS).map τ))).map
          ((pointPsi f A L ψ T x).app n) ≫
        laurentPullback ((BigFppfOver.toScheme B S hS).map τ) (pointLine B S hS L T x) n ≫
          (LaurentCongr.congrIso (pointLineIso L τ x) n).hom := by
  have hb := pointComparison_comp_pointAlgebraHom_app ψ τ x (yoneda.map τ ≫ x) rfl n
  have hc := pointComparison_comp_pointLaurentHom_app L τ x n
  have h1 := pointPsi_app f A L ψ T x n
  have h2 := pointPsi_app f A L ψ T' (yoneda.map τ ≫ x) n
  have h3 := pointComparison_comp_inv_pullbackPointHom_app f A τ x hτ n
  have key := comp_eq_map_comp_of_eq_comp
    (pullbackFunctor (ringedSpaceHom ((BigFppfOver.toScheme B S hS).map τ))) h1 h2 h3 hb hc
  exact key

end Psi

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.Space.RelativeProjSituation

open Stacks.Sheaves.GradedAlgebraEssentiallySmall (gradedPull)
open Stacks.AlgebraicGeometry.RelativeProjBridge Stacks.AlgebraicGeometry.RelativeProj
  Stacks.AlgebraicGeometry.RelativeProjInvertibleMorphism

/-! ### The pair `(ℒ, ψ)` on `X`, restricted to the scheme points of `X`

The pair is read over the re-presented situation `s.shrink`, which has the same site, base and
algebraic space as `s` (`shrink_site`, `shrink_base`, `shrink_space`, all `rfl`) and the
re-presentation `s.shrink.algebra` of `𝒜` with sections in the universe of the schemes; this is
where the restriction datum of Stacks 084A for Situation 0849, and hence the relative Proj,
lives. -/

variable (s : RelativeProjSituation.{u, m})
  {X : AlgebraicSpaces s.shrink.site s.shrink.base s.shrink.containsBase} (f : X ⟶ s.shrink.space)
  (L : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
    (smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X).O))
  [hL : Stacks.SheafOfModules.IsInvertible
    (smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X).O.obj
    (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X).O).property L]
  (ψ : SheafOfModules.GradedAlgebra.UnitalHom
    ((gradedPull (X := smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X)
      (Y := smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase s.shrink.space)
      (smallEtaleRingedToposHom s.shrink.site s.shrink.base s.shrink.containsBase f)).obj
        s.shrink.algebra)
    (Stacks.SheafOfModules.TensorPower.laurentAlgebra
      (smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X).O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X).O).property L))

/-- **`(x ∘ τ)^*ψ` is the pullback of `x^*ψ`, through the restriction map of Stacks 084A**: the
restriction map `(f ∘ x ∘ τ)^*𝒜 ⟶ τ^*((f ∘ x)^*𝒜)` of the restriction datum of Situation 0849,
followed by the pullback of `x^*ψ`, the comparison of the tensor powers and the Laurent algebra map
of `τ^*(x^*ℒ) ≅ (x ∘ τ)^*ℒ`, is `(x ∘ τ)^*ψ`. -/
theorem restrict_comp_pointPsi_app
    {T T' : BigFppfOver s.shrink.site s.shrink.base s.shrink.containsBase} (τ : T' ⟶ T)
    (x : yoneda.obj T ⟶ X.1) (hg : yoneda.map τ ≫ x ≫ f.hom = (yoneda.map τ ≫ x) ≫ f.hom) (n : ℤ) :
    (s.quadrupleRestriction.restrict τ (x ≫ f.hom) ((yoneda.map τ ≫ x) ≫ f.hom) hg).app n ≫
        (pullbackFunctor (ringedSpaceHom
          ((BigFppfOver.toScheme s.shrink.site s.shrink.base s.shrink.containsBase).map τ))).map
          ((pointPsi f s.shrink.algebra L ψ T x).app n) ≫
        laurentPullback
          ((BigFppfOver.toScheme s.shrink.site s.shrink.base s.shrink.containsBase).map τ)
          (pointLine s.shrink.site s.shrink.base s.shrink.containsBase L T x) n ≫
          (LaurentCongr.congrIso (pointLineIso L τ x) n).hom =
      (pointPsi f s.shrink.algebra L ψ T' (yoneda.map τ ≫ x)).app n := by
  have h := pointComparison_comp_pointPsi_app f s.shrink.algebra L ψ τ x hg n
  have key := (@IsIso.inv_comp_eq _ _ _ _ _ _
    (isIso_pointComparison_app s.shrink.algebra s.shrink.isQuasicoherent τ _ _ hg n) _ _).2 h.symm
  exact key

/-- **The restriction `x^*ψ` of `ψ` to a scheme point `x : T ⟶ X`, as the map `ψ` of a quadruple
over the identity of `T`** (Section 01NS): `twistingOfUnitalHom` of `pointPsi`, read through the
identification `(𝟙_T)^*((f ∘ x)^*𝒜) = (f ∘ x)^*𝒜`. -/
def pointTwisting (T : BigFppfOver s.shrink.site s.shrink.base s.shrink.containsBase)
    (x : yoneda.obj T ⟶ X.1) :
    Twisting (𝟙 ((BigFppfOver.toScheme s.shrink.site s.shrink.base s.shrink.containsBase).obj T))
      (situationAlgebra (s.shrink.pointAlgebra T (x ≫ f.hom))) 1
      (pointLine s.shrink.site s.shrink.base s.shrink.containsBase L T x) :=
  Stacks.RelativeProj.twistingOfUnitalHom
    (𝟙 ((BigFppfOver.toScheme s.shrink.site s.shrink.base s.shrink.containsBase).obj T))
    (situationAlgebra (s.shrink.pointAlgebra T (x ≫ f.hom)))
    (pointLine s.shrink.site s.shrink.base s.shrink.containsBase L T x)
    ((Stacks.Conormal.gradedPullbackId
      (situationAlgebra (s.shrink.pointAlgebra T (x ≫ f.hom)))).comp
        (pointPsi f s.shrink.algebra L ψ T x))

/-- **`(x ∘ τ)^*ψ` is the pullback of `x^*ψ` along `τ`**, as the restriction datum of
`AlgebraicGeometry.Space.RelativeProjSituation.InvertibleTwistingRestriction` demands. -/
theorem pointTwisting_map {T T' : BigFppfOver s.shrink.site s.shrink.base s.shrink.containsBase}
    (τ : T' ⟶ T) (x : yoneda.obj T ⟶ X.1) :
    s.pointTwisting f L ψ T' (yoneda.map τ ≫ x) =
      (Twisting.congrBase (CategoryTheory.Functor.map_id _ T')
        (s.quadrupleRestriction.squareTwisting s.shrink.contains_relativeProj_pointAlgebra
          s.shrink.space.property.isSheaf (s.pointTwisting f L ψ T x) ((yoneda.map τ ≫ x) ≫ f.hom)
          (𝟙 T') τ (by rw [CategoryTheory.Functor.map_id, Category.id_comp,
            Category.assoc]))).congrModule
        (pointLineIso L τ x) := by
  have hg : yoneda.map τ ≫ x ≫ f.hom = (yoneda.map τ ≫ x) ≫ f.hom := (Category.assoc _ _ _).symm
  have key := s.quadrupleRestriction.twistingOfUnitalHom_eq_squareTwisting_id
    s.shrink.contains_relativeProj_pointAlgebra s.shrink.space.property.isSheaf
    (pointPsi f s.shrink.algebra L ψ T x) τ ((yoneda.map τ ≫ x) ≫ f.hom)
    (by rw [CategoryTheory.Functor.map_id, Category.id_comp, Category.assoc]) hg
    (pointPsi f s.shrink.algebra L ψ T' (yoneda.map τ ≫ x)) (pointLineIso L τ x)
    (fun i => s.restrict_comp_pointPsi_app f L ψ τ x hg i)
  exact key

/-- **The restriction datum of a pair `(ℒ, ψ)` on the algebraic space `X`**, Stacks 0D2Z: for an
invertible `𝒪_X`-module `ℒ` on the small étale site of `X` and a unital homomorphism of sheaves of
graded algebras `ψ : f^*𝒜 ⟶ ⨁_{n ∈ ℤ} ℒ^{⊗ n}`, the restrictions `x^*ℒ`
(`AlgebraicGeometry.Space.pointLine`) and `x^*ψ` (`pointTwisting`) to the scheme points
`x : T ⟶ X`, with the identifications `τ^*(x^*ℒ) ≅ (x ∘ τ)^*ℒ`
(`AlgebraicGeometry.Space.pointLineIso`) under which `(x ∘ τ)^*ψ` is the pullback of `x^*ψ`
(`pointTwisting_map`). -/
def InvertibleTwistingRestriction.ofUnitalHom : s.InvertibleTwistingRestriction f.hom where
  line T x := pointLine s.shrink.site s.shrink.base s.shrink.containsBase L T x
  isInvertible T x := isInvertible_pointLine_toScheme L T x
  twisting T x := s.pointTwisting f L ψ T x
  lineIso τ x := pointLineIso L τ x
  twisting_map τ x := s.pointTwisting_map f L ψ τ x

namespace InvertibleTwistingRestriction

/-- The restriction of `ℒ` to a scheme point of a test object of the site of `s` is invertible. -/
instance isInvertibleModule_ofUnitalHom_line (T : BigFppfOver s.site s.base s.containsBase)
    (x : yoneda.obj T ⟶ X.1) :
    Stacks.Ample.IsInvertibleModule _ ((ofUnitalHom s f L ψ).line T x) :=
  (ofUnitalHom s f L ψ).isInvertible T x

/-- **`U(ψ)` is an open subspace of the algebraic space `X`**, for a pair `(ℒ, ψ)` on `X`. -/
@[stacks 0D2Z "the source U(psi) of r_{L,psi}, for an algebraic space X with an invertible \
O_X-module L on its small etale site and a homomorphism of graded algebras psi : f^*A -> \
(+)_n L^n on X: an open subspace of X"]
theorem isOpenSubspace_locus_ofUnitalHom :
    IsOpenSubspace s.site s.base s.containsBase (ofUnitalHom s f L ψ).locus :=
  (ofUnitalHom s f L ψ).isOpenSubspace_locus X.property

/-- **`r_{ℒ,ψ} : U(ψ) ⟶ Proj_Y(𝒜)` is a morphism over `Y`**, for a pair `(ℒ, ψ)` on the algebraic
space `X`. -/
@[stacks 0D2Z "the canonical morphism r_{L,psi} : U(psi) -> Proj_Y(A) over Y, for an algebraic \
space X with an invertible O_X-module L on its small etale site and a homomorphism of graded \
algebras psi : f^*A -> (+)_n L^n on X"]
theorem invertibleMorphism_comp_π_ofUnitalHom :
    (ofUnitalHom s f L ψ).invertibleMorphism ≫ s.relativeProjπ =
      (ofUnitalHom s f L ψ).locus.ι ≫ f.hom :=
  (ofUnitalHom s f L ψ).invertibleMorphism_comp_π

/-- **Clause (2)(a) of [Stacks, Tag 0D2Z]** for a pair `(ℒ, ψ)` on the algebraic space `X`: a
scheme `w : W ⟶ X` over which `ψ|_W : (f ∘ w)^*𝒜_k ⟶ (w^*ℒ)^{⊗ k}` is surjective for some
`k ≥ 1` factors through `U(ψ)`. Here `ψ|_W` is the restriction `(ofUnitalHom s f L ψ).twisting W w`
of `ψ` to `W` (`pointTwisting`, the map of `AlgebraicGeometry.Space.pointPsi`). -/
@[stacks 0D2Z "clause (2)(a), for a pair (L, psi) on an algebraic space X: a scheme W -> X over \
which psi|_W is surjective in some degree k >= 1 factors through U(psi)"]
theorem mem_locus_ofUnitalHom_of_epi {W : BigFppfOver s.site s.base s.containsBase}
    (w : yoneda.obj W ⟶ X.1) {k : ℕ} (hk : 0 < k)
    [Epi (((ofUnitalHom s f L ψ).twisting W w).app (k : ℤ))] :
    yonedaEquiv w ∈ (ofUnitalHom s f L ψ).locus.obj (op W) :=
  (ofUnitalHom s f L ψ).mem_locus_of_epi w hk

/-- **Clause (2)(b) of [Stacks, Tag 0D2Z]** for a pair `(ℒ, ψ)` on the algebraic space `X`: for a
scheme `w : W ⟶ X` over which `ψ|_W` is surjective in degree `k ≥ 1`, the composite
`W ⟶ U(ψ) ⟶ Proj_Y(𝒜)` is the morphism which the construction of the relative Proj attaches to
the quadruple `(k, W ⟶ Y, ℒ^{⊗ k}|_W, ψ|_W)`. -/
@[stacks 0D2Z "clause (2)(b), for a pair (L, psi) on an algebraic space X: for a scheme W -> X \
over which psi|_W is surjective in degree k >= 1, W -> U(psi) -> Proj_Y(A) is the morphism \
attached to the quadruple (k, W -> Y, L^k|_W, psi|_W)"]
theorem factor_invertibleMorphism_ofUnitalHom_of_epi {W : BigFppfOver s.site s.base s.containsBase}
    (w : yoneda.obj W ⟶ X.1) {k : ℕ} (hk : 0 < k)
    [Epi (((ofUnitalHom s f L ψ).twisting W w).app (k : ℤ))] :
    (ofUnitalHom s f L ψ).factor w (mem_locus_ofUnitalHom_of_epi s f L ψ w hk) ≫
        (ofUnitalHom s f L ψ).invertibleMorphism =
      (ofUnitalHom s f L ψ).quadruplePoint w hk :=
  (ofUnitalHom s f L ψ).factor_invertibleMorphism_of_epi w hk

/-- **`r_{ℒ,ψ}` is characterized by clause (2)**, for a pair `(ℒ, ψ)` on the algebraic space `X`:
a morphism `U(ψ) ⟶ Proj_Y(𝒜)` over `Y` which, on every scheme `W ⟶ X` over which `ψ|_W` is
surjective in some degree `k ≥ 1`, is the morphism attached to the quadruple of clause (2)(b), is
`r_{ℒ,ψ}`. -/
@[stacks 0D2Z "r_{L,psi} is characterized by property (2), for a pair (L, psi) on an algebraic \
space X: it is the only morphism U(psi) -> Proj_Y(A) over Y with clause (2)(b)"]
theorem eq_invertibleMorphism_ofUnitalHom
    (Φ : (ofUnitalHom s f L ψ).locus.toFunctor ⟶ s.relativeProjFunctor)
    (hΦπ : Φ ≫ s.relativeProjπ = (ofUnitalHom s f L ψ).locus.ι ≫ f.hom)
    (hΦ : ∀ {W : BigFppfOver s.site s.base s.containsBase} (w : yoneda.obj W ⟶ X.1) {k : ℕ}
      (hk : 0 < k) [Epi (((ofUnitalHom s f L ψ).twisting W w).app (k : ℤ))],
      (ofUnitalHom s f L ψ).factor w (mem_locus_ofUnitalHom_of_epi s f L ψ w hk) ≫ Φ =
        (ofUnitalHom s f L ψ).quadruplePoint w hk) :
    Φ = (ofUnitalHom s f L ψ).invertibleMorphism :=
  (ofUnitalHom s f L ψ).eq_invertibleMorphism Φ hΦπ hΦ

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory in
/-- **Clause (3) of [Stacks, Tag 0D2Z]** for a pair `(ℒ, ψ)` on the algebraic space `X`: for a
commutative square `g ∘ f' = f ∘ g'` with `X'`, `Y'` schemes and `ψ'` the pullback of `ψ`,
`U(ψ') = (g')^{-1}(U(ψ))` and `r_{ψ',ℒ'}` of Tag 01O9 is the base change of `r_{ℒ,ψ}` through
`Proj_{Y'}(g^*𝒜) = Y' ×_Y Proj_Y(𝒜)`, tested on every scheme `T ⟶ U(ψ')`. -/
@[stacks 0D2Z "clause (3), the open and the morphism, for a pair (L, psi) on an algebraic space \
X and an arbitrary commutative square g o f' = f o g' with X', Y' schemes: U(psi') = \
(g')^{-1}(U(psi)) and r_{psi',L'} is the base change of r_{L,psi}"]
theorem invertibleMorphism_baseChange_square_ofUnitalHom
    {X' Y' : BigFppfOver s.site s.base s.containsBase} (g' : yoneda.obj X' ⟶ X.1)
    (f' : X' ⟶ Y') (g : yoneda.obj Y' ⟶ s.space.1) (hsq : yoneda.map f' ≫ g = g' ≫ f.hom) :
    (ofUnitalHom s f L ψ).locus.preimage g' = subspaceOfOpens s.site s.base s.containsBase X'
        (toGradedPowerMap ((ofUnitalHom s f L ψ).squarePsi g' f' g hsq)).coveringOpen ∧
    ∀ {T : BigFppfOver s.site s.base s.containsBase} (t : T ⟶ X')
      (ht : yonedaEquiv (yoneda.map t ≫ g') ∈ (ofUnitalHom s f L ψ).locus.obj (op T)),
      (s.relativeProjPoints.pointEquivProjOver Y' g (t ≫ f')
          ⟨(ofUnitalHom s f L ψ).factor (yoneda.map t ≫ g') ht ≫
              (ofUnitalHom s f L ψ).invertibleMorphism,
            (ofUnitalHom s f L ψ).factor_invertibleMorphism_comp_π g' f' g hsq t ht⟩).1 =
        liftOfPreimageEqTop _ ((BigFppfOver.toScheme s.site s.base s.containsBase).map t)
            ((ofUnitalHom s f L ψ).preimage_coveringOpen_squarePsi_eq_top g' f' g hsq t ht) ≫
          (toGradedPowerMap ((ofUnitalHom s f L ψ).squarePsi g' f' g hsq)).globalMorphism
            (relativeProj (s.relativeProjPoints.algebra Y' g)) :=
  (ofUnitalHom s f L ψ).invertibleMorphism_baseChange_square g' f' g hsq

end InvertibleTwistingRestriction

end AlgebraicGeometry.Space.RelativeProjSituation

end
