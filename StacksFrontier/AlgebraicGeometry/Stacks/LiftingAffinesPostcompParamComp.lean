module

public import StacksFrontier.AlgebraicGeometry.Stacks.LiftingAffinesSelfIntersectionMapComp
public import StacksFrontier.AlgebraicGeometry.Stacks.LiftingAffinesAutomorphismRestriction

/-!
# The parameters of endomorphisms, read along a morphism of smooth lifts, restrict

Let `m : η ⟶ ξ` be a morphism of smooth lifts of étale opens of `W` along a first order
thickening (Stacks 0CJP), and `τ` an endomorphism of `η` over the identity, with parameter
`θ_τ : Δ^*Ω_{I_η/V'} ⟶ 𝒞_{V/V'}` (`AlgebraicGeometry.Stack.EtaleSmoothLift.autParam`). Pushing the
section `δ_τ` into `I'_ξ` along `Φ_m` moves the restricted diagonal `Φ_m ∘ Δ'_η` by the datum
`θ_τ''` of Stacks 0CK6 (`AlgebraicGeometry.Stack.EtaleSmoothLift.postcompParam`), and this datum,
read through Stacks 03LU and 04CQ, is a map `f^*Δ_ξ^*Ω_{I_ξ/U'} ⟶ f^*𝒞_{U/U'}` of modules on `V`
pulled back from `U` (`f : V ⟶ U` the restriction of `f'`).

This file shows that the reading is compatible with restriction along a second morphism
`n : η' ⟶ η`: if `τ' ≫ n = n ≫ τ` then the reading of `θ_{τ'}` along `n ≫ m` is the restriction,
in the sense of Stacks 03LU (`AlgebraicGeometry.Space.QuasiCoherentDescent.restrictForm`), of the
reading of `θ_τ` along `m` (`AlgebraicGeometry.Stack.EtaleSmoothLift.readParam_comp_eq`). This is
the naturality of the identification of the band of the gerbe of smooth lifts with
`SheafHom(Δ^*Ω_{I/U'}, 𝒞_{U/U'})` in the proof of Stacks 0CKG (2), item (1) of the source's proof
via its footnote. The argument: both readings move the same section, `δ_{τ'}` pushed by
`Φ_{n ≫ m} = Φ_n ≫ Φ_m` (`AlgebraicGeometry.Stack.EtaleSmoothLift.selfIntersectionMap_comp`), by
the restriction law of the action (`AlgebraicGeometry.Space.comp_derivationMove_restriction`),
and the action is free.

## References

* [Stacks Project, Tag 0CKG](https://stacks.math.columbia.edu/tag/0CKG)
* [Stacks Project, Tag 0CK6](https://stacks.math.columbia.edu/tag/0CK6)
* [Stacks Project, Tag 0CK8](https://stacks.math.columbia.edu/tag/0CK8)
-/

@[expose] public noncomputable section

open CategoryTheory


namespace CategoryTheory

/-- Pasting two commutative squares along a factorization of the edge. -/
theorem comp_comp_eq_of_squares_paste {C : Type*} [Category C] {a b c d a' e e' : C} {i : a ⟶ b}
    {ψ : b ⟶ c} {r : a ⟶ a'} {i' : a' ⟶ c} {cc : c ⟶ d} {k₁ : a' ⟶ e} {k₂ : e ⟶ e'}
    {j : e' ⟶ d} {k₁' : a ⟶ e} (h1 : i ≫ ψ = r ≫ i') (h2 : i' ≫ cc = (k₁ ≫ k₂) ≫ j)
    (h3 : r ≫ k₁ = k₁') : i ≫ ψ ≫ cc = (k₁' ≫ k₂) ≫ j := by
  rw [← Category.assoc, h1, Category.assoc, h2, ← Category.assoc, ← Category.assoc, h3]

end CategoryTheory

namespace AlgebraicGeometry.Stack.EtaleSmoothLift

universe u w

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {𝒳 𝒳' : AlgebraicStacks.{u, w} B S hS} {ι : 𝒳 ⟶ 𝒳'} {hι : IsThickening ι}
  {W : AlgebraicSpaces B S hS}
  {x : (algebraicSpaceStackFunctor B S hS).obj W ⟶ 𝒳}
  {hx : AlgebraicStacks.IsSmooth B S hS x}

attribute [local irreducible] Space.modulePullback Space.smallEtaleRingedSite Space.structureSheaf
  Space.smallEtaleRingedToposHom Space.chartFunctor Space.comparisonFunctor
  Space.modulePullbackCompIso

variable (hι₁ : AlgebraicStacks.IsFirstOrderThickening B S hS ι)

/-- The restriction of `f'` to the closed subspaces of a composite is the composite of the
restrictions. -/
theorem liftsZRestriction_comp_liftsZMap {η' η ξ : EtaleSmoothLift B S hS ι hι W x hx}
    (n : Hom η' η) (m : Hom η ξ) :
    liftsZRestriction hι₁ n ≫ liftsZMap hι₁ m = liftsZMap hι₁ (n.comp m) :=
  ObjectProperty.hom_ext _ rfl

variable {η ξ : EtaleSmoothLift B S hS ι hι W x hx} (m : Hom η ξ)

/-- The square `V ⊂ V' ⟶ I'_ξ` of the restricted diagonal `Φ_m ∘ Δ'_η`, over the edge
`f₀ ∘ Δ_η`. -/
private theorem inclusion_comp_diagonal_comp_selfIntersectionMap_edge :
    Space.subspaceInclusion B S hS _ (liftsZ hι₁ η) ≫ (η.diagonal ≫ selfIntersectionMap m) =
      (@CategoryStruct.comp (AlgebraicSpaces B S hS) _ _ _ _ (liftsEdge hι₁ η)
        (selfIntersectionMapRestriction hι₁ m)) ≫
        Space.subspaceInclusion B S hS ξ.selfIntersection.pt (liftsW₀ hι₁ ξ) :=
  Space.comp_assoc_of_square_algebraicSpaces B S hS (liftsZ hι₁ η) (liftsW₀ hι₁ η)
    (liftsW₀ hι₁ ξ) η.diagonal (liftsEdge hι₁ η) (selfIntersectionMapRestriction hι₁ m)
    (liftsBase hι₁ η).2.2.square (selfIntersectionMap m)
    (selfIntersectionMapRestriction_square hι₁ m)

/-- The restricted diagonal `Φ_m ∘ Δ'_η` lies over `m.ambient` on the final object of `V'`. -/
private theorem diagonal_comp_selfIntersectionMap_fst_final
    (hι₁ : AlgebraicStacks.IsFirstOrderThickening B S hS ι) :
    (η.diagonal ≫ selfIntersectionMap m) ≫ ξ.selfIntersection.fst =
      (((Space.SpacesEtale.inclusion B S hS η.ambient).obj
        (Space.SpacesEtale.final B S hS η.ambient)).hom ≫ 𝟙 η.ambient) ≫ m.ambient :=
  Space.comp_comp_eq_comp_of_comp_eq B S hS (selfIntersectionMap m) η.selfIntersection.fst
    ξ.selfIntersection.fst m.ambient (selfIntersectionMap_fst m) η.diagonal _
    (liftsBase hι₁ η).2.1.1

/-- The square `V ⊂ V' ⟶ I'_ξ` of the restricted diagonal `Φ_m ∘ Δ'_η`, over the edge
`Δ_ξ ∘ f`. -/
theorem inclusion_comp_diagonal_comp_selfIntersectionMap :
    Space.subspaceInclusion B S hS _ (liftsZ hι₁ η) ≫ (η.diagonal ≫ selfIntersectionMap m) =
      (@CategoryStruct.comp (AlgebraicSpaces B S hS) _ _ _ _ (liftsZMap hι₁ m)
        (diagonalRestriction hι₁ ξ)) ≫
        Space.subspaceInclusion B S hS ξ.selfIntersection.pt (liftsW₀ hι₁ ξ) :=
  (inclusion_comp_diagonal_comp_selfIntersectionMap_edge hι₁ m).trans
    (congrArg (· ≫ Space.subspaceInclusion B S hS ξ.selfIntersection.pt (liftsW₀ hι₁ ξ))
      (liftsEdge_comp_selfIntersectionMapRestriction hι₁ m))

/-- The restricted diagonal `Φ_m ∘ Δ'_η` is a section of `p'_ξ` over `f'`. -/
theorem diagonal_comp_selfIntersectionMap_fst :
    (η.diagonal ≫ selfIntersectionMap m) ≫ ξ.selfIntersection.fst = m.ambient ≫ 𝟙 ξ.ambient := by
  rw [Category.assoc, selfIntersectionMap_fst, ← Category.assoc, diagonal_fst, Category.id_comp,
    Category.comp_id]

/-- The two edges `V ⟶ I_ξ`, `Δ_ξ ∘ f = f₀ ∘ Δ_η`, composed in `AlgebraicSpaces`. -/
theorem liftsZMap_comp_diagonalRestriction :
    @CategoryStruct.comp (AlgebraicSpaces B S hS) _ _ _ _ (liftsZMap hι₁ m)
        (diagonalRestriction hι₁ ξ) =
      @CategoryStruct.comp (AlgebraicSpaces B S hS) _ _ _ _ (liftsEdge hι₁ η)
        (selfIntersectionMapRestriction hι₁ m) :=
  (liftsEdge_comp_selfIntersectionMapRestriction hι₁ m).symm

/-- The datum `θ''` of Stacks 0CK6 along `Φ_m`, read over the edge `Δ_ξ ∘ f : V ⟶ I_ξ`. -/
abbrev postcompParamEdge (θ : LiftsActingGroup hι₁ η) : RestrictedParam hι₁ m :=
  eqToHom (congrArg (fun e => (Space.modulePullback B S hS e).obj
    (Space.sheafOfDifferentials B S hS
      (Space.subspaceInclusion B S hS ξ.selfIntersection.pt (liftsW₀ hι₁ ξ) ≫
        ξ.selfIntersection.fst))) (liftsZMap_comp_diagonalRestriction hι₁ m)) ≫
    postcompParam hι₁ m θ

/-- The datum `postcompParamEdge hι₁ m θ` over the edge `Δ_ξ ∘ f` agrees with
`postcompParam hι₁ m θ` over the edge `f₀ ∘ Δ_η`, up to the equality of the two edges. -/
theorem heq_postcompParamEdge (θ : LiftsActingGroup hι₁ η) :
    HEq (postcompParamEdge hι₁ m θ) (postcompParam hι₁ m θ) :=
  heq_eqToHom_comp _ _

/-- A section `c` of `p'_ξ` over `f'`, restricting to the edge `Δ_ξ ∘ f` on `V`, moved by a
parameter over that edge (the action of Stacks 0CK6). -/
def moveRestricted (c : η.ambient ⟶ ξ.selfIntersection.pt)
    (hc : Space.subspaceInclusion B S hS _ (liftsZ hι₁ η) ≫ c =
      (@CategoryStruct.comp (AlgebraicSpaces B S hS) _ _ _ _ (liftsZMap hι₁ m)
        (diagonalRestriction hι₁ ξ)) ≫
        Space.subspaceInclusion B S hS ξ.selfIntersection.pt (liftsW₀ hι₁ ξ))
    (hcq : c ≫ ξ.selfIntersection.fst = m.ambient ≫ 𝟙 ξ.ambient)
    (θ : RestrictedParam hι₁ m) : η.ambient ⟶ ξ.selfIntersection.pt :=
  Space.derivationMove B S hS (liftsZ hι₁ η) (liftsW₀ hι₁ ξ)
    (@CategoryStruct.comp (AlgebraicSpaces B S hS) _ _ _ _ (liftsZMap hι₁ m)
      (diagonalRestriction hι₁ ξ)) ξ.selfIntersection.fst
    (isFirstOrderThickening_liftsZ hι₁ η) c hc θ (m.ambient ≫ 𝟙 ξ.ambient) hcq

/-- **The action over the edge `Δ_ξ ∘ f` is free.** -/
theorem eq_of_moveRestricted_eq {c c' : η.ambient ⟶ ξ.selfIntersection.pt} (hcc : c = c') (hc hcq)
    (hc' hcq') {θ θ' : RestrictedParam hι₁ m}
    (h : moveRestricted hι₁ m c hc hcq θ = moveRestricted hι₁ m c' hc' hcq' θ') : θ = θ' :=
  eq_of_heq (Space.heq_of_derivationMove_eq B S hS (liftsZ hι₁ η) (liftsW₀ hι₁ ξ) rfl
    ξ.selfIntersection.fst (isFirstOrderThickening_liftsZ hι₁ η)
    (isFirstOrderThickening_preimage_fst hι₁ ξ) hcc hc hc' rfl hcq hcq' h)

/-- The restricted diagonal `Φ_m ∘ Δ'_η` moved by a datum of Stacks 0CK6 over the edge `f₀ ∘ Δ_η`,
as in `AlgebraicGeometry.Stack.EtaleSmoothLift.derivationMove_postcompParam_autParam`. -/
def movePostcomp (θ : LiftsActingGroup hι₁ η) : η.ambient ⟶ ξ.selfIntersection.pt :=
  Space.derivationMove B S hS (liftsZ hι₁ η) (liftsW₀ hι₁ ξ)
    (@CategoryStruct.comp (AlgebraicSpaces B S hS) _ _ _ _ (liftsEdge hι₁ η)
      (selfIntersectionMapRestriction hι₁ m)) ξ.selfIntersection.fst
    (Space.isFirstOrderThickening_preimage B S hS _ _
      (isFirstOrderThickening_range_inclusion hι₁ η))
    (η.diagonal ≫ selfIntersectionMap m)
    (Space.comp_assoc_of_square_algebraicSpaces B S hS (liftsZ hι₁ η) (liftsW₀ hι₁ η)
      (liftsW₀ hι₁ ξ) η.diagonal (liftsEdge hι₁ η) (selfIntersectionMapRestriction hι₁ m)
      (liftsBase hι₁ η).2.2.square (selfIntersectionMap m)
      (selfIntersectionMapRestriction_square hι₁ m))
    (postcompParam hι₁ m θ)
    ((((Space.SpacesEtale.inclusion B S hS η.ambient).obj
      (Space.SpacesEtale.final B S hS η.ambient)).hom ≫ 𝟙 η.ambient) ≫ m.ambient)
    (Space.comp_comp_eq_comp_of_comp_eq B S hS (selfIntersectionMap m) η.selfIntersection.fst
      ξ.selfIntersection.fst m.ambient (selfIntersectionMap_fst m) η.diagonal _
      (liftsBase hι₁ η).2.1.1)

/-- The restricted diagonal `Φ_m ∘ Δ'_η` moved over the edge `Δ_ξ ∘ f` by
`postcompParamEdge hι₁ m θ` is `movePostcomp hι₁ m θ`. -/
theorem moveRestricted_postcompParamEdge (θ : LiftsActingGroup hι₁ η) :
    moveRestricted hι₁ m _ (inclusion_comp_diagonal_comp_selfIntersectionMap hι₁ m)
        (diagonal_comp_selfIntersectionMap_fst m) (postcompParamEdge hι₁ m θ) =
      movePostcomp hι₁ m θ :=
  Space.derivationMove_congr_edge B S hS (liftsZ hι₁ η) (liftsW₀ hι₁ ξ)
    (liftsZMap_comp_diagonalRestriction hι₁ m) ξ.selfIntersection.fst
    (isFirstOrderThickening_liftsZ hι₁ η) rfl
    (inclusion_comp_diagonal_comp_selfIntersectionMap hι₁ m)
    (inclusion_comp_diagonal_comp_selfIntersectionMap_edge hι₁ m) (heq_postcompParamEdge hι₁ m θ)
    ((congrArg (· ≫ m.ambient) (Category.comp_id ((Space.SpacesEtale.inclusion B S hS
      η.ambient).obj (Space.SpacesEtale.final B S hS η.ambient)).hom)).trans
      ((Category.id_comp m.ambient).trans (Category.comp_id m.ambient).symm)).symm
    (diagonal_comp_selfIntersectionMap_fst m)
    (diagonal_comp_selfIntersectionMap_fst_final m hι₁)

/-- **The section `δ_τ` pushed along `Φ_m` is the restricted diagonal moved by the datum of
`θ_τ`**, Stacks 0CK6 at `Φ_m`. -/
theorem movePostcomp_autParam (τ : Hom η η) (hτ : τ.base = 𝟙 η.base) :
    movePostcomp hι₁ m (autParam hι₁ η τ hτ) = η.autLift τ ≫ selfIntersectionMap m := by
  have hη := (congrArg Subtype.val (autParam_vadd hι₁ η τ hτ)).symm.trans
    (coe_lifts_vadd hι₁ η (autParam hι₁ η τ hτ) (liftsBase hι₁ η))
  have hcomp := Space.derivationMove_comp B S hS (liftsZ hι₁ η) (liftsW₀ hι₁ η) (liftsW₀ hι₁ ξ)
    (liftsEdge hι₁ η) (selfIntersectionMapRestriction hι₁ m) (selfIntersectionMap m)
    (selfIntersectionMapRestriction_square hι₁ m) η.selfIntersection.fst ξ.selfIntersection.fst
    m.ambient (selfIntersectionMapRestriction_comm hι₁ m) (selfIntersectionMap_fst m)
    (Space.isFirstOrderThickening_preimage B S hS _ _
      (isFirstOrderThickening_range_inclusion hι₁ η))
    (isFirstOrderThickening_preimage_fst hι₁ η) (isFirstOrderThickening_preimage_fst hι₁ ξ)
    η.diagonal (liftsBase hι₁ η).2.2.square (autParam hι₁ η τ hτ) _ (liftsBase hι₁ η).2.1.1
  exact hcomp.symm.trans (congrArg (· ≫ selfIntersectionMap m) hη).symm

/-- The restricted diagonal `Φ_m ∘ Δ'_η` moved over the edge `Δ_ξ ∘ f` by the datum of `θ_τ` is
the section `δ_τ` pushed along `Φ_m`. -/
theorem moveRestricted_postcompParamEdge_autParam (τ : Hom η η) (hτ : τ.base = 𝟙 η.base) :
    moveRestricted hι₁ m _ (inclusion_comp_diagonal_comp_selfIntersectionMap hι₁ m)
        (diagonal_comp_selfIntersectionMap_fst m) (postcompParamEdge hι₁ m (autParam hι₁ η τ hτ)) =
      η.autLift τ ≫ selfIntersectionMap m :=
  (moveRestricted_postcompParamEdge hι₁ m _).trans (movePostcomp_autParam hι₁ m τ hτ)

/-- `AlgebraicGeometry.Stack.EtaleSmoothLift.conormalRestrictionAlong`, with its target read on
the final object of `V'`. -/
abbrev conormalRestrictionAlongFinal {η ξ : EtaleSmoothLift B S hS ι hι W x hx} (m : Hom η ξ) :
    (Space.modulePullback B S hS (liftsZMap hι₁ m)).obj
        (Space.conormalModule B S hS ξ.ambient (baseSubspace hι₁ ξ)) ≅
      Space.conormalModule B S hS ((Space.SpacesEtale.toSpaces B S hS η.ambient).obj
        (Space.SpacesEtale.final B S hS η.ambient)) (liftsZ hι₁ η) :=
  conormalRestrictionAlong hι₁ m

variable {η' : EtaleSmoothLift B S hS ι hι W x hx} (n : Hom η' η)

/-- The square of the restricted diagonal `Φ_m ∘ Δ'_η` precomposed with `n`, over the edge
`Δ_ξ ∘ f` of the composite `n ≫ m`. -/
theorem inclusion_comp_ambient_comp_diagonal_comp_selfIntersectionMap :
    Space.subspaceInclusion B S hS _ (liftsZ hι₁ η') ≫ n.ambient ≫
        (η.diagonal ≫ selfIntersectionMap m) =
      (@CategoryStruct.comp (AlgebraicSpaces B S hS) _ _ _ _ (liftsZMap hι₁ (n.comp m))
        (diagonalRestriction hι₁ ξ)) ≫
        Space.subspaceInclusion B S hS ξ.selfIntersection.pt (liftsW₀ hι₁ ξ) :=
  CategoryTheory.comp_comp_eq_of_squares_paste (C := AlgebraicSpaces B S hS)
    (liftsZRestriction_square hι₁ n) (inclusion_comp_diagonal_comp_selfIntersectionMap hι₁ m)
    (liftsZRestriction_comp_liftsZMap hι₁ n m)

/-- The restricted diagonal `Φ_m ∘ Δ'_η` precomposed with `n` is a section of `p'_ξ` over the
ambient morphism of `n ≫ m`. -/
theorem ambient_comp_diagonal_comp_selfIntersectionMap_fst :
    (n.ambient ≫ η.diagonal ≫ selfIntersectionMap m) ≫ ξ.selfIntersection.fst =
      (n.comp m).ambient ≫ 𝟙 ξ.ambient :=
  (Category.assoc _ _ _).trans ((congrArg (n.ambient ≫ ·)
    (diagonal_comp_selfIntersectionMap_fst m)).trans (Category.assoc _ _ _).symm)

/-- **The reading of the parameters along a composite restricts** (the naturality of the
identification of the band with `SheafHom(Δ^*Ω_{I/U'}, 𝒞_{U/U'})`, Stacks 0CKG (2)): if
`τ' ≫ n = n ≫ τ` for endomorphisms over the identity, then the datum of `θ_{τ'}` along `n ≫ m`,
read through Stacks 03LU and 04CQ as a map of modules pulled back from `U`, is the restriction
along `n` of the reading of the datum of `θ_τ` along `m`. -/
theorem readParam_comp_eq (τ' : Hom η' η') (τ : Hom η η) (hτ' : τ'.base = 𝟙 η'.base)
    (hτ : τ.base = 𝟙 η.base) (h : τ'.comp n = n.comp τ) :
    (Iso.homCongr ((Space.modulePullbackCompIso B S hS
        (Z := ⟨(liftsW₀ hι₁ ξ).1.toFunctor, (liftsW₀ hι₁ ξ).2.1⟩) (liftsZMap hι₁ (n.comp m))
        (diagonalRestriction hι₁ ξ)).app (Space.sheafOfDifferentials B S hS
          (Space.subspaceInclusion B S hS ξ.selfIntersection.pt (liftsW₀ hι₁ ξ) ≫
            ξ.selfIntersection.fst))) (conormalRestrictionAlongFinal hι₁ (n.comp m))).symm
        (postcompParamEdge hι₁ (n.comp m) (autParam hι₁ η' τ' hτ')) =
      Space.QuasiCoherentDescent.restrictForm B S hS (liftsZRestriction hι₁ n) (liftsZMap hι₁ m)
        (liftsZMap hι₁ (n.comp m)) (liftsZRestriction_comp_liftsZMap hι₁ n m)
        ((Iso.homCongr ((Space.modulePullbackCompIso B S hS
        (Z := ⟨(liftsW₀ hι₁ ξ).1.toFunctor, (liftsW₀ hι₁ ξ).2.1⟩) (liftsZMap hι₁ m)
            (diagonalRestriction hι₁ ξ)).app (Space.sheafOfDifferentials B S hS
              (Space.subspaceInclusion B S hS ξ.selfIntersection.pt (liftsW₀ hι₁ ξ) ≫
                ξ.selfIntersection.fst))) (conormalRestrictionAlongFinal hι₁ m)).symm
          (postcompParamEdge hι₁ m (autParam hι₁ η τ hτ))) := by
  have H : n.ambient ≫ moveRestricted hι₁ m _
      (inclusion_comp_diagonal_comp_selfIntersectionMap hι₁ m)
      (diagonal_comp_selfIntersectionMap_fst m) (postcompParamEdge hι₁ m (autParam hι₁ η τ hτ)) =
      moveRestricted hι₁ (n.comp m) _
        (inclusion_comp_ambient_comp_diagonal_comp_selfIntersectionMap hι₁ m n)
        (ambient_comp_diagonal_comp_selfIntersectionMap_fst m n) _ :=
    Space.comp_derivationMove_restriction B S hS (baseSubspace hι₁ ξ) (liftsW₀ hι₁ ξ)
      (liftsZ hι₁ η) (liftsZ hι₁ η') n.ambient m.ambient (n.comp m).ambient rfl
      (liftsZMap hι₁ m) (liftsZMap hι₁ (n.comp m)) (liftsZMap_square hι₁ m)
      (liftsZMap_square hι₁ (n.comp m)) (diagonalRestriction hι₁ ξ) ξ.selfIntersection.fst
      (𝟙 ξ.ambient) (isFirstOrderThickening_liftsZ hι₁ η) (isFirstOrderThickening_liftsZ hι₁ η')
      (isFirstOrderThickening_preimage_fst hι₁ ξ) (liftsZRestriction hι₁ n)
      (liftsZRestriction_square hι₁ n) (liftsZRestriction_comp_liftsZMap hι₁ n m)
      (conormalRestrictionAlongFinal hι₁ m) rfl (conormalRestrictionAlongFinal hι₁ (n.comp m)) rfl
      (η.diagonal ≫ selfIntersectionMap m)
      (inclusion_comp_diagonal_comp_selfIntersectionMap hι₁ m)
      (diagonal_comp_selfIntersectionMap_fst m)
      (inclusion_comp_ambient_comp_diagonal_comp_selfIntersectionMap hι₁ m n)
      (ambient_comp_diagonal_comp_selfIntersectionMap_fst m n)
      (postcompParamEdge hι₁ m (autParam hι₁ η τ hτ)) _ rfl
  have H' := H.symm.trans ((congrArg (n.ambient ≫ ·)
    (moveRestricted_postcompParamEdge_autParam hι₁ m τ hτ)).trans
      (((Category.assoc _ _ _).symm.trans (congrArg (· ≫ selfIntersectionMap m)
        (autLift_comp_selfIntersectionMap n τ' τ h).symm)).trans
        ((Category.assoc _ _ _).trans ((congrArg (η'.autLift τ' ≫ ·)
          (selfIntersectionMap_comp n m).symm).trans
            (moveRestricted_postcompParamEdge_autParam hι₁ (n.comp m) τ' hτ').symm))))
  have hθ := eq_of_moveRestricted_eq hι₁ (n.comp m)
    (((Category.assoc _ _ _).symm.trans (congrArg (· ≫ selfIntersectionMap m)
      (diagonal_comp_selfIntersectionMap n).symm)).trans ((Category.assoc _ _ _).trans
        (congrArg (η'.diagonal ≫ ·) (selfIntersectionMap_comp n m).symm))) _ _ _ _ H'
  exact (congrArg (Iso.homCongr ((Space.modulePullbackCompIso B S hS
        (Z := ⟨(liftsW₀ hι₁ ξ).1.toFunctor, (liftsW₀ hι₁ ξ).2.1⟩) (liftsZMap hι₁ (n.comp m))
    (diagonalRestriction hι₁ ξ)).app (Space.sheafOfDifferentials B S hS
      (Space.subspaceInclusion B S hS ξ.selfIntersection.pt (liftsW₀ hι₁ ξ) ≫
        ξ.selfIntersection.fst))) (conormalRestrictionAlongFinal hι₁ (n.comp m))).symm
      hθ.symm).trans
    (Equiv.symm_apply_apply _ _)

end AlgebraicGeometry.Stack.EtaleSmoothLift
