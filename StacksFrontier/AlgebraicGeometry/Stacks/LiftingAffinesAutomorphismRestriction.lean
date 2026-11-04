module

public import StacksFrontier.AlgebraicGeometry.Stacks.LiftingAffinesAutomorphismEtale

/-!
# The restriction half of the étale compatibility of `Aut(ξ) ≅ SheafHom(Δ^*Ω, 𝒞)` (Stacks 0CKG (2))

Let `m = (f, f', γ_m) : η ⟶ ξ` be a morphism of smooth lifts of étale opens of `W`
(`AlgebraicGeometry.Stack.EtaleSmoothLift`, Stacks 0CJP) and `τ ≫ m = m ≫ σ` for endomorphisms over
the identity. Item (1) of the source's proof of Stacks 0CKG says that the identification of
equation 0CKH commutes with étale localization, through the footnote of the source and Stacks 0CK8.
`StacksFrontier.AlgebraicGeometry.Stacks.LiftingAffinesAutomorphismEtale` proved the half coming
from Stacks 0CK6 (pushing the parameter of `τ` along `Φ_m : I'_η ⟶ I'_ξ`); this file proves the
other half, the restriction law of the action of Stacks 061C along `f'` (Stacks 0CK8), and
concludes:

* `AlgebraicGeometry.Stack.EtaleSmoothLift.heq_postcompParam_autParam`: the parameter of `τ`,
  pushed along `Φ_m` by the datum of Stacks 0CK6, is the restriction along `m` of the parameter
  of `σ`.

## Implementation notes

The restriction `θ₂` of a parameter `θ` is never named by a definition. Its formula is the
right-hand side of the hypothesis of `AlgebraicGeometry.Space.comp_derivationMove_restriction`, a
morphism whose head is the coercion of `CategoryTheory.Iso.homCongr`; the kernel compares a
constant with such a term by unfolding the coercion side first, and that reduction reaches the
construction of the inverse image of modules and does not terminate in the allotted time. The
restriction is instead characterized by the restriction law it satisfies
(`AlgebraicGeometry.Stack.EtaleSmoothLift.IsRestrictParam`), which determines it because the
action is free; the witness is the formula itself, produced by unification with `rfl`.

## References

* [Stacks Project, Tag 0CKG](https://stacks.math.columbia.edu/tag/0CKG)
* [Stacks Project, Tag 0CK8](https://stacks.math.columbia.edu/tag/0CK8)
* [Stacks Project, Tag 061C](https://stacks.math.columbia.edu/tag/061C)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Space

universe u

variable (C : BigFppfSite.{u}) (S : Scheme.{u}) (hS : C.Contains S)

attribute [local irreducible] modulePullback

/-- **Freeness of the action of Stacks 061C, across a change of edge**: if `θ · c = θ' · c'` for
edges and sections equal along equations, then `θ` and `θ'` are heterogeneously equal. -/
theorem heq_of_derivationMove_eq {X W T : AlgebraicSpaces C S hS} (Z : ClosedSubspaces C S hS X.1)
    (W₀ : ClosedSubspaces C S hS W.1)
    {e₀ e₀' : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces C S hS) ⟶
      (⟨W₀.1.toFunctor, W₀.2.1⟩ : AlgebraicSpaces C S hS)} (he : e₀ = e₀')
    (q : W ⟶ T) (hZ : IsFirstOrderThickening C S hS X Z.1)
    (hW : IsFirstOrderThickening C S hS W W₀.1) {c c' : X ⟶ W} (hcc : c = c')
    (hc : subspaceInclusion C S hS X Z ≫ c = e₀ ≫ subspaceInclusion C S hS W W₀)
    (hc' : subspaceInclusion C S hS X Z ≫ c' = e₀' ≫ subspaceInclusion C S hS W W₀)
    {θ : (modulePullback C S hS e₀).obj
        (sheafOfDifferentials C S hS (subspaceInclusion C S hS W W₀ ≫ q)) ⟶
      conormalModule C S hS X Z}
    {θ' : (modulePullback C S hS e₀').obj
        (sheafOfDifferentials C S hS (subspaceInclusion C S hS W W₀ ≫ q)) ⟶
      conormalModule C S hS X Z} {p p' : X ⟶ T} (hp : p = p')
    (hcq : c ≫ q = p) (hcq' : c' ≫ q = p')
    (h : derivationMove C S hS Z W₀ e₀ q hZ c hc θ p hcq =
      derivationMove C S hS Z W₀ e₀' q hZ c' hc' θ' p' hcq') : HEq θ θ' := by
  subst he hcc hp
  exact heq_of_eq (derivationMove_injective C S hS Z W₀ e₀ q hZ hW c hc p hcq θ θ' h)

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.Stack.EtaleSmoothLift

universe u w

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {𝒳 𝒳' : AlgebraicStacks.{u, w} B S hS} {ι : 𝒳 ⟶ 𝒳'} {hι : IsThickening ι}
  {W : AlgebraicSpaces B S hS}
  {x : (algebraicSpaceStackFunctor B S hS).obj W ⟶ 𝒳}
  {hx : AlgebraicStacks.IsSmooth B S hS x}

section Compatibility

attribute [local irreducible] Space.modulePullback Space.smallEtaleRingedSite Space.structureSheaf
  Space.smallEtaleRingedToposHom Space.chartFunctor Space.comparisonFunctor
  Space.modulePullbackCompIso

variable (hι₁ : AlgebraicStacks.IsFirstOrderThickening B S hS ι)

/-- The closed subspace `U ⊂ U'`, read on the final object, is a first order thickening. -/
theorem isFirstOrderThickening_liftsZ (ξ : EtaleSmoothLift B S hS ι hι W x hx) :
    Space.IsFirstOrderThickening B S hS ((Space.SpacesEtale.toSpaces B S hS ξ.ambient).obj
      (Space.SpacesEtale.final B S hS ξ.ambient)) (liftsZ hι₁ ξ).1 :=
  Space.isFirstOrderThickening_preimage B S hS _ _ (isFirstOrderThickening_range_inclusion hι₁ ξ)

variable {η ξ : EtaleSmoothLift B S hS ι hι W x hx} (m : Hom η ξ)

/-- The diagonal of `ξ` restricted along `f'` lies over `U ⊂ U'` along `Δ ∘ f`. -/
theorem inclusion_comp_ambient_comp_diagonal :
    Space.subspaceInclusion B S hS η.ambient (liftsZ hι₁ η) ≫ m.ambient ≫ ξ.diagonal =
      (@CategoryStruct.comp (AlgebraicSpaces B S hS) _ _ _ _ (liftsZMap hι₁ m)
        (diagonalRestriction hι₁ ξ)) ≫
        Space.subspaceInclusion B S hS ξ.selfIntersection.pt (liftsW₀ hι₁ ξ) :=
  (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ ξ.diagonal) (liftsZMap_square hι₁ m)).trans
    ((Category.assoc _ _ _).trans ((congrArg (liftsZMap hι₁ m ≫ ·)
      (inclusion_comp_diagonal hι₁ ξ)).trans (Category.assoc _ _ _).symm)))

/-- The diagonal of `ξ` restricted along `f'` is a section of `p'` over `f'`. -/
theorem ambient_comp_diagonal_fst :
    (m.ambient ≫ ξ.diagonal) ≫ ξ.selfIntersection.fst = m.ambient ≫ 𝟙 ξ.ambient :=
  (Category.assoc _ _ _).trans (congrArg (m.ambient ≫ ·) (diagonal_fst ξ))

/-- The type of the restriction of a parameter of `ξ` along `m`: homomorphisms
`(Δ_ξ ∘ f)^*Ω_{I_ξ/U'} ⟶ 𝒞_{V/V'}`. -/
abbrev RestrictedParam :=
  (Space.modulePullback B S hS
      (@CategoryStruct.comp (AlgebraicSpaces B S hS) _ _ _ _ (liftsZMap hι₁ m)
        (diagonalRestriction hι₁ ξ))).obj
      (Space.sheafOfDifferentials B S hS
        (Space.subspaceInclusion B S hS ξ.selfIntersection.pt (liftsW₀ hι₁ ξ) ≫
          ξ.selfIntersection.fst)) ⟶
    Space.conormalModule B S hS η.ambient (liftsZ hι₁ η)

/-- **`θ₂` is the restriction of the parameter `θ` of `ξ` along `m`** (Stacks 0CK8 at
`f' : V' ⟶ U'`): moving the diagonal of `ξ` by `θ` and restricting along `f'` is moving the
restricted diagonal by `θ₂`, `(θ · Δ'_ξ) ∘ f' = θ₂ · (Δ'_ξ ∘ f')`. The action being free, `θ₂` is
determined by `θ` (`AlgebraicGeometry.Stack.EtaleSmoothLift.IsRestrictParam.unique`); it exists
by the restriction law of the action, `AlgebraicGeometry.Space.comp_derivationMove_restriction`
(`AlgebraicGeometry.Stack.EtaleSmoothLift.exists_isRestrictParam`), where it is `θ` read on `V`
through Stacks 03LU and 04CQ. -/
def IsRestrictParam (θ : LiftsActingGroup hι₁ ξ) (θ₂ : RestrictedParam hι₁ m) : Prop :=
  m.ambient ≫ Space.derivationMove B S hS (liftsZ hι₁ ξ) (liftsW₀ hι₁ ξ)
      (@CategoryStruct.comp (AlgebraicSpaces B S hS) _ _ _ _ (liftsProjection hι₁ ξ)
        (diagonalRestriction hι₁ ξ))
      ξ.selfIntersection.fst (isFirstOrderThickening_liftsZ hι₁ ξ) ξ.diagonal
      (liftsBase hι₁ ξ).2.2.square θ
      (((Space.SpacesEtale.inclusion B S hS ξ.ambient).obj
        (Space.SpacesEtale.final B S hS ξ.ambient)).hom ≫ 𝟙 ξ.ambient)
      (liftsBase hι₁ ξ).2.1.1 =
    Space.derivationMove B S hS (liftsZ hι₁ η) (liftsW₀ hι₁ ξ)
      (@CategoryStruct.comp (AlgebraicSpaces B S hS) _ _ _ _ (liftsZMap hι₁ m)
        (diagonalRestriction hι₁ ξ))
      ξ.selfIntersection.fst (isFirstOrderThickening_liftsZ hι₁ η) (m.ambient ≫ ξ.diagonal)
      (inclusion_comp_ambient_comp_diagonal hι₁ m) θ₂
      (m.ambient ≫ 𝟙 ξ.ambient) (ambient_comp_diagonal_fst m)

/-- **Every parameter of `ξ` has a restriction along `m`**: the restriction law of the action of
Stacks 061C along `f'` (Stacks 0CK8). -/
theorem exists_isRestrictParam (θ : LiftsActingGroup hι₁ ξ) :
    ∃ θ₂, IsRestrictParam hι₁ m θ θ₂ :=
  ⟨_, Space.comp_derivationMove_restriction B S hS (baseSubspace hι₁ ξ) (liftsW₀ hι₁ ξ)
    (liftsZ hι₁ ξ) (liftsZ hι₁ η) m.ambient
    ((Space.SpacesEtale.inclusion B S hS ξ.ambient).obj
      (Space.SpacesEtale.final B S hS ξ.ambient)).hom
    m.ambient (Category.comp_id _) (liftsProjection hι₁ ξ) (liftsZMap hι₁ m)
    (Space.conormalEtaleRestrictionSquare B S hS _ _) (liftsZMap_square hι₁ m)
    (diagonalRestriction hι₁ ξ) ξ.selfIntersection.fst (𝟙 ξ.ambient)
    (isFirstOrderThickening_liftsZ hι₁ ξ) (isFirstOrderThickening_liftsZ hι₁ η)
    (isFirstOrderThickening_preimage_fst hι₁ ξ) (liftsZRestriction hι₁ m)
    (liftsZRestriction_square hι₁ m) (liftsZRestriction_comp hι₁ m)
    (conormalRestrictionFinal hι₁ ξ) rfl (conormalRestrictionAlong hι₁ m) rfl ξ.diagonal
    (liftsBase hι₁ ξ).2.2.square (liftsBase hι₁ ξ).2.1.1
    (inclusion_comp_ambient_comp_diagonal hι₁ m) (ambient_comp_diagonal_fst m) θ _ rfl⟩

/-- The restriction of a parameter along `m` is unique: the action of Stacks 061C is free. -/
theorem IsRestrictParam.unique {θ : LiftsActingGroup hι₁ ξ} {θ₂ θ₂' : RestrictedParam hι₁ m}
    (h : IsRestrictParam hι₁ m θ θ₂) (h' : IsRestrictParam hι₁ m θ θ₂') : θ₂ = θ₂' :=
  Space.derivationMove_injective B S hS (liftsZ hι₁ η) (liftsW₀ hι₁ ξ) _
    ξ.selfIntersection.fst (isFirstOrderThickening_liftsZ hι₁ η)
    (isFirstOrderThickening_preimage_fst hι₁ ξ) _ _ _ _ _ _ (h.symm.trans h')

/-- The section `δ_σ ∘ f'` of `p'_ξ` over `f'`, as the restriction of the parameter of `σ` acting
on the restricted diagonal. -/
theorem ambient_comp_autLift_eq (σ : Hom ξ ξ) (hσ : σ.base = 𝟙 ξ.base) (θ₂)
    (hθ₂ : IsRestrictParam hι₁ m (autParam hι₁ ξ σ hσ) θ₂) :
    m.ambient ≫ ξ.autLift σ =
      Space.derivationMove B S hS (liftsZ hι₁ η) (liftsW₀ hι₁ ξ)
        (@CategoryStruct.comp (AlgebraicSpaces B S hS) _ _ _ _ (liftsZMap hι₁ m)
          (diagonalRestriction hι₁ ξ))
        ξ.selfIntersection.fst (isFirstOrderThickening_liftsZ hι₁ η) (m.ambient ≫ ξ.diagonal)
        (inclusion_comp_ambient_comp_diagonal hι₁ m) θ₂
        (m.ambient ≫ 𝟙 ξ.ambient) (ambient_comp_diagonal_fst m) :=
  (congrArg (m.ambient ≫ ·) ((congrArg Subtype.val (autParam_vadd hι₁ ξ σ hσ)).symm.trans
    (coe_lifts_vadd hι₁ ξ (autParam hι₁ ξ σ hσ) (liftsBase hι₁ ξ)))).trans hθ₂

/-- **Étale compatibility of the identification `Aut(ξ) ≅ SheafHom(Δ^*Ω, 𝒞)` (item (1) of the
source's proof of Stacks 0CKG, via its footnote and Stacks 0CK8).** If `τ ≫ m = m ≫ σ` for
endomorphisms over the identity, then the parameter of `τ`, pushed along `Φ_m` by the datum of
Stacks 0CK6, is the restriction along `m` of the parameter of `σ`; the two live over the two equal
edges `V ⟶ I_ξ`, hence the heterogeneous equality. -/
theorem heq_postcompParam_autParam (τ : Hom η η) (σ : Hom ξ ξ) (hτ : τ.base = 𝟙 η.base)
    (hσ : σ.base = 𝟙 ξ.base) (h : τ.comp m = m.comp σ) (θ₂)
    (hθ₂ : IsRestrictParam hι₁ m (autParam hι₁ ξ σ hσ) θ₂) :
    HEq (postcompParam hι₁ m (autParam hι₁ η τ hτ)) θ₂ :=
  Space.heq_of_derivationMove_eq B S hS (liftsZ hι₁ η) (liftsW₀ hι₁ ξ)
    (liftsEdge_comp_selfIntersectionMapRestriction hι₁ m) ξ.selfIntersection.fst
    (isFirstOrderThickening_liftsZ hι₁ η) (isFirstOrderThickening_preimage_fst hι₁ ξ)
    (diagonal_comp_selfIntersectionMap m) _ (inclusion_comp_ambient_comp_diagonal hι₁ m)
    ((congrArg (· ≫ m.ambient) (Category.comp_id ((Space.SpacesEtale.inclusion B S hS
      η.ambient).obj (Space.SpacesEtale.final B S hS η.ambient)).hom)).trans
      ((Category.id_comp m.ambient).trans (Category.comp_id m.ambient).symm)) _
    (ambient_comp_diagonal_fst m)
    ((derivationMove_postcompParam_autParam hι₁ m τ σ hτ hσ h).trans
      (ambient_comp_autLift_eq hι₁ m σ hσ θ₂ hθ₂))

end Compatibility

end AlgebraicGeometry.Stack.EtaleSmoothLift
