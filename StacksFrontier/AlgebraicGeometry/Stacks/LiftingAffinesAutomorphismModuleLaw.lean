module

public import StacksFrontier.AlgebraicGeometry.Stacks.LiftingAffinesAutomorphismScalars
public import StacksFrontier.CategoryTheory.Bicategory.WhiskerLeftCancelSelfIntersection
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.FormallyEtale

/-!
# Restriction of endomorphisms of smooth lifts is semilinear (Stacks 0CKG (2))

Let `m = (f, f', γ) : η ⟶ ξ` be a morphism of smooth lifts of étale opens of `W`
(`AlgebraicGeometry.Stack.EtaleSmoothLift`, Stacks 0CJP), and let `τ, τ'` be endomorphisms of `η`
and `σ, σ'` endomorphisms of `ξ`, all over the identity, with `τ ≫ m = m ≫ σ` and
`τ' ≫ m = m ≫ σ'`. If the parameter of `σ'` is the parameter of `σ` multiplied by a global regular
function `s` on `U`, then the parameter of `τ'` is the parameter of `τ` multiplied by `f^*s`
(`AlgebraicGeometry.Stack.EtaleSmoothLift.autParam_eq_of_comp_eq`). This is the compatibility of
the `𝒪`-module structure of `Aut(ξ) ≅ SheafHom(Δ^*Ω, 𝒞)` with restriction along `m`, item (1) of
the source's proof of Stacks 0CKG for scalars; at `m` an isomorphism over the identity it is the
linearity of conjugation.

The argument combines the étale compatibility of the identification
(`AlgebraicGeometry.Stack.EtaleSmoothLift.heq_postcompParam_autParam`), the semilinearity of the
restriction of parameters, and the injectivity of the datum `θ ↦ θ''` of Stacks 0CK6 along
`Φ_m : I'_η ⟶ I'_ξ` (`AlgebraicGeometry.Stack.EtaleSmoothLift.postcompParam_injective`). The last
holds because `Φ_m` is injective on the sections of `p'_η` which agree on `V`
(`AlgebraicGeometry.Stack.EtaleSmoothLift.eq_of_comp_selfIntersectionMap`): their second
projections agree by uniqueness of infinitesimal lifts along the étale `f'` (Stacks 0611), and
their 2-cells by the defining property of `Φ_m`.

## References

* [Stacks Project, Tag 0CKG](https://stacks.math.columbia.edu/tag/0CKG)
* [Stacks Project, Tag 0CK6](https://stacks.math.columbia.edu/tag/0CK6)
* [Stacks Project, Tag 0611](https://stacks.math.columbia.edu/tag/0611)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Bicategory

namespace AlgebraicGeometry.Space

universe u

variable (C : BigFppfSite.{u}) (S : Scheme.{u}) (hS : C.Contains S)

attribute [local irreducible] modulePullback

/-- Postcomposing heterogeneously equal maps out of inverse images along equal morphisms. -/
theorem heq_comp_of_heq {Z W₀ : AlgebraicSpaces C S hS} {e e' : Z ⟶ W₀} (he : e = e')
    (Ω : Modules.{u, u} C S hS W₀.1 W₀.2) {N N' : Modules.{u, u} C S hS Z.1 Z.2}
    {a : (modulePullback C S hS e).obj Ω ⟶ N} {b : (modulePullback C S hS e').obj Ω ⟶ N}
    (h : HEq a b) (g : N ⟶ N') : HEq (a ≫ g) (b ≫ g) := by
  subst he
  obtain rfl := eq_of_heq h
  rfl

end AlgebraicGeometry.Space

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
  {η ξ : EtaleSmoothLift B S hS ι hι W x hx} (m : Hom η ξ)

/-- **`Φ_m` is injective on the sections of `p'_η` agreeing on `V`.** Two morphisms
`δ₁, δ₂ : V' ⟶ I'_η` with the same first projection, the same restriction to `V`, and
`Φ_m ∘ δ₁ = Φ_m ∘ δ₂` are equal. -/
theorem eq_of_comp_selfIntersectionMap {δ₁ δ₂ : η.ambient ⟶ η.selfIntersection.pt}
    (hZ : Space.subspaceInclusion B S hS η.ambient (liftsZ hι₁ η) ≫ δ₁ =
      Space.subspaceInclusion B S hS η.ambient (liftsZ hι₁ η) ≫ δ₂)
    (hp : δ₁ ≫ η.selfIntersection.fst = δ₂ ≫ η.selfIntersection.fst)
    (hΦ : δ₁ ≫ selfIntersectionMap m = δ₂ ≫ selfIntersectionMap m) : δ₁ = δ₂ := by
  let F := algebraicSpaceStackFunctor.{u, w} B S hS
  have hFE : Space.FormallyEtale m.ambient.hom :=
    ((Space.isEtale_iff_isLocallyOfFinitePresentation_and_formallyEtale B S hS
      η.ambient.property ξ.ambient.property m.ambient.hom).mp (Hom.isEtale_ambient η ξ m)).2
  have hsnd : ∀ δ : η.ambient ⟶ η.selfIntersection.pt,
      δ ≫ η.selfIntersection.snd ≫ m.ambient = δ ≫ selfIntersectionMap m ≫ ξ.selfIntersection.snd :=
    fun δ => congrArg (δ ≫ ·) (selfIntersectionMap_snd m).symm
  have hq : δ₁ ≫ η.selfIntersection.snd = δ₂ ≫ η.selfIntersection.snd := by
    obtain ⟨c, -, huniq⟩ := Space.FormallyEtale.existsUnique_lift_of_firstOrderThickening B S hS
      (T' := (Space.SpacesEtale.toSpaces B S hS η.ambient).obj
        (Space.SpacesEtale.final B S hS η.ambient))
      m.ambient hFE (liftsZ hι₁ η).1 (isFirstOrderThickening_liftsZ hι₁ η)
      ((liftsZ hι₁ η).1.ι ≫ (δ₁ ≫ η.selfIntersection.snd).hom)
      ((δ₁ ≫ η.selfIntersection.snd ≫ m.ambient).hom) (Category.assoc _ _ _)
    have h1 := huniq (δ₁ ≫ η.selfIntersection.snd).hom ⟨rfl, rfl⟩
    have hZ' := congrArg (fun g => g.hom ≫ η.selfIntersection.snd.hom) hZ
    have h2 := huniq (δ₂ ≫ η.selfIntersection.snd).hom
      ⟨(Category.assoc _ _ _).symm.trans (hZ'.symm.trans (Category.assoc _ _ _)),
        congrArg (fun g => g.hom) (((Category.assoc _ _ _).trans (hsnd δ₂)).trans
          ((congrArg (· ≫ ξ.selfIntersection.snd) hΦ).symm.trans (hsnd δ₁).symm))⟩
    exact ObjectProperty.hom_ext _ (h1.trans h2.symm)
  have hmap : ∀ {Y : AlgebraicSpaces B S hS} {g₁ g₂ : η.ambient ⟶ η.selfIntersection.pt}
      {k : η.selfIntersection.pt ⟶ Y},
      g₁ ≫ k = g₂ ≫ k → F.map g₁ ≫ F.map k = F.map g₂ ≫ F.map k := fun h =>
    (F.map_comp _ _).symm.trans ((congrArg F.map h).trans (F.map_comp _ _))
  have e₁ : F.map (η.selfIntersection.fst ≫ m.ambient) ≫ ξ.ambientMap =
      F.map (selfIntersectionMap m) ≫ F.map ξ.selfIntersection.fst ≫ ξ.ambientMap :=
    (congrArg (fun g => F.map g ≫ ξ.ambientMap) (selfIntersectionMap_fst m).symm).trans
      ((congrArg (· ≫ ξ.ambientMap) (F.map_comp _ _)).trans (Category.assoc _ _ _))
  have e₂ : F.map (selfIntersectionMap m) ≫ F.map ξ.selfIntersection.snd ≫ ξ.ambientMap =
      F.map (η.selfIntersection.snd ≫ m.ambient) ≫ ξ.ambientMap :=
    ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ ξ.ambientMap) (F.map_comp _ _).symm)).trans
      (congrArg (fun g => F.map g ≫ ξ.ambientMap) (selfIntersectionMap_snd m))
  have hΦspec := eq_eqToHom_comp_comp_eqToHom_of_sandwich _ _ _ _
    ((selfIntersectionMapIso_hom m).symm.trans (selfIntersectionMap_spec m e₁ e₂)).symm
  refine hom_ext_of_isTwoFibreProduct_algebraicSpaceStackFunctor
    η.selfIntersection.isTwoFibreProduct.some hp hq
    (F.map_comp_map_comp_eq_of_comp_eq hp η.ambientMap)
    (F.map_comp_map_comp_eq_of_comp_eq hq η.ambientMap).symm ?_
  exact whiskerLeft_eq_of_comp_eq_of_selfIntersection η.selfIntersection.iso.hom
    ξ.selfIntersection.iso.hom m.comm _ _ hΦspec (hmap hp) (hmap hq) (hmap hΦ) _ _

/-- The 0CK6 composition law at the diagonal of `η`: `Φ_m ∘ (θ · Δ'_η) = θ'' · (Φ_m ∘ Δ'_η)`. -/
theorem derivationMove_comp_selfIntersectionMap (θ : LiftsActingGroup hι₁ η) :
    Space.derivationMove B S hS (liftsZ hι₁ η) (liftsW₀ hι₁ η) (liftsEdge hι₁ η)
        η.selfIntersection.fst (isFirstOrderThickening_liftsZ hι₁ η) η.diagonal
        (liftsBase hι₁ η).2.2.square θ
        (((Space.SpacesEtale.inclusion B S hS η.ambient).obj
          (Space.SpacesEtale.final B S hS η.ambient)).hom ≫ 𝟙 η.ambient)
        (liftsBase hι₁ η).2.1.1 ≫ selfIntersectionMap m =
      Space.derivationMove B S hS (liftsZ hι₁ η) (liftsW₀ hι₁ ξ)
        (@CategoryStruct.comp (AlgebraicSpaces B S hS) _ _ _ _ (liftsEdge hι₁ η)
          (selfIntersectionMapRestriction hι₁ m)) ξ.selfIntersection.fst
        (isFirstOrderThickening_liftsZ hι₁ η)
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
          (liftsBase hι₁ η).2.1.1) :=
  Space.derivationMove_comp B S hS (liftsZ hι₁ η) (liftsW₀ hι₁ η) (liftsW₀ hι₁ ξ)
    (liftsEdge hι₁ η) (selfIntersectionMapRestriction hι₁ m) (selfIntersectionMap m)
    (selfIntersectionMapRestriction_square hι₁ m) η.selfIntersection.fst ξ.selfIntersection.fst
    m.ambient (selfIntersectionMapRestriction_comm hι₁ m) (selfIntersectionMap_fst m)
    (isFirstOrderThickening_liftsZ hι₁ η) (isFirstOrderThickening_preimage_fst hι₁ η)
    (isFirstOrderThickening_preimage_fst hι₁ ξ) η.diagonal (liftsBase hι₁ η).2.2.square θ _
    (liftsBase hι₁ η).2.1.1

/-- **The datum of Stacks 0CK6 along `Φ_m` is injective.** -/
theorem postcompParam_injective {θ θ' : LiftsActingGroup hι₁ η}
    (h : postcompParam hι₁ m θ = postcompParam hι₁ m θ') : θ = θ' := by
  have spec := fun θ : LiftsActingGroup hι₁ η =>
    Space.derivationMove_spec B S hS (liftsZ hι₁ η) (liftsW₀ hι₁ η)
      (liftsEdge hι₁ η) η.selfIntersection.fst (isFirstOrderThickening_liftsZ hι₁ η)
      (isFirstOrderThickening_preimage_fst hι₁ η) η.diagonal (liftsBase hι₁ η).2.2.square θ _
      (liftsBase hι₁ η).2.1.1
  obtain ⟨hb, hbq, -, -⟩ := spec θ
  obtain ⟨hb', hbq', -, -⟩ := spec θ'
  have k1 := derivationMove_comp_selfIntersectionMap hι₁ m θ
  rw [h] at k1
  have key := k1.trans (derivationMove_comp_selfIntersectionMap hι₁ m θ').symm
  exact Space.derivationMove_injective B S hS (liftsZ hι₁ η) (liftsW₀ hι₁ η) _
    η.selfIntersection.fst (isFirstOrderThickening_liftsZ hι₁ η)
    (isFirstOrderThickening_preimage_fst hι₁ η) _ _ _ _ _ _
    (eq_of_comp_selfIntersectionMap hι₁ m (hb.trans hb'.symm) (hbq.trans hbq'.symm) key)

/-- **Restriction of endomorphisms along a morphism of smooth lifts is semilinear** (item (1) of
the source's proof of Stacks 0CKG, for the module structure). If `τ ≫ m = m ≫ σ`,
`τ' ≫ m = m ≫ σ'` and the parameter of `σ'` is the parameter of `σ` times a global regular function
`s` on `U`, then the parameter of `τ'` is the parameter of `τ` times `f^*s`. -/
theorem autParam_eq_of_comp_eq (τ τ' : Hom η η) (σ σ' : Hom ξ ξ) (hτ : τ.base = 𝟙 η.base)
    (hτ' : τ'.base = 𝟙 η.base) (hσ : σ.base = 𝟙 ξ.base) (hσ' : σ'.base = 𝟙 ξ.base)
    (h : τ.comp m = m.comp σ) (h' : τ'.comp m = m.comp σ')
    (s : Space.globalFunctions' B S hS ξ.base.obj.left.1)
    (hs : autParam hι₁ ξ σ' hσ' = autParam hι₁ ξ σ hσ ≫
      Space.globalFunctionsSmul B S hS (X := liftsZSpace hι₁ ξ) (liftsScalar hι₁ ξ s) _) :
    autParam hι₁ η τ' hτ' = autParam hι₁ η τ hτ ≫
      Space.globalFunctionsSmul B S hS (X := liftsZSpace hι₁ η)
        (liftsScalar hι₁ η (Space.globalFunctionsMap B S hS m.base.hom.left s))
        (Space.conormalModule B S hS η.ambient (liftsZ hι₁ η)) := by
  obtain ⟨θ₂, hθ₂⟩ := exists_isRestrictParam hι₁ m (autParam hι₁ ξ σ hσ)
  have r1 := heq_postcompParam_autParam hι₁ m τ σ hτ hσ h θ₂ hθ₂
  have hsm := hθ₂.smul hι₁ m s
  rw [← hs] at hsm
  have r2 := heq_postcompParam_autParam hι₁ m τ' σ' hτ' hσ' h' _ hsm
  have r3 := Space.heq_comp_of_heq B S hS (liftsEdge_comp_selfIntersectionMapRestriction hι₁ m)
    _ r1 (Space.globalFunctionsSmul B S hS (X := liftsZSpace hι₁ η)
      (liftsScalar hι₁ η (Space.globalFunctionsMap B S hS m.base.hom.left s))
      (Space.conormalModule B S hS η.ambient (liftsZ hι₁ η)))
  rw [← postcompParam_comp_globalFunctionsSmul] at r3
  exact postcompParam_injective hι₁ m (eq_of_heq (r2.trans r3.symm))

end AlgebraicGeometry.Stack.EtaleSmoothLift
