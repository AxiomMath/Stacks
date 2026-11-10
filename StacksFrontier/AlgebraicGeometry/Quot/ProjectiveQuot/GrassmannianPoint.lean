module

public import StacksFrontier.AlgebraicGeometry.Quot.ProjectiveQuot.FreeFrameBaseChange
public import StacksFrontier.AlgebraicGeometry.Recovery27.GrassmannianScheme

/-!
# The point of the Grassmannian attached to a point of `Quot^P`

Let `n ≥ 0`, `r ≥ 1`, `P ∈ ℚ[t]`, `m = AlgebraicGeometry.ProjectiveQuot.regularityIndex n r P`,
`N = freeRank n r m` (the dimension of `W = Γ(ℙⁿ_ℤ, 𝒪(m))^{⊕ r}`) and `p = ⌊P(m)⌋₊`. For
`K ∈ Quot^P(T)` with quotient `𝒬`, the composite

  `𝒪_T^{⊕ N} ≅ π_*(𝒪^{⊕ r}(m)) ⟶ π_*(𝒬(m))`

is a surjection onto a finite locally free module of rank `p`
(`AlgebraicGeometry.ProjectiveQuot.epi_pushforward_twistMap_quotientπ`,
`AlgebraicGeometry.ProjectiveQuot.isFiniteLocallyFreeOfRank_pushforward_twist_quotient`): a
`T`-point of the Grassmannian `G(N - p, N)` when `p ≤ N`. Its formation commutes with base change
(`AlgebraicGeometry.ProjectiveQuot.grassmannianPresentation_baseChange`): the pullback of the
presentation along `g : T' ⟶ T` is isomorphic to the presentation of the base change of `K`,
through the cohomology and base change isomorphism of `π_*(𝒬(m))`. This is the morphism
`Quot^P ⟶ G` of the proof of Stacks 0DPA.

## Main definitions

* `AlgebraicGeometry.ProjectiveQuot.quotRank`: `p = ⌊P(m)⌋₊`.
* `AlgebraicGeometry.ProjectiveQuot.grassmannianPresentation`: the presentation attached to `K`.
* `AlgebraicGeometry.ProjectiveQuot.grassmannianPoint`: its class, a `T`-point of
  `AlgebraicGeometry.Grassmannian.functor`.

## Main results

* `AlgebraicGeometry.ProjectiveQuot.grassmannianPresentation_baseChange`.
* `AlgebraicGeometry.ProjectiveQuot.functor_map_grassmannianPoint`: naturality in `T`.
* `AlgebraicGeometry.ProjectiveQuot.toGrassmannian`, `comp_toGrassmannian`: the classifying
  morphism `T ⟶ G(N - p, N)` and its naturality.

## References

* [Stacks Project, Tag 0DPA](https://stacks.math.columbia.edu/tag/0DPA)
* [Stacks Project, Tag 089S](https://stacks.math.columbia.edu/tag/089S)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.AlgebraicGeometry.AffinePushforward (baseChangeNatTrans)

universe u

namespace AlgebraicGeometry.ProjectiveQuot

variable {n r : ℕ}

variable (n r) in
/-- The rank `p = ⌊P(m)⌋₊` of `π_*(𝒬(m))` for `K ∈ Quot^P`, `m = regularityIndex n r P`. -/
def quotRank (P : Polynomial ℚ) : ℕ :=
  ⌊P.eval ((regularityIndex.{u} n r P : ℕ) : ℚ)⌋₊

variable {P : Polynomial ℚ}

/-- **The point of the Grassmannian attached to `K ∈ Quot^P(T)`**: the quotient
`𝒪_T^{⊕ N} ≅ π_*(𝒪^{⊕ r}(m)) ⟶ π_*(𝒬(m))`, finite locally free of rank `p`. -/
def grassmannianPresentation
    (hp : quotRank.{u} n r P ≤ freeRank.{u} n r (regularityIndex.{u} n r P))
    {T : Scheme.{u}} {K : Subobject (freeModule n r T)} (hK : K ∈ hilbertFamilies n r P T) :
    Grassmannian.QuotientPresentation T
      (freeRank.{u} n r (regularityIndex.{u} n r P) - quotRank.{u} n r P)
      (freeRank.{u} n r (regularityIndex.{u} n r P)) where
  target := (Scheme.Modules.pushforward (projectiveSpaceOver n T ↘ T)).obj
    (twist (regularityIndex.{u} n r P : ℤ) (quotient K))
  map := (pushforwardTwistFreeModuleIso (n := n) (r := r) T (regularityIndex.{u} n r P)).inv ≫
    (Scheme.Modules.pushforward (projectiveSpaceOver n T ↘ T)).map
      (twistMap (regularityIndex.{u} n r P : ℤ) (quotientπ K))
  map_epi := @epi_comp _ _ _ _ _ _
    (@IsIso.epi_of_iso _ _ _ _ _ (Iso.isIso_inv (pushforwardTwistFreeModuleIso (n := n) (r := r) T
      (regularityIndex.{u} n r P)))) _ (epi_pushforward_twistMap_quotientπ hK)
  finiteLocallyFree := by
    rw [Nat.sub_sub_self hp]
    exact isFiniteLocallyFreeOfRank_pushforward_twist_quotient hK

/-- **The base-change identification of the targets**:
`g^* π_*(𝒬(m)) ≅ π'_*(𝒬'(m))` for the base change `K' = baseChange g K`, the cohomology and base
change isomorphism followed by `(ℙⁿ_g)^*(𝒬(m)) ≅ ((ℙⁿ_g)^* 𝒬)(m) ≅ 𝒬'(m)`. -/
def grassmannianTargetBaseChangeIso {T' T : Scheme.{u}} (g : T' ⟶ T)
    {K : Subobject (freeModule n r T)} (hK : K ∈ hilbertFamilies n r P T) :
    (Scheme.Modules.pullback g).obj ((Scheme.Modules.pushforward (projectiveSpaceOver n T ↘ T)).obj
        (twist (regularityIndex.{u} n r P : ℤ) (quotient K))) ≅
      (Scheme.Modules.pushforward (projectiveSpaceOver n T' ↘ T')).obj
        (twist (regularityIndex.{u} n r P : ℤ) (quotient (baseChange g K))) :=
  @asIso _ _ _ _ ((baseChangeNatTrans (isPullback_projectiveSpaceOverMap n g).w).app
      (twist (regularityIndex.{u} n r P : ℤ) (quotient K)))
    (isIso_baseChangeNatTrans_twist_quotient hK g _ _ (isPullback_projectiveSpaceOverMap n g)) ≪≫
    (Scheme.Modules.pushforward (projectiveSpaceOver n T' ↘ T')).mapIso
      ((twistPullbackIso g (regularityIndex.{u} n r P : ℤ) (quotient K)).symm ≪≫
        (twistFunctor n T' (regularityIndex.{u} n r P : ℤ)).mapIso
          (quotientBaseChangeIso g K).symm)

/-- Two-step bookkeeping in an arbitrary category. -/
theorem comp_eq_comp_of_two {C : Type*} [Category* C] {A B D E F G : C} (a : A ⟶ B) (b : B ⟶ D)
    (c : D ⟶ E) (d : A ⟶ F) (k : F ⟶ D) (e : F ⟶ G) (f : G ⟶ E) (M1 : a ≫ b = d ≫ k)
    (M2 : k ≫ c = e ≫ f) : a ≫ b ≫ c = (d ≫ e) ≫ f := by
  rw [reassoc_of% M1, M2, Category.assoc]

/-- The bookkeeping of `grassmannianPresentation_baseChange`, in an arbitrary category. -/
theorem chain_of_points {C : Type*} [Category* C] {A A' B D E F H K : C}
    (a : A' ⟶ A) (h : A ⟶ A') (gAB : A ⟶ D) (gA : A ⟶ B) (gB : B ⟶ D) (bcQ : D ⟶ H)
    (X2 : H ⟶ K) (bcF : B ⟶ E) (X1 : E ⟶ H) (Φ : E ⟶ F) (Y : F ⟶ K) (pT' : A' ⟶ F)
    (H0 : gAB = gA ≫ gB) (N1 : gB ≫ bcQ = bcF ≫ X1) (N2 : X1 ≫ X2 = Φ ≫ Y)
    (S2 : gA ≫ bcF ≫ Φ = h ≫ pT') (hinv : a ≫ h = 𝟙 _) :
    (a ≫ gAB) ≫ (bcQ ≫ X2) = pT' ≫ Y := by
  rw [H0, Category.assoc, Category.assoc, reassoc_of% N1, N2, reassoc_of% S2, reassoc_of% hinv]

/-- A functor carries an equation between two-step composites to the corresponding equation. -/
private theorem map_comp_eq_map_comp {C D : Type*} [Category* C] [Category* D] (F : C ⥤ D)
    {A B X Y : C} {f : A ⟶ B} {g : B ⟶ X} {f' : A ⟶ Y} {g' : Y ⟶ X}
    (h : f ≫ g = f' ≫ g') : F.map f ≫ F.map g = F.map f' ≫ F.map g' := by
  rw [← F.map_comp, h, F.map_comp]

/-- **The point of the Grassmannian attached to `K` commutes with base change**: the pullback
along `g : T' ⟶ T` of the presentation of `K` is isomorphic to the presentation of
`baseChange g K`, through `AlgebraicGeometry.ProjectiveQuot.grassmannianTargetBaseChangeIso`. -/
theorem grassmannianPresentation_baseChange
    (hp : quotRank.{u} n r P ≤ freeRank.{u} n r (regularityIndex.{u} n r P))
    {T' T : Scheme.{u}} (g : T' ⟶ T) {K : Subobject (freeModule n r T)}
    (hK : K ∈ hilbertFamilies n r P T) :
    (Grassmannian.pullbackPresentation g (grassmannianPresentation hp hK)).Isomorphic
      (grassmannianPresentation hp (baseChange_mem_hilbertFamilies g hK)) := by
  refine ⟨grassmannianTargetBaseChangeIso g hK, ?_⟩
  have hnat := twistPullbackIso_hom_naturality g (regularityIndex.{u} n r P : ℤ) (quotientπ K)
  have M1 := (inv_comp_eq_comp_inv_of_hom_comp
    (twistPullbackIso g (regularityIndex.{u} n r P : ℤ) (freeModule n r T))
    (twistPullbackIso g (regularityIndex.{u} n r P : ℤ) (quotient K)) _ _ hnat.symm).symm
  have M2mod := inv_comp_eq_comp_inv_of_hom_comp (freeModulePullbackIso n r g).symm
    (quotientBaseChangeIso g K) _ _ (quotientπ_quotientBaseChangeIso_hom g K).symm
  have M2 : twistMap (regularityIndex.{u} n r P : ℤ)
        ((Scheme.Modules.pullback (projectiveSpaceOverMap n g)).map (quotientπ K)) ≫
        (twistFunctor n T' (regularityIndex.{u} n r P : ℤ)).map
          (quotientBaseChangeIso g K).inv =
      twistMap (regularityIndex.{u} n r P : ℤ) (freeModulePullbackIso n r g).hom ≫
        twistMap (regularityIndex.{u} n r P : ℤ) (quotientπ (baseChange g K)) :=
    by
    simp only [twistMap_eq_twistFunctor_map]
    exact map_comp_eq_map_comp _ M2mod.symm
  have N2 := map_comp_eq_map_comp (Scheme.Modules.pushforward (projectiveSpaceOver n T' ↘ T'))
    (comp_eq_comp_of_two _ _ _ _ _ _ _ M1 M2)
  have N1 := (baseChangeNatTrans (isPullback_projectiveSpaceOverMap n g).w).naturality
    (twistMap (regularityIndex.{u} n r P : ℤ) (quotientπ K))
  exact chain_of_points (C := T'.Modules) _ _ _ _ _ _ _ _ _ _ _ _
    (Functor.map_comp _ _ _) N1 N2
    (pushforwardTwistFreeModuleIso_baseChange n r g (regularityIndex.{u} n r P))
    (Grassmannian.pullbackFreeIso g _).inv_hom_id

/-- **The `T`-point of the Grassmannian `G(N - p, N)` attached to `K ∈ Quot^P(T)`.** -/
def grassmannianPoint
    (hp : quotRank.{u} n r P ≤ freeRank.{u} n r (regularityIndex.{u} n r P))
    {T : Scheme.{u}} {K : Subobject (freeModule n r T)} (hK : K ∈ hilbertFamilies n r P T) :
    (Grassmannian.functor.{u}
      (freeRank.{u} n r (regularityIndex.{u} n r P) - quotRank.{u} n r P)
      (freeRank.{u} n r (regularityIndex.{u} n r P))).obj (Opposite.op T) :=
  ((Grassmannian.functorData _ _).objEquiv T).symm ⟦grassmannianPresentation hp hK⟧

/-- **Naturality of the Grassmannian point**: the Grassmannian functor carries the point of `K`
along `g : T' ⟶ T` to the point of `baseChange g K`. -/
theorem functor_map_grassmannianPoint
    (hp : quotRank.{u} n r P ≤ freeRank.{u} n r (regularityIndex.{u} n r P))
    {T' T : Scheme.{u}} (g : T' ⟶ T) {K : Subobject (freeModule n r T)}
    (hK : K ∈ hilbertFamilies n r P T) :
    (Grassmannian.functor.{u} _ _).map g.op (grassmannianPoint hp hK) =
      grassmannianPoint hp (baseChange_mem_hilbertFamilies g hK) := by
  apply ((Grassmannian.functorData _ _).objEquiv T').injective
  rw [grassmannianPoint, grassmannianPoint, Equiv.apply_symm_apply]
  let := Grassmannian.small_points T
    (freeRank.{u} n r (regularityIndex.{u} n r P) - quotRank.{u} n r P)
    (freeRank.{u} n r (regularityIndex.{u} n r P))
  let := Grassmannian.small_points T'
    (freeRank.{u} n r (regularityIndex.{u} n r P) - quotRank.{u} n r P)
    (freeRank.{u} n r (regularityIndex.{u} n r P))
  change (equivShrink _).symm (equivShrink _ (Grassmannian.pullbackPointsMap g _ _
      ((equivShrink _).symm (equivShrink _ ⟦grassmannianPresentation hp hK⟧)))) = _
  rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  exact Quotient.sound (Relation.EqvGen.rel _ _ (grassmannianPresentation_baseChange hp g hK))

/-- **The morphism `T ⟶ G(N - p, N)` classifying the point of `K ∈ Quot^P(T)`**, through the
representability of the Grassmannian functor by `AlgebraicGeometry.Grassmannian.scheme`. -/
def toGrassmannian
    (hp : quotRank.{u} n r P ≤ freeRank.{u} n r (regularityIndex.{u} n r P))
    {T : Scheme.{u}} {K : Subobject (freeModule n r T)} (hK : K ∈ hilbertFamilies n r P T) :
    T ⟶ Grassmannian.scheme.{u}
      (freeRank.{u} n r (regularityIndex.{u} n r P) - quotRank.{u} n r P)
      (freeRank.{u} n r (regularityIndex.{u} n r P)) :=
  (Grassmannian.schemeRepresentableBy _ _).homEquiv.symm (grassmannianPoint hp hK)

/-- **`K ↦ (T ⟶ G)` is natural in `T`**:
`g ≫ toGrassmannian K = toGrassmannian (baseChange g K)`. -/
theorem comp_toGrassmannian
    (hp : quotRank.{u} n r P ≤ freeRank.{u} n r (regularityIndex.{u} n r P))
    {T' T : Scheme.{u}} (g : T' ⟶ T) {K : Subobject (freeModule n r T)}
    (hK : K ∈ hilbertFamilies n r P T) :
    g ≫ toGrassmannian hp hK = toGrassmannian hp (baseChange_mem_hilbertFamilies g hK) := by
  apply (Grassmannian.schemeRepresentableBy _ _).homEquiv.injective
  rw [(Grassmannian.schemeRepresentableBy _ _).homEquiv_comp, toGrassmannian, toGrassmannian,
    Equiv.apply_symm_apply, Equiv.apply_symm_apply, functor_map_grassmannianPoint]

end AlgebraicGeometry.ProjectiveQuot

end
