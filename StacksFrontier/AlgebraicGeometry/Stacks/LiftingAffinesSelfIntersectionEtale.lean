module

public import StacksFrontier.AlgebraicGeometry.Stacks.LiftingAffinesAutomorphismModuleLaw
public import StacksFrontier.AlgebraicGeometry.Stacks.LiftingAffinesAutomorphismScalars
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafOfDifferentialsMapEtale

/-!
# The morphism of self-intersections of a morphism of smooth lifts is étale

Let `m = (f, f', γ_m) : η ⟶ ξ` be a morphism of smooth lifts of étale opens of `W`
(`AlgebraicGeometry.Stack.EtaleSmoothLift`, Stacks 0CJP), with self-intersections
`I'_η = V' ×_{y'} V'` and `I'_ξ = U' ×_{x'} U'` and the induced morphism
`Φ_m : I'_η ⟶ I'_ξ` (`AlgebraicGeometry.Stack.EtaleSmoothLift.selfIntersectionMap`). Since
`γ_m : y' ≅ x' ∘ f'`, the space `I'_η` is `V' ×_{f', U'} I'_ξ ×_{U', f'} V'`, so `Φ_m` is a
composite of two base changes of the étale `f'`, hence étale. This is used in the proof of
Stacks 0CKG (2): it makes the comparison of the sheaves of differentials `Δ^*Ω_{I/U'}` along `f'`
an isomorphism.

Concretely, with `J = V' ×_{f', U', p'_ξ} I'_ξ`, the square
`I'_η ⟶ J` (by `(p'_η, Φ_m)`), `q'_η : I'_η ⟶ V'`, `q'_ξ ∘ pr₂ : J ⟶ U'`, `f' : V' ⟶ U'` is
cartesian (`AlgebraicGeometry.Stack.EtaleSmoothLift.isPullback_selfIntersectionMapLift`); the
2-cell computation behind it is done once in an arbitrary strict bicategory
(`CategoryTheory.Bicategory.whiskerLeft_comp_eq_of_selfIntersection`).

## Main results

* `AlgebraicGeometry.Stack.EtaleSmoothLift.isEtale_selfIntersectionMap`: `Φ_m` is étale.
* `AlgebraicGeometry.Stack.EtaleSmoothLift.isEtale_selfIntersectionMapRestriction`: so is its
  restriction `f₀ : I_η ⟶ I_ξ` to the thickenings.

## References

* [Stacks Project, Tag 0CKG](https://stacks.math.columbia.edu/tag/0CKG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Bicategory CategoryTheory.Limits

namespace CategoryTheory.Bicategory

universe w₀ v₀ u₀

variable {𝔅 : Type u₀} [Bicategory.{w₀, v₀} 𝔅] [Bicategory.Strict 𝔅]

/-- **Recovering a whiskering of `γ_ξ` from a whiskering of `γ_η`.** If `Φ` carries `γ_ξ` to the
conjugate of `γ_η` by `c`, and `δ ◁ γ_η` is the conjugate of `D ◁ γ_ξ` by `c`, then
`(δ ≫ Φ) ◁ γ_ξ = D ◁ γ_ξ` up to `eqToHom`s. -/
theorem whiskerLeft_comp_eq_of_selfIntersection {T A B P Q C : 𝔅} {pη qη : P ⟶ A} {y : A ⟶ C}
    (γη : pη ≫ y ⟶ qη ≫ y) {pξ qξ : Q ⟶ B} {x : B ⟶ C} (γξ : pξ ≫ x ⟶ qξ ≫ x) {f : A ⟶ B}
    (c : y ⟶ f ≫ x) [IsIso c] {Φ : P ⟶ Q} (e₀ : Φ ≫ pξ ≫ x = pη ≫ f ≫ x)
    (e₃ : qη ≫ f ≫ x = Φ ≫ qξ ≫ x)
    (hΦ : Φ ◁ γξ = eqToHom e₀ ≫ ((pη ◁ inv c) ≫ γη ≫ (qη ◁ c)) ≫ eqToHom e₃)
    (δ : T ⟶ P) (D : T ⟶ Q)
    (b₁ : δ ≫ pη ≫ y = (δ ≫ pη) ≫ y) (b₂ : (δ ≫ pη) ≫ f ≫ x = D ≫ pξ ≫ x)
    (b₃ : D ≫ qξ ≫ x = (δ ≫ qη) ≫ f ≫ x) (b₄ : (δ ≫ qη) ≫ y = δ ≫ qη ≫ y)
    (hδ : δ ◁ γη = eqToHom b₁ ≫ (((δ ≫ pη) ◁ c) ≫ eqToHom b₂ ≫ (D ◁ γξ) ≫ eqToHom b₃ ≫
      ((δ ≫ qη) ◁ inv c)) ≫ eqToHom b₄)
    (e₁ : (δ ≫ Φ) ≫ pξ ≫ x = D ≫ pξ ≫ x) (e₂ : D ≫ qξ ≫ x = (δ ≫ Φ) ≫ qξ ≫ x) :
    (δ ≫ Φ) ◁ γξ = eqToHom e₁ ≫ (D ◁ γξ) ≫ eqToHom e₂ := by
  have a₂ : (δ ≫ pη) ≫ f ≫ x = (δ ≫ Φ) ≫ pξ ≫ x := by simp only [Strict.assoc, e₀]
  have a₃ : (δ ≫ Φ) ≫ qξ ≫ x = (δ ≫ qη) ≫ f ≫ x := by simp only [Strict.assoc, e₃]
  have h := whiskerLeft_eq_of_selfIntersection γη γξ c e₀ e₃ hΦ δ (δ ≫ pη) (δ ≫ qη) (δ ≫ Φ)
    rfl rfl rfl b₁ a₂ a₃ b₄
  rw [h] at hδ
  simp only [Category.assoc, cancel_epi] at hδ
  simp only [← Category.assoc, cancel_mono] at hδ
  simp only [Category.assoc] at hδ
  rw [← cancel_epi (eqToHom a₂), ← cancel_mono (eqToHom a₃)]
  simpa using hδ

/-- `CategoryTheory.Bicategory.whiskerLeft_comp_eq_of_selfIntersection` with the composites
`δ ≫ pη`, `δ ≫ qη` and `δ ≫ Φ` given as variables carrying their defining equations. -/
theorem whiskerLeft_eq_of_selfIntersection_of_whiskerLeft_eq {T A B P Q C : 𝔅} {pη qη : P ⟶ A}
    {y : A ⟶ C} (γη : pη ≫ y ⟶ qη ≫ y) {pξ qξ : Q ⟶ B} {x : B ⟶ C} (γξ : pξ ≫ x ⟶ qξ ≫ x)
    {f : A ⟶ B} (c : y ⟶ f ≫ x) [IsIso c] {Φ : P ⟶ Q} (e₀ : Φ ≫ pξ ≫ x = pη ≫ f ≫ x)
    (e₃ : qη ≫ f ≫ x = Φ ≫ qξ ≫ x)
    (hΦ : Φ ◁ γξ = eqToHom e₀ ≫ ((pη ◁ inv c) ≫ γη ≫ (qη ◁ c)) ≫ eqToHom e₃)
    (δ : T ⟶ P) (dp dq : T ⟶ A) (D DΦ : T ⟶ Q) (hp : δ ≫ pη = dp) (hq : δ ≫ qη = dq)
    (hDΦ : δ ≫ Φ = DΦ)
    (b₁ : δ ≫ pη ≫ y = dp ≫ y) (b₂ : dp ≫ f ≫ x = D ≫ pξ ≫ x)
    (b₃ : D ≫ qξ ≫ x = dq ≫ f ≫ x) (b₄ : dq ≫ y = δ ≫ qη ≫ y)
    (hδ : δ ◁ γη = eqToHom b₁ ≫ ((dp ◁ c) ≫ eqToHom b₂ ≫ (D ◁ γξ) ≫ eqToHom b₃ ≫
      (dq ◁ inv c)) ≫ eqToHom b₄)
    (e₁ : DΦ ≫ pξ ≫ x = D ≫ pξ ≫ x) (e₂ : D ≫ qξ ≫ x = DΦ ≫ qξ ≫ x) :
    DΦ ◁ γξ = eqToHom e₁ ≫ (D ◁ γξ) ≫ eqToHom e₂ := by
  subst hp hq hDΦ
  exact whiskerLeft_comp_eq_of_selfIntersection γη γξ c e₀ e₃ hΦ δ D b₁ b₂ b₃ b₄ hδ e₁ e₂

end CategoryTheory.Bicategory

namespace AlgebraicGeometry.Stack.EtaleSmoothLift

universe u w

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {𝒳 𝒳' : AlgebraicStacks.{u, w} B S hS} {ι : 𝒳 ⟶ 𝒳'} {hι : IsThickening ι}
  {W : AlgebraicSpaces B S hS}
  {x : (algebraicSpaceStackFunctor B S hS).obj W ⟶ 𝒳}
  {hx : AlgebraicStacks.IsSmooth B S hS x}

variable {η ξ : EtaleSmoothLift B S hS ι hι W x hx} (m : Hom η ξ)

private theorem map_eq_of_comp_eq {T I U : AlgebraicSpaces B S hS} {h : T ⟶ I} {k : I ⟶ U}
    {g : T ⟶ U} (hk : h ≫ k = g) :
    (algebraicSpaceStackFunctor.{u, w} B S hS).map h ≫
        (algebraicSpaceStackFunctor.{u, w} B S hS).map k =
      (algebraicSpaceStackFunctor.{u, w} B S hS).map g :=
  ((algebraicSpaceStackFunctor.{u, w} B S hS).map_comp _ _).symm.trans
    (congrArg (algebraicSpaceStackFunctor.{u, w} B S hS).map hk)

/-- The two composites `I'_η ⟶ 𝒳'` through `Φ_m` followed by the first projection of `I'_ξ`, and
through the first projection of `I'_η` followed by `f'`, agree. -/
theorem selfIntersectionMap_eq₀ :
    (algebraicSpaceStackFunctor B S hS).map (selfIntersectionMap m) ≫
        (algebraicSpaceStackFunctor B S hS).map ξ.selfIntersection.fst ≫ ξ.ambientMap =
      (algebraicSpaceStackFunctor B S hS).map η.selfIntersection.fst ≫
        (algebraicSpaceStackFunctor B S hS).map m.ambient ≫ ξ.ambientMap := by
  rw [← Category.assoc, ← Category.assoc, map_eq_of_comp_eq (selfIntersectionMap_fst m),
    map_eq_of_comp_eq rfl]

/-- The two composites `I'_η ⟶ 𝒳'` through the second projection of `I'_η` followed by `f'`, and
through `Φ_m` followed by the second projection of `I'_ξ`, agree. -/
theorem selfIntersectionMap_eq₃ :
    (algebraicSpaceStackFunctor B S hS).map η.selfIntersection.snd ≫
        (algebraicSpaceStackFunctor B S hS).map m.ambient ≫ ξ.ambientMap =
      (algebraicSpaceStackFunctor B S hS).map (selfIntersectionMap m) ≫
        (algebraicSpaceStackFunctor B S hS).map ξ.selfIntersection.snd ≫ ξ.ambientMap := by
  rw [← Category.assoc, ← Category.assoc, map_eq_of_comp_eq (selfIntersectionMap_snd m),
    map_eq_of_comp_eq rfl]

/-- The defining 2-cell identity of `Φ_m`: `Φ_m^*γ_ξ` is `γ_η` conjugated by `γ_m`. -/
theorem selfIntersectionMap_whiskerLeft
    (e₀ : (algebraicSpaceStackFunctor B S hS).map (selfIntersectionMap m) ≫
        (algebraicSpaceStackFunctor B S hS).map ξ.selfIntersection.fst ≫ ξ.ambientMap =
      (algebraicSpaceStackFunctor B S hS).map η.selfIntersection.fst ≫
        (algebraicSpaceStackFunctor B S hS).map m.ambient ≫ ξ.ambientMap)
    (e₃ : (algebraicSpaceStackFunctor B S hS).map η.selfIntersection.snd ≫
        (algebraicSpaceStackFunctor B S hS).map m.ambient ≫ ξ.ambientMap =
      (algebraicSpaceStackFunctor B S hS).map (selfIntersectionMap m) ≫
        (algebraicSpaceStackFunctor B S hS).map ξ.selfIntersection.snd ≫ ξ.ambientMap) :
    (algebraicSpaceStackFunctor B S hS).map (selfIntersectionMap m) ◁
        ξ.selfIntersection.iso.hom = eqToHom e₀ ≫
      (((algebraicSpaceStackFunctor B S hS).map η.selfIntersection.fst ◁ inv m.comm) ≫
        η.selfIntersection.iso.hom ≫
          ((algebraicSpaceStackFunctor B S hS).map η.selfIntersection.snd ◁ m.comm)) ≫
        eqToHom e₃ := by
  let F := algebraicSpaceStackFunctor.{u, w} B S hS
  have e₁ : F.map (η.selfIntersection.fst ≫ m.ambient) ≫ ξ.ambientMap =
      F.map (selfIntersectionMap m) ≫ F.map ξ.selfIntersection.fst ≫ ξ.ambientMap :=
    (congrArg (fun g => F.map g ≫ ξ.ambientMap) (selfIntersectionMap_fst m).symm).trans
      ((congrArg (· ≫ ξ.ambientMap) (F.map_comp _ _)).trans (Category.assoc _ _ _))
  have e₂ : F.map (selfIntersectionMap m) ≫ F.map ξ.selfIntersection.snd ≫ ξ.ambientMap =
      F.map (η.selfIntersection.snd ≫ m.ambient) ≫ ξ.ambientMap :=
    ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ ξ.ambientMap) (F.map_comp _ _).symm)).trans
      (congrArg (fun g => F.map g ≫ ξ.ambientMap) (selfIntersectionMap_snd m))
  exact eq_eqToHom_comp_comp_eqToHom_of_sandwich _ _ _ _
    ((selfIntersectionMapIso_hom m).symm.trans (selfIntersectionMap_spec m e₁ e₂)).symm

/-- **The morphism `(p'_η, Φ_m) : I'_η ⟶ V' ×_{f', U', p'_ξ} I'_ξ`.** -/
def selfIntersectionMapLift :
    η.selfIntersection.pt ⟶ pullback m.ambient ξ.selfIntersection.fst :=
  pullback.lift η.selfIntersection.fst (selfIntersectionMap m) (selfIntersectionMap_fst m).symm

/-- The first component of `selfIntersectionMapLift m` is the first projection of `I'_η`. -/
theorem selfIntersectionMapLift_fst :
    selfIntersectionMapLift m ≫ pullback.fst _ _ = η.selfIntersection.fst :=
  pullback.lift_fst _ _ _

/-- The second component of `selfIntersectionMapLift m` is `selfIntersectionMap m`. -/
theorem selfIntersectionMapLift_snd :
    selfIntersectionMapLift m ≫ pullback.snd _ _ = selfIntersectionMap m :=
  pullback.lift_snd _ _ _

/-- **Existence half of the cartesian square**: a point `b` of `V'` and a point `a` of
`V' ×_{U'} I'_ξ` with `f'(b) = q'_ξ(a)` come from a point of `I'_η`. -/
theorem exists_selfIntersectionMapLift {T : AlgebraicSpaces B S hS} (b : T ⟶ η.ambient)
    (a : T ⟶ pullback m.ambient ξ.selfIntersection.fst)
    (hab : b ≫ m.ambient = a ≫ pullback.snd _ _ ≫ ξ.selfIntersection.snd) :
    ∃ h : T ⟶ η.selfIntersection.pt, h ≫ η.selfIntersection.snd = b ∧
      h ≫ selfIntersectionMapLift m = a := by
  let F := algebraicSpaceStackFunctor.{u, w} B S hS
  let j₁ := pullback.fst m.ambient ξ.selfIntersection.fst
  let j₂ := pullback.snd m.ambient ξ.selfIntersection.fst
  have E₂ : F.map (a ≫ j₁) ≫ F.map m.ambient ≫ ξ.ambientMap =
      F.map (a ≫ j₂) ≫ F.map ξ.selfIntersection.fst ≫ ξ.ambientMap := by
    rw [← Category.assoc, ← Category.assoc, map_eq_of_comp_eq rfl, map_eq_of_comp_eq rfl,
      Category.assoc a j₁, pullback.condition, Category.assoc]
  have E₃ : F.map (a ≫ j₂) ≫ F.map ξ.selfIntersection.snd ≫ ξ.ambientMap =
      F.map b ≫ F.map m.ambient ≫ ξ.ambientMap := by
    rw [← Category.assoc, ← Category.assoc, map_eq_of_comp_eq rfl, map_eq_of_comp_eq rfl,
      Category.assoc a j₂, hab]
  let ζ : F.map (a ≫ j₁) ≫ η.ambientMap ≅ F.map b ≫ η.ambientMap :=
    whiskerLeftIso (F.map (a ≫ j₁)) (asIso m.comm) ≪≫ eqToIso E₂ ≪≫
      whiskerLeftIso (F.map (a ≫ j₂)) ξ.selfIntersection.iso ≪≫ eqToIso E₃ ≪≫
        whiskerLeftIso (F.map b) (asIso m.comm).symm
  obtain ⟨h, hp, hq, hspec⟩ := exists_lift_of_isTwoFibreProduct_algebraicSpaceStackFunctor
    η.selfIntersection.isTwoFibreProduct.some (a ≫ j₁) b ζ
  refine ⟨h, hq, pullback.hom_ext ?_ ?_⟩
  · rwa [Category.assoc, selfIntersectionMapLift_fst]
  rw [Category.assoc, selfIntersectionMapLift_snd]
  have hp' : (h ≫ selfIntersectionMap m) ≫ ξ.selfIntersection.fst =
      (a ≫ j₂) ≫ ξ.selfIntersection.fst := by
    rw [Category.assoc, selfIntersectionMap_fst, ← Category.assoc, hp, Category.assoc,
      pullback.condition, Category.assoc]
  have hq' : (h ≫ selfIntersectionMap m) ≫ ξ.selfIntersection.snd =
      (a ≫ j₂) ≫ ξ.selfIntersection.snd := by
    rw [Category.assoc, selfIntersectionMap_snd, ← Category.assoc, hq, hab, Category.assoc]
  have e₁ : F.map (a ≫ j₁) ≫ η.ambientMap =
      F.map h ≫ F.map η.selfIntersection.fst ≫ η.ambientMap := by
    rw [← Category.assoc, map_eq_of_comp_eq hp]
  have e₂ : F.map h ≫ F.map η.selfIntersection.snd ≫ η.ambientMap = F.map b ≫ η.ambientMap := by
    rw [← Category.assoc, map_eq_of_comp_eq hq]
  have hδ : F.map h ◁ η.selfIntersection.iso.hom =
      eqToHom e₁.symm ≫ ζ.hom ≫ eqToHom e₂.symm := by
    rw [hspec e₁ e₂]
    simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp, eqToHom_trans,
      Category.comp_id]
    rfl
  refine hom_ext_of_isTwoFibreProduct_algebraicSpaceStackFunctor
    ξ.selfIntersection.isTwoFibreProduct.some hp' hq'
    (F.map_comp_map_comp_eq_of_comp_eq hp' ξ.ambientMap)
    (F.map_comp_map_comp_eq_of_comp_eq hq' ξ.ambientMap).symm ?_
  refine whiskerLeft_eq_of_selfIntersection_of_whiskerLeft_eq η.selfIntersection.iso.hom
    ξ.selfIntersection.iso.hom m.comm (selfIntersectionMap_eq₀ m) (selfIntersectionMap_eq₃ m)
    (selfIntersectionMap_whiskerLeft m (selfIntersectionMap_eq₀ m) (selfIntersectionMap_eq₃ m))
    (F.map h)
    (F.map (a ≫ j₁)) (F.map b) (F.map (a ≫ j₂)) (F.map (h ≫ selfIntersectionMap m))
    (map_eq_of_comp_eq hp) (map_eq_of_comp_eq hq) (map_eq_of_comp_eq rfl) e₁.symm E₂ E₃ e₂.symm
    ?_ _ _
  rw [hδ]
  simp [ζ]

/-- **Uniqueness half of the cartesian square.** -/
theorem selfIntersectionMapLift_hom_ext {T : AlgebraicSpaces B S hS}
    {h h' : T ⟶ η.selfIntersection.pt}
    (hq : h ≫ η.selfIntersection.snd = h' ≫ η.selfIntersection.snd)
    (hl : h ≫ selfIntersectionMapLift m = h' ≫ selfIntersectionMapLift m) : h = h' := by
  let F := algebraicSpaceStackFunctor.{u, w} B S hS
  have hp : h ≫ η.selfIntersection.fst = h' ≫ η.selfIntersection.fst := by
    simpa only [Category.assoc, selfIntersectionMapLift_fst] using
      congrArg (· ≫ pullback.fst _ _) hl
  have hΦ : h ≫ selfIntersectionMap m = h' ≫ selfIntersectionMap m := by
    simpa only [Category.assoc, selfIntersectionMapLift_snd] using
      congrArg (· ≫ pullback.snd _ _) hl
  have hmap : ∀ {Y : AlgebraicSpaces B S hS} {g₁ g₂ : T ⟶ η.selfIntersection.pt}
      {k : η.selfIntersection.pt ⟶ Y},
      g₁ ≫ k = g₂ ≫ k → F.map g₁ ≫ F.map k = F.map g₂ ≫ F.map k := fun h =>
    (F.map_comp _ _).symm.trans ((congrArg F.map h).trans (F.map_comp _ _))
  refine hom_ext_of_isTwoFibreProduct_algebraicSpaceStackFunctor
    η.selfIntersection.isTwoFibreProduct.some hp hq
    (F.map_comp_map_comp_eq_of_comp_eq hp η.ambientMap)
    (F.map_comp_map_comp_eq_of_comp_eq hq η.ambientMap).symm ?_
  exact whiskerLeft_eq_of_comp_eq_of_selfIntersection η.selfIntersection.iso.hom
    ξ.selfIntersection.iso.hom m.comm (selfIntersectionMap_eq₀ m) (selfIntersectionMap_eq₃ m)
    (selfIntersectionMap_whiskerLeft m (selfIntersectionMap_eq₀ m) (selfIntersectionMap_eq₃ m))
    (hmap hp)
    (hmap hq) (hmap hΦ) _ _

/-- **`I'_η = V' ×_{f', U'} (V' ×_{U'} I'_ξ)`**: the square `(q'_η, (p'_η, Φ_m))` over
`(f', q'_ξ ∘ pr₂)` is cartesian. -/
theorem isPullback_selfIntersectionMapLift :
    IsPullback η.selfIntersection.snd (selfIntersectionMapLift m) m.ambient
      (pullback.snd m.ambient ξ.selfIntersection.fst ≫ ξ.selfIntersection.snd) := by
  have w : η.selfIntersection.snd ≫ m.ambient = selfIntersectionMapLift m ≫
      pullback.snd m.ambient ξ.selfIntersection.fst ≫ ξ.selfIntersection.snd := by
    rw [← Category.assoc, selfIntersectionMapLift_snd, selfIntersectionMap_snd]
  choose l hl₁ hl₂ using fun s : PullbackCone m.ambient
      (pullback.snd m.ambient ξ.selfIntersection.fst ≫ ξ.selfIntersection.snd) =>
    exists_selfIntersectionMapLift m s.fst s.snd s.condition
  exact IsPullback.of_isLimit (PullbackCone.IsLimit.mk w l hl₁ hl₂
    fun s _ h₁ h₂ => selfIntersectionMapLift_hom_ext m (h₁.trans (hl₁ s).symm)
      (h₂.trans (hl₂ s).symm))

/-- **`Φ_m : I'_η ⟶ I'_ξ` is étale**: it is the composite of `(p'_η, Φ_m)`, a base change of the
étale `f'`, and the projection `V' ×_{U'} I'_ξ ⟶ I'_ξ`, another base change of `f'`. -/
theorem isEtale_selfIntersectionMap : Space.IsEtale B S hS (selfIntersectionMap m).hom := by
  rw [← selfIntersectionMapLift_snd m]
  exact Space.isEtale_comp B S hS
    (Space.isEtale_of_isPullback B S hS _ _ _ _ (isPullback_selfIntersectionMapLift m)
      (Hom.isEtale_ambient η ξ m))
    (Space.isEtale_of_isPullback B S hS _ _ _ _
      (IsPullback.of_hasPullback m.ambient ξ.selfIntersection.fst) (Hom.isEtale_ambient η ξ m))

variable (hι₁ : AlgebraicStacks.IsFirstOrderThickening B S hS ι)

/-- The thickening `I_η ⊂ I'_η` is the inverse image of `I_ξ ⊂ I'_ξ` along `Φ_m`. -/
theorem liftsW₀_eq_preimage :
    (liftsW₀ hι₁ η).1 = (liftsW₀ hι₁ ξ).1.preimage (selfIntersectionMap m).hom := by
  have hZ := congrArg Subtype.val (liftsZ_eq_preimageSubspace hι₁ m)
  refine Subfunctor.ext (funext fun V => Set.ext fun z => ?_)
  have hz : ξ.selfIntersection.fst.hom.app V ((selfIntersectionMap m).hom.app V z) =
      m.ambient.hom.app V (η.selfIntersection.fst.hom.app V z) :=
    congrArg (fun g => g.hom.app V z) (selfIntersectionMap_fst m)
  show η.selfIntersection.fst.hom.app V z ∈ (liftsZ hι₁ η).1.obj V ↔
    ξ.selfIntersection.fst.hom.app V ((selfIntersectionMap m).hom.app V z) ∈
      (Subfunctor.range ξ.inclusion.hom).obj V
  rw [hz, hZ]
  rfl

/-- **The restriction `f₀ : I_η ⟶ I_ξ` of `Φ_m` to the thickenings is étale**, a base change of
`Φ_m`. -/
theorem isEtale_selfIntersectionMapRestriction :
    Space.IsEtale B S hS (selfIntersectionMapRestriction hι₁ m).hom := by
  have hpb := Subfunctor.isPullback_of_eq_preimage (selfIntersectionMap m).hom
    (liftsW₀_eq_preimage m hι₁) (selfIntersectionMapRestriction hι₁ m).hom
    (congrArg (fun g => g.hom) (selfIntersectionMapRestriction_square hι₁ m)).symm
  have hpb' : IsPullback (selfIntersectionMapRestriction hι₁ m)
      (Space.subspaceInclusion B S hS η.selfIntersection.pt (liftsW₀ hι₁ η))
      (Space.subspaceInclusion B S hS ξ.selfIntersection.pt (liftsW₀ hι₁ ξ))
      (selfIntersectionMap m) :=
    IsPullback.of_map_of_faithful
      (F := ObjectProperty.ι fun F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u =>
        IsAlgebraicSpace B S hS F) hpb
  exact Space.isEtale_of_isPullback B S hS _ _ _ _ hpb'.flip (isEtale_selfIntersectionMap m)

section Differentials

attribute [local irreducible] Space.modulePullback Space.smallEtaleRingedSite Space.structureSheaf
  Space.smallEtaleRingedToposHom Space.chartFunctor Space.comparisonFunctor
  Space.modulePullbackCompIso

/-- **The canonical map `c_{f₀} : f₀^*Ω_{I_ξ/U'} ⟶ Ω_{I_η/V'}` of Stacks 04CX is an
isomorphism**, `f₀` and `f'` being étale. -/
theorem isIso_selfIntersectionDifferentialsMap :
    IsIso (Space.sheafOfDifferentialsMap B S hS (selfIntersectionMapRestriction hι₁ m)
      (Space.subspaceInclusion B S hS ξ.selfIntersection.pt (liftsW₀ hι₁ ξ) ≫
        ξ.selfIntersection.fst)
      (Space.subspaceInclusion B S hS η.selfIntersection.pt (liftsW₀ hι₁ η) ≫
        η.selfIntersection.fst) m.ambient (selfIntersectionMapRestriction_comm hι₁ m)) :=
  Space.isIso_sheafOfDifferentialsMap_of_isEtale B S hS _ _ _ _
    (isEtale_selfIntersectionMapRestriction m hι₁) (Hom.isEtale_ambient η ξ m) _

/-- **The 0CK6 datum `θ ↦ θ''` along `Φ_m` is a bijection** from the parameters of `η` to the
maps `(Δ_ξ ∘ f)^*Ω_{I_ξ/U'} ⟶ 𝒞_{V/V'}`: it is precomposition with an isomorphism, `c_{f₀}` being
one. -/
theorem postcompParam_bijective : Function.Bijective (postcompParam hι₁ m) := by
  have := isIso_selfIntersectionDifferentialsMap m hι₁
  exact ⟨fun _ _ h => postcompParam_injective hι₁ m h,
    fun θ'' => ⟨_, Space.postcompDerivationDatum_map_inv_comp B S hS _ _ _ _ _ _ _ θ''⟩⟩

end Differentials

end AlgebraicGeometry.Stack.EtaleSmoothLift
