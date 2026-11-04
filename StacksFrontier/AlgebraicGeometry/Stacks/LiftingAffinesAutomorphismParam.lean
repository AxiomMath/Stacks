module

public import StacksFrontier.AlgebraicGeometry.Stacks.LiftingAffinesAutomorphismAbelian

/-!
# Endomorphisms of a smooth lift as homomorphisms of modules (Stacks 0CKG (2), global part)

Let `𝒳 ⊂ 𝒳'` be a first-order thickening of algebraic stacks and `ξ = (U, U', a, i, x', α)` a
smooth lift of an étale open of `W` (`AlgebraicGeometry.Stack.EtaleSmoothLift`, Stacks 0CJP).
The proof of Stacks 0CKG identifies `Aut(ξ)` with `SheafHom_{𝒪_U}(Δ^*Ω_{I/U}, 𝒞_{U/U'})`
(equation 0CKH): an endomorphism `σ` of `ξ` over the identity is a section `δ_σ` of
`p' : I' ⟶ U'` restricting to the diagonal over `U`, and these sections form a torsor under that
group by Stacks 061C. This file proves the identification on global sections:

* `AlgebraicGeometry.Stack.EtaleSmoothLift.autParam`: the parameter `θ_σ` of `σ`, the unique
  `θ` with `θ · Δ' = δ_σ`;
* `AlgebraicGeometry.Stack.EtaleSmoothLift.autParam_comp`: composition is addition,
  `θ_{σ ≫ τ} = θ_σ + θ_τ` (item (3) of the source's proof of 0CKH);
* `AlgebraicGeometry.Stack.EtaleSmoothLift.autParam_injective` and
  `AlgebraicGeometry.Stack.EtaleSmoothLift.exists_autParam_eq`: `σ ↦ θ_σ` is a bijection from
  the endomorphisms of `ξ` over the identity onto the acting group; surjectivity is the
  converse construction `AlgebraicGeometry.Stack.EtaleSmoothLift.homOfLift`, the endomorphism
  `(id, q' ∘ δ, δ^*γ)` attached to a section `δ` of `p'` restricting to the diagonal, which is
  the source's "to be explicit" formula.

## References

* [Stacks Project, Tag 0CKG](https://stacks.math.columbia.edu/tag/0CKG)
* [Stacks Project, Tag 061C](https://stacks.math.columbia.edu/tag/061C)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Bicategory Opposite

/-- **A torsor argument for additivity.** In the situation of `AddAction.eq_of_translation`, the
translation parameters are additive: `θ (m * n) = θ m + θ n`. -/
theorem AddAction.add_of_translation {T L M : Type*} [AddCommGroup T] [AddAction T L] (o : L)
    (hfree : ∀ θ₁ θ₂ : T, θ₁ +ᵥ o = θ₂ +ᵥ o → θ₁ = θ₂) (x : M → L) (θ : M → T)
    (hθ : ∀ m, θ m +ᵥ o = x m) (φ : T → T) (mul : M → M → M)
    (hmul : ∀ m n, x (mul m n) = φ (θ m) +ᵥ x n) (e : M) (he : x e = o)
    (hre : ∀ m, x (mul m e) = x m) (m n : M) : θ (mul m n) = θ m + θ n := by
  have hφ : ∀ k, φ (θ k) = θ k := fun k =>
    hfree _ _ (((congrArg (φ (θ k) +ᵥ ·) he).symm.trans (hmul k e).symm).trans
      ((hre k).trans (hθ k).symm))
  apply hfree
  rw [hθ, hmul, hφ, ← hθ n, vadd_vadd]

namespace CategoryTheory

/-- Two `eqToHom`-sandwiches of morphisms which agree identify the two inner morphisms. -/
theorem eq_eqToHom_comp_comp_eqToHom_of_eq {𝒞 : Type*} [Category 𝒞] {P P' Q Q' _R R' : 𝒞}
    {Y : P' ⟶ Q'} {Z : R' ⟶ Q} (a₁ : P = P') (a₂ : Q' = Q) (b₁ : P = R')
    (h : eqToHom a₁ ≫ Y ≫ eqToHom a₂ = eqToHom b₁ ≫ Z) :
    Y = eqToHom (a₁.symm.trans b₁) ≫ Z ≫ eqToHom a₂.symm := by
  subst a₁ a₂ b₁
  simpa using h

/-- Two `eqToHom`-sandwiches which agree identify their inner morphisms, up to `eqToHom`. -/
theorem eq_eqToHom_comp_comp_eqToHom_of_sandwich {𝒞 : Type*} [Category 𝒞] {P P' Q Q' R R' : 𝒞}
    {Y : P' ⟶ Q'} {Z : R ⟶ R'} (a₁ : P = P') (a₂ : Q' = Q) (b₁ : P = R) (b₂ : R' = Q)
    (h : eqToHom a₁ ≫ Y ≫ eqToHom a₂ = eqToHom b₁ ≫ Z ≫ eqToHom b₂) :
    Y = eqToHom (a₁.symm.trans b₁) ≫ Z ≫ eqToHom (b₂.trans a₂.symm) := by
  subst a₁ a₂ b₁ b₂
  simpa using h

/-- Merging two leading `eqToHom`s. -/
theorem eqToHom_comp_eqToHom_comp_eq {𝒞 : Type*} [Category 𝒞] {X Y Z Z' : 𝒞} (a : X = Y)
    (b : Y = Z) (Q : Z ⟶ Z') (c : X = Z) : eqToHom a ≫ eqToHom b ≫ Q = eqToHom c ≫ Q := by
  subst a b
  simp

/-- A morphism whose `eqToHom`-sandwich is an `eqToHom` is an `eqToHom`. -/
theorem eq_eqToHom_of_eqToHom_comp_comp_eqToHom {𝒞 : Type*} [Category 𝒞] {P P' Q Q' : 𝒞}
    {X : P ⟶ Q} (a : P' = P) (b : Q = Q') (h : P' = Q') (hX : eqToHom a ≫ X ≫ eqToHom b = eqToHom h)
    (h' : P = Q) : X = eqToHom h' := by
  subst a b
  simpa using hX

/-- Changing the `eqToHom` on both sides of an equation of composites. -/
theorem comp_eqToHom_eq_of_comp_eqToHom_eq {𝒞 : Type*} [Category 𝒞] {X Y Y₁ Y₂ Z X' : 𝒞}
    (c : X ⟶ Y) (a : X ⟶ X') (M : X' ⟶ Z) (e₁ : Y = Y₁) (r₁ : Z = Y₁)
    (hc : c ≫ eqToHom e₁ = a ≫ M ≫ eqToHom r₁) (e₂ : Y = Y₂) (r₂ : Z = Y₂) :
    c ≫ eqToHom e₂ = a ≫ M ≫ eqToHom r₂ := by
  subst e₁ e₂
  simpa using hc

end CategoryTheory

namespace CategoryTheory.Bicategory

universe w₀ v₀ u₀

variable {𝔅 : Type u₀} [Bicategory.{w₀, v₀} 𝔅] [Bicategory.Strict 𝔅]

/-- **A whiskering that is an `eqToHom` stays one along an equal composite.** In a strict
bicategory let `γ` be a 2-cell between 1-morphisms out of `P`, and `d, s : A ⟶ P`, `i : T ⟶ A`
with `i ≫ s = i ≫ d`. If `d ◁ γ` is an `eqToHom`, so is `i ◁ (s ◁ γ)`. -/
theorem whiskerLeft_whiskerLeft_eq_eqToHom {T A P C : 𝔅} {g g' : P ⟶ C} (γ : g ⟶ g')
    {i : T ⟶ A} {s d : A ⟶ P} (hsd : i ≫ s = i ≫ d) (h₀ : d ≫ g = d ≫ g')
    (hd : d ◁ γ = eqToHom h₀) (h₁ : i ≫ s ≫ g = i ≫ s ≫ g') :
    i ◁ (s ◁ γ) = eqToHom h₁ := by
  have key : ∀ (f : T ⟶ P) (hf : f = i ≫ d) (h : f ≫ g = f ≫ g'), f ◁ γ = eqToHom h := by
    rintro f rfl h
    rw [comp_whiskerLeft, hd, whiskerLeft_eqToHom]
    simp [Strict.associator_eqToIso]
  have := key (i ≫ s) hsd (by simpa using h₁)
  rw [comp_whiskerLeft] at this
  simp only [Strict.associator_eqToIso, eqToIso.hom, eqToIso.inv] at this
  exact eq_eqToHom_of_eqToHom_comp_comp_eqToHom _ _ _ this _

/-- Whiskering an `eqToHom`-sandwich whose middle whiskers to an `eqToHom` gives an
`eqToHom`. -/
theorem whiskerLeft_eqToHom_comp_comp_eqToHom {T A C : 𝔅} {i : T ⟶ A} {g₁ g₂ g₃ g₄ : A ⟶ C}
    (a : g₁ = g₂) (b : g₂ ⟶ g₃) (c : g₃ = g₄) (hb' : i ≫ g₂ = i ≫ g₃) (hb : i ◁ b = eqToHom hb')
    (h : i ≫ g₁ = i ≫ g₄) : i ◁ (eqToHom a ≫ b ≫ eqToHom c) = eqToHom h := by
  rw [whiskerLeft_comp, whiskerLeft_comp, whiskerLeft_eqToHom, whiskerLeft_eqToHom, hb]
  simp

end CategoryTheory.Bicategory

namespace AlgebraicGeometry.Stack.EtaleSmoothLift

universe u w

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {𝒳 𝒳' : AlgebraicStacks.{u, w} B S hS} {ι : 𝒳 ⟶ 𝒳'} {hι : IsThickening ι}
  {W : AlgebraicSpaces B S hS}
  {x : (algebraicSpaceStackFunctor B S hS).obj W ⟶ 𝒳}
  {hx : AlgebraicStacks.IsSmooth B S hS x}

/-- Pulling `x'` back along a composite `c ≫ f = g` on the self-intersection. -/
private theorem map_comp_map_comp_ambientMap_eq (ξ : EtaleSmoothLift B S hS ι hι W x hx)
    {c : ξ.ambient ⟶ ξ.selfIntersection.pt} {f : ξ.selfIntersection.pt ⟶ ξ.ambient}
    {g : ξ.ambient ⟶ ξ.ambient} (hc : c ≫ f = g) :
    (algebraicSpaceStackFunctor B S hS).map c ≫ (algebraicSpaceStackFunctor B S hS).map f ≫
      ξ.ambientMap = (algebraicSpaceStackFunctor B S hS).map g ≫ ξ.ambientMap := by
  rw [← Functor.map_comp_assoc, hc]

/-- **The section `δ_σ` is the unique section with the defining property of `δ_σ`**: if `d`
satisfies `p' ∘ d = id`, `q' ∘ d = f'_σ` and `d^*γ = γ_σ`, then `d = δ_σ`. -/
theorem autLift_eq_of_isAutLift (ξ : EtaleSmoothLift B S hS ι hι W x hx) {σ : Hom ξ ξ}
    {d : ξ.ambient ⟶ ξ.selfIntersection.pt} (h : ξ.IsAutLift σ d) : ξ.autLift σ = d := by
  let F := algebraicSpaceStackFunctor.{u, w} B S hS
  have hp : ξ.autLift σ ≫ ξ.selfIntersection.fst = d ≫ ξ.selfIntersection.fst :=
    (autLift_fst ξ σ).trans h.1.symm
  have hq : ξ.autLift σ ≫ ξ.selfIntersection.snd = d ≫ ξ.selfIntersection.snd :=
    (autLift_snd ξ σ).trans h.2.1.symm
  refine hom_ext_of_isTwoFibreProduct_algebraicSpaceStackFunctor
    ξ.selfIntersection.isTwoFibreProduct.some hp hq
    (F.map_comp_map_comp_eq_of_comp_eq hp ξ.ambientMap)
    (F.map_comp_map_comp_eq_of_comp_eq hq ξ.ambientMap).symm ?_
  have e₁ := fun {c} (hc : c ≫ ξ.selfIntersection.fst = 𝟙 _) =>
    (map_comp_map_comp_ambientMap_eq ξ hc).symm
  exact eq_eqToHom_comp_comp_eqToHom_of_sandwich _ _ _ _
    ((autLift_spec ξ σ (map_id_comp_ambientMap ξ) (e₁ (autLift_fst ξ σ))
      (map_comp_map_comp_ambientMap_eq ξ (autLift_snd ξ σ))).symm.trans
      (h.2.2 (map_id_comp_ambientMap ξ) (e₁ h.1)
        (map_comp_map_comp_ambientMap_eq ξ h.2.1)))

section Setup

attribute [local irreducible] Space.modulePullback Space.smallEtaleRingedSite Space.structureSheaf
  Space.smallEtaleRingedToposHom Space.chartFunctor Space.comparisonFunctor
  Space.modulePullbackCompIso

variable (hι₁ : AlgebraicStacks.IsFirstOrderThickening B S hS ι)
  (ξ : EtaleSmoothLift B S hS ι hι W x hx)

/-- The corestriction `U ⟶ i(U)` of the inclusion of a smooth lift onto its image. -/
def toRangeHom : ξ.base.obj.left ⟶
    Space.IsThickening.space B S hS (isThickening_range_inclusion hι₁ ξ) :=
  ObjectProperty.homMk (Subfunctor.toRange ξ.inclusion.hom)

/-- The corestriction `U ⟶ i(U)` followed by the inclusion `i(U) ⟶ U'` is the inclusion `i`. -/
theorem toRangeHom_comp_inclusion :
    toRangeHom hι₁ ξ ≫ Space.IsThickening.inclusion B S hS (isThickening_range_inclusion hι₁ ξ) =
      ξ.inclusion :=
  ObjectProperty.hom_ext _ (Subfunctor.toRange_ι _)

/-- A lift of the diagonal is a section of `p' : I' ⟶ U'`. -/
theorem lifts_fst (s : Lifts hι₁ ξ) : s.1 ≫ ξ.selfIntersection.fst = 𝟙 ξ.ambient :=
  s.2.1.1.trans (Category.comp_id _)

/-- **A lift of the diagonal agrees with the diagonal on `U`**: `i ≫ δ = i ≫ Δ'`. -/
theorem inclusion_comp_lifts (s : Lifts hι₁ ξ) :
    ξ.inclusion ≫ s.1 = ξ.inclusion ≫ ξ.diagonal := by
  let hG := isThickening_range_inclusion hι₁ ξ
  have hpb := (Space.spacesBaseChange B S hS (Space.IsThickening.inclusion B S hS hG)).isPullback
    (Space.SpacesEtale.final B S hS ξ.ambient)
  have hw : ξ.inclusion ≫ (Space.SpacesEtale.final B S hS ξ.ambient).1.hom =
      toRangeHom hι₁ ξ ≫ Space.IsThickening.inclusion B S hS hG :=
    (Category.comp_id _).trans (toRangeHom_comp_inclusion hι₁ ξ).symm
  have hk := hpb.lift_fst ξ.inclusion (toRangeHom hι₁ ξ) hw
  have h : (Space.thickeningProjection B S hS hG).app (Space.SpacesEtale.final B S hS ξ.ambient) ≫
      s.1 = (Space.thickeningProjection B S hS hG).app (Space.SpacesEtale.final B S hS ξ.ambient) ≫
        ξ.diagonal := s.2.1.2.trans (autLiftLift hι₁ ξ (Hom.id ξ) rfl).2.1.2.symm
  exact (congrArg (· ≫ s.1) hk.symm).trans ((Category.assoc _ _ _).trans
    ((congrArg (hpb.lift ξ.inclusion (toRangeHom hι₁ ξ) hw ≫ ·) h).trans
      ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ ξ.diagonal) hk))))

/-- The comparison `x' = δ^*p'^*x'` for a section `δ` of `p'`. -/
theorem ambientMap_eq_map_comp_fst (s : Lifts hι₁ ξ) :
    ξ.ambientMap = (algebraicSpaceStackFunctor B S hS).map s.1 ≫
      (algebraicSpaceStackFunctor B S hS).map ξ.selfIntersection.fst ≫ ξ.ambientMap := by
  rw [← Functor.map_comp_assoc, lifts_fst]
  exact ambientMap_eq_map_id_comp ξ

/-- The comparison `δ^*q'^*x' = (q' ∘ δ)^*x'`. -/
theorem map_comp_snd_eq (s : Lifts hι₁ ξ) :
    (algebraicSpaceStackFunctor B S hS).map s.1 ≫
        (algebraicSpaceStackFunctor B S hS).map ξ.selfIntersection.snd ≫ ξ.ambientMap =
      (algebraicSpaceStackFunctor B S hS).map (s.1 ≫ ξ.selfIntersection.snd) ≫ ξ.ambientMap :=
  ((algebraicSpaceStackFunctor B S hS).map_comp_assoc _ _ _).symm

/-- The ambient component `q' ∘ δ` of the endomorphism attached to a lift `δ` restricts to the
identity on `U`. -/
theorem inclusion_comp_lifts_snd (s : Lifts hι₁ ξ) :
    ξ.inclusion ≫ (s.1 ≫ ξ.selfIntersection.snd) =
      (𝟙 ξ.base : ξ.base ⟶ ξ.base).hom.left ≫ ξ.inclusion := by
  refine (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ ξ.selfIntersection.snd)
    (inclusion_comp_lifts hι₁ ξ s)).trans ((Category.assoc _ _ _).trans ?_))
  refine (congrArg (ξ.inclusion ≫ ·) (autLift_snd ξ (Hom.id ξ))).trans ?_
  exact (Category.comp_id _).trans (Category.id_comp _).symm

/-- The 2-cell `δ^*γ : x' ⟶ (q' ∘ δ)^*x'` of the endomorphism attached to a lift `δ`. -/
def liftComm (s : Lifts hι₁ ξ) :
    ξ.ambientMap ⟶ (algebraicSpaceStackFunctor B S hS).map (s.1 ≫ ξ.selfIntersection.snd) ≫
      ξ.ambientMap :=
  eqToHom (ambientMap_eq_map_comp_fst hι₁ ξ s) ≫
    ((algebraicSpaceStackFunctor B S hS).map s.1 ◁ ξ.selfIntersection.iso.hom) ≫
      eqToHom (map_comp_snd_eq hι₁ ξ s)

/-- The 2-cell `Δ'^*γ` of the diagonal is an `eqToHom`: the diagonal is the section attached to
the identity, whose 2-cell is an identity. -/
theorem map_diagonal_whiskerLeft_iso_hom (h : (algebraicSpaceStackFunctor B S hS).map ξ.diagonal ≫
      (algebraicSpaceStackFunctor B S hS).map ξ.selfIntersection.fst ≫ ξ.ambientMap =
    (algebraicSpaceStackFunctor B S hS).map ξ.diagonal ≫
      (algebraicSpaceStackFunctor B S hS).map ξ.selfIntersection.snd ≫ ξ.ambientMap) :
    (algebraicSpaceStackFunctor B S hS).map ξ.diagonal ◁ ξ.selfIntersection.iso.hom =
      eqToHom h := by
  let F := algebraicSpaceStackFunctor.{u, w} B S hS
  have e₁ := (map_comp_map_comp_ambientMap_eq ξ (diagonal_fst ξ)).symm
  have e₂ := map_comp_map_comp_ambientMap_eq ξ (autLift_snd ξ (Hom.id ξ))
  refine eq_eqToHom_of_eqToHom_comp_comp_eqToHom e₁ e₂ (e₁.trans (h.trans e₂)) ?_ h
  exact (autLift_spec ξ (Hom.id ξ) (map_id_comp_ambientMap ξ) e₁ e₂).symm.trans
    ((congrArg (eqToHom _ ≫ ·)
      (rfl : (Hom.id ξ).comm = eqToHom (ambientMap_eq_map_id_comp ξ))).trans
        (eqToHom_trans (map_id_comp_ambientMap ξ) (ambientMap_eq_map_id_comp ξ)))

/-- The whiskering of the 2-cell of the endomorphism attached to a lift along `i : U ⟶ U'` is an
`eqToHom`: the lift agrees with the diagonal on `U`. -/
theorem map_inclusion_whiskerLeft_liftComm (s : Lifts hι₁ ξ)
    (h : (algebraicSpaceStackFunctor B S hS).map ξ.inclusion ≫ ξ.ambientMap =
      (algebraicSpaceStackFunctor B S hS).map ξ.inclusion ≫
        (algebraicSpaceStackFunctor B S hS).map (s.1 ≫ ξ.selfIntersection.snd) ≫ ξ.ambientMap) :
    (algebraicSpaceStackFunctor B S hS).map ξ.inclusion ◁ liftComm hι₁ ξ s = eqToHom h := by
  let F := algebraicSpaceStackFunctor.{u, w} B S hS
  have hsd : F.map ξ.inclusion ≫ F.map s.1 = F.map ξ.inclusion ≫ F.map ξ.diagonal :=
    (F.map_comp _ _).symm.trans ((congrArg F.map (inclusion_comp_lifts hι₁ ξ s)).trans
      (F.map_comp _ _))
  have h₀ : F.map ξ.diagonal ≫ F.map ξ.selfIntersection.fst ≫ ξ.ambientMap =
      F.map ξ.diagonal ≫ F.map ξ.selfIntersection.snd ≫ ξ.ambientMap :=
    (map_comp_map_comp_ambientMap_eq ξ (diagonal_fst ξ)).trans
      (map_comp_map_comp_ambientMap_eq ξ (autLift_snd ξ (Hom.id ξ))).symm
  have hb' : F.map ξ.inclusion ≫ F.map s.1 ≫ F.map ξ.selfIntersection.fst ≫ ξ.ambientMap =
      F.map ξ.inclusion ≫ F.map s.1 ≫ F.map ξ.selfIntersection.snd ≫ ξ.ambientMap := by
    rw [reassoc_of% hsd, h₀, reassoc_of% hsd]
  exact whiskerLeft_eqToHom_comp_comp_eqToHom _ _ _ hb'
    (whiskerLeft_whiskerLeft_eq_eqToHom ξ.selfIntersection.iso.hom hsd h₀
      (map_diagonal_whiskerLeft_iso_hom ξ h₀) hb') h

/-- The ambient component `q' ∘ δ` composed after `i` is `i`, on stacks. -/
theorem map_inclusion_comp_map_lifts_snd (s : Lifts hι₁ ξ) :
    (algebraicSpaceStackFunctor B S hS).map ξ.inclusion ≫
        (algebraicSpaceStackFunctor B S hS).map (s.1 ≫ ξ.selfIntersection.snd) =
      (algebraicSpaceStackFunctor B S hS).map ξ.inclusion :=
  ((algebraicSpaceStackFunctor B S hS).map_comp _ _).symm.trans
    (congrArg (algebraicSpaceStackFunctor B S hS).map
      ((inclusion_comp_lifts_snd hι₁ ξ s).trans (Category.id_comp _)))

/-- **The endomorphism of a smooth lift attached to a lift of the diagonal**: for a section `δ`
of `p' : I' ⟶ U'` restricting to the diagonal over `U`, the endomorphism
`(id_U, q' ∘ δ, δ^*γ)` of `ξ`. -/
def homOfLift (s : Lifts hι₁ ξ) : Hom ξ ξ where
  base := 𝟙 ξ.base
  ambient := s.1 ≫ ξ.selfIntersection.snd
  inclusion_comp := inclusion_comp_lifts_snd hι₁ ξ s
  comm := liftComm hι₁ ξ s
  coherence := by
    let F := algebraicSpaceStackFunctor.{u, w} B S hS
    have H : F.map ξ.inclusion ≫ ξ.ambientMap =
        F.map ξ.inclusion ≫ F.map (s.1 ≫ ξ.selfIntersection.snd) ≫ ξ.ambientMap :=
      (congrArg (· ≫ ξ.ambientMap) (map_inclusion_comp_map_lifts_snd hι₁ ξ s).symm).trans
        (Category.assoc _ _ _)
    have hid : F.map ξ.inclusion ◁ (Hom.id ξ).comm =
        eqToHom (congrArg (F.map ξ.inclusion ≫ ·) (ambientMap_eq_map_id_comp ξ)) :=
      whiskerLeft_eqToHom (F.map ξ.inclusion) (ambientMap_eq_map_id_comp ξ)
    exact (congrArg (ξ.comm.hom ≫ ·) (map_inclusion_whiskerLeft_liftComm hι₁ ξ s H)).trans
      (comp_eqToHom_eq_of_comp_eqToHom_eq _ _ _ _ _
        ((congrArg (ξ.comm.hom ≫ ·) hid).symm.trans (Hom.id ξ).coherence) _ _)

/-- **The section of the endomorphism attached to a lift is that lift**:
`δ_{(id, q' ∘ δ, δ^*γ)} = δ`. -/
theorem autLift_homOfLift (s : Lifts hι₁ ξ) : ξ.autLift (homOfLift hι₁ ξ s) = s.1 := by
  refine autLift_eq_of_isAutLift ξ ⟨lifts_fst hι₁ ξ s, rfl, fun e₀ e₁ e₂ => ?_⟩
  show eqToHom e₀ ≫ (eqToHom (ambientMap_eq_map_comp_fst hι₁ ξ s) ≫ _ ≫
    eqToHom (map_comp_snd_eq hι₁ ξ s)) = _
  exact eqToHom_comp_eqToHom_comp_eq _ _ _ _

/-- The lift of the diagonal attached to the endomorphism `homOfLift s` is `s`. -/
theorem autLiftLift_homOfLift (s : Lifts hι₁ ξ) :
    autLiftLift hι₁ ξ (homOfLift hι₁ ξ s) rfl = s :=
  Subtype.ext (autLift_homOfLift hι₁ ξ s)

/-- The base point of the torsor of lifts: the diagonal `Δ'`. -/
abbrev liftsBase : Lifts hι₁ ξ := autLiftLift hι₁ ξ (Hom.id ξ) rfl

/-- **The torsor of lifts of the diagonal is trivialized by the diagonal**: `θ ↦ θ · Δ'` is a
bijection from `Hom(Δ^*Ω, 𝒞_{U/U'})` onto the lifts (Stacks 061C). -/
def liftsEquiv : LiftsActingGroup hι₁ ξ ≃ Lifts hι₁ ξ :=
  letI := liftsAction hι₁ ξ
  Equiv.ofBijective (· +ᵥ liftsBase hι₁ ξ)
    (Space.conormalLiftSheafAddAction_bijective B S hS (𝟙 _) ξ.selfIntersection.fst
      (diagonalRestriction hι₁ ξ) (diagonalConormalMap hι₁ ξ)
      (isFirstOrderThickening_range_inclusion hι₁ ξ) (isFirstOrderThickening_preimage_fst hι₁ ξ)
      (Space.SpacesEtale.final B S hS ξ.ambient) (liftsBase hι₁ ξ))

/-- The bijection `liftsEquiv` sends `θ` to `θ · Δ'`. -/
theorem liftsEquiv_apply (θ : LiftsActingGroup hι₁ ξ) :
    letI := liftsAction hι₁ ξ
    liftsEquiv hι₁ ξ θ = θ +ᵥ liftsBase hι₁ ξ := rfl

/-- **The parameter of an endomorphism of a smooth lift over the identity**: the unique
`θ_σ ∈ Hom(Δ^*Ω, 𝒞_{U/U'})` with `θ_σ · Δ' = δ_σ`. This is the map
`Aut(ξ)(U) ⟶ SheafHom(Δ^*Ω, 𝒞_{U/U'})(U)` of equation 0CKH of the source, read inversely. -/
def autParam (σ : Hom ξ ξ) (hσ : σ.base = 𝟙 ξ.base) : LiftsActingGroup hι₁ ξ :=
  (liftsEquiv hι₁ ξ).symm (autLiftLift hι₁ ξ σ hσ)

/-- The parameter `θ_σ` satisfies `θ_σ · Δ' = δ_σ`. -/
theorem autParam_vadd (σ : Hom ξ ξ) (hσ : σ.base = 𝟙 ξ.base) :
    letI := liftsAction hι₁ ξ
    autParam hι₁ ξ σ hσ +ᵥ liftsBase hι₁ ξ = autLiftLift hι₁ ξ σ hσ :=
  (liftsEquiv hι₁ ξ).apply_symm_apply _

/-- **Composition is addition** (item (3) of the source's proof of 0CKH):
`θ_{σ ≫ τ} = θ_σ + θ_τ`. -/
theorem autParam_comp (σ τ : Hom ξ ξ) (hσ : σ.base = 𝟙 ξ.base) (hτ : τ.base = 𝟙 ξ.base) :
    autParam hι₁ ξ (σ.comp τ) (by change σ.base ≫ τ.base = _; rw [hσ, hτ, Category.comp_id]) =
      autParam hι₁ ξ σ hσ + autParam hι₁ ξ τ hτ := by
  let := liftsAction hι₁ ξ
  let M := {m : Hom ξ ξ // m.base = 𝟙 ξ.base}
  let xx : M → Lifts hι₁ ξ := fun m => autLiftLift hι₁ ξ m.1 m.2
  let mul : M → M → M := fun m n => ⟨m.1.comp n.1, by
    show m.1.base ≫ n.1.base = _
    rw [m.2, n.2, Category.comp_id]⟩
  exact AddAction.add_of_translation (liftsBase hι₁ ξ)
    (fun θ₁ θ₂ h => (liftsEquiv hι₁ ξ).injective h) xx (fun m => autParam hι₁ ξ m.1 m.2)
    (fun m => autParam_vadd hι₁ ξ m.1 m.2) (liftsTranslationDatum hι₁ ξ) mul
    (fun m n => Subtype.ext ((autLift_comp ξ m.1 n.1).trans
      ((congrArg (· ≫ ξ.rightTranslation n.1)
        (congrArg Subtype.val (autParam_vadd hι₁ ξ m.1 m.2)).symm).trans
        (vadd_diagonal_comp_rightTranslation hι₁ ξ n.1 n.2 _))))
    ⟨Hom.id ξ, rfl⟩ rfl
    (fun m => Subtype.ext (congrArg ξ.autLift
      (Category.comp_id (obj := EtaleSmoothLift B S hS ι hι W x hx) (X := ξ) (Y := ξ) m.1)))
    ⟨σ, hσ⟩ ⟨τ, hτ⟩

/-- An endomorphism over the identity is determined by its parameter. -/
theorem autParam_injective {σ τ : Hom ξ ξ} (hσ : σ.base = 𝟙 ξ.base) (hτ : τ.base = 𝟙 ξ.base)
    (h : autParam hι₁ ξ σ hσ = autParam hι₁ ξ τ hτ) : σ = τ :=
  ξ.autLift_injective (congrArg Subtype.val ((liftsEquiv hι₁ ξ).symm.injective h))
    (hσ.trans hτ.symm)

/-- **Every homomorphism `Δ^*Ω ⟶ 𝒞_{U/U'}` is the parameter of an endomorphism over the
identity**, namely of `homOfLift` applied to `θ · Δ'`. -/
theorem autParam_homOfLift (θ : LiftsActingGroup hι₁ ξ) :
    autParam hι₁ ξ (homOfLift hι₁ ξ (liftsEquiv hι₁ ξ θ)) rfl = θ := by
  unfold autParam
  rw [autLiftLift_homOfLift, Equiv.symm_apply_apply]

/-- The parameter of the identity endomorphism is zero. -/
theorem autParam_id : autParam hι₁ ξ (Hom.id ξ) rfl = 0 := by
  let := liftsAction hι₁ ξ
  exact (liftsEquiv hι₁ ξ).injective ((autParam_vadd hι₁ ξ _ _).trans
    (zero_vadd (LiftsActingGroup hι₁ ξ) (liftsBase hι₁ ξ)).symm)

end Setup

end AlgebraicGeometry.Stack.EtaleSmoothLift
