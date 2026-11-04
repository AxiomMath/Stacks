module

public import StacksFrontier.AlgebraicGeometry.Stacks.LiftingAffinesAutomorphismParam
public import StacksFrontier.AlgebraicGeometry.Stacks.LiftingAffinesEtaleAmbient
public import StacksFrontier.AlgebraicGeometry.Spaces.DeformationLiftActionNaturality
public import StacksFrontier.AlgebraicGeometry.Spaces.SchemeAsSpace

/-!
# Étale compatibility of the identification of `Aut(ξ)` (Stacks 0CKG (2))

Let `m = (f, f', γ_m) : η ⟶ ξ` be a morphism of smooth lifts of étale opens of `W`
(`AlgebraicGeometry.Stack.EtaleSmoothLift`, Stacks 0CJP), and `I'_η = V' ×_{y'} V'`,
`I'_ξ = U' ×_{x'} U'` their self-intersections. The proof of Stacks 0CKG checks that the
identification `Aut(ξ) ≅ SheafHom(Δ^*Ω_{I/U}, 𝒞_{U/U'})` of equation 0CKH commutes with étale
localization (item (1) of the source), through the footnote of the source and Stacks 0CK8. This
file supplies the geometric input: the morphism `Φ_m : I'_η ⟶ I'_ξ`
(`AlgebraicGeometry.Stack.EtaleSmoothLift.selfIntersectionMap`) over `f' × f'`, and the equation
`Φ_m ∘ δ_τ = δ_σ ∘ f'` whenever `τ ≫ m = m ≫ σ`
(`AlgebraicGeometry.Stack.EtaleSmoothLift.autLift_comp_selfIntersectionMap`): the section of the
restriction of `σ` along `m`, pushed into `I'_ξ`, is the restriction of the section of `σ`.

The 2-cell identity behind it is proved once, in an arbitrary strict bicategory
(`CategoryTheory.Bicategory.whiskerLeft_eq_of_selfIntersectionMap`), with every composite
1-morphism a variable carrying its defining equation, as in
`StacksFrontier.AlgebraicGeometry.Stacks.LiftingAffinesAutomorphismLift`.

## References

* [Stacks Project, Tag 0CKG](https://stacks.math.columbia.edu/tag/0CKG)
* [Stacks Project, Tag 0CK8](https://stacks.math.columbia.edu/tag/0CK8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Bicategory Opposite

namespace CategoryTheory

/-- An `eqToHom` on the left of one side moves to a sandwich on the other. -/
theorem eq_eqToHom_comp_comp_eqToHom_of_eqToHom_comp {𝒞 : Type*} [Category 𝒞] {P P' Q Q' R : 𝒞}
    {Z : R ⟶ Q} {Y : P' ⟶ Q'} (a : P = R) (b₁ : P = P') (b₂ : Q' = Q)
    (h : eqToHom a ≫ Z = eqToHom b₁ ≫ Y ≫ eqToHom b₂) :
    Y = eqToHom (b₁.symm.trans a) ≫ Z ≫ eqToHom b₂.symm := by
  subst a b₁ b₂
  simpa using h.symm

/-- Cancelling an isomorphism against its inverse inside `eqToHom`-sandwiches. -/
theorem eqToHom_comp_inv_comp_eq {𝒞 : Type*} [Category 𝒞] {X X' Y Z Z' W : 𝒞} (c : Y ⟶ X)
    [IsIso c] {Y₁ : 𝒞} (P₁ : Y ⟶ Y₁) (P₂ : Y₁ ⟶ Z) (R : X ⟶ Z') (E : Z = Z')
    (hc : P₁ ≫ P₂ ≫ eqToHom E = c ≫ R) (a : X' = X) (e : Z = W) (a' : X' = X) (e' : Z' = W) :
    eqToHom a ≫ inv c ≫ P₁ ≫ P₂ ≫ eqToHom e = eqToHom a' ≫ R ≫ eqToHom e' := by
  subst a E e
  simp only [eqToHom_refl, Category.comp_id, Category.id_comp] at hc ⊢
  rw [hc, IsIso.inv_hom_id_assoc]

/-- Heterogeneously equal morphisms with a common source agree after an `eqToHom`. -/
theorem comp_eqToHom_eq_of_heq {𝒞 : Type*} [Category 𝒞] {X Y Y' : 𝒞} {a : X ⟶ Y} {b : X ⟶ Y'}
    (h : HEq a b) (e : Y = Y') : a ≫ eqToHom e = b := by
  subst e
  simpa using eq_of_heq h

end CategoryTheory

namespace CategoryTheory.Bicategory

universe w₀ v₀ u₀

variable {𝔅 : Type u₀} [Bicategory.{w₀, v₀} 𝔅] [Bicategory.Strict 𝔅]

/-- Whiskering twice along a composite equal to a given 1-morphism, read along `eqToHom`s. -/
theorem whiskerLeft_whiskerLeft_eq_eqToHom_comp {T A P C : 𝔅} {g g' : A ⟶ C} (η : g ⟶ g')
    {d : T ⟶ P} {p : P ⟶ A} {k : T ⟶ A} (h : d ≫ p = k) (e₁ : d ≫ p ≫ g = k ≫ g)
    (e₂ : k ≫ g' = d ≫ p ≫ g') :
    d ◁ (p ◁ η) = eqToHom e₁ ≫ (k ◁ η) ≫ eqToHom e₂ := by
  subst h
  rw [comp_whiskerLeft]
  simp [Strict.associator_eqToIso]

/-- **The lift of a restricted endomorphism, mapped to the larger self-intersection, is the
restriction of the lift.** In a strict bicategory, let `γη : pη ∘ y ⟶ qη ∘ y` and
`γξ : pξ ∘ x ⟶ qξ ∘ x` be 2-cells over `P ⇉ A` and `Q ⇉ B`, let `c : y ⟶ f ∘ x` be invertible,
and let `Φ : P ⟶ Q` lie over `f` on both sides with `Φ^*γξ = (qη^*c) ∘ γη ∘ (pη^*c⁻¹)`. Let
`δτ`, `δσ` be sections of `pη`, `pξ` with `δτ^*γη = cτ`, `δσ^*γξ = cσ`, and suppose
`cτ` followed by `t^*c` equals `c` followed by `f^*cσ`. Then
`(Φ ∘ δτ)^*γξ = (δσ ∘ f)^*γξ` along the equalities. Every composite 1-morphism is a variable
carrying its defining equation. -/
theorem whiskerLeft_eq_of_selfIntersectionMap {A B P Q C : 𝔅} {y : A ⟶ C} {x : B ⟶ C}
    {pη qη : P ⟶ A} {pξ qξ : Q ⟶ B} (γη : pη ≫ y ⟶ qη ≫ y) (γξ : pξ ≫ x ⟶ qξ ≫ x)
    {f : A ⟶ B} (c : y ⟶ f ≫ x) [IsIso c] {Φ : P ⟶ Q} {pf qf : P ⟶ B}
    (hpf : pf = pη ≫ f) (hqf : qf = qη ≫ f) (hΦp : Φ ≫ pξ = pf) (hΦq : Φ ≫ qξ = qf)
    (hΦ : ∀ (e₀ : pf ≫ x = pη ≫ f ≫ x) (e₃ : qη ≫ f ≫ x = qf ≫ x) (e₁ : pf ≫ x = Φ ≫ pξ ≫ x)
      (e₂ : Φ ≫ qξ ≫ x = qf ≫ x),
      eqToHom e₀ ≫ ((pη ◁ inv c) ≫ γη ≫ (qη ◁ c)) ≫ eqToHom e₃ =
        eqToHom e₁ ≫ (Φ ◁ γξ) ≫ eqToHom e₂)
    {oneA : A ⟶ A} {oneB : B ⟶ B} (honeA : oneA = 𝟙 A) (honeB : oneB = 𝟙 B)
    {δτ : A ⟶ P} {t : A ⟶ A} (hτp : δτ ≫ pη = oneA) (hτq : δτ ≫ qη = t) (cτ : y ⟶ t ≫ y)
    (hτ : ∀ (e₀ : oneA ≫ y = y) (e₁ : oneA ≫ y = δτ ≫ pη ≫ y) (e₂ : δτ ≫ qη ≫ y = t ≫ y),
      eqToHom e₀ ≫ cτ = eqToHom e₁ ≫ (δτ ◁ γη) ≫ eqToHom e₂)
    {δσ : B ⟶ Q} {s : B ⟶ B} (hσp : δσ ≫ pξ = oneB) (hσq : δσ ≫ qξ = s) (cσ : x ⟶ s ≫ x)
    (hσ : ∀ (e₀ : oneB ≫ x = x) (e₁ : oneB ≫ x = δσ ≫ pξ ≫ x) (e₂ : δσ ≫ qξ ≫ x = s ≫ x),
      eqToHom e₀ ≫ cσ = eqToHom e₁ ≫ (δσ ◁ γξ) ≫ eqToHom e₂)
    (hts : t ≫ f = f ≫ s)
    (hcomm : ∀ e : t ≫ f ≫ x = f ≫ s ≫ x, cτ ≫ (t ◁ c) ≫ eqToHom e = c ≫ (f ◁ cσ))
    {dΦ fd : A ⟶ Q} (hdΦ : dΦ = δτ ≫ Φ) (hfd : fd = f ≫ δσ)
    (e₁ : dΦ ≫ pξ ≫ x = fd ≫ pξ ≫ x) (e₂ : fd ≫ qξ ≫ x = dΦ ≫ qξ ≫ x) :
    dΦ ◁ γξ = eqToHom e₁ ≫ (fd ◁ γξ) ≫ eqToHom e₂ := by
  subst hpf hqf honeA honeB hdΦ hfd
  have hΦγ := eq_eqToHom_comp_comp_eqToHom_of_sandwich _ _ _ _
    (hΦ (by simp only [Strict.assoc]) (by simp only [Strict.assoc])
      (by rw [← Strict.assoc Φ pξ, hΦp]) (by rw [← Strict.assoc Φ qξ, hΦq])).symm
  have hτγ := eq_eqToHom_comp_comp_eqToHom_of_eqToHom_comp _ _ _
    (hτ (Strict.id_comp y) (by rw [← Strict.assoc, hτp]) (by rw [← Strict.assoc, hτq]))
  have hσγ := eq_eqToHom_comp_comp_eqToHom_of_eqToHom_comp _ _ _
    (hσ (Strict.id_comp x) (by rw [← Strict.assoc, hσp]) (by rw [← Strict.assoc, hσq]))
  have h1 := whiskerLeft_whiskerLeft_eq_eqToHom_comp (inv c) hτp
    (by rw [← Strict.assoc, hτp]) (by rw [← Strict.assoc, hτp])
  have h3 := whiskerLeft_whiskerLeft_eq_eqToHom_comp c hτq
    (by rw [← Strict.assoc δτ qη, hτq]) (by rw [← Strict.assoc δτ qη, hτq])
  rw [comp_whiskerLeft, hΦγ, comp_whiskerLeft, hσγ]
  simp only [whiskerLeft_comp, Strict.associator_eqToIso, eqToIso.hom, eqToIso.inv,
    whiskerLeft_eqToHom, Category.assoc, eqToHom_trans, eqToHom_trans_assoc, h1, h3, hτγ,
    id_whiskerLeft, Strict.leftUnitor_eqToIso, eqToHom_refl, Category.id_comp]
  exact eqToHom_comp_inv_comp_eq c cτ (t ◁ c) (f ◁ cσ) _
    (hcomm (by rw [← Strict.assoc t f x, hts, Strict.assoc])) _ _ _ _

end CategoryTheory.Bicategory

namespace AlgebraicGeometry.Space

universe u

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **The canonical map of conormal modules along an étale morphism is an isomorphism**, for any
closed subspace equal to the inverse image (Stacks 04CQ). -/
theorem isIso_conormalMap_of_eq_preimageSubspace {X X' : AlgebraicSpaces B S hS} (φ : X ⟶ X')
    (hφ : IsEtale B S hS φ.hom) (Z' : ClosedSubspaces B S hS X'.1) {Z : ClosedSubspaces B S hS X.1}
    (hZ : Z = preimageSubspace B S hS φ Z')
    (p : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) ⟶ ⟨Z'.1.toFunctor, Z'.2.1⟩)
    (hsq : subspaceInclusion B S hS X Z ≫ φ = p ≫ subspaceInclusion B S hS X' Z') :
    IsIso (conormalMap B S hS Z Z' φ p hsq) := by
  subst hZ
  have hp : p = preimageProjection B S hS φ Z' :=
    ObjectProperty.hom_ext _ ((cancel_mono Z'.1.ι).1 (congrArg (fun g => g.hom)
      (hsq.symm.trans (conormalEtaleRestrictionSquare B S hS φ Z'))))
  subst hp
  exact isIso_conormalMap_of_isEtale B S hS φ hφ Z'

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.Stack.EtaleSmoothLift

universe u w

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {𝒳 𝒳' : AlgebraicStacks.{u, w} B S hS} {ι : 𝒳 ⟶ 𝒳'} {hι : IsThickening ι}
  {W : AlgebraicSpaces B S hS}
  {x : (algebraicSpaceStackFunctor B S hS).obj W ⟶ 𝒳}
  {hx : AlgebraicStacks.IsSmooth B S hS x}

section Map

variable {η ξ : EtaleSmoothLift B S hS ι hι W x hx} (m : Hom η ξ)

/-- The comparison `(p' ≫ f')^*x' = p'^*f'^*x'`. -/
theorem map_comp_ambientMap_assoc {T : AlgebraicSpaces B S hS} (p : T ⟶ η.ambient) :
    (algebraicSpaceStackFunctor B S hS).map (p ≫ m.ambient) ≫ ξ.ambientMap =
      (algebraicSpaceStackFunctor B S hS).map p ≫
        (algebraicSpaceStackFunctor B S hS).map m.ambient ≫ ξ.ambientMap :=
  (congrArg (· ≫ ξ.ambientMap) ((algebraicSpaceStackFunctor B S hS).map_comp _ _)).trans
    (Category.assoc _ _ _)

/-- The 2-isomorphism `x'_ξ ∘ f' ∘ p'_η ≅ x'_ξ ∘ f' ∘ q'_η` transported from the universal
2-isomorphism of `I'_η` along `γ_m : y' ≅ f'^*x'`. -/
def selfIntersectionMapIso :
    (algebraicSpaceStackFunctor B S hS).map (η.selfIntersection.fst ≫ m.ambient) ≫ ξ.ambientMap ≅
      (algebraicSpaceStackFunctor B S hS).map (η.selfIntersection.snd ≫ m.ambient) ≫
        ξ.ambientMap :=
  eqToIso (map_comp_ambientMap_assoc m _) ≪≫
    whiskerLeftIso ((algebraicSpaceStackFunctor B S hS).map η.selfIntersection.fst)
      (asIso m.comm).symm ≪≫ η.selfIntersection.iso ≪≫
    whiskerLeftIso ((algebraicSpaceStackFunctor B S hS).map η.selfIntersection.snd)
      (asIso m.comm) ≪≫ eqToIso (map_comp_ambientMap_assoc m _).symm

/-- The morphism underlying `selfIntersectionMapIso m`, written out as a composite. -/
theorem selfIntersectionMapIso_hom :
    (selfIntersectionMapIso m).hom = eqToHom (map_comp_ambientMap_assoc m _) ≫
      (((algebraicSpaceStackFunctor B S hS).map η.selfIntersection.fst ◁ inv m.comm) ≫
        η.selfIntersection.iso.hom ≫
          ((algebraicSpaceStackFunctor B S hS).map η.selfIntersection.snd ◁ m.comm)) ≫
      eqToHom (map_comp_ambientMap_assoc m _).symm := by
  simp [selfIntersectionMapIso]

/-- **The morphism `Φ_m : I'_η ⟶ I'_ξ` of self-intersections induced by a morphism of smooth
lifts** `m = (f, f', γ_m) : η ⟶ ξ`: on points `(a, b, ε) ↦ (f' a, f' b, γ_m ∘ ε ∘ γ_m⁻¹)`. -/
theorem exists_selfIntersectionMap :
    ∃ h : η.selfIntersection.pt ⟶ ξ.selfIntersection.pt,
      h ≫ ξ.selfIntersection.fst = η.selfIntersection.fst ≫ m.ambient ∧
      h ≫ ξ.selfIntersection.snd = η.selfIntersection.snd ≫ m.ambient ∧
      ∀ (e₁ : (algebraicSpaceStackFunctor B S hS).map (η.selfIntersection.fst ≫ m.ambient) ≫
            ξ.ambientMap = (algebraicSpaceStackFunctor B S hS).map h ≫
              (algebraicSpaceStackFunctor B S hS).map ξ.selfIntersection.fst ≫ ξ.ambientMap)
        (e₂ : (algebraicSpaceStackFunctor B S hS).map h ≫
            (algebraicSpaceStackFunctor B S hS).map ξ.selfIntersection.snd ≫ ξ.ambientMap =
          (algebraicSpaceStackFunctor B S hS).map (η.selfIntersection.snd ≫ m.ambient) ≫
            ξ.ambientMap),
        (selfIntersectionMapIso m).hom = eqToHom e₁ ≫
          ((algebraicSpaceStackFunctor B S hS).map h ◁ ξ.selfIntersection.iso.hom) ≫ eqToHom e₂ :=
  exists_lift_of_isTwoFibreProduct_algebraicSpaceStackFunctor
    ξ.selfIntersection.isTwoFibreProduct.some _ _ (selfIntersectionMapIso m)

/-- The morphism `Φ_m : I'_η ⟶ I'_ξ` of self-intersections induced by `m`, chosen by
`exists_selfIntersectionMap`. -/
def selfIntersectionMap : η.selfIntersection.pt ⟶ ξ.selfIntersection.pt :=
  (exists_selfIntersectionMap m).choose

/-- `Φ_m` lies over `f'` along the first projections: `p'_ξ ∘ Φ_m = f' ∘ p'_η`. -/
theorem selfIntersectionMap_fst :
    selfIntersectionMap m ≫ ξ.selfIntersection.fst = η.selfIntersection.fst ≫ m.ambient :=
  (exists_selfIntersectionMap m).choose_spec.1

/-- `Φ_m` lies over `f'` along the second projections: `q'_ξ ∘ Φ_m = f' ∘ q'_η`. -/
theorem selfIntersectionMap_snd :
    selfIntersectionMap m ≫ ξ.selfIntersection.snd = η.selfIntersection.snd ≫ m.ambient :=
  (exists_selfIntersectionMap m).choose_spec.2.1

/-- `Φ_m` carries the universal 2-isomorphism of `I'_η`, transported along `γ_m`, to the
universal 2-isomorphism of `I'_ξ`. -/
theorem selfIntersectionMap_spec
    (e₁ : (algebraicSpaceStackFunctor B S hS).map (η.selfIntersection.fst ≫ m.ambient) ≫
      ξ.ambientMap = (algebraicSpaceStackFunctor B S hS).map (selfIntersectionMap m) ≫
        (algebraicSpaceStackFunctor B S hS).map ξ.selfIntersection.fst ≫ ξ.ambientMap)
    (e₂ : (algebraicSpaceStackFunctor B S hS).map (selfIntersectionMap m) ≫
        (algebraicSpaceStackFunctor B S hS).map ξ.selfIntersection.snd ≫ ξ.ambientMap =
      (algebraicSpaceStackFunctor B S hS).map (η.selfIntersection.snd ≫ m.ambient) ≫
        ξ.ambientMap) :
    (selfIntersectionMapIso m).hom = eqToHom e₁ ≫
      ((algebraicSpaceStackFunctor B S hS).map (selfIntersectionMap m) ◁
        ξ.selfIntersection.iso.hom) ≫ eqToHom e₂ :=
  (exists_selfIntersectionMap m).choose_spec.2.2 e₁ e₂

/-- **The section of a restricted endomorphism, mapped by `Φ_m`, is the restriction of the
section**: if `τ ≫ m = m ≫ σ` then `Φ_m ∘ δ_τ = δ_σ ∘ f'`. -/
theorem autLift_comp_selfIntersectionMap (τ : Hom η η) (σ : Hom ξ ξ)
    (h : τ.comp m = m.comp σ) :
    η.autLift τ ≫ selfIntersectionMap m = m.ambient ≫ ξ.autLift σ := by
  let F := algebraicSpaceStackFunctor.{u, w} B S hS
  have hF {T T' T'' : AlgebraicSpaces B S hS} {a : T ⟶ T'} {b : T' ⟶ T''} {c : T ⟶ T''}
      (h : a ≫ b = c) : F.map a ≫ F.map b = F.map c := by rw [← F.map_comp, h]
  have hamb : τ.ambient ≫ m.ambient = m.ambient ≫ σ.ambient := congrArg Hom.ambient h
  have hp : (η.autLift τ ≫ selfIntersectionMap m) ≫ ξ.selfIntersection.fst =
      (m.ambient ≫ ξ.autLift σ) ≫ ξ.selfIntersection.fst := by
    rw [Category.assoc, selfIntersectionMap_fst, ← Category.assoc, autLift_fst, Category.assoc,
      autLift_fst, Category.id_comp, Category.comp_id]
  have hq : (η.autLift τ ≫ selfIntersectionMap m) ≫ ξ.selfIntersection.snd =
      (m.ambient ≫ ξ.autLift σ) ≫ ξ.selfIntersection.snd := by
    rw [Category.assoc, selfIntersectionMap_snd, ← Category.assoc, autLift_snd, Category.assoc,
      autLift_snd, hamb]
  refine hom_ext_of_isTwoFibreProduct_algebraicSpaceStackFunctor
    ξ.selfIntersection.isTwoFibreProduct.some hp hq
    (F.map_comp_map_comp_eq_of_comp_eq hp ξ.ambientMap)
    (F.map_comp_map_comp_eq_of_comp_eq hq ξ.ambientMap).symm ?_
  have hc : HEq (τ.comm ≫ (F.map τ.ambient ◁ m.comm)) (m.comm ≫ (F.map m.ambient ◁ σ.comm)) :=
    congr_arg_heq Hom.comm h
  exact whiskerLeft_eq_of_selfIntersectionMap η.selfIntersection.iso.hom ξ.selfIntersection.iso.hom
    m.comm (F.map_comp _ _) (F.map_comp _ _)
    (hF (selfIntersectionMap_fst m)) (hF (selfIntersectionMap_snd m))
    (fun e₀ e₃ e₁ e₂ =>
      (selfIntersectionMapIso_hom m).symm.trans (selfIntersectionMap_spec m e₁ e₂))
    (F.map_id _) (F.map_id _)
    (hF (autLift_fst η τ)) (hF (autLift_snd η τ)) τ.comm (autLift_spec η τ)
    (hF (autLift_fst ξ σ)) (hF (autLift_snd ξ σ)) σ.comm (autLift_spec ξ σ)
    ((F.map_comp _ _).symm.trans ((congrArg F.map hamb).trans (F.map_comp _ _)))
    (fun e => (Category.assoc _ _ _).symm.trans (comp_eqToHom_eq_of_heq hc e)) (F.map_comp _ _)
    (F.map_comp _ _) _ _

end Map

section Subspaces

variable (hι₁ : AlgebraicStacks.IsFirstOrderThickening B S hS ι)
  {η ξ : EtaleSmoothLift B S hS ι hι W x hx} (m : Hom η ξ)

/-- A point of `V'` in the image of `j : V ⟶ V'` maps into the image of `i : U ⟶ U'`. -/
theorem ambient_mem_range {V : (BigFppfOver B S hS)ᵒᵖ} {z : η.ambient.obj.obj V}
    (hz : z ∈ (Subfunctor.range η.inclusion.hom).obj V) :
    m.ambient.hom.app V z ∈ (Subfunctor.range ξ.inclusion.hom).obj V := by
  obtain ⟨v, rfl⟩ := hz
  refine ⟨m.base.hom.left.hom.app V v, ?_⟩
  have h := congrArg (fun g => g.hom.app V v) m.inclusion_comp
  exact h.symm

/-- The restriction `range(j) ⟶ range(i)` of `f'`, on the closed subspaces read on the final
objects. -/
def liftsZMap : (⟨(liftsZ hι₁ η).1.toFunctor, (liftsZ hι₁ η).2.1⟩ : AlgebraicSpaces B S hS) ⟶
    ⟨(baseSubspace hι₁ ξ).1.toFunctor, (baseSubspace hι₁ ξ).2.1⟩ :=
  ObjectProperty.homMk (Subfunctor.lift ((liftsZ hι₁ η).1.ι ≫ m.ambient.hom)
    (by
      rintro V _ ⟨z, rfl⟩
      exact ambient_mem_range m z.2))

/-- The square formed by `liftsZMap hι₁ m`, `f'` and the two subspace inclusions commutes. -/
theorem liftsZMap_square :
    Space.subspaceInclusion B S hS η.ambient (liftsZ hι₁ η) ≫ m.ambient =
      liftsZMap hι₁ m ≫ Space.subspaceInclusion B S hS ξ.ambient (baseSubspace hι₁ ξ) :=
  ObjectProperty.hom_ext _ rfl

/-- **The cartesian property of a morphism of smooth lifts, on points**: a point of `V'` whose
image under `f'` lies in the image of `i : U ⟶ U'` lies in the image of `j : V ⟶ V'`, because
`V = 𝒳 ×_{𝒳'} V'`. -/
theorem mem_range_of_ambient_mem_range {V : BigFppfOver B S hS} {z : η.ambient.obj.obj (op V)}
    (hz : m.ambient.hom.app (op V) z ∈ (Subfunctor.range ξ.inclusion.hom).obj (op V)) :
    z ∈ (Subfunctor.range η.inclusion.hom).obj (op V) := by
  obtain ⟨u, hu⟩ := hz
  let F := algebraicSpaceStackFunctor.{u, w} B S hS
  let tz : schemeSpace V ⟶ η.ambient := ObjectProperty.homMk (yonedaEquiv.symm z)
  let tu : schemeSpace V ⟶ ξ.base.obj.left := ObjectProperty.homMk (yonedaEquiv.symm u)
  have hsq : tu ≫ ξ.inclusion = tz ≫ m.ambient := ObjectProperty.hom_ext _
    ((yonedaEquiv_symm_naturality_right _ _ _).trans ((congrArg yonedaEquiv.symm hu).trans
      (yonedaEquiv_symm_naturality_right _ _ _).symm))
  have e : F.map tu ≫ F.map ξ.inclusion ≫ ξ.ambientMap =
      F.map tz ≫ F.map m.ambient ≫ ξ.ambientMap :=
    (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ ξ.ambientMap)
      ((F.map_comp _ _).symm.trans ((congrArg F.map hsq).trans (F.map_comp _ _)))).trans
        (Category.assoc _ _ _))
  obtain ⟨v, hv⟩ := exists_comp_eq_of_isTwoFibreProduct_snd η.isTwoFibreProduct
    (F.map tu ≫ F.map ξ.base.obj.hom ≫ x) tz
    (eqToIso (Category.assoc _ _ _) ≪≫ whiskerLeftIso (F.map tu) ξ.comm ≪≫ eqToIso e ≪≫
      whiskerLeftIso (F.map tz) (asIso m.comm).symm)
  refine ⟨yonedaEquiv v.hom, ?_⟩
  have h := congrArg (fun g => yonedaEquiv g.hom) hv
  exact (yonedaEquiv_comp v.hom η.inclusion.hom).symm.trans
    (h.trans (Equiv.apply_symm_apply _ _))

/-- **`V = U ×_{U'} V'` as closed subspaces**: the closed subspace `j(V) ⊂ V'` read on the final
object is the inverse image of `i(U) ⊂ U'` along `f'`. -/
theorem liftsZ_eq_preimageSubspace :
    liftsZ hι₁ η = Space.preimageSubspace B S hS m.ambient (baseSubspace hι₁ ξ) := by
  refine Subtype.ext (Subfunctor.ext (funext fun V => Set.ext fun z => ?_))
  induction V using Opposite.rec with | op V => ?_
  exact ⟨fun h => ambient_mem_range m h, fun h => mem_range_of_ambient_mem_range m h⟩

/-- The restriction of `f'` to the closed subspaces read on the final objects of `V'` and
`U'`. -/
def liftsZRestriction :
    (⟨(liftsZ hι₁ η).1.toFunctor, (liftsZ hι₁ η).2.1⟩ : AlgebraicSpaces B S hS) ⟶
      ⟨(liftsZ hι₁ ξ).1.toFunctor, (liftsZ hι₁ ξ).2.1⟩ :=
  ObjectProperty.homMk (Subfunctor.lift ((liftsZ hι₁ η).1.ι ≫ m.ambient.hom)
    (by
      rintro V _ ⟨z, rfl⟩
      exact ambient_mem_range m z.2))

/-- The square formed by `liftsZRestriction hι₁ m`, `f'` and the two subspace inclusions
commutes. -/
theorem liftsZRestriction_square :
    Space.subspaceInclusion B S hS η.ambient (liftsZ hι₁ η) ≫ m.ambient =
      liftsZRestriction hι₁ m ≫ Space.subspaceInclusion B S hS ξ.ambient (liftsZ hι₁ ξ) :=
  ObjectProperty.hom_ext _ rfl

/-- `liftsZRestriction hι₁ m` followed by the projection `liftsProjection` is `liftsZMap hι₁ m`. -/
theorem liftsZRestriction_comp :
    liftsZRestriction hι₁ m ≫ Space.preimageProjection B S hS
        ((Space.SpacesEtale.inclusion B S hS ξ.ambient).obj
          (Space.SpacesEtale.final B S hS ξ.ambient)).hom (baseSubspace hι₁ ξ) =
      liftsZMap hι₁ m :=
  ObjectProperty.hom_ext _ rfl

/-- The restriction `f₀ : I_η ⟶ I_ξ` of `Φ_m` to the thickenings of the self-intersections. -/
def selfIntersectionMapRestriction :
    (⟨(liftsW₀ hι₁ η).1.toFunctor, (liftsW₀ hι₁ η).2.1⟩ : AlgebraicSpaces B S hS) ⟶
      ⟨(liftsW₀ hι₁ ξ).1.toFunctor, (liftsW₀ hι₁ ξ).2.1⟩ :=
  ObjectProperty.homMk (Subfunctor.lift ((liftsW₀ hι₁ η).1.ι ≫ (selfIntersectionMap m).hom)
    (by
      rintro V _ ⟨w, rfl⟩
      have h : ξ.selfIntersection.fst.hom.app V ((selfIntersectionMap m).hom.app V w.1) =
          m.ambient.hom.app V (η.selfIntersection.fst.hom.app V w.1) :=
        congrArg (fun g => g.hom.app V w.1) (selfIntersectionMap_fst m)
      change ξ.selfIntersection.fst.hom.app V ((selfIntersectionMap m).hom.app V w.1) ∈
        (Subfunctor.range ξ.inclusion.hom).obj V
      rw [h]
      exact ambient_mem_range m w.2))

/-- The square formed by `selfIntersectionMapRestriction hι₁ m`, `Φ_m` and the two subspace
inclusions commutes. -/
theorem selfIntersectionMapRestriction_square :
    Space.subspaceInclusion B S hS η.selfIntersection.pt (liftsW₀ hι₁ η) ≫ selfIntersectionMap m =
      selfIntersectionMapRestriction hι₁ m ≫
        Space.subspaceInclusion B S hS ξ.selfIntersection.pt (liftsW₀ hι₁ ξ) :=
  ObjectProperty.hom_ext _ rfl

/-- `Φ_m` lies over `f'` on the thickenings. -/
theorem selfIntersectionMapRestriction_comm :
    @CategoryStruct.comp (AlgebraicSpaces B S hS) _ _ _ _ (selfIntersectionMapRestriction hι₁ m)
        (Space.subspaceInclusion B S hS ξ.selfIntersection.pt (liftsW₀ hι₁ ξ) ≫
          ξ.selfIntersection.fst) =
      @CategoryStruct.comp (AlgebraicSpaces B S hS) _ _ _ _
        (Space.subspaceInclusion B S hS η.selfIntersection.pt (liftsW₀ hι₁ η) ≫
          η.selfIntersection.fst) m.ambient :=
  (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ ξ.selfIntersection.fst)
    (selfIntersectionMapRestriction_square hι₁ m).symm).trans ((Category.assoc _ _ _).trans
      ((congrArg (_ ≫ ·) (selfIntersectionMap_fst m)).trans (Category.assoc _ _ _).symm)))

/-- The diagonal of `η` pushed into `I'_ξ` is the diagonal of `ξ` restricted along `f'`. -/
theorem diagonal_comp_selfIntersectionMap :
    η.diagonal ≫ selfIntersectionMap m = m.ambient ≫ ξ.diagonal :=
  autLift_comp_selfIntersectionMap m (Hom.id η) (Hom.id ξ)
    ((Category.id_comp (obj := EtaleSmoothLift B S hS ι hι W x hx) m).trans
      (Category.comp_id (obj := EtaleSmoothLift B S hS ι hι W x hx) m).symm)

/-- **The two edges `V ⟶ I_ξ` agree**: `f₀ ∘ Δ_η = Δ_ξ ∘ f`. -/
theorem liftsEdge_comp_selfIntersectionMapRestriction :
    liftsEdge hι₁ η ≫ selfIntersectionMapRestriction hι₁ m =
      liftsZMap hι₁ m ≫ diagonalRestriction hι₁ ξ := by
  refine ObjectProperty.hom_ext _ ?_
  ext V z
  exact Subtype.ext (congrArg (fun g => g.hom.app V z.1) (diagonal_comp_selfIntersectionMap m))

end Subspaces


section Compatibility

attribute [local irreducible] Space.modulePullback Space.smallEtaleRingedSite Space.structureSheaf
  Space.smallEtaleRingedToposHom Space.chartFunctor Space.comparisonFunctor
  Space.modulePullbackCompIso

variable (hι₁ : AlgebraicStacks.IsFirstOrderThickening B S hS ι)

/-- The sheaf of differentials `Ω_{I_ξ/U'}` acted through. -/
abbrev liftsDifferentials (ξ : EtaleSmoothLift B S hS ι hι W x hx) :=
  Space.sheafOfDifferentials B S hS
    (Space.subspaceInclusion B S hS ξ.selfIntersection.pt (liftsW₀ hι₁ ξ) ≫ ξ.selfIntersection.fst)

/-- The projection `U ⟶ i(U)` read on the final object of `U'`. -/
abbrev liftsProjection (ξ : EtaleSmoothLift B S hS ι hι W x hx) :=
  Space.preimageProjection B S hS ((Space.SpacesEtale.inclusion B S hS ξ.ambient).obj
    (Space.SpacesEtale.final B S hS ξ.ambient)).hom (baseSubspace hι₁ ξ)

/-- The isomorphism `𝒞_{U/U'}|_U ≅ 𝒞_{U/U'}` on the final object (04CQ). -/
def conormalRestrictionFinal (ξ : EtaleSmoothLift B S hS ι hι W x hx) :=
  @asIso _ _ _ _ (Space.conormalMap B S hS (liftsZ hι₁ ξ) (baseSubspace hι₁ ξ)
    ((Space.SpacesEtale.inclusion B S hS ξ.ambient).obj
      (Space.SpacesEtale.final B S hS ξ.ambient)).hom
    (liftsProjection hι₁ ξ) (Space.conormalEtaleRestrictionSquare B S hS _ _))
    (Space.isIso_conormalMap_of_isEtale B S hS _
      (Space.SpacesEtale.final B S hS ξ.ambient).property _)

variable {η ξ : EtaleSmoothLift B S hS ι hι W x hx} (m : Hom η ξ)

/-- The isomorphism `f^*𝒞_{U/U'} ≅ 𝒞_{V/V'}` of Stacks 04CQ along the étale `f'`. -/
def conormalRestrictionAlong :=
  @asIso _ _ _ _ (Space.conormalMap B S hS (liftsZ hι₁ η) (baseSubspace hι₁ ξ) m.ambient
    (liftsZMap hι₁ m) (liftsZMap_square hι₁ m))
    (Space.isIso_conormalMap_of_eq_preimageSubspace m.ambient (Hom.isEtale_ambient η ξ m) _
      (liftsZ_eq_preimageSubspace hι₁ m) _ _)

/-- **The restriction of a parameter along a morphism of smooth lifts**: a homomorphism
`θ : Δ^*Ω_{I_ξ/U'} ⟶ 𝒞_{U/U'}` read on `V` through Stacks 03LU and 04CQ, the map `θ₂` of the
restriction law of the action. -/
def restrictParam (θ : LiftsActingGroup hι₁ ξ) :
    (Space.modulePullback B S hS
        (@CategoryStruct.comp (AlgebraicSpaces B S hS) _ _ _ _ (liftsZMap hι₁ m)
          (diagonalRestriction hι₁ ξ))).obj (liftsDifferentials hι₁ ξ) ⟶
      Space.conormalModule B S hS η.ambient (liftsZ hι₁ η) :=
  Iso.homCongr ((Space.modulePullbackCompIso B S hS (liftsZMap hι₁ m)
      (diagonalRestriction hι₁ ξ)).app (liftsDifferentials hι₁ ξ)) (conormalRestrictionAlong hι₁ m)
    (Space.QuasiCoherentDescent.restrictForm B S hS (liftsZRestriction hι₁ m)
      (liftsProjection hι₁ ξ) (liftsZMap hι₁ m) (liftsZRestriction_comp hι₁ m)
      ((Iso.homCongr ((Space.modulePullbackCompIso B S hS (liftsProjection hι₁ ξ)
        (diagonalRestriction hι₁ ξ)).app (liftsDifferentials hι₁ ξ))
          (conormalRestrictionFinal hι₁ ξ)).symm θ))

/-- **The 0CK6 datum of a parameter of `η` along `Φ_m`**, `θ ↦ θ''`. -/
def postcompParam (θ : LiftsActingGroup hι₁ η) :=
  Space.postcompDerivationDatum B S hS
    (Space.subspaceInclusion B S hS η.selfIntersection.pt (liftsW₀ hι₁ η) ≫ η.selfIntersection.fst)
    (Space.subspaceInclusion B S hS ξ.selfIntersection.pt (liftsW₀ hι₁ ξ) ≫ ξ.selfIntersection.fst)
    (selfIntersectionMapRestriction hι₁ m) m.ambient (selfIntersectionMapRestriction_comm hι₁ m)
    (liftsEdge hι₁ η) (Space.conormalModule B S hS _ (liftsZ hι₁ η)) θ

/-- **Étale compatibility of the identification `Aut(ξ) ≅ SheafHom(Δ^*Ω, 𝒞)`, the postcomposition
half.** Let `τ ≫ m = m ≫ σ` for endomorphisms over the identity. Then the parameter `θ_τ` of `τ`,
pushed along `Φ_m : I'_η ⟶ I'_ξ` by the datum `θ ↦ θ''` of Stacks 0CK6, moves the diagonal of `η`
pushed into `I'_ξ` to the section `δ_σ ∘ f'`: `θ_τ'' · (Φ_m ∘ Δ'_η) = δ_σ ∘ f'`. -/
theorem derivationMove_postcompParam_autParam (τ : Hom η η) (σ : Hom ξ ξ) (hτ : τ.base = 𝟙 η.base)
    (_hσ : σ.base = 𝟙 ξ.base) (h : τ.comp m = m.comp σ) :
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
        (postcompParam hι₁ m (autParam hι₁ η τ hτ))
        ((((Space.SpacesEtale.inclusion B S hS η.ambient).obj
          (Space.SpacesEtale.final B S hS η.ambient)).hom ≫ 𝟙 η.ambient) ≫ m.ambient)
        (Space.comp_comp_eq_comp_of_comp_eq B S hS (selfIntersectionMap m) η.selfIntersection.fst
          ξ.selfIntersection.fst m.ambient (selfIntersectionMap_fst m) η.diagonal _
          (liftsBase hι₁ η).2.1.1) =
      m.ambient ≫ ξ.autLift σ := by
  have hη := (congrArg Subtype.val (autParam_vadd hι₁ η τ hτ)).symm.trans
    (coe_lifts_vadd hι₁ η (autParam hι₁ η τ hτ) (liftsBase hι₁ η))
  have hZη : Space.IsFirstOrderThickening B S hS ((Space.SpacesEtale.toSpaces B S hS η.ambient).obj
      (Space.SpacesEtale.final B S hS η.ambient)) (liftsZ hι₁ η).1 :=
    Space.isFirstOrderThickening_preimage B S hS _ _ (isFirstOrderThickening_range_inclusion hι₁ η)
  have hcomp := Space.derivationMove_comp B S hS (liftsZ hι₁ η) (liftsW₀ hι₁ η) (liftsW₀ hι₁ ξ)
    (liftsEdge hι₁ η) (selfIntersectionMapRestriction hι₁ m) (selfIntersectionMap m)
    (selfIntersectionMapRestriction_square hι₁ m) η.selfIntersection.fst ξ.selfIntersection.fst
    m.ambient (selfIntersectionMapRestriction_comm hι₁ m) (selfIntersectionMap_fst m) hZη
    (isFirstOrderThickening_preimage_fst hι₁ η) (isFirstOrderThickening_preimage_fst hι₁ ξ)
    η.diagonal (liftsBase hι₁ η).2.2.square (autParam hι₁ η τ hτ) _ (liftsBase hι₁ η).2.1.1
  exact hcomp.symm.trans ((congrArg (· ≫ selfIntersectionMap m) hη).symm.trans
    (autLift_comp_selfIntersectionMap m τ σ h))

end Compatibility

end AlgebraicGeometry.Stack.EtaleSmoothLift
