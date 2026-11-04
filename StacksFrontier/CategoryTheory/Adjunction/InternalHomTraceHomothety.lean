module

public import Mathlib.CategoryTheory.Monoidal.Rigid.Braided
public import StacksFrontier.CategoryTheory.Adjunction.InternalHomTraceNaturality
public import StacksFrontier.CategoryTheory.Monoidal.ExactPairingOfTensorHomDiagonal
public import StacksFrontier.CategoryTheory.Monoidal.InternalHomUnitHomothety
public import StacksFrontier.CategoryTheory.Monoidal.InternalHomUnitLeftUnitor

/-!
# The homothety of a dualizing object, for abstract tensor–Hom data

Let `C`, `D` be monoidal categories, `C` braided, with internal Homs `- ⊗ P ⊣ H(P, -)` whose
hom-set bijections are dinatural in `P`, and let `F ⊣ G` with `G : C ⥤ D` (a direct image
`Rf_*`) and a comparison of tensor products along `F`. Let `ω` be an object of `C` with a
morphism `ε : G ω ⟶ 𝟙` (the counit `Rf_*a(𝒪_Y) ⟶ 𝒪_Y`). For an object `E` of `C` with dual
`E^∨ = H(E, 𝟙)` this file builds the chain of maps of the proof of [Stacks, Tag 0E5V] (3)

`Hom(E, 𝟙) ≃ Hom(𝟙, E^∨) ⟶ Hom(F 𝟙, E^∨) ≃ Hom(𝟙, G E^∨) ⟶ Hom(H(G E^∨, 𝟙), 𝟙)`
`⟶ Hom(G H(E^∨, ω), 𝟙) ⟶ Hom(G(E ⊗ ω), 𝟙)`

(tensor–Hom adjunction, `F 𝟙 ⟶ 𝟙`, `F ⊣ G`, biduality, the trace map of [Stacks, Tag 0E57], and
`E ⊗ ω ⟶ H(E^∨, ω)`), proves that it is natural in `E`, and that it is bijective when
`E` and `G E^∨` are dualizable (tensor–Hom diagonals invertible), the trace map at `E^∨` is
invertible and `F 𝟙 ⟶ 𝟙` is invertible. By the Yoneda lemma, if moreover `v ↦ G v ≫ ε` is
bijective on `Hom(E ⊗ ω, ω)` and `Hom(𝟙 ⊗ ω, ω)`, postcomposition with the homothety
`𝟙 ⟶ H(ω, ω)` is a bijection `Hom(E, 𝟙) ⟶ Hom(E, H(ω, ω))`.

## Main definitions

* `CategoryTheory.InternalHomTrace.tensorDualHomMap`: the map `E ⊗ K ⟶ H(H(E, 𝟙), K)`.
* `CategoryTheory.InternalHomTrace.unitHomDualMap`: the map `Hom(𝟙, Q) ⟶ Hom(H(Q, 𝟙), 𝟙)`.
* `CategoryTheory.InternalHomTrace.dualityChainMap`: the chain of maps above.

## Main results

* `CategoryTheory.InternalHomTrace.isIso_tensorDualHomMap`,
  `CategoryTheory.InternalHomTrace.bijective_unitHomDualMap`,
  `CategoryTheory.InternalHomTrace.dualityChainMap_naturality`,
  `CategoryTheory.InternalHomTrace.bijective_dualityChainMap`.
* `CategoryTheory.InternalHomTrace.bijective_comp_homothety`,
  `CategoryTheory.InternalHomTrace.bijective_comp_homEquiv_leftUnitor`,
  `CategoryTheory.InternalHomTrace.bijective_comp_of_isIso_homEquiv_symm`: postcomposition with
  a homothety of `ω` is bijective on morphisms out of `E`.

## References

* [Stacks Project, Tag 0E57](https://stacks.math.columbia.edu/tag/0E57)
* [Stacks Project, Tag 0E5V](https://stacks.math.columbia.edu/tag/0E5V)
* [Stacks Project, Tag 08JJ](https://stacks.math.columbia.edu/tag/08JJ)
-/

@[expose] public noncomputable section

namespace CategoryTheory.InternalHomTrace

open MonoidalCategory Opposite PullbackInternalHom

section Comp

variable {C : Type*} [Category C]

/-- Precomposition with an isomorphism is a bijection on hom-sets. -/
theorem bijective_comp_left_of_isIso {X Y Z : C} (f : X ⟶ Y) [IsIso f] :
    Function.Bijective fun g : Y ⟶ Z => f ≫ g :=
  ⟨fun x y h => by simpa using congrArg (fun t => inv f ≫ t) h, fun y => ⟨inv f ≫ y, by simp⟩⟩

/-- Postcomposition with an isomorphism is a bijection on hom-sets. -/
theorem bijective_comp_right_of_isIso {X Y Z : C} (f : Y ⟶ Z) [IsIso f] :
    Function.Bijective fun g : X ⟶ Y => g ≫ f :=
  ⟨fun x y h => by simpa using congrArg (fun t => t ≫ inv f) h, fun y => ⟨y ≫ inv f, by simp⟩⟩

end Comp

section Dual

variable {C : Type*} [Category C] [MonoidalCategory C] (HC : Cᵒᵖ ⥤ C ⥤ C)
  (adjC : ∀ P : C, (curriedTensor C).flip.obj P ⊣ HC.obj (op P))

/-- **The map `E ⊗ K ⟶ H(E^∨, K)`**, for `E^∨ = H(E, 𝟙)`: the braiding `E ⊗ K ≅ K ⊗ E` followed by
the adjoint of `(K ⊗ E) ⊗ E^∨ ≅ K ⊗ (E ⊗ E^∨) ⟶ K ⊗ 𝟙 ≅ K`, whose middle step is the braiding
followed by the evaluation `E^∨ ⊗ E ⟶ 𝟙`. -/
def tensorDualHomMap [BraidedCategory C] (E K : C) :
    E ⊗ K ⟶ (HC.obj (op ((HC.obj (op E)).obj (𝟙_ C)))).obj K :=
  (β_ E K).hom ≫ (adjC ((HC.obj (op E)).obj (𝟙_ C))).homEquiv _ _
    ((α_ K E ((HC.obj (op E)).obj (𝟙_ C))).hom ≫
      K ◁ ((β_ E ((HC.obj (op E)).obj (𝟙_ C))).hom ≫ (adjC E).counit.app (𝟙_ C)) ≫ (ρ_ K).hom)

/-- **`E ⊗ K ⟶ H(E^∨, K)` is invertible when `E` is dualizable**, i.e. when the tensor–Hom
diagonal `E ⊗ E^∨ ⟶ H(E, E ⊗ 𝟙)` is invertible: then `(E^∨, E)` is an exact pairing (the swap of
`CategoryTheory.PullbackInternalHom.exactPairingOfIsIsoLeftTensorHomDiagonal`), and the map is the
braiding followed by the invertible map `K ⊗ E ⟶ H(E^∨, K)` of that pairing. -/
theorem isIso_tensorDualHomMap [BraidedCategory C] (E K : C)
    (hE : IsIso (leftTensorHomDiagonal (curriedTensor C) HC adjC (fun A B D => α_ A B D) E E
      (𝟙_ C))) :
    IsIso (tensorDualHomMap HC adjC E K) := by
  let := exactPairingOfIsIsoLeftTensorHomDiagonal HC adjC E
  let := BraidedCategory.exactPairing_swap E ((HC.obj (op E)).obj (𝟙_ C))
  exact IsIso.comp_isIso' inferInstance
    (isIso_exactPairingTensorHomMap (H := HC) (adj := adjC) ((HC.obj (op E)).obj (𝟙_ C)) E K)

/-- **`E ⊗ K ⟶ H(E^∨, K)` is natural in `E`**, if the hom-set bijections of the internal Homs are
dinatural. -/
theorem tensorDualHomMap_naturality [BraidedCategory C]
    (hdinC : ∀ {P' P : C} (u : P' ⟶ P) {A M : C} (θ : A ⟶ (HC.obj (op P)).obj M),
      ((adjC P').homEquiv A M).symm (θ ≫ (HC.map u.op).app M) =
        ((curriedTensor C).obj A).map u ≫ ((adjC P).homEquiv A M).symm θ)
    {E E' : C} (f : E ⟶ E') (K : C) :
    f ▷ K ≫ tensorDualHomMap HC adjC E' K =
      tensorDualHomMap HC adjC E K ≫ (HC.map ((HC.map f.op).app (𝟙_ C)).op).app K := by
  have hev := counit_dinaturality (curriedTensor C) HC adjC hdinC f (𝟙_ C)
  simp only [curriedTensor_map_app, curriedTensor_obj_map] at hev
  have key : f ▷ (HC.obj (op E')).obj (𝟙_ C) ≫ (β_ E' _).hom ≫ (adjC E').counit.app (𝟙_ C) =
      E ◁ (HC.map f.op).app (𝟙_ C) ≫ (β_ E _).hom ≫ (adjC E).counit.app (𝟙_ C) := by
    rw [BraidedCategory.braiding_naturality_left_assoc,
      BraidedCategory.braiding_naturality_right_assoc, hev]
  dsimp only [tensorDualHomMap]
  rw [BraidedCategory.braiding_naturality_left_assoc, Category.assoc]
  congr 1
  apply ((adjC _).homEquiv _ _).symm.injective
  rw [Adjunction.homEquiv_naturality_left_symm, hdinC, Equiv.symm_apply_apply,
    Equiv.symm_apply_apply]
  simp only [Functor.flip_obj_map, curriedTensor_map_app, curriedTensor_obj_map]
  rw [associator_naturality_middle_assoc, associator_naturality_right_assoc,
    ← MonoidalCategory.whiskerLeft_comp_assoc, ← MonoidalCategory.whiskerLeft_comp_assoc,
    ← Category.assoc, key, Category.assoc]

/-- **The biduality map `Hom(𝟙, Q) ⟶ Hom(Q^∨, 𝟙)`**, `χ ↦ ρ⁻¹ ≫ (Q^∨ ◁ χ) ≫ ev`, for
`Q^∨ = H(Q, 𝟙)` and the evaluation `ev : Q^∨ ⊗ Q ⟶ 𝟙`. -/
def unitHomDualMap (Q : C) (χ : 𝟙_ C ⟶ Q) : (HC.obj (op Q)).obj (𝟙_ C) ⟶ 𝟙_ C :=
  (ρ_ ((HC.obj (op Q)).obj (𝟙_ C))).inv ≫ (HC.obj (op Q)).obj (𝟙_ C) ◁ χ ≫
    (adjC Q).counit.app (𝟙_ C)

/-- The biduality map is dinatural in `Q`. -/
theorem unitHomDualMap_comp
    (hdinC : ∀ {P' P : C} (u : P' ⟶ P) {A M : C} (θ : A ⟶ (HC.obj (op P)).obj M),
      ((adjC P').homEquiv A M).symm (θ ≫ (HC.map u.op).app M) =
        ((curriedTensor C).obj A).map u ≫ ((adjC P).homEquiv A M).symm θ)
    {Q Q' : C} (χ : 𝟙_ C ⟶ Q) (g : Q ⟶ Q') :
    unitHomDualMap HC adjC Q' (χ ≫ g) =
      (HC.map g.op).app (𝟙_ C) ≫ unitHomDualMap HC adjC Q χ := by
  have hev := counit_dinaturality (curriedTensor C) HC adjC hdinC g (𝟙_ C)
  simp only [curriedTensor_map_app, curriedTensor_obj_map] at hev
  dsimp only [unitHomDualMap]
  rw [MonoidalCategory.whiskerLeft_comp_assoc, ← hev, whisker_exchange_assoc,
    ← rightUnitor_inv_naturality_assoc]

/-- **The biduality map is bijective when `Q` is dualizable**: by the exact pairing `(Q, Q^∨)` it
is the hom-set bijection `Hom(𝟙, Q ⊗ 𝟙) ≃ Hom(Q^∨ ⊗ 𝟙, 𝟙)` of the pairing, up to unitors. -/
theorem bijective_unitHomDualMap (Q : C)
    (hQ : IsIso (leftTensorHomDiagonal (curriedTensor C) HC adjC (fun A B D => α_ A B D) Q Q
      (𝟙_ C))) :
    Function.Bijective (unitHomDualMap HC adjC Q) := by
  let := exactPairingOfIsIsoLeftTensorHomDiagonal HC adjC Q
  have e : unitHomDualMap HC adjC Q =
      (fun g => (ρ_ _).inv ≫ g) ∘
        (tensorLeftHomEquiv (𝟙_ C) Q ((HC.obj (op Q)).obj (𝟙_ C)) (𝟙_ C)).symm ∘
          (fun χ => χ ≫ (ρ_ Q).inv) := by
    funext χ
    simp only [Function.comp_apply, tensorLeftHomEquiv, Equiv.coe_fn_symm_mk,
      unitHomDualMap, MonoidalCategory.whiskerLeft_comp, Category.assoc]
    congr 2
    rw [whiskerLeft_rightUnitor_inv, Category.assoc, Iso.hom_inv_id_assoc,
      ← rightUnitor_inv_naturality_assoc, ← unitors_inv_equal, Iso.inv_hom_id, Category.comp_id]
    rfl
  rw [e]
  exact ((bijective_comp_left_of_isIso _).comp (Equiv.bijective _)).comp
    (bijective_comp_right_of_isIso _)

end Dual

section Chain

variable {C D : Type*} [Category C] [Category D] [MonoidalCategory C] [BraidedCategory C]
  [MonoidalCategory D]
  {F : D ⥤ C} {G : C ⥤ D} (adj : F ⊣ G)
  (α : Functor.uncurry.obj (curriedTensor D) ⋙ F ⟶ F.prod F ⋙ Functor.uncurry.obj (curriedTensor C))
  (HC : Cᵒᵖ ⥤ C ⥤ C) (HD : Dᵒᵖ ⥤ D ⥤ D)
  (adjC : ∀ P : C, (curriedTensor C).flip.obj P ⊣ HC.obj (op P))
  (adjD : ∀ P : D, (curriedTensor D).flip.obj P ⊣ HD.obj (op P))
  (ι : F.obj (𝟙_ D) ⟶ 𝟙_ C) {ω : C} (ε : G.obj ω ⟶ 𝟙_ D)

/-- **The chain of maps of Stacks 0E5V (3)**, `Hom(E, 𝟙) ⟶ Hom(G(E ⊗ ω), 𝟙)`: `φ` goes to
`G(E ⊗ ω ⟶ H(E^∨, ω))`, then the trace map `G H(E^∨, ω) ⟶ H(G E^∨, 𝟙)`, then the biduality map
of the adjoint `𝟙 ⟶ G E^∨` of `F 𝟙 ⟶ 𝟙 ⟶ E^∨`, where `𝟙 ⟶ E^∨` is the transpose of
`λ_E ≫ φ`. -/
def dualityChainMap (E : C) (φ : E ⟶ 𝟙_ C) : G.obj (E ⊗ ω) ⟶ 𝟙_ D :=
  G.map (tensorDualHomMap HC adjC E ω) ≫
    pushforwardTrace adj (curriedTensor C) (curriedTensor D) α HC HD adjC adjD
      ((HC.obj (op E)).obj (𝟙_ C)) ε ≫
    unitHomDualMap HD adjD _
      (adj.homEquiv _ _ (ι ≫ (adjC E).homEquiv _ _ ((λ_ E).hom ≫ φ)))

/-- **The chain of maps of Stacks 0E5V (3) is natural in `E`.** -/
theorem dualityChainMap_naturality
    (hdinC : ∀ {P' P : C} (u : P' ⟶ P) {A M : C} (θ : A ⟶ (HC.obj (op P)).obj M),
      ((adjC P').homEquiv A M).symm (θ ≫ (HC.map u.op).app M) =
        ((curriedTensor C).obj A).map u ≫ ((adjC P).homEquiv A M).symm θ)
    (hdinD : ∀ {P' P : D} (u : P' ⟶ P) {A M : D} (θ : A ⟶ (HD.obj (op P)).obj M),
      ((adjD P').homEquiv A M).symm (θ ≫ (HD.map u.op).app M) =
        ((curriedTensor D).obj A).map u ≫ ((adjD P).homEquiv A M).symm θ)
    {E E' : C} (f : E ⟶ E') (ψ : E' ⟶ 𝟙_ C) :
    dualityChainMap adj α HC HD adjC adjD ι ε E (f ≫ ψ) =
      G.map (f ▷ ω) ≫ dualityChainMap adj α HC HD adjC adjD ι ε E' ψ := by
  have hA : (adjC E).homEquiv (𝟙_ C) (𝟙_ C) ((λ_ E).hom ≫ f ≫ ψ) =
      (adjC E').homEquiv (𝟙_ C) (𝟙_ C) ((λ_ E').hom ≫ ψ) ≫ (HC.map f.op).app (𝟙_ C) := by
    apply ((adjC E).homEquiv _ _).symm.injective
    rw [hdinC, Equiv.symm_apply_apply, Equiv.symm_apply_apply, curriedTensor_obj_map,
      leftUnitor_naturality_assoc]
  have hκ := tensorDualHomMap_naturality HC adjC hdinC f ω
  have hTr := pushforwardTrace_naturality_source adj (curriedTensor C) (curriedTensor D) α HC HD
    adjC adjD hdinC hdinD ((HC.map f.op).app (𝟙_ C)) ε
  dsimp only [dualityChainMap]
  rw [hA, ← Category.assoc ι, Adjunction.homEquiv_naturality_right,
    unitHomDualMap_comp HD adjD hdinD, ← reassoc_of% hTr, ← G.map_comp_assoc, ← hκ,
    G.map_comp_assoc]

/-- **The chain of maps of Stacks 0E5V (3) is bijective** when `E` and `G E^∨` are dualizable,
the trace map at `E^∨` is invertible and `F 𝟙 ⟶ 𝟙` is invertible. -/
theorem bijective_dualityChainMap (hι : IsIso ι) (E : C)
    (hE : IsIso (leftTensorHomDiagonal (curriedTensor C) HC adjC (fun A B D => α_ A B D) E E
      (𝟙_ C)))
    (hTr : IsIso (pushforwardTrace adj (curriedTensor C) (curriedTensor D) α HC HD adjC adjD
      ((HC.obj (op E)).obj (𝟙_ C)) ε))
    (hQ : IsIso (leftTensorHomDiagonal (curriedTensor D) HD adjD (fun A B D => α_ A B D)
      (G.obj ((HC.obj (op E)).obj (𝟙_ C))) (G.obj ((HC.obj (op E)).obj (𝟙_ C))) (𝟙_ D))) :
    Function.Bijective (dualityChainMap adj α HC HD adjC adjD ι ε E) := by
  have := isIso_tensorDualHomMap HC adjC E ω hE
  let pre := G.map (tensorDualHomMap HC adjC E ω) ≫
    pushforwardTrace adj (curriedTensor C) (curriedTensor D) α HC HD adjC adjD
      ((HC.obj (op E)).obj (𝟙_ C)) ε
  have e : dualityChainMap adj α HC HD adjC adjD ι ε E =
      (fun g => pre ≫ g) ∘ unitHomDualMap HD adjD _ ∘ adj.homEquiv _ _ ∘ (fun t => ι ≫ t) ∘
        (adjC E).homEquiv _ _ ∘ (fun φ : E ⟶ 𝟙_ C => (λ_ E).hom ≫ φ) := by
    funext φ
    simp only [Function.comp_apply, dualityChainMap, pre, Category.assoc]
  rw [e]
  exact (bijective_comp_left_of_isIso pre).comp <| (bijective_unitHomDualMap HD adjD _ hQ).comp <|
    (Equiv.bijective _).comp <| (bijective_comp_left_of_isIso ι).comp <|
      (Equiv.bijective _).comp (bijective_comp_left_of_isIso (λ_ E).hom)

/-- **Postcomposition with the homothety of `ω` is bijective on morphisms out of `E`** (the
chain of bijections of Stacks 0E5V (3)). Let `a : 𝟙 ⟶ H(ω, ω)` satisfy `a ▷ ω ≫ ev = λ_ω`.
Suppose the chain of maps of `CategoryTheory.InternalHomTrace.dualityChainMap` is bijective at
`E` and at `𝟙` and that `v ↦ G v ≫ ε` is bijective on `Hom(E ⊗ ω, ω)` and on `Hom(𝟙 ⊗ ω, ω)`.
Then `φ ↦ φ ≫ a` is a bijection `Hom(E, 𝟙) ⟶ Hom(E, H(ω, ω))`. -/
theorem bijective_comp_homothety
    (hdinC : ∀ {P' P : C} (u : P' ⟶ P) {A M : C} (θ : A ⟶ (HC.obj (op P)).obj M),
      ((adjC P').homEquiv A M).symm (θ ≫ (HC.map u.op).app M) =
        ((curriedTensor C).obj A).map u ≫ ((adjC P).homEquiv A M).symm θ)
    (hdinD : ∀ {P' P : D} (u : P' ⟶ P) {A M : D} (θ : A ⟶ (HD.obj (op P)).obj M),
      ((adjD P').homEquiv A M).symm (θ ≫ (HD.map u.op).app M) =
        ((curriedTensor D).obj A).map u ≫ ((adjD P).homEquiv A M).symm θ)
    {a : 𝟙_ C ⟶ (HC.obj (op ω)).obj ω} (ha : a ▷ ω ≫ (adjC ω).counit.app ω = (λ_ ω).hom)
    (E : C)
    (hN : Function.Bijective (dualityChainMap adj α HC HD adjC adjD ι ε E))
    (hN₁ : Function.Bijective (dualityChainMap adj α HC HD adjC adjD ι ε (𝟙_ C)))
    (hεE : Function.Bijective fun v : E ⊗ ω ⟶ ω => G.map v ≫ ε)
    (hε₁ : Function.Bijective fun v : 𝟙_ C ⊗ ω ⟶ ω => G.map v ≫ ε) :
    Function.Bijective fun φ : E ⟶ 𝟙_ C => φ ≫ a := by
  obtain ⟨x, hx⟩ := hε₁.2 (dualityChainMap adj α HC HD adjC adjD ι ε (𝟙_ C) (𝟙 _))
  dsimp only at hx
  let b : 𝟙_ C ⟶ (HC.obj (op ω)).obj ω := (adjC ω).homEquiv _ _ x
  have hc : ∀ Z : C, Function.Bijective fun y : Z ⟶ (HC.obj (op ω)).obj ω =>
      y ▷ ω ≫ (adjC ω).counit.app ω := fun Z => by
    have e : (fun y : Z ⟶ (HC.obj (op ω)).obj ω => y ▷ ω ≫ (adjC ω).counit.app ω) =
        ((adjC ω).homEquiv Z ω).symm := by
      funext y
      rw [Adjunction.homEquiv_counit]
      rfl
    rw [e]
    exact Equiv.bijective _
  have hb : ∀ Z : C, (Function.Bijective fun φ : Z ⟶ 𝟙_ C => G.map (φ ▷ ω) ≫
      dualityChainMap adj α HC HD adjC adjD ι ε (𝟙_ C) (𝟙 _)) →
      Function.Bijective (fun v : Z ⊗ ω ⟶ ω => G.map v ≫ ε) →
      Function.Bijective fun φ : Z ⟶ 𝟙_ C => φ ≫ b := fun Z hZ hεZ => by
    have e₁ : (fun φ : Z ⟶ 𝟙_ C => G.map (φ ▷ ω) ≫
        dualityChainMap adj α HC HD adjC adjD ι ε (𝟙_ C) (𝟙 _)) =
        (fun v : Z ⊗ ω ⟶ ω => G.map v ≫ ε) ∘ ((adjC ω).homEquiv Z ω).symm ∘
          (fun φ : Z ⟶ 𝟙_ C => φ ≫ b) := by
      funext φ
      simp only [Function.comp_apply, b, Adjunction.homEquiv_naturality_left_symm,
        Equiv.symm_apply_apply, ← hx, Functor.flip_obj_map, curriedTensor_map_app,
        G.map_comp_assoc]
    rw [e₁] at hZ
    exact (Function.Bijective.of_comp_iff' (hεZ.comp (Equiv.bijective _)) _).1
      (by simpa only [Function.comp_assoc] using hZ)
  have hN' : ∀ Z : C, dualityChainMap adj α HC HD adjC adjD ι ε Z =
      fun φ => G.map (φ ▷ ω) ≫ dualityChainMap adj α HC HD adjC adjD ι ε (𝟙_ C) (𝟙 _) :=
    fun Z => funext fun φ => by
      rw [← dualityChainMap_naturality adj α HC HD adjC adjD ι ε hdinC hdinD φ (𝟙 _),
        Category.comp_id]
  exact (bijective_comp_iff_of_whiskerRight_comp_eq_leftUnitor _ hc ha
    (hb (𝟙_ C) (hN' (𝟙_ C) ▸ hN₁) hε₁) E).2
    (hb E (hN' E ▸ hN) hεE)

/-- **Postcomposition with the transpose of `λ_ω` is bijective on morphisms out of `E`**: the
case of `CategoryTheory.InternalHomTrace.bijective_comp_homothety` for the homothety
`𝟙 ⟶ H(ω, ω)` adjoint to the left unitor. -/
theorem bijective_comp_homEquiv_leftUnitor
    (hdinC : ∀ {P' P : C} (u : P' ⟶ P) {A M : C} (θ : A ⟶ (HC.obj (op P)).obj M),
      ((adjC P').homEquiv A M).symm (θ ≫ (HC.map u.op).app M) =
        ((curriedTensor C).obj A).map u ≫ ((adjC P).homEquiv A M).symm θ)
    (hdinD : ∀ {P' P : D} (u : P' ⟶ P) {A M : D} (θ : A ⟶ (HD.obj (op P)).obj M),
      ((adjD P').homEquiv A M).symm (θ ≫ (HD.map u.op).app M) =
        ((curriedTensor D).obj A).map u ≫ ((adjD P).homEquiv A M).symm θ)
    (E : C)
    (hN : Function.Bijective (dualityChainMap adj α HC HD adjC adjD ι ε E))
    (hN₁ : Function.Bijective (dualityChainMap adj α HC HD adjC adjD ι ε (𝟙_ C)))
    (hεE : Function.Bijective fun v : E ⊗ ω ⟶ ω => G.map v ≫ ε)
    (hε₁ : Function.Bijective fun v : 𝟙_ C ⊗ ω ⟶ ω => G.map v ≫ ε) :
    Function.Bijective fun φ : E ⟶ 𝟙_ C => φ ≫ (adjC ω).homEquiv _ _ (λ_ ω).hom :=
  bijective_comp_homothety adj α HC HD adjC adjD ι ε hdinC hdinD
    (((adjC ω).homEquiv_counit (g := (adjC ω).homEquiv _ _ (λ_ ω).hom)).symm.trans
      (Equiv.symm_apply_apply _ _)) E hN hN₁ hεE hε₁

/-- **Postcomposition with a section of `H(ω, ω)` with invertible transpose is bijective on
morphisms out of `E`**: such a section is the transpose of `λ_ω` followed by an automorphism of
`H(ω, ω)`, so this follows from
`CategoryTheory.InternalHomTrace.bijective_comp_homEquiv_leftUnitor`. -/
theorem bijective_comp_of_isIso_homEquiv_symm
    (hdinC : ∀ {P' P : C} (u : P' ⟶ P) {A M : C} (θ : A ⟶ (HC.obj (op P)).obj M),
      ((adjC P').homEquiv A M).symm (θ ≫ (HC.map u.op).app M) =
        ((curriedTensor C).obj A).map u ≫ ((adjC P).homEquiv A M).symm θ)
    (hdinD : ∀ {P' P : D} (u : P' ⟶ P) {A M : D} (θ : A ⟶ (HD.obj (op P)).obj M),
      ((adjD P').homEquiv A M).symm (θ ≫ (HD.map u.op).app M) =
        ((curriedTensor D).obj A).map u ≫ ((adjD P).homEquiv A M).symm θ)
    {a : 𝟙_ C ⟶ (HC.obj (op ω)).obj ω} (ha : IsIso (((adjC ω).homEquiv _ _).symm a)) (E : C)
    (hN : Function.Bijective (dualityChainMap adj α HC HD adjC adjD ι ε E))
    (hN₁ : Function.Bijective (dualityChainMap adj α HC HD adjC adjD ι ε (𝟙_ C)))
    (hεE : Function.Bijective fun v : E ⊗ ω ⟶ ω => G.map v ≫ ε)
    (hε₁ : Function.Bijective fun v : 𝟙_ C ⊗ ω ⟶ ω => G.map v ≫ ε) :
    Function.Bijective fun φ : E ⟶ 𝟙_ C => φ ≫ a := by
  have hb := bijective_comp_homEquiv_leftUnitor adj α HC HD adjC adjD ι ε hdinC hdinD E hN hN₁
    hεE hε₁
  let g := (HC.obj (op ω)).map ((λ_ ω).inv ≫ ((adjC ω).homEquiv _ _).symm a)
  have hg : a = (adjC ω).homEquiv _ _ (λ_ ω).hom ≫ g := by
    rw [← Adjunction.homEquiv_naturality_right, Iso.hom_inv_id_assoc, Equiv.apply_symm_apply]
  have e : (fun φ : E ⟶ 𝟙_ C => φ ≫ a) =
      (fun x => x ≫ g) ∘ fun φ : E ⟶ 𝟙_ C => φ ≫ (adjC ω).homEquiv _ _ (λ_ ω).hom := by
    funext φ
    rw [Function.comp_apply, hg, Category.assoc]
  rw [e]
  exact (bijective_comp_right_of_isIso g).comp hb

end Chain

end CategoryTheory.InternalHomTrace

end
