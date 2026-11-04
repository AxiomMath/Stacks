module

public import StacksFrontier.CategoryTheory.Adjunction.PullbackInternalHomSquare
public import StacksFrontier.CategoryTheory.Adjunction.ProjectionFormulaMapCurried
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.KunnethIsomorphism

/-!
# The pullback map of internal Homs against the tensor–Hom diagonal at any object

In the setting of `StacksFrontier.CategoryTheory.Adjunction.PullbackInternalHomPushforward` (an
adjunction `F ⊣ G`, tensor bifunctors with a comparison `μ : F(A ⊗ B) ≅ F A ⊗ F B` and internal
Homs `- ⊗ P ⊣ H(P, -)`), write `π_{Y,N} : G Y ⊗ N ⟶ G(Y ⊗ F N)` for the projection-formula map,
`φ : F H(P, M) ⟶ H(F P, F M)` for the map of Stacks 08JF, `δ_Y : Y ⊗ H(P, K) ⟶ H(P, Y ⊗ K)` for
the tensor–Hom diagonal and `c : G H(F P, -) ≅ H(P, G -)` for the conjugate of `μ`. For every
object `Y` of the target

`π_{Y,H(P,M)} ≫ G(Y ⊗ φ) ≫ G(δ_Y) ≫ c = δ_{G Y} ≫ H(P, π_{Y,M})`.

Applied to the map `E ⊗ Q ⟶ E ⊗ G Q' ⟶ G(F E ⊗ Q') ⟶ G(K' ⊗ Q')` attached to `β : Q ⟶ G Q'`
and `χ : F E ⟶ K'` (the Künneth form of the base change map of Stacks 0DKH), this shows: if the
map attached to `(M, χ)` is invertible, the diagonal `δ_Q` at `(P, M)` is invertible and `Q'` is
isomorphic to the unit, then the map attached to `(H(P, M), φ ≫ H(F P, χ))` is invertible. This
is the step of the proof of Stacks 0DKI (3) which passes condition (2) of Stacks 0DKG to
`R𝓗om(P, -)`.

## Main results

* `CategoryTheory.PullbackInternalHom.leftTensorHomDiagonal_naturality_left`,
  `CategoryTheory.PullbackInternalHom.leftTensorHomDiagonal_naturality_right`
* `CategoryTheory.PullbackInternalHom.isIso_leftTensorHomDiagonal_of_iso_unit`
* `CategoryTheory.PullbackInternalHom.adjunctionTensorMap_comp_map_leftTensorHomDiagonal`
* `CategoryTheory.PullbackInternalHom.braiding_comp_adjunctionTensorMapRight`,
  `CategoryTheory.PullbackInternalHom.braiding_comp_tensorBaseChangeComp`
* `CategoryTheory.PullbackInternalHom.tensorBaseChangeComp_pullbackHomMap_square`
* `CategoryTheory.PullbackInternalHom.isIso_tensorBaseChangeComp_pullbackHomMap`
-/

@[expose] public noncomputable section

namespace CategoryTheory.PullbackInternalHom

open Opposite
open scoped CategoryTheory.Prod
open Stacks.Cohomology.DerivedKunneth (adjunctionTensorMapRight)

section Diagonal

variable {C : Type*} [Category C] (TC : C ⥤ C ⥤ C) (HC : Cᵒᵖ ⥤ C ⥤ C)
  (adjC : ∀ P : C, TC.flip.obj P ⊣ HC.obj (op P))
  (αC : ∀ A B E : C, (TC.obj ((TC.obj A).obj B)).obj E ≅ (TC.obj A).obj ((TC.obj B).obj E))

/-- The adjoint of the tensor–Hom diagonal is the associator followed by the evaluation. -/
theorem homEquiv_symm_leftTensorHomDiagonal (Y P K : C) :
    ((adjC P).homEquiv _ _).symm (leftTensorHomDiagonal TC HC adjC αC Y P K) =
      (αC Y ((HC.obj (op P)).obj K) P).hom ≫ (TC.obj Y).map ((adjC P).counit.app K) := by
  unfold leftTensorHomDiagonal
  exact Equiv.symm_apply_apply _ _

/-- The tensor–Hom diagonal followed by the evaluation, as a rewrite rule. -/
@[reassoc]
theorem leftTensorHomDiagonal_comp_counit (Y P K : C) :
    (TC.map (leftTensorHomDiagonal TC HC adjC αC Y P K)).app P ≫
        (adjC P).counit.app ((TC.obj Y).obj K) =
      (αC Y ((HC.obj (op P)).obj K) P).hom ≫ (TC.obj Y).map ((adjC P).counit.app K) := by
  rw [← homEquiv_symm_leftTensorHomDiagonal TC HC adjC αC Y P K, Adjunction.homEquiv_counit]
  rfl

/-- **The tensor–Hom diagonal is natural in the tensor factor**, for an associator natural in
its first variable. -/
theorem leftTensorHomDiagonal_naturality_left
    (hαC : ∀ {A A' : C} (a : A ⟶ A') (B E : C),
      (TC.map ((TC.map a).app B)).app E ≫ (αC A' B E).hom =
        (αC A B E).hom ≫ (TC.map a).app ((TC.obj B).obj E))
    {Y Y' : C} (y : Y ⟶ Y') (P K : C) :
    (TC.map y).app ((HC.obj (op P)).obj K) ≫ leftTensorHomDiagonal TC HC adjC αC Y' P K =
      leftTensorHomDiagonal TC HC adjC αC Y P K ≫ (HC.obj (op P)).map ((TC.map y).app K) := by
  apply ((adjC P).homEquiv _ _).symm.injective
  rw [Adjunction.homEquiv_naturality_left_symm, Adjunction.homEquiv_naturality_right_symm,
    homEquiv_symm_leftTensorHomDiagonal, homEquiv_symm_leftTensorHomDiagonal]
  simp only [Functor.flip_obj_map]
  rw [reassoc_of% (hαC y ((HC.obj (op P)).obj K) P), Category.assoc]
  exact congrArg ((αC Y ((HC.obj (op P)).obj K) P).hom ≫ ·)
    ((TC.map y).naturality ((adjC P).counit.app K)).symm

/-- **The tensor–Hom diagonal is natural in the target of the internal Hom**, for an associator
natural in its middle variable. -/
theorem leftTensorHomDiagonal_naturality_right
    (hαC : ∀ (A : C) {B B' : C} (b : B ⟶ B') (E : C),
      (TC.map ((TC.obj A).map b)).app E ≫ (αC A B' E).hom =
        (αC A B E).hom ≫ (TC.obj A).map ((TC.map b).app E))
    (Y P : C) {K K' : C} (k : K ⟶ K') :
    (TC.obj Y).map ((HC.obj (op P)).map k) ≫ leftTensorHomDiagonal TC HC adjC αC Y P K' =
      leftTensorHomDiagonal TC HC adjC αC Y P K ≫ (HC.obj (op P)).map ((TC.obj Y).map k) := by
  apply ((adjC P).homEquiv _ _).symm.injective
  rw [Adjunction.homEquiv_naturality_left_symm, Adjunction.homEquiv_naturality_right_symm,
    homEquiv_symm_leftTensorHomDiagonal, homEquiv_symm_leftTensorHomDiagonal]
  simp only [Functor.flip_obj_map]
  rw [reassoc_of% (hαC Y ((HC.obj (op P)).map k) P), ← Functor.map_comp, Category.assoc,
    ← Functor.map_comp]
  congr 2
  exact (adjC P).counit.naturality k

/-- **The tensor–Hom diagonal at the unit is the unit law**, for a left unitor satisfying the
triangle identity. -/
theorem leftTensorHomDiagonal_unit (O : C) (lam : TC.obj O ≅ 𝟭 C)
    (hunit : ∀ A B : C,
      (TC.map (lam.hom.app A)).app B = (αC O A B).hom ≫ lam.hom.app ((TC.obj A).obj B))
    (P K : C) :
    leftTensorHomDiagonal TC HC adjC αC O P K ≫ (HC.obj (op P)).map (lam.hom.app K) =
      lam.hom.app ((HC.obj (op P)).obj K) := by
  apply ((adjC P).homEquiv _ _).symm.injective
  rw [Adjunction.homEquiv_naturality_right_symm, homEquiv_symm_leftTensorHomDiagonal]
  rw [Adjunction.homEquiv_counit]
  simp only [Functor.flip_obj_map, Functor.id_obj]
  rw [hunit, Category.assoc, Category.assoc]
  exact congrArg ((αC O ((HC.obj (op P)).obj K) P).hom ≫ ·)
    (lam.hom.naturality ((adjC P).counit.app K))

/-- If `f ≫ g = h` with `g` and `h` invertible, then `f` is invertible. -/
private theorem isIso_of_comp_eq_of_isIso {C : Type*} [Category C] {X Y Z : C} {f : X ⟶ Y}
    {g : Y ⟶ Z} {h : X ⟶ Z} [IsIso g] [IsIso h] (e : f ≫ g = h) : IsIso f := by
  have : IsIso (f ≫ g) := by rw [e]; infer_instance
  exact IsIso.of_isIso_comp_right f g

/-- **The tensor–Hom diagonal at an object isomorphic to the unit is invertible.** -/
theorem isIso_leftTensorHomDiagonal_of_iso_unit
    (hαC : ∀ {A A' : C} (a : A ⟶ A') (B E : C),
      (TC.map ((TC.map a).app B)).app E ≫ (αC A' B E).hom =
        (αC A B E).hom ≫ (TC.map a).app ((TC.obj B).obj E))
    (O : C) (lam : TC.obj O ≅ 𝟭 C)
    (hunit : ∀ A B : C,
      (TC.map (lam.hom.app A)).app B = (αC O A B).hom ≫ lam.hom.app ((TC.obj A).obj B))
    {Y : C} (e : Y ≅ O) (P K : C) :
    IsIso (leftTensorHomDiagonal TC HC adjC αC Y P K) := by
  have hO : IsIso (leftTensorHomDiagonal TC HC adjC αC O P K) := by
    exact isIso_of_comp_eq_of_isIso (leftTensorHomDiagonal_unit TC HC adjC αC O lam hunit P K)
  exact isIso_of_comp_eq_of_isIso
    (leftTensorHomDiagonal_naturality_left TC HC adjC αC hαC e.hom P K).symm

end Diagonal

variable {C D : Type*} [Category C] [Category D]
  {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)
  (TC : C ⥤ C ⥤ C) (TD : D ⥤ D ⥤ D)
  (μ : Functor.uncurry.obj TC ⋙ F ≅ F.prod F ⋙ Functor.uncurry.obj TD)
  (HC : Cᵒᵖ ⥤ C ⥤ C) (HD : Dᵒᵖ ⥤ D ⥤ D)
  (adjC : ∀ P : C, TC.flip.obj P ⊣ HC.obj (op P))
  (adjD : ∀ P : D, TD.flip.obj P ⊣ HD.obj (op P))
  (αC : ∀ A B E : C, (TC.obj ((TC.obj A).obj B)).obj E ≅ (TC.obj A).obj ((TC.obj B).obj E))
  (αD : ∀ A B E : D, (TD.obj ((TD.obj A).obj B)).obj E ≅ (TD.obj A).obj ((TD.obj B).obj E))

/-- **`G` of the map of Stacks 08JF against the tensor–Hom diagonal at any object `Y`.** If `μ`
is compatible with the associators and `α_D` is natural in its first two variables, then
`π_{Y,H(P,M)} ≫ G(Y ⊗ φ) ≫ G(δ_Y) ≫ c = δ_{G Y} ≫ H(P, π_{Y,M})`. -/
theorem adjunctionTensorMap_comp_map_leftTensorHomDiagonal
    (hassoc : ∀ A B E : C, F.map (αC A B E).hom ≫ μ.hom.app (A, (TC.obj B).obj E) ≫
        (TD.obj (F.obj A)).map (μ.hom.app (B, E)) =
      μ.hom.app ((TC.obj A).obj B, E) ≫ (TD.map (μ.hom.app (A, B))).app (F.obj E) ≫
        (αD (F.obj A) (F.obj B) (F.obj E)).hom)
    (hαD : ∀ {A A' : D} (a : A ⟶ A') (B E : D),
      (TD.map ((TD.map a).app B)).app E ≫ (αD A' B E).hom =
        (αD A B E).hom ≫ (TD.map a).app ((TD.obj B).obj E))
    (hαDm : ∀ (A : D) {B B' : D} (b : B ⟶ B') (E : D),
      (TD.map ((TD.obj A).map b)).app E ≫ (αD A B' E).hom =
        (αD A B E).hom ≫ (TD.obj A).map ((TD.map b).app E))
    (Y : D) (P M : C) (μR : TC.flip.obj P ⋙ F ≅ F ⋙ TD.flip.obj (F.obj P))
    (hμR : ∀ T, μR.hom.app T = μ.hom.app (T, P)) :
    adjunctionTensorMap adj (Functor.uncurry.obj TC) (Functor.uncurry.obj TD) μ.hom Y
        ((HC.obj (op P)).obj M) ≫
      G.map ((TD.obj Y).map (pullbackHomMap TC TD μ HC HD adjC adjD P M)) ≫
      G.map (leftTensorHomDiagonal TD HD adjD αD Y (F.obj P) (F.obj M)) ≫
      (conjugateIsoEquiv (adj.comp (adjD (F.obj P))) ((adjC P).comp adj) μR).hom.app
        ((TD.obj Y).obj (F.obj M)) =
    leftTensorHomDiagonal TC HC adjC αC (G.obj Y) P M ≫
      (HC.obj (op P)).map
        (adjunctionTensorMap adj (Functor.uncurry.obj TC) (Functor.uncurry.obj TD) μ.hom Y M) := by
  apply ((adjC P).homEquiv _ _).symm.injective
  rw [Adjunction.homEquiv_naturality_left_symm, Adjunction.homEquiv_naturality_left_symm,
    Adjunction.homEquiv_naturality_left_symm,
    homEquiv_symm_conjugateIsoEquiv_hom_app adj TC TD μ HC HD adjC adjD P μR hμR,
    Adjunction.homEquiv_naturality_right_symm, Adjunction.homEquiv_counit]
  have pa := adjunctionTensorMap_assoc adj TC TD μ αC αD hassoc hαD Y
    ((HC.obj (op P)).obj M) P
  have hm := hαDm Y (pullbackHomMap TC TD μ HC HD adjC adjD P M) (F.obj P)
  have hφ := homEquiv_symm_pullbackHomMap TC TD μ HC HD adjC adjD P M
  rw [Adjunction.homEquiv_counit] at hφ
  dsimp only [Functor.flip_obj_map] at hφ
  dsimp only [Functor.flip_obj_map, Functor.uncurry_obj_obj, Functor.prod_obj, Functor.comp_obj]
    at pa ⊢
  rw [Category.assoc, leftTensorHomDiagonal_comp_counit_assoc,
    adjunctionTensorMap_natural_left_curried_assoc adj TC TD μ.hom
      (leftTensorHomDiagonal TD HD adjD αD Y (F.obj P) (F.obj M)),
    adjunctionTensorMap_natural_left_curried_assoc adj TC TD μ.hom
      ((TD.obj Y).map (pullbackHomMap TC TD μ HC HD adjC adjD P M)),
    ← G.map_comp, ← G.map_comp, leftTensorHomDiagonal_comp_counit, reassoc_of% hm,
    ← Functor.map_comp (TD.obj Y), hφ]
  simp only [Functor.map_comp]
  rw [reassoc_of% pa, adjunctionTensorMap_natural_right_curried adj TC TD μ.hom]
  simp only [← G.map_comp, ← Functor.map_comp, Iso.hom_inv_id_app_assoc]

/-- **The projection-formula maps of the two orders differ by the commutativity constraints**,
for a comparison `μ` compatible with them. -/
theorem braiding_comp_adjunctionTensorMapRight
    (bC : ∀ A B : C, (TC.obj A).obj B ≅ (TC.obj B).obj A)
    (bD : ∀ A B : D, (TD.obj A).obj B ≅ (TD.obj B).obj A)
    (hbμ : ∀ A B : C, F.map (bC A B).hom ≫ μ.hom.app (B, A) =
      μ.hom.app (A, B) ≫ (bD (F.obj A) (F.obj B)).hom)
    (hbD : ∀ {A A' : D} (a : A ⟶ A') (B : D),
      (TD.map a).app B ≫ (bD A' B).hom = (bD A B).hom ≫ (TD.obj B).map a)
    (Y : D) (E : C) :
    (bC (G.obj Y) E).hom ≫
        adjunctionTensorMapRight adj (Functor.uncurry.obj TC) (Functor.uncurry.obj TD) μ.hom E Y =
      adjunctionTensorMap adj (Functor.uncurry.obj TC) (Functor.uncurry.obj TD) μ.hom Y E ≫
        G.map (bD Y (F.obj E)).hom := by
  have hR : F.map (adjunctionTensorMapRight adj (Functor.uncurry.obj TC)
      (Functor.uncurry.obj TD) μ.hom E Y) ≫
        adj.counit.app ((Functor.uncurry.obj TD).obj (F.obj E, Y)) =
      μ.hom.app (E, G.obj Y) ≫ (Functor.uncurry.obj TD).map (𝟙 (F.obj E) ×ₘ adj.counit.app Y) := by
    have h := (adj.homEquiv _ _).symm_apply_apply
      (μ.hom.app (E, G.obj Y) ≫ (Functor.uncurry.obj TD).map (𝟙 (F.obj E) ×ₘ adj.counit.app Y))
    rw [Adjunction.homEquiv_counit] at h
    exact h
  apply (adj.homEquiv _ _).symm.injective
  rw [Adjunction.homEquiv_naturality_left_symm, Adjunction.homEquiv_naturality_right_symm,
    Adjunction.homEquiv_counit, Adjunction.homEquiv_counit, hR, Category.assoc,
    map_adjunctionTensorMap_comp_counit_assoc]
  simp only [Functor.comp_obj, Functor.prod_obj, Functor.uncurry_obj_obj, Functor.uncurry_obj_map,
    Functor.map_id, NatTrans.id_app, Category.id_comp, Category.comp_id]
  rw [reassoc_of% (hbμ (G.obj Y) E), hbD]

section BaseChange

variable (bC : ∀ A B : C, (TC.obj A).obj B ≅ (TC.obj B).obj A)
  (bD : ∀ A B : D, (TD.obj A).obj B ≅ (TD.obj B).obj A)

/-- **The Künneth form of the base change map, with the factors interchanged.** For
`β : Q ⟶ G Q'` and `χ : F E ⟶ K'`, the map `E ⊗ Q ⟶ E ⊗ G Q' ⟶ G(F E ⊗ Q') ⟶ G(K' ⊗ Q')` read
through the commutativity constraints is `Q ⊗ E ⟶ G Q' ⊗ E ⟶ G(Q' ⊗ F E) ⟶ G(Q' ⊗ K')`. -/
theorem braiding_comp_tensorBaseChangeComp
    (hbμ : ∀ A B : C, F.map (bC A B).hom ≫ μ.hom.app (B, A) =
      μ.hom.app (A, B) ≫ (bD (F.obj A) (F.obj B)).hom)
    (hbC : ∀ {A A' B B' : C} (a : A ⟶ A') (b : B ⟶ B'),
      (TC.map a).app B ≫ (TC.obj A').map b ≫ (bC A' B').hom =
        (bC A B).hom ≫ (TC.map b).app A ≫ (TC.obj B').map a)
    (hbD : ∀ {A A' B B' : D} (a : A ⟶ A') (b : B ⟶ B'),
      (TD.map a).app B ≫ (TD.obj A').map b ≫ (bD A' B').hom =
        (bD A B).hom ≫ (TD.map b).app A ≫ (TD.obj B').map a)
    {Q : C} {Q' : D} (β : Q ⟶ G.obj Q') (E : C) {K' : D} (χ : F.obj E ⟶ K') :
    (bC Q E).hom ≫ (Functor.uncurry.obj TC).map (𝟙 E ×ₘ β) ≫
        adjunctionTensorMapRight adj (Functor.uncurry.obj TC) (Functor.uncurry.obj TD) μ.hom E
          Q' ≫ G.map ((Functor.uncurry.obj TD).map (χ ×ₘ 𝟙 Q')) =
      ((TC.map β).app E ≫
        adjunctionTensorMap adj (Functor.uncurry.obj TC) (Functor.uncurry.obj TD) μ.hom Q' E ≫
          G.map ((TD.obj Q').map χ)) ≫ G.map (bD Q' K').hom := by
  have h₁ : (Functor.uncurry.obj TC).map (𝟙 E ×ₘ β) = (TC.obj E).map β := by
    simp only [Functor.uncurry_obj_map, Functor.map_id, NatTrans.id_app, Category.id_comp]
  have h₂ : (Functor.uncurry.obj TD).map (χ ×ₘ 𝟙 Q') = (TD.map χ).app Q' := by
    simp only [Functor.uncurry_obj_map, Functor.map_id, Category.comp_id]
  have hC : (TC.map β).app E ≫ (bC (G.obj Q') E).hom = (bC Q E).hom ≫ (TC.obj E).map β := by
    simpa using hbC β (𝟙 E)
  have hD : ∀ {A A' : D} (a : A ⟶ A') (B : D),
      (TD.map a).app B ≫ (bD A' B).hom = (bD A B).hom ≫ (TD.obj B).map a := fun a B => by
    simpa using hbD a (𝟙 B)
  have hD' : (TD.obj Q').map χ ≫ (bD Q' K').hom = (bD Q' (F.obj E)).hom ≫ (TD.map χ).app Q' := by
    simpa using hbD (𝟙 Q') χ
  rw [h₁, h₂, ← reassoc_of% hC,
    reassoc_of% (braiding_comp_adjunctionTensorMapRight adj TC TD μ bC bD hbμ hD Q' E),
    ← G.map_comp, ← hD', G.map_comp, Category.assoc, Category.assoc]

/-- **The core square of Stacks 0DKI (3).** With `ψ = φ ≫ H(F P, φ₀)` for the map `φ` of
Stacks 08JF, the factor-interchanged Künneth map at `(H(P, M), ψ)` followed by `G(δ_{Q'})` and
`c` is the diagonal `δ_Q` followed by `H(P, -)` of the Künneth map at `(M, φ₀)`. -/
theorem tensorBaseChangeComp_pullbackHomMap_square
    (hassoc : ∀ A B E : C, F.map (αC A B E).hom ≫ μ.hom.app (A, (TC.obj B).obj E) ≫
        (TD.obj (F.obj A)).map (μ.hom.app (B, E)) =
      μ.hom.app ((TC.obj A).obj B, E) ≫ (TD.map (μ.hom.app (A, B))).app (F.obj E) ≫
        (αD (F.obj A) (F.obj B) (F.obj E)).hom)
    (hαD : ∀ {A A' : D} (a : A ⟶ A') (B E : D),
      (TD.map ((TD.map a).app B)).app E ≫ (αD A' B E).hom =
        (αD A B E).hom ≫ (TD.map a).app ((TD.obj B).obj E))
    (hαDm : ∀ (A : D) {B B' : D} (b : B ⟶ B') (E : D),
      (TD.map ((TD.obj A).map b)).app E ≫ (αD A B' E).hom =
        (αD A B E).hom ≫ (TD.obj A).map ((TD.map b).app E))
    (hαC : ∀ {A A' : C} (a : A ⟶ A') (B E : C),
      (TC.map ((TC.map a).app B)).app E ≫ (αC A' B E).hom =
        (αC A B E).hom ≫ (TC.map a).app ((TC.obj B).obj E))
    {Q : C} {Q' : D} (β : Q ⟶ G.obj Q') (P M : C) {K' : D} (φ₀ : F.obj M ⟶ K')
    (μR : TC.flip.obj P ⋙ F ≅ F ⋙ TD.flip.obj (F.obj P))
    (hμR : ∀ T, μR.hom.app T = μ.hom.app (T, P)) :
    ((TC.map β).app ((HC.obj (op P)).obj M) ≫
        adjunctionTensorMap adj (Functor.uncurry.obj TC) (Functor.uncurry.obj TD) μ.hom Q'
          ((HC.obj (op P)).obj M) ≫
        G.map ((TD.obj Q').map (pullbackHomMap TC TD μ HC HD adjC adjD P M ≫
          (HD.obj (op (F.obj P))).map φ₀))) ≫
      G.map (leftTensorHomDiagonal TD HD adjD αD Q' (F.obj P) K') ≫
      (conjugateIsoEquiv (adj.comp (adjD (F.obj P))) ((adjC P).comp adj) μR).hom.app
        ((TD.obj Q').obj K') =
    leftTensorHomDiagonal TC HC adjC αC Q P M ≫
      (HC.obj (op P)).map ((TC.map β).app M ≫
        adjunctionTensorMap adj (Functor.uncurry.obj TC) (Functor.uncurry.obj TD) μ.hom Q' M ≫
          G.map ((TD.obj Q').map φ₀)) := by
  have hR := leftTensorHomDiagonal_naturality_right TD HD adjD αD hαDm Q' (F.obj P) φ₀
  have hc := (conjugateIsoEquiv (adj.comp (adjD (F.obj P))) ((adjC P).comp adj) μR).hom.naturality
    ((TD.obj Q').map φ₀)
  have hG := adjunctionTensorMap_comp_map_leftTensorHomDiagonal adj TC TD μ HC HD adjC adjD αC αD
    hassoc hαD hαDm Q' P M μR hμR
  have hL := leftTensorHomDiagonal_naturality_left TC HC adjC αC hαC β P M
  simp only [Functor.comp_obj, Functor.comp_map] at hc
  simp only [Functor.map_comp, Category.assoc]
  rw [← G.map_comp_assoc ((TD.obj Q').map ((HD.obj (op (F.obj P))).map φ₀)), hR, G.map_comp_assoc,
    hc, reassoc_of% hG, reassoc_of% hL]

/-- **Stacks 0DKI (3), the abstract step.** Let `β : Q ⟶ G Q'` with `Q'` isomorphic to the unit
`O` of the target, and for `χ : F E ⟶ K'` let `E ⊗ Q ⟶ E ⊗ G Q' ⟶ G(F E ⊗ Q') ⟶ G(K' ⊗ Q')` be
the Künneth form of the base change map. If it is invertible at `(M, φ₀)` and the tensor–Hom
diagonal `Q ⊗ H(P, M) ⟶ H(P, Q ⊗ M)` is invertible, it is invertible at
`(H(P, M), φ ≫ H(F P, φ₀))`, for `φ` the map of Stacks 08JF; the comparison `μ` is assumed
compatible with the associators and commutativity constraints, which are natural, and the left
unitor satisfies the triangle identity. -/
theorem isIso_tensorBaseChangeComp_pullbackHomMap
    (hassoc : ∀ A B E : C, F.map (αC A B E).hom ≫ μ.hom.app (A, (TC.obj B).obj E) ≫
        (TD.obj (F.obj A)).map (μ.hom.app (B, E)) =
      μ.hom.app ((TC.obj A).obj B, E) ≫ (TD.map (μ.hom.app (A, B))).app (F.obj E) ≫
        (αD (F.obj A) (F.obj B) (F.obj E)).hom)
    (hαD : ∀ {A A' : D} (a : A ⟶ A') (B E : D),
      (TD.map ((TD.map a).app B)).app E ≫ (αD A' B E).hom =
        (αD A B E).hom ≫ (TD.map a).app ((TD.obj B).obj E))
    (hαDm : ∀ (A : D) {B B' : D} (b : B ⟶ B') (E : D),
      (TD.map ((TD.obj A).map b)).app E ≫ (αD A B' E).hom =
        (αD A B E).hom ≫ (TD.obj A).map ((TD.map b).app E))
    (hαC : ∀ {A A' : C} (a : A ⟶ A') (B E : C),
      (TC.map ((TC.map a).app B)).app E ≫ (αC A' B E).hom =
        (αC A B E).hom ≫ (TC.map a).app ((TC.obj B).obj E))
    (hbμ : ∀ A B : C, F.map (bC A B).hom ≫ μ.hom.app (B, A) =
      μ.hom.app (A, B) ≫ (bD (F.obj A) (F.obj B)).hom)
    (hbC : ∀ {A A' B B' : C} (a : A ⟶ A') (b : B ⟶ B'),
      (TC.map a).app B ≫ (TC.obj A').map b ≫ (bC A' B').hom =
        (bC A B).hom ≫ (TC.map b).app A ≫ (TC.obj B').map a)
    (hbD : ∀ {A A' B B' : D} (a : A ⟶ A') (b : B ⟶ B'),
      (TD.map a).app B ≫ (TD.obj A').map b ≫ (bD A' B').hom =
        (bD A B).hom ≫ (TD.map b).app A ≫ (TD.obj B').map a)
    (O : D) (lam : TD.obj O ≅ 𝟭 D)
    (hunit : ∀ A B : D,
      (TD.map (lam.hom.app A)).app B = (αD O A B).hom ≫ lam.hom.app ((TD.obj A).obj B))
    {Q : C} {Q' : D} (eQ' : Q' ≅ O) (β : Q ⟶ G.obj Q') (P M : C) {K' : D}
    (φ₀ : F.obj M ⟶ K')
    (hδ : IsIso (leftTensorHomDiagonal TC HC adjC αC Q P M))
    (h : IsIso ((Functor.uncurry.obj TC).map (𝟙 M ×ₘ β) ≫
      adjunctionTensorMapRight adj (Functor.uncurry.obj TC) (Functor.uncurry.obj TD) μ.hom M Q' ≫
        G.map ((Functor.uncurry.obj TD).map (φ₀ ×ₘ 𝟙 Q')))) :
    IsIso ((Functor.uncurry.obj TC).map (𝟙 ((HC.obj (op P)).obj M) ×ₘ β) ≫
      adjunctionTensorMapRight adj (Functor.uncurry.obj TC) (Functor.uncurry.obj TD) μ.hom
        ((HC.obj (op P)).obj M) Q' ≫
        G.map ((Functor.uncurry.obj TD).map
          ((pullbackHomMap TC TD μ HC HD adjC adjD P M ≫ (HD.obj (op (F.obj P))).map φ₀) ×ₘ
            𝟙 Q'))) := by
  let μR : TC.flip.obj P ⋙ F ≅ F ⋙ TD.flip.obj (F.obj P) :=
    NatIso.ofComponents (fun T => μ.app (T, P)) fun {T T'} t => by
      have h := μ.hom.naturality (X := (T, P)) (Y := (T', P)) (t ×ₘ 𝟙 P)
      simp only [Functor.comp_obj, Functor.prod_obj, Functor.uncurry_obj_obj, Functor.comp_map,
        Functor.uncurry_obj_map, Functor.prod_map, Functor.map_id, Category.comp_id] at h
      simpa using h
  have eM := braiding_comp_tensorBaseChangeComp adj TC TD μ bC bD hbμ hbC hbD β M φ₀
  have eH := braiding_comp_tensorBaseChangeComp adj TC TD μ bC bD hbμ hbC hbD β
    ((HC.obj (op P)).obj M)
    (pullbackHomMap TC TD μ HC HD adjC adjD P M ≫ (HD.obj (op (F.obj P))).map φ₀)
  have sq := tensorBaseChangeComp_pullbackHomMap_square adj TC TD μ HC HD adjC adjD αC αD hassoc
    hαD hαDm hαC β P M φ₀ μR (fun _ => rfl)
  -- the factor-interchanged map at `(M, φ₀)` is invertible
  have hM : IsIso ((TC.map β).app M ≫
      adjunctionTensorMap adj (Functor.uncurry.obj TC) (Functor.uncurry.obj TD) μ.hom Q' M ≫
        G.map ((TD.obj Q').map φ₀)) := by
    exact isIso_of_comp_eq_of_isIso eM.symm
  have hδ' : IsIso (leftTensorHomDiagonal TD HD adjD αD Q' (F.obj P) K') :=
    isIso_leftTensorHomDiagonal_of_iso_unit TD HD adjD αD hαD O lam hunit eQ' (F.obj P) K'
  -- the factor-interchanged map at `(H(P, M), ψ)` is invertible
  have hH : IsIso ((TC.map β).app ((HC.obj (op P)).obj M) ≫
      adjunctionTensorMap adj (Functor.uncurry.obj TC) (Functor.uncurry.obj TD) μ.hom Q'
        ((HC.obj (op P)).obj M) ≫
      G.map ((TD.obj Q').map (pullbackHomMap TC TD μ HC HD adjC adjD P M ≫
        (HD.obj (op (F.obj P))).map φ₀))) := by
    exact isIso_of_comp_eq_of_isIso sq
  have : IsIso ((bC Q ((HC.obj (op P)).obj M)).hom ≫
      (Functor.uncurry.obj TC).map (𝟙 ((HC.obj (op P)).obj M) ×ₘ β) ≫
      adjunctionTensorMapRight adj (Functor.uncurry.obj TC) (Functor.uncurry.obj TD) μ.hom
        ((HC.obj (op P)).obj M) Q' ≫
        G.map ((Functor.uncurry.obj TD).map
          ((pullbackHomMap TC TD μ HC HD adjC adjD P M ≫ (HD.obj (op (F.obj P))).map φ₀) ×ₘ
            𝟙 Q'))) := by
    rw [eH]; infer_instance
  exact IsIso.of_isIso_comp_left (bC Q ((HC.obj (op P)).obj M)).hom _

end BaseChange

end CategoryTheory.PullbackInternalHom

end
