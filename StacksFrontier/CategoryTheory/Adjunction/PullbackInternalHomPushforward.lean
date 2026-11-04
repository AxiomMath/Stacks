module

public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Functor.Currying
public import StacksFrontier.CategoryTheory.Adjunction.ProjectionFormulaMap

/-!
# The pushforward of the pullback map of internal Homs, for abstract tensor–Hom data

Let `F ⊣ G` be an adjunction with `F : C ⥤ D` (a derived pullback `Lg^*`, with `G = Rg_*`), let
`T_C`, `T_D` be tensor bifunctors with an isomorphism `μ : F(A ⊗ B) ≅ F A ⊗ F B`, and let
`H_C`, `H_D` be internal Hom bifunctors with `- ⊗ P ⊣ H(P, -)` for every `P`. The map

`φ : F H_C(M, K) ⟶ H_D(F M, F K)`

is adjoint to `F H_C(M, K) ⊗ F M ≅ F(H_C(M, K) ⊗ M) ⟶ F K`. For a unit object `O` of `D` with a
left unitor `O ⊗ - ≅ 𝟭`, write `π` for the projection-formula map `G E ⊗ N ⟶ G(E ⊗ F N)` and
`ρ_N : G O ⊗ N ⟶ G(O ⊗ F N) ≅ G F N`. The main result says that, if `μ` is compatible with
associators `α_C`, `α_D` and the left unitor satisfies the triangle identity, then the square

```
G O ⊗ H_C(M, K) ----δ----> H_C(M, G O ⊗ K)
      |ρ                           |H_C(M, ρ)
   G F H_C(M, K) --c ∘ G φ--> H_C(M, G F K)
```

commutes, where `c : G H_D(F M, -) ≅ H_C(M, G -)` is the conjugate of `μ` and `δ` is the
tensor–Hom diagonal adjoint to `(P ⊗ H_C(M, K)) ⊗ M ≅ P ⊗ (H_C(M, K) ⊗ M) ⟶ P ⊗ K`. So `G φ` is
invertible as soon as `ρ` (a projection formula) and `δ` are. This is the computation in the
proof of [Stacks, Tag 0E4S] which identifies `R(g')_*` of the map of [Stacks, Tag 08JF] with the
map of [Stacks, Tag 0BYU] at `g'_*𝒪`.

## Main definitions

* `CategoryTheory.PullbackInternalHom.pullbackHomMap`: the map `φ` of [Stacks, Tag 08JF].
* `CategoryTheory.PullbackInternalHom.projectionUnitMap`: `ρ_N : G O ⊗ N ⟶ G F N`.
* `CategoryTheory.PullbackInternalHom.leftTensorHomDiagonal`: the diagonal `δ`.

## Main results

* `CategoryTheory.PullbackInternalHom.homEquiv_symm_conjugateIsoEquiv_hom_app`: the adjoint of
  `c` is the projection-formula map followed by `G` of the evaluation.
* `CategoryTheory.PullbackInternalHom.adjunctionTensorMap_assoc`: the projection-formula map is
  compatible with the associators.
* `CategoryTheory.PullbackInternalHom.projectionUnitMap_comp_map_pullbackHomMap`: the square.
* `CategoryTheory.PullbackInternalHom.isIso_map_pullbackHomMap`: `G φ` is invertible when `ρ` at
  both objects and `δ` are.

## References

* [Stacks Project, Tag 0E4S](https://stacks.math.columbia.edu/tag/0E4S)
* [Stacks Project, Tag 08JF](https://stacks.math.columbia.edu/tag/08JF)
* [Stacks Project, Tag 0BYU](https://stacks.math.columbia.edu/tag/0BYU)
-/

@[expose] public noncomputable section

namespace CategoryTheory.PullbackInternalHom

open Opposite
open scoped CategoryTheory.Prod

variable {C D : Type*} [Category C] [Category D]
  {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)
  (TC : C ⥤ C ⥤ C) (TD : D ⥤ D ⥤ D)
  (μ : Functor.uncurry.obj TC ⋙ F ≅ F.prod F ⋙ Functor.uncurry.obj TD)
  (HC : Cᵒᵖ ⥤ C ⥤ C) (HD : Dᵒᵖ ⥤ D ⥤ D)
  (adjC : ∀ P : C, TC.flip.obj P ⊣ HC.obj (op P))
  (adjD : ∀ P : D, TD.flip.obj P ⊣ HD.obj (op P))

/-- **The pullback map of internal Homs** `F H_C(M, K) ⟶ H_D(F M, F K)` of [Stacks, Tag 08JF]:
the adjoint of `F H_C(M, K) ⊗ F M ≅ F(H_C(M, K) ⊗ M) ⟶ F K`. -/
def pullbackHomMap (M K : C) :
    F.obj ((HC.obj (op M)).obj K) ⟶ (HD.obj (op (F.obj M))).obj (F.obj K) :=
  (adjD (F.obj M)).homEquiv _ _
    (μ.inv.app ((HC.obj (op M)).obj K, M) ≫ F.map ((adjC M).counit.app K))

/-- **The adjoint of the conjugate of `μ`.** For `μR : (- ⊗ M) ⋙ F ≅ F ⋙ (- ⊗ F M)` with
components those of `μ`, the adjoint of `c : G H_D(F M, N) ⟶ H_C(M, G N)` is the
projection-formula map `G H_D(F M, N) ⊗ M ⟶ G(H_D(F M, N) ⊗ F M)` followed by `G` of the
evaluation. -/
theorem homEquiv_symm_conjugateIsoEquiv_hom_app (M : C)
    (μR : TC.flip.obj M ⋙ F ≅ F ⋙ TD.flip.obj (F.obj M))
    (hμR : ∀ T, μR.hom.app T = μ.hom.app (T, M)) (N : D) :
    ((adjC M).homEquiv (G.obj ((HD.obj (op (F.obj M))).obj N)) (G.obj N)).symm
        ((conjugateIsoEquiv (adj.comp (adjD (F.obj M))) ((adjC M).comp adj) μR).hom.app N) =
      adjunctionTensorMap adj (Functor.uncurry.obj TC) (Functor.uncurry.obj TD) μ.hom
          ((HD.obj (op (F.obj M))).obj N) M ≫
        G.map ((adjD (F.obj M)).counit.app N) := by
  apply (adj.homEquiv _ _).symm.injective
  have h := conjugateEquiv_counit (adj.comp (adjD (F.obj M))) ((adjC M).comp adj) μR.hom N
  simp only [Functor.comp_map, Adjunction.comp_counit_app, Functor.comp_obj] at h
  rw [Adjunction.homEquiv_counit, Adjunction.homEquiv_counit, Adjunction.homEquiv_counit,
    Functor.map_comp, Category.assoc, conjugateIsoEquiv_apply_hom, h, hμR, Functor.map_comp,
    Category.assoc, adj.counit_naturality, map_adjunctionTensorMap_comp_counit_assoc]
  simp

/-- **The projection-formula map is compatible with the associators**, given that `μ` is:
`(G E ⊗ A) ⊗ B ⟶ G(E ⊗ F A) ⊗ B ⟶ G((E ⊗ F A) ⊗ F B) ≅ G(E ⊗ (F A ⊗ F B))` is
`(G E ⊗ A) ⊗ B ≅ G E ⊗ (A ⊗ B) ⟶ G(E ⊗ F(A ⊗ B)) ≅ G(E ⊗ (F A ⊗ F B))`. -/
theorem adjunctionTensorMap_assoc
    (αC : ∀ A B E : C, (TC.obj ((TC.obj A).obj B)).obj E ≅ (TC.obj A).obj ((TC.obj B).obj E))
    (αD : ∀ A B E : D, (TD.obj ((TD.obj A).obj B)).obj E ≅ (TD.obj A).obj ((TD.obj B).obj E))
    (hassoc : ∀ A B E : C, F.map (αC A B E).hom ≫ μ.hom.app (A, (TC.obj B).obj E) ≫
        (TD.obj (F.obj A)).map (μ.hom.app (B, E)) =
      μ.hom.app ((TC.obj A).obj B, E) ≫ (TD.map (μ.hom.app (A, B))).app (F.obj E) ≫
        (αD (F.obj A) (F.obj B) (F.obj E)).hom)
    (hαD : ∀ {A A' : D} (a : A ⟶ A') (B E : D),
      (TD.map ((TD.map a).app B)).app E ≫ (αD A' B E).hom =
        (αD A B E).hom ≫ (TD.map a).app ((TD.obj B).obj E))
    (E : D) (A B : C) :
    (TC.map (adjunctionTensorMap adj (Functor.uncurry.obj TC) (Functor.uncurry.obj TD) μ.hom
          E A)).app B ≫
        adjunctionTensorMap adj (Functor.uncurry.obj TC) (Functor.uncurry.obj TD) μ.hom
          ((TD.obj E).obj (F.obj A)) B ≫
        G.map (αD E (F.obj A) (F.obj B)).hom =
      (αC (G.obj E) A B).hom ≫
        adjunctionTensorMap adj (Functor.uncurry.obj TC) (Functor.uncurry.obj TD) μ.hom
          E ((TC.obj A).obj B) ≫
        G.map ((TD.obj E).map (μ.hom.app (A, B))) := by
  apply (adj.homEquiv _ _).symm.injective
  simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc,
    adj.counit_naturality]
  rw [map_adjunctionTensorMap_comp_counit_assoc, map_adjunctionTensorMap_comp_counit_assoc]
  have hn := μ.hom.naturality
    ((adjunctionTensorMap adj (Functor.uncurry.obj TC) (Functor.uncurry.obj TD) μ.hom E A) ×ₘ
      𝟙 B)
  have hπ := map_adjunctionTensorMap_comp_counit adj (Functor.uncurry.obj TC)
    (Functor.uncurry.obj TD) μ.hom E A
  simp only [Functor.comp_obj, Functor.prod_obj, Functor.uncurry_obj_obj, Functor.comp_map,
    Functor.uncurry_obj_map, Functor.prod_map, Functor.map_id, Category.comp_id] at hn hπ ⊢
  rw [reassoc_of% hn]
  rw [← NatTrans.comp_app_assoc, ← Functor.map_comp, hπ, Functor.map_comp,
    NatTrans.comp_app_assoc,
    hαD (A := F.obj (G.obj E)) (A' := E) (adj.counit.app E) (F.obj A) (F.obj B)]
  have hc := (TD.map (adj.counit.app E)).naturality (μ.hom.app (A, B))
  simp only [Functor.id_obj, Functor.comp_obj, Functor.uncurry_obj_obj, Functor.prod_obj] at hc
  rw [← hc, reassoc_of% (hassoc (G.obj E) A B)]

section Invariance

omit [Category C] [Category D] in
/-- The comparison `μ`, read on a pair of morphisms in the curried spelling. -/
private lemma μ_hom_naturality₂ [Category C] [Category D] {F : C ⥤ D} {TC : C ⥤ C ⥤ C}
    {TD : D ⥤ D ⥤ D} (μ : Functor.uncurry.obj TC ⋙ F ≅ F.prod F ⋙ Functor.uncurry.obj TD)
    {A A' B B' : C} (x : A ⟶ A') (y : B ⟶ B') :
    F.map ((TC.map x).app B ≫ (TC.obj A').map y) ≫ μ.hom.app (A', B') =
      μ.hom.app (A, B) ≫ ((TD.map (F.map x)).app (F.obj B) ≫ (TD.obj (F.obj A')).map (F.map y)) :=
  μ.hom.naturality ((x, y) : ((A, B) : C × C) ⟶ (A', B'))

/-- **The compatibility of `μ` with the associators is invariant under isomorphisms**: if it
holds at `(A', B', E')` it holds at any `(A, B, E)` isomorphic to it, the associators being
natural in their three variables. -/
theorem assoc_of_iso
    (αC : ∀ A B E : C, (TC.obj ((TC.obj A).obj B)).obj E ≅ (TC.obj A).obj ((TC.obj B).obj E))
    (αD : ∀ A B E : D, (TD.obj ((TD.obj A).obj B)).obj E ≅ (TD.obj A).obj ((TD.obj B).obj E))
    (hαC : ∀ {A A' B B' E E' : C} (a : A ⟶ A') (b : B ⟶ B') (e : E ⟶ E'),
      ((TC.map ((TC.map a).app B ≫ (TC.obj A').map b)).app E ≫
          (TC.obj ((TC.obj A').obj B')).map e) ≫ (αC A' B' E').hom =
        (αC A B E).hom ≫ (TC.map a).app ((TC.obj B).obj E) ≫
          (TC.obj A').map ((TC.map b).app E ≫ (TC.obj B').map e))
    (hαD : ∀ {A A' B B' E E' : D} (a : A ⟶ A') (b : B ⟶ B') (e : E ⟶ E'),
      ((TD.map ((TD.map a).app B ≫ (TD.obj A').map b)).app E ≫
          (TD.obj ((TD.obj A').obj B')).map e) ≫ (αD A' B' E').hom =
        (αD A B E).hom ≫ (TD.map a).app ((TD.obj B).obj E) ≫
          (TD.obj A').map ((TD.map b).app E ≫ (TD.obj B').map e))
    {A A' B B' E E' : C} (a : A ≅ A') (b : B ≅ B') (e : E ≅ E')
    (h : F.map (αC A' B' E').hom ≫ μ.hom.app (A', (TC.obj B').obj E') ≫
        (TD.obj (F.obj A')).map (μ.hom.app (B', E')) =
      μ.hom.app ((TC.obj A').obj B', E') ≫ (TD.map (μ.hom.app (A', B'))).app (F.obj E') ≫
        (αD (F.obj A') (F.obj B') (F.obj E')).hom) :
    F.map (αC A B E).hom ≫ μ.hom.app (A, (TC.obj B).obj E) ≫
        (TD.obj (F.obj A)).map (μ.hom.app (B, E)) =
      μ.hom.app ((TC.obj A).obj B, E) ≫ (TD.map (μ.hom.app (A, B))).app (F.obj E) ≫
        (αD (F.obj A) (F.obj B) (F.obj E)).hom := by
  let t : (TD.obj (F.obj A)).obj ((TD.obj (F.obj B)).obj (F.obj E)) ⟶
      (TD.obj (F.obj A')).obj ((TD.obj (F.obj B')).obj (F.obj E')) :=
    (TD.map (F.map a.hom)).app _ ≫
      (TD.obj (F.obj A')).map ((TD.map (F.map b.hom)).app _ ≫ (TD.obj (F.obj B')).map (F.map e.hom))
  have : IsIso t := by dsimp only [t]; infer_instance
  rw [← cancel_mono t]
  have hL : F.map (αC A B E).hom ≫ μ.hom.app (A, (TC.obj B).obj E) ≫
        (TD.obj (F.obj A)).map (μ.hom.app (B, E)) ≫ t =
      F.map ((TC.map ((TC.map a.hom).app B ≫ (TC.obj A').map b.hom)).app E ≫
          (TC.obj ((TC.obj A').obj B')).map e.hom) ≫
        F.map (αC A' B' E').hom ≫ μ.hom.app (A', (TC.obj B').obj E') ≫
          (TD.obj (F.obj A')).map (μ.hom.app (B', E')) := by
    symm
    calc _ = F.map (αC A B E).hom ≫
          F.map ((TC.map a.hom).app ((TC.obj B).obj E) ≫
            (TC.obj A').map ((TC.map b.hom).app E ≫ (TC.obj B').map e.hom)) ≫
          μ.hom.app (A', (TC.obj B').obj E') ≫ (TD.obj (F.obj A')).map (μ.hom.app (B', E')) := by
          rw [← F.map_comp_assoc, hαC, F.map_comp_assoc]
      _ = F.map (αC A B E).hom ≫ μ.hom.app (A, (TC.obj B).obj E) ≫
          ((TD.map (F.map a.hom)).app (F.obj ((TC.obj B).obj E)) ≫
            (TD.obj (F.obj A')).map (F.map ((TC.map b.hom).app E ≫ (TC.obj B').map e.hom))) ≫
          (TD.obj (F.obj A')).map (μ.hom.app (B', E')) := by
          rw [reassoc_of% (μ_hom_naturality₂ μ a.hom
            ((TC.map b.hom).app E ≫ (TC.obj B').map e.hom))]
          simp only [Category.assoc]
      _ = F.map (αC A B E).hom ≫ μ.hom.app (A, (TC.obj B).obj E) ≫
          (TD.map (F.map a.hom)).app (F.obj ((TC.obj B).obj E)) ≫
            (TD.obj (F.obj A')).map (F.map ((TC.map b.hom).app E ≫ (TC.obj B').map e.hom) ≫
              μ.hom.app (B', E')) := by
          rw [Category.assoc, ← (TD.obj (F.obj A')).map_comp]
      _ = F.map (αC A B E).hom ≫ μ.hom.app (A, (TC.obj B).obj E) ≫
          (TD.map (F.map a.hom)).app (F.obj ((TC.obj B).obj E)) ≫
            (TD.obj (F.obj A')).map (μ.hom.app (B, E) ≫
              ((TD.map (F.map b.hom)).app (F.obj E) ≫ (TD.obj (F.obj B')).map (F.map e.hom))) := by
          rw [μ_hom_naturality₂ μ b.hom e.hom]
      _ = _ := by
          rw [(TD.obj (F.obj A')).map_comp, ← NatTrans.naturality_assoc]
          rfl
  have hR : (μ.hom.app ((TC.obj A).obj B, E) ≫ (TD.map (μ.hom.app (A, B))).app (F.obj E) ≫
        (αD (F.obj A) (F.obj B) (F.obj E)).hom) ≫ t =
      F.map ((TC.map ((TC.map a.hom).app B ≫ (TC.obj A').map b.hom)).app E ≫
          (TC.obj ((TC.obj A').obj B')).map e.hom) ≫
        μ.hom.app ((TC.obj A').obj B', E') ≫ (TD.map (μ.hom.app (A', B'))).app (F.obj E') ≫
          (αD (F.obj A') (F.obj B') (F.obj E')).hom := by
    calc _ = μ.hom.app ((TC.obj A).obj B, E) ≫ (TD.map (μ.hom.app (A, B))).app (F.obj E) ≫
          ((TD.map ((TD.map (F.map a.hom)).app (F.obj B) ≫
              (TD.obj (F.obj A')).map (F.map b.hom))).app (F.obj E) ≫
            (TD.obj ((TD.obj (F.obj A')).obj (F.obj B'))).map (F.map e.hom)) ≫
          (αD (F.obj A') (F.obj B') (F.obj E')).hom := by
          dsimp only [t]
          rw [Category.assoc, Category.assoc, ← hαD]
      _ = μ.hom.app ((TC.obj A).obj B, E) ≫
          (TD.map (F.map ((TC.map a.hom).app B ≫ (TC.obj A').map b.hom) ≫
            μ.hom.app (A', B'))).app (F.obj E) ≫
          (TD.obj ((TD.obj (F.obj A')).obj (F.obj B'))).map (F.map e.hom) ≫
          (αD (F.obj A') (F.obj B') (F.obj E')).hom := by
          rw [μ_hom_naturality₂ μ a.hom b.hom]
          simp only [Functor.map_comp, NatTrans.comp_app, Category.assoc]
      _ = μ.hom.app ((TC.obj A).obj B, E) ≫
          ((TD.map (F.map ((TC.map a.hom).app B ≫ (TC.obj A').map b.hom))).app (F.obj E) ≫
            (TD.obj (F.obj ((TC.obj A').obj B'))).map (F.map e.hom)) ≫
          (TD.map (μ.hom.app (A', B'))).app (F.obj E') ≫
          (αD (F.obj A') (F.obj B') (F.obj E')).hom := by
          have hn := (TD.map (μ.hom.app (A', B'))).naturality (F.map e.hom)
          simp only [Functor.comp_obj, Functor.uncurry_obj_obj, Functor.prod_obj] at hn
          simp only [Functor.map_comp, NatTrans.comp_app, Category.assoc]
          rw [reassoc_of% hn]
      _ = _ := by
          rw [← Category.assoc (μ.hom.app _), ← μ_hom_naturality₂ μ
            ((TC.map a.hom).app B ≫ (TC.obj A').map b.hom) e.hom, Category.assoc]
  rw [Category.assoc, Category.assoc, hL, hR, h]

end Invariance

section Square

variable (O : D) (lam : TD.obj O ≅ 𝟭 D)
  (αC : ∀ A B E : C, (TC.obj ((TC.obj A).obj B)).obj E ≅ (TC.obj A).obj ((TC.obj B).obj E))
  (αD : ∀ A B E : D, (TD.obj ((TD.obj A).obj B)).obj E ≅ (TD.obj A).obj ((TD.obj B).obj E))

/-- **The projection formula at the unit**, `G O ⊗ N ⟶ G(O ⊗ F N) ≅ G F N`: the
projection-formula map followed by `G` of the left unitor. -/
def projectionUnitMap (N : C) : (TC.obj (G.obj O)).obj N ⟶ G.obj (F.obj N) :=
  adjunctionTensorMap adj (Functor.uncurry.obj TC) (Functor.uncurry.obj TD) μ.hom O N ≫
    G.map (lam.hom.app (F.obj N))

/-- The projection formula at the unit is invertible when the projection-formula map is. -/
private instance isIso_projectionUnitMap (N : C)
    [IsIso (adjunctionTensorMap adj (Functor.uncurry.obj TC) (Functor.uncurry.obj TD) μ.hom O N)] :
    IsIso (projectionUnitMap adj TC TD μ O lam N) := by
  unfold projectionUnitMap; infer_instance

/-- **The tensor–Hom diagonal with the factor on the left**,
`P ⊗ H_C(M, K) ⟶ H_C(M, P ⊗ K)`: the adjoint, for `- ⊗ M ⊣ H_C(M, -)`, of
`(P ⊗ H_C(M, K)) ⊗ M ≅ P ⊗ (H_C(M, K) ⊗ M) ⟶ P ⊗ K`. No commutativity constraint enters. -/
def leftTensorHomDiagonal (P M K : C) :
    (TC.obj P).obj ((HC.obj (op M)).obj K) ⟶ (HC.obj (op M)).obj ((TC.obj P).obj K) :=
  (adjC M).homEquiv _ _
    ((αC P ((HC.obj (op M)).obj K) M).hom ≫ (TC.obj P).map ((adjC M).counit.app K))

/-- **`G` of the pullback map of internal Homs against the tensor–Hom diagonal.** If `μ` is
compatible with the associators, `α_D` is natural in its first variable and the left unitor
satisfies the triangle identity `λ_A ⊗ B = λ_{A ⊗ B} ∘ α_D`, then
`ρ ≫ G φ ≫ c = δ ≫ H_C(M, ρ)` as maps `G O ⊗ H_C(M, K) ⟶ H_C(M, G F K)`. -/
theorem projectionUnitMap_comp_map_pullbackHomMap
    (hassoc : ∀ A B E : C, F.map (αC A B E).hom ≫ μ.hom.app (A, (TC.obj B).obj E) ≫
        (TD.obj (F.obj A)).map (μ.hom.app (B, E)) =
      μ.hom.app ((TC.obj A).obj B, E) ≫ (TD.map (μ.hom.app (A, B))).app (F.obj E) ≫
        (αD (F.obj A) (F.obj B) (F.obj E)).hom)
    (hαD : ∀ {A A' : D} (a : A ⟶ A') (B E : D),
      (TD.map ((TD.map a).app B)).app E ≫ (αD A' B E).hom =
        (αD A B E).hom ≫ (TD.map a).app ((TD.obj B).obj E))
    (hunit : ∀ A B : D,
      (TD.map (lam.hom.app A)).app B = (αD O A B).hom ≫ lam.hom.app ((TD.obj A).obj B))
    (M K : C) (μR : TC.flip.obj M ⋙ F ≅ F ⋙ TD.flip.obj (F.obj M))
    (hμR : ∀ T, μR.hom.app T = μ.hom.app (T, M)) :
    projectionUnitMap adj TC TD μ O lam ((HC.obj (op M)).obj K) ≫
        G.map (pullbackHomMap TC TD μ HC HD adjC adjD M K) ≫
          (conjugateIsoEquiv (adj.comp (adjD (F.obj M))) ((adjC M).comp adj) μR).hom.app
            (F.obj K) =
      leftTensorHomDiagonal TC HC adjC αC (G.obj O) M K ≫
        (HC.obj (op M)).map (projectionUnitMap adj TC TD μ O lam K) := by
  apply ((adjC M).homEquiv _ _).symm.injective
  rw [Adjunction.homEquiv_naturality_left_symm, Adjunction.homEquiv_naturality_left_symm,
    Adjunction.homEquiv_naturality_right_symm,
    homEquiv_symm_conjugateIsoEquiv_hom_app adj TC TD μ HC HD adjC adjD M μR hμR,
    leftTensorHomDiagonal, Equiv.symm_apply_apply]
  have n1 := adjunctionTensorMap_natural adj (Functor.uncurry.obj TC) (Functor.uncurry.obj TD)
    μ.hom (pullbackHomMap TC TD μ HC HD adjC adjD M K) (𝟙 M)
  have n2 := adjunctionTensorMap_natural adj (Functor.uncurry.obj TC) (Functor.uncurry.obj TD)
    μ.hom (lam.hom.app (F.obj ((HC.obj (op M)).obj K))) (𝟙 M)
  have n3 := adjunctionTensorMap_natural adj (Functor.uncurry.obj TC) (Functor.uncurry.obj TD)
    μ.hom (𝟙 O) ((adjC M).counit.app K)
  have hφ : (TD.map (pullbackHomMap TC TD μ HC HD adjC adjD M K)).app (F.obj M) ≫
      (adjD (F.obj M)).counit.app (F.obj K) =
        μ.inv.app ((HC.obj (op M)).obj K, M) ≫ F.map ((adjC M).counit.app K) := by
    have h := ((adjD (F.obj M)).homEquiv _ _).symm_apply_apply
      (μ.inv.app ((HC.obj (op M)).obj K, M) ≫ F.map ((adjC M).counit.app K))
    rw [Adjunction.homEquiv_counit] at h
    exact h
  have pa := adjunctionTensorMap_assoc adj TC TD μ αC αD hassoc hαD O
    ((HC.obj (op M)).obj K) M
  have hu := hunit (F.obj ((HC.obj (op M)).obj K)) (F.obj M)
  have l2 := lam.hom.naturality (F.map ((adjC M).counit.app K))
  simp only [Functor.comp_obj, Functor.prod_obj, Functor.uncurry_obj_obj, Functor.uncurry_obj_map,
    Functor.map_id, Category.comp_id, Category.id_comp, NatTrans.id_app, Functor.id_obj,
    Functor.id_map] at n1 n2 n3 pa hu l2
  simp only [projectionUnitMap, Functor.flip_obj_map, Functor.map_comp, NatTrans.comp_app,
    Category.assoc]
  rw [reassoc_of% n1, ← G.map_comp, hφ, reassoc_of% n2, ← G.map_comp, hu, Category.assoc,
    G.map_comp, reassoc_of% pa, reassoc_of% n3]
  simp only [← G.map_comp]
  simp only [Functor.flip_obj_obj, Functor.comp_obj, Functor.uncurry_obj_obj,
    Functor.prod_obj] at l2 ⊢
  rw [l2]
  have l1 := lam.hom.naturality (μ.hom.app ((HC.obj (op M)).obj K, M))
  simp only [Functor.comp_obj, Functor.uncurry_obj_obj, Functor.prod_obj, Functor.id_obj,
    Functor.id_map] at l1
  rw [reassoc_of% l1, Iso.hom_inv_id_app_assoc]

/-- **`G φ` is invertible when the projection formula at the unit and the diagonal are**, under
the coherence hypotheses of `projectionUnitMap_comp_map_pullbackHomMap`. -/
theorem isIso_map_pullbackHomMap
    (hassoc : ∀ A B E : C, F.map (αC A B E).hom ≫ μ.hom.app (A, (TC.obj B).obj E) ≫
        (TD.obj (F.obj A)).map (μ.hom.app (B, E)) =
      μ.hom.app ((TC.obj A).obj B, E) ≫ (TD.map (μ.hom.app (A, B))).app (F.obj E) ≫
        (αD (F.obj A) (F.obj B) (F.obj E)).hom)
    (hαD : ∀ {A A' : D} (a : A ⟶ A') (B E : D),
      (TD.map ((TD.map a).app B)).app E ≫ (αD A' B E).hom =
        (αD A B E).hom ≫ (TD.map a).app ((TD.obj B).obj E))
    (hunit : ∀ A B : D,
      (TD.map (lam.hom.app A)).app B = (αD O A B).hom ≫ lam.hom.app ((TD.obj A).obj B))
    (M K : C)
    (hH : IsIso (adjunctionTensorMap adj (Functor.uncurry.obj TC) (Functor.uncurry.obj TD) μ.hom
      O ((HC.obj (op M)).obj K)))
    (hK : IsIso (adjunctionTensorMap adj (Functor.uncurry.obj TC) (Functor.uncurry.obj TD) μ.hom
      O K))
    (hδ : IsIso (leftTensorHomDiagonal TC HC adjC αC (G.obj O) M K)) :
    IsIso (G.map (pullbackHomMap TC TD μ HC HD adjC adjD M K)) := by
  let μR : TC.flip.obj M ⋙ F ≅ F ⋙ TD.flip.obj (F.obj M) :=
    NatIso.ofComponents (fun T => μ.app (T, M)) fun {T T'} t => by
      have h := μ.hom.naturality (X := (T, M)) (Y := (T', M)) (t ×ₘ 𝟙 M)
      simp only [Functor.comp_obj, Functor.prod_obj, Functor.uncurry_obj_obj, Functor.comp_map,
        Functor.uncurry_obj_map, Functor.prod_map, Functor.map_id, Category.comp_id] at h
      simpa using h
  have h := projectionUnitMap_comp_map_pullbackHomMap adj TC TD μ HC HD adjC adjD O lam αC αD
    hassoc hαD hunit M K μR (fun _ => rfl)
  have : IsIso (G.map (pullbackHomMap TC TD μ HC HD adjC adjD M K) ≫
      (conjugateIsoEquiv (adj.comp (adjD (F.obj M))) ((adjC M).comp adj) μR).hom.app
        (F.obj K)) := IsIso.of_isIso_fac_left h
  exact IsIso.of_isIso_comp_right _
    ((conjugateIsoEquiv (adj.comp (adjD (F.obj M))) ((adjC M).comp adj) μR).hom.app (F.obj K))

end Square

end CategoryTheory.PullbackInternalHom

end
