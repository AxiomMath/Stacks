module

public import StacksFrontier.CategoryTheory.Sites.Topos.PreservesEpi
public import Mathlib.CategoryTheory.Sites.Limits

/-! # Stacks 04D7: the factorization criterion for `f_*` to preserve surjections

## Main definitions

* `sheafifiedYoneda K`: the functor `V ↦ h_V^#`.
* `FactorizationCondition u J K`: the hypothesis of Stacks 04D7: for every
  covering `{V j → u(U)}` there is a covering `{W i → U}` such that
  `∐ h_{u(W i)}^# → h_{u(U)}^#` factors through `∐ h_{V j}^# → h_{u(U)}^#`.

## Main results

* `hypothesis_of_factorizationCondition`: the factorization condition implies
  the section-lifting condition `Hypothesis`.
* `isLocallySurjective_sheafPushforwardContinuous_map`: under the
  factorization condition, `u.sheafPushforwardContinuous _ J K` transforms
  surjective maps of sheaves into surjective maps of sheaves (Stacks 04D7).

Tags covered: 04D7.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

section Factorization

universe w₁ w₂

variable {C D : Type w₁} [Category.{w₂} C] [Category.{w₂} D]

/-- The functor `V ↦ h_V^#` sending an object of `D` to the sheafification of
the presheaf of sets it represents (with the universe raised to
`max w₁ w₂`, so that it lands in the category of sheaves used by
`sheafPushforwardContinuous`). -/
noncomputable abbrev sheafifiedYoneda (K : GrothendieckTopology D) :
    D ⥤ Sheaf K (Type (max w₁ w₂)) :=
  uliftYoneda.{w₁} ⋙ presheafToSheaf K (Type (max w₁ w₂))

/-- Yoneda's lemma for sheafified representables: maps `h_X^# ⟶ F` to a sheaf
`F` are the sections of `F` over `X`. -/
noncomputable def sheafifiedYonedaEquiv (K : GrothendieckTopology D) (X : D)
    (F : Sheaf K (Type (max w₁ w₂))) :
    ((sheafifiedYoneda K).obj X ⟶ F) ≃ F.obj.obj (op X) :=
  ((sheafificationAdjunction K (Type (max w₁ w₂))).homEquiv _ _).trans uliftYonedaEquiv.{w₁}

lemma sheafifiedYonedaEquiv_comp (K : GrothendieckTopology D) {X : D}
    {F G : Sheaf K (Type (max w₁ w₂))} (ψ : (sheafifiedYoneda K).obj X ⟶ F) (η : F ⟶ G) :
    sheafifiedYonedaEquiv K X G (ψ ≫ η) = η.hom.app _ (sheafifiedYonedaEquiv K X F ψ) := by
  simp only [sheafifiedYonedaEquiv, Equiv.trans_apply, Adjunction.homEquiv_naturality_right]
  rfl

lemma sheafifiedYonedaEquiv_map_comp (K : GrothendieckTopology D) {X Y : D} (g : Y ⟶ X)
    {F : Sheaf K (Type (max w₁ w₂))} (ψ : (sheafifiedYoneda K).obj X ⟶ F) :
    sheafifiedYonedaEquiv K Y F ((sheafifiedYoneda K).map g ≫ ψ) =
      F.obj.map g.op (sheafifiedYonedaEquiv K X F ψ) := by
  simp only [sheafifiedYonedaEquiv, Equiv.trans_apply, Functor.comp_map,
    Adjunction.homEquiv_naturality_left]
  rw [uliftYonedaEquiv_naturality]
  rfl

/-- The hypothesis of Stacks 04D7 on a continuous functor `u : C ⥤ D` between
sites `(C, J)` and `(D, K)`: for every object `U` of `C` and every covering
`{g j : V j ⟶ u(U)}` in `D` there is a covering `{f i : W i ⟶ U}` in `C`
such that the map of sheaves `∐ h_{u(W i)}^# → h_{u(U)}^#` factors through
the map of sheaves `∐ h_{V j}^# → h_{u(U)}^#`.

Coverings are families whose generated sieve is covering. The families
`{V j}` range over index types in `Type (max w₁ w₂)`, which suffices to
present every covering sieve of `u(U)`. -/
def FactorizationCondition (u : C ⥤ D) (J : GrothendieckTopology C)
    (K : GrothendieckTopology D) : Prop :=
  ∀ (U : C) (ι : Type (max w₁ w₂)) (V : ι → D) (g : ∀ j, V j ⟶ u.obj U),
    Sieve.ofArrows V g ∈ K (u.obj U) →
    ∃ (I : Type (max w₁ w₂)) (W : I → C) (f : ∀ i, W i ⟶ U), Sieve.ofArrows W f ∈ J U ∧
      ∃ φ : (∐ fun i => (sheafifiedYoneda K).obj (u.obj (W i))) ⟶
          ∐ fun j => (sheafifiedYoneda K).obj (V j),
        φ ≫ Sigma.desc (fun j => (sheafifiedYoneda K).map (g j)) =
          Sigma.desc (fun i => (sheafifiedYoneda K).map (u.map (f i)))

/-- The lifting step of the proof of Stacks 04D7: if `∐ h_{W i}^# → h_X^#`
factors through `∐ h_{V j}^# → h_X^#`, and the restrictions of a section `s`
of `G` to the `V j` lift along `η : F ⟶ G`, then so do its restrictions to the
`W i`. -/
lemma exists_lift_of_sigmaDesc_factorization (K : GrothendieckTopology D) {X : D}
    {ι I : Type (max w₁ w₂)} (V : ι → D) (g : ∀ j, V j ⟶ X) (W : I → D) (f : ∀ i, W i ⟶ X)
    (φ : (∐ fun i => (sheafifiedYoneda K).obj (W i)) ⟶ ∐ fun j => (sheafifiedYoneda K).obj (V j))
    (hφ : φ ≫ Sigma.desc (fun j => (sheafifiedYoneda K).map (g j)) =
      Sigma.desc (fun i => (sheafifiedYoneda K).map (f i)))
    {F G : Sheaf K (Type (max w₁ w₂))} (η : F ⟶ G) (s : G.obj.obj (op X))
    (t : ∀ j, F.obj.obj (op (V j))) (ht : ∀ j, η.hom.app _ (t j) = G.obj.map (g j).op s)
    (i : I) : ∃ τ : F.obj.obj (op (W i)), η.hom.app _ τ = G.obj.map (f i).op s := by
  let σ : (∐ fun j => (sheafifiedYoneda K).obj (V j)) ⟶ F :=
    Sigma.desc fun j => (sheafifiedYonedaEquiv K (V j) F).symm (t j)
  have hσ : σ ≫ η = Sigma.desc (fun j => (sheafifiedYoneda K).map (g j)) ≫
      (sheafifiedYonedaEquiv K X G).symm s := by
    refine Sigma.hom_ext _ _ fun j => ?_
    rw [Sigma.ι_desc_assoc, Sigma.ι_desc_assoc]
    apply (sheafifiedYonedaEquiv K (V j) G).injective
    rw [sheafifiedYonedaEquiv_comp, Equiv.apply_symm_apply, ht,
      sheafifiedYonedaEquiv_map_comp, Equiv.apply_symm_apply]
  refine ⟨sheafifiedYonedaEquiv K (W i) F
    (Sigma.ι (fun i => (sheafifiedYoneda K).obj (W i)) i ≫ φ ≫ σ), ?_⟩
  have key : Sigma.ι (fun i => (sheafifiedYoneda K).obj (W i)) i ≫ φ ≫ σ ≫ η =
      (sheafifiedYoneda K).map (f i) ≫ (sheafifiedYonedaEquiv K X G).symm s := by
    rw [hσ, ← Category.assoc φ, hφ, Sigma.ι_desc_assoc]
  rw [← sheafifiedYonedaEquiv_comp, Category.assoc, Category.assoc, key,
    sheafifiedYonedaEquiv_map_comp, Equiv.apply_symm_apply]

/-- The factorization condition of Stacks 04D7 implies the section-lifting
condition `Hypothesis`: this is the argument of the proof of Stacks 04D7
(Yoneda, the universal property of sheafification and of coproducts). -/
theorem hypothesis_of_factorizationCondition (u : C ⥤ D) (J : GrothendieckTopology C)
    (K : GrothendieckTopology D) (h : FactorizationCondition u J K) : Hypothesis u J K := by
  intro F G η _ U s
  let S := Presheaf.imageSieve η.hom s
  have hS : S ∈ K (u.obj U) := Presheaf.imageSieve_mem K η.hom (U := op (u.obj U)) s
  let ι : Type (max w₁ w₂) := Σ V : D, {g : V ⟶ u.obj U // S g}
  have hι : Sieve.ofArrows (fun j : ι => j.1) (fun j => j.2.1) ∈ K (u.obj U) :=
    K.superset_covering (fun V g hg => Sieve.ofArrows_mk _ _ (⟨V, g, hg⟩ : ι)) hS
  obtain ⟨I, W, f, hW, φ, hφ⟩ := h U ι (fun j => j.1) (fun j => j.2.1) hι
  choose t ht using fun j : ι => j.2.2
  exact ⟨I, W, f, hW, exists_lift_of_sigmaDesc_factorization K (fun j : ι => j.1)
    (fun j => j.2.1) (fun i => u.obj (W i)) (fun i => u.map (f i)) φ hφ η s t ht⟩

/-- Let `u : C ⥤ D` be a continuous functor between sites `(C, J)` and
`(D, K)` (the continuous functor underlying a morphism of sites
`f : (D, K) → (C, J)`). Assume that for every object `U` of `C` and every
covering `{V j ⟶ u(U)}` in `D` there is a covering `{W i ⟶ U}` in `C` such
that `∐ h_{u(W i)}^# → h_{u(U)}^#` factors through `∐ h_{V j}^# → h_{u(U)}^#`
(`FactorizationCondition`). Then `f_* = u.sheafPushforwardContinuous _ J K`
transforms surjective maps of sheaves of sets into surjective maps of
sheaves. -/
@[stacks 04D7 "Stated for a continuous functor `u`; the exactness of `u_s`
making it a morphism of sites is not used. Coverings are families generating
a covering sieve, and surjective maps of sheaves are the locally surjective
ones."]
theorem isLocallySurjective_sheafPushforwardContinuous_map (u : C ⥤ D)
    (J : GrothendieckTopology C) (K : GrothendieckTopology D) [u.IsContinuous J K]
    (h : FactorizationCondition u J K) {F G : Sheaf K (Type (max w₁ w₂))} (a : F ⟶ G)
    [Sheaf.IsLocallySurjective a] :
    Sheaf.IsLocallySurjective ((u.sheafPushforwardContinuous (Type (max w₁ w₂)) J K).map a) := by
  have := preservesEpi u J K (hypothesis_of_factorizationCondition u J K h)
  have : Epi a := (Sheaf.isLocallySurjective_iff_epi a).mp inferInstance
  exact (Sheaf.isLocallySurjective_iff_epi _).mpr inferInstance

/-- Under the hypothesis of Stacks 04D7, the pushforward
`u.sheafPushforwardContinuous _ J K` preserves epimorphisms. -/
theorem preservesEpimorphisms_sheafPushforwardContinuous_of_factorizationCondition
    (u : C ⥤ D) (J : GrothendieckTopology C) (K : GrothendieckTopology D) [u.IsContinuous J K]
    (h : FactorizationCondition u J K) :
    (u.sheafPushforwardContinuous (Type (max w₁ w₂)) J K).PreservesEpimorphisms :=
  preservesEpi u J K (hypothesis_of_factorizationCondition u J K h)

end Factorization
