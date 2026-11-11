module

public import Mathlib.CategoryTheory.Sites.Continuous
public import Mathlib.CategoryTheory.Sites.LocallySurjective

/-! # Pushforward along a continuous functor preserves epimorphisms

## Main results

* `Hypothesis`, `preservesEpi`: an auxiliary section-lifting condition, which
  is the local surjectivity of `u_* η` written out, and the (formal) fact that
  it makes the pushforward preserve epimorphisms.

Stacks 04D7 itself, under its factorization hypothesis, is
`isLocallySurjective_sheafPushforwardContinuous_map` in
`StacksFrontier.CategoryTheory.Sites.Topos.PreservesEpiFactorization`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u₁ v₁ u₂ v₂

/-- An auxiliary section-lifting condition on a continuous functor
`u : C ⥤ D` between sites `(C, J)` and `(D, K)`: for every `K`-locally
surjective morphism `η : F ⟶ G` of sheaves of types on `(D, K)`, every object
`U : C`, and every section `s` of `G` over `u(U)`, there exists a `J`-covering
family `{f i : W i ⟶ U}_{i : I}` of `U` and sections `τ i` of `F` over
`u (W i)` such that `η` sends `τ i` to the restriction of `s` along
`u (f i)`.

This is the local surjectivity of every `u_* η` written out on sections; it is
not the hypothesis of Stacks 04D7, which is `FactorizationCondition`. The
implication from Stacks' condition to this one is
`hypothesis_of_factorizationCondition`. -/
def Hypothesis
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    (u : C ⥤ D) (J : GrothendieckTopology C) (K : GrothendieckTopology D) :
    Prop :=
  ∀ {F G : Sheaf K (Type max u₂ v₂)} (η : F ⟶ G)
    [Sheaf.IsLocallySurjective η]
    (U : C) (s : G.obj.obj (op (u.obj U))),
    ∃ (I : Type max u₂ v₂) (W : I → C) (f : ∀ i, W i ⟶ U),
      Sieve.ofArrows W f ∈ J U ∧
      ∀ i, ∃ τ : F.obj.obj (op (u.obj (W i))),
        η.hom.app (op (u.obj (W i))) τ
          = G.obj.map (u.map (f i)).op s

/-- Let `u : C ⥤ D` be a continuous functor between sites `(C, J)` and
`(D, K)` satisfying the auxiliary section-lifting condition `Hypothesis u J K`.
Then the pushforward functor
`u.sheafPushforwardContinuous (Type max u₂ v₂) J K : Sheaf K _ ⥤ Sheaf J _`
preserves epimorphisms. Since `Hypothesis u J K` is the local surjectivity of
the pushforwards of locally surjective maps, this is a formal step; the
statement of Stacks 04D7, under its own hypothesis, is
`isLocallySurjective_sheafPushforwardContinuous_map`. -/
theorem preservesEpi
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    (u : C ⥤ D) (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    [u.IsContinuous J K]
    (hyp : Hypothesis u J K) :
    (u.sheafPushforwardContinuous (Type max u₂ v₂) J K).PreservesEpimorphisms := by
  refine ⟨fun {F G} η hη => ?_⟩
  have : Sheaf.IsLocallySurjective η :=
    (Sheaf.isLocallySurjective_iff_epi η).mpr hη
  -- Local surjectivity of `u_*η` follows from the section-lifting hypothesis: over each
  -- `U : C` the hypothesis supplies a `J`-cover of `U` along which sections of `F` over
  -- `u (W i)` restrict to the right thing under `η`.
  have hSurj : Presheaf.IsLocallySurjective J
      ((u.sheafPushforwardContinuous (Type max u₂ v₂) J K).map η).hom := by
    refine ⟨?_⟩
    intro U s
    -- `s : (u_*G).obj.obj (op U)` is definitionally `G.obj.obj (op (u.obj U))`, since
    -- `sheafPushforwardContinuous` is precomposition with `u.op`.
    change G.obj.obj (op (u.obj U)) at s
    obtain ⟨I, W, f, hWf, hτ⟩ := hyp η U s
    refine J.superset_covering ?_ hWf
    intro V g hg
    obtain ⟨i, a, rfl⟩ := (Sieve.mem_ofArrows_iff W f g).1 hg
    obtain ⟨τ, hτi⟩ := hτ i
    refine ⟨F.obj.map (u.map a).op τ, ?_⟩
    have happ := congrArg (fun φ => φ τ) (η.hom.naturality (u.map a).op)
    simp only [types_comp_apply] at happ
    rw [show (((u.sheafPushforwardContinuous (Type max u₂ v₂) J K).map η).hom.app (op V)
            : ((u.sheafPushforwardContinuous _ J K).obj F).obj.obj (op V) → _)
          = η.hom.app (op (u.obj V)) from rfl,
        happ, hτi,
        show (((u.sheafPushforwardContinuous (Type max u₂ v₂) J K).obj G).obj.map (a ≫ f i).op
            : ((u.sheafPushforwardContinuous _ J K).obj G).obj.obj (op U) → _)
          = G.obj.map (u.map (a ≫ f i)).op from rfl]
    rw [u.map_comp, op_comp, Functor.map_comp_apply]
  exact Sheaf.epi_of_isLocallySurjective _
