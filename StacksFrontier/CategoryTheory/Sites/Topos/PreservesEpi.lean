module

public import Mathlib.CategoryTheory.Sites.Continuous
public import Mathlib.CategoryTheory.Sites.LocallySurjective

/-! # Pushforward along a continuous functor preserves epimorphisms

## Main results

* `Hypothesis`: the section-lifting form of the hypothesis of Stacks 04D7.
* `preservesEpi`: under that hypothesis the pushforward
  `u.sheafPushforwardContinuous _ J K` preserves epimorphisms (Stacks 04D7).

Tags covered: 04D7.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u₁ v₁ u₂ v₂

/-- Section-lifting form of the Stacks Tag 04D7 hypothesis for a continuous
functor `u : C ⥤ D` between sites `(C, J)` and `(D, K)`.

This is the operational content of the classical Stacks 04D7 condition:
for every `K`-locally surjective morphism `η : F ⟶ G` of sheaves of types
on `(D, K)`, every object `U : C`, and every section `s` of `G` over `u(U)`,
there exists a `J`-covering family `{f i : W i ⟶ U}_{i : I}` of `U` and
sections `τ i` of `F` over `u (W i)` such that `η` sends `τ i` to the
restriction of `s` along `u (f i)`.

This reformulates the categorical factorization condition from Stacks 04D7
(that for every `K`-cover `{V j → u(U)}` there exists a `J`-cover
`{W i → U}` such that `∐ h_{u(W i)}^# → h_{u(U)}^#` factors through
`∐ h_{V j}^# → h_{u(U)}^#`) in a form usable directly with Mathlib's
`Sheaf.IsLocallySurjective` API. The two formulations are equivalent for
sheaves of types via Yoneda and the universal property of sheafification:
the categorical factorization condition produces, for every section `s`
witnessing local surjectivity, the section-lifts above; conversely, given
section-lifts one recovers the factorization map from a sheafified
coproduct of representables. -/
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

/-- **Stacks 04D7.**

Let `u : C ⥤ D` be a continuous functor between sites `(C, J)` and
`(D, K)`. Assume `u` satisfies the section-lifting hypothesis of Stacks
04D7 (`Hypothesis u J K`): for every `K`-locally surjective morphism of
type-valued sheaves on `(D, K)` and every section on `u(U)`, sections lift
locally on a `J`-cover of `U`. Then the pushforward functor
`u.sheafPushforwardContinuous (Type max u₂ v₂) J K : Sheaf K _ ⥤ Sheaf J _`
preserves epimorphisms, i.e. transforms surjective maps of sheaves into
surjective maps of sheaves. -/
@[stacks 04D7]
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
