module

public import StacksFrontier.CategoryTheory.Sites.Stackification.StageThreeStack
public import StacksFrontier.CategoryTheory.Sites.Stackification.StageTwoMorSheaf

/-!
# Separatedness of the morphism presheaves of the third stage

The third stage of the construction of the stackification of a fibred category adjoins, to a
fibred category `p` whose morphism presheaves are already sheaves, the objects that descent data
prescribe. Its morphisms `CategoryTheory.Functor.DescentMor` are families of morphisms of descent
data defined on a covering sieve, two such being identified when they agree on a common covering
refinement. That is the same shape as the second stage, and the separatedness half of the sheaf
condition is proved here in the same way: the criterion
`CategoryTheory.Functor.isMorSheaf_of_locallyEqual_of_amalgamation` asks for
`CategoryTheory.Functor.LocallyEqual` to imply equality, and that is
`CategoryTheory.Functor.locallyEqual_descentPairProj_iff`.

The bridge from the hypothesis on `p` — that its *locally equal* morphisms are equal — to the
statement needed about the morphisms of a fibre is
`CategoryTheory.Functor.fiber_hom_eq_of_pullbackFiberHom_locally_eq`: two morphisms of a fibre
whose base changes along the members of a covering sieve agree are equal. Unlike
`CategoryTheory.Functor.eq_of_pullbackFiberHom_locally_eq` it does not presuppose the sheaf
condition, only separatedness of the morphisms of the total category, which is what the first two
stages supply.

## Main results

* `CategoryTheory.Functor.locallyEqual_fiberInclusion_map_of_pullbackFiberHom_eq` and
  `CategoryTheory.Functor.fiber_hom_eq_of_pullbackFiberHom_locally_eq`, the bridge;
* `CategoryTheory.Functor.locallyEqual_descentPairProj_iff`, the separatedness half of the sheaf
  condition for the morphism presheaves of the third stage;
* `CategoryTheory.Functor.locallyEqual_stageThreeProj_iff`, the same for the composite of the three
  stages;
* `CategoryTheory.Functor.isMorSheaf_descentPairProj_of_amalgamation`, which reduces condition (2)
  of Stacks 026F for the third stage to the gluing half alone. It is to be applied with `p` the
  second stage, where the hypothesis on locally equal morphisms is
  `CategoryTheory.Functor.locallyEqual_stageTwoProj_iff`.

## Obligations that remain before Stacks 02ZN

This file carries no `@[stacks 02ZN]` tag and nothing here may be read as claiming Stacks 02ZN, or
that the morphism presheaves of the third stage are sheaves. What is proved here is only the
separatedness half. The gluing half — the analogue of
`CategoryTheory.Functor.exists_amalgamation_stageTwoProj` for
`CategoryTheory.Functor.descentPairProj` — is not proved here;
`CategoryTheory.Functor.isMorSheaf_descentPairProj_of_amalgamation` takes it as a hypothesis and so
records exactly what this file owes. It is discharged in `StageThreeGluing.lean`, by
`CategoryTheory.Functor.exists_amalgamation_descentPairProj`, and condition (2) of Stacks 026F for
the third stage is `CategoryTheory.Functor.isMorSheaf_descentPairProj` there.

A warning about a route that does *not* work. It is tempting to argue that the sheaf condition for
the morphism presheaves of the third stage follows from full faithfulness of
`CategoryTheory.Functor.toDescentPair` together with the local essential surjectivity proved in
`StageThreeStack.lean`, on the grounds that being a sheaf is a local condition. It is not: for the
category of elements of the presheaf on the two-point discrete space with two sections over the
whole space and one over each point, `Mor(x, y)` is empty over the whole space and terminal over
each point, so it is a sheaf on each member of a covering without being a sheaf. What is true is
`CategoryTheory.Presieve.isSheafFor_trans`, and its first hypothesis is the sheaf condition for the
covering sieve itself — precisely the leg that locality does not supply. The gluing half therefore
has to be proved for `CategoryTheory.Functor.DescentMor` directly, exactly as
`CategoryTheory.Functor.exists_amalgamation_morPlusProj` was for the second stage; with
separatedness in hand, that is the only remaining input to
`CategoryTheory.Functor.isMorSheaf_of_locallyEqual_of_amalgamation`.
-/

@[expose] public section

-- `Functor.Fiber` and its inclusion are Mathlib definitions that are not implicit-reducible;
-- the composites below cross from a fibre into the total category through them.
attribute [local implicit_reducible] CategoryTheory.Functor.Fiber
  CategoryTheory.Functor.Fiber.fiberInclusion

universe v₁ u₁ v₂ u₂

namespace CategoryTheory.Functor

open CategoryTheory Category

variable {𝒮 : Type u₁} [Category.{v₁} 𝒮] {𝒳 : Type u₂} [Category.{v₂} 𝒳]
variable {p : 𝒳 ⥤ 𝒮} [p.IsFibered] {J : GrothendieckTopology 𝒮}

/-! ### From separatedness in the total category to separatedness in a fibre -/

/-- Two morphisms of the fibre over `V` whose base changes along the members of a covering sieve of
`V` agree are locally equal in the total category: every morphism into their common source lying
over a member of the sieve factors through the chosen cartesian lift. -/
theorem locallyEqual_fiberInclusion_map_of_pullbackFiberHom_eq {V : 𝒮} {a b : p.Fiber V}
    {m n : a ⟶ b} {T : Sieve V} (hT : T ∈ J V)
    (h : ∀ ⦃V' : 𝒮⦄ (e : V' ⟶ V), T.arrows e → pullbackFiberHom m e = pullbackFiberHom n e) :
    p.LocallyEqual J (Fiber.fiberInclusion.map m) (Fiber.fiberInclusion.map n) := by
  have ha : p.obj a.1 = V := a.2
  refine ⟨?_, T.pullback (eqToHom ha), J.pullback_stable _ hT, ?_⟩
  · rw [IsHomLift.fac' p (𝟙 V) (Fiber.fiberInclusion.map m),
      IsHomLift.fac' p (𝟙 V) (Fiber.fiberInclusion.map n)]
  · intro w φ hφ
    have hlift : p.IsHomLift (p.map φ ≫ eqToHom ha) φ :=
      IsHomLift.of_fac' p _ φ rfl ha (by simp)
    rw [← IsStronglyCartesian.fac p (p.map φ ≫ eqToHom ha)
        (IsPreFibered.pullbackMap a.2 (p.map φ ≫ eqToHom ha)) (id_comp _).symm φ,
      assoc, assoc, ← pullbackFiberHom_fac m (p.map φ ≫ eqToHom ha),
      ← pullbackFiberHom_fac n (p.map φ ≫ eqToHom ha), h _ hφ]

/-- **Two morphisms of a fibre whose base changes along the members of a covering sieve agree are
equal**, as soon as locally equal morphisms of the total category are equal. This is the
separatedness statement that the first two stages of the construction of the stackification make
available; `CategoryTheory.Functor.eq_of_pullbackFiberHom_locally_eq` is the same conclusion drawn
instead from the full sheaf condition. -/
theorem fiber_hom_eq_of_pullbackFiberHom_locally_eq
    (hsep : ∀ {x y : 𝒳} {a b : x ⟶ y}, p.LocallyEqual J a b → a = b)
    {V : 𝒮} {a b : p.Fiber V} {m n : a ⟶ b} {T : Sieve V} (hT : T ∈ J V)
    (h : ∀ ⦃V' : 𝒮⦄ (e : V' ⟶ V), T.arrows e → pullbackFiberHom m e = pullbackFiberHom n e) :
    m = n :=
  Fiber.hom_ext (hsep (locallyEqual_fiberInclusion_map_of_pullbackFiberHom_eq hT h))

/-! ### Separatedness of the morphism presheaves of the third stage -/

/-- The morphism that the canonical morphism from a pullback of a descent pair attaches to an
arrow of its sieve is the identity: the two objects of the fibre it connects are the same. -/
theorem pullbackHom_map_eq_id (A : DescentPair p J) {U₀ : 𝒮} (v : U₀ ⟶ A.pt) {V : 𝒮}
    (f : V ⟶ U₀) (hf : (A.sieve.pullback v).arrows f) (hg : A.sieve.arrows (f ≫ v)) :
    (DescentPairData.pullbackHom A v).hom.map f hf hg rfl = 𝟙 _ := rfl

/-- **If locally equal morphisms of `𝒳` are equal, the same holds in the third stage.** This is the
separatedness half of the sheaf condition for the morphism presheaves of
`CategoryTheory.Functor.descentPairProj`, and the first of the two hypotheses of
`CategoryTheory.Functor.isMorSheaf_of_locallyEqual_of_amalgamation`.

Two morphism data of descent pairs are identified when they agree on a covering sieve, so it
suffices to test them against the canonical morphisms from the pullbacks of the source. Testing
against the one at an arrow `f` says that the two data agree, after a further covering, at every
arrow `e ≫ f`; the compatibility of a morphism datum with the gluing isomorphisms turns that into
agreement of the base changes along `e` of the two morphisms attached to `f` itself, and
`CategoryTheory.Functor.fiber_hom_eq_of_pullbackFiberHom_locally_eq` then identifies them. -/
theorem locallyEqual_descentPairProj_iff
    (hsep : ∀ {x y : 𝒳} {a b : x ⟶ y}, p.LocallyEqual J a b → a = b)
    {A B : DescentPair p J} (F G : A ⟶ B) :
    (p.descentPairProj J).LocallyEqual J F G ↔ F = G := by
  refine ⟨fun hFG ↦ ?_, locallyEqual_of_eq⟩
  obtain ⟨X, rfl⟩ := DescentMor.exists_rep F
  obtain ⟨Y, rfl⟩ := DescentMor.exists_rep G
  obtain ⟨hbase, S, hS, hagree⟩ := hFG
  rw [DescentMor.mk_eq_iff]
  refine ⟨hbase, S ⊓ (X.hom.sieve ⊓ Y.hom.sieve),
    J.intersection_covering hS (J.intersection_covering X.hom.sieve_mem Y.hom.sieve_mem),
    fun _ _ hf ↦ hf.2.1, fun _ _ hf ↦ hf.2.2, ?_⟩
  intro V f hf g hg h h'
  have key : DescentMor.mk ((DescentPairData.pullbackHom A f).comp X) =
      DescentMor.mk ((DescentPairData.pullbackHom A f).comp Y) :=
    hagree (DescentMor.mk (DescentPairData.pullbackHom A f)) hf.1
  rw [DescentMor.mk_eq_iff] at key
  obtain ⟨-, T, hT, hT₁, _, hagree₂⟩ := key
  refine fiber_hom_eq_of_pullbackFiberHom_locally_eq hsep hT fun V' e he ↦ ?_
  have hX₂ : X.hom.sieve.arrows (e ≫ f) := X.hom.sieve.downward_closed hf.2.1 e
  have hY₂ : Y.hom.sieve.arrows (e ≫ f) := Y.hom.sieve.downward_closed hf.2.2 e
  have hg₂ : B.sieve.arrows (e ≫ g) := B.sieve.downward_closed hg e
  have hhX : (e ≫ f) ≫ X.base = e ≫ g := by rw [assoc, h]
  have hhY : (e ≫ f) ≫ Y.base = e ≫ g := by rw [assoc, h']
  have hmapeq : X.hom.map (e ≫ f) hX₂ hg₂ hhX = Y.hom.map (e ≫ f) hY₂ hg₂ hhY := by
    have h₂ := hagree₂ e he hg₂
      (show e ≫ (f ≫ X.base) = e ≫ g by rw [h])
      (show e ≫ (f ≫ Y.base) = e ≫ g by rw [h'])
    have hf₁ : (A.sieve.pullback f).arrows e := (hT₁ _ he).1
    rw [DescentPairData.comp_hom_map (DescentPairData.pullbackHom A f) X e hf₁ hX₂ hg₂ hhX,
      DescentPairData.comp_hom_map (DescentPairData.pullbackHom A f) Y e hf₁ hY₂ hg₂ hhY] at h₂
    simp only [pullbackHom_map_eq_id, id_comp] at h₂
    exact h₂
  refine (Iso.cancel_iso_hom_left
    (A.datum.iso (X.hom.le_dom _ hX₂) (X.hom.le_dom _ hf.2.1) (𝟙 V') e (id_comp _)) _ _).mp ?_
  rw [← X.hom.map_glue (e ≫ f) hX₂ f hf.2.1 hg₂ hhX hg h (𝟙 V') e (id_comp _), hmapeq]
  exact Y.hom.map_glue (e ≫ f) hY₂ f hf.2.2 hg₂ hhY hg h' (𝟙 V') e (id_comp _)

/-- **The separatedness half of the sheaf condition for the morphism presheaves of the composite of
the three stages.** The first two stages make the morphisms of their output separated
(`CategoryTheory.Functor.locallyEqual_stageTwoProj_iff`), and the third preserves that. -/
theorem locallyEqual_stageThreeProj_iff (q : 𝒳 ⥤ 𝒮) [q.IsFibered] (J : GrothendieckTopology 𝒮)
    {A B : q.StageThree J} (F G : A ⟶ B) :
    (q.stageThreeProj J).LocallyEqual J F G ↔ F = G :=
  locallyEqual_descentPairProj_iff (locallyEqual_stageTwoProj_iff _ _).mp F G

/-! ### What the sheaf condition for the third stage now reduces to -/

/-- **Condition (2) of Stacks 026F for the third stage, granted the gluing half.** With
`CategoryTheory.Functor.locallyEqual_descentPairProj_iff` supplying separatedness, the only thing
still missing is the hypothesis `hglue` below: the analogue, for
`CategoryTheory.Functor.descentPairProj`, of
`CategoryTheory.Functor.exists_amalgamation_stageTwoProj`. This theorem is stated with that
statement as an explicit hypothesis precisely so that the remaining obligation is a single named
thing; it is **not** a proof that the morphism presheaves of the third stage are sheaves. -/
theorem isMorSheaf_descentPairProj_of_amalgamation
    (hsep : ∀ {x y : 𝒳} {a b : x ⟶ y}, p.LocallyEqual J a b → a = b)
    (hglue : ∀ {A B : DescentPair p J} (u : (p.descentPairProj J).obj A ⟶
        (p.descentPairProj J).obj B) {S : Sieve ((p.descentPairProj J).obj A)},
      S ∈ J ((p.descentPairProj J).obj A) →
      ∀ (F : ∀ {W : DescentPair p J} (Φ : W ⟶ A),
          S.arrows ((p.descentPairProj J).map Φ) → (W ⟶ B)),
        (∀ {W : DescentPair p J} (Φ : W ⟶ A)
          (hΦ : S.arrows ((p.descentPairProj J).map Φ)),
          (p.descentPairProj J).map (F Φ hΦ) = (p.descentPairProj J).map Φ ≫ u) →
        (∀ {W W' : DescentPair p J} (Ψ : W' ⟶ W) (Φ : W ⟶ A)
          (hΦ : S.arrows ((p.descentPairProj J).map Φ))
          (hΨΦ : S.arrows ((p.descentPairProj J).map (Ψ ≫ Φ))),
          F (Ψ ≫ Φ) hΨΦ = Ψ ≫ F Φ hΦ) →
        ∃ G : A ⟶ B, (p.descentPairProj J).map G = u ∧
          ∀ {W : DescentPair p J} (Φ : W ⟶ A)
            (hΦ : S.arrows ((p.descentPairProj J).map Φ)), Φ ≫ G = F Φ hΦ)
    (U : 𝒮) (x y : (p.descentPairProj J).Fiber U) :
    IsMorSheaf (p.descentPairProj J) J U x y :=
  isMorSheaf_of_locallyEqual_of_amalgamation
    (locallyEqual_descentPairProj_iff hsep _ _).mp hglue U x y

end CategoryTheory.Functor
