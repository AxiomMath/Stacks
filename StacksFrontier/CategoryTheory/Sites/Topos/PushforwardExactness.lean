module

public import Mathlib.CategoryTheory.Limits.Constructions.EpiMono
public import Mathlib.CategoryTheory.Sites.RegularEpi
public import StacksFrontier.CategoryTheory.Sites.QuasiCompact.FiniteCoproducts
public import StacksFrontier.CategoryTheory.Sites.Topos.ExactnessOfMorphism
public import StacksFrontier.CategoryTheory.Sites.Topos.MorphismOfTopoi

/-!
# Exactness properties of the pushforward of a morphism of topoi

Stacks tag 04D6: for a morphism of topoi `f : Sh(C) → Sh(D)` it lists eleven properties of the
pushforward `f_*` on sheaves of sets and proves eight implications (a)–(h) among them.

## Main results

* `MorphismOfTopoi.pushforward_exactness_implications`: all eight implications (a)–(h).

In `Sh(C)` a map of sheaves of sets is surjective, injective or bijective exactly when it is an
epimorphism, a monomorphism or an isomorphism (`Sheaf.isLocallySurjective_iff_epi`,
`Sheaf.isLocallyInjective_iff_mono` and balancedness of `Sh(C)`), so the properties are stated
with `Epi`, `Mono` and `IsIso`. The implications that need no topos structure come from
`exactness_properties_bundled`.
-/

@[expose] public section

open CategoryTheory

namespace MorphismOfTopoi

open Limits

universe u v u' v'

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {D : Type u'} [Category.{v'} D] {K : GrothendieckTopology D}

/-- **Stacks 04D6.** Let `f : Sh(C) → Sh(D)` be a morphism of topoi, with pushforward
`f_* = f.pushforward`, inverse image `f⁻¹ = f.inverseImage` and counit
`ε : f⁻¹ f_* F ⟶ F`. Consider the properties (on sheaves of sets, where surjections,
injections and bijections are the epimorphisms, monomorphisms and isomorphisms)

1. `f_*` is faithful;
2. `f_*` is fully faithful;
3. `ε : f⁻¹ f_* F ⟶ F` is surjective for all `F`;
4. `f_*` transforms surjections into surjections;
5. `f_*` commutes with coequalizers;
6. `f_*` commutes with pushouts;
7. `ε : f⁻¹ f_* F ⟶ F` is an isomorphism for all `F`;
8. `f_*` reflects injections;
9. `f_*` reflects surjections;
10. `f_*` reflects bijections;
11. for every surjection `p : F ⟶ f⁻¹ G` there is a surjection `q : G' ⟶ G` such that
    `f⁻¹ q` factors through `p`.

Then the eight conjuncts below are the implications (a) `(2) ⇒ (1)`, (b) `(3) ⇒ (1)`,
(c) `(7) ⇒ (1), (2), (3), (8), (9), (10)`, (d) `(3) ⇔ (9)`, (e) `(6) ⇒ (4)` and `(5) ⇒ (4)`,
(f) `(4) ⇔ (11)`, (g) `(9) ⇒ (8), (10)` and (h) `(2) ⇔ (7)`.

The topos structure enters through balancedness of `Sh(C)` in (g), every epimorphism of
`Sh(C)` being a coequalizer in (e), and epimorphisms of `Sh(C)` and `Sh(D)` being stable under
base change in (f). -/
@[stacks 04D6]
theorem pushforward_exactness_implications
    (f : MorphismOfTopoi (Sheaf J (Type max u v)) (Sheaf K (Type max u' v'))) :
    -- (a) (2) ⇒ (1)
    (f.pushforward.Full ∧ f.pushforward.Faithful → f.pushforward.Faithful) ∧
    -- (b) (3) ⇒ (1)
    ((∀ F, Epi (f.adj.counit.app F)) → f.pushforward.Faithful) ∧
    -- (c) (7) ⇒ (1), (2), (3), (8), (9), (10)
    ((∀ F, IsIso (f.adj.counit.app F)) →
      f.pushforward.Faithful ∧ (f.pushforward.Full ∧ f.pushforward.Faithful) ∧
      (∀ F, Epi (f.adj.counit.app F)) ∧ f.pushforward.ReflectsMonomorphisms ∧
      f.pushforward.ReflectsEpimorphisms ∧ f.pushforward.ReflectsIsomorphisms) ∧
    -- (d) (3) ⇔ (9)
    ((∀ F, Epi (f.adj.counit.app F)) ↔ f.pushforward.ReflectsEpimorphisms) ∧
    -- (e) (6) ⇒ (4) and (5) ⇒ (4)
    ((PreservesColimitsOfShape WalkingSpan f.pushforward → f.pushforward.PreservesEpimorphisms) ∧
      (PreservesColimitsOfShape WalkingParallelPair f.pushforward →
        f.pushforward.PreservesEpimorphisms)) ∧
    -- (f) (4) ⇔ (11)
    (f.pushforward.PreservesEpimorphisms ↔
      ∀ (G : Sheaf K (Type max u' v')) (F : Sheaf J (Type max u v))
        (p : F ⟶ f.inverseImage.obj G), Epi p →
        ∃ (G' : Sheaf K (Type max u' v')) (q : G' ⟶ G), Epi q ∧
          ∃ r : f.inverseImage.obj G' ⟶ F, r ≫ p = f.inverseImage.map q) ∧
    -- (g) (9) ⇒ (8), (10)
    (f.pushforward.ReflectsEpimorphisms →
      f.pushforward.ReflectsMonomorphisms ∧ f.pushforward.ReflectsIsomorphisms) ∧
    -- (h) (2) ⇔ (7)
    (f.pushforward.Full ∧ f.pushforward.Faithful ↔ ∀ F, IsIso (f.adj.counit.app F)) := by
  set R := f.pushforward
  set L := f.inverseImage
  set adj : L ⊣ R := f.adj
  -- (b): an epimorphic counit makes `R` faithful.
  have hb : (∀ F, Epi (adj.counit.app F)) → R.Faithful := fun h => adj.faithful_R_of_epi_counit_app
  -- (9) ⇒ (3): `R` of the counit is split epi by the triangle identity.
  have h93 : R.ReflectsEpimorphisms → ∀ F, Epi (adj.counit.app F) :=
    fun h => (exactness_properties_bundled adj).2.2.1 h
  -- (7) ⇒ (2) and (2) ⇒ (7).
  have h72 : (∀ F, IsIso (adj.counit.app F)) → R.Full ∧ R.Faithful := fun h =>
    have hff := fullyFaithful_R_of_counit_app_isIso adj h
    ⟨hff.full, hff.faithful⟩
  have h27 : R.Full ∧ R.Faithful → ∀ F, IsIso (adj.counit.app F) := fun ⟨_, _⟩ =>
    counit_app_isIso_of_R_fullyFaithful adj (Functor.FullyFaithful.ofFullyFaithful R)
  -- (9) ⇒ (8), (10), using that `Sh(C)` is balanced.
  have hg : R.ReflectsEpimorphisms → R.ReflectsMonomorphisms ∧ R.ReflectsIsomorphisms := by
    intro h9
    have : R.Faithful := hb (h93 h9)
    refine ⟨inferInstance, ⟨fun {X Y} a _ => ?_⟩⟩
    have : Mono a := R.mono_of_mono_map inferInstance
    have : Epi a := R.epi_of_epi_map inferInstance
    exact isIso_of_mono_of_epi a
  refine ⟨fun h => h.2, hb, fun h7 => ?_, ⟨fun h3 => ?_, h93⟩, ⟨fun _ => inferInstance, ?_⟩,
    ⟨?_, ?_⟩, hg, ⟨h27, h72⟩⟩
  · -- (c)
    obtain ⟨_, _⟩ := h72 h7
    exact ⟨inferInstance, ⟨inferInstance, inferInstance⟩, fun F => inferInstance, inferInstance,
      inferInstance, inferInstance⟩
  · -- (d) (3) ⇒ (9): a faithful functor reflects epimorphisms.
    have : R.Faithful := hb h3
    infer_instance
  · -- (e) (5) ⇒ (4): every epimorphism of `Sh(C)` is a coequalizer.
    intro _
    refine ⟨fun {X Y} a _ => ?_⟩
    let ha := regularEpiOfEpi a
    exact epi_of_isColimit_cofork (isColimitCoforkMapOfIsColimit R ha.w ha.isColimit)
  · -- (f) (4) ⇒ (11)
    intro h4 G F p _
    refine ⟨pullback (R.map p) (adj.unit.app G), pullback.snd _ _,
      Sheaf.epi_pullback_snd _ _ inferInstance,
      L.map (pullback.fst (R.map p) (adj.unit.app G)) ≫ adj.counit.app F, ?_⟩
    have h := congrArg (fun k => L.map k ≫ adj.counit.app (L.obj G))
      (pullback.condition (f := R.map p) (g := adj.unit.app G))
    simpa using h
  · -- (f) (11) ⇒ (4)
    intro h11
    refine ⟨fun {F F'} a _ => ?_⟩
    obtain ⟨G', q, _, r, hr⟩ := h11 (R.obj F') (pullback a (adj.counit.app F'))
      (pullback.snd a (adj.counit.app F')) (Sheaf.epi_pullback_snd _ _ inferInstance)
    refine epi_of_epi_fac (f := adj.unit.app G' ≫ R.map (r ≫ pullback.fst _ _)) (h := q) ?_
    have h1 : r ≫ pullback.fst a (adj.counit.app F') ≫ a = L.map q ≫ adj.counit.app F' := by
      rw [pullback.condition, ← Category.assoc, hr]
    calc (adj.unit.app G' ≫ R.map (r ≫ pullback.fst a (adj.counit.app F'))) ≫ R.map a
        = adj.unit.app G' ≫ R.map (r ≫ pullback.fst a (adj.counit.app F') ≫ a) := by simp
      _ = q := by rw [h1]; simp

end MorphismOfTopoi
