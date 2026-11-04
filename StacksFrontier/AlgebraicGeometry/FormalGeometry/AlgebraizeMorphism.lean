module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Algebraization

/-!
# Algebraizing a compatible system of morphisms over the adic thickenings of the base

**Stacks 0A42.** Let `A` be a Noetherian ring complete with respect to an ideal `I`, write
`S = Spec A` and `Sₙ = Spec (A / Iⁿ)`, and let `X`, `Y` be schemes over `S`. Put
`Xₙ = X ×_S Sₙ` and `Yₙ = Y ×_S Sₙ` for `n ≥ 1`. Given a compatible system of morphisms
`gₙ : Xₙ ⟶ Yₙ` over `Sₙ`, compatible in the sense that each square

```
  X_{n+1} --g_{n+1}--> Y_{n+1}
    ↑                    ↑
   Xₙ ------gₙ-------> Yₙ
```

commutes, and assuming that `X ⟶ S` is proper and that `Y ⟶ S` is separated of finite type,
there is a *unique* morphism `g : X ⟶ Y` over `S` whose base change to every `Sₙ` is `gₙ`.

The geometric vocabulary — `adicThickening`, `adicBaseChange`, `adicBaseChangeMap` — is that of
`StacksFrontier.AlgebraicGeometry.Algebraization`; this file adds the lemmas that the base change
maps satisfy and then proves the theorem.

## Two inputs that this library does not carry

The source's proof has two deep ingredients, and neither is available here, so both enter as
explicit named hypotheses on the main theorem; the tag attribute records the restriction.

* `AlgebraicGeometry.AdicFiniteAlgebraization` is **Stacks 09ZT**, the algebraization of a
  cartesian system of finite morphisms over the adic thickenings of a separated finite-type base
  whose closed member is proper. The source invokes it (as Lemma 30.28.1) to produce the closed
  subscheme `Z ⊆ X ×_S Y` algebraizing the graphs of the `gₙ`. Nothing in this library carries
  09ZT.
* `AlgebraicGeometry.AdicRigidity` is the rigidity consequence of Grothendieck existence
  (**Stacks 088C**, through **Stacks 0883**) that the source uses at the last step: a closed
  immersion `i : Z ⟶ W` into a scheme `W` proper over `S` through which every `Wₙ ⟶ W` factors
  is an isomorphism. Equivalently `⋂ₙ (I · 𝒪_W)ⁿ = 0` on `𝒪_W`. The library's 0883
  (`Stacks.Algebraization.fullyFaithful_completionFunctor`) is itself conditional on the theorem
  on formal functions (**Stacks 087U**), so this cannot be discharged here either.

Everything else — the graph construction, the identification of the algebraized subscheme with
`X`, and the uniqueness clause — is proved.

## Main definitions

* `AlgebraicGeometry.AdicFiniteAlgebraization`, `AlgebraicGeometry.AdicRigidity` — the two
  hypotheses described above.

## Main results

* `AlgebraicGeometry.adicBaseChangeMap_fst`, `AlgebraicGeometry.adicBaseChangeMap_snd`,
  `AlgebraicGeometry.adicBaseChangeMap_comp`,
  `AlgebraicGeometry.adicBaseChangeSucc_adicBaseChangeMap`,
  `AlgebraicGeometry.isPullback_adicBaseChangeSucc` — the calculus of adic base change.
* `AlgebraicGeometry.hom_ext_of_adicBaseChangeMap` — two morphisms over `Spec A` out of a proper
  scheme into a separated one with the same base changes are equal.
* `AlgebraicGeometry.isIso_of_adicBaseChangeMap_isIso` — a morphism to a proper scheme over
  `Spec A` whose base changes are all isomorphisms is an isomorphism.
* `AlgebraicGeometry.exists_properGraph_of_adicSystem` — the graph construction and the
  algebraization of the graphs.
* `AlgebraicGeometry.existsUnique_algebraization_adicBaseChangeMap` — Stacks 0A42.

## Implementation notes

The positive powers `Iⁿ` of the source are indexed by `ℕ` through `n ↦ I ^ (n + 1)`, as in
`StacksFrontier.AlgebraicGeometry.Algebraization`, so index `n` here is the source's `n + 1`; the
compatibility maps are the ones from the reduction modulo `I ^ (n + 1)` to the reduction modulo
`I ^ (n + 2)`. Following Mathlib, "of finite type" is `LocallyOfFiniteType` together with
`QuasiCompact`.

Uniqueness is stated as `∃!` over the subtype `{h : X ⟶ Y // h ≫ fY = fX}` of morphisms over
`Spec A`, so the unique object really is a morphism *over `S`*, and the predicate is that its base
change to each `Sₙ` equals `gₙ` on the nose.

## References

* [Stacks Project, Tag 0A42](https://stacks.math.columbia.edu/tag/0A42)
* [Stacks Project, Tag 09ZT](https://stacks.math.columbia.edu/tag/09ZT)
* [Stacks Project, Tag 088C](https://stacks.math.columbia.edu/tag/088C)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable (A : Type u) [CommRing A] (I : Ideal A) {X Y : Scheme.{u}}

/-! ### The calculus of adic base change -/

/-- The base change of `g : X ⟶ Y` followed by the projection to `Y` is the projection to `X`
followed by `g`. -/
@[reassoc]
public lemma adicBaseChangeMap_fst {fX : X ⟶ Spec (.of A)} {fY : Y ⟶ Spec (.of A)}
    (g : X ⟶ Y) (hg : g ≫ fY = fX) (n : ℕ) :
    adicBaseChangeMap A I g hg n ≫ pullback.fst fY (adicThickeningι A I n) =
      pullback.fst fX (adicThickeningι A I n) ≫ g := by
  exact pullback.lift_fst _ _ _

/-- The base change of a morphism over `Spec A` is a morphism over the adic thickening. -/
@[reassoc]
public lemma adicBaseChangeMap_snd {fX : X ⟶ Spec (.of A)} {fY : Y ⟶ Spec (.of A)}
    (g : X ⟶ Y) (hg : g ≫ fY = fX) (n : ℕ) :
    adicBaseChangeMap A I g hg n ≫ pullback.snd fY (adicThickeningι A I n) =
      pullback.snd fX (adicThickeningι A I n) := by
  exact pullback.lift_snd _ _ _

/-- Base change to an adic thickening is functorial on morphisms over `Spec A`. -/
public lemma adicBaseChangeMap_comp {Z : Scheme.{u}} {fX : X ⟶ Spec (.of A)}
    {fY : Y ⟶ Spec (.of A)} {fZ : Z ⟶ Spec (.of A)}
    (g : X ⟶ Y) (hg : g ≫ fY = fX) (h : Y ⟶ Z) (hh : h ≫ fZ = fY) (n : ℕ) :
    adicBaseChangeMap A I (g ≫ h) (by rw [Category.assoc, hh, hg]) n =
      adicBaseChangeMap A I g hg n ≫ adicBaseChangeMap A I h hh n := by
  apply pullback.hom_ext <;>
    simp [adicBaseChangeMap, Category.assoc, pullback.lift_fst, pullback.lift_snd,
      pullback.lift_fst_assoc]

/-- A map out of the base change of `Y` that is compatible with both projections is a section of
the base change of `g : X ⟶ Y`. -/
private lemma comp_adicBaseChangeMap_eq_id {fX : X ⟶ Spec (.of A)} {fY : Y ⟶ Spec (.of A)}
    (g : X ⟶ Y) (hg : g ≫ fY = fX) (n : ℕ)
    (u : adicBaseChange A I fY n ⟶ adicBaseChange A I fX n)
    (h₁ : u ≫ pullback.fst fX (adicThickeningι A I n) ≫ g = pullback.fst fY (adicThickeningι A I n))
    (h₂ : u ≫ pullback.snd fX (adicThickeningι A I n) = pullback.snd fY (adicThickeningι A I n)) :
    u ≫ adicBaseChangeMap A I g hg n = 𝟙 _ := by
  apply pullback.hom_ext
  · rw [Category.assoc, adicBaseChangeMap_fst, h₁, Category.id_comp]
  · rw [Category.assoc, adicBaseChangeMap_snd, h₂, Category.id_comp]

/-- The system of base changes of a single morphism over `Spec A` is compatible with the
transition maps: this is the commuting square that the hypothesis `g_compatible` of Stacks 0A42
demands of an abstract system. -/
public lemma adicBaseChangeSucc_adicBaseChangeMap {fX : X ⟶ Spec (.of A)}
    {fY : Y ⟶ Spec (.of A)} (g : X ⟶ Y) (hg : g ≫ fY = fX) (n : ℕ) :
    adicBaseChangeSucc A I fX n ≫ adicBaseChangeMap A I g hg (n + 1) =
      adicBaseChangeMap A I g hg n ≫ adicBaseChangeSucc A I fY n := by
  apply pullback.hom_ext <;>
    simp [adicBaseChangeSucc, adicBaseChangeMap, Category.assoc, pullback.lift_fst,
      pullback.lift_snd, pullback.lift_fst_assoc, pullback.lift_snd_assoc]

/-- The transition map between consecutive adic base changes is cartesian over the transition
map of the thickenings. -/
public lemma isPullback_adicBaseChangeSucc (f : X ⟶ Spec (.of A)) (n : ℕ) :
    IsPullback (adicBaseChangeSucc A I f n) (pullback.snd f (adicThickeningι A I n))
      (pullback.snd f (adicThickeningι A I (n + 1))) (adicThickeningSucc A I n) := by
  apply IsPullback.of_right _ (by simp [adicBaseChangeSucc, pullback.lift_snd])
    (IsPullback.of_hasPullback f (adicThickeningι A I (n + 1)))
  simpa [adicBaseChangeSucc, adicThickeningSucc_ι, pullback.lift_fst] using
    IsPullback.of_hasPullback f (adicThickeningι A I n)

/-! ### The two inputs the library does not carry -/

/-- **Stacks 09ZT**, in the shape in which the proof of Stacks 0A42 uses it: let
`fP : P ⟶ Spec A` be separated, locally of finite type and quasi-compact and let `(Zₙ)` be a
system of finite schemes over the adic base changes `Pₙ = P ×_{Spec A} Sₙ`, cartesian over the
transition maps `Pₙ ⟶ P_{n+1}`, whose first member is proper over `S₀`. Then the system is the
system of adic base changes of a single scheme `Z` finite over `P` and proper over `Spec A`.

Only the data actually used below is demanded: a `Z`, a morphism `a : Z ⟶ P` with `a ≫ fP`
proper, and maps `Zₙ ⟶ Z` exhibiting each `Zₙ` as the base change of `Z` to `Sₙ` compatibly with
`a`. (The source also records that `a` is finite and that the maps `Zₙ ⟶ Z` are compatible with
the transitions; neither is needed here, so neither is assumed.)

Nothing in this library carries Stacks 09ZT, which is why this is a hypothesis. -/
public def AdicFiniteAlgebraization : Prop :=
  ∀ {P : Scheme.{u}} (fP : P ⟶ Spec (.of A)), IsSeparated fP → LocallyOfFiniteType fP →
    QuasiCompact fP → ∀ (Zn : ℕ → Scheme.{u}) (zToP : ∀ n, Zn n ⟶ adicBaseChange A I fP n)
      (t : ∀ n, Zn n ⟶ Zn (n + 1)),
      (∀ n, IsPullback (t n) (zToP n) (zToP (n + 1)) (adicBaseChangeSucc A I fP n)) →
      (∀ n, IsFinite (zToP n)) →
      IsProper (zToP 0 ≫ pullback.snd fP (adicThickeningι A I 0)) →
      ∃ (Z : Scheme.{u}) (a : Z ⟶ P), IsProper (a ≫ fP) ∧
        ∃ k : ∀ n, Zn n ⟶ Z,
          (∀ n, IsPullback (k n) (zToP n ≫ pullback.snd fP (adicThickeningι A I n))
            (a ≫ fP) (adicThickeningι A I n)) ∧
          ∀ n, k n ≫ a = zToP n ≫ pullback.fst fP (adicThickeningι A I n)

/-- **Adic rigidity over a proper base.** A closed immersion `i : Z ⟶ W` into a scheme `W` proper
over `Spec A`, through which every adic base change `Wₙ ⟶ W` factors, is an isomorphism.

The kernel ideal sheaf of such an `i` is contained in `(I · 𝒪_W) ^ (n + 1)` for every `n`, so this
says exactly that `⋂ₙ (I · 𝒪_W)ⁿ = 0` on a scheme proper over a Noetherian `I`-adically complete
ring. That is the consequence of Grothendieck existence (Stacks 088C, via the full faithfulness of
completion, Stacks 0883) which the source uses at the final step of the proof of Stacks 0A42. The
library's 0883 is itself conditional on the theorem on formal functions (Stacks 087U), so this is
a hypothesis here. -/
public def AdicRigidity : Prop :=
  ∀ {W Z : Scheme.{u}} (fW : W ⟶ Spec (.of A)), IsProper fW → ∀ i : Z ⟶ W,
    IsClosedImmersion i →
    (∀ n, ∃ k : adicBaseChange A I fW n ⟶ Z,
      k ≫ i = pullback.fst fW (adicThickeningι A I n)) →
    IsIso i

/-! ### Rigidity of morphisms out of a proper scheme -/

/-- Two morphisms over `Spec A` from a proper scheme to a separated scheme that agree after
restriction to every adic base change of the source are equal. -/
public lemma hom_ext_of_adicBaseChange (hrig : AdicRigidity A I)
    (fX : X ⟶ Spec (.of A)) (fY : Y ⟶ Spec (.of A)) [IsProper fX] [IsSeparated fY]
    (a b : X ⟶ Y) (ha : a ≫ fY = fX) (hb : b ≫ fY = fX)
    (h : ∀ n, pullback.fst fX (adicThickeningι A I n) ≫ a =
      pullback.fst fX (adicThickeningι A I n) ≫ b) : a = b := by
  let a' : Over.mk fX ⟶ Over.mk fY := Over.homMk a ha
  let b' : Over.mk fX ⟶ Over.mk fY := Over.homMk b hb
  have : IsSeparated (Over.mk fY).hom := inferInstanceAs (IsSeparated fY)
  let e := (equalizer.ι a' b').left
  have he : IsClosedImmersion e := isClosedImmersion_equalizer_ι_left a' b'
  have : IsIso e := by
    refine hrig fX inferInstance e he fun n => ?_
    let t : Over.mk (pullback.fst fX (adicThickeningι A I n) ≫ fX) ⟶ Over.mk fX :=
      Over.homMk (pullback.fst fX (adicThickeningι A I n)) rfl
    have ht : t ≫ a' = t ≫ b' := by
      ext1
      exact h n
    exact ⟨(equalizer.lift t ht).left, congrArg Over.Hom.left (equalizer.lift_ι t ht)⟩
  apply (cancel_epi e).mp
  exact congrArg Over.Hom.left (equalizer.condition a' b')

/-- Two morphisms over `Spec A` from a proper scheme to a separated scheme whose base changes to
every adic thickening agree are equal. -/
public lemma hom_ext_of_adicBaseChangeMap (hrig : AdicRigidity A I)
    (fX : X ⟶ Spec (.of A)) (fY : Y ⟶ Spec (.of A)) [IsProper fX] [IsSeparated fY]
    (a b : X ⟶ Y) (ha : a ≫ fY = fX) (hb : b ≫ fY = fX)
    (h : ∀ n, adicBaseChangeMap A I a ha n = adicBaseChangeMap A I b hb n) : a = b := by
  refine hom_ext_of_adicBaseChange A I hrig fX fY a b ha hb fun n => ?_
  rw [← adicBaseChangeMap_fst A I a ha n, ← adicBaseChangeMap_fst A I b hb n, h n]

/-- A morphism `p : Z ⟶ X` to a scheme proper over `Spec A`, with `Z` proper over `Spec A` too,
all of whose base changes to the adic thickenings are isomorphisms, is an isomorphism. -/
public lemma isIso_of_adicBaseChangeMap_isIso (hrig : AdicRigidity A I)
    {Z : Scheme.{u}} (fX : X ⟶ Spec (.of A)) [IsProper fX] (p : Z ⟶ X) [IsProper (p ≫ fX)]
    (hp : ∀ n, IsIso (adicBaseChangeMap A I (fY := fX) p rfl n)) : IsIso p := by
  have : IsProper p := IsProper.of_comp p fX
  let s := pullback.fst p p
  let t := pullback.snd p p
  have ht : t ≫ (p ≫ fX) = s ≫ (p ≫ fX) := by
    simpa only [s, t, Category.assoc] using (pullback.condition_assoc (f := p) (g := p) fX).symm
  have hst : s = t := by
    refine hom_ext_of_adicBaseChange A I hrig (s ≫ (p ≫ fX)) (p ≫ fX) s t rfl ht fun n => ?_
    have := hp n
    have hmaps : adicBaseChangeMap A I (fY := p ≫ fX) s rfl n = adicBaseChangeMap A I t ht n := by
      apply (cancel_mono (adicBaseChangeMap A I (fY := fX) p rfl n)).mp
      rw [← adicBaseChangeMap_comp, ← adicBaseChangeMap_comp]
      congr 1
      exact pullback.condition
    simpa only [adicBaseChangeMap_fst] using congrArg
      (fun k => k ≫ pullback.fst (p ≫ fX) (adicThickeningι A I n)) hmaps
  have : Mono p := ⟨fun {W} u v huv => by
    let l := pullback.lift u v huv
    calc
      u = l ≫ s := (pullback.lift_fst _ _ _).symm
      _ = l ≫ t := congrArg (l ≫ ·) hst
      _ = v := pullback.lift_snd _ _ _⟩
  have hclosed : IsClosedImmersion p :=
    (IsClosedImmersion.iff_isProper_and_mono p).mpr ⟨inferInstance, inferInstance⟩
  refine hrig fX inferInstance p hclosed fun n => ?_
  have := hp n
  refine ⟨inv (adicBaseChangeMap A I (fY := fX) p rfl n) ≫
    pullback.fst (p ≫ fX) (adicThickeningι A I n), ?_⟩
  rw [Category.assoc, ← adicBaseChangeMap_fst A I p rfl n, IsIso.inv_hom_id_assoc]

/-! ### The graph construction -/

/-- **The graph step of Stacks 0A42.** A compatible system of morphisms `gₙ : Xₙ ⟶ Yₙ` over `Sₙ`
has, for each `n`, a graph `Xₙ ⟶ (X ×_S Y)ₙ`, which is a closed immersion because `Y ⟶ S` is
separated; the system of graphs is cartesian, so by Stacks 09ZT it algebraizes to a scheme `Z`
proper over `S` with maps `p : Z ⟶ X` and `q : Z ⟶ Y` over `S` whose base change to each `Sₙ` is
the graph of `gₙ`. -/
public lemma exists_properGraph_of_adicSystem (halg : AdicFiniteAlgebraization A I)
    (fX : X ⟶ Spec (.of A)) (fY : Y ⟶ Spec (.of A))
    [IsProper fX] [IsSeparated fY] [LocallyOfFiniteType fY] [QuasiCompact fY]
    (g : ∀ n, adicBaseChange A I fX n ⟶ adicBaseChange A I fY n)
    (g_over : ∀ n, g n ≫ pullback.snd fY (adicThickeningι A I n) =
      pullback.snd fX (adicThickeningι A I n))
    (g_compatible : ∀ n, adicBaseChangeSucc A I fX n ≫ g (n + 1) =
      g n ≫ adicBaseChangeSucc A I fY n) :
    ∃ (Z : Scheme.{u}) (p : Z ⟶ X) (q : Z ⟶ Y), IsProper (p ≫ fX) ∧ p ≫ fX = q ≫ fY ∧
      ∀ n, ∃ k : adicBaseChange A I fX n ⟶ Z,
        IsPullback k (pullback.snd fX (adicThickeningι A I n)) (p ≫ fX)
          (adicThickeningι A I n) ∧
        k ≫ p = pullback.fst fX (adicThickeningι A I n) ∧
        k ≫ q = g n ≫ pullback.fst fY (adicThickeningι A I n) := by
  let fP := pullback.fst fX fY ≫ fX
  let j (n : ℕ) : adicBaseChange A I fX n ⟶ adicBaseChange A I fP n :=
    pullback.lift
      (pullback.lift (pullback.fst fX (adicThickeningι A I n))
        (g n ≫ pullback.fst fY (adicThickeningι A I n)) (by
          rw [Category.assoc, pullback.condition (f := fY), ← Category.assoc, g_over]
          exact pullback.condition))
      (pullback.snd fX (adicThickeningι A I n)) (by
        dsimp [fP]
        rw [pullback.lift_fst_assoc]
        exact pullback.condition)
  have j_snd (n) : j n ≫ pullback.snd fP (adicThickeningι A I n) =
      pullback.snd fX (adicThickeningι A I n) := pullback.lift_snd _ _ _
  have j_fst_fst (n) : j n ≫ pullback.fst fP (adicThickeningι A I n) ≫ pullback.fst fX fY =
      pullback.fst fX (adicThickeningι A I n) := by
    simp only [j, pullback.lift_fst_assoc, pullback.lift_fst]
  have j_fst_snd (n) : j n ≫ pullback.fst fP (adicThickeningι A I n) ≫ pullback.snd fX fY =
      g n ≫ pullback.fst fY (adicThickeningι A I n) := by
    simp only [j, pullback.lift_fst_assoc, pullback.lift_snd]
  have j_compatible (n) : adicBaseChangeSucc A I fX n ≫ j (n + 1) =
      j n ≫ adicBaseChangeSucc A I fP n := by
    apply pullback.hom_ext
    · apply pullback.hom_ext
      · simp only [Category.assoc, j_fst_fst, adicBaseChangeSucc, pullback.lift_fst]
      · simp only [Category.assoc, j_fst_snd, adicBaseChangeSucc, pullback.lift_fst]
        simpa only [Category.assoc, adicBaseChangeSucc, pullback.lift_fst] using
          congrArg (fun h => h ≫ pullback.fst fY (adicThickeningι A I (n + 1)))
            (g_compatible n)
    · simp only [Category.assoc, j_snd, adicBaseChangeSucc, pullback.lift_snd]
      rw [← Category.assoc, j_snd]
  have j_cart (n) : IsPullback (adicBaseChangeSucc A I fX n) (j n) (j (n + 1))
      (adicBaseChangeSucc A I fP n) := by
    apply IsPullback.of_bot _ (j_compatible n) (isPullback_adicBaseChangeSucc A I fP n)
    simpa only [j_snd] using isPullback_adicBaseChangeSucc A I fX n
  have j_closed (n) : IsClosedImmersion (j n) := by
    let r := adicBaseChangeMap A I (fX := fP) (fY := fX) (pullback.fst fX fY) rfl n
    have hr : r ≫ pullback.snd fX (adicThickeningι A I n) =
        pullback.snd fP (adicThickeningι A I n) := adicBaseChangeMap_snd ..
    have : IsSeparated (r ≫ pullback.snd fX (adicThickeningι A I n)) := by
      rw [hr]
      dsimp [fP]
      infer_instance
    have : IsSeparated r := IsSeparated.of_comp r (pullback.snd fX (adicThickeningι A I n))
    have hjr : j n ≫ r = 𝟙 _ :=
      comp_adicBaseChangeMap_eq_id A I _ rfl n _ (j_fst_fst n) (j_snd n)
    have : IsClosedImmersion (j n ≫ r) := by
      rw [hjr]
      infer_instance
    exact IsClosedImmersion.of_comp (j n) r
  obtain ⟨Z, a, hproper, k, hcart, hka⟩ :=
    halg fP inferInstance inferInstance inferInstance (adicBaseChange A I fX) j
      (adicBaseChangeSucc A I fX) j_cart
      (fun n => by
        have := j_closed n
        infer_instance)
      (by
        have : IsProper (j 0 ≫ pullback.snd fP (adicThickeningι A I 0)) := by
          rw [j_snd]
          infer_instance
        exact this)
  refine ⟨Z, a ≫ pullback.fst fX fY, a ≫ pullback.snd fX fY, ?_, ?_, ?_⟩
  · simpa only [Category.assoc] using hproper
  · simp only [Category.assoc, pullback.condition]
  · intro n
    refine ⟨k n, ?_, ?_, ?_⟩
    · have h := hcart n
      rw [j_snd] at h
      simpa only [Category.assoc, fP] using h
    · rw [← Category.assoc, hka n, Category.assoc, j_fst_fst]
    · rw [← Category.assoc, hka n, Category.assoc, j_fst_snd]

/-! ### Stacks 0A42 -/

/-- **Stacks Project, Tag 0A42.** Let `A` be a Noetherian ring complete with respect to an ideal
`I`, write `S = Spec A` and `Sₙ = Spec (A / Iⁿ)`, and let `fX : X ⟶ S` be proper and
`fY : Y ⟶ S` separated of finite type. A compatible system of morphisms `gₙ : Xₙ ⟶ Yₙ` over `Sₙ`
— one for every `n ≥ 1`, with every composite `Xₙ ⟶ X_{n+1} ⟶ Y_{n+1}` equal to
`Xₙ ⟶ Yₙ ⟶ Y_{n+1}` — comes from a unique morphism `g : X ⟶ Y` over `S` whose base change to
each `Sₙ` is `gₙ`.

The proof is the source's: the graphs of the `gₙ` are closed immersions `Xₙ ⟶ (X ×_S Y)ₙ` because
`fY` is separated, Stacks 09ZT algebraizes them to a closed subscheme `Z ⊆ X ×_S Y` proper over
`S` (the hypothesis `halg`), the first projection `p : Z ⟶ X` has all its adic base changes
isomorphisms and is therefore an isomorphism, and `g` is `inv p ≫ q`. Both that last step and the
uniqueness clause rest on adic rigidity over a proper base (the hypothesis `hrig`), the
consequence of Grothendieck existence used by the source.

Neither `halg` (Stacks 09ZT) nor `hrig` is carried by this library; see the module documentation.
The Noetherian and completeness hypotheses on `A` are exactly the ones under which `halg` and
`hrig` hold, and are kept in the statement for that reason. -/
@[stacks 0A42 "with Stacks 09ZT as the hypothesis halg and the rigidity consequence of \
Grothendieck existence (088C, via 0883) as the hypothesis hrig"]
public theorem existsUnique_algebraization_adicBaseChangeMap
    [IsNoetherianRing A] (hcomplete : IsAdicComplete I A)
    (halg : AdicFiniteAlgebraization A I) (hrig : AdicRigidity A I)
    (fX : X ⟶ Spec (.of A)) (fY : Y ⟶ Spec (.of A))
    [IsProper fX] [IsSeparated fY] [LocallyOfFiniteType fY] [QuasiCompact fY]
    (g : ∀ n, adicBaseChange A I fX n ⟶ adicBaseChange A I fY n)
    (g_over : ∀ n, g n ≫ pullback.snd fY (adicThickeningι A I n) =
      pullback.snd fX (adicThickeningι A I n))
    (g_compatible : ∀ n, adicBaseChangeSucc A I fX n ≫ g (n + 1) =
      g n ≫ adicBaseChangeSucc A I fY n) :
    ∃! algebraization : {h : X ⟶ Y // h ≫ fY = fX},
      ∀ n, adicBaseChangeMap A I algebraization.1 algebraization.2 n = g n := by
  have := hcomplete
  obtain ⟨Z, p, q, hp, hpq, hk⟩ :=
    exists_properGraph_of_adicSystem A I halg fX fY g g_over g_compatible
  have : IsProper (p ≫ fX) := hp
  have : IsIso p := by
    refine isIso_of_adicBaseChangeMap_isIso A I hrig fX p fun n => ?_
    obtain ⟨k, hcart, hkp, hkq⟩ := hk n
    have hpn : hcart.isoPullback.hom ≫ adicBaseChangeMap A I (fY := fX) p rfl n = 𝟙 _ :=
      comp_adicBaseChangeMap_eq_id A I _ rfl n _
        (by rw [← Category.assoc, hcart.isoPullback_hom_fst, hkp])
        hcart.isoPullback_hom_snd
    have heq : adicBaseChangeMap A I (fY := fX) p rfl n = hcart.isoPullback.inv := by
      rw [← cancel_epi hcart.isoPullback.hom, hpn, hcart.isoPullback.hom_inv_id]
    rw [heq]
    infer_instance
  have hg : (inv p ≫ q) ≫ fY = fX := by
    rw [Category.assoc, ← hpq, IsIso.inv_hom_id_assoc]
  have hgn (n) : adicBaseChangeMap A I (inv p ≫ q) hg n = g n := by
    obtain ⟨k, hcart, hkp, hkq⟩ := hk n
    apply pullback.hom_ext
    · rw [adicBaseChangeMap_fst, ← hkp, Category.assoc, IsIso.hom_inv_id_assoc, hkq]
    · rw [adicBaseChangeMap_snd, g_over]
  refine ⟨⟨inv p ≫ q, hg⟩, hgn, fun a ha => Subtype.ext ?_⟩
  refine hom_ext_of_adicBaseChangeMap A I hrig fX fY a.1 (inv p ≫ q) a.2 hg fun n => ?_
  rw [ha n, hgn n]

end AlgebraicGeometry

end
