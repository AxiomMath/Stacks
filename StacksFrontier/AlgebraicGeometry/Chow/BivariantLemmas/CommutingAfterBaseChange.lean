module

public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.CompletedRestrictionComposite
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.VirtualNormalBundleClassBaseChange
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.VirtualNormalBundleImmersionClass
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.FlatPullbackProperPushforward

/-!
# Classes commuting with every class after every base change

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project. Stacks 0FF6 asserts that
the Gysin map `f^!` of a local complete intersection morphism `f : X ⟶ Y` has the following
property: for every `Y' ⟶ Y` its restriction `res(f^!)` (Stacks 0F9Z) commutes with every
bivariant class over `Y'` (Stacks 0FA2). This file isolates that property and proves that it is
preserved by the operations from which `f^!` is built.

A homogeneous class `c ∈ A^p(X ⟶ Y)` *commutes with every class after every base change*
(`Stacks.Chow.BivariantClass.CommutesAfterBaseChange`) when all of its restrictions commute with
every class. This holds for flat pullbacks (Stacks 0B78), whose restrictions are flat pullbacks,
and for the class `c(Z ⟶ X, 𝒩)` of a virtual normal bundle of constant rank, whose restrictions are
classes of virtual normal bundles (Stacks 0FBK with Stacks 0FBJ) and commute with every class by
Stacks 0FBP. It is preserved by sums, by composition (Stacks 0B75: the restriction of a composite
is a transport of the composite of the restrictions), and by proper pushforward (Stacks 0EPK: the
restriction of a proper pushforward is the proper pushforward of the restriction).

A completed class `c ∈ A^*(X ⟶ Y)^∧` (Stacks 0FE0) commutes with every class after every base
change (`Stacks.Chow.completedCommutesAfterBaseChange`) when every term of its tuple does; then all
of its restrictions commute with every class on completions. The property can be checked on the
components of `c`: a class on a connected component `X_w` extends by zero to `X`
(`Stacks.Chow.bivariantComponentExtension`, a proper pushforward along `X_w ⟶ X`), and the
restriction of a class to a connected component of `X ×_Y Y'` only depends on its restriction to
the component of `X` below. Hence the property holds for the completed class of a virtual normal
bundle of arbitrary rank, for an immersion (Stacks 0FBQ (3)), for the completed smooth pullback,
and for completed composites.

## Main definitions

* `Stacks.Chow.BivariantClass.CommutesAfterBaseChange`,
  `Stacks.Chow.completedCommutesAfterBaseChange` — commuting with every class after every base
  change, for homogeneous and completed classes.
* `Stacks.Chow.bivariantComponentExtension` — a class on a connected component extended by zero.

## Main results

* `Stacks.Chow.bivariantRestriction_bivariantProperPushforward` — restriction of a proper
  pushforward.
* `Stacks.Chow.BivariantClass.CommutesWithEveryClass.bivariantTransport` — transport along an
  isomorphism of sources preserves commuting with every class.
* `Stacks.Chow.bivariantConnectedComponentRestriction_bivariantComponentExtension` — a class
  extended by zero restricts back to it.
* `Stacks.Chow.completedCommutesAfterBaseChange_of_apply` — the componentwise criterion.
* `Stacks.Chow.completedCommutesAfterBaseChange_completedVirtualNormalGysinClassOfImmersion`,
  `Stacks.Chow.completedCommutesAfterBaseChange_completedFlatPullbackOfSmooth`,
  `Stacks.Chow.completedCommutesAfterBaseChange_completedBivariantCompositeOfInvertible`.

## References

* [Stacks Project, Tag 0FF6](https://stacks.math.columbia.edu/tag/0FF6)
* [Stacks Project, Tag 0FBP](https://stacks.math.columbia.edu/tag/0FBP)
* [Stacks Project, Tag 0FBK](https://stacks.math.columbia.edu/tag/0FBK)
* [Stacks Project, Tag 0FBJ](https://stacks.math.columbia.edu/tag/0FBJ)
* [Stacks Project, Tag 0F9Z](https://stacks.math.columbia.edu/tag/0F9Z)
* [Stacks Project, Tag 0FA2](https://stacks.math.columbia.edu/tag/0FA2)
* [Stacks Project, Tag 0EPK](https://stacks.math.columbia.edu/tag/0EPK)
* [Stacks Project, Tag 0FDZ](https://stacks.math.columbia.edu/tag/0FDZ)
* [Stacks Project, Tag 0FE0](https://stacks.math.columbia.edu/tag/0FE0)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

/-! ### Transport and proper pushforward preserve commuting with every class -/

section Transport

variable {C : ChowSituation.{u}} {A B W : Scheme.{u}} {sA : A ⟶ C.S} [LocallyOfFiniteType sA]
  {sB : B ⟶ C.S} [LocallyOfFiniteType sB] {sW : W ⟶ C.S} [LocallyOfFiniteType sW]
  {v : A ⟶ W} [LocallyOfFiniteType v] {u : B ⟶ W} [LocallyOfFiniteType u] {p : ℤ}

/-- The transport of a class along an isomorphism `θ : A ≅ B` over `W` is its proper pushforward
(Stacks 0EPK) along `θ`. -/
theorem bivariantTransport_eq_bivariantProperPushforward (θ : A ≅ B) (hu : u ≫ sW = sB)
    (c : BivariantClass C (gysinSystemOfInvertible C) ((θ.hom ≫ u) ≫ sW) sW (θ.hom ≫ u) rfl p) :
    haveI : LocallyOfFiniteType (θ.hom ≫ u) := inferInstance
    bivariantTransport C (gysinSystemOfInvertible C) ((θ.hom ≫ u) ≫ sW) sB sW (θ.hom ≫ u) rfl u
        hu θ rfl p (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) c =
      bivariantProperPushforwardOfInvertible C ((θ.hom ≫ u) ≫ sW) sB sW θ.hom u
        (by rw [← hu, Category.assoc]) hu p c := by
  refine BivariantClass.ext _ _ _ _ _ _ _ fun {T} t _ k α ↦ ?_
  rw [bivariantTransport_cap, bivariantTransportCap_apply,
    bivariantProperPushforwardOfInvertible_cap, bivariantProperPushforwardCap_apply]
  have he : bivariantPushforwardBaseChange θ.hom u t =
      (transportPullbackIso (θ.hom ≫ u) u θ rfl t).hom := by
    apply pullback.hom_ext <;> simp
  have : IsIso (bivariantPushforwardBaseChange θ.hom u t) := he ▸ inferInstance
  rw [properChowPushforward_eq_chowPushforwardOfIso]
  exact chowPushforwardOfIso_congr_apply C _ _ _ _ he.symm _ _ _ _

/-- **Transport preserves commuting with every class.** The transport of a class commuting with
every bivariant class along an isomorphism of sources commutes with every bivariant class: it is
the proper pushforward along the isomorphism (Stacks 0FBX for proper pushforward). -/
theorem BivariantClass.CommutesWithEveryClass.bivariantTransport {hv : v ≫ sW = sA}
    {hu : u ≫ sW = sB} (θ : A ≅ B) (hθ : θ.hom ≫ u = v)
    {c : BivariantClass C (gysinSystemOfInvertible C) sA sW v hv p}
    (hc : c.CommutesWithEveryClass) :
    (Stacks.Chow.bivariantTransport C (gysinSystemOfInvertible C) sA sB sW v hv u hu θ hθ p
      (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) c).CommutesWithEveryClass := by
  subst hθ hv
  rw [bivariantTransport_eq_bivariantProperPushforward θ hu c]
  exact commutesWithEveryClass_bivariantProperPushforward θ.hom u _ hu c hc

/-- The transport of a class along the identity of its source is the same class, read for the
equal morphism. -/
theorem bivariantTransport_refl {v' : A ⟶ W} [LocallyOfFiniteType v'] (hvv' : v = v')
    (hv : v ≫ sW = sA) (hv' : v' ≫ sW = sA) (hθ : (Iso.refl A).hom ≫ v' = v)
    (c : BivariantClass C (gysinSystemOfInvertible C) sA sW v hv p) :
    bivariantTransport C (gysinSystemOfInvertible C) sA sA sW v hv v' hv' (Iso.refl A) hθ p
        (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) c =
      BivariantClass.copy C (gysinSystemOfInvertible C) sA sW hvv' hv hv' rfl c := by
  subst hvv'
  refine BivariantClass.ext _ _ _ _ _ _ _ fun {T} t _ k α ↦ ?_
  rw [bivariantTransport_cap, bivariantTransportCap_apply,
    chowPushforwardOfIso_congr_apply C _ _ _ (𝟙 _) (by apply pullback.hom_ext <;> simp) _
      (Category.id_comp _), chowPushforwardOfIso_id]
  rfl

end Transport

/-! ### Restriction of a proper pushforward -/

section ProperRestriction

variable (C : ChowSituation.{u}) {A X Y Y' : Scheme.{u}} (sA : A ⟶ C.S) [LocallyOfFiniteType sA]
  (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]
  (ι : A ⟶ X) [IsProper ι] (f : X ⟶ Y) [LocallyOfFiniteType f] [LocallyOfFiniteType (ι ≫ f)]
  (hι : ι ≫ sX = sA) (hf : f ≫ sY = sX) (h : Y' ⟶ Y) [LocallyOfFiniteType h] (p : ℤ)

/-- **Restriction of a proper pushforward is the proper pushforward of the restriction**
(Stacks 0F9Z and Stacks 0EPK). For `ι : A ⟶ X` proper, `f : X ⟶ Y`, `b ∈ A^p(A ⟶ Y)` and
`h : Y' ⟶ Y`, the restriction of `ι_* b` along `h` is the pushforward along the base change
`ι' : A ×_Y Y' ⟶ X ×_Y Y'` of the restriction of `b`, read as a class for `ι' ≫ (X ×_Y Y' ⟶ Y')`
(the transport along the identity of `A ×_Y Y'`). -/
theorem bivariantRestriction_bivariantProperPushforward
    (b : BivariantClass C (gysinSystemOfInvertible C) sA sY (ι ≫ f)
      (comp_comp_structureMorphism_eq hι hf) p) :
    bivariantRestriction C (gysinSystemOfInvertible C) sX sY f hf h p
        (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C)
        (bivariantProperPushforwardOfInvertible C sA sX sY ι f hι hf p b) =
      bivariantProperPushforwardOfInvertible C (pullback.fst (ι ≫ f) h ≫ sA) (pullback.fst f h ≫ sX)
        (h ≫ sY)
        (bivariantPushforwardBaseChange ι f h) (pullback.snd f h)
        (bivariantPushforwardBaseChange_comp_structure hι f h)
        (pullbackSnd_comp_structureMorphism_eq C sX sY f hf h) p
        (bivariantTransport C (gysinSystemOfInvertible C) (pullback.fst (ι ≫ f) h ≫ sA)
          (pullback.fst (ι ≫ f) h ≫ sA) (h ≫ sY) (pullback.snd (ι ≫ f) h)
          (pullbackSnd_comp_structureMorphism_eq C sA sY (ι ≫ f)
            (comp_comp_structureMorphism_eq hι hf) h)
          (bivariantPushforwardBaseChange ι f h ≫ pullback.snd f h)
          (comp_comp_structureMorphism_eq (bivariantPushforwardBaseChange_comp_structure hι f h)
            (pullbackSnd_comp_structureMorphism_eq C sX sY f hf h))
          (Iso.refl _) (by simp) p (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C)
          (bivariantRestriction C (gysinSystemOfInvertible C) sA sY (ι ≫ f)
            (comp_comp_structureMorphism_eq hι hf) h p
            (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) b)) := by
  refine BivariantClass.ext _ _ _ _ _ _ _ fun {T} t _ k α ↦ ?_
  rw [bivariantRestriction_cap, bivariantRestrictionCap_apply,
    bivariantProperPushforwardOfInvertible_cap,
    bivariantProperPushforwardCap_apply, bivariantProperPushforwardOfInvertible_cap,
    bivariantProperPushforwardCap_apply, bivariantTransport_cap, bivariantTransportCap_apply,
    bivariantRestriction_cap, bivariantRestrictionCap_apply]
  set x := b.cap (t ≫ h) k (chowGroupCongr C (Category.assoc t h sY).symm k α)
  rw [chowPushforwardOfIso_comp_apply,
    ← properChowPushforward_eq_chowPushforwardOfIso C _ _ _ _ _
      (properPushforwardFactorsThroughRationalEquivalence_of_isIso C _ _ _ _ _),
    ← properChowPushforward_eq_chowPushforwardOfIso C _ _ _ _ _
      (properPushforwardFactorsThroughRationalEquivalence_of_isIso C _ _ _ _ _)]
  refine properChowPushforward_comp_eq C _ _ _ _ _ _ _ _ ?_ _ _ _ _ _ _ _ _ _ x
  apply pullback.hom_ext
  · apply pullback.hom_ext <;> simp
  · simp

end ProperRestriction


/-! ### Commuting with every class after every base change -/

section AfterBaseChange

variable {C : ChowSituation.{u}} {X Y : Scheme.{u}} {sX : X ⟶ C.S} [LocallyOfFiniteType sX]
  {sY : Y ⟶ C.S} [LocallyOfFiniteType sY] {f : X ⟶ Y} [LocallyOfFiniteType f]
  {hf : f ≫ sY = sX} {p : ℤ}

/-- A class `c ∈ A^p(X ⟶ Y)` *commutes with every class after every base change* when, for every
morphism `h : Y' ⟶ Y` locally of finite type, its restriction `res(c) ∈ A^p(X ×_Y Y' ⟶ Y')`
(Stacks 0F9Z) commutes with every bivariant class over `Y'` (Stacks 0FA2). This is the property
Stacks 0FF6 asserts of the Gysin map of a local complete intersection morphism. -/
def BivariantClass.CommutesAfterBaseChange
    (c : BivariantClass C (gysinSystemOfInvertible C) sX sY f hf p) : Prop :=
  ∀ ⦃Y' : Scheme.{u}⦄ (h : Y' ⟶ Y) [LocallyOfFiniteType h],
    (bivariantRestriction C (gysinSystemOfInvertible C) sX sY f hf h p
      (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) c).CommutesWithEveryClass

/-- The zero class commutes with every class after every base change. -/
theorem BivariantClass.commutesAfterBaseChange_zero :
    (0 : BivariantClass C (gysinSystemOfInvertible C) sX sY f hf p).CommutesAfterBaseChange :=
  fun _ h _ ↦ by
    rw [bivariantRestriction_zero]
    exact BivariantClass.commutesWithEveryClass_zero

/-- A homogeneous summand `DirectSum.of _ m e` of a graded family commuting with every class after
every base change does so in every degree, if `e` does. -/
private theorem commutesAfterBaseChange_directSum_of {m : ℤ}
    (e : BivariantClass C (gysinSystemOfInvertible C) sX sY f hf m) (he : e.CommutesAfterBaseChange)
    (n : ℤ) :
    (DirectSum.of (fun n ↦ BivariantClass C (gysinSystemOfInvertible C) sX sY f hf n) m e
      n).CommutesAfterBaseChange := by
  by_cases hn : m = n
  · subst hn
    rw [DirectSum.of_eq_same]
    exact he
  · rw [DirectSum.of_eq_of_ne _ n _ (Ne.symm hn)]
    exact BivariantClass.commutesAfterBaseChange_zero

/-- A sum of classes commuting with every class after every base change does too. -/
theorem BivariantClass.CommutesAfterBaseChange.add
    {c d : BivariantClass C (gysinSystemOfInvertible C) sX sY f hf p}
    (hc : c.CommutesAfterBaseChange) (hd : d.CommutesAfterBaseChange) :
    (c + d).CommutesAfterBaseChange := fun _ h _ ↦ by
  rw [bivariantRestriction_add]
  exact (hc h).add (hd h)

/-- A finite sum of classes commuting with every class after every base change does too. -/
theorem BivariantClass.commutesAfterBaseChange_sum {ι : Type*} (s : Finset ι)
    (c : ι → BivariantClass C (gysinSystemOfInvertible C) sX sY f hf p)
    (hc : ∀ i ∈ s, (c i).CommutesAfterBaseChange) :
    (∑ i ∈ s, c i).CommutesAfterBaseChange := by
  classical
  induction s using Finset.induction_on with
  | empty => exact BivariantClass.commutesAfterBaseChange_zero
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (hc a (Finset.mem_insert_self a s)).add
      (ih fun i hi ↦ hc i (Finset.mem_insert_of_mem hi))

/-- Commuting with every class after every base change is invariant under reading a class for an
equal morphism and in an equal degree. -/
theorem BivariantClass.commutesAfterBaseChange_copy {f' : X ⟶ Y} [LocallyOfFiniteType f']
    (hff' : f = f') (hf' : f' ≫ sY = sX) {p' : ℤ} (hpp' : p = p')
    (c : BivariantClass C (gysinSystemOfInvertible C) sX sY f hf p) :
    (BivariantClass.copy C (gysinSystemOfInvertible C) sX sY hff' hf hf' hpp'
      c).CommutesAfterBaseChange ↔ c.CommutesAfterBaseChange := by
  subst hff' hpp'
  rfl

/-- A class commuting with every class after every base change commutes with every class after a
base change followed by any further base change: its restriction commutes with every class after
every base change. -/
theorem BivariantClass.CommutesAfterBaseChange.commutesWithEveryClass_bivariantRestriction
    {c : BivariantClass C (gysinSystemOfInvertible C) sX sY f hf p}
    (hc : c.CommutesAfterBaseChange) {Y' : Scheme.{u}} (h : Y' ⟶ Y) [LocallyOfFiniteType h] :
    (bivariantRestriction C (gysinSystemOfInvertible C) sX sY f hf h p
      (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) c).CommutesWithEveryClass :=
  hc h

end AfterBaseChange

section AfterBaseChangeComposite

variable {C : ChowSituation.{u}} {X P Y : Scheme.{u}} {sX : X ⟶ C.S} [LocallyOfFiniteType sX]
  {sP : P ⟶ C.S} [LocallyOfFiniteType sP] {sY : Y ⟶ C.S} [LocallyOfFiniteType sY]
  {i : X ⟶ P} [LocallyOfFiniteType i] {g : P ⟶ Y} [LocallyOfFiniteType g]
  {hi : i ≫ sP = sX} {hg : g ≫ sY = sP} {p q : ℤ}

/-- **A composite of classes commuting with every class after every base change does too.**
The restriction of `a ∘ b` along `h` is the transport of `res(a) ∘ res_h(b)`
(`Stacks.Chow.bivariantRestriction_bivariantCompositeOfInvertible`), a composite of classes
commuting with every class. -/
theorem BivariantClass.CommutesAfterBaseChange.bivariantCompositeOfInvertible
    {a : BivariantClass C (gysinSystemOfInvertible C) sX sP i hi p}
    {b : BivariantClass C (gysinSystemOfInvertible C) sP sY g hg q}
    (ha : a.CommutesAfterBaseChange) (hb : b.CommutesAfterBaseChange) :
    (Stacks.Chow.bivariantCompositeOfInvertible C sX sP sY i g hi hg p q a
      b).CommutesAfterBaseChange := fun _ h _ ↦ by
  rw [bivariantRestriction_bivariantCompositeOfInvertible]
  exact BivariantClass.CommutesWithEveryClass.bivariantTransport _ _
    ((ha (pullback.fst g h)).bivariantCompositeOfInvertible (hb h))

end AfterBaseChangeComposite

section AfterBaseChangeExamples

variable (C : ChowSituation.{u}) {X Y : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (f : X ⟶ Y) [LocallyOfFiniteType f]
  (hf : f ≫ sY = sX)

/-- **The flat-pullback class commutes with every class after every base change**: its
restriction is the flat-pullback class of the base change
(`Stacks.Chow.bivariantRestriction_flatPullbackBivariantClass`), which commutes with every class
(Stacks 0B76 (2)). -/
theorem commutesAfterBaseChange_flatPullbackBivariantClass [Flat f] (r : ℕ)
    (hfr : AlgebraicGeometry.RelativeDimension f r) :
    (flatPullbackBivariantClassOfInvertible C sX sY f hf r hfr).CommutesAfterBaseChange :=
  fun _ h _ ↦ by
    rw [bivariantRestriction_flatPullbackBivariantClass]
    exact commutesWithEveryClass_flatPullbackBivariantClass _ r _ (flatPullbackDescends C) _
      (isBivariantFlatPullback_flatPullbackBivariantClassOfInvertible C _ _ _ _ _ _)

/-- The flat-pullback class of an open immersion commutes with every class after every base
change. -/
theorem commutesAfterBaseChange_flatPullbackBivariantClassOfIsOpenImmersionOfInvertible
    [IsOpenImmersion f] :
    (flatPullbackBivariantClassOfIsOpenImmersionOfInvertible C sX sY f
      hf).CommutesAfterBaseChange := by
  have h : flatPullbackBivariantClassOfIsOpenImmersionOfInvertible C sX sY f hf =
      flatPullbackBivariantClassOfInvertible C sX sY f hf 0
        (relativeDimension_of_isOpenImmersion f) :=
    BivariantClass.ext _ _ _ _ _ _ _ fun _ _ _ _ ↦ rfl
  rw [h]
  exact commutesAfterBaseChange_flatPullbackBivariantClass C sX sY f hf 0 _

/-- **The Gysin class `c(Z ⟶ X, 𝒩)` of a virtual normal bundle of constant rank commutes with every
class after every base change**: its restriction is the class of the base-changed virtual normal
bundle (Stacks 0FBK with Stacks 0FBJ), which commutes with every class (Stacks 0FBP). -/
theorem commutesAfterBaseChange_virtualNormalGysinClass {Z : Scheme.{u}} (sZ : Z ⟶ C.S)
    [LocallyOfFiniteType sZ] (i : Z ⟶ X) [IsClosedImmersion i] (hi : i ≫ sX = sZ)
    (𝒩 : VirtualNormalBundle i) (r : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} 𝒩.bundle r] :
    (virtualNormalBundleClass C sZ sX i hi 𝒩 r).CommutesAfterBaseChange := fun _ h _ ↦ by
  rw [bivariantRestriction_virtualNormalGysinClass]
  exact virtualNormalBundleClass_commutesWithEveryClass C _ _ _ _ r _

/-- **The proper pushforward of a class commuting with every class after every base change does
too**: its restriction is the proper pushforward of a transport of the restriction
(`Stacks.Chow.bivariantRestriction_bivariantProperPushforward`). -/
theorem BivariantClass.CommutesAfterBaseChange.bivariantProperPushforward {A : Scheme.{u}}
    {sA : A ⟶ C.S} [LocallyOfFiniteType sA] {ι : A ⟶ X} [IsProper ι] [LocallyOfFiniteType (ι ≫ f)]
    {hι : ι ≫ sX = sA} {p : ℤ}
    {b : BivariantClass C (gysinSystemOfInvertible C) sA sY (ι ≫ f)
      (comp_comp_structureMorphism_eq hι hf) p}
    (hb : b.CommutesAfterBaseChange) :
    (Stacks.Chow.bivariantProperPushforwardOfInvertible C sA sX sY ι f hι hf p
      b).CommutesAfterBaseChange :=
  fun _ h _ ↦ by
    rw [bivariantRestriction_bivariantProperPushforward]
    exact commutesWithEveryClass_bivariantProperPushforward _ _ _ _ _
      (BivariantClass.CommutesWithEveryClass.bivariantTransport _ _ (hb h))

end AfterBaseChangeExamples

/-! ### Extension by zero from a connected component -/

section ComponentExtension

variable (C : ChowSituation.{u}) {X Y : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (f : X ⟶ Y) [LocallyOfFiniteType f]
  (hf : f ≫ sY = sX) [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
  (w : _root_.ConnectedComponents X) {n : ℤ}

/-- **A class on a connected component, extended by zero.** For a connected component `X_w` of `X`
lying over the connected component `Y_{w'}` of `Y` and a class `b ∈ A^n(X_w ⟶ Y_{w'})`, the class
`ι_* (b ∘ j^*) ∈ A^n(X ⟶ Y)`: the composite (Stacks 0B75) of `b` with the flat pullback along the
open immersion `j : Y_{w'} ⟶ Y` (Stacks 0B78), read as a class for `X_w ⟶ X ⟶ Y`, pushed forward
(Stacks 0EPK) along the inclusion `ι : X_w ⟶ X`, which is a closed immersion. Its restriction to
`X_w` (Stacks 0FDZ) is `b`, and its restriction to every other connected component vanishes. -/
def bivariantComponentExtension
    (b : BivariantClass C (gysinSystemOfInvertible C) ((X.connectedComponentOpens w).ι ≫ sX)
      ((Y.connectedComponentOpens (f.continuous.connectedComponentsMap w)).ι ≫ sY)
      (f.resConnectedComponent w) (f.resConnectedComponent_comp_ι_comp hf w) n) :
    BivariantClass C (gysinSystemOfInvertible C) sX sY f hf n :=
  bivariantProperPushforwardOfInvertible C ((X.connectedComponentOpens w).ι ≫ sX) sX sY
    (X.connectedComponentOpens w).ι f rfl hf n
    (bivariantTransport C (gysinSystemOfInvertible C) ((X.connectedComponentOpens w).ι ≫ sX)
      ((X.connectedComponentOpens w).ι ≫ sX) sY
      (f.resConnectedComponent w ≫
        (Y.connectedComponentOpens (f.continuous.connectedComponentsMap w)).ι)
      (comp_comp_structureMorphism_eq (f.resConnectedComponent_comp_ι_comp hf w) rfl)
      ((X.connectedComponentOpens w).ι ≫ f) (comp_comp_structureMorphism_eq rfl hf)
      (Iso.refl _)
      (by rw [Iso.refl_hom, Category.id_comp, Scheme.Hom.resConnectedComponent_comp_ι]) n
      (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C)
      (BivariantClass.copy C (gysinSystemOfInvertible C) _ sY rfl _ _ (add_zero n)
        (openImmersionComposite C ((X.connectedComponentOpens w).ι ≫ sX)
          ((Y.connectedComponentOpens (f.continuous.connectedComponentsMap w)).ι ≫ sY) sY
          (f.resConnectedComponent w)
          (Y.connectedComponentOpens (f.continuous.connectedComponentsMap w)).ι
          (f.resConnectedComponent_comp_ι_comp hf w) rfl n b)))

variable {C sX sY f hf w} in
/-- A class on a connected component commuting with every class after every base change extends
by zero to a class that does too. -/
theorem BivariantClass.CommutesAfterBaseChange.bivariantComponentExtension
    {b : BivariantClass C (gysinSystemOfInvertible C) ((X.connectedComponentOpens w).ι ≫ sX)
      ((Y.connectedComponentOpens (f.continuous.connectedComponentsMap w)).ι ≫ sY)
      (f.resConnectedComponent w) (f.resConnectedComponent_comp_ι_comp hf w) n}
    (hb : b.CommutesAfterBaseChange) :
    (bivariantComponentExtension C sX sY f hf w b).CommutesAfterBaseChange :=
  BivariantClass.CommutesAfterBaseChange.bivariantProperPushforward C sX sY f hf (by
    rw [bivariantTransport_refl (f.resConnectedComponent_comp_ι w)]
    exact (BivariantClass.commutesAfterBaseChange_copy _ _ _ _).2
      ((BivariantClass.commutesAfterBaseChange_copy _ _ _ _).2
        (hb.bivariantCompositeOfInvertible
          (commutesAfterBaseChange_flatPullbackBivariantClassOfIsOpenImmersionOfInvertible C _ sY _
            rfl))))

/-- **A class on a connected component, extended by zero, restricts to it.** The restriction
(Stacks 0FDZ) of `ι_* (b ∘ j^*)` to `X_w` is `b`: on a test scheme, restricting the pushforward
along the open and closed immersion `X_w ×_Y T ⟶ X ×_Y T` to its image undoes it, and restricting
`b ∘ j^*` back to `Y_{w'}` gives `b`. -/
theorem bivariantConnectedComponentRestriction_bivariantComponentExtension
    (b : BivariantClass C (gysinSystemOfInvertible C) ((X.connectedComponentOpens w).ι ≫ sX)
      ((Y.connectedComponentOpens (f.continuous.connectedComponentsMap w)).ι ≫ sY)
      (f.resConnectedComponent w) (f.resConnectedComponent_comp_ι_comp hf w) n) :
    bivariantConnectedComponentRestriction C (gysinSystemOfInvertible C) sX sY f hf n
        (gysinSystemOfInvertible_isNaturalUnderOpenImmersion C)
        (bivariantComponentExtension C sX sY f hf w b) w = b := by
  refine BivariantClass.ext _ _ _ _ _ _ _ fun {S} s _ k β ↦ ?_
  rw [bivariantConnectedComponentRestriction_cap, bivariantComponentExtension,
    bivariantProperPushforwardOfInvertible_cap, bivariantProperPushforwardCap_apply]
  set ιX := (X.connectedComponentOpens w).ι
  set ιY := (Y.connectedComponentOpens (f.continuous.connectedComponentsMap w)).ι
  set fw := f.resConnectedComponent w
  set t := s ≫ ιY
  have hc : pullback.fst (ιX ≫ f) t ≫ fw = pullback.snd (ιX ≫ f) t ≫ s := by
    rw [← cancel_mono ιY, Category.assoc, Scheme.Hom.resConnectedComponent_comp_ι, Category.assoc]
    exact pullback.condition
  have hc' : (pullback.fst fw s ≫ ιX) ≫ f = pullback.snd fw s ≫ t := by
    rw [Category.assoc, ← Scheme.Hom.resConnectedComponent_comp_ι, ← Category.assoc,
      pullback.condition, Category.assoc]
  let θ : pullback (ιX ≫ f) t ≅ pullback fw s :=
    { hom := pullback.lift _ _ hc
      inv := pullback.lift (pullback.fst fw s) (pullback.snd fw s)
        (by rw [← Category.assoc]; exact hc')
      hom_inv_id := by
        apply pullback.hom_ext
        · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst, Category.id_comp]
        · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd, Category.id_comp]
      inv_hom_id := by
        apply pullback.hom_ext
        · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst, Category.id_comp]
        · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd, Category.id_comp] }
  have hθq : θ.hom ≫ opensPullbackComparison f (X.connectedComponentOpens w)
      (Y.connectedComponentOpens (f.continuous.connectedComponentsMap w)) fw
      (Scheme.Hom.resConnectedComponent_comp_ι f w) s =
      bivariantPushforwardBaseChange ιX f t := by
    apply pullback.hom_ext
    · rw [Category.assoc, opensPullbackComparison_fst, bivariantPushforwardBaseChange_fst]
      exact pullback.lift_fst_assoc _ _ _ _
    · rw [Category.assoc, opensPullbackComparison_snd, bivariantPushforwardBaseChange_snd]
      exact pullback.lift_snd _ _ _
  have hθs : θ.hom ≫ (pullback.fst fw s ≫ (ιX ≫ sX)) = pullback.fst (ιX ≫ f) t ≫ (ιX ≫ sX) := by
    rw [← Category.assoc]
    exact congrArg (· ≫ (ιX ≫ sX)) (pullback.lift_fst _ _ _)
  have : IsIso θ.hom := Iso.isIso_hom θ
  rw [chowGroupRestrict_properChowPushforward C _ _ _ _ (bivariantPushforwardBaseChange ιX f t) _
    (𝟙 _) (Category.id_comp _) _ _ θ.hom hθs
    (IsPullback.of_horiz_isIso_mono ⟨by rw [Category.id_comp, hθq]⟩) _ _
    (properPushforwardFactorsThroughRationalEquivalence_of_isIso C _ _ θ.hom hθs _),
    chowGroupRestrict_id, properChowPushforward_eq_chowPushforwardOfIso, bivariantTransport_cap,
    bivariantTransportCap_apply, chowPushforwardOfIso_comp_apply]
  let ψ : S ≅ pullback ιY t :=
    { hom := pullback.lift s (𝟙 S) (Category.id_comp _).symm
      inv := pullback.snd ιY t
      hom_inv_id := pullback.lift_snd _ _ _
      inv_hom_id := by
        apply pullback.hom_ext
        · rw [Category.assoc, pullback.lift_fst, Category.id_comp, ← cancel_mono ιY,
            Category.assoc]
          exact pullback.condition.symm
        · rw [Category.assoc, pullback.lift_snd, Category.comp_id, Category.id_comp] }
  have : IsIso ψ.hom := Iso.isIso_hom ψ
  apply eq_of_heq
  refine (chowPushforwardOfIso_heq_congr C _ _ _ _ (by simp) _ _
    (BivariantClass.copy_cap C _ _ _ _ _ _ _ _ t k _)).trans ?_
  refine (chowPushforwardOfIso_heq_congr C _ _ _ _ (by simp) _ _
    (openImmersionComposite_cap_heq C _ _ _ _ _ _ _ _ b t k _)).trans (heq_of_eq ?_)
  have hγ : chowGroupRestrict C (t ≫ sY) (pullback.fst ιY t ≫ (ιY ≫ sY)) (pullback.snd ιY t)
      (pullbackSnd_comp_structureMorphism rfl t) k
        (chowGroupCongr C (Category.assoc s ιY sY).symm k β) =
      chowPushforwardOfIso C (t ≫ sY) (pullback.fst ιY t ≫ (ιY ≫ sY)) ψ.hom
        (by rw [pullback.lift_fst_assoc]; exact (Category.assoc _ _ _).symm) k
        (chowGroupCongr C (Category.assoc s ιY sY).symm k β) :=
    chowGroupRestrict_eq_chowPushforwardOfIso_inv C _ _ ψ.symm _ k _
  rw [chowPushforwardOfIso_comp_apply, hγ,
    BivariantClass.cap_chowPushforwardOfIso b (pullback.fst ιY t) ψ.hom s
      (pullback.lift_fst _ _ _) (t ≫ sY) (Category.assoc s ιY sY) k _ _ β
      (by rw [chowGroupCongr_chowGroupCongr]; rfl),
    chowPushforwardOfIso_comp_apply]
  refine eq_of_heq (chowPushforwardOfIso_heq_of_eq_id _ ?_ _ _)
  apply pullback.hom_ext
  · have h₁ : θ.hom ≫ pullback.fst fw s = pullback.fst (ιX ≫ f) t := pullback.lift_fst _ _ _
    rw [Category.assoc, Category.assoc, Category.assoc, h₁, transportPullbackIso_hom_fst,
      Iso.refl_hom, Category.comp_id, pullbackRightPullbackFstIso_hom_fst,
      testBaseChangeIso_hom_fst, Category.id_comp]
  · have h₁ : θ.hom ≫ pullback.snd fw s = pullback.snd (ιX ≫ f) t := pullback.lift_snd _ _ _
    rw [Category.assoc, Category.assoc, Category.assoc, h₁, transportPullbackIso_hom_snd,
      pullbackRightPullbackFstIso_hom_snd, ← Category.assoc, testBaseChangeIso_hom_snd,
      Category.assoc, Category.id_comp]
    exact (congrArg (pullback.snd fw s ≫ ·) ψ.hom_inv_id).trans (Category.comp_id _)

end ComponentExtension

/-! ### Completed classes commuting with every class after every base change -/

section Completed

variable (C : ChowSituation.{u}) {X Y : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (f : X ⟶ Y) [LocallyOfFiniteType f]
  (hf : f ≫ sY = sX) [IsLocallyNoetherian X] [IsLocallyNoetherian Y]

/-- A completed class `c ∈ A^*(X ⟶ Y)^∧` (Stacks 0FE0) *commutes with every class after every
base change* when every term of the tuple attached to it does. By
`Stacks.Chow.completedCommutesAfterBaseChange.completedCommutesWithEveryClass_restriction` its
restriction along any `h : Y' ⟶ Y` (Stacks 0F9Z) then commutes with every bivariant class over
`Y'`, which is what Stacks 0FF6 asserts of the Gysin map of a local complete intersection
morphism. -/
def completedCommutesAfterBaseChange
    (c : completedBivariantGroup C (gysinSystemOfInvertible C) sX sY f hf) : Prop :=
  ∀ n : ℤ, (completedBivariantSequenceOfInvertible C sX sY f hf c n).CommutesAfterBaseChange

variable {C sX sY f hf} in
/-- **The restriction of a completed class commuting with every class after every base change
commutes with every class** (Stacks 0FA2 on Stacks 0FE0). -/
theorem completedCommutesAfterBaseChange.completedCommutesWithEveryClass_restriction
    {c : completedBivariantGroup C (gysinSystemOfInvertible C) sX sY f hf}
    (hc : completedCommutesAfterBaseChange C sX sY f hf c) {Y' : Scheme.{u}} (h : Y' ⟶ Y)
    [LocallyOfFiniteType h] [IsLocallyNoetherian Y'] [IsLocallyNoetherian (pullback f h)] :
    completedCommutesWithEveryClass C (pullback.fst f h ≫ sX) (h ≫ sY) (pullback.snd f h)
      (pullbackSnd_comp_structureMorphism_eq C sX sY f hf h)
      (completedBivariantRestrictionViaSequence C sX sY f hf h c) := fun n ↦ by
  rw [completedBivariantSequenceOfInvertible_completedBivariantRestriction]
  exact hc n h

/-- **Commuting with every class after every base change is checked on the connected
components.** A completed class commutes with every class after every base change as soon as, on
each connected component `X_w` of `X` and in each degree `n`, its component agrees with the
restriction to `X_w` of some homogeneous class of degree `n` that does: on a connected component
of `X ×_Y Y'` lying over `X_w`, the restriction of a class depends only on its restriction to
`X_w` (`Stacks.Chow.bivariantConnectedComponentRestriction_bivariantRestriction_eq_zero`). -/
theorem completedCommutesAfterBaseChange_of_connectedComponent
    (c : completedBivariantGroup C (gysinSystemOfInvertible C) sX sY f hf)
    (H : ∀ (w : _root_.ConnectedComponents X) (n : ℤ),
      ∃ e : BivariantClass C (gysinSystemOfInvertible C) sX sY f hf n,
        e.CommutesAfterBaseChange ∧
          bivariantConnectedComponentRestriction C (gysinSystemOfInvertible C) sX sY f hf n
            (gysinSystemOfInvertible_isNaturalUnderOpenImmersion C) e w = c w n) :
    completedCommutesAfterBaseChange C sX sY f hf c := by
  intro n Y' h _
  have : IsLocallyNoetherian Y' := LocallyOfFiniteType.isLocallyNoetherian (h ≫ sY)
  have : IsLocallyNoetherian (pullback f h) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.fst f h ≫ sX)
  set x := completedBivariantSequenceOfInvertible C sX sY f hf c n
  refine BivariantClass.commutesWithEveryClass_of_connectedComponentRestriction
    (gysinSystemOfInvertible_isNaturalUnderOpenImmersion C) _ fun j ↦ ?_
  obtain ⟨e, he, hew⟩ := H ((pullback.fst f h).continuous.connectedComponentsMap j) n
  refine ⟨_, he h, ?_⟩
  have hx : bivariantConnectedComponentRestriction C (gysinSystemOfInvertible C) sX sY f hf n
      (gysinSystemOfInvertible_isNaturalUnderOpenImmersion C) x
        ((pullback.fst f h).continuous.connectedComponentsMap j) =
      c ((pullback.fst f h).continuous.connectedComponentsMap j) n :=
    restriction_completedBivariantSequence C (gysinSystemOfInvertible C) sX sY f hf _ _ _ c n _
  have h0 := bivariantConnectedComponentRestriction_bivariantRestriction_eq_zero C
    (gysinSystemOfInvertible C) sX sY f hf h n
    (gysinSystemOfInvertible_isNaturalUnderOpenImmersion C)
    (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) (e - x) j
    (by rw [map_sub, Pi.sub_apply, hew, hx, sub_self])
  rw [sub_eq_add_neg, bivariantRestriction_add, bivariantRestriction_neg, map_add, map_neg,
    Pi.add_apply, Pi.neg_apply, ← sub_eq_add_neg, sub_eq_zero] at h0
  exact h0

/-- **Commuting with every class after every base change is checked on the components
themselves.** A completed class commutes with every class after every base change as soon as each
of its components `c_{w,n} ∈ A^n(X_w ⟶ Y_{w'})` does: the component extended by zero
(`Stacks.Chow.bivariantComponentExtension`) is a homogeneous class on `X` that does and that
restricts to `c_{w,n}` on `X_w`. -/
theorem completedCommutesAfterBaseChange_of_apply
    (c : completedBivariantGroup C (gysinSystemOfInvertible C) sX sY f hf)
    (H : ∀ (w : _root_.ConnectedComponents X) (n : ℤ), (c w n).CommutesAfterBaseChange) :
    completedCommutesAfterBaseChange C sX sY f hf c :=
  completedCommutesAfterBaseChange_of_connectedComponent C sX sY f hf c fun w n ↦
    ⟨_, (H w n).bivariantComponentExtension,
      bivariantConnectedComponentRestriction_bivariantComponentExtension C sX sY f hf w _⟩

/-- Completed classes for equal morphisms: commuting with every class after every base change is
invariant under `Stacks.Chow.completedBivariantGroup.copy`. -/
theorem completedCommutesAfterBaseChange_copy {f' : X ⟶ Y} [LocallyOfFiniteType f']
    (hff' : f = f') (hf' : f' ≫ sY = sX)
    (c : completedBivariantGroup C (gysinSystemOfInvertible C) sX sY f hf) :
    completedCommutesAfterBaseChange C sX sY f' hf' (completedBivariantGroup.copy C hff' hf hf' c) ↔
      completedCommutesAfterBaseChange C sX sY f hf c := by
  subst hff'
  rfl

/-- **The completed composite of classes commuting with every class after every base change does
too.** On a connected component `X_w` the degree `n` part of `c ∘ d` is the restriction of the
finite sum `∑_p c_p ∘ d_{n-p}` of homogeneous composites
(`Stacks.Chow.bivariantConnectedComponentRestriction_sum_bivariantCompositeOfInvertible`). -/
theorem completedCommutesAfterBaseChange_completedBivariantCompositeOfInvertible {Z : Scheme.{u}}
    (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ] (g : Y ⟶ Z) [LocallyOfFiniteType g]
    (hg : g ≫ sZ = sY) [IsLocallyNoetherian Z]
    (c : completedBivariantGroup C (gysinSystemOfInvertible C) sX sY f hf)
    (d : completedBivariantGroup C (gysinSystemOfInvertible C) sY sZ g hg)
    (hc : completedCommutesAfterBaseChange C sX sY f hf c)
    (hd : completedCommutesAfterBaseChange C sY sZ g hg d) :
    completedCommutesAfterBaseChange C sX sZ (f ≫ g) (comp_comp_structureMorphism_eq hf hg)
      (completedBivariantCompositeOfInvertible C sX sY sZ f g hf hg c d) := by
  classical
  refine completedCommutesAfterBaseChange_of_connectedComponent C sX sZ (f ≫ g) _ _
    fun w n ↦ ⟨_, BivariantClass.commutesAfterBaseChange_sum _ _ fun p _ ↦
      (BivariantClass.commutesAfterBaseChange_copy rfl _ _ _).2
        ((hc p).bivariantCompositeOfInvertible (hd (n - p))),
      bivariantConnectedComponentRestriction_sum_bivariantCompositeOfInvertible C sX sY f hf sZ g
        hg c d w n (c w).support fun _ hp ↦ DFinsupp.mem_support_iff.2 hp⟩

/-- **The completed smooth pullback commutes with every class after every base change**: its
restriction is the completed flat pullback of the base change
(`Stacks.Chow.completedBivariantRestriction_completedFlatPullbackOfSmooth`), which commutes with
every class. -/
theorem completedCommutesAfterBaseChange_completedFlatPullbackOfSmooth [Smooth f] :
    completedCommutesAfterBaseChange C sX sY f hf (completedFlatPullbackOfSmooth C sX sY f hf) :=
  fun n Y' h _ ↦ by
    have : IsLocallyNoetherian Y' := LocallyOfFiniteType.isLocallyNoetherian (h ≫ sY)
    have : IsLocallyNoetherian (pullback f h) :=
      LocallyOfFiniteType.isLocallyNoetherian (pullback.fst f h ≫ sX)
    rw [← completedBivariantSequenceOfInvertible_completedBivariantRestriction,
      completedBivariantRestriction_completedFlatPullbackOfSmooth]
    exact completedCommutesWithEveryClass_completedFlatPullbackOfSmooth C _ _ _ _ n

/-- **The completed flat pullback of an open immersion commutes with every class after every base
change**: each of its components is the flat pullback of an open immersion. -/
theorem completedCommutesAfterBaseChange_completedFlatPullbackOfIsOpenImmersion
    [IsOpenImmersion f] :
    completedCommutesAfterBaseChange C sX sY f hf
      (completedFlatPullbackOfIsOpenImmersion C sX sY f hf) := by
  refine completedCommutesAfterBaseChange_of_apply C sX sY f hf _ fun w n ↦ ?_
  rw [completedFlatPullbackOfIsOpenImmersion_apply]
  exact commutesAfterBaseChange_directSum_of _
    (commutesAfterBaseChange_flatPullbackBivariantClassOfIsOpenImmersionOfInvertible C _ _ _ _) n

end Completed

/-! ### The completed class of a virtual normal bundle -/

section VirtualNormal

variable (C : ChowSituation.{u}) {Z X : Scheme.{u}} (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ]
  (sX : X ⟶ C.S) [LocallyOfFiniteType sX] [IsLocallyNoetherian Z] [IsLocallyNoetherian X]

/-- **The class `c(Z ⟶ X, 𝒩) ∈ A^*(Z ⟶ X)^∧` of a virtual normal bundle commutes with every class
after every base change** (Stacks 0FBP with Stacks 0FBJ, on Stacks 0FE0): on a connected component
`Z_a` it is `c(Z_a ⟶ U_a, 𝒩|_{Z_a}) ∘ (U_a ⟶ X_b)^*`, a composite of a class of constant rank,
whose restrictions are classes of base-changed virtual normal bundles, with a flat pullback. -/
theorem completedCommutesAfterBaseChange_completedVirtualNormalGysinClass (i : Z ⟶ X)
    [IsClosedImmersion i] (hi : i ≫ sX = sZ) (𝒩 : VirtualNormalBundle i) :
    completedCommutesAfterBaseChange C sZ sX i hi
      (completedVirtualNormalGysinClass C sZ sX i hi 𝒩) := by
  refine completedCommutesAfterBaseChange_of_apply C sZ sX i hi _ fun a n ↦ ?_
  rw [completedVirtualNormalGysinClass_apply]
  exact commutesAfterBaseChange_directSum_of _
    ((BivariantClass.commutesAfterBaseChange_copy _ _ _ _).2
      (BivariantClass.CommutesAfterBaseChange.bivariantCompositeOfInvertible
        (commutesAfterBaseChange_virtualNormalGysinClass C _ _ _ _ _ _)
        (commutesAfterBaseChange_flatPullbackBivariantClassOfIsOpenImmersionOfInvertible C _ _
          _ _)))
    n

/-- **The class `c(Z ⟶ X, 𝒩) ∈ A^*(Z ⟶ X)^∧` of a virtual normal bundle for an immersion commutes
with every class after every base change** (Stacks 0FBQ (3)): it is the composite of the class of
the closed factor `Z ⟶ U` with the flat pullback along the open immersion `U ⟶ X`. -/
theorem completedCommutesAfterBaseChange_completedVirtualNormalGysinClassOfOpen (i : Z ⟶ X)
    [IsImmersion i] (hi : i ≫ sX = sZ) (U : X.Opens) (i' : Z ⟶ U.toScheme) [IsClosedImmersion i']
    (hU : i' ≫ U.ι = i) (𝒩 : VirtualNormalBundle i) :
    completedCommutesAfterBaseChange C sZ sX i hi
      (completedVirtualNormalGysinClassOfOpen C sZ sX i hi U i' hU 𝒩) := by
  have : IsLocallyNoetherian U.toScheme := LocallyOfFiniteType.isLocallyNoetherian (U.ι ≫ sX)
  exact (completedCommutesAfterBaseChange_copy C sZ sX _ _ _ _ _).2
    (completedCommutesAfterBaseChange_completedBivariantCompositeOfInvertible C sZ (U.ι ≫ sX) i'
      _ sX U.ι rfl _ _
      (completedCommutesAfterBaseChange_completedVirtualNormalGysinClass C sZ (U.ι ≫ sX) i' _ _)
      (completedCommutesAfterBaseChange_completedFlatPullbackOfIsOpenImmersion C _ sX U.ι rfl))

/-- The class of a virtual normal bundle for an immersion, at the canonical open, commutes with
every class after every base change. -/
theorem completedCommutesAfterBaseChange_completedVirtualNormalGysinClassOfImmersion (i : Z ⟶ X)
    [IsImmersion i] (hi : i ≫ sX = sZ) (𝒩 : VirtualNormalBundle i) :
    completedCommutesAfterBaseChange C sZ sX i hi
      (completedVirtualNormalGysinClassOfImmersion C sZ sX i hi 𝒩) :=
  completedCommutesAfterBaseChange_completedVirtualNormalGysinClassOfOpen C sZ sX i hi _ _ _ 𝒩

end VirtualNormal

end Stacks.Chow

end
