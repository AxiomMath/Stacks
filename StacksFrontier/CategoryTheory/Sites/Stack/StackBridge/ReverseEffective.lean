module

public import StacksFrontier.CategoryTheory.Sites.Stack.StackBridge.ReverseDescent

/-!
# Condition (3) of Stacks 026F from condition (3) of Stacks 02ZI

`CategoryTheory.Functor.SieveDescentDatum.toFamilyDatum`
(`StacksFrontier/CategoryTheory/Sites/Stack/StackBridge/ReverseDescent.lean`) reads a sieve-indexed
descent datum as a descent datum relative to the tautological covering family of the sieve — the
family of all of its arrows. This file transports *effectivity* back across that reading, which is
the last step of the reverse stack bridge: condition (3) of Stacks 02ZI gives condition (3) of
Stacks 026F, and with `CategoryTheory.Functor.isMorSheaf_of_isStackInGroupoids` all three
conditions of 026F follow from those of 02ZI.

## Method

Effectivity of a sieve-indexed datum asks for an object `a` of the fibre over `U` and a cartesian
morphism `D.obj f ⟶ a` for every arrow `f` of the sieve, compatible with the gluing isomorphisms
of the datum over an *arbitrary* object mapping into two of the sources. The family-indexed
effectivity supplies the morphisms — every arrow of the sieve is a member of the tautological
family, so the restriction of the descended object at that arrow together with the fibre
isomorphism onto the object of the datum is one — and the compatibility over the *chosen* fibre
products only.

The gap between the two compatibilities is closed by the base-change axiom
`CategoryTheory.Functor.SieveDescentDatum.iso_pullback`, not by any gluing: a pair of morphisms
`ε`, `ε'` into two sources agreeing over the base factors through the chosen fibre product by
`CategoryTheory.Limits.pullback.lift`, and the gluing isomorphism at `(ε, ε')` is then the base
change of the gluing isomorphism at the two projections. So the condition at the chosen fibre
products *implies* the condition at an arbitrary pair, which is
`CategoryTheory.Functor.SieveDescentDatum.descent_compat_baseChange` below. No refinement of the
covering, no coverage reduction and no sheaf condition on the morphism presheaves is used.

## Main results

* `CategoryTheory.Functor.SieveDescentDatum.isEffective_of_chosenOverlaps` and
  `CategoryTheory.Functor.SieveDescentDatum.isEffective_of_arrowIndex`: a family of cartesian
  morphisms compatible with the gluing isomorphisms over the chosen fibre products alone already
  makes a sieve-indexed descent datum effective.
* `CategoryTheory.Functor.SieveDescentDatum.isEffective_of_toFamilyDatum`: effectivity of
  `CategoryTheory.Functor.SieveDescentDatum.toFamilyDatum` gives effectivity of the datum itself.
* `CategoryTheory.Functor.hasEffectiveDescent_of_isStackInGroupoids`: condition (3) of Stacks 026F
  from condition (3) of Stacks 02ZI.
* `CategoryTheory.Functor.isStack_of_isStackInGroupoids`: all three conditions of Stacks 026F from
  those of Stacks 02ZI, over a base with fibre products and at index universe `max u₁ v₁`.

## Implementation notes

The data of `CategoryTheory.Functor.DescentDatum.IsEffective` for
`CategoryTheory.Functor.SieveDescentDatum.toFamilyDatum` is phrased through the projections of
that definition, while the data of
`CategoryTheory.Functor.SieveDescentDatum.IsEffective` is phrased through `D.obj` itself. The two
are definitionally equal but the equality needs `toFamilyDatum` to unfold, so the composites
below are not type-correct at the `implicit` transparency level and `rw` stops matching silently.
`toFamilyDatum` is therefore made `implicit_reducible` for this file, and the translation between
the two spellings is confined to `isEffective_of_toFamilyDatum`: the abstract criterion
`isEffective_of_arrowIndex` mentions neither `toFamilyDatum` nor the arrow-to-index comparison.

*Universes.* The object universes and the two hom universes are independent: the hom universe of
the total category `𝒳` is unrelated to that of the base `𝒞`. The index universe at which the
conditions of Stacks 02ZI are consumed is `max u₁ v₁`, built from the base alone — it is the
universe of the type of arrows of a sieve on an object of `𝒞` — so it is unaffected.

## Tagging

Nothing here carries a `@[stacks]` attribute, for the reason recorded in the module docstring of
`StacksFrontier/CategoryTheory/Sites/Stack/StackBridge/Reverse.lean`: `@[stacks 02ZJ]` is attached
to `CategoryTheory.Functor.stackInGroupoids_tfae`, whose clause (1) is a sieve-phrased rendering of
Stacks 02ZI rather than `CategoryTheory.Functor.IsStackInGroupoids`, and the implication proved
here carries two extra hypotheses — fibre products in the base, and the index universe
`max u₁ v₁` — so it is a bridge rather than the tagged statement.

## References

* [Stacks 026F](https://stacks.math.columbia.edu/tag/026F)
* [Stacks 02ZI](https://stacks.math.columbia.edu/tag/02ZI)
* [Stacks 02ZJ](https://stacks.math.columbia.edu/tag/02ZJ)
-/

@[expose] public section

namespace CategoryTheory

open Limits Opposite

universe v₁ v₂ u₁ u₂

namespace Functor

attribute [local implicit_reducible] Fiber Fiber.fiberInclusion pullbackRestriction
  Restriction.ofCartesian

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞] {𝒳 : Type u₂} [Category.{v₂} 𝒳]
variable {p : 𝒳 ⥤ 𝒞} [p.IsFibered]

/-! ### Two readings of the chosen pullback -/

/-- The canonical comparison of the chosen pullback of `y` along `g`, read as a restriction of `y`
along `g`, with `y` itself read as a restriction along the identity, is the chosen cartesian lift
of `g`. This is the shape in which the compatibility clauses of
`CategoryTheory.Functor.DescentDatum.IsEffective` present their canonical restrictions: they
compare a restriction of the descended object with `CategoryTheory.Functor.Restriction.id` of an
object of the datum. -/
lemma compTo_id_pullbackRestriction {V W : 𝒞} (y : p.Fiber V) (g : W ⟶ V) (hg : g = g ≫ 𝟙 V) :
    Restriction.compTo p g (𝟙 V) hg (Restriction.id p y.1 y.2) (pullbackRestriction y g) =
      IsPreFibered.pullbackMap y.2 g := by
  have hc := IsPreFibered.pullbackMap.IsCartesian y.2 g
  have hh : p.IsHomLift g (IsPreFibered.pullbackMap y.2 g) := inferInstance
  refine (Restriction.eq_compTo g (𝟙 V) hg (Restriction.id p y.1 y.2) (pullbackRestriction y g)
    (IsPreFibered.pullbackMap y.2 g) ?_ ?_).symm
  · exact hh
  · exact Category.comp_id _

omit [p.IsFibered] in
/-- The inverse of an invertible morphism of a fibre lies over the identity. Writing it as
`(CategoryTheory.asIso φ).symm.hom` rather than as `CategoryTheory.inv φ` is what lets
`CategoryTheory.IsCartesian.of_iso_comp` fire on a composite beginning with it. -/
lemma isHomLift_asIso_symm_hom {V : 𝒞} {b c : 𝒳} {hb : p.obj b = V} {hc : p.obj c = V}
    {φ : b ⟶ c} (hφ : FibreHom p b c hb hc φ) (hι : IsIso φ) :
    p.IsHomLift (𝟙 V) (asIso φ).symm.hom :=
  (fibreIsoMk hφ hι).inv.2

/-! ### The compatibility condition over an arbitrary pair, from the chosen fibre products -/

namespace SieveDescentDatum

variable {U : 𝒞} {R : Sieve U} (D : SieveDescentDatum p R)

/-- **The compatibility condition of effectivity base-changes.** If a family of morphisms from the
objects of a sieve-indexed descent datum to an object `a` of the fibre over `U` is compatible with
the gluing isomorphism at a pair `(ε, ε')`, it is compatible with the gluing isomorphism at
`(γ ≫ ε, γ ≫ ε')`. The only input is the base-change axiom
`CategoryTheory.Functor.SieveDescentDatum.iso_pullback` of the datum, which expresses the gluing
isomorphism at the composed pair as the base change along `γ` of the one at `(ε, ε')`. -/
lemma descent_compat_baseChange {a : p.Fiber U}
    (ζ : ∀ ⦃V : 𝒞⦄ (f : V ⟶ U) (hf : R.arrows f), (D.obj f hf).1 ⟶ a.1) ⦃V W Z Z' : 𝒞⦄
    ⦃f : V ⟶ U⦄ (hf : R.arrows f) ⦃g : W ⟶ U⦄ (hg : R.arrows g) (ε : Z ⟶ V) (ε' : Z ⟶ W)
    (heq : ε ≫ f = ε' ≫ g) (γ : Z' ⟶ Z)
    (hcond : Fiber.fiberInclusion.map (D.iso hf hg ε ε' heq).hom ≫
        IsPreFibered.pullbackMap (D.obj g hg).2 ε' ≫ ζ g hg =
      IsPreFibered.pullbackMap (D.obj f hf).2 ε ≫ ζ f hf) :
    Fiber.fiberInclusion.map (D.iso hf hg (γ ≫ ε) (γ ≫ ε')
          (by rw [Category.assoc, Category.assoc, heq])).hom ≫
        IsPreFibered.pullbackMap (D.obj g hg).2 (γ ≫ ε') ≫ ζ g hg =
      IsPreFibered.pullbackMap (D.obj f hf).2 (γ ≫ ε) ≫ ζ f hf := by
  rw [← D.iso_pullback hf hg ε ε' heq γ]
  simp only [Functor.map_comp, Category.assoc, pullbackFiberIso_hom]
  rw [pullbackFiberCompIso_hom_fac_assoc, pullbackFiberHom_fac_assoc, hcond,
    pullbackFiberCompIso_inv_fac_assoc]

/-- **A sieve-indexed descent datum is effective as soon as a family of cartesian morphisms out of
its objects is compatible with its gluing isomorphisms over the chosen fibre products.** The
compatibility that effectivity asks for quantifies over an arbitrary object mapping into two of
the sources; such a pair of morphisms factors through the chosen fibre product by
`CategoryTheory.Limits.pullback.lift`, and
`CategoryTheory.Functor.SieveDescentDatum.descent_compat_baseChange` propagates the condition
along that factorization. -/
theorem isEffective_of_chosenOverlaps [HasPullbacks 𝒞] (a : p.Fiber U)
    (ζ : ∀ ⦃V : 𝒞⦄ (f : V ⟶ U) (hf : R.arrows f), (D.obj f hf).1 ⟶ a.1)
    (hcart : ∀ ⦃V : 𝒞⦄ (f : V ⟶ U) (hf : R.arrows f), p.IsCartesian f (ζ f hf))
    (hglue : ∀ ⦃V W : 𝒞⦄ ⦃f : V ⟶ U⦄ (hf : R.arrows f) ⦃g : W ⟶ U⦄ (hg : R.arrows g),
      Fiber.fiberInclusion.map (D.iso hf hg (Limits.pullback.fst f g)
            (Limits.pullback.snd f g) Limits.pullback.condition).hom ≫
          IsPreFibered.pullbackMap (D.obj g hg).2 (Limits.pullback.snd f g) ≫ ζ g hg =
        IsPreFibered.pullbackMap (D.obj f hf).2 (Limits.pullback.fst f g) ≫ ζ f hf) :
    D.IsEffective := by
  refine ⟨a, ζ, hcart, ?_⟩
  intro V W Z f hf g hg ε ε' heq
  obtain ⟨l, hl₁, hl₂⟩ : ∃ l : Z ⟶ Limits.pullback f g,
      l ≫ Limits.pullback.fst f g = ε ∧ l ≫ Limits.pullback.snd f g = ε' :=
    ⟨Limits.pullback.lift ε ε' heq, Limits.pullback.lift_fst _ _ _,
      Limits.pullback.lift_snd _ _ _⟩
  subst hl₁
  subst hl₂
  exact D.descent_compat_baseChange ζ hf hg (Limits.pullback.fst f g)
    (Limits.pullback.snd f g) Limits.pullback.condition l (hglue hf hg)

/-- `CategoryTheory.Functor.SieveDescentDatum.isEffective_of_chosenOverlaps` with the data indexed
by the arrows of the sieve read as the members of its tautological covering family, which is the
form the family-indexed effectivity produces. -/
theorem isEffective_of_arrowIndex [HasPullbacks 𝒞] (a : p.Fiber U)
    (ζ : ∀ i : ArrowIndex R, (D.obj (arrowHom R i) (arrowHom_mem R i)).1 ⟶ a.1)
    (hcart : ∀ i : ArrowIndex R, p.IsCartesian (arrowHom R i) (ζ i))
    (hglue : ∀ i j : ArrowIndex R,
      Fiber.fiberInclusion.map (D.iso (arrowHom_mem R i) (arrowHom_mem R j)
            (Limits.pullback.fst (arrowHom R i) (arrowHom R j))
            (Limits.pullback.snd (arrowHom R i) (arrowHom R j))
            Limits.pullback.condition).hom ≫
          IsPreFibered.pullbackMap (D.obj (arrowHom R j) (arrowHom_mem R j)).2
            (Limits.pullback.snd (arrowHom R i) (arrowHom R j)) ≫ ζ j =
        IsPreFibered.pullbackMap (D.obj (arrowHom R i) (arrowHom_mem R i)).2
          (Limits.pullback.fst (arrowHom R i) (arrowHom R j)) ≫ ζ i) :
    D.IsEffective := by
  refine D.isEffective_of_chosenOverlaps a (fun {_V} f hf => ζ (R.arrows.categoryMk f hf))
    (fun {_V} f hf => hcart (R.arrows.categoryMk f hf)) ?_
  intro V W f hf g hg
  exact hglue (R.arrows.categoryMk f hf) (R.arrows.categoryMk g hg)

/-- **Effectivity transports back across
`CategoryTheory.Functor.SieveDescentDatum.toFamilyDatum`.** This is the whole remaining content of
the reverse stack bridge.

The tautological covering family of the sieve has *every* arrow of the sieve as a member, so the
family-indexed effectivity already provides a cartesian morphism out of each object of the datum:
the fibre isomorphism `ψ i` onto the restriction `xr i` of the descended object, followed by the
cartesian morphism of that restriction. Its compatibility clause is stated over the chosen fibre
products of the base, which is exactly the hypothesis of
`CategoryTheory.Functor.SieveDescentDatum.isEffective_of_arrowIndex`; the two
canonical-restriction clauses of that compatibility become, through
`CategoryTheory.Functor.compTo_id_pullbackRestriction`, the statements that `ψ i` and `ψ j`
intertwine the chosen cartesian lifts of the two projections with the canonical comparisons of
the restrictions of the descended object, and the descent compatibility `ψir ≫ φ i j = ψjr` then
makes both sides of the condition equal to the cartesian morphism of the restriction of the
descended object to the overlap. -/
theorem isEffective_of_toFamilyDatum [HasPullbacks 𝒞] (h : D.toFamilyDatum.IsEffective) :
    D.IsEffective := by
  obtain ⟨x, hx, xr, ψ, hfib, hiso, hcompat⟩ := h
  -- The family-indexed data is phrased through the projections of `toFamilyDatum`; retyping it
  -- in the spelling of `D.obj` is what keeps the composites below type-correct at the `implicit`
  -- transparency level, where `toFamilyDatum` does not unfold.
  obtain ⟨ψ', hψ'⟩ :
      ∃ ψ' : ∀ i : ArrowIndex R, (xr i).pt ⟶ (D.obj (arrowHom R i) (arrowHom_mem R i)).1,
        ∀ i, ψ' i = ψ i := ⟨ψ, fun _ => rfl⟩
  have hiso' : ∀ i : ArrowIndex R, IsIso (ψ' i) := by
    intro i; rw [hψ' i]; exact hiso i
  have hfib' : ∀ i : ArrowIndex R, FibreHom p (xr i).pt
      (D.obj (arrowHom R i) (arrowHom_mem R i)).1 (xr i).hpt
      (D.obj (arrowHom R i) (arrowHom_mem R i)).2 (ψ' i) := by
    intro i; rw [hψ' i]; exact hfib i
  -- The cartesian morphism attached to an arrow of the sieve, with the one property of it used
  -- below: it absorbs the fibre isomorphism `ψ' i` into the cartesian morphism of `xr i`.
  obtain ⟨ζ, hζcart, hζfac⟩ :
      ∃ ζ : ∀ i : ArrowIndex R, (D.obj (arrowHom R i) (arrowHom_mem R i)).1 ⟶ x,
        (∀ i, p.IsCartesian (arrowHom R i) (ζ i)) ∧ ∀ i, ψ' i ≫ ζ i = (xr i).hom := by
    refine ⟨fun i => (asIso (ψ' i)).symm.hom ≫ (xr i).hom, fun i => ?_, fun i => ?_⟩
    · dsimp only
      have h₁ : p.IsHomLift (𝟙 (arrowSrc R i)) (asIso (ψ' i)).symm.hom :=
        isHomLift_asIso_symm_hom (hfib' i) (hiso' i)
      have h₂ : p.IsCartesian (arrowHom R i) (xr i).hom := (xr i).isCartesian_hom
      have := h₁
      have := h₂
      have h₃ : p.IsCartesian (arrowHom R i) ((asIso (ψ' i)).symm.hom ≫ (xr i).hom) :=
        inferInstance
      exact h₃
    · dsimp only
      have hid : ψ' i ≫ (asIso (ψ' i)).symm.hom = 𝟙 (xr i).pt := (asIso (ψ' i)).hom_inv_id
      rw [← Category.assoc, hid, Category.id_comp]
  refine D.isEffective_of_arrowIndex (Fiber.mk hx) ζ hζcart ?_
  intro i j
  obtain ⟨xrij, ψir, ψjr, -, -, hir, -, hres₁, hres₂, hcomm⟩ := hcompat i j
  -- the two components of the overlap compatibility, retyped and read through the chosen
  -- cartesian lifts of the two projections
  obtain ⟨q, hq⟩ : ∃ q : xrij.pt ⟶ (pullbackFiber p (D.obj (arrowHom R i) (arrowHom_mem R i))
      (Limits.pullback.fst (arrowHom R i) (arrowHom R j))).1, q = ψir := ⟨ψir, rfl⟩
  obtain ⟨q', hq'⟩ : ∃ q' : xrij.pt ⟶ (pullbackFiber p (D.obj (arrowHom R j) (arrowHom_mem R j))
      (Limits.pullback.snd (arrowHom R i) (arrowHom R j))).1, q' = ψjr := ⟨ψjr, rfl⟩
  have hqiso : IsIso q := by rw [hq]; exact hir
  have hcomm' : q ≫ Fiber.fiberInclusion.map (D.iso (arrowHom_mem R i) (arrowHom_mem R j)
      (Limits.pullback.fst (arrowHom R i) (arrowHom R j))
      (Limits.pullback.snd (arrowHom R i) (arrowHom R j)) Limits.pullback.condition).hom =
      q' := by rw [hq, hq']; exact hcomm
  -- reading the canonical restriction clause after `ζ k` gives the cartesian morphism of the
  -- restriction of the descended object to the overlap
  have key : ∀ (k : ArrowIndex R) (g : Limits.pullback (arrowHom R i) (arrowHom R j) ⟶ arrowSrc R k)
      (hg : Limits.pullback.fst (arrowHom R i) (arrowHom R j) ≫ arrowHom R i =
        g ≫ arrowHom R k)
      (r : xrij.pt ⟶ (pullbackFiber p (D.obj (arrowHom R k) (arrowHom_mem R k)) g).1),
      r ≫ Restriction.compTo p g (𝟙 _) (by simp) (Restriction.id p _ (D.obj _ _).2)
          (pullbackRestriction (D.obj (arrowHom R k) (arrowHom_mem R k)) g) =
        Restriction.compTo p g (arrowHom R k) hg (xr k) xrij ≫ ψ' k →
      r ≫ IsPreFibered.pullbackMap (D.obj (arrowHom R k) (arrowHom_mem R k)).2 g ≫ ζ k =
        xrij.hom := by
    intro k g hg r hr
    rw [compTo_id_pullbackRestriction] at hr
    rw [← Category.assoc, hr, Category.assoc, hζfac]
    exact Restriction.compTo_hom p g (arrowHom R k) hg (xr k) xrij
  have hL := key j _ Limits.pullback.condition q' (by rw [hq', hψ' j]; exact hres₂)
  have hR := key i _ rfl q (by rw [hq, hψ' i]; exact hres₁)
  rw [← hcomm', Category.assoc] at hL
  exact (cancel_epi q).1 (hL.trans hR.symm)

end SieveDescentDatum

/-! ### The reverse bridge -/

variable {J : GrothendieckTopology 𝒞}

/-- **Condition (3) of Stacks 026F from condition (3) of Stacks 02ZI.** Over a base with fibre
products, and at index universe `max u₁ v₁`, effectivity of every descent datum relative to a
covering family gives effectivity of every descent datum relative to a covering sieve.

A covering sieve `R` *is* the sieve generated by the family of all of its arrows
(`CategoryTheory.Sieve.ofArrows_category`), whose index type lies in `Type (max u₁ v₁)`; condition
(3) of 02ZI applied to that tautological family gives effectivity of
`CategoryTheory.Functor.SieveDescentDatum.toFamilyDatum`, and
`CategoryTheory.Functor.SieveDescentDatum.isEffective_of_toFamilyDatum` transports it back. -/
theorem hasEffectiveDescent_of_isStackInGroupoids [HasPullbacks 𝒞]
    (h : p.IsStackInGroupoids.{max u₁ v₁} J) : HasEffectiveDescent p J := by
  intro U R hR D
  refine D.isEffective_of_toFamilyDatum ?_
  exact h.effective_descent (SieveDescentDatum.arrowSrc R) (SieveDescentDatum.arrowHom R)
    (by rw [Sieve.ofArrows_category]; exact hR) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _

/-- **The reverse stack bridge: all three conditions of Stacks 026F from those of Stacks 02ZI.**
Over a base with fibre products, and at index universe `max u₁ v₁`, a category fibred in groupoids
which is a stack in groupoids in the sense of Stacks 02ZI is a stack in the sense of Stacks 026F.

Both hypotheses are necessary, for the reasons recorded in the module docstring of
`StacksFrontier/CategoryTheory/Sites/Stack/StackBridge/Reverse.lean`: without fibre products the
conditions of 02ZI say nothing about a covering sieve, and at a smaller index universe they
constrain only the covering families indexed by a type in that universe, which is a strictly
weaker hypothesis. -/
theorem isStack_of_isStackInGroupoids [HasPullbacks 𝒞]
    (h : p.IsStackInGroupoids.{max u₁ v₁} J) : p.IsStack J where
  isFibered := inferInstance
  isMorSheaf := isMorSheaf_of_isStackInGroupoids h
  hasEffectiveDescent := hasEffectiveDescent_of_isStackInGroupoids h

end Functor

end CategoryTheory

end
