module

public import StacksFrontier.CategoryTheory.Sites.Descent.IsStack.LocallyClosedSieve

/-!
# A full subcategory of a stack, closed under pullback and locally closed

Let `p : 𝒳 ⥤ 𝒮` be a stack over a site `(𝒮, J)` and let `P` be an `ObjectProperty` on `𝒳`. If `P`
is closed under strongly cartesian pullback and locally closed, then the restriction of `p` to
the full subcategory cut out by `P` is again a stack. Both conditions are read fibrewise, through
`CategoryTheory.Functor.IsoOverId`: isomorphic to an object of the subcategory in the fibre over
the same object of `𝒮`.

## Main results

* `CategoryTheory.Functor.IsStack.fullSubcategory`: the restriction of `p` to `P` is a stack.
* `CategoryTheory.Functor.SieveDescentDatum.isEffective_of_isEffective_mapι`: a descent datum in
  the full subcategory is effective as soon as its image in `𝒳` is.
* `CategoryTheory.Functor.IsStack.fullSubcategory_of_isClosedUnderIsomorphisms`: the same for a
  subcategory closed under isomorphism, with both conditions read up to isomorphism in `𝒳`.
-/

@[expose] public section

-- Needed throughout: the transfer lemmas below relate `p` and `P.ι ⋙ p`, and the instance
-- arguments of `IsHomLift` and `IsCartesian` are only found after unfolding the composite.
set_option backward.isDefEq.respectTransparency false

namespace CategoryTheory

open Limits Opposite

universe v₁ v₂ u₁ u₂

namespace Functor

variable {𝒮 : Type u₁} [Category.{v₁} 𝒮] {𝒳 : Type u₂} [Category.{v₂} 𝒳]

/-- If `P` is closed under strongly cartesian pullback, the restriction of a stack `p` to the
full subcategory cut out by `P` is a fibred category. -/
theorem isFibered_restrict (p : 𝒳 ⥤ 𝒮) (J : GrothendieckTopology 𝒮) (hp : IsStack p J)
    (P : ObjectProperty 𝒳) (h1 : ClosedUnderStronglyCartesian p P) :
    (restrict p P).IsFibered :=
  have := hp.isFibered
  isFibered_restrict_of_closed p P h1

/-- If `P` is closed under strongly cartesian pullback, the presheaves `Mor(x, y)` of the
restriction of a stack `p` to the full subcategory cut out by `P` are sheaves. -/
theorem isMorSheaf_restrict (p : 𝒳 ⥤ 𝒮) (J : GrothendieckTopology 𝒮) (hp : IsStack p J)
    (P : ObjectProperty 𝒳) (h1 : ClosedUnderStronglyCartesian p P) :
    haveI : (restrict p P).IsFibered := isFibered_restrict p J hp P h1
    ∀ (U : 𝒮) (x y : (restrict p P).Fiber U), IsMorSheaf (restrict p P) J U x y := by
  have := hp.isFibered
  have := isFibered_restrict_of_closed p P h1
  exact fun U x y ↦ (Presheaf.isSheaf_of_iso_iff (morPresheafιIso h1 x y)).2
    (hp.isMorSheaf U (fiberι p P x) (fiberι p P y))

/-- If `P` is closed under strongly cartesian pullback and locally closed, a descent datum in the
full subcategory cut out by `P` is effective as soon as its image in `𝒳` is. -/
theorem SieveDescentDatum.isEffective_of_isEffective_mapι (p : 𝒳 ⥤ 𝒮) (J : GrothendieckTopology 𝒮)
    [p.IsFibered] (P : ObjectProperty 𝒳) (h1 : ClosedUnderStronglyCartesian p P)
    (h3 : LocallyClosed p P J) {U : 𝒮} {R : Sieve U} (hR : R ∈ J U)
    (D : haveI := isFibered_restrict_of_closed p P h1; SieveDescentDatum (restrict p P) R)
    (hD : (SieveDescentDatum.mapι p P h1 D).IsEffective) :
    haveI := isFibered_restrict_of_closed p P h1
    D.IsEffective := by
  have := isFibered_restrict_of_closed p P h1
  obtain ⟨x, ζ, hζcart, hglue⟩ := hD
  have hpull : ∀ i : (Σ V : 𝒮, {f : V ⟶ U // R.arrows f}),
      IsoOverId p P (pullbackFiber p x i.2.val).1 := by
    rintro ⟨V, f, hf⟩
    exact isoOverId_pullbackFiber p P x f (ζ f hf) (hζcart f hf) (D.obj f hf).1.property
  obtain ⟨x', hx'P, e, he⟩ := isoOverId_of_locallyClosed p P J h3 hR x hpull
  rw [show p.obj x.1 = U from x.2] at he
  have hx'U : p.obj x' = U := IsHomLift.codomain_eq p (𝟙 U) e.hom
  refine ⟨⟨⟨x', hx'P⟩, hx'U⟩, fun V f hf => P.fullyFaithfulι.preimage (ζ f hf ≫ e.hom), ?_, ?_⟩
  · intro V f hf
    apply isCartesian_of_isCartesian_map_ι p P f
    rw [P.fullyFaithfulι.map_preimage]
    have := hζcart f hf
    have := he
    simpa using (IsFibered.comp f (𝟙 U) (ζ f hf) e.hom : p.IsCartesian (f ≫ 𝟙 U) _)
  · intro V W Z f hf g hg ε ε' heq
    apply P.ι.map_injective
    have hg' := (pullbackFiberιIso p P h1 (D.obj f hf) ε).hom ≫= hglue hf hg ε ε' heq
    simp only [SieveDescentDatum.mapι_iso, SieveDescentDatum.mapι_obj, Iso.trans_hom,
      Iso.symm_hom, Functor.mapIso_hom, Functor.map_comp,
      fiberInclusion_map_pullbackFiberιFiberIso_hom,
      fiberInclusion_map_pullbackFiberιFiberIso_inv, fiberInclusion_map_fiberιFunctor_map,
      Category.assoc, Iso.hom_inv_id_assoc] at hg'
    simp only [Functor.map_comp, P.fullyFaithfulι.map_preimage, Category.assoc,
      ← pullbackFiberιIso_hom_fac h1]
    exact (reassoc_of% hg') e.hom

/-- If `p` is a stack and `P` is closed under strongly cartesian pullback and locally closed,
descent data for the restriction of `p` to the full subcategory cut out by `P` are effective. -/
theorem hasEffectiveDescent_restrict (p : 𝒳 ⥤ 𝒮) (J : GrothendieckTopology 𝒮) (hp : IsStack p J)
    (P : ObjectProperty 𝒳) (h1 : ClosedUnderStronglyCartesian p P)
    (h3 : haveI : p.IsPreFibered := hp.isFibered.toIsPreFibered; LocallyClosed p P J) :
    haveI : p.IsFibered := hp.isFibered
    haveI := isFibered_restrict_of_closed p P h1
    HasEffectiveDescent (restrict p P) J := by
  have : p.IsFibered := hp.isFibered
  have := isFibered_restrict_of_closed p P h1
  intro U R hR D
  exact SieveDescentDatum.isEffective_of_isEffective_mapι p J P h1 h3 hR D
    (hp.hasEffectiveDescent R hR (SieveDescentDatum.mapι p P h1 D))

/-- Let `p : 𝒳 ⥤ 𝒮` be a stack over the site `(𝒮, J)` and let `P` cut out a full subcategory of
`𝒳`. If `P` is closed under strongly cartesian pullbacks and locally closed, both read fibrewise
through `IsoOverId`, then the restriction of `p` to that full subcategory is a stack. -/
@[stacks 04TU]
theorem IsStack.fullSubcategory (p : 𝒳 ⥤ 𝒮) (J : GrothendieckTopology 𝒮) (hp : IsStack p J)
    (P : ObjectProperty 𝒳) (h1 : ClosedUnderStronglyCartesian p P)
    (h3 : haveI : p.IsPreFibered := hp.isFibered.toIsPreFibered; LocallyClosed p P J) :
    IsStack (Functor.restrict p P) J :=
  have : p.IsPreFibered := hp.isFibered.toIsPreFibered
  { isFibered := isFibered_restrict p J hp P h1
    isMorSheaf := isMorSheaf_restrict p J hp P h1
    hasEffectiveDescent := hasEffectiveDescent_restrict p J hp P h1 h3 }

/-- Let `p : 𝒳 ⥤ 𝒮` be a stack and let `P` cut out a full subcategory of `𝒳` closed under
isomorphism. If `P` is closed under strongly cartesian pullbacks up to isomorphism and locally
closed up to isomorphism, then the restriction of `p` to that full subcategory is a stack. -/
theorem IsStack.fullSubcategory_of_isClosedUnderIsomorphisms (p : 𝒳 ⥤ 𝒮)
    (J : GrothendieckTopology 𝒮) (hp : IsStack p J) (P : ObjectProperty 𝒳)
    [P.IsClosedUnderIsomorphisms] (h1 : ClosedUnderStronglyCartesianUpToIso p P)
    (h3 : haveI : p.IsPreFibered := hp.isFibered.toIsPreFibered; LocallyClosedUpToIso p P J) :
    IsStack (Functor.restrict p P) J :=
  have : p.IsPreFibered := hp.isFibered.toIsPreFibered
  IsStack.fullSubcategory p J hp P ((closedUnderStronglyCartesian_iff_upToIso p P).2 h1)
    ((locallyClosed_iff_upToIso p P J).2 h3)

end Functor

end CategoryTheory
