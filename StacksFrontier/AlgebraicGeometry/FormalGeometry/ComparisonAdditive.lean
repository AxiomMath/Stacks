module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.Product
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.ComparisonShortExact
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.PrincipalFormalLocusTagInjectivity

/-!
# Additivity of the comparison map of Stacks 0EG2, and its sharpened short exact sequence

Let `I ⊆ 𝔞` be ideals of a Noetherian ring `A` and let `U = Spec(A) ∖ V(𝔞)`. The comparison map
`Stacks.Algebraization.comparisonMap A I a F` of Stacks 0EG2 goes from the colimit of the
sections of `F` over the open neighbourhoods of `U ∩ V(I)` to the limit of the sections of the
quotients `F / Iⁿ F` on all of `U`. Both sides are functors of `F` and the comparison is natural
in `F`; this file records that both sides are moreover *additive* in the morphism, and draws the
two consequences that a criterion for the comparison to be an isomorphism needs.

The first consequence is that the comparison for a biproduct is an isomorphism as soon as the
comparisons for the two summands are, and hence that it is an isomorphism for a finite direct sum
of copies of a module for which it is one. The second is a sharpening of Stacks 0H48: in the
ladder attached to a short exact sequence `0 → F' → F → F'' → 0`, the comparison for `F''` need
only be *injective* for the argument to run, and injectivity holds for every coherent module with
no further hypothesis, by `Stacks.Algebraization.mono_comparisonMap`. So the comparison for `F'`
is an isomorphism as soon as the comparison for `F` is — the hypothesis on `F''` can be dropped
outright.

## Main results

* `Stacks.Algebraization.formalSectionsMap_add` and
  `Stacks.Algebraization.sectionsNearVanishingMap_add` — the two sides of the comparison are
  additive in the morphism.
* `Stacks.Algebraization.limMap_formalSectionsMap_comp` and
  `Stacks.Algebraization.colimMap_sectionsNearVanishingMap_comp` — and functorial.
* `Stacks.Algebraization.isIso_comparisonMap_biprod` and
  `Stacks.Algebraization.isIso_comparisonMap_bicone` — the comparison for a binary and for a
  finite biproduct.
* `Stacks.Algebraization.isIso_comparisonMap_of_mono` — the comparison for a submodule of a
  module whose comparison is an isomorphism.
* `Stacks.Algebraization.isIso_comparisonMap_first_of_middle` — **Stacks 0H48, the first
  comparison, with the hypothesis on the third term removed.**

## Implementation notes

Additivity of the quotient map `F / Iⁿ F ⟶ G / Iⁿ G` is
`Stacks.Algebraization.idealPowerQuotientMap_add`; the additivity of the two induced maps on the
limit and the colimit then follows from `CategoryTheory.Limits.limMap_π` and
`CategoryTheory.Limits.ι_colimMap` together with the preadditivity of `Ab`.

The surjectivity argument for a biproduct is the usual one: a formal section `w` of `F ⊞ G` is
split by the two projections into formal sections of `F` and of `G`, each of which is realized
near the formal locus, and the two realizations are recombined along the two inclusions. The
recombination is the total relation `biprod.total`, which is where additivity is consumed.

## References

* [Stacks Project, Tag 0EG2](https://stacks.math.columbia.edu/tag/0EG2)
* [Stacks Project, Tag 0H48](https://stacks.math.columbia.edu/tag/0H48)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace Stacks.Algebraization

open Stacks.LocalCohomology

/-! ### Additivity and functoriality of the two sides of the comparison -/

variable (A : Type u) [CommRing A] (I a : Ideal A)

/-- The inverse system of sections of the ideal-power quotients is additive in the morphism. -/
theorem formalSectionsMap_add {F G : (complementZeroLocus A a : Scheme).Modules} (f g : F ⟶ G) :
    formalSectionsMap A I a (f + g) =
      formalSectionsMap A I a f + formalSectionsMap A I a g := by
  refine NatTrans.ext (funext fun n => ?_)
  rw [formalSectionsMap_app A I a, idealPowerQuotientMap_add]
  rfl

/-- The inverse system of sections of the ideal-power quotients is functorial. -/
theorem formalSectionsMap_comp {F G H : (complementZeroLocus A a : Scheme).Modules}
    (f : F ⟶ G) (g : G ⟶ H) :
    formalSectionsMap A I a (f ≫ g) =
      formalSectionsMap A I a f ≫ formalSectionsMap A I a g := by
  refine NatTrans.ext (funext fun n => ?_)
  rw [formalSectionsMap_app A I a, idealPowerQuotientMap_comp]
  rfl

/-- The inverse system of sections of the ideal-power quotients sends the identity to the
identity. -/
theorem formalSectionsMap_id (F : (complementZeroLocus A a : Scheme).Modules) :
    formalSectionsMap A I a (𝟙 F) = 𝟙 _ := by
  refine NatTrans.ext (funext fun n => ?_)
  rw [formalSectionsMap_app A I a, idealPowerQuotientMap_id]
  rfl

/-- The diagram of sections near the formal locus is additive in the morphism. -/
theorem sectionsNearVanishingMap_add {F G : (complementZeroLocus A a : Scheme).Modules}
    (f g : F ⟶ G) :
    sectionsNearVanishingMap A I a (f + g) =
      sectionsNearVanishingMap A I a f + sectionsNearVanishingMap A I a g :=
  NatTrans.ext (funext fun _ => rfl)

/-- The diagram of sections near the formal locus is functorial. -/
theorem sectionsNearVanishingMap_comp {F G H : (complementZeroLocus A a : Scheme).Modules}
    (f : F ⟶ G) (g : G ⟶ H) :
    sectionsNearVanishingMap A I a (f ≫ g) =
      sectionsNearVanishingMap A I a f ≫ sectionsNearVanishingMap A I a g :=
  NatTrans.ext (funext fun _ => rfl)

/-- The diagram of sections near the formal locus sends the identity to the identity. -/
theorem sectionsNearVanishingMap_id (F : (complementZeroLocus A a : Scheme).Modules) :
    sectionsNearVanishingMap A I a (𝟙 F) = 𝟙 _ :=
  NatTrans.ext (funext fun _ => rfl)

/-! ### The induced maps on the limit and the colimit -/

/-- The inverse system of sections of the ideal-power quotients sends the zero morphism to
zero. -/
theorem formalSectionsMap_zero (F G : (complementZeroLocus A a : Scheme).Modules) :
    formalSectionsMap A I a (0 : F ⟶ G) = 0 := by
  refine NatTrans.ext (funext fun n => ?_)
  rw [formalSectionsMap_app A I a, idealPowerQuotientMap_zero]
  rfl

/-- The diagram of sections near the formal locus sends the zero morphism to zero. -/
theorem sectionsNearVanishingMap_zero (F G : (complementZeroLocus A a : Scheme).Modules) :
    sectionsNearVanishingMap A I a (0 : F ⟶ G) = 0 :=
  NatTrans.ext (funext fun _ => rfl)

/-- The induced map on the limit of the sections of the ideal-power quotients sends the zero
morphism to zero. -/
theorem limMap_formalSectionsMap_zero (F G : (complementZeroLocus A a : Scheme).Modules) :
    limMap (formalSectionsMap A I a (0 : F ⟶ G)) = 0 := by
  rw [formalSectionsMap_zero, limMap_eq]
  exact Functor.map_zero _ _ _

/-- The induced map on the limit of the sections of the ideal-power quotients is additive. -/
theorem limMap_formalSectionsMap_add {F G : (complementZeroLocus A a : Scheme).Modules}
    (f g : F ⟶ G) :
    limMap (formalSectionsMap A I a (f + g)) =
      limMap (formalSectionsMap A I a f) + limMap (formalSectionsMap A I a g) := by
  refine limit.hom_ext fun n => ?_
  rw [limMap_π, formalSectionsMap_add]
  simp only [NatTrans.app_add, Preadditive.comp_add, Preadditive.add_comp, limMap_π]

/-- The induced map on the limit of the sections of the ideal-power quotients is functorial. -/
theorem limMap_formalSectionsMap_comp {F G H : (complementZeroLocus A a : Scheme).Modules}
    (f : F ⟶ G) (g : G ⟶ H) :
    limMap (formalSectionsMap A I a (f ≫ g)) =
      limMap (formalSectionsMap A I a f) ≫ limMap (formalSectionsMap A I a g) := by
  rw [formalSectionsMap_comp, limMap_eq]
  exact lim.map_comp _ _

/-- The induced map on the limit of the sections of the ideal-power quotients sends the identity
to the identity. -/
theorem limMap_formalSectionsMap_id (F : (complementZeroLocus A a : Scheme).Modules) :
    limMap (formalSectionsMap A I a (𝟙 F)) = 𝟙 _ := by
  rw [formalSectionsMap_id, limMap_eq]
  exact lim.map_id _

/-- The induced map on the colimit of the sections near the formal locus is additive. -/
theorem colimMap_sectionsNearVanishingMap_add
    {F G : (complementZeroLocus A a : Scheme).Modules} (f g : F ⟶ G) :
    colimMap (sectionsNearVanishingMap A I a (f + g)) =
      colimMap (sectionsNearVanishingMap A I a f) +
        colimMap (sectionsNearVanishingMap A I a g) := by
  rw [sectionsNearVanishingMap_add, colimMap_eq]
  exact Functor.map_add _

/-- The induced map on the colimit of the sections near the formal locus is functorial. -/
theorem colimMap_sectionsNearVanishingMap_comp
    {F G H : (complementZeroLocus A a : Scheme).Modules} (f : F ⟶ G) (g : G ⟶ H) :
    colimMap (sectionsNearVanishingMap A I a (f ≫ g)) =
      colimMap (sectionsNearVanishingMap A I a f) ≫
        colimMap (sectionsNearVanishingMap A I a g) := by
  rw [sectionsNearVanishingMap_comp, colimMap_eq]
  exact colim.map_comp _ _

/-- The induced map on the colimit of the sections near the formal locus sends the identity to
the identity. -/
theorem colimMap_sectionsNearVanishingMap_id (F : (complementZeroLocus A a : Scheme).Modules) :
    colimMap (sectionsNearVanishingMap A I a (𝟙 F)) = 𝟙 _ := by
  rw [sectionsNearVanishingMap_id, colimMap_eq]
  exact colim.map_id _

/-! ### Stacks 0H48 with the hypothesis on the third term removed -/

/-- **Stacks 0H48, the first comparison, sharpened.** For a short exact sequence
`0 → F' → F → F'' → 0` of coherent modules on `U = Spec(A) ∖ V(𝔞)` with `A` Noetherian, if the
comparison map of Stacks 0EG2 for `F` is an isomorphism, so is the one for `F'`.

The published statement also assumes the comparison for `F''` to be an isomorphism, but only its
injectivity enters the diagram chase, and that holds for every coherent module with no hypothesis
at all, by `Stacks.Algebraization.mono_comparisonMap`. -/
theorem isIso_comparisonMap_first_of_middle
    [IsNoetherianRing A]
    (S : ShortComplex (complementZeroLocus A a : Scheme).Modules) (hS : S.ShortExact)
    [S.X₁.IsCoherent] [S.X₂.IsCoherent] [S.X₃.IsCoherent]
    (h₂ : IsIso (comparisonMap A I a S.X₂)) :
    IsIso (comparisonMap A I a S.X₁) := by
  have hBf := injective_limMap_formalSectionsMap A I a S.f hS.mono_f
  have hAf := injective_colimMap_sectionsNearVanishingMap A I a S.f hS.mono_f
  have hc₂ := (ConcreteCategory.isIso_iff_bijective (comparisonMap A I a S.X₂)).1 h₂
  have hc₃ : Function.Injective (ConcreteCategory.hom (comparisonMap A I a S.X₃)) :=
    (ConcreteCategory.mono_iff_injective_of_preservesPullback _).1
      (mono_comparisonMap A I a S.X₃)
  rw [ConcreteCategory.isIso_iff_bijective]
  refine ⟨(injective_iff_map_eq_zero _).2 fun z hz => ?_, fun w => ?_⟩
  · have h1 := comparisonMap_apply_colimMap A I a S.f z
    rw [hz, map_zero] at h1
    exact hAf ((hc₂.1 (h1.trans (map_zero _).symm)).trans (map_zero _).symm)
  · obtain ⟨y, hy⟩ := hc₂.2 (ConcreteCategory.hom (limMap (formalSectionsMap A I a S.f)) w)
    have hgy : ConcreteCategory.hom (comparisonMap A I a S.X₃)
        (ConcreteCategory.hom (colimMap (sectionsNearVanishingMap A I a S.g)) y) = 0 := by
      rw [comparisonMap_apply_colimMap A I a S.g y, hy]
      exact limMap_formalSectionsMap_apply_eq_zero A I a S w
    obtain ⟨z, hz⟩ := exists_colimMap_sectionsNearVanishingMap_eq A I a S hS y
      (hc₃ (hgy.trans (map_zero _).symm))
    refine ⟨z, ?_⟩
    have h1 := comparisonMap_apply_colimMap A I a S.f z
    rw [hz, hy] at h1
    exact hBf h1.symm

/-- **A submodule of a module whose comparison map is an isomorphism has the same property.**
A monomorphism `E ⟶ P` of coherent modules on `U = Spec(A) ∖ V(𝔞)` sits in the short exact
sequence `0 → E → P → P/E → 0`, so this is
`Stacks.Algebraization.isIso_comparisonMap_first_of_middle` applied to that sequence. Nothing is
required of the quotient. -/
theorem isIso_comparisonMap_of_mono [IsNoetherianRing A]
    {E P : (complementZeroLocus A a : Scheme).Modules} [E.IsCoherent] [P.IsCoherent]
    (i : E ⟶ P) (hi : Mono (C := (complementZeroLocus A a : Scheme).Modules) i)
    (hP : IsIso (comparisonMap A I a P)) :
    IsIso (comparisonMap A I a E) := by
  have : (ShortComplex.cokernelSequence
      (C := (complementZeroLocus A a : Scheme).Modules) i).X₁.IsCoherent := ‹E.IsCoherent›
  have : (ShortComplex.cokernelSequence
      (C := (complementZeroLocus A a : Scheme).Modules) i).X₂.IsCoherent := ‹P.IsCoherent›
  have : (ShortComplex.cokernelSequence
      (C := (complementZeroLocus A a : Scheme).Modules) i).X₃.IsCoherent :=
    AlgebraicGeometry.CoherentAbelian.isCoherent_cokernel
      (R := (complementZeroLocus A a : Scheme).ringCatSheaf) i
  exact isIso_comparisonMap_first_of_middle A I a _
    { exact := ShortComplex.cokernelSequence_exact i, mono_f := hi } hP

/-! ### The comparison map on a biproduct -/

/-- **The comparison map of Stacks 0EG2 on a biproduct.** If the comparison maps for `F` and `G`
are isomorphisms, so is the comparison map for `F ⊞ G`.

Injectivity is `Stacks.Algebraization.mono_comparisonMap`, which needs nothing. For surjectivity,
a formal section of `F ⊞ G` is projected to formal sections of `F` and of `G`, each of which is
the comparison of a section near the formal locus; the two are recombined along the inclusions,
and `CategoryTheory.Limits.biprod.total` identifies the result with the original. -/
theorem isIso_comparisonMap_biprod [IsNoetherianRing A]
    (F G : (complementZeroLocus A a : Scheme).Modules)
    [F.IsCoherent] [G.IsCoherent]
    [(F ⊞ G : (complementZeroLocus A a : Scheme).Modules).IsCoherent]
    (hF : IsIso (comparisonMap A I a F)) (hG : IsIso (comparisonMap A I a G)) :
    IsIso (comparisonMap A I a (F ⊞ G)) := by
  have hcF := (ConcreteCategory.isIso_iff_bijective (comparisonMap A I a F)).1 hF
  have hcG := (ConcreteCategory.isIso_iff_bijective (comparisonMap A I a G)).1 hG
  rw [ConcreteCategory.isIso_iff_bijective]
  refine ⟨(ConcreteCategory.mono_iff_injective_of_preservesPullback _).1
    (mono_comparisonMap A I a (F ⊞ G)), fun w => ?_⟩
  obtain ⟨zF, hzF⟩ := hcF.2
    (ConcreteCategory.hom (limMap (formalSectionsMap A I a (biprod.fst : F ⊞ G ⟶ F))) w)
  obtain ⟨zG, hzG⟩ := hcG.2
    (ConcreteCategory.hom (limMap (formalSectionsMap A I a (biprod.snd : F ⊞ G ⟶ G))) w)
  refine ⟨ConcreteCategory.hom
      (colimMap (sectionsNearVanishingMap A I a (biprod.inl : F ⟶ F ⊞ G))) zF +
    ConcreteCategory.hom
      (colimMap (sectionsNearVanishingMap A I a (biprod.inr : G ⟶ F ⊞ G))) zG, ?_⟩
  have htot : limMap (formalSectionsMap A I a
        ((biprod.fst : F ⊞ G ⟶ F) ≫ (biprod.inl : F ⟶ F ⊞ G))) +
      limMap (formalSectionsMap A I a
        ((biprod.snd : F ⊞ G ⟶ G) ≫ (biprod.inr : G ⟶ F ⊞ G))) = 𝟙 _ := by
    rw [← limMap_formalSectionsMap_add, biprod.total, limMap_formalSectionsMap_id]
  rw [map_add, comparisonMap_apply_colimMap, comparisonMap_apply_colimMap, hzF, hzG,
    ← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
    ← limMap_formalSectionsMap_comp, ← limMap_formalSectionsMap_comp]
  have := ConcreteCategory.congr_hom htot w
  rw [AddCommGrpCat.hom_add_apply] at this
  simpa using this

/-- **The comparison map of Stacks 0EG2 on a finite biproduct.** If `b` is a bilimit bicone over
a finite family of coherent modules on `U = Spec(A) ∖ V(𝔞)` whose comparison maps are all
isomorphisms, then the comparison map for `b.pt` is an isomorphism.

Injectivity is `Stacks.Algebraization.mono_comparisonMap`, which needs nothing. For surjectivity,
a formal section `w` of `b.pt` is projected along each `b.π i` to a formal section of the `i`-th
summand, which is the comparison of a section `z i` near the formal locus; the sum of the images
of the `z i` along `b.ι i` is the required antecedent, because the two sides of the comparison are
additive in the morphism and `CategoryTheory.Limits.IsBilimit.total` identifies
`∑ i, b.π i ≫ b.ι i` with the identity. The empty family is included: the sum is then the zero
morphism, which is the identity of a zero object.

The family is indexed by a `Fintype` because that is the hypothesis of
`CategoryTheory.Limits.IsBilimit.total`; a `Finite` index type is converted by
`Fintype.ofFinite`. -/
theorem isIso_comparisonMap_bicone [IsNoetherianRing A] {ι : Type*} [Fintype ι]
    {P : ι → (complementZeroLocus A a : Scheme).Modules} [∀ i, (P i).IsCoherent]
    (b : Bicone P) [b.pt.IsCoherent] (hb : b.IsBilimit)
    (hP : ∀ i, IsIso (comparisonMap A I a (P i))) :
    IsIso (comparisonMap A I a b.pt) := by
  classical
  rw [ConcreteCategory.isIso_iff_bijective]
  refine ⟨(ConcreteCategory.mono_iff_injective_of_preservesPullback _).1
    (mono_comparisonMap A I a b.pt), fun w => ?_⟩
  choose z hz using fun i =>
    ((ConcreteCategory.isIso_iff_bijective (comparisonMap A I a (P i))).1 (hP i)).2
      (ConcreteCategory.hom (limMap (formalSectionsMap A I a (b.π i))) w)
  refine ⟨∑ i : ι, ConcreteCategory.hom
      (colimMap (sectionsNearVanishingMap A I a (b.ι i))) (z i), ?_⟩
  -- Evaluating `limMap (formalSectionsMap A I a ·) w` is additive in the morphism.
  let Θ : (b.pt ⟶ b.pt) →+ ToType (limit (formalSections A I a b.pt)) :=
    { toFun := fun f => ConcreteCategory.hom (limMap (formalSectionsMap A I a f)) w
      map_zero' := by
        rw [limMap_formalSectionsMap_zero]
        rfl
      map_add' := fun f g => by
        rw [limMap_formalSectionsMap_add]
        exact AddCommGrpCat.hom_add_apply _ _ w }
  have htot : ∑ i : ι, Θ (b.π i ≫ b.ι i) = w := by
    rw [← map_sum Θ, CategoryTheory.Limits.IsBilimit.total hb]
    change ConcreteCategory.hom (limMap (formalSectionsMap A I a (𝟙 b.pt))) w = w
    rw [limMap_formalSectionsMap_id]
    rfl
  refine Eq.trans ?_ htot
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [comparisonMap_apply_colimMap, hz i, ← ConcreteCategory.comp_apply,
    ← limMap_formalSectionsMap_comp]
  rfl

end Stacks.Algebraization

end
