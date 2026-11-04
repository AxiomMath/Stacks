module

public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.CompactFinite
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.SupportClosure
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.ComparisonShortExact
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.FormalSectionsSerreOneAlternative

/-!
# Algebraizing formal sections by induction on the associated points off the vanishing locus

Let `I ⊆ 𝔞` be ideals of a Noetherian ring `A`, let `U = Spec(A) ∖ V(𝔞)` and let `F` be a
coherent module on `U`. Stacks 0EIF makes the comparison map
`Stacks.Algebraization.comparisonMap A I 𝔞 F` an isomorphism under three conditions, the third
of which is the alternative "`F` is `(S₁)` off `V(I)`, or `V(𝔞)` has dimension at most `2`".
Stacks 0EG2 removes that third condition, by induction on the number of associated points of
`F` that do not lie in `V(I)`.

This file carries out that induction. The measure is
`Stacks.Algebraization.associatedRank`, the number of associated points of `F` off `V(I)`,
finite because `U` is quasi-compact and locally Noetherian. The base case is *proved*: a
coherent module with no associated point off `V(I)` vanishes on `U ∖ V(I)`, so it satisfies
condition (3)(a) vacuously and Stacks 0EIF applies to it unchanged. The inductive step splits
`F` and consumes, besides Stacks 0EIF, the middle clause of Stacks 0H48 and the short exact
sequence the source assembles from Stacks 0BK0, 0DX3 and 0AW0.

## Main definitions

* `Stacks.Algebraization.associatedPointsOffVanishing` — the associated points of `F` whose
  prime does not contain `I`.
* `Stacks.Algebraization.associatedRank` — the number of such points.
* `Stacks.Algebraization.BootstrapHypotheses` — conditions (1) and (2) of Stacks 0EG2.
* `Stacks.Algebraization.SerreOneAlternativeComparison` — Stacks 0EIF, for every Noetherian
  ring, every pair of ideals and every coherent module.
* `Stacks.Algebraization.MiddleComparisonOfShortExact` — the clause of Stacks 0H48 that says
  the middle comparison of a short exact sequence is an isomorphism when the outer two are.
* `Stacks.Algebraization.AssociatedPointSplitting` — the splitting of the source's proof: a
  coherent module with an associated point off `V(I)` sits in a short exact sequence whose
  third term satisfies the hypotheses of Stacks 0EIF and whose first term has strictly fewer
  associated points off `V(I)`.

## Main results

* `Stacks.Algebraization.finite_associatedPointsOffVanishing` — the measure is finite.
* `Stacks.Algebraization.associatedRank_le_of_mono` and
  `Stacks.Algebraization.BootstrapHypotheses.of_mono` — the measure and conditions (1) and (2)
  descend to a submodule.
* `Stacks.Algebraization.isSerreOneOffVanishing_of_associatedPointsOffVanishing_eq_empty` —
  **the base case**: a coherent module with no associated point off `V(I)` satisfies condition
  (3)(a) of Stacks 0EIF.
* `Stacks.Algebraization.isIso_comparisonMap_of_associatedPointsOffVanishing_eq_empty` — the
  base case at the level of the comparison map.
* `Stacks.Algebraization.isIso_comparisonMap` — **Stacks 0EG2**: the comparison map is an
  isomorphism under conditions (1) and (2) alone.

## Implementation notes

The measure is `Set.ncard`, which is `0` on an infinite set; nothing here depends on that,
because the only steps that compare two ranks are
`Stacks.Algebraization.associatedRank_le_of_mono`, which supplies finiteness of the larger set,
and the strict inequality inside `Stacks.Algebraization.AssociatedPointSplitting`, which is a
hypothesis.

The base case goes through sections rather than stalks. A section of a quasi-coherent module on
a locally Noetherian scheme over an open containing no associated point is zero, by
`AlgebraicGeometry.eq_zero_of_forall_germ_associatedPoints_eq_zero` whose hypothesis is then
vacuous; the sections of the restriction of `F` to an open `W` of `U ∖ V(I)` are the sections of
`F` over the image of `W`, which is an open of `U` off `V(I)`; so every germ of the restriction
vanishes, its stalks are subsingletons, their `Module.supportDim` is `⊥`, and Serre's condition
`(S₁)` holds because `min k ⊥ = ⊥`.

The three carried hypotheses are quantified over all inputs rather than specialized to `F`.
None of them is the conclusion of Stacks 0EG2 for `F`:
`Stacks.Algebraization.SerreOneAlternativeComparison` only applies to a module satisfying the
third condition, which is exactly what Stacks 0EG2 removes;
`Stacks.Algebraization.MiddleComparisonOfShortExact` needs two comparisons to be isomorphisms
before it produces a third; and `Stacks.Algebraization.AssociatedPointSplitting` does not
mention a comparison map at all.

## References

* [Stacks Project, Tag 0EG2](https://stacks.math.columbia.edu/tag/0EG2)
* [Stacks Project, Tag 0EIF](https://stacks.math.columbia.edu/tag/0EIF)
* [Stacks Project, Tag 0H48](https://stacks.math.columbia.edu/tag/0H48)
* [Stacks Project, Tag 0DX3](https://stacks.math.columbia.edu/tag/0DX3)
* [Stacks Project, Tag 0BK0](https://stacks.math.columbia.edu/tag/0BK0)
* [Stacks Project, Tag 0AW0](https://stacks.math.columbia.edu/tag/0AW0)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.Algebraization

open Stacks.LocalCohomology

/-! ### The associated points off the vanishing locus, and their number -/

variable (A : Type u) [CommRing A] (I a : Ideal A)

/-- The associated points of `F` whose prime does not contain `I`, that is, the associated
points of `F` lying in `U ∖ V(I)`. Their number is the measure of the induction in the source's
proof of Stacks 0EG2. -/
public def associatedPointsOffVanishing (F : (complementZeroLocus A a : Scheme).Modules) :
    Set (complementZeroLocus A a : Scheme) :=
  Stacks.Divisors.associatedPoints F ∩ {x | ¬ I ≤ x.1.asIdeal}

/-- A point lies in `associatedPointsOffVanishing A I a F` if and only if it is an associated
point of `F` whose prime does not contain `I`. -/
@[simp]
public theorem mem_associatedPointsOffVanishing
    (F : (complementZeroLocus A a : Scheme).Modules) (x : (complementZeroLocus A a : Scheme)) :
    x ∈ associatedPointsOffVanishing A I a F ↔
      x ∈ Stacks.Divisors.associatedPoints F ∧ ¬ I ≤ x.1.asIdeal :=
  Iff.rfl

/-- **The associated points off `V(I)` are finitely many.** Over a Noetherian ring the open
`U = Spec(A) ∖ V(𝔞)` is quasi-compact and locally Noetherian, so a coherent module on it has
finitely many associated points. -/
public theorem finite_associatedPointsOffVanishing [IsNoetherianRing A]
    (F : (complementZeroLocus A a : Scheme).Modules) [F.IsCoherent] :
    (associatedPointsOffVanishing A I a F).Finite :=
  (AlgebraicGeometry.associatedPoints_finite F).subset Set.inter_subset_left

/-- The number of associated points of `F` off `V(I)`. -/
public def associatedRank (F : (complementZeroLocus A a : Scheme).Modules) : ℕ :=
  (associatedPointsOffVanishing A I a F).ncard

/-- The associated points off `V(I)` of a submodule are associated points off `V(I)` of the
ambient module, by Stacks 05AE. -/
public theorem associatedPointsOffVanishing_subset_of_mono
    {F G : (complementZeroLocus A a : Scheme).Modules} (f : F ⟶ G) [Mono f] :
    associatedPointsOffVanishing A I a F ⊆ associatedPointsOffVanishing A I a G :=
  Set.inter_subset_inter_left _ (AlgebraicGeometry.associatedPoints_subset_of_mono f)

/-- The measure does not increase along a monomorphism of coherent modules. -/
public theorem associatedRank_le_of_mono [IsNoetherianRing A]
    {F G : (complementZeroLocus A a : Scheme).Modules} [G.IsCoherent] (f : F ⟶ G) [Mono f] :
    associatedRank A I a F ≤ associatedRank A I a G :=
  Set.ncard_le_ncard (associatedPointsOffVanishing_subset_of_mono A I a f)
    (finite_associatedPointsOffVanishing A I a G)

/-! ### Conditions (1) and (2) of Stacks 0EG2 -/

/-- **The hypotheses of Stacks 0EG2.** For ideals `I ⊆ 𝔞` of a Noetherian ring `A` and a
coherent module `F` on `U = Spec(A) ∖ V(𝔞)`: the ring is `I`-adically complete and has a
dualizing complex, and the associated points of `F` satisfy the dimension bound of condition
(2). These are the conditions of `Stacks.Algebraization.FormalSectionsHypotheses` with its
third condition dropped, which is what Stacks 0EG2 adds to Stacks 0EIF. -/
public structure BootstrapHypotheses [IsNoetherianRing A]
    (F : (complementZeroLocus A a : Scheme).Modules) : Prop where
  /-- The source's standing assumption `I ⊆ 𝔞`. -/
  le : I ≤ a
  /-- Condition (1), completeness: `A` is `I`-adically complete. -/
  adicComplete : IsAdicComplete I A
  /-- Condition (1), duality: `A` has a dualizing complex. -/
  dualizing : ∃ K : DerivedCategory (ModuleCat.{u} A), Dualizing.IsDualizingComplex K
  /-- Condition (2): the dimension bound at the associated points of `F`. -/
  associatedPointsDimension : AssociatedPointsClosureDimensionBound A I a F

/-- Condition (2) descends to a submodule: the associated points of a submodule are associated
points of the ambient module, by Stacks 05AE. -/
public theorem AssociatedPointsClosureDimensionBound.of_mono [IsNoetherianRing A]
    {F G : (complementZeroLocus A a : Scheme).Modules} (f : F ⟶ G) [Mono f]
    (h : AssociatedPointsClosureDimensionBound A I a G) :
    AssociatedPointsClosureDimensionBound A I a F :=
  fun x hx => h x (AlgebraicGeometry.associatedPoints_subset_of_mono f hx)

/-- Conditions (1) and (2) of Stacks 0EG2 descend to a submodule. -/
public theorem BootstrapHypotheses.of_mono [IsNoetherianRing A]
    {F G : (complementZeroLocus A a : Scheme).Modules} (f : F ⟶ G) [Mono f]
    (h : BootstrapHypotheses A I a G) :
    BootstrapHypotheses A I a F :=
  ⟨h.le, h.adicComplete, h.dualizing,
    AssociatedPointsClosureDimensionBound.of_mono A I a f h.associatedPointsDimension⟩

/-- The hypotheses of Stacks 0EIF contain those of Stacks 0EG2, apart from the standing
assumption `I ⊆ 𝔞`, which `Stacks.Algebraization.FormalSectionsHypotheses` does not record. -/
public theorem FormalSectionsHypotheses.toBootstrapHypotheses [IsNoetherianRing A]
    {F : (complementZeroLocus A a : Scheme).Modules} (hIa : I ≤ a)
    (h : FormalSectionsHypotheses A I a F) :
    BootstrapHypotheses A I a F :=
  ⟨hIa, h.adicComplete, h.dualizing, h.associatedPointsDimension⟩

/-- Conditions (1) and (2) of Stacks 0EG2 together with the third condition of Stacks 0EIF are
the hypotheses of Stacks 0EIF. -/
public theorem BootstrapHypotheses.formalSectionsHypotheses [IsNoetherianRing A]
    {F : (complementZeroLocus A a : Scheme).Modules} (h : BootstrapHypotheses A I a F)
    (h₃ : IsSerreOneOffVanishing A I a F ∨ VanishingLocusDimensionAtMostTwo A a) :
    FormalSectionsHypotheses A I a F :=
  ⟨h.adicComplete, h.dualizing, h.associatedPointsDimension, h₃⟩

/-! ### The base case: no associated point off the vanishing locus -/

/-- A section of a quasi-coherent module on a locally Noetherian scheme over an open containing
no associated point of the module is zero: the hypothesis of
`AlgebraicGeometry.eq_zero_of_forall_germ_associatedPoints_eq_zero` is vacuous. -/
public theorem subsingleton_sections_of_forall_notMem_associatedPoints {X : Scheme.{u}}
    [IsLocallyNoetherian X] (F : X.Modules) [F.IsQuasicoherent] (V : X.Opens)
    (h : ∀ x : X, x ∈ V → x ∉ Stacks.Divisors.associatedPoints F) :
    Subsingleton (ToType Γ(F, V)) :=
  subsingleton_of_forall_eq 0 fun s =>
    AlgebraicGeometry.eq_zero_of_forall_germ_associatedPoints_eq_zero F V s
      fun x hx hxass => absurd hxass (h x hx)

/-- The sections of the restriction of `F` to an open `V` over an open `W` of `V` are the
sections of `F` over the image of `W`, so they vanish when `V` contains no associated point of
`F`. -/
private theorem subsingleton_sections_restrictFunctor {X : Scheme.{u}} [IsLocallyNoetherian X]
    (F : X.Modules) [F.IsQuasicoherent] (V : X.Opens)
    (h : ∀ y : X, y ∈ V → y ∉ Stacks.Divisors.associatedPoints F) (W : V.toScheme.Opens) :
    Subsingleton (ToType Γ((Scheme.Modules.restrictFunctor V.ι).obj F, W)) := by
  have hF : Subsingleton (ToType Γ(F, V.ι ''ᵁ W)) :=
    subsingleton_sections_of_forall_notMem_associatedPoints F (V.ι ''ᵁ W)
      fun y hy hyass => h y (V.ι_image_le W hy) hyass
  exact ⟨fun s t => (ConcreteCategory.bijective_of_isIso
    (Scheme.Modules.restrictAppIso V.ι F W).hom).1 (hF.elim _ _)⟩

/-- The stalks of the restriction of `F` to an open containing no associated point of `F`
vanish: every germ is represented by a section over an open of that restriction, and those
sections are zero. -/
private theorem subsingleton_stalk_restrictFunctor {X : Scheme.{u}} [IsLocallyNoetherian X]
    (F : X.Modules) [F.IsQuasicoherent] (V : X.Opens)
    (h : ∀ y : X, y ∈ V → y ∉ Stacks.Divisors.associatedPoints F) (x : V.toScheme) :
    Subsingleton (ToType (TopCat.Presheaf.stalk (C := Ab.{u})
      ((Scheme.Modules.restrictFunctor V.ι).obj F).val.presheaf x)) := by
  refine subsingleton_of_forall_eq 0 fun z => ?_
  obtain ⟨W, hxW, w, hw⟩ := TopCat.Presheaf.exists_germ_eq
    ((Scheme.Modules.restrictFunctor V.ι).obj F).val.presheaf z
  have hw0 : w = 0 := (subsingleton_sections_restrictFunctor F V h W).elim w 0
  rw [← hw, hw0]
  exact map_zero _

/-- Serre's condition `(Sₖ)` holds for a sheaf of modules whose stalks are all subsingletons:
`Module.supportDim` of a subsingleton module is `⊥`, and `min k ⊥ = ⊥` is below every depth. -/
public theorem sheafHasPropertySk_of_forall_subsingleton_stalk {X : Scheme.{u}}
    (G : SheafOfModules.{u} (structureSheafRing
      X.toRingedSpace)) (k : ℕ)
    (h : ∀ x : X, Subsingleton
      (ToType (TopCat.Presheaf.stalk (C := Ab.{u}) G.val.presheaf x))) :
    SheafHasPropertySk X G k := by
  intro x
  have _ := h x
  refine le_trans (min_le_right _ _) ?_
  rw [Module.supportDim_eq_bot_of_subsingleton]
  exact bot_le

/-- **The base case of the induction of Stacks 0EG2.** A coherent module with no associated
point off `V(I)` satisfies condition (3)(a) of Stacks 0EIF: its restriction to `U ∖ V(I)`
vanishes, so Serre's condition `(S₁)` holds there vacuously.

Every germ of the restriction is represented by a section over an open `W` of `U ∖ V(I)`, whose
image in `U` contains no associated point of `F`; that section is therefore zero, so the stalks
of the restriction are subsingletons, their `Module.supportDim` is `⊥`, and `min 1 ⊥ = ⊥` is
below every depth. -/
public theorem isSerreOneOffVanishing_of_associatedPointsOffVanishing_eq_empty
    [IsNoetherianRing A] (F : (complementZeroLocus A a : Scheme).Modules) [F.IsCoherent]
    (h : associatedPointsOffVanishing A I a F = ∅) :
    IsSerreOneOffVanishing A I a F := by
  have _ : F.IsQuasicoherent := isQuasicoherent_of_isCoherent F
  rw [Set.eq_empty_iff_forall_notMem] at h
  exact sheafHasPropertySk_of_forall_subsingleton_stalk _ 1
    fun x => subsingleton_stalk_restrictFunctor F (opensOffVanishing A I a)
      (fun y hy hyass => h y ⟨hyass, (mem_opensOffVanishing A I a y).1 hy⟩) x

/-! ### The tags the source's proof of Stacks 0EG2 consumes -/

/-- **Stacks 0EIF**, stated for every Noetherian ring, every pair of ideals and every coherent
module: under conditions (1), (2) and (3) of that lemma the comparison map is an isomorphism.

This is a different statement from the conclusion of Stacks 0EG2 for one module: it never
applies to a module failing condition (3), which is the condition Stacks 0EG2 removes. -/
public def SerreOneAlternativeComparison : Prop :=
  ∀ (B : Type u) [CommRing B] [IsNoetherianRing B] (J b : Ideal B)
    (G : (complementZeroLocus B b : Scheme).Modules), G.IsCoherent →
      FormalSectionsHypotheses B J b G → IsIso (comparisonMap B J b G)

/-- **The middle comparison of Stacks 0H48**, stated for every Noetherian ring, every pair of
ideals and every short exact sequence of coherent modules: if the comparison maps of the outer
two terms are isomorphisms, so is that of the middle term.

It holds: `Stacks.Algebraization.middleComparisonOfShortExact`, alongside the companion clause
`Stacks.Algebraization.isIso_comparisonMap_first_of_middle_and_third` of the same lemma. It
cannot produce the conclusion of Stacks 0EG2 for a module on its own: it needs two comparisons
to be isomorphisms before it produces a third. -/
public def MiddleComparisonOfShortExact : Prop :=
  ∀ (B : Type u) [CommRing B] [IsNoetherianRing B] (J b : Ideal B)
    (S : ShortComplex (complementZeroLocus B b : Scheme).Modules), S.ShortExact →
      S.X₁.IsCoherent → S.X₂.IsCoherent → S.X₃.IsCoherent →
      IsIso (comparisonMap B J b S.X₁) → IsIso (comparisonMap B J b S.X₃) →
        IsIso (comparisonMap B J b S.X₂)

/-- **The splitting of the source's proof of Stacks 0EG2**, the combination of Stacks 0BK0,
0DX3 and 0AW0 that the source performs. A coherent module `F` on `U` satisfying conditions (1)
and (2) and having an associated point off `V(I)` is written as the middle term of a short exact
sequence `0 → F' → F → F'' → 0` of coherent modules in which `F''` satisfies the full
hypotheses of Stacks 0EIF — in the source, because `F''` has a single associated point, so that
condition (3)(a) holds for it — and `F'` has strictly fewer associated points off `V(I)`.

In the source `F` is `M̃|_U` for a finite module `M` (Stacks 0BK0), `F'` is cut out by the
torsion submodule `H⁰_{𝔭₁⋯𝔭_{n-1}I}(M)` after the depth reduction of Stacks 0DX3, and `F''` is
the quotient, whose single associated prime is identified by Stacks 0AW0.

No comparison map occurs in this statement: it is a statement about coherent modules, their
associated points and Serre's condition. -/
public def AssociatedPointSplitting [IsNoetherianRing A] : Prop :=
  ∀ F : (complementZeroLocus A a : Scheme).Modules, F.IsCoherent →
    BootstrapHypotheses A I a F → (associatedPointsOffVanishing A I a F).Nonempty →
      ∃ (F' F'' : (complementZeroLocus A a : Scheme).Modules) (f : F' ⟶ F) (g : F ⟶ F'')
        (w : f ≫ g = 0), (ShortComplex.mk f g w).ShortExact ∧ F'.IsCoherent ∧ F''.IsCoherent ∧
          FormalSectionsHypotheses A I a F'' ∧
          associatedRank A I a F' < associatedRank A I a F

/-! ### The induction -/

/-- **The base case of the induction of Stacks 0EG2, at the level of the comparison map.** A
coherent module satisfying conditions (1) and (2) with no associated point off `V(I)` satisfies
the full hypotheses of Stacks 0EIF, its third condition holding in the form (3)(a), so its
comparison map is an isomorphism. -/
public theorem isIso_comparisonMap_of_associatedPointsOffVanishing_eq_empty [IsNoetherianRing A]
    (hEIF : SerreOneAlternativeComparison.{u})
    (F : (complementZeroLocus A a : Scheme).Modules) (hFc : F.IsCoherent)
    (hF : BootstrapHypotheses A I a F) (h : associatedPointsOffVanishing A I a F = ∅) :
    IsIso (comparisonMap A I a F) :=
  have _ : F.IsCoherent := hFc
  hEIF A I a F hFc (hF.formalSectionsHypotheses A I a
    (Or.inl (isSerreOneOffVanishing_of_associatedPointsOffVanishing_eq_empty A I a F h)))

/-- **The induction of Stacks 0EG2**, on the number of associated points off `V(I)`. A coherent
module satisfying conditions (1) and (2) whose associated points off `V(I)` number at most `n`
has an isomorphic comparison map.

With no associated point off `V(I)` the module satisfies condition (3)(a) of Stacks 0EIF, by
`Stacks.Algebraization.isSerreOneOffVanishing_of_associatedPointsOffVanishing_eq_empty`, and
Stacks 0EIF applies to it. Otherwise the splitting produces `0 → F' → F → F'' → 0` with
Stacks 0EIF applying to `F''` and the induction hypothesis to `F'`, since conditions (1) and (2)
descend to the submodule `F'`; the middle clause of Stacks 0H48 then concludes for `F`. -/
public theorem isIso_comparisonMap_of_associatedRank_le [IsNoetherianRing A]
    (hEIF : SerreOneAlternativeComparison.{u}) (h48 : MiddleComparisonOfShortExact.{u})
    (hsplit : AssociatedPointSplitting A I a) :
    ∀ (n : ℕ) (F : (complementZeroLocus A a : Scheme).Modules), F.IsCoherent →
      BootstrapHypotheses A I a F → associatedRank A I a F ≤ n →
        IsIso (comparisonMap A I a F) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro F hFc hF hrank
    have _ : F.IsCoherent := hFc
    rcases Set.eq_empty_or_nonempty (associatedPointsOffVanishing A I a F) with hemp | hne
    · exact isIso_comparisonMap_of_associatedPointsOffVanishing_eq_empty A I a hEIF F hFc hF hemp
    · obtain ⟨F', F'', f, g, w, hSE, hF'c, hF''c, hF'', hlt⟩ := hsplit F hFc hF hne
      have _ : Mono f := hSE.mono_f
      have h₁ : IsIso (comparisonMap A I a F') :=
        ih _ (by omega) F' hF'c (BootstrapHypotheses.of_mono A I a f hF) le_rfl
      have h₃ : IsIso (comparisonMap A I a F'') := hEIF A I a F'' hF''c hF''
      exact h48 A I a (ShortComplex.mk f g w) hSE hF'c hFc hF''c h₁ h₃

/-- **Stacks 0EG2.** Let `I ⊆ 𝔞` be ideals of a Noetherian ring `A` and let `F` be a coherent
module on `U = Spec(A) ∖ V(𝔞)`. Assume

1. `A` is `I`-adically complete and has a dualizing complex, and
2. whenever `x` is an associated point of `F` outside `V(I)` whose closure meets `V(I)` outside
   `V(𝔞)`, every `z ∈ closure {x} ∩ V(𝔞)` has `dim(𝒪_{closure {x}, z}) > cd(A, I) + 1`.

Then the comparison map `Stacks.Algebraization.comparisonMap A I 𝔞 F`, from the sections of `F`
on arbitrarily small open neighbourhoods of `U ∩ V(I)` to the compatible families of sections of
`F / Iⁿ F` on all of `U`, is an isomorphism.

The source's third condition, present in Stacks 0EIF, is absent here; that is the whole content
of this proposition, and it is obtained by induction on the number of associated points of `F`
off `V(I)` over Stacks 0EIF, the middle clause of Stacks 0H48, and the splitting the source
assembles from Stacks 0BK0, 0DX3 and 0AW0. -/
@[stacks 0EG2 "the third condition of Stacks 0EIF removed, by induction on the associated \
points off V(I). Carried, each in its own generality and none of them this conclusion: Stacks \
0EIF (SerreOneAlternativeComparison), the middle clause of Stacks 0H48 \
(MiddleComparisonOfShortExact), and the short exact sequence the source builds from Stacks \
0BK0, 0DX3 and 0AW0 (AssociatedPointSplitting, in which no comparison map occurs). Proved \
here: the induction, the base case, and the descent of the measure and of conditions (1) and \
(2) to a submodule"]
public theorem isIso_comparisonMap [IsNoetherianRing A]
    (F : (complementZeroLocus A a : Scheme).Modules) [hFc : F.IsCoherent]
    (hF : BootstrapHypotheses A I a F)
    (hEIF : SerreOneAlternativeComparison.{u}) (h48 : MiddleComparisonOfShortExact.{u})
    (hsplit : AssociatedPointSplitting A I a) :
    IsIso (comparisonMap A I a F) :=
  isIso_comparisonMap_of_associatedRank_le A I a hEIF h48 hsplit
    (associatedRank A I a F) F hFc hF le_rfl

end Stacks.Algebraization

end
