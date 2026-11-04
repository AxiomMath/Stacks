module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AssociatedPointInductionComparison
public import StacksFrontier.AlgebraicGeometry.Divisors.DepthOneQuotient.Basic
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.CodimensionOneObstruction.AssociatedPointTransfer
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.Serre
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.Mono
public import StacksFrontier.AlgebraicGeometry.CoherentSubquotients.Abelian
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFullyFaithful.PrincipalComplement
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.Completion.RestrictOpen
public import StacksFrontier.AlgebraicGeometry.Morphisms.Support.FiniteType
public import StacksFrontier.RingTheory.Depth.AssociatedPrime

/-!
# Isolating one associated point of a coherent module off a vanishing locus

Let `I ⊆ 𝔞` be ideals of a Noetherian ring `A`, let `U = Spec(A) ∖ V(𝔞)` and let `F` be a
coherent module on `U` having at least one associated point off `V(I)`. Choose such a point `x₀`
whose prime is minimal among them, and let `T ⊆ U` be the set of points lying in `V(I)` or above
one of the other associated points off `V(I)`. Dividing `F` by its sections supported on `T`
gives a short exact sequence `0 → F' → F → F'' → 0` of coherent modules in which `F''` has `x₀`
as its only associated point off `V(I)` and `F'` has none at `x₀`.

That is exactly the input the induction of `Stacks.Algebraization.isIso_comparisonMap` consumes:
`F''` satisfies the three conditions of Stacks 0EIF, its third in the form (3)(a) because a
module with a single associated point has no embedded one, and `F'` has strictly fewer associated
points off `V(I)`.

## Main definitions

* `Stacks.Algebraization.splittingLocus` — the set `T`, closed under specialization.

## Main results

* `Stacks.Algebraization.isAssociatedPoint_iff_of_isIso_stalkFunctor_map` — a point is associated
  to the source of a morphism exactly when it is associated to the target, as soon as the stalk
  of the morphism at that point is an isomorphism.
* `Stacks.Algebraization.associatedPointSplitting` — the short exact sequence above, a term of
  `Stacks.Algebraization.AssociatedPointSplitting`.

## Implementation notes

The quotient `F''` is `AlgebraicGeometry.depthOneQuotient`, the canonical quotient of Stacks
0DX3 along a set closed under specialization: it is coherent, the quotient map is surjective and
an isomorphism on stalks off `T`, and the quotient has depth at least one along `T`. The depth
clause rules out an associated point of `F''` inside `T`, and the stalk clause transports the
associated points of `F''` off `T` to those of `F`; together they leave `x₀`.

The submodule `F'` is the categorical kernel of the quotient map rather than the sheaf of
sections supported on `T`, so that the short exact sequence is available without identifying the
two. Its stalk at `x₀` vanishes because the stalk of the quotient map there is an isomorphism and
the stalk of a monomorphism is injective.

No `@[stacks]` attribute is attached to anything here, and none may be: the source has no tag
for this step of the proof of Stacks 0EG2, whose registration belongs on
`Stacks.Algebraization.isIso_comparisonMap`, and the quotient this is built from already carries
the registration of Stacks 0DX3 on
`AlgebraicGeometry.depthOneQuotient_spec`.

## References

* [Stacks Project, Tag 0EG2](https://stacks.math.columbia.edu/tag/0EG2)
* [Stacks Project, Tag 0DX3](https://stacks.math.columbia.edu/tag/0DX3)
* [Stacks Project, Tag 0346](https://stacks.math.columbia.edu/tag/0346)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.AlgebraicGeometry.CodimensionOneObstruction
  (isAssociatedPrimeStacks_iff_of_semilinear isAssociatedPoint_restrict_iff)

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.Algebraization

open Stacks.LocalCohomology

/-! ### Associated points across a stalkwise isomorphism -/

/-- The stalk at `x` of the underlying presheaf of abelian groups, as a functor on modules. -/
private abbrev stalkAb (X : Scheme.{u}) (x : X) : X.Modules ⥤ Ab.{u} :=
  Scheme.Modules.toPresheaf X ⋙ TopCat.Presheaf.stalkFunctor Ab.{u} x

/-- **Association at a point is detected by the stalk there.** If the stalk of `g : F ⟶ G` at `x`
is an isomorphism then `x` is an associated point of `F` exactly when it is one of `G`. -/
public theorem isAssociatedPoint_iff_of_isIso_stalkFunctor_map {X : Scheme.{u}}
    {F G : X.Modules} (g : F ⟶ G) (x : X)
    (hg : IsIso ((TopCat.Presheaf.stalkFunctor Ab.{u} x).map g.mapPresheaf)) :
    Stacks.Divisors.IsAssociatedPoint F x ↔ Stacks.Divisors.IsAssociatedPoint G x := by
  let e : TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf x ≃+
      TopCat.Presheaf.stalk (C := Ab.{u}) G.val.presheaf x :=
    (@asIso _ _ _ _ ((TopCat.Presheaf.stalkFunctor Ab.{u} x).map g.mapPresheaf)
      hg).addCommGroupIsoToAddEquiv
  have hem : ∀ (U : X.Opens) (hx : x ∈ U) (s : Γ(F, U)),
      e (TopCat.Presheaf.germ F.val.presheaf U x hx s)
        = TopCat.Presheaf.germ G.val.presheaf U x hx (g.app U s) :=
    fun U hx s => TopCat.Presheaf.stalkFunctor_map_germ_apply U x hx _ s
  have he : ∀ r m, e (r • m) = (RingEquiv.refl (X.presheaf.stalk x)) r • e m := by
    intro r m
    obtain ⟨U₁, hx₁, b, hb⟩ := TopCat.Presheaf.exists_germ_eq X.presheaf r
    obtain ⟨U₂, hx₂, t, ht⟩ := TopCat.Presheaf.exists_germ_eq F.val.presheaf m
    have hx : x ∈ U₁ ⊓ U₂ := ⟨hx₁, hx₂⟩
    set b' := X.presheaf.map (homOfLE (inf_le_left : U₁ ⊓ U₂ ≤ U₁)).op b with hb'def
    set t' : Γ(F, U₁ ⊓ U₂) :=
      F.val.presheaf.map (homOfLE (inf_le_right : U₁ ⊓ U₂ ≤ U₂)).op t with ht'def
    have hb' : X.presheaf.germ (U₁ ⊓ U₂) x hx b' = r := by
      rwa [hb'def, TopCat.Presheaf.germ_res_apply]
    have ht' : TopCat.Presheaf.germ F.val.presheaf (U₁ ⊓ U₂) x hx t' = m := by
      rwa [ht'def, TopCat.Presheaf.germ_res_apply]
    rw [← hb', ← ht']
    refine (congrArg e (PresheafOfModules.germ_smul F.val x (U₁ ⊓ U₂) hx b' t').symm).trans ?_
    refine (hem (U₁ ⊓ U₂) hx (b' • t')).trans ?_
    rw [Scheme.Modules.Hom.app_smul g b' t']
    refine (PresheafOfModules.germ_smul G.val x (U₁ ⊓ U₂) hx b'
      (g.app (U₁ ⊓ U₂) t')).trans ?_
    rw [hem (U₁ ⊓ U₂) hx t']
    rfl
  have key := isAssociatedPrimeStacks_iff_of_semilinear
    (RingEquiv.refl (X.presheaf.stalk x)) e he
    (p := IsLocalRing.maximalIdeal (X.presheaf.stalk x))
  rwa [show Ideal.map (RingEquiv.refl (X.presheaf.stalk x)).toRingHom
    (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
      = IsLocalRing.maximalIdeal (X.presheaf.stalk x) from Ideal.map_id _] at key

/-- A module whose stalk at `x` is zero has no associated point at `x`: the annihilator of the
only germ there is the whole ring, which is not prime. -/
private theorem notMem_associatedPoints_of_stalk_eq_zero {X : Scheme.{u}} (F : X.Modules)
    (x : X) (h : ∀ m : ToType (TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf x), m = 0) :
    x ∉ Stacks.Divisors.associatedPoints F := by
  rintro ⟨hp, m, hm⟩
  rw [h m, Submodule.span_zero_singleton] at hm
  refine hp.ne_top ?_
  rw [← hm]
  refine Submodule.eq_top_iff'.2 fun r => Submodule.mem_colon.2 fun p hp' => ?_
  rw [(Submodule.mem_bot _).1 hp', smul_zero]
  exact Submodule.zero_mem _

/-! ### The locus that isolates one associated point -/

variable (A : Type u) [CommRing A] (I a : Ideal A)

/-- The points of `U = Spec(A) ∖ V(𝔞)` lying in `V(I)` together with those whose prime contains
the prime of a member of `S` other than `x₀`. For `S` the associated points of a module off
`V(I)` and `x₀` a minimal one, this is the locus to divide by. -/
public def splittingLocus (S : Set (complementZeroLocus A a : Scheme))
    (x₀ : (complementZeroLocus A a : Scheme)) : Set (complementZeroLocus A a : Scheme) :=
  {x | I ≤ x.1.asIdeal} ∪ {x | ∃ y ∈ S, y ≠ x₀ ∧ y.1.asIdeal ≤ x.1.asIdeal}

/-- Membership in the locus is the disjunction of its two defining conditions. -/
public theorem mem_splittingLocus {S : Set (complementZeroLocus A a : Scheme)}
    {x₀ x : (complementZeroLocus A a : Scheme)} :
    x ∈ splittingLocus A I a S x₀ ↔
      I ≤ x.1.asIdeal ∨ ∃ y ∈ S, y ≠ x₀ ∧ y.1.asIdeal ≤ x.1.asIdeal :=
  Iff.rfl

/-- The locus grows under specialization, because a specialization of a point of the spectrum has
a larger prime and both defining conditions ask for a lower bound on the prime. -/
public theorem stableUnderSpecialization_splittingLocus
    (S : Set (complementZeroLocus A a : Scheme)) (x₀ : (complementZeroLocus A a : Scheme)) :
    StableUnderSpecialization (splittingLocus A I a S x₀) := by
  intro x z hxz hx
  have hle : x.1.asIdeal ≤ z.1.asIdeal :=
    (PrimeSpectrum.le_iff_specializes _ _).mpr (hxz.map continuous_subtype_val)
  rcases hx with hx | ⟨y, hy, hyx₀, hyx⟩
  · exact Or.inl (hx.trans hle)
  · exact Or.inr ⟨y, hy, hyx₀, hyx.trans hle⟩

/-! ### The splitting -/

/-- **The splitting of the inductive step of the algebraization of formal sections, with
condition (3)(a) recorded.** A coherent module on `U = Spec(A) ∖ V(𝔞)` satisfying conditions (1)
and (2) and having an associated point off `V(I)` is the middle term of a short exact sequence of
coherent modules whose third term satisfies the hypotheses of Stacks 0EIF *with its condition (3)
in the form (3)(a)* — the third term has a single associated point off `V(I)`, so it is `(S₁)`
there — and whose first term has fewer associated points off `V(I)`. -/
public theorem exists_shortExact_serreOne_of_nonempty [IsNoetherianRing A]
    (F : (complementZeroLocus A a : Scheme).Modules) (hFc : F.IsCoherent)
    (hF : BootstrapHypotheses A I a F) (hne : (associatedPointsOffVanishing A I a F).Nonempty) :
    ∃ (F' F'' : (complementZeroLocus A a : Scheme).Modules) (f : F' ⟶ F) (g : F ⟶ F'')
      (w : f ≫ g = 0), (ShortComplex.mk f g w).ShortExact ∧ F'.IsCoherent ∧ F''.IsCoherent ∧
        FormalSectionsHypotheses A I a F'' ∧ IsSerreOneOffVanishing A I a F'' ∧
        associatedRank A I a F' < associatedRank A I a F := by
  obtain ⟨x₀, hx₀S, hx₀min⟩ :=
    (finite_associatedPointsOffVanishing A I a F).exists_minimalFor
      (fun x => x.1.asIdeal) _ hne
  have hx₀uniq : ∀ y ∈ associatedPointsOffVanishing A I a F,
      y.1.asIdeal ≤ x₀.1.asIdeal → y = x₀ := fun y hy hle =>
    Subtype.ext (PrimeSpectrum.ext (le_antisymm hle (hx₀min hy hle)))
  have hT : StableUnderSpecialization
      (splittingLocus A I a (associatedPointsOffVanishing A I a F) x₀) :=
    stableUnderSpecialization_splittingLocus A I a _ x₀
  have hx₀T : x₀ ∉ splittingLocus A I a (associatedPointsOffVanishing A I a F) x₀ := by
    rw [mem_splittingLocus]
    rintro (h | ⟨y, hy, hyne, hyle⟩)
    · exact hx₀S.2 h
    · exact hyne (hx₀uniq y hy hyle)
  -- the quotient of Stacks 0DX3 along that locus
  have hspec := AlgebraicGeometry.depthOneQuotient_spec (complementZeroLocus A a : Scheme)
    (splittingLocus A I a (associatedPointsOffVanishing A I a F) x₀) hT F
  set G := AlgebraicGeometry.depthOneQuotient (complementZeroLocus A a : Scheme)
    (splittingLocus A I a (associatedPointsOffVanishing A I a F) x₀) hT F
  set g : F ⟶ G := AlgebraicGeometry.toDepthOneQuotient (complementZeroLocus A a : Scheme)
    (splittingLocus A I a (associatedPointsOffVanishing A I a F) x₀) hT F
  have hGc : G.IsCoherent := hspec.1
  have _ : Epi g := hspec.2.1
  have _ : G.IsFiniteType :=
    (Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent G).2
  -- the depth clause removes every associated point of the quotient inside the locus
  have hGass : ∀ x : (complementZeroLocus A a : Scheme),
      x ∈ splittingLocus A I a (associatedPointsOffVanishing A I a F) x₀ →
      x ∉ Stacks.Divisors.associatedPoints G := by
    intro x hxT hxass
    rw [Stacks.Divisors.mem_associatedPoints_iff] at hxass
    let : Module ((complementZeroLocus A a : Scheme).presheaf.stalk x)
        (TopCat.Presheaf.stalk (C := Ab.{u}) G.val.presheaf x) :=
      PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
        (R := (complementZeroLocus A a : Scheme).presheaf) G.val x
    let : Module.Finite ((complementZeroLocus A a : Scheme).presheaf.stalk x)
        (TopCat.Presheaf.stalk (C := Ab.{u}) G.val.presheaf x) :=
      SheafOfModules.finite_stalk (complementZeroLocus A a : Scheme).sheaf G x
    exact maximalIdeal_not_isAssociatedPrimeStacks_of_one_le_depth (hspec.2.2.2 x hxT) hxass
  -- off the locus the stalk clause identifies the associated points with those of `F`
  have hGassOff : ∀ x : (complementZeroLocus A a : Scheme),
      x ∈ Stacks.Divisors.associatedPoints G → ¬ I ≤ x.1.asIdeal → x = x₀ := by
    intro x hxG hxI
    have hxT : x ∉ splittingLocus A I a (associatedPointsOffVanishing A I a F) x₀ :=
      fun h => hGass x h hxG
    have hxF : x ∈ Stacks.Divisors.associatedPoints F :=
      (isAssociatedPoint_iff_of_isIso_stalkFunctor_map g x (hspec.2.2.1 x hxT)).2 hxG
    by_contra hxne
    exact hxT ((mem_splittingLocus A I a).2 (Or.inr ⟨x, ⟨hxF, hxI⟩, hxne, le_rfl⟩))
  -- condition (3)(a) of Stacks 0EIF for the quotient
  have hS1 : IsSerreOneOffVanishing A I a G := by
    have _ : ((Scheme.Modules.restrictFunctor (opensOffVanishing A I a).ι).obj G).IsCoherent :=
      isCoherent_restrict_of_isOpenImmersion _ G
    have key : ∀ y : (opensOffVanishing A I a).toScheme,
        Stacks.Divisors.IsAssociatedPoint
            ((Scheme.Modules.restrictFunctor (opensOffVanishing A I a).ι).obj G) y →
          (opensOffVanishing A I a).ι.base y = x₀ := fun y hy =>
      hGassOff _ ((isAssociatedPoint_restrict_iff (opensOffVanishing A I a).ι G y).1 hy)
        ((mem_opensOffVanishing A I a _).1 y.2)
    refine (AlgebraicGeometry.hasNoEmbeddedAssociatedPoints_iff_hasPropertySk_one
      (opensOffVanishing A I a).toScheme _).1 ?_
    rintro y ⟨hyass, y', hy'ass, -, hy'ne⟩
    exact hy'ne ((opensOffVanishing A I a).ι.isOpenEmbedding.injective
      ((key y' hy'ass).trans (key y hyass).symm))
  -- condition (2) of Stacks 0EIF for the quotient
  have hdim : AssociatedPointsClosureDimensionBound A I a G := by
    intro x hxG hxI hclos z hz₁ hz₂
    exact hF.associatedPointsDimension x (hGassOff x hxG hxI ▸ hx₀S.1) hxI hclos z hz₁ hz₂
  -- the kernel, whose stalk at `x₀` vanishes
  have hF'c : (kernel g).IsCoherent := AlgebraicGeometry.isCoherent_kernel g
  have hx₀F' : x₀ ∉ Stacks.Divisors.associatedPoints (kernel g) := by
    have _ : IsIso ((stalkAb (complementZeroLocus A a : Scheme) x₀).map g) :=
      hspec.2.2.1 x₀ hx₀T
    have hzero : (stalkAb (complementZeroLocus A a : Scheme) x₀).map (kernel.ι g) = 0 := by
      refine zero_of_comp_mono ((stalkAb (complementZeroLocus A a : Scheme) x₀).map g) ?_
      rw [← Functor.map_comp, kernel.condition, Functor.map_zero]
    refine notMem_associatedPoints_of_stalk_eq_zero (kernel g) x₀ fun m => ?_
    refine AlgebraicGeometry.stalk_map_injective_of_mono (kernel.ι g) x₀ ?_
    show ((stalkAb (complementZeroLocus A a : Scheme) x₀).map (kernel.ι g)).hom m
      = ((stalkAb (complementZeroLocus A a : Scheme) x₀).map (kernel.ι g)).hom 0
    rw [hzero]
    rfl
  -- the measure drops
  have hsub : associatedPointsOffVanishing A I a (kernel g) ⊆
      associatedPointsOffVanishing A I a F \ {x₀} := fun x hx =>
    ⟨associatedPointsOffVanishing_subset_of_mono A I a (kernel.ι g) hx,
      fun hxx₀ => hx₀F' (hxx₀ ▸ hx.1)⟩
  have hlt : associatedRank A I a (kernel g) < associatedRank A I a F :=
    Set.ncard_lt_ncard ⟨hsub.trans Set.diff_subset, fun hcon => (hsub (hcon hx₀S)).2 rfl⟩
      (finite_associatedPointsOffVanishing A I a F)
  exact ⟨kernel g, G, kernel.ι g, g, kernel.condition g,
    ⟨CategoryTheory.ShortComplex.exact_kernel g⟩, hF'c, hGc,
    ⟨hF.adicComplete, hF.dualizing, hdim, Or.inl hS1⟩, hS1, hlt⟩

/-- **The splitting of the inductive step of the algebraization of formal sections.** A coherent
module on `U = Spec(A) ∖ V(𝔞)` satisfying conditions (1) and (2) and having an associated point
off `V(I)` is the middle term of a short exact sequence of coherent modules whose third term
satisfies the hypotheses of Stacks 0EIF and whose first term has fewer associated points
off `V(I)`. -/
public theorem associatedPointSplitting [IsNoetherianRing A] :
    AssociatedPointSplitting A I a := by
  intro F hFc hF hne
  obtain ⟨F', F'', f, g, w, hse, h₁, h₂, h₃, -, hlt⟩ :=
    exists_shortExact_serreOne_of_nonempty A I a F hFc hF hne
  exact ⟨F', F'', f, g, w, hse, h₁, h₂, h₃, hlt⟩

end Stacks.Algebraization

end
