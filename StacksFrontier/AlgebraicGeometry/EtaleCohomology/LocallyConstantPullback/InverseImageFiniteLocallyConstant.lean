module

public import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Over
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LocallyConstantPullback.CoverCriterion
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LocallyConstantPullback.GeneralCoefficients
public import StacksFrontier.CategoryTheory.Sites.Localization.PushforwardAdjunction
import StacksCore.Tactic.StacksAttribute

/-!
# The inverse image of a finite locally constant sheaf, for arbitrary coefficients

Let `G : C ⥤ D` be a continuous functor between sites `(C, J)` and `(D, K)` whose pushforward on
sheaves has a left adjoint, so that `G` induces an inverse image `G^* = G.sheafPullback`. Tag 093R
asserts that `G^*` carries (finite) locally constant sheaves to (finite) locally constant sheaves,
for every kind of coefficient: sets, groups, abelian groups, modules.

The library already had the case of a *constant* sheaf of **sets**, by uniqueness of left adjoints
(`Stacks.ConstantSheaf.inverseImageConstantSheafIso`). That proof identifies the right adjoint of
`constantSheaf K (Type w) ⋙ G^*` with global sections on `C` by *corepresenting* global sections by
the constant sheaf on a one-element set, a one-element set being a final object of `Type w`. This
step is special to sets: for a general coefficient category `A` the global sections functor is
`A`-valued and is not a `Hom`-functor, so there is nothing to corepresent.

This file replaces that step by one which is insensitive to the coefficients. The right adjoint of
`G^*` is *precomposition* with `G.op`, so the sections over an object `T` of `C` of a pushforward
are the sections over `G.obj T`:

`Γ_T (G_* F) = F.val.obj (op (G.obj T))`.

If `T` is final in `C` and `G.obj T` final in `D`, both sides are global sections, with no
hypothesis at all on `A`. Uniqueness of left adjoints then gives
`constantSheaf J A ⋙ G^* ≅ constantSheaf K A`, which is Tag 093R for a constant sheaf and
arbitrary coefficients. The same mechanism applies to any left adjoint whose right adjoint is a
pushforward, which covers restriction along a morphism of the site as well: there the right adjoint
is the pushforward along `Over.pullback f`, and the finality needed is the preservation of the final
object by a right adjoint.

The passage from constant to finite locally constant is then geometric rather than formal. A single
covering of a final object suffices for local constancy
(`Stacks.ConstantSheaf.isFiniteLocallyConstant_of_cover`, the arbitrary-coefficient form of the
set-valued statement in `CoverCriterion.lean`), so one trivializing covering `{X i ⟶ T}` of `F` is
enough, and its image `{G.obj (X i) ⟶ G.obj T}` is a covering because `G` preserves coverings. What
has to be checked on a member is that the restriction of `G^* F` to `G.obj (X i)` is constant, and
that is a *commuting square*: restriction to `G.obj X` after `G^*` agrees with the inverse image
along the slice `Over.post G` after restriction to `X`. Both composites are left adjoints, and their
right adjoints are the pushforwards along `G ⋙ Over.star (G.obj X)` and along
`Over.star X ⋙ Over.post G`; these two functors agree up to the product comparison of `G`, which is
an isomorphism because `G` is left exact. So the square commutes, and the restriction of `G^* F` to
`G.obj (X i)` is the inverse image along `Over.post G` of a constant sheaf, hence constant with the
*same* value — in particular with a finite value when the original value was finite.

## Main definitions

* `Stacks.ConstantSheaf.constantSheafIsoOfPushforward` — the mechanism: a left adjoint whose right
  adjoint is a pushforward along a functor carrying a final object to a final object commutes with
  the constant sheaf functor.
* `Stacks.ConstantSheaf.constantSheafOverMapPullbackIso` — the same for restriction along a morphism
  of the site, with no universe hypothesis relating the coefficients to the site.
* `Stacks.ConstantSheaf.constantIsoOverPullbackOfMap` — a trivialization survives refinement, for
  arbitrary coefficients.
* `Stacks.ConstantSheaf.starPostIso` — the slice of a left exact functor commutes with the right
  adjoints of the two localization functors.
* `Stacks.ConstantSheaf.overPullbackSheafPullbackIso` — the commuting square: restriction after
  inverse image is inverse image along the slice after restriction.

## Main results

* `Stacks.ConstantSheaf.isConstant_sheafPullback` — the inverse image of a constant sheaf is
  constant, for arbitrary coefficients.
* `Stacks.ConstantSheaf.isLocallyConstant_sheafPullback` and
  `Stacks.ConstantSheaf.isFiniteLocallyConstant_sheafPullback_of_coverPreserving` — **Tag 093R
  for a morphism of sites**: the inverse image of a locally constant, resp. finite locally
  constant, sheaf is locally constant, resp. finite locally constant.
* `Stacks.ConstantSheaf.isContinuous_overPost` — continuity of the slice of a left exact
  cover-preserving functor, which is what discharges the instance hypotheses of the above.

## Implementation notes

`Over.post G` is the slice of `G`, and its continuity is not an instance in Mathlib; it is taken as
an instance hypothesis of the main theorems and produced by
`Stacks.ConstantSheaf.isContinuous_overPost` from cover preservation and left exactness of `G`.
Cover preservation is a hypothesis of the main theorems rather than a consequence of continuity:
Mathlib's `CategoryTheory.Functor.IsContinuous` bundles only the condition that restriction along
the functor preserves sheaves, which does not by itself give cover preservation.

The source states Tag 093R for an arbitrary morphism of topoi `f : Sh(C) ⟶ Sh(D)`, whose inverse
image need not be induced by a functor between the two sites. What is proved here is the case where
it is, which is the case of every inverse image this library builds — base change between small
étale sites, and restriction to an object — and the two attributes below are qualified to record
the restriction. The localization square, which is what the proof turns on, is available for a
morphism of sites because the slice `Over.post G` of the functor is again a functor of sites. For a
bare morphism of topoi between the topoi of sheaves of *sets* on two small sites the tag is proved
in
`StacksFrontier.CategoryTheory.Sites.LocallyConstant.MorphismOfTopoiSectionRelocalization`, where
the
square is replaced by the relocalization of `f` along a section `h_V^# ⟶ f⁻¹h_Y^#`; the arbitrary
coefficient categories of this file are outside the reach of that argument, which is about
represented sheaves of sets.

The trivializing covering is taken over the final object of `C`, and no object with a final image
has to be supplied to the main theorems: left exactness of `G`, which the localization square
already needs, carries `⊤_C` to a final object of `D`. The intermediate
`Stacks.ConstantSheaf.isLocallyConstant_of_cover` still asks only for an object with a final image,
which is all its proof uses.

## References

* [Stacks Project, Tag 093R](https://stacks.math.columbia.edu/tag/093R)
* [Stacks Project, Tag 093Q](https://stacks.math.columbia.edu/tag/093Q)
* [Stacks Project, Tag 03CE](https://stacks.math.columbia.edu/tag/03CE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe wc w' w v u v' u'

namespace Stacks.ConstantSheaf

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  (A : Type w) [Category.{w'} A]

/-! ### The constant sheaf functor and a left adjoint whose right adjoint is a pushforward -/

section Mechanism

variable [HasWeakSheafify J A] [HasWeakSheafify K A]
  {L : Sheaf J A ⥤ Sheaf K A} {R : Sheaf K A ⥤ Sheaf J A}
  (H : C ⥤ D) [H.IsContinuous J K] {T : C} {T' : D}

/-- **The mechanism behind Tag 093R.** Let `L ⊣ R` be an adjoint pair between the sheaf categories
of `(C, J)` and `(D, K)` whose right adjoint `R` is the pushforward along a continuous functor `H`
carrying a final object of `C` to a final object of `D`. Then `L` commutes with the constant sheaf
functor.

Both `constantSheaf J A ⋙ L` and `constantSheaf K A` are left adjoint to global sections on `D`:
the first because its right adjoint `R ⋙ Γ_C` is `Γ_D` by
`Stacks.ConstantSheaf.pushforwardSectionsIsoOfTerminal`, the second by
`CategoryTheory.constantSheafAdj`. -/
public def constantSheafIsoOfPushforward (adj : L ⊣ R)
    (ε : R ≅ H.sheafPushforwardContinuous A J K) (hT : IsTerminal T) (hT' : IsTerminal T')
    (e : H.obj T ≅ T') :
    constantSheaf J A ⋙ L ≅ constantSheaf K A :=
  (((constantSheafAdj J A hT).comp adj).ofNatIsoRight
      (Functor.isoWhiskerRight ε ((sheafSections J A).obj (op T)) ≪≫
        pushforwardSectionsIsoOfTerminal H A J K e)).leftAdjointUniq (constantSheafAdj K A hT')

/-- A left adjoint whose right adjoint is a pushforward along a functor preserving the final object
carries constant sheaves to constant sheaves, for arbitrary coefficients. -/
public lemma isConstant_of_pushforward (adj : L ⊣ R)
    (ε : R ≅ H.sheafPushforwardContinuous A J K) (hT : IsTerminal T) (hT' : IsTerminal T')
    (e : H.obj T ≅ T') (F : Sheaf J A) [Sheaf.IsConstant J F] :
    Sheaf.IsConstant K (L.obj F) := by
  obtain ⟨E, ⟨c⟩⟩ := Sheaf.mem_essImage_of_isConstant J F
  exact Sheaf.isConstant_of_iso K
    (L.mapIso c.symm ≪≫ (constantSheafIsoOfPushforward J K A H adj ε hT hT' e).app E)

end Mechanism

/-! ### Inverse image along a continuous functor of sites -/

section Pullback

variable [HasWeakSheafify J A] [HasWeakSheafify K A]
  (G : C ⥤ D) [G.IsContinuous J K] [(G.sheafPushforwardContinuous A J K).IsRightAdjoint]
  {T : C} {T' : D}

/-- **Tag 093R for a constant sheaf, with arbitrary coefficients**, in its `Prop`-valued form.
The isomorphism itself is `Stacks.ConstantSheaf.sheafPullbackConstantSheafIso`. -/
public lemma isConstant_sheafPullback (hT : IsTerminal T) (hT' : IsTerminal T')
    (e : G.obj T ≅ T') (F : Sheaf J A) [Sheaf.IsConstant J F] :
    Sheaf.IsConstant K ((G.sheafPullback A J K).obj F) :=
  isConstant_of_pushforward J K A G (G.sheafAdjunctionContinuous A J K) (Iso.refl _) hT hT' e F

end Pullback

/-! ### Restriction along a morphism of the site -/

section OverMap

variable [HasPullbacks C] [∀ U : C, HasWeakSheafify (J.over U) A] {X Y : C}

/-- **Restriction of a constant sheaf along a morphism of the site is constant**, with the same
value, for arbitrary coefficients and with no universe hypothesis.

Restriction along `Over.map f` is a left adjoint whose right adjoint is the pushforward along
`Over.pullback f` (Tag 03CE), and `Over.pullback f` carries the final object of `C/Y` to the final
object of `C/X` because it is a right adjoint. So
`Stacks.ConstantSheaf.constantSheafIsoOfPushforward` applies.

This is `Stacks.ConstantSheaf.constantSheafOverMapIso` without its pointwise Kan extension
hypothesis, and `Stacks.ConstantSheaf.overMapPullbackConstantSheafIso` for coefficients other than
sets. -/
public def constantSheafOverMapPullbackIso (f : X ⟶ Y) :
    constantSheaf (J.over Y) A ⋙ J.overMapPullback A f ≅ constantSheaf (J.over X) A :=
  haveI := (Over.mapPullbackAdj f).rightAdjoint_preservesLimits
  constantSheafIsoOfPushforward (J.over Y) (J.over X) A (Over.pullback f)
    ((Over.mapPullbackAdj f).sheafPushforwardAdjunction A) (Iso.refl _)
    Over.mkIdTerminal Over.mkIdTerminal
    ((IsTerminal.isTerminalObj (Over.pullback f) _ Over.mkIdTerminal).uniqueUpToIso
      Over.mkIdTerminal)

/-- **A trivialization survives refinement, for arbitrary coefficients.** If the restriction of `F`
to `Y` is the constant sheaf on `E`, then its restriction to any `X` over `Y` is the constant sheaf
on the *same* `E`. Keeping the value unchanged is what makes the statement usable for *finite* local
constancy. -/
public def constantIsoOverPullbackOfMap (f : X ⟶ Y) (F : Sheaf J A) (E : A)
    (c : (constantSheaf (J.over Y) A).obj E ≅ (J.overPullback A Y).obj F) :
    (constantSheaf (J.over X) A).obj E ≅ (J.overPullback A X).obj F :=
  (constantSheafOverMapPullbackIso J A f).symm.app E ≪≫
    (J.overMapPullback A f).mapIso c ≪≫ F.pushforwardOverMapIso f

/-- The `Prop`-valued form of `Stacks.ConstantSheaf.constantIsoOverPullbackOfMap`. -/
public lemma isConstant_overPullback_of_map (f : X ⟶ Y) (F : Sheaf J A)
    [Sheaf.IsConstant (J.over Y) ((J.overPullback A Y).obj F)] :
    Sheaf.IsConstant (J.over X) ((J.overPullback A X).obj F) := by
  obtain ⟨E, ⟨c⟩⟩ := Sheaf.mem_essImage_of_isConstant (J.over Y) ((J.overPullback A Y).obj F)
  exact ⟨E, ⟨constantIsoOverPullbackOfMap J A f F E c⟩⟩

end OverMap

/-! ### One covering of a final object suffices, for arbitrary coefficients -/

/-- A morphism in the pullback to `U` of a covering sieve of a final object `T` factors through a
member of the covering family. -/
private theorem exists_hom_of_mem_pullback_ofArrows {T : C} (hT : IsTerminal T) {I : Type*}
    {X : I → C} {f : ∀ i, X i ⟶ T} {V U : C} (g : V ⟶ U)
    (hg : (Sieve.pullback (hT.from U) (Sieve.ofArrows X f)).arrows g) :
    ∃ i, Nonempty (V ⟶ X i) := by
  have h1 : (Sieve.ofArrows X f).arrows (g ≫ hT.from U) := hg
  rw [hT.hom_ext (g ≫ hT.from U) (hT.from V)] at h1
  obtain ⟨i, h, -⟩ := (Sieve.mem_ofArrows_iff _ _ _).mp h1
  exact ⟨i, ⟨h⟩⟩

section Cover

variable [HasPullbacks C] [∀ U : C, HasWeakSheafify (J.over U) A]

/-- **A single covering of a final object suffices for local constancy**, for arbitrary
coefficients. -/
public lemma isLocallyConstant_of_cover {T : C} (hT : IsTerminal T)
    (F : Sheaf J A) {I : Type*} {X : I → C} {f : ∀ i, X i ⟶ T}
    (hf : Sieve.ofArrows X f ∈ J T)
    (hc : ∀ i, Sheaf.IsConstant (J.over (X i)) ((J.overPullback A (X i)).obj F)) :
    IsLocallyConstant J F where
  exists_cover U := by
    refine ⟨Σ V : C, {g : V ⟶ U // (Sieve.pullback (hT.from U) (Sieve.ofArrows X f)).arrows g},
      fun p => p.1, fun p => p.2.1,
      sieve_ofArrows_arrows_mem J _ (J.pullback_stable (hT.from U) hf), fun p => ?_⟩
    obtain ⟨i, ⟨h⟩⟩ := exists_hom_of_mem_pullback_ofArrows hT p.2.1 p.2.2
    have := hc i
    exact isConstant_overPullback_of_map J A h F

/-- **A single covering of a final object suffices for finite local constancy**, for arbitrary
concrete coefficients. The constant values produced by the hypothesis are the constant values
produced by the conclusion, so finiteness of them is preserved. This is
`Stacks.ConstantSheaf.isFiniteLocallyConstant_of_finite_cover` for coefficients other than sets. -/
public lemma isFiniteLocallyConstant_of_cover {FA : A → A → Type*} {CA : A → Type wc}
    [∀ P Q, FunLike (FA P Q) (CA P) (CA Q)] [ConcreteCategory.{wc} A FA]
    {T : C} (hT : IsTerminal T)
    (F : Sheaf J A) {I : Type*} {X : I → C} {f : ∀ i, X i ⟶ T}
    (hf : Sieve.ofArrows X f ∈ J T)
    (hc : ∀ i, ∃ E : A, Finite (CA E) ∧ Nonempty
      ((constantSheaf (J.over (X i)) A).obj E ≅ (J.overPullback A (X i)).obj F)) :
    IsFiniteLocallyConstant (FD := FA) (CD := CA) J F where
  exists_finite_cover U := by
    refine ⟨Σ V : C, {g : V ⟶ U // (Sieve.pullback (hT.from U) (Sieve.ofArrows X f)).arrows g},
      fun p => p.1, fun p => p.2.1,
      sieve_ofArrows_arrows_mem J _ (J.pullback_stable (hT.from U) hf), fun p => ?_⟩
    obtain ⟨i, ⟨h⟩⟩ := exists_hom_of_mem_pullback_ofArrows hT p.2.1 p.2.2
    obtain ⟨E, hE, ⟨c⟩⟩ := hc i
    exact ⟨E, hE, ⟨constantIsoOverPullbackOfMap J A h F E c⟩⟩

end Cover

/-! ### The slice of a left exact functor -/

section Slice

omit [Category.{w'} A] in
/-- The structure morphism of `(Over.star X).obj Z` is the first projection of `X ⨯ Z`. -/
public lemma over_star_obj_hom {E : Type u} [Category.{v} E] [HasBinaryProducts E] (X Z : E) :
    ((Over.star X).obj Z).hom = prod.fst :=
  prod.lift_fst _ _

variable (G : C ⥤ D) [PreservesFiniteLimits G] [HasFiniteLimits C] [HasFiniteLimits D]

omit [Category.{w'} A] in
/-- **The slice of a left exact functor commutes with the right adjoints of the two localization
functors.** On an object `Z` of `C` both composites are the projection of a product onto the factor
`G.obj X`, formed either as `G (X ⨯ Z)` or as `G X ⨯ G Z`, and the comparison is the product
comparison of `G`, an isomorphism because `G` is left exact.

This is the identity which makes the localization square of Tag 093R commute. -/
public def starPostIso (X : C) :
    Over.star X ⋙ Over.post (X := X) G ≅ G ⋙ Over.star (G.obj X) :=
  NatIso.ofComponents
    (fun Z => Over.isoMk (PreservesLimitPair.iso G X Z) (by
      dsimp only [Functor.comp_obj, Over.post, Over.mk_hom]
      rw [over_star_obj_hom, over_star_obj_hom, PreservesLimitPair.iso_hom]
      exact prodComparison_fst G X Z))
    (fun {Z Z'} g => by
      apply Over.OverMorphism.ext
      change G.map (prod.map (𝟙 X) g) ≫ prodComparison G X Z' =
        prodComparison G X Z ≫ prod.map (𝟙 (G.obj X)) (G.map g)
      simpa using prodComparison_natural G (𝟙 X) g)

omit [Category.{w'} A] [HasFiniteLimits D] in
/-- **Continuity of the slice of a left exact, cover-preserving functor.** This is what discharges
the instance hypothesis `(Over.post G).IsContinuous (J.over X) (K.over (G.obj X))` of the main
theorems.

Cover preservation of the slice is `CategoryTheory.CoverPreserving.overPost`, and compatibility is
automatic because a left exact functor is representably flat and so is its slice. -/
public theorem isContinuous_overPost (hG : CoverPreserving J K G) (X : C) :
    (Over.post (X := X) G).IsContinuous (J.over X) (K.over (G.obj X)) :=
  have : RepresentablyFlat (Over.post (X := X) G) :=
    flat_of_preservesFiniteLimits (Over.post (X := X) G)
  Functor.isContinuous_of_coverPreserving
    (compatiblePreservingOfFlat (K.over (G.obj X)) (Over.post (X := X) G)) (hG.overPost X)

/-- The slice of `G` carries the final object of `C/X` to the final object of `D/(G.obj X)`: it
sends the identity of `X` to the image of the identity, which is the identity of `G.obj X`. -/
public def postMkIdIso (X : C) :
    (Over.post (X := X) G).obj (Over.mk (𝟙 X)) ≅ Over.mk (𝟙 (G.obj X)) :=
  Over.isoMk (Iso.refl _) (by
    dsimp only [Over.post, Over.mk_hom]
    simp)

end Slice

/-! ### Images of coverings -/

section CoverImage

/-- The image under a cover-preserving functor of a covering family of an object of `C` is a
covering family of its image. -/
public lemma sieve_ofArrows_map_mem (G : C ⥤ D) (hG : CoverPreserving J K G) {T : C}
    {I : Type*} {X : I → C} {f : ∀ i, X i ⟶ T} (hf : Sieve.ofArrows X f ∈ J T) :
    Sieve.ofArrows (fun i => G.obj (X i)) (fun i => G.map (f i)) ∈ K (G.obj T) := by
  refine K.superset_covering ?_ (hG.cover_preserve hf)
  rintro Z g ⟨W, a, b, hb, rfl⟩
  obtain ⟨i, h, rfl⟩ := (Sieve.mem_ofArrows_iff _ _ _).mp hb
  exact (Sieve.mem_ofArrows_iff _ _ _).mpr ⟨i, b ≫ G.map h, by simp⟩

end CoverImage

/-! ### The localization square and Tag 093R -/

section Main

variable [HasFiniteLimits C] [HasFiniteLimits D]
  [HasWeakSheafify J A] [HasWeakSheafify K A]
  [∀ U : C, HasWeakSheafify (J.over U) A] [∀ V : D, HasWeakSheafify (K.over V) A]
  (G : C ⥤ D) [G.IsContinuous J K] [PreservesFiniteLimits G]
  [(G.sheafPushforwardContinuous A J K).IsRightAdjoint]
  [∀ X : C, (Over.post (X := X) G).IsContinuous (J.over X) (K.over (G.obj X))]
  [∀ X : C, ((Over.post (X := X) G).sheafPushforwardContinuous A
    (J.over X) (K.over (G.obj X))).IsRightAdjoint]

/-- **The localization square of Tag 093R.** Restricting to `G.obj X` after taking the inverse image
along `G` is the same as taking the inverse image along the slice `Over.post G` after restricting
to `X`.

Both composites are left adjoints. Their right adjoints are the pushforwards along
`G ⋙ Over.star (G.obj X)` and along `Over.star X ⋙ Over.post G` respectively, and these two
functors of sites agree by `Stacks.ConstantSheaf.starPostIso`; uniqueness of left adjoints does the
rest. -/
public def overPullbackSheafPullbackIso (X : C) :
    G.sheafPullback A J K ⋙ K.overPullback A (G.obj X) ≅
      J.overPullback A X ⋙
        (Over.post (X := X) G).sheafPullback A (J.over X) (K.over (G.obj X)) :=
  letI : (Over.star X ⋙ Over.post (X := X) G).IsContinuous J (K.over (G.obj X)) :=
    Functor.isContinuous_comp _ _ J (J.over X) (K.over (G.obj X))
  letI : (G ⋙ Over.star (G.obj X)).IsContinuous J (K.over (G.obj X)) :=
    Functor.isContinuous_comp _ _ J K (K.over (G.obj X))
  Adjunction.leftAdjointUniq
    (((G.sheafAdjunctionContinuous A J K).comp
        ((Over.forgetAdjStar (G.obj X)).sheafPushforwardAdjunction A)).ofNatIsoRight
      (Functor.sheafPushforwardContinuousComp'
          (Iso.refl (G ⋙ Over.star (G.obj X))) A J K (K.over (G.obj X)) ≪≫
        (Functor.sheafPushforwardContinuousIso (starPostIso G X) A J
          (K.over (G.obj X))).symm ≪≫
        (Functor.sheafPushforwardContinuousComp'
          (Iso.refl (Over.star X ⋙ Over.post (X := X) G)) A J (J.over X)
          (K.over (G.obj X))).symm))
    (((Over.forgetAdjStar X).sheafPushforwardAdjunction A).comp
      ((Over.post (X := X) G).sheafAdjunctionContinuous A (J.over X) (K.over (G.obj X))))

/-- **A constant value survives inverse image, with the same value.** If `F` restricted to `X` is
the constant sheaf on `E`, then `G^* F` restricted to `G.obj X` is the constant sheaf on the same
`E`. -/
public def constantIsoOverPullbackSheafPullback (X : C) (F : Sheaf J A) (E : A)
    (c : (constantSheaf (J.over X) A).obj E ≅ (J.overPullback A X).obj F) :
    (constantSheaf (K.over (G.obj X)) A).obj E ≅
      (K.overPullback A (G.obj X)).obj ((G.sheafPullback A J K).obj F) :=
  (sheafPullbackConstantSheafIso (Over.post (X := X) G) A (J.over X) (K.over (G.obj X))
      Over.mkIdTerminal Over.mkIdTerminal (postMkIdIso G X)).symm.app E ≪≫
    ((Over.post (X := X) G).sheafPullback A (J.over X) (K.over (G.obj X))).mapIso c ≪≫
    ((overPullbackSheafPullbackIso J K A G X).app F).symm

section Conclusion

variable (hG : CoverPreserving J K G)

omit [HasWeakSheafify J A] [HasWeakSheafify K A] in
include hG in
/-- **Tag 093R, for a morphism of sites.** The inverse image of a locally constant sheaf along a
continuous functor of sites is locally constant, for arbitrary coefficients.

The trivializing covering is taken over the final object of `C`, whose image is final in `D`
because `G` is left exact; no object with a final image has to be supplied.

The source states the tag for an arbitrary morphism of topoi, whose inverse image need not be
induced by a functor between the two sites; the attribute is qualified accordingly. -/
@[stacks 093R "locally constant sheaves with arbitrary coefficients, for the inverse image \
  along a morphism of sites"]
public lemma isLocallyConstant_sheafPullback (F : Sheaf J A) [hF : IsLocallyConstant J F] :
    IsLocallyConstant K ((G.sheafPullback A J K).obj F) := by
  obtain ⟨I, X, f, hf, hc⟩ := hF.exists_cover (⊤_ C)
  refine isLocallyConstant_of_cover K A (IsTerminal.isTerminalObj G (⊤_ C) terminalIsTerminal) _
    (sieve_ofArrows_map_mem J K G hG hf) fun i => ?_
  obtain ⟨E, ⟨c⟩⟩ := Sheaf.mem_essImage_of_isConstant (J.over (X i))
    ((J.overPullback A (X i)).obj F)
  exact ⟨E, ⟨constantIsoOverPullbackSheafPullback J K A G (X i) F E c⟩⟩

end Conclusion

section Finite

variable {FA : A → A → Type*} {CA : A → Type wc} [∀ P Q, FunLike (FA P Q) (CA P) (CA Q)]
  [ConcreteCategory.{wc} A FA]
  (hG : CoverPreserving J K G)

omit [HasWeakSheafify J A] [HasWeakSheafify K A] in
include hG in
/-- **Tag 093R.** The inverse image of a finite locally constant sheaf along a continuous functor of
sites is finite locally constant, for arbitrary concrete coefficients. In particular this holds for
sheaves of abelian groups, which is the case Tag 03RZ (2) needs.

One trivializing covering `{X i ⟶ ⊤_C}` is enough, by
`Stacks.ConstantSheaf.isFiniteLocallyConstant_of_cover`. Its image under `G` covers `G.obj ⊤_C`,
which is final in `D` because `G` is left exact, and on a member the restriction of `G^* F` is
constant with the same finite value, by
`Stacks.ConstantSheaf.constantIsoOverPullbackSheafPullback`. -/
@[stacks 093R "finite locally constant sheaves with arbitrary concrete coefficients, for the \
  inverse image along a morphism of sites"]
public lemma isFiniteLocallyConstant_sheafPullback_of_coverPreserving (F : Sheaf J A)
    [hF : IsFiniteLocallyConstant (FD := FA) (CD := CA) J F] :
    IsFiniteLocallyConstant (FD := FA) (CD := CA) K ((G.sheafPullback A J K).obj F) := by
  obtain ⟨I, X, f, hf, hc⟩ := hF.exists_finite_cover (⊤_ C)
  refine isFiniteLocallyConstant_of_cover K A
    (IsTerminal.isTerminalObj G (⊤_ C) terminalIsTerminal) _
    (sieve_ofArrows_map_mem J K G hG hf) fun i => ?_
  obtain ⟨E, hE, ⟨c⟩⟩ := hc i
  exact ⟨E, hE, ⟨constantIsoOverPullbackSheafPullback J K A G (X i) F E c⟩⟩

end Finite

end Main

end Stacks.ConstantSheaf

end
