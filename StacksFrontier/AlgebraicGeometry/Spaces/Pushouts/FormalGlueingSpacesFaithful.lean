module

public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.FormalGlueingSpaces

/-!
# Faithfulness of the formal glueing functor for algebraic spaces

In a formal glueing situation `(f : Y ⟶ X, Z, U = X \ Z, V = Y \ f⁻¹(Z))` the restriction
functor of Stacks 0AF3 sends an algebraic space over `X` to its restrictions to `U` and to `Y`
together with the identification of their further restrictions to `V`. This module proves that
that functor is *faithful*: two morphisms of algebraic spaces over `X` with the same
restrictions to `U` and to `Y` are equal.

## Main results

* `AlgebraicGeometry.Space.FormalGlueingSituation.injective_formalGlueingFunctor_map`: two
  morphisms of algebraic spaces over `X` with the same image under the functor of Stacks 0AF3
  are equal.
* `AlgebraicGeometry.Space.FormalGlueingSituation.faithful_formalGlueingFunctor`: the same
  statement, as faithfulness of that functor.

## Implementation notes

*What this is and is not.* Stacks 0AF6 says that the functor of Stacks 0AF3 induces a
*bijection* `Mor_X(X'₁, X'₂) ⟶ Mor(F X'₁, F X'₂)` whenever `X'₂ ⟶ X` is separated. What is
proved here is the injectivity of that map, and it is proved without the separation hypothesis,
which the source consumes only for surjectivity. The bijection is
`FormalGlueingSituation.bijective_formalGlueingFunctor_map_of_isSeparated`
(`StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.FormalGlueingSpacesSeparatedBijection`), whose
surjectivity comes from the essential-surjectivity half of Stacks 0AF4 for closed immersions.

Surjectivity cannot be replaced by descent along the fpqc covering of Stacks 0AF1, even though
descent of morphisms along such a covering is available. A morphism of glueing data records an
agreement of its two components over `V` only. For two members of that covering which both
factor through `Y`, the two candidate morphisms on their overlap are the two restrictions of
the `Y`-component along the two projections of `Y ×_X Y`, and no part of the data identifies
them; the identification is a consequence of the glueing theorem for quasi-coherent modules,
not a step towards it.

*The proof.* Injectivity is the reflection of isomorphisms, Stacks 0AF5, applied to the
relative equalizer. For `a, b : X'₁ ⟶ X'₂` over `X`, let `Q = X'₂ ×_X X'₂`, let `d : X'₂ ⟶ Q`
be its diagonal — a split monomorphism, split by either projection — and let `m : X'₁ ⟶ Q` be
`(a, b)`. The pullback `E` of `m` along `d` is the locus where `a` and `b` agree: its first
projection `p : E ⟶ X'₁` satisfies `p ≫ a = p ≫ b`, so `a = b` as soon as `p` is an
epimorphism. `E` is an algebraic space because `Q` is one and because a presheaf fibre product
of algebraic spaces over an algebraic space is one (Stacks 02X2). Restricting along a morphism
`g`, the hypothesis gives `pullback.fst X'₁.hom g ≫ a = pullback.fst X'₁.hom g ≫ b`, which is
exactly a factorization of the restricted `m` through the restricted `d`, and
`isIso_baseChange_fst_of_isPullback` turns such a factorization into invertibility of the
restriction of `p`: the factorization is a section, and `d` being a monomorphism makes it a
two-sided inverse. So the restrictions of `p` to `U` and to `Y` are invertible, and Stacks 0AF5
makes `p` invertible.

The objects `m`, `d` and `E` are introduced by `obtain` from an existence statement rather than
by `set`, so that they stay opaque: the characterising equations are all that the rest of the
argument uses, and leaving the defining terms in the context makes the unifier re-examine them
at every step.

## References

* [Stacks Project, Tag 02X2](https://stacks.math.columbia.edu/tag/02X2)
* [Stacks Project, Tag 0AF3](https://stacks.math.columbia.edu/tag/0AF3)
* [Stacks Project, Tag 0AF5](https://stacks.math.columbia.edu/tag/0AF5)
* [Stacks Project, Tag 0AF6](https://stacks.math.columbia.edu/tag/0AF6)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space.FormalGlueingSituation

/-! ### Generalities -/

/-- A morphism of a comma category whose two components are invertible is invertible. -/
private theorem isIso_commaMorphism {A₁ B₁ T : Type*} [Category A₁] [Category B₁] [Category T]
    {L : A₁ ⥤ T} {R : B₁ ⥤ T} {x y : Comma L R} (f : x ⟶ y)
    (hl : IsIso f.left) (hr : IsIso f.right) : IsIso f := by
  have := hl
  have := hr
  have heq : (Comma.isoMk (asIso f.left) (asIso f.right) f.w).hom = f :=
    Comma.hom_ext _ _ rfl rfl
  rw [← heq]
  infer_instance

/-- A morphism of a full subcategory whose underlying morphism is invertible is invertible. -/
private theorem isIso_of_isIso_hom {C : Type*} [Category C] {P : ObjectProperty C}
    {x y : P.FullSubcategory} (f : x ⟶ y) (h : IsIso f.hom) : IsIso f := by
  have : IsIso ((ObjectProperty.ι P).map f) := h
  exact isIso_of_reflects_iso f (ObjectProperty.ι P)

/-- Let `E` be the pullback of `m : T.left ⟶ Q` along a monomorphism `d : T₂ ⟶ Q`, with first
projection `p : E ⟶ T.left`, and let `g : W ⟶ X` be a morphism to the base. If the restriction
of `m` along `g` factors through `d`, then the restriction of `p` along `g` is invertible: the
factorization is a section of it, and `d` being a monomorphism makes that section a two-sided
inverse. -/
private theorem isIso_baseChange_fst_of_isPullback
    {C : Type*} [Category C] [HasPullbacks C]
    {X W T T₂ Q E : C} (g : W ⟶ X) (t : T ⟶ X)
    {p : E ⟶ T} {q : E ⟶ T₂} {m : T ⟶ Q} {d : T₂ ⟶ Q} [Mono d]
    (hpb : IsPullback p q m d)
    (c : pullback t g ⟶ T₂) (hc : pullback.fst t g ≫ m = c ≫ d)
    (κ : pullback (p ≫ t) g ⟶ pullback t g)
    (hκfst : κ ≫ pullback.fst t g = pullback.fst (p ≫ t) g ≫ p)
    (hκsnd : κ ≫ pullback.snd t g = pullback.snd (p ≫ t) g) :
    IsIso κ := by
  have hLp : hpb.lift (pullback.fst t g) c hc ≫ p = pullback.fst t g := hpb.lift_fst _ _ _
  have hw : hpb.lift (pullback.fst t g) c hc ≫ p ≫ t = pullback.snd t g ≫ g := by
    rw [← Category.assoc, hLp]
    exact pullback.condition
  have hνfst : pullback.lift _ (pullback.snd t g) hw ≫ pullback.fst (p ≫ t) g =
      hpb.lift (pullback.fst t g) c hc := pullback.lift_fst _ _ _
  have hνsnd : pullback.lift (hpb.lift (pullback.fst t g) c hc) (pullback.snd t g) hw ≫
      pullback.snd (p ≫ t) g = pullback.snd t g := pullback.lift_snd _ _ _
  have hκL : κ ≫ hpb.lift (pullback.fst t g) c hc = pullback.fst (p ≫ t) g := by
    refine hpb.hom_ext ?_ ?_
    · rw [Category.assoc, hLp, hκfst]
    · rw [Category.assoc, hpb.lift_snd]
      refine (cancel_mono d).1 ?_
      rw [Category.assoc, ← hc, ← Category.assoc, hκfst, Category.assoc, Category.assoc, hpb.w]
  refine ⟨⟨pullback.lift (hpb.lift (pullback.fst t g) c hc) (pullback.snd t g) hw, ?_, ?_⟩⟩
  · refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, hνfst, hκL, Category.id_comp]
    · rw [Category.assoc, hνsnd, hκsnd, Category.id_comp]
  · refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, hκfst, ← Category.assoc, hνfst, hLp, Category.id_comp]
    · rw [Category.assoc, hκsnd, hνsnd, Category.id_comp]

/-- Restriction along `g` is compatible with the first projections. -/
theorem overPullback_map_left_comp_fst {C : Type*} [Category C] [HasPullbacks C]
    {X W : C} (g : W ⟶ X) {A A' : Over X} (f : A ⟶ A') :
    ((Over.pullback g).map f).left ≫ pullback.fst A'.hom g =
      pullback.fst A.hom g ≫ f.left := by
  dsimp [Over.pullback]
  exact pullback.lift_fst _ _ _

/-- Restriction along `g` is compatible with the second projections. -/
theorem overPullback_map_left_comp_snd {C : Type*} [Category C] [HasPullbacks C]
    {X W : C} (g : W ⟶ X) {A A' : Over X} (f : A ⟶ A') :
    ((Over.pullback g).map f).left ≫ pullback.snd A'.hom g = pullback.snd A.hom g := by
  dsimp [Over.pullback]
  exact pullback.lift_snd _ _ _

/-- Two morphisms of `Over X` with the same restriction along `g` have the same composite with
the first projection of the restriction of their source. -/
private theorem fst_comp_left_eq_of_map_eq {C : Type*} [Category C] [HasPullbacks C]
    {X W : C} (g : W ⟶ X) {T₁ T₂ : Over X} {a₀ b₀ : T₁ ⟶ T₂}
    (hg : (Over.pullback g).map a₀ = (Over.pullback g).map b₀) :
    pullback.fst T₁.hom g ≫ a₀.left = pullback.fst T₁.hom g ≫ b₀.left := by
  have h := congrArg (fun k : (Over.pullback g).obj T₁ ⟶ (Over.pullback g).obj T₂ ↦
    k.left ≫ pullback.fst T₂.hom g) hg
  rwa [overPullback_map_left_comp_fst g a₀, overPullback_map_left_comp_fst g b₀] at h

/-- The restriction along `g` of the first projection of the relative equalizer is invertible,
once the two morphisms have the same restriction along `g`. -/
private theorem isIso_overPullback_map_homMk {C : Type*} [Category C] [HasPullbacks C]
    {X W : C} (g : W ⟶ X) {T₁ T₂ : Over X} {Q E : C}
    {m : T₁.left ⟶ Q} {d : T₂.left ⟶ Q} [Mono d]
    {p : E ⟶ T₁.left} {q : E ⟶ T₂.left} (hpb : IsPullback p q m d)
    (c : pullback T₁.hom g ⟶ T₂.left) (hc : pullback.fst T₁.hom g ≫ m = c ≫ d) :
    IsIso ((Over.pullback g).map (Over.homMk p rfl : Over.mk (p ≫ T₁.hom) ⟶ T₁)) := by
  have : IsIso ((Over.forget W).map
      ((Over.pullback g).map (Over.homMk p rfl : Over.mk (p ≫ T₁.hom) ⟶ T₁))) :=
    isIso_baseChange_fst_of_isPullback g T₁.hom hpb c hc _
      (overPullback_map_left_comp_fst g (Over.homMk p rfl : Over.mk (p ≫ T₁.hom) ⟶ T₁))
      (overPullback_map_left_comp_snd g (Over.homMk p rfl : Over.mk (p ≫ T₁.hom) ⟶ T₁))
  exact isIso_of_reflects_iso _ (Over.forget W)

/-! ### Faithfulness -/

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- Two morphisms of algebraic spaces over `X` whose restrictions to `U` and to `Y` agree are
equal. This is the content of the faithfulness of the functor of Stacks 0AF3, read at the level
of `Over X`. -/
private theorem eq_of_overPullback_map_eq (D : FormalGlueingSituation B S hS)
    {T₁ T₂ : Over D.X} (h₁ : IsAlgebraicSpace B S hS T₁.left)
    (h₂ : IsAlgebraicSpace B S hS T₂.left) (a₀ b₀ : T₁ ⟶ T₂)
    (hU : (Over.pullback D.U.ι).map a₀ = (Over.pullback D.U.ι).map b₀)
    (hY : (Over.pullback D.f).map a₀ = (Over.pullback D.f).map b₀) :
    a₀ = b₀ := by
  -- the relative diagonal of `T₂`, kept opaque
  obtain ⟨d, hdfst, hdsnd⟩ : ∃ d : T₂.left ⟶ pullback T₂.hom T₂.hom,
      d ≫ pullback.fst T₂.hom T₂.hom = 𝟙 T₂.left ∧
        d ≫ pullback.snd T₂.hom T₂.hom = 𝟙 T₂.left :=
    ⟨pullback.lift (𝟙 T₂.left) (𝟙 T₂.left) rfl, pullback.lift_fst _ _ _,
      pullback.lift_snd _ _ _⟩
  have : IsSplitMono d := IsSplitMono.mk' ⟨pullback.fst T₂.hom T₂.hom, hdfst⟩
  -- the pair `(a₀, b₀)`, kept opaque
  obtain ⟨m, hmfst, hmsnd⟩ : ∃ m : T₁.left ⟶ pullback T₂.hom T₂.hom,
      m ≫ pullback.fst T₂.hom T₂.hom = a₀.left ∧
        m ≫ pullback.snd T₂.hom T₂.hom = b₀.left :=
    ⟨pullback.lift a₀.left b₀.left (by rw [Over.w, Over.w]), pullback.lift_fst _ _ _,
      pullback.lift_snd _ _ _⟩
  -- the relative equalizer, kept opaque
  obtain ⟨E, p, q, hpb, hE⟩ : ∃ (E : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (p : E ⟶ T₁.left)
      (q : E ⟶ T₂.left), IsPullback p q m d ∧ IsAlgebraicSpace B S hS E :=
    ⟨pullback m d, pullback.fst m d, pullback.snd m d, IsPullback.of_hasPullback m d,
      isAlgebraicSpace_pullback B S hS m d h₁ h₂
        (isAlgebraicSpace_pullback B S hS T₂.hom T₂.hom h₂ h₂ D.algebraicSpace_X)⟩
  -- the equalizer is where the two morphisms agree
  have hpa : p ≫ a₀.left = p ≫ b₀.left := by
    rw [← hmfst, ← hmsnd, ← Category.assoc, ← Category.assoc, hpb.w, Category.assoc,
      Category.assoc, hdfst, hdsnd]
  -- the restriction of `m` factors through `d` along either morphism
  have hc : ∀ {W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (g : W ⟶ D.X),
      pullback.fst T₁.hom g ≫ a₀.left = pullback.fst T₁.hom g ≫ b₀.left →
      pullback.fst T₁.hom g ≫ m = (pullback.fst T₁.hom g ≫ a₀.left) ≫ d := by
    intro W g hfst
    refine pullback.hom_ext ?_ ?_
    · simp [hmfst, hdfst]
    · simp [hmsnd, hdsnd, hfst]
  have hiso : ∀ {W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (g : W ⟶ D.X),
      (Over.pullback g).map a₀ = (Over.pullback g).map b₀ →
      IsIso ((Over.pullback g).map (Over.homMk p rfl : Over.mk (p ≫ T₁.hom) ⟶ T₁)) :=
    fun g hg => isIso_overPullback_map_homMk g hpb _ (hc g (fst_comp_left_eq_of_map_eq g hg))
  -- Stacks 0AF5 applies to the first projection, read in `spacesOverX D`
  have hcomma : IsIso ((restrictionDiagram D).map
      (Over.homMk p rfl : Over.mk (p ≫ T₁.hom) ⟶ T₁)) :=
    isIso_commaMorphism _ (hiso _ hU) (hiso _ hY)
  have hmap : IsIso ((formalGlueingFunctor D).1.map
      (⟨Over.homMk p rfl⟩ : (⟨Over.mk (p ≫ T₁.hom), hE⟩ : spacesOverX D) ⟶ ⟨T₁, h₁⟩)) :=
    isIso_of_isIso_hom _ ((NatIso.isIso_map_iff (formalGlueingFunctor D).2
      (⟨Over.homMk p rfl⟩ : (⟨Over.mk (p ≫ T₁.hom), hE⟩ : spacesOverX D) ⟶ ⟨T₁, h₁⟩)).2 hcomma)
  have : IsIso (⟨Over.homMk p rfl⟩ :
      (⟨Over.mk (p ≫ T₁.hom), hE⟩ : spacesOverX D) ⟶ ⟨T₁, h₁⟩) :=
    isIso_of_reflects_iso _ (formalGlueingFunctor D).1
  have : IsIso (Over.homMk p rfl : Over.mk (p ≫ T₁.hom) ⟶ T₁) :=
    Functor.map_isIso (ObjectProperty.ι _)
      (⟨Over.homMk p rfl⟩ : (⟨Over.mk (p ≫ T₁.hom), hE⟩ : spacesOverX D) ⟶ ⟨T₁, h₁⟩)
  have : IsIso p :=
    Functor.map_isIso (Over.forget D.X) (Over.homMk p rfl : Over.mk (p ≫ T₁.hom) ⟶ T₁)
  exact Over.OverMorphism.ext ((cancel_epi p).1 hpa)

/-- Two morphisms of algebraic spaces over `X` whose images under the restriction functor of
Stacks 0AF3 agree are equal.

This is the injectivity half of the bijection of Stacks 0AF6, and it needs no separation
hypothesis; see this module's implementation notes for what the other half needs. -/
theorem injective_formalGlueingFunctor_map (D : FormalGlueingSituation B S hS)
    {X₁ X₂ : spacesOverX D} (a b : X₁ ⟶ X₂)
    (h : (formalGlueingFunctor D).1.map a = (formalGlueingFunctor D).1.map b) : a = b := by
  have hcomp : ((formalGlueingFunctor D).1 ⋙ ObjectProperty.ι _).map a =
      ((formalGlueingFunctor D).1 ⋙ ObjectProperty.ι _).map b := by
    simp only [Functor.comp_map, h]
  have key : (restrictionDiagram D).map a.hom = (restrictionDiagram D).map b.hom := by
    have h1 := (formalGlueingFunctor D).2.hom.naturality a
    have h2 := (formalGlueingFunctor D).2.hom.naturality b
    rw [hcomp] at h1
    exact (cancel_epi ((formalGlueingFunctor D).2.hom.app X₁)).1 (h1.symm.trans h2)
  exact (ObjectProperty.ι _).map_injective
    (eq_of_overPullback_map_eq D X₁.property X₂.property a.hom b.hom
      (congrArg CommaMorphism.left key) (congrArg CommaMorphism.right key))

/-- **The faithfulness half of Stacks 0AF6.** The restriction functor of Stacks 0AF3 is
faithful on algebraic spaces over `X`.

Stacks 0AF6 itself, a bijection on hom-sets for a separated target, is
`FormalGlueingSituation.bijective_formalGlueingFunctor_map_of_isSeparated`. -/
instance faithful_formalGlueingFunctor (D : FormalGlueingSituation B S hS) :
    (formalGlueingFunctor D).1.Faithful :=
  ⟨fun {_ _ _ _} h => injective_formalGlueingFunctor_map D _ _ h⟩

end AlgebraicGeometry.Space.FormalGlueingSituation

end
