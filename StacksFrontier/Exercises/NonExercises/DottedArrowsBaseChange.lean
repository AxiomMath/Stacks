module

public import Mathlib.Tactic.CategoryTheory.Bicategory.Basic
import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.DottedArrows.BaseChange
public import StacksFrontier.CategoryTheory.DottedArrows.Defs
public import StacksFrontier.CategoryTheory.TwoFibreProduct.Defs

/-!
# Dotted arrows and base change along a 2-cartesian square

Split a 2-commutative rectangle in a `(2,1)`-category into a left square with witness `γ'` and
a right square with witness `φ`, and suppose the right square is 2-cartesian. Then the category
of dotted arrows of the left square is equivalent to the category of dotted arrows of the outer
rectangle, whose witness is the bicategorical pasting of the two given 2-cells.

The 2-cartesian hypothesis is the 2-universal property itself, `IsTwoCartesian`: every test
cone factors through the square, and any two factorizations of one cone are joined by a unique
compatible 2-isomorphism. That is the only hypothesis the equivalence needs, and the
equivalence is built from the functor sending a dotted 1-morphism `a` of the left square to
`a ≫ q`, which is shown to be full, faithful and essentially surjective.

That construction -- `TwoFiberCone`, `TwoFiberFactorization`, `IsTwoCartesian`,
`IsoDottedArrow`, `dottedFunctor` and the equivalence `dottedArrows_equiv` of Tag 0H1A -- lives
in `StacksFrontier/CategoryTheory/DottedArrows/BaseChange.lean` and is imported here. This file
adds the two things that are not in it: the equivalence with the bare-2-morphism dotted arrows
of `CategoryTheory.DottedArrow`, and the passage from a 2-fibre product in the terminal-object
form of Stacks 003Q to `IsTwoCartesian`.

A 2-fibre product is also available here in the terminal-object form of Stacks 003Q, as a
terminal object of the category of 2-commutative cones; terminality there is taken after cone
morphisms have been quotiented by 2-isomorphism, so it does not on its own express the full
2-universal property. `nonempty_isTwoCartesian_of_isTwoFibreProduct` upgrades it, given the
missing uniqueness clause, which for a 2-fibre product of algebraic stacks is the uniqueness
half of its 2-universal property. Consumers holding such a square go through that lemma, so
the clause is not a hypothesis of the theorem below.

The `(2,1)`-hypothesis is `Bicategory.IsLocallyGroupoid`, under which the dotted arrows of a
square form a groupoid; the data of a dotted arrow is carried as bare 2-morphisms by
`CategoryTheory.DottedArrow`, so the argument runs through the equivalent iso-valued form
`IsoDottedArrow` and transports the result back. Composition is diagrammatic, so the classical
`g ∘ f` is `f ≫ g` and the classical `τ ∘ σ` is `σ ≫ τ`; associators are written out even
where they are identities on the underlying 1-morphisms, to keep whiskered composites
well-typed.

## Main results

* `CategoryTheory.DottedArrowBaseChange.dottedArrows_baseChange_equivalence`: the categories of
  dotted arrows of the left square and of the outer rectangle are equivalent.
* `CategoryTheory.DottedArrowBaseChange.nonempty_isTwoCartesian_of_isTwoFibreProduct`: a
  2-fibre product in the terminal-object form of Stacks 003Q whose projections jointly detect
  2-isomorphisms is 2-cartesian.

## References

* [Stacks Project, Tag 0CLE](https://stacks.math.columbia.edu/tag/0CLE)
-/


@[expose] public section

open CategoryTheory
open CategoryTheory.Bicategory

namespace CategoryTheory.DottedArrowBaseChange

variable {B : Type*} [Bicategory B] [Bicategory.IsLocallyGroupoid B]

private noncomputable def toIsoDottedFunctor {S T X Y : B}
    {x : S ⟶ X} {j : S ⟶ T} {f : X ⟶ Y} {y : T ⟶ Y}
    {γ : (j ≫ y) ≅ (x ≫ f)} :
    CategoryTheory.DottedArrow x j f y γ.hom ⥤
      IsoDottedArrow x j f y γ where
  obj d :=
    { a := d.a
      α := asIso d.α
      β := asIso d.β
      compat := d.compat }
  map {d d'} h :=
    { θ := h.θ
      compat_α := by simpa only [asIso_hom] using h.cond_α
      compat_β := by simpa only [asIso_hom] using h.cond_β }
  map_id d := IsoDottedArrowHom.ext rfl
  map_comp h h' := IsoDottedArrowHom.ext rfl

private theorem toIsoDottedFunctor_essSurj {S T X Y : B}
    {x : S ⟶ X} {j : S ⟶ T} {f : X ⟶ Y} {y : T ⟶ Y}
    {γ : (j ≫ y) ≅ (x ≫ f)} :
    (toIsoDottedFunctor (γ := γ)).EssSurj := by
  constructor; intro d
  let e : CategoryTheory.DottedArrow x j f y γ.hom :=
    { a := d.a, α := d.α.hom, β := d.β.hom, compat := by simpa using d.compat }
  refine ⟨e, ?_⟩
  refine ⟨IsoDottedArrow.isoOfIso (Iso.refl e.a) ?_ ?_⟩
  · dsimp [toIsoDottedFunctor, e, IsoDottedArrow.isoOfIso]; simp
  · dsimp [toIsoDottedFunctor, e, IsoDottedArrow.isoOfIso]; simp

private theorem toIsoDottedFunctor_faithful {S T X Y : B}
    {x : S ⟶ X} {j : S ⟶ T} {f : X ⟶ Y} {y : T ⟶ Y}
    {γ : (j ≫ y) ≅ (x ≫ f)} :
    (toIsoDottedFunctor (γ := γ)).Faithful := by
  constructor; intro d d' h₁ h₂ hh
  exact DottedArrow.Hom.ext (congrArg IsoDottedArrowHom.θ hh)

private theorem toIsoDottedFunctor_full {S T X Y : B}
    {x : S ⟶ X} {j : S ⟶ T} {f : X ⟶ Y} {y : T ⟶ Y}
    {γ : (j ≫ y) ≅ (x ≫ f)} :
    (toIsoDottedFunctor (γ := γ)).Full := by
  constructor; intro d d' h
  refine ⟨{ θ := h.θ, cond_α := ?_, cond_β := ?_ }, ?_⟩
  · simpa only [toIsoDottedFunctor, asIso_hom] using h.compat_α
  · simpa only [toIsoDottedFunctor, asIso_hom] using h.compat_β
  · exact IsoDottedArrowHom.ext rfl

private noncomputable def toIsoDottedEquivalence {S T X Y : B}
    {x : S ⟶ X} {j : S ⟶ T} {f : X ⟶ Y} {y : T ⟶ Y}
    {γ : (j ≫ y) ≅ (x ≫ f)} :
    CategoryTheory.DottedArrow x j f y γ.hom ≌
      IsoDottedArrow x j f y γ :=
  have : (toIsoDottedFunctor (γ := γ)).IsEquivalence :=
    { faithful := toIsoDottedFunctor_faithful
      full := toIsoDottedFunctor_full
      essSurj := toIsoDottedFunctor_essSurj }
  (toIsoDottedFunctor (γ := γ)).asEquivalence

@[implicit_reducible]
private def coneSquare {X Y' Y W : B} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (c : TwoFiberCone f g W) :
    TwoCommSq f g where
  pt := W
  fst := c.a
  snd := c.b
  iso := c.ψ.symm

omit [Bicategory.IsLocallyGroupoid B] in
private theorem terminal_cone_preHom {X' X Y' Y W : B}
    {q : X' ⟶ X} {p : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (φ : (p ≫ g) ≅ (q ≫ f))
    (hcart : IsTwoFibreProduct
      ({ pt := X', fst := q, snd := p, iso := φ.symm } : TwoCommSq f g))
    (c : TwoFiberCone f g W) :
    ∃ F : TwoCommSq.PreHom (coneSquare c)
      ({ pt := X', fst := q, snd := p, iso := φ.symm } : TwoCommSq f g),
      Quotient.mk _ F = hcart.from (coneSquare c) :=
  Quotient.exists_rep (hcart.from (coneSquare c))

private def factorizationOfPreHom {X' X Y' Y W : B}
    {q : X' ⟶ X} {p : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (φ : (p ≫ g) ≅ (q ≫ f)) (c : TwoFiberCone f g W)
    (F : TwoCommSq.PreHom (coneSquare c)
      ({ pt := X', fst := q, snd := p, iso := φ.symm } : TwoCommSq f g)) :
    TwoFiberFactorization q p f g φ c where
  h := F.hom
  eq := F.isoFst.symm
  ep := F.isoSnd.symm
  compat := by
    have hpre := F.compat
    dsimp [coneSquare] at hpre
    have hpreAssoc :
        (c.ψ.symm.hom ≫ (F.isoSnd.hom ▷ g)) ≫ (α_ F.hom p g).hom =
          ((F.isoFst.hom ▷ f) ≫ (α_ F.hom q f).hom) ≫
            (F.hom ◁ φ.symm.hom) := by
      simpa only [Iso.symm_hom, Category.assoc] using hpre
    have hpre' :
        c.ψ.symm.hom ≫ (F.isoSnd.hom ▷ g) =
          (F.isoFst.hom ▷ f) ≫ (α_ F.hom q f).hom ≫
            (F.hom ◁ φ.symm.hom) ≫ (α_ F.hom p g).inv := by
      calc
        c.ψ.symm.hom ≫ (F.isoSnd.hom ▷ g) =
            (c.ψ.symm.hom ≫ (F.isoSnd.hom ▷ g)) ≫
              (α_ F.hom p g).hom ≫ (α_ F.hom p g).inv := by
                simp
        _ = ((F.isoFst.hom ▷ f) ≫ (α_ F.hom q f).hom ≫
              (F.hom ◁ φ.symm.hom)) ≫ (α_ F.hom p g).inv := by
                rw [← Category.assoc, hpreAssoc]
                simp [Category.assoc]
        _ = (F.isoFst.hom ▷ f) ≫ (α_ F.hom q f).hom ≫
              (F.hom ◁ φ.symm.hom) ≫ (α_ F.hom p g).inv := by
                simp [Category.assoc]
    let : IsIso (c.ψ.symm.hom) := inferInstance
    let : IsIso (F.isoSnd.hom ▷ g) := inferInstance
    let : IsIso (F.isoFst.hom ▷ f) := inferInstance
    let : IsIso ((α_ F.hom q f).hom) := inferInstance
    let : IsIso (F.hom ◁ φ.symm.hom) := inferInstance
    let : IsIso ((α_ F.hom p g).inv) := inferInstance
    let : IsIso (c.ψ.symm.hom ≫ (F.isoSnd.hom ▷ g)) := IsIso.comp_isIso
    let : IsIso ((F.isoFst.hom ▷ f) ≫ (α_ F.hom q f).hom) :=
      IsIso.comp_isIso
    let : IsIso ((F.isoFst.hom ▷ f) ≫ (α_ F.hom q f).hom ≫
      (F.hom ◁ φ.symm.hom)) := IsIso.comp_isIso
    let : IsIso ((F.isoFst.hom ▷ f) ≫ (α_ F.hom q f).hom ≫
      (F.hom ◁ φ.symm.hom) ≫ (α_ F.hom p g).inv) := IsIso.comp_isIso
    have hfac := congrArg
      (fun τ : (c.a ≫ f) ⟶ ((F.hom ≫ p) ≫ g) => inv τ) hpre'
    simp only [IsIso.inv_comp, inv_whiskerRight, inv_whiskerLeft,
      Iso.symm_hom] at hfac
    rw [IsIso.inv_eq_of_hom_inv_id (f := F.isoSnd.hom) (g := F.isoSnd.inv)
        F.isoSnd.hom_inv_id,
      IsIso.inv_eq_of_hom_inv_id (f := φ.inv) (g := φ.hom) φ.inv_hom_id,
      IsIso.inv_eq_of_hom_inv_id (f := (α_ F.hom q f).hom)
        (g := (α_ F.hom q f).inv) (α_ F.hom q f).hom_inv_id,
      IsIso.inv_eq_of_hom_inv_id (f := F.isoFst.hom) (g := F.isoFst.inv)
        F.isoFst.hom_inv_id] at hfac
    simpa [Category.assoc, Iso.symm_hom] using hfac

@[implicit_reducible]
private def preHomOfFactorization {X' X Y' Y W : B}
    {q : X' ⟶ X} {p : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (φ : (p ≫ g) ≅ (q ≫ f)) (c : TwoFiberCone f g W)
    (F : TwoFiberFactorization q p f g φ c) :
    TwoCommSq.PreHom (coneSquare c)
      ({ pt := X', fst := q, snd := p, iso := φ.symm } : TwoCommSq f g) where
  hom := F.h
  isoFst := F.eq.symm
  isoSnd := F.ep.symm
  compat := by
    dsimp only [coneSquare]
    have hIso :
        (whiskerRightIso F.ep g ≪≫ c.ψ) =
          (α_ F.h p g ≪≫ whiskerLeftIso F.h φ ≪≫ (α_ F.h q f).symm ≪≫
            whiskerRightIso F.eq f) := by
      apply Iso.ext
      simpa [Category.assoc] using F.compat
    calc
      c.ψ.symm.hom ≫ (F.ep.symm.hom ▷ g) ≫ (α_ F.h p g).hom =
          (whiskerRightIso F.ep g ≪≫ c.ψ).symm.hom ≫ (α_ F.h p g).hom := by
              simp [Category.assoc]
      _ = (α_ F.h p g ≪≫ whiskerLeftIso F.h φ ≪≫ (α_ F.h q f).symm ≪≫
            whiskerRightIso F.eq f).symm.hom ≫ (α_ F.h p g).hom := by rw [hIso]
      _ = (F.eq.inv ▷ f) ≫ (α_ F.h q f).hom ≫ (F.h ◁ φ.inv) := by
            simp [Category.assoc]

/-- Cancelling the inverses of two isomorphisms with a common target on either side. -/
private theorem inv_comp_eq_inv_iff {C : Type*} [Category C] {X X' Y : C}
    (e₁ : X ≅ Y) (e₂ : X' ≅ Y) (τ : X ⟶ X') :
    e₁.inv ≫ τ = e₂.inv ↔ τ ≫ e₂.hom = e₁.hom := by
  rw [Iso.inv_comp_eq, Iso.eq_comp_inv]

private noncomputable def twoCartesian_of_terminal {X' X Y' Y : B}
    {q : X' ⟶ X} {p : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (φ : (p ≫ g) ≅ (q ≫ f))
    (hcart : IsTwoFibreProduct
      ({ pt := X', fst := q, snd := p, iso := φ.symm } : TwoCommSq f g))
    (huniq : ∀ (C : TwoCommSq f g)
      (F G : TwoCommSq.PreHom C
        ({ pt := X', fst := q, snd := p, iso := φ.symm } : TwoCommSq f g))
      (ρ σ : F.hom ≅ G.hom),
      ((F.isoFst.hom ≫ (ρ.hom ▷ q) = G.isoFst.hom) ∧
        (F.isoSnd.hom ≫ (ρ.hom ▷ p) = G.isoSnd.hom)) →
      ((F.isoFst.hom ≫ (σ.hom ▷ q) = G.isoFst.hom) ∧
        (F.isoSnd.hom ≫ (σ.hom ▷ p) = G.isoSnd.hom)) → ρ = σ) :
    IsTwoCartesian q p f g φ where
  fac := by
    intro W c
    let F := Classical.choose (terminal_cone_preHom φ hcart c)
    exact factorizationOfPreHom φ c F
  uniq := by
    intro W c F G
    let F₀ := preHomOfFactorization φ c F
    let G₀ := preHomOfFactorization φ c G
    have heq : Quotient.mk _ F₀ = Quotient.mk _ G₀ := hcart.hom_ext _ _
    obtain ⟨ρ, hq, hp⟩ := Quotient.exact heq
    change F.eq.inv ≫ (ρ.hom ▷ q) = G.eq.inv at hq
    change F.ep.inv ≫ (ρ.hom ▷ p) = G.ep.inv at hp
    refine ⟨ρ, ⟨(inv_comp_eq_inv_iff _ _ _).1 hq, (inv_comp_eq_inv_iff _ _ _).1 hp⟩, ?_⟩
    intro σ hσ
    exact (huniq (coneSquare c) F₀ G₀ ρ σ ⟨hq, hp⟩
      ⟨(inv_comp_eq_inv_iff _ _ _).2 hσ.1, (inv_comp_eq_inv_iff _ _ _).2 hσ.2⟩).symm

/-- **A terminal $2$-commutative square whose projections jointly detect $2$-isomorphisms is
$2$-cartesian.**

Terminality in the category of $2$-commutative diagrams (`IsTwoFibreProduct`, Stacks 003Q) is
taken after the morphisms of that category have been quotiented by $2$-isomorphism, so it does
not by itself record that the mediating $2$-isomorphism is unique. The hypothesis `huniq` is
exactly that missing clause, and together the two give the $2$-universal property
`IsTwoCartesian` in the explicit existence-and-uniqueness form.

This is how a consumer holding a $2$-fibre product built as a terminal object — for instance a
$2$-fibre product of algebraic stacks, where `huniq` is the uniqueness half of the $2$-universal
property — supplies the $2$-cartesian hypothesis of `dottedArrows_baseChange_equivalence`
(Stacks 0CLE). -/
theorem nonempty_isTwoCartesian_of_isTwoFibreProduct {X' X Y' Y : B}
    {q : X' ⟶ X} {p : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (φ : (p ≫ g) ≅ (q ≫ f))
    (hcart : IsTwoFibreProduct
      ({ pt := X', fst := q, snd := p, iso := φ.symm } : TwoCommSq f g))
    (huniq : ∀ (C : TwoCommSq f g)
      (F G : TwoCommSq.PreHom C
        ({ pt := X', fst := q, snd := p, iso := φ.symm } : TwoCommSq f g))
      (ρ σ : F.hom ≅ G.hom),
      ((F.isoFst.hom ≫ (ρ.hom ▷ q) = G.isoFst.hom) ∧
        (F.isoSnd.hom ≫ (ρ.hom ▷ p) = G.isoSnd.hom)) →
      ((F.isoFst.hom ≫ (σ.hom ▷ q) = G.isoFst.hom) ∧
        (F.isoSnd.hom ≫ (σ.hom ▷ p) = G.isoSnd.hom)) → ρ = σ) :
    Nonempty (IsTwoCartesian q p f g φ) :=
  ⟨twoCartesian_of_terminal φ hcart huniq⟩
/-- **Stacks 0CLE.** The category of dotted arrows is invariant under base change along a
$2$-cartesian square.

Split a $2$-commutative rectangle into a left square, filled by `γ'`, and a right square,
filled by `φ` and assumed $2$-cartesian. Then the category of dotted arrows of the left square
is equivalent to the category of dotted arrows of the outer rectangle, whose filler is the
pasting of `γ'` and `φ`. -/
@[stacks 0CLE]
theorem dottedArrows_baseChange_equivalence
    {S T X X' Y Y' : B}
    (j : S ⟶ T) (x' : S ⟶ X') (q : X' ⟶ X) (p : X' ⟶ Y')
    (f : X ⟶ Y) (y' : T ⟶ Y') (g : Y' ⟶ Y)
    (φ : (p ≫ g) ≅ (q ≫ f)) (γ' : (j ≫ y') ≅ (x' ≫ p))
    (hcart : IsTwoCartesian q p f g φ) :
    Nonempty (CategoryTheory.DottedArrow x' j p y' γ'.hom ≌
      CategoryTheory.DottedArrow (x' ≫ q) j f (y' ≫ g)
          ((α_ j y' g).symm ≪≫ whiskerRightIso γ' g ≪≫ (α_ x' p g) ≪≫
            whiskerLeftIso x' φ ≪≫ (α_ x' q f).symm).hom) :=
by
  have hgpd : ∀ {A C : B} {u v : A ⟶ C} (θ : u ⟶ v), IsIso θ := by intros; infer_instance
  let γO := outerGamma φ γ'
  obtain ⟨e⟩ := dottedArrows_equiv
    hgpd j x' q p f y' g φ γ' hcart
  exact ⟨(toIsoDottedEquivalence (γ := γ')).trans e |>.trans
    (toIsoDottedEquivalence (γ := γO)).symm⟩

end CategoryTheory.DottedArrowBaseChange

end
