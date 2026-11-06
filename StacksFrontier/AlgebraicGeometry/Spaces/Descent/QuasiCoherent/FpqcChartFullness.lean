module

public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.QuasiCoherent.FpqcChartLocalization
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.QuasiCoherent.RefinementFullyFaithful
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.QuasiCoherent.SingleMemberFullness

/-!
# Fpqc descent of morphisms of quasi-coherent modules: fullness, localized at a represented base

Let `X` be an algebraic space over a scheme `S` of a big fppf site and let
`(f i : X i ⟶ X)` be an fpqc covering of `X` in the sense of Stacks 03MQ.  This file reduces the
*fullness* of the canonical descent functor of Stacks 04W5 for that family — the fullness half
of the full-faithfulness clause of Stacks 04W8 — to the same statement for an fpqc covering of a
*represented* algebraic space by represented algebraic spaces, that is to the fullness half of
Stacks 023T.

The represented case is stated here as
`AlgebraicGeometry.Space.QuasiCoherentDescent.ReprFpqcHomSurjective` and is taken as a
hypothesis.  For faithfulness, flatness of the members of the covering suffices and no base
enters, but fullness is not a consequence of flatness alone.  The represented case is stated for
**quasi-coherent** modules, as the descent statement of Stacks 04W8 is: fullness is a sheaf
condition on the presheaf of morphisms, and every fpqc sheaf condition in this tree is for
quasi-coherent modules.

The reduction has three steps.  Let `a : R ⟶ X` be a scheme atlas of `X`, a relatively
representable surjective étale morphism out of a represented algebraic space.

The first step is geometric:
`AlgebraicGeometry.Space.QuasiCoherentDescent.exists_represented_fpqc_refinement` turns the given
covering into an fpqc covering `(γ i)` of `R` by represented spaces, together with morphisms
`c i` to the members and commuting squares `γ i ≫ a = c i ≫ f i`.  The squares are *not*
cartesian: the members are atlases of the fibre products, chosen independently.

The second step transports the given family across those squares.  A morphism of the inverse
images along `f i`, restricted along `c i` and read through the comparison of Stacks 03LU, is a
morphism of the inverse images along `γ i` of the inverse images along `a`; the calculus of such
readings is `…factorForm`, `…restrictForm` and their composition law.  The transported family is
pairwise compatible, because a pair of morphisms
into two members over `R` has equal composites to `X` as well and the pairwise condition of the
original family can be read at an arbitrary such pair
(`…restrictForm_eq_of_isPairwiseCompatible`).  The represented case then descends it to a
morphism `ψ` of the inverse images along `a`.

The third step descends `ψ` along the atlas.  Descent of morphisms along a relatively
representable surjective étale morphism, `…exists_modulePullback_map_eq_of_dominated`, is
unconditional, and what it asks for — that `ψ` read the same along any two morphisms into `R`
with equal composites to `X` — follows from the pairwise condition of the original family after
pulling the two morphisms back along the fpqc covering `(γ i)` twice, once for each.  Finally
the inverse images of the resulting morphism of `𝒪_X`-modules are the given family, because they
agree after pullback along the fpqc base change of the atlas along each `f i`.

## Main definitions

* `AlgebraicGeometry.Space.QuasiCoherentDescent.factorForm` and `…restrictForm` are the two
  readings of a morphism of inverse images through the comparison of Stacks 03LU at a
  factorization.
* `AlgebraicGeometry.Space.QuasiCoherentDescent.ReprFpqcHomSurjective` is the fullness half of
  Stacks 023T, read on represented algebraic spaces and on quasi-coherent modules.  It is the one
  input of the reduction.

## Main results

* `AlgebraicGeometry.Space.QuasiCoherentDescent.restrictForm_eq_iff`: the pairwise condition of
  Stacks 04W3 at one pair of morphisms, in the two spellings.
* `AlgebraicGeometry.Space.QuasiCoherentDescent.pullbackComparison_trans`: **the comparison of
  Stacks 03LU at a two-step factorization**, which is the associativity coherence
  `AlgebraicGeometry.Space.modulePullbackCompIsoAssoc` written for factorizations.
* `AlgebraicGeometry.Space.QuasiCoherentDescent.factorForm_comp`,
  `…restrictForm_factorForm` and `…restrictForm_comp`: **the composition law of the readings** —
  reading along `p` and then along `m` is reading along `m ≫ p` in one step.
* `…canonicalComparison_naturality_of_isPairwiseCompatible` and
  `…restrictForm_eq_of_isPairwiseCompatible`: **the pairwise condition of Stacks 04W3, read
  at an arbitrary pair of morphisms with equal composites to `X`.**  The pairwise fibre product
  is a fibre product in the algebraic spaces, so such a pair factors through it.
* `AlgebraicGeometry.Space.QuasiCoherentDescent.exists_fpqc_leg_refinement` and
  `…exists_fpqc_pair_refinement`: an fpqc covering pulled back along one, respectively two,
  morphisms out of a test space, which is the base change of Stacks 03MR (3) and its
  composition clause.
* `AlgebraicGeometry.Space.QuasiCoherentDescent.eq_of_restrictForm_eq_of_isFpqcCovering`: a
  morphism of modules is determined by its restricted readings along an fpqc covering.
* `AlgebraicGeometry.Space.QuasiCoherentDescent.isPairwiseCompatible_of_square`,
  `…restrictForm_eq_of_comp_eq` and `…modulePullback_map_eq_of_square`: **the three facts about
  the family transported across the squares** — it is pairwise compatible over the new base, the
  morphism descending it reads the same along two morphisms with equal composites to `X`, and
  the morphism of `𝒪_X`-modules descending *that* has the original family as its inverse images.
* `AlgebraicGeometry.Space.QuasiCoherentDescent.exists_modulePullback_map_eq_of_isFpqcCovering`:
  **a pairwise compatible family of morphisms of the inverse images of two quasi-coherent
  modules along an fpqc covering of algebraic spaces is the family of the inverse images of a
  morphism of those modules**, stated over the represented case.
* `AlgebraicGeometry.Space.QuasiCoherentDescent.full_canonicalDescentFunctor_of_isFpqcCovering`:
  **the fullness half of the full-faithfulness clause of Stacks 04W8**, over the represented
  case.

## Implementation notes

Composition in `Stacks.SheafOfModules` is a projection of a structure instance, so asking the
kernel for a delta-iota step underneath a `≫` at these types does not finish.  Every unfolding
below is therefore performed by a rewrite with an explicit equation —
`AlgebraicGeometry.Space.QuasiCoherentDescent.factorForm_eq` and `…restrictForm_eq`, whose two
sides are the same term — and never by a conversion, and the two rearrangements of composites
that the composition law needs are stated in an arbitrary category
(`AlgebraicGeometry.Space.QuasiCoherentDescent.comp_conj_regroup`, and
`CategoryTheory.Functor.map_comp` itself) and applied here by instantiation only.

For the same reason a canonical comparison of Stacks 04W5 is never compared with another one
underneath a `≫`: the two proofs of its commuting square are interchangeable by proof
irrelevance, but to see that under `Iso.hom` the kernel first unfolds the comparison, which does
not finish.  The comparison is therefore rewritten in the goal by an equation *ascribed* at the
application itself, where proof irrelevance applies at once.

The step consuming the atlas,
`AlgebraicGeometry.Space.QuasiCoherentDescent.exists_modulePullback_map_eq_of_square`, is stated
with the atlas and the squares as variables: assembled in one term at the atlas that
`IsAlgebraicSpace.exists_atlas` produces, the same proof exhausts the elaborator's heartbeats.

The module universe is the universe of the structure rings, because
`AlgebraicGeometry.Space.modulePullback` exists only there.

## References

* [Stacks Project, Tag 04W8](https://stacks.math.columbia.edu/tag/04W8)
* [Stacks Project, Tag 04W6](https://stacks.math.columbia.edu/tag/04W6)
* [Stacks Project, Tag 04W5](https://stacks.math.columbia.edu/tag/04W5)
* [Stacks Project, Tag 04W3](https://stacks.math.columbia.edu/tag/04W3)
* [Stacks Project, Tag 023T](https://stacks.math.columbia.edu/tag/023T)
* [Stacks Project, Tag 03MQ](https://stacks.math.columbia.edu/tag/03MQ)
* [Stacks Project, Tag 03MR](https://stacks.math.columbia.edu/tag/03MR)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03G9](https://stacks.math.columbia.edu/tag/03G9)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 0419](https://stacks.math.columbia.edu/tag/0419)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry.Space.QuasiCoherentDescent

/- Instance search for pullbacks of presheaves on `BigFppfOver B S hS` times out under Lean
v4.35.0; supply the functor-category instance. -/
local instance (priority := high) {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
  functorCategoryHasLimitsOfShape

local instance (priority := high) {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {Y Z W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : Y ⟶ W) (g : Z ⟶ W) : HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit (cospan f g)

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### One step taken in an arbitrary category

The composition law of the readings below has to rearrange composites of morphisms of modules.
The step is stated for an arbitrary category and applied at the modules on an algebraic space by
instantiation only. -/

/-- Regrouping a morphism conjugated by two composites: the outer factors join the inner ones. -/
theorem comp_conj_regroup {C : Type*} [Category C] {T X Y Z V W : C} (a : T ⟶ X) (x : X ⟶ Y)
    (y : Y ⟶ Z) (z : Z ⟶ V) (d : V ⟶ W) :
    a ≫ (x ≫ y ≫ z) ≫ d = (a ≫ x) ≫ y ≫ (z ≫ d) := by
  simp only [Category.assoc]

section Forms

variable {A P P' Q R Z : AlgebraicSpaces B S hS} {M N : Modules.{u, u} B S hS A.1 A.2}

/-- A morphism of the iterated inverse images along a factorization `p ≫ k = r`, read through
the comparison of Stacks 03LU as a morphism of the inverse images along `r`.

The factorization is an explicit argument `r` together with the equation `hr`, rather than the
composite `p ≫ k` itself, so that the statements below compose with no transport. -/
def factorForm (p : P ⟶ Q) (k : Q ⟶ A) (r : P ⟶ A) (hr : p ≫ k = r)
    (u : (modulePullback B S hS p).obj ((modulePullback B S hS k).obj M) ⟶
      (modulePullback B S hS p).obj ((modulePullback B S hS k).obj N)) :
    (modulePullback B S hS r).obj M ⟶ (modulePullback B S hS r).obj N :=
  (pullbackComparison B S hS p k r hr M).hom ≫ u ≫
    (pullbackComparison B S hS p k r hr N).inv

/-- Reading a morphism through the comparison of Stacks 03LU is injective: it conjugates by two
isomorphisms. -/
theorem factorForm_injective (p : P ⟶ Q) (k : Q ⟶ A) (r : P ⟶ A) (hr : p ≫ k = r) :
    Function.Injective (factorForm B S hS p k r hr (M := M) (N := N)) := by
  intro u u' h
  have := congrArg (fun z => (pullbackComparison B S hS p k r hr M).inv ≫ z ≫
    (pullbackComparison B S hS p k r hr N).hom) h
  simpa only [factorForm, Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id,
    Category.comp_id] using this

/-- Every morphism of the inverse images along `r` is read off a morphism of the iterated
inverse images along a factorization of `r`. -/
theorem exists_factorForm_eq (p : P ⟶ Q) (k : Q ⟶ A) (r : P ⟶ A) (hr : p ≫ k = r)
    (v : (modulePullback B S hS r).obj M ⟶ (modulePullback B S hS r).obj N) :
    ∃ u, factorForm B S hS p k r hr u = v :=
  ⟨(pullbackComparison B S hS p k r hr M).inv ≫ v ≫
      (pullbackComparison B S hS p k r hr N).hom, by
    simp only [factorForm, Category.assoc, Iso.hom_inv_id, Category.comp_id,
      Iso.hom_inv_id_assoc]⟩

/-- A morphism of the inverse images along `k : Q ⟶ A`, restricted along `p : P ⟶ Q` and read
through the comparison of Stacks 03LU as a morphism of the inverse images along a factorization
`p ≫ k = r`. -/
def restrictForm (p : P ⟶ Q) (k : Q ⟶ A) (r : P ⟶ A) (hr : p ≫ k = r)
    (w : (modulePullback B S hS k).obj M ⟶ (modulePullback B S hS k).obj N) :
    (modulePullback B S hS r).obj M ⟶ (modulePullback B S hS r).obj N :=
  factorForm B S hS p k r hr ((modulePullback B S hS p).map w)

/-- The restricted reading of an inverse image of a morphism of modules is its inverse image
along the factorization. -/
theorem restrictForm_map (p : P ⟶ Q) (k : Q ⟶ A) (r : P ⟶ A) (hr : p ≫ k = r) (φ : M ⟶ N) :
    restrictForm B S hS p k r hr ((modulePullback B S hS k).map φ) =
      (modulePullback B S hS r).map φ := by
  simp only [restrictForm, factorForm]
  rw [← Category.assoc, ← pullbackComparison_naturality B S hS p k r hr φ, Category.assoc,
    Iso.hom_inv_id, Category.comp_id]

/-- The comparison of Stacks 03LU at a factorization `p ≫ k = r`, written through the
transport along that equation and the comparison at the composite itself. -/
theorem pullbackComparison_eq_eqToIso_trans (p : P ⟶ Q) (k : Q ⟶ A) (r : P ⟶ A)
    (hr : p ≫ k = r) (M : Modules.{u, u} B S hS A.1 A.2) :
    pullbackComparison B S hS p k r hr M =
      eqToIso (congrArg (fun z : P ⟶ A => (modulePullback B S hS z).obj M) hr.symm) ≪≫
        ((modulePullbackCompIso B S hS p k).app M).symm := by
  subst hr
  rw [pullbackComparison_rfl]
  exact (Iso.refl_trans _).symm

/-- **The canonical comparison of Stacks 04W5 is the comparison of two factorizations of one
morphism.**  At a common factorization `r` of `p ≫ k` and of `q ≫ l`, the canonical comparison
of the two inverse images of a module along `p` and `q` is the comparison of Stacks 03LU for `p`,
inverted, followed by the one for `q`. -/
theorem canonicalComparison_eq_pullbackComparison (p : P ⟶ Q) (q : P ⟶ R) (k : Q ⟶ A)
    (l : R ⟶ A) (h : p ≫ k = q ≫ l) (r : P ⟶ A) (hp : p ≫ k = r) (hq : q ≫ l = r)
    (M : Modules.{u, u} B S hS A.1 A.2) :
    canonicalComparison p q k l h M =
      (pullbackComparison B S hS p k r hp M).symm ≪≫
        pullbackComparison B S hS q l r hq M := by
  subst hp
  rw [canonicalComparison_eq, pullbackComparison_rfl, Iso.symm_symm_eq,
    pullbackComparison_eq_eqToIso_trans B S hS q l (p ≫ k) hq M]

/-- **The pairwise condition of Stacks 04W3 at one pair of morphisms, in the two spellings.**
Two morphisms of inverse images have equal restricted readings at a common factorization exactly
when they are intertwined by the canonical comparisons of Stacks 04W5.

The restricted readings are morphisms of the inverse images along *one* morphism `r`, so they
can be compared with no transport; that is what makes the left-hand spelling composable. -/
theorem restrictForm_eq_iff (p : P ⟶ Q) (q : P ⟶ R) (k : Q ⟶ A) (l : R ⟶ A) (r : P ⟶ A)
    (hp : p ≫ k = r) (hq : q ≫ l = r)
    (wk : (modulePullback B S hS k).obj M ⟶ (modulePullback B S hS k).obj N)
    (wl : (modulePullback B S hS l).obj M ⟶ (modulePullback B S hS l).obj N) :
    restrictForm B S hS p k r hp wk = restrictForm B S hS q l r hq wl ↔
      (modulePullback B S hS p).map wk ≫
          (canonicalComparison p q k l (hp.trans hq.symm) N).hom =
        (canonicalComparison p q k l (hp.trans hq.symm) M).hom ≫
          (modulePullback B S hS q).map wl := by
  rw [canonicalComparison_eq_pullbackComparison B S hS p q k l (hp.trans hq.symm) r hp hq M,
    canonicalComparison_eq_pullbackComparison B S hS p q k l (hp.trans hq.symm) r hp hq N]
  simp only [restrictForm, factorForm, Iso.trans_hom, Iso.symm_hom, Category.assoc]
  constructor
  · intro hh
    have := congrArg (fun z => (pullbackComparison B S hS p k r hp M).inv ≫ z ≫
      (pullbackComparison B S hS q l r hq N).hom) hh
    simpa only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id,
      Iso.hom_inv_id_assoc] using this
  · intro hh
    have := congrArg (fun z => (pullbackComparison B S hS p k r hp M).hom ≫ z ≫
      (pullbackComparison B S hS q l r hq N).inv) hh
    simpa only [Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id, Category.comp_id,
      Iso.inv_hom_id_assoc] using this

/-- **The pairwise condition of Stacks 04W3 at one pair of morphisms, from the equality of the
restricted readings, with the commuting square supplied.**

The square is an explicit argument rather than the one `…restrictForm_eq_iff` produces: two
proofs of it are interchangeable, and the equation that says so is ascribed at the comparison
itself, where proof irrelevance applies at once, never underneath a `≫`. -/
theorem canonicalComparison_naturality_of_restrictForm_eq (p : P ⟶ Q) (q : P ⟶ R) (k : Q ⟶ A)
    (l : R ⟶ A) (r : P ⟶ A) (hp : p ≫ k = r) (hq : q ≫ l = r) (h : p ≫ k = q ≫ l)
    (wk : (modulePullback B S hS k).obj M ⟶ (modulePullback B S hS k).obj N)
    (wl : (modulePullback B S hS l).obj M ⟶ (modulePullback B S hS l).obj N)
    (hww : restrictForm B S hS p k r hp wk = restrictForm B S hS q l r hq wl) :
    (modulePullback B S hS p).map wk ≫ (canonicalComparison p q k l h N).hom =
      (canonicalComparison p q k l h M).hom ≫ (modulePullback B S hS q).map wl := by
  have e : ∀ M' : Modules.{u, u} B S hS A.1 A.2,
      canonicalComparison p q k l h M' =
        canonicalComparison p q k l (hp.trans hq.symm) M' := fun _ => rfl
  rw [e M, e N]
  exact (restrictForm_eq_iff B S hS p q k l r hp hq wk wl).1 hww

/-- The reading of a morphism of the iterated inverse images through the comparison of
Stacks 03LU, written out.  The two sides are the same term; the equation exists so that the
unfolding can be performed by a rewrite, never by a conversion underneath a `≫`. -/
theorem factorForm_eq (p : P ⟶ Q) (k : Q ⟶ A) (r : P ⟶ A) (hr : p ≫ k = r)
    (u : (modulePullback B S hS p).obj ((modulePullback B S hS k).obj M) ⟶
      (modulePullback B S hS p).obj ((modulePullback B S hS k).obj N)) :
    factorForm B S hS p k r hr u =
      (pullbackComparison B S hS p k r hr M).hom ≫ u ≫
        (pullbackComparison B S hS p k r hr N).inv :=
  rfl

/-- The restricted reading is the reading of the inverse image, written out. -/
theorem restrictForm_eq (p : P ⟶ Q) (k : Q ⟶ A) (r : P ⟶ A) (hr : p ≫ k = r)
    (w : (modulePullback B S hS k).obj M ⟶ (modulePullback B S hS k).obj N) :
    restrictForm B S hS p k r hr w =
      factorForm B S hS p k r hr ((modulePullback B S hS p).map w) :=
  rfl

/-- **The comparison of Stacks 03LU at a two-step factorization.**  Comparing the inverse image
along `t` first with the one along `r` and then with the iterated one along `p`, is the same as
comparing it first with the one along `s` and then with the iterated one along `m`.

This is the associativity coherence of the comparison,
`AlgebraicGeometry.Space.modulePullbackCompIsoAssoc`, written for the factorizations rather than
for the composites. -/
theorem pullbackComparison_trans (m : P' ⟶ P) (p : P ⟶ Q) (k : Q ⟶ A) (r : P ⟶ A)
    (hr : p ≫ k = r) (s : P' ⟶ Q) (hs : m ≫ p = s) (t : P' ⟶ A) (ht : m ≫ r = t)
    (hst : s ≫ k = t) (M' : Modules.{u, u} B S hS A.1 A.2) :
    pullbackComparison B S hS m r t ht M' ≪≫
        (modulePullback B S hS m).mapIso (pullbackComparison B S hS p k r hr M') =
      pullbackComparison B S hS s k t hst M' ≪≫
        pullbackComparison B S hS m p s hs ((modulePullback B S hS k).obj M') := by
  subst hr
  subst hs
  subst ht
  rw [pullbackComparison_rfl, pullbackComparison_rfl, pullbackComparison_rfl,
    pullbackComparison]
  refine Iso.ext ?_
  simp only [Iso.trans_hom, Iso.symm_hom, Iso.app_inv, eqToIso.inv, eqToHom_refl,
    Category.id_comp]
  exact ModulePullbackCompIsoAssoc.inv_app (modulePullbackCompIsoAssoc B S hS) m p k M'

/-- The comparison of Stacks 03LU at a two-step factorization, on the forward morphisms. -/
theorem pullbackComparison_trans_hom (m : P' ⟶ P) (p : P ⟶ Q) (k : Q ⟶ A) (r : P ⟶ A)
    (hr : p ≫ k = r) (s : P' ⟶ Q) (hs : m ≫ p = s) (t : P' ⟶ A) (ht : m ≫ r = t)
    (hst : s ≫ k = t) (M' : Modules.{u, u} B S hS A.1 A.2) :
    (pullbackComparison B S hS m r t ht M').hom ≫
        (modulePullback B S hS m).map (pullbackComparison B S hS p k r hr M').hom =
      (pullbackComparison B S hS s k t hst M').hom ≫
        (pullbackComparison B S hS m p s hs ((modulePullback B S hS k).obj M')).hom := by
  simpa only [Iso.trans_hom, Functor.mapIso_hom] using
    congrArg Iso.hom (pullbackComparison_trans B S hS m p k r hr s hs t ht hst M')

/-- The comparison of Stacks 03LU at a two-step factorization, on the inverse morphisms. -/
theorem pullbackComparison_trans_inv (m : P' ⟶ P) (p : P ⟶ Q) (k : Q ⟶ A) (r : P ⟶ A)
    (hr : p ≫ k = r) (s : P' ⟶ Q) (hs : m ≫ p = s) (t : P' ⟶ A) (ht : m ≫ r = t)
    (hst : s ≫ k = t) (M' : Modules.{u, u} B S hS A.1 A.2) :
    (modulePullback B S hS m).map (pullbackComparison B S hS p k r hr M').inv ≫
        (pullbackComparison B S hS m r t ht M').inv =
      (pullbackComparison B S hS m p s hs ((modulePullback B S hS k).obj M')).inv ≫
        (pullbackComparison B S hS s k t hst M').inv := by
  simpa only [Iso.trans_inv, Functor.mapIso_inv] using
    congrArg Iso.inv (pullbackComparison_trans B S hS m p k r hr s hs t ht hst M')

/-- The image under a functor of a threefold composite of comparisons of Stacks 03LU. -/
theorem map_factorForm_eq (m : P' ⟶ P) (p : P ⟶ Q) (k : Q ⟶ A) (r : P ⟶ A) (hr : p ≫ k = r)
    (u : (modulePullback B S hS p).obj ((modulePullback B S hS k).obj M) ⟶
      (modulePullback B S hS p).obj ((modulePullback B S hS k).obj N)) :
    (modulePullback B S hS m).map ((pullbackComparison B S hS p k r hr M).hom ≫ u ≫
        (pullbackComparison B S hS p k r hr N).inv) =
      (modulePullback B S hS m).map (pullbackComparison B S hS p k r hr M).hom ≫
        (modulePullback B S hS m).map u ≫
        (modulePullback B S hS m).map (pullbackComparison B S hS p k r hr N).inv :=
  ((modulePullback B S hS m).map_comp (pullbackComparison B S hS p k r hr M).hom
      (u ≫ (pullbackComparison B S hS p k r hr N).inv)).trans
    (congrArg (fun z => (modulePullback B S hS m).map
        (pullbackComparison B S hS p k r hr M).hom ≫ z)
      ((modulePullback B S hS m).map_comp u (pullbackComparison B S hS p k r hr N).inv))

/-- Reading a morphism of the iterated inverse images along `p ≫ k = r` through the comparison
of Stacks 03LU and then reading the result along a further `m`, written out. -/
theorem factorForm_comp_left (m : P' ⟶ P) (p : P ⟶ Q) (k : Q ⟶ A) (r : P ⟶ A)
    (hr : p ≫ k = r) (t : P' ⟶ A) (ht : m ≫ r = t)
    (u : (modulePullback B S hS p).obj ((modulePullback B S hS k).obj M) ⟶
      (modulePullback B S hS p).obj ((modulePullback B S hS k).obj N)) :
    factorForm B S hS m r t ht
        ((modulePullback B S hS m).map (factorForm B S hS p k r hr u)) =
      (pullbackComparison B S hS m r t ht M).hom ≫
        ((modulePullback B S hS m).map (pullbackComparison B S hS p k r hr M).hom ≫
          (modulePullback B S hS m).map u ≫
          (modulePullback B S hS m).map (pullbackComparison B S hS p k r hr N).inv) ≫
        (pullbackComparison B S hS m r t ht N).inv := by
  rw [factorForm_eq B S hS p k r hr u, map_factorForm_eq B S hS m p k r hr u,
    factorForm_eq B S hS m r t ht]

/-- Reading a morphism of the iterated inverse images along `m ≫ p = s` through the comparison
of Stacks 03LU and then along `s ≫ k = t`, written out. -/
theorem factorForm_comp_right (m : P' ⟶ P) (p : P ⟶ Q) (k : Q ⟶ A) (s : P' ⟶ Q)
    (hs : m ≫ p = s) (t : P' ⟶ A) (hst : s ≫ k = t)
    (u : (modulePullback B S hS p).obj ((modulePullback B S hS k).obj M) ⟶
      (modulePullback B S hS p).obj ((modulePullback B S hS k).obj N)) :
    factorForm B S hS s k t hst
        (factorForm B S hS m p s hs ((modulePullback B S hS m).map u)) =
      (pullbackComparison B S hS s k t hst M).hom ≫
        ((pullbackComparison B S hS m p s hs ((modulePullback B S hS k).obj M)).hom ≫
          (modulePullback B S hS m).map u ≫
          (pullbackComparison B S hS m p s hs ((modulePullback B S hS k).obj N)).inv) ≫
        (pullbackComparison B S hS s k t hst N).inv := by
  rw [factorForm_eq B S hS m p s hs ((modulePullback B S hS m).map u),
    factorForm_eq B S hS s k t hst]

/-- The two written-out readings agree: the comparisons join by the associativity coherence. -/
theorem factorForm_comp_mid (m : P' ⟶ P) (p : P ⟶ Q) (k : Q ⟶ A) (r : P ⟶ A) (hr : p ≫ k = r)
    (s : P' ⟶ Q) (hs : m ≫ p = s) (t : P' ⟶ A) (ht : m ≫ r = t) (hst : s ≫ k = t)
    (x : (modulePullback B S hS m).obj
        ((modulePullback B S hS p).obj ((modulePullback B S hS k).obj M)) ⟶
      (modulePullback B S hS m).obj
        ((modulePullback B S hS p).obj ((modulePullback B S hS k).obj N))) :
    (pullbackComparison B S hS m r t ht M).hom ≫
        ((modulePullback B S hS m).map (pullbackComparison B S hS p k r hr M).hom ≫ x ≫
          (modulePullback B S hS m).map (pullbackComparison B S hS p k r hr N).inv) ≫
        (pullbackComparison B S hS m r t ht N).inv =
      (pullbackComparison B S hS s k t hst M).hom ≫
        ((pullbackComparison B S hS m p s hs ((modulePullback B S hS k).obj M)).hom ≫ x ≫
          (pullbackComparison B S hS m p s hs ((modulePullback B S hS k).obj N)).inv) ≫
        (pullbackComparison B S hS s k t hst N).inv := by
  rw [comp_conj_regroup, comp_conj_regroup,
    pullbackComparison_trans_hom B S hS m p k r hr s hs t ht hst M,
    pullbackComparison_trans_inv B S hS m p k r hr s hs t ht hst N]

/-- **The reading of a reading.**  Reading a morphism of the iterated inverse images along
`p ≫ k = r` through the comparison of Stacks 03LU, and then reading the result along a further
`m`, is reading it along `m ≫ p = s` in one step. -/
theorem factorForm_comp (m : P' ⟶ P) (p : P ⟶ Q) (k : Q ⟶ A) (r : P ⟶ A) (hr : p ≫ k = r)
    (s : P' ⟶ Q) (hs : m ≫ p = s) (t : P' ⟶ A) (ht : m ≫ r = t) (hst : s ≫ k = t)
    (u : (modulePullback B S hS p).obj ((modulePullback B S hS k).obj M) ⟶
      (modulePullback B S hS p).obj ((modulePullback B S hS k).obj N)) :
    factorForm B S hS m r t ht
        ((modulePullback B S hS m).map (factorForm B S hS p k r hr u)) =
      factorForm B S hS s k t hst
        (factorForm B S hS m p s hs ((modulePullback B S hS m).map u)) :=
  ((factorForm_comp_left B S hS m p k r hr t ht u).trans
      (factorForm_comp_mid B S hS m p k r hr s hs t ht hst
        ((modulePullback B S hS m).map u))).trans
    (factorForm_comp_right B S hS m p k s hs t hst u).symm

/-- **The restricted reading of a reading through a factorization.**  Reading a morphism `u` of
the iterated inverse images along `p ≫ k = r` through the comparison of Stacks 03LU and
restricting along `m` is restricting `u` along `m` first. -/
theorem restrictForm_factorForm (m : P' ⟶ P) (p : P ⟶ Q) (k : Q ⟶ A) (r : P ⟶ A)
    (hr : p ≫ k = r) (s : P' ⟶ Q) (hs : m ≫ p = s) (t : P' ⟶ A) (ht : m ≫ r = t)
    (hst : s ≫ k = t)
    (u : (modulePullback B S hS p).obj ((modulePullback B S hS k).obj M) ⟶
      (modulePullback B S hS p).obj ((modulePullback B S hS k).obj N)) :
    restrictForm B S hS m r t ht (factorForm B S hS p k r hr u) =
      factorForm B S hS s k t hst (restrictForm B S hS m p s hs u) := by
  rw [restrictForm_eq B S hS m r t ht (factorForm B S hS p k r hr u),
    factorForm_comp B S hS m p k r hr s hs t ht hst u,
    ← restrictForm_eq B S hS m p s hs u]

/-- **The restricted reading of a restricted reading.**  A morphism of the inverse images along
`k` is read along `m ≫ p = s` in one step. -/
theorem restrictForm_comp (m : P' ⟶ P) (p : P ⟶ Q) (k : Q ⟶ A) (r : P ⟶ A) (hr : p ≫ k = r)
    (s : P' ⟶ Q) (hs : m ≫ p = s) (t : P' ⟶ A) (ht : m ≫ r = t) (hst : s ≫ k = t)
    (w : (modulePullback B S hS k).obj M ⟶ (modulePullback B S hS k).obj N) :
    restrictForm B S hS m r t ht (restrictForm B S hS p k r hr w) =
      restrictForm B S hS s k t hst w := by
  rw [restrictForm_eq B S hS p k r hr w,
    restrictForm_factorForm B S hS m p k r hr s hs t ht hst ((modulePullback B S hS p).map w),
    restrictForm_map B S hS m p s hs w, ← restrictForm_eq B S hS s k t hst w]

end Forms

/-! ### The pairwise condition at an arbitrary pair of morphisms -/

section Pairwise

variable {I : Type v} {X : AlgebraicSpaces B S hS}

/-- **The pairwise condition of Stacks 04W3, read at an arbitrary pair of morphisms with equal
composites to `X`.**

The pairwise fibre product `X i ×_X X j` is a fibre product in the algebraic spaces, so such a
pair of morphisms factors through it; `AlgebraicGeometry.Space.QuasiCoherentDescent.transitionOn`
read there is the canonical comparison of Stacks 04W5 at the pair, by
`…transitionOn_canonicalComparison`, and a pairwise compatible family commutes with it by
`…transitionOn_naturality_of_pairwise`. -/
theorem canonicalComparison_naturality_of_isPairwiseCompatible
    (Xi : I → AlgebraicSpaces B S hS) (f : ∀ i, Xi i ⟶ X)
    {M N : Modules.{u, u} B S hS X.1 X.2}
    (w : ∀ i, (modulePullback B S hS (f i)).obj M ⟶ (modulePullback B S hS (f i)).obj N)
    (hw : IsPairwiseCompatible B S hS Xi f w) {P : AlgebraicSpaces B S hS} (i j : I)
    (vi : P ⟶ Xi i) (vj : P ⟶ Xi j) (hv : vi ≫ f i = vj ≫ f j) :
    (modulePullback B S hS vi).map (w i) ≫
        (canonicalComparison vi vj (f i) (f j) hv N).hom =
      (canonicalComparison vi vj (f i) (f j) hv M).hom ≫
        (modulePullback B S hS vj).map (w j) := by
  have hpb := AlgebraicSpaces.isPullback_fiberProduct B S hS (f i) (f j)
  have hfst : hpb.lift vi vj hv ≫ pairFst B S hS Xi f i j = vi := hpb.lift_fst vi vj hv
  have hsnd : hpb.lift vi vj hv ≫ pairSnd B S hS Xi f i j = vj := hpb.lift_snd vi vj hv
  have e : ∀ M' : Modules.{u, u} B S hS X.1 X.2,
      canonicalComparison vi vj (f i) (f j) hv M' =
        transitionOn B S hS Xi f (fun t => (modulePullback B S hS (f t)).obj M')
          (fun s t => canonicalComparison (pairFst B S hS Xi f s t)
            (pairSnd B S hS Xi f s t) (f s) (f t) (pair_condition B S hS Xi f s t) M')
          i j (hpb.lift vi vj hv) vi vj hfst hsnd := fun M' =>
    (transitionOn_canonicalComparison B S hS Xi f M' i j
      (hpb.lift vi vj hv) vi vj hfst hsnd).symm
  rw [e M, e N]
  exact transitionOn_naturality_of_pairwise B S hS Xi f
    (fun t => (modulePullback B S hS (f t)).obj M)
    (fun t => (modulePullback B S hS (f t)).obj N)
    (fun s t => canonicalComparison (pairFst B S hS Xi f s t) (pairSnd B S hS Xi f s t)
      (f s) (f t) (pair_condition B S hS Xi f s t) M)
    (fun s t => canonicalComparison (pairFst B S hS Xi f s t) (pairSnd B S hS Xi f s t)
      (f s) (f t) (pair_condition B S hS Xi f s t) N)
    w hw i j (hpb.lift vi vj hv) vi vj hfst hsnd

/-- **The pairwise condition of Stacks 04W3 at an arbitrary pair of morphisms, as an equality of
restricted readings.**  The restricted readings are morphisms of the inverse images along *one*
morphism `ρ`, so the conclusion needs no transport. -/
theorem restrictForm_eq_of_isPairwiseCompatible (Xi : I → AlgebraicSpaces B S hS)
    (f : ∀ i, Xi i ⟶ X) {M N : Modules.{u, u} B S hS X.1 X.2}
    (w : ∀ i, (modulePullback B S hS (f i)).obj M ⟶ (modulePullback B S hS (f i)).obj N)
    (hw : IsPairwiseCompatible B S hS Xi f w) {P : AlgebraicSpaces B S hS} (i j : I)
    (vi : P ⟶ Xi i) (vj : P ⟶ Xi j) (ρ : P ⟶ X) (hi : vi ≫ f i = ρ) (hj : vj ≫ f j = ρ) :
    restrictForm B S hS vi (f i) ρ hi (w i) = restrictForm B S hS vj (f j) ρ hj (w j) :=
  (restrictForm_eq_iff B S hS vi vj (f i) (f j) ρ hi hj (w i) (w j)).2
    (canonicalComparison_naturality_of_isPairwiseCompatible B S hS Xi f w hw i j vi vj
      (hi.trans hj.symm))

/-! ### Base change of an fpqc covering along one and along two morphisms -/

/-- **An fpqc covering of `R`, pulled back along a morphism `b : P ⟶ R`, is an fpqc covering of
`P` whose members map compatibly to the members of the original family.**  This is the base
change of Stacks 03MR (3), with the first projections named. -/
theorem exists_fpqc_leg_refinement {R : AlgebraicSpaces B S hS}
    (Yi : I → AlgebraicSpaces B S hS) (γ : ∀ i, Yi i ⟶ R)
    (hγ : IsFpqcCovering B S hS fun i => (γ i).hom) {P : AlgebraicSpaces B S hS} (b : P ⟶ R) :
    ∃ (G : I → AlgebraicSpaces B S hS) (m : ∀ i, G i ⟶ P) (α : ∀ i, G i ⟶ Yi i),
      (∀ i, α i ≫ γ i = m i ≫ b) ∧ IsFpqcCovering B S hS fun i => (m i).hom :=
  ⟨fun i => AlgebraicSpaces.fiberProduct B S hS (γ i) b,
    fun i => ObjectProperty.homMk (pullback.snd (γ i).hom b.hom),
    fun i => ObjectProperty.homMk (pullback.fst (γ i).hom b.hom),
    fun _ => ObjectProperty.hom_ext _ pullback.condition,
    isFpqcCovering_pullback B S hS γ b hγ⟩

/-- **An fpqc covering of `R`, pulled back along two morphisms `b, b' : P ⟶ R` at once.**  The
members of the resulting fpqc covering of `P` map compatibly to a member of the original family
over `b` and to a member of it over `b'`.  Composing the two base changes is the composition
clause of Stacks 03MR. -/
theorem exists_fpqc_pair_refinement {R : AlgebraicSpaces B S hS}
    (Yi : I → AlgebraicSpaces B S hS) (γ : ∀ i, Yi i ⟶ R)
    (hγ : IsFpqcCovering B S hS fun i => (γ i).hom) {P : AlgebraicSpaces B S hS}
    (b b' : P ⟶ R) :
    ∃ (G : (Σ _ : I, I) → AlgebraicSpaces B S hS) (m : ∀ e, G e ⟶ P)
      (α : ∀ e : Σ _ : I, I, G e ⟶ Yi e.1) (β : ∀ e : Σ _ : I, I, G e ⟶ Yi e.2),
      (∀ e, α e ≫ γ e.1 = m e ≫ b) ∧ (∀ e, β e ≫ γ e.2 = m e ≫ b') ∧
        IsFpqcCovering B S hS fun e => (m e).hom := by
  classical
  obtain ⟨G₁, m₁, α₁, hα₁, hcov₁⟩ := exists_fpqc_leg_refinement B S hS Yi γ hγ b
  choose G₂ m₂ β₂ hβ₂ hcov₂ using
    fun i => exists_fpqc_leg_refinement B S hS Yi γ hγ (m₁ i ≫ b')
  refine ⟨fun e => G₂ e.1 e.2, fun e => m₂ e.1 e.2 ≫ m₁ e.1,
    fun e => m₂ e.1 e.2 ≫ α₁ e.1, fun e => β₂ e.1 e.2, fun e => ?_, fun e => ?_, ?_⟩
  · rw [Category.assoc, hα₁ e.1, ← Category.assoc]
  · rw [hβ₂ e.1 e.2, Category.assoc]
  · exact isFpqcCovering_comp B S hS (X := P.1) (Xi := fun i => (G₁ i).1)
      (Xij := fun e : Σ _ : I, I => (G₂ e.1 e.2).1) P.property
      (fun i => (G₁ i).property) (fun i k => (G₂ i k).property)
      (fun i => (m₁ i).hom) (fun i k => (m₂ i k).hom) hcov₁ hcov₂

/-- A morphism of modules on an algebraic space is determined by its restricted readings along
an fpqc covering of that space. -/
theorem eq_of_restrictForm_eq_of_isFpqcCovering {A P : AlgebraicSpaces B S hS}
    {M N : Modules.{u, u} B S hS A.1 A.2} (G : I → AlgebraicSpaces B S hS)
    (m : ∀ i, G i ⟶ P) (hm : IsFpqcCovering B S hS fun i => (m i).hom) (σ : P ⟶ A)
    (τ : ∀ i, G i ⟶ A) (hτ : ∀ i, m i ≫ σ = τ i)
    (u u' : (modulePullback B S hS σ).obj M ⟶ (modulePullback B S hS σ).obj N)
    (h : ∀ i, restrictForm B S hS (m i) σ (τ i) (hτ i) u =
      restrictForm B S hS (m i) σ (τ i) (hτ i) u') :
    u = u' :=
  modulePullback_map_injective_of_isFlat B S hS G m (fun i => hm.1 i)
    (isJointlySurjective_of_isFpqcCovering B S hS (fun i => (m i).hom) hm) u u' fun i =>
    factorForm_injective B S hS (m i) σ (τ i) (hτ i) (by
      rw [← restrictForm_eq B S hS (m i) σ (τ i) (hτ i) u,
        ← restrictForm_eq B S hS (m i) σ (τ i) (hτ i) u']
      exact h i)

end Pairwise

/-! ### The readings transported across a commuting square -/

/-- Composing a test morphism through the left of a commuting square gives the same composite as
going down the right of the square, once the left side agrees with the given composite. -/
private theorem comp_comp_eq_of_square {C : Type*} [Category C] {X R Y Z P : C} {a : R ⟶ X}
    {γ : Y ⟶ R} {c : Y ⟶ Z} {f : Z ⟶ X} (hsq : γ ≫ a = c ≫ f) {n : P ⟶ Y} {b : P ⟶ R}
    {τ : P ⟶ X} (hb : n ≫ γ = b) (hτ : b ≫ a = τ) : (n ≫ c) ≫ f = τ := by
  rw [Category.assoc, ← hsq, ← Category.assoc, hb, hτ]

section Square

variable {I : Type v} {X R : AlgebraicSpaces B S hS} (Xi Yi : I → AlgebraicSpaces B S hS)
  (f : ∀ i, Xi i ⟶ X) (a : R ⟶ X) (γ : ∀ i, Yi i ⟶ R) (c : ∀ i, Yi i ⟶ Xi i)
  (hsq : ∀ i, γ i ≫ a = c i ≫ f i) {M N : Modules.{u, u} B S hS X.1 X.2}
  (w : ∀ i, (modulePullback B S hS (f i)).obj M ⟶ (modulePullback B S hS (f i)).obj N)
  (u : ∀ i, (modulePullback B S hS (γ i)).obj ((modulePullback B S hS a).obj M) ⟶
    (modulePullback B S hS (γ i)).obj ((modulePullback B S hS a).obj N))
  (hu : ∀ i, factorForm B S hS (γ i) a (γ i ≫ a) rfl (u i) =
    restrictForm B S hS (c i) (f i) (γ i ≫ a) (hsq i).symm (w i))

include hsq hu in
/-- **The reading of `u i` across the square, restricted to a test space.**  Restricting `u i`
along `n` and reading the result through the comparison of Stacks 03LU for the factorization
`b ≫ a` is the restricted reading of `w i` along the other side of the square. -/
theorem factorForm_restrictForm_eq (i : I) {P : AlgebraicSpaces B S hS} (n : P ⟶ Yi i)
    (b : P ⟶ R) (hb : n ≫ γ i = b) (τ : P ⟶ X) (hτ : b ≫ a = τ) (s : P ⟶ Xi i)
    (hs : n ≫ c i = s) (hsτ : s ≫ f i = τ) :
    factorForm B S hS b a τ hτ (restrictForm B S hS n (γ i) b hb (u i)) =
      restrictForm B S hS s (f i) τ hsτ (w i) := by
  have ht : n ≫ (γ i ≫ a) = τ := by rw [← Category.assoc, hb, hτ]
  rw [← restrictForm_factorForm B S hS n (γ i) a (γ i ≫ a) rfl b hb τ ht hτ (u i), hu i,
    restrictForm_comp B S hS n (c i) (f i) (γ i ≫ a) (hsq i).symm s hs τ ht hsτ (w i)]

include hsq hu in
/-- **The transported family is pairwise compatible.**  A pair of morphisms into two members of
the family over `R` has equal composites to `X` as well, so the pairwise condition of the
original family applies to the two sides of the square. -/
theorem isPairwiseCompatible_of_square (hw : IsPairwiseCompatible B S hS Xi f w) :
    IsPairwiseCompatible B S hS Yi γ u := by
  intro i j
  have hpc := pair_condition B S hS Yi γ i j
  have h1 := comp_comp_eq_of_square (hsq i) (rfl : pairFst B S hS Yi γ i j ≫ γ i = _) rfl
  have h2 := comp_comp_eq_of_square (hsq j) hpc.symm (rfl : _ ≫ a = _)
  refine canonicalComparison_naturality_of_restrictForm_eq B S hS
    (pairFst B S hS Yi γ i j) (pairSnd B S hS Yi γ i j) (γ i) (γ j)
    (pairFst B S hS Yi γ i j ≫ γ i) rfl hpc.symm hpc (u i) (u j) ?_
  refine factorForm_injective B S hS (pairFst B S hS Yi γ i j ≫ γ i) a
    ((pairFst B S hS Yi γ i j ≫ γ i) ≫ a) rfl ?_
  rw [factorForm_restrictForm_eq B S hS Xi Yi f a γ c hsq w u hu i
      (pairFst B S hS Yi γ i j) (pairFst B S hS Yi γ i j ≫ γ i) rfl
      ((pairFst B S hS Yi γ i j ≫ γ i) ≫ a) rfl (pairFst B S hS Yi γ i j ≫ c i) rfl h1,
    factorForm_restrictForm_eq B S hS Xi Yi f a γ c hsq w u hu j
      (pairSnd B S hS Yi γ i j) (pairFst B S hS Yi γ i j ≫ γ i) hpc.symm
      ((pairFst B S hS Yi γ i j ≫ γ i) ≫ a) rfl (pairSnd B S hS Yi γ i j ≫ c j) rfl h2]
  exact restrictForm_eq_of_isPairwiseCompatible B S hS Xi f w hw i j _ _ _ h1 h2

variable (ψ : (modulePullback B S hS a).obj M ⟶ (modulePullback B S hS a).obj N)
  (hψ : ∀ i, (modulePullback B S hS (γ i)).map ψ = u i)

include hsq hu hψ in
/-- **The restricted reading of a descended morphism across the square.**  A morphism `ψ` of the
inverse images along `a` whose restrictions along the members of the family over `R` are the
`u i` has, at a test space factoring through a member, the restricted reading of `w i`. -/
theorem restrictForm_eq_of_modulePullback_map_eq (i : I) {P : AlgebraicSpaces B S hS}
    (n : P ⟶ Yi i) (b : P ⟶ R) (hb : n ≫ γ i = b) (τ : P ⟶ X) (hτ : b ≫ a = τ)
    (s : P ⟶ Xi i) (hs : n ≫ c i = s) (hsτ : s ≫ f i = τ) :
    restrictForm B S hS b a τ hτ ψ = restrictForm B S hS s (f i) τ hsτ (w i) := by
  rw [restrictForm_eq B S hS b a τ hτ ψ, ← restrictForm_map B S hS n (γ i) b hb ψ, hψ i,
    factorForm_restrictForm_eq B S hS Xi Yi f a γ c hsq w u hu i n b hb τ hτ s hs hsτ]

include hsq hu hψ in
/-- **The descended morphism reads the same along two morphisms with equal composites to `X`.**
The two morphisms are covered, in the fpqc topology of the test space, by morphisms factoring
through a member of the family over `R` on either side at once, and there the pairwise condition
of the original family applies. -/
theorem restrictForm_eq_of_comp_eq (hw : IsPairwiseCompatible B S hS Xi f w)
    (hγ : IsFpqcCovering B S hS fun i => (γ i).hom) {P : AlgebraicSpaces B S hS}
    (b b' : P ⟶ R) (σ : P ⟶ X) (hb : b ≫ a = σ) (hb' : b' ≫ a = σ) :
    restrictForm B S hS b a σ hb ψ = restrictForm B S hS b' a σ hb' ψ := by
  obtain ⟨G, m, α, β, hα, hβ, hcov⟩ := exists_fpqc_pair_refinement B S hS Yi γ hγ b b'
  refine eq_of_restrictForm_eq_of_isFpqcCovering B S hS G m hcov σ (fun e => m e ≫ σ)
    (fun _ => rfl) _ _ fun e => ?_
  have hA : (m e ≫ b) ≫ a = m e ≫ σ := by rw [Category.assoc, hb]
  have hA' : (m e ≫ b') ≫ a = m e ≫ σ := by rw [Category.assoc, hb']
  have h1 := comp_comp_eq_of_square (hsq e.1) (hα e) hA
  have h2 := comp_comp_eq_of_square (hsq e.2) (hβ e) hA'
  rw [restrictForm_comp B S hS (m e) b a σ hb (m e ≫ b) rfl (m e ≫ σ) rfl hA ψ,
    restrictForm_comp B S hS (m e) b' a σ hb' (m e ≫ b') rfl (m e ≫ σ) rfl hA' ψ,
    restrictForm_eq_of_modulePullback_map_eq B S hS Xi Yi f a γ c hsq w u hu ψ hψ e.1
      (α e) (m e ≫ b) (hα e) (m e ≫ σ) hA (α e ≫ c e.1) rfl h1,
    restrictForm_eq_of_modulePullback_map_eq B S hS Xi Yi f a γ c hsq w u hu ψ hψ e.2
      (β e) (m e ≫ b') (hβ e) (m e ≫ σ) hA' (β e ≫ c e.2) rfl h2]
  exact restrictForm_eq_of_isPairwiseCompatible B S hS Xi f w hw e.1 e.2 _ _ _ h1 h2

include hsq hu hψ in
/-- **The morphism of `𝒪_X`-modules descended along `a` has the given inverse images.**  Its
inverse image along `f i` and `w i` have equal restricted readings on an fpqc covering of the
fibre product `R ×_X X i`, so they agree. -/
theorem modulePullback_map_eq_of_square (hw : IsPairwiseCompatible B S hS Xi f w)
    (hγ : IsFpqcCovering B S hS fun i => (γ i).hom)
    (hacov : IsFpqcCovering B S hS fun _ : Unit => a.hom) (φ : M ⟶ N)
    (hφ : (modulePullback B S hS a).map φ = ψ) (i : I) :
    (modulePullback B S hS (f i)).map φ = w i := by
  have hpb : IsFpqcCovering B S hS
      fun _ : Unit => pullback.snd a.hom (f i).hom :=
    isFpqcCovering_pullback B S hS (fun _ : Unit => a) (f i) hacov
  refine eq_of_restrictForm_eq_of_isFpqcCovering B S hS
    (fun _ : Unit => AlgebraicSpaces.fiberProduct B S hS a (f i))
    (fun _ => ObjectProperty.homMk (pullback.snd a.hom (f i).hom)) hpb (f i)
    (fun _ => ObjectProperty.homMk (pullback.snd a.hom (f i).hom) ≫ f i) (fun _ => rfl) _ _
    fun _ => ?_
  rw [restrictForm_map B S hS
    (ObjectProperty.homMk (pullback.snd a.hom (f i).hom) :
      AlgebraicSpaces.fiberProduct B S hS a (f i) ⟶ Xi i) (f i) _ rfl φ]
  obtain ⟨G, n, δ, hδ, hcov⟩ := exists_fpqc_leg_refinement B S hS Yi γ hγ
    (ObjectProperty.homMk (pullback.fst a.hom (f i).hom) :
      AlgebraicSpaces.fiberProduct B S hS a (f i) ⟶ R)
  have hsqa : (ObjectProperty.homMk (pullback.fst a.hom (f i).hom) :
      AlgebraicSpaces.fiberProduct B S hS a (f i) ⟶ R) ≫ a =
        ObjectProperty.homMk (pullback.snd a.hom (f i).hom) ≫ f i :=
    ObjectProperty.hom_ext _ pullback.condition
  refine (eq_of_restrictForm_eq_of_isFpqcCovering B S hS G n hcov _
    (fun j => n j ≫ (ObjectProperty.homMk (pullback.snd a.hom (f i).hom) ≫ f i))
    (fun _ => rfl) _ _ fun j => ?_).symm
  have hA : (n j ≫ ObjectProperty.homMk (pullback.fst a.hom (f i).hom)) ≫ a =
      n j ≫ (ObjectProperty.homMk (pullback.snd a.hom (f i).hom) ≫ f i) := by
    rw [Category.assoc, hsqa]
  have h1 := comp_comp_eq_of_square (hsq j) (hδ j) hA
  have h2 : (n j ≫ ObjectProperty.homMk (pullback.snd a.hom (f i).hom)) ≫ f i =
      n j ≫ (ObjectProperty.homMk (pullback.snd a.hom (f i).hom) ≫ f i) :=
    Category.assoc _ _ _
  rw [restrictForm_map B S hS (n j) _ _ (rfl :
      n j ≫ (ObjectProperty.homMk (pullback.snd a.hom (f i).hom) ≫ f i) = _) φ,
    restrictForm_comp B S hS (n j)
      (ObjectProperty.homMk (pullback.snd a.hom (f i).hom) :
        AlgebraicSpaces.fiberProduct B S hS a (f i) ⟶ Xi i) (f i) _ rfl
      (n j ≫ ObjectProperty.homMk (pullback.snd a.hom (f i).hom)) rfl _ rfl h2 (w i),
    ← restrictForm_eq_of_isPairwiseCompatible B S hS Xi f w hw j i (δ j ≫ c j)
      (n j ≫ ObjectProperty.homMk (pullback.snd a.hom (f i).hom)) _ h1 h2,
    ← restrictForm_eq_of_modulePullback_map_eq B S hS Xi Yi f a γ c hsq w u hu ψ hψ j
      (δ j) (n j ≫ ObjectProperty.homMk (pullback.fst a.hom (f i).hom)) (hδ j) _ hA
      (δ j ≫ c j) rfl h1,
    ← hφ, restrictForm_map B S hS
      (n j ≫ ObjectProperty.homMk (pullback.fst a.hom (f i).hom)) a _ hA φ]

include hsq hu in
/-- **The reduction at a given atlas.**  If the morphism of the inverse images along `a` that
the square transports the family to descends along the members of the family over `R`, then the
family itself is the family of the inverse images of a morphism of `𝒪_X`-modules.

`a` is a relatively representable surjective étale morphism, so descent of morphisms along it,
`AlgebraicGeometry.Space.QuasiCoherentDescent.exists_modulePullback_map_eq_of_dominated`, is
unconditional; what it asks for — that the morphism read the same along any two morphisms into
`R` with equal composites to `X` — is `…restrictForm_eq_of_comp_eq`. -/
theorem exists_modulePullback_map_eq_of_square (hw : IsPairwiseCompatible B S hS Xi f w)
    (hγ : IsFpqcCovering B S hS fun i => (γ i).hom) (ha : IsEtale B S hS a.hom)
    (harep : yoneda.relativelyRepresentable a.hom)
    (hacov : IsEtaleCovering B S hS (fun _ : Unit => R.1) (fun _ => a.hom))
    (hdesc : ∃ ψ : (modulePullback B S hS a).obj M ⟶ (modulePullback B S hS a).obj N,
      ∀ i, (modulePullback B S hS (γ i)).map ψ = u i) :
    ∃ φ : M ⟶ N, ∀ i, (modulePullback B S hS (f i)).map φ = w i := by
  obtain ⟨ψ, hψ⟩ := hdesc
  obtain ⟨φ, hφ⟩ := exists_modulePullback_map_eq_of_dominated B S hS a ha harep hacov ψ
    fun P b b' hbb => canonicalComparison_naturality_of_restrictForm_eq B S hS b b' a a
      (b ≫ a) rfl hbb.symm hbb ψ ψ
      (restrictForm_eq_of_comp_eq B S hS Xi Yi f a γ c hsq w u hu ψ hψ hw hγ b b' (b ≫ a) rfl
        hbb.symm)
  exact ⟨φ, fun i => modulePullback_map_eq_of_square B S hS Xi Yi f a γ c hsq w u hu ψ hψ hw hγ
    (isFpqcCovering_of_isEtaleCovering B S hS (fun _ : Unit => R.1) (fun _ => a.hom) hacov)
    φ hφ i⟩

end Square

/-! ### The reduction to the represented base -/

section Reduction

/-- **The fullness half of Stacks 023T, read on represented algebraic spaces.**  A pairwise
compatible family of morphisms of the inverse images of two **quasi-coherent** `𝒪`-modules on
the algebraic space represented by an object `U` of the big fppf site, along an fpqc covering of
`U` by objects of the site, is the family of the inverse images of a morphism of those modules.

For the Zariski modules on a scheme this is the `moreover` clause of Stacks 023T; the statement
below is the same assertion for the `𝒪`-modules of Stacks 03LU on the small étale site, and
passing between the two is the equivalence clause of Descent, Proposition 03DX (2).

Quasi-coherence of the two modules is one of the hypotheses of Stacks 04W8 itself, which asserts
effectivity and full faithfulness for descent data on **quasi-coherent** sheaves: fullness is a
*sheaf* condition on the presheaf of morphisms, and every fpqc sheaf condition here is for
quasi-coherent modules.  At arbitrary modules there is nothing to reduce to: the one sheaf
condition on the presheaf of morphisms of arbitrary modules is Zariski, and the passage from the
small étale site to the Zariski site, Descent, Proposition 03DX (2), is an equivalence of the
*quasi-coherent* subcategories alone.  That is why this predicate carries quasi-coherence while
the faithfulness counterpart
`AlgebraicGeometry.Space.QuasiCoherentDescent.ReprFpqcHomInjective` does not, flatness together
with joint surjectivity giving that one arbitrary-module strength for free. -/
abbrev ReprFpqcHomSurjective : Prop :=
  ∀ {J : Type v} (U : BigFppfOver B S hS) (T : J → BigFppfOver B S hS) (g : ∀ j, T j ⟶ U),
    IsFpqcCovering B S hS (fun j => yoneda.map (g j)) →
    ∀ {M N : Modules.{u, u} B S hS (representedAlgebraicSpace B S hS U).1
        (representedAlgebraicSpace B S hS U).2},
      M.IsQuasicoherentOnSite → N.IsQuasicoherentOnSite →
      ∀ w : ∀ j, (modulePullback B S hS (reprSpaceMap B S hS (g j))).obj M ⟶
        (modulePullback B S hS (reprSpaceMap B S hS (g j))).obj N,
      IsPairwiseCompatible B S hS (fun j => representedAlgebraicSpace B S hS (T j))
        (fun j => reprSpaceMap B S hS (g j)) w →
      ∃ χ : M ⟶ N, ∀ j, (modulePullback B S hS (reprSpaceMap B S hS (g j))).map χ = w j

variable {I : Type v} {X : AlgebraicSpaces B S hS}

/-- **A pairwise compatible family of morphisms of the inverse images of two `𝒪_X`-modules along
an fpqc covering of algebraic spaces is the family of the inverse images of a morphism of those
modules** — the fullness half of Stacks 04W8, reduced to the represented-base case, which is
taken as an argument.

The reduction is: restrict to a scheme atlas `a` of `X`, where
`AlgebraicGeometry.Space.QuasiCoherentDescent.exists_represented_fpqc_refinement` turns the
given covering into an fpqc covering of the atlas by represented spaces together with a
commuting square to the original family.  The given family, read across those squares, is a
pairwise compatible family on the atlas, so the represented case descends it to a morphism `ψ`
of the inverse images along `a`; that morphism reads the same along any two morphisms into the
atlas with equal composites to `X`, so descent of morphisms along the atlas,
`…exists_modulePullback_map_eq_of_dominated`, descends it again to a morphism of `𝒪_X`-modules;
and its inverse images are the given family because they agree after pullback along the fpqc
base change of the atlas along each member.

The two modules are quasi-coherent, as the descent statement of Stacks 04W8 has them be.
Quasi-coherence survives the reduction, the inverse image along an arbitrary morphism of
algebraic spaces preserving it by Stacks 03GA. -/
theorem exists_modulePullback_map_eq_of_isFpqcCovering
    (hrepr : ReprFpqcHomSurjective.{u, v} B S hS) (Xi : I → AlgebraicSpaces B S hS)
    (f : ∀ i, Xi i ⟶ X) (hf : IsFpqcCovering B S hS fun i => (f i).hom)
    {M N : Modules.{u, u} B S hS X.1 X.2}
    (w : ∀ i, (modulePullback B S hS (f i)).obj M ⟶ (modulePullback B S hS (f i)).obj N)
    (hw : IsPairwiseCompatible B S hS Xi f w) (hM : M.IsQuasicoherentOnSite)
    (hN : N.IsQuasicoherentOnSite) :
    ∃ φ : M ⟶ N, ∀ i, (modulePullback B S hS (f i)).map φ = w i := by
  classical
  obtain ⟨U, a₀, hsurj, hetale⟩ := X.property.exists_atlas
  have hEtaleCovering : IsEtaleCovering B S hS
      (fun _ : Unit => (representedAlgebraicSpace B S hS U).1) (fun _ => a₀) := by
    refine ⟨X.property, fun _ => isAlgebraicSpace_yoneda B S hS U,
      fun _ => (isEtale_iff_presheaf_of_yoneda B S hS a₀).2 hetale, ?_⟩
    rw [Set.iUnion_const, Set.range_eq_univ]
    exact (surjective_iff_surjective_pointsMap B S hS X.1 X.2 U a₀).1 hsurj
  obtain ⟨T, g, c, hsq, hcov⟩ := exists_represented_fpqc_refinement B S hS Xi f hf U
    (ObjectProperty.homMk a₀ : representedAlgebraicSpace B S hS U ⟶ X)
  choose u hu using fun i => exists_factorForm_eq B S hS (reprSpaceMap B S hS (g i))
    (ObjectProperty.homMk a₀ : representedAlgebraicSpace B S hS U ⟶ X)
    (reprSpaceMap B S hS (g i) ≫ ObjectProperty.homMk a₀) rfl
    (restrictForm B S hS (c i) (f i) (reprSpaceMap B S hS (g i) ≫ ObjectProperty.homMk a₀)
      (hsq i).symm (w i))
  exact exists_modulePullback_map_eq_of_square B S hS Xi
    (fun i => representedAlgebraicSpace B S hS (T i)) f
    (ObjectProperty.homMk a₀ : representedAlgebraicSpace B S hS U ⟶ X)
    (fun i => reprSpaceMap B S hS (g i)) c hsq w u hu hw hcov (hEtaleCovering.etale ())
    (relativelyRepresentable_of_isAlgebraicSpace B S hS X.property a₀) hEtaleCovering
    (hrepr U T g hcov
      (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS
        (ObjectProperty.homMk a₀ : representedAlgebraicSpace B S hS U ⟶ X) M hM)
      (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS
        (ObjectProperty.homMk a₀ : representedAlgebraicSpace B S hS U ⟶ X) N hN)
      u (isPairwiseCompatible_of_square B S hS Xi
      (fun i => representedAlgebraicSpace B S hS (T i)) f
      (ObjectProperty.homMk a₀ : representedAlgebraicSpace B S hS U ⟶ X)
      (fun i => reprSpaceMap B S hS (g i)) c hsq w u hu hw))

variable (Xi : I → AlgebraicSpaces B S hS) (f : ∀ i, Xi i ⟶ X)

/-- **The fullness half of the full-faithfulness clause of Stacks 04W8**, reduced to the
represented-base case.  The canonical descent functor of Stacks 04W5, from the quasi-coherent
`𝒪_X`-modules of Stacks 03G9 to the descent data of Stacks 04W3 relative to an fpqc covering
`(f i : X i ⟶ X)` of algebraic spaces in the sense of Stacks 03MQ, is full.

The components of a morphism of canonical descent data satisfy the pairwise condition of Stacks
04W3 by definition, so this is
`AlgebraicGeometry.Space.QuasiCoherentDescent.exists_modulePullback_map_eq_of_isFpqcCovering`
with nothing further. -/
theorem full_canonicalDescentFunctor_of_isFpqcCovering
    (hrepr : ReprFpqcHomSurjective.{u, v} B S hS)
    (hf : IsFpqcCovering B S hS fun i => (f i).hom) :
    (canonicalDescentFunctor' B S hS Xi f).Full where
  map_surjective {M N} θ := by
    obtain ⟨φ, hφ⟩ := exists_modulePullback_map_eq_of_isFpqcCovering B S hS hrepr Xi f hf
      (fun i => θ.app i) (fun i j => θ.naturality i j) M.property N.property
    exact ⟨ObjectProperty.homMk φ, DescentDatum.Hom.ext fun i => hφ i⟩

end Reduction

end AlgebraicGeometry.Space.QuasiCoherentDescent

end
