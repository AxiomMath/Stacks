module

public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.CategoryTheory.EssentiallySmall
public import Mathlib.CategoryTheory.InducedCategory
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChaoticSite.PointMorphism
public import StacksFrontier.Cotangent.PolynomialAlgebraSiteSmall
public import StacksFrontier.Cotangent.ThreefoldPolynomialSite
import StacksCore.Tactic.StacksAttribute

/-!
# The cardinality-restricted threefold site, and a small model of it

Let `A → B → C` be ring maps. The site `C_{C/B/A}` of Tag 08QT is the opposite of the category of
polynomial towers `(P → B, Q → C)` with `P` a polynomial algebra over `A` and `Q` a polynomial
algebra over `P`. The source writes its objects as `P = A[S]`, `Q = A[S ⨿ T]`, and restricts the
sets of variables by the footnote to the section on simplicial resolutions: *"It suffices to
consider sets of cardinality at most the cardinality of `B`."* That restriction is part of the
definition of the site, and it is what makes the site small enough for the criterion of Tag 08Q9
and for the derived lower shriek with coefficients in one universe, both of which need a small
index category.

`CommAlgCat.polynomialTowerSite` carries no such restriction: its objects involve objects of
`CommAlgCat.{u} A`, hence live in `Type (u + 1)`, and their iso classes are indexed by the
cardinals of `Type u`. So it is not even essentially small at `u`. This file implements the
footnote in both layers of the tower, at arbitrary cardinal bounds `κ` for the variables of `P`
over `A` and `μ` for the variables of `Q` over `P`:

* the full subcategory of the polynomial towers whose two layers of variables have cardinality at
  most `κ`, resp. `μ`;
* a *genuinely small* model of it — a category whose type of objects is a `Type u` — namely the
  towers `A[S] → B`, `A[S][T] → C` for `S` a subset of a representative of `κ` and `T` a subset of
  a representative of `μ`;
* the three functors `u₁`, `u₂`, `u₃` of Tag 08QT on the small model, the point morphism `π` and
  the identities `π = πᵢ ∘ gᵢ`, with coefficients in `Type u`.

## Main definitions

* `CommAlgCat.IsPolynomialTowerBelow`, `CommAlgCat.BoundedPolynomialTower` and
  `CommAlgCat.boundedPolynomialTowerSite`: the two bounds on a tower, the full subcategory of
  `CommAlgCat.TowerComma` they cut out, and the site it cuts out of
  `CommAlgCat.polynomialTowerSite`.
* `CommAlgCat.boundedPolynomialTowerIndex` and `CommAlgCat.boundedPolynomialTowerModel`: the
  `Type u` of pairs `((S, g), (T, h))`, and the tower `A[S] → B`, `A[S][T] → C` it names.
* `CommAlgCat.SmallBoundedPolynomialTower` and `CommAlgCat.smallBoundedPolynomialTowerSite`: the
  small model and its opposite, a `SmallCategory` whose objects live in `Type u`.
* `CommAlgCat.boundedPolynomialTowerι` and `CommAlgCat.boundedPolynomialTowerSiteι`: the
  inclusion of the restricted category into the unrestricted one.
* `CommAlgCat.boundedPolynomialTowerFirst`, `...Second`, `...Third` and
  `CommAlgCat.smallBoundedPolynomialTowerFirst`, `...Second`, `...Third`: the functors `u₁`, `u₂`,
  `u₃` on the restricted sites and on their small models.
* `CommAlgCat.smallBoundedPolynomialTowerFirstTopos`, `...SecondTopos`, `...ThirdTopos`: the three
  morphisms of topoi `g₁`, `g₂`, `g₃` of the small models.
* `CommAlgCat.smallBoundedPolynomialTowerProjection` and
  `CommAlgCat.smallBoundedPolynomialTowerFirstProjection`, `...SecondProjection`,
  `...ThirdProjection`: the projections `π`, `π₁`, `π₂`, `π₃` to the point.

## Main results

* `CommAlgCat.essSurj_smallBoundedPolynomialTowerι`: every polynomial tower bounded by `κ` and
  `μ` is isomorphic to one in the small model.
* `CommAlgCat.boundedPolynomialTowerEquiv`, `CommAlgCat.boundedPolynomialTowerSiteEquiv`,
  `CommAlgCat.essentiallySmall_boundedPolynomialTower` and
  `CommAlgCat.essentiallySmall_boundedPolynomialTowerSite`: the small model is equivalent to the
  restricted category, resp. to the restricted site, which are therefore essentially small at
  `u`.
* `CommAlgCat.fullyFaithfulSmallBoundedPolynomialTowerSiteToPolynomialTowerSite`: the comparison
  of the small model with the unrestricted site `C_{C/B/A}` is fully faithful.
* `CommAlgCat.isPolynomialAlgebraBelow_towerRightAlgebra`: `Q` is a polynomial algebra over `A`
  on at most `μ + κ` variables, since `A[ι][τ] = A[τ ⊕ ι]`; this is what makes `u₂` land in the
  restricted `C_{C/A}`.
* `CommAlgCat.isPolynomialAlgebraBelow_towerBaseChangeAlgebra`: `Q ⊗_P B` is a polynomial algebra
  over `B` on at most `μ` variables, since `P[τ] ⊗_P B = B[τ]`; this is what makes `u₃` land in
  the restricted `C_{C/B}`.
* `CommAlgCat.smallBoundedPolynomialTowerFirst_comp_ι`,
  `CommAlgCat.smallBoundedPolynomialTowerSecondCompι` and
  `CommAlgCat.smallBoundedPolynomialTowerThirdCompι`: the three squares identifying `uᵢ` on the
  small models with `uᵢ` on `C_{C/B/A}` through the comparisons.
* `CommAlgCat.smallBoundedPolynomialTowerFirstProjection_comp_inverseImage` and its two siblings,
  together with
  `CommAlgCat.smallBoundedPolynomialTowerFirstProjection_comp_pushforwardIso` and its two
  siblings: the identity `π = πᵢ ∘ gᵢ` for the small models.

## Implementation notes

**Why a small model and not merely essential smallness.** `CategoryTheory.SmallModel` would
produce a small category from essential smallness, but only through `Classical.choose`. The model
built here is explicit: its objects are the pairs `((S, g), (T, h))` with `S : Set κ.out`,
`g : S → B`, `T : Set μ.out` and `h : T → C`, a type that genuinely lives in `Type u`, and its
morphisms are *by construction* the morphisms of `CommAlgCat.BoundedPolynomialTower` between the
named objects, through `CategoryTheory.InducedCategory`. So the inclusion is fully faithful with
no proof obligation and the only thing to prove is essential surjectivity, which is the
mathematical content of the footnote in each of the two layers.

**The two stacked layers.** The first half of an index is an index of the small model of
`C_{B/A}`, and the tower it names has `A[S] → B` for its first component *on the nose*; so `u₁`
restricts to the small models with no transport, and the square for `u₁` holds by `rfl`. The
second layer is `Q = A[S][T]`, a polynomial algebra over the model's own `A[S]`, with the
inclusion of the constants for the map `P → Q` and the augmentation determined by `h` through
`MvPolynomial.aevalTower` — the tower condition `P → Q → C = P → B → C` then holds because
`aevalTower` restricts on the constants to the given map `A[S] → B → C`. For `u₂` and `u₃` the
value is only *isomorphic* to a model object (`A[S][T]` is not literally a polynomial algebra over
`A` on a subset of a representative of `μ + κ`, and `A[S][T] ⊗_{A[S]} B` is not literally
`B[T]`), so those two functors are transported into the small models along the quasi-inverse of
`CommAlgCat.boundedPolynomialSiteEquiv` and the corresponding squares are natural isomorphisms
rather than equalities.

**The bounds.** The bound on the second layer is kept by `u₃` and only the sum `μ + κ` bounds the
variables of `Q` over `A`, which is why `u₂` lands in the site restricted by `μ + κ` rather than
by `μ` or `κ`. As in the twofold case the bounds are left free: `κ = #B` does not contain the
standard resolution, and the bound a given resolution needs is recorded where the resolution is.

**The universe bookkeeping.** The small model has both objects and morphisms in `Type u`, which
is what `SmallCategory` means and what the criterion of Tag 08Q9 and the derived lower shriek with
coefficients ask for. Accordingly the morphisms of topoi here are formed on sheaves of sets valued
in `Type u`, not in `Type (u + 1)` as for the large site of Tag 08QT, and `π` is
`Stacks.ChaoticSite.pointMorphism` rather than the projection of a ringed point — no ring is
carried on the point, so no universe lift intervenes.

## References

* [Stacks Project, Tag 08QT](https://stacks.math.columbia.edu/tag/08QT)
* [Stacks Project, Section 08QR](https://stacks.math.columbia.edu/tag/08QR)
* [Stacks Project, Tag 08PR](https://stacks.math.columbia.edu/tag/08PR)
* [Stacks Project, Tag 08Q9](https://stacks.math.columbia.edu/tag/08Q9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace CommAlgCat

variable (A : Type u) [CommRing A] (B : Type u) [CommRing B] [Algebra A B]
  (C : Type u) [CommRing C] [Algebra A C] [Algebra B C] [IsScalarTower A B C]
  (κ μ : Cardinal.{u})

/-! ### The cardinality-restricted site -/

/-- The conditions on a tower `(P → B, Q → C, P → Q)` that make it a polynomial tower with
boundedly many variables in each layer: `P` is a polynomial algebra over `A` on at most `κ`
variables, `Q` is a polynomial algebra over `P` on at most `μ` variables, and the composite
`P → Q → C` agrees with `P → B → C`. -/
abbrev IsPolynomialTowerBelow : ObjectProperty (TowerComma A B C) := fun X =>
  IsPolynomialAlgebraBelow A κ (towerLeftAlgebra X) ∧
    IsPolynomialAlgebraBelow ↑(towerLeftAlgebra X) μ
        (CommAlgCat.of ↑(towerLeftAlgebra X) ↑(towerRightAlgebra X)) ∧
      X.hom ≫ X.right.hom = X.left.obj.hom ≫ towerBaseToTotal A B C

/-- A polynomial tower with boundedly many variables in each layer is a polynomial tower. -/
lemma isPolynomialTowerBelow_le_isPolynomialTower :
    IsPolynomialTowerBelow A B C κ μ ≤ IsPolynomialTower A B C :=
  fun _ h => ⟨h.2.1.isPolynomialAlgebra, h.2.2⟩

/-- The category of polynomial towers `(P → B, Q → C)` in which `P` has at most `κ` variables
over `A` and `Q` at most `μ` variables over `P`: the category underlying the site `C_{C/B/A}` as
the source defines it, with the section's footnote in force in both layers. -/
abbrev BoundedPolynomialTower := (IsPolynomialTowerBelow A B C κ μ).FullSubcategory

/-- **Stacks 08QT** with the footnote's restriction. The site `C_{C/B/A}` cut down to the towers
whose two polynomial layers have at most `κ`, resp. `μ`, variables: the opposite of
`CommAlgCat.BoundedPolynomialTower`. `CommAlgCat.polynomialTowerSite` is the same construction
with the footnote omitted. -/
@[stacks 08QT "the site C_{C/B/A} with the section's footnote in force, restricting the two \
  layers of variables to cardinality at most κ, resp. μ. The unrestricted version is \
  `CommAlgCat.polynomialTowerSite`; only this one is essentially small"]
abbrev boundedPolynomialTowerSite := (BoundedPolynomialTower A B C κ μ)ᵒᵖ

/-- The inclusion of the restricted category of polynomial towers into the unrestricted one. -/
abbrev boundedPolynomialTowerι :
    BoundedPolynomialTower A B C κ μ ⥤ PolynomialTower A B C :=
  ObjectProperty.ιOfLE (isPolynomialTowerBelow_le_isPolynomialTower A B C κ μ)

/-- The inclusion of the restricted site into the unrestricted site
`CommAlgCat.polynomialTowerSite`. -/
abbrev boundedPolynomialTowerSiteι :
    boundedPolynomialTowerSite A B C κ μ ⥤ polynomialTowerSite A B C :=
  (boundedPolynomialTowerι A B C κ μ).op

/-! ### The small model -/

/-- The index type of the small model of the restricted category of polynomial towers: an index
`(S, g)` of the small model of `C_{B/A}`, together with a subset `T` of a fixed `Type u`
representative of `μ` and the images in `C` of the variables indexed by `T`. -/
abbrev boundedPolynomialTowerIndex : Type u :=
  boundedPolynomialIndex A (towerBaseAlgebra A B) κ × Σ T : Set μ.out, (T → C)

/-- The first half `(A[S] → B)` of the tower named by an index, as an object of the unrestricted
category of polynomial augmentations. -/
abbrev boundedPolynomialTowerModelLeft (i : boundedPolynomialTowerIndex A B C κ μ) :
    PolynomialAugmentation A (towerBaseAlgebra A B) :=
  (boundedPolynomialAugmentationι A (towerBaseAlgebra A B) κ).obj
    (boundedPolynomialModel A (towerBaseAlgebra A B) κ i.1)

/-- The augmentation `A[S][T] → C` of the tower named by an index `((S, g), (T, h))`: the
`A`-algebra map sending the variable `X_t` to `h t` and restricting on `A[S]` to
`A[S] → B → C`, which is the map through which `A[S]` acts on `C`. -/
def boundedPolynomialTowerModelAugmentation (i : boundedPolynomialTowerIndex A B C κ μ) :
    MvPolynomial i.2.1 (MvPolynomial i.1.1 A) →ₐ[A] C :=
  MvPolynomial.aevalTower
    ((IsScalarTower.toAlgHom A B C).comp (MvPolynomial.aeval fun s : i.1.1 => (i.1.2 s : B)))
    fun t : i.2.1 => i.2.2 t

/-- On the constants `A[S] ⊆ A[S][T]` the augmentation of the tower named by an index is the
composite `A[S] → B → C` of the augmentation `g` with the given map `B → C`. -/
@[simp]
theorem boundedPolynomialTowerModelAugmentation_C (i : boundedPolynomialTowerIndex A B C κ μ)
    (p : MvPolynomial i.1.1 A) :
    boundedPolynomialTowerModelAugmentation A B C κ μ i (MvPolynomial.C p) =
      algebraMap B C (MvPolynomial.aeval (fun s : i.1.1 => (i.1.2 s : B)) p) :=
  MvPolynomial.aevalTower_C _ _ p

/-- On the variables of the second layer the augmentation of the tower named by an index
`((S, g), (T, h))` is `h`. -/
@[simp]
theorem boundedPolynomialTowerModelAugmentation_X (i : boundedPolynomialTowerIndex A B C κ μ)
    (t : i.2.1) :
    boundedPolynomialTowerModelAugmentation A B C κ μ i (MvPolynomial.X t) = i.2.2 t :=
  MvPolynomial.aevalTower_X _ _ t

/-- The polynomial tower named by an index `((S, g), (T, h))`: the polynomial algebra `A[S]`
augmented to `B` by `g`, the polynomial algebra `A[S][T]` over it augmented to `C` by `h`, and
the inclusion `A[S] → A[S][T]` of the constants. Both layers of variables are subsets of
representatives of `κ`, resp. `μ`, so they are bounded by those cardinals. -/
def boundedPolynomialTowerModel (i : boundedPolynomialTowerIndex A B C κ μ) :
    BoundedPolynomialTower A B C κ μ where
  obj :=
    { left := boundedPolynomialTowerModelLeft A B C κ μ i
      right :=
        Over.mk (CommAlgCat.ofHom (boundedPolynomialTowerModelAugmentation A B C κ μ i))
      hom := CommAlgCat.ofHom (IsScalarTower.toAlgHom A (MvPolynomial i.1.1 A)
        (MvPolynomial i.2.1 (MvPolynomial i.1.1 A))) }
  property :=
    ⟨(boundedPolynomialModel A (towerBaseAlgebra A B) κ i.1).property,
      ⟨i.2.1, (Cardinal.mk_set_le i.2.1).trans_eq (Cardinal.mk_out μ),
        ⟨AlgEquiv.ofRingEquiv (f := RingEquiv.refl _) fun _ => rfl⟩⟩, by
      refine CommAlgCat.hom_ext (AlgHom.ext fun p => ?_)
      change boundedPolynomialTowerModelAugmentation A B C κ μ i
          (algebraMap (MvPolynomial i.1.1 A) _ p) =
        algebraMap B C (MvPolynomial.aeval (fun s : i.1.1 => (i.1.2 s : B)) p)
      rw [MvPolynomial.algebraMap_eq]
      exact boundedPolynomialTowerModelAugmentation_C A B C κ μ i p⟩

/-- The small model of the restricted category of polynomial towers: the category whose objects
are the indices of `CommAlgCat.boundedPolynomialTowerIndex` and whose morphisms are the morphisms
of `CommAlgCat.BoundedPolynomialTower` between the towers they name. Both its objects and its
morphisms live in `Type u`, so it is a `SmallCategory`. -/
abbrev SmallBoundedPolynomialTower : Type u :=
  InducedCategory (BoundedPolynomialTower A B C κ μ) (boundedPolynomialTowerModel A B C κ μ)

/-- The small model of the restricted site `C_{C/B/A}`: the opposite of
`CommAlgCat.SmallBoundedPolynomialTower`, a `SmallCategory` in `Type u`. -/
abbrev smallBoundedPolynomialTowerSite := (SmallBoundedPolynomialTower A B C κ μ)ᵒᵖ

/-- The fully faithful inclusion of the small model into the restricted category of polynomial
towers. -/
abbrev smallBoundedPolynomialTowerι :
    SmallBoundedPolynomialTower A B C κ μ ⥤ BoundedPolynomialTower A B C κ μ :=
  inducedFunctor (boundedPolynomialTowerModel A B C κ μ)

/-- The fully faithful inclusion of the small model of the restricted site into the restricted
site. -/
abbrev smallBoundedPolynomialTowerSiteι :
    smallBoundedPolynomialTowerSite A B C κ μ ⥤ boundedPolynomialTowerSite A B C κ μ :=
  (smallBoundedPolynomialTowerι A B C κ μ).op

/-- **The content of the footnote, for the threefold tower.** Every polynomial tower whose two
layers of variables have cardinality at most `κ`, resp. `μ`, is isomorphic to one of the small
model: each layer of variables embeds into a representative of its bound, so it may be replaced
by a subset of that representative, and the tower is transported along the renamings. -/
instance essSurj_smallBoundedPolynomialTowerι :
    (smallBoundedPolynomialTowerι A B C κ μ).EssSurj where
  mem_essImage X := by
    obtain ⟨j, ⟨eL⟩⟩ :=
      Functor.EssSurj.mem_essImage
        (F := smallBoundedPolynomialAugmentationι A (towerBaseAlgebra A B) κ)
        (⟨X.obj.left.obj, X.property.1⟩ : BoundedPolynomialAugmentation A
          (towerBaseAlgebra A B) κ)
    obtain ⟨τ, hτ, ⟨e₂⟩⟩ := X.property.2.1
    obtain ⟨f⟩ : Nonempty (τ ↪ μ.out) :=
      (Cardinal.le_def τ μ.out).mp (hτ.trans_eq (Cardinal.mk_out μ).symm)
    set σ : τ ≃ (Set.range f : Set μ.out) := Equiv.ofInjective f f.injective
    set eL' : (boundedPolynomialModel A (towerBaseAlgebra A B) κ j).obj ≅ X.obj.left.obj :=
      (IsPolynomialAlgebraOverBelow A (towerBaseAlgebra A B) κ).ι.mapIso eL
    set α : MvPolynomial j.1 A ≃ₐ[A] ↑(towerLeftAlgebra X.obj) :=
      CommAlgCat.algEquivOfIso ((Over.forget (towerBaseAlgebra A B)).mapIso eL')
    set β : MvPolynomial (Set.range f : Set μ.out) (MvPolynomial j.1 A) ≃ₐ[A]
        ↑(towerRightAlgebra X.obj) :=
      (MvPolynomial.mapAlgEquiv _ α).trans
        (AlgEquiv.restrictScalars A ((MvPolynomial.renameEquiv _ σ.symm).trans e₂)) with hβ
    have hmapC : ∀ p : MvPolynomial j.1 A,
        (MvPolynomial.mapAlgEquiv (Set.range f : Set μ.out) α) (MvPolynomial.C p) =
          MvPolynomial.C (α p) := fun p => by simp
    have hβC : ∀ p : MvPolynomial j.1 A,
        β (MvPolynomial.C p) = (CommAlgCat.Hom.hom X.obj.hom) (α p) := by
      intro p
      rw [hβ, AlgEquiv.trans_apply, hmapC, AlgEquiv.restrictScalars_apply,
        AlgEquiv.trans_apply, MvPolynomial.renameEquiv_apply, MvPolynomial.rename_C,
        ← MvPolynomial.algebraMap_eq, AlgEquiv.commutes]
      rfl
    have hβX : ∀ t : (Set.range f : Set μ.out),
        β (MvPolynomial.X t) = e₂ (MvPolynomial.X (σ.symm t)) := by
      intro t
      rw [hβ, AlgEquiv.trans_apply, AlgEquiv.restrictScalars_apply, AlgEquiv.trans_apply]
      simp [MvPolynomial.renameEquiv]
    have hαw : ∀ p : MvPolynomial j.1 A,
        (CommAlgCat.Hom.hom X.obj.left.obj.hom) (α p) =
          MvPolynomial.aeval (fun s : j.1 => (j.2 s : B)) p :=
      fun p => DFunLike.congr_fun (congrArg CommAlgCat.Hom.hom (Over.w eL'.hom)) p
    have hX₂ : ∀ q : ↑(towerLeftAlgebra X.obj),
        (CommAlgCat.Hom.hom X.obj.right.hom) ((CommAlgCat.Hom.hom X.obj.hom) q) =
          algebraMap B C ((CommAlgCat.Hom.hom X.obj.left.obj.hom) q) :=
      fun q => congrArg (fun k => (CommAlgCat.Hom.hom k) q) X.property.2.2
    refine ⟨(j, ⟨Set.range f, fun t =>
      (CommAlgCat.Hom.hom X.obj.right.hom) (e₂ (MvPolynomial.X (σ.symm t)))⟩),
      ⟨ObjectProperty.isoMk _ (Comma.isoMk (ObjectProperty.isoMk _ eL')
        (Over.isoMk (CommAlgCat.isoMk β) ?_) ?_)⟩⟩
    · refine CommAlgCat.hom_ext (MvPolynomial.algHom_ext' (AlgHom.ext fun p => ?_) fun t => ?_)
      · change (CommAlgCat.Hom.hom X.obj.right.hom) (β (MvPolynomial.C p)) = _
        rw [hβC, hX₂, hαw]
        exact (boundedPolynomialTowerModelAugmentation_C A B C κ μ _ p).symm
      · change (CommAlgCat.Hom.hom X.obj.right.hom) (β (MvPolynomial.X t)) = _
        rw [hβX]
        exact (boundedPolynomialTowerModelAugmentation_X A B C κ μ _ t).symm
    · exact CommAlgCat.hom_ext (AlgHom.ext fun p => (hβC p).symm)

/-- The inclusion of the small model into the restricted tower category is an equivalence. -/
instance isEquivalence_smallBoundedPolynomialTowerι :
    (smallBoundedPolynomialTowerι A B C κ μ).IsEquivalence where

/-- The small model is equivalent to the restricted category of polynomial towers. -/
def boundedPolynomialTowerEquiv :
    SmallBoundedPolynomialTower A B C κ μ ≌ BoundedPolynomialTower A B C κ μ :=
  (smallBoundedPolynomialTowerι A B C κ μ).asEquivalence

/-- The small model of the restricted site is equivalent to the restricted site. -/
def boundedPolynomialTowerSiteEquiv :
    smallBoundedPolynomialTowerSite A B C κ μ ≌ boundedPolynomialTowerSite A B C κ μ :=
  (boundedPolynomialTowerEquiv A B C κ μ).op

/-- **The restricted category of polynomial towers is essentially small at `u`.** This is what
the footnote buys, and what the unrestricted `CommAlgCat.PolynomialTower` does not satisfy. -/
instance essentiallySmall_boundedPolynomialTower :
    EssentiallySmall.{u} (BoundedPolynomialTower A B C κ μ) :=
  EssentiallySmall.mk' (boundedPolynomialTowerEquiv A B C κ μ).symm

/-- **The restricted site `C_{C/B/A}` is essentially small at `u`.** -/
instance essentiallySmall_boundedPolynomialTowerSite :
    EssentiallySmall.{u} (boundedPolynomialTowerSite A B C κ μ) :=
  EssentiallySmall.mk' (boundedPolynomialTowerSiteEquiv A B C κ μ).symm

/-- The fully faithful functor from the small model of the restricted site to the unrestricted
site `CommAlgCat.polynomialTowerSite`: the composite of the inclusion of the model into the
restricted site with the inclusion of the restricted site into the unrestricted one. -/
abbrev smallBoundedPolynomialTowerSiteToPolynomialTowerSite :
    smallBoundedPolynomialTowerSite A B C κ μ ⥤ polynomialTowerSite A B C :=
  smallBoundedPolynomialTowerSiteι A B C κ μ ⋙ boundedPolynomialTowerSiteι A B C κ μ

/-- `CommAlgCat.smallBoundedPolynomialTowerSiteToPolynomialTowerSite` is fully faithful, being a
composite of inclusions of full subcategories read in opposite categories. -/
def fullyFaithfulSmallBoundedPolynomialTowerSiteToPolynomialTowerSite :
    (smallBoundedPolynomialTowerSiteToPolynomialTowerSite A B C κ μ).FullyFaithful :=
  Functor.FullyFaithful.ofFullyFaithful _

/-! ### The three functors on the restricted site -/

/-- The `A`-algebra `Q` of a restricted polynomial tower is a polynomial algebra over `A` on at
most `μ + κ` variables: it is `A[ι][τ] = A[τ ⊕ ι]` with `#ι ≤ κ` and `#τ ≤ μ`. This is what
makes `u₂` land in the restricted site `C_{C/A}`. -/
@[stacks 08QT "u₂ lands in C_{C/A}, for the small model of the footnote-restricted tower site: \
  the bound on the two layers gives the bound μ + κ on the variables of Q over A"]
theorem isPolynomialAlgebraBelow_towerRightAlgebra (Y : BoundedPolynomialTower A B C κ μ) :
    IsPolynomialAlgebraBelow A (μ + κ) (towerRightAlgebra Y.obj) := by
  obtain ⟨ι, hι, ⟨e₁⟩⟩ := Y.property.1
  obtain ⟨τ, hτ, ⟨e₂⟩⟩ := Y.property.2.1
  refine ⟨τ ⊕ ι, ?_, ⟨?_⟩⟩
  · simpa [Cardinal.mk_sum] using add_le_add hτ hι
  · have hA : ∀ a : A,
        e₂ (algebraMap A (MvPolynomial τ ↑(towerLeftAlgebra Y.obj)) a) =
          algebraMap A ↑(towerRightAlgebra Y.obj) a := fun a => by
      rw [IsScalarTower.algebraMap_apply A ↑(towerLeftAlgebra Y.obj)
          (MvPolynomial τ ↑(towerLeftAlgebra Y.obj)) a, e₂.commutes,
        ← IsScalarTower.algebraMap_apply A ↑(towerLeftAlgebra Y.obj)
          ↑(towerRightAlgebra Y.obj) a]
    exact (MvPolynomial.sumAlgEquiv A τ ι).trans
      ((MvPolynomial.mapAlgEquiv τ e₁).trans (AlgEquiv.ofRingEquiv (f := e₂.toRingEquiv) hA))

/-- `Q ⊗_P B` is a polynomial algebra over `B` on at most `μ` variables: if `Q = P[τ]` then
`Q ⊗_P B = B[τ]`, with the same set of variables. This is what makes `u₃` land in the restricted
site `C_{C/B}`. -/
@[stacks 08QT "u₃ lands in C_{C/B}, for the small model of the footnote-restricted tower site: \
  the base change Q ⊗_P B has the same set of variables as Q over P, so the bound μ is kept"]
theorem isPolynomialAlgebraBelow_towerBaseChangeAlgebra (Y : BoundedPolynomialTower A B C κ μ) :
    IsPolynomialAlgebraBelow B μ (towerBaseChangeAlgebra Y.obj) := by
  obtain ⟨τ, hτ, ⟨e⟩⟩ := Y.property.2.1
  refine ⟨τ, hτ, ⟨?_⟩⟩
  have hf : Function.Bijective
      (Algebra.TensorProduct.map (S := B) (AlgHom.id B B) e.toAlgHom) :=
    Algebra.TensorProduct.map_bijective
      (f := (AlgHom.id B B).restrictScalars ↑(towerLeftAlgebra Y.obj)) (g := e.toAlgHom)
      Function.bijective_id e.bijective
  exact (MvPolynomial.scalarRTensorAlgEquiv
      (R := ↑(towerLeftAlgebra Y.obj)) (N := B) (σ := τ)).symm.trans
    (AlgEquiv.ofBijective (Algebra.TensorProduct.map (AlgHom.id B B) e.toAlgHom) hf)

/-- `u₁ : (P → B, Q → C) ↦ (P → B)` on the restricted categories, before passing to opposite
categories. -/
def boundedPolynomialTowerFirstAugmentations :
    BoundedPolynomialTower A B C κ μ ⥤
      BoundedPolynomialAugmentation A (towerBaseAlgebra A B) κ :=
  (IsPolynomialAlgebraOverBelow A (towerBaseAlgebra A B) κ).lift
    (boundedPolynomialTowerι A B C κ μ ⋙ polynomialTowerFirstAugmentations A B C ⋙
      (IsPolynomialAlgebraOver A (towerBaseAlgebra A B)).ι)
    fun Y => Y.property.1

/-- `u₂ : (P → B, Q → C) ↦ (Q → C)` on the restricted categories, before passing to opposite
categories. -/
def boundedPolynomialTowerSecondAugmentations :
    BoundedPolynomialTower A B C κ μ ⥤
      BoundedPolynomialAugmentation A (towerTotalAlgebra A C) (μ + κ) :=
  (IsPolynomialAlgebraOverBelow A (towerTotalAlgebra A C) (μ + κ)).lift
    (boundedPolynomialTowerι A B C κ μ ⋙ polynomialTowerSecondAugmentations A B C ⋙
      (IsPolynomialAlgebraOver A (towerTotalAlgebra A C)).ι)
    fun Y => isPolynomialAlgebraBelow_towerRightAlgebra A B C κ μ Y

/-- `u₃ : (P → B, Q → C) ↦ (Q ⊗_P B → C)` on the restricted categories, before passing to
opposite categories. -/
def boundedPolynomialTowerThirdAugmentations :
    BoundedPolynomialTower A B C κ μ ⥤
      BoundedPolynomialAugmentation B (towerRelativeAlgebra B C) μ :=
  (IsPolynomialAlgebraOverBelow B (towerRelativeAlgebra B C) μ).lift
    (boundedPolynomialTowerι A B C κ μ ⋙ polynomialTowerThirdAugmentations A B C ⋙
      (IsPolynomialAlgebraOver B (towerRelativeAlgebra B C)).ι)
    fun Y => isPolynomialAlgebraBelow_towerBaseChangeAlgebra A B C κ μ Y

/-- `u₁` on the restricted sites. -/
@[stacks 08QT "the functor u₁, for the footnote-restricted tower site"]
def boundedPolynomialTowerFirst :
    boundedPolynomialTowerSite A B C κ μ ⥤ boundedPolynomialSite A (towerBaseAlgebra A B) κ :=
  (boundedPolynomialTowerFirstAugmentations A B C κ μ).op

/-- `u₂` on the restricted sites. -/
@[stacks 08QT "the functor u₂, for the footnote-restricted tower site"]
def boundedPolynomialTowerSecond :
    boundedPolynomialTowerSite A B C κ μ ⥤
      boundedPolynomialSite A (towerTotalAlgebra A C) (μ + κ) :=
  (boundedPolynomialTowerSecondAugmentations A B C κ μ).op

/-- `u₃` on the restricted sites. -/
@[stacks 08QT "the functor u₃, for the footnote-restricted tower site"]
def boundedPolynomialTowerThird :
    boundedPolynomialTowerSite A B C κ μ ⥤ boundedPolynomialSite B (towerRelativeAlgebra B C) μ :=
  (boundedPolynomialTowerThirdAugmentations A B C κ μ).op

/-- Read in the unrestricted categories, `u₁` on the restricted categories is `u₁`: the
restriction only cuts down the ambient categories. -/
theorem boundedPolynomialTowerFirstAugmentations_comp_ι :
    boundedPolynomialTowerFirstAugmentations A B C κ μ ⋙
        boundedPolynomialAugmentationι A (towerBaseAlgebra A B) κ =
      boundedPolynomialTowerι A B C κ μ ⋙ polynomialTowerFirstAugmentations A B C := rfl

/-- Read in the unrestricted categories, `u₂` on the restricted categories is `u₂`. -/
theorem boundedPolynomialTowerSecondAugmentations_comp_ι :
    boundedPolynomialTowerSecondAugmentations A B C κ μ ⋙
        boundedPolynomialAugmentationι A (towerTotalAlgebra A C) (μ + κ) =
      boundedPolynomialTowerι A B C κ μ ⋙ polynomialTowerSecondAugmentations A B C := rfl

/-- Read in the unrestricted categories, `u₃` on the restricted categories is `u₃`. -/
theorem boundedPolynomialTowerThirdAugmentations_comp_ι :
    boundedPolynomialTowerThirdAugmentations A B C κ μ ⋙
        boundedPolynomialAugmentationι B (towerRelativeAlgebra B C) μ =
      boundedPolynomialTowerι A B C κ μ ⋙ polynomialTowerThirdAugmentations A B C := rfl

/-- Read in the unrestricted sites, `u₁` on the restricted sites is `u₁`. -/
@[stacks 08QT "the functor u₁ of the footnote-restricted tower site is u₁"]
theorem boundedPolynomialTowerFirst_comp_ι :
    boundedPolynomialTowerFirst A B C κ μ ⋙ boundedPolynomialSiteι A (towerBaseAlgebra A B) κ =
      boundedPolynomialTowerSiteι A B C κ μ ⋙ polynomialTowerFirst A B C := rfl

/-- Read in the unrestricted sites, `u₂` on the restricted sites is `u₂`. -/
@[stacks 08QT "the functor u₂ of the footnote-restricted tower site is u₂"]
theorem boundedPolynomialTowerSecond_comp_ι :
    boundedPolynomialTowerSecond A B C κ μ ⋙
        boundedPolynomialSiteι A (towerTotalAlgebra A C) (μ + κ) =
      boundedPolynomialTowerSiteι A B C κ μ ⋙ polynomialTowerSecond A B C := rfl

/-- Read in the unrestricted sites, `u₃` on the restricted sites is `u₃`. -/
@[stacks 08QT "the functor u₃ of the footnote-restricted tower site is u₃"]
theorem boundedPolynomialTowerThird_comp_ι :
    boundedPolynomialTowerThird A B C κ μ ⋙ boundedPolynomialSiteι B (towerRelativeAlgebra B C) μ =
      boundedPolynomialTowerSiteι A B C κ μ ⋙ polynomialTowerThird A B C := rfl

/-! ### The three functors on the small model -/

/-- `u₁` on the small models, `((S, g), (T, h)) ↦ (S, g)`: the first half of an index of the
small model of the tower site *is* an index of the small model of `C_{B/A}`, so `u₁` needs no
transport. -/
def smallBoundedPolynomialTowerFirstAugmentations :
    SmallBoundedPolynomialTower A B C κ μ ⥤
      SmallBoundedPolynomialAugmentation A (towerBaseAlgebra A B) κ where
  obj i := i.1
  map f := InducedCategory.homMk (ObjectProperty.homMk f.hom.hom.left.hom)
  map_id _ := rfl
  map_comp _ _ := rfl

/-- `u₁ : C_{C/B/A} ⥤ C_{B/A}` on the small models of the restricted sites. -/
@[stacks 08QT "the functor u₁, for the small model of the footnote-restricted tower site"]
def smallBoundedPolynomialTowerFirst :
    smallBoundedPolynomialTowerSite A B C κ μ ⥤
      smallBoundedPolynomialSite A (towerBaseAlgebra A B) κ :=
  (smallBoundedPolynomialTowerFirstAugmentations A B C κ μ).op

/-- `u₂ : C_{C/B/A} ⥤ C_{C/A}` on the small models of the restricted sites: `u₂` on the
restricted sites, followed by the transport of its value into the small model of `C_{C/A}`. -/
@[stacks 08QT "the functor u₂, for the small model of the footnote-restricted tower site"]
def smallBoundedPolynomialTowerSecond :
    smallBoundedPolynomialTowerSite A B C κ μ ⥤
      smallBoundedPolynomialSite A (towerTotalAlgebra A C) (μ + κ) :=
  smallBoundedPolynomialTowerSiteι A B C κ μ ⋙ boundedPolynomialTowerSecond A B C κ μ ⋙
    (boundedPolynomialSiteEquiv A (towerTotalAlgebra A C) (μ + κ)).inverse

/-- `u₃ : C_{C/B/A} ⥤ C_{C/B}` on the small models of the restricted sites: `u₃` on the
restricted sites, followed by the transport of its value into the small model of `C_{C/B}`. -/
@[stacks 08QT "the functor u₃, for the small model of the footnote-restricted tower site"]
def smallBoundedPolynomialTowerThird :
    smallBoundedPolynomialTowerSite A B C κ μ ⥤
      smallBoundedPolynomialSite B (towerRelativeAlgebra B C) μ :=
  smallBoundedPolynomialTowerSiteι A B C κ μ ⋙ boundedPolynomialTowerThird A B C κ μ ⋙
    (boundedPolynomialSiteEquiv B (towerRelativeAlgebra B C) μ).inverse

/-- **The square for `u₁`.** Read in the unrestricted sites through the fully faithful
comparisons, `u₁` on the small models is `u₁` on `C_{C/B/A}`. -/
@[stacks 08QT "the functor u₁ of the small model of the footnote-restricted tower site is u₁"]
theorem smallBoundedPolynomialTowerFirst_comp_ι :
    smallBoundedPolynomialTowerFirst A B C κ μ ⋙
        smallBoundedPolynomialSiteToPolynomialSite A (towerBaseAlgebra A B) κ =
      smallBoundedPolynomialTowerSiteToPolynomialTowerSite A B C κ μ ⋙
        polynomialTowerFirst A B C := rfl

/-- **The square for `u₂`.** Read in the unrestricted sites through the fully faithful
comparisons, `u₂` on the small models is `u₂` on `C_{C/B/A}`, up to the canonical isomorphism
coming from the transport into the small model of `C_{C/A}`. -/
@[stacks 08QT "the functor u₂ of the small model of the footnote-restricted tower site is u₂"]
def smallBoundedPolynomialTowerSecondCompι :
    smallBoundedPolynomialTowerSecond A B C κ μ ⋙
        smallBoundedPolynomialSiteToPolynomialSite A (towerTotalAlgebra A C) (μ + κ) ≅
      smallBoundedPolynomialTowerSiteToPolynomialTowerSite A B C κ μ ⋙
        polynomialTowerSecond A B C :=
  Functor.isoWhiskerLeft
    (smallBoundedPolynomialTowerSiteι A B C κ μ ⋙ boundedPolynomialTowerSecond A B C κ μ)
    (Functor.isoWhiskerRight
      (boundedPolynomialSiteEquiv A (towerTotalAlgebra A C) (μ + κ)).counitIso
      (boundedPolynomialSiteι A (towerTotalAlgebra A C) (μ + κ)))

/-- **The square for `u₃`.** Read in the unrestricted sites through the fully faithful
comparisons, `u₃` on the small models is `u₃` on `C_{C/B/A}`, up to the canonical isomorphism
coming from the transport into the small model of `C_{C/B}`. -/
@[stacks 08QT "the functor u₃ of the small model of the footnote-restricted tower site is u₃"]
def smallBoundedPolynomialTowerThirdCompι :
    smallBoundedPolynomialTowerThird A B C κ μ ⋙
        smallBoundedPolynomialSiteToPolynomialSite B (towerRelativeAlgebra B C) μ ≅
      smallBoundedPolynomialTowerSiteToPolynomialTowerSite A B C κ μ ⋙
        polynomialTowerThird A B C :=
  Functor.isoWhiskerLeft
    (smallBoundedPolynomialTowerSiteι A B C κ μ ⋙ boundedPolynomialTowerThird A B C κ μ)
    (Functor.isoWhiskerRight (boundedPolynomialSiteEquiv B (towerRelativeAlgebra B C) μ).counitIso
      (boundedPolynomialSiteι B (towerRelativeAlgebra B C) μ))

/-! ### The chaotic topology, the point, and the three morphisms of topoi -/

/-- The topology of the small model of the restricted site `C_{C/B/A}` is the chaotic topology:
its only coverings are the maximal sieves, so every presheaf on it is a sheaf. -/
@[stacks 08QT "the chaotic topology on C_{C/B/A}, for the small model of the \
  footnote-restricted tower site"]
theorem smallBoundedPolynomialTowerTopology_eq_bot :
    GrothendieckTopology.trivial (smallBoundedPolynomialTowerSite A B C κ μ) = ⊥ :=
  GrothendieckTopology.trivial_eq_bot

/-- For the chaotic topologies, `u₁` on the small models is continuous. -/
instance smallBoundedPolynomialTowerFirst_isContinuous :
    (smallBoundedPolynomialTowerFirst A B C κ μ).IsContinuous
      (GrothendieckTopology.trivial (smallBoundedPolynomialTowerSite A B C κ μ))
      (GrothendieckTopology.trivial (smallBoundedPolynomialSite A (towerBaseAlgebra A B) κ)) :=
  Stacks.ChaoticSite.isContinuous_of_eq_bot _ _ _ GrothendieckTopology.trivial_eq_bot

/-- For the chaotic topologies, `u₁` on the small models is cocontinuous. -/
instance smallBoundedPolynomialTowerFirst_isCocontinuous :
    (smallBoundedPolynomialTowerFirst A B C κ μ).IsCocontinuous
      (GrothendieckTopology.trivial (smallBoundedPolynomialTowerSite A B C κ μ))
      (GrothendieckTopology.trivial (smallBoundedPolynomialSite A (towerBaseAlgebra A B) κ)) :=
  Stacks.ChaoticSite.isCocontinuous_of_eq_bot _ _ _ GrothendieckTopology.trivial_eq_bot

/-- For the chaotic topologies, `u₂` on the small models is continuous. -/
instance smallBoundedPolynomialTowerSecond_isContinuous :
    (smallBoundedPolynomialTowerSecond A B C κ μ).IsContinuous
      (GrothendieckTopology.trivial (smallBoundedPolynomialTowerSite A B C κ μ))
      (GrothendieckTopology.trivial
        (smallBoundedPolynomialSite A (towerTotalAlgebra A C) (μ + κ))) :=
  Stacks.ChaoticSite.isContinuous_of_eq_bot _ _ _ GrothendieckTopology.trivial_eq_bot

/-- For the chaotic topologies, `u₂` on the small models is cocontinuous. -/
instance smallBoundedPolynomialTowerSecond_isCocontinuous :
    (smallBoundedPolynomialTowerSecond A B C κ μ).IsCocontinuous
      (GrothendieckTopology.trivial (smallBoundedPolynomialTowerSite A B C κ μ))
      (GrothendieckTopology.trivial
        (smallBoundedPolynomialSite A (towerTotalAlgebra A C) (μ + κ))) :=
  Stacks.ChaoticSite.isCocontinuous_of_eq_bot _ _ _ GrothendieckTopology.trivial_eq_bot

/-- For the chaotic topologies, `u₃` on the small models is continuous. -/
instance smallBoundedPolynomialTowerThird_isContinuous :
    (smallBoundedPolynomialTowerThird A B C κ μ).IsContinuous
      (GrothendieckTopology.trivial (smallBoundedPolynomialTowerSite A B C κ μ))
      (GrothendieckTopology.trivial (smallBoundedPolynomialSite B (towerRelativeAlgebra B C) μ)) :=
  Stacks.ChaoticSite.isContinuous_of_eq_bot _ _ _ GrothendieckTopology.trivial_eq_bot

/-- For the chaotic topologies, `u₃` on the small models is cocontinuous. -/
instance smallBoundedPolynomialTowerThird_isCocontinuous :
    (smallBoundedPolynomialTowerThird A B C κ μ).IsCocontinuous
      (GrothendieckTopology.trivial (smallBoundedPolynomialTowerSite A B C κ μ))
      (GrothendieckTopology.trivial (smallBoundedPolynomialSite B (towerRelativeAlgebra B C) μ)) :=
  Stacks.ChaoticSite.isCocontinuous_of_eq_bot _ _ _ GrothendieckTopology.trivial_eq_bot

/-- `g₁ : Sh(C_{C/B/A}) ⟶ Sh(C_{B/A})` for the small models, the morphism of topoi induced by
`u₁`. Its inverse image is restriction along `u₁`; the coefficients are in the site's own
universe. -/
def smallBoundedPolynomialTowerFirstTopos :
    MorphismOfTopoi
      (Sheaf (GrothendieckTopology.trivial (smallBoundedPolynomialTowerSite A B C κ μ)) (Type u))
      (Sheaf (GrothendieckTopology.trivial (smallBoundedPolynomialSite A (towerBaseAlgebra A B) κ))
        (Type u)) :=
  Functor.morphismOfTopoiOfCocontinuous.{u, u, u, u, u}
    (smallBoundedPolynomialTowerFirst A B C κ μ) _ _

/-- `g₂ : Sh(C_{C/B/A}) ⟶ Sh(C_{C/A})` for the small models. -/
def smallBoundedPolynomialTowerSecondTopos :
    MorphismOfTopoi
      (Sheaf (GrothendieckTopology.trivial (smallBoundedPolynomialTowerSite A B C κ μ)) (Type u))
      (Sheaf (GrothendieckTopology.trivial
        (smallBoundedPolynomialSite A (towerTotalAlgebra A C) (μ + κ))) (Type u)) :=
  Functor.morphismOfTopoiOfCocontinuous.{u, u, u, u, u}
    (smallBoundedPolynomialTowerSecond A B C κ μ) _ _

/-- `g₃ : Sh(C_{C/B/A}) ⟶ Sh(C_{C/B})` for the small models. -/
def smallBoundedPolynomialTowerThirdTopos :
    MorphismOfTopoi
      (Sheaf (GrothendieckTopology.trivial (smallBoundedPolynomialTowerSite A B C κ μ)) (Type u))
      (Sheaf (GrothendieckTopology.trivial
        (smallBoundedPolynomialSite B (towerRelativeAlgebra B C) μ)) (Type u)) :=
  Functor.morphismOfTopoiOfCocontinuous.{u, u, u, u, u}
    (smallBoundedPolynomialTowerThird A B C κ μ) _ _

/-- The inverse image of `g₁` is restriction along `u₁`. -/
theorem smallBoundedPolynomialTowerFirstTopos_inverseImage :
    (smallBoundedPolynomialTowerFirstTopos A B C κ μ).inverseImage =
      (smallBoundedPolynomialTowerFirst A B C κ μ).sheafPushforwardContinuous (Type u)
        (GrothendieckTopology.trivial (smallBoundedPolynomialTowerSite A B C κ μ))
        (GrothendieckTopology.trivial (smallBoundedPolynomialSite A (towerBaseAlgebra A B) κ)) :=
  rfl

/-- The inverse image of `g₂` is restriction along `u₂`. -/
theorem smallBoundedPolynomialTowerSecondTopos_inverseImage :
    (smallBoundedPolynomialTowerSecondTopos A B C κ μ).inverseImage =
      (smallBoundedPolynomialTowerSecond A B C κ μ).sheafPushforwardContinuous (Type u)
        (GrothendieckTopology.trivial (smallBoundedPolynomialTowerSite A B C κ μ))
        (GrothendieckTopology.trivial
          (smallBoundedPolynomialSite A (towerTotalAlgebra A C) (μ + κ))) :=
  rfl

/-- The inverse image of `g₃` is restriction along `u₃`. -/
theorem smallBoundedPolynomialTowerThirdTopos_inverseImage :
    (smallBoundedPolynomialTowerThirdTopos A B C κ μ).inverseImage =
      (smallBoundedPolynomialTowerThird A B C κ μ).sheafPushforwardContinuous (Type u)
        (GrothendieckTopology.trivial (smallBoundedPolynomialTowerSite A B C κ μ))
        (GrothendieckTopology.trivial
          (smallBoundedPolynomialSite B (towerRelativeAlgebra B C) μ)) :=
  rfl

/-- `π : Sh(C_{C/B/A}) ⟶ Sh(*)`, the projection of the small model of the restricted site to
the point, with coefficients in the site's own universe. -/
@[stacks 08QT "the projection π, for the small model of the footnote-restricted tower site"]
abbrev smallBoundedPolynomialTowerProjection :
    MorphismOfTopoi
      (Sheaf (GrothendieckTopology.trivial (smallBoundedPolynomialTowerSite A B C κ μ)) (Type u))
      (Sheaf (GrothendieckTopology.trivial (Discrete PUnit.{u + 1})) (Type u)) :=
  Stacks.ChaoticSite.pointMorphism.{u, u, u} (smallBoundedPolynomialTowerSite A B C κ μ)

/-- `π₁ : Sh(C_{B/A}) ⟶ Sh(*)` for the small model of the restricted site `C_{B/A}`. -/
abbrev smallBoundedPolynomialTowerFirstProjection :
    MorphismOfTopoi
      (Sheaf (GrothendieckTopology.trivial (smallBoundedPolynomialSite A (towerBaseAlgebra A B) κ))
        (Type u))
      (Sheaf (GrothendieckTopology.trivial (Discrete PUnit.{u + 1})) (Type u)) :=
  Stacks.ChaoticSite.pointMorphism.{u, u, u} (smallBoundedPolynomialSite A (towerBaseAlgebra A B) κ)

/-- `π₂ : Sh(C_{C/A}) ⟶ Sh(*)` for the small model of the restricted site `C_{C/A}`. -/
abbrev smallBoundedPolynomialTowerSecondProjection :
    MorphismOfTopoi
      (Sheaf (GrothendieckTopology.trivial
        (smallBoundedPolynomialSite A (towerTotalAlgebra A C) (μ + κ))) (Type u))
      (Sheaf (GrothendieckTopology.trivial (Discrete PUnit.{u + 1})) (Type u)) :=
  Stacks.ChaoticSite.pointMorphism.{u, u, u}
    (smallBoundedPolynomialSite A (towerTotalAlgebra A C) (μ + κ))

/-- `π₃ : Sh(C_{C/B}) ⟶ Sh(*)` for the small model of the restricted site `C_{C/B}`. -/
abbrev smallBoundedPolynomialTowerThirdProjection :
    MorphismOfTopoi
      (Sheaf (GrothendieckTopology.trivial
        (smallBoundedPolynomialSite B (towerRelativeAlgebra B C) μ)) (Type u))
      (Sheaf (GrothendieckTopology.trivial (Discrete PUnit.{u + 1})) (Type u)) :=
  Stacks.ChaoticSite.pointMorphism.{u, u, u}
    (smallBoundedPolynomialSite B (towerRelativeAlgebra B C) μ)

/-- `π = π₁ ∘ g₁` on inverse images: both are restriction along the unique functor to the
point, because `u₁` followed by `C_{B/A} ⥤ *` is `C_{C/B/A} ⥤ *`. -/
@[stacks 08QT "π = π₁ ∘ g₁ on inverse images, for the small model of the footnote-restricted \
  tower site"]
theorem smallBoundedPolynomialTowerFirstProjection_comp_inverseImage :
    ((smallBoundedPolynomialTowerFirstProjection A B κ).comp
        (smallBoundedPolynomialTowerFirstTopos A B C κ μ)).inverseImage =
      (smallBoundedPolynomialTowerProjection A B C κ μ).inverseImage := rfl

/-- `π = π₂ ∘ g₂` on inverse images. -/
@[stacks 08QT "π = π₂ ∘ g₂ on inverse images, for the small model of the footnote-restricted \
  tower site"]
theorem smallBoundedPolynomialTowerSecondProjection_comp_inverseImage :
    ((smallBoundedPolynomialTowerSecondProjection A C κ μ).comp
        (smallBoundedPolynomialTowerSecondTopos A B C κ μ)).inverseImage =
      (smallBoundedPolynomialTowerProjection A B C κ μ).inverseImage := rfl

/-- `π = π₃ ∘ g₃` on inverse images. -/
@[stacks 08QT "π = π₃ ∘ g₃ on inverse images, for the small model of the footnote-restricted \
  tower site"]
theorem smallBoundedPolynomialTowerThirdProjection_comp_inverseImage :
    ((smallBoundedPolynomialTowerThirdProjection B C μ).comp
        (smallBoundedPolynomialTowerThirdTopos A B C κ μ)).inverseImage =
      (smallBoundedPolynomialTowerProjection A B C κ μ).inverseImage := rfl

/-- `π = π₁ ∘ g₁` on direct images: the canonical isomorphism `(π₁ ∘ g₁)_* ≅ π_*` between the
two right adjoints of the common inverse image. -/
@[stacks 08QT "π = π₁ ∘ g₁ on direct images, for the small model of the footnote-restricted \
  tower site"]
def smallBoundedPolynomialTowerFirstProjection_comp_pushforwardIso :
    ((smallBoundedPolynomialTowerFirstProjection A B κ).comp
        (smallBoundedPolynomialTowerFirstTopos A B C κ μ)).pushforward ≅
      (smallBoundedPolynomialTowerProjection A B C κ μ).pushforward :=
  (((smallBoundedPolynomialTowerFirstProjection A B κ).comp
          (smallBoundedPolynomialTowerFirstTopos A B C κ μ)).adj.ofNatIsoLeft
      (eqToIso
        (smallBoundedPolynomialTowerFirstProjection_comp_inverseImage A B C κ μ))).rightAdjointUniq
    (smallBoundedPolynomialTowerProjection A B C κ μ).adj

/-- `π = π₂ ∘ g₂` on direct images. -/
@[stacks 08QT "π = π₂ ∘ g₂ on direct images, for the small model of the footnote-restricted \
  tower site"]
def smallBoundedPolynomialTowerSecondProjection_comp_pushforwardIso :
    ((smallBoundedPolynomialTowerSecondProjection A C κ μ).comp
        (smallBoundedPolynomialTowerSecondTopos A B C κ μ)).pushforward ≅
      (smallBoundedPolynomialTowerProjection A B C κ μ).pushforward :=
  (((smallBoundedPolynomialTowerSecondProjection A C κ μ).comp
          (smallBoundedPolynomialTowerSecondTopos A B C κ μ)).adj.ofNatIsoLeft
      (eqToIso
        (smallBoundedPolynomialTowerSecondProjection_comp_inverseImage A B C κ μ))).rightAdjointUniq
    (smallBoundedPolynomialTowerProjection A B C κ μ).adj

/-- `π = π₃ ∘ g₃` on direct images. -/
@[stacks 08QT "π = π₃ ∘ g₃ on direct images, for the small model of the footnote-restricted \
  tower site"]
def smallBoundedPolynomialTowerThirdProjection_comp_pushforwardIso :
    ((smallBoundedPolynomialTowerThirdProjection B C μ).comp
        (smallBoundedPolynomialTowerThirdTopos A B C κ μ)).pushforward ≅
      (smallBoundedPolynomialTowerProjection A B C κ μ).pushforward :=
  (((smallBoundedPolynomialTowerThirdProjection B C μ).comp
          (smallBoundedPolynomialTowerThirdTopos A B C κ μ)).adj.ofNatIsoLeft
      (eqToIso
        (smallBoundedPolynomialTowerThirdProjection_comp_inverseImage A B C κ μ))).rightAdjointUniq
    (smallBoundedPolynomialTowerProjection A B C κ μ).adj

end CommAlgCat

end
