module

public import StacksCore.CategoryTheory.FiberedInGroupoids
public import StacksFrontier.AlgebraicGeometry.Size.Basic
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf
public import StacksFrontier.CategoryTheory.FiberedCategory.ChoiceOfPullbacks

/-!
# Fibredness over all `S`-schemes versus fibredness over the big fppf site

A category fibred in groupoids over the big fppf site `(Sch/S)_{fppf}` presents itself over the
category of all `S`-schemes through the composite `p ⋙ Over.post B.inclusion`. This file shows
that composite is *never* fibred in groupoids over `Over S`, and admits no choice of pullbacks
there, as soon as it has a `k`-valued point.

The reason is a size bound. A big fppf site carries a cutoff cardinal, and every object of the
site has underlying scheme of size below that cutoff. Fibredness over the category of *all*
`S`-schemes would require a lift of every morphism `V ⟶ U` of `S`-schemes, including those whose
source is larger than the cutoff; a polynomial ring on `cutoff`-many variables over the residue
field supplies such a `V`.

## Main results

* `Deformation.Artin.contains_left_of_isFiberedInGroupoids_comp_post` — fibredness over `Over S`
  forces every `S`-scheme mapping to the image of a point to lie in the site.
* `Deformation.Artin.not_contains_specMvPolynomial_ord_cutoff` — a polynomial ring on
  `cutoff`-many variables has spectrum outside the site.
* `Deformation.Artin.not_isFiberedInGroupoids_comp_post` — the composite is not fibred in
  groupoids over `Over S`.
* `Deformation.Artin.not_nonempty_choiceOfPullbacks_comp_post` — the composite has no choice of
  pullbacks over `Over S`.

## Implementation notes

These are stated for the composite `p ⋙ Over.post B.inclusion`, which is the way the site-level
work of this directory presents a site-fibred category over `Over S`.

Both conclusions are negations, so they are the obstruction to transporting
`Deformation.Artin.changeOfFieldFunctor_isEquivalence` to the site by instantiating its
hypotheses: that theorem takes a `q : 𝒳 ⥤ Over S` together with `q.IsFiberedInGroupoids` and a
`q.ChoiceOfPullbacks`, and for a site-presented `𝒳` neither is inhabited. A theorem of the shape
"site hypotheses imply the change-of-field functor is an equivalence" obtained that way would
therefore be vacuous, which is why the restriction recorded on the `@[stacks 07WX]` attributes of
`StacksFrontier/Deformation/Artin/ChangeOfField.lean` and
`StacksFrontier/Deformation/Artin/ChangeOfField/Equivalence.lean` is not a deferred step but a
genuinely different hypothesis.

What these negations rule out is the transport, not the statement. Tag 07WX over the site is
proved in `StacksFrontier/Deformation/Artin/ChangeOfField/SiteRestriction.lean`, where the cartesian
arrows are taken inside the site from `p.IsFiberedInGroupoids` for `p : 𝒳 ⥤ BigFppfOver B S hS`,
and no lift of a morphism of `Over S` with source outside the site is ever asked for.

The witness is `MvPolynomial B.cutoff.ord.ToType k`: its cardinality is at least the cutoff
because the variables inject into it, and the sections of an affine scheme inject into its size.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Cardinal

universe u u₁ v₁

namespace Deformation.Artin

/-- An `S`-scheme equal to the image in `Over S` of an object of `𝒳` lies in the site. -/
private theorem contains_left_of_obj_eq
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {𝒳 : Type u₁} [Category.{v₁} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS) {y : 𝒳} {V : Over S}
    (h : (p ⋙ Over.post B.inclusion).obj y = V) : B.Contains V.left :=
  congrArg Over.left h ▸ (p.obj y).left.property

/-- Fibredness over the category of **all** `S`-schemes forces every object of `Over S`
admitting a morphism to the image of a point of `𝒳` to lie in the chosen site. -/
public theorem contains_left_of_isFiberedInGroupoids_comp_post
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {𝒳 : Type u₁} [Category.{v₁} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS)
    (hq : (p ⋙ Over.post B.inclusion).IsFiberedInGroupoids)
    (x₀ : 𝒳) (V : Over S) (f : V ⟶ (p ⋙ Over.post B.inclusion).obj x₀) :
    B.Contains V.left := by
  obtain ⟨y, φ, hφ⟩ := hq.exists_lift f x₀ rfl
  exact contains_left_of_obj_eq B S hS p (IsHomLift.domain_eq (p ⋙ Over.post B.inclusion) f φ)

/-- A polynomial ring on `cutoff`-many variables has spectrum outside the site: its variables
inject into it, so its cardinality is at least the cutoff, and the sections of an affine scheme
inject into its size. -/
public theorem not_contains_specMvPolynomial_ord_cutoff
    (B : BigFppfSite.{u}) (k : Type u) [Field k] :
    ¬ B.Contains (Spec (CommRingCat.of (MvPolynomial B.cutoff.ord.ToType k))) := by
  set ι := B.cutoff.ord.ToType with hι
  set R := MvPolynomial ι k
  have h1 : B.cutoff ≤ #R := by
    have : #ι ≤ #R := Cardinal.mk_le_of_injective (MvPolynomial.X_injective (R := k) (σ := ι))
    simpa only [hι, Cardinal.mk_ord_toType] using this
  have h2 : #Γ(Spec (CommRingCat.of R), ⊤) = #R :=
    Cardinal.mk_congr
      (Scheme.ΓSpecIso (CommRingCat.of R)).commRingCatIsoToRingEquiv.toEquiv
  have h3 : #Γ(Spec (CommRingCat.of R), ⊤) ≤ (Spec (CommRingCat.of R)).size :=
    Scheme.mk_sections_le_size _ ⟨⊤, AlgebraicGeometry.isAffineOpen_top _⟩
  exact not_lt_of_ge (h1.trans (h2.ge.trans h3))

/-- Every `k`-point of `S` receives a morphism in `Over S` from an `S`-scheme outside the site. -/
private theorem exists_over_hom_not_contains (B : BigFppfSite.{u}) {S : Scheme.{u}}
    (k : Type u) [Field k] (u : Spec (CommRingCat.of k) ⟶ S) :
    ∃ V : Over S, ¬ B.Contains V.left ∧ Nonempty (V ⟶ Over.mk u) :=
  ⟨Over.mk (Spec.map (CommRingCat.ofHom
      (algebraMap k (MvPolynomial B.cutoff.ord.ToType k))) ≫ u),
    not_contains_specMvPolynomial_ord_cutoff B k,
    ⟨Over.homMk (Spec.map (CommRingCat.ofHom (algebraMap k _))) rfl⟩⟩

/-- **The obstruction.** For a category fibred in groupoids over the big fppf site of `S` with a
`k`-valued point, the composite to `Over S` is never fibred in groupoids over `Over S`. So the
fibredness hypothesis of `Deformation.Artin.changeOfFieldFunctor_isEquivalence` is unsatisfiable
for a site-presented category. -/
public theorem not_isFiberedInGroupoids_comp_post
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {𝒳 : Type u₁} [Category.{v₁} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS)
    {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k] (iΛ : Spec (.of Λ) ⟶ S)
    (x₀ : 𝒳)
    (hx₀ : (p ⋙ Over.post B.inclusion).obj x₀ =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)) :
    ¬ (p ⋙ Over.post B.inclusion).IsFiberedInGroupoids := by
  intro hq
  obtain ⟨V, hV, ⟨f⟩⟩ := exists_over_hom_not_contains B k
    (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)
  exact hV (contains_left_of_isFiberedInGroupoids_comp_post B S hS p hq x₀ V
    (f ≫ eqToHom hx₀.symm))

/-- The same for the other datum: a site-presented category has no choice of pullbacks over the
category of all `S`-schemes. -/
public theorem not_nonempty_choiceOfPullbacks_comp_post
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {𝒳 : Type u₁} [Category.{v₁} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS)
    {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k] (iΛ : Spec (.of Λ) ⟶ S)
    (x₀ : 𝒳)
    (hx₀ : (p ⋙ Over.post B.inclusion).obj x₀ =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)) :
    ¬ Nonempty (p ⋙ Over.post B.inclusion).ChoiceOfPullbacks := by
  rintro ⟨c⟩
  obtain ⟨V, hV, ⟨f⟩⟩ := exists_over_hom_not_contains B k
    (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)
  exact hV (contains_left_of_obj_eq B S hS p
    (c.obj (f ≫ eqToHom hx₀.symm) ⟨x₀, rfl⟩).property)

end Deformation.Artin

end
