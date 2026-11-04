module

public import Mathlib.AlgebraicGeometry.Birational.RationalMap
public import StacksFrontier.AlgebraicGeometry.F6Rank89.CoheightOfSurface
public import StacksFrontier.AlgebraicGeometry.Morphisms.Valuative.Extension
public import StacksFrontier.AlgebraicGeometry.Properties.RegularCharacterization
public import StacksFrontier.RingTheory.DiscreteValuationRing.TFAE

/-!
# Extending a rational map to a regular surface past its codimension-one indeterminacy

Let `X` be a regular Noetherian scheme of dimension two over `S` and let `Y` be proper over `S`.
A rational map `X ⇢ Y` over `S` extends to an open subscheme whose complement contains only
points whose local ring has Krull dimension two — that is, the indeterminacy locus can always be
shrunk to a finite set of closed points.

The mechanism is the valuative extension criterion
`AlgebraicGeometry.exists_open_extension_of_valuationRing_stalk`: at a point whose local ring is
a discrete valuation ring, a morphism from a dense open subscheme over `S` extends across that
point when the target is proper. On a regular scheme a local ring of Krull dimension one is
exactly a discrete valuation ring, so every codimension-one point of the indeterminacy locus can
be absorbed, one at a time.

## Main results

* `AlgebraicGeometry.Scheme.PartialMap.exists_extension_of_finset_ringKrullDim_eq_one`: a partial
  map over `S` extends across any finite set of points whose local rings are regular of dimension
  one.
* `AlgebraicGeometry.Scheme.PartialMap.exists_extension_codimension_two`: on a regular Noetherian
  scheme of dimension two, a partial map over `S` extends to a domain whose complement consists of
  points of local dimension two.

## Implementation notes

The first statement is proved by induction on the finite set, carrying the "is over `S`" equation
as an explicit hypothesis rather than as the instance `Scheme.PartialMap.IsOver`: the induction
replaces the partial map at every step, so an instance on the original map is of no use, and
`AlgebraicGeometry.Scheme.PartialMap.isOver_iff` converts in both directions at the two places
where the valuative criterion needs the instance form.

The regularity hypothesis enters only as *every local ring is a regular local ring*, which is the
second clause of `AlgebraicGeometry.isRegular_tfae`; the dimension hypothesis enters only through
`AlgebraicGeometry.coheight_eq_one_or_two_of_notMem_dense`. So the first lemma takes the pointwise
form directly, and the second extracts it once.

In the second statement the indeterminacy locus is decomposed into finitely many irreducible
closed sets by Noetherianity, and the generic points of those of coheight one — a finite set — are
the ones fed to the first lemma. A point of the remaining locus either specializes strictly from a
generic point of coheight one, which forces its own coheight to two, or equals a generic point of
coheight two by `AlgebraicGeometry.eq_genericPoint_of_coheight_two`.
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.PartialMap

/-- A partial map over `S` into a scheme proper over `S` extends across every point of a finite
set whose local rings are regular local rings of Krull dimension one. -/
theorem exists_extension_of_finset_ringKrullDim_eq_one {S X Y : Scheme.{u}} [X.Over S] [Y.Over S]
    [IsNoetherian X] [IsProper (Y ↘ S)] (f : X.PartialMap Y)
    (hfbase : f.hom ≫ (Y ↘ S) = f.domain.ι ≫ (X ↘ S))
    (hregular : ∀ x : X, IsRegularLocalRing (X.presheaf.stalk x)) (F : Finset X)
    (hFdim : ∀ x ∈ F, ringKrullDim (X.presheaf.stalk x) = 1) :
    ∃ g : X.PartialMap Y, ∃ hfg : f.domain ≤ g.domain,
      g.hom ≫ (Y ↘ S) = g.domain.ι ≫ (X ↘ S) ∧
      X.homOfLE hfg ≫ g.hom = f.hom ∧ ∀ x ∈ F, x ∈ g.domain := by
  classical
  induction F using Finset.induction_on generalizing f with
  | empty => exact ⟨f, le_rfl, hfbase, by simp, by simp⟩
  | @insert x F hxF ih =>
      obtain ⟨g, hfg, hgbase, hrestrict, hF⟩ :=
        ih f hfbase (fun y hy => hFdim y (Finset.mem_insert_of_mem hy))
      by_cases hxg : x ∈ g.domain
      · exact ⟨g, hfg, hgbase, hrestrict, (Finset.forall_mem_insert _ _ _).2 ⟨hxg, hF⟩⟩
      · obtain ⟨hdom, hdvr⟩ :
            ∃ _ : IsDomain (X.presheaf.stalk x), IsDiscreteValuationRing (X.presheaf.stalk x) :=
          ((isDiscreteValuationRing_tfae (X.presheaf.stalk x)).out 3 1).mp
            (show IsRegularLocalRing (X.presheaf.stalk x) ∧
                ringKrullDim (X.presheaf.stalk x) = 1 from
              ⟨hregular x, hFdim x (Finset.mem_insert_self x F)⟩)
        have : IsDomain (X.presheaf.stalk x) := hdom
        have : IsDiscreteValuationRing (X.presheaf.stalk x) := hdvr
        have : g.IsOver S := isOver_iff.mpr hgbase
        obtain ⟨V, hUV, hxV, gm, hgmBase, hgmRestr⟩ :=
          exists_open_extension_of_valuationRing_stalk (X ↘ S) (Y ↘ S) x g.domain g.hom hgbase
            (g.dense_domain x) (Or.inr inferInstance)
        refine ⟨⟨V, g.dense_domain.mono hUV, gm⟩, hfg.trans hUV, hgmBase, ?_, ?_⟩
        · rw [← Scheme.homOfLE_homOfLE X hfg hUV, Category.assoc, hgmRestr, hrestrict]
        · exact (Finset.forall_mem_insert _ _ _).2 ⟨hxV, fun y hy => hUV (hF y hy)⟩

/-- On a regular Noetherian scheme of dimension two over `S`, a partial map over `S` into a
scheme proper over `S` extends to a domain whose complement contains only points whose local ring
has Krull dimension two. -/
theorem exists_extension_codimension_two {S X Y : Scheme.{u}} [X.Over S] [Y.Over S]
    [IsNoetherian X] [IsProper (Y ↘ S)] (hregular : IsRegular X)
    (hdim : topologicalKrullDim X = 2) (f : X.PartialMap Y) [f.IsOver S] :
    ∃ g : X.PartialMap Y, f.domain ≤ g.domain ∧
      g.hom ≫ (Y ↘ S) = g.domain.ι ≫ (X ↘ S) ∧
      ∀ x : X, x ∉ (g.domain : Set X) → ringKrullDim (X.presheaf.stalk x) = 2 := by
  classical
  have hregularAt : ∀ x : X, IsRegularLocalRing (X.presheaf.stalk x) :=
    (((isRegular_tfae X).out 1 2 rfl rfl).mp hregular).2
  have hfbase : f.hom ≫ (Y ↘ S) = f.domain.ι ≫ (X ↘ S) := isOver_iff.mp ‹f.IsOver S›
  have hCclosed : IsClosed ((f.domain : Set X)ᶜ) := f.domain.2.isClosed_compl
  obtain ⟨T, hTfin, hTclosed, hTirr, hTC⟩ :=
    TopologicalSpace.NoetherianSpace.exists_finite_set_isClosed_irreducible hCclosed
  let : Finite {D : Set X // D ∈ T} := hTfin.to_subtype
  let η : {D : Set X // D ∈ T} → X := fun D => (hTirr D.1 D.2).genericPoint
  have hFfinite : {x : X | x ∈ Set.range η ∧ ringKrullDim (X.presheaf.stalk x) = 1}.Finite :=
    (Set.finite_range η).subset fun _ hx => hx.1
  obtain ⟨f₁, hff₁, hf₁base, hfrestrict, hFdomain⟩ :=
    exists_extension_of_finset_ringKrullDim_eq_one f hfbase hregularAt hFfinite.toFinset
      fun _ hx => (hFfinite.mem_toFinset.mp hx).2
  refine ⟨f₁, hff₁, hf₁base, fun x hxC₁ => ?_⟩
  have hxC : x ∈ (f.domain : Set X)ᶜ := fun hxU => hxC₁ (hff₁ hxU)
  rw [hTC] at hxC
  obtain ⟨D, hDT, hxD⟩ := Set.mem_sUnion.mp hxC
  have hyD : IsGenericPoint (η ⟨D, hDT⟩) D :=
    (hTirr D hDT).isGenericPoint_genericPoint (hTclosed D hDT)
  have hyU : η ⟨D, hDT⟩ ∉ (f.domain : Set X) := by
    rw [← Set.mem_compl_iff, hTC]
    exact Set.mem_sUnion.mpr ⟨D, hDT, hyD.mem⟩
  rcases coheight_eq_one_or_two_of_notMem_dense hdim.le f.dense_domain hyU with h1 | h2
  · have hyF : η ⟨D, hDT⟩ ∈ hFfinite.toFinset := hFfinite.mem_toFinset.mpr
      ⟨⟨⟨D, hDT⟩, rfl⟩, by rw [ringKrullDim_stalk_eq_coheight, h1]; rfl⟩
    have hxy : x ≤ η ⟨D, hDT⟩ := Scheme.le_iff_specializes.mpr (hyD.specializes hxD)
    have hne : x ≠ η ⟨D, hDT⟩ := fun heq => hxC₁ (heq ▸ hFdomain _ hyF)
    have hyx : ¬ η ⟨D, hDT⟩ ≤ x := fun hyx => hne (inseparable_iff_specializes_and.mpr
      ⟨Scheme.le_iff_specializes.mp hxy, Scheme.le_iff_specializes.mp hyx⟩).eq.symm
    have hco : Order.coheight x ≤ 2 :=
      WithBot.coe_le_coe.mp ((coheight_le_topologicalKrullDim x).trans hdim.le)
    have hxLower : (2 : ℕ∞) ≤ Order.coheight x :=
      calc (2 : ℕ∞) = Order.coheight (η ⟨D, hDT⟩) + 1 := by rw [h1]; norm_num
        _ ≤ Order.coheight x := Order.coheight_add_one_le (lt_of_le_not_ge hxy hyx)
    rw [ringKrullDim_stalk_eq_coheight, le_antisymm hco hxLower]
    norm_num
  · have hxy : x = η ⟨D, hDT⟩ := eq_genericPoint_of_coheight_two hdim.le hyD h2 hxD
    rw [ringKrullDim_stalk_eq_coheight, hxy, h2]
    norm_num

end AlgebraicGeometry.Scheme.PartialMap

end
