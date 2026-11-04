module

public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import StacksFrontier.AlgebraicGeometry.FormalSpace.AffineFibreProduct
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CoproductChartRepresentable
public import StacksFrontier.AlgebraicGeometry.FormalSpace.DiagonalAtlasCover
public import StacksFrontier.AlgebraicGeometry.FormalSpace.DiagonalChartRepresentable
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RelativeDiagonal
public import StacksFrontier.AlgebraicGeometry.FormalSpace.SchemeAtlas
public import StacksFrontier.AlgebraicGeometry.Size.FiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.ClopenPartRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.RelativeLocalCriteria
public import StacksFrontier.AlgebraicGeometry.Spaces.Presentation.BigFppfSite
public import StacksFrontier.CategoryTheory.Limits.BinaryProductDiagonal
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The diagonal of a formal algebraic space is representable

Let `S` be a scheme contained in a big fppf site `B`. **Stacks 0AIP** asserts five things about
the absolute diagonal `X ⟶ X ⨯ X` of a formal algebraic space over `S`: it is representable by
schemes, locally quasi-finite, locally of finite type, a monomorphism and separated. This file
proves the **representability** assertion for an arbitrary formal algebraic space, and then the
three other non-trivial ones, which are phrased through it:
`CategoryTheory.MorphismProperty.relative` contains relative representability, so none of them
can even be stated until representability is available. The remaining assertion, that the
diagonal is a monomorphism, costs nothing and is in
`StacksFrontier.AlgebraicGeometry.FormalSpace.RelativeDiagonal`. The corresponding four assertions
of **Stacks 0AN2** for the relative diagonal of a morphism out of a formal algebraic space
follow at the end of the file, by base change.

Representability of the diagonal is equivalent to representability of every morphism into `X`
from a sheaf represented by an object of the site, so the content is that the relative product
`h_a ×_X h_b` of two scheme-valued points is represented by an object of the site. That is
obtained from the criterion of
`StacksFrontier.AlgebraicGeometry.FormalSpace.DiagonalChartRepresentable`, which asks for a
monomorphism of `h_a ×_X h_b` into a sheaf represented by an object of the site together with
a surjective étale chart whose composite with it is locally of finite type. The monomorphism is
the inclusion into `h_{a ⨯ b}`; this file builds the chart.

## Main results

* `AlgebraicGeometry.FormalSpace.exists_member_chart`: for one member `Xi ⟶ X` of an atlas as
  in Definition 0AIM, a chart of `(h_a ×_X Xi) ×_{Xi} (h_b ×_X Xi)` by an object of the site
  whose morphism to `a ⨯ b` is locally of finite type.
* `AlgebraicGeometry.FormalSpace.relative_etale_comp_of_isPullback`: that chart, composed with
  the projection to `h_a ×_X h_b`, is étale after every represented base change.
* `AlgebraicGeometry.FormalSpace.exists_index_mem_range_of_atlas`: the members jointly cover
  every point of the ambient product which a scheme-valued point of `h_a ×_X h_b` reaches.
* `AlgebraicGeometry.FormalSpace.exists_isPullback_locallyOfFiniteType_of_isFormalAlgebraicSpace`,
  `AlgebraicGeometry.FormalSpace.essImage_pullback_of_isFormalAlgebraicSpace`: the relative
  product of two scheme-valued points is represented by an object of the site, locally of finite
  type over the product of the two points.
* `AlgebraicGeometry.FormalSpace.hasRepresentableRelativeProducts_of_isFormalAlgebraicSpace`,
  `AlgebraicGeometry.FormalSpace.relativelyRepresentable_diag_of_isFormalAlgebraicSpace`:
  the representability assertion of **Stacks 0AIP** for an arbitrary formal algebraic space.
* `AlgebraicGeometry.FormalSpace.isPullback_diag_of_isPullback_prodLift`: a represented base
  change of an absolute diagonal is the base change of the relative product of the two
  components of the test point, along the diagonal of the test object.
* `…relative_locallyOfFiniteType_diag_of_isFormalAlgebraicSpace`,
  `…relative_locallyQuasiFinite_diag_of_isFormalAlgebraicSpace`,
  `…relative_isSeparated_diag_of_isFormalAlgebraicSpace`: the three remaining non-trivial
  assertions of **Stacks 0AIP** for an arbitrary formal algebraic space.
* `…relative_locallyOfFiniteType_pullback_diagonal_of_isFormalAlgebraicSpace`,
  `…relative_locallyQuasiFinite_pullback_diagonal_of_isFormalAlgebraicSpace`,
  `…relative_isSeparated_pullback_diagonal_of_isFormalAlgebraicSpace`,
  `…relativelyRepresentable_pullback_diagonal_of_isFormalAlgebraicSpace`: the corresponding four
  assertions of **Stacks 0AN2**, for a morphism whose source is an arbitrary formal algebraic
  space.

## Implementation notes

**The members of the covering.** The source covers `h_a ×_X h_b` by the sheaves
`(h_a ×_X Xi) ×_{Xi} (h_b ×_X Xi)` and argues that each is a scheme. Here each of the two
factors is only an *algebraic space*, by Stacks 03XY twice
(`…isAlgebraicSpaceULift_pullback_snd_pullback_snd`), so Stacks 0AI8 does not apply to the
fibre product directly. It is applied one step further in: each factor carries a scheme atlas
`Za`, `Zb` by an object of the site, étale over `a` respectively over `b`, and `Za ×_{Xi} Zb`
*is* covered by Stacks 0AI8, which represents it by an object `W` of the site with
`W ⟶ Za ⨯ Zb` a closed immersion. That is what makes `W ⟶ a ⨯ b` locally of finite type: a
closed immersion followed by a product of two étale morphisms.

**Why the chart is étale over the relative product.** The composite `h_W ⟶ E` for
`E = h_a ×_X h_b` is not a composite of morphisms étale after every represented base change,
because the intermediate `E ×_X Xi` is representable only by algebraic spaces. The
monomorphism `E ⟶ h_{a ⨯ b}` is what repairs this: a represented base change of `h_W ⟶ E` is
the *scheme* fibre product over `a ⨯ b`, hence an object of the site, and it maps to
`E ×_X Xi` base-changed to the test object by a base change of the chart, which is étale over
that base change by the definition of an atlas. This is
`…relative_etale_comp_of_isPullback`.

**The point-indexed refinement, and the cardinal bound.** The atlas of a formal algebraic space
is indexed by a type of `Type (u + 1)` and carries no bound against the site's size cutoff, so
the family cannot be collected into a single object of the site as it stands. It is refined:
for each point of the scheme `a ⨯ b` lying in the range of some member, one member is chosen
together with an affine open of it around a preimage of that point, and that affine open is the
refined member. The index type is then a subtype of the points of `a ⨯ b`, so it is in
`Type u`, and `μ := 2 ^ (a ⨯ b).size` bounds it by
`AlgebraicGeometry.mk_scheme_le_two_power_size`, bounds each refined member by Stacks 04T7
(`AlgebraicGeometry.Scheme.size_le_of_locallyOfFiniteType`, which is why the members have to be
affine: it asks for a quasi-compact source), and lies below the cutoff because the cutoff is a
strong prelimit. No coproduct of atlas members ever enters the site.

**What the refined family has to satisfy.** Not that it generates a covering sieve of `a ⨯ b`:
it cannot, `E ⟶ h_{a ⨯ b}` being a monomorphism. What is needed is that for every object `T`
of the site and every section of `E` over `T` the base changes `T ×_E W_x` cover `T`, and those
base changes are the scheme fibre products `T ×_{a ⨯ b} W_x` precisely because that morphism is
a monomorphism. Each is étale over `T`, hence flat and locally of finite presentation, so
`…fppf_ofArrows_mem` reduces the claim to surjectivity on points of `T`; the image of a point
of `T` in `a ⨯ b` is in the range of some member by `…family_imageSieve_mem` together with
`AlgebraicGeometry.Space.exists_covering_refining_sieve`, which is
`…exists_index_mem_range_of_atlas`; and a point of `T ×_{a ⨯ b} W_x` above it then exists by
`AlgebraicGeometry.Scheme.Pullback.exists_preimage_pullback`.

**The other three assertions.** Locally of finite type, locally quasi-finite and separated are
phrased through `CategoryTheory.MorphismProperty.relative`, which contains relative
representability, so they become statable exactly when the representability assertion is
available — and they are proved here too. The criterion of
`StacksFrontier.AlgebraicGeometry.FormalSpace.DiagonalChartRepresentable` returns, besides the
representing object `Po` of the relative product, the local finite type of the morphism
`Po ⟶ a ⨯ b` of the site which the two projections assemble; a represented base change of
`diag X` is the base change of that morphism along `diag c`, by
`…isPullback_diag_of_isPullback_prodLift`, so it is locally of finite type. It is also a
monomorphism, the diagonal being one, so it is separated and locally quasi-finite by Stacks
0CT8 — separatedness needing no finiteness at all.

The four affine registrations of Stacks 0AIP and the general monomorphism registration remain in
`StacksFrontier.AlgebraicGeometry.FormalSpace.RelativeDiagonal`, which also carries the two
hypothesis-taking reductions of Stacks 0AN2 to Stacks 0AIP that this file feeds.

## References

* [Stacks Project, Tag 03XY](https://stacks.math.columbia.edu/tag/03XY)
* [Stacks Project, Tag 04T7](https://stacks.math.columbia.edu/tag/04T7)
* [Stacks Project, Tag 0AI8](https://stacks.math.columbia.edu/tag/0AI8)
* [Stacks Project, Tag 0AIM](https://stacks.math.columbia.edu/tag/0AIM)
* [Stacks Project, Tag 0AIP](https://stacks.math.columbia.edu/tag/0AIP)
* [Stacks Project, Tag 0AIS](https://stacks.math.columbia.edu/tag/0AIS)
* [Stacks Project, Tag 0AN2](https://stacks.math.columbia.edu/tag/0AN2)
* [Stacks Project, Tag 0CT8](https://stacks.math.columbia.edu/tag/0CT8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe u

section Categorical


variable {D : Type*} [Category* D]

/-- A cartesian square over a subobject stays cartesian over the ambient object. -/
theorem isPullback_comp_mono {P V T E N : D} {p : P ⟶ V} {q : P ⟶ T}
    {g : V ⟶ E} {s : T ⟶ E} (h : IsPullback p q g s) (n : E ⟶ N) [Mono n] :
    IsPullback p q (g ≫ n) (s ≫ n) := by
  have hw : p ≫ g ≫ n = q ≫ s ≫ n := by
    rw [← Category.assoc, ← Category.assoc, h.w]
  refine ⟨⟨hw⟩, ⟨PullbackCone.IsLimit.mk hw
    (fun c => h.lift c.fst c.snd ((cancel_mono n).mp (by
      simpa only [Category.assoc] using c.condition)))
    (fun c => h.lift_fst _ _ _) (fun c => h.lift_snd _ _ _)
    (fun c m h₁ h₂ => h.hom_ext (by rw [h₁, h.lift_fst]) (by rw [h₂, h.lift_snd]))⟩⟩

/-- A square cartesian over an ambient object through a monomorphism is cartesian over the
subobject. -/
theorem isPullback_of_comp_mono {P V T E N : D} {p : P ⟶ V} {q : P ⟶ T}
    {g : V ⟶ E} {s : T ⟶ E} (n : E ⟶ N) [Mono n]
    (h : IsPullback p q (g ≫ n) (s ≫ n)) : IsPullback p q g s := by
  have hw : p ≫ g = q ≫ s := (cancel_mono n).mp (by
    simpa only [Category.assoc] using h.w)
  refine ⟨⟨hw⟩, ⟨PullbackCone.IsLimit.mk hw
    (fun c => h.lift c.fst c.snd (by
      rw [← Category.assoc, ← Category.assoc, c.condition]))
    (fun c => h.lift_fst _ _ _) (fun c => h.lift_snd _ _ _)
    (fun c m h₁ h₂ => h.hom_ext (by rw [h₁, h.lift_fst]) (by rw [h₂, h.lift_snd]))⟩⟩

variable [HasPullbacks D]

/-- **The relative product of two morphisms, base changed along a third.** For three morphisms
`ξa`, `ξb` and `fi` into one object, the fibre product over the source of `fi` of the two base
changes `ξa ×_· fi` and `ξb ×_· fi` is the base change along `fi` of the fibre product
`ξa ×_· ξb`. -/
theorem isPullback_of_pullback_snd_snd {Xa Xb Xi Xo : D}
    (ξa : Xa ⟶ Xo) (ξb : Xb ⟶ Xo) (fi : Xi ⟶ Xo)
    (nE : pullback (pullback.snd ξa fi) (pullback.snd ξb fi) ⟶ pullback ξa ξb)
    (hnEa : nE ≫ pullback.fst ξa ξb =
      pullback.fst (pullback.snd ξa fi) (pullback.snd ξb fi) ≫ pullback.fst ξa fi)
    (hnEb : nE ≫ pullback.snd ξa ξb =
      pullback.snd (pullback.snd ξa fi) (pullback.snd ξb fi) ≫ pullback.fst ξb fi) :
    IsPullback
      (pullback.fst (pullback.snd ξa fi) (pullback.snd ξb fi) ≫ pullback.snd ξa fi)
      nE fi (pullback.fst ξa ξb ≫ ξa) := by
  have hw : (pullback.fst (pullback.snd ξa fi) (pullback.snd ξb fi) ≫
      pullback.snd ξa fi) ≫ fi = nE ≫ pullback.fst ξa ξb ≫ ξa := by
    rw [← Category.assoc nE, hnEa, Category.assoc, Category.assoc, pullback.condition]
  refine ⟨⟨hw⟩, ⟨PullbackCone.IsLimit.mk hw (fun c => ?_) (fun c => ?_) (fun c => ?_)
    (fun c m h₁ h₂ => ?_)⟩⟩
  · refine pullback.lift
      (pullback.lift (c.snd ≫ pullback.fst ξa ξb) c.fst ?_)
      (pullback.lift (c.snd ≫ pullback.snd ξa ξb) c.fst ?_) ?_
    · rw [Category.assoc]
      exact c.condition.symm
    · rw [Category.assoc, ← pullback.condition]
      exact c.condition.symm
    · rw [pullback.lift_snd, pullback.lift_snd]
  · rw [← Category.assoc, pullback.lift_fst, pullback.lift_snd]
  · refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, hnEa, ← Category.assoc, pullback.lift_fst, pullback.lift_fst]
    · rw [Category.assoc, hnEb, ← Category.assoc, pullback.lift_snd, pullback.lift_fst]
  · have ha : m ≫ pullback.fst (pullback.snd ξa fi) (pullback.snd ξb fi) =
        pullback.lift (c.snd ≫ pullback.fst ξa ξb) c.fst (by
          rw [Category.assoc]; exact c.condition.symm) := by
      refine pullback.hom_ext ?_ ?_
      · rw [Category.assoc, ← hnEa, ← Category.assoc, h₂, pullback.lift_fst]
      · rw [Category.assoc, pullback.lift_snd]
        exact h₁
    have hb : m ≫ pullback.snd (pullback.snd ξa fi) (pullback.snd ξb fi) =
        pullback.lift (c.snd ≫ pullback.snd ξa ξb) c.fst (by
          rw [Category.assoc, ← pullback.condition]; exact c.condition.symm) := by
      refine pullback.hom_ext ?_ ?_
      · rw [Category.assoc, ← hnEb, ← Category.assoc, h₂, pullback.lift_fst]
      · rw [Category.assoc, ← pullback.condition, h₁, pullback.lift_snd]
    refine pullback.hom_ext ?_ ?_
    · rw [ha, pullback.lift_fst]
    · rw [hb, pullback.lift_snd]

omit [HasPullbacks D] in
/-- **The base change of a diagonal along a pair of morphisms out of a product is the fibre
product of that pair.** If `T` is a binary product of `A` and `B` with projections `πa`, `πb`,
and `P` is the base change of `diag X` along the morphism `T ⟶ X ⨯ X` built from `πa ≫ ua` and
`πb ≫ ub`, then `P` is the fibre product of `ua` and `ub`. -/
theorem isPullback_of_isPullback_diag [HasBinaryProducts D]
    {Xx A Bb T P : D} {πa : T ⟶ A} {πb : T ⟶ Bb}
    (hT : IsLimit (BinaryFan.mk πa πb))
    {ua : A ⟶ Xx} {ub : Bb ⟶ Xx} {p : P ⟶ Xx} {q : P ⟶ T}
    (h : IsPullback p q (diag Xx) (prod.lift (πa ≫ ua) (πb ≫ ub))) :
    IsPullback (q ≫ πa) (q ≫ πb) ua ub := by
  have hpa : p = q ≫ πa ≫ ua := by
    have := h.w =≫ (prod.fst : Xx ⨯ Xx ⟶ Xx)
    simpa using this
  have hpb : p = q ≫ πb ≫ ub := by
    have := h.w =≫ (prod.snd : Xx ⨯ Xx ⟶ Xx)
    simpa using this
  have hw : (q ≫ πa) ≫ ua = (q ≫ πb) ≫ ub := by
    rw [Category.assoc, Category.assoc, ← hpa, ← hpb]
  have key : ∀ c : PullbackCone ua ub, ∃ l : c.pt ⟶ P,
      l ≫ p = c.fst ≫ ua ∧ l ≫ q ≫ πa = c.fst ∧ l ≫ q ≫ πb = c.snd := by
    intro c
    obtain ⟨z, hza, hzb⟩ := BinaryFan.IsLimit.lift' hT c.fst c.snd
    simp only [BinaryFan.mk_fst, BinaryFan.mk_snd] at hza hzb
    have hcond : (c.fst ≫ ua) ≫ diag Xx = z ≫ prod.lift (πa ≫ ua) (πb ≫ ub) := by
      refine prod.hom_ext ?_ ?_ <;>
        simp [reassoc_of% hza, reassoc_of% hzb, c.condition]
    exact ⟨h.lift (c.fst ≫ ua) z hcond, h.lift_fst _ _ _,
      by rw [← Category.assoc, h.lift_snd, hza], by rw [← Category.assoc, h.lift_snd, hzb]⟩
  choose L hLp hLa hLb using key
  refine ⟨⟨hw⟩, ⟨PullbackCone.IsLimit.mk hw L (fun c => hLa c) (fun c => hLb c)
    (fun c m h₁ h₂ => ?_)⟩⟩
  refine h.hom_ext ?_ ?_
  · rw [hLp, hpa, ← Category.assoc q πa ua, ← Category.assoc m (q ≫ πa) ua, h₁]
  · refine BinaryFan.IsLimit.hom_ext hT ?_ ?_
    · simp only [BinaryFan.mk_fst, Category.assoc, h₁, hLa]
    · simp only [BinaryFan.mk_snd, Category.assoc, h₂, hLb]

omit [HasPullbacks D] in
/-- **The base change of a diagonal along a morphism to a product is the diagonal base change
of the fibre product of its two components.** Let `gg : T ⟶ Xx ⨯ Xx` have components `ua`, `ub`,
let `Po` be a fibre product of `ua` and `ub` with projections `pa`, `pb`, and let
`nn : Po ⟶ T ⨯ T` be the morphism those projections assemble. Then the base change of `nn`
along `diag T` is the base change of `diag Xx` along `gg`, with the projection to `T` as one of
its legs.

This is the step which turns the fibre product of two scheme-valued points of a formal
algebraic space into a base change of the absolute diagonal: the fibre product lives over
`T ⨯ T`, and the diagonal of `T` cuts out of it exactly the locus where the two points agree,
which is what testing `diag Xx` against `gg` produces. -/
theorem isPullback_diag_of_isPullback_prodLift [HasBinaryProducts D]
    {Xx T Po Z : D} {ua ub : T ⟶ Xx} {gg : T ⟶ Xx ⨯ Xx}
    (hga : gg ≫ prod.fst = ua) (hgb : gg ≫ prod.snd = ub)
    {pa pb : Po ⟶ T}
    (hsq : IsPullback pa pb ua ub) {nn : Po ⟶ T ⨯ T}
    (hna : nn ≫ prod.fst = pa) (hnb : nn ≫ prod.snd = pb)
    {β : Z ⟶ Po} {σ : Z ⟶ T} (hbb : IsPullback β σ nn (diag T)) :
    IsPullback (σ ≫ ua) σ (diag Xx) gg := by
  obtain rfl : gg = prod.lift ua ub := by
    refine prod.hom_ext ?_ ?_ <;> simp [hga, hgb]
  have hβa : β ≫ pa = σ := by
    rw [← hna, ← Category.assoc, hbb.w]
    simp
  have hβb : β ≫ pb = σ := by
    rw [← hnb, ← Category.assoc, hbb.w]
    simp
  have hσ : σ ≫ ua = σ ≫ ub :=
    calc σ ≫ ua = (β ≫ pa) ≫ ua := by rw [hβa]
      _ = (β ≫ pb) ≫ ub := by rw [Category.assoc, Category.assoc, hsq.w]
      _ = σ ≫ ub := by rw [hβb]
  have hw : (σ ≫ ua) ≫ diag Xx = σ ≫ prod.lift ua ub := by
    refine prod.hom_ext ?_ ?_
    · simp
    · simpa using hσ
  have key : ∀ s : PullbackCone (diag Xx) (prod.lift ua ub), ∃ l : s.pt ⟶ Z,
      l ≫ σ ≫ ua = s.fst ∧ l ≫ σ = s.snd ∧ ∀ m : s.pt ⟶ Z, m ≫ σ = s.snd → m = l := by
    intro s
    have h₁ : s.snd ≫ ua = s.fst := by
      simpa using (s.condition =≫ (prod.fst : Xx ⨯ Xx ⟶ Xx)).symm
    have h₂ : s.snd ≫ ub = s.fst := by
      simpa using (s.condition =≫ (prod.snd : Xx ⨯ Xx ⟶ Xx)).symm
    have hc : s.snd ≫ ua = s.snd ≫ ub := h₁.trans h₂.symm
    have hlift : hsq.lift s.snd s.snd hc ≫ nn = s.snd ≫ diag T := by
      refine prod.hom_ext ?_ ?_
      · rw [Category.assoc, hna, hsq.lift_fst]
        simp
      · rw [Category.assoc, hnb, hsq.lift_snd]
        simp
    refine ⟨hbb.lift (hsq.lift s.snd s.snd hc) s.snd hlift, ?_, hbb.lift_snd _ _ _,
      fun m hm => ?_⟩
    · rw [← Category.assoc, hbb.lift_snd, h₁]
    · refine hbb.hom_ext ?_ (by rw [hm, hbb.lift_snd])
      rw [hbb.lift_fst]
      refine hsq.hom_ext ?_ ?_
      · rw [Category.assoc, hβa, hm, hsq.lift_fst]
      · rw [Category.assoc, hβb, hm, hsq.lift_snd]
  choose L hLfst hLsnd hLuniq using key
  exact ⟨⟨hw⟩, ⟨PullbackCone.IsLimit.mk hw L hLfst hLsnd
    (fun s m _ h₂ => hLuniq s m h₂)⟩⟩

end Categorical

section Member

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A scheme atlas of a scheme-valued point of a formal algebraic space pulled back to an
atlas member.** For `fi : Xi ⟶ X` representable by algebraic spaces and étale and `ξ` a
scheme-valued point of `X`, the fibre product `ξ ×_X Xi` is an algebraic space, so it has a
chart by an object of the site, and the composite of that chart with the projection to the
point is the universe-lifted Yoneda image of an étale morphism of the site. -/
theorem exists_atlas_pullback_fi {X Xi : FppfSheaf B S hS} (fi : Xi ⟶ X)
    (hfi : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS fi.hom)
    (het : Space.HasPropertyULift.{u + 1} B S hS
      (fun _ _ g ↦ Space.IsEtaleULift.{u + 1} B S hS g.hom) fi.hom hfi)
    (a : BigFppfOver B S hS) (ξ : uliftYoneda.{u + 1}.obj a ⟶ X.obj) :
    ∃ (Z : BigFppfOver B S hS) (z : uliftYoneda.{u + 1}.obj Z ⟶ pullback ξ fi.hom)
      (ρ : Z ⟶ a),
      (Space.surjectiveOnSite B S hS).relative uliftYoneda.{u + 1} z ∧
      (Space.etaleOnSite B S hS).relative uliftYoneda.{u + 1} z ∧
      uliftYoneda.{u + 1}.map ρ = z ≫ pullback.fst ξ fi.hom ∧
      Etale ((BigFppfOver.toScheme B S hS).map ρ) := by
  obtain ⟨Z, z, hs, he⟩ := (hfi a ξ).exists_atlas
  refine ⟨Z, z, uliftYoneda.{u + 1}.preimage (z ≫ pullback.fst ξ fi.hom), hs, he,
    uliftYoneda.{u + 1}.map_preimage _, ?_⟩
  have h1 : (Space.etaleOnSite B S hS).relative uliftYoneda.{u + 1}
      (z ≫ pullback.fst ξ fi.hom) := het a ξ Z z he
  rw [← uliftYoneda.{u + 1}.map_preimage (z ≫ pullback.fst ξ fi.hom)] at h1
  exact MorphismProperty.of_relative_map (P := Space.etaleOnSite B S hS)
    (F := uliftYoneda.{u + 1}) h1

/-- **A product of two morphisms of the site locally of finite type is locally of finite
type.** The product of two morphisms is the composite of two base changes, so the assertion is
the stability of local finite type under base change and composition, read on the site through
the universe-lifted Yoneda embedding, which preserves binary products. -/
@[ega "IV 1.3.4" "(iv), special case"]
theorem locallyOfFiniteType_prod_map [HasBinaryProducts (BigFppfOver B S hS)]
    {Za Zb a b : BigFppfOver B S hS} (ρa : Za ⟶ a) (ρb : Zb ⟶ b)
    (hρa : LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map ρa))
    (hρb : LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map ρb)) :
    LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map (prod.map ρa ρb)) := by
  let Y := uliftYoneda.{u + 1} (C := BigFppfOver B S hS)
  let Pft : MorphismProperty (BigFppfOver B S hS) :=
    MorphismProperty.inverseImage
      (@AlgebraicGeometry.LocallyOfFiniteType.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)
  let : Pft.IsStableUnderComposition := MorphismProperty.IsStableUnderComposition.inverseImage _
  have hprod : Pft.relative Y (prod.map (Y.map ρa) (Y.map ρb)) :=
    MorphismProperty.relative_prod_map Y Pft (Y.map ρa) (Y.map ρb)
      (Space.relative_uliftYoneda_map B S hS _ ρa hρa)
      (Space.relative_uliftYoneda_map B S hS _ ρb hρb)
  let e₁ : Y.obj (Za ⨯ Zb) ≅ Y.obj Za ⨯ Y.obj Zb := PreservesLimitPair.iso Y Za Zb
  let e₂ : Y.obj (a ⨯ b) ≅ Y.obj a ⨯ Y.obj b := PreservesLimitPair.iso Y a b
  have hnat : Y.map (prod.map ρa ρb) ≫ e₂.hom =
      e₁.hom ≫ prod.map (Y.map ρa) (Y.map ρb) := prodComparison_natural Y ρa ρb
  have hmap : Pft.relative Y (Y.map (prod.map ρa ρb)) := by
    have hcomp : Y.map (prod.map ρa ρb) =
        e₁.hom ≫ prod.map (Y.map ρa) (Y.map ρb) ≫ e₂.inv := by
      rw [← Category.assoc, ← hnat, Category.assoc, e₂.hom_inv_id, Category.comp_id]
    rw [hcomp]
    exact MorphismProperty.RespectsIso.precomp _ e₁.hom _
      (MorphismProperty.RespectsIso.postcomp _ e₂.inv _ hprod)
  exact MorphismProperty.of_relative_map (P := Pft) (F := Y) hmap

/-- **Stacks 0AI8 for two scheme-valued points of an affine formal algebraic space.** The fibre
product over an affine formal algebraic space `Xi` of two morphisms out of sheaves represented
by objects `Za`, `Zb` of the site is represented by an object `W` of the site, and the induced
morphism `W ⟶ Za ⨯ Zb` is a closed immersion of schemes.

The absolute diagonal of `Xi` is relatively a closed immersion, which is Stacks 0AI8; its base
change along the morphism `Za ⨯ Zb ⟶ Xi ⨯ Xi` assembled from the two points is the fibre
product, because the sheafified Yoneda embedding preserves binary products. -/
theorem exists_closedImmersion_isPullback_of_isAffineFormal
    [HasBinaryProducts (BigFppfOver B S hS)]
    {Xi : FppfSheaf B S hS} (hXi : IsAffineFormalAlgebraicSpace B S hS Xi)
    {Za Zb : BigFppfOver B S hS}
    (ζa : uliftYoneda.{u + 1}.obj Za ⟶ Xi.obj)
    (ζb : uliftYoneda.{u + 1}.obj Zb ⟶ Xi.obj) :
    ∃ (W : BigFppfOver B S hS) (si : W ⟶ Za ⨯ Zb),
      IsClosedImmersion ((BigFppfOver.toScheme B S hS).map si) ∧
      IsPullback (uliftYoneda.{u + 1}.map (si ≫ prod.fst))
        (uliftYoneda.{u + 1}.map (si ≫ prod.snd)) ζa ζb := by
  let J := BigFppfOver.topology B S hS
  let F := Sheaf.sheafifiedYoneda J
  let K := sheafToPresheaf J (Type (u + 1))
  let : J.Subcanonical := bigFppfOver_subcanonical B S hS
  let : F.Full := (Sheaf.fullyFaithfulSheafifiedYoneda J).full
  let : F.Faithful := (Sheaf.fullyFaithfulSheafifiedYoneda J).faithful
  let : PreservesLimitsOfShape (Discrete WalkingPair) F :=
    preservesLimitsOfShape_of_natIso (Sheaf.sheafifiedYonedaIsoUliftYoneda' J).symm
  let gl : F ⋙ K ≅ uliftYoneda.{u + 1} := sheafifiedYonedaPresheafIso B S hS
  let ζa' : F.obj Za ⟶ Xi := K.preimage (gl.hom.app Za ≫ ζa)
  let ζb' : F.obj Zb ⟶ Xi := K.preimage (gl.hom.app Zb ≫ ζb)
  have hζa : K.map ζa' = gl.hom.app Za ≫ ζa := K.map_preimage _
  have hζb : K.map ζb' = gl.hom.app Zb ≫ ζb := K.map_preimage _
  have hcl := relative_isClosedImmersion_diag_of_isAffineFormal B S hS hXi
  refine ⟨hcl.rep.pullback
    (prod.lift (F.map (prod.fst : Za ⨯ Zb ⟶ Za) ≫ ζa')
      (F.map (prod.snd : Za ⨯ Zb ⟶ Zb) ≫ ζb')),
    hcl.rep.snd _, hcl.property_snd _, ?_⟩
  have hT : IsLimit (BinaryFan.mk (F.map (prod.fst : Za ⨯ Zb ⟶ Za))
      (F.map (prod.snd : Za ⨯ Zb ⟶ Zb))) :=
    mapIsLimitOfPreservesOfIsLimit F _ _ (prodIsProd Za Zb)
  have hsq := isPullback_of_isPullback_diag hT (hcl.rep.isPullback
    (prod.lift (F.map (prod.fst : Za ⨯ Zb ⟶ Za) ≫ ζa')
      (F.map (prod.snd : Za ⨯ Zb ⟶ Zb) ≫ ζb')))
  rw [← F.map_comp, ← F.map_comp] at hsq
  refine (hsq.map K).of_iso (gl.app _) (gl.app Za) (gl.app Zb) (Iso.refl Xi.obj)
    (gl.hom.naturality _) (gl.hom.naturality _) ?_ ?_
  · exact (Category.comp_id _).trans hζa
  · exact (Category.comp_id _).trans hζb

/-- **The chart of one atlas member.** Let `X` be an fppf sheaf on the big fppf site of `S`,
let `fi : Xi ⟶ X` be a morphism from an affine formal algebraic space which is representable by
algebraic spaces and étale, as a member of an atlas as in Definition 0AIM, and let `ξa`, `ξb`
be two scheme-valued points of `X`. Then the base change along `fi` of the relative product of
`ξa` and `ξb` — the sheaf `(ξa ×_X Xi) ×_{Xi} (ξb ×_X Xi)` — carries a surjective étale chart
`W` by an object of the site, whose morphism to `a ⨯ b` is locally of finite type.

The two factors are algebraic spaces, so each has a scheme atlas `Za`, `Zb`, étale over `a`
respectively `b`; their fibre product over the affine formal algebraic space `Xi` is an object
of the site closed-immersed into `Za ⨯ Zb` by **Stacks 0AI8**, and a closed immersion followed
by a product of two étale morphisms is locally of finite type. -/
theorem exists_member_chart [HasBinaryProducts (BigFppfOver B S hS)]
    {X Xi : FppfSheaf B S hS} (fi : Xi ⟶ X)
    (hXi : IsAffineFormalAlgebraicSpace B S hS Xi)
    (hfi : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS fi.hom)
    (het : Space.HasPropertyULift.{u + 1} B S hS
      (fun _ _ g ↦ Space.IsEtaleULift.{u + 1} B S hS g.hom) fi.hom hfi)
    (a b : BigFppfOver B S hS)
    (ξa : uliftYoneda.{u + 1}.obj a ⟶ X.obj) (ξb : uliftYoneda.{u + 1}.obj b ⟶ X.obj) :
    ∃ (W : BigFppfOver B S hS)
      (g : uliftYoneda.{u + 1}.obj W ⟶
        pullback (pullback.snd ξa fi.hom) (pullback.snd ξb fi.hom))
      (w : W ⟶ a ⨯ b),
      (Space.etaleOnSite B S hS).relative uliftYoneda.{u + 1} g ∧
      (Space.surjectiveOnSite B S hS).relative uliftYoneda.{u + 1} g ∧
      LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map w) ∧
      g ≫ pullback.fst (pullback.snd ξa fi.hom) (pullback.snd ξb fi.hom) ≫
          pullback.fst ξa fi.hom = uliftYoneda.{u + 1}.map (w ≫ prod.fst) ∧
      g ≫ pullback.snd (pullback.snd ξa fi.hom) (pullback.snd ξb fi.hom) ≫
          pullback.fst ξb fi.hom = uliftYoneda.{u + 1}.map (w ≫ prod.snd) := by
  classical
  obtain ⟨Za, za, ρa, hzas, hzae, hρaY, hρa⟩ :=
    exists_atlas_pullback_fi B S hS fi hfi het a ξa
  obtain ⟨Zb, zb, ρb, hzbs, hzbe, hρbY, hρb⟩ :=
    exists_atlas_pullback_fi B S hS fi hfi het b ξb
  obtain ⟨W, si, hCI, hsq⟩ :=
    exists_closedImmersion_isPullback_of_isAffineFormal B S hS hXi
      (za ≫ pullback.snd ξa fi.hom) (zb ≫ pullback.snd ξb fi.hom)
  -- the two base-change squares assembling the chart
  have t1 : IsPullback
      (pullback.snd (pullback.snd ξa fi.hom) (zb ≫ pullback.snd ξb fi.hom))
      (pullback.fst (pullback.snd ξa fi.hom) (zb ≫ pullback.snd ξb fi.hom))
      (zb ≫ pullback.snd ξb fi.hom) (pullback.snd ξa fi.hom) :=
    (IsPullback.of_hasPullback _ _).flip
  have t2 : IsPullback (pullback.fst (pullback.snd ξa fi.hom) (pullback.snd ξb fi.hom))
      (pullback.snd (pullback.snd ξa fi.hom) (pullback.snd ξb fi.hom))
      (pullback.snd ξa fi.hom) (pullback.snd ξb fi.hom) := IsPullback.of_hasPullback _ _
  have hA := IsPullback.of_right' hsq.flip t1
  have hB := IsPullback.of_right'
    (IsPullback.of_hasPullback (pullback.snd ξa fi.hom) (zb ≫ pullback.snd ξb fi.hom)) t2
  -- the relative properties of the two base changes, and of their composite
  have hbce := MorphismProperty.relative_isStableUnderBaseChange
    (F := uliftYoneda.{u + 1} (C := BigFppfOver B S hS)) (Space.etaleOnSite B S hS)
  have hbcs := MorphismProperty.relative_isStableUnderBaseChange
    (F := uliftYoneda.{u + 1} (C := BigFppfOver B S hS)) (Space.surjectiveOnSite B S hS)
  refine ⟨W, _ ≫ _, si ≫ prod.map ρa ρb,
    MorphismProperty.comp_mem _ _ _ (hbce.of_isPullback hA.flip hzae)
      (hbce.of_isPullback hB.flip hzbe),
    MorphismProperty.comp_mem _ _ _ (hbcs.of_isPullback hA.flip hzas)
      (hbcs.of_isPullback hB.flip hzbs),
    ?_, ?_, ?_⟩
  · have _ : IsClosedImmersion ((BigFppfOver.toScheme B S hS).map si) := hCI
    have _ : Etale ((BigFppfOver.toScheme B S hS).map ρa) := hρa
    have _ : Etale ((BigFppfOver.toScheme B S hS).map ρb) := hρb
    have hprod : LocallyOfFiniteType
        ((BigFppfOver.toScheme B S hS).map (prod.map ρa ρb)) :=
      locallyOfFiniteType_prod_map B S hS ρa ρb inferInstance inferInstance
    have _ := hprod
    rw [Functor.map_comp]
    infer_instance
  · simp [← hρaY]
  · simp [← hρbY]

/-- **The chart of an atlas member is étale over the relative product itself.** Keep the
notation of `AlgebraicGeometry.FormalSpace.exists_member_chart`: `Nn` is the base change along
an atlas member `fi : Xi ⟶ X` of the relative product `E` of two scheme-valued points, `g` is
a chart of `Nn` by an object of the site which is étale after every represented base change,
and `n` is a monomorphism of `E` into a sheaf represented by an object of the site through
which the chart factors. Then the composite `h_W ⟶ Nn ⟶ E` is itself étale after every
represented base change.

The composite is *not* a composite of two such morphisms, `Nn ⟶ E` being representable only by
algebraic spaces. What makes the argument go through is the monomorphism: a represented base
change of the composite is the *scheme* fibre product, hence an object of the site, and it maps
to the base change of `Nn` by a base change of the chart; that base change of `Nn` is étale
over the point by the definition of an atlas, which is where the hypothesis on `fi` is used. -/
theorem relative_etale_comp_of_isPullback
    {X Xi : FppfSheaf B S hS} (fi : Xi ⟶ X)
    (hfi : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS fi.hom)
    (het : Space.HasPropertyULift.{u + 1} B S hS
      (fun _ _ g ↦ Space.IsEtaleULift.{u + 1} B S hS g.hom) fi.hom hfi)
    {a b : BigFppfOver B S hS}
    {ξa : uliftYoneda.{u + 1}.obj a ⟶ X.obj} {ξb : uliftYoneda.{u + 1}.obj b ⟶ X.obj}
    {Nn : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1)}
    {πX : Nn ⟶ Xi.obj} {πE : Nn ⟶ pullback ξa ξb}
    (hN : IsPullback πX πE fi.hom (pullback.fst ξa ξb ≫ ξa))
    {Wo : BigFppfOver B S hS} {g : uliftYoneda.{u + 1}.obj Wo ⟶ Nn}
    (hg : (Space.etaleOnSite B S hS).relative uliftYoneda.{u + 1} g)
    {No : BigFppfOver B S hS}
    (n : pullback ξa ξb ⟶ uliftYoneda.{u + 1}.obj No) [Mono n]
    {w : Wo ⟶ No} (hw : (g ≫ πE) ≫ n = uliftYoneda.{u + 1}.map w) :
    (Space.etaleOnSite B S hS).relative uliftYoneda.{u + 1} (g ≫ πE) := by
  classical
  refine MorphismProperty.relative.of_exists (fun {T} σ => ?_)
  obtain ⟨τ, hτ⟩ : ∃ τ : T ⟶ No, uliftYoneda.{u + 1}.map τ = σ ≫ n :=
    ⟨uliftYoneda.{u + 1}.preimage (σ ≫ n), uliftYoneda.{u + 1}.map_preimage _⟩
  have hbase : IsPullback
      (uliftYoneda.{u + 1}.map (pullback.fst w τ))
      (uliftYoneda.{u + 1}.map (pullback.snd w τ))
      (uliftYoneda.{u + 1}.map w) (uliftYoneda.{u + 1}.map τ) :=
    (IsPullback.of_hasPullback _ _).map uliftYoneda.{u + 1}
  rw [hτ, ← hw] at hbase
  have hRsq := isPullback_of_comp_mono n hbase
  have hDi : IsPullback
      (pullback.snd (σ ≫ pullback.fst ξa ξb ≫ ξa) fi.hom)
      (pullback.fst (σ ≫ pullback.fst ξa ξb ≫ ξa) fi.hom) fi.hom
      (σ ≫ pullback.fst ξa ξb ≫ ξa) := (IsPullback.of_hasPullback _ _).flip
  have hDsq := IsPullback.of_right' hDi hN
  have hφ := IsPullback.of_bot' hRsq hDsq
  have hbc := MorphismProperty.relative_isStableUnderBaseChange
    (F := uliftYoneda.{u + 1} (C := BigFppfOver B S hS)) (Space.etaleOnSite B S hS)
  have het' : Space.IsEtaleULift.{u + 1} B S hS
      (pullback.fst (σ ≫ pullback.fst ξa ξb ≫ ξa) fi.hom) :=
    het T (σ ≫ pullback.fst ξa ξb ≫ ξa)
  have hcomp := het' _ _ (hbc.of_isPullback hφ hg)
  rw [hDsq.lift_snd] at hcomp
  exact ⟨_, _, pullback.snd w τ, hRsq,
    MorphismProperty.of_relative_map (P := Space.etaleOnSite B S hS)
      (F := uliftYoneda.{u + 1}) hcomp⟩

/-- **The relative product of two scheme-valued points sits in the product of the site by a
monomorphism**, for the universe-lifted Yoneda embedding. This is the presheaf counterpart of
`AlgebraicGeometry.FormalSpace.exists_mono_toProd_pullback`. -/
theorem exists_mono_toProd_pullback_uliftYoneda [HasBinaryProducts (BigFppfOver B S hS)]
    (a b : BigFppfOver B S hS) {Xo : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1)}
    (ξa : uliftYoneda.{u + 1}.obj a ⟶ Xo) (ξb : uliftYoneda.{u + 1}.obj b ⟶ Xo) :
    ∃ n : pullback ξa ξb ⟶ uliftYoneda.{u + 1}.obj (a ⨯ b),
      Mono n ∧
      n ≫ uliftYoneda.{u + 1}.map prod.fst = pullback.fst ξa ξb ∧
      n ≫ uliftYoneda.{u + 1}.map prod.snd = pullback.snd ξa ξb := by
  let Y := uliftYoneda.{u + 1} (C := BigFppfOver B S hS)
  let e : Y.obj (a ⨯ b) ≅ Y.obj a ⨯ Y.obj b := PreservesLimitPair.iso Y a b
  have he : e.hom = prodComparison Y a b := rfl
  have hmono : Mono (prod.lift (pullback.fst ξa ξb) (pullback.snd ξa ξb)) :=
    ⟨fun g h hgh => pullback.hom_ext (by simpa using hgh =≫ prod.fst)
      (by simpa using hgh =≫ prod.snd)⟩
  have hfst : e.inv ≫ Y.map prod.fst = prod.fst := by
    rw [← prodComparison_fst Y a b, ← he, Iso.inv_hom_id_assoc]
  have hsnd : e.inv ≫ Y.map prod.snd = prod.snd := by
    rw [← prodComparison_snd Y a b, ← he, Iso.inv_hom_id_assoc]
  refine ⟨prod.lift (pullback.fst ξa ξb) (pullback.snd ξa ξb) ≫ e.inv, inferInstance, ?_, ?_⟩
  · rw [Category.assoc, hfst, prod.lift_fst]
  · rw [Category.assoc, hsnd, prod.lift_snd]

/-- **The chart of one atlas member, read over the relative product.** This packages
`AlgebraicGeometry.FormalSpace.exists_member_chart` with the cartesian square identifying the
base change of the relative product along the atlas member, and with the étaleness of the
composite chart supplied by
`AlgebraicGeometry.FormalSpace.relative_etale_comp_of_isPullback`. -/
theorem exists_member_chart_over_pullback [HasBinaryProducts (BigFppfOver B S hS)]
    {X Xi : FppfSheaf B S hS} (fi : Xi ⟶ X)
    (hXi : IsAffineFormalAlgebraicSpace B S hS Xi)
    (hfi : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS fi.hom)
    (het : Space.HasPropertyULift.{u + 1} B S hS
      (fun _ _ g ↦ Space.IsEtaleULift.{u + 1} B S hS g.hom) fi.hom hfi)
    (a b : BigFppfOver B S hS)
    (ξa : uliftYoneda.{u + 1}.obj a ⟶ X.obj) (ξb : uliftYoneda.{u + 1}.obj b ⟶ X.obj)
    (n : pullback ξa ξb ⟶ uliftYoneda.{u + 1}.obj (a ⨯ b)) [Mono n]
    (hna : n ≫ uliftYoneda.{u + 1}.map prod.fst = pullback.fst ξa ξb)
    (hnb : n ≫ uliftYoneda.{u + 1}.map prod.snd = pullback.snd ξa ξb) :
    ∃ (Wo : BigFppfOver B S hS) (Nn : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1))
      (πX : Nn ⟶ Xi.obj) (πE : Nn ⟶ pullback ξa ξb)
      (g : uliftYoneda.{u + 1}.obj Wo ⟶ Nn) (w : Wo ⟶ a ⨯ b),
      IsPullback πX πE fi.hom (pullback.fst ξa ξb ≫ ξa) ∧
      (Space.etaleOnSite B S hS).relative uliftYoneda.{u + 1} (g ≫ πE) ∧
      (Space.surjectiveOnSite B S hS).relative uliftYoneda.{u + 1} g ∧
      LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map w) ∧
      (g ≫ πE) ≫ n = uliftYoneda.{u + 1}.map w := by
  obtain ⟨Wo, g, w, hge, hgs, hlft, hwa, hwb⟩ :=
    exists_member_chart B S hS fi hXi hfi het a b ξa ξb
  have hcond : (pullback.fst (pullback.snd ξa fi.hom) (pullback.snd ξb fi.hom) ≫
        pullback.fst ξa fi.hom) ≫ ξa =
      (pullback.snd (pullback.snd ξa fi.hom) (pullback.snd ξb fi.hom) ≫
        pullback.fst ξb fi.hom) ≫ ξb := by
    rw [Category.assoc, Category.assoc, pullback.condition, pullback.condition,
      ← Category.assoc, ← Category.assoc, pullback.condition]
  have hT : IsLimit (BinaryFan.mk (uliftYoneda.{u + 1}.map (prod.fst : a ⨯ b ⟶ a))
      (uliftYoneda.{u + 1}.map (prod.snd : a ⨯ b ⟶ b))) :=
    mapIsLimitOfPreservesOfIsLimit uliftYoneda.{u + 1} _ _ (prodIsProd a b)
  have hfac : (g ≫ pullback.lift _ _ hcond) ≫ n = uliftYoneda.{u + 1}.map w := by
    refine BinaryFan.IsLimit.hom_ext hT ?_ ?_
    · simp only [BinaryFan.mk_fst, Category.assoc, hna, ← Functor.map_comp]
      rw [pullback.lift_fst]
      exact hwa
    · simp only [BinaryFan.mk_snd, Category.assoc, hnb, ← Functor.map_comp]
      rw [pullback.lift_snd]
      exact hwb
  have hpb := isPullback_of_pullback_snd_snd ξa ξb fi.hom _
    (pullback.lift_fst _ _ hcond) (pullback.lift_snd _ _ hcond)
  exact ⟨Wo, _, _, pullback.lift _ _ hcond, g, w, hpb,
    relative_etale_comp_of_isPullback B S hS fi hfi het hpb hge n hfac, hgs, hlft, hfac⟩

/-- **Every point of a test object has its image in the ambient product covered by some atlas
member.** For `X` an fppf sheaf on the big fppf site of `S` with a family `{Xi ⟶ X}` whose
members jointly cover it fppf-locally, and for the member charts of
`AlgebraicGeometry.FormalSpace.exists_member_chart_over_pullback`, the image in the ambient
object `No` of any point of any object `U` of the site carrying a section of the relative
product lies in the range of one of the members.

This is the joint surjectivity which the point-indexed refinement of the family needs. The
covering sieve of `U` produced by the family is refined by an fppf covering of schemes; over a
member of that covering the section lifts to one of the `Xi`, hence to the base change of the
relative product along that member, and the chart of that base change is surjective, so a
point of it lies over the given point. -/
theorem exists_index_mem_range_of_atlas
    {X : FppfSheaf B S hS} {I : Type (u + 1)} {Xi : I → FppfSheaf B S hS} (f : ∀ i, Xi i ⟶ X)
    (hsieve : ∀ (T : BigFppfOver B S hS) (x : X.obj.obj (Opposite.op T)),
      (⨆ i, Presheaf.imageSieve (f i).hom x) ∈ BigFppfOver.topology B S hS T)
    {a b : BigFppfOver B S hS}
    {ξa : uliftYoneda.{u + 1}.obj a ⟶ X.obj} {ξb : uliftYoneda.{u + 1}.obj b ⟶ X.obj}
    {No : BigFppfOver B S hS}
    (n : pullback ξa ξb ⟶ uliftYoneda.{u + 1}.obj No)
    {Wm : I → BigFppfOver B S hS}
    {Nm : I → ((BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1))}
    {πXm : ∀ i, Nm i ⟶ (Xi i).obj} {πEm : ∀ i, Nm i ⟶ pullback ξa ξb}
    {gm : ∀ i, uliftYoneda.{u + 1}.obj (Wm i) ⟶ Nm i} {wm : ∀ i, Wm i ⟶ No}
    (hNm : ∀ i, IsPullback (πXm i) (πEm i) (f i).hom (pullback.fst ξa ξb ≫ ξa))
    (hgSm : ∀ i, (Space.surjectiveOnSite B S hS).relative uliftYoneda.{u + 1} (gm i))
    (hfacm : ∀ i, (gm i ≫ πEm i) ≫ n = uliftYoneda.{u + 1}.map (wm i))
    (U : BigFppfOver B S hS) (σ : uliftYoneda.{u + 1}.obj U ⟶ pullback ξa ξb)
    {τ : U ⟶ No} (hτ : uliftYoneda.{u + 1}.map τ = σ ≫ n)
    (t : (BigFppfOver.toScheme B S hS).obj U) :
    ∃ i, (BigFppfOver.toScheme B S hS).map τ t ∈
      Set.range ((BigFppfOver.toScheme B S hS).map (wm i)) := by
  classical
  have hmem := hsieve U (uliftYonedaEquiv (σ ≫ pullback.fst ξa ξb ≫ ξa))
  rw [GrothendieckTopology.mem_over_iff] at hmem
  obtain ⟨E, hE, hER⟩ := Space.exists_covering_refining_sieve B hmem
  have hEF := B.isFppfCovering_of_isCovering hE
  rw [AlgebraicGeometry.IsFppfCovering, Precoverage.mem_comap_iff,
    PreZeroHypercover.presieve₀, Presieve.map_ofArrows,
    Scheme.fppfPrecoverage, Scheme.ofArrows_mem_precoverage_iff] at hEF
  obtain ⟨j, y, hy⟩ := hEF.1 t
  have hb := (Sieve.overEquiv_iff _ _).mp (hER _ _ ⟨j⟩)
  change (⨆ i, Presheaf.imageSieve (f i).hom
    (uliftYonedaEquiv (σ ≫ pullback.fst ξa ξb ≫ ξa)))
      (Over.homMk (E.f j) : Over.mk (E.f j ≫ U.hom) ⟶ U) at hb
  simp only [iSup, Sieve.sSup_apply, Set.mem_range] at hb
  obtain ⟨-, ⟨i, rfl⟩, z, hz⟩ := hb
  have hw : (uliftYonedaEquiv.symm z : uliftYoneda.{u + 1}.obj (Over.mk (E.f j ≫ U.hom)) ⟶
        (Xi i).obj) ≫ (f i).hom =
      (uliftYoneda.{u + 1}.map (Over.homMk (E.f j) : Over.mk (E.f j ≫ U.hom) ⟶ U) ≫ σ) ≫
        (pullback.fst ξa ξb ≫ ξa) := by
    apply uliftYonedaEquiv.injective
    rw [uliftYonedaEquiv_comp, Equiv.apply_symm_apply, Category.assoc]
    exact hz.trans (uliftYonedaEquiv_naturality.{u + 1} _ _)
  have hs'E : (hNm i).lift _ _ hw ≫ πEm i =
      uliftYoneda.{u + 1}.map (Over.homMk (E.f j) : Over.mk (E.f j ≫ U.hom) ⟶ U) ≫ σ :=
    (hNm i).lift_snd _ _ hw
  have hsq := (hgSm i).rep.isPullback ((hNm i).lift _ _ hw)
  have hsurj : Surjective ((BigFppfOver.toScheme B S hS).map
      ((hgSm i).rep.snd ((hNm i).lift _ _ hw))) := (hgSm i).property_snd _
  obtain ⟨y', hy'⟩ := hsurj.1 y
  have hcompat : (hgSm i).rep.fst' ((hNm i).lift _ _ hw) ≫ wm i =
      (hgSm i).rep.snd ((hNm i).lift _ _ hw) ≫
        (Over.homMk (E.f j) : Over.mk (E.f j ≫ U.hom) ⟶ U) ≫ τ := by
    apply uliftYoneda.{u + 1}.map_injective
    rw [Functor.map_comp, (hgSm i).rep.map_fst', ← hfacm i, Functor.map_comp,
      Functor.map_comp, hτ]
    simp only [Category.assoc]
    rw [← Category.assoc ((hgSm i).rep.fst ((hNm i).lift _ _ hw)) (gm i), hsq.w]
    simp only [Category.assoc]
    rw [reassoc_of% hs'E]
  refine ⟨i, (BigFppfOver.toScheme B S hS).map
    ((hgSm i).rep.fst' ((hNm i).lift _ _ hw)) y', ?_⟩
  rw [← Scheme.Hom.comp_apply, ← Functor.map_comp, hcompat, Functor.map_comp,
    Functor.map_comp, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hy']
  exact congrArg ((BigFppfOver.toScheme B S hS).map τ) hy

/-- **The relative product of two scheme-valued points of a formal algebraic space is
represented by an object of the site, locally of finite type over the product of the two
points.** This is the geometric content of **Stacks 0AIP**: the representability assertion is
the cartesian square, and the local finiteness assertions are the local finite type of the
morphism `Po ⟶ a ⨯ b` of the site which the two projections assemble.

The chart of the relative product is built below and handed to
`AlgebraicGeometry.FormalSpace.exists_locallyOfFiniteType_of_mono_of_chart`, which returns both
the representing object and that local finite type. -/
theorem exists_isPullback_locallyOfFiniteType_of_isFormalAlgebraicSpace
    [HasBinaryProducts (BigFppfOver B S hS)]
    {X : FppfSheaf B S hS} (hX : IsFormalAlgebraicSpace B S hS X)
    (a b : BigFppfOver B S hS)
    (ξa : uliftYoneda.{u + 1}.obj a ⟶ X.obj) (ξb : uliftYoneda.{u + 1}.obj b ⟶ X.obj) :
    ∃ (Po : BigFppfOver B S hS) (pa : Po ⟶ a) (pb : Po ⟶ b),
      IsPullback (uliftYoneda.{u + 1}.map pa) (uliftYoneda.{u + 1}.map pb) ξa ξb ∧
      LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map (prod.lift pa pb)) := by
  classical
  have hoiAff : ∀ {Xp : Scheme.{u}} (U : Xp.affineOpens),
      AlgebraicGeometry.IsOpenImmersion U.1.ι := fun U => inferInstance
  let : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
  obtain ⟨I, Xi, f, hXiaff, hfet, hcover⟩ := hX.2
  obtain ⟨n, hnmono, hna, hnb⟩ := exists_mono_toProd_pullback_uliftYoneda B S hS a b ξa ξb
  have := hnmono
  have hEsheaf : Presheaf.IsSheaf (BigFppfOver.topology B S hS) (pullback ξa ξb) := by
    have h1 := X.property
    have h2 := (Space.isAlgebraicSpaceULift_uliftYoneda.{u + 1} B S hS a).isSheaf
    have h3 := (Space.isAlgebraicSpaceULift_uliftYoneda.{u + 1} B S hS b).isSheaf
    refine ObjectProperty.prop_of_isLimit
      (Presheaf.IsSheaf (BigFppfOver.topology B S hS) (A := Type (u + 1)))
      (pullback.isLimit ξa ξb) ?_
    rintro (_ | _ | _) <;> assumption
  -- the member charts
  have hmem : ∀ i : I, ∃ (Wo : BigFppfOver B S hS)
      (Nn : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1))
      (πX : Nn ⟶ (Xi i).obj) (πE : Nn ⟶ pullback ξa ξb)
      (g : uliftYoneda.{u + 1}.obj Wo ⟶ Nn) (w : Wo ⟶ a ⨯ b),
      IsPullback πX πE (f i).hom (pullback.fst ξa ξb ≫ ξa) ∧
      (Space.etaleOnSite B S hS).relative uliftYoneda.{u + 1} (g ≫ πE) ∧
      (Space.surjectiveOnSite B S hS).relative uliftYoneda.{u + 1} g ∧
      LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map w) ∧
      (g ≫ πE) ≫ n = uliftYoneda.{u + 1}.map w := by
    intro i
    obtain ⟨hfi, hei⟩ := hfet i
    exact exists_member_chart_over_pullback B S hS (f i) (hXiaff i) hfi hei a b ξa ξb n hna hnb
  choose Wm Nm πXm πEm gm wm hNm hgEm hgSm hlftm hfacm using hmem
  -- the point-indexed refinement
  have hgood : ∀ (U : BigFppfOver B S hS) (σ : uliftYoneda.{u + 1}.obj U ⟶ pullback ξa ξb)
      (τ : U ⟶ a ⨯ b), uliftYoneda.{u + 1}.map τ = σ ≫ n →
      ∀ t : (BigFppfOver.toScheme B S hS).obj U,
      ∃ i, (BigFppfOver.toScheme B S hS).map τ t ∈
        Set.range ((BigFppfOver.toScheme B S hS).map (wm i)) :=
    fun U σ τ hτ t => exists_index_mem_range_of_atlas B S hS f
      (fun T x => family_imageSieve_mem (BigFppfOver.topology B S hS) Xi X f hcover T x)
      n hNm hgSm hfacm U σ hτ t
  have hchoice : ∀ x : {x : (BigFppfOver.toScheme B S hS).obj (a ⨯ b) //
      ∃ i : I, x ∈ Set.range ((BigFppfOver.toScheme B S hS).map (wm i))},
      ∃ (i : I) (A : ((BigFppfOver.toScheme B S hS).obj (Wm i)).affineOpens) (y : A.1),
        (BigFppfOver.toScheme B S hS).map (wm i) (A.1.ι y) = x.1 := by
    intro x
    obtain ⟨i, y, hy⟩ := x.2
    obtain ⟨A, hA, hyA, -⟩ :=
      exists_isAffineOpen_mem_and_subset (X := (BigFppfOver.toScheme B S hS).obj (Wm i))
        (x := y) (U := ⊤) trivial
    refine ⟨i, ⟨A, hA⟩, ⟨y, hyA⟩, ?_⟩
    simpa using hy
  choose idx Aff pt hpt using hchoice
  have hfam : ∀ x : {x : (BigFppfOver.toScheme B S hS).obj (a ⨯ b) //
      ∃ i : I, x ∈ Set.range ((BigFppfOver.toScheme B S hS).map (wm i))},
      ∃ (Vx : BigFppfOver B S hS) (kx : Vx ⟶ Wm (idx x)),
        IsOpenImmersion ((BigFppfOver.toScheme B S hS).map kx) ∧
        ((BigFppfOver.toScheme B S hS).obj Vx).size ≤
          2 ^ ((BigFppfOver.toScheme B S hS).obj (a ⨯ b)).size ∧
        ∃ p : (BigFppfOver.toScheme B S hS).obj Vx,
          (BigFppfOver.toScheme B S hS).map (kx ≫ wm (idx x)) p = x.1 := by
    intro x
    have : IsAffine ((Aff x).1.toScheme) := (Aff x).2
    have := hlftm (idx x)
    have hoi := hoiAff (Aff x)
    refine ⟨Space.openSubobject B S hS (Wm (idx x)) (Aff x).1.ι hoi,
      Space.openSubobjectHom B S hS (Wm (idx x)) (Aff x).1.ι hoi, ?_, ?_, ?_⟩
    · rw [Space.toScheme_map_openSubobjectHom B S hS (Wm (idx x)) (Aff x).1.ι hoi]
      exact hoi
    · show ((Aff x).1.toScheme).size ≤ _
      exact (Scheme.size_le_of_locallyOfFiniteType
        ((Aff x).1.ι ≫ (BigFppfOver.toScheme B S hS).map (wm (idx x)))).trans
        (Cardinal.cantor _).le
    · refine ⟨pt x, ?_⟩
      rw [Functor.map_comp,
        Space.toScheme_map_openSubobjectHom B S hS (Wm (idx x)) (Aff x).1.ι hoi]
      exact hpt x
  choose V kc hkcopen hsizeV hptV using hfam
  -- the properties of the refined family
  have hgxe : ∀ x, (Space.etaleOnSite B S hS).relative uliftYoneda.{u + 1}
      (uliftYoneda.{u + 1}.map (kc x) ≫ (gm (idx x) ≫ πEm (idx x))) := by
    intro x
    refine MorphismProperty.comp_mem _ _ _ ?_ (hgEm (idx x))
    have := hkcopen x
    exact Space.relative_uliftYoneda_map B S hS _ (kc x) inferInstance
  have hμ : (2 : Cardinal.{u}) ^ ((BigFppfOver.toScheme B S hS).obj (a ⨯ b)).size <
      B.cutoff := B.cutoff_isStrongPrelimit (a ⨯ b).left.property
  have hGPcard : Cardinal.mk {x : (BigFppfOver.toScheme B S hS).obj (a ⨯ b) //
      ∃ i : I, x ∈ Set.range ((BigFppfOver.toScheme B S hS).map (wm i))} ≤
      2 ^ ((BigFppfOver.toScheme B S hS).obj (a ⨯ b)).size :=
    (Cardinal.mk_subtype_le _).trans (mk_scheme_le_two_power_size _)
  obtain ⟨Wc, kk, q, hkq, hopenk, hcovk, hqrep⟩ :=
    exists_chart_of_size_le B S hS (X := (⟨pullback ξa ξb, hEsheaf⟩ : FppfSheaf B S hS))
      V (fun x => uliftYoneda.{u + 1}.map (kc x) ≫ (gm (idx x) ≫ πEm (idx x)))
      (fun x => (hgxe x).rep) hμ hGPcard hsizeV
  obtain ⟨wc, hwc⟩ : ∃ wc : Wc ⟶ a ⨯ b, uliftYoneda.{u + 1}.map wc = q ≫ n :=
    ⟨uliftYoneda.{u + 1}.preimage (q ≫ n), uliftYoneda.{u + 1}.map_preimage _⟩
  have hkkwc : ∀ x, kk x ≫ wc = kc x ≫ wm (idx x) := by
    intro x
    apply uliftYoneda.{u + 1}.map_injective
    simp only [Functor.map_comp]
    rw [hwc, ← Category.assoc, hkq x, Category.assoc, hfacm (idx x)]
  -- local finite type of the glued morphism
  let : IsZariskiLocalAtSource (@AlgebraicGeometry.LocallyOfFiniteType.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtSource
      (P := @AlgebraicGeometry.LocallyOfFiniteType.{u})
  have hlftwc : LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map wc) := by
    refine IsZariskiLocalAtSource.of_openCover
      (P := @AlgebraicGeometry.LocallyOfFiniteType.{u})
      { I₀ := _
        X := fun x => (BigFppfOver.toScheme B S hS).obj (V x)
        f := fun x => (BigFppfOver.toScheme B S hS).map (kk x)
        mem₀ := by
          rw [Scheme.presieve₀_mem_precoverage_iff]
          exact ⟨hcovk, hopenk⟩ } ?_
    intro x
    have := hkcopen x
    have := hlftm (idx x)
    show LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map (kk x) ≫
      (BigFppfOver.toScheme B S hS).map wc)
    rw [← Functor.map_comp, hkkwc x, Functor.map_comp]
    infer_instance
  -- local surjectivity of the glued chart
  have hqsurj : Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS) q := by
    refine ⟨fun {U} s => ?_⟩
    obtain ⟨σ, hσ⟩ : ∃ σ : uliftYoneda.{u + 1}.obj U ⟶ pullback ξa ξb,
        uliftYonedaEquiv σ = s := ⟨uliftYonedaEquiv.symm s, Equiv.apply_symm_apply _ _⟩
    obtain ⟨τ, hτ⟩ : ∃ τ : U ⟶ a ⨯ b, uliftYoneda.{u + 1}.map τ = σ ≫ n :=
      ⟨uliftYoneda.{u + 1}.preimage (σ ≫ n), uliftYoneda.{u + 1}.map_preimage _⟩
    have hwx : ∀ x, (uliftYoneda.{u + 1}.map (kc x) ≫ (gm (idx x) ≫ πEm (idx x))) ≫ n =
        uliftYoneda.{u + 1}.map (kc x ≫ wm (idx x)) := by
      intro x
      rw [Category.assoc, hfacm (idx x), Functor.map_comp]
    have hsq : ∀ x, IsPullback
        (uliftYoneda.{u + 1}.map (pullback.fst (kc x ≫ wm (idx x)) τ))
        (uliftYoneda.{u + 1}.map (pullback.snd (kc x ≫ wm (idx x)) τ))
        (uliftYoneda.{u + 1}.map (kc x) ≫ (gm (idx x) ≫ πEm (idx x))) σ := by
      intro x
      refine isPullback_of_comp_mono n ?_
      have h := (IsPullback.of_hasPullback (kc x ≫ wm (idx x)) τ).map uliftYoneda.{u + 1}
      rw [hτ, ← hwx x] at h
      exact h
    have hret : ∀ x, Etale (pullback.snd (kc x ≫ wm (idx x)) τ).left.hom := fun x =>
      (hgxe x).property σ _ _ (hsq x)
    have hptcov : ∀ t : (BigFppfOver.toScheme B S hS).obj U, ∃ x,
        t ∈ Set.range ((BigFppfOver.toScheme B S hS).map
          (pullback.snd (kc x ≫ wm (idx x)) τ)) := by
      intro t
      obtain ⟨i, hi⟩ := hgood U σ τ hτ t
      obtain ⟨p, hp⟩ := hptV ⟨(BigFppfOver.toScheme B S hS).map τ t, ⟨i, hi⟩⟩
      obtain ⟨z, hz1, hz2⟩ := Scheme.Pullback.exists_preimage_pullback
        (f := (BigFppfOver.toScheme B S hS).map
          (kc ⟨(BigFppfOver.toScheme B S hS).map τ t, ⟨i, hi⟩⟩ ≫
            wm (idx ⟨(BigFppfOver.toScheme B S hS).map τ t, ⟨i, hi⟩⟩)))
        (g := (BigFppfOver.toScheme B S hS).map τ) p t hp
      refine ⟨⟨(BigFppfOver.toScheme B S hS).map τ t, ⟨i, hi⟩⟩,
        ((IsPullback.of_hasPullback _ τ).map (BigFppfOver.toScheme B S hS)).isoPullback.inv z,
        ?_⟩
      rw [← Scheme.Hom.comp_apply,
        ((IsPullback.of_hasPullback _ τ).map
          (BigFppfOver.toScheme B S hS)).isoPullback_inv_snd]
      exact hz2
    have hmemsieve := fppf_ofArrows_mem B S hS
      (fun x => pullback (kc x ≫ wm (idx x)) τ)
      (fun x => pullback.snd (kc x ≫ wm (idx x)) τ)
      (fun x => by have := hret x; infer_instance)
      (fun x => by have := hret x; infer_instance) hptcov
    refine (BigFppfOver.topology B S hS).superset_covering ?_ hmemsieve
    rintro V' gg ⟨Z, h, g', ⟨x⟩, rfl⟩
    refine (Presheaf.imageSieve q s).downward_closed ?_ h
    refine ⟨uliftYonedaEquiv (uliftYoneda.{u + 1}.map
      (pullback.fst (kc x ≫ wm (idx x)) τ ≫ kk x)), ?_⟩
    rw [← uliftYonedaEquiv_comp, ← hσ, uliftYonedaEquiv_naturality]
    congr 1
    rw [Functor.map_comp, Category.assoc, hkq x]
    exact (hsq x).w
  obtain ⟨Po, pp, e, hfac, hlftp⟩ :=
    exists_locallyOfFiniteType_of_mono_of_chart B S hS hEsheaf n hnmono wc q hwc.symm hlftwc
      (relative_surjective_of_locallySurjective B S hS q hqrep hqsurj)
      (etale_of_openCover B S hS V kk hopenk hcovk q hqrep
        (fun x => by rw [hkq x]; exact hgxe x))
  have h1 : uliftYoneda.{u + 1}.map (pp ≫ prod.fst) = e.hom ≫ pullback.fst ξa ξb := by
    rw [Functor.map_comp, ← hfac, Category.assoc, hna]
  have h2 : uliftYoneda.{u + 1}.map (pp ≫ prod.snd) = e.hom ≫ pullback.snd ξa ξb := by
    rw [Functor.map_comp, ← hfac, Category.assoc, hnb]
  refine ⟨Po, pp ≫ prod.fst, pp ≫ prod.snd, ?_, ?_⟩
  · refine IsPullback.of_iso_pullback ⟨?_⟩ e h1.symm h2.symm
    rw [h1, h2, Category.assoc, Category.assoc, pullback.condition]
  · have hp : prod.lift (pp ≫ prod.fst) (pp ≫ prod.snd) = pp := by
      refine prod.hom_ext ?_ ?_ <;> simp
    rw [hp]
    exact hlftp

/-- **The relative product of two scheme-valued points of a formal algebraic space is
represented by an object of the site.** This is the representability half of
`AlgebraicGeometry.FormalSpace.exists_isPullback_locallyOfFiniteType_of_isFormalAlgebraicSpace`,
and is the geometric content of the representability assertion of **Stacks 0AIP**. -/
theorem essImage_pullback_of_isFormalAlgebraicSpace
    [HasBinaryProducts (BigFppfOver B S hS)]
    {X : FppfSheaf B S hS} (hX : IsFormalAlgebraicSpace B S hS X)
    (a b : BigFppfOver B S hS)
    (ξa : uliftYoneda.{u + 1}.obj a ⟶ X.obj) (ξb : uliftYoneda.{u + 1}.obj b ⟶ X.obj) :
    uliftYoneda.{u + 1}.essImage (pullback ξa ξb) :=
  let ⟨Po, _, _, hsq, _⟩ :=
    exists_isPullback_locallyOfFiniteType_of_isFormalAlgebraicSpace B S hS hX a b ξa ξb
  ⟨Po, ⟨hsq.isoPullback⟩⟩

/-- **The representability assertion of Stacks 0AIP, for an arbitrary formal algebraic
space.** Every morphism to a formal algebraic space from a sheaf represented by an object of
the big fppf site of `S` is representable by objects of the site. -/
theorem hasRepresentableRelativeProducts_of_isFormalAlgebraicSpace
    {X : FppfSheaf B S hS} (hX : IsFormalAlgebraicSpace B S hS X) :
    HasRepresentableRelativeProducts B S hS X := by
  classical
  let : HasBinaryProducts (BigFppfOver B S hS) :=
    hasBinaryProducts_of_hasTerminal_and_pullbacks _
  let J := BigFppfOver.topology B S hS
  let F := Sheaf.sheafifiedYoneda J
  let K := sheafToPresheaf J (Type (u + 1))
  let : J.Subcanonical := bigFppfOver_subcanonical B S hS
  let : F.Full := (Sheaf.fullyFaithfulSheafifiedYoneda J).full
  let : F.Faithful := (Sheaf.fullyFaithfulSheafifiedYoneda J).faithful
  let gl : F ⋙ K ≅ uliftYoneda.{u + 1} := sheafifiedYonedaPresheafIso B S hS
  have hpre : ∀ {c : BigFppfOver B S hS} (ξ : uliftYoneda.{u + 1}.obj c ⟶ X.obj),
      uliftYoneda.{u + 1}.relativelyRepresentable ξ := by
    intro c ξ d h
    obtain ⟨P, ⟨e⟩⟩ := essImage_pullback_of_isFormalAlgebraicSpace B S hS hX c d ξ h
    refine ⟨P, uliftYoneda.{u + 1}.preimage (e.hom ≫ pullback.snd ξ h),
      e.hom ≫ pullback.fst ξ h, ?_⟩
    refine IsPullback.of_iso_pullback ⟨?_⟩ e rfl
      ((uliftYoneda.{u + 1}).map_preimage _).symm
    rw [(uliftYoneda.{u + 1}).map_preimage, Category.assoc, Category.assoc,
      pullback.condition]
  intro c g
  have hK : uliftYoneda.{u + 1}.relativelyRepresentable (K.map g) := by
    have h0 := hpre (gl.inv.app c ≫ K.map g)
    have hcomp : K.map g = gl.hom.app c ≫ gl.inv.app c ≫ K.map g := by
      rw [← Category.assoc, Iso.hom_inv_id_app, Category.id_comp]
    rw [hcomp]
    exact MorphismProperty.RespectsIso.precomp _ (gl.hom.app c) _ h0
  have h1 : (⊤ : MorphismProperty (BigFppfOver B S hS)).relative uliftYoneda.{u + 1}
      (K.map g) := ⟨hK, fun _ _ _ _ _ _ => trivial⟩
  exact ((Space.relative_comp_map_iff F K ⊤ g).mp
    (relative_of_natIso gl.symm ⊤ (K.map g) h1)).rep

/-- **Stacks 0AIQ for an arbitrary formal algebraic space target.** A morphism of fppf sheaves
whose source is an algebraic space over `S` and whose target is a formal algebraic space over `S`
is representable by algebraic spaces.

This carries nothing. `isRepresentableByAlgebraicSpacesULift_of_isAlgebraicSpaceULift`
(`MapsFromAlgebraicSpace`) states the implication with the target's representable relative
products as a hypothesis, and that hypothesis is the theorem above -- the representability
assertion of **Stacks 0AIP**. It is stated here rather than beside that theorem because
`MapsFromAlgebraicSpace` lies in this module's import closure and not conversely, so the
discharge can only be written downstream. -/
@[stacks 0AIQ "for an arbitrary formal algebraic space target, carrying nothing: the \
representable-relative-products hypothesis is discharged by this module's own Stacks 0AIP"]
theorem isRepresentableByAlgebraicSpacesULift_of_isAlgebraicSpaceULift_of_isFormal
    {X Y : FppfSheaf B S hS} (f : X ⟶ Y)
    (hX : Space.IsAlgebraicSpaceULift.{u + 1} B S hS X.obj)
    (hY : IsFormalAlgebraicSpace B S hS Y) :
    Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS f.hom :=
  isRepresentableByAlgebraicSpacesULift_of_isAlgebraicSpaceULift B S hS f hX
    (hasRepresentableRelativeProducts_of_isFormalAlgebraicSpace B S hS hY)


/-- **Stacks 0AIP, representability, for an arbitrary formal algebraic space:** the absolute
diagonal of a formal algebraic space over `S` is representable by objects of the big fppf site
of `S`.

The diagonal is representable exactly when every morphism into the space from a sheaf
represented by an object of the site is, and that is
`AlgebraicGeometry.FormalSpace.hasRepresentableRelativeProducts_of_isFormalAlgebraicSpace`. -/
@[stacks 0AIP "representable by schemes, for an arbitrary formal algebraic space"]
theorem relativelyRepresentable_diag_of_isFormalAlgebraicSpace
    {X : FppfSheaf B S hS} (hX : IsFormalAlgebraicSpace B S hS X) :
    (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).relativelyRepresentable
      (diag X) := by
  let : HasBinaryProducts (BigFppfOver B S hS) :=
    hasBinaryProducts_of_hasTerminal_and_pullbacks _
  let : (BigFppfOver.topology B S hS).Subcanonical := bigFppfOver_subcanonical B S hS
  let : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).Full :=
    (Sheaf.fullyFaithfulSheafifiedYoneda (BigFppfOver.topology B S hS)).full
  let : PreservesLimitsOfShape (Discrete WalkingPair)
      (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)) :=
    preservesLimitsOfShape_of_natIso
      (Sheaf.sheafifiedYonedaIsoUliftYoneda' (BigFppfOver.topology B S hS)).symm
  let : PreservesLimitsOfShape WalkingCospan
      (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)) :=
    preservesLimitsOfShape_of_natIso
      (Sheaf.sheafifiedYonedaIsoUliftYoneda' (BigFppfOver.topology B S hS)).symm
  exact Functor.relativelyRepresentable.diag_of_map_from_obj
    (hasRepresentableRelativeProducts_of_isFormalAlgebraicSpace B S hS hX)

/-- **Stacks 0AN2, representability, for a morphism whose source is an *arbitrary* formal
algebraic space:** the relative diagonal of a morphism of fppf sheaves out of a formal
algebraic space is representable by objects of the big fppf site of `S`.

This discharges the hypothesis of
`AlgebraicGeometry.FormalSpace.relativelyRepresentable_pullback_diagonal`, the relative
diagonal being a base change of the absolute one. -/
@[stacks 0AN2 "representable by schemes, for a morphism whose source is an arbitrary formal \
algebraic space"]
theorem relativelyRepresentable_pullback_diagonal_of_isFormalAlgebraicSpace
    {X Y : FppfSheaf B S hS} (f : X ⟶ Y) (hX : IsFormalAlgebraicSpace B S hS X) :
    (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).relativelyRepresentable
      (pullback.diagonal f) :=
  relativelyRepresentable_pullback_diagonal B S hS f
    (relativelyRepresentable_diag_of_isFormalAlgebraicSpace B S hS hX)

/-- **The local finite type assertion of Stacks 0AIP, for an arbitrary formal algebraic space,
read on underlying presheaves.** Every represented base change of the absolute diagonal of the
presheaf underlying a formal algebraic space over `S` is a morphism of the site which is locally
of finite type.

A scheme-valued point `g` of `X ⨯ X` is a pair of scheme-valued points of `X`; their relative
product is represented by an object `Po` of the site which is locally of finite type over
`c ⨯ c`, by
`AlgebraicGeometry.FormalSpace.exists_isPullback_locallyOfFiniteType_of_isFormalAlgebraicSpace`,
and the base change of the diagonal along `g` is the base change of that morphism along
`diag c`, by `AlgebraicGeometry.FormalSpace.isPullback_diag_of_isPullback_prodLift`. Local
finite type is stable under base change, and the structure functor to schemes preserves fibre
products, so the base change is locally of finite type as a morphism of schemes. -/
theorem relative_locallyOfFiniteType_diag_hom_of_isFormalAlgebraicSpace
    {X : FppfSheaf B S hS} (hX : IsFormalAlgebraicSpace B S hS X) :
    (MorphismProperty.inverseImage
      (@AlgebraicGeometry.LocallyOfFiniteType.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).relative uliftYoneda.{u + 1} (diag X.obj) := by
  classical
  let : HasBinaryProducts (BigFppfOver B S hS) :=
    hasBinaryProducts_of_hasTerminal_and_pullbacks _
  let : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.LocallyOfFiniteType.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).IsStableUnderBaseChange :=
    BigFppfOver.isStableUnderBaseChange_inverseImage B S hS _
  let : MorphismProperty.RespectsIso
      (@AlgebraicGeometry.LocallyOfFiniteType.{u} : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  let : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.LocallyOfFiniteType.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).RespectsIso :=
    MorphismProperty.RespectsIso.inverseImage _ _
  refine MorphismProperty.relative.of_exists (fun {c} g => ?_)
  obtain ⟨Po, pa, pb, hsq, hlft⟩ :=
    exists_isPullback_locallyOfFiniteType_of_isFormalAlgebraicSpace B S hS hX c c
      (g ≫ prod.fst) (g ≫ prod.snd)
  let Y := uliftYoneda.{u + 1} (C := BigFppfOver B S hS)
  let κ : Y.obj (c ⨯ c) ≅ Y.obj c ⨯ Y.obj c := PreservesLimitPair.iso Y c c
  have hκ : κ.hom = prodComparison Y c c := rfl
  have hnn : Y.map (prod.lift pa pb) ≫ κ.hom = prod.lift (Y.map pa) (Y.map pb) := by
    rw [hκ]
    apply prod.hom_ext <;> simp [← Y.map_comp]
  have hdg : Y.map (diag c) ≫ κ.hom = diag (Y.obj c) := by
    rw [hκ]
    apply prod.hom_ext <;> simp [← Y.map_comp]
  have hbbsq : IsPullback (Y.map (pullback.fst (prod.lift pa pb) (diag c)))
      (Y.map (pullback.snd (prod.lift pa pb) (diag c)))
      (prod.lift (Y.map pa) (Y.map pb)) (diag (Y.obj c)) := by
    have h1 := isPullback_comp_mono
      ((IsPullback.of_hasPullback (prod.lift pa pb) (diag c)).map Y) κ.hom
    rwa [hnn, hdg] at h1
  refine ⟨pullback (prod.lift pa pb) (diag c),
    Y.map (pullback.snd (prod.lift pa pb) (diag c)) ≫ (g ≫ prod.fst),
    pullback.snd (prod.lift pa pb) (diag c),
    isPullback_diag_of_isPullback_prodLift rfl rfl hsq (prod.lift_fst _ _) (prod.lift_snd _ _)
      hbbsq, ?_⟩
  exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (IsPullback.of_hasPullback (prod.lift pa pb) (diag c)) hlft

/-- Every represented base change of the absolute diagonal of an fppf sheaf on the big fppf
site of `S` is a monomorphism of schemes. No algebraicity is used: the diagonal is a split
monomorphism, monomorphisms are stable under base change, the sheafified Yoneda embedding is
faithful and the structure functor to schemes preserves fibre products. -/
private theorem mono_toScheme_map_of_isPullback_diag_sheaf {X : FppfSheaf B S hS}
    {aa bb : BigFppfOver B S hS}
    (g : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj aa ⟶ X ⨯ X)
    (fst : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj bb ⟶ X)
    (snd : bb ⟶ aa)
    (sq : IsPullback fst
      ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map snd) (diag X) g) :
    Mono ((BigFppfOver.toScheme B S hS).map snd) := by
  let : (BigFppfOver.topology B S hS).Subcanonical := bigFppfOver_subcanonical B S hS
  let : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).Faithful :=
    (Sheaf.fullyFaithfulSheafifiedYoneda (BigFppfOver.topology B S hS)).faithful
  have hdiag : (MorphismProperty.monomorphisms (FppfSheaf B S hS)) (diag X) :=
    inferInstanceAs (Mono (diag X))
  have h1 : Mono ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map snd) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback sq hdiag
  have h2 : Mono snd :=
    (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).mono_of_mono_map h1
  exact preserves_mono_of_preservesLimit _ snd

/-- A relative property of the absolute diagonal of the underlying presheaf of an fppf sheaf on
the big fppf site of `S` is one of the absolute diagonal of the sheaf itself. The forgetful
functor to presheaves is fully faithful and preserves limits, so the two diagonals differ by the
comparison isomorphism for the binary product, and the sheafified Yoneda embedding agrees with
the universe-lifted one, the site being subcanonical. -/
private theorem relative_diag_of_relative_diag_hom
    (Q : MorphismProperty (BigFppfOver B S hS)) {X : FppfSheaf B S hS}
    (h : Q.relative uliftYoneda.{u + 1} (diag X.obj)) :
    Q.relative (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)) (diag X) := by
  let J := BigFppfOver.topology B S hS
  let F := Sheaf.sheafifiedYoneda J
  let K := sheafToPresheaf J (Type (u + 1))
  let : J.Subcanonical := bigFppfOver_subcanonical B S hS
  let : F.Full := (Sheaf.fullyFaithfulSheafifiedYoneda J).full
  let : F.Faithful := (Sheaf.fullyFaithfulSheafifiedYoneda J).faithful
  let gl : F ⋙ K ≅ uliftYoneda.{u + 1} := sheafifiedYonedaPresheafIso B S hS
  let κ : K.obj (X ⨯ X) ≅ K.obj X ⨯ K.obj X := PreservesLimitPair.iso K X X
  have hκ : κ.hom = prodComparison K X X := rfl
  have hd : K.map (diag X) ≫ prodComparison K X X = diag (K.obj X) := by
    apply prod.hom_ext <;> simp [← K.map_comp]
  have hmap : K.map (diag X) = diag (K.obj X) ≫ κ.inv := by
    rw [← hd, ← hκ, Category.assoc, κ.hom_inv_id, Category.comp_id]
  have h1 : Q.relative uliftYoneda.{u + 1} (K.map (diag X)) := by
    rw [hmap]
    exact MorphismProperty.RespectsIso.postcomp _ κ.inv _ h
  exact (Space.relative_comp_map_iff F K Q (diag X)).mp
    (relative_of_natIso gl.symm Q (K.map (diag X)) h1)

/-- **Stacks 0AIP, local finite type, for an arbitrary formal algebraic space:** every
represented base change of the absolute diagonal of a formal algebraic space over `S` is a
locally of finite type morphism of objects of the big fppf site of `S`.

This is the assertion on underlying presheaves,
`…relative_locallyOfFiniteType_diag_hom_of_isFormalAlgebraicSpace`, transported to the sheaf
category, which is where Stacks 0AIP and Stacks 0AN2 are stated. -/
@[stacks 0AIP "locally of finite type, for an arbitrary formal algebraic space"]
theorem relative_locallyOfFiniteType_diag_of_isFormalAlgebraicSpace
    {X : FppfSheaf B S hS} (hX : IsFormalAlgebraicSpace B S hS X) :
    (MorphismProperty.inverseImage
      (@AlgebraicGeometry.LocallyOfFiniteType.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).relative
      (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)) (diag X) :=
  relative_diag_of_relative_diag_hom B S hS _
    (relative_locallyOfFiniteType_diag_hom_of_isFormalAlgebraicSpace B S hS hX)

/-- **Stacks 0AIP, local quasi-finiteness, for an arbitrary formal algebraic space:** every
represented base change of the absolute diagonal of a formal algebraic space over `S` is a
locally quasi-finite, locally of finite type morphism of schemes.

The base change is locally of finite type by
`…relative_locallyOfFiniteType_diag_of_isFormalAlgebraicSpace` and a monomorphism because the
diagonal is, and a monomorphism of schemes locally of finite type is locally quasi-finite, which
is **Stacks 0CT8**. -/
@[stacks 0AIP "locally quasi-finite, for an arbitrary formal algebraic space"]
theorem relative_locallyQuasiFinite_diag_of_isFormalAlgebraicSpace
    {X : FppfSheaf B S hS} (hX : IsFormalAlgebraicSpace B S hS X) :
    (MorphismProperty.inverseImage
      ((@AlgebraicGeometry.LocallyOfFiniteType.{u} : MorphismProperty Scheme.{u}) ⊓
        (@AlgebraicGeometry.LocallyQuasiFinite.{u} : MorphismProperty Scheme.{u}))
      (BigFppfOver.toScheme B S hS)).relative
      (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)) (diag X) := by
  refine ⟨relativelyRepresentable_diag_of_isFormalAlgebraicSpace B S hS hX,
    fun _ _ g fst snd sq => ?_⟩
  have _ : AlgebraicGeometry.LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map snd) :=
    (relative_locallyOfFiniteType_diag_of_isFormalAlgebraicSpace B S hS hX).property g fst snd
      sq
  have _ : Mono ((BigFppfOver.toScheme B S hS).map snd) :=
    mono_toScheme_map_of_isPullback_diag_sheaf B S hS g fst snd sq
  exact ⟨inferInstance, inferInstance⟩

/-- **Stacks 0AIP, separatedness, for an arbitrary formal algebraic space:** every represented
base change of the absolute diagonal of a formal algebraic space over `S` is a separated
morphism of schemes.

This one needs only the representability assertion: the base change is a monomorphism because
the diagonal is, and a monomorphism of schemes is separated. -/
@[stacks 0AIP "separated, for an arbitrary formal algebraic space"]
theorem relative_isSeparated_diag_of_isFormalAlgebraicSpace
    {X : FppfSheaf B S hS} (hX : IsFormalAlgebraicSpace B S hS X) :
    (MorphismProperty.inverseImage
      (@AlgebraicGeometry.IsSeparated.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).relative
      (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)) (diag X) := by
  refine ⟨relativelyRepresentable_diag_of_isFormalAlgebraicSpace B S hS hX,
    fun _ _ g fst snd sq => ?_⟩
  have _ : Mono ((BigFppfOver.toScheme B S hS).map snd) :=
    mono_toScheme_map_of_isPullback_diag_sheaf B S hS g fst snd sq
  show AlgebraicGeometry.IsSeparated ((BigFppfOver.toScheme B S hS).map snd)
  infer_instance

/-- **Stacks 0AN2, local finite type, for a morphism whose source is an *arbitrary* formal
algebraic space:** every represented base change of the relative diagonal of a morphism of fppf
sheaves out of a formal algebraic space is a locally of finite type morphism of schemes.

This discharges the hypothesis of
`AlgebraicGeometry.FormalSpace.relative_pullback_diagonal` for local finite type, the relative
diagonal being a base change of the absolute one. -/
@[stacks 0AN2 "locally of finite type, for a morphism whose source is an arbitrary formal \
algebraic space"]
theorem relative_locallyOfFiniteType_pullback_diagonal_of_isFormalAlgebraicSpace
    {X Y : FppfSheaf B S hS} (f : X ⟶ Y) (hX : IsFormalAlgebraicSpace B S hS X) :
    (MorphismProperty.inverseImage
      (@AlgebraicGeometry.LocallyOfFiniteType.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).relative
      (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)) (pullback.diagonal f) :=
  relative_pullback_diagonal B S hS _ f
    (relative_locallyOfFiniteType_diag_of_isFormalAlgebraicSpace B S hS hX)

/-- **Stacks 0AN2, local quasi-finiteness, for a morphism whose source is an *arbitrary* formal
algebraic space:** every represented base change of the relative diagonal is a locally
quasi-finite, locally of finite type morphism of schemes. -/
@[stacks 0AN2 "locally quasi-finite, for a morphism whose source is an arbitrary formal \
algebraic space"]
theorem relative_locallyQuasiFinite_pullback_diagonal_of_isFormalAlgebraicSpace
    {X Y : FppfSheaf B S hS} (f : X ⟶ Y) (hX : IsFormalAlgebraicSpace B S hS X) :
    (MorphismProperty.inverseImage
      ((@AlgebraicGeometry.LocallyOfFiniteType.{u} : MorphismProperty Scheme.{u}) ⊓
        (@AlgebraicGeometry.LocallyQuasiFinite.{u} : MorphismProperty Scheme.{u}))
      (BigFppfOver.toScheme B S hS)).relative
      (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)) (pullback.diagonal f) :=
  relative_pullback_diagonal B S hS _ f
    (relative_locallyQuasiFinite_diag_of_isFormalAlgebraicSpace B S hS hX)

/-- **Stacks 0AN2, separatedness, for a morphism whose source is an *arbitrary* formal
algebraic space:** every represented base change of the relative diagonal is a separated
morphism of schemes. -/
@[stacks 0AN2 "separated, for a morphism whose source is an arbitrary formal algebraic space"]
theorem relative_isSeparated_pullback_diagonal_of_isFormalAlgebraicSpace
    {X Y : FppfSheaf B S hS} (f : X ⟶ Y) (hX : IsFormalAlgebraicSpace B S hS X) :
    (MorphismProperty.inverseImage
      (@AlgebraicGeometry.IsSeparated.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).relative
      (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)) (pullback.diagonal f) :=
  relative_pullback_diagonal B S hS _ f
    (relative_isSeparated_diag_of_isFormalAlgebraicSpace B S hS hX)

end Member


end AlgebraicGeometry.FormalSpace

end
