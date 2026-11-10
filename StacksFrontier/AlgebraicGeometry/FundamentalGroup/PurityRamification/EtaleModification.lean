module

public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.PurityRamificationLocus.EtaleLocus
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.FibreRankSemicontinuity
public import StacksFrontier.AlgebraicGeometry.Morphisms.QuasiFinite.Locus
public import StacksFrontier.AlgebraicGeometry.Morphisms.QuasiFinite.Permanence
public import StacksFrontier.AlgebraicGeometry.Variety.Geometric.BirationalIsomorphismLocus

/-!
# Étaleness descends along a modification which is étale over the target

The last sentence of the proof of [Stacks, Tag 0EA3] reads: "étaleness of `f'` forces `b` to be
an isomorphism", where `b : X' ⟶ X` is a proper birational morphism onto a scheme with normal
local ring at `x` and `f' = b ≫ f` has been shown to be étale along the fibre of `b` over `x`.
This file proves that step.

## Main results

* `AlgebraicGeometry.finite_preimage_singleton_of_quasiFiniteAt` — over a Noetherian source, a
  morphism quasi-finite at every point over `x` has finite fibre over `x`.
* `AlgebraicGeometry.exists_isIso_restrict_of_etaleAt_comp` — if `b : X' ⟶ X` is proper and
  birational, `X` is Noetherian, `X'` is reduced, `𝒪_{X, x}` is a normal domain and `b ≫ f` is
  étale at every point of the fibre of `b` over `x`, then `b` is an isomorphism over an open
  neighbourhood of `x`.
* `AlgebraicGeometry.etaleAt_of_etaleAt_comp_of_isBirational` — under the same hypotheses `f` is
  étale at `x`.

## Proof

Étaleness of `b ≫ f` at a point gives quasi-finiteness of `b ≫ f`, hence of `b`
([Stacks, Tag 03WR], `AlgebraicGeometry.quasiFiniteAt_of_comp`), at every point of the fibre over
`x`.  The fibre lies in the quasi-finite locus of `b` ([Stacks, Tag 01TI]), on which `b` is
locally quasi-finite and quasi-compact (its source is Noetherian), so the fibre is finite.  A
proper birational morphism with finite fibre over a point with normal local ring is an
isomorphism over a neighbourhood of that point, [Stacks, Tag 0BFP]
(`AlgebraicGeometry.exists_isIso_restrict_of_finite_fiber_of_normal`).  Over that neighbourhood
`f` is `b ≫ f` up to an isomorphism, so it is étale at `x`.

## References

* [Stacks Project, Tag 0EA3](https://stacks.math.columbia.edu/tag/0EA3)
* [Stacks Project, Tag 0BFP](https://stacks.math.columbia.edu/tag/0BFP)
* [Stacks Project, Tag 03WR](https://stacks.math.columbia.edu/tag/03WR)
* [Stacks Project, Tag 01TI](https://stacks.math.columbia.edu/tag/01TI)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- Over a Noetherian source, a morphism which is quasi-finite at every point over `x` has finite
fibre over `x`: the fibre lies in the quasi-finite locus, on which the morphism is locally
quasi-finite, and quasi-compact because its source is a Noetherian space. -/
theorem finite_preimage_singleton_of_quasiFiniteAt {X X' : Scheme.{u}} [IsNoetherian X']
    (b : X' ⟶ X) (x : X) (h : ∀ x' : X', b x' = x → quasiFiniteAt b x') :
    (b ⁻¹' {x}).Finite := by
  let W := quasiFiniteLocus b
  have _ : NoetherianSpace W.toScheme := inferInstanceAs (NoetherianSpace (W : Set X'))
  have _ : QuasiCompact (W.ι ≫ b) := quasiCompact_of_noetherianSpace_source _
  exact ((finite_preimage_singleton_of_locallyQuasiFinite (W.ι ≫ b) x).image W.ι).subset
    fun x' hx' => ⟨⟨x', (mem_quasiFiniteLocus_iff b x').mpr (h x' hx')⟩, hx', rfl⟩

/-- **A proper birational morphism which becomes étale after composing with `f` along the fibre
over `x` is an isomorphism near `x`.**  Let `b : X' ⟶ X` be proper and birational with `X`
Noetherian, `X'` reduced and `𝒪_{X, x}` a normal domain.  If `b ≫ f` is étale at every point of
the fibre of `b` over `x`, then `b` is an isomorphism over an open neighbourhood of `x`. -/
theorem exists_isIso_restrict_of_etaleAt_comp {X X' Y : Scheme.{u}} [IsNoetherian X]
    (b : X' ⟶ X) [IsProper b] [IsReduced X'] (hb : IsBirational b) (f : X ⟶ Y) (x : X)
    [IsDomain (X.presheaf.stalk x)] [IsIntegrallyClosed (X.presheaf.stalk x)]
    (h : ∀ x' : X', b x' = x → EtaleAt (b ≫ f) x') :
    ∃ U : X.Opens, x ∈ U ∧ IsIso (b ∣_ U) := by
  have _ : IsLocallyNoetherian X' := LocallyOfFiniteType.isLocallyNoetherian b
  have _ : CompactSpace X' := QuasiCompact.compactSpace_of_compactSpace b
  have _ : IsNoetherian X' := ⟨⟩
  exact exists_isIso_restrict_of_finite_fiber_of_normal b hb x
    (finite_preimage_singleton_of_quasiFiniteAt b x fun x' hx' =>
      quasiFiniteAt_of_comp b f x' (quasiFiniteAt_of_etaleAt _ x' (h x' hx')))

/-- **Étaleness descends along a modification which is étale over the target.**  Let
`b : X' ⟶ X` be proper and birational with `X` Noetherian, `X'` reduced and `𝒪_{X, x}` a normal
domain, and let `f : X ⟶ Y`.  If `b ≫ f` is étale at every point of the fibre of `b` over `x`,
then `f` is étale at `x`.

This is the last step of the proof of [Stacks, Tag 0EA3]: "étaleness of `f'` forces `b` to be an
isomorphism".  By `AlgebraicGeometry.exists_isIso_restrict_of_etaleAt_comp` the morphism `b` is
an isomorphism over a neighbourhood `U` of `x`, and over `U` the morphism `f` is `b ≫ f`
precomposed with the inverse of that isomorphism. -/
theorem etaleAt_of_etaleAt_comp_of_isBirational {X X' Y : Scheme.{u}} [IsNoetherian X]
    (b : X' ⟶ X) [IsProper b] [IsReduced X'] (hb : IsBirational b) (f : X ⟶ Y) (x : X)
    [IsDomain (X.presheaf.stalk x)] [IsIntegrallyClosed (X.presheaf.stalk x)]
    (h : ∀ x' : X', b x' = x → EtaleAt (b ≫ f) x') : EtaleAt f x := by
  obtain ⟨U, hxU, hU⟩ := exists_isIso_restrict_of_etaleAt_comp b hb f x h
  let p : U.toScheme := ⟨x, hxU⟩
  let q : (b ⁻¹ᵁ U).toScheme := (inv (b ∣_ U)) p
  have hq : b ((b ⁻¹ᵁ U).ι q) = x := by
    rw [← Scheme.Hom.comp_apply, ← morphismRestrict_ι, Scheme.Hom.comp_apply]
    change U.ι ((b ∣_ U) ((inv (b ∣_ U)) p)) = x
    rw [← Scheme.Hom.comp_apply (inv (b ∣_ U)), IsIso.inv_hom_id]
    rfl
  have hp := etaleAt_comp_of_etale (inv (b ∣_ U)) _ p
    (etaleAt_comp_of_etale (b ⁻¹ᵁ U).ι (b ≫ f) q (h _ hq))
  rw [← Category.assoc ((b ⁻¹ᵁ U).ι), ← morphismRestrict_ι, Category.assoc,
    IsIso.inv_hom_id_assoc] at hp
  exact etaleAt_of_open_precomp U.ι f p hp

end AlgebraicGeometry

end
