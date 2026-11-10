module

public import StacksFrontier.AlgebraicGeometry.Duality.ExtensionZeroCoherent.DeligneSystemTriangles

/-!
# Transferring `RestrictionLifting` along a fully faithful inclusion and along an isomorphism

`CategoryTheory.RestrictionLifting F R N` is the elementwise form of the identification
`colim_n Mor(F_n, N) = colim_n Mor(R F_n, R N)` of [Stacks, Tag 0G2H]. This file records the two
transfers the dévissage of that tag needs on top of
`CategoryTheory.RestrictionLifting.of_natIso` and `CategoryTheory.RestrictionLifting.map_source`.

* Along a **fully faithful** `ι : 𝒟 ⥤ 𝒟'`, the statement for `(ι F_n)` against `ι N` with respect
  to `R' : 𝒟' ⥤ 𝒞` gives the statement for `(F_n)` against `N` with respect to `ι ⋙ R'`. This is
  the direction `CategoryTheory.RestrictionLifting.map_source` does not provide, and it is what
  moves the statement for a Deligne system in `D^b_{Coh}(𝒪_X)` down from the statement in
  `D(𝒪_X)`, where `AlgebraicGeometry.restrictBoundedCoherent` is literally
  `(boundedCoherentDerived X).ι ⋙ (Scheme.Modules.restrictFunctor j).mapDerivedCategory`.
* Along an **isomorphism of the target object**, which is what replaces an object concentrated in
  a single degree by the `singleFunctor` of its cohomology there.

## Main results

* `CategoryTheory.RestrictionLifting.of_fullyFaithful_comp`
* `CategoryTheory.RestrictionLifting.of_iso_target`

## References

* [Stacks Project, Tag 0G2H](https://stacks.math.columbia.edu/tag/0G2H)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open InverseSequence

universe v u u' u''

namespace CategoryTheory

variable {𝒟 : Type u} [Category.{v} 𝒟] {𝒞 : Type u'} [Category.{v} 𝒞]

/-- **`CategoryTheory.RestrictionLifting` descends along a fully faithful functor.** If the
identification holds for the system `(ι F_n)` against `ι N` with respect to `R'`, then it holds
for `(F_n)` against `N` with respect to `ι ⋙ R'`.

Both halves are the hypothesis read through `ι`: a lift of a morphism out of `R' ι F_n` is
already a morphism out of `ι F_m`, so it is `ι` of a morphism out of `F_m` by fullness, and two
morphisms agreeing after `ι` agree by faithfulness. -/
public lemma RestrictionLifting.of_fullyFaithful_comp {𝒟' : Type u''} [Category.{v} 𝒟']
    (F : ℕᵒᵖ ⥤ 𝒟) (ι : 𝒟 ⥤ 𝒟') [ι.Full] [ι.Faithful] (R' : 𝒟' ⥤ 𝒞) (N : 𝒟)
    (h : RestrictionLifting (F ⋙ ι) R' (ι.obj N)) : RestrictionLifting F (ι ⋙ R') N := by
  constructor
  · intro n g
    obtain ⟨m, hm, f, hf⟩ := h.lift n g
    refine ⟨m, hm, ι.preimage f, ?_⟩
    change R'.map (ι.map (ι.preimage f)) = R'.map (ι.map (tr F hm)) ≫ g
    rwa [ι.map_preimage]
  · intro n f g hfg
    obtain ⟨m, hm, he⟩ := h.eq n (ι.map f) (ι.map g) hfg
    exact ⟨m, hm, ι.map_injective (by rwa [ι.map_comp, ι.map_comp])⟩

/-- **`CategoryTheory.RestrictionLifting` is invariant under an isomorphism of the target
object.** -/
public lemma RestrictionLifting.of_iso_target {F : ℕᵒᵖ ⥤ 𝒟} {R : 𝒟 ⥤ 𝒞} {N N' : 𝒟}
    (h : RestrictionLifting F R N) (e : N ≅ N') : RestrictionLifting F R N' := by
  constructor
  · intro n g
    obtain ⟨m, hm, f, hf⟩ := h.lift n (g ≫ R.map e.inv)
    refine ⟨m, hm, f ≫ e.hom, ?_⟩
    rw [R.map_comp, hf, Category.assoc, Category.assoc, ← R.map_comp, e.inv_hom_id, R.map_id,
      Category.comp_id]
  · intro n f g hfg
    obtain ⟨m, hm, he⟩ := h.eq n (f ≫ e.inv) (g ≫ e.inv)
      (by rw [R.map_comp, R.map_comp, hfg])
    rw [← Category.assoc, ← Category.assoc, cancel_mono] at he
    exact ⟨m, hm, he⟩

end CategoryTheory

end
