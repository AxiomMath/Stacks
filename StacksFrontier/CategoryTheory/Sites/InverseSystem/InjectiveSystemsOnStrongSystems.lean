module

public import StacksFrontier.CategoryTheory.Sites.InverseSystem.CohomologyOfColimitOfFiniteSites

/-!
# Injective embeddings of systems of abelian sheaves, for finitely generated coverings

Stacks 0EXZ over `InverseSystemOfSites`: let `I` be a cofiltered index category and
`(C_i, f_a)` an inverse system of sites over `I` as in Stacks Situation 0A34; given an abelian
sheaf `F_i` on `C_i` for every index and, for every `a : j → i`, a map
`φ_a : f_a^{-1}F_i → F_j` of abelian sheaves on `C_j` with `φ_c = φ_b ∘ f_b^{-1}φ_a` whenever
`c = a ∘ b`, there is a map of systems `(F_i, φ_a) → (G_i, ψ_a)` with every `F_i → G_i` injective
and every `G_i` an injective abelian sheaf.

Situation 0A34 has two renderings in this library, differing only in how they say that the
coverings of each `C_i` are finite (Stacks 00VH), and this file is Stacks 0EXZ for the second:

* `InverseSystemOfFiniteSites` asks that every covering sieve *contain* a finite covering family,
  which is the condition the source imposes, and carries the mathematics — the construction of
  the source's proof, `F_i → A_i` into an injective abelian sheaf followed by
  `G_i = ∏_{b : k → i} f_{b,*}A_k`, is in
  `StacksFrontier/CategoryTheory/Sites/InverseSystem/CohomologyOfColimitOfFiniteSites.lean`;
* `InverseSystemOfSites` asks that every covering sieve be *generated* by a finite family, which
  is strictly stronger.

Nothing is reproved here. `InverseSystemOfSites.toInverseSystemOfFiniteSites` carries the index
category, the sites, the transition functors and all of their properties across unchanged — the
two structures differ in no other field — so a system of abelian sheaves on the one is literally
a system of abelian sheaves on the other, and the result is the general one read at the image of
that map. This is the delegation the strong-system statements of Stacks 0A35 and 0EXJ in
`CohomologyOfColimitOfFiniteSites.lean` already use.

## Main definitions

* `InverseSystemOfSites.AbelianSheafSystem`: a system of abelian sheaves, with inverse-image
  transition maps, on an inverse system of sites whose covering sieves are finitely generated.
* `InverseSystemOfSites.AbelianSheafSystem.Hom`: a morphism of such systems.

## Main results

* `InverseSystemOfSites.AbelianSheafSystem.exists_mono_to_pointwise_injective`: **Stacks 0EXZ**
  for such a system — every system of abelian sheaves admits a levelwise monomorphism into a
  system whose sheaf at every index is injective.

## References

* [Stacks 0EXZ](https://stacks.math.columbia.edu/tag/0EXZ)
* [Stacks 0A34](https://stacks.math.columbia.edu/tag/0A34)
* [Stacks 00VH](https://stacks.math.columbia.edu/tag/00VH)

Tags covered: 0EXZ.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u w t

namespace InverseSystemOfSites

/-- A system of abelian sheaves on an inverse system of sites whose covering sieves are finitely
generated, with inverse-image transition maps: the data (1) and (2) of Stacks 0EXZ, namely an
abelian sheaf `obj i` on the site at each index together with maps
`map a : f_a^{-1}(obj j) ⟶ obj i` satisfying the cocycle condition.

This is the same notion as `InverseSystemOfFiniteSites.AbelianSheafSystem`, read through
`InverseSystemOfSites.toInverseSystemOfFiniteSites`: that map changes none of the data a system of
abelian sheaves refers to — the topologies `J i` and the transition functors `u a`, hence the
inverse-image functors `abelianSheafPullback` — so there is nothing to transport. -/
abbrev AbelianSheafSystem (D : InverseSystemOfSites.{v, u, w}) :=
  InverseSystemOfFiniteSites.AbelianSheafSystem.{v, u, w, t} D.toInverseSystemOfFiniteSites

/-- A morphism of systems of abelian sheaves: a map at each index, compatible with the
inverse-image transition maps of the two systems. -/
abbrev AbelianSheafSystem.Hom {D : InverseSystemOfSites.{v, u, w}}
    (F G : AbelianSheafSystem.{v, u, w, t} D) :=
  InverseSystemOfFiniteSites.AbelianSheafSystem.Hom.{v, u, w, t} F G

/-- **Stacks 0EXZ.** Every system of abelian sheaves on an inverse system of sites admits a
levelwise monomorphism to a system whose sheaf at every index is injective.

The system here is one on an `InverseSystemOfSites`, that is on a system of sites all of whose
covering sieves are finitely generated; see
`InverseSystemOfFiniteSites.AbelianSheafSystem.exists_mono_to_pointwise_injective` for the same
statement over the source-faithful finiteness condition of Stacks 00VH, which is where the
construction of the source's proof is carried out, and of which this is the reading along
`InverseSystemOfSites.toInverseSystemOfFiniteSites`. -/
@[stacks 0EXZ]
theorem AbelianSheafSystem.exists_mono_to_pointwise_injective
    {D : InverseSystemOfSites.{v, u, w}} (F : AbelianSheafSystem.{v, u, w, t} D) :
    ∃ (G : AbelianSheafSystem.{v, u, w, t} D) (f : AbelianSheafSystem.Hom.{v, u, w, t} F G),
      (∀ i, Mono (f.app i)) ∧ ∀ i, Injective (G.obj i) :=
  InverseSystemOfFiniteSites.AbelianSheafSystem.exists_mono_to_pointwise_injective.{v, u, w, t} F

end InverseSystemOfSites

end
