module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.Henselian.HenselizationUniversalProperty

/-!
# Canonicity of the map out of a henselization

The maps `R → R^h → R^{sh}` of the henselization tower are *canonical*: a henselization
receives exactly one local map of `R`-algebras into any henselian local `R`-algebra. This
module states that uniqueness in existential form, as the single assertion
`∃! f : Rh →ₐ[R] Sh, IsLocalHom f`.

## Main results

* `HenselianLocalRing.existsUnique_isLocalHom_of_ind_etale`: for a local `R`-algebra `Rh` with
  `R → Rh` local which is a filtered colimit of étale `R`-algebras and surjective on residue
  fields, and a henselian local ring `Sh` with `R → Sh` local, there is exactly one
  `R`-algebra map `Rh → Sh` that is a local ring map.

## Implementation notes

Of the henselization `R → Rh` only the two items of Tag 04GN that the argument uses are
assumed — that `Rh` is ind-étale over `R` and that `R → Rh` is surjective on residue fields —
and of the target only that it is henselian local with a local structure map; so `Rh` is the
initial object of the category of henselian local rings under `R` and local maps. The
commutative square of the source is carried by the `R`-algebra structure of `f`, so no separate
compatibility hypothesis appears.

This packages the three constituents of the universal property proved in
`StacksFrontier.RingTheory.Henselian.HenselizationUniversalProperty` —
`HenselianLocalRing.indEtaleAlgHom`, `HenselianLocalRing.isLocalHom_indEtaleAlgHom` and
`HenselianLocalRing.indEtaleAlgHom_unique` — into the one `ExistsUnique` statement that names
no chosen map, which is the form in which the canonicity of `R → R^h → R^{sh}` is asserted.

## References

* [Stacks Project, Tag 03QL](https://stacks.math.columbia.edu/tag/03QL)
* [Stacks Project, Tag 04GS](https://stacks.math.columbia.edu/tag/04GS)
* [Stacks Project, Tag 04GN](https://stacks.math.columbia.edu/tag/04GN)
-/

@[expose] public section

universe u v w

open IsLocalRing in
/-- **The universal property of the henselization, in existential form** (Stacks 04GS). Let
`(R, 𝔪, κ)` be a local ring, let `Rh` be a local `R`-algebra with `R → Rh` local which is a
filtered colimit of étale `R`-algebras and has residue field `κ`, and let `Sh` be a henselian
local ring with `R → Sh` local. Then there is exactly one `R`-algebra map `Rh → Sh` that is a
local ring map. This is what makes the maps `R → R^h → R^{sh}` of Tag 03QL canonical: applied
to `Rh = R^h` and `Sh = R^{sh}` it pins the map out of the henselization uniquely. -/
@[stacks 03QL "canonicity of the map from the henselization",
  ega "IV 18.6.6" "(ii)",
  sga "4 VIII 4.1" "partial"]
public theorem HenselianLocalRing.existsUnique_isLocalHom_of_ind_etale
    {R : Type u} {Rh : Type v} {Sh : Type w} [CommRing R] [CommRing Rh] [CommRing Sh]
    [IsLocalRing R]
    [IsLocalRing Rh] [HenselianLocalRing Sh] [Algebra R Rh] [Algebra R Sh]
    [IsLocalHom (algebraMap R Rh)] [IsLocalHom (algebraMap R Sh)]
    (hind : (CommAlgCat.etale.{max u v} R).ind.{max u v}
      (CommAlgCat.of R (ULift.{u} Rh)))
    (hres : Function.Surjective (ResidueField.map (algebraMap R Rh))) :
    ∃! f : Rh →ₐ[R] Sh, IsLocalHom f :=
  ⟨HenselianLocalRing.indEtaleAlgHom hind hres,
    HenselianLocalRing.isLocalHom_indEtaleAlgHom hind hres,
    fun f hf => HenselianLocalRing.indEtaleAlgHom_unique hind hres f hf⟩

end
