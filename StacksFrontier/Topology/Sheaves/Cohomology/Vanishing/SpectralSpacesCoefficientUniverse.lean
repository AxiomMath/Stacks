module

public import StacksFrontier.Topology.Sheaves.Cohomology.Vanishing.SpectralSpaces

/-!
# Vanishing above the dimension, with the coefficient universe free of the space's

`Stacks.CohomologyVanishing.subsingleton_sheafH_of_topologicalKrullDim_le` proves clause (1) of
[Stacks, Tag 0A3G] — on a spectral space of Krull dimension at most `d` every abelian sheaf has
vanishing cohomology above degree `d` — for a space `Y : Type u` with coefficients in
`AddCommGrpCat.{u}`.  The two universes are the same there, and not by choice: the induction on
the dimension runs through `CategoryTheory.Sheaf.cohomologyPresheaf`, whose coefficient universe
Mathlib pins to the morphism universe of the site, and for the lattice of opens of a `Type u` that
morphism universe is `u`.

This file removes the tie, by moving the space rather than the coefficients: for `X : Type u` the
space `ULift.{w} X` is homeomorphic to `X` and lives in `Type (max u w)`, so clause (1) applies to
it with coefficients in `AddCommGrpCat.{max u w}`, and the two lattices of opens are isomorphic,
which carries the vanishing back to `X`.

## Main results

* `Stacks.CohomologyVanishing.subsingleton_sheafH_of_topologicalKrullDim_le_of_coefficients`:
  **clause (1) of [Stacks, Tag 0A3G] with the coefficient universe free.**  For a spectral space
  `X : Type u` of Krull dimension at most `d`, every sheaf in `AddCommGrpCat.{max u w}` has
  vanishing cohomology above degree `d`.
* `Stacks.CohomologyVanishing`
  `.subsingleton_sheafCohomology_of_noetherianSpace_of_dim_le_of_coefficients`:
  **[Stacks, Tag 02UZ], Grothendieck's vanishing theorem, with the coefficient universe free.**
  This is `...subsingleton_sheafCohomology_of_noetherianSpace` with its `hspectral` hypothesis
  discharged; that hypothesis was already stated at a free coefficient universe and was the only
  thing the Noetherian form was waiting for.
* `Stacks.CohomologyVanishing.topologicalKrullDim_ulift` and the instance
  `Stacks.CohomologyVanishing.spectralSpace_ulift`: a `ULift` of a space is spectral of the same
  dimension.

## The transport

Every ingredient is available.  The order isomorphism `Opens (ULift.{w} X) ≃o Opens X` is
`Homeomorph.opensCongr` of `Homeomorph.ulift`.  Transport of sheaf cohomology along an order
isomorphism of lattices of opens is the toolkit of
`StacksFrontier/Topology/Sheaves/Cohomology/Vanishing/NoetherianSpaces.lean`, built there for the
soberification and already stated with the coefficient universe free and the two `Ext` universes
independent: `Stacks.CohomologyVanishing.isDenseSubsite_of_opensOrderIso`,
`...hasSheafify_of_opensOrderIso`, `...sheafEquivOfOpensOrderIso`,
`...constantSheafIsoOfOpensOrderIso`, `...subsingleton_ext_of_equivalence` and
`...subsingleton_ext_of_iso_source`.  The proof below is the proof of
`...subsingleton_sheafCohomology_of_soberification` with `Soberification X` replaced by
`ULift.{w} X`, which is why it is short: `Sheaf.H` is `Ext` out of the constant sheaf on `ℤ`, the
equivalence of sheaf categories induced by the order isomorphism carries that constant sheaf to
the constant sheaf, and an additive equivalence of abelian categories is a bijection on `Ext`.

What the transport does **not** do is move the *proof* of clause (1) to a free coefficient
universe.  The `cohomologyPresheaf`-mediated induction stays where it is, at the universe of the
`ULift`ed space, where the coefficient universe and the morphism universe agree; only its
conclusion, which is a statement about `CategoryTheory.Sheaf.H` and so already
universe-polymorphic in the coefficients, is carried across.

## Implementation notes

The coefficient universe is written `max u w` rather than as a free variable because the sheaf is
transported to a space in `Type (max u w)`, where clause (1) demands the coefficients at the
space's own universe; the `max` is how "the coefficient universe absorbs `u`" is said to the
elaborator, exactly as in
`StacksFrontier/CategoryTheory/Sites/GlobalSections/DerivedGlobalSectionsCohomology.lean`.  Taking
`w := u` recovers the existing statements, and `w := u + 1` is the case the crystalline chapter
needs, its Zariski site being the opens of a `Type u` with coefficients forced to `u + 1` by the
crystalline side.

The `Ext` universe `w'` of the conclusion is free of everything else, as it is in the
transport lemmas: the two cohomology groups are identified only up to a bijection of types, so the
universe the `Ext` groups are shrunk to on either side need not agree.

## References

* [Stacks Project, Tag 0A3G](https://stacks.math.columbia.edu/tag/0A3G)
* [Stacks Project, Tag 02UZ](https://stacks.math.columbia.edu/tag/02UZ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe w' w u

namespace Stacks.CohomologyVanishing

/-! ### `ULift` of a space -/

/-- **A `ULift` of a spectral space is spectral.**  Each of the five component classes of
`SpectralSpace` transports along the homeomorphism `ULift.{w} X ≃ₜ X`.

`SpectralSpace.of_homeomorph` says the same thing, but for two spaces in one universe, which is
exactly what a `ULift` is not. -/
instance spectralSpace_ulift (X : Type u) [TopologicalSpace X] [SpectralSpace X] :
    SpectralSpace (ULift.{w} X) := by
  have e : ULift.{w} X ≃ₜ X := Homeomorph.ulift
  have : T0Space (ULift.{w} X) := e.isEmbedding.t0Space
  have : CompactSpace (ULift.{w} X) := Homeomorph.compactSpace e.symm
  have : QuasiSober (ULift.{w} X) := Topology.IsClosedEmbedding.quasiSober e.isClosedEmbedding
  have : QuasiSeparatedSpace (ULift.{w} X) := (quasiSeparatedSpace_congr e.symm).mp inferInstance
  have : PrespectralSpace (ULift.{w} X) :=
    Topology.IsOpenEmbedding.prespectralSpace e.isOpenEmbedding
  exact ⟨⟩

/-- **A `ULift` of a space has the same topological Krull dimension**, being homeomorphic to
it. -/
theorem topologicalKrullDim_ulift (X : Type u) [TopologicalSpace X] :
    topologicalKrullDim (ULift.{w} X) = topologicalKrullDim X :=
  IsHomeomorph.topologicalKrullDim_eq _ (Homeomorph.ulift (X := X)).isHomeomorph

/-- **The order isomorphism `Opens (ULift.{w} X) ≃o Opens X`**, the lattices of opens of two
homeomorphic spaces.  This is the datum the cohomology transport of
`StacksFrontier/Topology/Sheaves/Cohomology/Vanishing/NoetherianSpaces.lean` consumes, and the one
place where the universes of the two spaces are allowed to differ. -/
def uliftOpensOrderIso (X : Type u) [TopologicalSpace X] :
    Opens (ULift.{w} X) ≃o Opens X :=
  (Homeomorph.ulift (X := X)).opensCongr

/-! ### Clause (1) of [Stacks, Tag 0A3G] at a free coefficient universe -/

/-- **Clause (1) of [Stacks, Tag 0A3G], with the coefficient universe free of the space's.**  Let
`X : Type u` be a spectral space of Krull dimension at most `d` and let `G` be an abelian sheaf on
`X` with values in `AddCommGrpCat.{max u w}`.  Then `H^q(X, G) = 0` for every `q > d`.

`Stacks.CohomologyVanishing.subsingleton_sheafH_of_topologicalKrullDim_le` is this statement with
`w := u`.  The generalization is proved from it, not independently: the space `ULift.{w} X` is
spectral of the same Krull dimension (`spectralSpace_ulift`, `topologicalKrullDim_ulift`) and
lives in `Type (max u w)`, which is the coefficient universe, so clause (1) applies to it there;
the lattices of opens of `X` and of `ULift.{w} X` are isomorphic, so the two categories of abelian
sheaves are equivalent compatibly with the constant sheaf on `ℤ`
(`sheafEquivOfOpensOrderIso`, `constantSheafIsoOfOpensOrderIso`), and `Sheaf.H` is `Ext` out of
that constant sheaf, which an additive equivalence preserves. -/
theorem subsingleton_sheafH_of_topologicalKrullDim_le_of_coefficients (d : ℕ) (X : Type u)
    [TopologicalSpace X] [SpectralSpace X]
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{max u w}]
    [HasExt.{w'} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{max u w})]
    (G : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{max u w}) (q : ℕ)
    (hdim : topologicalKrullDim X ≤ (d : WithBot ℕ∞)) (hq : d < q) :
    Subsingleton (Sheaf.H.{w', max u w, u, u} G q) := by
  classical
  let e : Opens (ULift.{w} X) ≃o Opens X := uliftOpensOrderIso.{w} X
  have hd : e.equivalence.functor.IsDenseSubsite
      (Opens.grothendieckTopology (ULift.{w} X)) (Opens.grothendieckTopology X) :=
    isDenseSubsite_of_opensOrderIso e
  have hsheafify : HasSheafify (Opens.grothendieckTopology (ULift.{w} X))
      AddCommGrpCat.{max u w} :=
    hasSheafify_of_opensOrderIso e (isDenseSubsite_of_opensOrderIso e.symm)
  have hext : HasExt.{max u w}
      (Sheaf (Opens.grothendieckTopology (ULift.{w} X)) AddCommGrpCat.{max u w}) :=
    hasExt_of_enoughInjectives _
  let E : Sheaf (Opens.grothendieckTopology (ULift.{w} X)) AddCommGrpCat.{max u w} ≌
      Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{max u w} :=
    sheafEquivOfOpensOrderIso e hd
  have : E.functor.Additive := E.functor.additive_of_preserves_binary_products
  exact subsingleton_ext_of_iso_source
    (constantSheafIsoOfOpensOrderIso e hd (AddCommGrpCat.of (ULift.{max u w} ℤ))) q
    (subsingleton_ext_of_equivalence E
      ((constantSheaf (Opens.grothendieckTopology (ULift.{w} X))
        AddCommGrpCat.{max u w}).obj (AddCommGrpCat.of (ULift.{max u w} ℤ))) G q
      (subsingleton_sheafH_of_topologicalKrullDim_le d (ULift.{w} X) hsheafify hext
        (E.inverse.obj G) q (by rwa [topologicalKrullDim_ulift]) hq))

/-- **Clause (1) of [Stacks, Tag 0A3G] with the coefficients one universe above the space.**  The
case `w := u + 1` of `subsingleton_sheafH_of_topologicalKrullDim_le_of_coefficients`, written out
because it is the recurring one — a site built from a `Type u` whose coefficient universe is
pushed to `u + 1` by a larger site it is compared with, as the small Zariski site of a scheme is
by the crystalline site over it — and because `max u (u + 1)` is a universe the elaborator will
not guess from `u + 1`. -/
theorem subsingleton_sheafH_of_topologicalKrullDim_le_succ (d : ℕ) (X : Type u)
    [TopologicalSpace X] [SpectralSpace X]
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u + 1}]
    [HasExt.{w'} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u + 1})]
    (G : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u + 1}) (q : ℕ)
    (hdim : topologicalKrullDim X ≤ (d : WithBot ℕ∞)) (hq : d < q) :
    Subsingleton (Sheaf.H.{w', u + 1, u, u} G q) :=
  subsingleton_sheafH_of_topologicalKrullDim_le_of_coefficients.{w', u + 1, u} d X G q hdim hq

/-! ### [Stacks, Tag 02UZ] at a free coefficient universe -/

/-- **[Stacks, Tag 02UZ], Grothendieck's vanishing theorem, with the coefficient universe free of
the space's.**  Let `X : Type u` be a Noetherian topological space of topological Krull dimension
at most `d` and let `F` be an abelian sheaf on `X` with values in `AddCommGrpCat.{max u w}`.  Then
`H^p(X, F) = 0` for every `p > d`.

This is `Stacks.CohomologyVanishing.subsingleton_sheafCohomology_of_noetherianSpace` with its
`hspectral` hypothesis discharged.  That reduction was already stated at a free coefficient
universe — it passes to the soberification, whose lattice of opens is that of `X` — so the only
thing it was waiting for was clause (1) of [Stacks, Tag 0A3G] there, which is
`subsingleton_sheafH_of_topologicalKrullDim_le_of_coefficients`.
`Stacks.CohomologyVanishing.subsingleton_sheafCohomology_of_noetherianSpace_of_dim_le` is this
statement with `w := u`. -/
@[stacks 02UZ "with the coefficient universe free of the universe of the space"]
theorem subsingleton_sheafCohomology_of_noetherianSpace_of_dim_le_of_coefficients
    {X : Type u} [TopologicalSpace X] [NoetherianSpace X]
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{max u w}]
    [HasExt.{w'} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{max u w})]
    {d p : ℕ} (hdim : topologicalKrullDim X ≤ (d : WithBot ℕ∞)) (hp : d < p)
    (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{max u w}) :
    Subsingleton (Sheaf.H.{w', max u w, u, u} F p) := by
  have hsheafify : HasSheafify (Opens.grothendieckTopology (Soberification X))
      AddCommGrpCat.{max u w} :=
    hasSheafify_of_opensOrderIso (soberificationOpensOrderIso (X := X))
      (isDenseSubsite_of_opensOrderIso (soberificationOpensOrderIso (X := X)).symm)
  have hext := HasExt.standard
    (Sheaf (Opens.grothendieckTopology (Soberification X)) AddCommGrpCat.{max u w})
  refine subsingleton_sheafCohomology_of_noetherianSpace (fun Y _ _ hsY heY G e q hdY hq => ?_)
    hdim hp F
  have := hsY
  have := heY
  exact subsingleton_sheafH_of_topologicalKrullDim_le_of_coefficients e Y G q hdY hq

end Stacks.CohomologyVanishing

end
