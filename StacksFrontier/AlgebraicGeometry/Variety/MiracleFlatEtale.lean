module

public import Mathlib.RingTheory.Unramified.LocalRing
public import StacksFrontier.AlgebraicGeometry.Etale.Morphisms.EtaleAt
public import StacksFrontier.AlgebraicGeometry.Morphisms.Etale.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.UnramifiedLocusBaseChange
public import StacksFrontier.RingTheory.Flat.MiracleFlatness
public import StacksFrontier.RingTheory.RegularLocalRing.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Étaleness at a nonsingular point by miracle flatness

Let `g : X ⟶ Y` be a morphism locally of finite type over a locally Noetherian scheme, and let
`x` be a point at which both `X` and `Y` are nonsingular, in the sense that the local rings
`𝒪_{X,x}` and `𝒪_{Y,g x}` are regular. If the two local rings have the same Krull dimension and
`g` is unramified at `x`, then `g` is étale at `x`.

The flatness of the stalk map is miracle flatness (Tag 00R4): the source local ring is regular,
hence Cohen–Macaulay, and unramifiedness makes the fibre ring `𝒪_{X,x}/𝔪_{Y,g x}𝒪_{X,x}` equal
to the residue field `κ(x)`, so the dimension formula `dim 𝒪_{X,x} = dim 𝒪_{Y,g x} + dim κ(x)`
reduces to the assumed equality of dimensions. Étaleness then follows because an étale local
homomorphism is exactly a flat, formally unramified, essentially of finite type one.

## Main results

* `Module.Flat.of_isMaximalCohenMacaulay_of_map_maximalIdeal`: a local homomorphism from a
  regular local ring to a Cohen–Macaulay local ring of the same dimension which extends the
  maximal ideal to the maximal ideal is flat.
* `Module.Flat.of_isRegularLocalRing_of_map_maximalIdeal`: the same statement for a local
  homomorphism of regular local rings.
* `AlgebraicGeometry.flat_stalkMap_of_map_maximalIdeal`: the stalk map of a morphism of schemes
  at a point where both local rings are regular of the same dimension, and where the maximal
  ideal extends to the maximal ideal, is flat.
* `AlgebraicGeometry.etaleAt_of_unramifiedAt_of_ringKrullDim_eq`: a morphism locally of finite
  type over a locally Noetherian scheme, unramified at a point where both local rings are
  regular of the same dimension, is étale there.
* `AlgebraicGeometry.smoothAt_of_unramifiedAt_of_ringKrullDim_eq`: the same hypotheses give
  smoothness at the point.

## Implementation notes

The dimension hypothesis is an equality of the Krull dimensions of the two stalks, which is the
form miracle flatness consumes directly; relating it to the dimension of the schemes at the
point is a separate matter.

Flatness is recorded as `RingHom.Flat` of the stalk map rather than through a scheme-level
predicate, matching `AlgebraicGeometry.IsEtaleAt`.

## References

* [Stacks Project, Tag 00R4](https://stacks.math.columbia.edu/tag/00R4)
* [Stacks Project, Tag 0258](https://stacks.math.columbia.edu/tag/0258)
* [Stacks Project, Tag 00UW](https://stacks.math.columbia.edu/tag/00UW)
-/

@[expose] public section

open CategoryTheory IsLocalRing

universe u

/-- **Miracle flatness in the unramified case.** A local homomorphism `R → S` from a regular
local ring to a Noetherian Cohen–Macaulay local ring of the same Krull dimension, extending the
maximal ideal of `R` to the maximal ideal of `S`, is flat. -/
@[ega "IV 15.4.2" "e′)⇒b), partial", ega "IV 6.1.5" "special case"]
public theorem Module.Flat.of_isMaximalCohenMacaulay_of_map_maximalIdeal
    {R S : Type*} [CommRing R] [IsRegularLocalRing R] [CommRing S] [IsLocalRing S]
    [IsNoetherianRing S] [Algebra R S] [IsLocalHom (algebraMap R S)]
    (hS : Module.IsMaximalCohenMacaulay S S)
    (hmap : (maximalIdeal R).map (algebraMap R S) = maximalIdeal S)
    (hdim : ringKrullDim S = ringKrullDim R) :
    Module.Flat R S := by
  refine Module.Flat.of_isMaximalCohenMacaulay_of_ringKrullDim_eq_add hS ?_
  rw [hmap, hdim]
  let : Field (S ⧸ maximalIdeal S) := Ideal.Quotient.field _
  rw [ringKrullDim_eq_zero_of_isField (Field.toIsField (S ⧸ maximalIdeal S)), add_zero]

/-- A local homomorphism of regular local rings of the same Krull dimension which extends the
maximal ideal to the maximal ideal is flat. -/
public theorem Module.Flat.of_isRegularLocalRing_of_map_maximalIdeal
    {R S : Type*} [CommRing R] [IsRegularLocalRing R] [CommRing S] [IsRegularLocalRing S]
    [Algebra R S] [IsLocalHom (algebraMap R S)]
    (hmap : (maximalIdeal R).map (algebraMap R S) = maximalIdeal S)
    (hdim : ringKrullDim S = ringKrullDim R) :
    Module.Flat R S :=
  .of_isMaximalCohenMacaulay_of_map_maximalIdeal
    (IsRegularLocalRing.isRegular_and_isRegularLocalRing_quotient_and_isMaximalCohenMacaulay
      S).2 hmap hdim

namespace AlgebraicGeometry

/-- A formally unramified, essentially of finite type local homomorphism of local rings extends
the maximal ideal to the maximal ideal. -/
private theorem map_maximalIdeal_of_formallyUnramified {R S : Type*} [CommRing R] [IsLocalRing R]
    [CommRing S] [IsLocalRing S] (f : R →+* S) [IsLocalHom f] (hfu : f.FormallyUnramified)
    (heft : f.EssFiniteType) : (maximalIdeal R).map f = maximalIdeal S := by
  let : Algebra R S := f.toAlgebra
  have : Algebra.FormallyUnramified R S := RingHom.formallyUnramified_algebraMap.mp hfu
  have : Algebra.EssFiniteType R S := RingHom.essFiniteType_algebraMap.mp heft
  exact Algebra.FormallyUnramified.map_maximalIdeal

/-- The stalk map of a morphism of schemes at a point where both local rings are regular of the
same Krull dimension, and where the maximal ideal of the target extends to the maximal ideal of
the source, is flat. -/
public theorem flat_stalkMap_of_map_maximalIdeal {X Y : Scheme.{u}} (g : X ⟶ Y) (x : X)
    [IsRegularLocalRing (Y.presheaf.stalk (g.base x))] [IsRegularLocalRing (X.presheaf.stalk x)]
    (hmap : Ideal.map (g.stalkMap x).hom (maximalIdeal (Y.presheaf.stalk (g.base x))) =
      maximalIdeal (X.presheaf.stalk x))
    (hdim : ringKrullDim (X.presheaf.stalk x) = ringKrullDim (Y.presheaf.stalk (g.base x))) :
    (g.stalkMap x).hom.Flat := by
  let : Algebra (Y.presheaf.stalk (g.base x)) (X.presheaf.stalk x) :=
    (g.stalkMap x).hom.toAlgebra
  have : IsLocalHom (algebraMap (Y.presheaf.stalk (g.base x)) (X.presheaf.stalk x)) :=
    inferInstanceAs (IsLocalHom (g.stalkMap x).hom)
  exact RingHom.flat_algebraMap_iff.mpr
    (Module.Flat.of_isRegularLocalRing_of_map_maximalIdeal hmap hdim)

/-- **Étaleness at a nonsingular point.** A morphism locally of finite type over a locally
Noetherian scheme which is unramified at a point where both local rings are regular of the same
Krull dimension is étale at that point. -/
public theorem etaleAt_of_unramifiedAt_of_ringKrullDim_eq {X Y : Scheme.{u}} (g : X ⟶ Y)
    [LocallyOfFiniteType g] [IsLocallyNoetherian Y] (x : X)
    [IsRegularLocalRing (Y.presheaf.stalk (g.base x))] [IsRegularLocalRing (X.presheaf.stalk x)]
    (hg : UnramifiedAt g x)
    (hdim : ringKrullDim (X.presheaf.stalk x) = ringKrullDim (Y.presheaf.stalk (g.base x))) :
    EtaleAt g x := by
  have hfu : (g.stalkMap x).hom.FormallyUnramified :=
    (unramifiedAt_iff_formallyUnramified_stalkMap g x).mp hg
  have heft : (g.stalkMap x).hom.EssFiniteType := LocallyOfFiniteType.stalkMap g x
  refine (isEtaleAt_iff_etaleAt g x).mp ⟨?_, hfu, heft⟩
  exact flat_stalkMap_of_map_maximalIdeal g x
    (map_maximalIdeal_of_formallyUnramified _ hfu heft) hdim

/-- Under the hypotheses of `AlgebraicGeometry.etaleAt_of_unramifiedAt_of_ringKrullDim_eq` the
morphism is in particular smooth at the point. -/
public theorem smoothAt_of_unramifiedAt_of_ringKrullDim_eq {X Y : Scheme.{u}} (g : X ⟶ Y)
    [LocallyOfFiniteType g] [IsLocallyNoetherian Y] (x : X)
    [IsRegularLocalRing (Y.presheaf.stalk (g.base x))] [IsRegularLocalRing (X.presheaf.stalk x)]
    (hg : UnramifiedAt g x)
    (hdim : ringKrullDim (X.presheaf.stalk x) = ringKrullDim (Y.presheaf.stalk (g.base x))) :
    InfinitesimalLifting.SmoothAt g x :=
  ((etaleAt_iff_smoothAt_and_unramifiedAt g x).mp
    (etaleAt_of_unramifiedAt_of_ringKrullDim_eq g x hg hdim)).1

end AlgebraicGeometry

end
