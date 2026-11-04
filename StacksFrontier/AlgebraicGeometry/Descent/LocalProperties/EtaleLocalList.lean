module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.SchemeProperty.ReducedSmoothLocal
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.Normal
public import StacksFrontier.AlgebraicGeometry.Descent.Germs.GorensteinFiber
public import StacksFrontier.AlgebraicGeometry.Descent.LocalProperties.CohenMacaulay
public import StacksFrontier.AlgebraicGeometry.Descent.LocalProperties.Jacobson
public import StacksFrontier.AlgebraicGeometry.Descent.LocalProperties.Nagata
public import StacksFrontier.AlgebraicGeometry.Descent.LocalProperties.Noetherian
public import StacksFrontier.AlgebraicGeometry.Descent.LocalProperties.Reduced
public import StacksFrontier.AlgebraicGeometry.Descent.LocalProperties.Regular
public import StacksFrontier.AlgebraicGeometry.Descent.LocalProperties.RegularInCodimension
public import StacksFrontier.AlgebraicGeometry.Descent.LocalProperties.SerreCondition
public import StacksFrontier.AlgebraicGeometry.Duality.GorensteinSchemes.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.Syntomic.Etale
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.Coverings

/-!
# The list of properties of schemes which are local for the étale topology

A property of schemes is local for the étale topology when a scheme has it if and only if
the members of an étale covering family of that scheme have it. This file collects the ten
properties for which this holds, each one with the locality statement of the étale
precoverage `AlgebraicGeometry.Scheme.etalePrecoverage`:

1. locally Noetherian,
2. Jacobson,
3. locally Noetherian and `(S_k)`,
4. Cohen-Macaulay,
5. Gorenstein,
6. reduced,
7. normal,
8. locally Noetherian and `(R_k)`,
9. regular,
10. Nagata.

The fpqc, fppf, syntomic and smooth topologies are stronger than the étale topology, so an
item already known to be local for one of those is local for the étale topology as well.

## Main results

* `AlgebraicGeometry.jacobsonSpace_isLocal_etale`, `AlgebraicGeometry.isGorenstein_isLocal_etale`,
  `AlgebraicGeometry.isReduced_isLocal_etale`,
  `AlgebraicGeometry.isCohenMacaulay_isLocal_etale`,
  `AlgebraicGeometry.isLocallyNoetherian_and_hasPropertySk_isLocal_etale` and
  `AlgebraicGeometry.isLocallyNoetherian_and_isRegularInCodimension_isLocal_etale` are the
  items of the list whose étale form is recorded here.
* The remaining four items are already available in étale form, and are recorded against this
  remark by `add_to_stacks`:
  `AlgebraicGeometry.isLocallyNoetherian_isLocal_etale`,
  `AlgebraicGeometry.isLocal_isNormal_etalePrecoverage`,
  `AlgebraicGeometry.isRegular_isLocal_etale` and
  `AlgebraicGeometry.isNagataScheme_isLocal_etale`.

## Implementation notes

Items (1), (7), (9) and (10) already carry a locality statement for the étale precoverage
where they are proved, so they are only recorded against this remark. Items (2), (3), (4),
(6) and (8) carry one for a stronger topology — fppf for (2), syntomic for (3) and (4),
smooth for (6) and (8) — and are read off it through
`CategoryTheory.ObjectProperty.IsLocal.of_le`: locality for a coarser precoverage is the
weaker statement, so an inclusion of precoverages is all that is needed. Gorensteinness,
item (5), is the one item of the list with no locality statement in the library, so it is
proved here.

Gorensteinness of a scheme is local Noetherianity together with Gorensteinness of every
stalk. Local Noetherianity is item (1), and along an étale morphism the stalk condition at a
point of the source and at its image agree by
`AlgebraicGeometry.noetherianGorenstein_iff_of_etale`; a joint surjectivity argument on the
covering family turns the pointwise equivalence into the descent half. This proves the étale
case of Stacks 0C01, which states the syntomic case; the syntomic case is not formalized and
is not claimed here.

## References

* [Stacks Project, Tag 03E7](https://stacks.math.columbia.edu/tag/03E7)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- Every étale morphism of schemes is smooth, so every étale covering family is a smooth
covering family. -/
private theorem etalePrecoverage_le_smoothPrecoverage :
    Scheme.etalePrecoverage.{u} ≤
      Scheme.precoverage (@Smooth.{u} : MorphismProperty Scheme.{u}) :=
  Scheme.precoverage_mono fun _ _ f hf => by
    let : Etale f := hf
    infer_instance

/-! ### Item (1): locally Noetherian -/

add_to_stacks 03E7 "item (1): locally Noetherian, by Stacks 034C" isLocallyNoetherian_isLocal_etale

/-! ### Item (2): Jacobson -/

/-- **Stacks Project, Tag 03E7, item (2).** Being a Jacobson scheme is local for étale
coverings of schemes: a scheme is Jacobson if and only if the members of an étale covering
family are.

This is Stacks 0368, which gives the fppf case, read through the inclusion of the étale
precoverage in the fppf one. -/
@[stacks 03E7 "item (2): Jacobson, by Stacks 0368"]
instance jacobsonSpace_isLocal_etale :
    ObjectProperty.IsLocal (fun X : Scheme.{u} => JacobsonSpace X) Scheme.etalePrecoverage :=
  ObjectProperty.IsLocal.of_le Scheme.etalePrecoverage_le_fppfPrecoverage

/-! ### Item (3): locally Noetherian and `(S_k)` -/

/-- **Stacks Project, Tag 03E7, item (3).** Being locally Noetherian and satisfying Serre's
condition `(S_k)` is local for étale coverings of schemes.

This is Stacks 036A, which gives the syntomic case, read through the inclusion of the étale
precoverage in the syntomic one. -/
@[stacks 03E7 "item (3): locally Noetherian and (S_k), by Stacks 036A"]
instance isLocallyNoetherian_and_hasPropertySk_isLocal_etale (k : ℕ) :
    ObjectProperty.IsLocal
      (fun X : Scheme.{u} => ∃ h : IsLocallyNoetherian X, @HasPropertySk X h k)
      Scheme.etalePrecoverage :=
  ObjectProperty.IsLocal.of_le Scheme.etalePrecoverage_le_syntomicPrecoverage

/-! ### Item (4): Cohen-Macaulay -/

/-- **Stacks Project, Tag 03E7, item (4).** Being a Cohen-Macaulay scheme is local for étale
coverings of schemes.

This is Stacks 036B, which gives the syntomic case, read through the inclusion of the étale
precoverage in the syntomic one. -/
@[stacks 03E7 "item (4): Cohen-Macaulay, by Stacks 036B"]
instance isCohenMacaulay_isLocal_etale :
    ObjectProperty.IsLocal (fun X : Scheme.{u} => IsCohenMacaulay X) Scheme.etalePrecoverage :=
  ObjectProperty.IsLocal.of_le Scheme.etalePrecoverage_le_syntomicPrecoverage

/-! ### Item (5): Gorenstein -/

/-- A scheme étale over a Gorenstein scheme is Gorenstein: it is locally Noetherian because
an étale morphism is locally of finite type, and the Gorenstein condition on a stalk is
unchanged by an étale morphism. -/
theorem isGorenstein_of_etale {X Y : Scheme.{u}} (f : X ⟶ Y) [Etale f] [IsGorenstein Y] :
    IsGorenstein X := by
  have hN : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  refine (isGorenstein_iff X).2 ⟨hN, fun x => ?_⟩
  obtain ⟨hNx, hGx⟩ := (noetherianGorenstein_iff_of_etale f x).2
    ⟨inferInstance, IsGorenstein.isGorensteinLocalRing (f x)⟩
  exact hGx

/-- Gorensteinness of schemes is closed under isomorphisms, an isomorphism being étale. -/
private instance isGorenstein_isClosedUnderIsomorphisms :
    ObjectProperty.IsClosedUnderIsomorphisms (fun X : Scheme.{u} => IsGorenstein X) :=
  ⟨fun e hX => by
    have : IsGorenstein _ := hX
    exact isGorenstein_of_etale e.inv⟩

/-- **Stacks Project, Tag 03E7, item (5).** Being a Gorenstein scheme is local for étale
coverings of schemes: a scheme is Gorenstein if and only if the members of an étale covering
family are.

The source cites Stacks 0C01, which states the syntomic case; only the étale case is proved
here. Ascent is `AlgebraicGeometry.isGorenstein_of_etale`. For descent, local Noetherianity
of the base is item (1), and the Gorenstein condition on the stalk at a point of the base is
transported from a point of a member of the family above it. -/
@[stacks 03E7 "item (5): Gorenstein, the étale case of Stacks 0C01"]
instance isGorenstein_isLocal_etale :
    ObjectProperty.IsLocal (fun X : Scheme.{u} => IsGorenstein X) Scheme.etalePrecoverage where
  component {X R} hR Y f hf hX := by
    have : Etale f := hR.2 hf
    have : IsGorenstein X := hX
    exact isGorenstein_of_etale f
  of_presieve {X R} hR H := by
    have hN : IsLocallyNoetherian X :=
      ObjectProperty.of_presieve (P := fun X : Scheme.{u} => IsLocallyNoetherian X) hR
        fun _ _ hf => (H hf).toIsLocallyNoetherian
    refine (isGorenstein_iff X).2 ⟨hN, fun x => ?_⟩
    obtain ⟨Y, f, hf, y, hy⟩ :=
      (Presieve.mem_comap_jointlySurjectivePrecoverage_iff Scheme.forget).1 hR.1 x
    have : Etale f := hR.2 hf
    have hY : IsGorenstein Y := H hf
    subst hy
    obtain ⟨hNy, hGy⟩ := (noetherianGorenstein_iff_of_etale f y).1
      ⟨inferInstance, IsGorenstein.isGorensteinLocalRing y⟩
    exact hGy

/-! ### Item (6): reduced -/

add_to_stacks 03E7 "item (6): reduced, by Stacks 034E" isReduced_isLocal_etale

/-! ### Item (7): normal -/

add_to_stacks 03E7 "item (7): normal, by Stacks 034F" isLocal_isNormal_etalePrecoverage

/-! ### Item (8): locally Noetherian and `(R_k)` -/

/-- **Stacks Project, Tag 03E7, item (8).** Being locally Noetherian and regular in
codimension `k` is local for étale coverings of schemes.

This is Stacks 036C, which gives the smooth case, read through the inclusion of the étale
precoverage in the smooth one. -/
@[stacks 03E7 "item (8): locally Noetherian and (R_k), by Stacks 036C",
  ega "IV 17.5.8" "(iii), special case"]
instance isLocallyNoetherian_and_isRegularInCodimension_isLocal_etale (k : ℕ) :
    ObjectProperty.IsLocal
      (fun X : Scheme.{u} => IsLocallyNoetherian X ∧ IsRegularInCodimension X k)
      Scheme.etalePrecoverage :=
  ObjectProperty.IsLocal.of_le etalePrecoverage_le_smoothPrecoverage

/-! ### Item (9): regular -/

add_to_stacks 03E7 "item (9): regular, by Stacks 036D" isRegular_isLocal_etale

/-! ### Item (10): Nagata -/

add_to_stacks 03E7 "item (10): Nagata, by Stacks 036E" isNagataScheme_isLocal_etale

end AlgebraicGeometry
