module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.AdicCompletion.LocalRing
public import StacksFrontier.AlgebraicGeometry.Etale.NeighborhoodStalkFiber
public import StacksFrontier.AlgebraicGeometry.Morphisms.EtaleNeighbourhood.CompletedStalkHelpers

/-!
# The closed point of the spectrum of a completed local ring of a scheme

Let `S` be a scheme and `s` a point of it whose local ring `A := 𝒪_{S, s}` is Noetherian, and let
`Λ := A^∧` be the completion of `A` along its maximal ideal. The completion map `ν : A ⟶ Λ` is a
local homomorphism, so it induces a canonical morphism

`b := Spec ν ≫ S.fromSpecStalk s : Spec Λ ⟶ S`.

Two elementary facts about `b` are proved here: it carries the closed point of `Spec Λ` to `s`,
and it induces an isomorphism on residue fields there. Both are standing inputs of the Artin
approximation arguments, which read `Spec Λ ⟶ S` as a "formal neighbourhood of `s`": the first
says the formal neighbourhood is centred at `s`, the second that it does not enlarge the residue
field at that centre.

## Main results

* `StacksDraft.ArtinApproximation.specCompletedStalkToBase_closedPoint`: the canonical morphism
  `Spec 𝒪^∧_{S, s} ⟶ S` sends the closed point to `s`.
* `StacksDraft.ArtinApproximation.isIso_residueFieldMap_specCompletedStalkToBase`: it induces an
  isomorphism `κ(s) ≅ κ(𝒪^∧_{S, s})` of residue fields at the closed point.

## Implementation notes

*The Noetherian hypothesis is needed for the statements, not just the proofs.* Writing
`IsLocalRing.closedPoint 𝒪^∧_{S, s}` presupposes that the completion is a local ring, and
Mathlib derives that from `IsLocalRing A` together with finite generation of `𝔪_A`
(`AdicCompletion.isLocalRing_of_fg`). The hypothesis carried below is therefore
`IsNoetherianRing (S.presheaf.stalk s)` rather than `IsLocallyNoetherian S`: it is what both
statements need in order to typecheck, it is weaker, and for a locally Noetherian `S` it is
supplied by a Mathlib instance, so a consumer in that situation need not produce it.

*Splitting the residue field map.* `AlgebraicGeometry.Scheme.residueFieldMap_comp` factors the
residue field map of `b` into the one of `S.fromSpecStalk s` and the one of `Spec ν`. The first
factor is an isomorphism because `S.fromSpecStalk s` is a preimmersion, hence surjective on
stalks, which is
`AlgebraicGeometry.Scheme.Hom.isIso_residueFieldMap_of_surjectiveOnStalks`. The second factor is
*not* covered by that route — `A ⟶ Λ` is far from surjective on stalks — and is instead the
scheme-level avatar of the ring-theoretic statement that `κ(A) → κ(Λ)` is bijective, which is
Mathlib's `AdicCompletion.residueField_map_bijective`. The bridge between the two levels is
`isIso_specMap_residueFieldMap_closedPoint` below.

*How the bridge is proved.* `AlgebraicGeometry.Scheme.Hom.residueFieldMap` of a morphism is by
definition `IsLocalRing.ResidueField.map` of its stalk map, so it suffices to exhibit the stalk
map of `Spec.map φ` at the closed point as `φ` conjugated by two surjections: the germ on `⊤`
followed by `AlgebraicGeometry.Scheme.ΓSpecIso` on the source, and
`AlgebraicGeometry.stalkClosedPointIso` on the target. Surjectivity on residue fields then
follows by an element chase, and injectivity is automatic because the source is a field.

*Why the point is quantified over.* `IsLocalRing.closedPoint R` inhabits `↥(Spec R)` only after
unfolding `Spec`, so a goal mentioning it is not type-correct at the transparency level at which
`rw` and `simp` abstract their patterns, and both refuse to fire — the same obstruction recorded
in the implementation notes of
`StacksFrontier.AlgebraicGeometry.Etale.NeighborhoodStalkFiber`. The two auxiliary results that
need tactic rewriting are therefore stated for a *variable* point `q` of `Spec R`, with the
closed point substituted only in term mode.

## References

* [Stacks Project, Tag 0GDX](https://stacks.math.columbia.edu/tag/0GDX)
* [Stacks Project, Tag 0CAW](https://stacks.math.columbia.edu/tag/0CAW)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits IsLocalRing AdicCompletion

universe u

namespace StacksDraft.ArtinApproximation

/-- The germ on `⊤` composed with the stalk map of `Spec.map φ` at the closed point of `Spec B`
is `φ` itself, read through `AlgebraicGeometry.Scheme.ΓSpecIso` and
`AlgebraicGeometry.stalkClosedPointIso`. -/
private theorem germ_stalkMap_specMap_closedPoint {A B : CommRingCat.{u}} [IsLocalRing B]
    (φ : A ⟶ B) :
    (Spec A).presheaf.germ ⊤ (Spec.map φ (closedPoint B)) trivial ≫
        (Spec.map φ).stalkMap (closedPoint B) =
      (Scheme.ΓSpecIso A).hom ≫ φ ≫ (stalkClosedPointIso B).inv := by
  have hdef : (Spec.map φ).stalkMap (closedPoint B) =
      Scheme.stalkClosedPointTo (Spec.map φ) ≫ (stalkClosedPointIso B).inv := by
    rw [show Scheme.stalkClosedPointTo (Spec.map φ) =
      (Spec.map φ).stalkMap (closedPoint B) ≫ (stalkClosedPointIso B).hom from rfl,
      Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [hdef, ← Category.assoc, Scheme.germ_stalkClosedPointTo_Spec, Category.assoc]

/-- The form of `germ_stalkMap_specMap_closedPoint` in which the surjection from `B` onto the
stalk at the closed point has been moved to the right-hand side. -/
private theorem germ_comp_stalkMap_specMap_closedPoint {A B : CommRingCat.{u}} [IsLocalRing B]
    (φ : A ⟶ B) :
    ((Scheme.ΓSpecIso A).inv ≫
          (Spec A).presheaf.germ ⊤ (Spec.map φ (closedPoint B)) trivial) ≫
        (Spec.map φ).stalkMap (closedPoint B) =
      φ ≫ (stalkClosedPointIso B).inv := by
  rw [Category.assoc, germ_stalkMap_specMap_closedPoint, Iso.inv_hom_id_assoc]

/-- **The residue field bridge, for a variable point.** Let `φ : A ⟶ B` be a local homomorphism
of local rings such that `IsLocalRing.ResidueField.map φ` is surjective. If a point `q` of
`Spec B` admits a surjection `ι` from `B` onto the local ring at `q` and the stalk map of
`Spec.map φ` at `q` is `φ` followed by `ι`, up to a map `ψ` out of `A`, then `Spec.map φ`
induces an isomorphism of residue fields at `q`.

The point is quantified over so that `rw` and `simp` can fire; see the implementation notes. -/
private theorem isIso_specMap_residueFieldMap_aux {A B : CommRingCat.{u}}
    [IsLocalRing A] [IsLocalRing B] (φ : A ⟶ B) [IsLocalHom φ.hom]
    (hφ : Function.Surjective (ResidueField.map φ.hom)) (q : ↥(Spec B))
    (ι : B ⟶ (Spec B).presheaf.stalk q) [IsLocalHom ι.hom] (hι : Function.Surjective ι.hom)
    (ψ : A ⟶ (Spec A).presheaf.stalk (Spec.map φ q))
    (hψ : ψ ≫ (Spec.map φ).stalkMap q = φ ≫ ι) :
    IsIso ((Spec.map φ).residueFieldMap q) := by
  rw [ConcreteCategory.isIso_iff_bijective]
  refine ⟨((Spec.map φ).residueFieldMap q).hom.injective, fun y => ?_⟩
  obtain ⟨z, hz⟩ := (Spec B).residue_surjective q y
  obtain ⟨b, hb⟩ := hι z
  obtain ⟨w, hw⟩ := hφ (residue B b)
  obtain ⟨a, ha⟩ := IsLocalRing.residue_surjective (R := A) w
  refine ⟨((Spec A).residue (Spec.map φ q)).hom (ψ.hom a), ?_⟩
  have h1 := congrArg
    (fun g : (Spec A).presheaf.stalk (Spec.map φ q) ⟶ (Spec B).residueField q => g.hom (ψ.hom a))
    (Scheme.residue_residueFieldMap (Spec.map φ) q)
  have h2 := congrArg (fun g : A ⟶ (Spec B).presheaf.stalk q => g.hom a) hψ
  simp only [CommRingCat.comp_apply] at h1 h2
  rw [h1, h2]
  change ResidueField.map ι.hom (ResidueField.map φ.hom (residue A a)) = y
  rw [ha, hw]
  change ((Spec B).residue q).hom (ι.hom b) = y
  rw [hb]
  exact hz

/-- **The residue field bridge.** For a local homomorphism `φ : A ⟶ B` of local rings, the
residue field map of `Spec.map φ` at the closed point of `Spec B` is the scheme-level avatar of
`IsLocalRing.ResidueField.map φ`: if the latter is surjective — equivalently bijective, both
sides being fields — then the former is an isomorphism. -/
private theorem isIso_specMap_residueFieldMap_closedPoint {A B : CommRingCat.{u}}
    [IsLocalRing A] [IsLocalRing B] (φ : A ⟶ B) [IsLocalHom φ.hom]
    (hφ : Function.Surjective (ResidueField.map φ.hom)) :
    IsIso ((Spec.map φ).residueFieldMap (closedPoint B)) :=
  have : IsLocalRing ((Spec B).presheaf.stalk (closedPoint B)) :=
    (Spec B).toLocallyRingedSpace.isLocalRing _
  have : IsLocalHom (stalkClosedPointIso B).inv.hom :=
    .of_surjective _ (ConcreteCategory.bijective_of_isIso (stalkClosedPointIso B).inv).2
  isIso_specMap_residueFieldMap_aux φ hφ (closedPoint B) (stalkClosedPointIso B).inv
    (ConcreteCategory.bijective_of_isIso (stalkClosedPointIso B).inv).2 _
    (germ_comp_stalkMap_specMap_closedPoint φ)

/-- The residue field map of `Spec.map f ≫ X.fromSpecStalk x` at a point `q` of the spectrum is
an isomorphism as soon as the one of `Spec.map f` is: the second factor `X.fromSpecStalk x` is a
preimmersion, hence surjective on stalks, hence an isomorphism on residue fields everywhere.

The point is quantified over so that `rw` can fire; see the implementation notes. -/
private theorem isIso_residueFieldMap_specMap_fromSpecStalk {X : Scheme.{u}} {x : X}
    {R : CommRingCat.{u}} (f : X.presheaf.stalk x ⟶ R) (q : ↥(Spec R))
    (hq : IsIso ((Spec.map f).residueFieldMap q)) :
    IsIso ((Spec.map f ≫ X.fromSpecStalk x).residueFieldMap q) := by
  have h := (X.fromSpecStalk x).isIso_residueFieldMap_of_surjectiveOnStalks (Spec.map f q)
  rw [Scheme.residueFieldMap_comp]
  exact IsIso.comp_isIso' h hq

/-- The completion map of the stalk at `s` is a local homomorphism. -/
private instance isLocalHom_ofHom_algebraMap_completedStalk {S : Scheme.{u}} (s : S)
    [IsNoetherianRing (S.presheaf.stalk s)] :
    IsLocalHom (CommRingCat.ofHom (algebraMap (S.presheaf.stalk s)
      (AdicCompletion (maximalIdeal (S.presheaf.stalk s)) (S.presheaf.stalk s)))).hom :=
  inferInstanceAs (IsLocalHom (algebraMap (S.presheaf.stalk s)
    (AdicCompletion (maximalIdeal (S.presheaf.stalk s)) (S.presheaf.stalk s))))

/-- **The formal neighbourhood is centred at `s`.** The canonical morphism
`Spec 𝒪^∧_{S, s} ⟶ S` out of the spectrum of the completed local ring carries the closed point
to `s`. -/
public theorem specCompletedStalkToBase_closedPoint {S : Scheme.{u}} (s : S)
    [IsNoetherianRing (S.presheaf.stalk s)] :
    (Spec.map (CommRingCat.ofHom (algebraMap (S.presheaf.stalk s)
        (AdicCompletion (maximalIdeal (S.presheaf.stalk s)) (S.presheaf.stalk s)))) ≫
      S.fromSpecStalk s)
      (closedPoint (AdicCompletion (maximalIdeal (S.presheaf.stalk s))
        (S.presheaf.stalk s))) = s :=
  specMap_fromSpecStalk_closedPoint _

/-- **The formal neighbourhood does not enlarge the residue field.** The canonical morphism
`Spec 𝒪^∧_{S, s} ⟶ S` induces an isomorphism of residue fields at the closed point of
`Spec 𝒪^∧_{S, s}`. -/
public theorem isIso_residueFieldMap_specCompletedStalkToBase {S : Scheme.{u}} (s : S)
    [IsNoetherianRing (S.presheaf.stalk s)] :
    IsIso ((Spec.map (CommRingCat.ofHom (algebraMap (S.presheaf.stalk s)
        (AdicCompletion (maximalIdeal (S.presheaf.stalk s)) (S.presheaf.stalk s)))) ≫
      S.fromSpecStalk s).residueFieldMap
      (closedPoint (AdicCompletion (maximalIdeal (S.presheaf.stalk s))
        (S.presheaf.stalk s)))) :=
  isIso_residueFieldMap_specMap_fromSpecStalk _ _
    (isIso_specMap_residueFieldMap_closedPoint _
      (AdicCompletion.residueField_map_bijective (S.presheaf.stalk s)).2)

end StacksDraft.ArtinApproximation

end
