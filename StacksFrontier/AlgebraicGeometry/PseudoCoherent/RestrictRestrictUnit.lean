module

public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.RestrictRestrict

/-!
# The comparison across one level of restriction preserves strict perfection

Let `X` be a ringed space, let `U` be an open of `X`, and let `D` be a pair of corresponding opens
(`AlgebraicGeometry.RingedSpace.CorrespondingOpens`): an open `W ≤ U` of `X` together with the open
`V` of `X|U` corresponding to it. The comparison functor
`AlgebraicGeometry.RingedSpace.CorrespondingOpens.compare` is an equivalence
`OXMod ((X|U)|V) ≌ OXMod (X|W)`, so it is additive and exact for free; what it does to the
*structure* module is extra information, and that is what this file supplies.

The comparison is the pushforward of sheaves of modules along the comparison of structure sheaves
of rings `AlgebraicGeometry.RingedSpace.CorrespondingOpens.structureSheafCompare`, whose component
at an open `Z` of `W` is `𝒪_X` applied to the inclusion of the image of the preimage of `Z` in `V`
into the image of `Z` in `X`. Those two opens of `X` are *equal*
(`AlgebraicGeometry.RingedSpace.CorrespondingOpens.image_eq_base`), so that component is an
isomorphism of rings, and the pushforward of the unit sheaf of modules along an isomorphism of
sheaves of rings is the unit sheaf of modules.

## Main definitions

* `ModuleCat.restrictScalarsSelfHom` and `ModuleCat.restrictScalarsSelfIso`: a ring homomorphism
  `f : A ⟶ B` is an `A`-linear map from `A` to `B` with its scalars restricted along `f`, and it is
  an isomorphism of `A`-modules as soon as `f` is an isomorphism of rings.
* `AlgebraicGeometry.RingedSpace.CorrespondingOpens.unitIso` is the identification
  `Φ 𝒪_{(X|U)|V} ≅ 𝒪_{X|W}`.

## Main results

* `AlgebraicGeometry.RingedSpace.CorrespondingOpens.isIso_structureSheafCompare_app`: the
  comparison of structure sheaves of rings is an isomorphism in each degree.
* `AlgebraicGeometry.RingedSpace.CorrespondingOpens.isDirectSummandOfFiniteFree_compare` and
  `AlgebraicGeometry.RingedSpace.CorrespondingOpens.isStrictlyPerfect_compare`: `Φ` preserves
  being a direct summand of a finite free module, and carries strictly perfect complexes to
  strictly perfect complexes.

## Implementation notes

`AlgebraicGeometry.RingedSpace.CorrespondingOpens.isIso_structureSheafCompare_app` is proved by
`Subsingleton.elim`: the morphism of opens inducing it has the same source and target as the
identity, because `TopologicalSpace.Opens X.carrier` is a poset, so the induced map on sections is
the identity.

The inverse of `ModuleCat.restrictScalarsSelfIso` is *not* built by hand. The scalar
multiplication of a `ModuleCat.restrictScalars` module is not reachable by rewriting at the
spelling in which it arises here, so the inverse's semilinearity is awkward; instead the forward
map is shown to be an isomorphism from bijectivity of the underlying function, through
`CategoryTheory.ConcreteCategory.isIso_iff_bijective`.

`AlgebraicGeometry.RingedSpace.CorrespondingOpens.isDirectSummandOfFiniteFree_compare` follows
`AlgebraicGeometry.RingedSpace.isDirectSummandOfFiniteFree_restrictModulesOfLE` verbatim: a
retract of `𝒪^{⊕n}` is carried to a retract of the image of `𝒪^{⊕n}`, which is a retract of
`⨁ⁿ 𝒪` because `Φ` is additive (`CategoryTheory.Functor.retractMapBiproduct`) and takes the
structure module to the structure module.

## References

* [Stacks Project, Definition 20.46.1 (Tag 08C4)](https://stacks.math.columbia.edu/tag/08C4)
* [Stacks Project, Lemma 20.49.2 (Tag 09VA)](https://stacks.math.columbia.edu/tag/09VA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace StrictlyPerfect

universe u

namespace ModuleCat

/-- **A ring homomorphism `f : A ⟶ B` as an `A`-linear map `A ⟶ B`**, the target carrying the
`A`-module structure obtained by restricting scalars along `f`. Its `A`-semilinearity is the
multiplicativity of `f`. -/
public def restrictScalarsSelfHom {A B : RingCat.{u}} (f : A ⟶ B) :
    ModuleCat.of A A ⟶ (ModuleCat.restrictScalars f.hom).obj (ModuleCat.of B B) :=
  ModuleCat.semilinearMapAddEquiv f.hom (ModuleCat.of A A) (ModuleCat.of B B)
    f.hom.toSemilinearMap

/-- `ModuleCat.restrictScalarsSelfHom` of an isomorphism of rings is an isomorphism of modules:
its underlying function is that of the ring isomorphism, hence bijective. -/
public instance isIso_restrictScalarsSelfHom {A B : RingCat.{u}} (f : A ⟶ B) [IsIso f] :
    IsIso (restrictScalarsSelfHom f) := by
  rw [ConcreteCategory.isIso_iff_bijective]
  exact ConcreteCategory.bijective_of_isIso f

/-- **An isomorphism of rings `f : A ≅ B` identifies `A` with `B` with its scalars restricted
along `f`**, as `A`-modules. -/
public def restrictScalarsSelfIso {A B : RingCat.{u}} (f : A ⟶ B) [IsIso f] :
    ModuleCat.of A A ≅ (ModuleCat.restrictScalars f.hom).obj (ModuleCat.of B B) :=
  asIso (restrictScalarsSelfHom f)

end ModuleCat

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace.{u, u}}

/-- The map on `𝒪_X`-sections induced by a morphism of opens of `X` between two opens which are
*equal* is an isomorphism: the morphism is the identity, because
`TopologicalSpace.Opens X.carrier` is a poset. -/
public theorem isIso_presheaf_map_of_eq {A B : Opens X.carrier} (e : A = B) (f : A ⟶ B) :
    IsIso ((forget₂ CommRingCat.{u} RingCat.{u}).map (X.presheaf.map f.op)) := by
  subst e
  rw [Subsingleton.elim f (𝟙 _), op_id, CategoryTheory.Functor.map_id,
    CategoryTheory.Functor.map_id]
  infer_instance

namespace CorrespondingOpens

variable {U : Opens X.carrier} (D : CorrespondingOpens X U)

/-! ### The comparison of structure sheaves of rings is an isomorphism -/

/-- **The comparison of structure sheaves of rings is an isomorphism in each degree.** Its
component at an open `Z` of `W` is the map on `𝒪_X`-sections induced by the inclusion
`AlgebraicGeometry.RingedSpace.CorrespondingOpens.opensCompare`, whose source and target are equal
by `AlgebraicGeometry.RingedSpace.CorrespondingOpens.image_eq_base`. -/
public instance isIso_structureSheafCompare_app (Z : (Opens (D.basespace).carrier)ᵒᵖ) :
    IsIso ((D.structureSheafCompare).hom.app Z) :=
  isIso_presheaf_map_of_eq (D.image_eq_base Z.unop) _

/-! ### The comparison takes the structure module to the structure module -/

/-- `AlgebraicGeometry.RingedSpace.CorrespondingOpens.unitIso` on underlying presheaves of
modules: over an open `Z` of `W` the sections of `𝒪_{X|W}` are the sections of `𝒪_X` over the
image of `Z` in `X`, and the sections of `Φ 𝒪_{(X|U)|V}` are the sections of `𝒪_X` over an open
of `X` equal to that image; the comparison between them is the isomorphism of rings
`AlgebraicGeometry.RingedSpace.CorrespondingOpens.structureSheafCompare` read as a map of
modules. -/
public def unitIsoVal :
    (structureModule (D.basespace)).val ≅ ((D.compare).obj (structureModule (D.subspace))).val :=
  PresheafOfModules.isoMk (fun Z => ModuleCat.restrictScalarsSelfIso
      ((D.structureSheafCompare).hom.app Z))
    (fun {_ _} k => ModuleCat.hom_ext (LinearMap.ext fun x =>
      ConcreteCategory.congr_hom ((D.structureSheafCompare).hom.naturality k) x))

/-- **`Φ` takes the structure module to the structure module**, `Φ 𝒪_{(X|U)|V} ≅ 𝒪_{X|W}`.

This is the one thing beyond exactness that the descent argument of Stacks 09VA needs from the
comparison: with it, `Φ` carries strictly perfect complexes to strictly perfect complexes. -/
public def unitIso :
    (D.compare).obj (structureModule (D.subspace)) ≅ structureModule (D.basespace) :=
  ((SheafOfModules.fullyFaithfulForget (structureSheafOfRings (D.basespace))).preimageIso
    (X := structureModule (D.basespace))
    (Y := (D.compare).obj (structureModule (D.subspace))) (D.unitIsoVal)).symm

/-! ### Strict perfection -/

/-- **`Φ` preserves being a direct summand of a finite free module.** A retract of `𝒪^{⊕n}` is
carried to a retract of `Φ(𝒪^{⊕n})`, which is a retract of `⨁ⁿ 𝒪_{X|W}` because `Φ` is additive
and takes the structure module to the structure module. -/
public theorem isDirectSummandOfFiniteFree_compare {A : OXMod.{u, u} (D.subspace)}
    (hA : IsDirectSummandOfFiniteFree A) :
    IsDirectSummandOfFiniteFree ((D.compare).obj A) := by
  obtain ⟨n, ⟨ρ⟩⟩ := (isDirectSummandOfFiniteFree_iff_retract _).mp hA
  exact (isDirectSummandOfFiniteFree_iff_retract _).mpr
    ⟨n, ⟨(ρ.map (D.compare)).trans
      (((D.compare).retractMapBiproduct
          (fun _ : Fin n => structureModule (D.subspace))).trans
        (Retract.ofIso (biproduct.mapIso fun _ => D.unitIso)))⟩⟩

/-- **`Φ` carries a strictly perfect complex of `𝒪_{(X|U)|V}`-modules to a strictly perfect
complex of `𝒪_{X|W}`-modules**: it takes a zero term to a zero term, so the complex stays
bounded, and it preserves being a direct summand of a finite free module. -/
public theorem isStrictlyPerfect_compare {P : CochainComplex (OXMod.{u, u} (D.subspace)) ℤ}
    (hP : IsStrictlyPerfect P) :
    IsStrictlyPerfect (((D.compare).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) where
  bounded := hP.bounded.subset fun _ hi hz => hi ((D.compare).isZero_obj hz)
  directSummand i := D.isDirectSummandOfFiniteFree_compare (hP.directSummand i)

end CorrespondingOpens

end AlgebraicGeometry.RingedSpace

end
