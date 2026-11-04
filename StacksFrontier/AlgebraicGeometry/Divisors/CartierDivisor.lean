module

public import StacksFrontier.AlgebraicGeometry.Divisors.Meromorphic.TotalQuotient
public import StacksFrontier.Topology.Sheaves.Cohomology.Torsors.GeneratorsOfARankOneModule

/-!
# Cartier divisors and the unit-sheaf sequence of the total quotient sheaf

For a sheaf of commutative rings `O` on a topological space, the groups of units of its rings
of sections form a presheaf of abelian groups, written additively.  A morphism of sheaves of
rings induces a morphism of these presheaves, and sheafifying gives the *unit-group sheaf*
`O^*`.  When the morphism is a monomorphism the resulting sequence of unit-group sheaves is
short exact, with the quotient the sheafification of the sectionwise cokernel.

Applied to the canonical morphism `𝒪_X ⟶ 𝒦_X` from the structure sheaf of a scheme to its
sheaf of total quotient rings, this is the short exact sequence

`0 ⟶ 𝒪_X^* ⟶ 𝒦_X^* ⟶ 𝒦_X^*/𝒪_X^* ⟶ 0`

and a *Cartier divisor* on `X` is a global section of the quotient `𝒦_X^*/𝒪_X^*`.

## Main definitions

* `AlgebraicGeometry.unitGroupPresheaf`: the presheaf of unit groups of a sheaf of rings.
* `AlgebraicGeometry.unitGroupSheaf`: its sheafification, the unit-group sheaf.
* `AlgebraicGeometry.unitGroupMap`, `AlgebraicGeometry.unitGroupSheafMap`: the induced maps.
* `AlgebraicGeometry.unitGroupQuotientSheaf`, `AlgebraicGeometry.unitGroupQuotientMap`: the
  quotient by the image, and the projection onto it.
* `AlgebraicGeometry.Scheme.CartierDivisor`: the Cartier divisors of a scheme.

## Main results

* `AlgebraicGeometry.mono_toTotalQuotientSheaf` and
  `AlgebraicGeometry.Scheme.mono_toTotalQuotientSheaf`: a sheaf of rings is a subsheaf of its
  sheaf of total quotient rings.
* `AlgebraicGeometry.mono_unitGroupMap`: a monomorphism of sheaves of rings induces a
  monomorphism of unit-group presheaves.
* `AlgebraicGeometry.shortExact_unitGroupSheaf` and
  `AlgebraicGeometry.Scheme.shortExact_unitGroupSheaf`: the sequence of unit-group sheaves of a
  monomorphism of sheaves of rings is short exact.

## Implementation notes

The functor taking a commutative ring to its group of units, written additively, is
`Stacks.Cohomology.Generators.unitsAddCommGrpFunctor`.  The unit-group sheaf of this file is for
an arbitrary sheaf of commutative rings on a topological space, where
`Stacks.Cohomology.Generators.unitsSheaf` is for the structure sheaf of a ringed space and
`AlgebraicGeometry.RingedSite.unitsSheaf` for the structure sheaf of a ringed site; the sequence
is needed at the sheaf of total quotient rings, which is not the structure sheaf of either.

Unit groups are written additively so that the quotient can be formed in an abelian category;
the underlying elements are unchanged.  Monomorphy of the map on unit groups is checked
sectionwise and reduces to injectivity of `Units.map` along an injective ring map, and short
exactness is the image of the presheaf-level cokernel sequence under sheafification, which is
exact because sheafification preserves finite limits and finite colimits.

## References

* [Stacks Project, Tag 02AR](https://stacks.math.columbia.edu/tag/02AR)
* [Stacks Project, Tag 01X4](https://stacks.math.columbia.edu/tag/01X4)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace AlgebraicGeometry

variable {X : TopCat.{u}}

/-- Sheaves of abelian groups on a topological space admit sheafification. -/
local instance hasSheafifyAddCommGrpCat (Y : TopCat.{u}) :
    HasSheafify (Opens.grothendieckTopology Y) AddCommGrpCat.{u} :=
  hasSheafifyEssentiallySmallSite _ _

/-- The presheaf of unit groups of a sheaf of commutative rings, written additively. -/
abbrev unitGroupPresheaf (F : TopCat.Sheaf CommRingCat.{u} X) :
    (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u} :=
  F.obj ⋙ Stacks.Cohomology.Generators.unitsAddCommGrpFunctor

/-- The map of unit-group presheaves induced by a morphism of sheaves of commutative rings. -/
def unitGroupMap {F G : TopCat.Sheaf CommRingCat.{u} X} (f : F ⟶ G) :
    unitGroupPresheaf F ⟶ unitGroupPresheaf G :=
  Functor.whiskerRight f.hom Stacks.Cohomology.Generators.unitsAddCommGrpFunctor

/-- The unit-group sheaf `F^*` of a sheaf of commutative rings. -/
def unitGroupSheaf (F : TopCat.Sheaf CommRingCat.{u} X) : TopCat.Sheaf AddCommGrpCat.{u} X :=
  (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj (unitGroupPresheaf F)

/-- The map of unit-group sheaves induced by a morphism of sheaves of commutative rings. -/
def unitGroupSheafMap {F G : TopCat.Sheaf CommRingCat.{u} X} (f : F ⟶ G) :
    unitGroupSheaf F ⟶ unitGroupSheaf G :=
  (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).map (unitGroupMap f)

/-- The quotient of the unit-group sheaf of the target by the image of the unit-group sheaf of
the source: the sheafification of the sectionwise cokernel. -/
def unitGroupQuotientSheaf {F G : TopCat.Sheaf CommRingCat.{u} X} (f : F ⟶ G) :
    TopCat.Sheaf AddCommGrpCat.{u} X :=
  (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
    (cokernel (unitGroupMap f))

/-- The projection of the unit-group sheaf of the target onto the quotient. -/
def unitGroupQuotientMap {F G : TopCat.Sheaf CommRingCat.{u} X} (f : F ⟶ G) :
    unitGroupSheaf G ⟶ unitGroupQuotientSheaf f :=
  (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).map
    (cokernel.π (unitGroupMap f))

/-- A sheaf of commutative rings is a subsheaf of its sheaf of total quotient rings. -/
theorem mono_toTotalQuotientSheaf (O : TopCat.Sheaf CommRingCat.{u} X) :
    Mono (toTotalQuotientSheaf O) := by
  let J := Opens.grothendieckTopology X
  let f := O.presheaf.toTotalQuotientPresheaf
  have : PreservesFiniteLimits (presheafToSheaf J CommRingCat.{u}) := inferInstance
  have : Mono f := inferInstance
  have : Mono (sheafifyMap J f) := by
    dsimp [sheafifyMap, sheafify]
    infer_instance
  have : IsIso (toSheafify J O.presheaf) := isIso_toSheafify J O.property
  apply (sheafToPresheaf J CommRingCat.{u}).mono_of_mono_map
  change Mono (f ≫ toSheafify J O.presheaf.totalQuotientPresheaf)
  rw [toSheafify_naturality]
  infer_instance

/-- A monomorphism of sheaves of commutative rings induces a monomorphism of unit-group
presheaves: it is injective on sections, hence on unit groups. -/
theorem mono_unitGroupMap {F G : TopCat.Sheaf CommRingCat.{u} X} (f : F ⟶ G) [Mono f] :
    Mono (unitGroupMap f) := by
  rw [NatTrans.mono_iff_mono_app]
  intro U
  dsimp [unitGroupMap, unitGroupPresheaf, Functor.whiskerRight_app]
  apply ConcreteCategory.mono_of_injective
  intro a b hab
  have : Mono (f.hom.app U) :=
    (NatTrans.mono_iff_mono_app _).mp
      (Functor.map_mono (TopCat.Sheaf.forget CommRingCat.{u} X) f) U
  have hg : Function.Injective (f.hom.app U).hom.toMonoidHom := by
    simpa using ConcreteCategory.injective_of_mono_of_preservesPullback (f.hom.app U)
  exact Units.map_injective hg (congrArg Additive.toMul hab)

/-- The sequence of unit-group sheaves of a monomorphism of sheaves of commutative rings is
short exact: sheafification is exact, and the presheaf-level sequence is the cokernel sequence
of a monomorphism. -/
theorem shortExact_unitGroupSheaf {F G : TopCat.Sheaf CommRingCat.{u} X} (f : F ⟶ G)
    [Mono f] :
    (ShortComplex.mk (unitGroupSheafMap f) (unitGroupQuotientMap f) (by
      change (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).map
          (unitGroupMap f) ≫
        (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).map
          (cokernel.π (unitGroupMap f)) = 0
      rw [← Functor.map_comp]
      simp)).ShortExact := by
  let J := Opens.grothendieckTopology X
  let S := presheafToSheaf J AddCommGrpCat.{u}
  let g := unitGroupMap f
  change ((ShortComplex.cokernelSequence g).map S).ShortExact
  exact (ShortComplex.ShortExact.mk' (ShortComplex.cokernelSequence_exact g)
    (mono_unitGroupMap f) inferInstance).map_of_exact S

/-- **Stacks 02AR part (6).** The structure sheaf of a scheme is a subsheaf of its sheaf of
total quotient rings. -/
@[stacks 02AR "unit_sheaf_sequence"]
theorem Scheme.mono_toTotalQuotientSheaf (Y : Scheme.{u}) :
    Mono Y.toTotalQuotientSheaf :=
  _root_.AlgebraicGeometry.mono_toTotalQuotientSheaf Y.sheaf

/-- **Stacks 02AR part (6).** The sequence `0 ⟶ 𝒪_X^* ⟶ 𝒦_X^* ⟶ 𝒦_X^*/𝒪_X^* ⟶ 0` of
unit-group sheaves of a scheme is short exact. -/
@[stacks 02AR "unit_sheaf_sequence"]
theorem Scheme.shortExact_unitGroupSheaf (Y : Scheme.{u}) :
    (ShortComplex.mk (unitGroupSheafMap Y.toTotalQuotientSheaf)
      (unitGroupQuotientMap Y.toTotalQuotientSheaf) (by
        change (presheafToSheaf (Opens.grothendieckTopology Y.toPresheafedSpace)
            AddCommGrpCat.{u}).map (unitGroupMap Y.toTotalQuotientSheaf) ≫
          (presheafToSheaf (Opens.grothendieckTopology Y.toPresheafedSpace)
            AddCommGrpCat.{u}).map
            (cokernel.π (unitGroupMap Y.toTotalQuotientSheaf)) = 0
        rw [← Functor.map_comp]
        simp)).ShortExact :=
  have := Y.mono_toTotalQuotientSheaf
  _root_.AlgebraicGeometry.shortExact_unitGroupSheaf Y.toTotalQuotientSheaf

/-- **Stacks 02AR part (7).** A Cartier divisor on a scheme is a global section of the quotient
sheaf `𝒦_X^*/𝒪_X^*`. -/
@[stacks 02AR "cartier_divisor"]
abbrev Scheme.CartierDivisor (Y : Scheme.{u}) : Type u :=
  (unitGroupQuotientSheaf Y.toTotalQuotientSheaf).obj.obj (op ⊤)

end AlgebraicGeometry

end
