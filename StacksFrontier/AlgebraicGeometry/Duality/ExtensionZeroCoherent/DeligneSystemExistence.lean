module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryHomology
public import StacksFrontier.AlgebraicGeometry.DerivedCoherent.CoherentComplexRepresentative
public import StacksFrontier.AlgebraicGeometry.Duality.ExtensionZeroCoherent.DeligneSystemRestrictionLifting
public import StacksFrontier.AlgebraicGeometry.Duality.ExtensionZeroCoherent.DeligneSystemTriangleExtensionCoherent
public import StacksFrontier.AlgebraicGeometry.Duality.ExtensionZeroCoherent.RestrictFunctorOpensRange
public import StacksFrontier.AlgebraicGeometry.Duality.ExtensionZeroCoherent.RestrictionLiftingColimit
public import StacksFrontier.AlgebraicGeometry.Duality.ExtensionZeroCoherent.RestrictionHomColimit

/-!
# Deligne systems with a prescribed value

Let `j : U ⟶ X` be an open immersion of Noetherian schemes. A Deligne system `(K_n)` is the
system `(𝓘^n𝓕^•)` of ideal-power subcomplexes of a bounded complex `𝓕^•` of coherent
`𝒪_X`-modules, for a quasi-coherent ideal sheaf `𝓘` cutting out `X ∖ U`. Since `𝓘` is the unit
ideal on `U`, the inclusions `𝓘^n𝓕^• ⟶ 𝓕^•` restrict to isomorphisms on `U`, so the restricted
system `(K_n|_U)` is constant with value `𝓕^•|_U`, an object of `D^b_{Coh}(𝒪_U)`.

This file proves that every object of `D^b_{Coh}(𝒪_U)` is the value of a Deligne system,
[Stacks, Tag 0G4L] (2). The source's proof: extend the object to `X` (Stacks 0G48), represent the
extension by a bounded complex of coherent modules (Stacks 0FDB), and take its ideal-power
system. Here the two steps are taken in the other order, at the level of complexes: the object
is represented on `U` by a bounded complex of coherent `𝒪_U`-modules (Stacks 0FDB on `U`), which
is transported to the open subscheme `j.opensRange` and extended to a bounded complex of coherent
`𝒪_X`-modules: `AlgebraicGeometry.exists_bounded_isCoherent_complex_restrict_Q_iso`, the
complex-level form of Stacks 0G48.

Together with Stacks 0G2H this gives the Deligne-system assignment
`AlgebraicGeometry.DeligneSystem.values` of `CategoryTheory.DeligneSystemValues`, through which
the general two-out-of-three argument of
`StacksFrontier.AlgebraicGeometry.Duality.ExtensionZeroCoherent.DeligneSystemTriangles` applies to
schemes, and the identification of being pro-isomorphic to a Deligne system with being
pro-isomorphic to an assigned one.

## Main definitions

* `AlgebraicGeometry.DeligneSystem.values`: the Deligne-system assignment `K ↦ (K_n)`.
* `AlgebraicGeometry.ProIsoDeligneSystem`: being pro-isomorphic to a Deligne system.

The restriction `AlgebraicGeometry.restrictBoundedCoherentLift : D^b_{Coh}(𝒪_X) ⥤ D^b_{Coh}(𝒪_U)`,
the value `AlgebraicGeometry.DeligneSystem.value` of a Deligne system and the identification
`AlgebraicGeometry.DeligneSystem.restrictIsoConst` of its restriction with the constant system
are in
`StacksFrontier.AlgebraicGeometry.Duality.ExtensionZeroCoherent.DeligneSystemTriangleExtension`.

## Main results

* `AlgebraicGeometry.DeligneSystem.exists_restrictIso`: **[Stacks, Tag 0G4L] (2)**.
* `AlgebraicGeometry.DeligneSystem.proObjectIsoValues`: a Deligne system is pro-isomorphic to the
  assigned Deligne system of its value.
* `AlgebraicGeometry.proIsoDeligneSystem_iff`.
* `AlgebraicGeometry.ProIsoDeligneSystem.of_natIso`: being pro-isomorphic to a Deligne system
  only depends on the isomorphism class of the inverse system.

## References

* [Stacks Project, Tag 0G4L](https://stacks.math.columbia.edu/tag/0G4L)
* [Stacks Project, Tag 0G48](https://stacks.math.columbia.edu/tag/0G48)
* [Stacks Project, Tag 0FDB](https://stacks.math.columbia.edu/tag/0FDB)
* [Stacks Project, Tag 0G2H](https://stacks.math.columbia.edu/tag/0G2H)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

attribute [local instance 10000] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry

variable {U X : Scheme.{u}}

namespace DeligneSystem

/-- **Stacks Project, Tag 0G4L (2).** Let `j : U ⟶ X` be an open immersion of Noetherian schemes.
Given `K` in `D^b_{Coh}(𝒪_U)`, there exists a Deligne system `(K_n)` such that `(K_n|_U)` is
constant with value `K`.

As in the source, `K` is the restriction of a bounded complex `𝓕^•` of coherent `𝒪_X`-modules
(`AlgebraicGeometry.exists_bounded_isCoherent_complex_restrict_Q_iso`, which rests on Stacks 0G48
and Stacks 0FDB), the ideal sheaf is that of the reduced closed complement of `U`, and the Deligne
system is `(𝓘^n𝓕^•)`, `AlgebraicGeometry.DeligneTriangle.deligneSystemOfComplex`. -/
@[stacks 0G4L "(2)"]
public theorem exists_restrictIso (j : U ⟶ X) [IsOpenImmersion j] [IsNoetherian X]
    (K : BoundedCoherentDerived U) :
    ∃ D : DeligneSystem j, Nonempty (D.system ⋙ restrictBoundedCoherent j ≅
      (Functor.const ℕᵒᵖ).obj ((boundedCoherentDerived U).ι.obj K)) := by
  obtain ⟨𝒢, hcoh, hGE, hLE, ⟨e⟩⟩ := exists_bounded_isCoherent_complex_restrict_Q_iso j K
  set Z : TopologicalSpace.Closeds X := j.opensRange.compl with hZdef
  have hZ : (Z : Set X) = (Set.range j.base)ᶜ := rfl
  set I := Scheme.IdealSheafData.vanishingIdeal Z with hIdef
  have hI : (I.support : Set X) = (Set.range j.base)ᶜ :=
    (Scheme.IdealSheafData.coe_support_vanishingIdeal Z).trans hZ
  let D := DeligneTriangle.deligneSystemOfComplex j I hI 𝒢 hGE hLE hcoh
  exact ⟨D, ⟨D.restrictIsoConst ≪≫ (Functor.const ℕᵒᵖ).mapIso e⟩⟩

variable {j : U ⟶ X} [IsOpenImmersion j] [IsNoetherian X]

/-- `AlgebraicGeometry.DeligneSystem.restrictionLifting` (Stacks 0G2H, elementwise) for the
restriction functor with values in `D^b_{Coh}(𝒪_U)`. -/
public lemma restrictionLifting_lift (D : DeligneSystem j) (N : BoundedCoherentDerived X) :
    RestrictionLifting D.system (restrictBoundedCoherentLift j) N :=
  RestrictionLifting.of_comp_fullyFaithful (boundedCoherentDerived U).ι (D.restrictionLifting N)

/-- An identification of a restricted system with a constant system of `D(𝒪_U)` whose value lies
in `D^b_{Coh}(𝒪_U)`, read in `D^b_{Coh}(𝒪_U)`. -/
public def liftRestrictIso {F : ℕᵒᵖ ⥤ BoundedCoherentDerived X} {K : BoundedCoherentDerived U}
    (e : F ⋙ restrictBoundedCoherent j ≅
      (Functor.const ℕᵒᵖ).obj ((boundedCoherentDerived U).ι.obj K)) :
    F ⋙ restrictBoundedCoherentLift j ≅ (Functor.const ℕᵒᵖ).obj K :=
  NatIso.ofComponents (fun n => (boundedCoherentDerived U).fullyFaithfulι.preimageIso (e.app n))
    (fun {n m} f => (boundedCoherentDerived U).ι.map_injective (by
      simpa using e.hom.naturality f))

/-- **The Deligne system with a prescribed value** `K` in `D^b_{Coh}(𝒪_U)`, chosen by Stacks
0G4L (2), `AlgebraicGeometry.DeligneSystem.exists_restrictIso`. -/
public def ofValue (j : U ⟶ X) [IsOpenImmersion j] [IsNoetherian X]
    (K : BoundedCoherentDerived U) : DeligneSystem j :=
  (exists_restrictIso j K).choose

/-- The restriction of `AlgebraicGeometry.DeligneSystem.ofValue j K` to `U` is the constant system
at `K`. -/
public def ofValueRestrictIso (j : U ⟶ X) [IsOpenImmersion j] [IsNoetherian X]
    (K : BoundedCoherentDerived U) :
    (ofValue j K).system ⋙ restrictBoundedCoherent j ≅
      (Functor.const ℕᵒᵖ).obj ((boundedCoherentDerived U).ι.obj K) :=
  (exists_restrictIso j K).choose_spec.some

/-- **The Deligne-system assignment of an open immersion of Noetherian schemes.** To an object `K`
of `D^b_{Coh}(𝒪_U)` it assigns the Deligne system `AlgebraicGeometry.DeligneSystem.ofValue j K`
of Stacks 0G4L (2); the identification of Stacks 0G2H for it is
`AlgebraicGeometry.DeligneSystem.restrictionLifting`, read as a colimit cocone by
`CategoryTheory.isColimitRestrictionHomCocone`. -/
public def values (j : U ⟶ X) [IsOpenImmersion j] [IsNoetherian X] :
    DeligneSystemValues (restrictBoundedCoherentLift j) where
  system K := (ofValue j K).system
  restrictIso K := liftRestrictIso (ofValueRestrictIso j K)
  isColimit K N :=
    isColimitRestrictionHomCocone _ _ _ _ _ ((ofValue j K).restrictionLifting_lift N)

/-- The functor of points of the pro-object of a Deligne system is `N ↦ Hom_U(K, N|_U)`, where `K`
is its value: this is Stacks 0G2H as an isomorphism of functors. -/
public def homIsoValue (D : DeligneSystem j) :
    Pro.seqHomColim D.system ≅ restrictBoundedCoherentLift j ⋙ coyoneda.obj (op D.value) :=
  restrictHomIso D.system (restrictBoundedCoherentLift j) D.value
    (liftRestrictIso D.restrictIsoConst) D.restrictionLifting_lift

/-- **Every Deligne system is pro-isomorphic to the assigned Deligne system of its value**: both
pro-objects have the functor of points `N ↦ Hom_U(K, N|_U)`, by Stacks 0G2H, so they are
isomorphic by the co-Yoneda lemma. -/
public def proObjectIsoValues (D : DeligneSystem j) :
    D.proObject ≅ ProSeq.of ((values j).system D.value) :=
  ProSeq.isoOfSeqHomColimIso (D.homIsoValue ≪≫ ((values j).systemHomIso D.value).symm)

end DeligneSystem

variable {j : U ⟶ X} [IsOpenImmersion j] [IsNoetherian X]

/-- An inverse system in `D^b_{Coh}(𝒪_X)` is **pro-isomorphic to a Deligne system** when its
pro-object is isomorphic to the pro-object of some Deligne system along `j`. -/
public def ProIsoDeligneSystem (j : U ⟶ X) [IsOpenImmersion j] [IsNoetherian X]
    (F : ℕᵒᵖ ⥤ BoundedCoherentDerived X) : Prop :=
  ∃ D : DeligneSystem j, Nonempty (ProSeq.of F ≅ D.proObject)

/-- Being pro-isomorphic to a Deligne system only depends on the isomorphism class of the
inverse system. -/
public lemma ProIsoDeligneSystem.of_natIso {F G : ℕᵒᵖ ⥤ BoundedCoherentDerived X} (e : F ≅ G)
    (h : ProIsoDeligneSystem j G) : ProIsoDeligneSystem j F := by
  obtain ⟨D, ⟨i⟩⟩ := h
  exact ⟨D, ⟨ProSeq.ofIsoOfNatIso e ≪≫ i⟩⟩

/-- **Being pro-isomorphic to a Deligne system is being pro-isomorphic to an assigned one**, for
the assignment `AlgebraicGeometry.DeligneSystem.values`: every Deligne system is pro-isomorphic to
the assigned system of its value, `AlgebraicGeometry.DeligneSystem.proObjectIsoValues`. -/
public lemma proIsoDeligneSystem_iff {F : ℕᵒᵖ ⥤ BoundedCoherentDerived X} :
    ProIsoDeligneSystem j F ↔ (DeligneSystem.values j).ProIsoDeligne F := by
  constructor
  · rintro ⟨D, ⟨i⟩⟩
    exact ⟨D.value, ⟨i ≪≫ D.proObjectIsoValues⟩⟩
  · rintro ⟨K, ⟨i⟩⟩
    exact ⟨DeligneSystem.ofValue j K, ⟨i⟩⟩

end AlgebraicGeometry

end
