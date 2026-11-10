module

public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.PullbackSectionsSheaf.UnitComparison
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.Reduced
public import StacksFrontier.AlgebraicGeometry.Divisors.Meromorphic.MeromorphicSections
public import StacksFrontier.AlgebraicGeometry.MeromorphicGenericPointDecomposition.Globalization
public import StacksFrontier.AlgebraicGeometry.PicardUFD.Affine
public import StacksFrontier.AlgebraicGeometry.PullbackInvertible.RingedSpace
public import StacksFrontier.Topology.Sheaves.Cohomology.StrictlyPerfectRestriction.PullbackOverASite

/-!
# Existence of regular meromorphic sections

Let `X` be a scheme and `L` an invertible sheaf of `𝒪_X`-modules. A meromorphic section of `L`
is a global section of `K_X(L)`, and it is *regular* when multiplication by it is a
monomorphism `K_X ⟶ K_X(L)`. This file produces a regular meromorphic section whenever the
weakly associated points of `X` are generic points of irreducible components and every
quasi-compact open has finitely many irreducible components, and specialises that to the three
cases of [Stacks, Tag 02OZ].

The source argues by choosing, at each generic point `η` of an irreducible component, a
generator of the stalk `L_η` over the local ring `𝒪_{X, η}`, and reading off from the
generic-point decomposition of `K_X` and `K_X(L)` that the resulting family is a regular
meromorphic section. The argument here is the same one, assembled categorically: it produces an
isomorphism `K_X ≅ K_X(L)` **of sheaves of `K_X`-modules**, and multiplication by the section
corresponding to such an isomorphism is an isomorphism, hence a monomorphism. The choice of
generators is exactly the triviality of `L` on each `Spec 𝒪_{X, η}`.

## Main results

* `AlgebraicGeometry.exists_isRegularMeromorphicSection`: an invertible sheaf of modules on a
  scheme whose weakly associated points are generic points of irreducible components and whose
  quasi-compact opens have finitely many irreducible components has a regular meromorphic
  section.
* `AlgebraicGeometry.exists_isRegularMeromorphicSection_of_hasNoEmbeddedPoints`: case (3) of
  [Stacks, Tag 02OZ], which is [Stacks, Tag 0EMI]. Cases (1) and (2), for an integral scheme
  and for a reduced scheme with locally finitely many irreducible components, are
  `AlgebraicGeometry.exists_isRegularMeromorphicSection_of_isIntegral` and
  `AlgebraicGeometry.exists_isRegularMeromorphicSection_of_isReduced`, each deduced from the
  generic-point decomposition instead.
* `AlgebraicGeometry.nonempty_unit_iso_meromorphicSectionSheaf`: the isomorphism
  `K_X ≅ K_X(L)` of sheaves of `K_X`-modules that the existence statement rests on.
* `AlgebraicGeometry.isIso_genericPointComparisonKPi`: the generic-point decomposition of
  `K_X(F)` of [Stacks, Tag 0EMF] part (2), as an isomorphism of sheaves of `K_X`-modules
  rather than of `𝒪_X`-modules.
* `AlgebraicGeometry.unitIsoMeromorphicSectionSheafUnit`: extension of scalars along
  `𝒪_X ⟶ K_X` takes the structure sheaf to the structure sheaf, `K_X(𝒪_X) ≅ K_X`.
* `AlgebraicGeometry.nonempty_pullback_fromSpecStalk_iso_unit_of_isInvertible`: an invertible
  sheaf of modules pulls back to a trivial one on the spectrum of any local ring of the scheme.

## Implementation notes

**Why the `K_X`-linear decomposition has to be built.** The library's form of part (2) of
[Stacks, Tag 0EMF] is an isomorphism of `𝒪_X`-modules
(`AlgebraicGeometry.isIso_genericPointComparisonPi`), and that is not enough here: regularity
of a meromorphic section is a statement about the `K_X`-linear map it induces, and an
`𝒪_X`-linear isomorphism `K_X ≅ K_X(L)` carries no information about the `K_X`-module
structures. The comparison morphism is however already available `K_X`-linearly, as
`AlgebraicGeometry.genericPointComparisonKSheaf`, so what is needed is only to transport the
*invertibility* across restriction of scalars. That is done twice over, in the two directions:
restriction of scalars along `𝒪_X ⟶ K_X` preserves products, because it is a right adjoint
(`AlgebraicGeometry.totalQuotientChangeOfRingsAdjunction`), and it reflects isomorphisms,
because it does not change the underlying sheaf of abelian groups
(`AlgebraicGeometry.isIso_of_isIso_restrictScalars_toTotalQuotientRingSheaf`).

`CategoryTheory.Limits.isIso_map_piLift_of_isIso_piLift` is stated at abstract types on purpose.
At the concrete types the rewriting of `CategoryTheory.Limits.piComparison` inside a term
mentioning `SheafOfModules.restrictScalars` exhausts the heartbeat budget; with the statement
generalised, the rewriting happens once at no cost and the concrete instance is a single
application.

**`K_X(𝒪_X) ≅ K_X` is proved by corepresentability, not by computing sections.** Both sides
corepresent the functor of global sections — one by `SheafOfModules.unitHomEquiv`, the other by
that equivalence composed with the change-of-rings adjunction — so the two comparison
morphisms are mutually inverse by formal manipulation of the two bijections. No description of
the sections of the sheafified tensor product is needed. The two compositions are computed in
term mode: `rw` fails on these goals because the target is not type-correct at `implicit`
transparency, the `Stacks.Sheaves.Differentials.ringSheaf` and
`Stacks.SheafOfModules.TensorSheafification.structureSheaf` spellings of the sheaf of rings
being only definitionally equal.

**The choice of generators.** `Stacks.PicardUFD.isTrivial_of_isInvertible_spec` trivialises an
invertible sheaf of modules on `Spec R` whenever `CommRing.Pic R` is trivial, and Mathlib's
`CommRing.instSubsingletonPic` makes that automatic for a local ring. Applied to `R = 𝒪_{X, η}`
this is the source's "pick a generator of the free rank one module `L_η`", with no case
distinction between the reduced and the locally Noetherian situation: in both, the only thing
used is that `𝒪_{X, η}` is local.

## References

* [Stacks Project, Tag 02OZ](https://stacks.math.columbia.edu/tag/02OZ)
* [Stacks Project, Tag 0EMI](https://stacks.math.columbia.edu/tag/0EMI)
* [Stacks Project, Tag 0EMF](https://stacks.math.columbia.edu/tag/0EMF)
* [Stacks Project, Tag 0EMH](https://stacks.math.columbia.edu/tag/0EMH)
* [Stacks Project, Tag 02OX](https://stacks.math.columbia.edu/tag/02OX)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe v₁ v₂ u₁ u₂ w u

noncomputable section

namespace CategoryTheory.Limits

/-- **A lifted morphism into a product is inverted by a functor preserving that product** as
soon as the lift of the identified components is. The components of the image are identified
with the given family by `e`, and the product comparison of the functor is assumed invertible,
which is what preservation of the product supplies. -/
theorem isIso_map_piLift_of_isIso_piLift {C : Type u₁} [Category.{v₁} C] {D : Type u₂}
    [Category.{v₂} D] (G : C ⥤ D) {J : Type w} {A : C} {f : J → C} (g : ∀ j, A ⟶ f j)
    [HasProduct f] [HasProductsOfShape J D]
    {h : J → D} (e : ∀ j, G.obj (f j) ≅ h j) (q : ∀ j, G.obj A ⟶ h j)
    (hq : ∀ j, q j = G.map (g j) ≫ (e j).hom)
    (hpc : IsIso (piComparison G f)) (hql : IsIso (Pi.lift q)) :
    IsIso (G.map (Pi.lift g)) := by
  have := hpc
  have := hql
  have key : G.map (Pi.lift g) ≫ (piComparison G f ≫ (Pi.mapIso e).hom) = Pi.lift q := by
    refine Pi.hom_ext _ _ fun j ↦ ?_
    rw [Category.assoc, Category.assoc, Pi.mapIso_hom_π,
      ← Category.assoc (piComparison G f), piComparison_comp_π, ← Category.assoc,
      ← G.map_comp, Pi.lift_comp_π, Pi.lift_comp_π, hq]
  have h2 : IsIso (G.map (Pi.lift g) ≫ (piComparison G f ≫ (Pi.mapIso e).hom)) := by
    rw [key]; infer_instance
  exact IsIso.of_isIso_comp_right (G.map (Pi.lift g)) (piComparison G f ≫ (Pi.mapIso e).hom)

end CategoryTheory.Limits

namespace AlgebraicGeometry

/-! ### Restriction of scalars along `𝒪_X ⟶ K_X` reflects isomorphisms -/

/-- **Restriction of scalars along `𝒪_X ⟶ K_X` reflects isomorphisms.** It does not change the
underlying sheaf of abelian groups, and a morphism of sheaves of modules is an isomorphism as
soon as that underlying morphism of sheaves of abelian groups is. -/
theorem isIso_of_isIso_restrictScalars_toTotalQuotientRingSheaf {X : Scheme.{u}}
    {M N : SheafOfModules.{u} (Stacks.Sheaves.Differentials.ringSheaf
      (J := Opens.grothendieckTopology X) X.totalQuotientSheaf)} (f : M ⟶ N)
    (h : IsIso ((SheafOfModules.restrictScalars (toTotalQuotientRingSheaf X)).map f)) :
    IsIso f :=
  have h' : IsIso ((SheafOfModules.toSheaf (Stacks.Sheaves.Differentials.ringSheaf
      (J := Opens.grothendieckTopology X) X.totalQuotientSheaf)).map f) :=
    show IsIso ((SheafOfModules.toSheaf (Stacks.Sheaves.Differentials.ringSheaf
      (J := Opens.grothendieckTopology X) X.sheaf)).map
        ((SheafOfModules.restrictScalars (toTotalQuotientRingSheaf X)).map f)) from inferInstance
  (isIso_iff_of_reflects_iso f (SheafOfModules.toSheaf _)).mp h'

/-! ### The generic-point decomposition, `K_X`-linearly -/

variable {X : Scheme.{u}}

set_option synthInstance.maxHeartbeats 100000 in
-- instance search for the product `∏ᶜ` of sheaves of `K_X`-modules is slow
/-- The comparison from `K_X(F)` to the product of the generic-point contributions, as a
morphism of sheaves of `K_X`-modules. -/
def genericPointComparisonKPi (F : X.Modules) :
    meromorphicSectionSheaf X.sheaf F ⟶
      ∏ᶜ fun η : genericPoints X ↦ genericPointStalkKModule F η :=
  Pi.lift fun η ↦ genericPointComparisonKSheaf F η

/-- **Part (2) of [Stacks, Tag 0EMF] for sheaves of `K_X`-modules.** The comparison from the
sheaf of meromorphic sections of a quasi-coherent module to the product of the generic-point
contributions is an isomorphism of sheaves of `K_X`-modules, not merely of `𝒪_X`-modules. -/
theorem isIso_genericPointComparisonKPi
    (hass : Stacks.Divisors.schemeWeaklyAssociatedPoints X ⊆ genericPoints X)
    (hfinite : ∀ V : X.Opens, IsCompact (V : Set X) → (irreducibleComponents V).Finite)
    (F : X.Modules) [F.IsQuasicoherent] : IsIso (genericPointComparisonKPi F) := by
  have hpres : PreservesLimitsOfShape (Discrete (genericPoints X))
      (SheafOfModules.restrictScalars (toTotalQuotientRingSheaf X)) :=
    ((totalQuotientChangeOfRingsAdjunction X).rightAdjoint_preservesLimits).preservesLimitsOfShape
  have hlift : IsIso (Pi.lift fun η : genericPoints X ↦ genericPointComparison F η) :=
    isIso_genericPointComparisonPi hass hfinite F
  exact isIso_of_isIso_restrictScalars_toTotalQuotientRingSheaf _
    (isIso_map_piLift_of_isIso_piLift
      (SheafOfModules.restrictScalars (toTotalQuotientRingSheaf X))
      (fun η : genericPoints X ↦ genericPointComparisonKSheaf F η)
      (fun η ↦ eqToIso (restrictScalars_genericPointStalkKModule F η))
      (fun η ↦ genericPointComparison F η) (fun η ↦ rfl) inferInstance hlift)

/-! ### Extension of scalars takes the structure sheaf to the structure sheaf -/

variable (X) in
/-- The section `1` of `K_X`, read as a section of `K_X` as a sheaf of modules over itself. -/
def kOne : (SheafOfModules.unit (Stacks.Sheaves.Differentials.ringSheaf
    (J := Opens.grothendieckTopology X) X.totalQuotientSheaf)).sections :=
  (SheafOfModules.unit (Stacks.Sheaves.Differentials.ringSheaf
    (J := Opens.grothendieckTopology X) X.totalQuotientSheaf)).unitHomEquiv (𝟙 _)

variable (X) in
/-- The canonical `𝒪_X`-linear map `𝒪_X ⟶ K_X`, as a morphism of sheaves of modules. -/
def toKUnit : SheafOfModules.unit X.ringCatSheaf ⟶
    (SheafOfModules.restrictScalars (toTotalQuotientRingSheaf X)).obj
      (SheafOfModules.unit (Stacks.Sheaves.Differentials.ringSheaf
        (J := Opens.grothendieckTopology X) X.totalQuotientSheaf)) :=
  ((SheafOfModules.restrictScalars (toTotalQuotientRingSheaf X)).obj
    (SheafOfModules.unit (Stacks.Sheaves.Differentials.ringSheaf
      (J := Opens.grothendieckTopology X) X.totalQuotientSheaf))).unitHomEquiv.symm (kOne X)

variable (X) in
/-- The comparison `K_X(𝒪_X) ⟶ K_X`: the transpose, along extension of scalars, of the
canonical map `𝒪_X ⟶ K_X`. -/
def meromorphicUnitToUnit :
    meromorphicSectionSheaf X.sheaf (SheafOfModules.unit X.ringCatSheaf) ⟶
      SheafOfModules.unit (Stacks.Sheaves.Differentials.ringSheaf
        (J := Opens.grothendieckTopology X) X.totalQuotientSheaf) :=
  ((totalQuotientChangeOfRingsAdjunction X).homEquiv (SheafOfModules.unit X.ringCatSheaf) _).symm
    (toKUnit X)

variable (X) in
/-- The section of `K_X(𝒪_X)` given by the unit of extension of scalars at the structure
sheaf. -/
def meromorphicUnitSection :
    (meromorphicSectionSheaf X.sheaf (SheafOfModules.unit X.ringCatSheaf)).sections :=
  ((SheafOfModules.restrictScalars (toTotalQuotientRingSheaf X)).obj
    (meromorphicSectionSheaf X.sheaf (SheafOfModules.unit X.ringCatSheaf))).unitHomEquiv
      ((totalQuotientChangeOfRingsAdjunction X).unit.app (SheafOfModules.unit X.ringCatSheaf))

variable (X) in
/-- The comparison `K_X ⟶ K_X(𝒪_X)`: multiplication by the canonical section. -/
def unitToMeromorphicUnit :
    SheafOfModules.unit (Stacks.Sheaves.Differentials.ringSheaf
        (J := Opens.grothendieckTopology X) X.totalQuotientSheaf) ⟶
      meromorphicSectionSheaf X.sheaf (SheafOfModules.unit X.ringCatSheaf) :=
  (meromorphicSectionSheaf X.sheaf (SheafOfModules.unit X.ringCatSheaf)).unitHomEquiv.symm
    (meromorphicUnitSection X)

variable (X) in
/-- The unit of extension of scalars, composed with the transpose of the canonical map
`𝒪_X ⟶ K_X`, is the canonical map. -/
theorem unit_comp_meromorphicUnitToUnit :
    (totalQuotientChangeOfRingsAdjunction X).unit.app (SheafOfModules.unit X.ringCatSheaf) ≫
        (SheafOfModules.restrictScalars (toTotalQuotientRingSheaf X)).map
          (meromorphicUnitToUnit X) = toKUnit X :=
  (Adjunction.homEquiv_unit (adj := totalQuotientChangeOfRingsAdjunction X)
    (f := meromorphicUnitToUnit X)).symm.trans (Equiv.apply_symm_apply _ (toKUnit X))

variable (X) in
/-- The comparison `K_X ⟶ K_X(𝒪_X)` followed by `K_X(𝒪_X) ⟶ K_X` is the identity of `K_X`. -/
theorem unitToMeromorphicUnit_comp_meromorphicUnitToUnit :
    unitToMeromorphicUnit X ≫ meromorphicUnitToUnit X = 𝟙 _ := by
  refine (SheafOfModules.unit (Stacks.Sheaves.Differentials.ringSheaf
    (J := Opens.grothendieckTopology X) X.totalQuotientSheaf)).unitHomEquiv.injective ?_
  rw [SheafOfModules.unitHomEquiv_comp_apply, unitToMeromorphicUnit, Equiv.apply_symm_apply,
    meromorphicUnitSection]
  change ((SheafOfModules.restrictScalars (toTotalQuotientRingSheaf X)).obj
      (SheafOfModules.unit (Stacks.Sheaves.Differentials.ringSheaf
        (J := Opens.grothendieckTopology X) X.totalQuotientSheaf))).unitHomEquiv
        ((totalQuotientChangeOfRingsAdjunction X).unit.app (SheafOfModules.unit X.ringCatSheaf) ≫
          (SheafOfModules.restrictScalars (toTotalQuotientRingSheaf X)).map
            (meromorphicUnitToUnit X)) = _
  exact (congrArg (fun t ↦ ((SheafOfModules.restrictScalars (toTotalQuotientRingSheaf X)).obj
      (SheafOfModules.unit (Stacks.Sheaves.Differentials.ringSheaf
        (J := Opens.grothendieckTopology X) X.totalQuotientSheaf))).unitHomEquiv t)
    (unit_comp_meromorphicUnitToUnit X)).trans (Equiv.apply_symm_apply _ (kOne X))

variable (X) in
/-- The comparison `K_X(𝒪_X) ⟶ K_X` followed by `K_X ⟶ K_X(𝒪_X)` is the identity of
`K_X(𝒪_X)`. -/
theorem meromorphicUnitToUnit_comp_unitToMeromorphicUnit :
    meromorphicUnitToUnit X ≫ unitToMeromorphicUnit X = 𝟙 _ := by
  refine ((totalQuotientChangeOfRingsAdjunction X).homEquiv
    (SheafOfModules.unit X.ringCatSheaf)
    (meromorphicSectionSheaf X.sheaf (SheafOfModules.unit X.ringCatSheaf))).injective ?_
  have h2 : SheafOfModules.sectionsMap
        ((SheafOfModules.restrictScalars (toTotalQuotientRingSheaf X)).map
          (unitToMeromorphicUnit X)) (kOne X) = meromorphicUnitSection X :=
    (SheafOfModules.unitHomEquiv_comp_apply (𝟙 _) (unitToMeromorphicUnit X)).symm.trans
      ((congrArg (fun t ↦ (meromorphicSectionSheaf X.sheaf
          (SheafOfModules.unit X.ringCatSheaf)).unitHomEquiv t)
        (Category.id_comp (unitToMeromorphicUnit X))).trans
          (Equiv.apply_symm_apply _ (meromorphicUnitSection X)))
  have h3 : toKUnit X ≫ (SheafOfModules.restrictScalars (toTotalQuotientRingSheaf X)).map
        (unitToMeromorphicUnit X) =
      (totalQuotientChangeOfRingsAdjunction X).unit.app (SheafOfModules.unit X.ringCatSheaf) :=
    (SheafOfModules.unitHomEquiv_symm_comp
      (M := (SheafOfModules.restrictScalars (toTotalQuotientRingSheaf X)).obj
        (SheafOfModules.unit (Stacks.Sheaves.Differentials.ringSheaf
          (J := Opens.grothendieckTopology X) X.totalQuotientSheaf))) (kOne X)
      ((SheafOfModules.restrictScalars (toTotalQuotientRingSheaf X)).map
        (unitToMeromorphicUnit X))).trans
      ((congrArg (fun t ↦ ((SheafOfModules.restrictScalars
          (toTotalQuotientRingSheaf X)).obj (meromorphicSectionSheaf X.sheaf
            (SheafOfModules.unit X.ringCatSheaf))).unitHomEquiv.symm t) h2).trans
        (Equiv.symm_apply_apply _ _))
  refine (Adjunction.homEquiv_unit (adj := totalQuotientChangeOfRingsAdjunction X)
    (f := meromorphicUnitToUnit X ≫ unitToMeromorphicUnit X)).trans ?_
  refine Eq.trans ?_ (Adjunction.homEquiv_unit
    (adj := totalQuotientChangeOfRingsAdjunction X)
    (f := 𝟙 (meromorphicSectionSheaf X.sheaf (SheafOfModules.unit X.ringCatSheaf)))).symm
  refine (congrArg (fun t ↦ (totalQuotientChangeOfRingsAdjunction X).unit.app
      (SheafOfModules.unit X.ringCatSheaf) ≫ t)
    ((SheafOfModules.restrictScalars (toTotalQuotientRingSheaf X)).map_comp
      (meromorphicUnitToUnit X) (unitToMeromorphicUnit X))).trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  refine ((congrArg (fun t ↦ t ≫ (SheafOfModules.restrictScalars
      (toTotalQuotientRingSheaf X)).map (unitToMeromorphicUnit X))
    (unit_comp_meromorphicUnitToUnit X)).trans h3).trans ?_
  exact (Category.comp_id _).symm.trans (congrArg (fun t ↦
    (totalQuotientChangeOfRingsAdjunction X).unit.app
      (SheafOfModules.unit X.ringCatSheaf) ≫ t)
    ((SheafOfModules.restrictScalars (toTotalQuotientRingSheaf X)).map_id _).symm)

variable (X) in
/-- **Extension of scalars along `𝒪_X ⟶ K_X` takes the structure sheaf to the structure
sheaf**: `K_X(𝒪_X) ≅ K_X` as sheaves of `K_X`-modules. -/
def unitIsoMeromorphicSectionSheafUnit :
    SheafOfModules.unit (Stacks.Sheaves.Differentials.ringSheaf
        (J := Opens.grothendieckTopology X) X.totalQuotientSheaf) ≅
      meromorphicSectionSheaf X.sheaf (SheafOfModules.unit X.ringCatSheaf) where
  hom := unitToMeromorphicUnit X
  inv := meromorphicUnitToUnit X
  hom_inv_id := unitToMeromorphicUnit_comp_meromorphicUnitToUnit X
  inv_hom_id := meromorphicUnitToUnit_comp_unitToMeromorphicUnit X

/-! ### Trivialising an invertible module at a generic point -/

/-- **An invertible sheaf of modules on the spectrum of a local ring is trivial.** The Picard
group of a local ring is trivial, so this is the affine triviality statement of
`Stacks.PicardUFD.isTrivial_of_isInvertible_spec`. -/
@[sga "1 XI 6.5" "local-ring example"]
theorem nonempty_iso_unit_of_isInvertible_spec_isLocalRing (R : Type u) [CommRing R]
    [IsLocalRing R] (M : (Spec (CommRingCat.of R)).Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible (Spec (CommRingCat.of R)).presheaf
      (Spec (CommRingCat.of R)).ringCatSheaf.2 M] :
    Nonempty (M ≅ SheafOfModules.unit (Spec (CommRingCat.of R)).ringCatSheaf) :=
  have : Stacks.SheafOfModules.IsInvertible (Spec (CommRingCat.of R)).presheaf
      (Spec (CommRingCat.of R)).ringCatSheaf.2 M :=
    (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ M).mpr ‹_›
  Stacks.PicardUFD.isTrivial_of_isInvertible_spec R M

/-- **An invertible sheaf of modules pulls back to a trivial one on the spectrum of a local
ring of the scheme.** This is the source's choice of a generator of the stalk `L_x` over
`𝒪_{X, x}`. For the same conclusion from finite local freeness of rank one instead of
invertibility, see `AlgebraicGeometry.nonempty_pullback_fromSpecStalk_iso_unit`. -/
theorem nonempty_pullback_fromSpecStalk_iso_unit_of_isInvertible (X : Scheme.{u})
    (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L] (x : X) :
    Nonempty ((Scheme.Modules.pullback (X.fromSpecStalk x)).obj L ≅
      SheafOfModules.unit (Spec (X.presheaf.stalk x)).ringCatSheaf) :=
  have : AlgebraicGeometry.SheafOfModules.IsInvertible
      (Spec (X.presheaf.stalk x)).presheaf (Spec (X.presheaf.stalk x)).ringCatSheaf.2
      ((Scheme.Modules.pullback (X.fromSpecStalk x)).obj L) :=
    Stacks.RingedSpace.algebraicGeometryIsInvertible_modulePullback
      (X.fromSpecStalk x).toLRSHom.toShHom L
  nonempty_iso_unit_of_isInvertible_spec_isLocalRing (ToType (X.presheaf.stalk x)) _

/-- **The generic-point contribution of an invertible sheaf of modules is the generic-point
contribution of the structure sheaf.** This is where the choice of a generator of `L_η` enters,
as the triviality of `L` on `Spec 𝒪_{X, η}`. -/
theorem nonempty_genericPointStalkKModule_iso_unit (X : Scheme.{u}) (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    (η : genericPoints X) :
    Nonempty (genericPointStalkKModule (SheafOfModules.unit X.ringCatSheaf) η ≅
      genericPointStalkKModule L η) :=
  ⟨(SheafOfModules.pushforward (toStalkSpecPushforwardRingCatSheafHom η)).mapIso
    ((Scheme.Modules.pullbackUnitIso (X.fromSpecStalk η.1)) ≪≫
      (nonempty_pullback_fromSpecStalk_iso_unit_of_isInvertible X L η.1).some.symm)⟩

/-! ### Existence of a regular meromorphic section -/

/-- A meromorphic section whose induced map from the sheaf of meromorphic functions is an
isomorphism is regular. -/
theorem isRegularMeromorphicSection_of_isIso {T : TopCat.{u}}
    (O : TopCat.Sheaf CommRingCat.{u} T)
    (L : SheafOfModules.{u} (Stacks.Sheaves.Differentials.ringSheaf (C := Opens T)
      (J := Opens.grothendieckTopology T) O))
    (s : MeromorphicSection O L)
    (h : IsIso ((meromorphicSectionSheaf O L).unitHomEquiv.symm s)) :
    IsRegularMeromorphicSection O L s :=
  @IsIso.mono_of_iso _ _ _ _ _ h

/-- **An isomorphism `K_X ≅ K_X(L)` of sheaves of `K_X`-modules produces a regular meromorphic
section of `L`**: the section it corresponds to under `SheafOfModules.unitHomEquiv` induces
that isomorphism, and an isomorphism is a monomorphism. -/
theorem exists_isRegularMeromorphicSection_of_nonempty_iso {T : TopCat.{u}}
    (O : TopCat.Sheaf CommRingCat.{u} T)
    (L : SheafOfModules.{u} (Stacks.Sheaves.Differentials.ringSheaf (C := Opens T)
      (J := Opens.grothendieckTopology T) O))
    (h : Nonempty (SheafOfModules.unit (Stacks.Sheaves.Differentials.ringSheaf (C := Opens T)
        (J := Opens.grothendieckTopology T) (totalQuotientSheaf (X := T) O)) ≅
      meromorphicSectionSheaf O L)) :
    ∃ s : MeromorphicSection O L, IsRegularMeromorphicSection O L s := by
  obtain ⟨e⟩ := h
  refine ⟨(meromorphicSectionSheaf O L).unitHomEquiv e.hom,
    isRegularMeromorphicSection_of_isIso O L _ ?_⟩
  exact Eq.mpr (congrArg IsIso
    (Equiv.symm_apply_apply (meromorphicSectionSheaf O L).unitHomEquiv e.hom))
      (inferInstanceAs (IsIso e.hom))

/-- **The sheaf of meromorphic sections of an invertible sheaf of modules is the sheaf of
meromorphic functions**, as sheaves of `K_X`-modules, for a scheme whose weakly associated
points are generic points of irreducible components and whose quasi-compact opens have
finitely many irreducible components. -/
@[ega "IV 20.1.8" "special case"]
theorem nonempty_unit_iso_meromorphicSectionSheaf (X : Scheme.{u}) (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    (hass : Stacks.Divisors.schemeWeaklyAssociatedPoints X ⊆ genericPoints X)
    (hfinite : ∀ V : X.Opens, IsCompact (V : Set X) → (irreducibleComponents V).Finite) :
    Nonempty (SheafOfModules.unit (Stacks.Sheaves.Differentials.ringSheaf
        (J := Opens.grothendieckTopology X) X.totalQuotientSheaf) ≅
      meromorphicSectionSheaf X.sheaf L) := by
  have hqc : L.IsQuasicoherent :=
    have : Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L :=
      (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ L).mpr ‹_›
    Stacks.SheafOfModules.Scheme.isQuasicoherent_of_isInvertible _ L
  have e (F : X.Modules) [F.IsQuasicoherent] :=
    haveI := isIso_genericPointComparisonKPi hass hfinite F
    asIso (genericPointComparisonKPi F)
  exact ⟨unitIsoMeromorphicSectionSheafUnit X ≪≫ e _ ≪≫
    Pi.mapIso (fun η : genericPoints X ↦
      (nonempty_genericPointStalkKModule_iso_unit X L η).some) ≪≫ (e L).symm⟩

/-- **An invertible sheaf of modules has a regular meromorphic section** on a scheme whose
weakly associated points are generic points of irreducible components and whose quasi-compact
opens have finitely many irreducible components. -/
theorem exists_isRegularMeromorphicSection (X : Scheme.{u}) (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    (hass : Stacks.Divisors.schemeWeaklyAssociatedPoints X ⊆ genericPoints X)
    (hfinite : ∀ V : X.Opens, IsCompact (V : Set X) → (irreducibleComponents V).Finite) :
    ∃ s : MeromorphicSection X.sheaf L, IsRegularMeromorphicSection X.sheaf L s :=
  exists_isRegularMeromorphicSection_of_nonempty_iso X.sheaf L
    (nonempty_unit_iso_meromorphicSectionSheaf X L hass hfinite)

/-! ### The three cases of Tag 02OZ -/

/-- On an irreducible space every open subspace has at most one irreducible component. -/
theorem finite_irreducibleComponents_of_irreducibleSpace (X : Scheme.{u})
    [IrreducibleSpace (X : Type u)] (V : X.Opens) :
    (irreducibleComponents (V : Set X)).Finite := by
  rcases Set.eq_empty_or_nonempty (V : Set X) with hV | hV
  · have : IsEmpty ((V : Set X) : Type u) := Set.isEmpty_coe_sort.mpr hV
    exact Set.toFinite _
  · have hpre : IsPreirreducible (V : Set X) := by
      intro A B hA hB ⟨a, ha, haA⟩ ⟨b, hb, hbB⟩
      obtain ⟨z, hzA, hzB⟩ := nonempty_preirreducible_inter (V.2.inter hA) (V.2.inter hB)
        ⟨a, ha, haA⟩ ⟨b, hb, hbB⟩
      exact ⟨z, ⟨hzA.1, hzA.2, hzB.2⟩⟩
    have : IrreducibleSpace ((V : Set X) : Type u) := Subtype.irreducibleSpace ⟨hV, hpre⟩
    rw [irreducibleComponents_eq_singleton]
    exact Set.finite_singleton _

/-- **[Stacks, Tag 0EMI]**, which is case (3) of [Stacks, Tag 02OZ]. An invertible sheaf of
modules on a locally Noetherian scheme without embedded points has a regular meromorphic
section. -/
@[stacks 02OZ "case (3), X locally Noetherian without embedded points", stacks 0EMI]
theorem exists_isRegularMeromorphicSection_of_hasNoEmbeddedPoints (X : Scheme.{u})
    [IsLocallyNoetherian X] (hX : HasNoEmbeddedPoints X) (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L] :
    ∃ s : MeromorphicSection X.sheaf L, IsRegularMeromorphicSection X.sheaf L s :=
  exists_isRegularMeromorphicSection X L
    (schemeWeaklyAssociatedPoints_eq_genericPoints_of_hasNoEmbeddedPoints X hX).le
    (finite_irreducibleComponents_of_isCompact X)

end AlgebraicGeometry

end

end
