module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EpiLocallySurjective
public import StacksFrontier.AlgebraicGeometry.Divisors.MorphismWeaklyAssociated.SpaceEtalePullback
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.InverseImageDeltaDimension
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.MaximalDeltaDimension
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.MultiplicityAtPoint
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.StructureSheafCycle
public import StacksFrontier.AlgebraicGeometry.Spaces.ShortExactQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.SupportGeometricStalkCriterion
public import StacksFrontier.AlgebraicGeometry.Spaces.WeaklyAssociatedInjective

/-!
# The cycle associated to a coherent sheaf

In Situation 0EDT let `X/B` be good and let `F` be a coherent `𝒪_X`-module. **Stacks 0EEB**
defines two things.

Part (1): for an integral closed subspace `Z ⊆ X` with generic point `ξ` such that `|Z|` is an
irreducible component of `Supp(F)`, the *multiplicity of `Z` in `F`* is the length of `F` at `ξ`
in the sense of Stacks 0EE2; by Stacks 0EE4 it is a positive integer.

Part (2): if `dim_δ(Supp(F)) ≤ k` then the *`k`-cycle associated to `F`* is

`[F]_k = ∑ m_{Z, F} [Z]`,

the sum running over the integral closed subspaces `Z ⊆ X` whose point set is an irreducible
component of `Supp(F)` of δ-dimension `k`. That this really is a `k`-cycle — that the collection
of those point sets is locally finite — is Stacks 0EE5.

A cycle is a coefficient family on the integral closed subspaces of `X`
(`AlgebraicGeometry.Space.cyclesOfDimension` of Stacks 0EDZ), so the formal sum above *is* a
coefficient family and nothing has to be summed. The coefficient family is the one already in the
library, `AlgebraicGeometry.Space.cycleCoeffOfModule`: it assigns to `Z` the length of `F` at the
generic point of `Z` when `Z` has δ-dimension `k`, and `0` otherwise. Those two readings agree
because off `Supp(F)` the length already vanishes, and the content of this file is that the
resulting family lies in `Z_k(X)`.

**Stacks 0EEC** reads that coefficient family back off `[F]_k`: for *every* integral closed
subspace `Z` of δ-dimension `k`, whether or not `|Z|` is a component of `Supp(F)`, the coefficient
of `Z` in `[F]_k` is the length of `F` at the generic point of `Z`.

**Stacks 0EEE** is additivity: for a short exact sequence `0 → F → G → H → 0` of coherent
`𝒪_X`-modules whose three supports have δ-dimension at most `k`, `[G]_k = [F]_k + [H]_k`. Read
coefficientwise through Stacks 0EEC, it is additivity of length in a short exact sequence,
Stacks 00IV, at the generic point of each integral closed subspace of δ-dimension `k`.

## Main definitions

* `AlgebraicGeometry.Space.moduleSupport`: the support of a module on an algebraic space, as a set
  of points.
* `AlgebraicGeometry.Space.moduleMultiplicity`: **Stacks 0EEB part (1)**, the multiplicity of an
  integral closed subspace in a module.
* `AlgebraicGeometry.Space.associatedCycle`: **Stacks 0EEB part (2)**, the `k`-cycle `[F]_k`
  associated to a coherent module whose support has δ-dimension at most `k`.
* `AlgebraicGeometry.Space.geometricModuleStalkLinearMap`: the map of geometric stalks induced by
  a morphism of `𝒪_X`-modules, as a map of modules over the étale local ring.

## Main results

* `AlgebraicGeometry.Space.moduleMultiplicity_pos_of_isIrreducibleComponent_moduleSupport`: the
  multiplicity of an irreducible component of the support is positive. This is the positivity
  half of the assertion of Stacks 0EE4 that the multiplicity is a positive integer.
* `AlgebraicGeometry.Space.exists_irreducibleComponents_of_cycleCoeffOfModule_ne_zero`:
  under the bound `dim_δ(Supp(F)) ≤ k`, an integral closed subspace with nonzero coefficient has
  point set an irreducible component of `Supp(F)`. This is what makes the coefficient family the
  sum of Stacks 0EEB part (2), and it is the step at which Stacks 0EE6 is used.
* `AlgebraicGeometry.Space.locallyFinite_cycleCoeffOfModule` and
  `AlgebraicGeometry.Space.cycleCoeffOfModule_mem_cyclesOfDimension`: the coefficient family is a
  `k`-cycle.
* `AlgebraicGeometry.Space.associatedCycle_apply_eq_geometricLength`: the coefficient of an
  integral closed subspace of δ-dimension `k` in `[F]_k` is the length of `F` at the chosen
  geometric point above its generic point. Stacks 0EEC itself, the length at the generic point in
  the sense of Stacks 0EE2, is
  `AlgebraicGeometry.Space.exists_associatedCycle_apply_eq_and_hasLengthAt` in
  `StacksFrontier.AlgebraicGeometry.Spaces.Chow.CoherentSheafCycleLength`.
* `AlgebraicGeometry.Space.associatedCycle_eq_zero_of_moduleSupport_eq_empty`: a module with empty
  support has associated cycle `0`.
* `AlgebraicGeometry.Space.geometricLength_add_of_shortExact`: the length at a geometric point is
  additive in a short exact sequence of `𝒪_X`-modules, and
  `AlgebraicGeometry.Space.moduleMultiplicity_add_of_shortExact` is the same statement for the
  multiplicity of an integral closed subspace.
* `AlgebraicGeometry.Space.associatedCycle_add_of_shortExact`: **Stacks 0EEE**, additivity of
  `[F]_k` along a short exact sequence of coherent modules whose three supports have δ-dimension
  at most `k`.

## Implementation notes

**The multiplicity is `ℕ∞`-valued.** Length on an algebraic space is
`AlgebraicGeometry.Space.geometricLength`, which takes values in `ℕ∞`, and the multiplicity is
defined at every integral closed subspace, where the length can be infinite. At a generic point of
an irreducible component of the support of a coherent module it is finite and positive, by Stacks
0EE4, `AlgebraicGeometry.Space.geometricLength_ne_top_and_pos_of_isGenericPoint_supportOfSheaf`.
Cycle coefficients are integers, so `AlgebraicGeometry.Space.cycleCoeffOfModule` applies
`ENat.toNat` to it, exactly as the scheme-side `Stacks.Chow.sheafMultiplicity` of Stacks 02QX does.

**The choice of geometric point.** Length is taken at a *geometric* point. Both definitions below
carry a function `γ` assigning a geometric point to each point of `|X|`, together with the
assumption that `γ x` lies over `x`, in the same shape as
`AlgebraicGeometry.Space.cycleCoeffOfModule` and the library's forms of Stacks 0EE2, 0EE3 and 0EED.
Such a `γ` exists, by `AlgebraicGeometry.Space.exists_geometricRepresentative`, and by Stacks 0EE1,
`AlgebraicGeometry.Space.geometricLength_eq_of_image_eq`, the length does not depend on which
geometric point above a point of `|X|` is chosen.

**Local finiteness is proved, not assumed.** The ingredients are those of the source: the support
of a coherent module is closed, by
`AlgebraicGeometry.Space.isClosed_supportOfSheaf_of_isCoherentOnSite`; the point space of `X` is
locally Noetherian, the structure morphism of a good space being locally of finite type over the
locally Noetherian base of Situation 0EDT, so the irreducible components of that closed set are
locally finite by Stacks 0EE5; a subspace with nonzero coefficient has its generic point in the
support — this is where quasi-coherence of `F` enters, through Stacks 07TZ — and attains the
δ-dimension bound, so by Stacks 0EE6 its point set is one of those components; and an integral
closed subspace is determined by its point set, by Stacks 0ENF. The family of point sets of the
subspaces with nonzero coefficient therefore injects into a locally finite family.

**The geometric stalks of a short exact sequence.** Injectivity of the first map and exactness in
the middle come from the left exactness of the sections of a short exact sequence of sheaves of
modules, `SheafOfModules.injective_f_val_app_of_shortExact` and
`SheafOfModules.exact_val_app_of_shortExact`, read on germs. Surjectivity of the second map cannot
be read on sections, where an epimorphism of sheaves is only locally surjective; it goes instead
through `Stacks.SheafOfModules.EpiMono.isLocallySurjective_of_epi` together with the lifting of a
point of the site through a covering sieve, which is part of the datum of such a point. Linearity
of the induced map over the étale local ring is `Stacks.moduleStalkLargeAddMap_smul`, which holds
because a scalar and a stalk element are germs of sections over one common neighbourhood.

**Additivity of the cycle uses the finiteness of Stacks 0EE4.** Additivity of the multiplicity,
`AlgebraicGeometry.Space.moduleMultiplicity_add_of_shortExact`, holds for any short exact sequence.
Cycle coefficients, however, are integers reached from the `ℕ∞`-valued multiplicity by
`ENat.toNat`, which is additive only on finite values. At an integral closed subspace of
δ-dimension `k` whose generic point lies off the support of the middle term the multiplicity is
zero, hence finite, by `AlgebraicGeometry.Space.moduleMultiplicity_ne_top_of_notMem_moduleSupport`.
At one whose generic point lies in that support, the δ-dimension bound makes the generic point a
generic point of an irreducible component of the support, by Stacks 0EE6, and there the length is
finite by Stacks 0EE4. Finiteness for the two outer terms then follows from additivity.

## References

* [Stacks Project, Tag 0EEB](https://stacks.math.columbia.edu/tag/0EEB)
* [Stacks Project, Tag 0EEC](https://stacks.math.columbia.edu/tag/0EEC)
* [Stacks Project, Tag 0EEE](https://stacks.math.columbia.edu/tag/0EEE)
* [Stacks Project, Tag 00IV](https://stacks.math.columbia.edu/tag/00IV)
* [Stacks Project, Tag 0EDT](https://stacks.math.columbia.edu/tag/0EDT)
* [Stacks Project, Tag 0EDZ](https://stacks.math.columbia.edu/tag/0EDZ)
* [Stacks Project, Tag 0EE1](https://stacks.math.columbia.edu/tag/0EE1)
* [Stacks Project, Tag 0EE2](https://stacks.math.columbia.edu/tag/0EE2)
* [Stacks Project, Tag 0EE4](https://stacks.math.columbia.edu/tag/0EE4)
* [Stacks Project, Tag 0EE5](https://stacks.math.columbia.edu/tag/0EE5)
* [Stacks Project, Tag 0EE6](https://stacks.math.columbia.edu/tag/0EE6)
* [Stacks Project, Tag 0ENF](https://stacks.math.columbia.edu/tag/0ENF)
* [Stacks Project, Tag 07TZ](https://stacks.math.columbia.edu/tag/07TZ)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

universe m v w t

namespace Stacks

section ModuleStalkLinearity

variable {C : Type t} [Category.{v} C] [LocallySmall.{w} C]
    {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    (p : J.Point.{w}) (O : Sheaf J CommRingCat.{w})

/-- The map of stalks at a point of a site induced by a morphism of sheaves of modules is linear
over the stalk of the sheaf of rings: a scalar and a stalk element are germs of sections over one
common neighbourhood of the point, where linearity is linearity on sections. -/
theorem moduleStalkLargeAddMap_smul {F₁ F₂ : SheafOfModules.{m} (commRingSheafToRingSheaf O)}
    (α : F₁ ⟶ F₂) (r : (p.presheafFiber (A := CommRingCat.{w})).obj O.obj)
    (z : moduleStalkLarge.{m} p O F₁) :
    moduleStalkLargeAddMap p O α (r • z) = r • moduleStalkLargeAddMap p O α z := by
  refine semilinear_of_semilinear_moduleStalkLargeGerm p O F₁
    (RingHom.id _) (moduleStalkLargeAddMap p O α) ?_ r z
  intro U y a s
  rw [← moduleStalkLargeGerm_smul, moduleStalkLargeAddMap_germ, map_smul,
    moduleStalkLargeGerm_smul, moduleStalkLargeAddMap_germ, RingHom.id_apply]

end ModuleStalkLinearity

end Stacks

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

/-! ### The support of a module, and the multiplicity of an integral closed subspace -/

section Multiplicity

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- The support of an `𝒪_X`-module on an algebraic space `X` over `S`, as a set of points of `X`:
the support of Stacks 04KA of the underlying sheaf of abelian groups. -/
abbrev moduleSupport (hX : IsAlgebraicSpace B S hS X) (F : Modules.{u, u} B S hS X hX) :
    Set (points B S hS X) :=
  supportOfSheaf B S hS X ((SheafOfModules.toSheaf _).obj F)

/-- The support of a coherent module is closed: a coherent module is of finite type, and the
support of a module of finite type is closed by Stacks 07TZ. -/
theorem isClosed_moduleSupport (hX : IsAlgebraicSpace B S hS X)
    (F : Modules.{u, u} B S hS X hX) [SheafOfModules.IsCoherentOnSite F] :
    IsClosed (moduleSupport B S hS hX F) :=
  isClosed_supportOfSheaf_of_isCoherentOnSite B S hS ⟨X, hX⟩ F

/-- **Stacks 0EEB, part (1).** The *multiplicity of an integral closed subspace `Z ⊆ X` in an
`𝒪_X`-module `F`*: the length of `F` at the generic point `ξ` of `Z`, in the sense of Stacks 0EE2,
read at the geometric point that `γ` assigns to `ξ`.

The source defines this when `|Z|` is an irreducible component of `Supp(F)`, where by Stacks 0EE4
it is a positive integer; the length itself is defined at every integral closed subspace, and the
positivity on a component is
`AlgebraicGeometry.Space.moduleMultiplicity_pos_of_isIrreducibleComponent_moduleSupport`. -/
@[stacks 0EEB "part (1): the multiplicity of an integral closed subspace in a module, at a chosen
  geometric representative of its generic point and valued in ℕ∞; the reading at a point of |X|
  additionally needs the equivalence of Lemma 0EE1, and the finiteness asserted by Lemma 0EE4,
  neither of which is proved in this library"]
def moduleMultiplicity (hX : IsAlgebraicSpace B S hS X) (F : Modules.{u, u} B S hS X hX)
    (γ : points B S hS X → GeometricPoint B S hS X)
    (Z : IntegralClosedSubspace B S hS X) : ℕ∞ :=
  geometricLength B S hS ⟨X, hX⟩ (γ (Z.ambientGenericPoint B S hS)) F

/-- The multiplicity of an integral closed subspace whose generic point lies outside the support
vanishes: the stalk of a quasi-coherent module at a geometric point over a point off the support is
zero, by Stacks 07TZ, so its length is zero. -/
theorem moduleMultiplicity_eq_zero_of_notMem_moduleSupport (hX : IsAlgebraicSpace B S hS X)
    (F : Modules.{u, u} B S hS X hX) [F.IsQuasicoherentOnSite]
    (γ : points B S hS X → GeometricPoint B S hS X)
    (hγ : ∀ x, (γ x).LiesOver x) (Z : IntegralClosedSubspace B S hS X)
    (hZ : Z.ambientGenericPoint B S hS ∉ moduleSupport B S hS hX F) :
    moduleMultiplicity B S hS hX F γ Z = 0 := by
  rw [moduleMultiplicity, geometricLength, Module.length_eq_zero_iff,
    ← not_nontrivial_iff_subsingleton]
  exact fun h => hZ ((mem_supportOfSheaf_iff_nontrivial_geometricModuleStalk_of_liesOver B S hS
    ⟨X, hX⟩ F _ _ (hγ (Z.ambientGenericPoint B S hS))).2 h)

/-- The multiplicity of an integral closed subspace whose generic point lies in the support is
positive: the stalk of a quasi-coherent module at a geometric point over a point of the support is
nonzero, by Stacks 07TZ, so its length is positive. -/
theorem moduleMultiplicity_pos_of_mem_moduleSupport (hX : IsAlgebraicSpace B S hS X)
    (F : Modules.{u, u} B S hS X hX) [F.IsQuasicoherentOnSite]
    (γ : points B S hS X → GeometricPoint B S hS X)
    (hγ : ∀ x, (γ x).LiesOver x) (Z : IntegralClosedSubspace B S hS X)
    (hZ : Z.ambientGenericPoint B S hS ∈ moduleSupport B S hS hX F) :
    0 < moduleMultiplicity B S hS hX F γ Z := by
  rw [moduleMultiplicity, geometricLength, Module.length_pos_iff]
  exact (mem_supportOfSheaf_iff_nontrivial_geometricModuleStalk_of_liesOver B S hS ⟨X, hX⟩ F _ _
    (hγ (Z.ambientGenericPoint B S hS))).1 hZ

/-- The multiplicity of an integral closed subspace contained in the support is positive: its
generic point is one of its own points, hence lies in the support. -/
theorem moduleMultiplicity_pos_of_subspacePointSet_subset (hX : IsAlgebraicSpace B S hS X)
    (F : Modules.{u, u} B S hS X hX) [F.IsQuasicoherentOnSite]
    (γ : points B S hS X → GeometricPoint B S hS X)
    (hγ : ∀ x, (γ x).LiesOver x) (Z : IntegralClosedSubspace B S hS X)
    (hZ : subspacePointSet B S hS X Z.subspace ⊆ moduleSupport B S hS hX F) :
    0 < moduleMultiplicity B S hS hX F γ Z := by
  refine moduleMultiplicity_pos_of_mem_moduleSupport B S hS hX F γ hγ Z (hZ ?_)
  rw [← Z.isGenericPoint_ambientGenericPoint B S hS hX]
  exact subset_closure rfl

/-- **The positivity half of Stacks 0EE4, at an integral closed subspace.** The multiplicity of an
integral closed subspace whose set of points is an irreducible component of the support of a
quasi-coherent module is positive.

A component of the support is contained in the support, so this is
`AlgebraicGeometry.Space.moduleMultiplicity_pos_of_subspacePointSet_subset`. Stacks 0EE4 itself,
finiteness included, is
`AlgebraicGeometry.Space.geometricLength_ne_top_and_pos_of_isGenericPoint_supportOfSheaf`, which
carries the tag; this declaration does not. -/
theorem moduleMultiplicity_pos_of_isIrreducibleComponent_moduleSupport
    (hX : IsAlgebraicSpace B S hS X) (F : Modules.{u, u} B S hS X hX) [F.IsQuasicoherentOnSite]
    (γ : points B S hS X → GeometricPoint B S hS X)
    (hγ : ∀ x, (γ x).LiesOver x) (Z : IntegralClosedSubspace B S hS X)
    (hZ : ∃ C : irreducibleComponents (moduleSupport B S hS hX F),
      subspacePointSet B S hS X Z.subspace =
        Subtype.val '' (C : Set (moduleSupport B S hS hX F))) :
    0 < moduleMultiplicity B S hS hX F γ Z := by
  obtain ⟨C, hC⟩ := hZ
  refine moduleMultiplicity_pos_of_subspacePointSet_subset B S hS hX F γ hγ Z ?_
  rw [hC]
  exact Set.image_subset_iff.2 fun p _ => p.2

end Multiplicity

/-! ### The geometric stalks of a short exact sequence -/

section StalkSequence

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS) (x : GeometricPoint B S hS X.1)

/-- The induced map of geometric stalks, read on a stalk element written through the extension of
scalars which defines the geometric stalk. -/
theorem geometricModuleStalkMap_addEquiv {F G : Modules.{u, u} B S hS X.1 X.2} (φ : F ⟶ G)
    (w : Stacks.moduleStalkLarge (etaleSitePoint B S hS X.1 x X.2)
      (smallEtaleRingedTopos B S hS X).O F) :
    geometricModuleStalkMap B S hS X x φ (geometricModuleStalkAddEquiv B S hS X x F w) =
      geometricModuleStalkAddEquiv B S hS X x G
        (Stacks.moduleStalkLargeAddMap (etaleSitePoint B S hS X.1 x X.2)
          (smallEtaleRingedTopos B S hS X).O φ w) :=
  congrArg (fun z => geometricModuleStalkAddEquiv B S hS X x G
      (Stacks.moduleStalkLargeAddMap (etaleSitePoint B S hS X.1 x X.2)
        (smallEtaleRingedTopos B S hS X).O φ z))
    ((geometricModuleStalkAddEquiv B S hS X x F).symm_apply_apply w)

/-- The induced map of geometric stalks is linear over the étale local ring: it is the map of
stalks of Stacks 05VQ, which is linear over the stalk of the structure sheaf, read through the
extension of scalars along the comparison of that stalk with the étale local ring. -/
theorem geometricModuleStalkMap_smul {F G : Modules.{u, u} B S hS X.1 X.2} (φ : F ⟶ G)
    (r : etaleLocalRing B S hS X.1 x) (z : geometricModuleStalk B S hS X x F) :
    geometricModuleStalkMap B S hS X x φ (r • z) =
      r • geometricModuleStalkMap B S hS X x φ z := by
  obtain ⟨w, rfl⟩ := (geometricModuleStalkAddEquiv B S hS X x F).surjective z
  obtain ⟨c, rfl⟩ := (pointStalkRingEquiv B S hS X x).surjective r
  calc geometricModuleStalkMap B S hS X x φ
        (pointStalkRingEquiv B S hS X x c • geometricModuleStalkAddEquiv B S hS X x F w)
      = geometricModuleStalkMap B S hS X x φ
          (geometricModuleStalkAddEquiv B S hS X x F (c • w)) :=
        congrArg (geometricModuleStalkMap B S hS X x φ)
          (geometricModuleStalkAddEquiv_smul B S hS X x F c w).symm
    _ = geometricModuleStalkAddEquiv B S hS X x G
          (Stacks.moduleStalkLargeAddMap (etaleSitePoint B S hS X.1 x X.2)
            (smallEtaleRingedTopos B S hS X).O φ (c • w)) :=
        geometricModuleStalkMap_addEquiv B S hS X x φ (c • w)
    _ = geometricModuleStalkAddEquiv B S hS X x G
          (c • Stacks.moduleStalkLargeAddMap (etaleSitePoint B S hS X.1 x X.2)
            (smallEtaleRingedTopos B S hS X).O φ w) :=
        congrArg (geometricModuleStalkAddEquiv B S hS X x G)
          (Stacks.moduleStalkLargeAddMap_smul (etaleSitePoint B S hS X.1 x X.2)
            (smallEtaleRingedTopos B S hS X).O φ c w)
    _ = pointStalkRingEquiv B S hS X x c •
          geometricModuleStalkAddEquiv B S hS X x G
            (Stacks.moduleStalkLargeAddMap (etaleSitePoint B S hS X.1 x X.2)
              (smallEtaleRingedTopos B S hS X).O φ w) :=
        geometricModuleStalkAddEquiv_smul B S hS X x G c _
    _ = pointStalkRingEquiv B S hS X x c •
          geometricModuleStalkMap B S hS X x φ (geometricModuleStalkAddEquiv B S hS X x F w) :=
        congrArg (fun y => pointStalkRingEquiv B S hS X x c • y)
          (geometricModuleStalkMap_addEquiv B S hS X x φ w).symm

/-- The map `F_x̄ → G_x̄` of geometric stalks induced by a morphism `φ : F ⟶ G` of `𝒪_X`-modules,
as a map of modules over the étale local ring `𝒪_{X, x̄}`. -/
def geometricModuleStalkLinearMap {F G : Modules.{u, u} B S hS X.1 X.2} (φ : F ⟶ G) :
    geometricModuleStalk B S hS X x F →ₗ[etaleLocalRing B S hS X.1 x]
      geometricModuleStalk B S hS X x G where
  toFun z := geometricModuleStalkMap B S hS X x φ z
  map_add' := map_add (geometricModuleStalkMap B S hS X x φ)
  map_smul' := geometricModuleStalkMap_smul B S hS X x φ

/-- The `𝒪_X`-modules with sections in the universe of the schemes form a balanced category: they
are abelian, the ambient site admitting sheafification in that universe and its local
equivalences being the local bijections. -/
theorem balanced_modules : Balanced (Modules.{u, u} B S hS X.1 X.2) := by
  let : Abelian (Modules.{u, u} B S hS X.1 X.2) :=
    @SheafOfModules.instAbelian _ _ _ _ (smallEtaleRingedSite_hasSheafify B S hS X.1 X.2)
      (smallEtaleRingedSite_wEqualsLocallyBijective B S hS X.1 X.2)
  exact Stacks.SheafOfModules.ImageSubsheaf.balanced_of_abelian

/-- The left-hand map of a short exact sequence of `𝒪_X`-modules is injective on geometric
stalks: a germ it kills dies on a smaller neighbourhood, where the map is injective on
sections. -/
theorem injective_geometricModuleStalkMap_f_of_shortExact
    (σ : ShortComplex (Modules.{u, u} B S hS X.1 X.2)) (hσ : σ.ShortExact) :
    Function.Injective (geometricModuleStalkMap B S hS X x σ.f) := by
  have := balanced_modules B S hS X
  rw [injective_iff_map_eq_zero]
  intro z hz
  obtain ⟨N, s, rfl⟩ := geometricModuleStalkGerm_jointly_surjective B S hS X x σ.X₁ z
  rw [geometricModuleStalkMap_germ] at hz
  obtain ⟨M, g, hg⟩ := (geometricModuleStalkGerm_eq_zero_iff B S hS X x σ.X₂ N _).mp hz
  refine (geometricModuleStalkGerm_eq_zero_iff B S hS X x σ.X₁ N s).mpr ⟨M, g, ?_⟩
  refine SheafOfModules.injective_f_val_app_of_shortExact hσ (Opposite.op M.chart) ?_
  refine Eq.trans ((PresheafOfModules.naturality_apply σ.f.val g.hom.op s).trans hg) ?_
  exact (map_zero (ConcreteCategory.hom (σ.f.val.app (Opposite.op M.chart)))).symm

/-- The two maps of a short exact sequence of `𝒪_X`-modules induce an exact pair on geometric
stalks: a germ killed by the second map dies on a smaller neighbourhood, where the sections of
the sequence are left exact. -/
theorem exact_geometricModuleStalkMap_of_shortExact
    (σ : ShortComplex (Modules.{u, u} B S hS X.1 X.2)) (hσ : σ.ShortExact) :
    Function.Exact (geometricModuleStalkMap B S hS X x σ.f)
      (geometricModuleStalkMap B S hS X x σ.g) := by
  have := balanced_modules B S hS X
  refine fun z => ⟨fun hz => ?_, ?_⟩
  · obtain ⟨N, s, rfl⟩ := geometricModuleStalkGerm_jointly_surjective B S hS X x σ.X₂ z
    rw [geometricModuleStalkMap_germ] at hz
    obtain ⟨M, g, hg⟩ := (geometricModuleStalkGerm_eq_zero_iff B S hS X x σ.X₃ N _).mp hz
    obtain ⟨b, hb⟩ := (SheafOfModules.exact_val_app_of_shortExact hσ (Opposite.op M.chart) _).mp
      ((PresheafOfModules.naturality_apply σ.g.val g.hom.op s).trans hg)
    refine ⟨geometricModuleStalkGerm B S hS X x σ.X₁ M b, ?_⟩
    refine Eq.trans (geometricModuleStalkMap_germ B S hS X x σ.f M b) ?_
    exact Eq.trans (congrArg (geometricModuleStalkGerm B S hS X x σ.X₂ M) hb)
      (geometricModuleStalkGerm_map B S hS X x σ.X₂ g s)
  · rintro ⟨y, rfl⟩
    obtain ⟨N, s, rfl⟩ := geometricModuleStalkGerm_jointly_surjective B S hS X x σ.X₁ y
    refine Eq.trans (congrArg (geometricModuleStalkMap B S hS X x σ.g)
      (geometricModuleStalkMap_germ B S hS X x σ.f N s)) ?_
    refine Eq.trans (geometricModuleStalkMap_germ B S hS X x σ.g N _) ?_
    refine Eq.trans (congrArg (geometricModuleStalkGerm B S hS X x σ.X₃ N) ?_)
      (map_zero (geometricModuleStalkGerm B S hS X x σ.X₃ N))
    simpa using congrArg (fun (ψ : σ.X₁.val ⟶ σ.X₃.val) => (ψ.app (Opposite.op N.chart)).hom s)
      (congrArg (fun ψ => ψ.val) σ.zero : σ.f.val ≫ σ.g.val = 0)

/-- An epimorphism of `𝒪_X`-modules is surjective on geometric stalks: an epimorphism of sheaves
of modules is locally surjective, and a covering sieve of a neighbourhood of a geometric point
contains an arrow through which the point lifts. -/
theorem surjective_geometricModuleStalkMap_of_epi {F G : Modules.{u, u} B S hS X.1 X.2}
    (φ : F ⟶ G) [Epi φ] :
    Function.Surjective (geometricModuleStalkMap B S hS X x φ) := by
  intro z
  obtain ⟨N, t, rfl⟩ := geometricModuleStalkGerm_jointly_surjective B S hS X x G z
  have hmem : Presheaf.imageSieve ((PresheafOfModules.toPresheaf
        ((Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B S hS X.1 X.2).O)).obj).map φ.val) t ∈
      SmallEtale.topology B S hS X.1 N.chart :=
    Stacks.SheafOfModules.EpiMono.imageSieve_mem_of_epi φ t
  obtain ⟨V, g, ⟨s, hs⟩, y, hy⟩ := (etaleSitePoint B S hS X.1 x X.2).jointly_surjective _ hmem
    ⟨N.point, N.point_comp⟩
  refine ⟨geometricModuleStalkGerm B S hS X x F ⟨V, y.1, y.2⟩ s, ?_⟩
  refine Eq.trans (geometricModuleStalkMap_germ B S hS X x φ ⟨V, y.1, y.2⟩ s) ?_
  refine Eq.trans (congrArg (geometricModuleStalkGerm B S hS X x G ⟨V, y.1, y.2⟩) hs) ?_
  exact geometricModuleStalkGerm_map B S hS X x G
    (⟨g, congrArg Subtype.val hy⟩ : (⟨V, y.1, y.2⟩ : SmallEtaleNeighborhood x) ⟶ N) t

/-- **Additivity of the length at a geometric point.** The length at a geometric point of the
middle term of a short exact sequence of `𝒪_X`-modules is the sum of the lengths of the two outer
terms: the geometric stalks form a short exact sequence of modules over the étale local ring, and
length is additive in a short exact sequence by Stacks 00IV. -/
theorem geometricLength_add_of_shortExact
    (σ : ShortComplex (Modules.{u, u} B S hS X.1 X.2)) (hσ : σ.ShortExact) :
    geometricLength B S hS X x σ.X₂ =
      geometricLength B S hS X x σ.X₁ + geometricLength B S hS X x σ.X₃ := by
  have := hσ.epi_g
  exact Module.length_eq_add_of_exact (geometricModuleStalkLinearMap B S hS X x σ.f)
    (geometricModuleStalkLinearMap B S hS X x σ.g)
    (injective_geometricModuleStalkMap_f_of_shortExact B S hS X x σ hσ)
    (surjective_geometricModuleStalkMap_of_epi B S hS X x σ.g)
    (exact_geometricModuleStalkMap_of_shortExact B S hS X x σ hσ)

end StalkSequence

/-! ### Additivity of the multiplicity -/

section MultiplicityAdditivity

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **Additivity of the multiplicity.** The multiplicity of an integral closed subspace in the
middle term of a short exact sequence of `𝒪_X`-modules is the sum of its multiplicities in the two
outer terms: the multiplicity is a length at a geometric point. -/
theorem moduleMultiplicity_add_of_shortExact (hX : IsAlgebraicSpace B S hS X)
    (σ : ShortComplex (Modules.{u, u} B S hS X hX)) (hσ : σ.ShortExact)
    (γ : points B S hS X → GeometricPoint B S hS X)
    (Z : IntegralClosedSubspace B S hS X) :
    moduleMultiplicity B S hS hX σ.X₂ γ Z =
      moduleMultiplicity B S hS hX σ.X₁ γ Z + moduleMultiplicity B S hS hX σ.X₃ γ Z :=
  geometricLength_add_of_shortExact B S hS ⟨X, hX⟩ _ σ hσ

/-- The multiplicity of an integral closed subspace whose generic point lies outside the support
of a quasi-coherent module is finite, being zero. -/
theorem moduleMultiplicity_ne_top_of_notMem_moduleSupport (hX : IsAlgebraicSpace B S hS X)
    (F : Modules.{u, u} B S hS X hX) [F.IsQuasicoherentOnSite]
    (γ : points B S hS X → GeometricPoint B S hS X)
    (hγ : ∀ x, (γ x).LiesOver x) (Z : IntegralClosedSubspace B S hS X)
    (hZ : Z.ambientGenericPoint B S hS ∉ moduleSupport B S hS hX F) :
    moduleMultiplicity B S hS hX F γ Z ≠ ⊤ := by
  rw [moduleMultiplicity_eq_zero_of_notMem_moduleSupport B S hS hX F γ hγ Z hZ]
  exact ENat.zero_ne_top

end MultiplicityAdditivity

/-! ### The integral closed subspace on an irreducible component of a closed set of points -/

section Components

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- An irreducible component of a closed set of points of an algebraic space, as an irreducible
closed subset of `|X|`: a component is irreducible and closed in the set, and the inclusion of a
closed set is a closed embedding. -/
def closedSetComponentPoints (T : Set (points B S hS X)) (hT : IsClosed T)
    (C : irreducibleComponents T) : IrreducibleCloseds (points B S hS X) where
  carrier := Subtype.val '' (C : Set T)
  isIrreducible' := C.2.1.image _ continuous_subtype_val.continuousOn
  isClosed' := hT.isClosedEmbedding_subtypeVal.isClosedMap _
    (isClosed_of_mem_irreducibleComponents _ C.2)

/-- The integral closed subspace of a decent algebraic space supported on an irreducible component
of a closed set of points: the reduced closed subspace of Stacks 03IQ on that component. -/
def closedSetComponent (hX : IsAlgebraicSpace B S hS X) (hXdec : IsDecentSpace B S hS X)
    (T : Set (points B S hS X)) (hT : IsClosed T) (C : irreducibleComponents T) :
    IntegralClosedSubspace B S hS X :=
  integralClosedSubspaceOfPoints B S hS hX hXdec (closedSetComponentPoints B S hS T hT C)

/-- The set of points of the integral closed subspace attached to an irreducible component of a
closed set of points is that component. -/
@[simp]
theorem subspacePointSet_closedSetComponent (hX : IsAlgebraicSpace B S hS X)
    (hXdec : IsDecentSpace B S hS X) (T : Set (points B S hS X)) (hT : IsClosed T)
    (C : irreducibleComponents T) :
    subspacePointSet B S hS X (closedSetComponent B S hS hX hXdec T hT C).subspace =
      Subtype.val '' (C : Set T) :=
  subspacePointSet_integralClosedSubspaceOfPoints B S hS hX hXdec _

/-- An integral closed subspace whose set of points is an irreducible component of a closed set of
points is the subspace attached to that component. -/
theorem eq_closedSetComponent (hX : IsAlgebraicSpace B S hS X) (hXdec : IsDecentSpace B S hS X)
    (T : Set (points B S hS X)) (hT : IsClosed T) (C : irreducibleComponents T)
    (Z : IntegralClosedSubspace B S hS X)
    (hZ : subspacePointSet B S hS X Z.subspace = Subtype.val '' (C : Set T)) :
    closedSetComponent B S hS hX hXdec T hT C = Z :=
  (eq_integralClosedSubspaceOfPoints B S hS hX hXdec Z
    (closedSetComponentPoints B S hS T hT C) hZ).symm

end Components

/-! ### The `k`-cycle associated to a coherent module -/

section Cycle

variable (D : BaseSpaceDimensionSituation.{u})
    {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}

/-- The coefficient of an integral closed subspace in `[F]_k` is its multiplicity in `F` when it
has δ-dimension `k`, and zero otherwise. -/
theorem cycleCoeffOfModule_eq_moduleMultiplicity (sX : X ⟶ D.space) (hX : D.IsGood sX)
    (F : Modules.{u, u} D.site D.base D.base_mem X hX.1) (k : ℤ)
    (γ : points D.site D.base D.base_mem X → GeometricPoint D.site D.base D.base_mem X)
    (Z : IntegralClosedSubspace D.site D.base D.base_mem X) :
    cycleCoeffOfModule D sX hX F k γ Z =
      if deltaDimension D sX Z = k then
        ((moduleMultiplicity D.site D.base D.base_mem hX.1 F γ Z).toNat : ℤ)
      else 0 :=
  rfl

/-- A nonzero coefficient in `[F]_k` forces the δ-dimension of the subspace to be `k`. -/
private theorem deltaDimension_eq_of_cycleCoeffOfModule_ne_zero (sX : X ⟶ D.space)
    (hX : D.IsGood sX) (F : Modules.{u, u} D.site D.base D.base_mem X hX.1) (k : ℤ)
    (γ : points D.site D.base D.base_mem X → GeometricPoint D.site D.base D.base_mem X)
    {Z : IntegralClosedSubspace D.site D.base D.base_mem X}
    (hZ : cycleCoeffOfModule D sX hX F k γ Z ≠ 0) : deltaDimension D sX Z = k := by
  by_contra h
  exact hZ (by rw [cycleCoeffOfModule_eq_moduleMultiplicity, ite_eq_right h])

/-- A point of δ-dimension `k` in a closed set of δ-dimension at most `k` is a generic point of an
irreducible component of that set. -/
private theorem exists_isGenericPoint_of_deltaDimension_eq (sX : X ⟶ D.space) (hX : D.IsGood sX)
    (T : Set (points D.site D.base D.base_mem X)) (hT : IsClosed T) (k : ℤ)
    (hdim : deltaDimensionClosed D sX hX T hT ≤ (k : EInt))
    {Z : IntegralClosedSubspace D.site D.base D.base_mem X} (hk : deltaDimension D sX Z = k)
    (hmem : Z.ambientGenericPoint D.site D.base D.base_mem ∈ T) :
    ∃ C : irreducibleComponents T,
      IsGenericPoint (⟨Z.ambientGenericPoint D.site D.base D.base_mem, hmem⟩ : T) C.1 :=
  isGenericPoint_of_deltaDimensionClosed_le D sX hX T hT _ hmem k hdim hk

/-- **The step at which Stacks 0EE6 enters.** Let `F` be a coherent `𝒪_X`-module on a good
algebraic space `X/B` whose support has δ-dimension at most `k`. An integral closed subspace whose
coefficient in `[F]_k` is nonzero has for its set of points an irreducible component of `Supp(F)`.

So the coefficient family of `[F]_k` is supported on exactly the subspaces the sum of Stacks 0EEB
part (2) runs over. A nonzero coefficient forces the δ-dimension to be `k` and the multiplicity to
be nonzero; the latter puts the generic point `ξ` of the subspace in `Supp(F)`, by Stacks 07TZ, and
the former makes the induced dimension function attain the bound at `ξ`, so Stacks 0EE6 makes `ξ`
a generic point of an irreducible component of `Supp(F)`. That component is then the closure of
`ξ`, which is the set of points of the subspace. -/
theorem exists_irreducibleComponents_of_cycleCoeffOfModule_ne_zero
    (sX : X ⟶ D.space) (hX : D.IsGood sX)
    (F : Modules.{u, u} D.site D.base D.base_mem X hX.1)
    [IsCoherent D.site D.base D.base_mem X hX.1 F] (k : ℤ)
    (γ : points D.site D.base D.base_mem X → GeometricPoint D.site D.base D.base_mem X)
    (hγ : ∀ x, (γ x).LiesOver x)
    (hdim : deltaDimensionClosed D sX hX (moduleSupport D.site D.base D.base_mem hX.1 F)
      (isClosed_moduleSupport D.site D.base D.base_mem hX.1 F) ≤ (k : EInt))
    (Z : IntegralClosedSubspace D.site D.base D.base_mem X)
    (hZ : cycleCoeffOfModule D sX hX F k γ Z ≠ 0) :
    ∃ C : irreducibleComponents (moduleSupport D.site D.base D.base_mem hX.1 F),
      subspacePointSet D.site D.base D.base_mem X Z.subspace =
        Subtype.val '' (C : Set (moduleSupport D.site D.base D.base_mem hX.1 F)) := by
  have hTcl : IsClosed (moduleSupport D.site D.base D.base_mem hX.1 F) :=
    isClosed_moduleSupport D.site D.base D.base_mem hX.1 F
  have hdk := deltaDimension_eq_of_cycleCoeffOfModule_ne_zero D sX hX F k γ hZ
  have hmult : moduleMultiplicity D.site D.base D.base_mem hX.1 F γ Z ≠ 0 := by
    intro h
    rw [cycleCoeffOfModule_eq_moduleMultiplicity, ite_eq_left hdk, h] at hZ
    simp at hZ
  have hmem : Z.ambientGenericPoint D.site D.base D.base_mem ∈
      moduleSupport D.site D.base D.base_mem hX.1 F := by
    by_contra h
    exact hmult (moduleMultiplicity_eq_zero_of_notMem_moduleSupport D.site D.base D.base_mem
      hX.1 F γ hγ Z h)
  obtain ⟨C, hC⟩ := exists_isGenericPoint_of_deltaDimension_eq D sX hX
    (moduleSupport D.site D.base D.base_mem hX.1 F) hTcl k hdim hdk hmem
  refine ⟨C, ?_⟩
  have himg := hTcl.isClosedEmbedding_subtypeVal.closure_image_eq
    ({⟨Z.ambientGenericPoint D.site D.base D.base_mem, hmem⟩} :
      Set (moduleSupport D.site D.base D.base_mem hX.1 F))
  rw [Set.image_singleton, hC] at himg
  exact (Z.isGenericPoint_ambientGenericPoint D.site D.base D.base_mem hX.1).symm.trans himg

/-- **Stacks 0EE5 for the coefficient family of `[F]_k`.** The sets of points of the integral
closed subspaces with nonzero coefficient in `[F]_k` form a locally finite collection, when the
support of the coherent module `F` has δ-dimension at most `k`.

Those sets of points are irreducible components of `Supp(F)`, by
`AlgebraicGeometry.Space.exists_irreducibleComponents_of_cycleCoeffOfModule_ne_zero`,
and an integral closed subspace is determined by its set of points, by Stacks 0ENF; so the
collection injects into the collection of all components of `Supp(F)`, which is locally finite by
Stacks 0EE5 — the point space of `X` being locally Noetherian, since the structure morphism of a
good algebraic space is locally of finite type over the locally Noetherian base. -/
theorem locallyFinite_cycleCoeffOfModule (sX : X ⟶ D.space) (hX : D.IsGood sX)
    (F : Modules.{u, u} D.site D.base D.base_mem X hX.1)
    [IsCoherent D.site D.base D.base_mem X hX.1 F] (k : ℤ)
    (γ : points D.site D.base D.base_mem X → GeometricPoint D.site D.base D.base_mem X)
    (hγ : ∀ x, (γ x).LiesOver x)
    (hdim : deltaDimensionClosed D sX hX (moduleSupport D.site D.base D.base_mem hX.1 F)
      (isClosed_moduleSupport D.site D.base D.base_mem hX.1 F) ≤ (k : EInt)) :
    LocallyFinite fun Z : IntegralClosedSubspace D.site D.base D.base_mem X =>
      if cycleCoeffOfModule D sX hX F k γ Z = 0 then
        (∅ : Set (points D.site D.base D.base_mem X))
      else subspacePointSet D.site D.base D.base_mem X Z.subspace := by
  have hN := isLocallyNoetherian_of_isLocallyOfFiniteType D.site D.base D.base_mem hX.1
    D.isAlgebraicSpace sX hX.2.2 D.locallyNoetherian
  intro p
  obtain ⟨t, htp, hfin⟩ := locallyFinite_irreducibleComponents_of_isClosed D.site D.base
    D.base_mem X hX.1 hN (moduleSupport D.site D.base D.base_mem hX.1 F)
    (isClosed_moduleSupport D.site D.base D.base_mem hX.1 F) p
  refine ⟨t, htp, (hfin.image (closedSetComponent D.site D.base D.base_mem hX.1
    (D.isDecentSpace_of_isGood sX hX) (moduleSupport D.site D.base D.base_mem hX.1 F)
    (isClosed_moduleSupport D.site D.base D.base_mem hX.1 F))).subset ?_⟩
  rintro Z ⟨q, hq, hqt⟩
  rw [Set.mem_ite_empty_left] at hq
  obtain ⟨C, hC⟩ := exists_irreducibleComponents_of_cycleCoeffOfModule_ne_zero D sX
    hX F k γ hγ hdim Z hq.1
  exact ⟨C, ⟨q, hC.subset hq.2, hqt⟩,
    eq_closedSetComponent D.site D.base D.base_mem hX.1 (D.isDecentSpace_of_isGood sX hX)
      (moduleSupport D.site D.base D.base_mem hX.1 F)
      (isClosed_moduleSupport D.site D.base D.base_mem hX.1 F) C Z hC⟩

/-- The coefficient family of `[F]_k` is a `k`-cycle: its support is locally finite by
`AlgebraicGeometry.Space.locallyFinite_cycleCoeffOfModule`, and a subspace with nonzero coefficient
has δ-dimension `k` by construction. -/
theorem cycleCoeffOfModule_mem_cyclesOfDimension (sX : X ⟶ D.space) (hX : D.IsGood sX)
    (F : Modules.{u, u} D.site D.base D.base_mem X hX.1)
    [IsCoherent D.site D.base D.base_mem X hX.1 F] (k : ℤ)
    (γ : points D.site D.base D.base_mem X → GeometricPoint D.site D.base D.base_mem X)
    (hγ : ∀ x, (γ x).LiesOver x)
    (hdim : deltaDimensionClosed D sX hX (moduleSupport D.site D.base D.base_mem hX.1 F)
      (isClosed_moduleSupport D.site D.base D.base_mem hX.1 F) ≤ (k : EInt)) :
    cycleCoeffOfModule D sX hX F k γ ∈ cyclesOfDimension D sX k := by
  refine ⟨locallyFinite_cycleCoeffOfModule D sX hX F k γ hγ hdim, fun Z hZ => ?_⟩
  exact deltaDimension_eq_of_cycleCoeffOfModule_ne_zero D sX hX F k γ hZ

/-- **Stacks 0EEB, part (2).** In Situation 0EDT let `X/B` be good, let `F` be a coherent
`𝒪_X`-module and assume `dim_δ(Supp(F)) ≤ k`. The *`k`-cycle associated to `F`* is

`[F]_k = ∑ m_{Z, F} [Z]`,

the sum over the integral closed subspaces `Z ⊆ X` whose set of points is an irreducible component
of `Supp(F)` of δ-dimension `k`, with `m_{Z, F}` the multiplicity of part (1).

As an element of `Z_k(X)` this is the coefficient family
`AlgebraicGeometry.Space.cycleCoeffOfModule`, which assigns `m_{Z, F}` to each `Z` of δ-dimension
`k`: off the support the multiplicity already vanishes, and
`AlgebraicGeometry.Space.exists_irreducibleComponents_of_cycleCoeffOfModule_ne_zero`
shows that the subspaces left with a nonzero coefficient are exactly the components of `Supp(F)`
of δ-dimension `k`, so the family is the displayed sum. That it is a `k`-cycle at all is
Stacks 0EE5, by `AlgebraicGeometry.Space.cycleCoeffOfModule_mem_cyclesOfDimension`. -/
@[stacks 0EEB "part (2): the k-cycle [F]_k of a coherent module, for a chosen geometric
  representative of each point; the reading at a point of |X| additionally needs the equivalence of
  Lemma 0EE1, which is not proved in this library"]
def associatedCycle (sX : X ⟶ D.space) (hX : D.IsGood sX)
    (F : Modules.{u, u} D.site D.base D.base_mem X hX.1)
    [IsCoherent D.site D.base D.base_mem X hX.1 F] (k : ℤ)
    (γ : points D.site D.base D.base_mem X → GeometricPoint D.site D.base D.base_mem X)
    (hγ : ∀ x, (γ x).LiesOver x)
    (hdim : deltaDimensionClosed D sX hX (moduleSupport D.site D.base D.base_mem hX.1 F)
      (isClosed_moduleSupport D.site D.base D.base_mem hX.1 F) ≤ (k : EInt)) :
    CycleGroup D sX k :=
  ⟨cycleCoeffOfModule D sX hX F k γ,
    cycleCoeffOfModule_mem_cyclesOfDimension D sX hX F k γ hγ hdim⟩

/-- The coefficient of an integral closed subspace in `[F]_k` is its multiplicity in `F` when it
has δ-dimension `k`, and zero otherwise. -/
theorem associatedCycle_apply (sX : X ⟶ D.space) (hX : D.IsGood sX)
    (F : Modules.{u, u} D.site D.base D.base_mem X hX.1)
    [IsCoherent D.site D.base D.base_mem X hX.1 F] (k : ℤ)
    (γ : points D.site D.base D.base_mem X → GeometricPoint D.site D.base D.base_mem X)
    (hγ : ∀ x, (γ x).LiesOver x)
    (hdim : deltaDimensionClosed D sX hX (moduleSupport D.site D.base D.base_mem hX.1 F)
      (isClosed_moduleSupport D.site D.base D.base_mem hX.1 F) ≤ (k : EInt))
    (Z : IntegralClosedSubspace D.site D.base D.base_mem X) :
    (associatedCycle D sX hX F k γ hγ hdim).1 Z =
      if deltaDimension D sX Z = k then
        ((moduleMultiplicity D.site D.base D.base_mem hX.1 F γ Z).toNat : ℤ)
      else 0 :=
  rfl

/-- An integral closed subspace of δ-dimension other than `k` has coefficient zero in `[F]_k`. -/
theorem associatedCycle_apply_eq_zero_of_deltaDimension_ne (sX : X ⟶ D.space) (hX : D.IsGood sX)
    (F : Modules.{u, u} D.site D.base D.base_mem X hX.1)
    [IsCoherent D.site D.base D.base_mem X hX.1 F] (k : ℤ)
    (γ : points D.site D.base D.base_mem X → GeometricPoint D.site D.base D.base_mem X)
    (hγ : ∀ x, (γ x).LiesOver x)
    (hdim : deltaDimensionClosed D sX hX (moduleSupport D.site D.base D.base_mem hX.1 F)
      (isClosed_moduleSupport D.site D.base D.base_mem hX.1 F) ≤ (k : EInt))
    {Z : IntegralClosedSubspace D.site D.base D.base_mem X}
    (hZ : deltaDimension D sX Z ≠ k) :
    (associatedCycle D sX hX F k γ hγ hdim).1 Z = 0 := by
  rw [associatedCycle_apply, ite_eq_right hZ]

/-- **The coefficient of `Z` in `[F]_k` at the chosen geometric point.** In Situation 0EDT let
`X/B` be good, let `F` be a coherent `𝒪_X`-module with `dim_δ(Supp(F)) ≤ k`, and let `Z` be an
integral closed subspace of `X` with `dim_δ(Z) = k` and generic point `ξ`. Then the coefficient of
`Z` in `[F]_k` is the length of `F` at the geometric point `γ ξ`, read in `ℤ` through
`ENat.toNat`. Stacks 0EEC itself, at every geometric point above `ξ` and with the length at `ξ`
shown finite, is `AlgebraicGeometry.Space.exists_associatedCycle_apply_eq_and_hasLengthAt`.

The generic point is `AlgebraicGeometry.Space.IntegralClosedSubspace.ambientGenericPoint`, which is
a generic point of `|Z|` by
`AlgebraicGeometry.Space.IntegralClosedSubspace.isGenericPoint_ambientGenericPoint`; the length is
read at the geometric point `γ` assigns to it, and is the multiplicity of part (1) of Stacks 0EEB.
No hypothesis asks `|Z|` to be an irreducible component of `Supp(F)`: the source reaches that case
from the dichotomy that `|Z|` is such a component exactly when `ξ` lies in `Supp(F)`, off which the
length vanishes, and both halves of it are already recorded here, as
`AlgebraicGeometry.Space.exists_irreducibleComponents_of_cycleCoeffOfModule_ne_zero` and
`AlgebraicGeometry.Space.moduleMultiplicity_eq_zero_of_notMem_moduleSupport`. -/
theorem associatedCycle_apply_eq_geometricLength (sX : X ⟶ D.space) (hX : D.IsGood sX)
    (F : Modules.{u, u} D.site D.base D.base_mem X hX.1)
    [IsCoherent D.site D.base D.base_mem X hX.1 F] (k : ℤ)
    (γ : points D.site D.base D.base_mem X → GeometricPoint D.site D.base D.base_mem X)
    (hγ : ∀ x, (γ x).LiesOver x)
    (hdim : deltaDimensionClosed D sX hX (moduleSupport D.site D.base D.base_mem hX.1 F)
      (isClosed_moduleSupport D.site D.base D.base_mem hX.1 F) ≤ (k : EInt))
    {Z : IntegralClosedSubspace D.site D.base D.base_mem X}
    (hZ : deltaDimension D sX Z = k) :
    (associatedCycle D sX hX F k γ hγ hdim).1 Z =
      ((geometricLength D.site D.base D.base_mem ⟨X, hX.1⟩
        (γ (Z.ambientGenericPoint D.site D.base D.base_mem)) F).toNat : ℤ) := by
  rw [associatedCycle_apply, ite_eq_left hZ, moduleMultiplicity]

/-- An integral closed subspace whose set of points is *not* an irreducible component of `Supp(F)`
has coefficient zero in `[F]_k`: this is the contrapositive of
`AlgebraicGeometry.Space.exists_irreducibleComponents_of_cycleCoeffOfModule_ne_zero`,
and together with `AlgebraicGeometry.Space.associatedCycle_apply` it says that `[F]_k` is the sum
of Stacks 0EEB part (2). -/
theorem associatedCycle_apply_eq_zero_of_not_isIrreducibleComponent (sX : X ⟶ D.space)
    (hX : D.IsGood sX) (F : Modules.{u, u} D.site D.base D.base_mem X hX.1)
    [IsCoherent D.site D.base D.base_mem X hX.1 F] (k : ℤ)
    (γ : points D.site D.base D.base_mem X → GeometricPoint D.site D.base D.base_mem X)
    (hγ : ∀ x, (γ x).LiesOver x)
    (hdim : deltaDimensionClosed D sX hX (moduleSupport D.site D.base D.base_mem hX.1 F)
      (isClosed_moduleSupport D.site D.base D.base_mem hX.1 F) ≤ (k : EInt))
    {Z : IntegralClosedSubspace D.site D.base D.base_mem X}
    (hZ : ¬ ∃ C : irreducibleComponents (moduleSupport D.site D.base D.base_mem hX.1 F),
      subspacePointSet D.site D.base D.base_mem X Z.subspace =
        Subtype.val '' (C : Set (moduleSupport D.site D.base D.base_mem hX.1 F))) :
    (associatedCycle D sX hX F k γ hγ hdim).1 Z = 0 := by
  by_contra h
  exact hZ (exists_irreducibleComponents_of_cycleCoeffOfModule_ne_zero D sX hX F k
    γ hγ hdim Z h)

/-- A coherent module with empty support has associated `k`-cycle `0`: every multiplicity vanishes,
the generic point of every integral closed subspace lying outside the support. -/
theorem associatedCycle_eq_zero_of_moduleSupport_eq_empty (sX : X ⟶ D.space) (hX : D.IsGood sX)
    (F : Modules.{u, u} D.site D.base D.base_mem X hX.1)
    [IsCoherent D.site D.base D.base_mem X hX.1 F] (k : ℤ)
    (γ : points D.site D.base D.base_mem X → GeometricPoint D.site D.base D.base_mem X)
    (hγ : ∀ x, (γ x).LiesOver x)
    (hdim : deltaDimensionClosed D sX hX (moduleSupport D.site D.base D.base_mem hX.1 F)
      (isClosed_moduleSupport D.site D.base D.base_mem hX.1 F) ≤ (k : EInt))
    (hempty : moduleSupport D.site D.base D.base_mem hX.1 F = ∅) :
    associatedCycle D sX hX F k γ hγ hdim = 0 := by
  refine Subtype.ext (funext fun Z => ?_)
  rw [associatedCycle_apply, moduleMultiplicity_eq_zero_of_notMem_moduleSupport D.site D.base
    D.base_mem hX.1 F γ hγ Z (by simp [hempty])]
  simp

/-- **Stacks 0EEE.** In Situation 0EDT let `X/B` be good and let `0 → F → G → H → 0` be a short
exact sequence of coherent `𝒪_X`-modules whose three supports have δ-dimension at most `k`. Then

`[G]_k = [F]_k + [H]_k`.

Coefficientwise this is additivity of the multiplicity,
`AlgebraicGeometry.Space.moduleMultiplicity_add_of_shortExact`, hence additivity of length in a
short exact sequence, Stacks 00IV, at the generic point of each integral closed subspace of
δ-dimension `k`; at the subspaces of other δ-dimension all three coefficients vanish.

Cycle coefficients are integers, reached from the `ℕ∞`-valued multiplicity by `ENat.toNat`, which
is additive only on finite values, so the proof also needs the multiplicities of the middle term to
be finite at the subspaces of δ-dimension `k`. Off its support the multiplicity is zero. On its
support, the generic point of such a subspace attains the δ-dimension bound, so it is a generic
point of an irreducible component of the support by Stacks 0EE6
(`AlgebraicGeometry.Space.isGenericPoint_of_deltaDimensionClosed_le`), and the length there is
finite by Stacks 0EE4
(`AlgebraicGeometry.Space.geometricLength_ne_top_and_pos_of_isGenericPoint_supportOfSheaf`).

The cycles are read at the geometric points `γ` chooses above the points of `|X|`; by Stacks 0EE1,
`AlgebraicGeometry.Space.geometricLength_eq_of_image_eq`, the lengths, hence the cycles, do not
depend on that choice. -/
@[stacks 0EEE]
theorem associatedCycle_add_of_shortExact (sX : X ⟶ D.space) (hX : D.IsGood sX)
    (σ : ShortComplex (Modules.{u, u} D.site D.base D.base_mem X hX.1)) (hσ : σ.ShortExact)
    [IsCoherent D.site D.base D.base_mem X hX.1 σ.X₁]
    [IsCoherent D.site D.base D.base_mem X hX.1 σ.X₂]
    [IsCoherent D.site D.base D.base_mem X hX.1 σ.X₃] (k : ℤ)
    (γ : points D.site D.base D.base_mem X → GeometricPoint D.site D.base D.base_mem X)
    (hγ : ∀ x, (γ x).LiesOver x)
    (hdim₁ : deltaDimensionClosed D sX hX
      (moduleSupport D.site D.base D.base_mem hX.1 σ.X₁)
      (isClosed_moduleSupport D.site D.base D.base_mem hX.1 σ.X₁) ≤ (k : EInt))
    (hdim₂ : deltaDimensionClosed D sX hX
      (moduleSupport D.site D.base D.base_mem hX.1 σ.X₂)
      (isClosed_moduleSupport D.site D.base D.base_mem hX.1 σ.X₂) ≤ (k : EInt))
    (hdim₃ : deltaDimensionClosed D sX hX
      (moduleSupport D.site D.base D.base_mem hX.1 σ.X₃)
      (isClosed_moduleSupport D.site D.base D.base_mem hX.1 σ.X₃) ≤ (k : EInt)) :
    associatedCycle D sX hX σ.X₂ k γ hγ hdim₂ =
      associatedCycle D sX hX σ.X₁ k γ hγ hdim₁ +
        associatedCycle D sX hX σ.X₃ k γ hγ hdim₃ := by
  have hco : ∀ Z : IntegralClosedSubspace D.site D.base D.base_mem X,
      (associatedCycle D sX hX σ.X₂ k γ hγ hdim₂).1 Z =
        (associatedCycle D sX hX σ.X₁ k γ hγ hdim₁).1 Z +
          (associatedCycle D sX hX σ.X₃ k γ hγ hdim₃).1 Z := by
    intro Z
    by_cases hk : deltaDimension D sX Z = k
    · have hadd := moduleMultiplicity_add_of_shortExact D.site D.base D.base_mem hX.1 σ hσ γ Z
      have htop : moduleMultiplicity D.site D.base D.base_mem hX.1 σ.X₁ γ Z +
          moduleMultiplicity D.site D.base D.base_mem hX.1 σ.X₃ γ Z ≠ ⊤ := by
        rw [← hadd]
        by_cases hmem : Z.ambientGenericPoint D.site D.base D.base_mem ∈
            moduleSupport D.site D.base D.base_mem hX.1 σ.X₂
        · obtain ⟨C, hC⟩ := exists_isGenericPoint_of_deltaDimension_eq D sX hX
            (moduleSupport D.site D.base D.base_mem hX.1 σ.X₂)
            (isClosed_moduleSupport D.site D.base D.base_mem hX.1 σ.X₂) k hdim₂ hk hmem
          exact (geometricLength_ne_top_and_pos_of_isGenericPoint_supportOfSheaf D.site D.base
            D.base_mem ⟨X, hX.1⟩
            (isLocallyNoetherian_of_isLocallyOfFiniteType D.site D.base D.base_mem hX.1
              D.isAlgebraicSpace sX hX.2.2 D.locallyNoetherian)
            (D.isDecentSpace_of_isGood sX hX) σ.X₂ hmem C hC _
            (hγ (Z.ambientGenericPoint D.site D.base D.base_mem))).1
        · exact moduleMultiplicity_ne_top_of_notMem_moduleSupport D.site D.base D.base_mem
            hX.1 σ.X₂ γ hγ Z hmem
      rw [associatedCycle_apply, associatedCycle_apply, associatedCycle_apply, ite_eq_left hk,
        ite_eq_left hk, ite_eq_left hk, hadd,
        ENat.toNat_add (fun h => htop (by rw [h, top_add]))
          (fun h => htop (by rw [h, add_top]))]
      push_cast
      rfl
    · rw [associatedCycle_apply_eq_zero_of_deltaDimension_ne D sX hX σ.X₂ k γ hγ hdim₂ hk,
        associatedCycle_apply_eq_zero_of_deltaDimension_ne D sX hX σ.X₁ k γ hγ hdim₁ hk,
        associatedCycle_apply_eq_zero_of_deltaDimension_ne D sX hX σ.X₃ k γ hγ hdim₃ hk,
        add_zero]
  exact Subtype.ext (funext hco)

end Cycle

end AlgebraicGeometry.Space

end
