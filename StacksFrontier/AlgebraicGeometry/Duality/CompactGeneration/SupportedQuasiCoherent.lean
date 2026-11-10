module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import StacksFrontier.Algebra.Homology.DerivedCategory.SerreSubcategory
public import StacksFrontier.Homology.DerivedCategory.LocallySmall
public import StacksFrontier.AlgebraicGeometry.DerivedTilde.Quasicoherent
public import StacksFrontier.Topology.Sheaves.Modules.Exactness

/-!
# The triangulated subcategory of complexes with support in a closed subset

Let `𝒪` be a sheaf of rings on a topological space `X` and let `T ⊆ X` be a subset. A sheaf of
`𝒪`-modules is *supported on `T`* when all of its stalks at points outside `T` vanish, and an
object of the derived category `D(𝒪)` is supported on `T` when all of its cohomology sheaves are.
Stacks 0A9A speaks about the strictly full, saturated, triangulated subcategory
`D_{QCoh,T}(𝒪_X) ⊆ D(𝒪_X)` of complexes whose cohomology sheaves are quasi-coherent *and*
supported on `T`; this file constructs that subcategory and proves it is one.

The mechanism is Stacks 06UP: an object property of an abelian category which is a weak Serre
subcategory (Stacks 02MO) cuts out a strictly full saturated triangulated subcategory of the
derived category, which is `CategoryTheory.ObjectProperty.IsTriangulated` of
`DerivedCategoryB.derivedCategoryB`. So the work is to show that the supported sheaves form a
weak Serre subcategory, and that is a one-line consequence of exactness being detected on stalks
(Stacks 01AG): in an exact sequence `M₁ → M₂ → M₃` of sheaves of modules the stalk sequence
`(M₁)ₓ → (M₂)ₓ → (M₃)ₓ` is exact, so if the two outer stalks vanish so does the middle one.
Quasi-coherence is a weak Serre subcategory by Stacks 06VT, which is an explicit argument of the
statements for a general scheme because it is not yet available in this repository at that
generality; for an affine scheme it is discharged.

## Main definitions

* `Stacks.Duality.supportedModules` — the sheaves of `𝒪`-modules whose stalks vanish off `T`.
* `Stacks.Duality.derivedSupported` — `D_T(𝒪)`, the objects of the derived category whose
  cohomology sheaves are supported on `T` (Stacks 08DA).
* `Stacks.Duality.quasiCoherentSupported` — `D_{QCoh,T}(𝒪_Z)` for a scheme `Z`, the meet of
  quasi-coherent cohomology with support in `T`.
* `Stacks.Duality.QuasiCoherentSupportedDerivedCategory` — the same thing as a category.

## Main results

* `Stacks.Duality.supportedModules_isWeakSerre` — the supported sheaves of modules form a weak
  Serre subcategory of all sheaves of `𝒪`-modules.
* `Stacks.Duality.derivedSupported_isTriangulated`,
  `Stacks.Duality.derivedSupported_isStableUnderRetracts` — `D_T(𝒪)` is a strictly full,
  saturated, triangulated subcategory of `D(𝒪)`.
* `Stacks.Duality.quasiCoherentSupported_isTriangulated`,
  `Stacks.Duality.quasiCoherentSupported_isStableUnderRetracts` — the same for
  `D_{QCoh,T}(𝒪_Z)`, given that quasi-coherent `𝒪_Z`-modules form a weak Serre subcategory.

## Implementation notes

No `@[stacks]` attribute is attached. Tag 0A9A has a single tagged statement, the existence of a
perfect generator, and that is not proved here: what is built is the category the tag speaks
about. Tag 08DA already carries `AlgebraicGeometry.CohomologySupportedOn` in
`StacksFrontier/AlgebraicGeometry/Perfect/SupportedCohomology.lean`; `derivedSupported` is the same
notion, differing in two respects which are both the reason it is restated. First, that
declaration is elaborated under a file-level `attribute [local instance]
HasDerivedCategory.standard`, so its derived-category argument is pinned to the standard model,
whose morphisms live a universe above its objects; the statements of Stacks 09IS and 0A9A are
about direct sums indexed by the morphism universe and are *false* rather than unavailable there
(see the implementation notes of `StacksFrontier/Homology/DerivedCategory/LocallySmall.lean`), so a
subcategory of the standard derived category cannot be used for them. The derived category here is
left as an instance argument, and the affine statements below are elaborated at the locally small
instance `SheafOfModules.hasDerivedCategory`. Second, `derivedSupported`
is phrased as `DerivedCategoryB.derivedCategoryB` of an object property on the modules, which is
what the weak Serre machinery of Stacks 06UP consumes and hence what produces the triangulated
structure.

The support condition is stated stalkwise rather than as containment of the support of the
cohomology sheaves, for the reason given in
`StacksFrontier/AlgebraicGeometry/Perfect/SupportedCohomology.lean`: in the derived category
the cohomology sheaves are determined only up to isomorphism.

Weak Serre-ness of quasi-coherent modules (Stacks 06VT) is a hypothesis of the theorems about a
general scheme and not of the definitions, because `quasiCoherentSupported` itself does not need
it — only the triangulated structure does. It is not a class, so it cannot be an instance
argument. For `Z = Spec R` it is supplied by `AlgebraicGeometry.isQuasicoherent_isWeakSerre`, and
the `spec*` theorems below carry no hypothesis at all.

Everything is phrased over `SheafOfModules.{u} Z.ringCatSheaf` rather than
`AlgebraicGeometry.Scheme.Modules`, in which Stacks 0A9A was previously stated. The two are
definitionally equal but carry separately declared `Category`, `Preadditive` and `Abelian`
instances, and instance search does not cross between them, so a statement about one is not
usable for the other without transport.

## References

* [Stacks Project, Tag 0A9A](https://stacks.math.columbia.edu/tag/0A9A)
* [Stacks Project, Tag 08DA](https://stacks.math.columbia.edu/tag/08DA)
* [Stacks Project, Tag 02MO](https://stacks.math.columbia.edu/tag/02MO)
* [Stacks Project, Tag 06UP](https://stacks.math.columbia.edu/tag/06UP)
* [Stacks Project, Tag 06VT](https://stacks.math.columbia.edu/tag/06VT)
* [Stacks Project, Tag 01AG](https://stacks.math.columbia.edu/tag/01AG)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for sheaves of modules on a small site.
attribute [local instance] SheafOfModules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty
  TopologicalSpace WeakSerre

universe w u

namespace Stacks.Duality

/-! ### Sheaves of modules supported on a subset -/

section Modules

variable {X : TopCat.{u}} (𝒪 : Sheaf (Opens.grothendieckTopology X) RingCat.{u}) (T : Set X)

/-- A sheaf of `𝒪`-modules is supported on `T` when its stalk at every point outside `T`
vanishes. -/
def supportedModules : ObjectProperty (SheafOfModules.{u} 𝒪) :=
  fun M => ∀ x : X, x ∉ T → IsZero ((SheafOfModules.stalkAddCommGroupFunctor 𝒪 x).obj M)

/-- A sheaf of `𝒪`-modules `M` is supported on `T` if and only if its stalk at every point
outside `T` is zero. -/
theorem supportedModules_iff (M : SheafOfModules.{u} 𝒪) :
    supportedModules 𝒪 T M ↔
      ∀ x : X, x ∉ T → IsZero ((SheafOfModules.stalkAddCommGroupFunctor 𝒪 x).obj M) :=
  Iff.rfl

/-- Support on `T` is invariant under isomorphism of sheaves of modules. -/
instance supportedModules_isClosedUnderIsomorphisms :
    (supportedModules 𝒪 T).IsClosedUnderIsomorphisms where
  of_iso e hM x hx :=
    (hM x hx).of_iso ((SheafOfModules.stalkAddCommGroupFunctor 𝒪 x).mapIso e.symm)

/-- A zero sheaf of modules is supported on every subset. -/
theorem supportedModules_of_isZero (M : SheafOfModules.{u} 𝒪) (hM : IsZero M) :
    supportedModules 𝒪 T M :=
  fun _ _ => Functor.map_isZero _ hM

/-- **The sheaves of modules supported on `T` form a weak Serre subcategory** (Stacks 02MO).
Closure under isomorphism and nonemptiness are immediate; the defining condition is exactness on
stalks (Stacks 01AG). Given an exact sequence `M₀ → M₁ → M₂ → M₃ → M₄` whose four outer terms are
supported on `T`, and a point `x ∉ T`, the stalk sequence `(M₁)ₓ → (M₂)ₓ → (M₃)ₓ` is exact with
both ends zero, so `(M₂)ₓ` vanishes. Only exactness at `M₂` is used. -/
theorem supportedModules_isWeakSerre : IsWeakSerre (supportedModules 𝒪 T) where
  isClosedUnderIsomorphisms := supportedModules_isClosedUnderIsomorphisms 𝒪 T
  nonempty :=
    ⟨(inferInstance : HasZeroObject (SheafOfModules.{u} 𝒪)).zero.choose,
      supportedModules_of_isZero 𝒪 T _
        (inferInstance : HasZeroObject (SheafOfModules.{u} 𝒪)).zero.choose_spec⟩
  mem_of_exact5 E _ h₁ h₃ _ := fun x hx =>
    (((SheafOfModules.exact_iff_stalkShortComplex_exact 𝒪
      (ShortComplex.mk E.f₁ E.f₂ E.zero₁)).1 E.exact₂) x).isZero_of_both_isZero
      (h₁ x hx) (h₃ x hx)

end Modules

/-! ### The derived category of complexes supported on a subset -/

section Derived

variable {X : TopCat.{u}} (𝒪 : Sheaf (Opens.grothendieckTopology X) RingCat.{u}) (T : Set X)
  [HasDerivedCategory.{w} (SheafOfModules.{u} 𝒪)]

/-- `D_T(𝒪)`: the objects of the derived category of sheaves of `𝒪`-modules all of whose
cohomology sheaves are supported on `T` (Stacks 08DA). The derived category is an instance
argument, so that the statement applies in particular to the locally small model, which is the
only one for which the compact-generation statements of Stacks 09IS and 0A9A have content. -/
abbrev derivedSupported : ObjectProperty (DerivedCategory (SheafOfModules.{u} 𝒪)) :=
  DerivedCategoryB.derivedCategoryB (supportedModules 𝒪 T)

/-- An object `K` of `D(𝒪)` lies in `D_T(𝒪)` if and only if, for every `n : ℤ`, the stalk of its
`n`-th cohomology sheaf at every point outside `T` is zero. -/
theorem derivedSupported_iff (K : DerivedCategory (SheafOfModules.{u} 𝒪)) :
    derivedSupported 𝒪 T K ↔
      ∀ (n : ℤ) (x : X), x ∉ T → IsZero ((SheafOfModules.stalkAddCommGroupFunctor 𝒪 x).obj
        ((DerivedCategory.homologyFunctor (SheafOfModules.{u} 𝒪) n).obj K)) :=
  Iff.rfl

/-- `D_T(𝒪)` is strictly full. -/
instance derivedSupported_isClosedUnderIsomorphisms :
    (derivedSupported 𝒪 T).IsClosedUnderIsomorphisms :=
  DerivedCategoryB.derivedCategoryB_isClosedUnderIsomorphisms _
    (supportedModules_isWeakSerre 𝒪 T)

/-- **`D_T(𝒪)` is a triangulated subcategory of `D(𝒪)`** (Stacks 06UP applied to the weak Serre
subcategory of supported sheaves). -/
instance derivedSupported_isTriangulated : (derivedSupported 𝒪 T).IsTriangulated :=
  DerivedCategoryB.derivedCategoryB_isTriangulated _ (supportedModules_isWeakSerre 𝒪 T)

/-- **`D_T(𝒪)` is saturated**: a direct summand of a complex supported on `T` is supported on
`T`. -/
instance derivedSupported_isStableUnderRetracts :
    (derivedSupported 𝒪 T).IsStableUnderRetracts :=
  DerivedCategoryB.derivedCategoryB_isStableUnderRetracts _ (supportedModules_isWeakSerre 𝒪 T)

end Derived

/-! ### Quasi-coherent complexes with support, on a scheme -/

section Scheme

variable (Z : Scheme.{u}) (T : Set Z)
  [HasDerivedCategory.{w} (SheafOfModules.{u} Z.ringCatSheaf)]

/-- Quasi-coherence of all the cohomology sheaves, as an object property of `D(𝒪_Z)`. -/
abbrev derivedQuasiCoherent :
    ObjectProperty (DerivedCategory (SheafOfModules.{u} Z.ringCatSheaf)) :=
  DerivedCategoryB.derivedCategoryB (SheafOfModules.isQuasicoherent Z.ringCatSheaf)

/-- `D_{QCoh,T}(𝒪_Z)`: the objects of the derived category of `𝒪_Z`-modules whose cohomology
sheaves are quasi-coherent and supported on `T`. This is the category Stacks 0A9A asserts to be
generated by a single perfect object. -/
abbrev quasiCoherentSupported :
    ObjectProperty (DerivedCategory (SheafOfModules.{u} Z.ringCatSheaf)) :=
  derivedQuasiCoherent Z ⊓ derivedSupported Z.ringCatSheaf T

/-- `D_{QCoh,T}(𝒪_Z)` as a category. -/
abbrev QuasiCoherentSupportedDerivedCategory : Type (u + 1) :=
  (quasiCoherentSupported Z T).FullSubcategory

/-- An object `K` of `D(𝒪_Z)` lies in `D_{QCoh,T}(𝒪_Z)` if and only if all of its cohomology
sheaves are quasi-coherent and `K` lies in `D_T(𝒪_Z)`. -/
theorem quasiCoherentSupported_iff
    (K : DerivedCategory (SheafOfModules.{u} Z.ringCatSheaf)) :
    quasiCoherentSupported Z T K ↔
      (∀ n : ℤ, ((DerivedCategory.homologyFunctor
          (SheafOfModules.{u} Z.ringCatSheaf) n).obj K).IsQuasicoherent) ∧
        derivedSupported Z.ringCatSheaf T K :=
  Iff.rfl

/-- `D_{QCoh,T}(𝒪_Z)` is strictly full. -/
theorem quasiCoherentSupported_isClosedUnderIsomorphisms
    (hqc : IsWeakSerre (SheafOfModules.isQuasicoherent Z.ringCatSheaf)) :
    (quasiCoherentSupported Z T).IsClosedUnderIsomorphisms := by
  have := DerivedCategoryB.derivedCategoryB_isClosedUnderIsomorphisms _ hqc
  infer_instance

/-- **`D_{QCoh,T}(𝒪_Z)` is a triangulated subcategory of `D(𝒪_Z)`**: a meet of two triangulated
subcategories, one cut out by quasi-coherence of the cohomology sheaves (Stacks 06VT) and one by
their support (Stacks 08DA). -/
theorem quasiCoherentSupported_isTriangulated
    (hqc : IsWeakSerre (SheafOfModules.isQuasicoherent Z.ringCatSheaf)) :
    (quasiCoherentSupported Z T).IsTriangulated := by
  have := DerivedCategoryB.derivedCategoryB_isClosedUnderIsomorphisms _ hqc
  have := DerivedCategoryB.derivedCategoryB_isTriangulated _ hqc
  infer_instance

/-- **`D_{QCoh,T}(𝒪_Z)` is saturated**: a direct summand of a complex with quasi-coherent
cohomology supported on `T` is again one. -/
theorem quasiCoherentSupported_isStableUnderRetracts
    (hqc : IsWeakSerre (SheafOfModules.isQuasicoherent Z.ringCatSheaf)) :
    (quasiCoherentSupported Z T).IsStableUnderRetracts := by
  have hq := DerivedCategoryB.derivedCategoryB_isStableUnderRetracts _ hqc
  exact ⟨fun h hY => ⟨hq.of_retract h hY.1, prop_of_retract _ h hY.2⟩⟩

end Scheme

/-! ### The affine case, at the locally small derived category -/

section Affine

variable (R : CommRingCat.{u}) (T : Set (Spec R))

/-- **`D_{QCoh,T}(𝒪_{Spec R})` is a strictly full, saturated, triangulated subcategory of
`D(𝒪_{Spec R})`.** This is the concrete, hypothesis-free form of the statements above: on an
affine scheme the quasi-coherent modules are known to form a weak Serre subcategory
(`AlgebraicGeometry.isQuasicoherent_isWeakSerre`), which is the one input the general scheme
statements take as an argument.

The derived category is the locally small one, `SheafOfModules.hasDerivedCategory`: its morphisms
lie in `Type u`, which is also the universe indexing the direct sums that sheaves of modules
have. That is the model in which the compact-generation statements of Stacks 09IS and 0A9A have
content; with `HasDerivedCategory.standard` the morphisms live in `Type (u + 1)` and the direct
sums Brown representability asks for do not exist. -/
theorem specQuasiCoherentSupported_isTriangulated :
    (quasiCoherentSupported.{u, u} (Spec R) T).IsTriangulated :=
  quasiCoherentSupported_isTriangulated _ _ (isQuasicoherent_isWeakSerre R)

/-- `D_{QCoh,T}(𝒪_{Spec R})` is strictly full. -/
theorem specQuasiCoherentSupported_isClosedUnderIsomorphisms :
    (quasiCoherentSupported.{u, u} (Spec R) T).IsClosedUnderIsomorphisms :=
  quasiCoherentSupported_isClosedUnderIsomorphisms _ _ (isQuasicoherent_isWeakSerre R)

/-- `D_{QCoh,T}(𝒪_{Spec R})` is saturated: a direct summand of a complex with quasi-coherent
cohomology supported on `T` is again one. -/
theorem specQuasiCoherentSupported_isStableUnderRetracts :
    (quasiCoherentSupported.{u, u} (Spec R) T).IsStableUnderRetracts :=
  quasiCoherentSupported_isStableUnderRetracts _ _ (isQuasicoherent_isWeakSerre R)

end Affine

end Stacks.Duality

end
