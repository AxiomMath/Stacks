module

public import Mathlib.CategoryTheory.Sites.DenseSubsite.InducedTopology
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.AffineSiteQuasiCoherentObjects
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ModulesOnACategory.CartesianBrownRepresentability
public import StacksFrontier.CategoryTheory.Triangulated.GeneratingFamilyAlongAdjunction
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ModulesOnACategory.PullbackQuasiCoherentBaseChange
import StacksCore.Tactic.StacksAttribute

/-!
# The small affine Zariski site of a scheme as a `Type u`-small ringed site

Let `X` be a scheme in `Scheme.{u}`. This file packages the small affine Zariski site of `X` — the
affine opens of the underlying space, with **all** inclusions as arrows, as in
[Stacks, Tag 0GZX] — as a `AlgebraicGeometry.RingedSite.{u, u, u}`: both its objects and its
morphisms live in `Type u`, and so does the universe of sections of its structure sheaf.

That is the whole point of the packaging. The library already has the same site built out of the
big Zariski site, `AlgebraicGeometry.smallAffineZariskiRingedSite`, but there the objects are
objects of the big Zariski site and therefore live in `Type (u + 1)`; every index universe
derived from it is `max (u + 1) w`, while the derived category of `𝒪_X`-modules on the space `X`
has morphisms in `Type u` and direct sums indexed by `Type u` only. The coverage note of
`StacksFrontier/AlgebraicGeometry/DerivedQCoh/AffineSiteQuasiCoherentObjects.lean` records that
obstruction and names the fix, which is this file: the affine opens of the *space*,
`{U : X.Opens // IsAffineOpen U}`, already form a `Type u`, and they carry the inclusion order,
hence a `CategoryTheory.SmallCategory` instance with morphisms in `Type u`.

Everything the library proves about the small affine site is then available at these universes.
In particular the generating family of [Stacks, Tag 0GYG] produced by
`Stacks.ModulesOnACategory.QuasiCoherentEquivalence.exists_qc_generating_family`, whose index
universe is `max u v r w` for a site with objects in `Type u`, morphisms in `Type v`, section
rings in `Type r` and modules in `Type w`, is indexed by a `Type u` here — see
`AlgebraicGeometry.exists_generating_family_affineChaoticDerivedQuasiCoherent`.

## Main definitions

* `AlgebraicGeometry.Scheme.affineOpensToOpens`: the inclusion functor from the affine opens of
  `X` to all opens of `X`. It is full and faithful, and a dense subsite for the Zariski topology.
* `AlgebraicGeometry.Scheme.affineOpensTopology`: the Zariski topology on the affine opens of
  `X`, induced from `TopologicalSpace.Opens.grothendieckTopology`.
* `AlgebraicGeometry.Scheme.affineZariskiRingedSite`: the ringed site
  `(X_{affine, Zar}, 𝒪)` of [Stacks, Tag 0GZZ] (3), as a `RingedSite.{u, u, u}`.
* `AlgebraicGeometry.Scheme.affineChaoticRingedSite`: the ringed site `(X_affine, 𝒪)` of
  [Stacks, Tag 0GZZ] (4) — the same category and structure sheaf with the chaotic topology — as
  a `RingedSite.{u, u, u}`.
* `AlgebraicGeometry.affineChaoticBaseChangeData`: derived base-change data for its structure
  sheaf.

## Main results

* `AlgebraicGeometry.Scheme.mem_affineOpensTopology`: a sieve on an affine open `U` covers it
  exactly when its members cover `U` pointwise, so the topology is the Zariski one.
* `AlgebraicGeometry.flat_presheaf_map_of_isAffineOpen`: the restriction homomorphism
  `Γ(X, U) ⟶ Γ(X, V)` attached to an inclusion `V ≤ U` of affine opens is flat.
* `AlgebraicGeometry.affineChaotic_isQC_eq_hasQuasicoherentCohomology`,
  `AlgebraicGeometry.affineChaoticDerivedQuasiCoherentEquivQC` and
  `AlgebraicGeometry.affineChaoticDerivedQuasiCoherentEquivQC_functor_comp_ι`: **the equivalence
  (4) ≃ (5) of [Stacks, Tag 0GZZ]** at these universes, in the sharp form of an equality of
  subcategories of `D(X_affine, 𝒪)`.
* `AlgebraicGeometry.exists_generating_family_affineChaoticDerivedQuasiCoherent` and
  `AlgebraicGeometry.exists_generating_family_qcohCohomology_affineChaotic`: **a generating
  family in the sense of [Stacks, Tag 0GYG] for `QC(X_affine, 𝒪)` and for
  `D_QCoh(X_affine, 𝒪)`, indexed by a `Type u`**, for an arbitrary scheme `X : Scheme.{u}` and
  with no hypothesis.
* `AlgebraicGeometry.affineChaotic_qcohCohomologyProperty_isClosedUnderColimitsOfShape`:
  `D_QCoh(X_affine, 𝒪)` is closed under arbitrary direct sums, which is what makes the second
  condition of [Stacks, Tag 0GYG] statable on it.
* `AlgebraicGeometry.exists_isTriangulated_rightAdjoint_affineChaoticDerivedQuasiCoherent`:
  **[Stacks, Tag 0GZ0] part (3) on `D_QCoh(X_affine, 𝒪)`** at these universes: an exact,
  direct-sum-preserving functor out of it, into a triangulated category with morphisms in
  `Type u`, has an exact right adjoint.

## Implementation notes

**The arrows are all inclusions, not the basic opens.** Mathlib has
`AlgebraicGeometry.Scheme.AffineZariskiSite`, which is the same *type*
`{U : X.Opens // IsAffineOpen U}` in `Type u`, but its order is `U ≤ V ↔ ∃ f : Γ(X, V),
X.basicOpen f = U`, so its arrows are only the basic-open inclusions; its own module docstring
records that this differs from the Stacks definition. The site of [Stacks, Tag 0GZX] has all
inclusions, and that is the one built here, as the subtype coercion
`↥X.affineOpens → X.Opens` is monotone for the inclusion order inherited from `X.Opens`. The two
sites have the same objects and the same structure presheaf, and both are dense subsites of
`X.Opens`, but they are different categories, so no statement here is about Mathlib's site.

**Density is easier here than for the basic opens.** `affineOpensToOpens` is *full*, because an
inclusion of affine opens is an arrow of the site, so
`CategoryTheory.Functor.IsLocallyFull` is automatic; only cover-density needs an argument, and
that is `AlgebraicGeometry.Scheme.isBasis_affineOpens`.

**Flatness is where the geometry enters.** For affine opens `V ≤ U` the induced morphism of
schemes `X ∣_ᵤ V ⟶ X ∣_ᵤ U` is an open immersion between affine schemes, hence flat, and
`AlgebraicGeometry.Scheme.Hom.flat_appTop` turns that into flatness of the map on global
functions. This is what [Stacks, Tag 0GZR] consumes, through
`Stacks.ModulesOnACategory.QuasiCoherentCohomology.isQC_eq_hasQuasicoherentCohomology`, to
identify `QC(X_affine, 𝒪)` with `D_QCoh(X_affine, 𝒪)` on the nose.

**No `stacks 0GYG` and no `stacks 0A9E` attribute is attached.** Tag 0GYG is weak Brown
representability itself, which the library has as
`CategoryTheory.Pretriangulated.exists_iso_preadditiveYoneda_of_isHomological_of_generating`;
`exists_generating_family_affineChaoticDerivedQuasiCoherent` produces a family satisfying its
hypothesis, which is [Stacks, Tag 0GYZ], not the tag itself. And nothing here is a statement
about `D_QCoh(𝒪_X)`: of the comparisons (1) ≃ (2) ≃ (3) ≃ (4) of [Stacks, Tag 0GZZ] the step
(1) ≃ (3) is proved — on modules in
`StacksFrontier/AlgebraicGeometry/DerivedQCoh/AffineOpensQuasiCoherentReflection.lean` and on
derived categories in
`StacksFrontier/AlgebraicGeometry/DerivedQCoh/AffineOpensDerivedComparison.lean` — and the step
(3) ≃ (4), which is where the family below lives, in
`StacksFrontier/AlgebraicGeometry/DerivedQCoh/AffineOpensChaoticComparison.lean`. The family below
is
carried across that chain to `D_QCoh(𝒪_X)`, and [Stacks, Tag 0A9E] deduced from it, in
`StacksFrontier/AlgebraicGeometry/DerivedQCoh/AffineOpensChaoticQuasicoherentEquality.lean`.

## Coverage limits

What this file removes is the *universe* obstruction described in the section "The hom-universe
obstruction to (1) ≃ (5)" of
`StacksFrontier/AlgebraicGeometry/DerivedQCoh/AffineSiteQuasiCoherentObjects.lean`: with the site
packaged at `RingedSite.{u, u, u}`, the morphisms of `QC(X_affine, 𝒪)` and the index universe of
its direct sums are `Type u`, matching `D_QCoh(𝒪_X)`. It does **not** supply the comparisons
themselves.

**Both comparisons are now available**, and neither carries a hypothesis.

* (1) ≃ (3), on derived categories: the packaging makes `affineOpensToOpens` a dense subsite of
  `X.Opens`, the site carrying `𝒪_X` itself, so the two Stacks steps (1) ≃ (2) ≃ (3) collapse to
  one, and `AlgebraicGeometry.Scheme.quasicoherentDerivedAffineOpensEquivalence` (in
  `StacksFrontier/AlgebraicGeometry/DerivedQCoh/AffineOpensDerivedComparison.lean`) is
  `D_QCoh(𝒪_X) ≌ D_QCoh(X_{affine, Zar}, 𝒪)`, induced by derived restriction. At the level of
  single modules it is `AlgebraicGeometry.Scheme.affineOpensModuleRestrictionEquivalence` with
  `…isQuasicoherentOnSite_affineOpensModuleRestriction_iff`.
* (3) ≃ (4), the change of topology, is the second conclusion of [Stacks, Tag 07A8], available
  for an arbitrary coarsening as
  `Stacks.Cohomology.CompareTopologies.derivedPullbackEquivalenceImageOfLE` and in the chaotic
  shape as `derivedPullbackEquivalenceImageOfBot`, both in
`StacksFrontier/CategoryTheory/Sites/Cohomology/ChangeOfTopology/CoarseningDerivedEquivalence.lean`.

Instantiating the chaotic case **here** asked for three things, all of them now supplied: the
vanishing of `H^p_Zar(U, F)` for `p > 0`, `U` an affine open and `F` quasi-coherent **on the
affine site**, which is
`AlgebraicGeometry.Scheme.isZero_moduleCohomology_affineZariskiRingedSite`; that the
quasi-coherent modules on the affine site form a weak Serre subcategory, which is
`AlgebraicGeometry.Scheme.isWeakSerreClass_isQuasicoherentOnSite_affineZariski`; and a bridge
between `DerivedCategoryB.derivedCategoryB (isQuasicoherentOnSite R)` and
`qcohCohomologyProperty`, which live over the different ambient categories
`DerivedCategory (SheafOfModules R)` and `DerivedCategory (PresheafOfModules O)`, which is
`AlgebraicGeometry.Scheme.affineChaoticQcohCohomologyEquivalence`.

The family below is produced on the **chaotic** site only: the machinery behind it,
`Stacks.ModulesOnACategory.QuasiCoherentEquivalence.exists_qc_generating_family`, is stated
for modules over a presheaf of rings on a bare category, and the identification of `QC` with
`D_QCoh` that carries it to `qcohCohomologyProperty` needs `J = ⊥`. So the Zariski affine site
carries no such family directly.

## References

* [Stacks Project, Tag 0GZZ](https://stacks.math.columbia.edu/tag/0GZZ)
* [Stacks Project, Tag 0GZX](https://stacks.math.columbia.edu/tag/0GZX)
* [Stacks Project, Tag 0GZR](https://stacks.math.columbia.edu/tag/0GZR)
* [Stacks Project, Tag 0GZ0](https://stacks.math.columbia.edu/tag/0GZ0)
* [Stacks Project, Tag 0GYZ](https://stacks.math.columbia.edu/tag/0GYZ)
* [Stacks Project, Tag 0GYG](https://stacks.math.columbia.edu/tag/0GYG)
* [Stacks Project, Tag 0GYW](https://stacks.math.columbia.edu/tag/0GYW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open CategoryTheory.Pretriangulated.Opposite

universe w u t

namespace AlgebraicGeometry

variable (X : Scheme.{u})

/-! ### The site of affine opens -/

/-- The inclusion of the affine opens of `X` into all opens of `X`, as a functor between the
order categories. The affine opens of a scheme in `Scheme.{u}` form a `Type u`, and the
inclusion order gives them morphisms in `Type u` as well. -/
def Scheme.affineOpensToOpens : X.affineOpens ⥤ X.Opens :=
  Monotone.functor (f := fun U : X.affineOpens ↦ (U : X.Opens)) fun _ _ h ↦ h

/-- The inclusion `Scheme.affineOpensToOpens` sends an affine open to its underlying open. -/
@[simp]
theorem Scheme.affineOpensToOpens_obj (U : X.affineOpens) :
    X.affineOpensToOpens.obj U = (U : X.Opens) := rfl

/-- The inclusion of the affine opens is full: an inclusion of affine opens is an arrow of the
site. This is the point at which the site of [Stacks, Tag 0GZX] differs from Mathlib's
`AlgebraicGeometry.Scheme.AffineZariskiSite`, whose arrows are only the basic opens. -/
instance : X.affineOpensToOpens.Full where
  map_surjective f := ⟨⟨⟨leOfHom f⟩⟩, rfl⟩

/-- The inclusion of the affine opens of `X` into all opens of `X` is faithful. -/
instance : X.affineOpensToOpens.Faithful where
  map_injective _ := Subsingleton.elim _ _

/-- The affine opens are cover-dense in the opens of `X`: they form a basis of the topology,
by `AlgebraicGeometry.Scheme.isBasis_affineOpens`. -/
instance : X.affineOpensToOpens.IsCoverDense (Opens.grothendieckTopology X) where
  is_cover U := by
    intro x hx
    obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open hx U.2
    exact ⟨V, homOfLE hVU, ⟨⟨V, hV⟩, 𝟙 _, homOfLE hVU, rfl⟩, hxV⟩

/-- **The Zariski topology on the affine opens of `X`**, induced from the topology of `X.Opens`
along the cover-dense inclusion. By `AlgebraicGeometry.Scheme.mem_affineOpensTopology` a sieve
covers an affine open exactly when its members cover it pointwise, which is the Zariski topology
of [Stacks, Tag 0GZX]. -/
def Scheme.affineOpensTopology : GrothendieckTopology X.affineOpens :=
  X.affineOpensToOpens.inducedTopology (Opens.grothendieckTopology X)

/-- The inclusion of the affine opens is a dense subsite, for `Scheme.affineOpensTopology` and
the Zariski topology on the opens of `X`. -/
instance : X.affineOpensToOpens.IsDenseSubsite X.affineOpensTopology
    (Opens.grothendieckTopology X) := by
  unfold Scheme.affineOpensTopology; infer_instance

/-- **The covers of the affine site are the Zariski covers.** A sieve `S` on an affine open `U`
of `X` belongs to `Scheme.affineOpensTopology` exactly when every point of `U` lies in some
affine open admitting an arrow of `S` into `U`. -/
theorem Scheme.mem_affineOpensTopology {U : X.affineOpens} {S : Sieve U} :
    S ∈ X.affineOpensTopology U ↔
      ∀ x ∈ (U : X.Opens), ∃ (V : X.affineOpens) (f : V ⟶ U), S.arrows f ∧ x ∈ (V : X.Opens) := by
  rw [Scheme.affineOpensTopology, Functor.mem_inducedTopology_iff_of_isCoverDense]
  refine forall₂_congr fun x _ ↦ ⟨?_, ?_⟩
  · rintro ⟨V, f, ⟨W, g, h, hg, rfl⟩, hxV⟩
    exact ⟨W, g, hg, leOfHom h hxV⟩
  · rintro ⟨W, g, hg, hxW⟩
    exact ⟨(W : X.Opens), homOfLE (leOfHom (X.affineOpensToOpens.map g)), ⟨W, g, 𝟙 _, hg, rfl⟩, hxW⟩

/-! ### The two ringed sites -/

/-- **The ringed site `(X_{affine, Zar}, 𝒪)` of [Stacks, Tag 0GZZ] (3), as a
`RingedSite.{u, u, u}`.** The affine opens of `X` with all inclusions as arrows and the Zariski
topology, carrying the restriction of the structure sheaf of `X`, `U ↦ Γ(X, U)`. -/
def Scheme.affineZariskiRingedSite : RingedSite.{u, u, u} :=
  affineRingedSite X.affineOpensTopology (Opens.grothendieckTopology X) X.affineOpensToOpens
    X.sheaf

/-- **The ringed site `(X_affine, 𝒪)` of [Stacks, Tag 0GZZ] (4), as a `RingedSite.{u, u, u}`.**
The same category and structure sheaf as `Scheme.affineZariskiRingedSite`, read with the chaotic
topology, for which sheaves agree with presheaves. -/
def Scheme.affineChaoticRingedSite : RingedSite.{u, u, u} :=
  X.affineZariskiRingedSite.chaotic

/-- The Grothendieck topology of `Scheme.affineChaoticRingedSite` is the chaotic topology `⊥`. -/
@[simp]
theorem Scheme.affineChaoticRingedSite_J : X.affineChaoticRingedSite.J = ⊥ := rfl

/-! ### Flatness of the restriction homomorphisms -/

/-- **The restriction homomorphisms between affine opens are flat.** For affine opens `V ≤ U` of
a scheme `X` the restriction `Γ(X, U) ⟶ Γ(X, V)` is a flat ring homomorphism: the induced
morphism of schemes `X ∣_ᵤ V ⟶ X ∣_ᵤ U` is an open immersion between affine schemes, hence
flat, and `AlgebraicGeometry.Scheme.Hom.flat_appTop` reads that off on global functions. -/
theorem flat_presheaf_map_of_isAffineOpen {U V : X.Opens} (hU : IsAffineOpen U)
    (hV : IsAffineOpen V) (h : V ≤ U) :
    RingHom.Flat (X.presheaf.map (homOfLE h).op).hom := by
  have : IsAffine (U : Scheme.{u}) := hU
  have : IsAffine (V : Scheme.{u}) := hV
  have hflat := Scheme.Hom.flat_appTop (X.homOfLE h)
  rw [Scheme.homOfLE_appTop] at hflat
  -- The two opens produced by `Scheme.homOfLE_appTop` are `V` and `U` only up to the
  -- simplifications below, so the inequality is transported rather than rewritten.
  have key : ∀ A B : X.Opens, A = V → B = U → ∀ e : A ≤ B,
      RingHom.Flat (X.presheaf.map (homOfLE e).op).hom →
        RingHom.Flat (X.presheaf.map (homOfLE h).op).hom := by
    rintro A B rfl rfl e hf
    exact hf
  exact key _ _ (by simp) (by simp) _ hflat

/-- The restriction homomorphisms of the structure sheaf of the affine site of `X` are flat,
which is the hypothesis of [Stacks, Tag 0GZR]. -/
theorem flat_affineChaoticRingedSite_O_map {U V : X.affineChaoticRingedSite.Cᵒᵖ} (a : V ⟶ U) :
    RingHom.Flat (X.affineChaoticRingedSite.O.obj.map a).hom :=
  flat_presheaf_map_of_isAffineOpen X V.unop.2 U.unop.2 (leOfHom a.unop)

/-- The section rings of the structure sheaf of the affine site are commutative: they are rings
of functions on a scheme, which the structure sheaf delivers as objects of `CommRingCat`. -/
theorem mul_comm_affineChaoticRingedSite_ringSheaf (U : X.affineChaoticRingedSite.Cᵒᵖ)
    (x y : (Stacks.SheafOfModules.Tensor.ringSheaf X.affineChaoticRingedSite.O).obj.obj U) :
    x * y = y * x := by
  let _ : CommRing
      ((Stacks.SheafOfModules.Tensor.ringSheaf X.affineChaoticRingedSite.O).obj.obj U) :=
    (X.affineChaoticRingedSite.O.obj.obj U).commRing
  exact mul_comm x y

/-! ### `QC(X_affine, 𝒪) = D_QCoh(X_affine, 𝒪)` -/

section BaseChange

open Stacks.ModulesOnACategory.QuasiCoherentEquivalence
open Stacks.ModulesOnACategory.QuasiCoherentCohomology
open Stacks.ModulesOnACategory.PullbackQuasiCoherentBaseChange

/-- Derived base-change data on the affine site of `X`: the derived extension-of-scalars functors
along the restriction homomorphisms of the structure sheaf, with their adjunctions to derived
restriction of scalars. Its only input is commutativity of the section rings, so it exists for an
arbitrary scheme and an arbitrary module universe. -/
def affineChaoticBaseChangeData :
    BaseChangeData.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.affineChaoticRingedSite.O).obj :=
  baseChangeDataOfComm (Stacks.SheafOfModules.Tensor.ringSheaf X.affineChaoticRingedSite.O).obj
    (mul_comm_affineChaoticRingedSite_ringSheaf X)

/-- **[Stacks, Tag 0GZZ], the equivalence (4) ≃ (5), as an equality of subcategories.** On the
affine site of `X` read with the chaotic topology, the object property cutting out
`QC(X_affine, 𝒪)` and the one cutting out `D_QCoh(X_affine, 𝒪)` are the same property of
`D(X_affine, 𝒪)`. This is [Stacks, Tag 0GZR] applied to the flat restriction homomorphisms
`AlgebraicGeometry.flat_affineChaoticRingedSite_O_map`.

[Stacks, Tag 0GZZ] (not registered here: this is not the whole statement of the tag): the
equivalence (4) ≃ (5), on the Type u-small affine site of a scheme, as an equality of
subcategories of D(X_affine, 𝒪)
-/
theorem affineChaotic_isQC_eq_hasQuasicoherentCohomology
    (bc : BaseChangeData.{w}
      (Stacks.SheafOfModules.Tensor.ringSheaf X.affineChaoticRingedSite.O).obj) :
    isQCProperty.{w} bc = qcohCohomologyProperty.{w} X.affineChaoticRingedSite :=
  isQC_eq_hasQuasicoherentCohomology.{w} X.affineChaoticRingedSite rfl
    (fun a ↦ flat_affineChaoticRingedSite_O_map X a) bc

/-- **[Stacks, Tag 0GZZ], the equivalence (4) ≃ (5).** For a scheme `X`, the derived category of
modules on the affine site `X_affine` with quasi-coherent cohomology is canonically equivalent to
the category `QC(X_affine, 𝒪)` of quasi-coherent objects of [Stacks, Tag 0GYV].

[Stacks, Tag 0GZZ] (not registered here: this is not the whole statement of the tag): the
equivalence (4) ≃ (5), on the Type u-small affine site of a scheme
-/
def affineChaoticDerivedQuasiCoherentEquivQC
    (bc : BaseChangeData.{w}
      (Stacks.SheafOfModules.Tensor.ringSheaf X.affineChaoticRingedSite.O).obj) :
    (qcohCohomologyProperty.{w} X.affineChaoticRingedSite).FullSubcategory ≌ QC.{w} bc :=
  derivedQuasiCoherentEquivQC.{w} X.affineChaoticRingedSite rfl
    (fun a ↦ flat_affineChaoticRingedSite_O_map X a) bc

/-- The comparison `D_QCoh(X_affine, 𝒪) ≌ QC(X_affine, 𝒪)` is the canonical one: it commutes
with the inclusions of both sides into `D(X_affine, 𝒪)`. -/
def affineChaoticDerivedQuasiCoherentEquivQC_functor_comp_ι
    (bc : BaseChangeData.{w}
      (Stacks.SheafOfModules.Tensor.ringSheaf X.affineChaoticRingedSite.O).obj) :
    (affineChaoticDerivedQuasiCoherentEquivQC.{w} X bc).functor ⋙ QCι.{w} bc ≅
      (qcohCohomologyProperty.{w} X.affineChaoticRingedSite).ι :=
  derivedQuasiCoherentEquivQCFunctorCompι.{w} X.affineChaoticRingedSite rfl
    (fun a ↦ flat_affineChaoticRingedSite_O_map X a) bc

/-- **[Stacks, Tag 0GZZ], triangulatedness of (4) and (5).** Both subcategories are triangulated
subcategories of `D(X_affine, 𝒪)`, by [Stacks, Tag 0GYW], so the comparison is an exact
equivalence of triangulated categories.

[Stacks, Tag 0GZZ] (not registered here: this is not the whole statement of the tag): (4) and (5)
are triangulated, on the Type u-small affine site of a scheme
-/
theorem affineChaotic_qcohCohomologyProperty_isTriangulated :
    ObjectProperty.IsTriangulated
      (qcohCohomologyProperty.{w} X.affineChaoticRingedSite) := by
  rw [← affineChaotic_isQC_eq_hasQuasicoherentCohomology.{w} X
    (affineChaoticBaseChangeData.{w} X)]
  exact isQC_isTriangulated _

/-- **[Stacks, Tag 0GZZ], direct sums in (4).** `D_QCoh(X_affine, 𝒪)` is closed under direct
sums indexed by an arbitrary type: it is the same subcategory of `D(X_affine, 𝒪)` as
`QC(X_affine, 𝒪)`, which is closed under them by [Stacks, Tag 0GYW]. In particular the
subcategory has the direct sums the generating family of [Stacks, Tag 0GYG] is stated with.

[Stacks, Tag 0GZZ] (not registered here: this is not the whole statement of the tag): (4) is
closed under arbitrary direct sums, on the Type u-small affine site of a scheme
-/
instance affineChaotic_qcohCohomologyProperty_isClosedUnderColimitsOfShape (J : Type t) :
    ObjectProperty.IsClosedUnderColimitsOfShape
      (qcohCohomologyProperty.{w} X.affineChaoticRingedSite) (Discrete J) := by
  rw [← affineChaotic_isQC_eq_hasQuasicoherentCohomology.{w} X
    (affineChaoticBaseChangeData.{w} X)]
  exact isQC_isClosedUnderColimitsOfShape _ J

/-! ### The generating family of [Stacks, Tag 0GYG], indexed by a `Type u` -/

/-- **`QC(X_affine, 𝒪) = D_QCoh(X_affine, 𝒪)` has a generating family in the sense of
[Stacks, Tag 0GYG], indexed by a `Type u`.** For an arbitrary scheme `X : Scheme.{u}` there is a
family `E : ι → QC(X_affine, 𝒪)` with `ι : Type u` such that every nonzero object receives a
nonzero morphism from some `E i`, and every morphism from some `E i` into a countable direct sum
`∐ K` factors as a direct sum of morphisms `E (j n) ⟶ K n` preceded by a morphism
`E i ⟶ ∐ₙ E (j n)`.

The members of `E` are **not** claimed to be compact, and no hypothesis is carried: not
quasi-compactness, not quasi-separatedness, and no compact generation. The content is
[Stacks, Tag 0GYZ], available as
`Stacks.ModulesOnACategory.QuasiCoherentEquivalence.exists_qc_generating_family`, whose index
universe is `max u v r w` for a site with objects in `Type u`, morphisms in `Type v`, section
rings in `Type r` and modules in `Type w`. What this statement adds is that on the affine site of
a scheme packaged as a `RingedSite.{u, u, u}` all four of those are `u`, so the index type is a
`Type u` — the universe in which the direct sums of `D_QCoh(𝒪_X)` are indexed. -/
theorem exists_generating_family_affineChaoticDerivedQuasiCoherent :
    ∃ (ι : Type u) (E : ι → QC.{u} (affineChaoticBaseChangeData.{u} X)),
      (∀ K : QC.{u} (affineChaoticBaseChangeData.{u} X), ¬ IsZero K →
          ∃ (i : ι) (f : E i ⟶ K), f ≠ 0) ∧
        ∀ (K : ℕ → QC.{u} (affineChaoticBaseChangeData.{u} X)) (i : ι) (α : E i ⟶ ∐ K),
          ∃ (j : ℕ → ι) (β : ∀ n, E (j n) ⟶ K n) (γ : E i ⟶ ∐ fun n ↦ E (j n)),
            α = γ ≫ Limits.Sigma.map β :=
  exists_qc_generating_family.{u} (affineChaoticBaseChangeData.{u} X)
    (mul_comm_affineChaoticRingedSite_ringSheaf X)

/-- **`D_QCoh(X_affine, 𝒪)` has a generating family in the sense of [Stacks, Tag 0GYG], indexed
by a `Type u`.** The same statement as
`AlgebraicGeometry.exists_generating_family_affineChaoticDerivedQuasiCoherent`, read on the
subcategory of `D(X_affine, 𝒪)` cut out by quasi-coherence of the cohomology sheaves rather than
on the cartesian objects.

The two subcategories are equal, by
`AlgebraicGeometry.affineChaotic_isQC_eq_hasQuasicoherentCohomology`, so the comparison
`AlgebraicGeometry.affineChaoticDerivedQuasiCoherentEquivQC` is an equivalence whose functors are
inclusions of object properties; `CategoryTheory.exists_generating_family_of_equivalence` carries
the family and both of its conditions across it. -/
theorem exists_generating_family_qcohCohomology_affineChaotic :
    ∃ (ι : Type u)
      (E : ι → (qcohCohomologyProperty.{u} X.affineChaoticRingedSite).FullSubcategory),
      (∀ K : (qcohCohomologyProperty.{u} X.affineChaoticRingedSite).FullSubcategory,
          ¬ IsZero K → ∃ (i : ι) (f : E i ⟶ K), f ≠ 0) ∧
        ∀ (K : ℕ → (qcohCohomologyProperty.{u} X.affineChaoticRingedSite).FullSubcategory)
          (i : ι) (α : E i ⟶ ∐ K),
          ∃ (k : ℕ → ι) (β : ∀ n, E (k n) ⟶ K n) (γ : E i ⟶ ∐ fun n ↦ E (k n)),
            α = γ ≫ Limits.Sigma.map β := by
  obtain ⟨ι, E, hE, hE'⟩ := exists_generating_family_affineChaoticDerivedQuasiCoherent X
  set e := (affineChaoticDerivedQuasiCoherentEquivQC.{u} X
    (affineChaoticBaseChangeData.{u} X)).symm with he
  have : e.functor.PreservesZeroMorphisms := ⟨fun _ _ ↦ rfl⟩
  have : e.inverse.PreservesZeroMorphisms := ⟨fun _ _ ↦ rfl⟩
  obtain ⟨h1, h2⟩ := CategoryTheory.exists_generating_family_of_equivalence e E hE hE'
  exact ⟨ι, _, h1, h2⟩

/-! ### [Stacks, Tag 0GZ0] at these universes -/

/-- **[Stacks, Tag 0GZ0] part (2) on `D_QCoh(X_affine, 𝒪)`, with morphisms in `Type u`.** Every
contravariant cohomological functor on `QC(X_affine, 𝒪)` which transforms direct sums into
products is representable.

[Stacks, Tag 0GZ0] (not registered here: this is not the whole statement of the tag): part (2) on
QC(X_affine, 𝒪) of an arbitrary scheme, at the Type u-small packaging of the affine site
-/
theorem exists_iso_preadditiveYoneda_affineChaoticDerivedQuasiCoherent
    (H : (QC.{u} (affineChaoticBaseChangeData.{u} X))ᵒᵖ ⥤ AddCommGrpCat.{u}) [H.IsHomological]
    [∀ J : Type u, PreservesLimitsOfShape (Discrete J) H] :
    ∃ K : QC.{u} (affineChaoticBaseChangeData.{u} X),
      Nonempty (preadditiveYoneda.obj K ≅ H) :=
  exists_iso_preadditiveYoneda_of_isHomological.{u} (affineChaoticBaseChangeData.{u} X)
    (mul_comm_affineChaoticRingedSite_ringSheaf X) H

/-- **[Stacks, Tag 0GZ0] part (3) on `D_QCoh(X_affine, 𝒪)`, with morphisms in `Type u`.** An
exact functor `F : QC(X_affine, 𝒪) ⥤ D'` of triangulated categories which transforms direct sums
into direct sums has a right adjoint `G`, which is again exact.

Compared with
`AlgebraicGeometry.exists_isTriangulated_rightAdjoint_smallAffineChaoticDerivedQuasiCoherent`,
which is the same statement on the packaging coming from the big Zariski site, the morphisms of
`D'` here live in `Type u` rather than in `Type (max (u + 1) w)`, and the direct sums are indexed
by `Type u`. That is the universe discipline of `D_QCoh(𝒪_X)`.

[Stacks, Tag 0GZ0] (not registered here: this is not the whole statement of the tag): part (3) on
QC(X_affine, 𝒪) of an arbitrary scheme, at the Type u-small packaging of the affine site
-/
theorem exists_isTriangulated_rightAdjoint_affineChaoticDerivedQuasiCoherent
    {D' : Type*} [Category.{u} D'] [HasZeroObject D'] [Preadditive D'] [HasShift D' ℤ]
    [∀ n : ℤ, (shiftFunctor D' n).Additive] [Pretriangulated D']
    (F : QC.{u} (affineChaoticBaseChangeData.{u} X) ⥤ D') [F.CommShift ℤ] [F.IsTriangulated]
    [∀ α : Type u, PreservesColimitsOfShape (Discrete α) F] :
    ∃ (G : D' ⥤ QC.{u} (affineChaoticBaseChangeData.{u} X)) (adj : F ⊣ G) (_ : G.CommShift ℤ),
      adj.IsTriangulated :=
  exists_isTriangulated_rightAdjoint_of_preservesCoproducts.{u} (affineChaoticBaseChangeData.{u} X)
    (mul_comm_affineChaoticRingedSite_ringSheaf X) F

end BaseChange

end AlgebraicGeometry

end
