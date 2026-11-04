module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import StacksFrontier.AlgebraicGeometry.AffineCohomologyVanishing.Basic
public import StacksFrontier.AlgebraicGeometry.Cohomology.Cech.AffineVanishing
public import StacksFrontier.AlgebraicGeometry.Duality.AffineVanishing.UpperBounds
public import StacksFrontier.CategoryTheory.Abelian.RightDerivedPostcompose
public import StacksFrontier.Homology.DerivedIndexing.Basic
public import StacksFrontier.Homology.Injectives.DerivedCategory.DerivedLimit
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.ConnectivityOnABasis

/-!
# Upper cohomological bounds for the derived direct image along an affine morphism

Let `f : X ⟶ Y` be an affine morphism of schemes and let `E` be an object of `D(𝒪_X)` whose
cohomology sheaves are quasi-coherent. If `E` lives in degrees `≤ b`, then so does `Rf_*E`. This
is [Stacks, Tag 08D5] part (2) in the case of an affine morphism, where the integer `N` of the
source may be taken to be `1`.

The argument is the one the source gives, with no loss. The cohomology sheaf `H^i(Rf_*E)` is the
sheaf associated to the presheaf `V ↦ H^i(f⁻¹V, E)` ([Stacks, Tag 0D5X], itself [Stacks, Tag 0D5W]
followed by [Stacks, Tag 0BKJ]), so it vanishes as soon as `H^i(f⁻¹V, E)` vanishes for `V` in a
basis of the topology of `Y`. Take that basis to be the affine opens. For `V` affine the inverse
image `f⁻¹V` is affine because `f` is, hence `H^p(f⁻¹V, ℱ) = 0` for `p > 0` and `ℱ` quasi-coherent
by Serre vanishing ([Stacks, Tag 01XB]); so [Stacks, Tag 08D4] part (3) applies to the functor
`Γ(f⁻¹V, -)` with `N = 1` and gives that `RΓ(f⁻¹V, E)` lives in degrees `≤ b + 1 - 1 = b`.

## Main results

* `AlgebraicGeometry.isZero_rightDerivedPlus_preimageSections_of_isAffineOpen` — Serre vanishing
  in the form [Stacks, Tag 08D4] part (3) consumes it: the higher right derived functors of
  `Γ(f⁻¹V, -) : Mod(𝒪_X) ⥤ Mod(Γ(V, 𝒪_Y))` vanish on quasi-coherent modules when `f⁻¹V` is
  affine.
* `AlgebraicGeometry.isLE_derivedPreimageSections_obj` — `RΓ(f⁻¹V, E)` lives in degrees `≤ b`
  when `E` does and `f⁻¹V` is affine.
* `AlgebraicGeometry.isLE_derivedPushforward_obj_of_isAffineHom` — **[Stacks, Tag 08D5] part (2)
  for an affine morphism, with `N = 1`:** `(Rf_*E).IsLE b` when `E.IsLE b`.
* `AlgebraicGeometry.isIso_homologyFunctor_map_derivedPushforward_truncGEπ` — the companion
  truncation comparison: `H^i(Rf_*E) ⟶ H^i(Rf_*(τ_{≥ b}E))` is invertible for `i ≥ b`.

## Implementation notes

**No `@[stacks 08D5]` attribute is placed.** Tag 08D5 has three parts and its hypothesis is that
`f` be quasi-compact and quasi-separated, with an integer `N = N(X, Y, f)` produced by
[Stacks, Tag 01XJ]; part (1) asserts that `Rf_*` carries `D_QCoh(𝒪_X)` into `D_QCoh(𝒪_Y)` and
part (3) that the bound of part (2) survives an arbitrary base change. What is proved here is
part (2) for an *affine* morphism, where `N = 1`. That is the case the comparison squares of
[Stacks, Tag 08D7] and [Stacks, Tag 0DJK] need, and it is a strictly weaker statement than the
tag; see `StacksFrontier/AlgebraicGeometry/QuasiCoherent/Coherator/AffineDerivedPushforward.lean`.
Part (2) for a quasi-compact quasi-separated morphism with quasi-compact target is
`AlgebraicGeometry.exists_isLE_derivedPushforward_obj` in
`StacksFrontier/AlgebraicGeometry/QuasiCoherent/Coherator/QcqsPushforwardBounds.lean`, which is this
file's argument with the single affine input replaced by the uniform bound over a basis; part (3)
is still missing, so the tag's covering set remains incomplete.

**Where the general acyclicity statement went.** Joining [Stacks, Tag 08D4] part (3) to
[Stacks, Tag 0D5W] looks as though it needs "a complex of sheaves of modules whose complexes of
sections over every open are acyclic is acyclic". It does not: the sheafification half of that
statement is already carried, in exactly the form required, by
`Stacks.Cohomology.UnboundedHigherDirectImage.isZero_homologyDerivedPushforward_of_isBasis`
(part of [Stacks, Tag 0D66]), which identifies `H^i(Rf_*E)` with the sheafification of
`V ↦ H^i(f⁻¹V, E)` and kills it from vanishing on a basis. Nothing is reproved here.

**Three instances are supplied positionally.**
`AlgebraicGeometry.isLE_rightDerivedFunctor_obj_of_isZero_rightDerivedPlus` is
stated with source category `SheafOfModules X.ringCatSheaf`, while `Γ(f⁻¹V, -)` and its derived
functor are stated with source `SheafOfModules (structureSheafRing
X.toRingedSpace)`. The two are definitionally equal, but `CategoryTheory.Functor.Additive` and
`CategoryTheory.Functor.IsRightDerivedFunctor` mention the `Preadditive` and `HasDerivedCategory`
instances of the source, and instance search does not cross the two spellings; so additivity,
preservation of countable products, and the derived-functor structure are handed to that theorem
as explicit positional arguments, where the defeq check does succeed.

**No model of the derived categories is chosen that was not already chosen.** Every input —
[Stacks, Tag 0D5W], [Stacks, Tag 0D5X], [Stacks, Tag 0D66] and
`AlgebraicGeometry.isLE_rightDerivedFunctor_obj_of_isZero_rightDerivedPlus` — is stated at
`CategoryTheory.HasDerivedCategory.standard`, so the statements below are too, and no re-binding
of a convergence chain at a free `HasDerivedCategory` binder is needed to join them.

## References

* [Stacks Project, Tag 08D5](https://stacks.math.columbia.edu/tag/08D5)
* [Stacks Project, Tag 08D4](https://stacks.math.columbia.edu/tag/08D4)
* [Stacks Project, Tag 0D5W](https://stacks.math.columbia.edu/tag/0D5W)
* [Stacks Project, Tag 0D5X](https://stacks.math.columbia.edu/tag/0D5X)
* [Stacks Project, Tag 0D66](https://stacks.math.columbia.edu/tag/0D66)
* [Stacks Project, Tag 01XB](https://stacks.math.columbia.edu/tag/01XB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
open TopologicalSpace AlgebraicGeometry
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPushforward derivedPushforwardUnit)
open Stacks.Cohomology.DerivedSectionsLeray
  (derivedPreimageSections derivedPreimageSectionsUnit preimageSections)

namespace AlgebraicGeometry

universe u

attribute [local instance] HasDerivedCategory.standard
attribute [local instance]
  Stacks.Cohomology.UnboundedHigherDirectImage.isGrothendieckAbelian_moduleSheaves

variable {X Y : Scheme.{u}}

/-! ### Countable products of sections -/

/-- **Restriction of scalars preserves countable products.** The underlying abelian group of a
product of modules is the product of the underlying groups, and restriction of scalars does not
change it. Stated for a map of not necessarily commutative rings, which is the generality the
structure sheaf of a ringed space is read in; for a map of commutative rings restriction of
scalars is a right adjoint and preservation of all limits is already available. -/
public instance preservesLimitsOfShape_discrete_nat_restrictScalars {R S : Type u} [Ring R]
    [Ring S] (φ : R →+* S) :
    PreservesLimitsOfShape (Discrete ℕ) (ModuleCat.restrictScalars.{u} φ) :=
  ⟨fun {_} ↦ inferInstance⟩

/-- **Sections over the inverse image of an open preserve countable products.** Sections of a
sheaf of modules over a fixed open are a limit, and the restriction of scalars that turns them
into a module over the functions on the image open preserves countable products. This is the
hypothesis under which a right derived functor carries derived limits of `ℕᵒᵖ`-towers to derived
limits, [Stacks, Tag 08U1], and hence the hypothesis of [Stacks, Tag 08D4]. -/
public instance preservesLimitsOfShape_discrete_nat_preimageSections (f : X ⟶ Y) (V : Y.Opens) :
    PreservesLimitsOfShape (Discrete ℕ) (preimageSections f.toLRSHom.toShHom V) :=
  @comp_preservesLimitsOfShape _ _ _ _ _ _ _ _ _ _
    (SheafOfModules.evaluationPreservesLimitsOfShape _ _ _)
    (preservesLimitsOfShape_discrete_nat_restrictScalars
      ((structureSheafHom f.toLRSHom.toShHom).hom.app (op V)).hom)

/-! ### Serre vanishing for sections over an affine inverse image -/

/-- **Serre vanishing for `Γ(f⁻¹V, -)`.** If the inverse image `f⁻¹V` of an open `V ⊆ Y` is an
affine open of `X`, then the higher right derived functors of
`Γ(f⁻¹V, -) : Mod(𝒪_X) ⥤ Mod(Γ(V, 𝒪_Y))` vanish on every quasi-coherent `𝒪_X`-module.

This is [Stacks, Tag 01XB] read in the right target. The cohomology `H^p(f⁻¹V, ℱ)` as an abelian
group vanishes by Serre vanishing on the affine open `f⁻¹V`; composing `Γ(f⁻¹V, -)` with the
forgetful functor to abelian groups — which is exact, hence commutes with right derived functors
— gives exactly that group, and a module with zero underlying group is zero. The passage between
the `ℕ`-indexed and `ℤ`-indexed derived functors is
`Stacks.DerivedIndexing.isZero_rightDerivedPlus_obj_iff`.

Note that restriction of scalars along `f^♯` is invisible to the statement: it is the identity on
underlying groups, so no separate transport along it is needed. -/
public theorem isZero_rightDerivedPlus_preimageSections_of_isAffineOpen (f : X ⟶ Y) (V : Y.Opens)
    (hV : IsAffineOpen (f ⁻¹ᵁ V)) (M : SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
    (hM : M.IsQuasicoherent) (p : ℤ) (hp : 0 < p) :
    IsZero (((preimageSections f.toLRSHom.toShHom V).rightDerivedPlus p).obj M) := by
  have hM' : (M : X.Modules).IsQuasicoherent := hM
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, p = (n : ℤ) := ⟨p.toNat, (Int.toNat_of_nonneg hp.le).symm⟩
  refine (Stacks.DerivedIndexing.isZero_rightDerivedPlus_obj_iff
    (preimageSections f.toLRSHom.toShHom V) (rfl : ((n : ℕ) : ℤ) = ((n : ℕ) : ℤ)) M).2 ?_
  have hAb : IsZero (((preimageSections f.toLRSHom.toShHom V ⋙
      forget₂ (ModuleCat.{u} ((structureSheafRing Y.toRingedSpace).obj.obj (op V)))
        AddCommGrpCat.{u}).rightDerived n).obj M) :=
    @Stacks.Cohomology.Cech.isZero_hgroup_of_isAffineOpen X M hM' (f ⁻¹ᵁ V) hV n
      (by exact_mod_cast hp)
  exact ModuleCat.isZero_iff_subsingleton.mpr (AddCommGrpCat.subsingleton_of_isZero
    (hAb.of_iso (((preimageSections f.toLRSHom.toShHom V).rightDerivedCompIso
      (forget₂ (ModuleCat.{u} ((structureSheafRing Y.toRingedSpace).obj.obj (op V)))
        AddCommGrpCat.{u}) n).app M).symm))

/-! ### The bound over an affine inverse image, and on the derived direct image -/

/-- **[Stacks, Tag 08D4] part (3) at the functor `Γ(f⁻¹V, -)`, with `N = 1`.** Let `V ⊆ Y` be an
open whose inverse image is an affine open of `X`, and let `E` be an object of `D(𝒪_X)` with
quasi-coherent cohomology sheaves living in degrees `≤ b`. Then the hypercohomology
`RΓ(f⁻¹V, E)` lives in degrees `≤ b`.

`AlgebraicGeometry.isLE_rightDerivedFunctor_obj_of_isZero_rightDerivedPlus` supplies the bound
`b + N - 1` from vanishing of the higher right derived functors in degrees `≥ N`; here `N = 1` by
`isZero_rightDerivedPlus_preimageSections_of_isAffineOpen`, so the bound is `b` itself. Sections
over an inverse image preserve countable products, which is that theorem's other hypothesis. -/
public theorem isLE_derivedPreimageSections_obj (f : X ⟶ Y) (V : Y.Opens)
    (hV : IsAffineOpen (f ⁻¹ᵁ V))
    (E : DerivedCategory (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)))
    (hcoh : ∀ i : ℤ, ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) i).obj E).IsQuasicoherent)
    (b : ℤ) (hE : E.IsLE b) :
    ((derivedPreimageSections f.toLRSHom.toShHom V).obj E).IsLE b := by
  have hirdf : (derivedPreimageSections f.toLRSHom.toShHom V).IsRightDerivedFunctor
      (derivedPreimageSectionsUnit f.toLRSHom.toShHom V)
      (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
        (ComplexShape.up ℤ)) := inferInstance
  have h := @isLE_rightDerivedFunctor_obj_of_isZero_rightDerivedPlus X _ _ _ _ _ _
    (preimageSections f.toLRSHom.toShHom V)
    (Stacks.Cohomology.DerivedSectionsLeray.preimageSections_additive _ _)
    (preservesLimitsOfShape_discrete_nat_preimageSections f V)
    (derivedPreimageSections f.toLRSHom.toShHom V)
    (derivedPreimageSectionsUnit f.toLRSHom.toShHom V) hirdf 1
    (fun M hM p hp ↦ isZero_rightDerivedPlus_preimageSections_of_isAffineOpen f V hV M hM p
      (by exact_mod_cast hp)) E hcoh b hE
  simpa using h

/-- **[Stacks, Tag 08D5] part (2) for an affine morphism, with `N = 1`.** Let `f : X ⟶ Y` be an
affine morphism of schemes and let `E` be an object of `D(𝒪_X)` whose cohomology sheaves are
quasi-coherent. If `E` lives in degrees `≤ b`, then `Rf_*E` lives in degrees `≤ b`.

The `i`-th cohomology sheaf of `Rf_*E` is the sheafification of the presheaf `V ↦ H^i(f⁻¹V, E)`,
so it is enough to make that presheaf vanish on a basis of the topology of `Y`
(`Stacks.Cohomology.UnboundedHigherDirectImage.isZero_homologyDerivedPushforward_of_isBasis`).
Take the basis of affine opens: the inverse image of an affine open under an affine morphism is
affine, so `isLE_derivedPreimageSections_obj` applies and `H^i(f⁻¹V, E) = 0` for `i > b`.

The bound is the one the source gives for `N = 1`, and it is sharp: no degree is lost, because
pushforward along an affine morphism has no higher cohomology on quasi-coherent modules. -/
public theorem isLE_derivedPushforward_obj_of_isAffineHom (f : X ⟶ Y) [IsAffineHom f]
    (E : DerivedCategory (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)))
    (hcoh : ∀ i : ℤ, ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) i).obj E).IsQuasicoherent)
    (b : ℤ) (hE : E.IsLE b) :
    ((derivedPushforward f.toLRSHom.toShHom).obj E).IsLE b := by
  rw [DerivedCategory.isLE_iff]
  intro i hi
  refine Stacks.Cohomology.UnboundedHigherDirectImage.isZero_homologyDerivedPushforward_of_isBasis
    f.toLRSHom.toShHom Y.isBasis_affineOpens E i fun V hV ↦ ?_
  have := isLE_derivedPreimageSections_obj f V (hV.preimage f) E hcoh b hE
  exact DerivedCategory.isZero_of_isLE _ b i hi

/-- **The derived direct image along an affine morphism does not see a truncation from below in
high degrees.** For `f` affine and `E` an object of `D(𝒪_X)` with quasi-coherent cohomology
sheaves, the canonical map `H^i(Rf_*E) ⟶ H^i(Rf_*(τ_{≥ b}E))` is an isomorphism for every
`i ≥ b`.

This is [Stacks, Tag 08D4] part (2) read at `Rf_*` with `N = 1`, so that the cut sits at
`b - N + 1 = b`; it is the step the proof of [Stacks, Tag 0G9N] uses to replace an unbounded
complex by a bounded below one, and it is deduced from
`isLE_derivedPushforward_obj_of_isAffineHom` exactly as the source deduces it from part (3).

The canonical truncation triangle `τ_{≤ b-1}E ⟶ E ⟶ τ_{≥ b}E` goes to a distinguished triangle
under `Rf_*`, which is exact because it is a right derived functor of an additive functor out of
a Grothendieck abelian category. Its first vertex has `Rf_*`-image in degrees `≤ b - 1`, so `H^i`
and `H^{i+1}` vanish there for `i ≥ b`, and the long exact homology sequence makes the second map
invertible on `H^i`. -/
public theorem isIso_homologyFunctor_map_derivedPushforward_truncGEπ (f : X ⟶ Y) [IsAffineHom f]
    (E : DerivedCategory (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)))
    (hcoh : ∀ i : ℤ, ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) i).obj E).IsQuasicoherent)
    (b i : ℤ) (hi : b ≤ i) :
    IsIso ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (structureSheafRing Y.toRingedSpace)) i).map
      ((derivedPushforward f.toLRSHom.toShHom).map
        ((DerivedCategory.TStructure.t.truncGEπ b).app E))) := by
  have hP := containsZero_isQuasicoherent X
  have _ := SheafOfModules.isGrothendieckAbelianU.{u, u, u} (structureSheafRing X.toRingedSpace)
  let _ := Functor.IsRightDerivedFunctor.commShift (derivedPushforward f.toLRSHom.toShHom)
    (derivedPushforwardUnit f.toLRSHom.toShHom)
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
      (ComplexShape.up ℤ)) ℤ
  have _ : (derivedPushforward f.toLRSHom.toShHom).IsTriangulated :=
    Stacks.Injectives.rightDerivedFunctor_isTriangulated
      (modulePushforward f.toLRSHom.toShHom) _ (derivedPushforwardUnit f.toLRSHom.toShHom)
  let T := (derivedPushforward f.toLRSHom.toShHom).mapTriangle.obj
    ((DerivedCategory.TStructure.t.triangleLEGE (b - 1) b (by omega)).obj E)
  have hT : T ∈ distTriang
      (DerivedCategory (SheafOfModules.{u} (structureSheafRing Y.toRingedSpace))) :=
    (derivedPushforward f.toLRSHom.toShHom).map_distinguished _
      (DerivedCategory.TStructure.t.triangleLEGE_distinguished (b - 1) b (by omega) E)
  have hl : T.obj₁.IsLE (b - 1) :=
    isLE_derivedPushforward_obj_of_isAffineHom f _
      (@Stacks.SmallDerivedCategory.prop_homologyFunctor_truncLE_obj _ _ _ _
        (SheafOfModules.isQuasicoherent (structureSheafRing X.toRingedSpace)) _ hP E hcoh (b - 1))
      (b - 1)
      (DerivedCategory.TStructure.t.isLE_truncLE_obj E (b - 1) (b - 1) le_rfl)
  have hz := T.obj₁.isZero_of_isLE (b - 1) i (by omega)
  have hz' := T.obj₁.isZero_of_isLE (b - 1) (i + 1) (by omega)
  have : Mono ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (structureSheafRing Y.toRingedSpace)) i).map T.mor₂) :=
    ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u}
        (structureSheafRing Y.toRingedSpace)) 0).homologySequence_mono_shift_map_mor₂_iff
      T hT i).2 (hz.eq_of_src _ _)
  have : Epi ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (structureSheafRing Y.toRingedSpace)) i).map T.mor₂) :=
    ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u}
        (structureSheafRing Y.toRingedSpace)) 0).homologySequence_epi_shift_map_mor₂_iff
      T hT i (i + 1) rfl).2 (hz'.eq_of_tgt _ _)
  exact isIso_of_mono_of_epi ((DerivedCategory.homologyFunctor
    (SheafOfModules.{u} (structureSheafRing Y.toRingedSpace)) i).map T.mor₂)

end AlgebraicGeometry

end
