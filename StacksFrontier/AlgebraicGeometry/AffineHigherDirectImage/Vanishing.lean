module

public import Mathlib.Algebra.Category.Grp.Zero
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.Topology.Sheaves.Abelian
public import Mathlib.Topology.Sheaves.Sheafify
public import Mathlib.Topology.Sheaves.Stalks
public import StacksFrontier.Topology.Sheaves.Cohomology.HigherDirectImage.SheafifiedCohomologyPresheaf
public import StacksFrontier.AlgebraicGeometry.AffineCohomologyGlue.AffineOpenVanishing
public import StacksFrontier.AlgebraicGeometry.AffineCohomologyVanishing.Basic
public import StacksFrontier.AlgebraicGeometry.CohomologyAffineReduction.Basic
public import StacksFrontier.Homology.DerivedIndexing.Basic
public import StacksFrontier.AlgebraicGeometry.SheafOfModulesEnoughInjectives

/-!
# Higher direct images along an affine morphism vanish

Let `f : X ⟶ S` be an affine morphism of schemes and `F` a quasi-coherent `𝒪_X`-module. Then
`R ⁱ f_* F = 0` for every `i > 0`. This is [Stacks, Tag 01XC].

The proof is the one in the source, and both of its halves are available.

* [Stacks, Tag 01E4] (`Stacks.Cohomology.HigherDirectImagePresheaf`) presents `R ⁿ f_* F` as the
  sheafification of the presheaf `V ↦ H ⁿ(f⁻¹(V), F)` on the target, with
  `higherDirectImage_iso_sheafify_preimageCohomology` the natural isomorphism and
  `preimageCohomologyPresheaf_evaluation_iso` the identification of its values.
* [Stacks, Tag 01XB] (`Stacks.Cohomology.AffineOpen.isZero_hgroup_of_isAffineOpen`) kills
  `H ⁿ(U, F)` for `n > 0` and `U` an affine open of `X`.

Since `f` is affine, `f⁻¹(V)` is an affine open of `X` whenever `V` is an affine open of `S`, so
the presheaf being sheafified vanishes on the affine opens of `S`; those form a basis, so all of
its stalks vanish, so its sheafification vanishes.

## Main results

* `Stacks.AffineHigherDirectImage.isZero_rightDerivedPlus_pushforward`: **[Stacks, Tag 01XC]**,
  in the `ℤ`-indexed spelling `Functor.rightDerivedPlus` of the higher direct images.
* `Stacks.AffineHigherDirectImage.isZero_rightDerived_pushforward`: the same in Mathlib's
  `ℕ`-indexed spelling `Functor.rightDerived`, which is the form [Stacks, Tag 01F4] part (1)
  consumes.
* `Stacks.AffineHigherDirectImage.rightAcyclic_pushforward`: therefore a quasi-coherent module is
  right acyclic for the pushforward along an affine morphism.
* `Stacks.AffineHigherDirectImage.isZero_rightDerivedPlus_pushforward_of_isZero_hgroup_preimage`:
  the above with the affineness removed — `R ⁿ f_* F` vanishes as soon as `H ⁿ(f⁻¹(V), F)` does
  for every `V` in some basis of the opens of the target.
* `Stacks.AffineHigherDirectImage.isZero_sheafification_of_isZero_on_basis`: the input of the
  above with the geometry removed — a presheaf of abelian groups whose sections over the members
  of a basis vanish has zero sheafification.

No stacks attribute is attached here: the covering set is reported rather than written.

## Implementation notes

The statement is about `AlgebraicGeometry.Scheme.Modules.pushforward`, and the whole of
[Stacks, Tag 01E4] is about `RingedSpaceModuleAdjunction.modulePushforward` of the underlying
morphism of ringed spaces. The two are the *same functor*, by
`Stacks.SchemeCohomology.modulePushforward_hom`, so the transport costs nothing and no comparison
isomorphism appears. The same `rfl` makes `Hfunctor (structureSheafRing (ringedSpace X))` be
`Hfunctor X.ringCatSheaf`, which is what lets [Stacks, Tag 01XB] be applied to a value of the
cohomology presheaf of [Stacks, Tag 01E4].

`Stacks.Cohomology.HigherDirectImagePresheaf.higherDirectImage_iso_sheafify_preimageCohomology`
lands in `PresheafOfModules.sheafification`, i.e. in sheaves of `𝒪_S`-modules, whereas the
vanishing criterion through stalks is about sheaves of abelian groups. The two are connected by
`PresheafOfModules.sheafificationCompToSheaf`, which is `Iso.refl`, and the descent from "the
underlying abelian sheaf is zero" to "the module sheaf is zero" is by reflection of isomorphisms
along `SheafOfModules.toSheaf`.

`AlgebraicGeometry.Scheme.ringCatSheaf` and `TopCat.Sheaf` are `def`s rather than abbreviations,
and `TopCat.Sheaf` carries its own *derived* `Category` instance, distinct as a term from the
`ObjectProperty.FullSubcategory.category` instance that `CategoryTheory.Sheaf` gets. So a goal
`IsZero G` for a `G : CategoryTheory.Sheaf (Opens.grothendieckTopology T) _` cannot be rewritten
with `TopCat.Sheaf.isZero_iff_stalkFunctor_obj_isZero`: the two sides are the same type with two
syntactically different instances, and `rw` fails to match. `isZero_presheaf_of_isZero_stalks`
exists to cross that boundary once, in a position where the sheaf is a *parameter* and so really
carries the `TopCat.Sheaf` spelling.

The three `Functor.Additive` instances of [Stacks, Tag 01E4] are `local` there, so they are
re-declared here.

## References

* [Stacks Project, Tag 01E4](https://stacks.math.columbia.edu/tag/01E4)
* [Stacks Project, Tag 01XB](https://stacks.math.columbia.edu/tag/01XB)
* [Stacks Project, Tag 01XC](https://stacks.math.columbia.edu/tag/01XC)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open AlgebraicGeometry
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.HigherDirectImagePresheaf
open scoped ZeroObject

universe u

namespace Stacks.AffineHigherDirectImage

/-! ### A presheaf vanishing on a basis has zero sheafification -/

section Sheafification

/-- **A sheaf of abelian groups on a space with vanishing stalks has zero underlying presheaf.**
This is `CategoryTheory.Sheaf.isZero_iff_stalkFunctor_obj_isZero` pushed through
`TopCat.Sheaf.forget`; it is stated with the sheaf as a parameter precisely so that the
`TopCat.Sheaf` spelling, and with it the `Category` instance the criterion is stated for, is the
one in the goal. -/
theorem isZero_presheaf_of_isZero_stalks {T : TopCat.{u}}
    (G : TopCat.Sheaf AddCommGrpCat.{u} T)
    (hG : ∀ x : T, IsZero (G.presheaf.stalk x)) : IsZero G.presheaf :=
  Functor.map_isZero (TopCat.Sheaf.forget AddCommGrpCat.{u} T)
    ((TopCat.Sheaf.isZero_iff_stalkFunctor_obj_isZero G).mpr hG)

/-- **A presheaf of abelian groups whose sections over the members of a basis vanish has zero
sheafification.** All its stalks vanish by
`Stacks.Cohomology.Affine.isZero_stalk_of_isZero_on_basis`, hence so do those of the
sheafification (`TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso`), hence the
sheafification is zero. -/
theorem isZero_sheafification_of_isZero_on_basis {T : TopCat.{u}} {B : Set (Opens T)}
    (hB : Opens.IsBasis B) (P : TopCat.Presheaf AddCommGrpCat.{u} T)
    (hP : ∀ U ∈ B, IsZero (P.obj (op U))) :
    IsZero ((presheafToSheaf (Opens.grothendieckTopology T) AddCommGrpCat.{u}).obj P) := by
  set J := Opens.grothendieckTopology (T : Type u) with hJ
  set F := (presheafToSheaf J AddCommGrpCat.{u}).obj P with hF
  have hStalkSheafify (x : T) : IsZero (TopCat.Presheaf.stalk F.1 x) := by
    refine (Stacks.Cohomology.Affine.isZero_stalk_of_isZero_on_basis hB P hP x).of_iso ?_
    have hUnit : IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
        ((sheafificationAdjunction J AddCommGrpCat.{u}).unit.app P)) :=
      TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso x AddCommGrpCat.{u} P
    exact (asIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
      ((sheafificationAdjunction J AddCommGrpCat.{u}).unit.app P))).symm
  have hF1 : IsZero F.1 := isZero_presheaf_of_isZero_stalks ⟨F.1, F.2⟩ hStalkSheafify
  exact IsZero.of_full_of_faithful_of_isZero (sheafToPresheaf J AddCommGrpCat.{u}) F hF1

end Sheafification

/-! ### Vanishing of the higher direct images -/

section Vanishing

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

attribute [local instance]
  CategoryTheory.Limits.preservesBinaryBiproducts_of_preservesBinaryProducts

-- Seated from `RingedSpaceModuleAdjunction`, not restated: pushforward of module sheaves along
-- a morphism of ringed spaces is a right adjoint, a theorem there, given the instance attribute
-- where it is needed.
attribute [local instance] RingedSpaceModuleAdjunction.modulePushforward_isRightAdjoint

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- The cohomology presheaf of [Stacks, Tag 01E4] on the target of a morphism of schemes, read as
a presheaf of abelian groups: on an open `V` of `S` its sections are `H ⁿ(f⁻¹(V), F)`. -/
abbrev preimageCohomologyPresheaf (F : X.Modules) (n : ℕ) :
    TopCat.Presheaf AddCommGrpCat.{u} (Stacks.SchemeCohomology.ringedSpace S).carrier :=
  (PresheafOfModules.toPresheaf
      (structureSheafRing (Stacks.SchemeCohomology.ringedSpace S)).obj).obj
    (((cohFunctor.{u, u, u, u, u, u} (opensMap (Stacks.SchemeCohomology.hom f))
      (structureSheafRing (Stacks.SchemeCohomology.ringedSpace X))
      (structureSheafRing (Stacks.SchemeCohomology.ringedSpace S))
      (structureSheafHom (Stacks.SchemeCohomology.hom f))).rightDerived n).obj F)

/-- The cohomology presheaf is zero over `V` as soon as `H ⁿ(f⁻¹(V), F)` is. -/
private theorem isZero_preimageCohomologyPresheaf_obj_of_isZero_hgroup (F : X.Modules) (n : ℕ)
    (V : S.Opens) (h : IsZero (Hgroup X.ringCatSheaf (f ⁻¹ᵁ V) n F)) :
    IsZero ((preimageCohomologyPresheaf f F n).obj (op V)) :=
  h.of_iso ((preimageCohomologyPresheaf_evaluation_iso (Stacks.SchemeCohomology.hom f) V n).app F)

/-- **The cohomology presheaf vanishes on the affine opens of the target.** On an affine open `V`
its sections are `H ⁿ(f⁻¹(V), F)`, the inverse image `f⁻¹(V)` is an affine open because `f` is
affine, and `H ⁿ` of a quasi-coherent module on an affine open vanishes for `n > 0` by
[Stacks, Tag 01XB]. -/
theorem isZero_preimageCohomologyPresheaf_obj [IsAffineHom f] (F : X.Modules)
    [F.IsQuasicoherent] (n : ℕ) (hn : 0 < n) (V : S.Opens) (hV : V ∈ S.affineOpens) :
    IsZero ((preimageCohomologyPresheaf f F n).obj (op V)) := by
  exact isZero_preimageCohomologyPresheaf_obj_of_isZero_hgroup f F n V
    (Stacks.Cohomology.AffineOpen.isZero_hgroup_of_isAffineOpen X F (f ⁻¹ᵁ V) (hV.preimage f) n hn)

/-- **Vanishing of a higher direct image is detected on a basis of the target.** If the
cohomology `H ⁿ(f⁻¹(V), F)` vanishes for every member `V` of a basis `B` of the opens of `S`,
then `R ⁿ f_* F = 0`.

This is the whole of the deduction of [Stacks, Tag 01XC] from [Stacks, Tag 01XB] with the
affineness removed: by [Stacks, Tag 01E4] the higher direct image is the sheafification of the
presheaf `V ↦ H ⁿ(f⁻¹(V), F)`, a presheaf vanishing on a basis has zero sheafification, and
`SheafOfModules.toSheaf` reflects isomorphisms. Neither `f` nor `F` carries any hypothesis. -/
theorem isZero_rightDerivedPlus_pushforward_of_isZero_hgroup_preimage (F : X.Modules) (n : ℕ)
    {B : Set S.Opens} (hB : Opens.IsBasis B)
    (hvan : ∀ V ∈ B, IsZero (Hgroup X.ringCatSheaf (f ⁻¹ᵁ V) n F)) :
    IsZero (((Scheme.Modules.pushforward f).rightDerivedPlus (n : ℤ)).obj F) := by
  set RS := structureSheafRing (Stacks.SchemeCohomology.ringedSpace S) with hRS
  set Q := ((cohFunctor.{u, u, u, u, u, u} (opensMap (Stacks.SchemeCohomology.hom f))
    (structureSheafRing (Stacks.SchemeCohomology.ringedSpace X)) RS
    (structureSheafHom (Stacks.SchemeCohomology.hom f))).rightDerived n).obj F with hQ
  -- The cohomology presheaf of [Stacks, Tag 01E4] vanishes on `B`.
  have hPresheaf : ∀ V ∈ B, IsZero ((preimageCohomologyPresheaf f F n).obj (op V)) :=
    fun V hV ↦ isZero_preimageCohomologyPresheaf_obj_of_isZero_hgroup f F n V (hvan V hV)
  -- The sheafification of the cohomology presheaf, as a sheaf of abelian groups, is zero.
  have hSheaf : IsZero ((presheafToSheaf
      (Opens.grothendieckTopology (Stacks.SchemeCohomology.ringedSpace S).carrier)
      AddCommGrpCat.{u}).obj (preimageCohomologyPresheaf f F n)) :=
    isZero_sheafification_of_isZero_on_basis hB _ hPresheaf
  -- Hence so is its sheafification as a sheaf of `𝒪_S`-modules.
  have hModuleSheaf : IsZero ((PresheafOfModules.sheafification (𝟙 RS.obj)).obj Q) := by
    set M := (PresheafOfModules.sheafification (𝟙 RS.obj)).obj Q with hM
    set T := SheafOfModules.toSheaf RS with hT
    have hTM : IsZero (T.obj M) :=
      hSheaf.of_iso ((PresheafOfModules.sheafificationCompToSheaf (𝟙 RS.obj)).app Q)
    set z : M ⟶ 0 := (isZero_zero _).from_ M with hz
    have hiso : IsIso (T.map z) :=
      isIso_of_source_target_iso_zero _ hTM.isoZero (T.map_isZero (isZero_zero _)).isoZero
    have hiso' : IsIso z := (isIso_iff_of_reflects_iso z T).mp hiso
    exact (isZero_zero _).of_iso (asIso z)
  -- And the higher direct image is that sheafification.
  exact hModuleSheaf.of_iso
    ((higherDirectImage_iso_sheafify_preimageCohomology
      (Stacks.SchemeCohomology.hom f) n).app F)

/-- **[Stacks, Tag 01XC] in degree `n : ℕ`.** The `n`-th higher direct image of a quasi-coherent
module along an affine morphism vanishes for `n > 0`.

The affine opens of `S` are a basis, and the preimage of an affine open under an affine morphism
is an affine open, over which [Stacks, Tag 01XB] kills the cohomology of a quasi-coherent module
in positive degree; so
`isZero_rightDerivedPlus_pushforward_of_isZero_hgroup_preimage` applies. -/
theorem isZero_rightDerivedPlus_pushforward_nat [IsAffineHom f] (F : X.Modules)
    [F.IsQuasicoherent] (n : ℕ) (hn : 0 < n) :
    IsZero (((Scheme.Modules.pushforward f).rightDerivedPlus (n : ℤ)).obj F) :=
  isZero_rightDerivedPlus_pushforward_of_isZero_hgroup_preimage f F n S.isBasis_affineOpens
    fun V hV ↦ Stacks.Cohomology.AffineOpen.isZero_hgroup_of_isAffineOpen X F (f ⁻¹ᵁ V)
      (hV.preimage f) n hn

/-- **[Stacks, Tag 01XC].** If `f : X ⟶ S` is an affine morphism of schemes and `F` is a
quasi-coherent `𝒪_X`-module, then `R ⁱ f_* F = 0` for every `i > 0`. -/
@[stacks 01XC]
theorem isZero_rightDerivedPlus_pushforward [IsAffineHom f] (F : X.Modules)
    [F.IsQuasicoherent] (i : ℤ) (hi : 0 < i) :
    IsZero (((Scheme.Modules.pushforward f).rightDerivedPlus i).obj F) := by
  obtain ⟨n, hn⟩ : ∃ n : ℕ, i = (n : ℤ) := ⟨i.toNat, (Int.toNat_of_nonneg hi.le).symm⟩
  subst hn
  exact isZero_rightDerivedPlus_pushforward_nat f F n (by omega)

/-- **[Stacks, Tag 01XC] in Mathlib's `ℕ`-indexed spelling.** This is the form that
[Stacks, Tag 01F4] part (1) takes as its hypothesis. -/
theorem isZero_rightDerived_pushforward [IsAffineHom f] (F : X.Modules) [F.IsQuasicoherent]
    (n : ℕ) (hn : 0 < n) :
    IsZero (((Scheme.Modules.pushforward f).rightDerived n).obj F) :=
  (Stacks.DerivedIndexing.isZero_rightDerivedPlus_obj_iff (Scheme.Modules.pushforward f)
    (rfl : (n : ℤ) = (n : ℤ)) F).1 (isZero_rightDerivedPlus_pushforward_nat f F n hn)

/-- **A quasi-coherent module is right acyclic for the pushforward along an affine morphism.**
The pushforward is a right adjoint, hence left exact
(`Stacks.SchemeCohomology.pushforward_preservesFiniteLimits`), so part (2) of
[Stacks, Tag 015C] turns the vanishing of [Stacks, Tag 01XC] into right acyclicity. -/
theorem rightAcyclic_pushforward [IsAffineHom f] (F : X.Modules) [F.IsQuasicoherent] :
    (Scheme.Modules.pushforward f).rightAcyclic F :=
  ((Functor.rightAcyclic_iff_isIso_and_isZero_rightDerivedPlus
      (Scheme.Modules.pushforward f) F).2 inferInstance).2
    fun i hi ↦ isZero_rightDerivedPlus_pushforward f F i hi

end Vanishing

end Stacks.AffineHigherDirectImage

end
