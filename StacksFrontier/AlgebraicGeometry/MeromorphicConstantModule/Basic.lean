module

public import StacksFrontier.AlgebraicGeometry.Divisors.Meromorphic.MeromorphicSections
public import StacksFrontier.AlgebraicGeometry.GenericStalkBaseChange.Basic
public import StacksFrontier.AlgebraicGeometry.MeromorphicConstant.Basic
public import StacksFrontier.AlgebraicGeometry.MeromorphicConstantModule.LocallyBijective
public import StacksFrontier.AlgebraicGeometry.OpensSheafificationInstances

/-!
# Meromorphic sections of a quasi-coherent module on an integral scheme

On an integral scheme `X` with generic point `η` and function field `K = 𝒪_{X, η}`, the sheaf
`K_X(F)` of meromorphic sections of a quasi-coherent `𝒪_X`-module `F` is the constant sheaf with
value the stalk `F_η`, as a sheaf of modules over the sheaf `K_X` of meromorphic functions.

## Main definitions

* `Stacks.AlgebraicGeometry.MeromorphicConstantModule.toTotalQuotient`: the morphism from the
  constant presheaf of rings with value the function field to the sheaf of total quotient rings,
  obtained from part (1) of the tag.
* `Stacks.AlgebraicGeometry.MeromorphicConstantModule.constGenericStalkSheaf`: the constant sheaf
  of modules with value `F_η`, over the sheaf of total quotient rings, together with its constant
  sections `constGenericStalkSection`.
* `Stacks.AlgebraicGeometry.MeromorphicConstantModule.compare`: the comparison of presheaves of
  modules `K_X ⊗_{𝒪_X} F ⟶ K_X ⊗_K F_η`, given on a pure tensor by `a ⊗ m ↦ a ⊗ germ_η m`.

## Main results

* `Stacks.AlgebraicGeometry.MeromorphicConstantModule.meromorphicSectionSheafIsoConstant` is
  part (2) of [Stacks, Tag 01X5]: the isomorphism, together with the statement that it carries
  the image of a section of `F` to the constant section given by its germ at the generic point.

## Implementation notes

Part (1) of the tag, `Stacks.AlgebraicGeometry.MeromorphicConstant.totalQuotientSheafIsoConstant`,
identifies `K_X` with the constant sheaf on `K`. That identification is used here only through
`toTotalQuotient`, the composite of the sheafification unit of the constant presheaf with the
inverse of part (1)'s isomorphism; the whole content of part (1) that part (2) needs is
`toTotalQuotient_app_germ`, which says that `toTotalQuotient` carries the germ at `η` of a regular
function to its image in `K_X`. Equivalently — and this is the form in which it is used —
`algebraOfSections` and `algebraOfFunctionField` form a scalar tower, so that `K_X(U)` is a
`K`-algebra over `Γ(X, U)`.

Both sides of the comparison are sheafifications, so neither has computable sections over an
arbitrary open set, and unlike in part (1) there is no need for a third sheaf: a morphism of
presheaves of modules *does* exist in one direction, namely `compare`, because over the empty
open set — the only open set of an irreducible space missing the generic point — the target
vanishes (`subsingleton_constModuleOverTotalQuotient`). The comparison is then an isomorphism
after sheafification because it is bijective on the sections over every nonempty affine open,
hence locally bijective; this is
`Stacks.AlgebraicGeometry.MeromorphicConstantModule.isIso_sheafification_map_of_bijective_basis`
in the companion file, used here in the unfolded form `isIso_tqSheafification_map_compare`.

The affine computation is where quasi-coherence enters, and it needs no surjectivity or
injectivity of anything: on a nonempty affine open `U`, with `A = Γ(X, U)` and `M = Γ(F, U)`,
the comparison is the composite of `TensorProduct.AlgebraTensorModule.cancelBaseChange`, which
rewrites `K_X(U) ⊗_A M` as `K_X(U) ⊗_K (K ⊗_A M)`, with the base-change identification
`K ⊗_A M ≅ F_η` of
`Stacks.AlgebraicGeometry.GenericStalkBaseChange.functionFieldTensorSectionsEquiv`. Both factors
are isomorphisms, so no property of `toTotalQuotient` beyond the scalar tower is used.

The statement is over the repository's and Mathlib's own names, and it differs deliberately on
one point from a literal transcription, which would state the compatibility clause about the *unit* of an
adjunction produced by a `Nonempty`-valued theorem, which records no choice of adjunction and is
therefore not a computable morphism. Here the clause is stated about `toMeromorphicSection` and
`constGenericStalkSection`, which are the explicit maps `m ↦ [1 ⊗ m]` and `v ↦ [1 ⊗ v]` built
from `tqUnit`, the unit of `PresheafOfModules.sheafificationAdjunction` — that unit is
`CategoryTheory.toSheafify` on the nose, hence computable.

## References

* [Stacks Project, Tag 01X5](https://stacks.math.columbia.edu/tag/01X5)
* [Stacks Project, Tag 01X4](https://stacks.math.columbia.edu/tag/01X4)
* [Stacks Project, Tag 03CU](https://stacks.math.columbia.edu/tag/03CU)
-/

@[expose] public section

open CategoryTheory Limits TopologicalSpace Opposite TensorProduct
open AlgebraicGeometry
open scoped AlgebraicGeometry nonZeroDivisors

universe u

namespace Stacks.AlgebraicGeometry.MeromorphicConstantModule

open Stacks.AlgebraicGeometry.MeromorphicConstant
open Stacks.AlgebraicGeometry.GenericStalkBaseChange
open Stacks.AlgebraicGeometry.AssociatedPointPrime
open Stacks.AlgebraicGeometry.AssociatedPointsMono

variable (X : Scheme.{u}) [IsIntegral X]

/-- The constant presheaf of rings with value the function field. -/
noncomputable abbrev constPresheaf : TopCat.Presheaf CommRingCat.{u} X :=
  constantPresheafOnSpace X CommRingCat.{u} X.functionField

/-- The canonical morphism from the constant presheaf with value the function field to the sheaf
of total quotient rings: the sheafification unit followed by the inverse of the identification of
part (1) of Stacks 01X5. -/
noncomputable def toTotalQuotient :
    constPresheaf X ⟶ (totalQuotientSheaf X.sheaf).obj :=
  toSheafify (Opens.grothendieckTopology X) (constPresheaf X) ≫ (presheafIso X).inv

/-- **The defining property of `toTotalQuotient`**: on an open set containing the generic point it
carries the germ at the generic point of a regular function to the image of that function in the
sheaf of total quotient rings. This is part (1) of Stacks 01X5, read backwards. -/
theorem toTotalQuotient_app_germ {U : X.Opens} (h : genericPoint X ∈ U) (r : Γ(X, U)) :
    (toTotalQuotient X).app (op U) (X.presheaf.germ U (genericPoint X) h r) =
      (toTotalQuotientSheaf X.sheaf).hom.app (op U) r := by
  have key := sheafIso_hom_app_apply X U r h
  rw [sheafIso_hom_hom] at key
  have h2 : (presheafIso X).inv.app (op U) ((presheafIso X).hom.app (op U)
      ((toTotalQuotientSheaf X.sheaf).hom.app (op U) r)) =
      (toTotalQuotientSheaf X.sheaf).hom.app (op U) r :=
    ConcreteCategory.congr_hom (Iso.hom_inv_id_app (presheafIso X) (op U)) _
  simp only [toTotalQuotient]
  exact (congrArg (ConcreteCategory.hom ((presheafIso X).inv.app (op U))) key).symm.trans h2

/-! ### The two algebra structures on the sections of the sheaf of total quotient rings -/

/-- The `Γ(X, U)`-algebra structure on the sections of the sheaf of total quotient rings. It is
the structure which the sectionwise tensor product of Tag 03CU uses. -/
@[instance_reducible]
noncomputable def algebraOfSections (U : X.Opens) :
    Algebra Γ(X, U) ((totalQuotientSheaf X.sheaf).obj.obj (op U)) :=
  ((toTotalQuotientSheaf X.sheaf).hom.app (op U)).hom.toAlgebra

/-- The function-field-algebra structure on the sections of the sheaf of total quotient rings,
through `toTotalQuotient`. -/
@[instance_reducible]
noncomputable def algebraOfFunctionField (U : X.Opens) :
    Algebra X.functionField ((totalQuotientSheaf X.sheaf).obj.obj (op U)) :=
  ((toTotalQuotient X).app (op U)).hom.toAlgebra

/-- The two algebra structures of `algebraOfSections` and `algebraOfFunctionField` form a tower
over the germ at the generic point. This is the content of part (1) of Stacks 01X5. -/
theorem isScalarTower_totalQuotient {U : X.Opens} [Nonempty U] :
    letI := algebraOfSections X U
    letI := algebraOfFunctionField X U
    IsScalarTower Γ(X, U) X.functionField
      ((totalQuotientSheaf X.sheaf).obj.obj (op U)) := by
  let := algebraOfSections X U
  let := algebraOfFunctionField X U
  have hη : genericPoint X ∈ U := genericPoint_mem_of_nonempty X ‹Nonempty U›
  refine ⟨fun r c a ↦ ?_⟩
  have hmul : (algebraMap X.functionField ((totalQuotientSheaf X.sheaf).obj.obj (op U)))
      ((algebraMap Γ(X, U) X.functionField) r) =
      (algebraMap Γ(X, U) ((totalQuotientSheaf X.sheaf).obj.obj (op U))) r := by
    show (toTotalQuotient X).app (op U) (X.germToFunctionField U r) =
      (toTotalQuotientSheaf X.sheaf).hom.app (op U) r
    exact toTotalQuotient_app_germ X hη r
  rw [Algebra.smul_def, Algebra.smul_def, Algebra.smul_def, map_mul, hmul,
    Algebra.smul_def, mul_assoc]

/-! ### The constant presheaf of modules on the generic stalk -/

variable {X}

/-- The stalk of a module at the generic point, as a module over the function field. -/
noncomputable def genericStalk (F : X.Modules) : ModuleCat.{u} X.functionField :=
  letI := stalkModule F (genericPoint X)
  ModuleCat.of X.functionField (F.presheaf.stalk (genericPoint X))

/-- The constant presheaf of modules with value `M`, over the constant presheaf of rings with
value the function field. -/
noncomputable def constModulePresheaf (X : Scheme.{u}) [IsIntegral X]
    (M : ModuleCat.{u} X.functionField) :
    PresheafOfModules.{u} (Stacks.PresheafOfModules.ChangeOfRings.ringPresheaf (constPresheaf X))
      where
  obj _ := M
  map {U V} f :=
    (ModuleCat.restrictScalarsId'
      ((Stacks.PresheafOfModules.ChangeOfRings.ringPresheaf (constPresheaf X)).map f).hom
        rfl).inv.app M
  map_id _ := by simp
  map_comp _ _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rfl

/-- The sections of the constant presheaf of modules are `M` itself; the module structure over
the function field is not found by instance search because the ring of sections of the constant
presheaf of rings is only definitionally the function field. -/
noncomputable local instance moduleConstModulePresheafObj (X : Scheme.{u}) [IsIntegral X]
    (M : ModuleCat.{u} X.functionField) (U : (Opens X)ᵒᵖ) :
    Module X.functionField ((constModulePresheaf X M).obj U) :=
  inferInstanceAs (Module X.functionField M)

/-- The restriction maps of the constant presheaf of modules are the identity of `M`. -/
theorem constModulePresheaf_map_apply (X : Scheme.{u}) [IsIntegral X]
    (M : ModuleCat.{u} X.functionField) {U V : (Opens X)ᵒᵖ} (f : U ⟶ V) (x : M) :
    ((constModulePresheaf X M).map f).hom x = x := rfl

/-- The presheaf `U ↦ K_X(U) ⊗_{K(X)} M` of modules over the sheaf of total quotient rings. Its
sheafification is the constant sheaf of modules with value `M`. -/
noncomputable def constModuleOverTotalQuotient (X : Scheme.{u}) [IsIntegral X]
    (M : ModuleCat.{u} X.functionField) :
    Stacks.PresheafOfModules.ChangeOfRings.PMod ((totalQuotientSheaf X.sheaf).obj) :=
  (Stacks.PresheafOfModules.ChangeOfRings.changeOfRings (toTotalQuotient X)).obj
    (constModulePresheaf X M)

/-- The constant section determined by an element of `M`. -/
noncomputable def constSection (X : Scheme.{u}) [IsIntegral X]
    (M : ModuleCat.{u} X.functionField) (U : X.Opens) (v : M) :
    (constModuleOverTotalQuotient X M).obj (op U) :=
  letI := algebraOfFunctionField X U
  (1 : (totalQuotientSheaf X.sheaf).obj.obj (op U)) ⊗ₜ[X.functionField] v

/-- The constant section determined by `v` is the pure tensor `1 ⊗ v`. -/
theorem constSection_eq (X : Scheme.{u}) [IsIntegral X]
    (M : ModuleCat.{u} X.functionField) (U : X.Opens) (v : M) :
    letI := algebraOfFunctionField X U
    constSection X M U v =
      (1 : (totalQuotientSheaf X.sheaf).obj.obj (op U)) ⊗ₜ[X.functionField] v := rfl

/-- The constant section is additive in the element of `M`. -/
theorem constSection_add (X : Scheme.{u}) [IsIntegral X]
    (M : ModuleCat.{u} X.functionField) (U : X.Opens) (v w : M) :
    constSection X M U (v + w) = constSection X M U v + constSection X M U w := by
  let := algebraOfFunctionField X U
  exact TensorProduct.tmul_add _ v w

/-- The constant section of `c • v` is the image of `c` in the sheaf of total quotient rings
acting on the constant section of `v`. -/
theorem constSection_smul (X : Scheme.{u}) [IsIntegral X]
    (M : ModuleCat.{u} X.functionField) (U : X.Opens) (c : X.functionField) (v : M) :
    constSection X M U (c • v) =
      ((toTotalQuotient X).app (op U) c) • constSection X M U v := by
  let := algebraOfFunctionField X U
  rw [constSection_eq, constSection_eq]
  have step1 : (algebraMap X.functionField ((totalQuotientSheaf X.sheaf).obj.obj (op U)) c) •
      ((1 : (totalQuotientSheaf X.sheaf).obj.obj (op U)) ⊗ₜ[X.functionField] v) =
      ((algebraMap X.functionField ((totalQuotientSheaf X.sheaf).obj.obj (op U)) c) •
        (1 : (totalQuotientSheaf X.sheaf).obj.obj (op U))) ⊗ₜ[X.functionField] v :=
    TensorProduct.smul_tmul' _ _ _
  have step2 : (algebraMap X.functionField ((totalQuotientSheaf X.sheaf).obj.obj (op U)) c) •
      (1 : (totalQuotientSheaf X.sheaf).obj.obj (op U)) =
      c • (1 : (totalQuotientSheaf X.sheaf).obj.obj (op U)) :=
    algebraMap_smul _ c _
  rw [step2] at step1
  exact (step1.trans (TensorProduct.smul_tmul c 1 v)).symm

/-- Restriction carries the constant section determined by `v` over `U` to the constant section
determined by `v` over `V`. -/
theorem constSection_naturality (X : Scheme.{u}) [IsIntegral X]
    (M : ModuleCat.{u} X.functionField) {U V : X.Opens} (i : V ⟶ U) (v : M) :
    ((constModuleOverTotalQuotient X M).map i.op).hom (constSection X M U v) =
      constSection X M V v := by
  let := algebraOfFunctionField X U
  let := algebraOfFunctionField X V
  rw [constSection_eq, constSection_eq]
  refine (Stacks.PresheafOfModules.ChangeOfRings.cofMap_tmul (toTotalQuotient X)
    (constModulePresheaf X M) i.op 1 v).trans ?_
  rw [map_one, constModulePresheaf_map_apply]
  rfl

/-! ### Vanishing over the empty open set -/

/-- The sections of the sheaf of total quotient rings over the empty open set form the zero
ring. -/
theorem subsingleton_totalQuotient_of_eq_bot (X : Scheme.{u}) [IsIntegral X] {V : X.Opens}
    (hV : V = ⊥) :
    Subsingleton ((totalQuotientSheaf X.sheaf).obj.obj (op V)) := by
  have h := TopCat.Sheaf.isTerminalOfEqEmpty (totalQuotientSheaf X.sheaf) hV
  have := Types.isTerminalEquivUnique _ (h.isTerminalObj (forget CommRingCat))
  infer_instance

/-- Over an open set not containing the generic point — that is, over the empty open set — the
constant presheaf of modules on the generic stalk has only the zero section. -/
theorem subsingleton_constModuleOverTotalQuotient (X : Scheme.{u}) [IsIntegral X]
    (M : ModuleCat.{u} X.functionField) {V : X.Opens} (hV : genericPoint X ∉ V) :
    Subsingleton ((constModuleOverTotalQuotient X M).obj (op V)) := by
  have hbot : V = ⊥ := by
    by_contra hne
    refine hV (((genericPoint_spec X).mem_open_set_iff V.isOpen).mpr ?_)
    refine Set.inter_nonempty.mpr ?_
    by_contra hh
    refine hne ?_
    ext x
    show (x ∈ V ↔ False)
    rw [iff_false]
    exact fun hx ↦ hh ⟨x, Set.mem_univ x, hx⟩
  have := subsingleton_totalQuotient_of_eq_bot X hbot
  exact Module.subsingleton ((totalQuotientSheaf X.sheaf).obj.obj (op V)) _

/-! ### The comparison morphism -/

variable (F : X.Modules)

/-- The underlying presheaf of modules of a sheaf of modules on a scheme, named at the spelling
`Stacks.PresheafOfModules.ChangeOfRings.PMod X.presheaf` of its presheaf of rings. The two
spellings of that presheaf of rings — through `AlgebraicGeometry.Scheme.ringCatSheaf` and through
`Stacks.PresheafOfModules.ChangeOfRings.ringPresheaf` — are only definitionally equal, and
instance search does not cross between them. -/
noncomputable def pmod (F : X.Modules) : Stacks.PresheafOfModules.ChangeOfRings.PMod X.presheaf :=
  F.val

omit [IsIntegral X] in
/-- `pmod F` is the underlying presheaf of modules of `F`. -/
theorem pmod_eq (F : X.Modules) : pmod F = F.val := rfl

/-- The `𝒪_X`-module structure on the sections of the constant presheaf of modules, obtained by
restriction of scalars along the canonical morphism to the sheaf of total quotient rings. It has
to be supplied explicitly: elaboration unfolds the restriction-of-scalars wrapper away, so
instance search no longer sees which morphism the structure comes from. -/
noncomputable local instance moduleConstModuleOverTotalQuotientRestricted
    (M : ModuleCat.{u} X.functionField) (U : (Opens X)ᵒᵖ) :
    Module ((Stacks.PresheafOfModules.ChangeOfRings.ringPresheaf X.presheaf).obj U)
      ((constModuleOverTotalQuotient X M).obj U) :=
  ModuleCat.isModule (((Stacks.PresheafOfModules.ChangeOfRings.restrictScalars (toTotalQuotientSheaf
    X.sheaf).hom).obj
    (constModuleOverTotalQuotient X M)).obj U)

/-- Membership of the generic point in an open set is decidable, classically. -/
noncomputable local instance decidableGenericPointMem' (U : X.Opens) :
    Decidable (genericPoint X ∈ U) := Classical.dec _

/-- **The comparison morphism, componentwise.** Over an open set containing the generic point it
sends a section of `F` to the constant section determined by its germ at the generic point; over
the empty open set — the only open set missing the generic point — the target vanishes. -/
noncomputable def toConstApp (U : (Opens X)ᵒᵖ) :
    (pmod F).obj U ⟶ ((Stacks.PresheafOfModules.ChangeOfRings.restrictScalars (toTotalQuotientSheaf
      X.sheaf).hom).obj
      (constModuleOverTotalQuotient X (genericStalk F))).obj U := by
  refine ModuleCat.ofHom
    { toFun := fun m ↦ if h : genericPoint X ∈ U.unop then
        constSection X (genericStalk F) U.unop (F.presheaf.germ U.unop (genericPoint X) h m)
        else 0
      map_add' := fun m n ↦ ?_
      map_smul' := fun r m ↦ ?_ }
  · split_ifs with h
    · exact (congrArg (constSection X (genericStalk F) U.unop)
        (map_add (ConcreteCategory.hom (F.presheaf.germ U.unop (genericPoint X) h)) m n)).trans
        (constSection_add X (genericStalk F) U.unop _ _)
    · exact (add_zero 0).symm
  · split_ifs with h
    · change constSection X (genericStalk F) U.unop
          (F.presheaf.germ U.unop (genericPoint X) h (r • m)) =
        ((toTotalQuotientSheaf X.sheaf).hom.app U r) •
          constSection X (genericStalk F) U.unop (F.presheaf.germ U.unop (genericPoint X) h m)
      refine Eq.trans (congrArg (constSection X (genericStalk F) U.unop)
        (PresheafOfModules.germ_smul F.val (genericPoint X) U.unop h r m)) ?_
      refine Eq.trans (constSection_smul X (genericStalk F) U.unop
        (X.presheaf.germ U.unop (genericPoint X) h r)
        (F.presheaf.germ U.unop (genericPoint X) h m)) ?_
      rw [toTotalQuotient_app_germ X h r]
    · exact (smul_zero _).symm

/-- Over an open set containing the generic point, `toConstApp` sends a section to the constant
section determined by its germ at the generic point. -/
theorem toConstApp_apply_of_mem {U : (Opens X)ᵒᵖ} (h : genericPoint X ∈ U.unop)
    (m : (pmod F).obj U) :
    (toConstApp F U).hom m =
      constSection X (genericStalk F) U.unop
        (F.presheaf.germ U.unop (genericPoint X) h m) := by
  show (if h : genericPoint X ∈ U.unop then
    constSection X (genericStalk F) U.unop
      (F.presheaf.germ U.unop (genericPoint X) h m) else 0) = _
  rw [dif_pos h]

/-- **The comparison morphism.** -/
noncomputable def toConst :
    pmod F ⟶ (Stacks.PresheafOfModules.ChangeOfRings.restrictScalars (toTotalQuotientSheaf
      X.sheaf).hom).obj
      (constModuleOverTotalQuotient X (genericStalk F)) :=
  PresheafOfModules.Hom.mk (fun U ↦ toConstApp F U) (by
    intro U V i
    refine ModuleCat.hom_ext (LinearMap.ext fun m ↦ ?_)
    by_cases hV : genericPoint X ∈ V.unop
    · have hU : genericPoint X ∈ U.unop := i.unop.le hV
      change (toConstApp F V).hom (((pmod F).map i).hom m) =
        ((constModuleOverTotalQuotient X (genericStalk F)).map i).hom
          ((toConstApp F U).hom m)
      refine Eq.trans (toConstApp_apply_of_mem F hV _) ?_
      refine Eq.trans (congrArg (constSection X (genericStalk F) V.unop)
        (F.presheaf.germ_res_apply i.unop (genericPoint X) hV m)) ?_
      refine Eq.trans (constSection_naturality X (genericStalk F) i.unop
        (F.presheaf.germ U.unop (genericPoint X) hU m)).symm ?_
      exact congrArg
        (fun z ↦ ((constModuleOverTotalQuotient X (genericStalk F)).map i).hom z)
        (toConstApp_apply_of_mem F hU m).symm
    · exact @Subsingleton.elim ((constModuleOverTotalQuotient X (genericStalk F)).obj V)
        (subsingleton_constModuleOverTotalQuotient X (genericStalk F) hV) _ _)

/-- Over an open set containing the generic point, `toConst` sends a section to the constant
section determined by its germ at the generic point. -/
theorem toConst_app_apply {U : X.Opens} (h : genericPoint X ∈ U) (m : (pmod F).obj (op U)) :
    ((toConst F).app (op U)).hom m =
      constSection X (genericStalk F) U (F.presheaf.germ U (genericPoint X) h m) :=
  toConstApp_apply_of_mem F (U := op U) h m

/-! ### The comparison of the two presheaves -/

/-- **The comparison of presheaves of modules** over the sheaf of total quotient rings: the
sectionwise tensor product `K_X ⊗_{𝒪_X} F` compared with the constant presheaf on the generic
stalk. It is the morphism adjoint to `toConst`, and on a pure tensor it is
`a ⊗ m ↦ a ⊗ (germ of m at the generic point)`. -/
noncomputable def compare :
    (Stacks.PresheafOfModules.ChangeOfRings.changeOfRings (toTotalQuotientSheaf X.sheaf).hom).obj
      (pmod F) ⟶
      constModuleOverTotalQuotient X (genericStalk F) :=
  Stacks.PresheafOfModules.ChangeOfRings.counitHom (toTotalQuotientSheaf X.sheaf).hom (toConst F)

/-- Over an open set containing the generic point, `compare` sends `a ⊗ m` to `a ⊗ m_η`, where
`m_η` is the germ of `m` at the generic point. -/
theorem compare_app_tmul {U : X.Opens} (h : genericPoint X ∈ U)
    (a : (totalQuotientSheaf X.sheaf).obj.obj (op U)) (m : (pmod F).obj (op U)) :
    letI := algebraOfSections X U
    letI := algebraOfFunctionField X U
    ((compare F).app (op U)).hom (a ⊗ₜ[Γ(X, U)] m) =
      a ⊗ₜ[X.functionField]
        (show genericStalk F from F.presheaf.germ U (genericPoint X) h m) := by
  let := algebraOfSections X U
  let := algebraOfFunctionField X U
  refine Eq.trans (Stacks.PresheafOfModules.ChangeOfRings.counitApp_tmul (toTotalQuotientSheaf
    X.sheaf).hom
    (toConst F) (op U) a m) ?_
  refine Eq.trans (congrArg (fun z ↦ a • z) (toConst_app_apply F h m)) ?_
  refine Eq.trans (TensorProduct.smul_tmul' a (1 : _)
    (show genericStalk F from F.presheaf.germ U (genericPoint X) h m)) ?_
  exact congrArg (fun z ↦ z ⊗ₜ[X.functionField]
    (show genericStalk F from F.presheaf.germ U (genericPoint X) h m))
    (by rw [smul_eq_mul, mul_one])

/-! ### The comparison is bijective on nonempty affine opens -/

variable [F.IsQuasicoherent]

/-- For a quasi-coherent module `F`, the comparison `compare F` is bijective on the sections over
every nonempty affine open set. -/
theorem bijective_compare_app {U : X.Opens} (hU : IsAffineOpen U) [Nonempty U] :
    Function.Bijective ((compare F).app (op U)).hom := by
  have h : genericPoint X ∈ U := genericPoint_mem_of_nonempty X ‹Nonempty U›
  let := algebraOfSections X U
  let := algebraOfFunctionField X U
  let := isScalarTower_totalQuotient X (U := U)
  let := stalkModule F (genericPoint X)
  let := sectionsStalkModule F h
  let := isScalarTower_functionField F h
  set e1 := (TensorProduct.AlgebraTensorModule.cancelBaseChange Γ(X, U) X.functionField
    ((totalQuotientSheaf X.sheaf).obj.obj (op U))
    ((totalQuotientSheaf X.sheaf).obj.obj (op U)) Γ(F, U)).symm with he1
  set e2 := TensorProduct.AlgebraTensorModule.congr
    (LinearEquiv.refl ((totalQuotientSheaf X.sheaf).obj.obj (op U))
      ((totalQuotientSheaf X.sheaf).obj.obj (op U)))
    (functionFieldTensorSectionsEquiv F hU h) with he2
  have hcomp : ∀ (a : (totalQuotientSheaf X.sheaf).obj.obj (op U)) (m : Γ(F, U)),
      e2 (e1 (a ⊗ₜ[Γ(X, U)] m)) = a ⊗ₜ[X.functionField]
        (show genericStalk F from functionFieldTensorSectionsEquiv F hU h
          ((1 : X.functionField) ⊗ₜ[Γ(X, U)] m)) :=
    fun _ _ ↦ rfl
  have h3 : ∀ m : Γ(F, U), functionFieldTensorSectionsEquiv F hU h
      ((1 : X.functionField) ⊗ₜ[Γ(X, U)] m) =
      F.presheaf.germ U (genericPoint X) h m := fun m ↦ by
    refine Eq.trans ((isBaseChange_germ_genericPoint F hU h).equiv_tmul 1 m) ?_
    rw [one_smul]
    rfl
  have key : ∀ t, ((compare F).app (op U)).hom t = e2 (e1 t) := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero =>
      refine Eq.trans (map_zero ((compare F).app (op U)).hom) ?_
      exact (Eq.trans (congrArg e2 (map_zero e1)) (map_zero e2)).symm
    | add x y hx hy =>
      refine Eq.trans (map_add ((compare F).app (op U)).hom x y) ?_
      refine Eq.trans (congrArg₂ (· + ·) hx hy) ?_
      exact (Eq.trans (congrArg e2 (map_add e1 x y)) (map_add e2 (e1 x) (e1 y))).symm
    | tmul a m =>
      refine Eq.trans (compare_app_tmul F h a m) (Eq.symm (Eq.trans (hcomp a m) ?_))
      exact congrArg (fun z ↦ a ⊗ₜ[X.functionField] (show genericStalk F from z)) (h3 m)
  have hfun : ⇑((compare F).app (op U)).hom = fun t ↦ e2 (e1 t) := funext key
  rw [hfun]
  exact e2.bijective.comp e1.bijective

/-! ### Sheafification -/

attribute [local instance]
  Stacks.OpensSheafification.hasSheafifyOpens
  Stacks.OpensSheafification.wEqualsLocallyBijectiveOpens

/-- Sheafification of presheaves of modules over the sheaf of total quotient rings. This is the
functor used to build the sheaf of meromorphic sections. -/
noncomputable def tqSheafification (X : Scheme.{u}) [IsIntegral X] :
    PresheafOfModules.{u} (Stacks.Sheaves.Differentials.ringSheaf (C := Opens X)
        (J := Opens.grothendieckTopology X) (totalQuotientSheaf.{u} X.sheaf)).obj ⥤
      SheafOfModules.{u} (Stacks.Sheaves.Differentials.ringSheaf (C := Opens X)
        (J := Opens.grothendieckTopology X) (totalQuotientSheaf.{u} X.sheaf)) :=
  PresheafOfModules.sheafification.{u} (𝟙 _)

/-- The sheaf of meromorphic sections is the sheafification of the sectionwise tensor product. -/
theorem meromorphicSectionSheaf_eq (F : X.Modules) :
    meromorphicSectionSheaf.{u, u} X.sheaf F =
      (tqSheafification X).obj
        ((Stacks.PresheafOfModules.ChangeOfRings.changeOfRings (toTotalQuotientSheaf
          X.sheaf).hom).obj (pmod F)) := rfl

/-- The canonical map from the sections of a presheaf of modules to the sections of its
sheafification. -/
noncomputable def tqUnit (X : Scheme.{u}) [IsIntegral X]
    (P : PresheafOfModules.{u} (Stacks.Sheaves.Differentials.ringSheaf (C := Opens X)
      (J := Opens.grothendieckTopology X) (totalQuotientSheaf.{u} X.sheaf)).obj)
    (U : (Opens X)ᵒᵖ) (t : P.obj U) : ((tqSheafification X).obj P).val.obj U :=
  (((PresheafOfModules.sheafificationAdjunction.{u} (𝟙 (Stacks.Sheaves.Differentials.ringSheaf (C :=
    Opens X)
    (J := Opens.grothendieckTopology X) (totalQuotientSheaf.{u} X.sheaf)).obj)).unit.app
      P).app U).hom t

/-- Sheafification is natural: the image of a sheafified morphism on a section coming from the
presheaf is the section coming from the image. -/
theorem tqUnit_naturality
    {P Q : PresheafOfModules.{u} (Stacks.Sheaves.Differentials.ringSheaf (C := Opens X)
      (J := Opens.grothendieckTopology X) (totalQuotientSheaf.{u} X.sheaf)).obj}
    (ψ : P ⟶ Q) (U : (Opens X)ᵒᵖ) (t : P.obj U) :
    (((tqSheafification X).map ψ).val.app U).hom (tqUnit X P U t) =
      tqUnit X Q U ((ψ.app U).hom t) :=
  congrArg (fun f ↦ ((PresheafOfModules.Hom.app f U).hom) t)
    ((PresheafOfModules.sheafificationAdjunction.{u} (𝟙 (Stacks.Sheaves.Differentials.ringSheaf (C
      := Opens X)
      (J := Opens.grothendieckTopology X)
        (totalQuotientSheaf.{u} X.sheaf)).obj)).unit.naturality ψ).symm

/-! ### Part (2) of Stacks 01X5 -/

/-- **The constant sheaf of modules on the generic stalk**, as a sheaf of modules over the sheaf
of meromorphic functions: the sheafification of `U ↦ K_X(U) ⊗_{K(X)} F_η`. -/
noncomputable def constGenericStalkSheaf (F : X.Modules) :
    SheafOfModules.{u} (Stacks.Sheaves.Differentials.ringSheaf (C := Opens X)
      (J := Opens.grothendieckTopology X) (totalQuotientSheaf.{u} X.sheaf)) :=
  (tqSheafification X).obj (constModuleOverTotalQuotient X (genericStalk F))

/-- The constant section of `constGenericStalkSheaf` determined by an element of the stalk at the
generic point. -/
noncomputable def constGenericStalkSection (F : X.Modules) (U : X.Opens)
    (v : genericStalk F) : (constGenericStalkSheaf F).val.obj (op U) :=
  tqUnit X (constModuleOverTotalQuotient X (genericStalk F)) (op U)
    (constSection X (genericStalk F) U v)

/-- The canonical map from the sections of `F` to the sections of the sheaf of meromorphic
sections: the class of `1 ⊗ m`. This is the computable form of the unit of the
extension-of-scalars adjunction. -/
noncomputable def toMeromorphicSection (F : X.Modules) (U : X.Opens)
    (m : (pmod F).obj (op U)) :
    (meromorphicSectionSheaf.{u, u} X.sheaf F).val.obj (op U) :=
  letI := algebraOfSections X U
  tqUnit X ((Stacks.PresheafOfModules.ChangeOfRings.changeOfRings (toTotalQuotientSheaf
    X.sheaf).hom).obj (pmod F)) (op U)
    ((1 : (totalQuotientSheaf X.sheaf).obj.obj (op U)) ⊗ₜ[Γ(X, U)] m)

/-- The sheafified comparison is an isomorphism: the presheaf comparison is bijective on the
basis of nonempty affine opens, hence locally bijective, hence inverted by sheafification. -/
theorem isIso_tqSheafification_map_compare :
    IsIso ((tqSheafification X).map (compare F)) := by
  set f := (PresheafOfModules.toPresheaf _).map (compare F)
  have hinj := isLocallyInjective_of_injective_basis f (isBasis_nonemptyAffineOpens X)
    (fun V ↦ by have := V.2.2; exact (bijective_compare_app F V.2.1).1)
  have hsurj := isLocallySurjective_of_surjective_basis f (isBasis_nonemptyAffineOpens X)
    (fun V ↦ by have := V.2.2; exact (bijective_compare_app F V.2.1).2)
  have hW : IsIso ((presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).map f) :=
    ((Opens.grothendieckTopology X).W_iff f).mp
      ((Opens.grothendieckTopology X).W_of_isLocallyBijective f)
  have h : IsIso ((SheafOfModules.toSheaf _).map
    ((tqSheafification X).map (compare F))) := hW
  exact isIso_of_reflects_iso _ (SheafOfModules.toSheaf _)

/-- **Stacks Project, Tag 01X5, part (2).** On an integral scheme the sheaf of meromorphic
sections of a quasi-coherent module `F` is the constant sheaf of modules with value the stalk of
`F` at the generic point, over the sheaf of meromorphic functions, compatibly with the germ at
the generic point. -/
@[stacks 01X5 "part (2)"]
noncomputable def meromorphicSectionSheafIsoConstant :
    { e : meromorphicSectionSheaf.{u, u} X.sheaf F ≅ constGenericStalkSheaf F //
      ∀ (U : X.Opens) (m : (pmod F).obj (op U)) (h : genericPoint X ∈ U),
        (e.hom.val.app (op U)).hom (toMeromorphicSection F U m) =
          constGenericStalkSection F U (F.presheaf.germ U (genericPoint X) h m) } := by
  refine ⟨@asIso _ _ _ _ ((tqSheafification X).map (compare F))
    (isIso_tqSheafification_map_compare F), fun U m h ↦ ?_⟩
  refine Eq.trans (tqUnit_naturality (compare F) (op U) _) ?_
  exact congrArg (tqUnit X (constModuleOverTotalQuotient X (genericStalk F)) (op U))
    (compare_app_tmul F h 1 m)

end Stacks.AlgebraicGeometry.MeromorphicConstantModule

end
