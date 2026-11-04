module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafificationTensor

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SectionwiseAlgebraUniversal
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorAlgebraPieceRecursion

/-!
# The tensor, exterior and symmetric algebras of a sheaf of modules

`SheafOfModules.TensorExteriorSymmetricAlgebras J F` (in
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorExteriorSymmetricAlgebras`) bundles the three
graded algebras Stacks Section 17.21 attaches to a sheaf of modules `F` on a ringed site,
together with their three universal properties, the identification of the homogeneous pieces of
`T(F)` with the sheafified tensor powers of `F`, and the two quotient maps. This file
**constructs the three algebras and every field of that bundle** for a sheaf of modules `F`; the
inhabitant of the bundle is assembled as `SheafOfModules.sheafifiedAlgebras` in
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.AlgebraBundleStalk`, and its ringed-space case
`SheafOfModules.ringedSpaceAlgebras` there carries the `@[stacks 01CF]` attribution.

The three algebras are the degreewise sheafifications
(`Stacks.GradedAlgebra.sheafify`) of the three *sectionwise* graded algebras
`U ↦ T_{O(U)}(F(U))`, `U ↦ ⋀_{O(U)}(F(U))` and `U ↦ Sym_{O(U)}(F(U))` of
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SectionwiseTensorAlgebra` and
`.SectionwiseExteriorSymmetricAlgebra`, whose universal properties are
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SectionwiseAlgebraUniversal`. The sheafification is
taken along the **identity** of the ring presheaf of the sheaf of rings, so that the presheaf
being sheafified in degree one is `F.val` itself and the sheafification counit identifies its
sheafification with `F`.

## Main definitions

* `SheafOfModules.sheafifiedTensorAlgebra`, `sheafifiedExteriorAlgebra` and
  `sheafifiedSymmetricAlgebra`: the three sheaves of graded algebras, with their degree-one
  generators `sheafifiedTensorGenerator`, `sheafifiedExteriorGenerator` and
  `sheafifiedSymmetricGenerator`.
* `SheafOfModules.sheafifiedTensorPieceIso`: the identification of the degree-`n` piece of `T(F)`
  with the `n`-fold tensor power `SheafOfModules.tensorPower J F n`, built from
  `SheafOfModules.tensorPowerSheafifyIso` out of the degree-zero and degree-one identifications
  `sheafifiedTensorPieceZeroIso` and `sheafifiedTensorPieceOneIso` and the sectionwise recursion
  `PresheafOfModules.tensorAlgebraPieceRecursion`.
* `SheafOfModules.sheafifiedValIso`: the sheafification of `F.val` is `F`, a case of
  `PresheafOfModules.sheafifyCounitIso`.
* `PresheafOfModules.tensorAlgebraGenIso`: the degree-one generator of the sectionwise tensor
  algebra, as an isomorphism of presheaves of modules.
* `PresheafOfModules.tensorAlgebraPieceZeroIso` and `exteriorAlgebraPieceZeroIso`: the degree-zero
  pieces of the two sectionwise algebras are the structure presheaf, by
  `TensorAlgebra.algebraMapInv` respectively `ExteriorAlgebra.algebraMapInv`.
* `SheafOfModules.tensorMulLeftSection`: the left-hand side of the `tensorPieceIso_mul_left` field.

## Main results

* `SheafOfModules.GradedAlgebra.IsUniversal.ofIso` and its three instances
  `isTensorAlgebra_ofIso`, `isExteriorAlgebra_ofIso`, `isSymmetricAlgebra_ofIso`: **a universal
  property transports along an isomorphism of the generating sheaf of modules.**
* `SheafOfModules.sheafifiedTensorPieceIso_one`, `sheafifiedTensorPieceIso_zero` and
  `sheafifiedTensorPieceIso_mul_left`: the three equations the homogeneous identifications of the
  bundle have to satisfy.
* `SheafOfModules.tensorMulLeftSection_eq`: the multiplication equation, identifying
  `tensorMulLeftSection` with the unit image of the pure tensor `s ⊗ₜ x`.
* `ExteriorAlgebra.algebraMap_algebraMapInv_of_mem_intPiece_zero` and
  `algebraMapInv_mapₛₗ_of_mem_intPiece_zero`: the exterior analogues of
  `TensorAlgebra.algebraMap_algebraMapInv_of_mem_intPiece_zero` and
  `TensorAlgebra.algebraMapInv_mapₛₗ_of_mem_intPiece_zero`.

## Implementation notes

**Why the sheafification is along the identity.** `Stacks.GradedAlgebra.sheafify` sheafifies
along any locally bijective `α : R₀ ⟶ R.obj`. Taking `R₀ := R.obj` and `α := 𝟙 R.obj` makes
`PresheafOfModules.restrictScalars α` the identity on objects *definitionally*, so the right
adjoint `SheafOfModules.forget R ⋙ restrictScalars α` sends `F` to `F.val` on the nose and the
sheafification counit is an isomorphism `(sheafification α).obj F.val ≅ F` with no transport.
With any other `α` the degree-one identification would have to cross a restriction of scalars.
`CategoryTheory.Sheaf.toRingCatMap J (𝟙 Osharp.obj) = 𝟙 (toRingCat J Osharp).obj` holds by `rfl`,
which is what lets `SheafOfModules.tensorPowerSheafifyIso` — stated for a morphism of presheaves
of *commutative* rings — be applied here.

**Universes.** The module universe is the ring universe `w`, exactly as in the bundle: the
degree-zero identifications compare with `PresheafOfModules.unit`, whose sections are the ring's,
and `SheafOfModules.unit` exists only there. This is the constraint the bundle itself records,
not a new one, and the ringed-space case of Section 17.21 — where
`structureSheafRing X = CategoryTheory.Sheaf.toRingCat _ X.sheaf` by `rfl` — has
all the universes equal anyway.

**The degree transport is paid once, at free degrees.** The `tensorPieceIso_mul_left` field
multiplies a degree-`1` by a degree-`n+1` section and compares the result with degree `n+2`,
so it carries `Eq.mp (congrArg _ h)` for `h : 1 + (n + 1) = n + 2` — an equality that cannot be
`subst`ed where the field is stated, since the degrees there are not local variables.
`Stacks.GradedAlgebra.eq_mp_sheafifyUnit` and `SheafOfModules.GradedAlgebra.map_eq_mp_mul` state
the two steps that transport is used in at *free* integer degrees, where `subst` applies, and are
then applied at the concrete ones.

**Why several steps are their own lemmas.** `sheafifiedTensorMul_gen_unit_eq_mp`,
`sheafifiedTensorPieceIso_add_two_unit_of_eq` and `tensorMulLeftSection_map` are split out of
`tensorMulLeftSection_eq` rather than inlined. Each of the three is a single application whose
arguments the elaborator would otherwise unify at once, exhausting its budget at `whnf`: the
homogeneous pieces of the sheafified algebra are spelled `((A.sheafify α).piece k).val.obj X` on
one side of each equation and `(PresheafOfModules.sheafifyRestrict α (P k)).obj X` on the other,
and the two agree only after unfolding the sheafification. Splitting the applications — and, in
`sheafifiedTensorPieceIso_add_two_unit_of_eq`, taking the sectionwise section as a *parameter*
with its presentation as a pure tensor as a hypothesis rather than writing it out — makes each
unification happen against a goal that is already fixed.

**No `@[stacks]` tag.** Tag 0FQW is the definition of a sheaf of graded algebras, carried by
`SheafOfModules.GradedAlgebra`; Section 17.21 is a section rather than a tagged statement, and
the bundle `SheafOfModules.TensorExteriorSymmetricAlgebras` it inhabits is itself untagged. What
is here is the construction the implementation notes of
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorExteriorSymmetricAlgebras` and
`.TensorAlgebraConstruction` record as missing.

## References

* [Stacks Project, Section 17.21](https://stacks.math.columbia.edu/tag/01CF)
* [Stacks Project, Tag 0FQW](https://stacks.math.columbia.edu/tag/0FQW)
* [Stacks Project, Tag 01CG](https://stacks.math.columbia.edu/tag/01CG)
* [Stacks Project, Tag 0GMW](https://stacks.math.columbia.edu/tag/0GMW)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf Opposite

universe v u w t a

/-! ## Degree zero of the exterior algebra -/

namespace ExteriorAlgebra

section IntPieceZero

variable (R : Type*) [CommRing R] (M : Type*) [AddCommGroup M] [Module R M]

/-- The degree-zero exterior power is the image of the base ring. -/
theorem intPiece_zero : intPiece R M 0 = 1 := pow_zero _

/-- The image of a scalar lies in degree zero. -/
theorem algebraMap_mem_intPiece_zero (r : R) :
    algebraMap R (ExteriorAlgebra R M) r ∈ intPiece R M 0 :=
  (intPiece_zero R M).symm ▸ Submodule.mem_one.mpr ⟨r, rfl⟩

/-- A degree-zero element of the exterior algebra is the image of a scalar, and
`ExteriorAlgebra.algebraMapInv` names that scalar. -/
theorem algebraMap_algebraMapInv_of_mem_intPiece_zero {x : ExteriorAlgebra R M}
    (hx : x ∈ intPiece R M 0) : algebraMap R (ExteriorAlgebra R M) (algebraMapInv x) = x := by
  rw [intPiece_zero] at hx
  obtain ⟨r, rfl⟩ := Submodule.mem_one.1 hx
  exact congrArg (algebraMap R (ExteriorAlgebra R M)) (algebraMap_leftInverse M r)

/-- **Base change on degree zero is the ring homomorphism itself**, read through
`ExteriorAlgebra.algebraMapInv`. -/
theorem algebraMapInv_mapₛₗ_of_mem_intPiece_zero {S : Type*} [CommRing S] {N : Type*}
    [AddCommGroup N] [Module S N] (φ : R →+* S) (u : M →ₛₗ[φ] N) {x : ExteriorAlgebra R M}
    (hx : x ∈ intPiece R M 0) : algebraMapInv (mapₛₗ φ u x) = φ (algebraMapInv x) := by
  conv_lhs => rw [← algebraMap_algebraMapInv_of_mem_intPiece_zero R M hx]
  rw [mapₛₗ_algebraMap, algebraMap_leftInverse]

end IntPieceZero

end ExteriorAlgebra

/-! ## Transport along an equality of degrees -/

namespace Stacks.GradedAlgebra

section Transport

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {R₀ : Cᵒᵖ ⥤ RingCat.{t}} {R : Sheaf J RingCat.{t}} (α : R₀ ⟶ R.obj)
  [Presheaf.IsLocallyInjective J α] [Presheaf.IsLocallySurjective J α]
  [J.WEqualsLocallyBijective AddCommGrpCat.{a}] [HasWeakSheafify J AddCommGrpCat.{a}]
  {P : ℤ → PresheafOfModules.{a} R₀}

/-- **The transport of a unit image along an equality of degrees.** -/
theorem eq_mp_sheafifyUnit (A : GradedAlgebra P) {i j : ℤ} (h : i = j) (X : Cᵒᵖ)
    {u : (P i).obj X} {v : (P j).obj X} (huv : HEq u v) :
    Eq.mp (congrArg (fun k : ℤ => (((A.sheafify α).piece k).val.obj X : Type a)) h)
        (PresheafOfModules.Hom.app (PresheafOfModules.sheafifyUnit α (P i)) X u) =
      PresheafOfModules.Hom.app (PresheafOfModules.sheafifyUnit α (P j)) X v := by
  subst h
  exact congrArg
    (fun t : (P i).obj X => PresheafOfModules.Hom.app (PresheafOfModules.sheafifyUnit α (P i)) X t)
    (eq_of_heq huv)

end Transport

end Stacks.GradedAlgebra

/-! ## Sheafification of the underlying presheaf of a sheaf of modules -/

namespace PresheafOfModules

section Counit

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {R₀ : Cᵒᵖ ⥤ RingCat.{t}} {R : Sheaf J RingCat.{t}} (α : R₀ ⟶ R.obj)
  [Presheaf.IsLocallyInjective J α] [Presheaf.IsLocallySurjective J α]
  [J.WEqualsLocallyBijective AddCommGrpCat.{a}] [HasWeakSheafify J AddCommGrpCat.{a}]

/-- **The sheafification of the underlying presheaf of a sheaf of modules is that sheaf.** This
is the counit of the sheafification adjunction, which Mathlib proves to be an isomorphism. -/
noncomputable def sheafifyCounitIso (M : SheafOfModules.{a} R) :
    (sheafification α).obj ((SheafOfModules.forget R ⋙ restrictScalars α).obj M) ≅ M :=
  (asIso ((sheafificationAdjunction α).counit)).app M

/-- The counit isomorphism undoes the sheafification unit on local sections. -/
theorem sheafifyCounitIso_hom_sheafifyUnit_apply (M : SheafOfModules.{a} R) (X : Cᵒᵖ)
    (t : ((SheafOfModules.forget R ⋙ restrictScalars α).obj M).obj X) :
    (sheafifyCounitIso α M).hom.val.app X
        (Hom.app (sheafifyUnit α ((SheafOfModules.forget R ⋙ restrictScalars α).obj M)) X t) =
      t :=
  hom_congr_apply' ((sheafificationAdjunction α).right_triangle_components M) X t

/-- The inverse of the counit isomorphism *is* the sheafification unit on local sections. -/
theorem sheafifyCounitIso_inv_apply (M : SheafOfModules.{a} R) (X : Cᵒᵖ)
    (t : ((SheafOfModules.forget R ⋙ restrictScalars α).obj M).obj X) :
    (sheafifyCounitIso α M).inv.val.app X t =
      Hom.app (sheafifyUnit α ((SheafOfModules.forget R ⋙ restrictScalars α).obj M)) X t := by
  conv_lhs => rw [← sheafifyCounitIso_hom_sheafifyUnit_apply α M X t]
  exact SheafOfModules.iso_inv_hom_app_apply (sheafifyCounitIso α M) X _

/-- **The transpose of a morphism into a sheaf, on unit images.** The morphism out of the
sheafification that the adjunction produces from `φ` — written here as `sheafification α` applied
to `φ` followed by the counit, which is what the adjunction's `homEquiv` unfolds to — agrees with
`φ` on the unit image of a local section. -/
theorem sheafifyCounitIso_map_comp_apply (M : SheafOfModules.{a} R)
    {N : PresheafOfModules.{a} R₀}
    (φ : N ⟶ (SheafOfModules.forget R ⋙ restrictScalars α).obj M) (X : Cᵒᵖ) (s : N.obj X) :
    ((sheafification α).map φ ≫ (sheafifyCounitIso α M).hom).val.app X
        (Hom.app (sheafifyUnit α N) X s) = Hom.app φ X s := by
  rw [show (((sheafification α).map φ ≫ (sheafifyCounitIso α M).hom)).val.app X
      (Hom.app (sheafifyUnit α N) X s) =
    (sheafifyCounitIso α M).hom.val.app X
      (((sheafification α).map φ).val.app X (Hom.app (sheafifyUnit α N) X s)) from rfl,
    unit_naturality_apply φ X s, sheafifyCounitIso_hom_sheafifyUnit_apply]

/-- An isomorphism of presheaves of modules undoes its inverse on local sections. -/
theorem iso_hom_app_inv_apply {R' : Cᵒᵖ ⥤ RingCat.{t}} {M N : PresheafOfModules.{a} R'}
    (e : M ≅ N) (X : Cᵒᵖ) (y : N.obj X) : Hom.app e.hom X (Hom.app e.inv X y) = y :=
  (comp_app_apply e.inv e.hom X y).symm.trans (hom_congr_apply' e.inv_hom_id X y)

end Counit

/-! ## The sectionwise degree-one and degree-zero identifications -/

section PieceIsos

variable {C : Type u} [Category.{v} C] {O : Cᵒᵖ ⥤ CommRingCat.{w}}

/-- **The degree-one generator of the sectionwise tensor algebra is an isomorphism**: the
degree-one piece of `T_{O(U)}(F(U))` is `F(U)`, naturally in `U`. -/
noncomputable def tensorAlgebraGenIso
    (F : PresheafOfModules.{max w a} (O ⋙ forget₂ _ RingCat)) : F ≅ tensorAlgebraPiece 1 F := by
  have hiso : ∀ X : Cᵒᵖ, IsIso ((tensorAlgebraGen F).app X) := fun X =>
    (ConcreteCategory.isIso_iff_bijective _).mpr
      ⟨tensorAlgebraGen_injective F X, tensorAlgebraGen_surjective F X⟩
  refine isoMk (fun X => asIso ((tensorAlgebraGen F).app X)) ?_
  intro X Y f
  exact (tensorAlgebraGen F).naturality f

/-- `PresheafOfModules.tensorAlgebraGenIso` is the degree-one generator. -/
@[simp]
theorem tensorAlgebraGenIso_hom (F : PresheafOfModules.{max w a} (O ⋙ forget₂ _ RingCat)) :
    (tensorAlgebraGenIso F).hom = tensorAlgebraGen F := rfl

variable (F : PresheafOfModules.{w} (O ⋙ forget₂ _ RingCat))

/-- **Degree zero of the sectionwise tensor algebra, on sections, is the base ring.** A
degree-zero element is the image of a unique scalar, which `TensorAlgebra.algebraMapInv` names. -/
noncomputable def tensorAlgebraPieceZeroEquiv (X : Cᵒᵖ) :
    (tensorAlgebraPiece (0 : ℤ) F).obj X ≃ₗ[(O ⋙ forget₂ _ RingCat).obj X]
      ((O ⋙ forget₂ _ RingCat).obj X) where
  toFun x := TensorAlgebra.algebraMapInv (tensorAlgebraPieceVal (0 : ℤ) F X x)
  map_add' x y := map_add _ _ _
  map_smul' r x := by
    change TensorAlgebra.algebraMapInv (r • tensorAlgebraPieceVal (0 : ℤ) F X x) = _
    rw [map_smul]
    rfl
  invFun r := ⟨algebraMap _ _ r, TensorAlgebra.algebraMap_mem_intPiece_zero _ _ r⟩
  left_inv x := Subtype.ext
    (TensorAlgebra.algebraMap_algebraMapInv_of_mem_intPiece_zero _ _
      (x : ↥(TensorAlgebra.intPiece _ _ (0 : ℤ))).2)
  right_inv r := TensorAlgebra.algebraMap_leftInverse _ r

/-- **The degree-zero piece of the sectionwise tensor algebra is the structure presheaf.** -/
noncomputable def tensorAlgebraPieceZeroIso :
    tensorAlgebraPiece (0 : ℤ) F ≅ unit (O ⋙ forget₂ CommRingCat.{w} RingCat.{w}) := by
  refine isoMk (fun X => (tensorAlgebraPieceZeroEquiv F X).toModuleIso) ?_
  intro X Y f
  refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
  exact TensorAlgebra.algebraMapInv_mapₛₗ_of_mem_intPiece_zero _ _ _ (F.restrictₛₗ f)
    (x : ↥(TensorAlgebra.intPiece _ _ (0 : ℤ))).2

/-- The degree-zero identification takes the algebra unit to `1`. -/
theorem tensorAlgebraPieceZeroIso_hom_one (X : Cᵒᵖ) :
    Hom.app (tensorAlgebraPieceZeroIso F).hom X ((tensorAlgebraOne F).eval X) =
      (1 : (O ⋙ forget₂ CommRingCat.{w} RingCat.{w}).obj X) := by
  change TensorAlgebra.algebraMapInv
      (1 : TensorAlgebra ((O ⋙ forget₂ CommRingCat.{w} RingCat.{w}).obj X) (F.obj X)) = 1
  exact map_one _

/-- The degree-zero identification of the sectionwise tensor algebra, on sections. -/
@[simp]
theorem tensorAlgebraPieceZeroIso_hom_apply (X : Cᵒᵖ)
    (x : (tensorAlgebraPiece (0 : ℤ) F).obj X) :
    Hom.app (tensorAlgebraPieceZeroIso F).hom X x =
      TensorAlgebra.algebraMapInv (tensorAlgebraPieceVal (0 : ℤ) F X x) := rfl

/-- **Degree zero of the sectionwise exterior algebra, on sections, is the base ring.** -/
noncomputable def exteriorAlgebraPieceZeroEquiv (X : Cᵒᵖ) :
    (exteriorAlgebraPiece (0 : ℤ) F).obj X ≃ₗ[(O ⋙ forget₂ _ RingCat).obj X]
      ((O ⋙ forget₂ _ RingCat).obj X) where
  toFun x := ExteriorAlgebra.algebraMapInv (exteriorAlgebraPieceVal (0 : ℤ) F X x)
  map_add' x y := map_add _ _ _
  map_smul' r x := by
    change ExteriorAlgebra.algebraMapInv (r • exteriorAlgebraPieceVal (0 : ℤ) F X x) = _
    rw [map_smul]
    rfl
  invFun r := ⟨algebraMap _ _ r, ExteriorAlgebra.algebraMap_mem_intPiece_zero _ _ r⟩
  left_inv x := Subtype.ext
    (ExteriorAlgebra.algebraMap_algebraMapInv_of_mem_intPiece_zero _ _
      (x : ↥(ExteriorAlgebra.intPiece _ _ (0 : ℤ))).2)
  right_inv r := ExteriorAlgebra.algebraMap_leftInverse _ r

/-- **The degree-zero piece of the sectionwise exterior algebra is the structure presheaf.** -/
noncomputable def exteriorAlgebraPieceZeroIso :
    exteriorAlgebraPiece (0 : ℤ) F ≅ unit (O ⋙ forget₂ CommRingCat.{w} RingCat.{w}) := by
  refine isoMk (fun X => (exteriorAlgebraPieceZeroEquiv F X).toModuleIso) ?_
  intro X Y f
  refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
  exact ExteriorAlgebra.algebraMapInv_mapₛₗ_of_mem_intPiece_zero _ _ _ (F.restrictₛₗ f)
    (x : ↥(ExteriorAlgebra.intPiece _ _ (0 : ℤ))).2

/-- The degree-zero identification takes the algebra unit to `1`. -/
theorem exteriorAlgebraPieceZeroIso_hom_one (X : Cᵒᵖ) :
    Hom.app (exteriorAlgebraPieceZeroIso F).hom X ((exteriorAlgebraOne F).eval X) =
      (1 : (O ⋙ forget₂ CommRingCat.{w} RingCat.{w}).obj X) := by
  change ExteriorAlgebra.algebraMapInv
      (1 : ExteriorAlgebra ((O ⋙ forget₂ CommRingCat.{w} RingCat.{w}).obj X) (F.obj X)) = 1
  exact map_one _

/-- The degree-zero identification of the sectionwise exterior algebra, on sections. -/
@[simp]
theorem exteriorAlgebraPieceZeroIso_hom_apply (X : Cᵒᵖ)
    (x : (exteriorAlgebraPiece (0 : ℤ) F).obj X) :
    Hom.app (exteriorAlgebraPieceZeroIso F).hom X x =
      ExteriorAlgebra.algebraMapInv (exteriorAlgebraPieceVal (0 : ℤ) F X x) := rfl

end PieceIsos

end PresheafOfModules

/-! ## Transport of a universal property along an isomorphism -/

namespace SheafOfModules

section IsoSections

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}

/-- An isomorphism of sheaves of modules undoes its inverse on local sections. -/
theorem iso_hom_app_apply_inv {M N : SheafOfModules.{a} R} (e : M ≅ N) (X : Cᵒᵖ)
    (y : N.val.obj X) : e.hom.val.app X (e.inv.val.app X y) = y :=
  iso_inv_hom_app_apply e.symm X y

/-- An isomorphism of sheaves of modules is surjective on local sections over every object. -/
theorem iso_hom_app_surjective {M N : SheafOfModules.{a} R} (e : M ≅ N) (X : Cᵒᵖ) :
    Function.Surjective (e.hom.val.app X) := fun y =>
  ⟨e.inv.val.app X y, iso_hom_app_apply_inv e X y⟩

end IsoSections

namespace GradedAlgebra

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}
  {M N : SheafOfModules.{a} R}

/-- Squaring to zero is unchanged by precomposing a degree-one generator with an isomorphism of
the generating sheaf of modules. -/
theorem squareZero_comp_iff (e : N ≅ M) {B : GradedAlgebra.{t, a} R} (κ : M ⟶ B.piece 1) :
    SquareZero (e.hom ≫ κ) ↔ SquareZero κ := by
  refine ⟨fun h U s => ?_, fun h U s => h U _⟩
  obtain ⟨s', rfl⟩ := iso_hom_app_surjective e U s
  exact h U s'

/-- Pairwise commutation is unchanged by precomposing a degree-one generator with an isomorphism
of the generating sheaf of modules. -/
theorem pairwiseCommutes_comp_iff (e : N ≅ M) {B : GradedAlgebra.{t, a} R}
    (κ : M ⟶ B.piece 1) : PairwiseCommutes (e.hom ≫ κ) ↔ PairwiseCommutes κ := by
  refine ⟨fun h U s u => ?_, fun h U s u => h U _ _⟩
  obtain ⟨s', rfl⟩ := iso_hom_app_surjective e U s
  obtain ⟨u', rfl⟩ := iso_hom_app_surjective e U u
  exact h U s' u'

/-- **A universal property of a sheaf of graded algebras transports along an isomorphism of the
generating sheaf of modules**, provided the property of generators transports. -/
theorem IsUniversal.ofIso (e : N ≅ M)
    {P : ∀ B : GradedAlgebra.{t, a} R, (M ⟶ B.piece 1) → Prop}
    {P' : ∀ B : GradedAlgebra.{t, a} R, (N ⟶ B.piece 1) → Prop}
    (hP : ∀ (B : GradedAlgebra.{t, a} R) (κ : M ⟶ B.piece 1), P' B (e.hom ≫ κ) ↔ P B κ)
    {A : GradedAlgebra.{t, a} R} {ι : M ⟶ A.piece 1} (hA : IsUniversal P A ι) :
    IsUniversal P' A (e.hom ≫ ι) := by
  refine ⟨(hP A ι).2 hA.1, fun B κ' hκ' => ?_⟩
  obtain ⟨g, hg, hgu⟩ := hA.2 B (e.inv ≫ κ') ((hP B (e.inv ≫ κ')).1 (by
    rw [← Category.assoc, e.hom_inv_id, Category.id_comp]; exact hκ'))
  refine ⟨g, ?_, fun h hh => hgu h ?_⟩
  · change (e.hom ≫ ι) ≫ g.app 1 = κ'
    rw [Category.assoc, hg, Iso.hom_inv_id_assoc]
  · change ι ≫ h.app 1 = e.inv ≫ κ'
    have hh' : (e.hom ≫ ι) ≫ h.app 1 = κ' := hh
    rw [← hh', Category.assoc, Iso.inv_hom_id_assoc]

/-- The tensor-algebra universal property transports along an isomorphism of the generating
sheaf of modules. -/
theorem isTensorAlgebra_ofIso (e : N ≅ M) {A : GradedAlgebra.{t, a} R} {ι : M ⟶ A.piece 1}
    (hA : IsTensorAlgebra A ι) : IsTensorAlgebra A (e.hom ≫ ι) :=
  IsUniversal.ofIso e (fun _ _ => Iff.rfl) hA

/-- The exterior-algebra universal property transports along an isomorphism of the generating
sheaf of modules. -/
theorem isExteriorAlgebra_ofIso (e : N ≅ M) {A : GradedAlgebra.{t, a} R} {ι : M ⟶ A.piece 1}
    (hA : IsExteriorAlgebra A ι) : IsExteriorAlgebra A (e.hom ≫ ι) :=
  IsUniversal.ofIso e (fun _ κ => squareZero_comp_iff e κ) hA

/-- The symmetric-algebra universal property transports along an isomorphism of the generating
sheaf of modules. -/
theorem isSymmetricAlgebra_ofIso (e : N ≅ M) {A : GradedAlgebra.{t, a} R} {ι : M ⟶ A.piece 1}
    (hA : IsSymmetricAlgebra A ι) : IsSymmetricAlgebra A (e.hom ≫ ι) :=
  IsUniversal.ofIso e (fun _ κ => pairwiseCommutes_comp_iff e κ) hA

/-- **Restriction commutes with a homogeneous product read through a degree transport** along
`h : i + j = k`. -/
theorem map_eq_mp_mul (A : GradedAlgebra.{t, a} R) {i j k : ℤ} (h : i + j = k) {X Y : Cᵒᵖ}
    (f : X ⟶ Y) (u : (A.piece i).val.obj X) (v : (A.piece j).val.obj X) :
    (A.piece k).val.map f
        (Eq.mp (congrArg (fun m : ℤ => ((A.piece m).val.obj X : Type a)) h)
          ((A.mul i j).app X u v)) =
      Eq.mp (congrArg (fun m : ℤ => ((A.piece m).val.obj Y : Type a)) h)
        ((A.mul i j).app Y ((A.piece i).val.map f u) ((A.piece j).val.map f v)) := by
  subst h
  exact (A.mul i j).naturality f u v

end GradedAlgebra

/-! ## The construction -/

open PresheafOfModules Stacks.GradedAlgebra

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  {Osharp : Sheaf J CommRingCat.{w}}
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]
  (F : SheafOfModules.{w} (toRingCat J Osharp))

/-- **The sheafification of the underlying presheaf of `F` is `F`.** The sheafification is taken
along the identity of the ring presheaf, so the right adjoint of the sheafification sends `F` to
`F.val` definitionally and this is the counit. -/
noncomputable def sheafifiedValIso :
    (PresheafOfModules.sheafification (𝟙 (toRingCat J Osharp).obj)).obj F.val ≅ F :=
  PresheafOfModules.sheafifyCounitIso (𝟙 (toRingCat J Osharp).obj) F

/-! ### The tensor algebra -/

/-- **The tensor algebra `T(F)`**: the degreewise sheafification of the sectionwise tensor
algebra `U ↦ T_{O(U)}(F(U))`. -/
noncomputable def sheafifiedTensorAlgebra : GradedAlgebra.{w, w} (toRingCat J Osharp) :=
  (tensorAlgebraGradedAlgebra F.val).sheafify (𝟙 (toRingCat J Osharp).obj)

/-- **The degree-one identification** `T¹(F) ≅ F`: the sectionwise degree-one generator is an
isomorphism, and the sheafification of `F.val` is `F`. -/
noncomputable def sheafifiedTensorPieceOneIso :
    (PresheafOfModules.sheafification (𝟙 (toRingCat J Osharp).obj)).obj
        (tensorAlgebraPiece ((1 : ℕ) : ℤ) F.val) ≅ F :=
  (PresheafOfModules.sheafification (𝟙 (toRingCat J Osharp).obj)).mapIso
      (tensorAlgebraGenIso F.val).symm ≪≫
    sheafifiedValIso J F

/-- **The degree-one generator of `T(F)`**, namely the inverse of the degree-one
identification. Taking it in this form rather than as the sheafification of the sectionwise
generator makes the `tensorPieceIso_one` field of the bundle `Iso.inv_hom_id`. -/
noncomputable def sheafifiedTensorGenerator : F ⟶ (sheafifiedTensorAlgebra J F).piece 1 :=
  (sheafifiedTensorPieceOneIso J F).inv

/-- The degree-one generator is the sheafification of the sectionwise degree-one generator,
read through the counit. -/
theorem sheafifiedTensorGenerator_eq :
    sheafifiedTensorGenerator J F =
      (sheafifiedValIso J F).inv ≫
        (tensorAlgebraGradedAlgebra F.val).sheafifyGen (𝟙 (toRingCat J Osharp).obj)
          (tensorAlgebraGen F.val) := rfl

/-- **`T(F)` has the universal property of the tensor algebra on `F`.** -/
theorem isTensorAlgebra_sheafifiedTensorAlgebra :
    GradedAlgebra.IsTensorAlgebra (sheafifiedTensorAlgebra J F)
      (sheafifiedTensorGenerator J F) :=
  GradedAlgebra.isTensorAlgebra_ofIso (sheafifiedValIso J F).symm
    (isTensorAlgebra_sheafify_tensorAlgebra (𝟙 (toRingCat J Osharp).obj) F.val)

/-- **The degree-zero identification** `T⁰(F) ≅ O`: degree zero of the sectionwise tensor
algebra is the structure presheaf, whose sheafification is the structure sheaf. -/
noncomputable def sheafifiedTensorPieceZeroIso :
    (PresheafOfModules.sheafification (𝟙 (toRingCat J Osharp).obj)).obj
        (tensorAlgebraPiece ((0 : ℕ) : ℤ) F.val) ≅ SheafOfModules.unit (toRingCat J Osharp) :=
  (PresheafOfModules.sheafification (𝟙 (toRingCat J Osharp).obj)).mapIso
      (tensorAlgebraPieceZeroIso F.val) ≪≫
    PresheafOfModules.sheafifyCounitIso (𝟙 (toRingCat J Osharp).obj)
      (SheafOfModules.unit (toRingCat J Osharp))

/-- **The degree-`n` piece of `T(F)` is the `n`-fold tensor power of `F`.** -/
noncomputable def sheafifiedTensorPieceIso (n : ℕ) :
    (sheafifiedTensorAlgebra J F).piece (n : ℤ) ≅ tensorPower J F n :=
  SheafOfModules.tensorPowerSheafifyIso J (𝟙 Osharp.obj)
    (Q := fun k : ℕ => tensorAlgebraPiece ((k : ℕ) : ℤ) F.val)
    (sheafifiedTensorPieceZeroIso J F)
    (sheafifiedTensorPieceOneIso J F) (tensorAlgebraPieceRecursion F.val) n

/-- Under the degree-one identification the generator is the identity. -/
theorem sheafifiedTensorPieceIso_one :
    sheafifiedTensorGenerator J F ≫ (sheafifiedTensorPieceIso J F 1).hom = 𝟙 F :=
  (sheafifiedTensorPieceOneIso J F).inv_hom_id

/-- The degree-zero identification takes the algebra unit to `1`. -/
theorem sheafifiedTensorPieceIso_zero (U : Cᵒᵖ) :
    (sheafifiedTensorPieceIso J F 0).hom.val.app U
        ((sheafifiedTensorAlgebra J F).one.eval U) =
      (1 : (toRingCat J Osharp).obj.obj U) :=
  (PresheafOfModules.sheafifyCounitIso_map_comp_apply (𝟙 (toRingCat J Osharp).obj)
    (SheafOfModules.unit (toRingCat J Osharp)) (tensorAlgebraPieceZeroIso F.val).hom U
    ((tensorAlgebraOne F.val).eval U)).trans (tensorAlgebraPieceZeroIso_hom_one F.val U)

/-- `T(F)` has no nonzero sections in a negative degree. -/
theorem tensorPiece_eq_zero_of_neg_sheafifiedTensorAlgebra (n : ℤ) (hn : n < 0) (U : Cᵒᵖ)
    (x : ((sheafifiedTensorAlgebra J F).piece n).val.obj U) : x = 0 :=
  (tensorAlgebraGradedAlgebra F.val).sheafify_piece_eq_zero (𝟙 (toRingCat J Osharp).obj) n
    (fun X m => tensorAlgebraPiece_eq_zero_of_neg hn F.val X m) U x

/-! ### The exterior algebra -/

/-- **The exterior algebra `⋀(F)`**: the degreewise sheafification of the sectionwise exterior
algebra `U ↦ ⋀_{O(U)}(F(U))`. -/
noncomputable def sheafifiedExteriorAlgebra : GradedAlgebra.{w, w} (toRingCat J Osharp) :=
  (exteriorAlgebraGradedAlgebra F.val).sheafify (𝟙 (toRingCat J Osharp).obj)

/-- **The degree-one generator of `⋀(F)`.** -/
noncomputable def sheafifiedExteriorGenerator : F ⟶ (sheafifiedExteriorAlgebra J F).piece 1 :=
  (sheafifiedValIso J F).inv ≫
    (exteriorAlgebraGradedAlgebra F.val).sheafifyGen (𝟙 (toRingCat J Osharp).obj)
      (exteriorAlgebraGen F.val)

/-- **`⋀(F)` has the universal property of the exterior algebra on `F`.** -/
theorem isExteriorAlgebra_sheafifiedExteriorAlgebra :
    GradedAlgebra.IsExteriorAlgebra (sheafifiedExteriorAlgebra J F)
      (sheafifiedExteriorGenerator J F) :=
  GradedAlgebra.isExteriorAlgebra_ofIso (sheafifiedValIso J F).symm
    (isExteriorAlgebra_sheafify_exteriorAlgebra (𝟙 (toRingCat J Osharp).obj) F.val)

/-- **The degree-zero identification** `⋀⁰(F) ≅ O`, with the structure sheaf spelled as the
zeroth tensor power, which it is definitionally. -/
noncomputable def sheafifiedExteriorPieceZeroIso :
    (PresheafOfModules.sheafification (𝟙 (toRingCat J Osharp).obj)).obj
        (exteriorAlgebraPiece (0 : ℤ) F.val) ≅ SheafOfModules.unit (toRingCat J Osharp) :=
  (PresheafOfModules.sheafification (𝟙 (toRingCat J Osharp).obj)).mapIso
      (exteriorAlgebraPieceZeroIso F.val) ≪≫
    PresheafOfModules.sheafifyCounitIso (𝟙 (toRingCat J Osharp).obj)
      (SheafOfModules.unit (toRingCat J Osharp))

/-- The degree-zero identification of `⋀(F)` takes the algebra unit to `1`. -/
theorem sheafifiedExteriorPieceZeroIso_one (U : Cᵒᵖ) :
    (sheafifiedExteriorPieceZeroIso J F).hom.val.app U
        ((sheafifiedExteriorAlgebra J F).one.eval U) =
      (1 : (toRingCat J Osharp).obj.obj U) :=
  (PresheafOfModules.sheafifyCounitIso_map_comp_apply (𝟙 (toRingCat J Osharp).obj)
    (SheafOfModules.unit (toRingCat J Osharp)) (exteriorAlgebraPieceZeroIso F.val).hom U
    ((exteriorAlgebraOne F.val).eval U)).trans (exteriorAlgebraPieceZeroIso_hom_one F.val U)

/-- `⋀(F)` has no nonzero sections in a negative degree. -/
theorem exteriorPiece_eq_zero_of_neg_sheafifiedExteriorAlgebra (n : ℤ) (hn : n < 0) (U : Cᵒᵖ)
    (x : ((sheafifiedExteriorAlgebra J F).piece n).val.obj U) : x = 0 :=
  (exteriorAlgebraGradedAlgebra F.val).sheafify_piece_eq_zero (𝟙 (toRingCat J Osharp).obj) n
    (fun X m => exteriorAlgebraPiece_eq_zero_of_neg hn F.val X m) U x

/-! ### The symmetric algebra -/

/-- **The symmetric algebra `Sym(F)`**: the degreewise sheafification of the sectionwise
symmetric algebra `U ↦ Sym_{O(U)}(F(U))`. -/
noncomputable def sheafifiedSymmetricAlgebra : GradedAlgebra.{w, w} (toRingCat J Osharp) :=
  (symPowIntGradedAlgebra F.val).sheafify (𝟙 (toRingCat J Osharp).obj)

/-- **The degree-one generator of `Sym(F)`.** -/
noncomputable def sheafifiedSymmetricGenerator : F ⟶ (sheafifiedSymmetricAlgebra J F).piece 1 :=
  (sheafifiedValIso J F).inv ≫
    (symPowIntGradedAlgebra F.val).sheafifyGen (𝟙 (toRingCat J Osharp).obj)
      (symPowIntGen F.val)

/-- **`Sym(F)` has the universal property of the symmetric algebra on `F`.** -/
theorem isSymmetricAlgebra_sheafifiedSymmetricAlgebra :
    GradedAlgebra.IsSymmetricAlgebra (sheafifiedSymmetricAlgebra J F)
      (sheafifiedSymmetricGenerator J F) :=
  GradedAlgebra.isSymmetricAlgebra_ofIso (sheafifiedValIso J F).symm
    (isSymmetricAlgebra_sheafify_symmetricAlgebra (𝟙 (toRingCat J Osharp).obj) F.val)

/-- `Sym(F)` has no nonzero sections in a negative degree. -/
theorem symmetricPiece_eq_zero_of_neg_sheafifiedSymmetricAlgebra (n : ℤ) (hn : n < 0) (U : Cᵒᵖ)
    (x : ((sheafifiedSymmetricAlgebra J F).piece n).val.obj U) : x = 0 :=
  (symPowIntGradedAlgebra F.val).sheafify_piece_eq_zero (𝟙 (toRingCat J Osharp).obj) n
    (fun X m => symPowInt_eq_zero_of_neg n F.val hn X m) U x

/-! ### The direct-sum comparison -/

/-- **The underlying sheaf of modules of `T(F)` is the direct sum of the tensor powers**, by the
homogeneous identifications summand by summand. -/
noncomputable def sheafifiedTensorDirectSumIso :
    (∐ fun n : ℕ => tensorPower J F n) ≅
      (∐ fun n : ℕ => (sheafifiedTensorAlgebra J F).piece (n : ℤ)) :=
  Sigma.mapIso fun n => (sheafifiedTensorPieceIso J F n).symm

/-- The direct-sum comparison is induced by the homogeneous identifications.
`SheafOfModules.TensorExteriorSymmetricAlgebras.tensorDirectSumIso_unique` shows that this
determines it. -/
theorem sheafifiedTensorDirectSumIso_ι (n : ℕ) :
    Sigma.ι (fun m : ℕ => tensorPower J F m) n ≫ (sheafifiedTensorDirectSumIso J F).hom =
      (sheafifiedTensorPieceIso J F n).inv ≫
        Sigma.ι (fun m : ℕ => (sheafifiedTensorAlgebra J F).piece (m : ℤ)) n :=
  Sigma.ι_mapIso_hom _ n

/-! ### The multiplication field -/

section MulLeft

/-- The inverse of `SheafOfModules.sheafifiedValIso` is the sheafification unit on sections. -/
theorem sheafifiedValIso_inv_apply (U : Cᵒᵖ) (s : F.val.obj U) :
    (sheafifiedValIso J F).inv.val.app U s =
      Hom.app (sheafifyUnit (𝟙 (toRingCat J Osharp).obj) F.val) U s :=
  PresheafOfModules.sheafifyCounitIso_inv_apply (𝟙 (toRingCat J Osharp).obj) F U s

/-- `SheafOfModules.sheafifiedValIso` undoes the sheafification unit on sections. -/
theorem sheafifiedValIso_hom_unit_apply (U : Cᵒᵖ) (s : F.val.obj U) :
    (sheafifiedValIso J F).hom.val.app U
        (Hom.app (sheafifyUnit (𝟙 (toRingCat J Osharp).obj) F.val) U s) = s :=
  PresheafOfModules.sheafifyCounitIso_hom_sheafifyUnit_apply
    (𝟙 (toRingCat J Osharp).obj) F U s

/-- **The degree-one generator of `T(F)` on sections**: it carries a local section of `F` to the
unit image of its sectionwise degree-one generator. -/
theorem sheafifiedTensorGenerator_apply (U : Cᵒᵖ) (s : F.val.obj U) :
    (sheafifiedTensorGenerator J F).val.app U s =
      Hom.app (sheafifyUnit (𝟙 (toRingCat J Osharp).obj) (tensorAlgebraPiece 1 F.val)) U
        (Hom.app (tensorAlgebraGen F.val) U s) := by
  rw [show (sheafifiedTensorGenerator J F).val.app U s =
      Hom.app (((PresheafOfModules.sheafification (𝟙 (toRingCat J Osharp).obj)).map
          (tensorAlgebraGen F.val)).val) U
        ((sheafifiedValIso J F).inv.val.app U s) from rfl,
    sheafifiedValIso_inv_apply]
  exact PresheafOfModules.unit_naturality_apply (tensorAlgebraGen F.val) U s

/-- **The degree-one identification on sections**, read on the unit image of a sectionwise
degree-one generator: it recovers the local section of `F` it came from. -/
theorem sheafifiedTensorPieceOneIso_hom_unit_gen (U : Cᵒᵖ) (s : F.val.obj U) :
    (sheafifiedTensorPieceOneIso J F).hom.val.app U
        (Hom.app (sheafifyUnit (𝟙 (toRingCat J Osharp).obj)
          (tensorAlgebraPiece ((1 : ℕ) : ℤ) F.val)) U
          (Hom.app (tensorAlgebraGen F.val) U s)) = s := by
  exact (congrArg _ (sheafifiedTensorGenerator_apply J F U s).symm).trans
    (iso_hom_app_apply_inv (sheafifiedTensorPieceOneIso J F) U s)

end MulLeft

section MulLeft2

/-- The product of a degree-one generator with the unit image of a degree-`n+1` sectionwise
section is, after the transport of the degree equality `1 + (n + 1) = n + 2`, the unit image of
the sectionwise product, read through the tensor-power recursion. -/
theorem sheafifiedTensorMul_gen_unit_eq_mp (n : ℕ) (U : Cᵒᵖ) (s : F.val.obj U)
    (y₀ : (tensorAlgebraPiece ((n + 1 : ℕ) : ℤ) F.val).obj U) :
    Eq.mp (congrArg
        (fun k : ℤ => (((sheafifiedTensorAlgebra J F).piece k).val.obj U : Type w))
        (show 1 + ((n + 1 : ℕ) : ℤ) = ((n + 2 : ℕ) : ℤ) by omega))
      (Hom.app (sheafifyUnit (𝟙 (toRingCat J Osharp).obj)
          (tensorAlgebraPiece (1 + ((n + 1 : ℕ) : ℤ)) F.val)) U
        ((tensorAlgebraMul F.val 1 ((n + 1 : ℕ) : ℤ)).app U
          (Hom.app (tensorAlgebraGen F.val) U s) y₀)) =
      Hom.app (sheafifyUnit (𝟙 (toRingCat J Osharp).obj)
          (tensorAlgebraPiece ((n + 2 : ℕ) : ℤ) F.val)) U
        (Hom.app (tensorAlgebraPieceRecursion F.val n).inv U
          (Hom.app (tensorAlgebraGen F.val) U s ⊗ₜ y₀)) := by
  have hheq : HEq ((tensorAlgebraMul F.val 1 ((n + 1 : ℕ) : ℤ)).app U
        (Hom.app (tensorAlgebraGen F.val) U s) y₀)
      (Hom.app (tensorAlgebraPieceRecursion F.val n).inv U
        (Hom.app (tensorAlgebraGen F.val) U s ⊗ₜ y₀)) :=
    heq_of_tensorAlgebraPieceVal_eq F.val (by omega) U _ _ rfl
  exact (tensorAlgebraGradedAlgebra F.val).eq_mp_sheafifyUnit (𝟙 (toRingCat J Osharp).obj)
    (show 1 + ((n + 1 : ℕ) : ℤ) = ((n + 2 : ℕ) : ℤ) by omega) U hheq

/-- **The degree-`n+2` identification on the unit image of a sectionwise section**, given a
presentation of that section as a pure tensor through the tensor-power recursion. -/
theorem sheafifiedTensorPieceIso_add_two_unit_of_eq (n : ℕ) (U : Cᵒᵖ)
    (z : (tensorAlgebraPiece ((n + 2 : ℕ) : ℤ) F.val).obj U)
    (x₀ : (tensorAlgebraPiece ((1 : ℕ) : ℤ) F.val).obj U)
    (y₀ : (tensorAlgebraPiece ((n + 1 : ℕ) : ℤ) F.val).obj U)
    (hz : Hom.app (tensorAlgebraPieceRecursion F.val n).hom U z = x₀ ⊗ₜ y₀) :
    (sheafifiedTensorPieceIso J F (n + 2)).hom.val.app U
        (Hom.app (sheafifyUnit (𝟙 (toRingCat J Osharp).obj)
            (tensorAlgebraPiece ((n + 2 : ℕ) : ℤ) F.val)) U z) =
      Hom.app ((PresheafOfModules.sheafificationAdjunction (R :=
          Stacks.SheafOfModules.Tensor.ringSheaf Osharp)
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf Osharp).obj)).unit.app
      (PresheafOfModules.tensorObj F.val (tensorPower J F (n + 1)).val)) U
        ((sheafifiedTensorPieceOneIso J F).hom.val.app U
            (Hom.app (sheafifyUnit (𝟙 (toRingCat J Osharp).obj)
              (tensorAlgebraPiece ((1 : ℕ) : ℤ) F.val)) U x₀) ⊗ₜ
          (sheafifiedTensorPieceIso J F (n + 1)).hom.val.app U
            (Hom.app (sheafifyUnit (𝟙 (toRingCat J Osharp).obj)
              (tensorAlgebraPiece ((n + 1 : ℕ) : ℤ) F.val)) U y₀)) :=
  SheafOfModules.tensorPowerSheafifyIso_add_two_unit J (𝟙 Osharp.obj)
    (Q := fun k : ℕ => tensorAlgebraPiece ((k : ℕ) : ℤ) F.val)
    (sheafifiedTensorPieceZeroIso J F) (sheafifiedTensorPieceOneIso J F)
    (tensorAlgebraPieceRecursion F.val) n U z x₀ y₀ hz

/-- `SheafOfModules.sheafifiedTensorPieceIso_add_two_unit_of_eq` on the section the tensor-power
recursion produces from a pure tensor. -/
theorem sheafifiedTensorPieceIso_add_two_unit (n : ℕ) (U : Cᵒᵖ)
    (x₀ : (tensorAlgebraPiece ((1 : ℕ) : ℤ) F.val).obj U)
    (y₀ : (tensorAlgebraPiece ((n + 1 : ℕ) : ℤ) F.val).obj U) :
    (sheafifiedTensorPieceIso J F (n + 2)).hom.val.app U
        (Hom.app (sheafifyUnit (𝟙 (toRingCat J Osharp).obj)
            (tensorAlgebraPiece ((n + 2 : ℕ) : ℤ) F.val)) U
          (Hom.app (tensorAlgebraPieceRecursion F.val n).inv U (x₀ ⊗ₜ y₀))) =
      Hom.app ((PresheafOfModules.sheafificationAdjunction (R :=
          Stacks.SheafOfModules.Tensor.ringSheaf Osharp)
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf Osharp).obj)).unit.app
      (PresheafOfModules.tensorObj F.val (tensorPower J F (n + 1)).val)) U
        ((sheafifiedTensorPieceOneIso J F).hom.val.app U
            (Hom.app (sheafifyUnit (𝟙 (toRingCat J Osharp).obj)
              (tensorAlgebraPiece ((1 : ℕ) : ℤ) F.val)) U x₀) ⊗ₜ
          (sheafifiedTensorPieceIso J F (n + 1)).hom.val.app U
            (Hom.app (sheafifyUnit (𝟙 (toRingCat J Osharp).obj)
              (tensorAlgebraPiece ((n + 1 : ℕ) : ℤ) F.val)) U y₀)) :=
  sheafifiedTensorPieceIso_add_two_unit_of_eq J F n U _ x₀ y₀
    (PresheafOfModules.iso_hom_app_inv_apply (tensorAlgebraPieceRecursion F.val n) U (x₀ ⊗ₜ y₀))

/-- The left-hand side of the `tensorPieceIso_mul_left` field of
`SheafOfModules.TensorExteriorSymmetricAlgebras` for this bundle: the product of the degree-one
generator of `s` with the degree-`n+1` section corresponding to `x`, carried into the
degree-`n+2` tensor power. -/
noncomputable def tensorMulLeftSection (n : ℕ) (U : Cᵒᵖ) (s : F.val.obj U)
    (x : (tensorPower J F (n + 1)).val.obj U) : (tensorPower J F (n + 2)).val.obj U :=
  (sheafifiedTensorPieceIso J F (n + 2)).hom.val.app U
    (Eq.mp (congrArg
        (fun k : ℤ => (((sheafifiedTensorAlgebra J F).piece k).val.obj U : Type w))
        (show 1 + ((n + 1 : ℕ) : ℤ) = ((n + 2 : ℕ) : ℤ) by omega))
      (((sheafifiedTensorAlgebra J F).mul 1 ((n + 1 : ℕ) : ℤ)).app U
        ((sheafifiedTensorGenerator J F).val.app U s)
        ((sheafifiedTensorPieceIso J F (n + 1)).inv.val.app U x)))

/-- `SheafOfModules.tensorMulLeftSection` written out. -/
theorem tensorMulLeftSection_def (n : ℕ) (U : Cᵒᵖ) (s : F.val.obj U)
    (x : (tensorPower J F (n + 1)).val.obj U) :
    tensorMulLeftSection J F n U s x =
      (sheafifiedTensorPieceIso J F (n + 2)).hom.val.app U
        (Eq.mp (congrArg
            (fun k : ℤ => (((sheafifiedTensorAlgebra J F).piece k).val.obj U : Type w))
            (show 1 + ((n + 1 : ℕ) : ℤ) = ((n + 2 : ℕ) : ℤ) by omega))
          (((sheafifiedTensorAlgebra J F).mul 1 ((n + 1 : ℕ) : ℤ)).app U
            ((sheafifiedTensorGenerator J F).val.app U s)
            ((sheafifiedTensorPieceIso J F (n + 1)).inv.val.app U x))) := rfl

/-- **The multiplication equation, for a local section of the tensor power that lifts** after
the degree-`n+1` identification to the unit image of a sectionwise section. -/
theorem tensorMulLeftSection_of_lift (n : ℕ) (U : Cᵒᵖ) (s : F.val.obj U)
    (x : (tensorPower J F (n + 1)).val.obj U)
    (y₀ : (tensorAlgebraPiece ((n + 1 : ℕ) : ℤ) F.val).obj U)
    (hx : (sheafifiedTensorPieceIso J F (n + 1)).inv.val.app U x =
      Hom.app (sheafifyUnit (𝟙 (toRingCat J Osharp).obj)
        (tensorAlgebraPiece ((n + 1 : ℕ) : ℤ) F.val)) U y₀) :
    tensorMulLeftSection J F n U s x =
      Hom.app ((PresheafOfModules.sheafificationAdjunction (R :=
          Stacks.SheafOfModules.Tensor.ringSheaf Osharp)
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf Osharp).obj)).unit.app
      (PresheafOfModules.tensorObj F.val (tensorPower J F (n + 1)).val)) U
        (s ⊗ₜ[Osharp.obj.obj U] x) := by
  have hmul : ((sheafifiedTensorAlgebra J F).mul 1 ((n + 1 : ℕ) : ℤ)).app U
      ((sheafifiedTensorGenerator J F).val.app U s)
      ((sheafifiedTensorPieceIso J F (n + 1)).inv.val.app U x) =
        Hom.app (sheafifyUnit (𝟙 (toRingCat J Osharp).obj)
            (tensorAlgebraPiece (1 + ((n + 1 : ℕ) : ℤ)) F.val)) U
          ((tensorAlgebraMul F.val 1 ((n + 1 : ℕ) : ℤ)).app U
            (Hom.app (tensorAlgebraGen F.val) U s) y₀) := by
    rw [sheafifiedTensorGenerator_apply, hx]
    exact (tensorAlgebraGradedAlgebra F.val).sheafify_mul_unit
      (𝟙 (toRingCat J Osharp).obj) 1 ((n + 1 : ℕ) : ℤ) U
      (Hom.app (tensorAlgebraGen F.val) U s) y₀
  rw [tensorMulLeftSection_def, hmul, sheafifiedTensorMul_gen_unit_eq_mp,
    sheafifiedTensorPieceIso_add_two_unit, sheafifiedTensorPieceOneIso_hom_unit_gen,
    ← hx, SheafOfModules.iso_hom_app_apply_inv]
  rfl

/-- `SheafOfModules.tensorMulLeftSection` commutes with restriction. -/
theorem tensorMulLeftSection_map (n : ℕ) (U V : Cᵒᵖ) (f : U ⟶ V) (s : F.val.obj U)
    (x : (tensorPower J F (n + 1)).val.obj U) :
    (tensorPower J F (n + 2)).val.map f (tensorMulLeftSection J F n U s x) =
      tensorMulLeftSection J F n V (F.val.map f s)
        ((tensorPower J F (n + 1)).val.map f x) := by
  rw [tensorMulLeftSection_def,
    ← PresheafOfModules.naturality_apply (sheafifiedTensorPieceIso J F (n + 2)).hom.val f,
    SheafOfModules.GradedAlgebra.map_eq_mp_mul,
    ← PresheafOfModules.naturality_apply (sheafifiedTensorGenerator J F).val f,
    ← PresheafOfModules.naturality_apply (sheafifiedTensorPieceIso J F (n + 1)).inv.val f]
  · exact (tensorMulLeftSection_def J F n V (F.val.map f s)
      ((tensorPower J F (n + 1)).val.map f x)).symm
  · omega

/-- The unit image of the pure tensor `s ⊗ₜ x` commutes with restriction. -/
theorem map_tensorSheafificationUnit_tmul (n : ℕ) (U V : Cᵒᵖ) (f : U ⟶ V) (s : F.val.obj U)
    (x : (tensorPower J F (n + 1)).val.obj U) :
    (tensorPower J F (n + 2)).val.map f
        (Hom.app ((PresheafOfModules.sheafificationAdjunction (R :=
            Stacks.SheafOfModules.Tensor.ringSheaf Osharp)
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf Osharp).obj)).unit.app
      (PresheafOfModules.tensorObj F.val (tensorPower J F (n + 1)).val)) U
          (s ⊗ₜ[Osharp.obj.obj U] x)) =
      Hom.app ((PresheafOfModules.sheafificationAdjunction (R :=
          Stacks.SheafOfModules.Tensor.ringSheaf Osharp)
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf Osharp).obj)).unit.app
      (PresheafOfModules.tensorObj F.val (tensorPower J F (n + 1)).val)) V
        (F.val.map f s ⊗ₜ[Osharp.obj.obj V] (tensorPower J F (n + 1)).val.map f x) := by
  refine (PresheafOfModules.naturality_apply
    ((PresheafOfModules.sheafificationAdjunction (R :=
        Stacks.SheafOfModules.Tensor.ringSheaf Osharp)
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf Osharp).obj)).unit.app
      (PresheafOfModules.tensorObj F.val (tensorPower J F (n + 1)).val)) f
    (s ⊗ₜ x)).symm.trans ?_
  exact congrArg
    (fun t => Hom.app ((PresheafOfModules.sheafificationAdjunction (R :=
        Stacks.SheafOfModules.Tensor.ringSheaf Osharp)
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf Osharp).obj)).unit.app
      (PresheafOfModules.tensorObj F.val (tensorPower J F (n + 1)).val)) V t)
    (PresheafOfModules.tensorObj_restrictₛₗ_tmul f s x)

/-- **The multiplication equation.** -/
theorem tensorMulLeftSection_eq (n : ℕ) (U : Cᵒᵖ) (s : F.val.obj U)
    (x : (tensorPower J F (n + 1)).val.obj U) :
    tensorMulLeftSection J F n U s x =
      Hom.app ((PresheafOfModules.sheafificationAdjunction (R :=
          Stacks.SheafOfModules.Tensor.ringSheaf Osharp)
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf Osharp).obj)).unit.app
      (PresheafOfModules.tensorObj F.val (tensorPower J F (n + 1)).val)) U
        (s ⊗ₜ[Osharp.obj.obj U] x) := by
  refine Stacks.eq_of_isSeparated (tensorPower J F (n + 2))
    (Stacks.liftSieve_mem (𝟙 (toRingCat J Osharp).obj)
      (tensorAlgebraPiece ((n + 1 : ℕ) : ℤ) F.val)
      ((sheafifiedTensorPieceIso J F (n + 1)).inv.val.app U x)) ?_
  rintro V g ⟨y₀, hy₀⟩
  have hy : Hom.app (sheafifyUnit (𝟙 (toRingCat J Osharp).obj)
      (tensorAlgebraPiece ((n + 1 : ℕ) : ℤ) F.val)) (op V) y₀ =
    ((sheafifiedTensorAlgebra J F).piece ((n + 1 : ℕ) : ℤ)).val.map g.op
      ((sheafifiedTensorPieceIso J F (n + 1)).inv.val.app U x) := hy₀
  rw [tensorMulLeftSection_map, map_tensorSheafificationUnit_tmul]
  refine tensorMulLeftSection_of_lift J F n (op V) (F.val.map g.op s)
    ((tensorPower J F (n + 1)).val.map g.op x) y₀ ?_
  rw [PresheafOfModules.naturality_apply (sheafifiedTensorPieceIso J F (n + 1)).inv.val g.op]
  exact hy.symm

/-- **The `tensorPieceIso_mul_left` field.** -/
theorem sheafifiedTensorPieceIso_mul_left (n : ℕ) (U : Cᵒᵖ) (s : F.val.obj U)
    (x : (tensorPower J F (n + 1)).val.obj U) :
    (sheafifiedTensorPieceIso J F (n + 2)).hom.val.app U
        (Eq.mp (congrArg
            (fun k : ℤ => (((sheafifiedTensorAlgebra J F).piece k).val.obj U : Type w))
            (show 1 + ((n + 1 : ℕ) : ℤ) = ((n + 2 : ℕ) : ℤ) by omega))
          (((sheafifiedTensorAlgebra J F).mul 1 ((n + 1 : ℕ) : ℤ)).app U
            ((sheafifiedTensorGenerator J F).val.app U s)
            ((sheafifiedTensorPieceIso J F (n + 1)).inv.val.app U x))) =
      Hom.app ((PresheafOfModules.sheafificationAdjunction (R :=
          Stacks.SheafOfModules.Tensor.ringSheaf Osharp)
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf Osharp).obj)).unit.app
      (PresheafOfModules.tensorObj F.val (tensorPower J F (n + 1)).val)) U
        (s ⊗ₜ[Osharp.obj.obj U] x) :=
  tensorMulLeftSection_eq J F n U s x

end MulLeft2

end SheafOfModules

end
