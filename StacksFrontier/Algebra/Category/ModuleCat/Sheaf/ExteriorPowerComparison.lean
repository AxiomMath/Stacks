module

public import Mathlib.LinearAlgebra.ExteriorPower.Basic
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PowerPresentationSequences
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SymmetricPowerComparison
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorAlgebraInhabitant
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorCoherence
public import StacksCore.Tactic.StacksAttribute

/-!
# Tag 01CG: the exterior power of a sheaf of modules is a sheafification

Let `(C, J)` be a site, `O♯` a sheaf of commutative rings on it and `M` a sheaf of modules over
the underlying sheaf of rings. Stacks Tag 01CG says that the degree-`n` exterior power `⋀ⁿ M` is
the **sheafification** of the presheaf of sectionwise exterior powers

`X ↦ ⋀ⁿ_{O♯(X)}(M(X))`,

the comparison being the map that wedges together degree-one generators.

`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SectionwiseAlgebras` builds that presheaf
(`PresheafOfModules.extPow`) and its graded algebra structure
(`PresheafOfModules.extPowGradedAlgebra`, with `PresheafOfModules.extPowGen` its square-zero
degree-one generator). What was missing, and is proved here, is the **comparison morphism** into
an arbitrary exterior algebra of `M` and the sheafification assertion itself: the comparison
becomes an isomorphism after sheafifying. `SheafOfModules.exteriorPower_isSheafification` is that
statement, and carries the tag.

This is the exterior counterpart of
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SymmetricPowerComparison`, whose
`SheafOfModules.symmetricPower_isSheafification` is the symmetric half of the same tag.

**Tag 01CG is covered by exactly that pair.** The source states two assertions and no more — that
`⋀ⁿ F` is the sheafification of `U ↦ ⋀ⁿ_{O(U)}(F(U))` and that `Symⁿ F` is the sheafification of
`U ↦ Symⁿ_{O(U)}(F(U))`. It says nothing about tensor powers. So with
`SheafOfModules.symmetricPower_isSheafification` already proved, the theorem below closes the
tag; the covering set is the two theorems, one clause each, and neither subsumes the other.

## Main definitions

* `Stacks.GradedAlgebra.GenSquareZero`: the presheaf-level form of
  `SheafOfModules.GradedAlgebra.SquareZero` — the image of a degree-one generator squares to
  zero. It is the exterior counterpart of `Stacks.GradedAlgebra.GenCommutes`.
* `Stacks.GradedAlgebra.extLiftTotal`: the ring homomorphism from the exterior algebra of the
  sections of `F` over `X` to the ungraded realization of a graded algebra, determined by a
  square-zero degree-one generator.
* `Stacks.GradedAlgebra.extCmpSections` and `Stacks.GradedAlgebra.extCmp`: **the comparison map
  on sections and the comparison morphism** `⋀ⁿ F ⟶ Pc n`, obtained by wedging generators.
* `SheafOfModules.GradedAlgebra.extPowCmp`: the comparison morphism for a *sheaf* of graded
  algebras. This is the declaration the implementation notes of
  `StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SymmetricPowerPresentation` and
  `StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FreePowerFree` record as not existing.
* `SheafOfModules.exteriorDesc` and `SheafOfModules.exteriorPieceIso`: the unital homomorphism
  of sheaves of graded algebras from the sheafified sectionwise exterior algebra of the sections
  of `M` to any exterior algebra of `M`, and its degreewise isomorphism.

## Main results

* `ExteriorAlgebra.powExtₛₗ`: two semilinear maps out of `⋀[R]^n M` which agree on wedges of
  vectors are equal. The `φ = RingHom.id` case is Mathlib's `exteriorPower.linearMap_ext`; the
  semilinear case is what the naturality of the comparison map needs, since a restriction map
  changes the base ring.
* `Stacks.GradedAlgebra.extCmpSections_ιMulti`: **the comparison map on a wedge of generators**
  is the ordered product of their images. By `ExteriorAlgebra.powExtₛₗ` this determines the map,
  and it is the equation Tag 01CG states the comparison by.
* `SheafOfModules.GradedAlgebra.IsExteriorAlgebra.comp_iso`: **the exterior-algebra universal
  property transports along an isomorphism of the sheaf of modules.** This is the exterior
  counterpart of `IsSymmetricAlgebra.comp_iso`, and it is needed for the same reason: the only
  exterior algebra this development constructs is one of a *sheafification*.
* `SheafOfModules.sheafifyUnit_extPow_ιMulti`: the sheafification unit of the presheaf of
  sectionwise exterior powers, on a wedge of degree-one generators, is the ordered product of
  the unit-images of those generators.
* `SheafOfModules.extPowCmp_eq_sheafifyUnit_comp`: **the comparison morphism factors as the
  sheafification unit followed by a degreewise isomorphism.** This is the identification that
  closes the tag.
* `SheafOfModules.isIso_sheafificationHomEquiv_symm_extPowCmp`: the comparison morphism becomes
  an isomorphism after sheafification.
* `SheafOfModules.exteriorPower_isSheafification`: **Tag 01CG for exterior powers.**

## Implementation notes

**Wedges, not products.** The symmetric file characterizes its comparison on
`∏ i, SymmetricAlgebra.ι (s i)`, a `Finset.prod`, which presupposes a commutative monoid.
`ExteriorAlgebra R M` is not one, so the spanning family here is `ExteriorAlgebra.ιMulti R n`,
whose value at `s` is the *ordered* product `(List.ofFn fun i => ι R (s i)).prod`, and the
subtype-valued `exteriorPower.ιMulti R n` is what the statements are phrased with. The ordering
matches `Stacks.GradedAlgebra.homogeneousProd`, which also multiplies on the right, so no
reordering appears anywhere below.

**Why `exists_liftRingHom` and not `ExteriorAlgebra.lift`.** The ungraded realization
`Stacks.GradedAlgebra.Total` is a ring with a compatible module structure over `O(X)`, but it
carries no `Algebra O(X)` instance — the compatibility is recorded as the two equations
`Stacks.GradedAlgebra.smul_mul_eq` and `mul_smul_eq`. `ExteriorAlgebra.lift` demands an algebra
target. `ExteriorAlgebra.exists_liftRingHom` (in
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorAlgebraInhabitant`) is exactly the universal
property for such a target, built by constructing `Algebra.ofModule` inside its proof; its
statement is existential so that the ad hoc algebra instance does not escape. `extLiftTotal`
names the map it produces, exactly as `Stacks.GradedAlgebra.liftTotal` names the one
`SymmetricAlgebra.liftComm` produces in the symmetric case.

**Transporting the universal property.** The only exterior algebra of a sheaf of modules this
development constructs is `SheafOfModules.sectionwiseExteriorAlgebra J a F`, which is an exterior
algebra of `(moduleSheafification J a).obj F`. Tag 01CG is about a sheaf of modules `M` given in
advance, and its presheaf of sectionwise exterior powers is formed from `M.val`, the sheaf's
*own* sections. Taking `a := 𝟙 O♯.obj` and `F := M.val` makes the two presheaves agree on the
nose, at the cost of an exterior algebra for `(moduleSheafification J (𝟙 O♯.obj)).obj M.val`;
`SheafOfModules.sheafifySectionsIso` is the isomorphism between them and
`IsExteriorAlgebra.comp_iso` is the transport. No sheafification morphism other than the
identity of the ring sheaf would do: `extPow n M.val` is a presheaf of `O♯`-modules, so only
`α = 𝟙 O♯.obj` sheafifies it to a sheaf of `O♯`-modules.

**Universes.** The ring universe and the module universe are *equal* in the sheaf half, which is
forced and not chosen: `SheafOfModules.sectionwiseExteriorAlgebra` and
`SheafOfModules.isExteriorAlgebra_sectionwiseExteriorAlgebra` are stated for
`GradedAlgebra.{w, w}`, so the exterior algebra this file compares against exists only in the
equal-universe case. The presheaf-level comparison `Stacks.GradedAlgebra.extCmp` and its
equations hold for modules in `max w a`; it is only the isomorphism assertion that is pinned.
Tag 01CG is stated in the equal-universe case, so nothing the source says is narrowed.

**Numerals in degrees.** No statement below writes `extPow 1 F` or any other numeral-indexed
sectionwise exterior power. `ExteriorAlgebra` is a `CliffordAlgebra` quotient of
`TensorAlgebra`, so asking the elaborator to identify `extPow 1 F` with
`Stacks.GradedAlgebra.extendFamily (fun k => extPow k F) 1` sends `whnf` through
`Submodule.mul`/`span` and the quotient and exhausts the heartbeat limit *in the statement*. The
degrees therefore stay variables, and the degree-one equations are obtained from
`Stacks.GradedAlgebra.sheafifyGen_unit` with no type ascription at all, so the library's own
spelling of the degree-one piece is the one that travels.

## References

* [Stacks Project, Tag 01CG](https://stacks.math.columbia.edu/tag/01CG)
* [Stacks Project, Section 17.21](https://stacks.math.columbia.edu/tag/01CF)
* [Stacks Project, Tag 0FQW](https://stacks.math.columbia.edu/tag/0FQW)
-/

@[expose] public section

open CategoryTheory Opposite CategoryTheory.Sheaf

universe v u w a

/-! ### Semilinear extensionality for the exterior power -/

namespace ExteriorAlgebra

/-- **Two semilinear maps out of `⋀[R]^n M` which agree on wedges of vectors are equal.**

Mathlib's `exteriorPower.linearMap_ext` is the case `φ = RingHom.id`. The semilinear case is what
the naturality of the comparison map needs: a restriction map of a presheaf of modules changes
the base ring, so the two composites being compared are semilinear over the restriction map of
the ring presheaf and not linear over a fixed ring. -/
theorem powExtₛₗ {R : Type*} [CommRing R] {S : Type*} [CommRing S] {M : Type*} [AddCommGroup M]
    [Module R M] {N : Type*} [AddCommGroup N] [Module S N] {φ : R →+* S} {n : ℕ}
    {f g : (⋀[R]^n M) →ₛₗ[φ] N}
    (h : ∀ s : Fin n → M, f (exteriorPower.ιMulti R n s) = g (exteriorPower.ιMulti R n s)) :
    f = g := by
  refine LinearMap.ext fun x => ?_
  have hx : x ∈ Submodule.span R (Set.range (exteriorPower.ιMulti R n (M := M))) := by
    rw [exteriorPower.ιMulti_span]
    exact Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem w hw => obtain ⟨s, rfl⟩ := hw; exact h s
  | zero => rw [map_zero, map_zero]
  | add p q _ _ hp hq => rw [map_add, map_add, hp, hq]
  | smul r p _ hp => rw [map_smulₛₗ, map_smulₛₗ, hp]

/-- **Peeling the last factor off a wedge.** Mathlib's `ExteriorAlgebra.ιMulti_succ_apply` peels
from the left, while `Stacks.GradedAlgebra.homogeneousProd` multiplies on the right; this is the
right-handed form, and it is what matches the recursion of `homogeneousProd` with no reordering.
-/
theorem ιMulti_succ_last {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]
    (n : ℕ) (s : Fin (n + 1) → M) :
    ιMulti R (n + 1) s = ιMulti R n (fun i => s i.castSucc) * ι R (s (Fin.last n)) := by
  rw [ιMulti_apply, ιMulti_apply, List.ofFn_succ', List.concat_eq_append, List.prod_append,
    List.prod_singleton]

end ExteriorAlgebra

/-! ### The comparison with the degree-`n` piece of a graded algebra -/

namespace Stacks.GradedAlgebra

section Comparison

variable {C : Type u} [Category.{v} C] {O : Cᵒᵖ ⥤ CommRingCat.{w}}
  {Pc : ℤ → PresheafOfModules.{max w a} (O ⋙ forget₂ _ RingCat)}
  (A : Stacks.GradedAlgebra Pc) {F : PresheafOfModules.{max w a} (O ⋙ forget₂ _ RingCat)}
  (gen : F ⟶ Pc 1)

/-- The degree-one local sections in the image of a generator `F ⟶ Pc 1` square to zero. This is
the presheaf-level form of `SheafOfModules.GradedAlgebra.SquareZero`, and the exterior
counterpart of `Stacks.GradedAlgebra.GenCommutes`. -/
def GenSquareZero : Prop :=
  ∀ (X : Cᵒᵖ) (x : F.obj X), (A.mul 1 1).app X (gen.app X x) (gen.app X x) = 0

/-- The exterior counterpart of `Stacks.GradedAlgebra.genLin_mul_comm`: a square-zero degree-one
generator squares to zero in the ungraded realization, which is the side condition
`ExteriorAlgebra.exists_liftRingHom` consumes. -/
theorem genLin_sq_zero (hs : A.GenSquareZero gen) (X : Cᵒᵖ) (m : F.obj X) :
    A.genLin gen X m * A.genLin gen X m = 0 := by
  rw [genLin_apply, A.incl_mul_incl, hs X m, A.incl_zero]

/-- The ring homomorphism from the exterior algebra of the sections of `F` over `X` to the
ungraded realization of the graded algebra, determined by a square-zero degree-one generator.

This is `ExteriorAlgebra.exists_liftRingHom` rather than `ExteriorAlgebra.lift`: the ungraded
realization carries no `Algebra` instance, only the two `smul`-multiplication compatibilities. -/
noncomputable def extLiftTotal (hs : A.GenSquareZero gen) (X : Cᵒᵖ) :
    ExteriorAlgebra ((O ⋙ forget₂ _ RingCat).obj X) (F.obj X) →+* A.Total X :=
  (ExteriorAlgebra.exists_liftRingHom (fun r x y => A.smul_mul_eq (X := X) r x y)
    (fun r x y => A.mul_smul_eq (X := X) r x y) (A.genLin gen X)
    (A.genLin_sq_zero gen hs X)).choose

/-- `extLiftTotal` sends a degree-one element `ι m` to the image of the generator at `m`. -/
@[simp]
theorem extLiftTotal_ι (hs : A.GenSquareZero gen) (X : Cᵒᵖ) (m : F.obj X) :
    A.extLiftTotal gen hs X (ExteriorAlgebra.ι _ m) = A.incl 1 (gen.app X m) :=
  (ExteriorAlgebra.exists_liftRingHom (fun r x y => A.smul_mul_eq (X := X) r x y)
    (fun r x y => A.mul_smul_eq (X := X) r x y) (A.genLin gen X)
    (A.genLin_sq_zero gen hs X)).choose_spec.1 m

/-- `extLiftTotal` commutes with scalar multiplication by sections of `O`. -/
theorem extLiftTotal_smul (hs : A.GenSquareZero gen) (X : Cᵒᵖ)
    (r : (O ⋙ forget₂ _ RingCat).obj X)
    (z : ExteriorAlgebra ((O ⋙ forget₂ _ RingCat).obj X) (F.obj X)) :
    A.extLiftTotal gen hs X (r • z) = r • A.extLiftTotal gen hs X z :=
  (ExteriorAlgebra.exists_liftRingHom (fun r x y => A.smul_mul_eq (X := X) r x y)
    (fun r x y => A.mul_smul_eq (X := X) r x y) (A.genLin gen X)
    (A.genLin_sq_zero gen hs X)).choose_spec.2 r z

/-- The value of `extLiftTotal` on a wedge of degree-one generators is the ordered product of
their images in the ungraded realization. Since wedges span every exterior power, this pins
`extLiftTotal` on all of them. -/
theorem extLiftTotal_ιMulti (hs : A.GenSquareZero gen) (X : Cᵒᵖ) (n : ℕ) (s : Fin n → F.obj X) :
    A.extLiftTotal gen hs X (ExteriorAlgebra.ιMulti _ n s) =
      (List.ofFn fun i => A.incl 1 (gen.app X (s i))).prod := by
  rw [ExteriorAlgebra.ιMulti_apply, map_list_prod (A.extLiftTotal gen hs X), List.map_ofFn]
  exact congrArg (fun h : Fin n → A.Total X => (List.ofFn h).prod)
    (funext fun i => A.extLiftTotal_ι gen hs X (s i))

/-- **The comparison map on sections.** The `n`-th exterior power of the sections of `F` over `X`
maps to the degree-`n` sections of the graded algebra, by wedging together the generators. -/
noncomputable def extCmpSections (hs : A.GenSquareZero gen) (n : ℕ) (X : Cᵒᵖ) :
    (⋀[(O ⋙ forget₂ _ RingCat).obj X]^n (F.obj X)) →ₗ[(O ⋙ forget₂ _ RingCat).obj X]
      (Pc (n : ℤ)).obj X :=
  (A.proj X (n : ℤ)).comp
    (({ toFun := fun z => A.extLiftTotal gen hs X z
        map_add' := fun z z' => map_add (A.extLiftTotal gen hs X) z z'
        map_smul' := fun r z => A.extLiftTotal_smul gen hs X r z } :
          ExteriorAlgebra ((O ⋙ forget₂ _ RingCat).obj X) (F.obj X) →ₗ[(O ⋙ forget₂ _
            RingCat).obj X] A.Total X).comp
      (⋀[(O ⋙ forget₂ _ RingCat).obj X]^n (F.obj X)).subtype)

/-- `extCmpSections` is the degree-`n` projection of `extLiftTotal`. -/
theorem extCmpSections_apply (hs : A.GenSquareZero gen) (n : ℕ) (X : Cᵒᵖ)
    (z : ⋀[(O ⋙ forget₂ _ RingCat).obj X]^n (F.obj X)) :
    A.extCmpSections gen hs n X z = A.proj X (n : ℤ) (A.extLiftTotal gen hs X z) := rfl

/-- **The comparison map on a wedge of generators.** This is the equation Tag 01CG states the
comparison by, and by `ExteriorAlgebra.powExtₛₗ` it determines the map. -/
theorem extCmpSections_ιMulti (hs : A.GenSquareZero gen) (n : ℕ) (X : Cᵒᵖ)
    (s : Fin n → F.obj X) :
    A.extCmpSections gen hs n X (exteriorPower.ιMulti _ n s) =
      A.homogeneousProd X n fun i => gen.app X (s i) := by
  rw [extCmpSections_apply]
  refine Eq.trans (congrArg (fun z => A.proj X (n : ℤ) (A.extLiftTotal gen hs X z))
    (exteriorPower.ιMulti_apply_coe _ n s)) ?_
  rw [A.extLiftTotal_ιMulti gen hs X n s,
    ← A.incl_homogeneousProd X n fun i => gen.app X (s i), A.proj_incl]

/-- The comparison map on sections commutes with restriction. -/
theorem extCmpSections_naturality (hs : A.GenSquareZero gen) (n : ℕ) {X Y : Cᵒᵖ} (f : X ⟶ Y)
    (z : ⋀[(O ⋙ forget₂ _ RingCat).obj X]^n (F.obj X)) :
    (Pc (n : ℤ)).map f (A.extCmpSections gen hs n X z) =
      A.extCmpSections gen hs n Y
        (ExteriorAlgebra.powMapₛₗ n ((O ⋙ forget₂ _ RingCat).map f).hom (F.restrictₛₗ f) z) := by
  have key : ((Pc (n : ℤ)).restrictₛₗ f).comp (A.extCmpSections gen hs n X) =
      (A.extCmpSections gen hs n Y).comp
        (ExteriorAlgebra.powMapₛₗ n ((O ⋙ forget₂ _ RingCat).map f).hom (F.restrictₛₗ f)) := by
    refine ExteriorAlgebra.powExtₛₗ fun s => ?_
    show (Pc (n : ℤ)).map f (A.extCmpSections gen hs n X _) =
      A.extCmpSections gen hs n Y (ExteriorAlgebra.powMapₛₗ n _ (F.restrictₛₗ f) _)
    rw [extCmpSections_ιMulti, A.homogeneousProd_naturality f n,
      ExteriorAlgebra.powMapₛₗ_ιMulti, extCmpSections_ιMulti]
    exact congrArg (A.homogeneousProd Y n)
      (funext fun i => (PresheafOfModules.naturality_apply gen f (s i)).symm)
  exact DFunLike.congr_fun key z

/-- **The comparison morphism.** The presheaf of sectionwise `n`-th exterior powers of `F` maps
to the degree-`n` piece of a graded algebra carrying a square-zero degree-one generator
`F ⟶ Pc 1`, by wedging together the generators. -/
noncomputable def extCmp (hs : A.GenSquareZero gen) (n : ℕ) :
    PresheafOfModules.extPow n F ⟶ Pc (n : ℤ) where
  app X := ModuleCat.ofHom (A.extCmpSections gen hs n X)
  naturality f := ModuleCat.hom_ext (LinearMap.ext fun z =>
    (A.extCmpSections_naturality gen hs n f z).symm)

/-- The component of `extCmp` at `X` is `extCmpSections` applied to the corresponding sectionwise
exterior power. -/
@[simp]
theorem extCmp_app (hs : A.GenSquareZero gen) (n : ℕ) (X : Cᵒᵖ)
    (z : (PresheafOfModules.extPow n F).obj X) :
    (A.extCmp gen hs n).app X z = A.extCmpSections gen hs n X
      (PresheafOfModules.extPowSections n F X z) := rfl

end Comparison

end Stacks.GradedAlgebra

namespace SheafOfModules.GradedAlgebra

/-! ### The comparison for a sheaf of graded algebras -/

section Sheaf

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {O : Cᵒᵖ ⥤ CommRingCat.{w}} {hO : Presheaf.IsSheaf J (O ⋙ forget₂ CommRingCat RingCat)}
  {M : SheafOfModules.{max w a} (ringSheafOfIsSheaf hO)}
  (A : SheafOfModules.GradedAlgebra.{w, max w a} (ringSheafOfIsSheaf hO)) (gen : M ⟶ A.piece 1)

/-- **The comparison morphism for a sheaf of graded algebras.** The presheaf of sectionwise
`n`-th exterior powers of `M` maps to the degree-`n` piece of a sheaf of graded algebras carrying
a square-zero degree-one generator `M ⟶ A.piece 1`.

This is `Stacks.GradedAlgebra.extCmp` read through
`SheafOfModules.GradedAlgebra.toPresheafGradedAlgebra`: a sheaf of graded algebras is in
particular a graded algebra of presheaves of modules, and the comparison does not see the sheaf
conditions. -/
noncomputable def extPowCmp (hgen : SquareZero gen) (n : ℕ) :
    PresheafOfModules.extPow n M.val ⟶ (A.piece (n : ℤ)).val :=
  A.toPresheafGradedAlgebra.extCmp gen.val (fun X x => hgen X x) n

/-- The comparison morphism of `extPowCmp` sends a wedge of `n` degree-one generators to their
ordered product in the graded algebra, read in the ungraded realization. By
`ExteriorAlgebra.powExtₛₗ` this determines the morphism. -/
theorem incl_extPowCmp_ιMulti (hgen : SquareZero gen) (n : ℕ)
    (X : Cᵒᵖ) (s : Fin n → M.val.obj X) (z : (PresheafOfModules.extPow n M.val).obj X)
    (hz : (PresheafOfModules.extPowSections n M.val X z :
        ExteriorAlgebra ((O ⋙ forget₂ _ RingCat).obj X) (M.val.obj X)) =
      ExteriorAlgebra.ιMulti ((O ⋙ forget₂ _ RingCat).obj X) n s) :
    A.toPresheafGradedAlgebra.incl (n : ℤ) ((A.extPowCmp gen hgen n).app X z) =
      (List.ofFn fun i => A.toPresheafGradedAlgebra.incl 1 (gen.val.app X (s i))).prod := by
  have hzeq : z = exteriorPower.ιMulti ((O ⋙ forget₂ _ RingCat).obj X) n s :=
    Subtype.ext (hz.trans (exteriorPower.ιMulti_apply_coe _ n s).symm)
  rw [hzeq]
  refine Eq.trans (congrArg (A.toPresheafGradedAlgebra.incl (n : ℤ))
    (Stacks.GradedAlgebra.extCmpSections_ιMulti A.toPresheafGradedAlgebra gen.val
      (fun X x => hgen X x) n X s)) ?_
  exact Stacks.GradedAlgebra.incl_homogeneousProd A.toPresheafGradedAlgebra X n _

end Sheaf

-- Neither `squareZero_comp` -- a square-zero degree-one generator stays square-zero when
-- restricted along a morphism of sheaves of modules -- nor
-- `IsExteriorAlgebra.comp_iso`, which transports the exterior-algebra universal property along
-- an isomorphism of the sheaf of modules, is declared here. Both are
-- `SheafOfModules.GradedAlgebra.*` in
-- `StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PowerPresentationSequences`, which this file
-- imports. This file originally declared a second copy of each, which would have made the two
-- modules impossible to co-import; that collision is invisible to a per-module build and only
-- shows up when a third file imports both, as the umbrella does. The same note appears in
-- `SymmetricPowerComparison` about `pairwiseCommutes_comp`.

end SheafOfModules.GradedAlgebra

namespace SheafOfModules

/-! ### The sheafification unit on wedges of degree-one generators -/

section UnitProd

open PresheafOfModules CategoryTheory.Sheaf

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  {O : Cᵒᵖ ⥤ CommRingCat.{w}} {Osharp : Sheaf J CommRingCat.{w}} (a : O ⟶ Osharp.obj)
  [Presheaf.IsLocallyInjective J (toRingCatMap J a)]
  [Presheaf.IsLocallySurjective J (toRingCatMap J a)]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]
  (F : PresheafOfModules.{w} (O ⋙ forget₂ CommRingCat RingCat))

/-- **The sheafification unit of the presheaf of sectionwise exterior powers, on a wedge of
degree-one generators.** The unit-image of `s₀ ∧ ⋯ ∧ s_{n-1}` is the ordered product, in the
sheafified sectionwise exterior algebra, of the unit-images of those generators under the
degree-one generator of that algebra.

Since wedges of `n` vectors span the `n`-th exterior power
(`ExteriorAlgebra.ιMulti_span_fixedDegree`, and `ExteriorAlgebra.powExtₛₗ` in the form used
here), this determines the sheafification unit in degree `n`. -/
theorem sheafifyUnit_extPow_ιMulti (n : ℕ) (X : Cᵒᵖ) (s : Fin n → F.obj X) :
    Hom.app (sheafifyUnit (toRingCatMap J a) (extPow n F)) X
        (exteriorPower.ιMulti ((O ⋙ forget₂ _ RingCat).obj X) n s) =
      (sectionwiseExteriorAlgebra J a F).toPresheafGradedAlgebra.homogeneousProd
        X n fun i => (sectionwiseExteriorAlgebraGen J a F).val.app X
          (Hom.app (sheafifyUnit (toRingCatMap J a) F) X (s i)) := by
  induction n with
  | zero =>
      refine congrArg (fun z => Hom.app (sheafifyUnit (toRingCatMap J a) (extPow 0 F)) X z)
        (Subtype.ext ?_)
      exact (exteriorPower.ιMulti_apply_coe _ 0 s).trans
        (ExteriorAlgebra.ιMulti_zero_apply s)
  | succ n ih =>
      -- The coercion identities are combined with `congrArg₂`/`Eq.trans`, never with `rw`. A
      -- section of `extPow 1 F` and an element of `⋀[O X]^1 (F X)` are definitionally but not
      -- syntactically the same type, so the goal below is not type-correct at `implicit`
      -- transparency: `rw` refuses to abstract either side, and a type ascription cannot even be
      -- written, since Lean will not insert the subtype coercion through the unreduced spelling.
      -- `exact` is defeq tolerant and bridges it in one step.
      have hcoe : extPowMulApp F n 1 X
            (exteriorPower.ιMulti ((O ⋙ forget₂ _ RingCat).obj X) n fun i => s i.castSucc)
            (Hom.app (extPowGen F) X (s (Fin.last n))) =
          (exteriorPower.ιMulti ((O ⋙ forget₂ _ RingCat).obj X) (n + 1) s) := by
        refine Subtype.ext ((extPowMulSections_coe F n 1 X _ _).trans ?_)
        refine Eq.trans ?_ (exteriorPower.ιMulti_apply_coe _ (n + 1) s).symm
        exact (congrArg₂ (· * ·) (exteriorPower.ιMulti_apply_coe _ n _)
          (extPowGen_coe F X (s (Fin.last n)))).trans
          (ExteriorAlgebra.ιMulti_succ_last n s).symm
      have hlast := (extPowGradedAlgebra F).extend.sheafifyGen_unit (toRingCatMap J a)
        (extPowGen F) X (s (Fin.last n))
      refine Eq.trans (congrArg (fun z =>
        Hom.app (sheafifyUnit (toRingCatMap J a) (extPow (n + 1) F)) X z) hcoe.symm) ?_
      refine Eq.trans ((extPowGradedAlgebra F).extend.sheafify_mul_unit
        (toRingCatMap J a) (n : ℤ) 1 X _ _).symm ?_
      exact GradedAlgebra.mul_congr (n : ℤ) 1 X (ih fun i => s i.castSucc) hlast.symm

end UnitProd

/-! ### The comparison morphism of Tag 01CG becomes an isomorphism -/

section Sheafification

open PresheafOfModules CategoryTheory.Sheaf

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  {Osharp : Sheaf J CommRingCat.{w}}
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]
  (M : SheafOfModules.{w} (toRingCat J Osharp))
  (A : GradedAlgebra.{w, w} (toRingCat J Osharp)) (gen : M ⟶ A.piece 1)
  (hgen : GradedAlgebra.SquareZero gen)
  (hA : GradedAlgebra.IsExteriorAlgebra A gen)

/-- **The comparison homomorphism of sheaves of graded algebras** from the sheafified sectionwise
exterior algebra of the sections of `M` to an exterior algebra `A` of `M`. It is the unique
unital homomorphism carrying one degree-one generator to the other, the generator of `A` being
read on `(moduleSheafification J (𝟙 O♯.obj)).obj M.val` through `sheafifySectionsIso`. -/
noncomputable def exteriorDesc :
    GradedAlgebra.UnitalHom (sectionwiseExteriorAlgebra J (𝟙 Osharp.obj) M.val) A :=
  (isExteriorAlgebra_sectionwiseExteriorAlgebra J (𝟙 Osharp.obj) M.val).desc A
    ((sheafifySectionsIso M).hom ≫ gen)
    (hA.comp_iso (sheafifySectionsIso M).hom (sheafifySectionsIso M).isIso_hom).1

/-- **The degreewise isomorphism** between the sheafified sectionwise exterior powers of the
sections of `M` and the homogeneous pieces of an exterior algebra of `M`: two sheaves of graded
algebras universal for square-zeroness of the degree-one generator are isomorphic in every
degree. -/
noncomputable def exteriorPieceIso (n : ℤ) :
    (sectionwiseExteriorAlgebra J (𝟙 Osharp.obj) M.val).piece n ≅ A.piece n :=
  (isExteriorAlgebra_sectionwiseExteriorAlgebra J (𝟙 Osharp.obj) M.val).pieceIso
    (hA.comp_iso (sheafifySectionsIso M).hom (sheafifySectionsIso M).isIso_hom) n

/-- The forward map of `exteriorPieceIso` in degree `n` is the degree-`n` component of
`exteriorDesc`. -/
theorem exteriorPieceIso_hom (n : ℤ) :
    (exteriorPieceIso M A gen hA n).hom = (exteriorDesc M A gen hA).app n := rfl

/-- The comparison homomorphism carries the degree-one generator of the sheafified sectionwise
exterior algebra to the degree-one generator of `A`, on the unit-image of a local section. -/
theorem exteriorDesc_gen (X : Cᵒᵖ) (m : M.val.obj X) :
    ((exteriorDesc M A gen hA).app 1).val.app X
        ((sectionwiseExteriorAlgebraGen J (𝟙 Osharp.obj) M.val).val.app X
          (Hom.app (sheafifyUnit (toRingCatMap J (𝟙 Osharp.obj)) M.val) X m)) =
      gen.val.app X m :=
  (SheafOfModules.hom_congr_app_apply
    ((isExteriorAlgebra_sectionwiseExteriorAlgebra J (𝟙 Osharp.obj) M.val).desc_extends A
      ((sheafifySectionsIso M).hom ≫ gen)
      (hA.comp_iso (sheafifySectionsIso M).hom (sheafifySectionsIso M).isIso_hom).1) X _).trans
    (congrArg (fun z => gen.val.app X z) (sheafifySectionsIso_hom_unit M X m))

/-- **The comparison morphism of Tag 01CG is the sheafification unit followed by a degreewise
isomorphism.**

Both sides are determined by their values on wedges of `n` degree-one generators
(`ExteriorAlgebra.powExtₛₗ`). There the left-hand side is the ordered product of the images of
those generators under the generator of `A`
(`Stacks.GradedAlgebra.extCmpSections_ιMulti`), and the right-hand side is the image under the
comparison homomorphism of the ordered product of the unit-images
(`SheafOfModules.sheafifyUnit_extPow_ιMulti`), which is the same ordered product because a
unital homomorphism preserves ordered products
(`SheafOfModules.GradedAlgebra.UnitalHom.app_homogeneousProd`) and carries one generator to the
other (`SheafOfModules.exteriorDesc_gen`). -/
theorem extPowCmp_eq_sheafifyUnit_comp (n : ℕ) :
    A.extPowCmp (hO := (toRingCat J Osharp).property) gen hgen n =
      sheafifyUnit (toRingCatMap J (𝟙 Osharp.obj)) (extPow n M.val) ≫
        (SheafOfModules.forget (toRingCat J Osharp)).map
          (exteriorPieceIso M A gen hA (n : ℤ)).hom := by
  refine PresheafOfModules.hom_ext fun X => ModuleCat.hom_ext ?_
  refine ExteriorAlgebra.powExtₛₗ fun s => ?_
  refine Eq.trans (Stacks.GradedAlgebra.extCmpSections_ιMulti A.toPresheafGradedAlgebra gen.val
    (fun X x => hgen X x) n X s) ?_
  refine Eq.symm (Eq.trans (congrArg
    (fun z => ((exteriorDesc M A gen hA).app (n : ℤ)).val.app X z)
    (sheafifyUnit_extPow_ιMulti (𝟙 Osharp.obj) M.val n X s)) ?_)
  refine Eq.trans (GradedAlgebra.UnitalHom.app_homogeneousProd
    (exteriorDesc M A gen hA) X n _) ?_
  exact congrArg (A.toPresheafGradedAlgebra.homogeneousProd X n)
    (funext fun i => exteriorDesc_gen M A gen hA X (s i))

include hA in
/-- **The comparison morphism of Tag 01CG becomes an isomorphism after sheafification.** This is
the third and last conjunct of `SheafOfModules.exteriorPower_isSheafification` below — the
sheafification clause, which is the whole content of Tag 01CG's exterior assertion: the presheaf
of sectionwise `n`-th exterior powers of the sections of `M` has the `n`-th exterior power of `M`
as its sheafification, with the comparison morphism as the sheafification map. (Tag 01CG itself
states two assertions and no more, the exterior one and the symmetric one; "third" here counts
conjuncts of the formalized statement, not assertions of the source.)

It follows from `SheafOfModules.extPowCmp_eq_sheafifyUnit_comp`: a sheafification unit is locally
bijective, an isomorphism is locally bijective, and a locally bijective morphism into a sheaf of
modules exhibits the latter as the sheafification of its source. -/
theorem isIso_sheafificationHomEquiv_symm_extPowCmp (n : ℕ) :
    IsIso ((sheafificationHomEquiv (𝟙 (toRingCat J Osharp).obj)).symm
      (A.extPowCmp (hO := (toRingCat J Osharp).property) gen hgen n)) := by
  have hfac : (toPresheaf (toRingCat J Osharp).obj).map
        (A.extPowCmp (hO := (toRingCat J Osharp).property) gen hgen n) =
      (toPresheaf (toRingCat J Osharp).obj).map
          (sheafifyUnit (toRingCatMap J (𝟙 Osharp.obj)) (extPow n M.val)) ≫
        (toPresheaf (toRingCat J Osharp).obj).map
          ((SheafOfModules.forget (toRingCat J Osharp)).map
            (exteriorPieceIso M A gen hA (n : ℤ)).hom) :=
    (congrArg (fun h => (toPresheaf (toRingCat J Osharp).obj).map h)
      (extPowCmp_eq_sheafifyUnit_comp M A gen hgen hA n)).trans
      ((toPresheaf (toRingCat J Osharp).obj).map_comp _ _)
  have hinj : Presheaf.IsLocallyInjective J ((toPresheaf (toRingCat J Osharp).obj).map
      ((SheafOfModules.forget (toRingCat J Osharp)).map
        (exteriorPieceIso M A gen hA (n : ℤ)).hom)) := inferInstance
  have hsurj : Presheaf.IsLocallySurjective J ((toPresheaf (toRingCat J Osharp).obj).map
      ((SheafOfModules.forget (toRingCat J Osharp)).map
        (exteriorPieceIso M A gen hA (n : ℤ)).hom)) := inferInstance
  exact Stacks.TensorCoherence.isIso_sheafificationHomEquiv_symm _ _
    (Stacks.TensorCoherence.isLocallyInjective_of_fac J _ hfac.symm inferInstance hinj)
    (Stacks.TensorCoherence.isLocallySurjective_of_fac J _ hfac.symm inferInstance hsurj)

/-- **Every sheaf of modules carries an exterior algebra**: the sheafified sectionwise exterior
algebra of the sections of `M`, with its degree-one generator read on `M` through
`SheafOfModules.sheafifySectionsIso`, is an exterior algebra of `M`. -/
theorem isExteriorAlgebra_sectionwiseExteriorAlgebra_val :
    GradedAlgebra.IsExteriorAlgebra (sectionwiseExteriorAlgebra J (𝟙 Osharp.obj) M.val)
      ((sheafifySectionsIso M).inv ≫
        sectionwiseExteriorAlgebraGen J (𝟙 Osharp.obj) M.val) :=
  (isExteriorAlgebra_sectionwiseExteriorAlgebra J (𝟙 Osharp.obj) M.val).comp_iso
    (sheafifySectionsIso M).inv (sheafifySectionsIso M).isIso_inv

include hgen hA in
/-- For a sheaf of modules `M` on a site with a sheaf of
commutative rings `O♯`, and an exterior algebra `A` of `M` in the sense of Section 17.21, the
degree-`n` exterior power `A.piece n` of `M` is the sheafification of the presheaf
`X ↦ ⋀ⁿ_{O♯(X)}(M(X))`.

The presheaf is exhibited together with the sectionwise identification of its sections with
`⋀ⁿ_{O♯(X)}(M(X))` and the comparison morphism to `A.piece n`; the two equation families fix the
restriction maps and the comparison morphism on wedges of degree-one generators, and the last
conjunct is the sheafification assertion. -/
@[stacks 01CG "exterior_power_sheafification: the exterior assertion, that `⋀ⁿ M` is the \
sheafification of `X ↦ ⋀ⁿ(M(X))`, with the comparison pinned on wedges of degree-one local \
sections. The symmetric assertion is `SheafOfModules.symmetricPower_isSheafification`; the tag \
states those two and nothing else, so that pair is its covering set."]
theorem exteriorPower_isSheafification (n : ℕ) :
    ∃ P : PresheafOfModules.{w} (toRingCat J Osharp).obj,
      ∃ e : ∀ X : Cᵒᵖ, P.obj X ≃ₗ[(toRingCat J Osharp).obj.obj X]
          ⋀[(toRingCat J Osharp).obj.obj X]^n (M.val.obj X),
        ∃ cmp : P ⟶ (SheafOfModules.forget (toRingCat J Osharp)).obj (A.piece (n : ℤ)),
          (∀ (X Y : Cᵒᵖ) (f : X ⟶ Y) (s : Fin n → M.val.obj X)
              (x : ⋀[(toRingCat J Osharp).obj.obj X]^n (M.val.obj X))
              (y : ⋀[(toRingCat J Osharp).obj.obj Y]^n (M.val.obj Y)),
            ((x : ExteriorAlgebra ((toRingCat J Osharp).obj.obj X) (M.val.obj X)) =
                ExteriorAlgebra.ιMulti ((toRingCat J Osharp).obj.obj X) n s) →
            ((y : ExteriorAlgebra ((toRingCat J Osharp).obj.obj Y) (M.val.obj Y)) =
                ExteriorAlgebra.ιMulti ((toRingCat J Osharp).obj.obj Y) n
                  fun i => M.val.map f (s i)) →
            e Y (P.map f ((e X).symm x)) = y) ∧
          (∀ (X : Cᵒᵖ) (s : Fin n → M.val.obj X)
              (x : ⋀[(toRingCat J Osharp).obj.obj X]^n (M.val.obj X)),
            ((x : ExteriorAlgebra ((toRingCat J Osharp).obj.obj X) (M.val.obj X)) =
                ExteriorAlgebra.ιMulti ((toRingCat J Osharp).obj.obj X) n s) →
            Hom.app cmp X ((e X).symm x) =
              A.toPresheafGradedAlgebra.homogeneousProdLeft X n
                fun i => gen.val.app X (s i)) ∧
          IsIso ((sheafificationHomEquiv (𝟙 (toRingCat J Osharp).obj)).symm cmp) := by
  refine ⟨extPow n M.val, extPowSections n M.val, A.extPowCmp gen hgen n,
    fun X Y f s x y hx hy => ?_, fun X s x hx => ?_,
    isIso_sheafificationHomEquiv_symm_extPowCmp M A gen hgen hA n⟩
  · refine Subtype.ext (Eq.trans ?_ hy.symm)
    refine Eq.trans (extPowSections_map n M.val f ((extPowSections n M.val X).symm x)) ?_
    refine Eq.trans (congrArg (ExteriorAlgebra.mapₛₗ
      ((Osharp.obj ⋙ forget₂ _ RingCat).map f).hom (M.val.restrictₛₗ f)) hx) ?_
    exact ExteriorAlgebra.mapₛₗ_ιMulti _ _ n s
  · refine Eq.trans (congrArg (fun z => Hom.app (A.extPowCmp gen hgen n) X z)
      (Subtype.ext (hx.trans
        (exteriorPower.ιMulti_apply_coe _ n s).symm) :
          (extPowSections n M.val X).symm x =
            exteriorPower.ιMulti ((Osharp.obj ⋙ forget₂ _ RingCat).obj X) n s)) ?_
    exact (Stacks.GradedAlgebra.extCmpSections_ιMulti A.toPresheafGradedAlgebra gen.val
      (fun X x => hgen X x) n X s).trans
      (A.toPresheafGradedAlgebra.homogeneousProdLeft_eq_homogeneousProd X n _).symm

end Sheafification

end SheafOfModules

end
