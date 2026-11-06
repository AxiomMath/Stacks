module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafificationTensor

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Localization
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SectionwiseAlgebras
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SymmetricAlgebraConstruction.DegreeZero.Unit
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorAlgebraBundle
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorAlgebraConstruction
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorExteriorSymmetricAlgebras

/-!
# The tensor, exterior and symmetric algebras of a sheaf of modules exist

Let `O` be a presheaf of commutative rings on a site `(C, J)`, let `Osharp` be a sheaf of
commutative rings and let `a : O ⟶ Osharp.obj` be locally bijective, so that
`PresheafOfModules.moduleSheafification J a` is the associated-sheaf functor on presheaves of
`O`-modules. `SheafOfModules.TensorExteriorSymmetricAlgebras` (in
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorExteriorSymmetricAlgebras`) is the
twenty-three-field package Stacks Section 17.21 attaches to a sheaf of modules: the tensor,
exterior and symmetric algebras, their three universal properties, the identification of the
homogeneous pieces of the tensor algebra with the sheafified tensor powers, the degree-zero
identifications, the direct-sum presentation, and the two quotient maps. This file **constructs
an inhabitant of it**, `SheafOfModules.tensorExteriorSymmetricAlgebras`, for the sheafification
of an arbitrary presheaf of `O`-modules.

Everything the construction needs about the three sectionwise algebras and about sheafification
is already in
`StacksDraft.Algebra.Category.ModuleCat.Sheaf.{SectionwiseAlgebras, TensorAlgebraConstruction,
TensorAlgebraBundle}`. What was missing is supplied here:

1. **the presheaf-level universal property** that `Stacks.GradedAlgebra.isUniversal_sheafify`
   consumes, proved once for an arbitrary sectionwise ungraded algebra presenting an
   `ℕ`-graded algebra of presheaves of modules as the submodule powers of its degree-one part
   (`Stacks.GradedAlgebra.existsUnique_unitalHom`), and then instantiated three times with
   `TensorAlgebra.lift`, `ExteriorAlgebra.lift` and `SymmetricAlgebra.liftComm`;
2. **the degree-zero comparison** `PresheafOfModules.sheafificationObjUnitIso`, read on the image
   of an arbitrary local section (`PresheafOfModules.sheafificationObjUnitIso_hom_unit`): the
   sheafification of the free presheaf of modules of rank one is the free sheaf of modules of
   rank one. This is the `e0` hypothesis of `SheafOfModules.tensorPowerSheafifyIso`;
3. **the degree-zero piece of the exterior algebra**, `ExteriorAlgebra.exteriorPowerZeroEquiv`
   and its sectionwise form `PresheafOfModules.extPowZeroIso`;
4. **the multiplication field** `SheafOfModules.sectionwiseTensorPieceIso_mul_left`, the one
   field of the bundle whose two sides are compared on arbitrary local sections rather than on
   unit images.

## Main definitions

* `Stacks.GradedAlgebra.descHom` and `descHomZ`: the degreewise morphism out of a sectionwise
  `ℕ`-graded algebra, and its extension by zero to the `ℤ`-graded one, determined by a ring
  homomorphism out of the ungraded sectionwise algebra.
* `SheafOfModules.GradedAlgebra.restrictGen`: a degree-one generator of a sheaf of graded
  algebras, restricted along the sheafification unit; `tensorLift`, `exteriorLift` and
  `symmetricLift`: the three lifts of it out of the sectionwise ungraded algebras.
* `ExteriorAlgebra.exteriorPowerZeroEquiv` and `PresheafOfModules.extPowZeroIso`: **the
  degree-zero exterior power is the base ring**, and its sectionwise form, the exterior
  analogue of `PresheafOfModules.tensorPowZeroIso`.
* `SheafOfModules.sheafifyTensorPowZeroIso` and `sheafifyExtPowZeroIso`: the degree-zero
  comparisons for the two families of sectionwise powers.
* `SheafOfModules.sectionwiseTensorPieceIso`: the identification of the degree-`n` piece of the
  sheafified sectionwise tensor algebra with the `n`-fold sheafified tensor power, and
  `sectionwiseTensorDirectSumIso`: the induced direct-sum comparison.
* `SheafOfModules.tensorExteriorSymmetricAlgebras`: **the inhabitant.**

## Main results

* `TensorAlgebra.exists_liftRingHom` and `ExteriorAlgebra.exists_liftRingHom`: **lifting out of
  the tensor and exterior algebras into a ring carrying a compatible module structure**, the
  analogues of `SymmetricAlgebra.exists_liftComm`. `TensorAlgebra.lift` and
  `ExteriorAlgebra.lift` need an `R`-algebra target; the ungraded realization of a graded
  algebra of presheaves of modules is only a ring with a compatible module structure, and
  `Algebra.ofModule` supplies the algebra structure inside the proof.
* `Stacks.GradedAlgebra.existsUnique_unitalHom`: **the presheaf-level universal property**, for
  an arbitrary sectionwise ungraded algebra. Its uniqueness half is
  `Stacks.GradedAlgebra.unitalHom_ext`, and the degreewise data is pinned down by
  `incl_descAppLin`.
* `SheafOfModules.GradedAlgebra.existsUnique_tensorUnitalHom`, `existsUnique_exteriorUnitalHom`
  and `existsUnique_symmetricUnitalHom`: the three instances of it, which are the `huniv`
  hypotheses of `Stacks.GradedAlgebra.isTensorAlgebra_sheafify`, `isExteriorAlgebra_sheafify`
  and `isSymmetricAlgebra_sheafify`.
* `SheafOfModules.isTensorAlgebra_sectionwiseTensorAlgebra`,
  `isExteriorAlgebra_sectionwiseExteriorAlgebra` and
  `isSymmetricAlgebra_sectionwiseSymmetricAlgebra`: the three universal properties of the
  sheafified sectionwise algebras.
* `SheafOfModules.sectionwiseTensorPieceIso_mul_left`: multiplication by a degree-one generator
  is tensor concatenation under the canonical homogeneous identifications.
* `SheafOfModules.nonempty_tensorExteriorSymmetricAlgebras`: the bundle is inhabited.

## Implementation notes

**Why the presheaf-level universal property is proved once and instantiated three times.** The
three sectionwise algebras differ only in the ungraded algebra they are formed in and in the
side condition the lift needs. Everything else — that the lift carries the degree-`n` part into
the degree-`n` part (`exists_eq_incl`), that the degreewise morphism so obtained is
multiplicative, unital and natural, that it extends to negative degrees by zero, and that it is
unique — is identical. `existsUnique_unitalHom` takes the ungraded algebra `Lam`, the degree-one
map `iota`, the sectionwise identification `qe` of the graded pieces with the submodule powers
of `LinearMap.range (iota X)`, and the lift `Φ`, and produces the whole statement; the three
instantiations supply `tensorPowSections`, `extPowSections` and `symPowSections` for `qe`.

**The data of that universal property is implicit and its hypotheses are explicit.** `Lam`,
`iota`, `Φ`, `lamRestrict` and the two graded algebras are implicit arguments, determined by the
explicit hypotheses `qe`, `hmul`, `hone`, `hgen`, `hqe`, `hΦι`, `hΦsmul` and `hΦnat`. That is
what keeps the three instantiations readable: a call names the eight hypotheses and nothing
else.

**Why the uniqueness induction is right-handed.** `unitalHom_app_natCast` inducts with
`Submodule.pow_induction_on_right'` rather than with its left-handed companion. The
right-handed step multiplies a section of degree `i` by one of degree `1` and lands in degree
`i + 1`, whose image in `ℤ` is *definitionally* `(i : ℤ) + 1`, which is the degree the
multiplicativity law of a unital homomorphism produces. The left-handed step lands in `1 + i`,
which is not definitionally `i + 1` in `ℕ`, and every statement would carry a transport. This
is the same choice, for the same reason, as `Stacks.GradedAlgebra.homogeneousProd`.

**The degrees in the multiplication field are variables, and are instantiated only at the point
of use.** `PresheafOfModules.tensorPowTensorIso_hom_tmul` and `tensorPowIsoTensor_hom_eq_mp` are
stated for arbitrary degrees `i`, `j`, `k` with `i + j = k`, even though only
`(1, n + 1, n + 2)` is ever used. With the numeral `1` in place the elaborator reconciles the
two sides by `isDefEq`, which unfolds the `Submodule` power `LinearMap.range ι ^ 1` and does not
terminate inside the heartbeat limit; with the degree a variable the power cannot reduce and the
statement elaborates at once. Instantiating at the point of use substitutes into an already
elaborated statement and costs nothing. No heartbeat limit is raised anywhere below.

**Transports along equalities of degrees are discharged by `subst`, which forces them into
separate declarations.** The `tensorPieceIso_mul_left` field of the bundle transports a section
of degree `1 + (n + 1)` to degree `n + 2` with `Eq.mp`, and `(1 : ℤ) + ((n + 1 : ℕ) : ℤ)` is not
definitionally `((n + 2 : ℕ) : ℤ)`. `Stacks.GradedAlgebra.map_eq_mp_mul` and
`PresheafOfModules.eq_mp_tensorPow_coe` state the two facts needed with the *target* degree a
variable together with the equation fixing it, so that `subst` removes the transport; at the
variable degrees the statements are the transport-free ones. Proof irrelevance then makes the
particular equality proof in the field's statement interchangeable with the one supplied here.

**Why `tensorPieceIso_mul_left` needs a separatedness argument.**
`SheafOfModules.tensorPowerSheafifyIso_add_two_unit` reads the comparison on the *unit image* of
a sectionwise section, whereas the field quantifies over arbitrary local sections of the
sheafification. The two are bridged by local lifting: both arguments lift along the
sheafification unit on a covering sieve (`Stacks.liftSieve_mem`), the restricted product is the
unit image of the sectionwise product (`Stacks.GradedAlgebra.sheafify_mul_restrict`), and the
target is a sheaf, hence separated (`Stacks.eq_of_isSeparated`). No exactness property of
sheafification is used.

**`ExteriorAlgebra.exteriorPowerZeroEquiv` duplicates Mathlib's `exteriorPower.zeroEquiv`, in
the other direction, on purpose.** Mathlib has
`exteriorPower.zeroEquiv : ⋀[R]^0 M ≃ₗ[R] R` (`Mathlib/LinearAlgebra/ExteriorPower/Basic.lean`),
built from `exteriorPower.ιMulti`; its inverse sends `r` to `r • ιMulti _ _ _`, so the
identification of a section of the degree-zero power with the image of a scalar under
`algebraMap` is a `simp` lemma rather than `rfl`. The sectionwise degree-zero comparison
`extPowZeroIso` and the computation of its inverse on the algebra unit are both stated at
`(extPow 0 F).obj X`, which is `↥(⋀[O(X)]^0 (F X))` only up to unfolding, and with a non-`rfl`
characterization of the sections every one of those statements needs an extra retyping
declaration to get past the structure-field wall. The version here is the exterior twin of the
repository's own `TensorAlgebra.gradedPieceZeroEquiv` and
`SymmetricAlgebra.symmetricPowerZeroEquiv`, which is what makes the three degree-zero
comparisons uniform. **The dedup against `exteriorPower.zeroEquiv` is owed**, and the right form
of it is a `rfl`-level `algebraMap` normalization of Mathlib's equivalence, upstream.

**The retyping declarations.** As in
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SectionwiseAlgebras`,
`PresheafOfModules.unitOneSection` exists only to spell the unit section of a free presheaf of
modules of rank one at the type of its sections rather than at the ring: the two are
definitionally equal, but the numeral `1` does not elaborate at the first.

**Universes.** The site universes `u`, `v` are independent of the ring universe `w`, but the
module universe is `w` as well, and that is forced rather than chosen in two places, exactly as
recorded in the implementation notes of
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorExteriorSymmetricAlgebras`: the tensor
product of sheaves of modules used for the tensor powers exists only over a presheaf of
commutative rings in the module universe, and the degree-zero identifications land in the
structure sheaf, whose sections are the ring's. In the two purely algebraic lemmas
`TensorAlgebra.exists_liftRingHom` and `ExteriorAlgebra.exists_liftRingHom`, and in
`ExteriorAlgebra.exteriorPowerZeroEquiv`, the universes of the ring and of the module are
independent. Nothing is narrowed relative to the files this builds on.

**No `@[stacks]` tag.** Tag 0FQW is the definition of a sheaf of graded algebras, carried by
`SheafOfModules.GradedAlgebra`; Tag 01CG is the symmetric-power sheafification statement, which
is not proved here. Section 17.21 has no tag of its own for the *existence* of the three
algebras, and the four files this one completes carry no tag for the same reason.

## References

* [Stacks Project, Section 17.21](https://stacks.math.columbia.edu/tag/01CF)
* [Stacks Project, Tag 0FQW](https://stacks.math.columbia.edu/tag/0FQW)
* [Stacks Project, Tag 01CG](https://stacks.math.columbia.edu/tag/01CG)
* [Stacks Project, Tag 0GMW](https://stacks.math.columbia.edu/tag/0GMW)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Sheaf Opposite

universe v u t a w

/-! ### Morphisms out of the zero presheaf of modules -/

namespace PresheafOfModules

variable {C : Type u} [Category.{v} C] (R : Cᵒᵖ ⥤ RingCat.{t})

/-- The unit section of the free presheaf of modules of rank one, with its type spelled at the
sections of `PresheafOfModules.unit`. The two types are definitionally equal, but the numeral
`1` does not elaborate at the second. -/
noncomputable def unitOneSection (X : Cᵒᵖ) : (PresheafOfModules.unit R).obj X := (1 : R.obj X)

/-- Any two morphisms out of the zero presheaf of modules agree: its sections vanish. -/
theorem hom_ext_zeroPresheaf {N : PresheafOfModules.{a} R}
    (φ ψ : zeroPresheaf.{v, u, t, a} R ⟶ N) : φ = ψ :=
  PresheafOfModules.hom_ext fun X => ModuleCat.hom_ext (LinearMap.ext fun x => by
    rw [zeroPresheaf_section_eq_zero R X x, map_zero, map_zero])

end PresheafOfModules

/-! ### The sheafification of the free presheaf of modules of rank one -/

namespace PresheafOfModules

section SheafifyUnit

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {R₀ : Cᵒᵖ ⥤ RingCat.{t}} {R : Sheaf J RingCat.{t}} (α : R₀ ⟶ R.obj)

/-- The comparison of the free objects of rank one is the ring map `α` itself, read in
`AddCommGrpCat`. -/
theorem toPresheaf_map_unitRestrictScalarsHom :
    (toPresheaf R₀).map (unitRestrictScalarsHom α) =
      Functor.whiskerRight α (forget₂ RingCat.{t} AddCommGrpCat.{t}) :=
  NatTrans.ext (funext fun X => AddCommGrpCat.hom_ext (AddMonoidHom.ext fun r =>
    mul_one ((α.app X).hom r)))

/-- The comparison of the free objects of rank one, on sections: it is the ring map `α`. -/
theorem unitRestrictScalarsHom_app (X : Cᵒᵖ) (r : R₀.obj X) :
    PresheafOfModules.Hom.app (unitRestrictScalarsHom α) X r = (α.app X).hom r :=
  mul_one ((α.app X).hom r)

variable [Presheaf.IsLocallyInjective J α] [Presheaf.IsLocallySurjective J α]

instance isLocallyInjective_whiskerRight_forget₂ :
    Presheaf.IsLocallyInjective J
      (Functor.whiskerRight α (forget₂ RingCat.{t} AddCommGrpCat.{t})) := by
  rw [← Presheaf.isLocallyInjective_forget_iff]
  exact inferInstanceAs
    (Presheaf.IsLocallyInjective J (Functor.whiskerRight α (forget RingCat)))

instance isLocallySurjective_whiskerRight_forget₂ :
    Presheaf.IsLocallySurjective J
      (Functor.whiskerRight α (forget₂ RingCat.{t} AddCommGrpCat.{t})) :=
  (Presheaf.isLocallySurjective_iff_whisker_forget J
    (Functor.whiskerRight α (forget₂ RingCat.{t} AddCommGrpCat.{t}))).2
      (inferInstanceAs (Presheaf.IsLocallySurjective J
        (Functor.whiskerRight α (forget RingCat))))

variable [J.WEqualsLocallyBijective AddCommGrpCat.{t}] [HasWeakSheafify J AddCommGrpCat.{t}]

instance isIso_sheafification_map_unitRestrictScalarsHom :
    IsIso ((sheafification.{t} α).map (unitRestrictScalarsHom α)) := by
  have hW : J.W ((toPresheaf R₀).map (unitRestrictScalarsHom α)) := by
    rw [toPresheaf_map_unitRestrictScalarsHom]
    exact J.W_of_isLocallyBijective
      (Functor.whiskerRight α (forget₂ RingCat.{t} AddCommGrpCat.{t}))
  have h : (MorphismProperty.isomorphisms (SheafOfModules.{t} R)).inverseImage
      (sheafification.{t} α) (unitRestrictScalarsHom α) := by
    rw [← inverseImage_W_toPresheaf_eq_inverseImage_isomorphisms α]
    exact hW
  exact h

/-- **The identification of the sheafified free rank-one presheaf of modules with the free
rank-one sheaf of modules, read on the image of a local section `r`:** it is `α r`. -/
theorem sheafificationObjUnitIso_hom_unit (X : Cᵒᵖ) (r : R₀.obj X) :
    (sheafificationObjUnitIso α).hom.val.app X
        (PresheafOfModules.Hom.app (sheafifyUnit α (PresheafOfModules.unit R₀)) X r) =
      (α.app X).hom r := by
  have h := sheafificationHomEquiv_app α (sheafificationObjUnitHom α) X r
  rw [show sheafificationHomEquiv α (sheafificationObjUnitHom α) = unitRestrictScalarsHom α from
    (sheafificationHomEquiv α).apply_symm_apply _, unitRestrictScalarsHom_app] at h
  exact h.symm

end SheafifyUnit

end PresheafOfModules

/-! ### Lifting out of the tensor and exterior algebras into a ring-module -/

/-- An algebra map into a ring `T` with the algebra structure `Algebra.ofModule` is `R`-linear. -/
private theorem algHom_ofModule_smul {R A T : Type*} [CommRing R] [Ring A] [Algebra R A] [Ring T]
    [Module R T] (h₁ : ∀ (r : R) (x y : T), r • x * y = r • (x * y))
    (h₂ : ∀ (r : R) (x y : T), x * r • y = r • (x * y)) :
    letI := Algebra.ofModule h₁ h₂
    ∀ (φ : A →ₐ[R] T) (r : R) (x : A), φ (r • x) = r • φ x := by
  let _ : Algebra R T := Algebra.ofModule h₁ h₂
  intro φ r x
  have hone : φ (algebraMap R A r) = r • (1 : T) :=
    (AlgHom.commutes _ r).trans (Algebra.algebraMap_eq_smul_one r)
  rw [Algebra.smul_def, map_mul, hone, h₁, one_mul]

namespace TensorAlgebra

/-- **Lifting out of the tensor algebra into a ring carrying a compatible module structure.**
A linear map `γ : M →ₗ[R] T` into a ring `T` which is an `R`-module satisfying the two scalar
laws extends to a ring homomorphism `TensorAlgebra R M →+* T` carrying `ι R m` to `γ m` and
linear over `R`.

`TensorAlgebra.lift` needs the target to be an `R`-algebra; the target here is an arbitrary
ring with a compatible module structure, and `Algebra.ofModule` supplies the algebra structure
inside the proof. The statement is existential so that that structure, which is not an instance
and is not canonical, does not appear in it. -/
theorem exists_liftRingHom {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]
    {T : Type*} [Ring T] [Module R T]
    (h₁ : ∀ (r : R) (x y : T), r • x * y = r • (x * y))
    (h₂ : ∀ (r : R) (x y : T), x * r • y = r • (x * y)) (γ : M →ₗ[R] T) :
    ∃ Φ : TensorAlgebra R M →+* T,
      (∀ m : M, Φ (TensorAlgebra.ι R m) = γ m) ∧
        ∀ (r : R) (x : TensorAlgebra R M), Φ (r • x) = r • Φ x := by
  let _ : Algebra R T := Algebra.ofModule h₁ h₂
  refine ⟨(TensorAlgebra.lift R γ).toRingHom, fun m => TensorAlgebra.lift_ι_apply γ m,
    fun r x => algHom_ofModule_smul h₁ h₂ _ r x⟩

end TensorAlgebra

namespace ExteriorAlgebra

/-- **Lifting out of the exterior algebra into a ring carrying a compatible module structure.**
The exterior analogue of `TensorAlgebra.exists_liftRingHom`; the extra hypothesis is that the
image of `γ` squares to zero. -/
theorem exists_liftRingHom {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]
    {T : Type*} [Ring T] [Module R T]
    (h₁ : ∀ (r : R) (x y : T), r • x * y = r • (x * y))
    (h₂ : ∀ (r : R) (x y : T), x * r • y = r • (x * y)) (γ : M →ₗ[R] T)
    (hγ : ∀ m : M, γ m * γ m = 0) :
    ∃ Φ : ExteriorAlgebra R M →+* T,
      (∀ m : M, Φ (ExteriorAlgebra.ι R m) = γ m) ∧
        ∀ (r : R) (x : ExteriorAlgebra R M), Φ (r • x) = r • Φ x := by
  let _ : Algebra R T := Algebra.ofModule h₁ h₂
  refine ⟨(ExteriorAlgebra.lift R ⟨γ, hγ⟩).toRingHom,
    fun m => ExteriorAlgebra.lift_ι_apply R γ hγ m,
    fun r x => algHom_ofModule_smul h₁ h₂ _ r x⟩

end ExteriorAlgebra

/-! ### The presheaf-level universal property of a sectionwise graded algebra -/

namespace Stacks

namespace BilinearMap

variable {C : Type u} [Category.{v} C] {R : Cᵒᵖ ⥤ RingCat.{t}}
  {M N P : PresheafOfModules.{a} R}

theorem app_zero_left (β : BilinearMap M N P) (X : Cᵒᵖ) (y : N.obj X) :
    β.app X 0 y = 0 := by rw [map_zero]; rfl

end BilinearMap

namespace GradedAlgebra

section Inj

variable {C : Type u} [Category.{v} C] {O : Cᵒᵖ ⥤ CommRingCat.{w}}
  {Pz : ℤ → PresheafOfModules.{w} (O ⋙ forget₂ CommRingCat RingCat)} (D : GradedAlgebra Pz)

/-- `Stacks.GradedAlgebra.incl` is injective, `Stacks.GradedAlgebra.proj` being a left
inverse. -/
theorem incl_inj {i : ℤ} {X : Cᵒᵖ} {x y : (Pz i).obj X} (h : D.incl i x = D.incl i y) :
    x = y := by
  have h2 := congrArg (D.proj X i) h
  rwa [D.proj_incl, D.proj_incl] at h2

end Inj

section Lift

variable {C : Type u} [Category.{v} C] {O : Cᵒᵖ ⥤ CommRingCat.{w}}
  {F : PresheafOfModules.{w} (O ⋙ forget₂ CommRingCat RingCat)}
  {Q : ℕ → PresheafOfModules.{w} (O ⋙ forget₂ CommRingCat RingCat)}
  {Pz : ℤ → PresheafOfModules.{w} (O ⋙ forget₂ CommRingCat RingCat)}
  {Lam : Cᵒᵖ → Type w} [∀ X : Cᵒᵖ, Ring (Lam X)]
  [∀ X : Cᵒᵖ, Algebra ((O ⋙ forget₂ CommRingCat RingCat).obj X) (Lam X)]
  {A : GradedAlgebra Q} {D : GradedAlgebra Pz}
  {gen : F ⟶ Q 1} {gen' : F ⟶ Pz 1}
  {iota : ∀ X : Cᵒᵖ, F.obj X →ₗ[(O ⋙ forget₂ CommRingCat RingCat).obj X] Lam X}
  {lamRestrict : ∀ {X Y : Cᵒᵖ}, (X ⟶ Y) → (Lam X →+* Lam Y)}
  {Φ : ∀ X : Cᵒᵖ, Lam X →+* D.Total X}

/-- The lift out of the sectionwise ungraded algebra, as a linear map. -/
noncomputable def liftLin
    (hΦsmul : ∀ (X : Cᵒᵖ) (r : (O ⋙ forget₂ CommRingCat RingCat).obj X) (z : Lam X),
      Φ X (r • z) = r • Φ X z) (X : Cᵒᵖ) :
    Lam X →ₗ[(O ⋙ forget₂ CommRingCat RingCat).obj X] D.Total X where
  toFun := Φ X
  map_add' := map_add (Φ X)
  map_smul' r z := hΦsmul X r z

variable
  (qe : ∀ (n : ℕ) (X : Cᵒᵖ), (Q n).obj X ≃ₗ[(O ⋙ forget₂ CommRingCat RingCat).obj X]
    ↥(LinearMap.range (iota X) ^ n))
  (hmul : ∀ (i j : ℕ) (X : Cᵒᵖ) (x : (Q i).obj X) (y : (Q j).obj X),
    ((qe (i + j) X ((A.mul i j).app X x y) : Lam X)) =
      (qe i X x : Lam X) * (qe j X y : Lam X))
  (hone : ∀ X : Cᵒᵖ, ((qe 0 X (A.one.eval X) : Lam X)) = 1)
  (hgen : ∀ (X : Cᵒᵖ) (m : F.obj X),
    ((qe 1 X (PresheafOfModules.Hom.app gen X m) : Lam X)) = iota X m)
  (hqe : ∀ (n : ℕ) {X Y : Cᵒᵖ} (f : X ⟶ Y) (x : (Q n).obj X),
    ((qe n Y (sectionRestrict (Q n) f x) : Lam Y)) = lamRestrict f (qe n X x))
  (hΦι : ∀ (X : Cᵒᵖ) (m : F.obj X),
    Φ X (iota X m) = D.incl 1 (PresheafOfModules.Hom.app gen' X m))
  (hΦsmul : ∀ (X : Cᵒᵖ) (r : (O ⋙ forget₂ CommRingCat RingCat).obj X) (z : Lam X),
    Φ X (r • z) = r • Φ X z)
  (hΦnat : ∀ {X Y : Cᵒᵖ} (f : X ⟶ Y) (z : Lam X),
    D.totalRestrict f (Φ X z) = Φ Y (lamRestrict f z))
  (hlamι : ∀ {X Y : Cᵒᵖ} (f : X ⟶ Y) (m : F.obj X),
    lamRestrict f (iota X m) = iota Y (sectionRestrict F f m))
  (hlamAlg : ∀ {X Y : Cᵒᵖ} (f : X ⟶ Y) (r : (O ⋙ forget₂ CommRingCat RingCat).obj X),
    lamRestrict f (algebraMap _ (Lam X) r) =
      algebraMap _ (Lam Y) ((O ⋙ forget₂ CommRingCat RingCat).map f r))
  (hlamExt : ∀ {X Y : Cᵒᵖ} (p q : Lam X →+* D.Total Y),
    (∀ r : (O ⋙ forget₂ CommRingCat RingCat).obj X,
      p (algebraMap _ (Lam X) r) = q (algebraMap _ (Lam X) r)) →
    (∀ m : F.obj X, p (iota X m) = q (iota X m)) → p = q)

include hΦsmul in
/-- The lift carries the image of the base ring to `r • 1`. -/
theorem lift_algebraMap (X : Cᵒᵖ) (r : (O ⋙ forget₂ CommRingCat RingCat).obj X) :
    Φ X (algebraMap _ (Lam X) r) = r • (1 : D.Total X) := by
  rw [Algebra.algebraMap_eq_smul_one, hΦsmul, map_one]

include hΦι hΦsmul hlamι hlamAlg hlamExt in
/-- **The lift commutes with restriction**, which is the hypothesis `hΦnat` of the results
below. Both sides are ring homomorphisms out of the sectionwise ungraded algebra, so they are
compared on the image of the base ring and on the degree-one generators. -/
theorem lift_naturality {X Y : Cᵒᵖ} (f : X ⟶ Y) (z : Lam X) :
    D.totalRestrict f (Φ X z) = Φ Y (lamRestrict f z) := by
  have h : (D.totalRestrictRingHom f).comp (Φ X) = (Φ Y).comp (lamRestrict f) := by
    refine hlamExt _ _ (fun r => ?_) (fun m => ?_)
    · change D.totalRestrict f (Φ X (algebraMap _ (Lam X) r)) =
        Φ Y (lamRestrict f (algebraMap _ (Lam X) r))
      rw [lift_algebraMap hΦsmul, hlamAlg, lift_algebraMap hΦsmul, D.totalRestrict_smul,
        D.totalRestrict_one]
    · change D.totalRestrict f (Φ X (iota X m)) = Φ Y (lamRestrict f (iota X m))
      rw [hΦι, hlamι, hΦι, D.totalRestrict_incl]
      exact congrArg (D.incl 1) (PresheafOfModules.naturality_apply gen' f m).symm
  exact congrArg (fun p : Lam X →+* D.Total Y => p z) h


include hΦι hΦsmul in
/-- **The lift carries the degree-`n` part of the sectionwise algebra into the degree-`n` part
of the target.** -/
theorem exists_eq_incl {X : Cᵒᵖ} {n : ℕ} {z : Lam X}
    (hz : z ∈ LinearMap.range (iota X) ^ n) :
    ∃ y : (Pz (n : ℤ)).obj X, Φ X z = D.incl (n : ℤ) y := by
  induction hz using Submodule.pow_induction_on_right' with
  | algebraMap r =>
      refine ⟨r • D.one.eval X, ?_⟩
      rw [Algebra.algebraMap_eq_smul_one, hΦsmul, map_one, D.incl_smul]
      exact congrArg (fun z => r • z) (D.one_eq_incl X)
  | add x y i _ _ ihx ihy =>
      obtain ⟨p, hp⟩ := ihx
      obtain ⟨q, hq⟩ := ihy
      exact ⟨p + q, by rw [map_add, hp, hq, D.incl_add]⟩
  | mul_mem i x _ ih m hm =>
      obtain ⟨y, hy⟩ := ih
      obtain ⟨m₀, rfl⟩ := hm
      exact ⟨(D.mul (i : ℤ) 1).app X y (PresheafOfModules.Hom.app gen' X m₀),
        by rw [map_mul, hy, hΦι, D.incl_mul_incl]; rfl⟩

/-- The degree-`n` component of the lift, on sections. -/
noncomputable def descAppLin (n : ℕ) (X : Cᵒᵖ) :
    (Q n).obj X →ₗ[(O ⋙ forget₂ CommRingCat RingCat).obj X] (Pz (n : ℤ)).obj X :=
  (D.proj X (n : ℤ)).comp ((liftLin hΦsmul X).comp
    (((LinearMap.range (iota X) ^ n).subtype).comp (qe n X).toLinearMap))

theorem descAppLin_apply (n : ℕ) (X : Cᵒᵖ) (x : (Q n).obj X) :
    descAppLin qe hΦsmul n X x = D.proj X (n : ℤ) (Φ X (qe n X x)) := rfl

include hΦι in
/-- The degree-`n` component of the lift is the lift itself, read in degree `n`. -/
theorem incl_descAppLin (n : ℕ) (X : Cᵒᵖ) (x : (Q n).obj X) :
    D.incl (n : ℤ) (descAppLin qe hΦsmul n X x) = Φ X (qe n X x) := by
  obtain ⟨y, hy⟩ := exists_eq_incl hΦι hΦsmul (qe n X x).2
  have h1 : descAppLin qe hΦsmul n X x = y := by
    rw [descAppLin_apply, hy, D.proj_incl]
  rw [h1, hy]

include hqe hΦι hΦnat in
/-- The degree-`n` component of the lift commutes with restriction. -/
theorem descAppLin_naturality (n : ℕ) {X Y : Cᵒᵖ} (f : X ⟶ Y) (x : (Q n).obj X) :
    sectionRestrict (Pz (n : ℤ)) f (descAppLin qe hΦsmul n X x) =
      descAppLin qe hΦsmul n Y (sectionRestrict (Q n) f x) := by
  refine D.incl_inj (i := (n : ℤ)) (X := Y) ?_
  rw [← D.totalRestrict_incl, incl_descAppLin qe hΦι hΦsmul,
    incl_descAppLin qe hΦι hΦsmul, hΦnat, hqe]

/-- The degree-`n` component of the lift, as a morphism of presheaves of modules. -/
noncomputable def descHom (n : ℕ) : Q n ⟶ Pz (n : ℤ) where
  app X := ModuleCat.ofHom (descAppLin qe hΦsmul n X)
  naturality f := ModuleCat.hom_ext (LinearMap.ext fun x =>
    (descAppLin_naturality qe hqe hΦι hΦsmul hΦnat n f x).symm)

theorem descHom_app (n : ℕ) (X : Cᵒᵖ) (x : (Q n).obj X) :
    PresheafOfModules.Hom.app (descHom qe hqe hΦι hΦsmul hΦnat n) X x =
      descAppLin qe hΦsmul n X x := rfl

include hmul hΦι in
/-- The lift is multiplicative. -/
theorem descAppLin_mul (i j : ℕ) (X : Cᵒᵖ) (x : (Q i).obj X) (y : (Q j).obj X) :
    descAppLin qe hΦsmul (i + j) X ((A.mul i j).app X x y) =
      (D.mul (i : ℤ) (j : ℤ)).app X (descAppLin qe hΦsmul i X x)
        (descAppLin qe hΦsmul j X y) := by
  refine D.incl_inj (i := ((i + j : ℕ) : ℤ)) (X := X) ?_
  rw [incl_descAppLin qe hΦι hΦsmul, hmul, map_mul, ← incl_descAppLin qe hΦι hΦsmul,
    ← incl_descAppLin qe hΦι hΦsmul]
  exact D.incl_mul_incl (i : ℤ) (j : ℤ) _ _

include hone hΦι in
/-- The lift is unital. -/
theorem descAppLin_one (X : Cᵒᵖ) :
    descAppLin qe hΦsmul 0 X (A.one.eval X) = D.one.eval X := by
  refine D.incl_inj (i := ((0 : ℕ) : ℤ)) (X := X) ?_
  rw [incl_descAppLin qe hΦι hΦsmul, hone, map_one]
  exact D.one_eq_incl X

include hgen hΦι in
/-- The lift extends the degree-one generator. -/
theorem descAppLin_gen (X : Cᵒᵖ) (m : F.obj X) :
    descAppLin qe hΦsmul 1 X (PresheafOfModules.Hom.app gen X m) =
      PresheafOfModules.Hom.app gen' X m := by
  refine D.incl_inj (i := ((1 : ℕ) : ℤ)) (X := X) ?_
  rw [incl_descAppLin qe hΦι hΦsmul, hgen, hΦι]
  rfl

/-- The lift, extended by zero into the negative degrees: the degreewise morphism out of the
`ℤ`-graded sectionwise algebra `Stacks.GradedAlgebra.extend`. -/
noncomputable def descHomZ : (n : ℤ) → extendFamily Q n ⟶ Pz n
  | Int.ofNat k => descHom qe hqe hΦι hΦsmul hΦnat k
  | Int.negSucc _ => 0

theorem descHomZ_natCast (k : ℕ) :
    descHomZ qe hqe hΦι hΦsmul hΦnat (k : ℤ) = descHom qe hqe hΦι hΦsmul hΦnat k := rfl

include hmul in
/-- The extended lift is multiplicative. -/
theorem descHomZ_mul (i j : ℤ) (X : Cᵒᵖ) (x : (extendFamily Q i).obj X)
    (y : (extendFamily Q j).obj X) :
    PresheafOfModules.Hom.app (descHomZ qe hqe hΦι hΦsmul hΦnat (i + j)) X
        ((A.extend.mul i j).app X x y) =
      (D.mul i j).app X (PresheafOfModules.Hom.app (descHomZ qe hqe hΦι hΦsmul hΦnat i) X x)
        (PresheafOfModules.Hom.app (descHomZ qe hqe hΦι hΦsmul hΦnat j) X y) := by
  rcases lt_or_ge i 0 with hi | hi
  · have hz : ((A.extend).mul i j).app X x y = 0 :=
      A.extendMul_app_eq_zero_of_neg_left hi j X x y
    have hx : x = 0 := extendFamily_section_eq_zero hi X x
    rw [hz, map_zero, hx, map_zero, BilinearMap.app_zero_left]
  rcases lt_or_ge j 0 with hj | hj
  · have hz : ((A.extend).mul i j).app X x y = 0 :=
      A.extendMul_app_eq_zero_of_neg_right i hj X x y
    have hy : y = 0 := extendFamily_section_eq_zero hj X y
    rw [hz, map_zero, hy, map_zero, map_zero]
  obtain ⟨p, rfl⟩ := Int.eq_ofNat_of_zero_le hi
  obtain ⟨q, rfl⟩ := Int.eq_ofNat_of_zero_le hj
  exact descAppLin_mul qe hmul hΦι hΦsmul p q X x y

include hone in
/-- The extended lift is unital. -/
theorem descHomZ_one (X : Cᵒᵖ) :
    PresheafOfModules.Hom.app (descHomZ qe hqe hΦι hΦsmul hΦnat 0) X (A.extend.one.eval X) =
      D.one.eval X :=
  descAppLin_one qe hone hΦι hΦsmul X

include hgen in
/-- The extended lift extends the degree-one generator. -/
theorem descHomZ_gen (X : Cᵒᵖ) (m : F.obj X) :
    PresheafOfModules.Hom.app (descHomZ qe hqe hΦι hΦsmul hΦnat 1) X
        (PresheafOfModules.Hom.app gen X m) =
      PresheafOfModules.Hom.app gen' X m :=
  descAppLin_gen qe hgen hΦι hΦsmul X m

include hmul hone hgen in
/-- **Degree `n` of the sectionwise algebra is generated by products of degree-one
generators**, in the form uniqueness needs it: two unital homomorphisms out of the extended
sectionwise algebra which agree on the images of the degree-one generator agree in every
nonnegative degree.

The induction is `Submodule.pow_induction_on_right'` and not its left-handed companion: the
right-handed step produces a section of degree `i + 1`, whose image in `ℤ` is definitionally
`(i : ℤ) + 1`, which is the degree the multiplicativity law of a unital homomorphism produces.
The left-handed step produces `1 + i`, which is not. -/
theorem unitalHom_app_natCast {g h : UnitalHom A.extend D}
    (hgh : ∀ (X : Cᵒᵖ) (m : F.obj X),
      PresheafOfModules.Hom.app (g.app 1) X (PresheafOfModules.Hom.app gen X m) =
        PresheafOfModules.Hom.app (h.app 1) X (PresheafOfModules.Hom.app gen X m))
    (X : Cᵒᵖ) (n : ℕ) (x : (Q n).obj X) :
    PresheafOfModules.Hom.app (g.app (n : ℤ)) X x =
      PresheafOfModules.Hom.app (h.app (n : ℤ)) X x := by
  have key : ∀ (m : ℕ) (z : Lam X), z ∈ LinearMap.range (iota X) ^ m →
      ∀ y : (Q m).obj X, (qe m X y : Lam X) = z →
        PresheafOfModules.Hom.app (g.app (m : ℤ)) X y =
          PresheafOfModules.Hom.app (h.app (m : ℤ)) X y := by
    intro m z hz
    induction hz using Submodule.pow_induction_on_right' with
    | algebraMap r =>
        intro y hy
        have hy' : y = r • A.one.eval X := by
          refine (qe 0 X).injective (Subtype.ext ?_)
          rw [hy, map_smul, Submodule.coe_smul, hone]
          exact Algebra.algebraMap_eq_smul_one r
        have hsm : ∀ k : UnitalHom A.extend D,
            PresheafOfModules.Hom.app (k.app ((0 : ℕ) : ℤ)) X y = r • D.one.eval X := by
          intro k
          rw [hy', show PresheafOfModules.Hom.app (k.app ((0 : ℕ) : ℤ)) X
              (r • A.one.eval X) =
                r • PresheafOfModules.Hom.app (k.app ((0 : ℕ) : ℤ)) X (A.one.eval X) from
            map_smul _ r _]
          exact congrArg (fun z => r • z) (k.map_one X)
        rw [hsm g, hsm h]
    | add z₁ z₂ i hz₁ hz₂ ih₁ ih₂ =>
        intro y hy
        have hy' : y = (qe i X).symm ⟨z₁, hz₁⟩ + (qe i X).symm ⟨z₂, hz₂⟩ := by
          refine (qe i X).injective ?_
          rw [map_add, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
          exact Subtype.ext hy
        have hadd : ∀ k : UnitalHom A.extend D,
            PresheafOfModules.Hom.app (k.app (i : ℤ)) X y =
              PresheafOfModules.Hom.app (k.app (i : ℤ)) X ((qe i X).symm ⟨z₁, hz₁⟩) +
                PresheafOfModules.Hom.app (k.app (i : ℤ)) X ((qe i X).symm ⟨z₂, hz₂⟩) := by
          intro k
          rw [hy']
          exact map_add _ _ _
        rw [hadd g, hadd h, ih₁ _ (by rw [LinearEquiv.apply_symm_apply]),
          ih₂ _ (by rw [LinearEquiv.apply_symm_apply])]
    | mul_mem i z₀ hz₀ ih m₁ hm₁ =>
        obtain ⟨m₀, rfl⟩ := hm₁
        intro y hy
        have hy' : y = (A.mul i 1).app X ((qe i X).symm ⟨z₀, hz₀⟩)
            (PresheafOfModules.Hom.app gen X m₀) := by
          refine (qe (i + 1) X).injective (Subtype.ext ?_)
          rw [hy, hmul, LinearEquiv.apply_symm_apply, hgen]
        have hgm : ∀ k : UnitalHom A.extend D,
            PresheafOfModules.Hom.app (k.app ((i + 1 : ℕ) : ℤ)) X y =
              (D.mul (i : ℤ) 1).app X
                (PresheafOfModules.Hom.app (k.app (i : ℤ)) X ((qe i X).symm ⟨z₀, hz₀⟩))
                (PresheafOfModules.Hom.app (k.app 1) X
                  (PresheafOfModules.Hom.app gen X m₀)) := by
          intro k
          rw [hy']
          exact k.map_mul (i : ℤ) 1 X _ _
        rw [hgm g, hgm h, ih _ (by rw [LinearEquiv.apply_symm_apply]), hgh]
  exact key n (qe n X x : Lam X) (qe n X x).2 x rfl

include hmul hone hgen in
/-- **Uniqueness of the lift.** -/
theorem unitalHom_ext {g h : UnitalHom A.extend D}
    (hgh : ∀ (X : Cᵒᵖ) (m : F.obj X),
      PresheafOfModules.Hom.app (g.app 1) X (PresheafOfModules.Hom.app gen X m) =
        PresheafOfModules.Hom.app (h.app 1) X (PresheafOfModules.Hom.app gen X m)) :
    g = h := by
  refine UnitalHom.ext fun n => ?_
  match n with
  | Int.negSucc k => exact PresheafOfModules.hom_ext_zeroPresheaf _ _ _
  | Int.ofNat k =>
      exact PresheafOfModules.hom_ext fun X =>
        ModuleCat.hom_ext (LinearMap.ext fun x =>
          unitalHom_app_natCast qe hmul hone hgen hgh X k x)

include hmul hone hgen hqe hΦι hΦsmul hΦnat in
/-- **The presheaf-level universal property of a sectionwise graded algebra.** Let `A` be an
`ℕ`-graded algebra of presheaves of modules whose degree-`n` piece is, sectionwise, the `n`-th
power of the range of `iota` inside an ungraded sectionwise algebra `Lam`, and let `D` be a
`ℤ`-graded algebra of presheaves of modules with a degree-one generator `gen'`. A lift `Φ` of
`gen'` to a ring homomorphism out of `Lam` produces a *unique* unital homomorphism
`A.extend ⟶ D` carrying the degree-one generator of `A` to `gen'`.

This is the hypothesis `huniv` of `Stacks.GradedAlgebra.isUniversal_sheafify`, for an arbitrary
target; the three algebras of Section 17.21 instantiate it with `TensorAlgebra.lift`,
`ExteriorAlgebra.lift` and `SymmetricAlgebra.liftComm`. -/
theorem existsUnique_unitalHom :
    ∃! k : UnitalHom A.extend D, ∀ (X : Cᵒᵖ) (m : F.obj X),
      PresheafOfModules.Hom.app (k.app 1) X (PresheafOfModules.Hom.app gen X m) =
        PresheafOfModules.Hom.app gen' X m := by
  refine ⟨{ app := descHomZ qe hqe hΦι hΦsmul hΦnat
            map_mul := descHomZ_mul qe hmul hqe hΦι hΦsmul hΦnat
            map_one := descHomZ_one qe hone hqe hΦι hΦsmul hΦnat },
    descHomZ_gen qe hgen hqe hΦι hΦsmul hΦnat, fun k hk => ?_⟩
  exact unitalHom_ext qe hmul hone hgen fun X m =>
    (hk X m).trans (descHomZ_gen qe hgen hqe hΦι hΦsmul hΦnat X m).symm

end Lift




end GradedAlgebra

end Stacks


/-! ### The presheaf-level universal property of the three sectionwise algebras -/

namespace SheafOfModules.GradedAlgebra

section Universal

open CategoryTheory.Sheaf PresheafOfModules

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  {O : Cᵒᵖ ⥤ CommRingCat.{w}} {Osharp : Sheaf J CommRingCat.{w}} (a : O ⟶ Osharp.obj)
  (F : PresheafOfModules.{w} (O ⋙ forget₂ CommRingCat RingCat))
  (B : GradedAlgebra.{w, w} (toRingCat J Osharp))

/-- The two scalar laws of the ungraded realization of the restriction of scalars, in the form
the lifts out of the three sectionwise algebras consume. -/
theorem restrictScalars_smul_mul_eq {X : Cᵒᵖ}
    (r : (O ⋙ forget₂ CommRingCat RingCat).obj X)
    (x y : (B.restrictScalars (toRingCatMap J a)).Total X) : r • x * y = r • (x * y) :=
  (B.restrictScalars (toRingCatMap J a)).smul_mul_eq r x y

/-- The companion of `SheafOfModules.GradedAlgebra.restrictScalars_smul_mul_eq` in the second
variable. -/
theorem restrictScalars_mul_smul_eq {X : Cᵒᵖ}
    (r : (O ⋙ forget₂ CommRingCat RingCat).obj X)
    (x y : (B.restrictScalars (toRingCatMap J a)).Total X) : x * (r • y) = r • (x * y) :=
  (B.restrictScalars (toRingCatMap J a)).mul_smul_eq r x y

variable [Presheaf.IsLocallyInjective J (toRingCatMap J a)]
  [Presheaf.IsLocallySurjective J (toRingCatMap J a)]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]
  (κ : (moduleSheafification J a).obj F ⟶ B.piece 1)

/-- A degree-one generator of a sheaf of graded algebras, restricted along the sheafification
unit to a degree-one generator of the restriction of scalars. This is the generator the
presheaf-level universal property lifts. -/
noncomputable def restrictGen :
    F ⟶ (SheafOfModules.forget (toRingCat J Osharp) ⋙
      PresheafOfModules.restrictScalars (toRingCatMap J a)).obj (B.piece 1) :=
  sheafifyUnit (toRingCatMap J a) F ≫
    (SheafOfModules.forget (toRingCat J Osharp) ⋙
      PresheafOfModules.restrictScalars (toRingCatMap J a)).map κ

theorem restrictGen_app (X : Cᵒᵖ) (s : F.obj X) :
    PresheafOfModules.Hom.app (restrictGen J a F B κ) X s =
      κ.val.app X (PresheafOfModules.Hom.app (sheafifyUnit (toRingCatMap J a) F) X s) := rfl

/-! #### The tensor algebra -/

/-- The existence statement from which the properties of `tensorLift` are read. -/
private abbrev tensorLiftEx (X : Cᵒᵖ) :=
  TensorAlgebra.exists_liftRingHom (restrictScalars_smul_mul_eq J a B)
    (restrictScalars_mul_smul_eq J a B)
    ((B.restrictScalars (toRingCatMap J a)).genLin (restrictGen J a F B κ) X)

/-- The lift of a degree-one generator to a ring homomorphism out of the sectionwise tensor
algebra, by `TensorAlgebra.lift`. -/
noncomputable def tensorLift (X : Cᵒᵖ) :
    TensorAlgebra ((O ⋙ forget₂ CommRingCat RingCat).obj X) (F.obj X) →+*
      (B.restrictScalars (toRingCatMap J a)).Total X :=
  (TensorAlgebra.exists_liftRingHom (restrictScalars_smul_mul_eq J a B)
    (restrictScalars_mul_smul_eq J a B)
    ((B.restrictScalars (toRingCatMap J a)).genLin (restrictGen J a F B κ) X)).choose

theorem tensorLift_ι (X : Cᵒᵖ) (m : F.obj X) :
    tensorLift J a F B κ X (TensorAlgebra.ι _ m) =
      (B.restrictScalars (toRingCatMap J a)).incl 1
        (PresheafOfModules.Hom.app (restrictGen J a F B κ) X m) :=
  (tensorLiftEx J a F B κ X).choose_spec.1 m

theorem tensorLift_smul (X : Cᵒᵖ) (r : (O ⋙ forget₂ CommRingCat RingCat).obj X)
    (z : TensorAlgebra ((O ⋙ forget₂ CommRingCat RingCat).obj X) (F.obj X)) :
    tensorLift J a F B κ X (r • z) = r • tensorLift J a F B κ X z :=
  (tensorLiftEx J a F B κ X).choose_spec.2 r z

/-- **The presheaf-level universal property of the sectionwise tensor algebra.** This is the
hypothesis `huniv` of `Stacks.GradedAlgebra.isTensorAlgebra_sheafify`. -/
theorem existsUnique_tensorUnitalHom :
    ∃! g : Stacks.GradedAlgebra.UnitalHom (tensorPowGradedAlgebra F).extend
      (B.restrictScalars (toRingCatMap J a)),
      ∀ (X : Cᵒᵖ) (s : F.obj X),
        PresheafOfModules.Hom.app (g.app 1) X
            (PresheafOfModules.Hom.app (tensorPowGen F) X s) =
          κ.val.app X (PresheafOfModules.Hom.app (sheafifyUnit (toRingCatMap J a) F) X s) :=
  Stacks.GradedAlgebra.existsUnique_unitalHom
    (A := tensorPowGradedAlgebra F) (gen := tensorPowGen F)
    (iota := fun X => TensorAlgebra.ι ((O ⋙ forget₂ CommRingCat RingCat).obj X))
    (lamRestrict := fun f => TensorAlgebra.mapₛₗ
      ((O ⋙ forget₂ CommRingCat RingCat).map f).hom (F.restrictₛₗ f))
    (Φ := tensorLift J a F B κ)
    (fun n X => tensorPowSections n F X)
    (fun _ _ _ _ _ => rfl) (fun _ => rfl) (fun X m => tensorPowGen_coe F X m)
    (fun n {_ _} f x => tensorPowSections_map n F f x)
    (tensorLift_ι J a F B κ) (tensorLift_smul J a F B κ)
    (fun {_ _} f z => Stacks.GradedAlgebra.lift_naturality
      (tensorLift_ι J a F B κ) (tensorLift_smul J a F B κ)
      (fun {_ _} f m => TensorAlgebra.mapₛₗ_ι ((O ⋙ forget₂ CommRingCat RingCat).map f).hom
        (F.restrictₛₗ f) m)
      (fun {_ _} f r => TensorAlgebra.mapₛₗ_algebraMap
        ((O ⋙ forget₂ CommRingCat RingCat).map f).hom (F.restrictₛₗ f) r)
      (fun _ _ h₁ h₂ => TensorAlgebra.ringHom_ext h₁ h₂) f z)

/-! #### The exterior algebra -/

/-- The degree-one generator of the restriction of scalars squares to zero as soon as the
generator it comes from does. -/
theorem genLin_sq_eq_zero (hκ : SquareZero κ) (X : Cᵒᵖ) (m : F.obj X) :
    (B.restrictScalars (toRingCatMap J a)).genLin (restrictGen J a F B κ) X m *
        (B.restrictScalars (toRingCatMap J a)).genLin (restrictGen J a F B κ) X m = 0 := by
  rw [Stacks.GradedAlgebra.genLin_apply,
    (B.restrictScalars (toRingCatMap J a)).incl_mul_incl,
    show ((B.restrictScalars (toRingCatMap J a)).mul 1 1).app X
        (PresheafOfModules.Hom.app (restrictGen J a F B κ) X m)
        (PresheafOfModules.Hom.app (restrictGen J a F B κ) X m) = 0 from
      hκ X (PresheafOfModules.Hom.app (sheafifyUnit (toRingCatMap J a) F) X m)]
  exact (B.restrictScalars (toRingCatMap J a)).incl_zero (1 + 1)

/-- The existence statement from which the properties of `exteriorLift` are read. -/
private abbrev exteriorLiftEx (hκ : SquareZero κ) (X : Cᵒᵖ) :=
  ExteriorAlgebra.exists_liftRingHom (restrictScalars_smul_mul_eq J a B)
    (restrictScalars_mul_smul_eq J a B)
    ((B.restrictScalars (toRingCatMap J a)).genLin (restrictGen J a F B κ) X)
    (genLin_sq_eq_zero J a F B κ hκ X)

/-- The lift of a square-zero degree-one generator to a ring homomorphism out of the
sectionwise exterior algebra, by `ExteriorAlgebra.lift`. -/
noncomputable def exteriorLift (hκ : SquareZero κ) (X : Cᵒᵖ) :
    ExteriorAlgebra ((O ⋙ forget₂ CommRingCat RingCat).obj X) (F.obj X) →+*
      (B.restrictScalars (toRingCatMap J a)).Total X :=
  (ExteriorAlgebra.exists_liftRingHom (restrictScalars_smul_mul_eq J a B)
    (restrictScalars_mul_smul_eq J a B)
    ((B.restrictScalars (toRingCatMap J a)).genLin (restrictGen J a F B κ) X)
    (genLin_sq_eq_zero J a F B κ hκ X)).choose

theorem exteriorLift_ι (hκ : SquareZero κ) (X : Cᵒᵖ) (m : F.obj X) :
    exteriorLift J a F B κ hκ X (ExteriorAlgebra.ι _ m) =
      (B.restrictScalars (toRingCatMap J a)).incl 1
        (PresheafOfModules.Hom.app (restrictGen J a F B κ) X m) :=
  (exteriorLiftEx J a F B κ hκ X).choose_spec.1 m

theorem exteriorLift_smul (hκ : SquareZero κ) (X : Cᵒᵖ)
    (r : (O ⋙ forget₂ CommRingCat RingCat).obj X)
    (z : ExteriorAlgebra ((O ⋙ forget₂ CommRingCat RingCat).obj X) (F.obj X)) :
    exteriorLift J a F B κ hκ X (r • z) = r • exteriorLift J a F B κ hκ X z :=
  (exteriorLiftEx J a F B κ hκ X).choose_spec.2 r z

/-- **The presheaf-level universal property of the sectionwise exterior algebra.** This is the
hypothesis `huniv` of `Stacks.GradedAlgebra.isExteriorAlgebra_sheafify`. -/
theorem existsUnique_exteriorUnitalHom (hκ : SquareZero κ) :
    ∃! g : Stacks.GradedAlgebra.UnitalHom (extPowGradedAlgebra F).extend
      (B.restrictScalars (toRingCatMap J a)),
      ∀ (X : Cᵒᵖ) (s : F.obj X),
        PresheafOfModules.Hom.app (g.app 1) X
            (PresheafOfModules.Hom.app (extPowGen F) X s) =
          κ.val.app X (PresheafOfModules.Hom.app (sheafifyUnit (toRingCatMap J a) F) X s) :=
  Stacks.GradedAlgebra.existsUnique_unitalHom
    (A := extPowGradedAlgebra F) (gen := extPowGen F)
    (iota := fun X => ExteriorAlgebra.ι ((O ⋙ forget₂ CommRingCat RingCat).obj X))
    (lamRestrict := fun f => ExteriorAlgebra.mapₛₗ
      ((O ⋙ forget₂ CommRingCat RingCat).map f).hom (F.restrictₛₗ f))
    (Φ := exteriorLift J a F B κ hκ)
    (fun n X => extPowSections n F X)
    (fun _ _ _ _ _ => rfl) (fun _ => rfl) (fun X m => extPowGen_coe F X m)
    (fun n {_ _} f x => extPowSections_map n F f x)
    (exteriorLift_ι J a F B κ hκ) (exteriorLift_smul J a F B κ hκ)
    (fun {_ _} f z => Stacks.GradedAlgebra.lift_naturality
      (exteriorLift_ι J a F B κ hκ) (exteriorLift_smul J a F B κ hκ)
      (fun {_ _} f m => ExteriorAlgebra.mapₛₗ_ι
        ((O ⋙ forget₂ CommRingCat RingCat).map f).hom (F.restrictₛₗ f) m)
      (fun {_ _} f r => ExteriorAlgebra.mapₛₗ_algebraMap
        ((O ⋙ forget₂ CommRingCat RingCat).map f).hom (F.restrictₛₗ f) r)
      (fun _ _ h₁ h₂ => ExteriorAlgebra.ringHom_ext h₁ h₂) f z)

/-! #### The symmetric algebra -/

/-- A pairwise-commuting degree-one generator restricts to one whose image commutes, in the
form `Stacks.GradedAlgebra.liftTotal` consumes. -/
theorem genCommutes_restrictGen (hκ : PairwiseCommutes κ) :
    (B.restrictScalars (toRingCatMap J a)).GenCommutes (restrictGen J a F B κ) :=
  fun X x y => hκ X (PresheafOfModules.Hom.app (sheafifyUnit (toRingCatMap J a) F) X x)
    (PresheafOfModules.Hom.app (sheafifyUnit (toRingCatMap J a) F) X y)

/-- The lift of a pairwise-commuting degree-one generator to a ring homomorphism out of the
sectionwise symmetric algebra, by `SymmetricAlgebra.liftComm`. -/
noncomputable def symmetricLift (hκ : PairwiseCommutes κ) (X : Cᵒᵖ) :
    SymmetricAlgebra ((O ⋙ forget₂ CommRingCat RingCat).obj X) (F.obj X) →+*
      (B.restrictScalars (toRingCatMap J a)).Total X :=
  SymmetricAlgebra.liftComm (restrictScalars_smul_mul_eq J a B)
    (restrictScalars_mul_smul_eq J a B)
    ((B.restrictScalars (toRingCatMap J a)).genLin (restrictGen J a F B κ) X)
    ((B.restrictScalars (toRingCatMap J a)).genLin_mul_comm (restrictGen J a F B κ)
      (genCommutes_restrictGen J a F B κ hκ) X)

theorem symmetricLift_ι (hκ : PairwiseCommutes κ) (X : Cᵒᵖ) (m : F.obj X) :
    symmetricLift J a F B κ hκ X (SymmetricAlgebra.ι _ _ m) =
      (B.restrictScalars (toRingCatMap J a)).incl 1
        (PresheafOfModules.Hom.app (restrictGen J a F B κ) X m) :=
  SymmetricAlgebra.liftComm_ι m

theorem symmetricLift_smul (hκ : PairwiseCommutes κ) (X : Cᵒᵖ)
    (r : (O ⋙ forget₂ CommRingCat RingCat).obj X)
    (z : SymmetricAlgebra ((O ⋙ forget₂ CommRingCat RingCat).obj X) (F.obj X)) :
    symmetricLift J a F B κ hκ X (r • z) = r • symmetricLift J a F B κ hκ X z :=
  SymmetricAlgebra.liftComm_smul r z

/-- **The presheaf-level universal property of the sectionwise symmetric algebra.** This is the
hypothesis `huniv` of `Stacks.GradedAlgebra.isSymmetricAlgebra_sheafify`. -/
theorem existsUnique_symmetricUnitalHom (hκ : PairwiseCommutes κ) :
    ∃! g : Stacks.GradedAlgebra.UnitalHom (symPowGradedAlgebra F).extend
      (B.restrictScalars (toRingCatMap J a)),
      ∀ (X : Cᵒᵖ) (s : F.obj X),
        PresheafOfModules.Hom.app (g.app 1) X
            (PresheafOfModules.Hom.app (symPowGen F) X s) =
          κ.val.app X (PresheafOfModules.Hom.app (sheafifyUnit (toRingCatMap J a) F) X s) :=
  Stacks.GradedAlgebra.existsUnique_unitalHom
    (A := symPowGradedAlgebra F) (gen := symPowGen F)
    (iota := fun X => SymmetricAlgebra.ι ((O ⋙ forget₂ CommRingCat RingCat).obj X) (F.obj X))
    (lamRestrict := fun f => SymmetricAlgebra.mapₛₗ
      ((O ⋙ forget₂ CommRingCat RingCat).map f).hom (F.restrictₛₗ f))
    (Φ := symmetricLift J a F B κ hκ)
    (fun n X => symPowSections n F X)
    (fun _ _ _ _ _ => rfl) (fun _ => rfl) (fun X m => symPowGen_coe F X m)
    (fun n {_ _} f x => symPowSections_map n F f x)
    (symmetricLift_ι J a F B κ hκ) (symmetricLift_smul J a F B κ hκ)
    (fun {_ _} f z => Stacks.GradedAlgebra.lift_naturality
      (symmetricLift_ι J a F B κ hκ) (symmetricLift_smul J a F B κ hκ)
      (fun {_ _} f m => SymmetricAlgebra.mapₛₗ_ι
        ((O ⋙ forget₂ CommRingCat RingCat).map f).hom (F.restrictₛₗ f) m)
      (fun {_ _} f r => SymmetricAlgebra.mapₛₗ_algebraMap
        ((O ⋙ forget₂ CommRingCat RingCat).map f).hom (F.restrictₛₗ f) r)
      (fun _ _ h₁ h₂ => SymmetricAlgebra.ringHom_ext h₁ h₂) f z)

end Universal

end SheafOfModules.GradedAlgebra


/-! ### Transport along an equality of degrees -/

namespace Stacks.GradedAlgebra

section Transport

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {R₀ : Cᵒᵖ ⥤ RingCat.{t}} {R : Sheaf J RingCat.{t}}

/-- **The multiplication of a sheafified graded algebra, transported to the sum of the degrees
and read on local lifts.** This is `Stacks.GradedAlgebra.sheafify_mul_restrict` with the degree
of the target given as a separate parameter together with the equation fixing it, which is the
form the `tensorPieceIso_mul_left` field of `SheafOfModules.TensorExteriorSymmetricAlgebras`
states its multiplication in. The transport is discharged by `subst`, which is possible only
because the target degree is a variable here. -/
theorem map_eq_mp_mul (α : R₀ ⟶ R.obj)
    [Presheaf.IsLocallyInjective J α] [Presheaf.IsLocallySurjective J α]
    [J.WEqualsLocallyBijective AddCommGrpCat.{a}] [HasWeakSheafify J AddCommGrpCat.{a}]
    {P : ℤ → PresheafOfModules.{a} R₀} (A : Stacks.GradedAlgebra P) (i j k : ℤ)
    (h : i + j = k) {U V : Cᵒᵖ} (g : U ⟶ V)
    (b₁ : ((A.sheafify α).piece i).val.obj U) (b₂ : ((A.sheafify α).piece j).val.obj U)
    (u₀ : (P i).obj V) (w₀ : (P j).obj V)
    (hu : PresheafOfModules.Hom.app (PresheafOfModules.sheafifyUnit α (P i)) V u₀ =
      ((A.sheafify α).piece i).val.map g b₁)
    (hw : PresheafOfModules.Hom.app (PresheafOfModules.sheafifyUnit α (P j)) V w₀ =
      ((A.sheafify α).piece j).val.map g b₂) :
    ((A.sheafify α).piece k).val.map g
        (Eq.mp (congrArg (fun l : ℤ => (((A.sheafify α).piece l).val.obj U : Type a)) h)
          (((A.sheafify α).mul i j).app U b₁ b₂)) =
      PresheafOfModules.Hom.app (PresheafOfModules.sheafifyUnit α (P k)) V
        (Eq.mp (congrArg (fun l : ℤ => ((P l).obj V : Type a)) h) ((A.mul i j).app V u₀ w₀)) := by
  subst h
  exact A.sheafify_mul_restrict α i j g b₁ b₂ u₀ w₀ hu hw

end Transport

end Stacks.GradedAlgebra

/-! ### The degree-zero piece of the exterior algebra -/

namespace ExteriorAlgebra

variable (R : Type*) [CommRing R] (M : Type*) [AddCommGroup M] [Module R M]

/-- **The degree-zero exterior power is the base ring**, by injectivity of the structure map,
with the identification normalized so that the structure map *is* `algebraMap`.

Mathlib's `exteriorPower.zeroEquiv` is the same equivalence in the other direction, built from
`exteriorPower.ιMulti` instead; this spelling is the exterior analogue of the repository's own
`TensorAlgebra.gradedPieceZeroEquiv` and `SymmetricAlgebra.symmetricPowerZeroEquiv`, and is the
one for which `PresheafOfModules.extPowZeroIso` below has a `rfl`-level characterization of its
sections. See the implementation notes. -/
noncomputable def exteriorPowerZeroEquiv : R ≃ₗ[R] ⋀[R]^0 M :=
  (LinearEquiv.ofInjective (Algebra.linearMap R (ExteriorAlgebra R M))
      (algebraMap_leftInverse M).injective).trans
    (LinearEquiv.ofEq _ _ (by
      simp only [exteriorPower, pow_zero]
      exact (Submodule.one_eq_range (R := R) (A := ExteriorAlgebra R M)).symm))

@[simp]
theorem exteriorPowerZeroEquiv_apply (r : R) :
    (exteriorPowerZeroEquiv R M r : ExteriorAlgebra R M) = algebraMap R _ r := rfl

end ExteriorAlgebra

namespace PresheafOfModules

section ExtPowZero

variable {C : Type u} [Category.{v} C] {O : Cᵒᵖ ⥤ CommRingCat.{w}}
  (F : PresheafOfModules.{w} (O ⋙ forget₂ _ RingCat))

/-- `ExteriorAlgebra.exteriorPowerZeroEquiv` with its type spelled at the sections of
`PresheafOfModules.unit` and of `PresheafOfModules.extPow`. -/
noncomputable def extPowZeroApp (X : Cᵒᵖ) :
    (PresheafOfModules.unit (O ⋙ forget₂ _ RingCat)).obj X ≃ₗ[(O ⋙ forget₂ _ RingCat).obj X]
      (extPow 0 F).obj X :=
  ExteriorAlgebra.exteriorPowerZeroEquiv _ _

/-- **The zeroth sectionwise exterior power is the free presheaf of modules of rank one.** -/
noncomputable def extPowZeroIso :
    PresheafOfModules.unit (O ⋙ forget₂ _ RingCat) ≅ extPow 0 F :=
  PresheafOfModules.isoMk (fun X => (extPowZeroApp F X).toModuleIso) fun {X Y} f => by
    refine ModuleCat.hom_ext (LinearMap.ext fun r => Subtype.ext ?_)
    exact (ExteriorAlgebra.mapₛₗ_algebraMap ((O ⋙ forget₂ _ RingCat).map f).hom
      (F.restrictₛₗ f) r).symm

/-- The degree-one identification of the sectionwise tensor powers *is* the degree-one
generator of the sectionwise tensor algebra. -/
theorem tensorPowOneIso_hom : (tensorPowOneIso F).hom = tensorPowGen F :=
  PresheafOfModules.hom_ext fun _ =>
    ModuleCat.hom_ext (LinearMap.ext fun _ => Subtype.ext rfl)

/-- The inverse of an isomorphism of presheaves of modules recovers `x` from `y = e.hom x`. -/
private theorem hom_inv_app_eq_of_hom_app_eq {R : Cᵒᵖ ⥤ RingCat.{w}} {M N : PresheafOfModules.{w} R}
    (e : M ≅ N) {X : Cᵒᵖ} {x : M.obj X} {y : N.obj X}
    (h : PresheafOfModules.Hom.app e.hom X x = y) : PresheafOfModules.Hom.app e.inv X y = x := by
  rw [← h, ← comp_app_apply, e.hom_inv_id]
  rfl

/-- The degree-zero identification of the sectionwise tensor powers carries the algebra unit
back to `1`. -/
theorem tensorPowZeroIso_inv_one (X : Cᵒᵖ) :
    PresheafOfModules.Hom.app (tensorPowZeroIso F).inv X ((tensorPowOne F).eval X) =
      unitOneSection (O ⋙ forget₂ _ RingCat) X :=
  hom_inv_app_eq_of_hom_app_eq _
    (Subtype.ext (map_one (algebraMap ((O ⋙ forget₂ CommRingCat RingCat).obj X)
      (TensorAlgebra ((O ⋙ forget₂ CommRingCat RingCat).obj X) (F.obj X)))))

/-- The degree-zero identification of the sectionwise exterior powers carries the algebra unit
back to `1`. -/
theorem extPowZeroIso_inv_one (X : Cᵒᵖ) :
    PresheafOfModules.Hom.app (extPowZeroIso F).inv X ((extPowOne F).eval X) =
      unitOneSection (O ⋙ forget₂ _ RingCat) X :=
  hom_inv_app_eq_of_hom_app_eq _
    (Subtype.ext (map_one (algebraMap ((O ⋙ forget₂ CommRingCat RingCat).obj X)
      (ExteriorAlgebra ((O ⋙ forget₂ CommRingCat RingCat).obj X) (F.obj X)))))

end ExtPowZero

end PresheafOfModules

/-! ### The sectionwise tensor-power recursion on products -/

namespace PresheafOfModules

section Recursion

variable {C : Type u} [Category.{v} C] {O : Cᵒᵖ ⥤ CommRingCat.{w}}
  (F : PresheafOfModules.{w} (O ⋙ forget₂ CommRingCat RingCat))

/-- Transport of a local section of a sectionwise tensor power along an equality of degrees does
not change it, read in the tensor algebra. -/
theorem eq_mp_tensorPow_coe {m k : ℕ} (hmk : m = k) {Y : Cᵒᵖ} (z : (tensorPow m F).obj Y)
    (p : ((tensorPow m F).obj Y : Type w) = ((tensorPow k F).obj Y : Type w)) :
    (tensorPowSections k F Y (Eq.mp p z) :
        TensorAlgebra ((O ⋙ forget₂ CommRingCat RingCat).obj Y) (F.obj Y)) =
      (tensorPowSections m F Y z :
        TensorAlgebra ((O ⋙ forget₂ CommRingCat RingCat).obj Y) (F.obj Y)) := by
  subst hmk
  rfl

/-- The recursion isomorphism of the sectionwise tensor powers, read on a pure tensor. The
degrees are variables throughout; see the module docstring for why none of them is a numeral. -/
theorem tensorPowTensorIso_hom_tmul (i j k : ℕ) (hij : i + j = k) (Y : Cᵒᵖ)
    (u : (tensorPow i F).obj Y) (ww : (tensorPow j F).obj Y)
    (p : ((tensorPow (i + j) F).obj Y : Type w) = ((tensorPow k F).obj Y : Type w)) :
    PresheafOfModules.Hom.app (tensorPowTensorIso F i j k hij).hom Y (u ⊗ₜ ww) =
      Eq.mp p (((tensorPowGradedAlgebra F).extend.mul (i : ℤ) (j : ℤ)).app Y u ww) := by
  refine Subtype.ext ?_
  refine Eq.trans (TensorAlgebra.mulGradedPieceEquivOfEq_tmul i j k hij
    (tensorPowSections i F Y u) (tensorPowSections j F Y ww)) ?_
  exact (eq_mp_tensorPow_coe F hij
    (((tensorPowGradedAlgebra F).extend.mul (i : ℤ) (j : ℤ)).app Y u ww) p).symm

/-- The inverse recursion isomorphism of the sectionwise tensor powers, read on the product of
two homogeneous local sections. -/
theorem tensorPowIsoTensor_hom_eq_mp (i j k : ℕ) (hij : i + j = k) (Y : Cᵒᵖ)
    (u : (tensorPow i F).obj Y) (ww : (tensorPow j F).obj Y)
    (p : ((tensorPow (i + j) F).obj Y : Type w) = ((tensorPow k F).obj Y : Type w)) :
    PresheafOfModules.Hom.app (tensorPowIsoTensor F i j k hij).hom Y
        (Eq.mp p (((tensorPowGradedAlgebra F).extend.mul (i : ℤ) (j : ℤ)).app Y u ww)) =
      u ⊗ₜ ww := by
  refine Eq.trans (congrArg (fun z => PresheafOfModules.Hom.app
      (tensorPowIsoTensor F i j k hij).hom Y z)
    (tensorPowTensorIso_hom_tmul F i j k hij Y u ww p).symm) ?_
  exact PresheafOfModules.hom_congr_apply'
    (tensorPowTensorIso F i j k hij).hom_inv_id Y (u ⊗ₜ ww)

end Recursion

end PresheafOfModules

/-! ### The degree-zero and degree-one identifications -/

namespace SheafOfModules

section LowDegrees

open CategoryTheory.Sheaf PresheafOfModules

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  {O : Cᵒᵖ ⥤ CommRingCat.{w}} {Osharp : Sheaf J CommRingCat.{w}} (a : O ⟶ Osharp.obj)
  [Presheaf.IsLocallyInjective J (toRingCatMap J a)]
  [Presheaf.IsLocallySurjective J (toRingCatMap J a)]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]
  (F : PresheafOfModules.{w} (O ⋙ forget₂ CommRingCat RingCat))

/-- **The `e0` hypothesis of `SheafOfModules.tensorPowerSheafifyIso`** for the family of
sectionwise tensor powers: the sheafification of the zeroth tensor power is the structure
sheaf. -/
noncomputable def sheafifyTensorPowZeroIso :
    (moduleSheafification J a).obj (tensorPow 0 F) ≅ SheafOfModules.unit (toRingCat J Osharp) :=
  (moduleSheafification J a).mapIso (tensorPowZeroIso F).symm ≪≫
    sheafificationObjUnitIso (toRingCatMap J a)

/-- The `e0` hypothesis of `SheafOfModules.tensorPowerSheafifyIso` for the family of
sectionwise exterior powers. -/
noncomputable def sheafifyExtPowZeroIso :
    (moduleSheafification J a).obj (extPow 0 F) ≅ SheafOfModules.unit (toRingCat J Osharp) :=
  (moduleSheafification J a).mapIso (extPowZeroIso F).symm ≪≫
    sheafificationObjUnitIso (toRingCatMap J a)

/-- The sheafified comparison with the structure sheaf, read on the unit image of a section of
`P` whose image under the inverse of `e` is the unit section, is `1`. -/
private theorem sheafifyZeroIso_hom_one
    {P : PresheafOfModules.{w} (O ⋙ forget₂ CommRingCat RingCat)}
    (e : PresheafOfModules.unit (O ⋙ forget₂ CommRingCat RingCat) ≅ P) (U : Cᵒᵖ) (z : P.obj U)
    (hz : PresheafOfModules.Hom.app e.inv U z =
      unitOneSection (O ⋙ forget₂ CommRingCat RingCat) U) :
    ((moduleSheafification J a).mapIso e.symm ≪≫
        sheafificationObjUnitIso (toRingCatMap J a)).hom.val.app U
      (PresheafOfModules.Hom.app (moduleSheafificationUnit J a P) U z) =
      (1 : (toRingCat J Osharp).obj.obj U) := by
  change (sheafificationObjUnitIso (toRingCatMap J a)).hom.val.app U
      (((moduleSheafification J a).map e.inv).val.app U
        (PresheafOfModules.Hom.app (moduleSheafificationUnit J a P) U z)) = _
  rw [unit_naturality_apply, hz]
  exact (sheafificationObjUnitIso_hom_unit (toRingCatMap J a) U
    (unitOneSection (O ⋙ forget₂ CommRingCat RingCat) U)).trans
      (map_one ((toRingCatMap J a).app U).hom)

/-- **The degree-zero identification of the sheafified sectionwise tensor algebra takes the
algebra unit to `1`.** This is the `tensorPieceIso_zero` field of the bundle. -/
theorem sheafifyTensorPowZeroIso_hom_one (U : Cᵒᵖ) :
    (sheafifyTensorPowZeroIso J a F).hom.val.app U
        (PresheafOfModules.Hom.app (moduleSheafificationUnit J a (tensorPow 0 F)) U
          ((tensorPowOne F).eval U)) =
      (1 : (toRingCat J Osharp).obj.obj U) :=
  sheafifyZeroIso_hom_one J a _ U _ (tensorPowZeroIso_inv_one F U)

/-- **The degree-zero identification of the sheafified sectionwise exterior algebra takes the
algebra unit to `1`.** This is the `exteriorPieceIso_zero_one` field of the bundle. -/
theorem sheafifyExtPowZeroIso_hom_one (U : Cᵒᵖ) :
    (sheafifyExtPowZeroIso J a F).hom.val.app U
        (PresheafOfModules.Hom.app (moduleSheafificationUnit J a (extPow 0 F)) U
          ((extPowOne F).eval U)) =
      (1 : (toRingCat J Osharp).obj.obj U) :=
  sheafifyZeroIso_hom_one J a _ U _ (extPowZeroIso_inv_one F U)

end LowDegrees

end SheafOfModules


/-! ### The inhabitant -/

namespace SheafOfModules

section Inhabitant

open CategoryTheory.Sheaf CategoryTheory.Limits PresheafOfModules

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  {O : Cᵒᵖ ⥤ CommRingCat.{w}} {Osharp : Sheaf J CommRingCat.{w}} (a : O ⟶ Osharp.obj)
  [Presheaf.IsLocallyInjective J (toRingCatMap J a)]
  [Presheaf.IsLocallySurjective J (toRingCatMap J a)]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]
  (F : PresheafOfModules.{w} (O ⋙ forget₂ CommRingCat RingCat))

/-- Countable coproducts of sheaves of modules, stated directly: instance search for
`HasColimit (Discrete.functor _)` in `SheafOfModules` times out under Lean v4.35.0. -/
local instance : HasColimitsOfShape (Discrete ℕ) (SheafOfModules.{w} (toRingCat J Osharp)) :=
  haveI := PresheafOfModules.hasColimitsOfShape (toRingCat J Osharp).obj (Discrete ℕ)
  SheafOfModules.instHasColimitsOfShapeOfPresheafOfModulesObjFunctorOppositeRingCatIsSheaf
    (toRingCat J Osharp) (Discrete ℕ)

/-- **The tensor-algebra universal property of the sheafified sectionwise tensor algebra.** -/
theorem isTensorAlgebra_sectionwiseTensorAlgebra :
    GradedAlgebra.IsTensorAlgebra (sectionwiseTensorAlgebra J a F)
      (sectionwiseTensorAlgebraGen J a F) :=
  (tensorPowGradedAlgebra F).extend.isTensorAlgebra_sheafify (toRingCatMap J a)
    (tensorPowGen F) fun B κ => GradedAlgebra.existsUnique_tensorUnitalHom J a F B κ

/-- **The exterior-algebra universal property of the sheafified sectionwise exterior
algebra.** -/
theorem isExteriorAlgebra_sectionwiseExteriorAlgebra :
    GradedAlgebra.IsExteriorAlgebra (sectionwiseExteriorAlgebra J a F)
      (sectionwiseExteriorAlgebraGen J a F) :=
  (extPowGradedAlgebra F).extend.isExteriorAlgebra_sheafify (toRingCatMap J a)
    (extPowGen F) (fun X x => extPowGen_sq_eq_zero F X x)
    fun B κ hκ => GradedAlgebra.existsUnique_exteriorUnitalHom J a F B κ hκ

/-- **The symmetric-algebra universal property of the sheafified sectionwise symmetric
algebra.** -/
theorem isSymmetricAlgebra_sectionwiseSymmetricAlgebra :
    GradedAlgebra.IsSymmetricAlgebra (sectionwiseSymmetricAlgebra J a F)
      (sectionwiseSymmetricAlgebraGen J a F) :=
  (symPowGradedAlgebra F).extend.isSymmetricAlgebra_sheafify (toRingCatMap J a)
    (symPowGen F) (fun X _ _ => symPowMul_self_comm F 1 X _ _)
    fun B κ hκ => GradedAlgebra.existsUnique_symmetricUnitalHom J a F B κ hκ

/-- **The identification of the degree-`n` piece of the sheafified sectionwise tensor algebra
with the `n`-fold tensor power.** -/
noncomputable def sectionwiseTensorPieceIso (n : ℕ) :
    (sectionwiseTensorAlgebra J a F).piece (n : ℤ) ≅
      tensorPower J ((moduleSheafification J a).obj F) n :=
  tensorPowerSheafifyIso J a (Q := fun k => tensorPow k F)
    (sheafifyTensorPowZeroIso J a F) (sheafifyTensorPowOneIso J a F)
    (fun k => tensorPowRecursionIso F k) n

/-- The degree-one identification is inverse to the degree-one generator. -/
theorem sectionwiseTensorPieceIso_one :
    sectionwiseTensorAlgebraGen J a F ≫ (sectionwiseTensorPieceIso J a F 1).hom =
      𝟙 ((moduleSheafification J a).obj F) := by
  have h : sectionwiseTensorAlgebraGen J a F ≫ (sectionwiseTensorPieceIso J a F 1).hom =
      (moduleSheafification J a).map ((tensorPowOneIso F).hom ≫ (tensorPowOneIso F).inv) := by
    rw [Functor.map_comp, tensorPowOneIso_hom]
    rfl
  rw [h, (tensorPowOneIso F).hom_inv_id]
  exact (moduleSheafification J a).map_id F

/-- The degree-zero identification takes the algebra unit to `1`. -/
theorem sectionwiseTensorPieceIso_zero (U : Cᵒᵖ) :
    (sectionwiseTensorPieceIso J a F 0).hom.val.app U
        ((sectionwiseTensorAlgebra J a F).one.eval U) =
      (1 : (toRingCat J Osharp).obj.obj U) :=
  sheafifyTensorPowZeroIso_hom_one J a F U

/-- The degree-zero identification of the exterior algebra. -/
noncomputable def sectionwiseExteriorPieceZeroIso :
    (sectionwiseExteriorAlgebra J a F).piece 0 ≅
      tensorPower J ((moduleSheafification J a).obj F) 0 :=
  sheafifyExtPowZeroIso J a F

/-- The degree-zero identification of the exterior algebra takes the algebra unit to `1`. -/
theorem sectionwiseExteriorPieceZeroIso_one (U : Cᵒᵖ) :
    (sectionwiseExteriorPieceZeroIso J a F).hom.val.app U
        ((sectionwiseExteriorAlgebra J a F).one.eval U) =
      (1 : (toRingCat J Osharp).obj.obj U) :=
  sheafifyExtPowZeroIso_hom_one J a F U

/-- The direct-sum comparison of the tensor powers with the homogeneous pieces. -/
noncomputable def sectionwiseTensorDirectSumIso :
    (∐ fun n : ℕ => tensorPower J ((moduleSheafification J a).obj F) n) ≅
      (∐ fun n : ℕ => (sectionwiseTensorAlgebra J a F).piece (n : ℤ)) :=
  Sigma.mapIso fun n => (sectionwiseTensorPieceIso J a F n).symm

theorem sectionwiseTensorDirectSumIso_ι (n : ℕ) :
    Sigma.ι (fun m : ℕ => tensorPower J ((moduleSheafification J a).obj F) m) n ≫
        (sectionwiseTensorDirectSumIso J a F).hom =
      (sectionwiseTensorPieceIso J a F n).inv ≫
        Sigma.ι (fun m : ℕ => (sectionwiseTensorAlgebra J a F).piece (m : ℤ)) n :=
  Sigma.ι_mapIso_hom (fun m => (sectionwiseTensorPieceIso J a F m).symm) n


/-- **Multiplication by a degree-one generator is tensor concatenation under the canonical
homogeneous identifications.** This is the `tensorPieceIso_mul_left` field of the bundle, and it
is the one field whose two sides are compared on arbitrary local sections rather than on unit
images: both lift on a covering sieve, and
`tensorPowerSheafifyIso_add_two_unit` settles the lifts. -/
theorem sectionwiseTensorPieceIso_mul_left_piece (n : ℕ) (U : Cᵒᵖ)
    (s : ((moduleSheafification J a).obj F).val.obj U)
    (x : ((sectionwiseTensorAlgebra J a F).piece ((n + 1 : ℕ) : ℤ)).val.obj U) :
    (sectionwiseTensorPieceIso J a F (n + 2)).hom.val.app U
        (Eq.mp (congrArg (fun k : ℤ =>
            (((sectionwiseTensorAlgebra J a F).piece k).val.obj U : Type w))
            (show (1 : ℤ) + ((n + 1 : ℕ) : ℤ) = ((n + 2 : ℕ) : ℤ) by omega))
          (((sectionwiseTensorAlgebra J a F).mul 1 ((n + 1 : ℕ) : ℤ)).app U
            ((sectionwiseTensorAlgebraGen J a F).val.app U s) x)) =
      ((PresheafOfModules.sheafificationAdjunction (R := Stacks.SheafOfModules.Tensor.ringSheaf
          Osharp)
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf Osharp).obj)).unit.app
      (PresheafOfModules.tensorObj ((moduleSheafification J a).obj F).val (tensorPower J
          ((moduleSheafification J a).obj F) (n + 1)).val)).app U
        (s ⊗ₜ[Osharp.obj.obj U]
          (sectionwiseTensorPieceIso J a F (n + 1)).hom.val.app U x) := by
  refine Stacks.eq_of_isSeparated
    (tensorPower J ((moduleSheafification J a).obj F) (n + 2))
    (J.intersection_covering (Stacks.liftSieve_mem (toRingCatMap J a) F s)
      (Stacks.liftSieve_mem (toRingCatMap J a) (tensorPow (n + 1) F) x)) ?_
  rintro Y f ⟨⟨s₁, hs₁⟩, ⟨y₁, hy₁⟩⟩
  obtain ⟨s₀, hs⟩ : ∃ s₀ : F.obj (op Y),
      PresheafOfModules.Hom.app (sheafifyUnit (toRingCatMap J a) F) (op Y) s₀ =
        ((moduleSheafification J a).obj F).val.map f.op s := ⟨s₁, hs₁⟩
  obtain ⟨y₀, hy⟩ : ∃ y₀ : (tensorPow (n + 1) F).obj (op Y),
      PresheafOfModules.Hom.app (sheafifyUnit (toRingCatMap J a) (tensorPow (n + 1) F))
          (op Y) y₀ =
        ((sectionwiseTensorAlgebra J a F).piece ((n + 1 : ℕ) : ℤ)).val.map f.op
          x := ⟨y₁, hy₁⟩
  have hx1 := (tensorPowGradedAlgebra F).extend.sheafifyGen_lift (toRingCatMap J a)
    (tensorPowGen F) f.op s s₀ hs
  have hz := tensorPowIsoTensor_hom_eq_mp F 1 (n + 1) (n + 2) (by omega) (op Y)
    (PresheafOfModules.Hom.app (tensorPowGen F) (op Y) s₀) y₀
    (congrArg (fun l : ℤ =>
      ((Stacks.GradedAlgebra.extendFamily (fun k => tensorPow k F) l).obj (op Y) : Type w))
      (show (1 : ℤ) + ((n + 1 : ℕ) : ℤ) = ((n + 2 : ℕ) : ℤ) by omega))
  -- the degree-one identification carries the generator back to the local lift
  have he1 : (sheafifyTensorPowOneIso J a F).hom.val.app (op Y)
      (PresheafOfModules.Hom.app (sheafifyUnit (toRingCatMap J a) (tensorPow 1 F)) (op Y)
        (PresheafOfModules.Hom.app (tensorPowGen F) (op Y) s₀)) =
      PresheafOfModules.Hom.app (sheafifyUnit (toRingCatMap J a) F) (op Y) s₀ := by
    refine Eq.trans (unit_naturality_apply (tensorPowOneIso F).inv (op Y) _) ?_
    refine congrArg (fun z => PresheafOfModules.Hom.app
      (sheafifyUnit (toRingCatMap J a) F) (op Y) z) ?_
    rw [← tensorPowOneIso_hom, ← comp_app_apply, (tensorPowOneIso F).hom_inv_id]
    rfl
  -- restrict the left-hand side and read it on unit images
  refine Eq.trans (PresheafOfModules.naturality_apply
      (sectionwiseTensorPieceIso J a F (n + 2)).hom.val f.op _).symm ?_
  refine Eq.trans (congrArg
    (fun z => (sectionwiseTensorPieceIso J a F (n + 2)).hom.val.app (op Y) z)
    (Stacks.GradedAlgebra.map_eq_mp_mul (toRingCatMap J a) (tensorPowGradedAlgebra F).extend
      1 ((n + 1 : ℕ) : ℤ) ((n + 2 : ℕ) : ℤ) (by omega) f.op _ x
      (PresheafOfModules.Hom.app (tensorPowGen F) (op Y) s₀) y₀ hx1 hy)) ?_
  rw [show sectionwiseTensorPieceIso J a F (n + 2) =
      tensorPowerSheafifyIso J a (Q := fun k => tensorPow k F)
        (sheafifyTensorPowZeroIso J a F)
        (sheafifyTensorPowOneIso J a F)
        (fun k => tensorPowRecursionIso F k) (n + 2) from rfl]
  have hkey := tensorPowerSheafifyIso_add_two_unit J a
    (Q := fun k => tensorPow k F) (F := (moduleSheafification J a).obj F)
    (sheafifyTensorPowZeroIso J a F) (sheafifyTensorPowOneIso J a F)
    (fun k => tensorPowRecursionIso F k) n (op Y) _
    (PresheafOfModules.Hom.app (tensorPowGen F) (op Y) s₀) y₀ hz
  refine Eq.trans hkey ?_
  -- restrict the right-hand side
  refine Eq.trans ?_ (PresheafOfModules.naturality_apply
    ((PresheafOfModules.sheafificationAdjunction (R := Stacks.SheafOfModules.Tensor.ringSheaf
        Osharp)
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf Osharp).obj)).unit.app
      (PresheafOfModules.tensorObj ((moduleSheafification J a).obj F).val (tensorPower J
          ((moduleSheafification J a).obj F) (n + 1)).val)) f.op _)
  refine congrArg (fun z => PresheafOfModules.Hom.app
    ((PresheafOfModules.sheafificationAdjunction (R := Stacks.SheafOfModules.Tensor.ringSheaf
        Osharp)
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf Osharp).obj)).unit.app
      (PresheafOfModules.tensorObj ((moduleSheafification J a).obj F).val (tensorPower J
          ((moduleSheafification J a).obj F) (n + 1)).val)) (op Y) z) ?_
  change _ = (PresheafOfModules.tensorObj ((moduleSheafification J a).obj F).val
      (tensorPower J ((moduleSheafification J a).obj F) (n + 1)).val).restrictₛₗ
    f.op (s ⊗ₜ (sectionwiseTensorPieceIso J a F (n + 1)).hom.val.app U x)
  rw [tensorObj_restrictₛₗ_tmul, he1]
  have h1 : (((moduleSheafification J a).obj F).val.restrictₛₗ f.op) s =
      PresheafOfModules.Hom.app (sheafifyUnit (toRingCatMap J a) F) (op Y) s₀ := hs.symm
  have h2 : ((tensorPower J ((moduleSheafification J a).obj F)
          (n + 1)).val.restrictₛₗ f.op)
        ((sectionwiseTensorPieceIso J a F (n + 1)).hom.val.app U x) =
      (tensorPowerSheafifyIso J a (Q := fun k => tensorPow k F)
          (sheafifyTensorPowZeroIso J a F)
          (sheafifyTensorPowOneIso J a F)
          (fun k => tensorPowRecursionIso F k) (n + 1)).hom.val.app (op Y)
        (PresheafOfModules.Hom.app (moduleSheafificationUnit J a (tensorPow (n + 1) F)) (op Y)
          y₀) := by
    refine Eq.trans (PresheafOfModules.naturality_apply
      (sectionwiseTensorPieceIso J a F (n + 1)).hom.val f.op x).symm ?_
    exact congrArg (fun z =>
      (sectionwiseTensorPieceIso J a F (n + 1)).hom.val.app (op Y) z) hy.symm
  rw [h1, h2]

/-- `SheafOfModules.sectionwiseTensorPieceIso_mul_left_piece` with the second factor taken in
the tensor power rather than in the homogeneous piece: this is the `tensorPieceIso_mul_left`
field of the bundle verbatim. -/
theorem sectionwiseTensorPieceIso_mul_left (n : ℕ) (U : Cᵒᵖ)
    (s : ((moduleSheafification J a).obj F).val.obj U)
    (x : (tensorPower J ((moduleSheafification J a).obj F) (n + 1)).val.obj U) :
    (sectionwiseTensorPieceIso J a F (n + 2)).hom.val.app U
        (Eq.mp (congrArg (fun k : ℤ =>
            (((sectionwiseTensorAlgebra J a F).piece k).val.obj U : Type w))
            (show (1 : ℤ) + ((n + 1 : ℕ) : ℤ) = ((n + 2 : ℕ) : ℤ) by omega))
          (((sectionwiseTensorAlgebra J a F).mul 1 ((n + 1 : ℕ) : ℤ)).app U
            ((sectionwiseTensorAlgebraGen J a F).val.app U s)
            ((sectionwiseTensorPieceIso J a F (n + 1)).inv.val.app U x))) =
      ((PresheafOfModules.sheafificationAdjunction (R := Stacks.SheafOfModules.Tensor.ringSheaf
          Osharp)
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf Osharp).obj)).unit.app
      (PresheafOfModules.tensorObj ((moduleSheafification J a).obj F).val (tensorPower J
          ((moduleSheafification J a).obj F) (n + 1)).val)).app U
        (s ⊗ₜ[Osharp.obj.obj U] x) := by
  refine Eq.trans (sectionwiseTensorPieceIso_mul_left_piece J a F n U s
    ((sectionwiseTensorPieceIso J a F (n + 1)).inv.val.app U x)) ?_
  refine congrArg (fun z => PresheafOfModules.Hom.app
    ((PresheafOfModules.sheafificationAdjunction (R := Stacks.SheafOfModules.Tensor.ringSheaf
        Osharp)
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf Osharp).obj)).unit.app
      (PresheafOfModules.tensorObj ((moduleSheafification J a).obj F).val (tensorPower J
          ((moduleSheafification J a).obj F) (n + 1)).val)) U
    (s ⊗ₜ[Osharp.obj.obj U] z)) ?_
  exact hom_congr_app_apply (sectionwiseTensorPieceIso J a F (n + 1)).inv_hom_id U x

/-- **The tensor, exterior and symmetric algebras of a sheaf of modules exist.** The three
algebras of Stacks Section 17.21, their three universal properties, the identification of the
homogeneous pieces of the tensor algebra with the sheafified tensor powers, and the two quotient
maps, assembled into an inhabitant of `SheafOfModules.TensorExteriorSymmetricAlgebras` for the
sheafification of an arbitrary presheaf of modules.

Each of the three algebras is the degreewise sheafification of its sectionwise counterpart; the
two quotient maps are not extra data but the homomorphisms the tensor algebra's universal
property produces from the exterior and symmetric generators. -/
noncomputable def tensorExteriorSymmetricAlgebras :
    TensorExteriorSymmetricAlgebras J ((moduleSheafification J a).obj F) where
  tensor := sectionwiseTensorAlgebra J a F
  tensorGenerator := sectionwiseTensorAlgebraGen J a F
  tensor_isTensorAlgebra := isTensorAlgebra_sectionwiseTensorAlgebra J a F
  tensorPieceIso := sectionwiseTensorPieceIso J a F
  tensorPieceIso_one := sectionwiseTensorPieceIso_one J a F
  tensorPieceIso_zero := sectionwiseTensorPieceIso_zero J a F
  tensorPieceIso_mul_left := sectionwiseTensorPieceIso_mul_left J a F
  tensorDirectSumIso := sectionwiseTensorDirectSumIso J a F
  tensorDirectSumIso_ι := sectionwiseTensorDirectSumIso_ι J a F
  tensorPiece_eq_zero_of_neg _ hn U x :=
    sectionwiseTensorAlgebra_piece_eq_zero_of_neg J a F hn U x
  exterior := sectionwiseExteriorAlgebra J a F
  exteriorGenerator := sectionwiseExteriorAlgebraGen J a F
  exterior_isExteriorAlgebra := isExteriorAlgebra_sectionwiseExteriorAlgebra J a F
  exteriorPieceIso_zero := sectionwiseExteriorPieceZeroIso J a F
  exteriorPieceIso_zero_one := sectionwiseExteriorPieceZeroIso_one J a F
  exteriorPiece_eq_zero_of_neg _ hn U x :=
    sectionwiseExteriorAlgebra_piece_eq_zero_of_neg J a F hn U x
  symmetric := sectionwiseSymmetricAlgebra J a F
  symmetricGenerator := sectionwiseSymmetricAlgebraGen J a F
  symmetric_isSymmetricAlgebra := isSymmetricAlgebra_sectionwiseSymmetricAlgebra J a F
  symmetricPiece_eq_zero_of_neg _ hn U x :=
    sectionwiseSymmetricAlgebra_piece_eq_zero_of_neg J a F hn U x
  tensorToExterior := (isTensorAlgebra_sectionwiseTensorAlgebra J a F).descAny
    (sectionwiseExteriorAlgebra J a F) (sectionwiseExteriorAlgebraGen J a F)
  tensorToExterior_extends := (isTensorAlgebra_sectionwiseTensorAlgebra J a F).descAny_extends
    (sectionwiseExteriorAlgebra J a F) (sectionwiseExteriorAlgebraGen J a F)
  tensorToSymmetric := (isTensorAlgebra_sectionwiseTensorAlgebra J a F).descAny
    (sectionwiseSymmetricAlgebra J a F) (sectionwiseSymmetricAlgebraGen J a F)
  tensorToSymmetric_extends := (isTensorAlgebra_sectionwiseTensorAlgebra J a F).descAny_extends
    (sectionwiseSymmetricAlgebra J a F) (sectionwiseSymmetricAlgebraGen J a F)

/-- **The bundle of Stacks Section 17.21 is inhabited** for the sheafification of any presheaf
of modules.

For a sheaf of modules `G` given in advance, take `O := Osharp.obj` and `a := 𝟙 Osharp.obj` and
`F := G.val`: the counit of the sheafification adjunction is an isomorphism
`(moduleSheafification J (𝟙 Osharp.obj)).obj G.val ≅ G`, so this gives the bundle for an object
*isomorphic* to `G`. Transporting a bundle along an isomorphism of the underlying sheaf of
modules is not proved here; a consumer that needs the bundle at `G` on the nose should either
use `SheafOfModules.TensorExteriorSymmetricAlgebras.tensorAlgebraIso` and its companions, which
is what makes the bundle a hypothesis rather than a chosen term, or supply that transport. -/
theorem nonempty_tensorExteriorSymmetricAlgebras :
    Nonempty (TensorExteriorSymmetricAlgebras J ((moduleSheafification J a).obj F)) :=
  ⟨tensorExteriorSymmetricAlgebras J a F⟩

end Inhabitant

end SheafOfModules


end
