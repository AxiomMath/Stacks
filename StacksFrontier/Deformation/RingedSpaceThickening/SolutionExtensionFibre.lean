module

public import StacksFrontier.Deformation.RingedSpaceThickening.SolutionIsomorphism
public import StacksFrontier.Deformation.RingedSpaceThickening.SquareZeroExtensionClasses

/-!
# Solutions of a ringed space deformation problem as a fibre of a map of `Ext¹` groups

Fix the data of the deformation problem of **Stacks 08U7**: a first order thickening
`t : (S, 𝒪_S) ⟶ (S', 𝒪_{S'})` with ideal `𝒥 = Ker(t^♯)`, a morphism `f : (X, 𝒪_X) ⟶ (S, 𝒪_S)`,
an `𝒪_X`-module `𝒢`, and a map `c : f^* 𝒥 ⟶ 𝒢`.  **Stacks 0GQ3** says the isomorphism classes
of solutions are canonically bijective to the fibre of

`Ext¹_{𝒪_X}(NL_{X/S'}, 𝒢) ⟶ Ext¹_{𝒪_X}(Lf^*NL_{S/S'}, 𝒢)`

over the image of the class `ξ ∈ Ext¹_{𝒪_S}(NL_{S/S'}, 𝒥)` of the extension `𝒪_{S'}` of `𝒪_S`
by `𝒥`.  The two `Ext¹` groups and the two maps between them are built in
`StacksFrontier/Deformation/RingedSpaceThickening/NaiveCotangentDerivedExt.lean`.  This file
identifies solutions with the square-zero extensions of `f^{-1}𝒪_{S'}`-algebras satisfying the
compatibility equation for `c`, and proves the bijection of the source's proof from the two
inputs that proof uses.

## Where the tag 0GQ3 is carried

The source's proof has three steps.  By **Stacks 0GPZ** applied to `X ⟶ S'`, classes in
`Ext¹_{𝒪_X}(NL_{X/S'}, 𝒢)` parametrize square-zero extensions of `f^{-1}𝒪_{S'}`-algebras.  By
**Stacks 0GQ1** applied to `X ⟶ S ⟶ S'` and `c`, such an extension admits an `S'`-morphism
compatible with `c` and `f` exactly when its class lands in the fibre over the image of `ξ`.
And a solution of **Stacks 08U7** is the same thing as an extension that does.

The third step is the one proved here, unconditionally: it is `toExtensionOverBase` with
`toExtensionOverBase_isSolutionFor`, and `ofExtensionOverBase`.  The first two enter
`solutionsEquivExtFibre` as its hypotheses `E` and `hcrit`, and `hcrit` *is* the assertion of
0GQ3 — "a class of extensions is a class of solutions exactly when it lands in that fibre".  So
no `@[stacks]` attribute belongs on anything in this file: on `solutionsEquivExtFibre` the tag
would sit on an assumption.  What remains once `E` and `hcrit` are granted is the restriction of
a bijection along a pointwise criterion, which is why `solutionsEquivExtFibre` is stated for an
arbitrary target and an arbitrary criterion: that is the whole of its content.

The tag is carried one module along, in
`StacksFrontier/Deformation/RingedSpaceThickening/DerivedExtensionClassCriterion.lean`, by
`AlgebraicGeometry.RingedSpaceThickening.solutionsEquivDerivedExtFibre` and by
`solutionsEquivDerivedExtFibre_apply`.  Those specialize the two declarations here to the `Ext¹`
groups of `StacksFrontier/Deformation/RingedSpaceThickening/NaiveCotangentDerivedExt.lean`, and
there `hcrit` is discharged rather than assumed: it is
`isSolutionClass_iff_eq_pullbackExtClass`, the **Stacks 0GQ1** criterion for the derived
pullback read on isomorphism classes of extensions.

## Main definitions

* `AlgebraicGeometry.RingedSpaceThickening.ExtensionOverBase`: the square-zero extensions
  `0 ⟶ 𝒢 ⟶ 𝒪_{X'} ⟶ 𝒪_X ⟶ 0` of `f^{-1}𝒪_{S'}`-algebras, as the solutions of **Stacks 08U7**
  over the identity thickening of `S'`; `ExtensionOverBase.IsSolutionFor` is the compatibility
  equation of **Stacks 08U7** for `c`, read on such an extension.
* `AlgebraicGeometry.RingedSpaceThickening.toExtensionOverBase` and `ofExtensionOverBase`: the
  passage between solutions and extensions satisfying that equation.
* `AlgebraicGeometry.RingedSpaceThickening.solutionSetoid`: isomorphism of solutions, as
  isomorphism of the underlying extensions.

## Main results

* `AlgebraicGeometry.RingedSpaceThickening.toExtensionOverBase_isSolutionFor` with
  `ofExtensionOverBase`: **a solution of Stacks 08U7 is the same thing as a square-zero
  extension of `f^{-1}𝒪_{S'}`-algebras satisfying the compatibility equation for `c`.**  This
  is the source's "of course this is the same thing as saying `𝒪_{X'}` is a solution of
  (91.7.0.1)", and it is unconditional: the two structures differ only in that equation, since
  a solution carries its morphism to `S'` as part of its data, so each is read off from the
  other with no further input.
* `AlgebraicGeometry.RingedSpaceThickening.isSolutionFor_id`: over the identity thickening of
  the base the compatibility equation holds for every extension, so that the solutions of
  **Stacks 08U7** there are exactly the square-zero extensions **Stacks 0GPZ** classifies.
* `AlgebraicGeometry.RingedSpaceThickening.solutionHomEquivOverBase` and
  `isomorphic_iff_isomorphic_overBase`: a morphism of solutions is the same thing as a morphism
  of the underlying extensions, so two solutions are isomorphic exactly when their underlying
  extensions are.  With `solutionSetoid_iff_isomorphic` this identifies the relation whose
  classes are counted with `AlgebraicGeometry.RingedSpaceThickening.Isomorphic`, the library's
  geometric isomorphism relation of **Stacks 08UC**.
* `AlgebraicGeometry.RingedSpaceThickening.solutionClassToExtClass_injective`: the class map is
  injective — two solutions whose underlying extensions have the same class are isomorphic.
  This needs nothing beyond the bijection `E`.
* `AlgebraicGeometry.RingedSpaceThickening.solutionsEquivExtFibre`: given a bijection `E` from
  the isomorphism classes of extensions to any target, and a criterion `hcrit` saying which
  classes are classes of solutions, the isomorphism classes of solutions are bijective to the
  subtype cut out by that criterion, by the constructed map `[X'] ↦ E [𝒪_{X'}]`, as
  `solutionsEquivExtFibre_apply` records.
* `AlgebraicGeometry.RingedSpaceThickening.nonempty_extFibre_of_nonempty`: the target subtype
  is nonempty as soon as a solution exists, which is the source's hypothesis in
  **Stacks 08UC**.

## Implementation notes

The passage between solutions and extensions is the pair of definitions `toExtensionOverBase`
and `ofExtensionOverBase`, not a bundled `Equiv`, and the two round-trip equations are not
stated.  They are true by `rfl`, but checking either asks the elaborator to compare two
instances of the `compatibility` field, whose type runs through
`MorphismOfThickenings.firstOrderIdealMap` — a tactic-built subtype whose first component is a
large term — and that comparison does not terminate in reasonable time.  Nothing below needs a
round trip: the class of a solution is read off through `toExtensionOverBase`, and surjectivity
of the class map is witnessed by a solution supplied by `hcrit` rather than by one rebuilt from
an extension.

For the same reason the `compatibility` field of `ofExtensionOverBase` introduces the morphism
of thickenings that the field's type binds, and only then appeals to the hypothesis, exactly as
`toExtensionOverBase` does.  Handing the hypothesis to the field as a term instead gives the
same definition, but it makes the elaborator compare two copies of
`MorphismOfThickenings.firstOrderIdealMap` at the expanded square rather than at that single
bound local, and the comparison then takes twenty-two minutes — twenty times the rest of this
file put together.

`solutionsEquivExtFibre` is stated for an arbitrary target type and criterion rather than for
the `Ext¹` groups of
`StacksFrontier/Deformation/RingedSpaceThickening/NaiveCotangentDerivedExt.lean` and the two maps
there.  That is both honest — it is the whole content of the statement once `E` and `hcrit` are
granted — and necessary: with the `Ext¹` groups of `D(𝒪_X)` substituted for the target, the
`rfl` proofs of `solutionClassToExtClass_mk` and `solutionsEquivExtFibre_apply` stop
elaborating in reasonable time.

## References

* [Stacks Project, Tag 0GQ3](https://stacks.math.columbia.edu/tag/0GQ3)
* [Stacks Project, Tag 08U7](https://stacks.math.columbia.edu/tag/08U7)
* [Stacks Project, Tag 0GPZ](https://stacks.math.columbia.edu/tag/0GPZ)
* [Stacks Project, Tag 0GQ0](https://stacks.math.columbia.edu/tag/0GQ0)
* [Stacks Project, Tag 0GQ1](https://stacks.math.columbia.edu/tag/0GQ1)
* [Stacks Project, Tag 08UC](https://stacks.math.columbia.edu/tag/08UC)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open RingedSpaceModuleAdjunction

universe u

namespace AlgebraicGeometry.RingedSpaceThickening

variable {X S S' : RingedSpace.{u, u}}

/-! ### Solutions and square-zero extensions of `f^{-1}𝒪_{S'}`-algebras -/

/-- The ideal `𝒥 = Ker(t^♯)` of a thickening of the base, pulled back to `S`: the `𝒪_S`-module
the prescribed map `c` of **Stacks 08U7** starts from, before pulling back along `f`. -/
abbrev baseIdealOnReduction (t : S ⟶ S') : SheafOfModules.{u} (structureSheafRing S) :=
  (modulePullback t).obj (AlgebraicGeometry.SheafOfModules.idealSheaf t)

/-- The square-zero extensions `0 ⟶ 𝒢 ⟶ 𝒪_{X'} ⟶ 𝒪_X ⟶ 0` of `f^{-1}𝒪_{S'}`-algebras, as the
solutions of the problem of **Stacks 08U7** over the identity thickening of `S'`.  These are
the objects **Stacks 0GPZ** classifies by `Ext¹_{𝒪_X}(NL_{X/S'}, 𝒢)`. -/
abbrev ExtensionOverBase (f : X ⟶ S) (t : S ⟶ S') (G : SheafOfModules.{u} (structureSheafRing X)) :=
  DeformationSolution (𝟙 S') (isFirstOrderThickening_id S') (f ≫ t) G 0

/-- The compatibility equation of **Stacks 08U7** for the prescribed map `c`, read on a
square-zero extension of `f^{-1}𝒪_{S'}`-algebras: the canonical first order factorization of
the ideal map of the square `(f, f')` is `c` under the identification of the ideal of `𝒪_{X'}`
with `𝒢`.  A solution of **Stacks 08U7** is exactly an extension satisfying it; see
`toExtensionOverBase` and `ofExtensionOverBase`. -/
def ExtensionOverBase.IsSolutionFor {t : S ⟶ S'} (ht : IsFirstOrderThickening t) {f : X ⟶ S}
    {G : SheafOfModules.{u} (structureSheafRing X)}
    (c : (modulePullback f).obj (baseIdealOnReduction t) ⟶ G)
    (P : ExtensionOverBase f t G) : Prop :=
  (MorphismOfThickenings.firstOrderIdealMap
      { X := X, X' := P.X', S := S, S' := S', i := P.i, t := t, f := f, f' := P.f',
        i_isThickening := P.i_firstOrder.1, t_isThickening := ht.1,
        comm := P.comm.trans (Category.comp_id _) } P.i_firstOrder ht).1 ≫ P.kernelIso.hom =
    (modulePushforward P.i).map c

/-- The square-zero extension of `f^{-1}𝒪_{S'}`-algebras underlying a solution of the problem
of **Stacks 08U7**: the same deformed space, thickening, morphism to `S'` and identification of
the ideal with `𝒢`, with the compatibility equation for `c` forgotten.  Over the identity
thickening of `S'` the compatibility equation is automatic, both of its sides being maps out of
a zero object. -/
def toExtensionOverBase {t : S ⟶ S'} {ht : IsFirstOrderThickening t} {f : X ⟶ S}
    {G : SheafOfModules.{u} (structureSheafRing X)}
    {c : (modulePullback f).obj (baseIdealOnReduction t) ⟶ G}
    (Q : DeformationSolution t ht f G c) : ExtensionOverBase f t G where
  X' := Q.X'
  i := Q.i
  f' := Q.f'
  i_firstOrder := Q.i_firstOrder
  comm := Q.comm.trans (Category.comp_id _).symm
  kernelIso := Q.kernelIso
  compatibility := by
    intro D
    refine IsZero.eq_of_src ?_ _ _
    exact isZero_modulePushforward_obj _
      (isZero_modulePullback_obj _
        (isZero_modulePullback_obj _ (isZero_idealSheaf_id S')))

/-- The extension underlying a solution satisfies the compatibility equation for `c`: that
equation is the solution's own last field.  This is one half of the source's "of course this is
the same thing as saying `𝒪_{X'}` is a solution of (91.7.0.1)". -/
theorem toExtensionOverBase_isSolutionFor {t : S ⟶ S'} {ht : IsFirstOrderThickening t}
    {f : X ⟶ S} {G : SheafOfModules.{u} (structureSheafRing X)}
    {c : (modulePullback f).obj (baseIdealOnReduction t) ⟶ G}
    (Q : DeformationSolution t ht f G c) :
    (toExtensionOverBase Q).IsSolutionFor ht c :=
  Q.compatibility

/-- A square-zero extension of `f^{-1}𝒪_{S'}`-algebras satisfying the compatibility equation
for `c` is a solution of the problem of **Stacks 08U7**.  This is the other half of the
source's "of course this is the same thing". -/
def ofExtensionOverBase {t : S ⟶ S'} (ht : IsFirstOrderThickening t) {f : X ⟶ S}
    {G : SheafOfModules.{u} (structureSheafRing X)}
    {c : (modulePullback f).obj (baseIdealOnReduction t) ⟶ G}
    (P : ExtensionOverBase f t G) (hP : P.IsSolutionFor ht c) :
    DeformationSolution t ht f G c where
  X' := P.X'
  i := P.i
  f' := P.f'
  i_firstOrder := P.i_firstOrder
  comm := P.comm.trans (Category.comp_id _)
  kernelIso := P.kernelIso
  compatibility := by
    intro D
    exact hP

/-- Over the identity thickening of the base the compatibility equation of **Stacks 08U7** is
automatic: both of its sides are maps out of `MorphismOfThickenings.reducedPullbackIdeal`, which
for a base thickening with zero ideal is a zero object.  So the solutions of **Stacks 08U7**
over `𝟙 S` are exactly the square-zero extensions of `f^{-1}𝒪_S`-algebras. -/
theorem isSolutionFor_id {f : X ⟶ S} {G : SheafOfModules.{u} (structureSheafRing X)}
    (c : (modulePullback f).obj (baseIdealOnReduction (𝟙 S)) ⟶ G)
    (P : ExtensionOverBase f (𝟙 S) G) :
    P.IsSolutionFor (isFirstOrderThickening_id S) c := by
  refine IsZero.eq_of_src ?_ _ _
  exact isZero_modulePushforward_obj _
    (isZero_modulePullback_obj _
      (isZero_modulePullback_obj _ (isZero_idealSheaf_id S)))

/-! ### Morphisms of solutions and morphisms of the underlying extensions -/

/-- **A morphism of solutions of Stacks 08U7 is the same thing as a morphism of the underlying
square-zero extensions of `f^{-1}𝒪_{S'}`-algebras.**  The three conditions of `SolutionHom` —
a morphism under `X`, a morphism over `S'`, the identity on `𝒢` — mention only the deformed
space, the thickening, the morphism to `S'` and the identification of the ideal with `𝒢`, and
`toExtensionOverBase` leaves all four untouched. -/
def solutionHomEquivOverBase {t : S ⟶ S'} {ht : IsFirstOrderThickening t} {f : X ⟶ S}
    {G : SheafOfModules.{u} (structureSheafRing X)}
    {c : (modulePullback f).obj (baseIdealOnReduction t) ⟶ G}
    (Q₁ Q₂ : DeformationSolution t ht f G c) :
    SolutionHom Q₁ Q₂ ≃
      SolutionHom (toExtensionOverBase Q₁) (toExtensionOverBase Q₂) where
  toFun e := ⟨e.hom, e.thickening_comm, e.base_comm, e.kernel_comm⟩
  invFun e := ⟨e.hom, e.thickening_comm, e.base_comm, e.kernel_comm⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Two solutions of **Stacks 08U7** are isomorphic — in the geometric sense of
`AlgebraicGeometry.RingedSpaceThickening.Isomorphic`, used by **Stacks 08UC** — exactly when
their underlying square-zero extensions of `f^{-1}𝒪_{S'}`-algebras are. -/
theorem isomorphic_iff_isomorphic_overBase {t : S ⟶ S'} {ht : IsFirstOrderThickening t}
    {f : X ⟶ S} {G : SheafOfModules.{u} (structureSheafRing X)}
    {c : (modulePullback f).obj (baseIdealOnReduction t) ⟶ G}
    (Q₁ Q₂ : DeformationSolution t ht f G c) :
    Isomorphic Q₁ Q₂ ↔
      Isomorphic (toExtensionOverBase Q₁) (toExtensionOverBase Q₂) := by
  rw [isomorphic_iff_nonempty_solutionHom, isomorphic_iff_nonempty_solutionHom]
  exact ⟨fun h => h.map fun e => solutionHomEquivOverBase Q₁ Q₂ e,
    fun h => h.map fun e => (solutionHomEquivOverBase Q₁ Q₂).symm e⟩

/-! ### Isomorphism classes of solutions -/

/-- Isomorphism of solutions of **Stacks 08U7**, as isomorphism of the underlying square-zero
extensions of `f^{-1}𝒪_{S'}`-algebras: the relation `r` on extensions, pulled back along
`toExtensionOverBase`.  When `r` is the library's geometric isomorphism relation this is the
library's geometric isomorphism relation on solutions; see `solutionSetoid_iff_isomorphic`. -/
def solutionSetoid {t : S ⟶ S'} (ht : IsFirstOrderThickening t) {f : X ⟶ S}
    {G : SheafOfModules.{u} (structureSheafRing X)}
    (c : (modulePullback f).obj (baseIdealOnReduction t) ⟶ G)
    (r : Setoid (ExtensionOverBase f t G)) : Setoid (DeformationSolution t ht f G c) where
  r Q₁ Q₂ := r.r (toExtensionOverBase Q₁) (toExtensionOverBase Q₂)
  iseqv :=
    { refl := fun _ => r.refl _
      symm := fun h => r.symm h
      trans := fun h₁ h₂ => r.trans h₁ h₂ }

/-- The class of the underlying extension of `f^{-1}𝒪_{S'}`-algebras of a solution, as a map
on isomorphism classes. -/
def solutionClassToExtensionClass {t : S ⟶ S'} (ht : IsFirstOrderThickening t) {f : X ⟶ S}
    {G : SheafOfModules.{u} (structureSheafRing X)}
    (c : (modulePullback f).obj (baseIdealOnReduction t) ⟶ G)
    (r : Setoid (ExtensionOverBase f t G)) :
    Quotient (solutionSetoid ht c r) → Quotient r :=
  Quotient.lift (fun Q => Quotient.mk r (toExtensionOverBase Q)) fun _ _ h => Quotient.sound h

/-- A class of extensions of `f^{-1}𝒪_{S'}`-algebras is a class of solutions of **Stacks 08U7**
when some extension in it underlies a solution — equivalently, by `toExtensionOverBase` and
`ofExtensionOverBase`, when some extension in it satisfies the compatibility equation for
`c`. -/
def ExtensionOverBase.IsSolutionClass {t : S ⟶ S'} (ht : IsFirstOrderThickening t) {f : X ⟶ S}
    {G : SheafOfModules.{u} (structureSheafRing X)}
    (c : (modulePullback f).obj (baseIdealOnReduction t) ⟶ G)
    (r : Setoid (ExtensionOverBase f t G)) (p : Quotient r) : Prop :=
  ∃ Q : DeformationSolution t ht f G c, Quotient.mk r (toExtensionOverBase Q) = p

section Main

variable {t : S ⟶ S'} (ht : IsFirstOrderThickening t) {f : X ⟶ S}
  {G : SheafOfModules.{u} (structureSheafRing X)}
  (c : (modulePullback f).obj (baseIdealOnReduction t) ⟶ G)
  {T₁ T₂ : Type*} (rho : T₁ → T₂) (eps : T₂)
  (r : Setoid (ExtensionOverBase f t G)) (E : Quotient r ≃ T₁)

/-- When the carried relation `r` is the library's geometric isomorphism relation on
square-zero extensions of `f^{-1}𝒪_{S'}`-algebras, the relation on solutions whose classes are
counted below is `AlgebraicGeometry.RingedSpaceThickening.Isomorphic`, the geometric
isomorphism relation of **Stacks 08UC** on the solutions themselves. -/
theorem solutionSetoid_iff_isomorphic
    (hr : ∀ P₁ P₂ : ExtensionOverBase f t G, r.r P₁ P₂ ↔ Isomorphic P₁ P₂)
    (Q₁ Q₂ : DeformationSolution t ht f G c) :
    (solutionSetoid ht c r).r Q₁ Q₂ ↔ Isomorphic Q₁ Q₂ :=
  (hr _ _).trans (isomorphic_iff_isomorphic_overBase Q₁ Q₂).symm

/-- The class of a solution of **Stacks 08U7**: the class of its underlying extension of
`f^{-1}𝒪_{S'}`-algebras, read through `E`.  At `T₁ = Ext¹_{𝒪_X}(NL_{X/S'}, 𝒢)` and `E` the
bijection of **Stacks 0GPZ** this is the class `ζ` of the source. -/
def solutionClassToExtClass : Quotient (solutionSetoid ht c r) → T₁ :=
  fun s => E (solutionClassToExtensionClass ht c r s)

/-- The class of the solution `Q` is the image under `E` of the class of its underlying
extension `toExtensionOverBase Q`. -/
theorem solutionClassToExtClass_mk (Q : DeformationSolution t ht f G c) :
    solutionClassToExtClass ht c r E (Quotient.mk (solutionSetoid ht c r) Q) =
      E (Quotient.mk r (toExtensionOverBase Q)) :=
  rfl

/-- The class map is injective: two solutions whose underlying extensions have the same class
are isomorphic.  This needs nothing beyond the bijection `E`. -/
theorem solutionClassToExtClass_injective :
    Function.Injective (solutionClassToExtClass ht c r E) := by
  intro s₁ s₂ h
  obtain ⟨Q₁, rfl⟩ := Quotient.exists_rep s₁
  obtain ⟨Q₂, rfl⟩ := Quotient.exists_rep s₂
  rw [solutionClassToExtClass_mk, solutionClassToExtClass_mk] at h
  have h' : Quotient.mk r (toExtensionOverBase Q₁) = Quotient.mk r (toExtensionOverBase Q₂) :=
    E.injective h
  have h'' : r.r (toExtensionOverBase Q₁) (toExtensionOverBase Q₂) := Quotient.exact h'
  exact Quotient.sound h''

/-- Given a bijection `E` from the isomorphism classes of square-zero extensions of
`f^{-1}𝒪_{S'}`-algebras to a target `T₁`, and a criterion `hcrit` telling which classes are
classes of solutions of **Stacks 08U7**, the isomorphism classes of solutions are bijective to
the subtype `rho z = eps` cut out by that criterion, by the constructed map
`[X'] ↦ E [𝒪_{X'}]`.

At `T₁ = Ext¹_{𝒪_X}(NL_{X/S'}, 𝒢)`, `rho = restrictDerivedExtClass q`,
`eps = pullbackExtClass f t c xi`, `E` the bijection of **Stacks 0GPZ** and `hcrit` the
criterion of **Stacks 0GQ1** this is the bijection of **Stacks 0GQ3**.  That specialization is
`solutionsEquivDerivedExtFibre`, and it is where the tag sits; the attribute stays off this
declaration because here `hcrit` is a hypothesis.  See the note at the top of this file. -/
def solutionsEquivExtFibre
    (hcrit : ∀ p : Quotient r, ExtensionOverBase.IsSolutionClass ht c r p ↔ rho (E p) = eps) :
    Quotient (solutionSetoid ht c r) ≃ { z : T₁ // rho z = eps } :=
  Equiv.ofBijective
    (fun s => ⟨solutionClassToExtClass ht c r E s, by
      obtain ⟨Q, rfl⟩ := Quotient.exists_rep s
      rw [solutionClassToExtClass_mk]
      exact (hcrit _).1 ⟨Q, rfl⟩⟩)
    ⟨fun s₁ s₂ h =>
      solutionClassToExtClass_injective ht c r E (congrArg Subtype.val h),
     by
      rintro ⟨z, hz⟩
      obtain ⟨Q, hQ⟩ := (hcrit (E.symm z)).2 (by rw [E.apply_symm_apply]; exact hz)
      refine ⟨Quotient.mk (solutionSetoid ht c r) Q, Subtype.ext ?_⟩
      change solutionClassToExtClass ht c r E (Quotient.mk (solutionSetoid ht c r) Q) = z
      rw [solutionClassToExtClass_mk, hQ, E.apply_symm_apply]⟩

/-- The bijection is the constructed map, not an arbitrary one. -/
theorem solutionsEquivExtFibre_apply
    (hcrit : ∀ p : Quotient r, ExtensionOverBase.IsSolutionClass ht c r p ↔ rho (E p) = eps)
    (s : Quotient (solutionSetoid ht c r)) :
    (solutionsEquivExtFibre ht c rho eps r E hcrit s).1 =
      solutionClassToExtClass ht c r E s :=
  rfl

/-- The target subtype is nonempty as soon as a solution exists.  This is the source's own
hypothesis in **Stacks 08UC**, and it says the bijection is not a bijection of empty sets. -/
theorem nonempty_extFibre_of_nonempty
    (hcrit : ∀ p : Quotient r, ExtensionOverBase.IsSolutionClass ht c r p ↔ rho (E p) = eps)
    (hne : Nonempty (DeformationSolution t ht f G c)) :
    Nonempty { z : T₁ // rho z = eps } :=
  hne.map fun Q =>
    solutionsEquivExtFibre ht c rho eps r E hcrit (Quotient.mk (solutionSetoid ht c r) Q)

end Main

end AlgebraicGeometry.RingedSpaceThickening

end
