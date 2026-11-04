module

public import StacksFrontier.AlgebraicGeometry.Constructions.SymmetricAlgebraAffinePieces
public import StacksFrontier.AlgebraicGeometry.Constructions.DirectSumQuasiCompactSections
public import StacksFrontier.AlgebraicGeometry.Constructions.VectorBundleOfModule
public import StacksFrontier.AlgebraicGeometry.Divisors.Meromorphic.FittingIdeals
public import StacksFrontier.AlgebraicGeometry.FPAlgebraSheaf.Locality
public import StacksFrontier.AlgebraicGeometry.ProEtale.Cohomology.DirectImageInputs
public import StacksFrontier.RingTheory.SymmetricAlgebra.FinitePresentation
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SymmetricAlgebraConstruction.Sectionwise
import StacksCore.Tactic.EgaSgaAttribute

/-!
# `Γ(V, Sym(ℰ))` is a symmetric algebra, and `Sym(ℰ)` is of finite presentation

Let `X` be a scheme, `ℰ` a quasi-coherent `𝒪_X`-module and `V` an affine open. This file
identifies the ring of sections of the **ungraded** realization of `Sym(ℰ)` over `V` with the
symmetric algebra of the sections,

`Γ(V, Sym(ℰ)) ≅ Sym_{Γ(X, V)}(Γ(ℰ, V))`,

carrying the structure map of the algebra sheaf to the structure map of the symmetric algebra; and
draws the consequence: when `ℰ` is of finite presentation, the algebra sheaf
`AlgebraicGeometry.Scheme.Modules.symmetricAlgebraSheaf` is of finite presentation and the
projection of the vector bundle `𝐕(ℰ) ⟶ X` is locally of finite presentation.

## Main definitions

* `Stacks.SymAlgSections.ofSymPowers`: the ring homomorphism
  `(⨁ n : ℕ, Symⁿ_{Γ(X, V)}(Γ(ℰ, V))) ⟶ ⨁ n : ℤ, Γ(V, Symⁿ ℰ)` which is the sheafification unit
  in each degree.
* `Stacks.SymAlgSections.symSectionsRingEquiv`: **the identification
  `Sym_{Γ(X, V)}(Γ(ℰ, V)) ≅ Γ(V, Sym(ℰ))`.**

## Main results

* `Stacks.SymAlgSections.bijective_ofSymPowers`: `ofSymPowers` is bijective.
* `Stacks.SymAlgSections.symSectionsRingEquiv_algebraMap`: **the identification carries
  `algebraMap` to the structure map of the algebra sheaf**, so the structural ring map of
  `Sym(ℰ)` over an affine open *is* the structure map of a symmetric algebra.
* `Stacks.SymAlgSections.finitePresentation_app`: for `ℰ` of finite presentation, the structural
  ring map of `Sym(ℰ)` over an affine open is of finite presentation.
* `Stacks.SymAlgSections.isOfFinitePresentation_symmetricAlgebraSheaf`: **`Sym(ℰ)` is a
  quasi-coherent algebra of finite presentation** for `ℰ` quasi-coherent of finite presentation.
* `Stacks.SymAlgSections.locallyOfFinitePresentation_vectorBundleToBase`: **the projection
  `𝐕(ℰ) ⟶ X` is locally of finite presentation.**

## Implementation notes

**Three identifications are composed and none of them is new.** Degreewise, the sections of
`Symⁿ ℰ` over an affine open are `Symⁿ` of the sections — that is
`AlgebraicGeometry.Scheme.Modules.symmetricAlgebraPieceEquiv`. Over the degrees, the sections of
the ungraded realization are the direct sum of the sections of the pieces — that is
`Stacks.RelativeSpec.totalSectionsRingEquiv`, which holds over a quasi-compact open. And the
symmetric algebra is the direct sum of its symmetric powers — that is
`DirectSum.decomposeRingEquiv` at `SymmetricAlgebra.gradedAlgebra`. What this file adds is that
the first one is multiplicative, which is `Stacks.GradedAlgebra.sheafify_mul_unit` and
`sheafify_one_eval` at the sectionwise symmetric algebra
`PresheafOfModules.symPowIntGradedAlgebra`, and the bookkeeping that turns the three into a
single ring isomorphism.

**Multiplicativity is proved on the source, by `DirectSum.toSemiring`.** The same device as in
`Stacks.SymGraded.AffinePieces.symSectionRingEquiv`: a family of additive maps out of the
homogeneous summands which carries the graded unit to the unit and the graded product of two
homogeneous elements to the product is a ring homomorphism out of the external direct sum. A map
*out of* `Γ(V, Sym(ℰ))` would instead need a decomposition of a general section.

**Bijectivity is proved by exhibiting the inverse, degreewise, and never by `rw` under
`DirectSum.of`.** The index family of the target is eta-expanded by the abbreviations, and `rw`
fails there at `implicit` transparency with a type-correctness error; this is recorded in the
implementation notes of
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafifiedDirectSum` and of
`StacksFrontier.AlgebraicGeometry.Constructions.DirectSumQuasiCompactSections` and is respected
here: the round-trip identities only ever see `DirectSum.of`, which `DirectSum.toAddMonoid_of`
discharges, and the `ℤ`-versus-`ℕ` indexing is crossed by `exact`, not `rw`.

**The `ℕ`-to-`ℤ` truncation is `Stacks.bijective_directSumNatToIntApp`**, fed from
`AlgebraicGeometry.Scheme.Modules.isZero_symmetricAlgebra_piece` through
`Stacks.subsingleton_of_isZero`: the negative-degree pieces of `Sym(ℰ)` are zero, so the direct
sum over the nonnegative degrees is the direct sum over all of them.

**The degree casts are definitional and are never rewritten.** The source of `ofSymPowers` is
`ℕ`-graded and the target `ℤ`-graded, so the product of the degree-`i` and degree-`j` summands is
indexed by `((i + j : ℕ) : ℤ)` on one side and `(i : ℤ) + (j : ℤ)` on the other. `Nat.cast` into
`ℤ` is `Int.ofNat` and `Int.add` reduces on constructors, so the two are definitionally equal and
every such step is an `exact`.

**Which spelling of `Γ(X, V)` each scalar action is stated at is not a matter of taste.**
`Module Γ(X, V) Γ(Symⁿ ℰ, V)` is **not** found by instance search — the homogeneous
pieces of a `SheafOfModules.GradedAlgebra` are `SheafOfModules`, not
`AlgebraicGeometry.Scheme.Modules`, which is a `def`, so Mathlib's instance at the `Γ` spelling
does not apply — whereas the action of `X.ringCatSheaf.obj.obj (op V)` on
`((Sym(ℰ)).piece n).val.obj (op V)` is. The same holds for the ungraded realization, whose
`Module` instance is stated at `X.ringCatSheaf.obj.obj (op V)`. So `structureMap_eq` takes its
scalar at that spelling, and the one crossing into `Γ(X, V)` happens in
`symSectionsRingEquiv_algebraMap`, by application — the two types are definitionally equal, so
nothing is transported. The scalar action on `Symⁿ_{Γ(X, V)}(Γ(ℰ, V))` is a `Submodule` action
over `Γ(X, V)`, and the `LinearMap.map_smul` of the sheafification unit is used without being
restated, so that neither spelling has to be written down in the step that crosses them.

**No locality argument is needed.** `Stacks.FPAlgebraSheaf.isOfFinitePresentation_of_iSup_eq_top`
would let finite presentation be checked on a cover only; here the structural ring map is
identified over *every* affine open at once, which is already the definition, so finite
presentation follows with no descent step.

**No `@[stacks]` tag.** The identification of the sections is Tag 01CG's content, carried
degreewise by `Stacks.SymGraded.bijective_sheafifyUnit_app_of_isAffineOpen`; finite presentation
of `Sym(ℰ)` is one input of Tag 05JS and not its assertion, which is the colimit presentation of
an arbitrary quasi-coherent algebra.

## References

* [Stacks Project, Tag 01CG](https://stacks.math.columbia.edu/tag/01CG)
* [Stacks Project, Tag 01AI](https://stacks.math.columbia.edu/tag/01AI)
* [Stacks Project, Tag 01M2](https://stacks.math.columbia.edu/tag/01M2)
* [Stacks Project, Tag 05JS](https://stacks.math.columbia.edu/tag/05JS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry
open PresheafOfModules
open scoped DirectSum

universe u

namespace Stacks.SymAlgSections

variable {X : Scheme.{u}} (E : X.Modules) [E.IsQuasicoherent] {V : X.Opens}
  (hV : IsAffineOpen V)

/-! ### The two graded algebras -/

/-- The homogeneous pieces of `Sym(ℰ)`, as a `ℤ`-indexed family of presheaves of modules. -/
abbrev symPiece (n : ℤ) : PresheafOfModules.{u} X.ringCatSheaf.obj :=
  ((Scheme.Modules.symmetricAlgebra X E).piece n).val

/-- `Sym(ℰ)` read as a graded algebra of presheaves of modules, which is the shape its ungraded
realization is formed from. -/
abbrev symPresheafAlgebra : Stacks.GradedAlgebra (symPiece E) :=
  (Scheme.Modules.symmetricAlgebra X E).toPresheafGradedAlgebra

/-- **`Sym(ℰ)` is a quasi-coherent algebra sheaf**, at the
`AlgebraicGeometry.Scheme.Modules` spelling of the module sheaf. This restates
`AlgebraicGeometry.Scheme.Modules.isQuasicoherent_symmetricAlgebraSheaf`, whose own statement is
at the `SheafOfModules X.ringCatSheaf` spelling; `AlgebraicGeometry.Scheme.Modules` is a `def`,
and instance search does not see through it. -/
instance isQuasicoherentAlgebra_symmetricAlgebraSheaf :
    Stacks.RelativeSpec.AlgebraSheaf.IsQuasicoherent
      (Scheme.Modules.symmetricAlgebraSheaf X E) :=
  Scheme.Modules.isQuasicoherent_symmetricAlgebraSheaf X E

/-! ### The sheafification unit in a single degree -/

/-- **`Symⁿ` of the sections of `ℰ` over an affine open is the sections of `Symⁿ(ℰ)` there**, as
an isomorphism of additive groups: `AlgebraicGeometry.Scheme.Modules.symmetricAlgebraPieceEquiv`
with the source written as the symmetric power of the sections — the two types are the same, the
degree-`n` piece of the sectionwise symmetric algebra being `SymPow.symmetricPowerInt (n : ℤ)`,
which is `SymPow.symmetricPower n` on the nose. -/
def pieceUnit (n : ℕ) :
    SymPow.symmetricPower n Γ(X, V) Γ(E, V) ≃+ ((symPiece E (n : ℤ)).obj (op V)) :=
  AddEquiv.mk' (Scheme.Modules.symmetricAlgebraPieceEquiv E hV (n : ℤ))
    fun x y => map_add ((sheafifyUnit (R := X.ringCatSheaf) (𝟙 X.ringCatSheaf.obj)
      (symPowInt (n : ℤ) E.val)).app (op V)).hom x y

/-- `Stacks.SymAlgSections.pieceUnit` is evaluation of the sheafification unit at `V`. -/
theorem pieceUnit_apply (n : ℕ) (x : SymPow.symmetricPower n Γ(X, V) Γ(E, V)) :
    pieceUnit E hV n x =
      Hom.app (sheafifyUnit (R := X.ringCatSheaf) (𝟙 X.ringCatSheaf.obj)
        (symPowInt (n : ℤ) E.val)) (op V) x := rfl

/-! ### The sheafification unit, assembled over the nonnegative degrees -/

/-- The degreewise sheafification unit, assembled over the nonnegative degrees. -/
def natSumUnit : (⨁ n : ℕ, SymPow.symmetricPower n Γ(X, V) Γ(E, V)) →+
    DirectSumType (fun n : ℕ => symPiece E (n : ℤ)) (op V) :=
  DirectSum.toAddMonoid fun n =>
    (DirectSum.of (fun m : ℕ => ((symPiece E (m : ℤ)).obj (op V) : Type u)) n).comp
      (pieceUnit E hV n).toAddMonoidHom

/-- `Stacks.SymAlgSections.natSumUnit` sends the degree-`n` summand `x` to the degree-`n`
summand `pieceUnit E hV n x`. -/
@[simp]
theorem natSumUnit_of (n : ℕ) (x : SymPow.symmetricPower n Γ(X, V) Γ(E, V)) :
    natSumUnit E hV (DirectSum.of _ n x) =
      DirectSum.of (fun m : ℕ => ((symPiece E (m : ℤ)).obj (op V) : Type u)) n
        (pieceUnit E hV n x) :=
  DirectSum.toAddMonoid_of _ _ _

/-- The inverse of `Stacks.SymAlgSections.natSumUnit`, degree by degree. -/
def natSumUnitInv : DirectSumType (fun n : ℕ => symPiece E (n : ℤ)) (op V) →+
    (⨁ n : ℕ, SymPow.symmetricPower n Γ(X, V) Γ(E, V)) :=
  DirectSum.toAddMonoid fun n =>
    (DirectSum.of (fun m : ℕ => (SymPow.symmetricPower m Γ(X, V) Γ(E, V) : Type u)) n).comp
      (pieceUnit E hV n).symm.toAddMonoidHom

/-- `Stacks.SymAlgSections.natSumUnitInv` sends the degree-`n` summand `y` to the degree-`n`
summand `(pieceUnit E hV n).symm y`. -/
@[simp]
theorem natSumUnitInv_of (n : ℕ) (y : (symPiece E (n : ℤ)).obj (op V)) :
    natSumUnitInv E hV (DirectSum.of _ n y) =
      DirectSum.of (fun m : ℕ => (SymPow.symmetricPower m Γ(X, V) Γ(E, V) : Type u)) n
        ((pieceUnit E hV n).symm y) :=
  DirectSum.toAddMonoid_of _ _ _

/-- `Stacks.SymAlgSections.natSumUnit` is bijective. -/
theorem bijective_natSumUnit : Function.Bijective (natSumUnit E hV) := by
  refine Function.bijective_iff_has_inverse.2 ⟨natSumUnitInv E hV, fun z => ?_, fun y => ?_⟩
  · exact DFunLike.congr_fun (DirectSum.addHom_ext
      (f := (natSumUnitInv E hV).comp (natSumUnit E hV)) (g := AddMonoidHom.id _)
      fun n x => by simp) z
  · exact DFunLike.congr_fun (DirectSum.addHom_ext
      (f := (natSumUnit E hV).comp (natSumUnitInv E hV)) (g := AddMonoidHom.id _)
      fun n y => by simp) y

/-! ### The direct sum of the symmetric powers as the direct sum of the sections -/

/-- The degreewise sheafification unit followed by the inclusion of the degree-`n` summand of
the direct sum of the sections. -/
def symPowerIncl (n : ℕ) : SymPow.symmetricPower n Γ(X, V) Γ(E, V) →+
    (symPresheafAlgebra E).Total (op V) :=
  (DirectSum.of (fun m : ℤ => ((symPiece E m).obj (op V) : Type u)) (n : ℤ)).comp
    (pieceUnit E hV n).toAddMonoidHom

/-- `Stacks.SymAlgSections.symPowerIncl E hV n x` is the degree-`n` summand
`pieceUnit E hV n x`. -/
theorem symPowerIncl_apply (n : ℕ) (x : SymPow.symmetricPower n Γ(X, V) Γ(E, V)) :
    symPowerIncl E hV n x =
      DirectSum.of (fun m : ℤ => ((symPiece E m).obj (op V) : Type u)) (n : ℤ)
        (pieceUnit E hV n x) := rfl

/-- **The degree-zero summand carries the unit to the unit**: this is
`Stacks.GradedAlgebra.sheafify_one_eval` at the sectionwise symmetric algebra. The hypothesis is
on the underlying element of the symmetric algebra rather than on a subtype element, so that
`DirectSum.toSemiring` can discharge its own `GradedMonoid.GOne.one` by `rfl`. -/
theorem symPowerIncl_one (x : SymPow.symmetricPower 0 Γ(X, V) Γ(E, V))
    (hx : (x : SymmetricAlgebra Γ(X, V) Γ(E, V)) = 1) :
    symPowerIncl E hV 0 x = 1 :=
  (congrArg (DirectSum.of (fun m : ℤ => ((symPiece E m).obj (op V) : Type u)) 0)
      ((congrArg (Hom.app (sheafifyUnit (R := X.ringCatSheaf) (𝟙 X.ringCatSheaf.obj)
            (symPowInt (0 : ℤ) E.val)) (op V))
          (Subtype.ext hx : x = (symPowIntGradedAlgebra E.val).one.eval (op V))).trans
        ((symPowIntGradedAlgebra E.val).sheafify_one_eval
          (𝟙 X.ringCatSheaf.obj) (op V)).symm)).trans
    ((symPresheafAlgebra E).one_eq_incl (op V)).symm

/-- **The summands multiply as the symmetric powers do**: this is
`Stacks.GradedAlgebra.sheafify_mul_unit` at the sectionwise symmetric algebra, whose homogeneous
multiplication is the multiplication of the symmetric algebra of the sections. -/
theorem symPowerIncl_mul (i j : ℕ)
    (a : SymPow.symmetricPower i Γ(X, V) Γ(E, V)) (b : SymPow.symmetricPower j Γ(X, V) Γ(E, V))
    (c : SymPow.symmetricPower (i + j) Γ(X, V) Γ(E, V))
    (hc : (c : SymmetricAlgebra Γ(X, V) Γ(E, V)) =
      (a : SymmetricAlgebra Γ(X, V) Γ(E, V)) * (b : SymmetricAlgebra Γ(X, V) Γ(E, V))) :
    symPowerIncl E hV (i + j) c = symPowerIncl E hV i a * symPowerIncl E hV j b :=
  Eq.symm
    (((symPresheafAlgebra E).incl_mul_incl (i : ℤ) (j : ℤ) _ _).trans
      (congrArg (DirectSum.of (fun m : ℤ => ((symPiece E m).obj (op V) : Type u)) _)
        (((symPowIntGradedAlgebra E.val).sheafify_mul_unit (𝟙 X.ringCatSheaf.obj)
            (i : ℤ) (j : ℤ) (op V) a b).trans
          (congrArg (Hom.app (sheafifyUnit (R := X.ringCatSheaf) (𝟙 X.ringCatSheaf.obj)
              (symPowInt ((i : ℤ) + (j : ℤ)) E.val)) (op V))
            (Subtype.ext hc.symm)))))

/-- **The degreewise sheafification unit as a ring homomorphism** out of the external direct sum
of the symmetric powers of `Γ(ℰ, V)` into the direct sum of the sections of the homogeneous
pieces of `Sym(ℰ)`. -/
def ofSymPowers : (⨁ n : ℕ, SymPow.symmetricPower n Γ(X, V) Γ(E, V)) →+*
    (symPresheafAlgebra E).Total (op V) :=
  DirectSum.toSemiring (symPowerIncl E hV) (symPowerIncl_one E hV _ rfl)
    (fun {_ _} ai aj => symPowerIncl_mul E hV _ _ ai aj _ rfl)

/-- `Stacks.SymAlgSections.ofSymPowers` agrees with `Stacks.SymAlgSections.symPowerIncl` on the
degree-`n` summand. -/
theorem ofSymPowers_of (n : ℕ) (x : SymPow.symmetricPower n Γ(X, V) Γ(E, V)) :
    ofSymPowers E hV (DirectSum.of _ n x) = symPowerIncl E hV n x :=
  DirectSum.toSemiring_of (symPowerIncl E hV) _ _ n x

/-- The underlying additive map of `Stacks.SymAlgSections.ofSymPowers` is the degreewise
sheafification unit followed by the inclusion of the nonnegative degrees. -/
theorem ofSymPowers_apply_eq (z : ⨁ n : ℕ, SymPow.symmetricPower n Γ(X, V) Γ(E, V)) :
    ofSymPowers E hV z =
      directSumNatToIntApp (symPiece E) (op V) (natSumUnit E hV z) := by
  exact DFunLike.congr_fun (DirectSum.addHom_ext
    (f := (ofSymPowers E hV).toAddMonoidHom)
    (g := (directSumNatToIntApp (symPiece E) (op V)).comp (natSumUnit E hV))
    fun n x =>
      ((ofSymPowers_of E hV n x).trans (symPowerIncl_apply E hV n x)).trans
        ((directSumNatToIntApp_of (symPiece E) (op V) n (pieceUnit E hV n x)).symm.trans
          (congrArg (directSumNatToIntApp (symPiece E) (op V))
            (natSumUnit_of E hV n x).symm))) z

/-- **The direct sum of the symmetric powers of `Γ(ℰ, V)` is the direct sum of the sections of
the homogeneous pieces of `Sym(ℰ)`.** The degreewise unit is bijective because `V` is affine and
`ℰ` quasi-coherent, and the negative degrees contribute nothing because the negative pieces of
`Sym(ℰ)` are zero. -/
theorem bijective_ofSymPowers : Function.Bijective (ofSymPowers E hV) := by
  have hzero : ∀ n : ℤ, n < 0 → Subsingleton ((symPiece E n).obj (op V)) := fun n hn =>
    subsingleton_of_isZero (Scheme.Modules.isZero_symmetricAlgebra_piece X E n hn) (op V)
  have hcomp : Function.Bijective fun z => directSumNatToIntApp (symPiece E) (op V)
      (natSumUnit E hV z) :=
    (bijective_directSumNatToIntApp (symPiece E) (op V) hzero).comp (bijective_natSumUnit E hV)
  exact (funext fun z => ofSymPowers_apply_eq E hV z) ▸ hcomp

/-- The direct sum of the symmetric powers of `Γ(ℰ, V)`, as a ring, is the direct sum of the
sections of the homogeneous pieces of `Sym(ℰ)`. -/
def symPowersRingEquiv : (⨁ n : ℕ, SymPow.symmetricPower n Γ(X, V) Γ(E, V)) ≃+*
    (symPresheafAlgebra E).Total (op V) :=
  RingEquiv.ofBijective (ofSymPowers E hV) (bijective_ofSymPowers E hV)

/-! ### The ring of sections over an affine open -/

/-- **`Γ(V, Sym(ℰ))` is the symmetric algebra of `Γ(ℰ, V)` over `Γ(X, V)`**, for `V` an affine
open of a scheme and `ℰ` a quasi-coherent `𝒪_X`-module: the sections of the algebra sheaf
`AlgebraicGeometry.Scheme.Modules.symmetricAlgebraSheaf` over `V` are the symmetric algebra of
the sections of `ℰ`. -/
@[ega "II 1.7.6" "partial"]
def symSectionsRingEquiv : SymmetricAlgebra Γ(X, V) Γ(E, V) ≃+*
    ((Scheme.Modules.symmetricAlgebraSheaf X E).right.obj.obj (op V)) :=
  (DirectSum.decomposeRingEquiv
      (fun n : ℕ => SymPow.symmetricPower n Γ(X, V) Γ(E, V))).trans
    ((symPowersRingEquiv E hV).trans
      (Stacks.RelativeSpec.totalSectionsRingEquiv X (Scheme.Modules.symmetricAlgebra X E)
        (Scheme.Modules.symmetricAlgebra_mul_comm X E) hV))

/-- The image of `r : Γ(X, V)` in the degree-zero symmetric power `Sym⁰_{Γ(X, V)}(Γ(ℰ, V))`. -/
def symOne (r : Γ(X, V)) : SymPow.symmetricPower 0 Γ(X, V) Γ(E, V) :=
  ⟨algebraMap Γ(X, V) (SymmetricAlgebra Γ(X, V) Γ(E, V)) r, by
    rw [Algebra.algebraMap_eq_smul_one]
    exact Submodule.smul_mem _ r SetLike.GradedOne.one_mem⟩

omit [E.IsQuasicoherent] in
/-- The decomposition of the image of `Γ(X, V)` in `Sym_{Γ(X, V)}(Γ(ℰ, V))`: it is concentrated
in degree zero. -/
private theorem decompose_algebraMap (r : Γ(X, V)) :
    DirectSum.decompose (fun n : ℕ => SymPow.symmetricPower n Γ(X, V) Γ(E, V))
        (algebraMap Γ(X, V) (SymmetricAlgebra Γ(X, V) Γ(E, V)) r) =
      DirectSum.of (fun m : ℕ => (SymPow.symmetricPower m Γ(X, V) Γ(E, V) : Type u)) 0
        (symOne E r) :=
  DirectSum.decompose_of_mem (fun n : ℕ => SymPow.symmetricPower n Γ(X, V) Γ(E, V))
    (symOne E r).2

/-- The structure map of the ungraded realization is the degree-zero part of the structure map of
the symmetric algebra of the sections. -/
private theorem structureMap_eq (r : X.ringCatSheaf.obj.obj (op V)) :
    (symPresheafAlgebra E).structureMap (op V) r =
      ofSymPowers E hV (DirectSum.of
        (fun m : ℕ => (SymPow.symmetricPower m Γ(X, V) Γ(E, V) : Type u)) 0 (symOne E r)) := by
  have hone := (symPowIntGradedAlgebra E.val).sheafify_one_eval (𝟙 X.ringCatSheaf.obj) (op V)
  have hlin := ((sheafifyUnit (R := X.ringCatSheaf) (𝟙 X.ringCatSheaf.obj)
    (symPowInt (0 : ℤ) E.val)).app (op V)).hom.map_smul r
      ((symPowIntGradedAlgebra E.val).one.eval (op V))
  have h3 : r • (Scheme.Modules.symmetricAlgebra X E).one.eval (op V) =
      Hom.app (sheafifyUnit (R := X.ringCatSheaf) (𝟙 X.ringCatSheaf.obj)
        (symPowInt (0 : ℤ) E.val)) (op V) (symOne E r) :=
    ((congrArg (fun y => r • y) hone).trans hlin.symm).trans
      (congrArg (Hom.app (sheafifyUnit (R := X.ringCatSheaf) (𝟙 X.ringCatSheaf.obj)
          (symPowInt (0 : ℤ) E.val)) (op V))
        (Subtype.ext
          (Algebra.algebraMap_eq_smul_one (R := Γ(X, V))
            (A := SymmetricAlgebra Γ(X, V) Γ(E, V)) r).symm))
  exact Eq.trans
    (((symPresheafAlgebra E).incl_smul (0 : ℤ) r
          ((Scheme.Modules.symmetricAlgebra X E).one.eval (op V))).symm.trans
      (congrArg (DirectSum.of (fun m : ℤ => ((symPiece E m).obj (op V) : Type u)) 0) h3))
    ((ofSymPowers_of E hV 0 (symOne E r)).trans
      (symPowerIncl_apply E hV 0 (symOne E r))).symm

/-- **The identification carries `algebraMap` to the structure map of the algebra sheaf.** So
the structural ring map of `Sym(ℰ)` over an affine open *is* the structure map of a symmetric
algebra, and not merely isomorphic to one in a way that forgets the base. -/
theorem symSectionsRingEquiv_algebraMap (r : Γ(X, V)) :
    symSectionsRingEquiv E hV (algebraMap Γ(X, V) (SymmetricAlgebra Γ(X, V) Γ(E, V)) r) =
      ((Scheme.Modules.symmetricAlgebraSheaf X E).hom.hom.app (op V)).hom r := by
  have h : ofSymPowers E hV (DirectSum.decompose
      (fun n : ℕ => SymPow.symmetricPower n Γ(X, V) Γ(E, V))
      (algebraMap Γ(X, V) (SymmetricAlgebra Γ(X, V) Γ(E, V)) r)) =
      (symPresheafAlgebra E).structureMap (op V) r :=
    (congrArg (ofSymPowers E hV) (decompose_algebraMap E r)).trans
      (structureMap_eq E hV r).symm
  exact congrArg (fun z => Stacks.RelativeSpec.totalSectionsRingEquiv X
    (Scheme.Modules.symmetricAlgebra X E)
    (Scheme.Modules.symmetricAlgebra_mul_comm X E) hV z) h

/-! ### Finite presentation -/

include hV in
/-- **For `ℰ` of finite presentation the structural ring map of `Sym(ℰ)` over an affine open is
of finite presentation.** Over an affine open it is the structure map of
`Sym_{Γ(X, V)}(Γ(ℰ, V))` for a finitely presented module `Γ(ℰ, V)`
(`AlgebraicGeometry.finitePresentation_sections_on_affine`), which is a finitely presented
algebra by `Stacks.SymAlg.finitePresentation`. -/
theorem finitePresentation_app [E.IsFinitePresentation] :
    RingHom.FinitePresentation
      ((Scheme.Modules.symmetricAlgebraSheaf X E).hom.hom.app (op V)).hom := by
  have hmod : Module.FinitePresentation Γ(X, V) Γ(E, V) :=
    AlgebraicGeometry.finitePresentation_sections_on_affine E ⟨V, hV⟩
  have halg : RingHom.FinitePresentation
      (algebraMap Γ(X, V) (SymmetricAlgebra Γ(X, V) Γ(E, V))) :=
    RingHom.finitePresentation_algebraMap.2 (Stacks.SymAlg.finitePresentation _ _)
  have htr := RingHom.finitePresentation_respectsIso.1 _ (symSectionsRingEquiv E hV) halg
  refine (show (symSectionsRingEquiv E hV).toRingHom.comp
    (algebraMap Γ(X, V) (SymmetricAlgebra Γ(X, V) Γ(E, V))) =
      ((Scheme.Modules.symmetricAlgebraSheaf X E).hom.hom.app (op V)).hom from ?_) ▸ htr
  exact RingHom.ext fun r => symSectionsRingEquiv_algebraMap E hV r

/-- **`Sym(ℰ)` is an algebra sheaf of finite presentation** for `ℰ` quasi-coherent of finite
presentation. -/
theorem isFinitePresentation_symmetricAlgebraSheaf [E.IsFinitePresentation] :
    Stacks.RelativeSpec.AlgebraSheaf.IsFinitePresentation
      (Scheme.Modules.symmetricAlgebraSheaf X E) :=
  fun _ hU => finitePresentation_app E hU

/-- **`Sym(ℰ)` is a quasi-coherent algebra of finite presentation** for `ℰ` quasi-coherent of
finite presentation. This is the statement in the vocabulary of
`AlgebraicGeometry.Scheme.QuasicoherentAlgebra`; quasi-coherence is
`Stacks.SymAlgSections.isQuasicoherentAlgebra_symmetricAlgebraSheaf`. -/
theorem isOfFinitePresentation_symmetricAlgebraSheaf [E.IsFinitePresentation] :
    Scheme.QuasicoherentAlgebra.IsOfFinitePresentation
      (Scheme.Modules.symmetricAlgebraSheaf X E) :=
  isFinitePresentation_symmetricAlgebraSheaf E

/-- **The projection `𝐕(ℰ) ⟶ X` of the vector bundle of a quasi-coherent module of finite
presentation is locally of finite presentation.** -/
theorem locallyOfFinitePresentation_vectorBundleToBase [E.IsFinitePresentation] :
    LocallyOfFinitePresentation (Scheme.Modules.vectorBundleToBase X E) :=
  Stacks.AffineAlgebraEquivalence.locallyOfFinitePresentation_relativeSpecToBase
    (Scheme.Modules.symmetricAlgebraSheaf X E)
    (isFinitePresentation_symmetricAlgebraSheaf E)

end Stacks.SymAlgSections

end
