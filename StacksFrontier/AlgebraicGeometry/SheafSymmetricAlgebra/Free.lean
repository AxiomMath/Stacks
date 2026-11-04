module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FreePowerSheafify
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafifyUnitIso
public import StacksFrontier.AlgebraicGeometry.AffineQcohEquivalence.Basic
public import StacksFrontier.AlgebraicGeometry.SheafSymmetricAlgebra.Scheme
public import StacksFrontier.AlgebraicGeometry.SymAlgebraQcohPieces.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The symmetric algebra of a finite free module sheaf needs no sheafification

`AlgebraicGeometry.Scheme.Modules.symmetricAlgebra X E` is the degreewise sheafification of
the sectionwise
symmetric algebra of an `𝒪_X`-module `E`, and in general nothing is known about its sections.
**For `E` finite free that sheafification is harmless**: the sectionwise degree-`k` piece of
`Sym(𝒪_X^ι)` is already a sheaf, namely the free sheaf on the degree-`k` multidegrees, so the
sheafification unit is an isomorphism and the sections of the degree-`k` piece over an open `U`
are `Sym^k_{Γ(X, U)}(Γ(X, U)^ι)` on the nose.

That is what makes the graded ring of homogeneous sections of `Sym(𝒪_X^ι)` over an affine open
computable, which is the chart-level input of Tag 01OE.

## Main definitions

* `Stacks.SymGraded.freePieceFreeIso`: **the degree-`k` piece of `Sym(𝒪_X^ι)` is the free sheaf
  on the degree-`k` multidegrees.**
* `Stacks.SymGraded.freePieceEquiv`: **the degreewise comparison**, the sheafification unit as a
  linear equivalence `Sym^k_{Γ(X, U)}(Γ(𝒪_X^ι, U)) ≃ₗ Γ(Sym(𝒪_X^ι)ₖ, U)`.
* `Stacks.SymGraded.freeSymGradedAlgebra`: `Sym(𝒪_X^ι)` as the input of the relative `Proj`
  construction, unconditionally.

## Main results

* `Stacks.SymGraded.isSheaf_symPow_free`: the sectionwise degree-`k` symmetric power of a finite
  free module sheaf is a sheaf.
* `Stacks.SymGraded.freePieceEquiv_one` and `Stacks.SymGraded.freePieceEquiv_mul`: the
  comparison takes the unit to the unit and the sectionwise graded multiplication to the
  multiplication of `Sym(𝒪_X^ι)`.
* `Stacks.SymGraded.isQuasicoherent_freeModule` and
  `Stacks.SymGraded.isQuasicoherentPieces_free`: a finite free module sheaf is quasi-coherent,
  and so are the homogeneous pieces of its symmetric algebra.
* `Stacks.SymGraded.resPiece_freePieceEquiv`: **the comparison is natural in the open**, that is,
  it intertwines the restriction map of the sectionwise symmetric power with restriction of
  homogeneous sections of `Sym(𝒪_X^ι)`.

## Implementation notes

`Stacks.SymGraded.siteGradedPiece F (k : ℤ)` and `PresheafOfModules.symPow k F` are **equal by
`rfl`** for `k : ℕ` — both are `PresheafOfModules.ofPresheaf` of the sectionwise symmetric power
with the semilinear restriction maps — which is what lets
`Stacks.SheafOfModules.symPowFreeIso` be used on the pieces of `Sym(E)`. No bridge
isomorphism is interposed.

The sheaf condition is transported along that isomorphism from the free sheaf on the
multidegrees. The sheaf-condition argument of `Stacks.SheafOfModules.symPowFreeIso` must be
`X.ringCatSheaf.property`, the sheaf condition for the `RingCat`-valued composite, and not
`X.sheaf.property`; with the latter the elaborator does not report a mismatch but spins to a
`whnf` timeout.

Multiplicativity is `Stacks.GradedAlgebra.sheafify_mul_unit` and the unit is
`Stacks.GradedAlgebra.sheafify_one_eval`, so — exactly as in
`StacksFrontier.AlgebraicGeometry.SheafSymmetricAlgebra.GlobalSections`, where the comparison was
`AlgebraicGeometry.tilde.toOpen` instead of the sheafification unit — no induction over the
symmetric algebra is needed.

## References

* [Stacks Project, Tag 01CG](https://stacks.math.columbia.edu/tag/01CG)
* [Stacks Project, Tag 01CK](https://stacks.math.columbia.edu/tag/01CK)
* [Stacks Project, Tag 01OE](https://stacks.math.columbia.edu/tag/01OE)

## Not done here

**No tag is claimed.** What is here is the first two layers of the route to Tag 01OE that does
*not* need Tag 01O3: since `Stacks.AlgebraicGeometry.RelativeProjGlue.relativeProj` is literally
`CategoryTheory.Limits.colimit` of the chart functor, with `chart = colimit.ι` and
`transition_comp_chart = colimit.w`, a cocone of charts gives a morphism
`Proj_X(Sym 𝒪_X^{n+1}) ⟶ ℙⁿ_X` with no cofinality obstruction, and invertibility then follows
from the affine case — `Stacks.SymGraded.projectiveBundleIsoProjectiveSpaceOverRing` — because
being an isomorphism is local at the target. Three layers are still owed:

* the chart-level graded ring isomorphism
  `(freeSymGradedAlgebra ι).grading U ≅ᵍ Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading
  Γ(X, U) n` for an affine open `U`, assembled from `freePieceEquiv`, `freePieceEquiv_one`,
  `freePieceEquiv_mul` and `SymPow.gradedMvPolynomialHom` exactly as
  `Stacks.SymGraded.globalSectionsRingEquiv` is assembled in
  `StacksFrontier/AlgebraicGeometry/SheafSymmetricAlgebra/GlobalSections.lean`;
* its naturality in `U`, for which `Stacks.SheafOfModules.basisSymPowSections_map` and
  `freeCoordBasis_map` are the inputs;
* the cocone itself, as `Limits.pullback.lift (relativeProjToBase _) (colimit.desc _ _)` with the
  square commuting by `terminal.hom_ext`, and the locality argument.

**The obstacle in the first of those is not mathematical.** The same ring appears in three
spellings that are definitionally equal but not syntactically interchangeable, so typeclass
search for the module structures fails whenever a type is written by hand rather than inferred:
`PresheafOfModules.symPow` puts its sections over
`((sheafToPresheaf _ CommRingCat).obj X.sheaf ⋙ forget₂ CommRingCat RingCat).obj U`,
`Stacks.SheafOfModules.freeCoordBasis` puts its basis over
`(SheafOfModules.GradedAlgebra.ringSheafOfIsSheaf X.ringCatSheaf.property).obj.obj U`, and
`Stacks.AlgebraicGeometry.RelativeProjBridge.SheafGradedAlgebra.sectionPieces` puts its sections
over `Γ(X, U)`. That is why `Stacks.SymGraded.freePieceEquiv` below carries no type ascription —
with one, the `Module` instance is not found. Whoever continues should settle on one spelling
(`ringSheafOfIsSheaf X.ringCatSheaf.property`, the vocabulary `symPowFreeIso` and
`freeCoordBasis` already share) and supply the bridges once, rather than meeting the clash
declaration by declaration.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open Stacks.AlgebraicGeometry.RelativeProjBridge

namespace Stacks.SymGraded

universe u

variable {X : Scheme.{u}} (ι : Type u) [Finite ι]

/-- The finite free module sheaf `𝒪_X^ι` on a scheme. -/
abbrev freeModule : X.Modules := SheafOfModules.free (R := X.ringCatSheaf) ι

/-- **The sectionwise degree-`k` symmetric power of a finite free module sheaf is a sheaf**, being
isomorphic to the free sheaf on the degree-`k` multidegrees. -/
theorem isSheaf_symPow_free (k : ℕ) :
    Presheaf.IsSheaf (Opens.grothendieckTopology X.carrier)
      (PresheafOfModules.symPow k (freeModule (X := X) ι).val).presheaf := by
  classical
  exact (Presheaf.isSheaf_of_iso_iff ((PresheafOfModules.toPresheaf _).mapIso
      (Stacks.SheafOfModules.symPowFreeIso X.ringCatSheaf.property k))).mpr
    (SheafOfModules.free (R := X.ringCatSheaf) {d : ι →₀ ℕ | d.degree = k}).isSheaf

/-- **The degree-`k` piece of `Sym(𝒪_X^ι)` is the free sheaf on the degree-`k` multidegrees.**
The sheafification is harmless because the sectionwise piece is already a sheaf. -/
def freePieceFreeIso [DecidableEq ι] (k : ℕ) :
    (Scheme.Modules.symmetricAlgebra X (freeModule (X := X) ι)).piece (k : ℤ) ≅
      SheafOfModules.free (R := X.ringCatSheaf) {d : ι →₀ ℕ | d.degree = k} :=
  ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).mapIso
      (Stacks.SheafOfModules.symPowFreeIso X.ringCatSheaf.property k)).trans
    (SheafOfModules.sheafifyValIso (Opens.grothendieckTopology X.carrier) _)

/-- **The degreewise comparison.** The sheafification unit identifies the sectionwise degree-`k`
symmetric power of `𝒪_X^ι` over an open with the sections of the degree-`k` piece of
`Sym(𝒪_X^ι)`. -/
def freePieceEquiv (k : ℕ) (U : (Opens X.carrier)ᵒᵖ) :=
  PresheafOfModules.unitAppEquiv (𝟙 X.ringCatSheaf.obj) _ (isSheaf_symPow_free ι k) U

/-- The degreewise comparison `freePieceEquiv` is the component over `U` of the sheafification
unit. -/
theorem freePieceEquiv_apply (k : ℕ) (U : (Opens X.carrier)ᵒᵖ)
    (x : (PresheafOfModules.symPow k (freeModule (X := X) ι).val).obj U) :
    freePieceEquiv ι k U x =
      PresheafOfModules.Hom.app
        (PresheafOfModules.sheafifyUnit (𝟙 X.ringCatSheaf.obj) _) U x :=
  rfl

/-- **The comparison takes the sectionwise unit to the unit of `Sym(𝒪_X^ι)`.** -/
theorem freePieceEquiv_one (U : (Opens X.carrier)ᵒᵖ) :
    freePieceEquiv ι 0 U ((sitePresheafAlgebra (freeModule (X := X) ι).val).one.eval U) =
      (Scheme.Modules.symmetricAlgebra X (freeModule (X := X) ι)).one.eval U :=
  (symmetricAlgebra_one_eval (freeModule (X := X) ι) U).symm

/-- **The comparison takes the sectionwise graded multiplication to the multiplication of
`Sym(𝒪_X^ι)`.** -/
theorem freePieceEquiv_mul (i j : ℕ) (U : (Opens X.carrier)ᵒᵖ)
    (x : (siteGradedPiece (freeModule (X := X) ι).val (i : ℤ)).obj U)
    (y : (siteGradedPiece (freeModule (X := X) ι).val (j : ℤ)).obj U) :
    freePieceEquiv ι (i + j) U ((siteMul (freeModule (X := X) ι).val i j).app U x y) =
      ((Scheme.Modules.symmetricAlgebra X (freeModule (X := X) ι)).mul (i : ℤ) (j : ℤ)).app U
        (freePieceEquiv ι i U x) (freePieceEquiv ι j U y) :=
  (symmetricAlgebra_mul_unit (freeModule (X := X) ι) (i : ℤ) (j : ℤ) U x y).symm

/-! ### Quasi-coherence, and the bundle -/

omit [Finite ι] in
/-- A finite free module sheaf is quasi-coherent. This is
`Stacks.AlgebraicGeometry.AffineQcohEquivalence.isQuasicoherent_free`, made an instance. -/
instance isQuasicoherent_freeModule : (freeModule (X := X) ι).IsQuasicoherent :=
  Stacks.AlgebraicGeometry.AffineQcohEquivalence.isQuasicoherent_free ι

omit [Finite ι] in
/-- **The homogeneous pieces of `Sym(𝒪_X^ι)` are quasi-coherent**, so the projective bundle of a
finite free module sheaf is unconditional. -/
@[ega "II 4.1.1" "special case"]
theorem isQuasicoherentPieces_free : IsQuasicoherentPieces (freeModule (X := X) ι) :=
  isQuasicoherentPieces_of_isQuasicoherent _

/-- **`Sym(𝒪_X^ι)` as the input of the relative `Proj` construction.** -/
abbrev freeSymGradedAlgebra : SheafGradedAlgebra X :=
  schemeSheafGradedAlgebra (freeModule (X := X) ι) (isQuasicoherentPieces_free ι)

/-- **The degreewise comparison is natural in the open.** Restriction of homogeneous sections of
`Sym(𝒪_X^ι)` along an inclusion of opens corresponds, under
`Stacks.SymGraded.freePieceEquiv`, to the restriction map of the sectionwise degree-`k`
symmetric power.

This is naturality of the sheafification unit, and it must be stated and used in this applied
form: `Stacks.AlgebraicGeometry.RelativeProjBridge.SheafGradedAlgebra.resPiece` and the
restriction map of the sheafification are definitionally equal but not *cheaply* so, and both
`rfl` and rewriting with `resPiece_apply` diverge on the equality of the two maps. -/
theorem resPiece_freePieceEquiv (k : ℕ) {U V : X.Opens} (h : U ≤ V)
    (x : (PresheafOfModules.symPow k (freeModule (X := X) ι).val).obj (op V)) :
    (freeSymGradedAlgebra ι).resPiece h k (freePieceEquiv ι k (op V) x) =
      freePieceEquiv ι k (op U)
        ((PresheafOfModules.symPow k (freeModule (X := X) ι).val).map (homOfLE h).op x) :=
  (PresheafOfModules.naturality_apply
    (PresheafOfModules.sheafifyUnit (𝟙 X.ringCatSheaf.obj)
      (PresheafOfModules.symPow k (freeModule (X := X) ι).val)) (homOfLE h).op x).symm

end Stacks.SymGraded

end
