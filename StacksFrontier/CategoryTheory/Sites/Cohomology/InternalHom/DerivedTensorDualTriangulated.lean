module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedCompositionUnit
public import StacksFrontier.CategoryTheory.Triangulated.ComponentwiseInvertibility
import StacksCore.Tactic.StacksAttribute

/-!
# The canonical map `M ⊗^L L^∨ ⟶ RSheafHom(L, M)` as a natural transformation of the dualized
variable

Let `(C, O)` be a ringed site and `M` an object of `D(O)`.  Stacks 08JD supplies the canonical
map

`Φ_L : M ⊗^L_O L^∨ ⟶ RSheafHom(L, M)`,

`AlgebraicGeometry.RingedSite.derivedTensorDualToSheafHom`, and
`AlgebraicGeometry.RingedSite.derivedTensorDualToSheafHom_naturality_source` says it is natural
in the **dualized** variable `L`, contravariantly.  This file packages that family and that
naturality as a single natural transformation of functors `D(O)ᵒᵖ ⥤ D(O)`, which is the form
in which the componentwise-invertibility machinery of
`StacksFrontier.CategoryTheory.Triangulated.ComponentwiseInvertibility` consumes a comparison map,
and records the invertibility statements that follow from it together with the base case of the
dévissage of Stacks 08JJ.

## Main definitions

* `AlgebraicGeometry.RingedSite.tensorDualSourceFunctor`: the source of `Φ` as a contravariant
  functor of the dualized object, `L ↦ M ⊗^L_O L^∨`.
* `AlgebraicGeometry.RingedSite.derivedTensorDualNatTrans`: `Φ` as a natural transformation
  `L ↦ M ⊗^L_O L^∨` to `L ↦ RSheafHom(L, M)` of functors `D(O)ᵒᵖ ⥤ D(O)`.

## Main results

* `AlgebraicGeometry.RingedSite.isIso_derivedTensorDualToSheafHom_of_sum_id_structureSheaf`:
  **`Φ_L` is invertible at every retract of a finite direct sum of copies of the structure
  sheaf.**  This is the dévissage step
  `AlgebraicGeometry.RingedSite.isIso_derivedTensorDualToSheafHom_of_sum_id` fed with the base
  case `AlgebraicGeometry.RingedSite.isIso_derivedTensorDualToSheafHom_structureSheaf`, and it
  is the first family of **nonzero** objects at which `Φ` is known to be invertible.
* `AlgebraicGeometry.RingedSite.isIso_derivedTensorDualToSheafHom_biproduct_structureSheaf`: the
  same at a finite direct sum of copies of the structure sheaf itself.
* `AlgebraicGeometry.RingedSite.isIso_derivedTensorDualToSheafHom_of_distTriang`: the dévissage
  step along a distinguished triangle, **conditional** on the two sides of `Φ` being
  shift-compatible exact functors of the dualized variable; see the section "What this file does
  not contain".
* `AlgebraicGeometry.RingedSite.isIso_derivedTensorDualToSheafHom_of_shift`: the dévissage step
  along a shift, **conditional** on `Φ` being compatible with the shift.

## Implementation notes

The source of `Φ` is the composite of the derived dual with the derived tensor product, and the
target is `(derivedSheafHomBifunctor X).flip.obj M`; both are functors `D(O)ᵒᵖ ⥤ D(O)` and
`Φ` is a natural transformation between them in that direction.  Note the orientation: the
dévissage of Stacks 08JJ runs over the object being **dualized**, which is the variable both
sides are contravariant in, and the base case of that dévissage is `L = O` with `M` arbitrary.
The transformation is *not* a transformation of covariant functors of `M`; that naturality is
`AlgebraicGeometry.RingedSite.derivedTensorDualToSheafHom_naturality` and is a separate
statement.

The two conditional statements take the shift data of the two functors as instance hypotheses
rather than deriving them, because the library does not have them; what they buy is that the
dévissage is reduced to those hypotheses alone, so that nothing else is missing from the
closure properties of the class `{L | IsIso (Φ_L)}`.

The universes are the diagonal `RingedSite.{u, u, u}` with the standard derived category, as in
every file of the derived internal Hom cluster.

## What this file does not contain

**Neither conditional statement is unconditional**, and the instance hypotheses they carry are
not available in the library.  Precisely:

* `L ↦ RSheafHom(L, M)` is **not** known to be a shift-compatible exact functor of the dualized
  variable.  What the library has is the existential form of Stacks 08JC in that variable,
  `AlgebraicGeometry.RingedSite.exists_distinguished_derivedSheafHom`, which supplies a
  connecting morphism making the image of a distinguished triangle distinguished, but no
  `CategoryTheory.Functor.CommShift` — the implementation notes of
  `StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedHomTriangulated` record that
  no such datum exists for the derived internal Hom in either variable, and
  `StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.Exactness` records that the
  adjunction route to one is unavailable because the development has the tensor–internal-Hom
  bijection of Stacks 08J8 only as a bijection of Hom groups,
  `AlgebraicGeometry.RingedSite.derivedCurryHomEquiv`, and not as a
  `CategoryTheory.Adjunction`.  Without a chosen connecting morphism the existential form cannot
  be upgraded: a triangle `(f, g, δ)` being distinguished does not make `(f, g, δ')`
  distinguished for the `δ'` that `CategoryTheory.Functor.mapTriangle` uses.
* `Φ` is **not** known to be compatible with the shift.  This is the content that the
  two-out-of-three step genuinely needs and that naturality alone does not give: for two
  distinguished triangles and a map of their first two vertices, the invertibility of those two
  maps does *not* force the invertibility of any map of the third vertices, so the connecting
  square is required.  `Stacks.CategoryTheory.ComponentwiseInvertibility.isIso_of_five` avoids
  assuming `CategoryTheory.NatTrans.CommShift` for `Φ`, at the price of hypotheses at the shifts
  of the two known vertices, which is why the triangle statement below is conditional only on
  the two functors and not on `Φ`; but the shift statement is conditional on `Φ`.

**How narrow the gap on the two functors actually is.** The triangle statement carries four
instance hypotheses and the shift statement three, but they are not four independent missing
data: every one of them reduces to a **single** datum, a
`CategoryTheory.Functor.CommShift` and a `CategoryTheory.Functor.IsTriangulated` for
`(derivedSheafHomBifunctor X).flip.obj N`, the derived internal Hom in its **dualized** variable,
at `N = M` for the target and at `N = O` for the source. The source is a composite,
`AlgebraicGeometry.RingedSite.tensorDualSourceFunctor` being
`(derivedSheafHomBifunctor X).flip.obj (derivedStructureSheaf X) ⋙ T.tensor.obj M`, and its
tensor factor is **free**: `commShift_right` and `exact_right` are fields of the derived tensor
product datum of Stacks 06YU, registered as instances
(`StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.OnARingedSite` and
`…DerivedTensor.Interface`). So nothing is owed for the tensor; what is owed is the dual, twice.

**Two routes to that datum, one of which is a circle.** The commutativity constraint
`Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.braidingIso` of [Stacks, Tag 0FPT] does
**not** supply it, and the reason is worth recording so that the route is not retried: composing
Stacks 08J8 at `(K, L, M)`, the braiding, and Stacks 08J8 at `(L, K, M)` gives the
self-adjointness of the pairing, `Hom(K, RSheafHom(L, M)) ≅ Hom(L, RSheafHom(K, M))`, which
exhibits `RSheafHom(-, M)` as a right adjoint of the same functor conjugated by `op`. The
principle that a right adjoint of a triangulated functor is triangulated then transfers this
statement's hypothesis to its own conclusion.

The non-circular route runs through the **second** variable and Yoneda. The adjunction
`(- ⊗^L_O L) ⊣ RSheafHom(L, -)` is derivable — not from
`AlgebraicGeometry.RingedSite.derivedCurryHomEquiv`, which carries no naturality of its own, but
from `AlgebraicGeometry.RingedSite.derivedCurryNatIso` of
`StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedCurryingNaturality`, the natural
isomorphism of trifunctors, with
`AlgebraicGeometry.RingedSite.derivedCurryIso_natural`. That gives the shift compatibility of
`RSheafHom(L, -)` in the second variable, and then

`Hom(K, RSheafHom(L⟦1⟧, M)) ≅ Hom(K ⊗^L L⟦1⟧, M) ≅ Hom((K ⊗^L L)⟦1⟧, M)`
`≅ Hom(K ⊗^L L, M⟦-1⟧) ≅ Hom(K, RSheafHom(L, M)⟦-1⟧)`

identifies `RSheafHom(L⟦1⟧, M)` with `RSheafHom(L, M)⟦-1⟧`, which is the dualized-variable
datum. The middle step is `commShift_right` of Stacks 06YU, so no step of the chain is the
statement being proved.

In consequence the hypothesis `hdual` of Stacks 0A0A —
`AlgebraicGeometry.RingedSite.isDerivedLimit_tensorDerivedDual_of_isHomotopyColimit'` — is **not
discharged** by this file.  What is new here is that the class of objects at which `Φ` is
invertible is now known to contain nonzero objects, namely the retracts of finite direct sums of
copies of the structure sheaf; the Koszul complexes that Stacks 0A0E feeds to Stacks 0A0A are
*not* among them, since they are two-term complexes and reaching them needs exactly the shift
and the cone, which are the two conditional statements.

## References

* [Stacks Project, Tag 08JD](https://stacks.math.columbia.edu/tag/08JD)
* [Stacks Project, Tag 08JJ](https://stacks.math.columbia.edu/tag/08JJ)
* [Stacks Project, Tag 08JC](https://stacks.math.columbia.edu/tag/08JC)
* [Stacks Project, Tag 0A0A](https://stacks.math.columbia.edu/tag/0A0A)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite

namespace AlgebraicGeometry.RingedSite

open Stacks.CategoryTheory.ComponentwiseInvertibility

universe u

attribute [local instance] HasDerivedCategory.standard

variable (X : RingedSite.{u, u, u})
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u,
    u} X.O))
      (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]
  (T : Stacks.SheafOfModules.DerivedTensorProduct X)

/-! ## `Φ` as a natural transformation of the dualized variable -/


/-- **The canonical map of Stacks 08JD as a natural transformation of the dualized variable.**
Its component at `L` is `Φ_L : M ⊗^L_O L^∨ ⟶ RSheafHom(L, M)` and its naturality is
`AlgebraicGeometry.RingedSite.derivedTensorDualToSheafHom_naturality_source`. -/
def derivedTensorDualNatTrans
    (M : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    tensorDualSourceFunctor X T M ⟶ (derivedSheafHomBifunctor X).flip.obj M where
  app L := derivedTensorDualToSheafHom X T L.unop M
  naturality _ _ f := derivedTensorDualToSheafHom_naturality_source X T f.unop M

/-- The component of `derivedTensorDualNatTrans X T M` at `op L` is
`derivedTensorDualToSheafHom X T L M`. -/
@[simp]
lemma derivedTensorDualNatTrans_app
    (M L : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    (derivedTensorDualNatTrans X T M).app (op L) = derivedTensorDualToSheafHom X T L M :=
  rfl

/-! ## Invertibility at the retracts of finite free objects -/

/-- **The canonical map of Stacks 08JD is invertible at every retract of a finite direct sum of
copies of the structure sheaf.**  The hypothesis is the decomposition of the identity of `L` as
a finite sum `∑ k ∈ s, r k ≫ i k` of composites through the structure sheaf, which is exactly
what exhibits `L` as such a retract.

This is the dévissage step
`AlgebraicGeometry.RingedSite.isIso_derivedTensorDualToSheafHom_of_sum_id` with its hypothesis
discharged at every index by the base case
`AlgebraicGeometry.RingedSite.isIso_derivedTensorDualToSheafHom_structureSheaf`.  It is the
first family of nonzero objects at which the canonical map is known to be invertible: the
section "What this file does not contain" of
`StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedTensorDualDevissage` records
that before the base case the only such object was the zero object. -/
theorem isIso_derivedTensorDualToSheafHom_of_sum_id_structureSheaf
    {ι : Type*} (s : Finset ι)
    {L : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (i : ι → (derivedStructureSheaf X ⟶ L)) (r : ι → (L ⟶ derivedStructureSheaf X))
    (hir : ∑ k ∈ s, r k ≫ i k = 𝟙 L)
    (M : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    IsIso (derivedTensorDualToSheafHom X T L M) :=
  isIso_derivedTensorDualToSheafHom_of_sum_id X T s i r hir M
    fun _ ↦ isIso_derivedTensorDualToSheafHom_structureSheaf X T M

/-- **The canonical map of Stacks 08JD is invertible at a finite direct sum of copies of the
structure sheaf.**  The identity of the direct sum is the sum of the composites of its
projections with its inclusions, so this is the previous statement at that decomposition. -/
theorem isIso_derivedTensorDualToSheafHom_biproduct_structureSheaf
    {ι : Type} [Finite ι] [HasBiproduct fun _ : ι ↦ derivedStructureSheaf X]
    (M : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    IsIso (derivedTensorDualToSheafHom X T (⨁ fun _ : ι ↦ derivedStructureSheaf X) M) :=
  isIso_derivedTensorDualToSheafHom_of_biproduct X T _ M
    fun _ ↦ isIso_derivedTensorDualToSheafHom_structureSheaf X T M

/-! ## The two conditional dévissage steps -/

/-- Invertibility of `Φ` at `op L` shifted by `n` is invertibility at `L⟦m⟧`, for `n + m = 0`. -/
private theorem isIso_app_shift_op_iff
    (M L : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (n m : ℤ) (h : n + m = 0) :
    IsIso ((derivedTensorDualNatTrans X T M).app ((op L)⟦n⟧)) ↔
      IsIso (derivedTensorDualToSheafHom X T (L⟦m⟧) M) :=
  NatTrans.isIso_app_iff_of_iso (derivedTensorDualNatTrans X T M)
    ((Pretriangulated.shiftFunctorOpIso _ n m h).app (op L))

/-- **The dévissage step of Stacks 08JJ along a distinguished triangle**, conditional on the two
sides of the canonical map being shift-compatible exact functors of the dualized variable.

Given a distinguished triangle `L₁ ⟶ L₂ ⟶ L₃ ⟶ L₁⟦1⟧` of `D(O)` and the invertibility of
`Φ` at `L₂`, `L₃` and at their shifts by `-1`, the canonical map is invertible at `L₁`.  The
appearance of the shifts, and the absence of any compatibility of `Φ` with the shift, is
explained in the implementation notes of
`StacksFrontier.CategoryTheory.Triangulated.ComponentwiseInvertibility`: two distinguished triangles
and a map of their first two vertices do not determine a map of the third vertices, so a plain
two-out-of-three along the two commuting squares that naturality supplies is false, and the
five-lemma form used here pays for the missing connecting square with the hypotheses at the
shifts.

The dualized variable is the contravariant one, so the triangle is read in `D(O)ᵒᵖ` through
`CategoryTheory.Pretriangulated.triangleOpEquivalence`, where `L₁` is the third vertex; the two
shifts by `1` of `D(O)ᵒᵖ` become the shifts by `-1` of `D(O)` by
`CategoryTheory.Pretriangulated.shiftFunctorOpIso`.

The two instance hypotheses are **not available in the library**; see the section "What this
file does not contain". -/
theorem isIso_derivedTensorDualToSheafHom_of_distTriang
    (M : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    [(tensorDualSourceFunctor X T M).CommShift ℤ]
    [((derivedSheafHomBifunctor X).flip.obj M).CommShift ℤ]
    [(tensorDualSourceFunctor X T M).IsTriangulated]
    [((derivedSheafHomBifunctor X).flip.obj M).IsTriangulated]
    (Tri : Triangle
      (DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))))
    (hTri : Tri ∈ distTriang
      (DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))))
    (h₂ : IsIso (derivedTensorDualToSheafHom X T Tri.obj₂ M))
    (h₃ : IsIso (derivedTensorDualToSheafHom X T Tri.obj₃ M))
    (h₂' : IsIso (derivedTensorDualToSheafHom X T (Tri.obj₂⟦(-1 : ℤ)⟧) M))
    (h₃' : IsIso (derivedTensorDualToSheafHom X T (Tri.obj₃⟦(-1 : ℤ)⟧) M)) :
    IsIso (derivedTensorDualToSheafHom X T Tri.obj₁ M) := by
  have hop := Pretriangulated.op_distinguished Tri hTri
  exact isIso_app_third_of_distinguished _ _ (derivedTensorDualNatTrans X T M) _ hop
    h₃ h₂ 
    ((isIso_app_shift_op_iff X T M _ 1 (-1) (by ring)).2 h₃')
    ((isIso_app_shift_op_iff X T M _ 1 (-1) (by ring)).2 h₂')

/-- **The dévissage step of Stacks 08JJ along a shift**, conditional on the canonical map being
compatible with the shift: if `Φ` is invertible at `L` then it is invertible at `L⟦n⟧`.

The instance hypotheses are **not available in the library**; see the section "What this file
does not contain".  The shift by `n` of `D(O)` is the shift by `-n` of `D(O)ᵒᵖ`, the dualized
variable being the contravariant one.

The component of a shift-compatible transformation at a shifted object is
`CategoryTheory.NatTrans.app_shift`, which is used inline here; the same two lines appear as the
general statement `StacksDraft.CompactDevissage.isIso_app_shift`, which is not imported because
its module brings in the whole compact-generation cluster. -/
theorem isIso_derivedTensorDualToSheafHom_of_shift
    (M : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    [(tensorDualSourceFunctor X T M).CommShift ℤ]
    [((derivedSheafHomBifunctor X).flip.obj M).CommShift ℤ]
    [NatTrans.CommShift (derivedTensorDualNatTrans X T M) ℤ]
    (L : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) (n : ℤ)
    (h : IsIso (derivedTensorDualToSheafHom X T L M)) :
    IsIso (derivedTensorDualToSheafHom X T (L⟦n⟧) M) := by
  have hshift : IsIso ((derivedTensorDualNatTrans X T M).app ((op L)⟦(-n : ℤ)⟧)) := by
    have h' : IsIso ((derivedTensorDualNatTrans X T M).app (op L)) := h
    have : IsIso (((derivedTensorDualNatTrans X T M).app (op L))⟦(-n : ℤ)⟧') :=
      Functor.map_isIso _ _
    rw [NatTrans.app_shift (derivedTensorDualNatTrans X T M) (-n) (op L)]
    infer_instance
  exact (isIso_app_shift_op_iff X T M L (-n) n (by ring)).1 hshift

end AlgebraicGeometry.RingedSite

end
