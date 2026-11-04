module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafificationTensor
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafificationUnitSections
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafifiedDirectSum
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.QuasiCompactCoproductSections
public import StacksFrontier.AlgebraicGeometry.Constructions.GradedAlgebraSheafQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.CoproductCartesian

/-!
# The sections of a sheafified direct sum over a quasi-compact object

A coproduct of sheaves of modules is the sheafification of the objectwise direct sum, so over a
general object of the site its sections are strictly larger than the direct sum of the sections of
the summands: a section is only locally a finite sum. **Over a quasi-compact object the two
agree**, and that is what this file proves, in the form that the consumers need: the
sheafification unit

`⨁ᵢ Γ(W, Nᵢ) ⟶ Γ(W, ∐ᵢ Nᵢ)`

is bijective. The consequence drawn here is the one the ungraded realization of a sheaf of graded
algebras needs: the sections of `Stacks.GradedAlgebra.totalSheaf` over an affine open of a scheme
are the direct sum of the sections of the homogeneous pieces, *as a ring*.

## Main definitions

* `Stacks.DirectSumSections.sheafifiedCofan` and `isColimitSheafifiedCofan`: **the sheafification
  of the objectwise direct sum, as a colimit cofan of the sheafified summands.** The objectwise
  direct sum is the coproduct in presheaves of modules (`Stacks.directSumIsColimit`) and
  sheafification is a left adjoint, so this is `isColimitOfPreserves` and nothing more.
* `Stacks.DirectSumSections.unitEquiv`, `unitDirectSum` and `unitDirectSumInv`: the sheafification
  unit of a single summand on sections — bijective, because the summand is already a sheaf — and
  the direct sum of those units, with its inverse.
* `Stacks.RelativeSpec.totalSectionsRingEquiv`: **the ring of sections of the ungraded realization
  of a sheaf of graded algebras over an affine open, identified with the direct sum of the
  sections of the homogeneous pieces.**

## Main results

* `Stacks.DirectSumSections.bijective_sheafifyUnit_directSum_app`: **the sheafification unit of
  the objectwise direct sum of a family of sheaves of modules is bijective on the sections over a
  quasi-compact object of the site.**
* `Stacks.RelativeSpec.bijective_totalUnit_of_isAffineOpen`: **the sheafification unit of the
  ungraded realization is bijective on the sections over an affine open of a scheme.**

## Implementation notes

**Why no coproduct and no comparison isomorphism appear.** The obvious route is through
`Stacks.sheafifyDirectSumIso`, which identifies the sheafification of the objectwise direct sum
with the coproduct `∐ N`, and then `Stacks.Sites.bijective_coproductSectionsMap` at that
coproduct. Taking it costs one computation that is not in the library: the coproduct injections
have to be identified, under that isomorphism, with `Stacks.inclHom` followed by the
sheafification unit, and `Stacks.sheafifyDirectSumIso` is built from
`CategoryTheory.IsColimit.coconePointUniqueUpToIso` and
`CategoryTheory.IsColimit.precomposeHomEquiv`, so the identification has to be unfolded through
both.

It is avoided entirely by applying `bijective_coproductSectionsMap` to a *different* colimit
cofan: the one whose point is the sheafification of the objectwise direct sum itself and whose
injections are `(sheafification α).map (Stacks.inclHom _ i)`. That cofan is a colimit because
sheafification preserves the colimit `Stacks.directSumIsColimit`, and its comparison map on
sections is then computed by `Stacks.Sites.coproductSectionsMap_lof` together with naturality of
the sheafification unit — two rewrites, no isomorphism. The index family of that cofan is the
family of *sheafifications* of the summands rather than the summands themselves, and the
difference is absorbed by `unitDirectSum`, which is bijective because each summand is already a
sheaf.

**Why the summandwise unit is bijective.**
`Stacks.PresheafOfModules.bijective_sheafifyUnit_app_iff` at the identity comparison `𝟙 (N i).val`
into the sheaf `N i`: the identity is bijective on sections over every object, so the unit is too.
No counit and no triangle identity is needed.

**Bijectivity of `unitDirectSum` is proved by exhibiting the inverse**, summand by summand, rather
than by a pointwise formula for the components of the direct sum. Both work; the pointwise route
needs `DirectSum.of_eq_same` and `DirectSum.of_eq_of_ne` to rewrite under a dependent family whose
index function is eta-expanded by the surrounding abbreviations, and `rw` fails there with a
type-correctness error at `implicit` transparency. The two round-trip identities, by contrast, only
ever see `DirectSum.of`, and `DirectSum.toAddMonoid_of` discharges them. For the same reason
every step of `coproductSectionsMap_unitDirectSum` that crosses `DirectSum.of` against
`DirectSum.lof` is an `exact` and not a `rw`.

**The ring structure is free.** `Stacks.GradedAlgebra.totalUnit` is already a ring homomorphism —
it is the sheafification unit of `Stacks.GradedAlgebra.totalPresheaf`, which is a presheaf of
rings — so `Stacks.RelativeSpec.totalSectionsRingEquiv` is `RingEquiv.ofBijective` of it and
carries the graded multiplication of the direct sum to the multiplication of the sections with no
further argument.

**Quasi-compactness, not affineness, is what is used.** The scheme-level statements are phrased
for an affine open only because that is how their consumers arrive; the input is
`Stacks.SheafOfModules.isQuasiCompactObject_of_isCompact` applied to
`AlgebraicGeometry.IsAffineOpen.isCompact`, and no quasi-coherence of the pieces is needed
anywhere.

**No `@[stacks]` tag.** Tag 01AI is the assertion that sections over a quasi-compact open commute
with direct sums, and it is already carried by
`Stacks.SheafOfModules.preservesCoproducts_evaluation_of_isCompact`; what is below is that
assertion transported onto the sheafification unit of the objectwise direct sum, which is not
itself a tag's statement.

## References

* [Stacks Project, Tag 01AI](https://stacks.math.columbia.edu/tag/01AI)
* [Stacks Project, Tag 0935](https://stacks.math.columbia.edu/tag/0935)
* [Stacks Project, Section 17.21](https://stacks.math.columbia.edu/tag/01CF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite PresheafOfModules

universe v u w

namespace Stacks.DirectSumSections

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w}}
  [HasWeakSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  {ι : Type} [DecidableEq ι] (N : ι → SheafOfModules.{w} R)

omit [DecidableEq ι] in
/-- **The sheafification unit of a sheaf of modules, read as a presheaf of modules, is bijective
on the sections over every object.** The identity is a locally bijective comparison into that
sheaf and is bijective on sections, so
`Stacks.PresheafOfModules.bijective_sheafifyUnit_app_iff` applies. -/
theorem bijective_sheafifyUnit_val_app (i : ι) (W : Cᵒᵖ) :
    Function.Bijective (Hom.app (sheafifyUnit (𝟙 R.obj) (N i).val) W) :=
  (Stacks.PresheafOfModules.bijective_sheafifyUnit_app_iff (𝟙 R.obj) (N i)
      (𝟙 ((N i).val)) (Presheaf.isLocallyInjective_of_injective J _ fun _ => fun _ _ h => h)
      (Presheaf.isLocallySurjective_of_surjective J _ fun _ => fun y => ⟨y, rfl⟩) W).2
    ⟨fun _ _ h => h, fun y => ⟨y, rfl⟩⟩

/-- The cofan of the sheafifications of a family of sheaves of modules with point the
sheafification of the objectwise direct sum. -/
abbrev sheafifiedCofan :
    Cofan fun i => (PresheafOfModules.sheafification (𝟙 R.obj)).obj (N i).val :=
  Cofan.mk ((PresheafOfModules.sheafification (𝟙 R.obj)).obj (directSum fun i => (N i).val))
    fun i => (PresheafOfModules.sheafification (𝟙 R.obj)).map (inclHom (fun i => (N i).val) i)

/-- **That cofan is a colimit cofan**: the objectwise direct sum is the coproduct in presheaves of
modules and sheafification, being a left adjoint, preserves it. -/
def isColimitSheafifiedCofan : IsColimit (sheafifiedCofan N) :=
  Cofan.isColimitMapCoconeEquiv (PresheafOfModules.sheafification (𝟙 R.obj))
    (fun i => (N i).val) (directSumCofan fun i => (N i).val)
    (isColimitOfPreserves (PresheafOfModules.sheafification (𝟙 R.obj))
      (directSumIsColimit fun i => (N i).val))

/-- The sheafification unit of a summand on the sections over an object, as an equivalence. -/
def unitEquiv (i : ι) (W : Cᵒᵖ) : ((N i).val.obj W : Type w) ≃
    (((PresheafOfModules.sheafification (𝟙 R.obj)).obj (N i).val).val.obj W : Type w) :=
  Equiv.ofBijective _ (bijective_sheafifyUnit_val_app N i W)

omit [DecidableEq ι] in
/-- `Stacks.DirectSumSections.unitEquiv` is the sheafification unit on sections. -/
theorem unitEquiv_apply (i : ι) (W : Cᵒᵖ) (x : (N i).val.obj W) :
    unitEquiv N i W x = Hom.app (sheafifyUnit (𝟙 R.obj) (N i).val) W x := rfl

omit [DecidableEq ι] in
/-- The inverse of `Stacks.DirectSumSections.unitEquiv` is additive. -/
theorem unitEquiv_symm_add (i : ι) (W : Cᵒᵖ)
    (a b : ((PresheafOfModules.sheafification (𝟙 R.obj)).obj (N i).val).val.obj W) :
    (unitEquiv N i W).symm (a + b) =
      (unitEquiv N i W).symm a + (unitEquiv N i W).symm b :=
  (unitEquiv N i W).injective
    (((unitEquiv N i W).apply_symm_apply (a + b)).trans
      ((congrArg₂ (· + ·) ((unitEquiv N i W).apply_symm_apply a).symm
          ((unitEquiv N i W).apply_symm_apply b).symm).trans
        (map_add ((sheafifyUnit (𝟙 R.obj) (N i).val).app W).hom _ _).symm))

/-- The direct sum of the sheafification units of the summands, on the sections over an object. -/
def unitDirectSum (W : Cᵒᵖ) :
    DirectSumType (fun i => (N i).val) W →+
      DirectSumType
        (fun i => ((PresheafOfModules.sheafification (𝟙 R.obj)).obj (N i).val).val) W :=
  DirectSum.toAddMonoid fun i =>
    (DirectSum.of _ i).comp
      (AddMonoidHom.mk' (fun x => ((sheafifyUnit (𝟙 R.obj) (N i).val).app W).hom x)
        fun x y => map_add ((sheafifyUnit (𝟙 R.obj) (N i).val).app W).hom x y)

/-- `Stacks.DirectSumSections.unitDirectSum` sends `DirectSum.of _ i x` to `DirectSum.of _ i` of
the sheafification unit applied to `x`. -/
@[simp]
theorem unitDirectSum_of (W : Cᵒᵖ) (i : ι) (x : (N i).val.obj W) :
    unitDirectSum N W (DirectSum.of _ i x) =
      DirectSum.of _ i (Hom.app (sheafifyUnit (𝟙 R.obj) (N i).val) W x) :=
  DirectSum.toAddMonoid_of _ _ _

/-- The inverse of `Stacks.DirectSumSections.unitDirectSum`, summand by summand. -/
def unitDirectSumInv (W : Cᵒᵖ) :
    DirectSumType
        (fun i => ((PresheafOfModules.sheafification (𝟙 R.obj)).obj (N i).val).val) W →+
      DirectSumType (fun i => (N i).val) W :=
  DirectSum.toAddMonoid fun i =>
    (DirectSum.of _ i).comp
      (AddMonoidHom.mk' (fun y => (unitEquiv N i W).symm y) (unitEquiv_symm_add N i W))

/-- `Stacks.DirectSumSections.unitDirectSumInv` sends `DirectSum.of _ i y` to `DirectSum.of _ i`
of the inverse of `Stacks.DirectSumSections.unitEquiv` applied to `y`. -/
@[simp]
theorem unitDirectSumInv_of (W : Cᵒᵖ) (i : ι)
    (y : ((PresheafOfModules.sheafification (𝟙 R.obj)).obj (N i).val).val.obj W) :
    unitDirectSumInv N W (DirectSum.of _ i y) =
      DirectSum.of _ i ((unitEquiv N i W).symm y) :=
  DirectSum.toAddMonoid_of _ _ _

/-- The direct sum `Stacks.DirectSumSections.unitDirectSum` of the sheafification units of the
summands is bijective. -/
theorem bijective_unitDirectSum (W : Cᵒᵖ) : Function.Bijective (unitDirectSum N W) := by
  have h₁ : (unitDirectSumInv N W).comp (unitDirectSum N W) = AddMonoidHom.id _ :=
    DirectSum.addHom_ext fun i x =>
      (congrArg (unitDirectSumInv N W) (unitDirectSum_of N W i x)).trans
        ((unitDirectSumInv_of N W i _).trans
          (congrArg (DirectSum.of _ i) ((unitEquiv N i W).symm_apply_apply x)))
  have h₂ : (unitDirectSum N W).comp (unitDirectSumInv N W) = AddMonoidHom.id _ :=
    DirectSum.addHom_ext fun i y =>
      (congrArg (unitDirectSum N W) (unitDirectSumInv_of N W i y)).trans
        ((unitDirectSum_of N W i _).trans
          (congrArg (DirectSum.of _ i) ((unitEquiv N i W).apply_symm_apply y)))
  exact Function.bijective_iff_has_inverse.2
    ⟨unitDirectSumInv N W, DFunLike.congr_fun h₁, DFunLike.congr_fun h₂⟩

/-- **The comparison map of the colimit cofan, read on the direct sum of the units, is the
sheafification unit of the objectwise direct sum.** -/
theorem coproductSectionsMap_unitDirectSum (W : C)
    (z : DirectSumType (fun i => (N i).val) (op W)) :
    Stacks.Sites.coproductSectionsMap (sheafifiedCofan N) (op W) (unitDirectSum N (op W) z) =
      Hom.app (sheafifyUnit (𝟙 R.obj) (directSum fun i => (N i).val)) (op W) z := by
  induction z using DirectSum.induction_on with
  | zero =>
      rw [map_zero, map_zero]
      exact (map_zero ((sheafifyUnit (𝟙 R.obj)
        (directSum fun i => (N i).val)).app (op W)).hom).symm
  | of i x =>
      rw [unitDirectSum_of]
      refine Eq.trans ?_ (PresheafOfModules.unit_naturality_apply
        (inclHom (fun k => (N k).val) i) (op W) x)
      exact Stacks.Sites.coproductSectionsMap_lof (sheafifiedCofan N) (op W) i
        (Hom.app (sheafifyUnit (𝟙 R.obj) (N i).val) (op W) x)
  | add z z' hz hz' =>
      rw [map_add, map_add, hz, hz']
      exact (map_add ((sheafifyUnit (𝟙 R.obj)
        (directSum fun i => (N i).val)).app (op W)).hom _ _).symm

/-- **The sheafification unit of the objectwise direct sum of a family of sheaves of modules is
bijective on the sections over a quasi-compact object of the site**: over such an object the
sections of the coproduct are the direct sum of the sections of the summands. -/
theorem bijective_sheafifyUnit_directSum_app (W : C) (hW : J.IsQuasiCompactObject W) :
    Function.Bijective (Hom.app
      (sheafifyUnit (𝟙 R.obj) (directSum fun i => (N i).val)) (op W)) := by
  have hcop := Stacks.Sites.bijective_coproductSectionsMap (sheafifiedCofan N)
    (isColimitSheafifiedCofan N) W hW
  have hcomp : Function.Bijective
      (fun z => Stacks.Sites.coproductSectionsMap (sheafifiedCofan N) (op W)
        (unitDirectSum N (op W) z)) :=
    hcop.comp (bijective_unitDirectSum N (op W))
  exact (funext fun z => coproductSectionsMap_unitDirectSum N W z) ▸ hcomp

end Stacks.DirectSumSections

namespace Stacks.RelativeSpec

open _root_.AlgebraicGeometry TopologicalSpace

universe u'

variable (X : Scheme.{u'}) (A : SheafOfModules.GradedAlgebra.{u', u'} X.ringCatSheaf)
  (hc : ∀ (i j : ℤ) (W : (Opens ↥X)ᵒᵖ) (a : (A.piece i).val.obj W) (b : (A.piece j).val.obj W),
    HEq ((A.mul i j).app W a b) ((A.mul j i).app W b a))
  {V : X.Opens} (hV : IsAffineOpen V)

include hc hV in
/-- **The sheafification unit of the ungraded realization is bijective on the sections over an
affine open**: the sections of the ungraded realization of a sheaf of graded algebras over an
affine open are the direct sum of the sections of the homogeneous pieces. -/
theorem bijective_totalUnit_of_isAffineOpen :
    Function.Bijective (A.toPresheafGradedAlgebra.totalUnit
      (Opens.grothendieckTopology (X : TopCat)) (op V)) :=
  (Stacks.PresheafOfModules.bijective_sheafifyUnit_app_iff (𝟙 X.ringCatSheaf.obj)
      (AlgebraSheaf.underlyingModule (gradedAlgebraSheaf X A hc))
      (gradedDirectSumHom X A hc)
      (Stacks.GradedAlgebra.isLocallyInjective_toPresheaf_map_directSumHom _ _ _ _
        (isLocallyInjective_toTotalSheaf X A))
      (Stacks.GradedAlgebra.isLocallySurjective_toPresheaf_map_directSumHom _ _ _ _
        (isLocallySurjective_toTotalSheaf X A))
      (op V)).1
    (Stacks.DirectSumSections.bijective_sheafifyUnit_directSum_app (fun n : ℤ => A.piece n) V
      (Stacks.SheafOfModules.isQuasiCompactObject_of_isCompact V hV.isCompact))

include hc hV in
/-- **The ring of sections of the ungraded realization over an affine open is the direct sum of
the sections of the homogeneous pieces**, as a ring isomorphism: the sheafification unit is a
ring homomorphism, so its bijectivity upgrades for free. -/
def totalSectionsRingEquiv :
    A.toPresheafGradedAlgebra.Total (op V) ≃+*
      ((A.toPresheafGradedAlgebra.totalSheaf
        (Opens.grothendieckTopology (X : TopCat))).obj.obj (op V)) :=
  RingEquiv.ofBijective
    (A.toPresheafGradedAlgebra.totalUnit (Opens.grothendieckTopology (X : TopCat)) (op V))
    (bijective_totalUnit_of_isAffineOpen X A hc hV)

end Stacks.RelativeSpec

end
