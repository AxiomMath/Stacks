module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SlicePowerRestriction
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedSliceRestriction
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedAlgebraUniversalTransport
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PowerPresentationSequences
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SymmetricAlgebraConstruction.DegreeZero.Unit
import StacksCore.Tactic.StacksAttribute

/-!
# Comparing an exterior algebra with the slice site's own, through the sectionwise model

Let `(C, J)` be a site, `O♯` a sheaf of commutative rings on it, `M` a sheaf of modules over the
underlying sheaf of rings, `A` a sheaf of graded algebras with a square-zero degree-one
generator `gen : M ⟶ A.piece 1`, and `U : C`. This file provides the material for comparing `A`
restricted to the slice site `(Over U, J.over U)` with a graded algebra of `M|_U` there, in a
form that carries the **algebra structure** and not only a degreewise isomorphism of sheaves of
modules.

`Stacks.SheafOfModules.exteriorPowerOverIso`
(`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SlicePowerRestriction`) already compares
`(⋀ⁿ M)|_U` with `⋀ⁿ(M|_U)` for an arbitrary pair of exterior algebras, but it is assembled from
the two universal properties and carries no compatibility with the multiplication
`A.exterior.mul 1 n` or with the generator `A.exteriorGenerator`, which is what
`SheafOfModules.TensorExteriorSymmetricAlgebras.IsExteriorAnnihilated` is phrased in. The way to
such a compatibility is the one the implementation notes of
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorDeterminantInvertible` describe: compare
both sides through the model they are both sheafifications of, the degreewise sheafification of
the sectionwise exterior power, where the comparison is componentwise the identity, so that the
generator and the multiplication match on the nose.

## Main definitions

* `SheafOfModules.exteriorDescSq`: the comparison homomorphism **of sheaves of graded algebras**
  from the sheafified sectionwise exterior algebra of the sections of `M` to `A`. This is
  `SheafOfModules.exteriorDesc` with the universal property of `A` dropped — only the
  square-zero condition on the generator is used, since the unital homomorphism comes from the
  universal property of the *source*. That is what makes it applicable to the restriction
  `A.over U`, whose universal property is exactly what is not available.
* `SheafOfModules.overGen`: the degree-one generator restricted to the slice site, a degree-one
  generator of `SheafOfModules.GradedAlgebra.over`.
* `SheafOfModules.sliceRestrictIso`, `extPowOverPresheafIso`, `sectionwiseExtPowOverIso`:
  the comparison of the slice site's own sheafified sectionwise exterior power with the
  restriction of the one over `C`, written as a composite of its legs.
* `SheafOfModules.exteriorOverIso`: the comparison of `A.over U` with an arbitrary exterior
  algebra of `M|_U` on the slice site, as the degreewise comparison of two algebras universal
  for the same property.

## Main results

* `SheafOfModules.exteriorDescSq_gen` and `exteriorDescSq_sheafifyUnit_ιMulti`: the comparison
  homomorphism carries the degree-one generator to `gen`, and a wedge of local sections to the
  ordered product of their images under `gen`.
* `SheafOfModules.extPowCmp_eq_sheafifyUnit_comp_sq`: **the comparison morphism of Tag 01CG is
  the sheafification unit followed by `exteriorDescSq`**, with no universal property assumed of
  the target. This is `SheafOfModules.extPowCmp_eq_sheafifyUnit_comp` with `exteriorPieceIso`
  replaced by a homomorphism that exists without it.
* `SheafOfModules.squareZero_overGen`: the restricted generator is still square-zero.
* `SheafOfModules.sheafificationHomEquiv_symm_app`: the morphism out of a sheafification adjoint
  to `u`, read on a unit-image, is `u` there.
* `SheafOfModules.sheafifyOverHom_sheafifyUnit` and
  `sectionwiseExtPowOverIso_hom_sheafifyUnit`: **the comparison carries the unit-image of a
  local section over an object of the slice site to the unit-image of that section over the
  underlying object of `C`.** This is the computation that a compatibility with the algebra
  structure reduces to, both sides of such a compatibility being determined by their values on
  unit-images.
* `SheafOfModules.homogeneousProd_over` and `exteriorDescSq_over_app`: the ordered product of
  degree-one sections of `A.over U` is the ordered product in `A` over the underlying object of
  `C`, and **the comparison homomorphism over the slice site is the restriction of the one over
  `C`**, read through `sectionwiseExtPowOverIso`.
* `SheafOfModules.isIso_exteriorDescSq_app`, `exteriorPiece_eq_zero_of_neg` and
  `isIso_exteriorDescSq_over_app`: for an exterior algebra `A` of `M` the comparison
  homomorphism is invertible in every degree, over `C` and over the slice site; in a negative
  degree both sides are zero objects.
* `SheafOfModules.isExteriorAlgebra_over`: **the restriction of an exterior algebra of `M` to a
  slice site is an exterior algebra of `M|_U`**, on the restricted generator. This is the
  statement with the algebra structure that `Stacks.SheafOfModules.exteriorPowerOverIso` does
  not carry.
* `SheafOfModules.exteriorOverIso_generator`, `exteriorOverIso_mul` and `exteriorOverIso_one`:
  the resulting comparison is compatible with the generators, the multiplications and the
  units. These are the slice-site analogues of
  `SheafOfModules.TensorExteriorSymmetricAlgebras.exteriorAlgebraIso_generator` and
  `exteriorAlgebraIso_mul`, and they come from
  `SheafOfModules.GradedAlgebra.IsUniversal.pieceIso_generator`, `pieceIso_mul` and
  `pieceIso_one` with no further work.

## Implementation notes

**Why restriction to a slice site appears in two spellings.**
`PresheafOfModules.extPowOverIso` is stated at `PresheafOfModules.sliceRestrict`, which is
`PresheafOfModules.pushforward₀`, while
`Stacks.SheafOfModules.SliceSheafification.sheafifyOverHom` is stated at
`presheafOverFunctor`, which is `PresheafOfModules.pushforward` at the identity, i.e.
`pushforward₀` followed by `PresheafOfModules.restrictScalars (𝟙 _)`. The two functors are
*equal* — `sliceRestrict_eq_presheafOverFunctor` is `rfl` — but recognising that at a
**concrete** exterior power is a defeq query on the two module structures on `⋀ⁿ`, and that
query exceeds the heartbeat budget, exactly as the implementation notes of
`SlicePowerRestriction` record for the same reason. `sliceRestrictIso` therefore discharges the
comparison **once, for an arbitrary presheaf of modules**, where the module structures are
opaque and the query is cheap; every concrete use goes through that isomorphism instead of
through a defeq.

**Why the isomorphisms are `def`s with no ascribed type.** `sectionwiseExtPowOverIso` is the
same mathematics as `Stacks.SheafOfModules.sectionwiseExteriorPowerOverIso`, read backwards, but
it is written as a composite whose type Lean *computes* rather than one it has to match against
a given type: matching the degree-`n` piece of
`SheafOfModules.sectionwiseExteriorAlgebra` against a sheafification of
`PresheafOfModules.extPow` is the same unification that `SlicePowerRestriction` pays for once,
and paying it again inside each proof is what exhausts the budget. The two isomorphisms agree,
and `sectionwiseExtPowOverIso_hom_val_app` is the factorization through the legs.

**The two ordered products and the two spellings of the sheaf of rings.**
`SheafOfModules.homogeneousProd_over` is not `rfl`: `Stacks.GradedAlgebra.homogeneousProd` is
defined by recursion on the number of factors, and over the slice site it is instantiated at the
site universe `max u v` rather than `u`, so the two sides are different universe instances of one
recursive definition and the induction has to be done. Its universe arguments and its sheaf of
commutative rings are written out, because `?O ⋙ forget₂ _ RingCat =?= ((toRingCat J O♯).over
U).obj` is a higher-order unification problem that reassociating a triple composite would have to
solve, and leaving the module universe to `max w ?a =?= w` leaves a metavariable behind.

**No compiler option is set and no heartbeat limit is raised.** Every defeq here is at the default
budget. The discipline that makes that possible is the one above, together with naming the
implicit arguments `R₀`, `Rs`, `P`, `T` and `α` at each application: leaving the sheaf of rings
to be inferred poses `?Rs.obj =?= ((toRingCat J Osharp).over U).obj`, a metavariable under a
projection, which is the failure mode `SliceSheafification` documents.

## References

* [Stacks Project, Tag 01CG](https://stacks.math.columbia.edu/tag/01CG)
* [Stacks Project, Tag 0FJN](https://stacks.math.columbia.edu/tag/0FJN)
* [Stacks Project, Section 17.21](https://stacks.math.columbia.edu/tag/01CF)
-/

@[expose] public section

universe v u w

open CategoryTheory CategoryTheory.Sheaf Opposite PresheafOfModules
  Stacks.SheafOfModules.SliceSheafification

namespace SheafOfModules

section DescOfSquareZero

open _root_.SheafOfModules.GradedAlgebra

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  {Osharp : Sheaf J CommRingCat.{w}}
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]
  (M : SheafOfModules.{w} (toRingCat J Osharp))
  (A : GradedAlgebra.{w, w} (toRingCat J Osharp)) (gen : M ⟶ A.piece 1)
  (hgen : GradedAlgebra.SquareZero gen)

/-- The comparison homomorphism of sheaves of graded algebras from the sheafified sectionwise
exterior algebra of the sections of `M` to a graded algebra `A` carrying a square-zero
degree-one generator of `M`. -/
noncomputable def exteriorDescSq :
    GradedAlgebra.UnitalHom (sectionwiseExteriorAlgebra J (𝟙 Osharp.obj) M.val) A :=
  (isExteriorAlgebra_sectionwiseExteriorAlgebra J (𝟙 Osharp.obj) M.val).desc A
    ((sheafifySectionsIso M).hom ≫ gen)
    (GradedAlgebra.squareZero_comp (sheafifySectionsIso M).hom hgen)

/-- `SheafOfModules.exteriorDescSq` carries the degree-one generator of the sheafified
sectionwise exterior algebra to `gen`, on the unit-image of a local section. -/
theorem exteriorDescSq_gen (X : Cᵒᵖ) (m : M.val.obj X) :
    ((exteriorDescSq M A gen hgen).app 1).val.app X
        ((sectionwiseExteriorAlgebraGen J (𝟙 Osharp.obj) M.val).val.app X
          (Hom.app (sheafifyUnit (toRingCatMap J (𝟙 Osharp.obj)) M.val) X m)) =
      gen.val.app X m :=
  (SheafOfModules.hom_congr_app_apply
    ((isExteriorAlgebra_sectionwiseExteriorAlgebra J (𝟙 Osharp.obj) M.val).desc_extends A
      ((sheafifySectionsIso M).hom ≫ gen)
      (GradedAlgebra.squareZero_comp (sheafifySectionsIso M).hom hgen)) X _).trans
    (congrArg (fun z => gen.val.app X z) (sheafifySectionsIso_hom_unit M X m))

/-- **The value of `SheafOfModules.exteriorDescSq` on the unit-image of a wedge of local
sections** is the ordered product in `A` of the images of those sections under the generator. -/
theorem exteriorDescSq_sheafifyUnit_ιMulti (n : ℕ) (X : Cᵒᵖ) (s : Fin n → M.val.obj X) :
    ((exteriorDescSq M A gen hgen).app (n : ℤ)).val.app X
        (Hom.app (sheafifyUnit (toRingCatMap J (𝟙 Osharp.obj)) (extPow n M.val)) X
          (exteriorPower.ιMulti ((Osharp.obj ⋙ forget₂ _ RingCat).obj X) n s)) =
      A.toPresheafGradedAlgebra.homogeneousProd X n fun i => gen.val.app X (s i) := by
  refine Eq.trans (congrArg
    (fun z => ((exteriorDescSq M A gen hgen).app (n : ℤ)).val.app X z)
    (sheafifyUnit_extPow_ιMulti (𝟙 Osharp.obj) M.val n X s)) ?_
  refine Eq.trans (GradedAlgebra.UnitalHom.app_homogeneousProd
    (exteriorDescSq M A gen hgen) X n _) ?_
  exact congrArg (A.toPresheafGradedAlgebra.homogeneousProd X n)
    (funext fun i => exteriorDescSq_gen M A gen hgen X (s i))

/-- **The comparison morphism of Tag 01CG is the sheafification unit followed by the degreewise
comparison homomorphism**, with no universal property assumed of the target. -/
theorem extPowCmp_eq_sheafifyUnit_comp_sq (n : ℕ) :
    A.extPowCmp (hO := (toRingCat J Osharp).property) gen hgen n =
      sheafifyUnit (toRingCatMap J (𝟙 Osharp.obj)) (extPow n M.val) ≫
        (SheafOfModules.forget (toRingCat J Osharp)).map
          ((exteriorDescSq M A gen hgen).app (n : ℤ)) := by
  refine PresheafOfModules.hom_ext fun X => ModuleCat.hom_ext ?_
  refine ExteriorAlgebra.powExtₛₗ fun s => ?_
  refine Eq.trans (Stacks.GradedAlgebra.extCmpSections_ιMulti A.toPresheafGradedAlgebra gen.val
    (fun X x => hgen X x) n X s) ?_
  exact (exteriorDescSq_sheafifyUnit_ιMulti M A gen hgen n X s).symm

end DescOfSquareZero

section SheafificationHomEquivSymm

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {R₀ : Cᵒᵖ ⥤ RingCat.{w}} {Rs : Sheaf J RingCat.{w}} (α : R₀ ⟶ Rs.obj)
  [Presheaf.IsLocallyInjective J α] [Presheaf.IsLocallySurjective J α]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]

/-- **The morphism out of a sheafification adjoint to `u`, read on the unit-image of a local
section**, is `u` on that section. This is the `Equiv.symm` companion of
`PresheafOfModules.sheafificationHomEquiv_app`. -/
theorem sheafificationHomEquiv_symm_app {P : PresheafOfModules.{w} R₀}
    {T : SheafOfModules.{w} Rs}
    (u : P ⟶ (SheafOfModules.forget Rs ⋙ PresheafOfModules.restrictScalars α).obj T)
    (X : Cᵒᵖ) (m : P.obj X) :
    ((PresheafOfModules.sheafificationHomEquiv α).symm u).val.app X
        (Hom.app (sheafifyUnit α P) X m) = Hom.app u X m := by
  rw [← PresheafOfModules.sheafificationHomEquiv_app α
    ((PresheafOfModules.sheafificationHomEquiv α).symm u) X m, Equiv.apply_symm_apply]

end SheafificationHomEquivSymm

section Slice

open _root_.SheafOfModules.GradedAlgebra

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  {Osharp : Sheaf J CommRingCat.{w}}
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]
  (M : SheafOfModules.{w} (toRingCat J Osharp))
  (A : GradedAlgebra.{w, w} (toRingCat J Osharp)) (gen : M ⟶ A.piece 1)
  (hgen : GradedAlgebra.SquareZero gen) (U : C)
  [(J.over U).HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify (J.over U) AddCommGrpCat.{w}]

/-- The degree-one generator restricted to the slice site over `U`. -/
noncomputable def overGen : M.over U ⟶ (A.over U).piece 1 :=
  (SheafOfModules.overFunctor (toRingCat J Osharp) U).map gen

omit [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]
  [(J.over U).HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify (J.over U) AddCommGrpCat.{w}] in
include hgen in
theorem squareZero_overGen : GradedAlgebra.SquareZero (overGen M A gen U) :=
  fun V x => hgen (op V.unop.left) x

omit [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]
  [(J.over U).HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify (J.over U) AddCommGrpCat.{w}] in
/-- Restriction to a slice site of a presheaf of modules, in the two spellings used by
`PresheafOfModules.extPowOverIso` and by
`Stacks.SheafOfModules.SliceSheafification.sheafifyOverHom`, is the same functor. -/
theorem sliceRestrict_eq_presheafOverFunctor :
    sliceRestrict U (O := Osharp.obj) = presheafOverFunctor.{w} (toRingCat J Osharp) U := rfl

/-- Restriction to a slice site in the two spellings, as an isomorphism. It is the identity:
the two restriction functors are equal (`sliceRestrict_eq_presheafOverFunctor`). Stated for an
arbitrary presheaf of modules, so that the defeq query between the two module structures is
discharged once, abstractly, rather than at each concrete exterior power. -/
noncomputable def sliceRestrictIso (P : PresheafOfModules.{w} (toRingCat J Osharp).obj) :
    (sliceRestrict U (O := Osharp.obj)).obj P ≅
      (presheafOverFunctor.{w} (toRingCat J Osharp) U).obj P := Iso.refl _

omit [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]
  [(J.over U).HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify (J.over U) AddCommGrpCat.{w}] in
theorem sliceRestrictIso_hom_apply (P : PresheafOfModules.{w} (toRingCat J Osharp).obj)
    (V : (Over U)ᵒᵖ) (z : ((sliceRestrict U (O := Osharp.obj)).obj P).obj V) :
    Hom.app (sliceRestrictIso (Osharp := Osharp) U P).hom V z = z := rfl

/-- The presheaf of sectionwise exterior powers of `M|_U` compared with the restriction of the
presheaf of sectionwise exterior powers of `M`, in the spelling of restriction that
`Stacks.SheafOfModules.SliceSheafification.sheafifyOverHom` consumes. -/
noncomputable def extPowOverPresheafIso (n : ℕ) :=
  (extPowOverIso U n M.val).symm ≪≫ sliceRestrictIso (Osharp := Osharp) U (extPow n M.val)

/-- **Restriction to a slice site commutes with the sheafified sectionwise exterior power.**
This is `Stacks.SheafOfModules.sectionwiseExteriorPowerOverIso M U n` read backwards, written as
the composite of its two legs so that its type is the type of that composite. -/
noncomputable def sectionwiseExtPowOverIso (n : ℕ) :=
  (PresheafOfModules.sheafification.{w} (𝟙 ((toRingCat J Osharp).over U).obj)).mapIso
      (extPowOverPresheafIso M U n) ≪≫
    sheafifyOverIso.{w} (toRingCat J Osharp) U (extPow n M.val)

omit [(J.over U).HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
theorem sectionwiseExtPowOverIso_hom_val_app (n : ℕ) (V : (Over U)ᵒᵖ)
    (x : ((PresheafOfModules.sheafification.{w}
      (𝟙 ((toRingCat J Osharp).over U).obj)).obj (extPow (O := (Over.forget U).op ⋙ Osharp.obj) n
        ((sliceRestrict U (O := Osharp.obj)).obj M.val))).val.obj V) :
    (sectionwiseExtPowOverIso M U n).hom.val.app V x =
      (sheafifyOverHom.{w} (toRingCat J Osharp) U (extPow n M.val)).val.app V
        (((PresheafOfModules.sheafification.{w}
              (𝟙 ((toRingCat J Osharp).over U).obj)).map
            (extPowOverPresheafIso M U n).hom).val.app V x) := rfl

omit [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]
  [(J.over U).HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify (J.over U) AddCommGrpCat.{w}] in
/-- `SheafOfModules.extPowOverPresheafIso` is the identity on sections. -/
theorem extPowOverPresheafIso_hom_apply (n : ℕ) (V : (Over U)ᵒᵖ)
    (z : (extPow (O := (Over.forget U).op ⋙ Osharp.obj) n
      ((sliceRestrict U (O := Osharp.obj)).obj M.val)).obj V) :
    Hom.app (extPowOverPresheafIso M U n).hom V z =
      Hom.app (extPowOverIso U n M.val).inv V z := rfl

omit [(J.over U).HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- The comparison morphism adjoint to the restricted sheafification unit, read on the
unit-image of a local section: it is the unit-image of the same section over the underlying
object of `C`. -/
theorem sheafifyOverHom_sheafifyUnit (P : PresheafOfModules.{w} (toRingCat J Osharp).obj)
    (V : (Over U)ᵒᵖ) (y : ((presheafOverFunctor.{w} (toRingCat J Osharp) U).obj P).obj V) :
    (sheafifyOverHom.{w} (toRingCat J Osharp) U P).val.app V
        (Hom.app (sheafifyUnit (𝟙 ((toRingCat J Osharp).over U).obj)
          ((presheafOverFunctor.{w} (toRingCat J Osharp) U).obj P)) V y) =
      Hom.app (sheafifyUnit (𝟙 (toRingCat J Osharp).obj) P) ((Over.forget U).op.obj V) y :=
  sheafificationHomEquiv_symm_app (R₀ := ((toRingCat J Osharp).over U).obj)
    (Rs := (toRingCat J Osharp).over U) (𝟙 ((toRingCat J Osharp).over U).obj)
    (P := (presheafOverFunctor.{w} (toRingCat J Osharp) U).obj P)
    (T := ((PresheafOfModules.sheafification.{w} (𝟙 (toRingCat J Osharp).obj)).obj P).over U)
    (restrictedUnit.{w} (toRingCat J Osharp) U P) V y

omit [(J.over U).HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- **The comparison carries the unit-image of a local section of the sectionwise exterior power
over an object of the slice site to the unit-image of that section over the underlying object of
`C`.** -/
theorem sectionwiseExtPowOverIso_hom_sheafifyUnit (n : ℕ) (V : (Over U)ᵒᵖ)
    (z : (extPow (O := (Over.forget U).op ⋙ Osharp.obj) n
      ((sliceRestrict U (O := Osharp.obj)).obj M.val)).obj V) :
    (sectionwiseExtPowOverIso M U n).hom.val.app V
        (Hom.app (sheafifyUnit (𝟙 ((toRingCat J Osharp).over U).obj)
          (extPow (O := (Over.forget U).op ⋙ Osharp.obj) n
            ((sliceRestrict U (O := Osharp.obj)).obj M.val))) V z) =
      Hom.app (sheafifyUnit (𝟙 (toRingCat J Osharp).obj) (extPow n M.val))
        ((Over.forget U).op.obj V) (Hom.app (extPowOverPresheafIso M U n).hom V z) := by
  refine Eq.trans (sectionwiseExtPowOverIso_hom_val_app M U n V _) ?_
  refine Eq.trans (congrArg (fun t =>
    (sheafifyOverHom.{w} (toRingCat J Osharp) U (extPow n M.val)).val.app V t)
    (PresheafOfModules.unit_naturality_apply
      (R₀ := ((toRingCat J Osharp).over U).obj) (R := (toRingCat J Osharp).over U)
      (α := 𝟙 ((toRingCat J Osharp).over U).obj)
      (extPowOverPresheafIso M U n).hom V z)) ?_
  have h := sheafifyOverHom_sheafifyUnit U (extPow n M.val) V
    (Hom.app (extPowOverPresheafIso M U n).hom V z)
  exact h

omit [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]
  [(J.over U).HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify (J.over U) AddCommGrpCat.{w}] in
/-- The ordered product of degree-one sections in the restricted graded algebra is the ordered
product in `A` over the underlying object of `C`. -/
theorem homogeneousProd_over (V : (Over U)ᵒᵖ) (n : ℕ)
    (z : Fin n → ((A.over U).piece 1).val.obj V) :
    Stacks.GradedAlgebra.homogeneousProd.{v, max u v, w, w} (O := (Osharp.over U).obj)
        (A.over U).toPresheafGradedAlgebra V n z =
      Stacks.GradedAlgebra.homogeneousProd.{v, u, w, w} (O := Osharp.obj)
        A.toPresheafGradedAlgebra ((Over.forget U).op.obj V) n z := by
  induction n with
  | zero => rfl
  | succ n ih =>
      exact congrArg (fun y => (A.mul (n : ℤ) 1).app ((Over.forget U).op.obj V) y
        (z (Fin.last n))) (ih fun i => z i.castSucc)

/-- **The comparison homomorphism over the slice site is the restriction of the one over `C`**,
read through the comparison of the two sectionwise models. Both sides are morphisms out of a
sheafification, so they are determined by their values on the unit-image of a local section
(`PresheafOfModules.sheafification_hom_ext`), and there by their values on a wedge of local
sections (`ExteriorAlgebra.powExtₛₗ`). On such a wedge both sides are the ordered product of the
images of those sections under the generator — on the left by
`SheafOfModules.exteriorDescSq_sheafifyUnit_ιMulti` over the slice site, on the right by
`SheafOfModules.sectionwiseExtPowOverIso_hom_sheafifyUnit` followed by the same lemma over `C` —
and the two ordered products agree by `SheafOfModules.homogeneousProd_over`. -/
theorem exteriorDescSq_over_app (n : ℕ) :
    (exteriorDescSq (J := J.over U) (Osharp := Osharp.over U) (M.over U) (A.over U)
        (overGen M A gen U) (squareZero_overGen M A gen hgen U)).app (n : ℤ) =
      (sectionwiseExtPowOverIso M U n).hom ≫
        (SheafOfModules.overFunctor (toRingCat J Osharp) U).map
          ((exteriorDescSq M A gen hgen).app (n : ℤ)) := by
  refine PresheafOfModules.sheafification_hom_ext
    (PresheafOfModules.hom_ext fun V => ModuleCat.hom_ext ?_)
  refine ExteriorAlgebra.powExtₛₗ fun s => ?_
  have hL := exteriorDescSq_sheafifyUnit_ιMulti (J := J.over U) (Osharp := Osharp.over U)
    (M.over U) (A.over U) (overGen M A gen U) (squareZero_overGen M A gen hgen U) n V s
  have hR := sectionwiseExtPowOverIso_hom_sheafifyUnit M U n V
    (exteriorPower.ιMulti _ n s)
  have hR2 := exteriorDescSq_sheafifyUnit_ιMulti M A gen hgen n ((Over.forget U).op.obj V) s
  refine Eq.trans hL (Eq.symm ?_)
  refine Eq.trans (congrArg (fun z => ((SheafOfModules.overFunctor (toRingCat J Osharp) U).map
    ((exteriorDescSq M A gen hgen).app (n : ℤ))).val.app V z) hR) ?_
  exact Eq.trans hR2 (homogeneousProd_over A U V n _).symm

end Slice

section SliceUniversal

open _root_.SheafOfModules.GradedAlgebra

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  {Osharp : Sheaf J CommRingCat.{w}}
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]
  (M : SheafOfModules.{w} (toRingCat J Osharp))
  (A : GradedAlgebra.{w, w} (toRingCat J Osharp)) (gen : M ⟶ A.piece 1)
  (hA : GradedAlgebra.IsExteriorAlgebra A gen) (U : C)
  [(J.over U).HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify (J.over U) AddCommGrpCat.{w}]

include hA in
/-- For an exterior algebra `A` of `M`, the comparison homomorphism out of the sheafified
sectionwise exterior algebra is invertible in every degree: it is the degreewise comparison
`SheafOfModules.exteriorPieceIso` of two exterior algebras. -/
theorem isIso_exteriorDescSq_app (n : ℤ) : IsIso ((exteriorDescSq M A gen hA.1).app n) := by
  have h : (exteriorDescSq M A gen hA.1).app n = (exteriorPieceIso M A gen hA n).hom := rfl
  rw [h]
  infer_instance

include hA in
/-- **An exterior algebra has no nonzero sections in negative degrees.** Its negative pieces are
isomorphic to those of the sheafified sectionwise exterior algebra, which is the extension by
zero of a family indexed by the natural numbers. -/
theorem exteriorPiece_eq_zero_of_neg {n : ℤ} (hn : n < 0) (X : Cᵒᵖ)
    (y : (A.piece n).val.obj X) : y = 0 := by
  refine Eq.trans (SheafOfModules.hom_congr_app_apply
    (exteriorPieceIso M A gen hA n).inv_hom_id X y).symm ?_
  refine Eq.trans (congrArg (fun z => (exteriorPieceIso M A gen hA n).hom.val.app X z)
    (sectionwiseExteriorAlgebra_piece_eq_zero_of_neg J (𝟙 Osharp.obj) M.val hn X
      ((exteriorPieceIso M A gen hA n).inv.val.app X y))) ?_
  exact map_zero _

include hA in
/-- **The comparison homomorphism over the slice site is invertible in every degree.** In a
nonnegative degree this is `SheafOfModules.exteriorDescSq_over_app` together with the
invertibility over `C`; in a negative degree both source and target are zero objects. -/
theorem isIso_exteriorDescSq_over_app (n : ℤ) :
    IsIso ((exteriorDescSq (J := J.over U) (Osharp := Osharp.over U) (M.over U) (A.over U)
      (overGen M A gen U) (squareZero_overGen M A gen hA.1 U)).app n) := by
  by_cases hn : n < 0
  · refine CategoryTheory.Limits.IsZero.isIso ?_ ?_ _
    · rw [CategoryTheory.Limits.IsZero.iff_id_eq_zero]
      ext V x
      exact sectionwiseExteriorAlgebra_piece_eq_zero_of_neg (J.over U)
        (𝟙 (Osharp.over U).obj) (M.over U).val hn V x
    · rw [CategoryTheory.Limits.IsZero.iff_id_eq_zero]
      ext V y
      exact exteriorPiece_eq_zero_of_neg M A gen hA hn ((Over.forget U).op.obj V) y
  · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le (not_lt.1 hn)
    rw [exteriorDescSq_over_app M A gen hA.1 U m]
    have := isIso_exteriorDescSq_app M A gen hA (m : ℤ)
    exact IsIso.comp_isIso' (Iso.isIso_hom _) (Functor.map_isIso
      (SheafOfModules.overFunctor (toRingCat J Osharp) U) ((exteriorDescSq M A gen hA.1).app m))

include hA in
/-- **The restriction to a slice site of an exterior algebra is an exterior algebra of the
restricted sheaf of modules**, on the restricted generator. This is the statement that carries
the algebra structure, and it is what `Stacks.SheafOfModules.exteriorPowerOverIso` lacks: with it,
`SheafOfModules.GradedAlgebra.IsUniversal.pieceIso` compares `A.over U` degreewise with any
exterior algebra of `M.over U` on the slice site, compatibly with the generators
(`SheafOfModules.GradedAlgebra.IsUniversal.pieceIso_generator`), with the multiplications
(`pieceIso_mul`) and with the units (`pieceIso_one`). -/
theorem isExteriorAlgebra_over :
    GradedAlgebra.IsExteriorAlgebra (A.over U) (overGen M A gen U) := by
  have hsq : GradedAlgebra.SquareZero
      ((sheafifySectionsIso (J := J.over U) (Osharp := Osharp.over U) (M.over U)).hom ≫
        overGen M A gen U) :=
    GradedAlgebra.squareZero_comp _ (squareZero_overGen M A gen hA.1 U)
  have huniv := GradedAlgebra.IsExteriorAlgebra.of_desc_isIso
    (isExteriorAlgebra_sectionwiseExteriorAlgebra (J.over U) (𝟙 (Osharp.over U).obj)
      (M.over U).val)
    ((sheafifySectionsIso (J := J.over U) (Osharp := Osharp.over U) (M.over U)).hom ≫
      overGen M A gen U) hsq
    (fun n => isIso_exteriorDescSq_over_app M A gen hA U n)
  have h2 := GradedAlgebra.IsExteriorAlgebra.comp_iso huniv
    (sheafifySectionsIso (J := J.over U) (Osharp := Osharp.over U) (M.over U)).inv
    (sheafifySectionsIso (J := J.over U) (Osharp := Osharp.over U) (M.over U)).isIso_inv
  have h3 : (sheafifySectionsIso (J := J.over U) (Osharp := Osharp.over U) (M.over U)).inv ≫
      (sheafifySectionsIso (J := J.over U) (Osharp := Osharp.over U) (M.over U)).hom ≫
        overGen M A gen U = overGen M A gen U :=
    Iso.inv_hom_id_assoc _ _
  rw [h3] at h2
  exact h2

variable (B : GradedAlgebra.{w, w} (toRingCat (J.over U) (Osharp.over U)))
  (gen' : M.over U ⟶ B.piece 1)
  (hB : GradedAlgebra.IsExteriorAlgebra B gen')

/-- **Restriction to a slice site commutes with the exterior algebra, compatibly with the
algebra structure.** This is `Stacks.SheafOfModules.exteriorPowerOverIso` again, but obtained
from a universal property of `A.over U` itself, so that the compatibilities below come with it. -/
noncomputable def exteriorOverIso (n : ℤ) : (A.over U).piece n ≅ B.piece n :=
  GradedAlgebra.IsUniversal.pieceIso (isExteriorAlgebra_over M A gen hA U).isUniversal
    hB.isUniversal n

/-- The comparison of exterior algebras over the slice site carries one generator to the
other. -/
theorem exteriorOverIso_generator :
    overGen M A gen U ≫ (exteriorOverIso M A gen hA U B gen' hB 1).hom = gen' :=
  GradedAlgebra.IsUniversal.pieceIso_generator _ _

/-- The comparison of exterior algebras over the slice site is multiplicative on homogeneous
local sections. -/
theorem exteriorOverIso_mul (i j : ℤ) (V : (Over U)ᵒᵖ)
    (x : ((A.over U).piece i).val.obj V) (y : ((A.over U).piece j).val.obj V) :
    (exteriorOverIso M A gen hA U B gen' hB (i + j)).hom.val.app V
        (((A.over U).mul i j).app V x y) =
      (B.mul i j).app V ((exteriorOverIso M A gen hA U B gen' hB i).hom.val.app V x)
        ((exteriorOverIso M A gen hA U B gen' hB j).hom.val.app V y) :=
  GradedAlgebra.IsUniversal.pieceIso_mul _ _ i j V x y

/-- The comparison of exterior algebras over the slice site carries the unit to the unit. -/
theorem exteriorOverIso_one (V : (Over U)ᵒᵖ) :
    (exteriorOverIso M A gen hA U B gen' hB 0).hom.val.app V ((A.over U).one.eval V) =
      B.one.eval V :=
  GradedAlgebra.IsUniversal.pieceIso_one _ _ V

end SliceUniversal

end SheafOfModules

end
