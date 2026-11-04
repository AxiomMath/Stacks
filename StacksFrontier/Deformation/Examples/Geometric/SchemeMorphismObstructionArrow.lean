module

public import StacksFrontier.Deformation.Examples.Geometric.SchemeMorphismLiftClass
public import StacksFrontier.Deformation.Examples.Geometric.SchemeMorphismSixTerm
public import StacksFrontier.Deformation.RingedSpaceThickening.NaiveCotangentDerivedTwoTerm
public import StacksFrontier.Deformation.RingedSpaceThickening.NaiveCotangentLiftingObstruction

/-!
# The obstruction arrow of the sequence of Stacks 0E3V

Let `f : X ⟶ Y` be a morphism of schemes over a field `k`. For tangent spaces taken with
coefficients in a finite-dimensional `k`-vector space `M`, i.e. over the square-zero base
`k ⊕ M`, the sixth term of the exact sequence of [Stacks Project, Tag 0E3V] is
`Ext¹_{𝒪_X}(Lf^*𝖭𝖫_{Y/k}, 𝒪_X ⊗_k M)`, built by
`Deformation.Examples.schemeMorphismObstructionExtTwisted`, and the sixth arrow of the sequence
is the obstruction map

`ob : T(Def_X × Def_Y) ⟶ Ext¹_{𝒪_X}(Lf^*𝖭𝖫_{Y/k}, 𝒪_X ⊗_k M)`

of the last paragraph of the source's proof. The source's own sequence is the case `M = k`,
where the coefficient sheaf `𝒪_X ⊗_k M` is canonically `𝒪_X` and the sixth term is canonically
`Deformation.Examples.schemeMorphismObstructionExt`.
`Deformation.Examples.exact_schemeMorphismTangentPair_obstruction` proves exactness at the fifth
spot while *carrying* that arrow as a hypothesis `ob`, pinned by `hob` to have as its zero locus
exactly the pairs of first-order deformations along which `f` deforms. This file constructs the
arrow and discharges `hob`.

What the arrow is built out of is the source's own recipe. Step 1 of the proof of
[Stacks Project, Tag 08U8] reads off from a pair of deformations a homomorphism
`ξ : 𝒥/𝒥² ⟶ 𝒪_X ⊗_k M` out of the conormal term of a two-term naive cotangent complex, and the
obstruction is the class of `ξ` in `Ext¹`, which is
`AlgebraicGeometry.RingedSpaceThickening.liftingObstruction` — by definition
`NaiveCotangentTwoTerm.conormalExtClass`. So `ob` is here *that class*, taken at the two-term
structure `P` of `Lf^*𝖭𝖫_{Y/k}`, and `schemeMorphismObstructionArrow_apply` pins it to be
exactly that; a bare function with the right zero locus would be satisfied by anything.

## Main results

* `Deformation.Examples.nonempty_globalLiftsOverBase_iff_exists_schemeMorphismDeformation`:
  **`f` deforms along a pair of first-order deformations of its endpoints exactly when it lifts
  to a morphism between their total spaces.** This is the geometric half of the last paragraph
  of the source's proof, and it is proved, not carried.
* `Deformation.Examples.schemeMorphismObstructionArrow_apply`: **the arrow is the class of the
  Step 1 homomorphism.** The value at a pair of classes of deformations is the `Ext¹` class of
  `ξ` at any pair of representatives. This is what makes the arrow a construction rather than a
  choice: it descends to the tangent module along `Deformation.tangentClassAt` and its value is
  determined by `ξ`.
* `Deformation.Examples.schemeMorphismObstructionArrow_eq_zero_iff`: **the zero locus of the
  arrow is the set of pairs along which `f` deforms**, which is the hypothesis `hob` of
  `Deformation.Examples.exact_schemeMorphismTangentPair_obstruction`, discharged.
* `Deformation.Examples.exact_schemeMorphismTangentPair_schemeMorphismObstructionArrow`:
  **[Stacks Project, Tag 0E3V], exactness at the fifth spot with the obstruction arrow
  constructed.** The sequence
  `T Def_{X ⟶ Y} → T(Def_X × Def_Y) → Ext¹_{𝒪_X}(Lf^*𝖭𝖫_{Y/k}, 𝒪_X ⊗_k M)` is exact at its
  middle term, the third map being `Deformation.Examples.schemeMorphismObstructionArrow` and not
  a hypothesis.
* `Deformation.Examples.exact_schemeMorphismTangentPair_obstructionArrow_derivedPullback`: **the
  same at the two-term structure of `Lf^*𝖭𝖫_{Y/k}` itself.** Here the two-term structure is not
  carried either — K-flatness of `𝖭𝖫_{Y/k}` is carried in its place — and the Step 1
  homomorphism is a map `f^*(𝒥/𝒥²) ⟶ 𝒪_X ⊗_k M` out of the source's own conormal module,
  factoring through `f^*Ω_{Y/k}` along
  `AlgebraicGeometry.RingedSpaceThickening.pulledConormalMap`.

## Main definitions

* `Deformation.Examples.schemeMorphismObstructionArrow`: **the sixth arrow of the sequence of
  [Stacks Project, Tag 0E3V]**, the map from `T(Def_X × Def_Y)` to
  `Ext¹_{𝒪_X}(Lf^*𝖭𝖫_{Y/k}, 𝒪_X ⊗_k M)` sending the pair of classes of two first-order
  deformations to the `Ext¹` class of the Step 1 homomorphism of [Stacks Project, Tag 08U8]
  attached to them.

## Implementation notes

**What is constructed and what is carried.** The arrow, its descent to the tangent module, the
geometric half of the source's last paragraph and the exactness are proved here. What is carried
is an input of [Stacks Project, Tag 08U8], not of [Stacks Project, Tag 0E3V]:

* the two-term structure `P` of `Lf^*𝖭𝖫_{Y/k}` with `hP : P.obj = Lf^*𝖭𝖫_{Y/k}`, exactly as
  `AlgebraicGeometry.RingedSpaceThickening.solutionsEquivDerivedExtFibre` and
  `nonempty_deformationSolution_iff_obstruction_eq_zero` carry theirs.
  `AlgebraicGeometry.RingedSpaceThickening.derivedPullbackNaiveCotangentTwoTerm` is the intended
  instance, where `hP` is `rfl` by `derivedPullbackNaiveCotangentTwoTerm_obj`, at the cost of a
  K-flatness hypothesis on `𝖭𝖫_{Y/k}`;
  `exact_schemeMorphismTangentPair_obstructionArrow_derivedPullback` is the statement at that
  instance, and there `P` and `hP` are gone;
* the family `ξ` of Step 1 homomorphisms of [Stacks Project, Tag 08U8], one for each pair of
  objects of the two fibres, with `hinv`, the invariance of its `Ext¹` class under isomorphism
  in those fibres;
* `hfactor`, clause (1) of [Stacks Project, Tag 08U8] at this situation: that `ξ` factors
  through the degree `0` term exactly when `f` lifts to a morphism `X' ⟶ Y'` of the two total
  spaces over the base. This mentions only the two deformations and the lifts of `f` between
  them — not the deformation category of morphisms, not its fibres and not the tangent module.
  Bridging it to the source's "`f` deforms along the pair" is
  `nonempty_globalLiftsOverBase_iff_exists_schemeMorphismDeformation`, which is proved below out
  of `Deformation.Examples.liftDeformationFiberObject` and
  `Deformation.Examples.exists_globalLift_of_isIsomorphic_endpoints`.

**Why `ξ` is indexed by fibre objects and not by tangent classes.** The Step 1 homomorphism
depends on the deformations themselves; only its `Ext¹` class is an invariant of their
isomorphism classes. So `ξ` takes objects of the fibres, and the descent of the *class* along
`Deformation.tangentClassAt` is the hypothesis `hinv`, which is the invariance the source's
Step 1 asserts and nothing stronger. The descent itself is by
`Deformation.tangentClassAt_surjective` and `Deformation.tangentClassAt_eq_iff`, and
`schemeMorphismObstructionArrow_apply` is what records that the choice of representatives does
not matter.

**The coefficient module `M`.** The tangent spaces are taken over the square-zero base
`k ⊕ M` for a finite-dimensional `k`-vector space `M`, and the arrow is built for each such
`M`. Its target is twisted to match: the ideal sheaf of the special fibre of a deformation of
`X` over `k ⊕ M` is `𝒪_X ⊗_k M`, so the Step 1 homomorphism of [Stacks Project, Tag 08U8] is a
map `𝒥/𝒥² ⟶ 𝒪_X ⊗_k M` and its class lies in `Ext¹_{𝒪_X}(Lf^*𝖭𝖫_{Y/k}, 𝒪_X ⊗_k M)`, which is
`Deformation.Examples.schemeMorphismObstructionExtTwisted`. The source's sequence is the case
`M = k`, where the coefficient sheaf is canonically `𝒪_X` and that group is canonically the
untwisted `Deformation.Examples.schemeMorphismObstructionExt`; for `M` of dimension greater than
one there is no canonical map from the twisted group to the untwisted one, which is why the
target has to be the twisted one for the statement to be about the source's obstruction at all.

## References

* [Stacks Project, Tag 0E3V](https://stacks.math.columbia.edu/tag/0E3V)
* [Stacks Project, Tag 08U8](https://stacks.math.columbia.edu/tag/08U8)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.RingedSpaceThickening

universe u

attribute [local instance 10000] HasDerivedCategory.standard

namespace Deformation.Examples

variable {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
variable {X Y : Scheme.{u}} (f : X ⟶ Y)
  (pX : X ⟶ baseSpec (residueFieldBase Λ k)) (pY : Y ⟶ baseSpec (residueFieldBase Λ k))
  (hf : f ≫ pY = pX)

/-! ### `f` deforms along a pair exactly when it lifts between the total spaces -/

section Lifts

variable
  (hM : IsDeformationCategory.{u, u, u}
    (schemeMorphismDeformationCategoryProjection f pX pY hf))
  (hX : IsDeformationCategory.{u, u, u}
    (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pX)))
  {A : ArtinianLocalAlgCat.{u, u, u} Λ k}

include hM hX in
/-- **Stacks 0E3V: `f` deforms along a pair of deformations of its endpoints exactly when it
lifts to a morphism between their total spaces.** Let `X'` and `Y'` be deformations of `X` and
of `Y` over one object `A` of `𝒞_Λ`. Then some deformation of `f` over `A` has `X'` and `Y'` as
its endpoints up to isomorphism in the two fibres — the right-hand side of
`Deformation.Examples.exists_schemeMorphismTangentPair_eq_iff`, the source's "`f` deforms along
the pair" — exactly when there is a morphism `X' ⟶ Y'` over `baseSpec A` restricting to `f` on
the special fibre.

Both directions are in the library: a lift determines a deformation of `f` whose endpoints are
`X'` and `Y'` (`Deformation.Examples.liftDeformationFiberObject` with
`isIsomorphic_sourceFiber_liftDeformationFiberObject` and
`isIsomorphic_targetFiber_liftDeformationFiberObject`), and a deformation of `f` with those
endpoints yields a lift by transporting its arrow along the two isomorphisms
(`Deformation.Examples.exists_globalLift_of_isIsomorphic_endpoints`).

This is what lets clause (1) of [Stacks Project, Tag 08U8] be stated for this situation purely
in terms of the lifts of `f`, with no reference to the deformation category of morphisms. -/
theorem nonempty_globalLiftsOverBase_iff_exists_schemeMorphismDeformation
    (xε : (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pX)).Fiber A)
    (yε : (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pY)).Fiber A) :
    Nonempty (globalLiftsOverBase f xε.1 yε.1 (eqToHom (yε.2.trans xε.2.symm))) ↔
      ∃ mε : (schemeMorphismDeformationCategoryProjection f pX pY hf).Fiber A,
        IsIsomorphic ((fiberFunctor (schemeMorphismSourceBased f pX pY hf) A).obj mε) xε ∧
          IsIsomorphic ((fiberFunctor (schemeMorphismTargetBased f pX pY hf) A).obj mε) yε :=
  ⟨fun ⟨ℓ⟩ => ⟨liftDeformationFiberObject f pX pY hf yε.2 ℓ,
      isIsomorphic_sourceFiber_liftDeformationFiberObject f pX pY hf hX xε.2 yε.2 ℓ,
      isIsomorphic_targetFiber_liftDeformationFiberObject f pX pY hf yε.2 ℓ⟩,
    fun ⟨mε, hsrc, htgt⟩ =>
      ⟨(exists_globalLift_of_isIsomorphic_endpoints f pX pY hf hM xε.2 yε.2 mε hsrc
        htgt).choose⟩⟩

end Lifts

/-! ### The obstruction arrow -/

section ObstructionArrow

variable
  (hM : IsDeformationCategory.{u, u, u}
    (schemeMorphismDeformationCategoryProjection f pX pY hf))
  (hX : IsDeformationCategory.{u, u, u}
    (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pX)))
  (hY : IsDeformationCategory.{u, u, u}
    (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pY)))
  (M : FGModuleCat.{u} k)
  (P : NaiveCotangentTwoTerm (DerivedCategory.singleFunctor
    (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) 0))
  (hP : P.obj = derivedPullbackNaiveCotangent f.toLRSHom.toShHom pY.toLRSHom.toShHom)
  (ξ : (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pX)).Fiber
        ((squareZeroExtensionArtinian.{u, u, u} Λ k).obj M) →
      (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pY)).Fiber
        ((squareZeroExtensionArtinian.{u, u, u} Λ k).obj M) →
      (P.conormal ⟶ schemeMorphismCoefficientSheaf f pY M))

/-- **Stacks 0E3V, the sixth arrow of the source's sequence.** The obstruction map

`ob : T(Def_X × Def_Y) ⟶ Ext¹_{𝒪_X}(Lf^*𝖭𝖫_{Y/k}, 𝒪_X ⊗_k M)`

of the last paragraph of the source's proof: a pair of classes of first-order deformations of
`X` and of `Y` goes to the `Ext¹` class of the Step 1 homomorphism `ξ` of
[Stacks Project, Tag 08U8] attached to a pair of representatives, which is
`AlgebraicGeometry.RingedSpaceThickening.liftingObstruction` at the two-term structure `P` of
`Lf^*𝖭𝖫_{Y/k}`.

The coefficients are `𝒪_X ⊗_k M`, the ideal sheaf of the special fibre of a deformation over
the square-zero base `k ⊕ M` over which the tangent spaces are taken; the source's sequence is
the case `M = k`, where that sheaf is canonically `𝒪_X`.

The representatives are supplied by `Deformation.tangentClassAt_surjective`.
`schemeMorphismObstructionArrow_apply` shows that, under the invariance the source's Step 1
asserts, the value does not depend on which ones are taken, so this is a descent along
`Deformation.tangentClassAt` and not a choice. -/
def schemeMorphismObstructionArrow :
    ↥(tangentModuleAt.{u, u, u} (BasedCategory.ofFunctor
        (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pX))) hX M) ×
      ↥(tangentModuleAt.{u, u, u} (BasedCategory.ofFunctor
        (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pY))) hY M) →
    schemeMorphismObstructionExtTwisted f pY M :=
  fun z => eqToHom hP.symm ≫ P.conormalExtClass (schemeMorphismCoefficientSheaf f pY M)
    (ξ (Function.surjInv (tangentClassAt_surjective.{u, u, u} (BasedCategory.ofFunctor
          (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pX))) hX M) z.1)
      (Function.surjInv (tangentClassAt_surjective.{u, u, u} (BasedCategory.ofFunctor
          (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pY))) hY M) z.2))

variable
  (hinv : ∀ (xε xε' : (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pX)).Fiber
        ((squareZeroExtensionArtinian.{u, u, u} Λ k).obj M))
      (yε yε' : (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pY)).Fiber
        ((squareZeroExtensionArtinian.{u, u, u} Λ k).obj M)),
    IsIsomorphic xε xε' → IsIsomorphic yε yε' →
      P.conormalExtClass (schemeMorphismCoefficientSheaf f pY M) (ξ xε yε) =
        P.conormalExtClass (schemeMorphismCoefficientSheaf f pY M) (ξ xε' yε'))

include hinv in
/-- **The sixth arrow of [Stacks Project, Tag 0E3V] is the class of the Step 1 homomorphism.**
At the pair of classes of two objects of the fibres, the value of
`Deformation.Examples.schemeMorphismObstructionArrow` is the `Ext¹` class of the Step 1
homomorphism of [Stacks Project, Tag 08U8] at *those* two objects, not at the representatives
the definition chooses.

This is what makes the arrow a construction: by `Deformation.tangentClassAt_surjective` every
element of the tangent module is a class, so the equation determines the arrow completely, and
by `Deformation.tangentClassAt_eq_iff` the invariance `hinv` of the class under isomorphism in
the fibres is exactly what is needed for the descent. -/
theorem schemeMorphismObstructionArrow_apply
    (xε : (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pX)).Fiber
      ((squareZeroExtensionArtinian.{u, u, u} Λ k).obj M))
    (yε : (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pY)).Fiber
      ((squareZeroExtensionArtinian.{u, u, u} Λ k).obj M)) :
    schemeMorphismObstructionArrow f pX pY hX hY M P hP ξ
        (tangentClassAt.{u, u, u} (BasedCategory.ofFunctor
            (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pX))) hX M xε,
          tangentClassAt.{u, u, u} (BasedCategory.ofFunctor
            (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pY))) hY M yε) =
      eqToHom hP.symm ≫
        P.conormalExtClass (schemeMorphismCoefficientSheaf f pY M) (ξ xε yε) := by
  refine congrArg (eqToHom hP.symm ≫ ·) (hinv _ xε _ yε ?_ ?_)
  · exact (tangentClassAt_eq_iff.{u, u, u} (BasedCategory.ofFunctor
      (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pX))) hX M _ xε).mp
      (Function.surjInv_eq _ _)
  · exact (tangentClassAt_eq_iff.{u, u, u} (BasedCategory.ofFunctor
      (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pY))) hY M _ yε).mp
      (Function.surjInv_eq _ _)

variable
  (hfactor : ∀ (xε : (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pX)).Fiber
        ((squareZeroExtensionArtinian.{u, u, u} Λ k).obj M))
      (yε : (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pY)).Fiber
        ((squareZeroExtensionArtinian.{u, u, u} Λ k).obj M)),
    (∃ θ : P.base ⟶ schemeMorphismCoefficientSheaf f pY M,
        P.d ≫ θ = ξ xε yε) ↔
      Nonempty (globalLiftsOverBase f xε.1 yε.1 (eqToHom (yε.2.trans xε.2.symm))))

include hM hinv hfactor in
/-- **The zero locus of the sixth arrow of [Stacks Project, Tag 0E3V] is the set of pairs of
first-order deformations along which `f` deforms.** This is the hypothesis `hob` of
`Deformation.Examples.exact_schemeMorphismTangentPair_obstruction`.

Three steps. The arrow is the class of `ξ`
(`Deformation.Examples.schemeMorphismObstructionArrow_apply`); that class vanishes exactly when
`ξ` factors through the degree `0` term
(`AlgebraicGeometry.RingedSpaceThickening.NaiveCotangentTwoTerm.conormalExtClass_eq_zero_iff`);
and `ξ` factors exactly when `f` lifts between the two total spaces (`hfactor`, clause (1) of
[Stacks Project, Tag 08U8]), which is exactly the source's "`f` deforms along the pair" by
`Deformation.Examples.nonempty_globalLiftsOverBase_iff_exists_schemeMorphismDeformation`. -/
theorem schemeMorphismObstructionArrow_eq_zero_iff
    (xε : (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pX)).Fiber
      ((squareZeroExtensionArtinian.{u, u, u} Λ k).obj M))
    (yε : (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pY)).Fiber
      ((squareZeroExtensionArtinian.{u, u, u} Λ k).obj M)) :
    schemeMorphismObstructionArrow f pX pY hX hY M P hP ξ
        (tangentClassAt.{u, u, u} (BasedCategory.ofFunctor
            (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pX))) hX M xε,
          tangentClassAt.{u, u, u} (BasedCategory.ofFunctor
            (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pY))) hY M yε) = 0 ↔
      ∃ mε : (schemeMorphismDeformationCategoryProjection f pX pY hf).Fiber
          ((squareZeroExtensionArtinian.{u, u, u} Λ k).obj M),
        IsIsomorphic ((fiberFunctor (schemeMorphismSourceBased f pX pY hf)
            ((squareZeroExtensionArtinian.{u, u, u} Λ k).obj M)).obj mε) xε ∧
          IsIsomorphic ((fiberFunctor (schemeMorphismTargetBased f pX pY hf)
            ((squareZeroExtensionArtinian.{u, u, u} Λ k).obj M)).obj mε) yε := by
  rw [schemeMorphismObstructionArrow_apply f pX pY hX hY M P hP ξ hinv xε yε,
    ← cancel_epi (eqToHom hP), eqToHom_trans_assoc, eqToHom_refl, Category.id_comp, comp_zero]
  exact ((P.conormalExtClass_eq_zero_iff _ (ξ xε yε)).trans (hfactor xε yε)).trans
    (nonempty_globalLiftsOverBase_iff_exists_schemeMorphismDeformation f pX pY hf hM hX xε yε)

include hM hinv hfactor in
/-- **[Stacks Project, Tag 0E3V], exactness at the fifth spot of the source's sequence, with the
obstruction arrow constructed.** The sequence

`T Def_{X ⟶ Y} → T(Def_X × Def_Y) → Ext¹_{𝒪_X}(Lf^*𝖭𝖫_{Y/k}, 𝒪_X ⊗_k M)`

is exact at its middle term, the third map being
`Deformation.Examples.schemeMorphismObstructionArrow` — the `Ext¹` class of the Step 1
homomorphism of [Stacks Project, Tag 08U8] — and not a hypothesis. This is
`Deformation.Examples.exact_schemeMorphismTangentPair_obstruction` with its `ob` instantiated
and its `hob` discharged by
`Deformation.Examples.schemeMorphismObstructionArrow_eq_zero_iff`.

The coefficients of both the Step 1 homomorphism `ξ` and the `Ext¹` group are `𝒪_X ⊗_k M`, the
ideal sheaf of the special fibre over the square-zero base `k ⊕ M` of the tangent spaces; the
source's sequence is the case `M = k`. -/
theorem exact_schemeMorphismTangentPair_schemeMorphismObstructionArrow :
    Function.Exact (schemeMorphismTangentPair f pX pY hf hM hX hY M)
      (schemeMorphismObstructionArrow f pX pY hX hY M P hP ξ) :=
  exact_schemeMorphismTangentPair_obstruction f pX pY hf hM hX hY M
    (schemeMorphismObstructionArrow f pX pY hX hY M P hP ξ)
    (schemeMorphismObstructionArrow_eq_zero_iff f pX pY hf hM hX hY M P hP ξ hinv hfactor)

end ObstructionArrow

/-! ### The arrow at the two-term structure of `Lf^*𝖭𝖫_{Y/k}` -/

section DerivedPullback

variable
  (hM : IsDeformationCategory.{u, u, u}
    (schemeMorphismDeformationCategoryProjection f pX pY hf))
  (hX : IsDeformationCategory.{u, u, u}
    (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pX)))
  (hY : IsDeformationCategory.{u, u, u}
    (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pY)))
  (M : FGModuleCat.{u} k)
  (hkf : Stacks.Cohomology.KFlatDerivedPullback.KFlatComplex Y.toRingedSpace
    (RingedSpace.naiveCotangentComplex pY.toLRSHom.toShHom))
  (ξ : (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pX)).Fiber
        ((squareZeroExtensionArtinian.{u, u, u} Λ k).obj M) →
      (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pY)).Fiber
        ((squareZeroExtensionArtinian.{u, u, u} Λ k).obj M) →
      ((derivedPullbackNaiveCotangentTwoTerm
            f.toLRSHom.toShHom pY.toLRSHom.toShHom hkf).conormal ⟶
        schemeMorphismCoefficientSheaf f pY M))
  (hinvd : ∀ (xε xε' : (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pX)).Fiber
        ((squareZeroExtensionArtinian.{u, u, u} Λ k).obj M))
      (yε yε' : (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pY)).Fiber
        ((squareZeroExtensionArtinian.{u, u, u} Λ k).obj M)),
    IsIsomorphic xε xε' → IsIsomorphic yε yε' →
      (derivedPullbackNaiveCotangentTwoTerm
            f.toLRSHom.toShHom pY.toLRSHom.toShHom hkf).conormalExtClass
          (schemeMorphismCoefficientSheaf f pY M) (ξ xε yε) =
        (derivedPullbackNaiveCotangentTwoTerm
              f.toLRSHom.toShHom pY.toLRSHom.toShHom hkf).conormalExtClass
          (schemeMorphismCoefficientSheaf f pY M) (ξ xε' yε'))
  (hfactord : ∀ (xε : (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pX)).Fiber
        ((squareZeroExtensionArtinian.{u, u, u} Λ k).obj M))
      (yε : (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pY)).Fiber
        ((squareZeroExtensionArtinian.{u, u, u} Λ k).obj M)),
    (∃ θ : (derivedPullbackNaiveCotangentTwoTerm
          f.toLRSHom.toShHom pY.toLRSHom.toShHom hkf).base ⟶
          schemeMorphismCoefficientSheaf f pY M,
        pulledConormalMap f.toLRSHom.toShHom pY.toLRSHom.toShHom ≫ θ = ξ xε yε) ↔
      Nonempty (globalLiftsOverBase f xε.1 yε.1 (eqToHom (yε.2.trans xε.2.symm))))

include hM hinvd hfactord in
/-- **[Stacks Project, Tag 0E3V], exactness at the fifth spot with the obstruction arrow
constructed at the source's own two-term complex.** The instance of
`Deformation.Examples.exact_schemeMorphismTangentPair_schemeMorphismObstructionArrow` at
`P = AlgebraicGeometry.RingedSpaceThickening.derivedPullbackNaiveCotangentTwoTerm`, the two-term
structure of `Lf^*𝖭𝖫_{Y/k}` itself, where `hP` is `rfl` by
`derivedPullbackNaiveCotangentTwoTerm_obj`. The two-term structure and its identification with
the sixth term's complex are no longer carried; what buys that is the K-flatness of
`𝖭𝖫_{Y/k}`, which is `hkf` and which
`AlgebraicGeometry.RingedSpaceThickening.kFlatComplex_naiveCotangentComplex_of_hasTorAmplitude`
supplies from Tor amplitude in `[-1, 0]`.

At this instance the Step 1 homomorphism `ξ` is the source's own: the differential of `P` is
`AlgebraicGeometry.RingedSpaceThickening.pulledConormalMap f pY` by
`derivedPullbackNaiveCotangentTwoTerm_d`, so `ξ` is a homomorphism
`f^*(𝒥/𝒥²) ⟶ 𝒪_X ⊗_k M` out of the
pullback of the conormal module of the canonical presentation of `𝒪_Y` over the residue field,
and `hfactor` says it factors through `f^*Ω_{Y/k}` exactly when `f` lifts between the two total
spaces.

The coefficients `𝒪_X ⊗_k M` are the ideal sheaf of the special fibre over the square-zero base
`k ⊕ M` of the tangent spaces; the source's sequence is the case `M = k`. -/
theorem exact_schemeMorphismTangentPair_obstructionArrow_derivedPullback :
    Function.Exact (schemeMorphismTangentPair f pX pY hf hM hX hY M)
      (schemeMorphismObstructionArrow f pX pY hX hY M
        (derivedPullbackNaiveCotangentTwoTerm f.toLRSHom.toShHom pY.toLRSHom.toShHom hkf)
        (derivedPullbackNaiveCotangentTwoTerm_obj
          f.toLRSHom.toShHom pY.toLRSHom.toShHom hkf) ξ) :=
  exact_schemeMorphismTangentPair_schemeMorphismObstructionArrow f pX pY hf hM hX hY M _ _ ξ
    hinvd hfactord

end DerivedPullback

end Deformation.Examples

end
