module

public import StacksFrontier.AlgebraicGeometry.Chow.LocalizedChern.BabyCaseLemmas
public import StacksFrontier.AlgebraicGeometry.Chow.LocalizedChern.SupportedIntersectionProduct
public import StacksFrontier.AlgebraicGeometry.Chow.LocalizedChern.BabyCaseWhitney
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.PerfectPowerSum
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.DerivedTensor
public import StacksFrontier.AlgebraicGeometry.Perfect.DerivedNakayama
public import StacksFrontier.AlgebraicGeometry.Properties.ReducedClosedSubscheme
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.TensorProduct
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.PerfectDerivedPullback

/-!
# The classes of Stacks 0F9H of a derived tensor product

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `X` be locally of
finite type over `S`, and let `X = X₁ ∪ X₂ = X₁' ∪ X₂'` be two ways of writing `X` as a
set-theoretic union of closed subschemes. Let `E`, `E' ∈ D(𝒪_X)` be perfect objects whose Chern
classes are defined, with `E|_{X₁}` and `E'|_{X₁'}` zero. Stacks 0F9H provides the classes

  `r = P'_0(E|_{X₂})`, `γ_p = c'_p(E|_{X₂})`, `χ_p = P'_p(E|_{X₂})` in `A^*(X₂ ⟶ X)`

and their analogues `r'`, `γ'_p`, `χ'_p` in `A^*(X₂' ⟶ X)`. Writing `W = X₂ ∩ X₂'`, the object
`E ⊗^L E'` restricts to zero on `Y = (X₁ ∩ X₁') ∪ (X₁ ∩ X₂') ∪ (X₂ ∩ X₁')`, and `X = Y ∪ W`, so
Stacks 0F9H also provides the classes of `(E ⊗^L E')|_W` in `A^*(W ⟶ X)`. Stacks 0FE5 computes
them:

  `c'_1((E ⊗^L E')|_W) = r γ'_1 + r' γ_1`,

  `c'_2((E ⊗^L E')|_W) = r γ'_2 + r' γ_2 + C(r, 2) (γ'_1)² + (r r' - 1) γ'_1 γ_1 + C(r', 2) γ_1²`,

  `P'_p((E ⊗^L E')|_W) = ∑_{p₁ + p₂ = p} C(p, p₁) χ_{p₁} χ'_{p₂}`.

The source says that this "follows from the characterization of Lemma 0F9H and the equalities of
Lemma 0FAG". The details are as follows. The product of `c₁ ∈ A^p(X₂ ⟶ X)` and
`c₂ ∈ A^q(X₂' ⟶ X)` is the bivariant product `res(c₁) ∘ c₂ ∈ A^{p+q}(W ⟶ X)`
(`Stacks.Chow.supportedIntersectionMul`): on a test scheme it caps with `c₂` and then with `c₁`.
If `c₁` and `c₂` extend `a ∈ A^p(X₂)` and `b ∈ A^q(X₂')` along the two covers, then `c₁ c₂` caps
the classes coming from `W` as `a|_W b|_W` does, and kills the classes coming from schemes over
`X₁` or over `X₁'` (`Stacks.Chow.IsClosedCoverExtension.supportedIntersectionMul`). Hence each
right-hand side satisfies the characterization of Stacks 0F9H, along `X = Y ∪ W` for every closed
subscheme `Y` with underlying set in `X₁ ∪ X₁'`, of the extension of a class of `A^*(W)`; by Stacks
0FAG restricted to `W` that class is the corresponding class of `(E ⊗^L E')|_W`, and uniqueness in
Stacks 0F9H concludes. That the left-hand sides are defined, i.e. that `E ⊗^L E'` restricts to zero
on `Y ∩ W`, is checked on derived fibres: at a point of `Y ∩ W` the derived fibre of `E ⊗^L E'` is
the tensor product of those of `E` and `E'`, one of which vanishes, and a perfect object with
vanishing derived fibres is zero (derived Nakayama,
`AlgebraicGeometry.isZero_of_forall_isZero_derivedPullback_fromSpecResidueField`).

## Main definitions

* `Stacks.Chow.closedCoverRankChoose` — the class `C(r, n) ∈ A^0(X₂ ⟶ X)`.
* `Stacks.Chow.reducedUnionIdeal` — the reduced closed subscheme on `X₁ ∪ X₁'`.
* `Stacks.Chow.closedCoverPowerSumRestrict`, `Stacks.Chow.closedCoverChernClassRestrict` — the
  classes `P'_p(E|_{X₂})` and `c'_p(E|_{X₂})` of Stacks 0F9H for `E ∈ D(𝒪_X)` zero on `X₁`.

## Main results

* `Stacks.Chow.closedCoverPowerSum_derivedTensor`,
  `Stacks.Chow.closedCoverChernClass_derivedTensor_one`,
  `Stacks.Chow.closedCoverChernClass_derivedTensor_two` — **Stacks 0FE5**, along the closed cover
  `X = Y ∪ W` with `Y` the reduced closed subscheme on `X₁ ∪ X₁'`.
* `Stacks.Chow.closedCoverPowerSum_derivedTensor_of_closedCover` and its analogues — the same
  along every closed cover `X = Y ∪ W` on which `(E ⊗^L E')|_W` restricts to zero on `Y ∩ W`.
* `Stacks.Chow.isClosedCoverExtension_derivedTensor_powerSum`,
  `Stacks.Chow.isClosedCoverExtension_derivedTensor_chernClass_one`,
  `Stacks.Chow.isClosedCoverExtension_derivedTensor_chernClass_two` — the right-hand sides satisfy
  the characterization of Stacks 0F9H along every closed `Y` with underlying set in `X₁ ∪ X₁'`.
* `Stacks.Chow.isZero_derivedPullback_derivedTensor_of_range_subset` — `E ⊗^L E'` restricts to
  zero along every morphism with image in `X₁ ∪ X₁'`.
* `Stacks.Chow.closedCoverExtension_eq_of_isClosedCoverExtension` — Stacks 0FAH, in the form used.
* `Stacks.Chow.isHomogeneous_perfectPowerSum` — `P_p(E)` is homogeneous of degree `p`.
* `Stacks.Chow.perfectChernClass_two_derivedPullback_derivedTensor` — Stacks 0FAG for `c₂`,
  restricted to `W` and written in components.

## Implementation notes

`X₂ ∩ X₂'` is the fibre product `X₂ ×_X X₂'`, mapping to `X` through `X₂'`. The source writes the
products of a class supported on `X₂` and a class supported on `X₂'` by juxtaposition, in both
orders, all landing in `A^*(X₂ ∩ X₂' ⟶ X)`; `Stacks.Chow.supportedIntersectionMul` is therefore
defined for any pullback square presenting `W`, and is applied to the square and to its flip.
Products of two classes with the same support are the third multiplication of Stacks 0FA0
(`Stacks.Chow.supportedMul`).

The classes on the left-hand sides are those of Stacks 0F9H along a closed cover `X = Y ∪ W`, which
are defined when `(E ⊗^L E')|_W` restricts to zero on `Y ∩ W`. The source takes
`Y = (X₁ ∩ X₁') ∪ (X₁ ∩ X₂') ∪ (X₂ ∩ X₁')`, a union of closed subschemes whose scheme structure
it leaves implicit; its underlying set is `X₁ ∪ X₁'`. The main theorems take for `Y` the reduced
closed subscheme on `X₁ ∪ X₁'` (`Stacks.Chow.reducedUnionIdeal`); by Stacks 0FAH any other
admissible choice gives the same classes, and the `_of_closedCover` forms are stated for every
admissible `Y`.

The rank `r(E) = P_0(E)` is the class of the locally constant function `x ↦ χ_E(x)`, the Euler
characteristic of the derived fibre (`Stacks.Chow.perfectPowerSum_zero_eq_ofLocallyConstant`), and
Stacks 0FAG reads `C(r(E), 2)` as the class of `x ↦ C(χ_E(x), 2)`. Accordingly `C(r, 2)` is the
extension along the closed cover of the restriction to `X₂` of that class, which vanishes on `X₁`
since `χ_E` does; `C(r, 1) = r`
(`Stacks.Chow.closedCoverPowerSum_zero_eq_closedCoverRankChoose_one`). The term
`(r r' - 1) γ'_1 γ_1` is read as `(r r') (γ'_1 γ_1) - γ'_1 γ_1`: there is no unit among the classes
supported on `W`.

Perfectness of `E` and `E'`, assumed by the source, is used to show that `E ⊗^L E'` restricts to
zero on `Y ∩ W` (derived Nakayama), and in the formula for `c'_2` to make sense of `C(r, 2)`, as in
Stacks 0FAG. The characterization forms and the `_of_closedCover` forms for `P'_p` and `c'_1` only
use that the Chern classes are defined. The source's "and so on for higher Chern classes" is not a
precise assertion and is not formalized.

## References

* [Stacks Project, Tag 0FE5](https://stacks.math.columbia.edu/tag/0FE5)
* [Stacks Project, Tag 0F9H](https://stacks.math.columbia.edu/tag/0F9H)
* [Stacks Project, Tag 0FAH](https://stacks.math.columbia.edu/tag/0FAH)
* [Stacks Project, Tag 0FAG](https://stacks.math.columbia.edu/tag/0FAG)
* [Stacks Project, Tag 0FA0](https://stacks.math.columbia.edu/tag/0FA0)
* [Stacks Project, Tag 0F9Z](https://stacks.math.columbia.edu/tag/0F9Z)
* [Stacks Project, Tag 0B75](https://stacks.math.columbia.edu/tag/0B75)
* [Stacks Project, Tag 0F94](https://stacks.math.columbia.edu/tag/0F94)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

attribute [local instance 10000] HasDerivedCategory.standard


/-! ### Objects restricting to zero -/

section Zero

/-- **Restriction to zero along a commutative square.** If `a ≫ i = b ≫ j` and the restriction
`E|_Z` of `E` along `i : Z ⟶ X` is zero, then so is the restriction `(E|_Y)|_V` along
`j : Y ⟶ X` and then `b : V ⟶ Y`. -/
theorem isZero_derivedPullback_of_isZero_of_comp_eq {V X Y Z : Scheme.{u}} {i : Z ⟶ X} {j : Y ⟶ X}
    {a : V ⟶ Z} {b : V ⟶ Y} (h : a ≫ i = b ≫ j) {E : DerivedCategory X.Modules}
    (hzero : IsZero ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
      i.toLRSHom.toShHom).obj E)) :
    IsZero ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback b.toLRSHom.toShHom).obj
      ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
        j.toLRSHom.toShHom).obj E)) := by
  have hsq : b.toLRSHom.toShHom ≫ j.toLRSHom.toShHom =
      a.toLRSHom.toShHom ≫ i.toLRSHom.toShHom :=
    congrArg (fun f => f.toLRSHom.toShHom) h.symm
  refine IsZero.of_iso ?_ ((Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical
      b.toLRSHom.toShHom j.toLRSHom.toShHom).app E ≪≫
    (eqToIso (Cohomology.DerivedPullbackAlongIso.derivedPullback_eq_of_eq hsq)).app E ≪≫
    ((Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical
      a.toLRSHom.toShHom i.toLRSHom.toShHom).app E).symm)
  exact Functor.map_isZero
    (Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback a.toLRSHom.toShHom) hzero

/-- The derived pullbacks along two composable morphisms of schemes compose. -/
def derivedPullbackCompIsoOfScheme {T Y X : Scheme.{u}} (a : T ⟶ Y) (b : Y ⟶ X)
    (E : DerivedCategory X.Modules) :
    (Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback a.toLRSHom.toShHom).obj
        ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback b.toLRSHom.toShHom).obj E) ≅
      (Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback (a ≫ b).toLRSHom.toShHom).obj
        E :=
  (Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical
      a.toLRSHom.toShHom b.toLRSHom.toShHom).app E ≪≫
    (eqToIso (Cohomology.DerivedPullbackAlongIso.derivedPullback_eq_of_eq
      (by simp only [Scheme.Hom.comp_toLRSHom, LocallyRingedSpace.comp_toShHom]))).app E

/-- **Restriction to zero along a factorization.** If `t = a ≫ i` and `E|_Z` is zero along `i`,
then the derived pullback of `E` along `t` is zero. -/
theorem isZero_derivedPullback_of_fac {T X Z : Scheme.{u}} {i : Z ⟶ X} {a : T ⟶ Z}
    {t : T ⟶ X} (h : a ≫ i = t) {E : DerivedCategory X.Modules}
    (hzero : IsZero ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
      i.toLRSHom.toShHom).obj E)) :
    IsZero ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
      t.toLRSHom.toShHom).obj E) := by
  subst h
  exact (Functor.map_isZero
    (Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback a.toLRSHom.toShHom) hzero).of_iso
    (derivedPullbackCompIsoOfScheme a i E).symm

/-- **Restriction to zero over a reduced scheme.** If `E|_Z` is zero along the closed immersion
`i : Z ⟶ X`, then the derived pullback of `E` along every morphism `t : T ⟶ X` from a reduced
scheme with image in `Z` is zero: such a morphism factors through `i`. -/
theorem isZero_derivedPullback_of_range_subset {T X Z : Scheme.{u}} [IsReduced T] (i : Z ⟶ X)
    [IsClosedImmersion i] (t : T ⟶ X) (ht : Set.range t ⊆ Set.range i)
    {E : DerivedCategory X.Modules}
    (hzero : IsZero ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
      i.toLRSHom.toShHom).obj E)) :
    IsZero ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
      t.toLRSHom.toShHom).obj E) := by
  obtain ⟨g, hg⟩ := (Scheme.IdealSheafData.exists_lift_subschemeι_iff_range_subset_support
    i.ker t).2 (by rw [Scheme.Hom.support_ker]; exact ht.trans subset_closure)
  refine isZero_derivedPullback_of_fac (a := g ≫ inv i.toImage) ?_ hzero
  rw [Category.assoc, inv_toImage_comp, hg]

open Stacks.DerivedTensor.RingedSite (derivedTensorProductFunctor canonicalDerivedTensorProduct)
  in
/-- The derived tensor product with a zero object on the left is zero. -/
theorem isZero_derivedTensor_of_isZero_left {T : Scheme.{u}} {A : DerivedCategory T.Modules}
    (hA : IsZero A) (B : DerivedCategory T.Modules) :
    IsZero (((derivedTensorProductFunctor T.sheaf).obj A).obj B) := by
  let := (canonicalDerivedTensorProduct T.sheaf).commShift_left B
  have := (canonicalDerivedTensorProduct T.sheaf).exact_left B
  exact ((derivedTensorProductFunctor T.sheaf).flip.obj B).map_isZero hA

open Stacks.DerivedTensor.RingedSite (derivedTensorProductFunctor canonicalDerivedTensorProduct)
  in
/-- The derived tensor product with a zero object on the right is zero. -/
theorem isZero_derivedTensor_of_isZero_right {T : Scheme.{u}} (A : DerivedCategory T.Modules)
    {B : DerivedCategory T.Modules} (hB : IsZero B) :
    IsZero (((derivedTensorProductFunctor T.sheaf).obj A).obj B) := by
  let := (canonicalDerivedTensorProduct T.sheaf).commShift_right A
  have := (canonicalDerivedTensorProduct T.sheaf).exact_right A
  exact ((derivedTensorProductFunctor T.sheaf).obj A).map_isZero hB

open Stacks.DerivedTensor.RingedSite (derivedTensorProductFunctor canonicalDerivedTensorProduct)
  in
/-- **A derived tensor product of objects vanishing on a closed cover of the image vanishes.**
Let `E`, `E'` be perfect objects of `D(𝒪_X)` restricting to zero on closed subschemes `X₁` and
`X₁'`. Then `E ⊗^L E'` restricts to zero along every morphism `t : V ⟶ X` whose image lies in
`X₁ ∪ X₁'`: its derived fibre at a point `v` is the tensor product of the derived fibres of `E` and
`E'` at `t v`, one of which vanishes, and a perfect object with vanishing derived fibres is zero
(`AlgebraicGeometry.isZero_of_forall_isZero_derivedPullback_fromSpecResidueField`). -/
theorem isZero_derivedPullback_derivedTensor_of_range_subset {V X X₁ X₁' : Scheme.{u}}
    (i₁ : X₁ ⟶ X) (j₁ : X₁' ⟶ X) [IsClosedImmersion i₁] [IsClosedImmersion j₁]
    {E E' : DerivedCategory X.Modules} (perfectE : RingedSpace.IsPerfect.{u, u + 1} E)
    (perfectE' : RingedSpace.IsPerfect.{u, u + 1} E')
    (hzero : IsZero ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
      i₁.toLRSHom.toShHom).obj E))
    (hzero' : IsZero ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
      j₁.toLRSHom.toShHom).obj E'))
    (t : V ⟶ X) (ht : Set.range t ⊆ Set.range i₁ ∪ Set.range j₁) :
    IsZero ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback t.toLRSHom.toShHom).obj
      (((derivedTensorProductFunctor X.sheaf).obj E).obj E')) := by
  have hT : RingedSpace.IsPerfect.{u, u + 1}
      (((derivedTensorProductFunctor X.sheaf).obj E).obj E') :=
    RingedSpace.isPerfect_canonicalDerivedTensorProduct X.toRingedSpace E E' perfectE perfectE'
  refine isZero_of_forall_isZero_derivedPullback_fromSpecResidueField _
    (RingedSpace.KFlatDerivedPullback.isPerfect_derivedPullback t.toLRSHom.toShHom _ hT)
    fun v ↦ ?_
  set φ := V.fromSpecResidueField v ≫ t
  refine IsZero.of_iso ?_ (derivedPullbackCompIsoOfScheme (V.fromSpecResidueField v) t _ ≪≫
    derivedPullbackDerivedTensorIso φ E E')
  have hφ : Set.range φ ⊆ {t v} := by
    rintro _ ⟨w, rfl⟩
    simp [φ]
  rcases ht ⟨v, rfl⟩ with h | h
  · exact isZero_derivedTensor_of_isZero_left
      (isZero_derivedPullback_of_range_subset i₁ φ (hφ.trans (Set.singleton_subset_iff.2 h))
        hzero) _
  · exact isZero_derivedTensor_of_isZero_right _
      (isZero_derivedPullback_of_range_subset j₁ φ (hφ.trans (Set.singleton_subset_iff.2 h))
        hzero')

end Zero

/-! ### Homogeneity of the power sums and of the classes of locally constant functions -/

namespace TotalChowClass

variable {C : ChowSituation.{u}} {X Y : Scheme.{u}} {sX : X ⟶ C.S} [LocallyOfFiniteType sX]
  {sY : Y ⟶ C.S} [LocallyOfFiniteType sY]

/-- Restriction preserves homogeneity. -/
theorem IsHomogeneous.res {i : ℕ} {c : TotalChowClass C sX} (hc : IsHomogeneous i c) (h : Y ⟶ X)
    [LocallyOfFiniteType h] (hs : h ≫ sX = sY) : IsHomogeneous i (res h hs c) := by
  subst hs
  intro p hp
  rw [res_rfl_apply, hc p hp, map_zero]

/-- Homogeneity can be checked after an injective restriction. -/
theorem isHomogeneous_of_res {i : ℕ} {c : TotalChowClass C sX} (h : Y ⟶ X)
    [LocallyOfFiniteType h] (hs : h ≫ sX = sY) (hinj : Function.Injective (res (C := C) h hs))
    (hc : IsHomogeneous i (res h hs c)) : IsHomogeneous i c := by
  have e : TotalChowClass.homComponent i c = c :=
    hinj (by rw [TotalChowClass.res_homComponent, hc.homComponent_self])
  rw [← e]
  exact TotalChowClass.isHomogeneous_homComponent i c

/-- Integers are homogeneous of degree `0`. -/
theorem isHomogeneous_intCast (k : ℤ) : IsHomogeneous 0 (k : TotalChowClass C sX) := by
  simpa using isHomogeneous_intCast_mul (isHomogeneous_one (C := C) (sX := sX)) k

variable (C sX) in
/-- **The class of a locally constant function is homogeneous of degree `0`.** -/
theorem isHomogeneous_ofLocallyConstant (n : LocallyConstant X ℤ) :
    IsHomogeneous 0 (ofLocallyConstant C sX n) := by
  have e : TotalChowClass.homComponent 0 (ofLocallyConstant C sX n) = ofLocallyConstant C sX n := by
    refine eq_of_res_eq (isClopenDecomposition_levelSets n) fun k ↦ ?_
    rw [TotalChowClass.res_homComponent,
      res_ofLocallyConstant (levelSets n k).ι rfl n k.down fun y ↦ mem_levelSets.1 y.2,
      (isHomogeneous_intCast _).homComponent_self]
  rw [← e]
  exact TotalChowClass.isHomogeneous_homComponent 0 _

end TotalChowClass

open TotalChowClass in
/-- **The power sum `P_p(ℰ^•)` of a complex of constant ranks is homogeneous of degree `p`.** -/
theorem isHomogeneous_powerSumComplexBounded (C : ChowSituation.{u}) {Y : Scheme.{u}}
    (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (P : CochainComplex Y.Modules ℤ) (ρ : ℤ →₀ ℕ)
    (hP : ∀ n, AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (P.X n) (ρ n))
    (p : ℕ) : IsHomogeneous p (powerSumComplexBounded C sY P ρ hP p) :=
  IsHomogeneous.sum fun n _ ↦
    (let := hP n; isHomogeneous_powerSumTotal C sY (P.X n) (ρ n) p).zsmul _

open TotalChowClass in
/-- **The power sum `P_p(ℰ^•)` of a locally bounded complex is homogeneous of degree `p`**: it is
on each rank locus. -/
theorem isHomogeneous_powerSumComplex (C : ChowSituation.{u}) {Y : Scheme.{u}}
    (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] {P : CochainComplex Y.Modules ℤ}
    (hP : IsLocallyBoundedFiniteLocallyFree P) (p : ℕ) :
    IsHomogeneous p (powerSumComplex C sY hP p) := by
  have e : TotalChowClass.homComponent p (powerSumComplex C sY hP p)
      = powerSumComplex C sY hP p := by
    refine eq_of_res_eq (isClopenDecomposition_complexRankLoci hP) fun ρ ↦ ?_
    rw [TotalChowClass.res_homComponent, res_powerSumComplex_complexRankLocus,
      (isHomogeneous_powerSumComplexBounded C _ _ _ _ p).homComponent_self]
  rw [← e]
  exact TotalChowClass.isHomogeneous_homComponent p _

open TotalChowClass in
/-- **The power sum `P_p(E)` is homogeneous of degree `p`**: it is after restriction along the
envelope of a presentation, where it is the power sum of the presenting complex. -/
theorem isHomogeneous_perfectPowerSum (C : ChowSituation.{u}) {X : Scheme.{u}} (sX : X ⟶ C.S)
    [LocallyOfFiniteType sX] {E : DerivedCategory X.Modules} (hE : HasDefinedChernClasses E)
    (p : ℕ) : IsHomogeneous p (perfectPowerSum C sX hE p) := by
  refine isHomogeneous_of_res hE.some.f rfl
    (res_injective_of_isEnvelope hE.some.f hE.some.envelope rfl) ?_
  rw [res_perfectPowerSum_eq_powerSumComplex C sX hE hE.some p]
  exact isHomogeneous_powerSumComplex C _ _ p

/-- **A component of a product with a homogeneous class.** If `A` is homogeneous of degree `i` and
`i + j = m`, the component of degree `m` of `A B` is `A_i B_j`, read in degree `m`. -/
theorem TotalChowClass.IsHomogeneous.mul_apply {C : ChowSituation.{u}} {Y : Scheme.{u}}
    {sY : Y ⟶ C.S} [LocallyOfFiniteType sY] {i j m : ℕ} {A : TotalChowClass C sY}
    (hA : IsHomogeneous i A) (B : TotalChowClass C sY) (h : i + j = m) :
    (A * B) m = bivariantClassDegreeCongr C _ sY sY (𝟙 Y) (Category.id_comp sY)
      (by rw [← h]; push_cast; rfl) ((A i).mulId C sY (B j)) := by
  conv_lhs => rw [← hA.homComponent_self]
  exact TotalChowClass.homPart_mul_apply C sY A B h

/-- The components of an integer multiple of a total class. -/
theorem TotalChowClass.zsmul_apply {C : ChowSituation.{u}} {Y : Scheme.{u}} {sY : Y ⟶ C.S}
    [LocallyOfFiniteType sY] (n : ℤ) (c : TotalChowClass C sY) (p : ℕ) : (n • c) p = n • c p :=
  rfl

/-- The component of degree `i` of the restriction of the homogeneous part of degree `i` is the
component of degree `i` of the restriction. -/
theorem TotalChowClass.res_homPart_apply_self {C : ChowSituation.{u}} {X Y : Scheme.{u}}
    {sX : X ⟶ C.S} [LocallyOfFiniteType sX] {sY : Y ⟶ C.S} [LocallyOfFiniteType sY] (h : Y ⟶ X)
    [LocallyOfFiniteType h] (hs : h ≫ sX = sY) (i : ℕ) (c : TotalChowClass C sX) :
    TotalChowClass.res h hs (TotalChowClass.homComponent i c) i = TotalChowClass.res h hs c i := by
  rw [TotalChowClass.res_homComponent, TotalChowClass.homComponent_apply, ite_eq_left rfl]

/-- **Restriction along a factorization.** If `w ≫ f = h`, then the component of degree `p` of
the restriction of a total class `A` along `h` is the restriction along `w` of the component of
degree `p` of its restriction along `f`. -/
theorem TotalChowClass.isRestriction_res_res {C : ChowSituation.{u}} {X Z W : Scheme.{u}}
    {sX : X ⟶ C.S} [LocallyOfFiniteType sX] (A : TotalChowClass C sX) (f : Z ⟶ X)
    [LocallyOfFiniteType f] (w : W ⟶ Z) [LocallyOfFiniteType w] (h : W ⟶ X)
    [LocallyOfFiniteType h] (hw : w ≫ f = h) (p : ℕ) :
    BivariantClass.IsRestriction (TotalChowClass.res h rfl A p) (TotalChowClass.res f rfl A p) w
    := by
  have e : TotalChowClass.res h rfl A =
      TotalChowClass.res w (by rw [← hw, Category.assoc]) (TotalChowClass.res f rfl A) := by
    rw [TotalChowClass.res_res]
    exact TotalChowClass.res_congr hw.symm _ _ _
  rw [e]
  exact TotalChowClass.isRestriction_res _ w _ p

/-- The product of Chow cohomology classes commutes with transport of the right factor along an
equality of degrees. -/
theorem BivariantClass.mulId_bivariantClassDegreeCongr_right {C : ChowSituation.{u}}
    {Y : Scheme.{u}} {sY : Y ⟶ C.S} [LocallyOfFiniteType sY] {a b b' : ℤ} (hb : b = b')
    (x : chowCohomologyComponent C (gysinSystemOfInvertible C) sY a)
    (y : chowCohomologyComponent C (gysinSystemOfInvertible C) sY b) :
    x.mulId C sY (bivariantClassDegreeCongr C _ sY sY (𝟙 Y) (Category.id_comp sY) hb y) =
      bivariantClassDegreeCongr C _ sY sY (𝟙 Y) (Category.id_comp sY) (by rw [hb])
        (x.mulId C sY y) := by
  subst hb
  rfl

/-- The product of Chow cohomology classes commutes with transport of the left factor along an
equality of degrees. -/
theorem BivariantClass.mulId_bivariantClassDegreeCongr_left {C : ChowSituation.{u}}
    {Y : Scheme.{u}} {sY : Y ⟶ C.S} [LocallyOfFiniteType sY] {a a' b : ℤ} (ha : a = a')
    (x : chowCohomologyComponent C (gysinSystemOfInvertible C) sY a)
    (y : chowCohomologyComponent C (gysinSystemOfInvertible C) sY b) :
    (bivariantClassDegreeCongr C _ sY sY (𝟙 Y) (Category.id_comp sY) ha x).mulId C sY y =
      bivariantClassDegreeCongr C _ sY sY (𝟙 Y) (Category.id_comp sY) (by rw [ha])
        (x.mulId C sY y) := by
  subst ha
  rfl

/-! ### The class `C(r, n)` -/

section RankChoose

variable (C : ChowSituation.{u}) {X X₁ X₂ : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (i₁ : X₁ ⟶ X) (i₂ : X₂ ⟶ X) [IsClosedImmersion i₁] [IsClosedImmersion i₂]
  {E : DerivedCategory X.Modules} (perfect : RingedSpace.IsPerfect.{u, u + 1} E)

/-- The rank of a perfect object vanishes at the points over which the object restricts to
zero. -/
theorem perfectRank_eq_zero_of_isZero {Z : Scheme.{u}} (i : Z ⟶ X)
    (hzero : IsZero ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
      i.toLRSHom.toShHom).obj E)) (z : Z) :
    perfectRank E perfect (i.base z) = 0 := by
  have h := congrFun (DerivedFibreBetti.chiDerivedFibre_derivedPullback i E
    (DerivedFibreBetti.isPseudoCoherent_of_isPerfect E perfect)) z
  rw [Function.comp_apply] at h
  rw [perfectRank_apply, ← h]
  exact chiDerivedFibre_eq_zero_of_isZero hzero _ z

variable {i₁} in
/-- The class of a locally constant function vanishing on `X₁`, restricted to `X₂`, vanishes over
`X₁ ×_X X₂`. -/
theorem vanishesOver_res_ofLocallyConstant (n : LocallyConstant X ℤ)
    (hn : ∀ y : X₁, n (i₁.base y) = 0) :
    BivariantClass.VanishesOver (TotalChowClass.res i₂ rfl (TotalChowClass.ofLocallyConstant C sX
      n) 0) (pullback.snd i₁ i₂) := by
  rw [← chowCohomologyRestriction_eq_zero_iff_vanishesOver, ← TotalChowClass.res_rfl_apply,
    TotalChowClass.res_res, TotalChowClass.res_ofLocallyConstant _ _ _ 0 fun y ↦ ?_,
    Int.cast_zero]
  · rfl
  · rw [← pullback.condition, Scheme.Hom.comp_apply]
    exact hn _

variable {i₁} in
/-- If `E` restricts to zero on `X₁`, the class of `x ↦ C(χ_E(x), n)` restricted to `X₂` vanishes
over `X₁ ×_X X₂` for `n ≥ 1`: the rank vanishes there. -/
theorem vanishesOver_res_ofLocallyConstant_rankChoose
    (hzero : IsZero ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
      i₁.toLRSHom.toShHom).obj E)) {n : ℕ} (hn : 0 < n) :
    BivariantClass.VanishesOver (TotalChowClass.res i₂ rfl (TotalChowClass.ofLocallyConstant C sX
      ((perfectRank E perfect).map fun k ↦ Ring.choose k n)) 0) (pullback.snd i₁ i₂) :=
  vanishesOver_res_ofLocallyConstant C sX i₂ _ fun y ↦ by
    rw [LocallyConstant.map_apply, Function.comp_apply,
      perfectRank_eq_zero_of_isZero perfect i₁ hzero, Ring.choose_zero_pos ℤ hn]

/-- **The class `C(r, n) ∈ A^0(X₂ ⟶ X)`** of Stacks 0FE5, for `r = P'_0(E|_{X₂})` and `n ≥ 1`. Let
`E ∈ D(𝒪_X)` be perfect and restrict to zero on `X₁`. The rank `r(E) = P_0(E)` is the class of the
locally constant function `x ↦ χ_E(x)` (`Stacks.Chow.perfectPowerSum_zero_eq_ofLocallyConstant`),
and `r = P'_0(E|_{X₂})` is the extension of its restriction to `X₂` along the closed cover
(Stacks 0F9H). Accordingly `C(r, n)` is the extension along the closed cover of the restriction to
`X₂` of the class of `x ↦ C(χ_E(x), n)`, which vanishes on `X₁` since `χ_E` does. -/
def closedCoverRankChoose (hcover : Set.range i₁ ∪ Set.range i₂ = Set.univ)
    (hzero : IsZero ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
      i₁.toLRSHom.toShHom).obj E)) (n : ℕ) (hn : 0 < n) :
    BivariantClass C (gysinSystemOfInvertible C) (i₂ ≫ sX) sX i₂ rfl ((0 : ℕ) : ℤ) :=
  closedCoverExtension C sX i₁ i₂ (i₂ ≫ sX) rfl _ hcover
    (vanishesOver_res_ofLocallyConstant_rankChoose C sX i₂ perfect hzero hn)

/-- `C(r, n)` is the extension of the class of `x ↦ C(χ_E(x), n)` along the closed cover. -/
theorem isClosedCoverExtension_closedCoverRankChoose
    (hcover : Set.range i₁ ∪ Set.range i₂ = Set.univ)
    (hzero : IsZero ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
      i₁.toLRSHom.toShHom).obj E)) (n : ℕ) (hn : 0 < n) :
    IsClosedCoverExtension C (gysinSystemOfInvertible C) sX i₁ i₂ (i₂ ≫ sX) rfl
      (TotalChowClass.res i₂ rfl (TotalChowClass.ofLocallyConstant C sX
        ((perfectRank E perfect).map fun k ↦ Ring.choose k n)) 0)
      (closedCoverRankChoose C sX i₁ i₂ perfect hcover hzero n hn) :=
  isClosedCoverExtension_closedCoverExtension C sX i₁ i₂ (i₂ ≫ sX) rfl hcover _

/-- **`r = C(r, 1)`.** For `E` perfect and restricting to zero on `X₁`, the class
`r = P'_0(E|_{X₂})` of Stacks 0F9H is the class `C(r, 1)`; this justifies reading `C(r, n)` as the
binomial coefficient of `r`. -/
theorem closedCoverPowerSum_zero_eq_closedCoverRankChoose_one
    (hcover : Set.range i₁ ∪ Set.range i₂ = Set.univ) (hE : HasDefinedChernClasses E)
    (hzero : IsZero ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
      i₁.toLRSHom.toShHom).obj E))
    (hzero₂ : IsZero ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
      (pullback.snd i₁ i₂).toLRSHom.toShHom).obj
        ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
          i₂.toLRSHom.toShHom).obj E))) :
    closedCoverPowerSum C sX i₁ i₂ (i₂ ≫ sX) rfl (hE.derivedPullback i₂) 0 hcover hzero₂ =
      closedCoverRankChoose C sX i₁ i₂ perfect hcover hzero 1 one_pos := by
  refine (IsClosedCoverExtension.eq_closedCoverExtension hcover _ ?_).trans rfl
  have e : (perfectRank E perfect).map (fun k ↦ Ring.choose k 1) = perfectRank E perfect :=
    LocallyConstant.ext fun x ↦ by simp
  have ha : perfectPowerSumComponent C (i₂ ≫ sX) (hE.derivedPullback i₂) 0 =
      TotalChowClass.res i₂ rfl (TotalChowClass.ofLocallyConstant C sX
        ((perfectRank E perfect).map fun k ↦ Ring.choose k 1)) 0 := by
    rw [e, ← perfectPowerSum_zero_eq_ofLocallyConstant C sX hE perfect,
      res_perfectPowerSum_derivedPullback C sX hE i₂ rfl (hE.derivedPullback i₂)]
    rfl
  rw [← ha]
  exact isClosedCoverExtension_closedCoverPowerSum C sX i₁ i₂ (i₂ ≫ sX) rfl _ 0 hcover hzero₂

end RankChoose

/-- **Comparing extensions along two closed covers with the same second member.** If `c` extends
`a` along `X = Y₀ ∪ X₂`, then `c` is the extension of `a` along every closed cover `X = Y ∪ X₂`
over whose intersection `a` vanishes (Stacks 0FAH). -/
theorem closedCoverExtension_eq_of_isClosedCoverExtension {C : ChowSituation.{u}}
    {X Y Y₀ X₂ : Scheme.{u}} {sX : X ⟶ C.S} [LocallyOfFiniteType sX] {iY : Y ⟶ X}
    {iY₀ : Y₀ ⟶ X} {i₂ : X₂ ⟶ X} [IsClosedImmersion iY] [IsClosedImmersion iY₀]
    [IsClosedImmersion i₂] {p : ℤ}
    {a : chowCohomologyComponent C (gysinSystemOfInvertible C) (i₂ ≫ sX) p}
    {c : BivariantClass C (gysinSystemOfInvertible C) (i₂ ≫ sX) sX i₂ rfl p}
    (hcover : Set.range iY ∪ Set.range i₂ = Set.univ)
    (hcover₀ : Set.range iY₀ ∪ Set.range i₂ = Set.univ)
    (ha : BivariantClass.VanishesOver a (pullback.snd iY i₂))
    (hc : IsClosedCoverExtension C (gysinSystemOfInvertible C) sX iY₀ i₂ (i₂ ≫ sX) rfl a c) :
    closedCoverExtension C sX iY i₂ (i₂ ≫ sX) rfl a hcover ha = c :=
  (closedCoverExtension_eq_of_closedCover C sX iY iY₀ i₂ (i₂ ≫ sX) rfl hcover hcover₀ ha
    hc.vanishesOver).trans (hc.eq_closedCoverExtension hcover₀ hc.vanishesOver).symm

/-! ### The classes of Stacks 0F9H of the restriction of an object of `D(𝒪_X)` -/

section Restrict

variable (C : ChowSituation.{u}) {X X₁ X₂ : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (i₁ : X₁ ⟶ X) (i₂ : X₂ ⟶ X) [IsClosedImmersion i₁] [IsClosedImmersion i₂]
  (hcover : Set.range i₁ ∪ Set.range i₂ = Set.univ) {E : DerivedCategory X.Modules}
  (hE : HasDefinedChernClasses E)
  (hzero : IsZero ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
    i₁.toLRSHom.toShHom).obj E))

/-- **The class `P'_p(E|_{X₂}) ∈ A^p(X₂ ⟶ X)` of Stacks 0F9H** of an object `E ∈ D(𝒪_X)` whose
Chern classes are defined and which restricts to zero on `X₁`; its restriction `E|_{X₂}` then
restricts to zero on `X₁ ∩ X₂`. -/
abbrev closedCoverPowerSumRestrict (p : ℕ) :
    BivariantClass C (gysinSystemOfInvertible C) (i₂ ≫ sX) sX i₂ rfl p :=
  closedCoverPowerSum C sX i₁ i₂ (i₂ ≫ sX) rfl (hE.derivedPullback i₂) p hcover
    (isZero_derivedPullback_of_isZero_of_comp_eq pullback.condition hzero)

/-- **The class `c'_p(E|_{X₂}) ∈ A^p(X₂ ⟶ X)` of Stacks 0F9H**, `p ≥ 1`, of an object
`E ∈ D(𝒪_X)` whose Chern classes are defined and which restricts to zero on `X₁`. -/
abbrev closedCoverChernClassRestrict (p : ℕ) (hp : 0 < p) :
    BivariantClass C (gysinSystemOfInvertible C) (i₂ ≫ sX) sX i₂ rfl p :=
  closedCoverChernClassOfIsZero C sX i₁ i₂ (i₂ ≫ sX) rfl (hE.derivedPullback i₂) hcover
    (isZero_derivedPullback_of_isZero_of_comp_eq pullback.condition hzero) p hp

end Restrict

/-! ### Stacks 0FE5 -/

section TensorProduct

open Stacks.DerivedTensor.RingedSite (derivedTensorProductFunctor)
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback)
open Finset TotalChowClass

variable (C : ChowSituation.{u}) {X X₁ X₂ X₁' X₂' : Scheme.{u}} (sX : X ⟶ C.S)
  [LocallyOfFiniteType sX] (i₁ : X₁ ⟶ X) (i₂ : X₂ ⟶ X) (j₁ : X₁' ⟶ X) (j₂ : X₂' ⟶ X)
  [IsClosedImmersion i₁] [IsClosedImmersion i₂] [IsClosedImmersion j₁] [IsClosedImmersion j₂]
  (hcover : Set.range i₁ ∪ Set.range i₂ = Set.univ)
  (hcover' : Set.range j₁ ∪ Set.range j₂ = Set.univ)
  {E E' : DerivedCategory X.Modules} (hE : HasDefinedChernClasses E)
  (hE' : HasDefinedChernClasses E')
  (hzero : IsZero ((derivedPullback i₁.toLRSHom.toShHom).obj E))
  (hzero' : IsZero ((derivedPullback j₁.toLRSHom.toShHom).obj E'))

include hcover hcover' in
omit [IsClosedImmersion i₁] [IsClosedImmersion i₂] [IsClosedImmersion j₁]
  [IsClosedImmersion j₂] in
/-- `X = (X₁ ∪ X₁') ∪ (X₂ ∩ X₂')` set-theoretically. -/
theorem range_union_range_pullbackSnd_comp_eq_univ :
    (Set.range i₁ ∪ Set.range j₁) ∪ Set.range (pullback.snd i₂ j₂ ≫ j₂) = Set.univ := by
  refine Set.eq_univ_of_forall fun x ↦ ?_
  have h₁ : x ∈ Set.range i₁ ∪ Set.range i₂ := hcover ▸ Set.mem_univ x
  have h₂ : x ∈ Set.range j₁ ∪ Set.range j₂ := hcover' ▸ Set.mem_univ x
  rw [Scheme.Pullback.range_snd_comp]
  rcases h₁ with h₁ | h₁ <;> rcases h₂ with h₂ | h₂
  exacts [Or.inl (Or.inl h₁), Or.inl (Or.inl h₁), Or.inl (Or.inr h₂), Or.inr ⟨h₁, h₂⟩]

/-- `res_h P_p(E)` is a restriction of `P_p(E|_Z)` along `w : W ⟶ Z` when `w ≫ i = h`. -/
private theorem isRestriction_res_perfectPowerSum {E : DerivedCategory X.Modules}
    (hE : HasDefinedChernClasses E) {Z W : Scheme.{u}} (i : Z ⟶ X) [LocallyOfFiniteType i]
    (w : W ⟶ Z) [LocallyOfFiniteType w] (h : W ⟶ X) [LocallyOfFiniteType h] (hw : w ≫ i = h)
    (p : ℕ) :
    BivariantClass.IsRestriction (res h rfl (perfectPowerSum C sX hE p) p)
      (perfectPowerSum C (i ≫ sX) (hE.derivedPullback i) p p) w := by
  have := isRestriction_res_res (perfectPowerSum C sX hE p) i w h hw p
  rwa [res_perfectPowerSum_derivedPullback C sX hE i rfl (hE.derivedPullback i)] at this

/-- `res_h c_p(E)` is a restriction of `c_p(E|_Z)` along `w : W ⟶ Z` when `w ≫ i = h`. -/
private theorem isRestriction_res_perfectChernClass {E : DerivedCategory X.Modules}
    (hE : HasDefinedChernClasses E) {Z W : Scheme.{u}} (i : Z ⟶ X) [LocallyOfFiniteType i]
    (w : W ⟶ Z) [LocallyOfFiniteType w] (h : W ⟶ X) [LocallyOfFiniteType h] (hw : w ≫ i = h)
    (p : ℕ) :
    BivariantClass.IsRestriction (res h rfl (perfectChernClass C sX hE) p)
      (perfectChernClass C (i ≫ sX) (hE.derivedPullback i) p) w := by
  have := isRestriction_res_res (perfectChernClass C sX hE) i w h hw p
  rwa [res_perfectChernClass_derivedPullback_of_comp_eq C sX hE i rfl (hE.derivedPullback i)]
    at this

/-- **Stacks 0FE5 for `P'_p`, the characterization.** The class
`∑_{p₁ + p₂ = p} C(p, p₁) χ_{p₁} χ'_{p₂} ∈ A^p(X₂ ∩ X₂' ⟶ X)` satisfies the characterization of
Stacks 0F9H for `P'_p((E ⊗^L E')|_{X₂ ∩ X₂'})` along the closed cover `X = Y ∪ (X₂ ∩ X₂')`, for
every closed subscheme `Y` whose points lie in `X₁ ∪ X₁'`. No vanishing hypothesis on `Y` is
needed: the vanishing of `P_p((E ⊗^L E')|_{X₂ ∩ X₂'})` over `Y ∩ (X₂ ∩ X₂')` follows
(`Stacks.Chow.IsClosedCoverExtension.vanishesOver`). -/
theorem isClosedCoverExtension_derivedTensor_powerSum {Y : Scheme.{u}} (iY : Y ⟶ X)
    [IsClosedImmersion iY] (hY : Set.range iY ⊆ Set.range i₁ ∪ Set.range j₁) (p : ℕ) :
    IsClosedCoverExtension C (gysinSystemOfInvertible C) sX iY (pullback.snd i₂ j₂ ≫ j₂) _ rfl
      (perfectPowerSumComponent C _ ((hasDefinedChernClasses_derivedTensor hE hE').derivedPullback
        (pullback.snd i₂ j₂ ≫ j₂)) p)
      (∑ q ∈ (antidiagonal p).attach, (p.choose q.1.1 : ℤ) •
        bivariantClassDegreeCongr C _ _ sX _ rfl
          (by have := mem_antidiagonal.1 q.2; omega)
          (supportedIntersectionMul C sX i₂ j₂ (IsPullback.of_hasPullback i₂ j₂) _ rfl
            (closedCoverPowerSumRestrict C sX i₁ i₂ hcover hE hzero q.1.1)
            (closedCoverPowerSumRestrict C sX j₁ j₂ hcover' hE' hzero' q.1.2))) := by
  set iW := pullback.snd i₂ j₂ ≫ j₂
  have hEE' := hasDefinedChernClasses_derivedTensor hE hE'
  have hD : perfectPowerSumComponent C (iW ≫ sX) (hEE'.derivedPullback iW) p =
      ∑ q ∈ (antidiagonal p).attach, (p.choose q.1.1 : ℤ) •
        bivariantClassDegreeCongr C _ _ _ (𝟙 _) (Category.id_comp _)
          (by have := mem_antidiagonal.1 q.2; omega)
          ((res iW rfl (perfectPowerSum C sX hE q.1.1) q.1.1).mulId C (iW ≫ sX)
            (res iW rfl (perfectPowerSum C sX hE' q.1.2) q.1.2)) := by
    change perfectPowerSum C (iW ≫ sX) (hEE'.derivedPullback iW) p p = _
    rw [← res_perfectPowerSum_derivedPullback C sX hEE' iW rfl,
      perfectPowerSum_derivedTensor C sX hE hE' hEE' p, map_sum, TotalChowClass.sum_apply,
      ← Finset.sum_attach]
    refine Finset.sum_congr rfl fun q _ ↦ ?_
    rw [map_zsmul, zsmul_apply, map_mul,
      ((isHomogeneous_perfectPowerSum C sX hE q.1.1).res iW rfl).mul_apply _
        (mem_antidiagonal.1 q.2)]
  rw [hD]
  refine IsClosedCoverExtension.sum C sX iY iW _ fun q _ ↦ ?_
  refine IsClosedCoverExtension.zsmul C sX iY iW ?_ _
  refine IsClosedCoverExtension.bivariantClassDegreeCongr C sX iY iW _ ?_
  exact IsClosedCoverExtension.supportedIntersectionMul iY
    (isClosedCoverExtension_closedCoverPowerSum C sX i₁ i₂ (i₂ ≫ sX) rfl _ _ hcover _)
    (isClosedCoverExtension_closedCoverPowerSum C sX j₁ j₂ (j₂ ≫ sX) rfl _ _ hcover' _)
    (isRestriction_res_perfectPowerSum C sX hE i₂ (pullback.fst i₂ j₂) iW pullback.condition _)
    (isRestriction_res_perfectPowerSum C sX hE' j₂ (pullback.snd i₂ j₂) iW rfl _) hY

/-- **The reduced closed subscheme with underlying set `X₁ ∪ X₁'`**, as an ideal sheaf: the
vanishing ideal of the closed set `X₁ ∪ X₁'`. -/
abbrev reducedUnionIdeal {X X₁ X₁' : Scheme.{u}} (i₁ : X₁ ⟶ X) (j₁ : X₁' ⟶ X)
    [IsClosedImmersion i₁] [IsClosedImmersion j₁] : X.IdealSheafData :=
  Scheme.IdealSheafData.vanishingIdeal
    ⟨Set.range i₁ ∪ Set.range j₁,
      i₁.isClosedEmbedding.isClosed_range.union j₁.isClosedEmbedding.isClosed_range⟩

omit [IsClosedImmersion i₂] [IsClosedImmersion j₂] in
/-- The reduced closed subscheme on `X₁ ∪ X₁'` has underlying set `X₁ ∪ X₁'`. -/
theorem range_subschemeι_reducedUnionIdeal :
    Set.range (reducedUnionIdeal i₁ j₁).subschemeι = Set.range i₁ ∪ Set.range j₁ :=
  Scheme.IdealSheafData.range_subschemeι_vanishingIdeal _

include hcover hcover' in
omit [IsClosedImmersion i₂] [IsClosedImmersion j₂] in
/-- `X = Y ∪ (X₂ ∩ X₂')` for `Y` the reduced closed subscheme on `X₁ ∪ X₁'`. -/
theorem range_union_range_reducedUnionIdeal :
    Set.range (reducedUnionIdeal i₁ j₁).subschemeι ∪ Set.range (pullback.snd i₂ j₂ ≫ j₂) =
      Set.univ := by
  rw [range_subschemeι_reducedUnionIdeal]
  exact range_union_range_pullbackSnd_comp_eq_univ i₁ i₂ j₁ j₂ hcover hcover'

include hcover hcover' in
omit [IsClosedImmersion i₂] [IsClosedImmersion j₂] in
/-- A closed subscheme `Y₀` of `X` with underlying set contained in `X₁ ∪ X₁'` which covers `X`
together with `X₂ ∩ X₂'`: the reduced closed subscheme on `X₁ ∪ X₁'`. -/
theorem exists_closedCover_union :
    ∃ (Y₀ : Scheme.{u}) (iY₀ : Y₀ ⟶ X), IsClosedImmersion iY₀ ∧
      Set.range iY₀ ⊆ Set.range i₁ ∪ Set.range j₁ ∧
      Set.range iY₀ ∪ Set.range (pullback.snd i₂ j₂ ≫ j₂) = Set.univ :=
  ⟨_, (reducedUnionIdeal i₁ j₁).subschemeι, inferInstance,
    (range_subschemeι_reducedUnionIdeal i₁ j₁).subset,
    range_union_range_reducedUnionIdeal i₁ i₂ j₁ j₂ hcover hcover'⟩

/-- **Stacks 0FE5 for `P'_p`, along an arbitrary closed cover `X = Y ∪ (X₂ ∩ X₂')`** on which
`(E ⊗^L E')|_{X₂ ∩ X₂'}` restricts to zero on `Y ∩ X₂ ∩ X₂'`; see
`Stacks.Chow.closedCoverPowerSum_derivedTensor` for the cover of the source. -/
theorem closedCoverPowerSum_derivedTensor_of_closedCover {Y : Scheme.{u}} (iY : Y ⟶ X)
    [IsClosedImmersion iY]
    (hcoverY : Set.range iY ∪ Set.range (pullback.snd i₂ j₂ ≫ j₂) = Set.univ)
    (hzeroY : IsZero
      ((derivedPullback (pullback.snd iY (pullback.snd i₂ j₂ ≫ j₂)).toLRSHom.toShHom).obj
        ((derivedPullback (pullback.snd i₂ j₂ ≫ j₂).toLRSHom.toShHom).obj
          (((derivedTensorProductFunctor X.sheaf).obj E).obj E')))) (p : ℕ) :
    closedCoverPowerSum C sX iY (pullback.snd i₂ j₂ ≫ j₂) _ rfl
        ((hasDefinedChernClasses_derivedTensor hE hE').derivedPullback _) p hcoverY hzeroY =
      ∑ q ∈ (antidiagonal p).attach, (p.choose q.1.1 : ℤ) •
        bivariantClassDegreeCongr C _ _ sX _ rfl
          (by have := mem_antidiagonal.1 q.2; omega)
          (supportedIntersectionMul C sX i₂ j₂ (IsPullback.of_hasPullback i₂ j₂) _ rfl
            (closedCoverPowerSumRestrict C sX i₁ i₂ hcover hE hzero q.1.1)
            (closedCoverPowerSumRestrict C sX j₁ j₂ hcover' hE' hzero' q.1.2)) := by
  obtain ⟨Y₀, iY₀, _, hY₀, hcover₀⟩ := exists_closedCover_union i₁ i₂ j₁ j₂ hcover hcover'
  exact closedCoverExtension_eq_of_isClosedCoverExtension hcoverY hcover₀
    (vanishesOver_perfectPowerSumClass_of_isZero C _ _ _ p hzeroY)
    (isClosedCoverExtension_derivedTensor_powerSum C sX i₁ i₂ j₁ j₂ hcover hcover' hE hE' hzero
      hzero' iY₀ hY₀ p)

/-- **Stacks 0FE5 for `c'_1`, the characterization.** The class `r γ'_1 + r' γ_1` satisfies the
characterization of Stacks 0F9H for `c'_1((E ⊗^L E')|_{X₂ ∩ X₂'})` along the closed cover
`X = Y ∪ (X₂ ∩ X₂')`, for every closed subscheme `Y` whose points lie in `X₁ ∪ X₁'`; no vanishing
hypothesis on `Y` is needed. -/
theorem isClosedCoverExtension_derivedTensor_chernClass_one {Y : Scheme.{u}} (iY : Y ⟶ X)
    [IsClosedImmersion iY] (hY : Set.range iY ⊆ Set.range i₁ ∪ Set.range j₁) :
    IsClosedCoverExtension C (gysinSystemOfInvertible C) sX iY (pullback.snd i₂ j₂ ≫ j₂) _ rfl
      (perfectChernClass C _ ((hasDefinedChernClasses_derivedTensor hE hE').derivedPullback
        (pullback.snd i₂ j₂ ≫ j₂)) 1)
      (bivariantClassDegreeCongr C _ _ sX _ rfl (by norm_num)
          (supportedIntersectionMul C sX i₂ j₂ (IsPullback.of_hasPullback i₂ j₂) _ rfl
            (closedCoverPowerSumRestrict C sX i₁ i₂ hcover hE hzero 0)
            (closedCoverChernClassRestrict C sX j₁ j₂ hcover' hE' hzero' 1 one_pos)) +
        bivariantClassDegreeCongr C _ _ sX _ rfl (by norm_num)
          (supportedIntersectionMul C sX j₂ i₂ (IsPullback.of_hasPullback i₂ j₂).flip _
            pullback.condition
            (closedCoverPowerSumRestrict C sX j₁ j₂ hcover' hE' hzero' 0)
            (closedCoverChernClassRestrict C sX i₁ i₂ hcover hE hzero 1 one_pos))) := by
  set iW := pullback.snd i₂ j₂ ≫ j₂
  have hEE' := hasDefinedChernClasses_derivedTensor hE hE'
  have hD : perfectChernClass C (iW ≫ sX) (hEE'.derivedPullback iW) 1 =
      bivariantClassDegreeCongr C _ _ _ (𝟙 _) (Category.id_comp _) (by norm_num)
          ((res iW rfl (perfectPowerSum C sX hE 0) 0).mulId C (iW ≫ sX)
            (res iW rfl (perfectChernClass C sX hE') 1)) +
        bivariantClassDegreeCongr C _ _ _ (𝟙 _) (Category.id_comp _) (by norm_num)
          ((res iW rfl (perfectPowerSum C sX hE' 0) 0).mulId C (iW ≫ sX)
            (res iW rfl (perfectChernClass C sX hE) 1)) := by
    rw [← res_perfectChernClass_derivedPullback_of_comp_eq C sX hEE' iW rfl,
      ← res_homPart_apply_self,
      perfectChernClass_derivedTensor_one C sX hE hE' hEE', map_add, TotalChowClass.add_apply,
      map_mul, map_mul,
      ((isHomogeneous_perfectPowerSum C sX hE 0).res iW rfl).mul_apply _ (zero_add 1),
      ((isHomogeneous_perfectPowerSum C sX hE' 0).res iW rfl).mul_apply _ (zero_add 1),
      res_homPart_apply_self, res_homPart_apply_self]
  rw [hD]
  refine IsClosedCoverExtension.add
    (IsClosedCoverExtension.bivariantClassDegreeCongr C sX iY iW _ ?_)
    (IsClosedCoverExtension.bivariantClassDegreeCongr C sX iY iW _ ?_)
  · exact IsClosedCoverExtension.supportedIntersectionMul iY
      (isClosedCoverExtension_closedCoverPowerSum C sX i₁ i₂ (i₂ ≫ sX) rfl _ _ hcover _)
      (isClosedCoverExtension_closedCoverChernClassOfIsZero C sX j₁ j₂ _ hcover' _ 1 one_pos)
      (isRestriction_res_perfectPowerSum C sX hE i₂ (pullback.fst i₂ j₂) iW pullback.condition _)
      (isRestriction_res_perfectChernClass C sX hE' j₂ (pullback.snd i₂ j₂) iW rfl _) hY
  · exact IsClosedCoverExtension.supportedIntersectionMul iY
      (isClosedCoverExtension_closedCoverPowerSum C sX j₁ j₂ (j₂ ≫ sX) rfl _ _ hcover' _)
      (isClosedCoverExtension_closedCoverChernClassOfIsZero C sX i₁ i₂ _ hcover _ 1 one_pos)
      (isRestriction_res_perfectPowerSum C sX hE' j₂ (pullback.snd i₂ j₂) iW rfl _)
      (isRestriction_res_perfectChernClass C sX hE i₂ (pullback.fst i₂ j₂) iW pullback.condition _)
      (hY.trans (Set.union_comm _ _).subset)

/-- **Stacks 0FE5 for `c'_1`, along an arbitrary closed cover `X = Y ∪ (X₂ ∩ X₂')`** on which
`(E ⊗^L E')|_{X₂ ∩ X₂'}` restricts to zero on `Y ∩ X₂ ∩ X₂'`; see
`Stacks.Chow.closedCoverChernClass_derivedTensor_one` for the cover of the source. -/
theorem closedCoverChernClass_derivedTensor_one_of_closedCover {Y : Scheme.{u}} (iY : Y ⟶ X)
    [IsClosedImmersion iY]
    (hcoverY : Set.range iY ∪ Set.range (pullback.snd i₂ j₂ ≫ j₂) = Set.univ)
    (hzeroY : IsZero
      ((derivedPullback (pullback.snd iY (pullback.snd i₂ j₂ ≫ j₂)).toLRSHom.toShHom).obj
        ((derivedPullback (pullback.snd i₂ j₂ ≫ j₂).toLRSHom.toShHom).obj
          (((derivedTensorProductFunctor X.sheaf).obj E).obj E')))) :
    closedCoverChernClassOfIsZero C sX iY (pullback.snd i₂ j₂ ≫ j₂) _ rfl
        ((hasDefinedChernClasses_derivedTensor hE hE').derivedPullback _) hcoverY hzeroY 1
        one_pos =
      bivariantClassDegreeCongr C _ _ sX _ rfl (by norm_num)
          (supportedIntersectionMul C sX i₂ j₂ (IsPullback.of_hasPullback i₂ j₂) _ rfl
            (closedCoverPowerSumRestrict C sX i₁ i₂ hcover hE hzero 0)
            (closedCoverChernClassRestrict C sX j₁ j₂ hcover' hE' hzero' 1 one_pos)) +
        bivariantClassDegreeCongr C _ _ sX _ rfl (by norm_num)
          (supportedIntersectionMul C sX j₂ i₂ (IsPullback.of_hasPullback i₂ j₂).flip _
            pullback.condition
            (closedCoverPowerSumRestrict C sX j₁ j₂ hcover' hE' hzero' 0)
            (closedCoverChernClassRestrict C sX i₁ i₂ hcover hE hzero 1 one_pos)) := by
  obtain ⟨Y₀, iY₀, _, hY₀, hcover₀⟩ := exists_closedCover_union i₁ i₂ j₁ j₂ hcover hcover'
  exact closedCoverExtension_eq_of_isClosedCoverExtension hcoverY hcover₀
    (vanishesOver_perfectChernClass_of_isZero' C sX iY _ _ hzeroY 1 one_pos)
    (isClosedCoverExtension_derivedTensor_chernClass_one C sX i₁ i₂ j₁ j₂ hcover hcover' hE hE'
      hzero hzero' iY₀ hY₀)

/-- **Stacks 0FAG for `c_2`, restricted along a morphism, in components.** For `h : W ⟶ X`, write
`ρ` for the restriction along `h`. The component of degree `2` of the total Chern class of
`(E ⊗^L E')|_W` is

  `ρr(E) ρc_2(E') + ρr(E') ρc_2(E) + ρC(r(E), 2) (ρc_1(E') ρc_1(E')) +
    (ρr(E) ρr(E')) (ρc_1(E') ρc_1(E)) - ρc_1(E') ρc_1(E) + ρC(r(E'), 2) (ρc_1(E) ρc_1(E))`,

with the products of `A^*(W)` and the binomial coefficients read as in
`Stacks.Chow.perfectChernClass_derivedTensor_two`; each summand is read in degree `2`. -/
theorem perfectChernClass_two_derivedPullback_derivedTensor
    (perfectE : RingedSpace.IsPerfect.{u, u + 1} E)
    (perfectE' : RingedSpace.IsPerfect.{u, u + 1} E') {W : Scheme.{u}} (h : W ⟶ X)
    [LocallyOfFiniteType h] :
    perfectChernClass C (h ≫ sX)
        ((hasDefinedChernClasses_derivedTensor hE hE').derivedPullback h) 2 =
      bivariantClassDegreeCongr C _ _ _ (𝟙 _) (Category.id_comp _) (by norm_num)
          ((res h rfl (perfectPowerSum C sX hE 0) 0).mulId C (h ≫ sX)
            (res h rfl (perfectChernClass C sX hE') 2)) +
        bivariantClassDegreeCongr C _ _ _ (𝟙 _) (Category.id_comp _) (by norm_num)
          ((res h rfl (perfectPowerSum C sX hE' 0) 0).mulId C (h ≫ sX)
            (res h rfl (perfectChernClass C sX hE) 2)) +
        bivariantClassDegreeCongr C _ _ _ (𝟙 _) (Category.id_comp _) (by norm_num)
          ((res h rfl (ofLocallyConstant C sX
              ((perfectRank E perfectE).map fun k ↦ Ring.choose k 2)) 0).mulId C (h ≫ sX)
            ((res h rfl (perfectChernClass C sX hE') 1).mulId C (h ≫ sX)
              (res h rfl (perfectChernClass C sX hE') 1))) +
        (bivariantClassDegreeCongr C _ _ _ (𝟙 _) (Category.id_comp _) (by norm_num)
            (((res h rfl (perfectPowerSum C sX hE 0) 0).mulId C (h ≫ sX)
                (res h rfl (perfectPowerSum C sX hE' 0) 0)).mulId C (h ≫ sX)
              ((res h rfl (perfectChernClass C sX hE') 1).mulId C (h ≫ sX)
                (res h rfl (perfectChernClass C sX hE) 1))) -
          bivariantClassDegreeCongr C _ _ _ (𝟙 _) (Category.id_comp _) (by norm_num)
            ((res h rfl (perfectChernClass C sX hE') 1).mulId C (h ≫ sX)
              (res h rfl (perfectChernClass C sX hE) 1))) +
        bivariantClassDegreeCongr C _ _ _ (𝟙 _) (Category.id_comp _) (by norm_num)
          ((res h rfl (ofLocallyConstant C sX
              ((perfectRank E' perfectE').map fun k ↦ Ring.choose k 2)) 0).mulId C (h ≫ sX)
            ((res h rfl (perfectChernClass C sX hE) 1).mulId C (h ≫ sX)
              (res h rfl (perfectChernClass C sX hE) 1))) := by
  have hEE' := hasDefinedChernClasses_derivedTensor hE hE'
  have hA := (isHomogeneous_perfectPowerSum C sX hE 0).res h rfl
  have hA' := (isHomogeneous_perfectPowerSum C sX hE' 0).res h rfl
  have hL := (isHomogeneous_ofLocallyConstant C sX
    ((perfectRank E perfectE).map fun k ↦ Ring.choose k 2)).res h rfl
  have hL' := (isHomogeneous_ofLocallyConstant C sX
    ((perfectRank E' perfectE').map fun k ↦ Ring.choose k 2)).res h rfl
  have hB₁ := (TotalChowClass.isHomogeneous_homComponent 1 (perfectChernClass C sX hE)).res h rfl
  have hB₁' := (TotalChowClass.isHomogeneous_homComponent 1 (perfectChernClass C sX hE')).res h rfl
  have hAA' := hA.mul hA'
  have hsq : ∀ (x : TotalChowClass C sX),
      IsHomogeneous 1 (res h rfl (TotalChowClass.homComponent 1 x)) →
      ((res h rfl (TotalChowClass.homComponent 1 x)) ^ 2) 2 =
        bivariantClassDegreeCongr C _ _ _ (𝟙 _) (Category.id_comp _) (by norm_num)
          ((res h rfl x 1).mulId C (h ≫ sX) (res h rfl x 1)) := fun x hx ↦ by
    rw [pow_two, hx.mul_apply _ (by norm_num : 1 + 1 = 2), res_homPart_apply_self]
  have hQ : (res h rfl (TotalChowClass.homComponent 1 (perfectChernClass C sX hE')) *
      res h rfl (TotalChowClass.homComponent 1 (perfectChernClass C sX hE))) 2 =
        bivariantClassDegreeCongr C _ _ _ (𝟙 _) (Category.id_comp _) (by norm_num)
          ((res h rfl (perfectChernClass C sX hE') 1).mulId C (h ≫ sX)
            (res h rfl (perfectChernClass C sX hE) 1)) := by
    rw [hB₁'.mul_apply _ (by norm_num : 1 + 1 = 2), res_homPart_apply_self,
      res_homPart_apply_self]
  rw [← res_perfectChernClass_derivedPullback_of_comp_eq C sX hEE' h rfl, ← res_homPart_apply_self,
    perfectChernClass_derivedTensor_two C sX hE hE' hEE' perfectE perfectE']
  simp only [map_add, map_sub, map_mul, map_pow, sub_mul, one_mul, TotalChowClass.add_apply,
    TotalChowClass.sub_apply]
  rw [hA.mul_apply _ (by norm_num : 0 + 2 = 2), hA'.mul_apply _ (by norm_num : 0 + 2 = 2),
    hL.mul_apply _ (by norm_num : 0 + 2 = 2), hL'.mul_apply _ (by norm_num : 0 + 2 = 2),
    hAA'.mul_apply _ (by norm_num : 0 + 0 + 2 = 2), hA.mul_apply _ (by norm_num : 0 + 0 = 0),
    hsq _ hB₁', hsq _ hB₁, hQ, res_homPart_apply_self, res_homPart_apply_self]
  simp only [BivariantClass.mulId_bivariantClassDegreeCongr_right,
    BivariantClass.mulId_bivariantClassDegreeCongr_left,
    bivariantClassDegreeCongr_bivariantClassDegreeCongr]

/-- **Stacks 0FE5 for `c'_2`, the characterization.** The class
`r γ'_2 + r' γ_2 + C(r, 2) (γ'_1)² + (r r' - 1) γ'_1 γ_1 + C(r', 2) γ_1²` satisfies the
characterization of Stacks 0F9H for `c'_2((E ⊗^L E')|_{X₂ ∩ X₂'})` along the closed cover
`X = Y ∪ (X₂ ∩ X₂')`, for every closed subscheme `Y` covering `X` with `X₂ ∩ X₂'` whose points lie
in `X₁ ∪ X₁'`; no vanishing hypothesis on `Y` is needed. The readings of `C(r, 2)` and of
`(r r' - 1) γ'_1 γ_1` are those of `Stacks.Chow.closedCoverChernClass_derivedTensor_two`. -/
theorem isClosedCoverExtension_derivedTensor_chernClass_two
    (perfectE : RingedSpace.IsPerfect.{u, u + 1} E)
    (perfectE' : RingedSpace.IsPerfect.{u, u + 1} E') {Y : Scheme.{u}} (iY : Y ⟶ X)
    [IsClosedImmersion iY] (hY : Set.range iY ⊆ Set.range i₁ ∪ Set.range j₁)
    (hcoverY : Set.range iY ∪ Set.range (pullback.snd i₂ j₂ ≫ j₂) = Set.univ) :
    IsClosedCoverExtension C (gysinSystemOfInvertible C) sX iY (pullback.snd i₂ j₂ ≫ j₂) _ rfl
      (perfectChernClass C _ ((hasDefinedChernClasses_derivedTensor hE hE').derivedPullback
        (pullback.snd i₂ j₂ ≫ j₂)) 2)
      (bivariantClassDegreeCongr C _ _ sX _ rfl (by norm_num)
          (supportedIntersectionMul C sX i₂ j₂ (IsPullback.of_hasPullback i₂ j₂) _ rfl
            (closedCoverPowerSumRestrict C sX i₁ i₂ hcover hE hzero 0)
            (closedCoverChernClassRestrict C sX j₁ j₂ hcover' hE' hzero' 2 two_pos)) +
        bivariantClassDegreeCongr C _ _ sX _ rfl (by norm_num)
          (supportedIntersectionMul C sX j₂ i₂ (IsPullback.of_hasPullback i₂ j₂).flip _
            pullback.condition
            (closedCoverPowerSumRestrict C sX j₁ j₂ hcover' hE' hzero' 0)
            (closedCoverChernClassRestrict C sX i₁ i₂ hcover hE hzero 2 two_pos)) +
        bivariantClassDegreeCongr C _ _ sX _ rfl (by norm_num)
          (supportedIntersectionMul C sX i₂ j₂ (IsPullback.of_hasPullback i₂ j₂) _ rfl
            (closedCoverRankChoose C sX i₁ i₂ perfectE hcover hzero 2 two_pos)
            (supportedMul C (j₂ ≫ sX) sX j₂ rfl
              (closedCoverChernClassRestrict C sX j₁ j₂ hcover' hE' hzero' 1 one_pos)
              (closedCoverChernClassRestrict C sX j₁ j₂ hcover' hE' hzero' 1 one_pos))) +
        (bivariantClassDegreeCongr C _ _ sX _ rfl (by norm_num)
            (supportedMul C ((pullback.snd i₂ j₂ ≫ j₂) ≫ sX) sX (pullback.snd i₂ j₂ ≫ j₂) rfl
              (supportedIntersectionMul C sX i₂ j₂ (IsPullback.of_hasPullback i₂ j₂) _ rfl
                (closedCoverPowerSumRestrict C sX i₁ i₂ hcover hE hzero 0)
                (closedCoverPowerSumRestrict C sX j₁ j₂ hcover' hE' hzero' 0))
              (supportedIntersectionMul C sX j₂ i₂ (IsPullback.of_hasPullback i₂ j₂).flip _
                pullback.condition
                (closedCoverChernClassRestrict C sX j₁ j₂ hcover' hE' hzero' 1 one_pos)
                (closedCoverChernClassRestrict C sX i₁ i₂ hcover hE hzero 1 one_pos))) -
          bivariantClassDegreeCongr C _ _ sX _ rfl (by norm_num)
            (supportedIntersectionMul C sX j₂ i₂ (IsPullback.of_hasPullback i₂ j₂).flip _
              pullback.condition
              (closedCoverChernClassRestrict C sX j₁ j₂ hcover' hE' hzero' 1 one_pos)
              (closedCoverChernClassRestrict C sX i₁ i₂ hcover hE hzero 1 one_pos))) +
        bivariantClassDegreeCongr C _ _ sX _ rfl (by norm_num)
          (supportedIntersectionMul C sX j₂ i₂ (IsPullback.of_hasPullback i₂ j₂).flip _
            pullback.condition
            (closedCoverRankChoose C sX j₁ j₂ perfectE' hcover' hzero' 2 two_pos)
            (supportedMul C (i₂ ≫ sX) sX i₂ rfl
              (closedCoverChernClassRestrict C sX i₁ i₂ hcover hE hzero 1 one_pos)
              (closedCoverChernClassRestrict C sX i₁ i₂ hcover hE hzero 1 one_pos)))) := by
  set iW := pullback.snd i₂ j₂ ≫ j₂
  have hEE' := hasDefinedChernClasses_derivedTensor hE hE'
  rw [perfectChernClass_two_derivedPullback_derivedTensor C sX hE hE' perfectE perfectE' iW]
  have hz₂ := isZero_derivedPullback_of_isZero_of_comp_eq
    (pullback.condition (f := i₁) (g := i₂)) hzero
  have hz₂' := isZero_derivedPullback_of_isZero_of_comp_eq
    (pullback.condition (f := j₁) (g := j₂)) hzero'
  have hcr := isClosedCoverExtension_closedCoverPowerSum C sX i₁ i₂ (i₂ ≫ sX) rfl
    (hE.derivedPullback i₂) 0 hcover hz₂
  have hcr' := isClosedCoverExtension_closedCoverPowerSum C sX j₁ j₂ (j₂ ≫ sX) rfl
    (hE'.derivedPullback j₂) 0 hcover' hz₂'
  have hcγ := isClosedCoverExtension_closedCoverChernClassOfIsZero C sX i₁ i₂
    (hE.derivedPullback i₂) hcover hz₂
  have hcγ' := isClosedCoverExtension_closedCoverChernClassOfIsZero C sX j₁ j₂
    (hE'.derivedPullback j₂) hcover' hz₂'
  have hdA := isRestriction_res_perfectPowerSum C sX hE i₂ (pullback.fst i₂ j₂) iW
    pullback.condition 0
  have hdA' := isRestriction_res_perfectPowerSum C sX hE' j₂ (pullback.snd i₂ j₂) iW rfl 0
  have hdB := isRestriction_res_perfectChernClass C sX hE i₂ (pullback.fst i₂ j₂) iW
    pullback.condition
  have hdB' := isRestriction_res_perfectChernClass C sX hE' j₂ (pullback.snd i₂ j₂) iW rfl
  have hdL := isRestriction_res_res (ofLocallyConstant C sX
    ((perfectRank E perfectE).map fun k ↦ Ring.choose k 2)) i₂ (pullback.fst i₂ j₂) iW
    pullback.condition 0
  have hdL' := isRestriction_res_res (ofLocallyConstant C sX
    ((perfectRank E' perfectE').map fun k ↦ Ring.choose k 2)) j₂ (pullback.snd i₂ j₂) iW rfl 0
  have hY' : Set.range iY ⊆ Set.range j₁ ∪ Set.range i₁ := hY.trans (Set.union_comm _ _).subset
  have hsq := IsClosedCoverExtension.supportedMul C sX i₁ i₂ hcover
    (vanishesOver_perfectChernClass_of_isZero' C sX i₁ i₂ _ hz₂ 1 one_pos)
    (vanishesOver_perfectChernClass_of_isZero' C sX i₁ i₂ _ hz₂ 1 one_pos)
    (hcγ 1 one_pos) (hcγ 1 one_pos)
  have hsq' := IsClosedCoverExtension.supportedMul C sX j₁ j₂ hcover'
    (vanishesOver_perfectChernClass_of_isZero' C sX j₁ j₂ _ hz₂' 1 one_pos)
    (vanishesOver_perfectChernClass_of_isZero' C sX j₁ j₂ _ hz₂' 1 one_pos)
    (hcγ' 1 one_pos) (hcγ' 1 one_pos)
  have hrr := IsClosedCoverExtension.supportedIntersectionMul
    (sq := IsPullback.of_hasPullback i₂ j₂) (hW := rfl) iY hcr hcr' hdA hdA' hY
  have hγγ := IsClosedCoverExtension.supportedIntersectionMul
    (sq := (IsPullback.of_hasPullback i₂ j₂).flip) (hW := pullback.condition) iY (hcγ' 1 one_pos)
    (hcγ 1 one_pos) (hdB' 1) (hdB 1) hY'
  refine IsClosedCoverExtension.add (IsClosedCoverExtension.add (IsClosedCoverExtension.add
    (IsClosedCoverExtension.add ?_ ?_) ?_) (IsClosedCoverExtension.sub C sX iY iW ?_ ?_)) ?_
  · exact IsClosedCoverExtension.bivariantClassDegreeCongr C sX iY iW _
      (IsClosedCoverExtension.supportedIntersectionMul iY hcr (hcγ' 2 two_pos) hdA (hdB' 2) hY)
  · exact IsClosedCoverExtension.bivariantClassDegreeCongr C sX iY iW _
      (IsClosedCoverExtension.supportedIntersectionMul iY hcr' (hcγ 2 two_pos) hdA' (hdB 2) hY')
  · exact IsClosedCoverExtension.bivariantClassDegreeCongr C sX iY iW _
      (IsClosedCoverExtension.supportedIntersectionMul iY
        (isClosedCoverExtension_closedCoverRankChoose C sX i₁ i₂ perfectE hcover hzero 2 two_pos)
        hsq' hdL ((hdB' 1).mulId (hdB' 1)) hY)
  · exact IsClosedCoverExtension.bivariantClassDegreeCongr C sX iY iW _
      (IsClosedCoverExtension.supportedMul C sX iY iW hcoverY hrr.vanishesOver
        hγγ.vanishesOver hrr hγγ)
  · exact IsClosedCoverExtension.bivariantClassDegreeCongr C sX iY iW _ hγγ
  · exact IsClosedCoverExtension.bivariantClassDegreeCongr C sX iY iW _
      (IsClosedCoverExtension.supportedIntersectionMul iY
        (isClosedCoverExtension_closedCoverRankChoose C sX j₁ j₂ perfectE' hcover' hzero' 2
          two_pos)
        hsq hdL' ((hdB 1).mulId (hdB 1)) hY')

/-- **Stacks 0FE5 for `c'_2`, along an arbitrary closed cover `X = Y ∪ (X₂ ∩ X₂')`** on which
`(E ⊗^L E')|_{X₂ ∩ X₂'}` restricts to zero on `Y ∩ X₂ ∩ X₂'`; see
`Stacks.Chow.closedCoverChernClass_derivedTensor_two` for the cover of the source. -/
theorem closedCoverChernClass_derivedTensor_two_of_closedCover
    (perfectE : RingedSpace.IsPerfect.{u, u + 1} E)
    (perfectE' : RingedSpace.IsPerfect.{u, u + 1} E') {Y : Scheme.{u}} (iY : Y ⟶ X)
    [IsClosedImmersion iY]
    (hcoverY : Set.range iY ∪ Set.range (pullback.snd i₂ j₂ ≫ j₂) = Set.univ)
    (hzeroY : IsZero
      ((derivedPullback (pullback.snd iY (pullback.snd i₂ j₂ ≫ j₂)).toLRSHom.toShHom).obj
        ((derivedPullback (pullback.snd i₂ j₂ ≫ j₂).toLRSHom.toShHom).obj
          (((derivedTensorProductFunctor X.sheaf).obj E).obj E')))) :
    closedCoverChernClassOfIsZero C sX iY (pullback.snd i₂ j₂ ≫ j₂) _ rfl
        ((hasDefinedChernClasses_derivedTensor hE hE').derivedPullback _) hcoverY hzeroY 2
        two_pos =
      (bivariantClassDegreeCongr C _ _ sX _ rfl (by norm_num)
          (supportedIntersectionMul C sX i₂ j₂ (IsPullback.of_hasPullback i₂ j₂) _ rfl
            (closedCoverPowerSumRestrict C sX i₁ i₂ hcover hE hzero 0)
            (closedCoverChernClassRestrict C sX j₁ j₂ hcover' hE' hzero' 2 two_pos)) +
        bivariantClassDegreeCongr C _ _ sX _ rfl (by norm_num)
          (supportedIntersectionMul C sX j₂ i₂ (IsPullback.of_hasPullback i₂ j₂).flip _
            pullback.condition
            (closedCoverPowerSumRestrict C sX j₁ j₂ hcover' hE' hzero' 0)
            (closedCoverChernClassRestrict C sX i₁ i₂ hcover hE hzero 2 two_pos)) +
        bivariantClassDegreeCongr C _ _ sX _ rfl (by norm_num)
          (supportedIntersectionMul C sX i₂ j₂ (IsPullback.of_hasPullback i₂ j₂) _ rfl
            (closedCoverRankChoose C sX i₁ i₂ perfectE hcover hzero 2 two_pos)
            (supportedMul C (j₂ ≫ sX) sX j₂ rfl
              (closedCoverChernClassRestrict C sX j₁ j₂ hcover' hE' hzero' 1 one_pos)
              (closedCoverChernClassRestrict C sX j₁ j₂ hcover' hE' hzero' 1 one_pos))) +
        (bivariantClassDegreeCongr C _ _ sX _ rfl (by norm_num)
            (supportedMul C ((pullback.snd i₂ j₂ ≫ j₂) ≫ sX) sX (pullback.snd i₂ j₂ ≫ j₂) rfl
              (supportedIntersectionMul C sX i₂ j₂ (IsPullback.of_hasPullback i₂ j₂) _ rfl
                (closedCoverPowerSumRestrict C sX i₁ i₂ hcover hE hzero 0)
                (closedCoverPowerSumRestrict C sX j₁ j₂ hcover' hE' hzero' 0))
              (supportedIntersectionMul C sX j₂ i₂ (IsPullback.of_hasPullback i₂ j₂).flip _
                pullback.condition
                (closedCoverChernClassRestrict C sX j₁ j₂ hcover' hE' hzero' 1 one_pos)
                (closedCoverChernClassRestrict C sX i₁ i₂ hcover hE hzero 1 one_pos))) -
          bivariantClassDegreeCongr C _ _ sX _ rfl (by norm_num)
            (supportedIntersectionMul C sX j₂ i₂ (IsPullback.of_hasPullback i₂ j₂).flip _
              pullback.condition
              (closedCoverChernClassRestrict C sX j₁ j₂ hcover' hE' hzero' 1 one_pos)
              (closedCoverChernClassRestrict C sX i₁ i₂ hcover hE hzero 1 one_pos))) +
        bivariantClassDegreeCongr C _ _ sX _ rfl (by norm_num)
          (supportedIntersectionMul C sX j₂ i₂ (IsPullback.of_hasPullback i₂ j₂).flip _
            pullback.condition
            (closedCoverRankChoose C sX j₁ j₂ perfectE' hcover' hzero' 2 two_pos)
            (supportedMul C (i₂ ≫ sX) sX i₂ rfl
              (closedCoverChernClassRestrict C sX i₁ i₂ hcover hE hzero 1 one_pos)
              (closedCoverChernClassRestrict C sX i₁ i₂ hcover hE hzero 1 one_pos)))) := by
  obtain ⟨Y₀, iY₀, _, hY₀, hcover₀⟩ := exists_closedCover_union i₁ i₂ j₁ j₂ hcover hcover'
  exact closedCoverExtension_eq_of_isClosedCoverExtension hcoverY hcover₀
    (vanishesOver_perfectChernClass_of_isZero' C sX iY _ _ hzeroY 2 two_pos)
    (isClosedCoverExtension_derivedTensor_chernClass_two C sX i₁ i₂ j₁ j₂ hcover hcover' hE hE'
      hzero hzero' perfectE perfectE' iY₀ hY₀ hcover₀)

/-! ### Stacks 0FE5 along the closed cover of the source -/

include hzero hzero' in
omit [IsClosedImmersion i₂] [IsClosedImmersion j₂] in
/-- **`E ⊗^L E'` restricts to zero on `Y ∩ (X₂ ∩ X₂')`**, for `Y` the reduced closed subscheme on
`X₁ ∪ X₁'` and `E`, `E'` perfect: the image of `Y ∩ (X₂ ∩ X₂') ⟶ X` lies in `X₁ ∪ X₁'`
(`Stacks.Chow.isZero_derivedPullback_derivedTensor_of_range_subset`). -/
theorem isZero_derivedPullback_derivedTensor_reducedUnion
    (perfectE : RingedSpace.IsPerfect.{u, u + 1} E)
    (perfectE' : RingedSpace.IsPerfect.{u, u + 1} E') :
    IsZero ((derivedPullback (pullback.snd (reducedUnionIdeal i₁ j₁).subschemeι
        (pullback.snd i₂ j₂ ≫ j₂)).toLRSHom.toShHom).obj
      ((derivedPullback (pullback.snd i₂ j₂ ≫ j₂).toLRSHom.toShHom).obj
        (((derivedTensorProductFunctor X.sheaf).obj E).obj E'))) := by
  refine IsZero.of_iso ?_ (derivedPullbackCompIsoOfScheme _ _ _)
  refine isZero_derivedPullback_derivedTensor_of_range_subset i₁ j₁ perfectE perfectE' hzero
    hzero' _ ?_
  rw [← range_subschemeι_reducedUnionIdeal i₁ j₁]
  rintro _ ⟨y, rfl⟩
  exact ⟨(pullback.fst (reducedUnionIdeal i₁ j₁).subschemeι (pullback.snd i₂ j₂ ≫ j₂)) y, by
    rw [← Scheme.Hom.comp_apply, pullback.condition]⟩

/-- **Stacks 0FE5 for `P'_p`.** Let `X = X₁ ∪ X₂ = X₁' ∪ X₂'` be two closed
covers and let `E`, `E' ∈ D(𝒪_X)` be perfect objects whose Chern classes are defined and which
restrict to zero on `X₁` and `X₁'`. Write `χ_p = P'_p(E|_{X₂})` and
`χ'_p = P'_p(E'|_{X₂'})` for the classes of Stacks 0F9H. Let `Y ⊆ X` be the reduced closed
subscheme with underlying set `X₁ ∪ X₁'` (`Stacks.Chow.reducedUnionIdeal`); then
`X = Y ∪ (X₂ ∩ X₂')`, and `E ⊗^L E'` restricts to zero on `Y ∩ (X₂ ∩ X₂')`, so the class of
Stacks 0F9H of `(E ⊗^L E')|_{X₂ ∩ X₂'}` along `X = Y ∪ (X₂ ∩ X₂')` is defined; by Stacks 0FAH
it does not depend on the choice of `Y`. Then

  `P'_p((E ⊗^L E')|_{X₂ ∩ X₂'}) = ∑_{p₁ + p₂ = p} C(p, p₁) χ_{p₁} χ'_{p₂}`

in `A^p(X₂ ∩ X₂' ⟶ X)`, with the product of `Stacks.Chow.supportedIntersectionMul`, each summand
read in degree `p`. -/
@[stacks 0FE5 "the formula P'_p((E tensor^L E')|_(X_2 cap X'_2)) = sum over p_1 + p_2 = p of C(p, \
p_1) chi_(p_1) chi'_(p_2) in A^p(X_2 cap X'_2 -> X), for every p >= 0, with E, E' perfect with \
defined Chern classes as in the source. The closed cover of X on which the left hand side is the \
class of 0F9H is X = Y cup (X_2 cap X'_2) with Y the reduced closed subscheme on |X_1| cup |X'_1| \
(reducedUnionIdeal); the vanishing of (E tensor^L E')|_(Y cap X_2 cap X'_2) that 0F9H needs is \
proved (isZero_derivedPullback_derivedTensor_reducedUnion, by derived Nakayama on the derived \
fibres), for E, E' perfect as in the source. The source's Y = (X_1 cap X'_1) cup (X_1 cap X'_2) \
cup (X_2 cap X'_1) has the same underlying set; by 0FAH the class does not depend on the choice. \
The product of a class on X_2 and a class on X'_2 is supportedIntersectionMul, res(c_1) o c_2 for \
the restriction of 0F9Z and the composition of 0B75"]
theorem closedCoverPowerSum_derivedTensor (perfectE : RingedSpace.IsPerfect.{u, u + 1} E)
    (perfectE' : RingedSpace.IsPerfect.{u, u + 1} E') (p : ℕ) :
    closedCoverPowerSum C sX (reducedUnionIdeal i₁ j₁).subschemeι (pullback.snd i₂ j₂ ≫ j₂) _ rfl
        ((hasDefinedChernClasses_derivedTensor hE hE').derivedPullback _) p
        (range_union_range_reducedUnionIdeal i₁ i₂ j₁ j₂ hcover hcover')
        (isZero_derivedPullback_derivedTensor_reducedUnion i₁ i₂ j₁ j₂ hzero hzero' perfectE
          perfectE') =
      ∑ q ∈ (antidiagonal p).attach, (p.choose q.1.1 : ℤ) •
        bivariantClassDegreeCongr C _ _ sX _ rfl
          (by have := mem_antidiagonal.1 q.2; omega)
          (supportedIntersectionMul C sX i₂ j₂ (IsPullback.of_hasPullback i₂ j₂) _ rfl
            (closedCoverPowerSumRestrict C sX i₁ i₂ hcover hE hzero q.1.1)
            (closedCoverPowerSumRestrict C sX j₁ j₂ hcover' hE' hzero' q.1.2)) :=
  closedCoverPowerSum_derivedTensor_of_closedCover C sX i₁ i₂ j₁ j₂ hcover hcover' hE hE' hzero
    hzero' _ _ _ p

/-- **Stacks 0FE5 for `c'_1`.** Let `X = X₁ ∪ X₂ = X₁' ∪ X₂'` be two closed
covers and let `E`, `E' ∈ D(𝒪_X)` be perfect objects whose Chern classes are defined and which
restrict to zero on `X₁` and `X₁'`. Write `r = P'_0(E|_{X₂})`,
`r' = P'_0(E'|_{X₂'})`, `γ_1 = c'_1(E|_{X₂})` and `γ'_1 = c'_1(E'|_{X₂'})` for the classes of
Stacks 0F9H. Let `Y ⊆ X` be the reduced closed subscheme with
underlying set `X₁ ∪ X₁'` (`Stacks.Chow.reducedUnionIdeal`); then `X = Y ∪ (X₂ ∩ X₂')`, and
`E ⊗^L E'` restricts to zero on `Y ∩ (X₂ ∩ X₂')`, so the class of Stacks 0F9H of
`(E ⊗^L E')|_{X₂ ∩ X₂'}` along `X = Y ∪ (X₂ ∩ X₂')` is defined; by Stacks 0FAH it does not
depend on the choice of `Y`. Then

  `c'_1((E ⊗^L E')|_{X₂ ∩ X₂'}) = r γ'_1 + r' γ_1`

in `A^1(X₂ ∩ X₂' ⟶ X)`, with the product of `Stacks.Chow.supportedIntersectionMul` (for `r' γ_1`
along the pullback square with the two factors exchanged), each summand read in degree `1`. -/
@[stacks 0FE5 "the formula c'_1((E tensor^L E')|_(X_2 cap X'_2)) = r gamma'_1 + r' gamma_1 in \
A^1(X_2 cap X'_2 -> X), with E, E' perfect with defined Chern classes as in the source. The closed \
cover of X on which the left hand side is the class of 0F9H is X = Y cup (X_2 cap X'_2) with Y the \
reduced closed subscheme on |X_1| cup |X'_1| (reducedUnionIdeal); the vanishing of (E tensor^L \
E')|_(Y cap X_2 cap X'_2) that 0F9H needs is proved \
(isZero_derivedPullback_derivedTensor_reducedUnion, by derived Nakayama on the derived fibres), \
for E, E' perfect as in the source. The source's Y = (X_1 cap X'_1) cup (X_1 cap X'_2) cup (X_2 \
cap X'_1) has the same underlying set; by 0FAH the class does not depend on the choice. Products \
are supportedIntersectionMul, res(c_1) o c_2, landing in the class group of X_2 x_X X'_2 -> X for \
both orders of the factors"]
theorem closedCoverChernClass_derivedTensor_one (perfectE : RingedSpace.IsPerfect.{u, u + 1} E)
    (perfectE' : RingedSpace.IsPerfect.{u, u + 1} E') :
    closedCoverChernClassOfIsZero C sX (reducedUnionIdeal i₁ j₁).subschemeι
        (pullback.snd i₂ j₂ ≫ j₂) _ rfl
        ((hasDefinedChernClasses_derivedTensor hE hE').derivedPullback _)
        (range_union_range_reducedUnionIdeal i₁ i₂ j₁ j₂ hcover hcover')
        (isZero_derivedPullback_derivedTensor_reducedUnion i₁ i₂ j₁ j₂ hzero hzero' perfectE
          perfectE') 1 one_pos =
      bivariantClassDegreeCongr C _ _ sX _ rfl (by norm_num)
          (supportedIntersectionMul C sX i₂ j₂ (IsPullback.of_hasPullback i₂ j₂) _ rfl
            (closedCoverPowerSumRestrict C sX i₁ i₂ hcover hE hzero 0)
            (closedCoverChernClassRestrict C sX j₁ j₂ hcover' hE' hzero' 1 one_pos)) +
        bivariantClassDegreeCongr C _ _ sX _ rfl (by norm_num)
          (supportedIntersectionMul C sX j₂ i₂ (IsPullback.of_hasPullback i₂ j₂).flip _
            pullback.condition
            (closedCoverPowerSumRestrict C sX j₁ j₂ hcover' hE' hzero' 0)
            (closedCoverChernClassRestrict C sX i₁ i₂ hcover hE hzero 1 one_pos)) :=
  closedCoverChernClass_derivedTensor_one_of_closedCover C sX i₁ i₂ j₁ j₂ hcover hcover' hE hE'
    hzero hzero' _ _ _

/-- **Stacks 0FE5 for `c'_2`.** Let `X = X₁ ∪ X₂ = X₁' ∪ X₂'` be two closed
covers and let `E`, `E' ∈ D(𝒪_X)` be perfect objects whose Chern classes are defined and which
restrict to zero on `X₁` and `X₁'`. Write `r = P'_0(E|_{X₂})`,
`r' = P'_0(E'|_{X₂'})`, `γ_p = c'_p(E|_{X₂})` and `γ'_p = c'_p(E'|_{X₂'})` for the classes of
Stacks 0F9H, and `C(r, 2)`, `C(r', 2)` for the classes `Stacks.Chow.closedCoverRankChoose`. Let
`Y ⊆ X` be the reduced closed subscheme with underlying set `X₁ ∪ X₁'`
(`Stacks.Chow.reducedUnionIdeal`); then `X = Y ∪ (X₂ ∩ X₂')`, and `E ⊗^L E'` restricts to zero
on `Y ∩ (X₂ ∩ X₂')`, so the class of Stacks 0F9H of `(E ⊗^L E')|_{X₂ ∩ X₂'}` along
`X = Y ∪ (X₂ ∩ X₂')` is defined; by Stacks 0FAH it does not depend on the choice of `Y`. Then

  `c'_2((E ⊗^L E')|_{X₂ ∩ X₂'}) =
    r γ'_2 + r' γ_2 + C(r, 2) (γ'_1)² + ((r r') (γ'_1 γ_1) - γ'_1 γ_1) + C(r', 2) γ_1²`

in `A^2(X₂ ∩ X₂' ⟶ X)`. The products of a class on `X₂` and a class on `X₂'` are those of
`Stacks.Chow.supportedIntersectionMul`, the squares `(γ'_1)²`, `γ_1²` and the product of `r r'`
with `γ'_1 γ_1` are the third multiplication of Stacks 0FA0 (`Stacks.Chow.supportedMul`), and each
summand is read in degree `2`. -/
@[stacks 0FE5 "the formula for c'_2((E tensor^L E')|_(X_2 cap X'_2)) in A^2(X_2 cap X'_2 -> X), \
with E, E' perfect with defined Chern classes as in the source. The closed cover of X on which the \
left hand side is the class of 0F9H is X = Y cup (X_2 cap X'_2) with Y the reduced closed \
subscheme on |X_1| cup |X'_1| (reducedUnionIdeal); the vanishing of (E tensor^L E')|_(Y cap X_2 \
cap X'_2) that 0F9H needs is proved (isZero_derivedPullback_derivedTensor_reducedUnion, by derived \
Nakayama on the derived fibres), for E, E' perfect as in the source. The source's Y = (X_1 cap \
X'_1) cup (X_1 cap X'_2) cup (X_2 cap X'_1) has the same underlying set; by 0FAH the class does \
not depend on the choice. C(r, 2) is read as closedCoverRankChoose: the 0F9H extension of the \
restriction to X_2 of the class ofLocallyConstant of x |-> C(chi_E(x), 2), chi_E the derived-fibre \
Euler characteristic whose class is r(E) = P_0(E), exactly as 0FAG reads C(r(E), 2); it vanishes \
on X_1 because chi_E does, and C(r, 1) = r. The term (r r' - 1) gamma'_1 gamma_1 is read as (r \
r')(gamma'_1 gamma_1) - gamma'_1 gamma_1, since 1 is not a class supported on X_2 cap X'_2; \
products of classes supported on X_2 and X'_2 are supportedIntersectionMul, products of classes on \
one support are supportedMul (0FA0). The source's 'and so on for higher Chern classes' is not a \
precise assertion and is not formalized"]
theorem closedCoverChernClass_derivedTensor_two (perfectE : RingedSpace.IsPerfect.{u, u + 1} E)
    (perfectE' : RingedSpace.IsPerfect.{u, u + 1} E') :
    closedCoverChernClassOfIsZero C sX (reducedUnionIdeal i₁ j₁).subschemeι
        (pullback.snd i₂ j₂ ≫ j₂) _ rfl
        ((hasDefinedChernClasses_derivedTensor hE hE').derivedPullback _)
        (range_union_range_reducedUnionIdeal i₁ i₂ j₁ j₂ hcover hcover')
        (isZero_derivedPullback_derivedTensor_reducedUnion i₁ i₂ j₁ j₂ hzero hzero' perfectE
          perfectE') 2 two_pos =
      (bivariantClassDegreeCongr C _ _ sX _ rfl (by norm_num)
          (supportedIntersectionMul C sX i₂ j₂ (IsPullback.of_hasPullback i₂ j₂) _ rfl
            (closedCoverPowerSumRestrict C sX i₁ i₂ hcover hE hzero 0)
            (closedCoverChernClassRestrict C sX j₁ j₂ hcover' hE' hzero' 2 two_pos)) +
        bivariantClassDegreeCongr C _ _ sX _ rfl (by norm_num)
          (supportedIntersectionMul C sX j₂ i₂ (IsPullback.of_hasPullback i₂ j₂).flip _
            pullback.condition
            (closedCoverPowerSumRestrict C sX j₁ j₂ hcover' hE' hzero' 0)
            (closedCoverChernClassRestrict C sX i₁ i₂ hcover hE hzero 2 two_pos)) +
        bivariantClassDegreeCongr C _ _ sX _ rfl (by norm_num)
          (supportedIntersectionMul C sX i₂ j₂ (IsPullback.of_hasPullback i₂ j₂) _ rfl
            (closedCoverRankChoose C sX i₁ i₂ perfectE hcover hzero 2 two_pos)
            (supportedMul C (j₂ ≫ sX) sX j₂ rfl
              (closedCoverChernClassRestrict C sX j₁ j₂ hcover' hE' hzero' 1 one_pos)
              (closedCoverChernClassRestrict C sX j₁ j₂ hcover' hE' hzero' 1 one_pos))) +
        (bivariantClassDegreeCongr C _ _ sX _ rfl (by norm_num)
            (supportedMul C ((pullback.snd i₂ j₂ ≫ j₂) ≫ sX) sX (pullback.snd i₂ j₂ ≫ j₂) rfl
              (supportedIntersectionMul C sX i₂ j₂ (IsPullback.of_hasPullback i₂ j₂) _ rfl
                (closedCoverPowerSumRestrict C sX i₁ i₂ hcover hE hzero 0)
                (closedCoverPowerSumRestrict C sX j₁ j₂ hcover' hE' hzero' 0))
              (supportedIntersectionMul C sX j₂ i₂ (IsPullback.of_hasPullback i₂ j₂).flip _
                pullback.condition
                (closedCoverChernClassRestrict C sX j₁ j₂ hcover' hE' hzero' 1 one_pos)
                (closedCoverChernClassRestrict C sX i₁ i₂ hcover hE hzero 1 one_pos))) -
          bivariantClassDegreeCongr C _ _ sX _ rfl (by norm_num)
            (supportedIntersectionMul C sX j₂ i₂ (IsPullback.of_hasPullback i₂ j₂).flip _
              pullback.condition
              (closedCoverChernClassRestrict C sX j₁ j₂ hcover' hE' hzero' 1 one_pos)
              (closedCoverChernClassRestrict C sX i₁ i₂ hcover hE hzero 1 one_pos))) +
        bivariantClassDegreeCongr C _ _ sX _ rfl (by norm_num)
          (supportedIntersectionMul C sX j₂ i₂ (IsPullback.of_hasPullback i₂ j₂).flip _
            pullback.condition
            (closedCoverRankChoose C sX j₁ j₂ perfectE' hcover' hzero' 2 two_pos)
            (supportedMul C (i₂ ≫ sX) sX i₂ rfl
              (closedCoverChernClassRestrict C sX i₁ i₂ hcover hE hzero 1 one_pos)
              (closedCoverChernClassRestrict C sX i₁ i₂ hcover hE hzero 1 one_pos)))) :=
  closedCoverChernClass_derivedTensor_two_of_closedCover C sX i₁ i₂ j₁ j₂ hcover hcover' hE hE'
    hzero hzero' perfectE perfectE' _ _ _

end TensorProduct

end Stacks.Chow

end
