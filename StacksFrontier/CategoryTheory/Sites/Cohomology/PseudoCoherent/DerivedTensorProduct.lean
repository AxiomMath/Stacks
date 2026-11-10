module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPushforwardModules.HasSheafComposeForget
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSite
public import StacksFrontier.Algebra.Homology.DerivedCategory.TriangleApproximation
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.BoundedAbovePreservation
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.BoundedAbove
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.ExistenceOnARingedSite
public import StacksFrontier.CategoryTheory.Sites.Cohomology.KFlat.BoundedAboveFlatComplexes
public import StacksFrontier.CategoryTheory.Sites.Cohomology.KFlat.ResolutionsOnARingedSite
public import StacksFrontier.CategoryTheory.Sites.Cohomology.KFlat.RestrictionToSlice
public import StacksFrontier.CategoryTheory.Sites.Localization.RingedSiteLocalization
public import StacksFrontier.CategoryTheory.Sites.Cohomology.PseudoCoherent.DerivedApproximationOnASlice
public import StacksFrontier.CategoryTheory.Sites.Cohomology.PseudoCoherent.Representatives
public import StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.FlatnessOfFiniteFreeSummands
public import StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.TensorOfStrictlyPerfectComplexes
public import StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.TruncatingApproximations
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TensorComplex.Restriction
import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPushforwardModules.HasSheafComposeForget

/-!
# Pseudo-coherence of the derived tensor product on a ringed site

Let `(C, O)` be a ringed site and let `K`, `L` be objects of `D(O)`. If `K` is
`n`-pseudo-coherent with `H^i(K) = 0` for `i > a` and `L` is `m`-pseudo-coherent with
`H^j(L) = 0` for `j > b`, then `K ⊗^{𝐋}_O L` is `t`-pseudo-coherent for
`t = max (m + a) (n + b)`; and if `K` and `L` are pseudo-coherent then so is `K ⊗^{𝐋}_O L`.

The argument is the source's. Both factors are replaced by complexes with flat terms whose
restriction to every slice of the site is again K-flat, so that the total tensor complex of the
two representatives represents `K ⊗^{𝐋} L`; pseudo-coherence passes to those representatives.
Over an object of the site carrying a strictly perfect approximation of each factor — of the
first in degree `n`, of the second in degree `m` — the total tensor complex of the two
approximations is strictly perfect (Stacks 09J8) and the derived tensor product of the two
approximations is an approximation in degree `t`. The source asserts that last step as a
consequence of "the spectral sequence of tors (details omitted)"; it is proved here instead from
right t-exactness of the derived tensor product, by factoring `α ⊗^{𝐋} β` through
`𝒫 ⊗^{𝐋} ℬ` and shifting the degree of each of the two legs by the cohomological bound of the
factor that stays fixed. Stacks 08FU assembles the local approximations.

## Main results

* `Stacks.SheafOfModules.DerivedTensorProduct.isPseudoCoherentFrom_derivedTensorProduct`:
  part (1), the quantitative statement, for the derived tensor product
  `Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor` of Stacks 06YU.
* `Stacks.SheafOfModules.DerivedTensorProduct.isPseudoCoherent_derivedTensorProduct`: part (2),
  preservation of pseudo-coherence, for the same derived tensor product.
* `Stacks.SheafOfModules.DerivedTensorProduct.isPseudoCoherentFrom_tensor` and
  `Stacks.SheafOfModules.DerivedTensorProduct.isPseudoCoherent_tensor`: the same two statements
  for any `Stacks.DerivedTensor.RingedSite.DerivedTensorProduct`; the two above are their
  instances at `Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct`, whose existence
  is Stacks 06YU.

## Implementation notes

**The degree estimate is derived-categorical.** The local step is
`Stacks.SheafOfModules.DerivedTensorProduct.exists_approximation_derivedTensor`, which needs no
spectral sequence: the cocone triangle of an approximation in degree `s` has third vertex in
`D^{≤ s - 1}`, tensoring with an object of `D^{≤ e}` keeps it in `D^{≤ s + e - 1}` by
`Stacks.DerivedTensor.RingedSite.isLE_derivedTensorProduct`, and reading that dictionary
backwards — `StacksFrontier.Algebra.Homology.DerivedCategory.TriangleApproximation` — returns an
approximation in degree `s + e`. Exactness of the derived tensor product in
each variable separately, the `exact_left` and `exact_right` fields of
`Stacks.DerivedTensor.RingedSite.DerivedTensorProduct`, is what makes the two legs available
without a symmetry constraint. Since `t = max (m + a) (n + b)` dominates both `m + a` and
`n + b`, and `t`-pseudo-coherence weakens as `t` grows, the two legs compose.

**Why part (2) is not part (1) at `t = q`.** A pseudo-coherent object of `D(O)` need not be
bounded above globally, so part (1) does not apply to it directly; the source restricts to a
covering on which both factors are bounded above. Here the bounds are produced on the covering
itself: a strictly perfect approximation in degree `0` over an object of the site has only
finitely many nonzero terms, which bounds the cohomology of the factor there, and the two
thresholds are then chosen as `n = min (q - b) a` and `m = min (q - a) b`, which makes
`max (m + a) (n + b) ≤ q`.

**The local data is kept in the derived category.** The approximations that pseudo-coherence
supplies are morphisms of complexes, but the one this file produces over an object of the site
is only a morphism of the derived category, since it is assembled from the derived tensor
product of the slice. Both are recorded by the single predicate
`Stacks.SheafOfModules.DerivedTensorProduct.HasApprox`, which descends along an arrow of the
site because restriction between slices is exact; that descent is what lets the covering
produced by the first factor and the one produced by the second be intersected. Passing from a
derived approximation on a covering back to the chain-level approximations the definition of
pseudo-coherence asks for is
`AlgebraicGeometry.RingedSite.exists_coveringSieve_approximation_of_derived`, and the covering
of an object is obtained from it by `CategoryTheory.Sieve.bind`.

**The universes are the diagonal `RingedSite.{0, 0, 0}`,** which is forced and not chosen. The
pseudo-coherence family of Stacks 08FT and 08FU is available only for sections of the structure
sheaf in `Type 0`, while right t-exactness of the derived tensor product
(`Stacks.DerivedTensor.RingedSite.isLE_derivedTensorProduct`) is available only for a small site
with the sections in the same universe as the objects and the morphisms. Together these force
all three universes to be `0`. Neither restriction originates here: the prerequisites of this
file, the total tensor complex of two strictly perfect complexes (Stacks 09J8) and the
commutation of restriction to a slice with the total tensor complex, hold at three free and
independent universes.

**K-flatness of the restrictions.** The comparison of the derived tensor product with the total
tensor complex is applied on the slice at an object of the site, so the representatives are
required to restrict to K-flat complexes there. For a representative which is bounded above
that is Stacks 06YQ on the slice, and for an arbitrary one it is the transport of the colimit
presentation of the resolution of Stacks 06YS, which is
`kFlat_restrictionComplex_of_isColimit` below. The latter is
`Stacks.SheafOfModules.KFlatRestriction.kFlat_restriction_of_isColimit` with the hypothesis
that the site have binary products dropped, which its own proof does not use.

## References

* [Stacks Project, Tag 06YQ](https://stacks.math.columbia.edu/tag/06YQ)
* [Stacks Project, Tag 06YS](https://stacks.math.columbia.edu/tag/06YS)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
* [Stacks Project, Tag 08FT](https://stacks.math.columbia.edu/tag/08FT)
* [Stacks Project, Tag 08FU](https://stacks.math.columbia.edu/tag/08FU)
* [Stacks Project, Tag 09J8](https://stacks.math.columbia.edu/tag/09J8)
* [Stacks Project, Lemma 21.44.6 (Tag 09J9)](https://stacks.math.columbia.edu/tag/09J9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated AlgebraicGeometry
open Stacks.SheafOfModules.Tensor
open scoped ZeroObject

namespace Stacks.SheafOfModules.DerivedTensorProduct

universe u d

/-! ### The derived-categorical core -/

section Core

variable {C : Type u} [SmallCategory.{u} C] {J : GrothendieckTopology C}
  (R : Sheaf J CommRingCat.{u})
  [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(sheafTensor.{u, u, u, u, u} R).Additive] [∀ M, ((sheafTensor.{u, u, u, u, u} R).obj M).Additive]
  [∀ (K₁ K₂ : CochainComplex (Stacks.DerivedTensor.RingedSite.Modules R) ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (sheafTensor.{u, u, u, u, u} R) (ComplexShape.up ℤ)]
  [HasDerivedCategory.{d} (Stacks.DerivedTensor.RingedSite.Modules R)]

/-- **The derived-categorical heart of Stacks 09J9 part (1).** Let `α : 𝒫 ⟶ 𝒜` and `β : 𝒬 ⟶ ℬ`
be morphisms of `D(O)` with `𝒜 ∈ D^{≤ a}` and `ℬ ∈ D^{≤ b}`, with `α` an approximation in
degree `n ≤ a` and `β` one in degree `m`. Then `𝒫 ⊗^{𝐋} 𝒬 ⟶ 𝒜 ⊗^{𝐋} ℬ` is an approximation
in degree `t = max (m + a) (n + b)`.

The morphism is factored as `𝒫 ⊗^{𝐋} 𝒬 ⟶ 𝒫 ⊗^{𝐋} ℬ ⟶ 𝒜 ⊗^{𝐋} ℬ`. The first leg is `β`
tensored with `𝒫`, which lies in `D^{≤ a}(O)` because `α` is an isomorphism on cohomology
above `n ≤ a` and `𝒜 ∈ D^{≤ a}`; the second is `α` tensored with `ℬ ∈ D^{≤ b}`. Right
t-exactness of the derived tensor product in each variable shifts the degree of each
approximation by the bound of the fixed factor, giving `m + a` and `n + b`; both are at most
`t`, so both legs are isomorphisms on cohomology above `t` and surjections in degree `t`, and
so is their composite. -/
private theorem exists_approximation_derivedTensor
    (T : Stacks.DerivedTensor.RingedSite.DerivedTensorProduct R)
    (P Q A B : Stacks.DerivedTensor.RingedSite.DerivedModules R)
    (n m a b : ℤ) (hna : n ≤ a) (hA : A.IsLE a) (hB : B.IsLE b)
    (α : P ⟶ A)
    (hαiso : ∀ j : ℤ, n < j →
      IsIso ((DerivedCategory.homologyFunctor _ j).map α))
    (hαepi : Epi ((DerivedCategory.homologyFunctor _ n).map α))
    (β : Q ⟶ B)
    (hβiso : ∀ j : ℤ, m < j →
      IsIso ((DerivedCategory.homologyFunctor _ j).map β))
    (hβepi : Epi ((DerivedCategory.homologyFunctor _ m).map β)) :
    ∃ γ : (T.tensor.obj P).obj Q ⟶ (T.tensor.obj A).obj B,
      (∀ j : ℤ, max (m + a) (n + b) < j →
          IsIso ((DerivedCategory.homologyFunctor _ j).map γ)) ∧
        Epi ((DerivedCategory.homologyFunctor _ (max (m + a) (n + b))).map γ) := by
  have hP : P.IsLE a := by
    rw [DerivedCategory.isLE_iff]
    intro j hj
    have := hαiso j (by omega)
    exact (DerivedCategory.isZero_of_isLE A a j hj).of_iso
      (asIso ((DerivedCategory.homologyFunctor _ j).map α))
  let csP : (T.tensor.obj P).CommShift ℤ := T.commShift_right P
  have exP : (T.tensor.obj P).IsTriangulated := T.exact_right P
  let csB : (T.tensor.flip.obj B).CommShift ℤ := T.commShift_left B
  have exB : (T.tensor.flip.obj B).IsTriangulated := T.exact_left B
  have hleg1 := DerivedCategory.approximation_of_isLE_functor (T.tensor.obj P) a
    (fun Z c _ => by
      have h := Stacks.DerivedTensor.RingedSite.isLE_derivedTensorProduct R T P Z a c
      exact DerivedCategory.TStructure.t.isLE_of_le _ (a + c) (c + a) (by omega))
    β m hβiso hβepi
  have hleg2 := DerivedCategory.approximation_of_isLE_functor (T.tensor.flip.obj B) b
    (fun Z c _ => Stacks.DerivedTensor.RingedSite.isLE_derivedTensorProduct R T Z B c b)
    α n hαiso hαepi
  refine ⟨(T.tensor.obj P).map β ≫ (T.tensor.flip.obj B).map α, ?_, ?_⟩
  · intro j hj
    have h1 := hleg1.1 j (by omega)
    have h2 := hleg2.1 j (by omega)
    rw [Functor.map_comp]
    infer_instance
  · have h1 := DerivedCategory.epi_homologyMap_of_le _ (m + a) (max (m + a) (n + b))
      (le_max_left _ _) hleg1.1 hleg1.2
    have h2 := DerivedCategory.epi_homologyMap_of_le _ (n + b) (max (m + a) (n + b))
      (le_max_right _ _) hleg2.1 hleg2.2
    rw [Functor.map_comp]
    infer_instance

omit [HasSheafify J AddCommGrpCat.{u}] [(sheafTensor.{u, u, u, u, u} R).Additive]
  [∀ M, ((sheafTensor.{u, u, u, u, u} R).obj M).Additive]
  [∀ (K₁ K₂ : CochainComplex (Stacks.DerivedTensor.RingedSite.Modules R) ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (sheafTensor.{u, u, u, u, u} R) (ComplexShape.up ℤ)]
  [HasDerivedCategory.{d} (Stacks.DerivedTensor.RingedSite.Modules R)] in
/-- **The restriction of a sequential colimit of bounded above complexes of flat `O`-modules to
a slice is K-flat**: restriction commutes with the colimit degreewise, and each stage restricts
to a bounded above complex of flat `O|_U`-modules.

This is `Stacks.SheafOfModules.KFlatRestriction.kFlat_restriction_of_isColimit` without the
hypothesis that the site have binary products. That hypothesis enters there only through the
left adjoint of restriction, which exists on a site with binary products; the preservation of
the colimit needed here follows instead from the cocontinuity of the forgetful functor of the
slice, which is `Stacks.SheafOfModules.pushforward_preservesColimits`. -/
private theorem kFlat_restrictionComplex_of_isColimit (U : C)
    [HasWeakSheafify J AddCommGrpCat.{u}]
    [HasSheafify (J.over U) AddCommGrpCat.{u}]
    [HasWeakSheafify (J.over U) AddCommGrpCat.{u}]
    [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}]
    (D : ℕ ⥤ CochainComplex (Stacks.DerivedTensor.RingedSite.Modules R) ℤ)
    (c : Cocone D) (hc : IsColimit c)
    (hLE : ∀ n : ℕ, ∃ b : ℤ, (D.obj n).IsStrictlyLE b)
    (hflat : ∀ (n : ℕ) (i : ℤ), AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := R)
      ((D.obj n).X i)) :
    CochainComplex.KFlatBifunctor.KFlat (sheafTensor.{u, u, u, u, u} (R.over U))
      (Stacks.SheafOfModules.KFlatRestriction.restrictionComplex R U c.pt) := by
  have h₀ : PreservesColimitsOfSize.{u, u}
      (Stacks.SheafOfModules.KFlatRestriction.restriction R U) :=
    Stacks.SheafOfModules.pushforward_preservesColimits (J := J.over U) (K := J)
      (Over.forget U) (𝟙 ((Tensor.ringSheaf R).over U))
  have h₁ : PreservesColimitsOfSize.{0, 0}
      (Stacks.SheafOfModules.KFlatRestriction.restriction R U) :=
    preservesColimitsOfSize_shrink _
  have hp := CochainComplex.KFlat.preservesColimit_mapHomologicalComplex D
    (Stacks.SheafOfModules.KFlatRestriction.restriction R U)
  refine CochainComplex.KFlatBifunctor.kFlat_of_isColimit (sheafTensor.{u, u, u, u, u} (R.over U))
    ((Stacks.SheafOfModules.KFlatRestriction.restrictionComplexFunctor R U).mapCocone c)
    (hp.preserves hc).some
    (Stacks.SheafOfModules.KFlatResolution.hF_sheafTensor (R.over U))
    (Stacks.SheafOfModules.KFlatResolution.hexact_sheafOfModules (R.over U)) fun n ↦ ?_
  obtain ⟨b, hb⟩ := hLE n
  have := hb
  exact Stacks.SheafOfModules.KFlatRestriction.kFlat_restriction_of_isStrictlyLE R U
    (D.obj n) b (hflat n)

end Core

/-! ### Local approximations on a ringed site -/

section Site

attribute [local instance] Stacks.hasSheafCompose_forget₂_commRingCat
attribute [local instance] HasDerivedCategory.standard

variable (X : RingedSite.{0, 0, 0})
variable [HasSheafify X.J AddCommGrpCat.{0}]
variable [X.J.WEqualsLocallyBijective AddCommGrpCat.{0}]
variable [∀ U : X.C, HasSheafify (X.J.over U) AddCommGrpCat.{0}]
variable [∀ U : X.C, (X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{0}]

/-- Restriction of sheaves of modules to the slice over `U` preserves finite limits. -/
local instance pcTensorOverFunctorLimits (U : X.C) :
    PreservesFiniteLimits
      (_root_.SheafOfModules.overFunctor.{0} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U) :=
  Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteLimits U

/-- Restriction of sheaves of modules to the slice over `U` preserves finite colimits. -/
local instance pcTensorOverFunctorColimits (U : X.C) :
    PreservesFiniteColimits
      (_root_.SheafOfModules.overFunctor.{0} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U) :=
  Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteColimits U

/-- Restriction of sheaves of modules along `g : V ⟶ U` between slices preserves finite limits. -/
local instance pcTensorOverMapLimits {U V : X.C} (g : V ⟶ U) :
    PreservesFiniteLimits
      (_root_.SheafOfModules.overMap.{0} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) g) :=
  Stacks.SheafOfModules.LocalCokernel.overMap_preservesFiniteLimits g

/-- Restriction of sheaves of modules along `g : V ⟶ U` between slices preserves finite
colimits. -/
local instance pcTensorOverMapColimits {U V : X.C} (g : V ⟶ U) :
    PreservesFiniteColimits
      (_root_.SheafOfModules.overMap.{0} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) g) :=
  Stacks.SheafOfModules.LocalCokernel.overMap_preservesFiniteColimits g

omit [HasSheafify X.J AddCommGrpCat.{0}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{0}] in
/-- A strictly perfect complex of `O|_V`-modules has no terms above some degree. -/
private theorem exists_isZero_X_of_lt (V : X.C)
    {P : CochainComplex
      (_root_.SheafOfModules.{0} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over V)) ℤ}
    (hP : IsStrictlyPerfect ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over V) P) :
    ∃ r : ℤ, ∀ i : ℤ, r < i → IsZero (P.X i) := by
  obtain ⟨r, hr⟩ := hP.bounded.bddAbove
  refine ⟨r, fun i hi => ?_⟩
  by_contra h
  exact absurd (hr (by simpa only [Set.mem_ofPred_eq] using h)) (by omega)

omit [HasSheafify X.J AddCommGrpCat.{0}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{0}] in
/-- A bound on the cohomology of the restriction of a complex to a slice descends along an
arrow of the site, restriction between slices being exact. -/
private theorem isLE_restrictComplex_of_hom
    (K : CochainComplex (_root_.SheafOfModules.{0} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    {V W : X.C} (g : W ⟶ V)
    (a : ℤ) (h : (DerivedCategory.Q.obj (X.restrictComplex K V)).IsLE a) :
    (DerivedCategory.Q.obj (X.restrictComplex K W)).IsLE a := by
  have := h
  have := Stacks.Homology.isLE_mapDerivedCategory_obj
    (_root_.SheafOfModules.overMap.{0} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) g)
    (DerivedCategory.Q.obj (X.restrictComplex K V)) a
  exact DerivedCategory.TStructure.t.isLE_of_iso (RingedSite.restrictComplexOverMapIso X K g) a

/-- A bound on the cohomology of a complex of `O`-modules bounds that of its restriction to any
slice, restriction being exact. -/
private theorem isLE_restrictComplex
    (K : CochainComplex (_root_.SheafOfModules.{0} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (V : X.C) (a : ℤ)
    (h : (DerivedCategory.Q.obj K).IsLE a) :
    (DerivedCategory.Q.obj (X.restrictComplex K V)).IsLE a := by
  have := h
  have := Stacks.Homology.isLE_mapDerivedCategory_obj
    (_root_.SheafOfModules.overFunctor.{0} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) V)
    (DerivedCategory.Q.obj K) a
  have e : (_root_.SheafOfModules.overFunctor.{0}
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O) V).mapDerivedCategory.obj
      (DerivedCategory.Q.obj K) ≅ DerivedCategory.Q.obj (X.restrictComplex K V) :=
    (_root_.SheafOfModules.overFunctor.{0}
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O) V).mapDerivedCategoryFactors.app K
  exact DerivedCategory.TStructure.t.isLE_of_iso e a

/-- The local datum carried by an object `V` of the site: a strictly perfect complex of
`O|_V`-modules which approximates `K|_V` in degrees `> t` in the derived category of the slice.

The approximations that pseudo-coherence supplies are morphisms of complexes, and this is
weaker; the one produced by the derived tensor product of two approximations is of this kind
only. -/
private def HasApprox
    (K : CochainComplex (_root_.SheafOfModules.{0} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (t : ℤ) (V : X.C) : Prop :=
  ∃ P : CochainComplex
      (_root_.SheafOfModules.{0} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over V)) ℤ,
    IsStrictlyPerfect ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over V) P ∧
    ∃ β : DerivedCategory.Q.obj P ⟶ DerivedCategory.Q.obj (X.restrictComplex K V),
      (∀ j : ℤ, t < j → IsIso ((DerivedCategory.homologyFunctor _ j).map β)) ∧
        Epi ((DerivedCategory.homologyFunctor _ t).map β)

omit [HasSheafify X.J AddCommGrpCat.{0}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{0}] in
/-- **A chain-level strictly perfect approximation descends along an arrow of the site.**
Restriction to a smaller slice is exact, so it preserves strict perfectness and both
cohomological conditions, and it carries a complex representative of a restriction to a complex
representative of the smaller restriction. -/
private theorem hasApprox_of_arrow
    (K : CochainComplex (_root_.SheafOfModules.{0} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (t : ℤ) {V W : X.C} (g : W ⟶ V)
    (h : ∃ P : CochainComplex
        (_root_.SheafOfModules.{0} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over V)) ℤ,
      IsStrictlyPerfect ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over V) P ∧
      ∃ α : P ⟶ X.restrictComplex K V,
        (∀ j : ℤ, t < j → IsIso (HomologicalComplex.homologyMap α j)) ∧
        Epi (HomologicalComplex.homologyMap α t)) :
    HasApprox X K t W := by
  obtain ⟨P, hP, α, hα⟩ := h
  have hα := Stacks.Cohomology.DerivedPullbackOnRingedTopoi.approximation_Q_map α t hα.1 hα.2
  have := Stacks.SheafOfModules.LocalCokernel.overMap_preservesEpimorphisms
    (R := (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) g
  set F := (_root_.SheafOfModules.overMap.{0}
    (Stacks.SheafOfModules.Tensor.ringSheaf X.O) g).mapDerivedCategory with hF
  have hFiso := Stacks.Cohomology.DerivedPullbackOnRingedTopoi.map_approximation_of_isLE F
    (fun Z n hZ => have := hZ
      Stacks.Homology.isLE_mapDerivedCategory_obj
        (_root_.SheafOfModules.overMap.{0} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) g) Z n)
    (DerivedCategory.Q.map α) t hα.1 hα.2
  refine ⟨(AlgebraicGeometry.RingedSite.restrictCochainAlong X g).obj P,
    Stacks.SheafOfModules.isStrictlyPerfect_restrictComplexAlong
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O) g hP,
    ((_root_.SheafOfModules.overMap.{0} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) g
      ).mapDerivedCategoryFactors.app P).inv ≫
      F.map (DerivedCategory.Q.map α) ≫ (RingedSite.restrictComplexOverMapIso X K g).hom, ?_, ?_⟩
  · intro j hj
    have := hFiso.1 j hj
    have h₁ := ((_root_.SheafOfModules.overMap.{0} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) g
      ).mapDerivedCategoryFactors.app P).isIso_inv
    have h₂ := (RingedSite.restrictComplexOverMapIso X K g).isIso_hom
    rw [Functor.map_comp, Functor.map_comp]
    infer_instance
  · have := hFiso.2
    have h₂ := (RingedSite.restrictComplexOverMapIso X K g).isIso_hom
    rw [Functor.map_comp, Functor.map_comp]
    exact epi_comp' (IsIso.epi_of_iso _) (epi_comp' hFiso.2 (IsIso.epi_of_iso _))

omit [HasSheafify X.J AddCommGrpCat.{0}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{0}] in
/-- A pseudo-coherent complex has derived strictly perfect approximations in degree `t` over every
member of a covering sieve of each object. -/
private theorem exists_covering_hasApprox
    (K : CochainComplex (_root_.SheafOfModules.{0} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (t : ℤ) (hK : X.IsPseudoCoherentComplexFrom K t) (U : X.C) :
    ∃ S : Sieve U, S ∈ X.J U ∧ ∀ ⦃V : X.C⦄ (g : V ⟶ U), S g → HasApprox X K t V := by
  obtain ⟨S, hS, hd⟩ := hK U
  exact ⟨Sieve.generate S, hS, by
    rintro V g ⟨V₁, u, f, hf, rfl⟩
    exact hasApprox_of_arrow X K t u (hd f hf)⟩

omit [HasSheafify X.J AddCommGrpCat.{0}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{0}] in
/-- A derived approximation in degree `t` is in particular one in any degree `q ≥ t`. -/
private theorem HasApprox.mono
    {K : CochainComplex (_root_.SheafOfModules.{0} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    {t q : ℤ} {V : X.C}
    (h : HasApprox X K t V) (htq : t ≤ q) : HasApprox X K q V := by
  obtain ⟨P, hP, β, hiso, hepi⟩ := h
  exact ⟨P, hP, β, fun j hj => hiso j (by omega),
    DerivedCategory.epi_homologyMap_of_le β t q htq hiso hepi⟩

/-- If a property of objects of the site holds on a covering of each member of a covering sieve,
it holds on a covering of the object. -/
private theorem exists_covering_of_locally {D : Type*} [Category D] (J : GrothendieckTopology D)
    {U : D} (S : Sieve U) (hS : S ∈ J U) (p : D → Prop)
    (h : ∀ ⦃V : D⦄ (g : V ⟶ U), S g → ∃ T : Sieve V, T ∈ J V ∧ ∀ ⦃W : D⦄ (b : W ⟶ V),
      T b → p W) :
    ∃ S' : Sieve U, S' ∈ J U ∧ ∀ ⦃W : D⦄ (b : W ⟶ U), S' b → p W := by
  choose T hT hp using h
  refine ⟨Sieve.bind S T, J.bind_covering hS hT, ?_⟩
  rintro W b ⟨V, g, g', hg', hg, rfl⟩
  exact hp g' hg' g hg

/-- **Derived strictly perfect approximations on a covering of every object make an object of
`D(O)` `t`-pseudo-coherent.** The covering of an object `U` that the definition of
`t`-pseudo-coherence asks for is obtained by binding the given covering of `U` with the
coverings that
`AlgebraicGeometry.RingedSite.exists_coveringSieve_approximation_of_derived` produces over its
members, which is covering by transitivity. -/
private theorem isPseudoCoherentFrom_of_locally_hasApprox
    (E : DerivedCategory (_root_.SheafOfModules.{0} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (t : ℤ)
    (K : CochainComplex (_root_.SheafOfModules.{0} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (e : DerivedCategory.Q.obj K ≅ E)
    (h : ∀ U : X.C, ∃ S : Sieve U, S ∈ X.J U ∧
      ∀ ⦃V : X.C⦄ (g : V ⟶ U), S g → HasApprox X K t V) :
    X.IsPseudoCoherentFrom E t := by
  refine ⟨K, fun U => ?_, ⟨e⟩⟩
  obtain ⟨S₀, hS₀, hdata⟩ := h U
  obtain ⟨S, hS, hp⟩ := exists_covering_of_locally X.J S₀ hS₀
    (fun W => ∃ P' : CochainComplex
      (_root_.SheafOfModules.{0} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over W)) ℤ,
      IsStrictlyPerfect ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over W) P' ∧
      ∃ α' : P' ⟶ X.restrictComplex K W,
        (∀ j : ℤ, t < j → IsIso (HomologicalComplex.homologyMap α' j)) ∧
        Epi (HomologicalComplex.homologyMap α' t)) fun V g hg => by
    obtain ⟨P, hP, β, hiso, hepi⟩ := hdata g hg
    exact X.exists_coveringSieve_approximation_of_derived V K t P hP β hiso hepi
  exact ⟨S.arrows, by rw [Sieve.generate_sieve]; exact hS, fun W b hb => hp b hb⟩

omit [HasSheafify X.J AddCommGrpCat.{0}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{0}] in
/-- The zero complex of `O|_V`-modules is strictly perfect: it has no nonzero terms, and a zero
module is a direct summand of a finite free module. -/
private theorem isStrictlyPerfect_zero (V : X.C) :
    IsStrictlyPerfect ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over V)
      (0 : CochainComplex
        (_root_.SheafOfModules.{0} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over V)) ℤ) := by
  have hzero : IsZero (0 : CochainComplex (_root_.SheafOfModules.{0}
      ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over V)) ℤ) := isZero_zero _
  have hX (i : ℤ) : IsZero
      ((0 : CochainComplex
        (_root_.SheafOfModules.{0} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over V)) ℤ).X i) :=
    (HomologicalComplex.eval _ (ComplexShape.up ℤ) i).map_isZero hzero
  refine ⟨Set.finite_empty.subset ?_, fun i => ?_⟩
  · intro i hi
    simp only [Set.mem_ofPred_eq] at hi
    exact False.elim (hi (hX i))
  · exact _root_.IsDirectSummandOfFiniteFree.of_isZero
      ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over V) (hX i)

/-- **An object of `D(O)` whose cohomology vanishes in every degree at least `t` is
`t`-pseudo-coherent**: the zero complex is strictly perfect over every object of the site and
the zero map out of it is an approximation in degree `t`, restriction being exact. -/
private theorem isPseudoCoherentFrom_of_isLE
    (E : DerivedCategory (_root_.SheafOfModules.{0} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (t : ℤ) (hE : E.IsLE (t - 1)) : X.IsPseudoCoherentFrom E t := by
  classical
  have := hE
  set K := DerivedCategory.Q.objPreimage E with hKdef
  have e : DerivedCategory.Q.obj K ≅ E := DerivedCategory.Q.objObjPreimageIso E
  have hQK : (DerivedCategory.Q.obj K).IsLE (t - 1) :=
    DerivedCategory.TStructure.t.isLE_of_iso e.symm (t - 1)
  refine X.isPseudoCoherentFrom_of_derived_approximation E t K e fun V => ?_
  have hV : (DerivedCategory.Q.obj (X.restrictComplex K V)).IsLE (t - 1) :=
    isLE_restrictComplex X K V (t - 1) hQK
  have hzero : IsZero (0 : CochainComplex (_root_.SheafOfModules.{0}
      ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over V)) ℤ) := isZero_zero _
  have hsrc (j : ℤ) : IsZero ((DerivedCategory.homologyFunctor _ j).obj
      (DerivedCategory.Q.obj (0 : CochainComplex
        (_root_.SheafOfModules.{0} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over V)) ℤ))) :=
    (DerivedCategory.homologyFunctor _ j).map_isZero (DerivedCategory.Q.map_isZero hzero)
  have htgt : ∀ j : ℤ, t ≤ j → IsZero ((DerivedCategory.homologyFunctor _ j).obj
      (DerivedCategory.Q.obj (X.restrictComplex K V))) := fun j hj => by
    have := hV
    exact DerivedCategory.isZero_of_isLE _ (t - 1) j (by omega)
  refine ⟨0, isStrictlyPerfect_zero X V, 0, fun j hj => ?_, ?_⟩
  · exact (hsrc j).isIso (htgt j (by omega)) _
  · have : IsIso ((DerivedCategory.homologyFunctor _ t).map
      (0 : DerivedCategory.Q.obj (0 : CochainComplex
        (_root_.SheafOfModules.{0} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over V)) ℤ) ⟶
        DerivedCategory.Q.obj (X.restrictComplex K V))) :=
      (hsrc t).isIso (htgt t le_rfl) _
    infer_instance

/-! ### The local step and Stacks 09J9 -/

variable [(sheafTensor.{0, 0, 0, 0, 0} X.O).Additive]
  [∀ M, ((sheafTensor.{0, 0, 0, 0, 0} X.O).obj M).Additive]
  [∀ (K₁ K₂ : CochainComplex (_root_.SheafOfModules.{0} (Tensor.ringSheaf X.O)) ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (sheafTensor.{0, 0, 0, 0, 0} X.O) (ComplexShape.up ℤ)]
variable [∀ V : X.C, (sheafTensor.{0, 0, 0, 0, 0} (X.O.over V)).Additive]
  [∀ (V : X.C) (M : _root_.SheafOfModules.{0} (Tensor.ringSheaf (X.O.over V))),
    ((sheafTensor.{0, 0, 0, 0, 0} (X.O.over V)).obj M).Additive]
  [∀ (V : X.C) (K₁ K₂ : CochainComplex
      (_root_.SheafOfModules.{0} (Tensor.ringSheaf (X.O.over V))) ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (sheafTensor.{0, 0, 0, 0, 0} (X.O.over V))
      (ComplexShape.up ℤ)]

/-- **Every object of `D(O)` is represented by a complex which is K-flat and whose restriction
to every slice of the site is K-flat.** This is the resolution of Stacks 06YS in its colimit
presentation: a sequential colimit of bounded above complexes of flat `O`-modules is K-flat by
Stacks 06YQ, and so is its restriction to any slice, each stage restricting to a bounded above
complex of flat modules there. -/
private theorem exists_sliceKFlat_representative
    (K : DerivedCategory (_root_.SheafOfModules.{0} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    ∃ A : CochainComplex (_root_.SheafOfModules.{0} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ,
      Stacks.SheafOfModules.KFlat X.O A ∧
      (∀ W : X.C, Stacks.SheafOfModules.KFlat (X.O.over W) (X.restrictComplex A W)) ∧
      Nonempty (DerivedCategory.Q.obj A ≅ K) := by
  obtain ⟨Kc, ⟨eKc⟩⟩ : ∃ P, Nonempty (DerivedCategory.Q.obj P ≅ K) :=
    ⟨_, ⟨DerivedCategory.Q.objObjPreimageIso K⟩⟩
  obtain ⟨D, f, hLE, hflat, hqis, -⟩ :=
    Stacks.SheafOfModules.KFlatResolution.exists_resolution_colimit X.O Kc
  have hq : IsIso (DerivedCategory.Q.map f) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ f).2 hqis
  exact ⟨colimit D,
    Stacks.SheafOfModules.KFlatResolution.kFlat_colimit_of_isStrictlyLE_of_isFlat X.O D
      hLE hflat,
    fun W => kFlat_restrictionComplex_of_isColimit X.O W D (colimit.cocone D)
      (colimit.isColimit D) hLE hflat,
    ⟨(@asIso _ _ _ _ (DerivedCategory.Q.map f) hq) ≪≫ eKc⟩⟩

/-- **The local step of Stacks 09J9 part (1), over one object of the site.** Over an object `W`
carrying a strictly perfect approximation of `𝒜|_W` in degree `n` and one of `ℬ|_W` in degree
`m`, with `𝒜|_W ∈ D^{≤ a}`, `ℬ|_W ∈ D^{≤ b}` and `n ≤ a`, the total tensor complex
`Tot(𝒜 ⊗_O ℬ)` carries the local datum of degree `t = max (m + a) (n + b)`.

The total tensor complex of the two approximations is strictly perfect (Stacks 09J8), hence
K-flat, and the derived tensor product on the slice makes the derived tensor product of the two
approximations an approximation in degree `t`. Its source is the class of that total tensor
complex and its target the class of `Tot(𝒜 ⊗_O ℬ)|_W`, by the comparison of Stacks 06YU on the
slice together with `AlgebraicGeometry.RingedSite.tensorComplexOverIso`. -/
private theorem hasApprox_tensorComplex
    (A B :
      CochainComplex (_root_.SheafOfModules.{0} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (W : X.C)
    (hAW : Stacks.SheafOfModules.KFlat (X.O.over W) (X.restrictComplex A W))
    (hBW : Stacks.SheafOfModules.KFlat (X.O.over W) (X.restrictComplex B W))
    (n m a b : ℤ) (hna : n ≤ a)
    (hA : (DerivedCategory.Q.obj (X.restrictComplex A W)).IsLE a)
    (hB : (DerivedCategory.Q.obj (X.restrictComplex B W)).IsLE b)
    (hApp : HasApprox X A n W) (hBpp : HasApprox X B m W) :
    HasApprox X (((tensorComplex X.O).obj A).obj B) (max (m + a) (n + b)) W := by
  obtain ⟨P₁, hP₁, α, hαiso, hαepi⟩ := hApp
  obtain ⟨P₂, hP₂, β, hβiso, hβepi⟩ := hBpp
  set TW := Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct (X.O.over W)
  obtain ⟨γ, hγiso, hγepi⟩ := exists_approximation_derivedTensor (X.O.over W) TW
    (DerivedCategory.Q.obj P₁) (DerivedCategory.Q.obj P₂)
    (DerivedCategory.Q.obj (X.restrictComplex A W))
    (DerivedCategory.Q.obj (X.restrictComplex B W)) n m a b hna hA hB
    α hαiso hαepi β hβiso hβepi
  set eS := TW.comparison P₁ P₂ (kFlat_over_of_isStrictlyPerfect X W P₁ hP₁)
    (kFlat_over_of_isStrictlyPerfect X W P₂ hP₂)
  set eT := TW.comparison (X.restrictComplex A W) (X.restrictComplex B W) hAW hBW
  set eR := DerivedCategory.Q.mapIso (X.tensorComplexOverIso W A B)
  have k1 := Stacks.Cohomology.DerivedPullbackOnRingedTopoi.approximation_comp_iso
    γ eT (max (m + a) (n + b)) hγiso hγepi
  have k2 := Stacks.Cohomology.DerivedPullbackOnRingedTopoi.approximation_comp_iso
    (γ ≫ eT.hom) eR.symm (max (m + a) (n + b)) k1.1 k1.2
  have k3 := Stacks.Cohomology.DerivedPullbackOnRingedTopoi.iso_comp_approximation
    eS.symm ((γ ≫ eT.hom) ≫ eR.symm.hom) (max (m + a) (n + b)) k2.1 k2.2
  exact ⟨((tensorComplex (X.O.over W)).obj P₁).obj P₂,
    isStrictlyPerfect_tensorComplex (X.O.over W) P₁ P₂ hP₁ hP₂,
    eS.symm.hom ≫ (γ ≫ eT.hom) ≫ eR.symm.hom, k3.1, k3.2⟩

/-- Let `(C, O)` be a ringed site, `T` a derived tensor product on `D(O)`, and `K`, `L` objects
of `D(O)`. If `K` is `n`-pseudo-coherent with `H^i(K) = 0` for `i > a`, and `L` is
`m`-pseudo-coherent with `H^j(L) = 0` for `j > b`, then `K ⊗^{𝐋}_O L` is `t`-pseudo-coherent for
`t = max (m + a) (n + b)`. -/
@[sga "6 I 2.16" "special case"]
theorem isPseudoCoherentFrom_tensor
    (T : Stacks.DerivedTensor.RingedSite.DerivedTensorProduct X.O)
    (K L : DerivedCategory (_root_.SheafOfModules.{0} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (n m a b : ℤ)
    (hK : X.IsPseudoCoherentFrom K n)
    (hKa : ∀ i : ℤ, a < i →
      IsZero ((DerivedCategory.homologyFunctor
        (_root_.SheafOfModules.{0} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) i).obj K))
    (hL : X.IsPseudoCoherentFrom L m)
    (hLb : ∀ j : ℤ, b < j →
      IsZero ((DerivedCategory.homologyFunctor
        (_root_.SheafOfModules.{0} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) j).obj L)) :
    X.IsPseudoCoherentFrom ((T.tensor.obj K).obj L) (max (m + a) (n + b)) := by
  have hKLE : K.IsLE a := (DerivedCategory.isLE_iff K a).2 hKa
  have hLLE : L.IsLE b := (DerivedCategory.isLE_iff L b).2 hLb
  rcases lt_or_ge a n with hna | hna
  · have hT : ((T.tensor.obj K).obj L).IsLE (a + b) :=
      Stacks.DerivedTensor.RingedSite.isLE_derivedTensorProduct X.O T K L a b
    have := le_max_right (m + a) (n + b)
    refine isPseudoCoherentFrom_of_isLE X _ (max (m + a) (n + b)) ?_
    have := hT
    exact DerivedCategory.TStructure.t.isLE_of_le _ (a + b) (max (m + a) (n + b) - 1) (by omega)
  have rep : ∀ (K' : DerivedCategory
      (_root_.SheafOfModules.{0} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) (c : ℤ),
      K'.IsLE c → ∃ A : CochainComplex
        (_root_.SheafOfModules.{0} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ,
      Stacks.SheafOfModules.KFlat X.O A ∧
      (∀ W : X.C, Stacks.SheafOfModules.KFlat (X.O.over W) (X.restrictComplex A W)) ∧
      (DerivedCategory.Q.obj A).IsLE c ∧ Nonempty (DerivedCategory.Q.obj A ≅ K') := by
    intro K' c hK'
    obtain ⟨A, hAflat, hALE, ⟨eA⟩⟩ :=
      Stacks.Cohomology.DerivedPullbackOnRingedTopoi.exists_flatRepresentative_of_isLE
        (Y := X) K' c hK'
    have := hALE
    refine ⟨A, Stacks.SheafOfModules.kFlat_of_boundedAbove_of_flat X.O A ⟨c, hALE⟩ hAflat,
      fun W => Stacks.SheafOfModules.KFlatRestriction.kFlat_restriction_of_isStrictlyLE X.O W A c
        hAflat, ?_, ⟨eA⟩⟩
    rw [DerivedCategory.isLE_Q_obj_iff]
    infer_instance
  obtain ⟨A, hAk, hAW, hQA, ⟨eA⟩⟩ := rep K a hKLE
  obtain ⟨B, hBk, hBW, hQB, ⟨eB⟩⟩ := rep L b hLLE
  have eG : DerivedCategory.Q.obj (((tensorComplex X.O).obj A).obj B) ≅
      (T.tensor.obj K).obj L :=
    (T.comparison A B hAk hBk).symm ≪≫ (T.tensor.mapIso eA).app _ ≪≫
      (T.tensor.obj K).mapIso eB
  have hApc : X.IsPseudoCoherentComplexFrom A n :=
    X.isPseudoCoherentComplexFrom_of_iso K n hK A eA
  have hBpc : X.IsPseudoCoherentComplexFrom B m :=
    X.isPseudoCoherentComplexFrom_of_iso L m hL B eB
  refine isPseudoCoherentFrom_of_locally_hasApprox X _ (max (m + a) (n + b)) _ eG fun U => ?_
  obtain ⟨S₁, hS₁, hd₁⟩ := exists_covering_hasApprox X A n hApc U
  obtain ⟨S₂, hS₂, hd₂⟩ := exists_covering_hasApprox X B m hBpc U
  exact ⟨S₁ ⊓ S₂, X.J.intersection_covering hS₁ hS₂, fun V g hg =>
    hasApprox_tensorComplex X A B V (hAW V) (hBW V) n m a b hna
      (isLE_restrictComplex X A V a hQA) (isLE_restrictComplex X B V b hQB)
      (hd₁ g hg.1) (hd₂ g hg.2)⟩

/-- **Stacks 09J9, part (2), for any derived tensor product `T`.** The derived tensor product
of two pseudo-coherent objects of `D(O)` is pseudo-coherent.

Neither factor is assumed bounded above, so the representatives are the resolutions of Stacks
06YS taken in their colimit presentation: a sequential colimit of bounded above complexes of
flat `O`-modules is K-flat and stays K-flat after restriction to any slice of the site, which
is what the comparison of Stacks 06YU needs there. `Tot(𝒜 ⊗_O ℬ)` is then a representative of
`K ⊗^{𝐋} L`, and it suffices to see that it is `q`-pseudo-coherent for every `q`. The
cohomological bounds that part (1) needs are produced on the covering itself: a strictly perfect
approximation in degree `0` over an object of the site has only finitely many nonzero terms, so
the two factors are bounded above there, say by `a` and `b`, and the thresholds
`n = min (q - b) a` and `m = min (q - a) b` give `max (m + a) (n + b) ≤ q` and `n ≤ a`. -/
@[sga "6 I 2.16" "partial", sga "6 III 1.8" "Case X_i = Y_i = S"]
theorem isPseudoCoherent_tensor
    (T : Stacks.DerivedTensor.RingedSite.DerivedTensorProduct X.O)
    (K L : DerivedCategory (_root_.SheafOfModules.{0} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (hK : X.IsPseudoCoherent K) (hL : X.IsPseudoCoherent L) :
    X.IsPseudoCoherent ((T.tensor.obj K).obj L) := by
  classical
  obtain ⟨Kc, hKc, ⟨eKc⟩⟩ := hK
  obtain ⟨Lc, hLc, ⟨eLc⟩⟩ := hL
  obtain ⟨A, hAk, hAW, ⟨eA⟩⟩ := exists_sliceKFlat_representative X K
  obtain ⟨B, hBk, hBW, ⟨eB⟩⟩ := exists_sliceKFlat_representative X L
  have hApc : ∀ q : ℤ, X.IsPseudoCoherentComplexFrom A q := fun q =>
    X.isPseudoCoherentComplexFrom_of_iso K q ⟨Kc, hKc q, ⟨eKc⟩⟩ A eA
  have hBpc : ∀ q : ℤ, X.IsPseudoCoherentComplexFrom B q := fun q =>
    X.isPseudoCoherentComplexFrom_of_iso L q ⟨Lc, hLc q, ⟨eLc⟩⟩ B eB
  have eG : DerivedCategory.Q.obj (((tensorComplex X.O).obj A).obj B) ≅
      (T.tensor.obj K).obj L :=
    (T.comparison A B hAk hBk).symm ≪≫ (T.tensor.mapIso eA).app _ ≪≫
      (T.tensor.obj K).mapIso eB
  have key : ∀ (q : ℤ) (U : X.C), ∃ S : Sieve U, S ∈ X.J U ∧
      ∀ ⦃V : X.C⦄ (g : V ⟶ U), S g →
        HasApprox X (((tensorComplex X.O).obj A).obj B) q V := by
    intro q U
    have pair : ∀ (n m : ℤ) (U : X.C), ∃ S : Sieve U, S ∈ X.J U ∧
        ∀ ⦃V : X.C⦄ (g : V ⟶ U), S g → HasApprox X A n V ∧ HasApprox X B m V := by
      intro n m U
      obtain ⟨S₁, hS₁, hd₁⟩ := exists_covering_hasApprox X A n (hApc n) U
      obtain ⟨S₂, hS₂, hd₂⟩ := exists_covering_hasApprox X B m (hBpc m) U
      exact ⟨S₁ ⊓ S₂, X.J.intersection_covering hS₁ hS₂, fun V g hg => ⟨hd₁ g hg.1, hd₂ g hg.2⟩⟩
    have hLE : ∀ (K : CochainComplex
        (_root_.SheafOfModules.{0} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) {V : X.C},
        HasApprox X K 0 V →
        ∃ c : ℤ, (DerivedCategory.Q.obj (X.restrictComplex K V)).IsLE c := by
      rintro K V ⟨P, hP, β, hiso, -⟩
      obtain ⟨c, hc⟩ := exists_isZero_X_of_lt X V hP
      exact ⟨_, DerivedCategory.isLE_Q_obj_of_approximation 0 c hc β hiso⟩
    obtain ⟨S, hS, hd⟩ := pair 0 0 U
    refine exists_covering_of_locally X.J S hS _ fun V g hg => ?_
    obtain ⟨a, ha⟩ := hLE A (hd g hg).1
    obtain ⟨b, hb⟩ := hLE B (hd g hg).2
    obtain ⟨S', hS', hd'⟩ := pair (min (q - b) a) (min (q - a) b) V
    refine ⟨S', hS', fun W h hh => ?_⟩
    refine HasApprox.mono X (hasApprox_tensorComplex X A B W (hAW W) (hBW W) _ _ a b
      (min_le_right _ _) (isLE_restrictComplex_of_hom X A h a ha)
      (isLE_restrictComplex_of_hom X B h b hb) (hd' h hh).1 (hd' h hh).2) (max_le ?_ ?_)
    · have := min_le_left (q - a) b
      omega
    · have := min_le_left (q - b) a
      omega
  refine ⟨((tensorComplex X.O).obj A).obj B, fun q => ?_, ⟨eG⟩⟩
  exact X.isPseudoCoherentComplexFrom_of_iso _ q
    (isPseudoCoherentFrom_of_locally_hasApprox X _ q _ eG (key q)) _ eG

end Site

/-! ### Stacks 09J9 for the derived tensor product of the library -/

section Canonical

attribute [local instance] HasDerivedCategory.standard

variable (X : RingedSite.{0, 0, 0})

/-- **Stacks 09J9, part (1).** Let `(C, O)` be a ringed site and let `K`, `L` be objects of
`D(O)`. If `K` is `n`-pseudo-coherent with `H^i(K) = 0` for `i > a`, and `L` is
`m`-pseudo-coherent with `H^j(L) = 0` for `j > b`, then `K ⊗^{𝐋}_O L` is `t`-pseudo-coherent
for `t = max (m + a) (n + b)`. Here `⊗^{𝐋}_O` is the derived tensor product of Stacks 06YU,
`Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor`. -/
@[stacks 09J9 "part (1)"]
theorem isPseudoCoherentFrom_derivedTensorProduct
    (K L : DerivedCategory (_root_.SheafOfModules.{0} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (n m a b : ℤ)
    (hK : X.IsPseudoCoherentFrom K n)
    (hKa : ∀ i : ℤ, a < i →
      IsZero ((DerivedCategory.homologyFunctor
        (_root_.SheafOfModules.{0} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) i).obj K))
    (hL : X.IsPseudoCoherentFrom L m)
    (hLb : ∀ j : ℤ, b < j →
      IsZero ((DerivedCategory.homologyFunctor
        (_root_.SheafOfModules.{0} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) j).obj L)) :
    X.IsPseudoCoherentFrom
      ((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.O |>.obj K).obj L)
      (max (m + a) (n + b)) :=
  isPseudoCoherentFrom_tensor X (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct X.O)
    K L n m a b hK hKa hL hLb

/-- **Stacks 09J9, part (2).** Let `(C, O)` be a ringed site. If `K` and `L` are pseudo-coherent
objects of `D(O)`, then `K ⊗^{𝐋}_O L` is pseudo-coherent. Here `⊗^{𝐋}_O` is the derived tensor
product of Stacks 06YU, `Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor`. -/
@[stacks 09J9 "part (2)"]
theorem isPseudoCoherent_derivedTensorProduct
    (K L : DerivedCategory (_root_.SheafOfModules.{0} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (hK : X.IsPseudoCoherent K) (hL : X.IsPseudoCoherent L) :
    X.IsPseudoCoherent
      ((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.O |>.obj K).obj L) :=
  isPseudoCoherent_tensor X (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct X.O)
    K L hK hL

end Canonical

end Stacks.SheafOfModules.DerivedTensorProduct

end
