module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.DerivedLimitOfTruncations
public import StacksFrontier.AlgebraicGeometry.Stacks.FibreEssentialSmallness
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.FppfEtaleComparisonLqcFbc

/-!
# A complex with cohomology in `LQCoh^fbc` is the derived limit of its truncations (Stacks 08IY)

Let `p : 𝒳 ⥤ (Sch/S)_{fppf}` be a category fibred in groupoids and let `K` be an object of
`D(𝒪_𝒳)` whose cohomology sheaves are locally quasi-coherent (**Stacks 06WJ**) and have the flat
base change property (**Stacks 0762**).  **Stacks 08IY** says that there is a distinguished
triangle

`K ⟶ ∏_{n ≥ 0} τ_{≥ -n}K ⟶ ∏_{n ≥ 0} τ_{≥ -n}K ⟶ K[1]`

in `D(𝒪_𝒳)`, that is, `K` is the derived limit of the tower of its canonical truncations from
below.

This file proves the triangle when the cohomology sheaves satisfy the presheaf reading
`AlgebraicGeometry.Stack.IsLocallyQuasicoherentWithFlatBaseChange` of the flat base change
property, which is stronger than **Stacks 0762**.  Stacks 08IY itself, with the reading of 0762 by
the inverse image of sheaves, is in
`StacksFrontier/AlgebraicGeometry/Stacks/Quasicoherent/SheafLqcFbcDerivedLimitOfTruncations.lean`.

The source's proof has two steps, both available here.

* The vanishing `H^p(x, ℱ) = 0` for `p > 0`, `ℱ` in `LQCoh^fbc(𝒪_𝒳)` and `x` an object of
  `𝒳_fppf` lying over an affine scheme is `AlgebraicGeometry.Stack.hasAffineAcyclicLqcFbcModules`.
* The convergence criterion of Cohomology on Sites **Stacks 0D6P** with `d = 0`, for the class
  `ℬ` of objects lying over an affine scheme, is
  `AlgebraicGeometry.Stack.exists_isDerivedLimit_truncGETower_of_lqcFbc`.  It needs `ℬ` to cover
  every object of `𝒳_fppf` by families indexed in the hom universe of the site, which is
  `AlgebraicGeometry.Stack.hasEnoughObjects_isAffineOver_of_essentiallySmall` below.

## Main results

* `AlgebraicGeometry.Stack.hasEnoughObjects_isAffineOver_of_essentiallySmall`: the objects of
  `𝒳_fppf` lying over an affine scheme cover every object, by families indexed in `Type u`.
* `AlgebraicGeometry.Stack.exists_isDerivedLimit_truncGETower_of_lqcFbc_of_essentiallySmall`:
  the triangle of Stacks 08IY for an essentially small category fibred in groupoids whose
  morphisms lie in the universe of the schemes.
* `AlgebraicGeometry.Stack.exists_isDerivedLimit_truncGETower_of_lqcFbc_algebraicStack`:
  the triangle of Stacks 08IY for every algebraic stack, under the presheaf reading of the flat
  base change property, which is stronger than **Stacks 0762**.  An object of
  `AlgebraicGeometry.Stack.AlgebraicStacks` is such a category: its morphisms lie in `Type u` and
  it is essentially small by `AlgebraicGeometry.Stack.essentiallySmall_obj_algebraicStack`.  The
  statement with the source's reading of 0762 is
  `AlgebraicGeometry.Stack.exists_isDerivedLimit_truncGETower_of_lqcohSheafFbc_algebraicStack`.

## Implementation notes

The seating is that of **Stacks 075R** in
`StacksFrontier/AlgebraicGeometry/Stacks/Quasicoherent/FppfEtaleComparisonLqcFbc.lean`: the total
category of `𝒳` has its morphisms in the universe `u` of the schemes and is essentially small
relative to `u`, which is the convention of the source that a category has a *set* of objects.
It makes the sheaves of `𝒪_𝒳`-modules with sections in `Type u` a Grothendieck abelian category,
so that `D(𝒪_𝒳)` and the derived functors exist; sheafification, enough injectives and the
`Ext`-groups are all derived from it here and are not hypotheses.  The derived category is the
standard localization, `HasDerivedCategory.standard`, as in
`StacksFrontier/AlgebraicGeometry/Stacks/Quasicoherent/DerivedLimitOfTruncations.lean`.

The covering families of `AlgebraicGeometry.FibredSite.exists_affine_ofArrows` are indexed in
`Type (u + 1)`.  Essential smallness cuts the index down to `Type u`: the arrows into an object
from the objects of a small model of `𝒳` lying over an affine scheme form a `u`-small family whose
sieve contains the given one.

## References

* [Stacks Project, Tag 08IY](https://stacks.math.columbia.edu/tag/08IY)
* [Stacks Project, Tag 0D6P](https://stacks.math.columbia.edu/tag/0D6P)
* [Stacks Project, Tag 06WJ](https://stacks.math.columbia.edu/tag/06WJ)
* [Stacks Project, Tag 0762](https://stacks.math.columbia.edu/tag/0762)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated AlgebraicGeometry

universe u v w

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck
  Stacks.Cohomology.SiteModules.moduleSheavesEnoughInjectives
  AlgebraicGeometry.BigFppfOver.hasPointwiseRightKanExtension_op_homFunctor

namespace AlgebraicGeometry.Stack

attribute [local instance] HasDerivedCategory.standard

variable (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
  (S : Scheme.{u}) (hS : B.Contains S)

attribute [local instance 10] hasSheafifyEssentiallySmallSite
attribute [local instance] FibredSite.wEqualsLocallyBijective_associatedTopology
  enoughInjectives_fppfSiteModules_of_essentiallySmall

section EssentiallySmall

variable {𝒳 : Type v} [Category.{u} 𝒳] [EssentiallySmall.{u} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS)
  (hp : p.IsFiberedInGroupoids)

include hp in
/-- **The objects lying over an affine scheme cover the fppf site of an essentially small category
fibred in groupoids**, by families indexed in the hom universe `u` of the site.  This is the class
`ℬ` of the proof of **Stacks 08IY** as a covering class in the sense of **Stacks 090L** (3).

`AlgebraicGeometry.FibredSite.exists_affine_ofArrows` gives a covering family by objects lying
over affine schemes, indexed in `Type (u + 1)`.  The family of all arrows `Z ⟶ U` from the
objects `Z` of a small model of `𝒳` lying over an affine scheme is indexed in `Type u`, and its
sieve contains every member of the given family, each member being isomorphic to an object of
the small model. -/
theorem hasEnoughObjects_isAffineOver_of_essentiallySmall :
    (BigFppfOver.associatedTopology B S hS p .fppf).HasEnoughObjects
      (fun x => IsAffineOver B S hS (p.obj x)) := by
  intro U
  obtain ⟨I, y, φ, hyaff, hcov⟩ := FibredSite.exists_affine_ofArrows B S hS p hp U
  let e := equivSmallModel 𝒳
  let A : Type u := Σ Z : SmallModel 𝒳,
    { f : e.inverse.obj Z ⟶ U // IsAffineOver B S hS (p.obj (e.inverse.obj Z)) }
  refine ⟨A, fun a => e.inverse.obj a.1, fun a => a.2.1, ?_, fun a => a.2.2⟩
  refine (BigFppfOver.associatedTopology B S hS p .fppf).superset_covering ?_ hcov
  intro V g hg
  obtain ⟨i, b, rfl⟩ := (Sieve.mem_ofArrows_iff _ _ _).1 hg
  let ι : y i ≅ e.inverse.obj (e.functor.obj (y i)) := e.unitIso.app (y i)
  have hi : IsAffineOver B S hS (p.obj (e.inverse.obj (e.functor.obj (y i)))) :=
    IsAffine.of_isIso ((BigFppfOver.toScheme B S hS).mapIso (p.mapIso ι)).inv (h := hyaff i)
  let a : A := ⟨e.functor.obj (y i), ι.inv ≫ φ i, hi⟩
  have hfac : b ≫ φ i = (b ≫ ι.hom) ≫ (ι.inv ≫ φ i) := by
    rw [Category.assoc, Iso.hom_inv_id_assoc]
  rw [hfac]
  exact (Sieve.ofArrows _ _).downward_closed
    (Sieve.ofArrows_mk (fun a : A => e.inverse.obj a.1) (fun a => a.2.1) a) _

/-- **The triangle of Stacks 08IY for an essentially small category fibred in groupoids.** Let
`p : 𝒳 ⥤ (Sch/S)_{fppf}` be a category fibred in groupoids and let `K`
be an object of `D(𝒪_𝒳)`, the derived category of the sheaves of `𝒪_𝒳`-modules on the fppf site
of `𝒳`, whose cohomology sheaves are locally quasi-coherent (**Stacks 06WJ**) and have the flat
base change property in the presheaf reading
`AlgebraicGeometry.Stack.IsLocallyQuasicoherentWithFlatBaseChange`, which is stronger than
**Stacks 0762**.  Then there is a distinguished triangle

`K ⟶ ∏_{n ≥ 0} τ_{≥ -n}K ⟶ ∏_{n ≥ 0} τ_{≥ -n}K ⟶ K[1]`

in `D(𝒪_𝒳)`: the product of the tower `n ↦ τ_{≥ -n}K` exists and `K` is its derived limit
(`CategoryTheory.Pretriangulated.IsDerivedLimit`, **Stacks 08TC**), the second arrow being
`1 - shift`.

As in the source, the higher fppf cohomology of a module in `LQCoh^fbc(𝒪_𝒳)` vanishes over the
objects lying over an affine scheme (`AlgebraicGeometry.Stack.hasAffineAcyclicLqcFbcModules`),
those objects cover `𝒳_fppf`
(`AlgebraicGeometry.Stack.hasEnoughObjects_isAffineOver_of_essentiallySmall`), and the
convergence criterion of **Stacks 0D6P** with `d = 0` applies
(`AlgebraicGeometry.Stack.exists_isDerivedLimit_truncGETower_of_lqcFbc`). -/
theorem exists_isDerivedLimit_truncGETower_of_lqcFbc_of_essentiallySmall
    (K : DerivedCategory (fppfSiteModules B S hS p hp))
    (hK : ∀ i : ℤ, IsLocallyQuasicoherentWithFlatBaseChange B E h S hS p hp
      ((DerivedCategory.homologyFunctor (fppfSiteModules B S hS p hp) i).obj K).val) :
    ∃ _ : HasProduct fun n : ℕ ↦ (fppfTruncGETower B S hS p hp K).obj ⟨n⟩,
      IsDerivedLimit (fppfTruncGETower B S hS p hp K) K :=
  exists_isDerivedLimit_truncGETower_of_lqcFbc B E h S hS p hp K hK
    (hasEnoughObjects_isAffineOver_of_essentiallySmall B S hS p hp)
    (hasAffineAcyclicLqcFbcModules B E h S hS p hp)

end EssentiallySmall

/-- **The triangle of Stacks 08IY for an algebraic stack, under the presheaf reading of flat base
change.** Let `𝒳` be an algebraic stack and let `K` be an object of `D(𝒪_𝒳)`, the derived category
of the sheaves of `𝒪_𝒳`-modules on the fppf site of `𝒳`, whose cohomology sheaves are locally
quasi-coherent (**Stacks 06WJ**) and satisfy
`AlgebraicGeometry.Stack.IsLocallyQuasicoherentWithFlatBaseChange`, the flat base change property
with the presheaf inverse image.  That reading is strictly stronger than **Stacks 0762**; the
statement of Stacks 08IY with the source's reading is
`AlgebraicGeometry.Stack.exists_isDerivedLimit_truncGETower_of_lqcohSheafFbc_algebraicStack`,
which implies this one.  Then there is a distinguished triangle

`K ⟶ ∏_{n ≥ 0} τ_{≥ -n}K ⟶ ∏_{n ≥ 0} τ_{≥ -n}K ⟶ K[1]`

in `D(𝒪_𝒳)`: the product of the tower `n ↦ τ_{≥ -n}K` exists and `K` is its derived limit
(`CategoryTheory.Pretriangulated.IsDerivedLimit`, **Stacks 08TC**), the second arrow being
`1 - shift`.

The total category of an object of `AlgebraicGeometry.Stack.AlgebraicStacks` has its morphisms
in the universe of the schemes and is essentially small,
`AlgebraicGeometry.Stack.essentiallySmall_obj_algebraicStack`, so this is
`AlgebraicGeometry.Stack.exists_isDerivedLimit_truncGETower_of_lqcFbc_of_essentiallySmall` at the
structure functor of `𝒳`. -/
theorem exists_isDerivedLimit_truncGETower_of_lqcFbc_algebraicStack
    (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (K : DerivedCategory (fppfSiteModules B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids))
    (hK : ∀ i : ℤ, IsLocallyQuasicoherentWithFlatBaseChange B E h S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids
      ((DerivedCategory.homologyFunctor
        (fppfSiteModules B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids) i).obj K).val) :
    ∃ _ : HasProduct fun n : ℕ ↦
        (fppfTruncGETower B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids K).obj ⟨n⟩,
      IsDerivedLimit (fppfTruncGETower B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids K) K :=
  exists_isDerivedLimit_truncGETower_of_lqcFbc_of_essentiallySmall B E h S hS 𝒳.val.val.p
    𝒳.val.isFiberedInGroupoids K hK

end AlgebraicGeometry.Stack

end
