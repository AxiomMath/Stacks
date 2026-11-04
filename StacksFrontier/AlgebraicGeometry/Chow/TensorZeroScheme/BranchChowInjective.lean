module

public import StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.LocalizationSurjectivity
public import StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.VectorBundlePullbackIso
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.FirstChernClassCentral
public import StacksFrontier.AlgebraicGeometry.Chow.TensorZeroScheme.BranchLineBundle
public import StacksFrontier.AlgebraicGeometry.Chow.TensorZeroScheme.ChowMaps

/-!
# Flat pullback along a branch projection of Tag 0F97 is injective

[Stacks, Tag 0B74] says that flat pullback along the structure morphism of the total space of a
line bundle is an isomorphism on Chow groups; its injectivity half is
`Stacks.Chow.flatPullbackChow_totalSpaceToBase_injective`, proved with nothing assumed. Condition
(4) of [Stacks, Tag 0F97] identifies each branch projection `pᵢ : Dᵢ ⟶ D` of the tag's diagram
with such a structure morphism, by an isomorphism over `D` — but only up to that isomorphism, so
the injectivity has to be carried across it.

This file does that. It is what clause (2) of [Stacks, Tag 0F99] — injectivity of
`p^* : A_k(D) ⟶ A_{k+1}(D')` for the morphism `p = p₁` of that tag's diagram — is proved from.

## Main results

* `Stacks.Chow.flatPullbackChow_injective_of_isIso_comp` — **precomposing with an isomorphism
  does not change injectivity of flat pullback**, the counterpart of
  `Stacks.Chow.flatPullbackChow_surjective_of_isIso_comp`.
* `Stacks.Chow.TensorZeroScheme.flatPullbackChowProj₁_injective` — **[Stacks, Tag 0B74] for the
  first branch projection of [Stacks, Tag 0F97]**: `p₁^* : A_k(D) ⟶ A_{k+1}(D₁)` is injective.

## Implementation notes

### No degree transport is needed in the composite

[Stacks, Tag 02RD] on Chow groups, `Stacks.Chow.flatPullbackChow_comp`, is a heterogeneous
equality: `f^*(g^*α)` sits in degree `k + s + r` and `(f ≫ g)^*α` in degree `k + (r + s)`. The
surjectivity counterpart has to move a class across that gap and so uses
`Stacks.Chow.chowGroupDegreeEquiv`. Injectivity does not: the chain

  `f^*(g^*α) ≍ (f ≫ g)^*α = (f ≫ g)^*β ≍ f^*(g^*β)`

has the same type at both ends, so `eq_of_heq` applies to it directly and the intermediate
degree never has to be named.

### The transparency crossing at the base of the branch bundle

`(branchSituation Y L₁ L₂ s L₂).X` and `(zeroIdeal Y L₁ L₂ s).subscheme` agree only at default
transparency, so a statement about `p₁`, whose target is spelled as the zero scheme, offers
instance search a structure morphism of the first that it cannot see through — the situation
described in the implementation notes of
`StacksFrontier.AlgebraicGeometry.Chow.TensorZeroScheme.BranchProjection`. The two general lemmas
below are therefore stated with every structure morphism a variable, and the single crossing
happens once, at the use site in `flatPullbackChowProj₁_injective`, where the elaborator performs
it against the ascribed type.

### No `@[stacks]` attribute

[Stacks, Tag 0B74] is registered on `Stacks.Chow.flatPullbackChow_totalSpaceToBase_injective`,
which is the tag's own statement; what is below carries it across the identification of condition
(4) of [Stacks, Tag 0F97] and is a consequence, not a further clause of either tag.

## References

* [Stacks Project, Tag 0B74](https://stacks.math.columbia.edu/tag/0B74)
* [Stacks Project, Tag 02RD](https://stacks.math.columbia.edu/tag/02RD)
* [Stacks Project, Tag 0F97](https://stacks.math.columbia.edu/tag/0F97)
* [Stacks Project, Tag 0F99](https://stacks.math.columbia.edu/tag/0F99)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Chow

/-- **Precomposing with an isomorphism does not change injectivity of flat pullback.** If
`p = e ≫ q` with `e` an isomorphism and `q` flat of relative dimension `r` with injective flat
pullback in degree `k`, then `p^*` is injective in degree `k`.

Flat pullback along an isomorphism is bijective by
`Stacks.Chow.flatPullbackChow_bijective_of_isIso`; the composite is then
`Stacks.Chow.flatPullbackChow_injective_of_comp_eq` with the ranks `0` and `r`. -/
theorem flatPullbackChow_injective_of_isIso_comp (C : ChowSituation.{u}) {X A Y : Scheme.{u}}
    (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sA : A ⟶ C.S) [LocallyOfFiniteType sA]
    (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (e : X ⟶ A) [IsIso e] (q : A ⟶ Y)
    [LocallyOfFiniteType q] [AlgebraicGeometry.Flat q] (p : X ⟶ Y) [LocallyOfFiniteType p]
    [AlgebraicGeometry.Flat p] (hp : e ≫ q = p) (hebase : e ≫ sA = sX)
    (hqbase : q ≫ sY = sA) (hpbase : p ≫ sY = sX) (r : ℕ)
    (hq : AlgebraicGeometry.RelativeDimension q r)
    (hpr : AlgebraicGeometry.RelativeDimension p r) (k : ℤ)
    (hface : FlatPullbackFactorsThroughRationalEquivalence C sX sA e hebase 0
      (relativeDimension_of_isIso e) (k + (r : ℤ)))
    (hfacq : FlatPullbackFactorsThroughRationalEquivalence C sA sY q hqbase r hq k)
    (hfacp : FlatPullbackFactorsThroughRationalEquivalence C sX sY p hpbase r hpr k)
    (hinjq : Function.Injective (flatPullbackChow C sA sY q hqbase r hq k hfacq)) :
    Function.Injective (flatPullbackChow C sX sY p hpbase r hpr k hfacp) := by
  have _ : IsOpenImmersion e := IsOpenImmersion.of_isIso e
  exact flatPullbackChow_injective_of_comp_eq C sX sA sY e q p hp hebase hqbase hpbase 0 r r
    (Nat.zero_add r).symm (relativeDimension_of_isIso e) hq hpr k hface hfacq hfacp
    (flatPullbackChow_bijective_of_isIso C sX sA e hebase (relativeDimension_of_isIso e)
      (k + (r : ℤ)) hface).1
    hinjq

/-- **[Stacks, Tag 0B74], the injectivity half, for a morphism presented as an isomorphism onto
the total space of a line bundle followed by that bundle's structure morphism.** This is the
missing fourth member of the family
`Stacks.Chow.TensorZeroScheme.locallyOfFiniteType_of_iso_totalSpace`,
`flat_of_iso_totalSpace`, `relativeDimension_of_iso_totalSpace`: every structure morphism is a
variable and every target is `D.X`, so instance search succeeds here and the one transparency
crossing happens at the use site.

The isomorphism is eliminated by `subst`, after which
`Stacks.Chow.flatPullbackChow_totalSpaceToBase_injective_of_base` supplies the injectivity for
the bundle and `Stacks.Chow.flatPullbackChow_injective_of_isIso_comp` carries it across. -/
theorem injective_flatPullbackChow_of_iso_totalSpace (C : ChowSituation.{u})
    {D : Stacks.LineBundle.Situation.{u}} {Z : Scheme.{u}} (e : Z ≅ D.totalSpace)
    {g : Z ⟶ D.X} (hg : e.hom ≫ D.totalSpaceToBase = g) (sX : D.X ⟶ C.S)
    [LocallyOfFiniteType sX] (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ] (hsZ : g ≫ sX = sZ)
    (hgdim : letI : LocallyOfFiniteType g :=
        TensorZeroScheme.locallyOfFiniteType_of_iso_totalSpace e hg
      AlgebraicGeometry.RelativeDimension g 1) (k : ℤ) :
    letI : LocallyOfFiniteType g := TensorZeroScheme.locallyOfFiniteType_of_iso_totalSpace e hg
    letI : AlgebraicGeometry.Flat g := TensorZeroScheme.flat_of_iso_totalSpace e hg
    Function.Injective (flatPullbackChowOfRelativeDimension C sZ sX g hsZ 1 hgdim k) := by
  subst hg
  have : LocallyOfFiniteType D.totalSpaceToBase := D.locallyOfFiniteType_totalSpaceToBase
  have : AlgebraicGeometry.Flat D.totalSpaceToBase := D.flat_totalSpaceToBase
  have : LocallyOfFiniteType (D.totalSpaceToBase ≫ sX) := locallyOfFiniteType_comp _ _
  refine flatPullbackChow_injective_of_isIso_comp C sZ (D.totalSpaceToBase ≫ sX) sX e.hom
    D.totalSpaceToBase (e.hom ≫ D.totalSpaceToBase) rfl (by rw [← Category.assoc, hsZ]) rfl hsZ 1
    D.relativeDimension_totalSpaceToBase hgdim k ?_ ?_ ?_
    (flatPullbackChow_totalSpaceToBase_injective_of_base C D sX (D.totalSpaceToBase ≫ sX) rfl k ?_)
  all_goals exact flatPullbackFactorsThroughRationalEquivalence_general C _ _ _ _ _ _ _

namespace TensorZeroScheme

variable (C : ChowSituation.{u}) (Y : Scheme.{u}) (L₁ L₂ : Y.Modules)
  [h₁ : AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property L₁]
  [h₂ : AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property L₂]
  (s : Γ(Stacks.Divisors.tensorModules L₁ L₂, ⊤)) (R : Decomposition Y L₁ L₂ s)
  (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]

include h₁ h₂ in
/-- **[Stacks, Tag 0B74] for the first branch projection of a diagram as in [Stacks, Tag 0F97]**,
and clause (2) of [Stacks, Tag 0F99]: the flat pullback

  `p₁^* : A_k(D) ⟶ A_{k+1}(D₁)`

along the projection `p₁ : D₁ ⟶ D` of the diagram is injective for every `k`.

Condition (4) of [Stacks, Tag 0F97] identifies `D₁` with the total space of a line bundle over
`D`, by an isomorphism over `D`; flat pullback along the structure morphism of that total space
is injective with nothing assumed by
`Stacks.Chow.flatPullbackChow_totalSpaceToBase_injective_of_base`, and
`Stacks.Chow.flatPullbackChow_injective_of_isIso_comp` carries that across the
identification. -/
theorem flatPullbackChowProj₁_injective (k : ℤ) :
    Function.Injective (flatPullbackChowProj₁ C Y L₁ L₂ s R sY k) :=
  @injective_flatPullbackChow_of_iso_totalSpace C (branchSituation Y L₁ L₂ s L₂)
    R.normalize.D₁.subscheme R.normalize.branch₁ R.normalize.p₁
    R.normalize.branch₁_toBase
    ((zeroIdeal Y L₁ L₂ s).subschemeι ≫ sY)
    (inferInstance : LocallyOfFiniteType ((zeroIdeal Y L₁ L₂ s).subschemeι ≫ sY))
    (R.normalize.D₁.subschemeι ≫ R.normalize.p ≫ sY) inferInstance
    (proj₁_comp_zeroIdeal_subschemeι_comp C Y L₁ L₂ s R sY)
    (Decomposition.relativeDimension_p₁ Y L₁ L₂ s R.normalize) k

end TensorZeroScheme

end Stacks.Chow

end
