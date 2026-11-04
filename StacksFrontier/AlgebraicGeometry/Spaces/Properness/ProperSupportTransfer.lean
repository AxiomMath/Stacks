module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChowLemma.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescendingFiniteTypeLimitImage
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperClosedSubset
public import StacksFrontier.AlgebraicGeometry.Spaces.Properness.ProperClosedSubset
public import StacksFrontier.AlgebraicGeometry.Spaces.Properness.ProperSupport

/-!
# Properness of a closed subspace sitting inside the proper support of a sheaf

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` which is locally of finite
type and let `F` be an abelian sheaf on the small étale site of `X` whose support is proper
over `Y` in the sense of Stacks 0CZD, that is,
`AlgebraicGeometry.Space.HasProperSupport`. If `i : Z ⟶ X` is a closed immersion whose image on
points lies inside that support, then the composite `Z ⟶ Y` is proper.

This is the step by which hypothesis (3) of Stacks 083M — properness of the support of `𝒢` —
becomes properness of the closed subspace that carries `𝒢`, which is the form in which
Stacks 0CVI part (1) and the dévissage of Stacks 0CWC consume it.

## Main results

* `AlgebraicGeometry.Space.isProper_comp_of_hasProperSupport_of_range_subset`: properness over
  `Y` of a closed immersion into `X` whose image on points is contained in the support of a
  sheaf with proper support.

## Implementation notes

`AlgebraicGeometry.Space.HasProperSupport` is properness over `Y` of the support *as a closed
subset of points*, which by Definition 0CZD means properness of the **reduced** induced closed
subspace on it. The closed subspace `Z` to which properness is transferred need not be reduced,
so the statement is not a rewriting: it needs both halves of the properness layer of
Chapter 75, and it is their composite rather than any new mathematics.

* Stacks 0CZE, `AlgebraicGeometry.Space.isProperOver_of_subset`, brings properness over `Y` down
  from the support to the smaller closed subset `|i|(|Z|)`, which is closed by
  `AlgebraicGeometry.Space.isClosed_range_pointsMap_of_isClosedImmersion`.
* Stacks 0CZC, in the two halves
  `AlgebraicGeometry.Space.isProper_reducedClosedSubspace_iff_exists` and
  `AlgebraicGeometry.Space.exists_isProper_closedSubspace_iff_forall`, moves it from the reduced
  induced subspace on `|i|(|Z|)` to *every* closed subspace of `X` with that point set, `Z`
  among them.

Only the containment `|i|(|Z|) ⊆ Supp(F)` is asked for, not equality: the smaller the image the
more 0CZE gives. For the presentations this is applied to the containment is in fact an
equality — for the scheme-theoretic support of a finite type module by part (4) of Stacks 07U0,
`AlgebraicGeometry.Space.supportOfSheaf_eq_range_pointsMap_schemeTheoreticSupport`, and for the
subspace cut out by the zeroth Fitting ideal by part (2) of Stacks 0CZ6,
`AlgebraicGeometry.Space.idealZeroLocus_fittingIdeal_zero_eq_supportOfSheaf`.

The hypothesis is not implied by a presentation `F ≅ i_*ℋ`, and that is the whole reason it is
stated. For `ℋ` of finite type
`AlgebraicGeometry.Space.supportOfSheaf_modulePushforward_eq_image_of_isFiniteTypeOnSite` gives
`Supp(i_*ℋ) = |i|(Supp ℋ)`, so the containment asked for here amounts to `Supp(ℋ) = |Z|`: it
says that `Z` is no larger than the subspace `ℋ` actually lives on. Without it the statement is
false — take `ℋ = 0`, which leaves `Supp(F)` empty and `Z` arbitrary, so that properness of the
support says nothing whatever about `Z ⟶ Y`.

Stacks 0CZB is a section tag, not a lemma, so no tag attribute is carried here; the mathematical
content is that of Stacks 0CZE and Stacks 0CZC, whose covering sets are already complete in
`StacksFrontier/AlgebraicGeometry/Spaces/ProperClosedSubset.lean` and
`StacksFrontier/AlgebraicGeometry/Spaces/Properness/ProperClosedSubset.lean`.

The closed subspace handed to Stacks 0CZC has to be a `CategoryTheory.Subfunctor` of `X`, while
`i` is an arbitrary closed immersion; the two are matched by
`AlgebraicGeometry.Space.isClosedSubspace_range_of_isClosedImmersion`, which exhibits
`CategoryTheory.Subfunctor.range i` as a closed subspace; its point set is that of `i` by
`AlgebraicGeometry.Space.range_pointsMap_ι_range`. Both rest on
`CategoryTheory.Subfunctor.toRange i` being an isomorphism because a closed immersion is a
monomorphism, `AlgebraicGeometry.Space.mono_of_isClosedImmersion`, and properness crosses that
isomorphism by `AlgebraicGeometry.Space.isProper_of_isIso` and composition.

## References

* [Stacks Project, Tag 0CZC](https://stacks.math.columbia.edu/tag/0CZC)
* [Stacks Project, Tag 0CZD](https://stacks.math.columbia.edu/tag/0CZD)
* [Stacks Project, Tag 0CZE](https://stacks.math.columbia.edu/tag/0CZE)
* [Stacks Project, Tag 083M](https://stacks.math.columbia.edu/tag/083M)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u v

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **A closed subspace inside the proper support of a sheaf is proper over the base.** Let
`f : X ⟶ Y` be locally of finite type, let the support of an abelian sheaf `F` on the small
étale site of `X` be proper over `Y` in the sense of Stacks 0CZD, and let `i : Z ⟶ X` be a
closed immersion with `|i|(|Z|) ⊆ Supp(F)`. Then `Z ⟶ Y` is proper.

Properness over `Y` passes from the support to the closed subset `|i|(|Z|)` by Stacks 0CZE, and
from the reduced induced subspace on that set to `Z` itself — which need not be reduced — by
Stacks 0CZC. -/
theorem isProper_comp_of_hasProperSupport_of_range_subset
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (f : X ⟶ Y) (hf : IsLocallyOfFiniteType B S hS f)
    {F : Sheaf (SmallEtale.topology B S hS X) AddCommGrpCat.{v}}
    (hF : HasProperSupport B S hS hX hY f hf F)
    (hZ : IsAlgebraicSpace B S hS Z) (i : Z ⟶ X) (hi : IsClosedImmersion B S hS i)
    (hsub : Set.range (pointsMap B S hS Z i) ⊆ supportOfSheaf B S hS X F) :
    IsProper B S hS (i ≫ f) := by
  obtain ⟨hcl, hp⟩ := hF
  have hmono : Mono i := mono_of_isClosedImmersion B S hS i hi
  have hTcl : _root_.IsClosed (Set.range (pointsMap B S hS Z i)) :=
    isClosed_range_pointsMap_of_isClosedImmersion B S hS hX i hi
  have hW : IsClosedSubspace B S hS (Subfunctor.range i) :=
    isClosedSubspace_range_of_isClosedImmersion B S hS i hZ hi
  have hWrange : Set.range (pointsMap B S hS (Subfunctor.range i).toFunctor
      (Subfunctor.range i).ι) = Set.range (pointsMap B S hS Z i) :=
    range_pointsMap_ι_range B S hS i
  have hpo : IsProperOver B S hS hX hY f hf _ hTcl :=
    isProperOver_of_subset B S hS hX hY f hf _ _ hTcl hcl hsub hp
  have hWproper : IsProper B S hS ((Subfunctor.range i).ι ≫ f) :=
    (exists_isProper_closedSubspace_iff_forall B S hS hX hY f hf _ hTcl).1
      ((isProper_reducedClosedSubspace_iff_exists B S hS hX hY f hf _ hTcl).1 hpo)
      (Subfunctor.range i) hW hWrange
  have heq : i ≫ f = Subfunctor.toRange i ≫ ((Subfunctor.range i).ι ≫ f) := by
    rw [← Category.assoc, Subfunctor.toRange_ι]
  rw [heq]
  exact isProper_comp' B S hS (Subfunctor.toRange i) ((Subfunctor.range i).ι ≫ f) hW.1 hY
    (isProper_of_isIso B S hS _) hWproper

end AlgebraicGeometry.Space

end
