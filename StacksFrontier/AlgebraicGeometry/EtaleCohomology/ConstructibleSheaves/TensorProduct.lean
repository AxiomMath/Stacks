module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ConstantSheafHom
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.SimultaneousStratification
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.WeakSerre.FiniteTypeLocallyConstant
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LocallyConstantPullback.SmallEtaleStability
public import StacksFrontier.CategoryTheory.Sites.InverseImageTensor
public import StacksFrontier.CategoryTheory.Sites.LocallyConstant.TensorFiniteType
import StacksCore.Tactic.StacksAttribute

/-!
# Tensor products of constructible étale sheaves of modules

Let `X` be a scheme of a big étale site and let `Λ` be a Noetherian ring. The tensor product of
two constructible sheaves of `Λ`-modules on `X_étale` is a constructible sheaf of `Λ`-modules.
This is Stacks 095I.

## Main definitions

* `AlgebraicGeometry.smallEtaleSheafPullbackTensorIso` — inverse image along a morphism of the
  big étale site commutes with the tensor product of sheaves of `Λ`-modules.

## Main results

* `Stacks.EtaleCohomology.isConstructibleModuleSheaf_tensor` — Stacks 095I.

## Implementation notes

Constructibility is `AlgebraicGeometry.IsConstructibleModuleSheaf`, part (3) of Tag 03RW: on a
finite partition of every affine open into constructible locally closed subschemes, the inverse
image of the sheaf is locally constant with finitely generated values. The tensor product is the
one of `CategoryTheory.Sheaf.monoidalCategory`, the sheafification of the objectwise tensor
product over the constant sheaf `Λ`, which Mathlib does not make an instance and which is
therefore activated as a local instance; it is the same tensor product as in Tags 093V and 095D.

The proof is the source's. The definition already quantifies over the affine opens, so the
reduction to the affine case is in the statement rather than in the proof; what remains is to
replace the two partitions by one, which is
`AlgebraicGeometry.exists_stratification_isStratifiedSheaf_pair` applied to local constancy of
finite type, and then on each stratum to move the inverse image across the tensor product, which
is `AlgebraicGeometry.smallEtaleSheafPullbackTensorIso` — the source's "pullbacks commute with
tensor products" — and to apply the local statement
`Stacks.ConstantSheaf.isFiniteTypeLocallyConstantModuleSheaf_tensor`, the finite type refinement
of Tag 095D.

`Λ` Noetherian is carried because `AlgebraicGeometry.IsConstructibleModuleSheaf` is only defined
for a Noetherian coefficient ring, as in the source; the tensor product of two finitely
generated modules is finitely generated over any commutative ring.

The coefficient universe is `max (u + 1) w` for a big étale site in universe `u`. This is not a
convenience: the small étale site has objects in `Type (u + 1)` and morphisms in `Type u`, and
`ModuleCat.{s} Λ` is monoidal only for `Λ : Type s`, so `s` must dominate `u + 1` for the
colimits computing an inverse image to exist and for the tensor product of sheaves to be
available at all. It is the universe hypothesis `UnivLE.{u + 1, w}` of Tags 095C (2) and 095D in
the form which keeps `w` free, and at this universe every sheafification hypothesis is
automatic; only the right-adjointness of small étale pushforward remains a hypothesis, and that
one is already part of the statement of Tag 03RW (3).

## References

* [Stacks Project, Tag 095I](https://stacks.math.columbia.edu/tag/095I)
* [Stacks Project, Tag 095D](https://stacks.math.columbia.edu/tag/095D)
* [Stacks Project, Tag 03RW](https://stacks.math.columbia.edu/tag/03RW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open Stacks.ConstantSheaf

universe w u

attribute [local instance] Sheaf.monoidalCategory

namespace AlgebraicGeometry

/-- **Inverse image along a morphism of a big étale site commutes with the tensor product of
sheaves of `Λ`-modules.** This is the small étale instance of
`Stacks.InverseImageTensor.sheafPullbackTensorIso`: small étale base change preserves finite
limits, hence is representably flat, so the comma categories computing the inverse image
pointwise are filtered. -/
def smallEtaleSheafPullbackTensorIso (B : BigEtaleSite.{u}) {Z X : B.Scheme} (h : Z ⟶ X)
    (Λ : Type (max (u + 1) w)) [CommRing Λ]
    [((smallEtaleBaseChange B h).sheafPushforwardContinuous (ModuleCat.{max (u + 1) w} Λ)
      (SmallEtale.topology B X.obj X.property)
      (SmallEtale.topology B Z.obj Z.property)).IsRightAdjoint]
    (F G : Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{max (u + 1) w} Λ)) :
    ((smallEtaleBaseChange B h).sheafPullback (ModuleCat.{max (u + 1) w} Λ)
        (SmallEtale.topology B X.obj X.property)
        (SmallEtale.topology B Z.obj Z.property)).obj (F ⊗ G)
      ≅ ((smallEtaleBaseChange B h).sheafPullback (ModuleCat.{max (u + 1) w} Λ)
            (SmallEtale.topology B X.obj X.property)
            (SmallEtale.topology B Z.obj Z.property)).obj F ⊗
          ((smallEtaleBaseChange B h).sheafPullback (ModuleCat.{max (u + 1) w} Λ)
            (SmallEtale.topology B X.obj X.property)
            (SmallEtale.topology B Z.obj Z.property)).obj G :=
  letI : ∀ Y : (SmallEtale B Z.obj Z.property)ᵒᵖ,
      IsFiltered (CostructuredArrow (smallEtaleBaseChange B h).op Y) := fun Y =>
    IsFiltered.of_equivalence
      (structuredArrowOpEquivalence (smallEtaleBaseChange B h) (Opposite.unop Y))
  Stacks.InverseImageTensor.sheafPullbackTensorIso (smallEtaleBaseChange B h) Λ
    (SmallEtale.topology B X.obj X.property) (SmallEtale.topology B Z.obj Z.property) F G

end AlgebraicGeometry

namespace Stacks.EtaleCohomology

/-- **Stacks 095I.** The tensor product of two constructible sheaves of `Λ`-modules on the small
étale site of a scheme, for `Λ` a Noetherian ring, is a constructible sheaf of `Λ`-modules. -/
@[stacks 095I]
theorem isConstructibleModuleSheaf_tensor (B : BigEtaleSite.{u}) (X : B.Scheme)
    (Λ : Type (max (u + 1) w)) [CommRing Λ] [IsNoetherianRing Λ]
    [∀ (S T : B.Scheme) (f : T ⟶ S),
      ((smallEtaleBaseChange B f).sheafPushforwardContinuous (ModuleCat.{max (u + 1) w} Λ)
        (SmallEtale.topology B S.obj S.property)
        (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
    (F G : Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{max (u + 1) w} Λ))
    (hF : IsConstructibleModuleSheaf B X Λ F) (hG : IsConstructibleModuleSheaf B X Λ G) :
    IsConstructibleModuleSheaf B X Λ (F ⊗ G) := by
  let : ∀ (T : B.Scheme) (V : SmallEtale B T.obj T.property),
      HasWeakSheafify ((SmallEtale.topology B T.obj T.property).over V)
        (ModuleCat.{max (u + 1) w} Λ) := fun _ _ => inferInstance
  intro U
  obtain ⟨r, hr⟩ := exists_stratification_isStratifiedSheaf_pair B X
    (fun T H => IsFiniteTypeLocallyConstant Λ (SmallEtale.topology B T.obj T.property) H)
    (by intro _ _ _ e h; exact isFiniteTypeLocallyConstant_congr _ Λ e h)
    (fun _ _ g _ H h => isFiniteTypeLocallyConstant_smallEtaleSheafPullback B Λ g H h)
    hF hG U
  refine ⟨r, fun k => ?_⟩
  obtain ⟨hFk, hGk⟩ := hr k
  exact isFiniteTypeLocallyConstant_congr _ Λ
    (smallEtaleSheafPullbackTensorIso B (r.inclusion k) Λ F G).symm
    (isFiniteTypeLocallyConstantModuleSheaf_tensor _ Λ _ _ hFk hGk)

end Stacks.EtaleCohomology

end
