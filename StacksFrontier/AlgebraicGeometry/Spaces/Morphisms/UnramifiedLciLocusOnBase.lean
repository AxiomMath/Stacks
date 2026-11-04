module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.ClosedImmersions
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PseudoCoherent.LocalCompleteIntersection.KoszulLocusOnBaseUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.RationalMapDomainOfDefinition
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.UnramifiedLocusOnBase
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceSiteFactorization

/-!
# The open subscheme of the base cutting out the unramified local complete intersection locus

Consider a commutative triangle of algebraic spaces over a scheme `S`: a morphism `f : X ⟶ Y`
together with morphisms `p : X ⟶ Z` and `q : Y ⟶ Z` such that `f ≫ q = p`. **Stacks 05X8**
produces an open subspace of `Z` through which a morphism `Z' ⟶ Z` factors exactly when the base
change of `f` along it is unramified, and **Stacks 06CE** produces one for the base change being
a local complete intersection morphism. This file constructs the open subspace of `Z` for the two
conditions together, and, for a base which is an object of the big fppf site, the corresponding
open subscheme of that base.

## Main results

* `exists_isOpenSubspace_factorsThrough_iff_isUnramified_and_isLocalCompleteIntersection`:
  the conjoined locus, as an open subspace of the base.
* `exists_isOpenImmersion_comp_iff_isUnramified_and_isLocalCompleteIntersection_baseChange`:
  the conjoined locus on a base which is an object of the site, as an open subscheme of it.

## Implementation notes

The conjoined locus is the intersection of the two subfunctors, which is again an open subspace
by `AlgebraicGeometry.Space.isOpenSubspace_inf`. Factoring through the intersection is factoring
through both, by the universal property `CategoryTheory.Subfunctor.isPullback_inf` presenting the
intersection as the fibre product of the two inclusions; no point-set argument is needed, and in
particular the equivalence holds for a morphism from an arbitrary presheaf.

Local finite type of `p`, which Stacks 05X8 asks for and Stacks 06CE does not, follows from local
finite presentation by Stacks 0464, so the two hypotheses of Stacks 06CE suffice for both inputs.

Descending the open subspace to an open subscheme of the base is
`AlgebraicGeometry.Space.exists_isOpenImmersion_forall_factorsThrough_iff`, the base change of the
inclusion along the identity.

## References

* [Stacks Project, Tag 0464](https://stacks.math.columbia.edu/tag/0464)
* [Stacks Project, Tag 05X8](https://stacks.math.columbia.edu/tag/05X8)
* [Stacks Project, Tag 06CE](https://stacks.math.columbia.edu/tag/06CE)
* [Stacks Project, Tag 06CL](https://stacks.math.columbia.edu/tag/06CL)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Factoring through an intersection of subfunctors -/

/-- A morphism factors through the intersection of two subfunctors exactly when it factors
through each of them: the intersection is the fibre product of the two inclusions. -/
theorem exists_comp_inf_ι_iff {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (W₁ W₂ : Subfunctor F)
    {Z' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (g : Z' ⟶ F) :
    (∃ r : Z' ⟶ (W₁ ⊓ W₂).toFunctor, r ≫ (W₁ ⊓ W₂).ι = g) ↔
      ((∃ r : Z' ⟶ W₁.toFunctor, r ≫ W₁.ι = g) ∧
        ∃ r : Z' ⟶ W₂.toFunctor, r ≫ W₂.ι = g) := by
  have hle₁ : (W₁ ⊓ W₂).ι =
      Subfunctor.homOfLe (inf_le_left : W₁ ⊓ W₂ ≤ W₁) ≫ W₁.ι :=
    (Subfunctor.homOfLe_ι _).symm
  constructor
  · rintro ⟨r, rfl⟩
    exact ⟨⟨r ≫ Subfunctor.homOfLe (inf_le_left : W₁ ⊓ W₂ ≤ W₁),
        by rw [Category.assoc, Subfunctor.homOfLe_ι]⟩,
      ⟨r ≫ Subfunctor.homOfLe (inf_le_right : W₁ ⊓ W₂ ≤ W₂),
        by rw [Category.assoc, Subfunctor.homOfLe_ι]⟩⟩
  · rintro ⟨⟨r₁, h₁⟩, ⟨r₂, h₂⟩⟩
    refine ⟨(Subfunctor.isPullback_inf W₁ W₂).lift r₂ r₁ (by rw [h₁, h₂]), ?_⟩
    rw [hle₁, ← Category.assoc, (Subfunctor.isPullback_inf W₁ W₂).lift_snd, h₁]

/-! ### The conjoined unramified local complete intersection locus on the base -/

section OnBase

variable {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **The open locus on the base over which a base change is unramified and a local complete
intersection morphism.** Let `f : X ⟶ Y` be a morphism of algebraic spaces over `S` whose source
and target are given over a third algebraic space `Z` by morphisms `p : X ⟶ Z` and `q : Y ⟶ Z` with
`f ≫ q = p`. If `p` is flat, locally of finite presentation and closed and `q` is flat and locally
of finite presentation, then there is an open subspace `W` of `Z` through which a morphism `Z' ⟶ Z`
from an algebraic space factors exactly when the base change of `f` along it is both unramified and
a local complete intersection morphism. -/
theorem exists_isOpenSubspace_factorsThrough_iff_isUnramified_and_isLocalCompleteIntersection
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hZ : IsAlgebraicSpace B S hS Z) (f : X ⟶ Y) (p : X ⟶ Z) (q : Y ⟶ Z) (hfq : f ≫ q = p)
    (hpflat : IsFlat B S hS p) (hplfp : IsLocallyOfFinitePresentation B S hS p)
    (hpc : IsClosedMorphism B S hS p) (hqflat : IsFlat B S hS q)
    (hqlfp : IsLocallyOfFinitePresentation B S hS q) :
    ∃ W : Subfunctor Z, IsOpenSubspace B S hS W ∧
      ∀ (Z' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (_ : IsAlgebraicSpace B S hS Z') (g : Z' ⟶ Z),
        (∃ r : Z' ⟶ W.toFunctor, r ≫ W.ι = g) ↔
          (IsUnramified B S hS (baseChangeOverBase B S hS f p q hfq g) ∧
            IsLocalCompleteIntersection B S hS
              (baseChangeOverBase B S hS f p q hfq g)) := by
  obtain ⟨W₁, hW₁, hW₁prop⟩ :=
    exists_isOpenSubspace_forall_factorsThrough_iff_isUnramified_baseChange B S hS hX hY hZ
      f p q hfq (isLocallyOfFiniteType_of_isLocallyOfFinitePresentation B S hS hplfp) hpc
  obtain ⟨W₂, hW₂, hW₂prop⟩ :=
    exists_isOpenSubspace_factorsThrough_iff_isLocalCompleteIntersection B S hS hX hY hZ
      f p q hfq hpflat hplfp hpc hqflat hqlfp
  refine ⟨W₁ ⊓ W₂, isOpenSubspace_inf B S hS hZ W₁ W₂ hW₁ hW₂, fun Z' hZ' g => ?_⟩
  rw [exists_comp_inf_ι_iff B S hS W₁ W₂ g, hW₁prop Z' hZ' g, hW₂prop Z' hZ' g]

end OnBase

/-! ### The locus as an open subscheme of a base in the site -/

/-- **The open subscheme of a represented base cutting out the unramified local complete
intersection locus.** Let `f : X ⟶ Y` be a morphism of algebraic spaces over `S` whose source and
target are given over the algebraic space represented by an object `A` of the big fppf site by
morphisms `p` and `q` with `f ≫ q = p`. If `p` is flat, locally of finite presentation and closed
and `q` is flat and locally of finite presentation, then there is an object `V` of the site and a
morphism `s : V ⟶ A` whose underlying morphism of schemes is an open immersion such that a morphism
`g : A' ⟶ A` of the site factors through `s` exactly when the base change of `f` along `g` is
unramified and a local complete intersection morphism. -/
theorem exists_isOpenImmersion_comp_iff_isUnramified_and_isLocalCompleteIntersection_baseChange
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (A : BigFppfOver B S hS) (f : X ⟶ Y)
    (p : X ⟶ yoneda.obj A) (q : Y ⟶ yoneda.obj A) (hfq : f ≫ q = p)
    (hpflat : IsFlat B S hS p) (hplfp : IsLocallyOfFinitePresentation B S hS p)
    (hpc : IsClosedMorphism B S hS p) (hqflat : IsFlat B S hS q)
    (hqlfp : IsLocallyOfFinitePresentation B S hS q) :
    ∃ (V : BigFppfOver B S hS) (s : V ⟶ A),
      _root_.AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map s) ∧
        ∀ (A' : BigFppfOver B S hS) (g : A' ⟶ A),
          (∃ t : A' ⟶ V, t ≫ s = g) ↔
            (IsUnramified B S hS
                (baseChangeOverBase B S hS f p q hfq (yoneda.map g)) ∧
              IsLocalCompleteIntersection B S hS
                (baseChangeOverBase B S hS f p q hfq (yoneda.map g))) := by
  obtain ⟨W, hW, hWprop⟩ :=
    exists_isOpenSubspace_factorsThrough_iff_isUnramified_and_isLocalCompleteIntersection
      B S hS hX hY (isAlgebraicSpace_yoneda B S hS A) f p q hfq hpflat hplfp hpc hqflat hqlfp
  obtain ⟨V, s, hs, hsprop⟩ :=
    exists_isOpenImmersion_forall_factorsThrough_iff B S hS W hW.2
  refine ⟨V, s, hs, fun A' g => ?_⟩
  rw [hsprop A' g, hWprop (yoneda.obj A') (isAlgebraicSpace_yoneda B S hS A') (yoneda.map g)]

end AlgebraicGeometry.Space

end
