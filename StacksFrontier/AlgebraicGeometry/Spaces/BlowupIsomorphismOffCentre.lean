module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.BlowupUniversalLift
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.EffectiveCartierEtaleEquiv
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceCorrespondence
public import StacksFrontier.AlgebraicGeometry.Spaces.WeilDivisor

/-!
# A blowup is an isomorphism away from its centre

Let `S` be a scheme, let `X` be an algebraic space over `S`, let `Z ⊆ X` be a closed subspace
and let `b : X' ⟶ X` be the blowup of `X` in `Z`.  Stacks 085T, part (1) says that the
restriction of `b` over the open complement `X ∖ Z` is an isomorphism

```
b|_{b⁻¹(X ∖ Z)} : b⁻¹(X ∖ Z) ⟶ X ∖ Z,
```

and part (2) says that the exceptional divisor `E = b⁻¹(Z)` is an effective Cartier divisor on
`X'`.  Both are proved here.

## Main definitions

* `AlgebraicGeometry.Space.openComplementOfClosedSubspace` is the open subspace `X ∖ Z`
  complementary to a closed subspace, obtained from the order isomorphism of Stacks 03BZ
  between open subspaces and open sets of points.

## Main results

* `AlgebraicGeometry.Space.isEffectiveCartierDivisor_of_isEmpty_points`: a closed subspace with
  no points is an effective Cartier divisor.
* `AlgebraicGeometry.Space.isEmpty_points_preimage_of_disjoint`: the inverse image of a closed
  subspace along a morphism factoring through an open subspace disjoint from it has no points.
* `AlgebraicGeometry.Space.isIso_fromPreimage_openComplement`: **Stacks 085T, part (1)**, the
  blowup is an isomorphism over the complement of its centre.
* `AlgebraicGeometry.Space.isEffectiveCartierDivisor_exceptionalDivisor`: **Stacks 085T,
  part (2)**, the exceptional divisor of the blowup is an effective Cartier divisor on the
  blowup.

## Implementation notes

The source proves both clauses by base change to a surjective étale scheme chart, where they
are the scheme-level Stacks 02OS.  The proof here is instead the universal-property proof, which
does not need a construction of the blowup — not available for algebraic spaces, see the module
documentation of `StacksFrontier/AlgebraicGeometry/Spaces/AdmissibleBlowup.lean` — and uses only
finality of `b` in the category `𝒞` of Stacks 085U, in the form
`AlgebraicGeometry.Space.IsBlowupAlong.existsUnique_lift`.

Both the complement `U = X ∖ Z` and the inverse image `b⁻¹(U)` are algebraic spaces over `X`
along which `Z` pulls back to a closed subspace with *no points*, hence an effective Cartier
divisor; so each receives a unique morphism to `X'` over `X`.  The morphism `U ⟶ X'` factors
through `b⁻¹(U)` because its composite with `b` is the inclusion of `U`, and the two composites
with `b⁻¹(U) ⟶ U` are forced by uniqueness of the lift.  That a closed subspace with no points
is an effective Cartier divisor is condition (4) of Stacks 083C holding vacuously, together with
the implication (4) ⟹ (1) of
`AlgebraicGeometry.Space.isEffectiveCartierDivisor_of_hasAffinePrincipalEtaleNeighborhoods`.

Part (2) is immediate: in the rendering of "the blowup" by the universal property of Stacks 085U
it is the assertion that `b` is an *object* of the category `𝒞`, which is half of being its final
object.  Its content — that the relative `Proj` of the Rees algebra lies in `𝒞` — belongs to the
missing construction of Stacks 085Q, so nothing more can be said here; the statement itself is
exactly part (2) of the source.

Part (3), the canonical isomorphism `𝒪_{X'}(-1) ≅ 𝒪_{X'}(E)`, is not stated: it speaks about the
twists `𝒪_{X'}(n)` of the relative `Proj`, which this library does not produce — see the
implementation notes of `StacksFrontier/AlgebraicGeometry/Spaces/RelativeProj.lean`.

## References

* [Stacks Project, Tag 085T](https://stacks.math.columbia.edu/tag/085T)
* [Stacks Project, Tag 085U](https://stacks.math.columbia.edu/tag/085U)
* [Stacks Project, Tag 083B](https://stacks.math.columbia.edu/tag/083B)
* [Stacks Project, Tag 083C](https://stacks.math.columbia.edu/tag/083C)
* [Stacks Project, Tag 083Y](https://stacks.math.columbia.edu/tag/083Y)
* [Stacks Project, Tag 03BZ](https://stacks.math.columbia.edu/tag/03BZ)
* [Stacks Project, Tag 04CD](https://stacks.math.columbia.edu/tag/04CD)
* [Stacks Project, Tag 02OS](https://stacks.math.columbia.edu/tag/02OS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Closed subspaces with no points -/

/-- **A closed subspace with no points is an effective Cartier divisor.**

Condition (4) of Stacks 083C — every point of the subspace has an affine étale neighbourhood of
the ambient space on which the subspace is cut out by a nonzerodivisor — holds vacuously, and
it implies effective Cartier-ness by Stacks 083C. -/
theorem isEffectiveCartierDivisor_of_isEmpty_points (X : AlgebraicSpaces B S hS)
    (D : ClosedSubspaces B S hS X.1) (h : IsEmpty (points B S hS D.1.toFunctor)) :
    IsEffectiveCartierDivisor B S hS X D :=
  isEffectiveCartierDivisor_of_hasAffinePrincipalEtaleNeighborhoods B S hS X D
    fun x => (h.false x).elim

/-- **The inverse image of a subspace along a morphism whose points miss it has no points.**

The hypothesis is on the point-image of the morphism itself, which is the weakest form the
argument needs: a point of the inverse image would lie in both ranges. -/
theorem isEmpty_points_preimage_of_disjoint_range {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (f : G ⟶ F) (Z : Subfunctor F)
    (hdisj : Disjoint (Set.range (pointsMap B S hS G f))
      (Set.range (pointsMap B S hS Z.toFunctor Z.ι))) :
    IsEmpty (points B S hS (Z.preimage f).toFunctor) := by
  refine ⟨fun x => ?_⟩
  have hp := congrArg (fun k => pointsMap B S hS (Z.preimage f).toFunctor k x)
    (CategoryTheory.Subfunctor.isPullback_preimage f Z).w
  rw [pointsMap_comp_apply, pointsMap_comp_apply] at hp
  exact Set.disjoint_left.mp hdisj ⟨_, rfl⟩ ⟨_, hp⟩

/-- **The inverse image of a subspace along a morphism factoring through a disjoint subspace has
no points.**

A point of the inverse image gives a point of the ambient space lying both in the image of the
subspace and in the image of the subspace factored through, and those two images are
disjoint. -/
theorem isEmpty_points_preimage_of_disjoint {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (Z U : Subfunctor F)
    (hdisj : Disjoint (subspacePointSet B S hS F Z) (subspacePointSet B S hS F U))
    (f : G ⟶ F) (k : G ⟶ U.toFunctor) (hk : k ≫ U.ι = f) :
    IsEmpty (points B S hS (Z.preimage f).toFunctor) := by
  refine isEmpty_points_preimage_of_disjoint_range B S hS f Z (hdisj.symm.mono_left ?_)
  rintro _ ⟨x, rfl⟩
  exact ⟨pointsMap B S hS _ k x, by rw [← hk, pointsMap_comp_apply]⟩

/-! ### The open complement of a closed subspace -/

/-- **The open complement `X ∖ Z` of a closed subspace.**  The point set of a closed subspace is
closed by Stacks 04CD, and the order isomorphism of Stacks 03BZ turns its complement back into
an open subspace of `X`. -/
def openComplementOfClosedSubspace (X : AlgebraicSpaces B S hS) (Z : ClosedSubspaces B S hS X.1) :
    OpenSubspaces B S hS X.1 :=
  (openSubspacesOrderIso B S hS X.1 X.2).symm
    ⟨(subspacePointSet B S hS X.1 Z.1)ᶜ,
      (isClosed_range_pointsMap_of_isClosedImmersion B S hS X.2 Z.1.ι Z.2.2).isOpen_compl⟩

/-- The points of the open complement of a closed subspace are exactly the points outside
it. -/
theorem subspacePointSet_openComplement (X : AlgebraicSpaces B S hS)
    (Z : ClosedSubspaces B S hS X.1) :
    subspacePointSet B S hS X.1 (openComplementOfClosedSubspace B S hS X Z).1 =
      (subspacePointSet B S hS X.1 Z.1)ᶜ := by
  have h : openSubspacesOrderIso B S hS X.1 X.2 (openComplementOfClosedSubspace B S hS X Z) =
      ⟨(subspacePointSet B S hS X.1 Z.1)ᶜ,
        (isClosed_range_pointsMap_of_isClosedImmersion B S hS X.2 Z.1.ι Z.2.2).isOpen_compl⟩ :=
    OrderIso.apply_symm_apply _ _
  exact (openSubspacesOrderIso_apply B S hS X.1 X.2
      (openComplementOfClosedSubspace B S hS X Z)).symm.trans
    (congrArg (fun W : TopologicalSpace.Opens (points B S hS X.1) => W.1) h)

/-- The centre of a blowup is disjoint from its open complement. -/
theorem disjoint_subspacePointSet_openComplement (X : AlgebraicSpaces B S hS)
    (Z : ClosedSubspaces B S hS X.1) :
    Disjoint (subspacePointSet B S hS X.1 Z.1)
      (subspacePointSet B S hS X.1 (openComplementOfClosedSubspace B S hS X Z).1) := by
  rw [subspacePointSet_openComplement]
  exact disjoint_compl_right

/-! ### The two clauses of Stacks 085T -/

variable {B S hS}

/-- The exceptional divisor `E = b⁻¹(Z)` of the blowup `b : X' ⟶ X` of an algebraic space `X`
in a closed subspace `Z` is an effective Cartier divisor on `X'`.

No `@[stacks 085T]` attribute is attached to this projection. Under the rendering of "the blowup
of `X` in `Z`" by the universal property of Stacks 085U, being an object of the category `𝒞` of
spaces over `X` on which the inverse image of `Z` is an effective Cartier divisor is one half of
being its final object, so the statement is a component of the hypothesis and its proof is that
component. The mathematical content of part (2) of Stacks 085T is that the relative `Proj` of the
Rees algebra has this property, which belongs to the construction of Stacks 085Q. -/
theorem isEffectiveCartierDivisor_exceptionalDivisor {X X' : AlgebraicSpaces B S hS}
    {Z : ClosedSubspaces B S hS X.1} {b : X' ⟶ X} (hb : IsBlowupAlong B S hS Z b) :
    IsEffectiveCartierDivisor B S hS X'
      ⟨Z.1.preimage b.hom,
        isClosedSubspace_preimage B S hS b.hom Z.1 X.2 X'.2 Z.2⟩ :=
  hb.isPullbackDefined

/-- **Stacks 085T, part (1).** The blowup `b : X' ⟶ X` of an algebraic space `X` in a closed
subspace `Z` is an isomorphism over the open complement of `Z`: the restriction
`b⁻¹(X ∖ Z) ⟶ X ∖ Z` of `b` is an isomorphism.

Both `X ∖ Z` and `b⁻¹(X ∖ Z)` are algebraic spaces over `X` on which the inverse image of `Z`
has no points, hence is an effective Cartier divisor, so each admits a unique morphism to `X'`
over `X` by the universal property of Stacks 085U.  The morphism out of `X ∖ Z` lands in
`b⁻¹(X ∖ Z)` and is inverse to the restriction of `b`, the two composites being identified with
the identities by the uniqueness of those lifts. -/
@[stacks 085T "part (1): the blowup is an isomorphism away from the centre"]
theorem isIso_fromPreimage_openComplement {X X' : AlgebraicSpaces B S hS}
    {Z : ClosedSubspaces B S hS X.1} {b : X' ⟶ X} (hb : IsBlowupAlong B S hS Z b) :
    IsIso ((openComplementOfClosedSubspace B S hS X Z).1.fromPreimage b.hom) := by
  set U := openComplementOfClosedSubspace B S hS X Z with hU
  have hdisj := disjoint_subspacePointSet_openComplement B S hS X Z
  set Y : AlgebraicSpaces B S hS := ⟨U.1.toFunctor, U.2.1⟩ with hY
  have hPalg : IsAlgebraicSpace B S hS (U.1.preimage b.hom).toFunctor :=
    isAlgebraicSpace_of_iso B S hS
      (Subfunctor.isPullback_preimage b.hom U.1).isoPullback.symm
      (isAlgebraicSpace_pullback B S hS U.1.ι b.hom U.2.1 X'.2 X.2)
  set P : AlgebraicSpaces B S hS := ⟨(U.1.preimage b.hom).toFunctor, hPalg⟩ with hP
  set p : P.1 ⟶ Y.1 := U.1.fromPreimage b.hom with hp
  -- The inverse image of `Z` in the complement is an effective Cartier divisor.
  have hYcart : IsPullbackDefined B S hS (ObjectProperty.homMk U.1.ι : Y ⟶ X) Z :=
    isEffectiveCartierDivisor_of_isEmpty_points B S hS Y _
      (isEmpty_points_preimage_of_disjoint B S hS Z.1 U.1 hdisj U.1.ι (𝟙 _)
        (Category.id_comp _))
  obtain ⟨l, hl, -⟩ := hb.existsUnique_lift (ObjectProperty.homMk U.1.ι : Y ⟶ X) hYcart
  have hlhom : l.hom ≫ b.hom = U.1.ι := congrArg (fun φ : Y ⟶ X => φ.hom) hl
  -- The lift out of the complement factors through the inverse image of the complement.
  have hrange : Subfunctor.range l.hom ≤ U.1.preimage b.hom := by
    rintro T x ⟨v, rfl⟩
    change b.hom.app T (l.hom.app T v) ∈ U.1.obj T
    exact (congrArg (fun φ => φ.app T v) hlhom) ▸ v.2
  set inv : Y.1 ⟶ P.1 := Subfunctor.lift l.hom hrange with hinv
  have hinvι : inv ≫ (U.1.preimage b.hom).ι = l.hom := Subfunctor.lift_ι _ _
  have hright : inv ≫ p = 𝟙 Y.1 := by
    refine (cancel_mono U.1.ι).1 ?_
    rw [Category.assoc, hp, Subfunctor.fromPreimage_ι, ← Category.assoc, hinvι, hlhom,
      Category.id_comp]
  -- The inverse image of `Z` in the inverse image of the complement is likewise an effective
  -- Cartier divisor.
  have hPcart : IsPullbackDefined B S hS
      (ObjectProperty.homMk ((U.1.preimage b.hom).ι ≫ b.hom) : P ⟶ X) Z :=
    isEffectiveCartierDivisor_of_isEmpty_points B S hS P _
      (isEmpty_points_preimage_of_disjoint B S hS Z.1 U.1 hdisj
        ((U.1.preimage b.hom).ι ≫ b.hom) p (Subfunctor.fromPreimage_ι _ _))
  obtain ⟨c, -, huniq⟩ := hb.existsUnique_lift
    (ObjectProperty.homMk ((U.1.preimage b.hom).ι ≫ b.hom) : P ⟶ X) hPcart
  have hleft : p ≫ inv = 𝟙 P.1 := by
    refine (cancel_mono (U.1.preimage b.hom).ι).1 ?_
    rw [Category.assoc, hinvι, Category.id_comp]
    have h₁ : (ObjectProperty.homMk (p ≫ l.hom) : P ⟶ X') ≫ b =
        (ObjectProperty.homMk ((U.1.preimage b.hom).ι ≫ b.hom) : P ⟶ X) := by
      refine ObjectProperty.hom_ext _ ?_
      change (p ≫ l.hom) ≫ b.hom = (U.1.preimage b.hom).ι ≫ b.hom
      rw [Category.assoc, hlhom, hp]
      exact Subfunctor.fromPreimage_ι _ _
    have h₂ : (ObjectProperty.homMk (U.1.preimage b.hom).ι : P ⟶ X') ≫ b =
        (ObjectProperty.homMk ((U.1.preimage b.hom).ι ≫ b.hom) : P ⟶ X) :=
      ObjectProperty.hom_ext _ rfl
    exact congrArg (fun φ : P ⟶ X' => φ.hom) ((huniq _ h₁).trans (huniq _ h₂).symm)
  exact ⟨inv, hleft, hright⟩

end AlgebraicGeometry.Space

end
