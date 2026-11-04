module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Correspondences.Transpose
public import StacksCore.Tactic.StacksAttribute

/-!
# Correspondences to and from the base point

A correspondence of degree `r` from `X` to `Y` lives on the product `X ×_S Y`. When one of the
two factors is the base itself the product collapses: `X ×_{Spec k} Spec k ≅ X` through the
first projection, and `Spec k ×_{Spec k} X ≅ X` through the second. Transporting Chow classes
across those two projections identifies the correspondences having the base as a factor with
rational Chow groups of the other factor:

* `Corrʳ(X, Spec k) = CH_{-r}(X) ⊗ ℚ`, the target contributing dimension `0`;
* `Corrʳ(Spec k, X) = CH^r(X) ⊗ ℚ = A_{d-r}(X) ⊗ ℚ` for `X` of dimension `d`.

These are parts (2) and (3) of Stacks 0FG0, whose proof in the source is exactly this
bookkeeping of where the cycles live.

## Main definitions

* `Stacks.WeilCohomology.baseUnitRightIso`: the projection `X ×_{Spec k} Spec k ≅ X`.
* `Stacks.WeilCohomology.chowGroupEquivPullbackUnitRight` and
  `Stacks.WeilCohomology.chowGroupEquivPullbackUnitLeft`: the induced isomorphisms of Chow
  groups, pushforward along the two projections.
* `Stacks.WeilCohomology.correspondenceToPointEquiv`: **Stacks 0FG0 (2)**, the canonical
  `ℚ`-linear isomorphism `CH_{-r}(X) ⊗ ℚ ≃ Corrʳ(X, Spec k)`.
* `Stacks.WeilCohomology.correspondenceFromPointEquiv`: **Stacks 0FG0 (3)**, the canonical
  `ℚ`-linear isomorphism `CH^r(X) ⊗ ℚ ≃ Corrʳ(Spec k, X)`.

## Main results

* `Stacks.WeilCohomology.chowGroupEquivPullbackUnitRight_symm_apply` and
  `Stacks.WeilCohomology.chowGroupEquivPullbackUnitLeft_symm_apply` identify the inverses of the
  two transports with proper pushforward along the collapsing projection. This is what makes the
  identifications of Stacks 0FG0 (2) and (3) *canonical*: they are not an arbitrary choice of
  isomorphism but the one induced by the projection of the product onto its non-trivial factor.
* `Stacks.WeilCohomology.correspondenceToPointEquiv_tmul` and
  `Stacks.WeilCohomology.correspondenceFromPointEquiv_tmul` evaluate the two identifications on
  pure tensors.

## Implementation notes

**What is and is not covered.** Stacks 0FG0 has four parts, and only the two *identifications*
of parts (2) and (3) are proved here. Both `@[stacks 0FG0]` attributes are therefore keyed. Not
covered: part (1), bilinearity and associativity of composition of correspondences; the second
halves of (2) and (3), that pullback and pushforward by correspondences correspond to
composition; and part (4), compatibility of composition with pushforward and pullback of cycles.
All four of those speak about *composition of correspondences*,
`c' ∘ c = pr₁₃,*(pr₁₂^* c · pr₂₃^* c')`, which is not available in this repository: it needs the
intersection product on a smooth projective scheme (Stacks 0FC1) together with the Gysin
pullback of Stacks 0FFB and the projection formula of Stacks 0FFC, none of which is formalized
here. Composition is accordingly carried as data where it is needed, in
`Stacks.WeilCohomology.CorrespondenceCalculus`; nothing in this file assumes it.

**Degrees and dimensions.** Following
`StacksFrontier.AlgebraicGeometry.WeilCohomology.Correspondences.Transpose`,
`Stacks.WeilCohomology.Correspondence C sX sY e r` is `A_{e-r}(X ×_S Y) ⊗ ℚ`, with `e` the
dimension of the second factor supplied as a parameter rather than derived from `Y`. For
`Y = Spec k` that parameter is `0`, and `Corrʳ(X, Spec k) = A_{-r}(X) ⊗ ℚ = CH_{-r}(X) ⊗ ℚ`. For
`X = Spec k` and a second factor of dimension `d` it is `A_{d-r}(X) ⊗ ℚ`, which is
`CH^r(X) ⊗ ℚ` in the codimension grading of the source; equidimensionality of `X` is not
imposed, exactly as in `Transpose`, since with the dimension supplied as a parameter the
statement is the intended one for any scheme locally of finite type over the base.

**No instance of Stacks 02S2 is needed.** Both transports are pushforward along an
*isomorphism*, for which `Stacks.Chow.chowGroupEquivOfIso` is unconditional.

## References

* [Stacks Project, Tag 0FG0](https://stacks.math.columbia.edu/tag/0FG0)
* [Stacks Project, Tag 0FFZ](https://stacks.math.columbia.edu/tag/0FFZ)
-/

open AlgebraicGeometry

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Stacks.Chow

universe u

namespace Stacks.WeilCohomology

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]

/-! ### Collapsing a product one of whose factors is the base -/

/-- The first projection `X ×_{Spec k} Spec k ≅ X`: the base change of the identity of the base
along `sX` is an isomorphism. The companion isomorphism `Spec k ×_{Spec k} X ≅ X` is
`Stacks.Chow.identityBaseChangeIso sX`, whose forward map is the second projection. -/
abbrev baseUnitRightIso : pullback sX (𝟙 C.S) ≅ X :=
  asIso (pullback.fst sX (𝟙 C.S))

/-- Transport of Chow groups along the first projection `X ×_{Spec k} Spec k ≅ X`. -/
def chowGroupEquivPullbackUnitRight (n : ℤ) :
    chowGroup C sX n ≃+ chowGroup C (pullback.fst sX (𝟙 C.S) ≫ sX) n :=
  (chowGroupEquivOfIso C (pullback.fst sX (𝟙 C.S) ≫ sX) sX (pullback.fst sX (𝟙 C.S)) rfl n).symm

/-- The transport along `X ×_{Spec k} Spec k ≅ X` is inverse to proper pushforward along the
first projection. -/
@[simp]
theorem chowGroupEquivPullbackUnitRight_symm_apply (n : ℤ)
    (x : chowGroup C (pullback.fst sX (𝟙 C.S) ≫ sX) n) :
    (chowGroupEquivPullbackUnitRight C sX n).symm x =
      chowPushforwardOfIso C (pullback.fst sX (𝟙 C.S) ≫ sX) sX (pullback.fst sX (𝟙 C.S)) rfl n
        x :=
  rfl

/-- Transport of Chow groups along the second projection `Spec k ×_{Spec k} X ≅ X`. -/
def chowGroupEquivPullbackUnitLeft (n : ℤ) :
    chowGroup C sX n ≃+ chowGroup C (pullback.fst (𝟙 C.S) sX ≫ 𝟙 C.S) n :=
  (chowGroupEquivOfIso C (pullback.fst (𝟙 C.S) sX ≫ 𝟙 C.S) sX (pullback.snd (𝟙 C.S) sX)
    pullback.condition.symm n).symm

/-- The transport along `Spec k ×_{Spec k} X ≅ X` is inverse to proper pushforward along the
second projection. -/
@[simp]
theorem chowGroupEquivPullbackUnitLeft_symm_apply (n : ℤ)
    (x : chowGroup C (pullback.fst (𝟙 C.S) sX ≫ 𝟙 C.S) n) :
    (chowGroupEquivPullbackUnitLeft C sX n).symm x =
      chowPushforwardOfIso C (pullback.fst (𝟙 C.S) sX ≫ 𝟙 C.S) sX (pullback.snd (𝟙 C.S) sX)
        pullback.condition.symm n x :=
  rfl

/-! ### The two identifications of Stacks 0FG0 -/

/-- **Stacks Project, Tag 0FG0 (2).** The canonical `ℚ`-linear isomorphism

  `CH_{-r}(X) ⊗ ℚ = Corrʳ(X, Spec k)`,

pushforward along the collapsing projection `X ×_{Spec k} Spec k ≅ X`. The target of the
correspondence is the base, which contributes dimension `0`, so a correspondence of degree `r`
from `X` to `Spec k` is a rational Chow class of dimension `-r`. -/
@[stacks 0FG0 "CH_{-r}(X) ⊗ Q = Corr^r(X, Spec k)"]
def correspondenceToPointEquiv (r : ℤ) :
    TensorProduct ℤ ℚ (chowGroup C sX (-r)) ≃ₗ[ℚ] Correspondence C sX (𝟙 C.S) 0 r :=
  TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl ℚ ℚ)
    (((chowGroupEquivPullbackUnitRight C sX (-r)).trans
      (chowGroupDegreeEquiv C (pullback.fst sX (𝟙 C.S) ≫ sX)
        (show (-r : ℤ) = 0 - r by omega))).toIntLinearEquiv)

/-- `Stacks.WeilCohomology.correspondenceToPointEquiv` on a pure tensor `q ⊗ α`: it keeps `q`
and transports `α` along `X ×_{Spec k} Spec k ≅ X`, then reindexes its dimension `-r` as
`0 - r`. -/
@[simp]
theorem correspondenceToPointEquiv_tmul (r : ℤ) (q : ℚ) (α : chowGroup C sX (-r)) :
    correspondenceToPointEquiv C sX r (q ⊗ₜ[ℤ] α) =
      q ⊗ₜ[ℤ] chowGroupDegreeEquiv C (pullback.fst sX (𝟙 C.S) ≫ sX)
        (show (-r : ℤ) = 0 - r by omega) (chowGroupEquivPullbackUnitRight C sX (-r) α) :=
  rfl

/-- **Stacks Project, Tag 0FG0 (3).** The canonical `ℚ`-linear isomorphism

  `CH^r(X) ⊗ ℚ = Corrʳ(Spec k, X)`,

pushforward along the collapsing projection `Spec k ×_{Spec k} X ≅ X`. The source of the
correspondence is the base, which contributes dimension `0`, so a correspondence of degree `r`
from `Spec k` to a target of dimension `d` is a rational Chow class of dimension `d - r`, which
is codimension `r`. -/
@[stacks 0FG0 "CH^r(X) ⊗ Q = Corr^r(Spec k, X)"]
def correspondenceFromPointEquiv (d r : ℤ) :
    TensorProduct ℤ ℚ (chowGroup C sX (d - r)) ≃ₗ[ℚ] Correspondence C (𝟙 C.S) sX d r :=
  TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl ℚ ℚ)
    (chowGroupEquivPullbackUnitLeft C sX (d - r)).toIntLinearEquiv

/-- `Stacks.WeilCohomology.correspondenceFromPointEquiv` on a pure tensor `q ⊗ α`: it keeps `q`
and transports `α` along `Spec k ×_{Spec k} X ≅ X`. -/
@[simp]
theorem correspondenceFromPointEquiv_tmul (d r : ℤ) (q : ℚ) (α : chowGroup C sX (d - r)) :
    correspondenceFromPointEquiv C sX d r (q ⊗ₜ[ℤ] α) =
      q ⊗ₜ[ℤ] chowGroupEquivPullbackUnitLeft C sX (d - r) α :=
  rfl

end Stacks.WeilCohomology

end
