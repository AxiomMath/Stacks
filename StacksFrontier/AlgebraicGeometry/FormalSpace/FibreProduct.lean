module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.AffineFibreProduct
public import StacksFrontier.AlgebraicGeometry.FormalSpace.LocalProperty
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RepresentableLocalOnSourceAndTarget
public import StacksFrontier.CategoryTheory.Sites.QuasiCompact.LocallySurjectiveTransfer
import StacksFrontier.AlgebraicGeometry.FormalSpace.AffineCompletionTypes
import StacksFrontier.AlgebraicGeometry.FormalSpace.DiagonalRepresentable

/-!
# Fibre products of formal algebraic spaces

Let `S` be a scheme contained in a big fppf site `B`, let `X` and `Y` be formal algebraic
spaces over `S` and let `p : X ⟶ Z` and `q : Y ⟶ Z` be morphisms of fppf sheaves on the big
fppf site of `S`. **Stacks 0AJ2** says that `X ×_Z Y` is a formal algebraic space over `S` as
soon as the diagonal of `Z` is representable by algebraic spaces.

## Main results

* `AlgebraicGeometry.FormalSpace.isFormalAlgebraicSpace_of_iso`: being a formal algebraic space
  is invariant under isomorphism of fppf sheaves.
* `AlgebraicGeometry.FormalSpace.isFormalAlgebraicSpace_pullback_of_affineStages`: the reduction
  of Stacks 0AJ2 to the case of two affine formal algebraic spaces.
* `AlgebraicGeometry.FormalSpace.isFormalAlgebraicSpace_pullback_of_isSeparated`:
  **Stacks 0AJ2** for a separated base.
* `AlgebraicGeometry.FormalSpace.isFormalAlgebraicSpace_pullback_of_isAffineFormal`: **Stacks
  0AJ2** for a separated base, on two affine formal algebraic spaces.

## Implementation notes

The first step of the proof of Stacks 0AJ2 is carried out in full: an affine étale covering
`{Xᵢ ⟶ X}` pulls back along `X ×_Z Y ⟶ X` to a representable étale covering of `X ×_Z Y`, and
an affine étale covering `{Yⱼ ⟶ Y}` pulls back along `Xᵢ ×_Z Y ⟶ Y` to a representable étale
covering of `Xᵢ ×_Z Y`; two applications of Stacks 0AJ1 therefore reduce the statement to the
fibre products `Xᵢ ×_Z Yⱼ` of two affine formal algebraic spaces, which is the hypothesis
`hstage`. Pulling a covering back is joint surjectivity by
`CategoryTheory.Sheaf.isLocallySurjective_sigmaDesc_pullback_snd` and the two conditions on each
member by `AlgebraicGeometry.FormalSpace.isRepresentableEtale_pullback_snd`.

The second step of the source — writing `Xᵢ` and `Yⱼ` as directed colimits of affine schemes
and recognising `Xᵢ ×_Z Yⱼ` as the colimit of the algebraic spaces `Xλ ×_Z Yμ` along
thickenings, to which Stacks 0AIU applies — is carried out in
`AlgebraicGeometry.FormalSpace.isFormalAlgebraicSpace_pullback_of_representableDiagonal`, which
is Stacks 0AJ2 under the source's own condition on the diagonal of `Z`. It is replaced here,
for a *separated* base, by clause (2) of Stacks 0AJ6, which makes each `Xλ ×_Z Yμ` affine, so
that Stacks 0AN3 clause (1) (`isAffineFormalAlgebraicSpace_pullback`) proves `hstage` outright
and no colimit argument is needed.

The set-theoretic condition of Stacks 0AIS on `X ×_Z Y` and on the intermediate fibre products
`Xᵢ ×_Z Y` is an input to the reduction rather than one of its conclusions, for the same reason
as in `AlgebraicGeometry.FormalSpace.isFormalAlgebraicSpace_of_etaleCover`: it does not follow
from the corresponding conditions on the members of a covering family. Over a base whose
relative products of representables are representable it is a theorem,
`satisfiesSetTheoreticCondition_pullback_of_hasRepresentableRelativeProducts`, and that is how
`isFormalAlgebraicSpace_pullback_of_isSeparated` supplies both of them.

## References

* [Stacks Project, Tag 0AI7](https://stacks.math.columbia.edu/tag/0AI7)
* [Stacks Project, Tag 0AIM](https://stacks.math.columbia.edu/tag/0AIM)
* [Stacks Project, Tag 0AIS](https://stacks.math.columbia.edu/tag/0AIS)
* [Stacks Project, Tag 0AJ1](https://stacks.math.columbia.edu/tag/0AJ1)
* [Stacks Project, Tag 0AJ2](https://stacks.math.columbia.edu/tag/0AJ2)
* [Stacks Project, Tag 0AJ6](https://stacks.math.columbia.edu/tag/0AJ6)
* [Stacks Project, Tag 0AN3](https://stacks.math.columbia.edu/tag/0AN3)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Transport along an isomorphism -/

/-- An isomorphism of fppf sheaves is representable étale: every represented base change of it
has a universe-lifted Yoneda presheaf as its source, and the projection to that presheaf is an
isomorphism. -/
private theorem isRepresentableEtale_of_isIso {X Y : FppfSheaf B S hS} (e : X ⟶ Y) [IsIso e] :
    IsRepresentableEtale B S hS e := by
  have hIso : IsIso e.hom :=
    inferInstanceAs (IsIso ((sheafToPresheaf (BigFppfOver.topology B S hS)
      (Type (u + 1))).map e))
  have hfst : ∀ (U : BigFppfOver B S hS) (ξ : (uliftYoneda.{u + 1}).obj U ⟶ Y.obj),
      IsIso (pullback.fst ξ e.hom) :=
    fun U ξ ↦ (IsPullback.of_hasPullback ξ e.hom).isIso_fst_of_isIso
  refine ⟨fun U ξ ↦ ?_, fun U ξ ↦ ?_⟩
  · have := hfst U ξ
    exact Space.isAlgebraicSpaceULift_of_iso B S hS (asIso (pullback.fst ξ e.hom)).symm
      (Space.isAlgebraicSpaceULift_uliftYoneda B S hS U)
  · have := hfst U ξ
    exact isEtaleULift_of_isIso B S hS (pullback.fst ξ e.hom)

/-- Being a formal algebraic space is invariant under isomorphism of fppf sheaves: an affine
étale covering of one sheaf becomes one of the other after composition with the isomorphism. -/
theorem isFormalAlgebraicSpace_of_iso {X Y : FppfSheaf B S hS} (e : X ≅ Y)
    (hY : IsFormalAlgebraicSpace B S hS Y) : IsFormalAlgebraicSpace B S hS X := by
  let _ : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
  obtain ⟨hset, I, Yi, g, haff, het, hsurj⟩ := hY
  refine ⟨satisfiesSetTheoreticCondition_of_iso B S hS e.symm hset, I, Yi,
    fun i ↦ g i ≫ e.inv, haff, fun i ↦ ?_, ?_⟩
  · exact IsRepresentableEtale.comp B S hS (het i) (isRepresentableEtale_of_isIso B S hS e.inv)
  · have h : Sigma.desc (fun i ↦ g i ≫ e.inv) = Sigma.desc g ≫ e.inv := by
      apply Sigma.hom_ext
      intro i
      simp
    have _ : Epi (Sigma.desc g) := (Sheaf.isLocallySurjective_iff_epi _).mp hsurj
    rw [h]
    exact (Sheaf.isLocallySurjective_iff_epi _).mpr (epi_comp _ _)

/-- Pasting a pullback square of `a` and `h` with a pullback square of `h` and `k`. -/
private theorem isPullback_pullback_fst_snd_comp {C : Type*} [Category C] [HasPullbacks C]
    {T W X Y Z : C} (a : T ⟶ X) {h : W ⟶ X} {k : W ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
    (H : IsPullback h k f g) :
    IsPullback (pullback.fst a h) (pullback.snd a h ≫ k) (a ≫ f) g :=
  (IsPullback.of_hasPullback a _).paste_vert H

/-! ### Stacks 0AJ2 -/

/-- The reduction of **Stacks 0AJ2** to the case of two affine formal algebraic spaces. If the
fibre product over `Z` of any two affine formal algebraic spaces over `Z` is a formal algebraic
space, then so is the fibre product of two formal algebraic spaces over `Z`.

The affine étale coverings of `X` and of `Y` pull back to representable étale coverings of
`X ×_Z Y` and of its members `Xᵢ ×_Z Y`, whose own members are the fibre products
`Xᵢ ×_Z Yⱼ`; two applications of Stacks 0AJ1 assemble `X ×_Z Y` from them. -/
theorem isFormalAlgebraicSpace_pullback_of_affineStages
    {X Y Z : FppfSheaf B S hS} (p : X ⟶ Z) (q : Y ⟶ Z)
    (hX : IsFormalAlgebraicSpace B S hS X)
    (hY : IsFormalAlgebraicSpace B S hS Y)
    (hstage : ∀ (X' Y' : FppfSheaf B S hS) (p' : X' ⟶ Z) (q' : Y' ⟶ Z),
      IsAffineFormalAlgebraicSpace B S hS X' → IsAffineFormalAlgebraicSpace B S hS Y' →
      IsFormalAlgebraicSpace B S hS (pullback p' q'))
    (hset : SatisfiesSetTheoreticCondition B S hS (pullback p q))
    (hstageset : ∀ (X' : FppfSheaf B S hS) (a : X' ⟶ X),
      IsAffineFormalAlgebraicSpace B S hS X' →
      SatisfiesSetTheoreticCondition B S hS (pullback a (pullback.fst p q))) :
    IsFormalAlgebraicSpace B S hS (pullback p q) := by
  classical
  let _ : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
  obtain ⟨-, I, Xi, a, hXiaff, hXiet, hXsurj⟩ := hX
  obtain ⟨-, K, Yj, b, hYjaff, hYjet, hYsurj⟩ := hY
  refine isFormalAlgebraicSpace_of_etaleCover B S hS (pullback p q)
    (fun i ↦ pullback (a i) (pullback.fst p q))
    (fun i ↦ pullback.snd (a i) (pullback.fst p q)) (fun i ↦ ?_)
    (fun i ↦ isRepresentableEtale_pullback_snd B S hS (a i) (pullback.fst p q) (hXiet i))
    (Sheaf.isLocallySurjective_sigmaDesc_pullback_snd (pullback.fst p q) a hXsurj) hset
  have hPi : IsPullback (pullback.fst (a i) (pullback.fst p q))
      (pullback.snd (a i) (pullback.fst p q) ≫ pullback.snd p q) (a i ≫ p) q :=
    isPullback_pullback_fst_snd_comp (a i) (.of_hasPullback p q)
  refine isFormalAlgebraicSpace_of_etaleCover B S hS _
    (fun j ↦ pullback (b j)
      (pullback.snd (a i) (pullback.fst p q) ≫ pullback.snd p q))
    (fun j ↦ pullback.snd (b j)
      (pullback.snd (a i) (pullback.fst p q) ≫ pullback.snd p q)) (fun j ↦ ?_)
    (fun j ↦ isRepresentableEtale_pullback_snd B S hS (b j)
      (pullback.snd (a i) (pullback.fst p q) ≫ pullback.snd p q) (hYjet j))
    (Sheaf.isLocallySurjective_sigmaDesc_pullback_snd
      (pullback.snd (a i) (pullback.fst p q) ≫ pullback.snd p q) b hYsurj)
    (hstageset (Xi i) (a i) (hXiaff i))
  have hQ : IsPullback
      (pullback.snd (b j) (pullback.snd (a i) (pullback.fst p q) ≫ pullback.snd p q) ≫
        pullback.fst (a i) (pullback.fst p q))
      (pullback.fst (b j) (pullback.snd (a i) (pullback.fst p q) ≫ pullback.snd p q))
      (a i ≫ p) (b j ≫ q) :=
    (isPullback_pullback_fst_snd_comp (b j) hPi.flip).flip
  exact isFormalAlgebraicSpace_of_iso B S hS hQ.isoPullback
    (hstage (Xi i) (Yj j) (a i ≫ p) (b j ≫ q) (hXiaff i) (hYjaff j))

/-- **Stacks 0AJ2** for a base which is separated in the sense of clause (2) of Stacks 0AJ6.
The fibre product of two formal algebraic spaces over such a base, whose relative products of
representables are representable, is a formal algebraic space.

Separatedness enters only through Stacks 0AN3 clause (1): it makes the fibre product of two
affine formal algebraic spaces over `Z` again an affine formal algebraic space, which is the
hypothesis `hstage` of `isFormalAlgebraicSpace_pullback_of_affineStages`. The set-theoretic
condition of Stacks 0AIS on `X ×_Z Y` and on the intermediate fibre products follows from
`hZrep` alone, by `satisfiesSetTheoreticCondition_pullback_of_hasRepresentableRelativeProducts`
over `Z` and, after the pasting isomorphism, over `Z` again. -/
@[stacks 0AJ2 "the case of a base separated in the sense of clause (2) of Stacks 0AJ6, where \
Stacks 0AN3 clause (1) makes every fibre product of two affine formal algebraic spaces over \
the base an affine formal algebraic space, in place of the directed colimit argument of \
Stacks 0AIU that the general case needs"]
theorem isFormalAlgebraicSpace_pullback_of_isSeparated
    {X Y Z : FppfSheaf B S hS} (p : X ⟶ Z) (q : Y ⟶ Z)
    (hZrep : HasRepresentableRelativeProducts B S hS Z)
    (hZsep : IsSeparated B S hS Z)
    (hX : IsFormalAlgebraicSpace B S hS X)
    (hY : IsFormalAlgebraicSpace B S hS Y) :
    IsFormalAlgebraicSpace B S hS (pullback p q) := by
  have hXrep := hasRepresentableRelativeProducts_of_isFormalAlgebraicSpace B S hS hX
  have hYrep := hasRepresentableRelativeProducts_of_isFormalAlgebraicSpace B S hS hY
  refine isFormalAlgebraicSpace_pullback_of_affineStages B S hS p q hX hY
    (fun _X' _Y' p' q' hX' hY' ↦ isFormalAlgebraicSpace_of_isAffineFormalAlgebraicSpace B S hS
      (isAffineFormalAlgebraicSpace_pullback B S hS p' q' hZrep hZsep hX' hY'))
    (satisfiesSetTheoreticCondition_pullback_of_hasRepresentableRelativeProducts B S hS p q
      hZrep hXrep hYrep hX.1 hY.1)
    fun X' a hX' ↦ ?_
  have hPi : IsPullback (pullback.fst a (pullback.fst p q))
      (pullback.snd a (pullback.fst p q) ≫ pullback.snd p q) (a ≫ p) q :=
    isPullback_pullback_fst_snd_comp a (.of_hasPullback p q)
  exact satisfiesSetTheoreticCondition_of_iso B S hS hPi.isoPullback.symm
    (satisfiesSetTheoreticCondition_pullback_of_hasRepresentableRelativeProducts B S hS
      (a ≫ p) q hZrep
      (hasRepresentableRelativeProducts_of_isAffineFormalAlgebraicSpace B S hS hX') hYrep
      hX'.1 hY.1)

/-- **Stacks 0AJ2** for a separated base, on two affine formal algebraic spaces: an affine
formal algebraic space is a formal algebraic space, so this is a special case of
`isFormalAlgebraicSpace_pullback_of_isSeparated`. -/
@[stacks 0AJ2 "the case of two affine formal algebraic spaces over a base separated in the \
sense of clause (2) of Stacks 0AJ6, where Stacks 0AN3 clause (1) makes the fibre product of \
the two an affine formal algebraic space"]
theorem isFormalAlgebraicSpace_pullback_of_isAffineFormal
    {X Y Z : FppfSheaf B S hS} (p : X ⟶ Z) (q : Y ⟶ Z)
    (hZrep : HasRepresentableRelativeProducts B S hS Z)
    (hZsep : IsSeparated B S hS Z)
    (hX : IsAffineFormalAlgebraicSpace B S hS X)
    (hY : IsAffineFormalAlgebraicSpace B S hS Y) :
    IsFormalAlgebraicSpace B S hS (pullback p q) :=
  isFormalAlgebraicSpace_pullback_of_isSeparated B S hS p q hZrep hZsep
    (isFormalAlgebraicSpace_of_isAffineFormalAlgebraicSpace B S hS hX)
    (isFormalAlgebraicSpace_of_isAffineFormalAlgebraicSpace B S hS hY)

end AlgebraicGeometry.FormalSpace

end
