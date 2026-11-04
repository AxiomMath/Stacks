module

public import StacksFrontier.AlgebraicGeometry.Descent.AffineHomEtaleDatum
public import StacksFrontier.AlgebraicGeometry.Descent.DescentDatumStepFourFive
public import StacksFrontier.AlgebraicGeometry.Descent.IntersectionOpenImage

/-!
# The interface between step 3 and steps 4 and 5 of the proof of Stacks 0APK

Step 3 of the proof of [Stacks, Tag 0APK](https://stacks.math.columbia.edu/tag/0APK) is proved
unconditionally as
`AlgebraicGeometry.exists_mem_isTransitionInvariant_isTransitionInvariantSet_descentDatum`: for a
descent datum `D` relative to a flat quasi-compact morphism `f : X ⟶ S` with `X` affine and with
`V ⟶ X` ind-quasi-affine, every point of `V` lies in an open `W` invariant under the gluing
isomorphism `φ`, contained in a subset `E` which is an intersection of a nonempty family of
quasi-compact opens and is invariant under `φ` set-theoretically.

Steps 4 and 5 are proved as
`AlgebraicGeometry.DescentDatum.exists_subalgebra_isPushout_and_existsUnique_opens_preimage_eq`,
but they are stated against four pieces of data that step 3 does not produce in that shape: the
two one-sided inclusions `h₁` and `h₂` rather than the invariance of `E`, faithful flatness of
`Γ(S, ⊤) ⟶ Γ(X, ⊤)`, quasi-separatedness of `V`, and an `Opens`-valued rather than a
`Set`-valued presentation of `E`. **This file removes three of those four from the statement** and
reduces the fourth to a single named lemma, so that the conclusion of steps 4 and 5 is available
from step 3 with nothing left over but the coassociativity hypothesis `hkey` — the cocycle
condition for `φ` transported to `ψ`, which the source performs with "details omitted".
Quasi-separatedness is the one that stays an instance *binder*, because the statement of `hkey`
mentions `AlgebraicGeometry.DescentDatum.descentAlgebraTransition`, which cannot be written
without it; what this file supplies for it is the one-line lemma that discharges it from
ind-quasi-affineness of the structure morphism.

## Main results

* `AlgebraicGeometry.DescentDatum.subset_preimage_transitionPullbackIso_hom_of_invariantSet` and
  `AlgebraicGeometry.DescentDatum.subset_preimage_transitionPullbackIso_inv_of_invariantSet` :
  the hypotheses `h₁` and `h₂` of steps 4 and 5 follow from
  `AlgebraicGeometry.DescentDatum.IsTransitionInvariantSet`, which is what step 3 produces.
* `AlgebraicGeometry.faithfullyFlat_of_algebraMap_eq_appTop` : **a flat surjection of affine
  schemes is faithfully flat on global sections**, in the `Module.FaithfullyFlat` shape that
  steps 4 and 5 ask for.
* `AlgebraicGeometry.quasiSeparatedSpace_of_isIndQuasiAffineHom_hom` : the scheme over `X`
  carried by a datum whose structure morphism is ind-quasi-affine is quasi-separated.
* `AlgebraicGeometry.exists_mem_isTransitionInvariant_invariantSet_opens_descentDatum` : step 3
  with its family of quasi-compact opens presented as `Scheme.Opens`.
* `AlgebraicGeometry.DescentDatum.isPushout_descentInvariants_of_invariantSet` : **step 4 of the
  proof of Stacks 0APK from the invariance of `E` alone.** This is the isomorphism `χ` of the
  source.
* `AlgebraicGeometry.DescentDatum.exists_subalgebra_isPushout_and_existsUnique_opens_of_invariant`:
  **steps 4 and 5 from the invariance of `E` alone.**
* `AlgebraicGeometry.DescentDatum.exists_mem_isTransitionInvariant_subsetΓSpecOpens` : step 3
  together with the packaging of `j(W)` as an open subscheme of `Spec Γ(E, 𝒪_V|_E)`, which is the
  open that step 5 descends.

## Implementation notes

*Why the algebra structures stay hypotheses.* `Algebra ↥Γ(S, ⊤) ↥Γ(X, ⊤)` holds only through the
particular ring map `f.appTop`, so it cannot be an instance; the three structures and the three
equations identifying each `algebraMap` with the geometric morphism it is meant to be are carried
exactly as in `StacksFrontier.AlgebraicGeometry.Descent.DescentDatumStepFourFive`, and a consumer
installs them with `RingHom.toAlgebra`. Faithful flatness, by contrast, is a *property* of those
structures and is therefore derivable once `hRA` is given, which is why it is discharged here and
the algebra structures are not.

*Why quasi-separatedness is not an instance either.*
`AlgebraicGeometry.quasiSeparatedSpace_of_isIndQuasiAffine` is a lemma rather than an instance,
and `AlgebraicGeometry.isIndQuasiAffine_of_isIndQuasiAffineHom_hom` has a conclusion about
`V.left` which does not determine `V`, so neither can be registered without hijacking instance
search. The composite is therefore recorded as a named lemma, to be supplied with `have` at each
use — `StacksFrontier.AlgebraicGeometry.Descent.DescentDatumResidue` is the use. It remains an
instance binder of the statements below, because `hkey` mentions
`AlgebraicGeometry.DescentDatum.descentAlgebraTransition`, whose own statement needs it, so it is
not discharged *here*; it is discharged wherever those statements are applied.

*No tag is placed.* Tag 0APK is stated for arbitrary fpqc covering families and everything here is
the affine single-morphism case; Tag 0APJ, Tag 023N and Tag 03N0 are carried elsewhere, and Tag
0API is carried by `AlgebraicGeometry.exists_iInter_iso_iInter_in_specΓ` and
`AlgebraicGeometry.isOpen_image_toΓSpec_of_isOpen`.

## References

* [Stacks Project, Tag 0APK](https://stacks.math.columbia.edu/tag/0APK)
* [Stacks Project, Tag 0API](https://stacks.math.columbia.edu/tag/0API)
* [Stacks Project, Tag 0APJ](https://stacks.math.columbia.edu/tag/0APJ)
* [Stacks Project, Tag 023N](https://stacks.math.columbia.edu/tag/023N)
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits TensorProduct

universe u v

namespace AlgebraicGeometry

/-! ### The two one-sided inclusions from invariance of the subset -/

namespace DescentDatum

variable {S X : Scheme.{u}} {f : X ⟶ S} (D : DescentDatum f) (E : Set D.over.left)

/-- **The hypothesis `h₁` of steps 4 and 5 of the proof of
[Stacks, Tag 0APK](https://stacks.math.columbia.edu/tag/0APK), from invariance of `E`.**  The
gluing isomorphism carries `E ×_S X` into `X ×_S E`. -/
alias subset_preimage_transitionPullbackIso_hom_of_invariantSet := subset_preimage_transitionPullbackIso_hom

/-- **The hypothesis `h₂` of steps 4 and 5 of the proof of
[Stacks, Tag 0APK](https://stacks.math.columbia.edu/tag/0APK), from invariance of `E`.**  The
inverse of the gluing isomorphism carries `X ×_S E` into `E ×_S X`. -/
alias subset_preimage_transitionPullbackIso_inv_of_invariantSet := subset_preimage_transitionPullbackIso_inv

end DescentDatum

/-! ### Faithful flatness and quasi-separatedness -/

/-- **A flat surjection of affine schemes is faithfully flat on global sections**, in the
`Module.FaithfullyFlat` shape that steps 4 and 5 of the proof of
[Stacks, Tag 0APK](https://stacks.math.columbia.edu/tag/0APK) ask for.

This is `AlgebraicGeometry.Flat.flat_and_surjective_iff_faithfullyFlat_of_isAffine` read through
the algebra structure that the consumer has installed on `f.appTop`. -/
theorem faithfullyFlat_of_algebraMap_eq_appTop {S X : Scheme.{u}} (f : X ⟶ S)
    [IsAffine S] [IsAffine X] [Flat f] [Surjective f] [Algebra ↥Γ(S, ⊤) ↥Γ(X, ⊤)]
    (hRA : CommRingCat.ofHom (algebraMap ↥Γ(S, ⊤) ↥Γ(X, ⊤)) = f.appTop) :
    Module.FaithfullyFlat ↥Γ(S, ⊤) ↥Γ(X, ⊤) := by
  have h : f.appTop.hom.FaithfullyFlat :=
    (Flat.flat_and_surjective_iff_faithfullyFlat_of_isAffine f).1 ⟨‹Flat f›, ‹Surjective f›⟩
  rw [← RingHom.faithfullyFlat_algebraMap_iff,
    show (algebraMap ↥Γ(S, ⊤) ↥Γ(X, ⊤)) = f.appTop.hom from congrArg CommRingCat.Hom.hom hRA]
  exact h

/-- The scheme over `X` carried by an object of `Over X` whose structure morphism is
ind-quasi-affine is quasi-separated, for `X` affine.

This is the composite of `AlgebraicGeometry.isIndQuasiAffine_of_isIndQuasiAffineHom_hom` with
`AlgebraicGeometry.quasiSeparatedSpace_of_isIndQuasiAffine`; it is the instance
`QuasiSeparatedSpace` that steps 4 and 5 of the proof of
[Stacks, Tag 0APK](https://stacks.math.columbia.edu/tag/0APK) ask for. -/
theorem quasiSeparatedSpace_of_isIndQuasiAffineHom_hom {X : Scheme.{u}} [IsAffine X]
    (V : Over X) [IsIndQuasiAffineHom V.hom] :
    QuasiSeparatedSpace V.left :=
  have : IsIndQuasiAffine V.left := isIndQuasiAffine_of_isIndQuasiAffineHom_hom V
  quasiSeparatedSpace_of_isIndQuasiAffine V.left

/-! ### Step 3 with its family of quasi-compact opens presented as opens -/

/-- **Step 3 of the proof of [Stacks, Tag 0APK](https://stacks.math.columbia.edu/tag/0APK), with
the family of quasi-compact opens presented as `AlgebraicGeometry.Scheme.Opens`.**  Every point of
the scheme `V` underlying a descent datum lies in an open `W` invariant under the gluing
isomorphism, contained in a set-theoretically invariant intersection `E` of a nonempty family of
quasi-compact *opens of the scheme* `V`.

This is `AlgebraicGeometry.exists_mem_isTransitionInvariant_isTransitionInvariantSet_descentDatum`
with each member of its family of open subsets packaged with its openness; the coercion back to
subsets is definitional, so the equation `hE` is unchanged.  It is the shape that steps 4 and 5
consume. -/
theorem exists_mem_isTransitionInvariant_invariantSet_opens_descentDatum
    {S X : Scheme.{u}} {f : X ⟶ S} (D : DescentDatum f) [IsAffine X] [Flat f] [QuasiCompact f]
    [IsIndQuasiAffineHom D.over.hom] (v : D.over.left) :
    ∃ (W : D.over.left.Opens) (E : Set D.over.left) (I : Type u) (_ : Nonempty I)
        (U : I → D.over.left.Opens),
      D.IsTransitionInvariant W ∧ (∀ i, IsCompact (U i : Set D.over.left)) ∧
        E = ⋂ i, (U i : Set D.over.left) ∧ D.IsTransitionInvariantSet E ∧
          v ∈ W ∧ (W : Set D.over.left) ⊆ E := by
  obtain ⟨W, E, I, hI, U, hWinv, hU, hEeq, hEinv, hv, hWE⟩ :=
    exists_mem_isTransitionInvariant_isTransitionInvariantSet_descentDatum D v
  exact ⟨W, E, I, hI, fun i => ⟨U i, (hU i).1⟩, hWinv, fun i => (hU i).2, hEeq, hEinv, hv, hWE⟩

/-! ### Steps 4 and 5 from invariance of the subset -/

namespace DescentDatum

variable {S X : Scheme.{u}} {f : X ⟶ S} (D : DescentDatum f) (E : Set D.over.left)
    [Algebra ↥Γ(S, ⊤) ↥Γ(X, ⊤)] [Algebra ↥Γ(S, ⊤) ↥(D.over.left.sectionsRingOnSubset E)]
    [Algebra ↥Γ(X, ⊤) ↥(D.over.left.sectionsRingOnSubset E)]
    [IsScalarTower ↥Γ(S, ⊤) ↥Γ(X, ⊤) ↥(D.over.left.sectionsRingOnSubset E)]
    (hRA : CommRingCat.ofHom (algebraMap ↥Γ(S, ⊤) ↥Γ(X, ⊤)) = f.appTop)
    (hRC : CommRingCat.ofHom (algebraMap ↥Γ(S, ⊤) ↥(D.over.left.sectionsRingOnSubset E)) =
      (D.over.hom ≫ f).appTop ≫ D.over.left.topToSubset E)
    (hAC : CommRingCat.ofHom (algebraMap ↥Γ(X, ⊤) ↥(D.over.left.sectionsRingOnSubset E)) =
      D.over.hom.appTop ≫ D.over.left.topToSubset E)
    [IsAffine S] [IsAffine X] [Flat f] [Surjective f]
    [QuasiSeparatedSpace D.over.left]
    {I : Type u} [Nonempty I] (U : I → D.over.left.Opens)
    (hU : ∀ i, IsCompact (U i : Set D.over.left)) (hE : E = ⋂ i, (U i : Set D.over.left))
    (hEinv : D.IsTransitionInvariantSet E)

include hRA hRC hAC hEinv in
/-- **Step 4 of the proof of [Stacks, Tag 0APK](https://stacks.math.columbia.edu/tag/0APK) from
the invariance of `E` alone.**  With `R = Γ(S, ⊤)`, `A = Γ(X, ⊤)` and `C = Γ(E, 𝒪_V|_E)`: if the
unit of the transition isomorphism `ψ` is coassociative, then `C` is the base change to `A` of the
`R`-subalgebra of `ψ`-invariants.

This is `AlgebraicGeometry.DescentDatum.isPushout_descentInvariants_of_cocycle` with its two
one-sided inclusions replaced by the invariance of `E` which step 3 produces, and with its
faithful-flatness hypothesis discharged from `[Flat f]` and `[Surjective f]`.  The subalgebra is
the ring called `R'` in the source and the pushout property is the isomorphism `χ`. -/
theorem isPushout_descentInvariants_of_invariantSet
    (hkey : ∀ c : ↥(D.over.left.sectionsRingOnSubset E),
      LinearMap.lTensor ↥Γ(X, ⊤)
          (ModuleCat.algebraUnitTransition ↥Γ(S, ⊤) ↥Γ(X, ⊤) _
            (D.descentAlgebraTransition E hRA hRC hAC U hU hE
              (D.subset_preimage_transitionPullbackIso_hom_of_invariantSet E hEinv)
              (D.subset_preimage_transitionPullbackIso_inv_of_invariantSet E hEinv)))
          (ModuleCat.algebraUnitTransition ↥Γ(S, ⊤) ↥Γ(X, ⊤) _
            (D.descentAlgebraTransition E hRA hRC hAC U hU hE
              (D.subset_preimage_transitionPullbackIso_hom_of_invariantSet E hEinv)
              (D.subset_preimage_transitionPullbackIso_inv_of_invariantSet E hEinv)) c) =
        LinearMap.lTensor ↥Γ(X, ⊤)
          (TensorProduct.mk ↥Γ(S, ⊤) ↥Γ(X, ⊤) ↥(D.over.left.sectionsRingOnSubset E) 1)
          (ModuleCat.algebraUnitTransition ↥Γ(S, ⊤) ↥Γ(X, ⊤) _
            (D.descentAlgebraTransition E hRA hRC hAC U hU hE
              (D.subset_preimage_transitionPullbackIso_hom_of_invariantSet E hEinv)
              (D.subset_preimage_transitionPullbackIso_inv_of_invariantSet E hEinv)) c)) :
    Algebra.IsPushout ↥Γ(S, ⊤) ↥Γ(X, ⊤)
      (ModuleCat.descentInvariants ↥Γ(S, ⊤) ↥Γ(X, ⊤) ↥(D.over.left.sectionsRingOnSubset E)
        (D.descentAlgebraTransition E hRA hRC hAC U hU hE
          (D.subset_preimage_transitionPullbackIso_hom_of_invariantSet E hEinv)
          (D.subset_preimage_transitionPullbackIso_inv_of_invariantSet E hEinv)))
      ↥(D.over.left.sectionsRingOnSubset E) :=
  have : Module.FaithfullyFlat ↥Γ(S, ⊤) ↥Γ(X, ⊤) := faithfullyFlat_of_algebraMap_eq_appTop f hRA
  D.isPushout_descentInvariants_of_cocycle E hRA hRC hAC U hU hE _ _ hkey

include hRA hRC hAC hEinv in
/-- **Steps 4 and 5 of the proof of
[Stacks, Tag 0APK](https://stacks.math.columbia.edu/tag/0APK) from the invariance of `E` alone.**
Under the coassociativity hypothesis of
`AlgebraicGeometry.DescentDatum.isPushout_descentInvariants_of_invariantSet` there is a
`Γ(S, ⊤)`-subalgebra `C₀` of `Γ(E, 𝒪_V|_E)` whose base change to `Γ(X, ⊤)` is `Γ(E, 𝒪_V|_E)`, and
every open subscheme of `Spec Γ(E, 𝒪_V|_E)` whose two preimages in
`Spec Γ(E, 𝒪_V|_E) ×_{Spec C₀} Spec Γ(E, 𝒪_V|_E)` agree is the preimage of a unique open subscheme
of `Spec C₀`.

This is
`AlgebraicGeometry.DescentDatum.exists_subalgebra_isPushout_and_existsUnique_opens_preimage_eq`
with its two one-sided inclusions replaced by the invariance of `E` and its faithful-flatness
hypothesis discharged.  The open subscheme the source applies this to is the image `j(W)` of the
invariant open `W` of step 3, available from
`AlgebraicGeometry.DescentDatum.exists_mem_isTransitionInvariant_subsetΓSpecOpens` below; the
compatibility of its two preimages is not proved in this development. -/
theorem exists_subalgebra_isPushout_and_existsUnique_opens_of_invariant
    (hkey : ∀ c : ↥(D.over.left.sectionsRingOnSubset E),
      LinearMap.lTensor ↥Γ(X, ⊤)
          (ModuleCat.algebraUnitTransition ↥Γ(S, ⊤) ↥Γ(X, ⊤) _
            (D.descentAlgebraTransition E hRA hRC hAC U hU hE
              (D.subset_preimage_transitionPullbackIso_hom_of_invariantSet E hEinv)
              (D.subset_preimage_transitionPullbackIso_inv_of_invariantSet E hEinv)))
          (ModuleCat.algebraUnitTransition ↥Γ(S, ⊤) ↥Γ(X, ⊤) _
            (D.descentAlgebraTransition E hRA hRC hAC U hU hE
              (D.subset_preimage_transitionPullbackIso_hom_of_invariantSet E hEinv)
              (D.subset_preimage_transitionPullbackIso_inv_of_invariantSet E hEinv)) c) =
        LinearMap.lTensor ↥Γ(X, ⊤)
          (TensorProduct.mk ↥Γ(S, ⊤) ↥Γ(X, ⊤) ↥(D.over.left.sectionsRingOnSubset E) 1)
          (ModuleCat.algebraUnitTransition ↥Γ(S, ⊤) ↥Γ(X, ⊤) _
            (D.descentAlgebraTransition E hRA hRC hAC U hU hE
              (D.subset_preimage_transitionPullbackIso_hom_of_invariantSet E hEinv)
              (D.subset_preimage_transitionPullbackIso_inv_of_invariantSet E hEinv)) c)) :
    ∃ C₀ : Subalgebra ↥Γ(S, ⊤) ↥(D.over.left.sectionsRingOnSubset E),
      Algebra.IsPushout ↥Γ(S, ⊤) ↥Γ(X, ⊤) C₀ ↥(D.over.left.sectionsRingOnSubset E) ∧
        ∀ W' : (Spec (CommRingCat.of ↥(D.over.left.sectionsRingOnSubset E))).Opens,
          (pullback.fst (Spec.map (CommRingCat.ofHom
                  (algebraMap C₀ ↥(D.over.left.sectionsRingOnSubset E))))
                (Spec.map (CommRingCat.ofHom
                  (algebraMap C₀ ↥(D.over.left.sectionsRingOnSubset E))))).base ⁻¹'
              (W' : Set _) =
            (pullback.snd (Spec.map (CommRingCat.ofHom
                  (algebraMap C₀ ↥(D.over.left.sectionsRingOnSubset E))))
                (Spec.map (CommRingCat.ofHom
                  (algebraMap C₀ ↥(D.over.left.sectionsRingOnSubset E))))).base ⁻¹'
              (W' : Set _) →
          ∃! W : (Spec (CommRingCat.of C₀)).Opens,
            Spec.map (CommRingCat.ofHom
              (algebraMap C₀ ↥(D.over.left.sectionsRingOnSubset E))) ⁻¹ᵁ W = W' :=
  have : Module.FaithfullyFlat ↥Γ(S, ⊤) ↥Γ(X, ⊤) := faithfullyFlat_of_algebraMap_eq_appTop f hRA
  D.exists_subalgebra_isPushout_and_existsUnique_opens_preimage_eq E hRA hRC hAC U hU hE _ _ hkey

end DescentDatum

/-! ### Step 3 together with the open subscheme `j(W)` that step 5 descends -/

namespace DescentDatum

variable {S X : Scheme.{u}} {f : X ⟶ S} (D : DescentDatum f)

/-- **Step 3 of the proof of [Stacks, Tag 0APK](https://stacks.math.columbia.edu/tag/0APK)
together with the open subscheme that step 5 descends.**  Every point `v` of the scheme `V`
underlying the datum lies in an open `W` invariant under the gluing isomorphism, contained in a
set-theoretically invariant intersection `E` of a nonempty family of quasi-compact opens, and the
image `j(W)` of `W` under the canonical embedding of Stacks 0API is an open subscheme of
`Spec Γ(E, 𝒪_V|_E)`.

Both halves are already proved —
`AlgebraicGeometry.exists_mem_isTransitionInvariant_invariantSet_opens_descentDatum` and
`AlgebraicGeometry.DescentDatum.exists_opens_coe_eq_subsetΓSpecImage` — and this is their
composition, which is the complete input of step 5 apart from the compatibility of the two
preimages of `j(W)`. -/
theorem exists_mem_isTransitionInvariant_subsetΓSpecOpens [IsAffine X] [Flat f] [QuasiCompact f]
    [IsIndQuasiAffineHom D.over.hom] (v : D.over.left) :
    ∃ (W : D.over.left.Opens) (E : Set D.over.left) (I : Type u) (_ : Nonempty I)
        (U : I → D.over.left.Opens),
      D.IsTransitionInvariant W ∧ (∀ i, IsCompact (U i : Set D.over.left)) ∧
        E = ⋂ i, (U i : Set D.over.left) ∧ D.IsTransitionInvariantSet E ∧
          v ∈ W ∧ (W : Set D.over.left) ⊆ E ∧
            ∃ W₀ : (Spec (D.over.left.sectionsRingOnSubset E)).Opens,
              (W₀ : Set (Spec (D.over.left.sectionsRingOnSubset E))) =
                subsetΓSpecImage D.over.left E (W : Set D.over.left) := by
  obtain ⟨W, E, I, hI, U, hWinv, hU, hEeq, hEinv, hv, hWE⟩ :=
    exists_mem_isTransitionInvariant_invariantSet_opens_descentDatum D v
  exact ⟨W, E, I, hI, U, hWinv, hU, hEeq, hEinv, hv, hWE,
    D.exists_opens_coe_eq_subsetΓSpecImage U hU E (W : Set D.over.left) hEeq hWE W.isOpen⟩

end DescentDatum

end AlgebraicGeometry

end

end
