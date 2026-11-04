module

public import StacksFrontier.AlgebraicGeometry.Descent.DescentDatumAlgebraPushout

/-!
# Steps 4 and 5 of the proof of Stacks 0APK over an affine base, from the geometry

Let `f : X ⟶ S` be a flat morphism of affine schemes, let `D` be a descent datum relative to `f`
with underlying scheme `V` quasi-separated, and let `E ⊆ V` be an intersection of a nonempty
family of quasi-compact opens, invariant under the gluing isomorphism `φ` set-theoretically.
Write `R = Γ(S, ⊤)`, `A = Γ(X, ⊤)` and `C = Γ(E, 𝒪_V|_E)`.

Step 4 of the proof of [Stacks, Tag 0APK](https://stacks.math.columbia.edu/tag/0APK) produces from
this an `R`-algebra `R'` together with an isomorphism `χ : R' ⊗_R A → C` of `A`-algebras, and step
5 descends an open subscheme of `Spec C` to one of `Spec R'`. Both are proved algebraically —
`AlgebraicGeometry.ModuleCat.isPushout_descentInvariants_of_isPushout` and
`AlgebraicGeometry.ModuleCat.exists_subalgebra_isPushout_and_existsUnique_opens_preimage_eq` — and
`StacksFrontier.AlgebraicGeometry.Descent.DescentDatumAlgebraPushout` supplies their four pieces of
geometric input. This file joins the two, so that the conclusion of steps 4 and 5 is available
*from the geometry*.

Exactly two hypotheses remain. The first is faithful flatness of `R ⟶ A`, which in the situation
of Tag 0APK is part of the reduction to the affine case. The second is the coassociativity
condition `hkey` on the unit of `ψ`: that is the cocycle condition for `φ` transported to `ψ`,
which the source of Tag 0APK performs with "details omitted", and it is *not* derived here.

## Main definitions

* `AlgebraicGeometry.DescentDatum.descentAlgebraTransition` : the isomorphism
  `ψ : C ⊗_R A ≃ₐ[R] A ⊗_R C` of `A ⊗_R A`-algebras that the gluing isomorphism of the descent
  datum induces on the rings of functions. This is the `ψ` of the source of Tag 0APK.

## Main results

* `AlgebraicGeometry.DescentDatum.isPushout_descentInvariants_of_cocycle` : **step 4 of the proof
  of Stacks 0APK over an affine base, from the geometry.** `C` is the base change to `A` of the
  `R`-subalgebra of `ψ`-invariants, which is the isomorphism `χ` of the source.
* `AlgebraicGeometry.DescentDatum.exists_subalgebra_isPushout_and_existsUnique_opens_preimage_eq` :
  **steps 4 and 5 chained.** There is an `R`-subalgebra `C₀ ⊆ C` with `C = A ⊗_R C₀`, and every
  open subscheme of `Spec C` whose two preimages in `Spec C ×_{Spec C₀} Spec C` agree descends
  uniquely to `Spec C₀`.

## Implementation notes

`AlgebraicGeometry.DescentDatum.descentAlgebraTransition` exists so that `hkey` can be stated
against a name rather than against the five-argument application of
`AlgebraicGeometry.ModuleCat.algebraTransitionOfPushout` that it unfolds to; the two theorems then
hold by `exact`, which crosses that unfolding.

The algebra structures on `A` over `R` and on `C` over `A` and over `R` are hypotheses rather than
instances, with the three equations identifying each `algebraMap` with the geometric morphism it
is meant to be; see the implementation notes of
`StacksFrontier.AlgebraicGeometry.Descent.DescentDatumAlgebraPushout`. A consumer installs them with
`RingHom.toAlgebra` on `f.appTop`, on `D.over.hom.appTop ≫ topToSubset E`, and on their composite.

The open subscheme of `Spec C` that step 5 is applied to in the proof of Tag 0APK is the image
`j(W)` of the invariant *open* `W` of step 3, which is available as
`AlgebraicGeometry.subsetΓSpecOpens`; what is not available, and is the reason this file stops at
an implication, is the compatibility of its two preimages. See the implementation notes of
`StacksFrontier.AlgebraicGeometry.Descent.IntersectionOpenImage`.

No tag is placed. Tag 0APK is stated for arbitrary fpqc covering families and this is the affine
single-morphism case; Tag 023N is module-only mathematics and must not be placed on an algebra
statement; Tag 03N0 is already carried elsewhere.

## References

* [Stacks Project, Tag 0APK](https://stacks.math.columbia.edu/tag/0APK)
* [Stacks Project, Tag 023G](https://stacks.math.columbia.edu/tag/023G)
* [Stacks Project, Tag 023N](https://stacks.math.columbia.edu/tag/023N)
* [Stacks Project, Tag 03N0](https://stacks.math.columbia.edu/tag/03N0)
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits TensorProduct

universe u

namespace AlgebraicGeometry

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
    [IsAffine S] [IsAffine X] [Flat f] [QuasiSeparatedSpace D.over.left]

/-- **The isomorphism `ψ` of step 4 of the proof of
[Stacks, Tag 0APK](https://stacks.math.columbia.edu/tag/0APK).**  The gluing isomorphism of a
descent datum induces, through the two instances of Stacks 0APJ, an isomorphism
```
ψ : Γ(E, 𝒪_V|_E) ⊗_{Γ(S, ⊤)} Γ(X, ⊤) ≃ₐ Γ(X, ⊤) ⊗_{Γ(S, ⊤)} Γ(E, 𝒪_V|_E)
```
of `Γ(X, ⊤) ⊗_{Γ(S, ⊤)} Γ(X, ⊤)`-algebras. -/
def descentAlgebraTransition {I : Type u} [Nonempty I] (U : I → D.over.left.Opens)
    (hU : ∀ i, IsCompact (U i : Set D.over.left)) (hE : E = ⋂ i, (U i : Set D.over.left))
    (h₁ : (⇑(pullback.fst (D.over.hom ≫ f) f) ⁻¹' E) ⊆
      ⇑D.transitionPullbackIso.hom ⁻¹' (⇑(pullback.snd f (D.over.hom ≫ f)) ⁻¹' E))
    (h₂ : (⇑(pullback.snd f (D.over.hom ≫ f)) ⁻¹' E) ⊆
      ⇑D.transitionPullbackIso.inv ⁻¹' (⇑(pullback.fst (D.over.hom ≫ f) f) ⁻¹' E)) :
    (↥(D.over.left.sectionsRingOnSubset E) ⊗[↥Γ(S, ⊤)] ↥Γ(X, ⊤)) ≃ₐ[↥Γ(S, ⊤)]
      (↥Γ(X, ⊤) ⊗[↥Γ(S, ⊤)] ↥(D.over.left.sectionsRingOnSubset E)) :=
  ModuleCat.algebraTransitionOfPushout
    (D.isPushout_algebraMap_transitionSource E hRA hRC U hU hE)
    (D.isPushout_algebraMap_transitionTarget E hRA hRC U hU hE)
    (D.transitionSectionsIso E h₁ h₂)
    (D.algebraMap_comp_transitionSectionsIso_hom E hAC h₁ h₂)
    (D.transitionSectionsIso_hom_eq_algebraMap_comp E hAC h₁ h₂)

variable [Module.FaithfullyFlat ↥Γ(S, ⊤) ↥Γ(X, ⊤)] {I : Type u} [Nonempty I]
    (U : I → D.over.left.Opens) (hU : ∀ i, IsCompact (U i : Set D.over.left))
    (hE : E = ⋂ i, (U i : Set D.over.left))
    (h₁ : (⇑(pullback.fst (D.over.hom ≫ f) f) ⁻¹' E) ⊆
      ⇑D.transitionPullbackIso.hom ⁻¹' (⇑(pullback.snd f (D.over.hom ≫ f)) ⁻¹' E))
    (h₂ : (⇑(pullback.snd f (D.over.hom ≫ f)) ⁻¹' E) ⊆
      ⇑D.transitionPullbackIso.inv ⁻¹' (⇑(pullback.fst (D.over.hom ≫ f) f) ⁻¹' E))

include hRA hRC hAC in
/-- **Step 4 of the proof of [Stacks, Tag 0APK](https://stacks.math.columbia.edu/tag/0APK) over an
affine base, from the geometry.**  If the unit of
`AlgebraicGeometry.DescentDatum.descentAlgebraTransition` is coassociative — which is the cocycle
condition for the gluing isomorphism of the datum, transported to `ψ` — then `Γ(E, 𝒪_V|_E)` is the
base change to `Γ(X, ⊤)` of the `Γ(S, ⊤)`-subalgebra of `ψ`-invariants.

That subalgebra is the ring called `R'` in the source, and the pushout property is its isomorphism
`χ : R' ⊗_R A → Γ(E, 𝒪_V|_E)` of `A`-algebras. -/
theorem isPushout_descentInvariants_of_cocycle
    (hkey : ∀ c : ↥(D.over.left.sectionsRingOnSubset E),
      LinearMap.lTensor ↥Γ(X, ⊤)
          (ModuleCat.algebraUnitTransition ↥Γ(S, ⊤) ↥Γ(X, ⊤) _
            (D.descentAlgebraTransition E hRA hRC hAC U hU hE h₁ h₂))
          (ModuleCat.algebraUnitTransition ↥Γ(S, ⊤) ↥Γ(X, ⊤) _
            (D.descentAlgebraTransition E hRA hRC hAC U hU hE h₁ h₂) c) =
        LinearMap.lTensor ↥Γ(X, ⊤)
          (TensorProduct.mk ↥Γ(S, ⊤) ↥Γ(X, ⊤) ↥(D.over.left.sectionsRingOnSubset E) 1)
          (ModuleCat.algebraUnitTransition ↥Γ(S, ⊤) ↥Γ(X, ⊤) _
            (D.descentAlgebraTransition E hRA hRC hAC U hU hE h₁ h₂) c)) :
    Algebra.IsPushout ↥Γ(S, ⊤) ↥Γ(X, ⊤)
      (ModuleCat.descentInvariants ↥Γ(S, ⊤) ↥Γ(X, ⊤) ↥(D.over.left.sectionsRingOnSubset E)
        (D.descentAlgebraTransition E hRA hRC hAC U hU hE h₁ h₂))
      ↥(D.over.left.sectionsRingOnSubset E) :=
  ModuleCat.isPushout_descentInvariants_of_isPushout
    (D.isPushout_algebraMap_transitionSource E hRA hRC U hU hE)
    (D.isPushout_algebraMap_transitionTarget E hRA hRC U hU hE)
    (D.transitionSectionsIso E h₁ h₂)
    (D.algebraMap_comp_transitionSectionsIso_hom E hAC h₁ h₂)
    (D.transitionSectionsIso_hom_eq_algebraMap_comp E hAC h₁ h₂) hkey

include hRA hRC hAC in
/-- **Steps 4 and 5 of the proof of
[Stacks, Tag 0APK](https://stacks.math.columbia.edu/tag/0APK) over an affine base, from the
geometry, chained.**  Under the hypotheses of
`AlgebraicGeometry.DescentDatum.isPushout_descentInvariants_of_cocycle` there is a
`Γ(S, ⊤)`-subalgebra `C₀` of `Γ(E, 𝒪_V|_E)` whose base change to `Γ(X, ⊤)` is `Γ(E, 𝒪_V|_E)`, and
every open subscheme of `Spec Γ(E, 𝒪_V|_E)` whose two preimages in
`Spec Γ(E, 𝒪_V|_E) ×_{Spec C₀} Spec Γ(E, 𝒪_V|_E)` agree is the preimage of a unique open subscheme
of `Spec C₀`.

The open subscheme the proof of Tag 0APK applies this to is the image `j(W)` of the invariant open
`W` of step 3, which is `AlgebraicGeometry.subsetΓSpecOpens`; the compatibility of its two
preimages is the one remaining geometric input of step 5. -/
theorem exists_subalgebra_isPushout_and_existsUnique_opens_preimage_eq
    (hkey : ∀ c : ↥(D.over.left.sectionsRingOnSubset E),
      LinearMap.lTensor ↥Γ(X, ⊤)
          (ModuleCat.algebraUnitTransition ↥Γ(S, ⊤) ↥Γ(X, ⊤) _
            (D.descentAlgebraTransition E hRA hRC hAC U hU hE h₁ h₂))
          (ModuleCat.algebraUnitTransition ↥Γ(S, ⊤) ↥Γ(X, ⊤) _
            (D.descentAlgebraTransition E hRA hRC hAC U hU hE h₁ h₂) c) =
        LinearMap.lTensor ↥Γ(X, ⊤)
          (TensorProduct.mk ↥Γ(S, ⊤) ↥Γ(X, ⊤) ↥(D.over.left.sectionsRingOnSubset E) 1)
          (ModuleCat.algebraUnitTransition ↥Γ(S, ⊤) ↥Γ(X, ⊤) _
            (D.descentAlgebraTransition E hRA hRC hAC U hU hE h₁ h₂) c)) :
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
  ModuleCat.exists_subalgebra_isPushout_and_existsUnique_opens_preimage_eq
    (D.isPushout_algebraMap_transitionSource E hRA hRC U hU hE)
    (D.isPushout_algebraMap_transitionTarget E hRA hRC U hU hE)
    (D.transitionSectionsIso E h₁ h₂)
    (D.algebraMap_comp_transitionSectionsIso_hom E hAC h₁ h₂)
    (D.transitionSectionsIso_hom_eq_algebraMap_comp E hAC h₁ h₂) hkey

end DescentDatum

end AlgebraicGeometry

end

end
