module

public import
  StacksFrontier.AlgebraicGeometry.Intersection.Projections.UniversalFamilyOverProjectiveSpace
public import StacksFrontier.AlgebraicGeometry.Morphisms.Projective.BaseChange

/-!
# The target of the universal family is the product `𝐏 × 𝐏(V)`

Tag 0B2W displays its universal family of projective transformations as a partially defined
self-map of `𝐏 × 𝐏(V)`, using the two identifications

`𝐏(V ⊗ 𝒪_𝐏) = 𝐏 × 𝐏(V)` and `𝐏(V ⊗ 𝒪_𝐏(1)) = 𝐏(V ⊗ 𝒪_𝐏)`.

The source gets the first from Tag 01O3, that forming a relative homogeneous spectrum commutes
with base change, applied to the structure morphism `𝐏 ⟶ Spec k`: the constant module
`V ⊗ 𝒪_𝐏` is the inverse image of `Ṽ` along it, so its projective bundle is the fibre product of
`𝐏(Ṽ)` with `𝐏` over `Spec k`. **This file makes that identification**, for an arbitrary scheme
over `Spec k` and then at `𝐏` itself.

The base here is *not* assumed affine, and nothing in the argument is local on it: Tag 01O3 over
an arbitrary base is `AlgebraicGeometry.projectiveBundleBaseChangeComparison`, which is proved
unconditionally in `StacksFrontier/AlgebraicGeometry/Morphisms/Projective/BaseChange.lean`. The
affine-base statements `Stacks.ProjectiveSpaceBaseChange.isPullback_projectiveSpaceOfModuleToSpec`
and `AlgebraicGeometry.ProjectiveSpaceOfModule.isPullback_universalFamilySpace` are not used and
are not what this rests on.

## Main results

* `Stacks.AlgebraicGeometry.ConstantModuleBundle.exists_iso_pullback_tensorStructureSheafBundle`:
  **the projective bundle of a constant module over an arbitrary base is a product.** For every
  scheme `S` over `Spec k` and every `k`-module `V`,
  `𝐏_S(V ⊗ 𝒪_S) ≅ S ×_{Spec k} 𝐏_{Spec k}(Ṽ)`, by an isomorphism carrying the projection of the
  bundle to the projection to `S`.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.exists_iso_pullback_universalEndTarget`:
  **the target of the universal family is `𝐏 × 𝐏(V)`**, the first of Tag 0B2W's two displayed
  identifications.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.exists_iso_pullback_universalEndTarget_comp_toBase`:
  the same identification stated against the morphism the family is a morphism over, so that
  `AlgebraicGeometry.ProjectiveSpaceOfModule.universalEndSheafProjection_comp_toBase` reads as a
  statement about the projection `𝐏 × 𝐏(V) ⟶ 𝐏`.

## Implementation notes

The input of `AlgebraicGeometry.projectiveBundleBaseChangeComparison` is an isomorphism
`ℰ' ≅ g^* ℰ`. Here it is `CategoryTheory.Iso.refl`: by the definition of
`Stacks.AlgebraicGeometry.BaseModuleOnScheme.tensorFunctor` as
`AlgebraicGeometry.tilde.functor k ⋙ AlgebraicGeometry.Scheme.Modules.pullback π`, the constant
module `V ⊗ 𝒪_S` *is* the inverse image of `Ṽ` along the structure morphism, so no comparison of
modules has to be built. `Stacks.AlgebraicGeometry.BaseModuleOnScheme.pullbackIso` is therefore
not needed either.

Quasi-coherence of the homogeneous pieces is supplied throughout by
`Stacks.SymGraded.isQuasicoherentPieces_of_isQuasicoherent`, as elsewhere, so
both sides are unconditional constructions.

The conclusions are existential, in the shape
`AlgebraicGeometry.ProjectiveBundleBaseChangeComparison` is stated: the comparison it provides is
obtained from `AlgebraicGeometry.projectiveBundlePresentationsAgree`, which is itself an
existence statement about two glueings of one object, so there is no named isomorphism to project
out of it.

## What is not done here

**Tag 0B2W's second identification, `𝐏(V ⊗ 𝒪_𝐏(1)) = 𝐏(V ⊗ 𝒪_𝐏)`, is not made.** That is Tag
02NC, the invariance of a relative homogeneous spectrum under twisting the graded algebra by an
invertible module, and it exists in this repository only in the absolute graded-ring form
`Stacks.GradedRing.InvertibleTwist.projTwistIsoGeneral`, over a commutative ring
rather than over a base scheme. Until it is available over a base scheme the *source* of the
family, `U(ψ) ⊆ 𝐏(V ⊗ 𝒪_𝐏(1))`, is not identified with an open of `𝐏 × 𝐏(V)`, so the family is
still not a partially defined self-map of one scheme, and the fibre of `r_ψ` over a point `[g]`
of `𝐏` is still not compared with the fibrewise `r_g` of
`AlgebraicGeometry.ProjectiveSpaceOfModule.endProjection`.

**The second factor is the projective bundle of `Ṽ` over `Spec k`, not
`AlgebraicGeometry.projectiveSpaceOfModule k V`.** The two are the same scheme, and **exactly one
step of the comparison is missing.** The bundle used here is
`Stacks.SymGraded.schemeProjectiveBundle`, built from the degreewise sheafification of the
sectionwise symmetric algebra, while `Stacks.SymGraded.projectiveBundleIsoProjectiveSpaceOfModule`
— which does identify a projective bundle over an affine base with `projectiveSpaceOfModule` —
is stated for `Stacks.SymGraded.projectiveBundle`, built from the associated sheaves of the
symmetric powers. That identification is now known to be one **over `Spec k`**
(`Stacks.SymGraded.projectiveBundleIsoProjectiveSpaceOfModule_hom_toSpec`), so it can be
substituted into a fibre product; what is still absent is the comparison of the two
presentations over `Spec k`, which by
`Stacks.FiniteMorphismProjective.projTopIso` is the comparison of their graded rings of global
sections, i.e. the transport of `Stacks.SymGraded.AffinePieces.symSectionRingEquiv` at the top
open — whose target is the symmetric algebra of the `Γ(Spec k, ⊤)`-module `Γ(Ṽ, ⊤)` — onto
`Sym_k(V)` along `AlgebraicGeometry.Scheme.ΓSpecIso` and `AlgebraicGeometry.tilde.isoTop`, as an
isomorphism of **graded** rings. Nothing in either tree performs that transport.

## References

* [Stacks Project, Tag 0B2W](https://stacks.math.columbia.edu/tag/0B2W)
* [Stacks Project, Tag 01O3](https://stacks.math.columbia.edu/tag/01O3)
* [Stacks Project, Tag 02NC](https://stacks.math.columbia.edu/tag/02NC)
* [Stacks Project, Tag 07ZG](https://stacks.math.columbia.edu/tag/07ZG)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.AlgebraicGeometry.BaseModuleOnScheme
open Stacks.AlgebraicGeometry.ProjectiveSpaceSections
open Stacks.SymGraded

namespace Stacks.AlgebraicGeometry.ConstantModuleBundle

universe u

/-- **The projective bundle of a constant module over an arbitrary base is a product.** For a
scheme `S` over `Spec k`, given by a structure morphism `π`, and a `k`-module `V`,

`𝐏_S(V ⊗ 𝒪_S) ≅ S ×_{Spec k} 𝐏_{Spec k}(Ṽ)`,

by an isomorphism carrying the first projection of the fibre product to the projection of the
bundle to `S`.

This is Tag 01O3 over an arbitrary — in particular non-affine — base, applied to `π`: the
constant module `V ⊗ 𝒪_S` is by definition the inverse image of `Ṽ` along `π`. -/
public theorem exists_iso_pullback_tensorStructureSheafBundle {k : CommRingCat.{u}}
    {S : Scheme.{u}} (π : S ⟶ Spec k) (V : ModuleCat.{u} k) :
    ∃ e : (schemeProjectiveBundle (tensorStructureSheaf π V)
          (isQuasicoherentPieces_of_isQuasicoherent _)).scheme ≅
        pullback π (schemeProjectiveBundle (AlgebraicGeometry.tilde V)
          (isQuasicoherentPieces_of_isQuasicoherent _)).toBase,
      e.hom ≫ pullback.fst π (schemeProjectiveBundle (AlgebraicGeometry.tilde V)
          (isQuasicoherentPieces_of_isQuasicoherent _)).toBase =
        (schemeProjectiveBundle (tensorStructureSheaf π V)
          (isQuasicoherentPieces_of_isQuasicoherent _)).toBase :=
  AlgebraicGeometry.projectiveBundleBaseChangeComparison π (AlgebraicGeometry.tilde V)
    (isQuasicoherentPieces_of_isQuasicoherent _) (tensorStructureSheaf π V)
    (isQuasicoherentPieces_of_isQuasicoherent _) (Iso.refl _)

/-- **The product identification as a cartesian square.** The square formed by the projection of
`𝐏_S(V ⊗ 𝒪_S)` to `S`, the comparison morphism to `𝐏_{Spec k}(Ṽ)` and the two structure
morphisms to `Spec k` is cartesian.

This is the shape of the affine-base statements
`Stacks.ProjectiveSpaceBaseChange.isPullback_projectiveSpaceOfModuleToSpec` and
`AlgebraicGeometry.ProjectiveSpaceOfModule.isPullback_universalFamilySpace`, with no affineness
of the base: those two are base change along a ring map `k → A`, this one is base change along an
arbitrary morphism of schemes `S ⟶ Spec k`. -/
public theorem exists_isPullback_tensorStructureSheafBundle {k : CommRingCat.{u}}
    {S : Scheme.{u}} (π : S ⟶ Spec k) (V : ModuleCat.{u} k) :
    ∃ q : (schemeProjectiveBundle (tensorStructureSheaf π V)
          (isQuasicoherentPieces_of_isQuasicoherent _)).scheme ⟶
        (schemeProjectiveBundle (AlgebraicGeometry.tilde V)
          (isQuasicoherentPieces_of_isQuasicoherent _)).scheme,
      IsPullback (schemeProjectiveBundle (tensorStructureSheaf π V)
          (isQuasicoherentPieces_of_isQuasicoherent _)).toBase q π
        (schemeProjectiveBundle (AlgebraicGeometry.tilde V)
          (isQuasicoherentPieces_of_isQuasicoherent _)).toBase := by
  obtain ⟨e, he⟩ := exists_iso_pullback_tensorStructureSheafBundle π V
  refine ⟨e.hom ≫ pullback.snd _ _, IsPullback.of_iso_pullback ⟨?_⟩ e he rfl⟩
  rw [← he, Category.assoc, Category.assoc, pullback.condition]

end Stacks.AlgebraicGeometry.ConstantModuleBundle

namespace AlgebraicGeometry.ProjectiveSpaceOfModule

universe u

variable (k V : Type u) [Field k] [AddCommGroup V] [Module k V] [Module.Finite k V]

omit [Module.Finite k V] in
/-- **The target of Tag 0B2W's universal family is the product `𝐏 × 𝐏(V)`.** The relative
projective space `𝐏(V ⊗ 𝒪_𝐏)` over the projective parameter space `𝐏 = 𝐏(Eᵛ)` is the fibre
product of `𝐏` with the projective space of `V` over `Spec k`, by an isomorphism over `𝐏`.

This is the first of the two identifications Tag 0B2W's display uses, and it is the base change
of a relative homogeneous spectrum (Tag 01O3) along the structure morphism of `𝐏`, which is not
an affine morphism and over which nothing is assumed. -/
@[stacks 0B2W "the identification 𝐏(V ⊗ 𝒪_𝐏) = 𝐏 × 𝐏(V) over the projective parameter space \
𝐏 = 𝐏(Eᵛ), the target of r_ψ; the second factor is the projective bundle of Ṽ over Spec k"]
public theorem exists_iso_pullback_universalEndTarget :
    ∃ e : (Stacks.SymGraded.schemeProjectiveBundle
          (constantModule k (dualEndSpace k V) V)
          (Stacks.SymGraded.isQuasicoherentPieces_of_isQuasicoherent _)).scheme ≅
        pullback (projectiveSpaceOfModuleToSpec k (dualEndSpace k V))
          (Stacks.SymGraded.schemeProjectiveBundle
            (AlgebraicGeometry.tilde (ModuleCat.of (CommRingCat.of k) V))
            (Stacks.SymGraded.isQuasicoherentPieces_of_isQuasicoherent _)).toBase,
      e.hom ≫ pullback.fst (projectiveSpaceOfModuleToSpec k (dualEndSpace k V))
          (Stacks.SymGraded.schemeProjectiveBundle
            (AlgebraicGeometry.tilde (ModuleCat.of (CommRingCat.of k) V))
            (Stacks.SymGraded.isQuasicoherentPieces_of_isQuasicoherent _)).toBase =
        (Stacks.SymGraded.schemeProjectiveBundle
          (constantModule k (dualEndSpace k V) V)
          (Stacks.SymGraded.isQuasicoherentPieces_of_isQuasicoherent _)).toBase :=
  Stacks.AlgebraicGeometry.ConstantModuleBundle.exists_iso_pullback_tensorStructureSheafBundle
    (projectiveSpaceOfModuleToSpec k (dualEndSpace k V))
    (ModuleCat.of (CommRingCat.of k) V)

omit [Module.Finite k V] in
/-- **The target of Tag 0B2W's universal family is the product `𝐏 × 𝐏(V)`, as a cartesian
square.** The projection of `𝐏(V ⊗ 𝒪_𝐏)` to `𝐏`, the comparison with the projective space of `V`
over `Spec k` and the two structure morphisms form a cartesian square.

This is the statement `AlgebraicGeometry.ProjectiveSpaceOfModule.isPullback_universalFamilySpace`
over the projective parameter space `𝐏` instead of over the affine cone `𝔸(E)`. -/
@[stacks 0B2W "the identification 𝐏(V ⊗ 𝒪_𝐏) = 𝐏 × 𝐏(V) as a cartesian square over Spec k, the \
affine-cone product identification carried over to the projective parameter space 𝐏 = 𝐏(Eᵛ)"]
public theorem exists_isPullback_universalEndTarget :
    ∃ q : (Stacks.SymGraded.schemeProjectiveBundle
          (constantModule k (dualEndSpace k V) V)
          (Stacks.SymGraded.isQuasicoherentPieces_of_isQuasicoherent _)).scheme ⟶
        (Stacks.SymGraded.schemeProjectiveBundle
          (AlgebraicGeometry.tilde (ModuleCat.of (CommRingCat.of k) V))
          (Stacks.SymGraded.isQuasicoherentPieces_of_isQuasicoherent _)).scheme,
      IsPullback (Stacks.SymGraded.schemeProjectiveBundle
          (constantModule k (dualEndSpace k V) V)
          (Stacks.SymGraded.isQuasicoherentPieces_of_isQuasicoherent _)).toBase q
        (projectiveSpaceOfModuleToSpec k (dualEndSpace k V))
        (Stacks.SymGraded.schemeProjectiveBundle
          (AlgebraicGeometry.tilde (ModuleCat.of (CommRingCat.of k) V))
          (Stacks.SymGraded.isQuasicoherentPieces_of_isQuasicoherent _)).toBase :=
  Stacks.AlgebraicGeometry.ConstantModuleBundle.exists_isPullback_tensorStructureSheafBundle
    (projectiveSpaceOfModuleToSpec k (dualEndSpace k V))
    (ModuleCat.of (CommRingCat.of k) V)

/-- **The universal family is a family over `𝐏` read on the product.** Composing
`AlgebraicGeometry.ProjectiveSpaceOfModule.universalEndSheafProjection_comp_toBase` with the
identification of the target with `𝐏 × 𝐏(V)`: the first projection of the product, pulled back
along `r_ψ` and the identification, is the projection of `U(ψ)` to `𝐏`. -/
@[stacks 0B2W "r_ψ followed by the identification of its target with 𝐏 × 𝐏(V) is a morphism \
over 𝐏, the first projection of the product"]
public theorem exists_iso_pullback_universalEndTarget_comp_toBase :
    ∃ e : (Stacks.SymGraded.schemeProjectiveBundle
          (constantModule k (dualEndSpace k V) V)
          (Stacks.SymGraded.isQuasicoherentPieces_of_isQuasicoherent _)).scheme ≅
        pullback (projectiveSpaceOfModuleToSpec k (dualEndSpace k V))
          (Stacks.SymGraded.schemeProjectiveBundle
            (AlgebraicGeometry.tilde (ModuleCat.of (CommRingCat.of k) V))
            (Stacks.SymGraded.isQuasicoherentPieces_of_isQuasicoherent _)).toBase,
      (universalEndSheafProjection k V ≫ e.hom) ≫
          pullback.fst (projectiveSpaceOfModuleToSpec k (dualEndSpace k V))
            (Stacks.SymGraded.schemeProjectiveBundle
              (AlgebraicGeometry.tilde (ModuleCat.of (CommRingCat.of k) V))
              (Stacks.SymGraded.isQuasicoherentPieces_of_isQuasicoherent _)).toBase =
        (universalEndSheafDomain k V).ι ≫
          Stacks.SymGraded.schemeProjectiveBundleToBase
            (twistObj k (dualEndSpace k V)
              (constantModule k (dualEndSpace k V) V) ((1 : ℕ) : ℤ))
            (Stacks.SymGraded.isQuasicoherentPieces_of_isQuasicoherent _) := by
  obtain ⟨e, he⟩ := exists_iso_pullback_universalEndTarget k V
  refine ⟨e, ?_⟩
  rw [Category.assoc, he]
  exact universalEndSheafProjection_comp_toBase k V

end AlgebraicGeometry.ProjectiveSpaceOfModule

end
