module

public import StacksFrontier.AlgebraicGeometry.Duality.CompactGeneration.QcqsCoherator
public import StacksCore.Tactic.StacksAttribute

/-!
# The Mayer--Vietoris triangle of the coherator of a quasi-compact quasi-separated scheme

Let `X` be a quasi-compact and quasi-separated scheme covered by two quasi-compact opens,
`X = U ∪ V`. For a quasi-compact quasi-separated scheme `Z` the inclusion
`D_QCoh(𝒪_Z) ⥤ D(𝒪_Z)` has a right adjoint `DQ_Z`, the coherator: this is [Stacks, Tag 0CR0],
`Stacks.Duality.Coherator.isLeftAdjoint_quasiCoherentι`. The four schemes `X`, `U`, `V` and
`U ∩ V` are quasi-compact and quasi-separated, so all four coherators exist, and
[Stacks, Tag 0CR2] says that for every `K` in `D(𝒪_X)` there is a distinguished triangle in
`D_QCoh(𝒪_X)`

`DQ_X(K) ⟶ Rj_{U,*}DQ_U(K|_U) ⊕ Rj_{V,*}DQ_V(K|_V) ⟶ Rj_{U ∩ V,*}DQ_{U ∩ V}(K|_{U ∩ V}) ⟶`

This file is that statement at those coherators. The triangle itself is built in
`StacksFrontier/AlgebraicGeometry/QuasiCoherent/Coherator/MayerVietorisTriangle.lean`, where it is
constructed for coherators given in advance; what is added here is the production of the four
coherators from [Stacks, Tag 0CR0] and of the exactness of `DQ_X`, so that the statements below
rest on nothing beyond the quasi-compactness and quasi-separatedness hypotheses of the tag.

## Main results

* `Stacks.Duality.Coherator.quasiSeparatedSpace_toScheme` — an open subscheme of a quasi-separated
  scheme is quasi-separated, one of the two inputs Tag 0CR0 asks of `U`, `V` and `U ∩ V`.
* `Stacks.Duality.Coherator.mayerVietorisTriangle_rightAdjoint_mem_distTriang` —
  **[Stacks, Tag 0CR2]**: at the coherators `(quasiCoherentι Z).rightAdjoint` of the four
  schemes, whose existence is [Stacks, Tag 0CR0], the canonical triangle of the tag is
  distinguished.
* `Stacks.Duality.Coherator.exists_distTriang_rightAdjoint_quasiCoherentι` — a distinguished
  triangle on the three terms of the tag exists, at those coherators.
* `Stacks.Duality.Coherator.exists_coherator_distTriang` — coherators of `X`, `U`, `V` and
  `U ∩ V` exist, and for every `K` some distinguished triangle on the three terms exists.

## Implementation notes

*Exactness of `DQ_X`.* The source uses that `DQ_X` is an exact functor. This comes out of the
adjunction: the inclusion `D_QCoh(𝒪_X) ⥤ D(𝒪_X)` is exact, being the inclusion of a triangulated
subcategory, and a right adjoint of an exact functor between pretriangulated categories is exact
(`CategoryTheory.Adjunction.isTriangulated_rightAdjoint`). The `Functor.CommShift ℤ` structure on
`DQ_X` and the triangulatedness of the adjunction are therefore built inside
`Stacks.Duality.Coherator.mayerVietorisTriangle_distinguished`, by
`CategoryTheory.Adjunction.rightAdjointCommShift` and
`CategoryTheory.Adjunction.IsTriangulated.mk'`, as in
`Stacks.Duality.Coherator.exists_isTriangulated_rightAdjoint_quasiCoherentι`.

*The three auxiliary schemes are quasi-compact and quasi-separated.* `U` and `V` are quasi-compact
by hypothesis and `U ∩ V` is quasi-compact because `X` is quasi-separated
(`AlgebraicGeometry.Scheme.Opens.compactSpace_inf`); an open subscheme of a quasi-separated scheme
is quasi-separated (`Stacks.Duality.Coherator.quasiSeparatedSpace_toScheme`). These are what feed
[Stacks, Tag 0CR0] at `U`, `V` and `U ∩ V`, and [Stacks, Tag 08D5] part (1) at the three open
immersions.

*The model of the derived categories.* As in
`StacksFrontier/AlgebraicGeometry/QuasiCoherent/Coherator/MayerVietorisTriangle.lean`, no
`[HasDerivedCategory.{w}]` binder appears, so everything is at the locally small model
`AlgebraicGeometry.Scheme.Modules.hasDerivedCategory`, which is the model of [Stacks, Tag 0CR1]
and of [Stacks, Tag 0CR0] in this repository.

## References

* [Stacks Project, Tag 0CR2](https://stacks.math.columbia.edu/tag/0CR2)
* [Stacks Project, Tag 0CR1](https://stacks.math.columbia.edu/tag/0CR1)
* [Stacks Project, Tag 0CR0](https://stacks.math.columbia.edu/tag/0CR0)
* [Stacks Project, Tag 08BV](https://stacks.math.columbia.edu/tag/08BV)
* [Stacks Project, Tag 08D5](https://stacks.math.columbia.edu/tag/08D5)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe u

namespace Stacks.Duality.Coherator

/-- **An open subscheme of a quasi-separated scheme is quasi-separated.** This is quasi-separation
transported along the open immersion `j_W : W → X`, and it is what makes [Stacks, Tag 0CR0]
available at the open subschemes `U`, `V` and `U ∩ V`. -/
theorem quasiSeparatedSpace_toScheme {X : Scheme.{u}} [QuasiSeparatedSpace X] (W : X.Opens) :
    QuasiSeparatedSpace W.toScheme :=
  QuasiSeparatedSpace.of_isOpenEmbedding W.ι.isOpenEmbedding

/- `U ∩ V` is quasi-compact because `X` is quasi-separated and `U`, `V` are quasi-compact, and
each of the three opens is quasi-separated because `X` is. Neither statement is an instance
globally, being about the formation of `U ⊓ V` and of `W.toScheme`, so both are made instances
for the rest of this module: they are what [Stacks, Tag 0CR0] is applied to below. -/
attribute [local instance] AlgebraicGeometry.Scheme.Opens.compactSpace_inf
attribute [local instance] quasiSeparatedSpace_toScheme

section

variable {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X] (U V : X.Opens)
  [CompactSpace U.toScheme] [CompactSpace V.toScheme]

/-- Let `X` be a quasi-compact and quasi-separated scheme covered by two
quasi-compact opens, `X = U ∪ V`, and write `DQ_Z` for the coherator of `Z`, the right adjoint of
the inclusion `D_QCoh(𝒪_Z) ⥤ D(𝒪_Z)` whose existence for `Z` quasi-compact and quasi-separated is
[Stacks, Tag 0CR0] (`Stacks.Duality.Coherator.isLeftAdjoint_quasiCoherentι`). Then for every
object `K` of `D(𝒪_X)` there is a distinguished triangle

`DQ_X(K) ⟶ Rj_{U,*}DQ_U(K|_U) ⊕ Rj_{V,*}DQ_V(K|_V) ⟶ Rj_{U ∩ V,*}DQ_{U ∩ V}(K|_{U ∩ V}) ⟶`

in `D_QCoh(𝒪_X)`.

The four coherators are the ones [Stacks, Tag 0CR0] produces at `X`, `U`, `V` and `U ∩ V`: the
three opens are quasi-compact — `U ∩ V` because `X` is quasi-separated — and quasi-separated,
being opens of a quasi-separated scheme. The triangle is then
`Stacks.Duality.Coherator.mayerVietorisTriangle_distinguished` at those coherators. The triangle
with the canonical maps of [Stacks, Tag 0CR2] is
`Stacks.Duality.Coherator.mayerVietorisTriangle_rightAdjoint_mem_distTriang`. -/
theorem exists_distTriang_rightAdjoint_quasiCoherentι (hUV : U ⊔ V = ⊤)
    (K : DerivedCategory X.Modules) :
    letI := isLeftAdjoint_quasiCoherentι X
    letI := isLeftAdjoint_quasiCoherentι U.toScheme
    letI := isLeftAdjoint_quasiCoherentι V.toScheme
    letI := isLeftAdjoint_quasiCoherentι (U ⊓ V).toScheme
    ∃ (f : (quasiCoherentι X).rightAdjoint.obj K ⟶
          coheratorPushforwardOpens U (quasiCoherentι U.toScheme).rightAdjoint K ⊞
            coheratorPushforwardOpens V (quasiCoherentι V.toScheme).rightAdjoint K)
      (g : coheratorPushforwardOpens U (quasiCoherentι U.toScheme).rightAdjoint K ⊞
            coheratorPushforwardOpens V (quasiCoherentι V.toScheme).rightAdjoint K ⟶
          coheratorPushforwardOpens (U ⊓ V) (quasiCoherentι (U ⊓ V).toScheme).rightAdjoint K)
      (h : coheratorPushforwardOpens (U ⊓ V) (quasiCoherentι (U ⊓ V).toScheme).rightAdjoint K ⟶
          ((quasiCoherentι X).rightAdjoint.obj K)⟦(1 : ℤ)⟧),
      Triangle.mk f g h ∈ distTriang (quasiCoherentDerivedCategory X) := by
  let := isLeftAdjoint_quasiCoherentι X
  let := isLeftAdjoint_quasiCoherentι U.toScheme
  let := isLeftAdjoint_quasiCoherentι V.toScheme
  let := isLeftAdjoint_quasiCoherentι (U ⊓ V).toScheme
  exact mayerVietorisTriangle_distinguished U V _ _ _ _
    (Adjunction.ofIsLeftAdjoint (quasiCoherentι X))
    (Adjunction.ofIsLeftAdjoint (quasiCoherentι U.toScheme))
    (Adjunction.ofIsLeftAdjoint (quasiCoherentι V.toScheme))
    (Adjunction.ofIsLeftAdjoint (quasiCoherentι (U ⊓ V).toScheme)) K hUV

/-- For a quasi-compact quasi-separated scheme `X`
covered by two quasi-compact opens, `X = U ∪ V`, there are coherators `DQ_X`, `DQ_U`, `DQ_V`,
`DQ_{U ∩ V}` of `X`, `U`, `V` and `U ∩ V` — right adjoints of the inclusions
`D_QCoh(𝒪_Z) ⥤ D(𝒪_Z)`, [Stacks, Tag 0CR0] — such that every object `K` of `D(𝒪_X)` sits in a
distinguished triangle

`DQ_X(K) ⟶ Rj_{U,*}DQ_U(K|_U) ⊕ Rj_{V,*}DQ_V(K|_V) ⟶ Rj_{U ∩ V,*}DQ_{U ∩ V}(K|_{U ∩ V}) ⟶`

in `D_QCoh(𝒪_X)`. A coherator is unique up to a canonical isomorphism, so this is the same
assertion as `Stacks.Duality.Coherator.exists_distTriang_rightAdjoint_quasiCoherentι`, read
without naming the right adjoints. -/
theorem exists_coherator_distTriang (hUV : U ⊔ V = ⊤) :
    ∃ (DQX : DerivedCategory X.Modules ⥤ quasiCoherentDerivedCategory X)
      (DQU : DerivedCategory U.toScheme.Modules ⥤ quasiCoherentDerivedCategory U.toScheme)
      (DQV : DerivedCategory V.toScheme.Modules ⥤ quasiCoherentDerivedCategory V.toScheme)
      (DQUV : DerivedCategory (U ⊓ V).toScheme.Modules ⥤
        quasiCoherentDerivedCategory (U ⊓ V).toScheme)
      (_ : quasiCoherentι X ⊣ DQX) (_ : quasiCoherentι U.toScheme ⊣ DQU)
      (_ : quasiCoherentι V.toScheme ⊣ DQV) (_ : quasiCoherentι (U ⊓ V).toScheme ⊣ DQUV),
      ∀ K : DerivedCategory X.Modules,
        ∃ (f : DQX.obj K ⟶
              coheratorPushforwardOpens U DQU K ⊞ coheratorPushforwardOpens V DQV K)
          (g : coheratorPushforwardOpens U DQU K ⊞ coheratorPushforwardOpens V DQV K ⟶
              coheratorPushforwardOpens (U ⊓ V) DQUV K)
          (h : coheratorPushforwardOpens (U ⊓ V) DQUV K ⟶ (DQX.obj K)⟦(1 : ℤ)⟧),
          Triangle.mk f g h ∈ distTriang (quasiCoherentDerivedCategory X) := by
  let := isLeftAdjoint_quasiCoherentι X
  let := isLeftAdjoint_quasiCoherentι U.toScheme
  let := isLeftAdjoint_quasiCoherentι V.toScheme
  let := isLeftAdjoint_quasiCoherentι (U ⊓ V).toScheme
  exact ⟨_, _, _, _, Adjunction.ofIsLeftAdjoint (quasiCoherentι X),
    Adjunction.ofIsLeftAdjoint (quasiCoherentι U.toScheme),
    Adjunction.ofIsLeftAdjoint (quasiCoherentι V.toScheme),
    Adjunction.ofIsLeftAdjoint (quasiCoherentι (U ⊓ V).toScheme),
    fun K => exists_distTriang_rightAdjoint_quasiCoherentι U V hUV K⟩

/-- **[Stacks, Tag 0CR2].** Let `X` be a quasi-compact and quasi-separated scheme covered by two
quasi-compact opens, `X = U ∪ V`. By [Stacks, Tag 0CR0] the coherators `DQ_X`, `DQ_U`, `DQ_V`,
`DQ_{U ∩ V}` exist — here the right adjoints `(quasiCoherentι Z).rightAdjoint` — and for every
object `K` of `D(𝒪_X)` the canonical triangle

`DQ_X(K) ⟶ Rj_{U,*}DQ_U(K|_U) ⊕ Rj_{V,*}DQ_V(K|_V) ⟶ Rj_{U ∩ V,*}DQ_{U ∩ V}(K|_{U ∩ V}) ⟶`

is distinguished in `D_QCoh(𝒪_X)`. The triangle is `DQ_X` applied to the Mayer--Vietoris
triangle `Stacks.Duality.Coherator.mayerVietorisDerivedTriangle` of [Stacks, Tag 08BV], read
through the identifications of [Stacks, Tag 0CR1]; this is
`Stacks.Duality.Coherator.mayerVietorisTriangle_mem_distTriang` at those coherators. -/
@[stacks 0CR2 "the canonical triangle at the coherators of `X`, `U`, `V` and `U ∩ V` supplied by \
  Tag 0CR0"]
theorem mayerVietorisTriangle_rightAdjoint_mem_distTriang (hUV : U ⊔ V = ⊤)
    (K : DerivedCategory X.Modules) :
    letI := isLeftAdjoint_quasiCoherentι X
    letI := isLeftAdjoint_quasiCoherentι U.toScheme
    letI := isLeftAdjoint_quasiCoherentι V.toScheme
    letI := isLeftAdjoint_quasiCoherentι (U ⊓ V).toScheme
    letI : (quasiCoherentι X).rightAdjoint.CommShift ℤ :=
      (Adjunction.ofIsLeftAdjoint (quasiCoherentι X)).rightAdjointCommShift ℤ
    mayerVietorisTriangle U V _ _ _ _
        (Adjunction.ofIsLeftAdjoint (quasiCoherentι X))
        (Adjunction.ofIsLeftAdjoint (quasiCoherentι U.toScheme))
        (Adjunction.ofIsLeftAdjoint (quasiCoherentι V.toScheme))
        (Adjunction.ofIsLeftAdjoint (quasiCoherentι (U ⊓ V).toScheme))
        (isQuasicoherent_homology_derivedPushforward_opens U)
        (isQuasicoherent_homology_derivedPushforward_opens V)
        (isQuasicoherent_homology_derivedPushforward_opens (U ⊓ V)) K
        (biprod.desc (restrictPushforwardRes (inf_le_left : U ⊓ V ≤ U) K)
          (-restrictPushforwardRes (inf_le_right : U ⊓ V ≤ V) K))
        (mayerVietorisDerivedδ U V hUV K) ∈
      distTriang (quasiCoherentDerivedCategory X) :=
  letI := isLeftAdjoint_quasiCoherentι X
  letI := isLeftAdjoint_quasiCoherentι U.toScheme
  letI := isLeftAdjoint_quasiCoherentι V.toScheme
  letI := isLeftAdjoint_quasiCoherentι (U ⊓ V).toScheme
  mayerVietorisTriangle_mem_distTriang U V _ _ _ _
    (Adjunction.ofIsLeftAdjoint (quasiCoherentι X))
    (Adjunction.ofIsLeftAdjoint (quasiCoherentι U.toScheme))
    (Adjunction.ofIsLeftAdjoint (quasiCoherentι V.toScheme))
    (Adjunction.ofIsLeftAdjoint (quasiCoherentι (U ⊓ V).toScheme)) K hUV

end

end Stacks.Duality.Coherator

end
