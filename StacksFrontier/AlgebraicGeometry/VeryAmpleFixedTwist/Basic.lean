module

public import StacksFrontier.AlgebraicGeometry.AmpleLocalGeneration.FromExtension
public import StacksFrontier.AlgebraicGeometry.AmplePullbackPart1.TensorPowerTensor
public import StacksFrontier.AlgebraicGeometry.ProductFamilyRatio.Consequences
public import StacksFrontier.AlgebraicGeometry.VeryAmplePowersQuasiCompactBase.Basic
public import StacksCore.Tactic.StacksAttribute

/-!
# Stacks Tag 0FVC: a fixed twist of the high powers of a relatively ample module is very ample

Stacks Tag 0FVC says that for a morphism of schemes `f : X ⟶ S` and invertible `𝒪_X`-modules `N`
and `L` with `S` quasi-compact, `f` of finite type and `L` relatively ample for `f`, the module
`N ⊗ L^{⊗ d}` is relatively very ample for `f` for every sufficiently large `d`.

**This is not a corollary of Stacks Tag 01VU**, which is proved in
`StacksFrontier/AlgebraicGeometry/VeryAmplePowersQuasiCompactBase/Basic.lean`: that tag produces
very ampleness of the *powers of one module*, and no amount of it reaches a fixed twist by `N`. The
source's proof needs two further inputs, and this file supplies both rather than assuming them.

* **A very ample module tensored with a globally generated one is very ample.** This is the
  geometric content, and it is **proved**, as
  `Stacks.VeryAmpleFixedTwist.familyImmersion_tensor`. The source gets it from the Segre
  embedding of `𝐏ⁿ_S ×_S 𝐏ᵐ_S` into `𝐏^{nm+n+m}_S`, which this repository cannot use for the
  purpose: Stacks Tag 01WD is stated here as an existential with no clause about the coordinates
  of the embedding, and the identification of `𝒪(1)` along it
  (`Stacks.ChartImmersionAssembly.SegreTwist`) is an open statement that would additionally need
  the two tensor products of sheaves of modules on a scheme identified. What is used instead is
  the Segre-free chart route of `StacksFrontier/AlgebraicGeometry/ProductFamilyRatio/Basic.lean`,
  whose supporting lemmas are already stated for arbitrary modules; only the family builder and
  its three chart lemmas are specialised there to the powers of one `L`, and generalising them to
  an arbitrary comparison isomorphism `F ⊗ G ≅ H` is what this file does first.
* **Relative global generation of `N ⊗ L^{⊗ d}` for `d ≫ 1`.** This is **not** carried as a
  hypothesis either. The source reduces to an affine base by Stacks Tag 02NQ before invoking it,
  and over an affine base — indeed over any base — it is the *absolute* statement, clause (7) of
  Stacks Tag 01Q3, which is proved with no hypothesis as
  `Stacks.AmpleLocalGeneration.isEventuallyGloballyGenerated_of_isAmple`. The reduction is
  performed here by hand, member by member of a finite affine covering of `S`, exactly as in the
  library's Stacks Tag 01VU, (1) ⟹ (3).

The two remaining steps of the source — reading an immersion into `𝐏ⁿ` over a member of the
covering as relative very ampleness (Stacks Tag 01VT, (5) ⟹ (3)) and gluing over the covering
(Stacks Tag 01VR, (2) ⟹ (1)) — are performed together by
`Stacks.VeryAmpleGlue.isRelativelyVeryAmple_of_cover`, which takes the generating families over
the members of a finite affine covering of `S` and produces an immersion of `X` into
`𝐏(f_*(N ⊗ L^{⊗ d}))` over `S` pulling `𝒪(1)` back to `N ⊗ L^{⊗ d}`.

## Main definitions

* `Stacks.VeryAmpleFixedTwist.prodTensorFamily`: **the family of products `s_α t_β` of step 6 of
  the proof of Stacks Tag 01VS, at an arbitrary comparison isomorphism `F ⊗ G ≅ H`** rather than
  at `L^{⊗ a} ⊗ L^{⊗ b} ≅ L^{⊗ (a + b)}`. This is the generalisation of
  `Stacks.ProductFamilyTwist.prodPowFamily`, and the two agree when the isomorphism is
  `Stacks.AmpleEventualGeneration.tensorPowAdd`.
* `Stacks.VeryAmpleFixedTwist.FamilyImmersion`: **the conclusion of Stacks Tag 01VS at an
  arbitrary module, carrying its generating family** — a finite family of global sections
  generating every stalk whose pinned morphism to projective space over the base is an immersion.
  This is `Stacks.ProductFamilyTwist.FamilyImmersionTwist` with the tensor power replaced by an
  arbitrary module, which is a strengthening of
  `Stacks.AmpleProjectiveImmersion.HasImmersionTwistOver`; see the implementation notes.
* `Stacks.VeryAmpleFixedTwist.twistRearrangeIso`:
  `L^{⊗ a} ⊗ (N ⊗ L^{⊗ b}) ≅ N ⊗ L^{⊗ (a + b)}`.
* `Stacks.VeryAmpleFixedTwist.pullbackTensorMonoidalIso`,
  `Stacks.VeryAmpleFixedTwist.pullbackTensorTwistIso`: Stacks Tag 01CD in the monoidal vocabulary
  the product family is written in, and the consequence
  `g^* (N ⊗ L^{⊗ d}) ≅ g^* N ⊗ (g^* L)^{⊗ d}`.
* `Stacks.VeryAmpleFixedTwist.EventuallyVeryAmpleFixedTwist`: **the conclusion of Stacks Tag
  0FVC**, over `Stacks.Tag01VMVeryAmple.IsRelativelyVeryAmple`, which is Stacks Tag 01VM itself.

## Main results

* `Stacks.VeryAmpleFixedTwist.familyImmersion_tensor`: **a very ample module tensored with a
  globally generated one is very ample, with no hypothesis.** This is the substantive input of
  Stacks Tag 0FVC that the trees lacked.
* `Stacks.VeryAmpleFixedTwist.hasImmersionTwistOver_tensor`: the same read in the conclusion of
  Stacks Tag 01VS, through `Stacks.AmpleImmersionReduction.twistPullback`.
* `Stacks.VeryAmpleFixedTwist.exists_eventually_familyImmersion_tensorPowModule`: every
  sufficiently high power of an ample invertible module carries a generating family whose pinned
  morphism is an immersion — the family-carrying form of Stacks Tag 01VS, with no hypothesis.
* `Stacks.VeryAmpleFixedTwist.eventually_familyImmersion_tensor`: **Stacks Tag 0FVC's engine**
  — for `f` locally of finite type, `L` *absolutely* ample and `N` arbitrary invertible, every
  sufficiently high `N ⊗ L^{⊗ d}` carries a finite generating family of global sections whose
  pinned morphism to projective space over `S` is an immersion.
* `Stacks.VeryAmpleFixedTwist.eventuallyVeryAmpleFixedTwist_of_isRelativelyAmple`: **Stacks Tag
  0FVC**. The `example` in the last section writes its conclusion out, with the source's binders,
  so that the faithfulness of the statement is checked by elaboration rather than asserted here.

## The proof, step by step

Written against the source's own proof:

* *"By Lemma 02NQ we reduce to the case `S` is affine."* Performed in the form the library's Stacks
  Tag 01VU uses: a finite affine covering of the quasi-compact base with one degree bound valid on
  every member, so that the degrees match across members and the gluing step has something to
  glue.
* *"Combining Lemma 01VT and Properties, Proposition 01Q3 we can find an integer `d₀` such that
  `N ⊗ L^{⊗ d₀}` is globally generated. Choose global sections `s₀, …, sₙ` which generate it."*
  Proved. Clause (7) of Stacks Tag 01Q3 is
  `Stacks.AmpleLocalGeneration.isEventuallyGloballyGenerated_of_isAmple`, proved with no
  hypothesis; `N` is quasi-coherent and of finite type because it is invertible
  (`Stacks.AmpleGlobalGeneration.isQuasicoherent_of_isInvertibleModule`,
  `Stacks.AmpleEventualGeneration.isFiniteType_of_isInvertibleModule`), and
  `Stacks.StalkwiseGeneration.exists_generatesStalks_of_isFinGen` converts the epimorphism form
  of generation into the stalkwise form the morphism of Stacks Tag 01NE consumes.
* *"This determines a morphism `j : X → 𝐏ⁿ_S` over `S`."* Proved, as
  `Stacks.ProjGlobalSectionsAppTop.exists_hom_projectiveSpaceOver_of_generatesStalks`; the twist
  is `Stacks.AmpleImmersionReduction.twistPullback`.
* *"By Lemma 01VT we can also pick an integer `d₁` such that for all `d ≥ d₁` there exist sections
  of `L^{⊗ d}` which generate it and define an immersion `j_d : X → 𝐏^{n(d)}_S`."* Proved, as
  `exists_eventually_familyImmersion_tensorPowModule`, from
  `Stacks.ChartImmersionFinish.chartImmersion`,
  `Stacks.ProductFamilyRatio.productFamilyImmersion` and
  `Stacks.StalkwiseGeneration.eventuallyGeneratesStalksPowers_of_isAmple`, all three theorems.
* *"Then for `d ≥ d₀ + d₁` consider the morphism defined by `s_j ⊗ t_{d - d₀, i}`. This morphism
  is an immersion as it is the composition `X → 𝐏ⁿ_S ×_S 𝐏^{n(d-d₀)}_S → 𝐏^{…}_S` where the
  second is the Segre embedding."* Proved, as `familyImmersion_tensor`, **without the Segre
  embedding**: see "Implementation notes".
* *"As `𝐏ⁿ_B` is a projective bundle over `B`"* (Stacks Tag 01VT's (5) ⟹ (3)), and the gluing of
  relative very ampleness over the covering of the base (Stacks Tag 01VR's (2) ⟹ (1)). Both are
  `Stacks.VeryAmpleGlue.isRelativelyVeryAmple_of_cover`, applied to the families of the previous
  step over the members of the covering. It follows the source's route for Stacks Tag 01VR
  through `E = f_*(N ⊗ L^{⊗ d})`: the morphism `X ⟶ 𝐏(E)` of Stacks Tag 01O9 attached to
  `f^* Sym(E) ⟶ ⨁_n (N ⊗ L^{⊗ d})^{⊗ n}` is an immersion chart by chart, because over each member
  it factors the immersion pinned by the family, and it pulls `𝒪_{𝐏(E)}(1)` back to
  `N ⊗ L^{⊗ d}`.

## Implementation notes

**The Segre embedding is not used, and the twist never travels along one.** The source's sentence
"`i` is the composition … and the second morphism is the Segre embedding" is replaced by the chart
computation of `StacksFrontier/AlgebraicGeometry/ProductFamilyRatio/Basic.lean`: being an immersion
is Zariski local on the target, the charts of the product family cover `X`, and on the chart at
`T_{αβ}` the restriction of the product-family morphism composed with the *linear projection*
`Stacks.ProductFamilyRatio.chartProj`, `T_{α'} ↦ T_{α'β}`, is the restriction of the first
family's morphism, which is an immersion; `AlgebraicGeometry.IsImmersion.of_comp` finishes. The
arithmetic behind that is `(s_{α'} t_β)/(s_α t_β) = s_{α'}/s_α`, which is
`Stacks.ProductFamilyRatio.ratio_prodFamily` and is already stated for arbitrary modules. What had
to be generalised is only the three chart lemmas about the family that pins the composite
(`prodTensorFamily_segreIdx`, `nvCover_prodTensorFamily_le_left`, `ratio_prodTensorFamily`), which
are the present file's versions of the `ProductPower` section there with
`Stacks.AmpleEventualGeneration.tensorPowAdd` replaced by an arbitrary isomorphism; the transport
identification `Stacks.ProductFamilyRatio.resLE_comp_chartProj` they feed is already stated at two
arbitrary modules and is reused verbatim.

**Very ampleness enters `familyImmersion_tensor` in the family-carrying form, and that is not a
weakening of the result but is a genuine restriction on its reuse.**
`Stacks.VeryAmpleFixedTwist.FamilyImmersion` asserts more than
`Stacks.AmpleProjectiveImmersion.HasImmersionTwistOver`: it names the generating family and says
that *every* morphism pinned by it is an immersion, where the latter is existential in the
morphism and forgets the family. The implication `FamilyImmersion ⟹ HasImmersionTwistOver` is
`hasImmersionTwistOver_of_familyImmersion`; the converse is not available, and
`StacksFrontier/AlgebraicGeometry/ProductFamilyRatio/Basic.lean` records why — a family cannot be
recovered from `HasImmersionTwistOver`. Nothing is lost for Stacks Tag 0FVC, because every
immersion the proof consumes is produced by the family-carrying machinery and the family is
carried the whole way; but a consumer holding only `HasImmersionTwistOver` cannot feed it to
`familyImmersion_tensor`.

**Degrees of `L` are integers, the final quantifier is over naturals.** `Stacks.Ample`
`tensorPowModule` is indexed by `ℤ`, so the engine's bookkeeping is in `ℤ`, while Stacks Tag
0FVC's "for all `d ≫ 1`" is transcribed as `∃ d₀ : ℕ, 1 ≤ d₀ ∧ ∀ d : ℕ, d₀ ≤ d` with the module
taken at `(d : ℤ)` — the shape of `Stacks.VeryAmplePowersQuasiCompactBase.EventuallyVeryAmplePower`
and of `Stacks.AmpleProjectiveImmersion.EventualImmersionTwist`, with the bound forced positive.

**The tensor product is the monoidal one on `X.Modules`.** `Stacks.Ample.tensorPowModule`,
`Stacks.AmpleEventualGeneration.tensorPowAdd` and
`Stacks.ProductFamilyTwist.prodSection` are all written over
`Stacks.SheafInternalHom.schemeMonoidalCategory`, so `N ⊗ L^{⊗ d}` is read there too and the
braiding of `Stacks.SectionRingGeometric.schemeBraidedCategory` is what `twistRearrangeIso` uses.
`AlgebraicGeometry.externalTensorProduct` and
`Stacks.SheafOfModules.TensorStalkRingedSpace.tensorSheaf` do not occur anywhere below, which is
why the identification of those two tensor products — recorded as missing in
`StacksFrontier/AlgebraicGeometry/ExternalTensorPullback/Basic.lean` — is not needed. Pullback is
crossed in the `Stacks.RelativeVeryAmple.tensorModules` spelling, where Stacks Tag 01CD is proved,
and `Stacks.AmplePullbackPart1.tensorIsoTensorModules` returns to the monoidal one; that round
trip is `pullbackTensorMonoidalIso`.

**Quasi-compactness of `S` is `CompactSpace S`** and finite type is `LocallyOfFiniteType`
together with `QuasiCompact`, as elsewhere in these trees, with quasi-compactness of `f` taken
from the first component of relative ampleness rather than assumed.

## References

* [Stacks Project, Tag 0FVC](https://stacks.math.columbia.edu/tag/0FVC)
* [Stacks Project, Tag 01VU](https://stacks.math.columbia.edu/tag/01VU)
* [Stacks Project, Tag 01VT](https://stacks.math.columbia.edu/tag/01VT)
* [Stacks Project, Tag 01VR](https://stacks.math.columbia.edu/tag/01VR)
* [Stacks Project, Tag 01VS](https://stacks.math.columbia.edu/tag/01VS)
* [Stacks Project, Tag 01VM](https://stacks.math.columbia.edu/tag/01VM)
* [Stacks Project, Tag 01VH](https://stacks.math.columbia.edu/tag/01VH)
* [Stacks Project, Tag 02NQ](https://stacks.math.columbia.edu/tag/02NQ)
* [Stacks Project, Tag 02NR](https://stacks.math.columbia.edu/tag/02NR)
* [Stacks Project, Tag 01Q3](https://stacks.math.columbia.edu/tag/01Q3)
* [Stacks Project, Tag 01NE](https://stacks.math.columbia.edu/tag/01NE)
* [Stacks Project, Tag 01WD](https://stacks.math.columbia.edu/tag/01WD)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 01CY](https://stacks.math.columbia.edu/tag/01CY)
* [Stacks Project, Tag 01OE](https://stacks.math.columbia.edu/tag/01OE)
* [Stacks Project, Tag 07RK](https://stacks.math.columbia.edu/tag/07RK)
* [Stacks Project, Tag 02V0](https://stacks.math.columbia.edu/tag/02V0)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.Ample Stacks.ProjectiveFromSections Stacks.AmpleProjectiveImmersion
open Stacks.SectionProduct Stacks.TensorSectionNonvanishing Stacks.SectionsToProjectiveSpace
open Stacks.ProductFamilyTwist Stacks.ProductFamilyRatio

universe u

namespace Stacks.VeryAmpleFixedTwist

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory
attribute [local instance] Stacks.TensorSectionNonvanishing.isInvertibleModule_tensorObj

variable {X : Scheme.{u}}

/-! ### The product family at an arbitrary comparison isomorphism -/

/-- **The family of products `s_α t_β` of step 6 of the proof of [Stacks, Tag 01VS], at an
arbitrary comparison isomorphism.** From families of global sections of `F` and of `G` and an
isomorphism `F ⊗ G ≅ H`, the family of pairwise products read in `H`, indexed by the homogeneous
coordinates of `ℙ^{nm+n+m}` through `Stacks.ProductFamilyTwist.segreIndexEquiv`.

This is `Stacks.ProductFamilyTwist.prodPowFamily` with
`Stacks.AmpleEventualGeneration.tensorPowAdd` replaced by an arbitrary isomorphism; the two agree
when the isomorphism is that one. The `Function.comp` spelling is deliberate and is the one that
file explains: written as a lambda, matching the reindexing lemma against it forces the chain of
monoidal localization instances through unification. -/
def prodTensorFamily {F G H : X.Modules} (e : (F ⊗ G : X.Modules) ≅ H) {n m : ℕ}
    (s : Fin (n + 1) → Γ(F, ⊤)) (t : Fin (m + 1) → Γ(G, ⊤)) :
    Fin (n * m + n + m + 1) → Γ(H, ⊤) :=
  (fun p => e.hom.app ⊤ (prodFamily s t p)) ∘ segreIndexEquiv n m

/-- **The products of two generating families generate the third module.** This is the generation
claim of step 6 of the proof of [Stacks, Tag 01VS]: the chart of a product is the intersection of
the two charts (the Tag 01CY remark `X_{e ⊗ f} = X_e ∩ X_f`), and neither the reindexing nor the
transport along `e` moves a nonvanishing locus. -/
theorem generatesStalks_prodTensorFamily {F G H : X.Modules} [IsInvertibleModule X F]
    [IsInvertibleModule X G] [IsInvertibleModule X H] (e : (F ⊗ G : X.Modules) ≅ H) {n m : ℕ}
    {s : Fin (n + 1) → Γ(F, ⊤)} {t : Fin (m + 1) → Γ(G, ⊤)} (hs : GeneratesStalks s)
    (ht : GeneratesStalks t) : GeneratesStalks (prodTensorFamily e s t) :=
  generatesStalks_comp_equiv (segreIndexEquiv n m)
    (generatesStalks_congr e (generatesStalks_prodFamily hs ht))

/-- The member of `Stacks.VeryAmpleFixedTwist.prodTensorFamily` at the product coordinate
`T_{αβ}` is the transported product `s_α t_β`: the reindexing is undone by
`Stacks.ProductFamilyRatio.segreIndexEquiv_segreIdx`. -/
theorem prodTensorFamily_segreIdx {F G H : X.Modules} (e : (F ⊗ G : X.Modules) ≅ H) {n m : ℕ}
    (s : Fin (n + 1) → Γ(F, ⊤)) (t : Fin (m + 1) → Γ(G, ⊤)) (α : Fin (n + 1))
    (β : Fin (m + 1)) :
    prodTensorFamily e s t (segreIdx n m α β) = e.hom.app ⊤ (prodFamily s t (α, β)) :=
  congrArg (fun p => e.hom.app ⊤ (prodFamily s t p)) (segreIndexEquiv_segreIdx n m α β)

/-- The chart of `Stacks.VeryAmpleFixedTwist.prodTensorFamily` at the product coordinate `T_{αβ}`
is the chart of the transported product family at `(α, β)`. -/
theorem nvCover_prodTensorFamily_segreIdx {F G H : X.Modules} [IsInvertibleModule X H]
    (e : (F ⊗ G : X.Modules) ≅ H) {n m : ℕ} (s : Fin (n + 1) → Γ(F, ⊤))
    (t : Fin (m + 1) → Γ(G, ⊤)) (α : Fin (n + 1)) (β : Fin (m + 1)) :
    nvCover (prodTensorFamily e s t) (segreIdx n m α β) =
      nvCover (fun p => e.hom.app ⊤ (prodFamily s t p)) (α, β) :=
  congrArg (nvOpen H) (prodTensorFamily_segreIdx e s t α β)

/-- **The chart of `Stacks.VeryAmpleFixedTwist.prodTensorFamily` at `T_{αβ}` lies in the chart of
the first family at `α`.** This is the Tag 01CY remark after the two transports the family carries,
the reindexing and the isomorphism `e`. -/
theorem nvCover_prodTensorFamily_le_left {F G H : X.Modules} [IsInvertibleModule X F]
    [IsInvertibleModule X G] [IsInvertibleModule X H] (e : (F ⊗ G : X.Modules) ≅ H) {n m : ℕ}
    (s : Fin (n + 1) → Γ(F, ⊤)) (t : Fin (m + 1) → Γ(G, ⊤)) (α : Fin (n + 1))
    (β : Fin (m + 1)) :
    nvCover (prodTensorFamily e s t) (segreIdx n m α β) ≤ nvCover s α :=
  (nvCover_prodTensorFamily_segreIdx e s t α β).le.trans
    ((nvCover_congr_le e (prodFamily s t) (α, β)).trans (nvCover_prodFamily_le_left s t (α, β)))

/-- **The coordinate ratios of `Stacks.VeryAmpleFixedTwist.prodTensorFamily` along a fixed second
index are the coordinate ratios of the first family**: `(s_{α'} t_β)/(s_α t_β) = s_{α'}/s_α` on the
chart at `T_{αβ}`.

This is the arithmetic of step 6 of the proof of [Stacks, Tag 01VS]. It is
`Stacks.ProductFamilyRatio.ratio_prodFamily` — which is already stated for arbitrary modules —
carried across `e` by `Stacks.ProductFamilyRatio.ratio_congr` and across the reindexing, and it is
the input to the identification of the product-family chart morphism with the first family's. -/
theorem ratio_prodTensorFamily {F G H : X.Modules} [IsInvertibleModule X F]
    [IsInvertibleModule X G] [IsInvertibleModule X H] (e : (F ⊗ G : X.Modules) ≅ H) {n m : ℕ}
    (s : Fin (n + 1) → Γ(F, ⊤)) (t : Fin (m + 1) → Γ(G, ⊤)) (α : Fin (n + 1)) (β : Fin (m + 1))
    (α' : Fin (n + 1)) :
    ratio (prodTensorFamily e s t) (segreIdx n m α β) (segreIdx n m α' β) =
      resO (nvCover_prodTensorFamily_le_left e s t α β) (ratio s α α') := by
  have hle : nvCover (prodTensorFamily e s t) (segreIdx n m α β) ≤
      nvCover (fun p => e.hom.app ⊤ (prodFamily s t p)) (α, β) :=
    (nvCover_prodTensorFamily_segreIdx e s t α β).le
  have hQ := resO_ratio_smul (fun p => e.hom.app ⊤ (prodFamily s t p)) hle (α', β)
  rw [ratio_congr, ratio_prodFamily, Stacks.ChartImmersionFinish.resO_resO,
    Stacks.ChartImmersionFinish.resO_resO] at hQ
  refine (eq_div (prodTensorFamily e s t (segreIdx n m α β)) le_rfl ?_).symm
  have hres : ∀ a : Fin (n + 1),
      resT (nvCover (prodTensorFamily e s t) (segreIdx n m α β))
          (prodTensorFamily e s t (segreIdx n m a β)) =
        resT (nvCover (prodTensorFamily e s t) (segreIdx n m α β))
          (e.hom.app ⊤ (prodFamily s t (a, β))) :=
    fun a => congrArg _ (prodTensorFamily_segreIdx e s t a β)
  refine Eq.trans ?_ (Eq.trans hQ ?_)
  · exact congrArg (fun z => resO (nvCover_prodTensorFamily_le_left e s t α β) (ratio s α α') • z)
      (hres α)
  · exact (hres α').symm

/-! ### The family-carrying immersion-twist conclusion at an arbitrary module -/

/-- **The conclusion of [Stacks, Tag 01VS] at an arbitrary module, carrying its generating
family.** There is a finite family of global sections of `M` generating every stalk such that
every morphism to projective space over `S` pinned by it, and lying over `f`, is an immersion.

This is `Stacks.ProductFamilyTwist.FamilyImmersionTwist` with the tensor power replaced by an
arbitrary module — the two agree at a tensor power, by
`Stacks.VeryAmpleFixedTwist.familyImmersion_tensorPowModule_iff`, which is `Iff.rfl`. It is
*stronger* than `Stacks.AmpleProjectiveImmersion.HasImmersionTwistOver`, which is existential in
the morphism and forgets the family; see the implementation notes for why the strengthening is
what the induction needs and what it costs a consumer. -/
def FamilyImmersion {S : Scheme.{u}} (f : X ⟶ S) (M : X.Modules) [IsInvertibleModule X M] :
    Prop :=
  ∃ (n : ℕ) (s : Fin (n + 1) → Γ(M, ⊤)), GeneratesStalks s ∧
    ∀ p : X ⟶ projectiveSpaceOver n S,
      p ≫ pullback.fst (terminal.from S)
          (terminal.from (projectiveSpaceAtUniverse.{u} n)) = f →
        (∀ i, (nvCover s i).ι ≫ p ≫ projectiveSpaceOver.toIntegralAtUniverse n S =
          toProjectiveSpaceAtUniverse (chartRatio s i) (span_range_chartRatio s i)) →
        IsImmersion p

/-- **`Stacks.VeryAmpleFixedTwist.FamilyImmersion` at a tensor power is
`Stacks.ProductFamilyTwist.FamilyImmersionTwist`**, on the nose: the generalisation changes no
binder. Recorded so that the specialisation is checked by elaboration rather than asserted. -/
theorem familyImmersion_tensorPowModule_iff {S : Scheme.{u}} (f : X ⟶ S) (L : X.Modules)
    [IsInvertibleModule X L] (d : ℤ) :
    FamilyImmersion f (tensorPowModule X L d) ↔ FamilyImmersionTwist f L d := Iff.rfl

/-- **The family-carrying conclusion gives [Stacks, Tag 01VS]'s conclusion at that module.** The
morphism is the one pinned by the family
(`Stacks.ProjGlobalSectionsAppTop.exists_hom_projectiveSpaceOver_of_generatesStalks`), the
immersion property is the predicate's, and the twist is the hypothesis. It is taken as a
hypothesis here only to keep this lemma free of the monoidal preamble;
`Stacks.AmpleImmersionReduction.twistPullback` discharges it, and
`Stacks.VeryAmpleFixedTwist.hasImmersionTwistOver_tensor` spends it. -/
theorem hasImmersionTwistOver_of_familyImmersion {S : Scheme.{u}} (f : X ⟶ S) (M : X.Modules)
    [IsInvertibleModule X M] (htw : Stacks.AmpleImmersionReduction.TwistPullback f)
    (h : FamilyImmersion f M) : HasImmersionTwistOver f M := by
  obtain ⟨n, s, hs, himm⟩ := h
  obtain ⟨p, hpf, hchart⟩ :=
    Stacks.ProjGlobalSectionsAppTop.exists_hom_projectiveSpaceOver_of_generatesStalks s hs f
  exact ⟨n, p, himm p hpf hchart, hpf, htw _ n s hs p hpf hchart⟩

/-! ### Very ample tensor globally generated is very ample -/

/-- **A VERY AMPLE MODULE TENSORED WITH A GLOBALLY GENERATED ONE IS VERY AMPLE.** Let `F` carry a
generating family whose pinned morphism to projective space over `S` is an immersion, let `G`
carry any finite family of global sections generating every stalk, and let `F ⊗ G ≅ H`. Then `H`
carries a generating family whose pinned morphism is an immersion.

This is the substantive input of [Stacks, Tag 0FVC], and it has **no hypothesis**. The generating
family of `H` is the family of products `s_α t_β`, which generates by
`Stacks.VeryAmpleFixedTwist.generatesStalks_prodTensorFamily`. The source proves the immersion
property with the Segre embedding; this proof uses none. Being an immersion is Zariski local on
the target and the charts of the product family cover `X`
(`Stacks.ChartImmersionFinish.isImmersion_of_isImmersion_standardChart_subcover`), so it suffices
that on the chart at `T_{αβ}` the restriction `X_{s_α t_β} ⟶ D₊(T_{αβ})` is an immersion; composed
with the linear projection `Stacks.ProductFamilyRatio.chartProj`, `T_{α'} ↦ T_{α'β}`, that
restriction becomes the restriction of the first family's morphism `j` — this is
`Stacks.ProductFamilyRatio.resLE_comp_chartProj`, whose arithmetic input is
`Stacks.VeryAmpleFixedTwist.ratio_prodTensorFamily` — and `j` is an immersion by hypothesis, so
`AlgebraicGeometry.IsImmersion.of_comp` finishes.

**It is not [Stacks, Tag 0FVC] and carries no attribute**: no ampleness, no finite-type
hypothesis, no base condition and no degree occurs in it. -/
@[ega "II 4.4.8" "special case"]
theorem familyImmersion_tensor {S : Scheme.{u}} (f : X ⟶ S) {F G H : X.Modules}
    [IsInvertibleModule X F] [IsInvertibleModule X G] [IsInvertibleModule X H]
    (e : (F ⊗ G : X.Modules) ≅ H) (hF : FamilyImmersion f F) {m : ℕ}
    {t : Fin (m + 1) → Γ(G, ⊤)} (ht : GeneratesStalks t) : FamilyImmersion f H := by
  obtain ⟨n, s, hs, himm⟩ := hF
  have hgen : GeneratesStalks (prodTensorFamily e s t) :=
    generatesStalks_prodTensorFamily e hs ht
  refine ⟨n * m + n + m, prodTensorFamily e s t, hgen, fun q hqf hqchart => ?_⟩
  obtain ⟨j, hjf, hjchart⟩ :=
    Stacks.ProjGlobalSectionsAppTop.exists_hom_projectiveSpaceOver_of_generatesStalks s hs f
  have hjimm : IsImmersion j := himm j hjf hjchart
  refine Stacks.ChartImmersionFinish.isImmersion_of_isImmersion_standardChart_subcover
    (prodTensorFamily e s t) hgen q hqchart
    (fun p : Fin (n + 1) × Fin (m + 1) => segreIdx n m p.1 p.2) ?_ ?_
  · intro x
    obtain ⟨k, hk⟩ := exists_mem_nvCover_of_generatesStalks _ hgen x
    exact ⟨segreIndexEquiv n m k, by simpa only [segreIdx_segreIndexEquiv] using hk⟩
  · rintro ⟨α, β⟩
    have hpre := Stacks.AmpleImmersionReduction.preimage_standardChart
      (prodTensorFamily e s t) hgen q hqchart (segreIdx n m α β)
    refine ⟨q.resLE (projectiveSpaceOver.standardChart (n * m + n + m) S (segreIdx n m α β))
      (nvCover (prodTensorFamily e s t) (segreIdx n m α β)) hpre.ge, ?_,
      Scheme.Hom.resLE_comp_ι _ _⟩
    have hcomp := resLE_comp_chartProj (prodTensorFamily e s t) s q hqf j hjf α β
      (hqchart (segreIdx n m α β)) (hjchart α) (nvCover_prodTensorFamily_le_left e s t α β)
      (ratio_prodTensorFamily e s t α β) hpre.ge
    have hcomp' : IsImmersion
        (q.resLE (projectiveSpaceOver.standardChart (n * m + n + m) S (segreIdx n m α β))
          (nvCover (prodTensorFamily e s t) (segreIdx n m α β)) hpre.ge ≫
            chartProj.{u} n m S α β) := by
      rw [hcomp]; infer_instance
    exact IsImmersion.of_comp _ (chartProj.{u} n m S α β)

/-- **A very ample module tensored with a globally generated one is very ample, in the conclusion
of Stacks Tag 01VS.** From `Stacks.VeryAmpleFixedTwist.familyImmersion_tensor` by
`Stacks.AmpleImmersionReduction.twistPullback`, which is a theorem, so this too has no
hypothesis. -/
@[ega "II 4.4.8" "special case"]
theorem hasImmersionTwistOver_tensor {S : Scheme.{u}} (f : X ⟶ S) {F G H : X.Modules}
    [IsInvertibleModule X F] [IsInvertibleModule X G] [IsInvertibleModule X H]
    (e : (F ⊗ G : X.Modules) ≅ H) (hF : FamilyImmersion f F) {m : ℕ}
    {t : Fin (m + 1) → Γ(G, ⊤)} (ht : GeneratesStalks t) : HasImmersionTwistOver f H :=
  hasImmersionTwistOver_of_familyImmersion f H (Stacks.AmpleImmersionReduction.twistPullback f)
    (familyImmersion_tensor f e hF ht)

/-! ### The rearrangement isomorphism -/

/-- **`L^{⊗ a} ⊗ (N ⊗ L^{⊗ b}) ≅ N ⊗ L^{⊗ (a + b)}`.** The associator, the braiding of
`Stacks.SectionRingGeometric.schemeBraidedCategory` and
`Stacks.AmpleEventualGeneration.tensorPowAdd`, in that order. The power of `L` is the *left*
factor because `Stacks.VeryAmpleFixedTwist.familyImmersion_tensor` asks the immersion-pinned
family for the left factor, and it is the power that is immersion-pinned. -/
def twistRearrangeIso (N L : X.Modules) [IsInvertibleModule X L] {a b c : ℤ} (h : a + b = c) :
    (tensorPowModule X L a ⊗ (N ⊗ tensorPowModule X L b) : X.Modules) ≅
      (N ⊗ tensorPowModule X L c : X.Modules) :=
  (α_ (tensorPowModule X L a) N (tensorPowModule X L b)).symm ≪≫
    (β_ (tensorPowModule X L a) N ⊗ᵢ Iso.refl (tensorPowModule X L b)) ≪≫
    α_ N (tensorPowModule X L a) (tensorPowModule X L b) ≪≫
    (Iso.refl N ⊗ᵢ Stacks.AmpleEventualGeneration.tensorPowAdd h)

/-! ### Every sufficiently high power carries a family-immersion -/

/-- **Every sufficiently high tensor power of an ample invertible module carries a generating
family whose pinned morphism is an immersion.** This is the family-carrying form of
[Stacks, Tag 01VS], and it has no hypothesis: the base degree is
`Stacks.ChartImmersionFinish.chartImmersion`, the induction step is
`Stacks.ProductFamilyRatio.productFamilyImmersion`, and the generating families of the
intermediate powers that the step consumes are
`Stacks.StalkwiseGeneration.eventuallyGeneratesStalksPowers_of_isAmple`, all three theorems.

`Stacks.ProductFamilyRatio.immersionTwistGap_of_eventuallyGeneratesStalksPowers` is the same
argument ending in `Stacks.AmpleProjectiveImmersion.HasImmersionTwistOver`, which forgets the
family; the family is what [Stacks, Tag 0FVC] needs, which is why the argument is run again
here. -/
@[ega "II 4.5.8" "special case"]
theorem exists_eventually_familyImmersion_tensorPowModule {S : Scheme.{u}} (f : X ⟶ S)
    (L : X.Modules) [IsInvertibleModule X L] (hL : IsAmple X L) (hft : LocallyOfFiniteType f) :
    ∃ c₀ : ℤ, 1 ≤ c₀ ∧ ∀ c : ℤ, c₀ ≤ c → FamilyImmersion f (tensorPowModule X L c) := by
  obtain ⟨N₁, hN₁, hfam⟩ := exists_familyImmersionTwist_of_chartImmersion f L
    (Stacks.ChartImmersionFinish.chartImmersion f L) hL hft
  obtain ⟨b₀, hb₀⟩ := Stacks.StalkwiseGeneration.eventuallyGeneratesStalksPowers_of_isAmple L hL
  refine ⟨max 1 (N₁ + b₀), le_max_left _ _, fun c hc => ?_⟩
  have hc' : max 1 (N₁ + b₀) ≤ c := hc
  have hb : b₀ ≤ c - N₁ := by
    have := le_trans (le_max_right 1 (N₁ + b₀)) hc'
    omega
  obtain ⟨m, t, ht⟩ := hb₀ (c - N₁) hb
  have key := familyImmersionTwist_add f L (productFamilyImmersion f L) hfam ht
  rw [show N₁ + (c - N₁) = c from by ring] at key
  exact key

/-! ### Stacks Tag 0FVC for an absolutely ample module: the engine -/

/-- **The engine of [Stacks, Tag 0FVC].** For `f : X ⟶ S` locally of finite type, `L` an
*absolutely* ample invertible `𝒪_X`-module and `N` any invertible `𝒪_X`-module, there is a
`d₀ ≥ 1` such that for every `d ≥ d₀` the module `N ⊗ L^{⊗ d}` carries a finite generating family
of global sections whose pinned morphism `X ⟶ ℙⁿ_S` over `S` is an immersion.

This is the source's proof after its reduction to an affine base. Clause (7) of
[Stacks, Tag 01Q3] — `Stacks.AmpleLocalGeneration.isEventuallyGloballyGenerated_of_isAmple` —
applied to `N`, which is quasi-coherent and of finite type because it is invertible, gives a
`b ≥ 0` with `N ⊗ L^{⊗ b}` generated by finitely many global sections;
`Stacks.StalkwiseGeneration.exists_generatesStalks_of_isFinGen` puts that generation in the
stalkwise form the morphism of [Stacks, Tag 01NE] consumes.
`Stacks.VeryAmpleFixedTwist.exists_eventually_familyImmersion_tensorPowModule` gives an immersion-
pinned family of `L^{⊗ c}` for every large `c`, and
`Stacks.VeryAmpleFixedTwist.familyImmersion_tensor` multiplies the two at `c = d - b`, along
`Stacks.VeryAmpleFixedTwist.twistRearrangeIso`. -/
@[ega "II 4.5.8" "more general"]
theorem eventually_familyImmersion_tensor {S : Scheme.{u}} (f : X ⟶ S) (N L : X.Modules)
    [IsInvertibleModule X N] [IsInvertibleModule X L] (hL : IsAmple X L)
    (hft : LocallyOfFiniteType f) :
    ∃ d₀ : ℕ, 1 ≤ d₀ ∧ ∀ d : ℕ, d₀ ≤ d →
      FamilyImmersion f (N ⊗ tensorPowModule X L (d : ℤ)) := by
  obtain ⟨c₀, hc₀, hc⟩ := exists_eventually_familyImmersion_tensorPowModule f L hL hft
  obtain ⟨n₀, hn₀⟩ := Stacks.AmpleLocalGeneration.isEventuallyGloballyGenerated_of_isAmple L hL N
    (Stacks.AmpleGlobalGeneration.isQuasicoherent_of_isInvertibleModule N)
    (Stacks.AmpleEventualGeneration.isFiniteType_of_isInvertibleModule N)
  obtain ⟨σ, hσ⟩ := hn₀ (max 0 n₀) (le_max_right _ _)
  obtain ⟨m, t, ht⟩ := Stacks.StalkwiseGeneration.exists_generatesStalks_of_isFinGen
    (⟨σ, hσ⟩ : Stacks.AmpleEventualGeneration.IsFinGen
      (N ⊗ tensorPowModule X L (max 0 n₀)))
  have hb0 : (0 : ℤ) ≤ max 0 n₀ := le_max_left _ _
  refine ⟨(c₀ + max 0 n₀).toNat, by omega, fun d hd => ?_⟩
  have hdz : c₀ + max 0 n₀ ≤ (d : ℤ) := by omega
  have hcc : c₀ ≤ (d : ℤ) - max 0 n₀ := by omega
  exact familyImmersion_tensor f
    (twistRearrangeIso N L (show (d : ℤ) - max 0 n₀ + max 0 n₀ = (d : ℤ) from by ring))
    (hc _ hcc) ht

/-! ### Pullback and the fixed twist -/

/-- **[Stacks, Tag 01CD] in the monoidal vocabulary**: `g^* (A ⊗ B) ≅ g^* A ⊗ g^* B`, with both
tensor products taken in `Stacks.SheafInternalHom.schemeMonoidalCategory`.

No attribute: Tag 01CD is already live on `Stacks.PullbackTensorIso.pullbackTensorIso`, and this is
that statement read through `Stacks.AmplePullbackPart1.tensorIsoTensorModules` on each side. The
round trip exists because pullback is crossed where Tag 01CD is stated, in the
`Stacks.RelativeVeryAmple.tensorModules` spelling, while the product family is written in the
monoidal one. -/
def pullbackTensorMonoidalIso {Y Z : Scheme.{u}} (g : Y ⟶ Z) (A B : Z.Modules) :
    (modulePullback g.toLRSHom.toShHom).obj (A ⊗ B : Z.Modules) ≅
      ((modulePullback g.toLRSHom.toShHom).obj A ⊗
        (modulePullback g.toLRSHom.toShHom).obj B : Y.Modules) :=
  (modulePullback g.toLRSHom.toShHom).mapIso
      (Stacks.AmplePullbackPart1.tensorIsoTensorModules Z A B) ≪≫
    Stacks.RelativeVeryAmple.pullbackTensorModulesIso g A B ≪≫
    (Stacks.AmplePullbackPart1.tensorIsoTensorModules Y
      ((modulePullback g.toLRSHom.toShHom).obj A)
      ((modulePullback g.toLRSHom.toShHom).obj B)).symm

/-- **`g^* (N ⊗ L^{⊗ d}) ≅ g^* N ⊗ (g^* L)^{⊗ d}`.** The previous isomorphism whiskered by
`Stacks.RelativeVeryAmple.pullbackTensorPowModuleIso`, which is Tag 01CD iterated. This is the one
place where the restriction of the twisted power and the twisted power of the restrictions are
interchanged. -/
def pullbackTensorTwistIso {Y Z : Scheme.{u}} (g : Y ⟶ Z) (N L : Z.Modules)
    [IsInvertibleModule Z L] (d : ℕ) :
    (modulePullback g.toLRSHom.toShHom).obj
        (N ⊗ tensorPowModule Z L (d : ℤ) : Z.Modules) ≅
      ((modulePullback g.toLRSHom.toShHom).obj N ⊗
        tensorPowModule Y ((modulePullback g.toLRSHom.toShHom).obj L) (d : ℤ) : Y.Modules) :=
  pullbackTensorMonoidalIso g N (tensorPowModule Z L (d : ℤ)) ≪≫
    (show ((modulePullback g.toLRSHom.toShHom).obj N ⊗
          (modulePullback g.toLRSHom.toShHom).obj (tensorPowModule Z L (d : ℤ)) :
            Y.Modules) ≅
        ((modulePullback g.toLRSHom.toShHom).obj N ⊗
          tensorPowModule Y ((modulePullback g.toLRSHom.toShHom).obj L) (d : ℤ) : Y.Modules)
      from whiskerLeftIso _ (Stacks.RelativeVeryAmple.pullbackTensorPowModuleIso g L d))

/-! ### Stacks Tag 0FVC -/

/-- **The conclusion of [Stacks, Tag 0FVC]**: every sufficiently high `N ⊗ L^{⊗ d}` is very ample
relative to `f`.

Relative very ampleness is `Stacks.Tag01VMVeryAmple.IsRelativelyVeryAmple`, [Stacks, Tag 01VM]
itself — an immersion of `X` into the projective bundle `𝐏(E)` of a quasi-coherent `𝒪_S`-module,
over `S`, pulling `𝒪_{𝐏(E)}(1)` back to the module — and not a surrogate; it is the same predicate
the library's Stacks Tag 01VU is stated over. "For all `d ≫ 1`" is the shape
`Stacks.VeryAmplePowersQuasiCompactBase.EventuallyVeryAmplePower` uses. -/
def EventuallyVeryAmpleFixedTwist {S : Scheme.{u}} (f : X ⟶ S) (N L : X.Modules)
    [IsInvertibleModule X N] [IsInvertibleModule X L] : Prop :=
  ∃ d₀ : ℕ, 1 ≤ d₀ ∧ ∀ d : ℕ, d₀ ≤ d →
    Stacks.Tag01VMVeryAmple.IsRelativelyVeryAmple f (N ⊗ tensorPowModule X L (d : ℤ))

/-- **Stacks Tag 0FVC.** Let `f : X ⟶ S` be a morphism of schemes and `N`, `L` invertible
`𝒪_X`-modules. If `S` is quasi-compact, `f` is of finite type and `L` is `f`-relatively ample,
then `N ⊗ L^{⊗ d}` is `f`-relatively very ample for every sufficiently large `d`.

The proof is the source's. The affine open covering `S.affineCover.finiteSubcover` of `S` is
finite because `S` is quasi-compact, and
`Stacks.VeryAmpleFixedTwist.eventually_familyImmersion_tensor` at the restriction of `f`, whose
ampleness hypothesis is the defining clause of relative ampleness, gives over each member a bound
past which `N ⊗ L^{⊗ d}` restricted to the member carries a generating family pinning an
immersion into projective space over the member — the source's reduction to an affine base, Tag
02NQ, performed by hand so that the engine runs with absolute ampleness. The largest of the
finitely many bounds serves every member, and
`Stacks.VeryAmpleGlue.isRelativelyVeryAmple_of_cover` (Stacks Tag 01VT's (5) ⟹ (3) and Stacks Tag
01VR's (2) ⟹ (1) together) turns the families into relative very ampleness over `S`; the
restriction of `N ⊗ L^{⊗ d}` is matched with the module the families live on by
`Stacks.VeryAmpleFixedTwist.pullbackTensorTwistIso`. Quasi-compactness of `f` is taken from
relative ampleness. -/
@[stacks 0FVC,
  ega "II 4.5.10" "(ii): ample implies e)",
  ega "II 4.5.11" "more general",
  ega "II 4.6.12"]
theorem eventuallyVeryAmpleFixedTwist_of_isRelativelyAmple {S : Scheme.{u}}
    (f : X ⟶ S) (N L : X.Modules) [IsInvertibleModule X N] [IsInvertibleModule X L]
    [CompactSpace S] [LocallyOfFiniteType f]
    (hL : Stacks.RelativeAmple.IsRelativelyAmple f L) :
    EventuallyVeryAmpleFixedTwist f N L := by
  classical
  have : QuasiCompact f := hL.1
  set 𝒰 := S.affineCover.finiteSubcover with h𝒰
  have hVaff : ∀ j : 𝒰.I₀, IsAffineOpen (𝒰.f j).opensRange := fun j =>
    isAffineOpen_opensRange _
  choose d₀ hd₀ hd using fun j : 𝒰.I₀ =>
    eventually_familyImmersion_tensor (f ∣_ (𝒰.f j).opensRange)
      ((modulePullback (f ⁻¹ᵁ (𝒰.f j).opensRange).ι.toLRSHom.toShHom).obj N)
      ((modulePullback (f ⁻¹ᵁ (𝒰.f j).opensRange).ι.toLRSHom.toShHom).obj L)
      (hL.2 _ (hVaff j)) inferInstance
  refine ⟨max 1 (Finset.univ.sup d₀), le_max_left _ _, fun d hdd => ?_⟩
  have hd' := fun j : 𝒰.I₀ => hd j d
    (le_trans (le_trans (Finset.le_sup (Finset.mem_univ j)) (le_max_right _ _)) hdd)
  choose n s hs himm using hd'
  let M : ∀ j : 𝒰.I₀, (f ⁻¹ᵁ (𝒰.f j).opensRange).toScheme.Modules := fun j =>
    (modulePullback (f ⁻¹ᵁ (𝒰.f j).opensRange).ι.toLRSHom.toShHom).obj N ⊗
      tensorPowModule _ ((modulePullback (f ⁻¹ᵁ (𝒰.f j).opensRange).ι.toLRSHom.toShHom).obj L)
        (d : ℤ)
  have : ∀ j, IsInvertibleModule _ (M j) := fun j => by
    have := Stacks.Ample.isInvertibleModule_tensorPowModule (f ⁻¹ᵁ (𝒰.f j).opensRange).toScheme
      ((modulePullback (f ⁻¹ᵁ (𝒰.f j).opensRange).ι.toLRSHom.toShHom).obj L) (d : ℤ)
    exact Stacks.TensorSectionNonvanishing.isInvertibleModule_tensorObj _ _
  exact Stacks.VeryAmpleGlue.isRelativelyVeryAmple_of_cover f (N ⊗ tensorPowModule X L (d : ℤ))
    (fun j => (𝒰.f j).opensRange) hVaff (Scheme.OpenCover.iSup_opensRange 𝒰) n M
    s hs himm fun j => λ_ _ ≪≫ pullbackTensorTwistIso (f ⁻¹ᵁ (𝒰.f j).opensRange).ι N L d

/-! ### Faithfulness: Stacks Tag 0FVC's conclusion, written out -/

section Faithfulness

/-- **Stacks Tag 0FVC, with `Stacks.VeryAmpleFixedTwist.EventuallyVeryAmpleFixedTwist` unfolded.**
The conclusion is checked by elaboration rather than asserted in prose: for `S` quasi-compact, `f`
of finite type and `L` relatively ample, there is a `d₀ ≥ 1` such that `N ⊗ L^{⊗ d}` is relatively
very ample for `f` — in the sense of Stacks Tag 01VM — for every `d ≥ d₀`. Quasi-compactness of
`f` is the hypothesis `hf`, which the proof does not use: it is taken from relative ampleness
instead, and is written here only because the source states it. -/
example {S : Scheme.{u}} (f : X ⟶ S)
    (N L : X.Modules) [IsInvertibleModule X N] [IsInvertibleModule X L] [CompactSpace S]
    [LocallyOfFiniteType f] (_hf : QuasiCompact f)
    (hL : Stacks.RelativeAmple.IsRelativelyAmple f L) :
    ∃ d₀ : ℕ, 1 ≤ d₀ ∧ ∀ d : ℕ, d₀ ≤ d →
      Stacks.Tag01VMVeryAmple.IsRelativelyVeryAmple f
        (N ⊗ tensorPowModule X L (d : ℤ) : X.Modules) :=
  eventuallyVeryAmpleFixedTwist_of_isRelativelyAmple f N L hL

end Faithfulness

end Stacks.VeryAmpleFixedTwist

end
