module

public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.BundleTensorTwist
public import StacksFrontier.AlgebraicGeometry.ExternalTensorPullback.Basic
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.ChernClasses.InvertibleTensor
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.ChernClasses.KZeroRule
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.ChernClasses.PullbackTensor
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.ChernClasses.StandingSituation
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.ChernClasses.Twist
import all StacksFrontier.AlgebraicGeometry.WeilCohomology.ChernClasses.Twist

/-!
# The Chern classes of a twist, Stacks Tag 0FI8, in the standing situation of Section 45.12

Let `ℰ` be a finite locally free `𝒪_X`-module of rank `r` and `ℒ` an invertible `𝒪_X`-module,
on an object `X` of the category `𝒞` of the standing situation of Stacks Section 45.12
(Tag 0FI4). Tag 0FI8 says
`c^A_i(ℰ ⊗ ℒ) = ∑_{j=0}^{i} binom(r - i + j, j) c^A_{i-j}(ℰ) ∪ c₁^A(ℒ)^j`.

`Stacks.WeilCohomology.ChernSetup.chernClass_tensorObj` in
`StacksFrontier.AlgebraicGeometry.WeilCohomology.ChernClasses.Twist` proves this from an
isomorphism `𝐏(ℰ) ≅ 𝐏(ℰ ⊗ ℒ)` of objects of `𝒞` over `X` and the effect of that isomorphism on
`c₁^A(𝒪(1))`, both taken as hypotheses, and with the rank of `ℰ ⊗ ℒ` assumed. This file proves the
same formula with **none** of these hypotheses, from the source's data alone.

## Main results

* `Stacks.WeilCohomology.chernClass_tensorObjRingedSpace`: **Tag 0FI8** for `ℰ` of constant rank
  `r + 1`, for every `i`, over `Stacks.WeilCohomology.SourceChernSetup` and the source's
  condition (3), clause (3)(b) and clause (3)(c).
* `Stacks.WeilCohomology.ChernSituation.totalChernClass_classOf_tensorObjRingedSpace`:
  **Tag 0FI8** for the rule `c^A` of Tag 0FI5, for `ℰ` of any constant rank `r`, `r = 0`
  included.
* `Stacks.WeilCohomology.ChernSituation.pull_totalChernClass_classOf_tensorObjRingedSpace`:
  **Tag 0FI8** for the rule `c^A` of Tag 0FI5 and an **arbitrary** finite locally free `ℰ`, read on
  every object over `X` on which `ℰ` has constant rank `r` — which is how the source's `r` is to be
  read when the rank of `ℰ` is not constant ("by the construction of `c^A_i` we may assume `ℰ` has
  constant rank `r`"). Condition (2) makes `A(X)` the product of the `A` of those loci
  (`Stacks.WeilCohomology.ChernSituation.eq_of_pull_one`), so this determines `c^A_i(ℰ ⊗ ℒ)`.
* `Stacks.WeilCohomology.QuotientBundleEmbeddingClause`: **clause (3)(c) of the source** for an
  arbitrary surjection `ℰ ⟶ 𝓕`.

## The argument

The source's proof: `P = 𝐏(ℰ)` and `P' = 𝐏(ℰ ⊗ ℒ)` are isomorphic over `X` by some `g` with
`g^*𝒪_{P'}(1) = 𝒪_P(1) ⊗ p^*ℒ` (Constructions, Lemma 27.20.1, Tag 02NC); hence
`g^*c₁^A(𝒪_{P'}(1)) = c₁^A(𝒪_P(1)) + p^*c₁^A(ℒ)`, and the formula follows from equation
45.12.1.1.

Tag 02NC for the constructed projective bundles is
`Stacks.Chow.GenuineChern.exists_bundleTensorIso`: an isomorphism of **schemes**
`𝐏(ℰ ⊗ ℒ) ≅ 𝐏(ℰ)` over `X` with `𝒪_{𝐏(ℰ ⊗ ℒ)}(1) ≅ g^*𝒪_{𝐏(ℰ)}(1) ⊗ π'^*ℒ`. Here `𝒞` is a
category presented by a functor `S : 𝒞 ⥤ Scheme`, and nothing in the source's clauses makes an
isomorphism of schemes between two objects a morphism of `𝒞`; so `A` cannot be pulled back along
`g` directly. The comparison is instead routed through the morphisms the clauses do supply
(`Stacks.WeilCohomology.exists_bundleTensor_comparison`). On `P'`, with projection `p'`:

* `p'^*ℰ` has the invertible quotient `𝒩 = g^*𝒪_{𝐏(ℰ)}(1)`, the pullback of the tautological
  quotient of `𝐏(ℰ)`, and Tag 02NC with Tag 01CD gives `𝒪_{P'}(1) ≅ 𝒩 ⊗ p'^*ℒ`, so
  `c₁^A(𝒩) = c₁^A(𝒪_{P'}(1)) - p'^*c₁^A(ℒ)` by Tag 01CX and condition (3);
* clause (3)(b) at `p'` gives `h : 𝐏(p'^*ℰ) ⟶ 𝐏(ℰ)` in `𝒞`, over `p'`, carrying
  `c₁^A(𝒪(1))` to `c₁^A(𝒪(1))`;
* clause (3)(c) at `p'^*ℰ ⟶ 𝒩` gives `i : Q = 𝐏(𝒩) ⟶ 𝐏(p'^*ℰ)` in `𝒞`, over `P'`, carrying
  `c₁^A(𝒪(1))` to `c₁^A(𝒪_Q(1))`;
* the projection `q : Q ⟶ P'` is a morphism of `𝒞` by clause (3)(a), `𝒪_Q(1) ≅ q^*𝒩` because
  the kernel of the tautological quotient of a module of rank one has rank zero, and `q^*` is
  injective on `A` by condition (4) in rank one.

So `(i ≫ h)^*c₁^A(𝒪_P(1)) = q^*(c₁^A(𝒪_{P'}(1)) - p'^*c₁^A(ℒ))` with `i ≫ h ≫ p = q ≫ p'`, and
pulling equation 45.12.1.1 for `ℰ` back along `i ≫ h` and cancelling the injective `q^*` gives that
equation in `A(P')` with `c₁^A(𝒪_P(1))` replaced by `c₁^A(𝒪_{P'}(1)) - p'^*c₁^A(ℒ)`. The rest is
the formal computation of `Stacks.WeilCohomology.eq_of_alternating_relations` in
`StacksFrontier.AlgebraicGeometry.WeilCohomology.ChernClasses.Twist` (the binomial theorem applied
to `x = (x + u) - u`, then uniqueness from condition (4) for `ℰ ⊗ ℒ`).

## The binomial coefficient

The source's `binom(r - i + j, j)` is written `(r + j - i).choose j` in `ℕ`. The two agree
whenever `r - i + j ≥ 0`. When `r - i + j < 0` the truncated subtraction gives `0` and
`(0).choose j` need not vanish, but then `i - j > r`, so the factor `c^A_{i-j}(ℰ)` vanishes and the
term is zero under either reading. No restriction on `i` is needed.

## The clause (3)(c) used

`Stacks.WeilCohomology.DivisorDatumClause` transcribes clause (3)(c) together with condition (5),
for the surjections with invertible kernel that condition (5) speaks about. The source's clause
(3)(c) is stated for **every** surjection `ℰ ⟶ 𝓕` of finite locally free modules, and the argument
above uses it for one with kernel of rank `r`.
`Stacks.WeilCohomology.QuotientBundleEmbeddingClause` is that clause, for modules of positive
constant rank (the ones whose projective bundles clause (3)(a) provides as objects of `𝒞`). It is
part of the source's **data** — an axiom of the standing situation, a closure property of `𝒞` —
and not a result: the closed immersion `𝐏(𝓕) ⟶ 𝐏(ℰ)` itself is constructed
(`Stacks.Chow.GenuineChern.bundleEmbedding`), and the identification of the twists along it is
derived
(`Stacks.WeilCohomology.BundleObject.nonempty_pullback_twist_of_isQuotientBundleEmbedding`).

## References

* [Stacks Project, Tag 0FI8](https://stacks.math.columbia.edu/tag/0FI8)
* [Stacks Project, Tag 0FI4](https://stacks.math.columbia.edu/tag/0FI4)
* [Stacks Project, Tag 0FI5](https://stacks.math.columbia.edu/tag/0FI5)
* [Stacks Project, Tag 02NC](https://stacks.math.columbia.edu/tag/02NC)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 01CX](https://stacks.math.columbia.edu/tag/01CX)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u v v₁ w

namespace Stacks.WeilCohomology

/-! ### Clause (3)(c) for an arbitrary surjection -/

/-- **Clause (3)(c) of the source's category, for an arbitrary surjection: the induced closed
immersion `𝐏(𝓕) ⟶ 𝐏(ℰ)` is a morphism of `𝒞`.** For an epimorphism `q : ℰ ⟶ 𝓕` and the
clause-(3)(a) objects `B` of `ℰ` and `B'` of `𝓕`, a morphism `i : B' ⟶ B` of `𝒞` is the induced
closed immersion when it lies over `X` and its morphism of schemes is the constructed
`Stacks.Chow.GenuineChern.bundleEmbedding`, read through the two identifications of clause (3)(a).

This is `Stacks.WeilCohomology.IsBundleEmbedding` without the restriction to a surjection whose
kernel is invertible. -/
structure IsQuotientBundleEmbedding {C : Type w} [Category.{v₁} C] {S : C ⥤ Scheme.{u}} {X : C}
    {E F : (S.obj X).Modules} (q : E ⟶ F) [Epi q] {r s : ℕ}
    (B : BundleObject S X E r) (B' : BundleObject S X F s) (i : B'.bundle ⟶ B.bundle) : Prop where
  /-- The morphism of `𝒞` lies over `X`. -/
  comp_proj : i ≫ B.proj = B'.proj
  /-- Its morphism of schemes is the induced closed immersion `𝐏(𝓕) ⟶ 𝐏(ℰ)`. -/
  map_eq : S.map i ≫ B.iso.hom =
    B'.iso.hom ≫ @Stacks.Chow.GenuineChern.bundleEmbedding (S.obj X) E F
      B.isFiniteLocallyFree B'.isFiniteLocallyFree q _

/-- **Clause (3)(c) of Stacks Section 45.12, as the source states it**: if `ℰ ⟶ 𝓕` is a surjection
onto another finite locally free `𝒪_X`-module, then the closed immersion `𝐏(𝓕) ⟶ 𝐏(ℰ)` is a
morphism of `𝒞`. It is read for modules of positive constant rank, whose projective bundles clause
(3)(a) (`Stacks.WeilCohomology.SourceChernSetup.bundleObject`) provides as objects of `𝒞`.

This is an **axiom of the source's setting** — a closure property of the category `𝒞`, listed
among the source's assumptions on `𝒞` — and not a result the source derives. Nothing else about
the closed immersion is assumed: the morphism of schemes is constructed and the identification of
the twists along it is
`Stacks.WeilCohomology.BundleObject.nonempty_pullback_twist_of_isQuotientBundleEmbedding`.
`Stacks.WeilCohomology.DivisorDatumClause` carries the same clause for a surjection with invertible
kernel, together with condition (5). -/
def QuotientBundleEmbeddingClause {C : Type w} [Category.{v₁} C] {S : C ⥤ Scheme.{u}}
    (𝔄 : SourceChernSetup.{u, v, v₁, w} C S) : Prop :=
  ∀ (X : C) (E F : (S.obj X).Modules) (q : E ⟶ F) (_hq : Epi q) (r s : ℕ)
    (hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E (r + 1))
    (hF : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} F (s + 1)),
    ∃ i : (𝔄.bundleObject X F s hF).bundle ⟶ (𝔄.bundleObject X E r hE).bundle,
      IsQuotientBundleEmbedding q (𝔄.bundleObject X E r hE) (𝔄.bundleObject X F s hF) i

namespace BundleObject

variable {C : Type w} [Category.{v₁} C] {S : C ⥤ Scheme.{u}} {X : C}

/-- **The twist of `𝐏(ℰ)` pulls back along the clause-(3)(c) morphism to the twist of `𝐏(𝓕)`**, for
an arbitrary surjection `ℰ ⟶ 𝓕`: the morphism of schemes is the induced closed immersion, along
which the twist pulls back to the twist by `Stacks.Chow.GenuineChern.bundleEmbeddingTwistIso`, and
the clause-(3)(a) identifications are carried along by the pseudofunctoriality of pullback. -/
theorem nonempty_pullback_twist_of_isQuotientBundleEmbedding {E F : (S.obj X).Modules}
    (q : E ⟶ F) [Epi q] {r s : ℕ} (B : BundleObject S X E r) (B' : BundleObject S X F s)
    (i : B'.bundle ⟶ B.bundle) (h : IsQuotientBundleEmbedding q B B' i) :
    Nonempty ((Scheme.Modules.pullback (S.map i)).obj B.twist ≅ B'.twist) := by
  have := B.isFiniteLocallyFree
  have := B'.isFiniteLocallyFree
  rw [B.twist_eq, B'.twist_eq]
  exact ⟨(Scheme.Modules.pullbackComp (S.map i) B.iso.hom).app _ ≪≫
    (Scheme.Modules.pullbackCongr h.map_eq).app _ ≪≫
    ((Scheme.Modules.pullbackComp B'.iso.hom
        (Stacks.Chow.GenuineChern.bundleEmbedding q)).app _).symm ≪≫
    (Scheme.Modules.pullback B'.iso.hom).mapIso
      (Stacks.Chow.GenuineChern.bundleEmbeddingTwistIso q)⟩

end BundleObject

/-- **The twist of a module of constant rank `n` by an invertible module has rank `n`**, at the
spelling `AlgebraicGeometry.Scheme.Modules.tensorObjRingedSpace` of the tensor product: an
invertible module has rank one (Stacks 0B8M) and ranks multiply. -/
theorem isFiniteLocallyFreeOfRank_tensorObjRingedSpace_of_isInvertible {X : Scheme.{u}}
    (E L : X.Modules) (n : ℕ)
    (hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E n)
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L) :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (Scheme.Modules.tensorObjRingedSpace X E L) n := by
  have h := Stacks.Chow.isFiniteLocallyFreeOfRank_tensor hE
    (Stacks.ProjectiveBundleSplitting.isFiniteLocallyFreeOfRank_one_of_isInvertible L hL)
  rw [mul_one] at h
  exact h

section Twist

variable {C : Type w} [Category.{v₁} C] {S : C ⥤ Scheme.{u}}

/-- **Condition (3) under an isomorphism of invertible modules**, `f^*c₁^A(ℒ) = c₁^A(ℒ')` for any
`ℒ'` isomorphic to `f^*ℒ`: `c₁^A` is a function on `Pic`, where isomorphic invertible modules have
the same class. This is `Stacks.WeilCohomology.ChernSituation.pull_c₁` read from the condition
alone, without the rest of `Stacks.WeilCohomology.ChernSituation`. -/
theorem PullbackFirstChernCondition.pull_c₁ {𝔄 : SourceChernSetup.{u, v, v₁, w} C S}
    (hpull : PullbackFirstChernCondition 𝔄) {X Y : C} (f : X ⟶ Y) (L : (S.obj Y).Modules)
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible (S.obj Y).presheaf
      (S.obj Y).ringCatSheaf.2 L) (L' : (S.obj X).Modules)
    (hL' : AlgebraicGeometry.SheafOfModules.IsInvertible (S.obj X).presheaf
      (S.obj X).ringCatSheaf.2 L')
    (e : (Scheme.Modules.pullback (S.map f)).obj L ≅ L') :
    𝔄.pull f (𝔄.c₁ Y (picardClassOf (S.obj Y) L hL)) =
      𝔄.c₁ X (picardClassOf (S.obj X) L' hL') := by
  rw [hpull f L hL,
    picardClassOf_eq_of_iso (S.obj X) _ L' (isInvertible_pullback_obj (S.map f) L hL) hL' e]

/-- **The comparison of `𝐏(ℰ)` with `𝐏(ℰ ⊗ ℒ)` inside `𝒞`.** There are an object `Q` of `𝒞`,
a morphism `q : Q ⟶ 𝐏(ℰ ⊗ ℒ)` of `𝒞` with `q^*` injective on `A`, and a morphism
`g : Q ⟶ 𝐏(ℰ)` of `𝒞` with `g ≫ p = q ≫ p'` and
`g^*c₁^A(𝒪_{𝐏(ℰ)}(1)) = q^*(c₁^A(𝒪_{𝐏(ℰ ⊗ ℒ)}(1)) - p'^*c₁^A(ℒ))`.

This is the source's "there is an isomorphism `g : P ⟶ P'` such that
`g^*𝒪_{P'}(1) = 𝒪_P(1) ⊗ p^*ℒ`, see Constructions, Lemma 27.20.1" together with its consequence
on first Chern classes, in the form in which it can be stated in `𝒞`: the isomorphism of Tag 02NC
is one of schemes, and `Q` with `q` and `g` is how the clauses of the source carry it into `𝒞`.
The construction is described in the module documentation. -/
theorem exists_bundleTensor_comparison (𝔄 : SourceChernSetup.{u, v, v₁, w} C S)
    (hpull : PullbackFirstChernCondition 𝔄) (hcompare : BundleCompareClause 𝔄)
    (hquot : QuotientBundleEmbeddingClause 𝔄) (X : C) (E L : (S.obj X).Modules) (r : ℕ)
    (hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E (r + 1))
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible (S.obj X).presheaf
      (S.obj X).ringCatSheaf.2 L)
    (hEL : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (Scheme.Modules.tensorObjRingedSpace (S.obj X) E L) (r + 1)) :
    ∃ (Y : C) (q : Y ⟶ (𝔄.bundleDatum X
        (Scheme.Modules.tensorObjRingedSpace (S.obj X) E L) r hEL).bundle)
      (g : Y ⟶ (𝔄.bundleDatum X E r hE).bundle),
      Function.Injective (𝔄.pull q) ∧
      g ≫ (𝔄.bundleDatum X E r hE).proj =
        q ≫ (𝔄.bundleDatum X (Scheme.Modules.tensorObjRingedSpace (S.obj X) E L) r hEL).proj ∧
      𝔄.pull g (𝔄.c₁ _ (𝔄.bundleDatum X E r hE).twistClass) =
        𝔄.pull q (𝔄.c₁ _ (𝔄.bundleDatum X
            (Scheme.Modules.tensorObjRingedSpace (S.obj X) E L) r hEL).twistClass -
          𝔄.pull (𝔄.bundleDatum X
            (Scheme.Modules.tensorObjRingedSpace (S.obj X) E L) r hEL).proj
            (𝔄.c₁ X (picardClassOf (S.obj X) L hL))) := by
  rw [𝔄.bundleDatum_eq X E r hE, 𝔄.bundleDatum_eq X _ r hEL]
  simp only [BundleObject.toBundleDatum_bundle, BundleObject.toBundleDatum_proj,
    BundleObject.toBundleDatum_twistClass]
  set BE := 𝔄.bundleObject X E r hE with hBE
  set B' := 𝔄.bundleObject X (Scheme.Modules.tensorObjRingedSpace (S.obj X) E L) r hEL with hB'
  have := AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree E
    (r + 1) (hM := hE)
  have : AlgebraicGeometry.SheafOfModules.IsInvertible (S.obj X).sheaf.obj
      (S.obj X).ringCatSheaf.property L := hL
  obtain ⟨g, hgiso, hgproj, ⟨τ⟩⟩ := Stacks.Chow.GenuineChern.exists_bundleTensorIso E L
  have := hgiso
  have hπ := B'.isBundle.iso_hom_comp_bundleProj
  -- `𝐏(ℰ ⊗ ℒ)`, read as a projective bundle of `ℰ` through Stacks 02NC
  let Bs : BundleObject S X E r :=
    { bundle := B'.bundle
      proj := B'.proj
      isBundle :=
        { rank := hE
          iso := B'.isBundle.iso ≪≫ @asIso _ _ _ _ g hgiso
          iso_hom_comp_bundleProj := by
            refine (Category.assoc _ _ _).trans ?_
            change B'.isBundle.iso.hom ≫ g ≫ Chow.bundleProj E = _
            exact (congrArg (B'.isBundle.iso.hom ≫ ·) hgproj).trans hπ } }
  have hBs : Bs.iso.hom = B'.iso.hom ≫ g := by
    unfold BundleObject.iso
    rfl
  have hτ : Nonempty (B'.twist ≅ Scheme.Modules.tensorObjRingedSpace (S.obj B'.bundle) Bs.twist
      ((Scheme.Modules.pullback (S.map B'.proj)).obj L)) := by
    rw [B'.twist_eq, Bs.twist_eq]
    exact ⟨(Scheme.Modules.pullback B'.iso.hom).mapIso τ ≪≫
      Stacks.Tag01VSPullbackTensor.schemePullbackTensorIso B'.iso.hom _ _ ≪≫
      Stacks.Tag01VSPullbackTensor.tensorSheafMapIso
        ((Scheme.Modules.pullbackComp B'.iso.hom g).app _ ≪≫
          (Scheme.Modules.pullbackCongr hBs.symm).app _)
        ((Scheme.Modules.pullbackComp B'.iso.hom _).app L ≪≫
          (Scheme.Modules.pullbackCongr B'.iso_hom_comp_bundleProj).app L)⟩
  have hLp := isInvertible_pullback_obj (S.map B'.proj) L hL
  have hc₁N : 𝔄.c₁ B'.bundle (picardClassOf _ Bs.twist Bs.twist_isInvertible) =
      𝔄.c₁ B'.bundle B'.twistClass - 𝔄.pull B'.proj (𝔄.c₁ X (picardClassOf (S.obj X) L hL)) := by
    obtain ⟨e⟩ := hτ
    have hcl : B'.twistClass = picardClassOf _ Bs.twist Bs.twist_isInvertible +
        picardClassOf _ ((Scheme.Modules.pullback (S.map B'.proj)).obj L) hLp := by
      rw [BundleObject.twistClass, picardClassOf_eq_of_iso _ _ _ _
        (isInvertible_tensorObjRingedSpace _ _ Bs.twist_isInvertible hLp) e]
      exact picardClassOf_tensorObjRingedSpace _ _ _ _ _
    rw [hpull B'.proj L hL, hcl, map_add]
    abel
  have hEP : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback (S.map B'.proj)).obj E) (r + 1) :=
    AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback _ E (r + 1)
  have hN1 : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} Bs.twist
      (0 + 1) :=
    Stacks.ProjectiveBundleSplitting.isFiniteLocallyFreeOfRank_one_of_isInvertible _
      Bs.twist_isInvertible
  have := Bs.epi_quot
  obtain ⟨h, hh⟩ := hcompare X B'.bundle B'.proj E r hE hEP
  obtain ⟨θh⟩ := BundleObject.nonempty_pullback_twist_of_isBundleCompare B'.proj BE
    (𝔄.bundleObject B'.bundle _ r hEP) (Iso.refl _) h hh
  obtain ⟨i, hi⟩ := hquot B'.bundle ((Scheme.Modules.pullback (S.map B'.proj)).obj E) Bs.twist
    Bs.quot Bs.epi_quot r 0 hEP hN1
  obtain ⟨θi⟩ :=
    BundleObject.nonempty_pullback_twist_of_isQuotientBundleEmbedding Bs.quot _ _ i hi
  -- `𝒪_Q(1) ≅ q^*𝒩`: the kernel of the tautological quotient of a module of rank one is zero
  have hYquot : IsIso (𝔄.bundleObject B'.bundle Bs.twist 0 hN1).quot := by
    have hsub : IsZero (𝔄.bundleObject B'.bundle Bs.twist 0 hN1).toBundleDatum.sub :=
      isZero_of_isFiniteLocallyFreeOfRank_zero _
        (𝔄.bundleObject B'.bundle Bs.twist 0 hN1).toBundleDatum.sub_rank
    have hincl : (𝔄.bundleObject B'.bundle Bs.twist 0 hN1).toBundleDatum.incl = 0 :=
      hsub.eq_zero_of_src _
    have hmono : Mono (𝔄.bundleObject B'.bundle Bs.twist 0 hN1).toBundleDatum.quot :=
      (ShortComplex.exact_iff_mono _ hincl).1
        (𝔄.bundleObject B'.bundle Bs.twist 0 hN1).toBundleDatum.shortExact.exact
    have hepi : Epi (𝔄.bundleObject B'.bundle Bs.twist 0 hN1).toBundleDatum.quot :=
      (𝔄.bundleObject B'.bundle Bs.twist 0 hN1).toBundleDatum.shortExact.epi_g
    exact isIso_of_mono_of_epi (𝔄.bundleObject B'.bundle Bs.twist 0 hN1).toBundleDatum.quot
  refine ⟨(𝔄.bundleObject B'.bundle Bs.twist 0 hN1).bundle,
    (𝔄.bundleObject B'.bundle Bs.twist 0 hN1).proj, i ≫ h, ?_, ?_, ?_⟩
  · have hinj := 𝔄.injective_pull_proj B'.bundle Bs.twist 0 hN1
    rw [𝔄.bundleDatum_eq] at hinj
    exact hinj
  · rw [Category.assoc, hh.comp_proj, ← Category.assoc]
    exact congrArg (· ≫ B'.proj) hi.comp_proj
  · refine Eq.trans ?_
      (congrArg (𝔄.pull (𝔄.bundleObject B'.bundle Bs.twist 0 hN1).proj) hc₁N)
    calc 𝔄.pull (i ≫ h) (𝔄.c₁ BE.bundle BE.twistClass)
        = 𝔄.pull i (𝔄.pull h (𝔄.c₁ BE.bundle BE.twistClass)) := by
          rw [𝔄.pull_comp]; rfl
      _ = 𝔄.pull i (𝔄.c₁ _ (𝔄.bundleObject B'.bundle _ r hEP).twistClass) :=
          congrArg (𝔄.pull i)
            (hpull.pull_c₁ h BE.twist BE.twist_isInvertible _
              (BundleObject.twist_isInvertible _) θh)
      _ = 𝔄.c₁ _ (𝔄.bundleObject B'.bundle Bs.twist 0 hN1).twistClass :=
          hpull.pull_c₁ i _ (BundleObject.twist_isInvertible _) _
            (BundleObject.twist_isInvertible _) θi
      _ = _ := (hpull.pull_c₁ (𝔄.bundleObject B'.bundle Bs.twist 0 hN1).proj Bs.twist
            Bs.twist_isInvertible _ (BundleObject.twist_isInvertible _)
            (asIso (𝔄.bundleObject B'.bundle Bs.twist 0 hN1).quot)).symm

/-- **The binomial formula from a comparison of projective bundles.** Let `ℰ` and `ℱ` have constant
rank `r + 1`, let `t ∈ A(X)` be central, and let `q : Q ⟶ 𝐏(ℱ)` and `g : Q ⟶ 𝐏(ℰ)` be morphisms
of `𝒞` with `q^*` injective, `g ≫ p = q ≫ p'` and
`g^*c₁^A(𝒪_{𝐏(ℰ)}(1)) = q^*(c₁^A(𝒪_{𝐏(ℱ)}(1)) - p'^*t)`. Then for `m ≤ r + 1`
`c^A_m(ℱ) = ∑_{j=0}^{m} binom(r + 1 - m + j, j) c^A_{m-j}(ℰ) t^j`.

Equation 45.12.1.1 for `ℰ`, pulled back along `g`, is `q^*` of that equation in `A(𝐏(ℱ))` with
the tautological class replaced by `c₁^A(𝒪_{𝐏(ℱ)}(1)) - p'^*t`; cancelling `q^*`, the formal
computation `Stacks.WeilCohomology.eq_of_alternating_relations` applies, with uniqueness from
condition (4) for `ℱ`. No isomorphism between the two projective bundles is needed. -/
theorem ChernSetup.chernClass_eq_of_comparison (𝔄 : ChernSetup.{u, v, v₁, w} C S) (X : C)
    (E F : (S.obj X).Modules) (r : ℕ)
    (hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E (r + 1))
    (hF : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} F (r + 1))
    (t : 𝔄.A X) (ht : ∀ a : 𝔄.A X, Commute t a) (Y : C)
    (q : Y ⟶ (𝔄.bundleDatum X F r hF).bundle) (g : Y ⟶ (𝔄.bundleDatum X E r hE).bundle)
    (hqinj : Function.Injective (𝔄.pull q))
    (hgq : g ≫ (𝔄.bundleDatum X E r hE).proj = q ≫ (𝔄.bundleDatum X F r hF).proj)
    (hgx : 𝔄.pull g (𝔄.c₁ _ (𝔄.bundleDatum X E r hE).twistClass) =
      𝔄.pull q (𝔄.c₁ _ (𝔄.bundleDatum X F r hF).twistClass -
        𝔄.pull (𝔄.bundleDatum X F r hF).proj t))
    (m : ℕ) (hm : m ≤ r + 1) :
    𝔄.chernClass X F r hF m =
      ∑ j ∈ Finset.range (m + 1),
        (r + 1 - m + j).choose j • (𝔄.chernClass X E r hE (m - j) * t ^ j) := by
  have hpq : ∀ c, 𝔄.pull q (𝔄.pull (𝔄.bundleDatum X F r hF).proj c) =
      𝔄.pull g (𝔄.pull (𝔄.bundleDatum X E r hE).proj c) := fun c => by
    rw [← RingHom.comp_apply, ← 𝔄.pull_comp, ← RingHom.comp_apply, ← 𝔄.pull_comp, hgq]
  have h0 := 𝔄.sum_chernClass_eq_zero X E r hE
  rw [← Finset.sum_range (fun k => ((-1 : ℤ) ^ k) •
    (𝔄.c₁ (𝔄.bundleDatum X E r hE).bundle (𝔄.bundleDatum X E r hE).twistClass ^ k *
      𝔄.pull (𝔄.bundleDatum X E r hE).proj (𝔄.chernClass X E r hE (r + 1 - k))))] at h0
  have hrelE : ∑ k ∈ Finset.range (r + 1 + 1), ((-1 : ℤ) ^ k) •
      ((𝔄.c₁ _ (𝔄.bundleDatum X F r hF).twistClass -
          𝔄.pull (𝔄.bundleDatum X F r hF).proj t) ^ k *
        𝔄.pull (𝔄.bundleDatum X F r hF).proj (𝔄.chernClass X E r hE (r + 1 - k))) = 0 := by
    apply hqinj
    rw [map_zero, map_sum, ← map_zero (𝔄.pull g), ← h0, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_zsmul, map_zsmul, map_mul, map_mul, map_pow, map_pow, hgx, hpq]
  have hrelF : ∑ k ∈ Finset.range (r + 1 + 1), ((-1 : ℤ) ^ k) •
      ((𝔄.c₁ _ (𝔄.bundleDatum X F r hF).twistClass - 𝔄.pull (𝔄.bundleDatum X F r hF).proj t +
          𝔄.pull (𝔄.bundleDatum X F r hF).proj t) ^ k *
        𝔄.pull (𝔄.bundleDatum X F r hF).proj (𝔄.chernClass X F r hF (r + 1 - k))) = 0 := by
    rw [sub_add_cancel, Finset.sum_range]
    exact 𝔄.sum_chernClass_eq_zero X F r hF
  have hinj : Function.Injective (fun c : Fin (r + 1) → 𝔄.A X =>
      ∑ i : Fin (r + 1),
        (𝔄.c₁ _ (𝔄.bundleDatum X F r hF).twistClass - 𝔄.pull (𝔄.bundleDatum X F r hF).proj t +
          𝔄.pull (𝔄.bundleDatum X F r hF).proj t) ^ (i : ℕ) *
        𝔄.pull (𝔄.bundleDatum X F r hF).proj (c i)) := by
    rw [sub_add_cancel]
    exact (𝔄.bijective_bundleFormula X F r hF).injective
  exact eq_of_alternating_relations (𝔄.pull (𝔄.bundleDatum X F r hF).proj)
    (𝔄.c₁ _ (𝔄.bundleDatum X F r hF).twistClass - 𝔄.pull (𝔄.bundleDatum X F r hF).proj t) t ht
    (Commute.sub_left (𝔄.c₁_central _ _ (𝔄.pull (𝔄.bundleDatum X F r hF).proj t))
      (Commute.refl _))
    (𝔄.chernClass X E r hE) (𝔄.chernClass X F r hF) (r + 1) (𝔄.chernClass_zero X E r hE)
    (𝔄.chernClass_zero X F r hF) hrelE hrelF hinj m hm

/-- **Stacks Project, Tag 0FI8.** In the standing situation of Section 45.12, let `ℰ` be a finite
locally free `𝒪_X`-module of constant rank `r + 1` and `ℒ` an invertible `𝒪_X`-module. Then for
every `i`
`c^A_i(ℰ ⊗ ℒ) = ∑_{j=0}^{i} binom(r + 1 - i + j, j) c^A_{i-j}(ℰ) ∪ c₁^A(ℒ)^j`,
the binomial coefficient written `(r + 1 + j - i).choose j` (see the module documentation).

The situation is `Stacks.WeilCohomology.SourceChernSetup` with the source's condition (3),
clause (3)(b) and clause (3)(c), each in the source's own form. The comparison of `𝐏(ℰ)` with
`𝐏(ℰ ⊗ ℒ)` and its effect on `c₁^A(𝒪(1))` are proved
(`Stacks.WeilCohomology.exists_bundleTensor_comparison`, from Tag 02NC), and so is the rank of
`ℰ ⊗ ℒ`. -/
@[stacks 0FI8 "for E of constant rank r + 1 and every i, the binomial coefficient \
  binom(r - i + j, j) written (r + 1 + j - i).choose j in N, which agrees with it wherever the \
  term c_{i-j}(E) is nonzero. The situation is SourceChernSetup with the source's condition (3), \
  clause (3)(b) and clause (3)(c) (QuotientBundleEmbeddingClause, the closure property for an \
  arbitrary surjection), each as the source states it. PROVED, not assumed: the comparison of \
  P(E) with P(E tensor L) inside the category and g^*c_1(O(1)) = c_1(O(1)) + p^*c_1(L) \
  (exists_bundleTensor_comparison, from Tag 02NC exists_bundleTensorIso, Tag 01CD and Tag 01CX), \
  and the rank of E tensor L. The rule c^A on K_0 and an arbitrary finite locally free E are \
  ChernSituation.totalChernClass_classOf_tensorObjRingedSpace and \
  ChernSituation.pull_totalChernClass_classOf_tensorObjRingedSpace"]
theorem chernClass_tensorObjRingedSpace (𝔄 : SourceChernSetup.{u, v, v₁, w} C S)
    (hpull : PullbackFirstChernCondition 𝔄) (hcompare : BundleCompareClause 𝔄)
    (hquot : QuotientBundleEmbeddingClause 𝔄) (X : C) (E L : (S.obj X).Modules) (r : ℕ)
    (hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E (r + 1))
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible (S.obj X).presheaf
      (S.obj X).ringCatSheaf.2 L) (i : ℕ) :
    𝔄.chernClass X (Scheme.Modules.tensorObjRingedSpace (S.obj X) E L) r
        (isFiniteLocallyFreeOfRank_tensorObjRingedSpace_of_isInvertible E L (r + 1) hE hL) i =
      ∑ j ∈ Finset.range (i + 1), (r + 1 + j - i).choose j •
        (𝔄.chernClass X E r hE (i - j) * 𝔄.c₁ X (picardClassOf (S.obj X) L hL) ^ j) := by
  rcases le_or_gt i (r + 1) with hi | hi
  · obtain ⟨Y, q, g, hqinj, hgq, hgx⟩ := exists_bundleTensor_comparison 𝔄 hpull hcompare hquot X
      E L r hE hL (isFiniteLocallyFreeOfRank_tensorObjRingedSpace_of_isInvertible E L (r + 1) hE hL)
    rw [𝔄.chernClass_eq_of_comparison X E _ r hE _ _ (fun a => 𝔄.c₁_central X _ a) Y q g hqinj
      hgq hgx i hi]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [show r + 1 - i + j = r + 1 + j - i by omega]
  · rw [𝔄.chernClass_of_gt X _ r _ hi]
    refine (Finset.sum_eq_zero fun j hj => ?_).symm
    have hj' : j ≤ i := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    rcases lt_or_ge (r + 1) (i - j) with h | h
    · rw [𝔄.chernClass_of_gt X E r hE h, zero_mul, smul_zero]
    · rw [Nat.choose_eq_zero_of_lt (by omega), zero_smul]

/-! ### Every constant rank, and an arbitrary finite locally free module

The total Chern class of Tag 0FI5 is defined for a module of arbitrary rank by patching over the
loci of constant rank (`Stacks.WeilCohomology.ChernSituation.chernSeriesOfModule`), and on `K₀`
by the universal property (`Stacks.WeilCohomology.ChernSituation.totalChernClass`). The formula
of Tag 0FI8 is read for that rule here: for every constant rank, `0` included, and for an
arbitrary finite locally free module on each object over `X` where its rank is constant. -/

namespace ChernSituation

variable (𝔖 : ChernSituation.{u, v, v₁, w} C S)

/-- **The formula of Tag 0FI8 for the total Chern class of a module of constant rank `m`**, `m = 0`
included. In positive rank it is `Stacks.WeilCohomology.chernClass_tensorObjRingedSpace`; in rank
zero both sides are `1` in degree zero and `0` above. -/
theorem chernSeries_coeff_tensorObjRingedSpace
    (hquot : QuotientBundleEmbeddingClause 𝔖.toSourceChernSetup) (X : C)
    (E L : (S.obj X).Modules) (m : ℕ)
    (hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E m)
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible (S.obj X).presheaf
      (S.obj X).ringCatSheaf.2 L) (i : ℕ) :
    (𝔖.chernSeries X (Scheme.Modules.tensorObjRingedSpace (S.obj X) E L) m
        (isFiniteLocallyFreeOfRank_tensorObjRingedSpace_of_isInvertible E L m hE hL)).coeff i =
      ∑ j ∈ Finset.range (i + 1), (m + j - i).choose j •
        ((𝔖.chernSeries X E m hE).coeff (i - j) *
          𝔖.c₁ X (picardClassOf (S.obj X) L hL) ^ j) := by
  cases m with
  | zero =>
    rw [𝔖.chernSeries_rank_zero, 𝔖.chernSeries_rank_zero, UnitalCentralSeries.coeff_one,
      Finset.sum_range_succ, Finset.sum_eq_zero fun j hj => ?_, zero_add]
    · rw [UnitalCentralSeries.coeff_one, Nat.sub_self, ite_eq_left rfl, one_mul,
        show 0 + i - i = 0 by omega]
      rcases i with _ | i
      · simp
      · simp
    · have hji : j < i := Finset.mem_range.mp hj
      rw [UnitalCentralSeries.coeff_one, ite_eq_right (by omega), zero_mul, smul_zero]
  | succ r =>
    rw [𝔖.chernSeries_coeff_succ, chernClass_tensorObjRingedSpace 𝔖.toSourceChernSetup
      (fun f L hL => 𝔖.pull_c₁_pullback f L hL) 𝔖.exists_bundleCompare_bundleObject hquot X E L
      r hE hL i]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [𝔖.chernSeries_coeff_succ]

/-- **The formula of Tag 0FI8 for the total Chern class of an arbitrary finite locally free
module, on each object over `X` where its rank is constant.** For `f : Z ⟶ X` in `𝒞` with `f^*ℰ`
of constant rank `m`, the formula holds after `f^*`.

`f^*` commutes with the total Chern class (property (2) of Tag 0FI5), `f^*(ℰ ⊗ ℒ) ≅ f^*ℰ ⊗ f^*ℒ`
(Tag 01CD) and the total Chern class is invariant under isomorphism, so this is the constant-rank
formula on `Z`. -/
theorem pull_coeff_chernSeriesOfModule_tensorObjRingedSpace
    (hquot : QuotientBundleEmbeddingClause 𝔖.toSourceChernSetup) (X : C)
    (E L : (S.obj X).Modules)
    (hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (R := (S.obj X).ringCatSheaf) E)
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible (S.obj X).presheaf
      (S.obj X).ringCatSheaf.2 L) (Z : C) (f : Z ⟶ X) (m : ℕ)
    (hm : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback (S.map f)).obj E) m) (i : ℕ) :
    𝔖.pull f
        ((𝔖.chernSeriesOfModule X (Scheme.Modules.tensorObjRingedSpace (S.obj X) E L)).coeff i) =
      ∑ j ∈ Finset.range (i + 1), (m + j - i).choose j •
        (𝔖.pull f ((𝔖.chernSeriesOfModule X E).coeff (i - j)) *
          𝔖.pull f (𝔖.c₁ X (picardClassOf (S.obj X) L hL)) ^ j) := by
  have hEL : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (R := (S.obj X).ringCatSheaf) (Scheme.Modules.tensorObjRingedSpace (S.obj X) E L) :=
    Stacks.Chow.isFiniteLocallyFree_tensor hE
      (AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree L 1
        (hM := Stacks.ProjectiveBundleSplitting.isFiniteLocallyFreeOfRank_one_of_isInvertible L hL))
  have hLZ := isInvertible_pullback_obj (S.map f) L hL
  have hmEL := isFiniteLocallyFreeOfRank_tensorObjRingedSpace_of_isInvertible
    ((Scheme.Modules.pullback (S.map f)).obj E) ((Scheme.Modules.pullback (S.map f)).obj L) m hm
    hLZ
  have e := pullbackTensorObjRingedSpaceIso (S.map f) E L
  have hm1 : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback (S.map f)).obj
        (Scheme.Modules.tensorObjRingedSpace (S.obj X) E L)) m :=
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso e.symm hmEL
  rw [𝔖.pull_coeff_chernSeriesOfModule X Z f _ hEL i,
    𝔖.chernSeriesOfModule_eq_chernSeries Z _ m hm1,
    𝔖.chernSeries_eq_of_iso Z _ _ m m hm1 hmEL e,
    𝔖.chernSeries_coeff_tensorObjRingedSpace hquot Z _ _ m hm hLZ i]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [𝔖.pull_coeff_chernSeriesOfModule X Z f E hE (i - j),
    𝔖.chernSeriesOfModule_eq_chernSeries Z _ m hm, 𝔖.pull_c₁_pullback f L hL]

/-- **Stacks Project, Tag 0FI8, for the rule `c^A` of Tag 0FI5.** In the standing situation, for
`ℰ` finite locally free of constant rank `r` (`r = 0` included) and `ℒ` invertible,
`c^A_i([ℰ ⊗ ℒ]) = ∑_{j=0}^{i} binom(r - i + j, j) c^A_{i-j}([ℰ]) ∪ c₁^A(ℒ)^j` for every `i`. -/
@[stacks 0FI8 "for the rule c^A of Tag 0FI5 (ChernSituation.totalChernClass on K_0(Vect(X))), \
  E of constant rank r, r = 0 included, and every i; binom(r - i + j, j) written \
  (r + j - i).choose j in N, which agrees with it wherever c_{i-j}(E) is nonzero. The situation \
  is ChernSituation, the source's clauses and conditions each in the source's form, with the \
  source's clause (3)(c) for an arbitrary surjection (QuotientBundleEmbeddingClause). The \
  comparison of P(E) with P(E tensor L) and the rank of E tensor L are proved; see \
  chernClass_tensorObjRingedSpace"]
theorem totalChernClass_classOf_tensorObjRingedSpace
    (hquot : QuotientBundleEmbeddingClause 𝔖.toSourceChernSetup) (X : C)
    (E L : (S.obj X).Modules) (r : ℕ)
    (hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r)
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible (S.obj X).presheaf
      (S.obj X).ringCatSheaf.2 L) (i : ℕ) :
    𝔖.totalChernClass X
        (VectorBundleKZero.classOf (S.obj X) (Scheme.Modules.tensorObjRingedSpace (S.obj X) E L))
        i =
      ∑ j ∈ Finset.range (i + 1), (r + j - i).choose j •
        (𝔖.totalChernClass X (VectorBundleKZero.classOf (S.obj X) E) (i - j) *
          𝔖.c₁ X (picardClassOf (S.obj X) L hL) ^ j) := by
  rw [𝔖.totalChernClass_classOf, 𝔖.chernSeriesOfModule_eq_chernSeries X _ r
      (isFiniteLocallyFreeOfRank_tensorObjRingedSpace_of_isInvertible E L r hE hL),
    𝔖.chernSeries_coeff_tensorObjRingedSpace hquot X E L r hE hL i]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [𝔖.totalChernClass_classOf, 𝔖.chernSeriesOfModule_eq_chernSeries X E r hE]

/-- **Stacks Project, Tag 0FI8, for the rule `c^A` of Tag 0FI5 and an arbitrary finite locally
free module.** In the standing situation, let `ℰ` be finite locally free, of possibly
non-constant rank, and `ℒ` invertible. On every object `f : Z ⟶ X` over `X` on which `ℰ` has
constant rank `r`,
`f^*c^A_i([ℰ ⊗ ℒ]) = ∑_{j=0}^{i} binom(r - i + j, j) f^*c^A_{i-j}([ℰ]) ∪ f^*c₁^A(ℒ)^j`.

The source's `r` is the rank of `ℰ`, and its proof begins "by the construction of `c^A_i` we may
assume `ℰ` has constant rank `r`": the formula is read on the loci of constant rank, and by
condition (2) these determine `A(X)` (`Stacks.WeilCohomology.ChernSituation.eq_of_pull_one`). -/
@[stacks 0FI8 "for the rule c^A of Tag 0FI5 and an ARBITRARY finite locally free E: the formula \
  holds after pullback along every morphism f : Z to X of the category along which E has \
  constant rank r, which by condition (2) (ChernSituation.eq_of_pull_one) determines \
  c^A_i(E tensor L); binom(r - i + j, j) written (r + j - i).choose j in N, which agrees with it \
  wherever c_{i-j}(f^*E) is nonzero. The situation is ChernSituation with the source's clause \
  (3)(c) for an arbitrary surjection (QuotientBundleEmbeddingClause). Proved, not assumed: the \
  comparison of P(E) with P(E tensor L), the rank of E tensor L, and f^*(E tensor L) = \
  f^*E tensor f^*L (Tag 01CD)"]
theorem pull_totalChernClass_classOf_tensorObjRingedSpace
    (hquot : QuotientBundleEmbeddingClause 𝔖.toSourceChernSetup) (X : C)
    (E L : (S.obj X).Modules)
    (hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (R := (S.obj X).ringCatSheaf) E)
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible (S.obj X).presheaf
      (S.obj X).ringCatSheaf.2 L) (Z : C) (f : Z ⟶ X) (r : ℕ)
    (hr : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback (S.map f)).obj E) r) (i : ℕ) :
    𝔖.pull f (𝔖.totalChernClass X
        (VectorBundleKZero.classOf (S.obj X) (Scheme.Modules.tensorObjRingedSpace (S.obj X) E L))
        i) =
      ∑ j ∈ Finset.range (i + 1), (r + j - i).choose j •
        (𝔖.pull f (𝔖.totalChernClass X (VectorBundleKZero.classOf (S.obj X) E) (i - j)) *
          𝔖.pull f (𝔖.c₁ X (picardClassOf (S.obj X) L hL)) ^ j) := by
  rw [𝔖.totalChernClass_classOf,
    𝔖.pull_coeff_chernSeriesOfModule_tensorObjRingedSpace hquot X E L hE hL Z f r hr i]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [𝔖.totalChernClass_classOf]

end ChernSituation

end Twist

end Stacks.WeilCohomology

end
