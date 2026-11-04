module

public import Mathlib.CategoryTheory.Sites.Equivalence
public import StacksCore.CategoryTheory.Abelian.SerreClass.Weak
public import StacksFrontier.AlgebraicGeometry.Stacks.FibreEssentialSmallness
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.HigherDirectImageFppfWeakSerre
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.HigherDirectImageSmoothLocalCriterion
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.LocallyQuasicoherentClosure
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.LocallyQuasicoherentSmoothDescent
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.Cech.RelativeSpectralSequence

/-!
# Rules in the sense of Stacks 076Z and 0770, for every topology, at the universe of the schemes

**Stacks 076Z** (étale topology) and **Stacks 0770** (fppf topology) are one criterion about a
*rule* `𝓜` assigning to every algebraic stack `𝒳` a subcategory `𝓜_𝒳` of the sheaves of
`𝒪_𝒳`-modules on `𝒳_τ`. This file sets up such rules for an arbitrary one of the five
topologies `τ` of Stacks 06TP, with the modules' sections in the universe `u` of the schemes,
states the first three clauses of the criterion, and verifies them for the rule of local
quasi-coherence (**Stacks 06WJ**) in the étale topology, which is the rule of **Stacks 075Z**.

## Main definitions

* `AlgebraicGeometry.Stack.StackModuleRule`: a rule, indexed by a category fibred in groupoids
  over `(Sch/S)_{fppf}` presented by its structure functor.
* `AlgebraicGeometry.Stack.StackModuleRule.IsWeakSerre`,
  `AlgebraicGeometry.Stack.StackModuleRule.IsStableUnderSmoothPullback` and
  `AlgebraicGeometry.Stack.StackModuleRule.IsSmoothLocal`: clauses (1), (2) and (3) of
  **Stacks 076Z** and **Stacks 0770**;
  `AlgebraicGeometry.Stack.StackModuleRule.IsSmoothLocalConverse` is the converse half of
  clause (3).
* `AlgebraicGeometry.Stack.StackModuleDirectImage`: a direct image for the modules on the
  `τ`-sites of algebraic stacks, and
  `AlgebraicGeometry.Stack.StackModuleDirectImage.higherDirectImage` its higher direct images.
* `AlgebraicGeometry.Stack.StackModuleRule.PreservedBy`,
  `AlgebraicGeometry.Stack.StackModuleRule.PreservesHigherDirectImagesOfAffine` and
  `AlgebraicGeometry.Stack.StackModuleRule.PreservesHigherDirectImages`: clause (4) and the
  conclusion of the criterion.
* `AlgebraicGeometry.Stack.locallyQuasicoherentModuleRule`: the rule of local quasi-coherence.

## Main results

* `AlgebraicGeometry.Stack.isWeakSerre_locallyQuasicoherentModuleRule`: clause (1) for local
  quasi-coherence, which is parts (1) to (3) of **Stacks 06WM**.
* `AlgebraicGeometry.Stack.isStableUnderSmoothPullback_locallyQuasicoherentModuleRule`: clause (2)
  for local quasi-coherence, which is **Stacks 06WL**.
* `AlgebraicGeometry.Stack.isSmoothLocal_locallyQuasicoherentModuleRule`: clause (3) for local
  quasi-coherence, which is **Stacks 06WL** together with **Stacks 075Y**.

## Implementation notes

### The universe of the sections

The modules have their sections in the universe `u` of the schemes, as the sheaves of sets on the
sites of the source do: the source does not distinguish sizes, and at that universe the closure
properties of quasi-coherent modules on small étale sites (Descent, Lemma 0GNB) are available.
Sheaves of modules at universe `u` on the associated site of a category fibred in groupoids form
an abelian category, since every slice of it is essentially small (**Stacks 06W0**); the
sheafification this needs is supplied by the instances
`AlgebraicGeometry.Stack.hasSheafify_stackModules` and
`AlgebraicGeometry.Stack.wEqualsLocallyBijective_stackModules`.

### Indexing and the direct image

A rule assigns to every algebraic stack `𝒳` a property of the objects of
`AlgebraicGeometry.Stack.StackModules`, the sheaves of modules over the structure sheaf
`Stacks.RelativeCech.moduleRingSheaf` of `𝒳` on its own structure functor; this is the structure
sheaf the relative Čech spectral sequences of **Stacks 072D** and **Stacks 072E** are stated with,
and on the terms of a Čech nerve (`AlgebraicGeometry.Stack.AlgebraicStacks.cechNerveTerm`) it is,
by definition, the one over the projection to the base. The inverse image along `g : 𝒵 ⟶ 𝒳` is
`Stacks.RelativeCech.moduleInverseImage` along the functor of `g`, related to the structure
functors by `CatFiberedInGroupoids.homFunctor_comp_p`.

The higher direct images are those of an arbitrary
`AlgebraicGeometry.Stack.StackModuleDirectImage`: a right adjoint of the inverse image for every
1-morphism, with enough injectives. A right adjoint is unique up to unique isomorphism, so the
clauses and the conclusion of the criterion do not depend on the choice; the statements of the
source are obtained by instantiating it.

Clause (1) is asked of algebraic stacks only, as in the source, and clause (3) of families
indexed in one fixed universe `s`.

## References

* [Stacks Project, Tag 076Z](https://stacks.math.columbia.edu/tag/076Z)
* [Stacks Project, Tag 0770](https://stacks.math.columbia.edu/tag/0770)
* [Stacks Project, Tag 06TP](https://stacks.math.columbia.edu/tag/06TP)
* [Stacks Project, Tag 06W0](https://stacks.math.columbia.edu/tag/06W0)
* [Stacks Project, Tag 06WJ](https://stacks.math.columbia.edu/tag/06WJ)
* [Stacks Project, Tag 06WL](https://stacks.math.columbia.edu/tag/06WL)
* [Stacks Project, Tag 06WM](https://stacks.math.columbia.edu/tag/06WM)
* [Stacks Project, Tag 075Y](https://stacks.math.columbia.edu/tag/075Y)
* [Stacks Project, Tag 02MO](https://stacks.math.columbia.edu/tag/02MO)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u v w t s

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section Sheafification

variable {𝒳 : Type v} [Category.{w} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)

include hp in
/-- Abelian presheaves on the site associated with a category fibred in groupoids and one of the
five topologies, with sections in the universe of the schemes, have a sheafification: every slice
is essentially small (**Stacks 06W0**). Unlike
`AlgebraicGeometry.FibredSite.hasWeakSheafify_associatedTopology`, no smallness of the category
itself is assumed, so this applies to every algebraic stack. -/
theorem hasSheafify_associatedTopology_siteKind (τ : SiteKind) :
    HasSheafify (BigFppfOver.associatedTopology B S hS p τ) AddCommGrpCat.{u} :=
  have : ∀ x : 𝒳, EssentiallySmall.{u} (Over x) := FibredSite.essentiallySmall_over B S hS p hp
  GrothendieckTopology.hasSheafify_addCommGrpCat_of_essentiallySmall_over _

end Sheafification

/-- The category `Mod(𝒳_τ, 𝒪_𝒳)` of sheaves of modules, with sections in the universe `u` of the
schemes, on the site associated with the topology `τ` of an algebraic stack `𝒳`, over its own
structure functor. -/
abbrev StackModules (τ : SiteKind) (𝒳 : AlgebraicStacks.{u, t} B S hS) :=
  SheafOfModules.{u} (Stacks.RelativeCech.moduleRingSheaf B S hS 𝒳.val.val.p
    𝒳.val.isFiberedInGroupoids τ)

/-- `Mod(𝒳_τ, 𝒪_𝒳)` has a sheafification at the universe of the schemes. -/
instance hasSheafify_stackModules (τ : SiteKind) (𝒳 : AlgebraicStacks.{u, t} B S hS) :
    HasSheafify (BigFppfOver.associatedTopology B S hS 𝒳.val.val.p τ) AddCommGrpCat.{u} :=
  hasSheafify_associatedTopology_siteKind B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids τ

/-- The weak equivalences of that sheafification are the locally bijective maps: this is
`AlgebraicGeometry.FibredSite.wEqualsLocallyBijective_associatedTopology`, the site of an algebraic
stack being essentially small (`AlgebraicGeometry.Stack.essentiallySmall_obj_algebraicStack`). -/
instance wEqualsLocallyBijective_stackModules (τ : SiteKind)
    (𝒳 : AlgebraicStacks.{u, t} B S hS) :
    (BigFppfOver.associatedTopology B S hS 𝒳.val.val.p τ).WEqualsLocallyBijective
      AddCommGrpCat.{u} :=
  FibredSite.wEqualsLocallyBijective_associatedTopology B S hS 𝒳.val.val.p τ

/-- **A rule in the sense of Stacks 076Z and Stacks 0770**, for the topology `τ`: to every
algebraic stack `𝒳` over `S` a property of the objects of `Mod(𝒳_τ, 𝒪_𝒳)`. -/
abbrev StackModuleRule (τ : SiteKind) :=
  ∀ 𝒳 : AlgebraicStacks.{u, t} B S hS, ObjectProperty (StackModules B S hS τ 𝒳)

/-- The inverse image `g⁻¹ : Mod(𝒳_τ, 𝒪_𝒳) ⥤ Mod(𝒵_τ, 𝒪_𝒵)` along a 1-morphism `g : 𝒵 ⟶ 𝒳` of
algebraic stacks, over the structure functors of the two stacks. -/
noncomputable abbrev stackModuleInverseImage (τ : SiteKind) {𝒵 𝒳 : AlgebraicStacks.{u, t} B S hS}
    (g : 𝒵 ⟶ 𝒳) : StackModules B S hS τ 𝒳 ⥤ StackModules B S hS τ 𝒵 :=
  Stacks.RelativeCech.moduleInverseImage.{u, u + 1, u + 1, u, u, u} B S hS 𝒵.val.val.p
    𝒳.val.val.p 𝒵.val.isFiberedInGroupoids 𝒳.val.isFiberedInGroupoids
    (CatFiberedInGroupoids.homFunctor g.hom) (CatFiberedInGroupoids.homFunctor_comp_p g.hom) τ

/-- The inverse image is additive. -/
instance additive_stackModuleInverseImage (τ : SiteKind) {𝒵 𝒳 : AlgebraicStacks.{u, t} B S hS}
    (g : 𝒵 ⟶ 𝒳) : (stackModuleInverseImage B S hS τ g).Additive :=
  Stacks.RelativeCech.moduleInverseImage_additive _ _ _ _ _ _ _ _ _ _

/-- **A direct image for the modules on the `τ`-sites of algebraic stacks**: for every 1-morphism
`f : 𝒳 ⟶ 𝒴` a right adjoint `f_*` of the inverse image, together with enough injectives in every
`Mod(𝒳_τ, 𝒪_𝒳)`. The direct image of **Stacks 06WE** at the universe of the schemes is one. -/
structure StackModuleDirectImage (τ : SiteKind) where
  /-- The direct image `f_*`. -/
  pushforward {𝒳 𝒴 : AlgebraicStacks.{u, t} B S hS} (f : 𝒳 ⟶ 𝒴) :
    StackModules B S hS τ 𝒳 ⥤ StackModules B S hS τ 𝒴
  /-- The inverse image is left adjoint to the direct image. -/
  adjunction {𝒳 𝒴 : AlgebraicStacks.{u, t} B S hS} (f : 𝒳 ⟶ 𝒴) :
    stackModuleInverseImage B S hS τ f ⊣ pushforward f
  /-- Every `Mod(𝒳_τ, 𝒪_𝒳)` has enough injectives. -/
  enoughInjectives (𝒳 : AlgebraicStacks.{u, t} B S hS) : EnoughInjectives (StackModules B S hS τ 𝒳)

namespace StackModuleDirectImage

variable {B S hS} {τ : SiteKind} (D : StackModuleDirectImage.{u, t} B S hS τ)

/-- The direct image is additive, being a right adjoint with an additive left adjoint. -/
instance additive_pushforward {𝒳 𝒴 : AlgebraicStacks.{u, t} B S hS} (f : 𝒳 ⟶ 𝒴) :
    (D.pushforward f).Additive :=
  (D.adjunction f).right_adjoint_additive

/-- **The higher direct image `Rⁱf_*`**: the `i`-th right derived functor of the direct image. -/
noncomputable def higherDirectImage {𝒳 𝒴 : AlgebraicStacks.{u, t} B S hS} (f : 𝒳 ⟶ 𝒴)
    (i : ℕ) : StackModules B S hS τ 𝒳 ⥤ StackModules B S hS τ 𝒴 :=
  letI := D.enoughInjectives 𝒳
  (D.pushforward f).rightDerived i

end StackModuleDirectImage

namespace StackModuleRule

variable {B S hS}

/-- **Clause (1) of Stacks 076Z and Stacks 0770.** At every algebraic stack the rule cuts out a
weak Serre subcategory (**Stacks 02MO**, in the closure form of **Stacks 0754**) of
`Mod(𝒳_τ, 𝒪_𝒳)`. -/
abbrev IsWeakSerre (τ : SiteKind) (M : StackModuleRule.{u, t} B S hS τ) : Prop :=
  ∀ 𝒳 : AlgebraicStacks.{u, t} B S hS, (M 𝒳).IsWeakSerreClass

/-- **Clause (2) of Stacks 076Z and Stacks 0770.** The inverse image of a member of the rule along
a smooth 1-morphism of algebraic stacks is a member. -/
abbrev IsStableUnderSmoothPullback (τ : SiteKind) (M : StackModuleRule.{u, t} B S hS τ) : Prop :=
  ∀ {𝒵 𝒳 : AlgebraicStacks.{u, t} B S hS} (g : 𝒵 ⟶ 𝒳), AlgebraicStacks.IsSmooth B S hS g →
    ∀ F, M 𝒳 F → M 𝒵 ((stackModuleInverseImage B S hS τ g).obj F)

/-- **The converse half of clause (3) of Stacks 076Z and Stacks 0770.** Let `f j : 𝒲 j ⟶ 𝒳` be a
family of smooth 1-morphisms of algebraic stacks with `|𝒳| = ⋃ j, |f j|(|𝒲 j|)`. A module on
`𝒳_τ` whose inverse images along the family are members of the rule is a member. -/
abbrev IsSmoothLocalConverse (τ : SiteKind) (M : StackModuleRule.{u, t} B S hS τ) : Prop :=
  ∀ {J : Type s} {𝒲 : J → AlgebraicStacks.{u, t} B S hS} {𝒳 : AlgebraicStacks.{u, t} B S hS}
      (f : ∀ j, 𝒲 j ⟶ 𝒳), (∀ j, AlgebraicStacks.IsSmooth B S hS (f j)) →
      (Set.univ : Set (AlgebraicStacks.points B S hS 𝒳)) =
        ⋃ j, Set.range (AlgebraicStacks.pointsMap B S hS (f j)) →
      ∀ F, (∀ j, M (𝒲 j) ((stackModuleInverseImage B S hS τ (f j)).obj F)) → M 𝒳 F

/-- **Clause (3) of Stacks 076Z and Stacks 0770.** For a family of smooth 1-morphisms
`f j : 𝒲 j ⟶ 𝒳` of algebraic stacks with `|𝒳| = ⋃ j, |f j|(|𝒲 j|)`, a module on `𝒳_τ` is a member
of the rule if and only if all its inverse images along the family are. -/
abbrev IsSmoothLocal (τ : SiteKind) (M : StackModuleRule.{u, t} B S hS τ) : Prop :=
  ∀ {J : Type s} {𝒲 : J → AlgebraicStacks.{u, t} B S hS} {𝒳 : AlgebraicStacks.{u, t} B S hS}
      (f : ∀ j, 𝒲 j ⟶ 𝒳), (∀ j, AlgebraicStacks.IsSmooth B S hS (f j)) →
      (Set.univ : Set (AlgebraicStacks.points B S hS 𝒳)) =
        ⋃ j, Set.range (AlgebraicStacks.pointsMap B S hS (f j)) →
      ∀ F, M 𝒳 F ↔ ∀ j, M (𝒲 j) ((stackModuleInverseImage B S hS τ (f j)).obj F)

/-- Clause (3) is clause (2) for the members of the family together with its converse half. -/
theorem isSmoothLocal_of_isSmoothLocalConverse {τ : SiteKind} {M : StackModuleRule.{u, t} B S hS τ}
    (h2 : IsStableUnderSmoothPullback τ M) (h3 : IsSmoothLocalConverse.{u, t, s} τ M) :
    IsSmoothLocal.{u, t, s} τ M :=
  fun f hsmooth hjs F => ⟨fun hF j => h2 (f j) (hsmooth j) F hF, h3 f hsmooth hjs F⟩

variable {τ : SiteKind} (D : StackModuleDirectImage.{u, t} B S hS τ)

/-- **The conclusion of Stacks 076Z and Stacks 0770 at one 1-morphism and one degree**: the higher
direct image `Rⁱf_*` carries members of the rule to members of the rule. -/
abbrev PreservedBy (M : StackModuleRule.{u, t} B S hS τ) {𝒳 𝒴 : AlgebraicStacks.{u, t} B S hS}
    (f : 𝒳 ⟶ 𝒴) (i : ℕ) : Prop :=
  ∀ F, M 𝒳 F → M 𝒴 ((D.higherDirectImage f i).obj F)

/-- **Clause (4) of Stacks 076Z and Stacks 0770.** For a 1-morphism between algebraic stacks
representable by affine schemes (`AlgebraicGeometry.Stack.AlgebraicStacks.IsAffineRepresentable`:
equivalent over the site to the category represented by an object with affine underlying scheme)
the higher direct images carry the rule into the rule, in every degree. -/
abbrev PreservesHigherDirectImagesOfAffine (M : StackModuleRule.{u, t} B S hS τ) : Prop :=
  ∀ {𝒳 𝒴 : AlgebraicStacks.{u, t} B S hS} (f : 𝒳 ⟶ 𝒴),
    AlgebraicStacks.IsAffineRepresentable B S hS 𝒳 →
      AlgebraicStacks.IsAffineRepresentable B S hS 𝒴 → ∀ i : ℕ, PreservedBy D M f i

/-- **The conclusion of Stacks 076Z and Stacks 0770.** For every quasi-compact quasi-separated
1-morphism of algebraic stacks the higher direct images carry the rule into the rule, in every
degree. -/
abbrev PreservesHigherDirectImages (M : StackModuleRule.{u, t} B S hS τ) : Prop :=
  ∀ {𝒳 𝒴 : AlgebraicStacks.{u, t} B S hS} (f : 𝒳 ⟶ 𝒴), IsQuasiCompactMorphism B S hS f →
    AlgebraicStacks.IsQuasiSeparated B S hS f → ∀ i : ℕ, PreservedBy D M f i

end StackModuleRule

variable (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)

/-- **The rule of local quasi-coherence** (**Stacks 06WJ**), in the étale topology: the rule of
**Stacks 075Z**. -/
noncomputable abbrev locallyQuasicoherentModuleRule : StackModuleRule.{u, t} B S hS .etale :=
  fun 𝒳 F => IsLocallyQuasicoherent B E h S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids F.val

/-- **Clause (1) of Stacks 076Z for local quasi-coherence**: at every algebraic stack the locally
quasi-coherent modules form a weak Serre subcategory of `Mod(𝒳_étale, 𝒪_𝒳)`. This is parts (1)
to (3) of **Stacks 06WM**: they are closed under isomorphisms, kernels and cokernels, contain a
zero object, and an extension of two of them is one. -/
theorem isWeakSerre_locallyQuasicoherentModuleRule :
    StackModuleRule.IsWeakSerre .etale (locallyQuasicoherentModuleRule.{u, t} B S hS E h) := by
  intro 𝒳
  let P : ObjectProperty (StackModules B S hS .etale 𝒳) :=
    locallyQuasicoherentModuleRule B S hS E h 𝒳
  change P.IsWeakSerreClass
  have : P.IsClosedUnderKernels :=
    isClosedUnderKernels_isLocallyQuasicoherent B E h S hS _ _
  have : P.IsClosedUnderCokernels :=
    isClosedUnderCokernels_isLocallyQuasicoherent B E h S hS _ _
  have : P.ContainsZero := containsZero_isLocallyQuasicoherent B E h S hS _ _
  have : P.IsClosedUnderIsomorphisms :=
    isClosedUnderIsomorphisms_isLocallyQuasicoherent B E h S hS _ _
  have : P.IsClosedUnderExtensions :=
    ⟨fun hT h₁ h₃ => (isLocallyQuasicoherent_twoOutOfThree B E h S hS _ _ _ hT).2.2 h₁ h₃⟩
  exact ObjectProperty.IsWeakSerreClass.mk

/-- Local quasi-coherence of the inverse image of a sheaf of modules along a 1-morphism of
categories fibred in groupoids, presented over an arbitrary functor `p` equal to `F ⋙ q`, is local
quasi-coherence of the inverse image of presheaves of modules of **Stacks 06WL**, over the strict
presentation `F ⋙ q`. -/
theorem isLocallyQuasicoherent_moduleInverseImage_iff {𝒵 𝒳 : Type (u + 1)} [Category.{u} 𝒵]
    [Category.{u} 𝒳] (p : 𝒵 ⥤ BigFppfOver B S hS) (q : 𝒳 ⥤ BigFppfOver B S hS)
    (hp : p.IsFiberedInGroupoids) (hq : q.IsFiberedInGroupoids) (F : 𝒵 ⥤ 𝒳) (hF : F ⋙ q = p)
    (hFq : (F ⋙ q).IsFiberedInGroupoids)
    (G : SheafOfModules.{u} (Stacks.RelativeCech.moduleRingSheaf B S hS q hq .etale)) :
    IsLocallyQuasicoherent B E h S hS p hp
        ((Stacks.RelativeCech.moduleInverseImage.{u, u + 1, u + 1, u, u, u} B S hS p q hp hq F hF
          .etale).obj G).val ↔
      IsLocallyQuasicoherent B E h S hS (F ⋙ q) hFq
        ((modulePresheafPullback.{u, u + 1, u, u + 1, u, u} B S hS q hq F hFq).obj G.val) := by
  subst hF
  have e : ((Stacks.RelativeCech.moduleInverseImage.{u, u + 1, u + 1, u, u, u} B S hS (F ⋙ q) q
      hp hq F rfl .etale).obj G).val =
        (modulePresheafPullback.{u, u + 1, u, u + 1, u, u} B S hS q hq F hFq).obj G.val := by
    unfold Stacks.RelativeCech.moduleInverseImage
    congr 1
  rw [e]

/-- Local quasi-coherence of an inverse image of modules along a 1-morphism of algebraic stacks is
local quasi-coherence of the corresponding inverse image of presheaves of modules. -/
private theorem isLocallyQuasicoherent_stackModuleInverseImage_iff
    {𝒵 𝒳 : AlgebraicStacks.{u, t} B S hS} (g : 𝒵 ⟶ 𝒳) (F : StackModules B S hS .etale 𝒳) :
    locallyQuasicoherentModuleRule B S hS E h 𝒵
        ((stackModuleInverseImage B S hS .etale g).obj F) ↔
      IsLocallyQuasicoherent B E h S hS _ (isFiberedInGroupoids_homFunctor_comp B S hS g.hom)
        ((stackModulePresheafPullback B S hS g).obj F.val) :=
  isLocallyQuasicoherent_moduleInverseImage_iff B S hS E h _ _ _ _ _ _ _ F

/-- **Clause (2) of Stacks 076Z for local quasi-coherence**, which is **Stacks 06WL**: the inverse
image of a locally quasi-coherent module along a 1-morphism of algebraic stacks is locally
quasi-coherent. No smoothness is needed. -/
theorem isStableUnderSmoothPullback_locallyQuasicoherentModuleRule :
    StackModuleRule.IsStableUnderSmoothPullback .etale
      (locallyQuasicoherentModuleRule.{u, t} B S hS E h) := fun g _ F hF =>
  (isLocallyQuasicoherent_stackModuleInverseImage_iff B S hS E h g F).2
    (isLocallyQuasicoherent_stackModulePresheafPullback B E h S hS g F.val hF)

/-- **The converse half of clause (3) of Stacks 076Z for local quasi-coherence**, which is
**Stacks 075Y**. -/
theorem isSmoothLocalConverse_locallyQuasicoherentModuleRule :
    StackModuleRule.IsSmoothLocalConverse.{u, t, s} .etale
      (locallyQuasicoherentModuleRule.{u, t} B S hS E h) := fun f hsmooth hjs F hF =>
  isLocallyQuasicoherent_of_isSmooth_jointlySurjective B E h S hS f hsmooth hjs F.val
    F.isSheaf fun j => (isLocallyQuasicoherent_stackModuleInverseImage_iff B S hS E h (f j) F).1
      (hF j)

/-- **Clause (3) of Stacks 076Z for local quasi-coherence**: **Stacks 06WL** and
**Stacks 075Y**. -/
theorem isSmoothLocal_locallyQuasicoherentModuleRule :
    StackModuleRule.IsSmoothLocal.{u, t, s} .etale
      (locallyQuasicoherentModuleRule.{u, t} B S hS E h) :=
  StackModuleRule.isSmoothLocal_of_isSmoothLocalConverse
    (isStableUnderSmoothPullback_locallyQuasicoherentModuleRule B S hS E h)
    (isSmoothLocalConverse_locallyQuasicoherentModuleRule B S hS E h)

end AlgebraicGeometry.Stack

end
