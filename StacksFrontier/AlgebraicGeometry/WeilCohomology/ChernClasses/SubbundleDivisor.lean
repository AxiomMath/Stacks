module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ConstantSheafHom
public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.SubbundleZeroScheme
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.ChernClasses.SourceChernSetup
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.ChernClasses.SplittingPrinciple
public import StacksFrontier.AlgebraicGeometry.PicardGroup.Pullback
import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.SubbundleGeometry

/-!
# `𝒪_P(𝐏(𝓕))`, the invertible module of the divisor `𝐏(𝓕) ⊂ 𝐏(ℰ)`

Condition (5) of the standing situation of Stacks Section 45.12 (Tag 0FI4) is read at the class
`c₁^A(𝒪_P(𝐏(𝓕)))`, where `𝐏(𝓕) ⊂ 𝐏(ℰ)` is the effective Cartier divisor the clause-(3)(c) closed
immersion exhibits. The proof of Tag 0FI5 uses it at `c₁^A(𝒪_P(1)) - p^*c₁^A(ℒ)`, and the source
gets from one to the other by **deriving** `𝒪_P(𝐏(𝓕)) ≅ 𝒪_P(1) ⊗ (p^*ℒ)^{⊗ -1}` from the
description of `𝐏(𝓕)` as the zero scheme of a regular section. This file is that derivation.

## Main definitions

* `Stacks.WeilCohomology.IsSubbundleDivisorModule`: **`ℒ' = 𝒪_P(𝐏(𝓕))`** — an invertible module on
  `𝐏(ℰ)` carrying a section whose zero scheme is a relative effective Cartier divisor over the
  base, identified with `𝐏(𝓕)` over `𝐏(ℰ)`. This says nothing about `𝒪_P(1)`.

## Main results

* `Stacks.WeilCohomology.exists_isSubbundleDivisorModule`: such an `ℒ'` exists, **and**
  `p^*ℒ ⊗ ℒ' ≅ 𝒪_P(1)`.
* `Stacks.WeilCohomology.BundleObject.twistClass_eq_picardClassOf_add`: **the derived
  identification, in `Pic`**: `c₁^A`'s argument `𝒪_P(1) - p^*ℒ` is the class of `ℒ'`, in the
  additive form `[p^*ℒ] + [ℒ'] = [𝒪_P(1)]`.

## Where this comes from, and what is not re-proved here

Both results are read off `Stacks.Chow.GenuineChern.SubbundleHolds`, the predicate that already
packages exactly this geometry — the pullback of the twist along the embedding, and the divisor
datum with its tensor identification — and which
`Stacks.Chow.GenuineChern.subbundleHolds` proves, from
`Stacks.Chow.GenuineChern.exists_relativeEffectiveCartierDivisor_bundleEmbedding`. Nothing about
the divisor is proved again here. `IsSubbundleDivisorModule` is the per-module form of the second
conjunct of that predicate, which is the form condition (5) has to be quantified over: condition
(5) is a statement about `A`, so it must be stated *for* the divisor module rather than
alongside an existential producing it.

`Stacks.Chow.GenuineChern.SubbundleHolds` cannot be named in
`StacksFrontier.AlgebraicGeometry.WeilCohomology.ChernClasses.BundleObject`, where the rest of the
clause-(3)(a)–(3)(c) derivations live: its file imports
`StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.ModuleFacts`, which imports
`StacksFrontier.AlgebraicGeometry.WeilCohomology.ChernClasses.Situation`. That is why this file sits
downstream of `Situation` instead.

The arithmetic is `Stacks.SheafOfModules.pullbackPicardClass_schemeTensor` with
`Stacks.SheafOfModules.pullbackPicardClass_eq_picardClass`. The group structure on `Pic` needs
the sheafification instances for `AddCommGrpCat` on the site of opens, which is why
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ConstantSheafHom` — where the existing global
instance `Stacks.SheafOfModules.hasWeakSheafify_addCommGrp_of_univLE` lives — is imported rather
than a local instance declared. The identification is produced on the
constructed `Stacks.Chow.bundle`, and only the *module* is pulled back along the clause-(3)(a)
identification `S(b) ≅ 𝐏(ℰ)` — no divisor is transported. It is proved in the **additive** form
because `Stacks.SheafOfModules.pullbackPicardClass` is not packaged as a group homomorphism.

## Three things that cost time here

* `Stacks.WeilCohomology.BundleObject.twist` is sealed (`irreducible`) once
  `Stacks.WeilCohomology.BundleObject.toBundleDatum` is assembled, so an isomorphism whose target
  is `B.twist` is **not** accepted by definitional unfolding from one whose target is
  `e^*𝒪_{𝐏(ℰ)}(1)`. Compose with `eqToIso B.twist_eq.symm`.
* `rw [twistClass, twist_eq]` fails: `Stacks.WeilCohomology.picardClassOf` takes the invertibility
  proof as an argument, so rewriting the module moves that argument's type and the motive is not
  type correct. Give the term instead —
  `Stacks.WeilCohomology.picardClassOf_eq_of_iso` with both modules and both invertibility proofs
  written out.
* `AlgebraicGeometry.Scheme.Modules.tensorObj = Stacks.SheafOfModules.schemeTensor`,
  `Stacks.WeilCohomology.picardClassOf = Stacks.SheafOfModules.picardClass` and
  `AlgebraicGeometry.Scheme.Modules.pullback = RingedSpaceModuleAdjunction.modulePullback` all hold
  by `rfl`. That is what lets the Picard arithmetic below run with no bridging lemmas, and it is
  worth checking before writing one.

## References

* [Stacks Project, Tag 0FI4](https://stacks.math.columbia.edu/tag/0FI4)
* [Stacks Project, Tag 0FI5](https://stacks.math.columbia.edu/tag/0FI5)
* [Stacks Project, Tag 01CX](https://stacks.math.columbia.edu/tag/01CX)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u v₁ w

namespace Stacks.WeilCohomology

/-! ### `𝒪_P(𝐏(𝓕))` -/

/-- **`ℒ' = 𝒪_P(𝐏(𝓕))`.** For `0 ⟶ ℒ ⟶ ℰ ⟶ 𝓕 ⟶ 0` short exact with `ℰ`, `𝓕` finite locally free,
an invertible `ℒ'` on `𝐏(ℰ)` is the module of the divisor `𝐏(𝓕) ⊂ 𝐏(ℰ)` when it carries a
section whose zero scheme is a relative effective Cartier divisor over the base and is identified
with `𝐏(𝓕)` over `𝐏(ℰ)`, through the induced closed immersion.

This is **purely divisor-theoretic**: `𝒪_P(1)` does not occur in it. That is the point —
condition (5) of the source is read at `c₁^A` of this module, and the identification with
`𝒪_P(1) ⊗ (p^*ℒ)^{⊗ -1}` is a *theorem*,
`Stacks.WeilCohomology.BundleObject.twistClass_eq_picardClassOf_add`. -/
def IsSubbundleDivisorModule {X : Scheme.{u}} (T : ShortComplex X.Modules) (hT : T.ShortExact)
    (hE2 : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} T.X₂)
    (hE3 : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} T.X₃)
    (L : (@Stacks.Chow.bundle X T.X₂ hE2).Modules)
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible
      (@Stacks.Chow.bundle X T.X₂ hE2).presheaf
      (@Stacks.Chow.bundle X T.X₂ hE2).ringCatSheaf.2 L) : Prop :=
  ∃ s : L.sections,
    Stacks.Divisors.IsRelativeEffectiveCartierDivisor (@Stacks.Chow.bundleProj X T.X₂ hE2)
        (@Stacks.Divisors.zeroScheme _ L hL (s.eval (.op ⊤))) ∧
      ∃ e : (@Stacks.Divisors.zeroScheme _ L hL (s.eval (.op ⊤))).subscheme ≅
          @Stacks.Chow.bundle X T.X₃ hE3,
        e.hom ≫ @Stacks.Chow.GenuineChern.bundleEmbedding X T.X₂ T.X₃ hE2 hE3 T.g hT.epi_g =
          (@Stacks.Divisors.zeroScheme _ L hL (s.eval (.op ⊤))).subschemeι

/-- **The divisor module exists, and `p^*ℒ ⊗ 𝒪_P(𝐏(𝓕)) ≅ 𝒪_P(1)`.**

Both halves are `Stacks.Chow.GenuineChern.subbundleHolds`, which proves
`Stacks.Chow.GenuineChern.SubbundleHolds` from
`Stacks.Chow.GenuineChern.exists_relativeEffectiveCartierDivisor_bundleEmbedding`: the divisor is
the zero scheme of the section of `ℒ' = 𝒪(1) ⊗ (p^*ℒ)^{⊗ -1}` attached to
`p^*ℒ ⟶ p^*ℰ ⟶ 𝒪(1)`, and the tensor identification is the last conjunct of that predicate.
Nothing is re-proved; this only reshapes it so that the divisor module can be quantified over. -/
theorem exists_isSubbundleDivisorModule {X : Scheme.{u}} (T : ShortComplex X.Modules)
    (hT : T.ShortExact)
    (hX1 : AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 T.X₁)
    (r : ℕ)
    (hF : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} T.X₃ (r + 1))
    (hE2 : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} T.X₂)
    (hE3 : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} T.X₃) :
    ∃ (L : (@Stacks.Chow.bundle X T.X₂ hE2).Modules)
      (hL : AlgebraicGeometry.SheafOfModules.IsInvertible
        (@Stacks.Chow.bundle X T.X₂ hE2).presheaf
        (@Stacks.Chow.bundle X T.X₂ hE2).ringCatSheaf.2 L),
      IsSubbundleDivisorModule T hT hE2 hE3 L hL ∧
        Nonempty (Scheme.Modules.tensorObj
          ((Scheme.Modules.pullback (@Stacks.Chow.bundleProj X T.X₂ hE2)).obj T.X₁) L ≅
            @Stacks.Chow.bundleTwist X T.X₂ hE2) := by
  have : AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj
      X.ringCatSheaf.property T.X₁ := hX1
  have := hE2
  have := hE3
  have := hF
  obtain ⟨-, L, hL, s, hD, e, he, hTen⟩ := Stacks.Chow.GenuineChern.subbundleHolds T hT r
  exact ⟨L, hL, ⟨s, hD, e, he⟩, hTen⟩

/-! ### The derived identification in `Pic` -/

namespace BundleObject

variable {C : Type w} [Category.{v₁} C] {S : C ⥤ Scheme.{u}} {X : C}
  {E : (S.obj X).Modules} {r : ℕ}

/-- **`[p^*ℒ] + [𝒪_P(𝐏(𝓕))] = [𝒪_P(1)]` in `Pic` of the object of `𝒞`.**

This is the identification the source derives from `𝐏(𝓕)` being the zero scheme of a regular
section, in the form condition (5) is consumed in: it says that the class
`𝒪_P(1) - p^*ℒ`, at which the Whitney computation reads `c₁^A`, is the class of the divisor
module. The hypothesis `eT` is `p^*ℒ ⊗ ℒ' ≅ 𝒪_P(1)` on the constructed bundle, which
`Stacks.WeilCohomology.exists_isSubbundleDivisorModule` supplies.

Only the *modules* travel along the clause-(3)(a) identification `S(b) ≅ 𝐏(ℰ)`; the divisor stays
on the constructed bundle. `Stacks.SheafOfModules.pullbackPicardClass_schemeTensor` is additivity
of the pullback class on a tensor product, and
`Stacks.SheafOfModules.pullbackPicardClass_eq_picardClass` identifies the pullback class with the
class of the pullback. -/
theorem twistClass_eq_picardClassOf_add (B : BundleObject S X E r) (M : (S.obj X).Modules)
    (hM : AlgebraicGeometry.SheafOfModules.IsInvertible (S.obj X).presheaf
      (S.obj X).ringCatSheaf.2 M)
    (L : (@Stacks.Chow.bundle (S.obj X) E B.isFiniteLocallyFree).Modules)
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible
      (@Stacks.Chow.bundle (S.obj X) E B.isFiniteLocallyFree).presheaf
      (@Stacks.Chow.bundle (S.obj X) E B.isFiniteLocallyFree).ringCatSheaf.2 L)
    (eT : Scheme.Modules.tensorObj
        ((Scheme.Modules.pullback
          (@Stacks.Chow.bundleProj (S.obj X) E B.isFiniteLocallyFree)).obj M) L ≅
      @Stacks.Chow.bundleTwist (S.obj X) E B.isFiniteLocallyFree) :
    picardClassOf (S.obj B.bundle) ((Scheme.Modules.pullback (S.map B.proj)).obj M)
          (isInvertible_pullback_obj _ M hM) +
        picardClassOf (S.obj B.bundle) ((Scheme.Modules.pullback B.iso.hom).obj L)
          (isInvertible_pullback_obj _ L hL) =
      B.twistClass := by
  have hfl := B.isFiniteLocallyFree
  -- invertibility of `p^*ℳ` and of the tensor product (the two spellings agree by `Iff.rfl`)
  have hAag : AlgebraicGeometry.SheafOfModules.IsInvertible
      (Stacks.Chow.bundle E).presheaf (Stacks.Chow.bundle E).ringCatSheaf.2
      ((Scheme.Modules.pullback (Stacks.Chow.bundleProj E)).obj M) :=
    isInvertible_pullback_obj _ M hM
  have hTag : AlgebraicGeometry.SheafOfModules.IsInvertible
      (Stacks.Chow.bundle E).presheaf (Stacks.Chow.bundle E).ringCatSheaf.2
      (Stacks.SheafOfModules.schemeTensor (Stacks.Chow.bundle E)
        ((Scheme.Modules.pullback (Stacks.Chow.bundleProj E)).obj M) L) :=
    Stacks.SheafOfModules.isInvertible_schemeTensor _ _ _ hAag hL
  -- the pullback class of an invertible module is the class of its pullback
  have hcls : ∀ (N : (Stacks.Chow.bundle E).Modules)
      (hN : AlgebraicGeometry.SheafOfModules.IsInvertible
        (Stacks.Chow.bundle E).presheaf (Stacks.Chow.bundle E).ringCatSheaf.2 N),
      Stacks.SheafOfModules.pullbackPicardClass B.iso.hom N hN =
        picardClassOf (S.obj B.bundle) ((Scheme.Modules.pullback B.iso.hom).obj N)
          (isInvertible_pullback_obj B.iso.hom N hN) :=
    fun N hN => Stacks.SheafOfModules.pullbackPicardClass_eq_picardClass B.iso.hom N hN _
  -- additivity of the pullback class on the tensor product
  have hsplit := Stacks.SheafOfModules.pullbackPicardClass_schemeTensor B.iso.hom
    ((Scheme.Modules.pullback (Stacks.Chow.bundleProj E)).obj M) L hAag hL
  rw [hcls _ hAag, hcls L hL, hcls _ hTag] at hsplit
  -- the tensor product is `𝒪_P(1)`, so its pullback class is the twist class
  have htw : picardClassOf (S.obj B.bundle)
        ((Scheme.Modules.pullback B.iso.hom).obj
          (Stacks.SheafOfModules.schemeTensor (Stacks.Chow.bundle E)
            ((Scheme.Modules.pullback (Stacks.Chow.bundleProj E)).obj M) L))
        (isInvertible_pullback_obj B.iso.hom _ hTag) =
      B.twistClass :=
    picardClassOf_eq_of_iso (S.obj B.bundle) _ B.twist
      (isInvertible_pullback_obj B.iso.hom _ hTag) B.twist_isInvertible
      ((Scheme.Modules.pullback B.iso.hom).mapIso eT ≪≫ eqToIso B.twist_eq.symm)
  -- the pullback of `p^*ℳ` along the identification is `S(p)^*ℳ`
  have hproj : picardClassOf (S.obj B.bundle)
        ((Scheme.Modules.pullback B.iso.hom).obj
          ((Scheme.Modules.pullback (Stacks.Chow.bundleProj E)).obj M))
        (isInvertible_pullback_obj B.iso.hom _ hAag) =
      picardClassOf (S.obj B.bundle) ((Scheme.Modules.pullback (S.map B.proj)).obj M)
        (isInvertible_pullback_obj _ M hM) :=
    picardClassOf_eq_of_iso (S.obj B.bundle) _ _ _ _ (B.pullObjIso M).symm
  rw [← htw, ← hproj]
  exact hsplit.symm

end BundleObject

end Stacks.WeilCohomology

end
