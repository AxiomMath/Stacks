module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import StacksFrontier.AlgebraicGeometry.CompactOpenInduction.Basic
public import StacksFrontier.AlgebraicGeometry.HigherDirectImageQcoh.LocalityAndExactness
public import StacksFrontier.AlgebraicGeometry.RelativeMayerVietoris.Qcoh
public import StacksFrontier.Topology.Sheaves.Cohomology.RelativeMayerVietoris.LongExactSequence
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.AffineBaseChange.Basic

/-!
# Quasi-coherence of the higher direct images of a quasi-coherent module

[Stacks, Tag 01XJ] part (1) asserts that the higher direct images `R ᵖ f_* F` of a quasi-coherent
module along a quasi-compact quasi-separated morphism of schemes are quasi-coherent. This file
proves it, in every integer degree, as
`Stacks.AlgebraicGeometry.Tag01XJQcohInduction.higherDirectImage_isQuasicoherent`.

Every ingredient of the source's proof was already in the tree; what was missing was the
induction that composes them.

* **locality on the base** is
  `Stacks.AlgebraicGeometry.HigherDirectImageQcoh.isQuasicoherent_rightDerivedPlus_of_affineOpens`
  ([Stacks, Tag 01E5] for schemes), reducing to an affine base;
* **the induction over the quasi-compact opens of the source** is [Stacks, Tag 08DR], in the form
  `Stacks.AlgebraicGeometry.CompactOpenInduction.top_of_qcqs_over_affine`, which was written for
  this tag;
* **the base case** is [Stacks, Tag 01XC], as the lemma
  `isQuasicoherent_higherDirectImage_of_isAffineHom` in the namespace
  `Stacks.AlgebraicGeometry.HigherDirectImageAffine`;
* **the inductive step** reads `R ᵖ` off the relative Mayer-Vietoris long exact sequence
  `Stacks.Cohomology.RelativeMayerVietoris.relativeMayerVietorisPlus` ([Stacks, Tag 01EC]) using
  `Stacks.AlgebraicGeometry.HigherDirectImageQcoh.isQuasicoherent_of_exact₄`.

## Main definitions

* `Stacks.AlgebraicGeometry.Tag01XJQcohInduction.QcohImage`: the property of an open `U` of the
  source that carries the induction.

## Main results

* `Stacks.AlgebraicGeometry.Tag01XJQcohInduction.higherDirectImage_isQuasicoherent`:
  **[Stacks, Tag 01XJ], the `quasicoherence` assertion.**
* `Stacks.AlgebraicGeometry.Tag01XJQcohInduction.isQuasicoherent_rightDerivedPlus_of_isAffine`:
  the same over an affine base.
* `Stacks.AlgebraicGeometry.Tag01XJQcohInduction.isQuasicoherent_of_mvSequence`: the middle term
  of the Mayer-Vietoris sequence is quasi-coherent when its four neighbours are.

## Implementation notes

**Why the induction is over open immersions rather than over opens.** `QcohImage f F U`
quantifies over *every* open immersion `j` whose image is `U`, not just over `U.ι`. This is what
makes the available Mayer-Vietoris sequence sufficient. `relativeMayerVietorisPlus` has the
hypothesis `Set.range iU ∪ Set.range iV = Set.univ`, i.e. it covers the *whole* source; in the
inductive step for `U ⊔ V` one is handed `j : Y ⟶ X` with image `U ⊔ V`, and then
`j ⁻¹ᵁ U` and `j ⁻¹ᵁ V` cover the whole of `Y`, so the total-cover sequence applies verbatim.
Quantifying over all `j` is also what lets the step recurse: the inclusion of `j ⁻¹ᵁ U` followed
by `j` is again an open immersion with image `U`, so no isomorphism of open subschemes has to be
transported.

An induction phrased over `U.ι` alone would instead need the Mayer-Vietoris short exact sequence
for a cover of `U ⊔ V` by `U` and `V` with `U ⊔ V` arbitrary. The docstring of
`StacksFrontier/AlgebraicGeometry/HigherDirectImageQcoh/LocalityAndExactness.lean` records that
sequence as the whole remaining content of this tag; **it is not needed**, because the reformulation
above moves the cover to the whole of a source and the available sequence already covers that case.

**The degree bookkeeping is free.** `QcohImage` asserts quasi-coherence in *every* integer degree
rather than up to a bound, so the step may use the degrees `m` and `m + 1` that the sequence
supplies without any index arithmetic: writing the goal degree as `m + 1` by
`obtain ⟨m, rfl⟩ : ∃ m, n = m + 1`, the three exactness fields of
`RelativeMayerVietorisSequencePlus` are consumed at `m`, `m` and `m + 1` exactly as stated. The
negative degrees need no separate treatment here, being part of the same universally quantified
statement, discharged in the base case by [Stacks, Tag 01XC].

**The scheme / ringed-space bridge is definitional, and needs no compiler option.** The
Mayer-Vietoris sequence is stated for morphisms of ringed spaces, in terms of
`RingedSpaceModuleAdjunction.modulePushforward` and `modulePullback`, while the statement of this
tag uses `AlgebraicGeometry.Scheme.Modules.pushforward` and `Scheme.Modules.pullback`. All of

* `Scheme.Modules.pushforward f = modulePushforward f.toLRSHom.toShHom`,
* `Scheme.Modules.pullback j = modulePullback j.toLRSHom.toShHom`,
* `(i ≫ f).toLRSHom.toShHom = i.toLRSHom.toShHom ≫ f.toLRSHom.toShHom`, and hence
* `restrictedHigherDirectImagePlus f' i' n =
  Scheme.Modules.pullback i ⋙ (Scheme.Modules.pushforward (i ≫ f)).rightDerivedPlus n`

hold by `rfl`, so `isQuasicoherent_of_mvSequence` is applied to scheme-level data directly. The
`pushforward` identification was already recorded at
`StacksFrontier/AlgebraicGeometry/HigherDirectImageAffine/AffineMorphismVanishing.lean`; the
`pullback` one is checked here.

**What is not definitional** is re-bracketing: `QcohImage` applied to a composite `i ≫ j` speaks
of `(i ≫ j) ≫ f` and of `(i ≫ j)^* F`, where the sequence over the source of `j` speaks of
`i ≫ (j ≫ f)` and of `i^* j^* F`. `isQuasicoherent_nested` bridges the two, by `simp only
[Category.assoc]` — which transports through `Functor.rightDerivedPlus` because that functor
depends on its argument only through a `Prop`-valued class, so the motive is type-correct — and by
`Scheme.Modules.pullbackComp`.

**Biproducts in the functor category.** The middle terms of the sequence are biproducts of
*functors*, so their values are not literally biproducts of modules;
`isQuasicoherent_biprod_obj` moves across that by `Functor.mapBiprod` for evaluation at the
module, which is additive and preserves binary products.
`CategoryTheory.Abelian.hasBinaryBiproducts` is installed at a raised priority, as in the file
that states the sequence, and
`CategoryTheory.Limits.preservesBinaryBiproducts_of_preservesBinaryProducts` is not a global
instance in Mathlib.

## References

* [Stacks Project, Tag 01XJ](https://stacks.math.columbia.edu/tag/01XJ)
* [Stacks Project, Tag 01E5](https://stacks.math.columbia.edu/tag/01E5)
* [Stacks Project, Tag 01EC](https://stacks.math.columbia.edu/tag/01EC)
* [Stacks Project, Tag 01XC](https://stacks.math.columbia.edu/tag/01XC)
* [Stacks Project, Tag 08DR](https://stacks.math.columbia.edu/tag/08DR)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry RingedSpaceModuleAdjunction
open Stacks.Cohomology.RelativeMayerVietoris

universe u

attribute [local instance] HasDerivedCategory.standard

namespace Stacks.AlgebraicGeometry.Tag01XJQcohInduction

variable {X S : Scheme.{u}}

section Biprod

attribute [local instance 2000] CategoryTheory.Abelian.hasBinaryBiproducts
attribute [local instance] preservesBinaryBiproducts_of_preservesBinaryProducts

/-- The value at `M` of a biproduct of two functors into modules on `S` is quasi-coherent as soon
as the two values are: evaluation at `M` is additive and preserves binary products, hence carries
the biproduct of functors to the biproduct of values. -/
theorem isQuasicoherent_biprod_obj {Y : Scheme.{u}}
    (F G : SheafOfModules.{u} Y.ringCatSheaf ⥤ SheafOfModules.{u} S.ringCatSheaf)
    (M : SheafOfModules.{u} Y.ringCatSheaf)
    (hF : (F.obj M).IsQuasicoherent) (hG : (G.obj M).IsQuasicoherent) :
    ((F ⊞ G).obj M).IsQuasicoherent :=
  (SheafOfModules.isQuasicoherent S.ringCatSheaf).prop_of_iso
    (((evaluation (SheafOfModules.{u} Y.ringCatSheaf)
      (SheafOfModules.{u} S.ringCatSheaf)).obj M).mapBiprod F G).symm
    (RelativeMayerVietoris.isQuasicoherent_biprod _ _ hF hG)

end Biprod

/-! ### Reading the higher direct image off the Mayer-Vietoris sequence -/

section Sequence

attribute [local instance 2000] CategoryTheory.Abelian.hasBinaryBiproducts

/-- **The Mayer-Vietoris step.** In the long exact sequence of [Stacks, Tag 01EC],

`R ᵐ|_U ⊕ R ᵐ|_V ⟶ R ᵐ|_W ⟶ R ᵐ⁺¹ g_* ⟶ R ᵐ⁺¹|_U ⊕ R ᵐ⁺¹|_V ⟶ R ᵐ⁺¹|_W`,

the middle term `R ᵐ⁺¹ g_*` is quasi-coherent as soon as its four neighbours are. The three
exactness assertions are the sequence's own fields at `m`, `m` and `m + 1`, so no index
arithmetic is needed; the conclusion is
`Stacks.AlgebraicGeometry.HigherDirectImageQcoh.isQuasicoherent_of_exact₄`. -/
theorem isQuasicoherent_of_mvSequence {Z U V W : RingedSpace.{u, u}}
    {g : Z ⟶ S.toRingedSpace} {iU : U ⟶ Z} {iV : V ⟶ Z} {iW : W ⟶ Z}
    (MV : RelativeMayerVietorisSequencePlus g iU iV iW)
    (M : SheafOfModules.{u} (structureSheafRing Z)) (m : ℤ)
    (hC : ((restrictedHigherDirectImagePlus g iU m ⊞
      restrictedHigherDirectImagePlus g iV m).obj M).IsQuasicoherent)
    (hI : ((restrictedHigherDirectImagePlus g iW m).obj M).IsQuasicoherent)
    (hC' : ((restrictedHigherDirectImagePlus g iU (m + 1) ⊞
      restrictedHigherDirectImagePlus g iV (m + 1)).obj M).IsQuasicoherent)
    (hI' : ((restrictedHigherDirectImagePlus g iW (m + 1)).obj M).IsQuasicoherent) :
    ((higherDirectImagePlus g (m + 1)).obj M).IsQuasicoherent := by
  obtain ⟨zab, eab⟩ := MV.exact_intersection m M
  obtain ⟨zbc, ebc⟩ := MV.exact_base m M
  obtain ⟨zcd, ecd⟩ := MV.exact_cover (m + 1) M
  exact HigherDirectImageQcoh.isQuasicoherent_of_exact₄ _ _ _ _ zab zbc zcd eab ebc ecd
    hC hI hC' hI'

end Sequence

/-- **Re-bracketing a nested open immersion.** The predicate `QcohImage` applied to the composite
`i ≫ j` speaks of `(i ≫ j) ≫ f` and of `(i ≫ j)^* F`, while the Mayer-Vietoris sequence over the
source of `j` speaks of `i ≫ (j ≫ f)` and of `i^* j^* F`. The two differ by associativity, which
transports under `simp only` because `Functor.rightDerivedPlus` depends on its functor only
through a `Prop`-valued class, and by `Scheme.Modules.pullbackComp`. -/
theorem isQuasicoherent_nested {Y Z : Scheme.{u}} (f : X ⟶ S) (j : Y ⟶ X) (i : Z ⟶ Y)
    (F : X.Modules) (n : ℤ)
    (h : (((Scheme.Modules.pushforward ((i ≫ j) ≫ f)).rightDerivedPlus n).obj
      ((Scheme.Modules.pullback (i ≫ j)).obj F)).IsQuasicoherent) :
    (((Scheme.Modules.pushforward (i ≫ j ≫ f)).rightDerivedPlus n).obj
      ((Scheme.Modules.pullback i).obj ((Scheme.Modules.pullback j).obj F))).IsQuasicoherent := by
  simp only [Category.assoc] at h
  exact (SheafOfModules.isQuasicoherent S.ringCatSheaf).prop_of_iso
    (((Scheme.Modules.pushforward (i ≫ j ≫ f)).rightDerivedPlus n).mapIso
      ((Scheme.Modules.pullbackComp i j).app F).symm) h

section Step

attribute [local instance 2000] CategoryTheory.Abelian.hasBinaryBiproducts

/-- **The inductive step, with the two opens of the source given explicitly.** For `A`, `B` opens
of `Y` covering `Y`, if the higher direct images along `A.ι ≫ j ≫ f`, `B.ι ≫ j ≫ f` and
`(A ⊓ B).ι ≫ j ≫ f` of the restrictions of `j^* F` are quasi-coherent in all degrees, then
`R ᵐ⁺¹ (j ≫ f)_* (j^* F)` is quasi-coherent.

Because `A` and `B` cover the *whole* of `Y`, the relative Mayer-Vietoris sequence of
[Stacks, Tag 01EC] applies in the form in which it is stated in the library, whose cover hypothesis is
`Set.range iU ∪ Set.range iV = Set.univ`. -/
theorem isQuasicoherent_succ_of_cover (f : X ⟶ S) (F : X.Modules) {Y : Scheme.{u}} (j : Y ⟶ X)
    (A B : Y.Opens) (hcover : A ⊔ B = ⊤) (m : ℤ)
    (hA : ∀ k : ℤ, (((Scheme.Modules.pushforward (A.ι ≫ j ≫ f)).rightDerivedPlus k).obj
      ((Scheme.Modules.pullback A.ι).obj ((Scheme.Modules.pullback j).obj F))).IsQuasicoherent)
    (hB : ∀ k : ℤ, (((Scheme.Modules.pushforward (B.ι ≫ j ≫ f)).rightDerivedPlus k).obj
      ((Scheme.Modules.pullback B.ι).obj ((Scheme.Modules.pullback j).obj F))).IsQuasicoherent)
    (hI : ∀ k : ℤ, (((Scheme.Modules.pushforward ((A ⊓ B).ι ≫ j ≫ f)).rightDerivedPlus k).obj
      ((Scheme.Modules.pullback (A ⊓ B).ι).obj
        ((Scheme.Modules.pullback j).obj F))).IsQuasicoherent) :
    (((Scheme.Modules.pushforward (j ≫ f)).rightDerivedPlus (m + 1)).obj
      ((Scheme.Modules.pullback j).obj F)).IsQuasicoherent := by
  have hcov : Set.range (A.ι.toLRSHom.toShHom).hom.base ∪
      Set.range (B.ι.toLRSHom.toShHom).hom.base = Set.univ := by
    show Set.range A.ι.base ∪ Set.range B.ι.base = Set.univ
    rw [Scheme.Opens.range_ι, Scheme.Opens.range_ι]
    exact congrArg (fun T : Y.Opens => (T : Set Y)) hcover
  have hint : Set.range ((A ⊓ B).ι.toLRSHom.toShHom).hom.base =
      Set.range (A.ι.toLRSHom.toShHom).hom.base ∩
        Set.range (B.ι.toLRSHom.toShHom).hom.base := by
    show Set.range (A ⊓ B).ι.base = Set.range A.ι.base ∩ Set.range B.ι.base
    rw [Scheme.Opens.range_ι, Scheme.Opens.range_ι, Scheme.Opens.range_ι]
    rfl
  obtain ⟨MV⟩ := relativeMayerVietorisPlus (j ≫ f).toLRSHom.toShHom
    A.ι.toLRSHom.toShHom B.ι.toLRSHom.toShHom (A ⊓ B).ι.toLRSHom.toShHom hcov hint
  exact isQuasicoherent_of_mvSequence MV ((Scheme.Modules.pullback j).obj F) m
    (isQuasicoherent_biprod_obj _ _ _ (hA m) (hB m)) (hI m)
    (isQuasicoherent_biprod_obj _ _ _ (hA (m + 1)) (hB (m + 1))) (hI (m + 1))

end Step

/-! ### The induction predicate -/

/-- The property of an open `U` of `X` that drives the induction of [Stacks, Tag 01XJ]: every
higher direct image along `j ≫ f`, for `j` an open immersion with image `U`, of the inverse image
of `F`, is quasi-coherent. -/
def QcohImage (f : X ⟶ S) (F : X.Modules) (U : X.Opens) : Prop :=
  ∀ ⦃Y : Scheme.{u}⦄ (j : Y ⟶ X), IsOpenImmersion j → Set.range j.base = U → ∀ n : ℤ,
    (((Scheme.Modules.pushforward (j ≫ f)).rightDerivedPlus n).obj
      ((Scheme.Modules.pullback j).obj F)).IsQuasicoherent

/-- The image of the inclusion of `j ⁻¹ᵁ U` followed by `j` is `U`, when `U` is contained in the
image of `j`. -/
theorem range_preimage_ι_comp {Y : Scheme.{u}} (j : Y ⟶ X) [IsOpenImmersion j] (W U : X.Opens)
    (hW : j.opensRange = W) (hUW : U ≤ W) : Set.range ((j ⁻¹ᵁ U).ι ≫ j).base = U := by
  show (((j ⁻¹ᵁ U).ι ≫ j).opensRange : Set X) = U
  rw [Scheme.Hom.opensRange_comp, Scheme.Opens.opensRange_ι,
    Scheme.Hom.image_preimage_eq_opensRange_inf, hW]
  exact inf_eq_right.mpr hUW

/-- Taking the preimage of an open along `j` commutes with intersection. -/
theorem preimage_inf {Y : Scheme.{u}} (j : Y ⟶ X) (U V : X.Opens) :
    j ⁻¹ᵁ U ⊓ j ⁻¹ᵁ V = j ⁻¹ᵁ (U ⊓ V) := rfl

/-- **The inductive step in the form the induction principle wants.** -/
theorem qcohImage_sup (f : X ⟶ S) (F : X.Modules) (U V : X.Opens)
    (hU : QcohImage f F U) (hV : QcohImage f F V) (hI : QcohImage f F (U ⊓ V)) :
    QcohImage f F (U ⊔ V) := by
  intro Y j _ hrange n
  obtain ⟨m, rfl⟩ : ∃ m : ℤ, n = m + 1 := ⟨n - 1, by omega⟩
  have hRange : j.opensRange = U ⊔ V := SetLike.coe_injective hrange
  have hAB : j ⁻¹ᵁ U ⊔ j ⁻¹ᵁ V = ⊤ := by
    ext y
    refine ⟨fun _ => trivial, fun _ => ?_⟩
    have hy : j.base y ∈ ((U ⊔ V : X.Opens) : Set X) := hrange ▸ ⟨y, rfl⟩
    simpa using hy
  refine isQuasicoherent_succ_of_cover f F j (j ⁻¹ᵁ U) (j ⁻¹ᵁ V) hAB m
    (fun k => isQuasicoherent_nested f j (j ⁻¹ᵁ U).ι F k
      (hU _ inferInstance (range_preimage_ι_comp j (U ⊔ V) U hRange le_sup_left) k))
    (fun k => isQuasicoherent_nested f j (j ⁻¹ᵁ V).ι F k
      (hV _ inferInstance (range_preimage_ι_comp j (U ⊔ V) V hRange le_sup_right) k)) ?_
  intro k
  rw [preimage_inf]
  exact isQuasicoherent_nested f j (j ⁻¹ᵁ (U ⊓ V)).ι F k
    (hI _ inferInstance
      (range_preimage_ι_comp j (U ⊔ V) (U ⊓ V) hRange (inf_le_left.trans le_sup_left)) k)

/-- **The base case.** Over an affine base, an open immersion whose image is an affine open has
affine source, so `j ≫ f` is an affine morphism and [Stacks, Tag 01XC] gives the conclusion in
every integer degree. -/
theorem qcohImage_of_isAffineOpen (f : X ⟶ S) [IsAffine S] (F : X.Modules) [F.IsQuasicoherent]
    (U : X.Opens) (hU : IsAffineOpen U) : QcohImage f F U := by
  intro Y j _ hrange n
  have hRange : j.opensRange = U := SetLike.coe_injective hrange
  have : IsAffine j.opensRange.toScheme := by rwa [hRange]
  have : IsAffine Y := IsAffine.of_isIso j.isoOpensRange.hom
  have : IsAffineHom (j ≫ f) := isAffineHom_of_isAffine _
  have : ((Scheme.Modules.pullback j).obj F).IsQuasicoherent :=
    Stacks.AlgebraicGeometry.AffineBaseChange.isQuasicoherent_pullback_of_isOpenImmersion j F
  exact HigherDirectImageAffine.isQuasicoherent_higherDirectImage_of_isAffineHom (j ≫ f) _ n

/-! ### The theorem -/

/-- **The induction, run.** Over an affine base `S`, for `f` quasi-compact and quasi-separated,
`QcohImage f F` holds at `⊤`: this is [Stacks, Tag 08DR] applied to the base case
`qcohImage_of_isAffineOpen` and the Mayer-Vietoris step `qcohImage_sup`. -/
theorem qcohImage_top (f : X ⟶ S) [IsAffine S] [QuasiCompact f] [QuasiSeparated f]
    (F : X.Modules) [F.IsQuasicoherent] : QcohImage f F ⊤ :=
  CompactOpenInduction.top_of_qcqs_over_affine (P := QcohImage f F)
    (fun U hU => qcohImage_of_isAffineOpen f F U hU)
    (fun U V _ _ hU hV hI => qcohImage_sup f F U V hU hV hI) f

/-- **[Stacks, Tag 01XJ] part (1) over an affine base.** Instantiating `QcohImage f F ⊤` at the
identity open immersion `𝟙 X`, whose image is all of `X`. -/
theorem isQuasicoherent_rightDerivedPlus_of_isAffine (f : X ⟶ S) [IsAffine S] [QuasiCompact f]
    [QuasiSeparated f] (F : X.Modules) [F.IsQuasicoherent] (p : ℤ) :
    (((Scheme.Modules.pushforward f).rightDerivedPlus p).obj F).IsQuasicoherent := by
  have h := qcohImage_top f F (𝟙 X) inferInstance (by simp) p
  simp only [Category.id_comp] at h
  exact (SheafOfModules.isQuasicoherent S.ringCatSheaf).prop_of_iso
    (((Scheme.Modules.pushforward f).rightDerivedPlus p).mapIso
      ((Scheme.Modules.pullbackId X).app F)) h

/-- **Stacks Project, Tag 01XJ (quasicoherence).** The higher direct images of a quasi-coherent
module under a quasi-compact and quasi-separated morphism of schemes are quasi-coherent.

Quasi-coherence is local on the base
(`Stacks.AlgebraicGeometry.HigherDirectImageQcoh.isQuasicoherent_rightDerivedPlus_of_affineOpens`,
which is [Stacks, Tag 01E5] for schemes), and `f ∣_ V` is again quasi-compact and quasi-separated
with affine target, so the statement reduces to
`isQuasicoherent_rightDerivedPlus_of_isAffine`. -/
@[stacks 01XJ "quasicoherence", ega "III 6.2.3" "special case"]
instance higherDirectImage_isQuasicoherent (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f]
    (F : X.Modules) [F.IsQuasicoherent] (p : ℤ) :
    (((Scheme.Modules.pushforward f).rightDerivedPlus p).obj F).IsQuasicoherent :=
  HigherDirectImageQcoh.isQuasicoherent_rightDerivedPlus_of_affineOpens f F p fun V => by
    have : IsAffine (V : S.Opens).toScheme := V.2
    exact isQuasicoherent_rightDerivedPlus_of_isAffine (f ∣_ (V : S.Opens)) _ p

end Stacks.AlgebraicGeometry.Tag01XJQcohInduction

end
