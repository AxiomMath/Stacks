module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import StacksFrontier.AlgebraicGeometry.HigherDirectImageAffine.AffineMorphismVanishing
public import StacksFrontier.AlgebraicGeometry.ProjectiveCoherentImage.Basic
public import StacksFrontier.AlgebraicGeometry.QcohInduction.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.AffineBaseChange.Basic

/-!
# Uniform vanishing of the higher direct images of a quasi-coherent module

[Stacks, Tag 01XJ] part (2) asserts that for `f : X ⟶ S` quasi-compact and quasi-separated with
`S` quasi-compact there is an integer `n`, depending only on `f`, such that `R ᵖ f_* F = 0` for
all `p ≥ n` and **every** quasi-coherent `𝒪_X`-module `F`.  This file proves it as
`Stacks.AlgebraicGeometry.Tag01XJUniformVanishing.exists_isZero_rightDerived_pushforward`.

## The cohomological-dimension bound, as it is stated here

The bound is not produced as an explicit number.  It is carried by the induction predicate
`VanishImage`, which has the existential quantifier *inside*:

`VanishImage f U` says that there is **one** integer `n` such that for every open immersion `j`
with image `U`, every quasi-coherent `F` on `X` and every `p ≥ n`, the higher direct image
`R ᵖ (j ≫ f)_* (j^* F)` vanishes.

The induction of [Stacks, Tag 08DR] then produces the bound for `U = ⊤` by the same recursion
that produces the vanishing: the affine base case gives the bound `1`, and the Mayer–Vietoris
step for `U ⊔ V` gives `max (max n_U n_V) n_W + 1`.  Unwinding the recursion, the bound obtained
for `⊤` over an affine base is one more than the number of affine opens the induction consumes,
i.e. the length of a finite affine cover of `X` — which is exactly where the source gets it.  For
a general quasi-compact base it is the maximum of the bounds of the finitely many affine opens of
a cover of `S`.  Making the number explicit is *not* needed for the statement, and the existential
form is what makes the induction principle of [Stacks, Tag 08DR] applicable unchanged: the
principle quantifies over a property of opens, and "there is a bound" is such a property while
"the bound is `n`" is not.

Uniformity in `F` is likewise free: `VanishImage` quantifies over every quasi-coherent `F` on `X`
inside the existential, so no step of the induction may choose a bound depending on `F`.

## Main definitions

* `Stacks.AlgebraicGeometry.Tag01XJUniformVanishing.VanishImage`: the property of an open `U` of
  the source that carries the induction.

## Main results

* `Stacks.AlgebraicGeometry.Tag01XJUniformVanishing.exists_isZero_rightDerived_pushforward`:
  **[Stacks, Tag 01XJ], the `uniform_vanishing` assertion.**
* `Stacks.AlgebraicGeometry.Tag01XJUniformVanishing`'s
  `exists_isZero_rightDerived_pushforward_of_isAffine`: the same over an affine base, which is
  what the induction proves.
* `Stacks.AlgebraicGeometry.Tag01XJUniformVanishing.isZero_of_isZero_restrict`: a sheaf of
  modules on a scheme which restricts to zero on each member of an open cover is zero.

## Implementation notes

The skeleton is the one the sibling assertion of this tag uses
(`StacksFrontier/AlgebraicGeometry/QcohInduction/Basic.lean`), with quasi-coherence of the
middle term of the Mayer–Vietoris sequence replaced by its vanishing and with a degree bound
threaded through:

* the base case is [Stacks, Tag 01XC] in the vanishing form
  `Stacks.AlgebraicGeometry.HigherDirectImageAffine.isZero_higherDirectImage_of_pos`;
* the inductive step reads vanishing of `R ᵐ⁺¹ (j ≫ f)_*` off exactness at that term of the
  relative Mayer–Vietoris sequence of [Stacks, Tag 01EC], which needs only **two** of the four
  neighbours (the incoming `R ᵐ|_{U ⊓ V}` and the outgoing `R ᵐ⁺¹|_U ⊕ R ᵐ⁺¹|_V`) rather than all
  four, since a monomorphism out of an object which is itself zero forces the object to vanish;
* the induction over the quasi-compact opens of the source is
  `Stacks.AlgebraicGeometry.CompactOpenInduction.top_of_qcqs_over_affine`, [Stacks, Tag 08DR];
* the predicate is phrased over **every** open immersion with a given image, not over `U.ι`, for
  the reason recorded in the sibling file: the library's Mayer–Vietoris sequence covers the *whole*
  of its source, and a `j` with image `U ⊔ V` has `j ⁻¹ᵁ U` and `j ⁻¹ᵁ V` covering all of its
  source.  `range_preimage_ι_comp` and `preimage_inf` are reused from the sibling file.

**Locality on the base is at `IsZero`, not at quasi-coherence, so [Stacks, Tag 01E5] is used
differently.** The sibling assertion is a property local on `S`, and
`isQuasicoherent_rightDerivedPlus_of_affineOpens` quantifies over *all* affine opens of `S`.  A
*bound* cannot be assembled from an infinite family, so here `S` is covered by **finitely many**
affine opens — which is what `[CompactSpace S]` supplies — the bound is the maximum of their
bounds, and the vanishing is glued by `isZero_of_isZero_restrict`, a stalkwise argument over
`CategoryTheory.Limits.IsZero` on `AlgebraicGeometry.Scheme.Modules.restrictFunctor`.  The
comparison of the restriction of a higher direct image with the higher direct image of the
restriction is [Stacks, Tag 01E5] for schemes, in the form
`AlgebraicGeometry.ProjectiveCoherentImage.higherDirectImageRestrictObjIso`.

Quasi-coherence of the higher direct images is **not** used anywhere: the only place
quasi-coherence of a module enters is the affine base case, where it is quasi-coherence of the
inverse image of `F`.

## References

* [Stacks Project, Tag 01XJ](https://stacks.math.columbia.edu/tag/01XJ)
* [Stacks Project, Tag 01E5](https://stacks.math.columbia.edu/tag/01E5)
* [Stacks Project, Tag 01EC](https://stacks.math.columbia.edu/tag/01EC)
* [Stacks Project, Tag 01XC](https://stacks.math.columbia.edu/tag/01XC)
* [Stacks Project, Tag 08DR](https://stacks.math.columbia.edu/tag/08DR)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open AlgebraicGeometry RingedSpaceModuleAdjunction
open Stacks.Cohomology.RelativeMayerVietoris

universe u

attribute [local instance] HasDerivedCategory.standard

namespace Stacks.AlgebraicGeometry.Tag01XJUniformVanishing

variable {X S : Scheme.{u}}

/-! ### A finite affine cover of a quasi-compact scheme -/

/-- A quasi-compact scheme is covered by a finite family of affine opens, indexed by `Fin m`.
The `Fin` indexing is what lets the bound of [Stacks, Tag 01XJ] be taken as a `Finset.sup`. -/
theorem exists_fin_affineOpen_cover (T : Scheme.{u}) [CompactSpace T] :
    ∃ (m : ℕ) (B : Fin m → T.Opens), (∀ j, IsAffineOpen (B j)) ∧ iSup B = ⊤ := by
  classical
  have htop : IsCompact ((⊤ : T.Opens) : Set T) := by
    simpa using (isCompact_univ : IsCompact (Set.univ : Set T))
  obtain ⟨Us, hUs, hUsfin, hUssup⟩ :=
    T.isBasis_affineOpens.exists_finite_of_isCompact (U := ⊤) htop
  have : Fintype Us := hUsfin.fintype
  let e := Fintype.equivFin Us
  refine ⟨Fintype.card Us, fun i => (e.symm i).val, fun i => hUs (e.symm i).property,
    le_antisymm le_top ?_⟩
  rw [hUssup, sSup_eq_iSup]
  refine iSup_le fun U' => iSup_le fun hU' => ?_
  exact le_iSup_of_le (e ⟨U', hU'⟩) (by simp)

/-! ### Vanishing of a sheaf of modules is local on the scheme -/

/-- **Vanishing of a sheaf of modules is local.** If a scheme `T` is covered by opens `U i` and
the restriction of `M` to each `U i` is a zero object, then `M` is a zero object.

The argument is stalkwise: `AlgebraicGeometry.Scheme.Modules.restrictStalkNatIso` identifies the
stalk at a point of `U i` of the restriction with the stalk of `M`,
`TopCat.Sheaf.isZero_iff_stalkFunctor_obj_isZero` detects vanishing of the underlying sheaf of
abelian groups from its stalks, and `AlgebraicGeometry.Scheme.Modules.toPresheaf` is faithful. -/
@[sga "4 IV 8.5.1" "partial"]
theorem isZero_of_isZero_restrict {T : Scheme.{u}} {I : Type*} (U : I → T.Opens)
    (hU : iSup U = ⊤) (M : T.Modules)
    (hrest : ∀ i, IsZero ((Scheme.Modules.restrictFunctor (U i).ι).obj M)) : IsZero M := by
  have hstalk (x : T) : IsZero (M.presheaf.stalk x) := by
    have hxcover : x ∈ ⋃ i, (U i : Set T) := by
      have hx : x ∈ (iSup U : T.Opens) := by rw [hU]; simp
      simpa using hx
    obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hxcover
    let y : (U i : Scheme) := ⟨x, hxi⟩
    have hz : IsZero
        (((Scheme.Modules.restrictFunctor (U i).ι).obj M).presheaf.stalk y) :=
      Functor.map_isZero
        (Scheme.Modules.toPresheaf (U i : Scheme) ⋙
          TopCat.Presheaf.stalkFunctor.{u} Ab (y : TopCat.of (U i : Scheme))) (hrest i)
    exact IsZero.of_iso hz
      ((Scheme.Modules.restrictStalkNatIso (U i).ι y).app M).symm
  have hF := (TopCat.Sheaf.isZero_iff_stalkFunctor_obj_isZero
    (⟨M.presheaf, M.isSheaf⟩ : TopCat.Sheaf Ab.{u} _)).mpr hstalk
  have hP : IsZero ((Scheme.Modules.toPresheaf T).obj M) :=
    Functor.map_isZero (TopCat.Sheaf.forget Ab.{u} _) hF
  exact (IsZero.iff_id_eq_zero M).mpr
    ((Scheme.Modules.toPresheaf T).map_injective (hP.eq_of_src _ _))

/-! ### Reading the vanishing off the Mayer–Vietoris sequence -/

section Biprod

attribute [local instance 2000] CategoryTheory.Abelian.hasBinaryBiproducts
attribute [local instance] preservesBinaryBiproducts_of_preservesBinaryProducts

/-- The value at `M` of a biproduct of two functors into modules on `S` is a zero object as soon
as the two values are: evaluation at `M` preserves binary biproducts. -/
theorem isZero_biprod_obj {Y : Scheme.{u}}
    (F G : SheafOfModules.{u} Y.ringCatSheaf ⥤ SheafOfModules.{u} S.ringCatSheaf)
    (M : SheafOfModules.{u} Y.ringCatSheaf)
    (hF : IsZero (F.obj M)) (hG : IsZero (G.obj M)) : IsZero ((F ⊞ G).obj M) := by
  let E := (evaluation (SheafOfModules.{u} Y.ringCatSheaf)
    (SheafOfModules.{u} S.ringCatSheaf)).obj M
  have hE : E.Additive := inferInstance
  have hEl : PreservesFiniteLimits E := inferInstance
  exact IsZero.of_iso
    (Stacks.Cohomology.RelativeMayerVietoris.isZero_biprod hF hG) (E.mapBiprod F G)

end Biprod

section Sequence

attribute [local instance 2000] CategoryTheory.Abelian.hasBinaryBiproducts

/-- **The Mayer–Vietoris step for vanishing.** In the long exact sequence of [Stacks, Tag 01EC],

`R ᵐ|_W ⟶ R ᵐ⁺¹ g_* ⟶ R ᵐ⁺¹|_U ⊕ R ᵐ⁺¹|_V`,

the middle term vanishes as soon as its two neighbours do.  Exactness at the middle term is the
sequence's field `exact_base` at `m`; with a zero incoming term the outgoing map is a
monomorphism, and with a zero outgoing term it is the zero morphism, so the identity of the
middle term is zero.

Only two of the four neighbours used by the quasi-coherence half of this tag are needed. -/
theorem isZero_of_mvSequence {Z U V W : RingedSpace.{u, u}}
    {g : Z ⟶ S.toRingedSpace} {iU : U ⟶ Z} {iV : V ⟶ Z} {iW : W ⟶ Z}
    (MV : RelativeMayerVietorisSequencePlus g iU iV iW)
    (M : SheafOfModules.{u} (structureSheafRing Z)) (m : ℤ)
    (hI : IsZero ((restrictedHigherDirectImagePlus g iW m).obj M))
    (hC' : IsZero ((restrictedHigherDirectImagePlus g iU (m + 1) ⊞
      restrictedHigherDirectImagePlus g iV (m + 1)).obj M)) :
    IsZero ((higherDirectImagePlus g (m + 1)).obj M) := by
  obtain ⟨zbc, ebc⟩ := MV.exact_base m M
  have hmono : Mono ((MV.toCover (m + 1)).app M) :=
    ebc.mono_g (hI.eq_of_src _ _)
  have hzero : (MV.toCover (m + 1)).app M = 0 := hC'.eq_of_tgt _ _
  refine (IsZero.iff_id_eq_zero _).mpr ((cancel_mono ((MV.toCover (m + 1)).app M)).1 ?_)
  simp [hzero]

end Sequence

/-- **Re-bracketing a nested open immersion**, the vanishing counterpart of
`Stacks.AlgebraicGeometry.Tag01XJQcohInduction.isQuasicoherent_nested`.  The two sides differ by
associativity, which transports under `simp only` because `Functor.rightDerivedPlus` depends on
its functor only through a `Prop`-valued class, and by
`AlgebraicGeometry.Scheme.Modules.pullbackComp`. -/
theorem isZero_nested {Y Z : Scheme.{u}} (f : X ⟶ S) (j : Y ⟶ X) (i : Z ⟶ Y)
    (F : X.Modules) (n : ℤ)
    (h : IsZero (((Scheme.Modules.pushforward ((i ≫ j) ≫ f)).rightDerivedPlus n).obj
      ((Scheme.Modules.pullback (i ≫ j)).obj F))) :
    IsZero (((Scheme.Modules.pushforward (i ≫ j ≫ f)).rightDerivedPlus n).obj
      ((Scheme.Modules.pullback i).obj ((Scheme.Modules.pullback j).obj F))) := by
  simp only [Category.assoc] at h
  exact IsZero.of_iso h
    (((Scheme.Modules.pushforward (i ≫ j ≫ f)).rightDerivedPlus n).mapIso
      ((Scheme.Modules.pullbackComp i j).app F))

section Step

attribute [local instance 2000] CategoryTheory.Abelian.hasBinaryBiproducts

/-- **The inductive step, with the two opens of the source given explicitly.** For `A`, `B` opens
covering the source of `j`, vanishing of the higher direct images of the restrictions of `j^* F`
along `A.ι ≫ j ≫ f` and `B.ι ≫ j ≫ f` in degree `m + 1` and along `(A ⊓ B).ι ≫ j ≫ f` in degree
`m` gives vanishing of `R ᵐ⁺¹ (j ≫ f)_* (j^* F)`.

Because `A` and `B` cover the *whole* of the source, the relative Mayer–Vietoris sequence of
[Stacks, Tag 01EC] applies in the form in which it is formalized, whose cover hypothesis is
`Set.range iU ∪ Set.range iV = Set.univ`. -/
theorem isZero_succ_of_cover (f : X ⟶ S) (F : X.Modules) {Y : Scheme.{u}} (j : Y ⟶ X)
    (A B : Y.Opens) (hcover : A ⊔ B = ⊤) (m : ℤ)
    (hA : IsZero (((Scheme.Modules.pushforward (A.ι ≫ j ≫ f)).rightDerivedPlus (m + 1)).obj
      ((Scheme.Modules.pullback A.ι).obj ((Scheme.Modules.pullback j).obj F))))
    (hB : IsZero (((Scheme.Modules.pushforward (B.ι ≫ j ≫ f)).rightDerivedPlus (m + 1)).obj
      ((Scheme.Modules.pullback B.ι).obj ((Scheme.Modules.pullback j).obj F))))
    (hI : IsZero (((Scheme.Modules.pushforward ((A ⊓ B).ι ≫ j ≫ f)).rightDerivedPlus m).obj
      ((Scheme.Modules.pullback (A ⊓ B).ι).obj ((Scheme.Modules.pullback j).obj F)))) :
    IsZero (((Scheme.Modules.pushforward (j ≫ f)).rightDerivedPlus (m + 1)).obj
      ((Scheme.Modules.pullback j).obj F)) := by
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
  exact isZero_of_mvSequence MV ((Scheme.Modules.pullback j).obj F) m hI
    (isZero_biprod_obj _ _ _ hA hB)

end Step

/-! ### The induction predicate -/

/-- The property of an open `U` of `X` that drives the proof of [Stacks, Tag 01XJ] part (2):
there is **one** integer `n` such that for every open immersion `j` with image `U`, every
quasi-coherent `F` on `X` and every `p ≥ n`, the higher direct image `R ᵖ (j ≫ f)_* (j^* F)`
vanishes.

The existential is inside, so that the induction principle of [Stacks, Tag 08DR] — which
quantifies over a property of opens — produces the bound along with the vanishing; and the
quantifier over `F` is inside the existential, so that the bound is uniform in `F`. -/
def VanishImage (f : X ⟶ S) (U : X.Opens) : Prop :=
  ∃ n : ℤ, ∀ ⦃Y : Scheme.{u}⦄ (j : Y ⟶ X), IsOpenImmersion j → Set.range j.base = U →
    ∀ F : X.Modules, F.IsQuasicoherent → ∀ p : ℤ, n ≤ p →
      IsZero (((Scheme.Modules.pushforward (j ≫ f)).rightDerivedPlus p).obj
        ((Scheme.Modules.pullback j).obj F))

/-- **The base case, with bound `1`.** Over an affine base, an open immersion whose image is an
affine open has affine source, so `j ≫ f` is an affine morphism and [Stacks, Tag 01XC] gives the
vanishing in every positive degree. -/
theorem vanishImage_of_isAffineOpen (f : X ⟶ S) [IsAffine S] (U : X.Opens)
    (hU : IsAffineOpen U) : VanishImage f U := by
  refine ⟨1, fun Y j hj hrange F hF p hp => ?_⟩
  have hRange : j.opensRange = U := SetLike.coe_injective hrange
  have : IsAffine j.opensRange.toScheme := by
    rw [hRange]
    exact hU
  have : IsAffine Y := IsAffine.of_isIso j.isoOpensRange.hom
  have : IsAffineHom (j ≫ f) := isAffineHom_of_isAffine _
  have : ((Scheme.Modules.pullback j).obj F).IsQuasicoherent :=
    Stacks.AlgebraicGeometry.AffineBaseChange.isQuasicoherent_pullback_of_isOpenImmersion
      j F
  exact HigherDirectImageAffine.isZero_higherDirectImage_of_pos (j ≫ f) _ p
    (by omega)

/-- **The inductive step in the form the induction principle wants.** The bound for `U ⊔ V` is one
more than the maximum of the bounds for `U`, `V` and `U ⊓ V`: in degree `p = m + 1` the sequence
consumes `U` and `V` in degree `m + 1` and `U ⊓ V` in degree `m`. -/
theorem vanishImage_sup (f : X ⟶ S) (U V : X.Opens)
    (hU : VanishImage f U) (hV : VanishImage f V) (hI : VanishImage f (U ⊓ V)) :
    VanishImage f (U ⊔ V) := by
  obtain ⟨nU, hnU⟩ := hU
  obtain ⟨nV, hnV⟩ := hV
  obtain ⟨nW, hnW⟩ := hI
  refine ⟨max (max nU nV) nW + 1, fun Y j hj hrange F hF p hp => ?_⟩
  obtain ⟨m, rfl⟩ : ∃ m : ℤ, p = m + 1 := ⟨p - 1, by omega⟩
  have hRange : j.opensRange = U ⊔ V := SetLike.coe_injective hrange
  have hAB : j ⁻¹ᵁ U ⊔ j ⁻¹ᵁ V = ⊤ := by
    ext y
    refine ⟨fun _ => trivial, fun _ => ?_⟩
    have hy : j.base y ∈ (U : X.Opens) ⊔ V := by
      have hmem : j.base y ∈ Set.range j.base := ⟨y, rfl⟩
      rwa [hrange] at hmem
    simpa using hy
  refine isZero_succ_of_cover f F j (j ⁻¹ᵁ U) (j ⁻¹ᵁ V) hAB m
    (isZero_nested f j (j ⁻¹ᵁ U).ι F (m + 1)
      (hnU _ inferInstance
        (Tag01XJQcohInduction.range_preimage_ι_comp j (U ⊔ V) U hRange le_sup_left) F hF _
          (by omega)))
    (isZero_nested f j (j ⁻¹ᵁ V).ι F (m + 1)
      (hnV _ inferInstance
        (Tag01XJQcohInduction.range_preimage_ι_comp j (U ⊔ V) V hRange le_sup_right) F hF _
          (by omega)))
    ?_
  rw [Tag01XJQcohInduction.preimage_inf]
  exact isZero_nested f j (j ⁻¹ᵁ (U ⊓ V)).ι F m
    (hnW _ inferInstance
      (Tag01XJQcohInduction.range_preimage_ι_comp j (U ⊔ V) (U ⊓ V) hRange
        (inf_le_left.trans le_sup_left)) F hF _ (by omega))

/-! ### The theorem -/

/-- **The induction, run.** Over an affine base `S`, for `f` quasi-compact and quasi-separated,
`VanishImage f` holds at `⊤`: this is [Stacks, Tag 08DR] applied to the base case
`vanishImage_of_isAffineOpen` and the Mayer–Vietoris step `vanishImage_sup`. -/
theorem vanishImage_top (f : X ⟶ S) [IsAffine S] [QuasiCompact f] [QuasiSeparated f] :
    VanishImage f ⊤ :=
  CompactOpenInduction.top_of_qcqs_over_affine (P := VanishImage f)
    (fun U hU => vanishImage_of_isAffineOpen f U hU)
    (fun U V _ _ hU hV hI => vanishImage_sup f U V hU hV hI) f

/-- **[Stacks, Tag 01XJ] part (2) over an affine base.** Instantiating `VanishImage f ⊤` at the
identity open immersion `𝟙 X`, whose image is all of `X`. -/
theorem exists_isZero_rightDerived_pushforward_of_isAffine (f : X ⟶ S) [IsAffine S] [QuasiCompact f]
    [QuasiSeparated f] :
    ∃ n : ℤ, ∀ p : ℤ, n ≤ p → ∀ F : X.Modules, F.IsQuasicoherent →
      IsZero (((Scheme.Modules.pushforward f).rightDerivedPlus p).obj F) := by
  obtain ⟨n, hn⟩ := vanishImage_top f
  refine ⟨n, fun p hp F hF => ?_⟩
  have h := hn (𝟙 X) inferInstance (by simp) F hF p hp
  simp only [Category.id_comp] at h
  exact IsZero.of_iso h
    (((Scheme.Modules.pushforward f).rightDerivedPlus p).mapIso
      ((Scheme.Modules.pullbackId X).app F).symm)

/-- **Stacks Project, Tag 01XJ (uniform_vanishing).** Let `f : X ⟶ S` be a quasi-compact and
quasi-separated morphism of schemes with `S` quasi-compact.  Then there is an integer `n`,
depending only on `f`, such that `R ᵖ f_* F = 0` for every `p ≥ n` and every quasi-coherent
`𝒪_X`-module `F`.

`S` is covered by finitely many affine opens `B j` (`exists_fin_affineOpen_cover`), each
`f ∣_ B j` is again quasi-compact and quasi-separated with affine target, so
`exists_isZero_rightDerived_pushforward_of_isAffine` supplies a bound `n j`; the bound is
`⨆ j, (n j).toNat`.  Above it every restriction of `R ᵖ f_* F` to a `B j` vanishes — by
[Stacks, Tag 01E5] for schemes, `higherDirectImageRestrictObjIso` — and vanishing is local,
`isZero_of_isZero_restrict`. -/
@[stacks 01XJ "uniform_vanishing",
  ega "IV 1.7.21" "vanishing bound",
  ega "III 1.4.12" "existence of r"]
theorem exists_isZero_rightDerived_pushforward (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f]
    [CompactSpace S] :
    ∃ n : ℤ, ∀ (p : ℤ), n ≤ p → ∀ (F : X.Modules) [F.IsQuasicoherent],
      IsZero (((Scheme.Modules.pushforward f).rightDerivedPlus p).obj F) := by
  classical
  obtain ⟨m, B, hBaff, hBcover⟩ := exists_fin_affineOpen_cover S
  have hbound : ∀ j : Fin m, ∃ n : ℤ, ∀ p : ℤ, n ≤ p →
      ∀ G : (f ⁻¹ᵁ B j : X.Opens).toScheme.Modules, G.IsQuasicoherent →
        IsZero (((Scheme.Modules.pushforward (f ∣_ B j)).rightDerivedPlus p).obj G) := by
    intro j
    have : IsAffine (B j).toScheme := hBaff j
    exact exists_isZero_rightDerived_pushforward_of_isAffine (f ∣_ B j)
  choose n hn using hbound
  refine ⟨((Finset.univ.sup fun j => (n j).toNat : ℕ) : ℤ), fun p hp F hF => ?_⟩
  obtain ⟨q, rfl⟩ : ∃ q : ℕ, p = (q : ℤ) :=
    ⟨p.toNat, (Int.toNat_of_nonneg (le_trans (Int.natCast_nonneg _) hp)).symm⟩
  refine isZero_of_isZero_restrict B hBcover _ fun j => ?_
  have hnj : n j ≤ (q : ℤ) := by
    refine le_trans (Int.self_le_toNat (n j)) ?_
    exact_mod_cast le_trans (Finset.le_sup (f := fun k => (n k).toNat) (Finset.mem_univ j))
      (by exact_mod_cast hp)
  exact IsZero.of_iso (hn j (q : ℤ) hnj _ inferInstance)
    (ProjectiveCoherentImage.higherDirectImageRestrictObjIso f (B j) F q).symm

end Stacks.AlgebraicGeometry.Tag01XJUniformVanishing

end
