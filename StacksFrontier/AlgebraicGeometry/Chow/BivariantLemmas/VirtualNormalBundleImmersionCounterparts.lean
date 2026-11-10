module

public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.VirtualNormalCommutingEveryClass
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.CompletedIdentity
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.CompletedExcessIntersectionFormula
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.CompletedRestrictionComposite
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.VirtualNormalCapCohenMacaulay
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.CompletedVirtualNormalSubbundle
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.ExcessIntersectionFormula
public import StacksFrontier.AlgebraicGeometry.Chow.CoherentCycle.MaximalDeltaDimension
public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.CapRuleTwist
public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.CapRuleFlatGeneral
public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.FirstChernClassCommute
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.RegularImmersion.SmoothPermanence
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.VirtualNormalBundleImmersionClass
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.VirtualNormalSubbundleClass
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantClassCopy

/-!
# The lemmas on virtual normal bundles, for immersions

Stacks 0FBQ extends the class `c(Z ⟶ X, 𝒩)` of Stacks 0FBK from closed immersions to immersions
`i : Z ⟶ X`: for an open subscheme `U ⊆ X` through which `i` factors as a closed immersion
`i' : Z ⟶ U`, it sets `c(Z ⟶ X, 𝒩) = c(Z ⟶ U, 𝒩) ∘ (U ⟶ X)^*`
(`Stacks.Chow.virtualNormalGysinClassOfOpen`), and asserts that all of the lemmas of the section
have immediate counterparts for this construction. This file proves them, each from the lemma for
the closed immersion `i'`, the definition, and the associativity of composition (Stacks 0B75).

Where the source's lemma is for a virtual normal sheaf of arbitrary rank, the counterpart
registered under Stacks 0FBQ is the one for the class `c(Z ⟶ X, 𝒩) ∈ A^*(Z ⟶ X)^∧` of arbitrary
rank; the constant-rank counterparts in this file are the steps towards it and are not registered.

## Main results

* `Stacks.Chow.virtualNormalGysinClassOfOpen_eq_virtualNormalGysinClass` — for a closed immersion
  the construction of Stacks 0FBQ (3) is the class of Stacks 0FBK, so every lemma on the latter
  holds for the former.
* `Stacks.Chow.virtualNormalGysinClassOfOpen_commutesWithEveryClass`,
  `Stacks.Chow.virtualNormalGysinClassOfOpen_bivariantCommute` — the counterpart of Stacks 0FBP:
  `c(Z ⟶ X, 𝒩)` commutes with every bivariant class.
* `Stacks.Chow.bivariantTransport_bivariantRestriction_virtualNormalGysinClassOfOpen`,
  `Stacks.Chow.virtualNormalGysinClassOfOpen_cap_baseChange` — the counterpart of the base-change
  clause of Stacks 0FBK at constant rank: the restriction of `c(Z ⟶ X, 𝒩)` along `X' ⟶ X` is
  `c(Z' ⟶ X', g^*𝒩)`. The counterparts at arbitrary rank, of the base-change clause of Stacks 0FBK
  and of Stacks 0FV7, are in
  `StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.CompletedVirtualNormalImmersionBaseChange`.
* `Stacks.Chow.virtualNormalGysinClassOfOpen_cap_fundamentalChowClass_excess` — the counterpart
  of Stacks 0FBM, the excess intersection formula
  `c(Z ⟶ X, 𝒩) ∩ [Y]_n = c_top(ℰ) ∩ [Z ×_X Y]_{n - r}`.
* `Stacks.Chow.completedVirtualNormalGysinClassOfOpen_cap_fundamentalChowClass_excess` — the
  counterpart of Stacks 0FBM when the virtual normal bundle has unbounded rank, degree by degree.
* `Stacks.Chow.virtualNormalGysinClassOfOpen_cap_fundamentalChowClass_of_isCohenMacaulayLocalRing`
  — the counterpart of Stacks 0FEA, `c(Z ⟶ X, 𝒩) ∩ [Y]_n = [Z ×_X Y]_{n - r}`.
* `Stacks.Chow.completedVirtualNormalGysinClassOfOpen_eq_of_isTopChernComposition` — the
  counterpart of Stacks 0FBL in `A^*(Z ⟶ X)^∧`, at arbitrary rank.
* `Stacks.Chow.virtualNormalGysinClassOfOpen_eq_of_isTopChernComposition` — the counterpart of
  Stacks 0FBL: for `0 ⟶ 𝒩' ⟶ 𝒩 ⟶ ℰ ⟶ 0` with `σ` factoring through `σ'`,
  `c(Z ⟶ X, 𝒩) = c_top(ℰ) ∘ c(Z ⟶ X, 𝒩')`.

## References

* [Stacks Project, Tag 0FBQ](https://stacks.math.columbia.edu/tag/0FBQ)
* [Stacks Project, Tag 0FBJ](https://stacks.math.columbia.edu/tag/0FBJ)
* [Stacks Project, Tag 0FBK](https://stacks.math.columbia.edu/tag/0FBK)
* [Stacks Project, Tag 0FBL](https://stacks.math.columbia.edu/tag/0FBL)
* [Stacks Project, Tag 0FBM](https://stacks.math.columbia.edu/tag/0FBM)
* [Stacks Project, Tag 0FBP](https://stacks.math.columbia.edu/tag/0FBP)
* [Stacks Project, Tag 0FEA](https://stacks.math.columbia.edu/tag/0FEA)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open RingedSpaceModuleAdjunction Stacks.AlgebraicGeometry.ReflexiveModules
open Stacks.AlgebraicGeometry.RegularIdealSheaf

universe u

namespace Stacks.Chow

variable (C : ChowSituation.{u}) {Z X : Scheme.{u}} (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ]
  (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (i : Z ⟶ X) [IsImmersion i] (hi : i ≫ sX = sZ)
  (U : X.Opens) (i' : Z ⟶ U.toScheme) [IsClosedImmersion i'] (hU : i' ≫ U.ι = i)

/-! ### The counterpart of Stacks 0FBJ -/

/- Stacks 0FBJ is formalized for immersions (`Stacks.Chow.VirtualNormalBundle.baseChange`): for a
cartesian square whose horizontal arrows are immersions, `g^*𝒩` is a virtual normal bundle for
`Z' ⟶ X'`. -/
add_to_stacks 0FBQ "(3), counterparts: the counterpart of Lemma 0FBJ, g^*𝒩 is a virtual normal \
bundle for Z' → X' for a cartesian square whose horizontal arrows are immersions"
  VirtualNormalBundle.baseChange

/-! ### Open factors and base change -/

section OpenFactorBaseChange

variable {Z X Z' Y : Scheme.{u}} {i : Z ⟶ X} [IsImmersion i] {i₂ : Z' ⟶ Y} [IsImmersion i₂]
  {g' : Z' ⟶ Z} {g : Y ⟶ X} {U : X.Opens} {iU : Z ⟶ U.toScheme} [IsImmersion iU]
  (hU : iU ≫ U.ι = i) {V : Y.Opens} {iV : Z' ⟶ V.toScheme} [IsImmersion iV] (hV : iV ≫ V.ι = i₂)
  {h : V.toScheme ⟶ U.toScheme}

/-- **The comparison maps of conormal sheaves of Stacks 0473 commute with
`𝒞_{Z/X} ≅ 𝒞_{Z/U}`.** For a commutative square `i₂ ≫ g = g' ≫ i` of immersions and
factorizations `i = iU ≫ ι_U`, `i₂ = iV ≫ ι_V` through opens with `h : V ⟶ U` over `g`, the
comparison map `g'^* 𝒞_{Z/U} ⟶ 𝒞_{Z'/V}` of the square of closed factors is that of the original
square, `g'^* 𝒞_{Z/X} ⟶ 𝒞_{Z'/Y}`, read through the two identifications: both composites are the
comparison map of the square `iV ≫ (h ≫ ι_U) = g' ≫ i` (Stacks 01R4, for stacked squares). -/
theorem immersionConormalSheafMap_openFactor (hh : h ≫ U.ι = V.ι ≫ g)
    (commV : iV ≫ h = g' ≫ iU) (comm : i₂ ≫ g = g' ≫ i) :
    (modulePullback g'.toLRSHom.toShHom).map (immersionConormalSheafFactorIso U iU hU).hom ≫
        Stacks.Immersion.immersionConormalSheafMap iV iU g' h
          (Stacks.Immersion.toShHom_square commV) =
      Stacks.Immersion.immersionConormalSheafMap i₂ i g' g (Stacks.Immersion.toShHom_square comm) ≫
        (immersionConormalSheafFactorIso V iV hV).hom := by
  -- `𝒞_{Z/X} ≅ 𝒞_{Z/U}` and `𝒞_{Z'/Y} ≅ 𝒞_{Z'/V}` are conormal maps
  have hFU : (immersionConormalSheafFactorIso U iU hU).hom =
      (modulePullbackId Z.toRingedSpace).inv.app _ ≫
        Stacks.Immersion.immersionConormalSheafMap iU i (𝟙 Z) U.ι
          (Stacks.Immersion.toShHom_square (hU.trans (Category.id_comp i).symm)) := by
    rw [immersionConormalSheafMap_id_ι U iU hU, Iso.inv_hom_id_app_assoc]
  have hFV : (immersionConormalSheafFactorIso V iV hV).hom =
      (modulePullbackId Z'.toRingedSpace).inv.app _ ≫
        Stacks.Immersion.immersionConormalSheafMap iV i₂ (𝟙 Z') V.ι
          (Stacks.Immersion.toShHom_square (hV.trans (Category.id_comp i₂).symm)) := by
    rw [immersionConormalSheafMap_id_ι V iV hV, Iso.inv_hom_id_app_assoc]
  have c1 := Stacks.Immersion.immersionConormalSheafMap_comp iV iU i g' h commV (𝟙 Z) U.ι
    (hU.trans (Category.id_comp i).symm)
  have c2 := Stacks.Immersion.immersionConormalSheafMap_comp iV i₂ i (𝟙 Z') V.ι
    (hV.trans (Category.id_comp i₂).symm) g' g comm
  have hci : ∀ {A B : Scheme.{u}} (j : A ⟶ B)
      (M : SheafOfModules.{u} (structureSheafRing B.toRingedSpace)),
      (modulePullbackComp j.toLRSHom.toShHom (Scheme.Hom.toLRSHom (𝟙 B)).toShHom).hom.app M =
        (modulePullback j.toLRSHom.toShHom).map ((modulePullbackId B.toRingedSpace).inv.app M) :=
    fun j M ↦ modulePullbackComp_comp_id_hom_app j.toLRSHom.toShHom M
  have hic : ∀ {A B : Scheme.{u}} (j : A ⟶ B)
      (M : SheafOfModules.{u} (structureSheafRing B.toRingedSpace)),
      (modulePullbackComp (Scheme.Hom.toLRSHom (𝟙 A)).toShHom j.toLRSHom.toShHom).hom.app M =
        (modulePullbackId A.toRingedSpace).inv.app ((modulePullback j.toLRSHom.toShHom).obj M) := by
    intro A B j M
    exact (Iso.hom_eq_inv ((modulePullbackComp (Scheme.Hom.toLRSHom (𝟙 A)).toShHom
      j.toLRSHom.toShHom).app M) ((modulePullbackId A.toRingedSpace).app _)).2
      (modulePullbackComp_id_inv_app j.toLRSHom.toShHom M).symm
  rw [hci] at c1
  rw [hic] at c2
  have hA := (congrArg (fun φ ↦ (modulePullback g'.toLRSHom.toShHom).map φ ≫
      Stacks.Immersion.immersionConormalSheafMap iV iU g' h
        (Stacks.Immersion.toShHom_square commV)) hFU).trans
    ((congrArg (· ≫ _) (Functor.map_comp _ _ _)).trans ((Category.assoc _ _ _).trans c1.symm))
  have hB := (congrArg (fun φ ↦ Stacks.Immersion.immersionConormalSheafMap i₂ i g' g
      (Stacks.Immersion.toShHom_square comm) ≫ φ) hFV).trans
    ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _)
      ((modulePullbackId Z'.toRingedSpace).inv.naturality _)).trans
      ((Category.assoc _ _ _).trans c2.symm)))
  refine hA.trans (Eq.trans ?_ hB.symm)
  have hL : ∀ (f : Z' ⟶ Z) (hf : f = g') (k : V.toScheme ⟶ X) (hk : k = V.ι ≫ g) (c c'),
      Stacks.Immersion.immersionConormalSheafMap iV i f k c ≍
        Stacks.Immersion.immersionConormalSheafMap iV i g' (V.ι ≫ g) c' := by
    rintro f rfl k rfl c c'
    rfl
  exact eq_of_heq ((hL _ (Category.comp_id g') _ hh _ (Stacks.Immersion.toShHom_square
    (Stacks.Immersion.square_comp (hV.trans (Category.id_comp i₂).symm) comm))).trans
    (hL _ (Category.id_comp g') _ rfl _ _).symm)

/-- **Reading a base change of a virtual normal bundle on open factors.** For a cartesian square
`i₂ ≫ g = g' ≫ i` of immersions and factorizations `i = iU ≫ ι_U`, `i₂ = iV ≫ ι_V` through opens
with `h : V ⟶ U` over `g`, the base change `g'^*𝒩` read along `iV` and the base change along `h`
of `𝒩` read along `iU` carry the same surjection onto `𝒞_{Z'/V}`. -/
theorem VirtualNormalBundle.toOpenFactor_baseChange_surjection (N : VirtualNormalBundle i)
    (sq : IsPullback i₂ g' g i) (hh : h ≫ U.ι = V.ι ≫ g) (sqV : IsPullback iV g' h iU) :
    ((N.baseChange i i₂ g' g sq).toOpenFactor hV).surjection =
      ((N.toOpenFactor hU).baseChange iU iV g' h sqV).surjection := by
  rw [VirtualNormalBundle.toOpenFactor_surjection, VirtualNormalBundle.baseChange_surjection,
    VirtualNormalBundle.baseChange_surjection, VirtualNormalBundle.toOpenFactor_surjection]
  refine (Category.assoc _ _ _).trans (congrArg (_ ≫ ·) ((Category.assoc _ _ _).trans
    ((congrArg (_ ≫ ·) (immersionConormalSheafMap_openFactor hU hV hh sqV.w sq.w).symm).trans
      ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) (Functor.map_comp _ _ _).symm)))))

omit [IsImmersion i] [IsImmersion i₂] [IsImmersion iU] in
/-- Two virtual normal bundles for the same immersion with the same module and the same
surjection are equal. -/
theorem VirtualNormalBundle.ext_of_surjection_heq {N₁ N₂ : VirtualNormalBundle iV}
    (hb : N₁.bundle = N₂.bundle) (hs : N₁.surjection ≍ N₂.surjection) : N₁ = N₂ := by
  obtain ⟨b₁, _, s₁, _⟩ := N₁
  obtain ⟨b₂, _, s₂, _⟩ := N₂
  simp only at hb hs
  subst hb
  cases hs
  rfl

/-- **Reading a base change of a virtual normal bundle on open factors**, as an equality of
virtual normal bundles: the two have the same module `g'^*𝒩` and the same surjection
(`Stacks.Chow.VirtualNormalBundle.toOpenFactor_baseChange_surjection`). -/
theorem VirtualNormalBundle.toOpenFactor_baseChange (N : VirtualNormalBundle i)
    (sq : IsPullback i₂ g' g i) (hh : h ≫ U.ι = V.ι ≫ g) (sqV : IsPullback iV g' h iU) :
    (N.baseChange i i₂ g' g sq).toOpenFactor hV = (N.toOpenFactor hU).baseChange iU iV g' h sqV :=
  VirtualNormalBundle.ext_of_surjection_heq rfl
    (heq_of_eq (VirtualNormalBundle.toOpenFactor_baseChange_surjection hU hV N sq hh sqV))

end OpenFactorBaseChange

/-! ### The closed case -/

section Closed

/-- **The flat pullback along the identity is the unit.** The class `(𝟙 X)^* ∈ A^0(X ⟶ X)` of
Stacks 0B78 is the unit `1 ∈ A^0(X)`: both cap by pushing forward along `T ≅ X ×_X T`. -/
theorem flatPullbackBivariantClassOfIsOpenImmersionOfInvertible_id_heq :
    flatPullbackBivariantClassOfIsOpenImmersionOfInvertible C sX sX (𝟙 X) (Category.id_comp sX) ≍
      bivariantIdentityClassOfInvertible C sX := by
  refine BivariantClass.heq_of_congrHom_cap_heq rfl (by simp) _ _ fun t _ k α ↦ ?_
  refine (chowPushforwardOfIso_heq_of_eq_id _ (by apply pullback.hom_ext <;> simp) _ _).trans ?_
  refine (flatPullbackBivariantCap_heq_chowGroupRestrict C sX sX (𝟙 X) (Category.id_comp sX) t k
    α).trans ?_
  refine HEq.trans ?_ (bivariantIdentityClassOfInvertible_cap_heq C sX t k α).symm
  rw [chowGroupRestrict_of_isIso]
  exact heq_of_eq (chowPushforwardOfIso_congr_apply C _ _ _ _ rfl _ _ k α)

/-- **For a closed immersion the construction of Stacks 0FBQ (3) is that of Stacks 0FBK.** If
`i : Z ⟶ X` is a closed immersion, then for every open `U ⊆ X` through which `i` factors as a
closed immersion `i' : Z ⟶ U`,

  `c(Z ⟶ U, 𝒩) ∘ (U ⟶ X)^* = c(Z ⟶ X, 𝒩)`.

By the base-change clause of Stacks 0FBK along `U ⟶ X`, `c(Z ⟶ U, 𝒩)` is the restriction of
`c(Z ⟶ X, 𝒩)` to `U`, so `c(Z ⟶ U, 𝒩) ∘ (U ⟶ X)^* = c(Z ⟶ X, 𝒩) ∘ (𝟙 X)^*`, and `(𝟙 X)^* = 1`. In
particular every lemma on the class of Stacks 0FBK applies to the class of Stacks 0FBQ (3) of a
closed immersion. -/
theorem virtualNormalGysinClassOfOpen_eq_virtualNormalGysinClass [IsClosedImmersion i]
    (𝒩 : VirtualNormalBundle i) (r : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} 𝒩.bundle r] :
    virtualNormalGysinClassOfOpen C sZ sX i hi U i' hU 𝒩 r =
      virtualNormalBundleClass C sZ sX i hi 𝒩 r := by
  have hi' := openFactor_comp_structureMorphism C sZ sX i hi hU
  refine eq_of_heq ((BivariantClass.copy_heq _ _ _ _ _).trans ?_)
  refine (openImmersionComposite_heq_of_isOpenRestriction C sZ sX (U.ι ≫ sX) sX i i' (𝟙 X) U.ι
    U.ι hi hi' (Category.id_comp sX) rfl rfl hU (r : ℤ) (Category.comp_id U.ι) _ _
    (isOpenRestriction_of_bivariantTransport_bivariantRestriction_heq rfl hU _ _ _ _ hi'
      (heq_of_eq (bivariantTransport_bivariantRestriction_virtualNormalGysinClass_toOpenFactor C sZ
        sX hi hU 𝒩 r sZ hi')))).symm.trans ?_
  exact (bivariantCompositeOfInvertible_heq_congr rfl rfl rfl (by simp) HEq.rfl
    (flatPullbackBivariantClassOfIsOpenImmersionOfInvertible_id_heq C sX)).trans
    (bivariantCompositeOfInvertible_bivariantIdentityClassOfInvertible C sZ sX i hi (r : ℤ) _)

end Closed

/-! ### The counterpart of Stacks 0FBP -/

section Commute

variable (𝒩 : VirtualNormalBundle i) (r : ℕ)
  [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} 𝒩.bundle r]

/-- **The counterpart of Stacks 0FBP for immersions, for every class at once.** The class
`c(Z ⟶ X, 𝒩) = c(Z ⟶ U, 𝒩) ∘ (U ⟶ X)^*` of a virtual normal bundle of constant rank for an
immersion commutes with every bivariant class: both factors do, by Stacks 0FBP for the closed
immersion `Z ⟶ U` and by Stacks 0FF6 for the flat pullback `(U ⟶ X)^*`, and so does their
composite. -/
theorem virtualNormalGysinClassOfOpen_commutesWithEveryClass :
    (virtualNormalGysinClassOfOpen C sZ sX i hi U i' hU 𝒩 r).CommutesWithEveryClass :=
  (BivariantClass.commutesWithEveryClass_copy _ _ _ _ _).2
    (commutesWithEveryClass_bivariantCompositeOfInvertible _ _ _ _ _ _ _
      (virtualNormalBundleClass_commutesWithEveryClass C sZ (U.ι ≫ sX) i'
        (openFactor_comp_structureMorphism C sZ sX i hi hU) r (𝒩.toOpenFactor hU))
      (commutesWithEveryClass_flatPullbackBivariantClassOfIsOpenImmersionOfInvertible rfl))

/-- **The counterpart of Stacks 0FBP for immersions.** Let `i : Z ⟶ X` be an immersion with a
virtual normal bundle `𝒩` of constant rank `r`, let `g : Y ⟶ X` be locally of finite type and let
`c ∈ A^p(Y ⟶ X)`. Then `c` and `c(Z ⟶ X, 𝒩)` commute (Stacks 0FA2). -/
theorem virtualNormalGysinClassOfOpen_bivariantCommute {Y : Scheme.{u}} (g : Y ⟶ X)
    [LocallyOfFiniteType g] (p : ℤ)
    (c : BivariantClass C (gysinSystemOfInvertible C) (g ≫ sX) sX g rfl p) :
    BivariantCommute C (gysinSystemOfInvertible C) sX i g (r : ℤ) p
      (virtualNormalGysinClassOfOpen C (i ≫ sX) sX i rfl U i' hU 𝒩 r) c :=
  virtualNormalGysinClassOfOpen_commutesWithEveryClass C (i ≫ sX) sX i rfl U i' hU 𝒩 r g p c

end Commute

/-! ### The counterpart of Stacks 0FBL -/

section TopChern

variable (𝒩 𝒩' : VirtualNormalBundle i) (m' e : ℕ)
  [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} 𝒩'.bundle m']
  [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} 𝒩.bundle (m' + e)]
  (Eb : Z.Modules) [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} Eb e]
  (inc : 𝒩'.bundle ⟶ 𝒩.bundle) (pr : 𝒩.bundle ⟶ Eb)

/-- **The counterpart of Stacks 0FBL for immersions.** Let `i : Z ⟶ X` be an immersion with a
virtual normal bundle `𝒩`, and let `0 ⟶ 𝒩' ⟶ 𝒩 ⟶ ℰ ⟶ 0` be a short exact sequence of finite
locally free `𝒪_Z`-modules of constant ranks `m'`, `m' + e` and `e` such that the surjection
`σ : 𝒩^∨ ⟶ 𝒞_{Z/X}` factors as `σ' ∘ (𝒩^∨ ⟶ (𝒩')^∨)` through that of `𝒩'`. Then

  `c(Z ⟶ X, 𝒩) = c_e(ℰ) ∘ c(Z ⟶ X, 𝒩')`

in `A^{m' + e}(Z ⟶ X)`, both classes built from the same open `U`.

By Stacks 0FBL for the closed immersion `Z ⟶ U`, `c(Z ⟶ U, 𝒩) = c_e(ℰ) ∘ c(Z ⟶ U, 𝒩')`, and
composing with `(U ⟶ X)^*` the associativity of Stacks 0B75 gives
`(c_e(ℰ) ∘ c(Z ⟶ U, 𝒩')) ∘ (U ⟶ X)^* = c_e(ℰ) ∘ (c(Z ⟶ U, 𝒩') ∘ (U ⟶ X)^*)`. -/
theorem virtualNormalGysinClassOfOpen_eq_of_isTopChernComposition
    (w : inc ≫ pr = 0) (hseq : (ShortComplex.mk inc pr w).ShortExact)
    (hsigma : dualMap inc ≫ 𝒩'.surjection = 𝒩.surjection) :
    virtualNormalGysinClassOfOpen C sZ sX i hi U i' hU 𝒩 (m' + e) =
      BivariantClass.copy C (gysinSystemOfInvertible C) sZ sX (Category.id_comp i)
        (comp_comp_structureMorphism_eq (Category.id_comp sZ) hi) hi (by push_cast; ring)
        (bivariantCompositeOfInvertible C sZ sZ sX (𝟙 Z) i (Category.id_comp sZ) hi (e : ℤ)
          (m' : ℤ) (GenuineChern.chernClass C sZ Eb e (Fin.last e))
          (virtualNormalGysinClassOfOpen C sZ sX i hi U i' hU 𝒩' m')) := by
  have hi' := openFactor_comp_structureMorphism C sZ sX i hi hU
  -- Stacks 0FBL for the closed immersion `Z ⟶ U`
  have hL := virtualNormalBundleClass_eq_of_isTopChernComposition C sZ (U.ι ≫ sX) i' hi'
    (𝒩.toOpenFactor hU) (𝒩'.toOpenFactor hU) m' e Eb inc pr w hseq
    ((Category.assoc _ _ _).symm.trans
      (congrArg (· ≫ (immersionConormalSheafFactorIso U i' hU).hom) hsigma))
  refine eq_of_heq ?_
  refine (BivariantClass.copy_heq _ _ _ _ _).trans ?_
  refine HEq.trans ?_ (BivariantClass.copy_heq _ _ _ _ _).symm
  refine (bivariantCompositeOfInvertible_heq_congr (Category.id_comp i').symm rfl
    (by push_cast; ring) rfl
    ((heq_of_eq hL).trans (BivariantClass.copy_heq _ _ _ _ _)) HEq.rfl).trans ?_
  refine (bivariantCompositeOfInvertible_assoc C sZ sZ (U.ι ≫ sX) sX (𝟙 Z) i' U.ι
    (Category.id_comp sZ) hi' rfl (e : ℤ) (m' : ℤ) (-((0 : ℕ) : ℤ)) _ _ _).trans ?_
  exact bivariantCompositeOfInvertible_heq_congr rfl hU rfl (by simp) HEq.rfl
    (BivariantClass.copy_heq _ _ _ _ _).symm

end TopChern

/-! ### Factoring through a preimage open -/

section PreimageFactor

/-- A morphism `i₂ : Z' ⟶ Y` with `i₂ ≫ g = g' ≫ i' ≫ ι_U` lands in the open `g⁻¹(U)`. -/
theorem range_base_subset_range_preimage_ι {Y Z' : Scheme.{u}} {g : Y ⟶ X} {i₂ : Z' ⟶ Y}
    {g' : Z' ⟶ Z} {U : X.Opens} {i' : Z ⟶ U.toScheme} (w : i₂ ≫ g = g' ≫ i' ≫ U.ι) :
    Set.range i₂.base ⊆ Set.range (g ⁻¹ᵁ U).ι.base := by
  rintro _ ⟨z, rfl⟩
  rw [Scheme.Opens.range_ι]
  change (i₂ ≫ g).base z ∈ U
  rw [w]
  exact ((g' ≫ i').base z).2

/-- For a cartesian square `i₂ ≫ g = g' ≫ i' ≫ ι_U`, the factor `Z' ⟶ g⁻¹(U)` of `i₂` and `g'`
form a cartesian square over `g|_U` and `i'`. -/
theorem isPullback_lift_morphismRestrict {Y Z' : Scheme.{u}} {g : Y ⟶ X} {i₂ : Z' ⟶ Y}
    {g' : Z' ⟶ Z} {U : X.Opens} {i' : Z ⟶ U.toScheme} (sq : IsPullback i₂ g' g (i' ≫ U.ι)) :
    IsPullback (IsOpenImmersion.lift (g ⁻¹ᵁ U).ι i₂ (range_base_subset_range_preimage_ι sq.w))
      g' (g ∣_ U) i' := by
  have hV := IsOpenImmersion.lift_fac (g ⁻¹ᵁ U).ι i₂ (range_base_subset_range_preimage_ι sq.w)
  have comm : IsOpenImmersion.lift (g ⁻¹ᵁ U).ι i₂ (range_base_subset_range_preimage_ι sq.w) ≫
      g ∣_ U = g' ≫ i' := by
    rw [← cancel_mono U.ι, Category.assoc, morphismRestrict_ι, ← Category.assoc, hV, sq.w,
      Category.assoc]
  exact IsPullback.of_right (by rwa [hV]) comm (isPullback_morphismRestrict g U).flip

/-- A cartesian square `i₂ ≫ g = g' ≫ i' ≫ ι_U` over a closed immersion `i'` gives a closed factor
`Z' ⟶ g⁻¹(U)` of `i₂`, cartesian over `g|_U` and `i'`. -/
private theorem exists_closedFactor_preimage {Y Z' : Scheme.{u}} {g : Y ⟶ X} {i₂ : Z' ⟶ Y}
    {g' : Z' ⟶ Z} {U : X.Opens} {i' : Z ⟶ U.toScheme} [IsClosedImmersion i']
    (sq : IsPullback i₂ g' g (i' ≫ U.ι)) :
    ∃ (iV : Z' ⟶ (g ⁻¹ᵁ U).toScheme) (_ : iV ≫ (g ⁻¹ᵁ U).ι = i₂)
      (_ : IsPullback iV g' (g ∣_ U) i'), IsClosedImmersion iV :=
  ⟨_, IsOpenImmersion.lift_fac _ _ _, isPullback_lift_morphismRestrict sq,
    MorphismProperty.of_isPullback (isPullback_lift_morphismRestrict sq).flip inferInstance⟩

/-- If `dim_δ(Y) ≤ n` then the open `g⁻¹(U)` of `Y` has `δ`-dimension at most `n` over `U`. -/
theorem schemeDeltaDimension_morphismRestrict_le {Y : Scheme.{u}} (g : Y ⟶ X)
    [LocallyOfFiniteType g] {n : ℤ} (hY : schemeDeltaDimension C (g ≫ sX) ≤ (n : EInt)) :
    schemeDeltaDimension C (g ∣_ U ≫ (U.ι ≫ sX)) ≤ (n : EInt) := by
  have H : schemeDeltaDimension C (𝟙 (g ⁻¹ᵁ U).toScheme ≫ ((g ⁻¹ᵁ U).ι ≫ (g ≫ sX))) ≤
      (n : EInt) :=
    schemeDeltaDimension_le_of_forall_relativeDimension_le C _ (𝟙 _) fun w ↦
      (relativeDimension_comp_isOpenImmersion C.dimensionFunction (g ⁻¹ᵁ U).ι (g ≫ sX)
        w).trans_le (relativeDimension_le_of_schemeDeltaDimension_le' C (g ≫ sX) hY _)
  convert H using 2
  rw [Category.id_comp, ← Category.assoc, morphismRestrict_ι, Category.assoc]

/-- An immersion `iV` whose composite with a smooth morphism is a regular immersion `i₂` is
itself a regular immersion. -/
theorem isRegularImmersion_of_comp_of_smooth_of_eq {Z' V Y : Scheme.{u}} (iV : Z' ⟶ V)
    (j : V ⟶ Y) [IsImmersion iV] [Smooth j] {i₂ : Z' ⟶ Y} [IsImmersion i₂] (h : iV ≫ j = i₂)
    (hreg : IsRegularImmersion i₂) : IsRegularImmersion iV := by
  subst h
  exact isRegularImmersion_of_comp_of_smooth iV j hreg

end PreimageFactor

/-! ### The counterpart of Stacks 0FBM -/

section Excess

variable (𝒩 : VirtualNormalBundle i) (r e : ℕ)
  [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} 𝒩.bundle (r + e)]

/-- **The counterpart of Stacks 0FBM for immersions, the excess intersection formula.** Let
`i : Z ⟶ X` be an immersion with a virtual normal bundle `𝒩` of constant rank `r + e`, and let
`g : Y ⟶ X` be locally of finite type such that the base change `i₂ : Z' = Z ×_X Y ⟶ Y` is a
regular immersion whose conormal sheaf `𝒞_{Z'/Y}` has constant rank `r`. Let `ℰ` be the excess
normal sheaf, `0 ⟶ ℰ^∨ ⟶ 𝒩^∨|_{Z'} ⟶ 𝒞_{Z'/Y} ⟶ 0`, of rank `e`. If `dim_δ(Y) ≤ n` then

  `c(Z ⟶ X, 𝒩) ∩ [Y]_n = c_top(ℰ) ∩ [Z']_{n - r}`

in `A_{n - (r + e)}(Z ×_X Y)`, with `c(Z ⟶ X, 𝒩) = c(Z ⟶ U, 𝒩) ∘ (U ⟶ X)^*`.

On `V = g⁻¹(U) ⊆ Y` the immersion `i₂` factors through a regular closed immersion
`Z' ⟶ V`, the base change of `Z ⟶ U` along `V ⟶ U`, with the same conormal sheaf and the same
excess normal sheaf, and `[Y]_n` restricts to `[V]_n`; so this is Stacks 0FBM for `Z ⟶ U`. -/
theorem virtualNormalGysinClassOfOpen_cap_fundamentalChowClass_excess {Y Z' : Scheme.{u}}
    (g : Y ⟶ X) [LocallyOfFiniteType g] (i₂ : Z' ⟶ Y) [IsImmersion i₂] (g' : Z' ⟶ Z)
    (sq : IsPullback i₂ g' g i) (sZ' : Z' ⟶ C.S) [LocallyOfFiniteType sZ']
    (hi₂ : i₂ ≫ (g ≫ sX) = sZ') (hreg : IsRegularImmersion i₂)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (conormalModule i₂) r]
    (n : ℤ) (hY : schemeDeltaDimension C (g ≫ sX) ≤ (n : EInt)) :
    haveI : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (𝒩.baseChange i i₂ g' g sq).bundle
        (r + e) :=
      isFiniteLocallyFreeOfRank_modulePullback g' 𝒩.bundle (r + e) inferInstance
    haveI := (𝒩.baseChange i i₂ g' g sq).isFiniteLocallyFreeOfRank_excessNormalSheaf_of_add r e
    (virtualNormalGysinClassOfOpen C sZ sX i hi U i' hU 𝒩 (r + e)).cap g n
        (fundamentalChowClass C (g ≫ sX) n) =
      chowPushforwardOfIso C sZ' (pullback.fst i g ≫ sZ) sq.flip.isoPullback.hom
        (isoPullback_hom_comp_structureMorphism C sZ sX sq hi sZ' hi₂) (n - ((r + e : ℕ) : ℤ))
        (chowGroupDegreeEquiv C sZ' (by push_cast; ring)
          (GenuineChern.chernCap C e sZ' (𝒩.baseChange i i₂ g' g sq).excessNormalSheaf
            (n - (r : ℤ)) (Fin.last e) (fundamentalChowClass C sZ' (n - (r : ℤ))))) := by
  have : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (𝒩.baseChange i i₂ g' g sq).bundle
      (r + e) :=
    isFiniteLocallyFreeOfRank_modulePullback g' 𝒩.bundle (r + e) inferInstance
  have := (𝒩.baseChange i i₂ g' g sq).isFiniteLocallyFreeOfRank_excessNormalSheaf_of_add r e
  subst hU
  have hi' := openFactor_comp_structureMorphism C sZ sX _ hi rfl
  -- the open `V = g⁻¹(U)` of `Y` and the closed factor `iV : Z' ⟶ V` of `i₂`
  obtain ⟨iV, hV, sqV, _⟩ := exists_closedFactor_preimage sq
  have hh : g ∣_ U ≫ U.ι = (g ⁻¹ᵁ U).ι ≫ g := morphismRestrict_ι g U
  have hregV := isRegularImmersion_of_comp_of_smooth_of_eq iV (g ⁻¹ᵁ U).ι hV hreg
  have : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (conormalModule iV) r :=
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso.{u, u, u}
      (immersionConormalSheafFactorIso (g ⁻¹ᵁ U) iV hV) inferInstance
  have hdimV := schemeDeltaDimension_morphismRestrict_le C sX U g hY
  have hiV : iV ≫ (g ∣_ U ≫ (U.ι ≫ sX)) = sZ' := by
    rw [reassoc_of% hh, ← hi₂, ← hV, Category.assoc]
  -- Stacks 0FBM for the closed immersion `Z ⟶ U` and the test scheme `V ⟶ U`
  have H := virtualNormalBundleClass_cap_fundamentalChowClass_excess C sZ (U.ι ≫ sX) i' hi'
    (𝒩.toOpenFactor rfl) r e
    (isVirtualNormalBundleClass_virtualNormalBundleClass C sZ (U.ι ≫ sX) i' hi'
      (𝒩.toOpenFactor rfl) (r + e)) (g ∣_ U) iV g' sqV sZ' hiV hregV n hdimV
  -- the excess normal sheaves of `Z' ⟶ V` and of `Z' ⟶ Y` agree
  have hσ : ((𝒩.toOpenFactor rfl).baseChange i' iV g' (g ∣_ U) sqV).conormalSurjection =
      (𝒩.baseChange _ i₂ g' g sq).conormalSurjection ≫
        (immersionConormalSheafFactorIso (g ⁻¹ᵁ U) iV hV).hom :=
    (VirtualNormalBundle.toOpenFactor_baseChange_surjection rfl hV 𝒩 sq hh sqV).symm
  have : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((𝒩.toOpenFactor rfl).baseChange i' iV g' (g ∣_ U) sqV).bundle (r + e) :=
    isFiniteLocallyFreeOfRank_modulePullback g' 𝒩.bundle (r + e) inferInstance
  have := ((𝒩.toOpenFactor rfl).baseChange i' iV g' (g ∣_ U)
    sqV).isFiniteLocallyFreeOfRank_excessNormalSheaf_of_add r e
  have : @Mono Z'.Modules _ _ _ (immersionConormalSheafFactorIso (g ⁻¹ᵁ U) iV hV).hom :=
    @IsIso.mono_of_iso _ _ _ _ _ (Iso.isIso_hom _)
  have hE : GenuineChern.chernCap C e sZ'
        ((𝒩.toOpenFactor rfl).baseChange i' iV g' (g ∣_ U) sqV).excessNormalSheaf (n - (r : ℤ))
        (Fin.last e) (fundamentalChowClass C sZ' (n - (r : ℤ))) =
      GenuineChern.chernCap C e sZ' (𝒩.baseChange _ i₂ g' g sq).excessNormalSheaf (n - (r : ℤ))
        (Fin.last e) (fundamentalChowClass C sZ' (n - (r : ℤ))) :=
    GenuineChern.chernCap_congr C sZ'
      (E := ((𝒩.toOpenFactor rfl).baseChange i' iV g' (g ∣_ U) sqV).excessNormalSheaf)
      (E' := (𝒩.baseChange _ i₂ g' g sq).excessNormalSheaf) e
      ((dualFunctor Z').mapIso (kernelIsoOfEq hσ ≪≫ kernelCompMono _ _).op).symm (n - (r : ℤ))
      (Fin.last e) (fundamentalChowClass C sZ' (n - (r : ℤ)))
  rw [hE] at H
  -- `U ×_X Y ≅ V` over `U`
  let u : pullback U.ι g ⟶ (g ⁻¹ᵁ U).toScheme :=
    (pullbackSymmetry U.ι g).hom ≫ (pullbackRestrictIsoRestrict g U).hom
  have hu : u ≫ g ∣_ U = pullback.fst U.ι g := by
    simp [u, pullbackRestrictIsoRestrict_hom_morphismRestrict]
  have hu' : inv u ≫ pullback.snd U.ι g = (g ⁻¹ᵁ U).ι := by
    rw [IsIso.inv_comp_eq]
    simp [u, pullbackRestrictIsoRestrict_hom_ι]
  have hcap := BivariantClass.cap_chowPushforwardOfIso
    (virtualNormalBundleClass C sZ (U.ι ≫ sX) i' hi' (𝒩.toOpenFactor rfl) (r + e)) (g ∣_ U) u
    (pullback.fst U.ι g) hu (pullback.fst U.ι g ≫ (U.ι ≫ sX)) rfl n (by rw [reassoc_of% hu])
    (fundamentalChowClass C _ n) (fundamentalChowClass C _ n) rfl
  rw [chowPushforwardOfIso_fundamentalChowClass, H] at hcap
  -- the cap operation of `c(Z ⟶ U, 𝒩) ∘ (U ⟶ X)^*` restricts `[Y]_n` to `[U ×_X Y]_n`
  refine eq_of_heq ((virtualNormalGysinClassOfOpen_cap_heq C sZ sX _ hi U i' rfl 𝒩 (r + e) g n
    _).trans (heq_of_eq ?_))
  rw [chowGroupRestrict_fundamentalChowClass C (g ≫ sX) _ (pullback.snd U.ι g) _ n hY]
  set x := (virtualNormalBundleClass C sZ (U.ι ≫ sX) i' hi' (𝒩.toOpenFactor rfl) (r + e)).cap
    (pullback.fst U.ι g) n (fundamentalChowClass C _ n)
  set T := testBaseChangeIso i' (g ∣_ U) u (pullback.fst U.ι g) hu
  have hTinv : T.inv ≫ pullback.fst i' (pullback.fst U.ι g) = pullback.fst i' (g ∣_ U) := by
    rw [Iso.inv_comp_eq]
    simp [T]
  have hx : x = chowPushforwardOfIso C (pullback.fst i' (g ∣_ U) ≫ sZ)
      (pullback.fst i' (pullback.fst U.ι g) ≫ sZ) T.inv (by rw [reassoc_of% hTinv]) _
      (chowPushforwardOfIso C (pullback.fst i' (pullback.fst U.ι g) ≫ sZ)
        (pullback.fst i' (g ∣_ U) ≫ sZ) T.hom (by simp [T]) _ x) := by
    rw [chowPushforwardOfIso_comp_apply]
    exact ((chowPushforwardOfIso_congr_apply C _ _ _ (𝟙 _) T.hom_inv_id _ (by simp) _ x).trans
      (chowPushforwardOfIso_id C _ _ x)).symm
  rw [hx, ← hcap, chowPushforwardOfIso_comp_apply, chowPushforwardOfIso_comp_apply]
  refine chowPushforwardOfIso_congr_apply C _ _ _ _ ?_ _ _ _ _
  refine pullback.hom_ext ?_ ?_
  · simp [T, testBaseChangeIso]
  · simp [T, testBaseChangeIso, hu', hV]

end Excess

/-! ### The counterpart of the base-change clause of Stacks 0FBK -/

section BaseChange

variable {X' Z' : Scheme.{u}} (f : X' ⟶ X) [LocallyOfFiniteType f] (i₂ : Z' ⟶ X') [IsImmersion i₂]
  (g' : Z' ⟶ Z) (sq : IsPullback i₂ g' f i) (sZ' : Z' ⟶ C.S) [LocallyOfFiniteType sZ']
  (hi₂ : i₂ ≫ (f ≫ sX) = sZ') (𝒩 : VirtualNormalBundle i) (r : ℕ)
  [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} 𝒩.bundle r]

omit [LocallyOfFiniteType f] in
/-- `U ×_X T = f⁻¹(U) ×_{X'} T` for a test scheme `t : T ⟶ X'` and `f : X' ⟶ X`. -/
theorem isPullback_preimageTest {T : Scheme.{u}} (t : T ⟶ X') :
    IsPullback (pullback.fst (f ⁻¹ᵁ U).ι t ≫ f ∣_ U) (pullback.snd (f ⁻¹ᵁ U).ι t) U.ι (t ≫ f) :=
  (IsPullback.of_hasPullback (f ⁻¹ᵁ U).ι t).paste_horiz (isPullback_morphismRestrict f U)

omit [IsImmersion i] in
/-- **Restricting to `U ×_X T` or to `f⁻¹(U) ×_{X'} T`.** For a bivariant class `c` for a
morphism to an open `U ⊆ X`, `f : X' ⟶ X` and a test scheme `t : T ⟶ X'`, capping with `c` the
restriction of a class on `T` to `f⁻¹(U) ×_{X'} T` (a test scheme over `U` through `f⁻¹(U) ⟶ U`)
or to `U ×_X T` gives the same class, read through the identification of the two. -/
theorem BivariantClass.cap_preimageTest {G : GysinSystem C} {sU : U.toScheme ⟶ C.S}
    [LocallyOfFiniteType sU] (hU' : U.ι ≫ sX = sU) {p : ℤ}
    (c : BivariantClass C G sZ sU i' (by rw [← hU', ← Category.assoc, hU, hi]) p)
    {T : Scheme.{u}} (t : T ⟶ X') [LocallyOfFiniteType t] (k : ℤ)
    (α : chowGroup C (t ≫ (f ≫ sX)) k) :
    c.cap (pullback.fst (f ⁻¹ᵁ U).ι t ≫ f ∣_ U) k
        (chowGroupRestrict C (t ≫ (f ≫ sX)) ((pullback.fst (f ⁻¹ᵁ U).ι t ≫ f ∣_ U) ≫ sU)
          (pullback.snd (f ⁻¹ᵁ U).ι t)
          (by rw [← hU']; simp [pullback.condition_assoc]) k α) =
      chowPushforwardOfIso C (pullback.fst i' (pullback.fst U.ι (t ≫ f)) ≫ sZ)
        (pullback.fst i' (pullback.fst (f ⁻¹ᵁ U).ι t ≫ f ∣_ U) ≫ sZ)
        (testBaseChangeIso i' (pullback.fst (f ⁻¹ᵁ U).ι t ≫ f ∣_ U)
          (isPullback_preimageTest U f t).isoPullback.inv (pullback.fst U.ι (t ≫ f))
          (isPullback_preimageTest U f t).isoPullback_inv_fst).hom (by simp) (k - p)
        (c.cap (pullback.fst U.ι (t ≫ f)) k
          (chowGroupRestrict C (t ≫ (f ≫ sX)) (pullback.fst U.ι (t ≫ f) ≫ sU)
            (pullback.snd U.ι (t ≫ f))
            (by rw [← hU']; simp [pullback.condition_assoc]) k α)) := by
  subst hU'
  have : IsIso (isPullback_preimageTest U f t).isoPullback.inv := Iso.isIso_inv _
  refine Eq.trans ?_ (c.cap_chowPushforwardOfIso _ (isPullback_preimageTest U f t).isoPullback.inv
    (pullback.fst U.ι (t ≫ f)) (isPullback_preimageTest U f t).isoPullback_inv_fst _ rfl k
    (by rw [← Category.assoc, (isPullback_preimageTest U f t).isoPullback_inv_fst]) _ _ rfl)
  refine congrArg (c.cap _ k) ?_
  have e := isPullback_preimageTest U f t
  have hs : pullback.snd U.ι (t ≫ f) ≫ (t ≫ (f ≫ sX)) = pullback.fst U.ι (t ≫ f) ≫ (U.ι ≫ sX) := by
    simp [pullback.condition_assoc]
  refine (eq_of_heq (chowGroupRestrict_heq_congr C _ _ _ (pullback.snd (f ⁻¹ᵁ U).ι t)
    (e.isoPullback.hom ≫ pullback.snd U.ι (t ≫ f)) _ (by simp [pullback.condition_assoc])
    e.isoPullback_hom_snd.symm k α)).trans ?_
  refine (chowGroupRestrict_comp C (t ≫ (f ≫ sX)) (pullback.fst U.ι (t ≫ f) ≫ (U.ι ≫ sX))
    (pullback.snd U.ι (t ≫ f)) hs k _ e.isoPullback.hom
    (by rw [IsPullback.isoPullback_hom_fst_assoc]) α).symm.trans ?_
  exact chowGroupRestrict_eq_chowPushforwardOfIso_inv C _ _ e.isoPullback _ k _

/-- **The class of Stacks 0FBK of `g^*𝒩` on `f⁻¹(U)`, as a base change of that on `U`.** For a
cartesian square `Z' = Z ×_X X'` of immersions and a closed factor `iW : Z' ⟶ f⁻¹(U)` of
`Z' ⟶ X'`, the class `c(Z' ⟶ f⁻¹(U), g^*𝒩)` caps on a test scheme `t'` as `c(Z ⟶ U, 𝒩)` does on
`t' ≫ (f⁻¹(U) ⟶ U)`. -/
theorem virtualNormalGysinClass_toOpenFactor_baseChange_cap
    (iW : Z' ⟶ (f ⁻¹ᵁ U).toScheme) [IsClosedImmersion iW] (hW : iW ≫ (f ⁻¹ᵁ U).ι = i₂)
    (sqW : IsPullback iW g' (f ∣_ U) i') (hiW' : iW ≫ (f ∣_ U ≫ (U.ι ≫ sX)) = sZ')
    {T : Scheme.{u}} (t' : T ⟶ (f ⁻¹ᵁ U).toScheme) [LocallyOfFiniteType t'] (k : ℤ)
    (a : chowGroup C (t' ≫ ((f ⁻¹ᵁ U).ι ≫ (f ≫ sX))) k) :
    haveI : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
        (𝒩.baseChange i i₂ g' f sq).bundle r :=
      isFiniteLocallyFreeOfRank_modulePullback g' 𝒩.bundle r inferInstance
    (virtualNormalBundleClass C sZ' ((f ⁻¹ᵁ U).ι ≫ (f ≫ sX)) iW
        (by rw [← Category.assoc, hW, hi₂]) ((𝒩.baseChange i i₂ g' f sq).toOpenFactor hW) r).cap
        t' k a =
      chowPushforwardOfIso C (pullback.fst i' (t' ≫ f ∣_ U) ≫ sZ) (pullback.fst iW t' ≫ sZ')
        (subschemeTestBaseChangeIso i' iW g' (f ∣_ U) sqW t').hom
        (by rw [← hiW', ← openFactor_comp_structureMorphism C sZ sX i hi hU]
            exact subschemeTestBaseChangeIso_hom_comp_structure i' iW g' (f ∣_ U) sqW t'
              (U.ι ≫ sX))
        (k - r)
        ((virtualNormalBundleClass C sZ (U.ι ≫ sX) i'
            (openFactor_comp_structureMorphism C sZ sX i hi hU) (𝒩.toOpenFactor hU) r).cap
          (t' ≫ f ∣_ U) k
          (chowGroupCongr C (by rw [Category.assoc, morphismRestrict_ι_assoc]) k a)) := by
  have : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (𝒩.baseChange i i₂ g' f sq).bundle r :=
    isFiniteLocallyFreeOfRank_modulePullback g' 𝒩.bundle r inferInstance
  have : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((𝒩.toOpenFactor hU).baseChange i' iW g' (f ∣_ U) sqW).bundle r :=
    isFiniteLocallyFreeOfRank_modulePullback g' 𝒩.bundle r inferInstance
  have hiW : iW ≫ ((f ⁻¹ᵁ U).ι ≫ (f ≫ sX)) = sZ' := by rw [← Category.assoc, hW, hi₂]
  have hB : virtualNormalBundleClass C sZ' ((f ⁻¹ᵁ U).ι ≫ (f ≫ sX)) iW hiW
      ((𝒩.baseChange i i₂ g' f sq).toOpenFactor hW) r =
        virtualNormalBundleClass C sZ' ((f ⁻¹ᵁ U).ι ≫ (f ≫ sX)) iW hiW
          ((𝒩.toOpenFactor hU).baseChange i' iW g' (f ∣_ U) sqW) r :=
    virtualNormalGysinClass_eq_of_dualIso C sZ' _ iW hiW
      ((𝒩.baseChange i i₂ g' f sq).toOpenFactor hW)
      ((𝒩.toOpenFactor hU).baseChange i' iW g' (f ∣_ U) sqW)
      (Iso.refl (dualSheaf ((modulePullback g'.toLRSHom.toShHom).obj 𝒩.bundle)))
      ((Category.id_comp _).trans (VirtualNormalBundle.toOpenFactor_baseChange_surjection hU hW 𝒩
        sq (morphismRestrict_ι f U) sqW)) r
  have hbase : ∀ (s s' : (f ⁻¹ᵁ U).toScheme ⟶ C.S) [LocallyOfFiniteType s]
      [LocallyOfFiniteType s'] (_ : s = s') (h₁ : iW ≫ s = sZ') (h₂ : iW ≫ s' = sZ')
      (N : VirtualNormalBundle iW) [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} N.bundle r]
      (b : chowGroup C (t' ≫ s) k) (b' : chowGroup C (t' ≫ s') k), b ≍ b' →
      (virtualNormalBundleClass C sZ' s iW h₁ N r).cap t' k b =
        (virtualNormalBundleClass C sZ' s' iW h₂ N r).cap t' k b' := by
    intro s s' _ _ hs h₁ h₂ N _ b b' hb
    subst hs
    cases hb
    rfl
  rw [hB, hbase _ (f ∣_ U ≫ (U.ι ≫ sX)) (morphismRestrict_ι_assoc f U sX).symm hiW hiW' _ a
    (chowGroupCongr C (by rw [morphismRestrict_ι_assoc]) k a) (chowGroupCongr_heq C _ k a).symm,
    virtualNormalGysinClass_cap_baseChange C sZ (U.ι ≫ sX) i'
      (openFactor_comp_structureMorphism C sZ sX i hi hU) iW g' (f ∣_ U) sqW
      (𝒩.toOpenFactor hU) r sZ' hiW' t' k, chowGroupCongr_chowGroupCongr]

/-- **The counterpart for immersions of the base-change clause of Stacks 0FBK, on cap
operations.** For a cartesian square `Z' = Z ×_X X'` of immersions with `X' ⟶ X` locally of finite
type and a test scheme `t : T ⟶ X'`, the class `c(Z' ⟶ X', g^*𝒩)` caps as `c(Z ⟶ X, 𝒩)` does on
`t ≫ f`, through `Z ×_X T ≅ Z' ×_{X'} T`; the opens through which the two immersions factor as
closed immersions are arbitrary. -/
theorem virtualNormalGysinClassOfOpen_cap_baseChange (V : X'.Opens) (iV : Z' ⟶ V.toScheme)
    [IsClosedImmersion iV] (hV : iV ≫ V.ι = i₂) {T : Scheme.{u}} (t : T ⟶ X')
    [LocallyOfFiniteType t] (k : ℤ) (α : chowGroup C (t ≫ (f ≫ sX)) k) :
    haveI : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
        (𝒩.baseChange i i₂ g' f sq).bundle r :=
      isFiniteLocallyFreeOfRank_modulePullback g' 𝒩.bundle r inferInstance
    (virtualNormalGysinClassOfOpen C sZ' (f ≫ sX) i₂ hi₂ V iV hV (𝒩.baseChange i i₂ g' f sq) r).cap
        t k α =
      chowPushforwardOfIso C (pullback.fst i (t ≫ f) ≫ sZ) (pullback.fst i₂ t ≫ sZ')
        ((IsPullback.of_hasPullback i₂ t).paste_horiz sq.flip).isoPullback.inv
        (by rw [Iso.inv_comp_eq, IsPullback.isoPullback_hom_fst_assoc, Category.assoc, ← hi₂,
          ← Category.assoc i₂, sq.w, Category.assoc, hi])
        (k - r)
        ((virtualNormalGysinClassOfOpen C sZ sX i hi U i' hU 𝒩 r).cap (t ≫ f) k
          (chowGroupCongr C (Category.assoc t f sX).symm k α)) := by
  have : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (𝒩.baseChange i i₂ g' f sq).bundle r :=
    isFiniteLocallyFreeOfRank_modulePullback g' 𝒩.bundle r inferInstance
  -- the open `W = f⁻¹(U)` of `X'` and the closed factor `iW : Z' ⟶ W` of `i₂`
  obtain ⟨iW, hW, sqW, _⟩ := exists_closedFactor_preimage (hU ▸ sq : IsPullback i₂ g' f (i' ≫ U.ι))
  have hiW' : iW ≫ (f ∣_ U ≫ (U.ι ≫ sX)) = sZ' := by
    rw [morphismRestrict_ι_assoc, ← Category.assoc, hW, hi₂]
  refine (congrArg (fun c ↦ BivariantClass.cap c t k α)
    (virtualNormalGysinClassOfOpen_independent C sZ' (f ≫ sX) i₂ hi₂ (𝒩.baseChange _ i₂ g' f sq) r
      V (f ⁻¹ᵁ U) iV hV iW hW)).trans ?_
  -- the left side: through `f⁻¹(U) ×_{X'} T`, then `U ×_X T`
  have hL := virtualNormalGysinClassOfOpen_cap_heq C sZ' (f ≫ sX) i₂ hi₂ (f ⁻¹ᵁ U) iW hW
    (𝒩.baseChange _ i₂ g' f sq) r t k α
  rw [virtualNormalGysinClass_toOpenFactor_baseChange_cap C sZ sX i hi U i' hU f i₂ g' sq sZ' hi₂
      𝒩 r iW hW sqW hiW' (pullback.fst (f ⁻¹ᵁ U).ι t) k, chowGroupCongr_chowGroupRestrict,
    BivariantClass.cap_preimageTest C sZ sX i hi U i' hU f rfl _ t k α] at hL
  on_goal 2 => simp [pullback.condition_assoc]
  refine eq_of_heq (hL.trans ?_)
  -- the right side: through `U ×_X T`
  subst hU
  rw [eq_of_heq (virtualNormalGysinClassOfOpen_cap_heq C sZ sX _ hi U i' rfl 𝒩 r (t ≫ f) k _),
    chowGroupRestrict_chowGroupCongr, chowPushforwardOfIso_comp_apply,
    chowPushforwardOfIso_comp_apply, chowPushforwardOfIso_comp_apply]
  on_goal 2 => simp [pullback.condition_assoc]
  refine (chowPushforwardOfIso_congrHom_heq hW t (by simp) (k - r) _).symm.trans (heq_of_eq ?_)
  rw [chowPushforwardOfIso_comp_apply]
  refine chowPushforwardOfIso_congr_apply C _ _ _ _ ?_ _ _ _ _
  rw [← cancel_mono ((IsPullback.of_hasPullback i₂ t).paste_horiz sq.flip).isoPullback.hom]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  refine pullback.hom_ext ?_ ?_
  · simp [pullback.congrHom]
  · simp [pullback.congrHom]

/-- **The counterpart for immersions of the base-change clause of Stacks 0FBK.** For a cartesian
square `Z' = Z ×_X X'` of immersions with `f : X' ⟶ X` locally of finite type, the restriction
(Stacks 0F9Z) of `c(Z ⟶ X, 𝒩)` along `f`, carried to `Z'` along `Z ×_X X' ≅ Z'`, is
`c(Z' ⟶ X', g^*𝒩)`, with `g^*𝒩` the virtual normal bundle of Stacks 0FBJ; the opens through which
the two immersions factor as closed immersions are arbitrary. This is the constant-rank form; the
registered counterpart, at arbitrary rank in `A^*(Z' ⟶ X')^∧`, is
`completedBivariantTransport_completedBivariantRestriction_completedVirtualNormalGysinClassOfOpen`.
-/
theorem bivariantTransport_bivariantRestriction_virtualNormalGysinClassOfOpen (V : X'.Opens)
    (iV : Z' ⟶ V.toScheme) [IsClosedImmersion iV] (hV : iV ≫ V.ι = i₂) :
    haveI : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
        (𝒩.baseChange i i₂ g' f sq).bundle r :=
      isFiniteLocallyFreeOfRank_modulePullback g' 𝒩.bundle r inferInstance
    bivariantTransport C (gysinSystemOfInvertible C) (pullback.fst i f ≫ sZ) sZ' (f ≫ sX)
        (pullback.snd i f) (pullbackSnd_comp_structureMorphism_eq C sZ sX i hi f) i₂ hi₂
        sq.flip.isoPullback.symm (sq.flip.isoPullback_inv_snd) (r : ℤ)
        (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C)
        (bivariantRestriction C (gysinSystemOfInvertible C) sZ sX i hi f (r : ℤ)
          (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C)
          (virtualNormalGysinClassOfOpen C sZ sX i hi U i' hU 𝒩 r)) =
      virtualNormalGysinClassOfOpen C sZ' (f ≫ sX) i₂ hi₂ V iV hV
        (𝒩.baseChange i i₂ g' f sq) r := by
  have : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (𝒩.baseChange i i₂ g' f sq).bundle r :=
    isFiniteLocallyFreeOfRank_modulePullback g' 𝒩.bundle r inferInstance
  refine eq_of_isBivariantTransport C _ _ _ _ _ _ _ _ _ _ _
    (isBivariantTransport_bivariantTransport C _ _ _ _ _ _ _ _ _ _ _ _ _) ?_
  intro T t _ k α
  rw [virtualNormalGysinClassOfOpen_cap_baseChange C sZ sX i hi U i' hU f i₂ g' sq sZ' hi₂ 𝒩 r V iV
      hV t k α, bivariantTransportCap_apply, bivariantRestriction_cap,
    bivariantRestrictionCap_apply, chowPushforwardOfIso_comp_apply]
  refine chowPushforwardOfIso_congr_apply C _ _ _ _ ?_ _ _ _ _
  rw [← cancel_mono ((IsPullback.of_hasPullback i₂ t).paste_horiz sq.flip).isoPullback.hom]
  simp only [Category.assoc, Iso.inv_hom_id]
  refine pullback.hom_ext ?_ ?_
  · simp
  · simp

end BaseChange

/-! ### The degree parts of `c ∘ j^*` on completions -/

section CompletedComposite

variable {Z U W : Scheme.{u}} (sZ₀ : Z ⟶ C.S) [LocallyOfFiniteType sZ₀] (sU : U ⟶ C.S)
  [LocallyOfFiniteType sU] (sW : W ⟶ C.S) [LocallyOfFiniteType sW] (i₀ : Z ⟶ U)
  [LocallyOfFiniteType i₀] (j : U ⟶ W) [IsOpenImmersion j] (hi₀ : i₀ ≫ sU = sZ₀)
  (hj : j ≫ sW = sU) [IsLocallyNoetherian Z] [IsLocallyNoetherian U] [IsLocallyNoetherian W]

omit [LocallyOfFiniteType sX] in
/-- **The degree parts of `c ∘ j^*`** (Stacks 0FE0 and Stacks 0B75). For a completed class `c` and
the flat pullback `j^*` along an open immersion, the degree `p + 0` part of the completed composite
`c ∘ j^*` is the composite of the degree `p` part of `c` with `j^*`. Both are compared on every
connected component of the source (Stacks 0FDZ), where they are composites of the same two
classes. -/
theorem completedBivariantSequenceOfInvertible_completedOpenImmersionComposite
    (c : completedBivariantGroup C (gysinSystemOfInvertible C) sZ₀ sU i₀ hi₀) (p : ℤ) :
    completedBivariantSequenceOfInvertible C sZ₀ sW (i₀ ≫ j) (comp_comp_structureMorphism_eq hi₀ hj)
        (completedOpenImmersionComposite C sZ₀ sU sW i₀ j hi₀ hj c) (p + -((0 : ℕ) : ℤ)) =
      openImmersionComposite C sZ₀ sU sW i₀ j hi₀ hj p
        (completedBivariantSequenceOfInvertible C sZ₀ sU i₀ hi₀ c p) := by
  apply (bivariantConnectedComponentEquiv C (gysinSystemOfInvertible C) sZ₀ sW (i₀ ≫ j)
    (comp_comp_structureMorphism_eq hi₀ hj) (p + -((0 : ℕ) : ℤ))
    (gysinSystemOfInvertible_isNaturalUnderOpenImmersion C)
    (gysinSystemOfInvertible_isNaturalUnderOpensRestriction C)
    (gysinSystemOfInvertible_isNaturalUnderPullbackComp C)).injective
  funext z
  rw [bivariantConnectedComponentEquiv_apply, bivariantConnectedComponentEquiv_apply]
  refine (restriction_completedBivariantSequence C (gysinSystemOfInvertible C) sZ₀ sW (i₀ ≫ j)
    (comp_comp_structureMorphism_eq hi₀ hj) (gysinSystemOfInvertible_isNaturalUnderOpenImmersion C)
    (gysinSystemOfInvertible_isNaturalUnderOpensRestriction C)
    (gysinSystemOfInvertible_isNaturalUnderPullbackComp C) _ _ z).trans ?_
  rw [openImmersionComposite,
    bivariantConnectedComponentRestriction_bivariantCompositeOfInvertible,
    bivariantConnectedComponentRestriction_flatPullbackBivariantClassOfIsOpenImmersion]
  refine eq_of_heq ((completedOpenImmersionComposite_apply_heq C sZ₀ sU sW i₀ j hi₀ hj c z
    _).trans (HEq.trans ?_ (bivariantClassComponentCongr_heq C _ _ _ _ _ _ _ _ _ _).symm))
  have hdeg : ∀ q : ℤ, q = p →
      openImmersionComposite C ((Z.connectedComponentOpens z).ι ≫ sZ₀)
          ((U.connectedComponentOpens (i₀.continuous.connectedComponentsMap z)).ι ≫ sU)
          ((W.connectedComponentOpens (j.continuous.connectedComponentsMap
            (i₀.continuous.connectedComponentsMap z))).ι ≫ sW)
          (i₀.resConnectedComponent z)
          (j.resConnectedComponent (i₀.continuous.connectedComponentsMap z))
          (i₀.resConnectedComponent_comp_ι_comp hi₀ z)
          (j.resConnectedComponent_comp_ι_comp hj (i₀.continuous.connectedComponentsMap z)) q
          (c z q) ≍
        openImmersionComposite C ((Z.connectedComponentOpens z).ι ≫ sZ₀)
          ((U.connectedComponentOpens (i₀.continuous.connectedComponentsMap z)).ι ≫ sU)
          ((W.connectedComponentOpens (j.continuous.connectedComponentsMap
            (i₀.continuous.connectedComponentsMap z))).ι ≫ sW)
          (i₀.resConnectedComponent z)
          (j.resConnectedComponent (i₀.continuous.connectedComponentsMap z))
          (i₀.resConnectedComponent_comp_ι_comp hi₀ z)
          (j.resConnectedComponent_comp_ι_comp hj (i₀.continuous.connectedComponentsMap z)) p
          (c z p) := by
    rintro q rfl
    rfl
  refine (hdeg _ (by simp)).trans (heq_of_eq ?_)
  exact congrArg _ (restriction_completedBivariantSequence C (gysinSystemOfInvertible C) sZ₀ sU i₀
    hi₀ (gysinSystemOfInvertible_isNaturalUnderOpenImmersion C)
    (gysinSystemOfInvertible_isNaturalUnderOpensRestriction C)
    (gysinSystemOfInvertible_isNaturalUnderPullbackComp C) c p z).symm

end CompletedComposite

/-! ### The cap operation of the completed class of an immersion -/

section CompletedCap

/-- The degree-`q` part of `c ∘ (U ⟶ X)^*` for a completed class `c` on `U` caps on `t : T ⟶ X`
as the degree-`q` part of `c` does on `U ×_X T`, pushed forward along
`Z ×_U (U ×_X T) ≅ Z ×_X T`. -/
private theorem cap_completedSequence_completedOpenImmersionComposite_heq
    [IsLocallyNoetherian Z] [IsLocallyNoetherian X] [IsLocallyNoetherian U.toScheme]
    (hi' : i' ≫ (U.ι ≫ sX) = sZ) (hi : (i' ≫ U.ι) ≫ sX = sZ)
    (c : completedBivariantGroup C (gysinSystemOfInvertible C) sZ (U.ι ≫ sX) i' hi') (q : ℤ)
    {T : Scheme.{u}} (t : T ⟶ X) [LocallyOfFiniteType t] (k : ℤ) (α : chowGroup C (t ≫ sX) k) :
    (completedBivariantSequenceOfInvertible C sZ sX (i' ≫ U.ι) hi
        (completedOpenImmersionComposite C sZ (U.ι ≫ sX) sX i' U.ι hi' rfl c) q).cap t k α ≍
      chowPushforwardOfIso C (pullback.fst i' (pullback.fst U.ι t) ≫ sZ)
        (pullback.fst (i' ≫ U.ι) t ≫ sZ) (pullbackRightPullbackFstIso U.ι t i').hom
        (pullbackRightPullbackFstIso_hom_comp_fst_comp sZ i' U.ι t) (k - q)
        ((completedBivariantSequenceOfInvertible C sZ (U.ι ≫ sX) i' hi' c q).cap
          (pullback.fst U.ι t) k
          (chowGroupRestrict C (t ≫ sX) (pullback.fst U.ι t ≫ (U.ι ≫ sX)) (pullback.snd U.ι t)
            (pullbackSnd_comp_structureMorphism rfl t) k α)) := by
  have hcapc : ∀ (q₁ q₂ : ℤ) (_ : q₁ = q₂)
      (d₁ : BivariantClass C (gysinSystemOfInvertible C) sZ sX (i' ≫ U.ι) hi q₁)
      (d₂ : BivariantClass C (gysinSystemOfInvertible C) sZ sX (i' ≫ U.ι) hi q₂), d₁ ≍ d₂ →
      d₁.cap t k α ≍ d₂.cap t k α := by
    rintro q₁ _ rfl d₁ d₂ hd
    cases hd
    rfl
  have hseq : ∀ (q₁ q₂ : ℤ), q₁ = q₂ →
      completedBivariantSequenceOfInvertible C sZ sX (i' ≫ U.ι) hi
        (completedOpenImmersionComposite C sZ (U.ι ≫ sX) sX i' U.ι hi' rfl c) q₁ ≍
      completedBivariantSequenceOfInvertible C sZ sX (i' ≫ U.ι) hi
        (completedOpenImmersionComposite C sZ (U.ι ≫ sX) sX i' U.ι hi' rfl c) q₂ := by
    rintro q₁ _ rfl
    rfl
  exact (hcapc _ _ (by simp) _ _ ((hseq q (q + -((0 : ℕ) : ℤ)) (by simp)).trans
    (heq_of_eq (completedBivariantSequenceOfInvertible_completedOpenImmersionComposite C sZ
      (U.ι ≫ sX) sX i' U.ι hi' rfl c q)))).trans
    (openImmersionComposite_cap_heq C sZ (U.ι ≫ sX) sX i' U.ι hi' rfl q _ t k α)

variable (𝒩 : VirtualNormalBundle i)

/-- **The cap operation of `c(Z ⟶ X, 𝒩) ∈ A^*(Z ⟶ X)^∧`, degree by degree.** On a test scheme
`t : T ⟶ X` the degree-`n` part of `c(Z ⟶ U, 𝒩) ∘ (U ⟶ X)^*` restricts a class on `T` to
`U ×_X T`, caps there with the degree-`n` part of `c(Z ⟶ U, 𝒩)`, and pushes the result forward
along `Z ×_U (U ×_X T) ≅ Z ×_X T`. -/
theorem completedVirtualNormalGysinClassOfOpen_cap_heq [IsLocallyNoetherian Z]
    [IsLocallyNoetherian X] (n : ℤ) {T : Scheme.{u}} (t : T ⟶ X) [LocallyOfFiniteType t] (k : ℤ)
    (α : chowGroup C (t ≫ sX) k) :
    haveI : IsLocallyNoetherian U.toScheme := LocallyOfFiniteType.isLocallyNoetherian (U.ι ≫ sX)
    (completedBivariantSequenceOfInvertible C sZ sX i hi
        (completedVirtualNormalGysinClassOfOpen C sZ sX i hi U i' hU 𝒩) n).cap t k α ≍
      chowPushforwardOfIso C (pullback.fst i' (pullback.fst U.ι t) ≫ sZ)
        (pullback.fst (i' ≫ U.ι) t ≫ sZ) (pullbackRightPullbackFstIso U.ι t i').hom
        (pullbackRightPullbackFstIso_hom_comp_fst_comp sZ i' U.ι t) (k - n)
        ((completedBivariantSequenceOfInvertible C sZ (U.ι ≫ sX) i'
            (openFactor_comp_structureMorphism C sZ sX i hi hU)
            (completedVirtualNormalGysinClass C sZ (U.ι ≫ sX) i'
              (openFactor_comp_structureMorphism C sZ sX i hi hU) (𝒩.toOpenFactor hU)) n).cap
          (pullback.fst U.ι t) k
          (chowGroupRestrict C (t ≫ sX) (pullback.fst U.ι t ≫ (U.ι ≫ sX)) (pullback.snd U.ι t)
            (pullbackSnd_comp_structureMorphism rfl t) k α)) := by
  have : IsLocallyNoetherian U.toScheme := LocallyOfFiniteType.isLocallyNoetherian (U.ι ≫ sX)
  subst hU
  exact cap_completedSequence_completedOpenImmersionComposite_heq C sZ sX U i' _ hi _ n t k α

end CompletedCap

/-! ### The counterpart of Stacks 0FBM at unbounded rank -/

section CompletedExcess

/-- **The fundamental class of `Y`, restricted to `U ×_X Y` or to `g⁻¹(U)`.** For a bivariant class
`d` for a closed immersion `i' : Z ⟶ U` into an open `U ⊆ X` and `g : Y ⟶ X` with
`dim_δ(Y) ≤ n`, capping `[U ×_X Y]_n` (the restriction of `[Y]_n`) with `d` gives `d ∩ [g⁻¹(U)]_n`,
read through `U ×_X Y ≅ g⁻¹(U)`. -/
theorem BivariantClass.cap_fundamentalChowClass_preimage {G : GysinSystem C}
    (hi' : i' ≫ (U.ι ≫ sX) = sZ) {p : ℤ}
    (d : BivariantClass C G sZ (U.ι ≫ sX) i' hi' p) {Y : Scheme.{u}} (g : Y ⟶ X)
    [LocallyOfFiniteType g] (n : ℤ) (hY : schemeDeltaDimension C (g ≫ sX) ≤ (n : EInt)) :
    d.cap (pullback.fst U.ι g) n
        (chowGroupRestrict C (g ≫ sX) (pullback.fst U.ι g ≫ (U.ι ≫ sX)) (pullback.snd U.ι g)
          (pullbackSnd_comp_structureMorphism rfl g) n (fundamentalChowClass C (g ≫ sX) n)) =
      chowPushforwardOfIso C (pullback.fst i' (g ∣_ U) ≫ sZ)
        (pullback.fst i' (pullback.fst U.ι g) ≫ sZ)
        (testBaseChangeIso i' (g ∣_ U) ((pullbackSymmetry U.ι g) ≪≫
          (pullbackRestrictIsoRestrict g U)).hom (pullback.fst U.ι g)
          (by simp [pullbackRestrictIsoRestrict_hom_morphismRestrict])).inv
        (by rw [Iso.inv_comp_eq]; simp) (n - p)
        (d.cap (g ∣_ U) n (fundamentalChowClass C (g ∣_ U ≫ (U.ι ≫ sX)) n)) := by
  set e := (pullbackSymmetry U.ι g) ≪≫ (pullbackRestrictIsoRestrict g U)
  have hu : e.hom ≫ g ∣_ U = pullback.fst U.ι g := by
    simp [e, pullbackRestrictIsoRestrict_hom_morphismRestrict]
  rw [chowGroupRestrict_fundamentalChowClass C (g ≫ sX) _ (pullback.snd U.ι g) _ n hY]
  have hcap := BivariantClass.cap_chowPushforwardOfIso d (g ∣_ U) e.hom (pullback.fst U.ι g) hu
    (pullback.fst U.ι g ≫ (U.ι ≫ sX)) rfl n (by rw [reassoc_of% hu])
    (fundamentalChowClass C _ n) (fundamentalChowClass C _ n) rfl
  rw [chowPushforwardOfIso_fundamentalChowClass] at hcap
  rw [hcap, chowPushforwardOfIso_comp_apply]
  exact ((chowPushforwardOfIso_congr_apply C _ _ _ (𝟙 _) (Iso.hom_inv_id _) _ (by simp) _ _).trans
    (chowPushforwardOfIso_id C _ _ _)).symm

variable (𝒩 : VirtualNormalBundle i)

/-- **The counterpart of Stacks 0FBM for immersions, at unbounded rank.** Let `i : Z ⟶ X` be an
immersion with a virtual normal bundle `𝒩` of arbitrary rank, and let `g : Y ⟶ X` be locally of
finite type such that the base change `i₂ : Z' = Z ×_X Y ⟶ Y` is a regular immersion whose
conormal sheaf has constant rank `r`; let `ℰ` be the excess normal sheaf. If `dim_δ(Y) ≤ n` then

  `c(Z ⟶ X, 𝒩) ∩ [Y]_n = c_top(ℰ) ∩ [Z']_{n - r}`

degree by degree in `CH_*(Z ×_X Y)`, for `c(Z ⟶ X, 𝒩) = c(Z ⟶ U, 𝒩) ∘ (U ⟶ X)^*` in
`A^*(Z ⟶ X)^∧`: the degree-`(r + e)` part of the left side is the degree-`e` part of `c_top(ℰ)`
capped with `[Z']_{n - r}` (`Stacks.Chow.topChernCap`), and the parts of degree `p < r` vanish.
This is how the source reads the equality when the rank is unbounded on the connected components.

On `V = g⁻¹(U)` the immersion `i₂` factors through the regular closed immersion `Z' ⟶ V`, the
base change of `Z ⟶ U`, with the same conormal and excess normal sheaves, and `[Y]_n` restricts
to `[V]_n`; so this is Stacks 0FBM at arbitrary rank
(`Stacks.Chow.completedVirtualNormalGysinCap_fundamentalChowClass_excess`) for `Z ⟶ U`. -/
@[stacks 0FBQ "(3), counterparts: the counterpart of Lemma 0FBM when the virtual normal bundle has \
unbounded rank, c(Z → X, N) ∩ [Y]_n = c_top(E) ∩ [Z ×_X Y]_{n-r} degree by degree in CH_*, for an \
immersion Z → X, c(Z → X, N) ∈ A^*(Z → X)^∧, Z ×_X Y → Y regular with conormal sheaf of constant \
rank r, E the excess normal sheaf and dim_δ(Y) ≤ n"]
theorem completedVirtualNormalGysinClassOfOpen_cap_fundamentalChowClass_excess {Y Z' : Scheme.{u}}
    (g : Y ⟶ X) [LocallyOfFiniteType g] (i₂ : Z' ⟶ Y) [IsImmersion i₂] (g' : Z' ⟶ Z)
    (sq : IsPullback i₂ g' g i) (sZ' : Z' ⟶ C.S) [LocallyOfFiniteType sZ']
    (hi₂ : i₂ ≫ (g ≫ sX) = sZ') (hreg : IsRegularImmersion i₂) (r : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (conormalModule i₂) r]
    (n : ℤ) (hY : schemeDeltaDimension C (g ≫ sX) ≤ (n : EInt)) :
    haveI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
    haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
    haveI : SheafOfModules.IsFiniteLocallyFree.{u, u, u}
        (𝒩.baseChange i i₂ g' g sq).excessNormalSheaf :=
      (𝒩.baseChange i i₂ g' g sq).isFiniteLocallyFree_excessNormalSheaf
        (SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree _ r)
    (∀ e : ℕ, (completedBivariantSequenceOfInvertible C sZ sX i hi
        (completedVirtualNormalGysinClassOfOpen C sZ sX i hi U i' hU 𝒩) ((r + e : ℕ) : ℤ)).cap g n
          (fundamentalChowClass C (g ≫ sX) n) =
        chowPushforwardOfIso C sZ' (pullback.fst i g ≫ sZ) sq.flip.isoPullback.hom
          (isoPullback_hom_comp_structureMorphism C sZ sX sq hi sZ' hi₂) (n - ((r + e : ℕ) : ℤ))
          (chowGroupDegreeEquiv C sZ' (by push_cast; ring)
            (topChernCap C sZ' (𝒩.baseChange i i₂ g' g sq).excessNormalSheaf (n - (r : ℤ)) e
              (fundamentalChowClass C sZ' (n - (r : ℤ)))))) ∧
      ∀ p : ℤ, p < r → (completedBivariantSequenceOfInvertible C sZ sX i hi
        (completedVirtualNormalGysinClassOfOpen C sZ sX i hi U i' hU 𝒩) p).cap g n
          (fundamentalChowClass C (g ≫ sX) n) = 0 := by
  have : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  have : IsLocallyNoetherian U.toScheme := LocallyOfFiniteType.isLocallyNoetherian (U.ι ≫ sX)
  have : SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (𝒩.baseChange i i₂ g' g sq).excessNormalSheaf :=
    (𝒩.baseChange i i₂ g' g sq).isFiniteLocallyFree_excessNormalSheaf
      (SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree _ r)
  subst hU
  have hi' := openFactor_comp_structureMorphism C sZ sX _ hi rfl
  obtain ⟨iV, hV, sqV, _⟩ := exists_closedFactor_preimage sq
  have hh : g ∣_ U ≫ U.ι = (g ⁻¹ᵁ U).ι ≫ g := morphismRestrict_ι g U
  have hregV := isRegularImmersion_of_comp_of_smooth_of_eq iV (g ⁻¹ᵁ U).ι hV hreg
  have : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (conormalModule iV) r :=
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso.{u, u, u}
      (immersionConormalSheafFactorIso (g ⁻¹ᵁ U) iV hV) inferInstance
  have hdimV := schemeDeltaDimension_morphismRestrict_le C sX U g hY
  have hiV : iV ≫ (g ∣_ U ≫ (U.ι ≫ sX)) = sZ' := by
    rw [reassoc_of% hh, ← hi₂, ← hV, Category.assoc]
  -- Stacks 0FBM at arbitrary rank for the closed immersion `Z ⟶ U` and the test scheme `V ⟶ U`
  set c := completedVirtualNormalGysinClass C sZ (U.ι ≫ sX) i' hi' (𝒩.toOpenFactor rfl)
  have H := completedVirtualNormalGysinCap_fundamentalChowClass_excess C sZ (U.ι ≫ sX) i' hi'
    (𝒩.toOpenFactor rfl) (g ∣_ U) iV g' sqV sZ' hiV hregV r n hdimV
  -- the degree-`q` part of `c ∘ (U ⟶ X)^*` caps as the degree-`q` part of `c` on `V`
  have hdeg : ∀ q : ℤ, (completedBivariantSequenceOfInvertible C sZ sX (i' ≫ U.ι) hi
      (completedVirtualNormalGysinClassOfOpen C sZ sX (i' ≫ U.ι) hi U i' rfl 𝒩) q).cap g n
        (fundamentalChowClass C (g ≫ sX) n) ≍
      chowPushforwardOfIso C (pullback.fst i' (pullback.fst U.ι g) ≫ sZ)
        (pullback.fst (i' ≫ U.ι) g ≫ sZ) (pullbackRightPullbackFstIso U.ι g i').hom
        (pullbackRightPullbackFstIso_hom_comp_fst_comp sZ i' U.ι g) (n - q)
        (chowPushforwardOfIso C (pullback.fst i' (g ∣_ U) ≫ sZ)
          (pullback.fst i' (pullback.fst U.ι g) ≫ sZ)
          (testBaseChangeIso i' (g ∣_ U) ((pullbackSymmetry U.ι g) ≪≫
            (pullbackRestrictIsoRestrict g U)).hom (pullback.fst U.ι g)
            (by simp [pullbackRestrictIsoRestrict_hom_morphismRestrict])).inv
          (by rw [Iso.inv_comp_eq]; simp) (n - q)
          ((completedBivariantSequenceOfInvertible C sZ (U.ι ≫ sX) i' hi' c q).cap (g ∣_ U) n
            (fundamentalChowClass C (g ∣_ U ≫ (U.ι ≫ sX)) n))) := by
    intro q
    refine (cap_completedSequence_completedOpenImmersionComposite_heq C sZ sX U i' hi' hi c q
      g n _).trans ?_
    rw [BivariantClass.cap_fundamentalChowClass_preimage C sZ sX U i' hi' _ g n hY]
  -- the excess normal sheaves of `Z' ⟶ V` and of `Z' ⟶ Y` agree
  have hσ : ((𝒩.toOpenFactor rfl).baseChange i' iV g' (g ∣_ U) sqV).conormalSurjection =
      (𝒩.baseChange _ i₂ g' g sq).conormalSurjection ≫
        (immersionConormalSheafFactorIso (g ⁻¹ᵁ U) iV hV).hom :=
    (VirtualNormalBundle.toOpenFactor_baseChange_surjection rfl hV 𝒩 sq hh sqV).symm
  have : @Mono Z'.Modules _ _ _ (immersionConormalSheafFactorIso (g ⁻¹ᵁ U) iV hV).hom :=
    @IsIso.mono_of_iso _ _ _ _ _ (Iso.isIso_hom _)
  refine ⟨fun e ↦ eq_of_heq ((hdeg _).trans (heq_of_eq ?_)), fun p hp ↦
    eq_of_heq ((hdeg p).trans (heq_of_eq ?_))⟩
  · have : IsLocallyNoetherian Z' := LocallyOfFiniteType.isLocallyNoetherian sZ'
    have : SheafOfModules.IsFiniteLocallyFree.{u, u, u}
        ((𝒩.toOpenFactor rfl).baseChange i' iV g' (g ∣_ U) sqV).excessNormalSheaf :=
      ((𝒩.toOpenFactor rfl).baseChange i' iV g' (g ∣_ U) sqV).isFiniteLocallyFree_excessNormalSheaf
        (SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree _ r)
    rw [H.1 e, topChernCap_congr C sZ'
      (E := ((𝒩.toOpenFactor rfl).baseChange i' iV g' (g ∣_ U) sqV).excessNormalSheaf)
      (E' := (𝒩.baseChange _ i₂ g' g sq).excessNormalSheaf)
      ((dualFunctor Z').mapIso (kernelIsoOfEq hσ ≪≫ kernelCompMono _ _).op).symm,
      chowPushforwardOfIso_comp_apply, chowPushforwardOfIso_comp_apply]
    refine chowPushforwardOfIso_congr_apply C _ _ _ _ ?_ _ _ _ _
    refine pullback.hom_ext ?_ ?_
    · simp [testBaseChangeIso]
    · simp [testBaseChangeIso, hV]
  · rw [H.2 p hp, map_zero, map_zero]

end CompletedExcess

/-! ### The counterpart of Stacks 0FEA -/

section CohenMacaulay

variable (𝒩 : VirtualNormalBundle i) (r : ℕ)
  [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} 𝒩.bundle r]

/-- **The counterpart of Stacks 0FEA for immersions.** Let `i : Z ⟶ X` be an immersion with a
virtual normal bundle `𝒩`, let `g : Y ⟶ X` be locally of finite type, and given integers `r` and
`n` assume

1. `𝒩` is locally free of rank `r`,
2. every irreducible component of `Y` has `δ`-dimension `n`,
3. `dim_δ(Z ×_X Y) ≤ n - r`, and
4. `𝒪_{Y, ξ}` is Cohen–Macaulay for every `ξ ∈ Z ×_X Y` with `δ(ξ) = n - r`.

Then `c(Z ⟶ X, 𝒩) ∩ [Y]_n = [Z ×_X Y]_{n - r}`, for `c(Z ⟶ X, 𝒩) = c(Z ⟶ U, 𝒩) ∘ (U ⟶ X)^*`.

On `V = g⁻¹(U)` the four hypotheses hold for the closed immersion `Z ⟶ U` and `V ⟶ U`: the
irreducible components of the open `V` are pure of `δ`-dimension `n`, `Z ×_U V = Z ×_X Y`, and the
local rings of `V` are those of `Y`. So this is Stacks 0FEA
(`Stacks.Chow.virtualNormalGysinClass_cap_fundamentalChowClass_of_isCohenMacaulayLocalRing`) for
`Z ⟶ U`, and `[Y]_n` restricts to `[V]_n`. -/
@[stacks 0FBQ "(3), counterparts: the counterpart of Lemma 0FEA, c(Z → X, N) ∩ [Y]_n = \
[Z ×_X Y]_{n-r} for an immersion Z → X, N locally free of rank r, Y pure of δ-dimension n, \
dim_δ(Z ×_X Y) ≤ n - r and O_{Y,ξ} Cohen-Macaulay at the points of Z ×_X Y of δ = n - r"]
theorem virtualNormalGysinClassOfOpen_cap_fundamentalChowClass_of_isCohenMacaulayLocalRing
    {n : ℤ} {Y : Scheme.{u}} (g : Y ⟶ X) [LocallyOfFiniteType g]
    (hY : ∀ W : irreducibleComponents Y,
      deltaDimension C (g ≫ sX)
        ⟨W, W.2.1, isClosed_of_mem_irreducibleComponents (W : Set Y) W.2⟩ = n)
    (hZY : schemeDeltaDimension C (pullback.snd i g ≫ (g ≫ sX)) ≤ ((n - r : ℤ) : EInt))
    (hCM : ∀ ξ : (pullback i g : Scheme.{u}),
      relativeDimension C.dimensionFunction (g ≫ sX) ((pullback.snd i g).base ξ) = n - r →
      letI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian (g ≫ sX)
      IsCohenMacaulayLocalRing (Y.presheaf.stalk ((pullback.snd i g).base ξ))) :
    (virtualNormalGysinClassOfOpen C sZ sX i hi U i' hU 𝒩 r).cap g n
        (fundamentalChowClass C (g ≫ sX) n) =
      fundamentalChowClass C (pullback.fst i g ≫ sZ) (n - r) := by
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian (g ≫ sX)
  subst hU
  have hi' := openFactor_comp_structureMorphism C sZ sX _ hi rfl
  have sq : IsPullback (pullback.snd (i' ≫ U.ι) g) (pullback.fst (i' ≫ U.ι) g) g (i' ≫ U.ι) :=
    (IsPullback.of_hasPullback (i' ≫ U.ι) g).flip
  -- the open `V = g⁻¹(U)` of `Y` and the closed factor `iV` of `Z ×_X Y ⟶ Y`
  obtain ⟨iV, hV, sqV, _⟩ := exists_closedFactor_preimage sq
  have hh : g ∣_ U ≫ U.ι = (g ⁻¹ᵁ U).ι ≫ g := morphismRestrict_ι g U
  -- `Z ×_U V ≅ Z ×_X Y`
  have hΨ : sqV.flip.isoPullback.inv ≫ pullback.snd (i' ≫ U.ι) g =
      pullback.snd i' (g ∣_ U) ≫ (g ⁻¹ᵁ U).ι := by
    rw [← hV, ← Category.assoc, IsPullback.isoPullback_inv_snd]
  have hYV := deltaDimension_irreducibleComponents_opens C (g ≫ sX) hY (g ⁻¹ᵁ U)
  have hstr : g ∣_ U ≫ (U.ι ≫ sX) = (g ⁻¹ᵁ U).ι ≫ (g ≫ sX) := by rw [reassoc_of% hh]
  have hYV' : ∀ W : irreducibleComponents (g ⁻¹ᵁ U).toScheme,
      deltaDimension C (g ∣_ U ≫ (U.ι ≫ sX))
        ⟨W, W.2.1, isClosed_of_mem_irreducibleComponents (W : Set (g ⁻¹ᵁ U).toScheme) W.2⟩ = n :=
    fun W ↦ by convert hYV W using 2
  have hZV : schemeDeltaDimension C (pullback.snd i' (g ∣_ U) ≫ (g ∣_ U ≫ (U.ι ≫ sX))) ≤
      ((n - r : ℤ) : EInt) :=
    schemeDeltaDimension_le_of_isOpenImmersion C (pullback.snd (i' ≫ U.ι) g ≫ (g ≫ sX)) _
      sqV.flip.isoPullback.inv (by rw [reassoc_of% hΨ, hstr]) hZY
  have hCMV : ∀ ξ : (pullback i' (g ∣_ U) : Scheme.{u}),
      relativeDimension C.dimensionFunction (g ∣_ U ≫ (U.ι ≫ sX))
          ((pullback.snd i' (g ∣_ U)).base ξ) = n - r →
      let : IsLocallyNoetherian (g ⁻¹ᵁ U).toScheme :=
        LocallyOfFiniteType.isLocallyNoetherian (g ∣_ U ≫ (U.ι ≫ sX))
      IsCohenMacaulayLocalRing ((g ⁻¹ᵁ U).toScheme.presheaf.stalk
        ((pullback.snd i' (g ∣_ U)).base ξ)) := by
    intro ξ hξ
    have hpt : (pullback.snd (i' ≫ U.ι) g).base (sqV.flip.isoPullback.inv.base ξ) =
        (g ⁻¹ᵁ U).ι.base ((pullback.snd i' (g ∣_ U)).base ξ) := by
      rw [← Scheme.Hom.comp_apply, hΨ, Scheme.Hom.comp_apply]
    have hrel : relativeDimension C.dimensionFunction (g ≫ sX)
        ((pullback.snd (i' ≫ U.ι) g).base (sqV.flip.isoPullback.inv.base ξ)) = n - r := by
      rw [hpt, ← relativeDimension_comp_isOpenImmersion, ← hstr]
      exact hξ
    have h := hCM _ hrel
    rw [hpt] at h
    exact (isCohenMacaulayLocalRing_iff_of_ringEquiv (asIso ((g ⁻¹ᵁ U).ι.stalkMap
      ((pullback.snd i' (g ∣_ U)).base ξ))).commRingCatIsoToRingEquiv).1 h
  -- Stacks 0FEA for the closed immersion `Z ⟶ U` and the test scheme `V ⟶ U`
  have H := virtualNormalGysinClass_cap_fundamentalChowClass_of_isCohenMacaulayLocalRing C sZ
    (U.ι ≫ sX) i' hi' (𝒩.toOpenFactor rfl) r (g ∣_ U) hYV' hZV hCMV
  refine eq_of_heq ((virtualNormalGysinClassOfOpen_cap_heq C sZ sX _ hi U i' rfl 𝒩 r g n
    _).trans (heq_of_eq ?_))
  have hYn : schemeDeltaDimension C (g ≫ sX) ≤ (n : EInt) := by
    rw [schemeDeltaDimension_eq_iSup]
    exact iSup_le fun W ↦ WithBotTop.coe_le_coe.mpr (hY W).le
  rw [BivariantClass.cap_fundamentalChowClass_preimage C sZ sX U i' hi' _ g n hYn, H,
    chowPushforwardOfIso_fundamentalChowClass, chowPushforwardOfIso_fundamentalChowClass]

end CohenMacaulay

/-! ### The counterpart of Stacks 0FBL at arbitrary rank -/

section CompletedTopChern

variable (𝒩 𝒩' : VirtualNormalBundle i) (Eb : Z.Modules)
  [SheafOfModules.IsFiniteLocallyFree.{u, u, u} Eb] (inc : 𝒩'.bundle ⟶ 𝒩.bundle)
  (pr : 𝒩.bundle ⟶ Eb)

/-- **The counterpart of Stacks 0FBL for immersions, at arbitrary rank.** Let `i : Z ⟶ X` be an
immersion with a virtual normal bundle `𝒩`, and let `0 ⟶ 𝒩' ⟶ 𝒩 ⟶ ℰ ⟶ 0` be a short exact
sequence of finite locally free `𝒪_Z`-modules, of arbitrary ranks, such that the surjection
`σ : 𝒩^∨ ⟶ 𝒞_{Z/X}` factors as `σ' ∘ (𝒩^∨ ⟶ (𝒩')^∨)` through that of `𝒩'`. Then

  `c(Z ⟶ X, 𝒩) = c_top(ℰ) ∘ c(Z ⟶ X, 𝒩')`

in `A^*(Z ⟶ X)^∧`, both classes built from the same open `U`. By Stacks 0FBL at arbitrary rank
(`Stacks.Chow.completedVirtualNormalGysinClass_eq_of_isTopChernComposition`) for `Z ⟶ U` and the
associativity of the composition on completions (Stacks 0FE0). -/
@[stacks 0FBQ "(3), counterparts: the counterpart of Lemma 0FBL in A^*(Z → X)^∧, c(Z → X, N) = \
c_top(E) ∘ c(Z → X, N') for an immersion Z → X and a short exact sequence 0 → N' → N → E → 0 of \
finite locally free modules of arbitrary rank whose surjection factors through that of N'"]
theorem completedVirtualNormalGysinClassOfOpen_eq_of_isTopChernComposition
    (w : inc ≫ pr = 0) (hseq : (ShortComplex.mk inc pr w).ShortExact)
    (hsigma : dualMap inc ≫ 𝒩'.surjection = 𝒩.surjection) :
    haveI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
    haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
    completedVirtualNormalGysinClassOfOpen C sZ sX i hi U i' hU 𝒩 =
      completedBivariantGroup.copy C (Category.id_comp i) _ hi
        (completedBivariantCompositeOfInvertible C sZ sZ sX (𝟙 Z) i (Category.id_comp sZ) hi
          (topChernClassOfInvertible C sZ Eb)
          (completedVirtualNormalGysinClassOfOpen C sZ sX i hi U i' hU 𝒩'))
    := by
  have : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  have : IsLocallyNoetherian U.toScheme := LocallyOfFiniteType.isLocallyNoetherian (U.ι ≫ sX)
  have hi' := openFactor_comp_structureMorphism C sZ sX i hi hU
  -- the completed composite respects heterogeneous equality of its factors
  have congr : ∀ {A B D : Scheme.{u}} {sA : A ⟶ C.S} [LocallyOfFiniteType sA] {sB : B ⟶ C.S}
      [LocallyOfFiniteType sB] {sD : D ⟶ C.S} [LocallyOfFiniteType sD] [IsLocallyNoetherian A]
      [IsLocallyNoetherian B] [IsLocallyNoetherian D] {f f' : A ⟶ B} [LocallyOfFiniteType f]
      [LocallyOfFiniteType f'] {g g' : B ⟶ D} [LocallyOfFiniteType g] [LocallyOfFiniteType g']
      (_ : f = f') (_ : g = g') {hf : f ≫ sB = sA} {hf' : f' ≫ sB = sA} {hg : g ≫ sD = sB}
      {hg' : g' ≫ sD = sB}
      {a : completedBivariantGroup C (gysinSystemOfInvertible C) sA sB f hf}
      {a' : completedBivariantGroup C (gysinSystemOfInvertible C) sA sB f' hf'}
      {b : completedBivariantGroup C (gysinSystemOfInvertible C) sB sD g hg}
      {b' : completedBivariantGroup C (gysinSystemOfInvertible C) sB sD g' hg'} (_ : a ≍ a')
      (_ : b ≍ b'),
      completedBivariantCompositeOfInvertible C sA sB sD f g hf hg a b ≍
        completedBivariantCompositeOfInvertible C sA sB sD f' g' hf' hg' a' b' := by
    intro A B D sA _ sB _ sD _ _ _ _ f f' _ _ g g' _ _ hff' hgg' hf hf' hg hg' a a' b b' ha hb
    subst hff' hgg'
    cases ha
    cases hb
    rfl
  -- Stacks 0FBL at arbitrary rank for the closed immersion `Z ⟶ U`
  have hL := completedVirtualNormalGysinClass_eq_of_isTopChernComposition C sZ (U.ι ≫ sX) i' hi'
    (𝒩.toOpenFactor hU) (𝒩'.toOpenFactor hU) Eb inc pr w hseq
    ((Category.assoc _ _ _).symm.trans
      (congrArg (· ≫ (immersionConormalSheafFactorIso U i' hU).hom) hsigma))
  refine eq_of_heq ((completedBivariantGroup.copy_heq C _ _ _ _).trans ?_)
  refine HEq.trans ?_ (completedBivariantGroup.copy_heq C _ _ _ _).symm
  refine (congr (Category.id_comp i').symm rfl ((heq_of_eq hL).trans
    (completedBivariantGroup.copy_heq C _ _ _ _)) HEq.rfl).trans ?_
  refine (completedBivariantCompositeOfInvertible_assoc C sZ sZ (U.ι ≫ sX) sX (𝟙 Z) i' U.ι
    (Category.id_comp sZ) hi' rfl _ _ _).trans ?_
  exact congr rfl hU HEq.rfl (completedBivariantGroup.copy_heq C _ _ _ _).symm

end CompletedTopChern

end Stacks.Chow

end
