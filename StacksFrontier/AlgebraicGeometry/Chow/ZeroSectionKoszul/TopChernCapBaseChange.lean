module

public import StacksFrontier.AlgebraicGeometry.Chow.ZeroSectionKoszul.TopChernCap
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.DualSectionsInfinitesimal

/-!
# The top Chern class of `π^*𝒞 ⊗ 𝒪(-1)` after a base change

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `X` be locally of
finite type over `S`, let `𝒞` be a finite locally free `𝒪_X`-module of rank `r`, and let
`π : E = 𝐏(𝒞 ⊕ 𝒪_X) ⟶ X` be the projective completion of the vector bundle `C`, with
`V ⊆ E` the complement of the divisor at infinity. Let `g : X' ⟶ X` be locally of finite type
and form the fibre product `E' = X' ×_X E`, with projections `π' : E' ⟶ X'` and `q : E' ⟶ E`,
the open `V' = q⁻¹(V)` and `p' : V' ⟶ X'`. The module `ℰ' = q^*(π^*𝒞 ⊗ 𝒪_E(-1))` is the
module `π'^*(g^*𝒞) ⊗ (q^*𝒪_E(1))^∨`, and the computation of
`StacksFrontier.AlgebraicGeometry.Chow.ZeroSectionKoszul.TopChernCap` holds on `E'`: for every
`α ∈ CH_*(E')`,

  `p'^*(π'_*(c_r(ℰ') ∩ α)) = (-1)^r α|_{V'}`.

This is the cap-product computation of the proof of Stacks 0FEF on the test scheme `q : E' ⟶ E`
("after replacing `X` by a scheme locally of finite type over `X`").

## The proof

The morphism `π'` is a locally projective tower of fibre dimension `r` with twist `q^*𝒪_E(1)`, so
by `Stacks.Chow.flatPullback_pushforward_chernCap_tensorDual` it suffices to show:

* `ξ' ∩ c_r(ℰ') ∩ π'^*β = 0` for `ξ' = c₁(q^*𝒪_E(1))`. The projective bundle of
  `g^*𝒞 ⊕ 𝒪_{X'}` is isomorphic to `E'` over `X'` compatibly with the twists (Stacks 01O3), so
  the relation of Stacks 02U6 for `g^*𝒞 ⊕ 𝒪_{X'}` holds on `E'` with `ξ'`; this gives the
  vanishing exactly as on `E` itself
  (`Stacks.Chow.capOnChow_chernCap_tensorDual_bundlePullback_of_relation`).
* `(ξ' ∩ y)|_{V'} = 0`. The pullback of the section of `𝒪_E(1)` cutting out the divisor at
  infinity is a section of `q^*𝒪_E(1)` whose zero scheme is the inverse image of that divisor
  (Stacks 0B6Y), which is the complement of `V'`; then Stacks 02T9 and 02RX apply.

## Main results

* `Stacks.Chow.relativeDimension_pullback_fst_projectiveCompletionProj` — `π'` has relative
  dimension `r`.
* `Stacks.Chow.relativeDimension_complementOpenBaseChange` — so has `p' : V' ⟶ X'`.
* `Stacks.Chow.pullbackKoszulModuleIso` — `q^*(π^*𝒞 ⊗ 𝒪_E(-1)) ≅ π'^*(g^*𝒞) ⊗ (q^*𝒪_E(1))^∨`.
* `Stacks.Chow.capOnChow_chernCap_koszulModule_baseChange` — `ξ' ∩ c_r(ℰ') ∩ π'^*β = 0`.
* `Stacks.Chow.restrict_complementOpenBaseChange_capOnChow` — `(ξ' ∩ y)|_{V'} = 0`.
* `Stacks.Chow.flatPullback_pushforward_chernCap_koszulModule_baseChange` — the identity
  displayed above.

## References

* [Stacks Project, Tag 0FEF](https://stacks.math.columbia.edu/tag/0FEF)
* [Stacks Project, Tag 01O3](https://stacks.math.columbia.edu/tag/01O3)
* [Stacks Project, Tag 02U6](https://stacks.math.columbia.edu/tag/02U6)
* [Stacks Project, Tag 0B6Y](https://stacks.math.columbia.edu/tag/0B6Y)
* [Stacks Project, Tag 02T9](https://stacks.math.columbia.edu/tag/02T9)
* [Stacks Project, Tag 02RX](https://stacks.math.columbia.edu/tag/02RX)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.AlgebraicGeometry.ReflexiveModules
open Stacks.ProjectiveCompletion

universe u

namespace Stacks.Chow

variable (C : ChowSituation.{u}) {X X' : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (sX' : X' ⟶ C.S) [LocallyOfFiniteType sX'] (g : X' ⟶ X) [LocallyOfFiniteType g]
  (hg : g ≫ sX = sX') (𝒞 : X.Modules) (r : ℕ)
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} 𝒞 r]
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} 𝒞]
  [Flat (projectiveCompletionProj 𝒞)] [LocallyOfFiniteType (projectiveCompletionProj 𝒞)]

/-! ### The base-changed tower -/

omit [LocallyOfFiniteType sX] [LocallyOfFiniteType sX'] [LocallyOfFiniteType g]
    [Flat (projectiveCompletionProj 𝒞)] [LocallyOfFiniteType (projectiveCompletionProj 𝒞)] in
include sX hg in
/-- The structure morphism of `E' = X' ×_X E`, read through either projection. -/
theorem pullback_fst_comp_eq_pullback_snd_comp :
    pullback.fst g (projectiveCompletionProj 𝒞) ≫ sX' =
      pullback.snd g (projectiveCompletionProj 𝒞) ≫ projectiveCompletionProj 𝒞 ≫ sX := by
  rw [← hg, pullback.condition_assoc]

omit [LocallyOfFiniteType g] [Flat (projectiveCompletionProj 𝒞)] in
/-- The projection `π' : X' ×_X E ⟶ X'` has relative dimension `r`. -/
theorem relativeDimension_pullback_fst_projectiveCompletionProj :
    AlgebraicGeometry.RelativeDimension (pullback.fst g (projectiveCompletionProj 𝒞)) r :=
  AlgebraicGeometry.RelativeDimension.of_isPullback (IsPullback.of_hasPullback g _).flip
    (relativeDimension_projectiveCompletionProj' 𝒞 r)

/-- The open `V' = q⁻¹(V)` of `E' = X' ×_X E`, the base change of the complement `V` of the
divisor at infinity. -/
abbrev complementOpenBaseChange : (pullback g (projectiveCompletionProj 𝒞)).Opens :=
  pullback.snd g (projectiveCompletionProj 𝒞) ⁻¹ᵁ complementOpen 𝒞

omit [LocallyOfFiniteType g] [Flat (projectiveCompletionProj 𝒞)] in
/-- The projection `p' : V' ⟶ X'` has relative dimension `r`: it is the base change of
`p : V ⟶ X`. -/
theorem relativeDimension_complementOpenBaseChange :
    AlgebraicGeometry.RelativeDimension
      ((complementOpenBaseChange g 𝒞).ι ≫ pullback.fst g (projectiveCompletionProj 𝒞)) r :=
  AlgebraicGeometry.RelativeDimension.of_isPullback
    ((isPullback_morphismRestrict (pullback.snd g (projectiveCompletionProj 𝒞))
      (complementOpen 𝒞)).paste_vert (IsPullback.of_hasPullback g _).flip)
    (relativeDimension_complementOpen_ι_comp 𝒞 r)

/-- **The module `q^*(π^*𝒞 ⊗ 𝒪_E(-1))` on `E' = X' ×_X E`** is `π'^*(g^*𝒞) ⊗ (q^*𝒪_E(1))^∨`:
pullback commutes with tensor products (Stacks 01CD) and with duals of finite locally free
modules, and `q^*π^* = π'^*g^*`. -/
def pullbackKoszulModuleIso :
    (Scheme.Modules.pullback (pullback.snd g (projectiveCompletionProj 𝒞))).obj
        (koszulModule 𝒞) ≅
      ((Stacks.SheafOfModules.Tensor.sheafTensor
          (pullback g (projectiveCompletionProj 𝒞)).sheaf).obj
        ((Scheme.Modules.pullback (pullback.fst g (projectiveCompletionProj 𝒞))).obj
          ((Scheme.Modules.pullback g).obj 𝒞))).obj
        (dualSheaf ((Scheme.Modules.pullback (pullback.snd g (projectiveCompletionProj 𝒞))).obj
          (bundleTwist (completionModule 𝒞)))) :=
  sheafTensorPullbackIso _ _ _ ≪≫
    sheafTensorMapIso (pullbackObjIsoOfComm pullback.condition.symm 𝒞)
      (Stacks.FundamentalGroup.pullbackDualSheafIso _ _
        (haveI := isFiniteLocallyFreeOfRank_one_of_isInvertible
          (bundleTwist (completionModule 𝒞))
        AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree _ 1))

/-! ### `ξ'` away from the base change of the divisor at infinity -/

/-- If a closed subscheme `Z` of `P` is the complement of an open `V`, then for every morphism
`f : Y ⟶ P` the inverse image `f⁻¹(Z)` is the complement of `f⁻¹(V)`. -/
theorem range_comap_subschemeι_eq_compl {P Y : Scheme.{u}} (f : Y ⟶ P) (I : P.IdealSheafData)
    (V : P.Opens) (hV : Set.range I.subschemeι.base = (Set.range V.ι.base)ᶜ) :
    Set.range (I.comap f).subschemeι.base = (Set.range (f ⁻¹ᵁ V).ι.base)ᶜ := by
  rw [Scheme.IdealSheafData.range_subschemeι] at hV ⊢
  rw [Scheme.IdealSheafData.support_comap, TopologicalSpace.Closeds.coe_preimage, hV]
  simp

omit [LocallyOfFiniteType g] [Flat (projectiveCompletionProj 𝒞)]
    [LocallyOfFiniteType (projectiveCompletionProj 𝒞)] in
/-- **The base change of the divisor at infinity is the complement of `V'`**: the zero scheme of
the pulled-back section `q^*s` of `q^*𝒪_E(1)` is `q⁻¹(Z(s))` (Stacks 0B6Y). -/
theorem range_zeroScheme_pullback_infinityTwistSection :
    Set.range (Stacks.Divisors.zeroScheme (pullback g (projectiveCompletionProj 𝒞))
      ((Scheme.Modules.pullback (pullback.snd g (projectiveCompletionProj 𝒞))).obj
        (bundleTwist (completionModule 𝒞)))
      (pullbackGlobalSections (pullback.snd g (projectiveCompletionProj 𝒞))
        (bundleTwist (completionModule 𝒞)) (infinityTwistSection 𝒞))).subschemeι.base =
      (Set.range (complementOpenBaseChange g 𝒞).ι.base)ᶜ :=
  (congrArg (fun I : (pullback g (projectiveCompletionProj 𝒞)).IdealSheafData ↦
    Set.range I.subschemeι.base) (Stacks.Divisors.zeroScheme_pullback _
      (bundleTwist (completionModule 𝒞)) (infinityTwistSection 𝒞))).trans
    (range_comap_subschemeι_eq_compl _ _ _ (range_infinityDivisor_eq_compl 𝒞))

omit [LocallyOfFiniteType g] [Flat (projectiveCompletionProj 𝒞)]
    [LocallyOfFiniteType (projectiveCompletionProj 𝒞)] in
/-- **`(ξ' ∩ y)|_{V'} = 0`** for `ξ' = c₁(q^*𝒪_E(1))` on `E' = X' ×_X E`: `ξ' ∩ y` is pushed
forward from the zero scheme of `q^*s` (Stacks 02T9), which is the complement of `V'`
(Stacks 02RX). -/
theorem restrict_complementOpenBaseChange_capOnChow
    (sP : pullback g (projectiveCompletionProj 𝒞) ⟶ C.S) [LocallyOfFiniteType sP] (d : ℤ)
    (y : chowGroup C sP (d + 1)) :
    chowGroupOpensRestrictOfIsOpenImmersion C sP (complementOpenBaseChange g 𝒞) d
      ((invCap C sP ((Scheme.Modules.pullback (pullback.snd g (projectiveCompletionProj 𝒞))).obj
        (bundleTwist (completionModule 𝒞)))).capOnChow C sP d y) = 0 :=
  restrict_capOnChow_eq_zero_of_range_zeroScheme C sP _
    (pullbackGlobalSections (pullback.snd g (projectiveCompletionProj 𝒞))
      (bundleTwist (completionModule 𝒞)) (infinityTwistSection 𝒞)) _
    (range_zeroScheme_pullback_infinityTwistSection g 𝒞) d y

/-! ### The relation of Stacks 02U6 on the base change -/

attribute [local instance] AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback

omit [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} 𝒞] in
/-- **`g^*(𝒞 ⊕ 𝒪_X) ≅ g^*𝒞 ⊕ 𝒪_{X'}`**: pullback preserves biproducts and `g^*𝒪_X ≅ 𝒪_{X'}`. -/
def completionModulePullbackIso :
    completionModule ((Scheme.Modules.pullback g).obj 𝒞) ≅
      (Scheme.Modules.pullback g).obj (completionModule 𝒞) :=
  haveI := preservesBinaryBiproducts_of_preservesBiproducts (Scheme.Modules.pullback g)
  let eU : (Scheme.Modules.pullback g).obj (Stacks.Ample.unitModule X) ≅
      Stacks.Ample.unitModule X' :=
    RingedSpaceModuleAdjunction.modulePullbackObjUnitIso g.toLRSHom.toShHom
  biprod.mapIso (Iso.refl _) eU.symm ≪≫
    ((Scheme.Modules.pullback g).mapBiprod 𝒞 (Stacks.Ample.unitModule X)).symm

include hg in
/-- **The relation of Stacks 02U6 for `g^*𝒞 ⊕ 𝒪_{X'}` holds on `E' = X' ×_X E`** with
`ξ' = c₁(q^*𝒪_E(1))`: the projective bundle `P'` of `g^*𝒞 ⊕ 𝒪_{X'}` is `E'` over `X'` with
`𝒪_{P'}(1)` the pullback of `q^*𝒪_E(1)` (Stacks 01O3), and the flat pullback along the
isomorphism `E' ≅ P'` carries the relation on `P'` to `E'`. -/
theorem projectiveBundleChernRelation_baseChange (m : ℤ) (β : chowGroup C sX' m) :
    ProjectiveBundleChernRelation C sX'
      (pullback.snd g (projectiveCompletionProj 𝒞) ≫ projectiveCompletionProj 𝒞 ≫ sX)
      (pullback.fst g (projectiveCompletionProj 𝒞))
      (pullback_fst_comp_eq_pullback_snd_comp C sX sX' g hg 𝒞) (r + 1)
      (relativeDimension_pullback_fst_projectiveCompletionProj g 𝒞 r)
      (fun k ↦ flatPullbackFactorsThroughRationalEquivalence_general C _ sX' _ _ _ _ k)
      (invCap C _ ((Scheme.Modules.pullback (pullback.snd g (projectiveCompletionProj 𝒞))).obj
        (bundleTwist (completionModule 𝒞))))
      m (bundleChernCapFamily (completionModule ((Scheme.Modules.pullback g).obj 𝒞)) r C sX' m
        β) := by
  have : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      ((Scheme.Modules.pullback g).obj 𝒞) :=
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree _ r
  have := flat_projectiveCompletionProj ((Scheme.Modules.pullback g).obj 𝒞) r
  have := locallyOfFiniteType_projectiveCompletionProj ((Scheme.Modules.pullback g).obj 𝒞) r
  obtain ⟨e, he, ⟨eT⟩⟩ := GenuineChern.bundleBaseChangeHolds g (completionModule 𝒞)
    (completionModule ((Scheme.Modules.pullback g).obj 𝒞)) (completionModulePullbackIso g 𝒞)
  have hcomm : e.inv ≫ projectiveCompletionProj ((Scheme.Modules.pullback g).obj 𝒞) =
      pullback.fst g (projectiveCompletionProj 𝒞) ≫ 𝟙 X' := by
    rw [Category.comp_id, Iso.inv_comp_eq]
    exact he.symm
  have hf' : e.inv ≫ (projectiveCompletionProj ((Scheme.Modules.pullback g).obj 𝒞) ≫ sX') =
      pullback.snd g (projectiveCompletionProj 𝒞) ≫ projectiveCompletionProj 𝒞 ≫ sX := by
    rw [← Category.assoc, hcomm, Category.comp_id,
      pullback_fst_comp_eq_pullback_snd_comp C sX sX' g hg 𝒞]
  have hd' : AlgebraicGeometry.RelativeDimension e.inv 0 := relativeDimension_of_isOpenImmersion _
  have hfacg := fun k ↦ flatPullbackFactorsThroughRationalEquivalence_general C _ _ e.inv hf' 0
    hd' k
  have eL : (Scheme.Modules.pullback (pullback.snd g (projectiveCompletionProj 𝒞))).obj
        (bundleTwist (completionModule 𝒞)) ≅
      (Scheme.Modules.pullback e.inv).obj
        (bundleTwist (completionModule ((Scheme.Modules.pullback g).obj 𝒞))) :=
    ((Scheme.Modules.pullbackCongr (show e.inv ≫ e.hom ≫ pullback.snd g _ =
      pullback.snd g (projectiveCompletionProj 𝒞) by simp)).app _).symm ≪≫
      ((Scheme.Modules.pullbackComp e.inv (e.hom ≫ pullback.snd g _)).app _).symm ≪≫
      (Scheme.Modules.pullback e.inv).mapIso eT
  have hcompat := chernTermsCompatibleWithFlatPullback_of_square C sX' sX'
    (pullback.snd g (projectiveCompletionProj 𝒞) ≫ projectiveCompletionProj 𝒞 ≫ sX)
    (projectiveCompletionProj ((Scheme.Modules.pullback g).obj 𝒞) ≫ sX')
    (pullback.fst g (projectiveCompletionProj 𝒞))
    (pullback_fst_comp_eq_pullback_snd_comp C sX sX' g hg 𝒞)
    (projectiveCompletionProj ((Scheme.Modules.pullback g).obj 𝒞)) rfl (r + 1)
    (relativeDimension_pullback_fst_projectiveCompletionProj g 𝒞 r)
    (relativeDimension_bundleProj (completionModule ((Scheme.Modules.pullback g).obj 𝒞)) r)
    (fun k ↦ flatPullbackFactorsThroughRationalEquivalence_general C _ sX' _ _ _ _ k)
    (fun k ↦ flatPullbackFactorsThroughRationalEquivalence_general C _ sX' _ rfl _ _ k)
    (invCap C _ ((Scheme.Modules.pullback (pullback.snd g (projectiveCompletionProj 𝒞))).obj
      (bundleTwist (completionModule 𝒞))))
    (bundleTwistCap (completionModule ((Scheme.Modules.pullback g).obj 𝒞)) C sX')
    (𝟙 X') (Category.id_comp sX') 0 (relativeDimension_identity X')
    (fun k ↦ flatPullbackFactorsThroughRationalEquivalence_id C sX' k) e.inv hf' hd' hfacg hcomm
    (fun j y y' hy ↦ flatPullbackChow_firstChernClassCapChow_heq C _ _ e.inv hf' 0 hd' hfacg
      (bundleTwist (completionModule ((Scheme.Modules.pullback g).obj 𝒞))) _ eL j y y' hy)
  have hrelA := flatPullback_projectiveBundleChernRelation C sX' sX'
    (pullback.snd g (projectiveCompletionProj 𝒞) ≫ projectiveCompletionProj 𝒞 ≫ sX)
    (projectiveCompletionProj ((Scheme.Modules.pullback g).obj 𝒞) ≫ sX')
    (pullback.fst g (projectiveCompletionProj 𝒞))
    (pullback_fst_comp_eq_pullback_snd_comp C sX sX' g hg 𝒞)
    (projectiveCompletionProj ((Scheme.Modules.pullback g).obj 𝒞)) rfl (r + 1)
    (relativeDimension_pullback_fst_projectiveCompletionProj g 𝒞 r)
    (relativeDimension_bundleProj (completionModule ((Scheme.Modules.pullback g).obj 𝒞)) r)
    _ _ _ _ (𝟙 X') (Category.id_comp sX') 0 (relativeDimension_identity X')
    (fun k ↦ flatPullbackFactorsThroughRationalEquivalence_id C sX' k) e.inv hf' hd' hfacg
    hcompat m _ (isChernCapFamily_bundleChernCapFamily
      (completionModule ((Scheme.Modules.pullback g).obj 𝒞)) r C sX' m β).2
  refine GenuineChern.projectiveBundleChernRelation_congr C sX' _
    (pullback.fst g (projectiveCompletionProj 𝒞)) _ (r + 1) _ _ _
    (show m + ((0 : ℕ) : ℤ) = m by simp) _ _ (fun j ↦ ?_) hrelA
  simp only [flatPullbackChernFamily]
  refine (chowGroupCast_heq C sX' _ _).trans ?_
  rw [flatPullbackChow_id]
  exact chowGroupCast_heq C sX' _ _

include hg in
/-- **`ξ' ∩ c_r(ℰ') ∩ π'^*β = 0` on `E' = X' ×_X E`**, for `ℰ' = q^*(π^*𝒞 ⊗ 𝒪_E(-1))` and
`ξ' = c₁(q^*𝒪_E(1))`: the relation of Stacks 02U6 for `g^*𝒞 ⊕ 𝒪_{X'}` on `E'`
(`Stacks.Chow.projectiveBundleChernRelation_baseChange`), read through Stacks 02UG and 02UD. -/
theorem capOnChow_chernCap_koszulModule_baseChange (m d : ℤ) (hd : m + r - r = d + 1)
    (β : chowGroup C sX' m) :
    (invCap C _ ((Scheme.Modules.pullback (pullback.snd g (projectiveCompletionProj 𝒞))).obj
        (bundleTwist (completionModule 𝒞)))).capOnChow C
      (pullback.snd g (projectiveCompletionProj 𝒞) ≫ projectiveCompletionProj 𝒞 ≫ sX) d
      (chowGroupCast C _ hd (GenuineChern.chernCap C r
        (pullback.snd g (projectiveCompletionProj 𝒞) ≫ projectiveCompletionProj 𝒞 ≫ sX)
        ((Scheme.Modules.pullback (pullback.snd g (projectiveCompletionProj 𝒞))).obj
          (koszulModule 𝒞)) (m + r) (Fin.last r)
        (bundlePullback C sX' _ (pullback.fst g (projectiveCompletionProj 𝒞))
          (pullback_fst_comp_eq_pullback_snd_comp C sX sX' g hg 𝒞) r
          (relativeDimension_pullback_fst_projectiveCompletionProj g 𝒞 r) m β))) = 0 :=
  capOnChow_chernCap_tensorDual_bundlePullback_of_relation C sX' _ _
    (pullback_fst_comp_eq_pullback_snd_comp C sX sX' g hg 𝒞) r
    (relativeDimension_pullback_fst_projectiveCompletionProj g 𝒞 r) _ _ _
    (pullbackKoszulModuleIso g 𝒞) m d hd β
    (projectiveBundleChernRelation_baseChange C sX sX' g hg 𝒞 r m β)

/-! ### The cap-product identity on the base change -/

omit [LocallyOfFiniteType g] [Flat (projectiveCompletionProj 𝒞)]
    [LocallyOfFiniteType (projectiveCompletionProj 𝒞)] in
/-- **`π' : X' ×_X E ⟶ X'` is a locally projective tower** of fibre dimension `r` with twist
`q^*𝒪_E(1)`: so is `π`, and locally projective towers are stable under base change. -/
theorem isLocallyProjectiveTower_pullback_fst_projectiveCompletionProj :
    IsLocallyProjectiveTower r (pullback.fst g (projectiveCompletionProj 𝒞))
      ((Scheme.Modules.pullback (pullback.snd g (projectiveCompletionProj 𝒞))).obj
        (bundleTwist (completionModule 𝒞))) :=
  (isLocallyProjectiveTower_bundle (completionModule 𝒞) r).of_isPullback
    (IsPullback.of_hasPullback g _).flip (Iso.refl _)

include hg in
/-- **The cap-product identity of Stacks 0FEF on the test scheme `q : E' = X' ×_X E ⟶ E`,
before the Koszul resolution.** For `g : X' ⟶ X` locally of finite type and every
`α ∈ CH_{k+r}(E')`,

  `p'^*(π'_*(c_r(q^*(π^*𝒞 ⊗ 𝒪_E(-1))) ∩ α)) = (-1)^r α|_{V'}`

in `CH_{k+r}(V')`, where `π' : E' ⟶ X'` is the projection, `V' = q⁻¹(V)` the base change of the
complement of the divisor at infinity and `p' : V' ⟶ X'`. -/
theorem flatPullback_pushforward_chernCap_koszulModule_baseChange (k : ℤ)
    (α : chowGroup C (pullback.snd g (projectiveCompletionProj 𝒞) ≫ projectiveCompletionProj 𝒞 ≫
      sX) (k + r)) :
    chowGroupCast C _ (by ring) (bundlePullback C sX'
      ((complementOpenBaseChange g 𝒞).ι ≫ pullback.snd g (projectiveCompletionProj 𝒞) ≫
        projectiveCompletionProj 𝒞 ≫ sX)
      ((complementOpenBaseChange g 𝒞).ι ≫ pullback.fst g (projectiveCompletionProj 𝒞))
      (by rw [Category.assoc, pullback_fst_comp_eq_pullback_snd_comp C sX sX' g hg 𝒞]) r
      (relativeDimension_complementOpenBaseChange g 𝒞 r) (k + r - r)
      (properChowPushforward C
        (pullback.snd g (projectiveCompletionProj 𝒞) ≫ projectiveCompletionProj 𝒞 ≫ sX) sX'
        (pullback.fst g (projectiveCompletionProj 𝒞))
        (pullback_fst_comp_eq_pullback_snd_comp C sX sX' g hg 𝒞) (k + r - r)
        (properPushforwardFactorsThroughRationalEquivalence_of_isProper C _ sX' _
          (pullback_fst_comp_eq_pullback_snd_comp C sX sX' g hg 𝒞) _)
        (GenuineChern.chernCap C r
          (pullback.snd g (projectiveCompletionProj 𝒞) ≫ projectiveCompletionProj 𝒞 ≫ sX)
          ((Scheme.Modules.pullback (pullback.snd g (projectiveCompletionProj 𝒞))).obj
            (koszulModule 𝒞)) (k + r) (Fin.last r) α))) =
      ((-1 : ℤ) ^ r) • chowGroupOpensRestrictOfIsOpenImmersion C
        (pullback.snd g (projectiveCompletionProj 𝒞) ≫ projectiveCompletionProj 𝒞 ≫ sX)
        (complementOpenBaseChange g 𝒞) (k + r) α :=
  flatPullback_pushforward_chernCap_tensorDual C sX' _ _
    (pullback_fst_comp_eq_pullback_snd_comp C sX sX' g hg 𝒞) r
    (relativeDimension_pullback_fst_projectiveCompletionProj g 𝒞 r) _
    ((Scheme.Modules.pullback g).obj 𝒞) _ (complementOpenBaseChange g 𝒞)
    (relativeDimension_complementOpenBaseChange g 𝒞 r)
    (isLocallyProjectiveTower_pullback_fst_projectiveCompletionProj g 𝒞 r)
    (pullbackKoszulModuleIso g 𝒞) (capOnChow_chernCap_koszulModule_baseChange C sX sX' g hg 𝒞 r)
    (restrict_complementOpenBaseChange_capOnChow C g 𝒞 _) k α

end Stacks.Chow

end
