module

public import StacksFrontier.AlgebraicGeometry.Chow.BivariantComposition.OpenImmersionComposite
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.CompletedOpenImmersionComposite
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.CompletedVirtualNormalBundleClass
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.VirtualNormalBundleClassConstruction
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.VirtualNormalBundleClassOpenFactor
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.VirtualNormalBundleOpenFactor
public import StacksFrontier.AlgebraicGeometry.ConormalComparison.Factorization
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantClassCopy

/-!
# The bivariant class of a virtual normal bundle of an immersion

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `X` be locally of
finite type over `S`, let `i : Z ⟶ X` be an immersion and let `𝒩` be a virtual normal bundle for
`i` (Stacks 0FBQ (2)). Stacks 0FBQ (3) chooses an open subscheme `U ⊆ X` such that `i` factors
through a closed immersion `i' : Z ⟶ U`, and sets

  `c(Z ⟶ X, 𝒩) = c(Z ⟶ U, 𝒩) ∘ (U ⟶ X)^*`,

where `c(Z ⟶ U, 𝒩)` is the class of Stacks 0FBK for the closed immersion `i'` and `(U ⟶ X)^*` is
flat pullback along the open immersion (Stacks 0B78), composed as in Stacks 0B75.

## Main definitions

* `Stacks.Chow.virtualNormalGysinClassOfOpen` — the class `c(Z → U, 𝒩) ∘ (U → X)^*` of
  Stacks 0FBQ (3) in `A^r(Z ⟶ X)`, built from a choice of `U`, for `𝒩` of constant rank `r`.
* `Stacks.Chow.immersionVirtualNormalGysinClass` — the same at the canonical choice
  `U = AlgebraicGeometry.Scheme.Hom.coborderRange i`.
* `Stacks.Chow.completedVirtualNormalGysinClassOfOpen`,
  `Stacks.Chow.completedVirtualNormalGysinClassOfImmersion` — **Stacks 0FBQ (3)** for `𝒩` of
  arbitrary rank, in `A^*(Z ⟶ X)^∧`.

## Main results

* `Stacks.Chow.virtualNormalGysinClassOfOpen_cap_heq` — the class caps by restricting to
  `U ×_X T` and capping there with `c(Z → U, 𝒩)`.
* `Stacks.Chow.virtualNormalGysinClassOfOpen_independent` — the class does not depend on the
  choice of `U`, for `𝒩` of constant rank; with
  `Stacks.Chow.virtualNormalGysinClassOfOpen_eq_immersionVirtualNormalGysinClass`, every choice
  gives the canonical class.
* `Stacks.Chow.completedVirtualNormalGysinClassOfOpen_independent` — **Stacks 0FBQ (3)**: the
  class in `A^*(Z ⟶ X)^∧` does not depend on the choice of `U`, for `𝒩` of arbitrary rank.

## Implementation notes

The statements registered under Stacks 0FBQ (3) are those for `𝒩` of arbitrary rank, in
`A^*(Z ⟶ X)^∧`; the constant-rank ones are the steps towards them.

The independence of the choice of `U` asserted by Stacks 0FBQ, for `𝒩` of constant rank, is
`Stacks.Chow.virtualNormalGysinClassOfOpen_independent`: every admissible `U` lies in
`i.coborderRange`, and shrinking `U` does not change the class, by
`Stacks.Chow.openImmersionComposite_heq_of_isOpenRestriction` and the restriction of the class of
Stacks 0FBK along an inclusion of opens
(`Stacks.Chow.bivariantTransport_bivariantRestriction_virtualNormalGysinClass_homOfLE`). For `𝒩`
of arbitrary rank it is `Stacks.Chow.completedVirtualNormalGysinClassOfOpen_independent`, proved
the same way one connected component of `Z` at a time: on a component the class of Stacks 0FBK is
built on a component neighbourhood, and those of `V ⊆ U` are related by
`Stacks.Chow.bivariantTransport_bivariantRestriction_virtualNormalGysinClass_componentShrink`.

## References

* [Stacks Project, Tag 0FBQ](https://stacks.math.columbia.edu/tag/0FBQ)
* [Stacks Project, Tag 0FBK](https://stacks.math.columbia.edu/tag/0FBK)
* [Stacks Project, Tag 0B75](https://stacks.math.columbia.edu/tag/0B75)
* [Stacks Project, Tag 0B78](https://stacks.math.columbia.edu/tag/0B78)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

variable (C : ChowSituation.{u}) {Z X : Scheme.{u}} (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ]
  (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (i : Z ⟶ X) [IsImmersion i] (hi : i ≫ sX = sZ)

omit [LocallyOfFiniteType sZ] [LocallyOfFiniteType sX] [IsImmersion i] in
include hi in
/-- The closed factor `i' : Z ⟶ U` of `i = i' ≫ ι_U` is a morphism over the base. -/
theorem openFactor_comp_structureMorphism {U : X.Opens} {i' : Z ⟶ U.toScheme}
    (hU : i' ≫ U.ι = i) : i' ≫ (U.ι ≫ sX) = sZ := by
  rw [← Category.assoc, hU, hi]

/-- **Stacks 0FBQ (3), the construction.** For an immersion `i : Z ⟶ X`, an open subscheme
`U ⊆ X` with `i = i' ≫ ι_U` and `i' : Z ⟶ U` a closed immersion, and a virtual normal bundle `𝒩`
for `i` of constant rank `r`: the class

  `c(Z ⟶ U, 𝒩) ∘ (U ⟶ X)^* ∈ A^r(Z ⟶ X)`,

the composite (Stacks 0B75) of flat pullback along `U ⟶ X` (Stacks 0B78) with the class of Stacks
0FBK of `𝒩`, read as a virtual normal bundle for `i'`. The degree `r + -0` of the composite is
written `r`. -/
def virtualNormalGysinClassOfOpen (U : X.Opens) (i' : Z ⟶ U.toScheme) [IsClosedImmersion i']
    (hU : i' ≫ U.ι = i) (𝒩 : VirtualNormalBundle i) (r : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} 𝒩.bundle r] :
    BivariantClass C (gysinSystemOfInvertible C) sZ sX i hi (r : ℤ) :=
  BivariantClass.copy C (gysinSystemOfInvertible C) sZ sX hU
    (comp_comp_structureMorphism_eq (openFactor_comp_structureMorphism C sZ sX i hi hU) rfl) hi
    (by simp)
    (openImmersionComposite C sZ (U.ι ≫ sX) sX i' U.ι
      (openFactor_comp_structureMorphism C sZ sX i hi hU) rfl (r : ℤ)
      (virtualNormalBundleClass C sZ (U.ι ≫ sX) i'
        (openFactor_comp_structureMorphism C sZ sX i hi hU) (𝒩.toOpenFactor hU) r))

/-- **The cap operation of `c(Z ⟶ U, 𝒩) ∘ (U ⟶ X)^*`.** On a test scheme `t : T ⟶ X` it
restricts a class on `T` to the open subscheme `U ×_X T`, caps there with the class of Stacks 0FBK
of `𝒩` for `i' : Z ⟶ U`, and pushes the result forward along the associativity isomorphism
`Z ×_U (U ×_X T) ≅ Z ×_X T`, read through `i' ≫ ι_U = i`. -/
theorem virtualNormalGysinClassOfOpen_cap_heq (U : X.Opens) (i' : Z ⟶ U.toScheme)
    [IsClosedImmersion i'] (hU : i' ≫ U.ι = i) (𝒩 : VirtualNormalBundle i) (r : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} 𝒩.bundle r] {T : Scheme.{u}}
    (t : T ⟶ X) [LocallyOfFiniteType t] (k : ℤ) (α : chowGroup C (t ≫ sX) k) :
    (virtualNormalGysinClassOfOpen C sZ sX i hi U i' hU 𝒩 r).cap t k α ≍
      chowPushforwardOfIso C (pullback.fst i' (pullback.fst U.ι t) ≫ sZ)
        (pullback.fst (i' ≫ U.ι) t ≫ sZ) (pullbackRightPullbackFstIso U.ι t i').hom
        (pullbackRightPullbackFstIso_hom_comp_fst_comp sZ i' U.ι t) (k - r)
        ((virtualNormalBundleClass C sZ (U.ι ≫ sX) i'
            (openFactor_comp_structureMorphism C sZ sX i hi hU) (𝒩.toOpenFactor hU) r).cap
          (pullback.fst U.ι t) k
          (chowGroupRestrict C (t ≫ sX) (pullback.fst U.ι t ≫ (U.ι ≫ sX)) (pullback.snd U.ι t)
            (pullbackSnd_comp_structureMorphism rfl t) k α)) := by
  subst hU
  exact (BivariantClass.copy_cap C _ _ _ _ _ _ _ _ t k α).trans
    (openImmersionComposite_cap_heq C sZ (U.ι ≫ sX) sX i' U.ι _ rfl (r : ℤ) _ t k α)

/-- **The class `c(Z ⟶ X, 𝒩) ∈ A^r(Z ⟶ X)` of a virtual normal bundle of constant rank `r` for
an immersion**, Stacks 0FBQ (3) at the canonical choice of `U`: the largest open
`AlgebraicGeometry.Scheme.Hom.coborderRange` of `X` in which `Z` is closed, with the closed
immersion `AlgebraicGeometry.Scheme.Hom.liftCoborder`. -/
def immersionVirtualNormalGysinClass (𝒩 : VirtualNormalBundle i) (r : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} 𝒩.bundle r] :
    BivariantClass C (gysinSystemOfInvertible C) sZ sX i hi (r : ℤ) :=
  virtualNormalGysinClassOfOpen C sZ sX i hi i.coborderRange i.liftCoborder i.liftCoborder_ι 𝒩 r

/-- **Stacks 0FBQ (3), the construction, for a virtual normal bundle of arbitrary rank.** For an
immersion `i : Z ⟶ X`, an open subscheme `U ⊆ X` with `i = i' ≫ ι_U` and `i' : Z ⟶ U` a closed
immersion, and a virtual normal bundle `𝒩` for `i`: the class

  `c(Z ⟶ U, 𝒩) ∘ (U ⟶ X)^* ∈ A^*(Z ⟶ X)^∧`,

the composite on completions (Stacks 0FE0) of flat pullback along `U ⟶ X` (Stacks 0B78) with the
class of Stacks 0FBK of `𝒩` in `A^*(Z ⟶ U)^∧`, read as a virtual normal bundle for `i'`. -/
@[stacks 0FBQ "(3), the construction: c(Z → X, 𝒩) = c(Z → U, 𝒩) ∘ (U → X)^* in A^*(Z → X)^∧ \
for a choice of an open U through which Z → X factors as a closed immersion, 𝒩 of arbitrary rank"]
def completedVirtualNormalGysinClassOfOpen (U : X.Opens) (i' : Z ⟶ U.toScheme)
    [IsClosedImmersion i'] (hU : i' ≫ U.ι = i) (𝒩 : VirtualNormalBundle i) :
    completedBivariantGroup C (gysinSystemOfInvertible C) sZ sX i hi :=
  haveI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
  haveI : IsLocallyNoetherian U.toScheme := LocallyOfFiniteType.isLocallyNoetherian (U.ι ≫ sX)
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  completedBivariantGroup.copy C hU
    (comp_comp_structureMorphism_eq (openFactor_comp_structureMorphism C sZ sX i hi hU) rfl) hi
    (completedOpenImmersionComposite C sZ (U.ι ≫ sX) sX i' U.ι
      (openFactor_comp_structureMorphism C sZ sX i hi hU) rfl
      (completedVirtualNormalGysinClass C sZ (U.ι ≫ sX) i'
        (openFactor_comp_structureMorphism C sZ sX i hi hU) (𝒩.toOpenFactor hU)))

/-- **The class `c(Z ⟶ X, 𝒩) ∈ A^*(Z ⟶ X)^∧` of a virtual normal bundle of arbitrary rank for an
immersion**, Stacks 0FBQ (3) at the canonical choice of `U`: the largest open
`AlgebraicGeometry.Scheme.Hom.coborderRange` of `X` in which `Z` is closed, with the closed
immersion `AlgebraicGeometry.Scheme.Hom.liftCoborder`. -/
def completedVirtualNormalGysinClassOfImmersion (𝒩 : VirtualNormalBundle i) :
    completedBivariantGroup C (gysinSystemOfInvertible C) sZ sX i hi :=
  completedVirtualNormalGysinClassOfOpen C sZ sX i hi i.coborderRange i.liftCoborder
    i.liftCoborder_ι 𝒩

/-! ### Independence of the choice of `U` -/

section Independence

variable {U V : X.Opens} (hVU : V ≤ U) {iU : Z ⟶ U.toScheme} [IsClosedImmersion iU]
  {iV : Z ⟶ V.toScheme} [IsClosedImmersion iV] (hU : iU ≫ U.ι = i) (hV : iV ≫ V.ι = i)

omit [IsImmersion i] [IsClosedImmersion iU] [IsClosedImmersion iV] in
include hU hV in
/-- The closed factor through `V ⊆ U` factors the closed factor through `U`. -/
theorem openFactor_comp_homOfLE : iV ≫ X.homOfLE hVU = iU := by
  rw [← cancel_mono U.ι, Category.assoc, Scheme.homOfLE_ι, hV, hU]

/-- **Shrinking `U` does not change `c(Z → U, 𝒩) ∘ (U → X)^*`, provided `c(Z → V, 𝒩)` is the
restriction of `c(Z → U, 𝒩)` to `V`.** The provision is the base-change clause of Stacks 0FBK
along the open immersion `V ⟶ U`. -/
theorem virtualNormalGysinClassOfOpen_eq_of_isOpenRestriction (𝒩 : VirtualNormalBundle i) (r : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} 𝒩.bundle r]
    (H : IsOpenRestriction C sZ (U.ι ≫ sX) (V.ι ≫ sX) iU iV (X.homOfLE hVU)
      (openFactor_comp_structureMorphism C sZ sX i hi hU)
      (openFactor_comp_structureMorphism C sZ sX i hi hV)
      (by rw [← Category.assoc, Scheme.homOfLE_ι]) (openFactor_comp_homOfLE i hVU hU hV) (r : ℤ)
      (virtualNormalBundleClass C sZ (U.ι ≫ sX) iU
        (openFactor_comp_structureMorphism C sZ sX i hi hU) (𝒩.toOpenFactor hU) r)
      (virtualNormalBundleClass C sZ (V.ι ≫ sX) iV
        (openFactor_comp_structureMorphism C sZ sX i hi hV) (𝒩.toOpenFactor hV) r)) :
    virtualNormalGysinClassOfOpen C sZ sX i hi U iU hU 𝒩 r =
      virtualNormalGysinClassOfOpen C sZ sX i hi V iV hV 𝒩 r := by
  refine eq_of_heq ((BivariantClass.copy_heq _ _ _ _ _).trans (HEq.trans ?_
    (BivariantClass.copy_heq _ _ _ _ _).symm))
  exact openImmersionComposite_heq_of_isOpenRestriction C sZ (U.ι ≫ sX) (V.ι ≫ sX) sX iU iV U.ι
    V.ι (X.homOfLE hVU) _ _ rfl rfl (by rw [← Category.assoc, Scheme.homOfLE_ι])
    (openFactor_comp_homOfLE i hVU hU hV) (r : ℤ)
    (Scheme.homOfLE_ι X hVU) _ _ H

end Independence

/-! ### Restriction along an open immersion, as a cap formula -/

section OpenRestriction

variable {C} {Z U V : Scheme.{u}} {sZ : Z ⟶ C.S} [LocallyOfFiniteType sZ]
  {sU : U ⟶ C.S} [LocallyOfFiniteType sU] {sV : V ⟶ C.S} [LocallyOfFiniteType sV]
  {i : Z ⟶ U} [LocallyOfFiniteType i] {iV : Z ⟶ V} [LocallyOfFiniteType iV]
  {ι : V ⟶ U} [IsOpenImmersion ι] {hi : i ≫ sU = sZ} {hiV : iV ≫ sV = sZ} {p : ℤ}

/-- **The restriction of Stacks 0F9Z along an open immersion, as `Stacks.Chow.IsOpenRestriction`.**
If `c_V ∈ A^p(Z ⟶ V)` is the restriction of `c_U ∈ A^p(Z ⟶ U)` along an open immersion
`ι : V ⟶ U` through which `i` factors as `iV ≫ ι`, transported to `Z` along an identification
`θ : Z ×_U V ≅ Z` over `V`, then on every test scheme over `V` capping with `c_V` is capping with
`c_U`. -/
theorem isOpenRestriction_of_bivariantTransport_bivariantRestriction_heq [Mono iV]
    (hι : ι ≫ sU = sV) (hιi : iV ≫ ι = i)
    (cU : BivariantClass C (gysinSystemOfInvertible C) sZ sU i hi p)
    (cV : BivariantClass C (gysinSystemOfInvertible C) sZ sV iV hiV p)
    (θ : pullback i ι ≅ Z) (hθ : θ.hom ≫ iV = pullback.snd i ι) (hiV' : iV ≫ (ι ≫ sU) = sZ)
    (h : bivariantTransport C (gysinSystemOfInvertible C) (pullback.fst i ι ≫ sZ) sZ (ι ≫ sU)
        (pullback.snd i ι) (pullbackSnd_comp_structureMorphism_eq C sZ sU i hi ι) iV hiV' θ hθ p
        (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C)
        (bivariantRestriction C (gysinSystemOfInvertible C) sZ sU i hi ι p
          (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) cU) ≍ cV) :
    IsOpenRestriction C sZ sU sV i iV ι hi hiV hι hιi p cU cV := by
  subst hι
  obtain rfl := eq_of_heq h
  intro T t _ k α
  rw [bivariantTransport_cap, bivariantTransportCap_apply, bivariantRestriction_cap,
    bivariantRestrictionCap_apply, chowPushforwardOfIso_comp_apply,
    chowPushforwardOfIso_comp_apply]
  refine (chowPushforwardOfIso_congr_apply C _ _ _ (𝟙 _) ?_ _ (Category.id_comp _) _ _).trans
    (chowPushforwardOfIso_id C _ _ _)
  refine pullback.hom_ext ?_ ?_
  · simp only [Category.assoc, openRestrictionPullbackIso_hom_fst, Category.id_comp]
    have hθf : θ.hom = pullback.fst i ι := by
      rw [← cancel_mono iV, hθ, ← cancel_mono ι, Category.assoc, hιi, pullback.condition]
    rw [transportPullbackIso_hom_fst, hθf, pullbackLeftPullbackSndIso_inv_fst]
  · simp only [Category.assoc, openRestrictionPullbackIso_hom_snd, transportPullbackIso_hom_snd,
      pullbackLeftPullbackSndIso_inv_snd_snd, Category.id_comp]

end OpenRestriction

/-! ### Independence of the choice of `U`, unconditionally -/

section IndependenceFinal

variable (𝒩 : VirtualNormalBundle i) (r : ℕ)
  [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} 𝒩.bundle r]

/-- **Shrinking `U` does not change `c(Z → U, 𝒩) ∘ (U → X)^*`.** For opens `V ⊆ U` of `X` through
both of which the immersion `i` factors as a closed immersion, the two classes of Stacks 0FBQ (3)
agree. The class of Stacks 0FBK restricts along `V ⊆ U`
(`Stacks.Chow.bivariantTransport_bivariantRestriction_virtualNormalGysinClass_homOfLE`), which is
what `Stacks.Chow.virtualNormalGysinClassOfOpen_eq_of_isOpenRestriction` needs. -/
theorem virtualNormalGysinClassOfOpen_eq_of_le {U V : X.Opens} (hVU : V ≤ U)
    {iU : Z ⟶ U.toScheme} [IsClosedImmersion iU] {iV : Z ⟶ V.toScheme} [IsClosedImmersion iV]
    (hU : iU ≫ U.ι = i) (hV : iV ≫ V.ι = i) :
    virtualNormalGysinClassOfOpen C sZ sX i hi U iU hU 𝒩 r =
      virtualNormalGysinClassOfOpen C sZ sX i hi V iV hV 𝒩 r :=
  virtualNormalGysinClassOfOpen_eq_of_isOpenRestriction C sZ sX i hi hVU hU hV 𝒩 r
    (isOpenRestriction_of_bivariantTransport_bivariantRestriction_heq
      (by rw [← Category.assoc, Scheme.homOfLE_ι]) (openFactor_comp_homOfLE i hVU hU hV) _ _ _ _ _
      (bivariantTransport_bivariantRestriction_virtualNormalGysinClass_homOfLE C sZ sX hi hVU hU
        hV 𝒩 r))

/-- **Stacks 0FBQ (3): the class `c(Z ⟶ X, 𝒩)` does not depend on the choice of `U`.** Any open
`U ⊆ X` through which the immersion `i` factors as a closed immersion gives the class
`c(Z ⟶ X, 𝒩)` of the canonical choice `U = i.coborderRange`: such a `U` lies in
`i.coborderRange` (`Stacks.Conormal.le_coborderRange_of_comp_eq`), and shrinking does not change
the class (`Stacks.Chow.virtualNormalGysinClassOfOpen_eq_of_le`). -/
theorem virtualNormalGysinClassOfOpen_eq_immersionVirtualNormalGysinClass (U : X.Opens)
    (iU : Z ⟶ U.toScheme) [IsClosedImmersion iU] (hU : iU ≫ U.ι = i) :
    virtualNormalGysinClassOfOpen C sZ sX i hi U iU hU 𝒩 r =
      immersionVirtualNormalGysinClass C sZ sX i hi 𝒩 r :=
  (virtualNormalGysinClassOfOpen_eq_of_le C sZ sX i hi 𝒩 r
    (Stacks.Conormal.le_coborderRange_of_comp_eq i U iU hU) i.liftCoborder_ι hU).symm

/-- **Stacks 0FBQ (3): the bivariant class `c(Z ⟶ X, 𝒩)` does not depend on the choice of the
open subscheme `U`.** Two opens `U₁, U₂ ⊆ X` through which the immersion `i` factors as a closed
immersion give the same class `c(Z ⟶ U₁, 𝒩) ∘ (U₁ ⟶ X)^* = c(Z ⟶ U₂, 𝒩) ∘ (U₂ ⟶ X)^*`. -/
theorem virtualNormalGysinClassOfOpen_independent (U₁ U₂ : X.Opens) (i₁ : Z ⟶ U₁.toScheme)
    [IsClosedImmersion i₁] (h₁ : i₁ ≫ U₁.ι = i) (i₂ : Z ⟶ U₂.toScheme) [IsClosedImmersion i₂]
    (h₂ : i₂ ≫ U₂.ι = i) :
    virtualNormalGysinClassOfOpen C sZ sX i hi U₁ i₁ h₁ 𝒩 r =
      virtualNormalGysinClassOfOpen C sZ sX i hi U₂ i₂ h₂ 𝒩 r :=
  (virtualNormalGysinClassOfOpen_eq_immersionVirtualNormalGysinClass C sZ sX i hi 𝒩 r U₁ i₁
    h₁).trans
    (virtualNormalGysinClassOfOpen_eq_immersionVirtualNormalGysinClass C sZ sX i hi 𝒩 r U₂ i₂
      h₂).symm

end IndependenceFinal

/-! ### The cartesian square of component neighbourhoods -/

section ComponentSquare

variable {Z X : Scheme.{u}} {U V : X.Opens} [IsLocallyNoetherian Z]
  [IsLocallyNoetherian U.toScheme] [IsLocallyNoetherian V.toScheme] [IsLocallyNoetherian X]
  (hVU : V ≤ U) {iU : Z ⟶ U.toScheme} [IsClosedImmersion iU] {iV : Z ⟶ V.toScheme}
  [IsClosedImmersion iV] (hιi : iV ≫ X.homOfLE hVU = iU) (z : _root_.ConnectedComponents Z)

omit [IsLocallyNoetherian X] in
include hιi in
/-- **`W_V = V_{a'} ×_{U_a} W_U`**: the square of the component neighbourhoods and the connected
components of `V ⊆ U` containing `Z_z` is cartesian. -/
theorem isPullback_componentNeighbourhoodShrink_componentInclusion :
    IsPullback (componentNeighbourhoodShrink hVU hιi z) (componentInclusion iV z)
      (componentInclusion iU z) (componentShrinkMap iU iV (X.homOfLE hVU) hιi z) := by
  have H : IsPullback (X.homOfLE hVU) (𝟙 V.toScheme) (𝟙 U.toScheme) (X.homOfLE hVU) :=
    IsPullback.of_vert_isIso ⟨by rw [Category.id_comp, Category.comp_id]⟩
  have h := Scheme.Hom.isPullback_resLE H
    (UT := V.toScheme.connectedComponentOpens (iV.continuous.connectedComponentsMap z))
    (US := U.toScheme.connectedComponentOpens (iU.continuous.connectedComponentsMap z))
    (UX := componentNeighbourhood iU z)
    (connectedComponentOpens_le_preimage_of_comp_eq iU iV (X.homOfLE hVU) hιi z)
    (by simpa using componentNeighbourhood_le iU z)
    (componentNeighbourhood_eq_preimage_inf hVU hιi z)
  have e₁ : ∀ e, Scheme.Hom.resLE (𝟙 V.toScheme)
      (V.toScheme.connectedComponentOpens (iV.continuous.connectedComponentsMap z))
      (componentNeighbourhood iV z) e = componentInclusion iV z := by
    intro e
    rw [← cancel_mono (V.toScheme.connectedComponentOpens _).ι, Scheme.Hom.resLE_comp_ι,
      Scheme.homOfLE_ι, Category.comp_id]
  have e₂ : ∀ e, Scheme.Hom.resLE (𝟙 U.toScheme)
      (U.toScheme.connectedComponentOpens (iU.continuous.connectedComponentsMap z))
      (componentNeighbourhood iU z) e = componentInclusion iU z := by
    intro e
    rw [← cancel_mono (U.toScheme.connectedComponentOpens _).ι, Scheme.Hom.resLE_comp_ι,
      Scheme.homOfLE_ι, Category.comp_id]
  rw [e₁, e₂] at h
  exact h

end ComponentSquare

/-! ### Restriction of classes to an open, and its invariance under transport -/

section OpenRestrictionTransport

variable {C} {Z U V : Scheme.{u}} {sZ : Z ⟶ C.S} [LocallyOfFiniteType sZ]
  {sU : U ⟶ C.S} [LocallyOfFiniteType sU] {sV : V ⟶ C.S} [LocallyOfFiniteType sV]
  {ι : V ⟶ U} [IsOpenImmersion ι] {p : ℤ}

/-- `Stacks.Chow.IsOpenRestriction` only depends on the two classes up to `≍`, for equal
morphisms and degrees. -/
theorem IsOpenRestriction.of_heq {p₁ : ℤ} (hp : p₁ = p) {i₁ i₂ : Z ⟶ U} [LocallyOfFiniteType i₁]
    [LocallyOfFiniteType i₂]
    {iV₁ iV₂ : Z ⟶ V} [LocallyOfFiniteType iV₁] [LocallyOfFiniteType iV₂]
    {hi₁ : i₁ ≫ sU = sZ} {hi₂ : i₂ ≫ sU = sZ} {hiV₁ : iV₁ ≫ sV = sZ} {hiV₂ : iV₂ ≫ sV = sZ}
    {hι : ι ≫ sU = sV} {hιi₁ : iV₁ ≫ ι = i₁} {hιi₂ : iV₂ ≫ ι = i₂} (h₁ : i₁ = i₂)
    (h₂ : iV₁ = iV₂)
    {cU₁ : BivariantClass C (gysinSystemOfInvertible C) sZ sU i₁ hi₁ p₁}
    {cU₂ : BivariantClass C (gysinSystemOfInvertible C) sZ sU i₂ hi₂ p}
    {cV₁ : BivariantClass C (gysinSystemOfInvertible C) sZ sV iV₁ hiV₁ p₁}
    {cV₂ : BivariantClass C (gysinSystemOfInvertible C) sZ sV iV₂ hiV₂ p} (hU : cU₁ ≍ cU₂)
    (hV : cV₁ ≍ cV₂) (H : IsOpenRestriction C sZ sU sV i₁ iV₁ ι hi₁ hiV₁ hι hιi₁ p₁ cU₁ cV₁) :
    IsOpenRestriction C sZ sU sV i₂ iV₂ ι hi₂ hiV₂ hι hιi₂ p cU₂ cV₂ := by
  subst hp h₁ h₂
  obtain rfl := eq_of_heq hU
  obtain rfl := eq_of_heq hV
  exact H

/-- The zero classes restrict to one another. -/
theorem isOpenRestriction_zero {i : Z ⟶ U} [LocallyOfFiniteType i] {iV : Z ⟶ V}
    [LocallyOfFiniteType iV] {hi : i ≫ sU = sZ} {hiV : iV ≫ sV = sZ} {hι : ι ≫ sU = sV}
    {hιi : iV ≫ ι = i} :
    IsOpenRestriction C sZ sU sV i iV ι hi hiV hι hιi p 0 0 := by
  intro T t _ k α
  rw [BivariantClass.zero_cap, BivariantClass.zero_cap, map_zero]

end OpenRestrictionTransport

/-! ### Independence of the choice of `U` on completions -/

section CompletedIndependence

variable (𝒩 : VirtualNormalBundle i)

include hi in
/-- **The class of Stacks 0FBK on completions restricts along an inclusion of opens `V ⊆ U`**
through both of which the immersion `i` factors as a closed immersion: on every connected
component `Z_z` of `Z`, the class `c(Z_z ⟶ W_U, 𝒩|) ∘ (W_U ⟶ U_a)^*` restricts to
`c(Z_z ⟶ W_V, 𝒩|) ∘ (W_V ⟶ V_{a'})^*` along `V_{a'} ⟶ U_a`. -/
theorem isCompletedOpenRestriction_completedVirtualNormalGysinClass {U V : X.Opens}
    (hVU : V ≤ U) {iU : Z ⟶ U.toScheme} [IsClosedImmersion iU] {iV : Z ⟶ V.toScheme}
    [IsClosedImmersion iV] (hU : iU ≫ U.ι = i) (hV : iV ≫ V.ι = i) :
    letI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
    letI : IsLocallyNoetherian U.toScheme := LocallyOfFiniteType.isLocallyNoetherian (U.ι ≫ sX)
    letI : IsLocallyNoetherian V.toScheme := LocallyOfFiniteType.isLocallyNoetherian (V.ι ≫ sX)
    IsCompletedOpenRestriction C sZ (U.ι ≫ sX) (V.ι ≫ sX) iU iV (X.homOfLE hVU)
      (openFactor_comp_structureMorphism C sZ sX i hi hU)
      (openFactor_comp_structureMorphism C sZ sX i hi hV)
      (by rw [← Category.assoc, Scheme.homOfLE_ι]) (openFactor_comp_homOfLE i hVU hU hV)
      (completedVirtualNormalGysinClass C sZ (U.ι ≫ sX) iU
        (openFactor_comp_structureMorphism C sZ sX i hi hU) (𝒩.toOpenFactor hU))
      (completedVirtualNormalGysinClass C sZ (V.ι ≫ sX) iV
        (openFactor_comp_structureMorphism C sZ sX i hi hV) (𝒩.toOpenFactor hV)) := by
  let : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
  let : IsLocallyNoetherian U.toScheme := LocallyOfFiniteType.isLocallyNoetherian (U.ι ≫ sX)
  let : IsLocallyNoetherian V.toScheme := LocallyOfFiniteType.isLocallyNoetherian (V.ι ≫ sX)
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  intro z p
  have hιi := openFactor_comp_homOfLE i hVU hU hV
  have hiU : iU ≫ (U.ι ≫ sX) = sZ := openFactor_comp_structureMorphism C sZ sX i hi hU
  have hiV : iV ≫ (V.ι ≫ sX) = sZ := openFactor_comp_structureMorphism C sZ sX i hi hV
  obtain hp | hp := eq_or_ne (componentRank 𝒩.bundle z : ℤ) p
  · subst hp
    -- the restriction of the classes of Stacks 0FBK on the component neighbourhoods
    have hκ := isOpenRestriction_of_bivariantTransport_bivariantRestriction_heq
      (by rw [← Category.assoc, Scheme.Hom.resLE_comp_ι, Category.assoc, Scheme.homOfLE_ι_assoc])
      (componentRestriction_comp_componentNeighbourhoodShrink hVU hιi z) _ _ _ _ _
      (bivariantTransport_bivariantRestriction_virtualNormalGysinClass_componentShrink C sZ sX
        hVU hιi z hi hU hV 𝒩)
    have hcomp := isOpenRestriction_openImmersionComposite C _ _ _
      (((U.toScheme).connectedComponentOpens (iU.continuous.connectedComponentsMap z)).ι ≫
        (U.ι ≫ sX))
      (((V.toScheme).connectedComponentOpens (iV.continuous.connectedComponentsMap z)).ι ≫
        (V.ι ≫ sX))
      (componentRestriction iU z) (componentRestriction iV z) (componentInclusion iU z)
      (componentInclusion iV z) (componentShrinkMap iU iV (X.homOfLE hVU) hιi z)
      (componentNeighbourhoodShrink hVU hιi z) _ _
      (by rw [← Category.assoc, Scheme.homOfLE_ι]) (by rw [← Category.assoc, Scheme.homOfLE_ι])
      (componentShrinkMap_comp_structureMorphism C (U.ι ≫ sX) (V.ι ≫ sX) iU iV (X.homOfLE hVU)
        (by rw [← Category.assoc, Scheme.homOfLE_ι]) hιi z) _
      (componentRestriction_comp_componentNeighbourhoodShrink hVU hιi z)
      (isPullback_componentNeighbourhoodShrink_componentInclusion hVU hιi z) _ _ _ hκ
    refine IsOpenRestriction.of_heq ?_ (componentRestriction_comp_componentInclusion iU z)
      (componentRestriction_comp_componentInclusion iV z) ?_ ?_ (by exact hcomp)
    · simp
    · exact (BivariantClass.copy_heq _ _ _ _ _).symm.trans
        (heq_of_eq (DirectSum.of_eq_same _ _).symm)
    · exact (BivariantClass.copy_heq _ _ _ _ _).symm.trans
        (heq_of_eq (DirectSum.of_eq_same _ _).symm)
  · have eU : completedVirtualNormalGysinClass C sZ (U.ι ≫ sX) iU hiU (𝒩.toOpenFactor hU) z p =
        0 := DirectSum.of_eq_of_ne _ _ _ (Ne.symm hp)
    have eV : completedVirtualNormalGysinClass C sZ (V.ι ≫ sX) iV hiV (𝒩.toOpenFactor hV) z p =
        0 := DirectSum.of_eq_of_ne _ _ _ (Ne.symm hp)
    rw [eU, eV]
    exact isOpenRestriction_zero

/-- **Shrinking `U` does not change `c(Z → U, 𝒩) ∘ (U → X)^*` on completions.** For opens
`V ⊆ U` of `X` through both of which the immersion `i` factors as a closed immersion, the two
classes of Stacks 0FBQ (3) in `A^*(Z ⟶ X)^∧` agree. -/
theorem completedVirtualNormalGysinClassOfOpen_eq_of_le {U V : X.Opens} (hVU : V ≤ U)
    {iU : Z ⟶ U.toScheme} [IsClosedImmersion iU] {iV : Z ⟶ V.toScheme} [IsClosedImmersion iV]
    (hU : iU ≫ U.ι = i) (hV : iV ≫ V.ι = i) :
    completedVirtualNormalGysinClassOfOpen C sZ sX i hi U iU hU 𝒩 =
      completedVirtualNormalGysinClassOfOpen C sZ sX i hi V iV hV 𝒩 := by
  let : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
  let : IsLocallyNoetherian U.toScheme := LocallyOfFiniteType.isLocallyNoetherian (U.ι ≫ sX)
  let : IsLocallyNoetherian V.toScheme := LocallyOfFiniteType.isLocallyNoetherian (V.ι ≫ sX)
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  refine eq_of_heq ((completedBivariantGroup.copy_heq _ _ _ _ _).trans (HEq.trans ?_
    (completedBivariantGroup.copy_heq _ _ _ _ _).symm))
  exact completedOpenImmersionComposite_heq_of_isCompletedOpenRestriction C sZ (U.ι ≫ sX)
    (V.ι ≫ sX) sX iU iV U.ι V.ι (X.homOfLE hVU) _ _ rfl rfl
    (by rw [← Category.assoc, Scheme.homOfLE_ι]) (openFactor_comp_homOfLE i hVU hU hV)
    (Scheme.homOfLE_ι X hVU) _ _
    (isCompletedOpenRestriction_completedVirtualNormalGysinClass C sZ sX i hi 𝒩 hVU hU hV)

/-- Every choice of `U` gives the class `c(Z ⟶ X, 𝒩) ∈ A^*(Z ⟶ X)^∧` of the canonical choice
`U = i.coborderRange`. -/
theorem completedVirtualNormalGysinClassOfOpen_eq_completedVirtualNormalGysinClassOfImmersion
    (U : X.Opens) (iU : Z ⟶ U.toScheme) [IsClosedImmersion iU] (hU : iU ≫ U.ι = i) :
    completedVirtualNormalGysinClassOfOpen C sZ sX i hi U iU hU 𝒩 =
      completedVirtualNormalGysinClassOfImmersion C sZ sX i hi 𝒩 :=
  (completedVirtualNormalGysinClassOfOpen_eq_of_le C sZ sX i hi 𝒩
    (Stacks.Conormal.le_coborderRange_of_comp_eq i U iU hU) i.liftCoborder_ι hU).symm

/-- **Stacks 0FBQ (3): the bivariant class `c(Z ⟶ X, 𝒩) ∈ A^*(Z ⟶ X)^∧` does not depend on the
choice of the open subscheme `U`**, for a virtual normal bundle `𝒩` of arbitrary rank: two opens
`U₁, U₂ ⊆ X` through which the immersion `i` factors as a closed immersion give the same class
`c(Z ⟶ U₁, 𝒩) ∘ (U₁ ⟶ X)^* = c(Z ⟶ U₂, 𝒩) ∘ (U₂ ⟶ X)^*`. -/
@[stacks 0FBQ "(3), the bivariant class c(Z → X, 𝒩) ∈ A^*(Z → X)^∧ does not depend on the \
choice of U, for 𝒩 of arbitrary rank"]
theorem completedVirtualNormalGysinClassOfOpen_independent (U₁ U₂ : X.Opens)
    (i₁ : Z ⟶ U₁.toScheme) [IsClosedImmersion i₁] (h₁ : i₁ ≫ U₁.ι = i) (i₂ : Z ⟶ U₂.toScheme)
    [IsClosedImmersion i₂] (h₂ : i₂ ≫ U₂.ι = i) :
    completedVirtualNormalGysinClassOfOpen C sZ sX i hi U₁ i₁ h₁ 𝒩 =
      completedVirtualNormalGysinClassOfOpen C sZ sX i hi U₂ i₂ h₂ 𝒩 :=
  (completedVirtualNormalGysinClassOfOpen_eq_completedVirtualNormalGysinClassOfImmersion C sZ sX
    i hi 𝒩 U₁ i₁ h₁).trans
    (completedVirtualNormalGysinClassOfOpen_eq_completedVirtualNormalGysinClassOfImmersion C sZ sX
      i hi 𝒩 U₂ i₂ h₂).symm

end CompletedIndependence

end Stacks.Chow

end
