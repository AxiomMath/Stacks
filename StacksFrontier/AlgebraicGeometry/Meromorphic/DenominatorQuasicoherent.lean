module

public import StacksFrontier.AlgebraicGeometry.TorsionQuasicoherent.Local
public import StacksFrontier.AlgebraicGeometry.Meromorphic.DenominatorSupport
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The ideal of denominators of a meromorphic section is quasi-coherent

Let `X` be a scheme, `L` an invertible sheaf of `𝒪_X`-modules and `s` a meromorphic section of
`L`. [Stacks, Tag 02P0](https://stacks.math.columbia.edu/tag/02P0) asserts that the ideal `I` of
denominators of `s` is quasi-coherent. This file proves it.

The source reduces to `X = Spec A`, `L = 𝒪_X` and `s = a/b` with `b` a nonzerodivisor, where
`I = {x ∈ A | x (a/b) ∈ A}`, and then checks `I_f = {x ∈ A_f | x (a/b) ∈ A_f}` for every
`f ∈ A`. That is exactly the shape of the argument here: on an affine open inside a
trivialization neighbourhood the sections of `I` are described by the colon condition
`f · a ∈ (b)` (`AlgebraicGeometry.exists_denominatorIdeal_inclusion_app_eq_iff_mul_eq`), and the
colon condition localizes (`AlgebraicGeometry.isLocalizedModule_restrictₗ_of_colon`).

## Main results

* `AlgebraicGeometry.denominatorIdeal_isQuasicoherent`: **Tag 02P0**, quasi-coherence of the
  ideal of denominators.
* `AlgebraicGeometry.exists_denominatorIdeal_inclusion_app_eq_iff_mul_eq`: the colon-ideal
  description of the sections of the ideal, and
  `AlgebraicGeometry.exists_denominatorIdeal_inclusion_app_eq_iff_mul_eq_of_le` the same on
  every smaller open.
* `AlgebraicGeometry.exists_isAffineOpen_nhds_denominator_numerator_isUnit`: the local normal
  form `b · s = a · g` with `g` a basis of the sections of `L` and `b` invertible in `K_X`.
* `AlgebraicGeometry.isLocalizedModule_restrictₗ_of_colon`: an `𝒪_X`-submodule of the structure
  sheaf cut out by a colon condition has, over each basic open of an affine open, the
  localization of its sections over that affine open.
* `AlgebraicGeometry.isQuasicoherent_of_isLocalizedModule_restrictₗ_of_cover`: the localization
  criterion for quasi-coherence, needed only at the affine opens of a covering family rather
  than at every affine open.

## Implementation notes

Quasi-coherence is checked by
`Stacks.AlgebraicGeometry.TorsionQuasicoherent.isQuasicoherent_of_isLocalizedModule_restrictₗ`,
which asks for the localization property at *every* affine open. The normal form
`b · s = a · g` is only available near each point, so that criterion is first weakened to a
covering family of affine opens; the weakening is the original proof with its index type
changed, the affine opens below the members of the family still covering `X` because the affine
opens form a basis.

Two refinements of the existing local theory are needed and are proved here. The generator of `L`
has to be a *basis* of the sections over every smaller open, not merely a generating section:
the injectivity half is what turns an equation `(f · a) · g = (b · c) · g` in `L` into the
equation `f · a = b · c` in `𝒪_X`. And the denominator `b` has to be kept *invertible in
`K_X(V)`*, which is what
`AlgebraicGeometry.Scheme.exists_isAffineOpen_nhds_isFraction_totalQuotientSheaf` produces,
rather than only a nonzerodivisor in `Γ(X, V)`: multiplication by `b` is then injective on
`K_X(L)`, which is what makes the colon description an identity of sections rather than a local
one. Invertibility passes to every smaller open by functoriality, where being a nonzerodivisor
would have had to be reproved.

Scalars are written in the `RingCat` spelling
`(Stacks.Sheaves.Differentials.ringSheaf X.sheaf).obj.obj (op W)` where a scalar action is needed
and in the `Γ(X, W)` spelling where a product or commutativity is needed, the two being bridged
by `AlgebraicGeometry.mul_comm_ringSheaf_sections`; the bridging `Module` instance of
`PresheafOfModules` is only found at the former and commutativity is only recorded at the
latter.

## References

* [Stacks Project, Tag 02P0](https://stacks.math.columbia.edu/tag/02P0)
* [Stacks Project, Tag 02P1](https://stacks.math.columbia.edu/tag/02P1)
* [Stacks Project, Tag 0B8M](https://stacks.math.columbia.edu/tag/0B8M)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.AlgebraicGeometry.AffinePushforward
open Stacks.AlgebraicGeometry.QuasicoherentBaseChange
open Stacks.AlgebraicGeometry.TorsionQuasicoherent

universe u

namespace AlgebraicGeometry

/-! ### Two pieces of general quasi-coherence theory -/

/-- **Quasi-coherence is detected by localization on the basic opens of the affine opens of a
covering family.** This is
`Stacks.AlgebraicGeometry.TorsionQuasicoherent.isQuasicoherent_of_isLocalizedModule_restrictₗ`
with the localization property demanded only at the affine opens satisfying a predicate `P`
which holds on some affine neighbourhood of every point; those affine opens still cover `X`, so
the proof is unchanged apart from its index type. -/
theorem isQuasicoherent_of_isLocalizedModule_restrictₗ_of_cover {X : Scheme.{u}} (N : X.Modules)
    (P : X.Opens → Prop) (hcov : ∀ x : X, ∃ U : X.Opens, IsAffineOpen U ∧ P U ∧ x ∈ U)
    (h : ∀ (U : X.Opens), IsAffineOpen U → P U → ∀ a : Γ(X, U),
      letI := moduleOfLE N (X.basicOpen_le a)
      IsLocalizedModule.Away a (restrictₗ N (X.basicOpen_le a))) :
    N.IsQuasicoherent := by
  refine isQuasicoherent_of_presentations N
    (fun V : {U : X.Opens // IsAffineOpen U ∧ P U} => (V : X.Opens)) ?_ fun V => ?_
  · refine top_le_iff.mp fun x _ => ?_
    obtain ⟨U, hU, hPU, hxU⟩ := hcov x
    exact Opens.mem_iSup.mpr ⟨⟨U, hU, hPU⟩, hxU⟩
  · obtain ⟨U, hU, hPU⟩ := V
    have h1 : (N.restrict hU.fromSpec).IsQuasicoherent :=
      isQuasicoherent_restrict_fromSpec N hU (h U hU hPU)
    have h2 : ((N.restrict hU.fromSpec).restrict hU.isoSpec.hom).IsQuasicoherent := inferInstance
    have iso : (N.restrict hU.fromSpec).restrict hU.isoSpec.hom ≅ N.restrict U.ι :=
      ((Scheme.Modules.restrictFunctorComp hU.isoSpec.hom hU.fromSpec).app N).symm ≪≫
        (Scheme.Modules.restrictFunctorCongr hU.isoSpec_hom_fromSpec).app N
    have : (N.restrict U.ι).IsQuasicoherent :=
      (SheafOfModules.isQuasicoherent U.toScheme.ringCatSheaf).prop_of_iso iso h2
    exact (nonempty_presentation_of_isoSpec hU.isoSpec _).some

/-- **A colon ideal localizes.** Let `N` be an `𝒪_X`-module whose sections embed in those of the
structure sheaf by a family of maps `ιs`, compatibly with scalars and restriction, and let `U`
be an affine open carrying sections `α`, `β` of `𝒪_X` such that over `U` and over the basic open
of `a` the sections of `N` are exactly those `f` with `f · α` a multiple of `β`. Then the
sections of `N` over `X.basicOpen a` are the localization of its sections over `U` away from
`a`.

This is the localization step of [Stacks, Tag 02P0]: `a` is invertible on `X.basicOpen a`, so it
acts invertibly on the sections there; a section of `𝒪_X` over `X.basicOpen a` is a fraction
`x / aⁿ`, and clearing denominators in its colon condition gives a colon condition for `aᵏ x`
over `U`. -/
theorem isLocalizedModule_restrictₗ_of_colon {X : Scheme.{u}} (N : X.Modules)
    (ιs : ∀ W : X.Opens, Γ(N, W) → Γ(X, W))
    (hinj : ∀ W : X.Opens, Function.Injective (ιs W))
    (hsmul : ∀ (W : X.Opens) (r : Γ(X, W)) (d : Γ(N, W)), ιs W (r • d) = r * ιs W d)
    (hnat : ∀ (W W' : X.Opens) (h : W' ≤ W) (d : Γ(N, W)),
      ιs W' (N.presheaf.map (homOfLE h).op d) = X.presheaf.map (homOfLE h).op (ιs W d))
    {U : X.Opens} (hU : IsAffineOpen U) (α β a : Γ(X, U))
    (hcolonU : ∀ f : Γ(X, U), (∃ d : Γ(N, U), ιs U d = f) ↔ ∃ c : Γ(X, U), f * α = β * c)
    (hcolonD : ∀ f : Γ(X, X.basicOpen a),
      (∃ d : Γ(N, X.basicOpen a), ιs (X.basicOpen a) d = f) ↔
        ∃ c : Γ(X, X.basicOpen a),
          f * algebraMap Γ(X, U) Γ(X, X.basicOpen a) α
            = algebraMap Γ(X, U) Γ(X, X.basicOpen a) β * c) :
    letI := moduleOfLE N (X.basicOpen_le a)
    IsLocalizedModule.Away a (restrictₗ N (X.basicOpen_le a)) := by
  let := moduleOfLE N (X.basicOpen_le a)
  have hloc : IsLocalization.Away a Γ(X, X.basicOpen a) := hU.isLocalization_basicOpen a
  have hnatD : ∀ d : Γ(N, U), ιs (X.basicOpen a) (restrictₗ N (X.basicOpen_le a) d)
      = algebraMap Γ(X, U) Γ(X, X.basicOpen a) (ιs U d) :=
    fun d => hnat U (X.basicOpen a) (X.basicOpen_le a) d
  refine ⟨?_, ?_, ?_⟩
  · intro x
    obtain ⟨n, hn⟩ := x.2
    have hua : IsUnit (algebraMap Γ(X, U) Γ(X, X.basicOpen a) (x : Γ(X, U))) := by
      rw [← hn, map_pow]
      exact (X.toRingedSpace.isUnit_res_basicOpen a).pow n
    rw [Module.End.isUnit_iff]
    have hfun : ⇑(algebraMap Γ(X, U) (Module.End Γ(X, U) Γ(N, X.basicOpen a)) (x : Γ(X, U)))
        = fun z : Γ(N, X.basicOpen a) =>
          (algebraMap Γ(X, U) Γ(X, X.basicOpen a) (x : Γ(X, U))) • z := funext fun z => rfl
    rw [hfun]
    exact hua.smul_bijective
  · intro y
    obtain ⟨c, hc⟩ := (hcolonD (ιs (X.basicOpen a) y)).mp ⟨y, rfl⟩
    obtain ⟨⟨x, sx⟩, hx⟩ :=
      IsLocalization.surj (M := Submonoid.powers a) (ιs (X.basicOpen a) y)
    obtain ⟨⟨w, sw⟩, hw⟩ := IsLocalization.surj (M := Submonoid.powers a) c
    have key : algebraMap Γ(X, U) Γ(X, X.basicOpen a) (x * α * (sw : Γ(X, U)))
        = algebraMap Γ(X, U) Γ(X, X.basicOpen a) (β * w * (sx : Γ(X, U))) := by
      simp only [map_mul]
      linear_combination (-(algebraMap Γ(X, U) Γ(X, X.basicOpen a) α
          * algebraMap Γ(X, U) Γ(X, X.basicOpen a) (sw : Γ(X, U)))) * hx
        + (algebraMap Γ(X, U) Γ(X, X.basicOpen a) (sx : Γ(X, U))
          * algebraMap Γ(X, U) Γ(X, X.basicOpen a) (sw : Γ(X, U))) * hc
        + (algebraMap Γ(X, U) Γ(X, X.basicOpen a) β
          * algebraMap Γ(X, U) Γ(X, X.basicOpen a) (sx : Γ(X, U))) * hw
    obtain ⟨k, hk⟩ := (IsLocalization.eq_iff_exists (Submonoid.powers a)
      Γ(X, X.basicOpen a)).mp key
    obtain ⟨d, hd⟩ : ∃ d : Γ(N, U), ιs U d = (k : Γ(X, U)) * x * (sw : Γ(X, U)) :=
      (hcolonU _).mpr ⟨(k : Γ(X, U)) * w * (sx : Γ(X, U)), by linear_combination hk⟩
    refine ⟨⟨d, k * sx * sw⟩, hinj (X.basicOpen a)
      ((hsmul (X.basicOpen a) (algebraMap Γ(X, U) Γ(X, X.basicOpen a)
        ((k * sx * sw : Submonoid.powers a) : Γ(X, U))) y).trans ?_)⟩
    rw [hnatD d, hd, Submonoid.coe_mul, Submonoid.coe_mul]
    simp only [map_mul]
    linear_combination (algebraMap Γ(X, U) Γ(X, X.basicOpen a) (k : Γ(X, U))
      * algebraMap Γ(X, U) Γ(X, X.basicOpen a) (sw : Γ(X, U))) * hx
  · intro d₁ d₂ hd
    have h1 : algebraMap Γ(X, U) Γ(X, X.basicOpen a) (ιs U d₁)
        = algebraMap Γ(X, U) Γ(X, X.basicOpen a) (ιs U d₂) := by
      rw [← hnatD d₁, ← hnatD d₂]
      exact congrArg (ιs (X.basicOpen a)) hd
    obtain ⟨k, hk⟩ := (IsLocalization.eq_iff_exists (Submonoid.powers a)
      Γ(X, X.basicOpen a)).mp h1
    exact ⟨k, hinj U ((hsmul U (k : Γ(X, U)) d₁).trans
      (hk.trans (hsmul U (k : Γ(X, U)) d₂).symm))⟩

/-! ### The local normal form, with a basis and an invertible denominator -/

variable (X : Scheme.{u})
  (L : SheafOfModules.{u}
    (Stacks.Sheaves.Differentials.ringSheaf (J := Opens.grothendieckTopology X) X.sheaf))
  (s : MeromorphicSection X.sheaf L)

/-- Multiplication of sections of the structure sheaf is commutative in the `RingCat` spelling
`(Stacks.Sheaves.Differentials.ringSheaf X.sheaf).obj.obj (op W)`, which forgets commutativity
but not the ring structure it comes from. The scalar action on the sections of a sheaf of
`𝒪_X`-modules is only found by instance search at that spelling, so the two have to be used
together. -/
theorem mul_comm_ringSheaf_sections (W : X.Opens)
    (r t : (Stacks.Sheaves.Differentials.ringSheaf (J := Opens.grothendieckTopology X)
      X.sheaf).obj.obj (op W)) :
    r * t = t * r :=
  mul_comm (show Γ(X, W) from r) (show Γ(X, W) from t)

/-- **An invertible sheaf of modules on a scheme has a single generator near every point**,
whose restriction to each smaller open is a *basis* of the sections there. This is
`AlgebraicGeometry.exists_nhds_section_forall_surjective_smul_of_isInvertible` with the
injectivity half of Tag 0B8M kept. -/
theorem exists_nhds_section_forall_bijective_smul_of_isInvertible
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj
      (Stacks.Sheaves.Differentials.ringSheaf (J := Opens.grothendieckTopology X) X.sheaf).property
        L) (x : X) :
    ∃ (W : X.Opens) (_ : x ∈ W) (g : L.val.obj (op W)),
      ∀ (V : X.Opens) (hVW : V ≤ W), Function.Bijective
        (fun c : (Stacks.Sheaves.Differentials.ringSheaf (J := Opens.grothendieckTopology X)
          X.sheaf).obj.obj
          (op V) => c • (L.val.restrictₛₗ (homOfLE hVW).op g)) := by
  have hloc : ∀ y : X.toRingedSpace.carrier,
      IsLocalRing (Stacks.SheafOfModules.TensorStalkRingedSpace.ringStalk X.toRingedSpace y) :=
    fun y => X.isLocalRing y
  have hinv : Stacks.SheafOfModules.IsInvertible X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property L :=
    (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ L).mpr hL
  obtain ⟨W, hxW, g, hbij⟩ := Stacks.SheafOfModules.exists_bijective_smul_of_isInvertible
    (X := X.toRingedSpace) L x
  exact ⟨W, hxW, g, hbij⟩

/-- **The local normal form `b · s = a · g` with the denominator a unit in the meromorphic
functions.** This is
`AlgebraicGeometry.exists_isAffineOpen_nhds_denominator_numerator` with the generator `g` a
basis of the sections of `L` over every smaller open, and with the invertibility of the
denominator `b` in `K_X(V)` kept in place of its being a nonzerodivisor in `Γ(X, V)`. Both are
needed to turn the denominator rule into the colon-ideal description
`AlgebraicGeometry.exists_denominatorIdeal_inclusion_app_eq_iff_mul_eq`. -/
theorem exists_isAffineOpen_nhds_denominator_numerator_isUnit
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj
      (Stacks.Sheaves.Differentials.ringSheaf (J := Opens.grothendieckTopology X) X.sheaf).property
        L) (x : X) :
    ∃ V : X.Opens, x ∈ V ∧ IsAffineOpen V ∧ ∃ g : L.val.obj (op V),
      (∀ (U : X.Opens) (hUV : U ≤ V), Function.Bijective
        (fun c : (Stacks.Sheaves.Differentials.ringSheaf (J := Opens.grothendieckTopology X)
          X.sheaf).obj.obj
          (op U) => c • (L.val.restrictₛₗ (homOfLE hUV).op g))) ∧
      ∃ b : Γ(X, V), IsUnit (X.toTotalQuotientSheaf.hom.app (op V) b) ∧
        ∃ a : (Stacks.Sheaves.Differentials.ringSheaf (J := Opens.grothendieckTopology X)
          X.sheaf).obj.obj (op V),
          ((meromorphicSectionMul X L s).val.app (op V)).hom b
            = ((toMeromorphicSectionSheafAsModule X L).val.app (op V)).hom (a • g) := by
  obtain ⟨W₀, hxW₀, g₀, hbij⟩ := exists_nhds_section_forall_bijective_smul_of_isInvertible X L hL x
  obtain ⟨W₁, hxW₁, z₁, hz₁⟩ := exists_nhds_toSheafifyMeromorphicTensor_app_eq X L s x
  have hz := toSheafifyMeromorphicTensor_app_restrict_eq X L s
    (inf_le_right : W₀ ⊓ W₁ ≤ W₁) z₁ hz₁
  have hWW₀ : W₀ ⊓ W₁ ≤ W₀ := inf_le_left
  have hxW : x ∈ W₀ ⊓ W₁ := ⟨hxW₀, hxW₁⟩
  have h1 := Stacks.Meromorphic.exists_forall_smul_eval_eq_oneTmul
    (Opens.grothendieckTopology X) X.toTotalQuotientSheaf.hom
    (Stacks.Sheaves.Differentials.ringSheaf (J := Opens.grothendieckTopology X)
      X.totalQuotientSheaf).property
    L.val (L.val.restrictₛₗ (homOfLE hWW₀).op g₀)
    ((hbij (W₀ ⊓ W₁) hWW₀).surjective) _ s hz
  obtain ⟨u, hgenu⟩ := h1
  have h2 := X.exists_isAffineOpen_nhds_isFraction_totalQuotientSheaf (U := W₀ ⊓ W₁) u hxW
  obtain ⟨V, hVW, hVaff, hxV, a, b, hb, hbu, heq⟩ := h2
  refine ⟨V, hxV, hVaff, L.val.restrictₛₗ (homOfLE (hVW.trans hWW₀)).op g₀,
    fun U hUV => ?_, b, hbu, a, ?_⟩
  · rw [PresheafOfModules.restrictₛₗ_restrictₛₗ]
    exact hbij U (hUV.trans (hVW.trans hWW₀))
  · have h3 := hgenu (op V) (homOfLE hVW).op b a heq
    have hrest : ((L.val.map (homOfLE hVW).op).hom
          (L.val.restrictₛₗ (homOfLE hWW₀).op g₀) : L.val.obj (op V))
        = L.val.restrictₛₗ (homOfLE (hVW.trans hWW₀)).op g₀ :=
      PresheafOfModules.restrictₛₗ_restrictₛₗ L.val _ _ g₀
    refine ((meromorphicSectionMul_val_app X L s (op V) b).trans
      ((Stacks.Meromorphic.unitHomEquiv_symm_val_app_apply _ _ s (op V) _).trans
        (h3.trans ?_)))
    exact oneTmulMeromorphicSectionSheaf_app_smul X L (op V) a hrest

/-! ### The colon-ideal description of the sections of the ideal -/

/-- **The colon-ideal description of the ideal of denominators.** On an open set carrying a
basis `g` of the sections of `L`, a denominator `b` which is invertible in the meromorphic
functions, and a numerator `a` with `b · s = a · g`, a section `f` of the structure sheaf is a
denominator of `s` exactly when `f · a` is a multiple of `b`. This is the sheaf-theoretic form
of the source's `I = {x ∈ A | x (a/b) ∈ A}`, and — because `b` is invertible in `K_X` — it is an
identity of sections rather than merely a local one. -/
theorem exists_denominatorIdeal_inclusion_app_eq_iff_mul_eq
    (hmono : Mono (toMeromorphicSectionSheafAsModule X L))
    (W : X.Opens) (g : L.val.obj (op W))
    (hbij : Function.Bijective
      (fun c : (Stacks.Sheaves.Differentials.ringSheaf (J := Opens.grothendieckTopology X)
        X.sheaf).obj.obj (op W)
        => c • g))
    (b : (Stacks.Sheaves.Differentials.ringSheaf (J := Opens.grothendieckTopology X)
      X.sheaf).obj.obj (op W))
    (hbu : IsUnit (X.toTotalQuotientSheaf.hom.app (op W) b))
    (a : (Stacks.Sheaves.Differentials.ringSheaf (J := Opens.grothendieckTopology X)
      X.sheaf).obj.obj (op W))
    (heq : ((meromorphicSectionMul X L s).val.app (op W)).hom b
      = ((toMeromorphicSectionSheafAsModule X L).val.app (op W)).hom (a • g))
    (f : (Stacks.Sheaves.Differentials.ringSheaf (J := Opens.grothendieckTopology X)
      X.sheaf).obj.obj (op W)) :
    (∃ d : (denominatorIdeal X L s).val.obj (op W),
        ((denominatorIdealι X L s).val.app (op W)).hom d = f) ↔
      ∃ c : (Stacks.Sheaves.Differentials.ringSheaf (J := Opens.grothendieckTopology X)
        X.sheaf).obj.obj (op W),
        f * a = b * c := by
  have hinj : Function.Injective
      ((toMeromorphicSectionSheafAsModule X L).val.app (op W)).hom :=
    SheafOfModules.app_injective_of_mono hmono (op W)
  have hbinj : Function.Injective
      (fun z : (meromorphicSectionSheafAsModule X L).val.obj (op W) => b • z) := by
    have h : IsUnit (show (Stacks.Sheaves.Differentials.ringSheaf
        (J := Opens.grothendieckTopology X) X.totalQuotientSheaf).obj.obj (op W) from
        X.toTotalQuotientSheaf.hom.app (op W) b) := hbu
    exact (h.smul_bijective (β := (meromorphicSectionSheaf X.sheaf L).val.obj (op W))).injective
  have hkey : b • (((meromorphicSectionMul X L s).val.app (op W)).hom f)
      = ((toMeromorphicSectionSheafAsModule X L).val.app (op W)).hom ((f * a) • g) :=
    (((meromorphicSectionMul X L s).val.app (op W)).hom.map_smul b f).symm.trans
      ((congrArg (fun y : (SheafOfModules.unit (Stacks.Sheaves.Differentials.ringSheaf
            (J := Opens.grothendieckTopology X) X.sheaf)).val.obj (op W) =>
          ((meromorphicSectionMul X L s).val.app (op W)).hom y)
        (mul_comm_ringSheaf_sections X W b f)).trans
        ((((meromorphicSectionMul X L s).val.app (op W)).hom.map_smul f b).trans
          ((congrArg (fun z : (meromorphicSectionSheafAsModule X L).val.obj (op W) => f • z)
              heq).trans
            ((((toMeromorphicSectionSheafAsModule X L).val.app (op W)).hom.map_smul f
                (a • g)).symm.trans
              (congrArg (fun y : L.val.obj (op W) =>
                  ((toMeromorphicSectionSheafAsModule X L).val.app (op W)).hom y)
                (smul_smul f a g))))))
  refine Iff.trans (exists_denominatorIdeal_inclusion_app_eq_iff X L s W f) ?_
  constructor
  · rintro ⟨t, ht⟩
    have ht' : ((meromorphicSectionMul X L s).val.app (op W)).hom f
        = ((toMeromorphicSectionSheafAsModule X L).val.app (op W)).hom t := ht
    obtain ⟨c₀, hc₀⟩ := hbij.surjective t
    have htail : (b • t : L.val.obj (op W)) = (b * c₀) • g :=
      (congrArg (fun y : L.val.obj (op W) => b • y) hc₀.symm).trans (smul_smul b c₀ g)
    refine ⟨c₀, hbij.injective (hinj (hkey.symm.trans ?_))⟩
    refine (congrArg (fun z : (meromorphicSectionSheafAsModule X L).val.obj (op W) => b • z)
      ht').trans ?_
    exact ((((toMeromorphicSectionSheafAsModule X L).val.app (op W)).hom.map_smul b t).symm.trans
      (congrArg (fun y : L.val.obj (op W) =>
        ((toMeromorphicSectionSheafAsModule X L).val.app (op W)).hom y) htail))
  · rintro ⟨c, hc⟩
    refine ⟨c • g, hbinj (hkey.trans ?_)⟩
    refine (congrArg (fun r : (Stacks.Sheaves.Differentials.ringSheaf (J :=
      Opens.grothendieckTopology X)
        X.sheaf).obj.obj (op W) =>
      ((toMeromorphicSectionSheafAsModule X L).val.app (op W)).hom (r • g)) hc).trans ?_
    refine (congrArg (fun y : L.val.obj (op W) =>
      ((toMeromorphicSectionSheafAsModule X L).val.app (op W)).hom y)
      (smul_smul b c g).symm).trans ?_
    exact ((toMeromorphicSectionSheafAsModule X L).val.app (op W)).hom.map_smul b (c • g)

/-- `AlgebraicGeometry.exists_denominatorIdeal_inclusion_app_eq_iff_mul_eq` on every open set
inside the one carrying the normal form: the restricted generator is again a basis, the
restricted denominator is again invertible in the meromorphic functions, and the normal form
restricts by `AlgebraicGeometry.meromorphicSectionMul_app_res_smul_eq`. -/
theorem exists_denominatorIdeal_inclusion_app_eq_iff_mul_eq_of_le
    (hmono : Mono (toMeromorphicSectionSheafAsModule X L))
    {V : X.Opens} (g : L.val.obj (op V))
    (hbij : ∀ (U : X.Opens) (hUV : U ≤ V), Function.Bijective
      (fun c : (Stacks.Sheaves.Differentials.ringSheaf (J := Opens.grothendieckTopology X)
        X.sheaf).obj.obj (op U)
        => c • (L.val.restrictₛₗ (homOfLE hUV).op g)))
    (b : Γ(X, V)) (hbu : IsUnit (X.toTotalQuotientSheaf.hom.app (op V) b))
    (a : (Stacks.Sheaves.Differentials.ringSheaf (J := Opens.grothendieckTopology X)
      X.sheaf).obj.obj (op V))
    (heq : ((meromorphicSectionMul X L s).val.app (op V)).hom b
      = ((toMeromorphicSectionSheafAsModule X L).val.app (op V)).hom (a • g))
    {W : X.Opens} (hWV : W ≤ V) (f : Γ(X, W)) :
    (∃ d : (denominatorIdeal X L s).val.obj (op W),
        ((denominatorIdealι X L s).val.app (op W)).hom d = f) ↔
      ∃ c : Γ(X, W), f * X.presheaf.map (homOfLE hWV).op (show Γ(X, V) from a)
        = X.presheaf.map (homOfLE hWV).op b * c := by
  have hbuW : IsUnit (X.toTotalQuotientSheaf.hom.app (op W)
      (X.presheaf.map (homOfLE hWV).op b)) := by
    have hnat := X.toTotalQuotientSheaf.hom.naturality (homOfLE hWV).op
    have h1 : X.toTotalQuotientSheaf.hom.app (op W) (X.presheaf.map (homOfLE hWV).op b)
        = X.totalQuotientSheaf.presheaf.map (homOfLE hWV).op
            (X.toTotalQuotientSheaf.hom.app (op V) b) := congr($hnat b)
    rw [h1]
    exact hbu.map (X.totalQuotientSheaf.presheaf.map (homOfLE hWV).op).hom
  exact exists_denominatorIdeal_inclusion_app_eq_iff_mul_eq X L s hmono W
    (L.val.restrictₛₗ (homOfLE hWV).op g) (hbij W hWV)
    (X.presheaf.map (homOfLE hWV).op b) hbuW
    ((Stacks.Sheaves.Differentials.ringSheaf (J := Opens.grothendieckTopology X) X.sheaf).obj.map
      (homOfLE hWV).op a) (meromorphicSectionMul_app_res_smul_eq X L s hWV b a g heq) f

/-! ### Tag 02P0, quasi-coherence -/

/-- **Stacks Project, Tag 02P0**, quasi-coherence of the ideal of denominators. For an
invertible sheaf of modules `L` and a meromorphic section `s` of `L`, the ideal of denominators
of `s` is a quasi-coherent sheaf of ideals.

Quasi-coherence is checked by the localization criterion on the affine opens contained in the
neighbourhoods of `AlgebraicGeometry.exists_isAffineOpen_nhds_denominator_numerator_isUnit`,
which cover `X`. There the sections of the ideal are cut out by the colon condition
`f · a ∈ (b)` of
`AlgebraicGeometry.exists_denominatorIdeal_inclusion_app_eq_iff_mul_eq_of_le`, and a colon
condition localizes by `AlgebraicGeometry.isLocalizedModule_restrictₗ_of_colon`. Regularity of
`s` is not used: the source assumes it throughout Tag 02P0, but of its conclusions only
injectivity of multiplication by `s` and the support of that map's cokernel need it. -/
@[stacks 02P0 "quasi-coherence", ega "IV 20.2.14" "special case"]
theorem denominatorIdeal_isQuasicoherent
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj
      (Stacks.Sheaves.Differentials.ringSheaf (J := Opens.grothendieckTopology X) X.sheaf).property
        L) :
    (denominatorIdeal X L s).IsQuasicoherent := by
  have hmono := mono_toMeromorphicSectionSheafAsModule X L hL
  have hmonoι : Mono (denominatorIdealι X L s) := by
    have := hmono
    exact pullback.fst_of_mono
  choose V hxV hVaff g hbij b hbu a heq using
    fun x : X => exists_isAffineOpen_nhds_denominator_numerator_isUnit X L s hL x
  refine isQuasicoherent_of_isLocalizedModule_restrictₗ_of_cover (denominatorIdeal X L s)
    (fun U => ∃ y : X, U ≤ V y) (fun x => ⟨V x, hVaff x, ⟨x, le_rfl⟩, hxV x⟩) ?_
  intro U hU hPU c
  obtain ⟨y, hUV⟩ := hPU
  have hres : ∀ t : Γ(X, V y),
      X.presheaf.map (homOfLE ((X.basicOpen_le c).trans hUV)).op t
        = algebraMap Γ(X, U) Γ(X, X.basicOpen c)
            (X.presheaf.map (homOfLE hUV).op t) := by
    intro t
    have h := CommRingCat.comp_apply (X.presheaf.map (homOfLE hUV).op)
      (X.presheaf.map (homOfLE (X.basicOpen_le c)).op) t
    rwa [← X.presheaf.map_comp] at h
  refine isLocalizedModule_restrictₗ_of_colon (denominatorIdeal X L s)
    (fun W d => ((denominatorIdealι X L s).val.app (op W)).hom d)
    (fun W => SheafOfModules.app_injective_of_mono hmonoι (op W))
    (fun W r d => ((denominatorIdealι X L s).val.app (op W)).hom.map_smul r d)
    (fun W W' h d => PresheafOfModules.naturality_apply (denominatorIdealι X L s).val
      (homOfLE h).op d)
    hU (X.presheaf.map (homOfLE hUV).op (show Γ(X, V y) from a y))
    (X.presheaf.map (homOfLE hUV).op (b y)) c
    (exists_denominatorIdeal_inclusion_app_eq_iff_mul_eq_of_le X L s hmono (g y)
      (hbij y) (b y) (hbu y) (a y) (heq y) hUV) fun f => ?_
  rw [← hres (show Γ(X, V y) from a y), ← hres (b y)]
  exact exists_denominatorIdeal_inclusion_app_eq_iff_mul_eq_of_le X L s hmono (g y)
    (hbij y) (b y) (hbu y) (a y) (heq y) ((X.basicOpen_le c).trans hUV) f

end AlgebraicGeometry

end
