module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.Noetherian.Nilpotent

/-!
# Morphisms from quasi-compact schemes into the support of an ideal sheaf

Let `X` be a locally Noetherian scheme and `J` an ideal sheaf on `X`. A morphism `g : V ⟶ X`
from a quasi-compact scheme whose image lies in the support of `J` factors through the closed
subscheme cut out by some power `J ^ n`: the kernel of `g` contains `J ^ n`.

## Main results

* `AlgebraicGeometry.Scheme.Hom.exists_pow_le_ker_of_range_subset_support`: the kernel of `g`
  contains a power of `J`.
* `AlgebraicGeometry.Scheme.Hom.exists_lift_subschemeι_pow_of_range_subset_support`: `g` factors
  through `(J ^ n).subschemeι` for some `n`.
* `AlgebraicGeometry.Scheme.Hom.exists_lift_specMap_quotient_pow`: the affine form, a morphism
  from an affine scheme into `V(I) ⊆ Spec A` factors through some `Spec (A ⧸ I ^ (n + 1))`.

## Implementation notes

Over an affine open `W` of `V` mapping into an affine open `U` of `X`, the ideal `J(U)` is finitely
generated (`Γ(X, U)` is Noetherian) and its image in `Γ(V, W)` consists of functions vanishing at
every point, hence lies in the nilradical; a finitely generated ideal in the nilradical is
nilpotent. Finitely many such pairs `(W, U)` cover `V`, which bounds the exponent. For an arbitrary
affine open `U'` of `X` the vanishing of the image of `J(U') ^ n` is checked on stalks: near a
point of `V` it is read on a basic open of `X` which is basic both in `U'` and in one of the
chosen `U`, where the two ideals `J(U')` and `J(U)` generate the same ideal.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme

variable {X V : Scheme.{u}}

/-- Let `W` be an affine open of `V` mapping into an affine open `U` of `X` under `g`, and let
`J(U)` be finitely generated. If every point of `W` maps into the support of `J`, a power of
`J(U)` dies in `Γ(V, W)`. -/
theorem Hom.exists_pow_le_ker_appLE_of_mem_support (g : V ⟶ X) (J : X.IdealSheafData)
    {U : X.affineOpens} {W : V.Opens} (hW : IsAffineOpen W) (e : W ≤ g ⁻¹ᵁ U.1)
    (hfg : (J.ideal U).FG) (hJ : ∀ y ∈ W, g y ∈ J.support) :
    ∃ m : ℕ, J.ideal U ^ m ≤ RingHom.ker (g.appLE U.1 W e).hom := by
  set φ := (g.appLE U.1 W e).hom
  have hK : (J.ideal U).map φ ≤ _root_.nilradical Γ(V, W) := by
    rw [Ideal.map_le_iff_le_comap]
    intro j hj
    change φ j ∈ _root_.nilradical Γ(V, W)
    rw [mem_nilradical, V.isNilpotent_iff_basicOpen_eq_bot_of_isCompact hW.isCompact,
      Scheme.basicOpen_appLE, eq_bot_iff]
    rintro y ⟨hyW, hy⟩
    have hgy := hJ y hyW
    rw [IdealSheafData.mem_support_iff_of_mem (U := U) (e hyW), Scheme.mem_zeroLocus_iff] at hgy
    exact hgy j hj hy
  obtain ⟨m, hm⟩ := (Ideal.FG.isNilpotent_iff_le_nilradical (hfg.map φ)).mpr hK
  refine ⟨m, fun s hs => ?_⟩
  have hm' : (J.ideal U).map φ ^ m = ⊥ := hm
  rw [RingHom.mem_ker, ← Ideal.mem_bot, ← hm', ← Ideal.map_pow]
  exact Ideal.mem_map_of_mem _ hs

/-- **A morphism from a quasi-compact scheme into the support of an ideal sheaf kills a power of
it.** Let `X` be locally Noetherian, `J` an ideal sheaf on `X` and `g : V ⟶ X` a morphism from a
quasi-compact scheme with image in the support of `J`. Then `J ^ n ≤ ker g` for some `n`. -/
theorem Hom.exists_pow_le_ker_of_range_subset_support [IsLocallyNoetherian X] [CompactSpace V]
    (g : V ⟶ X) (J : X.IdealSheafData) (hg : Set.range g ⊆ J.support) :
    ∃ n : ℕ, J ^ n ≤ g.ker := by
  -- an affine open of `V` around each point, mapping into an affine open of `X`
  have hloc : ∀ y : V, ∃ (U : X.affineOpens) (W : V.affineOpens), y ∈ W.1 ∧ W.1 ≤ g ⁻¹ᵁ U.1 := by
    intro y
    obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (g y)) (⊤ : X.Opens).2
    obtain ⟨_, ⟨W, hW, rfl⟩, hyW, hWU⟩ :=
      V.isBasis_affineOpens.exists_subset_of_mem_open (a := y)
        (show y ∈ ((g ⁻¹ᵁ U : V.Opens) : Set V) from hxU) (g ⁻¹ᵁ U).2
    exact ⟨⟨U, hU⟩, ⟨W, hW⟩, hyW, hWU⟩
  choose U W hyW hWU using hloc
  have hmem : ∀ y : V, ∀ z ∈ (W y).1, g z ∈ J.support := fun _ z _ => hg ⟨z, rfl⟩
  have hexp : ∀ y : V, ∃ m : ℕ, J.ideal (U y) ^ m ≤ RingHom.ker (g.appLE (U y).1 (W y).1
      (hWU y)).hom := fun y =>
    haveI := IsLocallyNoetherian.component_noetherian (X := X) (U y)
    g.exists_pow_le_ker_appLE_of_mem_support J (W y).2 (hWU y) (IsNoetherian.noetherian _)
      (hmem y)
  choose m hm using hexp
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover (fun y => ((W y).1 : Set V))
    (fun y => (W y).1.2) (fun y _ => Set.mem_iUnion.2 ⟨y, hyW y⟩)
  refine ⟨s.sup m, IdealSheafData.le_ofIdeals_iff.mpr fun U' a ha => ?_⟩
  change a ∈ J.ideal U' ^ s.sup m at ha
  rw [RingHom.mem_ker]
  refine TopCat.Presheaf.section_ext V.sheaf (g ⁻¹ᵁ U'.1) _ 0 fun y hy => ?_
  obtain ⟨y₀, hy₀s, hy₀⟩ := Set.mem_iUnion₂.1 (hs (Set.mem_univ y))
  obtain ⟨r, r', hrr', hr⟩ := exists_basicOpen_le_affine_inter U'.2 (U y₀).2 (g y)
    ⟨hy, hWU y₀ hy₀⟩
  set O : X.affineOpens := ⟨X.basicOpen r, U'.2.basicOpen r⟩ with hO
  have hOU' : O.1 ≤ U'.1 := X.basicOpen_le r
  have hOU : O.1 ≤ (U y₀).1 := hrr'.trans_le (X.basicOpen_le r')
  set W' : V.Opens := (W y₀).1 ⊓ g ⁻¹ᵁ O.1
  have hW'O : W' ≤ g ⁻¹ᵁ O.1 := inf_le_right
  have hyW' : y ∈ W' := ⟨hy₀, hr⟩
  have hW'U' : W' ≤ g ⁻¹ᵁ U'.1 := fun z hz => hOU' hz.2
  -- the restriction of `a` to `O` lies in the ideal generated by `J(U y₀) ^ m y₀`
  have hres : (X.presheaf.map (homOfLE hOU').op).hom a ∈
      (J.ideal (U y₀) ^ m y₀).map (X.presheaf.map (homOfLE hOU).op).hom := by
    have h₁ : (X.presheaf.map (homOfLE hOU').op).hom a ∈ J.ideal O ^ s.sup m := by
      rw [← J.map_ideal (U := O) (V := U') hOU', ← Ideal.map_pow]
      exact Ideal.mem_map_of_mem _ ha
    rw [← J.map_ideal (U := O) (V := U y₀) hOU, ← Ideal.map_pow] at h₁
    exact Ideal.map_mono (Ideal.pow_le_pow_right (Finset.le_sup hy₀s)) h₁
  -- which dies on `W'`
  have hkill : (J.ideal (U y₀) ^ m y₀).map (X.presheaf.map (homOfLE hOU).op).hom ≤
      RingHom.ker (g.appLE O.1 W' hW'O).hom := by
    rw [Ideal.map_le_iff_le_comap]
    intro b hb
    have hb' := hm y₀ hb
    rw [RingHom.mem_ker] at hb'
    rw [Ideal.mem_comap, RingHom.mem_ker, ← CommRingCat.comp_apply, Scheme.Hom.map_appLE,
      ← Scheme.Hom.appLE_map (e := hWU y₀) (i := (homOfLE (inf_le_left : W' ≤ (W y₀).1)).op),
      CommRingCat.comp_apply, hb', map_zero]
  have hzero : (V.presheaf.map (homOfLE hW'U').op).hom ((g.app U'.1).hom a) = 0 := by
    have := hkill hres
    rw [RingHom.mem_ker, ← CommRingCat.comp_apply, Scheme.Hom.map_appLE] at this
    rw [← CommRingCat.comp_apply, ← Scheme.Hom.appLE]
    exact this
  change V.presheaf.germ _ y hy _ = V.presheaf.germ _ y hy 0
  rw [map_zero, ← TopCat.Presheaf.germ_res_apply V.presheaf (homOfLE hW'U') y hyW']
  rw [hzero]
  exact map_zero _

/-- **A morphism from a quasi-compact scheme into the support of an ideal sheaf factors through
an infinitesimal neighbourhood.** Let `X` be locally Noetherian, `J` an ideal sheaf on `X` and
`g : V ⟶ X` a morphism from a quasi-compact scheme with image in the support of `J`. Then `g`
factors through the closed subscheme cut out by `J ^ n` for some `n`. -/
theorem Hom.exists_lift_subschemeι_pow_of_range_subset_support [IsLocallyNoetherian X]
    [CompactSpace V] (g : V ⟶ X) (J : X.IdealSheafData) (hg : Set.range g ⊆ J.support) :
    ∃ n : ℕ, ∃ h : V ⟶ (J ^ n).subscheme, h ≫ (J ^ n).subschemeι = g := by
  obtain ⟨n, hn⟩ := g.exists_pow_le_ker_of_range_subset_support J hg
  exact ⟨n, g.toImage ≫ IdealSheafData.inclusion hn, by
    rw [Category.assoc, IdealSheafData.inclusion_subschemeι, Hom.toImage_imageι]⟩

/-- **A morphism from an affine scheme into `V(I) ⊆ Spec A` factors through a thickening.** Let
`A` be Noetherian, `I ⊆ A` an ideal and `g : W ⟶ Spec A` a morphism from an affine scheme with
image in `V(I)`. Then `g` factors through `Spec (A ⧸ I ^ (n + 1)) ⟶ Spec A` for some `n`. -/
theorem Hom.exists_lift_specMap_quotient_pow {W : Scheme.{u}} [IsAffine W] {A : CommRingCat.{u}}
    [IsNoetherianRing A] (I : Ideal A) (g : W ⟶ Spec A)
    (hg : ∀ x, g x ∈ PrimeSpectrum.zeroLocus (I : Set A)) :
    ∃ n : ℕ, ∃ ℓ : W ⟶ Spec (.of (A ⧸ I ^ (n + 1))),
      ℓ ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk _)) = g := by
  set φ := (Scheme.ΓSpecIso A).inv ≫ g.appTop
  have hφ : W.toSpecΓ ≫ Spec.map φ = g := by
    rw [Spec.map_comp, ← Category.assoc, ← Scheme.toSpecΓ_naturality, Category.assoc,
      toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]
  have hnil : I.map φ.hom ≤ (⊥ : Ideal Γ(W, ⊤)).radical := by
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    have hn : IsNilpotent (φ.hom a) := by
      rw [nilpotent_iff_mem_prime]
      intro P hP
      obtain ⟨y, hy⟩ := W.toSpecΓ.homeomorph.surjective ⟨P, hP⟩
      have hgy := hg y
      have h₂ : g y = PrimeSpectrum.comap φ.hom ⟨P, hP⟩ := by
        rw [← hφ, Scheme.Hom.comp_apply]
        exact congrArg (Spec.map φ) hy
      rw [h₂] at hgy
      exact hgy ha
    exact hn.imp fun _ => (Submodule.mem_bot _).2
  obtain ⟨N, hN⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hnil (I.fg_of_isNoetherianRing.map _)
  have hker : I ^ (N + 1) ≤ RingHom.ker φ.hom :=
    (Ideal.pow_le_pow_right (Nat.le_succ N)).trans ((Ideal.map_eq_bot_iff_le_ker _).1
      (by rw [Ideal.map_pow]; exact le_bot_iff.1 hN))
  refine ⟨N, W.toSpecΓ ≫ Spec.map (CommRingCat.ofHom
    (Ideal.Quotient.lift _ φ.hom fun a ha => hker ha)), ?_⟩
  rw [Category.assoc, ← Spec.map_comp, ← hφ]
  congr 2

end AlgebraicGeometry.Scheme

end
