module

public import StacksFrontier.AlgebraicGeometry.Duality.NormalizedDualizingTransitivity
public import StacksFrontier.AlgebraicGeometry.Duality.NormalizedOnOpens

/-!
# Restricting a normalized dualizing complex to an open

Let `ω_X^•` be a dualizing complex on `X` normalized relative to `ω_S^•`, i.e. with
isomorphisms `α_W : ω_X^•|_W ≅ (W → S)^! ω_S^•` for the opens `W` separated over `S`, compatible
with restriction. For an open `V ⊆ X`, the restriction `ω_X^•|_V = (V → X)^! ω_X^•` is
normalized relative to `ω_S^•` as a complex on `V`: an open `W'` of `V` is identified with the open
`W = V ∩ W'` of `X`, and `α_{W'}` is `α_W` transported along `W' ≅ W` by the comparisons of
[Stacks, Tag 0ATX].

## Main definitions

* `Stacks.Duality.NormalizedOnOpens.restrict` — `ω_X^•|_V`, normalized relative to `ω_S^•`.

## Main results

* `Stacks.Duality.UpperShriek.restrictCompare_comp` — restricting a comparison twice is
  restricting it along the composite.

## References

* [Stacks Project, Tag 0AU5](https://stacks.math.columbia.edu/tag/0AU5)
* [Stacks Project, Tag 0ATY](https://stacks.math.columbia.edu/tag/0ATY)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u v v'

namespace Stacks.Duality

namespace IsFiniteTypeOverNoetherian

variable {X S : Scheme.{u}} {p : X ⟶ S}

/-- An open subscheme of a scheme of finite type over a Noetherian base is of finite type over
the base. -/
theorem ι_comp (hp : IsFiniteTypeOverNoetherian p) (V : X.Opens) :
    IsFiniteTypeOverNoetherian (V.ι ≫ p) :=
  let := hp.locallyOfFiniteType
  let := hp.quasiCompact
  let := hp.source_noetherian
  let : NoetherianSpace V.toScheme := V.ι.isOpenEmbedding.isInducing.noetherianSpace
  let : QuasiCompact V.ι := quasiCompact_of_noetherianSpace_source _
  { base_noetherian := hp.base_noetherian
    locallyOfFiniteType := inferInstance
    quasiCompact := inferInstance }

/-- An isomorphism between open subschemes of schemes of finite type over a Noetherian base is
shriekable. -/
theorem isShriekable_hom_of_iso {Z : Scheme.{u}} {q : Z ⟶ S} (hp : IsFiniteTypeOverNoetherian p)
    (hq : IsFiniteTypeOverNoetherian q) (V : X.Opens) (W : Z.Opens)
    (e : V.toScheme ≅ W.toScheme) : IsShriekable e.hom :=
  let := hp.source_noetherian
  let : NoetherianSpace V.toScheme := V.ι.isOpenEmbedding.isInducing.noetherianSpace
  { target_noetherian := hq.opens_noetherian W
    separatedFiniteType :=
      ⟨⟨inferInstance, inferInstance⟩, quasiCompact_of_noetherianSpace_source _⟩ }

/-- The image in `X` of an open `W` of an open `V ⊆ X`, separated over the base, is separated over
the base. -/
theorem isShriekable_image (hp : IsFiniteTypeOverNoetherian p) (V : X.Opens)
    (W : V.toScheme.Opens) (hW : IsShriekable (W.ι ≫ V.ι ≫ p)) :
    IsShriekable ((V.ι ''ᵁ W).ι ≫ p) :=
  IsShriekable.of_eq (show (V.ι.isoImage W).symm.hom ≫ W.ι ≫ V.ι ≫ p = (V.ι ''ᵁ W).ι ≫ p by
      rw [Iso.symm_hom, V.ι.isoImage_inv_ι_assoc])
    ((hp.isShriekable_hom_of_iso (hp.ι_comp V) _ _ (V.ι.isoImage W).symm).comp hW)

end IsFiniteTypeOverNoetherian

namespace UpperShriek

variable {𝒟 : Scheme.{u} → Type v} [∀ X : Scheme.{u}, Category.{v'} (𝒟 X)] (A : UpperShriek 𝒟)

/-- Restricting a comparison along `r₁` and then along `r₂` is restricting it along
`r₂ ≫ r₁`: the coherence of [Stacks, Tag 0ATY] on both sides. -/
theorem restrictCompare_comp {W₃ W₂ W₁ T Z : Scheme.{u}} {r₂ : W₃ ⟶ W₂} {r₁ : W₂ ⟶ W₁}
    {r : W₃ ⟶ W₁} {m : W₁ ⟶ T} {n : W₁ ⟶ Z} {m₁ : W₂ ⟶ T} {n₁ : W₂ ⟶ Z} {m₂ : W₃ ⟶ T}
    {n₂ : W₃ ⟶ Z} (hr : r₂ ≫ r₁ = r) (h₁m : r₁ ≫ m = m₁) (h₁n : r₁ ≫ n = n₁)
    (h₂m : r₂ ≫ m₁ = m₂) (h₂n : r₂ ≫ n₁ = n₂) (hm₂ : r ≫ m = m₂) (hn₂ : r ≫ n = n₂)
    (hr₂ : IsShriekable r₂) (hr₁ : IsShriekable r₁) (hr' : IsShriekable r)
    (hm : IsShriekable m) (hn : IsShriekable n) (hm₁ : IsShriekable m₁)
    (hn₁ : IsShriekable n₁) (hm₂' : IsShriekable m₂) (hn₂' : IsShriekable n₂) {ω : 𝒟 T}
    {L : 𝒟 Z} (Θ : (A.shriek m hm).obj ω ≅ (A.shriek n hn).obj L) :
    A.restrictCompare h₂m h₂n hr₂ hm₁ hn₁ hm₂' hn₂'
        (A.restrictCompare h₁m h₁n hr₁ hm hn hm₁ hn₁ Θ) =
      A.restrictCompare hm₂ hn₂ hr' hm hn hm₂' hn₂' Θ := by
  have pm := A.factorIso_assoc hr h₁m hm₂ h₂m hr₂ hr₁ hm hr' hm₁ hm₂' ω
  have pn := A.factorIso_assoc hr h₁n hn₂ h₂n hr₂ hr₁ hn hr' hn₁ hn₂' L
  have pniso : (A.factorIso h₂n hr₂ hn₁ hn₂').app L ≪≫
      (A.shriek r₂ hr₂).mapIso ((A.factorIso h₁n hr₁ hn hn₁).app L) =
        (A.factorIso hn₂ hr' hn hn₂').app L ≪≫
          (A.factorIso hr hr₂ hr₁ hr').app ((A.shriek n hn).obj L) := Iso.ext pn
  have pninv := congrArg Iso.inv pniso
  have nat := (A.factorIso hr hr₂ hr₁ hr').hom.naturality Θ.hom
  simp only [Iso.trans_inv, Functor.mapIso_inv, Iso.app_inv, Functor.comp_map] at pninv nat
  refine Iso.ext ?_
  simp only [restrictCompare, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Iso.app_hom,
    Iso.app_inv, Functor.map_comp, Category.assoc]
  rw [reassoc_of% pm, ← reassoc_of% nat, pninv, Iso.hom_inv_id_app_assoc]

/-- `restrictCompare` depends on the morphism it restricts along only. -/
theorem restrictCompare_congr {W' W T Z : Scheme.{u}} {r r' : W' ⟶ W} (e : r = r') {m : W ⟶ T}
    {n : W ⟶ Z} {m' : W' ⟶ T} {n' : W' ⟶ Z} (hrm : r ≫ m = m') (hrn : r ≫ n = n')
    (hr : IsShriekable r) (hrm' : r' ≫ m = m') (hrn' : r' ≫ n = n') (hr' : IsShriekable r')
    (hm : IsShriekable m) (hn : IsShriekable n) (hm' : IsShriekable m') (hn' : IsShriekable n')
    {ω : 𝒟 T} {L : 𝒟 Z} (Θ : (A.shriek m hm).obj ω ≅ (A.shriek n hn).obj L) :
    A.restrictCompare hrm hrn hr hm hn hm' hn' Θ =
      A.restrictCompare hrm' hrn' hr' hm hn hm' hn' Θ := by
  subst e
  rfl

/-- Restricting a normalization isomorphism is `restrictCompare` along the inclusion. -/
theorem restrictLocalIso_eq_restrictCompare {X S : Scheme.{u}} {p : X ⟶ S}
    (hp : IsFiniteTypeOverNoetherian p) (ω : 𝒟 S) (K : 𝒟 X) {W U : X.Opens} (h : W ≤ U)
    (hU : IsShriekable (U.ι ≫ p)) (α : A.restrictTo hp U K ≅ A.localModel hU ω) :
    A.restrictLocalIso hp ω K h hU α =
      A.restrictCompare (X.homOfLE_ι h)
        (show X.homOfLE h ≫ U.ι ≫ p = W.ι ≫ p by rw [← Category.assoc, X.homOfLE_ι])
        (hp.isShriekable_homOfLE h) (hp.isShriekable_ι U) hU (hp.isShriekable_ι W)
        (hp.isShriekable_le h hU) α :=
  rfl

/-- Restricting along `r : W' ⟶ W` a comparison precomposed with `m^!(g^! K) ≅ (m ≫ g)^! K`. -/
theorem restrictCompare_factorIso_symm_trans {W' W V T Z : Scheme.{u}} {r : W' ⟶ W}
    {m : W ⟶ V} {g : V ⟶ T} {n : W ⟶ Z} {m' : W' ⟶ V} {n' : W' ⟶ Z}
    (hrm : r ≫ m = m') (hrn : r ≫ n = n') (hr : IsShriekable r) (hm : IsShriekable m)
    (hg : IsShriekable g) (hn : IsShriekable n) (hm' : IsShriekable m') (hn' : IsShriekable n')
    (hmg : IsShriekable (m ≫ g)) (hm'g : IsShriekable (m' ≫ g)) {K : 𝒟 T} {L : 𝒟 Z}
    (Θ : (A.shriek (m ≫ g) hmg).obj K ≅ (A.shriek n hn).obj L) :
    A.restrictCompare hrm hrn hr hm hn hm' hn' (((A.factorIso rfl hm hg hmg).app K).symm ≪≫ Θ) =
      ((A.factorIso rfl hm' hg hm'g).app K).symm ≪≫
        A.restrictCompare (by rw [← Category.assoc, hrm]) hrn hr hmg hn hm'g hn' Θ := by
  have pm := A.factorIso_assoc hrm rfl rfl (by rw [← Category.assoc, hrm]) hr hm hg hm' hmg
    hm'g K
  refine Iso.ext ?_
  simp only [restrictCompare, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Iso.app_hom,
    Iso.app_inv, Functor.map_comp, Category.assoc]
  rw [← cancel_epi ((A.factorIso rfl hm' hg hm'g).hom.app K), Iso.hom_inv_id_app_assoc,
    ← reassoc_of% pm, ← Functor.map_comp_assoc, Iso.hom_inv_id_app,
    CategoryTheory.Functor.map_id, Category.id_comp]

end UpperShriek


namespace NormalizedOnOpens

variable {𝒟 : Scheme.{u} → Type v} [∀ X : Scheme.{u}, Category.{v'} (𝒟 X)] {A : UpperShriek 𝒟}
  {X S : Scheme.{u}} {p : X ⟶ S} {hp : IsFiniteTypeOverNoetherian p} {ωS : 𝒟 S}

/-- The normalization isomorphism of `ω_X^•|_V` on an open `W` of `V`: the one of `ω_X^•` on the
image of `W` in `X`, transported along `W ≅ V ∩ W`. -/
def restrictLocalIsoOfImage (𝒦 : NormalizedOnOpens A hp ωS) (V : X.Opens)
    (W : V.toScheme.Opens) (hW : IsShriekable (W.ι ≫ V.ι ≫ p)) :
    A.restrictTo (hp.ι_comp V) W (A.restrictTo hp V 𝒦.complex) ≅ A.localModel hW ωS :=
  ((A.factorIso rfl ((hp.ι_comp V).isShriekable_ι W) (hp.isShriekable_ι V)
      (((hp.ι_comp V).isShriekable_ι W).comp (hp.isShriekable_ι V))).app 𝒦.complex).symm ≪≫
    A.restrictCompare (V.ι.isoImage_hom_ι W) (by rw [V.ι.isoImage_hom_ι_assoc])
      ((hp.ι_comp V).isShriekable_hom_of_iso hp _ _ (V.ι.isoImage W))
      (hp.isShriekable_ι _) (hp.isShriekable_image V W hW)
      (((hp.ι_comp V).isShriekable_ι W).comp (hp.isShriekable_ι V)) hW
      (𝒦.localIso _ (hp.isShriekable_image V W hW))

/-- **`ω_X^•|_V` is normalized relative to `ω_S^•`**: for an open `V ⊆ X`, the restriction of a
dualizing complex normalized relative to `ω_S^•` with the normalizations
`restrictLocalIsoOfImage`. -/
def restrict (𝒦 : NormalizedOnOpens A hp ωS) (V : X.Opens) :
    NormalizedOnOpens A (hp.ι_comp V) ωS where
  complex := A.restrictTo hp V 𝒦.complex
  localIso W hW := 𝒦.restrictLocalIsoOfImage V W hW
  compat {W'' W'} h hW' hW'' := by
    have h₂ : V.ι ''ᵁ W'' ≤ V.ι ''ᵁ W' := V.ι.opensFunctor.monotone h
    have hr : V.toScheme.homOfLE h ≫ (V.ι.isoImage W').hom =
        (V.ι.isoImage W'').hom ≫ X.homOfLE h₂ := by
      rw [← cancel_mono (V.ι ''ᵁ W').ι]
      simp only [Category.assoc, Scheme.Hom.isoImage_hom_ι, Scheme.homOfLE_ι,
        Scheme.homOfLE_ι_assoc]
    have hc := 𝒦.compat h₂ (hp.isShriekable_image V W' hW') (hp.isShriekable_image V W'' hW'')
    rw [UpperShriek.restrictLocalIso_eq_restrictCompare] at hc ⊢
    simp only [restrictLocalIsoOfImage]
    rw [UpperShriek.restrictCompare_factorIso_symm_trans, ← hc,
      UpperShriek.restrictCompare_comp _ (rfl : V.toScheme.homOfLE h ≫ _ = _),
      UpperShriek.restrictCompare_comp _ (rfl : (V.ι.isoImage W'').hom ≫ X.homOfLE h₂ = _)]
    · congr 1
      exact UpperShriek.restrictCompare_congr _ hr _ _ _ _ _ _ _ _ _ _ _
    all_goals first
      | exact (by rw [Category.assoc, X.homOfLE_ι, V.ι.isoImage_hom_ι] :
          ((V.ι.isoImage W'').hom ≫ X.homOfLE h₂) ≫ (V.ι ''ᵁ W').ι = W''.ι ≫ V.ι)
      | exact (by rw [Category.assoc, X.homOfLE_ι_assoc, V.ι.isoImage_hom_ι_assoc] :
          ((V.ι.isoImage W'').hom ≫ X.homOfLE h₂) ≫ (V.ι ''ᵁ W').ι ≫ p = W''.ι ≫ V.ι ≫ p)
      | exact (by rw [Category.assoc, V.ι.isoImage_hom_ι, Scheme.homOfLE_ι_assoc] :
          (V.toScheme.homOfLE h ≫ (V.ι.isoImage W').hom) ≫ (V.ι ''ᵁ W').ι = W''.ι ≫ V.ι)
      | exact (by rw [Category.assoc, V.ι.isoImage_hom_ι_assoc, Scheme.homOfLE_ι_assoc] :
          (V.toScheme.homOfLE h ≫ (V.ι.isoImage W').hom) ≫ (V.ι ''ᵁ W').ι ≫ p = W''.ι ≫ V.ι ≫ p)
      | exact ((hp.ι_comp V).isShriekable_hom_of_iso hp _ _ (V.ι.isoImage W'')).comp
          (hp.isShriekable_homOfLE h₂)
      | exact ((hp.ι_comp V).isShriekable_homOfLE h).comp
          ((hp.ι_comp V).isShriekable_hom_of_iso hp _ _ (V.ι.isoImage W'))

/-- The underlying complex of `𝒦.restrict V` is the restriction `ω_X^•|_V` of the underlying
complex of `𝒦`. -/
@[simp]
theorem restrict_complex (𝒦 : NormalizedOnOpens A hp ωS) (V : X.Opens) :
    (𝒦.restrict V).complex = A.restrictTo hp V 𝒦.complex :=
  rfl

end NormalizedOnOpens

end Stacks.Duality

end
