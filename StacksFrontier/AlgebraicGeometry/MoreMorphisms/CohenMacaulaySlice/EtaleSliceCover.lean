module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.CohenMacaulaySlice.EtaleSliceUnramifiedPair
public import StacksFrontier.AlgebraicGeometry.Spaces.Glueing.SchemeSizeBounds
public import StacksFrontier.AlgebraicGeometry.Size.OpenCover
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf

/-!
# Étale slices through every point, assembled into one

Let `s, t : E ⟶ W` be smooth morphisms of schemes such that `(s, t) : E ⟶ W × W` is unramified.
`Stacks.AlgebraicGeometry.exists_etale_slice_of_unramified_pair` cuts, through any point `e` of
`E`, a locally closed subscheme `Y_e ⟶ W` and an open subscheme `P_e` of `E ×_{s, W} Y_e`
surjecting onto `Y_e` and étale over `W` through `t`, with a point over `t e`. This file takes the
disjoint union over all points of `E`: `Z = ∐ Y_e`, `P = ∐ P_e`. The result is the scheme-level
input of the covering step in the proof of Stacks 06N3: one slice `Z ⟶ W` and one étale `P ⟶
E ×_W Z`, with `P ⟶ Z` surjective and `P ⟶ W` étale, whose image in `W` contains `t(E)`.

Both disjoint unions stay inside any big fppf site containing `E` and `W`: each `Y_e` maps
monomorphically to `W` and each `P_e` to `E`, so their sizes are bounded by a double power of the
sizes of `W` and `E`, and so is the number of summands.

## Main results

* `Stacks.AlgebraicGeometry.exists_etale_slice_cover_of_unramified_pair`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Cardinal

universe u

namespace Stacks.AlgebraicGeometry

/-- **The étale slices through all points of `E`, as one slice.** For smooth `s, t : E ⟶ W` with
`(s, t) : E ⟶ W × W` unramified at every point, there are a morphism `ι : Z ⟶ W` and, for every
fibre product `EZ` of `s` and `ι`, an étale morphism `p : P ⟶ EZ` with `P ⟶ Z` surjective and
`P ⟶ W` (through `t`) étale, whose image in `W` contains `t e` for every point `e` of `E`; `Z`
and `P` lie in every big fppf site containing `E` and `W`.

The fibre product is quantified so that a consumer may supply its own, for instance the image of
a fibre product of a big site. -/
theorem exists_etale_slice_cover_of_unramified_pair (B : BigFppfSite.{u}) {E W : Scheme.{u}}
    (hE : B.Contains E) (hW : B.Contains W) (s t : E ⟶ W) [Smooth s] [Smooth t]
    (hDM : ∀ e : E, UnramifiedAt (pullback.lift s t (terminal.hom_ext _ _) :
      E ⟶ pullback (terminal.from W) (terminal.from W)) e) :
    ∃ (Z P : Scheme.{u}) (ι : Z ⟶ W), B.Contains Z ∧ B.Contains P ∧
      ∀ (EZ : Scheme.{u}) (pr₁ : EZ ⟶ E) (pr₂ : EZ ⟶ Z), IsPullback pr₁ pr₂ s ι →
        ∃ p : P ⟶ EZ, Etale p ∧ Etale (p ≫ pr₁ ≫ t) ∧ Function.Surjective (p ≫ pr₂).base ∧
          ∀ e : E, ∃ x : P, (p ≫ pr₁ ≫ t) x = t e := by
  classical
  choose Y P ι p hmono hp het hsurj hx using
    fun e : E => exists_etale_slice_of_unramified_pair s t hDM e
  let ιZ : (∐ Y) ⟶ W := Sigma.desc ι
  let m : ∀ e, pullback s (ι e) ⟶ pullback s ιZ := fun e =>
    pullback.map s (ι e) s ιZ (𝟙 E) (Sigma.ι Y e) (𝟙 W) (by simp) (by simp [ιZ])
  have hm : ∀ e, IsOpenImmersion (m e) := fun e => by dsimp only [m]; infer_instance
  have hmfst : ∀ e, m e ≫ pullback.fst s ιZ = pullback.fst s (ι e) := fun e => by simp [m]
  have hmsnd : ∀ e, m e ≫ pullback.snd s ιZ = pullback.snd s (ι e) ≫ Sigma.ι Y e :=
    fun e => by simp [m]
  let pZ : (∐ P) ⟶ pullback s ιZ := Sigma.desc fun e => p e ≫ m e
  have hpZ : ∀ e, Sigma.ι P e ≫ pZ = p e ≫ m e := fun e => by simp [pZ]
  -- the size bound
  let μ : Cardinal.{u} := (2 : Cardinal.{u}) ^ ((2 : Cardinal.{u}) ^ max E.size W.size)
  have hμ : μ < B.cutoff :=
    B.cutoff_isStrongPrelimit (B.cutoff_isStrongPrelimit (max_lt hE hW))
  have hℵ : ℵ₀ ≤ μ := E.aleph0_le_size.trans ((le_max_left _ _).trans
    ((cantor _).le.trans (cantor _).le))
  have hle : ∀ {X : Scheme.{u}}, X.size ≤ max E.size W.size →
      (2 : Cardinal.{u}) ^ ((2 : Cardinal.{u}) ^ X.size) ≤ μ := fun h =>
    power_le_power_left two_ne_zero (power_le_power_left two_ne_zero h)
  have hK : #E ≤ μ := (mk_scheme_le_two_power_size E).trans
    ((cantor _).le.trans (hle (le_max_left _ _)))
  have hZ : B.Contains (∐ Y) := (schemeSize_coproduct_le Y μ hℵ hK fun e =>
    (size_le_of_mono_double_power (ι e)).trans (hle (le_max_right _ _))).trans_lt hμ
  have hP : B.Contains (∐ P) := (schemeSize_coproduct_le P μ hℵ hK fun e => by
    have := hmono e
    have := hp e
    exact (size_le_of_mono_double_power (p e ≫ pullback.fst s (ι e))).trans
      (hle (le_max_left _ _))).trans_lt hμ
  have hEtloc : IsZariskiLocalAtSource (@Etale.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtSource (Q := RingHom.Etale)
  suffices H : Etale pZ ∧ Etale (pZ ≫ pullback.fst s ιZ ≫ t) ∧
      Function.Surjective (pZ ≫ pullback.snd s ιZ).base ∧
      ∀ e : E, ∃ x : (∐ P : Scheme.{u}), (pZ ≫ pullback.fst s ιZ ≫ t) x = t e by
    refine ⟨∐ Y, ∐ P, ιZ, hZ, hP, fun EZ pr₁ pr₂ hpb => ?_⟩
    obtain ⟨h₁, h₂, h₃, h₄⟩ := H
    have hfst : hpb.isoPullback.inv ≫ pr₁ = pullback.fst s ιZ := hpb.isoPullback_inv_fst
    have hsnd : hpb.isoPullback.inv ≫ pr₂ = pullback.snd s ιZ := hpb.isoPullback_inv_snd
    refine ⟨pZ ≫ hpb.isoPullback.inv, ?_, ?_, ?_, ?_⟩
    · have := h₁
      infer_instance
    · rwa [Category.assoc, reassoc_of% hfst]
    · rwa [Category.assoc, hsnd]
    · simpa only [Category.assoc, reassoc_of% hfst] using h₄
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact IsZariskiLocalAtSource.sigmaDesc fun e => by
      have := hp e
      have := hm e
      infer_instance
  · have h : pZ ≫ pullback.fst s ιZ ≫ t = Sigma.desc fun e => p e ≫ pullback.fst s (ι e) ≫ t := by
      refine Sigma.hom_ext _ _ fun e => ?_
      rw [Sigma.ι_desc, reassoc_of% (hpZ e), reassoc_of% (hmfst e)]
    rw [h]
    exact IsZariskiLocalAtSource.sigmaDesc fun e => het e
  · intro z
    obtain ⟨⟨e, y⟩, rfl⟩ := (sigmaMk Y).surjective z
    obtain ⟨x, rfl⟩ := hsurj e y
    refine ⟨Sigma.ι P e x, ?_⟩
    rw [sigmaMk_mk, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, reassoc_of% (hpZ e),
      Category.assoc, hmsnd e]
  · intro e
    obtain ⟨x, hx'⟩ := hx e
    refine ⟨Sigma.ι P e x, ?_⟩
    rw [← Scheme.Hom.comp_apply, reassoc_of% (hpZ e), reassoc_of% (hmfst e), hx']

end Stacks.AlgebraicGeometry

end
