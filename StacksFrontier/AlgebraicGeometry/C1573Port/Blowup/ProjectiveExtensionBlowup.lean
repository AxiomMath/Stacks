module

public import StacksFrontier.AlgebraicGeometry.C1573Port.Blowup.ProjectiveExtensionCentre

namespace Stacks.ProjectiveExtension.C1573
end Stacks.ProjectiveExtension.C1573

/-!
# The blowup in the centre of a rational map is the blowup of its graph closure

Let `V` be an affine scheme, `U ⊆ V` a quasi-compact quasi-separated open covered by the basic
opens of an ideal `I` of global functions, and `[g₀ : ⋯ : gₘ] : U ⟶ ℙᵐ` a morphism given by
regular functions spanning the unit ideal, with centre `𝒥 = centreSheaf U I g`. Let `t : T ⟶ V`
be a morphism which is an isomorphism over `U` and comes with a closed immersion
`c : T ⟶ V × ℙᵐ` over `V` whose second component restricts over `U` to `[g₀ : ⋯ : gₘ]`; this is
the situation of the closure of the graph of the rational map, or of any closed subscheme of
`V × ℙᵐ` containing it.

Then the blowup of `T` in the inverse image of `𝒥` is isomorphic, over `V`, to the blowup of `V`
in `𝒥`. The comparison morphisms come from the universal property of blowing up, Stacks 0806,
together with the extension of the rational map to the blowup of `V` in its centre,
`Stacks.ProjectiveExtension.C1573.exists_hom_projectiveSpace_of_isEffectiveCartierDivisor'`.

## Main results

* `Stacks.ProjectiveExtension.C1573.ker_ι_comp`: precomposing with the inclusion of a
  scheme-theoretically dense open does not change the kernel.
* `Stacks.ProjectiveExtension.C1573.exists_iso_blowUp_comap_centreSheaf`: the statement above.

## References

* [Stacks Project, Tag 0806](https://stacks.math.columbia.edu/tag/0806)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace

universe u

namespace Stacks.ProjectiveExtension

open _root_.Stacks.ProjectiveExtension.C1573
/-- Precomposing with the inclusion of a scheme-theoretically dense open does not change the
kernel of a morphism of schemes. -/
theorem C1573.ker_ι_comp {Y Z : Scheme.{u}} (W : Y.Opens)
    (hW : Scheme.Opens.IsSchemeTheoreticallyDense W) (q : Y ⟶ Z) : (W.ι ≫ q).ker = q.ker := by
  have : IsSchemeTheoreticallyDominant W.ι := by
    let i : (⊤ : Y.Opens).toScheme ⟶ Y := (⊤ : Y.Opens).ι
    have : IsIso i := by change IsIso (Scheme.topIso Y).hom; infer_instance
    have hq : IsSchemeTheoreticallyDominant ((⊤ : Y.Opens).ι ⁻¹ᵁ W).ι := hW ⊤
    apply IsSchemeTheoreticallyDominant.mk
    rw [← Scheme.Hom.ker_comp_of_isIso (i.preimageIso W).hom W.ι,
      Scheme.Hom.preimageIso_hom_ι, Scheme.Hom.ker_comp, hq.ker_eq_bot,
      Scheme.IdealSheafData.map_bot]
    exact i.ker_eq_bot
  rw [Scheme.Hom.ker_comp, IsSchemeTheoreticallyDominant.ker_eq_bot,
    Scheme.IdealSheafData.map_bot]

/-- A morphism whose restriction to a scheme-theoretically dense open factors through a closed
immersion factors through it. -/
theorem C1573.exists_lift_of_isClosedImmersion {Y Z P : Scheme.{u}} (c : P ⟶ Z)
    [IsClosedImmersion c] (q : Y ⟶ Z) (W : Y.Opens) (hW : Scheme.Opens.IsSchemeTheoreticallyDense W)
    (a : W.toScheme ⟶ P) (ha : W.ι ≫ q = a ≫ c) : ∃ h : Y ⟶ P, h ≫ c = q := by
  have hker : c.ker ≤ q.ker := by
    rw [← ker_ι_comp W hW q, ha]
    exact Scheme.Hom.le_ker_comp a c
  exact ⟨IsClosedImmersion.lift c q hker, IsClosedImmersion.lift_fac c q hker⟩

variable {V Q : Scheme.{u}} [IsAffine V] (U : V.Opens) (I : Ideal Γ(V, ⊤)) {m : ℕ}
  (g : Fin (m + 1) → Γ(V, U))

omit [IsAffine V] in
open Stacks.SectionsToProjectiveSpace in
/-- On the preimage of `U`, the extension of the rational map to the blowup of `V` in its
centre is the rational map. -/
theorem C1573.preimage_ι_comp_eq (π : Q ⟶ V)
    (hgU : Ideal.span (Set.range fun j => U.topIso.inv (g j)) = ⊤)
    (hg' : Ideal.span (Set.range fun j => (π ⁻¹ᵁ U).topIso.inv (π.app U (g j))) = ⊤)
    (f : Q ⟶ projectiveSpaceAtUniverse.{u} m)
    (hf : (π ⁻¹ᵁ U).ι ≫ f = toProjectiveSpaceAtUniverse _ hg') :
    (π ⁻¹ᵁ U).ι ≫ f = (π ∣_ U) ≫ toProjectiveSpaceAtUniverse (fun j => U.topIso.inv (g j)) hgU := by
  rw [hf, Stacks.ProjGlobalSectionsAppTop.hasPullbackNaturality (π ∣_ U) _ hgU
    (by simpa only [morphismRestrict_appTop_topIso_inv] using hg')]
  exact toProjectiveSpaceAtUniverse_congr
    (funext fun j => (morphismRestrict_appTop_topIso_inv π U (g j)).symm) _ _

/-- An endomorphism of the blowup over the base is the identity, by the universal property. -/
private theorem eq_id_of_comp_blowUpToBase {X : Scheme.{u}} {I : X.IdealSheafData}
    {hI : Stacks.Blowup.IsCartierOver I (Over.mk (blowUpToBase I))}
    (term : IsTerminal (⟨Over.mk (blowUpToBase I), hI⟩ : Stacks.Blowup.CartierOver I))
    (e : blowUp I ⟶ blowUp I) (he : e ≫ blowUpToBase I = blowUpToBase I) : e = 𝟙 _ :=
  congrArg (fun m => m.hom.left) (term.hom_ext
    (ObjectProperty.homMk (Over.homMk e he) :
      (⟨Over.mk (blowUpToBase I), hI⟩ : Stacks.Blowup.CartierOver I) ⟶ ⟨_, hI⟩) (𝟙 _))

open Stacks.SectionsToProjectiveSpace in
/-- **The blowup in the centre of a rational map is the blowup of its graph closure.** Let
`[g₀ : ⋯ : gₘ] : U ⟶ ℙᵐ` be as in
`Stacks.ProjectiveExtension.C1573.exists_hom_projectiveSpace_of_isEffectiveCartierDivisor'`, and
let `t : T ⟶ V` be an isomorphism over `U` with a closed immersion `c : T ⟶ V × ℙᵐ` over `V` whose
second component is `[g₀ : ⋯ : gₘ]` over `U`. Then the blowup of `T` in the inverse image of the
centre is isomorphic over `V` to the blowup of `V` in the centre. -/
theorem C1573.exists_iso_blowUp_comap_centreSheaf {T : Scheme.{u}} (hU : IsCompact (U : Set V))
    (hU' : IsQuasiSeparated (U : Set V)) (hIle : ∀ f ∈ I, V.basicOpen f ≤ U)
    (hIU : ∀ x ∈ U, ∃ f ∈ I, x ∈ V.basicOpen f) (hg : Ideal.span (Set.range g) = ⊤)
    (hgU : Ideal.span (Set.range fun j => U.topIso.inv (g j)) = ⊤)
    (t : T ⟶ V)
    (c : T ⟶ pullback (terminal.from V) (terminal.from (projectiveSpaceAtUniverse.{u} m)))
    [IsClosedImmersion c] (hct : c ≫ pullback.fst _ _ = t) [IsIso (t ∣_ U)]
    (hcg : (t ⁻¹ᵁ U).ι ≫ c ≫ pullback.snd _ _ =
      (t ∣_ U) ≫ toProjectiveSpaceAtUniverse (fun j => U.topIso.inv (g j)) hgU) :
    ∃ e : blowUp ((centreSheaf U I g).comap t) ≅ blowUp (centreSheaf U I g),
      e.hom ≫ blowUpToBase (centreSheaf U I g) =
        blowUpToBase ((centreSheaf U I g).comap t) ≫ t := by
  set J := centreSheaf U I g
  set π := blowUpToBase J
  set p := blowUpToBase (J.comap t)
  obtain ⟨hJπ, ⟨termJ⟩⟩ := Stacks.Blowup.isTerminal_blowUp J
  obtain ⟨hJp, ⟨termJt⟩⟩ := Stacks.Blowup.isTerminal_blowUp (J.comap t)
  obtain ⟨hWπ, hg', f, hf⟩ :=
    exists_hom_projectiveSpace_of_isEffectiveCartierDivisor' U I g π hU hU' hIle hIU hg hJπ
  have hf' := preimage_ι_comp_eq U g π hgU hg' f hf
  -- the section of `t` over `U`
  set σ : U.toScheme ⟶ T := inv (t ∣_ U) ≫ (t ⁻¹ᵁ U).ι with hσ
  have hσt : σ ≫ t = U.ι := by
    rw [hσ, Category.assoc, ← morphismRestrict_ι, IsIso.inv_hom_id_assoc]
  have hσc : σ ≫ c ≫ pullback.snd _ _ =
      toProjectiveSpaceAtUniverse (fun j => U.topIso.inv (g j)) hgU := by
    rw [hσ, Category.assoc, hcg, IsIso.inv_hom_id_assoc]
  -- the morphism `Bl_J V ⟶ V × ℙᵐ`
  set q : blowUp J ⟶ pullback (terminal.from V) (terminal.from (projectiveSpaceAtUniverse.{u} m)) :=
    pullback.lift π f (terminal.hom_ext _ _)
  have hqU : (π ⁻¹ᵁ U).ι ≫ q = ((π ∣_ U) ≫ σ) ≫ c := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, Category.assoc, Category.assoc, hct, hσt,
        morphismRestrict_ι]
    · rw [Category.assoc, pullback.lift_snd, hf', Category.assoc, Category.assoc, hσc]
  have hdense : (π ⁻¹ᵁ U).IsSchemeTheoreticallyDense :=
    hWπ ▸ Stacks.Divisors.isSchemeTheoreticallyDense_compl_of_isEffectiveCartierDivisor _ hJπ
  obtain ⟨h, hh⟩ := exists_lift_of_isClosedImmersion c q (π ⁻¹ᵁ U) hdense _ hqU
  have hht : h ≫ t = π := by rw [← hct, ← Category.assoc, hh, pullback.lift_fst]
  -- the comparison morphisms, by the universal property of the two blowups
  have hcH : Stacks.Blowup.IsCartierOver (J.comap t) (Over.mk h) := by
    change Stacks.Divisors.IsEffectiveCartierDivisor ((J.comap t).comap h)
    rw [← Scheme.IdealSheafData.comap_comp, hht]
    exact hJπ
  have hcK : Stacks.Blowup.IsCartierOver J (Over.mk (p ≫ t)) := by
    change Stacks.Divisors.IsEffectiveCartierDivisor (J.comap (p ≫ t))
    rw [Scheme.IdealSheafData.comap_comp]
    exact hJp
  set h' : blowUp J ⟶ blowUp (J.comap t) :=
    (termJt.from (⟨Over.mk h, hcH⟩ : Stacks.Blowup.CartierOver (J.comap t))).hom.left
  have hh' : h' ≫ p = h :=
    Over.w (termJt.from (⟨Over.mk h, hcH⟩ : Stacks.Blowup.CartierOver (J.comap t))).hom
  set k : blowUp (J.comap t) ⟶ blowUp J :=
    (termJ.from (⟨Over.mk (p ≫ t), hcK⟩ : Stacks.Blowup.CartierOver J)).hom.left
  have hk : k ≫ π = p ≫ t :=
    Over.w (termJ.from (⟨Over.mk (p ≫ t), hcK⟩ : Stacks.Blowup.CartierOver J)).hom
  have e1 : h' ≫ k = 𝟙 _ := eq_id_of_comp_blowUpToBase termJ _
    (by rw [Category.assoc, hk, ← Category.assoc, hh', hht])
  -- `k ≫ h = p`, checked after the closed immersion `c`
  have hYdense : ((p ≫ t) ⁻¹ᵁ U).IsSchemeTheoreticallyDense := by
    have heq : (p ≫ t) ⁻¹ᵁ U = (J.comap (p ≫ t)).support.compl := by
      ext y
      change (p ≫ t) y ∈ U ↔ y ∉ (J.comap (p ≫ t)).support
      rw [Scheme.IdealSheafData.support_comap]
      change (p ≫ t) y ∈ U ↔ ¬ (p ≫ t) y ∈ J.support
      have key := mem_support_centreSheaf_iff U I g hU hU' hIle hIU hg ((p ≫ t) y)
      exact ⟨fun h1 h2 => key.1 h2 h1, fun h1 => by_contra fun h2 => h1 (key.2 h2)⟩
    rw [heq, Scheme.IdealSheafData.comap_comp]
    exact Stacks.Divisors.isSchemeTheoreticallyDense_compl_of_isEffectiveCartierDivisor _ hJp
  set Y := (p ≫ t) ⁻¹ᵁ U with hY
  have hr1 : Set.range (Y.ι ≫ p).base ⊆ Set.range (t ⁻¹ᵁ U).ι.base := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨y, rfl⟩
    exact y.2
  have hr2 : Set.range (Y.ι ≫ k).base ⊆ Set.range (π ⁻¹ᵁ U).ι.base := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨y, rfl⟩
    change (Y.ι ≫ k ≫ π).base y ∈ U
    rw [hk]
    exact y.2
  set a₁ := IsOpenImmersion.lift (t ⁻¹ᵁ U).ι (Y.ι ≫ p) hr1 with ha₁
  set a₂ := IsOpenImmersion.lift (π ⁻¹ᵁ U).ι (Y.ι ≫ k) hr2 with ha₂
  have ha₁' : a₁ ≫ (t ⁻¹ᵁ U).ι = Y.ι ≫ p := IsOpenImmersion.lift_fac _ _ _
  have ha₂' : a₂ ≫ (π ⁻¹ᵁ U).ι = Y.ι ≫ k := IsOpenImmersion.lift_fac _ _ _
  have ha : a₁ ≫ (t ∣_ U) = a₂ ≫ (π ∣_ U) := by
    rw [← cancel_mono U.ι, Category.assoc, Category.assoc, morphismRestrict_ι,
      morphismRestrict_ι, ← Category.assoc, ha₁', ← Category.assoc, ha₂', Category.assoc,
      Category.assoc, hk]
  have hkh : k ≫ h = p := by
    rw [← cancel_mono c, Category.assoc, hh]
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, hk, Category.assoc, hct]
    · rw [Category.assoc, pullback.lift_snd]
      refine eq_of_isSchemeTheoreticallyDense _ _ Y hYdense ?_
      simp only [Category.assoc]
      rw [← reassoc_of% ha₂', hf', ← reassoc_of% ha₁', hcg, ← Category.assoc, ← ha,
        Category.assoc]
  have e2 : k ≫ h' = 𝟙 _ := eq_id_of_comp_blowUpToBase termJt _
    (by rw [Category.assoc, hh', hkh])
  exact ⟨{ hom := k, inv := h', hom_inv_id := e2, inv_hom_id := e1 }, hk⟩

end Stacks.ProjectiveExtension

end
