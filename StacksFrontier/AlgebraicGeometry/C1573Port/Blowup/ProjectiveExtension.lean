module

public import StacksFrontier.AlgebraicGeometry.Blowup.ClassifyingMorphism
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartierComplement
public import StacksFrontier.AlgebraicGeometry.ProjGlobalSectionsAppTop.Consumers
public import StacksFrontier.Examples.Spaces.ProductOfProjectiveLines

namespace Stacks.ProjectiveExtension.C1573
end Stacks.ProjectiveExtension.C1573

/-!
# Extending a morphism to projective space across a scheme-theoretically dense open

Two general facts about morphisms of schemes into a separated scheme `Y`, used to resolve a
rational map to projective space by an explicit blowup.

* `Stacks.ProjectiveExtension.C1573.eq_of_isSchemeTheoreticallyDense`: two morphisms into a
  separated scheme which agree on a scheme-theoretically dense open subscheme of the source are
  equal.
* `Stacks.ProjectiveExtension.C1573.exists_hom_of_local`: a morphism `φ : W ⟶ Y` defined on a
  scheme-theoretically dense open `W ⊆ Q` extends to `Q` as soon as it extends locally on `Q`.

## References

* [Stacks Project, Tag 01RH](https://stacks.math.columbia.edu/tag/01RH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace

universe u

namespace Stacks.ProjectiveExtension

open _root_.Stacks.ProjectiveExtension.C1573
/-- **Stacks 01RH, absolute form.** Two morphisms into a separated scheme which agree on a
scheme-theoretically dense open subscheme of the source are equal. -/
theorem C1573.eq_of_isSchemeTheoreticallyDense {T Y : Scheme.{u}} [IsSeparated (terminal.from Y)]
    (g₁ g₂ : T ⟶ Y) (U : T.Opens) (hU : Scheme.Opens.IsSchemeTheoreticallyDense U)
    (h : U.ι ≫ g₁ = U.ι ≫ g₂) : g₁ = g₂ :=
  Stacks.Blowup.eq_of_eq_restrict (terminal.from Y) g₁ g₂ (f := terminal.from T)
    (terminal.hom_ext _ _) (terminal.hom_ext _ _) U hU h

/-- An open subscheme `W ⊆ Q` which is scheme-theoretically dense stays so in every open
`O ⊆ Q`. -/
theorem C1573.isSchemeTheoreticallyDense_preimage {Q : Scheme.{u}} (W : Q.Opens)
    (hW : Scheme.Opens.IsSchemeTheoreticallyDense W) (O : Q.Opens) :
    Scheme.Opens.IsSchemeTheoreticallyDense (O.ι ⁻¹ᵁ W) :=
  AlgebraicGeometry.Scheme.Opens.isSchemeTheoreticallyDense_preimage_of_isOpenImmersion W hW O.ι

/-- **Glueing local extensions across a scheme-theoretically dense open.** Let `W ⊆ Q` be a
scheme-theoretically dense open and `φ : W ⟶ Y` a morphism into a separated scheme. If every
point of `Q` has an open neighbourhood `O` on which `φ` extends, in the sense that some
`f : O ⟶ Y` agrees with `φ` on every test scheme mapping to both `O` and `W` compatibly, then
`φ` extends to all of `Q`. -/
theorem C1573.exists_hom_of_local {Q Y : Scheme.{u}} [IsSeparated (terminal.from Y)] (W : Q.Opens)
    (hW : Scheme.Opens.IsSchemeTheoreticallyDense W) (φ : W.toScheme ⟶ Y)
    (hloc : ∀ x : Q, ∃ O : Q.Opens, x ∈ O ∧ ∃ f : O.toScheme ⟶ Y,
      ∀ {T : Scheme.{u}} (a : T ⟶ O.toScheme) (b : T ⟶ W.toScheme), a ≫ O.ι = b ≫ W.ι →
        a ≫ f = b ≫ φ) :
    ∃ f : Q ⟶ Y, W.ι ≫ f = φ := by
  choose O hxO f hf using hloc
  have hcov : IsOpenCover O :=
    IsOpenCover.mk (eq_top_iff.2 fun z _ => Opens.mem_iSup.2 ⟨z, hxO z⟩)
  have key : ∀ x y : Q, pullback.fst (O x).ι (O y).ι ≫ f x =
      pullback.snd (O x).ι (O y).ι ≫ f y := by
    intro x y
    set U : (pullback (O x).ι (O y).ι).Opens :=
      (pullback.fst (O x).ι (O y).ι ≫ (O x).ι) ⁻¹ᵁ W
    have hU : Scheme.Opens.IsSchemeTheoreticallyDense U :=
      AlgebraicGeometry.Scheme.Opens.isSchemeTheoreticallyDense_preimage_of_isOpenImmersion W hW
        (pullback.fst (O x).ι (O y).ι ≫ (O x).ι)
    refine eq_of_isSchemeTheoreticallyDense _ _ U hU ?_
    have hb : (pullback.fst (O x).ι (O y).ι ≫ (O x).ι) ∣_ W ≫ W.ι =
        U.ι ≫ pullback.fst (O x).ι (O y).ι ≫ (O x).ι := morphismRestrict_ι _ _
    rw [← Category.assoc, hf x (U.ι ≫ pullback.fst (O x).ι (O y).ι) _
      (by rw [hb, Category.assoc]), ← Category.assoc,
      hf y (U.ι ≫ pullback.snd (O x).ι (O y).ι) _
      (by rw [hb, Category.assoc, pullback.condition])]
  let g := (Q.openCoverOfIsOpenCover O hcov).glueMorphisms f key
  have hg : ∀ x, (O x).ι ≫ g = f x := fun x =>
    (Q.openCoverOfIsOpenCover O hcov).ι_glueMorphisms f key x
  refine ⟨g, Scheme.hom_ext_of_forall _ _ fun w => ⟨W.ι ⁻¹ᵁ O (W.ι w), hxO (W.ι w), ?_⟩⟩
  have ha := morphismRestrict_ι W.ι (O (W.ι w))
  rw [← Category.assoc, ← ha, Category.assoc, hg]
  exact hf _ _ _ ha

/-- A pair of morphisms into two opens `O` and `W` of `Q` which agree in `Q` factors through
the open `O ⊓ W`. -/
theorem C1573.exists_lift_inf {Q T : Scheme.{u}} (O W : Q.Opens) (a : T ⟶ O.toScheme)
    (b : T ⟶ W.toScheme) (hab : a ≫ O.ι = b ≫ W.ι) :
    ∃ c : T ⟶ (O ⊓ W : Q.Opens).toScheme,
      c ≫ Q.homOfLE inf_le_left = a ∧ c ≫ Q.homOfLE inf_le_right = b := by
  have hr : Set.range (a ≫ O.ι).base ⊆ Set.range (O ⊓ W : Q.Opens).ι.base := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨t, rfl⟩
    refine ⟨(a t).2, ?_⟩
    change (a ≫ O.ι).base t ∈ W
    rw [hab]
    exact (b t).2
  refine ⟨IsOpenImmersion.lift (O ⊓ W : Q.Opens).ι (a ≫ O.ι) hr, ?_, ?_⟩
  · rw [← cancel_mono O.ι, Category.assoc, Scheme.homOfLE_ι, IsOpenImmersion.lift_fac]
  · rw [← cancel_mono W.ι, Category.assoc, Scheme.homOfLE_ι, IsOpenImmersion.lift_fac, hab]

open Stacks.SectionsToProjectiveSpace in
/-- **Extending a morphism to projective space from local regularity of ratios.** Let `W ⊆ Q`
be a scheme-theoretically dense open and let `g₀, …, gₙ` be regular functions on `W` spanning
the unit ideal, so that they define `[g₀ : ⋯ : gₙ] : W ⟶ ℙⁿ`. Suppose every point of `Q` has an
open neighbourhood `O` and an index `i` such that every ratio `gⱼ / gᵢ` is, on `O ⊓ W`, the
restriction of a regular function `rⱼ` on `O`, with `rᵢ = 1`. Then `[g₀ : ⋯ : gₙ]` extends to a
morphism `Q ⟶ ℙⁿ`. -/
theorem C1573.exists_hom_projectiveSpace_of_local {Q : Scheme.{u}} (W : Q.Opens)
    (hW : Scheme.Opens.IsSchemeTheoreticallyDense W) {n : ℕ}
    (g : Fin (n + 1) → Γ(W.toScheme, ⊤)) (hg : Ideal.span (Set.range g) = ⊤)
    (hloc : ∀ x : Q, ∃ O : Q.Opens, x ∈ O ∧ ∃ (i : Fin (n + 1))
      (r : Fin (n + 1) → Γ(O.toScheme, ⊤)), r i = 1 ∧
      ∀ j, (Q.homOfLE (inf_le_left : O ⊓ W ≤ O)).appTop (r j) *
          (Q.homOfLE (inf_le_right : O ⊓ W ≤ W)).appTop (g i) =
        (Q.homOfLE (inf_le_right : O ⊓ W ≤ W)).appTop (g j)) :
    ∃ f : Q ⟶ projectiveSpaceAtUniverse.{u} n, W.ι ≫ f = toProjectiveSpaceAtUniverse g hg := by
  refine exists_hom_of_local W hW _ fun x => ?_
  obtain ⟨O, hxO, i, r, hri, hr⟩ := hloc x
  have hrspan : Ideal.span (Set.range r) = ⊤ :=
    Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨i, rfl⟩) (by simp [hri])
  refine ⟨O, hxO, toProjectiveSpaceAtUniverse r hrspan, fun {T} a b hab => ?_⟩
  obtain ⟨c, hca, hcb⟩ := exists_lift_inf O W a b hab
  have hrT : ∀ j, a.appTop (r j) * b.appTop (g i) = b.appTop (g j) := fun j => by
    simpa only [map_mul, ← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, hca, hcb] using
      congrArg c.appTop.hom (hr j)
  have hgb : Ideal.span (Set.range fun j => b.appTop (g j)) = ⊤ := span_range_comp _ _ hg
  have hra : Ideal.span (Set.range fun j => a.appTop (r j)) = ⊤ := span_range_comp _ _ hrspan
  rw [Stacks.ProjGlobalSectionsAppTop.hasPullbackNaturality a r hrspan hra,
    Stacks.ProjGlobalSectionsAppTop.hasPullbackNaturality b g hg hgb]
  -- the common factor `b^* gᵢ` is a unit
  have hu : IsUnit (b.appTop (g i)) := by
    have hle : Ideal.span (Set.range fun j => b.appTop (g j)) ≤
        Ideal.span {b.appTop (g i)} := by
      rw [Ideal.span_le]
      rintro - ⟨j, rfl⟩
      change b.appTop (g j) ∈ Ideal.span {b.appTop (g i)}
      rw [← hrT j]
      exact Ideal.mem_span_singleton.2 ⟨a.appTop (r j), mul_comm _ _⟩
    rwa [hgb, top_le_iff, Ideal.span_singleton_eq_top] at hle
  have hfun : (fun j => b.appTop (g j)) = fun j => (hu.unit : Γ(T, ⊤)) * a.appTop (r j) := by
    funext j
    rw [IsUnit.unit_spec, mul_comm, hrT j]
  rw [toProjectiveSpaceAtUniverse_congr hfun hgb (by rwa [← hfun])]
  exact (Stacks.ProjGlobalSectionsAppTop.hasUnitInvariance hu.unit _ hra _).symm

/-- Restricting a section along an inclusion of opens commutes with the comparison
`Γ(V, ⊤) ≅ Γ(Q, V)`. -/
theorem C1573.homOfLE_appTop_topIso_inv {Q : Scheme.{u}} {V W : Q.Opens} (h : W ≤ V) (x : Γ(Q, V)) :
    (Q.homOfLE h).appTop (V.topIso.inv x) = W.topIso.inv (Q.presheaf.map (homOfLE h).op x) := by
  rw [← Iso.hom_inv_id_apply W.topIso ((Q.homOfLE h).appTop (V.topIso.inv x))]
  congr 1
  change ((Q.homOfLE h).appTop ≫ W.topIso.hom) (V.topIso.inv x) = _
  have hnat : (Q.homOfLE h).appTop ≫ W.topIso.hom =
      V.topIso.hom ≫ Q.presheaf.map (homOfLE h).op :=
    Scheme.restrictFunctorΓ.hom.naturality (X := op V) (Y := op W) (homOfLE h).op
  rw [hnat, CommRingCat.comp_apply, Iso.inv_hom_id_apply]

open Stacks.SectionsToProjectiveSpace in
/-- `Stacks.ProjectiveExtension.C1573.exists_hom_projectiveSpace_of_local`, with the regular
functions taken as sections of the structure sheaf of `Q` over the opens `W` and `O`. -/
theorem C1573.exists_hom_projectiveSpace_of_local' {Q : Scheme.{u}} (W : Q.Opens)
    (hW : Scheme.Opens.IsSchemeTheoreticallyDense W) {n : ℕ}
    (g : Fin (n + 1) → Γ(Q, W)) (hg : Ideal.span (Set.range fun j => W.topIso.inv (g j)) = ⊤)
    (hloc : ∀ x : Q, ∃ O : Q.Opens, x ∈ O ∧ ∃ (i : Fin (n + 1))
      (r : Fin (n + 1) → Γ(Q, O)), r i = 1 ∧
      ∀ j, Q.presheaf.map (homOfLE (inf_le_left : O ⊓ W ≤ O)).op (r j) *
          Q.presheaf.map (homOfLE (inf_le_right : O ⊓ W ≤ W)).op (g i) =
        Q.presheaf.map (homOfLE (inf_le_right : O ⊓ W ≤ W)).op (g j)) :
    ∃ f : Q ⟶ projectiveSpaceAtUniverse.{u} n,
      W.ι ≫ f = toProjectiveSpaceAtUniverse (fun j => W.topIso.inv (g j)) hg := by
  refine exists_hom_projectiveSpace_of_local W hW _ hg fun x => ?_
  obtain ⟨O, hxO, i, r, hri, hr⟩ := hloc x
  refine ⟨O, hxO, i, fun j => O.topIso.inv (r j), by simp [hri], fun j => ?_⟩
  simp only [homOfLE_appTop_topIso_inv]
  rw [← map_mul, hr j]

/-- The sections of a morphism restricted to a pair of opens, read through the comparisons
`Γ(U, ⊤) ≅ Γ(Y, U)`. -/
theorem C1573.resLE_appTop_topIso_inv {X Y : Scheme.{u}} (f : X ⟶ Y) {U : Y.Opens} {V : X.Opens}
    (e : V ≤ f ⁻¹ᵁ U) (x : Γ(Y, U)) :
    (f.resLE U V e).appTop (U.topIso.inv x) = V.topIso.inv (f.appLE U V e x) := by
  rw [← Iso.hom_inv_id_apply V.topIso ((f.resLE U V e).appTop (U.topIso.inv x))]
  congr 1
  change ((f.resLE U V e).appTop ≫ V.topIso.hom) (U.topIso.inv x) = _
  rw [Scheme.Hom.appTop, Scheme.Hom.resLE_app_top]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id, CommRingCat.comp_apply,
    Iso.inv_hom_id_apply]

/-- The sections of a restricted morphism, read through the comparisons `Γ(U, ⊤) ≅ Γ(Y, U)`. -/
theorem C1573.morphismRestrict_appTop_topIso_inv {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens)
    (x : Γ(Y, U)) :
    (f ∣_ U).appTop (U.topIso.inv x) = (f ⁻¹ᵁ U).topIso.inv (f.app U x) := by
  rw [← Scheme.Hom.resLE_eq_morphismRestrict, resLE_appTop_topIso_inv,
    Scheme.Hom.appLE_eq_app]

end Stacks.ProjectiveExtension

end
