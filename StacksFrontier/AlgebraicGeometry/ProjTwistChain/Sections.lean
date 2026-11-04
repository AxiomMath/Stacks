module

public import StacksFrontier.AlgebraicGeometry.ProjTwistChain.MY

/-!
# The morphism induced by a graded ring homomorphism, read on the sections of a chart

Let `ψ : 𝒜 →+*ᵍ ℬ` be a graded ring homomorphism, with morphism `mapHom ψ : U(ψ) ⟶ Proj 𝒜` on its
domain of definition. For `f` homogeneous of positive degree, a function on `D₊(f) ⊆ Proj 𝒜`
given by a degree-zero fraction in `f` pulls back along `mapHom ψ` to the function on
`D₊(ψ f) ⊆ Proj ℬ` given by its image under `HomogeneousLocalization.Away.map ψ f`.

## Main results

* `Stacks.AlgebraicGeometry.ProjTwistChain.appLE_awayι_awayToSection`: on the standard open of a
  homogeneous element of positive degree, the open immersion
  `AlgebraicGeometry.Proj.awayι` is the identity on sections, both being the degree-zero
  localization.
* `Stacks.AlgebraicGeometry.ProjTwistChain.appLE_mapAwayHom_awayToSection`: the local morphism
  attached to `f` carries a degree-zero fraction in `f` to its image under
  `HomogeneousLocalization.Away.map ψ f`.
* `Stacks.AlgebraicGeometry.ProjTwistChain.appLE_mapHom_awayToSection`: the same statement for
  a scheme over `Proj ℬ` factoring through the domain of definition.

## References

* [Stacks Project, Tag 01MY](https://stacks.math.columbia.edu/tag/01MY)
-/

@[expose] public noncomputable section

open AlgebraicGeometry HomogeneousLocalization CategoryTheory
open Stacks.AlgebraicGeometry.ProjShared

namespace Stacks.AlgebraicGeometry.ProjTwistChain

universe u w w'

section

variable {A B : Type u} {σ : Type w} {τ : Type w'}
  [CommRing A] [CommRing B] [SetLike σ A] [AddSubgroupClass σ A]
  [SetLike τ B] [AddSubgroupClass τ B]
  (𝒜 : ℕ → σ) (ℬ : ℕ → τ) [GradedRing 𝒜] [GradedRing ℬ]

/-! ### Sections of an open subscheme -/

omit [AddSubgroupClass σ A] [GradedRing 𝒜] [AddSubgroupClass τ B] [GradedRing ℬ] in
/-- The inclusion of an open subscheme identifies the sections over that open with the global
sections of the restriction. -/
public theorem Opens_ι_appLE_top {X : Scheme.{u}} (U : X.Opens)
    (h : (⊤ : U.toScheme.Opens) ≤ U.ι ⁻¹ᵁ U) :
    U.ι.appLE U ⊤ h = U.topIso.inv := by
  rw [Scheme.Opens.ι_appLE]
  rfl

omit [AddSubgroupClass σ A] [GradedRing 𝒜] [AddSubgroupClass τ B] [GradedRing ℬ] in
/-- Equal morphisms have equal maps on sections, whatever the two containments are. -/
public theorem appLE_congr_hom {X Y : Scheme.{u}} {m m' : X ⟶ Y} (hm : m = m') (U : Y.Opens)
    (V : X.Opens) (e : V ≤ m ⁻¹ᵁ U) (e' : V ≤ m' ⁻¹ᵁ U) :
    m.appLE U V e = m'.appLE U V e' := by
  subst hm
  rfl

omit [AddSubgroupClass σ A] [GradedRing 𝒜] [AddSubgroupClass τ B] [GradedRing ℬ] in
/-- Over the whole of both source and target, `appLE` is the map on global sections. -/
public theorem appLE_top_top {X Y : Scheme.{u}} (m : X ⟶ Y)
    (e : (⊤ : X.Opens) ≤ m ⁻¹ᵁ (⊤ : Y.Opens)) : m.appLE ⊤ ⊤ e = m.appTop :=
  m.appLE_eq_app

/-- Two factorizations of the same morphism give the same map on sections. -/
private theorem appLE_comp_apply_eq {X Y Z W : Scheme.{u}} {a : X ⟶ Y} {b : Y ⟶ Z} {c : X ⟶ W}
    {d : W ⟶ Z} (hab : a ≫ b = c ≫ d) {U : Z.Opens} {V : Y.Opens} {V' : W.Opens}
    (hb : V ≤ b ⁻¹ᵁ U) (hd : V' ≤ d ⁻¹ᵁ U) (ha : ⊤ ≤ a ⁻¹ᵁ V) (hc : ⊤ ≤ c ⁻¹ᵁ V')
    (s : Γ(Z, U)) :
    (a.appLE V ⊤ ha).hom ((b.appLE U V hb).hom s) =
      (c.appLE V' ⊤ hc).hom ((d.appLE U V' hd).hom s) := by
  have e := (Scheme.Hom.appLE_comp_appLE a b U V ⊤ hb ha).trans
    ((appLE_congr_hom hab U ⊤ _ _).trans (Scheme.Hom.appLE_comp_appLE c d U V' ⊤ hd hc).symm)
  simpa only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] using
    congrArg (fun m => m.hom s) e

/-! ### Sections along the chart of a standard open -/

variable {𝒜}

/-- The global sections of the chart of a standard open, in terms of `awayToSection`. -/
private theorem basicOpenToSpec_appTop_eq (f : A) :
    (Proj.basicOpenToSpec 𝒜 f).appTop =
      (Scheme.ΓSpecIso (CommRingCat.of (Away 𝒜 f))).hom ≫ Proj.awayToSection 𝒜 f ≫
        (Proj.basicOpen 𝒜 f).topIso.inv :=
  Proj.basicOpenToSpec_app_top 𝒜 f

omit [AddSubgroupClass τ B] [GradedRing ℬ] in
/-- The chart identification of a standard open is injective on global sections: it is an
isomorphism when the element is homogeneous of positive degree. -/
public theorem injective_basicOpenToSpec_appTop {d : ℕ} (hd : 0 < d) {f : A} (hf : f ∈ 𝒜 d) :
    Function.Injective (Proj.basicOpenToSpec 𝒜 f).appTop.hom := by
  have hiso : IsIso (Proj.awayToSection 𝒜 f) := by
    rw [← Proj.basicOpenIsoAway_hom 𝒜 f hf hd]
    infer_instance
  rw [basicOpenToSpec_appTop_eq]
  exact (ConcreteCategory.bijective_of_isIso
    ((Scheme.ΓSpecIso (CommRingCat.of (Away 𝒜 f))).hom ≫ Proj.awayToSection 𝒜 f ≫
      (Proj.basicOpen 𝒜 f).topIso.inv)).1

omit [AddSubgroupClass τ B] [GradedRing ℬ] in
/-- The chart `Spec A_{(f)} ⟶ Proj 𝒜` is the identity on sections: a degree-zero fraction in `f`,
read as a function on `D₊(f)`, pulls back to itself under the standard open immersion. -/
public theorem appLE_awayι_awayToSection {d : ℕ} (hd : 0 < d) {f : A} (hf : f ∈ 𝒜 d)
    (h : (⊤ : (Spec (CommRingCat.of (Away 𝒜 f))).Opens) ≤
      Proj.awayι 𝒜 f hf hd ⁻¹ᵁ Proj.basicOpen 𝒜 f) (x : Away 𝒜 f) :
    ((Proj.awayι 𝒜 f hf hd).appLE (Proj.basicOpen 𝒜 f) ⊤ h).hom
        ((Proj.awayToSection 𝒜 f).hom x) =
      (Scheme.ΓSpecIso (CommRingCat.of (Away 𝒜 f))).inv.hom x := by
  refine injective_basicOpenToSpec_appTop hd hf ?_
  have hcomp : Proj.basicOpenToSpec 𝒜 f ≫ Proj.awayι 𝒜 f hf hd = (Proj.basicOpen 𝒜 f).ι := by
    rw [Proj.awayι, ← Proj.basicOpenIsoSpec_hom 𝒜 f hf hd, Iso.hom_inv_id_assoc]
  have hsplit := Scheme.Hom.appLE_comp_appLE (Proj.basicOpenToSpec 𝒜 f)
    (Proj.awayι 𝒜 f hf hd) (Proj.basicOpen 𝒜 f) ⊤ ⊤ h le_top
  rw [appLE_top_top (Proj.basicOpenToSpec 𝒜 f) le_top] at hsplit
  have hpre : Proj.awayι 𝒜 f hf hd ⁻¹ᵁ Proj.basicOpen 𝒜 f = ⊤ := top_le_iff.mp h
  have hι := (appLE_congr_hom hcomp (Proj.basicOpen 𝒜 f) ⊤
    (by rw [Scheme.Hom.comp_preimage, hpre]; simp)
    (Proj.basicOpen 𝒜 f).ι_preimage_self.ge).trans (Opens_ι_appLE_top _ _)
  have hval := congrArg (fun m : Γ(Proj 𝒜, Proj.basicOpen 𝒜 f) ⟶
      Γ((Proj.basicOpen 𝒜 f).toScheme, ⊤) => m.hom ((Proj.awayToSection 𝒜 f).hom x))
    (hsplit.trans hι)
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] at hval
  refine hval.trans ?_
  rw [basicOpenToSpec_appTop_eq]
  simp
  rfl

/-! ### Sections along the local morphism of a graded ring homomorphism -/

variable (𝒜)

/-- The local morphism of `ψ` on `D₊(ψ f)` carries a degree-zero fraction in `f` to its image
under `HomogeneousLocalization.Away.map ψ f`. -/
public theorem appLE_mapAwayHom_awayToSection (ψ : 𝒜 →+*ᵍ ℬ) {d : ℕ} (hd : 0 < d) {f : A}
    (hf : f ∈ 𝒜 d)
    (h : (⊤ : (Proj.basicOpen ℬ (ψ f)).toScheme.Opens) ≤
      mapAwayHom 𝒜 ℬ ψ hd hf ⁻¹ᵁ Proj.basicOpen 𝒜 f)
    (h' : (⊤ : (Proj.basicOpen ℬ (ψ f)).toScheme.Opens) ≤
      (Proj.basicOpen ℬ (ψ f)).ι ⁻¹ᵁ Proj.basicOpen ℬ (ψ f))
    (x : Away 𝒜 f) :
    ((mapAwayHom 𝒜 ℬ ψ hd hf).appLE (Proj.basicOpen 𝒜 f) ⊤ h).hom
        ((Proj.awayToSection 𝒜 f).hom x) =
      ((Proj.basicOpen ℬ (ψ f)).ι.appLE (Proj.basicOpen ℬ (ψ f)) ⊤ h').hom
        ((Proj.awayToSection ℬ (ψ f)).hom (Away.map ψ f x)) := by
  have hawayι : Proj.awayι 𝒜 f hf hd ⁻¹ᵁ Proj.basicOpen 𝒜 f = ⊤ := by
    rw [← Proj.opensRange_awayι 𝒜 f hf hd, Scheme.Hom.preimage_opensRange]
  have h2 : Scheme.Hom.appLE
      (Spec.map (CommRingCat.ofHom (Away.map ψ f)) ≫ Proj.awayι 𝒜 f hf hd)
        (Proj.basicOpen 𝒜 f) ⊤ (by rw [Scheme.Hom.comp_preimage, hawayι]; simp) =
      (Proj.awayι 𝒜 f hf hd).appLE (Proj.basicOpen 𝒜 f) ⊤ hawayι.ge ≫
        (Spec.map (CommRingCat.ofHom (Away.map ψ f))).appTop := by
    rw [← appLE_top_top (Spec.map (CommRingCat.ofHom (Away.map ψ f))) le_top]
    exact (Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _).symm
  have h1 : (mapAwayHom 𝒜 ℬ ψ hd hf).appLE (Proj.basicOpen 𝒜 f) ⊤ h =
      Scheme.Hom.appLE (Spec.map (CommRingCat.ofHom (Away.map ψ f)) ≫
          Proj.awayι 𝒜 f hf hd) (Proj.basicOpen 𝒜 f) ⊤
          (by rw [Scheme.Hom.comp_preimage, hawayι]; simp) ≫
        (Proj.basicOpenToSpec ℬ (ψ f)).appTop := by
    rw [← appLE_top_top (Proj.basicOpenToSpec ℬ (ψ f)) le_top]
    exact (Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _).symm
  rw [h1]
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply]
  rw [h2]
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply]
  rw [appLE_awayι_awayToSection hd hf hawayι.ge x]
  have hnat := congrArg (fun m : CommRingCat.of (Away 𝒜 f) ⟶
      Γ(Spec (CommRingCat.of (Away ℬ (ψ f))), ⊤) => m.hom x)
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (Away.map ψ f)))
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply,
    CommRingCat.hom_ofHom] at hnat
  rw [← hnat, Opens_ι_appLE_top (Proj.basicOpen ℬ (ψ f)) h', basicOpenToSpec_appTop_eq]
  simp
  rfl

/-- Let `Z` be a scheme mapping into `Proj ℬ` through the domain of definition of `ψ`. Then on the
chart `Z ∩ D₊(ψ f)` the morphism `Z ⟶ Proj 𝒜` induced by `ψ` carries a degree-zero fraction in
`f`, read as a function on `D₊(f)`, to the restriction along `Z ⟶ Proj ℬ` of its image under
`HomogeneousLocalization.Away.map ψ f`. -/
public theorem appLE_mapHom_awayToSection (ψ : 𝒜 →+*ᵍ ℬ) {d : ℕ} (hd : 0 < d) {f : A}
    (hf : f ∈ 𝒜 d) {Z : Scheme.{u}} {i : Z ⟶ Proj ℬ} {q : Z ⟶ Proj 𝒜}
    (p : Z ⟶ (mapDomain 𝒜 ℬ ψ).toScheme) (hp : p ≫ (mapDomain 𝒜 ℬ ψ).ι = i)
    (hq : q = p ≫ mapHom 𝒜 ℬ ψ)
    (h : i ⁻¹ᵁ Proj.basicOpen ℬ (ψ f) ≤ q ⁻¹ᵁ Proj.basicOpen 𝒜 f)
    (x : Away 𝒜 f) :
    (q.appLE (Proj.basicOpen 𝒜 f)
          (i ⁻¹ᵁ Proj.basicOpen ℬ (ψ f)) h).hom ((Proj.awayToSection 𝒜 f).hom x) =
      (i.appLE (Proj.basicOpen ℬ (ψ f)) (i ⁻¹ᵁ Proj.basicOpen ℬ (ψ f)) le_rfl).hom
        ((Proj.awayToSection ℬ (ψ f)).hom (Away.map ψ f x)) := by
  subst hq
  set D : (Proj ℬ).Opens := Proj.basicOpen ℬ (ψ f) with hD
  set V : Z.Opens := i ⁻¹ᵁ D with hV
  set ρ : V.toScheme ⟶ D.toScheme := i.resLE D V le_rfl with hρ
  set g : D.toScheme ⟶ (mapDomain 𝒜 ℬ ψ).toScheme :=
    (Proj ℬ).homOfLE (basicOpen_le_mapDomain 𝒜 ℬ ψ hd hf) with hg
  have hfac : V.ι ≫ p = ρ ≫ g := by
    rw [← cancel_mono (mapDomain 𝒜 ℬ ψ).ι, Category.assoc, Category.assoc, hp, hg,
      Scheme.homOfLE_ι, hρ, Scheme.Hom.resLE_comp_ι]
  refine (ConcreteCategory.bijective_of_isIso (V.ι.appLE V ⊤ V.ι_preimage_self.ge)).1 ?_
  have hmapaway : g ≫ mapHom 𝒜 ℬ ψ = mapAwayHom 𝒜 ℬ ψ hd hf := homOfLE_mapHom 𝒜 ℬ ψ hd hf
  have hV1 : V.ι ≫ p ≫ mapHom 𝒜 ℬ ψ = ρ ≫ mapAwayHom 𝒜 ℬ ψ hd hf := by
    rw [← Category.assoc, hfac, Category.assoc, hmapaway]
  have hV2 : V.ι ≫ i = ρ ≫ D.ι := (Scheme.Hom.resLE_comp_ι i le_rfl).symm
  have hawayD : mapAwayHom 𝒜 ℬ ψ hd hf ⁻¹ᵁ Proj.basicOpen 𝒜 f = ⊤ := by
    rw [mapAwayHom_preimage_basicOpen 𝒜 ℬ ψ hd hf hd hf, Scheme.Opens.ι_preimage_self]
  have hL := appLE_comp_apply_eq (a := V.ι) (b := p ≫ mapHom 𝒜 ℬ ψ) (c := ρ)
    (d := mapAwayHom 𝒜 ℬ ψ hd hf) (U := Proj.basicOpen 𝒜 f) (V := V) (V' := ⊤) hV1 h
    hawayD.ge V.ι_preimage_self.ge le_top ((Proj.awayToSection 𝒜 f).hom x)
  have hR := appLE_comp_apply_eq (a := V.ι) (b := i) (c := ρ) (d := D.ι) (U := D) (V := V)
    (V' := ⊤) hV2 le_rfl D.ι_preimage_self.ge V.ι_preimage_self.ge le_top
    ((Proj.awayToSection ℬ (ψ f)).hom (Away.map ψ f x))
  rw [hL, hR]
  exact congrArg (ρ.appLE ⊤ ⊤ le_top).hom
    (appLE_mapAwayHom_awayToSection 𝒜 ℬ ψ hd hf hawayD.ge D.ι_preimage_self.ge x)

end

end Stacks.AlgebraicGeometry.ProjTwistChain

end
