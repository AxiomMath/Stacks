module

public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.CategoryTheory.Limits.Shapes.Biproducts
public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import StacksFrontier.AlgebraicGeometry.Morphisms.Closure.DenseOpenImmersion
public import StacksFrontier.AlgebraicGeometry.Morphisms.Closure.SchemeTheoreticallyDense
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.SectionIdealSumCapture
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Pulling back a scheme-theoretically dense open along a quasi-finite flat morphism

The inverse image of a scheme-theoretically dense open subscheme under a morphism which is
flat, locally of finite presentation and locally quasi-finite is again scheme-theoretically
dense.

## Main results

* `AlgebraicGeometry.isSchemeTheoreticallyDense_preimage`: scheme-theoretic density of an open
  subscheme is inherited by its inverse image along a flat, locally finitely presented and
  locally quasi-finite morphism.

## Implementation notes

Scheme-theoretic density of `f ⁻¹ᵁ W` in `X` is the vanishing of the kernel ideal sheaf of the
inclusion of `V ∩ f ⁻¹ W` for every open `V ⊆ X`, and such a vanishing may be tested on an
affine cover of `V`. On an affine open `A ⊆ V` the relevant map of sections is the one attached
to the composite `A ⟶ V ⟶ X ⟶ S`, so the whole statement reduces to the injectivity of
`(j ⁻¹ᵁ W).ι.appTop` for a single morphism `j` with the three stated properties.

That injectivity is where the hypotheses on `f` enter. A global function on `j ⁻¹ᵁ W` killed by
the restriction is exhibited as a section of a finite direct sum of copies of a quasi-coherent
ideal sheaf on an open of the base, by
`AlgebraicGeometry.exists_open_injective_ideal_sum_with_section`. Density of `W` makes
restriction to the dense open injective on such an ideal sheaf, so the section dies there, and
the projections of a biproduct recover the section from its components.

## References

* [Stacks Project, Tag 0832](https://stacks.math.columbia.edu/tag/0832)
-/

@[expose] public section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry

section ProofLemmas

/-- The map on global sections induced by the inclusion of an open subscheme `D ⊆ Y` factors as
the restriction `Γ(Y, ⊤) ⟶ Γ(Y, D)` followed by the comparison map `Γ(Y, D) ⟶ Γ(D, ⊤)`. -/
private lemma inclusion_appTop_eq_restr_appLE {Y : Scheme.{u}} (D : Y.Opens) :
    D.ι.appTop = Y.presheaf.map (homOfLE (le_top : D ≤ ⊤)).op ≫
      D.ι.appLE D ⊤ D.ι_preimage_self.ge := by
  have htop : D.ι.appLE ⊤ ⊤ (by simp) = D.ι.appTop := by
    simpa [Scheme.Hom.appTop] using (Scheme.Hom.appLE_eq_app (f := D.ι) (U := ⊤))
  exact htop.symm.trans (Scheme.Hom.map_appLE (f := D.ι) D.ι_preimage_self.ge
    (homOfLE (le_top : D ≤ ⊤)).op).symm

/-- Restriction to a scheme-theoretically dense open `D ⊆ Y` is injective on the global
sections of a submodule of the structure sheaf of `Y`. -/
private lemma dense_submodule_restriction_injective {Y : Scheme.{u}} (D : Y.Opens)
    (hD : Scheme.Opens.IsSchemeTheoreticallyDense D)
    (F : (SheafOfModules.unit Y.ringCatSheaf).Submodule) :
    Function.Injective
      ((F.toSheafOfModules).val.map (homOfLE (le_top : D ≤ ⊤)).op).hom := by
  let i : Opposite.op ⊤ ⟶ Opposite.op D := (homOfLE (le_top : D ≤ ⊤)).op
  have hm := (isSchemeTheoreticallyDense_opensRange_iff_mono D.ι).mp
    (by simpa [Scheme.Opens.opensRange_ι] using hD)
  have hinjD := (ConcreteCategory.mono_iff_injective_of_preservesPullback _).mp
    ((CategoryTheory.NatTrans.mono_iff_mono_app _).mp hm (Opposite.op ⊤))
  have hinjQ : Function.Injective (D.ι.appTop).hom := hinjD
  have hinjF : Function.Injective (Scheme.Modules.Hom.app F.ι ⊤).hom :=
    fun _ _ hxy => Subtype.ext hxy
  intro x y hxy
  apply hinjF
  apply hinjQ
  rw [inclusion_appTop_eq_restr_appLE]
  have hv := congrArg (fun z => z.val) hxy
  change ((F.toSubmodule.toPresheafOfModules.map i) x).val =
    ((F.toSubmodule.toPresheafOfModules.map i) y).val at hv
  rw [PresheafOfModules.Submodule.toPresheafOfModules_map_apply
    (N := F.toSubmodule) i x] at hv
  exact congrArg (ConcreteCategory.hom (D.ι.appLE D ⊤ D.ι_preimage_self.ge)) hv

/-- Sheaves of modules on a scheme form an additive category with finite products, hence have
finite biproducts. -/
private instance hasFiniteBiproducts_modules (Y : Scheme.{u}) :
    HasFiniteBiproducts Y.Modules := HasFiniteBiproducts.of_hasFiniteProducts

/-- A monomorphism of sheaves of modules is injective on the sections over every open. -/
private lemma mono_modules_app_injective {Y : Scheme.{u}} {M N : Y.Modules}
    (φ : M ⟶ N) (hφ : Mono φ) (U : Y.Opens) :
    Function.Injective (Scheme.Modules.Hom.app φ U).hom := by
  have hm := Functor.map_mono (Scheme.Modules.toPresheaf Y) φ
  exact (ConcreteCategory.mono_iff_injective_of_preservesPullback _).mp
    ((CategoryTheory.NatTrans.mono_iff_mono_app _).mp hm (Opposite.op U))

/-- A morphism of sheaves of modules commutes with restriction from the whole space to an
open subscheme. -/
private lemma modules_hom_restriction_natural {Y : Scheme.{u}} {M N : Y.Modules}
    (φ : M ⟶ N) (D : Y.Opens) (x : Γ(M, ⊤)) :
    (((Scheme.Modules.toPresheaf Y).map φ).app (Opposite.op D)).hom
        ((((Scheme.Modules.toPresheaf Y).obj M).map
          (homOfLE (le_top : D ≤ ⊤)).op).hom x) =
      ((((Scheme.Modules.toPresheaf Y).obj N).map
        (homOfLE (le_top : D ≤ ⊤)).op).hom
          ((((Scheme.Modules.toPresheaf Y).map φ).app (Opposite.op ⊤)).hom x)) := by
  have hn := (Scheme.Modules.toPresheaf Y).map φ |>.naturality_apply
    (homOfLE (le_top : D ≤ ⊤)).op x
  simpa only [ConcreteCategory.comp_apply] using hn

/-- A section of a finite coproduct of copies of a sheaf of modules vanishes as soon as all of
its biproduct components do. -/
private lemma coproduct_section_eq_zero_of_projection_eq_zero {Y : Scheme.{u}}
    {M : Y.Modules} {r : ℕ} (D : Y.Opens) (t : Γ((∐ fun _ : Fin r => M), D))
    (h : ∀ j : Fin r,
      (biproduct.π (fun _ : Fin r => M) j).app D
        ((biproduct.isoCoproduct (fun _ : Fin r => M)).inv.app D t) = 0) :
    t = 0 := by
  let P := ⨁ fun _ : Fin r => M
  let e := biproduct.isoCoproduct (fun _ : Fin r => M)
  let x := e.inv.app D t
  let q : Fin r → (P ⟶ P) := fun j =>
    biproduct.π (fun _ : Fin r => M) j ≫ biproduct.ι (fun _ : Fin r => M) j
  have heval (s : Finset (Fin r)) :
      (Scheme.Modules.Hom.app (∑ j ∈ s, q j) D) x =
        ∑ j ∈ s, (Scheme.Modules.Hom.app (q j) D) x := by
    classical
    induction s using Finset.induction_on with
    | empty => simp
    | @insert j s hj hs => simp [Finset.sum_insert, hj, Scheme.Modules.Hom.add_app, hs]
  have hproj : ∀ j : Fin r,
      (Scheme.Modules.Hom.app (biproduct.π (fun _ : Fin r => M) j) D) x = 0 := fun j => by
    simpa [x, e] using h j
  have hzero : ∀ j : Fin r, (Scheme.Modules.Hom.app (q j) D) x = 0 := fun j => by
    simp [q, Scheme.Modules.Hom.comp_app, hproj j]
  have hx : x = 0 :=
    calc
      x = (Scheme.Modules.Hom.app (𝟙 P) D) x := by simp
      _ = (Scheme.Modules.Hom.app (∑ j : Fin r, q j) D) x := by
        rw [← biproduct.total]
      _ = ∑ j : Fin r, (Scheme.Modules.Hom.app (q j) D) x := heval Finset.univ
      _ = 0 := by simp [hzero]
  have ht : e.hom.app D x = t := by
    change (Scheme.Modules.Hom.app (e.inv ≫ e.hom) D) t = t
    rw [e.inv_hom_id]
    simp
  rw [← ht, hx]
  simp

/-- A global section of a finite coproduct of copies of a sheaf of modules `M` vanishes as soon
as it restricts to zero on an open over which restriction is injective on `M`. -/
private lemma coproduct_section_eq_zero_of_restriction_injective {Y : Scheme.{u}}
    {M : Y.Modules} {r : ℕ} (D : Y.Opens)
    (hD : Function.Injective ((((Scheme.Modules.toPresheaf Y).obj M).map
      (homOfLE (le_top : D ≤ ⊤)).op).hom))
    (t : Γ((∐ fun _ : Fin r => M), ⊤))
    (htD : ((((Scheme.Modules.toPresheaf Y).obj (∐ fun _ : Fin r => M)).map
      (homOfLE (le_top : D ≤ ⊤)).op).hom t) = 0) : t = 0 := by
  let e := biproduct.isoCoproduct (fun _ : Fin r => M)
  have hproj : ∀ k : Fin r,
      (biproduct.π (fun _ : Fin r => M) k).app ⊤ (e.inv.app ⊤ t) = 0 := by
    intro k
    let π := biproduct.π (fun _ : Fin r => M) k
    have hzero : (((Scheme.Modules.toPresheaf Y).map (e.inv ≫ π)).app
        (Opposite.op ⊤)).hom t = 0 := by
      apply hD
      simpa only [htD, map_zero] using
        (modules_hom_restriction_natural (e.inv ≫ π) D t).symm
    exact hzero
  exact coproduct_section_eq_zero_of_projection_eq_zero ⊤ t fun k => by
    simpa [e] using hproj k

/-- Scheme-theoretic density is inherited by the inverse image along the inclusion of an open
subscheme. -/
private lemma dense_open_restriction {S : Scheme.{u}} (W : S.Opens)
    (hW : Scheme.Opens.IsSchemeTheoreticallyDense W) (U : S.Opens) :
    Scheme.Opens.IsSchemeTheoreticallyDense (U.ι ⁻¹ᵁ W) := by
  intro V
  let O : S.Opens := U.ι ''ᵁ V
  let R : O.toScheme.Opens := O.ι ⁻¹ᵁ W
  let e : V.toScheme ≅ O.toScheme := U.ι.isoImage V
  let E : V.toScheme.Opens := e.hom ⁻¹ᵁ R
  have he : e.hom ≫ O.ι = V.ι ≫ U.ι := by
    simpa only [e, O] using Scheme.Hom.isoImage_hom_ι U.ι V
  have hE : E = V.ι ⁻¹ᵁ (U.ι ⁻¹ᵁ W) := by
    dsimp [E, R, O]
    rw [← Scheme.Hom.comp_preimage, he, Scheme.Hom.comp_preimage]
  have hdomR : IsSchemeTheoreticallyDominant R.ι := by
    simpa [R, O] using hW O
  let q : E.toScheme ⟶ R.toScheme := e.hom.resLE R E (by rfl)
  have hImage : e.hom ''ᵁ E = R := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf]
    simp [R, Scheme.Hom.opensRange_of_isIso]
  have hqcomp : q ≫ R.ι = E.ι ≫ e.hom := Scheme.Hom.resLE_comp_ι e.hom (by rfl)
  have : IsOpenImmersion q := by
    rw [show q = e.hom ∣_ R by
      dsimp [q]
      rw [Scheme.Hom.resLE_eq_morphismRestrict]]
    infer_instance
  have hqrange : q.opensRange = ⊤ := by
    apply R.ι.image_injective
    calc
      R.ι ''ᵁ q.opensRange = (q ≫ R.ι).opensRange := by
        rw [Scheme.Hom.opensRange_comp]
      _ = (E.ι ≫ e.hom).opensRange := by simp only [hqcomp]
      _ = e.hom ''ᵁ E := by
        rw [Scheme.Hom.opensRange_comp]
        simp
      _ = R.ι ''ᵁ ⊤ := by rw [hImage]; simp
  have : IsIso q := isIso_of_isOpenImmersion_of_opensRange_eq_top q hqrange
  have hdomE : IsSchemeTheoreticallyDominant E.ι := by
    rw [show E.ι = q ≫ R.ι ≫ e.inv by rw [← Category.assoc, hqcomp]; simp]
    infer_instance
  exact hE ▸ hdomE

/-- For `j` flat, locally of finite presentation and locally quasi-finite and `W` a
scheme-theoretically dense open of the target, restriction of global functions along the
inclusion of `j ⁻¹ᵁ W` is injective. -/
private lemma preimage_appTop_injective {Z S : Scheme.{u}}
    (j : Z ⟶ S) [Flat j] [LocallyOfFinitePresentation j] [LocallyQuasiFinite j]
    {W : S.Opens} (hW : Scheme.Opens.IsSchemeTheoreticallyDense W) :
    Function.Injective (((j ⁻¹ᵁ W).ι.appTop).hom) := by
  let P : Z.Opens := j ⁻¹ᵁ W
  intro a b hab
  have hab' : (P.ι.appTop).hom a = (P.ι.appTop).hom b := hab
  have hvan : (P.ι.appTop).hom (a - b) = 0 := by
    rw [map_sub, hab', sub_self]
  by_contra hne
  have hg : a - b ≠ 0 := sub_ne_zero.mpr hne
  obtain ⟨U, V, hVU, F, _, r, _, φ, hφ, t, ht, hnz⟩ :=
    exists_open_injective_ideal_sum_with_section j (a - b) hg
  have hD : Scheme.Opens.IsSchemeTheoreticallyDense (U.ι ⁻¹ᵁ W) :=
    dense_open_restriction W hW U
  let π : V.toScheme ⟶ U.toScheme := j.resLE U V hVU
  let D : U.toScheme.Opens := U.ι ⁻¹ᵁ W
  let K : V.toScheme.Opens := π ⁻¹ᵁ D
  have hK : K = V.ι ⁻¹ᵁ P := by
    dsimp [K, P, D, π]
    rw [← Scheme.Hom.comp_preimage, Scheme.Hom.resLE_comp_ι, Scheme.Hom.comp_preimage]
  have hle : K ≤ V.ι ⁻¹ᵁ P := hK.le
  let q : K.toScheme ⟶ P.toScheme := V.ι.resLE P K hle
  have hqcomp : q ≫ P.ι = K.ι ≫ V.ι :=
    Scheme.Hom.resLE_comp_ι V.ι hle
  have hVzero : (K.ι.appTop).hom ((V.ι.appTop).hom (a - b)) = 0 := by
    have hcomp := congrArg Scheme.Hom.appTop hqcomp
    rw [Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop] at hcomp
    have hcomp' : (q.appTop).hom ((P.ι.appTop).hom (a - b)) =
        (K.ι.appTop).hom ((V.ι.appTop).hom (a - b)) :=
      congrArg (fun k => k.hom (a - b)) hcomp
    rw [← hcomp']
    simpa using congrArg (fun x => (q.appTop).hom x) hvan
  let iD : Opposite.op ⊤ ⟶ Opposite.op D := (homOfLE (le_top : D ≤ ⊤)).op
  let M := ∐ fun _ : Fin r => F.toSheafOfModules
  let tD := (((Scheme.Modules.toPresheaf U.toScheme).obj M).map iD).hom t
  have htarget :
      ((((Scheme.Modules.toPresheaf U.toScheme).obj
        ((Scheme.Modules.pushforward π).obj (SheafOfModules.unit _))).map iD).hom
        ((V.ι.appTop).hom (a - b))) = 0 := by
    change ((((Scheme.Modules.pushforward π).obj (SheafOfModules.unit _)).presheaf.map
      (homOfLE (le_top : D ≤ ⊤)).op).hom
      ((V.ι.appTop).hom (a - b))) = 0
    rw [Scheme.Modules.pushforward_obj_presheaf_map (f := π)
      (M := SheafOfModules.unit V.toScheme.ringCatSheaf)
      (i := homOfLE (le_top : D ≤ ⊤))]
    have hmap :
        (TopologicalSpace.Opens.map π.base).map (homOfLE (le_top : D ≤ ⊤)) =
          homOfLE (le_top : K ≤ ⊤) := by
      apply Subsingleton.elim
    rw [hmap]
    change (V.toScheme.presheaf.map (homOfLE (le_top : K ≤ ⊤)).op).hom
      ((V.ι.appTop).hom (a - b)) = 0
    have hleTop : ⊤ ≤ K.ι ⁻¹ᵁ K := K.ι_preimage_self.ge
    have hLEiso : IsIso (K.ι.appLE K ⊤ hleTop) := by
      have : IsIso (K.ι.app K) := by
        apply Scheme.Hom.isIso_app K.ι K
        rw [Scheme.Opens.opensRange_ι]
      have : IsIso (homOfLE hleTop) :=
        ⟨homOfLE le_top, Subsingleton.elim _ _, Subsingleton.elim _ _⟩
      change IsIso (K.ι.app K ≫ K.toScheme.presheaf.map (homOfLE hleTop).op)
      infer_instance
    have hLEzero : (K.ι.appLE K ⊤ hleTop).hom
        ((V.toScheme.presheaf.map (homOfLE (le_top : K ≤ ⊤)).op).hom
          ((V.ι.appTop).hom (a - b))) = 0 := by
      rw [← ConcreteCategory.comp_apply,
        ← inclusion_appTop_eq_restr_appLE K]
      exact hVzero
    have hinj : Function.Injective (K.ι.appLE K ⊤ hleTop).hom :=
      (ConcreteCategory.bijective_of_isIso (K.ι.appLE K ⊤ hleTop)).1
    apply hinj
    simpa using hLEzero
  have ht' : ((((Scheme.Modules.toPresheaf U.toScheme).map φ).app
      (Opposite.op ⊤)).hom t) = (V.ι.appTop).hom (a - b) := ht
  have hφD : (Scheme.Modules.Hom.app φ D) tD = 0 := by
    change ((((Scheme.Modules.toPresheaf U.toScheme).map φ).app (Opposite.op D)).hom
      ((((Scheme.Modules.toPresheaf U.toScheme).obj M).map iD).hom t)) = 0
    rw [modules_hom_restriction_natural φ D t, ht']
    exact htarget
  have htD : tD = 0 := by
    have hmap : (Scheme.Modules.Hom.app φ D).hom tD =
        (Scheme.Modules.Hom.app φ D).hom 0 := by
      rw [hφD]
      simp
    exact mono_modules_app_injective φ hφ D hmap
  have htzero : t = 0 := coproduct_section_eq_zero_of_restriction_injective
    (M := F.toSheafOfModules) D (dense_submodule_restriction_injective D hD F) t htD
  exact hnz (ht.symm.trans (by rw [htzero]; exact map_zero _))

end ProofLemmas

/-- **Stacks 0832.** The inverse image of a scheme-theoretically dense open subscheme under a
morphism of schemes which is flat, locally of finite presentation and locally quasi-finite is
scheme-theoretically dense. -/
@[stacks 0832, ega "IV 20.5.7" "special case"]
public theorem isSchemeTheoreticallyDense_preimage {X S : Scheme.{u}} (f : X ⟶ S)
    [Flat f] [LocallyOfFinitePresentation f] [LocallyQuasiFinite f]
    {W : S.Opens} (hW : Scheme.Opens.IsSchemeTheoreticallyDense W) :
    Scheme.Opens.IsSchemeTheoreticallyDense (f ⁻¹ᵁ W) := by
  intro V
  let J : V.toScheme.Opens := V.ι ⁻¹ᵁ (f ⁻¹ᵁ W)
  apply (isSchemeTheoreticallyDominant_iff J.ι).2
  apply ker_eq_bot_of_app_injective_affine J.ι
  intro A
  let A' : V.toScheme.Opens := A.1
  have : IsAffine A'.toScheme := A.2
  have hEq : A'.ι ⁻¹ᵁ J = (A'.ι ≫ V.ι ≫ f) ⁻¹ᵁ W := by
    simp [J]
  rw [app_injective_iff_appTop_inter J A', hEq]
  exact preimage_appTop_injective (A'.ι ≫ V.ι ≫ f) hW

end AlgebraicGeometry
