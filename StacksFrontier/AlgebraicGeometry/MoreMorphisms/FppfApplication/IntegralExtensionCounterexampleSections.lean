module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.FppfApplication.IntegralExtensionCounterexampleChase

/-!
# The glued cover is not the base change of an integral morphism

This file completes the refutation of [Stacks, Tag 0CNX] for a general open subscheme by reading
the comparison isomorphisms of
the companion module `IntegralExtensionCounterexampleChase`
on sections.
-/

@[expose] public section

namespace Stacks.IntegralExtensionCounterexample

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits TopologicalSpace
open Stacks.SqZero Stacks.ModuleQuadraticExtension Stacks.TwoChartGluing
open Stacks.OpenBaseChangeCharts

universe u

noncomputable section

/-! ### Two lemmas on away localizations -/

/-- An away localization may be read along a ring isomorphism of the base ring: if `L` is the
localization of `B` away from `e a`, then it is the localization of `A` away from `a`, for the
algebra structure obtained from that of `B` by composing with `e`. -/
lemma isLocalization_away_comp {A B L : Type u} [CommRing A] [CommRing B] [CommRing L]
    [Algebra B L] [Algebra A L] (e : A ≃+* B)
    (he : ∀ y : A, algebraMap A L y = algebraMap B L (e y)) (a : A)
    (hloc : IsLocalization.Away (e a) L) : IsLocalization.Away a L := by
  have := hloc
  refine IsLocalization.Away.mk _ ?_ (fun s => ?_) (fun y z h => ?_)
  · rw [he]
    exact IsLocalization.Away.algebraMap_isUnit (e a)
  · obtain ⟨n, c, hc⟩ := IsLocalization.Away.surj (e a) s
    refine ⟨n, e.symm c, ?_⟩
    simp only [he, e.apply_symm_apply]
    exact hc
  · simp only [he] at h
    obtain ⟨n, hn⟩ := IsLocalization.Away.exists_of_eq (e a) h
    refine ⟨n, e.injective ?_⟩
    rw [map_mul, map_mul, map_pow]
    exact hn

/-- A localization away from an idempotent element is a quotient: the structure map is
surjective, because the image of an idempotent that becomes a unit is `1`. -/
theorem surjective_algebraMap_of_isIdempotentElem {R : Type u} [CommRing R] (s : R)
    (hs : IsIdempotentElem s) (L : Type u) [CommRing L] [Algebra R L]
    [IsLocalization.Away s L] : Function.Surjective (algebraMap R L) := by
  have hunit : IsUnit (algebraMap R L s) := IsLocalization.Away.algebraMap_isUnit s
  have hone : algebraMap R L s = 1 :=
    hunit.mul_left_cancel (by rw [mul_one, ← map_mul, hs])
  intro z
  obtain ⟨k, a, h⟩ := IsLocalization.Away.surj s z
  exact ⟨a, by rw [← h, hone, one_pow, mul_one]⟩

/-! ### Sections over the preimage of an open of the base -/

/-- For a scheme morphism `f : X ⟶ Y`, the structure map of the sections of `X` over `f ⁻¹ᵁ Ω`
is compatible with shrinking `Ω`. -/
lemma ι_appTop_homOfLE {X Y : Scheme.{u}} (f : X ⟶ Y) {Ω Ω' : Y.Opens} (h : Ω' ≤ Ω) :
    (f ⁻¹ᵁ Ω).ι.appTop ≫ (X.homOfLE (preimage_mono f h)).appTop = (f ⁻¹ᵁ Ω').ι.appTop := by
  rw [← Scheme.Hom.comp_appTop, Scheme.homOfLE_ι]

/-- The elementwise form of `Stacks.IntegralExtensionCounterexample.ι_appTop_homOfLE`. -/
lemma ι_appTop_homOfLE_apply {X Y : Scheme.{u}} (f : X ⟶ Y) {Ω Ω' : Y.Opens} (h : Ω' ≤ Ω)
    (z : Γ(X, ⊤)) :
    (X.homOfLE (preimage_mono f h)).appTop ((f ⁻¹ᵁ Ω).ι.appTop z) = (f ⁻¹ᵁ Ω').ι.appTop z := by
  rw [← CommRingCat.comp_apply, ι_appTop_homOfLE f h]

/-- Restriction maps of an open subscheme compose. -/
lemma homOfLE_appTop_apply {X : Scheme.{u}} {U V W : X.Opens} (h₁ : U ≤ V) (h₂ : V ≤ W)
    (z : Γ(W.toScheme, ⊤)) :
    (X.homOfLE h₁).appTop ((X.homOfLE h₂).appTop z) = (X.homOfLE (h₁.trans h₂)).appTop z := by
  rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, Scheme.homOfLE_homOfLE]

/-- The structure map of the sections of an open subscheme is the restriction of global
sections. -/
lemma algebraMap_eq_ι_appTop {X : Scheme.{u}} (U : X.Opens) (z : Γ(X, ⊤)) :
    algebraMap Γ(X, ⊤) Γ(U.toScheme, ⊤) z = U.ι.appTop z := rfl

/-! ### The square-zero extension read on sections -/

/-- The global square-zero extension, read as sections over the part of `Aff` above `Ω`. -/
def gl (Ω : Sch.{u}.Opens) : Ecat.{u} ⟶ Γ((toSch.{u} ⁻¹ᵁ Ω).toScheme, ⊤) :=
  (Scheme.ΓSpecIso Ecat.{u}).inv ≫ (toSch.{u} ⁻¹ᵁ Ω).ι.appTop

/-- `Stacks.IntegralExtensionCounterexample.gl` is compatible with shrinking the open. -/
lemma gl_homOfLE {Ω Ω' : Sch.{u}.Opens} (h : Ω' ≤ Ω) :
    gl.{u} Ω ≫ (Aff.{u}.homOfLE (preimage_mono toSch.{u} h)).appTop = gl.{u} Ω' := by
  rw [gl, gl, Category.assoc, ι_appTop_homOfLE toSch.{u} h]

/-- The elementwise form of `Stacks.IntegralExtensionCounterexample.gl_homOfLE`. -/
lemma gl_homOfLE_apply {Ω Ω' : Sch.{u}.Opens} (h : Ω' ≤ Ω) (z : Sq Base.{u}) :
    (Aff.{u}.homOfLE (preimage_mono toSch.{u} h)).appTop (gl.{u} Ω z) = gl.{u} Ω' z := by
  rw [← CommRingCat.comp_apply, gl_homOfLE h]

/-- A global section of the base ring has the same image in the sections of `Aff` over
`toSch ⁻¹ᵁ Ω` whether it is pushed forward through `toSch` or through the structure map of the
square-zero extension. -/
lemma glSpec (Ω : Sch.{u}.Opens) (t : Base.{u}) :
    (toSch.{u} ⁻¹ᵁ Ω).ι.appTop (toSch.{u}.appTop ((Scheme.ΓSpecIso Rcat.{u}).inv t))
      = gl.{u} Ω (algebraMap Base.{u} (Sq Base.{u}) t) := by
  have hnat : CommRingCat.ofHom (algebraMap Base.{u} (Sq Base.{u}))
        ≫ (Scheme.ΓSpecIso Ecat.{u}).inv
      = (Scheme.ΓSpecIso Rcat.{u}).inv ≫ toSch.{u}.appTop :=
    Scheme.ΓSpecIso_inv_naturality _
  have h1 : toSch.{u}.appTop ((Scheme.ΓSpecIso Rcat.{u}).inv t)
      = (Scheme.ΓSpecIso Ecat.{u}).inv (algebraMap Base.{u} (Sq Base.{u}) t) :=
    (congr($hnat t)).symm
  rw [h1]
  rfl

/-- The twist on sections: the endomorphism induced by `psiRes` is scaling by `(1, 2, 4, …)`. -/
lemma gl_comp_psiRes (Ω : Sch.{u}.Opens) :
    gl.{u} Ω ≫ (psiRes.{u} Ω).appTop
      = CommRingCat.ofHom (scale pows.{u} : Sq Base.{u} →ₐ[Base.{u}] Sq Base.{u}).toRingHom
        ≫ gl.{u} Ω := by
  have hnat : CommRingCat.ofHom (scale pows.{u} : Sq Base.{u} →ₐ[Base.{u}] Sq Base.{u}).toRingHom
        ≫ (Scheme.ΓSpecIso Ecat.{u}).inv
      = (Scheme.ΓSpecIso Ecat.{u}).inv ≫ psi.{u}.appTop :=
    Scheme.ΓSpecIso_inv_naturality _
  rw [gl, Category.assoc, ← Scheme.Hom.comp_appTop, psiRes_ι, Scheme.Hom.comp_appTop,
    ← Category.assoc, ← hnat, Category.assoc]

/-- The elementwise form of `Stacks.IntegralExtensionCounterexample.gl_comp_psiRes`. -/
lemma psiRes_appTop_gl (Ω : Sch.{u}.Opens) (z : Sq Base.{u}) :
    (psiRes.{u} Ω).appTop (gl.{u} Ω z) = gl.{u} Ω (scale pows.{u} z) := by
  rw [← CommRingCat.comp_apply, gl_comp_psiRes, CommRingCat.comp_apply]
  rfl

/-! ### The three localization facts -/

/-- The part of `Aff` above a basic open of the base is the basic open of the image of the
corresponding global section. -/
lemma basicOpen_eq_preimage_D (g : Base.{u}) :
    Aff.{u}.basicOpen ((Scheme.ΓSpecIso Ecat.{u}).inv (algebraMap Base.{u} (Sq Base.{u}) g))
      = toSch.{u} ⁻¹ᵁ D.{u} g :=
  (basicOpen_eq_of_affine _).trans (SpecMap_preimage_basicOpen _ _).symm

/-- **The sections of `Aff` over the part above `D g` are the localization of the square-zero
extension away from the image of `g`.** -/
lemma isLocalization_gl (g : Base.{u}) :
    letI : Algebra (Sq Base.{u}) Γ((toSch.{u} ⁻¹ᵁ D.{u} g).toScheme, ⊤) :=
      (gl.{u} (D.{u} g)).hom.toAlgebra
    IsLocalization.Away (algebraMap Base.{u} (Sq Base.{u}) g)
      Γ((toSch.{u} ⁻¹ᵁ D.{u} g).toScheme, ⊤) := by
  let : Algebra (Sq Base.{u}) Γ((toSch.{u} ⁻¹ᵁ D.{u} g).toScheme, ⊤) :=
    (gl.{u} (D.{u} g)).hom.toAlgebra
  have hloc : IsLocalization.Away
      ((Scheme.ΓSpecIso Ecat.{u}).inv (algebraMap Base.{u} (Sq Base.{u}) g))
      Γ((toSch.{u} ⁻¹ᵁ D.{u} g).toScheme, ⊤) :=
    basicOpen_eq_preimage_D g ▸ AlgebraicGeometry.Γ_restrict_isLocalization Aff.{u} _
  exact isLocalization_away_comp (Scheme.ΓSpecIso Ecat.{u}).symm.commRingCatIsoToRingEquiv
    (fun y => rfl) _ hloc

/-- The `n`-th standard idempotent of the base ring is idempotent. -/
lemma isIdempotentElem_idem (n : ℕ) : IsIdempotentElem (idem.{u} n) := by
  funext m
  show idem.{u} n m * idem.{u} n m = idem.{u} n m
  by_cases h : m = n <;> simp [idem, h]

/-- The image of the `n`-th standard idempotent in the square-zero extension is idempotent. -/
lemma isIdempotentElem_algebraMap_idem (n : ℕ) :
    IsIdempotentElem (algebraMap Base.{u} (Sq Base.{u}) (idem n)) := by
  rw [IsIdempotentElem, ← map_mul, isIdempotentElem_idem n]

/-- **Every section of `Aff` over the part above `De n` comes from the square-zero extension**:
`idem n` is idempotent, so localizing away from it changes nothing. -/
lemma exists_gl_D_idem (n : ℕ) (z : Γ((toSch.{u} ⁻¹ᵁ D.{u} (idem n)).toScheme, ⊤)) :
    ∃ y : Sq Base.{u}, gl.{u} (D.{u} (idem n)) y = z := by
  let : Algebra (Sq Base.{u}) Γ((toSch.{u} ⁻¹ᵁ D.{u} (idem n)).toScheme, ⊤) :=
    (gl.{u} (D.{u} (idem n))).hom.toAlgebra
  have := isLocalization_gl.{u} (idem n)
  exact surjective_algebraMap_of_isIdempotentElem _ (isIdempotentElem_algebraMap_idem n) _ z

/-- The part of a scheme over `Df` is the basic open of the image of `(2, 2, …)`. -/
lemma basicOpen_eq_preimage_Df {A' : Scheme.{u}} (α : A' ⟶ Sch.{u}) :
    A'.basicOpen (α.appTop ((Scheme.ΓSpecIso Rcat.{u}).inv twos.{u})) = α ⁻¹ᵁ Df.{u} := by
  have h : α ⁻¹ᵁ Sch.{u}.basicOpen ((Scheme.ΓSpecIso Rcat.{u}).inv twos.{u})
      = A'.basicOpen (α.appTop ((Scheme.ΓSpecIso Rcat.{u}).inv twos.{u})) :=
    Scheme.preimage_basicOpen α _
  rw [← h, basicOpen_eq_of_affine]
  rfl

/-- **The sections of an affine scheme over the part above `Df` are a localization away from the
image of `(2, 2, …)`.** -/
lemma isLocalization_ex {A' : Scheme.{u}} (α : A' ⟶ Sch.{u}) [IsAffine A'] :
    IsLocalization.Away (α.appTop ((Scheme.ΓSpecIso Rcat.{u}).inv twos.{u}))
      Γ((α ⁻¹ᵁ Df.{u}).toScheme, ⊤) :=
  basicOpen_eq_preimage_Df α ▸ AlgebraicGeometry.Γ_restrict_isLocalization A' _

/-- In the square-zero extension, the generator of the square-zero ideal times `p ^ k` is
`(0, p ^ k)`. -/
lemma mk_zero_one_mul_algebraMap_pow {R : Type u} [CommRing R] (p : R) (k : ℕ) :
    Ext.mk (zeroDatum R) 0 1 * algebraMap R (Sq R) p ^ k = Ext.mk (zeroDatum R) 0 (p ^ k) := by
  rw [algebraMap_pow_eq]
  ext <;> simp

/-! ### The chase -/

/-- An equality of composites of scheme morphisms, read on global sections. -/
private lemma appTop_apply_eq_of_comp_eq {X Y Z W : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    {f' : X ⟶ W} {g' : W ⟶ Z} (h : f ≫ g = f' ≫ g') (z : Γ(Z, ⊤)) :
    f.appTop (g.appTop z) = f'.appTop (g'.appTop z) := by
  rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop,
    ← Scheme.Hom.comp_appTop, h]

section Extension

variable (G : GluedCover.{u}) {A' : Scheme.{u}} {α : A' ⟶ Sch.{u}} {ρ : G.carrier ⟶ A'}
  (hρ : IsPullback ρ G.str α Uo.{u}.ι)

include hρ in
/-- The comparison carries the image of a global section of the base ring to its image in the
square-zero extension. -/
lemma cmp_appTop_gl {Ω : Sch.{u}.Opens} (hΩ : Ω ≤ Uo.{u})
    (κ : (toSch.{u} ⁻¹ᵁ Ω).toScheme ⟶ G.carrier)
    (hκ : IsPullback (toSch.{u} ∣_ Ω) κ Ω.ι (G.str ≫ Uo.{u}.ι)) (t : Base.{u}) :
    (cmp G hρ hΩ κ hκ).hom.appTop
        ((α ⁻¹ᵁ Ω).ι.appTop (α.appTop ((Scheme.ΓSpecIso Rcat.{u}).inv t)))
      = gl.{u} Ω (algebraMap Base.{u} (Sq Base.{u}) t) := by
  rw [← glSpec]
  simpa only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply] using
    appTop_apply_eq_of_comp_eq (cmp_hom_ι G hρ hΩ κ hκ) ((Scheme.ΓSpecIso Rcat.{u}).inv t)

include hρ in
/-- **Step 1 of the chase.** If the glued cover were the base change of `α`, then over `Df` the
generator of the square-zero ideal would be a single global section of `A'` divided by a single
power of `2`. -/
lemma exists_section_div [IsAffine A'] :
    ∃ (N : ℕ) (b : Γ(A', ⊤)),
      gl.{u} Df.{u} (Ext.mk (zeroDatum Base.{u}) 0 (twos.{u} ^ N))
        = (cmp G hρ Df_le_Uo.{u} G.chartDf G.isPullback_Df).hom.appTop
            ((α ⁻¹ᵁ Df.{u}).ι.appTop b) := by
  have := isLocalization_ex α
  obtain ⟨N, b, hb⟩ := IsLocalization.Away.surj
    (α.appTop ((Scheme.ΓSpecIso Rcat.{u}).inv twos.{u}))
    ((cmp G hρ Df_le_Uo.{u} G.chartDf G.isPullback_Df).inv.appTop
      (gl.{u} Df.{u} (Ext.mk (zeroDatum Base.{u}) 0 1)))
  refine ⟨N, b, ?_⟩
  have hid : (cmp G hρ Df_le_Uo.{u} G.chartDf G.isPullback_Df).inv.appTop
      ≫ (cmp G hρ Df_le_Uo.{u} G.chartDf G.isPullback_Df).hom.appTop = 𝟙 _ := by
    rw [← Scheme.Hom.comp_appTop, Iso.hom_inv_id, Scheme.Hom.id_appTop]
  have happ := congrArg
    (fun z => (cmp G hρ Df_le_Uo.{u} G.chartDf G.isPullback_Df).hom.appTop z) hb
  simp only [map_mul, map_pow, algebraMap_eq_ι_appTop, cmp_appTop_gl G hρ] at happ
  rw [← CommRingCat.comp_apply, hid] at happ
  rw [← mk_zero_one_mul_algebraMap_pow, map_mul, map_pow]
  simpa using happ

include hρ in
/-- **Step 2 of the chase.** Restricting the identity of
`Stacks.IntegralExtensionCounterexample.exists_section_div` to the `n`-th overlap. -/
lemma restrict_to_ovl (n N : ℕ) (b : Γ(A', ⊤))
    (h : gl.{u} Df.{u} (Ext.mk (zeroDatum Base.{u}) 0 (twos.{u} ^ N))
        = (cmp G hρ Df_le_Uo.{u} G.chartDf G.isPullback_Df).hom.appTop
            ((α ⁻¹ᵁ Df.{u}).ι.appTop b)) :
    gl.{u} (D.{u} (ovl n)) (Ext.mk (zeroDatum Base.{u}) 0 (twos.{u} ^ N))
      = (cmp G hρ (ovl_le_Uo.{u} n) (G.chartI (GluedCover.ovl_le_inf.{u} n))
          (G.isPullback_chartI (GluedCover.ovl_le_inf.{u} n))).hom.appTop
        ((α ⁻¹ᵁ D.{u} (ovl n)).ι.appTop b) := by
  have h2 := appTop_apply_eq_of_comp_eq (cmp_left G hρ n) ((α ⁻¹ᵁ Df.{u}).ι.appTop b)
  rw [← h, gl_homOfLE_apply (GluedCover.ovl_le_Df.{u} n),
    ι_appTop_homOfLE_apply α (GluedCover.ovl_le_Df.{u} n)] at h2
  exact h2

include hρ in
/-- **Step 4 of the chase.** Over the `n`-th overlap the section produced in step 1 is the twist
of a section coming from the whole of `De n`. -/
lemma exists_scale_eq (n : ℕ) (b : Γ(A', ⊤)) :
    ∃ y : Sq Base.{u},
      gl.{u} (D.{u} (ovl n)) (scale pows.{u} y)
        = (cmp G hρ (ovl_le_Uo.{u} n) (G.chartI (GluedCover.ovl_le_inf.{u} n))
            (G.isPullback_chartI (GluedCover.ovl_le_inf.{u} n))).hom.appTop
          ((α ⁻¹ᵁ D.{u} (ovl n)).ι.appTop b) := by
  have hoe : D.{u} (ovl n) ≤ D.{u} (idem n) := GluedCover.ovl_le_De.{u} n
  have hew : D.{u} (idem n) ≤ Wo.{u} := De_le_Wo.{u} n
  obtain ⟨y, hy⟩ := exists_gl_D_idem.{u} n
    ((Aff.{u}.homOfLE (preimage_mono toSch.{u} hew)).appTop
      ((cmp G hρ Wo_le_Uo.{u} G.chartWo G.isPullback_Wo).hom.appTop
        ((α ⁻¹ᵁ Wo.{u}).ι.appTop b)))
  refine ⟨y, ?_⟩
  have h2 := appTop_apply_eq_of_comp_eq (cmp_right G hρ n) ((α ⁻¹ᵁ Wo.{u}).ι.appTop b)
  simp only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply] at h2
  rw [ι_appTop_homOfLE_apply α (hoe.trans hew),
    ← homOfLE_appTop_apply (preimage_mono toSch.{u} hoe) (preimage_mono toSch.{u} hew),
    ← hy, gl_homOfLE_apply hoe, psiRes_appTop_gl] at h2
  exact h2

end Extension

/-- **The glued cover of the counterexample is not the base change of an integral morphism.**

If the scheme `G.carrier` over the non-retrocompact open `Uo` were the base change along `Uo.ι`
of an integral morphism `α : A' ⟶ Sch`, then over `Df` the generator of the square-zero ideal
would be a global section of `A'` divided by a single power of `2`; but over the `n`-th overlap
the twist multiplies the generator by `2 ^ n`, which forces `n ≤ N` for every `n`. -/
theorem GluedCover.no_extension (G : GluedCover.{u}) {A' : Scheme.{u}} (α : A' ⟶ Sch.{u})
    [IsIntegralHom α] (e : Over.mk G.str ≅ (Over.pullback Uo.{u}.ι).obj (Over.mk α)) : False := by
  have : IsAffine A' := isAffine_of_isAffineHom α
  obtain ⟨ρ, hρ⟩ := isPullback_of_overIso G.str α e
  obtain ⟨N, b, hNb⟩ := exists_section_div G hρ
  obtain ⟨y, hy⟩ := exists_scale_eq G hρ (N + 1) b
  have hkey : gl.{u} (D.{u} (ovl (N + 1))) (Ext.mk (zeroDatum Base.{u}) 0 (twos.{u} ^ N))
      = gl.{u} (D.{u} (ovl (N + 1))) (scale pows.{u} y) :=
    (restrict_to_ovl G hρ (N + 1) N b hNb).trans hy.symm
  let : Algebra (Sq Base.{u}) Γ((toSch.{u} ⁻¹ᵁ D.{u} (ovl (N + 1))).toScheme, ⊤) :=
    (gl.{u} (D.{u} (ovl (N + 1)))).hom.toAlgebra
  have := isLocalization_gl.{u} (ovl (N + 1))
  exact absurd (le_of_eq_scale_pows (n := N + 1) (N := N) _ y hkey) (by omega)

end

end Stacks.IntegralExtensionCounterexample

end
