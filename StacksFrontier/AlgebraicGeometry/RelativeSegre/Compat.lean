module

public import StacksFrontier.AlgebraicGeometry.RelativeSegre.Cover

/-!
# The Segre morphisms of two affine pieces agree on their overlap

Let `H` and `G` be quasi-coherent modules on a scheme `X`. On an affine piece
`D₊(a) ×_U D₊(b)` of `𝐏(H) ×_X 𝐏(G)` the Segre morphism to `𝐏(H ⊗ G)` is the morphism of the ring
map `h ⊗ g ↦ (h/a) ⊗ (g/b)`. On the overlap with a second piece `D₊(a') ×_U D₊(b')` over the same
affine open the two ring maps differ, in degree `n`, by the `n`-th power of the unit
`(a/a') (b/b')`, so they define the same morphism to `Proj`.

## Main results

* `Stacks.RelativeSegre.ringHom_ext_sectionRing`: a ring map out of `Γ(U, Sym E)` is determined
  by its values on the structure map and on the degree-one elements of sections.
* `Stacks.RelativeSegre.scaledHom`: a ring map out of `Γ(U, Sym E)` rescaled in degree `n` by the
  `n`-th power of a fixed element.
* `Stacks.RelativeSegre.pieceSegre_compat_sameBase`: **the Segre morphisms of two pieces over the
  same affine open agree on their overlap.**
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry HomogeneousLocalization
open Stacks.AlgebraicGeometry.RelativeProjBridge
open scoped TensorProduct DirectSum

universe u

namespace Stacks.RelativeSegre

variable {X : Scheme.{u}}

/-! ### Functions pulled back from a spectrum -/

/-- The functions on `Y` pulled back from `Spec R` along `z`. -/
def fn {Y : Scheme.{u}} {R : CommRingCat.{u}} (z : Y ⟶ Spec R) : R →+* Γ(Y, ⊤) :=
  z.appTop.hom.comp (Scheme.ΓSpecIso R).inv.hom

/-- Pulling back along `z ≫ Spec.map φ` is pulling back along `z` after applying `φ`. -/
theorem fn_comp_SpecMap {Y : Scheme.{u}} {R S : CommRingCat.{u}} (z : Y ⟶ Spec S) (φ : R ⟶ S)
    (w : R) : fn (z ≫ Spec.map φ) w = fn z (φ w) := by
  have h := congrArg (fun k => k.hom w) (Scheme.ΓSpecIso_inv_naturality φ)
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] at h
  simp only [fn, RingHom.coe_comp, Function.comp_apply, Scheme.Hom.comp_appTop,
    CommRingCat.hom_comp, h]

/-- Pulling back along `g ≫ z` is pulling back along `z` followed by `g.appTop`. -/
theorem fn_precomp {Y Y' : Scheme.{u}} {R : CommRingCat.{u}} (g : Y' ⟶ Y) (z : Y ⟶ Spec R)
    (w : R) : fn (g ≫ z) w = g.appTop (fn z w) := by
  simp only [fn, RingHom.coe_comp, Function.comp_apply, Scheme.Hom.comp_appTop,
    CommRingCat.hom_comp]

/-! ### Ratios in a degree-zero localization -/

section Ratios

variable {σ A : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ℕ → σ)
  [GradedRing 𝒜] {f g x : A} (hf : f ∈ 𝒜 1) (hg : g ∈ 𝒜 1) (hx : x = f * g)

/-- The ratio `h / f` of two elements of degree one. -/
abbrev rat {f : A} (hf : f ∈ 𝒜 1) (h : A) (hh : h ∈ 𝒜 1) : Away 𝒜 f :=
  Away.mk 𝒜 hf 1 h (by simpa only [smul_eq_mul, mul_one] using hh)

/-- The image of `h / f` in `A_{(x)}`, for `x = f g`, is the fraction `(h g) / x`. -/
theorem val_awayMap_rat (h : A) (hh : h ∈ 𝒜 1) :
    (awayMap 𝒜 hg hx (rat 𝒜 hf h hh)).val =
      Localization.mk (h * g) (⟨x, 1, pow_one x⟩ : Submonoid.powers x) := by
  rw [awayMap_mk, Away.val_mk]
  congr 1 <;> simp

/-- **The ratios change by the ratio of the denominators**: in `A_{(fg)}`,
`h / g = (h / f) · (f / g)`. -/
theorem awayMap_rat_eq_mul (h : A) (hh : h ∈ 𝒜 1) :
    awayMap 𝒜 hf (hx.trans (mul_comm _ _)) (rat 𝒜 hg h hh) =
      awayMap 𝒜 hg hx (rat 𝒜 hf h hh) * awayMap 𝒜 hf (hx.trans (mul_comm _ _)) (rat 𝒜 hg f hf) := by
  apply HomogeneousLocalization.val_injective
  rw [HomogeneousLocalization.val_mul, val_awayMap_rat, val_awayMap_rat, val_awayMap_rat,
    Localization.mk_mul, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  simp only [OneMemClass.coe_one, Submonoid.coe_mul, one_mul]
  subst hx
  ring

/-- The two ratios of the denominators are inverse to each other in `A_{(fg)}`. -/
theorem awayMap_rat_mul_awayMap_rat :
    awayMap 𝒜 hf (hx.trans (mul_comm _ _)) (rat 𝒜 hg f hf) * awayMap 𝒜 hg hx (rat 𝒜 hf g hg) =
      1 := by
  apply HomogeneousLocalization.val_injective
  rw [HomogeneousLocalization.val_mul, val_awayMap_rat, val_awayMap_rat, Localization.mk_mul,
    HomogeneousLocalization.val_one, ← Localization.mk_one, Localization.mk_eq_mk_iff,
    Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  simp only [OneMemClass.coe_one, Submonoid.coe_mul, one_mul, mul_one]
  subst hx
  ring

end Ratios

/-! ### Ring maps out of `Γ(U, Sym E)` and their rescalings -/

section Generators

variable (E : X.Modules) [E.IsQuasicoherent] {U : X.Opens} (hU : IsAffineOpen U)

/-- **Two ring maps out of `Γ(U, Sym E)` related on generators are related in every degree.** If
`f'` agrees with `f` on the structure map and is `u` times `f` on the degree-one elements of the
sections of `E`, then `f'` is `uⁿ` times `f` on elements of degree `n`. -/
theorem eq_pow_mul_of_generators {S : Type u} [CommRing S]
    (f f' : (alg E).sectionRing U →+* S) (u : S)
    (h0 : ∀ r : Γ(X, U), f' ((alg E).strHom U r) = f ((alg E).strHom U r))
    (h1 : ∀ m : Γ(E, U), f' (deg1 E hU m) = u * f (deg1 E hU m)) :
    ∀ (d : ℕ), ∀ x ∈ (alg E).grading U d, f' x = u ^ d * f x := by
  set e := Stacks.SymGraded.AffinePieces.symSectionRingEquiv E hU
    (Stacks.SymGraded.isQuasicoherentPieces_of_isQuasicoherent E)
  have key : ∀ (d : ℕ), ∀ y ∈ SymPow.symmetricPower d Γ(X, U) Γ(E, U),
      f' (e.symm y) = u ^ d * f (e.symm y) := by
    intro d
    induction d with
    | zero =>
      intro y hy
      have h1' : SymPow.symmetricPower 0 Γ(X, U) Γ(E, U) =
          LinearMap.range (Algebra.linearMap Γ(X, U) (SymmetricAlgebra Γ(X, U) Γ(E, U))) :=
        (pow_zero _).trans Submodule.one_eq_range
      rw [h1'] at hy
      obtain ⟨r, rfl⟩ := hy
      have := Stacks.SymTwistChart.symSectionRingEquiv_symm_algebraMap E
        (Stacks.SymGraded.isQuasicoherentPieces_of_isQuasicoherent E) hU r
      simp only [Algebra.linearMap_apply, pow_zero, one_mul]
      rw [this, h0]
    | succ d ih =>
      intro y hy
      have hsucc : SymPow.symmetricPower (d + 1) Γ(X, U) Γ(E, U) =
          SymPow.symmetricPower d Γ(X, U) Γ(E, U) *
            LinearMap.range (SymmetricAlgebra.ι Γ(X, U) Γ(E, U)) := pow_succ _ _
      rw [hsucc] at hy
      refine Submodule.mul_induction_on hy (fun y hy z hz => ?_) (fun y z hy hz => ?_)
      · obtain ⟨m, rfl⟩ := hz
        have hm : e.symm (SymmetricAlgebra.ι Γ(X, U) Γ(E, U) m) = deg1 E hU m := rfl
        rw [map_mul, map_mul, map_mul, ih y hy, hm, h1 m]
        ring
      · rw [map_add, map_add, map_add, hy, hz, mul_add]
  intro d x hx
  simpa only [RingEquiv.symm_apply_apply] using key d (e x)
    ((Stacks.SymGraded.AffinePieces.mem_symmetricPower_symSectionRingEquiv E hU _ d x).mpr hx)

end Generators

/-! ### Pulling back the Segre ring map -/

section Pullback

variable (H G : X.Modules) [H.IsQuasicoherent] [G.IsQuasicoherent] {U : X.Opens}
  (hU : IsAffineOpen U) (a : (alg H).grading U 1) (b : (alg G).grading U 1)

/-- The first projection of a piece to the standard chart of `a`. -/
abbrev prL : Spec (CommRingCat.of (pieceRing H G a b)) ⟶
    Spec (CommRingCat.of (Away ((alg H).grading U) (a : (alg H).sectionRing U))) :=
  Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom)

/-- The second projection of a piece to the standard chart of `b`. -/
abbrev prR : Spec (CommRingCat.of (pieceRing H G a b)) ⟶
    Spec (CommRingCat.of (Away ((alg G).grading U) (b : (alg G).sectionRing U))) :=
  Spec.map (CommRingCat.ofHom (RingHomClass.toRingHom (Algebra.TensorProduct.includeRight
    (R := Γ(X, U)) (A := Away ((alg H).grading U) (a : (alg H).sectionRing U))
    (B := Away ((alg G).grading U) (b : (alg G).sectionRing U)))))

/-- The function pulled back along `s` from `x ⊗ y` is the product of the functions pulled back
from `x` along `s ≫ prL` and from `y` along `s ≫ prR`. -/
theorem fn_tmul {T : Scheme.{u}} (s : T ⟶ Spec (CommRingCat.of (pieceRing H G a b)))
    (x : Away ((alg H).grading U) (a : (alg H).sectionRing U))
    (y : Away ((alg G).grading U) (b : (alg G).sectionRing U)) :
    fn s (x ⊗ₜ[Γ(X, U)] y) = fn (s ≫ prL H G a b) x * fn (s ≫ prR H G a b) y := by
  rw [fn_comp_SpecMap, fn_comp_SpecMap, ← map_mul]
  congr 1
  simp [Algebra.TensorProduct.tmul_mul_tmul]

/-- The function pulled back along `s` from the image of a section `r` of `𝒪_X` over `U` is the
function pulled back along `s ≫ prL` from the image of `r` in degree zero. -/
theorem fn_algebraMap {T : Scheme.{u}} (s : T ⟶ Spec (CommRingCat.of (pieceRing H G a b)))
    (r : Γ(X, U)) :
    fn s (algebraMap Γ(X, U) (pieceRing H G a b) r) =
      fn (s ≫ prL H G a b) (fromZeroRingHom ((alg H).grading U) _
        (Stacks.AlgebraicGeometry.ProjBundleSurjection.strZeroSheaf (alg H) U r)) := by
  rw [fn_comp_SpecMap, Algebra.TensorProduct.algebraMap_apply]
  rfl

/-- The irrelevant ideal of `Γ(U, Sym(H ⊗ G))` generates the unit ideal of `Γ(T, 𝒪_T)` under the
Segre ring map followed by the functions pulled back along `s`. -/
theorem map_irrelevant_fn_segre {T : Scheme.{u}}
    (s : T ⟶ Spec (CommRingCat.of (pieceRing H G a b))) :
    (HomogeneousIdeal.irrelevant ((alg (tens H G)).grading U)).toIdeal.map
      ((fn s).comp (segreRingHom H G hU a b)) = ⊤ := by
  rw [← Ideal.map_map (segreRingHom H G hU a b) (fn s)]
  have h := map_irrelevant_segreΓ H G hU a b
  rw [segreΓ, ← Ideal.map_map] at h
  rw [show fn s = s.appTop.hom.comp (Scheme.ΓSpecIso _).inv.hom from rfl,
    ← Ideal.map_map, h, Ideal.map_top]

/-- The morphism of a piece to `Proj Γ(U, Sym(H ⊗ G))`, pulled back along `s`, is the morphism of
the Segre ring map followed by the functions pulled back along `s`. -/
theorem comp_fromOfGlobalSections_segre {T : Scheme.{u}}
    (s : T ⟶ Spec (CommRingCat.of (pieceRing H G a b))) :
    s ≫ Proj.fromOfGlobalSections ((alg (tens H G)).grading U) (segreΓ H G hU a b)
        (map_irrelevant_segreΓ H G hU a b) =
      Proj.fromOfGlobalSections ((alg (tens H G)).grading U)
        ((fn s).comp (segreRingHom H G hU a b)) (map_irrelevant_fn_segre H G hU a b s) :=
  Proj.comp_fromOfGlobalSections _ s _ _ _

end Pullback

/-! ### Two pieces over the same affine open -/

section SameBase

variable (E : X.Modules) [E.IsQuasicoherent] {U : X.Opens} (hU : IsAffineOpen U)

/-- Two morphisms into standard charts `D₊(a)` and `D₊(a')` of `𝐏(E)` over the same affine open
which agree in `𝐏(E)` factor through `D₊(a a') = D₊(a) ∩ D₊(a')`. -/
theorem exists_overlap {T : Scheme.{u}} (a a' : (alg E).grading U 1)
    (φ : T ⟶ Spec (CommRingCat.of (Away ((alg E).grading U) (a : (alg E).sectionRing U))))
    (φ' : T ⟶ Spec (CommRingCat.of (Away ((alg E).grading U) (a' : (alg E).sectionRing U))))
    (h : φ ≫ chartι E hU a = φ' ≫ chartι E hU a') :
    ∃ ρ : T ⟶ Spec (CommRingCat.of (Away ((alg E).grading U)
        ((a : (alg E).sectionRing U) * a'))),
      ρ ≫ Spec.map (CommRingCat.ofHom (awayMap ((alg E).grading U) a'.2 rfl)) = φ ∧
      ρ ≫ Spec.map (CommRingCat.ofHom (awayMap ((alg E).grading U) a.2 (mul_comm _ _))) = φ' := by
  have := isOpenImmersion_chart E hU
  have h' : φ ≫ Proj.awayι ((alg E).grading U) _ a.2 Nat.one_pos =
      φ' ≫ Proj.awayι ((alg E).grading U) _ a'.2 Nat.one_pos := by
    rw [← cancel_mono ((bun E).chart U hU)]
    simpa only [chartι, Category.assoc] using h
  refine ⟨pullback.lift φ φ' h' ≫
    (Proj.pullbackAwayιIso ((alg E).grading U) a.2 Nat.one_pos a'.2 Nat.one_pos rfl).hom, ?_, ?_⟩
  · rw [Category.assoc, Proj.pullbackAwayιIso_hom_SpecMap_awayMap_left, pullback.lift_fst]
  · rw [Category.assoc, Proj.pullbackAwayιIso_hom_SpecMap_awayMap_right, pullback.lift_snd]

end SameBase

section SameBaseSegre

variable (H G : X.Modules) [H.IsQuasicoherent] [G.IsQuasicoherent] {U : X.Opens}
  (hU : IsAffineOpen U)

/-- The ratios of two pieces pulled back along `ρ` are inverse to each other. -/
private theorem fn_awayMap_rat_mul_eq_one (F : X.Modules) [F.IsQuasicoherent] {U : X.Opens}
    (c c' : (alg F).grading U 1) {T : Scheme.{u}}
    (ρ : T ⟶ Spec (CommRingCat.of (Away ((alg F).grading U)
      ((c : (alg F).sectionRing U) * c')))) :
    fn ρ (awayMap ((alg F).grading U) c.2 (mul_comm _ _)
        (rat ((alg F).grading U) c'.2 c c.2)) *
      fn ρ (awayMap ((alg F).grading U) c'.2 rfl (rat ((alg F).grading U) c.2 c' c'.2)) = 1 := by
  rw [← map_mul, awayMap_rat_mul_awayMap_rat ((alg F).grading U) c.2 c'.2 rfl, map_one]

/-- Changing the denominator of a ratio, pulled back along `ρ`, multiplies by the ratio of the
denominators. -/
private theorem fn_awayMap_rat_eq_mul (F : X.Modules) [F.IsQuasicoherent] {U : X.Opens}
    (c c' : (alg F).grading U 1) {T : Scheme.{u}}
    (ρ : T ⟶ Spec (CommRingCat.of (Away ((alg F).grading U)
      ((c : (alg F).sectionRing U) * c'))))
    (h : (alg F).sectionRing U) (hh : h ∈ (alg F).grading U 1) :
    fn ρ (awayMap ((alg F).grading U) c.2 (mul_comm _ _) (rat ((alg F).grading U) c'.2 h hh)) =
      fn ρ (awayMap ((alg F).grading U) c'.2 rfl (rat ((alg F).grading U) c.2 h hh)) *
      fn ρ (awayMap ((alg F).grading U) c.2 (mul_comm _ _)
        (rat ((alg F).grading U) c'.2 c c.2)) := by
  rw [← map_mul, ← awayMap_rat_eq_mul ((alg F).grading U) c.2 c'.2 rfl h hh]

/-- **The Segre morphisms of two pieces over the same affine open agree on their overlap.** -/
theorem pieceSegre_compat_sameBase (a a' : (alg H).grading U 1) (b b' : (alg G).grading U 1)
    {T : Scheme.{u}} (s : T ⟶ Spec (CommRingCat.of (pieceRing H G a b)))
    (s' : T ⟶ Spec (CommRingCat.of (pieceRing H G a' b')))
    (hs : s ≫ pieceMap H G hU a b = s' ≫ pieceMap H G hU a' b') :
    s ≫ pieceSegre H G hU a b = s' ≫ pieceSegre H G hU a' b' := by
  have hL : (s ≫ prL H G a b) ≫ chartι H hU a = (s' ≫ prL H G a' b') ≫ chartι H hU a' := by
    simpa only [Category.assoc, pieceMap_fst] using
      congrArg (· ≫ pullback.fst (bun H).toBase (bun G).toBase) hs
  have hR : (s ≫ prR H G a b) ≫ chartι G hU b = (s' ≫ prR H G a' b') ≫ chartι G hU b' := by
    simpa only [Category.assoc, pieceMap_snd] using
      congrArg (· ≫ pullback.snd (bun H).toBase (bun G).toBase) hs
  obtain ⟨ρA, hρA, hρA'⟩ := exists_overlap H hU a a' _ _ hL
  obtain ⟨ρB, hρB, hρB'⟩ := exists_overlap G hU b b' _ _ hR
  let uA := fn ρA
    (awayMap ((alg H).grading U) a.2 (mul_comm _ _) (rat ((alg H).grading U) a'.2 a a.2))
  let vA := fn ρA (awayMap ((alg H).grading U) a'.2 rfl (rat ((alg H).grading U) a.2 a' a'.2))
  let uB := fn ρB
    (awayMap ((alg G).grading U) b.2 (mul_comm _ _) (rat ((alg G).grading U) b'.2 b b.2))
  let vB := fn ρB (awayMap ((alg G).grading U) b'.2 rfl (rat ((alg G).grading U) b.2 b' b'.2))
  have hA : uA * vA = 1 := fn_awayMap_rat_mul_eq_one H a a' ρA
  have hB : uB * vB = 1 := fn_awayMap_rat_mul_eq_one G b b' ρB
  let u : Γ(T, ⊤)ˣ := ⟨uA * uB, vA * vB, by rw [mul_mul_mul_comm, hA, hB, one_mul],
    by rw [mul_mul_mul_comm, mul_comm vA, mul_comm vB, hA, hB, one_mul]⟩
  rw [pieceSegre, pieceSegre, ← Category.assoc, ← Category.assoc,
    comp_fromOfGlobalSections_segre, comp_fromOfGlobalSections_segre]
  congr 1
  refine Proj.fromOfGlobalSections_congr_unit _ _ _ u ?_ _ _
  refine eq_pow_mul_of_generators (tens H G) hU _ _ _ (fun r => ?_) (fun m => ?_)
  · simp only [RingHom.comp_apply, segreRingHom_strHom]
    rw [fn_algebraMap, fn_algebraMap, ← hρA, ← hρA', fn_comp_SpecMap, fn_comp_SpecMap]
    simp only [CommRingCat.hom_ofHom, awayMap_fromZeroRingHom]
  · obtain ⟨t, rfl⟩ := (Stacks.SectionTensorFormula.tensorSectionEquiv H G hU).surjective m
    induction t using TensorProduct.inductionOn with
    | tmul h g =>
      rw [Stacks.SectionTensorFormula.tensorSectionEquiv_tmul]
      simp only [RingHom.comp_apply, segreRingHom_deg1, segreLin_tensorSection]
      rw [fn_tmul, fn_tmul, ← hρA, ← hρA', ← hρB, ← hρB', fn_comp_SpecMap, fn_comp_SpecMap,
        fn_comp_SpecMap, fn_comp_SpecMap]
      refine (congrArg₂ (· * ·)
        (fn_awayMap_rat_eq_mul H a a' ρA (deg1 H hU h) (deg1_mem H hU h))
        (fn_awayMap_rat_eq_mul G b b' ρB (deg1 G hU g) (deg1_mem G hU g))).trans ?_
      ring!
    | add t₁ t₂ ih₁ ih₂ =>
      rw [map_add, deg1_add, map_add, map_add, ih₁, ih₂, mul_add]

end SameBaseSegre

end Stacks.RelativeSegre

end
