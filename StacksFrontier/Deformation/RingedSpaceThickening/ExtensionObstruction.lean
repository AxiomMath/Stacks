module

public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.SheafOfModules
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.CategoryTheory.Abelian.Refinements
public import Mathlib.CategoryTheory.Abelian.ShortExact
public import StacksFrontier.Algebra.Homology.DerivedCategory.Ext.YonedaExtOne
public import StacksFrontier.Deformation.RingedSpaceThickening.ExtensionActionNaturality
import StacksCore.Tactic.StacksAttribute

/-!
# Machinery for the obstruction to lifting a map of extensions (towards Stacks 08L6)

Let `i : (X, 𝒪_X) ⟶ (X', 𝒪_{X'})` be a first order thickening of ringed spaces, let

    0 ⟶ i_* 𝒦 ⟶ ℱ' ⟶ i_* ℱ ⟶ 0    and    0 ⟶ i_* ℒ ⟶ 𝒢' ⟶ i_* 𝒢 ⟶ 0

be extensions as in Tag 08L4, and let `φ : ℱ ⟶ 𝒢` and `ψ : 𝒦 ⟶ ℒ` be maps whose square with
the two canonical maps commutes, as in Tag 08L5 part (1). Tag 08L6 produces a class in
`Ext¹_{𝒪_X}(ℱ, ℒ)` whose vanishing is necessary and sufficient for the existence of an
`𝒪_{X'}`-module map `φ' : ℱ' ⟶ 𝒢'` compatible with `φ` and `ψ`. This file assembles the
ingredients of that construction.

The construction is the one in the source. Pull `𝒢'` back along `ℱ' ⟶ i_* ℱ ⟶ i_* 𝒢`, so that
its sections are pairs of sections of `ℱ'` and `𝒢'` with the same image in `i_* 𝒢`, and divide
by the copy of `i_* 𝒦` embedded by `(ℱ' ⟶ i_* ℱ, ψ)`. The quotient is an extension of `i_* ℱ`
by `i_* ℒ`; a compatible `φ'` is the same thing as a splitting of it; the ideal acts as zero on
its middle term, so by Tag 08KS that middle term is a pushforward and the extension descends to
`X`; and the class of the descended extension is the obstruction.

## Main definitions

* `CategoryTheory.Abelian.pullbackShortComplex`, `CategoryTheory.Abelian.quotientShortComplex`
  and `CategoryTheory.Abelian.pairShortComplex`: the pullback of a short exact sequence along a
  map of its quotient object, the quotient of the middle term of one short exact sequence by a
  subobject transverse to the kernel of another, and the sequence of pairs of sections of two
  short exact sequences with matching images.
* `CategoryTheory.Abelian.extClassOfEssImage`: the class, in the `Ext` group of the source
  category, of an extension whose middle term lies in the essential image of a fully faithful
  functor, bundled with its splitting criterion.

## Main results

* `CategoryTheory.Abelian.pullbackShortComplex_shortExact`,
  `CategoryTheory.Abelian.quotientShortComplex_shortExact` and
  `CategoryTheory.Abelian.pairShortComplex_shortExact`: the three constructions above are short
  exact.
* `CategoryTheory.Abelian.exists_lift_iff_exists_retraction`: a retraction of the kernel in the
  quotient of the pullback is the same thing as a compatible map of the two extensions.
* `CategoryTheory.Abelian.extClass_eq_zero_iff_exists_retraction`: the class of a short exact
  sequence vanishes exactly when its injection is split.
* `AlgebraicGeometry.RingedSpaceThickening.essImage_of_idealAction_eq_zero`: the converse of
  `AlgebraicGeometry.RingedSpaceThickening.idealAction_eq_zero_of_essImage` — a module on which
  the ideal of the thickening acts as zero is a direct image.

## Implementation notes

The abstract half of the file — everything in `CategoryTheory.Abelian` — is general homological
algebra and does not mention ringed spaces; it is kept here because this is its only consumer.

Each intermediate object of the construction is a named declaration rather than a `let` inside
one proof. The three short complexes are `abbrev`s on purpose: their field projections have to
be transparent to `rw`, which works at `implicit` transparency; this avoids switching that
transparency check off globally.

`Stacks.SheafOfModules.Tensor.ringSheaf` is made `implicit_reducible` for
`AlgebraicGeometry.RingedSpaceThickening.essImage_of_idealAction_eq_zero`, whose hypothesis
asserts that the ideal action is the zero morphism. The action is a map out of a tensor product,
and the tensor product is a functor into
`SheafOfModules (Stacks.SheafOfModules.Tensor.ringSheaf ⟨𝒪_{X'}, _⟩)`, while its target is typed
`SheafOfModules (structureSheafRing X')`; the two indices are equal by `rfl`, but
`Tensor.ringSheaf` is a plain `def`, so instance search — which does not unfold one — cannot
check that the target is an object of the source's category, and the numeral `0` is left without
an `OfNat` instance. The zero-morphism structure is found at either spelling; only the two
objects fail to be recognised as living in one category. Raising the transparency of that one
definition lets the check succeed, and leaves the statement exactly as written.

## References

* [Stacks Project, Tag 08L6](https://stacks.math.columbia.edu/tag/08L6)
* [Stacks Project, Tag 08L5](https://stacks.math.columbia.edu/tag/08L5)
* [Stacks Project, Tag 08L4](https://stacks.math.columbia.edu/tag/08L4)
* [Stacks Project, Tag 08KS](https://stacks.math.columbia.edu/tag/08KS)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive
open Opposite TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.SheafOfModules.TensorStalkRingedSpace

universe u

namespace CategoryTheory.Abelian

section Abstract

universe v

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The short complex obtained by pulling a short exact sequence `S` back along a morphism
`φ` into its quotient object: its middle term is the object of pairs of a section of `M` and a
section of `S.X₂` with the same image in `S.X₃`. -/
noncomputable abbrev pullbackShortComplex (S : ShortComplex C) {M : C} (φ : M ⟶ S.X₃) :
    ShortComplex C :=
  ShortComplex.mk (pullback.lift 0 S.f (by simp)) (pullback.fst φ S.g)
    (pullback.lift_fst _ _ _)

/-- If a map into a pullback of `u` and `S.g` is killed by `fst ≫ u`, its second projection
factors through the kernel `S.f` of the exact sequence `S`. -/
private theorem exists_lift_pullback_snd {S : ShortComplex C} [Mono S.f] (hS : S.Exact) {X A : C}
    {u : X ⟶ S.X₃} (a : A ⟶ pullback u S.g) (ha : a ≫ pullback.fst u S.g ≫ u = 0) :
    ∃ d : A ⟶ S.X₁, d ≫ S.f = a ≫ pullback.snd u S.g := by
  have hzero : (a ≫ pullback.snd u S.g) ≫ S.g = 0 := by
    rw [Category.assoc, ← pullback.condition, ha]
  exact ⟨hS.lift _ hzero, hS.lift_f _ hzero⟩

/-- Pulling a short exact sequence back along a morphism into its quotient object gives a short
exact sequence, with the same kernel. -/
theorem pullbackShortComplex_shortExact {S : ShortComplex C} (hS : S.ShortExact)
    {M : C} (φ : M ⟶ S.X₃) : (pullbackShortComplex S φ).ShortExact := by
  have := hS.mono_f
  have := hS.epi_g
  have hm : Mono (pullback.lift (0 : S.X₁ ⟶ M) S.f (by simp) : _ ⟶ pullback φ S.g) :=
    mono_of_mono_fac (pullback.lift_snd _ _ _)
  refine { exact := ?_, mono_f := hm, epi_g := by dsimp [pullbackShortComplex]; infer_instance }
  rw [ShortComplex.exact_iff_exact_up_to_refinements]
  intro A a ha
  dsimp only [pullbackShortComplex] at a ha ⊢
  obtain ⟨d, hd⟩ := exists_lift_pullback_snd hS.exact a (by rw [← Category.assoc, ha, zero_comp])
  refine ⟨A, 𝟙 A, inferInstance, d, ?_⟩
  apply pullback.hom_ext
  · simpa only [Category.id_comp, Category.assoc, pullback.lift_fst, comp_zero] using ha
  · simpa only [Category.id_comp, Category.assoc, pullback.lift_snd] using hd.symm

/-- Dividing the middle term of a short exact sequence `T` by a subobject `k` transverse to its
kernel: the descended map to the quotient object of a second short exact sequence `S`. -/
noncomputable abbrev quotientDesc {S T : ShortComplex C} (k : S.X₁ ⟶ T.X₂) (e : T.X₃ ≅ S.X₂)
    (hk : k ≫ T.g ≫ e.hom = S.f) : cokernel k ⟶ S.X₃ :=
  cokernel.desc k (T.g ≫ e.hom ≫ S.g)
    (by simpa only [Category.assoc, S.zero] using hk =≫ S.g)

@[simp]
theorem π_quotientDesc {S T : ShortComplex C} (k : S.X₁ ⟶ T.X₂) (e : T.X₃ ≅ S.X₂)
    (hk : k ≫ T.g ≫ e.hom = S.f) :
    cokernel.π k ≫ quotientDesc k e hk = T.g ≫ e.hom ≫ S.g :=
  cokernel.π_desc _ _ _

theorem quotientShortComplex_zero {S T : ShortComplex C} (k : S.X₁ ⟶ T.X₂) (e : T.X₃ ≅ S.X₂)
    (hk : k ≫ T.g ≫ e.hom = S.f) :
    (T.f ≫ cokernel.π k) ≫ quotientDesc k e hk = 0 := by
  rw [Category.assoc, π_quotientDesc, ← Category.assoc, T.zero, zero_comp]

/-- The quotient of the middle term of `T` by a subobject transverse to the kernel of `S`, as a
short complex `0 → T.X₁ → cokernel k → S.X₃ → 0`. -/
noncomputable abbrev quotientShortComplex {S T : ShortComplex C} (k : S.X₁ ⟶ T.X₂)
    (e : T.X₃ ≅ S.X₂) (hk : k ≫ T.g ≫ e.hom = S.f) : ShortComplex C :=
  ShortComplex.mk (T.f ≫ cokernel.π k) (quotientDesc k e hk)
    (quotientShortComplex_zero k e hk)

/-- Dividing the middle term of a short exact sequence by a subobject transverse to the kernel
of another gives an extension of the corresponding quotient by the same kernel. -/
theorem quotientShortComplex_shortExact {S T : ShortComplex C}
    (hS : S.ShortExact) (hT : T.ShortExact) (k : S.X₁ ⟶ T.X₂) (e : T.X₃ ≅ S.X₂)
    (hk : k ≫ T.g ≫ e.hom = S.f) : (quotientShortComplex k e hk).ShortExact := by
  have := hS.mono_f
  have := hS.epi_g
  have := hT.mono_f
  have := hT.epi_g
  have : Mono k := mono_of_mono_fac hk
  have hp : cokernel.π k ≫ quotientDesc k e hk = T.g ≫ e.hom ≫ S.g := π_quotientDesc k e hk
  have hm : Mono (T.f ≫ cokernel.π k) := by
    rw [Preadditive.mono_iff_cancel_zero]
    intro A a ha
    have ha' : (a ≫ T.f) ≫ cokernel.π k = 0 := by
      simpa only [Category.assoc] using ha
    let b := Abelian.monoLift k (a ≫ T.f) ha'
    have hb : b ≫ k = a ≫ T.f := Abelian.monoLift_comp _ _ _
    have hb0 : b = 0 := by
      rw [← cancel_mono S.f, zero_comp, ← hk, ← Category.assoc, ← Category.assoc, hb]
      simp [Category.assoc]
    rw [← cancel_mono T.f, zero_comp, ← hb, hb0, zero_comp]
  have he : Epi (quotientDesc k e hk) := epi_of_epi_fac hp
  refine { exact := ?_, mono_f := hm, epi_g := he }
  rw [ShortComplex.exact_iff_exact_up_to_refinements]
  intro A a ha
  dsimp only [quotientShortComplex] at a ha ⊢
  obtain ⟨A', π, hπ, b, hb⟩ := surjective_up_to_refinements_of_epi (cokernel.π k) a
  have hb0 : (b ≫ T.g ≫ e.hom) ≫ S.g = 0 := by
    rw [Category.assoc, Category.assoc, ← hp, ← Category.assoc, ← hb, Category.assoc, ha,
      comp_zero]
  have hc : hS.exact.lift (b ≫ T.g ≫ e.hom) hb0 ≫ S.f = b ≫ T.g ≫ e.hom :=
    hS.exact.lift_f _ _
  have hd0 : (b - hS.exact.lift (b ≫ T.g ≫ e.hom) hb0 ≫ k) ≫ T.g = 0 := by
    apply (cancel_mono e.hom).1
    simp only [sub_comp, Category.assoc, hk, hc, sub_self, zero_comp]
  refine ⟨A', π, hπ, hT.exact.lift _ hd0, ?_⟩
  change π ≫ a = _ ≫ (T.f ≫ cokernel.π k)
  symm
  rw [← Category.assoc, hT.exact.lift_f, sub_comp, Category.assoc, cokernel.condition,
    comp_zero, sub_zero, ← hb]

/-- The short complex of pairs: sections of the middle terms of `S` and `T` whose images in the
quotient objects agree under `φ`, as an extension of `S.X₃` by `S.X₁ ⊞ T.X₁`. -/
noncomputable abbrev pairShortComplex (S T : ShortComplex C) (φ : S.X₃ ⟶ T.X₃) : ShortComplex C :=
  ShortComplex.mk
    (pullback.lift (f := S.g ≫ φ) (g := T.g)
      (biprod.fst ≫ S.f) (biprod.snd ≫ T.f) (by simp))
    (pullback.fst (S.g ≫ φ) T.g ≫ S.g)
    (by rw [← Category.assoc, pullback.lift_fst, Category.assoc, S.zero, comp_zero])

/-- Pairs of sections whose images agree form an extension by the direct sum of the kernels. -/
theorem pairShortComplex_shortExact {S T : ShortComplex C}
    (hS : S.ShortExact) (hT : T.ShortExact) (φ : S.X₃ ⟶ T.X₃) :
    (pairShortComplex S T φ).ShortExact := by
  have := hS.mono_f
  have := hT.mono_f
  have := hS.epi_g
  have := hT.epi_g
  have hm : Mono (pairShortComplex S T φ).f := by
    rw [Preadditive.mono_iff_cancel_zero]
    intro A a ha
    apply biprod.hom_ext
    · apply (cancel_mono S.f).1
      simpa only [Category.assoc, pullback.lift_fst, zero_comp]
        using ha =≫ pullback.fst (S.g ≫ φ) T.g
    · apply (cancel_mono T.f).1
      simpa only [Category.assoc, pullback.lift_snd, zero_comp]
        using ha =≫ pullback.snd (S.g ≫ φ) T.g
  refine { mono_f := hm, epi_g := by dsimp [pairShortComplex]; infer_instance, exact := ?_ }
  rw [ShortComplex.exact_iff_exact_up_to_refinements]
  intro A a ha
  dsimp [pairShortComplex] at a ha ⊢
  have ha' : (a ≫ pullback.fst (S.g ≫ φ) T.g) ≫ S.g = 0 := by
    simpa only [Category.assoc] using ha
  obtain ⟨d, hd⟩ := exists_lift_pullback_snd hT.exact a
    (by simpa only [Category.assoc, zero_comp] using ha' =≫ φ)
  refine ⟨A, 𝟙 A, inferInstance,
    biprod.lift (hS.exact.lift (a ≫ pullback.fst (S.g ≫ φ) T.g) ha') d, ?_⟩
  apply pullback.hom_ext
  · simp only [Category.id_comp, Category.assoc, pullback.lift_fst, biprod.lift_fst_assoc]
    exact (hS.exact.lift_f _ ha').symm
  · simp only [Category.id_comp, Category.assoc, pullback.lift_snd, biprod.lift_snd_assoc]
    exact hd.symm

/-- A retraction of the kernel in the quotient of the pullback is the same thing as a map of the
two original extensions inducing `φ` on quotient objects and `ψ` on kernels. -/
theorem exists_lift_iff_exists_retraction {K L M N B D Pb : C}
    (f : K ⟶ M) (g : M ⟶ B) (ii : L ⟶ N) (j : N ⟶ D)
    (s : L ⟶ Pb) (t : Pb ⟶ M) (r : Pb ⟶ N) (k : K ⟶ Pb)
    (φ : B ⟶ D) (ψ : K ⟶ L)
    (hij : ii ≫ j = 0) (hst : s ≫ t = 0)
    (hT : (ShortComplex.mk ii j hij).Exact) (hR : (ShortComplex.mk s t hst).Exact)
    [Mono ii] [Epi t]
    (hkt : k ≫ t = f) (hkr : k ≫ r = ψ ≫ ii) (hsr : s ≫ r = ii)
    (htr : t ≫ g ≫ φ = r ≫ j) :
    (∃ v : cokernel k ⟶ L, (s ≫ cokernel.π k) ≫ v = 𝟙 L) ↔
      ∃ α : M ⟶ N, f ≫ α = ψ ≫ ii ∧ α ≫ j = g ≫ φ := by
  constructor
  · rintro ⟨v, hv⟩
    have hd : s ≫ (r - cokernel.π k ≫ v ≫ ii) = 0 := by
      rw [comp_sub, hsr, ← Category.assoc, ← Category.assoc, hv, Category.id_comp, sub_self]
    have hα : t ≫ hR.desc (r - cokernel.π k ≫ v ≫ ii) hd = r - cokernel.π k ≫ v ≫ ii :=
      hR.g_desc _ hd
    refine ⟨hR.desc (r - cokernel.π k ≫ v ≫ ii) hd, ?_, ?_⟩
    · rw [← hkt, Category.assoc, hα]
      simp only [comp_sub, hkr, ← Category.assoc, cokernel.condition, zero_comp, sub_zero]
    · apply (cancel_epi t).1
      rw [← Category.assoc, hα, sub_comp, Category.assoc, Category.assoc, hij, comp_zero,
        comp_zero, sub_zero, htr]
  · rintro ⟨α, hα₁, hα₂⟩
    have hd : (r - t ≫ α) ≫ j = 0 := by
      rw [sub_comp, Category.assoc, hα₂, htr, sub_self]
    have hdi : hT.lift (r - t ≫ α) hd ≫ ii = r - t ≫ α := hT.lift_f _ _
    have hkd : k ≫ hT.lift (r - t ≫ α) hd = 0 := by
      apply (cancel_mono ii).1
      rw [Category.assoc, hdi, comp_sub, ← Category.assoc, hkt, hα₁, hkr, sub_self, zero_comp]
    refine ⟨cokernel.desc k (hT.lift (r - t ≫ α) hd) hkd, ?_⟩
    rw [Category.assoc, cokernel.π_desc]
    apply (cancel_mono ii).1
    rw [Category.assoc, hdi, comp_sub, ← Category.assoc, hst, zero_comp, sub_zero, hsr,
      Category.id_comp]

end Abstract

section ExtClass

universe v u' v'

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt C] [HasDerivedCategory C]
  {D : Type u'} [Category.{v'} D] [Abelian D]

/-- The class of a short exact sequence vanishes exactly when its injection is split. -/
theorem extClass_eq_zero_iff_exists_retraction {S : ShortComplex C} (hS : S.ShortExact) :
    hS.extClass.hom = 0 ↔ ∃ r : S.X₂ ⟶ S.X₁, S.f ≫ r = 𝟙 _ := by
  have he : hS.extClass.hom = 0 ↔ hS.extClass = 0 := by
    refine ⟨fun h => Abelian.Ext.ext (by simpa using h), fun h => by simp [h]⟩
  rw [he]
  constructor
  · intro h
    obtain ⟨y, hy⟩ := Abelian.Ext.contravariant_sequence_exact₁ hS S.X₁
      (Abelian.Ext.mk₀ (𝟙 S.X₁)) (add_zero 1) (by simp [h])
    obtain ⟨r, rfl⟩ := (Abelian.Ext.mk₀_bijective S.X₂ S.X₁).surjective y
    refine ⟨r, (Abelian.Ext.mk₀_bijective _ _).injective ?_⟩
    simpa only [Abelian.Ext.mk₀_comp_mk₀] using hy
  · rintro ⟨r, hr⟩
    calc
      hS.extClass = hS.extClass.comp (Abelian.Ext.mk₀ (𝟙 _)) (add_zero 1) := by simp
      _ = hS.extClass.comp (Abelian.Ext.mk₀ (S.f ≫ r)) (add_zero 1) := by rw [hr]
      _ = 0 := by rw [← Abelian.Ext.mk₀_comp_mk₀]; exact hS.extClass_comp_assoc _

/-- Descend an extension whose middle term lies in the essential image of a fully faithful
functor through that functor, and take the class of the descent in degree one. The bundled
property is that the class vanishes exactly when the extension is split. -/
noncomputable def extClassOfEssImage
    (P : C ⥤ D) [P.Full] [P.Faithful] [P.PreservesZeroMorphisms]
    {F L : C} {H : D} (a : P.obj L ⟶ H) (b : H ⟶ P.obj F)
    (w : a ≫ b = 0) (hS : (ShortComplex.mk a b w).ShortExact)
    (hH : P.essImage H) :
    {o : Abelian.zExt F L 1 // o = 0 ↔ ∃ r : H ⟶ P.obj L, a ≫ r = 𝟙 _} := by
  apply Classical.indefiniteDescription
  obtain ⟨H₀, ⟨e⟩⟩ := hH
  have ha : P.map (P.preimage (a ≫ e.inv)) = a ≫ e.inv := P.map_preimage _
  have hb : P.map (P.preimage (e.hom ≫ b)) = e.hom ≫ b := P.map_preimage _
  have w₀ : P.preimage (a ≫ e.inv) ≫ P.preimage (e.hom ≫ b) = 0 := by
    apply P.map_injective
    simp only [P.map_comp, P.map_zero, ha, hb, Category.assoc, e.inv_hom_id_assoc, w]
  have hS₀ : (ShortComplex.mk (P.preimage (a ≫ e.inv)) (P.preimage (e.hom ≫ b)) w₀).ShortExact := by
    apply ShortExact.reflects_shortExact_of_faithful P
    refine ShortComplex.shortExact_of_iso
      (ShortComplex.isoMk (S₁ := ShortComplex.mk a b w)
        (S₂ := (ShortComplex.mk (P.preimage (a ≫ e.inv)) (P.preimage (e.hom ≫ b)) w₀).map P)
        (Iso.refl _) e.symm (Iso.refl _) ?_ ?_) hS
    · simp [ha]
    · simp [hb]
  refine ⟨hS₀.extClass.hom, ?_⟩
  rw [extClass_eq_zero_iff_exists_retraction]
  constructor
  · rintro ⟨r, hr⟩
    refine ⟨e.inv ≫ P.map r, ?_⟩
    rw [← Category.assoc, ← ha, ← P.map_comp, hr, P.map_id]
  · rintro ⟨r, hr⟩
    refine ⟨P.preimage (e.hom ≫ r), ?_⟩
    apply P.map_injective
    simp only [P.map_comp, P.map_preimage, P.map_id, Category.assoc, e.inv_hom_id_assoc, hr]

end ExtClass

end CategoryTheory.Abelian

namespace AlgebraicGeometry.RingedSpaceThickening

variable {X X' : RingedSpace.{u, u}} (i : X ⟶ X')

/-- The ideal of a thickening `i : X ⟶ X'`, named in the spelling of the category of
`𝒪_{X'}`-modules that the tensor product and the ideal action use. -/
noncomputable abbrev idealSheafModule : SheafOfModules.{u} (structureSheafRing X') :=
  AlgebraicGeometry.SheafOfModules.idealSheaf i

/-- A section of a sheaf of modules killed by a morphism comes from the kernel. -/
theorem exists_kernel_section {Y : RingedSpace.{u, u}}
    {M N : SheafOfModules.{u} (structureSheafRing Y)} (f : M ⟶ N)
    (U : (Opens Y)ᵒᵖ) (x : M.val.obj U) (hx : (f.val.app U).hom x = 0) :
    ∃ a : (kernel f).val.obj U, ((kernel.ι f).val.app U).hom a = x := by
  have h := KernelFork.mapIsLimit _ (kernelIsKernel f)
    (SheafOfModules.forget (structureSheafRing Y) ⋙ PresheafOfModules.evaluation (structureSheafRing Y).obj U)
  have he := (ShortComplex.mk
    ((SheafOfModules.forget (structureSheafRing Y) ⋙
      PresheafOfModules.evaluation (structureSheafRing Y).obj U).map (kernel.ι f))
    ((SheafOfModules.forget (structureSheafRing Y) ⋙
      PresheafOfModules.evaluation (structureSheafRing Y).obj U).map f)
    (by rw [← Functor.map_comp, kernel.condition, Functor.map_zero])).exact_of_f_is_kernel h
  exact (ShortComplex.moduleCat_exact_iff _).1 he x hx

-- The hypothesis and the first step both read the zero morphism of `Mod(𝒪_{X'})` at a hom type
-- the tensor product spells with its own ring; see the implementation note.
attribute [local implicit_reducible] Stacks.SheafOfModules.Tensor.ringSheaf in
/-- The converse of `idealAction_eq_zero_of_essImage`: an `𝒪_{X'}`-module on which the ideal of
a thickening acts as zero lies in the essential image of `i_*`, hence descends to `X`. By
**Stacks 08KS** it is enough that the kernel ideal annihilate it, and that is read off the
action on pure tensors of local sections. -/
theorem essImage_of_idealAction_eq_zero (hi : IsThickening i)
    (N : SheafOfModules.{u} (structureSheafRing X')) (h : idealAction i N = 0) :
    (modulePushforward i).essImage N := by
  refine ((closedQuotientOfIsThickening i hi).modulePushforward_essImage_iff N).2 ?_
  intro U a ha
  have hker : ((structureSheafHom i).hom.app (op U)).hom a = 0 :=
    RingHom.mem_ker.mp
      ((ClosedQuotientMorphismOfRingedSpaces.mem_kernelIdeal_iff_mem_ker_structureSheafHom
        (S := closedQuotientOfIsThickening i hi) (U := op U) a).2 ha)
  obtain ⟨a', ha'⟩ := exists_kernel_section
    (SheafOfModules.unitToPushforwardObjUnit (structureSheafHom i)) (op U) a hker
  intro m
  have key := idealAction_app_tmul i N U a' m
  rw [h] at key
  exact ha' ▸ key.symm

end AlgebraicGeometry.RingedSpaceThickening

end
