module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjTriplePullbackPowMul

/-!
# The weight transition `F_d → F_{kd}` is a map of functors

The transition `Stacks.AlgebraicGeometry.ProjTripleDegreeFunctor.Fd.veronese` sends the class of a
weight-`d` triple `(L, ψ)` to the class of `(L^{⊗ k}, ψ|_{A^{(kd)}})`. This file proves it
**natural in the test scheme**: it commutes with the pullback maps of the two functors, so it is a
morphism `F_d ⟶ F_{kd}` in `Scheme.{u}ᵒᵖ ⥤ Type (u + 1)` and the `F_d` form a genuine diagram
along divisibility.

The content is one coherence: the Veronese comparison `(L^{⊗ k}) ^⊗ m ≅ L ^⊗ (km)` is compatible
with the comparison `(j^*L) ^⊗ n ≅ j^*(L ^⊗ n)` through which a section is pulled back. Its proof
is an induction on `m` whose step is the multiplicativity of the latter comparison,
`Stacks.AlgebraicGeometry.ProjTriplePullbackPowMul.mulIso_pullbackNatTensorPowIso`, because the
successor comparison of a Veronese system *is* a multiplication isomorphism of the underlying
system.

## Main results

* `Stacks.AlgebraicGeometry.ProjVeroneseRestrict.powVeroneseIso_zero_inv`,
  `powVeroneseIso_succ` and `powVeroneseIso_succ_inv`: the two arms of the recursion defining the
  Veronese comparison, with the identity comparisons of the iterated powers cancelled.
* `Stacks.AlgebraicGeometry.ProjVeroneseRestrict.pullbackNatTensorPowIso_powVeroneseIso`: **the
  Veronese comparison is compatible with the comparison of the inverse images of the tensor
  powers.**
* `Stacks.AlgebraicGeometry.ProjVeroneseRestrict.veroneseRestrict_pullbackSections`: **the
  Veronese restriction of a pulled-back graded map is strictly equivalent to the pullback of its
  Veronese restriction.**
* `Stacks.AlgebraicGeometry.ProjTripleDegreeFunctor.Fd.veronese_pullback`: **the transition
  commutes with the pullback maps**, and
  `Stacks.AlgebraicGeometry.ProjTripleDegreeFunctor.Fd.veroneseNatTrans`: **the transition as a
  morphism of functors `F_d ⟶ F_{kd}`.**

## Implementation notes

**Why the section-level statement is reached through `secOf`.** The two graded maps being compared
are built from the inverse comparisons applied to a global section, and the only available handle
on the pullback of a section as a morphism out of the monoidal unit is
`Stacks.AlgebraicGeometry.ProjChartSectionPullback.secOf_pullSection`. So the comparison of the
two sections is turned into a comparison of morphisms out of the unit, where it is the coherence
above postcomposed with a fixed morphism, and turned back by the bijection
`Stacks.AlgebraicGeometry.ProjChartFromRatios.globalSection_secOf`.

## References

* [Stacks Project, Section 01N4](https://stacks.math.columbia.edu/tag/01N4)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 01NC](https://stacks.math.columbia.edu/tag/01NC)
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory TopologicalSpace Opposite
open AlgebraicGeometry
open Stacks.Ample (IsInvertibleModule)
open Stacks.AmplePullbackPart1 (natTensorPowCongr)
open Stacks.GradedSections (natPowerSystem)
open Stacks.Monoidal (PowerSystem)
open Stacks.TensorPowers (natTensorPow)
open Stacks.AlgebraicGeometry.ProjChartFromRatios (VeroneseSections secOf globalSection_secOf)
open Stacks.AlgebraicGeometry.ProjChartRatioPullback (pullSection pullbackNatTensorPowIso)
open Stacks.AlgebraicGeometry.ProjChartPullbackCotensorator (pullbackCotensorator
  pullbackCotensorator_whiskerRight pullbackNatTensorPowIso_inv_succ)
open Stacks.AlgebraicGeometry.ProjChartSectionPullback (pullbackNatTensorPowIso_inv_zero
  secOf_pullSection)
open Stacks.AlgebraicGeometry.ProjTripleClassifying (SectionsEquiv)
open Stacks.AlgebraicGeometry.ProjTriplePullback (pullbackSections)
open Stacks.AlgebraicGeometry.ProjTriplePullbackPowMul (mulIso_pullbackNatTensorPowIso)
open Stacks.PullbackUnitSection (unitPullback)

universe u w

namespace Stacks.AlgebraicGeometry.ProjVeroneseRestrict

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory

/-! ### The recursion defining the Veronese comparison -/

section Recursion

variable {Y : Scheme.{u}} (L : Y.Modules)

/-- In degree zero the Veronese comparison is the identity of the monoidal unit: both systems
identify their zeroth power with the unit by the identity. -/
theorem powVeroneseIso_zero_inv (k : ℕ) :
    (powVeroneseIso L k 0).inv = 𝟙 (natTensorPow L (k * 0)) := by
  rw [powVeroneseIso, PowerSystem.compare_zero]
  simp only [Iso.trans_inv, Iso.symm_inv]
  simp only [Stacks.GradedSections.natPowerSystem_objZeroIso, Iso.refl_hom, Iso.refl_inv]
  exact Category.id_comp _

/-- **The successor step of the Veronese comparison**: one factor `L^{⊗ k}` is split off and the
two sides are joined by the multiplication isomorphism `L ^⊗ (km) ⊗ L ^⊗ k ≅ L ^⊗ (km + k)` of the
iterated powers — the successor comparison of a Veronese system is a multiplication isomorphism of
the underlying system. -/
theorem powVeroneseIso_succ (k m : ℕ) :
    powVeroneseIso L k (m + 1)
      = tensorIso (powVeroneseIso L k m) (Iso.refl (natTensorPow L k)) ≪≫
          (natPowerSystem L).mulIso (k * m) k := by
  rw [powVeroneseIso, PowerSystem.compare_succ, ← powVeroneseIso]
  exact Iso.ext (Category.id_comp _)

/-- `powVeroneseIso_succ` read on inverses, in the whiskered spelling the coherence below
consumes. -/
theorem powVeroneseIso_succ_inv (k m : ℕ) :
    (powVeroneseIso L k (m + 1)).inv
      = ((natPowerSystem L).mulIso (k * m) k).inv ≫
          ((powVeroneseIso L k m).inv ▷ natTensorPow L k) := by
  rw [powVeroneseIso_succ]
  simp only [Iso.trans_inv, tensorIso_inv, Iso.refl_inv, MonoidalCategory.tensorHom_id]
  rfl

end Recursion

/-! ### The Veronese comparison against the comparison of the inverse images -/

section Pullback

variable {Y Y' : Scheme.{u}} (j : Y' ⟶ Y) (L : Y.Modules) [IsInvertibleModule Y L]

/-- The `(m+1)`-st tensor power of an isomorphism, on `hom`. -/
theorem natTensorPowCongr_succ_hom {C : Type*} [Category C] [MonoidalCategory C] {M N : C}
    (e : M ≅ N) (m : ℕ) :
    (natTensorPowCongr e (m + 1)).hom = (natTensorPowCongr e m).hom ⊗ₘ e.hom := rfl

/-- The bookkeeping of the inductive step in a bare monoidal category: a comparison in the second
factor cancels against its inverse, leaving the first factor's composite whiskered. -/
private theorem tensor_aux {D : Type*} [Category D] [MonoidalCategory D]
    {A₀ A₁ A₂ A₃ E₀ E₁ : D} (a : A₀ ⟶ A₁) (b : A₁ ⟶ A₂) (c : A₂ ⟶ A₃) (e : E₁ ≅ E₀) :
    (a ⊗ₘ e.inv) ≫ (b ▷ E₁) ≫ (c ⊗ₘ e.hom) = ((a ≫ b ≫ c) ▷ E₀) := by
  rw [← MonoidalCategory.tensorHom_id b E₁, MonoidalCategory.tensorHom_comp_tensorHom,
    MonoidalCategory.tensorHom_comp_tensorHom, Category.id_comp, Iso.inv_hom_id,
    MonoidalCategory.tensorHom_id]

/-- **The comparison of the inverse images of the tensor powers against the inverse of a
multiplication isomorphism**, the form of
`Stacks.AlgebraicGeometry.ProjTriplePullbackPowMul.mulIso_pullbackNatTensorPowIso` the induction
below consumes. -/
theorem pullbackNatTensorPowIso_inv_mulIso_inv (p q : ℕ) :
    (pullbackNatTensorPowIso j L (p + q)).inv ≫
        ((natPowerSystem ((Scheme.Modules.pullback j).obj L)).mulIso p q).inv
      = (Scheme.Modules.pullback j).map ((natPowerSystem L).mulIso p q).inv ≫
          pullbackCotensorator j (natTensorPow L p) (natTensorPow L q) ≫
          ((pullbackNatTensorPowIso j L p).inv ⊗ₘ (pullbackNatTensorPowIso j L q).inv) := by
  have h : (pullbackNatTensorPowIso j L (p + q)).inv
      = (Scheme.Modules.pullback j).map ((natPowerSystem L).mulIso p q).inv ≫
          pullbackCotensorator j (natTensorPow L p) (natTensorPow L q) ≫
          ((pullbackNatTensorPowIso j L p).inv ⊗ₘ (pullbackNatTensorPowIso j L q).inv) ≫
          ((natPowerSystem ((Scheme.Modules.pullback j).obj L)).mulIso p q).hom := by
    rw [← mulIso_pullbackNatTensorPowIso j L p q, ← Functor.map_comp_assoc, Iso.inv_hom_id,
      (Scheme.Modules.pullback j).map_id, Category.id_comp]
  rw [h, Category.assoc, Category.assoc, Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- **The Veronese comparison is compatible with the comparison of the inverse images of the
tensor powers.** Reading a global section of `L ^⊗ (km)` backwards through the Veronese comparison
and then pulling it back is pulling it back and then reading it backwards through the Veronese
comparison for `j^*L`, up to the `m`-th tensor power of the comparison in degree `k`.

By induction on `m`. At a successor the Veronese comparison splits off one factor by a
multiplication isomorphism of the iterated powers, and the comparison of the inverse images
carries that multiplication to the corresponding one for `j^*L`
(`Stacks.AlgebraicGeometry.ProjTriplePullbackPowMul.mulIso_pullbackNatTensorPowIso`); what is left
is the naturality of the cotensorator in its first variable and the successor recursion of the
comparison of the inverse images. -/
theorem pullbackNatTensorPowIso_powVeroneseIso (k : ℕ) : ∀ m : ℕ,
    (pullbackNatTensorPowIso j L (k * m)).inv ≫
        (powVeroneseIso ((Scheme.Modules.pullback j).obj L) k m).inv ≫
        (natTensorPowCongr (pullbackNatTensorPowIso j L k) m).hom
      = (Scheme.Modules.pullback j).map (powVeroneseIso L k m).inv ≫
          (pullbackNatTensorPowIso j (natTensorPow L k) m).inv
  | 0 => by
      have h1 : (powVeroneseIso ((Scheme.Modules.pullback j).obj L) k 0).inv ≫
            (natTensorPowCongr (pullbackNatTensorPowIso j L k) 0).hom
          = 𝟙 (natTensorPow ((Scheme.Modules.pullback j).obj L) (k * 0)) := by
        rw [powVeroneseIso_zero_inv]
        exact Category.id_comp _
      have hW : (Scheme.Modules.pullback j).map (powVeroneseIso L k 0).inv
          = 𝟙 ((Scheme.Modules.pullback j).obj (natTensorPow (natTensorPow L k) 0)) := by
        rw [powVeroneseIso_zero_inv]
        exact (Scheme.Modules.pullback j).map_id _
      rw [h1, hW]
      exact (Category.comp_id _).trans ((pullbackNatTensorPowIso_inv_zero j L).trans
        ((pullbackNatTensorPowIso_inv_zero j (natTensorPow L k)).symm.trans
          (Category.id_comp _).symm))
  | m + 1 => by
      have key : (pullbackNatTensorPowIso j L (k * m + k)).inv ≫
            (((natPowerSystem ((Scheme.Modules.pullback j).obj L)).mulIso (k * m) k).inv ≫
              ((powVeroneseIso ((Scheme.Modules.pullback j).obj L) k m).inv ▷
                natTensorPow ((Scheme.Modules.pullback j).obj L) k)) ≫
            ((natTensorPowCongr (pullbackNatTensorPowIso j L k) m).hom ⊗ₘ
              (pullbackNatTensorPowIso j L k).hom)
          = (Scheme.Modules.pullback j).map (((natPowerSystem L).mulIso (k * m) k).inv ≫
              ((powVeroneseIso L k m).inv ▷ natTensorPow L k)) ≫
            pullbackCotensorator j (natTensorPow (natTensorPow L k) m) (natTensorPow L k) ≫
            ((pullbackNatTensorPowIso j (natTensorPow L k) m).inv ▷
              (Scheme.Modules.pullback j).obj (natTensorPow L k)) := by
        rw [Category.assoc,
          ← Category.assoc, pullbackNatTensorPowIso_inv_mulIso_inv j L (k * m) k,
          Category.assoc, Category.assoc,
          tensor_aux (pullbackNatTensorPowIso j L (k * m)).inv
            (powVeroneseIso ((Scheme.Modules.pullback j).obj L) k m).inv
            (natTensorPowCongr (pullbackNatTensorPowIso j L k) m).hom
            (pullbackNatTensorPowIso j L k),
          pullbackNatTensorPowIso_powVeroneseIso k m,
          MonoidalCategory.comp_whiskerRight,
          ← reassoc_of% (pullbackCotensorator_whiskerRight j (powVeroneseIso L k m).inv
            (natTensorPow L k)),
          ← Functor.map_comp_assoc]
      rw [← powVeroneseIso_succ_inv ((Scheme.Modules.pullback j).obj L) k m,
        ← natTensorPowCongr_succ_hom (pullbackNatTensorPowIso j L k) m,
        ← powVeroneseIso_succ_inv L k m,
        ← pullbackNatTensorPowIso_inv_succ j (natTensorPow L k) m] at key
      exact key

/-- `pullbackNatTensorPowIso_powVeroneseIso` read on a global section: the Veronese restriction
commutes with pulling a section back, up to the `m`-th tensor power of the comparison in degree
`k`.

Both sides are global sections of the same module, so both are read as morphisms out of the
monoidal unit, where `Stacks.AlgebraicGeometry.ProjChartSectionPullback.secOf_pullSection`
describes a pulled-back section and the coherence above finishes. -/
theorem natTensorPowCongr_app_pullSection (k m : ℕ) (z : Γ(natTensorPow L (k * m), ⊤)) :
    (natTensorPowCongr (pullbackNatTensorPowIso j L k) m).hom.app ⊤
        ((powVeroneseIso ((Scheme.Modules.pullback j).obj L) k m).inv.app ⊤
          (pullSection j L (k * m) z))
      = pullSection j (natTensorPow L k) m ((powVeroneseIso L k m).inv.app ⊤ z) := by
  have hsec : secOf ((Scheme.Modules.pullback j).obj (natTensorPow L k))
        ((natTensorPowCongr (pullbackNatTensorPowIso j L k) m).hom.app ⊤
          ((powVeroneseIso ((Scheme.Modules.pullback j).obj L) k m).inv.app ⊤
            (pullSection j L (k * m) z)))
      = secOf ((Scheme.Modules.pullback j).obj (natTensorPow L k))
          (pullSection j (natTensorPow L k) m ((powVeroneseIso L k m).inv.app ⊤ z)) := by
    rw [secOf_app, secOf_app, secOf_pullSection, secOf_pullSection, secOf_app,
      (Scheme.Modules.pullback j).map_comp, Category.assoc, Category.assoc, Category.assoc,
      Category.assoc, pullbackNatTensorPowIso_powVeroneseIso j L k m]
  have h := congrArg
    (Stacks.SectionProduct.globalSection Y' (natTensorPow
      ((Scheme.Modules.pullback j).obj (natTensorPow L k)) m)) hsec
  rwa [globalSection_secOf, globalSection_secOf] at h

end Pullback

/-! ### The transition against the pullback of a graded map -/

section Transition

variable {σ : Type w} {A : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜] {Y Y' : Scheme.{u}} {d : ℕ} {L : Y.Modules}
  [IsInvertibleModule Y L]

/-- **The Veronese restriction of a pulled-back graded map is strictly equivalent to the pullback
of its Veronese restriction.** The comparing isomorphism is
`Stacks.AlgebraicGeometry.ProjChartRatioPullback.pullbackNatTensorPowIso` in degree `k`, and the
degreewise identity is `natTensorPowCongr_app_pullSection`. -/
theorem veroneseRestrict_pullbackSections (ψ : VeroneseSections 𝒜 d L) (k : ℕ) (h : Y' ⟶ Y) :
    SectionsEquiv 𝒜 (veroneseRestrict 𝒜 (pullbackSections 𝒜 ψ h) k)
      (pullbackSections 𝒜 (veroneseRestrict 𝒜 ψ k) h) := by
  refine ⟨pullbackNatTensorPowIso h L k, fun m x => ?_⟩
  have hx : ((x : A)) ∈ 𝒜 (k * m * d) := mem_graded_of_eq 𝒜 (by ring) x.2
  rw [veroneseRestrict_toFun,
    veroneseComp_apply 𝒜 (pullbackSections 𝒜 ψ h) k m x ⟨(x : A), hx⟩ rfl,
    Stacks.AlgebraicGeometry.ProjTriplePullback.pullbackSections_toFun,
    Stacks.AlgebraicGeometry.ProjTriplePullback.pullbackSections_toFun,
    veroneseRestrict_toFun, veroneseComp_apply 𝒜 ψ k m x ⟨(x : A), hx⟩ rfl,
    natTensorPowCongr_app_pullSection]

end Transition

end Stacks.AlgebraicGeometry.ProjVeroneseRestrict

namespace Stacks.AlgebraicGeometry.ProjTripleDegreeFunctor

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory

variable {σ : Type w} {A : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜]

/-- **The weight transition commutes with the pullback maps.** Pulling a class back and then
restricting it to the weight `kd` is restricting it and then pulling it back: the two triples
carry the merely isomorphic modules `(h^*L)^{⊗ k}` and `h^*(L^{⊗ k})`, and they are strictly
equivalent by
`Stacks.AlgebraicGeometry.ProjVeroneseRestrict.veroneseRestrict_pullbackSections`. -/
theorem Fd.veronese_pullback {Y Y' : Scheme.{u}} {d : ℕ} (k : ℕ) (h : Y' ⟶ Y)
    (ξ : Fd 𝒜 d Y) :
    Fd.veronese 𝒜 k (Fd.pullback 𝒜 h ξ) = Fd.pullback 𝒜 h (Fd.veronese 𝒜 k ξ) := by
  induction ξ using Quotient.ind with
  | _ t =>
      have := t.isInvertible
      exact (Fd.mk_eq_mk_iff 𝒜 _ _).mpr
        (ProjVeroneseRestrict.veroneseRestrict_pullbackSections 𝒜 t.psi k h)

/-- **The weight transition `F_d ⟶ F_{kd}` as a morphism of functors**, Section 27.12's diagram
of the `F_d` along divisibility. Naturality is `Fd.veronese_pullback`. -/
def Fd.veroneseNatTrans (d k : ℕ) : Fd.functor 𝒜 d ⟶ Fd.functor 𝒜 (k * d) where
  app Y := TypeCat.ofHom (Fd.veronese 𝒜 (d := d) (Y := Y.unop) k)
  naturality _ _ φ :=
    TypeCat.homEquiv.injective (funext fun ξ => Fd.veronese_pullback 𝒜 k φ.unop ξ)

/-- The component of `Fd.veroneseNatTrans 𝒜 d k` at `Y` sends `ξ` to `Fd.veronese 𝒜 k ξ`. -/
@[simp] theorem Fd.veroneseNatTrans_app (d k : ℕ) (Y : Scheme.{u}ᵒᵖ) (ξ : Fd 𝒜 d Y.unop) :
    (Fd.veroneseNatTrans 𝒜 d k).app Y ξ = Fd.veronese 𝒜 k ξ := rfl

end Stacks.AlgebraicGeometry.ProjTripleDegreeFunctor

end
