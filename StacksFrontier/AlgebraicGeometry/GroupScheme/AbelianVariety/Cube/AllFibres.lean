module

public import StacksFrontier.AlgebraicGeometry.GroupScheme.AbelianVariety.Cube.Fibres
public import StacksFrontier.AlgebraicGeometry.AffineExtend.Induction
public import StacksFrontier.AlgebraicGeometry.Picard.AbelMapSurjective
public import StacksFrontier.AlgebraicGeometry.Picard.HilbertSchemeCurveSupplement

/-!
# The theorem of the cube: all fibres are trivial

Let `A` be an abelian variety over an algebraically closed field and `N` an invertible module on
`(A × A) × A` whose pullbacks to the three faces are trivial. Then the pullback of `N` to every
fibre `A × A × z` over a rational point is trivial (`Stacks.Cube.all_good`). Over the identity
this is the third face; the trivial fibres propagate through every affine chart by
`Stacks.Cube.false_of_fibre` and Tag 0B40 (3), and the charts of a finite affine cover overlap
because `A` is irreducible.

## References

* [Stacks Project, Tag 0BF4](https://stacks.math.columbia.edu/tag/0BF4)
* [Stacks Project, Tag 0B40](https://stacks.math.columbia.edu/tag/0B40)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace Opposite
open CartesianMonoidalCategory MonoidalCategory
open Stacks.SheafOfModules.Invertible (tensorPowerModule)

universe u

namespace Stacks.Cube

open Stacks.KunnethCech Stacks.TrivialGenerator

variable {k : Type u} [Field k] {A : Over (Spec (.of k))} [GrpObj A]

/-- If a rational point `z` has image in `V`, then `z ⁻¹ᵁ V = ⊤`. -/
private theorem preimage_eq_top_of_mem {X : Scheme.{u}} {z : Spec (.of k) ⟶ X} {V : X.Opens}
    (h : z default ∈ V) : z ⁻¹ᵁ V = ⊤ := by
  refine top_unique fun p _ => ?_
  rw [Subsingleton.elim p default]
  exact h

/-- **A finite affine cover with the identity in the first member.** -/
theorem exists_cover [CompactSpace A.left] :
    ∃ (ι : Type u) (_ : Fintype ι) (_ : DecidableEq ι) (U : ι → A.left.Opens) (a₀ : ι),
      (∀ a, IsAffineOpen (U a)) ∧ (⊤ : A.left.Opens) = ⨆ a, U a ∧
        eA (A := A) ⁻¹ᵁ U a₀ = ⊤ := by
  classical
  obtain ⟨s, hs⟩ :=
    Stacks.AlgebraicGeometry.Tag01PFAffineExtend.exists_finset_affineOpens_iSup_eq_top (X := A.left)
  obtain ⟨_, ⟨W₀, hW₀, rfl⟩, he₀, -⟩ := A.left.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (eA (A := A) (default : Spec (.of k)))) isOpen_univ
  let t : Finset A.left.affineOpens := insert ⟨W₀, hW₀⟩ s
  refine ⟨t, inferInstance, inferInstance, fun i => (i.1 : A.left.Opens),
    ⟨⟨W₀, hW₀⟩, Finset.mem_insert_self _ _⟩, fun i => i.1.2, ?_, ?_⟩
  · refine (top_unique fun x _ => ?_).symm
    have hx : x ∈ (⨆ V ∈ s, (V : A.left.Opens)) := by rw [hs]; trivial
    simp only [TopologicalSpace.Opens.mem_iSup] at hx ⊢
    obtain ⟨V, hV, hxV⟩ := hx
    exact ⟨⟨V, Finset.mem_insert_of_mem hV⟩, hxV⟩
  · exact preimage_eq_top_of_mem he₀

/-! ### Trivial fibres -/

variable (N : (P A).Modules)

/-- The fibre of `N` over the rational point `z` is trivial. -/
def Good (z : Spec (.of k) ⟶ A.left) (hzk : z ≫ A.hom = 𝟙 _) : Prop :=
  ∃ σ : Γ((Scheme.Modules.pullback (jz z hzk)).obj N, ⊤), IsGen _ σ

variable {N}

omit [GrpObj A] in
/-- If the fibre of `N` over `z` is trivial, so is the fibre module `fibreModule z hzk hzV N`
over any open `V` with `z ⁻¹ᵁ V = ⊤`. -/
theorem Good.fibre {z : Spec (.of k) ⟶ A.left} {hzk : z ≫ A.hom = 𝟙 _} (h : Good N z hzk)
    {V : A.left.Opens} (hzV : z ⁻¹ᵁ V = ⊤) :
    ∃ σ₀ : Γ(fibreModule z hzk hzV N, ⊤), IsGen _ σ₀ := by
  obtain ⟨σ, hσ⟩ := h
  exact ⟨_, isGen_app_iso hσ (fibreIso z hzk hzV N).symm⟩

/-- An element of `Γ(L, ⊤)` whose image under an isomorphism `L ≅ M` is zero is zero. -/
private theorem eq_zero_of_app_hom_eq_zero {X : Scheme.{u}} {L M : X.Modules} (e : L ≅ M)
    {s : Γ(L, ⊤)} (h : Scheme.Modules.Hom.app e.hom ⊤ s = 0) : s = 0 := by
  have h2 := congrArg (Scheme.Modules.Hom.app e.inv ⊤) h
  rw [map_zero] at h2
  refine Eq.trans ?_ h2
  show s = (Scheme.Modules.Hom.app e.hom ⊤ ≫ Scheme.Modules.Hom.app e.inv ⊤) s
  rw [← Scheme.Modules.Hom.comp_app, Iso.hom_inv_id]
  rfl

omit [GrpObj A] in
/-- If the pullback of `N` along `jz z hzk` has no nonzero global sections, neither does
`fibreModule z hzk hzV N`. -/
theorem noSec_fibre {z : Spec (.of k) ⟶ A.left} {hzk : z ≫ A.hom = 𝟙 _}
    (h : ∀ s : Γ((Scheme.Modules.pullback (jz z hzk)).obj N, ⊤), s = 0)
    {V : A.left.Opens} (hzV : z ⁻¹ᵁ V = ⊤) (s : Γ(fibreModule z hzk hzV N, ⊤)) : s = 0 := by
  exact eq_zero_of_app_hom_eq_zero (fibreIso z hzk hzV N) (h _)

/-- If the pullback of `N` along the third face is trivial, then the fibre of `N` over the identity
`eA` is trivial. -/
theorem good_eA (e3 : SheafOfModules.unit (B A).ringCatSheaf ≅
    (Scheme.Modules.pullback (Stacks.Groupoids.cubeFace₃ A).left).obj N) :
    Good N eA eA_hom :=
  exists_isGen_of_iso (e3 ≪≫ (Scheme.Modules.pullbackCongr jz_eA.symm).app N)

/-! ### Tag 0B40 (3) on a fibre -/

section Trichotomy

variable [IsAbelianVariety k A] (N)
  [hN : AlgebraicGeometry.SheafOfModules.IsInvertible (P A).presheaf (P A).ringCatSheaf.property N]

omit [GrpObj A] [IsAbelianVariety k A] in
/-- The pullback of an invertible module `N` along `jz z hzk` is invertible. -/
theorem isInvertible_jz (z : Spec (.of k) ⟶ A.left) (hzk : z ≫ A.hom = 𝟙 _) :
    AlgebraicGeometry.SheafOfModules.IsInvertible (B A).presheaf (B A).ringCatSheaf.property
      ((Scheme.Modules.pullback (jz z hzk)).obj N) :=
  have := Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _ hN
  (Stacks.ProjectiveBundleQuotients.isInvertible_pullback_obj (jz z hzk) N).toAlgebraicGeometry

/-- The section `Scheme.Modules.sectionsTopEquiv L x` evaluates to `x` on `⊤`. -/
theorem sections_eval_top {X : Scheme.{u}} (L : X.Modules) (x : Γ(L, ⊤)) :
    (Scheme.Modules.sectionsTopEquiv L x).eval (op ⊤) = x := by
  show (Scheme.Modules.sectionsTopEquiv L x).val (op ⊤) = x
  rw [Scheme.Modules.sectionsTopEquiv_val]
  show L.presheaf.map (𝟙 _) x = x
  rw [CategoryTheory.Functor.map_id]
  rfl

/-- **A fibre is trivial, or the fibre of `N` or of `N^{⊗ -1}` has no sections**, by Tag 0B40 (3)
on the integral proper scheme `A × A`. -/
theorem fibre_trichotomy (z : Spec (.of k) ⟶ A.left) (hzk : z ≫ A.hom = 𝟙 _) :
    Good N z hzk ∨ (∀ s : Γ((Scheme.Modules.pullback (jz z hzk)).obj N, ⊤), s = 0) ∨
      (∀ s : Γ((Scheme.Modules.pullback (jz z hzk)).obj (tensorPowerModule N (-1)), ⊤), s = 0) := by
  by_contra hcon
  simp only [not_or, not_forall] at hcon
  obtain ⟨hng, ⟨s, hs⟩, ⟨t, ht⟩⟩ := hcon
  have := isInvertible_jz N z hzk
  obtain ⟨e⟩ := nonempty_pullback_inv_iso (jz z hzk) N
  have ht' : Scheme.Modules.Hom.app e.hom ⊤ t ≠ 0 := fun h0 => ht (eq_zero_of_app_hom_eq_zero e h0)
  obtain ⟨e'⟩ := AlgebraicGeometry.isTrivial_of_eval_top_ne_zero_of_inverse k (A ⊗ A).hom
    ((Scheme.Modules.pullback (jz z hzk)).obj N)
    (Scheme.Modules.sectionsTopEquiv _ s) (by rwa [sections_eval_top])
    (Scheme.Modules.sectionsTopEquiv _ (Scheme.Modules.Hom.app e.hom ⊤ t))
    (by rwa [sections_eval_top])
  exact hng (exists_isGen_of_iso e'.symm)

omit [GrpObj A] [IsAbelianVariety k A] in
/-- If the fibre of `N` over `z` is trivial, so is the fibre of `N^{⊗ -1}` over `z`. -/
theorem good_inv {z : Spec (.of k) ⟶ A.left} {hzk : z ≫ A.hom = 𝟙 _} (h : Good N z hzk) :
    Good (tensorPowerModule N (-1)) z hzk := by
  have := isInvertible_jz N z hzk
  obtain ⟨σ, hσ⟩ := h
  obtain ⟨e, -⟩ := exists_iso_of_isGen hσ
  obtain ⟨e₁⟩ := nonempty_pullback_inv_iso (jz z hzk) N
  obtain ⟨e₂⟩ := nonempty_inv_iso_unit _ e
  exact exists_isGen_of_iso (e₂ ≪≫ e₁.symm)

end Trichotomy

/-! ### Propagation -/

section Propagation

variable [IsAlgClosed k] [IsAbelianVariety k A] (N)
  [hN : AlgebraicGeometry.SheafOfModules.IsInvertible (P A).presheaf (P A).ringCatSheaf.property N]
  {ι : Type u} [Fintype ι] [DecidableEq ι] {U : ι → A.left.Opens} {a₀ : ι}
  (ha₀ : eA (A := A) ⁻¹ᵁ U a₀ = ⊤) (hUaff : ∀ a, IsAffineOpen (U a))
  (hUcov : (⊤ : A.left.Opens) = ⨆ a, U a)
  {g₁ : Γ((Scheme.Modules.pullback (face₁ A)).obj N, ⊤)} (hg₁ : IsGen _ g₁)
  {g₂ : Γ((Scheme.Modules.pullback (face₂ A)).obj N, ⊤)} (hg₂ : IsGen _ g₂)
  (hnorm : Normalized N (g₁ := g₁) (g₂ := g₂))
  {g₁' : Γ((Scheme.Modules.pullback (face₁ A)).obj (tensorPowerModule N (-1)), ⊤)}
  (hg₁' : IsGen _ g₁')
  {g₂' : Γ((Scheme.Modules.pullback (face₂ A)).obj (tensorPowerModule N (-1)), ⊤)}
  (hg₂' : IsGen _ g₂')
  (hnorm' : Normalized (tensorPowerModule N (-1)) (g₁ := g₁') (g₂ := g₂'))

omit [GrpObj A] [IsAlgClosed k] [IsAbelianVariety k A] in
/-- The tensor power `N^{⊗ -1}` of an invertible module `N` is invertible. -/
theorem isInvertible_inv :
    AlgebraicGeometry.SheafOfModules.IsInvertible (P A).presheaf (P A).ringCatSheaf.property
      (tensorPowerModule N (-1)) :=
  have := Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _ hN
  (Stacks.SheafOfModules.Invertible.tensorPower_isInvertible (P A).presheaf
    (P A).ringCatSheaf.property N (-1)).toAlgebraicGeometry

omit [GrpObj A] [IsAlgClosed k] [IsAbelianVariety k A] in
/-- If `z ⁻¹ᵁ V = ⊤`, then the image of the rational point `z` lies in `V`. -/
theorem mem_of_preimage_top {z : Spec (.of k) ⟶ A.left} {V : A.left.Opens} (hzV : z ⁻¹ᵁ V = ⊤) :
    z default ∈ V := by
  have : (default : Spec (.of k)) ∈ z ⁻¹ᵁ V := by rw [hzV]; trivial
  exact this

include ha₀ hUaff hUcov hg₁ hg₂ hnorm hg₁' hg₂' hnorm' in
/-- **Trivial fibres propagate through a chart.** -/
theorem good_of_chart {V : A.left.Opens} (hV : IsAffineOpen V)
    (z' : Spec (.of k) ⟶ A.left) (hzk' : z' ≫ A.hom = 𝟙 _) (hzV' : z' ⁻¹ᵁ V = ⊤)
    (hz' : Good N z' hzk')
    (z : Spec (.of k) ⟶ A.left) (hzk : z ≫ A.hom = 𝟙 _) (hzV : z ⁻¹ᵁ V = ⊤) :
    Good N z hzk := by
  have : Smooth A.hom := Stacks.Groupoids.smooth_hom A
  have hU : ∀ (n : ℕ) (i : Fin (n + 1) → ι), IsAffineOpen (CechCochains.inter U i) :=
    fun n i => Stacks.Cech.inter_isAffineOpen A.hom U hUaff i
  have hAc := surjective_globalSections A.hom
  have hBc := surjective_globalSections (A ⊗ A).hom
  have : Nonempty V := ⟨⟨z default, mem_of_preimage_top hzV⟩⟩
  rcases fibre_trichotomy N z hzk with h | h0 | h0
  · exact h
  · exfalso
    obtain ⟨σ₀, hσ₀⟩ := hz'.fibre hzV'
    exact false_of_fibre hg₁ hg₂ hV U ha₀ (chartHyp U hUaff hUcov N hV) hU hUcov hAc hBc hnorm
      z' hzk' hzV' hσ₀ z hzk hzV (noSec_fibre h0 hzV)
  · exfalso
    have := isInvertible_inv N
    obtain ⟨σ₀, hσ₀⟩ := (good_inv N hz').fibre hzV'
    exact false_of_fibre hg₁' hg₂' hV U ha₀ (chartHyp U hUaff hUcov (tensorPowerModule N (-1)) hV)
      hU hUcov hAc hBc hnorm' z' hzk' hzV' hσ₀ z hzk hzV (noSec_fibre h0 hzV)

include ha₀ hUaff hUcov hg₁ hg₂ hnorm hg₁' hg₂' hnorm' in
/-- **All fibres are trivial.** -/
theorem all_good (e3 : SheafOfModules.unit (B A).ringCatSheaf ≅
      (Scheme.Modules.pullback (Stacks.Groupoids.cubeFace₃ A).left).obj N)
    (z : Spec (.of k) ⟶ A.left) (hzk : z ≫ A.hom = 𝟙 _) : Good N z hzk := by
  have : Smooth A.hom := Stacks.Groupoids.smooth_hom A
  have hz : z default ∈ (⨆ a, U a) := by rw [← hUcov]; trivial
  obtain ⟨c, hc⟩ := TopologicalSpace.Opens.mem_iSup.mp hz
  have hzc : z ⁻¹ᵁ U c = ⊤ := preimage_eq_top_of_mem hc
  let W := U c ⊓ U a₀
  have hW : (W : Set A.left).Nonempty :=
    nonempty_preirreducible_inter (U c).isOpen (U a₀).isOpen ⟨_, hc⟩ ⟨_, mem_of_preimage_top ha₀⟩
  have : Nonempty W := ⟨⟨hW.some, hW.some_mem⟩⟩
  obtain ⟨σ, hσ⟩ := Stacks.AbelMap.exists_section_of_isSepClosed (W.ι ≫ A.hom)
  let t := σ ≫ W.ι
  have htk : t ≫ A.hom = 𝟙 _ := by simp only [t, Category.assoc, hσ]
  have hWle : ∀ O : A.left.Opens, W ≤ O → t ⁻¹ᵁ O = ⊤ := fun O hO =>
    preimage_eq_top_of_mem (hO (σ default).2)
  exact good_of_chart N ha₀ hUaff hUcov hg₁ hg₂ hnorm hg₁' hg₂' hnorm' (hUaff c) t htk
    (hWle _ inf_le_left)
    (good_of_chart N ha₀ hUaff hUcov hg₁ hg₂ hnorm hg₁' hg₂' hnorm' (hUaff a₀) eA eA_hom ha₀
      (good_eA e3) t htk (hWle _ inf_le_right)) z hzk hzc

end Propagation

end Stacks.Cube

end
