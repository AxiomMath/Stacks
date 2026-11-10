module

public import StacksFrontier.AlgebraicGeometry.GroupScheme.AbelianVariety.Cube.AllFibres

/-!
# The theorem of the cube for abelian varieties

Let `A` be an abelian variety over an algebraically closed field `k`. An invertible module on
`A × A × A` whose pullbacks to the three faces `e × A × A`, `A × e × A`, `A × A × e` are trivial is
trivial (`Stacks.Cube.hasTheoremOfTheCube`), which is the hypothesis
`Stacks.Groupoids.HasTheoremOfTheCube A` of Tags 0BFE and 0BFF.

The proof is the cohomology-and-base-change argument of [Stacks, Tag 0BF4], specialised to the
triple self-product of `A`: every fibre `A × A × z` is trivial (`Stacks.Cube.all_good`); over every
affine chart `V` of the third factor there is a unique section of `N` restricting to the face
generators (`Stacks.Cube.exists_normSec`, `Stacks.Cube.normSec_unique`); these glue to a global
section `s` of `N`, and likewise a section `t` of `N^{⊗ -1}`; the product of `s` and `t` is a
global function on `A × A × A`, hence a constant, whose restriction to the face `e × A × A` is a
unit; so it is a unit and `N` is trivial.

## References

* [Stacks Project, Tag 0BF4](https://stacks.math.columbia.edu/tag/0BF4)
* [Stacks Project, Tag 0BF2](https://stacks.math.columbia.edu/tag/0BF2)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace Opposite
open CartesianMonoidalCategory MonoidalCategory
open Stacks.SheafOfModules.Invertible (tensorPowerModule globalSectionsMulNegOne)

universe u

namespace Stacks.Cube

open Stacks.KunnethCech Stacks.TrivialGenerator

variable {k : Type u} [Field k] {A : Over (Spec (.of k))} [GrpObj A]

section Glue

variable [IsAlgClosed k] [IsAbelianVariety k A] (N : (P A).Modules)
  [hN : AlgebraicGeometry.SheafOfModules.IsInvertible (P A).presheaf (P A).ringCatSheaf.property N]
  {ι : Type u} [Finite ι] {U : ι → A.left.Opens} {a₀ : ι}
  (ha₀ : eA (A := A) ⁻¹ᵁ U a₀ = ⊤) (hUaff : ∀ a, IsAffineOpen (U a))
  (hUcov : (⊤ : A.left.Opens) = ⨆ a, U a)
  {g₁ : Γ((Scheme.Modules.pullback (face₁ A)).obj N, ⊤)} (hg₁ : IsGen _ g₁)
  {g₂ : Γ((Scheme.Modules.pullback (face₂ A)).obj N, ⊤)} (hg₂ : IsGen _ g₂)
  (hnorm : Normalized N (g₁ := g₁) (g₂ := g₂))

omit [GrpObj A] [IsAlgClosed k] [IsAbelianVariety k A] in
/-- The image in the triple product of the open `PV (V ⊓ W)` is the intersection of the images of
`PV V` and `PV W`. -/
theorem PV_inf (V W : A.left.Opens) :
    (PV (V ⊓ W)).ι ''ᵁ ⊤ = (PV V).ι ''ᵁ ⊤ ⊓ (PV W).ι ''ᵁ ⊤ := by
  rw [Scheme.Opens.ι_image_top, Scheme.Opens.ι_image_top, Scheme.Opens.ι_image_top]
  ext x
  rfl

include ha₀ hUaff hUcov hg₁ hg₂ hnorm in
/-- **A global section restricting to the face generator**, when all fibres are trivial. -/
theorem exists_global (hall : ∀ (z : Spec (.of k) ⟶ A.left) (hzk : z ≫ A.hom = 𝟙 _), Good N z hzk) :
    ∃ s : Γ(N, ⊤), pbS (face₁ A) N ⊤ (face₁ A ⁻¹ᵁ ⊤) le_rfl s = resTop _ g₁ _ := by
  classical
  have := Fintype.ofFinite ι
  have : Smooth A.hom := Stacks.Groupoids.smooth_hom A
  have hU : ∀ (n : ℕ) (i : Fin (n + 1) → ι), IsAffineOpen (CechCochains.inter U i) :=
    fun n i => Stacks.Cech.inter_isAffineOpen A.hom U hUaff i
  have hAc := surjective_globalSections A.hom
  have hBc := surjective_globalSections (A ⊗ A).hom
  have hallV : ∀ (V : A.left.Opens) (z : Spec (.of k) ⟶ A.left) (hzk : z ≫ A.hom = 𝟙 _)
      (hzV : z ⁻¹ᵁ V = ⊤), ∃ σ₀ : Γ(fibreModule z hzk hzV N, ⊤), IsGen _ σ₀ :=
    fun V z hzk hzV => (hall z hzk).fibre hzV
  let O : ι → (P A).Opens := fun c => (PV (U c)).ι ''ᵁ ⊤
  have hsec : ∀ c, ∃ s : Γ(N, O c), NormSec N (g₁ := g₁) (g₂ := g₂) (O c) s := fun c =>
    exists_normSec hg₁ hg₂ ha₀ (chartHyp U hUaff hUcov N (hUaff c)) hU hUcov hAc hBc hnorm
      (hallV (U c))
  choose s hs using hsec
  have hinf : ∀ c d, IsAffineOpen (U c ⊓ U d) := fun c d => by
    have := hU 1 ![c, d]
    convert this using 1
    refine le_antisymm (le_iInf fun m => ?_) (le_inf (iInf_le _ 0) (iInf_le _ 1))
    fin_cases m
    · exact inf_le_left
    · exact inf_le_right
  have hcompat : ∀ c d, N.presheaf.map (homOfLE (inf_le_left : O c ⊓ O d ≤ O c)).op (s c) =
      N.presheaf.map (homOfLE (inf_le_right : O c ⊓ O d ≤ O d)).op (s d) := by
    intro c d
    have hW := hinf c d
    have hOW := PV_inf (U c) (U d)
    have hcone := ker_cone_eq_bot ha₀ hg₁ hg₂ hU hUcov hAc hBc
      (chartHyp U hUaff hUcov N hW) hnorm (hallV (U c ⊓ U d))
    have key := normSec_unique hg₁ hg₂ ha₀ (chartHyp U hUaff hUcov N hW) hcone
      (N.presheaf.map (homOfLE ((le_of_eq hOW).trans inf_le_left)).op (s c))
      (N.presheaf.map (homOfLE ((le_of_eq hOW).trans inf_le_right)).op (s d))
      ((hs c).res _) ((hs d).res _)
    have e := congrArg (N.presheaf.map (homOfLE (le_of_eq hOW.symm)).op) key
    rw [map_map_eq, map_map_eq] at e
    exact e
  have hcover : ∀ x : P A, x ∈ ⨆ c, O c := fun x => by
    have hx : r A x ∈ (⨆ a, U a) := by rw [← hUcov]; trivial
    rw [TopologicalSpace.Opens.mem_iSup] at hx ⊢
    obtain ⟨c, hc⟩ := hx
    refine ⟨c, ?_⟩
    change x ∈ (PV (U c)).ι ''ᵁ ⊤
    rw [Scheme.Opens.ι_image_top]
    exact hc
  obtain ⟨gs, hgs, -⟩ := TopCat.Sheaf.existsUnique_gluing' (⟨N.presheaf, Scheme.Modules.isSheaf N⟩ :
    TopCat.Sheaf Ab (P A)) O ⊤ (fun c => homOfLE le_top) (fun x _ => hcover x) s hcompat
  refine ⟨gs, ?_⟩
  refine sec_ext _ (fun c => face₁ A ⁻¹ᵁ O c) _ (fun c => Scheme.Hom.preimage_mono _ le_top)
    ?_ _ _ fun c => ?_
  · intro x _
    obtain ⟨c, hc⟩ := TopologicalSpace.Opens.mem_iSup.1 (hcover (face₁ A x))
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨c, hc⟩
  · rw [pbS_res, resTop_res]
    have hm := pbS_map (face₁ A) N (le_top : O c ≤ ⊤) (face₁ A ⁻¹ᵁ O c) le_rfl gs
    have := hgs c
    change N.presheaf.map (homOfLE le_top).op gs = s c at this
    rw [this] at hm
    exact hm.symm.trans (hs c).1

end Glue

/-! ### The pairing with the inverse -/

section Pairing

variable {Y X : Scheme.{u}} (p : Y ⟶ X) (L : X.Modules)
  [hL : AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property L]

/-- **The pulled-back pairing of two generators is a unit**, when the pullback is trivial. -/
theorem isUnit_pullbackMulNegOne (e : SheafOfModules.unit Y.ringCatSheaf ≅
      (Scheme.Modules.pullback p).obj L)
    {m : Γ((Scheme.Modules.pullback p).obj L, ⊤)} (hm : IsGen _ m)
    {n : Γ((Scheme.Modules.pullback p).obj (tensorPowerModule L (-1)), ⊤)} (hn : IsGen _ n) :
    IsUnit (Stacks.AlgebraicGeometry.PicardBaseChange.pullbackMulNegOne p L m n) := by
  obtain ⟨m₀, n₀, h1⟩ := Stacks.AlgebraicGeometry.PicardBaseChange.exists_pullbackMulNegOne_eq_one
    p L ⟨e.symm⟩
  have hres : ∀ {G : Y.Modules} (x : Γ(G, ⊤)), resTop G x ⊤ = x := fun {G} x => by
    change G.presheaf.map (homOfLE (le_top : (⊤ : Y.Opens) ≤ ⊤)).op x = x
    rw [show homOfLE (le_top : (⊤ : Y.Opens) ≤ ⊤) = 𝟙 _ from rfl, op_id,
      CategoryTheory.Functor.map_id]
    rfl
  have hm₀ := divGen_smul_resTop hm ⊤ m₀
  have hn₀ := divGen_smul_resTop hn ⊤ n₀
  rw [hres] at hm₀ hn₀
  rw [← Stacks.AlgebraicGeometry.PicardBaseChange.pullbackMulNegOneLinear_tmul, ← hm₀, ← hn₀,
    TensorProduct.smul_tmul_smul, map_smul,
    Stacks.AlgebraicGeometry.PicardBaseChange.pullbackMulNegOneLinear_tmul, smul_eq_mul] at h1
  rw [mul_comm] at h1
  exact IsUnit.of_mul_eq_one _ h1

/-- A section whose restriction to the face `face₁` is `resTop g` has pullback unit section `g`. -/
private theorem pullbackUnitSections_eq_of_pbS (N : (P A).Modules) {g : Γ((Scheme.Modules.pullback
    (face₁ A)).obj N, ⊤)} {s : Γ(N, ⊤)}
    (h : pbS (face₁ A) N ⊤ (face₁ A ⁻¹ᵁ ⊤) le_rfl s = resTop _ g _) :
    Stacks.AlgebraicGeometry.SectionsBaseChange.pullbackUnitSections (face₁ A) N ⊤ s = g := by
  rw [pbS_apply] at h
  refine Eq.trans ?_ (h.trans ?_)
  · change _ = ((Scheme.Modules.pullback (face₁ A)).obj N).presheaf.map (𝟙 _) _
    rw [CategoryTheory.Functor.map_id]; rfl
  · change ((Scheme.Modules.pullback (face₁ A)).obj N).presheaf.map (𝟙 _) g = g
    rw [CategoryTheory.Functor.map_id]; rfl

end Pairing

/-! ### The theorem of the cube -/

section Main

variable [IsAlgClosed k] [IsAbelianVariety k A]

/-- The pullback of an invertible module along a morphism of schemes `f : Y ⟶ X` is an invertible
module on `Y`. -/
theorem isInvertible_pullback_ag {X Y : Scheme.{u}} (f : Y ⟶ X) (L : X.Modules)
    [hL : AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property L] :
    AlgebraicGeometry.SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.property
      ((Scheme.Modules.pullback f).obj L) :=
  have := Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _ hL
  (Stacks.ProjectiveBundleQuotients.isInvertible_pullback_obj f L).toAlgebraicGeometry

/-- The inverse of a module with a trivial pullback has a trivial pullback. -/
theorem nonempty_pullback_inv_unit {X Y : Scheme.{u}} (f : Y ⟶ X) (L : X.Modules)
    [hL : AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property L]
    (e : SheafOfModules.unit Y.ringCatSheaf ≅ (Scheme.Modules.pullback f).obj L) :
    Nonempty (SheafOfModules.unit Y.ringCatSheaf ≅
      (Scheme.Modules.pullback f).obj (tensorPowerModule L (-1))) := by
  have := isInvertible_pullback_ag f L
  obtain ⟨e₁⟩ := nonempty_pullback_inv_iso f L
  obtain ⟨e₂⟩ := nonempty_inv_iso_unit _ e
  exact ⟨e₂ ≪≫ e₁.symm⟩

/-- **The theorem of the cube**, for the triple self-product of an abelian variety over an
algebraically closed field: an invertible module whose pullbacks to the three faces are trivial is
trivial. -/
theorem isTrivial_of_faces (N : (P A).Modules)
    [hN : AlgebraicGeometry.SheafOfModules.IsInvertible (P A).presheaf
      (P A).ringCatSheaf.property N]
    (e1 : SheafOfModules.unit (B A).ringCatSheaf ≅ (Scheme.Modules.pullback (face₁ A)).obj N)
    (e2 : SheafOfModules.unit (B A).ringCatSheaf ≅ (Scheme.Modules.pullback (face₂ A)).obj N)
    (e3 : SheafOfModules.unit (B A).ringCatSheaf ≅
      (Scheme.Modules.pullback (Stacks.Groupoids.cubeFace₃ A).left).obj N) :
    AlgebraicGeometry.SheafOfModules.IsTrivial (P A).presheaf (P A).ringCatSheaf.property N := by
  have : CompactSpace A.left := QuasiCompact.compactSpace_of_compactSpace A.hom
  obtain ⟨ι, _, _, U, a₀, hUaff, hUcov, ha₀⟩ := exists_cover (A := A)
  have hAc := surjective_globalSections A.hom
  have := isInvertible_inv N
  obtain ⟨g₁, hg₁⟩ := exists_isGen_of_iso e1
  obtain ⟨g₂₀, hg₂₀⟩ := exists_isGen_of_iso e2
  obtain ⟨g₂, hg₂, hnorm⟩ := exists_normalized hg₁ hg₂₀ hAc
  obtain ⟨e1'⟩ := nonempty_pullback_inv_unit (face₁ A) N e1
  obtain ⟨e2'⟩ := nonempty_pullback_inv_unit (face₂ A) N e2
  obtain ⟨g₁', hg₁'⟩ := exists_isGen_of_iso e1'
  obtain ⟨g₂₀', hg₂₀'⟩ := exists_isGen_of_iso e2'
  obtain ⟨g₂', hg₂', hnorm'⟩ := exists_normalized hg₁' hg₂₀' hAc
  have hall : ∀ (z : Spec (.of k) ⟶ A.left) (hzk : z ≫ A.hom = 𝟙 _), Good N z hzk :=
    all_good N ha₀ hUaff hUcov hg₁ hg₂ hnorm hg₁' hg₂' hnorm' e3
  obtain ⟨s, hs⟩ := exists_global N ha₀ hUaff hUcov hg₁ hg₂ hnorm hall
  obtain ⟨t, ht⟩ := exists_global (tensorPowerModule N (-1)) ha₀ hUaff hUcov hg₁' hg₂' hnorm'
    fun z hzk => good_inv N (hall z hzk)
  have hpair := Stacks.AlgebraicGeometry.PicardBaseChange.pullbackMulNegOneIso_pullbackUnitSections
    (face₁ A) N s t
  have hu := isUnit_pullbackMulNegOne (face₁ A) N e1 hg₁ hg₁'
  rw [← pullbackUnitSections_eq_of_pbS N hs, ← pullbackUnitSections_eq_of_pbS _ ht] at hu
  have e : Stacks.AlgebraicGeometry.PicardBaseChange.pullbackMulNegOne (face₁ A) N
      (Stacks.AlgebraicGeometry.SectionsBaseChange.pullbackUnitSections (face₁ A) N ⊤ s)
      (Stacks.AlgebraicGeometry.SectionsBaseChange.pullbackUnitSections (face₁ A)
        (tensorPowerModule N (-1)) ⊤ t) = (face₁ A).app ⊤ (globalSectionsMulNegOne N s t) := hpair
  rw [e] at hu
  have hne : globalSectionsMulNegOne N s t ≠ 0 := fun h0 => by
    rw [h0, map_zero] at hu
    have hd : IsDomain Γ(B A, ⊤) := inferInstance
    have : Nontrivial Γ(B A, ⊤) := hd.toNontrivial
    exact not_isUnit_zero hu
  have hfield := isField_of_universallyClosed k (Stacks.Groupoids.cubeObj A).hom
  obtain ⟨b, hb⟩ := hfield.mul_inv_cancel hne
  exact Stacks.AlgebraicGeometry.PicardBaseChange.isTrivial_of_isUnit_globalSectionsMulNegOne N s t
    (IsUnit.of_mul_eq_one b hb)

/-- **The theorem of the cube for an abelian variety over an algebraically closed field**: the
hypothesis `Stacks.Groupoids.HasTheoremOfTheCube A` of Tags 0BFE, 0BFF and 0BFG holds. This is the
"often used special case" of [Stacks, Tag 0BF4] for `X = Y = Z = A` and `x = y = z = e`. -/
theorem hasTheoremOfTheCube : Stacks.Groupoids.HasTheoremOfTheCube A := by
  intro N hN h1 h2 h3
  have : AlgebraicGeometry.SheafOfModules.IsInvertible (P A).presheaf (P A).ringCatSheaf.property
      (N : (P A).Modules) := hN.toAlgebraicGeometry
  obtain ⟨e1⟩ := h1
  obtain ⟨e2⟩ := h2
  obtain ⟨e3⟩ := h3
  exact isTrivial_of_faces N
    (((Stacks.ProjectiveBundleQuotients.pullbackIso (face₁ A)).app N) ≪≫ e1).symm
    (((Stacks.ProjectiveBundleQuotients.pullbackIso (face₂ A)).app N) ≪≫ e2).symm
    (((Stacks.ProjectiveBundleQuotients.pullbackIso
      (Stacks.Groupoids.cubeFace₃ A).left).app N) ≪≫ e3).symm

end Main

end Stacks.Cube

end
