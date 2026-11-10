module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.ChartBoxOperatorConstruction
public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.ChartRefinedOperatorAgreement

/-!
# Base change of a differential operator along a morphism of schemes

Let `a : X ⟶ S` and `b : Y ⟶ S` be morphisms of schemes, let `F`, `F'` be quasi-coherent
`𝒪_X`-modules, let `G` be a quasi-coherent `𝒪_Y`-module and let `D : F ⟶ F'` be a differential
operator of order at most `k` on `X/S`. This file glues the affine-chart base changes of `D` into
a differential operator of order at most `k` on `X ×_S Y / Y` from `F ⊠ G = pr₁^*F ⊗ pr₂^*G` to
`F' ⊠ G`, and shows that it is the unique such operator carrying the section attached to a pair of
local sections `s` of `F` and `t` of `G` to the section attached to `D s` and `t`.

## Main results

* `Stacks.FibreProductAffineChart.exists_chart_mem_le`: a point lying over an open of `X` and an
  open of `Y` lies in a chart whose two factors are contained in those opens.
* `Stacks.FibreProductAffineChart.Chart.boxOp_slice`: the chart base change of `D` on a chart
  restricts, on a chart whose range is a principal open of the range of the first and whose
  factors are contained in its factors, to the chart base change of `D` there.
* `Stacks.FibreProductAffineChart.Chart.agreeOnCover_boxOp`: the chart base changes of `D` agree
  on every open contained in two charts.
* `AlgebraicGeometry.existsUnique_globalDiffOp_externalTensorProduct`: there is a unique
  differential operator of order at most `k` on `X ×_S Y / Y` from `pr₁^*F ⊗ pr₂^*G` to
  `pr₁^*F' ⊗ pr₂^*G` carrying, for all local sections `s` of `F` and `t` of `G`, the section
  attached to `s` and `t` to the section attached to `D s` and `t`.

## References

* [Stacks Project, Tag 0G44](https://stacks.math.columbia.edu/tag/0G44)
* [Stacks Project, Tag 0G45](https://stacks.math.columbia.edu/tag/0G45)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TensorProduct TopologicalSpace
open CommRingCat
open Stacks.Tag01VSPullbackTensor

universe u

namespace AlgebraicGeometry

/-- The value of an operator on the sections over an open does not depend on which inclusion of
that open into the base is used. -/
theorem rawOp_apply_hom_eq {Z : Scheme.{u}} {M M' : Z.Modules} {U : Z.Opens}
    (R : DiffOp.RawOp M M' U) {W : Z.Opens} (i j : W ⟶ U) :
    R (Over.mk i) = R (Over.mk j) := by
  rw [Subsingleton.elim i j]

/-- **Naturality of a differential operator, in restriction form.** Applying an operator of order
at most `k` on `Z/Z'` over the opens of `U` and restricting to a smaller open is restricting and
then applying it. -/
theorem rawOp_presheaf_map {Z Z' : Scheme.{u}} (p : Z ⟶ Z') {M M' : Z.Modules} {U : Z.Opens}
    {k : ℕ} (R : DiffOp.RawOp M M' U)
    (hR : DiffOp.IsDiffOpOfOrder p.relativeStructureSheafMap k R)
    {W W' : Z.Opens} (hW : W ≤ U) (hW' : W' ≤ U) (i : W' ⟶ W) (x : Γ(M, W)) :
    R (Over.mk (homOfLE hW')) (M.presheaf.map i.op x) =
      M'.presheaf.map i.op (R (Over.mk (homOfLE hW)) x) :=
  DiffOp.RawOp.isNatural_of_isDiffOpOfOrder _ k R hR (Over.mk (homOfLE hW'))
    (Over.mk (homOfLE hW)) (Over.homMk i (Subsingleton.elim _ _)) x

/-- **Naturality of a global operator, in restriction form.** -/
theorem globalOp_presheaf_map {Z : Scheme.{u}} {M M' : Z.Modules} (E : DiffOp.GlobalOp M M')
    (hE : (E.restrict ⊤).IsNatural) {W W' : Z.Opens} (i : W' ⟶ W) (x : Γ(M, W)) :
    E (op W') (M.presheaf.map i.op x) = M'.presheaf.map i.op (E (op W) x) :=
  hE (Over.mk (homOfLE (le_top : W' ≤ ⊤))) (Over.mk (homOfLE (le_top : W ≤ ⊤)))
    (Over.homMk i (Subsingleton.elim _ _)) x

end AlgebraicGeometry

namespace Stacks.FibreProductAffineChart

open _root_.AlgebraicGeometry

/-- **A point lying over two opens lies in a chart whose factors are inside them.** For opens `U'`
of `X` and `V'` of `Y` and a point of `X ×_S Y` whose two projections lie in `U'` and in `V'`,
there is an affine chart containing the point whose first factor is contained in `U'` and whose
second factor is contained in `V'`. -/
theorem exists_chart_mem_le {X Y S : Scheme.{u}} (a : X ⟶ S) (b : Y ⟶ S) (U' : X.Opens)
    (V' : Y.Opens) (z : ↥(pullback a b)) (h₁ : (pullback.fst a b).base z ∈ U')
    (h₂ : (pullback.snd a b).base z ∈ V') :
    ∃ c : Chart a b, z ∈ c.ι.opensRange ∧ c.left ≤ U' ∧ c.right ≤ V' := by
  obtain ⟨c, hc⟩ := exists_chart_mem a b z
  have hz : z ∈ pullback.fst a b ⁻¹ᵁ c.left ⊓ pullback.snd a b ⁻¹ᵁ c.right :=
    c.opensRange_ι ▸ (show z ∈ c.ι.opensRange from hc)
  obtain ⟨f, hfU, hfz⟩ := c.isAffineOpen_left.exists_basicOpen_le
    (⟨(pullback.fst a b).base z, h₁⟩ : U') hz.1
  obtain ⟨g, hgV, hgz⟩ := c.isAffineOpen_right.exists_basicOpen_le
    (⟨(pullback.snd a b).base z, h₂⟩ : V') hz.2
  exact ⟨c.basicOpenChart f g, Chart.mem_range_ι _ z hfz hgz, hfU, hgV⟩

namespace Chart

variable {X Y S : Scheme.{u}} {a : X ⟶ S} {b : Y ⟶ S} (c : Chart a b)

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- **Two additive maps out of the sections of `F ⊠ G` over an open equal to the range of a chart
which agree on the external tensor sections are equal.** -/
theorem ext_of_externalTensorSection_of_eq (F : X.Modules) (G : Y.Modules)
    [F.IsQuasicoherent] [G.IsQuasicoherent] {A : Type*} [AddCommGroup A]
    {V : (pullback a b).Opens}
    (hV : letI := c.algebraLeft
      letI := c.algebraRight
      ((c.specIso (ofHom_algebraMap_left c) (ofHom_algebraMap_right c)).inv ≫ c.ι) ''ᵁ
        (⊤ : (Spec (.of (Γ(X, c.left) ⊗[Γ(S, c.base)] Γ(Y, c.right)))).Opens) = V)
    (h₁ : V ≤ pullback.fst a b ⁻¹ᵁ c.left) (h₂ : V ≤ pullback.snd a b ⁻¹ᵁ c.right)
    (φ ψ : Γ(externalTensorProduct a b F G, V) →+ A)
    (h : ∀ (s : Γ(F, c.left)) (t : Γ(G, c.right)),
      φ (externalTensorSection a b F G s t V h₁ h₂) =
        ψ (externalTensorSection a b F G s t V h₁ h₂))
    (w : Γ(externalTensorProduct a b F G, V)) : φ w = ψ w := by
  let := c.algebraLeft
  let := c.algebraRight
  subst hV
  exact c.ext_of_externalTensorSection (ofHom_algebraMap_left c) (ofHom_algebraMap_right c)
    F G h₁ h₂ φ ψ h w

/-- The range of a chart lies over its first factor. -/
private theorem opensRange_le_fst_left : c.ι.opensRange ≤ pullback.fst a b ⁻¹ᵁ c.left :=
  c.opensRange_ι.le.trans inf_le_left

/-- The range of a chart lies over its second factor. -/
private theorem opensRange_le_snd_right : c.ι.opensRange ≤ pullback.snd a b ⁻¹ᵁ c.right :=
  c.opensRange_ι.le.trans inf_le_right

/-- Two additive maps out of the sections of `F ⊠ G` over the range of a chart which agree on the
external tensor sections are equal. -/
private theorem ext_of_externalTensorSection_opensRange (F : X.Modules) (G : Y.Modules)
    [F.IsQuasicoherent] [G.IsQuasicoherent] {A : Type*} [AddCommGroup A]
    (φ ψ : Γ(externalTensorProduct a b F G, c.ι.opensRange) →+ A)
    (h : ∀ (s : Γ(F, c.left)) (t : Γ(G, c.right)),
      φ (externalTensorSection a b F G s t c.ι.opensRange c.opensRange_le_fst_left
          c.opensRange_le_snd_right) =
        ψ (externalTensorSection a b F G s t c.ι.opensRange c.opensRange_le_fst_left
          c.opensRange_le_snd_right))
    (w : Γ(externalTensorProduct a b F G, c.ι.opensRange)) : φ w = ψ w :=
  c.ext_of_externalTensorSection_of_eq F G
    (by rw [Scheme.Hom.image_top_eq_opensRange, Scheme.Hom.opensRange_comp_of_isIso])
    c.opensRange_le_fst_left c.opensRange_le_snd_right φ ψ h w

variable (F F' : X.Modules) (G : Y.Modules)
  [F.IsQuasicoherent] [F'.IsQuasicoherent] [G.IsQuasicoherent] (k : ℕ)
  (D : DiffOp.GlobalOp F F')
  (hD : DiffOp.IsGlobalDiffOpOfOrder a.relativeStructureSheafMap k D)

/-- **The chart base change of a differential operator on a refining chart.** Let `e` be a chart
whose range is the principal open of a section over the range of `c` and whose two factors are
contained in those of `c`. The chart base change of `D` on `c`, restricted to the opens of `e`, is
the chart base change of `D` on `e`. -/
theorem boxOp_slice (e : Chart a b) (s₀ : Γ(pullback a b, c.ι.opensRange))
    (hle : e.ι.opensRange ≤ c.ι.opensRange)
    (he : (pullback a b).basicOpen s₀ = e.ι.opensRange)
    (hleft : e.left ≤ c.left) (hright : e.right ≤ c.right) :
    (c.boxOp F F' G k D hD).1.slice (Over.mk (homOfLE hle)) =
      (e.boxOp F F' G k D hD).1 := by
  have hV₁ : e.ι.opensRange ≤ pullback.fst a b ⁻¹ᵁ c.left := hle.trans c.opensRange_le_fst_left
  have hV₂ : e.ι.opensRange ≤ pullback.snd a b ⁻¹ᵁ c.right := hle.trans c.opensRange_le_snd_right
  refine Chart.rawOp_ext_of_restriction c e s₀ hle he _ _ k
    ⟨_, DiffOp.RawOp.isDiffOpOfOrder_slice _ k _ (c.boxOp F F' G k D hD).2 _⟩
    (e.boxOp F F' G k D hD) fun x ↦ ?_
  refine Eq.trans (DFunLike.congr_fun (rawOp_apply_hom_eq (c.boxOp F F' G k D hD).1 _
    (homOfLE hle)) _) ?_
  refine c.ext_of_externalTensorSection_opensRange F G
    (((c.boxOp F F' G k D hD).1 (Over.mk (homOfLE hle))).comp
      ((externalTensorProduct a b F G).presheaf.map (homOfLE hle).op).hom)
    (((e.boxOp F F' G k D hD).1 (Over.mk (𝟙 _))).comp
      ((externalTensorProduct a b F G).presheaf.map (homOfLE hle).op).hom)
    (fun s t ↦ ?_) x
  change (c.boxOp F F' G k D hD).1 (Over.mk (homOfLE hle))
        ((externalTensorProduct a b F G).presheaf.map (homOfLE hle).op
          (externalTensorSection a b F G s t c.ι.opensRange c.opensRange_le_fst_left
            c.opensRange_le_snd_right)) =
      (e.boxOp F F' G k D hD).1 (Over.mk (𝟙 _))
        ((externalTensorProduct a b F G).presheaf.map (homOfLE hle).op
          (externalTensorSection a b F G s t c.ι.opensRange c.opensRange_le_fst_left
            c.opensRange_le_snd_right))
  rw [externalTensorSection_presheaf_map a b F G s t _ _ hV₁ hV₂ (homOfLE hle)]
  refine Eq.trans (c.apply_externalTensorSection_boxOp F F' G k D hD le_rfl le_rfl s t
    e.ι.opensRange hle hV₁ hV₂) ?_
  refine Eq.trans ?_ (DFunLike.congr_fun (rawOp_apply_hom_eq
    (e.boxOp F F' G k D hD).1 (homOfLE le_rfl) (𝟙 _)) _)
  exact (e.apply_externalTensorSection_boxOp F F' G k D hD hleft hright s t
    e.ι.opensRange le_rfl hV₁ hV₂).symm

/-- The chart base change of `D` on `c` and on a refining chart `e` as in
`Stacks.FibreProductAffineChart.Chart.boxOp_slice` agree on the sections over any open contained
in the range of `e`. -/
theorem boxOp_apply_of_le (e : Chart a b) (s₀ : Γ(pullback a b, c.ι.opensRange))
    (hle : e.ι.opensRange ≤ c.ι.opensRange)
    (he : (pullback a b).basicOpen s₀ = e.ι.opensRange)
    (hleft : e.left ≤ c.left) (hright : e.right ≤ c.right)
    {W : (pullback a b).Opens} (hWc : W ≤ c.ι.opensRange) (hWe : W ≤ e.ι.opensRange) :
    (c.boxOp F F' G k D hD).1 (Over.mk (homOfLE hWc)) =
      (e.boxOp F F' G k D hD).1 (Over.mk (homOfLE hWe)) :=
  (rawOp_apply_hom_eq (c.boxOp F F' G k D hD).1 (homOfLE hWc)
      (homOfLE hWe ≫ homOfLE hle)).trans
    (congrFun (c.boxOp_slice F F' G k D hD e s₀ hle he hleft hright) (Over.mk (homOfLE hWe)))

/-- **The chart base changes of `D` agree on an open contained in two charts.** -/
theorem boxOp_apply_eq (c₁ c₂ : Chart a b) {W : (pullback a b).Opens}
    (hi : W ≤ c₁.ι.opensRange) (hj : W ≤ c₂.ι.opensRange) :
    (c₁.boxOp F F' G k D hD).1 (Over.mk (homOfLE hi)) =
      (c₂.boxOp F F' G k D hD).1 (Over.mk (homOfLE hj)) := by
  refine AddMonoidHom.ext fun x ↦ ?_
  refine TopCat.Presheaf.IsSheaf.section_ext
    (F := (externalTensorProduct a b F' G).val.presheaf)
    (externalTensorProduct a b F' G).isSheaf fun p hp ↦ ?_
  obtain ⟨f, g, f', g', hf, hg, hpe, heq⟩ :=
    Chart.exists_basicOpenChart_mem_inter c₁ c₂ p (hi hp) (hj hp)
  have hle₁ : (c₁.basicOpenChart f g).ι.opensRange ≤ c₁.ι.opensRange :=
    c₁.opensRange_basicOpenChart_le f g
  have hle₂ : (c₁.basicOpenChart f g).ι.opensRange ≤ c₂.ι.opensRange :=
    heq.le.trans (c₂.opensRange_basicOpenChart_le f' g')
  refine ⟨W ⊓ (c₁.basicOpenChart f g).ι.opensRange, inf_le_left, ⟨hp, hpe⟩, ?_⟩
  have hsub : W ⊓ (c₁.basicOpenChart f g).ι.opensRange ≤ W := inf_le_left
  have hnat₁ := rawOp_presheaf_map (pullback.snd a b) (c₁.boxOp F F' G k D hD).1
    (c₁.boxOp F F' G k D hD).2 hi (hsub.trans hi) (homOfLE hsub) x
  have hnat₂ := rawOp_presheaf_map (pullback.snd a b) (c₂.boxOp F F' G k D hD).1
    (c₂.boxOp F F' G k D hD).2 hj (hsub.trans hj) (homOfLE hsub) x
  refine hnat₁.symm.trans (Eq.trans ?_ hnat₂)
  exact DFunLike.congr_fun
    ((c₁.boxOp_apply_of_le F F' G k D hD (c₁.basicOpenChart f g) (c₁.basicOpenSection f g)
        hle₁ (c₁.basicOpen_basicOpenSection f g) (X.basicOpen_le f) (Y.basicOpen_le g)
        (hsub.trans hi) inf_le_right).trans
      (c₂.boxOp_apply_of_le F F' G k D hD (c₁.basicOpenChart f g)
        (c₂.basicOpenSection f' g') hle₂
        ((c₂.basicOpen_basicOpenSection f' g').trans heq.symm)
        (hf.le.trans (X.basicOpen_le f')) (hg.le.trans (Y.basicOpen_le g'))
        (hsub.trans hj) inf_le_right).symm)
    ((externalTensorProduct a b F G).presheaf.map (homOfLE hsub).op x)

/-- **The chart base changes of `D` agree on the opens contained in two charts.** -/
theorem agreeOnCover_boxOp :
    DiffOp.AgreeOnCover (fun c : Chart a b ↦ (Chart.ι c).opensRange)
      (fun c ↦ (c.boxOp F F' G k D hD).1) :=
  fun c₁ c₂ _ hi hj ↦ boxOp_apply_eq F F' G k D hD c₁ c₂ hi hj

/-- **An operator restricting on every chart to the chart base change of `D` is characterised on
local sections.** It carries the section of `F ⊠ G` attached to a section `s` of `F` over `U'` and
a section `t` of `G` over `V'`, over any open `W` of `X ×_S Y` inside `pr₁⁻¹U' ⊓ pr₂⁻¹V'`, to the
section of `F' ⊠ G` attached to `D s` and `t`. -/
theorem apply_externalTensorSection_of_restrict
    (E : DiffOp.GlobalOp (externalTensorProduct a b F G) (externalTensorProduct a b F' G))
    (hEnat : (E.restrict ⊤).IsNatural)
    (hErestrict : ∀ c : Chart a b, E.restrict c.ι.opensRange = (c.boxOp F F' G k D hD).1)
    {U' : X.Opens} {V' : Y.Opens} (s : Γ(F, U')) (t : Γ(G, V')) (W : (pullback a b).Opens)
    (hW₁ : W ≤ pullback.fst a b ⁻¹ᵁ U') (hW₂ : W ≤ pullback.snd a b ⁻¹ᵁ V') :
    E (op W) (externalTensorSection a b F G s t W hW₁ hW₂) =
      externalTensorSection a b F' G (D (op U') s) t W hW₁ hW₂ := by
  refine TopCat.Presheaf.IsSheaf.section_ext
    (F := (externalTensorProduct a b F' G).val.presheaf)
    (externalTensorProduct a b F' G).isSheaf fun p hp ↦ ?_
  obtain ⟨c₀, hpc, hcU, hcV⟩ := exists_chart_mem_le a b U' V' p (hW₁ hp) (hW₂ hp)
  have hsub : W ⊓ c₀.ι.opensRange ≤ W := inf_le_left
  have hW'₁ : W ⊓ c₀.ι.opensRange ≤ pullback.fst a b ⁻¹ᵁ U' := hsub.trans hW₁
  have hW'₂ : W ⊓ c₀.ι.opensRange ≤ pullback.snd a b ⁻¹ᵁ V' := hsub.trans hW₂
  have hW'c : W ⊓ c₀.ι.opensRange ≤ c₀.ι.opensRange := inf_le_right
  refine ⟨W ⊓ c₀.ι.opensRange, hsub, ⟨hp, hpc⟩, ?_⟩
  refine (globalOp_presheaf_map E hEnat (homOfLE hsub)
      (externalTensorSection a b F G s t W hW₁ hW₂)).symm.trans ?_
  refine (congrArg (E (op (W ⊓ c₀.ι.opensRange)))
    (externalTensorSection_presheaf_map a b F G s t hW₁ hW₂ hW'₁ hW'₂ (homOfLE hsub))).trans ?_
  refine (DFunLike.congr_fun (congrFun (hErestrict c₀) (Over.mk (homOfLE hW'c))) _).trans ?_
  refine (c₀.apply_externalTensorSection_boxOp F F' G k D hD hcU hcV s t
    (W ⊓ c₀.ι.opensRange) hW'c hW'₁ hW'₂).trans ?_
  exact (externalTensorSection_presheaf_map a b F' G (D (op U') s) t hW₁ hW₂ hW'₁ hW'₂
    (homOfLE hsub)).symm

end Chart

end Stacks.FibreProductAffineChart

namespace AlgebraicGeometry

open Stacks.FibreProductAffineChart

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- **Base change of a differential operator.** Let `a : X ⟶ S` and `b : Y ⟶ S` be morphisms of
schemes, let `F`, `F'` be quasi-coherent `𝒪_X`-modules, let `G` be a quasi-coherent `𝒪_Y`-module
and let `D : F ⟶ F'` be a differential operator of order at most `k` on `X/S`. There is a unique
differential operator of order at most `k` on `X ×_S Y / Y` from `pr₁^*F ⊗ pr₂^*G` to
`pr₁^*F' ⊗ pr₂^*G` which carries, for all local sections `s` of `F` and `t` of `G`, the section
attached to `s` and `t` to the section attached to `D s` and `t`. -/
@[stacks 0G45]
theorem existsUnique_globalDiffOp_externalTensorProduct {X Y S : Scheme.{u}} (a : X ⟶ S)
    (b : Y ⟶ S) (F F' : X.Modules) (G : Y.Modules)
    [F.IsQuasicoherent] [F'.IsQuasicoherent] [G.IsQuasicoherent] (k : ℕ)
    (D : DiffOp.GlobalOp F F')
    (hD : DiffOp.IsGlobalDiffOpOfOrder a.relativeStructureSheafMap k D) :
    ∃! E : DiffOp.GlobalOp (externalTensorProduct a b F G) (externalTensorProduct a b F' G),
      DiffOp.IsGlobalDiffOpOfOrder (pullback.snd a b).relativeStructureSheafMap k E ∧
        ∀ (U' : X.Opens) (V' : Y.Opens) (s : Γ(F, U')) (t : Γ(G, V'))
          (W : (pullback a b).Opens) (hW₁ : W ≤ pullback.fst a b ⁻¹ᵁ U')
          (hW₂ : W ≤ pullback.snd a b ⁻¹ᵁ V'),
          E (op W) (externalTensorSection a b F G s t W hW₁ hW₂) =
            externalTensorSection a b F' G (D (op U') s) t W hW₁ hW₂ := by
  obtain ⟨E, ⟨hEord, hErestrict⟩, -⟩ := existsUnique_globalDiffOp_of_charts a b k
    (fun c ↦ (c.boxOp F F' G k D hD).1) (fun c ↦ (c.boxOp F F' G k D hD).2)
    (Chart.agreeOnCover_boxOp F F' G k D hD)
  have hEnat : (E.restrict ⊤).IsNatural :=
    DiffOp.RawOp.isNatural_of_isDiffOpOfOrder _ k _ (hEord ⊤)
  have hEchar : ∀ (U' : X.Opens) (V' : Y.Opens) (s : Γ(F, U')) (t : Γ(G, V'))
      (W : (pullback a b).Opens) (hW₁ : W ≤ pullback.fst a b ⁻¹ᵁ U')
      (hW₂ : W ≤ pullback.snd a b ⁻¹ᵁ V'),
      E (op W) (externalTensorSection a b F G s t W hW₁ hW₂) =
        externalTensorSection a b F' G (D (op U') s) t W hW₁ hW₂ :=
    fun _ _ s t W hW₁ hW₂ ↦ Chart.apply_externalTensorSection_of_restrict F F' G k D hD E
      hEnat hErestrict s t W hW₁ hW₂
  refine ⟨E, ⟨hEord, hEchar⟩, ?_⟩
  rintro E' ⟨hE'ord, hE'char⟩
  refine globalDiffOp_ext_of_chart_sections a b k E' E hE'ord hEord fun c₀ x ↦ ?_
  refine c₀.ext_of_externalTensorSection_opensRange F G
    (E' (op c₀.ι.opensRange)) (E (op c₀.ι.opensRange)) (fun s t ↦ ?_) x
  exact (hE'char c₀.left c₀.right s t _ _ _).trans (hEchar c₀.left c₀.right s t _ _ _).symm

end AlgebraicGeometry

end
