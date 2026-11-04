module

public import StacksFrontier.AlgebraicGeometry.Curves.ContractingRationalBridges.Terminal
public import StacksFrontier.AlgebraicGeometry.Curves.ContractingRationalBridges.PicardDescent
public import StacksFrontier.AlgebraicGeometry.AmpleDegreeCriterion.ComponentCriterion
public import StacksFrontier.AlgebraicGeometry.Curves.Models.StableModel.ChainDescent.BridgeComponent
public import StacksFrontier.AlgebraicGeometry.Curves.Models.StableModel.ChainDescent.ComponentLift
public import StacksFrontier.AlgebraicGeometry.Curves.Models.StableModel.ChainDescent.ComponentPullbackDegree

/-!
# Invertible modules descending along a chain of contractions of rational bridges

Let `c : X ⟶ Y` be the composite of a chain `X = X₀ → X₁ → ⋯ → Xₙ = Y` of contractions of
rational bridges of proper nodal curves over a field `k` (Tag 0E3M). An invertible `𝒪_X`-module
`N` whose degree vanishes on every irreducible component of `X` that `c` maps to a point is the
pullback of an invertible `𝒪_Y`-module: along each step the bridge is contracted by the step, hence
by `c`, so `N` has degree zero on it; a degree-zero invertible module on the genus-zero bridge is
trivial, so it descends ([Stacks, Tag 0E24]); the degrees of the descended module on the components
of the next curve are those of `N` on the components of `X` mapping onto them, divided by the
(positive) degrees of these maps.

Dually, an invertible `𝒪_Y`-module whose pullback has positive degree on every component of `X`
not mapped to a point by a surjection `c` is ample ([Stacks, Tag 0B5Y]).

## Main results

* `IsIteratedContractionOfRationalBridges.exists_pullback_iso_of_invertibleCurveDegree_eq_zero`:
  an invertible module of degree zero on every component contracted by `c` is a pullback along `c`.
* `isAmple_of_invertibleCurveDegree_pullback_pos`: an invertible module on `Y` whose pullback has
  positive degree on every component not contracted by a surjection `c` is ample.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Stacks.AlgebraicGeometry.ComponentDegrees

universe u

namespace AlgebraicGeometry

variable {k : Type u} [Field k]

/-- The descent along a chain, with the standing hypotheses as explicit arguments so that they
can be carried along the induction. -/
private theorem exists_pullback_iso_aux {X Y : Scheme.{u}}
    {fX : X ⟶ Spec (.of k)} {fY : Y ⟶ Spec (.of k)} {c : X ⟶ Y}
    (hseq : IsIteratedContractionOfRationalBridges k fX fY c)
    (hproper : IsProper fX) (hdim : topologicalKrullDim X = 1)
    (hglobal : IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ fX.appTop))
    (hnodal : letI : X.Over (Spec (.of k)) := ⟨fX⟩
      Stacks.Curves.HasAtWorstNodalSingularities k X)
    (N : X.Modules) (hNinv : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 N)
    (hN : ∀ ζ : genericPointsOne X, (∃ y : Y, ∀ x ∈ closure ({ζ.1} : Set X), c x = y) →
      @invertibleCurveDegree k _ (reducedComponent X ζ) (reducedComponentι X ζ ≫ fX)
          (@isProper_reducedComponentι_comp k _ X fX hproper ζ)
          (topologicalKrullDim_reducedComponent_le X hdim.le ζ)
          ((Scheme.Modules.pullback (reducedComponentι X ζ)).obj N)
          (@SheafOfModules.isInvertible_pullback _ _ (reducedComponentι X ζ) N hNinv) = 0) :
    ∃ (N' : Y.Modules) (_ : SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 N'),
      Nonempty ((Scheme.Modules.pullback c).obj N' ≅ N) := by
  induction hseq with
  | identity X fX => exact ⟨N, hNinv, ⟨(Scheme.Modules.pullbackId X).app N⟩⟩
  | @step X Y Z fX fY fZ c d C hC hbase hd ih =>
    let : X.Over (Spec (.of k)) := ⟨fX⟩
    have : IsProper (X ↘ Spec (.of k)) := hproper
    have : IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ (X ↘ Spec (.of k)).appTop) := hglobal
    have : IsProper fX := hproper
    have := hNinv
    obtain ⟨hCb, hc⟩ := hC hproper
    obtain ⟨g, hcg, hgp, hgdim, hgglob, -⟩ :=
      Stacks.Curves.exists_isProper_structureMorphism_and_genus_eq_contraction_bridge k X hdim
        hnodal C hCb c hc
    have hfY : fY = g := Stacks.Curves.structureMorphism_eq_of_isContractionOfRationalBridge
      hdim hnodal hc (hbase.trans hcg.symm)
    subst hfY
    have hYnodal := Stacks.Curves.hasAtWorstNodalSingularities_of_isContractionOfRationalBridge
      hdim hnodal hc hcg
    have : IsProper fY := hgp
    have : IsProper (c ≫ fY) := by rw [hbase]; infer_instance
    have : IsProper c := IsProper.of_comp c fY
    -- the contraction is surjective
    have hsurj : Function.Surjective c.base := by
      obtain ⟨-, -, -, -, -, hO, -⟩ := (IsIteratedContractionOfRationalBridges.step C hC hbase
        (.identity Y fY)).standing_target hproper hdim hglobal hnodal
      have h := ((c ≫ 𝟙 Y).surjective_of_isIso_app fun U =>
        Stacks.Curves.DualizingPullback.isIso_app_of_isIso_unitToPushforwardObjUnit
          (c ≫ 𝟙 Y) hO U).surj
      simpa using h
    -- `N` has degree zero on the bridge, hence is trivial there
    obtain ⟨ζC, hζC, ψ, hψ, hψι⟩ :=
      Stacks.Curves.exists_genericPointsOne_reducedComponent_iso_of_isRationalBridge hdim hCb
    have hdegR := hN ζC ⟨(c ≫ d).base ζC.1, fun x hx => by
      rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]
      congr 1
      have hxC : x ∈ (C.support : Set X) := hζC ▸ hx
      have hζ : ζC.1 ∈ (C.support : Set X) := hζC ▸ subset_closure rfl
      exact Stacks.Curves.subsingleton_image_contraction_bridge hc ⟨x, hxC, rfl⟩ ⟨_, hζ, rfl⟩⟩
    have := isProper_reducedComponentι_comp k fX ζC
    have := SheafOfModules.isInvertible_pullback (reducedComponentι X ζC) N
    have := SheafOfModules.isInvertible_pullback C.subschemeι N
    have := SheafOfModules.isInvertible_pullback ψ
      ((Scheme.Modules.pullback (reducedComponentι X ζC)).obj N)
    have hCdim := Stacks.Curves.topologicalKrullDim_subscheme_eq_one_of_isRationalBridge k X hdim
      hCb
    have hcongr : ∀ (f₁ f₂ : C.subscheme ⟶ Spec (.of k)) [IsProper f₁] [IsProper f₂],
        f₁ = f₂ → ∀ (h : topologicalKrullDim C.subscheme ≤ 1) (M : C.subscheme.Modules)
          [SheafOfModules.IsInvertible C.subscheme.presheaf C.subscheme.ringCatSheaf.2 M],
          invertibleCurveDegree k f₁ h M = invertibleCurveDegree k f₂ h M := by
      intro f₁ f₂ _ _ hf h M _
      subst hf
      rfl
    let eψ : (Scheme.Modules.pullback ψ).obj
          ((Scheme.Modules.pullback (reducedComponentι X ζC)).obj N) ≅
        (Scheme.Modules.pullback C.subschemeι).obj N :=
      (Scheme.Modules.pullbackComp ψ (reducedComponentι X ζC)).app N ≪≫
        (Scheme.Modules.pullbackCongr hψι).app N
    have hdegC : invertibleCurveDegree k (C.subschemeι ≫ (X ↘ Spec (.of k))) hCdim.le
        ((Scheme.Modules.pullback C.subschemeι).obj N) = 0 := by
      rw [← hcongr (ψ ≫ reducedComponentι X ζC ≫ fX) _ (by rw [← Category.assoc, hψι]; rfl),
        ← invertibleCurveDegree_eq_of_iso k _ _ eψ,
        invertibleCurveDegree_pullback_of_isIso ψ (reducedComponentι X ζC ≫ fX) hCdim.le
          (topologicalKrullDim_reducedComponent_le X hdim.le ζC)]
      exact hdegR
    obtain ⟨eC⟩ := Stacks.Curves.nonempty_pullback_subschemeι_iso_unit_of_isRationalBridge hdim C
      hCb N hdegC
    -- so `N` descends to `Y`
    have : Stacks.SheafOfModules.IsInvertible X.presheaf
        (structureSheafRing X.toRingedSpace).property N :=
      Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _ hNinv
    obtain ⟨M, hM, ⟨eM⟩⟩ :=
      Stacks.Curves.exists_pullback_iso_of_pullback_subschemeι_iso_unit_contraction_bridge hdim
        hnodal hc N eC
    have hM' : SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 M :=
      Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ _ hM
    -- the descended module has degree zero on the components contracted by `d`
    have hNM : ∀ ζ₁ : genericPointsOne Y, (∃ z : Z, ∀ y ∈ closure ({ζ₁.1} : Set Y), d y = z) →
        @invertibleCurveDegree k _ (reducedComponent Y ζ₁) (reducedComponentι Y ζ₁ ≫ fY)
          (@isProper_reducedComponentι_comp k _ Y fY hgp ζ₁)
          (topologicalKrullDim_reducedComponent_le Y hgdim.le ζ₁)
          ((Scheme.Modules.pullback (reducedComponentι Y ζ₁)).obj M)
          (@SheafOfModules.isInvertible_pullback _ _ (reducedComponentι Y ζ₁) M hM') = 0 := by
      rintro ζ₁ ⟨z, hz⟩
      obtain ⟨ζ, g', hg', hnc⟩ :=
        exists_reducedComponent_hom_of_surjective c c.isClosedMap hsurj hdim.le ζ₁
      obtain ⟨m, hm, heq⟩ := exists_pos_mul_invertibleCurveDegree_reducedComponent_pullback k fX
        fY c hbase hdim.le hgdim.le g' hg' hnc M
      have h0 := hN ζ ⟨z, fun x hx => by
        rw [Scheme.Hom.comp_apply]
        exact hz _ (mem_closure_of_reducedComponent_hom c g' hg' hx)⟩
      have := SheafOfModules.isInvertible_pullback c M
      have := SheafOfModules.isInvertible_pullback (reducedComponentι X ζ) N
      have := SheafOfModules.isInvertible_pullback (reducedComponentι X ζ)
        ((Scheme.Modules.pullback c).obj M)
      have h1 := invertibleCurveDegree_eq_of_iso k (reducedComponentι X ζ ≫ fX)
        (topologicalKrullDim_reducedComponent_le X hdim.le ζ)
        ((Scheme.Modules.pullback (reducedComponentι X ζ)).mapIso eM)
      have h2 : (m : ℤ) * _ = 0 := heq.symm.trans (h1.trans h0)
      exact (mul_eq_zero.1 h2).resolve_left hm.ne'
    obtain ⟨N', hN', ⟨e'⟩⟩ := ih hgp hgdim hgglob hYnodal M hM' hNM
    exact ⟨N', hN', ⟨((Scheme.Modules.pullbackComp c d).app N').symm ≪≫
      (Scheme.Modules.pullback c).mapIso e' ≪≫ eM⟩⟩

/-- **Descent along a chain of contractions of rational bridges.** Let `c : X ⟶ Y` be the
composite of a chain of contractions of rational bridges of a proper curve `X` over `k` of
dimension one with `H⁰(X, 𝒪_X) = k` and at-worst-nodal singularities. An invertible `𝒪_X`-module
`N` of degree zero on every one-dimensional irreducible component of `X` which `c` maps to a single
point is isomorphic to the pullback of an invertible `𝒪_Y`-module. -/
theorem IsIteratedContractionOfRationalBridges.exists_pullback_iso_of_invertibleCurveDegree_eq_zero
    {X Y : Scheme.{u}} {fX : X ⟶ Spec (.of k)} {fY : Y ⟶ Spec (.of k)} {c : X ⟶ Y}
    (hseq : IsIteratedContractionOfRationalBridges k fX fY c) [IsProper fX]
    (hdim : topologicalKrullDim X = 1)
    (hglobal : IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ fX.appTop))
    (hnodal : letI : X.Over (Spec (.of k)) := ⟨fX⟩;
      Stacks.Curves.HasAtWorstNodalSingularities k X)
    (N : X.Modules) [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 N]
    (hN : ∀ ζ : genericPointsOne X, (∃ y : Y, ∀ x ∈ closure ({ζ.1} : Set X), c x = y) →
      @invertibleCurveDegree k _ (reducedComponent X ζ) (reducedComponentι X ζ ≫ fX)
          (isProper_reducedComponentι_comp k fX ζ)
          (topologicalKrullDim_reducedComponent_le X hdim.le ζ)
          ((Scheme.Modules.pullback (reducedComponentι X ζ)).obj N)
          (SheafOfModules.isInvertible_pullback (reducedComponentι X ζ) N) = 0) :
    ∃ (N' : Y.Modules) (_ : SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 N'),
      Nonempty ((Scheme.Modules.pullback c).obj N' ≅ N) := by
  exact exists_pullback_iso_aux hseq inferInstance hdim hglobal hnodal N inferInstance hN

/-- **Ampleness from positive degrees after a surjection of curves.** Let `c : X ⟶ Y` be a
surjective morphism of proper schemes of dimension at most one over `k`, compatible with the
structure morphisms. An invertible `𝒪_Y`-module whose pullback has positive degree on every
one-dimensional irreducible component of `X` not mapped to a single point by `c` is ample. -/
theorem isAmple_of_invertibleCurveDegree_pullback_pos {X Y : Scheme.{u}}
    (fX : X ⟶ Spec (.of k)) (fY : Y ⟶ Spec (.of k)) [IsProper fX] [IsProper fY]
    (c : X ⟶ Y) (hc : c ≫ fY = fX) (hsurj : Function.Surjective c)
    (hdimX : topologicalKrullDim X ≤ 1) (hdimY : topologicalKrullDim Y ≤ 1)
    (N' : Y.Modules) [SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 N']
    (hN : ∀ ζ : genericPointsOne X, ¬ (∃ y : Y, ∀ x ∈ closure ({ζ.1} : Set X), c x = y) →
      0 < @invertibleCurveDegree k _ (reducedComponent X ζ) (reducedComponentι X ζ ≫ fX)
          (isProper_reducedComponentι_comp k fX ζ)
          (topologicalKrullDim_reducedComponent_le X hdimX ζ)
          ((Scheme.Modules.pullback (reducedComponentι X ζ)).obj
            ((Scheme.Modules.pullback c).obj N'))
          (SheafOfModules.isInvertible_pullback (reducedComponentι X ζ)
            ((Scheme.Modules.pullback c).obj N'))) :
    Scheme.Modules.IsAmple Y N' := by
  have : IsProper (c ≫ fY) := by rw [hc]; infer_instance
  have : IsProper c := IsProper.of_comp c fY
  rw [isAmple_iff_forall_invertibleCurveDegree_reducedComponent_pos k fY hdimY N']
  intro ζ₁
  obtain ⟨ζ, g, hg, hnc⟩ :=
    exists_reducedComponent_hom_of_surjective c c.isClosedMap hsurj hdimX ζ₁
  obtain ⟨d, hd, heq⟩ := exists_pos_mul_invertibleCurveDegree_reducedComponent_pullback k fX fY
    c hc hdimX hdimY g hg hnc N'
  have hpos := hN ζ (not_exists_forall_eq_of_reducedComponent_hom c g hg hnc)
  rw [heq] at hpos
  exact pos_of_mul_pos_right hpos hd.le

end AlgebraicGeometry

end
