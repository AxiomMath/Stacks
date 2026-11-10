module

public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.BundleBaseChangeDegreeOne
public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.SymGenSections
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundle.EpiClosedImmersionTwist
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundle.TautologicalDatumBaseChange
public import StacksFrontier.AlgebraicGeometry.RelativeProjMapDomain.Open
public import StacksFrontier.AlgebraicGeometry.SymTwistChart.DegreeOne

/-!
# The closed immersion of a quotient commutes with base change

Let `g : X' ⟶ X` be a morphism of schemes, `u : F ⟶ G` an epimorphism of quasi-coherent
`𝒪_X`-modules and `u' : F' ⟶ G'` an epimorphism of quasi-coherent `𝒪_{X'}`-modules, with
identifications `F' ≅ g^*F` and `G' ≅ g^*G` under which `u'` is `g^*u`. Then the square

```
𝐏(G') ⟶ 𝐏(F')
  |         |
𝐏(G)  ⟶ 𝐏(F)
```

formed by the two closed immersions `Stacks.RelativeProj.projectiveBundleMapOfEpi` and the two
base-change morphisms `Stacks.RelativeProj.projectiveBundleBaseChange` commutes.

On the `SheafGradedAlgebra` substrate both composites are, over the chart of an affine open
`W' ⊆ g⁻¹W` with `W` affine, `Proj` of a graded ring map `Γ(W, Sym F) ⟶ Γ(W', Sym G')`; the two
ring maps agree on the structure map and on the degree-one sections, which generate
(`Stacks.SymTwistChart.gradedRingHom_ext_degree_one`), and such charts cover.

## Main results

* `Stacks.AlgebraicGeometry.RelativeProj.RelativeProjData.hom_ext_of_cover`: a morphism out of a
  relative homogeneous spectrum is determined on the charts over a covering family of affine
  opens of the base.
* `Stacks.ProjectiveBundle.baseChangeGradedHom_strHom`: the base-change homomorphism of graded
  rings of sections is the pullback of functions in degree zero.
* `Stacks.RelativeProj.sectionHom_comp_baseChangeGradedHom`: the square of graded rings of
  sections.
* `Stacks.RelativeProj.symGradedMapOfEpi_comp_baseChangeHom`: the square on the substrate.
* `Stacks.RelativeProj.projectiveBundleMapOfEpi_comp_projectiveBundleBaseChange`: **the square on
  `Stacks.RelativeProj.projectiveBundle`.**

## References

* [Stacks Project, Tag 01O3](https://stacks.math.columbia.edu/tag/01O3)
* [Stacks Project, Tag 0ERW](https://stacks.math.columbia.edu/tag/0ERW)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite
open Stacks.SymGraded

universe u

namespace Stacks.AlgebraicGeometry.RelativeProj.RelativeProjData

open Stacks.AlgebraicGeometry.RelativeProjBridge

variable {S : Scheme.{u}} {A : SheafGradedAlgebra S}

/-- **A morphism out of a relative homogeneous spectrum is determined on charts**: two morphisms
which agree on the charts over a family of affine opens covering the base are equal. The charts
are open immersions whose images are the inverse images of the affine opens. -/
theorem hom_ext_of_cover (P : RelativeProjData A) {Y : Scheme.{u}} (f₁ f₂ : P.scheme ⟶ Y)
    {ι : Type u} (U : ι → S.Opens) (hU : ∀ i, IsAffineOpen (U i))
    (hcov : ∀ s : S, ∃ i, s ∈ U i)
    (h : ∀ i, P.chart (U i) (hU i) ≫ f₁ = P.chart (U i) (hU i) ≫ f₂) : f₁ = f₂ := by
  refine Scheme.Cover.hom_ext
    (Scheme.Cover.mkOfCovers ι (fun i => AlgebraicGeometry.Proj (A.grading (U i)))
      (fun i => P.chart (U i) (hU i)) (fun x => ?_)
      (fun i => Stacks.AlgebraicGeometry.RelativeProjTwistGlue.isOpenImmersion_chart P (U i)
        (hU i))) f₁ f₂ h
  obtain ⟨i, hi⟩ := hcov (P.toBase x)
  have hx : x ∈ (P.chart (U i) (hU i)) ''ᵁ ⊤ := by
    rw [Stacks.AlgebraicGeometry.RelativeProjTwistGlue.chart_image_top P (U i) (hU i)]
    exact hi
  rw [Scheme.Hom.image_top_eq_opensRange] at hx
  obtain ⟨y, hy⟩ := hx
  exact ⟨i, y, hy⟩

end Stacks.AlgebraicGeometry.RelativeProj.RelativeProjData

namespace Stacks.ProjectiveBundle

variable {X X' : Scheme.{u}} (g : X' ⟶ X) (E : X.Modules) [E.IsQuasicoherent]
  (E' : X'.Modules) [E'.IsQuasicoherent] (hE : E' ≅ (Scheme.Modules.pullback g).obj E)

/-- **The base-change homomorphism of graded rings of sections in degree zero** is the pullback
of functions `Γ(X, W) ⟶ Γ(X', W')`. -/
theorem baseChangeGradedHom_strHom (W : X.AffineZariskiSite) (W' : X'.AffineZariskiSite)
    (h : W'.toOpens ≤ g ⁻¹ᵁ W.toOpens) (r : Γ(X, W.toOpens)) :
    baseChangeGradedHom g E (isQuasicoherentPieces_of_isQuasicoherent E) E'
        (isQuasicoherentPieces_of_isQuasicoherent E') hE W W' h
        ((schemeSheafGradedAlgebra E (isQuasicoherentPieces_of_isQuasicoherent E)).strHom
          W.toOpens r) =
      (schemeSheafGradedAlgebra E' (isQuasicoherentPieces_of_isQuasicoherent E')).strHom
        W'.toOpens ((g.appLE W.toOpens W'.toOpens h).hom r) := by
  change situationSectionRingHomInv E' (isQuasicoherentPieces_of_isQuasicoherent E') W'.toOpens
      (Stacks.RelativeProj.Situation.sectionRingBaseChange (s := symSituation E)
        (s' := symSituation E') g (Stacks.RelativeProj.symmetricSituationPullbackHom g E E' hE)
        W.toOpens W'.toOpens h (situationSectionRingHom E
          (isQuasicoherentPieces_of_isQuasicoherent E) W.toOpens
          ((situationSheafGradedAlgebra E (isQuasicoherentPieces_of_isQuasicoherent E)).strHom
            W.toOpens r))) = _
  rw [situationSectionRingHom_strHom, Stacks.RelativeProj.Situation.sectionRingBaseChange_baseMap,
    ← situationSectionRingHom_strHom E' (isQuasicoherentPieces_of_isQuasicoherent E') W'.toOpens,
    situationSectionRingHomInv_hom]
  rfl

/-- The base-change homomorphism of graded rings of sections
`Stacks.ProjectiveBundle.baseChangeGradedHom`, with its source and target written at the
`Stacks.SymGraded.schemeSheafGradedAlgebra` spelling of `Sym`, which is the one `Sym` of a
morphism of modules is stated at. -/
def schemeBaseChangeGradedHom (W : X.AffineZariskiSite) (W' : X'.AffineZariskiSite)
    (h : W'.toOpens ≤ g ⁻¹ᵁ W.toOpens) :
    (schemeSheafGradedAlgebra E (isQuasicoherentPieces_of_isQuasicoherent E)).grading
        W.toOpens →+*ᵍ
      (schemeSheafGradedAlgebra E' (isQuasicoherentPieces_of_isQuasicoherent E')).grading
        W'.toOpens :=
  baseChangeGradedHom g E (isQuasicoherentPieces_of_isQuasicoherent E) E'
    (isQuasicoherentPieces_of_isQuasicoherent E') hE W W' h

/-- The irrelevant ideal of `Γ(W', Sym E')` is contained in the image of the irrelevant ideal of
`Γ(W, Sym E)` under `schemeBaseChangeGradedHom`, for affine opens `W' ⊆ g⁻¹W`. -/
theorem irrelevant_le_schemeBaseChangeGradedHom (W : X.AffineZariskiSite)
    (W' : X'.AffineZariskiSite) (h : W'.toOpens ≤ g ⁻¹ᵁ W.toOpens) :
    HomogeneousIdeal.irrelevant ((schemeSheafGradedAlgebra E'
        (isQuasicoherentPieces_of_isQuasicoherent E')).grading W'.toOpens) ≤
      (HomogeneousIdeal.irrelevant ((schemeSheafGradedAlgebra E
        (isQuasicoherentPieces_of_isQuasicoherent E)).grading W.toOpens)).map
          (schemeBaseChangeGradedHom g E E' hE W W' h) :=
  irrelevant_le_baseChangeGradedHom g E _ E' _ hE W W' h

/-- The base-change morphism on charts, at the `schemeSheafGradedAlgebra` spelling. -/
theorem chart_baseChangeHom_scheme (W : X.AffineZariskiSite) (W' : X'.AffineZariskiSite)
    (h : W'.toOpens ≤ g ⁻¹ᵁ W.toOpens) :
    (Stacks.AlgebraicGeometry.RelativeProj.relativeProj (schemeSheafGradedAlgebra E'
        (isQuasicoherentPieces_of_isQuasicoherent E'))).chart W'.toOpens W'.2 ≫
        baseChangeHom g E (isQuasicoherentPieces_of_isQuasicoherent E) E'
          (isQuasicoherentPieces_of_isQuasicoherent E') hE =
      AlgebraicGeometry.Proj.map (schemeBaseChangeGradedHom g E E' hE W W' h)
          (irrelevant_le_schemeBaseChangeGradedHom g E E' hE W W' h) ≫
        (Stacks.AlgebraicGeometry.RelativeProj.relativeProj (schemeSheafGradedAlgebra E
          (isQuasicoherentPieces_of_isQuasicoherent E))).chart W.toOpens W.2 :=
  chart_baseChangeHom g E _ E' _ hE W W' h

/-- In degree zero, `schemeBaseChangeGradedHom` is the pullback of functions
`Γ(X, W) ⟶ Γ(X', W')`. -/
theorem schemeBaseChangeGradedHom_strHom (W : X.AffineZariskiSite) (W' : X'.AffineZariskiSite)
    (h : W'.toOpens ≤ g ⁻¹ᵁ W.toOpens) (r : Γ(X, W.toOpens)) :
    schemeBaseChangeGradedHom g E E' hE W W' h
        ((schemeSheafGradedAlgebra E (isQuasicoherentPieces_of_isQuasicoherent E)).strHom
          W.toOpens r) =
      (schemeSheafGradedAlgebra E' (isQuasicoherentPieces_of_isQuasicoherent E')).strHom
        W'.toOpens ((g.appLE W.toOpens W'.toOpens h).hom r) :=
  baseChangeGradedHom_strHom g E E' hE W W' h r

/-- `schemeBaseChangeGradedHom` carries the degree-one element of `Γ(W, Sym E)` attached to
`x ∈ Γ(W, E)` to the degree-one element of `Γ(W', Sym E')` attached to the restriction to `W'` of
the transpose of `hE.inv` at `x`. -/
theorem schemeBaseChangeGradedHom_of_one (W : X.AffineZariskiSite) (W' : X'.AffineZariskiSite)
    (h : W'.toOpens ≤ g ⁻¹ᵁ W.toOpens) (x : Γ(E, W.toOpens)) :
    schemeBaseChangeGradedHom g E E' hE W W' h
        (DirectSum.of ((schemeSheafGradedAlgebra E
          (isQuasicoherentPieces_of_isQuasicoherent E)).sectionPieces W.toOpens) 1
          ((Scheme.Modules.symmetricAlgebraGen X E).val.app (op W.toOpens) x)) =
      DirectSum.of ((schemeSheafGradedAlgebra E'
          (isQuasicoherentPieces_of_isQuasicoherent E')).sectionPieces W'.toOpens) 1
        ((Scheme.Modules.symmetricAlgebraGen X' E').val.app (op W'.toOpens)
          (E'.val.map (homOfLE h).op
            (((Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv _ _ hE.inv).val.app
              (op W.toOpens) x))) :=
  baseChangeGradedHom_of_one g E E' hE _ _ W W' h x

end Stacks.ProjectiveBundle

namespace Stacks.RelativeProj

variable {X X' : Scheme.{u}} (g : X' ⟶ X) {F G : X.Modules} [F.IsQuasicoherent]
  [G.IsQuasicoherent] (u : F ⟶ G) [Epi u] {F' G' : X'.Modules} [F'.IsQuasicoherent]
  [G'.IsQuasicoherent] (u' : F' ⟶ G') [Epi u'] (eF : F' ≅ (Scheme.Modules.pullback g).obj F)
  (eG : G' ≅ (Scheme.Modules.pullback g).obj G)
  (hu : u' ≫ eG.hom = eF.hom ≫ (Scheme.Modules.pullback g).map u)

omit [F.IsQuasicoherent] [G.IsQuasicoherent] [Epi u] [F'.IsQuasicoherent] [G'.IsQuasicoherent]
  [Epi u'] in
include hu in
/-- The compatibility of `u` and `u'` read on sections through the adjunction: the transposes of
`eF⁻¹` and `eG⁻¹` intertwine `u` and `u'`. -/
theorem homEquiv_inv_app_comp (W : X.Opens) (x : Γ(F, W)) :
    u'.val.app (op (g ⁻¹ᵁ W))
        (((Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv _ _ eF.inv).val.app
          (op W) x) =
      ((Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv _ _ eG.inv).val.app (op W)
        (u.val.app (op W) x) := by
  have hinv : eF.inv ≫ u' = (Scheme.Modules.pullback g).map u ≫ eG.inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, ← hu, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]
  have h₁ := (Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv_naturality_right eF.inv u'
  have h₂ := (Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv_naturality_left u eG.inv
  rw [hinv, h₂] at h₁
  exact (congrArg (fun φ => φ.val.app (op W) x) h₁).symm

omit [Epi u] [Epi u'] in
include hu in
/-- **The square of graded rings of sections**: over affine opens `W' ⊆ g⁻¹W`, `Sym(u')` after
the base change of `F` is the base change of `G` after `Sym(u)`, as maps
`Γ(W, Sym F) ⟶ Γ(W', Sym G')`. Both agree on the structure map and on the degree-one sections. -/
theorem sectionHom_comp_baseChangeGradedHom (W : X.AffineZariskiSite)
    (W' : X'.AffineZariskiSite) (h : W'.toOpens ≤ g ⁻¹ᵁ W.toOpens) :
    ((schemeSheafGradedAlgebraHom u' (isQuasicoherentPieces_of_isQuasicoherent F')
        (isQuasicoherentPieces_of_isQuasicoherent G')).sectionHom W'.toOpens).comp
      (Stacks.ProjectiveBundle.schemeBaseChangeGradedHom g F F' eF W W' h) =
    (Stacks.ProjectiveBundle.schemeBaseChangeGradedHom g G G' eG W W' h).comp
      ((schemeSheafGradedAlgebraHom u (isQuasicoherentPieces_of_isQuasicoherent F)
        (isQuasicoherentPieces_of_isQuasicoherent G)).sectionHom W.toOpens) := by
  refine Stacks.SymTwistChart.gradedRingHom_ext_degree_one F
    (isQuasicoherentPieces_of_isQuasicoherent F) (show IsAffineOpen W.toOpens from W.2)
    (fun r => ?_) (fun m => ?_)
  · rw [GradedRingHom.comp_apply, GradedRingHom.comp_apply,
      Stacks.ProjectiveBundle.schemeBaseChangeGradedHom_strHom,
      Stacks.AlgebraicGeometry.ProjBundleSurjection.sectionHom_strHom,
      Stacks.AlgebraicGeometry.ProjBundleSurjection.sectionHom_strHom,
      Stacks.ProjectiveBundle.schemeBaseChangeGradedHom_strHom]
  · have hm : Stacks.SymTwistChart.symOne F (isQuasicoherentPieces_of_isQuasicoherent F) m =
        (Scheme.Modules.symmetricAlgebraGen X F).val.app (op W.toOpens) m :=
      (Stacks.SymGraded.AffinePieces.symmetricAlgebraGen_app_eq F W.toOpens m).symm
    rw [hm, GradedRingHom.comp_apply, GradedRingHom.comp_apply]
    refine (congrArg _
      (Stacks.ProjectiveBundle.schemeBaseChangeGradedHom_of_one g F F' eF W W' h m)).trans ?_
    refine (Stacks.Chow.GenuineChern.sectionHom_of_symmetricAlgebraGen u'
      (isQuasicoherentPieces_of_isQuasicoherent F') (isQuasicoherentPieces_of_isQuasicoherent G')
      W'.toOpens _).trans ?_
    refine Eq.trans ?_ ((congrArg _ (Stacks.Chow.GenuineChern.sectionHom_of_symmetricAlgebraGen u
      (isQuasicoherentPieces_of_isQuasicoherent F) (isQuasicoherentPieces_of_isQuasicoherent G)
      W.toOpens m)).trans
        (Stacks.ProjectiveBundle.schemeBaseChangeGradedHom_of_one g G G' eG W W' h _)).symm
    refine congrArg (fun z => DirectSum.of ((schemeSheafGradedAlgebra G'
      (isQuasicoherentPieces_of_isQuasicoherent G')).sectionPieces W'.toOpens) 1
        ((Scheme.Modules.symmetricAlgebraGen X' G').val.app (op W'.toOpens) z)) ?_
    exact (PresheafOfModules.naturality_apply u'.val (homOfLE h).op _).trans
      (congrArg (G'.val.map (homOfLE h).op) (homEquiv_inv_app_comp g u u' eF eG hu W.toOpens m))

/-- The morphism of the substrate on the chart over an affine open: `Proj` of `Sym(u)` on sections
followed by the chart. -/
theorem chart_comp_symGradedMapOfEpi (W : X.AffineZariskiSite) :
    (symGradedBundle G).chart W.toOpens W.2 ≫ symGradedMapOfEpi u =
      AlgebraicGeometry.Proj.map
          ((schemeSheafGradedAlgebraHom u (isQuasicoherentPieces_of_isQuasicoherent F)
            (isQuasicoherentPieces_of_isQuasicoherent G)).sectionHom W.toOpens)
          (Stacks.AlgebraicGeometry.ProjBundleSurjection.irrelevant_le_map_sectionHom
            (surjectiveOnAffineSections_symGradedHom u) W.2) ≫
        (symGradedBundle F).chart W.toOpens W.2 := by
  rw [symGradedMapOfEpi_eq, Stacks.AlgebraicGeometry.ProjBundleSurjection.chart_comp_map,
    Stacks.AlgebraicGeometry.ProjBundleSurjection.chartMap_eq_map]

include hu in
/-- **The closed immersion of a quotient commutes with base change, on the `SheafGradedAlgebra`
substrate.** -/
theorem symGradedMapOfEpi_comp_baseChangeHom :
    symGradedMapOfEpi u' ≫
        Stacks.ProjectiveBundle.baseChangeHom g F (isQuasicoherentPieces_of_isQuasicoherent F) F'
          (isQuasicoherentPieces_of_isQuasicoherent F') eF =
      Stacks.ProjectiveBundle.baseChangeHom g G (isQuasicoherentPieces_of_isQuasicoherent G) G'
          (isQuasicoherentPieces_of_isQuasicoherent G') eG ≫ symGradedMapOfEpi u := by
  refine Stacks.AlgebraicGeometry.RelativeProj.RelativeProjData.hom_ext_of_cover
    (symGradedBundle G') _ _
    (ι := {p : X.AffineZariskiSite × X'.AffineZariskiSite // p.2.toOpens ≤ g ⁻¹ᵁ p.1.toOpens})
    (fun p => p.1.2.toOpens) (fun p => p.1.2.2) (fun x' => ?_) (fun p => ?_)
  · obtain ⟨W, W', h, hx⟩ := Stacks.ProjectiveBundle.exists_affineZariskiSite_le_preimage g x'
    exact ⟨⟨(W, W'), h⟩, hx⟩
  · obtain ⟨⟨W, W'⟩, h⟩ := p
    change (symGradedBundle G').chart W'.toOpens W'.2 ≫ (symGradedMapOfEpi u' ≫ _) =
      (symGradedBundle G').chart W'.toOpens W'.2 ≫ (_ ≫ symGradedMapOfEpi u)
    have c2 := Stacks.ProjectiveBundle.chart_baseChangeHom_scheme g F F' eF W W' h
    have c3 := Stacks.ProjectiveBundle.chart_baseChangeHom_scheme g G G' eG W W' h
    have lhs := (Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ Stacks.ProjectiveBundle.baseChangeHom g F
          (isQuasicoherentPieces_of_isQuasicoherent F) F'
          (isQuasicoherentPieces_of_isQuasicoherent F') eF)
          (chart_comp_symGradedMapOfEpi u' W')).trans
        ((Category.assoc _ _ _).trans (congrArg (AlgebraicGeometry.Proj.map _ _ ≫ ·) c2)))
    have rhs := (Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ symGradedMapOfEpi u) c3).trans
        ((Category.assoc _ _ _).trans (congrArg (AlgebraicGeometry.Proj.map _ _ ≫ ·)
          (chart_comp_symGradedMapOfEpi u W))))
    refine lhs.trans (Eq.trans ?_ rhs.symm)
    refine (Category.assoc _ _ _).symm.trans (Eq.trans ?_ (Category.assoc _ _ _))
    refine congrArg (· ≫ _) ?_
    refine (AlgebraicGeometry.Proj.map_comp _ _ _ _).symm.trans
      (Eq.trans ?_ (AlgebraicGeometry.Proj.map_comp _ _ _ _))
    exact AlgebraicGeometry.Proj.map_congr
      (sectionHom_comp_baseChangeGradedHom g u u' eF eG hu W W' h) _ _

include hu in
/-- **The closed immersion of a quotient commutes with base change**: for `u' : F' ⟶ G'`
identified with `g^*u` through `F' ≅ g^*F` and `G' ≅ g^*G`, the square of the two closed
immersions `𝐏(G') ⟶ 𝐏(F')`, `𝐏(G) ⟶ 𝐏(F)` and the two base-change morphisms commutes. -/
theorem projectiveBundleMapOfEpi_comp_projectiveBundleBaseChange :
    projectiveBundleMapOfEpi u' ≫ projectiveBundleBaseChange g F F' eF =
      projectiveBundleBaseChange g G G' eG ≫ projectiveBundleMapOfEpi u := by
  refine (cancel_mono (bundlePresentationIso F).inv).1 ?_
  refine ((Category.assoc _ _ _).trans
    ((congrArg (projectiveBundleMapOfEpi u' ≫ ·)
      (projectiveBundleBaseChange_comp_bundlePresentationIso_inv g F F' eF)).trans
    ((Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ Stacks.ProjectiveBundle.baseChangeHom g F
        (isQuasicoherentPieces_of_isQuasicoherent F) F'
        (isQuasicoherentPieces_of_isQuasicoherent F') eF)
      (projectiveBundleMapOfEpi_comp_bundlePresentationIso_inv u')).trans
    ((Category.assoc _ _ _).trans
      (congrArg ((bundlePresentationIso G').inv ≫ ·)
        (symGradedMapOfEpi_comp_baseChangeHom g u u' eF eG hu))))))).trans ?_
  exact ((Category.assoc _ _ _).trans
    ((congrArg (projectiveBundleBaseChange g G G' eG ≫ ·)
      (projectiveBundleMapOfEpi_comp_bundlePresentationIso_inv u)).trans
    ((Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ symGradedMapOfEpi u)
      (projectiveBundleBaseChange_comp_bundlePresentationIso_inv g G G' eG)).trans
    (Category.assoc _ _ _))))).symm

end Stacks.RelativeProj

end
