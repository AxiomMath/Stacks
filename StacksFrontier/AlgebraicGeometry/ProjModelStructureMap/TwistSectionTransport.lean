module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjTwistTensorPow
public import StacksFrontier.AlgebraicGeometry.Descent.PullbackSectionsSheaf.UnitComparison
public import StacksFrontier.AlgebraicGeometry.ProjModelStructureMap.TwistTransport
public import StacksFrontier.AlgebraicGeometry.ProjPolyChart.Away
public import StacksFrontier.AlgebraicGeometry.ProjSaturation.Basic
public import StacksFrontier.AlgebraicGeometry.ProjTwistSection.Basic
public import StacksFrontier.AlgebraicGeometry.TwistChartLocality.ChartGamma

/-!
# Global sections of `𝒪(d)` across the two models of projective space

The degree-`d` global sections of the twisting sheaves `𝒪(d)` on
`AlgebraicGeometry.Proj (Stacks.ProjectiveCohomology.polyGrading S n)` and on the base-change
model `AlgebraicGeometry.projectiveSpaceOverRing n S` correspond along
`Stacks.ProjectiveCohomology.projModelIso`. Over a field the base-change model therefore carries
a nonzero global section of `𝒪(1)` in every dimension.

## Main definitions

* `AlgebraicGeometry.Scheme.Modules.gammaTopIsoOfPullbackIso`: for an isomorphism `f : X ⟶ Y` of
  schemes and an isomorphism `f^*M ≅ N`, the global sections `Γ(M, ⊤)` and `Γ(N, ⊤)` agree.
* `AlgebraicGeometry.Scheme.Modules.sectionsEquivOfPullbackIso`: the same comparison read on
  `CategoryTheory.SheafOfModules.sections`.
* `Stacks.ProjectiveCohomology.pullbackProjModelIsoHomTwistOverIso`: the inverse image along
  `projModelIso` of the base-change model's `𝒪(d)` is the `Proj`-model's `𝒪(d)`.
* `Stacks.ProjectiveCohomology.twistSectionsEquiv`: the transport of global sections of `𝒪(d)`
  between the two models of `ℙⁿ_S`, in every degree and over every coefficient ring.

## Main results

* `Stacks.ProjectiveCohomology.eval_top_twistSectionsEquiv_eq_zero_iff`: a transported section
  vanishes over `⊤` exactly when its source does.
* `Stacks.ProjectiveCohomology.exists_eval_top_ne_zero_twistingSheaf_polyGrading`: over a field
  the linear form `T₀` is a nonzero global section of `𝒪(1)` on `Proj k[T₀, …, Tₙ]`.
* `Stacks.ProjectiveCohomology.exists_eval_top_ne_zero_twistOver`: a nonzero global section of
  `𝒪(1)` on `AlgebraicGeometry.projectiveSpaceOverRing n k`, for every field `k` and every `n`.

## References

* [Stacks Project, Tag 01N2](https://stacks.math.columbia.edu/tag/01N2)
* [Stacks Project, Tag 01MN](https://stacks.math.columbia.edu/tag/01MN)
* [Stacks Project, Tag 01NF](https://stacks.math.columbia.edu/tag/01NF)
* [Stacks Project, Tag 08A0](https://stacks.math.columbia.edu/tag/08A0)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}}

/-- A direct image has the same global sections as the module it comes from:
`Γ(f_*N, ⊤) ≅ Γ(N, ⊤)`. -/
def pushforwardGammaTopIso (f : X ⟶ Y) (N : X.Modules) :
    Γ((pushforward f).obj N, ⊤) ≅ Γ(N, ⊤) :=
  N.presheaf.mapIso (eqToIso (show (⊤ : X.Opens) = f ⁻¹ᵁ ⊤ by simp)).op

/-- If `f : X ⟶ Y` is an isomorphism of schemes and `f^*M ≅ N`, then `Γ(M, ⊤) ≅ Γ(N, ⊤)`. -/
def gammaTopIsoOfPullbackIso (f : X ⟶ Y) [IsIso f] {M : Y.Modules} {N : X.Modules}
    (e : (pullback f).obj M ≅ N) : Γ(M, ⊤) ≅ Γ(N, ⊤) :=
  haveI : IsIso ((pullbackPushforwardAdjunction f).unit.app M) :=
    Adjunction.isIso_unit_app_of_iso _
      (((pushforwardComp (inv f) f ≪≫ pushforwardCongr (IsIso.inv_hom_id f) ≪≫
          pushforwardId Y).app M).symm)
  asIso ((asIso ((pullbackPushforwardAdjunction f).unit.app M) ≪≫
      (pushforward f).mapIso e).hom.app ⊤) ≪≫ pushforwardGammaTopIso f N

/-- The section attached to a global section over `⊤` takes that value over `⊤`. -/
theorem sectionsTopEquiv_eval_top (M : X.Modules) (x : Γ(M, ⊤)) :
    (sectionsTopEquiv M x).eval (op ⊤) = x :=
  (sectionsTopEquiv M).symm_apply_apply x

/-- For an isomorphism `f : X ⟶ Y` of schemes and an isomorphism `f^*M ≅ N`, the sections of `M`
and of `N` correspond, through their values over `⊤`. -/
def sectionsEquivOfPullbackIso (f : X ⟶ Y) [IsIso f] {M : Y.Modules} {N : X.Modules}
    (e : (pullback f).obj M ≅ N) : M.sections ≃ N.sections :=
  (sectionsTopEquiv M).symm.trans
    ((Equiv.ofBijective _
        (ConcreteCategory.bijective_of_isIso (gammaTopIsoOfPullbackIso f e).hom)).trans
      (sectionsTopEquiv N))

/-- The transported section is the one whose value over `⊤` is the transported value. -/
theorem sectionsEquivOfPullbackIso_apply (f : X ⟶ Y) [IsIso f] {M : Y.Modules} {N : X.Modules}
    (e : (pullback f).obj M ≅ N) (s : M.sections) :
    sectionsEquivOfPullbackIso f e s =
      sectionsTopEquiv N ((gammaTopIsoOfPullbackIso f e).hom (s.eval (op ⊤))) := rfl

/-- The transported section vanishes over `⊤` exactly when the original one does. -/
theorem eval_top_sectionsEquivOfPullbackIso_eq_zero_iff (f : X ⟶ Y) [IsIso f] {M : Y.Modules}
    {N : X.Modules} (e : (pullback f).obj M ≅ N) (s : M.sections) :
    (sectionsEquivOfPullbackIso f e s).eval (op ⊤) = 0 ↔ s.eval (op ⊤) = 0 := by
  have key : (sectionsEquivOfPullbackIso f e s).eval (op ⊤) =
      (gammaTopIsoOfPullbackIso f e).hom (s.eval (op ⊤)) :=
    (congrArg (fun t ↦ PresheafOfModules.sections.eval t (op ⊤))
      (sectionsEquivOfPullbackIso_apply f e s)).trans (sectionsTopEquiv_eval_top N _)
  refine ⟨fun h ↦ ?_, fun h ↦ key.trans ?_⟩
  · exact (Iso.hom_inv_id_apply (gammaTopIsoOfPullbackIso f e) (s.eval (op ⊤))).symm.trans
      ((congrArg (ConcreteCategory.hom (gammaTopIsoOfPullbackIso f e).inv)
        (key.symm.trans h)).trans (map_zero _))
  · exact (congrArg (ConcreteCategory.hom (gammaTopIsoOfPullbackIso f e).hom) h).trans
      (map_zero _)

end AlgebraicGeometry.Scheme.Modules

namespace Stacks.ProjectiveCohomology

attribute [local instance] MvPolynomial.gradedAlgebra

/-! ### The two models' `𝒪(d)` -/

section TwoModels

variable (S : Type u) [CommRing S] (n : ℕ)

/-- The inverse image of the base-change model's `𝒪(d)` along the comparison of models is the
twisting sheaf `𝒪(d)` of `S[T₀, …, Tₙ]`. -/
def pullbackProjModelIsoHomTwistOverIso (d : ℤ) :
    (Scheme.Modules.pullback (projModelIso S n).hom).obj
        (Stacks.AlgebraicGeometry.ProjTwistTensorPow.twistOver n (Spec (CommRingCat.of S)) d) ≅
      ProjectiveSpectrum.Proj.twistingSheaf (polyGrading S n) d :=
  pullbackProjModelIsoHomProjectiveTwistingSheafIso S n d ≪≫
    (Stacks.AlgebraicGeometry.TwistChartLocality.hasPolyTwistTransport S n d).some

/-- The global sections of the degree-`d` twist on `AlgebraicGeometry.projectiveSpaceOverRing n S`
are the global sections of `𝒪(d)` on `Proj S[T₀, …, Tₙ]`, in every integer degree and over every
coefficient ring. -/
def twistSectionsEquiv (d : ℤ) :
    (Stacks.AlgebraicGeometry.ProjTwistTensorPow.twistOver n
        (Spec (CommRingCat.of S)) d).sections ≃
      (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading S n) d).sections :=
  Scheme.Modules.sectionsEquivOfPullbackIso (projModelIso S n).hom
    (pullbackProjModelIsoHomTwistOverIso S n d)

/-- The transport of global sections of `𝒪(d)` carries a section vanishing over `⊤` to one
vanishing over `⊤`, and nothing else. -/
theorem eval_top_twistSectionsEquiv_eq_zero_iff (d : ℤ)
    (s : (Stacks.AlgebraicGeometry.ProjTwistTensorPow.twistOver n
      (Spec (CommRingCat.of S)) d).sections) :
    (twistSectionsEquiv S n d s).eval (op ⊤) = 0 ↔ s.eval (op ⊤) = 0 :=
  Scheme.Modules.eval_top_sectionsEquivOfPullbackIso_eq_zero_iff (projModelIso S n).hom
    (pullbackProjModelIsoHomTwistOverIso S n d) s

end TwoModels

/-! ### A nonzero degree-one section over a field -/

variable (k : Type u) [Field k] (n : ℕ)

/-- Over a field, the global section `T₀ / 1` of `𝒪(1)` on `Proj k[T₀, …, Tₙ]` is nonzero. -/
theorem degreeSection_X_one_ne_zero :
    ProjectiveSpectrum.Proj.degreeSection (polyGrading k n) 1
        ⟨MvPolynomial.X 0, Stacks.AlgebraicGeometry.ProjPolyChart.X_mem_one k n 0⟩ ≠ 0 := by
  intro hz
  obtain ⟨N, hN⟩ := (ProjectiveSpectrum.Proj.degreeSection_eq_zero_iff (polyGrading k n)
    (MvPolynomial.adjoin_homogeneousSubmodule_one_eq_top (Fin (n + 1)) k) _).mp hz
  have hmem : (MvPolynomial.X 0 : MvPolynomial (Fin (n + 1)) k) ^ N ∈ polyGrading k n N := by
    simpa using SetLike.pow_mem_graded N
      (Stacks.AlgebraicGeometry.ProjPolyChart.X_mem_one k n 0)
  have h := hN _ hmem
  rw [← pow_succ] at h
  exact pow_ne_zero _ (MvPolynomial.X_ne_zero (0 : Fin (n + 1))) h

/-- For every field `k`, `𝒪(1)` on `Proj k[T₀, …, Tₙ]` has a global section that is nonzero over
`⊤`. -/
theorem exists_eval_top_ne_zero_twistingSheaf_polyGrading :
    ∃ s : (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading k n) (1 : ℤ)).sections,
      s.eval (op ⊤) ≠ 0 :=
  ⟨Stacks.ProjTwistSection.homogeneousSection (polyGrading k n) (MvPolynomial.X 0)
      (Stacks.AlgebraicGeometry.ProjPolyChart.X_mem_one k n 0),
    (Stacks.SheafOfModules.sectionsOfTop_eval_top _ _).trans_ne (degreeSection_X_one_ne_zero k n)⟩

/-- For every field `k` and every `n`, `𝒪(1)` on the base-change model of `ℙⁿ_k` has a global
section that is nonzero over `⊤`. -/
theorem exists_eval_top_ne_zero_twistOver :
    ∃ s : (Stacks.AlgebraicGeometry.ProjTwistTensorPow.twistOver n
        (Spec (CommRingCat.of k)) 1).sections, s.eval (op ⊤) ≠ 0 := by
  obtain ⟨t, ht⟩ := exists_eval_top_ne_zero_twistingSheaf_polyGrading k n
  exact ⟨(twistSectionsEquiv k n 1).symm t, fun hz ↦ ht <|
    (congrArg (fun u ↦ PresheafOfModules.sections.eval u (op ⊤))
      ((twistSectionsEquiv k n 1).apply_symm_apply t).symm).trans
        ((eval_top_twistSectionsEquiv_eq_zero_iff k n 1 _).mpr hz)⟩

end Stacks.ProjectiveCohomology

end
