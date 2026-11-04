module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.Fiber
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartSchemePoints
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleAffineMemberThroughPoint
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.VectorBundle.SymmetricAlgebraBounded

/-!
# The local model of a vector bundle on an algebraic space

Let `W` be an algebraic space over a scheme `S` in a big fppf site and `ℰ` a finite locally free
`𝒪_W`-module, with vector bundle `p : E = \underline{Spec}_W(Sym(ℰ)) ⟶ W`. Over an affine étale
chart `V` of `W` on which `ℰ` is free on a finite type `ι`, the fibre product `E ×_W V` is the
spectrum of the sections `Γ(V, Sym(ℰ))`, and these are the polynomial ring `Γ(V, 𝒪)[T_i, i ∈ ι]`.
So `E ×_W V` is affine space `𝐀^ι_V` over `V`, compatibly with the projections to `V`. Every point
of `W` lies in the image of such a chart.

## Main definitions

* `AlgebraicGeometry.Space.vectorBundleChart`: the object `E ×_W V` of the big fppf site, with its
  projection `AlgebraicGeometry.Space.vectorBundleChartHom` to `V` and its morphism
  `AlgebraicGeometry.Space.vectorBundleChartToTotal` to `E`.
* `AlgebraicGeometry.Space.vectorBundleChartIso`: the identification of the scheme underlying
  `E ×_W V` with `𝐀^n_V`, for a trivialization of `ℰ` over `V` on a finite type in bijection
  with `n`.

## Main results

* `AlgebraicGeometry.Space.isPullback_vectorBundleChart`: the square formed by `E ×_W V`, `E`,
  `V` and `W` is cartesian.
* `AlgebraicGeometry.Space.vectorBundleChartIso_hom_over`: the identification is one over `V`.
* `AlgebraicGeometry.Space.isPullback_affineSpace_fiber_vectorBundleChartHom`: the fibre of
  `E ×_W V ⟶ V` over a point `v` of the chart is affine space `𝐀^n_{κ(v)}` over the residue field.
* `AlgebraicGeometry.Space.exists_trivializing_affine_chart`: every point of `W` is the image of a
  point of an affine chart on which `ℰ` is free of finite rank, of rank `r` if `ℰ` is finite
  locally free of rank `r`.

## References

* [Stacks Project, Tag 081W](https://stacks.math.columbia.edu/tag/081W)
* [Stacks Project, Tag 01M0](https://stacks.math.columbia.edu/tag/01M0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (W : AlgebraicSpaces B S hS)
  (F : SheafOfModules.{u} (structureRingSheaf B S hS W))
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree F]

/-! ### The fibre over an affine chart -/

section Chart

variable (V : SmallEtale B S hS W.1) [IsAffine (chartScheme V)]

/-- **The fibre product `E ×_W V` of the vector bundle with an affine chart**, as an object of the
big fppf site: the spectrum of the sections of `Sym(ℰ)` over `V`. -/
abbrev vectorBundleChart : BigFppfOver B S hS :=
  affineChartSpec B S hS (symmetricAlgebraSheaf B S hS W F)
    (sectionsBelowCutoff_symmetricAlgebraSheaf B S hS W F
      (SheafOfModules.IsQuasicoherentOnSite.of_isQuasicoherent F)
      (_root_.SheafOfModules.isFinitePresentationOnSite_of_isFiniteLocallyFreeOnSite
        (Stacks.SheafOfModules.isFiniteLocallyFreeOnSite_of_isFiniteLocallyFree F
          inferInstance))) V

/-- The projection `E ×_W V ⟶ V`. -/
abbrev vectorBundleChartHom : vectorBundleChart B S hS W F V ⟶ V.obj.left :=
  affineChartSpecHom B S hS (symmetricAlgebraSheaf B S hS W F)
    (sectionsBelowCutoff_symmetricAlgebraSheaf B S hS W F
      (SheafOfModules.IsQuasicoherentOnSite.of_isQuasicoherent F)
      (_root_.SheafOfModules.isFinitePresentationOnSite_of_isFiniteLocallyFreeOnSite
        (Stacks.SheafOfModules.isFiniteLocallyFreeOnSite_of_isFiniteLocallyFree F
          inferInstance))) V

/-- The chart reading of `Sym(ℰ)` at an affine chart reaches every algebra map. -/
theorem exists_chartEval_symmetricAlgebraSheaf_eq {T : BigFppfOver B S hS} (v : T ⟶ V.obj.left)
    (x : W.1.obj (op T)) (hxv : yonedaEquiv.symm x = yoneda.map v ≫ V.obj.hom)
    (β : (symmetricAlgebraSheaf B S hS W F).right.obj.obj (op V) ⟶
      Γ((BigFppfOver.toScheme B S hS).obj T, ⊤))
    (hβ : chartAlgebraMap B S hS (symmetricAlgebraSheaf B S hS W F) V ≫ β =
      ((BigFppfOver.toScheme B S hS).map v).appTop) :
    ∃ α, chartEval B S hS (symmetricAlgebraSheaf B S hS W F) V v x hxv α = β :=
  exists_chartEval_eq B S hS _ (isQuasicoherent_symmetricAlgebraSheaf B S hS W F
    (SheafOfModules.IsQuasicoherentOnSite.of_isQuasicoherent F)) V v x hxv β hβ

/-- The projection `E ×_W V ⟶ E`. -/
def vectorBundleChartToTotal :
    yoneda.obj (vectorBundleChart B S hS W F V) ⟶ (vectorBundle B S hS W F).obj.left.1 :=
  affineChartSpecToPoints B S hS (symmetricAlgebraSheaf B S hS W F)
    (sectionsBelowCutoff_symmetricAlgebraSheaf B S hS W F
      (SheafOfModules.IsQuasicoherentOnSite.of_isQuasicoherent F)
      (_root_.SheafOfModules.isFinitePresentationOnSite_of_isFiniteLocallyFreeOnSite
        (Stacks.SheafOfModules.isFiniteLocallyFreeOnSite_of_isFiniteLocallyFree F
          inferInstance))) V
    (exists_chartEval_symmetricAlgebraSheaf_eq B S hS W F V)

/-- **The fibre of the vector bundle over an affine chart.** The square formed by
`E ×_W V ⟶ E`, `E ×_W V ⟶ V`, the projection `p : E ⟶ W` and the chart `V ⟶ W` is cartesian. -/
theorem isPullback_vectorBundleChart :
    IsPullback (vectorBundleChartToTotal B S hS W F V)
      (yoneda.map (vectorBundleChartHom B S hS W F V))
      (vectorBundleProjection B S hS W F).hom V.obj.hom :=
  isPullback_affineChartSpec B S hS _ _ V
    (hinj := fun v x hxv => injective_chartEval_of_isAffine B S hS _
      (isQuasicoherent_symmetricAlgebraSheaf B S hS W F
        (SheafOfModules.IsQuasicoherentOnSite.of_isQuasicoherent F)) V v x hxv)
    (exists_chartEval_symmetricAlgebraSheaf_eq B S hS W F V)

/-- A ring isomorphism `Γ(V, 𝒪)[T_i, i ∈ n] ≅ Γ(V, Sym(ℰ))` over `Γ(V, 𝒪)` identifies
`E ×_W V` with `𝐀^n_V`. -/
def vectorBundleChartIsoOfRingEquiv {n : Type u}
    (ψ : MvPolynomial n Γ(chartScheme V, ⊤) ≃+*
      (symmetricAlgebraSheaf B S hS W F).right.obj.obj (op V)) :
    (BigFppfOver.toScheme B S hS).obj (vectorBundleChart B S hS W F V) ≅
      𝔸(n; chartScheme V) :=
  Scheme.Spec.mapIso ψ.toCommRingCatIso.op ≪≫
    (AffineSpace.isoOfIsAffine n (chartScheme V)).symm

/-- When `ψ` sends each constant `C r` to the image of `r` in `Γ(V, Sym(ℰ))`, the isomorphism
`vectorBundleChartIsoOfRingEquiv` lies over `V`: it commutes with the projections of
`E ×_W V` and `𝐀^n_V` to `V`. -/
theorem vectorBundleChartIsoOfRingEquiv_hom_over {n : Type u}
    (ψ : MvPolynomial n Γ(chartScheme V, ⊤) ≃+*
      (symmetricAlgebraSheaf B S hS W F).right.obj.obj (op V))
    (hψ : ∀ r, ψ (MvPolynomial.C r) = (symmetricAlgebraSheaf B S hS W F).algebraMap (op V) r) :
    (vectorBundleChartIsoOfRingEquiv B S hS W F V ψ).hom ≫ 𝔸(n; chartScheme V) ↘ chartScheme V =
      (BigFppfOver.toScheme B S hS).map (vectorBundleChartHom B S hS W F V) := by
  rw [toScheme_map_affineChartSpecHom, vectorBundleChartIsoOfRingEquiv, Iso.trans_hom,
    Iso.symm_hom, Category.assoc, AffineSpace.isoOfIsAffine_inv_over, specChartMap,
    ← Category.assoc]
  congr 1
  show Spec.map _ ≫ Spec.map _ = _
  rw [← Spec.map_comp]
  congr 1
  ext r
  exact hψ r

variable {ι : Type u} [DecidableEq ι] [Finite ι]
  (e : F.over V ≅ SheafOfModules.free (R := (structureRingSheaf B S hS W).over V) ι)

/-- The sections of `Sym(ℰ)` over a trivializing affine chart are the polynomial ring over the
functions on the chart, `Γ(V, 𝒪)[T_i, i ∈ ι] ≅ Γ(V, Sym(ℰ))`. -/
def polynomialChartRingEquiv :
    MvPolynomial ι Γ(chartScheme V, ⊤) ≃+*
      (symmetricAlgebraSheaf B S hS W F).right.obj.obj (op V) :=
  SymAlgSections.polynomialSectionsRingEquiv B S hS W F V e ‹_›

omit [SheafOfModules.IsFiniteLocallyFree F] in
/-- The isomorphism `polynomialChartRingEquiv` sends a constant polynomial `C r` to the image
of `r` under the structure map `Γ(V, 𝒪) ⟶ Γ(V, Sym(ℰ))`. -/
theorem polynomialChartRingEquiv_C (r : Γ(chartScheme V, ⊤)) :
    polynomialChartRingEquiv B S hS W F V e (MvPolynomial.C r) =
      (symmetricAlgebraSheaf B S hS W F).algebraMap (op V) r :=
  SymAlgSections.polynomialSectionsRingEquiv_C B S hS W F V e ‹_› r

/-- **The local model of the vector bundle.** Over an affine chart `V` on which `ℰ` is free on a
finite type `ι`, and for a bijection `ι ≃ n`, the scheme underlying `E ×_W V` is affine space
`𝐀^n_V`. -/
def vectorBundleChartIso {n : Type u} (ε : ι ≃ n) :
    (BigFppfOver.toScheme B S hS).obj (vectorBundleChart B S hS W F V) ≅ 𝔸(n; chartScheme V) :=
  vectorBundleChartIsoOfRingEquiv B S hS W F V
    ((MvPolynomial.renameEquiv Γ(chartScheme V, ⊤) ε.symm).toRingEquiv.trans
      (polynomialChartRingEquiv B S hS W F V e))

/-- **The local model is one over `V`**: under `vectorBundleChartIso` the projection
`E ×_W V ⟶ V` is the structure morphism of affine space. -/
theorem vectorBundleChartIso_hom_over {n : Type u} (ε : ι ≃ n) :
    (vectorBundleChartIso B S hS W F V e ε).hom ≫ 𝔸(n; chartScheme V) ↘ chartScheme V =
      (BigFppfOver.toScheme B S hS).map (vectorBundleChartHom B S hS W F V) :=
  vectorBundleChartIsoOfRingEquiv_hom_over B S hS W F V _ fun r => by
    rw [RingEquiv.trans_apply, AlgEquiv.toRingEquiv_eq_coe, AlgEquiv.coe_ringEquiv,
      MvPolynomial.renameEquiv_apply, MvPolynomial.rename_C]
    exact polynomialChartRingEquiv_C B S hS W F V e r

/-- **The fibre of the vector bundle over a point of a trivializing affine chart is affine space
over the residue field.** For a point `v` of an affine chart `V` on which `ℰ` is free on `ι ≃ n`,
the square formed by `𝐀^n_{κ(v)} ⟶ E ×_W V`, the projections and `Spec κ(v) ⟶ V` is cartesian,
so the fibre of `E ×_W V ⟶ V` over `v`, which is the fibre of `E ⟶ W` over the corresponding
point, is `𝐀^n_{κ(v)}`. -/
theorem isPullback_affineSpace_fiber_vectorBundleChartHom {n : Type u} (ε : ι ≃ n)
    (v : chartScheme V) :
    IsPullback
      (AffineSpace.map n ((chartScheme V).fromSpecResidueField v) ≫
        (vectorBundleChartIso B S hS W F V e ε).inv)
      (𝔸(n; Spec ((chartScheme V).residueField v)) ↘ Spec ((chartScheme V).residueField v))
      ((BigFppfOver.toScheme B S hS).map (vectorBundleChartHom B S hS W F V))
      ((chartScheme V).fromSpecResidueField v) := by
  refine (AffineSpace.isPullback_map (n := n) ((chartScheme V).fromSpecResidueField v)).of_iso
    (Iso.refl _) (vectorBundleChartIso B S hS W F V e ε).symm (Iso.refl _) (Iso.refl _)
    (by simp) (by simp) ?_ (by simp)
  rw [Iso.refl_hom, Category.comp_id, Iso.symm_hom,
    ← vectorBundleChartIso_hom_over B S hS W F V e ε,
    Iso.inv_hom_id_assoc]

/-- **The fibre of `E ×_W V ⟶ V` over a point of a trivializing affine chart is `𝐀^n_{κ(v)}`.** -/
def vectorBundleChartFiberIso {n : Type u} (ε : ι ≃ n) (v : chartScheme V) :
    𝔸(n; Spec ((chartScheme V).residueField v)) ≅
      ((BigFppfOver.toScheme B S hS).map (vectorBundleChartHom B S hS W F V)).fiber v :=
  (isPullback_affineSpace_fiber_vectorBundleChartHom B S hS W F V e ε v).isoPullback

end Chart

/-! ### Trivializing affine charts through every point -/

/-- **A covering family of charts has an affine member, below one of its objects, through every
point.** For a family of étale charts of an algebraic space `X` which covers every chart, every
point of `X` is the image of a point of an affine chart mapping to a member of the family. -/
theorem exists_affine_chartSchemeToPoints_eq_of_coversTop (X : AlgebraicSpaces B S hS)
    {I : Type*} {Y : I → SmallEtale B S hS X.1}
    (hY : ∀ U : SmallEtale B S hS X.1, Sieve.ofObjects Y U ∈ SmallEtale.topology B S hS X.1 U)
    (x : points B S hS X.1) :
    ∃ (Q : SmallEtale B S hS X.1) (i : I) (_ : Q ⟶ Y i) (z : chartScheme Q),
      IsAffine (chartScheme Q) ∧ chartSchemeToPoints B S hS X.1 Q z = x := by
  obtain ⟨V₀, hV₀⟩ := exists_isSurjective_chart B S hS X
  obtain ⟨z₀, rfl⟩ := surjective_chartSchemeToPoints B S hS X.1 V₀ hV₀ x
  obtain ⟨Q, φ, ⟨i, ⟨g⟩⟩, hQ, z, hz⟩ :=
    SmallEtale.exists_affine_mem_range_of_mem_topology B S hS X.1 (hY V₀) z₀
  refine ⟨Q, i, g, z, hQ, ?_⟩
  rw [← chartSchemeToPoints_map B S hS X.1 φ z]
  exact congrArg _ hz

/-- **Every point of `W` lies on an affine chart trivializing `ℰ`**: it is the image of a point of
an affine chart on which `ℰ` is free on a finite type. -/
theorem exists_trivializing_affine_chart (x : points B S hS W.1) :
    ∃ (V : SmallEtale B S hS W.1) (ι : Type u) (_ : Finite ι)
      (_ : F.over V ≅ SheafOfModules.free (R := (structureRingSheaf B S hS W).over V) ι)
      (z : chartScheme V), IsAffine (chartScheme V) ∧ chartSchemeToPoints B S hS W.1 V z = x := by
  obtain ⟨q, hq, hfin⟩ :=
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.exists_isFiniteLocallyFreeData (M := F)
  obtain ⟨V, i, g, z, hV, hz⟩ :=
    exists_affine_chartSchemeToPoints_eq_of_coversTop B S hS W q.coversTop x
  have := hfin.isFiniteType i
  have : IsIso (q.generators i).π := hq.isIso i
  exact ⟨V, (q.generators i).I, inferInstance,
    overFreeIsoOfHom B S hS W F g (asIso (q.generators i).π).symm, z, hV, hz⟩

omit [SheafOfModules.IsFiniteLocallyFree F] in
/-- **Every point of `W` lies on an affine chart trivializing `ℰ` with rank `r`**, when `ℰ` is
finite locally free of rank `r`. -/
theorem exists_trivializing_affine_chart_of_rank (r : ℕ)
    [hr : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank F r]
    (x : points B S hS W.1) :
    ∃ (V : SmallEtale B S hS W.1) (ι : Type u) (_ : Finite ι)
      (_ : F.over V ≅ SheafOfModules.free (R := (structureRingSheaf B S hS W).over V) ι)
      (_ : ι ≃ Fin r) (z : chartScheme V),
      IsAffine (chartScheme V) ∧ chartSchemeToPoints B S hS W.1 V z = x := by
  obtain ⟨q, hq, hrank⟩ := hr.exists_isFiniteLocallyFreeOfRankData
  obtain ⟨V, i, g, z, hV, hz⟩ :=
    exists_affine_chartSchemeToPoints_eq_of_coversTop B S hS W q.coversTop x
  have : IsIso (q.generators i).π := hq.isIso i
  exact ⟨V, (q.generators i).I, Finite.of_equiv _ (hrank i).some.symm,
    overFreeIsoOfHom B S hS W F g (asIso (q.generators i).π).symm, (hrank i).some, z, hV, hz⟩

end AlgebraicGeometry.Space

end
