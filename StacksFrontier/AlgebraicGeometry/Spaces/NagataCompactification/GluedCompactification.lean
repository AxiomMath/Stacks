module

public import StacksFrontier.AlgebraicGeometry.Spaces.CommonAdmissibleBlowup
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteMorphismClosedImmersionLimit
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.ProperLimitOfFinitePresentationEmbedding
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.RefinedValuativeCriterion
public import StacksFrontier.AlgebraicGeometry.Spaces.NagataCompactification.GluedValuativeStep
public import StacksFrontier.AlgebraicGeometry.Spaces.NagataCompactification.HasCompactification
public import StacksFrontier.AlgebraicGeometry.Spaces.ReducedFactorThroughClosedSubspace

/-!
# A compactification from two separated spaces through which valuation rings extend

Let `Y` be a quasi-compact and quasi-separated algebraic space and `p : U ⟶ Y` separated and of
finite type. Let `U ⟶ W₁` and `U ⟶ W₂` be open immersions into algebraic spaces separated and of
finite type over `Y`, such that every `γ : Spec K ⟶ U` from the fraction field of a valuation
ring `A`, compatible with `Spec A ⟶ Y`, extends after an extension of valuation rings to
`Spec A ⟶ W₁` or to `Spec A ⟶ W₂`. Then `U` has a compactification over `Y`.

This is the last paragraph of the proof of Stacks 0F4B. By Stacks 088Q there are `U`-admissible
blowups `W₁' ⟶ W₁` and `W₂' ⟶ W₂` which are open subspaces of one algebraic space `W` separated
and of finite type over `Y`. Let `W̄` be the scheme-theoretic image of `U` in `W`; `U` is a dense
open subspace of it (Stacks 088G). A valuative square for `W̄ ⟶ Y` whose generic point lies in
`U` extends to some `Wᵢ`, then by properness of `Wᵢ' ⟶ Wᵢ` to `Wᵢ'` and so to `W`; it lands in the
closed subspace `W̄`, being a reduced scheme whose generic point lands there. By Stacks 089G,
`W̄ ⟶ Y` is universally closed, hence proper.

## Main results

* `AlgebraicGeometry.Space.hasCompactification_of_forall_exists_lift`: the compactification.

## Implementation notes

The source applies Stacks 089G to `W` itself; the open subspaces `W₁'` and `W₂'` need not cover
`W` in the statement of Stacks 088Q, and `U` need not be dense in `W`, so the compactification is
taken to be the closure `W̄` of `U` in `W`.

## References

* [Stacks Project, Tag 0F4B](https://stacks.math.columbia.edu/tag/0F4B)
* [Stacks Project, Tag 088Q](https://stacks.math.columbia.edu/tag/088Q)
* [Stacks Project, Tag 088G](https://stacks.math.columbia.edu/tag/088G)
* [Stacks Project, Tag 089G](https://stacks.math.columbia.edu/tag/089G)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Topology

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

attribute [local instance] pointTopology

/-- **Lifting an extension through a proper modification into a closed subspace.** Let
`b : W' ⟶ W₀` be proper, `i : W' ⟶ W` with `i ≫ g = b ≫ g₀`, `u₀ : U ⟶ W'`, and let `I ⊆ W` be
a closed subspace through which `u₀ ≫ i` factors as `ū`. If `h : Spec A ⟶ W₀` extends
`γ ≫ u₀ ≫ b` over `σ`, then after a dominating extension there is a dotted arrow `Spec A ⟶ I`
extending `γ ≫ ū` over `σ`. -/
theorem ValuativeSquare.exists_lift_of_isProper {U W₀ W' W Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {X₀ Y₀ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f₀ : X₀ ⟶ Y₀} (q : ValuativeSquare f₀)
    (hW₀ : IsAlgebraicSpace B S hS W₀) (hW' : IsAlgebraicSpace B S hS W')
    (hW : IsAlgebraicSpace B S hS W) {b : W' ⟶ W₀} (hb : IsProper B S hS b) {i : W' ⟶ W}
    {g : W ⟶ Y} {g₀ : W₀ ⟶ Y} (hig : i ≫ g = b ≫ g₀) {u₀ : U ⟶ W'} (I : Subfunctor W)
    (hI : IsClosedSubspace B S hS I) {ū : U ⟶ I.toFunctor} (hū : ū ≫ I.ι = u₀ ≫ i)
    (γ : yoneda.obj (siteObject B S hS q.field_mem
      (Spec.map (CommRingCat.ofHom (algebraMap q.R q.K)) ≫ q.base)) ⟶ U)
    (σ : yoneda.obj (siteObject B S hS q.ring_mem q.base) ⟶ Y)
    (h : yoneda.obj (siteObject B S hS q.ring_mem q.base) ⟶ W₀)
    (hh₁ : yoneda.map q.fracHom ≫ h = γ ≫ u₀ ≫ b) (hh₂ : h ≫ g₀ = σ) :
    ∃ (e : q.DominatingExtension)
      (φ : yoneda.obj (siteObject B S hS e.square.ring_mem e.square.base) ⟶ I.toFunctor),
      yoneda.map e.square.fracHom ≫ φ = yoneda.map e.genericOver ≫ γ ≫ ū ∧
        φ ≫ I.ι ≫ g = yoneda.map e.specialOver ≫ σ := by
  have : Mono I.ι := mono_of_isClosedImmersion B S hS _ hI.2
  have hbE : ValuativeCriterion.Existence b :=
    valuativeCriterion_existence_of_isQuasiSeparated_of_universallyClosed hW' hW₀ b
      (isQuasiSeparated_of_isSeparated B S hS hb.1) hb.2.2
  obtain ⟨e, φ, hφgen, hφsp⟩ := exists_dominatingExtension_lift_of_existence q b hbE
    (γ ≫ u₀) h (by rw [Category.assoc, hh₁])
  have hred : HasEtaleLocalProperty B S hS
      (yoneda.obj (siteObject B S hS e.square.ring_mem e.square.base))
      (fun T : Scheme.{u} => IsReduced T) := by
    refine hasEtaleLocalProperty_of_representable B S hS _ _ _ (Iso.refl _) ?_
    show IsReduced (Spec (.of e.square.R))
    infer_instance
  have hIcl : IsClosed (Set.range (pointsMap B S hS _ I.ι)) :=
    isClosed_range_pointsMap_of_isProper B S hS hW
      (isProper_of_isClosedImmersion B S hS hI.1 hW _ hI.2)
  obtain ⟨φ', hφ'⟩ := (exists_lift_closedSubspace_iff_pointsMap_range_subset B S hS hW
    (isAlgebraicSpace_yoneda B S hS _) I hI hred (φ ≫ i)).2 (by
      refine (e.square.range_subset_closure_range_fracHom_comp (φ ≫ i)).trans
        (closure_minimal ?_ hIcl)
      rintro _ ⟨x, rfl⟩
      refine ⟨pointsMap B S hS _ (yoneda.map e.genericOver ≫ γ ≫ ū) x, ?_⟩
      rw [← pointsMap_comp_apply, reassoc_of% hφgen]
      simp only [Category.assoc, hū])
  refine ⟨e, φ', ?_, ?_⟩
  · refine (cancel_mono I.ι).1 ?_
    rw [Category.assoc, hφ', reassoc_of% hφgen]
    simp only [Category.assoc, hū]
  · rw [reassoc_of% hφ', hig, reassoc_of% hφsp, hh₂]

/-- **A compactification from two separated spaces through which valuation rings extend** (the
last paragraph of the proof of Stacks 0F4B). Let `Y` be
quasi-compact and quasi-separated, `p : U ⟶ Y` separated and of finite type, and
`aᵢ : U ⟶ Wᵢ` open immersions over `Y` into algebraic spaces separated and of finite type over
`Y`. If every `γ : Spec K ⟶ U` compatible with `σ : Spec A ⟶ Y`, for `A` a valuation ring with
fraction field `K`, extends after a dominating extension to `Spec A ⟶ W₁` or to `Spec A ⟶ W₂` over
`σ`, then `U` has a compactification over `Y`. -/
theorem hasCompactification_of_forall_exists_lift (hZ : B.Contains (⊤_ Scheme.{u}))
    {Y U W₁ W₂ : AlgebraicSpaces B S hS} (hYqc : IsQuasiCompactSpace B S hS Y.1)
    (hYqs : IsAbsolutelyQuasiSeparated B S hS hZ Y.1) {p : U.1 ⟶ Y.1}
    (hpsep : IsSeparated B S hS p) (hpft : IsFiniteType B S hS p) (a₁ : U ⟶ W₁) (a₂ : U ⟶ W₂)
    (ha₁ : IsOpenImmersion B S hS a₁.hom) (ha₂ : IsOpenImmersion B S hS a₂.hom)
    (g₁ : W₁ ⟶ Y) (g₂ : W₂ ⟶ Y) (hg₁sep : IsSeparated B S hS g₁.hom)
    (hg₁ft : IsFiniteType B S hS g₁.hom) (hg₂sep : IsSeparated B S hS g₂.hom)
    (hg₂ft : IsFiniteType B S hS g₂.hom) (hp₁ : a₁.hom ≫ g₁.hom = p) (hp₂ : a₂.hom ≫ g₂.hom = p)
    (hval : ∀ {X₀ Y₀ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f₀ : X₀ ⟶ Y₀} (q : ValuativeSquare f₀)
      (γ : yoneda.obj (siteObject B S hS q.field_mem
        (Spec.map (CommRingCat.ofHom (algebraMap q.R q.K)) ≫ q.base)) ⟶ U.1)
      (σ : yoneda.obj (siteObject B S hS q.ring_mem q.base) ⟶ Y.1),
      γ ≫ p = yoneda.map q.fracHom ≫ σ →
      ∃ e : q.DominatingExtension,
        (∃ h : yoneda.obj (siteObject B S hS e.square.ring_mem e.square.base) ⟶ W₁.1,
          yoneda.map e.square.fracHom ≫ h = yoneda.map e.genericOver ≫ γ ≫ a₁.hom ∧
            h ≫ g₁.hom = yoneda.map e.specialOver ≫ σ) ∨
        (∃ h : yoneda.obj (siteObject B S hS e.square.ring_mem e.square.base) ⟶ W₂.1,
          yoneda.map e.square.fracHom ≫ h = yoneda.map e.genericOver ≫ γ ≫ a₂.hom ∧
            h ≫ g₂.hom = yoneda.map e.specialOver ≫ σ)) :
    HasCompactification B S hS p := by
  have hj : a₁ ≫ g₁ = a₂ ≫ g₂ := by
    ext1
    exact hp₁.trans hp₂.symm
  obtain ⟨W₁', W₂', W, b₁, b₂, i₁, i₂, g, u₁, u₂, hb₁, hb₂, hi₁, hi₂, hgsep, hgft, hig₁, hig₂,
    hub₁, hub₂, hu, hu₁o, -⟩ := exists_isAdmissibleBlowup_isOpenImmersion_of_isOpenImmersion hZ
      g₁ g₂ a₁ a₂ hYqc hYqs ha₁ ha₂ hj (by rwa [ObjectProperty.FullSubcategory.comp_hom, hp₁])
      (by rwa [ObjectProperty.FullSubcategory.comp_hom, hp₁]) hg₁ft hg₁sep hg₂ft hg₂sep
      exists_integralFiniteSystem_isClosedImmersion_of_isFinite
      (fun f hX hY hft hsep hqc hqs => by
        obtain ⟨X', i, f', hX', hi, hf'sep, hf'fp, hif⟩ :=
          exists_isClosedImmersion_isSeparated_isFinitePresentation_of_isFiniteType B S hS hX hY f
            hft hsep hqc hqs
        exact ⟨X', f', i, hX', hf'sep, hf'fp, hi, hif⟩)
  have hom {X Y : AlgebraicSpaces B S hS} {f f' : X ⟶ Y} (h : f = f') : f.hom = f'.hom := h ▸ rfl
  have hig₁' : i₁.hom ≫ g.hom = b₁.hom ≫ g₁.hom := hom hig₁
  have hig₂' : i₂.hom ≫ g.hom = b₂.hom ≫ g₂.hom := hom hig₂
  have hub₁' : u₁.hom ≫ b₁.hom = a₁.hom := hom hub₁
  have hub₂' : u₂.hom ≫ b₂.hom = a₂.hom := hom hub₂
  have hu' : u₁.hom ≫ i₁.hom = u₂.hom ≫ i₂.hom := hom hu
  set u := u₁.hom ≫ i₁.hom with hudef
  have hug : u ≫ g.hom = p := by rw [hudef, Category.assoc, hig₁', reassoc_of% hub₁', hp₁]
  have huo : IsOpenImmersion B S hS u := isOpenImmersion_comp B S hS _ _ hu₁o hi₁
  have huqc : IsQuasiCompact B S hS u :=
    isQuasiCompact_of_comp_of_isQuasiSeparated B S hS u g.hom U.2 Y.2 (by rw [hug]; exact hpft.2)
      (isQuasiSeparated_of_isSeparated B S hS hgsep)
  obtain ⟨hopen, -, -, -, hdense⟩ :=
    isOpenImmersion_and_dense_toSchemeTheoreticImage_of_qc_or_reduced B S hS U.2 W.2 u
      (isImmersion_of_isOpenImmersion B S hS huo) (Or.inl huqc)
  set I := schemeTheoreticImageSubfunctor B S hS u with hI
  have hIc : IsClosedSubspace B S hS I :=
    isClosedSubspace_schemeTheoreticImageSubfunctor B S hS u W.2
  have : Mono I.ι := mono_of_isClosedImmersion B S hS _ hIc.2
  set ū := toSchemeTheoreticImage B S hS u with hūdef
  have hūι : ū ≫ I.ι = u := toSchemeTheoreticImage_ι B S hS u
  have hūqc : IsQuasiCompact B S hS ū :=
    isQuasiCompact_of_comp_mono B S hS ū I.ι (by rwa [hūι])
  have hIP : IsProper B S hS I.ι := isProper_of_isClosedImmersion B S hS hIc.1 W.2 _ hIc.2
  have hgIsep : IsSeparated B S hS (I.ι ≫ g.hom) := isSeparated_comp B S hS _ _ hIP.1 hgsep
  have hgIft : IsFiniteType B S hS (I.ι ≫ g.hom) :=
    isFiniteType_comp' B S hS _ _ W.2 Y.2 hIP.2.1 hgft
  have huc : UniversallyClosed B S hS (I.ι ≫ g.hom) := by
    refine universallyClosed_of_refinedValuativeCriterion B S hS U.2 hIc.1 Y.2 ū (I.ι ≫ g.hom)
      hgIft.2 hūqc hdense (fun q _ _ => valuativeCriterion_uniqueness_of_isSeparated _ hgIsep q) ?_
    intro q γ hγ
    have hγσ : γ ≫ p = yoneda.map q.fracHom ≫ q.special := by
      rw [← hug, ← hūι, ← Category.assoc, ← Category.assoc, hγ, Category.assoc]
      exact q.comm
    obtain ⟨e, hcase⟩ := hval q γ q.special hγσ
    obtain ⟨e', φ, hφgen, hφsp⟩ : ∃ (e' : e.square.DominatingExtension)
        (φ : yoneda.obj (siteObject B S hS e'.square.ring_mem e'.square.base) ⟶ I.toFunctor),
        yoneda.map e'.square.fracHom ≫ φ =
            yoneda.map e'.genericOver ≫ (yoneda.map e.genericOver ≫ γ) ≫ ū ∧
          φ ≫ I.ι ≫ g.hom = yoneda.map e'.specialOver ≫ yoneda.map e.specialOver ≫ q.special := by
      rcases hcase with ⟨h, hh₁, hh₂⟩ | ⟨h, hh₁, hh₂⟩
      · exact e.square.exists_lift_of_isProper W₁.2 W₁'.2 W.2 hb₁.isProper hig₁' I hIc hūι
          (yoneda.map e.genericOver ≫ γ) _ h (by rw [hh₁, hub₁']; simp only [Category.assoc]) hh₂
      · exact e.square.exists_lift_of_isProper W₂.2 W₂'.2 W.2 hb₂.isProper hig₂' I hIc
          (hūι.trans hu') (yoneda.map e.genericOver ≫ γ) _ h
          (by rw [hh₁, hub₂']; simp only [Category.assoc]) hh₂
    refine ⟨e.trans e', ⟨⟨φ, ?_, ?_⟩⟩⟩
    · show yoneda.map e'.square.fracHom ≫ φ = e'.square.generic
      rw [hφgen, e'.generic_comm, e.generic_comm, ← hγ]
      simp only [Category.assoc]
    · show φ ≫ I.ι ≫ g.hom = e'.square.special
      rw [hφsp, e'.special_comm, e.special_comm]
  exact ⟨I.toFunctor, ū, I.ι ≫ g.hom, hIc.1, hopen, hūqc, IsProper.mk' B S hS hgIsep hgIft huc,
    by rw [reassoc_of% hūι, hug]⟩

end AlgebraicGeometry.Space

end
