module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.Normalization.EtaleBaseChange
public import StacksFrontier.AlgebraicGeometry.NormalizationBaseChange.UniversalProperty
public import StacksFrontier.AlgebraicGeometry.NormalizationBaseChangeBirational.Basic
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.ProjectiveCompletion
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.ProjectiveCompletionDiscreteValuation
public import StacksFrontier.AlgebraicGeometry.Variety.OneDimensional.NormalizationIso
public import StacksFrontier.AlgebraicGeometry.Variety.OneDimensional.SmoothProjectiveNormalizationProper

/-!
# Smooth projective compactification of the normalization of a reduced curve

Let `k` be a field and let `X` be a reduced separated scheme of finite type over `k` with
`dim(X) ≤ 1`. There is a finite purely inseparable extension `k'/k` such that the normalization
of `X_{k'}` sits as a *dense open subscheme* of a finite disjoint union of schemes `Ȳᵢ`, each
smooth, H-projective and geometrically irreducible of dimension at most one over a finite
separable extension `k'ᵢ/k'`, all over `Spec k'`.

This is [Stacks, Tag 0GK5] for a reduced `X`: the source's first move is to replace `X` by its
reduction, and everything after that move is proved here.

## Main results

* `exists_isPurelyInseparable_dense_openImmersion_smooth_projective_of_isReduced`:
  for `X` reduced, the extension `k'`, the compactifications `Ȳᵢ`, the fields `k'ᵢ`, the dense
  open immersion `j` and the commuting diagram.
* `AlgebraicGeometry.exists_isPurelyInseparable_dense_openImmersion_smooth_projective`: the same
  for an arbitrary separated `X` of finite type, which is the whole of the tag.

## Implementation notes

**The route is the source's own, in the source's order.** First `X` is compactified: [Stacks,
Tag 0BXW] gives a dense open immersion `X ⟶ W` with `W` H-projective over `k`, and `W` again has
dimension at most one because a scheme locally of finite type over a field has the dimension of
any dense open
(`Stacks.CurveProjectiveCompletion.topologicalKrullDim_le_of_dense_isOpenImmersion`). *Then* the
purely inseparable extension is chosen, for `W` rather than for `X`:
`exists_isPurelyInseparable_normalization_coproduct_smooth_projective` -- the
proper case of this tag -- supplies `k'`, the decomposition of the normalization of `W_{k'}` into
the `Ȳᵢ`, and clauses (4) and (5). Taking the extension after the compactification is what makes
the compactified pieces *smooth*: the normalization of `W_{k'}` is geometrically normal by the
choice of `k'`, whereas compactifying the normalization of `X_{k'}` afterwards would add boundary
points at which geometric regularity is not available.

**Transporting back along the open immersion.** The base change `φ : X_{k'} ⟶ W_{k'}` of the open
immersion is again an open immersion
(`CategoryTheory.MorphismProperty.pullbackMap`), hence etale, so the normalization of `X_{k'}` is
the base change of the normalization of `W_{k'}` along it -- [Stacks, Tag 0BXW]'s companion
[Stacks, Tag 07TD], `AlgebraicGeometry.isPullback_normalizationSchemeMap_of_etale` -- and the
induced morphism of normalizations is the open immersion `j` of clause (3).

**Density of `j`.** The image of `j` is the preimage under the normalization morphism of `W_{k'}`
of the image of `φ`. The image of `φ` is dense because `Spec k' ⟶ Spec k` is a universal
homeomorphism, so the projections `X_{k'} ⟶ X` and `W_{k'} ⟶ W` are homeomorphisms carrying `φ`
to the dense open immersion `X ⟶ W`. A dense open of a Noetherian space contains every generic
point (`Stacks.CurveProjectiveCompletion.mem_of_mem_genericPoints`), the normalization carries
generic points to generic points (`AlgebraicGeometry.Scheme.normalization_mem_genericPoints`), and
a set containing every generic point of a sober space is dense.

**The reduction of `X`.** The source's first move is carried out last, in
`exists_isPurelyInseparable_dense_openImmersion_smooth_projective`: the closed immersion of the
reduction of `X` is surjective, so after base change to `k'` it is still a surjective closed
immersion, and such a morphism induces an isomorphism on reductions
(`Scheme.reductionMap'_isIso_of_isClosedImmersion_of_surjective`). The normalization
only sees the reduction ([Stacks, Tag 035O]) and is functorial along an isomorphism over the base
field, so the normalizations of `X_{k'}` and of `(X_red)_{k'}` agree over `Spec k'`.

## References

* [Stacks Project, Tag 0GK5](https://stacks.math.columbia.edu/tag/0GK5)
* [Stacks Project, Tag 0BXW](https://stacks.math.columbia.edu/tag/0BXW)
* [Stacks Project, Tag 07TD](https://stacks.math.columbia.edu/tag/07TD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- The range of a composite whose first factor is an isomorphism is the range of the second. -/
private theorem range_comp_base_of_isIso {Z Y W : Scheme.{u}} (f : Z ⟶ Y) [IsIso f] (g : Y ⟶ W) :
    Set.range (f ≫ g).base = Set.range g.base :=
  f.homeomorph.surjective.range_comp g.base

/-- The base change of a morphism `g` over `Spec k` along `Spec k' ⟶ Spec k` satisfies any
property `P` that is stable under base change and composition and satisfied by `g`. -/
private theorem pullbackMap_spectrumMap {k k' : Type u} [Field k] [Field k'] [Algebra k k']
    (P : MorphismProperty Scheme.{u}) [P.IsStableUnderBaseChange] [P.IsStableUnderComposition]
    {X W : Scheme.{u}} {g : X ⟶ W} {p : X ⟶ Spec (.of k)}
    {q : W ⟶ Spec (.of k)} (h : g ≫ q = p) (hid : P (𝟙 (Spec (.of k')))) (hg : P g) :
    P (pullback.map (spectrumMap k k') p (spectrumMap k k') q (𝟙 _) g (𝟙 _)
      ((Category.comp_id _).trans (Category.id_comp _).symm)
      ((Category.comp_id _).trans h.symm)) :=
  MorphismProperty.pullbackMap (P := P) hid hg (Category.id_comp _).symm
    h.symm

/-- **[Stacks, Tag 0GK5] for a reduced `X`.** Let `k` be a field and let `X` be a reduced
separated scheme of finite type over `k` with `dim(X) ≤ 1`. There is a finite purely inseparable
extension `k'/k`, a finite family of schemes `Ȳᵢ` over `Spec k'`, and a dense open immersion `j`
from the normalization of `X_{k'}` into their disjoint union over `Spec k'`, such that each `Ȳᵢ`
is smooth, H-projective and geometrically irreducible of dimension at most one over a finite
separable extension `k'ᵢ/k'`. -/
@[stacks 0GK5 "clauses (3), (4) and (5) -- the whole diagram -- for a REDUCED X. The source's \
first move is to replace X by its reduction; everything after that move is proved here. The \
normalization of X_{k'} is exhibited as a DENSE OPEN SUBSCHEME of the disjoint union of the \
compactifications Ybar_i (clause 3), each of which is SMOOTH, PROJECTIVE and GEOMETRICALLY \
IRREDUCIBLE of dimension at most one over a finite SEPARABLE extension k'_i/k' (clauses 4 \
and 5), and the diagram commutes over Spec k'. What is NOT covered: the reduction step, i.e. the \
case of an X that is not reduced.",
  ega "IV 17.15.14" "special case",
  sga "4 XIV 1.11" "special case"]
public theorem exists_isPurelyInseparable_dense_openImmersion_smooth_projective_of_isReduced
    (k : Type u) [Field k] {X : Scheme.{u}} (p : X ⟶ Spec (.of k))
    [IsSeparated p] [LocallyOfFiniteType p] [QuasiCompact p] [AlgebraicGeometry.IsReduced X]
    (hdim : topologicalKrullDim (X : Type u) ≤ 1) :
    ∃ (k' : Type u) (_ : Field k') (_ : Algebra k k') (_ : Module.Finite k k')
      (_ : IsPurelyInseparable k k') (ι : Type u) (_ : Finite ι) (Ybar : ι → Scheme.{u})
      (sbar : (∐ Ybar) ⟶ Spec (.of k'))
      (K : ι → Type u) (_ : ∀ i, Field (K i)) (_ : ∀ i, Algebra k' (K i))
      (_ : ∀ i, Module.Finite k' (K i)) (_ : ∀ i, Algebra.IsSeparable k' (K i))
      (rbar : ∀ i, Ybar i ⟶ Spec (.of (K i)))
      (j : normalizationSchemeOverField k' (pullback.fst (spectrumMap k k') p) ⟶ ∐ Ybar)
      (_ : IsOpenImmersion j),
      Dense (Set.range j.base) ∧
        j ≫ sbar = normalizationOverField k' (pullback.fst (spectrumMap k k') p) ≫
            pullback.fst (spectrumMap k k') p ∧
          (∀ i, rbar i ≫ Spec.map (CommRingCat.ofHom (algebraMap k' (K i)))
              = Sigma.ι Ybar i ≫ sbar) ∧
            ∀ i, Smooth (rbar i) ∧ IsProjectiveMorphism (rbar i) ∧
              GeometricallyIrreducible (rbar i) ∧ topologicalKrullDim (Ybar i : Type u) ≤ 1 := by
  classical
  -- Step 1: compactify `X` over `k` ([Stacks, Tag 0BXW]).
  obtain ⟨W, qW, j₁, hj₁, hcomp, hWproj, hdom, -, -, -⟩ :=
    Stacks.CurveProjectiveCompletion.exists_projective_completion_discreteValuation_of_isReduced
      k p hdim
  let := hj₁
  let := hdom
  have hWproper : IsProper qW := isProper_of_isProjectiveMorphism qW hWproj
  let := hWproper
  have hWlft : LocallyOfFiniteType qW := IsProper.toLocallyOfFiniteType
  let := hWlft
  have hdense₁ : Dense (Set.range j₁.base) := hdom.denseRange
  let : NoetherianSpace W :=
    Stacks.AlgebraicGeometry.ProperGeomConnected.noetherianSpace_of_isProper qW
  have hdimW : topologicalKrullDim (W : Type u) ≤ 1 :=
    (Stacks.CurveProjectiveCompletion.topologicalKrullDim_le_of_dense_isOpenImmersion
      k j₁ p qW hcomp hdense₁).trans hdim
  -- Step 2: the proper case of the tag, applied to `W`.
  obtain ⟨k', hfield, halg, hfink, hpi, ι, hfinι, Ybar, e, K, fieldK, algK, finK, sepK, rbar,
    hrbar, hprops⟩ :=
    exists_isPurelyInseparable_normalization_coproduct_smooth_projective k qW hdimW
  let : Field k' := hfield
  let : Algebra k k' := halg
  let : Module.Finite k k' := hfink
  let : IsPurelyInseparable k k' := hpi
  -- Step 3: the base change of the open immersion.
  set φ := pullback.map (spectrumMap k k') p (spectrumMap k k') qW (𝟙 _) j₁ (𝟙 _)
      ((Category.comp_id _).trans (Category.id_comp _).symm)
      ((Category.comp_id _).trans hcomp.symm) with hφdef
  have hφopen : IsOpenImmersion φ :=
    pullbackMap_spectrumMap (@IsOpenImmersion) hcomp inferInstance hj₁
  let := hφopen
  have hφfst : φ ≫ pullback.fst (spectrumMap k k') qW = pullback.fst (spectrumMap k k') p := by
    rw [hφdef, pullback.lift_fst, Category.comp_id]
  have hφsnd : φ ≫ pullback.snd (spectrumMap k k') qW
      = pullback.snd (spectrumMap k k') p ≫ j₁ := by
    rw [hφdef, pullback.lift_snd]
  -- The two projections to `X` and `W` are homeomorphisms, the base being a universal
  -- homeomorphism.
  have hhomeo : ∀ {Z : Scheme.{u}} (g : Z ⟶ Spec (.of k)),
      IsHomeomorph (pullback.snd (spectrumMap k k') g).base := by
    intro Z g
    rw [← pullbackSymmetry_hom_comp_fst]
    exact (isHomeomorph_pullbackFst_specMap_algebraMap k k' g).comp
      (pullbackSymmetry (spectrumMap k k') g).hom.homeomorph.isHomeomorph
  -- Step 4: the image of `φ` is dense.
  have hpt : ∀ x : (pullback (spectrumMap k k') p : Scheme.{u}),
      (pullback.snd (spectrumMap k k') qW) (φ x)
        = j₁ ((pullback.snd (spectrumMap k k') p) x) := fun x => by
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hφsnd]
  have hrangeφ : Set.range φ.base
      = (pullback.snd (spectrumMap k k') qW).base ⁻¹' Set.range j₁.base := by
    refine Set.eq_of_subset_of_subset ?_ ?_
    · rintro w ⟨x, rfl⟩
      exact ⟨(pullback.snd (spectrumMap k k') p) x, (hpt x).symm⟩
    · rintro w ⟨x₀, hx₀⟩
      obtain ⟨x, hx⟩ := (hhomeo p).surjective x₀
      refine ⟨x, (hhomeo qW).injective ?_⟩
      rw [hpt x, hx]
      exact hx₀
  have hdenseφ : Dense (Set.range φ.base) :=
    hrangeφ ▸ hdense₁.preimage (hhomeo qW).isOpenMap
  -- Step 5: the normalization of `X_{k'}` is the base change of that of `W_{k'}`.
  have hYfin := finite_irreducibleComponents_of_locallyOfFiniteType k'
    (pullback.fst (spectrumMap k k') qW)
  have hpb := isPullback_normalizationSchemeMap_of_etale φ hYfin
  set j₂ := normalizationSchemeMap φ (finite_irreducibleComponents_of_smooth φ hYfin) hYfin
    with hj₂def
  have hj₂open : IsOpenImmersion j₂ :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsOpenImmersion)
      hpb.flip hφopen
  let := hj₂open
  -- Step 6: the image of `j₂` is dense: it is the preimage of the image of `φ`.
  have hrangej₂ : Set.range j₂.base
      = ((pullback (spectrumMap k k') qW).normalization hYfin).base ⁻¹' Set.range φ.base := by
    have hfst : hpb.isoPullback.hom ≫ pullback.fst
        ((pullback (spectrumMap k k') qW).normalization hYfin) φ = j₂ := hpb.isoPullback_hom_fst
    rw [← hfst, range_comp_base_of_isIso]
    exact Scheme.Pullback.range_fst _ φ
  let : NoetherianSpace (pullback (spectrumMap k k') qW : Scheme.{u}) :=
    Stacks.AlgebraicGeometry.ProperGeomConnected.noetherianSpace_of_isProper
      (pullback.fst (spectrumMap k k') qW)
  have hgp : genericPoints ((pullback (spectrumMap k k') qW).normalizationScheme hYfin)
      ⊆ Set.range j₂.base := by
    intro η hη
    rw [hrangej₂]
    exact AlgebraicGeometry.mem_of_mem_genericPoints_of_dense
      ⟨Set.range φ.base, φ.isOpenEmbedding.isOpen_range⟩ hdenseφ
      (Scheme.normalization_mem_genericPoints (pullback (spectrumMap k k') qW) hYfin hη)
  have hdensej₂ : Dense (Set.range j₂.base) := by
    rw [dense_iff_closure_eq]
    refine Set.eq_univ_of_univ_subset ?_
    rw [← genericPoints.closure (α := (pullback (spectrumMap k k') qW).normalizationScheme hYfin)]
    exact closure_mono hgp
  -- Step 7: assemble.
  refine ⟨k', hfield, halg, hfink, hpi, ι, hfinι, Ybar,
    e.inv ≫ normalizationOverField k' (pullback.fst (spectrumMap k k') qW)
      ≫ pullback.fst (spectrumMap k k') qW,
    K, fieldK, algK, finK, sepK, rbar, j₂ ≫ e.hom, inferInstance, ?_, ?_, hrbar, hprops⟩
  · have hehomeo : IsHomeomorph (e.hom.base : (pullback (spectrumMap k k') qW).normalizationScheme
        hYfin → (∐ Ybar : Scheme.{u})) := e.hom.homeomorph.isHomeomorph
    have hrange : Set.range (j₂ ≫ e.hom).base = e.hom.base '' Set.range j₂.base := by
      rw [← Set.range_comp]
      rfl
    rw [hrange]
    exact hehomeo.surjective.denseRange.dense_image hehomeo.continuous hdensej₂
  · rw [Category.assoc, Iso.hom_inv_id_assoc, ← Category.assoc,
      hpb.w, Category.assoc, hφfst]

/-- **[Stacks, Tag 0GK5].** Let `k` be a field and let `X` be a separated scheme of finite type
over `k` with `dim(X) ≤ 1`. There is a finite purely inseparable extension `k'/k` (clause 1) such
that the normalization of `X_{k'}` (clause 2) is a dense open subscheme (clause 3) of a finite
disjoint union of schemes `Ȳᵢ`, each smooth, H-projective and geometrically irreducible of
dimension at most one (clause 5) over a finite separable extension `k'ᵢ/k'` (clause 4), the whole
diagram commuting over `Spec k'`. -/
@[stacks 0GK5, ega "IV 17.15.14" "special case", sga "4 XIV 1.11" "special case"]
public theorem exists_isPurelyInseparable_dense_openImmersion_smooth_projective
    (k : Type u) [Field k] {X : Scheme.{u}} (p : X ⟶ Spec (.of k))
    [IsSeparated p] [LocallyOfFiniteType p] [QuasiCompact p]
    (hdim : topologicalKrullDim (X : Type u) ≤ 1) :
    ∃ (k' : Type u) (_ : Field k') (_ : Algebra k k') (_ : Module.Finite k k')
      (_ : IsPurelyInseparable k k') (ι : Type u) (_ : Finite ι) (Ybar : ι → Scheme.{u})
      (sbar : (∐ Ybar) ⟶ Spec (.of k'))
      (K : ι → Type u) (_ : ∀ i, Field (K i)) (_ : ∀ i, Algebra k' (K i))
      (_ : ∀ i, Module.Finite k' (K i)) (_ : ∀ i, Algebra.IsSeparable k' (K i))
      (rbar : ∀ i, Ybar i ⟶ Spec (.of (K i)))
      (j : normalizationSchemeOverField k' (pullback.fst (spectrumMap k k') p) ⟶ ∐ Ybar)
      (_ : IsOpenImmersion j),
      Dense (Set.range j.base) ∧
        j ≫ sbar = normalizationOverField k' (pullback.fst (spectrumMap k k') p) ≫
            pullback.fst (spectrumMap k k') p ∧
          (∀ i, rbar i ≫ Spec.map (CommRingCat.ofHom (algebraMap k' (K i)))
              = Sigma.ι Ybar i ≫ sbar) ∧
            ∀ i, Smooth (rbar i) ∧ IsProjectiveMorphism (rbar i) ∧
              GeometricallyIrreducible (rbar i) ∧ topologicalKrullDim (Ybar i : Type u) ≤ 1 := by
  classical
  -- The reduction of `X`, a reduced scheme homeomorphic to `X` and closed in it.
  have hsurjα : Function.Surjective X.nilradical.subschemeι := fun x =>
    Set.mem_range.mp (by rw [X.nilradical.range_subschemeι, Scheme.support_nilradical]; trivial)
  let : Surjective X.nilradical.subschemeι := ⟨hsurjα⟩
  have : AlgebraicGeometry.IsReduced X.nilradical.subscheme :=
    isReduced_nilradical_subscheme X
  have hdim₀ : topologicalKrullDim (X.nilradical.subscheme : Type u) ≤ 1 :=
    (IsHomeomorph.topologicalKrullDim_eq _
      ((X.nilradical.subschemeι.isClosedEmbedding.isEmbedding.toHomeomorphOfSurjective
        hsurjα).isHomeomorph)).le.trans hdim
  obtain ⟨k', hfield, halg, hfink, hpi, ι, hfinι, Ybar, sbar, K, fieldK, algK, finK, sepK,
    rbar, j₀, hj₀open, hdense₀, hj₀fac, hrbar, hprops⟩ :=
    exists_isPurelyInseparable_dense_openImmersion_smooth_projective_of_isReduced k
      (X.nilradical.subschemeι ≫ p) hdim₀
  let : Field k' := hfield
  let : Algebra k k' := halg
  let : Module.Finite k k' := hfink
  let : IsPurelyInseparable k k' := hpi
  let := hj₀open
  -- The base change of the closed immersion of the reduction.
  set β := pullback.map (spectrumMap k k') (X.nilradical.subschemeι ≫ p) (spectrumMap k k') p
      (𝟙 _) X.nilradical.subschemeι (𝟙 _)
      ((Category.comp_id _).trans (Category.id_comp _).symm)
      ((Category.comp_id _).trans rfl) with hβdef
  have hcompCI : MorphismProperty.IsStableUnderComposition @IsClosedImmersion :=
    ⟨fun a c ha hc => by have := ha; have := hc; infer_instance⟩
  have hcompSurj : MorphismProperty.IsStableUnderComposition @Surjective :=
    ⟨fun a c ha hc => by have := ha; have := hc; infer_instance⟩
  have hβclosed : IsClosedImmersion β :=
    pullbackMap_spectrumMap (@IsClosedImmersion) rfl inferInstance inferInstance
  have hβsurj : Surjective β :=
    pullbackMap_spectrumMap (@Surjective) rfl inferInstance inferInstance
  let := hβclosed
  let := hβsurj
  have hβfst : β ≫ pullback.fst (spectrumMap k k') p
      = pullback.fst (spectrumMap k k') (X.nilradical.subschemeι ≫ p) := by
    rw [hβdef, pullback.lift_fst, Category.comp_id]
  -- The reductions of the two base changes agree.
  have hrmap : IsIso (Scheme.reductionMap' β) :=
    Scheme.reductionMap'_isIso_of_isClosedImmersion_of_surjective β
  let := hrmap
  have hrfac : Scheme.reductionMap' β ≫ ((pullback (spectrumMap k k') p :
        Scheme.{u}).nilradical.subschemeι ≫ pullback.fst (spectrumMap k k') p)
      = (pullback (spectrumMap k k') (X.nilradical.subschemeι ≫ p) :
          Scheme.{u}).nilradical.subschemeι
        ≫ pullback.fst (spectrumMap k k') (X.nilradical.subschemeι ≫ p) := by
    rw [← Category.assoc, Scheme.reductionMap'_comp_subschemeι, Category.assoc, hβfst]
  have : AlgebraicGeometry.IsReduced
      (pullback (spectrumMap k k') (X.nilradical.subschemeι ≫ p) :
        Scheme.{u}).nilradical.subscheme :=
    isReduced_nilradical_subscheme _
  have : AlgebraicGeometry.IsReduced
      (pullback (spectrumMap k k') p : Scheme.{u}).nilradical.subscheme :=
    isReduced_nilradical_subscheme _
  obtain ⟨ε, hε⟩ := exists_iso_normalizationSchemeOverField_of_iso k'
    ((pullback (spectrumMap k k') (X.nilradical.subschemeι ≫ p) :
        Scheme.{u}).nilradical.subschemeι
      ≫ pullback.fst (spectrumMap k k') (X.nilradical.subschemeι ≫ p))
    ((pullback (spectrumMap k k') p : Scheme.{u}).nilradical.subschemeι
      ≫ pullback.fst (spectrumMap k k') p)
    (asIso (Scheme.reductionMap' β)) hrfac
  -- The normalization only sees the reduction.
  obtain ⟨d, hd⟩ := Scheme.exists_normalizationScheme_iso_reduction
    (pullback (spectrumMap k k') p : Scheme.{u})
    (finite_irreducibleComponents_of_locallyOfFiniteType k' (pullback.fst (spectrumMap k k') p))
  obtain ⟨d₀, hd₀⟩ := Scheme.exists_normalizationScheme_iso_reduction
    (pullback (spectrumMap k k') (X.nilradical.subschemeι ≫ p) : Scheme.{u})
    (finite_irreducibleComponents_of_locallyOfFiniteType k'
      (pullback.fst (spectrumMap k k') (X.nilradical.subschemeι ≫ p)))
  refine ⟨k', hfield, halg, hfink, hpi, ι, hfinι, Ybar, sbar, K, fieldK, algK, finK, sepK, rbar,
    (d ≪≫ ε.symm ≪≫ d₀.symm).hom ≫ j₀, inferInstance, ?_, ?_, hrbar, hprops⟩
  · rwa [range_comp_base_of_isIso]
  · -- Re-ascribe the two reduction isomorphisms to the `normalizationOverField` spelling; the
    -- finiteness hypotheses are propositions, so the two spellings are definitionally equal.
    have hd' : d.hom ≫ normalizationOverField k'
          ((pullback (spectrumMap k k') p : Scheme.{u}).nilradical.subschemeι
            ≫ pullback.fst (spectrumMap k k') p)
          ≫ (pullback (spectrumMap k k') p : Scheme.{u}).nilradical.subschemeι
        = normalizationOverField k' (pullback.fst (spectrumMap k k') p) := hd
    have hd₀' : d₀.hom ≫ normalizationOverField k'
          ((pullback (spectrumMap k k') (X.nilradical.subschemeι ≫ p) :
              Scheme.{u}).nilradical.subschemeι
            ≫ pullback.fst (spectrumMap k k') (X.nilradical.subschemeι ≫ p))
          ≫ (pullback (spectrumMap k k') (X.nilradical.subschemeι ≫ p) :
              Scheme.{u}).nilradical.subschemeι
        = normalizationOverField k'
            (pullback.fst (spectrumMap k k') (X.nilradical.subschemeι ≫ p)) := hd₀
    rw [Category.assoc, hj₀fac, ← hd₀', ← hd']
    simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id_assoc]
    rw [← hε]
    simp only [Iso.inv_hom_id_assoc]

end AlgebraicGeometry

end
