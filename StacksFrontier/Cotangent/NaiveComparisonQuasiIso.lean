module

public import StacksFrontier.Algebra.Homology.HomologyIsoOfVanishing
public import StacksFrontier.Cotangent.NaiveComparisonHomologyNegOne
public import StacksFrontier.Cotangent.NaiveComparisonIndependence

/-!
# The comparison map of Tag 08R9 on `H^{-1}`, at the canonical presentation

`Stacks.Cotangent.evalCone` is the evaluation at an object `U = (P → B)` of `C_{B/A}` of the
two-term complex `𝒥/𝒥² → Ω`, as a map of cochain complexes from the naive cotangent complex of
`U` into the mapping cone of `d` on the standard resolution; the comparison map of Tag 08R9 is
its image in `D(B)`, followed by the truncation. This file proves that at the object
`P₀ = A[B] → B` — the degree-zero term of the standard resolution — that map is an isomorphism
on cohomology in degree `-1`.

The route is the factorisation through the cone of `Ker(d) ⟶ 0`:

* `Stacks.Cotangent.isIso_homologyMap_kernelConeToCotangentCone` says that
  `cone (Ker(d) ⟶ 0) ⟶ cone(d)` is an isomorphism on `H^{-1}`, by
  `CochainComplex.mappingCone.isIso_homologyMap_mapFromZero`;
* `Stacks.Cotangent.isIso_homologyMap_kernelConeToNaive` says the same for the comparison
  `cone (Ker(d) ⟶ 0) ⟶ NL(P₀ → B)`, which in degree `-1` is the inclusion of `Ker(d)` in degree
  `0`, hence a kernel of the differential of the two-term complex;
* the two composites agree in degree `-1`, and a map on homology in a degree depends only on the
  component of the chain map in that degree (`HomologicalComplex.homologyMap_congr`).

The two chain maps do *not* agree: the two-term complex vanishes in cohomological degrees `≤ -2`,
where `Stacks.Cotangent.kernelConeToCotangentCone` does not. Only the degree `-1` components
agree, which is all the homology in that degree sees.

## Main definitions

* `Stacks.Cotangent.kernelConeToNaive`: the comparison `cone (Ker(d) ⟶ 0) ⟶ NL(P₀ → B)`.

## Main results

* `Stacks.Cotangent.isIso_homologyMap_kernelConeToNaive`: it is an isomorphism on `H^{-1}`.
* `Stacks.Cotangent.isIso_homologyMap_evalCone_conormalExtension`: **the evaluation at
  `P₀ → B` is an isomorphism on `H^{-1}`**, for every morphism of extensions
  `(P₀ → B) ⟶ (P₀ → B)` the construction may be given.

## Implementation notes

The degree-zero term of the cotangent complex is written `Stacks.Cotangent.cotangentTerm` on the
standard-resolution side and `Algebra.Extension.CotangentSpace` on the two-term-complex side.
These are the same module, but only definitionally so, and at the single object `⦋0⦌` the unifier
does not see it within the elaboration budget: it would have to evaluate the standard resolution
at a simplex. `Stacks.Cotangent.cotangentTermIsoCotangentSpace` crosses the two spellings once
and for all, in an *arbitrary* simplicial degree, where the identification is immediate; every
composite below is then written through that isomorphism and matches on the nose.

## References

* [Stacks Project, Tag 08R9](https://stacks.math.columbia.edu/tag/08R9)
* [Stacks Project, Tag 08RB](https://stacks.math.columbia.edu/tag/08RB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial

open scoped ZeroObject

universe u v

namespace Stacks.Cotangent

open CommAlgCat

variable (A : Type u) [CommRing A] (B : CommAlgCat.{max u v} A)

/-! ### The two-term complex at `P₀ → B` against the complexes on the standard resolution -/

/-- In cohomological degree `-1` the two-term complex at `P₀ → B` is the degree-zero term of the
conormal complex: both are `𝒥₀/𝒥₀²`. -/
def conormalXZeroIsoNaiveXNegOne :
    (conormalComplex A B).X 0 ≅
      (Algebra.Extension.naiveComplex (conormalExtension A B (op ⦋0⦌))).X (-1) :=
  conormalComplexXZeroIso A B ≪≫
    (Algebra.Extension.naiveComplexXNegOneIso (conormalExtension A B (op ⦋0⦌))).symm

/-- **`Stacks.Cotangent.cotangentTerm` in simplicial degree `n` is the cotangent space of the
extension `Pₙ → B`**: the identity map, the two being the same module under the two spellings
this development uses for it.

The identification is made in an *arbitrary* simplicial degree. Were it made at `⦋0⦌`, the
unifier would be asked to see through the standard resolution evaluated at a simplex, which it
does not do within the elaboration budget; stated for a variable `n` it is immediate, and the two
spellings are never mixed again, every composite below matching on the nose. -/
def cotangentTermIsoCotangentSpace (n : SimplexCategoryᵒᵖ) :
    cotangentTerm A B n ≅ ModuleCat.of ↥B ((conormalExtension A B n).CotangentSpace) :=
  Iso.refl _

/-- **The map `d` in simplicial degree `n`, read through that identification, is
`Algebra.Extension.cotangentComplex` of the extension `Pₙ → B`.** -/
theorem conormalToCotangentApp_comp_cotangentTermIso (n : SimplexCategoryᵒᵖ) :
    conormalToCotangentApp A B n ≫ (cotangentTermIsoCotangentSpace A B n).hom =
      ModuleCat.ofHom (conormalExtension A B n).cotangentComplex :=
  Category.comp_id _

/-- In cohomological degree `0` the two-term complex at `P₀ → B` is the degree-zero term of the
cotangent complex: both are `Ω[P₀⁄A] ⊗[P₀] B`. -/
def cotangentXZeroIsoNaiveXZero :
    (cotangentComplex A B).X 0 ≅
      (Algebra.Extension.naiveComplex (conormalExtension A B (op ⦋0⦌))).X 0 :=
  cotangentComplexXZeroIso A B ≪≫ cotangentTermIsoCotangentSpace A B (op ⦋0⦌) ≪≫
    (Algebra.Extension.naiveComplexXZeroIso (conormalExtension A B (op ⦋0⦌))).symm

/-- Those two identifications carry `d` in cohomological degree `0` to the differential of the
two-term complex at `P₀ → B`. -/
theorem conormalToCotangentComplex_f_zero_comm :
    (conormalToCotangentComplex A B).f 0 ≫ (cotangentXZeroIsoNaiveXZero A B).hom =
      (conormalXZeroIsoNaiveXNegOne A B).hom ≫
        (Algebra.Extension.naiveComplex (conormalExtension A B (op ⦋0⦌))).d (-1) 0 := by
  rw [conormalToCotangentComplex_f_zero, Algebra.Extension.naiveComplex_d,
    cotangentXZeroIsoNaiveXZero, conormalXZeroIsoNaiveXNegOne,
    ← conormalToCotangentApp_comp_cotangentTermIso A B (op ⦋0⦌)]
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id_assoc]

/-- `Ker(d)` in cohomological degree `0` is a kernel of `d` there. -/
def isLimitKernelForkConormalKernelIota :
    IsLimit (KernelFork.ofι ((conormalKernelIota A B).f 0)
      (show (conormalKernelIota A B).f 0 ≫ (conormalToCotangentComplex A B).f 0 = 0 by
        rw [← HomologicalComplex.comp_f,
          conormalKernelIota_comp_conormalToCotangentComplex]
        simp)) := by
  have h₁ := (HomologicalComplex.shortExact_iff_degreewise_shortExact _).1
    (shortExact_conormalKernelImage A B) 0
  have h₂ := (HomologicalComplex.shortExact_iff_degreewise_shortExact _).1
    (shortExact_conormalImageCokernel A B) 0
  have hm₁ := h₁.mono_f
  have hm₂ := h₂.mono_f
  haveI : Mono ((conormalImageIota A B).f 0) := by assumption
  have hker : IsLimit (KernelFork.ofι ((conormalKernelIota A B).f 0)
      (show (conormalKernelIota A B).f 0 ≫ (conormalToImage A B).f 0 = 0 by
        rw [← HomologicalComplex.comp_f, conormalKernelIota_comp_conormalToImage]
        simp)) := h₁.exact.fIsKernel
  refine isKernelCompMono hker ((conormalImageIota A B).f 0) ?_
  rw [← HomologicalComplex.comp_f, conormalToImage_comp]

/-! ### The comparison into the two-term complex -/

/-- The degree `-1` component of the comparison from the cone of `Ker(d) ⟶ 0` into the two-term
complex at `P₀ → B`: the inclusion of `Ker(d)` in degree `0`. -/
def kernelConeToNaiveNegOne :
    (kernelCone A B).X (-1) ⟶
      (Algebra.Extension.naiveComplex (conormalExtension A B (op ⦋0⦌))).X (-1) :=
  inv ((CochainComplex.mappingCone.inl
      (0 : conormalKernelComplex A B ⟶
        (0 : CochainComplex (ModuleCat.{max u v} B) ℤ))).v 0 (-1) (by norm_num)) ≫
    (conormalKernelIota A B).f 0 ≫ (conormalXZeroIsoNaiveXNegOne A B).hom

/-- The degree `-1` component of the comparison is killed by the differential of the two-term
complex, `Ker(d)` being killed by `d`. -/
theorem kernelConeToNaiveNegOne_comp_d :
    kernelConeToNaiveNegOne A B ≫
        (Algebra.Extension.naiveComplex (conormalExtension A B (op ⦋0⦌))).d (-1) 0 = 0 := by
  have h0 : (conormalKernelIota A B).f 0 ≫ (conormalToCotangentComplex A B).f 0 = 0 := by
    rw [← HomologicalComplex.comp_f, conormalKernelIota_comp_conormalToCotangentComplex]
    simp
  rw [kernelConeToNaiveNegOne, Category.assoc, Category.assoc,
    ← conormalToCotangentComplex_f_zero_comm,
    ← Category.assoc ((conormalKernelIota A B).f 0) ((conormalToCotangentComplex A B).f 0)
      (cotangentXZeroIsoNaiveXZero A B).hom,
    h0, zero_comp, comp_zero]

/-- The differential of the cone of `Ker(d) ⟶ 0` out of cohomological degree `-2` vanishes,
because that of `Ker(d)` out of degree `-1` does. -/
theorem kernelCone_d : (kernelCone A B).d (-2) (-1) = 0 := by
  have h := CochainComplex.mappingCone.inl_v_d
    (0 : conormalKernelComplex A B ⟶ (0 : CochainComplex (ModuleCat.{max u v} B) ℤ))
    (-1) (-2) 0 (by norm_num) (by norm_num)
  rw [conormalKernelComplex_d] at h
  simp only [HomologicalComplex.zero_f, zero_comp, sub_zero] at h
  rw [← Category.id_comp ((kernelCone A B).d (-2) (-1)),
    ← IsIso.inv_hom_id ((CochainComplex.mappingCone.inl
      (0 : conormalKernelComplex A B ⟶
        (0 : CochainComplex (ModuleCat.{max u v} B) ℤ))).v (-1) (-2) (by norm_num)),
    Category.assoc, h, comp_zero]

/-- The components of the comparison into the two-term complex: the inclusion of `Ker(d)` in
degree `-1`, zero elsewhere. -/
def kernelConeToNaiveComponent (i : ℤ) :
    (kernelCone A B).X i ⟶
      (Algebra.Extension.naiveComplex (conormalExtension A B (op ⦋0⦌))).X i :=
  if h : i = -1 then eqToHom (by rw [h]) ≫ kernelConeToNaiveNegOne A B ≫ eqToHom (by rw [h])
  else 0

/-- In degree `-1`, the component of the comparison is `kernelConeToNaiveNegOne`. -/
theorem kernelConeToNaiveComponent_negOne :
    kernelConeToNaiveComponent A B (-1) = kernelConeToNaiveNegOne A B := by
  rw [kernelConeToNaiveComponent, dif_pos rfl, eqToHom_refl, eqToHom_refl, Category.id_comp,
    Category.comp_id]

/-- Outside degree `-1`, the component of the comparison is zero. -/
theorem kernelConeToNaiveComponent_eq_zero (i : ℤ) (h : i ≠ -1) :
    kernelConeToNaiveComponent A B i = 0 := by
  rw [kernelConeToNaiveComponent, dif_neg h]

/-- **The comparison from the cone of `Ker(d) ⟶ 0` into the two-term complex at `P₀ → B`.** -/
def kernelConeToNaive :
    kernelCone A B ⟶ Algebra.Extension.naiveComplex (conormalExtension A B (op ⦋0⦌)) where
  f := kernelConeToNaiveComponent A B
  comm' i j hij := by
    have hij' : i + 1 = j := hij
    by_cases hj : j = 0
    · subst hj
      have hi : i = -1 := by lia
      subst hi
      rw [kernelConeToNaiveComponent_eq_zero A B 0 (by decide), comp_zero,
        kernelConeToNaiveComponent_negOne, kernelConeToNaiveNegOne_comp_d]
    · by_cases hj1 : j = -1
      · subst hj1
        have hi : i = -2 := by lia
        subst hi
        rw [kernelCone_d, zero_comp, kernelConeToNaiveComponent_eq_zero A B (-2) (by decide),
          zero_comp]
      · exact (Algebra.Extension.isZero_naiveComplex_X _ j hj1 hj).eq_of_tgt _ _

/-- The degree `-1` component of `kernelConeToNaive` is `kernelConeToNaiveNegOne`. -/
theorem kernelConeToNaive_f_negOne :
    (kernelConeToNaive A B).f (-1) = kernelConeToNaiveNegOne A B :=
  kernelConeToNaiveComponent_negOne A B

/-! ### The comparison into the two-term complex is a homology isomorphism in degree `-1` -/

/-- The inclusion of `Ker(d)` in cohomological degree `0` is a monomorphism, being the first map
of a short exact sequence there. -/
theorem mono_conormalKernelIota_f_zero : Mono ((conormalKernelIota A B).f 0) := by
  have h₁ := (HomologicalComplex.shortExact_iff_degreewise_shortExact _).1
    (shortExact_conormalKernelImage A B) 0
  have hm₁ := h₁.mono_f
  assumption

/-- The degree `-1` component of the comparison is a monomorphism: it is the inclusion of
`Ker(d)` in degree `0`, composed with two isomorphisms. -/
theorem mono_kernelConeToNaiveNegOne : Mono (kernelConeToNaiveNegOne A B) := by
  have := mono_conormalKernelIota_f_zero A B
  rw [kernelConeToNaiveNegOne]
  infer_instance

/-- The degree `-1` component of the comparison is a kernel of the differential of the two-term
complex: it is the inclusion of `Ker(d)` in degree `0`, read through the identification of the
degree `-1` term of the two-term complex with `𝒥₀/𝒥₀²`. -/
def isLimitKernelForkKernelConeToNaiveNegOne :
    IsLimit (KernelFork.ofι (kernelConeToNaiveNegOne A B)
      (kernelConeToNaiveNegOne_comp_d A B)) := by
  haveI := mono_kernelConeToNaiveNegOne A B
  refine KernelFork.IsLimit.ofι' _ _ (fun {T} k hk => ?_)
  have hk' : (k ≫ (conormalXZeroIsoNaiveXNegOne A B).inv) ≫
      (conormalToCotangentComplex A B).f 0 = 0 := by
    rw [Category.assoc, ← cancel_mono (cotangentXZeroIsoNaiveXZero A B).hom, Category.assoc,
      Category.assoc, conormalToCotangentComplex_f_zero_comm, Iso.inv_hom_id_assoc, hk,
      zero_comp]
  obtain ⟨w, hw⟩ := KernelFork.IsLimit.lift'
    (isLimitKernelForkConormalKernelIota A B) _ hk'
  refine ⟨w ≫ (CochainComplex.mappingCone.inl
    (0 : conormalKernelComplex A B ⟶
      (0 : CochainComplex (ModuleCat.{max u v} B) ℤ))).v 0 (-1) (by norm_num), ?_⟩
  rw [kernelConeToNaiveNegOne, Category.assoc, IsIso.hom_inv_id_assoc, ← Category.assoc,
    show w ≫ (conormalKernelIota A B).f 0 = k ≫ (conormalXZeroIsoNaiveXNegOne A B).inv from hw,
    Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- The degree `-1` component of the comparison is killed by the differential of the two-term
complex, stated at the component of the chain map rather than at
`Stacks.Cotangent.kernelConeToNaiveNegOne`. -/
theorem kernelConeToNaive_f_negOne_comp_d :
    (kernelConeToNaive A B).f (-1) ≫
        (Algebra.Extension.naiveComplex (conormalExtension A B (op ⦋0⦌))).d (-1) 0 = 0 := by
  rw [kernelConeToNaive_f_negOne]
  exact kernelConeToNaiveNegOne_comp_d A B

/-- The degree `-1` component of the comparison is a kernel of the differential of the two-term
complex, stated at the component of the chain map. The lift is that of
`Stacks.Cotangent.isLimitKernelForkKernelConeToNaiveNegOne`, carried across the identification of
the two by `Stacks.Cotangent.kernelConeToNaive_f_negOne`. -/
def isLimitKernelForkKernelConeToNaive :
    IsLimit (KernelFork.ofι ((kernelConeToNaive A B).f (-1))
      (kernelConeToNaive_f_negOne_comp_d A B)) := by
  haveI : Mono ((kernelConeToNaive A B).f (-1)) := by
    rw [kernelConeToNaive_f_negOne]
    exact mono_kernelConeToNaiveNegOne A B
  refine KernelFork.IsLimit.ofι' _ _ (fun {T} k hk => ?_)
  obtain ⟨l, hl⟩ := KernelFork.IsLimit.lift'
    (isLimitKernelForkKernelConeToNaiveNegOne A B) k hk
  exact ⟨l, by rw [kernelConeToNaive_f_negOne]; exact hl⟩

/-- **The comparison from the cone of `Ker(d) ⟶ 0` into the two-term complex at `P₀ → B` is an
isomorphism on `H^{-1}`.** Both sides compute `Ker(d)` in degree `0`: the cone has no term in
degree `0` and no differential into degree `-1`, and the two-term complex has no term in degree
`-2`, so its `H^{-1}` is the kernel of its differential. -/
theorem isIso_homologyMap_kernelConeToNaive :
    IsIso (HomologicalComplex.homologyMap (kernelConeToNaive A B) (-1)) := by
  refine HomologicalComplex.isIso_homologyMap_of_isKernel (kernelConeToNaive A B) (-1) (-2) 0
    ((ComplexShape.up ℤ).prev_eq' (show (ComplexShape.up ℤ).Rel (-2) (-1) by norm_num))
    ((ComplexShape.up ℤ).next_eq' (show (ComplexShape.up ℤ).Rel (-1) 0 by norm_num))
    ?_ (kernelCone_d A B) ?_ ?_ ?_
  · rw [CochainComplex.mappingCone.isZero_X_iff]
    exact ⟨HomologicalComplex.isZero_extend_X _ _ 1
      ((ComplexShape.notMem_range_embeddingUpIntLE_iff (0 : ℤ) 1).2 (by norm_num)),
      CochainComplex.mappingCone.isZero_zero_X 0⟩
  · exact (Algebra.Extension.isZero_naiveComplex_X (conormalExtension A B (op ⦋0⦌)) (-2)
      (by decide) (by decide)).eq_of_src _ _
  · exact kernelConeToNaive_f_negOne_comp_d A B
  · exact isLimitKernelForkKernelConeToNaive A B

/-! ### The evaluation at `P₀ → B` is an isomorphism on `H^{-1}` -/

/-- The evaluation of `𝒥/𝒥²` at `P₀ → B` along the identity is the identity. -/
theorem evalCotangent_id :
    evalCotangent A B (conormalExtension A B (op ⦋0⦌))
        (Algebra.Extension.Hom.id (conormalExtension A B (op ⦋0⦌))) = 𝟙 _ := by
  rw [evalCotangent, Algebra.Extension.Cotangent.map_id]
  rfl

/-- The degree `-1` components of `kernelConeToNaive ≫ evalCone` and of
`kernelConeToCotangentCone` agree: both are the inclusion of `Ker(d)` in degree `0` into the
`𝒥₀/𝒥₀²` summand of the cone. The two chain maps themselves do not agree, the two-term complex
vanishing in degrees `≤ -2`. -/
theorem kernelConeToNaive_comp_evalCone_f_negOne :
    (kernelConeToNaive A B ≫ evalCone A B (conormalExtension A B (op ⦋0⦌))
        (Algebra.Extension.Hom.id (conormalExtension A B (op ⦋0⦌)))).f (-1) =
      (kernelConeToCotangentCone A B).f (-1) := by
  rw [HomologicalComplex.comp_f, kernelConeToNaive_f_negOne, evalCone_f_negOne, evalConeNegOne,
    evalCotangent_id, kernelConeToNaiveNegOne, conormalXZeroIsoNaiveXNegOne]
  rw [← cancel_epi ((CochainComplex.mappingCone.inl
    (0 : conormalKernelComplex A B ⟶
      (0 : CochainComplex (ModuleCat.{max u v} B) ℤ))).v 0 (-1) (by norm_num))]
  rw [kernelConeToCotangentCone, CochainComplex.mappingCone.inl_v_mapFromZero_f]
  simp

/-- **The evaluation at `P₀ → B` of the two-term complex is an isomorphism on cohomology in
degree `-1`.** This is the degree `-1` content of Lemma 08RB: the comparison map of Tag 08R9 at
the object `P₀ → B` of `C_{B/A}` — which is the map `c` of that lemma — induces an isomorphism
`H¹(NL_{B/A}) ≅ H^{-1}(L_{B/A})`.

The statement does not depend on the morphism of extensions the construction is given, the two
evaluations being chain homotopic (`Stacks.Cotangent.evalConeHomotopy`). -/
theorem isIso_homologyMap_evalCone_conormalExtension
    (hom : (conormalExtension A B (op ⦋0⦌)).Hom (conormalExtension A B (op ⦋0⦌))) :
    IsIso (HomologicalComplex.homologyMap
      (evalCone A B (conormalExtension A B (op ⦋0⦌)) hom) (-1)) := by
  rw [(evalConeHomotopy A B (conormalExtension A B (op ⦋0⦌)) hom
    (Algebra.Extension.Hom.id (conormalExtension A B (op ⦋0⦌)))).homologyMap_eq (-1)]
  have hcomp : HomologicalComplex.homologyMap (kernelConeToNaive A B) (-1) ≫
      HomologicalComplex.homologyMap (evalCone A B (conormalExtension A B (op ⦋0⦌))
        (Algebra.Extension.Hom.id (conormalExtension A B (op ⦋0⦌)))) (-1) =
      HomologicalComplex.homologyMap (kernelConeToCotangentCone A B) (-1) := by
    rw [← HomologicalComplex.homologyMap_comp]
    exact HomologicalComplex.homologyMap_congr (-1)
      (kernelConeToNaive_comp_evalCone_f_negOne A B)
  have := isIso_homologyMap_kernelConeToNaive A B
  have := isIso_homologyMap_kernelConeToCotangentCone A B
  exact IsIso.of_isIso_fac_left hcomp

end Stacks.Cotangent

end
