module

public import StacksFrontier.AlgebraicGeometry.Variety.Curve.GraphFibreDegree
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.DivisorDegree
public import StacksFrontier.AlgebraicGeometry.Divisors.DivisorPicardClassPullback
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.Reduced
public import StacksFrontier.AlgebraicGeometry.Spaces.EffectiveCartierPullbackCriteria
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.ClassGroupPicardBaseChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.SelfMapFixedPointTrace
public import StacksFrontier.RingTheory.TotallySplit.PrimeSpectrum
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The intersection number `V(φ)` counts fixed points when they are simple

Let `f : C ⟶ Spec k` be a smooth proper curve over an algebraically closed field and `φ : C ⟶ C`
a morphism over `k`, with graph `Γ_φ : C ⟶ C ×_k C`. The *fixed-point locus* of `φ` is the
scheme-theoretic inverse image `Γ_φ^{-1}(Δ_C)` of the diagonal. Its `T`-points are the morphisms
`y : T ⟶ C` with `y ≫ φ = y`, so it is the equalizer of `𝟙` and `φ`.

If `φ` moves some point of `C`, the fixed-point locus is an effective Cartier divisor on `C`.
The generic point of `C` is then not carried into the diagonal, and it is the only weakly
associated point of the integral scheme `C` ([Stacks, Tag 02OO]). The intersection number
`V(φ) = (𝒪(Δ_C) · Γ_φ)` of [Stacks, Tag 03U1] is the degree of `Γ_φ^* 𝒪(Δ_C) = 𝒪(Γ_φ^{-1}Δ_C)`,
which is the dimension over `k` of the ring of functions on the fixed-point locus. When that
locus is reduced, each fixed point counts once. A finite reduced algebra over an algebraically
closed field is a product of copies of the field, so the dimension is the number of `k`-points
of the locus, and those are the fixed `k`-points of `φ`:

`V(φ) = #{c ∈ C(k) : φ(c) = c}`.

This is the statement "the fixed points of `φ` all have multiplicity one" of the proof of
[Stacks, Tag 03UJ], applied there to the geometric Frobenius.

## Main definitions

* `AlgebraicGeometry.CurveGraph.fixedPointLocus`: `Γ_φ^{-1}(Δ_C)`, as an ideal sheaf on `C`.

## Main results

* `Algebra.IsFiniteSplit.of_isReduced_of_isAlgClosed`: a finite reduced algebra over an
  algebraically closed field is totally split.
* `AlgebraicGeometry.natCard_sections_eq_finrank`: a finite reduced scheme over an algebraically
  closed field `k` has `dim_k Γ(Z, 𝒪_Z)` points with values in `k`.
* `AlgebraicGeometry.CurveGraph.fixedSectionsEquivFixedPointLocus`: the `k`-points of the
  fixed-point locus are the fixed `k`-points of `φ`.
* `AlgebraicGeometry.CurveGraph.isPullbackDefined_graph_diagonalDivisor`: the fixed-point locus
  of a morphism that moves some point is an effective Cartier divisor.
* `AlgebraicGeometry.CurveGraph.fixedPointIntersection_eq_natCard_fixedSections`:
  `V(φ) = #{c ∈ C(k) : φ(c) = c}` when the fixed-point locus is reduced.

## References

* [Stacks Project, Tag 03U1](https://stacks.math.columbia.edu/tag/03U1)
* [Stacks Project, Tag 03UJ](https://stacks.math.columbia.edu/tag/03UJ)
* [Stacks Project, Tag 02OO](https://stacks.math.columbia.edu/tag/02OO)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace Algebra.IsFiniteSplit

/-- **A finite reduced algebra over an algebraically closed field is totally split.** It is
Artinian and reduced, so it is the product of its residue fields at the maximal ideals. Each
residue field is finite over the algebraically closed field, so it is that field. -/
theorem of_isReduced_of_isAlgClosed (K A : Type*) [Field K] [IsAlgClosed K] [CommRing A]
    [Algebra K A] [Module.Finite K A] [IsReduced A] : Algebra.IsFiniteSplit K A := by
  have : IsArtinianRing A := IsArtinianRing.of_finite K A
  have hbij : ∀ I : MaximalSpectrum A, Function.Bijective (algebraMap K (A ⧸ I.asIdeal)) := by
    intro I
    have := I.isMaximal
    let := Ideal.Quotient.field I.asIdeal
    exact IsAlgClosed.ringHom_bijective_of_isIntegral _
      (Algebra.IsIntegral.isIntegral (R := K) (A := A ⧸ I.asIdeal) ·)
  let e : A ≃ₐ[K] (MaximalSpectrum A → K) :=
    ((IsArtinianRing.equivPi A).restrictScalars K).trans
      (AlgEquiv.piCongrRight fun I => (AlgEquiv.ofBijective (Algebra.ofId K _) (hbij I)).symm)
  exact of_algEquiv e.symm

end Algebra.IsFiniteSplit

namespace AlgebraicGeometry

/-- **A finite reduced scheme over an algebraically closed field `k` has `dim_k Γ(Z, 𝒪_Z)`
points with values in `k`.** `Z` is affine, so its `k`-points are the `k`-algebra maps
`Γ(Z, 𝒪_Z) ⟶ k`, and `Γ(Z, 𝒪_Z)` is totally split. -/
theorem natCard_sections_eq_finrank {k : Type u} [Field k] [IsAlgClosed k] {Z : Scheme.{u}}
    (q : Z ⟶ Spec (.of k)) [IsFinite q] [IsReduced Z] :
    letI : Algebra k Γ(Z, ⊤) := ((Scheme.ΓSpecIso (.of k)).inv ≫ q.appTop).hom.toAlgebra
    Nat.card {s : Spec (.of k) ⟶ Z // s ≫ q = 𝟙 _} = Module.finrank k Γ(Z, ⊤) := by
  let : Algebra k Γ(Z, ⊤) := ((Scheme.ΓSpecIso (.of k)).inv ≫ q.appTop).hom.toAlgebra
  have : IsAffine Z := isAffine_of_isAffineHom q
  have hfin : Module.Finite k Γ(Z, ⊤) := by
    have hiso : Function.Surjective ((Scheme.ΓSpecIso (CommRingCat.of k)).inv).hom :=
      (ConcreteCategory.bijective_of_isIso ((Scheme.ΓSpecIso (CommRingCat.of k)).inv)).surjective
    have h : ((Scheme.ΓSpecIso (.of k)).inv ≫ q.appTop).hom.Finite := by
      rw [CommRingCat.hom_comp]
      exact RingHom.Finite.comp (Scheme.Hom.finite_appTop q) (RingHom.Finite.of_surjective _ hiso)
    exact h
  have := Algebra.IsFiniteSplit.of_isReduced_of_isAlgClosed k Γ(Z, ⊤)
  rw [← Algebra.IsFiniteSplit.natCard_algHom_eq_finrank]
  -- a section `s` gives the algebra map `s^* : Γ(Z, 𝒪_Z) ⟶ Γ(Spec k, 𝒪) = k`
  have hcomm : ∀ s : {s : Spec (.of k) ⟶ Z // s ≫ q = 𝟙 _},
      (Scheme.ΓSpecIso (.of k)).inv ≫ q.appTop ≫ s.1.appTop ≫ (Scheme.ΓSpecIso (.of k)).hom =
        𝟙 _ := by
    intro s
    rw [← Category.assoc q.appTop, ← Scheme.Hom.comp_appTop, s.2]
    simp
  let Φ : {s : Spec (.of k) ⟶ Z // s ≫ q = 𝟙 _} → (Γ(Z, ⊤) →ₐ[k] k) := fun s =>
    { toRingHom := (s.1.appTop ≫ (Scheme.ΓSpecIso (.of k)).hom).hom
      commutes' := fun c => congrArg (fun φ => φ.hom c) (hcomm s) }
  refine Nat.card_eq_of_bijective Φ ⟨fun s s' h => Subtype.ext (ext_of_isAffine ?_), fun g => ?_⟩
  · have h' : s.1.appTop ≫ (Scheme.ΓSpecIso (.of k)).hom =
        s'.1.appTop ≫ (Scheme.ΓSpecIso (.of k)).hom := by
      ext x
      exact congrArg (fun φ : Γ(Z, ⊤) →ₐ[k] k => φ x) h
    simpa using h'
  · -- the section `Spec g ≫ Z ≅ Spec Γ(Z, 𝒪_Z)`
    let g' : Γ(Z, ⊤) ⟶ CommRingCat.of k := CommRingCat.ofHom g.toRingHom
    let s₀ : Spec (.of k) ⟶ Z := Spec.map g' ≫ Z.isoSpec.inv
    have happ : s₀.appTop = g' ≫ (Scheme.ΓSpecIso (.of k)).inv := by
      have h1 : Z.isoSpec.inv.appTop = (Scheme.ΓSpecIso Γ(Z, ⊤)).inv := by
        have e : Z.isoSpec.inv.appTop ≫ Z.isoSpec.hom.appTop = 𝟙 _ := by
          rw [← Scheme.Hom.comp_appTop, Iso.hom_inv_id, Scheme.Hom.id_appTop]
        have hhom : Z.isoSpec.hom.appTop = (Scheme.ΓSpecIso Γ(Z, ⊤)).hom :=
          Scheme.toSpecΓ_appTop Z
        rw [← Category.comp_id Z.isoSpec.inv.appTop, ← Iso.hom_inv_id (Scheme.ΓSpecIso Γ(Z, ⊤)),
          ← Category.assoc, ← hhom, e, Category.id_comp]
      rw [Scheme.Hom.comp_appTop, h1, ← cancel_mono (Scheme.ΓSpecIso (.of k)).hom,
        Category.assoc, Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc, Category.assoc,
        Iso.inv_hom_id, Category.comp_id]
    have hs₀ : s₀ ≫ q = 𝟙 _ := by
      refine ext_of_isAffine ?_
      rw [Scheme.Hom.comp_appTop, happ, Scheme.Hom.id_appTop,
        ← cancel_epi (Scheme.ΓSpecIso (.of k)).inv, Category.comp_id]
      ext c
      exact congrArg (Scheme.ΓSpecIso (.of k)).inv.hom (g.commutes c)
    refine ⟨⟨s₀, hs₀⟩, AlgHom.ext fun x => ?_⟩
    change (s₀.appTop ≫ (Scheme.ΓSpecIso (.of k)).hom).hom x = g x
    rw [happ, Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rfl

namespace CurveGraph

variable {k : Type u} [Field k] {C : Scheme.{u}} (f : C ⟶ Spec (.of k))

/-- **The fixed-point locus** `Γ_φ^{-1}(Δ_C)` of a morphism `φ : C ⟶ C` over `k`: the inverse
image of the diagonal under the graph. It is the equalizer of `𝟙` and `φ`. -/
def fixedPointLocus (φ : C ⟶ C) (w : φ ≫ f = f) : C.IdealSheafData :=
  (diagonalDivisor f).comap (graph f φ w)

/-- The diagonal, through its closed subscheme, has equal projections. -/
theorem diagonalDivisor_subschemeι_fst [IsSeparated f] :
    (diagonalDivisor f).subschemeι ≫ pullback.fst f f =
      (diagonalDivisor f).subschemeι ≫ pullback.snd f f := by
  let g := graph f (𝟙 C) (Category.id_comp f)
  have hiso : IsIso g.toImage :=
    IsClosedImmersion.isIso_of_ker_eq g g.imageι g.toImage g.toImage_imageι
      (Scheme.IdealSheafData.ker_subschemeι g.ker).symm
  change g.imageι ≫ _ = g.imageι ≫ _
  rw [← cancel_epi g.toImage, g.toImage_imageι_assoc, g.toImage_imageι_assoc, graph_fst, graph_snd]

/-- The fixed-point locus is fixed by `φ`: `ι ≫ φ = ι` for its inclusion `ι`. -/
@[reassoc, sga "1 IX 5.8" "partial"]
theorem fixedPointLocus_subschemeι_comp [IsSeparated f] (φ : C ⟶ C) (w : φ ≫ f = f) :
    (fixedPointLocus f φ w).subschemeι ≫ φ = (fixedPointLocus f φ w).subschemeι := by
  have hι := (diagonalDivisor f).comapIso_hom_fst (graph f φ w)
  have e := fun p : pullback f f ⟶ C =>
    pullback.condition (f := graph f φ w) (g := (diagonalDivisor f).subschemeι) =≫ p
  have e1 := e (pullback.snd f f)
  have e2 := e (pullback.fst f f)
  simp only [Category.assoc, graph_snd, graph_fst, Category.comp_id] at e1 e2
  change ((diagonalDivisor f).comap (graph f φ w)).subschemeι ≫ φ =
    ((diagonalDivisor f).comap (graph f φ w)).subschemeι
  rw [← hι, Category.assoc, e1, e2, diagonalDivisor_subschemeι_fst]

/-- The diagonal `C ⟶ Δ_C`, onto its closed subscheme. -/
def diagonalLift : C ⟶ (diagonalDivisor f).subscheme :=
  (graph f (𝟙 C) (Category.id_comp f)).toImage

/-- The diagonal lift followed by the inclusion of the diagonal is the graph of `𝟙 C`. -/
@[reassoc (attr := simp)]
theorem diagonalLift_subschemeι :
    diagonalLift f ≫ (diagonalDivisor f).subschemeι = graph f (𝟙 C) (Category.id_comp f) :=
  Scheme.Hom.toImage_imageι _

/-- A morphism `y : T ⟶ C` fixed by `φ` factors through the fixed-point locus. -/
def fixedPointLocusLift [IsSeparated f] (φ : C ⟶ C) (w : φ ≫ f = f) {T : Scheme.{u}}
    (y : T ⟶ C) (hy : y ≫ φ = y) : T ⟶ (fixedPointLocus f φ w).subscheme :=
  pullback.lift y (y ≫ diagonalLift f) (by
      rw [Category.assoc, diagonalLift_subschemeι]
      refine pullback.hom_ext ?_ ?_ <;> simp [hy]) ≫
    ((diagonalDivisor f).comapIso (graph f φ w)).inv

/-- The lift of a fixed morphism `y` followed by the inclusion of the fixed-point locus is `y`. -/
@[reassoc (attr := simp), sga "1 IX 5.8" "partial"]
theorem fixedPointLocusLift_subschemeι [IsSeparated f] (φ : C ⟶ C) (w : φ ≫ f = f)
    {T : Scheme.{u}} (y : T ⟶ C) (hy : y ≫ φ = y) :
    fixedPointLocusLift f φ w y hy ≫ (fixedPointLocus f φ w).subschemeι = y := by
  change _ ≫ ((diagonalDivisor f).comapIso (graph f φ w)).inv ≫
    ((diagonalDivisor f).comap (graph f φ w)).subschemeι = y
  rw [Scheme.IdealSheafData.comapIso_inv_subschemeι, pullback.lift_fst]

/-- **The `k`-points of the fixed-point locus are the fixed `k`-points of `φ`.** -/
def fixedSectionsEquivFixedPointLocus [IsSeparated f] (φ : C ⟶ C) (w : φ ≫ f = f) :
    Stacks.EtaleCohomology.fixedSections f φ ≃
      {s : Spec (.of k) ⟶ (fixedPointLocus f φ w).subscheme //
        s ≫ (fixedPointLocus f φ w).subschemeι ≫ f = 𝟙 _} where
  toFun y := ⟨fixedPointLocusLift f φ w y.1 y.2.2, by
    rw [fixedPointLocusLift_subschemeι_assoc, y.2.1]⟩
  invFun s := ⟨s.1 ≫ (fixedPointLocus f φ w).subschemeι, by rw [Category.assoc, s.2], by
    rw [Category.assoc, fixedPointLocus_subschemeι_comp]⟩
  left_inv y := Subtype.ext (fixedPointLocusLift_subschemeι f φ w y.1 y.2.2)
  right_inv s := Subtype.ext ((cancel_mono (fixedPointLocus f φ w).subschemeι).1 (by simp))

/-- **The fixed-point locus of a morphism that moves some point is an effective Cartier divisor
on `C`.** The diagonal is an effective Cartier divisor on `C ×_k C`. The only weakly associated
point of the integral scheme `C` is its generic point `η`. If `Γ_φ(η)` lay on the diagonal, the
closed set `Γ_φ^{-1}(Δ_C)` would contain `η` and so be all of `C`. Every point `c` would then
satisfy `Γ_φ(c) = Δ(x)` for some `x`, which gives `c = x = φ(c)` after projecting. So the pullback
is defined ([Stacks, Tag 02OO]). -/
theorem isPullbackDefined_graph_diagonalDivisor [IsCurve k f] [Smooth f]
    (φ : C ⟶ C) (w : φ ≫ f = f) (hmoved : ∃ c : C, φ.base c ≠ c) :
    Stacks.Divisors.IsPullbackDefined (graph f φ w) (diagonalDivisor f) := by
  refine Stacks.Divisors.isPullbackDefined_of_notMem_support_of_weaklyAssociated _ _
    inferInstance fun x hx hmem => ?_
  rw [weaklyAssociatedPointsOfScheme_eq_genericPoints, genericPoints_eq_singleton] at hx
  obtain ⟨c, hc⟩ := hmoved
  apply hc
  have hclosed : IsClosed ((graph f φ w).base ⁻¹' ((diagonalDivisor f).support : Set _)) :=
    (diagonalDivisor f).support.isClosed.preimage (graph f φ w).base.hom.continuous
  have hη : x ∈ (graph f φ w).base ⁻¹' ((diagonalDivisor f).support : Set _) :=
    Scheme.IdealSheafData.mem_supportSet_iff_mem_support.mp hmem
  have hcmem : c ∈ (graph f φ w).base ⁻¹' ((diagonalDivisor f).support : Set _) := by
    have hgen : IsGenericPoint x (Set.univ : Set C) := by
      rw [Set.mem_singleton_iff.mp hx]
      exact genericPoint_spec C
    exact hclosed.closure_subset_iff.mpr (Set.singleton_subset_iff.mpr hη)
      (hgen.symm ▸ Set.mem_univ c :)
  change (graph f φ w).base c ∈ ((graph f (𝟙 C) _).ker.support : Set _) at hcmem
  rw [Scheme.Hom.support_ker, (graph f (𝟙 C) _).isClosedEmbedding.isClosed_range.closure_eq]
    at hcmem
  obtain ⟨x', hx'⟩ := hcmem
  have h1 := congrArg (pullback.fst f f).base hx'
  have h2 := congrArg (pullback.snd f f).base hx'
  simp only [← Scheme.Hom.comp_apply, graph_fst, graph_snd] at h1 h2
  exact h2.symm.trans h1

/-- **`V(φ)` is the dimension of the ring of functions on the fixed-point locus**, when that
locus is an effective Cartier divisor: `𝒪(Δ_C)` pulls back along `Γ_φ` to
`𝒪(Γ_φ^{-1}Δ_C)` ([Stacks, Tag 0C4U]), whose degree is `dim_k Γ(Γ_φ^{-1}Δ_C, 𝒪)`. -/
theorem fixedPointIntersection_eq_finrank [IsCurve k f] [Smooth f] [IsProper f]
    (hdim : topologicalKrullDim C ≤ 1) (φ : C ⟶ C) (w : φ ≫ f = f)
    [Stacks.Divisors.IsPullbackDefined (graph f φ w) (diagonalDivisor f)] :
    letI : Algebra k Γ((fixedPointLocus f φ w).subscheme, ⊤) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫
        ((fixedPointLocus f φ w).subschemeι ≫ f).appTop).hom.toAlgebra
    fixedPointIntersection f hdim φ w =
      (Module.finrank k Γ((fixedPointLocus f φ w).subscheme, ⊤) : ℤ) := by
  have : Stacks.Divisors.IsEffectiveCartierDivisor (fixedPointLocus f φ w) :=
    ‹Stacks.Divisors.IsPullbackDefined (graph f φ w) (diagonalDivisor f)›
  rw [fixedPointIntersection_eq_picardDegree, Stacks.Divisors.schemePullbackClass_picardClass,
    Stacks.EtaleCohomology.picardModelAddEquiv_picardClass]
  exact picardDegree_divisorSchemePicardClass k f hdim (fixedPointLocus f φ w)

/-- **`V(φ)` counts the fixed points of `φ` when they are simple** ([Stacks, Tag 03UJ]). Over an
algebraically closed field `k`, let `φ` move some point of `C` and have reduced fixed-point locus.
Then `V(φ) = (𝒪(Δ_C) · Γ_φ)` is the number of `k`-points `c` of `C` with `φ(c) = c`. -/
theorem fixedPointIntersection_eq_natCard_fixedSections [IsAlgClosed k] [IsCurve k f] [Smooth f]
    [IsProper f] (hdim : topologicalKrullDim C ≤ 1) (φ : C ⟶ C) (w : φ ≫ f = f)
    (hmoved : ∃ c : C, φ.base c ≠ c) (hred : IsReduced (fixedPointLocus f φ w).subscheme) :
    fixedPointIntersection f hdim φ w = Nat.card (Stacks.EtaleCohomology.fixedSections f φ) := by
  have := isPullbackDefined_graph_diagonalDivisor f φ w hmoved
  have : Stacks.Divisors.IsEffectiveCartierDivisor (fixedPointLocus f φ w) :=
    ‹Stacks.Divisors.IsPullbackDefined (graph f φ w) (diagonalDivisor f)›
  have : IsFinite ((fixedPointLocus f φ w).subschemeι ≫ f) :=
    isFinite_divisorSubscheme k f hdim (fixedPointLocus f φ w)
  rw [fixedPointIntersection_eq_finrank f hdim φ w,
    Nat.card_congr (fixedSectionsEquivFixedPointLocus f φ w),
    natCard_sections_eq_finrank ((fixedPointLocus f φ w).subschemeι ≫ f)]

end CurveGraph

end AlgebraicGeometry

end
