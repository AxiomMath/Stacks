module

public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.GeometricGenusAlgClosure
public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.GeometricGenusDisjointCover
public import StacksFrontier.FieldTheory.SeparableDegreeTensorProduct

/-!
# The geometric genus as a sum over the embeddings of the field of global functions

Let `k` be a field, `E` a finite extension of `k` and `X` a proper scheme over `k` whose structure
morphism factors through `Spec E`.  Writing `k̄` for an algebraic closure of `k`, the base change
`X_{k̄}` lies over `Spec (k̄ ⊗_k E)`, a finite discrete scheme whose points are exactly the
`k`-embeddings `t : E → k̄`.  The fibres of `X_{k̄} ⟶ Spec (k̄ ⊗_k E)` are therefore finitely many
pairwise disjoint closed subschemes with open underlying sets covering `X_{k̄}`, each isomorphic
to the fibre `X ×_{E, t} k̄` of `X ⟶ Spec E` over `t`.  Additivity of the geometric genus over such
a partition gives

`g_geom(X/k) = ∑_{t : E →ₐ[k] k̄} g_geom(X ×_{E,t} k̄ / k̄)`.

## Main definitions

* `AlgebraicGeometry.specTensorToLeft`, `AlgebraicGeometry.specTensorToRight`: the two projections
  of `Spec (L ⊗[k] E)`.
* `AlgebraicGeometry.tensorPoint`: the `L`-point of `Spec (L ⊗[k] E)` attached to a `k`-embedding
  `t : E →ₐ[k] L`.

## Main results

* `AlgebraicGeometry.isPullback_specTensor`: `Spec (L ⊗[k] E)` is the fibre product of `Spec L`
  and `Spec E` over `Spec k`.
* `AlgebraicGeometry.isClosedImmersion_tensorPoint`: the `L`-points are closed immersions.
* `AlgebraicGeometry.discreteTopology_specTensor`: `Spec (L ⊗[k] E)` is discrete.
* `AlgebraicGeometry.mem_range_tensorPoint_iff`: the image of the `L`-point attached to `t` is the
  point of `Spec (L ⊗[k] E)` that `Field.primeSpectrumTensorProductEquivAlgHom` matches with `t`.
* `AlgebraicGeometry.geometricGenus_eq_finsum_geometricGenus_pullback_snd`: the geometric genus of
  `X` over `k` is the sum over the `k`-embeddings `E → k̄` of the geometric genera of the fibres.

## References

* [Stacks Project, Tag 0CE5](https://stacks.math.columbia.edu/tag/0CE5)
* [Stacks Project, Tag 09HJ](https://stacks.math.columbia.edu/tag/09HJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TensorProduct

universe u

namespace AlgebraicGeometry

section TensorPoints

variable (k : Type u) [Field k] (E : Type u) [Field E] [Algebra k E] [FiniteDimensional k E]
  (L : Type u) [Field L] [Algebra k L] [IsAlgClosed L]

/-- The projection `Spec (L ⊗[k] E) ⟶ Spec L`. -/
public def specTensorToLeft : Spec (.of (L ⊗[k] E)) ⟶ Spec (.of L) :=
  Spec.map (CommRingCat.ofHom (algebraMap L (L ⊗[k] E)))

/-- The projection `Spec (L ⊗[k] E) ⟶ Spec E`. -/
public def specTensorToRight : Spec (.of (L ⊗[k] E)) ⟶ Spec (.of E) :=
  Spec.map (CommRingCat.ofHom
    (Algebra.TensorProduct.includeRight (R := k) (A := L) (B := E)).toRingHom)

/-- The `L`-point of `Spec (L ⊗[k] E)` attached to a `k`-embedding `t : E → L`, namely `Spec` of
the `L`-algebra map `L ⊗[k] E → L` extending `t`. -/
public def tensorPoint (t : E →ₐ[k] L) : Spec (.of L) ⟶ Spec (.of (L ⊗[k] E)) :=
  Spec.map (CommRingCat.ofHom (Field.algHomEquivTensorProductAlgHom k E L t).toRingHom)

omit [FiniteDimensional k E] [IsAlgClosed L] in
/-- `specTensorToLeft` is `Spec` of the algebra map `L → L ⊗[k] E`. -/
public theorem specTensorToLeft_eq :
    specTensorToLeft k E L = Spec.map (CommRingCat.ofHom (algebraMap L (L ⊗[k] E))) := rfl

omit [FiniteDimensional k E] [IsAlgClosed L] in
/-- `specTensorToRight` is `Spec` of the inclusion `E → L ⊗[k] E`. -/
public theorem specTensorToRight_eq :
    specTensorToRight k E L = Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeRight (R := k) (A := L) (B := E)).toRingHom) := rfl

omit [FiniteDimensional k E] [IsAlgClosed L] in
/-- `tensorPoint k E L t` is `Spec` of the `L`-algebra map `L ⊗[k] E → L` extending `t`. -/
public theorem tensorPoint_eq (t : E →ₐ[k] L) :
    tensorPoint k E L t =
      Spec.map (CommRingCat.ofHom (Field.algHomEquivTensorProductAlgHom k E L t).toRingHom) :=
  rfl

omit [FiniteDimensional k E] [IsAlgClosed L] in
/-- **`Spec (L ⊗[k] E)` is the fibre product of `Spec L` and `Spec E` over `Spec k`.** -/
public theorem isPullback_specTensor :
    IsPullback (specTensorToLeft k E L) (specTensorToRight k E L)
      (Spec.map (CommRingCat.ofHom (algebraMap k L)))
      (Spec.map (CommRingCat.ofHom (algebraMap k E))) := by
  have hleft : CommRingCat.ofHom
      (Algebra.TensorProduct.includeLeftRingHom (R := k) (A := L) (B := E)) =
      CommRingCat.ofHom (algebraMap L (L ⊗[k] E)) := by
    ext x
    simp [Algebra.TensorProduct.includeLeftRingHom, Algebra.TensorProduct.algebraMap_apply]
  rw [specTensorToLeft_eq, specTensorToRight_eq, ← hleft]
  exact isPullback_SpecMap_of_isPushout _ _ _ _ (CommRingCat.isPushout_tensorProduct k L E)

omit [FiniteDimensional k E] [IsAlgClosed L] in
/-- An `L`-point of `Spec (L ⊗[k] E)` is a section of the projection to `Spec L`. -/
public theorem tensorPoint_comp_specTensorToLeft (t : E →ₐ[k] L) :
    tensorPoint k E L t ≫ specTensorToLeft k E L = 𝟙 _ := by
  have hcomp : CommRingCat.ofHom (algebraMap L (L ⊗[k] E)) ≫
      CommRingCat.ofHom (Field.algHomEquivTensorProductAlgHom k E L t).toRingHom =
      𝟙 (CommRingCat.of L) := by
    ext x
    simp
  rw [tensorPoint_eq, specTensorToLeft_eq, ← Spec.map_comp, hcomp, Spec.map_id]

omit [FiniteDimensional k E] [IsAlgClosed L] in
/-- The `L`-point attached to `t` lies over `t` itself. -/
public theorem tensorPoint_comp_specTensorToRight (t : E →ₐ[k] L) :
    tensorPoint k E L t ≫ specTensorToRight k E L =
      Spec.map (CommRingCat.ofHom t.toRingHom) := by
  have hcomp : CommRingCat.ofHom
      (Algebra.TensorProduct.includeRight (R := k) (A := L) (B := E)).toRingHom ≫
      CommRingCat.ofHom (Field.algHomEquivTensorProductAlgHom k E L t).toRingHom =
      CommRingCat.ofHom t.toRingHom := by
    ext x
    exact congrArg (fun φ : E →ₐ[k] L => φ x)
      ((Field.algHomEquivTensorProductAlgHom k E L).symm_apply_apply t)
  rw [tensorPoint_eq, specTensorToRight_eq, ← Spec.map_comp, hcomp]

/-- The `L`-points of `Spec (L ⊗[k] E)` are closed immersions. -/
public instance isClosedImmersion_tensorPoint (t : E →ₐ[k] L) :
    IsClosedImmersion (tensorPoint k E L t) :=
  IsClosedImmersion.spec_of_surjective _ fun x =>
    ⟨algebraMap L (L ⊗[k] E) x, (Field.algHomEquivTensorProductAlgHom k E L t).commutes x⟩

omit [IsAlgClosed L] in
/-- **`Spec (L ⊗[k] E)` is discrete.** -/
public theorem discreteTopology_specTensor :
    DiscreteTopology (Spec (.of (L ⊗[k] E)) : Type u) := by
  have : IsArtinianRing (L ⊗[k] E) := IsArtinianRing.of_finite L _
  have : DiscreteTopology (PrimeSpectrum (L ⊗[k] E)) := by
    rw [PrimeSpectrum.discreteTopology_iff_finite_and_krullDimLE_zero]
    exact ⟨inferInstance,
      Ring.krullDimLE_zero_iff.mpr fun I _ => IsArtinianRing.isMaximal_of_isPrime I⟩
  infer_instance

/-- The `L`-point attached to `t` lands on the point of `Spec (L ⊗[k] E)` that
`Field.primeSpectrumTensorProductEquivAlgHom` matches with `t`, namely the kernel of the
`L`-algebra map extending `t`. -/
public theorem base_tensorPoint (t : E →ₐ[k] L) (y : PrimeSpectrum L) :
    (tensorPoint k E L t).base y =
      (Field.primeSpectrumTensorProductEquivAlgHom k E L).symm t := by
  apply PrimeSpectrum.ext
  show Ideal.comap (Field.algHomEquivTensorProductAlgHom k E L t).toRingHom y.asIdeal = _
  have hy : y.asIdeal = (⊥ : Ideal L) :=
    congrArg PrimeSpectrum.asIdeal (Subsingleton.elim y ⊥)
  rw [hy, ← RingHom.ker_eq_comap_bot]
  rfl

/-- **The image of the `L`-point attached to `t` is exactly the point of `Spec (L ⊗[k] E)` that
`Field.primeSpectrumTensorProductEquivAlgHom` matches with `t`.** -/
public theorem mem_range_tensorPoint_iff (t : E →ₐ[k] L)
    (x : (Spec (.of (L ⊗[k] E)) : Type u)) :
    x ∈ Set.range (tensorPoint k E L t).base ↔
      x = (Field.primeSpectrumTensorProductEquivAlgHom k E L).symm t := by
  refine ⟨?_, fun hx => ?_⟩
  · rintro ⟨y, rfl⟩
    exact base_tensorPoint k E L t y
  · exact ⟨(⊥ : PrimeSpectrum L), (base_tensorPoint k E L t ⊥).trans hx.symm⟩

/-- Distinct `k`-embeddings `E → L` cut out distinct points of `Spec (L ⊗[k] E)`. -/
public theorem disjoint_range_tensorPoint {t t' : E →ₐ[k] L} (hne : t ≠ t') :
    Disjoint (Set.range (tensorPoint k E L t).base)
      (Set.range (tensorPoint k E L t').base) := by
  refine Set.disjoint_left.2 fun x hx hx' => hne ?_
  refine (Field.primeSpectrumTensorProductEquivAlgHom k E L).symm.injective ?_
  exact ((mem_range_tensorPoint_iff k E L t x).1 hx).symm.trans
    ((mem_range_tensorPoint_iff k E L t' x).1 hx')

/-- **Every point of `Spec (L ⊗[k] E)` is the `L`-point attached to a `k`-embedding `E → L`.** -/
public theorem exists_mem_range_tensorPoint (x : (Spec (.of (L ⊗[k] E)) : Type u)) :
    ∃ t : E →ₐ[k] L, x ∈ Set.range (tensorPoint k E L t).base :=
  ⟨Field.primeSpectrumTensorProductEquivAlgHom k E L x,
    (mem_range_tensorPoint_iff k E L _ x).2
      ((Field.primeSpectrumTensorProductEquivAlgHom k E L).symm_apply_apply x).symm⟩

end TensorPoints

/-- The geometric genus of the base change of `X` to an algebraically closed extension `L` of `k`
is the sum, over the `k`-embeddings `t : E → L`, of the geometric genera of the fibres of
`X ⟶ Spec E` over `t`. -/
private theorem geometricGenus_pullback_snd_eq_finsum
    (k : Type u) [Field k] (E : Type u) [Field E] [Algebra k E] [FiniteDimensional k E]
    (L : Type u) [Field L] [Algebra k L] [IsAlgClosed L]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f] (h : X ⟶ Spec (.of E)) [IsProper h]
    (hfh : h ≫ Spec.map (CommRingCat.ofHom (algebraMap k E)) = f) :
    geometricGenus L (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k L)))) =
      ∑ᶠ t : E →ₐ[k] L, geometricGenus L
        (pullback.snd h (Spec.map (CommRingCat.ofHom t.toRingHom))) := by
  classical
  have : Finite (E →ₐ[k] L) := inferInstance
  let : Fintype (E →ₐ[k] L) := Fintype.ofFinite _
  have hTsq := (isPullback_specTensor k E L).flip
  have hcond : (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k L))) ≫ h) ≫
      Spec.map (CommRingCat.ofHom (algebraMap k E)) =
      pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k L))) ≫
        Spec.map (CommRingCat.ofHom (algebraMap k L)) := by
    rw [Category.assoc, hfh]
    exact pullback.condition
  set w := hTsq.lift (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k L))) ≫ h)
    (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k L)))) hcond with hwdef
  have hwβ : w ≫ specTensorToRight k E L =
      pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k L))) ≫ h :=
    hTsq.lift_fst _ _ _
  have hwσ : w ≫ specTensorToLeft k E L =
      pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k L))) :=
    hTsq.lift_snd _ _ _
  have hYsq : IsPullback (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k L)))) w h
      (specTensorToRight k E L) := by
    refine IsPullback.of_bot ?_ hwβ.symm hTsq
    rw [hwσ, hfh]
    exact IsPullback.of_hasPullback _ _
  have hfib : ∀ t : E →ₐ[k] L, ∃ i : pullback (C := Scheme.{u}) h
        (Spec.map (CommRingCat.ofHom t.toRingHom)) ⟶
      pullback (C := Scheme.{u}) f (Spec.map (CommRingCat.ofHom (algebraMap k L))),
      IsPullback i (pullback.snd h (Spec.map (CommRingCat.ofHom t.toRingHom))) w
        (tensorPoint k E L t) := by
    intro t
    refine ⟨hYsq.lift (pullback.fst h (Spec.map (CommRingCat.ofHom t.toRingHom)))
      (pullback.snd h (Spec.map (CommRingCat.ofHom t.toRingHom)) ≫ tensorPoint k E L t)
      (by rw [Category.assoc, tensorPoint_comp_specTensorToRight]; exact pullback.condition), ?_⟩
    refine IsPullback.of_right ?_ (hYsq.lift_snd _ _ _) hYsq
    rw [hYsq.lift_fst, tensorPoint_comp_specTensorToRight]
    exact IsPullback.of_hasPullback _ _
  have hopen : ∀ t : E →ₐ[k] L,
      IsOpen (Set.range (pullback.fst w (tensorPoint k E L t)).base) := by
    intro t
    have := discreteTopology_specTensor k E L
    rw [Scheme.Pullback.range_fst]
    exact (isOpen_discrete _).preimage w.continuous
  have hdisj : Pairwise fun t t' : E →ₐ[k] L =>
      Disjoint (Set.range (pullback.fst w (tensorPoint k E L t)).base)
        (Set.range (pullback.fst w (tensorPoint k E L t')).base) := by
    intro t t' hne
    rw [Scheme.Pullback.range_fst, Scheme.Pullback.range_fst]
    exact Disjoint.preimage _ (disjoint_range_tensorPoint k E L hne)
  have hcover : ∀ x : (pullback (C := Scheme.{u}) f
      (Spec.map (CommRingCat.ofHom (algebraMap k L))) : Type u),
      ∃ t : E →ₐ[k] L, x ∈ Set.range (pullback.fst w (tensorPoint k E L t)).base := by
    intro x
    obtain ⟨t, ht⟩ := exists_mem_range_tensorPoint k E L (w.base x)
    exact ⟨t, by rwa [Scheme.Pullback.range_fst]⟩
  have hgen : ∀ t : E →ₐ[k] L,
      geometricGenus L (pullback.fst w (tensorPoint k E L t) ≫
        pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k L)))) =
      geometricGenus L (pullback.snd h (Spec.map (CommRingCat.ofHom t.toRingHom))) := by
    intro t
    obtain ⟨i, hi⟩ := hfib t
    refine (geometricGenus_eq_of_iso _ hi.isoPullback ?_).symm
    rw [← Category.assoc, hi.isoPullback_hom_fst, ← hwσ, ← Category.assoc, hi.w,
      Category.assoc, tensorPoint_comp_specTensorToLeft, Category.comp_id]
  rw [finsum_eq_sum_of_fintype,
    geometricGenus_eq_sum_of_isClopen_cover
      (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k L))))
      (fun t : E →ₐ[k] L => pullback.fst w (tensorPoint k E L t)) hopen hdisj hcover]
  exact Finset.sum_congr rfl fun t _ => hgen t

/-- **The geometric genus as a sum over the embeddings of an intermediate field.**  Let `X` be a
proper scheme of dimension at most one over a field `k` whose structure morphism factors through
`Spec E` for a finite extension `E / k`.  Then the geometric genus of `X` over `k` is the sum,
over the `k`-embeddings `t` of `E` into an algebraic closure `k̄` of `k`, of the geometric genera
over `k̄` of the fibres of `X ⟶ Spec E` at `t`. -/
public theorem geometricGenus_eq_finsum_geometricGenus_pullback_snd
    (k : Type u) [Field k] (E : Type u) [Field E] [Algebra k E] [FiniteDimensional k E]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f] (h : X ⟶ Spec (.of E)) [IsProper h]
    (hfh : h ≫ Spec.map (CommRingCat.ofHom (algebraMap k E)) = f)
    (hX : topologicalKrullDim (X : Type u) ≤ 1) :
    geometricGenus k f = ∑ᶠ t : E →ₐ[k] AlgebraicClosure k,
      geometricGenus (AlgebraicClosure k)
        (pullback.snd h (Spec.map (CommRingCat.ofHom t.toRingHom))) :=
  (geometricGenus_eq_geometricGenus_pullback_snd k f hX).trans
    (geometricGenus_pullback_snd_eq_finsum k E (AlgebraicClosure k) f h hfh)

end AlgebraicGeometry

end
