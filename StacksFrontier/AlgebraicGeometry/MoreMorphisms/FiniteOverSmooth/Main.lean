module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.EtaleLocalizationQuasiFinite.FiniteNeighborhood
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.FiniteOverSmooth.AffineFactorization
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.FinitePresentation.Basic

/-!
# The local structure of a morphism of finite type

Let `f : X ⟶ S` be locally of finite type, let `x` be a point of `X` with image `s = f x`, and
suppose the fibre `X_s` has local dimension `n` at `x`. Then `f` becomes, after passing to an
elementary étale neighbourhood `(X', x')` of `(X, x)`, a finite morphism onto a scheme smooth of
relative dimension `n` over `S`, in which the fibre of `x'` is a single point and the residue
field of its image is a purely transcendental extension of `κ(s)`.

## Main results

* `AlgebraicGeometry.exists_finite_over_smooth_of_locallyOfFiniteType`: Stacks 052E.

## Implementation notes

The factorisation of `f` through affine `n`-space over `S` is
`AlgebraicGeometry.exists_quasiFinite_over_affineSpace`, which also carries the purely
transcendental residue field extension. Stacks 02LK turns the quasi-finite morphism it produces
into a finite one over an elementary étale neighbourhood of the base, and all that remains is
to compose the two squares, transport the residue field extension along the residue field
isomorphism of the elementary neighbourhood, and read the finite-presentation clause off
Stacks 02FV part (1).

Part (2) of Stacks 02FV is not used: it asks for finite presentation of the composite morphism
to `S`, which would require quasi-compactness of the étale neighbourhood over `S`. The
quasi-compactness and quasi-separatedness needed for finite presentation of `π` come instead
from the finiteness of `π` itself.

## References

* [Stacks Project, Tag 052E](https://stacks.math.columbia.edu/tag/052E)
* [Stacks Project, Tag 02LK](https://stacks.math.columbia.edu/tag/02LK)
* [Stacks Project, Tag 02FV](https://stacks.math.columbia.edu/tag/02FV)
-/

@[expose] public section

namespace AlgebraicGeometry

open CategoryTheory CategoryTheory.Limits

universe u

/-- **Stacks 052E.** Let `f : X ⟶ S` be locally of finite type, let `x ∈ X` and set `s = f x`.
If the fibre `X_s` has local dimension `n` at `x`, then there is a commutative square
`g ≫ f = π ≫ h` in which `h : Y ⟶ S` is smooth of relative dimension `n`,
`g : (X', x') ⟶ (X, x)` is an elementary étale neighbourhood, `π : X' ⟶ Y` is finite, and the
fibre of `π` over `y = π x'` is the single point `x'`; moreover `κ(y)` is a purely
transcendental extension of `κ(s)`, and if `f` is locally of finite presentation then `π` is of
finite presentation. -/
@[stacks 052E]
theorem exists_finite_over_smooth_of_locallyOfFiniteType
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f] (x : X) (n : ℕ)
    (hdim : topologicalKrullDimAt (f.fiber (f x)) (f.asFiber x) = n) :
    ∃ (Y : Scheme.{u}) (h : Y ⟶ S) (N : EtaleNeighborhood X x) (π : N.scheme ⟶ Y),
      SmoothOfRelativeDimension n h ∧ N.IsElementary ∧ IsFinite π ∧
      {z : N.scheme | π z = π N.point} = {N.point} ∧
      N.toBase ≫ f = π ≫ h ∧
      (∃ hy : h (π N.point) = f x,
        letI : Algebra (S.residueField (f x)) (Y.residueField (π N.point)) :=
          (((S.residueFieldCongr hy).inv ≫ h.residueFieldMap (π N.point)).hom).toAlgebra
        PurelyTranscendental (S.residueField (f x)) (Y.residueField (π N.point))) ∧
      (LocallyOfFinitePresentation f → FinitePresentation π) := by
  obtain ⟨X₀, Y₀, ι, π₀, hY, x₀, hιopen, hιx, hsmooth, hπft, hisol, hsq, hy₀, hpt₀⟩ :=
    exists_quasiFinite_over_affineSpace f x n hdim
  have _ : IsOpenImmersion ι := hιopen
  have _ : SmoothOfRelativeDimension n hY := hsmooth
  have _ : LocallyOfFiniteType π₀ := hπft
  obtain ⟨⟨W, hWelem, V, hspec⟩⟩ :=
    Stacks.Flatness.exists_etaleNeighborhood_finiteAt π₀ x₀ hisol
  obtain ⟨hVfin, ⟨v, hv, hvuniq⟩, hvrest⟩ := hspec
  obtain ⟨hvx, hvres⟩ := hvrest v hv
  set π := V.ι ≫ pullback.snd π₀ W.toBase with hπ
  set gX := (V.ι ≫ pullback.fst π₀ W.toBase) ≫ ι with hgX
  set hm : W.scheme ⟶ S := W.toBase ≫ hY with hhm
  have hgXv : gX v = x := by
    change ι ((V.ι ≫ pullback.fst π₀ W.toBase) v) = x
    exact (congrArg (fun z : ↥X₀ => ι z) hvx).trans hιx
  have _ : Etale (V.ι ≫ pullback.fst π₀ W.toBase) := by infer_instance
  have hgXetale : Etale gX := by
    rw [hgX]
    infer_instance
  set N : EtaleNeighborhood X x :=
    { scheme := V.toScheme, point := v, toBase := gX, etale_toBase := hgXetale,
      map_point := hgXv }
  have hsmoothm : SmoothOfRelativeDimension n hm :=
    SmoothOfRelativeDimension.etale_comp n W.toBase hY
  have hNelem : N.IsElementary := by
    rw [EtaleNeighborhood.isElementary_iff]
    change IsIso (gX.residueFieldMap v)
    have h₁ : ∀ z : ↥X₀, IsIso (ι.residueFieldMap z) := fun _ => inferInstance
    rw [hgX, Scheme.residueFieldMap_comp (f := V.ι ≫ pullback.fst π₀ W.toBase) ι v]
    exact IsIso.comp_isIso' (h₁ _) hvres
  have hpre : {z : V.toScheme | π z = π v} = {v} := by
    ext z
    change π z = π v ↔ z = v
    exact ⟨fun hz => hvuniq z (hz.trans hv), fun hz => hz ▸ rfl⟩
  have hsquare : gX ≫ f = π ≫ hm := by
    rw [hgX, hπ, hhm]
    simp only [Category.assoc, hsq, pullback.condition_assoc]
  have hWtoBase : W.toBase (π v) = π₀ x₀ := by rw [hv]; exact W.map_point
  have hym : hm (π v) = f x := by
    change hY (W.toBase (π v)) = f x
    rwa [hWtoBase]
  refine ⟨W.scheme, hm, N, π, hsmoothm, hNelem, hVfin, hpre, hsquare, ⟨hym, ?_⟩, ?_⟩
  · -- the purely transcendental residue field extension
    have _ : IsIso W.residueFieldMap := hWelem
    set E : ↥(Y₀.residueField (π₀ x₀)) ≃+* ↥(W.scheme.residueField (π v)) :=
      (asIso W.residueFieldMap ≪≫ W.scheme.residueFieldCongr hv.symm).commRingCatIsoToRingEquiv
    let inst₀ : Algebra ↥(S.residueField (f x)) ↥(Y₀.residueField (π₀ x₀)) :=
      (((S.residueFieldCongr hy₀).inv ≫ hY.residueFieldMap (π₀ x₀)).hom).toAlgebra
    let inst₁ : Algebra ↥(S.residueField (f x)) ↥(W.scheme.residueField (π v)) :=
      (((S.residueFieldCongr hym).inv ≫ hm.residueFieldMap (π v)).hom).toAlgebra
    have hcompat : ∀ z : ↥(S.residueField (f x)),
        E (@algebraMap _ _ _ _ inst₀ z) = @algebraMap _ _ _ _ inst₁ z := by
      intro z
      have hstep₁ := residueFieldCongr_hom_residueFieldMap hY hWtoBase.symm hy₀ hym z
      have hstep₂ := residueFieldCongr_hom_residueFieldMap W.toBase hv.symm W.map_point
        hWtoBase (hY.residueFieldMap (π₀ x₀) ((S.residueFieldCongr hy₀).inv z))
      have hfin : @algebraMap _ _ _ _ inst₁ z =
          W.toBase.residueFieldMap (π v)
            (hY.residueFieldMap (W.toBase (π v)) ((S.residueFieldCongr hym).inv z)) :=
        congrArg (fun m : S.residueField (hm (π v)) ⟶ W.scheme.residueField (π v) =>
          m ((S.residueFieldCongr hym).inv z))
            (Scheme.residueFieldMap_comp (f := W.toBase) hY (π v))
      change (W.scheme.residueFieldCongr hv.symm).hom
        (W.residueFieldMap (@algebraMap _ _ _ _ inst₀ z)) = _
      rw [EtaleNeighborhood.residueFieldMap_def]
      change (W.scheme.residueFieldCongr hv.symm).hom
        (W.toBase.residueFieldMap W.point ((Y₀.residueFieldCongr W.map_point).inv
          (hY.residueFieldMap (π₀ x₀) ((S.residueFieldCongr hy₀).inv z)))) = _
      rw [hstep₂, hfin]
      exact congrArg (fun u => W.toBase.residueFieldMap (π v) u) hstep₁
    exact @purelyTranscendental_of_ringEquiv _ _ _ _ _ _ _ _ inst₀ inst₁ (.refl _) E hcompat hpt₀
  · -- the finite presentation clause
    intro hfp
    have _ : IsFinite π := hVfin
    have hcomp : LocallyOfFinitePresentation (π ≫ hm) := by
      rw [← hsquare]
      infer_instance
    have _ : Smooth hm := SmoothOfRelativeDimension.smooth n hm
    exact ⟨locallyOfFinitePresentation_of_comp π hm, inferInstance, inferInstance⟩

end AlgebraicGeometry
