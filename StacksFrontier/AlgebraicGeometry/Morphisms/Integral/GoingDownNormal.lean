module

public import Mathlib.AlgebraicGeometry.Morphisms.Integral
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.RingTheory.IntegralClosure.GoingDown
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.FiniteOverSmooth.NormalFibre
public import StacksFrontier.AlgebraicGeometry.Morphisms.Dominant.IntegralSchemes
public import StacksFrontier.AlgebraicGeometry.Properties.Dimension
public import StacksFrontier.AlgebraicGeometry.Properties.NormalCoproduct

/-!
# An integral morphism between normal schemes lifts generalizations

Let `f : X ⟶ Y` be an integral morphism of locally Noetherian **normal** schemes which carries
generic points to generic points.  Then the underlying map of `f` lifts generalizations:
`GeneralizingMap f.base`.

This is going down.  On an integral affine chart it is Mathlib's instance
`Algebra.HasGoingDown` for an integral extension of a domain whose base is integrally closed,
turned into a topological statement by
`Algebra.HasGoingDown.iff_generalizingMap_primeSpectrumComap`; the global statement follows
because `GeneralizingMap` is Zariski-local on source and target, after reducing to integral
charts.  A normal locally Noetherian scheme is a disjoint union of normal *integral* schemes
(`AlgebraicGeometry.isNormal_iff_exists_iso_coproduct_integral_normal`), so such charts exist
around any point, and the component of the base change through a given point of `X` is integral
and dominates its chart downstairs exactly because `f` carries generic points to generic points.

Normality of the target is essential, and finiteness of `f` is no substitute: a finite morphism
does not preserve codimension — the closed immersion of a closed point into a curve takes
coheight `0` to coheight `1` — and a point of `X` can fail to be a generic point of its own
fibre over a non-normal `Y`.

## Main results

* `AlgebraicGeometry.generalizingMap_base_of_isIntegralHom_of_isNormal`: an integral morphism of
  locally Noetherian normal schemes carrying generic points to generic points lifts
  generalizations.
* `AlgebraicGeometry.isClosedImmersion_sigma_ι`: the inclusion of a summand of a coproduct of
  schemes is a closed immersion.

## Implementation notes

The reduction to charts is not a bare open cover: `GeneralizingMap` is checked at a single
generalization `y ⤳ f x`, and the chart downstairs has to contain `f x` while the chart upstairs
has to contain `x` *and* map into it.  The second is arranged by base change: `X ×_Y V` is an
open subscheme of `X` containing `x`, and the component of it through `x` — picked out by the
coproduct decomposition of the normal scheme `X ×_Y V` — is integral, affine (being integral over
the affine `V`) and closed in `X ×_Y V`, hence integral over `V`.  Dominance of that component
over `V` is where the hypothesis on generic points is used.

## References

* [Stacks Project, Tag 09IL](https://stacks.math.columbia.edu/tag/09IL)
* [Stacks Project, Tag 0GLQ](https://stacks.math.columbia.edu/tag/0GLQ)
* [Stacks Project, Tag 037F](https://stacks.math.columbia.edu/tag/037F)
-/

public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- **Going down on integral affine charts.** A dominant integral morphism of integral affine
schemes with normal target lifts generalizations: on sections it is an injective integral ring
map out of an integrally closed domain, so Mathlib's going-down instance applies, and going down
for a ring map is exactly the lifting of generalizations on spectra. -/
private lemma generalizingMap_base_of_isIntegralHom_affine {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsAffine X] [IsAffine Y] [IsIntegral X] [IsIntegral Y] [IsNormal Y] [IsIntegralHom f]
    [IsDominant f] : GeneralizingMap f.base := by
  have : Nonempty X := IsIntegral.nonempty
  have : Nonempty Y := IsIntegral.nonempty
  have : Nonempty (⊤ : X.Opens) := ⟨⟨Classical.choice (IsIntegral.nonempty : Nonempty X), by simp⟩⟩
  have : Nonempty (⊤ : Y.Opens) := ⟨⟨Classical.choice (IsIntegral.nonempty : Nonempty Y), by simp⟩⟩
  have _ : IsDomain Γ(Y, ⊤) := IsIntegral.component_integral ⊤
  have _ : IsDomain Γ(X, ⊤) := IsIntegral.component_integral ⊤
  have _ : IsIntegrallyClosed Γ(Y, ⊤) :=
    (isNormal_iff_forall_affineOpen_normal Y).mp inferInstance ⟨⊤, isAffineOpen_top Y⟩ inferInstance
  have _ : IsSchemeTheoreticallyDominant f := .of_isDominant f
  have hinj : Function.Injective f.appTop.hom := f.app_injective ⊤
  algebraize [f.appTop.hom]
  have _ : FaithfulSMul Γ(Y, ⊤) Γ(X, ⊤) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr hinj
  have hInt : f.appTop.hom.IsIntegral := f.isIntegral_app ⊤ (isAffineOpen_top Y)
  have _ : Algebra.IsIntegral Γ(Y, ⊤) Γ(X, ⊤) :=
    algebraMap_isIntegral_iff.mp (by simpa only [RingHom.algebraMap_toAlgebra] using hInt)
  have _ : Algebra.HasGoingDown Γ(Y, ⊤) Γ(X, ⊤) := inferInstance
  have _ := HasRingHomProperty.of_isZariskiLocalAtSource_of_isZariskiLocalAtTarget.{u}
    (topologically GeneralizingMap)
  change (topologically GeneralizingMap) f
  exact (HasRingHomProperty.iff_of_isAffine (P := topologically GeneralizingMap)).mpr
    (Algebra.HasGoingDown.iff_generalizingMap_primeSpectrumComap.mp inferInstance)

/-- The inclusion of a summand of a coproduct of schemes is a closed immersion. -/
lemma isClosedImmersion_sigma_ι {ι : Type u} (X : ι → Scheme.{u}) (i : ι) :
    IsClosedImmersion (Sigma.ι X i) := by
  refine IsClosedImmersion.of_isPreimmersion (Sigma.ι X i) ?_
  have h : (⇑(Sigma.ι X i) : X i → (∐ X : Scheme.{u})) = sigmaMk X ∘ Sigma.mk i :=
    funext fun x => (sigmaMk_mk X i x).symm
  rw [h]
  exact ((sigmaMk X).isClosedEmbedding.comp Topology.IsClosedEmbedding.sigmaMk).isClosed_range

/-- **Generic points pull back along an injective morphism.** If the image of `x` is a generic
point of the target then `x` is a generic point of the source: a proper generalization of `x`
would map to one of `j x`. -/
private lemma mem_genericPoints_of_injective {X Y : Scheme.{u}} (j : X ⟶ Y)
    (hinj : Function.Injective j.base) {x : X} (hx : j.base x ∈ genericPoints Y) :
    x ∈ genericPoints X := by
  rw [mem_genericPoints_iff_isMax] at hx ⊢
  intro b hb
  have hspec : j.base b ⤳ j.base x := (Scheme.le_iff_specializes.mp hb).map j.continuous
  exact le_of_eq (hinj (hspec.antisymm
    (Scheme.le_iff_specializes.mp (hx (Scheme.le_iff_specializes.mpr hspec)))).eq)

/-- Every point of a normal locally Noetherian scheme lies in a component: an integral normal
scheme with a clopen immersion into it, obtained from the coproduct decomposition. -/
private lemma exists_isIntegral_isNormal_isClosedImmersion (Y : Scheme.{u})
    [IsLocallyNoetherian Y] [IsNormal Y] (y : Y) :
    ∃ (Z : Scheme.{u}) (_ : IsIntegral Z) (_ : IsNormal Z) (k : Z ⟶ Y) (_ : IsOpenImmersion k)
      (_ : IsClosedImmersion k) (z : Z), k.base z = y := by
  obtain ⟨ι, Z, hN, hZ, ⟨e⟩⟩ := (isNormal_iff_exists_iso_coproduct_integral_normal Y).mp
    inferInstance
  obtain ⟨⟨i, z⟩, hz⟩ := (sigmaMk Z).surjective (e.hom.base y)
  have _ := isClosedImmersion_sigma_ι Z i
  refine ⟨Z i, hZ i, hN i, Sigma.ι Z i ≫ e.inv, inferInstance, inferInstance, z, ?_⟩
  change e.inv.base (Sigma.ι Z i |>.base z) = y
  rw [← sigmaMk_mk, hz]
  change (e.hom ≫ e.inv).base y = y
  rw [e.hom_inv_id]
  rfl

/-- An integral normal affine neighbourhood of a point of a normal locally Noetherian scheme:
an affine open of a component through the point is again integral and normal. -/
private lemma exists_isIntegral_isNormal_affine_nhd (Y : Scheme.{u}) [IsLocallyNoetherian Y]
    [IsNormal Y] (y : Y) :
    ∃ (V : Scheme.{u}) (_ : IsAffine V) (_ : IsIntegral V) (_ : IsNormal V) (j : V ⟶ Y)
      (_ : IsOpenImmersion j) (v : V), j.base v = y := by
  obtain ⟨Z, _, _, k, _, -, z, hz⟩ := exists_isIntegral_isNormal_isClosedImmersion Y y
  obtain ⟨U, hzU⟩ := Z.isBasis_affineOpens.isOpenCover.exists_mem z
  let V : Z.Opens := U.1
  have _ : IsAffine V.toScheme := U.2
  have _ : Nonempty V.toScheme := ⟨⟨z, hzU⟩⟩
  have _ : IsIntegral V.toScheme := isIntegral_of_isOpenImmersion V.ι
  have _ : IsNormal V.toScheme := isNormal_of_isOpenImmersion V.ι
  exact ⟨V.toScheme, inferInstance, inferInstance, inferInstance, V.ι ≫ k, inferInstance,
    ⟨z, hzU⟩, hz⟩

/-- **Going down for an integral morphism of normal schemes.** Let `f : X ⟶ Y` be integral with
`X` and `Y` normal and locally Noetherian, and suppose `f` carries every generic point of `X` to
a generic point of `Y`.  Then `f` lifts generalizations.

Pick an integral normal affine open `V ⊆ Y` through `f x`; the base change `X ×_Y V` is a normal
locally Noetherian open subscheme of `X` containing a preimage of `x`, so the component of it
through that preimage is an integral scheme, open and closed in `X ×_Y V`, hence integral and
affine over `V`.  It dominates `V` because `f` carries generic points to generic points, so
`AlgebraicGeometry.generalizingMap_base_of_isIntegralHom_affine` lifts the given generalization
of `f x` through it, and the projection to `X` carries the lift back. -/
theorem generalizingMap_base_of_isIntegralHom_of_isNormal {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsIntegralHom f] [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [IsNormal X] [IsNormal Y]
    (hgen : ∀ x : X, x ∈ genericPoints X → f.base x ∈ genericPoints Y) :
    GeneralizingMap f.base := by
  intro x y hy
  obtain ⟨V, _, _, _, j, _, v, hv⟩ := exists_isIntegral_isNormal_affine_nhd Y (f.base x)
  have hyv : y ⤳ j.base v := by rw [hv]; exact hy
  obtain ⟨w, hwv, hw⟩ := j.isOpenEmbedding.generalizingMap hyv
  obtain ⟨xV, hxV, hxVv⟩ :=
    Scheme.Pullback.exists_preimage_pullback (f := f) (g := j) x v hv.symm
  have _ : IsNormal (pullback f j) := isNormal_of_isOpenImmersion (pullback.fst f j)
  have _ : IsLocallyNoetherian (pullback f j) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.fst f j)
  obtain ⟨Z, _, _, k, _, _, z, hkz⟩ := exists_isIntegral_isNormal_isClosedImmersion
    (pullback f j) xV
  set d : Z ⟶ V := k ≫ pullback.snd f j with hd
  have _ : IsIntegralHom d := inferInstance
  have _ : IsAffine (Z) := isAffine_of_isAffineHom d
  have hdgen : d.base (genericPoint (Z)) ∈ genericPoints V := by
    refine mem_genericPoints_of_injective j j.isOpenEmbedding.injective ?_
    have hc : d ≫ j = (k ≫ pullback.fst f j) ≫ f := by
      simp only [hd, Category.assoc, pullback.condition]
    rw [← Scheme.Hom.comp_apply, hc, Scheme.Hom.comp_apply]
    refine hgen _ (mem_genericPoints_of_generalizingMap
      (k ≫ pullback.fst f j).isOpenEmbedding.generalizingMap ?_)
    simp [genericPoints_eq_singleton]
  have _ : IsDominant d :=
    ((tfae_isDominant_of_isIntegral d).out 2 1).mp
      (by simpa only [genericPoints_eq_singleton, Set.mem_singleton_iff] using hdgen)
  have hdz : d.base z = v := by rw [hd]; change (pullback.snd f j).base (k.base z) = v
                                rw [hkz]; exact hxVv
  obtain ⟨z', hz'z, hdz'⟩ := generalizingMap_base_of_isIntegralHom_affine d
    (show w ⤳ d.base z by rw [hdz]; exact hwv)
  refine ⟨(pullback.fst f j).base (k.base z'), ?_, ?_⟩
  · have h := hz'z.map (k ≫ pullback.fst f j).continuous
    change (pullback.fst f j).base (k.base z') ⤳ (pullback.fst f j).base (k.base z) at h
    rwa [hkz, hxV] at h
  · have hc := congrArg (fun a : (pullback f j : Scheme.{u}) ⟶ Y => a.base (k.base z'))
      (pullback.condition (f := f) (g := j))
    change f.base ((pullback.fst f j).base (k.base z')) = j.base (d.base z') at hc
    rw [hc, hdz', hw]

end AlgebraicGeometry

end
