module

public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.FinitePresentationLocalAtSource
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineHomTfaeComplete
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartLocality
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescendingFiniteTypeLimitImage
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.ImageSystemProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.SpecialCoverings
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeSpecDirectImage
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleSchemeStructureSharp

/-!
# A space affine over the base whose direct image is of finite presentation

Let `Z` be an algebraic space affine over a quasi-compact algebraic space `Y` whose direct image
`Z_* 𝒪_Z` is identified with a quasi-coherent `𝒪_Y`-algebra `𝒜` of finite presentation, so
that `Z` is the relative spectrum `\underline{Spec}_Y(𝒜)` of Stacks 081W.  Then `Z ⟶ Y` is of
finite presentation.  The proof of Stacks 0870 calls this "by construction".

## Main results

* `AlgebraicGeometry.Space.isFinitePresentation_of_pushforwardAlgebraIso`.

## Implementation notes

An affine morphism is quasi-compact and quasi-separated, so only local finite presentation is at
stake, and since that is étale local it is checked on one surjective étale chart `b : V ⟶ Y`
with `V` affine.  The morphism `Z ⟶ Y` is affine, hence representable, so its base change to `V`
is an affine scheme `Z ×_Y V`, and the sections of the direct image of the structure sheaf of
`Z` over the chart `b` are the functions on `Z ×_Y V`, the structure map being pullback along
`Z ×_Y V ⟶ V`: this is `AlgebraicGeometry.Space.fSharp_comp_chartProjectionSharpDirectImage`
(Stacks 03G8, part (2)).  The identification of that direct image with `𝒜`, whose structure map
on the affine chart `b` is of finite presentation by assumption, finishes the proof.  No base
change of algebras is involved.

## References

* [Stacks Project, Tag 0870](https://stacks.math.columbia.edu/tag/0870)
* [Stacks Project, Tag 081W](https://stacks.math.columbia.edu/tag/081W)
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {Y : AlgebraicSpaces B S hS}

/-- Finite presentation transfers along a ring map that factors, up to a bijection, through a ring
map of finite presentation. -/
private theorem finitePresentation_of_bijective_comp {R S T : Type u} [CommRing R] [CommRing S]
    [CommRing T] (f : R →+* S) (g : S →+* T) (k : R →+* T) (hk : ∀ r, g (f r) = k r)
    (hg : Function.Bijective g) (hf : f.FinitePresentation) : k.FinitePresentation := by
  have : k = (RingEquiv.ofBijective g hg).toRingHom.comp f := RingHom.ext fun r => (hk r).symm
  exact this ▸ RingHom.finitePresentation_respectsIso.left _ _ hf

/-- **The relative spectrum of an algebra of finite presentation is of finite presentation.**  Let
`𝒜` be a quasi-coherent `𝒪_Y`-algebra of finite presentation on a quasi-compact algebraic space
`Y`, and `Z` an algebraic space affine over `Y` together with an identification
`φ : Z_* 𝒪_Z ≅ 𝒜` of `𝒪_Y`-algebras, that is, a relative spectrum `\underline{Spec}_Y(𝒜)`.  Then
`Z ⟶ Y` is a morphism of finite presentation. -/
theorem isFinitePresentation_of_pushforwardAlgebraIso (A : QuasicoherentAlgebra B S hS Y)
    (Z : AffineOver B S hS Y) (φ : pushforwardAlgebra B S hS Z.obj ≅ A.obj)
    (hYqc : IsQuasiCompactSpace B S hS Y.obj) (hA : A.obj.IsFinitePresentation) :
    IsFinitePresentation B S hS Z.obj.hom.hom := by
  have hZ : IsAlgebraicSpace B S hS Z.obj.left.obj := Z.obj.left.property
  have haff : IsAffineHom B S hS Z.obj.hom.hom := Z.property
  obtain ⟨hrep, hpre⟩ :=
    presheaf_isAffineHom_of_isAffineHom_of_isAlgebraicSpace B S hS hZ Y.property haff
  refine ⟨?_, isQuasiCompact_of_isAffineHom' B S hS _ hZ Y.property haff,
    isQuasiSeparated_of_isAffineHom B S hS _ hZ Y.property haff⟩
  refine (holdsOnEveryEtaleChart_iff_surjectiveChart B S hS (P := @LocallyOfFinitePresentation)
    LocallyOfFinitePresentation.isEtaleLocalOnSourceAndTarget hZ Y.property _).2 ?_
  obtain ⟨V, b, hVaff, hbsurj, hbet⟩ :=
    (isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover B S hS Y.obj Y.property).1 hYqc
  have hbet' := (isEtale_iff_presheaf_of_yoneda B S hS b).1 hbet
  have hsq := hrep.isPullback b
  refine ⟨hrep.pullback b, V, hrep.fst b, b, hrep.snd b,
    presheaf_of_isPullback B S hS hsq.flip hbet', hbet',
    presheaf_of_isPullback B S hS hsq.flip hbsurj, (hrep.w b).symm, ?_⟩
  -- the étale chart `b` of `Y`
  let Vc : SmallEtale B S hS Y.1 := ⟨CostructuredArrow.mk b, hbet'⟩
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj V) := hVaff
  have : _root_.AlgebraicGeometry.IsAffineHom
      ((BigFppfOver.toScheme B S hS).map (hrep.snd b)) := hpre.property_snd b
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj (hrep.pullback b)) :=
    isAffine_of_isAffineHom ((BigFppfOver.toScheme B S hS).map (hrep.snd b))
  rw [HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFinitePresentation)]
  -- `A ≅ f_* 𝒪_Z`
  have hφiso : IsIso (φ.inv.right.hom.app (op Vc)) :=
    NatIso.isIso_app_of_isIso ((sheafToPresheaf _ _).map (AlgebraSheaf.forget.map φ.inv)) (op Vc)
  have h1 : RingHom.FinitePresentation
      ((pushforwardAlgebra B S hS Z.obj).algebraMap (op Vc)) :=
    finitePresentation_of_bijective_comp _ (φ.inv.right.hom.app (op Vc)).hom _
      (fun r => φ.inv.comm (op Vc) r) (ConcreteCategory.bijective_of_isIso _) (hA Vc hVaff)
  -- `f_* 𝒪_Z` on the chart `b` is the ring of functions on the base-changed chart
  let ψ := (chartProjectionSharpDirectImage B S hS Z.obj.hom hrep).hom.app (op Vc)
  have hψiso : IsIso ψ := by
    let := isContinuous_smallBaseChange B S hS Z.obj.hom hrep
    exact NatIso.isIso_app_of_isIso ((sheafToPresheaf _ _).map
      (chartProjectionSharpDirectImage B S hS Z.obj.hom hrep)) (op Vc)
  exact finitePresentation_of_bijective_comp _ ψ.hom _
    (fun r => congrArg (fun φ => (φ.hom.app (op Vc)).hom r)
      (fSharp_comp_chartProjectionSharpDirectImage B S hS Z.obj.hom hrep))
    (ConcreteCategory.bijective_of_isIso ψ) h1

end AlgebraicGeometry.Space
