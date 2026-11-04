module

public import Mathlib.AlgebraicGeometry.Artinian
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.RingTheory.Etale.QuasiFinite
public import Mathlib.RingTheory.Unramified.LocalStructure
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.AffineHomEtaleDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Affine
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiSeparatedFibreProducts
import StacksFrontier.AlgebraicGeometry.Spaces.Basic
import StacksFrontier.AlgebraicGeometry.Spaces.Separated
import StacksFrontier.AlgebraicGeometry.Topologies.Fppf

/-!
# Morphisms from the spectrum of an Artinian ring

Let `S` be a scheme and let `X` be a quasi-separated algebraic space over `S`. Every morphism
`Spec(A) ⟶ X` with `A` an Artinian ring is affine: this is **Stacks 09TF**.

## Main results

* `AlgebraicGeometry.Space.isAffineHom_of_isArtinianRing` — a morphism from the spectrum of an
  Artinian ring to a quasi-separated algebraic space is affine.

## Implementation notes

Affineness is tested chartwise, through the equivalent condition of
`AlgebraicGeometry.Space.isAffineHom_tfae_of_isAlgebraicSpace`: for every affine object `V` of
the site with an étale morphism to `X`, the fibre product with `Spec(A)` is representable by an
affine scheme. The fibre product is taken in the category of algebraic spaces,
`AlgebraicGeometry.AlgebraicSpaces.fiberProduct`, and the quasi-separatedness of `X` enters
through
`AlgebraicGeometry.Space.isAbsolutelyQuasiSeparated_iff_compactSpace_pullback_affine`, which
makes that fibre product quasi-compact.

The spectrum is required to belong to the chosen big fppf site, so that its structure morphism
to the base gives an object of the slice site, and quasi-separatedness is the absolute one,
tested after viewing the space over the terminal scheme.

That the fibre product is affine is then the scheme-theoretic fact that a quasi-compact scheme
étale over the spectrum of an Artinian ring has finite discrete underlying space: étale
morphisms are locally quasi-finite, and a locally quasi-finite morphism to a discrete space has
discrete source.

## References

* [Stacks Project, Tag 09TF](https://stacks.math.columbia.edu/tag/09TF)
* [Stacks Project, Tag 03WF](https://stacks.math.columbia.edu/tag/03WF)
* [Stacks Project, Tag 02X2](https://stacks.math.columbia.edu/tag/02X2)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

/-- A quasi-compact scheme étale over the spectrum of an Artinian ring is affine. -/
private theorem isAffine_of_etale_of_isArtinianRing {A : CommRingCat.{u}} [IsArtinianRing A]
    {X : Scheme.{u}} [CompactSpace X] (f : X ⟶ Spec A) [Etale f] : IsAffine X := by
  have : LocallyQuasiFinite f := by
    rw [locallyQuasiFinite_iff]
    intro U hU V hV hVpre
    have hφ : (f.appLE U V hVpre).hom.Etale := f.etale_appLE hU hV hVpre
    algebraize [(f.appLE U V hVpre).hom]
    exact Algebra.IsUnramifiedAt.instQuasiFiniteOfEssFiniteTypeOfFormallyUnramified
  have : DiscreteTopology X := isDiscrete_univ_iff.mp <| by
    simpa using
      f.isDiscrete_preimage (isDiscrete_univ_iff.mpr (inferInstance : DiscreteTopology (Spec A)))
  have : Finite X := finite_of_compact_of_discrete
  infer_instance

/-- An isomorphism of presheaves on the big fppf site is representable by étale morphisms. -/
private theorem presheaf_etale_of_isIso (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {P Q : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (e : P ⟶ Q) [IsIso e] :
    (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf e := by
  refine ⟨yoneda.relativelyRepresentable.of_isIso e, fun X Y k fst snd hsq => ?_⟩
  have : IsIso (yoneda.map snd) := hsq.isIso_snd_of_isIso
  have : IsIso snd := Yoneda.fullyFaithful.isIso_of_isIso_map snd
  show Etale ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map snd)
  infer_instance

/-- **Stacks 09TF.** A morphism from the spectrum of an Artinian ring to a quasi-separated
algebraic space is affine.

Following the source: for an étale morphism from an affine scheme `V ⟶ X`, the fibre product
`Spec(A) ×_X V` is quasi-compact because `X` is quasi-separated, and étale over `Spec(A)`, whose
topology is discrete; so it is a scheme with finite discrete underlying space, hence affine. -/
@[stacks 09TF]
theorem isAffineHom_of_isArtinianRing
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (hZ : B.Contains (⊤_ Scheme.{u}))
    (F : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hF : AlgebraicGeometry.IsAlgebraicSpace B S hS F)
    (hqs : AlgebraicGeometry.Space.IsAbsolutelyQuasiSeparated B S hS hZ F)
    (A : CommRingCat.{u}) [IsArtinianRing A]
    (hA : B.Contains (Spec A)) (p : B.obj hA ⟶ B.obj hS)
    (f : yoneda.obj (Over.mk p) ⟶ F) :
    AlgebraicGeometry.Space.IsAffineHom B S hS f := by
  let T := AlgebraicGeometry.BigFppfOver.toScheme B S hS
  let U : AlgebraicGeometry.BigFppfOver B S hS := Over.mk p
  have hUaff : IsAffine (T.obj U) := inferInstanceAs (IsAffine (Spec A))
  have hlocal :
      ∀ (V : AlgebraicGeometry.BigAffineFppf B S hS)
        (g : yoneda.obj ((AlgebraicGeometry.BigAffineFppf.inclusion B S hS).obj V) ⟶ F),
        AlgebraicGeometry.Space.IsEtale B S hS g →
          ∃ (W : AlgebraicGeometry.BigAffineFppf B S hS)
            (p' : yoneda.obj ((AlgebraicGeometry.BigAffineFppf.inclusion B S hS).obj W) ⟶
              yoneda.obj U)
            (q : (AlgebraicGeometry.BigAffineFppf.inclusion B S hS).obj W ⟶
              (AlgebraicGeometry.BigAffineFppf.inclusion B S hS).obj V),
            IsPullback p' (yoneda.map q) f g := by
    intro V g hg
    let V' := (AlgebraicGeometry.BigAffineFppf.inclusion B S hS).obj V
    obtain ⟨W, hWcompact, ⟨e⟩⟩ :=
      ((AlgebraicGeometry.Space.isAbsolutelyQuasiSeparated_iff_compactSpace_pullback_affine
          B S hS hZ F hF).mp hqs)
        U V' f g hUaff (AlgebraicGeometry.BigAffineFppf.isAffine_toScheme_obj B S hS V)
    let Vsp : AlgebraicSpaces B S hS :=
      ⟨yoneda.obj V', AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS V'⟩
    let Usp : AlgebraicSpaces B S hS :=
      ⟨yoneda.obj U, AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS U⟩
    let Fsp : AlgebraicSpaces B S hS := ⟨F, hF⟩
    let gsp : Vsp ⟶ Fsp := ObjectProperty.homMk g
    let fsp : Usp ⟶ Fsp := ObjectProperty.homMk f
    let Psp := AlgebraicSpaces.fiberProduct B S hS fsp gsp
    let toU : Psp ⟶ Usp := ObjectProperty.homMk (pullback.fst f g)
    let toV : Psp ⟶ Vsp := ObjectProperty.homMk (pullback.snd f g)
    have hEtaleP : AlgebraicGeometry.Space.IsEtale B S hS toU.hom :=
      AlgebraicGeometry.Space.isEtale_of_isPullback B S hS toV toU gsp fsp
        (AlgebraicSpaces.isPullback_fiberProduct B S hS fsp gsp).flip hg
    let q : W ⟶ U := yoneda.preimage (e.hom ≫ toU.hom)
    let r : W ⟶ V' := yoneda.preimage (e.hom ≫ toV.hom)
    have hMapEtale : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
        T).presheaf (yoneda.map q) := by
      rw [show yoneda.map q = e.hom ≫ toU.hom by simp [q]]
      exact hEtaleP W e.hom (presheaf_etale_of_isIso B S hS e.hom)
    have : Etale (T.map q) :=
      hMapEtale.2 (g := 𝟙 (yoneda.obj U)) (fst := 𝟙 (yoneda.obj W)) q IsPullback.of_id_fst
    have hr : yoneda.map r = e.hom ≫ toV.hom := by simp [r]
    refine ⟨⟨W, isAffine_of_etale_of_isArtinianRing (A := A) (T.map q)⟩,
      e.hom ≫ pullback.fst f g, r, ?_⟩
    refine IsPullback.of_iso_pullback (fst := e.hom ≫ pullback.fst f g) (snd := yoneda.map r)
      (f := f) (g := g) ⟨?_⟩ e rfl hr.symm
    rw [hr]
    show (e.hom ≫ pullback.fst f g) ≫ f = (e.hom ≫ pullback.snd f g) ≫ g
    simp [pullback.condition]
  exact ((AlgebraicGeometry.Space.isAffineHom_tfae_of_isAlgebraicSpace B S hS f
      (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS (Over.mk p)) hF).out 3 2).mp hlocal

end AlgebraicGeometry.Space

end
