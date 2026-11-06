module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.AbsolutelyIntegrallyClosed.ConstantSheafSections
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.AbsolutelyIntegrallyClosed.LocallyConstantCoboundary
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.AbsolutelyIntegrallyClosedVanishing

/-!
# Vanishing of the higher étale cohomology of a finite constant sheaf on an absolutely
integrally closed ring

Let `R` be an absolutely integrally closed ring and let `M` be a finite abelian group. Then
`H^i(Spec R, M) = 0` for `i > 0`.

## Main results

* `Stacks.EtaleCohomology.AbsolutelyIntegrallyClosed.sectionsSub_constantSheaf` — the
  degree-zero gluing condition for a finite constant sheaf on the pairs of basic opens
  `D(f(f + g))`, `D(g(f + g))`.
* `Stacks.EtaleCohomology.AbsolutelyIntegrallyClosed.subsingleton_H_constantSheaf_of_finite` —
  **Stacks 0GY7**.

## Implementation notes

Vanishing is `Subsingleton` of `CategoryTheory.Sheaf.H`, as in Stacks 0GY0; the site is
`Stacks.EtaleCohomology.MayerVietoris.topology`, the one-universe model of the small étale site
of `Spec R` on which `CategoryTheory.Sheaf.H'` and the Mayer--Vietoris sequence are available.

Everything except the degree-zero gluing condition is
`Stacks.EtaleCohomology.AbsolutelyIntegrallyClosed.subsingleton_H_of_sectionsSub`. That
condition is discharged here by combining two inputs. The first identifies degree-zero
cohomology over an open subscheme with the locally constant `M`-valued maps on it, through
`Stacks.Cohomology.FreeYoneda.extSectionsAddEquiv` (degree-zero cohomology is sections) and
`Stacks.EtaleCohomology.ConstantSections.opensIsoLocallyConstant` (Stacks 03P5 for the constant
sheaf, transported to this site). The second is the coboundary statement
`exists_locallyConstant_coboundary_on_basicOpen_sum`, which is the source's own argument with the
short exact sequence of group schemes of Stacks 0GY4.

The overlap `D(f(f + g)) ⊓ D(g(f + g))` is the basic open of the product of the two elements,
and the coboundary statement is stated there; the two presentations of that open are identified
by `Homeomorph.setCongr`, no point of the spectrum being moved.

## References

* [Stacks Project, Tag 0GY7](https://stacks.math.columbia.edu/tag/0GY7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry Opposite
  TopologicalSpace
open Stacks.Cohomology.FreeYoneda Stacks.EtaleCohomology.ConstantSections

universe u

namespace Stacks.EtaleCohomology.AbsolutelyIntegrallyClosed

variable {R : Type u} [CommRing R]

/-- Degree-zero étale cohomology over the open subschemes of a scheme is the presheaf of
sections: `Stacks.Cohomology.FreeYoneda.cohomologyPresheafIsoSections`, restricted along the
inclusion of the opens into the one-universe model of the small étale site. -/
private def opensCohomologyZeroIsoSections {Y : Scheme.{u}}
    (F : Sheaf (MayerVietoris.topology Y) AddCommGrpCat.{u + 1}) :
    Stacks.EtaleCohomology.StrictlyHenselian.opensCohomology F 0 ≅
      (MayerVietoris.opensToSite Y).op ⋙ F.obj :=
  Functor.isoWhiskerLeft (MayerVietoris.opensToSite Y).op (cohomologyPresheafIsoSections F)

/-- **Degree-zero étale cohomology of a constant sheaf over an open subscheme is the group of
locally constant functions on it.** -/
private def opensCohomologyZeroIsoLocallyConstant {Y : Scheme.{u}} (B : BigEtaleSite.{u})
    (hY : B.Contains Y) (M : AddCommGrpCat.{u + 1}) (U : Y.Opens) :
    (Stacks.EtaleCohomology.StrictlyHenselian.opensCohomology
        ((constantSheaf (MayerVietoris.topology Y) AddCommGrpCat.{u + 1}).obj M) 0).obj (op U) ≅
      AddCommGrpCat.of (LocallyConstant ((U : Y.Opens) : Set Y) (ToType M)) :=
  (opensCohomologyZeroIsoSections
      ((constantSheaf (MayerVietoris.topology Y) AddCommGrpCat.{u + 1}).obj M)).app (op U) ≪≫
    (opensIsoLocallyConstant B Y hY M U).symm

/-- **The degree-zero gluing condition for a constant sheaf is a statement about locally
constant functions.** If every locally constant `M`-valued function on `U ⊓ V` is the difference
of the restrictions of one on `U` and one on `V`, then the degree-zero cohomology classes of the
constant sheaf `M` satisfy the gluing condition of
`Stacks.EtaleCohomology.AbsolutelyIntegrallyClosed.SectionsSub`. -/
theorem sectionsSub_constantSheaf_of_exists_locallyConstant {Y : Scheme.{u}}
    (B : BigEtaleSite.{u}) (hY : B.Contains Y) (M : AddCommGrpCat.{u + 1}) (U V : Y.Opens)
    (h : ∀ τ : LocallyConstant ((U ⊓ V : Y.Opens) : Set Y) (ToType M),
      ∃ (x : LocallyConstant ((U : Y.Opens) : Set Y) (ToType M))
        (y : LocallyConstant ((V : Y.Opens) : Set Y) (ToType M)),
        ∀ q : ((U ⊓ V : Y.Opens) : Set Y),
          x ⟨q.val, (inf_le_left : U ⊓ V ≤ U) q.property⟩ -
            y ⟨q.val, (inf_le_right : U ⊓ V ≤ V) q.property⟩ = τ q) :
    SectionsSub ((constantSheaf (MayerVietoris.topology Y) AddCommGrpCat.{u + 1}).obj M) U V := by
  set F := (constantSheaf (MayerVietoris.topology Y) AddCommGrpCat.{u + 1}).obj M
  have hcomp : ∀ (W : Y.Opens)
      (z : ToType ((Stacks.EtaleCohomology.StrictlyHenselian.opensCohomology F 0).obj (op W))),
      (opensCohomologyZeroIsoLocallyConstant B hY M W).hom z =
        (opensIsoLocallyConstant B Y hY M W).inv
          ((opensCohomologyZeroIsoSections F).hom.app (op W) z) :=
    fun _ _ ↦ rfl
  have hβ : ∀ (W : Y.Opens) (hW : U ⊓ V ≤ W)
      (z : ToType ((Stacks.EtaleCohomology.StrictlyHenselian.opensCohomology F 0).obj (op W))),
      (opensCohomologyZeroIsoLocallyConstant B hY M (U ⊓ V)).hom
          ((Stacks.EtaleCohomology.StrictlyHenselian.opensCohomology F 0).map
            (homOfLE hW).op z) =
        LocallyConstant.comap ⟨fun p ↦ ⟨p.val, hW p.property⟩,
            Continuous.subtype_mk continuous_subtype_val _⟩
          ((opensCohomologyZeroIsoLocallyConstant B hY M W).hom z) := by
    intro W hW z
    have h1 : (opensCohomologyZeroIsoSections F).hom.app (op (U ⊓ V))
          ((Stacks.EtaleCohomology.StrictlyHenselian.opensCohomology F 0).map
            (homOfLE hW).op z) =
        F.obj.map ((MayerVietoris.opensToSite Y).map (homOfLE hW)).op
          ((opensCohomologyZeroIsoSections F).hom.app (op W) z) :=
      (opensCohomologyZeroIsoSections F).hom.naturality_apply (Quiver.Hom.op (homOfLE hW)) z
    have h2 := opensIsoLocallyConstant_naturality B Y hY M hW
      ((opensIsoLocallyConstant B Y hY M W).inv
        ((opensCohomologyZeroIsoSections F).hom.app (op W) z))
    rw [Iso.inv_hom_id_apply] at h2
    rw [hcomp, hcomp, h1, h2, Iso.hom_inv_id_apply]
  intro τ
  obtain ⟨x, y, hxy⟩ := h ((opensCohomologyZeroIsoLocallyConstant B hY M (U ⊓ V)).hom τ)
  refine ⟨(opensCohomologyZeroIsoLocallyConstant B hY M U).inv x,
    (opensCohomologyZeroIsoLocallyConstant B hY M V).inv y, ?_⟩
  apply (AddCommGrpCat.mono_iff_injective
    (opensCohomologyZeroIsoLocallyConstant B hY M (U ⊓ V)).hom).mp inferInstance
  rw [map_sub, hβ U inf_le_left, hβ V inf_le_right, Iso.inv_hom_id_apply,
    Iso.inv_hom_id_apply]
  exact LocallyConstant.ext hxy

/-- **The degree-zero gluing condition for a finite constant sheaf on the spectrum of an
absolutely integrally closed ring**, over the pair of basic opens `D(f(f + g))`, `D(g(f + g))`
covering `D(f + g)`.

The overlap of the two is the basic open of the product of the two elements, where the gluing
statement is `exists_locallyConstant_coboundary_on_basicOpen_sum`. -/
theorem sectionsSub_constantSheaf (hR : IsAbsolutelyIntegrallyClosed R)
    (M : AddCommGrpCat.{u + 1}) [Finite M] (f g : R) :
    SectionsSub ((constantSheaf (MayerVietoris.topology (Spec (CommRingCat.of R)))
        AddCommGrpCat.{u + 1}).obj M)
      (PrimeSpectrum.basicOpen (f * (f + g))) (PrimeSpectrum.basicOpen (g * (f + g))) := by
  have _ : Finite (ToType M) := inferInstanceAs (Finite M)
  have hinf : PrimeSpectrum.basicOpen (f * (f + g) * (g * (f + g))) =
      (PrimeSpectrum.basicOpen (f * (f + g)) ⊓ PrimeSpectrum.basicOpen (g * (f + g)) :
        (Spec (CommRingCat.of R)).Opens) :=
    PrimeSpectrum.basicOpen_mul _ _
  have hset : ((PrimeSpectrum.basicOpen (f * (f + g)) ⊓
        PrimeSpectrum.basicOpen (g * (f + g)) : (Spec (CommRingCat.of R)).Opens) :
          Set (Spec (CommRingCat.of R))) =
      (PrimeSpectrum.basicOpen (f * (f + g) * (g * (f + g))) : Set (PrimeSpectrum R)) := by
    rw [← hinf]
    rfl
  refine sectionsSub_constantSheaf_of_exists_locallyConstant
    (BigEtaleSite.containing (Spec (CommRingCat.of R)))
    (BigEtaleSite.contains_containing _) M _ _ (fun τ ↦ ?_)
  obtain ⟨a, b, hab⟩ :=
    LocallyConstantCoboundary.exists_locallyConstant_coboundary_on_basicOpen_sum hR f g
      (M := ToType M)
      (LocallyConstant.comap (ContinuousMap.mk _ (Homeomorph.setCongr hset.symm).continuous) τ)
  exact ⟨-a, -b, fun q ↦ (neg_sub_neg (a _) (b _)).trans (hab (Homeomorph.setCongr hset q))⟩

/-- **Stacks 0GY7.** Let `R` be an absolutely integrally closed ring and let `M` be a finite
abelian group. Then the étale cohomology of `Spec R` with coefficients in the constant sheaf `M`
vanishes in every positive degree.

All local rings of `R` are strictly henselian, so Stacks 0GY0 reduces the vanishing to the
degree-one condition over the covering `D(f + g) = D(f(f + g)) ∪ D(g(f + g))`, and by
Mayer--Vietoris that condition follows from the degree-zero gluing statement
`sectionsSub_constantSheaf`. -/
theorem subsingleton_H_constantSheaf_of_finite (hR : IsAbsolutelyIntegrallyClosed R)
    (M : AddCommGrpCat.{u + 1}) [Finite M] (q : ℕ) (hq : 0 < q) :
    Subsingleton (Sheaf.H.{u + 1}
      ((constantSheaf (MayerVietoris.topology (Spec (CommRingCat.of R)))
        AddCommGrpCat.{u + 1}).obj M) q) :=
  subsingleton_H_constantSheaf hR M (fun f g ↦ sectionsSub_constantSheaf hR M f g) q hq

/-- **Stacks 0GY7.** Let `R` be an absolutely integrally closed ring and let `M` be a finite
abelian group. Then `H^i_étale(Spec R, M) = 0` for `i > 0`.

This is `subsingleton_H_constantSheaf_of_finite` read on Mathlib's small étale site of `Spec R`,
to which the one-universe model used there is a dense subsite. -/
@[stacks 0GY7]
theorem subsingleton_H_constantSheaf_smallEtale (hR : IsAbsolutelyIntegrallyClosed R)
    (M : AddCommGrpCat.{u + 1}) [Finite M] (q : ℕ) (hq : 0 < q) :
    Subsingleton (Sheaf.H.{u + 1}
      ((constantSheaf (Spec (CommRingCat.of R)).smallEtaleTopology
        AddCommGrpCat.{u + 1}).obj M) q) :=
  ConstantTransport.subsingleton_H_smallEtale_of_mayerVietoris _ M q
    (subsingleton_H_constantSheaf_of_finite hR M q hq)

end Stacks.EtaleCohomology.AbsolutelyIntegrallyClosed

end
