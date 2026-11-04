module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.RingTheory.Etale.Field
public import Mathlib.RingTheory.Etale.Finite
public import StacksFrontier.AlgebraicGeometry.Morphisms.Etale.Defs
public import StacksFrontier.AlgebraicGeometry.Morphisms.Unramified.Fibers
public import StacksFrontier.AlgebraicGeometry.Scheme.Immersion.Monomorphism
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Étale schemes over a field and fibres of étale morphisms

A scheme étale over the spectrum of a field is precisely a disjoint union of spectra of finite
separable extensions of that field. Consequently, every fibre of an étale morphism has this form
over the residue field of its base point.

## Main definitions

No new definitions are introduced.

## Main results

* `AlgebraicGeometry.etale_iff_iso_coproduct_spectra_finite_separable` characterizes morphisms
  étale over a field by such a decomposition.
* `AlgebraicGeometry.Etale.exists_iso_fiber_coproduct_spectra_finite_separable` describes the
  fibres of an étale morphism.
* `AlgebraicGeometry.isFinite_of_isAffine_of_etale_over_field`: an *affine* scheme étale over
  the spectrum of a field is finite over it.
* `AlgebraicGeometry.exists_finite_iso_coproduct_spectra_of_isAffine_of_etale_over_field`: for an
  affine source the index set of the decomposition is finite.
* `AlgebraicGeometry.isAffine_of_mono_of_etale_over_field`: the source of a monomorphism into an
  affine scheme étale over the spectrum of a field is affine.

## Implementation notes

The isomorphism with the coproduct is required to respect the given morphism to the spectrum of
the base field. A finite separable extension is expressed by `Module.Finite` together with
`Algebra.IsSeparable`.

For an affine source the decomposition is finite, and the morphism to the spectrum of the base
field is finite. Both come from the ring-theoretic structure of an étale algebra over a field
(`Algebra.Etale.iff_exists_algEquiv_prod`, `Algebra.FormallyUnramified.finite_of_free`) applied to
the global sections, rather than from the decomposition of the scheme: the general decomposition
says nothing about the size of its index set.

Over a field, étaleness coincides with unramifiedness: a morphism to the spectrum of a field is
locally of finite type and formally unramified exactly when it is étale, because finite type over
a field upgrades to finite presentation. The characterization is therefore obtained from the
corresponding statement for unramified morphisms, and the statement about fibres follows from it
by base change along the inclusion of the residue field of the base point.

## References

* [Stacks Project, Tag 03PC](https://stacks.math.columbia.edu/tag/03PC)
* [Stacks Project, Tag 02GL](https://stacks.math.columbia.edu/tag/02GL)
* [Stacks Project, Tag 03II](https://stacks.math.columbia.edu/tag/03II)
-/

@[expose] public section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry

/-- **Stacks Project, Tag 03PC (over a field).** A morphism to the spectrum of a field is
étale if and only if its source is, over that spectrum, a coproduct of spectra of finite
separable field extensions. -/
@[stacks 03PC "over_field", stacks 03II "etale_over_field",
  ega "IV 17.6.2" "base = Spec k", sga "4½ Arcata 2.1.2" "a)"]
public theorem etale_iff_iso_coproduct_spectra_finite_separable
    (k : Type u) [Field k] {U : Scheme.{u}} (f : U ⟶ Spec (.of k)) :
    Etale f ↔
      ∃ (I : Type u) (K : I → Type u) (_ : ∀ i, Field (K i))
        (_ : ∀ i, Algebra k (K i)) (_ : ∀ i, Module.Finite k (K i))
        (_ : ∀ i, Algebra.IsSeparable k (K i))
        (e : U ≅ ∐ fun i ↦ Spec (.of (K i))),
        e.hom ≫ Sigma.desc (fun i ↦ Spec.map (CommRingCat.ofHom (algebraMap k (K i)))) = f := by
  constructor
  · intro hf
    exact (unramified_iff_iso_coproduct_spectra_finite_separable k f).mp
      ((unramified_iff_locallyOfFiniteType_and_formallyUnramified f).mpr
        ⟨inferInstance, inferInstance⟩)
  · rintro ⟨I, K, hK, hAlg, hFin, hSep, e, he⟩
    let (i : I) : Field (K i) := hK i
    let (i : I) : Algebra k (K i) := hAlg i
    let (i : I) : Module.Finite k (K i) := hFin i
    let (i : I) : Algebra.IsSeparable k (K i) := hSep i
    let : IsZariskiLocalAtSource (@Etale : MorphismProperty Scheme.{u}) :=
      HasRingHomProperty.instIsZariskiLocalAtSource (Q := @RingHom.Etale)
    let : Etale (Sigma.desc fun i ↦ Spec.map (CommRingCat.ofHom (algebraMap k (K i)))) :=
      IsZariskiLocalAtSource.sigmaDesc (fun i ↦ by
        rw [HasRingHomProperty.Spec_iff (P := @Etale)]
        change (algebraMap k (K i)).Etale
        rw [RingHom.etale_algebraMap]
        exact ⟨Algebra.FormallyEtale.of_isSeparable k (K i),
          Algebra.FinitePresentation.of_finiteType.mp inferInstance⟩)
    rw [← he]
    infer_instance

add_to_stacks 02GL "part (1)"
  AlgebraicGeometry.etale_iff_iso_coproduct_spectra_finite_separable

/-- **Stacks Project, Tag 02GL, part (2).** Every fibre of an étale morphism is, over the
residue field of the base point, a coproduct of spectra of finite separable field extensions. -/
@[stacks 02GL "part (2)", ega "IV 17.6.2" "a) => c')"]
public theorem Etale.exists_iso_fiber_coproduct_spectra_finite_separable
    {X S : Scheme.{u}} (f : X ⟶ S) [Etale f] (s : S) :
    ∃ (I : Type u) (K : I → Type u) (_ : ∀ i, Field (K i))
      (_ : ∀ i, Algebra (S.residueField s) (K i))
      (_ : ∀ i, Module.Finite (S.residueField s) (K i))
      (_ : ∀ i, Algebra.IsSeparable (S.residueField s) (K i))
      (e : f.fiber s ≅ ∐ fun i ↦ Spec (.of (K i))),
      e.hom ≫ Sigma.desc (fun i ↦
        Spec.map (CommRingCat.ofHom (algebraMap (S.residueField s) (K i)))) =
        f.fiberToSpecResidueField s :=
  (etale_iff_iso_coproduct_spectra_finite_separable (S.residueField s)
    (f.fiberToSpecResidueField s)).mp
    (by change Etale (pullback.snd f (S.fromSpecResidueField s)); infer_instance)

/-! ### Affine schemes étale over a field -/

section Affine

variable (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- The algebra structure on the global sections of a scheme over the spectrum of a field,
induced by the structure morphism through the identification of `k` with the global sections of
`Spec k`. -/
public noncomputable abbrev globalSectionsAlgebra : Algebra k Γ(X, ⊤) :=
  ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom.toAlgebra

/-- The global sections of an affine scheme étale over the spectrum of a field form an étale
algebra over that field. -/
public theorem algebra_etale_globalSections [IsAffine X] [Etale f] :
    letI := globalSectionsAlgebra k f
    Algebra.Etale k Γ(X, ⊤) := by
  let := globalSectionsAlgebra k f
  have happ : RingHom.Etale f.appTop.hom :=
    (HasRingHomProperty.iff_of_isAffine (P := @Etale)).mp inferInstance
  have hφ : RingHom.Etale ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom :=
    (RingHom.Etale.respectsIso.cancel_left_isIso (Scheme.ΓSpecIso (.of k)).inv f.appTop).2 happ
  rw [← RingHom.etale_algebraMap]
  exact hφ

/-- **An affine scheme étale over the spectrum of a field is finite over it.** The global
sections form an étale algebra over the field, hence a finite module over it. -/
public theorem isFinite_of_isAffine_of_etale_over_field [IsAffine X] [Etale f] : IsFinite f := by
  let := globalSectionsAlgebra k f
  let : Algebra.Etale k Γ(X, ⊤) := algebra_etale_globalSections k f
  have hmod : Module.Finite k Γ(X, ⊤) := Algebra.FormallyUnramified.finite_of_free k Γ(X, ⊤)
  have hspec : IsFinite (Spec.map ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop)) :=
    (IsFinite.SpecMap_iff _).2 (RingHom.finite_algebraMap.2 hmod)
  have hf : X.isoSpec.hom ≫ Spec.map ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop) = f := by
    calc
      X.isoSpec.hom ≫ Spec.map ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop) =
          X.isoSpec.hom ≫ Spec.map f.appTop ≫ Spec.map (Scheme.ΓSpecIso (.of k)).inv := by
        rw [Spec.map_comp]
      _ = (f ≫ (Spec (.of k)).isoSpec.hom) ≫ Spec.map (Scheme.ΓSpecIso (.of k)).inv := by
        rw [← Category.assoc, Scheme.isoSpec_hom_naturality f]
      _ = f := by
        change (f ≫ (Spec (.of k)).toSpecΓ) ≫ Spec.map (Scheme.ΓSpecIso (.of k)).inv = f
        rw [Category.assoc, toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]
  have : IsFinite (X.isoSpec.hom ≫ Spec.map ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop)) :=
    inferInstance
  rwa [hf] at this

/-- **An affine scheme étale over the spectrum of a field is a *finite* disjoint union of spectra
of finite separable extensions.**

`AlgebraicGeometry.etale_iff_iso_coproduct_spectra_finite_separable` decomposes an arbitrary
source and identifies the morphism to `Spec k`, but says nothing about the size of the index set;
affineness is exactly what makes the index set finite. The isomorphism here is not claimed to be
compatible with the morphisms to `Spec k`. -/
public theorem exists_finite_iso_coproduct_spectra_of_isAffine_of_etale_over_field
    [IsAffine X] [Etale f] :
    ∃ (I : Type u) (_ : Finite I) (K : I → Type u) (_ : ∀ i, Field (K i))
      (_ : ∀ i, Algebra k (K i)) (_ : ∀ i, Module.Finite k (K i))
      (_ : ∀ i, Algebra.IsSeparable k (K i)),
      Nonempty (X ≅ ∐ fun i ↦ Spec (.of (K i))) := by
  let := globalSectionsAlgebra k f
  let : Algebra.Etale k Γ(X, ⊤) := algebra_etale_globalSections k f
  obtain ⟨I, hI, K, hfield, halg, e, hprops⟩ :=
    (Algebra.Etale.iff_exists_algEquiv_prod k Γ(X, ⊤)).mp inferInstance
  let := hI
  let (i : I) : Field (K i) := hfield i
  let (i : I) : Algebra k (K i) := halg i
  have hiso : IsIso (CommRingCat.ofHom e.toRingEquiv.toRingHom :
      CommRingCat.of Γ(X, ⊤) ⟶ CommRingCat.of (∀ i, K i)) :=
    (ConcreteCategory.isIso_iff_bijective _).2 e.toRingEquiv.bijective
  refine ⟨I, hI, K, hfield, halg, fun i ↦ (hprops i).1, fun i ↦ (hprops i).2,
    ⟨X.isoSpec ≪≫ (Scheme.Spec.mapIso (asIso (CommRingCat.ofHom
        e.toRingEquiv.toRingHom)).op).symm ≪≫
      (asIso (sigmaSpec fun i ↦ CommRingCat.of (K i))).symm⟩⟩

/-- **The source of a monomorphism into an affine scheme étale over the spectrum of a field is
affine.** The target is a finite disjoint union of spectra of fields, and a monomorphism into
such a disjoint union is the inclusion of a subfamily of its components. -/
public theorem isAffine_of_mono_of_etale_over_field [IsAffine X] [Etale f] {Y : Scheme.{u}}
    (g : Y ⟶ X) [Mono g] : IsAffine Y := by
  obtain ⟨I, hI, K, hfield, _, _, _, ⟨e⟩⟩ :=
    exists_finite_iso_coproduct_spectra_of_isAffine_of_etale_over_field k f
  let := hI
  let (i : I) : Field (K i) := hfield i
  have : Mono (g ≫ e.hom) := inferInstance
  obtain ⟨J, eJ, -⟩ := exists_iso_coproduct_spec_of_mono K (g ≫ e.hom)
  let : Finite J := Finite.of_injective Subtype.val Subtype.val_injective
  exact IsAffine.of_isIso eJ.hom

end Affine

end AlgebraicGeometry
