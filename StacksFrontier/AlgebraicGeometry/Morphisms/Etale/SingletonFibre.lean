module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import Mathlib.RingTheory.KrullDimension.Zero
public import Mathlib.RingTheory.Unramified.Field
public import StacksCore.Tactic.StacksAttribute

/-!
# A finite étale morphism with a single purely inseparable point

A finite étale morphism `f : X ⟶ S` whose fibre over a point `s` consists of a single point `x`
with `κ(s) ⊂ κ(x)` purely inseparable is an isomorphism over an open neighbourhood of `s`.

The proof runs through the rank function `AlgebraicGeometry.Scheme.Hom.finrank` of a finite flat
morphism. Two steps: the rank of `f` at `s` is `1`, because the scheme-theoretic fibre over `s`
is the spectrum of a field that is both separable and purely inseparable over `κ(s)`; and a
finite flat morphism of rank `1` near a point is an isomorphism over a neighbourhood of it,
because the rank function is locally constant.

## Main definitions

No new definitions are introduced.

## Main results

* `AlgebraicGeometry.exists_open_restrict_isIso_of_finite_etale_fiber_eq_singleton`: Tag 04DH,
  the open neighbourhood on which the morphism is an isomorphism.
* `AlgebraicGeometry.exists_open_restrict_isIso_of_finrank_eq_one`: a finite flat morphism
  locally of finite presentation whose rank at `s` is `1` is an isomorphism over an open
  neighbourhood of `s`.
* `AlgebraicGeometry.isIso_fiberToSpecResidueField_of_preimage_singleton`: the fibre of a finite
  étale morphism over a point with a single preimage and surjective residue field map is the
  spectrum of the residue field of the base point.
* `Algebra.FormallyUnramified.isField_of_subsingleton_primeSpectrum`: a nontrivial finite
  formally unramified algebra over a field whose spectrum is a single point is a field.

## Implementation notes

The inverse-image scheme over an open `U` and its morphism to `U` are represented by Mathlib's
restriction `Scheme.Hom.restrict`, and the algebra structure on the residue field at the unique
point of the fibre is the canonical one induced by `Scheme.Hom.residueFieldMap`; both as in the
statement of the tag.

Separability of the residue field extension is not proved here: it is Mathlib's instance for a
formally unramified morphism locally of finite type. Together with the purely inseparable
hypothesis it gives surjectivity of the residue field map, which is the only form in which the
hypothesis is used.

The fibre is identified with the spectrum of a ring by `Scheme.isoSpec`, and the two ring maps
`κ(s) ⟶ Γ(X_s, ⊤)` and `Γ(X_s, ⊤) ⟶ κ(x)` are produced by surjectivity of `Spec.map` rather
than written down; faithfulness of `Spec` then turns
`Scheme.Hom.asFiberHom_fiberToSpecResidueField` into the factorisation of the residue field map
through `Γ(X_s, ⊤)`. Surjectivity of `κ(s) ⟶ Γ(X_s, ⊤)` follows because `Γ(X_s, ⊤) ⟶ κ(x)` is
injective, the fibre ring being a field.

## References

* [Stacks Project, Tag 04DH](https://stacks.math.columbia.edu/tag/04DH)
-/

@[expose] public section

open CategoryTheory Limits TopologicalSpace

universe u

namespace Algebra.FormallyUnramified

/-- A nontrivial algebra over a field which is module-finite, formally unramified and has a
single prime ideal is a field.

This is the fibre of a finite étale morphism over a point at which the fibre is a single point:
formal unramifiedness over a field forces the algebra to be reduced, and a nontrivial reduced
ring with a unique prime is a field. -/
theorem isField_of_subsingleton_primeSpectrum (K C : Type*) [Field K] [CommRing C] [Nontrivial C]
    [Algebra K C] [Module.Finite K C] [Algebra.FormallyUnramified K C]
    [Subsingleton (PrimeSpectrum C)] :
    IsField C :=
  have := Algebra.FormallyUnramified.isReduced_of_field K C
  PrimeSpectrum.subsingleton_iff_isField_of_isReduced.mp ‹_›

end Algebra.FormallyUnramified

namespace AlgebraicGeometry

/-- A finite flat morphism locally of finite presentation whose rank at a point `s` of the target
is `1` is an isomorphism over an open neighbourhood of `s`.

The rank function of such a morphism is locally constant, so it is constantly `1` on some open
neighbourhood `U` of `s`; the restriction over `U` is a base change of `f`, hence has the same
rank function, and a finite flat morphism of constant rank `1` is an isomorphism. -/
theorem exists_open_restrict_isIso_of_finrank_eq_one {X S : Scheme.{u}} (f : X ⟶ S) [IsFinite f]
    [Flat f] [LocallyOfFinitePresentation f] (s : S) (hs : f.finrank s = 1) :
    ∃ U : S.Opens, s ∈ U ∧ IsIso (f ∣_ U) := by
  obtain ⟨V, hV, hsV, hconst⟩ :=
    (IsLocallyConstant.iff_exists_open f.finrank).mp f.isLocallyConstant_finrank s
  refine ⟨⟨V, hV⟩, hsV, ?_⟩
  rw [Scheme.Hom.isIso_iff_finrank_eq]
  funext t
  rw [Scheme.Hom.finrank_of_isPullback _ _ _ _
    (isPullback_morphismRestrict f ⟨V, hV⟩).flip t]
  simp only [Pi.one_apply]
  exact (hconst _ t.2).trans hs

/-- For a finite étale morphism `f : X ⟶ S` whose fibre over `f x` is the single point `x` and
whose residue field map at `x` is surjective, the scheme-theoretic fibre over `f x` is the
spectrum of `κ(f x)`. -/
theorem isIso_fiberToSpecResidueField_of_preimage_singleton {X S : Scheme.{u}} (f : X ⟶ S)
    [IsFinite f] [Etale f] (x : X) (hfiber : f ⁻¹' {f x} = {x})
    (hsurj : Function.Surjective (f.residueFieldMap x).hom) :
    IsIso (f.fiberToSpecResidueField (f x)) := by
  have hsub0 : Subsingleton (f ⁻¹' {f x} : Set X) := by
    rw [hfiber]
    infer_instance
  have hsub : Subsingleton (f.fiber (f x)) := (f.fiberHomeo (f x)).toEquiv.subsingleton
  obtain ⟨φ, hφ⟩ := Spec.map_surjective
    ((f.fiber (f x)).isoSpec.inv ≫ f.fiberToSpecResidueField (f x))
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective
    (f.asFiberHom x ≫ (f.fiber (f x)).isoSpec.hom)
  have hfac : f.residueFieldMap x = φ ≫ ψ := by
    apply Spec.map_injective
    rw [Spec.map_comp, hψ, hφ, ← f.asFiberHom_fiberToSpecResidueField x]
    simp
  have hφ' : IsFinite (Spec.map φ) ∧ Etale (Spec.map φ) := by
    have : IsFinite (f.fiberToSpecResidueField (f x)) :=
      inferInstanceAs (IsFinite (pullback.snd f (S.fromSpecResidueField (f x))))
    have : Etale (f.fiberToSpecResidueField (f x)) :=
      inferInstanceAs (Etale (pullback.snd f (S.fromSpecResidueField (f x))))
    rw [hφ]
    exact ⟨inferInstance, inferInstance⟩
  have hnontriv : Nontrivial Γ(f.fiber (f x), ⊤) :=
    PrimeSpectrum.nontrivial ((f.fiber (f x)).isoSpec.hom (f.asFiber x))
  have hspec : Subsingleton (PrimeSpectrum Γ(f.fiber (f x), ⊤)) :=
    (Scheme.homeoOfIso (f.fiber (f x)).isoSpec).symm.toEquiv.subsingleton
  let _ : Algebra (S.residueField (f x)) Γ(f.fiber (f x), ⊤) := φ.hom.toAlgebra
  have : Module.Finite (S.residueField (f x)) Γ(f.fiber (f x), ⊤) :=
    RingHom.finite_algebraMap.mp
      (by rw [RingHom.algebraMap_toAlgebra]; exact (IsFinite.SpecMap_iff φ).mp hφ'.1)
  have : Algebra.FormallyUnramified (S.residueField (f x)) Γ(f.fiber (f x), ⊤) :=
    RingHom.formallyUnramified_algebraMap.mp (by
      rw [RingHom.algebraMap_toAlgebra]
      exact ((HasRingHomProperty.Spec_iff (P := @Etale)).mp hφ'.2).formallyUnramified)
  have hfield : IsField Γ(f.fiber (f x), ⊤) :=
    Algebra.FormallyUnramified.isField_of_subsingleton_primeSpectrum
      (S.residueField (f x)) Γ(f.fiber (f x), ⊤)
  have hψinj : Function.Injective ψ.hom := by
    let := hfield.toField
    exact ψ.hom.injective
  have hφsurj : Function.Surjective φ.hom := fun c => by
    obtain ⟨k, hk⟩ := hsurj (ψ.hom c)
    refine ⟨k, hψinj ?_⟩
    rw [← hk, hfac]
    rfl
  have : IsIso φ := (ConcreteCategory.isIso_iff_bijective _).mpr ⟨φ.hom.injective, hφsurj⟩
  have hiso : IsIso (Spec.map φ) := inferInstance
  rw [hφ] at hiso
  exact IsIso.of_isIso_comp_left (f.fiber (f x)).isoSpec.inv _

/-- **Stacks Project, Tag 04DH.** A finite étale morphism with a singleton fibre and purely
inseparable residue-field extension is an isomorphism over some open neighbourhood of the
point in the target. -/
@[stacks 04DH]
theorem exists_open_restrict_isIso_of_finite_etale_fiber_eq_singleton
    {X S : Scheme.{u}} (f : X ⟶ S) [IsFinite f] [Etale f]
    (s : S) (x : X) (hfiber : f ⁻¹' {s} = {x})
    (hpure :
      let hxs : f x = s := by
        have : x ∈ f ⁻¹' {s} := by simp [hfiber]
        simpa only [Set.mem_preimage, Set.mem_singleton_iff] using this
      letI := ((S.residueFieldCongr hxs).inv ≫ f.residueFieldMap x).hom.toAlgebra
      IsPurelyInseparable (S.residueField s) (X.residueField x)) :
    ∃ U : S.Opens, s ∈ U ∧ IsIso (f ∣_ U) := by
  have hxs : f x = s := by
    have : x ∈ f ⁻¹' {s} := by simp [hfiber]
    simpa only [Set.mem_preimage, Set.mem_singleton_iff] using this
  subst hxs
  -- The residue field extension is separable and purely inseparable, hence trivial.
  let _ : Algebra (S.residueField (f x)) (X.residueField x) := (f.residueFieldMap x).hom.toAlgebra
  have : IsPurelyInseparable (S.residueField (f x)) (X.residueField x) := hpure
  have hsurj : Function.Surjective (f.residueFieldMap x).hom :=
    IsPurelyInseparable.surjective_algebraMap_of_isSeparable
      (S.residueField (f x)) (X.residueField x)
  -- Hence the fibre is the spectrum of `κ(f x)`, so the rank of `f` at `f x` is `1`.
  have hiso := isIso_fiberToSpecResidueField_of_preimage_singleton f x hfiber hsurj
  have hrank : f.finrank (f x) = 1 := by
    have key : (f.fiberToSpecResidueField (f x)).finrank = 1 :=
      Scheme.Hom.finrank_eq_one_of_isIso _
    have hpb := Scheme.Hom.finrank_pullback_snd f (S.fromSpecResidueField (f x))
      (default : Spec (S.residueField (f x)))
    rw [Scheme.fromSpecResidueField_apply] at hpb
    rw [← hpb]
    exact congrFun key default
  exact exists_open_restrict_isIso_of_finrank_eq_one f (f x) hrank

end AlgebraicGeometry

end
