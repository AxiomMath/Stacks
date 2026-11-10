module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.AffineDerivedEquivalenceStandard
public import StacksFrontier.AlgebraicGeometry.DerivedTildePerfect
public import StacksFrontier.AlgebraicGeometry.Perfect.BoundedLocallyFreeComplexes.CanonicalFunctor
public import StacksFrontier.AlgebraicGeometry.Perfect.BoundedLocallyFreeComplexes.Defs
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.QuasicoherentCohomology
public import StacksFrontier.CategoryTheory.Triangulated.KGroup.Equivalence
public import StacksFrontier.KTheory.Grothendieck.PerfectDerivedCategory
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.TriangulatedSubcategory

/-!
# The Grothendieck group of an affine scheme

For a commutative ring `R` the Grothendieck group `K₀(Spec R) = K₀(D_perf(𝒪_{Spec R}))` of the
affine scheme `Spec R` agrees with the Grothendieck group `K₀(R)` of finite projective
`R`-modules.

Derived sheafification `M ↦ M̃` is an equivalence `D(R) ≌ D_QCoh(𝒪_{Spec R})` ([Stacks, Tag 06Z0])
matching perfectness on the two sides ([Stacks, Tag 08EB]), and a perfect object of
`D(𝒪_{Spec R})` has quasi-coherent cohomology, so it restricts to an equivalence
`D_perf(R) ≌ D_perf(𝒪_{Spec R})`. The identification `K₀(D_perf(R)) = K₀(R)` is
[Stacks, Tag 0FCU].

The other half of [Stacks, Tag 0FDH], the identification `K'₀(Spec R) = K'₀(R)` for `R`
Noetherian, is `Stacks.AlgebraicGeometry.GrothendieckGroupAffine.affineCoherentKZeroEquiv` in
`StacksFrontier/AlgebraicGeometry/Perfect/GrothendieckGroupAffine/Basic.lean`.

## Main definitions

* `perfectInQcoh R`: the perfect objects of `D(𝒪_{Spec R})` cut out inside
  `D_QCoh(𝒪_{Spec R})` rather than inside `D(𝒪_{Spec R})`.
* `perfectQcohEquiv R`: the two spellings of `D_perf(𝒪_{Spec R})` give the same category.
* `perfEquiv R`: the equivalence `D_perf(R) ≌ D_perf(𝒪_{Spec R})`.

## Main results

* `isQuasicoherentDerived_of_isPerfect`: a perfect object of `D(𝒪_{Spec R})` lies in
  `D_QCoh(𝒪_{Spec R})`.
* `perfectInQcoh_inverseImage`: derived sheafification carries the perfect objects of `D(R)`
  exactly onto the perfect objects of `D_QCoh(𝒪_{Spec R})`.
* `exists_addEquiv_K0_perfectDerivedCategory_spec`: **[Stacks, Tag 0FDH]**, the clause
  `K₀(Spec R) = K₀(R)`.

## Implementation notes

The identification is recorded as an existence statement carrying the property that determines
it, in the shape of [Stacks, Tag 0FCU]: the class of a perfect object of `D(𝒪_{Spec R})`
isomorphic to `M̃` goes to the alternating sum of the classes of the terms of a bounded complex
of finite projective `R`-modules representing `M`. Every perfect object of `D(𝒪_{Spec R})` is of
this form, so that property determines the isomorphism.

No hypothesis is placed on `R`; the source assumes `R` Noetherian only for the second clause of
the tag.

The derived categories are those of `CategoryTheory.HasDerivedCategory.standard`, the model of
`Stacks.Perfect.BoundedLocallyFreeComplexes.PerfectDerivedCategory` and of [Stacks, Tag 0FCU],
made a local instance of priority 10000. The equivalence of [Stacks, Tag 06Z0] at this model is
in `StacksFrontier.AlgebraicGeometry.DerivedQCoh.AffineDerivedEquivalenceStandard`;
`AlgebraicGeometry.derivedTilde_isEquivalence` is the same statement at the locally small model.

The perfect objects of `D(𝒪_{Spec R})` are cut out of `D(𝒪_{Spec R})`, whereas the restriction of
an equivalence onto `D_QCoh(𝒪_{Spec R})` cuts them out of `D_QCoh(𝒪_{Spec R})`;
`perfectQcohEquiv` compares the two. Perfectness over `R` is spelled by
`StacksDraft.Perfect.IsPerfect` in [Stacks, Tag 08EB] and by the triangulated envelope of `R` in
[Stacks, Tag 0FCU]; the two are the same object property by
`StacksDraft.Perfect.isPerfect_eq_triangEnvelope_singleton_regularModule`, and the envelope
spelling is the one used here.

## References

* [Stacks Project, Tag 0FDH](https://stacks.math.columbia.edu/tag/0FDH)
* [Stacks Project, Tag 0FCU](https://stacks.math.columbia.edu/tag/0FCU)
* [Stacks Project, Tag 08EB](https://stacks.math.columbia.edu/tag/08EB)
* [Stacks Project, Tag 06Z0](https://stacks.math.columbia.edu/tag/06Z0)
* [Stacks Project, Tag 08E5](https://stacks.math.columbia.edu/tag/08E5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Perfect.BoundedLocallyFreeComplexes (PerfectDerivedCategory)

universe u

attribute [local instance 10000] HasDerivedCategory.standard

namespace Stacks.AlgebraicGeometry.GrothendieckGroupAffine

variable (R : CommRingCat.{u})

/-! ### Perfect objects of `D(𝒪_{Spec R})` have quasi-coherent cohomology -/

/-- A perfect object of `D(𝒪_{Spec R})` lies in `D_QCoh(𝒪_{Spec R})`: it is pseudo-coherent
([Stacks, Tag 08CQ]) and a pseudo-coherent object of the derived category of a scheme has
quasi-coherent cohomology in every degree ([Stacks, Tag 08E5]). -/
theorem isQuasicoherentDerived_of_isPerfect (K : DerivedCategory (Spec R).Modules)
    (hK : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := (Spec R).toRingedSpace) K) :
    StandardModel.derivedQuasicoherent R K :=
  AlgebraicGeometry.isQuasicoherentDerived_of_isPseudoCoherent (Spec R) K
    (Stacks.Cohomology.TorAmplitude.isPseudoCoherent_of_isPerfect K hK)

/-! ### The two spellings of `D_perf(𝒪_{Spec R})` -/

/-- Perfectness of an object of `D(𝒪_{Spec R})` is invariant under isomorphism. -/
private theorem isPerfect_iff_of_iso {K L : DerivedCategory (Spec R).Modules} (e : K ≅ L) :
    Stacks.Cohomology.PerfectComplexes.IsPerfect (X := (Spec R).toRingedSpace) K ↔
      Stacks.Cohomology.PerfectComplexes.IsPerfect (X := (Spec R).toRingedSpace) L :=
  ⟨Stacks.Cohomology.PerfectComplexTriangles.isPerfect_of_iso (X := (Spec R).toRingedSpace) e,
    Stacks.Cohomology.PerfectComplexTriangles.isPerfect_of_iso (X := (Spec R).toRingedSpace)
      e.symm⟩

/-- The perfect objects of `D(𝒪_{Spec R})`, cut out of `D_QCoh(𝒪_{Spec R})`. -/
abbrev perfectInQcoh : ObjectProperty (StandardModel.derivedQuasicoherent R).FullSubcategory :=
  fun E => Stacks.Cohomology.PerfectComplexes.IsPerfect (X := (Spec R).toRingedSpace) E.obj

/-- Perfectness in `D_QCoh(𝒪_{Spec R})` is closed under isomorphisms. -/
instance perfectInQcoh_isClosedUnderIsomorphisms :
    (perfectInQcoh R).IsClosedUnderIsomorphisms :=
  ⟨fun e hX => Stacks.Cohomology.PerfectComplexTriangles.isPerfect_of_iso
    (X := (Spec R).toRingedSpace) ((StandardModel.derivedQuasicoherent R).ι.mapIso e) hX⟩

/-- Perfectness may equivalently be imposed on all of `D(𝒪_{Spec R})` or on
`D_QCoh(𝒪_{Spec R})`: the two full subcategories are equivalent. -/
def perfectQcohEquiv : (perfectInQcoh R).FullSubcategory ≌ PerfectDerivedCategory (Spec R) := by
  let Pperf : ObjectProperty (DerivedCategory (Spec R).Modules) :=
    fun K => Stacks.Cohomology.PerfectComplexes.IsPerfect (X := (Spec R).toRingedSpace) K
  let F₁ : (perfectInQcoh R).FullSubcategory ⥤ Pperf.FullSubcategory :=
    Pperf.lift ((perfectInQcoh R).ι ⋙ (StandardModel.derivedQuasicoherent R).ι)
      (fun E => E.property)
  let G₁ : Pperf.FullSubcategory ⥤ (perfectInQcoh R).FullSubcategory :=
    (perfectInQcoh R).lift
      ((StandardModel.derivedQuasicoherent R).lift Pperf.ι
        (fun K => isQuasicoherentDerived_of_isPerfect R K.obj K.property))
      (fun K => K.property)
  exact
    { functor := F₁
      inverse := G₁
      unitIso := NatIso.ofComponents
        (fun E => (perfectInQcoh R).isoMk
          ((StandardModel.derivedQuasicoherent R).isoMk (Iso.refl E.obj.obj)))
        (fun _ => (perfectInQcoh R).hom_ext
          ((StandardModel.derivedQuasicoherent R).hom_ext (by simp [F₁, G₁])))
      counitIso := NatIso.ofComponents (fun K => Pperf.isoMk (Iso.refl K.obj))
        (fun _ => Pperf.hom_ext (by simp [F₁, G₁]))
      functor_unitIso_comp := fun _ => Pperf.hom_ext (by simp [F₁, G₁]) }

/-! ### `D_perf(R) = D_perf(𝒪_{Spec R})` -/

/-- **[Stacks, Tag 08EB] as an identity of object properties.** Derived sheafification carries
the perfect objects of `D(R)` exactly onto the perfect objects of `D_QCoh(𝒪_{Spec R})`. -/
theorem perfectInQcoh_inverseImage :
    (perfectInQcoh R).inverseImage (derivedTilde R).asEquivalence.functor =
      (ObjectProperty.singleton ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj
        (ModuleCat.of R R))).triangEnvelope := by
  rw [← StacksDraft.Perfect.isPerfect_eq_triangEnvelope_singleton_regularModule]
  ext M
  change Stacks.Cohomology.PerfectComplexes.IsPerfect (((derivedTilde R).obj M).obj) ↔ _
  exact (isPerfect_iff_of_iso R ((derivedTildeCompι R).app M)).trans (isPerfect_tilde_iff M)

/-- **`D_perf(R) = D_perf(𝒪_{Spec R})`** ([Stacks, Tag 08EB], [Stacks, Tag 06Z0], as used in the
proof of [Stacks, Tag 0FDH]): derived sheafification restricts to an equivalence between the
perfect objects of `D(R)` and those of `D(𝒪_{Spec R})`. -/
def perfEquiv :
    (ObjectProperty.singleton ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj
      (ModuleCat.of R R))).triangEnvelope.FullSubcategory ≌ PerfectDerivedCategory (Spec R) :=
  (Equivalence.congrFullSubcategory (derivedTilde R).asEquivalence
    (perfectInQcoh_inverseImage R)).trans (perfectQcohEquiv R)

/-! ### The `K`-groups -/

/-- **[Stacks, Tag 0FDH], the clause `K₀(Spec R) = K₀(R)`.** For a commutative ring `R` the
Grothendieck group `K₀(Spec R) = K₀(D_perf(𝒪_{Spec R}))` of the affine scheme `Spec R` is
isomorphic to the Grothendieck group `K₀(R)` of finite projective `R`-modules, by the
isomorphism taking the class of a perfect object `K` of `D(𝒪_{Spec R})` which is isomorphic to
`M̃` to the alternating sum of the classes of the terms of a bounded complex of finite projective
`R`-modules representing `M`.

`perfEquiv` identifies `D_perf(R)` with `D_perf(𝒪_{Spec R})`,
`CategoryTheory.Pretriangulated.K0.mapEquiv` turns that into an isomorphism of `K`-groups, and
`K0.exists_k0_perfectDerivedCategory_addEquiv` ([Stacks, Tag 0FCU]) identifies `K₀(D_perf(R))`
with `K₀(R)` by the Euler characteristic, which is where the alternating sum comes from. -/
@[stacks 0FDH "affine_k0", sga "6 0 3.1" "special case", sga "6 VII 2.6" "special case"]
theorem exists_addEquiv_K0_perfectDerivedCategory_spec :
    ∃ e : Pretriangulated.K0 (PerfectDerivedCategory (Spec R)) ≃+ K0 (R : Type u),
      ∀ (K : PerfectDerivedCategory (Spec R)) (M : DerivedCategory (ModuleCat.{u} R))
        (Q : CochainComplex (ModuleCat.{u} (R : Type u)) ℤ) (a b : ℤ),
        Q.IsStrictlyGE a → Q.IsStrictlyLE b →
        (hfinite : ∀ i : ℤ, Module.Finite (R : Type u) (Q.X i)) →
        (hprojective : ∀ i : ℤ, Module.Projective (R : Type u) (Q.X i)) →
        Nonempty (M ≅ DerivedCategory.Q.obj Q) →
        Nonempty (K.obj ≅ (tilde.functor R).mapDerivedCategory.obj M) →
        e (Pretriangulated.K0.cls K) = ∑ i ∈ Finset.Icc a b,
          (i.negOnePow : ℤ) • K0.mk
            ({ carrier := Q.X i, finite := hfinite i, projective := hprojective i } :
              FGProj (R : Type u)) := by
  let Pperf : ObjectProperty (DerivedCategory (Spec R).Modules) :=
    fun K => Stacks.Cohomology.PerfectComplexes.IsPerfect (X := (Spec R).toRingedSpace) K
  have eF : (perfEquiv R).functor ⋙ Pperf.ι ≅
      (ObjectProperty.singleton ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj
        (ModuleCat.of R R))).triangEnvelope.ι ⋙ derivedTilde R ⋙
          (StandardModel.derivedQuasicoherent R).ι := Iso.refl _
  let : (perfEquiv R).functor.CommShift ℤ := Functor.CommShift.ofComp eF ℤ
  have : NatTrans.CommShift eF.hom ℤ := Functor.CommShift.ofComp_compatibility eF ℤ
  let : (perfEquiv R).functor.IsTriangulated :=
    (Functor.isTriangulated_iff_comp_right eF).2 inferInstance
  let : (perfEquiv R).inverse.CommShift ℤ := (perfEquiv R).commShiftInverse ℤ
  have : (perfEquiv R).CommShift ℤ := (perfEquiv R).commShift_of_functor ℤ
  have : (perfEquiv R).IsTriangulated := Equivalence.IsTriangulated.mk' _ inferInstance
  let : (perfEquiv R).inverse.IsTriangulated := inferInstance
  obtain ⟨e₀, he₀⟩ := K0.exists_k0_perfectDerivedCategory_addEquiv (R : Type u)
  refine ⟨(Pretriangulated.K0.mapEquiv (perfEquiv R)).symm.trans e₀, ?_⟩
  intro K M Q a b hge hle hfinite hprojective hMQ hKM
  obtain ⟨eKM⟩ := hKM
  have hM : (ObjectProperty.singleton ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj
      (ModuleCat.of R R))).triangEnvelope M := by
    rw [← perfectInQcoh_inverseImage R]
    exact (isPerfect_iff_of_iso R (eKM ≪≫ ((derivedTildeCompι R).app M).symm)).1 K.property
  set KP : (ObjectProperty.singleton ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj
      (ModuleCat.of R R))).triangEnvelope.FullSubcategory := ⟨M, hM⟩ with hKPdef
  have hcls : Pretriangulated.K0.mapEquiv (perfEquiv R) (Pretriangulated.K0.cls KP) =
      Pretriangulated.K0.cls K := by
    rw [Pretriangulated.K0.mapEquiv_cls]
    exact Pretriangulated.K0.cls_eq_of_iso
      (Pperf.isoMk (((derivedTildeCompι R).app M) ≪≫ eKM.symm))
  have hsymm : (Pretriangulated.K0.mapEquiv (perfEquiv R)).symm
      (Pretriangulated.K0.cls K) = Pretriangulated.K0.cls KP := by
    rw [← hcls, AddEquiv.symm_apply_apply]
  rw [AddEquiv.trans_apply, hsymm]
  exact he₀ KP Q a b hge hle hfinite hprojective hMQ

end Stacks.AlgebraicGeometry.GrothendieckGroupAffine

end
