module

public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import StacksFrontier.Homology.ExtendScalars.Flat
public import StacksFrontier.Homology.KFlat.Resolution
public import StacksFrontier.Homology.Perfect.BaseChange
public import StacksFrontier.Homology.Perfect.LargeUniverse
public import StacksFrontier.Homology.Perfect.NilpotentLifting
public import StacksFrontier.Homology.Tor.DerivedChangeOfRingsAdjunction

@[expose] public section

/-!
# Functoriality of derived reduction, and descent of perfectness

Derived extension of scalars is a left derived functor, so it is only functorial up to canonical
isomorphism: for `f : R →+* S` and `g : S →+* T` the composite of the two total derived
extension-of-scalars functors is isomorphic to the one attached to `g ∘ f`, but not equal to it.
This module constructs those comparison isomorphisms and uses them to move perfectness along
reductions modulo ideals.

Two consequences are recorded. First, perfectness of `K ⊗_R^L S` implies perfectness of `K`
whenever `f : R → S` is surjective with nilpotent kernel: factoring `f` through `R ⧸ ker f` turns
this into [stacks 07LU]. Second, for `I ≤ J` the reduction of `K` modulo `J` is the reduction
modulo `J ⧸ I` of the reduction modulo `I`, so perfectness modulo `J` is inherited by the iterated
reduction; the identification of `(R ⧸ I) ⧸ (J ⧸ I)` with `R ⧸ J` is
`DoubleQuot.quotQuotEquivQuotOfLE`.

## Main results

* `StacksDraft.Perfect.derivedRestrictScalarsComp`: derived restriction of scalars is
  functorial.
* `StacksDraft.Perfect.derivedExtensionScalarsComp`: the comparison isomorphism
  `(- ⊗_R^L S) ⊗_S^L T ≅ - ⊗_R^L T`.
* `StacksDraft.Perfect.derivedExtensionScalarsId`: derived extension of scalars along the
  identity is the identity.
* `StacksDraft.Perfect.exists_kFlat_representative`: every object of `D(R)` is represented by a
  K-flat complex with flat terms.
* `StacksDraft.Perfect.isPerfect_of_derivedExtensionScalars_ringEquiv`: perfectness descends
  along a ring isomorphism.
* `StacksDraft.Perfect.isPerfect_of_derivedExtensionScalars_surjective`: perfectness descends
  along a surjection with nilpotent kernel.
* `StacksDraft.Perfect.derivedReductionComp`: reduction modulo `J` factors through reduction
  modulo `I ≤ J`.
* `StacksDraft.Perfect.isPerfect_derivedReduction_map`: perfectness modulo `J` is inherited by
  the reduction of the reduction modulo `I ≤ J`.

## Implementation notes

The comparison isomorphisms are produced from uniqueness of left adjoints rather than from
uniqueness of left derived functors: derived extension of scalars along `f` is left adjoint to
derived restriction of scalars along `f` ([stacks 0GMT]), restriction of scalars *is* functorial
on the nose up to the canonical isomorphism `derivedRestrictScalarsComp`, and a composite of left
adjoints is left adjoint to the composite of the right adjoints. Two left adjoints of one functor
agree, whence the comparison.

The ring universes are tied together (`R`, `S`, `T` all in `Type u`) because the derived
extension-of-scalars datum `totalDerivedExtensionScalars.{u, u, v}` used throughout acts on
`R`-modules in the universe `max u v`, which must be the same universe on both sides of a
composition.

## References

* [The Stacks Project, Tag 064H](https://stacks.math.columbia.edu/tag/064H)
* [The Stacks Project, Tag 07LU](https://stacks.math.columbia.edu/tag/07LU)
* [The Stacks Project, Tag 0GMT](https://stacks.math.columbia.edu/tag/0GMT)
-/

universe u v

open CategoryTheory CategoryTheory.Limits
open CochainComplex.DerivedExtensionScalars

attribute [local instance] HasDerivedCategory.standard

namespace StacksDraft.Perfect

variable {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]

/-- Derived restriction of scalars is functorial: restricting along `g` and then along `f` is
restricting along `g ∘ f`. Restriction of scalars is exact, so this is the descent to derived
categories of the corresponding isomorphism of termwise functors. -/
noncomputable def derivedRestrictScalarsComp (f : R →+* S) (g : S →+* T) :
    (ModuleCat.restrictScalars.{max u v} g).mapDerivedCategory ⋙
      (ModuleCat.restrictScalars.{max u v} f).mapDerivedCategory ≅
        (ModuleCat.restrictScalars.{max u v} (g.comp f)).mapDerivedCategory := by
  let F := ModuleCat.restrictScalars.{max u v} g
  let G := ModuleCat.restrictScalars.{max u v} f
  let H := ModuleCat.restrictScalars.{max u v} (g.comp f)
  exact Localization.liftNatIso DerivedCategory.Q
    (HomologicalComplex.quasiIso (ModuleCat.{max u v} T) (ComplexShape.up ℤ))
    (DerivedCategory.Q ⋙ F.mapDerivedCategory ⋙ G.mapDerivedCategory)
    (DerivedCategory.Q ⋙ H.mapDerivedCategory)
    (F.mapDerivedCategory ⋙ G.mapDerivedCategory) H.mapDerivedCategory
    ((Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight F.mapDerivedCategoryFactors _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ G.mapDerivedCategoryFactors ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (Functor.mapHomologicalComplexCompIso
        (ModuleCat.restrictScalarsComp f g).symm (ComplexShape.up ℤ)) _ ≪≫
      H.mapDerivedCategoryFactors.symm)

/-- Derived extension of scalars is functorial up to canonical isomorphism: extending along `f`
and then along `g` agrees with extending along `g ∘ f`. Both are left adjoint to derived
restriction of scalars along `g ∘ f`, by [stacks 0GMT] and `derivedRestrictScalarsComp`. -/
noncomputable def derivedExtensionScalarsComp (f : R →+* S) (g : S →+* T) :
    (totalDerivedExtensionScalars.{u, u, v} f).functor ⋙
      (totalDerivedExtensionScalars.{u, u, v} g).functor ≅
        (totalDerivedExtensionScalars.{u, u, v} (g.comp f)).functor := by
  let Df := totalDerivedExtensionScalars.{u, u, v} f
  let Dg := totalDerivedExtensionScalars.{u, u, v} g
  let Dh := totalDerivedExtensionScalars.{u, u, v} (g.comp f)
  let af := @derivedExtensionScalarsAdjunction.{u, u, v}
    R S _ _ f _ _ Df.functor Df.comparison Df.isLeftDerived
  let ag := @derivedExtensionScalarsAdjunction.{u, u, v}
    S T _ _ g _ _ Dg.functor Dg.comparison Dg.isLeftDerived
  let ah := @derivedExtensionScalarsAdjunction.{u, u, v}
    R T _ _ (g.comp f) _ _ Dh.functor Dh.comparison Dh.isLeftDerived
  exact Adjunction.leftAdjointUniq
    ((af.comp ag).ofNatIsoRight (derivedRestrictScalarsComp f g)) ah

/-- `derivedExtensionScalarsComp` for a composite known only up to equality. -/
private noncomputable def derivedExtensionScalarsCompOfEq (f : R →+* S) (g : S →+* T)
    (h : R →+* T) (hfg : g.comp f = h) :
    (totalDerivedExtensionScalars.{u, u, v} f).functor ⋙
      (totalDerivedExtensionScalars.{u, u, v} g).functor ≅
        (totalDerivedExtensionScalars.{u, u, v} h).functor := by
  subst hfg
  exact derivedExtensionScalarsComp f g

/-- Every object of the derived category of `R`-modules is represented by a K-flat complex with
flat terms ([stacks 06Y4]). -/
theorem exists_kFlat_representative (K : DerivedCategory (ModuleCat.{max u v} R)) :
    ∃ P : CochainComplex (ModuleCat.{max u v} R) ℤ,
      P.KFlat ∧ (∀ i, Module.Flat R (P.X i)) ∧ Nonempty (K ≅ DerivedCategory.Q.obj P) := by
  obtain ⟨P, p, hP, hflat, hp, -⟩ :=
    CochainComplex.KFlat.exists_kFlat_resolution (DerivedCategory.Q.objPreimage K)
  have : IsIso (DerivedCategory.Q.map p) := by rwa [DerivedCategory.isIso_Q_map_iff_quasiIso]
  exact ⟨P, hP, hflat, ⟨(DerivedCategory.Q.objObjPreimageIso K).symm ≪≫
    (asIso (DerivedCategory.Q.map p)).symm⟩⟩

/-- Derived extension of scalars along the identity of `R` is the identity: it is computed on a
K-flat representative by termwise extension of scalars along the identity. -/
noncomputable def derivedExtensionScalarsId (K : DerivedCategory (ModuleCat.{max u v} R)) :
    (totalDerivedExtensionScalars.{u, u, v} (RingHom.id R)).functor.obj K ≅ K := by
  apply Classical.choice
  obtain ⟨P, hP, -, ⟨e⟩⟩ := exists_kFlat_representative K
  let D := totalDerivedExtensionScalars.{u, u, v} (RingHom.id R)
  have : IsIso (D.comparison.app P) := D.comparison_isIso_of_kFlat P hP
  exact ⟨D.functor.mapIso e ≪≫ asIso (D.comparison.app P) ≪≫
    DerivedCategory.Q.mapIso
      ((NatIso.mapHomologicalComplex (ModuleCat.extendScalarsId.{u, max u v} R)
        (ComplexShape.up ℤ)).app P ≪≫
        (Functor.mapHomologicalComplexIdIso (ModuleCat.{max u v} R)
          (ComplexShape.up ℤ)).app P) ≪≫ e.symm⟩

/-- Perfectness descends along a ring isomorphism: if `K ⊗_R^L S` is perfect for an isomorphism
`R ≃+* S`, then `K` is perfect, since extending along the inverse returns `K`. -/
theorem isPerfect_of_derivedExtensionScalars_ringEquiv (e : R ≃+* S)
    (K : DerivedCategory (ModuleCat.{max u v} R))
    (hK : IsPerfect ((totalDerivedExtensionScalars.{u, u, v} e.toRingHom).functor.obj K)) :
    IsPerfect K := by
  have ec := (derivedExtensionScalarsCompOfEq.{u, v} e.toRingHom e.symm.toRingHom (RingHom.id R)
    (by ext x; simp)).app K
  exact isPerfect_of_iso (ec ≪≫ derivedExtensionScalarsId K).symm
    (isPerfect_derivedExtensionScalars.{u, u, v} e.symm.toRingHom _ hK)

/-- Perfectness descends along a surjection with nilpotent kernel: factor `f` as the quotient by
`ker f` followed by the isomorphism `R ⧸ ker f ≃+* S`, and apply [stacks 07LU]. -/
theorem isPerfect_of_derivedExtensionScalars_surjective (f : R →+* S) (hf : Function.Surjective f)
    (hn : IsNilpotent (RingHom.ker f)) (K : DerivedCategory (ModuleCat.{max u v} R))
    (hK : IsPerfect ((totalDerivedExtensionScalars.{u, u, v} f).functor.obj K)) :
    IsPerfect K := by
  apply isPerfect_of_isPerfect_mod_isNilpotent (RingHom.ker f) K _ hn
  apply isPerfect_of_derivedExtensionScalars_ringEquiv (RingHom.quotientKerEquivOfSurjective hf)
  have ec := (derivedExtensionScalarsCompOfEq.{u, v} (Ideal.Quotient.mk (RingHom.ker f))
    (RingHom.quotientKerEquivOfSurjective hf).toRingHom f (by ext x; rfl)).app K
  exact isPerfect_of_iso ec hK

/-- For `I ≤ J`, reduction modulo `J` is reduction modulo `J ⧸ I` after reduction modulo `I`. -/
noncomputable def derivedReductionComp (I J : Ideal R) (hIJ : I ≤ J) :
    (totalDerivedExtensionScalars.{u, u, v} (Ideal.Quotient.mk I)).functor ⋙
      (totalDerivedExtensionScalars.{u, u, v} (Ideal.Quotient.factor hIJ)).functor ≅
      (totalDerivedExtensionScalars.{u, u, v} (Ideal.Quotient.mk J)).functor := by
  have h : (Ideal.Quotient.factor hIJ).comp (Ideal.Quotient.mk I) = Ideal.Quotient.mk J := by
    ext x
    rfl
  have ec := derivedExtensionScalarsComp.{u, v}
    (Ideal.Quotient.mk I) (Ideal.Quotient.factor hIJ)
  rw [h] at ec
  exact ec

/-- If the reduction of `K` modulo `J` is perfect and `I ≤ J`, then the reduction modulo
`J ⧸ I` of the reduction of `K` modulo `I` is perfect. The two agree, `(R ⧸ I) ⧸ (J ⧸ I)` being
`R ⧸ J`. -/
theorem isPerfect_derivedReduction_map (I J : Ideal R) (hIJ : I ≤ J)
    (K : DerivedCategory (ModuleCat.{max u v} R))
    (hK : IsPerfect
      ((totalDerivedExtensionScalars.{u, u, v} (Ideal.Quotient.mk J)).functor.obj K)) :
    IsPerfect ((totalDerivedExtensionScalars.{u, u, v}
      (Ideal.Quotient.mk (J.map (Ideal.Quotient.mk I)))).functor.obj
        ((totalDerivedExtensionScalars.{u, u, v} (Ideal.Quotient.mk I)).functor.obj K)) := by
  let e := DoubleQuot.quotQuotEquivQuotOfLE hIJ
  apply isPerfect_of_derivedExtensionScalars_ringEquiv e
  have ec := (derivedExtensionScalarsCompOfEq.{u, v}
    (Ideal.Quotient.mk (J.map (Ideal.Quotient.mk I))) e.toRingHom (Ideal.Quotient.factor hIJ)
    (by ext x; exact DoubleQuot.quotQuotEquivQuotOfLE_quotQuotMk x hIJ)).app
      ((totalDerivedExtensionScalars.{u, u, v} (Ideal.Quotient.mk I)).functor.obj K)
  exact isPerfect_of_iso (ec ≪≫ (derivedReductionComp I J hIJ).app K) hK

end StacksDraft.Perfect

end
