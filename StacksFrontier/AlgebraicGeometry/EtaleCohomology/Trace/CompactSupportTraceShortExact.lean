module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CurveTraceDevissage
public import StacksFrontier.Homology.Injectives.FilteredComplex.InverseSystemRepresentation

/-!
# Vanishing of the trace on `RΓ_c` along short exact sequences

Let `j : X ⟶ X̄` be a compactification of a scheme `X` over a finite field `k`. The condition
`Stacks.EtaleCohomology.CompactSupportTraceVanishes` on a bounded below complex `K` on `X_étale`
— `RΓ_c(X_k̄, K)` is perfect and `Tr(π_X^* | RΓ_c(X_k̄, K)) = 0` — is two out of three along a
short exact sequence of complexes, in all three directions, and holds for acyclic complexes.

Additivity of the trace along a short exact sequence is
`Stacks.EtaleCohomology.canonicalCompactSupportLefschetzNumber_X₂_eq_add`; perfectness is two out
of three because the image of the sequence under `RΓ_c` is a distinguished triangle
(`CategoryTheory.Functor.twistTriangle_distinguished`, [Stacks, Tag 066R]). An acyclic complex is
zero in the derived category, and right derived functors preserve zero objects.

The standard model `HasDerivedCategory.standard` of the derived categories is used because the
consumed trace and Frobenius objects (`perfectDerivedTrace`, `canonicalCompactSupportFrobenius`)
are defined there.

## Main results

* `CategoryTheory.Functor.isZero_rightDerivedFunctorPlus_obj`: right derived functors preserve
  zero objects.
* `Stacks.EtaleCohomology.CompactSupportTraceVanishes.of_acyclic`
* `Stacks.EtaleCohomology.CompactSupportTraceVanishes.of_shortExact₁`,
  `Stacks.EtaleCohomology.CompactSupportTraceVanishes.of_shortExact₂`,
  `Stacks.EtaleCohomology.CompactSupportTraceVanishes.of_shortExact₃`
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme Stacks.Frobenius CategoryTheory.FilteredDerived

universe u

namespace CategoryTheory.Functor

/-- **Right derived functors preserve zero objects**: the zero complex consists of injectives, so
the derived functor is computed on it by applying the functor termwise. -/
theorem isZero_rightDerivedFunctorPlus_obj {C D : Type*} [Category* C] [Category* D] [Abelian C]
    [Abelian D] [HasDerivedCategory C] [HasDerivedCategory D] (F : C ⥤ D) [F.Additive]
    [EnoughInjectives C] {X : DerivedCategory.Plus C} (hX : IsZero X) :
    IsZero (F.rightDerivedFunctorPlus.obj X) := by
  let Z : CochainComplex C ℤ := HomologicalComplex.zero
  have hZ : IsZero Z := HomologicalComplex.isZero_zero
  have hZX (n : ℤ) : IsZero (Z.X n) := Functor.map_isZero (HomologicalComplex.eval _ _ n) hZ
  have hZp : CochainComplex.plus C Z := ⟨0, by
    rw [CochainComplex.isStrictlyGE_iff]
    exact fun i _ => hZX i⟩
  let L : HomotopyCategory.Plus C := (HomotopyCategory.Plus.quotient C).obj ⟨Z, hZp⟩
  have hL : ∀ n : ℤ, Injective (L.obj.as.X n) := fun n => (hZX n).injective
  have hQL : IsZero (DerivedCategory.Plus.Qh.obj L) := Functor.map_isZero _
    (Functor.map_isZero _ (IsZero.of_full_of_faithful_of_isZero (ObjectProperty.ι _) _ hZ))
  have hFL : IsZero ((F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).obj L) := by
    refine Functor.map_isZero DerivedCategory.Plus.Qh ?_
    show IsZero ((HomotopyCategory.Plus.quotient D).obj (F.mapCochainComplexPlus.obj ⟨Z, hZp⟩))
    refine Functor.map_isZero _ (IsZero.of_full_of_faithful_of_isZero (ObjectProperty.ι _) _ ?_)
    rw [IsZero.iff_id_eq_zero]
    ext n : 1
    exact (Functor.map_isZero F (hZX n)).eq_of_src _ _
  exact (hFL.of_iso (asIso (F.rightDerivedFunctorPlusUnith.app L)).symm).of_iso
    (F.rightDerivedFunctorPlus.mapIso (hX.iso hQL))

end CategoryTheory.Functor

namespace Stacks.EtaleCohomology

section Standard

attribute [local instance] HasDerivedCategory.standard

variable {Λ : Type} [Ring Λ] [Finite Λ] {k : Type u} [Field k] [Fintype k] {kbar : Type u}
  [Field kbar] [Algebra k kbar] {p q : ℕ} [Fact p.Prime] [CharP k p]
  {hcard : Fintype.card k = p ^ q} {X : Scheme.{u}} {f : X ⟶ Spec (.of k)}
  {J : CompactificationOf (Over.mk f)}

omit [Finite Λ] [Fintype k] in
/-- **`RΓ_c` of an acyclic complex vanishes.** -/
theorem isZero_compactSupportFrobeniusCohomology_of_acyclic
    (K : CochainComplex.Plus (EtaleModules.{u, 0} Λ X)) (hK : K.obj.Acyclic) :
    IsZero (DerivedCategory.Plus.ι.obj
      (compactSupportFrobeniusCohomology.{u, 0} Λ f J kbar K)) := by
  have := etaleModuleInverseImage_preservesFiniteLimits.{u, 0} Λ
    (fieldBaseChangeProj (Over.mk J.toBase) kbar)
  have := etaleModuleInverseImage_preservesFiniteColimits.{u, 0} Λ
    (fieldBaseChangeProj (Over.mk J.toBase) kbar)
  have : PreservesFiniteColimits (etaleModuleExtensionByZero.{u, 0} Λ J.immersion) :=
    let : (etaleModuleExtensionByZero.{u, 0} Λ J.immersion).IsLeftAdjoint :=
      (etaleModuleExtensionByZeroAdj.{u, 0} Λ J.immersion).isLeftAdjoint
    inferInstance
  let M := (etaleModuleInverseImage.{u, 0} Λ
    (fieldBaseChangeProj (Over.mk J.toBase) kbar)).mapCochainComplexPlus.obj
      ((etaleModuleExtensionByZero.{u, 0} Λ J.immersion).mapCochainComplexPlus.obj K)
  have hQM : IsZero (DerivedCategory.Plus.Q.obj M) :=
    IsZero.of_full_of_faithful_of_isZero DerivedCategory.Plus.ι _
      (Stacks.Injectives.isZero_Q_obj_of_acyclic M.obj ((hK.map _).map _))
  have := etaleModules_enoughInjectives.{u, 0} Λ
    (pullback (Over.mk J.toBase).hom (specAlgebraMap k kbar))
  have := etaleModules_enoughInjectives.{u, 0} Λ (Spec (.of kbar))
  exact Functor.map_isZero _ (Functor.isZero_rightDerivedFunctorPlus_obj _
    (Functor.isZero_rightDerivedFunctorPlus_obj _ hQM))

omit [Finite Λ] in
/-- **The trace vanishes on `RΓ_c` of an acyclic complex.** -/
theorem CompactSupportTraceVanishes.of_acyclic
    (K : CochainComplex.Plus (EtaleModules.{u, 0} Λ X)) (hK : K.obj.Acyclic) :
    CompactSupportTraceVanishes Λ kbar p q hcard f J K := by
  have h := isZero_compactSupportFrobeniusCohomology_of_acyclic (f := f) (J := J) (kbar := kbar)
    K hK
  exact ⟨StacksDraft.Perfect.isPerfect_of_isZero _ h, perfectDerivedTrace_eq_zero_of_isZero Λ _ h _⟩

variable {S : ShortComplex (CochainComplex (EtaleModules.{u, 0} Λ X) ℤ)} (hS : S.ShortExact)
  (h₁ : CochainComplex.plus _ S.X₁) (h₂ : CochainComplex.plus _ S.X₂)
  (h₃ : CochainComplex.plus _ S.X₃)

omit [Finite Λ] in
include hS hcard in
/-- **Perfectness of `RΓ_c` along a short exact sequence, in all directions**: the image of the
sequence is a distinguished triangle in `D(Λ)`. -/
theorem isPerfect_compactSupportFrobeniusCohomology_triangle :
    (StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj
        (compactSupportFrobeniusCohomology.{u, 0} Λ f J kbar ⟨S.X₁, h₁⟩)) →
      StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj
        (compactSupportFrobeniusCohomology.{u, 0} Λ f J kbar ⟨S.X₂, h₂⟩)) →
      StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj
        (compactSupportFrobeniusCohomology.{u, 0} Λ f J kbar ⟨S.X₃, h₃⟩))) ∧
    (StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj
        (compactSupportFrobeniusCohomology.{u, 0} Λ f J kbar ⟨S.X₂, h₂⟩)) →
      StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj
        (compactSupportFrobeniusCohomology.{u, 0} Λ f J kbar ⟨S.X₃, h₃⟩)) →
      StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj
        (compactSupportFrobeniusCohomology.{u, 0} Λ f J kbar ⟨S.X₁, h₁⟩))) := by
  have := etaleModules_enoughInjectives.{u, 0} Λ (fieldBaseChange (Over.mk J.toBase) kbar)
  have := etaleModules_enoughInjectives.{u, 0} Λ
    (pullback (Over.mk J.toBase).hom (specAlgebraMap k kbar))
  have := etaleModules_enoughInjectives.{u, 0} Λ (Spec (.of kbar))
  have hS' := compactSupportShortComplex_shortExact.{u, 0} Λ f J kbar hS
  have hplus (K : CochainComplex.Plus (EtaleModules.{u, 0} Λ X)) :=
    ((etaleModuleInverseImage.{u, 0} Λ
    (fieldBaseChangeProj (Over.mk J.toBase) kbar)).mapCochainComplexPlus.obj
      ((etaleModuleExtensionByZero.{u, 0} Λ J.immersion).mapCochainComplexPlus.obj K)).property
  have h₁' := hplus ⟨S.X₁, h₁⟩
  have h₂' := hplus ⟨S.X₂, h₂⟩
  have h₃' := hplus ⟨S.X₃, h₃⟩
  obtain ⟨Rs⟩ := Functor.TwistResolution.nonempty
    (etaleModuleDirectImage.{u, 0} Λ
      (geometricFrobeniusBaseChange (Over.mk J.toBase) kbar p q hcard))
    hS' h₁' h₃' (compactSupportShortComplexTwist.{u, 0} Λ f J kbar p q hcard S)
  have hT := Functor.twistTriangle_distinguished.{0, u + 1}
    (etaleModuleDirectImage.{u, 0} Λ (pullback.snd (Over.mk J.toBase).hom (specAlgebraMap k kbar)))
    (etaleModuleGlobalSections.{u, 0} Λ (Spec (.of kbar))) h₁' h₂' h₃' Rs
  have h := StacksDraft.Perfect.isPerfect_of_distinguished _ hT
  exact ⟨h.1, h.2.2⟩

/-- Additivity of the trace of the canonical Frobenius on `RΓ_c` along a short exact sequence. -/
private theorem trace_X₂_eq_add
    (hS : S.ShortExact) (h₁ : CochainComplex.plus _ S.X₁) (h₂ : CochainComplex.plus _ S.X₂)
    (h₃ : CochainComplex.plus _ S.X₃)
    (hp₁ : StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj
      (compactSupportFrobeniusCohomology.{u, 0} Λ f J kbar ⟨S.X₁, h₁⟩)))
    (hp₂ : StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj
      (compactSupportFrobeniusCohomology.{u, 0} Λ f J kbar ⟨S.X₂, h₂⟩)))
    (hp₃ : StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj
      (compactSupportFrobeniusCohomology.{u, 0} Λ f J kbar ⟨S.X₃, h₃⟩))) :
    perfectDerivedTrace Λ ⟨_, hp₂⟩ (DerivedCategory.Plus.ι.map
      (canonicalCompactSupportFrobenius.{u, 0} Λ f J kbar p q hcard ⟨S.X₂, h₂⟩)) =
    perfectDerivedTrace Λ ⟨_, hp₁⟩ (DerivedCategory.Plus.ι.map
      (canonicalCompactSupportFrobenius.{u, 0} Λ f J kbar p q hcard ⟨S.X₁, h₁⟩)) +
    perfectDerivedTrace Λ ⟨_, hp₃⟩ (DerivedCategory.Plus.ι.map
      (canonicalCompactSupportFrobenius.{u, 0} Λ f J kbar p q hcard ⟨S.X₃, h₃⟩)) := by
  have := canonicalCompactSupportLefschetzNumber_X₂_eq_add Λ f J kbar p q hcard hS h₁ h₂ h₃
    hp₁ hp₂ hp₃
  simpa only [canonicalCompactSupportLefschetzNumber, globalLefschetzNumber,
    canonicalFrobeniusActionOnCompactSupport] using this

include hS in
/-- The vanishing of the trace for the middle term from the outer two. -/
theorem CompactSupportTraceVanishes.of_shortExact₂
    (hv₁ : CompactSupportTraceVanishes Λ kbar p q hcard f J ⟨S.X₁, h₁⟩)
    (hv₃ : CompactSupportTraceVanishes Λ kbar p q hcard f J ⟨S.X₃, h₃⟩) :
    CompactSupportTraceVanishes Λ kbar p q hcard f J ⟨S.X₂, h₂⟩ := by
  obtain ⟨hp₁, ht₁⟩ := hv₁
  obtain ⟨hp₃, ht₃⟩ := hv₃
  have hp₂ := isPerfect_compactSupportFrobeniusCohomology_X₂ Λ f J kbar hS h₁ h₂ h₃ hp₁ hp₃
  refine ⟨hp₂, ?_⟩
  have := trace_X₂_eq_add (hcard := hcard) hS h₁ h₂ h₃ hp₁ hp₂ hp₃
  exact this.trans ((congrArg₂ (· + ·) ht₁ ht₃).trans (add_zero 0))

include hS in
/-- The vanishing of the trace for the subobject from the other two terms. -/
theorem CompactSupportTraceVanishes.of_shortExact₁
    (hv₂ : CompactSupportTraceVanishes Λ kbar p q hcard f J ⟨S.X₂, h₂⟩)
    (hv₃ : CompactSupportTraceVanishes Λ kbar p q hcard f J ⟨S.X₃, h₃⟩) :
    CompactSupportTraceVanishes Λ kbar p q hcard f J ⟨S.X₁, h₁⟩ := by
  obtain ⟨hp₂, ht₂⟩ := hv₂
  obtain ⟨hp₃, ht₃⟩ := hv₃
  have hp₁ := (isPerfect_compactSupportFrobeniusCohomology_triangle (hcard := hcard) hS h₁ h₂ h₃).2
    hp₂ hp₃
  refine ⟨hp₁, ?_⟩
  have := trace_X₂_eq_add (hcard := hcard) hS h₁ h₂ h₃ hp₁ hp₂ hp₃
  rw [ht₃, add_zero] at this
  exact (ht₂.symm.trans this).symm

include hS in
/-- The vanishing of the trace for the quotient from the other two terms. -/
theorem CompactSupportTraceVanishes.of_shortExact₃
    (hv₁ : CompactSupportTraceVanishes Λ kbar p q hcard f J ⟨S.X₁, h₁⟩)
    (hv₂ : CompactSupportTraceVanishes Λ kbar p q hcard f J ⟨S.X₂, h₂⟩) :
    CompactSupportTraceVanishes Λ kbar p q hcard f J ⟨S.X₃, h₃⟩ := by
  obtain ⟨hp₁, ht₁⟩ := hv₁
  obtain ⟨hp₂, ht₂⟩ := hv₂
  have hp₃ := (isPerfect_compactSupportFrobeniusCohomology_triangle (hcard := hcard) hS h₁ h₂ h₃).1
    hp₁ hp₂
  refine ⟨hp₃, ?_⟩
  have := trace_X₂_eq_add (hcard := hcard) hS h₁ h₂ h₃ hp₁ hp₂ hp₃
  rw [ht₁, zero_add] at this
  exact (ht₂.symm.trans this).symm

end Standard

end Stacks.EtaleCohomology

end
