module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.Etale.IndEtaleFibres
public import StacksFrontier.RingTheory.FormallySmooth.SpecialFibre
public import StacksFrontier.RingTheory.GeometricallyRegular.FormalSmoothness
public import StacksFrontier.RingTheory.GRing.Henselization

@[expose] public section

/-!
# Formal smoothness and regular ring maps

A formally smooth algebra over a field is geometrically regular, so a flat formally smooth map
of Noetherian rings is a regular ring map. For a Noetherian local ring this makes formal
smoothness of the completion map a criterion for being a G-ring.
-/

open IsLocalRing
open scoped TensorProduct

universe u

section

variable (k : Type u) (C : Type u) [Field k] [CommRing C] [Algebra k C]

/-- A Noetherian local algebra over a field which is formally smooth is a regular local ring. -/
@[ega "0 19.6.4" "a ⇒ c, special case"]
private theorem isRegularLocalRing_of_formallySmooth_field
    [IsNoetherianRing C] [IsLocalRing C] [Algebra.FormallySmooth k C] :
    IsRegularLocalRing C := by
  let : TopologicalSpace k := ⊥
  let : DiscreteTopology k := ⟨rfl⟩
  let : TopologicalSpace C := (maximalIdeal C).adicTopology
  let : IsTopologicalRing C := (maximalIdeal C).ringFilterBasis.isTopologicalRing
  let : IsLinearTopology C C := (maximalIdeal C).isLinearTopology
  have hfs : IsFormallySmooth.{u} (algebraMap k C) :=
    (isFormallySmooth_iff_formallySmoothNAdic (algebraMap k C) (maximalIdeal C) (by rfl)).mpr
      ((RingHom.formallySmoothNAdic_bot_iff.mpr ‹Algebra.FormallySmooth k C›).mono bot_le)
  obtain hk | ⟨p, hp, hkp⟩ := CharP.exists' k
  · let : CharZero k := hk
    exact ((formalSmoothness_maximalIdeal_characterizations k C).1).mpr hfs
  · let := hp
    let := hkp
    have hgr : Algebra.IsGeometricallyRegular k C :=
      (((formalSmoothness_maximalIdeal_characterizations k C).2 p).out 1 2).mpr hfs
    have : IsRegularRing (k ⊗[k] C) := hgr.isRegularRing_tensorProduct k
    have : IsRegularRing C :=
      IsRegularRing.of_ringEquiv (Algebra.TensorProduct.lid k C).toRingEquiv
    exact IsRegularLocalRing.of_isRegularRing_of_isLocalRing C

/-- A Noetherian algebra over a field which is formally smooth is a regular ring. -/
public theorem isRegularRing_of_formallySmooth_field
    [IsNoetherianRing C] [Algebra.FormallySmooth k C] : IsRegularRing C := by
  rw [isRegularRing_iff]
  intro q hq
  let L := Localization.AtPrime q
  let : Algebra.FormallyEtale C L := Algebra.FormallyEtale.of_isLocalization q.primeCompl
  let : Algebra.FormallySmooth k L := Algebra.FormallySmooth.comp k C L
  have : IsNoetherianRing L := IsLocalization.isNoetherianRing q.primeCompl L inferInstance
  exact isRegularLocalRing_of_formallySmooth_field k L

/-- A Noetherian algebra over a field which is formally smooth is geometrically regular: its
base change along any finite purely inseparable extension is again formally smooth. -/
@[ega "0 19.6.5" "special case", ega "0 19.6.6" "(a) ⇒ (c)", ega "0 22.5.8" "a) ⇒ b), special case"]
public theorem isGeometricallyRegular_of_formallySmooth_field
    [IsNoetherianRing C] [Algebra.FormallySmooth k C] : Algebra.IsGeometricallyRegular k C := by
  refine ⟨(Algebra.forall_isRegularRing_tensorProduct_essFiniteType_iff_finite_isPurelyInseparable
    k C).mpr ?_⟩
  intro K _ _ _ _
  have : IsNoetherianRing (C ⊗[k] K) := IsNoetherianRing.of_finite C (C ⊗[k] K)
  have : IsNoetherianRing (K ⊗[k] C) :=
    isNoetherianRing_of_ringEquiv _ (Algebra.TensorProduct.comm k C K).toRingEquiv
  exact isRegularRing_of_formallySmooth_field K (K ⊗[k] C)

end

section

variable (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]

/-- A flat formally smooth map of Noetherian rings is a regular ring map: each of its
residue-field fibres is formally smooth over that residue field, hence geometrically regular. -/
@[ega "IV 17.5.2" "special case"]
public theorem isRegularRingHom_of_formallySmooth_of_flat
    [IsNoetherianRing A] [IsNoetherianRing B] [Algebra.FormallySmooth A B] [Module.Flat A B] :
    IsRegularRingHom (algebraMap A B) := by
  rw [isRegularRingHom_algebraMap_iff]
  refine ⟨RingHom.flat_algebraMap_iff.mpr inferInstance, fun q hq => ?_⟩
  have hN : IsNoetherianRing (q.Fiber B) := q.isNoetherianRing_fiber B
  exact ⟨hN, isGeometricallyRegular_of_formallySmooth_field q.ResidueField (q.Fiber B)⟩

end

section

variable (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]

/-- A Noetherian local ring whose completion map is formally smooth is a G-ring. -/
public theorem isGRing_of_formallySmooth_adicCompletion
    [Algebra.FormallySmooth A (AdicCompletion (maximalIdeal A) A)] : IsGRing A := by
  refine (isGRing_iff_isRegularRingHom_adicCompletion_at_maximal A).mpr fun m hm => ?_
  obtain rfl := IsLocalRing.eq_maximalIdeal hm
  let e : Localization.AtPrime (maximalIdeal A) ≃ₐ[A] A :=
    (IsLocalization.atUnits A (maximalIdeal A).primeCompl (fun _ hx => not_not.mp hx)).symm
  exact Stacks.RegularRingHom.isRegularRingHom_of_ringEquiv e.symm.toRingEquiv
    (Stacks.FormalFibres.completionRingEquiv e.symm.toRingEquiv)
    (Stacks.FormalFibres.completionRingEquiv_algebraMap e.symm.toRingEquiv)
    (isRegularRingHom_of_formallySmooth_of_flat A (AdicCompletion (maximalIdeal A) A))

end

end
