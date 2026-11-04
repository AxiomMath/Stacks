module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Topology.Connected.TotallyDisconnected
public import StacksFrontier.AlgebraicGeometry.ProperGeomConnected.Local
public import StacksFrontier.AlgebraicGeometry.ProperGeomConnected.Sections
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The fibres of `X ⟶ Spec Γ(X, ⊤)` for `X` proper over a field

Let `k` be a field and let `X` be a scheme proper over `k`. The canonical morphism
`X.toSpecΓ : X ⟶ Spec Γ(X, ⊤)` is surjective and each of its fibres is connected.

## Main results

In the namespace `Stacks.AlgebraicGeometry.ProperGeomConnected`:

* `isConnected_preimage_singleton_toSpecΓ_of_integral`: for `X` a Noetherian space with
  `Γ(X, ⊤)` integral over a field, every fibre of `X.toSpecΓ` is connected.
* `isConnected_preimage_singleton_toSpecΓ`: for `X` proper over a field, every fibre of
  `X.toSpecΓ` is connected (in particular nonempty).
* `connectedSpace_fiber_toSpecΓ`: the same statement for the scheme-theoretic fibre.
* `surjective_toSpecΓ`: `X.toSpecΓ` is surjective.
* `geometricallyConnected_toSpecΓ_iff_isIdempotentElem`: `X.toSpecΓ` has geometrically connected
  fibres if and only if the ring of global sections of each of its base changes to a field is
  nontrivial with no idempotents other than `0` and `1`.

## References

* [Stacks Project, Tag 0FD1](https://stacks.math.columbia.edu/tag/0FD1)
* [Stacks Project, Tag 0BUG](https://stacks.math.columbia.edu/tag/0BUG)
* [Stacks Project, Tag 01I1](https://stacks.math.columbia.edu/tag/01I1)
* [Stacks Project, Tag 02KH](https://stacks.math.columbia.edu/tag/02KH)
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry

universe u

namespace Stacks.AlgebraicGeometry.ProperGeomConnected

section Topology

variable {α : Type*} [TopologicalSpace α]

/-- A space with finitely many connected components has open connected components. -/
theorem isOpen_connectedComponent_of_finite [Finite (ConnectedComponents α)] (x : α) :
    IsOpen (connectedComponent x) := by
  rw [← isClosed_compl_iff, ← connectedComponents_preimage_singleton, ← Set.preimage_compl]
  have h : (({ConnectedComponents.mk x}ᶜ : Set (ConnectedComponents α))) =
      ⋃ c ∈ ({ConnectedComponents.mk x}ᶜ : Set (ConnectedComponents α)), {c} :=
    (Set.biUnion_of_singleton _).symm
  rw [h, Set.preimage_iUnion₂]
  refine Set.Finite.isClosed_biUnion (Set.toFinite _) fun c _ ↦ ?_
  obtain ⟨y, rfl⟩ := ConnectedComponents.surjective_coe c
  rw [connectedComponents_preimage_singleton]
  exact isClosed_connectedComponent

/-- A Noetherian space has finitely many connected components. -/
theorem finite_connectedComponents_of_noetherianSpace [NoetherianSpace α] :
    Finite (ConnectedComponents α) := by
  have hfin : (irreducibleComponents α).Finite := NoetherianSpace.finite_irreducibleComponents
  have := hfin.to_subtype
  refine Finite.of_surjective
    (fun t : irreducibleComponents α ↦ ConnectedComponents.mk t.2.1.1.some) fun c ↦ ?_
  obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
  refine ⟨⟨irreducibleComponent x, irreducibleComponent_mem_irreducibleComponents x⟩, ?_⟩
  refine ConnectedComponents.coe_eq_coe'.mpr ?_
  exact isIrreducible_irreducibleComponent.2.isPreconnected.subset_connectedComponent
    mem_irreducibleComponent (Set.Nonempty.some_mem _)

end Topology

variable {k : Type u} [Field k] {X : Scheme.{u}}

/-- If `X` is a Noetherian scheme whose ring of global sections is integral over a field, then
every fibre of `X.toSpecΓ` is connected. -/
theorem isConnected_preimage_singleton_toSpecΓ_of_integral [NoetherianSpace X]
    (φ : k →+* Γ(X, ⊤)) (hφ : φ.IsIntegral) (s : Spec Γ(X, ⊤)) :
    _root_.IsConnected (X.toSpecΓ ⁻¹' {s}) := by
  classical
  have hfin : Finite (ConnectedComponents X) := finite_connectedComponents_of_noetherianSpace
  have hdisc : DiscreteTopology (ConnectedComponents X) :=
    ConnectedComponents.discreteTopology_iff.mpr isOpen_connectedComponent_of_finite
  let U : ConnectedComponents X → X.Opens := fun c ↦
    ⟨ConnectedComponents.mk ⁻¹' {c},
      (isOpen_discrete _).preimage ConnectedComponents.continuous_coe⟩
  have hUeq : ∀ x : X, (U (ConnectedComponents.mk x) : Set X) = connectedComponent x := fun x ↦
    connectedComponents_preimage_singleton
  have hcover : (⊤ : X.Opens) ≤ ⨆ c, U c := fun x _ ↦
    TopologicalSpace.Opens.mem_iSup.mpr ⟨ConnectedComponents.mk x, rfl⟩
  have hdisj : ∀ c d, c ≠ d → U c ⊓ U d = ⊥ := fun c d hcd ↦
    TopologicalSpace.Opens.ext (Set.eq_empty_iff_forall_notMem.mpr fun x hx ↦
      hcd (hx.1.symm.trans hx.2))
  have hne : ∀ c, Nonempty (U c) := by
    intro c
    obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
    exact ⟨⟨x, rfl⟩⟩
  let ρ : ∀ c, Γ(X, ⊤) →+* Γ(X, U c) := fun c ↦
    (X.presheaf.map (homOfLE (le_top : U c ≤ ⊤)).op).hom
  let E : Γ(X, ⊤) ≃+* (∀ c, Γ(X, U c)) :=
    RingEquiv.ofBijective _ (bijective_piRestrict U hcover hdisj)
  have hEapp : ∀ (x : Γ(X, ⊤)) (c), E x c = ρ c x := fun _ _ ↦ rfl
  have hρsurj : ∀ c, Function.Surjective (ρ c) := by
    intro c a
    refine ⟨E.symm (Function.update (fun d ↦ (0 : Γ(X, U d))) c a), ?_⟩
    rw [← hEapp, E.apply_symm_apply, Function.update_self]
  have hunique : ∀ c, Unique (PrimeSpectrum (Γ(X, U c) : Type u)) := by
    intro c
    have := hne c
    have hnt : Nontrivial Γ(X, U c) := Scheme.component_nontrivial X (U c)
    have hsub : Subsingleton (PrimeSpectrum (Γ(X, U c) : Type u)) := by
      refine Stacks.RingTheory.IntegralOverField.subsingleton_primeSpectrum_of_isIntegral
        ((ρ c).comp φ) (RingHom.IsIntegral.trans φ (ρ c) hφ
          (RingHom.isIntegral_of_surjective (ρ c) (hρsurj c))) ?_
      intro e he
      obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
      refine isIdempotentElem_eq_zero_or_one ?_ he
      rw [hUeq x]
      exact isPreconnected_connectedComponent
    exact ⟨⟨Classical.arbitrary _⟩, fun _ ↦ Subsingleton.elim _ _⟩
  have := hunique
  let e : ConnectedComponents X ≃ PrimeSpectrum (Γ(X, ⊤) : Type u) :=
    (Equiv.sigmaUnique _ _).symm.trans
      ((PrimeSpectrum.sigmaToPiHomeo fun c ↦ (Γ(X, U c) : Type u)).toEquiv.trans
        (PrimeSpectrum.comapEquiv E).toEquiv.symm)
  have hfinSpec : Finite (PrimeSpectrum (Γ(X, ⊤) : Type u)) := Finite.of_equiv _ e
  have hdim : Ring.KrullDimLE 0 (Γ(X, ⊤) : Type u) :=
    Stacks.RingTheory.IntegralOverField.krullDimLE_zero_of_isIntegral φ hφ
  have hdiscSpec : DiscreteTopology (PrimeSpectrum (Γ(X, ⊤) : Type u)) :=
    PrimeSpectrum.discreteTopology_iff_finite_and_krullDimLE_zero.mpr ⟨hfinSpec, hdim⟩
  have hdiscSpec' : DiscreteTopology (Spec Γ(X, ⊤) : Type u) := hdiscSpec
  have htd : TotallyDisconnectedSpace (Spec Γ(X, ⊤) : Type u) := inferInstance
  have hsurj : Function.Surjective (X.toSpecΓ.base) := by
    have hd : Dense (Set.range X.toSpecΓ.base) := IsDominant.denseRange (f := X.toSpecΓ)
    rw [dense_iff_closure_eq, (isClosed_discrete _).closure_eq, Set.range_eq_univ] at hd
    exact hd
  let ψ : ConnectedComponents X → (Spec Γ(X, ⊤) : Type u) :=
    X.toSpecΓ.base.hom.continuous_toFun.connectedComponentsLift
  have hψ : ∀ x : X, ψ (ConnectedComponents.mk x) = X.toSpecΓ.base x := fun x ↦ rfl
  have hψsurj : Function.Surjective ψ := fun t ↦
    (hsurj t).elim fun x hx ↦ ⟨ConnectedComponents.mk x, (hψ x).trans hx⟩
  have hψinj : Function.Injective ψ := Function.Injective.of_comp
    (Finite.surjective_iff_bijective.mp (e.symm.surjective.comp hψsurj)).1
  obtain ⟨c, hc⟩ := hψsurj s
  obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
  have hfib : X.toSpecΓ.base ⁻¹' {s} =
      ConnectedComponents.mk ⁻¹' {ConnectedComponents.mk x} := by
    refine Set.ext fun y ↦ ?_
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    refine ⟨fun hy ↦ hψinj (((hψ y).trans hy).trans hc.symm), fun hy ↦ ?_⟩
    rw [← hψ y, hy, hc]
  rw [show (X.toSpecΓ ⁻¹' {s}) = X.toSpecΓ.base ⁻¹' {s} from rfl, hfib,
    connectedComponents_preimage_singleton]
  exact isConnected_connectedComponent

/-- For `X` proper over a field, `Γ(X, ⊤)` is integral over the field. -/
theorem isIntegral_toSpecΓ_algebraMap (f : X ⟶ Spec (.of k)) [IsProper f] :
    (((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom : k →+* Γ(X, ⊤)).IsIntegral := by
  apply RingHom.isIntegral_respectsIso.2
    (e := (Scheme.ΓSpecIso (.of k)).symm.commRingCatIsoToRingEquiv)
  exact isIntegral_appTop_of_universallyClosed f

/-- For `X` proper over a field the space `X` is Noetherian. -/
theorem noetherianSpace_of_isProper (f : X ⟶ Spec (.of k)) [IsProper f] :
    NoetherianSpace X := by
  have : CompactSpace X := (quasiCompact_iff_compactSpace f).mp inferInstance
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : IsNoetherian X := ⟨⟩
  infer_instance

/-- If `X` is proper over a field, then every fibre of the canonical morphism
`X ⟶ Spec Γ(X, ⊤)` is connected. -/
theorem isConnected_preimage_singleton_toSpecΓ (f : X ⟶ Spec (.of k)) [IsProper f]
    (s : Spec Γ(X, ⊤)) : _root_.IsConnected (X.toSpecΓ ⁻¹' {s}) :=
  have := noetherianSpace_of_isProper f
  isConnected_preimage_singleton_toSpecΓ_of_integral _ (isIntegral_toSpecΓ_algebraMap f) s

/-- The scheme-theoretic fibres of `X ⟶ Spec Γ(X, ⊤)` are connected, for `X` proper over a
field. -/
theorem connectedSpace_fiber_toSpecΓ (f : X ⟶ Spec (.of k)) [IsProper f] (s : Spec Γ(X, ⊤)) :
    ConnectedSpace (X.toSpecΓ.fiber s) :=
  (X.toSpecΓ.fiberHomeo s).connectedSpace_iff.mpr
    (isConnected_iff_connectedSpace.mp (isConnected_preimage_singleton_toSpecΓ f s))

/-- If `X` is proper over an affine scheme, then `X.toSpecΓ` is proper. -/
theorem isProper_toSpecΓ {Y : Scheme.{u}} (f : X ⟶ Y) [IsAffine Y] [IsProper f] :
    IsProper X.toSpecΓ := by
  have h : IsProper (X.toSpecΓ ≫ Spec.map f.appTop) := by
    rwa [← Scheme.toSpecΓ_naturality,
      MorphismProperty.cancel_right_of_respectsIso (P := @IsProper)]
  exact IsProper.of_comp _ (Spec.map f.appTop)

/-- A scheme proper over a field is connected as soon as its ring of global sections is
nontrivial and has no idempotents other than `0` and `1`. -/
@[ega "III 7.8.6.1" "special case"]
theorem connectedSpace_of_isProper_of_isIdempotentElem {L : Type u} [Field L] {Y : Scheme.{u}}
    (g : Y ⟶ Spec (.of L)) [IsProper g] [Nontrivial Γ(Y, ⊤)]
    (hidem : ∀ e : Γ(Y, ⊤), IsIdempotentElem e → e = 0 ∨ e = 1) : ConnectedSpace Y := by
  have hsub : Subsingleton (PrimeSpectrum (Γ(Y, ⊤) : Type u)) :=
    Stacks.RingTheory.IntegralOverField.subsingleton_primeSpectrum_of_isIntegral _
      (isIntegral_toSpecΓ_algebraMap g) hidem
  have hsub' : Subsingleton (Spec Γ(Y, ⊤) : Type u) := hsub
  obtain ⟨s⟩ : Nonempty (PrimeSpectrum (Γ(Y, ⊤) : Type u)) := inferInstance
  have hall : Y.toSpecΓ.base ⁻¹' {(s : Spec Γ(Y, ⊤))} = Set.univ :=
    Set.eq_univ_of_forall fun _ ↦ Subsingleton.elim _ _
  rw [connectedSpace_iff_univ, ← hall]
  exact isConnected_preimage_singleton_toSpecΓ g _

/-- For `X` proper over a field `k`, the canonical morphism `X ⟶ Spec Γ(X, ⊤)` has geometrically
connected fibres if and only if, for every field `L` and every `L`-point `y` of `Spec Γ(X, ⊤)`,
the ring of global sections of the base change `X ×_{Spec Γ(X, ⊤)} Spec L` is nontrivial with no
idempotents other than `0` and `1`. -/
theorem geometricallyConnected_toSpecΓ_iff_isIdempotentElem (f : X ⟶ Spec (.of k)) [IsProper f] :
    GeometricallyConnected X.toSpecΓ ↔
      ∀ (L : Type u) (_ : Field L) (y : Spec (.of L) ⟶ Spec Γ(X, ⊤)),
        Nontrivial Γ(Limits.pullback X.toSpecΓ y, ⊤) ∧
          ∀ e : Γ(Limits.pullback X.toSpecΓ y, ⊤), IsIdempotentElem e → e = 0 ∨ e = 1 := by
  have hpr : IsProper X.toSpecΓ := isProper_toSpecΓ f
  refine ⟨fun hgc L hL y ↦ ?_, fun h ↦ ⟨fun {K} _ y {Z} fst snd hpb ↦ ?_⟩⟩
  · have hc : ConnectedSpace ↥(Limits.pullback X.toSpecΓ y) :=
      pullback_of_geometrically hgc.geometrically_connectedSpace L y
    have hnec : Nonempty ((⊤ : (Limits.pullback X.toSpecΓ y).Opens)) :=
      ⟨⟨Nonempty.some hc.toNonempty, trivial⟩⟩
    refine ⟨Scheme.component_nontrivial _ ⊤, fun e he ↦ ?_⟩
    refine isIdempotentElem_eq_zero_or_one ?_ he
    rw [TopologicalSpace.Opens.coe_top]
    exact isPreconnected_univ
  · have hnt := (h K ‹Field K› y).1
    have hP : ConnectedSpace ↥(Limits.pullback X.toSpecΓ y) :=
      connectedSpace_of_isProper_of_isIdempotentElem (Limits.pullback.snd X.toSpecΓ y)
        (h K ‹Field K› y).2
    exact (hpb.isoPullback.hom.homeomorph).connectedSpace_iff.mpr hP

/-- For `X` proper over a field, `X ⟶ Spec Γ(X, ⊤)` is surjective. -/
theorem surjective_toSpecΓ (f : X ⟶ Spec (.of k)) [IsProper f] :
    Function.Surjective X.toSpecΓ.base := fun s ↦
  (isConnected_preimage_singleton_toSpecΓ f s).nonempty

end Stacks.AlgebraicGeometry.ProperGeomConnected
