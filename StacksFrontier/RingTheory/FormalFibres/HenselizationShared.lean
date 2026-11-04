module

public import Mathlib
public import StacksFrontier.RingTheory.Etale.IndEtaleFibres
public import StacksFrontier.RingTheory.FormallySmooth.TopologicalRings
public import StacksFrontier.RingTheory.Henselian.Henselization.Basic
public import StacksFrontier.RingTheory.Henselian.Henselization.Defs

@[expose] public section

/-!
# Shared henselization helpers for the formal-fibre and G-ring developments

Stacks Project, Chapter 15 "More on Algebra". This module holds the general henselization
bookkeeping that `StacksFrontier.RingTheory.FormalFibres.Henselization` (Tags 0BKA, 0C36) and
`StacksFrontier.RingTheory.GRing.Henselization` (Tags 07PT, 07QR, 0AH2, 0AH3) both need: the
transport of ind-étaleness along restriction of scalars by a ring equivalence, transport of
henselianness along a ring equivalence, the `ULift` and residue-field-equivalence transports of
`IsLocalRing.IsHenselization`, the concrete directed-preorder presentation of a categorically
ind-étale algebra, and the passage from topological formal smoothness for the adic topologies to
the `n`-adic predicate
`RingHom.FormallySmoothNAdic`. Those two files are import-incomparable — neither is an ancestor of
the other — so neither could host these helpers without being imported by the other; keeping them
here lets both import a single small module whose own import closure is already contained in the
closure of each.

The restriction-of-scalars functor and equivalence themselves,
`Stacks.Henselization.Shared.commAlgCatRestrictScalars` and
`Stacks.Henselization.Shared.commAlgCatRestrictScalarsEquivalence`, together with
`Stacks.Henselization.Shared.ind_etale_restrictScalars`, are in the same namespace but
live in `StacksFrontier.RingTheory.Henselian.Henselization.Defs`: they were needed by developments
that do not see this module either, and that module is the common ancestor of all of them.

## Main results

* `Stacks.Henselization.Shared.henselianLocalRing_of_ringEquiv`: henselianness transports along
  a ring equivalence.
* `Stacks.Henselization.Shared.isHenselization_ulift`,
  `Stacks.Henselization.Shared.isHenselization_of_residueFieldEquiv`: transport of
  `IsLocalRing.IsHenselization` along `ULift` and along an equivalence of the target residue field.
* `Stacks.Henselization.Shared.isFilteredColimitEtale_of_ind`: a categorically ind-étale algebra
  satisfies the concrete `IsFilteredColimitEtale` predicate.
* `Stacks.Henselization.Shared.formallySmoothNAdic_of_isFormallySmooth`: topological formal
  smoothness for the adic topologies implies `RingHom.FormallySmoothNAdic`.

## Implementation notes

The declarations live in the namespace `Stacks.Henselization.Shared` rather than at the root: a
root-level public declaration of any of these names would be a hard error in the many files of this
development that declare a root-level `private` of the same name.
-/

namespace Stacks.Henselization.Shared

open CategoryTheory CategoryTheory.Limits IsLocalRing

universe u v w

/-- The concrete directed-preorder presentation associated to a categorical filtered-colimit
presentation: reindex the filtered category by a directed preorder and transport the colimit
through the forgetful functors to `Under (CommRingCat.of A)`, `CommRingCat` and `Type u`. -/
theorem isFilteredColimitEtale_of_ind (A B : Type u) [CommRing A] [CommRing B]
    [Algebra A B]
    (h : (CommAlgCat.etale.{u} A).ind.{u} (CommAlgCat.of A B)) :
    IsFilteredColimitEtale.{u, u, u, u} A B := by
  classical
  obtain ⟨J, _, _, pres, hEt⟩ := h
  obtain ⟨ι, _, _, _, F, _⟩ := IsFiltered.exists_directed J
  let pres' := pres.reindex F
  let e := commAlgCatEquivUnder (CommRingCat.of A)
  let c₁ := e.functor.mapCocone pres'.cocone
  let c₂ := (Under.forget (CommRingCat.of A)).mapCocone c₁
  let c₃ := (forget CommRingCat.{u}).mapCocone c₂
  have hc₃ : IsColimit c₃ := isColimitOfPreserves (forget CommRingCat.{u})
    (isColimitOfPreserves (Under.forget (CommRingCat.of A))
      (isColimitOfPreserves e.functor pres'.isColimit))
  refine ⟨ι, inferInstance, inferInstance, inferInstance,
    (fun i ↦ (pres'.diag.obj i).carrier), (fun i ↦ (pres'.diag.obj i).commRing),
    (fun i ↦ (pres'.diag.obj i).algebra), fun i ↦ hEt (F.obj i), ?_⟩
  · refine ⟨(fun i j hij ↦ (pres'.diag.map (homOfLE hij)).hom), ?_,
      (fun i ↦ (pres'.ι.app i).hom), ?_, ?_, ?_⟩
    · constructor
      · intro i z
        simp
      · intro k j i hij hjk z
        simp only [← CommAlgCat.comp_apply]
        rw [← Functor.map_comp]
        congr 1
    · intro i j hij z
      exact congrArg (fun f : (pres'.diag.obj i) ⟶ CommAlgCat.of A B ↦ f.hom z)
        (pres'.w (homOfLE hij))
    · intro z
      exact Types.jointly_surjective_of_isColimit hc₃ z
    · intro i a b hab
      have hab' : c₃.ι.app i a = c₃.ι.app i b := hab
      obtain ⟨j, f, g, heq⟩ := (Types.FilteredColimit.isColimit_eq_iff _ hc₃).mp hab'
      obtain rfl : f = g := Subsingleton.elim _ _
      exact ⟨j, leOfHom f, heq⟩

/-- Henselianness of a local ring transports along a ring equivalence. -/
lemma henselianLocalRing_of_ringEquiv {A : Type u} {B : Type v}
    [CommRing A] [CommRing B] [IsLocalRing B] [HenselianLocalRing A]
    (e : A ≃+* B) : HenselianLocalRing B := by
  have hm (b : B) : e.symm b ∈ IsLocalRing.maximalIdeal A ↔
      b ∈ IsLocalRing.maximalIdeal B := by
    simp [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  constructor
  intro f hf b hb hd
  have hb' : (f.map e.symm.toRingHom).eval (e.symm b) ∈ IsLocalRing.maximalIdeal A := by
    show (f.map e.symm.toRingHom).eval (e.symm.toRingHom b) ∈ _
    rw [Polynomial.eval_map_apply]
    exact (hm _).mpr hb
  have hd' : IsUnit ((f.map e.symm.toRingHom).derivative.eval (e.symm b)) := by
    rw [Polynomial.derivative_map]
    show IsUnit ((f.derivative.map e.symm.toRingHom).eval (e.symm.toRingHom b))
    rw [Polynomial.eval_map_apply]
    exact hd.map e.symm.toRingHom
  obtain ⟨a, ha, hab⟩ := HenselianLocalRing.is_henselian
    (f.map e.symm.toRingHom) (hf.map _) (e.symm b) hb' hd'
  refine ⟨e a, ?_, ?_⟩
  · simpa [Polynomial.map_map] using ha.map (f := e.toRingHom)
  · exact (hm _).mp (by simpa using hab)

/-- A henselization of `R` with residue field extension `L` remains one after lifting both
the base ring and the henselization to the join of their universes. -/
lemma isHenselization_ulift (R : Type u) (L : Type v) (H : Type w)
    [CommRing R] [IsLocalRing R] [Field L] [Algebra (ResidueField R) L]
    [CommRing H] [IsLocalRing H] [Algebra R H] [IsHenselization R L H] :
    let R' := ULift.{w} R
    let H' := ULift.{u} H
    letI : IsLocalRing R' := (ULift.ringEquiv : R' ≃+* R).symm.isLocalRing
    letI : IsLocalRing H' := (ULift.ringEquiv : H' ≃+* H).symm.isLocalRing
    letI : Algebra R' H' :=
      ((algebraMap R H').comp (ULift.ringEquiv : R' ≃+* R).toRingHom).toAlgebra
    letI : Algebra (ResidueField R') L :=
      ((algebraMap (ResidueField R) L).comp
        (ResidueField.mapEquiv (ULift.ringEquiv : R' ≃+* R)).toRingHom).toAlgebra
    IsHenselization R' L H' := by
  dsimp only
  let R' := ULift.{w} R
  let H' := ULift.{u} H
  have : IsLocalRing R' := (ULift.ringEquiv : R' ≃+* R).symm.isLocalRing
  have : IsLocalRing H' := (ULift.ringEquiv : H' ≃+* H).symm.isLocalRing
  let eR : R' ≃+* R := ULift.ringEquiv
  let eH : H ≃+* H' := ULift.ringEquiv.symm
  let : Algebra R' H' := ((algebraMap R H').comp eR.toRingHom).toAlgebra
  let : Algebra (ResidueField R') L :=
    ((algebraMap (ResidueField R) L).comp (ResidueField.mapEquiv eR).toRingHom).toAlgebra
  have : HenselianLocalRing H := IsHenselization.henselian R L
  have hH : HenselianLocalRing H' := henselianLocalRing_of_ringEquiv eH
  have hind := ind_etale_restrictScalars eR (CommAlgCat.of R H')
    (IsHenselization.ind_etale (R := R) (L := L) (Rh := H))
  obtain ⟨eL, heL⟩ := IsHenselization.exists_residueFieldEquiv (R := R) (L := L) (Rh := H)
  refine IsHenselization.of_ind_etale.{max u w, v, 0} hH hind
    ⟨eL.trans (ResidueField.mapEquiv eH), fun r => ?_⟩
  show ResidueField.mapEquiv eH
    (eL (algebraMap (ResidueField R) L (ResidueField.mapEquiv eR (residue R' r)))) = _
  simp only [ResidueField.mapEquiv, RingEquiv.coe_mk, Equiv.coe_fn_mk,
    ResidueField.map_residue, heL]
  rfl

/-- Being a henselization is insensitive to replacing the prescribed residue field extension
by an equivalent one. -/
lemma isHenselization_of_residueFieldEquiv
    (R : Type u) (L : Type v) (L' : Type*) (H : Type u)
    [CommRing R] [IsLocalRing R] [Field L] [Algebra (ResidueField R) L]
    [Field L'] [Algebra (ResidueField R) L']
    [CommRing H] [IsLocalRing H] [Algebra R H] [IsHenselization R L H]
    (e : L' ≃+* L) (he : ∀ r, e (algebraMap (ResidueField R) L' r) =
      algebraMap (ResidueField R) L r) : IsHenselization R L' H := by
  obtain ⟨E, hE⟩ := IsHenselization.exists_residueFieldEquiv (R := R) (L := L) (Rh := H)
  exact IsHenselization.of_ind_etale.{u, _, 0} (IsHenselization.henselian R L)
    (IsHenselization.ind_etale_of_universe_le.{u, v, 0} (R := R) L)
    ⟨e.trans E, fun r => (congrArg E (he (residue R r))).trans (hE r)⟩

/-- Topological formal smoothness of `f` for the `m`-adic and `n`-adic topologies implies
the `n`-adic formal smoothness predicate `RingHom.FormallySmoothNAdic`. -/
lemma formallySmoothNAdic_of_isFormallySmooth
    {R : Type v} {S : Type w} [CommRing R] [CommRing S]
    (f : R →+* S) (m : Ideal R) (n : Ideal S)
    (h : letI : TopologicalSpace R := m.adicTopology
         letI : IsTopologicalRing R := m.nonarchimedean.toIsTopologicalRing
         letI : IsLinearTopology R R := m.isLinearTopology
         letI : TopologicalSpace S := n.adicTopology
         letI : IsTopologicalRing S := n.nonarchimedean.toIsTopologicalRing
         letI : IsLinearTopology S S := n.isLinearTopology
         IsFormallySmooth.{u} f) : RingHom.FormallySmoothNAdic.{u} f n := by
  have hd := (isFormallySmooth_of_formallySmooth_and_isAdic_and_iff_discrete f).2
    m n h.1 |>.mp h
  let : TopologicalSpace R := ⊥
  have : DiscreteTopology R := ⟨rfl⟩
  let : TopologicalSpace S := n.adicTopology
  have : IsTopologicalRing S := n.nonarchimedean.toIsTopologicalRing
  intro A _ J hJ g ψ hcomm hk
  let : TopologicalSpace A := ⊥
  have : DiscreteTopology A := ⟨rfl⟩
  have : DiscreteTopology (A ⧸ J) :=
    QuotientAddGroup.discreteTopology (isOpen_discrete (J : Set A))
  have hψ : Continuous ψ := by
    have ht : (inferInstance : TopologicalSpace (A ⧸ J)) =
        (⊥ : Ideal (A ⧸ J)).adicTopology :=
      (is_bot_adic_iff (A := A ⧸ J)).2 inferInstance
    have hψ' : @Continuous S (A ⧸ J) n.adicTopology (⊥ : Ideal (A ⧸ J)).adicTopology ψ := by
      obtain ⟨k, hk, hk'⟩ := hk
      exact (RingHom.continuous_adic_iff ψ n ⊥).2 ⟨k, hk, fun x hx => hk' hx⟩
    exact Eq.mp (congrArg (fun t => @Continuous S (A ⧸ J) n.adicTopology t ψ) ht.symm) hψ'
  obtain ⟨g', -, hg', hψ'⟩ := hd.2 A J hJ g continuous_of_discreteTopology ψ hψ hcomm
  exact ⟨g', hψ', hg'⟩

end Stacks.Henselization.Shared
