module

public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.CompleteIntersection.BaseChange
public import StacksFrontier.RingTheory.Syntomic.SyntomicAt

/-!
# The closed fibre of a local ring map, and when it is a complete intersection

Let `R → A` be a ring map, let `q` be a prime of `A` lying over the prime `p` of `R`, and let
`Rp`, `Aq` be *abstract* localizations of `R` at `p` and of `A` at `q`, forming a commuting
square with `R → A`.  The *closed fibre* of the local ring map `Rp → Aq` is
`κ(Rp) ⊗_{Rp} Aq`, where `κ(Rp)` is the residue field of `Rp`.  This file identifies the
condition that the closed fibre be a complete intersection over `κ(Rp)` with the condition
appearing in item (3) of Stacks Lemma 00SY, namely that `κ(p) ⊗_R A_q` be a complete
intersection over `κ(p)`.

The point of working with abstract localizations is that the stalks of a scheme are abstract
localizations of the sections over any affine open neighbourhood, so the resulting predicate on
a morphism of schemes at a point does not refer to a choice of affine chart.

## Main results

* `IsCompleteIntersection.of_ringEquiv`: being a complete intersection is transported by a pair
  of ring isomorphisms, one of the base field and one of the algebra, which commute with the
  structure maps.  This is the form needed because both the base field and the fibre change when
  an abstract localization is replaced by a concrete one.
* `isCompleteIntersection_closedFibre_iff`: the closed fibre of `Rp → Aq` is a complete
  intersection over `κ(Rp)` if and only if `κ(p) ⊗_R A_q` is a complete intersection over `κ(p)`.
* `exists_notMem_syntomic_iff_isCompleteIntersection_fiber`: for a flat ring map of finite
  presentation, `R → A` is syntomic on a neighbourhood of `q` if and only if `κ(p) ⊗_R A_q` is a
  complete intersection over `κ(p)`.  This is the local form of Stacks Lemma 01UE at the level of
  rings.

## References

* [Stacks 00SY](https://stacks.math.columbia.edu/tag/00SY), Lemma 10.136.15.
* [Stacks 00SD](https://stacks.math.columbia.edu/tag/00SD), Definition 10.135.5.
-/

@[expose] public section

open scoped TensorProduct

open IsLocalRing

universe u v

namespace Stacks.SyntomicLocus

/-! ### Transporting a complete intersection along a pair of ring isomorphisms -/

/-- If `(ek, eD)` is compatible with the structure maps, so is the inverse pair. -/
private theorem ringEquiv_symm_algebraMap {k l : Type u} [Field k] [Field l]
    {D E : Type v} [CommRing D] [CommRing E] [Algebra k D] [Algebra l E]
    {ek : k ≃+* l} {eD : D ≃+* E} (h : ∀ a : k, eD (algebraMap k D a) = algebraMap l E (ek a))
    (a : l) : eD.symm (algebraMap l E a) = algebraMap k D (ek.symm a) := by
  rw [eD.symm_apply_eq, h, RingEquiv.apply_symm_apply]

/-- Being a complete intersection over a field is transported by a pair of ring isomorphisms
`k ≃+* l` and `D ≃+* E` which commute with the two structure maps.  Unlike
`IsCompleteIntersection.of_algEquiv`, the base field is allowed to change; it must stay in the
same universe, because the auxiliary regular local ring of Definition 00SD is quantified in the
universe of the base field. -/
theorem IsCompleteIntersection.of_ringEquiv {k l : Type u} [Field k] [Field l]
    {D E : Type v} [CommRing D] [CommRing E] [Algebra k D] [Algebra l E]
    (ek : k ≃+* l) (eD : D ≃+* E)
    (h : ∀ a : k, eD (algebraMap k D a) = algebraMap l E (ek a))
    (hD : IsCompleteIntersection k D) : IsCompleteIntersection l E := by
  obtain ⟨W, _, _, hreg, hef, fs, hfs, ⟨e⟩⟩ := hD
  let _ : Algebra l k := ek.symm.toRingHom.toAlgebra
  let _ : Algebra l W := ((algebraMap k W).comp ek.symm.toRingHom).toAlgebra
  have hlk : ∀ x : l, algebraMap l k x = ek.symm x := fun _ ↦ rfl
  have htow : IsScalarTower l k W :=
    .of_algebraMap_eq fun x ↦ by rw [RingHom.algebraMap_toAlgebra]; rfl
  have : Algebra.EssFiniteType l k :=
    Algebra.EssFiniteType.of_surjective (Algebra.ofId l k) fun x ↦
      ⟨ek x, by simp [Algebra.ofId, hlk]⟩
  have : Algebra.EssFiniteType l W := .comp l k W
  refine ⟨W, ‹_›, ‹_›, hreg, ‹_›, fs, hfs, ⟨?_⟩⟩
  refine { __ := eD.symm.trans e.toRingEquiv, commutes' := fun a ↦ ?_ }
  change e (eD.symm (algebraMap l E a)) = _
  rw [ringEquiv_symm_algebraMap h, AlgEquiv.commutes,
    IsScalarTower.algebraMap_apply l k (W ⧸ Ideal.ofList fs) a, hlk]

/-! ### The closed fibre of an abstract local ring map -/

section

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    (p : Ideal R) [p.IsPrime] (q : Ideal A) [q.IsPrime] [q.LiesOver p]
    (Rp : Type u) [CommRing Rp] [Algebra R Rp] [IsLocalization.AtPrime Rp p] [IsLocalRing Rp]
    (Aq : Type u) [CommRing Aq] [Algebra A Aq] [Algebra R Aq] [IsScalarTower R A Aq]
    [IsLocalization.AtPrime Aq q] [Algebra Rp Aq] [IsScalarTower R Rp Aq]

/-- The residue field of an abstract localization of `R` at `p`, as an `R`-algebra, is `κ(p)`. -/
noncomputable def residueFieldAlgEquiv : ResidueField Rp ≃ₐ[R] p.ResidueField where
  __ := ResidueField.mapEquiv
    (IsLocalization.algEquiv p.primeCompl Rp (Localization.AtPrime p)).toRingEquiv
  commutes' r := by
    simp only [IsScalarTower.algebraMap_apply R Rp (ResidueField Rp),
      IsScalarTower.algebraMap_apply R (Localization.AtPrime p) p.ResidueField,
      IsLocalRing.ResidueField.algebraMap_eq]
    exact congrArg (residue (Localization.AtPrime p))
      ((IsLocalization.algEquiv p.primeCompl Rp (Localization.AtPrime p)).commutes r)

/-- The closed fibre `κ(Rp) ⊗_{Rp} Aq` of the local ring map `Rp → Aq`, compared with the fibre
`κ(p) ⊗_R A_q` of `R → A` at `p` localized at `q`. -/
noncomputable def closedFibreRingEquiv :
    ResidueField Rp ⊗[Rp] Aq ≃+* p.Fiber (Localization.AtPrime q) :=
  let := IsLocalization.tensorProduct_compatibleSMul (S := p.primeCompl) (A := Rp)
    (ResidueField Rp) Aq
  ((Algebra.TensorProduct.equivOfCompatibleSMul R Rp (ResidueField Rp)
      (ResidueField Rp) Aq).toRingEquiv).trans <|
    ((Algebra.TensorProduct.congr (residueFieldAlgEquiv p Rp)
        (AlgEquiv.refl : Aq ≃ₐ[R] Aq)).toRingEquiv).trans
      (Algebra.TensorProduct.congr (AlgEquiv.refl : p.ResidueField ≃ₐ[R] p.ResidueField)
        ((IsLocalization.algEquiv q.primeCompl Aq
          (Localization.AtPrime q)).restrictScalars R)).toRingEquiv

omit [q.LiesOver p] in
/-- The isomorphism `closedFibreRingEquiv` is compatible with the structure maps from the residue
fields, identified through `residueFieldAlgEquiv`. -/
theorem closedFibreRingEquiv_algebraMap (a : ResidueField Rp) :
    closedFibreRingEquiv p q Rp Aq (algebraMap (ResidueField Rp) _ a) =
      algebraMap p.ResidueField _ (residueFieldAlgEquiv p Rp a) := by
  simp [closedFibreRingEquiv, Algebra.TensorProduct.algebraMap_apply,
    Algebra.TensorProduct.equivOfCompatibleSMul, Algebra.TensorProduct.map_tmul]

omit [q.LiesOver p] in
/-- **The closed fibre of the stalk map, computed in an affine chart.**  The closed fibre
`κ(Rp) ⊗_{Rp} Aq` of the local ring map `Rp → Aq` is a complete intersection over the residue
field `κ(Rp)` if and only if `κ(p) ⊗_R A_q` is a complete intersection over `κ(p)`, the
condition appearing in item (3) of Lemma 00SY. -/
theorem isCompleteIntersection_closedFibre_iff :
    IsCompleteIntersection (ResidueField Rp) (ResidueField Rp ⊗[Rp] Aq) ↔
      IsCompleteIntersection p.ResidueField (p.Fiber (Localization.AtPrime q)) := by
  refine ⟨fun h ↦ IsCompleteIntersection.of_ringEquiv
      (residueFieldAlgEquiv p Rp).toRingEquiv (closedFibreRingEquiv p q Rp Aq)
      (closedFibreRingEquiv_algebraMap p q Rp Aq) h,
    fun h ↦ IsCompleteIntersection.of_ringEquiv
      (residueFieldAlgEquiv p Rp).toRingEquiv.symm (closedFibreRingEquiv p q Rp Aq).symm
      (ringEquiv_symm_algebraMap (closedFibreRingEquiv_algebraMap p q Rp Aq)) h⟩

end

/-- **The local syntomic criterion, Stacks Lemma 01UE (1) ⟺ (3).**  Let `R → A` be flat and of
finite presentation and let `q` be a prime of `A` lying over `p`.  Then `R → A` becomes syntomic
after inverting a single element outside `q` if and only if the fibre `κ(p) ⊗_R A_q` is a
complete intersection over `κ(p)`.

This is Lemma 00SY (1) ⟺ (3) with the finite presentation and flatness conditions of item (3)
supplied by the global hypotheses. -/
theorem exists_notMem_syntomic_iff_isCompleteIntersection_fiber
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    [Algebra.FinitePresentation R A] [Module.Flat R A]
    (p : Ideal R) [p.IsPrime] (q : Ideal A) [q.IsPrime] [q.LiesOver p] :
    (∃ g ∉ q, Algebra.Syntomic R (Localization.Away g)) ↔
      IsCompleteIntersection p.ResidueField (p.Fiber (Localization.AtPrime q)) := by
  have h13 := (Algebra.exists_notMem_syntomic_tfae p q).out 1 3
  refine ⟨fun h ↦ let ⟨_, _, _, _, hci⟩ := h13.mp h; hci, fun h ↦ h13.mpr ⟨1, ?_, ?_, ?_, h⟩⟩
  · exact (Ideal.ne_top_iff_one q).mp ‹q.IsPrime›.ne_top
  · have : Algebra.FinitePresentation A (Localization.Away (1 : A)) :=
      IsLocalization.Away.finitePresentation (1 : A)
    exact Algebra.FinitePresentation.trans R A (Localization.Away (1 : A))
  · rw [Localization.AtPrime.flat_localRingHom_iff]
    infer_instance

/-- Syntomicity is preserved by an isomorphism of algebras. -/
theorem Algebra.Syntomic.of_algEquiv {R A B : Type*} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] (e : A ≃ₐ[R] B) [Algebra.Syntomic R A] :
    Algebra.Syntomic R B where
  flat := Module.Flat.of_linearEquiv e.symm.toLinearEquiv
  finitePresentation := Algebra.FinitePresentation.equiv e
  isLocalCompleteIntersection_fiber p _ :=
    lci_transport p.ResidueField
      (Algebra.TensorProduct.congr
        (AlgEquiv.refl : p.ResidueField ≃ₐ[p.ResidueField] p.ResidueField) e)
      (Algebra.Syntomic.isLocalCompleteIntersection_fiber p)

end Stacks.SyntomicLocus
