module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.FiniteOverSmooth.EtaleLocalStructure
public import StacksFrontier.FieldTheory.AlgebraicClosureTransport

/-!
# A geometrically irreducible open in the fibre of a smooth morphism

Let `h : V ⟶ U` be smooth and quasi-compact and let `v : V`. If the residue field `κ(h v)` is
algebraically closed in `κ(v)`, then the connected component of `v` in the fibre of `h` through
`v` is an open subscheme which is geometrically irreducible over `κ(h v)`.

This is the input that Stacks 05HE (and, in the same shape, Stacks 057K) feeds to Stacks 057J:
057J spreads a geometrically irreducible open of one fibre out to a quasi-compact open with
geometrically integral fibres after an elementary étale base change, and the open it is given is
produced here.

## Main results

* `AlgebraicGeometry.exists_geometricallyIrreducible_open_fibre_of_isAlgClosedIn`.

## Implementation notes

The fibre is locally Noetherian and quasi-compact, hence Noetherian, so it has finitely many
connected components and the connected component `T` of the point is open as well as closed.
Over the field `κ(h v)` the scheme `T` is then connected, and the residue field of `T` at the
point is `κ(v)` because the inclusion of `T` into `V` is a preimmersion; so Tag 04KV applies and
`T` is geometrically connected. Being smooth and quasi-compact over a field it is therefore
geometrically irreducible.

The hypothesis is stated for the residue field map transported along `rfl`, which is the form in
which `AlgebraicGeometry.OneStepDevissageAt` and the elementary étale neighbourhoods of Tag 02LE
record their residue field extensions.

## References

* [Stacks Project, Tag 04KV](https://stacks.math.columbia.edu/tag/04KV)
* [Stacks Project, Tag 05HE](https://stacks.math.columbia.edu/tag/05HE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- If `κ(h v)` is algebraically closed in `κ(v)`, then a connected open of the fibre of `h`
through `v` containing `v` is geometrically connected over `κ(h v)`. -/
theorem geometricallyConnected_fibre_open_of_isAlgClosedIn {V U : Scheme.{u}} (h : V ⟶ U)
    (v : V)
    (hclosed :
      letI : Algebra (U.residueField (h v)) (V.residueField v) :=
        ((U.residueFieldCongr rfl).inv ≫ h.residueFieldMap v).hom.toAlgebra
      IsAlgClosedIn (U.residueField (h v)) (V.residueField v))
    (T : (h.fiber (h v)).Opens) [ConnectedSpace T.toScheme] (hv : h.asFiber v ∈ T) :
    GeometricallyConnected (T.ι ≫ h.fiberToSpecResidueField (h v)) := by
  classical
  set pT : T.toScheme := ⟨h.asFiber v, hv⟩
  set gT := T.ι ≫ h.fiberToSpecResidueField (h v) with hgT
  let k : Type u := U.residueField (h v)
  let E : Type u := V.residueField v
  let KT : Type u := T.toScheme.residueField pT
  set φold : CommRingCat.of k ⟶ CommRingCat.of E :=
    (U.residueFieldCongr rfl).inv ≫ h.residueFieldMap v with hφold
  let : Algebra k E := φold.hom.toAlgebra
  have hclosedOld : IsAlgClosedIn k E := hclosed
  set m : T.toScheme ⟶ V := T.ι ≫ h.fiberι (h v) with hm
  have hmpt : m pT = v := by
    show h.fiberι (h v) (T.ι pT) = v
    exact Scheme.Hom.fiberι_asFiber h v
  have : IsPreimmersion m := IsPreimmersion.comp T.ι (h.fiberι (h v))
  have hmres : IsIso (m.residueFieldMap pT) := isIso_residueFieldMap_of_isPreimmersion m pT
  set eTopIso : CommRingCat.of E ≅ CommRingCat.of KT :=
    (V.residueFieldCongr hmpt).symm ≪≫ asIso (m.residueFieldMap pT) with heTopIso
  set q := gT pT
  have hqa : U.fromSpecResidueField (h v) q = h v := by
    rw [show q = default from Subsingleton.elim _ _]
    exact Scheme.fromSpecResidueField_apply (h v) default
  have : q.asIdeal.IsPrime := q.isPrime
  set φnew : CommRingCat.of k ⟶ CommRingCat.of KT :=
    CommRingCat.ofHom (algebraMap k q.asIdeal.ResidueField) ≫
      (Scheme.Spec.residueFieldIso (.of k) q).inv ≫ gT.residueFieldMap pT with hφnew
  have hcomm : m ≫ h = gT ≫ U.fromSpecResidueField (h v) := by
    simp only [hm, hgT, Category.assoc, h.fiber_fac (h v)]
  have hfield : φnew = φold ≫ eTopIso.hom := calc
    φnew = (U.residueFieldCongr hqa).inv ≫
        (U.fromSpecResidueField (h v)).residueFieldMap q ≫ gT.residueFieldMap pT := by
      simpa only [hφnew, Category.assoc] using congrArg (fun j ↦ j ≫ gT.residueFieldMap pT)
        (algebraMap_residueField_comp_specResidueFieldIso_inv U (h v) q hqa)
    _ = φold ≫ eTopIso.hom := by
      simpa only [hφold, heTopIso, Iso.trans_hom, Iso.symm_hom, asIso_hom,
        Category.assoc] using (residueFieldMap_square_of_eq h gT m
          (U.fromSpecResidueField (h v)) hcomm pT v (h v) hmpt hqa rfl).symm
  let : Algebra k KT := φnew.hom.toAlgebra
  set eTop : E ≃+* KT := eTopIso.commRingCatIsoToRingEquiv
  have he : ∀ c : k, algebraMap k KT c = eTop (algebraMap k E c) := fun c ↦
    congrArg (fun j : CommRingCat.of k ⟶ CommRingCat.of KT ↦ j.hom c) hfield
  have hclosedNew : IsAlgClosedIn k KT :=
    IsAlgClosedIn.of_ringEquiv_square (RingEquiv.refl k) eTop (fun c ↦ (he c).symm) hclosedOld
  exact geometricallyConnected_of_connectedSpace_of_algebraicClosure_eq_bot gT pT hclosedNew

/-- A smooth quasi-compact morphism whose residue field extension at a point `v` is relatively
algebraically closed has a geometrically irreducible open neighbourhood of `v` in the fibre of
`h` through `v`. -/
theorem exists_geometricallyIrreducible_open_fibre_of_isAlgClosedIn {V U : Scheme.{u}}
    (h : V ⟶ U) [Smooth h] [QuasiCompact h] (v : V)
    (hclosed :
      letI : Algebra (U.residueField (h v)) (V.residueField v) :=
        ((U.residueFieldCongr rfl).inv ≫ h.residueFieldMap v).hom.toAlgebra
      IsAlgClosedIn (U.residueField (h v)) (V.residueField v)) :
    ∃ T : (h.fiber (h v)).Opens, h.asFiber v ∈ T ∧
      GeometricallyIrreducible (T.ι ≫ h.fiberToSpecResidueField (h v)) := by
  have hfibSmooth : Smooth (h.fiberToSpecResidueField (h v)) :=
    inferInstanceAs (Smooth (pullback.snd h (U.fromSpecResidueField (h v))))
  have hfibLFT : LocallyOfFiniteType (h.fiberToSpecResidueField (h v)) :=
    inferInstanceAs (LocallyOfFiniteType (pullback.snd h (U.fromSpecResidueField (h v))))
  have hfibQC : QuasiCompact (h.fiberToSpecResidueField (h v)) :=
    inferInstanceAs (QuasiCompact (pullback.snd h (U.fromSpecResidueField (h v))))
  have : IsNoetherian (h.fiber (h v) : Scheme.{u}) := by
    have : IsLocallyNoetherian (h.fiber (h v) : Scheme.{u}) :=
      LocallyOfFiniteType.isLocallyNoetherian (h.fiberToSpecResidueField (h v))
    have : CompactSpace (h.fiber (h v) : Scheme.{u}) :=
      (quasiCompact_iff_compactSpace (h.fiberToSpecResidueField (h v))).mp hfibQC
    exact ⟨⟩
  have : Finite (_root_.ConnectedComponents (h.fiber (h v) : Scheme.{u})) :=
    NoetherianSpace.finite_connectedComponents _
  set T : (h.fiber (h v)).Opens := ⟨connectedComponent (h.asFiber v),
    (isClopen_connectedComponent_of_finite_connectedComponents _).2⟩
  have : ConnectedSpace T.toScheme :=
    isConnected_iff_connectedSpace.mp isConnected_connectedComponent
  refine ⟨T, mem_connectedComponent, ?_⟩
  exact geometricallyIrreducible_of_geometricallyConnected_of_smooth _
    (geometricallyConnected_fibre_open_of_isAlgClosedIn h v hclosed T mem_connectedComponent)

end AlgebraicGeometry

end
