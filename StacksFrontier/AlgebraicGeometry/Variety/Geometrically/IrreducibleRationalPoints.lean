module

public import Mathlib.AlgebraicGeometry.Geometrically.Irreducible
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Iso
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteLocallyFree.NowhereDense
public import StacksFrontier.AlgebraicGeometry.Variety.Geometric.IrreducibleComponentsBaseChange
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.IrreducibleSeparableClosure
import StacksFrontier.AlgebraicGeometry.Groupoids.GroupSchemeProperties.TangentIdentity

/-!
# Dense rational points and geometric irreducibility

An irreducible scheme over a field whose rational points are dense is geometrically
irreducible.

## Main results

* `AlgebraicGeometry.geometricallyIrreducible_of_irreducibleSpace_of_dense_rationalPoints`:
  an irreducible scheme over a field with a dense set of rational points is geometrically
  irreducible.

## Implementation notes

A rational point of `X` over `k` is a section `s : Spec k ⟶ X` of the structure morphism. Its
image is a singleton, and density is asked of the union of these images; no distinguished point
of `Spec k` has to be chosen.

The proof tests geometric irreducibility over a separable algebraic closure. Over a finite
separable extension `K/k` the projection `p : X_K ⟶ X` is finite, so the image of the
intersection of two distinct irreducible components of `X_K` is nowhere dense; a rational point
outside that image lies in the image of every irreducible component of `X_K`, and its fibre in
`X_K` is a single point because the residue field extension at a rational point is trivial.
Hence there is only one component.

## References

* [Stacks Project, Tag 0G69](https://stacks.math.columbia.edu/tag/0G69)
-/

@[expose] public section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry

/-- The fibre of the base change `X_K ⟶ X` over a rational point of `X` is a single point. -/
private lemma baseChange_fiber_unique
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    (X : Scheme.{u}) (f : X ⟶ Spec (.of k))
    (s : Spec (.of k) ⟶ X) (hs : s ≫ f = 𝟙 (Spec (.of k)))
    (x : X) (hx : x = s (IsLocalRing.closedPoint k))
    (y z : ↥(pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K)))))
    (hy : (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K)))).base y = x)
    (hz : (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K)))).base z = x) :
    y = z := by
  let g := Spec.map (CommRingCat.ofHom (algebraMap k K))
  let e := Scheme.Pullback.carrierEquiv (f := f) (g := g)
  let Ty := (e y).1
  let Tz := (e z).1
  have hT (w : ↥(pullback f g)) (hw : (pullback.fst f g).base w = x) : (e w).1.x = x := by
    simpa [e, Scheme.Pullback.carrierEquiv, Scheme.Pullback.Triplet.ofPoint] using hw
  have hTz : Tz.x = x := hT z hz
  have hTyTz : Ty = Tz :=
    Scheme.Pullback.Triplet.ext ((hT y hy).trans hTz.symm) (Subsingleton.elim _ _)
  have hfieldTz : IsIso Tz.tensorInr := by
    have : IsIso (f.residueFieldMap Tz.x) := by
      rw [hTz, hx]
      exact isIso_residueFieldMap_of_mem_range_section f s hs (IsLocalRing.closedPoint k)
    have : IsIso (((Spec (.of k)).residueFieldCongr Tz.hx.symm).hom ≫
        f.residueFieldMap Tz.x) := inferInstance
    dsimp [Scheme.Pullback.Triplet.tensorInr]
    exact (IsPushout.of_hasPushout _ _).isIso_inr_of_isIso
  let : Field (Tz.tensor : Type u) :=
    ((asIso Tz.tensorInr).commRingCatIsoToRingEquiv.symm.toMulEquiv.isField
      (Field.toIsField ((Spec (.of K)).residueField Tz.y))).toField
  have hpoint :
      Spec.map (Scheme.Pullback.Triplet.tensorCongr hTyTz).inv (e y).2 = (e z).2 := by
    let : Unique (PrimeSpectrum (Tz.tensor : Type u)) := inferInstance
    show PrimeSpectrum.comap _ _ = _
    exact Subsingleton.elim _ _
  exact e.injective (Scheme.Pullback.carrierEquiv_eq_iff.mpr ⟨hTyTz, hpoint⟩)

/-- The intersection of two distinct irreducible components of a topological space is nowhere
dense. -/
private lemma nowhereDense_inter_of_distinct_irreducibleComponents
    {α : Type*} [TopologicalSpace α] {A B : Set α}
    (hA : A ∈ irreducibleComponents α) (hB : B ∈ irreducibleComponents α)
    (hne : A ≠ B) : IsNowhereDense (A ∩ B) := by
  rw [IsNowhereDense, (isClosed_of_mem_irreducibleComponents A hA).inter
    (isClosed_of_mem_irreducibleComponents B hB) |>.closure_eq]
  refine Set.eq_empty_iff_forall_notMem.mpr fun x hx => ?_
  have hsubB : B ⊆ closure (interior (A ∩ B)) := fun a ha => mem_closure_iff.mpr fun U hU hau => by
    obtain ⟨w, -, hw⟩ :=
      hB.1.2 _ U isOpen_interior hU ⟨x, (interior_subset hx).2, hx⟩ ⟨a, ha, hau⟩
    exact ⟨w, hw.2, hw.1⟩
  have hBA : B ⊆ A := hsubB.trans <| closure_minimal (interior_subset.trans Set.inter_subset_left)
    (isClosed_of_mem_irreducibleComponents A hA)
  exact hne (Set.Subset.antisymm (hB.2 hA.1 hBA) hBA)

/-- Base change of an irreducible scheme with dense rational points along a finite extension of
the ground field stays irreducible. -/
private theorem irreducibleSpace_baseChange_of_dense_rationalPoints
    (k K : Type u) [Field k] [Field K] [Algebra k K] [FiniteDimensional k K]
    (X : Scheme.{u}) (f : X ⟶ Spec (.of k)) [IrreducibleSpace X]
    (h : Dense {x : X | ∃ (s : Spec (.of k) ⟶ X),
      s ≫ f = 𝟙 (Spec (.of k)) ∧ x ∈ Set.range s.base}) :
    IrreducibleSpace ↥(pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K)))) := by
  let g := Spec.map (CommRingCat.ofHom (algebraMap k K))
  let Y := ↥(pullback f g)
  let p := pullback.fst f g
  obtain ⟨x₀, hx₀⟩ := h.nonempty
  obtain ⟨y₀, -, -⟩ := Scheme.Pullback.exists_preimage_pullback
    (f := f) (g := g) x₀ (IsLocalRing.closedPoint K) (Subsingleton.elim _ _)
  let C := irreducibleComponent y₀
  have hC : C ∈ irreducibleComponents Y := irreducibleComponent_mem_irreducibleComponents y₀
  have : IsFinite g := by
    rw [IsFinite.SpecMap_iff]
    exact RingHom.finite_algebraMap.mpr inferInstance
  have himage (E : Set Y) (hE : E ∈ irreducibleComponents Y) : p.base '' E = Set.univ := by
    simpa [irreducibleComponents_eq_singleton] using
      mapsTo_irreducibleComponents_baseChange k K X f hE
  have hcomponent_eq (D : Set Y) (hD : D ∈ irreducibleComponents Y) : D = C := by
    by_contra hne
    have hTclosed : IsClosed (D ∩ C) :=
      (isClosed_of_mem_irreducibleComponents D hD).inter
        (isClosed_of_mem_irreducibleComponents C hC)
    obtain ⟨hcompOpen, hcompDense⟩ := isClosed_isNowhereDense_iff_compl.mp
      ⟨p.isClosedMap _ hTclosed, Stacks.Morphisms.isNowhereDense_image_of_isFinite p hTclosed
        (nowhereDense_inter_of_distinct_irreducibleComponents hD hC hne)⟩
    obtain ⟨x, hxnot, hxrat⟩ :=
      (dense_iff_inter_open.mp h) (p.base '' (D ∩ C))ᶜ hcompOpen hcompDense.nonempty
    obtain ⟨s, hs, x', rfl⟩ := hxrat
    obtain ⟨yd, hydD, hyd⟩ := (himage D hD).ge (Set.mem_univ _)
    obtain ⟨yc, hycC, hyc⟩ := (himage C hC).ge (Set.mem_univ _)
    have heq : yd = yc := baseChange_fiber_unique k K X f s hs (s.base x')
      (congrArg s.base (Subsingleton.elim _ _)) yd yc
      hyd hyc
    exact hxnot ⟨yd, ⟨hydD, heq ▸ hycC⟩, hyd⟩
  have hCuniv : C = Set.univ := Set.eq_univ_of_forall fun y =>
    hcomponent_eq _ (irreducibleComponent_mem_irreducibleComponents y) ▸ mem_irreducibleComponent
  exact (irreducibleSpace_def Y).mpr
    (hCuniv ▸ isIrreducible_irreducibleComponent : IsIrreducible (Set.univ : Set Y))

/-- **Stacks Project, Tag 0G69.** An irreducible scheme over a field with a dense set of
rational points is geometrically irreducible. -/
@[stacks 0G69]
theorem geometricallyIrreducible_of_irreducibleSpace_of_dense_rationalPoints
    (k : Type u) [Field k] (X : Scheme.{u}) (f : X ⟶ Spec (.of k))
    [IrreducibleSpace X]
    (h : Dense {x : X | ∃ (s : Spec (.of k) ⟶ X),
      s ≫ f = 𝟙 (Spec (.of k)) ∧ x ∈ Set.range s.base}) :
    GeometricallyIrreducible f := by
  apply ((geometricallyIrreducible_tfae_of_isSepClosure
    k X f (SeparableClosure k)).out 2 1).mp
  intro K _ hK _ hsepK
  exact irreducibleSpace_baseChange_of_dense_rationalPoints k K X f h

end AlgebraicGeometry
