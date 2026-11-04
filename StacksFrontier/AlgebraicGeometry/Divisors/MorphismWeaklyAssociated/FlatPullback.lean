module

public import Mathlib.AlgebraicGeometry.Fiber
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Flatness.WeaklyAssociated
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.FibreStalk
public import StacksFrontier.AlgebraicGeometry.RingedSpace.Flat
public import StacksFrontier.RingTheory.Ideal.Annihilator.FlatBaseChange
public import StacksFrontier.Topology.Sheaves.Functors.Module.RingedSpace
public import StacksFrontier.Topology.Sheaves.RingedSpace.ModulePullbackStalkAdjunction

/-!
# Weakly associated points under a flat pullback

Let `f : X ⟶ S` be a morphism of schemes and let `x : X` be a point at which `f` is flat and
which is a generic point of the scheme-theoretic fibre through it. This file shows that `x` is
weakly associated to the pullback `f^* G` of an `𝒪_S`-module `G` as soon as `f x` is weakly
associated to `G`.

The argument is entirely stalkwise. Flatness of `𝒪_{S, f x} → 𝒪_{X, x}` turns the annihilator
of a witnessing element `m` of `G_{f x}` into the annihilator of `1 ⊗ m` in
`𝒪_{X, x} ⊗ G_{f x} ≅ (f^* G)_x`, by base change of annihilators along a flat extension. It
therefore suffices to see that the extension of the maximal ideal of `𝒪_{S, f x}` to `𝒪_{X, x}`
has the maximal ideal of `𝒪_{X, x}` as its radical. That extension is the kernel of the
surjection onto the local ring of the fibre at `x`
(`AlgebraicGeometry.quotientStalkEquivFiberStalk`), and the local ring of a scheme at a generic
point has nilpotent maximal ideal.

## Main results

* `AlgebraicGeometry.isWeaklyAssociatedPoint_pullback_of_isGenericPoint_fiber`: Stacks 05F0.

## Implementation notes

The point of the fibre corresponding to `x` is `f.asFiber x`, and flatness at a point is
`AlgebraicGeometry.IsFlatAt` for the underlying morphism of ringed spaces. Quasi-coherence of
the module is not used.

## References

* [Stacks Project, Tag 05F0](https://stacks.math.columbia.edu/tag/05F0)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Limits

universe u

namespace AlgebraicGeometry

/-- At a generic point of a scheme every element of the maximal ideal of the local ring is
nilpotent: the only prime of that local ring is its maximal ideal. -/
lemma maximalIdeal_isNilpotent_of_mem_genericPoints
    {T : Scheme.{u}} {y : T} (hy : y ∈ genericPoints T) :
    ∀ a ∈ IsLocalRing.maximalIdeal (T.presheaf.stalk y), IsNilpotent a := by
  intro a ha
  rw [← mem_nilradical, nilradical_eq_sInf, Ideal.mem_sInf]
  intro J hJ
  let R := T.presheaf.stalk y
  let z : Spec R := ⟨J, hJ⟩
  let zmax : Spec R := IsLocalRing.closedPoint R
  let t : T := T.fromSpecStalk y z
  have hty : t ⤳ y := by
    have ht : t ∈ Set.range (T.fromSpecStalk y) := ⟨z, rfl⟩
    simpa only [T.range_fromSpecStalk, Set.mem_ofPred_eq] using ht
  let eta : genericPoints T := ⟨y, hy⟩
  let C : Set T := genericPoints.component eta
  have hgeneric : IsGenericPoint y C := genericPoints.isGenericPoint eta
  have hCmin : Maximal IsIrreducible C := (genericPoints.component eta).property
  have hsubset : C ⊆ closure ({t} : Set T) := by
    rw [← hgeneric.def]
    exact closure_minimal (Set.singleton_subset_iff.mpr
      (specializes_iff_mem_closure.mp hty)) isClosed_closure
  have hclosure : closure ({t} : Set T) = C :=
    (hCmin.eq_of_subset (isIrreducible_singleton.closure) hsubset).symm
  have htGeneric : IsGenericPoint t C := by
    rw [← hclosure]
    exact isGenericPoint_closure
  have hty' : t = y := htGeneric.eq hgeneric
  have hz : z = zmax := (T.fromSpecStalk y).isEmbedding.injective
    (hty'.trans (T.fromSpecStalk_closedPoint (x := y)).symm)
  have hJ : J = IsLocalRing.maximalIdeal R := by
    simpa [z, zmax, IsLocalRing.closedPoint] using congrArg (fun z : Spec R => z.asIdeal) hz
  rwa [hJ]

/-- A linear equivalence preserves the annihilator of an element. -/
lemma annihilatorOfElem_semiring_eq_of_linearEquiv
    {R : Type*} [CommRing R] {M N : Type*}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (e : M ≃ₗ[R] N) (m : M) :
    annihilatorOfElem_semiring (R := R) m =
      annihilatorOfElem_semiring (R := R) (e m) := by
  ext r
  rw [mem_annihilatorOfElem_semiring_iff, mem_annihilatorOfElem_semiring_iff]
  exact ⟨fun h => by simpa using congrArg e h, fun h => e.injective (by simpa using h)⟩

/-- At a point which is generic in its scheme-theoretic fibre, the extension of the maximal
ideal of the target local ring has the maximal ideal of the source local ring as its radical.

The quotient of `𝒪_{X, x}` by that extension is the local ring of the fibre at `x`, and the
maximal ideal of the local ring of a scheme at a generic point is nilpotent. -/
@[ega "IV 5.5.2" "partial"]
lemma radical_map_stalkMap_maximalIdeal_eq_of_mem_genericPoints_fiber
    {X S : Scheme.{u}} (f : X ⟶ S) (x : X)
    (hgeneric : f.asFiber x ∈ genericPoints (f.fiber (f x))) :
    (Ideal.map (f.stalkMap x).hom
      (IsLocalRing.maximalIdeal (S.presheaf.stalk (f x)))).radical =
      IsLocalRing.maximalIdeal (X.presheaf.stalk x) := by
  let A := S.presheaf.stalk (f x)
  let B := X.presheaf.stalk x
  let φ : A →+* B := (f.stalkMap x).hom
  let J : Ideal B := Ideal.map φ (IsLocalRing.maximalIdeal A)
  let Q := B ⧸ J
  let C := (f.fiber (f x)).presheaf.stalk (f.asFiber x)
  let e : Q ≃+* C := quotientStalkEquivFiberStalk f x
  have hJle : J ≤ IsLocalRing.maximalIdeal B := by
    simpa [J, φ] using IsLocalRing.map_maximalIdeal_le φ
  have : Nontrivial Q := Ideal.Quotient.nontrivial_iff.mpr
    (ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal B).ne_top hJle)
  have : IsLocalRing Q :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
  have : IsLocalHom (Ideal.Quotient.mk J) :=
    IsLocalHom.of_surjective (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
  have : IsLocalHom e.toRingHom := IsLocalHom.of_surjective e.toRingHom e.surjective
  apply le_antisymm
  · exact (Ideal.radical_mono hJle).trans_eq
      (IsLocalRing.maximalIdeal.isMaximal B).isPrime.radical
  · intro b hb
    let q : Q := Ideal.Quotient.mk J b
    have hqmax : q ∈ IsLocalRing.maximalIdeal Q := map_nonunit _ b hb
    have hemax : e q ∈ IsLocalRing.maximalIdeal C := map_nonunit e.toRingHom q hqmax
    obtain ⟨n, hn⟩ :=
      maximalIdeal_isNilpotent_of_mem_genericPoints hgeneric (e q) hemax
    have hnq : q ^ n = 0 := by
      apply e.injective
      simpa using hn
    exact Ideal.mem_radical_iff.mpr ⟨n, Ideal.Quotient.eq_zero_iff_mem.mp (by simpa [q] using hnq)⟩

/-- If `I` has radical `P` and the extension of `P` along `f` has radical `Q`, then the
extension of `I` along `f` has radical `Q`. -/
private lemma radical_map_eq_of_radical_eq {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) {I P : Ideal R} {Q : Ideal S}
    (hI : I.radical = P) (hP : (P.map f).radical = Q) : (I.map f).radical = Q := by
  subst hI hP
  exact le_antisymm (Ideal.radical_mono (Ideal.map_mono Ideal.le_radical))
    (by simpa using Ideal.radical_mono (Ideal.map_radical_le f))

open TensorProduct in
/-- **Stacks Project, Tag 05F0.** A point which is generic in its fibre and at which a
morphism is flat is weakly associated to the pullback of a module whenever
its image is weakly associated to the original module. -/
@[stacks 05F0]
theorem isWeaklyAssociatedPoint_pullback_of_isGenericPoint_fiber
    {X S : Scheme.{u}} (f : X ⟶ S) (G : S.Modules) (x : X)
    (hflat : IsFlatAt f.toLRSHom.toShHom x)
    (hgeneric : f.asFiber x ∈ genericPoints (f.fiber (f x)))
    (hweak : Stacks.Divisors.IsWeaklyAssociatedPoint G (f x)) :
    Stacks.Divisors.IsWeaklyAssociatedPoint ((Scheme.Modules.pullback f).obj G) x := by
  let g := f.toLRSHom.toShHom
  let A := S.presheaf.stalk (g.hom.base x)
  let B := X.presheaf.stalk x
  let φ : A →+* B := (f.stalkMap x).hom
  let : Algebra (↑A) (↑B) := φ.toAlgebra
  have : IsLocalHom φ := by
    show IsLocalHom (f.stalkMap x).hom
    exact f.toLRSHom.prop x
  let M := ↑(TopCat.Presheaf.stalk G.val.presheaf (g.hom.base x))
  let : Module A M :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      G.val (g.hom.base x)
  change WeaklyAssociated (IsLocalRing.maximalIdeal A) M at hweak
  obtain ⟨m, hmrad⟩ :=
    (weaklyAssociated_maximalIdeal_iff_exists_radical_eq (S := A) (N := M)).mp hweak
  let P' : PresheafOfModules (X.presheaf ⋙ forget₂ CommRingCat RingCat) :=
    ((RingedSpaceModuleAdjunction.modulePullback g).obj G).val
  let N := ↑(TopCat.Presheaf.stalk P'.presheaf x)
  let : Module B N :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      P' x
  let e : N ≃ₗ[B] TensorProduct A B M := Classical.choose
    (RingedSpaceModuleAdjunction.exists_modulePullbackStalkLinearEquiv g G x)
  let n : N := e.symm ((1 : B) ⊗ₜ[A] m)
  have : Module.Flat A B := hflat
  have hAnn :
      annihilatorOfElem_semiring (R := B) n =
        Ideal.map φ (annihilatorOfElem_semiring (R := A) m) := calc
    _ = annihilatorOfElem_semiring (R := B) (e n) :=
      annihilatorOfElem_semiring_eq_of_linearEquiv e n
    _ = annihilatorOfElem_semiring (R := B) ((1 : B) ⊗ₜ[A] m) := by simp [n]
    _ = Ideal.torsionOf B (B ⊗[A] M) ((1 : B) ⊗ₜ[A] m) :=
      Ideal.annihilator_span_singleton_eq_torsionOf _
    _ = Ideal.map (algebraMap A B) (Ideal.torsionOf A M m) :=
      (ann_extension_eq_ann_baseChange_elem (R := A) (S := B) (M := M) m).symm
    _ = _ := congrArg (Ideal.map (algebraMap A B))
      (Ideal.annihilator_span_singleton_eq_torsionOf m).symm
  have hrad :
      (annihilatorOfElem_semiring (R := B) n).radical = IsLocalRing.maximalIdeal B := by
    rw [hAnn]
    exact radical_map_eq_of_radical_eq φ hmrad
      (radical_map_stalkMap_maximalIdeal_eq_of_mem_genericPoints_fiber f x hgeneric)
  show IsWeaklyAssociatedPrime B N (IsLocalRing.maximalIdeal B)
  simpa [IsWeaklyAssociatedPrime, WeaklyAssociated, annihilatorOfElem_semiring] using
    (weaklyAssociated_maximalIdeal_iff_exists_radical_eq (S := B) (N := N)).mpr ⟨n, hrad⟩

end AlgebraicGeometry
