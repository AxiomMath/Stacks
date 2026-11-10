module

public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.BaseChangeSupport
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.Effective
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.Relative
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.Specialization
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.SpecializationSupport
public import StacksFrontier.AlgebraicGeometry.Divisors.Meromorphic.WeilDivisors
import StacksFrontier.AlgebraicGeometry.Divisors.RelativeAssassin.TensorPullbackWeakAssassin
public import StacksFrontier.AlgebraicGeometry.Properties.DiscreteValuation
public import StacksCore.Tactic.StacksAttribute

/-!
# The support of an effective relative cycle is closed

Let `S` be locally Noetherian, let `f : X ⟶ S` be locally of finite type and let `α` be a
relative `r`-cycle on `X/S`. If `α` is effective then `Supp(α)` is closed in `X`.

The proof identifies `Supp(α)` with a locally finite union of closed sets. For a point `s` of
`S` the *generic support closure* of `α` at `s` is the union of the closures in `X` of the
images of the points of the fibre `X_s` carrying a nonzero coefficient; it is closed, being a
locally finite union of closures of points. Two inclusions show that `Supp(α)` is the union of
these sets as `s` ranges over the generic points of `S`.

One inclusion is stability of `Supp(α)` under specialization. A specialization `x' ⤳ x` in `X`
is the image of the generic-to-closed specialization on the spectrum of a discrete valuation
ring `R`, and `X ×_S Spec R ⟶ Spec R` carries a section through which the two points are seen.
The valuative condition identifies the cycle of the base change on the special fibre as the
specialization of its cycle on the generic fibre, and — effectivity forbidding cancellation —
the support of a specialized effective cycle contains every specialization of a point of the
support. Compatibility of supports with base change transports the conclusion back to `X`.

The other inclusion says that a point of `Supp(α)` lies in the generic support closure at any
point of `S` generalizing its image. Again base change to a discrete valuation ring, this time
mapping the generic point to the chosen generalization, reduces the claim to the statement that
the support of a specialized cycle lies in the closure of the image of the support of the cycle
it specializes.

Finally the generic support closures at the generic points of `S` form a locally finite family,
because each lies over the corresponding irreducible component of `S` and the irreducible
components of a locally Noetherian scheme are locally finite.

## Main results

* `Stacks.Chow.genericSupportClosure` — the closure in `X` of the image of the support of the
  cycle on a fibre.
* `Stacks.Chow.mem_supportOfFamily_of_specializes` — a specialization of a point of the support
  of a relative cycle stays in the support when the fibre cycle through the point is effective.
* `Stacks.Chow.stableUnderSpecialization_supportOfFamily` — the support of an effective relative
  cycle is stable under specialization.
* `Stacks.Chow.supportOfFamily_eq_iUnion_genericSupportClosure` — the support is the union of
  the generic support closures at the generic points of the base.
* `Stacks.Chow.isClosed_supportOfFamily_of_isEffectiveFamily` — the support of an effective
  relative `r`-cycle is closed.

## Implementation notes

The source states the lemma for integers `r, e ≥ 0`; the integer `e` does not occur in the
statement and only the relative dimension `r` is retained.

## References

* [Stacks Project, Tag 0H5W](https://stacks.math.columbia.edu/tag/0H5W)
* [Stacks Project, Tag 0H4V](https://stacks.math.columbia.edu/tag/0H4V)
* [Stacks Project, Tag 054F](https://stacks.math.columbia.edu/tag/054F)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

variable {X S : Scheme.{u}}

/-! ### Membership in the support, read on a fibre -/

/-- A point of the scheme-theoretic fibre over `s` lies over `s`. -/
alias fiberι_apply_base := AlgebraicGeometry.apply_fiberι

/-- A point of a fibre lies in the support of a family of cycles, read in the total space,
exactly when it lies in the support of the cycle on that fibre. -/
theorem fiberι_mem_supportOfFamily_iff (f : X ⟶ S) [LocallyOfFiniteType f] (r : ℕ)
    (α : FamilyOfCycles f r) (s : S) (y : f.fiber s) :
    f.fiberι s y ∈ supportOfFamily f α ↔
      y ∈ tsupport (α s : AlgebraicCycle (f.fiber s) ℤ) := by
  rw [mem_supportOfFamily]
  refine ⟨?_, fun hy ↦ ⟨s, y, hy, rfl⟩⟩
  rintro ⟨t, z, hz, he⟩
  have ht : s = t := by
    rw [← fiberι_apply_base f s y, ← he, fiberι_apply_base f t z]
  subst ht
  rwa [(f.fiberι s).isEmbedding.injective he] at hz

/-- The image in the total space of the support of the cycle on the fibre over `s` consists of
the points of the support of the family which lie over `s`. -/
theorem mem_image_tsupport_iff (f : X ⟶ S) [LocallyOfFiniteType f] (r : ℕ)
    (α : FamilyOfCycles f r) (s : S) (x : X) :
    x ∈ f.fiberι s '' tsupport (α s : AlgebraicCycle (f.fiber s) ℤ) ↔
      x ∈ supportOfFamily f α ∧ f x = s := by
  refine ⟨?_, ?_⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨(fiberι_mem_supportOfFamily_iff f r α s y).mpr hy, fiberι_apply_base f s y⟩
  · rintro ⟨hx, hs⟩
    obtain ⟨y, rfl⟩ := (f.range_fiberι s).symm.subset hs
    exact ⟨y, (fiberι_mem_supportOfFamily_iff f r α s y).mp hx, rfl⟩

/-! ### The generic support closure -/

/- `locallyFinite_singleton_image_of_isSpectralMap` stood here, the same statement with the
same proof as `locallyFinite_singleton_image` in
`StacksFrontier/AlgebraicGeometry/Chow/RelativeCycles/SpecializationCycle.lean:128`, which this
module imports. That one was `private`, which is why the copy existed; it is now public and
the uses below name it. -/

/-- The closure in `X` of the image of the support of the cycle on the fibre over `s`: the union
of the closures of the images of the points of that fibre carrying a nonzero coefficient. -/
def genericSupportClosure (f : X ⟶ S) [LocallyOfFiniteType f] (r : ℕ) (α : FamilyOfCycles f r)
    (s : S) : Set X :=
  ⋃ ξ : Function.support (α s).1, closure ({f.fiberι s ξ.1} : Set X)

/-- The generic support closure at `s` is the closure of the image of the support of the cycle
on the fibre over `s`. -/
theorem closure_image_tsupport_eq_genericSupportClosure (f : X ⟶ S) [LocallyOfFiniteType f]
    (r : ℕ) (α : FamilyOfCycles f r) (s : S) :
    closure (f.fiberι s '' tsupport (α s : AlgebraicCycle (f.fiber s) ℤ)) =
      genericSupportClosure f r α s := by
  classical
  have hlf : LocallyFinite fun ξ : Function.support (α s).1 ↦
      ({f.fiberι s ξ.1} : Set X) :=
    locallyFinite_singleton_image _ (f.fiberι s).isSpectralMap (α s).1
  have hcoeff : Function.support (α s).1 =
      ⋃ ξ : Function.support (α s).1, ({ξ.1} : Set (f.fiber s)) := by
    ext z
    simp only [Set.mem_iUnion, Set.mem_singleton_iff]
    exact ⟨fun hz ↦ ⟨⟨z, hz⟩, rfl⟩, by rintro ⟨ξ, rfl⟩; exact ξ.2⟩
  have hclosure : closure (f.fiberι s '' tsupport (α s : AlgebraicCycle (f.fiber s) ℤ)) =
      closure (f.fiberι s '' Function.support (α s).1) := by
    refine le_antisymm (closure_minimal ?_ isClosed_closure)
      (closure_mono (Set.image_mono subset_closure))
    rintro z ⟨y, hy, rfl⟩
    exact image_closure_subset_closure_image (f.fiberι s).continuous ⟨y, hy, rfl⟩
  have himage : f.fiberι s '' (⋃ ξ : Function.support (α s).1, ({ξ.1} : Set (f.fiber s))) =
      ⋃ ξ : Function.support (α s).1, ({f.fiberι s ξ.1} : Set X) := by
    ext z
    simp only [Set.mem_image, Set.mem_iUnion, Set.mem_singleton_iff]
    exact ⟨by rintro ⟨y, ⟨ξ, rfl⟩, rfl⟩; exact ⟨ξ, rfl⟩,
      by rintro ⟨ξ, rfl⟩; exact ⟨ξ.1, ⟨ξ, rfl⟩, rfl⟩⟩
  rw [hclosure, hcoeff, himage, hlf.closure_iUnion]
  rfl

/-- The generic support closure is closed: it is a locally finite union of closures of points. -/
theorem isClosed_genericSupportClosure (f : X ⟶ S) [LocallyOfFiniteType f] (r : ℕ)
    (α : FamilyOfCycles f r) (s : S) : IsClosed (genericSupportClosure f r α s) := by
  rw [← closure_image_tsupport_eq_genericSupportClosure]
  exact isClosed_closure

/-- The generic support closure at `s` lies over the closure of `s`. -/
theorem genericSupportClosure_subset_preimage_closure (f : X ⟶ S) [LocallyOfFiniteType f]
    (r : ℕ) (α : FamilyOfCycles f r) (s : S) :
    genericSupportClosure f r α s ⊆ f ⁻¹' closure ({s} : Set S) := by
  refine Set.iUnion_subset fun ξ ↦ closure_minimal ?_ (isClosed_closure.preimage f.continuous)
  rintro x rfl
  change f (f.fiberι s ξ.1) ∈ closure ({s} : Set S)
  rw [fiberι_apply_base f s ξ.1]
  exact subset_closure rfl

/-- Over the generic points of a locally Noetherian base the generic support closures form a
locally finite family: each lies over the corresponding irreducible component of the base, and
the irreducible components of a locally Noetherian scheme are locally finite. -/
theorem locallyFinite_genericSupportClosure (f : X ⟶ S) [LocallyOfFiniteType f]
    [IsLocallyNoetherian S] (r : ℕ) (α : FamilyOfCycles f r) :
    LocallyFinite fun η : genericPoints S ↦ genericSupportClosure f r α η.1 := by
  have hcomp : LocallyFinite fun C : irreducibleComponents S ↦ (C : Set S) := by
    simpa using AlgebraicGeometry.locallyFinite_irreducibleComponents_image (𝟙 S)
  have hgen := hcomp.comp_injective genericPoints.component_injective
  change LocallyFinite fun η : genericPoints S ↦ closure ({η.1} : Set S) at hgen
  exact (hgen.preimage_continuous f.continuous).subset fun η ↦
    genericSupportClosure_subset_preimage_closure f r α η.1

/-! ### The two inclusions -/

/-- Over a discrete valuation ring base the support of a family of cycles satisfying the
valuative condition, and whose cycle on the generic fibre is effective, is stable under the
generic-to-closed specialization. -/
private theorem mem_supportOfFamily_of_specializes_closedPoint {R : Type u} [CommRing R]
    [IsDomain R] [IsDiscreteValuationRing R] {Y : Scheme.{u}} (p : Y ⟶ Spec (.of R))
    [LocallyOfFiniteType p] (r : ℕ) (β : FamilyOfCycles p r)
    (hsp : specializationCycle p r (β (genericPoint (Spec (.of R)))) =
      β (IsLocalRing.closedPoint R))
    (hβ : IsEffectiveCycle (β (genericPoint (Spec (.of R))) :
      AlgebraicCycle (p.fiber (genericPoint (Spec (.of R)))) ℤ)) {a b : Y}
    (ha : p a = genericPoint (Spec (.of R))) (hb : p b = IsLocalRing.closedPoint R)
    (hab : a ⤳ b) (haβ : a ∈ supportOfFamily p β) : b ∈ supportOfFamily p β := by
  obtain ⟨y, rfl⟩ := (p.range_fiberι (genericPoint (Spec (.of R)))).symm.subset ha
  obtain ⟨z, rfl⟩ := (p.range_fiberι (IsLocalRing.closedPoint R)).symm.subset hb
  have hy := (fiberι_mem_supportOfFamily_iff p r β _ y).mp haβ
  have hlfs : LocallyFiniteSupport ⇑(β (genericPoint (Spec (.of R))) :
      AlgebraicCycle (p.fiber (genericPoint (Spec (.of R)))) ℤ) :=
    Function.locallyFinsupp.locallyFiniteSupport _
  rw [tsupport_eq_biUnion_closure_singleton hlfs] at hy
  obtain ⟨ξ, hξ, hξy⟩ := Set.mem_iUnion₂.mp hy
  refine (fiberι_mem_supportOfFamily_iff p r β _ z).mpr ?_
  rw [← hsp]
  exact mem_tsupport_specializationCycle_of_specializes p r _ hβ
    (Function.mem_support.mp hξ) z
    (((specializes_iff_mem_closure.mpr hξy).map
      (p.fiberι (genericPoint (Spec (.of R)))).continuous).trans hab)

/-- Along a specialization `a ⤳ b` in `X`, a point of the support of a relative `r`-cycle `α`
carries `b` into the support as soon as the cycle of `α` on the fibre through `a` is effective.

The specialization is the image of the generic-to-closed specialization on the spectrum of a
discrete valuation ring `R`, and `X ×_S Spec R ⟶ Spec R` carries a section through which the
two points are seen. The cycle of the base change on the generic fibre is a base change of the
cycle of `α` on the fibre through `a`, hence effective, so no cancellation occurs when the
valuative condition specializes it to the special fibre. -/
theorem mem_supportOfFamily_of_specializes (f : X ⟶ S) [LocallyOfFiniteType f]
    [IsLocallyNoetherian S] (r : ℕ) (α : FamilyOfCycles f r) (hα : IsRelativeCycle f r α)
    {a b : X} (hab : a ⤳ b) (heff : IsEffectiveCycle (α (f a) : AlgebraicCycle (f.fiber (f a)) ℤ))
    (ha : a ∈ supportOfFamily f α) : b ∈ supportOfFamily f α := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  obtain ⟨R, _, _, _, h, hη, hs⟩ := AlgebraicGeometry.exists_dvr_morphism_of_specializes X hab
  obtain ⟨g, hgf⟩ : ∃ g : (Spec (.of R) : Scheme.{u}) ⟶ S, h ≫ f = g :=
    ⟨h ≫ f, rfl⟩
  have hcomm : h ≫ f =
      (𝟙 (Spec (.of R) : Scheme.{u}) : (Spec (.of R) : Scheme.{u}) ⟶ _) ≫ g := by
    rw [hgf, Category.id_comp]
  obtain ⟨l, hl₁, hl₂⟩ : ∃ l : (Spec (.of R) : Scheme.{u}) ⟶ (pullback f g : Scheme.{u}),
      (∀ t, pullback.fst f g (l t) = h t) ∧ ∀ t, pullback.snd f g (l t) = t := by
    refine ⟨pullback.lift h (𝟙 _) hcomm, fun t ↦ ?_, fun t ↦ ?_⟩
    · rw [← Scheme.Hom.comp_apply, pullback.lift_fst]
    · rw [← Scheme.Hom.comp_apply, pullback.lift_snd]
      rfl
  have hgη : g (genericPoint (Spec (.of R))) = f a := by
    rw [← hgf, Scheme.Hom.comp_apply, hη]
  have heff' : ∀ s : S, s = f a → IsEffectiveCycle (α s : AlgebraicCycle (f.fiber s) ℤ) := by
    rintro s rfl
    exact heff
  have hbc : IsEffectiveCycle (baseChangeFamily f g r α (genericPoint (Spec (.of R))) :
      AlgebraicCycle ((pullback.snd f g).fiber (genericPoint (Spec (.of R)))) ℤ) := by
    intro y
    rw [baseChangeFamily_apply f g r α _ y]
    exact mul_nonneg (heff' _ hgη _) (closedSubschemeCycleCoeff_nonneg _ _ _ _ _)
  have hsupp := supportOfFamily_baseChangeFamily f g r α
  have hin : l (genericPoint (Spec (.of R))) ∈
      supportOfFamily (pullback.snd f g) (baseChangeFamily f g r α) := by
    rw [hsupp]
    simp only [Set.mem_preimage, hl₁, hη]
    exact ha
  have hout := mem_supportOfFamily_of_specializes_closedPoint (pullback.snd f g) r
    (baseChangeFamily f g r α) (hα R g) hbc (hl₂ _) (hl₂ _)
    ((IsLocalRing.specializes_closedPoint _).map l.continuous) hin
  rw [hsupp, Set.mem_preimage, hl₁ (IsLocalRing.closedPoint R), hs] at hout
  exact hout

/-- The support of an effective relative `r`-cycle is stable under specialization: a
specialization in `X` is the image of the generic-to-closed specialization on the spectrum of a
discrete valuation ring, where the valuative condition applies after base change. -/
theorem stableUnderSpecialization_supportOfFamily (f : X ⟶ S) [LocallyOfFiniteType f]
    [IsLocallyNoetherian S] (r : ℕ) (α : FamilyOfCycles f r) (hα : IsRelativeCycle f r α)
    (heff : IsEffectiveFamily f r α) :
    StableUnderSpecialization (supportOfFamily f α) :=
  fun _ _ hab ha ↦ mem_supportOfFamily_of_specializes f r α hα hab (heff _) ha

/-- A point of the support of a relative `r`-cycle lies in the generic support closure at every
point of the base generalizing its image: base change to a discrete valuation ring whose generic
point maps to that generalization reduces the claim to the corresponding statement for the
specialization map. -/
theorem mem_genericSupportClosure_of_mem_supportOfFamily (f : X ⟶ S) [LocallyOfFiniteType f]
    [IsLocallyNoetherian S] (r : ℕ) (α : FamilyOfCycles f r) (hα : IsRelativeCycle f r α)
    (η : S) {x : X} (hη : η ⤳ f x) (hx : x ∈ supportOfFamily f α) :
    x ∈ genericSupportClosure f r α η := by
  rw [← closure_image_tsupport_eq_genericSupportClosure]
  obtain ⟨R, _, _, _, g, hgη, hgs⟩ := AlgebraicGeometry.exists_dvr_morphism_of_specializes S hη
  have hsupp := supportOfFamily_baseChangeFamily f g r α
  obtain ⟨z, hzx, hzs⟩ := Scheme.Pullback.exists_preimage_pullback (f := f) (g := g) x
    (IsLocalRing.closedPoint R : Spec (.of R)) hgs.symm
  obtain ⟨y, hyz⟩ :=
    ((pullback.snd f g).range_fiberι (IsLocalRing.closedPoint R)).symm.subset hzs
  have hy : y ∈ tsupport (baseChangeFamily f g r α (IsLocalRing.closedPoint R) :
      AlgebraicCycle ((pullback.snd f g).fiber (IsLocalRing.closedPoint R)) ℤ) := by
    refine (fiberι_mem_supportOfFamily_iff (pullback.snd f g) r _ _ y).mp ?_
    rw [hyz, hsupp, Set.mem_preimage, hzx]
    exact hx
  rw [← hα R g] at hy
  have hycl := fiberι_mem_closure_image_support_of_mem_tsupport_specializationCycle
    (pullback.snd f g) r (baseChangeFamily f g r α (genericPoint (Spec (.of R)))) hy
  have himage := image_closure_subset_closure_image (pullback.fst f g).continuous ⟨_, hycl, rfl⟩
  rw [hyz, hzx] at himage
  refine closure_mono (t := f.fiberι η '' tsupport (α η : AlgebraicCycle (f.fiber η) ℤ)) ?_ himage
  rintro t ⟨w, ⟨v, hv, rfl⟩, rfl⟩
  refine (mem_image_tsupport_iff f r α η _).mpr ⟨?_, ?_⟩
  · have hv' : (pullback.snd f g).fiberι (genericPoint (Spec (.of R))) v ∈
        supportOfFamily (pullback.snd f g) (baseChangeFamily f g r α) :=
      (fiberι_mem_supportOfFamily_iff (pullback.snd f g) r _ _ v).mpr (subset_closure hv)
    rw [hsupp] at hv'
    exact hv'
  · rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply,
      fiberι_apply_base, hgη]

/-! ### The support of an effective relative cycle -/

/-- The support of an effective relative `r`-cycle is the union, over the generic points of the
base, of the generic support closures: one inclusion holds because a point of the support lies
in the generic support closure at the generic point of an irreducible component of the base
containing its image, and the other because the support is stable under specialization. -/
theorem supportOfFamily_eq_iUnion_genericSupportClosure (f : X ⟶ S) [LocallyOfFiniteType f]
    [IsLocallyNoetherian S] (r : ℕ) (α : FamilyOfCycles f r) (hα : IsRelativeCycle f r α)
    (heff : IsEffectiveFamily f r α) :
    supportOfFamily f α = ⋃ η : genericPoints S, genericSupportClosure f r α η.1 := by
  refine Set.Subset.antisymm (fun x hx ↦ ?_) (fun x hx ↦ ?_)
  · have hC : irreducibleComponent (f x) ∈ irreducibleComponents S :=
      irreducibleComponent_mem_irreducibleComponents (f x)
    have hη : (genericPoints.ofComponent ⟨irreducibleComponent (f x), hC⟩).1 ⤳ f x :=
      (genericPoints.isGenericPoint_ofComponent
        ⟨irreducibleComponent (f x), hC⟩).specializes mem_irreducibleComponent
    exact Set.mem_iUnion.mpr ⟨genericPoints.ofComponent ⟨irreducibleComponent (f x), hC⟩,
      mem_genericSupportClosure_of_mem_supportOfFamily f r α hα _ hη hx⟩
  · obtain ⟨η, hη⟩ := Set.mem_iUnion.mp hx
    obtain ⟨ξ, hξ⟩ := Set.mem_iUnion.mp hη
    exact stableUnderSpecialization_supportOfFamily f r α hα heff
      (specializes_iff_mem_closure.mpr hξ)
      ((fiberι_mem_supportOfFamily_iff f r α η.1 ξ.1).mpr (subset_closure ξ.2))

/-- **Stacks Project, Tag 0H5W.** Let `f : X ⟶ S` be a morphism of schemes with `S` locally
Noetherian and `f` locally of finite type, let `r ≥ 0` be an integer and let `α` be a relative
`r`-cycle on `X/S`. If `α` is effective then its support is closed in `X`. -/
@[stacks 0H5W]
theorem isClosed_supportOfFamily_of_isEffectiveFamily (f : X ⟶ S) [LocallyOfFiniteType f]
    [IsLocallyNoetherian S] (r : ℕ) (α : FamilyOfCycles f r) (hα : IsRelativeCycle f r α)
    (heff : IsEffectiveFamily f r α) : IsClosed (supportOfFamily f α) := by
  rw [supportOfFamily_eq_iUnion_genericSupportClosure f r α hα heff]
  exact (locallyFinite_genericSupportClosure f r α).isClosed_iUnion fun η ↦
    isClosed_genericSupportClosure f r α η.1

end Stacks.Chow

end
