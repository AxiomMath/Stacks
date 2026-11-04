module

public import StacksFrontier.RingTheory.Cech.FamilySystemLeg
public import StacksFrontier.RingTheory.Cech.IdealCechZeroLocus

/-!
# When the transitions of a family system diagram are quasi-isomorphisms

Let `R` be a presheaf of commutative rings and `F` a family system on it. Over an object `V` the
transitions of the diagram `Stacks.CechFamilySystem.cechDiagram F V` are **not**
quasi-isomorphisms in general: the distinguished families over `V` need not span one ideal of
`R(V)`, and the extended alternating Čech complex of a family depends on the family through the
closed subset it cuts out.

This file isolates the hypothesis under which they are. A nonempty finite set `T` of
distinguished families **all spanning the same ideal `I` of `R(V)`** has a product family cutting
out `V(I)` (`Stacks.CechFamilySystem.zeroLocus_span_range_fam_of_span_eq`), so any two such sets
have product families with the same zero locus and every comparison between their Čech complexes
compatible with the augmentations is a quasi-isomorphism
(`Stacks.IdealCechComplex.quasiIso_of_comp_augmentation_of_zeroLocus_eq`).

Two consequences are recorded: a transition `S ≤ T` of the diagram is a quasi-isomorphism as soon
as the families of `T` all span one ideal
(`Stacks.CechFamilySystem.quasiIso_cechDiagram_map_of_span_eq`),
and the reindexing `Č(x) ⟶ Č(fam {x})` of `FamilySystemLeg.lean` is a quasi-isomorphism with no
hypothesis at all (`Stacks.CechFamilySystem.quasiIso_singleLeg`), the product family of a
singleton index being the family itself up to a bijection of index sets.

This is [Stacks, Tag 099D]'s `Stacks.PairSite.quasiIso_cechDiagram_map`, where the hypothesis is
built into the index — there every family of every index spans the one fixed ideal of the pair.
Over a site that cannot be asked of a condition stable under restriction, so the hypothesis is
carried as an argument and discharged, on a covering, by the consumer.

## Main results

* `Stacks.CechFamilySystem.zeroLocus_range_fam_of_span_eq`: **the product family of a finite set
  of families all spanning `I` cuts out `V(I)`.**
* `Stacks.CechFamilySystem.quasiIso_cechDiagram_map_of_span_eq`: **a transition of the diagram is
  a quasi-isomorphism when the families of its target all span one ideal.**
* `Stacks.CechFamilySystem.quasiIso_singleLeg`: **the reindexing onto the product family of a
  singleton index is a quasi-isomorphism.**

## References

* [Stacks Project, Tag 099D](https://stacks.math.columbia.edu/tag/099D)
* [Stacks Project, Tag 099E](https://stacks.math.columbia.edu/tag/099E)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace Stacks.CechFamilySystem

open FamilySystem

variable {C : Type u} [Category.{u} C] {R : Cᵒᵖ ⥤ CommRingCat.{u}} {F : FamilySystem R}

/-! ### The zero locus of the product family -/

variable {V : Cᵒᵖ}

/-- **Every value of the product family of `S` lies in `I`**, when every family of `S` spans `I`:
the value is a product with at least one factor in `I`, `S` being nonempty. -/
theorem famFun_mem_of_span_eq {S : F.GenSet V} {I : Ideal (R.obj V)}
    (h : ∀ x ∈ S.carrier, Ideal.span (Set.range x.elts) = I) (c : Idx S) : famFun S c ∈ I := by
  obtain ⟨x, hx⟩ := S.nonempty'
  obtain ⟨d, hd⟩ := Finset.dvd_prod_of_mem (fun z : {y // y ∈ S.carrier} => z.1.elts (c z))
    (Finset.mem_univ (⟨x, hx⟩ : {y // y ∈ S.carrier}))
  rw [famFun, hd]
  refine Ideal.mul_mem_right _ _ ?_
  rw [← h x hx]
  exact Ideal.subset_span ⟨c ⟨x, hx⟩, rfl⟩

/-- A prime containing every value of the product family of `S` contains one of the families of
`S` entirely: were every family of `S` to have an element outside the prime, choosing one such
element from each family would give a value of the product family outside the prime. -/
theorem exists_forall_elts_mem_of_famFun_mem {S : F.GenSet V} {p : Ideal (R.obj V)}
    (hp : p.IsPrime) (h : ∀ c : Idx S, famFun S c ∈ p) :
    ∃ x ∈ S.carrier, ∀ i : Fin x.arity, x.elts i ∈ p := by
  by_contra hcon
  simp only [not_exists, not_and, not_forall] at hcon
  have hchoice : ∀ z : {y // y ∈ S.carrier}, ∃ i : Fin z.1.arity, z.1.elts i ∉ p :=
    fun z => hcon z.1 z.2
  obtain ⟨c, hc⟩ := Classical.axiomOfChoice hchoice
  have hmem : ∏ z : {y // y ∈ S.carrier}, (z : F.Gen V).elts (c z) ∈ p := h c
  obtain ⟨z, -, hz⟩ := (Ideal.IsPrime.prod_mem_iff (hp := hp)).1 hmem
  exact hc z hz

/-- **The product family of `S` cuts out the zero locus of `I`**, when every family of `S` spans
`I`. Its values lie in `I`, which gives one inclusion; for the other, a prime containing every
value of the product family contains one of the families of `S` entirely, hence contains `I`. -/
theorem zeroLocus_range_fam_of_span_eq {S : F.GenSet V} {I : Ideal (R.obj V)}
    (h : ∀ x ∈ S.carrier, Ideal.span (Set.range x.elts) = I) :
    PrimeSpectrum.zeroLocus (Set.range (fam S)) =
      PrimeSpectrum.zeroLocus ((I : Set (R.obj V))) := by
  refine le_antisymm ?_ (PrimeSpectrum.zeroLocus_anti_mono ?_)
  · intro p hp
    rw [PrimeSpectrum.mem_zeroLocus, range_fam_eq, Set.range_subset_iff] at hp
    obtain ⟨x, hxS, hx⟩ := exists_forall_elts_mem_of_famFun_mem p.isPrime hp
    rw [PrimeSpectrum.mem_zeroLocus]
    intro a ha
    rw [← h x hxS] at ha
    exact Ideal.span_le.2 (by rintro b ⟨i, rfl⟩; exact hx i) ha
  · rw [range_fam_eq]
    rintro a ⟨c, rfl⟩
    exact famFun_mem_of_span_eq h c

/-- **The ideal generated by the product family of `S` cuts out the zero locus of `I`.** -/
theorem zeroLocus_span_range_fam_of_span_eq {S : F.GenSet V} {I : Ideal (R.obj V)}
    (h : ∀ x ∈ S.carrier, Ideal.span (Set.range x.elts) = I) :
    PrimeSpectrum.zeroLocus ((Ideal.span (Set.range (fam S)) : Ideal (R.obj V)) :
        Set (R.obj V)) =
      PrimeSpectrum.zeroLocus ((I : Set (R.obj V))) := by
  rw [PrimeSpectrum.zeroLocus_span, zeroLocus_range_fam_of_span_eq h]

/-- **Two indices whose families all span the same ideal have product families with the same zero
locus.** -/
theorem zeroLocus_span_range_fam_eq_of_span_eq {S T : F.GenSet V} {I : Ideal (R.obj V)}
    (hS : ∀ x ∈ S.carrier, Ideal.span (Set.range x.elts) = I)
    (hT : ∀ x ∈ T.carrier, Ideal.span (Set.range x.elts) = I) :
    PrimeSpectrum.zeroLocus ((Ideal.span (Set.range (fam S)) : Ideal (R.obj V)) :
        Set (R.obj V)) =
      PrimeSpectrum.zeroLocus ((Ideal.span (Set.range (fam T)) : Ideal (R.obj V)) :
        Set (R.obj V)) := by
  rw [zeroLocus_span_range_fam_of_span_eq hS, zeroLocus_span_range_fam_of_span_eq hT]

/-! ### The transitions of the diagram -/

/-- In degree zero every transition of the diagram respects the identification of the degree-zero
Čech term with the ring of sections. -/
theorem cechZeroIso_cechDiagram_map {S T : F.GenSet V} (h : S ⟶ T) :
    ((cechDiagram F V).map h).f 0 ≫
        (LocalCohomology.cechZeroIso (fam T) (ModuleCat.of (R.obj V) (R.obj V))).hom =
      (LocalCohomology.cechZeroIso (fam S) (ModuleCat.of (R.obj V) (R.obj V))).hom :=
  PairSite.cechZeroIso_cechGenMap (fam S) (fam T) _ _ (ModuleCat.of (R.obj V) (R.obj V))

/-- A map between Čech complexes of two families with the same zero locus, compatible with the
degree-zero identifications, is a quasi-isomorphism. -/
private theorem quasiIso_of_cechZeroIso_comp {r s : ℕ} {f : Fin r → R.obj V} {g : Fin s → R.obj V}
    (hfg : PrimeSpectrum.zeroLocus ((Ideal.span (Set.range f) : Ideal (R.obj V)) :
        Set (R.obj V)) =
      PrimeSpectrum.zeroLocus ((Ideal.span (Set.range g) : Ideal (R.obj V)) : Set (R.obj V)))
    (u : Cech.cechComplex f (R.obj V) ⟶ Cech.cechComplex g (R.obj V))
    (hu : u.f 0 ≫ (LocalCohomology.cechZeroIso g (ModuleCat.of (R.obj V) (R.obj V))).hom =
      (LocalCohomology.cechZeroIso f (ModuleCat.of (R.obj V) (R.obj V))).hom) :
    QuasiIso u := by
  rw [← HomologicalComplex.quasiIso_extendMap_iff _ ComplexShape.embeddingUpNat]
  exact IdealCechComplex.quasiIso_of_comp_augmentation_of_zeroLocus_eq f g
    (ModuleCat.of (R.obj V) (R.obj V)) hfg _
    (IdealCechComplex.extendMap_comp_augmentation f g (ModuleCat.of (R.obj V) (R.obj V)) u hu)

/-- **A transition of the diagram whose source and target consist of families all spanning one
ideal is a quasi-isomorphism.** -/
theorem quasiIso_cechDiagram_map_of_span_eq {S T : F.GenSet V} (h : S ⟶ T)
    {I : Ideal (R.obj V)} (hS : ∀ x ∈ S.carrier, Ideal.span (Set.range x.elts) = I)
    (hT : ∀ x ∈ T.carrier, Ideal.span (Set.range x.elts) = I) :
    QuasiIso ((cechDiagram F V).map h) :=
  quasiIso_of_cechZeroIso_comp (zeroLocus_span_range_fam_eq_of_span_eq hS hT) _
    (cechZeroIso_cechDiagram_map h)

/-- **A transition of the diagram out of a singleton index is a quasi-isomorphism** as soon as
every family of the target spans the ideal the single family of the source spans. -/
theorem quasiIso_cechDiagram_map_single {x : F.Gen V} {T : F.GenSet V} (h : single x ⟶ T)
    (hT : ∀ y ∈ T.carrier, Ideal.span (Set.range y.elts) = Ideal.span (Set.range x.elts)) :
    QuasiIso ((cechDiagram F V).map h) :=
  quasiIso_cechDiagram_map_of_span_eq h
    (fun y hy => by rw [Finset.mem_singleton.1 hy]) hT

/-! ### The reindexing onto the product family of a singleton index -/

/-- **The product family of a singleton index has the same values as the family itself.** The
reindexing `Stacks.CechFamilySystem.singleIdx` is a bijection, being a composite of two
equivalences. -/
theorem range_fam_single (x : F.Gen V) : Set.range (fam (single x)) = Set.range x.elts := by
  have hbij : Function.Surjective (singleIdx x) :=
    ((idxSingleEquiv x).surjective.comp (idxEquiv (single x)).symm.surjective)
  refine Set.Subset.antisymm ?_ ?_
  · rintro a ⟨k, rfl⟩
    exact ⟨singleIdx x k, (fam_single_apply x k).symm⟩
  · rintro a ⟨i, rfl⟩
    obtain ⟨k, rfl⟩ := hbij i
    exact ⟨k, fam_single_apply x k⟩

/-- **The reindexing `Č(x) ⟶ Č(fam {x})` is a quasi-isomorphism**, with no hypothesis: the two
families have the same values, hence the same zero locus. -/
theorem quasiIso_singleLeg (x : F.Gen V) : QuasiIso (singleLeg x) := by
  refine quasiIso_of_cechZeroIso_comp ?_ _
    (PairSite.cechZeroIso_cechGenMap x.elts (fam (single x)) (singleIdx x)
      (exists_dvd_fam_single x) (ModuleCat.of (R.obj V) (R.obj V)))
  rw [range_fam_single]

end Stacks.CechFamilySystem

end
