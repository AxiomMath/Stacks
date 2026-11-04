module

public import StacksFrontier.Algebra.Homology.Embedding.ExtendMap
public import StacksFrontier.Homology.FilteredColimitQuasiIso
public import StacksFrontier.RingTheory.Cech.CechColimitDatum
public import StacksFrontier.RingTheory.Cech.GeneralReindex
public import StacksFrontier.RingTheory.Cech.GeneralReindexBaseChange
public import StacksFrontier.RingTheory.Cech.IdealCechZeroLocus
public import StacksFrontier.RingTheory.Cech.PairGenSet
public import StacksFrontier.RingTheory.Cech.PresentedCechDatum
public import StacksFrontier.RingTheory.Cech.RingBaseChangeDerived

/-!
# The complex of pair-modules of [Stacks, Tag 099D], and the Čech datum on presented pairs

[Stacks, Tag 099D] asks for one complex `𝒦•` of presheaves of modules on the category of
*presented pairs* `Stacks.PairSite.Pair`, with an augmentation onto the structure presheaf in
degree zero, whose complexes of sections satisfy the two derived-category conditions (c) and (d)
of the tag at every presented pair. That package is
`Stacks.PairSite.PresentedCechDatum`; this file constructs a term of it.

The complex is **not** the Čech complex of a chosen generating family — no such choice is
functorial (`Stacks.FunctorialCechFamily.isEmpty_functorialGenerators`). It is the **filtered
colimit of the extended alternating Čech complexes over all finite sets of finite generating
families of the pair's ideal**, the transition maps being the comparison maps of
`Cech.cechGenMap` from the product family of a set to the product family of a larger one. At a
presented pair the index system `Stacks.PairSite.PairGenSet` is filtered with no hypothesis, and
every transition is a quasi-isomorphism because the two product families cut out the same closed
subset of the spectrum
(`Stacks.IdealCechComplex.quasiIso_of_comp_augmentation_of_zeroLocus_eq`). So the colimit is,
at each pair, quasi-isomorphic to the Čech complex of any one family, compatibly with the
augmentations — which is condition (d) — while the restriction maps of the resulting presheaf of
modules compose strictly, which is conditions (a) and (b).

Functoriality in a morphism of pairs `f : P ⟶ Q` is `Stacks.PairSite.cechTransport`: the
change-of-rings map of the Čech complex along the underlying ring map, followed by the
comparison from the image family to the product family of the transported index. Condition (c)
follows, because the change-of-rings half is already known to satisfy it
(`Stacks.CechRingBaseChange.isIso_derivedBaseChange_extendedComplexMap`) and the other half is a
quasi-isomorphism.

## Main definitions

* `Stacks.PairSite.cechDiagram` — the filtered diagram of Čech complexes at a presented pair.
* `Stacks.PairSite.cechTransport` — the comparison along a morphism of pairs.
* `Stacks.PairSite.cechTermPair`, `Stacks.PairSite.cechDiffPair`,
  `Stacks.PairSite.cechComplexPairNat`, `Stacks.PairSite.cechComplexPair` — the complex of
  pair-modules, degreewise the colimit of the diagram.
* `Stacks.PairSite.cechAugZero`, `Stacks.PairSite.cechAugmentationPair` — its augmentation onto
  the structure presheaf placed in degree zero.
* `Stacks.PairSite.cechSectionsIota` — the comparison from the extended Čech complex of one
  product family into the sections of the complex of pair-modules.

## Main results

* `Stacks.PairSite.quasiIso_cechDiagram_map` — every transition of the diagram is a
  quasi-isomorphism.
* `Stacks.PairSite.quasiIso_cechSectionsIota` and
  `Stacks.PairSite.cechSectionsIota_comp_augmentation` — the sections at a pair are the Čech
  complex of any one product family, over the pair's ring.
* `Stacks.PairSite.exists_cech_iso_sectionsInt` — condition (d) at a presented pair.
* `Stacks.PairSite.isIso_derivedBaseChange_sectionsIntMap` — condition (c) at presented pairs.
* `Stacks.PairSite.exists_presentedCechDatum` — **there is a Čech datum on the category of
  presented pairs.**

## Implementation notes

The value of a presheaf of modules on pairs at `P` is an object of
`ModuleCat ↑(structureRings.obj P.ix)`, while every Čech construction produces an object of
`ModuleCat P.ring`. The two categories are definitionally equal but not syntactically so, and
`rw`, `simp` and instance search all work below the transparency at which they become equal.
Everything below therefore names the `ModuleCat P.ring` spelling —
`Stacks.PairSite.transportDesc`, `Stacks.PairSite.diffDesc`, `Stacks.PairSite.augDesc`,
`Stacks.PairSite.sectionsNat`, `Stacks.PairSite.sectionsInt`,
`Stacks.PairSite.sectionsIntMap`, `Stacks.PairSite.sectionsIntAugmentation` — and the bridges to
the `structureRings` spelling (`Stacks.PairSite.sectionsInt_eq`,
`Stacks.PairSite.sectionsIntMap_eq`, `Stacks.PairSite.sectionsIntAugmentation_eq`) are `rfl`.
In the mixed region the proofs are built from `Eq.trans` and `congrArg` rather than from `rw`,
which refuses to rewrite there.

No `@[stacks 099D]` attribute is attached: the tag quantifies over *all* pairs, and a datum on
presented pairs alone proves no part of it; the passage to all pairs is
`Stacks.PairSite.exists_functorialCechData`.

## References

* [Stacks Project, Tag 099D](https://stacks.math.columbia.edu/tag/099D)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.PairSite

open Stacks.GenFamily

/-- Evaluation at a pair is additive. This is `PresheafOfModules.evaluation`'s own instance,
restated with the target category written as `ModuleCat P.ring` rather than as
`ModuleCat ↑(structureRings.obj P.ix)`: the two are the same category, but instance search
does not unfold `Stacks.PairSite.structureRings` to see it. -/
instance instAdditiveEvaluation (P : Pair.{u}) : (PairModule.evaluation.{u} P).Additive :=
  inferInstanceAs ((PresheafOfModules.evaluation.{u} structureRings.{u} P.ix).Additive)

/-- Evaluation at a pair preserves zero morphisms. -/
instance instPreservesZeroMorphismsEvaluation (P : Pair.{u}) :
    (PairModule.evaluation.{u} P).PreservesZeroMorphisms :=
  Functor.preservesZeroMorphisms_of_additive _

/-- **In degree zero the comparison map respects the identification with the module.** -/
theorem cechZeroIso_cechGenMap {R : Type u} [CommRing R] {r s : ℕ} (f : Fin r → R)
    (g : Fin s → R) (α : Fin s → Fin r) (hα : ∀ j : Fin s, ∃ n : ℕ, f (α j) ∣ g j ^ n)
    (M : ModuleCat.{u} R) :
    (Cech.cechGenMap f g α hα (M : Type u)).f 0 ≫ (LocalCohomology.cechZeroIso g M).hom =
      (LocalCohomology.cechZeroIso f M).hom := by
  refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
  show LocalCohomology.cechTermZeroEquiv g M (Cech.genTerm f g α hα (M : Type u) 0 x) =
    LocalCohomology.cechTermZeroEquiv f M x
  have key : (LocalCohomology.cechTermZeroEquiv g M).toLinearMap.comp
        (Cech.genTerm f g α hα (M : Type u) 0) =
      (LocalCohomology.cechTermZeroEquiv f M).toLinearMap := by
    refine DirectSum.linearMap_ext R fun S => LinearMap.ext fun y => ?_
    obtain rfl : S = default := Subsingleton.elim _ _
    obtain ⟨m, rfl⟩ : ∃ m, y = LocalizedModule.mkLinearMap (Cech.cechSub f ∅) M m :=
      ⟨Stacks.CechBaseChange.cechModEmptyEquiv f M y, by
        rw [← Stacks.CechBaseChange.cechModEmptyEquiv_symm_apply, LinearEquiv.symm_apply_apply]⟩
    show LocalCohomology.cechTermZeroEquiv g M (Cech.genTerm f g α hα (M : Type u) 0
        (DirectSum.lof R (ExtendedAlternatingCech.Idx r 0)
          (fun U => Cech.cechMod f (M : Type u) U.1) default
          (LocalizedModule.mkLinearMap (Cech.cechSub f ∅) (M : Type u) m))) =
      LocalCohomology.cechTermZeroEquiv f M (DirectSum.lof R (ExtendedAlternatingCech.Idx r 0)
        (fun U => Cech.cechMod f (M : Type u) U.1) default
        (LocalizedModule.mkLinearMap (Cech.cechSub f ∅) (M : Type u) m))
    rw [Cech.genTerm_lof_zero, LocalCohomology.cechTermZeroEquiv_lof,
      LocalCohomology.cechTermZeroEquiv_lof, Stacks.CechBaseChange.cechModEmptyEquiv_mk,
      Stacks.CechBaseChange.cechModEmptyEquiv_mk]
  exact LinearMap.congr_fun key x

/-! ### The filtered diagram of Čech complexes at a pair -/

/-- **The filtered diagram of Čech complexes at a presented pair.** -/
def cechDiagram (P : Pair.{u}) : PairGenSet P ⥤ CochainComplex (ModuleCat.{u} P.ring) ℕ where
  obj S := Cech.cechComplex (fam S) P.ring
  map {_ _} h := Cech.cechGenMap (fam _) (fam _) (idxLe (leOfHom h))
    (exists_dvd_fam_of_le (leOfHom h)) P.ring
  map_id S := by
    have hid : ∀ j : Fin (famCard S), ∃ n : ℕ, fam S (id j) ∣ fam S j ^ n :=
      fun j => ⟨1, by rw [pow_one]; exact dvd_rfl⟩
    exact (Cech.cechGenMap_congr (fam S) (fam S) _ _ P.ring hid (idxLe_refl S)).trans
      (Cech.cechGenMap_id (fam S) P.ring hid)
  map_comp {S T U} h₁ h₂ := by
    have hαβ : ∀ k : Fin (famCard U), ∃ n : ℕ,
        fam S (idxLe (leOfHom h₁) (idxLe (leOfHom h₂) k)) ∣ fam U k ^ n := fun k =>
      ⟨1, by
        rw [pow_one]
        exact (fam_dvd_of_le (leOfHom h₁) (idxLe (leOfHom h₂) k)).trans
          (fam_dvd_of_le (leOfHom h₂) k)⟩
    exact (Cech.cechGenMap_congr (fam S) (fam U) _ _ P.ring hαβ
          (idxLe_trans (leOfHom h₁) (leOfHom h₂))).trans
      (Cech.cechGenMap_comp (fam S) (fam T) _ _ P.ring (fam U)
        (idxLe (leOfHom h₂)) _ hαβ).symm

/-- The value of the diagram at `S` is the Čech complex of the product family of `S`. -/
@[simp]
theorem cechDiagram_obj (P : Pair.{u}) (S : PairGenSet P) :
    (cechDiagram P).obj S = Cech.cechComplex (fam S) P.ring := rfl

/-- The transition of the diagram along `S ≤ T` is the comparison map `Cech.cechGenMap` from
the product family of `S` to that of `T`. -/
theorem cechDiagram_map (P : Pair.{u}) {S T : PairGenSet P} (h : S ⟶ T) :
    (cechDiagram P).map h = Cech.cechGenMap (fam S) (fam T) (idxLe (leOfHom h))
      (exists_dvd_fam_of_le (leOfHom h)) P.ring := rfl

/-- The degreewise diagram of Čech terms at a pair. -/
abbrev cechTermDiagram (P : Pair.{u}) (n : ℕ) : PairGenSet P ⥤ ModuleCat.{u} P.ring :=
  cechDiagram P ⋙ HomologicalComplex.eval _ _ n

/-! ### The transitions are quasi-isomorphisms -/

/-- In degree zero every transition of the diagram respects the identification of the degree-zero
Čech term with the pair's ring. -/
theorem cechZeroIso_cechDiagram_map (P : Pair.{u}) {S T : PairGenSet P} (h : S ⟶ T) :
    ((cechDiagram P).map h).f 0 ≫
        (LocalCohomology.cechZeroIso (fam T) (ModuleCat.of P.ring P.ring)).hom =
      (LocalCohomology.cechZeroIso (fam S) (ModuleCat.of P.ring P.ring)).hom :=
  cechZeroIso_cechGenMap (fam S) (fam T) _ _ (ModuleCat.of P.ring P.ring)

/-- **Every transition of the diagram is a quasi-isomorphism.** -/
theorem quasiIso_cechDiagram_map (P : Pair.{u}) {S T : PairGenSet P} (h : S ⟶ T) :
    QuasiIso ((cechDiagram P).map h) := by
  rw [← HomologicalComplex.quasiIso_extendMap_iff _ ComplexShape.embeddingUpNat]
  exact IdealCechComplex.quasiIso_of_comp_augmentation_of_zeroLocus_eq (fam S) (fam T)
    (ModuleCat.of P.ring P.ring) zeroLocus_span_range_fam_eq _
    (IdealCechComplex.extendMap_comp_augmentation (fam S) (fam T)
      (ModuleCat.of P.ring P.ring) _ (cechZeroIso_cechDiagram_map P h))

/-! ### Change of rings in degree zero -/

section ZeroDegree

variable {A B : Type u} [CommRing A] [CommRing B] {r : ℕ}

/-- **Change of rings respects the degree-zero identification of the Čech complex.** -/
theorem cechZeroIso_complexMap (φ : A →+* B) (f : Fin r → A) :
    (CechRingBaseChange.complexMap φ f).f 0 ≫
        (ModuleCat.restrictScalars φ).map
          (LocalCohomology.cechZeroIso (CechRingBaseChange.mapFamily φ f)
            (ModuleCat.of B B)).hom =
      (LocalCohomology.cechZeroIso f (ModuleCat.of A A)).hom ≫
        ModuleCat.ofHom (CechRingBaseChange.ofRingHom φ) := by
  refine ModuleCat.hom_ext (DirectSum.linearMap_ext A fun s => LinearMap.ext fun y => ?_)
  obtain rfl : s = default := Subsingleton.elim _ _
  show LocalCohomology.cechTermZeroEquiv (CechRingBaseChange.mapFamily φ f) (ModuleCat.of B B)
      (CechRingBaseChange.termMap φ f 0 (DirectSum.lof A (ExtendedAlternatingCech.Idx r 0)
        (fun U => Cech.cechMod f (ModuleCat.of A A : Type u) U.1) default y)) =
    φ (LocalCohomology.cechTermZeroEquiv f (ModuleCat.of A A)
      (DirectSum.lof A (ExtendedAlternatingCech.Idx r 0)
        (fun U => Cech.cechMod f (ModuleCat.of A A : Type u) U.1) default y))
  rw [CechRingBaseChange.termMap_lof]
  refine (LocalCohomology.cechTermZeroEquiv_lof (M := ModuleCat.of B B)
      (CechRingBaseChange.mapFamily φ f) _).trans ?_
  refine (CechRingBaseChange.cechModEmptyEquiv_modMap φ f y).trans ?_
  exact congrArg φ (LocalCohomology.cechTermZeroEquiv_lof (M := ModuleCat.of A A) f y).symm

end ZeroDegree

/-! ### The transport along a morphism of pairs -/

/-- The divisibility datum of the transport, read against the image family: the image of the
product family of `S` divides a power of the product family of the transported index. -/
theorem exists_dvd_mapFamily_fam {P Q : Pair.{u}} (f : P ⟶ Q) (S : PairGenSet P)
    (k : Fin (famCard (pairGenMap f S))) :
    ∃ n : ℕ, CechRingBaseChange.mapFamily f.toRingHom (fam S)
        (idxMap f.toRingHom f.map_ideal S k) ∣ fam (pairGenMap f S) k ^ n :=
  exists_dvd_map_fam f.toRingHom f.map_ideal S k

/-- The divisibility datum of the composite of a transition of the diagram with the transport. -/
theorem exists_dvd_idxLe_idxMap {P Q : Pair.{u}} (f : P ⟶ Q) {S T : PairGenSet P} (hST : S ≤ T)
    (k : Fin (famCard (pairGenMap f T))) :
    ∃ n : ℕ, f.toRingHom (fam S (idxLe hST (idxMap f.toRingHom f.map_ideal T k))) ∣
      fam (pairGenMap f T) k ^ n := by
  obtain ⟨n, hn⟩ := exists_dvd_map_fam f.toRingHom f.map_ideal T k
  exact ⟨n, dvd_trans (map_dvd _ (fam_dvd_of_le hST _)) hn⟩

/-- **The comparison along a morphism of pairs.** It is the change-of-rings map of the Čech
complex along the underlying ring map, followed by the same-ring comparison from the image of
the product family of `S` to the product family of the transported index — the composite being
`Cech.cechGenRingMap` in one step. -/
def cechTransport {P Q : Pair.{u}} (f : P ⟶ Q) (S : PairGenSet P) :
    Cech.cechComplex (fam S) P.ring ⟶
      ((ModuleCat.restrictScalars f.toRingHom).mapHomologicalComplex (ComplexShape.up ℕ)).obj
        (Cech.cechComplex (fam (pairGenMap f S)) Q.ring) :=
  Cech.cechGenRingMap f.toRingHom (fam S) (fam (pairGenMap f S))
    (idxMap f.toRingHom f.map_ideal S) (exists_dvd_map_fam f.toRingHom f.map_ideal S)

/-- The degree-`p` component of the transport is the linear map `Cech.genRingTerm`. -/
theorem cechTransport_f_hom {P Q : Pair.{u}} (f : P ⟶ Q) (S : PairGenSet P) (p : ℕ) :
    ((cechTransport f S).f p).hom =
      Cech.genRingTerm f.toRingHom (fam S) (fam (pairGenMap f S))
        (idxMap f.toRingHom f.map_ideal S) (exists_dvd_map_fam f.toRingHom f.map_ideal S) p :=
  rfl

/-- **The transport factors through the change of rings.** -/
theorem cechTransport_eq {P Q : Pair.{u}} (f : P ⟶ Q) (S : PairGenSet P) :
    cechTransport f S =
      CechRingBaseChange.complexMap f.toRingHom (fam S) ≫
        ((ModuleCat.restrictScalars f.toRingHom).mapHomologicalComplex (ComplexShape.up ℕ)).map
          (Cech.cechGenMap (CechRingBaseChange.mapFamily f.toRingHom (fam S))
            (fam (pairGenMap f S)) (idxMap f.toRingHom f.map_ideal S)
            (exists_dvd_mapFamily_fam f S) Q.ring) :=
  HomologicalComplex.hom_ext _ _ fun _ => ModuleCat.hom_ext rfl

/-- **The transport commutes with the transitions of the diagram.** -/
theorem cechDiagram_map_comp_cechTransport {P Q : Pair.{u}} (f : P ⟶ Q) {S T : PairGenSet P}
    (h : S ⟶ T) :
    (cechDiagram P).map h ≫ cechTransport f T =
      cechTransport f S ≫
        ((ModuleCat.restrictScalars f.toRingHom).mapHomologicalComplex (ComplexShape.up ℕ)).map
          ((cechDiagram Q).map (homOfLE (pairGenMap_monotone f (leOfHom h)))) := by
  refine HomologicalComplex.hom_ext _ _ fun p => ModuleCat.hom_ext ?_
  refine Eq.trans (Cech.genRingTerm_comp_genTerm f.toRingHom (fam S) (fam T)
    (fam (pairGenMap f T)) (idxLe (leOfHom h)) (exists_dvd_fam_of_le (leOfHom h))
    (idxMap f.toRingHom f.map_ideal T) (exists_dvd_map_fam f.toRingHom f.map_ideal T)
    (idxLe (leOfHom h) ∘ idxMap f.toRingHom f.map_ideal T)
    (exists_dvd_idxLe_idxMap f (leOfHom h)) rfl p) ?_
  exact (Cech.genTerm_comp_genRingTerm f.toRingHom (fam S) (fam (pairGenMap f S))
    (fam (pairGenMap f T)) (idxMap f.toRingHom f.map_ideal S)
    (exists_dvd_map_fam f.toRingHom f.map_ideal S)
    (idxLe (pairGenMap_monotone f (leOfHom h)))
    (exists_dvd_fam_of_le (pairGenMap_monotone f (leOfHom h)))
    (idxLe (leOfHom h) ∘ idxMap f.toRingHom f.map_ideal T)
    (exists_dvd_idxLe_idxMap f (leOfHom h))
    (idxLe_idxMap (leOfHom h) f.toRingHom f.map_ideal).symm p).symm

/-- The underlying ring map of a morphism of pairs, as a map of modules over the source ring.
This is the restriction map of the structure presheaf, written without the coercion
`↑(structureRings.obj X)` that the type of a presheaf of modules carries. -/
def ringTransport {P Q : Pair.{u}} (f : P ⟶ Q) :
    ModuleCat.of P.ring P.ring ⟶
      (ModuleCat.restrictScalars f.toRingHom).obj (ModuleCat.of Q.ring Q.ring) :=
  ModuleCat.ofHom
    (Y := (ModuleCat.restrictScalars f.toRingHom).obj (ModuleCat.of Q.ring Q.ring))
    (CechRingBaseChange.ofRingHom f.toRingHom)

/-- **The transport respects the degree-zero identification of the Čech complex.** -/
theorem cechZeroIso_cechTransport {P Q : Pair.{u}} (f : P ⟶ Q) (S : PairGenSet P) :
    (cechTransport f S).f 0 ≫
        (ModuleCat.restrictScalars f.toRingHom).map
          (LocalCohomology.cechZeroIso (fam (pairGenMap f S))
            (ModuleCat.of Q.ring Q.ring)).hom =
      (LocalCohomology.cechZeroIso (fam S) (ModuleCat.of P.ring P.ring)).hom ≫
        ringTransport f := by
  rw [cechTransport_eq, HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
    Category.assoc, ← Functor.map_comp,
    cechZeroIso_cechGenMap (CechRingBaseChange.mapFamily f.toRingHom (fam S))
      (fam (pairGenMap f S)) (idxMap f.toRingHom f.map_ideal S) (exists_dvd_mapFamily_fam f S)
      (ModuleCat.of Q.ring Q.ring)]
  exact cechZeroIso_complexMap f.toRingHom (fam S)

/-! ### The degreewise maps, typed through the diagram -/

/-- The degree-`n` component of the transport along a morphism of pairs. -/
def cechTransportTerm {P Q : Pair.{u}} (f : P ⟶ Q) (n : ℕ) (S : PairGenSet P) :
    (cechTermDiagram P n).obj S ⟶
      (ModuleCat.restrictScalars f.toRingHom).obj
        ((cechTermDiagram Q n).obj (pairGenMap f S)) :=
  (cechTransport f S).f n

/-- The degree-`n` component of the differential of a Čech complex of the diagram. -/
def cechDiffTerm (P : Pair.{u}) (n : ℕ) (S : PairGenSet P) :
    (cechTermDiagram P n).obj S ⟶ (cechTermDiagram P (n + 1)).obj S :=
  ((cechDiagram P).obj S).d n (n + 1)

/-- The degree-zero identification of a Čech complex of the diagram with the pair's ring. -/
def cechAugTerm (P : Pair.{u}) (S : PairGenSet P) :
    (cechTermDiagram P 0).obj S ⟶ ModuleCat.of P.ring P.ring :=
  (LocalCohomology.cechZeroIso (fam S) (ModuleCat.of P.ring P.ring)).hom

/-- The transitions of the diagram commute with the transport, degreewise. -/
theorem cechTransportTerm_naturality {P Q : Pair.{u}} (f : P ⟶ Q) {S T : PairGenSet P}
    (h : S ⟶ T) (n : ℕ) :
    (cechTermDiagram P n).map h ≫ cechTransportTerm f n T =
      cechTransportTerm f n S ≫
        (ModuleCat.restrictScalars f.toRingHom).map
          ((cechTermDiagram Q n).map (homOfLE (pairGenMap_monotone f (leOfHom h)))) :=
  HomologicalComplex.congr_hom (cechDiagram_map_comp_cechTransport f h) n

/-- The transitions of the diagram commute with the Čech differentials. -/
theorem cechDiffTerm_naturality (P : Pair.{u}) {S T : PairGenSet P} (h : S ⟶ T) (n : ℕ) :
    (cechTermDiagram P n).map h ≫ cechDiffTerm P n T =
      cechDiffTerm P n S ≫ (cechTermDiagram P (n + 1)).map h :=
  ((cechDiagram P).map h).comm n (n + 1)

/-- The Čech differentials of the diagram compose to zero. -/
theorem cechDiffTerm_comp_cechDiffTerm (P : Pair.{u}) (n : ℕ) (S : PairGenSet P) :
    cechDiffTerm P n S ≫ cechDiffTerm P (n + 1) S = 0 :=
  HomologicalComplex.d_comp_d _ n (n + 1) (n + 1 + 1)

/-- The transport is a map of complexes, degreewise. -/
theorem cechDiffTerm_comp_cechTransportTerm {P Q : Pair.{u}} (f : P ⟶ Q) (n : ℕ)
    (S : PairGenSet P) :
    cechDiffTerm P n S ≫ cechTransportTerm f (n + 1) S =
      cechTransportTerm f n S ≫
        (ModuleCat.restrictScalars f.toRingHom).map (cechDiffTerm Q n (pairGenMap f S)) :=
  ((cechTransport f S).comm n (n + 1)).symm

/-- The transitions of the diagram respect the degree-zero identification. -/
theorem cechAugTerm_naturality (P : Pair.{u}) {S T : PairGenSet P} (h : S ⟶ T) :
    (cechTermDiagram P 0).map h ≫ cechAugTerm P T = cechAugTerm P S :=
  cechZeroIso_cechDiagram_map P h

/-- The transport respects the degree-zero identification, degreewise. -/
theorem cechTransportTerm_comp_cechAugTerm {P Q : Pair.{u}} (f : P ⟶ Q) (S : PairGenSet P) :
    cechTransportTerm f 0 S ≫
        (ModuleCat.restrictScalars f.toRingHom).map (cechAugTerm Q (pairGenMap f S)) =
      cechAugTerm P S ≫ ringTransport f :=
  cechZeroIso_cechTransport f S

/-! ### The degreewise colimit, as a pair-module -/

/-- The cocone whose descent is the restriction map of the pair-module. -/
def transportCocone {P Q : Pair.{u}} (f : P ⟶ Q) (n : ℕ) : Cocone (cechTermDiagram P n) where
  pt := (ModuleCat.restrictScalars f.toRingHom).obj (colimit (cechTermDiagram Q n))
  ι :=
    { app := fun S =>
        cechTransportTerm f n S ≫
          (ModuleCat.restrictScalars f.toRingHom).map
            (colimit.ι (cechTermDiagram Q n) (pairGenMap f S))
      naturality := fun S T h => by
        dsimp only [Functor.const_obj_obj, Functor.const_obj_map]
        rw [Category.comp_id, ← Category.assoc, cechTransportTerm_naturality f h n,
          Category.assoc, ← Functor.map_comp, colimit.w] }

/-- The cone point of `transportCocone f n` is the restriction of scalars of the degree-`n`
colimit at the target pair. -/
@[simp]
theorem transportCocone_pt {P Q : Pair.{u}} (f : P ⟶ Q) (n : ℕ) :
    (transportCocone f n).pt =
      (ModuleCat.restrictScalars f.toRingHom).obj (colimit (cechTermDiagram Q n)) := rfl

/-- The leg of `transportCocone f n` at `S` is the transport followed by the colimit inclusion at
the transported index. -/
@[simp]
theorem transportCocone_ι_app {P Q : Pair.{u}} (f : P ⟶ Q) (n : ℕ) (S : PairGenSet P) :
    (transportCocone f n).ι.app S =
      cechTransportTerm f n S ≫
        (ModuleCat.restrictScalars f.toRingHom).map
          (colimit.ι (cechTermDiagram Q n) (pairGenMap f S)) := rfl

/-- **The restriction map of the degree-`n` pair-module**: the descent of the transport along a
morphism of pairs to the colimit over the generating families.

It is stated with its source and target written over the two pairs' own rings; the target of
`Stacks.PairSite.transportCocone` is the same object, but only through the projection `.pt` of a
cocone, which does not unfold at the transparency `rw` type-checks at. -/
def transportDesc {P Q : Pair.{u}} (f : P ⟶ Q) (n : ℕ) :
    (colimit (cechTermDiagram P n) : ModuleCat.{u} P.ring) ⟶
      (ModuleCat.restrictScalars f.toRingHom).obj
        (colimit (cechTermDiagram Q n) : ModuleCat.{u} Q.ring) :=
  colimit.desc _ (transportCocone f n)

/-- The descended transport restricted to the leg at `S` is the transport followed by the colimit
inclusion at the transported index. -/
@[simp]
theorem ι_transportDesc {P Q : Pair.{u}} (f : P ⟶ Q) (n : ℕ) (S : PairGenSet P) :
    colimit.ι (cechTermDiagram P n) S ≫ transportDesc f n =
      cechTransportTerm f n S ≫
        (ModuleCat.restrictScalars f.toRingHom).map
          (colimit.ι (cechTermDiagram Q n) (pairGenMap f S)) :=
  colimit.ι_desc _ _

/-- **The transport along the identity is a transition of the diagram**: the one along the
inclusion `S ≤ pairGenMap (𝟙 P) S`, which is an equality of indices but only propositionally,
`Finset.image` of the identity not being the identity on the nose. -/
theorem cechTransport_id_apply (P : Pair.{u}) (S : PairGenSet P) (n : ℕ)
    (x : Cech.cechTerm (fam S) P.ring n) :
    ((cechTransport (𝟙 P) S).f n).hom x =
      (((cechDiagram P).map (homOfLE (pairGenMap_id P S).ge)).f n).hom x := by
  refine Eq.trans (LinearMap.congr_fun (Cech.genRingTerm_id_ring (fam S)
    (fam (pairGenMap (𝟙 P) S)) (idxMap (RingHom.id P.ring) (Pair.Hom.map_ideal (𝟙 P)) S)
    (exists_dvd_map_fam (RingHom.id P.ring) (Pair.Hom.map_ideal (𝟙 P)) S) n) x) ?_
  exact LinearMap.congr_fun (Cech.genTerm_congr (fam S) (fam (pairGenMap (𝟙 P) S))
    (idxMap (RingHom.id P.ring) (Pair.Hom.map_ideal (𝟙 P)) S)
    (exists_dvd_map_fam (RingHom.id P.ring) (Pair.Hom.map_ideal (𝟙 P)) S) P.ring
    (exists_dvd_fam_of_le (pairGenMap_id P S).ge)
    (idxMap_id S (Pair.Hom.map_ideal (𝟙 P))) n) x

/-- The divisibility datum of the composite of two transports. -/
theorem exists_dvd_idxMap_idxMap {P Q R : Pair.{u}} (f : P ⟶ Q) (g : Q ⟶ R) (S : PairGenSet P)
    (k : Fin (famCard (pairGenMap g (pairGenMap f S)))) :
    ∃ n : ℕ, (g.toRingHom.comp f.toRingHom) (fam S
        ((idxMap f.toRingHom f.map_ideal S ∘
          idxMap g.toRingHom g.map_ideal (pairGenMap f S)) k)) ∣
      fam (pairGenMap g (pairGenMap f S)) k ^ n := by
  obtain ⟨m, hm⟩ := exists_dvd_map_fam g.toRingHom g.map_ideal (pairGenMap f S) k
  obtain ⟨c, hc⟩ := exists_dvd_map_fam f.toRingHom f.map_ideal S
    (idxMap g.toRingHom g.map_ideal (pairGenMap f S) k)
  refine ⟨m * c, ?_⟩
  have h1 := map_dvd g.toRingHom hc
  rw [map_pow] at h1
  rw [pow_mul]
  exact h1.trans (pow_dvd_pow_of_dvd hm c)

/-- **The transports compose**, up to the transition of the diagram along the inclusion
`pairGenMap (f ≫ g) S ≤ pairGenMap g (pairGenMap f S)`; the first half, computing the composite
of the two transports as a single comparison. -/
theorem cechTransport_comp_apply₁ {P Q R : Pair.{u}} (f : P ⟶ Q) (g : Q ⟶ R) (S : PairGenSet P)
    (n : ℕ) (x : Cech.cechTerm (fam S) P.ring n) :
    ((cechTransport g (pairGenMap f S)).f n).hom (((cechTransport f S).f n).hom x) =
      Cech.genRingTerm (g.toRingHom.comp f.toRingHom) (fam S)
        (fam (pairGenMap g (pairGenMap f S)))
        (idxMap f.toRingHom f.map_ideal S ∘
          idxMap g.toRingHom g.map_ideal (pairGenMap f S))
        (exists_dvd_idxMap_idxMap f g S) n x :=
  LinearMap.congr_fun (Cech.genRingTerm_comp f.toRingHom g.toRingHom
    (fam S) (fam (pairGenMap f S)) (fam (pairGenMap g (pairGenMap f S)))
    (idxMap f.toRingHom f.map_ideal S) (idxMap g.toRingHom g.map_ideal (pairGenMap f S))
    (exists_dvd_map_fam f.toRingHom f.map_ideal S)
    (exists_dvd_map_fam g.toRingHom g.map_ideal (pairGenMap f S))
    (exists_dvd_idxMap_idxMap f g S) n) x

/-- The second half: the single comparison factors through the transport along `f ≫ g`. -/
theorem cechTransport_comp_apply₂ {P Q R : Pair.{u}} (f : P ⟶ Q) (g : Q ⟶ R) (S : PairGenSet P)
    (n : ℕ) (x : Cech.cechTerm (fam S) P.ring n) :
    Cech.genRingTerm (g.toRingHom.comp f.toRingHom) (fam S)
        (fam (pairGenMap g (pairGenMap f S)))
        (idxMap f.toRingHom f.map_ideal S ∘
          idxMap g.toRingHom g.map_ideal (pairGenMap f S))
        (exists_dvd_idxMap_idxMap f g S) n x =
      (((cechDiagram R).map (homOfLE (pairGenMap_comp f g S).ge)).f n).hom
        (((cechTransport (f ≫ g) S).f n).hom x) :=
  (LinearMap.congr_fun (Cech.genTerm_comp_genRingTerm (f ≫ g).toRingHom (fam S)
    (fam (pairGenMap (f ≫ g) S)) (fam (pairGenMap g (pairGenMap f S)))
    (idxMap (f ≫ g).toRingHom (f ≫ g).map_ideal S)
    (exists_dvd_map_fam (f ≫ g).toRingHom (f ≫ g).map_ideal S)
    (idxLe (pairGenMap_comp f g S).ge)
    (exists_dvd_fam_of_le (pairGenMap_comp f g S).ge)
    (idxMap f.toRingHom f.map_ideal S ∘ idxMap g.toRingHom g.map_ideal (pairGenMap f S))
    (exists_dvd_idxMap_idxMap f g S)
    (idxMap_comp f.toRingHom g.toRingHom f.map_ideal g.map_ideal (f ≫ g).map_ideal S) n) x).symm

/-- **The transports compose**, up to the transition of the diagram along the inclusion
`pairGenMap (f ≫ g) S ≤ pairGenMap g (pairGenMap f S)`. -/
theorem cechTransport_comp_apply {P Q R : Pair.{u}} (f : P ⟶ Q) (g : Q ⟶ R) (S : PairGenSet P)
    (n : ℕ) (x : Cech.cechTerm (fam S) P.ring n) :
    ((cechTransport g (pairGenMap f S)).f n).hom (((cechTransport f S).f n).hom x) =
      (((cechDiagram R).map (homOfLE (pairGenMap_comp f g S).ge)).f n).hom
        (((cechTransport (f ≫ g) S).f n).hom x) :=
  (cechTransport_comp_apply₁ f g S n x).trans (cechTransport_comp_apply₂ f g S n x)

/-- The descended transport, read on the elements of a leg of the colimit. -/
theorem transportDesc_ι_apply {P Q : Pair.{u}} (f : P ⟶ Q) (n : ℕ) (S : PairGenSet P)
    (x : (cechTermDiagram P n).obj S) :
    (transportDesc f n).hom ((colimit.ι (cechTermDiagram P n) S).hom x) =
      (colimit.ι (cechTermDiagram Q n) (pairGenMap f S)).hom
        (((cechTransport f S).f n).hom x) :=
  LinearMap.congr_fun (congrArg ModuleCat.Hom.hom (ι_transportDesc f n S)) x

/-- The transitions of the colimit, read on elements. -/
theorem colimit_ι_apply_of_le (P : Pair.{u}) (n : ℕ) {S T : PairGenSet P} (h : S ⟶ T)
    (x : (cechTermDiagram P n).obj S) :
    (colimit.ι (cechTermDiagram P n) T).hom
        ((((cechDiagram P).map h).f n).hom x) =
      (colimit.ι (cechTermDiagram P n) S).hom x :=
  LinearMap.congr_fun (congrArg ModuleCat.Hom.hom (colimit.w (cechTermDiagram P n) h)) x

/-- **The descended transport along the identity is the identity.** -/
theorem transportDesc_id (P : Pair.{u}) (n : ℕ) :
    transportDesc (𝟙 P) n =
      (ModuleCat.restrictScalarsId' (RingHom.id P.ring) rfl).inv.app
        (colimit (cechTermDiagram P n) : ModuleCat.{u} P.ring) := by
  refine colimit.hom_ext fun S => ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
  refine Eq.trans (transportDesc_ι_apply (𝟙 P) n S x) ?_
  refine Eq.trans (congrArg
    (fun y => (colimit.ι (cechTermDiagram P n) (pairGenMap (𝟙 P) S)).hom y)
    (cechTransport_id_apply P S n x)) ?_
  exact colimit_ι_apply_of_le P n (homOfLE (pairGenMap_id P S).ge) x

/-- **The descended transports compose on the nose.** -/
theorem transportDesc_comp {P Q R : Pair.{u}} (f : P ⟶ Q) (g : Q ⟶ R) (n : ℕ) :
    transportDesc (f ≫ g) n =
      transportDesc f n ≫ (ModuleCat.restrictScalars f.toRingHom).map (transportDesc g n) ≫
        (ModuleCat.restrictScalarsComp' f.toRingHom g.toRingHom
            (g.toRingHom.comp f.toRingHom) rfl).inv.app
          (colimit (cechTermDiagram R n) : ModuleCat.{u} R.ring) := by
  refine colimit.hom_ext fun S => ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
  refine Eq.trans (transportDesc_ι_apply (f ≫ g) n S x) ?_
  refine Eq.trans ?_ (congrArg (fun y => (transportDesc g n).hom y)
    (transportDesc_ι_apply f n S x)).symm
  refine Eq.trans ?_ (transportDesc_ι_apply g n (pairGenMap f S)
    (((cechTransport f S).f n).hom x)).symm
  refine Eq.trans ?_ (congrArg
    (fun y => (colimit.ι (cechTermDiagram R n) (pairGenMap g (pairGenMap f S))).hom y)
    (cechTransport_comp_apply f g S n x)).symm
  exact (colimit_ι_apply_of_le R n (homOfLE (pairGenMap_comp f g S).ge)
    (((cechTransport (f ≫ g) S).f n).hom x)).symm

/-- **The degree-`n` term of the complex of pair-modules.** -/
def cechTermPair (n : ℕ) : PairModule.{u} where
  obj X := (colimit (cechTermDiagram X.unop.unop n) : ModuleCat.{u} (X.unop.unop).ring)
  map {_ _} f := transportDesc f.unop.unop n
  map_id X := transportDesc_id X.unop.unop n
  map_comp {_ _ _} f g := transportDesc_comp f.unop.unop g.unop.unop n

/-- The value of the degree-`n` term at a pair is the colimit of the degree-`n` Čech terms. -/
@[simp]
theorem cechTermPair_obj (n : ℕ) (X : Pair.{u}ᵒᵖᵒᵖ) :
    (cechTermPair n).obj X = colimit (cechTermDiagram X.unop.unop n) := rfl

/-- The restriction map of the degree-`n` term along a morphism is the descended transport. -/
@[simp]
theorem cechTermPair_map (n : ℕ) {X Y : Pair.{u}ᵒᵖᵒᵖ} (f : X ⟶ Y) :
    (cechTermPair n).map f = transportDesc f.unop.unop n := rfl

/-- **Two maps out of the degree-`n` term agree as soon as they agree on each leg of the
colimit.** This is `CategoryTheory.Limits.colimit.hom_ext`, restated with the ambient category
written as `ModuleCat (X.unop.unop).ring` rather than as `ModuleCat ↑(structureRings.obj X)`:
the two are the same category, but only the first spelling lets instance search find the
colimit. -/
theorem cechTermPair_hom_ext (n : ℕ) (X : Pair.{u}ᵒᵖᵒᵖ)
    {W : ModuleCat.{u} (X.unop.unop).ring}
    {g g' : (colimit (cechTermDiagram X.unop.unop n) : ModuleCat.{u} (X.unop.unop).ring) ⟶ W}
    (w : ∀ S, colimit.ι (cechTermDiagram X.unop.unop n) S ≫ g =
      colimit.ι (cechTermDiagram X.unop.unop n) S ≫ g') :
    g = g' :=
  colimit.hom_ext w

/-! ### The differential -/

/-- The cocone whose descent is the differential of the complex of pair-modules. -/
def diffCocone (P : Pair.{u}) (n : ℕ) : Cocone (cechTermDiagram P n) where
  pt := (colimit (cechTermDiagram P (n + 1)) : ModuleCat.{u} P.ring)
  ι :=
    { app := fun S => cechDiffTerm P n S ≫ colimit.ι (cechTermDiagram P (n + 1)) S
      naturality := fun S T h => by
        dsimp only [Functor.const_obj_obj, Functor.const_obj_map]
        rw [Category.comp_id, ← Category.assoc, cechDiffTerm_naturality P h n,
          Category.assoc, colimit.w] }

/-- The cone point of `diffCocone P n` is the degree-`n + 1` colimit. -/
@[simp]
theorem diffCocone_pt (P : Pair.{u}) (n : ℕ) :
    (diffCocone P n).pt = (colimit (cechTermDiagram P (n + 1)) : ModuleCat.{u} P.ring) := rfl

/-- The leg of `diffCocone P n` at `S` is the Čech differential followed by the colimit
inclusion at `S`. -/
@[simp]
theorem diffCocone_ι_app (P : Pair.{u}) (n : ℕ) (S : PairGenSet P) :
    (diffCocone P n).ι.app S =
      cechDiffTerm P n S ≫ colimit.ι (cechTermDiagram P (n + 1)) S := rfl

/-- **The differential of the degree-`n` pair-module**, descended to the colimit. -/
def diffDesc (P : Pair.{u}) (n : ℕ) :
    (colimit (cechTermDiagram P n) : ModuleCat.{u} P.ring) ⟶
      (colimit (cechTermDiagram P (n + 1)) : ModuleCat.{u} P.ring) :=
  colimit.desc _ (diffCocone P n)

/-- The descended differential restricted to the leg at `S` is the Čech differential followed by
the colimit inclusion at `S`. -/
@[simp]
theorem ι_diffDesc (P : Pair.{u}) (n : ℕ) (S : PairGenSet P) :
    colimit.ι (cechTermDiagram P n) S ≫ diffDesc P n =
      cechDiffTerm P n S ≫ colimit.ι (cechTermDiagram P (n + 1)) S :=
  colimit.ι_desc _ _

/-- **The descended differentials commute with the descended transports.** This is the
naturality of `Stacks.PairSite.cechDiffPair`, stated with every module written over the pair's
own ring. -/
theorem transportDesc_comp_diffDesc {P Q : Pair.{u}} (f : P ⟶ Q) (n : ℕ) :
    transportDesc f n ≫ (ModuleCat.restrictScalars f.toRingHom).map (diffDesc Q n) =
      diffDesc P n ≫ transportDesc f (n + 1) := by
  refine colimit.hom_ext fun S => ?_
  rw [← Category.assoc, ι_transportDesc, Category.assoc, ← Functor.map_comp, ι_diffDesc,
    ← Category.assoc, ι_diffDesc, Category.assoc, ι_transportDesc, Functor.map_comp,
    ← Category.assoc, ← cechDiffTerm_comp_cechTransportTerm, Category.assoc]

/-- **The differential of the complex of pair-modules.** -/
def cechDiffPair (n : ℕ) : cechTermPair.{u} n ⟶ cechTermPair.{u} (n + 1) where
  app X := diffDesc X.unop.unop n
  naturality {_ _} f := transportDesc_comp_diffDesc f.unop.unop n

/-- The component of the differential at a pair is the descended differential. -/
@[simp]
theorem cechDiffPair_app (n : ℕ) (X : Pair.{u}ᵒᵖᵒᵖ) :
    PresheafOfModules.Hom.app (cechDiffPair.{u} n) X = diffDesc X.unop.unop n := rfl

/-- **The descended differentials compose to zero.** -/
theorem diffDesc_comp_diffDesc (P : Pair.{u}) (n : ℕ) :
    diffDesc P n ≫ diffDesc P (n + 1) = 0 := by
  refine colimit.hom_ext fun S => ?_
  rw [← Category.assoc, ι_diffDesc, Category.assoc, ι_diffDesc, ← Category.assoc,
    cechDiffTerm_comp_cechDiffTerm, zero_comp, comp_zero]

/-! ### The complex of pair-modules -/

/-- **The complex of pair-modules of [Stacks, Tag 099D], in nonnegative degrees.** -/
def cechComplexPairNat : CochainComplex PairModule.{u} ℕ :=
  CochainComplex.of cechTermPair.{u} cechDiffPair.{u} fun n =>
    PresheafOfModules.hom_ext fun X => diffDesc_comp_diffDesc X.unop.unop n

/-- The degree-`n` object of the complex is `cechTermPair n`. -/
@[simp]
theorem cechComplexPairNat_X (n : ℕ) : cechComplexPairNat.{u}.X n = cechTermPair.{u} n := rfl

/-- The differential of the complex from degree `n` to `n + 1` is `cechDiffPair n`. -/
@[simp]
theorem cechComplexPairNat_d (n : ℕ) :
    cechComplexPairNat.{u}.d n (n + 1) = cechDiffPair.{u} n :=
  CochainComplex.of_d _ _ n

/-- **The complex of pair-modules of [Stacks, Tag 099D]**, in integer degrees. -/
abbrev cechComplexPair : CochainComplex PairModule.{u} ℤ :=
  cechComplexPairNat.{u}.extend ComplexShape.embeddingUpNat

/-- The complex of pair-modules vanishes in negative degrees. -/
theorem isZero_cechComplexPair_X (i : ℤ) (hi : i < 0) :
    Limits.IsZero (cechComplexPair.{u}.X i) := by
  refine HomologicalComplex.isZero_extend_X _ _ _ fun n hn => ?_
  rw [ComplexShape.embeddingUpNat_f] at hn
  omega

/-! ### The augmentation -/

/-- The cocone whose descent is the augmentation of the complex of pair-modules. -/
def augCocone (P : Pair.{u}) : Cocone (cechTermDiagram P 0) where
  pt := ModuleCat.of P.ring P.ring
  ι :=
    { app := fun S => cechAugTerm P S
      naturality := fun S T h => by
        dsimp only [Functor.const_obj_obj, Functor.const_obj_map]
        rw [Category.comp_id, cechAugTerm_naturality] }

/-- The cone point of `augCocone P` is the pair's ring, as a module over itself. -/
@[simp]
theorem augCocone_pt (P : Pair.{u}) : (augCocone P).pt = ModuleCat.of P.ring P.ring := rfl

/-- The leg of `augCocone P` at `S` is the degree-zero identification `cechAugTerm P S`. -/
@[simp]
theorem augCocone_ι_app (P : Pair.{u}) (S : PairGenSet P) :
    (augCocone P).ι.app S = cechAugTerm P S := rfl

/-- **The augmentation of the degree-zero pair-module**, descended to the colimit. -/
def augDesc (P : Pair.{u}) :
    (colimit (cechTermDiagram P 0) : ModuleCat.{u} P.ring) ⟶ ModuleCat.of P.ring P.ring :=
  colimit.desc _ (augCocone P)

/-- The descended augmentation restricted to the leg at `S` is `cechAugTerm P S`. -/
@[simp]
theorem ι_augDesc (P : Pair.{u}) (S : PairGenSet P) :
    colimit.ι (cechTermDiagram P 0) S ≫ augDesc P = cechAugTerm P S :=
  colimit.ι_desc _ _

/-- **The descended augmentations commute with the descended transports.** This is the
naturality of `Stacks.PairSite.cechAugZero`, stated with every module written over the pair's
own ring. -/
theorem transportDesc_comp_augDesc {P Q : Pair.{u}} (f : P ⟶ Q) :
    transportDesc f 0 ≫ (ModuleCat.restrictScalars f.toRingHom).map (augDesc Q) =
      augDesc P ≫ ringTransport f := by
  refine colimit.hom_ext fun S => ?_
  rw [← Category.assoc, ι_transportDesc, Category.assoc, ← Functor.map_comp, ι_augDesc,
    ← Category.assoc, ι_augDesc, cechTransportTerm_comp_cechAugTerm]

/-- **The augmentation of the degree-zero term onto the structure presheaf.** -/
def cechAugZero : cechTermPair.{u} 0 ⟶ structureModule.{u} where
  app X := augDesc X.unop.unop
  naturality {_ _} f := transportDesc_comp_augDesc f.unop.unop

/-- The component of the augmentation at a pair is the descended augmentation. -/
@[simp]
theorem cechAugZero_app (X : Pair.{u}ᵒᵖᵒᵖ) :
    PresheafOfModules.Hom.app cechAugZero.{u} X = augDesc X.unop.unop := rfl

/-- The degree-zero term of the integer-indexed complex of pair-modules. -/
def cechComplexPairXZeroIso : cechComplexPair.{u}.X 0 ≅ cechTermPair.{u} 0 :=
  HomologicalComplex.extendXIso cechComplexPairNat.{u} ComplexShape.embeddingUpNat
    ComplexShape.embeddingUpNat_f_zero

/-- **The augmentation `𝒦• ⟶ 𝒪[0]` of the complex of pair-modules.** -/
def cechAugmentationPair : cechComplexPair.{u} ⟶ structureSingle.{u} :=
  HomologicalComplex.mkHomToSingle
    (cechComplexPairXZeroIso.{u}.hom ≫ cechAugZero.{u}) fun i hi =>
      (isZero_cechComplexPair_X i (by change i + 1 = 0 at hi; omega)).eq_of_src _ _

/-- The degree-zero component of the augmentation is `cechAugZero`, composed with the
identifications of the degree-zero objects. -/
theorem cechAugmentationPair_f_zero :
    cechAugmentationPair.{u}.f 0 =
      (cechComplexPairXZeroIso.{u}.hom ≫ cechAugZero.{u}) ≫
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 structureModule.{u}).inv :=
  HomologicalComplex.mkHomToSingle_f _ _

/-! ### The sections at a pair are the colimit -/

/-- **The sections of the `ℕ`-graded complex of pair-modules at a pair**, written over the
pair's own ring. -/
abbrev sectionsNat (P : Pair.{u}) : CochainComplex (ModuleCat.{u} P.ring) ℕ :=
  ((PairModule.evaluation P).mapHomologicalComplex (ComplexShape.up ℕ)).obj
    cechComplexPairNat.{u}

/-- The differential of the sections from degree `n` to `n + 1` is the descended differential. -/
theorem sectionsNat_d (P : Pair.{u}) (n : ℕ) : (sectionsNat P).d n (n + 1) = diffDesc P n :=
  congrArg (fun w => (PairModule.evaluation P).map w) (cechComplexPairNat_d.{u} n)

/-- **The sections of the complex of pair-modules at a pair, as a cocone.** -/
def sectionsCoconeNat (P : Pair.{u}) : Cocone (cechDiagram P) where
  pt := sectionsNat P
  ι :=
    { app := fun S =>
        { f := fun n => colimit.ι (cechTermDiagram P n) S
          comm' := fun n m hnm => by
            obtain rfl : n + 1 = m := hnm
            exact Eq.trans (congrArg (fun w => colimit.ι (cechTermDiagram P n) S ≫ w)
              (sectionsNat_d P n)) (ι_diffDesc P n S) }
      naturality := fun S T h =>
        HomologicalComplex.hom_ext _ _ fun n =>
          (colimit.w (cechTermDiagram P n) h).trans (Category.comp_id _).symm }

/-- **The leg of the sections cocone at one generating index**, with its target written as
`Stacks.PairSite.sectionsNat` rather than as the value at `S` of a constant functor: the two
are the same complex, but only the first spelling lets instance search see it. -/
def sectionsLegNat (P : Pair.{u}) (S : PairGenSet P) :
    Cech.cechComplex (fam S) P.ring ⟶ sectionsNat P :=
  (sectionsCoconeNat P).ι.app S

/-- The degree-`n` component of the leg at `S` is the colimit inclusion at `S`. -/
@[simp]
theorem sectionsLegNat_f (P : Pair.{u}) (S : PairGenSet P) (n : ℕ) :
    (sectionsLegNat P S).f n = colimit.ι (cechTermDiagram P n) S := rfl

/-- **The sections of the complex of pair-modules at a pair are the colimit.** -/
def isColimit_sectionsCoconeNat (P : Pair.{u}) : IsColimit (sectionsCoconeNat P) := by
  refine HomologicalComplex.isColimitOfEval _ _ fun n => ?_
  exact IsColimit.ofIsoColimit (colimit.isColimit (cechTermDiagram P n))
    (Cocone.ext (Iso.refl _) fun S => Category.comp_id _)

/-- **The sections of the complex of pair-modules at a pair**, in integer degrees and written
over the pair's own ring. This is `Stacks.PairSite.sectionsComplex` of `cechComplexPair`, spelled
so that the ambient category is `ModuleCat P.ring` rather than
`ModuleCat ↑(structureRings.obj P.ix)`. -/
abbrev sectionsInt (P : Pair.{u}) : CochainComplex (ModuleCat.{u} P.ring) ℤ :=
  ((PairModule.evaluation P).mapHomologicalComplex (ComplexShape.up ℤ)).obj cechComplexPair.{u}

/-- `sectionsInt P` is the complex of sections of `cechComplexPair` at `P`. -/
theorem sectionsInt_eq (P : Pair.{u}) :
    sectionsInt P = sectionsComplex cechComplexPair.{u} P := rfl

/-! ### The Čech complex of one family maps into the sections -/

/-- **The comparison from the extended Čech complex of one product family into the sections.** -/
def cechSectionsIota (P : Pair.{u}) (S : PairGenSet P) :
    LocalCohomology.extendedCechComplex (fam S) (ModuleCat.of P.ring P.ring) ⟶ sectionsInt P :=
  HomologicalComplex.extendMap (sectionsLegNat P S) ComplexShape.embeddingUpNat ≫
    (HomologicalComplex.mapHomologicalComplexExtendIso (PairModule.evaluation P)
      cechComplexPairNat.{u} ComplexShape.embeddingUpNat).hom

/-- The comparison in a degree coming from `ℕ`. -/
theorem cechSectionsIota_f (P : Pair.{u}) (S : PairGenSet P) {n : ℕ} {i : ℤ}
    (h : ComplexShape.embeddingUpNat.f n = i) :
    (cechSectionsIota P S).f i =
      (HomologicalComplex.extendXIso (Cech.cechComplex (fam S) P.ring)
          ComplexShape.embeddingUpNat h).hom ≫
        colimit.ι (cechTermDiagram P n) S ≫
          (PairModule.evaluation P).map
            (HomologicalComplex.extendXIso cechComplexPairNat.{u}
              ComplexShape.embeddingUpNat h).inv :=
  HomologicalComplex.extendMap_mapHomologicalComplexExtendIso_f _ _ _ _ h

/-- **The sections of the complex of pair-modules at a pair are the Čech complex of any one
product family.** -/
theorem quasiIso_cechSectionsIota (P : Pair.{u}) (S : PairGenSet P) :
    QuasiIso (cechSectionsIota P S) := by
  have hnat : QuasiIso (sectionsLegNat P S) :=
    StacksDraft.quasiIso_isColimit_ι (cechDiagram P) (fun _ _ h => quasiIso_cechDiagram_map P h)
      (sectionsCoconeNat P) (isColimit_sectionsCoconeNat P) S
  refine quasiIso_comp (HomologicalComplex.extendMap (sectionsLegNat P S)
      ComplexShape.embeddingUpNat)
    (HomologicalComplex.mapHomologicalComplexExtendIso (PairModule.evaluation P)
      cechComplexPairNat.{u} ComplexShape.embeddingUpNat).hom (hφ := ?_) (hφ' := ?_)
  · rwa [HomologicalComplex.quasiIso_extendMap_iff]
  · exact quasiIso_of_isIso _

/-! ### The comparison is compatible with the augmentations -/

/-- **The augmentation on the sections at a pair**, written over the pair's own ring. This is
`Stacks.PairSite.sectionsAugmentation` of `cechAugmentationPair`. -/
def sectionsIntAugmentation (P : Pair.{u}) :
    sectionsInt P ⟶ (CochainComplex.singleFunctor (ModuleCat.{u} P.ring) 0).obj
      (ModuleCat.of P.ring P.ring) :=
  ((PairModule.evaluation P).mapHomologicalComplex (ComplexShape.up ℤ)).map
      cechAugmentationPair.{u} ≫
    ((HomologicalComplex.singleMapHomologicalComplex (PairModule.evaluation P)
      (ComplexShape.up ℤ) 0).app structureModule.{u}).hom

/-- `sectionsIntAugmentation P` is the augmentation on sections of `cechAugmentationPair` at
`P`. -/
theorem sectionsIntAugmentation_eq (P : Pair.{u}) :
    sectionsIntAugmentation P = sectionsAugmentation cechAugmentationPair.{u} P := rfl

/-- The degree-zero component of the augmentation, read back through the identification of the
degree-zero term of the integer-graded complex with the degree-zero pair-module. -/
theorem cechComplexPairXZeroIso_inv_comp_augmentation :
    cechComplexPairXZeroIso.{u}.inv ≫ cechAugmentationPair.{u}.f 0 ≫
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 structureModule.{u}).hom =
      cechAugZero.{u} := by
  refine Eq.trans (congrArg (fun w => cechComplexPairXZeroIso.{u}.inv ≫ w ≫
    (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 structureModule.{u}).hom)
    cechAugmentationPair_f_zero.{u}) ?_
  refine Eq.trans (Iso.inv_hom_id_assoc cechComplexPairXZeroIso.{u}
    (cechAugZero.{u} ≫ (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
        structureModule.{u}).inv ≫
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 structureModule.{u}).hom)) ?_
  refine Eq.trans (congrArg (fun w => cechAugZero.{u} ≫ w)
    (Iso.inv_hom_id (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
      structureModule.{u}))) ?_
  exact Category.comp_id _

/-- The three-fold composite of evaluated maps that computes the degree-zero component of the
augmentation on sections. -/
theorem evaluation_comp_augmentation (P : Pair.{u}) :
    (PairModule.evaluation P).map cechComplexPairXZeroIso.{u}.inv ≫
        (PairModule.evaluation P).map (cechAugmentationPair.{u}.f 0) ≫
          (PairModule.evaluation P).map
            (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 structureModule.{u}).hom =
      augDesc P := by
  refine Eq.trans ?_ (congrArg (fun w => (PairModule.evaluation P).map w)
    cechComplexPairXZeroIso_inv_comp_augmentation.{u})
  exact (((PairModule.evaluation P).map_comp _ _).trans
    (congrArg (fun w => (PairModule.evaluation P).map cechComplexPairXZeroIso.{u}.inv ≫ w)
      ((PairModule.evaluation P).map_comp _ _))).symm

/-- **The identification of the sections with a single Čech complex is compatible with the
augmentations.** -/
theorem cechSectionsIota_comp_augmentation (P : Pair.{u}) (S : PairGenSet P) :
    cechSectionsIota P S ≫ sectionsIntAugmentation P =
      LocalCohomology.extendedCechAugmentation (fam S) (ModuleCat.of P.ring P.ring) := by
  refine HomologicalComplex.to_single_hom_ext ?_
  refine Eq.trans (congrArg (fun w => w ≫ (sectionsIntAugmentation P).f 0)
    (cechSectionsIota_f P S ComplexShape.embeddingUpNat_f_zero)) ?_
  refine Eq.trans (congrArg (fun w =>
    (HomologicalComplex.extendXIso (Cech.cechComplex (fam S) P.ring)
        ComplexShape.embeddingUpNat ComplexShape.embeddingUpNat_f_zero).hom ≫
      colimit.ι (cechTermDiagram P 0) S ≫
        (PairModule.evaluation P).map cechComplexPairXZeroIso.{u}.inv ≫
          (PairModule.evaluation P).map (cechAugmentationPair.{u}.f 0) ≫ w)
    (HomologicalComplex.singleMapHomologicalComplex_hom_app_self (PairModule.evaluation P)
      (ComplexShape.up ℤ) 0 structureModule.{u})) ?_
  refine Eq.trans (congrArg (fun w =>
    (HomologicalComplex.extendXIso (Cech.cechComplex (fam S) P.ring)
        ComplexShape.embeddingUpNat ComplexShape.embeddingUpNat_f_zero).hom ≫
      colimit.ι (cechTermDiagram P 0) S ≫ w ≫
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
          (ModuleCat.of P.ring P.ring)).inv) (evaluation_comp_augmentation P)) ?_
  refine Eq.trans (congrArg (fun w =>
    (HomologicalComplex.extendXIso (Cech.cechComplex (fam S) P.ring)
        ComplexShape.embeddingUpNat ComplexShape.embeddingUpNat_f_zero).hom ≫ w ≫
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
        (ModuleCat.of P.ring P.ring)).inv) (ι_augDesc P S)) ?_
  exact ((LocalCohomology.extendedCechAugmentation_f_zero (fam S)
      (ModuleCat.of P.ring P.ring)).trans
    (congrArg (fun w => w ≫ (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
        (ModuleCat.of P.ring P.ring)).inv)
      (LocalCohomology.extendedCechXZeroIso_hom (fam S) (ModuleCat.of P.ring P.ring)))).symm

/-! ### The transport in integer degrees -/

/-- **The restriction map on the sections at a pair**, written over the two pairs' own rings.
This is `Stacks.PairSite.sectionsMap` of `cechComplexPair`. -/
def sectionsIntMap {P Q : Pair.{u}} (f : P ⟶ Q) :
    sectionsInt P ⟶ (CochainComplex.restrictScalars f.toRingHom).obj (sectionsInt Q) where
  f n := (cechComplexPair.{u}.X n).restriction f
  comm' n m _ := (cechComplexPair.{u}.d n m).naturality (Pair.Hom.ix f)

/-- `sectionsIntMap f` is the map on sections of `cechComplexPair` along `f`. -/
theorem sectionsIntMap_eq {P Q : Pair.{u}} (f : P ⟶ Q) :
    sectionsIntMap f = sectionsMap cechComplexPair.{u} f := rfl

/-- **The comparison along a morphism of pairs, in integer degrees.** -/
def extendedCechTransport {P Q : Pair.{u}} (f : P ⟶ Q) (S : PairGenSet P) :
    LocalCohomology.extendedCechComplex (fam S) (ModuleCat.of P.ring P.ring) ⟶
      (CochainComplex.restrictScalars f.toRingHom).obj
        (LocalCohomology.extendedCechComplex (fam (pairGenMap f S))
          (ModuleCat.of Q.ring Q.ring)) :=
  HomologicalComplex.extendMap (cechTransport f S) ComplexShape.embeddingUpNat ≫
    (HomologicalComplex.mapHomologicalComplexExtendIso
      (ModuleCat.restrictScalars f.toRingHom)
      (Cech.cechComplex (fam (pairGenMap f S)) Q.ring) ComplexShape.embeddingUpNat).hom

/-- The comparison along a morphism of pairs in a degree coming from `ℕ`. -/
theorem extendedCechTransport_f {P Q : Pair.{u}} (f : P ⟶ Q) (S : PairGenSet P) {n : ℕ} {i : ℤ}
    (h : ComplexShape.embeddingUpNat.f n = i) :
    (extendedCechTransport f S).f i =
      (HomologicalComplex.extendXIso (Cech.cechComplex (fam S) P.ring)
          ComplexShape.embeddingUpNat h).hom ≫
        (cechTransport f S).f n ≫
          (ModuleCat.restrictScalars f.toRingHom).map
            (HomologicalComplex.extendXIso (Cech.cechComplex (fam (pairGenMap f S)) Q.ring)
              ComplexShape.embeddingUpNat h).inv :=
  HomologicalComplex.extendMap_mapHomologicalComplexExtendIso_f _ _ _ _ h

/-- **The identification of the sections with a single Čech complex is compatible with the
restriction maps.** -/
theorem cechSectionsIota_comp_sectionsMap {P Q : Pair.{u}} (f : P ⟶ Q) (S : PairGenSet P) :
    cechSectionsIota P S ≫ sectionsIntMap f =
      extendedCechTransport f S ≫
        (CochainComplex.restrictScalars f.toRingHom).map
          (cechSectionsIota Q (pairGenMap f S)) := by
  refine HomologicalComplex.hom_ext _ _ fun i => ?_
  rcases hi : ComplexShape.embeddingUpNat.r i with _ | n
  · exact (HomologicalComplex.isZero_extend_X' _ _ i hi).eq_of_src _ _
  · have h : ComplexShape.embeddingUpNat.f n = i :=
      ComplexShape.Embedding.f_eq_of_r_eq_some _ hi
    have hsplit : (ModuleCat.restrictScalars f.toRingHom).map
          ((HomologicalComplex.extendXIso (Cech.cechComplex (fam (pairGenMap f S)) Q.ring)
              ComplexShape.embeddingUpNat h).hom ≫
            colimit.ι (cechTermDiagram Q n) (pairGenMap f S) ≫
              (PairModule.evaluation Q).map
                (HomologicalComplex.extendXIso cechComplexPairNat.{u}
                  ComplexShape.embeddingUpNat h).inv) =
        (ModuleCat.restrictScalars f.toRingHom).map
            (HomologicalComplex.extendXIso (Cech.cechComplex (fam (pairGenMap f S)) Q.ring)
              ComplexShape.embeddingUpNat h).hom ≫
          (ModuleCat.restrictScalars f.toRingHom).map
              (colimit.ι (cechTermDiagram Q n) (pairGenMap f S)) ≫
            (ModuleCat.restrictScalars f.toRingHom).map
              ((PairModule.evaluation Q).map
                (HomologicalComplex.extendXIso cechComplexPairNat.{u}
                  ComplexShape.embeddingUpNat h).inv) :=
      ((ModuleCat.restrictScalars f.toRingHom).map_comp _ _).trans
        (congrArg (fun w => (ModuleCat.restrictScalars f.toRingHom).map
            (HomologicalComplex.extendXIso (Cech.cechComplex (fam (pairGenMap f S)) Q.ring)
              ComplexShape.embeddingUpNat h).hom ≫ w)
          ((ModuleCat.restrictScalars f.toRingHom).map_comp _ _))
    have hnat := (PresheafOfModules.Hom.naturality
      (HomologicalComplex.extendXIso cechComplexPairNat.{u} ComplexShape.embeddingUpNat h).inv
      (Pair.Hom.ix f)).symm
    refine Eq.trans (congrArg (fun w => w ≫ (sectionsIntMap f).f i)
      (cechSectionsIota_f P S h)) ?_
    refine Eq.trans (congrArg (fun w =>
      (HomologicalComplex.extendXIso (Cech.cechComplex (fam S) P.ring)
          ComplexShape.embeddingUpNat h).hom ≫
        colimit.ι (cechTermDiagram P n) S ≫ w) hnat) ?_
    refine Eq.trans (congrArg (fun w => (HomologicalComplex.extendXIso
        (Cech.cechComplex (fam S) P.ring) ComplexShape.embeddingUpNat h).hom ≫ w ≫
        (ModuleCat.restrictScalars f.toRingHom).map
          ((PairModule.evaluation Q).map
            (HomologicalComplex.extendXIso cechComplexPairNat.{u}
              ComplexShape.embeddingUpNat h).inv)) (ι_transportDesc f n S)) ?_
    refine Eq.trans ?_ (congrArg (fun w => w ≫
      (ModuleCat.restrictScalars f.toRingHom).map ((cechSectionsIota Q (pairGenMap f S)).f i))
      (extendedCechTransport_f f S h)).symm
    refine Eq.trans ?_ (congrArg (fun w =>
      ((HomologicalComplex.extendXIso (Cech.cechComplex (fam S) P.ring)
            ComplexShape.embeddingUpNat h).hom ≫ (cechTransport f S).f n ≫
          (ModuleCat.restrictScalars f.toRingHom).map
            (HomologicalComplex.extendXIso (Cech.cechComplex (fam (pairGenMap f S)) Q.ring)
              ComplexShape.embeddingUpNat h).inv) ≫
        (ModuleCat.restrictScalars f.toRingHom).map w)
      (cechSectionsIota_f Q (pairGenMap f S) h)).symm
    refine Eq.trans ?_ (congrArg (fun w =>
      ((HomologicalComplex.extendXIso (Cech.cechComplex (fam S) P.ring)
            ComplexShape.embeddingUpNat h).hom ≫ (cechTransport f S).f n ≫
          (ModuleCat.restrictScalars f.toRingHom).map
            (HomologicalComplex.extendXIso (Cech.cechComplex (fam (pairGenMap f S)) Q.ring)
              ComplexShape.embeddingUpNat h).inv) ≫ w) hsplit).symm
    exact (congrArg (fun w => (HomologicalComplex.extendXIso (Cech.cechComplex (fam S) P.ring)
        ComplexShape.embeddingUpNat h).hom ≫ (cechTransport f S).f n ≫ w)
      (CategoryTheory.Iso.map_inv_hom_id_assoc
        (HomologicalComplex.extendXIso (Cech.cechComplex (fam (pairGenMap f S)) Q.ring)
          ComplexShape.embeddingUpNat h)
        (ModuleCat.restrictScalars f.toRingHom)
        ((ModuleCat.restrictScalars f.toRingHom).map
            (colimit.ι (cechTermDiagram Q n) (pairGenMap f S)) ≫
          (ModuleCat.restrictScalars f.toRingHom).map
            ((PairModule.evaluation Q).map
              (HomologicalComplex.extendXIso cechComplexPairNat.{u}
                ComplexShape.embeddingUpNat h).inv)))).symm

/-! ### Condition (d) at a presented pair -/

/-- The product family of the singleton index on a generating family spans the same ideal as the
family itself: it is that family, reindexed along a bijection. -/
theorem span_range_fam_single (P : Pair.{u}) {r : ℕ} (g : Fin r → P.ring)
    (hg : Ideal.span (Set.range g) = P.ideal) :
    Ideal.span (Set.range g) =
      Ideal.span (Set.range (fam (GenFamily.single (⟨r, g, hg⟩ : Gen P.ring P.ideal)))) := by
  obtain ⟨σ, hσ, hfam⟩ := exists_bijective_single (⟨r, g, hg⟩ : Gen P.ring P.ideal)
  have hr : Set.range (fam (GenFamily.single (⟨r, g, hg⟩ : Gen P.ring P.ideal)))
      = Set.range g := by
    rw [show fam (GenFamily.single (⟨r, g, hg⟩ : Gen P.ring P.ideal)) = g ∘ σ from funext hfam]
    exact hσ.2.range_comp g
  rw [hr]

/-- **Condition (d) of [Stacks, Tag 099D] at a presented pair**, for the complex of
pair-modules. -/
theorem exists_cech_iso_sectionsInt (P : Pair.{u}) {r : ℕ} (g : Fin r → P.ring)
    (hg : Ideal.span (Set.range g) = P.ideal) :
    ∃ e : LocalCohomology.extendedCechObject g (ModuleCat.of P.ring P.ring) ≅
        DerivedCategory.Q.obj (sectionsInt P),
      e.hom ≫ DerivedCategory.Q.map (sectionsIntAugmentation P) ≫
          ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{u} P.ring) 0).app
            (ModuleCat.of P.ring P.ring)).inv =
        LocalCohomology.extendedCechAugmentationHom g (ModuleCat.of P.ring P.ring) := by
  have hspan := span_range_fam_single P g hg
  have hqi : QuasiIso (cechSectionsIota P
    (GenFamily.single (⟨r, g, hg⟩ : Gen P.ring P.ideal))) := quasiIso_cechSectionsIota _ _
  refine ⟨IdealCechComplex.canonicalIso g
    (fam (GenFamily.single (⟨r, g, hg⟩ : Gen P.ring P.ideal)))
    (ModuleCat.of P.ring P.ring) hspan ≪≫
      asIso (DerivedCategory.Q.map (cechSectionsIota P
        (GenFamily.single (⟨r, g, hg⟩ : Gen P.ring P.ideal)))), ?_⟩
  rw [Iso.trans_hom, asIso_hom, IdealCechComplex.canonicalIso_hom, Category.assoc,
    ← Category.assoc (DerivedCategory.Q.map (cechSectionsIota P
      (GenFamily.single (⟨r, g, hg⟩ : Gen P.ring P.ideal)))), ← Functor.map_comp,
    cechSectionsIota_comp_augmentation]
  exact IdealCechComplex.canonicalHom_comp_augmentationHom g
    (fam (GenFamily.single (⟨r, g, hg⟩ : Gen P.ring P.ideal)))
    (ModuleCat.of P.ring P.ring) hspan

/-! ### Condition (c) at a presented pair -/

/-- The image of the product family of `S` and the product family of the transported index cut
out the same closed subset of `Spec Q.ring`: both cut out the ideal of `Q`, which is the image
of the ideal of `P`. -/
theorem zeroLocus_mapFamily_eq {P Q : Pair.{u}} (f : P ⟶ Q) (S : PairGenSet P) :
    PrimeSpectrum.zeroLocus
        ((Ideal.span (Set.range (CechRingBaseChange.mapFamily f.toRingHom (fam S)))
          : Ideal Q.ring) : Set Q.ring) =
      PrimeSpectrum.zeroLocus
        ((Ideal.span (Set.range (fam (pairGenMap f S))) : Ideal Q.ring) : Set Q.ring) := by
  have hL : PrimeSpectrum.zeroLocus
        ((Ideal.span (Set.range (CechRingBaseChange.mapFamily f.toRingHom (fam S)))
          : Ideal Q.ring) : Set Q.ring)
      = PrimeSpectrum.comap f.toRingHom ⁻¹'
          PrimeSpectrum.zeroLocus ((P.ideal : Ideal P.ring) : Set P.ring) := by
    rw [PrimeSpectrum.zeroLocus_span,
      show Set.range (CechRingBaseChange.mapFamily f.toRingHom (fam S))
        = f.toRingHom '' Set.range (fam S) from Set.range_comp _ _,
      ← PrimeSpectrum.preimage_comap_zeroLocus, zeroLocus_range_fam S]
  have hR : PrimeSpectrum.zeroLocus
        ((Ideal.span (Set.range (fam (pairGenMap f S))) : Ideal Q.ring) : Set Q.ring)
      = PrimeSpectrum.comap f.toRingHom ⁻¹'
          PrimeSpectrum.zeroLocus ((P.ideal : Ideal P.ring) : Set P.ring) := by
    rw [zeroLocus_span_range_fam (pairGenMap f S), PrimeSpectrum.preimage_comap_zeroLocus,
      Pair.Hom.map_ideal f]
    exact PrimeSpectrum.zeroLocus_span (f.toRingHom '' (P.ideal : Set P.ring))
  exact hL.trans hR.symm

/-- **The same-ring comparison from the image family to the product family of the transported
index**, in integer degrees. -/
def cechImageComparison {P Q : Pair.{u}} (f : P ⟶ Q) (S : PairGenSet P) :
    LocalCohomology.extendedCechComplex (CechRingBaseChange.mapFamily f.toRingHom (fam S))
        (ModuleCat.of Q.ring Q.ring) ⟶
      LocalCohomology.extendedCechComplex (fam (pairGenMap f S)) (ModuleCat.of Q.ring Q.ring) :=
  HomologicalComplex.extendMap
    (Cech.cechGenMap (CechRingBaseChange.mapFamily f.toRingHom (fam S))
      (fam (pairGenMap f S)) (idxMap f.toRingHom f.map_ideal S)
      (exists_dvd_mapFamily_fam f S) Q.ring) ComplexShape.embeddingUpNat

/-- **The comparison from the image family is a quasi-isomorphism**: the two families cut out the
same closed subset and the comparison respects the augmentations. -/
theorem quasiIso_cechImageComparison {P Q : Pair.{u}} (f : P ⟶ Q) (S : PairGenSet P) :
    QuasiIso (cechImageComparison f S) :=
  IdealCechComplex.quasiIso_of_comp_augmentation_of_zeroLocus_eq _ _
    (ModuleCat.of Q.ring Q.ring) (zeroLocus_mapFamily_eq f S) _
    (IdealCechComplex.extendMap_comp_augmentation _ _ (ModuleCat.of Q.ring Q.ring) _
      (cechZeroIso_cechGenMap _ _ _ _ (ModuleCat.of Q.ring Q.ring)))

/-- **The transport in integer degrees factors through the change of rings.** -/
theorem extendedCechTransport_eq {P Q : Pair.{u}} (f : P ⟶ Q) (S : PairGenSet P) :
    extendedCechTransport f S =
      CechRingBaseChange.extendedComplexMap f.toRingHom (fam S) ≫
        (CochainComplex.restrictScalars f.toRingHom).map (cechImageComparison f S) := by
  have hnat := HomologicalComplex.mapHomologicalComplexExtendIso_inv_naturality
    (ModuleCat.restrictScalars f.toRingHom)
    (Cech.cechComplex (CechRingBaseChange.mapFamily f.toRingHom (fam S)) Q.ring)
    (Cech.cechGenMap (CechRingBaseChange.mapFamily f.toRingHom (fam S))
      (fam (pairGenMap f S)) (idxMap f.toRingHom f.map_ideal S)
      (exists_dvd_mapFamily_fam f S) Q.ring) ComplexShape.embeddingUpNat
  have hnat2 : HomologicalComplex.extendMap
        (((ModuleCat.restrictScalars f.toRingHom).mapHomologicalComplex
            (ComplexShape.up ℕ)).map
          (Cech.cechGenMap (CechRingBaseChange.mapFamily f.toRingHom (fam S))
            (fam (pairGenMap f S)) (idxMap f.toRingHom f.map_ideal S)
            (exists_dvd_mapFamily_fam f S) Q.ring)) ComplexShape.embeddingUpNat ≫
        (HomologicalComplex.mapHomologicalComplexExtendIso
          (ModuleCat.restrictScalars f.toRingHom)
          (Cech.cechComplex (fam (pairGenMap f S)) Q.ring) ComplexShape.embeddingUpNat).hom =
      (HomologicalComplex.mapHomologicalComplexExtendIso
            (ModuleCat.restrictScalars f.toRingHom)
            (Cech.cechComplex (CechRingBaseChange.mapFamily f.toRingHom (fam S)) Q.ring)
            ComplexShape.embeddingUpNat).hom ≫
        ((ModuleCat.restrictScalars f.toRingHom).mapHomologicalComplex
            (ComplexShape.up ℤ)).map (cechImageComparison f S) := by
    rw [← cancel_mono (HomologicalComplex.mapHomologicalComplexExtendIso
      (ModuleCat.restrictScalars f.toRingHom)
      (Cech.cechComplex (fam (pairGenMap f S)) Q.ring) ComplexShape.embeddingUpNat).inv]
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
    rw [cechImageComparison, hnat, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  rw [extendedCechTransport, cechTransport_eq f S, HomologicalComplex.extendMap_comp]
  exact (Category.assoc _ _ _).trans (congrArg (fun w =>
    HomologicalComplex.extendMap (CechRingBaseChange.complexMap f.toRingHom (fam S))
      ComplexShape.embeddingUpNat ≫ w) hnat2)

/-- **Condition (c) of [Stacks, Tag 099D] for the transport at one generating index.** -/
theorem isIso_derivedBaseChange_extendedCechTransport {P Q : Pair.{u}} (f : P ⟶ Q)
    (S : PairGenSet P) :
    IsIso (LocalCohomology.derivedBaseChange f.toRingHom (extendedCechTransport f S)) := by
  have : QuasiIso (cechImageComparison f S) := quasiIso_cechImageComparison f S
  have : IsIso (LocalCohomology.derivedBaseChange f.toRingHom
      (CechRingBaseChange.extendedComplexMap f.toRingHom (fam S))) :=
    CechRingBaseChange.isIso_derivedBaseChange_extendedComplexMap f.toRingHom (fam S)
  have h2 : LocalCohomology.derivedBaseChange f.toRingHom (extendedCechTransport f S) =
      LocalCohomology.derivedBaseChange f.toRingHom
          (CechRingBaseChange.extendedComplexMap f.toRingHom (fam S)) ≫
        DerivedCategory.Q.map (cechImageComparison f S) :=
    (congrArg (fun w => LocalCohomology.derivedBaseChange f.toRingHom w)
        (extendedCechTransport_eq f S)).trans
      (LocalCohomology.derivedBaseChange_comp_right f.toRingHom
        (CechRingBaseChange.extendedComplexMap f.toRingHom (fam S)) (cechImageComparison f S))
  rw [h2]
  infer_instance

/-- **Condition (c) of [Stacks, Tag 099D] at presented pairs**, for the complex of
pair-modules. -/
theorem isIso_derivedBaseChange_sectionsIntMap {P Q : Pair.{u}} (f : P ⟶ Q) :
    IsIso (LocalCohomology.derivedBaseChange f.toRingHom (sectionsIntMap f)) := by
  obtain ⟨S⟩ := instNonemptyPairGenSet P
  have : QuasiIso (cechSectionsIota P S) := quasiIso_cechSectionsIota P S
  have : QuasiIso (cechSectionsIota Q (pairGenMap f S)) :=
    quasiIso_cechSectionsIota Q (pairGenMap f S)
  have hbc := isIso_derivedBaseChange_extendedCechTransport f S
  have heq2 : LocalCohomology.derivedBaseChange f.toRingHom
        (cechSectionsIota P S ≫ sectionsIntMap f) =
      LocalCohomology.derivedBaseChange f.toRingHom (extendedCechTransport f S) ≫
        DerivedCategory.Q.map (cechSectionsIota Q (pairGenMap f S)) := by
    rw [cechSectionsIota_comp_sectionsMap, LocalCohomology.derivedBaseChange_comp_right]
  have hX : LocalCohomology.derivedBaseChange f.toRingHom (sectionsIntMap f) =
      inv ((CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsGeneral.{u, u, u}
            f.toRingHom).functor.map
          (DerivedCategory.Q.map (cechSectionsIota P S))) ≫
        (LocalCohomology.derivedBaseChange f.toRingHom (extendedCechTransport f S) ≫
          DerivedCategory.Q.map (cechSectionsIota Q (pairGenMap f S))) := by
    rw [← heq2, LocalCohomology.derivedBaseChange_comp_left, IsIso.inv_hom_id_assoc]
  rw [hX]
  infer_instance

/-! ### The datum -/

/-- **A Čech datum on the category of presented pairs exists**: the complex of pair-modules
built as the filtered colimit of the extended Čech complexes over the generating families at
each presented pair, with its augmentation onto the structure presheaf. -/
theorem exists_presentedCechDatum : Nonempty PresentedCechDatum.{u} :=
  ⟨{ complex := cechComplexPair.{u}
     augmentation := cechAugmentationPair.{u}
     isIso_derivedBaseChange := @fun _ _ f => isIso_derivedBaseChange_sectionsIntMap f
     exists_cech_iso := @fun P _ g hg => exists_cech_iso_sectionsInt P g hg }⟩

end Stacks.PairSite

end
