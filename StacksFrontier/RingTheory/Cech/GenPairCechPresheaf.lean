module

public import StacksFrontier.RingTheory.Cech.GenPairSite

/-!
# The Čech identification of [Stacks, Tag 099D] as a quasi-isomorphism of presheaf complexes

Let `r : ℕ`. On the category `Stacks.GenPairSite.GenPair r` of commutative rings carrying a
chosen family of `r` elements, two complexes of presheaves of modules are available:

* `Č`, the **extended alternating Čech complex of the chosen family**,
  `X = (A, f₁, …, f_r) ↦ Č(A, f₁, …, f_r)`, whose restriction maps are the change-of-rings maps
  of the Čech complex. They compose **on the nose**, because a morphism of generated pairs
  carries the chosen family pointwise onto the chosen family, so the image family at the target
  *is* the target's family and no comparison is needed;
* `K`, the filtered colimit `Stacks.GenPairSite.kComplexNat`, which depends only on the ring and
  the ideal.

This file builds a **map of complexes of presheaves of modules**

`Č ⟶ K`

which at each object is a quasi-isomorphism, and which is compatible with the two augmentations
onto the structure presheaf. At an object it is the comparison `Č(A, f) ⟶ Č(A, fam (single f))`
onto the product family of the singleton index, followed by the colimit leg at that index; both
are quasi-isomorphisms, the first because the two families cut out the same closed subset of the
spectrum and the second because the index system is filtered with quasi-isomorphic transitions.

This is the form in which the identification of [Stacks, Tag 099D] condition (d) is needed by
[Stacks, Tag 099E]: a family of isomorphisms in the derived categories `D(𝒪(V))`, one for each
object `V` and compatible with the restriction maps, is **not** a morphism in
`D(PresheafOfModules 𝒪)` — `Hom` in a derived category of presheaves has no objectwise
description — so there would be nothing to sheafify. A map of complexes of presheaves, which is
what this file produces, does sheafify.

## Main definitions

* `Stacks.GenPairSite.cechTermPre`, `Stacks.GenPairSite.cechDiffPre`,
  `Stacks.GenPairSite.cechComplexPre` — the Čech complex of the chosen family, as a complex of
  presheaves of modules; `Stacks.GenPairSite.cechAugZeroPre` is its augmentation.
* `Stacks.GenPairSite.evalCechIso` — its sections at an object are the Čech complex of that
  object's family.
* `Stacks.GenPairSite.cechLeg` — the comparison onto the Čech complex of the product family of
  the singleton index, and `Stacks.GenPairSite.cechCompare` its composite with the colimit leg.
* `Stacks.GenPairSite.cechToKTerm`, `Stacks.GenPairSite.cechToK` — **the map of complexes of
  presheaves of modules `Č ⟶ K`.**

## Main results

* `Stacks.GenPairSite.quasiIso_cechLeg`, `Stacks.GenPairSite.quasiIso_cechCompare` — the two
  halves of the comparison at one object are quasi-isomorphisms, hence so is their composite.
* `Stacks.GenPairSite.evaluation_cechToK` — the sections of `Č ⟶ K` at an object are
  `Stacks.GenPairSite.cechCompare`.
* `Stacks.GenPairSite.quasiIso_evaluation_cechToK` — **`Č ⟶ K` is a quasi-isomorphism at every
  object.**
* `Stacks.GenPairSite.cechToKTerm_comp_kAugZero` — **it is compatible with the augmentations**
  onto the structure presheaf.

## Implementation notes

The reindexing `Stacks.GenFamily.singleIdx` of the product family of a singleton index onto the
family itself is not canonical — it is built from `Fintype.equivFin` — and the two reindexings
at the source and at the target of a morphism therefore have to be *compared*, which is
`Stacks.GenFamily.singleIdx_idxLe_heq`: along the equality
`GenSet.map φ (single x) = single (Gen.map φ x)` the two restrictions of a choice agree. That
comparison is the one place where the naturality of the map built here has content; everything
else is the absorption laws `Cech.genTerm_comp_genRingTerm` and
`Cech.genRingTerm_comp_genTerm` of the Čech comparison maps.

No `@[stacks]` attribute is attached: this is the Čech identification realised at the level of
complexes, which is a step towards [Stacks, Tag 099E] and not a clause of it — the tag asks for
a map in `D(𝒪)` on a ringed site, which needs the sheafification of the complex built here and
the descent of the resulting complexes along the slices.

## References

* [Stacks Project, Tag 099D](https://stacks.math.columbia.edu/tag/099D)
* [Stacks Project, Tag 099E](https://stacks.math.columbia.edu/tag/099E)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace Stacks.GenPairSite

open Stacks.GenFamily
open Stacks.PairSite (exists_dvd_fam_of_le exists_dvd_map_fam)

variable {r : ℕ}

/-! ### The Čech complex of the chosen family, as a complex of presheaves of modules -/

/-- The divisibility datum of a morphism of generated pairs: the image of a member of the chosen
family *is* the corresponding member of the target's chosen family. -/
theorem exists_dvd_elts {P Q : GenPair.{u} r} (u : P ⟶ Q) (i : Fin r) :
    ∃ n : ℕ, (GenPair.Hom.toRingHom u) (P.elts (id i)) ∣ Q.elts i ^ n := by
  refine ⟨1, ?_⟩
  have h : (GenPair.Hom.toRingHom u) (P.elts (id i)) = Q.elts i := GenPair.Hom.map_elts u i
  rw [h, pow_one]

/-- **The degree-`n` term of the Čech complex of the chosen family, as a presheaf of modules.**
Its restriction maps are the change-of-rings maps of the Čech complex, which compose on the
nose. -/
def cechTermPre (r : ℕ) (n : ℕ) : GenPairModule.{u} r where
  obj X :=
    ModuleCat.of (X.unop.unop).ring
      (Cech.cechTerm (X.unop.unop).elts (X.unop.unop).ring n)
  map {X Y} f :=
    (Cech.cechGenRingMap (GenPair.Hom.toRingHom f.unop.unop) (X.unop.unop).elts
      (Y.unop.unop).elts id (exists_dvd_elts f.unop.unop)).f n
  map_id X :=
    GenSetCech.cechGenRingMap_id_f (X.unop.unop).elts
      (exists_dvd_elts (𝟙 (X.unop.unop))) n
  map_comp {X Y Z} f g :=
    GenSetCech.cechGenRingMap_comp_f (GenPair.Hom.toRingHom f.unop.unop)
      (GenPair.Hom.toRingHom g.unop.unop) (X.unop.unop).elts (Y.unop.unop).elts
      (Z.unop.unop).elts (exists_dvd_elts f.unop.unop) (exists_dvd_elts g.unop.unop)
      (exists_dvd_elts (f.unop.unop ≫ g.unop.unop)) n

/-- The sections of `cechTermPre r n` at `X` are the degree-`n` Čech term of `X`'s family. -/
@[simp]
theorem cechTermPre_obj (n : ℕ) (X : (GenPair.{u} r)ᵒᵖᵒᵖ) :
    (cechTermPre.{u} r n).obj X =
      ModuleCat.of (X.unop.unop).ring
        (Cech.cechTerm (X.unop.unop).elts (X.unop.unop).ring n) := rfl

/-- The restriction maps of `cechTermPre r n` are the change-of-rings maps of the Čech term. -/
theorem cechTermPre_map (n : ℕ) {X Y : (GenPair.{u} r)ᵒᵖᵒᵖ} (f : X ⟶ Y) :
    (cechTermPre.{u} r n).map f =
      (Cech.cechGenRingMap (GenPair.Hom.toRingHom f.unop.unop) (X.unop.unop).elts
        (Y.unop.unop).elts id (exists_dvd_elts f.unop.unop)).f n := rfl

/-- **The Čech differential, as a map of presheaves of modules.** -/
def cechDiffPre (r : ℕ) (n : ℕ) : cechTermPre.{u} r n ⟶ cechTermPre.{u} r (n + 1) where
  app X := ModuleCat.ofHom (Cech.cechD (X.unop.unop).elts (X.unop.unop).ring n)
  naturality {X Y} f :=
    GenSetCech.cechGenRingMap_comm_f (GenPair.Hom.toRingHom f.unop.unop) (X.unop.unop).elts
      (Y.unop.unop).elts id (exists_dvd_elts f.unop.unop) n

/-- The component of `cechDiffPre r n` at `X` is the Čech differential of `X`'s family. -/
@[simp]
theorem cechDiffPre_app (n : ℕ) (X : (GenPair.{u} r)ᵒᵖᵒᵖ) :
    PresheafOfModules.Hom.app (cechDiffPre.{u} r n) X =
      ModuleCat.ofHom (Cech.cechD (X.unop.unop).elts (X.unop.unop).ring n) := rfl

/-- **The Čech complex of the chosen family, as a complex of presheaves of modules.** -/
def cechComplexPre (r : ℕ) : CochainComplex (GenPairModule.{u} r) ℕ :=
  CochainComplex.of (cechTermPre.{u} r) (cechDiffPre.{u} r) fun n =>
    PresheafOfModules.hom_ext fun X =>
      GenSetCech.cechD_comp_cechD_ofHom (X.unop.unop).elts n

/-- The degree-`n` term of `cechComplexPre r` is `cechTermPre r n`. -/
@[simp]
theorem cechComplexPre_X (n : ℕ) : (cechComplexPre.{u} r).X n = cechTermPre.{u} r n := rfl

/-- The differential of `cechComplexPre r` in degree `n` is `cechDiffPre r n`. -/
@[simp]
theorem cechComplexPre_d (n : ℕ) :
    (cechComplexPre.{u} r).d n (n + 1) = cechDiffPre.{u} r n :=
  CochainComplex.of_d _ _ n

/-- **The augmentation of the Čech complex of the chosen family onto the structure
presheaf.** -/
def cechAugZeroPre (r : ℕ) : cechTermPre.{u} r 0 ⟶ structureModule.{u} r where
  app X :=
    (LocalCohomology.cechZeroIso (X.unop.unop).elts
      (ModuleCat.of (X.unop.unop).ring (X.unop.unop).ring)).hom
  naturality {_ _} f :=
    GenSetCech.cechZeroIso_genRingMap (GenPair.Hom.toRingHom f.unop.unop) _ _ id
      (exists_dvd_elts f.unop.unop)

/-- The component of `cechAugZeroPre r` at `X` is the identification of the degree-zero Čech
term with the ring. -/
@[simp]
theorem cechAugZeroPre_app (X : (GenPair.{u} r)ᵒᵖᵒᵖ) :
    PresheafOfModules.Hom.app (cechAugZeroPre.{u} r) X =
      (LocalCohomology.cechZeroIso (X.unop.unop).elts
        (ModuleCat.of (X.unop.unop).ring (X.unop.unop).ring)).hom := rfl

/-- **The sections of the Čech complex of presheaves at an object are the Čech complex of that
object's family.** Both complexes have the same terms and the same differentials; the
identification is the identity in each degree. -/
def evalCechIso (P : GenPair.{u} r) :
    ((evaluation P).mapHomologicalComplex (ComplexShape.up ℕ)).obj (cechComplexPre.{u} r) ≅
      Cech.cechComplex P.elts P.ring :=
  HomologicalComplex.Hom.isoOfComponents (fun _ => Iso.refl _) fun i j hij => by
    obtain rfl : i + 1 = j := hij
    have h1 : (evaluation P).map (cechDiffPre.{u} r i) =
        ModuleCat.ofHom (Cech.cechD P.elts P.ring i) := rfl
    have hd : (((evaluation P).mapHomologicalComplex (ComplexShape.up ℕ)).obj
          (cechComplexPre.{u} r)).d i (i + 1) =
        (Cech.cechComplex P.elts P.ring).d i (i + 1) :=
      ((congrArg (fun w => (evaluation P).map w)
        (cechComplexPre_d.{u} (r := r) i)).trans h1).trans
        (Cech.cechComplex_d P.elts P.ring i).symm
    refine (Category.id_comp _).trans ?_
    exact hd.symm.trans (Category.comp_id _).symm

/-! ### The comparison with the product family of the singleton index -/

/-- The divisibility datum of the comparison onto the product family of the singleton index: the
product family of a singleton is the family itself, reindexed. -/
theorem exists_dvd_fam_theGen (P : GenPair.{u} r) (k : Fin (famCard (single P.theGen))) :
    ∃ n : ℕ, P.elts (singleIdx P.theGen k) ∣ fam (single P.theGen) k ^ n :=
  exists_dvd_fam_single P.theGen k

/-- **The comparison from the Čech complex of the chosen family onto the Čech complex of the
product family of the singleton index on it.** -/
def cechLeg (P : GenPair.{u} r) :
    Cech.cechComplex P.elts P.ring ⟶ Cech.cechComplex (fam (single P.theGen)) P.ring :=
  Cech.cechGenMap P.elts (fam (single P.theGen)) (singleIdx P.theGen)
    (exists_dvd_fam_theGen P) P.ring

/-- The chosen family and the product family of its singleton index span the same ideal, hence
cut out the same closed subset of the spectrum. -/
theorem zeroLocus_elts_eq (P : GenPair.{u} r) :
    PrimeSpectrum.zeroLocus ((Ideal.span (Set.range P.elts) : Ideal P.ring) : Set P.ring) =
      PrimeSpectrum.zeroLocus
        ((Ideal.span (Set.range (fam (single P.theGen))) : Ideal P.ring) : Set P.ring) :=
  (zeroLocus_span_range_fam (single P.theGen)).symm

/-- **The comparison onto the product family of the singleton index is a quasi-isomorphism**:
the two families cut out the same closed subset of the spectrum and the comparison respects the
augmentations onto the ring. -/
theorem quasiIso_cechLeg (P : GenPair.{u} r) : QuasiIso (cechLeg P) := by
  rw [← HomologicalComplex.quasiIso_extendMap_iff _ ComplexShape.embeddingUpNat]
  exact IdealCechComplex.quasiIso_of_comp_augmentation_of_zeroLocus_eq P.elts
    (fam (single P.theGen)) (ModuleCat.of P.ring P.ring) (zeroLocus_elts_eq P) _
    (IdealCechComplex.extendMap_comp_augmentation P.elts (fam (single P.theGen))
      (ModuleCat.of P.ring P.ring) _
      (Stacks.PairSite.cechZeroIso_cechGenMap P.elts (fam (single P.theGen)) (singleIdx P.theGen)
        (exists_dvd_fam_theGen P) (ModuleCat.of P.ring P.ring)))

/-- **The comparison of the Čech complex of the chosen family with the sections of the filtered
colimit at one object.** -/
def cechCompare (P : GenPair.{u} r) :
    Cech.cechComplex P.elts P.ring ⟶ sectionsNat P :=
  cechLeg P ≫ sectionsLegNat P (single P.theGen)

/-- **The comparison at one object is a quasi-isomorphism.** -/
theorem quasiIso_cechCompare (P : GenPair.{u} r) : QuasiIso (cechCompare P) :=
  have := quasiIso_cechLeg P
  have := quasiIso_sectionsLegNat P (single P.theGen)
  quasiIso_comp (cechLeg P) (sectionsLegNat P (single P.theGen))

/-! ### The transport of the singleton index along a morphism -/

/-- **The transport of the singleton index on the chosen family is the singleton index on the
target's chosen family.** -/
theorem genSet_map_single {P Q : GenPair.{u} r} (u : P ⟶ Q) :
    GenSet.map (GenPair.Hom.toRingHom u) (GenPair.Hom.map_ideal u) (single P.theGen) =
      single Q.theGen :=
  (map_single (GenPair.Hom.toRingHom u) (GenPair.Hom.map_ideal u) P.theGen).trans
    (congrArg single (GenPair.map_theGen u))

/-- The comparison of the two singleton indices, as an inequality of indices. -/
theorem single_theGen_le_map {P Q : GenPair.{u} r} (u : P ⟶ Q) :
    single Q.theGen ≤
      GenSet.map (GenPair.Hom.toRingHom u) (GenPair.Hom.map_ideal u) (single P.theGen) :=
  (genSet_map_single u).ge

/-- **The two reindexings agree**: restricting a choice to the singleton on the target's family
and restricting it along the transport are the same operation. This is the one step of the
naturality below with content. -/
theorem singleIdx_comp {P Q : GenPair.{u} r} (u : P ⟶ Q)
    (k : Fin (famCard (GenSet.map (GenPair.Hom.toRingHom u) (GenPair.Hom.map_ideal u)
      (single P.theGen)))) :
    singleIdx Q.theGen (idxLe (single_theGen_le_map u) k) =
      singleIdx P.theGen (idxMap (GenPair.Hom.toRingHom u) (GenPair.Hom.map_ideal u)
        (single P.theGen) k) :=
  eq_of_heq (singleIdx_idxLe_heq (GenPair.Hom.toRingHom u) (GenPair.Hom.map_ideal u)
    P.theGen Q.theGen (GenPair.map_theGen u).symm (single_theGen_le_map u) k)

/-! ### The divisibility data of the naturality square -/

section Naturality

variable {P Q : GenPair.{u} r}

/-- The chosen family of the source divides, through the ring map, the product family of the
singleton index on the target's chosen family. -/
theorem exists_dvd_fam_theGen_target (u : P ⟶ Q) (k : Fin (famCard (single Q.theGen))) :
    ∃ n : ℕ, (GenPair.Hom.toRingHom u) (P.elts (singleIdx Q.theGen k)) ∣
      fam (single Q.theGen) k ^ n := by
  obtain ⟨m, hm⟩ := exists_dvd_fam_theGen Q k
  refine ⟨m, ?_⟩
  have h : (GenPair.Hom.toRingHom u) (P.elts (singleIdx Q.theGen k)) =
      Q.elts (singleIdx Q.theGen k) := GenPair.Hom.map_elts u _
  exact (Eq.dvd h).trans hm

/-- The same, read against the product family of the transported index. -/
theorem exists_dvd_fam_map_target (u : P ⟶ Q)
    (k : Fin (famCard (GenSet.map (GenPair.Hom.toRingHom u) (GenPair.Hom.map_ideal u)
      (single P.theGen)))) :
    ∃ n : ℕ, (GenPair.Hom.toRingHom u)
        (P.elts ((fun j => singleIdx Q.theGen (idxLe (single_theGen_le_map u) j)) k)) ∣
      fam (GenSet.map (GenPair.Hom.toRingHom u) (GenPair.Hom.map_ideal u)
        (single P.theGen)) k ^ n := by
  obtain ⟨m, hm⟩ := exists_dvd_fam_theGen_target u (idxLe (single_theGen_le_map u) k)
  exact ⟨m, hm.trans (pow_dvd_pow_of_dvd (fam_dvd_of_le (single_theGen_le_map u) k) m)⟩

/-- The chosen family of the source divides, through the ring map, the product family of the
transported singleton index, read along the reindexing of the source. -/
theorem exists_dvd_fam_map_source (u : P ⟶ Q)
    (k : Fin (famCard (GenSet.map (GenPair.Hom.toRingHom u) (GenPair.Hom.map_ideal u)
      (single P.theGen)))) :
    ∃ n : ℕ, (GenPair.Hom.toRingHom u)
        (P.elts ((fun j => singleIdx P.theGen
          (idxMap (GenPair.Hom.toRingHom u) (GenPair.Hom.map_ideal u) (single P.theGen) j)) k)) ∣
      fam (GenSet.map (GenPair.Hom.toRingHom u) (GenPair.Hom.map_ideal u)
        (single P.theGen)) k ^ n := by
  obtain ⟨m, hm⟩ := exists_dvd_fam_theGen P
    (idxMap (GenPair.Hom.toRingHom u) (GenPair.Hom.map_ideal u) (single P.theGen) k)
  obtain ⟨c, hc⟩ := exists_dvd_map_fam (GenPair.Hom.toRingHom u) (GenPair.Hom.map_ideal u)
    (single P.theGen) k
  refine ⟨c * m, ?_⟩
  have h1 := map_dvd (GenPair.Hom.toRingHom u) hm
  rw [map_pow] at h1
  rw [pow_mul]
  exact h1.trans (pow_dvd_pow_of_dvd hc m)

end Naturality


/-! ### The map of complexes of presheaves of modules -/

/-- The comparison at one object, degreewise. -/
abbrev cechCompareTerm (P : GenPair.{u} r) (n : ℕ) :
    (Cech.cechComplex P.elts P.ring).X n ⟶ (sectionsNat P).X n :=
  (cechCompare P).f n

/-- The degree-`n` comparison is the degree-`n` component of `cechLeg P` followed by the colimit
leg at the singleton index. -/
theorem cechCompareTerm_eq (P : GenPair.{u} r) (n : ℕ) :
    cechCompareTerm P n =
      (cechLeg P).f n ≫
        colimit.ι (GenSetCech.cechTermDiagram P.ring (ideal P) n) (single P.theGen) := rfl

/-- **The comparison commutes with the differentials.** -/
theorem cechCompareTerm_comm (P : GenPair.{u} r) (n : ℕ) :
    cechCompareTerm P n ≫ GenSetCech.diffDesc P.ring (ideal P) n =
      ModuleCat.ofHom (Cech.cechD P.elts P.ring n) ≫ cechCompareTerm P (n + 1) := by
  refine ((congrArg (fun w => cechCompareTerm P n ≫ w) (sectionsNat_d P n).symm).trans
    ((cechCompare P).comm n (n + 1))).trans ?_
  exact congrArg (fun w => w ≫ cechCompareTerm P (n + 1))
    (Cech.cechComplex_d P.elts P.ring n)

/-- **The naturality of the comparison in the ring**, read on elements. The one step with
content is `Stacks.GenPairSite.singleIdx_comp`, the comparison of the two reindexings; the rest
is the two absorption laws of the Čech comparison maps together with the fact that a colimit leg
is unchanged by composing with a transition of the diagram. -/
theorem cechCompareTerm_naturality_apply {P Q : GenPair.{u} r} (u : P ⟶ Q) (n : ℕ)
    (x : Cech.cechTerm P.elts P.ring n) :
    (colimit.ι (GenSetCech.cechTermDiagram Q.ring (ideal Q) n) (single Q.theGen)).hom
        (((cechLeg Q).f n).hom
          (Cech.genRingTerm (GenPair.Hom.toRingHom u) P.elts Q.elts id
            (exists_dvd_elts u) n x)) =
      (GenSetCech.transportDesc (GenPair.Hom.toRingHom u) (GenPair.Hom.map_ideal u) n).hom
        ((colimit.ι (GenSetCech.cechTermDiagram P.ring (ideal P) n) (single P.theGen)).hom
          (((cechLeg P).f n).hom x)) := by
  have step : ∀ {I} {y z : (GenSetCech.cechTermDiagram Q.ring (ideal Q) n).obj I}, y = z →
      (colimit.ι (GenSetCech.cechTermDiagram Q.ring (ideal Q) n) I).hom y =
        (colimit.ι (GenSetCech.cechTermDiagram Q.ring (ideal Q) n) I).hom z :=
    fun h => congrArg _ h
  refine Eq.trans (step
    (LinearMap.congr_fun (Cech.genTerm_comp_genRingTerm (GenPair.Hom.toRingHom u) P.elts
      Q.elts (fam (single Q.theGen)) id (exists_dvd_elts u) (singleIdx Q.theGen)
      (exists_dvd_fam_theGen Q) (singleIdx Q.theGen) (exists_dvd_fam_theGen_target u)
      rfl n) x)) ?_
  refine Eq.trans (GenSetCech.colimit_ι_apply_of_le n
    (homOfLE (single_theGen_le_map u)) _).symm ?_
  refine Eq.trans (step
    (LinearMap.congr_fun (Cech.genTerm_comp_genRingTerm (GenPair.Hom.toRingHom u) P.elts
      (fam (single Q.theGen))
      (fam (GenSet.map (GenPair.Hom.toRingHom u) (GenPair.Hom.map_ideal u) (single P.theGen)))
      (singleIdx Q.theGen) (exists_dvd_fam_theGen_target u)
      (idxLe (single_theGen_le_map u)) (exists_dvd_fam_of_le (single_theGen_le_map u))
      (fun j => singleIdx Q.theGen (idxLe (single_theGen_le_map u) j))
      (exists_dvd_fam_map_target u) rfl n) x)) ?_
  refine Eq.trans (step
    (LinearMap.congr_fun (Cech.genRingTerm_congr (GenPair.Hom.toRingHom u) P.elts
      (fam (GenSet.map (GenPair.Hom.toRingHom u) (GenPair.Hom.map_ideal u) (single P.theGen)))
      (exists_dvd_fam_map_target u) (exists_dvd_fam_map_source u)
      (funext fun j => singleIdx_comp u j) n) x)) ?_
  refine Eq.trans (step
    (LinearMap.congr_fun (Cech.genRingTerm_comp_genTerm (GenPair.Hom.toRingHom u) P.elts
      (fam (single P.theGen))
      (fam (GenSet.map (GenPair.Hom.toRingHom u) (GenPair.Hom.map_ideal u) (single P.theGen)))
      (singleIdx P.theGen) (exists_dvd_fam_theGen P)
      (idxMap (GenPair.Hom.toRingHom u) (GenPair.Hom.map_ideal u) (single P.theGen))
      (exists_dvd_map_fam (GenPair.Hom.toRingHom u) (GenPair.Hom.map_ideal u)
        (single P.theGen))
      (fun j => singleIdx P.theGen
        (idxMap (GenPair.Hom.toRingHom u) (GenPair.Hom.map_ideal u) (single P.theGen) j))
      (exists_dvd_fam_map_source u) rfl n) x).symm) ?_
  exact (GenSetCech.transportDesc_ι_apply (GenPair.Hom.toRingHom u)
    (GenPair.Hom.map_ideal u) n (single P.theGen) (((cechLeg P).f n).hom x)).symm

/-- **The naturality of the comparison in the ring.** -/
theorem cechCompareTerm_naturality {P Q : GenPair.{u} r} (u : P ⟶ Q) (n : ℕ) :
    (Cech.cechGenRingMap (GenPair.Hom.toRingHom u) P.elts Q.elts id (exists_dvd_elts u)).f n ≫
        (ModuleCat.restrictScalars (GenPair.Hom.toRingHom u)).map (cechCompareTerm Q n) =
      cechCompareTerm P n ≫
        GenSetCech.transportDesc (GenPair.Hom.toRingHom u) (GenPair.Hom.map_ideal u) n :=
  ModuleCat.hom_ext (LinearMap.ext fun x => cechCompareTerm_naturality_apply u n x)

/-- **The degree-`n` component of the comparison `Č ⟶ K`, as a map of presheaves of
modules.** -/
def cechToKTerm (r : ℕ) (n : ℕ) : cechTermPre.{u} r n ⟶ kTerm.{u} (r := r) n where
  app X := cechCompareTerm (X.unop.unop) n
  naturality {_ _} f := cechCompareTerm_naturality f.unop.unop n

/-- The component of `cechToKTerm r n` at `X` is `cechCompareTerm` at `X`. -/
@[simp]
theorem cechToKTerm_app (n : ℕ) (X : (GenPair.{u} r)ᵒᵖᵒᵖ) :
    PresheafOfModules.Hom.app (cechToKTerm.{u} r n) X = cechCompareTerm (X.unop.unop) n := rfl

/-- The component at `X` of the differential of `kComplexNat r` in degree `n` is the
differential of the colimit at `X`. -/
theorem kComplexNat_d_app (n : ℕ) (X : (GenPair.{u} r)ᵒᵖᵒᵖ) :
    PresheafOfModules.Hom.app ((kComplexNat.{u} r).d n (n + 1)) X =
      GenSetCech.diffDesc (X.unop.unop).ring (ideal X.unop.unop) n :=
  congrArg (fun w => PresheafOfModules.Hom.app w X) (kComplexNat_d.{u} (r := r) n)

/-- The component at `X` of the differential of `cechComplexPre r` in degree `n` is the Čech
differential of `X`'s family. -/
theorem cechComplexPre_d_app (n : ℕ) (X : (GenPair.{u} r)ᵒᵖᵒᵖ) :
    PresheafOfModules.Hom.app ((cechComplexPre.{u} r).d n (n + 1)) X =
      ModuleCat.ofHom (Cech.cechD (X.unop.unop).elts (X.unop.unop).ring n) :=
  congrArg (fun w => PresheafOfModules.Hom.app w X) (cechComplexPre_d.{u} (r := r) n)

/-- **The comparison `Č ⟶ K`: a map of complexes of presheaves of modules.** -/
def cechToK (r : ℕ) : cechComplexPre.{u} r ⟶ kComplexNat.{u} r where
  f n := cechToKTerm.{u} r n
  comm' n m hnm := by
    obtain rfl : n + 1 = m := hnm
    refine PresheafOfModules.hom_ext fun X => ?_
    refine Eq.trans (congrArg (fun w => cechCompareTerm (X.unop.unop) n ≫ w)
      (kComplexNat_d_app.{u} (r := r) n X)) ?_
    refine Eq.trans ?_ (congrArg (fun w => w ≫ cechCompareTerm (X.unop.unop) (n + 1))
      (cechComplexPre_d_app.{u} (r := r) n X)).symm
    exact cechCompareTerm_comm (X.unop.unop) n

/-- **The sections of the comparison `Č ⟶ K` at an object are the comparison of the Čech
complex of that object's family with the filtered colimit.** -/
theorem evaluation_cechToK (P : GenPair.{u} r) (n : ℕ) :
    (evaluation P).map ((cechToK.{u} r).f n) = cechCompareTerm P n := rfl

/-- **The comparison `Č ⟶ K` is a quasi-isomorphism at every object.** -/
theorem quasiIso_evaluation_cechToK (P : GenPair.{u} r) :
    QuasiIso (((evaluation P).mapHomologicalComplex (ComplexShape.up ℕ)).map
      (cechToK.{u} r)) := by
  have hfac : ((evaluation P).mapHomologicalComplex (ComplexShape.up ℕ)).map (cechToK.{u} r) =
      (evalCechIso P).hom ≫ cechCompare P :=
    HomologicalComplex.hom_ext _ _ fun n =>
      (evaluation_cechToK P n).trans (Category.id_comp _).symm
  have := quasiIso_cechCompare P
  have h2 : QuasiIso ((evalCechIso P).hom ≫ cechCompare P) :=
    quasiIso_comp (evalCechIso P).hom (cechCompare P) (hφ := quasiIso_of_isIso _)
  rw [hfac]
  exact h2

/-- **The comparison `Č ⟶ K` is compatible with the two augmentations onto the structure
presheaf.** -/
theorem cechToKTerm_comp_kAugZero (r : ℕ) :
    cechToKTerm.{u} r 0 ≫ kAugZero.{u} r = cechAugZeroPre.{u} r :=
  PresheafOfModules.hom_ext fun X =>
    (Category.assoc _ _ _).trans
      ((congrArg (fun w => (cechLeg (X.unop.unop)).f 0 ≫ w)
          (GenSetCech.ι_augDesc (single (X.unop.unop).theGen))).trans
        (Stacks.PairSite.cechZeroIso_cechGenMap (X.unop.unop).elts
          (fam (single (X.unop.unop).theGen)) (singleIdx (X.unop.unop).theGen)
          (exists_dvd_fam_theGen (X.unop.unop))
          (ModuleCat.of (X.unop.unop).ring (X.unop.unop).ring)))

end Stacks.GenPairSite

end
