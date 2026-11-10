module

public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.Algebra.Category.Ring.FinitePresentation
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Mathlib.CategoryTheory.Limits.Preserves.Over
public import Mathlib.CategoryTheory.Presentable.Directed
public import Mathlib.RingTheory.Etale.Weakly
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import Mathlib.Topology.Irreducible
public import StacksFrontier.AlgebraicGeometry.Morphisms.EtaleNeighbourhood.Henselization
public import StacksFrontier.AlgebraicGeometry.Morphisms.EtaleNeighbourhood.MinimalPrimesDirectLimit
public import StacksFrontier.AlgebraicGeometry.Properties.Unibranch
public import StacksFrontier.RingTheory.Henselian.StrictHenselizationColimit
public import StacksFrontier.RingTheory.Etale.FilteredColimit.Basic
public import StacksFrontier.RingTheory.Etale.IndEtaleUniverse
public import StacksFrontier.RingTheory.Flat.FaithfullyFlat.Basic
public import StacksFrontier.RingTheory.Henselian.Henselization.EtaleNeighborhood
public import StacksFrontier.RingTheory.Henselian.StrictHenselization.QuasiFinite
public import StacksFrontier.RingTheory.Spectrum.Prime.IrreducibleComponents
public import StacksFrontier.RingTheory.Spectrum.Prime.Surjective
public import StacksCore.Tactic.StacksAttribute

/-!
# Branches and geometric branches as suprema over étale neighbourhoods

The number of branches of a scheme at a point is the supremum, over the elementary étale
neighbourhoods of that point, of the number of irreducible components through the distinguished
point; the number of geometric branches is the analogous supremum over all étale neighbourhoods.
Both statements come from the description of the henselization — respectively the strict
henselization — of the local ring as a filtered colimit of the rings of global sections of those
neighbourhoods (Tag 05KS): a faithfully flat map of local rings does not decrease the number of
minimal primes, and every finite family of minimal primes of the colimit is already separated at
some stage.

## Main results

* `AlgebraicGeometry.numberOfBranches_eq_iSup_encard_irreducibleComponentsThrough`: the number of
  branches is the supremum of the numbers of irreducible components through the distinguished
  points of the elementary étale neighbourhoods.
* `AlgebraicGeometry.numberOfGeometricBranches_eq_iSup_encard`: the number of geometric branches
  is the supremum of the same counts over all étale neighbourhoods.

## Implementation notes

The number of components through a point is expressed as the extended cardinality of the
corresponding subset of Mathlib's `irreducibleComponents`, which at the level of local rings is
the set of minimal primes of the stalk. A henselization and a strict henselization of the local
ring are taken to be the chosen models `henselizationData` and `strictHenselizationData`.

## References

* [Stacks Project, Tag 0CB4](https://stacks.math.columbia.edu/tag/0CB4)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits IsLocalRing

universe u v w

namespace AlgebraicGeometry

/-- A flat local homomorphism of local rings is faithfully flat.

This is Mathlib's `Module.FaithfullyFlat.of_flat_of_isLocalHom`, transported from the
`Module.Flat` formulation to the `RingHom.Flat` one. -/
@[ega "0 6.6.1" "(e) ⇒ (a), special case",
  ega "0 6.6.2" "partial, special case",
  sga "1 IV 2.2" "special case",
  sga "1 IV 2.6" "(i), special case"]
private theorem faithfullyFlat_of_flat_of_isLocalHom {R S : Type*} [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S] (f : R →+* S) [IsLocalHom f] (hf : f.Flat) :
    f.FaithfullyFlat := by
  let : Algebra R S := f.toAlgebra
  have : Module.Flat R S := hf
  have : IsLocalHom (algebraMap R S) := ‹IsLocalHom f›
  exact Module.FaithfullyFlat.of_flat_of_isLocalHom

private theorem comap_mem_minimalPrimes_of_faithfullyFlat
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Module.FaithfullyFlat R S] {q : Ideal S} (hq : q ∈ minimalPrimes S) :
    Ideal.comap (algebraMap R S) q ∈ minimalPrimes R := by
  let : Algebra.HasGoingDown R S := Algebra.HasGoingDown.of_flat
  have hqprime : q.IsPrime := hq.isPrime
  let p : Ideal R := Ideal.comap (algebraMap R S) q
  have hpprime : p.IsPrime := Ideal.IsPrime.comap _
  change Minimal (fun r : Ideal R => r.IsPrime ∧ (⊥ : Ideal R) ≤ r) p
  refine ⟨⟨hpprime, bot_le⟩, ?_⟩
  intro p₀ hp₀ hp₀le
  by_contra hne
  have hlt : p₀ < p := lt_of_le_of_ne hp₀le (fun h => hne h.ge)
  have hp₀prime : p₀.IsPrime := hp₀.1
  have hlt' : p₀ < Ideal.under R q := by
    change p₀ < q.comap (algebraMap R S)
    exact hlt
  obtain ⟨P, hPle, hPprime, hPlies⟩ :=
    Algebra.HasGoingDown.exists_ideal_le_liesOver_of_lt q hlt'
  have hqP : q ≤ P := hq.2 ⟨hPprime, bot_le⟩ hPle
  have hpP : p ≤ P.comap (algebraMap R S) := Ideal.comap_mono hqP
  have hPunder : P.comap (algebraMap R S) = p₀ := by
    have h := hPlies.over
    change p₀ = P.comap (algebraMap R S) at h
    exact h.symm
  rw [hPunder] at hpP
  exact hne hpP

private theorem exists_minimalPrime_comap_eq_of_faithfullyFlat
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Module.FaithfullyFlat R S] (p : Ideal R) (hp : p ∈ minimalPrimes R) :
    ∃ q ∈ minimalPrimes S, Ideal.comap (algebraMap R S) q = p := by
  obtain ⟨P, hP⟩ := PrimeSpectrum.comap_surjective_of_faithfullyFlat (A := R) (B := S)
    ⟨p, hp.isPrime⟩
  have hPas := congrArg PrimeSpectrum.asIdeal hP
  change Ideal.comap (algebraMap R S) P.asIdeal = p at hPas
  obtain ⟨q, hq, hqP⟩ := Ideal.exists_minimalPrimes_le
    (I := (⊥ : Ideal S)) (J := P.asIdeal) bot_le
  have hle : Ideal.comap (algebraMap R S) q ≤ p := by
    rw [← hPas]
    exact Ideal.comap_mono hqP
  exact ⟨q, hq, le_antisymm hle (hp.2 ⟨(comap_mem_minimalPrimes_of_flat _
    (RingHom.flat_algebraMap_iff.mpr inferInstance) hq).isPrime, bot_le⟩ hle)⟩

private theorem encard_minimalPrimes_le_of_faithfullyFlat
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Module.FaithfullyFlat R S] :
    Set.encard (minimalPrimes R) ≤ Set.encard (minimalPrimes S) :=
  (Set.encard_le_encard (t := Ideal.comap (algebraMap R S) '' minimalPrimes S)
    fun p hp => exists_minimalPrime_comap_eq_of_faithfullyFlat p hp).trans
    (Set.encard_image_le _ _)

private theorem encard_minimalPrimes_localization_eq_of_ideal_eq
    {R : Type u} [CommRing R] (I J : Ideal R) [I.IsPrime] [J.IsPrime] (h : I = J) :
    Set.encard (minimalPrimes (Localization.AtPrime I)) =
      Set.encard (minimalPrimes (Localization.AtPrime J)) := by
  cases h
  rfl

private abbrev algebraCoconeRange {R : Type u} [CommRing R] {J : Type v} [Category.{w} J]
    {F : J ⥤ CommAlgCat.{u} R} (c : Cocone F) (j : J) :
    Subalgebra R (c.pt : Type u) := (c.ι.app j).hom.range

private theorem directed_algebraCoconeRange {R : Type u} [CommRing R]
    {J : Type v} [Category.{w} J] [IsFilteredOrEmpty J] {F : J ⥤ CommAlgCat.{u} R}
    (c : Cocone F) : Directed (· ≤ ·) (algebraCoconeRange c) := by
  have hle : ∀ {i j : J}, (i ⟶ j) → algebraCoconeRange c i ≤ algebraCoconeRange c j := by
    rintro i j f y ⟨a, rfl⟩
    exact ⟨(F.map f).hom a, ConcreteCategory.congr_hom (c.w f) a⟩
  exact fun i j => ⟨IsFiltered.max i j, hle (IsFiltered.leftToMax i j),
    hle (IsFiltered.rightToMax i j)⟩

private theorem iSup_algebraCoconeRange_eq_top {R : Type u} [CommRing R]
    {J : Type v} [Category.{w} J] {F : J ⥤ CommAlgCat.{u} R}
    (c : Cocone F) (hc : IsColimit c) : ⨆ j, algebraCoconeRange c j = ⊤ := by
  set T := ⨆ j, algebraCoconeRange c j
  have hmem (j : J) (y : (F.obj j : Type u)) : (c.ι.app j).hom y ∈ T :=
    le_iSup (algebraCoconeRange c) j ⟨y, rfl⟩
  let d : Cocone F :=
    { pt := CommAlgCat.of R T
      ι.app j := CommAlgCat.ofHom ((c.ι.app j).hom.codRestrict T (hmem j))
      ι.naturality i j f := by
        apply CommAlgCat.hom_ext
        ext a
        exact Subtype.ext (ConcreteCategory.congr_hom (c.w f) a) }
  have hid : hc.desc d ≫ CommAlgCat.ofHom T.val = 𝟙 _ := by
    refine hc.hom_ext fun j => ?_
    rw [← Category.assoc, hc.fac, Category.comp_id]
    apply CommAlgCat.hom_ext
    ext a
    rfl
  refine eq_top_iff.2 fun x _ => ?_
  have h : T.val ((hc.desc d).hom x) = x := ConcreteCategory.congr_hom hid x
  exact h ▸ ((hc.desc d).hom x).property

private theorem exists_algebraCocone_rep {R : Type u} [CommRing R]
    {J : Type v} [Category.{w} J] [IsFiltered J] {F : J ⥤ CommAlgCat.{u} R}
    (c : Cocone F) (hc : IsColimit c) (x : (c.pt : Type u)) :
    ∃ j : J, ∃ y : (F.obj j : Type u), (c.ι.app j).hom y = x := by
  have : Nonempty J := IsFiltered.nonempty
  have hx : x ∈ (↑(⨆ j, algebraCoconeRange c j) : Set (c.pt : Type u)) := by
    rw [iSup_algebraCoconeRange_eq_top c hc]
    trivial
  rw [Subalgebra.coe_iSup_of_directed (directed_algebraCoconeRange c)] at hx
  obtain ⟨_, ⟨j, rfl⟩, y, hy⟩ := hx
  exact ⟨j, y, hy⟩




private theorem encard_minimalPrimes_of_directedColimit
    {R : Type u} [CommRing R] {ι : Type v} [PartialOrder ι]
    [IsDirected ι (· ≤ ·)] [Nonempty ι] (F : ι ⥤ CommAlgCat.{u} R)
    (c : Cocone F) (hc : IsColimit c)
    (hff : ∀ i j (f : i ⟶ j), (F.map f).hom.FaithfullyFlat)
    (hinj : ∀ i, Function.Injective (c.ι.app i).hom) :
    Set.encard (minimalPrimes (c.pt : Type u)) =
      ⨆ i, Set.encard (minimalPrimes (F.obj i : Type u)) := by
  classical
  let A : ι → Type u := fun i => F.obj i
  let f : (i j : ι) → i ≤ j → A i →+* A j := fun i j h =>
    (F.map (homOfLE h)).hom.toRingHom
  have hfid (i : ι) : f i i le_rfl = RingHom.id (A i) := by
    ext x
    have hi : homOfLE (le_rfl : i ≤ i) = 𝟙 i := Subsingleton.elim _ _
    change (F.map (homOfLE (le_rfl : i ≤ i))).hom x = x
    rw [hi, F.map_id]
    rfl
  have hcomp (i j k : ι) (hij : i ≤ j) (hjk : j ≤ k) :
      (f j k hjk).comp (f i j hij) = f i k (hij.trans hjk) := by
    have hm : homOfLE hij ≫ homOfLE hjk = homOfLE (hij.trans hjk) := Subsingleton.elim _ _
    have hmap : F.map (homOfLE hij) ≫ F.map (homOfLE hjk) =
        F.map (homOfLE (hij.trans hjk)) := by
      rw [← F.map_comp, hm]
    ext x
    exact congrArg (fun g => g.hom x) hmap
  have : DirectedSystem A (fun i j h => (f i j h : A i → A j)) :=
    ⟨fun i x => DFunLike.congr_fun (hfid i) x,
      fun _ _ _ hij hjk x => DFunLike.congr_fun (hcomp _ _ _ hij hjk) x⟩
  let g : (i : ι) → A i →+* (c.pt : Type u) := fun i => (c.ι.app i).hom.toRingHom
  have hg (i j : ι) (h : i ≤ j) (x : A i) : g j (f i j h x) = g i x :=
    ConcreteCategory.congr_hom (c.w (homOfLE h)) x
  let e : Ring.DirectLimit A (fun i j h => (f i j h : A i → A j)) →+* (c.pt : Type u) :=
    Ring.DirectLimit.lift A (fun i j h => (f i j h : A i →+* A j)) _ g hg
  have heinj : Function.Injective e := by
    apply Ring.DirectLimit.lift_injective
    intro i x y hxy
    exact hinj i hxy
  have hesurj : Function.Surjective e := by
    intro x
    obtain ⟨i, y, hy⟩ := exists_algebraCocone_rep c hc x
    refine ⟨Ring.DirectLimit.of A (fun i j h => (f i j h : A i → A j)) i y, ?_⟩
    rw [Ring.DirectLimit.lift_of]
    exact hy
  let er : Ring.DirectLimit A (fun i j h => (f i j h : A i → A j)) ≃+* (c.pt : Type u) :=
    RingEquiv.ofBijective e ⟨heinj, hesurj⟩
  rw [← Set.encard_congr (minimalPrimes_equiv_of_ringEquiv er)]
  exact _root_.encard_minimalPrimes_directLimit A f fun i j h => hff i j (homOfLE h)

private noncomputable def isColimitForget₂CommAlgCat
    {R : Type u} [CommRing R] {J : Type v} [Category.{w} J] [IsConnected J]
    {F : J ⥤ CommAlgCat.{u} R} {c : Cocone F} (hc : IsColimit c) :
    IsColimit ((forget₂ (CommAlgCat.{u} R) CommRingCat.{u}).mapCocone c) := by
  classical
  refine IsColimit.ofExistsUnique fun s => ?_
  obtain ⟨a, ha⟩ := constant_of_preserves_morphisms' (α := R →+* s.pt)
    (fun j => (s.ι.app j).hom.comp (algebraMap R (F.obj j))) (by
      intro i j f
      ext r
      change (s.ι.app i).hom (algebraMap R (F.obj i) r) =
        (s.ι.app j).hom (algebraMap R (F.obj j) r)
      have hw := congrArg (fun q => q.hom (algebraMap R (F.obj i) r)) (s.w f)
      simpa using hw.symm)
  let _ : Algebra R s.pt := a.toAlgebra
  let s' : Cocone F :=
    { pt := CommAlgCat.of R s.pt
      ι :=
        { app := fun j => CommAlgCat.ofHom
            { toRingHom := (s.ι.app j).hom
              commutes' := fun r => RingHom.congr_fun (ha j) r }
          naturality := fun i j f => by
            ext x
            exact congrArg (fun q => q.hom x) (s.w f) } }
  refine ⟨CommRingCat.ofHom (hc.desc s').hom.toRingHom, ?_, ?_⟩
  · intro j
    ext x
    exact congrArg (fun q => q.hom x) (hc.fac s' j)
  · intro m hm
    let m' : c.pt ⟶ s'.pt := CommAlgCat.ofHom
      { toRingHom := m.hom
        commutes' := fun r => by
          let j : J := Classical.arbitrary J
          change m.hom (algebraMap R c.pt r) = a r
          calc
            _ = m.hom ((c.ι.app j).hom (algebraMap R (F.obj j) r)) := by
              rw [AlgHom.commutes]
              rfl
            _ = (s.ι.app j).hom (algebraMap R (F.obj j) r) :=
              congrArg (fun q => q.hom (algebraMap R (F.obj j) r)) (hm j)
            _ = a r := RingHom.congr_fun (ha j) r }
    have he : m' = hc.desc s' := hc.uniq s' m' (fun j => by
      ext x
      exact congrArg (fun q => q.hom x) (hm j))
    exact congrArg (fun q => CommRingCat.ofHom q.hom.toRingHom) he

private theorem encard_minimalPrimes_of_filteredColimit
    {R : Type u} [CommRing R] {J : Type u} [SmallCategory J] [IsFiltered J]
    (F : J ⥤ CommAlgCat.{u} R) (c : Cocone F) (hc : IsColimit c)
    (hff : ∀ i j (f : i ⟶ j), (F.map f).hom.FaithfullyFlat) :
    Set.encard (minimalPrimes (c.pt : Type u)) =
      ⨆ j, Set.encard (minimalPrimes (F.obj j : Type u)) := by
  classical
  obtain ⟨ι, _, _, _, H, hH⟩ := IsFiltered.exists_directed J
  let F' : ι ⥤ CommAlgCat.{u} R := H ⋙ F
  let c' : Cocone F' := c.whisker H
  have hc' : IsColimit c' := (Functor.Final.isColimitWhiskerEquiv H c).symm hc
  have hff' (i j : ι) (f : i ⟶ j) : (F'.map f).hom.FaithfullyFlat :=
    hff (H.obj i) (H.obj j) (H.map f)
  let : IsConnected ι := IsFiltered.isConnected ι
  have hcRing := isColimitForget₂CommAlgCat hc'
  let : PreservesFilteredColimits (forget CommRingCat.{u}) := by infer_instance
  have hcTypes : IsColimit
      ((forget CommRingCat.{u}).mapCocone
        ((forget₂ (CommAlgCat.{u} R) CommRingCat.{u}).mapCocone c')) :=
    isColimitOfPreserves (forget CommRingCat.{u}) hcRing
  have hinj' (i : ι) : Function.Injective (c'.ι.app i).hom := by
    intro x y hxy
    obtain ⟨k, f, hxy'⟩ := (Types.FilteredColimit.isColimit_eq_iff' hcTypes x y).mp hxy
    exact (hff' i k f).injective hxy'
  have hdir := encard_minimalPrimes_of_directedColimit F' c' hc' hff' hinj'
  have hobj : ∀ j : J, ∃ i : ι, Nonempty (j ⟶ H.obj i) :=
    (Functor.final_iff_of_isFiltered H).mp hH |>.1
  have hsup : (⨆ j, Set.encard (minimalPrimes (F.obj j : Type u))) =
      ⨆ i, Set.encard (minimalPrimes (F'.obj i : Type u)) := by
    apply le_antisymm
    · apply iSup_le
      intro j
      obtain ⟨i, ⟨f⟩⟩ := hobj j
      calc
        Set.encard (minimalPrimes (F.obj j : Type u)) ≤
            Set.encard (minimalPrimes (F.obj (H.obj i) : Type u)) := by
          let : Algebra (F.obj j : Type u) (F.obj (H.obj i) : Type u) :=
            (F.map f).hom.toRingHom.toAlgebra
          let : Module.FaithfullyFlat (F.obj j : Type u) (F.obj (H.obj i) : Type u) := hff j _ f
          exact encard_minimalPrimes_le_of_faithfullyFlat
        _ ≤ ⨆ i, Set.encard (minimalPrimes (F'.obj i : Type u)) :=
          le_iSup (fun i => Set.encard (minimalPrimes (F'.obj i : Type u))) i
    · exact iSup_le fun i =>
        le_iSup (fun j => Set.encard (minimalPrimes (F.obj j : Type u))) (H.obj i)
  exact hdir.trans hsup.symm

private theorem faithfullyFlat_localizationMap_augmentedEtale
    {R L : Type u} [CommRing R] [Field L] [Algebra R L]
    (A B : CommAlgCat.AugmentedEtale R L) (f : A ⟶ B) :
    ((CommAlgCat.AugmentedEtale.localization R L).map f).hom.FaithfullyFlat := by
  let S := (A.left.obj : Type u)
  let T := (B.left.obj : Type u)
  let : Algebra S T := (CommAlgCat.AugmentedEtale.map f).toRingHom.toAlgebra
  have : IsScalarTower R S T := .of_algebraMap_eq fun r =>
    ((CommAlgCat.AugmentedEtale.map f).commutes r).symm
  have hetale : Algebra.Etale S T := Algebra.Etale.of_restrictScalars R S T
  let P := Localization.AtPrime A.prime
  let Q := Localization.AtPrime B.prime
  let : Algebra P Q :=
    (Localization.localRingHom A.prime B.prime (CommAlgCat.AugmentedEtale.map f).toRingHom
      (CommAlgCat.AugmentedEtale.prime_eq_comap f)).toAlgebra
  let : Algebra T Q := inferInstance
  let : IsScalarTower S T Q := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower S P Q := IsScalarTower.of_algebraMap_eq fun s => by
    change algebraMap S Q s = algebraMap P Q (algebraMap S P s)
    rw [IsScalarTower.algebraMap_apply S T Q,
      RingHom.algebraMap_toAlgebra (CommAlgCat.AugmentedEtale.map f).toRingHom,
      show algebraMap P Q = Localization.localRingHom A.prime B.prime
        (CommAlgCat.AugmentedEtale.map f).toRingHom
        (CommAlgCat.AugmentedEtale.prime_eq_comap f) from RingHom.algebraMap_toAlgebra _,
      Localization.localRingHom_to_map A.prime B.prime
        (CommAlgCat.AugmentedEtale.map f).toRingHom
        (CommAlgCat.AugmentedEtale.prime_eq_comap f) s]
  have hflatST : Module.Flat S Q := by
    let : Module.Flat S T := inferInstance
    let : Module.Flat T Q := IsLocalization.flat Q B.prime.primeCompl
    exact Module.Flat.trans S T Q
  have hflat : Module.Flat P Q :=
    (Module.flat_iff_of_isLocalization P A.prime.primeCompl Q).2 hflatST
  let : IsLocalHom (algebraMap P Q) :=
    Localization.isLocalHom_localRingHom A.prime B.prime
      (CommAlgCat.AugmentedEtale.map f).toRingHom
      (CommAlgCat.AugmentedEtale.prime_eq_comap f)
  exact faithfullyFlat_of_flat_of_isLocalHom (algebraMap P Q)
    (RingHom.flat_algebraMap_iff.mpr hflat)

private noncomputable def isColimit_localizedStages_augmentedEtale
    {R L : Type u} [CommRing R] [Field L] [Algebra R L]
    {J : Type u} [SmallCategory J]
    (G : J ⥤ CommAlgCat.AugmentedEtale R L)
    (c : Cocone (G ⋙ CommAlgCat.AugmentedEtale.forget R L)) (hc : IsColimit c)
    (ι : (G ⋙ CommAlgCat.AugmentedEtale.localization R L) ⟶
      (Functor.const J).obj c.pt)
    (hfac : ∀ j, (CommAlgCat.AugmentedEtale.toLocalization R L).app (G.obj j) ≫
      ι.app j = c.ι.app j) :
    IsColimit (Cocone.mk c.pt ι) := by
  classical
  let d : Cocone (G ⋙ CommAlgCat.AugmentedEtale.localization R L) := Cocone.mk c.pt ι
  refine IsColimit.ofExistsUnique fun t => ?_
  let d' : Cocone (G ⋙ CommAlgCat.AugmentedEtale.forget R L) :=
    { pt := t.pt
      ι :=
        { app := fun j =>
          (CommAlgCat.AugmentedEtale.toLocalization R L).app (G.obj j) ≫ t.ι.app j
          naturality := fun i j f => by
            simp only [Functor.comp_obj, Functor.comp_map]
            calc
              _ = (((CommAlgCat.AugmentedEtale.forget R L).map (G.map f) ≫
                    (CommAlgCat.AugmentedEtale.toLocalization R L).app (G.obj j)) ≫
                  t.ι.app j) := by simp [Category.assoc]
              _ = (((CommAlgCat.AugmentedEtale.toLocalization R L).app (G.obj i) ≫
                    (CommAlgCat.AugmentedEtale.localization R L).map (G.map f)) ≫
                  t.ι.app j) := by
                rw [(CommAlgCat.AugmentedEtale.toLocalization R L).naturality (G.map f)]
              _ = (CommAlgCat.AugmentedEtale.toLocalization R L).app (G.obj i) ≫
                    ((CommAlgCat.AugmentedEtale.localization R L).map (G.map f) ≫
                      t.ι.app j) := by simp [Category.assoc]
              _ = (CommAlgCat.AugmentedEtale.toLocalization R L).app (G.obj i) ≫
                    t.ι.app i := by
                have htw : (CommAlgCat.AugmentedEtale.localization R L).map (G.map f) ≫
                    t.ι.app j = t.ι.app i := by
                  simpa only [Functor.comp_map] using t.w f
                exact congrArg
                  (fun g => (CommAlgCat.AugmentedEtale.toLocalization R L).app (G.obj i) ≫ g)
                  htw } }
  have hfacLoc (j) : d.ι.app j ≫ hc.desc d' = t.ι.app j := by
    let : Algebra (G.obj j).left.obj ((G ⋙ CommAlgCat.AugmentedEtale.localization R L).obj j) := by
      change Algebra (G.obj j).left.obj (Localization.AtPrime (G.obj j).prime)
      infer_instance
    let : IsLocalization (G.obj j).prime.primeCompl
        ((G ⋙ CommAlgCat.AugmentedEtale.localization R L).obj j) := by
      change IsLocalization (G.obj j).prime.primeCompl
        (Localization.AtPrime (G.obj j).prime)
      infer_instance
    let : IsScalarTower R (G.obj j).left.obj
        ((G ⋙ CommAlgCat.AugmentedEtale.localization R L).obj j) := by
      change IsScalarTower R (G.obj j).left.obj (Localization.AtPrime (G.obj j).prime)
      infer_instance
    apply CommAlgCat.hom_ext
    apply IsLocalization.algHom_ext (G.obj j).prime.primeCompl
    apply congrArg CommAlgCat.Hom.hom
    calc
      (CommAlgCat.AugmentedEtale.toLocalization R L).app (G.obj j) ≫
          (d.ι.app j ≫ hc.desc d') =
          ((CommAlgCat.AugmentedEtale.toLocalization R L).app (G.obj j) ≫
            ι.app j) ≫ hc.desc d' := by rfl
      _ = c.ι.app j ≫ hc.desc d' := by rw [hfac j]
      _ = d'.ι.app j := hc.fac d' j
      _ = (CommAlgCat.AugmentedEtale.toLocalization R L).app (G.obj j) ≫ t.ι.app j := rfl
  refine ⟨hc.desc d', hfacLoc, ?_⟩
  intro m hm
  apply hc.hom_ext
  intro j
  calc
    c.ι.app j ≫ m =
        ((CommAlgCat.AugmentedEtale.toLocalization R L).app (G.obj j) ≫
          ι.app j) ≫ m := by rw [hfac j]
    _ = (CommAlgCat.AugmentedEtale.toLocalization R L).app (G.obj j) ≫
        (d.ι.app j ≫ m) := by rfl
    _ = (CommAlgCat.AugmentedEtale.toLocalization R L).app (G.obj j) ≫ t.ι.app j := by
      rw [hm j]
    _ = (CommAlgCat.AugmentedEtale.toLocalization R L).app (G.obj j) ≫
        (d.ι.app j ≫ hc.desc d') := by rw [← hfacLoc j]
    _ = c.ι.app j ≫ hc.desc d' := by rw [← Category.assoc, hfac j]


private theorem encard_irreducibleComponentsThrough_eq_minimalPrimes_stalk
    (X : AlgebraicGeometry.Scheme.{u}) (x : X) :
    Set.encard {Z : Set X | Z ∈ irreducibleComponents X ∧ x ∈ Z} =
      Set.encard (minimalPrimes (X.presheaf.stalk x)) := by
  classical
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, _⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (a := x) (by trivial) isOpen_univ
  let : IsOpenImmersion hV.fromSpec := hV.isOpenImmersion_fromSpec
  let p : PrimeSpectrum Γ(X, V) := hV.primeIdealOf ⟨x, hxV⟩
  have hp : hV.fromSpec p = x := hV.fromSpec_primeIdealOf ⟨x, hxV⟩
  let ePoint : {Z : irreducibleComponents X // x ∈ (Z : Set X)} ≃
    {Z : irreducibleComponents X // hV.fromSpec p ∈ (Z : Set X)} :=
    { toFun := fun Z => ⟨Z.1, by simpa [hp] using Z.2⟩
      invFun := fun Z => ⟨Z.1, by simpa [hp] using Z.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let eOpen := irreducibleComponentsThrough_equiv_of_isOpenEmbedding
    hV.fromSpec.isOpenEmbedding p
  let eAffine : PrimeSpectrum.irreducibleComponentsThrough Γ(X, V) p.asIdeal ≃
      minimalPrimes (Localization.AtPrime p.asIdeal) :=
    PrimeSpectrum.irreducibleComponentsThroughEquiv (Γ(X, V)) p.asIdeal
      (Localization.AtPrime p.asIdeal)
  let : Algebra Γ(X, V) (X.presheaf.stalk x) :=
    (X.presheaf.germ V x hxV).hom.toAlgebra
  let : IsLocalization.AtPrime (X.presheaf.stalk x) p.asIdeal :=
    hV.isLocalization_stalk ⟨x, hxV⟩
  let eStalk : Localization.AtPrime p.asIdeal ≃+* X.presheaf.stalk x :=
    (IsLocalization.algEquiv p.asIdeal.primeCompl (Localization.AtPrime p.asIdeal)
      (X.presheaf.stalk x)).toRingEquiv
  let eCompSpec : {Z : irreducibleComponents (PrimeSpectrum Γ(X, V)) //
      p ∈ (Z : Set (PrimeSpectrum Γ(X, V)))} ≃
      PrimeSpectrum.irreducibleComponentsThrough Γ(X, V) p.asIdeal :=
    { toFun := fun Z => ⟨Z.1, Z.1.property, Z.2⟩
      invFun := fun Z => ⟨⟨Z.1, Z.2.1⟩, Z.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  exact Set.encard_congr <| (componentThrough_equiv_subtype x).trans
    (ePoint.trans (eOpen.trans (eCompSpec.trans (eAffine.trans
      (minimalPrimes_equiv_of_ringEquiv eStalk)))))

private theorem ind_etale_of_base_equiv
    {R S A : Type u} [CommRing R] [CommRing S] [CommRing A]
    [Algebra R A] [Algebra S A] (e : S ≃+* R)
    (he : ∀ s, algebraMap S A s = algebraMap R A (e s))
    (h : (CommAlgCat.etale R).ind.{u} (CommAlgCat.of R A)) :
    (CommAlgCat.etale S).ind.{u} (CommAlgCat.of S A) := by
  let E := (commAlgCatEquivUnder (.of R)).trans
    ((Under.mapIso e.toCommRingCatIso).trans (commAlgCatEquivUnder (.of S)).symm)
  obtain ⟨J, _, _, pres, hp⟩ := h
  refine ⟨J, inferInstance, inferInstance, (pres.map E.functor).ofIso ?_, fun j => ?_⟩
  · let B : CommAlgCat S := E.functor.obj (CommAlgCat.of R A)
    let f : B ≃ₐ[S] A := { toRingEquiv := RingEquiv.refl A, commutes' := fun s => (he s).symm }
    exact CommAlgCat.isoMk f
  · let B := pres.diag.obj j
    let : Algebra S R := e.toRingHom.toAlgebra
    let : Algebra S B := ((algebraMap R B).comp e.toRingHom).toAlgebra
    have : IsScalarTower S R B := IsScalarTower.of_algebraMap_eq' rfl
    have : Algebra.Etale S R := RingHom.Etale.toAlgebra (RingHom.Etale.of_bijective e.bijective)
    have : Algebra.Etale R B := hp j
    exact Algebra.Etale.comp S R B

private theorem henselianLocalRing_of_ringEquiv
    {R S : Type u} [CommRing R] [CommRing S]
    [HenselianLocalRing R] (e : R ≃+* S) : HenselianLocalRing S := by
  have : IsLocalRing S := e.isLocalRing
  refine ⟨fun f hf a ha hu => ?_⟩
  have heval (p : Polynomial S) (a : S) :
      (p.map (e.symm : S →+* R)).eval (e.symm a) = e.symm (p.eval a) := by
    simpa only [Polynomial.eval_map, RingEquiv.coe_toRingHom] using
      (Polynomial.eval₂_at_apply (e.symm : S →+* R) a (p := p))
  have ha' : (f.map (e.symm : S →+* R)).eval (e.symm a) ∈ IsLocalRing.maximalIdeal R := by
    rw [heval]
    exact (IsLocalRing.map_maximalIdeal_le (e.symm : S →+* R)) (Ideal.mem_map_of_mem _ ha)
  have hu' : IsUnit ((f.map (e.symm : S →+* R)).derivative.eval (e.symm a)) := by
    rw [Polynomial.derivative_map, heval]
    exact hu.map (e.symm : S →+* R)
  obtain ⟨b, hb, hba⟩ := HenselianLocalRing.is_henselian
    (f.map (e.symm : S →+* R)) (hf.map _) (e.symm a) ha' hu'
  refine ⟨e b, ?_, ?_⟩
  · apply e.symm.injective
    simpa only [Polynomial.IsRoot, ← heval, RingEquiv.symm_apply_apply, map_zero] using hb
  · have h := (IsLocalRing.map_maximalIdeal_le (e : R →+* S))
      (Ideal.mem_map_of_mem (e : R →+* S) hba)
    simpa only [map_sub, RingEquiv.coe_toRingHom, RingEquiv.apply_symm_apply] using h

private theorem henselization_of_base_equiv
    {R S A : Type u} [CommRing R] [IsLocalRing R] [CommRing S] [IsLocalRing S]
    [CommRing A] [IsLocalRing A] [Algebra R A] [Algebra S A]
    {K : Type v} [Field K] [Algebra (ResidueField R) K]
    {L : Type w} [Field L] [Algebra (ResidueField S) L]
    [IsLocalRing.IsHenselization R K A]
    (e : S ≃+* R) (he : ∀ s, algebraMap S A s = algebraMap R A (e s))
    (eL : L ≃+* K)
    (hL : ∀ s, eL (algebraMap (ResidueField S) L (residue S s)) =
      algebraMap (ResidueField R) K (residue R (e s))) : IsLocalRing.IsHenselization S L A := by
  obtain ⟨a, ha⟩ := IsHenselization.exists_residueFieldEquiv (R := R) (L := K) (Rh := A)
  exact IsHenselization.of_ind_etale.{u,w} (L := L) (Rh := A)
    (IsHenselization.henselian (R := R) (L := K) (Rh := A))
    (ind_etale_of_base_equiv (A := A) e he
      (IsHenselization.ind_etale_of_universe_le.{u,v} (R := R) (L := K) (Rh := A)))
    ⟨eL.trans a, fun s => by rw [RingEquiv.trans_apply, hL, ha, ← he]⟩

/-- The number of irreducible components of `Spec B` through `z` is the number of minimal primes
of the localization of `B` at `z`. -/
private theorem encard_irreducibleComponentsThrough_spec {B : Type u} [CommRing B]
    (z : PrimeSpectrum B) :
    Set.encard {Z ∈ irreducibleComponents (PrimeSpectrum B) | z ∈ Z} =
      Set.encard (minimalPrimes (Localization.AtPrime z.asIdeal)) :=
  (encard_irreducibleComponentsThrough_eq_minimalPrimes_stalk (Spec (CommRingCat.of B)) z).trans
    (Set.encard_congr (minimalPrimes_equiv_of_ringEquiv
      (Spec.stalkIso (CommRingCat.of B) z).commRingCatIsoToRingEquiv))

/-- **Stacks Project, Tag 0CB4.** The number of geometric branches at a point is the
supremum, over all étale neighborhoods of that point, of the number of irreducible components
of the neighborhood passing through its distinguished point. -/
@[stacks 0CB4 "geometric_branches_supremum"]
theorem numberOfGeometricBranches_eq_iSup_encard
    (X : AlgebraicGeometry.Scheme.{u}) (x : X) :
    numberOfGeometricBranches X x =
      ⨆ U : EtaleNeighborhood X x,
        Set.encard {Z ∈ irreducibleComponents U.scheme | U.point ∈ Z} := by
  classical
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, _⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (a := x) (by trivial) isOpen_univ
  let T := X.presheaf.stalk x
  let A := Γ(X, V)
  let p := hV.primeIdealOf ⟨x, hxV⟩
  have hp : hV.fromSpec p = x := hV.fromSpec_primeIdealOf ⟨x, hxV⟩
  let S := Localization.AtPrime p.asIdeal
  let D := (strictHenselizationData T).carrier
  let K := SeparableClosure (ResidueField T)
  let : Algebra A T := (X.presheaf.germ V x hxV).hom.toAlgebra
  let : IsLocalization.AtPrime T p.asIdeal := hV.isLocalization_stalk ⟨x, hxV⟩
  let eAlg : S ≃ₐ[A] T := IsLocalization.algEquiv p.asIdeal.primeCompl S T
  let e : S ≃+* T := eAlg.toRingEquiv
  let : Algebra S T := e.toRingHom.toAlgebra
  let : IsScalarTower A S T := IsScalarTower.of_algebraMap_eq fun a => by
    change algebraMap A T a = e (algebraMap A S a)
    exact (eAlg.commutes a).symm
  let : CommRing D := (strictHenselizationData T).commRing
  let : IsLocalRing D := (strictHenselizationData T).isLocalRing
  let : Algebra T D := (strictHenselizationData T).algebra
  let : Algebra A D := ((algebraMap T D).comp (algebraMap A T)).toAlgebra
  let : IsScalarTower A T D := IsScalarTower.of_algebraMap_eq' rfl
  let : Algebra S D := ((algebraMap T D).comp e.toRingHom).toAlgebra
  let : IsScalarTower S T D := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower A S D := IsScalarTower.of_algebraMap_eq fun a => by
    change algebraMap A D a = algebraMap T D (e (algebraMap A S a))
    change algebraMap T D (algebraMap A T a) = _
    congr 1
    exact (eAlg.commutes a).symm
  let : Field K := inferInstance
  let : Algebra (ResidueField T) K := inferInstance
  let : IsHenselization T K D := (strictHenselizationData T).isHenselization
  let : IsLocalHom e.toRingHom := IsLocalHom.of_surjective _ e.surjective
  let eRes := ResidueField.map e.toRingHom
  let : Algebra (ResidueField S) K :=
    ((algebraMap (ResidueField T) K).comp eRes).toAlgebra
  have hRes (s : S) :
      algebraMap (ResidueField S) K (residue S s) =
        algebraMap (ResidueField T) K (residue T (e s)) := by
    change algebraMap (ResidueField T) K
      (ResidueField.map e.toRingHom (residue S s)) = _
    exact congrArg (algebraMap (ResidueField T) K)
      (ResidueField.map_residue e.toRingHom s)
  have hBase : IsHenselization S K D :=
    henselization_of_base_equiv (R := T) (S := S) (A := D) e (by intro s; rfl)
      (RingEquiv.refl K) hRes
  let : IsHenselization S K D := hBase
  let eκT : p.asIdeal.ResidueField ≃+* ResidueField T := ResidueField.mapEquiv e
  let : Algebra A K :=
    ((algebraMap (p.asIdeal.ResidueField) K).comp
      (algebraMap A (p.asIdeal.ResidueField))).toAlgebra
  let : IsScalarTower A (p.asIdeal.ResidueField) K :=
    IsScalarTower.of_algebraMap_eq' rfl
  have hAK (a : A) : algebraMap A K a = 0 ↔ a ∈ p.asIdeal := by
    rw [IsScalarTower.algebraMap_apply A p.asIdeal.ResidueField K,
      map_eq_zero_iff _ (RingHom.injective _), Ideal.algebraMap_residueField_eq_zero]
  obtain ⟨eD, heA⟩ :=
    IsLocalRing.IsHenselization.exists_residueFieldEquiv_algebraMap
      (R := A) (p := p.asIdeal) (L := K) (Rsh := D)
  let aug : D →ₐ[A] K :=
    { toRingHom := eD.symm.toRingHom.comp (residue D)
      commutes' := fun a => by
        change eD.symm (residue D (algebraMap A D a)) = algebraMap A K a
        apply eD.injective
        rw [RingEquiv.apply_symm_apply]
        exact heA a |>.symm }
  have haug (y : D) : eD (aug y) = residue D y := by
    simp [aug, RingHom.comp_apply]
  obtain ⟨J, _, _, pres, hpres⟩ := CommAlgCat.ind_etale_comp
    (CommAlgCat.ind_etale_atPrime A S p.asIdeal)
    (IsLocalRing.IsHenselization.ind_etale_of_universe_le
      (R := S) (L := K) (Rh := D))
  let obj (j : J) : CommAlgCat.AugmentedEtale A K :=
    CostructuredArrow.mk (Y := ⟨pres.diag.obj j, hpres j⟩)
      (CommAlgCat.ofHom (aug.comp (pres.ι.app j).hom))
  let mapj {i j : J} (f : i ⟶ j) : obj i ⟶ obj j :=
    CostructuredArrow.homMk (ObjectProperty.homMk (pres.diag.map f))
      (CommAlgCat.hom_ext (AlgHom.ext fun x =>
        congrArg aug (ConcreteCategory.congr_hom (pres.w f) x)))
  let G : J ⥤ CommAlgCat.AugmentedEtale A K :=
    { obj := obj
      map := mapj
      map_id := by
        intro j
        apply CostructuredArrow.hom_ext
        apply ObjectProperty.hom_ext
        simp [mapj, obj]
      map_comp := by
        intro i j k f g
        apply CostructuredArrow.hom_ext
        apply ObjectProperty.hom_ext
        simp [mapj, obj] }
  let c : Cocone (G ⋙ CommAlgCat.AugmentedEtale.forget A K) :=
    { pt := CommAlgCat.of A D
      ι :=
        { app := fun j => pres.ι.app j
          naturality := fun i j f => by
            change pres.diag.map f ≫ pres.ι.app j = pres.ι.app i
            exact pres.w f } }
  have hc : IsColimit c := by
    change IsColimit pres.cocone
    exact pres.isColimit
  let Floc := G ⋙ CommAlgCat.AugmentedEtale.localization A K
  let stageUnit (j : J) (s : (G.obj j).prime.primeCompl) :
      IsUnit ((pres.ι.app j).hom (s : (G.obj j).left.obj)) := by
    apply (isUnit_map_iff (residue D) _).mp
    apply isUnit_iff_ne_zero.mpr
    intro hs
    apply s.property
    change aug ((pres.ι.app j).hom (s : (G.obj j).left.obj)) = 0
    apply eD.injective
    rw [haug, hs, map_zero]
  let locLeg (j : J) : Floc.obj j ⟶ CommAlgCat.of A D := by
    let q := (G.obj j).prime
    let B := ((G.obj j).left.obj : Type u)
    let : Algebra B D := (pres.ι.app j).hom.toRingHom.toAlgebra
    let : IsScalarTower A B D := IsScalarTower.of_algebraMap_eq fun a => by
      exact ((pres.ι.app j).hom.commutes a).symm
    let : Algebra B (Localization.AtPrime q) := inferInstance
    let : IsLocalization q.primeCompl (Localization.AtPrime q) := inferInstance
    exact CommAlgCat.ofHom (IsLocalization.liftAlgHom (A := A) (R := B)
      (P := D) (S := Localization.AtPrime q) (f := (pres.ι.app j).hom) (stageUnit j))
  have hfacLoc (j : J) :
      (CommAlgCat.AugmentedEtale.toLocalization A K).app (G.obj j) ≫ locLeg j =
        CommAlgCat.ofHom (pres.ι.app j).hom := by
    let q := (G.obj j).prime
    let B := ((G.obj j).left.obj : Type u)
    let : Algebra B D := (pres.ι.app j).hom.toRingHom.toAlgebra
    let : IsScalarTower A B D := IsScalarTower.of_algebraMap_eq fun a => by
      exact ((pres.ι.app j).hom.commutes a).symm
    let : Algebra B (Localization.AtPrime q) := inferInstance
    let : IsLocalization q.primeCompl (Localization.AtPrime q) := inferInstance
    ext x
    rw [CommAlgCat.hom_comp, AlgHom.comp_apply]
    exact IsLocalization.lift_eq (S := Localization.AtPrime q) (stageUnit j) x
  let ιLoc : Floc ⟶ (Functor.const J).obj (CommAlgCat.of A D) :=
    { app := locLeg
      naturality := by
        intro i j f
        let qi := (G.obj i).prime
        let Bi := ((G.obj i).left.obj : Type u)
        let : Algebra Bi D := (pres.ι.app i).hom.toRingHom.toAlgebra
        let : IsScalarTower A Bi D := IsScalarTower.of_algebraMap_eq fun a =>
          ((pres.ι.app i).hom.commutes a).symm
        let : Algebra Bi (Localization.AtPrime qi) := inferInstance
        let : IsLocalization qi.primeCompl (Localization.AtPrime qi) := inferInstance
        let : Algebra Bi (Floc.obj i) := by
          change Algebra Bi (Localization.AtPrime qi)
          infer_instance
        let : IsLocalization qi.primeCompl (Floc.obj i) := by
          change IsLocalization qi.primeCompl (Localization.AtPrime qi)
          infer_instance
        let : IsScalarTower A Bi (Floc.obj i) := by
          change IsScalarTower A Bi (Localization.AtPrime qi)
          infer_instance
        have hnat : (CommAlgCat.AugmentedEtale.forget A K).map (G.map f) ≫
            (CommAlgCat.AugmentedEtale.toLocalization A K).app (G.obj j) =
              (CommAlgCat.AugmentedEtale.toLocalization A K).app (G.obj i) ≫
                (CommAlgCat.AugmentedEtale.localization A K).map (G.map f) :=
          (CommAlgCat.AugmentedEtale.toLocalization A K).naturality (G.map f)
        apply CommAlgCat.hom_ext
        apply IsLocalization.algHom_ext qi.primeCompl
        exact congrArg CommAlgCat.Hom.hom (by
          calc
            (CommAlgCat.AugmentedEtale.toLocalization A K).app (G.obj i) ≫
                ((CommAlgCat.AugmentedEtale.localization A K).map (G.map f) ≫ locLeg j) =
                ((CommAlgCat.AugmentedEtale.forget A K).map (G.map f) ≫
                  (CommAlgCat.AugmentedEtale.toLocalization A K).app (G.obj j)) ≫ locLeg j := by
                    calc
                      _ = ((CommAlgCat.AugmentedEtale.toLocalization A K).app (G.obj i) ≫
                          (CommAlgCat.AugmentedEtale.localization A K).map (G.map f)) ≫
                            locLeg j := by
                            simp [Category.assoc]
                      _ = ((CommAlgCat.AugmentedEtale.forget A K).map (G.map f) ≫
                          (CommAlgCat.AugmentedEtale.toLocalization A K).app (G.obj j)) ≫
                            locLeg j :=
                            congrArg (fun g => g ≫ locLeg j) hnat.symm
            _ = (CommAlgCat.AugmentedEtale.forget A K).map (G.map f) ≫
                  ((CommAlgCat.AugmentedEtale.toLocalization A K).app (G.obj j) ≫ locLeg j) := by
                    simp [Category.assoc]
            _ = (CommAlgCat.AugmentedEtale.forget A K).map (G.map f) ≫
                  CommAlgCat.ofHom (pres.ι.app j).hom := by rw [hfacLoc j]
            _ = CommAlgCat.ofHom (pres.ι.app i).hom := c.w f
            _ = (CommAlgCat.AugmentedEtale.toLocalization A K).app (G.obj i) ≫ locLeg i :=
              (hfacLoc i).symm) }
  have hcLoc : IsColimit (Cocone.mk (CommAlgCat.of A D) ιLoc) :=
    isColimit_localizedStages_augmentedEtale G c hc ιLoc hfacLoc
  have hff (i j : J) (f : i ⟶ j) : (Floc.map f).hom.FaithfullyFlat :=
    faithfullyFlat_localizationMap_augmentedEtale (G.obj i) (G.obj j) (G.map f)
  have hcount : Set.encard (minimalPrimes D) =
      ⨆ j : J, Set.encard (minimalPrimes (Floc.obj j : Type u)) :=
    encard_minimalPrimes_of_filteredColimit Floc (Cocone.mk (CommAlgCat.of A D) ιLoc)
      hcLoc hff
  let stageNeighborhood (j : J) : EtaleNeighborhood X x := by
    let B := (pres.diag.obj j : Type u)
    let q := (G.obj j).prime
    let : q.IsPrime := RingHom.ker_isPrime (G.obj j).hom.hom
    let fAB : CommRingCat.of A ⟶ CommRingCat.of B :=
      CommRingCat.ofHom (algebraMap A B)
    let z : Spec (CommRingCat.of B) := ⟨q, inferInstance⟩
    have hz : Spec.map fAB z = p := by
      apply PrimeSpectrum.ext
      change Ideal.comap (algebraMap A B) q = p.asIdeal
      ext a
      change (G.obj j).hom.hom (algebraMap A B a) = 0 ↔ a ∈ p.asIdeal
      exact (congrArg (· = 0) ((G.obj j).hom.hom.commutes a)).to_iff.trans (hAK a)
    have : Etale (Spec.map fAB) := by
      rw [HasRingHomProperty.Spec_iff (P := @Etale)]
      change RingHom.Etale (algebraMap A B)
      exact RingHom.etale_algebraMap.mpr (hpres j)
    let : IsOpenImmersion hV.fromSpec := hV.isOpenImmersion_fromSpec
    let : Etale hV.fromSpec := by infer_instance
    exact
      { scheme := Spec (CommRingCat.of B)
        point := z
        toBase := Spec.map fAB ≫ hV.fromSpec
        etale_toBase := inferInstance
        map_point := by simpa [hz] using hp }
  have hstageCount (j : J) :
      Set.encard {Z ∈ irreducibleComponents (stageNeighborhood j).scheme |
          (stageNeighborhood j).point ∈ Z} =
        Set.encard (minimalPrimes (Floc.obj j : Type u)) := by
    exact encard_irreducibleComponentsThrough_spec (B := (pres.diag.obj j : Type u))
      (stageNeighborhood j).point
  let branchesAt (U : EtaleNeighborhood X x) : ℕ∞ :=
    Set.encard {Z ∈ irreducibleComponents U.scheme | U.point ∈ Z}
  have hupper (U : EtaleNeighborhood X x) :
      branchesAt U ≤ ⨆ j : J, Set.encard (minimalPrimes (Floc.obj j : Type u)) := by
    let O : U.scheme.Opens := U.toBase ⁻¹ᵁ V
    have hpointO : U.point ∈ O := by
      change U.toBase U.point ∈ V
      rw [U.map_point]
      exact hxV
    obtain ⟨_, ⟨W, hW, rfl⟩, hpointW, hWO⟩ :=
      U.scheme.isBasis_affineOpens.exists_subset_of_mem_open hpointO O.2
    let B := Γ(U.scheme, W)
    let hW' : IsAffineOpen W := hW
    let iVW : W ≤ U.toBase ⁻¹ᵁ V := hWO
    let fAB : CommRingCat.of A ⟶ CommRingCat.of B := U.toBase.appLE V W iVW
    let z : Spec (CommRingCat.of B) := hW'.primeIdealOf ⟨U.point, hpointW⟩
    let : IsOpenImmersion hV.fromSpec := hV.isOpenImmersion_fromSpec
    have hzpoint : hW'.fromSpec z = U.point :=
      hW'.fromSpec_primeIdealOf ⟨U.point, hpointW⟩
    have hchart : Spec.map fAB ≫ hV.fromSpec = hW'.fromSpec ≫ U.toBase :=
      IsAffineOpen.SpecMap_appLE_fromSpec U.toBase hV hW' iVW
    have hzbase : Spec.map fAB z = p := by
      apply hV.fromSpec.isOpenEmbedding.injective
      have heq := congrArg (fun f : Spec (CommRingCat.of B) ⟶ X => f z) hchart
      simpa [Scheme.Hom.comp_apply, hzpoint, U.map_point, hp] using heq
    let : Algebra A B := fAB.hom.toAlgebra
    let : Algebra.Etale A B :=
      RingHom.etale_algebraMap.mp (U.toBase.etale_appLE hV hW' iVW)
    have : Etale (Spec.map fAB) := by
      rw [HasRingHomProperty.Spec_iff (P := @Etale)]
      change RingHom.Etale (algebraMap A B)
      exact RingHom.etale_algebraMap.mpr inferInstance
    let Uaff : EtaleNeighborhood X x :=
      { scheme := Spec (CommRingCat.of B)
        point := z
        toBase := Spec.map fAB ≫ hV.fromSpec
        etale_toBase := inferInstance
        map_point := by simpa [hzbase] using hp }
    have hgeomPoint : Spec.map (CommRingCat.ofHom (algebraMap A K)) default = p := by
      apply PrimeSpectrum.ext
      change Ideal.comap (algebraMap A K) (⊥ : Ideal K) = p.asIdeal
      ext a
      exact hAK a
    let s : Spec (CommRingCat.of K) ⟶ X :=
      Spec.map (CommRingCat.ofHom (algebraMap A K)) ≫ hV.fromSpec
    have hs : s default = x := by
      change hV.fromSpec (Spec.map (CommRingCat.ofHom (algebraMap A K)) default) = x
      rw [hgeomPoint, hp]
    let : IsSepClosed K := IsSepClosure.sep_closed (ResidueField T)
    have hpoint : U.toBase U.point = s default := by
      rw [U.map_point, hs]
    obtain ⟨l, hlbase, hlpoint⟩ :=
      AlgebraicGeometry.Scheme.exists_fac_of_etale_of_isSepClosed
        U.toBase s U.point hpoint
    let : IsOpenImmersion hW'.fromSpec := hW'.isOpenImmersion_fromSpec
    have hrange : Set.range l.base ⊆ Set.range hW'.fromSpec.base := by
      rintro y ⟨t, rfl⟩
      have ht : t = default := Subsingleton.elim _ _
      subst t
      exact ⟨z, hzpoint.trans hlpoint.symm⟩
    let lB : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of B) :=
      IsOpenImmersion.lift hW'.fromSpec l hrange
    have hlB : lB ≫ hW'.fromSpec = l := IsOpenImmersion.lift_fac hW'.fromSpec l hrange
    obtain ⟨gBK, hgBK⟩ := Spec.map_surjective lB
    have hgpoint : Spec.map gBK default = z := by
      apply hW'.fromSpec.isOpenEmbedding.injective
      have heq := congrArg (fun f : Spec (CommRingCat.of K) ⟶ U.scheme => f default) hlB
      simpa [hgBK, hlpoint, hzpoint] using heq
    have hbaseRing : fAB ≫ gBK = CommRingCat.ofHom (algebraMap A K) := by
      apply Spec.map_injective
      apply (cancel_mono hV.fromSpec).mp
      calc
        Spec.map (fAB ≫ gBK) ≫ hV.fromSpec =
            (Spec.map gBK ≫ Spec.map fAB) ≫ hV.fromSpec := by rw [Spec.map_comp]
        _ = Spec.map gBK ≫ hW'.fromSpec ≫ U.toBase := by
          rw [Category.assoc, hchart]
        _ = (lB ≫ hW'.fromSpec) ≫ U.toBase := by
          simp only [Category.assoc]
          rw [hgBK]
        _ = l ≫ U.toBase := by rw [hlB]
        _ = s := hlbase
        _ = Spec.map (CommRingCat.ofHom (algebraMap A K)) ≫ hV.fromSpec := rfl
    let augB : B →ₐ[A] K :=
      { toRingHom := gBK.hom
        commutes' := fun a => ConcreteCategory.congr_hom hbaseRing a }
    have hker : RingHom.ker augB.toRingHom = z.asIdeal := by
      have hh := congrArg PrimeSpectrum.asIdeal hgpoint
      change Ideal.comap gBK.hom (⊥ : Ideal K) = z.asIdeal
      exact hh
    let E : CommAlgCat.AugmentedEtale A K :=
      CostructuredArrow.mk (Y := ⟨CommAlgCat.of A B, inferInstance⟩)
        (CommAlgCat.ofHom augB)
    have hEprime : E.prime = z.asIdeal := by
      change RingHom.ker augB.toRingHom = z.asIdeal
      exact hker
    let : E.prime.IsPrime := RingHom.ker_isPrime augB.toRingHom
    have hUaff : branchesAt U = branchesAt Uaff := by
      apply Set.encard_congr
      let ePoint : {C : irreducibleComponents U.scheme // U.point ∈ (C : Set U.scheme)} ≃
          {C : irreducibleComponents U.scheme // hW'.fromSpec z ∈ (C : Set U.scheme)} :=
        { toFun := fun C => ⟨C.1, by simpa [hzpoint] using C.2⟩
          invFun := fun C => ⟨C.1, by simpa [hzpoint] using C.2⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
      let eOpen := irreducibleComponentsThrough_equiv_of_isOpenEmbedding
        hW'.fromSpec.isOpenEmbedding z
      exact (componentThrough_equiv_subtype U.point).trans
        (ePoint.trans (eOpen.trans (componentThrough_equiv_subtype z).symm))
    have hUaffCount : branchesAt Uaff =
        Set.encard (minimalPrimes (Localization.AtPrime E.prime)) := by
      exact (encard_irreducibleComponentsThrough_spec z).trans
        (encard_minimalPrimes_localization_eq_of_ideal_eq z.asIdeal E.prime hEprime.symm)
    let : HenselianLocalRing D := IsHenselization.henselian
      (R := S) (L := K) (Rh := D)
    let ψ : B →ₐ[A] ResidueField D :=
      { toRingHom := eD.toRingHom.comp augB.toRingHom
        commutes' := fun a => by
          change eD (augB (algebraMap A B a)) = algebraMap A (ResidueField D) a
          rw [augB.commutes, heA] }
    obtain ⟨fBD, hfBD, _⟩ :=
      HenselianLocalRing.existsUnique_algHom_residue_of_etale
        (R := A) (A := B) (S := D) ψ
    have hcompat : aug.comp fBD = augB := by
      apply AlgHom.ext
      intro b
      exact (RingEquiv.injective eD) (by
        calc
          eD ((aug.comp fBD) b) = residue D (fBD b) := haug _
          _ = ψ b := hfBD b
          _ = eD (augB b) := rfl)
    let : IsFinitelyPresentable.{u} (CommAlgCat.of A B) :=
      CommAlgCat.isFinitelyPresentable_of_etale (CommAlgCat.of A B)
    obtain ⟨j, g, hg⟩ := IsFinitelyPresentable.exists_hom_of_isColimit hc
      (CommAlgCat.ofHom fBD)
    have haugfactor : (G.obj j).hom.hom.comp g.hom = augB := by
      apply AlgHom.ext
      intro b
      simp only [AlgHom.comp_apply]
      dsimp [G, obj]
      change aug ((pres.ι.app j).hom (g.hom b)) = augB b
      have hgb : (pres.ι.app j).hom (g.hom b) = fBD b := by
        exact ConcreteCategory.congr_hom hg b
      calc
        (G.obj j).hom.hom (g.hom b) = aug ((pres.ι.app j).hom (g.hom b)) := rfl
        _ = aug (fBD b) := congrArg aug hgb
        _ = augB b := congrArg (fun f : B →ₐ[A] K => f b) hcompat
    let fEj : E ⟶ G.obj j :=
      CostructuredArrow.homMk (ObjectProperty.homMk g)
        (CommAlgCat.hom_ext (AlgHom.ext fun b =>
          congrArg (fun f : B →ₐ[A] K => f b) haugfactor))
    have hlocFF : ((CommAlgCat.AugmentedEtale.localization A K).map fEj).hom.FaithfullyFlat :=
      faithfullyFlat_localizationMap_augmentedEtale E (G.obj j) fEj
    let locHom : Localization.AtPrime E.prime →+* (Floc.obj j : Type u) :=
      ((CommAlgCat.AugmentedEtale.localization A K).map fEj).hom.toRingHom
    let : Algebra (Localization.AtPrime E.prime) (Floc.obj j : Type u) := locHom.toAlgebra
    have hlocFFalg :
        (algebraMap (Localization.AtPrime E.prime) (Floc.obj j : Type u)).FaithfullyFlat := by
      change locHom.FaithfullyFlat
      exact hlocFF
    let : Module.FaithfullyFlat (Localization.AtPrime E.prime) (Floc.obj j : Type u) :=
      (RingHom.faithfullyFlat_algebraMap_iff).mp hlocFFalg
    have hmin : Set.encard (minimalPrimes (Localization.AtPrime E.prime)) ≤
        Set.encard (minimalPrimes (Floc.obj j : Type u)) :=
      encard_minimalPrimes_le_of_faithfullyFlat
    calc
      branchesAt U = branchesAt Uaff := hUaff
      _ = Set.encard (minimalPrimes (Localization.AtPrime E.prime)) := hUaffCount
      _ ≤ Set.encard (minimalPrimes (Floc.obj j : Type u)) := hmin
      _ ≤ ⨆ k : J, Set.encard (minimalPrimes (Floc.obj k : Type u)) :=
        le_iSup (fun k : J => Set.encard (minimalPrimes (Floc.obj k : Type u))) j
  have hstageLe : (⨆ j : J, Set.encard (minimalPrimes (Floc.obj j : Type u))) ≤
      ⨆ U : EtaleNeighborhood X x, branchesAt U := by
    apply iSup_le
    intro j
    calc
      Set.encard (minimalPrimes (Floc.obj j : Type u)) = branchesAt (stageNeighborhood j) :=
        (hstageCount j).symm
      _ ≤ ⨆ U : EtaleNeighborhood X x, branchesAt U :=
        le_iSup (fun U : EtaleNeighborhood X x => branchesAt U) (stageNeighborhood j)
  have hleft : numberOfGeometricBranches X x =
      Set.encard (minimalPrimes D) := rfl
  rw [hleft, hcount]
  apply le_antisymm
  · exact hstageLe
  · exact iSup_le fun U => hupper U

private abbrev coconeRange {J : Type v} [Category.{w, v} J]
    {F : J ⥤ CommRingCat.{u}} (c : CategoryTheory.Limits.Cocone F) (j : J) :
    Subring (c.pt : Type u) := (c.ι.app j).hom.range

private theorem directed_coconeRange {J : Type v} [Category.{w, v} J] [IsFilteredOrEmpty J]
    {F : J ⥤ CommRingCat.{u}} (c : CategoryTheory.Limits.Cocone F) :
    Directed (· ≤ ·) (coconeRange c) := by
  have hle : ∀ {i j : J}, (i ⟶ j) → coconeRange c i ≤ coconeRange c j := by
    rintro i j f y ⟨x, rfl⟩
    exact ⟨(F.map f).hom x, ConcreteCategory.congr_hom (c.w f) x⟩
  exact fun i j => ⟨IsFiltered.max i j, hle (IsFiltered.leftToMax i j),
    hle (IsFiltered.rightToMax i j)⟩

private theorem exists_app_eq_finset {J : Type v} [Category.{w, v} J] [IsFiltered J]
    {F : J ⥤ CommRingCat.{u}} (c : CategoryTheory.Limits.Cocone F)
    (hc : CategoryTheory.Limits.IsColimit c) (s : Finset (c.pt : Type u)) :
    ∃ j : J, ∀ x ∈ s, ∃ y : (F.obj j : Type u), (c.ι.app j).hom y = x := by
  classical
  let : Nonempty J := IsFiltered.nonempty
  let S : Subring (c.pt : Type u) := ⨆ j, coconeRange c j
  let stageMap (j : J) : (F.obj j : Type u) →+* S :=
    (c.ι.app j).hom.codRestrict S (fun x =>
      le_iSup (fun j => coconeRange c j) j ⟨x, rfl⟩)
  let d : Cocone F := {
    pt := CommRingCat.of S
    ι := {
      app := fun j => CommRingCat.ofHom (stageMap j)
      naturality := by
        intro i j f
        ext x
        apply Subtype.ext
        exact ConcreteCategory.congr_hom (c.w f) x
    }
  }
  have hright : hc.desc d ≫ CommRingCat.ofHom S.subtype = 𝟙 c.pt := by
    apply hc.hom_ext
    intro j
    ext x
    have hfac := ConcreteCategory.congr_hom (hc.fac d j) x
    simp [d, stageMap, RingHom.comp_apply]
  have rep (x : (c.pt : Type u)) : ∃ j y, (c.ι.app j).hom y = x := by
    have hx : S.subtype ((hc.desc d).hom x) = x := ConcreteCategory.congr_hom hright x
    have hxS : x ∈ S := hx ▸ ((hc.desc d).hom x).property
    obtain ⟨j, y, hy⟩ := (Subring.mem_iSup_of_directed (directed_coconeRange c)).mp hxS
    exact ⟨j, y, hy⟩
  choose j y hy using rep
  obtain ⟨k, hk⟩ := (directed_coconeRange c).finset_le (s.image j)
  exact ⟨k, fun x hx => hk (j x) (Finset.mem_image_of_mem _ hx) ⟨y x, hy x⟩⟩

private theorem finite_minimalPrimes_le_stageOf_cocone
    {J : Type v} [Category.{w, v} J] [IsFiltered J]
    {F : J ⥤ CommRingCat.{u}} (c : Cocone F) (hc : IsColimit c)
    (B : J → Type u) [(i : J) → CommRing (B i)]
    (f : ∀ i, B i →+* (c.pt : Type u)) (hf : ∀ i, (f i).Flat)
    (g : ∀ i, (F.obj i : Type u) →+* B i)
    (hfac : ∀ i, (c.ι.app i).hom = (f i).comp (g i))
    (s : Finset (Ideal (c.pt : Type u)))
    (hs : ∀ q ∈ s, q ∈ minimalPrimes (c.pt : Type u)) :
    ∃ i, s.card ≤ Set.encard (minimalPrimes (B i)) := by
  classical
  let T := (c.pt : Type u)
  let witness : {q // q ∈ s} → {q // q ∈ s} → T := fun q q' =>
    if h : q.1 = q'.1 then 0 else Classical.choose
      (Set.not_subset_iff_exists_mem_notMem.mp
        (fun hle => h (le_antisymm hle
          ((hs q'.1 q'.2).2 ⟨(hs q.1 q.2).isPrime, bot_le⟩ hle))))
  let elems : Finset T :=
    (s.attach ×ˢ s.attach).image fun p => witness p.1 p.2
  obtain ⟨i, hi⟩ := exists_app_eq_finset c hc elems
  let repr : T → (F.obj i : Type u) := fun z =>
    if hz : z ∈ elems then Classical.choose (hi z hz) else 0
  let ofi := (c.ι.app i).hom
  have hrepr (z : T) (hz : z ∈ elems) : ofi (repr z) = z := by
    simp only [repr, dite_eq_left_of_eq_true (eq_true hz)]
    exact Classical.choose_spec (hi z hz)
  let comap : Ideal T → Ideal (B i) := fun q => q.comap (f i)
  have hcomap_maps : Set.MapsTo comap (↑s : Set (Ideal T)) (minimalPrimes (B i)) := by
    intro q hq
    exact comap_mem_minimalPrimes_of_flat (f i) (hf i) (hs q hq)
  have hcomap_inj : Set.InjOn comap (↑s : Set (Ideal T)) := by
    intro q hq q' hq' heq
    by_contra hne
    let Q : {q // q ∈ s} := ⟨q, hq⟩
    let Q' : {q // q ∈ s} := ⟨q', hq'⟩
    have hQQ : Q' ≠ Q := fun e => hne (congrArg Subtype.val e).symm
    have hw := Classical.choose_spec (Set.not_subset_iff_exists_mem_notMem.mp
      (fun hle => hne (le_antisymm
        ((hs q hq).2 ⟨(hs q' hq').isPrime, bot_le⟩ hle) hle)))
    have hmem : witness Q' Q ∈ elems := by
      apply Finset.mem_image.mpr
      exact ⟨(Q', Q), Finset.mem_product.mpr ⟨by simp [Q'], by simp [Q]⟩, rfl⟩
    have hstage (z : T) (hz : z ∈ elems) : (f i) (g i (repr z)) = z := by
      rw [← RingHom.comp_apply, ← hfac i]
      exact hrepr z hz
    have ha : g i (repr (witness Q' Q)) ∈ comap q' := by
      change (f i) (g i (repr (witness Q' Q))) ∈ q'
      rw [hstage _ hmem]
      simpa [witness, hQQ] using hw.1
    have ha' : g i (repr (witness Q' Q)) ∈ comap q := by rwa [← heq] at ha
    change (f i) (g i (repr (witness Q' Q))) ∈ q at ha'
    rw [hstage _ hmem] at ha'
    exact hw.2 (by simpa [witness, hQQ] using ha')
  have := Set.encard_le_encard_of_injOn hcomap_maps hcomap_inj
  exact ⟨i, by simpa using this⟩

/-- **Stacks Project, Tag 0CB4.** The number of branches at a point is the
supremum, over elementary étale neighborhoods, of the number of irreducible
components passing through the distinguished point. -/
@[stacks 0CB4 "branches_supremum"]
theorem numberOfBranches_eq_iSup_encard_irreducibleComponentsThrough
    (X : Scheme.{u}) (x : X) :
    numberOfBranches X x =
      ⨆ (U : EtaleNeighborhood X x) (_ : U.IsElementary),
        Set.encard {Z ∈ irreducibleComponents U.scheme | U.point ∈ Z} := by
  classical
  let R := X.presheaf.stalk x
  let H := (henselizationData R).carrier
  let : CommRing H := henselizationDataCommRing R
  let : IsLocalRing H := henselizationDataIsLocalRing R
  let : Algebra R H := henselizationDataAlgebra R
  let : IsLocalHom (algebraMap R H) := henselizationDataIsLocalHom R
  let : IsLocalRing.IsHenselization R (IsLocalRing.ResidueField R) H :=
    henselizationDataIsHenselization R
  obtain ⟨ι, -, hover, -, ⟨hc⟩⟩ := isColimit_globalSections X x H
  let c : Cocone (globalSections X x) := Cocone.mk _ ι
  have hc' : IsColimit c := hc
  let stageMap (U : ElementaryEtaleNeighborhood X x) :
      U.obj.scheme.presheaf.stalk U.obj.point →+* H :=
    Classical.choose (hover (Opposite.op U))
  have stageMap_spec (U : ElementaryEtaleNeighborhood X x) :
      IsLocalHom (stageMap U) ∧
        (stageMap U).comp (stalkMap X x U) = algebraMap R H ∧
        (ι.app (Opposite.op U)).hom =
          (stageMap U).comp
            (U.obj.scheme.presheaf.germ ⊤ U.obj.point (Set.mem_univ _)).hom :=
    Classical.choose_spec (hover (Opposite.op U))
  let stageRing (U : ElementaryEtaleNeighborhood X x) :=
    U.obj.scheme.presheaf.stalk U.obj.point
  let germ (U : ElementaryEtaleNeighborhood X x) :
      ((globalSections X x).obj (Opposite.op U) : Type u) →+* stageRing U :=
    (U.obj.scheme.presheaf.germ ⊤ U.obj.point (Set.mem_univ _)).hom
  have hfac (U : ElementaryEtaleNeighborhood X x) :
      (c.ι.app (Opposite.op U)).hom = (stageMap U).comp (germ U) :=
    (stageMap_spec U).2.2
  have hff (U : ElementaryEtaleNeighborhood X x) :
      (stageMap U).FaithfullyFlat := by
    let : Algebra R (stageRing U) := (stalkMap X x U).toAlgebra
    let : Algebra (stageRing U) H := (stageMap U).toAlgebra
    let : IsLocalHom (stageMap U) := (stageMap_spec U).1
    let : IsScalarTower R (stageRing U) H := IsScalarTower.of_algebraMap_eq fun r => by
      have heq := congrArg (fun f : R →+* H => f r) (stageMap_spec U).2.1
      change algebraMap R H r = stageMap U (stalkMap X x U r)
      simpa only [RingHom.comp_apply] using heq.symm
    have hRB : StacksDraft.IndEtale R (stageRing U) :=
      indEtale_elementaryStalkMap X x U
    have hRH : StacksDraft.IndEtale R H := by
      change (CommAlgCat.etale.{u} R).ind
        (CommAlgCat.of R (ULift.{u} H))
      exact IsLocalRing.IsHenselization.ind_etale (L := IsLocalRing.ResidueField R)
    have hBH : StacksDraft.IndEtale (stageRing U) H :=
      StacksDraft.indEtale_of_comp hRB hRH
    exact faithfullyFlat_of_flat_of_isLocalHom (stageMap U)
      (CommAlgCat.flat_of_ind_etale (StacksDraft.indEtale_iff.mp hBH))
  let stageRingOp (i : (ElementaryEtaleNeighborhood X x)ᵒᵖ) : Type u := stageRing i.unop
  let stageMapOp (i : (ElementaryEtaleNeighborhood X x)ᵒᵖ) := stageMap i.unop
  let germOp (i : (ElementaryEtaleNeighborhood X x)ᵒᵖ) := germ i.unop
  have hffOp (i : (ElementaryEtaleNeighborhood X x)ᵒᵖ) := (hff i.unop).flat
  have hfacOp (i : (ElementaryEtaleNeighborhood X x)ᵒᵖ) :
      (c.ι.app i).hom = (stageMapOp i).comp (germOp i) := hfac i.unop
  have hmin : Set.encard (minimalPrimes H) =
      ⨆ U : ElementaryEtaleNeighborhood X x,
        Set.encard (minimalPrimes (stageRing U)) := by
    apply le_antisymm
    · apply ENat.forall_natCast_le_iff_le.mp
      intro n hn
      by_cases hfinite : (minimalPrimes H).Finite
      · obtain ⟨i, hi⟩ := finite_minimalPrimes_le_stageOf_cocone
          c hc' stageRingOp stageMapOp hffOp germOp hfacOp hfinite.toFinset
          fun q hq => hfinite.mem_toFinset.mp hq
        have hncard : n ≤ hfinite.toFinset.card := by
          rwa [← Nat.cast_le (α := ℕ∞), ← hfinite.encard_eq_coe_toFinset_card]
        exact (Nat.cast_le.mpr hncard).trans
          (hi.trans (le_iSup (fun U => Set.encard (minimalPrimes (stageRing U))) i.unop))
      · have hinfinite : (minimalPrimes H).Infinite := hfinite
        obtain ⟨s, hs, hscard⟩ := hinfinite.exists_subset_card_eq n
        obtain ⟨i, hi⟩ := finite_minimalPrimes_le_stageOf_cocone
          c hc' stageRingOp stageMapOp hffOp germOp hfacOp s fun q hq => hs hq
        rw [hscard] at hi
        exact hi.trans
          (le_iSup (fun U => Set.encard (minimalPrimes (stageRing U))) i.unop)
    · refine iSup_le fun U => ?_
      let : Algebra (stageRing U) H := (stageMap U).toAlgebra
      have : Module.FaithfullyFlat (stageRing U) H := hff U
      exact encard_minimalPrimes_le_of_faithfullyFlat
  have hcomponents :
      (⨆ U : ElementaryEtaleNeighborhood X x,
        Set.encard {Z ∈ irreducibleComponents U.obj.scheme |
        U.obj.point ∈ Z}) =
      ⨆ U : ElementaryEtaleNeighborhood X x,
        Set.encard (minimalPrimes (stageRing U)) :=
    iSup_congr fun U =>
      encard_irreducibleComponentsThrough_eq_minimalPrimes_stalk U.obj.scheme U.obj.point
  have hsubtype :
      (⨆ (U : EtaleNeighborhood X x) (_ : U.IsElementary),
        Set.encard {Z ∈ irreducibleComponents U.scheme | U.point ∈ Z}) =
      ⨆ U : ElementaryEtaleNeighborhood X x,
        Set.encard {Z ∈ irreducibleComponents U.obj.scheme | U.obj.point ∈ Z} := by
    let e : {U : EtaleNeighborhood X x // U.IsElementary} ≃
        ElementaryEtaleNeighborhood X x :=
      { toFun := fun U => ⟨U.1, U.2⟩
        invFun := fun U => ⟨U.obj, U.property⟩
        left_inv := fun U => by cases U; rfl
        right_inv := fun U => by cases U; rfl }
    calc
      (⨆ (U : EtaleNeighborhood X x) (_ : U.IsElementary),
          Set.encard {Z ∈ irreducibleComponents U.scheme | U.point ∈ Z}) =
        ⨆ U : {U : EtaleNeighborhood X x // U.IsElementary},
          Set.encard {Z ∈ irreducibleComponents U.1.scheme | U.1.point ∈ Z} :=
        iSup_subtype'
      _ = ⨆ U : ElementaryEtaleNeighborhood X x,
          Set.encard {Z ∈ irreducibleComponents U.obj.scheme | U.obj.point ∈ Z} :=
        Equiv.iSup_congr e fun _ => rfl
  rw [numberOfBranches_eq_numberOfBranchesOfLocalRing,
    numberOfBranchesOfLocalRing_eq_encard_minimalPrimes]
  exact hmin.trans (hcomponents.symm.trans hsubtype.symm)

end AlgebraicGeometry
