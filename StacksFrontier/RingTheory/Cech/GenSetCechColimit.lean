module

public import StacksFrontier.Algebra.Homology.Embedding.ExtendMap
public import StacksFrontier.Homology.FilteredColimitQuasiIso
public import StacksFrontier.RingTheory.Cech.GenFamilySystem
public import StacksFrontier.RingTheory.Cech.GeneralReindexBaseChange
public import StacksFrontier.RingTheory.Cech.IdealCechZeroLocus
public import StacksFrontier.RingTheory.Cech.PairCechColimit
public import StacksFrontier.RingTheory.Cech.PairGenSet

/-!
# The filtered colimit of Čech complexes attached to a ring and a finitely generated ideal

Fix a commutative ring `A` and an ideal `I ⊆ A`. The index system
`Stacks.GenFamily.GenSet A I` of nonempty finite sets of finite generating families of `I`
carries, by `Stacks.GenFamily.fam`, a product family for each index, and the product family of a
larger index is divisible by the product family of a smaller one. So the extended alternating
Čech complexes of the product families form a **filtered diagram over `GenSet A I`**, and its
colimit

`K(A, I) = colim_{S ∈ GenSet A I} Č(A, fam S)`

is a complex of `A`-modules attached to the pair `(A, I)` alone — no generating family is
chosen. For a ring map `φ : A → B` with `J = Ideal.map φ I` the transport
`Stacks.GenFamily.GenSet.map φ hJ` of indices lifts to a map of the two diagrams, hence to a map
`K(A, I) → K(B, J)` of the colimits, and these maps compose **on the nose**.

This file is the ring-level core of that construction: everything here speaks of rings, ideals
and ring maps only, with no site and no category of pairs. Two consumers assemble a complex of
presheaves of modules out of it by varying the ring along a category:
`StacksFrontier/RingTheory/Cech/GenPairCechPresheaf.lean` over the category of rings carrying a
chosen generating family, and — through the same ring-level lemmas — the construction on the
site of presented pairs of `StacksFrontier/RingTheory/Cech/PairCechColimit.lean`.

## Main definitions

* `Stacks.GenSetCech.cechDiagram` — the filtered diagram `S ↦ Č(A, fam S)` over `GenSet A I`,
  and `Stacks.GenSetCech.cechTermDiagram`, its degreewise part.
* `Stacks.GenSetCech.cechTransport` — the comparison `Č(A, fam S) → Č(B, fam (GenSet.map φ S))`
  along a ring map.
* `Stacks.GenSetCech.transportDesc` — the descended map of degreewise colimits
  `K(A, I)^n → K(B, J)^n`.
* `Stacks.GenSetCech.diffDesc`, `Stacks.GenSetCech.augDesc` — the descended differential and the
  descended augmentation onto the ring.
* `Stacks.GenSetCech.ringTransport` — a ring map, read as a map of modules over the source.

## Main results

* `Stacks.GenSetCech.quasiIso_cechDiagram_map` — **every transition of the diagram is a
  quasi-isomorphism**: the two product families cut out the same closed subset of the spectrum.
* `Stacks.GenSetCech.transportDesc_id` and `Stacks.GenSetCech.transportDesc_comp` — **the
  descended transports are strictly functorial**, which is what makes the colimit a presheaf of
  modules and gives conditions (a) and (b) of [Stacks, Tag 099D] on the nose.
* `Stacks.GenSetCech.transportDesc_comp_diffDesc`,
  `Stacks.GenSetCech.transportDesc_comp_augDesc`, `Stacks.GenSetCech.diffDesc_comp_diffDesc` —
  the descended differential and augmentation are natural in the ring, and the differential
  squares to zero.

## Implementation notes

The transport of indices along a ring map is functorial only *propositionally*:
`Finset.image` of the identity is not the identity on the nose
(`Stacks.GenFamily.GenSet.map_id`, `Stacks.GenFamily.GenSet.map_map`). The strictness of
`Stacks.GenSetCech.transportDesc_id` and `Stacks.GenSetCech.transportDesc_comp` is recovered
because a colimit leg is unchanged by composing with a transition of the diagram
(`CategoryTheory.Limits.colimit.w`), and the two indices in question are comparable, being
equal.

The divisibility facts in the shape the Čech comparison maps consume,
`Stacks.PairSite.exists_dvd_fam_of_le`, `Stacks.PairSite.exists_dvd_map_fam` and
`Stacks.PairSite.zeroLocus_span_range_fam_eq`, are stated for an arbitrary ring and ideal in
`StacksFrontier/RingTheory/Cech/PairGenSet.lean` and are used here as they stand.

No `@[stacks]` attribute is attached: this is the ring-level engine of a construction, not a
clause of any tag's statement. The tag it serves is [Stacks, Tag 099D], registered on
`Stacks.LocalCohomology.nonempty_functorialCechData`.

## References

* [Stacks Project, Tag 099D](https://stacks.math.columbia.edu/tag/099D)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.GenSetCech

open Stacks.GenFamily
open Stacks.PairSite (exists_dvd_fam_of_le exists_dvd_map_fam zeroLocus_span_range_fam_eq)

variable {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
variable {I : Ideal A} {J : Ideal B} {K : Ideal C}

/-! ### Degree zero and the comparison maps -/

/-- A ring map, read as a map of modules over the source ring. -/
def ringTransport (φ : A →+* B) :
    ModuleCat.of A A ⟶ (ModuleCat.restrictScalars φ).obj (ModuleCat.of B B) :=
  ModuleCat.ofHom
    (Y := (ModuleCat.restrictScalars φ).obj (ModuleCat.of B B))
    (CechRingBaseChange.ofRingHom φ)

/-- The comparison along a ring map is the change-of-rings map followed by a same-ring
comparison. -/
private theorem cechGenRingMap_eq_complexMap_comp {r s : ℕ} (φ : A →+* B) (f : Fin r → A)
    (g : Fin s → B) (α : Fin s → Fin r) (hα : ∀ j : Fin s, ∃ n : ℕ, φ (f (α j)) ∣ g j ^ n) :
    Cech.cechGenRingMap φ f g α hα =
      CechRingBaseChange.complexMap φ f ≫
        ((ModuleCat.restrictScalars φ).mapHomologicalComplex (ComplexShape.up ℕ)).map
          (Cech.cechGenMap (CechRingBaseChange.mapFamily φ f) g α hα B) :=
  HomologicalComplex.hom_ext _ _ fun _ => ModuleCat.hom_ext rfl

/-- **The comparison along a ring map together with a reindexing respects the degree-zero
identification of the Čech complex**: in degree zero it is the ring map itself. -/
theorem cechZeroIso_genRingMap {r s : ℕ} (φ : A →+* B) (f : Fin r → A) (g : Fin s → B)
    (α : Fin s → Fin r) (hα : ∀ j : Fin s, ∃ n : ℕ, φ (f (α j)) ∣ g j ^ n) :
    (Cech.cechGenRingMap φ f g α hα).f 0 ≫
        (ModuleCat.restrictScalars φ).map
          (LocalCohomology.cechZeroIso g (ModuleCat.of B B)).hom =
      (LocalCohomology.cechZeroIso f (ModuleCat.of A A)).hom ≫ ringTransport φ := by
  rw [cechGenRingMap_eq_complexMap_comp, HomologicalComplex.comp_f,
    Functor.mapHomologicalComplex_map_f, Category.assoc, ← Functor.map_comp,
    PairSite.cechZeroIso_cechGenMap (CechRingBaseChange.mapFamily φ f) g α hα (ModuleCat.of B B)]
  exact PairSite.cechZeroIso_complexMap φ f

/-- **A same-ring comparison on the target is absorbed** into a comparison along a ring map, at
the level of the maps of complexes. -/
theorem cechGenRingMap_comp_cechGenMap {r s t : ℕ} (φ : A →+* B) (f : Fin r → A) (g : Fin s → B)
    (g' : Fin t → B) (α : Fin s → Fin r) (hα : ∀ j : Fin s, ∃ n : ℕ, φ (f (α j)) ∣ g j ^ n)
    (δ : Fin t → Fin s) (hδ : ∀ k : Fin t, ∃ n : ℕ, g (δ k) ∣ g' k ^ n) (γ : Fin t → Fin r)
    (hγ : ∀ k : Fin t, ∃ n : ℕ, φ (f (γ k)) ∣ g' k ^ n) (hγαδ : γ = α ∘ δ) (p : ℕ) :
    (Cech.cechGenRingMap φ f g α hα).f p ≫
        (ModuleCat.restrictScalars φ).map ((Cech.cechGenMap g g' δ hδ B).f p) =
      (Cech.cechGenRingMap φ f g' γ hγ).f p :=
  ModuleCat.hom_ext (Cech.genTerm_comp_genRingTerm φ f g g' α hα δ hδ γ hγ hγαδ p)

/-- **A same-ring comparison on the source is absorbed** into a comparison along a ring map, at
the level of the maps of complexes. -/
theorem cechGenMap_comp_cechGenRingMap {r s t : ℕ} (φ : A →+* B) (f : Fin r → A)
    (f' : Fin s → A) (g : Fin t → B) (α : Fin s → Fin r)
    (hα : ∀ j : Fin s, ∃ n : ℕ, f (α j) ∣ f' j ^ n) (β : Fin t → Fin s)
    (hβ : ∀ k : Fin t, ∃ n : ℕ, φ (f' (β k)) ∣ g k ^ n) (γ : Fin t → Fin r)
    (hγ : ∀ k : Fin t, ∃ n : ℕ, φ (f (γ k)) ∣ g k ^ n) (hγαβ : γ = α ∘ β) (p : ℕ) :
    (Cech.cechGenMap f f' α hα A).f p ≫ (Cech.cechGenRingMap φ f' g β hβ).f p =
      (Cech.cechGenRingMap φ f g γ hγ).f p :=
  ModuleCat.hom_ext (Cech.genRingTerm_comp_genTerm φ f f' g α hα β hβ γ hγ hγαβ p)

/-! ### The change-of-rings maps of the Čech complex of one fixed family

These are the restriction maps of the Čech complex of a family carried pointwise onto a family,
read in the shape that `PresheafOfModules` consumes. They are stated here, over plain rings, so
that the consumer can supply them as *terms*: elaborating them inside the definition of a
presheaf of modules, where the module categories are spelled through the structure presheaf of
rings, is what exhausts the elaboration budget. -/

/-- **Along the identity ring map the comparison of a family with itself is the identity.** -/
theorem cechGenRingMap_id_f {r : ℕ} (f : Fin r → A)
    (hf : ∀ i : Fin r, ∃ n : ℕ, (RingHom.id A) (f (id i)) ∣ f i ^ n) (n : ℕ) :
    (Cech.cechGenRingMap (RingHom.id A) f f id hf).f n =
      (ModuleCat.restrictScalarsId' (RingHom.id A) rfl).inv.app
        (ModuleCat.of A (Cech.cechTerm f A n)) := by
  refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
  change Cech.genRingTerm (RingHom.id A) f f id hf n x = x
  rw [Cech.genRingTerm_id_ring, Cech.genTerm_id]
  rfl

/-- **The comparisons of a family carried pointwise onto a family compose on the nose.** -/
theorem cechGenRingMap_comp_f {r : ℕ} (φ : A →+* B) (ψ : B →+* C) (f : Fin r → A)
    (g : Fin r → B) (h : Fin r → C)
    (hg : ∀ i : Fin r, ∃ n : ℕ, φ (f (id i)) ∣ g i ^ n)
    (hh : ∀ i : Fin r, ∃ n : ℕ, ψ (g (id i)) ∣ h i ^ n)
    (hgh : ∀ i : Fin r, ∃ n : ℕ, (ψ.comp φ) (f (id i)) ∣ h i ^ n) (n : ℕ) :
    (Cech.cechGenRingMap (ψ.comp φ) f h id hgh).f n =
      (Cech.cechGenRingMap φ f g id hg).f n ≫
        (ModuleCat.restrictScalars φ).map ((Cech.cechGenRingMap ψ g h id hh).f n) ≫
          (ModuleCat.restrictScalarsComp' φ ψ (ψ.comp φ) rfl).inv.app
            (ModuleCat.of C (Cech.cechTerm h C n)) := by
  refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
  exact (LinearMap.congr_fun (Cech.genRingTerm_comp φ ψ f g h id id hg hh hgh n) x).symm

/-- **The comparison along a ring map commutes with the Čech differentials**, in the shape the
naturality of a map of presheaves of modules consumes. -/
theorem cechGenRingMap_comm_f {r s : ℕ} (φ : A →+* B) (f : Fin r → A) (g : Fin s → B)
    (α : Fin s → Fin r) (hα : ∀ j : Fin s, ∃ n : ℕ, φ (f (α j)) ∣ g j ^ n) (n : ℕ) :
    (Cech.cechGenRingMap φ f g α hα).f n ≫
        (ModuleCat.restrictScalars φ).map (ModuleCat.ofHom (Cech.cechD g B n)) =
      ModuleCat.ofHom (Cech.cechD f A n) ≫ (Cech.cechGenRingMap φ f g α hα).f (n + 1) :=
  ModuleCat.hom_ext (Cech.genRingTerm_comp_cechD φ f g α hα n).symm

/-- The Čech differentials compose to zero, as maps of module objects. -/
theorem cechD_comp_cechD_ofHom {r : ℕ} (f : Fin r → A) (n : ℕ) :
    ModuleCat.ofHom (Cech.cechD f A n) ≫ ModuleCat.ofHom (Cech.cechD f A (n + 1)) =
      (0 : ModuleCat.of A (Cech.cechTerm f A n) ⟶
        ModuleCat.of A (Cech.cechTerm f A (n + 1 + 1))) :=
  ModuleCat.hom_ext (Cech.cechD_comp_cechD f A n)

/-! ### The filtered diagram of Čech complexes -/

/-- **The filtered diagram of Čech complexes attached to `(A, I)`**: at the index `S` the
extended alternating Čech complex of the product family of `S`, with the comparison maps of the
system as transitions. -/
def cechDiagram (A : Type u) [CommRing A] (I : Ideal A) :
    GenSet A I ⥤ CochainComplex (ModuleCat.{u} A) ℕ where
  obj S := Cech.cechComplex (fam S) A
  map {_ _} h := Cech.cechGenMap (fam _) (fam _) (idxLe (leOfHom h))
    (exists_dvd_fam_of_le (leOfHom h)) A
  map_id S := by
    have hid : ∀ j : Fin (famCard S), ∃ n : ℕ, fam S (id j) ∣ fam S j ^ n :=
      fun j => ⟨1, by rw [pow_one]; exact dvd_rfl⟩
    exact (Cech.cechGenMap_congr (fam S) (fam S) _ _ A hid (idxLe_refl S)).trans
      (Cech.cechGenMap_id (fam S) A hid)
  map_comp {S T U} h₁ h₂ := by
    have hαβ : ∀ k : Fin (famCard U), ∃ n : ℕ,
        fam S (idxLe (leOfHom h₁) (idxLe (leOfHom h₂) k)) ∣ fam U k ^ n := fun k =>
      ⟨1, by
        rw [pow_one]
        exact (fam_dvd_of_le (leOfHom h₁) (idxLe (leOfHom h₂) k)).trans
          (fam_dvd_of_le (leOfHom h₂) k)⟩
    exact (Cech.cechGenMap_congr (fam S) (fam U) _ _ A hαβ
          (idxLe_trans (leOfHom h₁) (leOfHom h₂))).trans
      (Cech.cechGenMap_comp (fam S) (fam T) _ _ A (fam U)
        (idxLe (leOfHom h₂)) _ hαβ).symm

/-- The diagram sends a generating set `S` to the Čech complex of its product family. -/
@[simp]
theorem cechDiagram_obj (S : GenSet A I) :
    (cechDiagram A I).obj S = Cech.cechComplex (fam S) A := rfl

/-- The diagram sends `S ≤ T` to the comparison map of Čech complexes `Cech.cechGenMap`. -/
theorem cechDiagram_map {S T : GenSet A I} (h : S ⟶ T) :
    (cechDiagram A I).map h = Cech.cechGenMap (fam S) (fam T) (idxLe (leOfHom h))
      (exists_dvd_fam_of_le (leOfHom h)) A := rfl

/-- The degreewise diagram of Čech terms. -/
abbrev cechTermDiagram (A : Type u) [CommRing A] (I : Ideal A) (n : ℕ) :
    GenSet A I ⥤ ModuleCat.{u} A :=
  cechDiagram A I ⋙ HomologicalComplex.eval _ _ n

/-! ### The transitions are quasi-isomorphisms -/

/-- In degree zero every transition of the diagram respects the identification of the degree-zero
Čech term with the ring. -/
theorem cechZeroIso_cechDiagram_map {S T : GenSet A I} (h : S ⟶ T) :
    ((cechDiagram A I).map h).f 0 ≫
        (LocalCohomology.cechZeroIso (fam T) (ModuleCat.of A A)).hom =
      (LocalCohomology.cechZeroIso (fam S) (ModuleCat.of A A)).hom :=
  PairSite.cechZeroIso_cechGenMap (fam S) (fam T) _ _ (ModuleCat.of A A)

/-- **Every transition of the diagram is a quasi-isomorphism.** -/
theorem quasiIso_cechDiagram_map {S T : GenSet A I} (h : S ⟶ T) :
    QuasiIso ((cechDiagram A I).map h) := by
  rw [← HomologicalComplex.quasiIso_extendMap_iff _ ComplexShape.embeddingUpNat]
  exact IdealCechComplex.quasiIso_of_comp_augmentation_of_zeroLocus_eq (fam S) (fam T)
    (ModuleCat.of A A) zeroLocus_span_range_fam_eq _
    (IdealCechComplex.extendMap_comp_augmentation (fam S) (fam T)
      (ModuleCat.of A A) _ (cechZeroIso_cechDiagram_map h))

/-! ### The transport along a ring map -/

/-- The divisibility datum of the transport, read against the image family. -/
theorem exists_dvd_mapFamily_fam (φ : A →+* B) (hJ : J = Ideal.map φ I) (S : GenSet A I)
    (k : Fin (famCard (GenSet.map φ hJ S))) :
    ∃ n : ℕ, CechRingBaseChange.mapFamily φ (fam S) (idxMap φ hJ S k) ∣
      fam (GenSet.map φ hJ S) k ^ n :=
  exists_dvd_map_fam φ hJ S k

/-- The divisibility datum of the composite of a transition of the diagram with the transport. -/
theorem exists_dvd_idxLe_idxMap (φ : A →+* B) (hJ : J = Ideal.map φ I) {S T : GenSet A I}
    (hST : S ≤ T) (k : Fin (famCard (GenSet.map φ hJ T))) :
    ∃ n : ℕ, φ (fam S (idxLe hST (idxMap φ hJ T k))) ∣ fam (GenSet.map φ hJ T) k ^ n := by
  obtain ⟨n, hn⟩ := exists_dvd_map_fam φ hJ T k
  exact ⟨n, dvd_trans (map_dvd _ (fam_dvd_of_le hST _)) hn⟩

/-- **The comparison along a ring map.** It is the change-of-rings map of the Čech complex
followed by the same-ring comparison from the image of the product family of `S` to the product
family of the transported index — the composite being `Cech.cechGenRingMap` in one step. -/
def cechTransport (φ : A →+* B) (hJ : J = Ideal.map φ I) (S : GenSet A I) :
    Cech.cechComplex (fam S) A ⟶
      ((ModuleCat.restrictScalars φ).mapHomologicalComplex (ComplexShape.up ℕ)).obj
        (Cech.cechComplex (fam (GenSet.map φ hJ S)) B) :=
  Cech.cechGenRingMap φ (fam S) (fam (GenSet.map φ hJ S)) (idxMap φ hJ S)
    (exists_dvd_map_fam φ hJ S)

/-- In degree `p`, the transport is the termwise change-of-rings map `Cech.genRingTerm`. -/
theorem cechTransport_f_hom (φ : A →+* B) (hJ : J = Ideal.map φ I) (S : GenSet A I) (p : ℕ) :
    ((cechTransport φ hJ S).f p).hom =
      Cech.genRingTerm φ (fam S) (fam (GenSet.map φ hJ S)) (idxMap φ hJ S)
        (exists_dvd_map_fam φ hJ S) p :=
  rfl

/-- **The transport factors through the change of rings.** -/
theorem cechTransport_eq (φ : A →+* B) (hJ : J = Ideal.map φ I) (S : GenSet A I) :
    cechTransport φ hJ S =
      CechRingBaseChange.complexMap φ (fam S) ≫
        ((ModuleCat.restrictScalars φ).mapHomologicalComplex (ComplexShape.up ℕ)).map
          (Cech.cechGenMap (CechRingBaseChange.mapFamily φ (fam S))
            (fam (GenSet.map φ hJ S)) (idxMap φ hJ S)
            (exists_dvd_mapFamily_fam φ hJ S) B) :=
  cechGenRingMap_eq_complexMap_comp φ _ _ _ _

/-- **The transport commutes with the transitions of the diagram.** -/
theorem cechDiagram_map_comp_cechTransport (φ : A →+* B) (hJ : J = Ideal.map φ I)
    {S T : GenSet A I} (h : S ⟶ T) :
    (cechDiagram A I).map h ≫ cechTransport φ hJ T =
      cechTransport φ hJ S ≫
        ((ModuleCat.restrictScalars φ).mapHomologicalComplex (ComplexShape.up ℕ)).map
          ((cechDiagram B J).map (homOfLE (GenSet.map_monotone φ hJ (leOfHom h)))) := by
  refine HomologicalComplex.hom_ext _ _ fun p => ModuleCat.hom_ext ?_
  refine Eq.trans (Cech.genRingTerm_comp_genTerm φ (fam S) (fam T)
    (fam (GenSet.map φ hJ T)) (idxLe (leOfHom h)) (exists_dvd_fam_of_le (leOfHom h))
    (idxMap φ hJ T) (exists_dvd_map_fam φ hJ T)
    (idxLe (leOfHom h) ∘ idxMap φ hJ T)
    (exists_dvd_idxLe_idxMap φ hJ (leOfHom h)) rfl p) ?_
  exact (Cech.genTerm_comp_genRingTerm φ (fam S) (fam (GenSet.map φ hJ S))
    (fam (GenSet.map φ hJ T)) (idxMap φ hJ S) (exists_dvd_map_fam φ hJ S)
    (idxLe (GenSet.map_monotone φ hJ (leOfHom h)))
    (exists_dvd_fam_of_le (GenSet.map_monotone φ hJ (leOfHom h)))
    (idxLe (leOfHom h) ∘ idxMap φ hJ T)
    (exists_dvd_idxLe_idxMap φ hJ (leOfHom h))
    (idxLe_idxMap (leOfHom h) φ hJ).symm p).symm

/-- **The transport respects the degree-zero identification of the Čech complex.** -/
theorem cechZeroIso_cechTransport (φ : A →+* B) (hJ : J = Ideal.map φ I) (S : GenSet A I) :
    (cechTransport φ hJ S).f 0 ≫
        (ModuleCat.restrictScalars φ).map
          (LocalCohomology.cechZeroIso (fam (GenSet.map φ hJ S)) (ModuleCat.of B B)).hom =
      (LocalCohomology.cechZeroIso (fam S) (ModuleCat.of A A)).hom ≫ ringTransport φ :=
  cechZeroIso_genRingMap φ (fam S) (fam (GenSet.map φ hJ S)) (idxMap φ hJ S)
    (exists_dvd_map_fam φ hJ S)

/-! ### The degreewise maps, typed through the diagram -/

/-- The degree-`n` component of the transport along a ring map. -/
def cechTransportTerm (φ : A →+* B) (hJ : J = Ideal.map φ I) (n : ℕ) (S : GenSet A I) :
    (cechTermDiagram A I n).obj S ⟶
      (ModuleCat.restrictScalars φ).obj ((cechTermDiagram B J n).obj (GenSet.map φ hJ S)) :=
  (cechTransport φ hJ S).f n

/-- The degree-`n` component of the differential of a Čech complex of the diagram. -/
def cechDiffTerm (A : Type u) [CommRing A] (I : Ideal A) (n : ℕ) (S : GenSet A I) :
    (cechTermDiagram A I n).obj S ⟶ (cechTermDiagram A I (n + 1)).obj S :=
  ((cechDiagram A I).obj S).d n (n + 1)

/-- The degree-zero identification of a Čech complex of the diagram with the ring. -/
def cechAugTerm (A : Type u) [CommRing A] (I : Ideal A) (S : GenSet A I) :
    (cechTermDiagram A I 0).obj S ⟶ ModuleCat.of A A :=
  (LocalCohomology.cechZeroIso (fam S) (ModuleCat.of A A)).hom

/-- The transitions of the diagram commute with the transport, degreewise. -/
theorem cechTransportTerm_naturality (φ : A →+* B) (hJ : J = Ideal.map φ I) {S T : GenSet A I}
    (h : S ⟶ T) (n : ℕ) :
    (cechTermDiagram A I n).map h ≫ cechTransportTerm φ hJ n T =
      cechTransportTerm φ hJ n S ≫
        (ModuleCat.restrictScalars φ).map
          ((cechTermDiagram B J n).map (homOfLE (GenSet.map_monotone φ hJ (leOfHom h)))) :=
  HomologicalComplex.congr_hom (cechDiagram_map_comp_cechTransport φ hJ h) n

/-- The transitions of the diagram commute with the Čech differentials. -/
theorem cechDiffTerm_naturality {S T : GenSet A I} (h : S ⟶ T) (n : ℕ) :
    (cechTermDiagram A I n).map h ≫ cechDiffTerm A I n T =
      cechDiffTerm A I n S ≫ (cechTermDiagram A I (n + 1)).map h :=
  ((cechDiagram A I).map h).comm n (n + 1)

/-- The Čech differentials of the diagram compose to zero. -/
theorem cechDiffTerm_comp_cechDiffTerm (n : ℕ) (S : GenSet A I) :
    cechDiffTerm A I n S ≫ cechDiffTerm A I (n + 1) S = 0 :=
  HomologicalComplex.d_comp_d _ n (n + 1) (n + 1 + 1)

/-- The transport is a map of complexes, degreewise. -/
theorem cechDiffTerm_comp_cechTransportTerm (φ : A →+* B) (hJ : J = Ideal.map φ I) (n : ℕ)
    (S : GenSet A I) :
    cechDiffTerm A I n S ≫ cechTransportTerm φ hJ (n + 1) S =
      cechTransportTerm φ hJ n S ≫
        (ModuleCat.restrictScalars φ).map (cechDiffTerm B J n (GenSet.map φ hJ S)) :=
  ((cechTransport φ hJ S).comm n (n + 1)).symm

/-- The transitions of the diagram respect the degree-zero identification. -/
theorem cechAugTerm_naturality {S T : GenSet A I} (h : S ⟶ T) :
    (cechTermDiagram A I 0).map h ≫ cechAugTerm A I T = cechAugTerm A I S :=
  cechZeroIso_cechDiagram_map h

/-- The transport respects the degree-zero identification, degreewise. -/
theorem cechTransportTerm_comp_cechAugTerm (φ : A →+* B) (hJ : J = Ideal.map φ I)
    (S : GenSet A I) :
    cechTransportTerm φ hJ 0 S ≫
        (ModuleCat.restrictScalars φ).map (cechAugTerm B J (GenSet.map φ hJ S)) =
      cechAugTerm A I S ≫ ringTransport φ :=
  cechZeroIso_cechTransport φ hJ S

/-! ### The degreewise colimit -/

/-- The cocone whose descent is the transport of the colimits along a ring map. -/
def transportCocone (φ : A →+* B) (hJ : J = Ideal.map φ I) (n : ℕ) :
    Cocone (cechTermDiagram A I n) where
  pt := (ModuleCat.restrictScalars φ).obj (colimit (cechTermDiagram B J n))
  ι :=
    { app := fun S =>
        cechTransportTerm φ hJ n S ≫
          (ModuleCat.restrictScalars φ).map
            (colimit.ι (cechTermDiagram B J n) (GenSet.map φ hJ S))
      naturality := fun S T h => by
        dsimp only [Functor.const_obj_obj, Functor.const_obj_map]
        rw [Category.comp_id, ← Category.assoc, cechTransportTerm_naturality φ hJ h n,
          Category.assoc, ← Functor.map_comp, colimit.w] }

/-- The cone point of `transportCocone` is the restriction of scalars of the degree-`n` colimit
over `B`. -/
@[simp]
theorem transportCocone_pt (φ : A →+* B) (hJ : J = Ideal.map φ I) (n : ℕ) :
    (transportCocone φ hJ n).pt =
      (ModuleCat.restrictScalars φ).obj (colimit (cechTermDiagram B J n)) := rfl

/-- The leg of `transportCocone` at `S` is the transport followed by the colimit inclusion at
the transported generating set. -/
@[simp]
theorem transportCocone_ι_app (φ : A →+* B) (hJ : J = Ideal.map φ I) (n : ℕ) (S : GenSet A I) :
    (transportCocone φ hJ n).ι.app S =
      cechTransportTerm φ hJ n S ≫
        (ModuleCat.restrictScalars φ).map
          (colimit.ι (cechTermDiagram B J n) (GenSet.map φ hJ S)) := rfl

/-- **The transport of the degree-`n` colimits along a ring map**: the descent of the transport
of the diagrams. -/
def transportDesc (φ : A →+* B) (hJ : J = Ideal.map φ I) (n : ℕ) :
    (colimit (cechTermDiagram A I n) : ModuleCat.{u} A) ⟶
      (ModuleCat.restrictScalars φ).obj (colimit (cechTermDiagram B J n) : ModuleCat.{u} B) :=
  colimit.desc _ (transportCocone φ hJ n)

/-- The colimit inclusion at `S` followed by `transportDesc` is the transport followed by the
colimit inclusion at the transported generating set. -/
@[simp]
theorem ι_transportDesc (φ : A →+* B) (hJ : J = Ideal.map φ I) (n : ℕ) (S : GenSet A I) :
    colimit.ι (cechTermDiagram A I n) S ≫ transportDesc φ hJ n =
      cechTransportTerm φ hJ n S ≫
        (ModuleCat.restrictScalars φ).map
          (colimit.ι (cechTermDiagram B J n) (GenSet.map φ hJ S)) :=
  colimit.ι_desc _ _

/-- **The transport along the identity is a transition of the diagram**: the one along the
inclusion `S ≤ GenSet.map (RingHom.id A) S`, which is an equality of indices but only
propositionally, `Finset.image` of the identity not being the identity on the nose. -/
theorem cechTransport_id_apply (hI : I = Ideal.map (RingHom.id A) I) (S : GenSet A I) (n : ℕ)
    (x : Cech.cechTerm (fam S) A n) :
    ((cechTransport (RingHom.id A) hI S).f n).hom x =
      (((cechDiagram A I).map (homOfLE (GenSet.map_id S hI).ge)).f n).hom x := by
  refine Eq.trans (LinearMap.congr_fun (Cech.genRingTerm_id_ring (fam S)
    (fam (GenSet.map (RingHom.id A) hI S)) (idxMap (RingHom.id A) hI S)
    (exists_dvd_map_fam (RingHom.id A) hI S) n) x) ?_
  exact LinearMap.congr_fun (Cech.genTerm_congr (fam S) (fam (GenSet.map (RingHom.id A) hI S))
    (idxMap (RingHom.id A) hI S) (exists_dvd_map_fam (RingHom.id A) hI S) A
    (exists_dvd_fam_of_le (GenSet.map_id S hI).ge) (idxMap_id S hI) n) x

/-- The divisibility datum of the composite of two transports. -/
theorem exists_dvd_idxMap_idxMap (φ : A →+* B) (ψ : B →+* C) (hJ : J = Ideal.map φ I)
    (hK : K = Ideal.map ψ J) (S : GenSet A I)
    (k : Fin (famCard (GenSet.map ψ hK (GenSet.map φ hJ S)))) :
    ∃ n : ℕ, (ψ.comp φ) (fam S
        ((idxMap φ hJ S ∘ idxMap ψ hK (GenSet.map φ hJ S)) k)) ∣
      fam (GenSet.map ψ hK (GenSet.map φ hJ S)) k ^ n := by
  obtain ⟨m, hm⟩ := exists_dvd_map_fam ψ hK (GenSet.map φ hJ S) k
  obtain ⟨c, hc⟩ := exists_dvd_map_fam φ hJ S (idxMap ψ hK (GenSet.map φ hJ S) k)
  refine ⟨m * c, ?_⟩
  have h1 := map_dvd ψ hc
  rw [map_pow] at h1
  rw [pow_mul]
  exact h1.trans (pow_dvd_pow_of_dvd hm c)

/-- **The transports compose**, up to the transition of the diagram along the inclusion
`GenSet.map (ψ ∘ φ) S ≤ GenSet.map ψ (GenSet.map φ S)`; the first half, computing the composite
of the two transports as a single comparison. -/
theorem cechTransport_comp_apply₁ (φ : A →+* B) (ψ : B →+* C) (hJ : J = Ideal.map φ I)
    (hK : K = Ideal.map ψ J) (S : GenSet A I) (n : ℕ) (x : Cech.cechTerm (fam S) A n) :
    ((cechTransport ψ hK (GenSet.map φ hJ S)).f n).hom
        (((cechTransport φ hJ S).f n).hom x) =
      Cech.genRingTerm (ψ.comp φ) (fam S) (fam (GenSet.map ψ hK (GenSet.map φ hJ S)))
        (idxMap φ hJ S ∘ idxMap ψ hK (GenSet.map φ hJ S))
        (exists_dvd_idxMap_idxMap φ ψ hJ hK S) n x :=
  LinearMap.congr_fun (Cech.genRingTerm_comp φ ψ (fam S) (fam (GenSet.map φ hJ S))
    (fam (GenSet.map ψ hK (GenSet.map φ hJ S))) (idxMap φ hJ S)
    (idxMap ψ hK (GenSet.map φ hJ S)) (exists_dvd_map_fam φ hJ S)
    (exists_dvd_map_fam ψ hK (GenSet.map φ hJ S))
    (exists_dvd_idxMap_idxMap φ ψ hJ hK S) n) x

/-- The second half: the single comparison factors through the transport along `ψ ∘ φ`. -/
theorem cechTransport_comp_apply₂ (φ : A →+* B) (ψ : B →+* C) (hJ : J = Ideal.map φ I)
    (hK : K = Ideal.map ψ J) (hKA : K = Ideal.map (ψ.comp φ) I) (S : GenSet A I) (n : ℕ)
    (x : Cech.cechTerm (fam S) A n) :
    Cech.genRingTerm (ψ.comp φ) (fam S) (fam (GenSet.map ψ hK (GenSet.map φ hJ S)))
        (idxMap φ hJ S ∘ idxMap ψ hK (GenSet.map φ hJ S))
        (exists_dvd_idxMap_idxMap φ ψ hJ hK S) n x =
      (((cechDiagram C K).map
            (homOfLE (GenSet.map_map φ ψ hJ hK hKA S).ge)).f n).hom
        (((cechTransport (ψ.comp φ) hKA S).f n).hom x) :=
  (LinearMap.congr_fun (Cech.genTerm_comp_genRingTerm (ψ.comp φ) (fam S)
    (fam (GenSet.map (ψ.comp φ) hKA S)) (fam (GenSet.map ψ hK (GenSet.map φ hJ S)))
    (idxMap (ψ.comp φ) hKA S) (exists_dvd_map_fam (ψ.comp φ) hKA S)
    (idxLe (GenSet.map_map φ ψ hJ hK hKA S).ge)
    (exists_dvd_fam_of_le (GenSet.map_map φ ψ hJ hK hKA S).ge)
    (idxMap φ hJ S ∘ idxMap ψ hK (GenSet.map φ hJ S))
    (exists_dvd_idxMap_idxMap φ ψ hJ hK S)
    (idxMap_comp φ ψ hJ hK hKA S) n) x).symm

/-- **The transports compose**, up to the transition of the diagram along the inclusion
`GenSet.map (ψ ∘ φ) S ≤ GenSet.map ψ (GenSet.map φ S)`. -/
theorem cechTransport_comp_apply (φ : A →+* B) (ψ : B →+* C) (hJ : J = Ideal.map φ I)
    (hK : K = Ideal.map ψ J) (hKA : K = Ideal.map (ψ.comp φ) I) (S : GenSet A I) (n : ℕ)
    (x : Cech.cechTerm (fam S) A n) :
    ((cechTransport ψ hK (GenSet.map φ hJ S)).f n).hom
        (((cechTransport φ hJ S).f n).hom x) =
      (((cechDiagram C K).map
            (homOfLE (GenSet.map_map φ ψ hJ hK hKA S).ge)).f n).hom
        (((cechTransport (ψ.comp φ) hKA S).f n).hom x) :=
  (cechTransport_comp_apply₁ φ ψ hJ hK S n x).trans
    (cechTransport_comp_apply₂ φ ψ hJ hK hKA S n x)

/-- The descended transport, read on the elements of a leg of the colimit. -/
theorem transportDesc_ι_apply (φ : A →+* B) (hJ : J = Ideal.map φ I) (n : ℕ) (S : GenSet A I)
    (x : (cechTermDiagram A I n).obj S) :
    (transportDesc φ hJ n).hom ((colimit.ι (cechTermDiagram A I n) S).hom x) =
      (colimit.ι (cechTermDiagram B J n) (GenSet.map φ hJ S)).hom
        (((cechTransport φ hJ S).f n).hom x) :=
  LinearMap.congr_fun (congrArg ModuleCat.Hom.hom (ι_transportDesc φ hJ n S)) x

/-- The transitions of the colimit, read on elements. -/
theorem colimit_ι_apply_of_le (n : ℕ) {S T : GenSet A I} (h : S ⟶ T)
    (x : (cechTermDiagram A I n).obj S) :
    (colimit.ι (cechTermDiagram A I n) T).hom
        ((((cechDiagram A I).map h).f n).hom x) =
      (colimit.ι (cechTermDiagram A I n) S).hom x :=
  LinearMap.congr_fun (congrArg ModuleCat.Hom.hom (colimit.w (cechTermDiagram A I n) h)) x

/-- **The descended transport along the identity is the identity.** -/
theorem transportDesc_id (hI : I = Ideal.map (RingHom.id A) I) (n : ℕ) :
    transportDesc (RingHom.id A) hI n =
      (ModuleCat.restrictScalarsId' (RingHom.id A) rfl).inv.app
        (colimit (cechTermDiagram A I n) : ModuleCat.{u} A) := by
  refine colimit.hom_ext fun S => ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
  refine Eq.trans (transportDesc_ι_apply (RingHom.id A) hI n S x) ?_
  refine Eq.trans (congrArg
    (fun y => (colimit.ι (cechTermDiagram A I n) (GenSet.map (RingHom.id A) hI S)).hom y)
    (cechTransport_id_apply hI S n x)) ?_
  exact colimit_ι_apply_of_le n (homOfLE (GenSet.map_id S hI).ge) x

/-- **The descended transports compose on the nose.** -/
theorem transportDesc_comp (φ : A →+* B) (ψ : B →+* C) (hJ : J = Ideal.map φ I)
    (hK : K = Ideal.map ψ J) (hKA : K = Ideal.map (ψ.comp φ) I) (n : ℕ) :
    transportDesc (ψ.comp φ) hKA n =
      transportDesc φ hJ n ≫ (ModuleCat.restrictScalars φ).map (transportDesc ψ hK n) ≫
        (ModuleCat.restrictScalarsComp' φ ψ (ψ.comp φ) rfl).inv.app
          (colimit (cechTermDiagram C K n) : ModuleCat.{u} C) := by
  refine colimit.hom_ext fun S => ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
  refine Eq.trans (transportDesc_ι_apply (ψ.comp φ) hKA n S x) ?_
  refine Eq.trans ?_ (congrArg (fun y => (transportDesc ψ hK n).hom y)
    (transportDesc_ι_apply φ hJ n S x)).symm
  refine Eq.trans ?_ (transportDesc_ι_apply ψ hK n (GenSet.map φ hJ S)
    (((cechTransport φ hJ S).f n).hom x)).symm
  refine Eq.trans ?_ (congrArg
    (fun y => (colimit.ι (cechTermDiagram C K n)
      (GenSet.map ψ hK (GenSet.map φ hJ S))).hom y)
    (cechTransport_comp_apply φ ψ hJ hK hKA S n x)).symm
  exact (colimit_ι_apply_of_le n (homOfLE (GenSet.map_map φ ψ hJ hK hKA S).ge)
    (((cechTransport (ψ.comp φ) hKA S).f n).hom x)).symm

/-! ### The differential and the augmentation of the colimit -/

/-- The cocone whose descent is the differential of the colimit. -/
def diffCocone (A : Type u) [CommRing A] (I : Ideal A) (n : ℕ) :
    Cocone (cechTermDiagram A I n) where
  pt := (colimit (cechTermDiagram A I (n + 1)) : ModuleCat.{u} A)
  ι :=
    { app := fun S => cechDiffTerm A I n S ≫ colimit.ι (cechTermDiagram A I (n + 1)) S
      naturality := fun S T h => by
        dsimp only [Functor.const_obj_obj, Functor.const_obj_map]
        rw [Category.comp_id, ← Category.assoc, cechDiffTerm_naturality h n,
          Category.assoc, colimit.w] }

/-- The cone point of `diffCocone` is the degree-`(n + 1)` colimit. -/
@[simp]
theorem diffCocone_pt (n : ℕ) :
    (diffCocone A I n).pt = (colimit (cechTermDiagram A I (n + 1)) : ModuleCat.{u} A) := rfl

/-- The leg of `diffCocone` at `S` is the Čech differential followed by the colimit inclusion. -/
@[simp]
theorem diffCocone_ι_app (n : ℕ) (S : GenSet A I) :
    (diffCocone A I n).ι.app S =
      cechDiffTerm A I n S ≫ colimit.ι (cechTermDiagram A I (n + 1)) S := rfl

/-- **The differential of the colimit in degree `n`.** -/
def diffDesc (A : Type u) [CommRing A] (I : Ideal A) (n : ℕ) :
    (colimit (cechTermDiagram A I n) : ModuleCat.{u} A) ⟶
      (colimit (cechTermDiagram A I (n + 1)) : ModuleCat.{u} A) :=
  colimit.desc _ (diffCocone A I n)

/-- The colimit inclusion at `S` followed by `diffDesc` is the Čech differential followed by the
colimit inclusion. -/
@[simp]
theorem ι_diffDesc (n : ℕ) (S : GenSet A I) :
    colimit.ι (cechTermDiagram A I n) S ≫ diffDesc A I n =
      cechDiffTerm A I n S ≫ colimit.ι (cechTermDiagram A I (n + 1)) S :=
  colimit.ι_desc _ _

/-- **The descended differentials commute with the descended transports.** -/
theorem transportDesc_comp_diffDesc (φ : A →+* B) (hJ : J = Ideal.map φ I) (n : ℕ) :
    transportDesc φ hJ n ≫ (ModuleCat.restrictScalars φ).map (diffDesc B J n) =
      diffDesc A I n ≫ transportDesc φ hJ (n + 1) := by
  refine colimit.hom_ext fun S => ?_
  rw [← Category.assoc, ι_transportDesc, Category.assoc, ← Functor.map_comp, ι_diffDesc,
    ← Category.assoc, ι_diffDesc, Category.assoc, ι_transportDesc, Functor.map_comp,
    ← Category.assoc, ← cechDiffTerm_comp_cechTransportTerm, Category.assoc]

/-- **The descended differentials compose to zero.** -/
theorem diffDesc_comp_diffDesc (n : ℕ) :
    diffDesc A I n ≫ diffDesc A I (n + 1) = 0 := by
  refine colimit.hom_ext fun S => ?_
  rw [← Category.assoc, ι_diffDesc, Category.assoc, ι_diffDesc, ← Category.assoc,
    cechDiffTerm_comp_cechDiffTerm, zero_comp, comp_zero]

/-- The cocone whose descent is the augmentation of the colimit. -/
def augCocone (A : Type u) [CommRing A] (I : Ideal A) : Cocone (cechTermDiagram A I 0) where
  pt := ModuleCat.of A A
  ι :=
    { app := fun S => cechAugTerm A I S
      naturality := fun S T h => by
        dsimp only [Functor.const_obj_obj, Functor.const_obj_map]
        rw [Category.comp_id, cechAugTerm_naturality] }

/-- The cone point of `augCocone` is the ring `A`. -/
@[simp]
theorem augCocone_pt : (augCocone A I).pt = ModuleCat.of A A := rfl

/-- The leg of `augCocone` at `S` is the augmentation of the Čech complex of `S`. -/
@[simp]
theorem augCocone_ι_app (S : GenSet A I) : (augCocone A I).ι.app S = cechAugTerm A I S := rfl

/-- **The augmentation of the degree-zero colimit onto the ring.** -/
def augDesc (A : Type u) [CommRing A] (I : Ideal A) :
    (colimit (cechTermDiagram A I 0) : ModuleCat.{u} A) ⟶ ModuleCat.of A A :=
  colimit.desc _ (augCocone A I)

/-- The colimit inclusion at `S` followed by `augDesc` is the augmentation of the Čech complex
of `S`. -/
@[simp]
theorem ι_augDesc (S : GenSet A I) :
    colimit.ι (cechTermDiagram A I 0) S ≫ augDesc A I = cechAugTerm A I S :=
  colimit.ι_desc _ _

/-- **The descended augmentations commute with the descended transports.** -/
theorem transportDesc_comp_augDesc (φ : A →+* B) (hJ : J = Ideal.map φ I) :
    transportDesc φ hJ 0 ≫ (ModuleCat.restrictScalars φ).map (augDesc B J) =
      augDesc A I ≫ ringTransport φ := by
  refine colimit.hom_ext fun S => ?_
  rw [← Category.assoc, ι_transportDesc, Category.assoc, ← Functor.map_comp, ι_augDesc,
    ← Category.assoc, ι_augDesc, cechTransportTerm_comp_cechAugTerm]

end Stacks.GenSetCech

end
