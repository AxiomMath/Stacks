module

public import StacksFrontier.RingTheory.Cech.FamilySystem
public import StacksFrontier.RingTheory.Cech.GeneralReindexBaseChange

/-!
# The filtered diagram of Čech complexes of a family system

Let `R` be a presheaf of commutative rings on a category `C` and `F` a family system on it
(`Stacks.CechFamilySystem.FamilySystem`), singling out over each object a restriction-stable
class of finite families of sections. Over each object `V` the nonempty finite sets of
distinguished families form a directed poset `F.GenSet V`, and this file turns the extended
alternating Čech complexes of their product families into a filtered diagram

`Stacks.CechFamilySystem.cechDiagram F V : F.GenSet V ⥤ CochainComplex (ModuleCat (R.obj V)) ℕ`

together with, for each arrow `a : V ⟶ W` of `Cᵒᵖ`, a comparison
`Stacks.CechFamilySystem.cechTransport F a S` from the Čech complex of the product family of `S`
to the one of the product family of the restricted index, semilinear over the restriction map of
`R`. The two divisibility facts the comparisons consume are exactly the two the family system
supplies (`Stacks.CechFamilySystem.FamilySystem.exists_dvd_fam_of_le` and
`Stacks.CechFamilySystem.FamilySystem.exists_dvd_map_fam`).

This is [Stacks, Tag 099D]'s diagram `Stacks.PairSite.cechDiagram` with the ring replaced by a
presheaf of rings. The one substantive difference is that a presheaf is functorial only
*propositionally*: `R.map (𝟙 V)` is the identity and `R.map (a ≫ b)` the composite only up to
`R.map_id` and `R.map_comp`, where for a morphism of pairs both hold on the nose. Every
comparison map below therefore has to be compared across a change of the ring map it is taken
along, which is what `Stacks.CechFamilySystem.genRingTerm_congr_ringHom` is for: the comparison
depends on the ring map through nothing but the map itself, the divisibility data being
propositions, so equal ring maps give equal comparisons.

## Main definitions

* `Stacks.CechFamilySystem.cechDiagram`: the filtered diagram at an object.
* `Stacks.CechFamilySystem.cechTransport`: the comparison along an arrow of the base category.

## Main results

* `Stacks.CechFamilySystem.cechDiagram_map_comp_cechTransport`: the transport commutes with the
  transitions of the diagram.
* `Stacks.CechFamilySystem.cechTransport_id_apply`: the transport along an identity is the
  transition of the diagram along `S ≤ GenSet.map (𝟙 V) S`.
* `Stacks.CechFamilySystem.cechTransport_comp_apply`: the transports compose, up to the
  transition along `GenSet.map (a ≫ b) S ≤ GenSet.map b (GenSet.map a S)`.

## References

* [Stacks Project, Tag 099D](https://stacks.math.columbia.edu/tag/099D)
* [Stacks Project, Tag 099E](https://stacks.math.columbia.edu/tag/099E)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace Stacks.CechFamilySystem

open FamilySystem

/-! ### The comparison does not depend on the spelling of the ring map -/

/-- **Equal ring maps give equal comparison maps.** The divisibility datum a comparison map
carries is a proposition, so it is determined by the ring map; this is the congruence that lets
a comparison taken along `R.map (𝟙 V)` be read as one taken along the identity, and one taken
along `R.map (a ≫ b)` as one taken along the composite. -/
theorem genRingTerm_congr_ringHom {A B : Type u} [CommRing A] [CommRing B] {r s : ℕ}
    {φ ψ : A →+* B} (hφ : φ = ψ) (f : Fin r → A) (g : Fin s → B) (α : Fin s → Fin r)
    (hα : ∀ j : Fin s, ∃ n : ℕ, φ (f (α j)) ∣ g j ^ n)
    (hψ : ∀ j : Fin s, ∃ n : ℕ, ψ (f (α j)) ∣ g j ^ n) (p : ℕ) (x : Cech.cechTerm f A p) :
    Cech.genRingTerm φ f g α hα p x = Cech.genRingTerm ψ f g α hψ p x := by
  subst hφ
  rfl

variable {C : Type u} [Category.{u} C] {R : Cᵒᵖ ⥤ CommRingCat.{u}} (F : FamilySystem R)

/-! ### The filtered diagram at an object -/

/-- **The filtered diagram of Čech complexes at an object.** Its value at a nonempty finite set
`S` of distinguished families is the extended alternating Čech complex of the product family of
`S`, and its transition along `S ≤ T` is the comparison map of `Cech.cechGenMap` for the
divisibility `fam S (idxLe h k) ∣ fam T k`. -/
def cechDiagram (V : Cᵒᵖ) : F.GenSet V ⥤ CochainComplex (ModuleCat.{u} (R.obj V)) ℕ where
  obj S := Cech.cechComplex (fam S) (R.obj V)
  map {_ _} h := Cech.cechGenMap (fam _) (fam _) (idxLe (leOfHom h))
    (exists_dvd_fam_of_le (leOfHom h)) (R.obj V)
  map_id S := by
    have hid : ∀ j : Fin (famCard S), ∃ n : ℕ, fam S (id j) ∣ fam S j ^ n :=
      fun j => ⟨1, by rw [pow_one]; exact dvd_rfl⟩
    exact (Cech.cechGenMap_congr (fam S) (fam S) _ _ (R.obj V) hid (idxLe_refl S)).trans
      (Cech.cechGenMap_id (fam S) (R.obj V) hid)
  map_comp {S T U} h₁ h₂ := by
    have hαβ : ∀ k : Fin (famCard U), ∃ n : ℕ,
        fam S (idxLe (leOfHom h₁) (idxLe (leOfHom h₂) k)) ∣ fam U k ^ n := fun k =>
      ⟨1, by
        rw [pow_one]
        exact (fam_dvd_of_le (leOfHom h₁) (idxLe (leOfHom h₂) k)).trans
          (fam_dvd_of_le (leOfHom h₂) k)⟩
    exact (Cech.cechGenMap_congr (fam S) (fam U) _ _ (R.obj V) hαβ
          (idxLe_trans (leOfHom h₁) (leOfHom h₂))).trans
      (Cech.cechGenMap_comp (fam S) (fam T) _ _ (R.obj V) (fam U)
        (idxLe (leOfHom h₂)) _ hαβ).symm

/-- The value of `cechDiagram` at `S` is the Čech complex of the product family of `S`. -/
@[simp]
theorem cechDiagram_obj (V : Cᵒᵖ) (S : F.GenSet V) :
    (cechDiagram F V).obj S = Cech.cechComplex (fam S) (R.obj V) := rfl

/-- The transition of `cechDiagram` along `S ⟶ T` is the comparison map `Cech.cechGenMap`. -/
theorem cechDiagram_map (V : Cᵒᵖ) {S T : F.GenSet V} (h : S ⟶ T) :
    (cechDiagram F V).map h = Cech.cechGenMap (fam S) (fam T) (idxLe (leOfHom h))
      (exists_dvd_fam_of_le (leOfHom h)) (R.obj V) := rfl

/-- The degreewise diagram of Čech terms at an object. -/
abbrev cechTermDiagram (V : Cᵒᵖ) (n : ℕ) : F.GenSet V ⥤ ModuleCat.{u} (R.obj V) :=
  cechDiagram F V ⋙ HomologicalComplex.eval _ _ n

/-! ### The transport along an arrow of the base category -/

/-- The divisibility datum of the composite of a transition of the diagram with the
transport. -/
theorem exists_dvd_idxLe_idxMap {V W : Cᵒᵖ} (a : V ⟶ W) {S T : F.GenSet V} (hST : S ≤ T)
    (k : Fin (famCard (GenSet.map a T))) :
    ∃ n : ℕ, (R.map a).hom (fam S (idxLe hST (idxMap a T k))) ∣ fam (GenSet.map a T) k ^ n := by
  obtain ⟨n, hn⟩ := exists_dvd_map_fam a T k
  exact ⟨n, dvd_trans (map_dvd _ (fam_dvd_of_le hST _)) hn⟩

/-- **The comparison along an arrow of the base category.** It is the change of rings along the
restriction map of `R`, followed by the same-ring comparison from the image of the product
family of `S` to the product family of the restricted index — the composite being
`Cech.cechGenRingMap` in one step. -/
def cechTransport {V W : Cᵒᵖ} (a : V ⟶ W) (S : F.GenSet V) :
    Cech.cechComplex (fam S) (R.obj V) ⟶
      ((ModuleCat.restrictScalars (R.map a).hom).mapHomologicalComplex (ComplexShape.up ℕ)).obj
        (Cech.cechComplex (fam (GenSet.map a S)) (R.obj W)) :=
  Cech.cechGenRingMap (R.map a).hom (fam S) (fam (GenSet.map a S)) (idxMap a S)
    (exists_dvd_map_fam a S)

/-- In degree `p`, the underlying linear map of `cechTransport` is `Cech.genRingTerm`. -/
theorem cechTransport_f_hom {V W : Cᵒᵖ} (a : V ⟶ W) (S : F.GenSet V) (p : ℕ) :
    ((cechTransport F a S).f p).hom =
      Cech.genRingTerm (R.map a).hom (fam S) (fam (GenSet.map a S)) (idxMap a S)
        (exists_dvd_map_fam a S) p :=
  rfl

/-- **The transport commutes with the transitions of the diagram.** -/
theorem cechDiagram_map_comp_cechTransport {V W : Cᵒᵖ} (a : V ⟶ W) {S T : F.GenSet V}
    (h : S ⟶ T) :
    (cechDiagram F V).map h ≫ cechTransport F a T =
      cechTransport F a S ≫
        ((ModuleCat.restrictScalars (R.map a).hom).mapHomologicalComplex
          (ComplexShape.up ℕ)).map
            ((cechDiagram F W).map (homOfLE (GenSet.map_monotone a (leOfHom h)))) := by
  refine HomologicalComplex.hom_ext _ _ fun p => ModuleCat.hom_ext ?_
  refine Eq.trans (Cech.genRingTerm_comp_genTerm (R.map a).hom (fam S) (fam T)
    (fam (GenSet.map a T)) (idxLe (leOfHom h)) (exists_dvd_fam_of_le (leOfHom h))
    (idxMap a T) (exists_dvd_map_fam a T)
    (idxLe (leOfHom h) ∘ idxMap a T) (exists_dvd_idxLe_idxMap F a (leOfHom h)) rfl p) ?_
  exact (Cech.genTerm_comp_genRingTerm (R.map a).hom (fam S) (fam (GenSet.map a S))
    (fam (GenSet.map a T)) (idxMap a S) (exists_dvd_map_fam a S)
    (idxLe (GenSet.map_monotone a (leOfHom h)))
    (exists_dvd_fam_of_le (GenSet.map_monotone a (leOfHom h)))
    (idxLe (leOfHom h) ∘ idxMap a T) (exists_dvd_idxLe_idxMap F a (leOfHom h))
    (idxLe_idxMap (leOfHom h) a).symm p).symm

/-! ### The transport along an identity -/

/-- The restriction map along an identity is the identity ring map. -/
private theorem hom_map_id (V : Cᵒᵖ) : (R.map (𝟙 V)).hom = RingHom.id (R.obj V) :=
  congrArg CommRingCat.Hom.hom (R.map_id V)

/-- The restriction map along a composite is the composite of the restriction maps. -/
private theorem hom_map_comp {V W Y : Cᵒᵖ} (a : V ⟶ W) (b : W ⟶ Y) :
    (R.map (a ≫ b)).hom = (R.map b).hom.comp (R.map a).hom :=
  congrArg CommRingCat.Hom.hom (R.map_comp a b)

/-- **The transport along an identity is a transition of the diagram**: the one along the
inclusion `S ≤ GenSet.map (𝟙 V) S`, which is an equality of indices but only propositionally,
`Finset.image` of the identity not being the identity on the nose. -/
theorem cechTransport_id_apply (V : Cᵒᵖ) (S : F.GenSet V) (n : ℕ)
    (x : Cech.cechTerm (fam S) (R.obj V) n) :
    ((cechTransport F (𝟙 V) S).f n).hom x =
      (((cechDiagram F V).map (homOfLE (GenSet.map_id S).ge)).f n).hom x := by
  have hmap := hom_map_id (R := R) V
  have hid : ∀ k : Fin (famCard (GenSet.map (𝟙 V) S)), ∃ m : ℕ,
      (RingHom.id (R.obj V)) (fam S (idxMap (𝟙 V) S k)) ∣ fam (GenSet.map (𝟙 V) S) k ^ m :=
    fun k => hmap ▸ exists_dvd_map_fam (𝟙 V) S k
  refine Eq.trans (genRingTerm_congr_ringHom hmap (fam S) (fam (GenSet.map (𝟙 V) S))
    (idxMap (𝟙 V) S) (exists_dvd_map_fam (𝟙 V) S) hid n x) ?_
  refine Eq.trans (LinearMap.congr_fun (Cech.genRingTerm_id_ring (fam S)
    (fam (GenSet.map (𝟙 V) S)) (idxMap (𝟙 V) S) hid n) x) ?_
  exact LinearMap.congr_fun (Cech.genTerm_congr (fam S) (fam (GenSet.map (𝟙 V) S))
    (idxMap (𝟙 V) S) hid (R.obj V) (exists_dvd_fam_of_le (GenSet.map_id S).ge)
    (idxMap_id S) n) x

/-! ### The transport along a composite -/

/-- The divisibility datum of the composite of two transports. -/
theorem exists_dvd_idxMap_idxMap {V W Y : Cᵒᵖ} (a : V ⟶ W) (b : W ⟶ Y) (S : F.GenSet V)
    (k : Fin (famCard (GenSet.map b (GenSet.map a S)))) :
    ∃ n : ℕ, ((R.map b).hom.comp (R.map a).hom)
        (fam S ((idxMap a S ∘ idxMap b (GenSet.map a S)) k)) ∣
      fam (GenSet.map b (GenSet.map a S)) k ^ n := by
  obtain ⟨m, hm⟩ := exists_dvd_map_fam b (GenSet.map a S) k
  obtain ⟨c, hc⟩ := exists_dvd_map_fam a S (idxMap b (GenSet.map a S) k)
  refine ⟨m * c, ?_⟩
  have h1 := map_dvd (R.map b).hom hc
  rw [map_pow] at h1
  rw [pow_mul]
  exact h1.trans (pow_dvd_pow_of_dvd hm c)

/-- The divisibility datum of the composite, read along the restriction map of the composite
arrow. -/
theorem exists_dvd_idxMap_comp {V W Y : Cᵒᵖ} (a : V ⟶ W) (b : W ⟶ Y) (S : F.GenSet V)
    (k : Fin (famCard (GenSet.map b (GenSet.map a S)))) :
    ∃ n : ℕ, (R.map (a ≫ b)).hom
        (fam S ((idxMap a S ∘ idxMap b (GenSet.map a S)) k)) ∣
      fam (GenSet.map b (GenSet.map a S)) k ^ n := by
  have hmap := hom_map_comp (R := R) a b
  rw [hmap]
  exact exists_dvd_idxMap_idxMap F a b S k

/-- **The transports compose**, the first half: the composite of the two transports is a single
comparison, taken along the composite of the two restriction maps. -/
theorem cechTransport_comp_apply₁ {V W Y : Cᵒᵖ} (a : V ⟶ W) (b : W ⟶ Y) (S : F.GenSet V)
    (n : ℕ) (x : Cech.cechTerm (fam S) (R.obj V) n) :
    ((cechTransport F b (GenSet.map a S)).f n).hom (((cechTransport F a S).f n).hom x) =
      Cech.genRingTerm ((R.map b).hom.comp (R.map a).hom) (fam S)
        (fam (GenSet.map b (GenSet.map a S)))
        (idxMap a S ∘ idxMap b (GenSet.map a S))
        (exists_dvd_idxMap_idxMap F a b S) n x :=
  LinearMap.congr_fun (Cech.genRingTerm_comp (R.map a).hom (R.map b).hom
    (fam S) (fam (GenSet.map a S)) (fam (GenSet.map b (GenSet.map a S)))
    (idxMap a S) (idxMap b (GenSet.map a S))
    (exists_dvd_map_fam a S) (exists_dvd_map_fam b (GenSet.map a S))
    (exists_dvd_idxMap_idxMap F a b S) n) x

/-- **The transports compose**, the second half: the single comparison factors through the
transport along `a ≫ b`, up to the transition of the diagram along the inclusion
`GenSet.map (a ≫ b) S ≤ GenSet.map b (GenSet.map a S)`. -/
theorem cechTransport_comp_apply₂ {V W Y : Cᵒᵖ} (a : V ⟶ W) (b : W ⟶ Y) (S : F.GenSet V)
    (n : ℕ) (x : Cech.cechTerm (fam S) (R.obj V) n) :
    Cech.genRingTerm ((R.map b).hom.comp (R.map a).hom) (fam S)
        (fam (GenSet.map b (GenSet.map a S)))
        (idxMap a S ∘ idxMap b (GenSet.map a S))
        (exists_dvd_idxMap_idxMap F a b S) n x =
      (((cechDiagram F Y).map (homOfLE (GenSet.map_map a b S).ge)).f n).hom
        (((cechTransport F (a ≫ b) S).f n).hom x) := by
  have hmap := hom_map_comp (R := R) a b
  refine Eq.trans ?_ (congrArg
    (fun y => (((cechDiagram F Y).map (homOfLE (GenSet.map_map a b S).ge)).f n).hom y)
    (genRingTerm_congr_ringHom hmap (fam S) (fam (GenSet.map (a ≫ b) S)) (idxMap (a ≫ b) S)
      (exists_dvd_map_fam (a ≫ b) S) (hmap ▸ exists_dvd_map_fam (a ≫ b) S) n x)).symm
  exact (LinearMap.congr_fun (Cech.genTerm_comp_genRingTerm ((R.map b).hom.comp (R.map a).hom)
    (fam S) (fam (GenSet.map (a ≫ b) S)) (fam (GenSet.map b (GenSet.map a S)))
    (idxMap (a ≫ b) S) (hmap ▸ exists_dvd_map_fam (a ≫ b) S)
    (idxLe (GenSet.map_map a b S).ge) (exists_dvd_fam_of_le (GenSet.map_map a b S).ge)
    (idxMap a S ∘ idxMap b (GenSet.map a S)) (exists_dvd_idxMap_idxMap F a b S)
    (idxMap_comp a b S) n) x).symm

/-- **The transports compose**, up to the transition of the diagram along the inclusion
`GenSet.map (a ≫ b) S ≤ GenSet.map b (GenSet.map a S)`. -/
theorem cechTransport_comp_apply {V W Y : Cᵒᵖ} (a : V ⟶ W) (b : W ⟶ Y) (S : F.GenSet V)
    (n : ℕ) (x : Cech.cechTerm (fam S) (R.obj V) n) :
    ((cechTransport F b (GenSet.map a S)).f n).hom (((cechTransport F a S).f n).hom x) =
      (((cechDiagram F Y).map (homOfLE (GenSet.map_map a b S).ge)).f n).hom
        (((cechTransport F (a ≫ b) S).f n).hom x) :=
  (cechTransport_comp_apply₁ F a b S n x).trans (cechTransport_comp_apply₂ F a b S n x)

end Stacks.CechFamilySystem

end
