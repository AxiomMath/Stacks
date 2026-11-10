module

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import Mathlib.CategoryTheory.Subobject.Lattice
public import Mathlib.CategoryTheory.Subobject.Limits
public import Mathlib.Data.Int.Interval
public import StacksFrontier.Algebra.Homology.DerivedCategory.Filtered.Defs
import Mathlib.Tactic.Ring
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Filtered injective objects of the category of finite filtered objects

Let `𝒜` be an abelian category. An object `I` of `Fil^f(𝒜)` is filtered injective
(`CategoryTheory.FilteredObject.IsFilteredInjective`, [Stacks, Tag 015P]) if every graded piece
`gr^p(I)` is an injective object of `𝒜`. This file proves [Stacks, Tag 05TP]: `I` is filtered
injective if and only if it is isomorphic, as a filtered object, to a finite direct sum
`⨁_{a ≤ n ≤ b} I_n` of injective objects with the filtration `F^p = ⨁_{n ≥ p} I_n`
(`CategoryTheory.FilteredObject.stdBiprod`). The forward direction splits the short exact
sequences `0 → F^{p + 1} → F^p → gr^p → 0` one step at a time, their quotients being injective.

## Main results

* `CategoryTheory.FilteredObject.isFilteredInjective_iff_nonempty_iso_stdBiprod`: a finite
  filtered object is filtered injective if and only if it is isomorphic to some
  `FilteredObject.stdBiprod a b Inj` with every `Inj n` injective.

## References

* [Stacks, Tag 015P](https://stacks.math.columbia.edu/tag/015P)
* [Stacks, Tag 05TP](https://stacks.math.columbia.edu/tag/05TP)
-/

section

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory Limits Opposite

namespace CategoryTheory.FilteredObject.InjectiveSplitting

variable {𝒜 : Type*} [Category 𝒜] [Abelian 𝒜]

noncomputable section

/-- The inclusion `ι` composed with the projection onto a sub-biproduct lands in the
corresponding summand when the predicate holds. -/
theorem aux_iotosub {J : Type} [Finite J] (f : J → 𝒜) [HasFiniteBiproducts 𝒜]
    (Pp : J → Prop) (k : J) (hk : Pp k) :
    biproduct.ι f k ≫ biproduct.toSubtype f Pp
      = biproduct.ι (Subtype.restrict Pp f) ⟨k, hk⟩ := by
  classical
  rw [biproduct.ι_toSubtype, dite_eq_left hk]

/-- If `Pp k` holds, the inclusion `ι` of the `k`-th summand composed with the diagonal map
`⨁ f → ⨁ f` that is the identity on the summands satisfying `Pp` and zero elsewhere is `ι`. -/
theorem aux_map {J : Type} [Finite J] (f : J → 𝒜) [HasFiniteBiproducts 𝒜]
    (Pp : J → Prop) [DecidablePred Pp] (k : J) (hk : Pp k) :
    biproduct.ι f k ≫ (biproduct.map fun j => if Pp j then 𝟙 (f j) else 0) = biproduct.ι f k := by
  rw [biproduct.ι_map, ite_eq_left hk, Category.id_comp]

/-- If `Qp ⊆ Pp`, the canonical map `⨁_{Qp} → ⨁_{Pp}` (the inclusion of sub-biproducts)
composed with the inclusion of `⨁_{Pp}` recovers the inclusion of `⨁_{Qp}`. -/
theorem hgm_lemma {J : Type} [Finite J] (f : J → 𝒜) [HasFiniteBiproducts 𝒜]
    (Pp Qp : J → Prop)
    (himp : ∀ j, Qp j → Pp j) :
    (biproduct.fromSubtype f Qp ≫ biproduct.toSubtype f Pp) ≫ biproduct.fromSubtype f Pp
      = biproduct.fromSubtype f Qp := by
  classical
  rw [Category.assoc, biproduct.toSubtype_fromSubtype]
  apply biproduct.hom_ext'
  intro k
  rw [← Category.assoc, biproduct.ι_fromSubtype]
  exact aux_map f Pp k.1 (himp k.1 k.2)

/-- The canonical inclusion `⨁_{Qp} → ⨁_{Pp}` (for `Qp ⊆ Pp`) is, up to a reindexing
isomorphism of the source, the sub-biproduct inclusion `fromSubtype` of the restricted
predicate on `Subtype Pp`. -/
theorem reindex_g {J : Type} [Finite J] (f : J → 𝒜) [HasFiniteBiproducts 𝒜]
    (Pp Qp : J → Prop)
    (himp : ∀ j, Qp j → Pp j) :
    ∃ (R : (⨁ Subtype.restrict Qp f)
        ≅ (⨁ Subtype.restrict (fun j : Subtype Pp => Qp j.1) (Subtype.restrict Pp f))),
      biproduct.fromSubtype f Qp ≫ biproduct.toSubtype f Pp
        = R.hom ≫ biproduct.fromSubtype (Subtype.restrict Pp f)
            (fun j : Subtype Pp => Qp j.1) := by
  classical
  let e : Subtype Qp ≃ Subtype (fun j : Subtype Pp => Qp j.1) :=
  { toFun := fun k => ⟨⟨k.1, himp k.1 k.2⟩, k.2⟩
    invFun := fun j => ⟨j.1.1, j.2⟩
    left_inv := fun k => rfl
    right_inv := fun j => rfl }
  let w : (k : Subtype Qp) →
      (Subtype.restrict (fun j : Subtype Pp => Qp j.1) (Subtype.restrict Pp f)) (e k)
        ≅ (Subtype.restrict Qp f) k :=
    fun k => eqToIso rfl
  refine ⟨biproduct.whiskerEquiv e w, ?_⟩
  apply biproduct.hom_ext'
  intro k
  have lhs : biproduct.ι (Subtype.restrict Qp f) k ≫
      (biproduct.fromSubtype f Qp ≫ biproduct.toSubtype f Pp)
      = biproduct.ι (Subtype.restrict Pp f) ⟨k.1, himp k.1 k.2⟩ := by
    rw [← Category.assoc, biproduct.ι_fromSubtype]
    exact aux_iotosub f Pp k.1 (himp k.1 k.2)
  have rhs : biproduct.ι (Subtype.restrict Qp f) k ≫ (biproduct.whiskerEquiv e w).hom ≫
      biproduct.fromSubtype (Subtype.restrict Pp f) (fun j : Subtype Pp => Qp j.1)
      = biproduct.ι (Subtype.restrict Pp f) ⟨k.1, himp k.1 k.2⟩ := by
    rw [← Category.assoc, biproduct.whiskerEquiv_hom, biproduct.ι_desc, Category.assoc,
      biproduct.ι_fromSubtype]
    exact Category.id_comp _
  rw [lhs, rhs]

/-- The cokernel of the sub-biproduct inclusion `fromSubtype f' q'` is the complementary
sub-biproduct `⨁_{¬q'}`. -/
def cokernelFromSubtypeIso {K : Type} [Fintype K] [DecidableEq K] (f' : K → 𝒜)
    [HasFiniteBiproducts 𝒜] (q' : K → Prop) [DecidablePred q'] :
    cokernel (biproduct.fromSubtype f' q') ≅ ⨁ (Subtype.restrict (fun j => ¬ q' j) f') := by
  have cross1 : biproduct.fromSubtype f' q' ≫ biproduct.toSubtype f' (fun j => ¬ q' j) = 0 := by
    ext j k
    simp only [biproduct.ι_fromSubtype_assoc, Category.assoc, biproduct.toSubtype_π, zero_comp,
      comp_zero]
    have hne : (↑k : K) ≠ (↑j : K) := fun h => j.2 (h ▸ k.2)
    exact biproduct.ι_π_ne f' hne
  have cross2 : biproduct.fromSubtype f' (fun j => ¬ q' j) ≫ biproduct.toSubtype f' q' = 0 := by
    ext j k
    simp only [biproduct.ι_fromSubtype_assoc, Category.assoc, biproduct.toSubtype_π, zero_comp,
      comp_zero]
    have hne : (↑k : K) ≠ (↑j : K) := fun h => k.2 (h ▸ j.2)
    exact biproduct.ι_π_ne f' hne
  let D : (⨁ f') ≅ (⨁ Subtype.restrict q' f') ⊞ (⨁ Subtype.restrict (fun j => ¬ q' j) f') :=
  { hom := biprod.lift (biproduct.toSubtype f' q') (biproduct.toSubtype f' (fun j => ¬ q' j))
    inv := biprod.desc (biproduct.fromSubtype f' q') (biproduct.fromSubtype f' (fun j => ¬ q' j))
    hom_inv_id := by
      rw [biprod.lift_desc, biproduct.toSubtype_fromSubtype, biproduct.toSubtype_fromSubtype]
      ext j k
      simp only [Preadditive.add_comp, Preadditive.comp_add, biproduct.map_π, Category.id_comp]
      by_cases hq : q' j <;> simp [hq]
    inv_hom_id := by
      apply biprod.hom_ext' <;> apply biprod.hom_ext
      · simp [biproduct.fromSubtype_toSubtype]
      · simp [cross1]
      · simp [cross2]
      · simp [biproduct.fromSubtype_toSubtype] }
  refine (cokernel.mapIso (biproduct.fromSubtype f' q') biprod.inl (Iso.refl _) D ?_) ≪≫
    cokernelBiprodInlIso
  show biproduct.fromSubtype f' q' ≫ D.hom = (Iso.refl _).hom ≫ biprod.inl
  simp only [D, Iso.refl_hom, Category.id_comp, biprod.lift_eq, Preadditive.comp_add,
    ← Category.assoc, biproduct.fromSubtype_toSubtype, cross1, zero_comp, add_zero,
    Category.id_comp]

/-- The cokernel of `Subobject.ofLE` between two subobjects presented as `Subobject.mk`
of monos is the cokernel of the comparison map `gm`. -/
def cokernelOfLEMkIso' {B A₁ A₂ : 𝒜} (f₁ : A₁ ⟶ B) (f₂ : A₂ ⟶ B) [Mono f₁] [Mono f₂]
    (S T : Subobject B) (hS : S = Subobject.mk f₁) (hT : T = Subobject.mk f₂)
    (gm : A₁ ⟶ A₂) (hgm : gm ≫ f₂ = f₁) (h : S ≤ T) :
    cokernel (Subobject.ofLE S T h) ≅ cokernel gm := by
  subst hS hT
  rw [Subobject.ofLE_mk_le_mk_of_comm gm hgm]
  refine cokernel.mapIso _ _ (Subobject.underlyingIso f₁) (Subobject.underlyingIso f₂) ?_
  simp

open Classical in
/-- The standard decreasing filtration on a finite biproduct `⨁_{a ≤ n ≤ b} I_n`: its `p`-th
term is the sub-biproduct `⨁_{n ≥ p, a ≤ n ≤ b} I_n`, the supremum of the images of the
inclusions `I_n → ⨁` over the indices `n ≥ p`. -/
def stdFil (a b : ℤ) (Inj : ℤ → 𝒜) (p : ℤ) :
    haveI : HasFiniteBiproducts 𝒜 := HasFiniteBiproducts.of_hasFiniteProducts
    Subobject (⨁ (fun n : (Finset.Icc a b) => Inj n.1)) :=
  haveI : HasFiniteBiproducts 𝒜 := HasFiniteBiproducts.of_hasFiniteProducts
  Finset.sup (Finset.univ.filter (fun n : (Finset.Icc a b) => p ≤ (n : ℤ)))
    (fun n => Subobject.mk (biproduct.ι (fun n : (Finset.Icc a b) => Inj n.1) n))

/-- The filtration `stdFil a b Inj` is decreasing: `stdFil a b Inj q ≤ stdFil a b Inj p`
whenever `p ≤ q`. -/
theorem stdFil_antitone (a b : ℤ) (Inj : ℤ → 𝒜) :
    ∀ ⦃p q : ℤ⦄, p ≤ q → stdFil a b Inj q ≤ stdFil a b Inj p := by
  intro p q hpq
  classical
  apply Finset.sup_mono
  intro n hn
  simp only [Finset.mem_filter] at hn ⊢
  exact ⟨hn.1, le_trans hpq hn.2⟩

/-- The sub-biproduct inclusion `fromSubtype f P` is a monomorphism. -/
private theorem mono_fromSubtype {J : Type} [Finite J] [HasFiniteBiproducts 𝒜] (f : J → 𝒜)
    (P : J → Prop) : Mono (biproduct.fromSubtype f P) :=
  ⟨fun {Z} g h H => by
    simpa [biproduct.fromSubtype_toSubtype] using H =≫ biproduct.toSubtype f P⟩

/-- If the predicate `P` holds everywhere, the projection `toSubtype f P` is an isomorphism. -/
private theorem isIso_toSubtype_of_forall {J : Type} [Finite J] [HasFiniteBiproducts 𝒜]
    (f : J → 𝒜) (P : J → Prop) (hP : ∀ j, P j) : IsIso (biproduct.toSubtype f P) := by
  classical
  refine ⟨biproduct.fromSubtype f P, ?_, biproduct.fromSubtype_toSubtype f P⟩
  rw [biproduct.toSubtype_fromSubtype]
  apply biproduct.hom_ext'
  intro k
  rw [biproduct.ι_map, ite_eq_left (hP k), Category.id_comp, Category.comp_id]

/-- `stdFil a b Inj p` coincides with the subobject `Subobject.mk` of the sub-biproduct
inclusion `fromSubtype` for the predicate `n ↦ p ≤ n`. -/
theorem stdFil_eq_mk (a b : ℤ) (Inj : ℤ → 𝒜) (p : ℤ) :
    haveI : HasFiniteBiproducts 𝒜 := HasFiniteBiproducts.of_hasFiniteProducts
    haveI hM : Mono (biproduct.fromSubtype (fun n : (Finset.Icc a b) => Inj n.1)
        (fun n => p ≤ (n:ℤ))) :=
      ⟨fun {Z} g h H => by
        have := H =≫ biproduct.toSubtype (fun n : (Finset.Icc a b) => Inj n.1) (fun n => p ≤ (n:ℤ))
        simpa [biproduct.fromSubtype_toSubtype] using this⟩
    stdFil a b Inj p = Subobject.mk (biproduct.fromSubtype
      (fun n : (Finset.Icc a b) => Inj n.1) (fun n => p ≤ (n:ℤ))) := by
  classical
  have : HasFiniteBiproducts 𝒜 := HasFiniteBiproducts.of_hasFiniteProducts
  set f : (Finset.Icc a b) → 𝒜 := fun n => Inj n.1 with hf
  set P : (Finset.Icc a b) → Prop := fun n => p ≤ (n:ℤ) with hP
  have hM := mono_fromSubtype f P
  have hle : ∀ (j : Subtype P), Subobject.mk (biproduct.ι f ↑j) ≤ stdFil a b Inj p := by
    intro j
    unfold stdFil
    apply Finset.le_sup (f := fun n => Subobject.mk (biproduct.ι f n))
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact j.2
  apply le_antisymm
  · unfold stdFil
    rw [Finset.sup_le_iff]
    intro n hn
    simp only [Finset.mem_filter] at hn
    refine Subobject.mk_le_mk_of_comm (biproduct.ι (Subtype.restrict P f) ⟨n, hn.2⟩) ?_
    rw [biproduct.ι_fromSubtype]
  · refine Subobject.mk_le_of_comm
      (biproduct.desc (fun j => (stdFil a b Inj p).factorThru (biproduct.ι f ↑j)
        (Subobject.factors_of_le _ (hle j) (Subobject.mk_factors_self _)))) ?_
    apply biproduct.hom_ext'
    intro k
    rw [biproduct.ι_desc_assoc, Subobject.factorThru_arrow, biproduct.ι_fromSubtype]

/-- When `p ∉ Finset.Icc a b`, no index is dropped between `p` and `p+1`, so the two
filtration terms agree. -/
theorem stdFil_eq_of_not_mem (a b : ℤ) (Inj : ℤ → 𝒜) (p : ℤ) (hp : p ∉ Finset.Icc a b) :
    stdFil a b Inj (p+1) = stdFil a b Inj p := by
  classical
  unfold stdFil
  congr 1
  apply Finset.filter_congr
  intro n _
  simp only [Finset.mem_Icc] at hp
  have hn := n.2
  simp only [Finset.mem_Icc] at hn
  refine ⟨fun h => by omega, fun h => ?_⟩
  have : (n:ℤ) ≠ p := by intro he; rw [he] at hn; omega
  omega

/-- If every `Inj n` is injective, then the `p`-th graded piece of `stdFil a b Inj`, the
cokernel of the inclusion `stdFil a b Inj (p + 1) ⟶ stdFil a b Inj p`, is injective. -/
theorem stdFil_gr_injective (a b : ℤ) (Inj : ℤ → 𝒜) (hInj : ∀ n, Injective (Inj n)) (p : ℤ) :
    haveI : HasFiniteBiproducts 𝒜 := HasFiniteBiproducts.of_hasFiniteProducts
    Injective (cokernel (Subobject.ofLE (stdFil a b Inj (p+1)) (stdFil a b Inj p)
      (stdFil_antitone a b Inj (by omega : p ≤ p + 1)))) := by
  classical
  have : HasFiniteBiproducts 𝒜 := HasFiniteBiproducts.of_hasFiniteProducts
  set f : (Finset.Icc a b) → 𝒜 := fun n => Inj n.1 with hf
  set Pp : (Finset.Icc a b) → Prop := fun n => p ≤ (n:ℤ) with hPp
  set Qp : (Finset.Icc a b) → Prop := fun n => p+1 ≤ (n:ℤ) with hQp
  have himp : ∀ j, Qp j → Pp j := by intro j hj; simp only [hQp, hPp] at *; omega
  have hMP := mono_fromSubtype f Pp
  have hMQ := mono_fromSubtype f Qp
  have e2 : stdFil a b Inj p = Subobject.mk (biproduct.fromSubtype f Pp) := stdFil_eq_mk a b Inj p
  have e1 : stdFil a b Inj (p+1) = Subobject.mk (biproduct.fromSubtype f Qp) :=
    stdFil_eq_mk a b Inj (p+1)
  by_cases hmem : p ∈ Finset.Icc a b
  · obtain ⟨R, hR⟩ := reindex_g f Pp Qp himp
    have : ∀ j, Injective
        ((Subtype.restrict (fun j : Subtype Pp => ¬ (fun j : Subtype Pp => Qp j.1) j)
        (Subtype.restrict Pp f)) j) := fun j => hInj _
    have hcompInj : Injective
        (⨁ (Subtype.restrict (fun j : Subtype Pp => ¬ (fun j : Subtype Pp => Qp j.1) j)
          (Subtype.restrict Pp f))) := inferInstance
    refine Injective.of_iso (?_ : _ ≅ cokernel _) hcompInj
    refine (cokernelFromSubtypeIso (Subtype.restrict Pp f) (fun j : Subtype Pp => Qp j.1)).symm
      ≪≫ ?_
    refine (cokernel.mapIso (biproduct.fromSubtype (Subtype.restrict Pp f)
        (fun j : Subtype Pp => Qp j.1))
      (biproduct.fromSubtype f Qp ≫ biproduct.toSubtype f Pp) R.symm (Iso.refl _) ?_) ≪≫ ?_
    · simp only [Iso.symm_hom, Iso.refl_hom, Category.comp_id]
      rw [hR, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
    · exact (cokernelOfLEMkIso' (biproduct.fromSubtype f Qp) (biproduct.fromSubtype f Pp)
        (stdFil a b Inj (p+1)) (stdFil a b Inj p) e1 e2
        (biproduct.fromSubtype f Qp ≫ biproduct.toSubtype f Pp) (hgm_lemma f Pp Qp himp) _).symm
  · have heq := stdFil_eq_of_not_mem a b Inj p hmem
    have iso := cokernelOfLEMkIso' (biproduct.fromSubtype f Pp) (biproduct.fromSubtype f Pp)
      (stdFil a b Inj (p+1)) (stdFil a b Inj p) (heq.trans e2) e2
      (𝟙 _) (Category.id_comp _)
      (stdFil_antitone a b Inj (by omega : p ≤ p + 1))
    refine Injective.of_iso iso.symm ?_
    have : IsZero (cokernel (𝟙 (⨁ Subtype.restrict Pp f))) := isZero_cokernel_of_epi _
    exact this.injective

section Decomposition

variable {X : 𝒜} (F : ℤ → Subobject X) (hF : Antitone F)

/-- The graded piece `F p / F (p + 1)` of a decreasing family `F` of subobjects of `X`, the
cokernel of the inclusion `F (p + 1) ⟶ F p`. -/
@[ega "0 11.1.1" "partial"]
def grSub (p : ℤ) : 𝒜 :=
  cokernel ((F (p + 1)).ofLE (F p) (hF (by omega)))

/-- An extension `X ⟶ gr^n` of the projection `cokernel.π : F^n → gr^n` along `F^n ⟶ X`,
which exists because `gr^n` is injective. -/
def gext (hI : ∀ p, Injective (grSub F hF p)) (n : ℤ) : X ⟶ grSub F hF n :=
  haveI := hI n
  Injective.factorThru
    (cokernel.π ((F (n+1)).ofLE (F n) (hF (by omega)))) (F n).arrow

/-- The restriction of `gext F hF hI n` to `F n` is the projection `F n ⟶ grSub F hF n`. -/
theorem gext_spec (hI : ∀ p, Injective (grSub F hF p)) (n : ℤ) :
    (F n).arrow ≫ gext F hF hI n
      = cokernel.π ((F (n+1)).ofLE (F n) (hF (by omega : n ≤ n+1))) := by
  have := hI n
  exact Injective.comp_factorThru _ _

/-- For `n + 1 ≤ p`, the map `gext F hF hI n` vanishes on `F p`. -/
theorem gext_vanish (hI : ∀ p, Injective (grSub F hF p)) (n p : ℤ) (hp : n + 1 ≤ p) :
    (F p).arrow ≫ gext F hF hI n = 0 := by
  have hle : F p ≤ F (n+1) := hF hp
  have h1 : (F p).arrow = (F p).ofLE (F (n+1)) hle ≫ (F (n+1)).arrow := by
    rw [Subobject.ofLE_arrow]
  rw [h1, Category.assoc]
  have h2 : (F (n+1)).arrow ≫ gext F hF hI n = 0 := by
    have h3 : (F (n+1)).arrow
        = (F (n+1)).ofLE (F n) (hF (by omega)) ≫ (F n).arrow := by
      rw [Subobject.ofLE_arrow]
    rw [h3, Category.assoc, gext_spec, cokernel.condition]
  rw [h2, comp_zero]

/-- Factoring through a sub-biproduct when the complementary components vanish. -/
theorem factor_through_fromSubtype {J : Type} [Finite J] (f : J → 𝒜)
    [HasFiniteBiproducts 𝒜] (P : J → Prop)
    {W : 𝒜} (w : W ⟶ ⨁ f) (hw : ∀ j, ¬ P j → w ≫ biproduct.π f j = 0) :
    w = (w ≫ biproduct.toSubtype f P) ≫ biproduct.fromSubtype f P := by
  classical
  apply biproduct.hom_ext
  intro j
  rw [Category.assoc]
  by_cases hP : P j
  · rw [Category.assoc, biproduct.fromSubtype_π, dite_eq_left hP]
    congr 1
    exact (biproduct.toSubtype_π f P ⟨j, hP⟩).symm
  · rw [Category.assoc, biproduct.fromSubtype_π, dite_eq_right hP, comp_zero, comp_zero, hw j hP]

/-- A morphism whose composite with `cokernel.π i` (for `i` mono) is zero factors through `i`. -/
theorem factor_through_mono_of_comp_cokernel {A B Z : 𝒜} (i : A ⟶ B) [Mono i] (kp : Z ⟶ B)
    (h : kp ≫ cokernel.π i = 0) : ∃ (kp' : Z ⟶ A), kp' ≫ i = kp :=
  ⟨_, (Abelian.monoIsKernelOfCokernel _ (cokernelIsCokernel i)).fac
    (KernelFork.ofι kp (by simpa using h)) WalkingParallelPair.zero⟩

/-- For `b < p` no summand has index at least `p`, so `stdFil a b Inj p` is `⊥`. -/
theorem stdFil_eq_bot (a b : ℤ) (Inj : ℤ → 𝒜) (p : ℤ) (hp : b < p) :
    stdFil a b Inj p = ⊥ := by
  classical
  unfold stdFil
  convert Finset.sup_empty
  rw [Finset.filter_eq_empty_iff]
  intro n _
  have := n.2
  simp only [Finset.mem_Icc] at this
  omega

/-- For `p ≤ a` every summand has index at least `p`, so `stdFil a b Inj p` is the whole
biproduct. -/
theorem stdFil_eq_top (a b : ℤ) (Inj : ℤ → 𝒜) {p : ℤ} (hp : p ≤ a) :
    stdFil a b Inj p = ⊤ := by
  classical
  have : HasFiniteBiproducts 𝒜 := HasFiniteBiproducts.of_hasFiniteProducts
  have hfull : ∀ n : (Finset.Icc a b), p ≤ (n : ℤ) := fun n => by
    have := n.2
    simp only [Finset.mem_Icc] at this
    omega
  have := mono_fromSubtype (fun n : (Finset.Icc a b) => Inj n.1) (fun n => p ≤ (n : ℤ))
  have := isIso_toSubtype_of_forall (fun n : (Finset.Icc a b) => Inj n.1)
    (fun n => p ≤ (n : ℤ)) hfull
  rw [stdFil_eq_mk, ← Subobject.isIso_iff_mk_eq_top]
  exact IsIso.of_isIso_fac_right (biproduct.fromSubtype_toSubtype _ _)

/-- Total-identity decomposition of a biproduct: if `e : K → J` is injective with image the
complement of a single index `kp`, then the sum of the diagonal idempotents over the image
(realized via `lift`/`desc` along `e`) plus the `kp` idempotent is the identity. -/
theorem biproduct_total_split [HasFiniteBiproducts 𝒜]
    {K J : Type} [Finite K] [Finite J]
    (f : J → 𝒜) (e : K → J) (he : Function.Injective e) (kp : J)
    (hkp : ∀ k, e k ≠ kp) (hcov : ∀ j, j ≠ kp → ∃ k, e k = j) :
    (biproduct.lift (fun k => biproduct.π f (e k)) ≫
       biproduct.desc (fun k => biproduct.ι f (e k)))
    + biproduct.π f kp ≫ biproduct.ι f kp = 𝟙 (⨁ f) := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have : Fintype J := Fintype.ofFinite J
  rw [biproduct.lift_desc, ← biproduct.total (f := f)]
  set g : J → (⨁ f ⟶ ⨁ f) := fun j => biproduct.π f j ≫ biproduct.ι f j with hg
  change (∑ k, g (e k)) + g kp = ∑ j, g j
  rw [← Finset.sum_image fun _ _ _ _ h => he h]
  have himage : Finset.univ.image e = Finset.univ.filter (fun j => j ≠ kp) := by
    ext j
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_filter]
    exact ⟨fun ⟨k, hk⟩ => hk ▸ hkp k, hcov j⟩
  rw [himage]
  have hk : g kp = ∑ j ∈ Finset.univ.filter (fun j => ¬ (j ≠ kp)), g j := by
    have hset : Finset.univ.filter (fun j => ¬ (j ≠ kp)) = {kp} := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_not, Finset.mem_singleton]
    rw [hset, Finset.sum_singleton]
  rw [hk, Finset.sum_filter_add_sum_filter_not]

/-- Let `g : X ⟶ ⨁_{a ≤ n ≤ b} gr^n` have components `gext F hF hI n`, and let `p ∈ [a, b]`.
If the composite `F^{p + 1} ⟶ X ⟶ ⨁_{n ≥ p + 1} gr^n` is an isomorphism, then so is the
composite `F^p ⟶ X ⟶ ⨁_{n ≥ p} gr^n`. -/
theorem psi_step (hI : ∀ p, Injective (grSub F hF p)) (a b : ℤ)
    (g : X ⟶ (haveI : HasFiniteBiproducts 𝒜 := HasFiniteBiproducts.of_hasFiniteProducts
      ⨁ (fun n : (Finset.Icc a b) => grSub F hF n.1)))
    (hg_π : haveI : HasFiniteBiproducts 𝒜 := HasFiniteBiproducts.of_hasFiniteProducts
      ∀ (n : Finset.Icc a b), g ≫ biproduct.π (fun n : (Finset.Icc a b) => grSub F hF n.1) n
        = gext F hF hI n.1)
    (p : ℤ) (hmem : p ∈ Finset.Icc a b)
    (hIH : haveI : HasFiniteBiproducts 𝒜 := HasFiniteBiproducts.of_hasFiniteProducts
      IsIso (((F (p+1)).arrow ≫ g) ≫ biproduct.toSubtype
        (fun n : (Finset.Icc a b) => grSub F hF n.1) (fun n => p + 1 ≤ (n:ℤ)))) :
    haveI : HasFiniteBiproducts 𝒜 := HasFiniteBiproducts.of_hasFiniteProducts
    IsIso (((F p).arrow ≫ g) ≫ biproduct.toSubtype
      (fun n : (Finset.Icc a b) => grSub F hF n.1) (fun n => p ≤ (n:ℤ))) := by
  classical
  have : HasFiniteBiproducts 𝒜 := HasFiniteBiproducts.of_hasFiniteProducts
  set j : ((F (p+1) : 𝒜)) ⟶ ((F p : 𝒜)) :=
    (F (p+1)).ofLE (F p) (hF (by omega : p ≤ p+1)) with hj
  have : Mono j := mono_of_mono_fac (Subobject.ofLE_arrow _)
  set S₁ : ShortComplex 𝒜 := ShortComplex.mk j (cokernel.π j) (cokernel.condition j) with hS₁
  have hS₁exact : S₁.ShortExact :=
    ShortComplex.ShortExact.mk (ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel j))
  set Pp : (Finset.Icc a b) → Prop := fun n => p ≤ (n:ℤ) with hPp
  set Qp : (Finset.Icc a b) → Prop := fun n => p+1 ≤ (n:ℤ) with hQp
  have himp : ∀ n, Qp n → Pp n := by
    intro n hn
    simp only [hQp, hPp] at *
    omega
  have hPp_p : Pp ⟨p, hmem⟩ := le_refl p
  set kp : Subtype Pp := ⟨⟨p, hmem⟩, hPp_p⟩ with hkp
  set e : Subtype Qp → Subtype Pp := fun n => ⟨n.1, himp n.1 n.2⟩ with he_def
  have he_inj : Function.Injective e := fun n n' h =>
    Subtype.ext (congrArg (fun x : Subtype Pp => (x : Finset.Icc a b)) h)
  have he_ne_kp : ∀ n, e n ≠ kp := fun n h => by
    have h₁ : (n.1 : ℤ) = p := congrArg (fun x : Subtype Pp => (x.1 : ℤ)) h
    have h₂ : p + 1 ≤ (n.1 : ℤ) := n.2
    omega
  have he_cov : ∀ jj : Subtype Pp, jj ≠ kp → ∃ n, e n = jj := fun jj hjj => by
    refine ⟨⟨jj.1, ?_⟩, rfl⟩
    have h₁ : p ≤ (jj.1 : ℤ) := jj.2
    change p + 1 ≤ (jj.1 : ℤ)
    by_contra hQ
    exact hjj (Subtype.ext (Subtype.ext (by change (jj.1 : ℤ) = p; omega)))
  set Sf : (⨁ (Subtype.restrict Qp (fun n : (Finset.Icc a b) => grSub F hF n.1))) ⟶
      (⨁ (Subtype.restrict Pp (fun n : (Finset.Icc a b) => grSub F hF n.1))) :=
    biproduct.desc
      (fun n => biproduct.ι
        (Subtype.restrict Pp (fun n : (Finset.Icc a b) => grSub F hF n.1)) (e n))
      with hSf
  set Sg : (⨁ (Subtype.restrict Pp (fun n : (Finset.Icc a b) => grSub F hF n.1))) ⟶ grSub F hF p :=
    biproduct.π (Subtype.restrict Pp (fun n : (Finset.Icc a b) => grSub F hF n.1)) kp with hSg
  have hSfg : Sf ≫ Sg = 0 := by
    apply biproduct.hom_ext'
    intro n
    rw [← Category.assoc, hSf, biproduct.ι_desc, hSg, comp_zero]
    exact biproduct.ι_π_ne _ (he_ne_kp n)
  set S₂ : ShortComplex 𝒜 := ShortComplex.mk Sf Sg hSfg with hS₂
  set rB : (⨁ (Subtype.restrict Pp (fun n : (Finset.Icc a b) => grSub F hF n.1))) ⟶
      (⨁ (Subtype.restrict Qp (fun n : (Finset.Icc a b) => grSub F hF n.1))) :=
    biproduct.lift
      (fun n => biproduct.π
        (Subtype.restrict Pp (fun n : (Finset.Icc a b) => grSub F hF n.1)) (e n))
      with hrB
  set sB : grSub F hF p ⟶ (⨁ (Subtype.restrict Pp (fun n : (Finset.Icc a b) => grSub F hF n.1))) :=
    biproduct.ι (Subtype.restrict Pp (fun n : (Finset.Icc a b) => grSub F hF n.1)) kp with hsB
  have hf_r : Sf ≫ rB = 𝟙 _ := by
    apply biproduct.hom_ext'
    intro n
    apply biproduct.hom_ext
    intro n'
    rw [← Category.assoc, hSf, biproduct.ι_desc, hrB, Category.assoc, biproduct.lift_π,
      Category.comp_id]
    by_cases h : n = n'
    · subst h
      rw [biproduct.ι_π_self]
      exact (biproduct.ι_π_self
        (Subtype.restrict Qp (fun n : (Finset.Icc a b) => grSub F hF n.1)) n).symm
    · rw [biproduct.ι_π_ne _ (fun hh => h (he_inj hh)), biproduct.ι_π_ne _ h]
  have hs_g : sB ≫ Sg = 𝟙 _ := by
    rw [hsB, hSg]
    exact biproduct.ι_π_self (Subtype.restrict Pp (fun n : (Finset.Icc a b) => grSub F hF n.1)) kp
  have hid : rB ≫ Sf + Sg ≫ sB = 𝟙 _ := by
    rw [hrB, hSf, hSg, hsB]
    exact biproduct_total_split (Subtype.restrict Pp (fun n : (Finset.Icc a b) => grSub F hF n.1))
      e he_inj kp he_ne_kp he_cov
  let splB : S₂.Splitting :=
  { r := rB
    s := sB
    f_r := hf_r
    s_g := hs_g
    id := hid }
  have hS₂exact : S₂.ShortExact := splB.shortExact
  set τ₁ : ((F (p+1) : 𝒜)) ⟶
      (⨁ (Subtype.restrict Qp (fun n : (Finset.Icc a b) => grSub F hF n.1))) :=
    ((F (p+1)).arrow ≫ g) ≫
      biproduct.toSubtype (fun n : (Finset.Icc a b) => grSub F hF n.1) Qp with hτ₁
  set τ₂ : ((F p : 𝒜)) ⟶ (⨁ (Subtype.restrict Pp (fun n : (Finset.Icc a b) => grSub F hF n.1))) :=
    ((F p).arrow ≫ g) ≫ biproduct.toSubtype (fun n : (Finset.Icc a b) => grSub F hF n.1) Pp with hτ₂
  have hcomm₂₃ : τ₂ ≫ Sg = cokernel.π j ≫ 𝟙 (cokernel j) := by
    rw [Category.comp_id, hτ₂, hSg, Category.assoc, biproduct.toSubtype_π]
    change ((F p).arrow ≫ g) ≫
      biproduct.π (fun n : (Finset.Icc a b) => grSub F hF n.1) ⟨p, hmem⟩ = _
    rw [Category.assoc, hg_π ⟨p, hmem⟩]
    exact gext_spec F hF hI p
  have hsfπ : ∀ m : Subtype Pp,
      biproduct.toSubtype (fun n : (Finset.Icc a b) => grSub F hF n.1) Qp ≫ Sf
          ≫ biproduct.π (Subtype.restrict Pp (fun n : (Finset.Icc a b) => grSub F hF n.1)) m
        = if Qp m.1 then biproduct.π (fun n : (Finset.Icc a b) => grSub F hF n.1) m.1 else 0 := by
    intro m
    apply biproduct.hom_ext'
    intro k
    rw [← Category.assoc, biproduct.ι_toSubtype]
    by_cases hQk : Qp k
    · rw [dite_eq_left hQk, ← Category.assoc, hSf, biproduct.ι_desc]
      have hekm : (e ⟨k, hQk⟩ = m) ↔ ((k : Finset.Icc a b) = m.1) :=
        ⟨fun h => congrArg (fun x : Subtype Pp => (x : Finset.Icc a b)) h, fun h => Subtype.ext h⟩
      by_cases hk : (k : Finset.Icc a b) = m.1
      · have hQm : Qp m.1 := hk ▸ hQk
        rw [ite_eq_left hQm, biproduct.ι_π, biproduct.ι_π, dite_eq_left (hekm.2 hk),
            dite_eq_left hk]
      · rw [biproduct.ι_π_ne _ (fun h => hk (hekm.1 h))]
        by_cases hQm : Qp m.1
        · rw [ite_eq_left hQm, biproduct.ι_π_ne _ hk]
        · rw [ite_eq_right hQm, comp_zero]
    · rw [dite_eq_right hQk, zero_comp]
      by_cases hQm : Qp m.1
      · rw [ite_eq_left hQm, biproduct.ι_π_ne _ (fun h => hQk (by rw [h]; exact hQm))]
      · rw [ite_eq_right hQm, comp_zero]
  have hcomm₁₂ : τ₁ ≫ Sf = j ≫ τ₂ := by
    apply biproduct.hom_ext
    intro m
    rw [hτ₁, hτ₂, hj]
    have hRHS : ((F (p+1)).ofLE (F p) (hF (by omega : p ≤ p+1))
        ≫ ((F p).arrow ≫ g) ≫ biproduct.toSubtype (fun n : (Finset.Icc a b) => grSub F hF n.1) Pp)
          ≫ biproduct.π (Subtype.restrict Pp (fun n : (Finset.Icc a b) => grSub F hF n.1)) m
        = (F (p+1)).arrow ≫ gext F hF hI m.1 := by
      rw [Category.assoc, Category.assoc, biproduct.toSubtype_π, ← Category.assoc,
        ← Category.assoc, Subobject.ofLE_arrow, Category.assoc, hg_π m.1]
    rw [hRHS, Category.assoc, Category.assoc, hsfπ m]
    by_cases hQm : Qp m.1
    · rw [ite_eq_left hQm, Category.assoc, hg_π m.1]
    · rw [ite_eq_right hQm, comp_zero]
      have hPm : Pp m.1 := m.2
      have hm1 : (m.1 : ℤ) = p := by simp only [hQp, hPp] at hQm hPm; omega
      have hvanish : (F (p+1)).arrow ≫ gext F hF hI m.1 = 0 :=
        gext_vanish F hF hI m.1 (p+1) (by omega)
      rw [hvanish]
  have hτ₁iso : IsIso τ₁ := hIH
  exact ShortComplex.isIso₂_of_shortExact_of_isIso₁₃
    (ShortComplex.Hom.mk τ₁ τ₂ (𝟙 (cokernel j)) hcomm₁₂ hcomm₂₃) hS₁exact hS₂exact

/-- Let `F` be a decreasing filtration of `X` by subobjects with `F p = ⊤` for `p` small and
`F p = ⊥` for `p` large. If every graded piece `grSub F hF p` is injective, then there are
integers `a ≤ b`, injective objects `Inj n` and an isomorphism `e : X ≅ ⨁_{a ≤ n ≤ b} Inj n`
carrying each `F p` onto `stdFil a b Inj p`. -/
theorem exists_filtered_iso_of_injective (hI : ∀ p, Injective (grSub F hF p))
    (hex : ∃ a : ℤ, ∀ p ≤ a, F p = ⊤) (hsep : ∃ b : ℤ, ∀ p ≥ b, F p = ⊥) :
    ∃ (a b : ℤ), a ≤ b ∧ ∃ (Inj : ℤ → 𝒜), (∀ n, Injective (Inj n)) ∧
      haveI : HasFiniteBiproducts 𝒜 := HasFiniteBiproducts.of_hasFiniteProducts
      ∃ (e : X ≅ ⨁ (fun n : (Finset.Icc a b) => Inj n.1)),
        ∀ p : ℤ, (Subobject.map e.hom).obj (F p) = stdFil a b Inj p := by
  classical
  have : HasFiniteBiproducts 𝒜 := HasFiniteBiproducts.of_hasFiniteProducts
  obtain ⟨a₀, ha₀⟩ := hex
  obtain ⟨b₀, hb₀⟩ := hsep
  set a : ℤ := a₀ with ha_def
  set b : ℤ := max a₀ (b₀ - 1) with hb_def
  have hab : a ≤ b := le_max_left _ _
  have hFb : ∀ p, b < p → F p = ⊥ := fun p hp => hb₀ p (by simp only [hb_def] at hp ⊢; omega)
  set Inj : ℤ → 𝒜 := fun n => grSub F hF n with hInj_def
  refine ⟨a, b, hab, Inj, hI, ?_⟩
  set M : 𝒜 := ⨁ (fun n : (Finset.Icc a b) => Inj n.1) with hM_def
  set g : X ⟶ M := biproduct.lift (fun n : (Finset.Icc a b) => gext F hF hI n.1) with hg_def
  have hg_π : ∀ (n : Finset.Icc a b), g ≫ biproduct.π _ n = gext F hF hI n.1 :=
    fun _ => biproduct.lift_π _ _
  set P : ℤ → ((Finset.Icc a b) → Prop) := fun p n => p ≤ (n : ℤ) with hP_def
  set φ : ∀ p : ℤ, ((F p : 𝒜)) ⟶ M := fun p => (F p).arrow ≫ g with hφ_def
  have hφ_factor : ∀ p : ℤ, φ p =
      (φ p ≫ biproduct.toSubtype (fun n : (Finset.Icc a b) => Inj n.1) (P p))
        ≫ biproduct.fromSubtype (fun n : (Finset.Icc a b) => Inj n.1) (P p) := by
    intro p
    refine factor_through_fromSubtype (fun n : (Finset.Icc a b) => Inj n.1) (P p) (φ p) ?_
    intro n hn
    have hlt : (n : ℤ) + 1 ≤ p := by simp only [hP_def, not_le] at hn; omega
    change ((F p).arrow ≫ g) ≫ biproduct.π _ n = 0
    rw [Category.assoc, hg_π]
    exact gext_vanish F hF hI n.1 p hlt
  have hbase : ∀ p : ℤ, b < p → IsIso (φ p ≫ biproduct.toSubtype
      (fun n : (Finset.Icc a b) => Inj n.1) (P p)) := by
    intro p hp
    have hSrc : IsZero ((F p : 𝒜)) := by
      rw [hFb p hp]; exact Subobject.botCoeIsoZero.isZero_iff.2 (Limits.isZero_zero _)
    have hTgt : IsZero (⨁ (Subtype.restrict (P p) (fun n : (Finset.Icc a b) => Inj n.1))) := by
      rw [IsZero.iff_id_eq_zero]
      apply biproduct.hom_ext
      rintro ⟨n, hn⟩
      have hnb : (n : ℤ) ≤ b := by have := n.2; simp only [Finset.mem_Icc] at this; omega
      simp only [hP_def] at hn
      omega
    refine ⟨0, hSrc.eq_of_tgt _ _, hTgt.eq_of_tgt _ _⟩
  have hge : ∀ (k : ℕ) (p : ℤ), a ≤ p → (b + 1 - p).toNat = k →
      IsIso (φ p ≫ biproduct.toSubtype (fun n : (Finset.Icc a b) => Inj n.1) (P p)) := by
    intro k
    induction k with
    | zero =>
      intro p _ hk
      have hp : b < p := by
        by_contra hc
        push Not at hc
        have : 0 < (b + 1 - p).toNat := by omega
        omega
      exact hbase p hp
    | succ k ih =>
      intro p hpa hk
      by_cases hpb : p ≤ b
      · have hmem : p ∈ Finset.Icc a b := by simp only [Finset.mem_Icc]; exact ⟨hpa, hpb⟩
        have hIH : IsIso (((F (p+1)).arrow ≫ g) ≫ biproduct.toSubtype
            (fun n : (Finset.Icc a b) => grSub F hF n.1) (fun n => p + 1 ≤ (n:ℤ))) :=
          ih (p+1) (by omega) (by omega)
        exact psi_step F hF hI a b g hg_π p hmem hIH
      · exact hbase p (by omega)
  have hψ_ge : ∀ p : ℤ, a ≤ p → IsIso (φ p ≫ biproduct.toSubtype
      (fun n : (Finset.Icc a b) => Inj n.1) (P p)) :=
    fun p hpa => hge ((b + 1 - p).toNat) p hpa rfl
  have hfull : ∀ p : ℤ, p ≤ a → ∀ n : (Finset.Icc a b), P p n := by
    intro p hpa n
    have := n.2
    simp only [Finset.mem_Icc] at this
    simp only [hP_def]
    omega
  have hg_iso : IsIso g := by
    have := isIso_toSubtype_of_forall (fun n : (Finset.Icc a b) => Inj n.1) (P a) (hfull a le_rfl)
    have : IsIso (F a).arrow := by
      rw [Subobject.isIso_arrow_iff_eq_top]; exact ha₀ a le_rfl
    have hψa := hψ_ge a le_rfl
    rw [hφ_def, Category.assoc] at hψa
    have : IsIso (g ≫ biproduct.toSubtype (fun n : (Finset.Icc a b) => Inj n.1) (P a)) :=
      IsIso.of_isIso_comp_left (F a).arrow _
    exact IsIso.of_isIso_comp_right g
      (biproduct.toSubtype (fun n : (Finset.Icc a b) => Inj n.1) (P a))
  have hψ_iso : ∀ p : ℤ, IsIso (φ p ≫ biproduct.toSubtype
      (fun n : (Finset.Icc a b) => Inj n.1) (P p)) := by
    intro p
    by_cases hpa : a ≤ p
    · exact hψ_ge p hpa
    · have := isIso_toSubtype_of_forall (fun n : (Finset.Icc a b) => Inj n.1) (P p)
        (hfull p (by omega))
      have : IsIso (F p).arrow := by
        rw [Subobject.isIso_arrow_iff_eq_top]; exact ha₀ p (by omega)
      rw [hφ_def, Category.assoc]
      infer_instance
  refine ⟨asIso g, ?_⟩
  intro p
  have := hψ_iso p
  change (Subobject.map (asIso g).hom).obj (F p) = stdFil a b Inj p
  rw [stdFil_eq_mk a b Inj p]
  conv_lhs => rw [← Subobject.mk_arrow (F p)]
  rw [Subobject.map_mk]
  have hMono := mono_fromSubtype (fun n : (Finset.Icc a b) => Inj n.1) (P p)
  refine Subobject.mk_eq_mk_of_comm _ _
    (asIso (φ p ≫ biproduct.toSubtype (fun n : (Finset.Icc a b) => Inj n.1) (P p))) ?_
  change (φ p ≫ biproduct.toSubtype (fun n : (Finset.Icc a b) => Inj n.1) (P p))
      ≫ biproduct.fromSubtype (fun n : (Finset.Icc a b) => Inj n.1) (P p)
      = (F p).arrow ≫ (asIso g).hom
  exact (hφ_factor p).symm

end Decomposition

end

end CategoryTheory.FilteredObject.InjectiveSplitting

end

end

section

@[expose] public section

open CategoryTheory Limits Opposite

namespace CategoryTheory.FilteredObject.InjectiveSplitting

variable {𝒜 : Type*} [Category 𝒜] [Abelian 𝒜]

noncomputable section

/-- An isomorphism `e : A.X ≅ B.X` of the underlying objects of two filtered objects which carries
each step `F^i A` onto `F^i B` is an isomorphism of filtered objects. -/
def isoOfMapEq {A B : FilteredObject 𝒜 ℤᵒᵖ} (e : A.X ≅ B.X)
    (he : ∀ i, (Subobject.map e.hom).obj (A.subobject i) = B.subobject i) : A ≅ B :=
  FilteredObject.isoMk e
    (fun i => Subobject.isoOfMkEqMk (A.filtration.ι.app i ≫ e.hom) (B.filtration.ι.app i)
      (by rw [← Subobject.map_mk]; exact he i))
    (fun i => by rw [Subobject.isoOfMkEqMk_hom, Subobject.ofMkLEMk_comp])

/-- The `p`-th graded piece of a filtered object is the cokernel of the inclusion of subobjects
`F^{p + 1} ⟶ F^p`. -/
def grIsoGrSub (A : FilteredObject 𝒜 ℤᵒᵖ) (p : ℤ) :
    (FilteredObject.gr p).obj A ≅ grSub (fun n => A.subobject (op n)) A.filtration.antitone p :=
  (cokernelOfLEMkIso' (A.filtration.ι.app (op (p + 1))) (A.filtration.ι.app (op p)) _ _ rfl rfl
    (A.filtration.step (FilteredObject.succHom p)) (A.filtration.step_comp_ι_app _) _).symm

end

end CategoryTheory.FilteredObject.InjectiveSplitting

namespace CategoryTheory.FilteredObject

open CategoryTheory.FilteredObject.InjectiveSplitting Opposite

variable {𝒜 : Type*} [Category 𝒜] [Abelian 𝒜]

/-- The filtered object `⨁_{a ≤ n ≤ b} I_n` of `𝒜` whose `p`-th step is the sub-biproduct
`⨁_{n ≥ p} I_n` of the summands of index at least `p`. -/
@[implicit_reducible]
noncomputable def stdBiprod (a b : ℤ) (Inj : ℤ → 𝒜) : FilteredObject 𝒜 ℤᵒᵖ where
  X := haveI : HasFiniteBiproducts 𝒜 := HasFiniteBiproducts.of_hasFiniteProducts
    ⨁ fun n : Finset.Icc a b => Inj n.1
  filtration := Filtration.ofAntitone (stdFil a b Inj) (stdFil_antitone a b Inj)

/-- The `p`-th step of `stdBiprod a b Inj` is the sub-biproduct `⨁_{n ≥ p} I_n`. -/
lemma stdBiprod_subobject (a b : ℤ) (Inj : ℤ → 𝒜) (p : ℤ) :
    (stdBiprod a b Inj).filtration.subobject (op p) = stdFil a b Inj p :=
  Filtration.subobject_ofAntitone (stdFil a b Inj) (stdFil_antitone a b Inj) p

/-- The inclusion of consecutive steps of `stdBiprod a b Inj` is the inclusion of subobjects
`stdFil a b Inj (p + 1) ≤ stdFil a b Inj p`. -/
lemma stdBiprod_step (a b : ℤ) (Inj : ℤ → 𝒜) (p : ℤ) :
    (stdBiprod a b Inj).filtration.step (succHom p) =
      Subobject.ofLE _ _ (stdFil_antitone a b Inj (Int.le_add_one le_rfl)) :=
  rfl

/-- Let `𝒜` be an abelian category. An object `I` of `Fil^f(𝒜)` is filtered injective if and
only if there are integers `a ≤ b`, injective objects `I_n` of `𝒜` and an isomorphism
`I ≅ ⨁_{a ≤ n ≤ b} I_n` of filtered objects, where the right-hand side carries the filtration
`F^p = ⨁_{n ≥ p} I_n` (`FilteredObject.stdBiprod`). The finiteness of the filtration of `I` is
part of both sides, and is not a hypothesis. -/
@[stacks 05TP]
theorem isFilteredInjective_iff_nonempty_iso_stdBiprod (I : FilteredObject 𝒜 ℤᵒᵖ) :
    I.IsFilteredInjective ↔ ∃ a b : ℤ, a ≤ b ∧ ∃ Inj : ℤ → 𝒜, (∀ n, Injective (Inj n)) ∧
      Nonempty (I ≅ stdBiprod a b Inj) := by
  constructor
  · rintro ⟨hfin, hgr⟩
    obtain ⟨n, hn⟩ := hfin.exists_isIso_ι
    obtain ⟨m, hm⟩ := hfin.exists_isZero_obj
    obtain ⟨a, b, hab, Inj, hInj, e, he⟩ := exists_filtered_iso_of_injective
      (fun p => I.subobject (op p)) I.filtration.antitone
      (fun p => Injective.of_iso (grIsoGrSub I p) (hgr p))
      ⟨n, fun p hp => (I.filtration.subobject_eq_top_iff _).2
        (I.filtration.isIso_ι_app_of_le hp hn)⟩
      ⟨m, fun p hp => (I.filtration.subobject_eq_bot_iff _).2
        ⟨(I.filtration.isZero_obj_of_le hp hm).isInitial⟩⟩
    exact ⟨a, b, hab, Inj, hInj, ⟨isoOfMapEq e fun i => (he i.unop).trans
      (stdBiprod_subobject a b Inj i.unop).symm⟩⟩
  · rintro ⟨a, b, hab, Inj, hInj, ⟨e⟩⟩
    refine ⟨?_, fun p => Injective.of_iso ((gr p).mapIso e).symm ?_⟩
    · have : (stdBiprod a b Inj).filtration.IsFinite := by
        rw [Filtration.isFinite_iff_subobject]
        exact ⟨⟨op a, by rw [stdBiprod_subobject, stdFil_eq_top a b Inj le_rfl]⟩,
          ⟨op (b + 1), by rw [stdBiprod_subobject, stdFil_eq_bot a b Inj _ (by omega)]⟩⟩
      exact isFinite_of_iso e.symm
    · exact Injective.of_iso (cokernelIsoOfEq (stdBiprod_step a b Inj p)).symm
        (stdFil_gr_injective a b Inj hInj p)

end CategoryTheory.FilteredObject

end

end
