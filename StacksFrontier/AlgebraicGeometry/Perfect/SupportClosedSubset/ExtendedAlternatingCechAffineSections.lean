module

public import Mathlib.Algebra.Exact.Basic
public import Mathlib.Algebra.Homology.ShortComplex.Ab
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import StacksFrontier.AlgebraicGeometry.Modules.TildeExactness
public import StacksFrontier.AlgebraicGeometry.Perfect.SupportClosedSubset.DerivedSupportInvertsAugmentation
public import StacksFrontier.AlgebraicGeometry.Properties.PrincipalOpens.Sections
public import StacksFrontier.RingTheory.Cech.Extended
public import StacksFrontier.RingTheory.Cech.FlatKoszulVanishing

/-!
# The extended alternating Čech complex on an affine, read on global sections

Let `X` be an affine scheme, let `f₁, …, f_c ∈ Γ(X, 𝒪_X)` and let `F` be a quasi-coherent
`𝒪_X`-module.  The extended alternating Čech complex `𝓕^•` of [Stacks, Tag 0G7I] is a complex of
`𝒪_X`-modules whose degree-`0` term is `F` and whose degree-`p + 1` term is the product, over the
strictly increasing `(p + 1)`-tuples `i₀ < ⋯ < i_p`, of the direct images of the restrictions of
`F` to the principal intersections `U_{i₀…i_p}`.  Its complex of global sections is the
*algebraic* extended alternating Čech complex `Cech.cechComplex f Γ(F, ⊤)` of
`StacksFrontier/RingTheory/Cech/Substrate.lean`: on an affine, `Γ(F, X.basicOpen g)` is the
localization of `Γ(F, ⊤)` at the powers of `g`, and `U_{i₀…i_p}` is the principal open of the
product `f_{i₀} ⋯ f_{i_p}`.

This file proves that identification and reads off the consequence this library needs: on an
affine, if the equations are a Koszul-regular sequence and the module of global sections of `F`
is flat, then `𝓕^•` is exact in every degree other than `c`.  Above `c` this is already known
and for a different reason — the index type of the product is empty there
(`Stacks.Perfect.CechSupportRepresentation.exactAt_of_lt`); *below* `c` it is the content of the
ring-theoretic Stacks 0G6L for flat coefficients, which is
`Cech.cechComplex_homology_isZero_of_isKoszulRegular_of_flat`.

## Main results

* `Stacks.Perfect.CechAffineSections.extendedAlternatingCech_exactAt_of_isKoszulRegular_of_flat`:
  on an affine scheme, for a Koszul-regular sequence of equations and a quasi-coherent module
  with flat global sections, the extended alternating Čech complex is exact in every degree
  other than the length of the sequence.

Everything else here is private: the identification of the two complexes, `cechSectionsComplexIso`,
and the auxiliary facts it is read through — that on an affine a short complex of quasi-coherent
modules is exact as soon as its global sections are (`exact_of_sections`), and that the terms of
the extended alternating Čech complex of a quasi-coherent module are quasi-coherent
(`isQuasicoherent_cechTerm`, through `isQuasicoherent_product`).

## Implementation notes

The two complexes are indexed by the same `ℕ` but their terms are described by different index
types: the sheaf-level complex is a product over the strictly increasing tuples
`CechCochains.OrdIndex (Fin c) p`, the algebraic one a direct sum over the subsets of `Fin c` of
a given cardinality.  `orderedIndexEquivFinset` is the comparison — a tuple goes to its image —
and `cechSign_image_univ` is the corresponding comparison of signs: the Čech sign of omitting
`i_j` from the image of a tuple is `(-1) ^ j`, because the number of elements of the image below
`i_j` is `j`.  With those two the degreewise comparison is assembled from the localization
statement `AlgebraicGeometry.isLocalizedModule_restriction_basicOpen_of_qcqs`, and its
compatibility with the differentials is checked componentwise against `cechD_component`, the
formula for a component of the algebraic differential as a signed sum over the elements of the
target index.

Passing from exactness of the sections to exactness of the complex of modules is
`exact_of_sections`: it reduces along `X.isoSpec` to `Spec Γ(X, ⊤)` and there inverts
`Scheme.Modules.fromTildeΓ`,
available because the terms are quasi-coherent; so `isQuasicoherent_cechTerm` is needed, and for
that the quasi-coherence of a finite product, which is `isQuasicoherent_product`.

## References

* [Stacks Project, Tag 0G7I](https://stacks.math.columbia.edu/tag/0G7I)
* [Stacks Project, Tag 0G6L](https://stacks.math.columbia.edu/tag/0G6L)
* [Stacks Project, Tag 01HV](https://stacks.math.columbia.edu/tag/01HV)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.Perfect.ExtendedAlternatingCech (extendedAlternatingCech restrictedModule)
open Stacks.Perfect.CechDerivedSupport (equationsOpen_eq_basicOpen_prod)
open scoped AlgebraicGeometry

universe u

namespace Stacks.Perfect.CechAffineSections

/-! ### Comparing the two index types -/

/-- A strictly increasing `(p + 1)`-tuple in `Fin c` is the same thing as a subset of `Fin c`
with `p + 1` elements: send the tuple to its image. -/
private def orderedIndexEquivFinset (c p : ℕ) :
    CechCochains.OrdIndex (I := Fin c) p ≃ {s : Finset (Fin c) // s.card = p + 1} where
  toFun s := ⟨Finset.image s.1 Finset.univ, by
    rw [Finset.card_image_of_injective _ s.2.injective]
    simp⟩
  invFun t := ⟨Finset.orderEmbOfFin t.1 t.2, (Finset.orderEmbOfFin t.1 t.2).strictMono⟩
  left_inv s := Subtype.ext (Finset.orderEmbOfFin_unique
    (by rw [Finset.card_image_of_injective _ s.2.injective]; simp)
    (fun i => Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩) s.2).symm
  right_inv t := Subtype.ext (Finset.image_orderEmbOfFin_univ t.1 t.2)

/-- Omitting the `j`-th entry of an injective tuple erases its value from the image. -/
private theorem image_univ_comp_succAbove {c n : ℕ}
    (s : Fin (n + 1) → Fin c) (hs : Function.Injective s) (j : Fin (n + 1)) :
    Finset.image (s ∘ j.succAbove) Finset.univ =
      (Finset.image s Finset.univ).erase (s j) := by
  ext a
  simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_erase]
  constructor
  · rintro ⟨k, rfl⟩
    exact ⟨fun h => Fin.succAbove_ne j k (hs h), ⟨j.succAbove k, rfl⟩⟩
  · rintro ⟨hne, k, rfl⟩
    obtain ⟨l, rfl⟩ := Fin.exists_succAbove_eq (show k ≠ j from fun h => hne (congrArg s h))
    exact ⟨l, rfl⟩

/-- The Čech sign of removing `s j` from the image of a strictly increasing tuple `s` is
`(-1) ^ j`: the elements of the image below `s j` are exactly the `s k` with `k < j`. -/
private theorem cechSign_image_univ {c n : ℕ}
    (s : Fin n → Fin c) (hs : StrictMono s) (j : Fin n) :
    Cech.cechSign (Finset.image s Finset.univ) (s j) = (-1 : ℤ) ^ (j : ℕ) := by
  unfold Cech.cechSign
  have he : (Finset.image s Finset.univ).filter (· < s j) =
      Finset.image s (Finset.univ.filter (· < j)) := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨⟨k, rfl⟩, hk⟩
      exact ⟨k, hs.lt_iff_lt.mp hk, rfl⟩
    · rintro ⟨k, hk, rfl⟩
      exact ⟨⟨k, rfl⟩, hs hk⟩
  rw [he, Finset.card_image_of_injective _ hs.injective]
  congr 1
  convert Fin.card_Iio j using 2
  ext k
  simp

/-- The principal intersection of a tuple is the principal open of the product of the equations
indexed by its image. -/
private theorem equationsOpen_eq_basicOpen_finsetProd
    {X : Scheme.{u}} {c p : ℕ} (f : Fin c → Γ(X, ⊤))
    (s : CechCochains.OrdIndex (I := Fin c) p) :
    Stacks.Perfect.ExtendedAlternatingCech.equationsOpen f p s =
      X.basicOpen (∏ i ∈ (orderedIndexEquivFinset c p s).1, f i) := by
  rw [equationsOpen_eq_basicOpen_prod]
  change X.basicOpen (∏ k, f (s.1 k)) =
    X.basicOpen (∏ i ∈ Finset.image s.1 Finset.univ, f i)
  rw [Finset.prod_image fun _ _ _ _ hab => s.2.injective hab]

/-! ### The summands of the algebraic complex are the sections on the principal opens -/

/-- On an affine, the sections of a quasi-coherent module over the principal open of
`g = ∏_{i ∈ s} f i` are the localization of its global sections at the powers of `g`, which is
the summand of the algebraic extended alternating Čech complex indexed by `s`. -/
private def cechModSectionsEquiv {X : Scheme.{u}} [IsAffine X] {c : ℕ} (f : Fin c → Γ(X, ⊤))
    (F : X.Modules) [F.IsQuasicoherent] (s : Finset (Fin c)) :
    let g := ∏ i ∈ s, f i
    letI : Module Γ(X, ⊤) Γ(F, X.basicOpen g) :=
      Module.compHom Γ(F, X.basicOpen g)
        (X.presheaf.map (homOfLE (X.basicOpen_le g)).op).hom
    Cech.cechMod f Γ(F, ⊤) s ≃ₗ[Γ(X, ⊤)] Γ(F, X.basicOpen g) := by
  let g := ∏ i ∈ s, f i
  letI : Module Γ(X, ⊤) Γ(F, X.basicOpen g) :=
    Module.compHom Γ(F, X.basicOpen g)
      (X.presheaf.map (homOfLE (X.basicOpen_le g)).op).hom
  change Cech.cechMod f Γ(F, ⊤) s ≃ₗ[Γ(X, ⊤)] Γ(F, X.basicOpen g)
  have hloc : IsLocalizedModule.Away g
      (Scheme.Modules.restrictionLinearMap F (homOfLE (X.basicOpen_le g))) :=
    AlgebraicGeometry.isLocalizedModule_restriction_basicOpen_of_qcqs F
      (isAffineOpen_top X).isCompact (isAffineOpen_top X).isQuasiSeparated g
  exact IsLocalizedModule.linearEquiv (Submonoid.powers g)
    (LocalizedModule.mkLinearMap (Submonoid.powers g) Γ(F, ⊤))
    (Scheme.Modules.restrictionLinearMap F (homOfLE (X.basicOpen_le g)))

/-- `cechModSectionsEquiv` sends `m / 1` to the restriction of `m`. -/
private theorem cechModSectionsEquiv_mk {X : Scheme.{u}} [IsAffine X] {c : ℕ}
    (f : Fin c → Γ(X, ⊤)) (F : X.Modules) [F.IsQuasicoherent] (s : Finset (Fin c))
    (m : Γ(F, ⊤)) :
    (cechModSectionsEquiv f F s)
      (LocalizedModule.mkLinearMap (Cech.cechSub f s) Γ(F, ⊤) m) =
      F.presheaf.map (homOfLE (X.basicOpen_le (∏ i ∈ s, f i))).op m := by
  let g := ∏ i ∈ s, f i
  let : Module Γ(X, ⊤) Γ(F, X.basicOpen g) :=
    Module.compHom Γ(F, X.basicOpen g)
      (X.presheaf.map (homOfLE (X.basicOpen_le g)).op).hom
  let : IsLocalizedModule.Away g
      (Scheme.Modules.restrictionLinearMap F (homOfLE (X.basicOpen_le g))) :=
    AlgebraicGeometry.isLocalizedModule_restriction_basicOpen_of_qcqs F
      (isAffineOpen_top X).isCompact (isAffineOpen_top X).isQuasiSeparated g
  exact IsLocalizedModule.linearEquiv_apply (Submonoid.powers g)
    (LocalizedModule.mkLinearMap (Submonoid.powers g) Γ(F, ⊤))
    (Scheme.Modules.restrictionLinearMap F (homOfLE (X.basicOpen_le g))) m

/-! ### A component of the algebraic differential -/

/-- Transport of a transition map of the algebraic complex along an equality of target
indices. -/
private theorem cechι_cast_target {R : Type u} [CommRing R] {r p : ℕ}
    (f : Fin r → R) (M : Type u) [AddCommGroup M] [Module R M]
    {S : Finset (Fin r)} {T T' : _root_.ExtendedAlternatingCech.Idx r p}
    (h : T = T') (h₁ : S ⊆ T.1) (h₂ : S ⊆ T'.1) (x : Cech.cechMod f M S) :
    h ▸ Cech.cechι f M h₁ x = Cech.cechι f M h₂ x := by
  subst h
  rfl

/-- The component of the algebraic Čech differential at a target index `T` is the signed sum,
over the elements `k` of `T`, of the transition maps from `T \ {k}`. -/
private theorem cechD_component {R : Type u} [CommRing R] {r p : ℕ}
    (f : Fin r → R) (M : Type u) [AddCommGroup M] [Module R M]
    (x : Cech.cechTerm f M p) (T : _root_.ExtendedAlternatingCech.Idx r (p + 1)) :
    Cech.cechD f M p x T =
      ∑ k : T.1, Cech.cechSign T.1 k •
        Cech.cechι f M (show (T.erase k).1 ⊆ T.1 from Finset.erase_subset _ _)
          (x (T.erase k)) := by
  classical
  induction x using DirectSum.induction_on with
  | zero => simp only [map_zero, DirectSum.zero_apply, zsmul_zero, Finset.sum_const_zero]
  | add x y hx hy => simp only [map_add, DirectSum.add_apply, hx, hy, zsmul_add,
      Finset.sum_add_distrib]
  | of S m =>
    change Cech.cechD f M p (DirectSum.lof R _ _ S m) T = _
    rw [Cech.cechD_lof]
    simp only [DirectSum.sum_apply, DirectSum.smul_apply,
      DirectSum.lof_eq_of, DirectSum.of_apply]
    by_cases h : ∃ k : T.1, S = T.erase k
    · obtain ⟨k, rfl⟩ := h
      let k' : ↥((T.erase k).1ᶜ) := ⟨k, by simp⟩
      have hI : (⟨insert (k' : Fin r) (T.erase k).1, by
          rw [Finset.card_insert_of_notMem (Finset.mem_compl.mp k'.2), (T.erase k).2]⟩ :
          _root_.ExtendedAlternatingCech.Idx r (p + 1)) = T :=
        Subtype.ext (Finset.insert_erase k.2)
      have hE (l : T.1) (hne : l ≠ k) : T.erase k ≠ T.erase l := by
        intro he
        have hl : (l : Fin r) ∈ (T.erase k).1 := by
          simp only [_root_.ExtendedAlternatingCech.Idx.val_erase, Finset.mem_erase]
          exact ⟨fun h => hne (Subtype.ext h), l.2⟩
        rw [he] at hl
        simp at hl
      have hI' (l : ↥((T.erase k).1ᶜ)) (hne : l ≠ k') :
          (⟨insert (l : Fin r) (T.erase k).1, by
            rw [Finset.card_insert_of_notMem (Finset.mem_compl.mp l.2), (T.erase k).2]⟩ :
            _root_.ExtendedAlternatingCech.Idx r (p + 1)) ≠ T := by
        intro he
        have hk : (k : Fin r) ∈ insert (l : Fin r) (T.erase k).1 := by
          rw [show insert (l : Fin r) (T.erase k).1 = T.1 from congrArg Subtype.val he]
          exact k.2
        simp only [_root_.ExtendedAlternatingCech.Idx.val_erase, Finset.mem_insert,
          Finset.notMem_erase, or_false] at hk
        exact hne (Subtype.ext hk.symm)
      rw [Finset.sum_eq_single k', Finset.sum_eq_single k]
      · rw [dite_eq_left hI, dite_eq_left rfl,
          cechι_cast_target f M hI _ (show (T.erase k).1 ⊆ T.1 from Finset.erase_subset _ _)]
        change Cech.cechSign (T.1.erase k) k • _ = _
        rw [Cech.cechSign_erase]
      · intro l _ hl
        simp only [hE l hl, dite_false, map_zero, zsmul_zero]
      · simp
      · intro l _ hl
        simp only [hI' l hl, dite_false, zsmul_zero]
      · intro hk'
        exact absurd (Finset.mem_attach _ k') hk'
    · have hE (k : T.1) : S ≠ T.erase k := fun he => h ⟨k, he⟩
      have hI (k : ↥(S.1ᶜ)) :
          (⟨insert (k : Fin r) S.1, by
            rw [Finset.card_insert_of_notMem (Finset.mem_compl.mp k.2), S.2]⟩ :
            _root_.ExtendedAlternatingCech.Idx r (p + 1)) ≠ T := by
        intro he
        have hk : (k : Fin r) ∈ T.1 := by
          rw [← congrArg Subtype.val he]
          exact Finset.mem_insert_self _ _
        refine h ⟨⟨k, hk⟩, Subtype.ext ?_⟩
        change S.1 = T.1.erase k
        rw [← congrArg Subtype.val he]
        exact (Finset.erase_insert (Finset.mem_compl.mp k.2)).symm
      simp only [hI, hE, dite_false, map_zero, zsmul_zero, Finset.sum_const_zero]

/-! ### Naturality of the comparison of summands -/

/-- Restriction of module sections, as a map linear over the global functions. -/
private def globalRestrictionLinearMap {X : Scheme.{u}} (F : X.Modules)
    {U V : X.Opens} (h : V ≤ U) :
    letI : Module Γ(X, ⊤) Γ(F, U) :=
      Module.compHom Γ(F, U) (X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op).hom
    letI : Module Γ(X, ⊤) Γ(F, V) :=
      Module.compHom Γ(F, V) (X.presheaf.map (homOfLE (show V ≤ ⊤ from le_top)).op).hom
    Γ(F, U) →ₗ[Γ(X, ⊤)] Γ(F, V) := by
  letI : Module Γ(X, ⊤) Γ(F, U) :=
    Module.compHom Γ(F, U) (X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op).hom
  letI : Module Γ(X, ⊤) Γ(F, V) :=
    Module.compHom Γ(F, V) (X.presheaf.map (homOfLE (show V ≤ ⊤ from le_top)).op).hom
  refine { toFun := F.presheaf.map (homOfLE h).op
           map_add' := map_add _
           map_smul' := ?_ }
  intro a m
  change F.presheaf.map (homOfLE h).op
      ((X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op a) • m) =
    (X.presheaf.map (homOfLE (show V ≤ ⊤ from le_top)).op a) • F.presheaf.map (homOfLE h).op m
  rw [F.map_smul]
  congr 1
  exact (ConcreteCategory.congr_hom (X.presheaf.map_comp
    (homOfLE (show U ≤ ⊤ from le_top)).op (homOfLE h).op) a).symm

/-- The principal opens of the products of the equations are antitone in the index set. -/
private theorem basicOpen_prod_antitone {X : Scheme.{u}} {c : ℕ}
    (f : Fin c → Γ(X, ⊤)) {s t : Finset (Fin c)} (h : s ⊆ t) :
    X.basicOpen (∏ j ∈ t, f j) ≤ X.basicOpen (∏ j ∈ s, f j) := by
  obtain ⟨a, ha⟩ := Finset.prod_dvd_prod_of_subset s t f h
  rw [ha, Scheme.basicOpen_mul]
  exact inf_le_left

/-- The comparison of summands carries the transition maps of the algebraic complex to the
restriction maps of `F`. -/
private theorem cechModSectionsEquiv_naturality {X : Scheme.{u}} [IsAffine X] {c : ℕ}
    (f : Fin c → Γ(X, ⊤)) (F : X.Modules) [F.IsQuasicoherent] {s t : Finset (Fin c)}
    (h : s ⊆ t) (x : Cech.cechMod f Γ(F, ⊤) s) :
    cechModSectionsEquiv f F t (Cech.cechι f Γ(F, ⊤) h x) =
      F.presheaf.map (homOfLE (basicOpen_prod_antitone f h)).op
        (cechModSectionsEquiv f F s x) := by
  let : Module Γ(X, ⊤) Γ(F, X.basicOpen (∏ j ∈ s, f j)) :=
    Module.compHom _ (X.presheaf.map (homOfLE (X.basicOpen_le (∏ j ∈ s, f j))).op).hom
  let : Module Γ(X, ⊤) Γ(F, X.basicOpen (∏ j ∈ t, f j)) :=
    Module.compHom _ (X.presheaf.map (homOfLE (X.basicOpen_le (∏ j ∈ t, f j))).op).hom
  let eS := cechModSectionsEquiv f F s
  let eT := cechModSectionsEquiv f F t
  let ρ := globalRestrictionLinearMap F (basicOpen_prod_antitone f h)
  have he : Cech.cechι f Γ(F, ⊤) h =
      eT.symm.toLinearMap.comp (ρ.comp eS.toLinearMap) := by
    apply IsLocalizedModule.ext (Cech.cechSub f s)
      (LocalizedModule.mkLinearMap (Cech.cechSub f s) Γ(F, ⊤))
      (Cech.isUnit_algebraMap f Γ(F, ⊤) h
        (LocalizedModule.mkLinearMap (Cech.cechSub f t) Γ(F, ⊤)))
    ext m
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, Cech.cechι_mk]
    apply eT.injective
    simp only [LinearEquiv.apply_symm_apply]
    change cechModSectionsEquiv f F t _ =
      F.presheaf.map (homOfLE (basicOpen_prod_antitone f h)).op
        (cechModSectionsEquiv f F s _)
    rw [cechModSectionsEquiv_mk, cechModSectionsEquiv_mk]
    exact ConcreteCategory.congr_hom (F.presheaf.map_comp
      (homOfLE (X.basicOpen_le (∏ j ∈ s, f j))).op
      (homOfLE (basicOpen_prod_antitone f h)).op) m
  change eT (Cech.cechι f Γ(F, ⊤) h x) = ρ (eS x)
  rw [LinearMap.congr_fun he x]
  exact eT.apply_symm_apply _

/-! ### The degreewise comparison -/

/-- The summand of the algebraic complex indexed by the image of a tuple `s` is the group of
sections of `F` over the principal intersection belonging to `s`. -/
private def cechOrderedSectionsEquiv {X : Scheme.{u}} [IsAffine X] {c p : ℕ}
    (f : Fin c → Γ(X, ⊤)) (F : X.Modules) [F.IsQuasicoherent]
    (s : CechCochains.OrdIndex (I := Fin c) p) :
    Cech.cechMod f Γ(F, ⊤) (orderedIndexEquivFinset c p s).1 ≃+
      Γ(F, CechCochains.inter (fun i => (⊤ : X.Opens) ⊓ X.basicOpen (f i)) s.1) := by
  have h : CechCochains.inter (fun i => (⊤ : X.Opens) ⊓ X.basicOpen (f i)) s.1 =
      X.basicOpen (∏ i ∈ (orderedIndexEquivFinset c p s).1, f i) := by
    simpa only [CechCochains.inter, top_inf_eq,
      Stacks.Perfect.ExtendedAlternatingCech.equationsOpen] using
      equationsOpen_eq_basicOpen_finsetProd f s
  letI : Module Γ(X, ⊤) Γ(F, X.basicOpen (∏ i ∈ (orderedIndexEquivFinset c p s).1, f i)) :=
    Module.compHom _ (X.presheaf.map
      (homOfLE (X.basicOpen_le (∏ i ∈ (orderedIndexEquivFinset c p s).1, f i))).op).hom
  exact (cechModSectionsEquiv f F (orderedIndexEquivFinset c p s).1).toAddEquiv.trans
    (F.presheaf.mapIso (eqToIso h).op).addCommGroupIsoToAddEquiv

/-- The degree-`(p + 1)` term of the algebraic complex is the group of global sections of the
degree-`(p + 1)` term of the sheaf-level complex. -/
private def cechTermSectionsEquiv {X : Scheme.{u}} [IsAffine X] {c : ℕ} (f : Fin c → Γ(X, ⊤))
    (F : X.Modules) [F.IsQuasicoherent] (p : ℕ) :
    Cech.cechTerm f Γ(F, ⊤) (p + 1) ≃+
      Γ((extendedAlternatingCech f F).complex.X (p + 1), ⊤) := by
  let e₁ : Cech.cechTerm f Γ(F, ⊤) (p + 1) ≃ₗ[Γ(X, ⊤)]
      ((s : {s : Finset (Fin c) // s.card = p + 1}) → Cech.cechMod f Γ(F, ⊤) s.1) :=
    DFinsupp.linearEquivFunOnFintype
  let e₂ := LinearEquiv.piCongrLeft Γ(X, ⊤)
    (fun s : {s : Finset (Fin c) // s.card = p + 1} => Cech.cechMod f Γ(F, ⊤) s.1)
    (orderedIndexEquivFinset c p)
  let e₃ := AddEquiv.piCongrRight (cechOrderedSectionsEquiv f F (p := p))
  exact e₁.toAddEquiv.trans (e₂.symm.toAddEquiv.trans
    (e₃.trans ((extendedAlternatingCech f F).sectionsIso p ⊤).symm))

/-- The components of `cechTermSectionsEquiv`, read through the sectionwise identification of the
sheaf-level complex. -/
private theorem cechTermSectionsEquiv_apply {X : Scheme.{u}} [IsAffine X] {c p : ℕ}
    (f : Fin c → Γ(X, ⊤)) (F : X.Modules) [F.IsQuasicoherent]
    (x : Cech.cechTerm f Γ(F, ⊤) (p + 1)) (s : CechCochains.OrdIndex (I := Fin c) p) :
    (extendedAlternatingCech f F).sectionsIso p ⊤ (cechTermSectionsEquiv f F p x) s =
      cechOrderedSectionsEquiv f F s (x (orderedIndexEquivFinset c p s)) := by
  change (extendedAlternatingCech f F).sectionsIso p ⊤
      (((extendedAlternatingCech f F).sectionsIso p ⊤).symm
        (fun s => cechOrderedSectionsEquiv f F s (x (orderedIndexEquivFinset c p s)))) s = _
  exact congrArg (fun z : CechCochains.OrdCochain
      (fun i => (⊤ : X.Opens) ⊓ X.basicOpen (f i)) (Scheme.Modules.presheaf F) p => z s)
    (((extendedAlternatingCech f F).sectionsIso p ⊤).apply_symm_apply _)

/-- The entries of a strictly increasing tuple enumerate its image. -/
private def orderedElementEquiv {c p : ℕ} (s : CechCochains.OrdIndex (I := Fin c) p) :
    Fin (p + 1) ≃ (orderedIndexEquivFinset c p s).1 :=
  Equiv.ofBijective (fun j => ⟨s.1 j, Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩⟩)
    ⟨fun _ _ h => s.2.injective (congrArg Subtype.val h), by
      rintro ⟨a, ha⟩
      obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp ha
      exact ⟨j, rfl⟩⟩

/-- Omitting an entry of a tuple erases the corresponding element of its image. -/
private theorem orderedIndexEquivFinset_omit {c p : ℕ}
    (s : CechCochains.OrdIndex (I := Fin c) (p + 1)) (j : Fin (p + 2)) :
    orderedIndexEquivFinset c p ⟨s.1 ∘ j.succAbove, CechCochains.strictMono_omit s.2 j⟩ =
      _root_.ExtendedAlternatingCech.Idx.erase (orderedIndexEquivFinset c (p + 1) s)
        (orderedElementEquiv s j) :=
  Subtype.ext (image_univ_comp_succAbove s.1 s.2.injective j)

/-- The degreewise comparison carries a transition map of the algebraic complex to a restriction
map of `F`. -/
private theorem cechOrderedSectionsEquiv_naturality {X : Scheme.{u}} [IsAffine X] {c p q : ℕ}
    (f : Fin c → Γ(X, ⊤)) (F : X.Modules) [F.IsQuasicoherent]
    (s : CechCochains.OrdIndex (I := Fin c) p) (t : CechCochains.OrdIndex (I := Fin c) q)
    (h : (orderedIndexEquivFinset c p s).1 ⊆ (orderedIndexEquivFinset c q t).1)
    (hU : CechCochains.inter (fun i => (⊤ : X.Opens) ⊓ X.basicOpen (f i)) t.1 ≤
      CechCochains.inter (fun i => (⊤ : X.Opens) ⊓ X.basicOpen (f i)) s.1)
    (x : Cech.cechMod f Γ(F, ⊤) (orderedIndexEquivFinset c p s).1) :
    cechOrderedSectionsEquiv f F t (Cech.cechι f Γ(F, ⊤) h x) =
      F.presheaf.map (homOfLE hU).op (cechOrderedSectionsEquiv f F s x) := by
  change F.presheaf.map _
      (cechModSectionsEquiv f F _ (Cech.cechι f Γ(F, ⊤) h x)) =
    F.presheaf.map (homOfLE hU).op
      (F.presheaf.map _ (cechModSectionsEquiv f F _ x))
  rw [cechModSectionsEquiv_naturality]
  simp only [← F.presheaf.map_comp_apply]
  rfl

/-- The degreewise comparison commutes with the differentials in positive degrees. -/
private theorem cechTermSectionsEquiv_comm_d {X : Scheme.{u}} [IsAffine X] {c : ℕ}
    (f : Fin c → Γ(X, ⊤)) (F : X.Modules) [F.IsQuasicoherent] (p : ℕ)
    (x : Cech.cechTerm f Γ(F, ⊤) (p + 1)) :
    cechTermSectionsEquiv f F (p + 1) (Cech.cechD f Γ(F, ⊤) (p + 1) x) =
      ((extendedAlternatingCech f F).complex.d (p + 1) (p + 2)).app ⊤
        (cechTermSectionsEquiv f F p x) := by
  apply ((extendedAlternatingCech f F).sectionsIso (p + 1) ⊤).injective
  funext s
  rw [cechTermSectionsEquiv_apply, (extendedAlternatingCech f F).differential_succ]
  change cechOrderedSectionsEquiv f F s
      (Cech.cechD f Γ(F, ⊤) (p + 1) x (orderedIndexEquivFinset c (p + 1) s)) =
    ∑ j : Fin (p + 2), (-1 : ℤ) ^ (j : ℕ) •
      F.presheaf.map (homOfLE (CechCochains.inter_le_omit _ s.1 j)).op
        ((extendedAlternatingCech f F).sectionsIso p ⊤ (cechTermSectionsEquiv f F p x)
          ⟨s.1 ∘ j.succAbove, CechCochains.strictMono_omit s.2 j⟩)
  simp only [cechTermSectionsEquiv_apply]
  rw [cechD_component, map_sum, ← (orderedElementEquiv s).sum_comp]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_zsmul]
  change Cech.cechSign (Finset.image s.1 Finset.univ) (s.1 j) • _ = _
  rw [cechSign_image_univ s.1 s.2 j]
  congr 1
  let t : CechCochains.OrdIndex (I := Fin c) p :=
    ⟨s.1 ∘ j.succAbove, CechCochains.strictMono_omit s.2 j⟩
  have ht := orderedIndexEquivFinset_omit s j
  have hsub : (orderedIndexEquivFinset c p t).1 ⊆
      (orderedIndexEquivFinset c (p + 1) s).1 := by
    rw [ht]
    exact Finset.erase_subset _ _
  rw [← _root_.ExtendedAlternatingCech.cechι_apply_congr f Γ(F, ⊤) (fun V => x V) ht
    (hsub := hsub)]
  exact cechOrderedSectionsEquiv_naturality f F t s hsub
    (CechCochains.inter_le_omit _ s.1 j) _

/-! ### Degree zero -/

/-- The degree-`0` term of the algebraic complex is the group of global sections of `F`, which is
the degree-`0` term of the sheaf-level complex. -/
private def cechZeroSectionsEquiv {X : Scheme.{u}} [IsAffine X] {c : ℕ} (f : Fin c → Γ(X, ⊤))
    (F : X.Modules) [F.IsQuasicoherent] :
    Cech.cechTerm f Γ(F, ⊤) 0 ≃+ Γ((extendedAlternatingCech f F).complex.X 0, ⊤) :=
  ((DFinsupp.linearEquivFunOnFintype (R := Γ(X, ⊤))).toAddEquiv.trans
    (_root_.ExtendedAlternatingCech.cechZeroEquiv f Γ(F, ⊤)).toAddEquiv).trans
    (((Scheme.Modules.toPresheaf X) ⋙
      (CategoryTheory.evaluation _ _).obj (Opposite.op (⊤ : X.Opens))).mapIso
        (extendedAlternatingCech f F).zeroIso.symm).addCommGroupIsoToAddEquiv

/-- The inverse of the degree-`0` comparison sends a section to the constant tuple `m / 1`. -/
private theorem cechZeroSectionsEquiv_symm_apply {X : Scheme.{u}} [IsAffine X] {c : ℕ}
    (f : Fin c → Γ(X, ⊤)) (F : X.Modules) [F.IsQuasicoherent]
    (x : Γ((extendedAlternatingCech f F).complex.X 0, ⊤))
    (s : _root_.ExtendedAlternatingCech.Idx c 0) :
    (cechZeroSectionsEquiv f F).symm x s =
      LocalizedModule.mk ((extendedAlternatingCech f F).zeroIso.hom.app ⊤ x) 1 := by
  change ((_root_.ExtendedAlternatingCech.cechZeroEquiv f Γ(F, ⊤)).symm _) s = _
  rw [_root_.ExtendedAlternatingCech.cechZeroEquiv_symm_apply]
  rfl

/-- The degreewise comparison on a constant tuple `m / 1` is the restriction of `m`. -/
private theorem cechOrderedSectionsEquiv_mk {X : Scheme.{u}} [IsAffine X] {c p : ℕ}
    (f : Fin c → Γ(X, ⊤)) (F : X.Modules) [F.IsQuasicoherent]
    (s : CechCochains.OrdIndex (I := Fin c) p) (m : Γ(F, ⊤)) :
    cechOrderedSectionsEquiv f F s (LocalizedModule.mk m 1) =
      F.presheaf.map (homOfLE (show CechCochains.inter
        (fun i => (⊤ : X.Opens) ⊓ X.basicOpen (f i)) s.1 ≤ ⊤ from le_top)).op m := by
  change F.presheaf.map _ (cechModSectionsEquiv f F _ _) = _
  rw [show (LocalizedModule.mk m 1 : Cech.cechMod f Γ(F, ⊤) _) =
    LocalizedModule.mkLinearMap _ _ m from rfl, cechModSectionsEquiv_mk,
    ← F.presheaf.map_comp_apply]
  rfl

/-- The comparison commutes with the augmentation, the differential out of degree `0`. -/
private theorem cechZeroSectionsEquiv_comm_d {X : Scheme.{u}} [IsAffine X] {c : ℕ}
    (f : Fin c → Γ(X, ⊤)) (F : X.Modules) [F.IsQuasicoherent]
    (x : Cech.cechTerm f Γ(F, ⊤) 0) :
    cechTermSectionsEquiv f F 0 (Cech.cechD f Γ(F, ⊤) 0 x) =
      ((extendedAlternatingCech f F).complex.d 0 1).app ⊤ (cechZeroSectionsEquiv f F x) := by
  obtain ⟨y, rfl⟩ := (cechZeroSectionsEquiv f F).symm.surjective x
  rw [AddEquiv.apply_symm_apply]
  apply ((extendedAlternatingCech f F).sectionsIso 0 ⊤).injective
  funext s
  rw [cechTermSectionsEquiv_apply, (extendedAlternatingCech f F).differential_zero,
    cechD_component]
  simp only [cechZeroSectionsEquiv_symm_apply]
  rw [← (orderedElementEquiv s).sum_comp, Fin.sum_univ_one]
  change cechOrderedSectionsEquiv f F s
    (Cech.cechSign (Finset.image s.1 Finset.univ) (s.1 0) • _) = _
  rw [cechSign_image_univ s.1 s.2 0]
  simp only [Fin.val_zero, pow_zero, one_zsmul]
  change cechOrderedSectionsEquiv f F s
    (Cech.cechι f Γ(F, ⊤) _ (LocalizedModule.mkLinearMap _ _ _)) = _
  rw [Cech.cechι_mk]
  exact cechOrderedSectionsEquiv_mk f F s _

/-! ### The comparison of complexes -/

/-- The degreewise comparison, in every degree at once. -/
private def cechAllSectionsEquiv {X : Scheme.{u}} [IsAffine X] {c : ℕ} (f : Fin c → Γ(X, ⊤))
    (F : X.Modules) [F.IsQuasicoherent] (p : ℕ) :
    Cech.cechTerm f Γ(F, ⊤) p ≃+ Γ((extendedAlternatingCech f F).complex.X p, ⊤) :=
  match p with
  | 0 => cechZeroSectionsEquiv f F
  | p + 1 => cechTermSectionsEquiv f F p

/-- The degreewise comparison commutes with every differential. -/
private theorem cechAllSectionsEquiv_comm_d {X : Scheme.{u}} [IsAffine X] {c : ℕ}
    (f : Fin c → Γ(X, ⊤)) (F : X.Modules) [F.IsQuasicoherent] (p : ℕ)
    (x : Cech.cechTerm f Γ(F, ⊤) p) :
    cechAllSectionsEquiv f F (p + 1) (Cech.cechD f Γ(F, ⊤) p x) =
      ((extendedAlternatingCech f F).complex.d p (p + 1)).app ⊤
        (cechAllSectionsEquiv f F p x) := by
  cases p with
  | zero => exact cechZeroSectionsEquiv_comm_d f F x
  | succ p => exact cechTermSectionsEquiv_comm_d f F p x

/-! ### Exactness read on global sections -/

/-- On `Spec R` a short complex of quasi-coherent modules is exact as soon as its global sections
are: the global-sections functor is an equivalence onto `ModuleCat R` there. -/
private theorem exact_of_sections_onSpec (R : CommRingCat.{u}) (S : ShortComplex (Spec R).Modules)
    [S.X₁.IsQuasicoherent] [S.X₂.IsQuasicoherent] [S.X₃.IsQuasicoherent]
    (h : Function.Exact (S.f.app ⊤) (S.g.app ⊤)) : S.Exact := by
  let G := moduleSpecΓFunctor (R := R)
  let : G.Additive := ⟨rfl⟩
  have hG : (S.map G).Exact :=
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).2 h
  have i₁ : IsIso S.X₁.fromTildeΓ := Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent S.X₁
  have i₂ : IsIso S.X₂.fromTildeΓ := Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent S.X₂
  have i₃ : IsIso S.X₃.fromTildeΓ := Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent S.X₃
  let e : (S.map G).map (tilde.functor R) ≅ S :=
    ShortComplex.isoMk (@asIso _ _ _ _ _ i₁) (@asIso _ _ _ _ _ i₂) (@asIso _ _ _ _ _ i₃)
      (Scheme.Modules.fromTildeΓNatTrans.naturality S.f).symm
      (Scheme.Modules.fromTildeΓNatTrans.naturality S.g).symm
  let : PreservesFiniteLimits (tilde.functor R) :=
    AlgebraicGeometry.tilde.preservesFiniteLimits R
  let : PreservesFiniteColimits (tilde.functor R) := inferInstance
  let : (tilde.functor R).PreservesHomology := inferInstance
  exact ShortComplex.exact_of_iso e (hG.map (tilde.functor R))

/-- The image of the whole space under the inverse of an isomorphism of schemes is the whole
space. -/
private theorem image_top_of_iso {X Y : Scheme.{u}} (e : X ≅ Y) :
    e.inv ''ᵁ (⊤ : Y.Opens) = ⊤ := by
  rw [Scheme.Hom.image_top_eq_opensRange]
  ext x
  change (∃ y, e.inv y = x) ↔ True
  exact iff_true_intro ⟨e.hom x, congrArg (fun f : X ⟶ X => f x) e.hom_inv_id⟩

/-- Transport of global sections along an isomorphism of schemes. -/
private def restrictTopIso {X Y : Scheme.{u}} (e : X ≅ Y) (M : X.Modules) :
    Γ(M.restrict e.inv, ⊤) ≅ Γ(M, ⊤) :=
  M.restrictAppIso e.inv ⊤ ≪≫
    M.presheaf.mapIso (eqToIso (image_top_of_iso e)).symm.op

/-- The transport of global sections is natural. -/
private theorem restrictTopIso_naturality {X Y : Scheme.{u}} (e : X ≅ Y)
    {M N : X.Modules} (φ : M ⟶ N) :
    (((Scheme.Modules.restrictFunctor e.inv).map φ).app ⊤) ≫
      (restrictTopIso e N).hom = (restrictTopIso e M).hom ≫ φ.app ⊤ := by
  change (φ.app (e.inv ''ᵁ ⊤)) ≫ N.presheaf.map _ = M.presheaf.map _ ≫ φ.app ⊤
  exact (φ.mapPresheaf.naturality _).symm

/-- Restriction along the inverse of an isomorphism of schemes is an equivalence of categories of
modules. -/
private theorem restrictFunctor_isEquivalence_iso {X Y : Scheme.{u}} (e : X ≅ Y) :
    (Scheme.Modules.restrictFunctor e.inv).IsEquivalence := by
  let G := Scheme.Modules.restrictFunctor e.hom
  let η : 𝟭 X.Modules ≅ Scheme.Modules.restrictFunctor e.inv ⋙ G :=
    (Scheme.Modules.restrictFunctorId (X := X)).symm ≪≫
      (Scheme.Modules.restrictFunctorCongr e.hom_inv_id).symm ≪≫
      Scheme.Modules.restrictFunctorComp e.hom e.inv
  let ε : G ⋙ Scheme.Modules.restrictFunctor e.inv ≅ 𝟭 Y.Modules :=
    (Scheme.Modules.restrictFunctorComp e.inv e.hom).symm ≪≫
      Scheme.Modules.restrictFunctorCongr e.inv_hom_id ≪≫
      Scheme.Modules.restrictFunctorId (X := Y)
  exact Functor.IsEquivalence.mk' G η ε

/-- **On an affine scheme a short complex of quasi-coherent modules is exact as soon as its
global sections are.** -/
private theorem exact_of_sections {X : Scheme.{u}} [IsAffine X] (S : ShortComplex X.Modules)
    [S.X₁.IsQuasicoherent] [S.X₂.IsQuasicoherent] [S.X₃.IsQuasicoherent]
    (h : Function.Exact (S.f.app ⊤) (S.g.app ⊤)) : S.Exact := by
  let e := X.isoSpec
  let G := Scheme.Modules.restrictFunctor e.inv
  let := restrictFunctor_isEquivalence_iso e
  apply (S.exact_map_iff_of_faithful G).mp
  let : (S.map G).X₁.IsQuasicoherent := Scheme.Modules.isQuasicoherent_restrictFunctor e.inv _
  let : (S.map G).X₂.IsQuasicoherent := Scheme.Modules.isQuasicoherent_restrictFunctor e.inv _
  let : (S.map G).X₃.IsQuasicoherent := Scheme.Modules.isQuasicoherent_restrictFunctor e.inv _
  refine exact_of_sections_onSpec _ (S.map G) (Function.Exact.of_ladder_addEquiv_of_exact'
    (restrictTopIso e S.X₁).addCommGroupIsoToAddEquiv
    (restrictTopIso e S.X₂).addCommGroupIsoToAddEquiv
    (restrictTopIso e S.X₃).addCommGroupIsoToAddEquiv ?_ ?_ h)
  · exact congrArg AddCommGrpCat.Hom.hom (restrictTopIso_naturality e S.f).symm
  · exact congrArg AddCommGrpCat.Hom.hom (restrictTopIso_naturality e S.g).symm

/-! ### Quasi-coherence of the terms -/

/-- A finite product of quasi-coherent modules on `Spec R` is quasi-coherent. -/
private theorem isQuasicoherent_product_onSpec (R : CommRingCat.{u}) {I : Type*} [Finite I]
    (M : I → (Spec R).Modules) [∀ i, (M i).IsQuasicoherent] : (∏ᶜ M).IsQuasicoherent := by
  let : Fintype I := Fintype.ofFinite I
  let G := moduleSpecΓFunctor (R := R)
  have hi : ∀ i, IsIso (M i).fromTildeΓ :=
    fun i => Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent (M i)
  let e : (tilde.functor R).obj (∏ᶜ fun i => G.obj (M i)) ≅ ∏ᶜ M :=
    PreservesProduct.iso (tilde.functor R) (fun i => G.obj (M i)) ≪≫
      Pi.mapIso (fun i => @asIso _ _ _ _ _ (hi i))
  exact (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).prop_of_iso e inferInstance

/-- **A finite product of quasi-coherent modules on an affine scheme is quasi-coherent.** -/
private theorem isQuasicoherent_product {X : Scheme.{u}} [IsAffine X] {I : Type*} [Finite I]
    (M : I → X.Modules) [∀ i, (M i).IsQuasicoherent] : (∏ᶜ M).IsQuasicoherent := by
  let : Fintype I := Fintype.ofFinite I
  let e := X.isoSpec
  let G := Scheme.Modules.restrictFunctor e.inv
  let T := Scheme.Modules.restrictFunctor e.hom
  let := restrictFunctor_isEquivalence_iso e
  let : ∀ i, (G.obj (M i)).IsQuasicoherent := fun i =>
    Scheme.Modules.isQuasicoherent_restrictFunctor e.inv (M i)
  have hprod : (∏ᶜ fun i => G.obj (M i)).IsQuasicoherent :=
    isQuasicoherent_product_onSpec _ _
  let : (G.obj (∏ᶜ M)).IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent (Spec Γ(X, ⊤)).ringCatSheaf).prop_of_iso
      (PreservesProduct.iso G M).symm hprod
  have hb : (T.obj (G.obj (∏ᶜ M))).IsQuasicoherent :=
    Scheme.Modules.isQuasicoherent_restrictFunctor e.hom (G.obj (∏ᶜ M))
  let eBack : T.obj (G.obj (∏ᶜ M)) ≅ ∏ᶜ M :=
    ((Scheme.Modules.restrictFunctorComp e.hom e.inv).symm ≪≫
      Scheme.Modules.restrictFunctorCongr e.hom_inv_id ≪≫
      Scheme.Modules.restrictFunctorId).app _
  exact (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso eBack hb

/-- **Every term of the extended alternating Čech complex of a quasi-coherent module on an affine
scheme is quasi-coherent.** -/
private theorem isQuasicoherent_cechTerm {X : Scheme.{u}} [IsAffine X] {c : ℕ}
    (f : Fin c → Γ(X, ⊤)) (F : X.Modules) [F.IsQuasicoherent] (p : ℕ) :
    ((extendedAlternatingCech f F).complex.X p).IsQuasicoherent := by
  cases p with
  | zero =>
      exact (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
        (extendedAlternatingCech f F).zeroIso.symm inferInstance
  | succ p =>
      have hqc (s : CechCochains.OrdIndex (I := Fin c) p) :
          (restrictedModule f F p s).IsQuasicoherent := by
        unfold Stacks.Perfect.ExtendedAlternatingCech.restrictedModule
        rw [equationsOpen_eq_basicOpen_prod]
        let j := (X.basicOpen (∏ k, f (s.1 k))).ι
        have : ((Scheme.Modules.pullback j).obj F).IsQuasicoherent :=
          (SheafOfModules.isQuasicoherent
              (X.basicOpen (∏ k, f (s.1 k))).toScheme.ringCatSheaf).prop_of_iso
            ((Scheme.Modules.restrictFunctorIsoPullback j).app F) inferInstance
        infer_instance
      exact (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
        ((extendedAlternatingCech f F).termIso p).symm (isQuasicoherent_product _)

/-! ### The identification of the complexes, and the vanishing -/

/-- Global sections of modules on `X`, as an additive functor to abelian groups. -/
private def sectionsFunctor (X : Scheme.{u}) : X.Modules ⥤ AddCommGrpCat.{u} :=
  Scheme.Modules.toPresheaf X ⋙
    (CategoryTheory.evaluation _ _).obj (Opposite.op (⊤ : X.Opens))

private theorem sectionsFunctor_additive (X : Scheme.{u}) :
    (sectionsFunctor X).Additive := ⟨rfl⟩

attribute [local instance] sectionsFunctor_additive

/-- **The complex of global sections of the extended alternating Čech complex of `F` on an affine
scheme is the algebraic extended alternating Čech complex of `Γ(F, ⊤)`**, as complexes of abelian
groups. -/
private def cechSectionsComplexIso {X : Scheme.{u}} [IsAffine X] {c : ℕ} (f : Fin c → Γ(X, ⊤))
    (F : X.Modules) [F.IsQuasicoherent] :
    ((forget₂ (ModuleCat Γ(X, ⊤)) AddCommGrpCat).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj (_root_.Cech.cechComplex f ↑Γ(F, ⊤)) ≅
      ((sectionsFunctor X).mapHomologicalComplex (ComplexShape.up ℕ)).obj
        (extendedAlternatingCech f F).complex := by
  refine HomologicalComplex.Hom.isoOfComponents
    (fun p => (cechAllSectionsEquiv f F p).toAddCommGrpIso) ?_
  intro i j hij
  obtain rfl : i + 1 = j := by simpa [ComplexShape.up_Rel] using hij
  apply ConcreteCategory.hom_ext
  intro x
  simp only [Functor.mapHomologicalComplex_obj_d, _root_.Cech.cechComplex, CochainComplex.of_d]
  exact (cechAllSectionsEquiv_comm_d f F i x).symm

/-- **The extended alternating Čech complex of a Koszul-regular sequence with flat coefficients
is exact away from the length of the sequence.**  Let `X` be an affine scheme, let
`f₁, …, f_c ∈ Γ(X, 𝒪_X)` be a Koszul-regular sequence and let `F` be a quasi-coherent
`𝒪_X`-module whose module of global sections is flat over `Γ(X, 𝒪_X)`.  Then the extended
alternating Čech complex of [Stacks, Tag 0G7I] is exact in every degree other than `c`.

On global sections the complex is the algebraic extended alternating Čech complex of `Γ(F, ⊤)`,
which is the statement `cechSectionsComplexIso`; that complex is acyclic away from degree `c` by
Stacks 0G6L for flat coefficients; and on an affine, exactness of a short complex of
quasi-coherent modules is exactness of its global sections. -/
public theorem extendedAlternatingCech_exactAt_of_isKoszulRegular_of_flat {X : Scheme.{u}}
    [IsAffine X] {c : ℕ} (f : Fin c → Γ(X, ⊤)) (hf : Koszul.IsKoszulRegular f)
    (F : X.Modules) [F.IsQuasicoherent] [Module.Flat Γ(X, ⊤) Γ(F, ⊤)] (p : ℕ) (hp : p ≠ c) :
    (extendedAlternatingCech f F).complex.ExactAt p := by
  let K := (extendedAlternatingCech f F).complex
  have hA := (HomologicalComplex.exactAt_iff_isZero_homology _ _).mpr
    (_root_.Cech.cechComplex_homology_isZero_of_isKoszulRegular_of_flat f ↑Γ(F, ⊤) hf p hp)
  have hB : (((forget₂ (ModuleCat Γ(X, ⊤)) AddCommGrpCat).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj (_root_.Cech.cechComplex f ↑Γ(F, ⊤))).ExactAt p :=
    hA.map (forget₂ (ModuleCat Γ(X, ⊤)) AddCommGrpCat)
  have hC := hB.of_iso (cechSectionsComplexIso f F)
  exact @exact_of_sections _ _ (K.sc p) (isQuasicoherent_cechTerm f F _)
    (isQuasicoherent_cechTerm f F _) (isQuasicoherent_cechTerm f F _)
    ((ShortComplex.ab_exact_iff_function_exact _).mp hC)

end Stacks.Perfect.CechAffineSections

end
