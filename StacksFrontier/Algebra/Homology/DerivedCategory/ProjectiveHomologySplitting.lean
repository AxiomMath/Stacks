module

public import Mathlib.Algebra.Homology.DerivedCategory.Plus
public import StacksFrontier.Algebra.Homology.DerivedCategory.ProjectiveCorepresents
public import StacksFrontier.Algebra.Homology.DerivedCategory.TruncGELTSingle

/-!
# A bounded below complex with projective cohomology is the sum of its cohomology

Let `𝒜` be an abelian category and let `L` be an object of the bounded below derived category
`D⁺(𝒜)` whose cohomology objects `Hᑫ(L)` are projective and vanish outside a finite set `I` of
degrees. Then

`L ≅ ⨁_{q ∈ I} Hᑫ(L)[-q]`

in `D⁺(𝒜)`. This is the remark on "the derived category of a field" used in the proof of
[Stacks, Tag 0BEF]: over a field every module is projective, so every bounded complex is
isomorphic to the sum of its shifted cohomology modules.

The isomorphism is the canonical one. For `P = Hᑫ(L)` projective, taking cohomology in degree
`q` is a bijection `Hom(P[-q], L) ≅ Hom(P, Hᑫ(L))`
(`DerivedCategory.homologyFromSingleAddEquiv`), so there is exactly one morphism
`DerivedCategory.Plus.homologySection L q : Hᑫ(L)[-q] ⟶ L` inducing the identity on `Hᑫ`; the
splitting is the morphism out of the biproduct whose components are these.

## Main definitions

* `DerivedCategory.Plus.homologySection`: the morphism `Hᑫ(L)[-q] ⟶ L` inducing the identity on
  `Hᑫ`, for `Hᑫ(L)` projective.
* `DerivedCategory.Plus.homologySplitting`: the isomorphism `L ≅ ⨁_{q ∈ I} Hᑫ(L)[-q]`.

## Main results

* `DerivedCategory.Plus.homologyFunctor_map_homologySection`: on `Hᑫ` the section is the
  canonical identification `H^q(Hᑫ(L)[-q]) ≅ Hᑫ(L)`.
* `DerivedCategory.Plus.isIso_biproduct_desc_homologySection`: the morphism out of the biproduct
  is an isomorphism.
-/

@[expose] public noncomputable section

open CategoryTheory Limits

universe w v u

namespace DerivedCategory.Plus

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

/-! ### Biproducts and additive functors killing all but one summand -/

section Biproduct

variable {D E : Type*} [Category* D] [Category* E] [Preadditive D] [Preadditive E]
  (H : D ⥤ E) [H.Additive] {J : Type} [Finite J]
  (X : J → D) [HasBiproduct X]

/-- An additive functor which kills every summand of a finite biproduct kills the biproduct. -/
theorem isZero_map_biproduct_of_forall (h : ∀ j, IsZero (H.obj (X j))) :
    IsZero (H.obj (⨁ X)) := by
  have := Fintype.ofFinite J
  rw [IsZero.iff_id_eq_zero, ← H.map_id, ← biproduct.total, H.map_sum]
  refine Finset.sum_eq_zero fun j _ ↦ ?_
  rw [H.map_comp, (h j).eq_of_src (H.map (biproduct.ι X j)) 0, comp_zero]

/-- An additive functor which kills every summand of a finite biproduct but the `m`-th sends a
morphism `biproduct.desc g` out of the biproduct to `H.map (π m) ≫ H.map (g m)`. -/
private theorem map_biproduct_desc_eq_of_forall_ne (m : J)
    (h : ∀ j, j ≠ m → IsZero (H.obj (X j))) {Y : D} (g : ∀ j, X j ⟶ Y) :
    H.map (biproduct.desc g) = H.map (biproduct.π X m) ≫ H.map (g m) := by
  have := Fintype.ofFinite J
  rw [biproduct.desc_eq, H.map_sum, Finset.sum_eq_single m (fun j _ hj ↦ ?_) (by simp), H.map_comp]
  rw [H.map_comp, (h j hj).eq_of_tgt (H.map (biproduct.π X j)) 0, zero_comp]

/-- An additive functor which kills every summand of a finite biproduct but the `m`-th sends the
projection onto the `m`-th summand to an isomorphism. -/
theorem isIso_map_biproduct_π_of_forall_ne (m : J) (h : ∀ j, j ≠ m → IsZero (H.obj (X j))) :
    IsIso (H.map (biproduct.π X m)) := by
  have := Fintype.ofFinite J
  refine ⟨H.map (biproduct.ι X m), ?_, ?_⟩
  · rw [← H.map_id, ← biproduct.total, ← biproduct.desc_eq,
      map_biproduct_desc_eq_of_forall_ne H X m h]
  · rw [← H.map_comp, biproduct.ι_π_self, H.map_id]

end Biproduct

/-! ### A projective object corepresents cohomology in `D⁺` -/

/-- **A projective object corepresents cohomology in `D⁺(𝒜)`**: for `P` projective, taking
cohomology in degree `a` is a bijection `Hom(P[-a], K) ≅ Hom(P, Hᵃ(K))`. This is
`DerivedCategory.homologyFromSingleAddEquiv` read through the fully faithful inclusion
`D⁺(𝒜) ⥤ D(𝒜)`. -/
def homologyFromSingleAddEquiv (P : C) [Projective P] (K : Plus C) (a : ℤ) :
    ((singleFunctor C a).obj P ⟶ K) ≃+ (P ⟶ (homologyFunctor C a).obj K) :=
  (AddEquiv.mk' (DerivedCategory.TStructure.t.plus.fullyFaithfulι.homEquiv)
    (fun _ _ ↦ ι.map_add)).trans
      (DerivedCategory.homologyFromSingleAddEquiv P (ι.obj K) a)

/-- The bijection `homologyFromSingleAddEquiv P K a` sends `f : P[-a] ⟶ K` to `Hᵃ(f)` precomposed
with the identification `P ≅ Hᵃ(P[-a])`. -/
theorem homologyFromSingleAddEquiv_apply (P : C) [Projective P] (K : Plus C) (a : ℤ)
    (f : (singleFunctor C a).obj P ⟶ K) :
    homologyFromSingleAddEquiv P K a f =
      (singleFunctorCompHomologyFunctorIso (C := C) a).inv.app P ≫ (homologyFunctor C a).map f :=
  rfl

/-- The bijection `homologyFromSingleAddEquiv` is natural in the target: postcomposing with
`g : K ⟶ K'` corresponds to postcomposing with `Hᵃ(g)`. -/
theorem homologyFromSingleAddEquiv_comp (P : C) [Projective P] {K K' : Plus C} (a : ℤ)
    (f : (singleFunctor C a).obj P ⟶ K) (g : K ⟶ K') :
    homologyFromSingleAddEquiv P K' a (f ≫ g) =
      homologyFromSingleAddEquiv P K a f ≫ (homologyFunctor C a).map g := by
  simp [homologyFromSingleAddEquiv_apply]

/-! ### The section of a projective cohomology object -/

variable (L : Plus C) (q : ℤ)

/-- **The canonical morphism `Hᑫ(L)[-q] ⟶ L`** for `Hᑫ(L)` projective: the unique one inducing
the identity on `Hᑫ` (`DerivedCategory.Plus.homologyFromSingleAddEquiv`). -/
def homologySection [Projective ((homologyFunctor C q).obj L)] :
    (singleFunctor C q).obj ((homologyFunctor C q).obj L) ⟶ L :=
  (homologyFromSingleAddEquiv ((homologyFunctor C q).obj L) L q).symm (𝟙 _)

/-- **On `Hᑫ` the section is the canonical identification `Hᑫ(Hᑫ(L)[-q]) ≅ Hᑫ(L)`.** -/
theorem homologyFunctor_map_homologySection [Projective ((homologyFunctor C q).obj L)] :
    (homologyFunctor C q).map (homologySection L q) =
      (singleFunctorCompHomologyFunctorIso (C := C) q).hom.app ((homologyFunctor C q).obj L) := by
  have h := (homologyFromSingleAddEquiv ((homologyFunctor C q).obj L) L q).apply_symm_apply (𝟙 _)
  rw [homologyFromSingleAddEquiv_apply, ← Iso.app_inv, Iso.inv_comp_eq] at h
  exact h.trans (Category.comp_id _)

/-- The section `homologySection L q` induces an isomorphism on `Hᑫ`. -/
instance isIso_homologyFunctor_map_homologySection [Projective ((homologyFunctor C q).obj L)] :
    IsIso ((homologyFunctor C q).map (homologySection L q)) := by
  rw [homologyFunctor_map_homologySection]
  exact ((singleFunctorCompHomologyFunctorIso (C := C) q).app _).isIso_hom

/-- Cohomology of a single complex vanishes away from its degree. -/
theorem isZero_homologyFunctor_singleFunctor_obj (X : C) {n q : ℤ} (h : n ≠ q) :
    IsZero ((homologyFunctor C n).obj ((singleFunctor C q).obj X)) := by
  rcases lt_or_gt_of_ne h with h | h
  · exact isZero_homology_of_isGE _ q n h
  · exact isZero_homology_of_isLE _ q n h

/-! ### The splitting -/

variable (I : Finset ℤ)
  (hP : ∀ q ∈ I, Projective ((homologyFunctor C q).obj L))

/-- The summands `Hᑫ(L)[-q]`, `q ∈ I`, of the splitting. -/
abbrev homologySummand (q : I) : Plus C :=
  (singleFunctor C q).obj ((homologyFunctor C q).obj L)

/-- **A bounded below complex with projective cohomology in finitely many degrees is the sum of
its shifted cohomology objects**: the morphism `⨁_{q ∈ I} Hᑫ(L)[-q] ⟶ L` with components the
sections `homologySection L q` is an isomorphism, provided `Hᑫ(L) = 0` for `q ∉ I`. -/
theorem isIso_biproduct_desc_homologySection
    (hZ : ∀ q, q ∉ I → IsZero ((homologyFunctor C q).obj L)) :
    IsIso (biproduct.desc (f := homologySummand L I)
      fun q : I ↦ @homologySection _ _ _ _ L q (hP q q.2)) := by
  classical
  rw [isIso_iff]
  intro n
  by_cases hn : n ∈ I
  · have := hP n hn
    have hz : ∀ j : I, j ≠ ⟨n, hn⟩ → IsZero ((homologyFunctor C n).obj (homologySummand L I j)) :=
      fun j hj ↦ isZero_homologyFunctor_singleFunctor_obj _ fun h ↦ hj (Subtype.ext h.symm)
    have hπ := isIso_map_biproduct_π_of_forall_ne (homologyFunctor C n)
      (homologySummand L I) ⟨n, hn⟩ hz
    rw [map_biproduct_desc_eq_of_forall_ne (homologyFunctor C n) (homologySummand L I) ⟨n, hn⟩ hz]
    infer_instance
  · have hX := isZero_map_biproduct_of_forall (homologyFunctor C n) (homologySummand L I)
      fun j ↦ isZero_homologyFunctor_singleFunctor_obj _ fun h ↦ hn (h ▸ j.2)
    exact ⟨⟨0, hX.eq_of_src _ _, (hZ n hn).eq_of_src _ _⟩⟩

/-- **The splitting** `L ≅ ⨁_{q ∈ I} Hᑫ(L)[-q]` of a bounded below complex whose cohomology is
projective and vanishes outside the finite set `I`. -/
def homologySplitting
    (hZ : ∀ q, q ∉ I → IsZero ((homologyFunctor C q).obj L)) :
    L ≅ ⨁ homologySummand L I :=
  have := isIso_biproduct_desc_homologySection L I hP hZ
  (asIso (biproduct.desc (f := homologySummand L I)
    fun q : I ↦ @homologySection _ _ _ _ L q (hP q q.2))).symm

end DerivedCategory.Plus
