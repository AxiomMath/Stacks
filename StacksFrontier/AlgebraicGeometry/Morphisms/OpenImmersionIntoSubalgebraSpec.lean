module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.IsIso
import StacksCore.Tactic.EgaSgaAttribute

/-!
# A quasi-compact open of finite type survives in the spectrum of a large enough subring

Let `φ : R ⟶ A` be a ring map and let `W ⊆ Spec A` be a quasi-compact open which is locally of
finite type over `Spec R`. Then finitely many elements of `A` control `W`: for every subring
`A' ⊆ A` containing `R`'s image and those elements, there is an open `O ⊆ Spec A'` whose preimage
in `Spec A` is `W` and over which `Spec A ⟶ Spec A'` is an isomorphism. In particular `W` maps
isomorphically onto an open of `Spec A'`.

The open is a finite union of basic opens `D(rₖ)` with `rₖ ∈ A'`. Over `D(rₖ)` the map
`Spec A ⟶ Spec A'` is `Spec` of `A'_{rₖ} ⟶ A_{rₖ}`, which is injective because localization is
exact, and surjective once `A'` contains numerators of finitely many generators of the finite
type `R`-algebra `A_{rₖ}`.

## Main results

* `AlgebraicGeometry.isIso_morphismRestrict_iSup_basicOpen`: `Spec A ⟶ Spec A'` is an isomorphism
  over a union of basic opens away from whose members the ring map is bijective.
* `AlgebraicGeometry.exists_finset_bijective_awayMap`: the localization `A'_{r'} ⟶ A_a` is
  bijective as soon as `A'` contains finitely many prescribed elements.
* `AlgebraicGeometry.exists_finset_isIso_morphismRestrict_specMap`: the statement above.

## Implementation notes

This is the ring-theoretic step of the argument by which an integral morphism of algebraic spaces
is replaced by a finite one without losing a given quasi-compact open of finite type, the
replacement being the relative spectrum of a finite subalgebra.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

variable {A' A : CommRingCat.{u}} (ι : A' ⟶ A)

/-- The localization of an injective ring map away from an element is injective. -/
theorem injective_awayMap_of_injective (hι : Function.Injective ι.hom) (r : A') :
    Function.Injective (Localization.awayMap ι.hom r) := by
  have : IsLocalization ((Submonoid.powers r).map ι.hom) (Localization.Away (ι.hom r)) := by
    rw [Submonoid.map_powers]
    infer_instance
  exact IsLocalization.map_injective_of_injective (Submonoid.powers r) (Localization.Away r)
    (Localization.Away (ι.hom r)) hι

/-- **`Spec A ⟶ Spec A'` is an isomorphism over a union of basic opens over whose members it is
one.** If `ι : A' ⟶ A` becomes bijective after inverting each member of a family `r`, then the
restriction of `Spec ι` over `⋃ D(rₖ)` is an isomorphism. -/
theorem isIso_morphismRestrict_iSup_basicOpen {K : Type*} (r : K → A')
    (hr : ∀ k, Function.Bijective (Localization.awayMap ι.hom (r k))) :
    IsIso (Spec.map ι ∣_ ⨆ k, (PrimeSpectrum.basicOpen (r k) : (Spec A').Opens)) := by
  set D : K → (Spec A').Opens := fun k => PrimeSpectrum.basicOpen (r k)
  set O : (Spec A').Opens := ⨆ k, D k
  refine (IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := MorphismProperty.isomorphisms Scheme)
    (f := Spec.map ι ∣_ O) (fun k => O.ι ⁻¹ᵁ D k) ?_).2 fun k => ?_
  · refine top_le_iff.1 fun x _ => ?_
    have hx : x.1 ∈ O := x.2
    obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨k, hk⟩
  · have himg : O.ι ''ᵁ (O.ι ⁻¹ᵁ D k) = D k := by
      rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι, inf_eq_right]
      exact le_iSup D k
    have : IsIso (CommRingCat.ofHom (Localization.awayMap ι.hom (r k))) :=
      (ConcreteCategory.isIso_iff_bijective _).mpr (hr k)
    exact ((MorphismProperty.isomorphisms Scheme).arrow_mk_iso_iff
      (morphismRestrictRestrict _ O _ ≪≫ morphismRestrictEq _ himg ≪≫
        SpecMapRestrictBasicOpenIso ι (r k))).2
      (inferInstance : IsIso (Spec.map (CommRingCat.ofHom (Localization.awayMap ι.hom (r k)))))

/-- **Finitely many elements of `A` make a localization of finite type survive in any subring
containing them.** Let `φ : R →+* A` and `a : A` be such that `A_a` is of finite type over `R`.
There is a finite set `G ∋ a` of elements of `A` such that for every factorization
`R → A' ↪ A` of `φ` through an injective ring map whose image contains `G`, and every `r' ∈ A'`
mapping to `a`, the induced map `A'_{r'} → A_a` is bijective. -/
theorem exists_finset_bijective_awayMap {R A : Type u} [CommRing R] [CommRing A] (φ : R →+* A)
    (a : A) (hft : ((algebraMap A (Localization.Away a)).comp φ).FiniteType) :
    ∃ G : Finset A, a ∈ G ∧ ∀ (A' : Type u) [CommRing A'] (ψ : R →+* A') (ι : A' →+* A),
      ι.comp ψ = φ → Function.Injective ι → (G : Set A) ⊆ Set.range ι → ∀ r' : A', ι r' = a →
        Function.Bijective (Localization.awayMap ι r') := by
  classical
  let : Algebra R (Localization.Away a) := ((algebraMap A (Localization.Away a)).comp φ).toAlgebra
  obtain ⟨T, hT⟩ := (hft : Algebra.FiniteType R (Localization.Away a)).out
  choose pr hpr using IsLocalization.mk'_surjective (Submonoid.powers a) (S := Localization.Away a)
  refine ⟨insert a (T.image fun x => (pr x).1), Finset.mem_insert_self _ _, ?_⟩
  rintro A' _ ψ ι hcomp hinj hG r' rfl
  refine ⟨injective_awayMap_of_injective (CommRingCat.ofHom ι) hinj r', ?_⟩
  set g := Localization.awayMap ι r'
  -- the range of `g` is an `R`-subalgebra
  let Sg : Subalgebra R (Localization.Away (ι r')) :=
    { carrier := Set.range g
      mul_mem' := by rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩; exact ⟨x * y, map_mul g x y⟩
      add_mem' := by rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩; exact ⟨x + y, map_add g x y⟩
      algebraMap_mem' := fun x => by
        refine ⟨algebraMap A' (Localization.Away r') (ψ x), ?_⟩
        change g (algebraMap A' _ (ψ x)) = algebraMap A _ (φ x)
        rw [← hcomp]
        exact IsLocalization.map_eq _ _ }
  have hTS : (T : Set (Localization.Away (ι r'))) ⊆ Sg := by
    intro x hx
    obtain ⟨b', hb'⟩ := hG (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hx))
    obtain ⟨n, hn⟩ := (pr x).2.2
    refine ⟨IsLocalization.mk' (Localization.Away r') b'
      ⟨r' ^ n, Submonoid.pow_mem _ (Submonoid.mem_powers r') n⟩, ?_⟩
    have hmap : g (IsLocalization.mk' (Localization.Away r') b'
        ⟨r' ^ n, Submonoid.pow_mem _ (Submonoid.mem_powers r') n⟩) =
        IsLocalization.mk' (Localization.Away (ι r')) (ι b')
          ⟨ι r' ^ n, Submonoid.pow_mem _ (Submonoid.mem_powers _) n⟩ := by
      simp [g, IsLocalization.Away.map, IsLocalization.map_mk']
    rw [hmap, ← hpr x]
    congr 1
    ext
    simp [← hn]
  exact fun y => Algebra.adjoin_le hTS (hT ▸ Algebra.mem_top)

/-- A point lies in an open with complement `V(t)` iff `t` is not contained in its prime. -/
private theorem mem_iff_not_subset_of_compl_zeroLocus_eq {A : CommRingCat.{u}} {t : Finset A}
    {W : (Spec A).Opens} (ht : (PrimeSpectrum.zeroLocus (t : Set A))ᶜ = (W : Set (Spec A)))
    (x : Spec A) : x ∈ W ↔ ¬ ((t : Set A) ⊆ (x : PrimeSpectrum A).asIdeal) := by
  rw [← SetLike.mem_coe, ← ht]
  rfl

/-- A union of basic opens of `Spec A` over a finite set `t` is the open whose complement is the
zero locus of `t`. -/
theorem iSup_basicOpen_eq_of_compl_zeroLocus_eq {A : CommRingCat.{u}} (t : Finset A)
    (W : (Spec A).Opens) (ht : (PrimeSpectrum.zeroLocus (t : Set A))ᶜ = (W : Set (Spec A))) :
    (⨆ a : t, (PrimeSpectrum.basicOpen a.1 : (Spec A).Opens)) = W := by
  have hW' := mem_iff_not_subset_of_compl_zeroLocus_eq ht
  refine le_antisymm (iSup_le fun a x hx => (hW' x).2 fun hz => ?_) fun x hx => ?_
  · exact (PrimeSpectrum.mem_basicOpen _ _).1 hx (hz a.2)
  · obtain ⟨a, ha, hxa⟩ := Set.not_subset.1 ((hW' x).1 hx)
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨a, ha⟩, (PrimeSpectrum.mem_basicOpen _ _).2 hxa⟩

/-- **A basic open inside an open of finite type is of finite type.** If `W ⊆ Spec A` is locally
of finite type over `Spec R` and `D(a) ⊆ W`, then `A_a` is of finite type over `R`. -/
private theorem finiteType_comp_algebraMap_away_of_basicOpen_le {R A : CommRingCat.{u}} (φ : R ⟶ A)
    (W : (Spec A).Opens) [LocallyOfFiniteType (W.ι ≫ Spec.map φ)] (a : A)
    (h : (PrimeSpectrum.basicOpen a : (Spec A).Opens) ≤ W) :
    ((algebraMap A (Localization.Away a)).comp φ.hom).FiniteType := by
  let D : (Spec A).Opens := PrimeSpectrum.basicOpen a
  have hD : D ≤ W := h
  have h1 : LocallyOfFiniteType ((Spec A).homOfLE hD ≫ W.ι ≫ Spec.map φ) := inferInstance
  have h1' : (Spec A).homOfLE hD ≫ W.ι ≫ Spec.map φ = D.ι ≫ Spec.map φ := by
    rw [← Category.assoc, Scheme.homOfLE_ι]
  rw [h1'] at h1
  have h2 : LocallyOfFiniteType ((basicOpenIsoSpecAway a).inv ≫ D.ι ≫ Spec.map φ) :=
    inferInstance
  have h2' : (basicOpenIsoSpecAway a).inv ≫ D.ι ≫ Spec.map φ =
      Spec.map (φ ≫ CommRingCat.ofHom (algebraMap A (Localization.Away a))) := by
    rw [← Category.assoc, show D.ι = (basicOpenIsoSpecAway a).hom ≫
        Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away a))) from
        (basicOpenIsoSpecAway_hom_SpecMap a).symm, ← Category.assoc, Iso.inv_hom_id,
      Category.id_comp, Spec.map_comp]
  rw [h2'] at h2
  exact HasRingHomProperty.Spec_iff.1 h2

/-- **A quasi-compact open of `Spec A` of finite type over `Spec R` survives in `Spec A'` for every
subring `A'` of `A` containing finitely many given elements.** Let `φ : R ⟶ A` and let `W` be a
quasi-compact open of `Spec A` which is locally of finite type over `Spec R`. There is a finite set
`G` of elements of `A` such that for every factorization `R ⟶ A' ⟶ A` of `φ` through an injective
`ι` whose image contains `G`, there is an open `O` of `Spec A'` whose preimage is `W` and over
which `Spec ι` is an isomorphism. -/
theorem exists_finset_isIso_morphismRestrict_specMap {R A : CommRingCat.{u}} (φ : R ⟶ A)
    (W : (Spec A).Opens) (hW : IsCompact (W : Set (Spec A)))
    (hft : LocallyOfFiniteType (W.ι ≫ Spec.map φ)) :
    ∃ G : Finset A, ∀ (A' : CommRingCat.{u}) (ψ : R ⟶ A') (ι : A' ⟶ A), ψ ≫ ι = φ →
      Function.Injective ι.hom → (G : Set A) ⊆ Set.range ι.hom →
        ∃ O : (Spec A').Opens, Spec.map ι ⁻¹ᵁ O = W ∧ IsIso (Spec.map ι ∣_ O) := by
  classical
  obtain ⟨t, ht⟩ := PrimeSpectrum.isCompact_isOpen_iff.1 ⟨hW, W.2⟩
  let D : A → (Spec A).Opens := fun a => PrimeSpectrum.basicOpen a
  have hle : ∀ a ∈ t, D a ≤ W := fun a ha x hx =>
    (mem_iff_not_subset_of_compl_zeroLocus_eq ht x).2 fun hz => hx (hz (Finset.mem_coe.2 ha))
  choose G hG hGbij using fun (a : t) => exists_finset_bijective_awayMap φ.hom a.1
    (finiteType_comp_algebraMap_away_of_basicOpen_le φ W a.1 (hle a.1 a.2))
  refine ⟨Finset.univ.biUnion G, fun A' ψ ι hcomp hinj hsub => ?_⟩
  have hsub' : ∀ a : t, (G a : Set A) ⊆ Set.range ι.hom := fun a x hx =>
    hsub (Finset.mem_coe.2 (Finset.mem_biUnion.2 ⟨a, Finset.mem_univ _, hx⟩))
  choose r' hr' using fun (a : t) => hsub' a (hG a)
  have hbij : ∀ a : t, Function.Bijective (Localization.awayMap ι.hom (r' a)) := fun a =>
    hGbij a A' ψ.hom ι.hom (congrArg CommRingCat.Hom.hom hcomp) hinj (hsub' a) (r' a) (hr' a)
  let D' : t → (Spec A').Opens := fun a => PrimeSpectrum.basicOpen (r' a)
  have hD' : ∀ a, Spec.map ι ⁻¹ᵁ D' a = D a.1 := fun a =>
    (PrimeSpectrum.comap_basicOpen ι.hom (r' a)).trans (congrArg _ (hr' a))
  refine ⟨⨆ a, D' a, ?_, isIso_morphismRestrict_iSup_basicOpen ι r' hbij⟩
  simp_rw [Scheme.Hom.preimage_iSup, hD']
  exact iSup_basicOpen_eq_of_compl_zeroLocus_eq t W ht

/-- **The affine-scheme form.** Let `p : Y ⟶ Z₀` be a morphism of affine schemes and `j : W ⟶ Y` a
quasi-compact open immersion with `j ≫ p` locally of finite type. There are finitely many global
functions on `Y` such that for every factorization `Y ⟶ T ⟶ Z₀` of `p` through an affine scheme `T`
whose ring map `Γ(T) ⟶ Γ(Y)` is injective with image containing them, `j ≫ (Y ⟶ T)` is an open
immersion. -/
@[ega "II 5.1.9" "special case"]
theorem exists_finset_isOpenImmersion_comp_of_isAffine {Y Z₀ W : Scheme.{u}} [IsAffine Y]
    [IsAffine Z₀] (p : Y ⟶ Z₀) (j : W ⟶ Y) [IsOpenImmersion j] [CompactSpace W]
    [LocallyOfFiniteType (j ≫ p)] :
    ∃ G : Finset Γ(Y, ⊤), ∀ {T : Scheme.{u}} [IsAffine T] (m : Y ⟶ T) (p' : T ⟶ Z₀),
      m ≫ p' = p → Function.Injective m.appTop.hom → (G : Set Γ(Y, ⊤)) ⊆ Set.range m.appTop.hom →
        IsOpenImmersion (j ≫ m) := by
  let j' : W ⟶ Spec Γ(Y, ⊤) := j ≫ Y.isoSpec.hom
  let W' : (Spec Γ(Y, ⊤)).Opens := j'.opensRange
  have hW' : IsCompact (W' : Set (Spec Γ(Y, ⊤))) := isCompact_range j'.continuous
  let e := j'.isoOpensRange
  have he : e.hom ≫ W'.ι = j' := j'.isoOpensRange_hom_ι
  have hft : LocallyOfFiniteType (W'.ι ≫ Spec.map p.appTop) := by
    have : W'.ι ≫ Spec.map p.appTop = e.inv ≫ (j ≫ p) ≫ Z₀.isoSpec.hom := by
      calc W'.ι ≫ Spec.map p.appTop = e.inv ≫ (e.hom ≫ W'.ι) ≫ Spec.map p.appTop := by simp
        _ = e.inv ≫ j' ≫ Spec.map p.appTop := by rw [he]
        _ = e.inv ≫ (j ≫ p) ≫ Z₀.isoSpec.hom := by
          simp only [j', Category.assoc, Scheme.isoSpec_hom_naturality]
    rw [this]
    infer_instance
  obtain ⟨G, hG⟩ := exists_finset_isIso_morphismRestrict_specMap p.appTop W' hW' hft
  refine ⟨G, fun {T} _ m p' hmp hinj hsub => ?_⟩
  have hcomp : p'.appTop ≫ m.appTop = p.appTop := by rw [← Scheme.Hom.comp_appTop, hmp]
  obtain ⟨O, hO, hiso⟩ := hG _ p'.appTop m.appTop hcomp hinj hsub
  have hOW : IsOpenImmersion (W'.ι ≫ Spec.map m.appTop) := by
    have h1 : W'.ι ≫ Spec.map m.appTop =
        ((Spec Γ(Y, ⊤)).isoOfEq hO.symm).hom ≫ (Spec.map m.appTop ∣_ O) ≫ O.ι := by
      rw [morphismRestrict_ι, ← Category.assoc, Scheme.isoOfEq_hom_ι]
    rw [h1]
    infer_instance
  have h2 : j ≫ m = e.hom ≫ (W'.ι ≫ Spec.map m.appTop) ≫ T.isoSpec.inv := by
    simp only [Category.assoc]
    rw [reassoc_of% he]
    simp [j', Scheme.isoSpec_hom_naturality_assoc]
  rw [h2]
  infer_instance

end AlgebraicGeometry

end
