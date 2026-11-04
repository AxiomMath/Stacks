module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.QuasiAffine
public import StacksFrontier.AlgebraicGeometry.AmpleCluster.Basic
public import StacksFrontier.AlgebraicGeometry.CompactOpenLocalization.StageOpenImmersion
public import StacksFrontier.AlgebraicGeometry.NoetherianApproximation.FibreProductOpenImmersion

/-!
# Finitely many global functions make a quasi-affine scheme open in a spectrum

Let `π : V ⟶ U` be a morphism locally of finite type from a quasi-affine scheme to an affine
scheme.  Then there is a finite set `s` of global functions on `V` with the following property:
for every affine scheme `P` over `U` and every morphism `g : V ⟶ P` over `U` such that
`g^* : Γ(P) ⟶ Γ(V)` is injective and its image contains `s`, the morphism `g` is an open
immersion.

This is the chart-level step in the proof of Stacks 0871 for an algebraic-space target: a
quasi-affine morphism of finite type is an open immersion into the relative spectrum of any
quasi-coherent subalgebra of its direct-image algebra which contains finitely many given local
sections.

## The argument

Cover `V` by finitely many affine basic opens `V_{b_i}` of global sections.  Then
`Γ(V)_{b_i} = Γ(V_{b_i})` is of finite type over `Γ(U)`; choose generators `h/b_i^N`.  The set
`s` consists of the `b_i` and the numerators `h`.  If `φ = g^* : C = Γ(P) ⟶ Γ(V)` is injective
with image containing `s`, write `b_i = φ(c_i)`; then `C_{c_i} ⟶ Γ(V)_{b_i}` is injective
(localization is exact) and surjective (its image is a `Γ(U)`-subalgebra containing the
generators), so `⨆ D(b_i) ⟶ Spec C` is an open immersion
(`AlgebraicGeometry.isOpenImmersion_iSup_basicOpen_comp_SpecMap_of_isPullback`, along the
trivial pullback square), and so is `V ⟶ Spec Γ(V) ⟶ Spec C`
(`AlgebraicGeometry.isOpenImmersion_toSpecΓ_comp'`).

## Main results

* `AlgebraicGeometry.exists_finset_isOpenImmersion_toSpecΓ_comp_specMap`: the ring-level form.
* `AlgebraicGeometry.exists_finset_isOpenImmersion_of_injective_appTop`: the statement above.
* `AlgebraicGeometry.exists_finset_isImmersion_of_range_appTop`: without injectivity, `g` is an
  immersion (an open immersion into the spectrum of the image, followed by a closed immersion).
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- A quasi-affine scheme is covered by finitely many affine basic opens of global sections. -/
theorem Scheme.exists_fin_isAffineOpen_basicOpen_iSup_eq_top (V : Scheme.{u})
    [V.IsQuasiAffine] :
    ∃ (n : ℕ) (b : Fin n → Γ(V, ⊤)), (∀ i, IsAffineOpen (V.basicOpen (b i))) ∧
      ⨆ i, V.basicOpen (b i) = ⊤ := by
  classical
  have hpt : ∀ x : V, ∃ g : Γ(V, ⊤), IsAffineOpen (V.basicOpen g) ∧ x ∈ V.basicOpen g := by
    intro x
    obtain ⟨g, haff, hx, -⟩ :=
      Stacks.AmpleCluster.exists_affine_basicOpen_of_finite_of_isQuasiAffine
      (X := V) (E := {x}) (Set.finite_singleton x) ⊤ (by simp)
    exact ⟨g, haff, hx rfl⟩
  choose g hgaff hgmem using hpt
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x => (V.basicOpen (g x) : Set V))
    (fun x => (V.basicOpen (g x)).isOpen) (fun x _ => Set.mem_iUnion.2 ⟨x, hgmem x⟩)
  refine ⟨t.card, fun i => g (t.equivFin.symm i), fun i => hgaff _, ?_⟩
  refine eq_top_iff.2 fun x _ => ?_
  obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ x))
  exact Opens.mem_iSup.2 ⟨t.equivFin ⟨y, hy⟩, by simpa using hxy⟩

/-- **The localization of an injective ring map at a generating element is bijective.**  Let
`φ : C ⟶ A` be injective, `c ∈ C` with `φ c = a`, and suppose `A_a` is generated, as an algebra
over a ring `R` mapping to `C`, by finitely many fractions whose numerators lie in the image of
`φ`.  Then `C_c ⟶ A_a` is bijective. -/
theorem bijective_awayMap_of_adjoin {R C A : Type u} [CommRing R] [CommRing C] [CommRing A]
    (ψ : R →+* C) (φ : C →+* A) (hφ : Function.Injective φ) (θ : R →+* A)
    (hθ : ∀ r, θ r = φ (ψ r)) (c : C) (T : Finset (Localization.Away (φ c)))
    (hT : letI : Algebra R (Localization.Away (φ c)) :=
        ((algebraMap A (Localization.Away (φ c))).comp θ).toAlgebra
      Algebra.adjoin R (T : Set (Localization.Away (φ c))) = ⊤)
    (hnum : ∀ t ∈ T, ∃ h ∈ Set.range φ, ∃ y : Submonoid.powers (φ c),
      t = IsLocalization.mk' (Localization.Away (φ c)) h y) :
    Function.Bijective (Localization.awayMap φ c) := by
  let : Algebra R (Localization.Away (φ c)) :=
    ((algebraMap A (Localization.Away (φ c))).comp θ).toAlgebra
  refine ⟨?_, ?_⟩
  · rw [Localization.awayMap_injective_iff]
    intro z hz
    exact ⟨0, by rw [hφ (hz.trans (map_zero φ).symm), mul_zero]⟩
  · let S' : Subalgebra R (Localization.Away (φ c)) :=
      { (Localization.awayMap φ c).range with
        algebraMap_mem' := fun r => by
          refine ⟨algebraMap C (Localization.Away c) (ψ r), ?_⟩
          show Localization.awayMap φ c (algebraMap C _ (ψ r)) =
            algebraMap A (Localization.Away (φ c)) (θ r)
          rw [hθ, Localization.awayMap, IsLocalization.Away.map, IsLocalization.map_eq] }
    have hle : (⊤ : Subalgebra R (Localization.Away (φ c))) ≤ S' := by
      rw [← hT, Algebra.adjoin_le_iff]
      intro t ht
      obtain ⟨_, ⟨h, rfl⟩, ⟨y, hy⟩, rfl⟩ := hnum t ht
      obtain ⟨N, rfl⟩ := (Submonoid.mem_powers_iff _ _).1 hy
      refine ⟨IsLocalization.mk' (Localization.Away c) h
        ⟨c ^ N, (Submonoid.mem_powers_iff _ _).2 ⟨N, rfl⟩⟩, ?_⟩
      show Localization.awayMap φ c _ = _
      rw [Localization.awayMap, IsLocalization.Away.map, IsLocalization.map_mk']
      congr 1
      exact Subtype.ext (map_pow φ c N)
    exact fun z => hle Algebra.mem_top

/-- **The ring-level form.**  Let `π : V ⟶ U` be locally of finite type, `V` quasi-affine and
`U` affine.  There is a finite set `s` of global functions on `V` such that for every ring `C`
under `Γ(U)` and every injective `Γ(U)`-algebra map `φ : C ⟶ Γ(V)` whose image contains `s`, the
composite `V ⟶ Spec Γ(V) ⟶ Spec C` is an open immersion. -/
theorem exists_finset_isOpenImmersion_toSpecΓ_comp_specMap {V U : Scheme.{u}} (π : V ⟶ U)
    [IsAffine U] [V.IsQuasiAffine] [LocallyOfFiniteType π] :
    ∃ s : Finset Γ(V, ⊤), ∀ {C : CommRingCat.{u}} (ψ : Γ(U, ⊤) ⟶ C) (φ : C ⟶ Γ(V, ⊤)),
      ψ ≫ φ = π.appTop → Function.Injective φ →
        (s : Set Γ(V, ⊤)) ⊆ Set.range φ → IsOpenImmersion (V.toSpecΓ ≫ Spec.map φ) := by
  classical
  obtain ⟨n, b, hbaff, hbcov⟩ := V.exists_fin_isAffineOpen_basicOpen_iSup_eq_top
  -- the localizations `Γ(V)_{b_i}` are of finite type over `Γ(U)`
  let alg : ∀ i, Algebra Γ(U, ⊤) (Localization.Away (b i)) := fun i =>
    ((algebraMap Γ(V, ⊤) (Localization.Away (b i))).comp π.appTop.hom).toAlgebra
  have hft : ∀ i, @Algebra.FiniteType Γ(U, ⊤) (Localization.Away (b i)) _ _ (alg i) := by
    intro i
    have hloc : IsLocalization.Away (b i) Γ(V, V.basicOpen (b i)) :=
      isLocalization_basicOpen_of_qcqs isCompact_univ isQuasiSeparated_univ (b i)
    let e : Γ(V, V.basicOpen (b i)) ≃+* Localization.Away (b i) :=
      (IsLocalization.algEquiv (Submonoid.powers (b i)) Γ(V, V.basicOpen (b i))
        (Localization.Away (b i))).toRingEquiv
    have happle : RingHom.FiniteType (π.appLE ⊤ (V.basicOpen (b i)) le_top).hom :=
      HasRingHomProperty.appLE (P := @LocallyOfFiniteType) π inferInstance
        ⟨⊤, isAffineOpen_top U⟩ ⟨_, hbaff i⟩ le_top
    have hcomp : (e : Γ(V, V.basicOpen (b i)) →+* Localization.Away (b i)).comp
        (π.appLE ⊤ (V.basicOpen (b i)) le_top).hom =
          (algebraMap Γ(V, ⊤) (Localization.Away (b i))).comp π.appTop.hom := by
      ext x
      simp only [RingHom.comp_apply, Scheme.Hom.appLE, CommRingCat.hom_comp, e]
      exact IsLocalization.algEquiv_apply _ _ _ _ |>.trans
        (IsLocalization.map_eq (S := Γ(V, V.basicOpen (b i))) _ _)
    have : RingHom.FiniteType
        ((algebraMap Γ(V, ⊤) (Localization.Away (b i))).comp π.appTop.hom) := by
      rw [← hcomp]
      exact RingHom.FiniteType.comp_surjective happle e.surjective
    exact this
  have hfg : ∀ i, ∃ T : Finset (Localization.Away (b i)),
      @Algebra.adjoin Γ(U, ⊤) _ _ _ (alg i) (T : Set (Localization.Away (b i))) = ⊤ :=
    fun i => (hft i).out
  choose T hT using hfg
  have hsurj : ∀ i (t : Localization.Away (b i)), ∃ (r : Γ(V, ⊤)) (m : Submonoid.powers (b i)),
      IsLocalization.mk' (Localization.Away (b i)) r m = t := fun i t => by
    obtain ⟨⟨r, m⟩, h⟩ := IsLocalization.mk'_surjective (Submonoid.powers (b i)) t
    exact ⟨r, m, h⟩
  choose x y hxy using hsurj
  refine ⟨Finset.univ.image b ∪ Finset.univ.biUnion (fun i => (T i).image (x i)), ?_⟩
  intro C ψ φ hq hinj hs
  have hb : ∀ i, b i ∈ Set.range φ := fun i =>
    hs (Finset.mem_union_left _ (Finset.mem_image_of_mem b (Finset.mem_univ i)))
  have hx : ∀ i, ∀ t ∈ T i, x i t ∈ Set.range φ := fun i t ht =>
    hs (Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨i, Finset.mem_univ i,
      Finset.mem_image_of_mem (x i) ht⟩))
  choose c hc using hb
  have hθ : ∀ r, π.appTop.hom r = φ.hom (ψ.hom r) := fun r => by
    rw [← hq]
    rfl
  have hloc : ∀ i, Function.Bijective (Localization.awayMap φ.hom (c i)) := by
    intro i
    have key : ∀ (a : Γ(V, ⊤)), φ.hom (c i) = a →
        ∀ (T' : Finset (Localization.Away a)),
          (let _ : Algebra Γ(U, ⊤) (Localization.Away a) :=
            ((algebraMap Γ(V, ⊤) (Localization.Away a)).comp π.appTop.hom).toAlgebra
          Algebra.adjoin Γ(U, ⊤) (T' : Set (Localization.Away a)) = ⊤) →
        (∀ t ∈ T', ∃ h ∈ Set.range φ.hom, ∃ y : Submonoid.powers a,
          t = IsLocalization.mk' (Localization.Away a) h y) →
        Function.Bijective (Localization.awayMap φ.hom (c i)) := by
      rintro a rfl T' hT' hnum'
      exact bijective_awayMap_of_adjoin ψ.hom φ.hom hinj π.appTop.hom hθ (c i)
        T' hT' hnum'
    exact key (b i) (hc i) (T i) (hT i) fun t ht => ⟨x i t, hx i t ht, y i t, (hxy i t).symm⟩
  have hcart : IsPullback (CommRingCat.ofHom (RingHom.id C))
      (CommRingCat.ofHom φ.hom) (CommRingCat.ofHom φ.hom)
      (CommRingCat.ofHom (RingHom.id Γ(V, ⊤))) := by
    rw [CommRingCat.ofHom_id, CommRingCat.ofHom_id]
    exact IsPullback.of_horiz_isIso ⟨by simp⟩
  exact isOpenImmersion_toSpecΓ_comp' b hbcov (Spec.map φ)
    (isOpenImmersion_iSup_basicOpen_comp_SpecMap_of_isPullback φ.hom (RingHom.id C) φ.hom
      (RingHom.id Γ(V, ⊤)) hcart b c (fun i => (hc i).symm) hloc)

/-- **Finitely many global functions make a quasi-affine scheme of finite type over an affine
scheme an open subscheme of every spectrum containing them.**  Let `π : V ⟶ U` be locally of
finite type, `V` quasi-affine and `U` affine.  There is a finite set `s` of global functions on
`V` such that every morphism `g : V ⟶ P` over `U` to an affine scheme `P` whose map on global
functions is injective with image containing `s` is an open immersion. -/
theorem exists_finset_isOpenImmersion_of_injective_appTop {V U : Scheme.{u}} (π : V ⟶ U)
    [IsAffine U] [V.IsQuasiAffine] [LocallyOfFiniteType π] :
    ∃ s : Finset Γ(V, ⊤), ∀ {P : Scheme.{u}} [IsAffine P] (q : P ⟶ U) (g : V ⟶ P),
      g ≫ q = π → Function.Injective g.appTop →
        (s : Set Γ(V, ⊤)) ⊆ Set.range g.appTop → IsOpenImmersion g := by
  obtain ⟨s, hs⟩ := exists_finset_isOpenImmersion_toSpecΓ_comp_specMap π
  refine ⟨s, fun {P} _ q g hq hinj hsr => ?_⟩
  have : IsOpenImmersion (g ≫ P.toSpecΓ) := by
    rw [Scheme.toSpecΓ_naturality]
    exact hs (C := Γ(P, ⊤)) q.appTop g.appTop (by rw [← hq, Scheme.Hom.comp_appTop]) hinj hsr
  exact IsOpenImmersion.of_comp g P.toSpecΓ

/-- **Finitely many global functions make a quasi-affine scheme of finite type over an affine
scheme a locally closed subscheme of every spectrum whose functions reach them.**  Let
`π : V ⟶ U` be locally of finite type, `V` quasi-affine and `U` affine.  There is a finite set `s`
of global functions on `V` such that every morphism `g : V ⟶ P` over `U` to an affine scheme `P`
whose map on global functions has image containing `s` is an immersion: it is an open immersion
into the spectrum of that image followed by the closed immersion of that spectrum. -/
theorem exists_finset_isImmersion_of_range_appTop {V U : Scheme.{u}} (π : V ⟶ U)
    [IsAffine U] [V.IsQuasiAffine] [LocallyOfFiniteType π] :
    ∃ s : Finset Γ(V, ⊤), ∀ {P : Scheme.{u}} [IsAffine P] (q : P ⟶ U) (g : V ⟶ P),
      g ≫ q = π → (s : Set Γ(V, ⊤)) ⊆ Set.range g.appTop → IsImmersion g := by
  obtain ⟨s, hs⟩ := exists_finset_isOpenImmersion_toSpecΓ_comp_specMap π
  refine ⟨s, fun {P} _ q g hq hsr => ?_⟩
  let R' : CommRingCat.{u} := CommRingCat.of g.appTop.hom.range
  let φ : R' ⟶ Γ(V, ⊤) := CommRingCat.ofHom g.appTop.hom.range.subtype
  let ρ : Γ(P, ⊤) ⟶ R' := CommRingCat.ofHom g.appTop.hom.rangeRestrict
  have hfac : ρ ≫ φ = g.appTop := CommRingCat.hom_ext (RingHom.ext fun _ => rfl)
  have h2 : IsOpenImmersion (V.toSpecΓ ≫ Spec.map φ) := by
    refine hs (q.appTop ≫ ρ) φ ?_ Subtype.val_injective ?_
    · rw [Category.assoc, hfac, ← hq, Scheme.Hom.comp_appTop]
    · intro t ht
      obtain ⟨a, ha⟩ := hsr ht
      exact ⟨⟨g.appTop a, a, rfl⟩, ha⟩
  have hcl : IsClosedImmersion (Spec.map ρ) :=
    IsClosedImmersion.spec_of_surjective _ (RingHom.rangeRestrict_surjective g.appTop.hom)
  have : IsImmersion (g ≫ P.toSpecΓ) := by
    rw [Scheme.toSpecΓ_naturality, ← hfac, Spec.map_comp, ← Category.assoc]
    exact IsImmersion.comp _ _
  have hg : g = (g ≫ P.toSpecΓ) ≫ inv P.toSpecΓ := by
    rw [Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  rw [hg]
  exact IsImmersion.comp _ _

end AlgebraicGeometry
