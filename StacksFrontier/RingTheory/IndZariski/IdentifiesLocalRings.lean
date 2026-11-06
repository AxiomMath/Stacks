module

public import Mathlib.RingTheory.Localization.LocalizationLocalization
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import StacksFrontier.RingTheory.IndZariski.Defs
public import StacksFrontier.RingTheory.LocalIso.IdentifiesLocalRings

import StacksCore.Tactic.StacksAttribute

/-!
# Ind-Zariski ring maps identify local rings

An ind-Zariski ring map `A → B` (Definition 096N, `Algebra.IsIndZariski`) identifies local
rings (Definition 096E part (2), `Algebra.IdentifiesLocalRings`): for every prime `𝔮` of `B`
the canonical map `A_{𝔮 ∩ A} → B_𝔮` is bijective.

## Main results

* `Algebra.IsLocalIso.identifiesLocalRings`: a local isomorphism identifies local rings.
* `Algebra.identifiesLocalRings_of_ind_localIso`: an algebra that is a filtered colimit of
  local isomorphisms identifies local rings, for an arbitrary index universe.
* `Algebra.IdentifiesLocalRings.of_isIndZariski`: Lemma 096T, an ind-Zariski algebra
  identifies local rings, with the base and the algebra in independent universes.

## Implementation notes

The source omits the proof. It is built here in two steps.

The first step is that a *local isomorphism* identifies local rings. Unfolding
`Algebra.IsLocalIso`, a prime `𝔮` of `S` has some `g ∉ 𝔮` with `A → S_g` a standard open
immersion, that is a localization of `A` away from a single element `a`. Localizing `S_g`
at the prime of `S_g` lying under `𝔮` therefore computes both `S_𝔮` — because localizing at
`𝔮` factors through the inversion of `g` — and `A_{𝔮 ∩ A}` — by
`IsLocalization.localizationLocalizationAtPrimeIsoLocalization`, a localization of a
localization being a localization. The two identifications compose to a ring isomorphism
`A_{𝔮 ∩ A} ≃ S_𝔮`, and `Localization.localRingHom_unique` identifies it with the canonical
map, since both agree on the image of `A`.

The second step is stability under filtered colimits, and is where the maps of the colimit
are used rather than just the objects. Writing `φᵢ : Bᵢ → B` for the colimit maps and `𝔮ᵢ` for
the preimage of `𝔮` in `Bᵢ`, step one turns every comparison `A_{𝔮 ∩ A} → (Bᵢ)_{𝔮ᵢ}` into an
isomorphism `Eᵢ`. The maps `Eᵢ⁻¹ ∘ (Bᵢ → (Bᵢ)_{𝔮ᵢ})` are compatible with the transition maps
of the diagram, so they assemble, by the universal property of the colimit, into an
`A`-algebra map `B → A_{𝔮 ∩ A}` — transported into `(B_{i₀})_{𝔮_{i₀}}` for a fixed index `i₀`
only so that the elements inverted by the localization at `𝔮` become invertible, which is
checked on a representative at a stage. The resulting map `B_𝔮 → A_{𝔮 ∩ A}` is a two-sided
inverse of the canonical map, both identities being checked on the image of `A`,
respectively of `B`, by `IsLocalization.ringHom_ext`.

That filtered colimits of sets are computed stage-wise is not used through the forgetful
functor of `CommAlgCat`, for which Mathlib has no such instance; `exists_ι_app_eq` instead
exhibits the set of elements of `B` coming from a stage as an `A`-subalgebra `D ⊆ B`, which
receives a cocone, hence a retraction `B → D` of the inclusion, forcing `D = B`.

Universes. `Algebra.identifiesLocalRings_of_ind_localIso` is stated with the index universe
of the filtered colimit *free*, which is strictly more general than the pinned convention of
`Algebra.IsIndZariski` and is what lets Lemma 096T be deduced at the pinned index universe
`max u v`; the lifted target of `Algebra.IsIndZariski` is then brought back to `B` along
`ULift.algEquiv`.

## References

* [Stacks Project, Tag 096T](https://stacks.math.columbia.edu/tag/096T)
* [Stacks Project, Tag 096N](https://stacks.math.columbia.edu/tag/096N)
* [Stacks Project, Tag 096E](https://stacks.math.columbia.edu/tag/096E)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v w

/-- **A local isomorphism identifies local rings.** At a prime `q` of `S` choose `g ∉ q` with
`A → S_g` a standard open immersion, hence a localization of `A` away from one element. The
localization of `S_g` at the prime below `q` is then simultaneously the localization of `S` at
`q` and the localization of `A` at `q ∩ A`. -/
theorem Algebra.IsLocalIso.identifiesLocalRings {A S : Type*} [CommRing A] [CommRing S]
    [Algebra A S] [Algebra.IsLocalIso A S] : Algebra.IdentifiesLocalRings A S := by
  intro q hq
  set p := q.comap (algebraMap A S)
  have hp : p.IsPrime := Ideal.comap_isPrime (algebraMap A S) q
  obtain ⟨g, hgq, hg⟩ := Algebra.IsLocalIso.exists_notMem_isStandardOpenImmersion (R := A) q
  -- `T = S_g` is a standard open immersion over `A`, and `q` lies in its image on spectra.
  let T := Localization.Away g
  obtain ⟨r, hr⟩ : (⟨q, hq⟩ : PrimeSpectrum S) ∈
      Set.range (PrimeSpectrum.comap (algebraMap S T)) := by
    rw [PrimeSpectrum.localization_away_comap_range T g]
    exact hgq
  let qT : Ideal T := r.asIdeal
  have hqT : qT.IsPrime := r.isPrime
  have hqTbase : qT.comap (algebraMap S T) = q := by
    simpa [qT] using congrArg PrimeSpectrum.asIdeal hr
  -- `U = A_a` is the same ring as `T`, presented as a localization of `A`.
  obtain ⟨a, ha⟩ := Algebra.IsStandardOpenImmersion.exists_away A T
  let U := Localization.Away a
  have _ : IsLocalization.Away a T := ha
  let e : T ≃ₐ[A] U := IsLocalization.algEquiv (.powers a) T U
  let qU : Ideal U := qT.comap e.symm.toRingHom
  have hqU : qT = qU.comap e.toRingHom := by
    ext x
    simp [qU, Ideal.mem_comap]
  have hpu : p = qU.comap (algebraMap A U) := by
    ext x
    show algebraMap A S x ∈ q ↔ algebraMap A U x ∈ qU
    rw [← hqTbase]
    simp [qU, IsScalarTower.algebraMap_apply A S T]
  have hqUprime : qU.IsPrime := Ideal.comap_isPrime e.symm.toRingHom qT
  let e₁ : Localization.AtPrime qT ≃ₐ[A] Localization.AtPrime qU :=
    Localization.localAlgEquiv qT qU e hqU
  -- `U_{qU}` is the localization of `A` at `qU ∩ A`, which is `p`.
  let e₂ := IsLocalization.localizationLocalizationAtPrimeIsoLocalization (.powers a) qU
  set p' : Ideal A := qU.comap (algebraMap A U)
  have hp' : p'.IsPrime := Ideal.comap_isPrime (algebraMap A U) qU
  have hpu' : p = p'.comap (RingEquiv.refl A) :=
    hpu.trans (by ext x; simp)
  let c₂ : Localization.AtPrime p ≃+* Localization.AtPrime p' :=
    Localization.localRingEquiv p p' (RingEquiv.refl A) hpu'
  -- `T_{qT}` is the localization of `S` at `qT ∩ S`, which is `q`.
  have _ : IsScalarTower A S (Localization.AtPrime qT) := IsScalarTower.of_algebraMap_eq' rfl
  let e₃ := IsLocalization.localizationLocalizationAtPrimeIsoLocalization (.powers g) qT
  set qS : Ideal S := qT.comap (algebraMap S T)
  have _ : qS.IsPrime := Ideal.comap_isPrime (algebraMap S T) qT
  have hqS' : q = qS.comap (RingEquiv.refl S) :=
    hqTbase.symm.trans (by ext x; simp)
  let c₃ : Localization.AtPrime q ≃+* Localization.AtPrime qS :=
    Localization.localRingEquiv q qS (RingEquiv.refl S) hqS'
  -- The composite `A_p ≃ A_{p'} ≃ U_{qU} ≃ T_{qT}` is a map of `A`-algebras.
  let F : Localization.AtPrime p ≃+* Localization.AtPrime qT :=
    c₂.trans (e₂.toRingEquiv.trans e₁.symm.toRingEquiv)
  have hF (x : A) : F (algebraMap A (Localization.AtPrime p) x) =
      algebraMap A (Localization.AtPrime qT) x := by
    show e₁.symm (e₂ (c₂ (algebraMap A (Localization.AtPrime p) x))) = _
    rw [show c₂ (algebraMap A (Localization.AtPrime p) x) =
        algebraMap A (Localization.AtPrime p') x from
      Localization.localRingHom_to_map p p' (RingEquiv.refl A) hpu' x, e₂.commutes,
      e₁.symm.commutes]
  -- The composite `T_{qT} ≃ S_{qS} ≃ S_q` is a map of `S`-algebras.
  let G : Localization.AtPrime qT ≃+* Localization.AtPrime q :=
    e₃.symm.toRingEquiv.trans c₃.symm
  have hG (z : S) : G (algebraMap S (Localization.AtPrime qT) z) =
      algebraMap S (Localization.AtPrime q) z := by
    show c₃.symm (e₃.symm (algebraMap S (Localization.AtPrime qT) z)) = _
    rw [e₃.symm.commutes]
    refine c₃.injective ?_
    rw [c₃.apply_symm_apply]
    exact (Localization.localRingHom_to_map q qS (RingEquiv.refl S) hqS' z).symm
  let ee : Localization.AtPrime p ≃+* Localization.AtPrime q := F.trans G
  have hh : Localization.localRingHom p q (algebraMap A S) rfl = ee.toRingHom := by
    refine Localization.localRingHom_unique p q (algebraMap A S) rfl fun x ↦ ?_
    show G (F (algebraMap A (Localization.AtPrime p) x)) = _
    rw [hF, IsScalarTower.algebraMap_apply A S (Localization.AtPrime qT) x, hG]
  rw [hh]
  exact ee.toEquiv.bijective

/-- Every element of a filtered colimit of commutative algebras comes from a stage. The subset
of such elements is an `A`-subalgebra `D` of the colimit which receives a cocone on the
diagram, hence a map from the colimit splitting the inclusion of `D`; so `D` is everything. -/
private theorem Algebra.exists_ι_app_eq {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    [Algebra A B] {J : Type w} [SmallCategory J] [IsFiltered J]
    (pres : ColimitPresentation J (CommAlgCat.of A B)) (b : B) :
    ∃ i x, (pres.ι.app i).hom x = b := by
  classical
  let φ (i : J) : pres.diag.obj i →ₐ[A] B := (pres.ι.app i).hom
  have hnat {i j : J} (f : i ⟶ j) (x : pres.diag.obj i) :
      φ i x = φ j ((pres.diag.map f).hom x) := by
    simp [φ]
  let D : Subalgebra A B :=
    { carrier := {y | ∃ i : J, ∃ x : pres.diag.obj i, φ i x = y}
      add_mem' := by
        rintro _ _ ⟨i, xi, rfl⟩ ⟨j, yj, rfl⟩
        obtain ⟨k, f, g, _⟩ := IsFilteredOrEmpty.cocone_objs i j
        exact ⟨k, (pres.diag.map f).hom xi + (pres.diag.map g).hom yj,
          (map_add (φ k) _ _).trans (by rw [← hnat f, ← hnat g])⟩
      mul_mem' := by
        rintro _ _ ⟨i, xi, rfl⟩ ⟨j, yj, rfl⟩
        obtain ⟨k, f, g, _⟩ := IsFilteredOrEmpty.cocone_objs i j
        exact ⟨k, (pres.diag.map f).hom xi * (pres.diag.map g).hom yj,
          (map_mul (φ k) _ _).trans (by rw [← hnat f, ← hnat g])⟩
      algebraMap_mem' := fun a ↦
        let i : J := Classical.choice (IsFiltered.nonempty (C := J))
        ⟨i, algebraMap A (pres.diag.obj i) a, (φ i).commutes a⟩ }
  let coc : Cocone pres.diag :=
    { pt := CommAlgCat.of A D
      ι :=
        { app := fun i ↦ CommAlgCat.ofHom ((φ i).codRestrict D (⟨i, ·, rfl⟩))
          naturality := by
            intro i j f
            refine CommAlgCat.hom_ext ?_
            ext x
            exact Subtype.ext (congrArg (fun h ↦ h x) (pres.ι.naturality f)) } }
  let desc := pres.isColimit.desc coc
  have hcat : CommAlgCat.ofHom (D.val.comp desc.hom) = CommAlgCat.ofHom (AlgHom.id A B) := by
    refine pres.isColimit.hom_ext fun i ↦ CommAlgCat.hom_ext ?_
    ext x
    show D.val (desc.hom (φ i x)) = φ i x
    have hfac' : desc.hom (φ i x) = (φ i).codRestrict D (fun x ↦ ⟨i, x, rfl⟩) x := by
      simpa [desc, coc] using congrArg (fun h ↦ h x) (pres.isColimit.fac coc i)
    rw [hfac']
    exact AlgHom.coe_codRestrict (φ i) D (fun x ↦ ⟨i, x, rfl⟩) x
  have hdesc : D.val.comp desc.hom = AlgHom.id A B :=
    AlgHom.ext fun x ↦ congrArg (fun h ↦ h x) (congrArg CommAlgCat.Hom.hom hcat)
  have hb : (desc b).val = b := by
    simpa using AlgHom.congr_fun hdesc b
  obtain ⟨i, x, hx⟩ := (desc b).property
  exact ⟨i, x, hx.trans hb⟩

/-- **An algebra presented as a filtered colimit of local isomorphisms identifies local
rings.** The index universe of the colimit is arbitrary. -/
theorem Algebra.identifiesLocalRings_of_ind_localIso (A : Type u) (B : Type v) [CommRing A]
    [CommRing B] [Algebra A B]
    (h : (CommAlgCat.localIso.{u, v} A).ind.{w} (CommAlgCat.of A B)) :
    Algebra.IdentifiesLocalRings A B := by
  intro q hq
  classical
  obtain ⟨J, hJsmall, hJfiltered, pres, hstage⟩ := h
  let φ (i : J) : pres.diag.obj i →ₐ[A] B := (pres.ι.app i).hom
  set p : Ideal A := q.comap (algebraMap A B)
  have hp : p.IsPrime := Ideal.comap_isPrime (algebraMap A B) q
  let qi (i : J) : Ideal (pres.diag.obj i) := q.comap (φ i).toRingHom
  have hqi (i : J) : (qi i).IsPrime := Ideal.comap_isPrime (φ i).toRingHom q
  have hpi (i : J) : p = (qi i).comap (algebraMap A (pres.diag.obj i)) := by
    ext a
    show algebraMap A B a ∈ q ↔ φ i (algebraMap A (pres.diag.obj i) a) ∈ q
    simp [φ]
  let fA (i : J) : A →ₐ[A] pres.diag.obj i := Algebra.ofId A (pres.diag.obj i)
  -- Step one applied at each stage: the comparison `A_p → (B i)_{q i}` is an isomorphism.
  let ei (i : J) : Localization.AtPrime p →ₐ[A] Localization.AtPrime (qi i) :=
    Localization.localAlgHom p (qi i) (fA i) (hpi i)
  have hei_bij (i : J) : Function.Bijective (ei i) := by
    have _ : Algebra.IsLocalIso A (pres.diag.obj i) := hstage i
    have _ : IsScalarTower A (pres.diag.obj i) (Localization.AtPrime (qi i)) :=
      IsScalarTower.of_algebraMap_eq' rfl
    have hbi := Algebra.IsLocalIso.identifiesLocalRings (A := A) (S := pres.diag.obj i) (qi i)
    set pᵢ := (qi i).comap (algebraMap A (pres.diag.obj i))
    have hpᵢ : pᵢ.IsPrime := Ideal.comap_isPrime (algebraMap A (pres.diag.obj i)) (qi i)
    let c : Localization.AtPrime p ≃ₐ[A] Localization.AtPrime pᵢ :=
      Localization.localAlgEquiv p pᵢ (AlgEquiv.refl : A ≃ₐ[A] A) (by
        show p = pᵢ; exact hpi i)
    let l : Localization.AtPrime pᵢ →ₐ[A] Localization.AtPrime (qi i) :=
      Localization.localAlgHom pᵢ (qi i) (fA i) rfl
    have hl : Function.Bijective l := hbi
    have heq : l.comp c.toAlgHom = ei i :=
      IsLocalization.algHom_ext p.primeCompl (Subsingleton.elim _ _)
    rw [← heq]
    exact hl.comp c.bijective
  let Ei (i : J) : Localization.AtPrime p ≃ₐ[A] Localization.AtPrime (qi i) :=
    AlgEquiv.ofBijective (ei i) (hei_bij i)
  let inc (i : J) : pres.diag.obj i →ₐ[A] Localization.AtPrime (qi i) :=
    { toRingHom := algebraMap (pres.diag.obj i) (Localization.AtPrime (qi i))
      commutes' := fun a ↦ by
        simp [IsScalarTower.algebraMap_apply A (pres.diag.obj i) (Localization.AtPrime (qi i))] }
  let vi (i : J) : Localization.AtPrime (qi i) →ₐ[A] Localization.AtPrime q :=
    Localization.localAlgHom (qi i) q (φ i) rfl
  have hvi (i : J) : (vi i).comp (Ei i).toAlgHom =
      Localization.localAlgHom p q (Algebra.ofId A B) rfl :=
    IsLocalization.algHom_ext p.primeCompl (Subsingleton.elim _ _)
  -- The inverted stage comparisons are compatible with the transition maps of the diagram.
  let ψ (i : J) : pres.diag.obj i →ₐ[A] Localization.AtPrime p :=
    (Ei i).symm.toAlgHom.comp (inc i)
  have hψ (i j : J) (f : i ⟶ j) : (ψ j).comp (pres.diag.map f).hom = ψ i := by
    refine AlgHom.ext fun x ↦ ?_
    let u : pres.diag.obj i →ₐ[A] pres.diag.obj j := (pres.diag.map f).hom
    have hqij : qi i = (qi j).comap u := by
      ext y
      show φ i y ∈ q ↔ φ j (u y) ∈ q
      simp [u, φ]
    let vij : Localization.AtPrime (qi i) →ₐ[A] Localization.AtPrime (qi j) :=
      Localization.localAlgHom (qi i) (qi j) u hqij
    have hcomp : vij.comp (Ei i).toAlgHom = (Ei j).toAlgHom :=
      IsLocalization.algHom_ext p.primeCompl (Subsingleton.elim _ _)
    have hinc : vij (inc i x) = inc j (u x) := by
      simp [vij, inc, Localization.localAlgHom]
    show (Ei j).symm ((inc j) (u x)) = (Ei i).symm ((inc i) x)
    rw [← hinc]
    simpa using congrArg (fun g : Localization.AtPrime p →ₐ[A] Localization.AtPrime (qi j) ↦
      (Ei j).symm (g ((Ei i).symm (inc i x)))) hcomp
  -- Assemble them, through a fixed stage, into a map out of the colimit.
  let i₀ : J := Classical.choice (IsFiltered.nonempty (C := J))
  let ψ₀ (i : J) : pres.diag.obj i →ₐ[A] Localization.AtPrime (qi i₀) :=
    (Ei i₀).toAlgHom.comp (ψ i)
  have hψ₀ (i j : J) (f : i ⟶ j) : (ψ₀ j).comp (pres.diag.map f).hom = ψ₀ i := by
    simpa [ψ₀, AlgHom.comp_assoc] using
      congrArg (fun g : pres.diag.obj i →ₐ[A] Localization.AtPrime p ↦
        (Ei i₀).toAlgHom.comp g) (hψ i j f)
  let coc : Cocone pres.diag :=
    { pt := CommAlgCat.of A (Localization.AtPrime (qi i₀))
      ι :=
        { app := fun i ↦ CommAlgCat.ofHom (ψ₀ i)
          naturality := by
            intro i j f
            refine CommAlgCat.hom_ext ?_
            ext x
            exact congrArg (fun g : pres.diag.obj i →ₐ[A] Localization.AtPrime (qi i₀) ↦ g x)
              (hψ₀ i j f) } }
  let descB : B →ₐ[A] Localization.AtPrime (qi i₀) := (pres.isColimit.desc coc).hom
  have hdescFac (i : J) (x : pres.diag.obj i) : descB (φ i x) = ψ₀ i x := by
    simpa [descB, coc] using congrArg (fun g ↦ g x) (pres.isColimit.fac coc i)
  have hunit (s : q.primeCompl) : IsUnit (descB (s : B)) := by
    obtain ⟨i, x, hxrep⟩ := Algebra.exists_ι_app_eq pres (s : B)
    have hxs : φ i x ∉ q := by
      rw [hxrep]
      exact s.property
    have hx : x ∉ qi i := by simpa [qi] using hxs
    rw [← hxrep, hdescFac]
    show IsUnit ((Ei i₀) ((Ei i).symm (inc i x)))
    exact IsUnit.map (Ei i₀).toRingHom <| IsUnit.map (Ei i).symm.toRingHom
      (IsLocalization.map_units _ (⟨x, hx⟩ : (qi i).primeCompl))
  let gAlg₀ : Localization.AtPrime q →ₐ[A] Localization.AtPrime (qi i₀) :=
    { toRingHom := IsLocalization.lift hunit
      commutes' := fun a ↦ by
        show IsLocalization.lift hunit
          (algebraMap B (Localization.AtPrime q) (algebraMap A B a)) = _
        rw [IsLocalization.lift_eq]
        exact descB.commutes a }
  let gAlg : Localization.AtPrime q →ₐ[A] Localization.AtPrime p :=
    (Ei i₀).symm.toAlgHom.comp gAlg₀
  let f : Localization.AtPrime p →ₐ[A] Localization.AtPrime q :=
    Localization.localAlgHom p q (Algebra.ofId A B) rfl
  have hleft : gAlg.comp f = AlgHom.id A (Localization.AtPrime p) :=
    IsLocalization.algHom_ext p.primeCompl (Subsingleton.elim _ _)
  have hright : f.comp gAlg = AlgHom.id A (Localization.AtPrime q) := by
    refine IsLocalization.algHom_ext q.primeCompl ?_
    ext b
    obtain ⟨i, x, rfl⟩ := Algebra.exists_ι_app_eq pres b
    show f ((Ei i₀).symm (gAlg₀ (algebraMap B (Localization.AtPrime q) (φ i x)))) =
      algebraMap B (Localization.AtPrime q) (φ i x)
    calc f ((Ei i₀).symm (gAlg₀ (algebraMap B (Localization.AtPrime q) (φ i x))))
        = f ((Ei i₀).symm (ψ₀ i x)) := by
          congr 2
          exact (IsLocalization.lift_eq hunit _).trans (hdescFac i x)
      _ = f ((Ei i).symm (inc i x)) := by simp [ψ₀, ψ]
      _ = vi i (inc i x) := by
          simpa using (AlgHom.congr_fun (hvi i) ((Ei i).symm (inc i x))).symm
      _ = algebraMap B (Localization.AtPrime q) (φ i x) :=
          Localization.localRingHom_to_map (I := qi i) (J := q) (f := (φ i).toRingHom)
            (hIJ := rfl) x
  show Function.Bijective (Localization.localRingHom p q (algebraMap A B) rfl)
  have hf_eq : Localization.localRingHom p q (algebraMap A B) rfl = f := RingHom.ext fun _ ↦ rfl
  rw [hf_eq]
  exact (AlgEquiv.ofAlgHom f gAlg hright hleft).bijective

/-- **Stacks 096T.** An ind-Zariski algebra identifies local rings: for every prime `q` of `B`
the canonical map from the localization of `A` at the preimage of `q` to the localization of
`B` at `q` is bijective. -/
@[stacks 096T]
theorem Algebra.IdentifiesLocalRings.of_isIndZariski {A : Type u} {B : Type v} [CommRing A]
    [CommRing B] [Algebra A B] (h : Algebra.IsIndZariski A B) :
    Algebra.IdentifiesLocalRings A B := by
  intro q hq
  -- The presentation has target `ULift B`; transport the conclusion back along `ULift.algEquiv`.
  let e : ULift.{u} B ≃ₐ[A] B := ULift.algEquiv
  set q' : Ideal (ULift.{u} B) := q.comap e.toRingHom
  have _ : q'.IsPrime := Ideal.comap_isPrime e.toRingHom q
  have hbij := Algebra.identifiesLocalRings_of_ind_localIso A (ULift.{u} B) h q'
  let f : Localization.AtPrime (q.comap (algebraMap A B)) →ₐ[A] Localization.AtPrime q' :=
    Localization.localAlgHom _ q' (Algebra.ofId A (ULift.{u} B)) rfl
  let E : Localization.AtPrime q' ≃ₐ[A] Localization.AtPrime q :=
    Localization.localAlgEquiv q' q e rfl
  have hf : Localization.localRingHom (q.comap (algebraMap A B)) q (algebraMap A B) rfl =
      (E.toAlgHom.comp f).toRingHom := by
    refine Localization.localRingHom_unique _ _ _ _ fun a ↦ ?_
    show E (f (algebraMap A _ a)) = _
    rw [f.commutes, E.commutes]
    rfl
  rw [hf]
  exact E.bijective.comp hbij

end
