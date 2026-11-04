module

public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import StacksFrontier.RingTheory.Henselian.Pair.Henselization
public import StacksFrontier.RingTheory.Rig.HenselizationDescent

/-!
# The henselization at a maximal ideal, and at a finite intersection of them

For a maximal ideal `𝔪` of `R`, the henselization of the pair `(R, 𝔪)` is the henselization of
the pair `(R_𝔪, 𝔪 R_𝔪)`: every element outside `𝔪` already becomes a unit in `R^h_𝔪`, because
its image lies outside the Jacobson radical of the henselian pair, so `R → R^h_𝔪` factors
through the local ring and the two universal properties identify the two henselizations.

Combining this with `henselization_iInf_equiv_pi`, which decomposes the henselization at a
finite intersection of pairwise comaximal ideals, gives `R^h_{⋂ 𝔪 i} ≅ ∏ R^h_{𝔪 i}` with the
factors the henselizations of the *local rings*. This is the step the proof of **Stacks 0DZF**
records as "`P^h = ∏ P^h_{𝔪 i}`", obtained there "by looking at idempotents" and More on
Algebra, Lemma 15.11.6.

## Main results

* `exists_ringEquiv_henselization_localization_atMaximalIdeal`: the henselization of `(R, 𝔪)` is
  the henselization of `(R_𝔪, 𝔪 R_𝔪)`, compatibly with the maps out of `R`.
* `exists_ringEquiv_henselization_iInf_pi_localization`: the henselization of `R` at a finite
  intersection of distinct maximal ideals is the product of the henselizations of the local
  rings, compatibly with the maps out of `R`.

## Implementation notes

The equivalences are produced as existentials together with the characterisation of their
composite with `algebraMap`, rather than as named maps: the henselization is a colimit whose
structure maps are private, so the only handle on a map out of it is its universal property, and
that is what `henselization_ringHom_ext` below packages.

`henselization_iInf_equiv_pi` is stated for an index type in `Type`, so the family is reindexed
along `Fintype.equivFin` before it is applied and the result transported back; the empty case is
separate, the henselization of `(R, ⊤)` being the zero ring.

## References

* [Stacks Project, Tag 0DZF](https://stacks.math.columbia.edu/tag/0DZF)
* [Stacks Project, Tag 0A02](https://stacks.math.columbia.edu/tag/0A02)
* [Stacks Project, Tag 09XI](https://stacks.math.columbia.edu/tag/09XI)
-/

@[expose] public section

universe uι u

/-- **Two maps out of a henselization agree as soon as they agree on the ring.** This is the
uniqueness half of the universal property of `henselization R I`, read as an extensionality
principle. -/
public theorem henselization_ringHom_ext {R C : Type u} [CommRing R] [CommRing C]
    (I : Ideal R) (J : Ideal C) (hC : HenselianPair C J)
    (f g : (henselization R I : Type u) →+* C)
    (hf : I ≤ J.comap (f.comp (algebraMap R (henselization R I : Type u))))
    (hfg : f.comp (algebraMap R (henselization R I : Type u)) =
      g.comp (algebraMap R (henselization R I : Type u))) : f = g := by
  obtain ⟨a, ha, hu⟩ := henselization_universalProperty R I C inferInstance J hC
    (f.comp (algebraMap R (henselization R I : Type u))) hf
  have hf' : I.map (algebraMap R (henselization R I : Type u)) ≤ J.comap f := by
    rwa [Ideal.map_le_iff_le_comap, Ideal.comap_comap]
  have hg' : I.map (algebraMap R (henselization R I : Type u)) ≤ J.comap g := by
    rwa [Ideal.map_le_iff_le_comap, Ideal.comap_comap, ← hfg]
  exact (hu f ⟨rfl, hf'⟩).trans (hu g ⟨hfg.symm, hg'⟩).symm

/-- An element outside a maximal ideal `𝔪` becomes a unit under any map carrying `𝔪` into an
ideal contained in the Jacobson radical of the zero ideal. -/
public theorem isUnit_map_of_notMem_maximal {R C : Type*} [CommRing R] [CommRing C]
    (m : Ideal R) [m.IsMaximal] (J : Ideal C) (hJ : J ≤ (⊥ : Ideal C).jacobson) (f : R →+* C)
    (hf : m ≤ J.comap f) {s : R} (hs : s ∉ m) : IsUnit (f s) := by
  obtain ⟨r, a, ha, hra⟩ := Ideal.IsMaximal.exists_inv ‹m.IsMaximal› hs
  have hrel : f r * f s + f a = 1 := by
    simpa only [map_add, map_mul, map_one] using congrArg f hra
  have hmem : f r * f s - 1 ∈ (⊥ : Ideal C).jacobson := by
    rw [← hrel]
    simpa using Submodule.neg_mem _ (hJ (hf ha))
  exact (IsUnit.mul_iff.mp (Ideal.isUnit_of_sub_one_mem_jacobson_bot _ hmem)).2

/-- A self-map of a henselization that fixes the image of the ring is the identity. -/
private theorem henselization_ringHom_eq_id {R : Type u} [CommRing R] {I : Ideal R}
    {f : (henselization R I : Type u) →+* (henselization R I : Type u)}
    (hf : f.comp (algebraMap R (henselization R I : Type u)) =
      algebraMap R (henselization R I : Type u)) : f = RingHom.id _ :=
  henselization_ringHom_ext I _ (henselianPair_henselization R I) f _
    (by rw [hf]; exact Ideal.le_comap_map) (by rw [hf, RingHom.id_comp])

/-- **The henselization at a maximal ideal is the henselization of the local ring.** For a
maximal ideal `𝔪` of `R` there is a ring isomorphism from the henselization of the pair
`(R, 𝔪)` onto the henselization of the pair `(R_𝔪, 𝔪 R_𝔪)` compatible with the maps out of
`R`. -/
public theorem exists_ringEquiv_henselization_localization_atMaximalIdeal
    {R : Type u} [CommRing R] (m : Ideal R) [m.IsMaximal] :
    ∃ e : (henselization R m : Type u) ≃+*
        (henselization (Localization m.primeCompl)
          (IsLocalRing.maximalIdeal (Localization m.primeCompl)) : Type u),
      ∀ r : R, e (algebraMap R (henselization R m : Type u) r) =
        algebraMap (Localization m.primeCompl)
          (henselization (Localization m.primeCompl)
            (IsLocalRing.maximalIdeal (Localization m.primeCompl)) : Type u)
          (algebraMap R (Localization m.primeCompl) r) := by
  let L := Localization m.primeCompl
  let M := IsLocalRing.maximalIdeal L
  let H := (henselization R m : Type u)
  let K := (henselization L M : Type u)
  let J := m.map (algebraMap R H)
  let N := M.map (algebraMap L K)
  have hM : m.map (algebraMap R L) = M := IsLocalization.AtPrime.map_eq_maximalIdeal m L
  let c : R →+* K := (algebraMap L K).comp (algebraMap R L)
  have hc : m ≤ N.comap c := by
    rw [← Ideal.map_le_iff_le_comap, ← Ideal.map_map, hM]
  obtain ⟨f, hf, -⟩ := henselization_universalProperty R m K inferInstance N
    (henselianPair_henselization L M) c hc
  have hu (s : m.primeCompl) : IsUnit (algebraMap R H s) :=
    isUnit_map_of_notMem_maximal m J (henselianPair_henselization R m).1
      (algebraMap R H) Ideal.le_comap_map s.property
  let t : L →+* H := IsLocalization.lift hu
  have ht : t.comp (algebraMap R L) = algebraMap R H := IsLocalization.lift_comp hu
  have htM : M ≤ J.comap t := by
    rw [← hM, Ideal.map_le_iff_le_comap, Ideal.comap_comap, ht]
    exact Ideal.le_comap_map
  obtain ⟨g, hg, -⟩ := henselization_universalProperty L M H inferInstance J
    (henselianPair_henselization R m) t htM
  have hgf : g.comp f = RingHom.id H := by
    apply henselization_ringHom_eq_id
    rw [RingHom.comp_assoc, hf.1]
    show (g.comp (algebraMap L K)).comp (algebraMap R L) = algebraMap R H
    rw [hg.1, ht]
  have hft : f.comp t = algebraMap L K := by
    apply IsLocalization.ringHom_ext m.primeCompl
    rw [RingHom.comp_assoc, ht, hf.1]
  have hfg : f.comp g = RingHom.id K := by
    apply henselization_ringHom_eq_id
    rw [RingHom.comp_assoc, hg.1, hft]
  exact ⟨RingEquiv.ofBijective f
    (Function.bijective_iff_has_inverse.mpr
      ⟨g, DFunLike.congr_fun hgf, DFunLike.congr_fun hfg⟩), DFunLike.congr_fun hf.1⟩

/-- The henselization of a ring at the unit ideal is the zero ring. -/
private theorem subsingleton_henselization_of_eq_top {R : Type u} [CommRing R] {I : Ideal R}
    (hI : I = ⊤) : Subsingleton (henselization R I : Type u) := by
  subst hI
  have hbot : (⊥ : Ideal (henselization R ⊤ : Type u)) = ⊤ :=
    Ideal.jacobson_eq_top_iff.mp <| top_le_iff.mp <| by
      simpa only [Ideal.map_top] using (henselianPair_henselization R ⊤).1
  exact subsingleton_of_zero_eq_one (Ideal.mem_bot.mp ((Ideal.eq_top_iff_one _).mp hbot)).symm

/-- **The henselization at a finite intersection of distinct maximal ideals is the product of
the henselizations of the local rings.** This is the step the proof of Stacks 0DZF records as
"`P^h = ∏ P^h_{𝔪 i}`". -/
public theorem exists_ringEquiv_henselization_iInf_pi_localization
    {R : Type u} {ι : Type uι} [Finite ι] [CommRing R] (m : ι → Ideal R)
    (hmax : ∀ i, (m i).IsMaximal) (hinj : Function.Injective m) :
    ∃ e : (henselization R (⨅ i, m i) : Type u) ≃+*
        (∀ i, (henselization (Localization (m i).primeCompl)
          (IsLocalRing.maximalIdeal (Localization (m i).primeCompl)) : Type u)),
      ∀ (r : R) (i : ι), e (algebraMap R (henselization R (⨅ j, m j) : Type u) r) i =
          algebraMap (Localization (m i).primeCompl)
            (henselization (Localization (m i).primeCompl)
              (IsLocalRing.maximalIdeal (Localization (m i).primeCompl)) : Type u)
            (algebraMap R (Localization (m i).primeCompl) r) := by
  classical
  cases isEmpty_or_nonempty ι with
  | inl hι =>
    have := subsingleton_henselization_of_eq_top (R := R) (I := ⨅ i, m i) (by simp)
    exact ⟨RingEquiv.ofBijective (RingHom.pi fun i => isEmptyElim i)
      ⟨fun _ _ _ => Subsingleton.elim _ _, fun _ => ⟨0, Subsingleton.elim _ _⟩⟩,
      fun _ i => isEmptyElim i⟩
  | inr hι =>
    let := Fintype.ofFinite ι
    let b := Fintype.equivFin ι
    let I := fun j : Fin (Fintype.card ι) => m (b.symm j)
    let J := ⨅ i, m i
    let H := (henselization R J : Type u)
    have hI : ∀ i j, i ≠ j → I i ⊔ I j = ⊤ := by
      intro i j hij
      let := hmax (b.symm i)
      let := hmax (b.symm j)
      exact Ideal.isCoprime_iff_sup_eq.mp
        (Ideal.isCoprime_of_isMaximal fun h => hij (b.symm.injective (hinj h)))
    have hJ : (⨅ j, I j) = J := Equiv.iInf_comp (g := m) b.symm
    have hH : HenselianPair H ((⨅ j, I j).map (algebraMap R H)) := by
      rw [hJ]
      exact henselianPair_henselization R J
    obtain ⟨a, ha, -⟩ := henselization_iInf_equiv_pi R I hI H (algebraMap R H)
      ⟨hH, by
        intro C hC N hN f hf
        rw [hJ] at hf ⊢
        exact henselization_universalProperty R J C hC N hN f hf⟩
      (fun j => (henselization R (I j) : Type u))
      (fun j => algebraMap R (henselization R (I j) : Type u))
      (fun j => ⟨henselianPair_henselization R (I j), henselization_universalProperty R (I j)⟩)
    choose c hc using fun i =>
      have := hmax i
      exists_ringEquiv_henselization_localization_atMaximalIdeal (m i)
    let d := RingEquiv.piCongrLeft (fun i => (henselization R (m i) : Type u)) b.symm
    refine ⟨(a.trans d).trans (RingEquiv.piCongrRight c), ?_⟩
    intro r i
    show c i (d (a (algebraMap R H r)) i) = _
    rw [← hc i r]
    congr 1
    have har : a (algebraMap R H r) =
        fun j => algebraMap R (henselization R (I j) : Type u) r := funext (ha r)
    rw [har]
    simp only [d, RingEquiv.piCongrLeft_apply, I]
    have hcast {j i : ι} (h : j = i) :
        (h ▸ algebraMap R (henselization R (m j) : Type u) r) =
          algebraMap R (henselization R (m i) : Type u) r := by
      subst i
      rfl
    exact hcast _

end
