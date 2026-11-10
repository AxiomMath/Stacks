module

public import StacksFrontier.AlgebraicGeometry.Morphisms.RingMapProperty.Defs
public import Mathlib.RingTheory.Localization.LocalizationLocalization

/-!
# Inducing isomorphisms on local rings

A ring homomorphism `f : R → S` induces, at every prime `q` of `S`, a map from the local ring
of `R` at the contracted prime to the local ring of `S` at `q`. The property that all of these
maps are isomorphisms is local, is stable under base change, and is stable under composition.

## Main results

* `RingHom.localRingHom_bijective_propertyIsLocal` states locality of the property.
* `RingHom.localRingHom_bijective_isStableUnderBaseChange` states stability under base change.
* `RingHom.localRingHom_bijective_stableUnderComposition` states stability under composition.

## Implementation notes

The induced map on local rings is Mathlib's `Localization.localRingHom`. Bijectivity of its
underlying function expresses that it is a ring isomorphism. The three statements spell the
property out inline, so that each reads independently of the others; the auxiliary
`RingHom.LocalRingIso` abbreviation names it for the base-change proof.

## References

* [Stacks Project, Tag 01SX](https://stacks.math.columbia.edu/tag/01SX)
* [Stacks Project, Tag 01SY](https://stacks.math.columbia.edu/tag/01SY)
* [Stacks Project, Tag 01SZ](https://stacks.math.columbia.edu/tag/01SZ)
-/

@[expose] public section

open scoped TensorProduct

universe u

namespace RingHom

/-- A ring homomorphism induces an isomorphism on the local rings at every prime of its
target. -/
abbrev LocalRingIso :
    ∀ {R S : Type u} [CommRing R] [CommRing S], (R →+* S) → Prop :=
  fun {_ S} _ _ f ↦ ∀ (q : Ideal S) [q.IsPrime],
    Function.Bijective (Localization.localRingHom (Ideal.comap f q) q f rfl)

/-- The canonical map to a localization induces isomorphisms on local rings. -/
private lemma localRingHom_bijective_algebraMap_of_isLocalization
    {R S : Type u} [CommRing R] [CommRing S] (M : Submonoid R)
    [Algebra R S] [IsLocalization M S] (q : Ideal S) [q.IsPrime] :
    Function.Bijective
      (Localization.localRingHom (q.comap (algebraMap R S)) q (algebraMap R S) rfl) := by
  let p := q.comap (algebraMap R S)
  have : IsLocalization.AtPrime (Localization.AtPrime q) p :=
    IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
      M (Localization.AtPrime q) q
  let e : Localization.AtPrime p ≃ₐ[R] Localization.AtPrime q :=
    IsLocalization.algEquiv p.primeCompl _ _
  have he : Localization.localRingHom p q (algebraMap R S) rfl = e.toRingHom :=
    Localization.localRingHom_unique _ _ _ _ fun x ↦ e.commutes x
  rw [he]
  exact e.toRingEquiv.bijective

/-- The preceding lemma, with the prime of the source given by an equation rather than
syntactically as a contraction. -/
private lemma localRingHom_bijective_algebraMap_of_isLocalization_at
    {R S : Type u} [CommRing R] [CommRing S] (M : Submonoid R)
    [Algebra R S] [IsLocalization M S] {I : Ideal R} [I.IsPrime]
    (q : Ideal S) [q.IsPrime] (hI : I = q.comap (algebraMap R S)) :
    Function.Bijective (Localization.localRingHom I q (algebraMap R S) hI) := by
  subst I
  exact localRingHom_bijective_algebraMap_of_isLocalization M q

/-- The map on local rings induced by a composite is the composite of the induced maps. -/
private lemma localRingHom_comp_atPrime
    {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
    (I : Ideal R) (J : Ideal S) (q : Ideal T) [I.IsPrime] [J.IsPrime] [q.IsPrime]
    (f : R →+* S) (hIJ : I = J.comap f) (g : S →+* T) (hJq : J = q.comap g) :
    Localization.localRingHom I q (g.comp f)
        (by rw [hIJ, hJq, Ideal.comap_comap]) =
      (Localization.localRingHom J q g hJq).comp
        (Localization.localRingHom I J f hIJ) := by
  subst J
  subst I
  simpa only [Ideal.comap_comap] using
    (Localization.localRingHom_comp ((q.comap g).comap f) (q.comap g) q f rfl g rfl)

/-- Bijectivity of an induced map on local rings depends only on the prime of the source, not
on how it is presented as a contraction. -/
private lemma localRingHom_bijective_congr {R S : Type u} [CommRing R] [CommRing S]
    {I I' : Ideal R} [I.IsPrime] [I'.IsPrime] {J : Ideal S} [J.IsPrime] {f : R →+* S}
    {hI : I = J.comap f} (hI' : I' = J.comap f)
    (h : Function.Bijective (Localization.localRingHom I J f hI)) :
    Function.Bijective (Localization.localRingHom I' J f hI') := by
  subst hI hI'
  exact h

/-- If two composable ring maps induce bijections on local rings, so does their composite. -/
private lemma localRingHom_bijective_comp
    {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
    (I : Ideal R) (J : Ideal S) (q : Ideal T) [I.IsPrime] [J.IsPrime] [q.IsPrime]
    (f : R →+* S) (g : S →+* T) (hIJ : I = J.comap f) (hJq : J = q.comap g)
    (hf : Function.Bijective (Localization.localRingHom I J f hIJ))
    (hg : Function.Bijective (Localization.localRingHom J q g hJq)) :
    Function.Bijective (Localization.localRingHom I q (g.comp f)
      (by rw [hIJ, hJq, Ideal.comap_comap])) := by
  rw [localRingHom_comp_atPrime I J q f hIJ g hJq, RingHom.coe_comp]
  exact hg.comp hf

/-- In a commutative square of ring maps, if three of the four induced maps on local rings at
a prime of the final target are bijective, so is the fourth. -/
private theorem localRingHom_bijective_of_square
    {R R' A A' : Type u} [CommRing R] [CommRing R'] [CommRing A] [CommRing A']
    (u : R →+* R') (f : R →+* A) (g : R' →+* A') (v : A →+* A')
    (h : g.comp u = v.comp f) (q : Ideal A') [q.IsPrime]
    (hu : Function.Bijective
      (Localization.localRingHom ((q.comap v).comap f) (q.comap g) u
        (by rw [Ideal.comap_comap, Ideal.comap_comap, h])))
    (hf : Function.Bijective
      (Localization.localRingHom ((q.comap v).comap f) (q.comap v) f rfl))
    (hv : Function.Bijective (Localization.localRingHom (q.comap v) q v rfl)) :
    Function.Bijective (Localization.localRingHom (q.comap g) q g rfl) := by
  have hI : (q.comap v).comap f = (q.comap g).comap u := by
    simpa only [Ideal.comap_comap] using
      congrArg (fun k : R →+* A' => Ideal.comap k q) h.symm
  have hcgu := localRingHom_comp_atPrime ((q.comap v).comap f) (q.comap g) q u hI g rfl
  have hcvf := localRingHom_comp_atPrime ((q.comap v).comap f) (q.comap v) q f rfl v rfl
  have hmaps :
      Localization.localRingHom ((q.comap v).comap f) q (g.comp u)
          (by rw [← Ideal.comap_comap, hI]) =
        Localization.localRingHom ((q.comap v).comap f) q (v.comp f)
          (by rw [Ideal.comap_comap]) :=
    Localization.localRingHom_unique _ _ _ _ fun x ↦ by simp [h]
  have htotal : (Localization.localRingHom (q.comap g) q g rfl).comp
        (Localization.localRingHom ((q.comap v).comap f) (q.comap g) u
          hI) =
      (Localization.localRingHom (q.comap v) q v rfl).comp
        (Localization.localRingHom ((q.comap v).comap f) (q.comap v) f rfl) :=
    hcgu.symm.trans (hmaps.trans hcvf)
  apply (Function.Bijective.of_comp_iff _ hu).mp
  change Function.Bijective ((Localization.localRingHom (q.comap g) q g rfl).comp
    (Localization.localRingHom ((q.comap v).comap f) (q.comap g) u hI))
  rw [htotal]
  simpa only [RingHom.coe_comp] using Function.Bijective.comp hv hf

/-- Isomorphisms on local rings are preserved by localizing at an element of the source. -/
private lemma localRingIso_localizationAwayPreserves :
    RingHom.LocalizationAwayPreserves @LocalRingIso := by
  intro R S _ _ f r R' S' _ _ _ _ hR hS hf
  let g := IsLocalization.Away.map R' S' f r
  have hsq : g.comp (algebraMap R R') = (algebraMap S S').comp f := by
    ext x
    simp [g, IsLocalization.Away.map]
  intro q _
  apply localRingHom_bijective_of_square
    (algebraMap R R') f g (algebraMap S S') hsq q
  · exact localRingHom_bijective_algebraMap_of_isLocalization_at
      (R := R) (S := R') (Submonoid.powers r) (q.comap g)
      (by
        simpa only [Ideal.comap_comap] using
          congrArg (fun k : R →+* S' => Ideal.comap k q) hsq.symm)
  · exact hf (q.comap (algebraMap S S'))
  · exact localRingHom_bijective_algebraMap_of_isLocalization
      (R := S) (S := S') (Submonoid.powers (f r)) q

/-- Isomorphisms on local rings pass from `R_f → A` to the composite `R → A_a`. -/
private lemma localRingIso_compPrincipalLocalizations :
    ∀ {R A Rf Aa : Type u} [CommRing R] [CommRing A] [CommRing Rf] [CommRing Aa]
      (f : R) (a : A) [Algebra R Rf] [IsLocalization.Away f Rf] [Algebra A Aa]
      [IsLocalization.Away a Aa] (g : Rf →+* A),
      LocalRingIso g → LocalRingIso ((algebraMap A Aa).comp (g.comp (algebraMap R Rf))) := by
  intro R A Rf Aa _ _ _ _ f a _ _ _ _ g hg
  let u := algebraMap R Rf
  let v := algebraMap A Aa
  intro q _
  let qA := q.comap v
  let p := qA.comap g
  let r := q.comap (v.comp (g.comp u))
  have hru : r = p.comap u := by
    dsimp [r, p, qA]
    simp only [Ideal.comap_comap, RingHom.comp_assoc]
  have hu : Function.Bijective (Localization.localRingHom r p u hru) :=
    localRingHom_bijective_algebraMap_of_isLocalization_at
      (R := R) (S := Rf) (Submonoid.powers f) p hru
  have hf : Function.Bijective (Localization.localRingHom (qA.comap g) qA g rfl) := hg qA
  have hv : Function.Bijective (Localization.localRingHom (q.comap v) q v rfl) :=
    localRingHom_bijective_algebraMap_of_isLocalization
      (R := A) (S := Aa) (Submonoid.powers a) q
  have hrOuter : r = qA.comap (g.comp u) := by
    dsimp [r, qA]
    simp [Ideal.comap_comap]
  exact localRingHom_bijective_comp r qA q (g.comp u) v hrOuter rfl
    (localRingHom_bijective_comp r p qA u g hru rfl hu hf) hv

/-- Isomorphisms on local rings can be checked on a finite principal open cover of the
target. -/
private lemma localRingIso_ofLocalizationFiniteSpanTarget :
    RingHom.OfLocalizationFiniteSpanTarget @LocalRingIso := by
  intro R S _ _ f s hs h q hq
  obtain ⟨a, ha, haq⟩ : ∃ a ∈ s, a ∉ q := by
    by_contra! hnone
    refine hq.ne_top (top_unique ?_)
    rw [← hs]
    exact Ideal.span_le.2 hnone
  let Sa := Localization.Away a
  let v : S →+* Sa := algebraMap S Sa
  have hdisj : Disjoint (Submonoid.powers a : Set S) (q : Set S) := by
    rw [Set.disjoint_left]
    rintro x ⟨n, rfl⟩ hx
    exact haq (hq.mem_of_pow_mem n hx)
  let qa : Ideal Sa := Ideal.map v q
  have : qa.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint
    (Submonoid.powers a) Sa q hq hdisj
  have hqcomap : qa.comap v = q :=
    IsLocalization.under_map_of_isPrime_disjoint (Submonoid.powers a) Sa hq hdisj
  have hvq : Function.Bijective (Localization.localRingHom q qa v hqcomap.symm) :=
    localRingHom_bijective_algebraMap_of_isLocalization_at
      (R := S) (S := Sa) (Submonoid.powers a) qa hqcomap.symm
  have hp : q.comap f = qa.comap (v.comp f) := by
    rw [← hqcomap, Ideal.comap_comap]
  have hfa : Function.Bijective (Localization.localRingHom (q.comap f) qa (v.comp f) hp) :=
    localRingHom_bijective_congr hp (h ⟨a, ha⟩ qa)
  rw [localRingHom_comp_atPrime (q.comap f) q qa f rfl v hqcomap.symm, RingHom.coe_comp] at hfa
  exact (Function.Bijective.of_comp_iff' hvq _).mp hfa

/-- Having isomorphisms on the local rings at every prime of the target is a
local property of ring homomorphisms. -/
@[stacks 01SX "isomorphism_on_local_rings_is_local"]
theorem localRingHom_bijective_propertyIsLocal :
    RingHom.StacksPropertyIsLocal
      (fun {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) ↦
        ∀ (q : Ideal S) [q.IsPrime],
          Function.Bijective
            (Localization.localRingHom (Ideal.comap f q) q f rfl)) :=
  ⟨localRingIso_localizationAwayPreserves, localRingIso_compPrincipalLocalizations,
    localRingIso_ofLocalizationFiniteSpanTarget⟩

/-- Inducing isomorphisms on local rings is invariant under pre- and post-composition with
ring isomorphisms. -/
private theorem localRingIso_respectsIso : RingHom.RespectsIso (@LocalRingIso) := by
  constructor
  · intro R S T _ _ _ f e hf q hq
    let p := Ideal.comap (e : S →+* T) q
    have : p.IsPrime := Ideal.comap_isPrime (e : S →+* T) q
    have hI : Ideal.comap ((e : S →+* T).comp f) q = p.comap f := by simp [p, Ideal.comap_comap]
    exact localRingHom_bijective_comp _ p q f (e : S →+* T) hI rfl
      (localRingHom_bijective_congr hI (hf p))
      (Localization.localRingEquiv p q (e : S ≃+* T) rfl).bijective
  · intro R S T _ _ _ f e hf q hq
    let p := Ideal.comap f q
    have : p.IsPrime := Ideal.comap_isPrime f q
    have hI : Ideal.comap (f.comp (e : R →+* S)) q = p.comap (e : R →+* S) := by
      simp [p, Ideal.comap_comap]
    exact localRingHom_bijective_comp _ p q (e : R →+* S) f hI rfl
      (Localization.localRingEquiv _ p (e : R ≃+* S) rfl).bijective (hf q)

/-- If `R → C` induces isomorphisms on local rings, then for a prime `p` of `C` the base change
`A ⊗[R] C_p` is the localization of `A` at the image of the complement of the contraction of
`p`. -/
private noncomputable def tensorAtPrimeAlgEquiv {R A C : Type u} [CommRing R] [CommRing A]
    [CommRing C] [Algebra R A] [Algebra R C] (hf : LocalRingIso (algebraMap R C))
    (p : Ideal C) [p.IsPrime] :
    A ⊗[R] Localization.AtPrime p ≃ₐ[A]
      Localization (Algebra.algebraMapSubmonoid A (p.comap (algebraMap R C)).primeCompl) :=
  let i := p.comap (algebraMap R C)
  let g : Localization.AtPrime i →ₐ[R] Localization.AtPrime p :=
    Localization.localAlgHom i p (Algebra.ofId R C) rfl
  let e : Localization.AtPrime i ≃ₐ[R] Localization.AtPrime p := AlgEquiv.ofBijective g (hf p)
  let φ : A ⊗[R] Localization.AtPrime p →ₐ[A]
      A ⊗[R] Localization.AtPrime i := Algebra.TensorProduct.map (AlgHom.id A A) e.symm
  have hφ : Function.Bijective φ := by
    change Function.Bijective (TensorProduct.map (LinearEquiv.refl R A).toLinearMap
      e.symm.toLinearEquiv.toLinearMap)
    exact TensorProduct.map_bijective (LinearEquiv.refl R A).bijective
      e.symm.toLinearEquiv.bijective
  (AlgEquiv.ofBijective φ hφ).trans (Localization.tensorLeftAlgEquiv i.primeCompl A)

/-- If `A → E → E'` and `A → L` are maps with `E'` a localization of `E`, `L` a localization of
`A`, and `E' ≃ L` compatible with the maps from `A`, then `A → E` induces isomorphisms on the
local rings at the primes of `E` coming from `E'`. -/
private lemma localRingHom_bijective_of_localization_equiv
    {A E E' L : Type u} [CommRing A] [CommRing E] [CommRing E'] [CommRing L]
    [Algebra A E] [Algebra E E'] [Algebra A L] (M : Submonoid E) (M₂ : Submonoid A)
    [IsLocalization M E'] [IsLocalization M₂ L] (e : E' ≃+* L)
    (he : (e : E' →+* L).comp ((algebraMap E E').comp (algebraMap A E)) = algebraMap A L)
    (q : Ideal E) [q.IsPrime] (qE' : Ideal E') [qE'.IsPrime]
    (hq : q = qE'.comap (algebraMap E E')) :
    Function.Bijective
      (Localization.localRingHom (q.comap (algebraMap A E)) q (algebraMap A E) rfl) := by
  let qL := qE'.comap (e.symm : L →+* E')
  have hqL : qE' = qL.comap (e : E' →+* L) := by
    ext x
    simp [qL]
  have ht : q.comap (algebraMap A E) = qL.comap (algebraMap A L) := by
    rw [← he, hq, hqL]
    simp only [Ideal.comap_comap, RingHom.comp_assoc]
  have key : Localization.localRingHom (q.comap (algebraMap A E)) qL (algebraMap A L) ht =
      (Localization.localRingHom qE' qL (e : E' →+* L) hqL).comp
        ((Localization.localRingHom q qE' (algebraMap E E') hq).comp
          (Localization.localRingHom (q.comap (algebraMap A E)) q (algebraMap A E) rfl)) := by
    refine Localization.localRingHom_unique _ _ _ _ fun x ↦ ?_
    simp only [RingHom.comp_apply, Localization.localRingHom_to_map, ← he]
  have hb := localRingHom_bijective_algebraMap_of_isLocalization_at M₂ qL ht
  have he' : Function.Bijective (Localization.localRingHom qE' qL (e : E' →+* L) hqL) :=
    (Localization.localRingEquiv qE' qL e hqL).bijective
  rw [key, RingHom.coe_comp, RingHom.coe_comp] at hb
  exact (Function.Bijective.of_comp_iff'
    (localRingHom_bijective_algebraMap_of_isLocalization_at M qE' hq) _).mp
    ((Function.Bijective.of_comp_iff' he' _).mp hb)

/-- The tensor-product form of base-change stability: if `R → C` induces isomorphisms on
local rings, so does `A → A ⊗[R] C`. -/
private theorem tensor_localRingHom_bijective
    {R A C : Type u} [CommRing R] [CommRing A] [CommRing C]
    [Algebra R A] [Algebra R C]
    (hf : LocalRingIso (algebraMap R C))
    (q : Ideal (A ⊗[R] C)) [q.IsPrime] :
    Function.Bijective (Localization.localRingHom (Ideal.comap (algebraMap A (A ⊗[R] C)) q)
      q (algebraMap A (A ⊗[R] C)) rfl) := by
  let p := Ideal.comap (Algebra.TensorProduct.includeRight (R := R) (A := A) (B := C)) q
  have : p.IsPrime := Ideal.comap_isPrime _ q
  let i := Ideal.comap (algebraMap R C) p
  let eTotal := tensorAtPrimeAlgEquiv (A := A) hf p
  let E := A ⊗[R] C
  let E' := A ⊗[R] Localization.AtPrime p
  let eMapAlg : E →ₐ[R] E' :=
    Algebra.TensorProduct.map (AlgHom.id R A) (IsScalarTower.toAlgHom R C _)
  let algEE : Algebra E E' := eMapAlg.toRingHom.toAlgebra
  have : IsScalarTower A E E' := IsScalarTower.of_algebraMap_eq fun x => by
    change x ⊗ₜ[R] (1 : Localization.AtPrime p) =
      eMapAlg (x ⊗ₜ[R] (1 : C))
    rw [Algebra.TensorProduct.map_tmul]
    simp
  let M := p.primeCompl.map
    (Algebra.TensorProduct.includeRight (R := R) (A := A) (B := C)).toRingHom
  have : IsLocalization M E' := by
    refine IsLocalization.tensorProduct_tensorProduct_right R A p.primeCompl
      (Localization.AtPrime p) ?_
    change eMapAlg.toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom = _
    exact congrArg AlgHom.toRingHom <| Algebra.TensorProduct.map_comp_includeRight
      (AlgHom.id R A) (IsScalarTower.toAlgHom R C (Localization.AtPrime p))
  let qE' := q.map (algebraMap E E')
  have hdisj : Disjoint (M : Set E) q := by
    rw [Set.disjoint_left]
    intro x hxM hxq
    change x ∈ p.primeCompl.map
      (Algebra.TensorProduct.includeRight (R := R) (A := A) (B := C)).toRingHom at hxM
    rcases hxM with ⟨c, hc, rfl⟩
    exact hc (Ideal.mem_comap.mp hxq)
  have : qE'.IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint M E' q (inferInstance : q.IsPrime) hdisj
  have hUnder1 : qE'.under E = q :=
    IsLocalization.under_map_of_isPrime_disjoint M E' (inferInstance : q.IsPrime) hdisj
  let M₂ := Algebra.algebraMapSubmonoid A i.primeCompl
  let L := Localization M₂
  have he : (eTotal.toRingEquiv : E' →+* L).comp ((algebraMap E E').comp (algebraMap A E)) =
      algebraMap A L := by
    rw [← IsScalarTower.algebraMap_eq A E E']
    ext a
    exact eTotal.commutes a
  exact localRingHom_bijective_of_localization_equiv M M₂ eTotal.toRingEquiv he q qE'
    hUnder1.symm

/-- Isomorphisms on local rings at every prime of the target are preserved by
arbitrary base change of commutative rings. -/
@[stacks 01SY "local_rings_base_change"]
theorem localRingHom_bijective_isStableUnderBaseChange :
    RingHom.IsStableUnderBaseChange
      (fun {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) ↦
        ∀ (q : Ideal S) [q.IsPrime],
          Function.Bijective
            (Localization.localRingHom (Ideal.comap f q) q f rfl)) := by
  apply RingHom.IsStableUnderBaseChange.mk localRingIso_respectsIso
  intro R S T _ _ _ _ _ hf q hq
  exact tensor_localRingHom_bijective hf q

/-- The property that all induced maps on local rings are isomorphisms is
stable under composition. -/
@[stacks 01SZ "local_rings_composition"]
theorem localRingHom_bijective_stableUnderComposition :
    RingHom.StableUnderComposition
      (fun {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) ↦
        ∀ (q : Ideal S) [q.IsPrime],
          Function.Bijective
            (Localization.localRingHom (Ideal.comap f q) q f rfl)) := by
  intro R A B _ _ _ f g hf hg r hr
  let q := Ideal.comap g r
  have : q.IsPrime := Ideal.comap_isPrime g r
  change Function.Bijective
    (Localization.localRingHom (q.comap f) r (g.comp f) (Ideal.comap_comap f g))
  exact localRingHom_bijective_comp (q.comap f) q r f g rfl rfl (hf q) (hg r)

end RingHom
