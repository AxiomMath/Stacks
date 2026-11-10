module

public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.FiniteOverSmooth.ResidueFieldSpecMap
public import StacksFrontier.AlgebraicGeometry.ProEtale.IndZariski.FaithfullyFlatExtension
public import StacksFrontier.AlgebraicGeometry.ProEtale.WLocal.WContractibleCharacterization
public import StacksFrontier.AlgebraicGeometry.ProEtale.WLocal.WLocalIndEtaleSquare
public import StacksFrontier.RingTheory.Etale.IndEtaleUniverse
public import StacksFrontier.RingTheory.WeaklyEtale.Descent
public import StacksFrontier.RingTheory.WeaklyEtale.ResidueField
public import StacksFrontier.RingTheory.WeaklyEtale.StrictlyHenselian
public import StacksCore.Tactic.StacksAttribute

/-!
# Faithfully flat ind-étale extensions of weakly étale maps

A weakly étale ring map `A → B` becomes ind-étale after a faithfully flat ind-étale extension
`B → B'` of its target.

## Main results

* `AlgebraicGeometry.ProEtale.exists_faithfullyFlat_indEtale_extension`: a weakly étale ring map
  `A → B` admits a faithfully flat ind-étale `B → B'` with `A → B'` ind-étale.
* `AlgebraicGeometry.ProEtale.identifiesLocalRings_of_isMaximal`: identifying local rings may be
  checked at the maximal ideals of the target.
* `AlgebraicGeometry.ProEtale.isAlgebraic_residueField_specMap`: algebraicity of the residue
  field extensions of a ring map, read on the induced morphism of affine schemes.
* `AlgebraicGeometry.ProEtale.indEtale_of_indEtaleUnder` and
  `AlgebraicGeometry.ProEtale.indEtaleUnder_of_indEtale`: ind-étaleness of an algebra and the
  property of its structure morphism of being a filtered colimit of étale ring maps in the
  under-category agree.

## References

* [Stacks Project, Tag 097Z](https://stacks.math.columbia.edu/tag/097Z)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.ProEtale

universe u

/-- Algebraicity of the residue field extensions of a ring map `A → B`, stated for the residue
fields of the ideals of `B`, is algebraicity of the residue field extensions of the induced
morphism of affine schemes. -/
theorem isAlgebraic_residueField_specMap (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    (h : ∀ (q : Ideal B) [q.IsPrime],
      letI := (Ideal.ResidueField.map (q.comap (algebraMap A B)) q (algebraMap A B) rfl).toAlgebra
      Algebra.IsAlgebraic (q.comap (algebraMap A B)).ResidueField q.ResidueField) :
    let f : AlgebraicGeometry.Spec (.of B) ⟶ AlgebraicGeometry.Spec (.of A) :=
        Scheme.Spec.map (CommRingCat.ofHom (algebraMap A B)).op
      ∀ x,
        letI := (f.residueFieldMap x).hom.toAlgebra
        Algebra.IsAlgebraic
          ((AlgebraicGeometry.Spec (.of A)).residueField (f x))
          ((AlgebraicGeometry.Spec (.of B)).residueField x) := by
  intro f x
  let φ : CommRingCat.of A ⟶ CommRingCat.of B := CommRingCat.ofHom (algebraMap A B)
  let p : Ideal A := (PrimeSpectrum.comap φ.hom x).asIdeal
  have : p.IsPrime := (PrimeSpectrum.comap φ.hom x).isPrime
  have : x.asIdeal.IsPrime := x.isPrime
  let : Algebra p.ResidueField x.asIdeal.ResidueField :=
    (Ideal.ResidueField.map p x.asIdeal φ.hom rfl).toAlgebra
  have : Algebra.IsAlgebraic p.ResidueField x.asIdeal.ResidueField := h x.asIdeal
  let : Algebra ((AlgebraicGeometry.Spec (.of A)).residueField (f x))
      ((AlgebraicGeometry.Spec (.of B)).residueField x) := (f.residueFieldMap x).hom.toAlgebra
  exact Algebra.IsAlgebraic.of_ringHom_of_comp_eq
    (Scheme.Spec.residueFieldIso (.of A) (PrimeSpectrum.comap φ.hom x)).hom.hom
    (Scheme.Spec.residueFieldIso (.of B) x).hom.hom
    (ConcreteCategory.bijective_of_isIso
      (Scheme.Spec.residueFieldIso (.of A) (PrimeSpectrum.comap φ.hom x)).hom).surjective
    (ConcreteCategory.bijective_of_isIso
      (Scheme.Spec.residueFieldIso (.of B) x).hom).injective
    (RingHom.ext fun z => (residueFieldMap_specMap_apply φ x z).symm)

/-- Ind-étaleness of an algebra is the property of its structure morphism of being a filtered
colimit of étale ring maps in the under-category of the base. -/
theorem indEtale_of_indEtaleUnder (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    (h : ObjectProperty.ind.{u} (fun C : Under (CommRingCat.of A) ↦ C.hom.hom.Etale)
      (Under.mk (CommRingCat.ofHom (algebraMap A B)))) : StacksDraft.IndEtale A B := by
  refine StacksDraft.indEtale_iff.mpr (CommAlgCat.ind_etale_iff_ind_algebraMap.2 ?_)
  rwa [MorphismProperty.ind_iff_ind_underMk]

/-- The structure morphism of an ind-étale algebra is a filtered colimit of étale ring maps in
the under-category of the base. -/
theorem indEtaleUnder_of_indEtale (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    (h : StacksDraft.IndEtale A B) :
    ObjectProperty.ind.{u} (fun C : Under (CommRingCat.of A) ↦ C.hom.hom.Etale)
      (Under.mk (CommRingCat.ofHom (algebraMap A B))) := by
  have h' := CommAlgCat.ind_etale_iff_ind_algebraMap.1 (StacksDraft.indEtale_iff.mp h)
  rwa [MorphismProperty.ind_iff_ind_underMk] at h'

/-- Bijectivity of the local map of local rings descends along a specialization: if `q ≤ m` are
primes of `D` and `C_{m ∩ C} → D_m` is bijective, then so is `C_{q ∩ C} → D_q`. -/
private theorem bijective_localRingHom_comap_of_le {C D : Type u} [CommRing C] [CommRing D]
    (f : C →+* D) {q m : Ideal D} [hq : q.IsPrime] [m.IsPrime] (hm : q ≤ m)
    (h : Function.Bijective (Localization.localRingHom (m.comap f) m f rfl)) :
    Function.Bijective (Localization.localRingHom (q.comap f) q f rfl) := by
  let p : Ideal C := q.comap f
  let n : Ideal C := m.comap f
  let Cn := Localization.AtPrime n
  let Dm := Localization.AtPrime m
  have hdisj : Disjoint (m.primeCompl : Set D) (q : Set D) :=
    Set.disjoint_left.mpr fun _ hyM hyq => hyM (hm hyq)
  let q' : Ideal Dm := Ideal.map (algebraMap D Dm) q
  have : q'.IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint m.primeCompl Dm q hq hdisj
  have hq'comap : q'.comap (algebraMap D Dm) = q :=
    IsLocalization.under_map_of_isPrime_disjoint m.primeCompl Dm hq hdisj
  let e : Cn ≃+* Dm := RingEquiv.ofBijective (Localization.localRingHom n m f rfl) h
  have hecomp : e.toRingHom.comp (algebraMap C Cn) = (algebraMap D Dm).comp f :=
    RingHom.ext fun y => Localization.localRingHom_to_map n m f rfl y
  let p' : Ideal Cn := q'.comap e.toRingHom
  have hp'comap : p'.comap (algebraMap C Cn) = p := by
    simp only [p', Ideal.comap_comap, hecomp]
    rw [← Ideal.comap_comap, hq'comap]
  have : IsLocalization.AtPrime (Localization.AtPrime p') p := by
    simpa [n, hp'comap] using
      (IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
        n.primeCompl (Localization.AtPrime p') p')
  have : IsLocalization.AtPrime (Localization.AtPrime q') q := by
    simpa [hq'comap] using
      (IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
        m.primeCompl (Localization.AtPrime q') q')
  let eC : Localization.AtPrime p ≃ₐ[C] Localization.AtPrime p' :=
    IsLocalization.algEquiv p.primeCompl _ _
  let eD : Localization.AtPrime q' ≃ₐ[D] Localization.AtPrime q :=
    IsLocalization.algEquiv q.primeCompl _ _
  let ePQ : Localization.AtPrime p' ≃+* Localization.AtPrime q' :=
    Localization.localRingEquiv p' q' e rfl
  have hk : eD.toRingHom.comp (ePQ.toRingHom.comp eC.toRingHom) =
      Localization.localRingHom p q f rfl := by
    symm
    refine Localization.localRingHom_unique p q f rfl fun y => ?_
    change eD (ePQ (eC (algebraMap C (Localization.AtPrime p) y))) = _
    rw [eC.commutes]
    change eD (Localization.localRingHom p' q' e rfl
      (algebraMap Cn (Localization.AtPrime p') (algebraMap C Cn y))) = _
    rw [Localization.localRingHom_to_map p' q' e rfl]
    change eD (algebraMap Dm (Localization.AtPrime q') (e.toRingHom (algebraMap C Cn y))) = _
    rw [show e.toRingHom (algebraMap C Cn y) = algebraMap D Dm (f y) from
      congrArg (fun g : C →+* Dm => g y) hecomp]
    exact eD.commutes (f y)
  change Function.Bijective (Localization.localRingHom p q f rfl)
  rw [← hk]
  exact eD.bijective.comp (ePQ.bijective.comp eC.bijective)

/-- A ring map `f : C → D` identifies local rings as soon as the local map
`C_{m ∩ C} → D_m` is bijective at every maximal ideal `m` of `D`. -/
theorem identifiesLocalRings_of_isMaximal {C D : Type u} [CommRing C] [CommRing D] (f : C →+* D)
    (hmax : ∀ (m : Ideal D) [m.IsMaximal],
      Function.Bijective (Localization.localRingHom (m.comap f) m f rfl)) :
    letI := f.toAlgebra; Algebra.IdentifiesLocalRings C D := by
  intro q _
  obtain ⟨m, _, hqm⟩ := Ideal.exists_le_maximal q (Ideal.IsPrime.ne_top ‹q.IsPrime›)
  exact bijective_localRingHom_comap_of_le f hqm (hmax m)

/-- A weakly étale ring map `C → D` whose source is strictly henselian at the contraction of a
prime `m` of `D` induces a bijection `C_{m ∩ C} → D_m` of local rings. -/
private theorem bijective_localRingHom_of_weaklyEtale_of_strictlyHenselian {C D : Type u}
    [CommRing C] [CommRing D] [Algebra C D] [Algebra.WeaklyEtale C D] (m : Ideal D) [m.IsPrime]
    [StrictlyHenselianLocalRing (Localization.AtPrime (m.comap (algebraMap C D)))] :
    Function.Bijective
      (Localization.localRingHom (m.comap (algebraMap C D)) m (algebraMap C D) rfl) := by
  set n : Ideal C := m.comap (algebraMap C D)
  let Cn := Localization.AtPrime n
  let Dm := Localization.AtPrime m
  let : Algebra Cn Dm := (Localization.localRingHom n m (algebraMap C D) rfl).toAlgebra
  let : Algebra C Dm := ((algebraMap D Dm).comp (algebraMap C D)).toAlgebra
  let : SMul C Dm := (inferInstance : Algebra C Dm).toSMul
  let : IsScalarTower C D Dm := IsScalarTower.of_algebraMap_eq' rfl
  let : SMul Cn Dm := (inferInstance : Algebra Cn Dm).toSMul
  let : IsScalarTower C Cn Dm :=
    IsScalarTower.of_algebraMap_eq' (RingHom.ext fun c =>
      (Localization.localRingHom_to_map n m (algebraMap C D) rfl c).symm)
  let : Algebra.WeaklyEtale C Cn :=
    (weaklyEtale_of_isLocalization_etale_filteredColimit.{u, u, u} C).1 Cn n.primeCompl
  let : Algebra.WeaklyEtale D Dm :=
    (weaklyEtale_of_isLocalization_etale_filteredColimit.{u, u, u} D).1 Dm m.primeCompl
  have : IsLocalHom (algebraMap Cn Dm) :=
    Localization.isLocalHom_localRingHom n m (algebraMap C D) rfl
  exact bijective_algebraMap_of_weaklyEtale_of_isLocalHom Cn Dm
    (weaklyEtale_of_comp C Cn Dm inferInstance (Algebra.WeaklyEtale.trans C D Dm))

/-- A weakly étale ring map admits a faithfully flat ind-étale extension of its target after which
the composite is ind-étale. -/
@[stacks 097Z]
theorem exists_faithfullyFlat_indEtale_extension
    {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B)
    (hf : letI := f.toAlgebra; Algebra.WeaklyEtale A B) :
    ∃ (B' : Type u) (_ : CommRing B') (g : B →+* B'),
      g.FaithfullyFlat ∧
        (ObjectProperty.ind.{u}
          (fun C : Under (CommRingCat.of B) ↦ C.hom.hom.Etale)
          (Under.mk (CommRingCat.ofHom g)) ∧
        ObjectProperty.ind.{u}
          (fun C : Under (CommRingCat.of A) ↦ C.hom.hom.Etale)
          (Under.mk (CommRingCat.ofHom (g.comp f)))) := by
  let : Algebra A B := f.toAlgebra
  let : Algebra.WeaklyEtale A B := hf
  obtain ⟨C, D, hCR, hDR, hAC, hAD, hBD, hCD, hABD, hACD, hACff, hACind, hBDff, hBDind,
      hWC, hWD, hWCD, hclosedD, -, -, hstrict⟩ :=
    exists_wLocal_faithfullyFlat_indEtale_extensions A B
      (isAlgebraic_residueField_specMap A B fun q _ =>
        (isSeparable_and_isAlgebraic_residueField_of_weaklyEtale A B hf
          (q.comap (algebraMap A B)) q rfl).2)
  have hACindEtale : StacksDraft.IndEtale A C := indEtale_of_indEtaleUnder A C hACind
  have hBDindEtale : StacksDraft.IndEtale B D := indEtale_of_indEtaleUnder B D hBDind
  have : Algebra.WeaklyEtale B D := Algebra.weaklyEtale_of_ind_etale hBDindEtale
  have : Algebra.WeaklyEtale C D := weaklyEtale_of_comp A C D
    (Algebra.weaklyEtale_of_ind_etale hACindEtale) (Algebra.WeaklyEtale.trans A B D)
  have hmax : ∀ (m : Ideal D) [m.IsMaximal],
      Function.Bijective (Localization.localRingHom (m.comap (algebraMap C D)) m
        (algebraMap C D) rfl) := by
    intro m hm
    have hmclosed : (⟨m, hm.isPrime⟩ : PrimeSpectrum D) ∈ closedPoints (PrimeSpectrum D) :=
      mem_closedPoints_iff.mpr ((PrimeSpectrum.isClosed_singleton_iff_isMaximal _).mpr hm)
    rw [hclosedD] at hmclosed
    have : (m.comap (algebraMap C D)).IsMaximal :=
      (PrimeSpectrum.isClosed_singleton_iff_isMaximal
        (⟨m.comap (algebraMap C D), inferInstance⟩ : PrimeSpectrum C)).mp
        (mem_closedPoints_iff.mp hmclosed)
    have := hstrict (m.comap (algebraMap C D))
    exact bijective_localRingHom_of_weaklyEtale_of_strictlyHenselian m
  obtain ⟨D', hD'R, g', hgff, hgInd, hCInd⟩ :=
    exists_faithfullyFlat_indZariski_extension (algebraMap C D)
      (identifiesLocalRings_of_isMaximal (algebraMap C D) hmax)
  let : Algebra D D' := g'.toAlgebra
  let : Algebra B D' := (g'.comp (algebraMap B D)).toAlgebra
  let : IsScalarTower B D D' := IsScalarTower.of_algebraMap_eq' rfl
  let : Algebra C D' := (g'.comp (algebraMap C D)).toAlgebra
  let : IsScalarTower C D D' := IsScalarTower.of_algebraMap_eq' rfl
  let : Algebra A D' := ((g'.comp (algebraMap B D)).comp f).toAlgebra
  let : IsScalarTower A C D' := IsScalarTower.of_algebraMap_eq' (RingHom.ext fun a => by
    change g' (algebraMap B D (algebraMap A B a)) = g' (algebraMap C D (algebraMap A C a))
    rw [← IsScalarTower.algebraMap_apply A B D, ← IsScalarTower.algebraMap_apply A C D])
  refine ⟨D', hD'R, g'.comp (algebraMap B D),
    RingHom.FaithfullyFlat.stableUnderComposition _ _ hBDff hgff, ?_, ?_⟩
  · change ObjectProperty.ind.{u} (fun C : Under (CommRingCat.of B) ↦ C.hom.hom.Etale)
      (Under.mk (CommRingCat.ofHom (algebraMap B D) ≫ CommRingCat.ofHom g'))
    exact indEtaleUnder_of_indEtale B D'
      (StacksDraft.indEtale_comp hBDindEtale (indEtale_of_isIndZariski D D' hgInd))
  · change ObjectProperty.ind.{u} (fun C : Under (CommRingCat.of A) ↦ C.hom.hom.Etale)
      (Under.mk (CommRingCat.ofHom f ≫ CommRingCat.ofHom (algebraMap B D) ≫
        CommRingCat.ofHom g'))
    exact indEtaleUnder_of_indEtale A D'
      (StacksDraft.indEtale_comp hACindEtale (indEtale_of_isIndZariski C D' hCInd))

end AlgebraicGeometry.ProEtale

end
