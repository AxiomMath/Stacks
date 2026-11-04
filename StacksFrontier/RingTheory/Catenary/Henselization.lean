module

public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.Spectrum.Prime.RingHom
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.Branches.Completion
public import StacksFrontier.RingTheory.Catenary.Formal
public import StacksFrontier.RingTheory.Henselian.Henselization.Existence
public import StacksFrontier.RingTheory.Henselian.StrictHenselization.Existence

@[expose] public section

/-!
# Universal catenarity from geometrically normal formal fibres

A Noetherian local ring whose formal fibres are all geometrically normal has a universally
catenary henselization, and is itself universally catenary as soon as it is unibranch.

## Main results

* `isUniversallyCatenary_henselization_and_of_isUnibranch` (Stacks 0C2F): geometrically normal
  formal fibres make a henselization of `A` universally catenary, and make `A` universally
  catenary if `A` is unibranch.
* `ringKrullDim_eq_ringKrullDim_of_isHenselization`: a Noetherian local ring and a henselization
  of it have the same Krull dimension.

## Implementation notes

The proof is Ratliff's criterion (Stacks 0AW6) applied to a henselization `Aʰ`: universal
catenarity of `Aʰ` is equidimensionality of `(Aʰ)^∧ ⧸ p (Aʰ)^∧` for every minimal prime `p` of
`Aʰ`, and that holds as soon as the radical of `p (Aʰ)^∧` is prime, which is what Stacks 0C29
gives once the branch counts of `A` and `Â` are known to agree — and Stacks 0C2E says they do,
because the formal fibres are geometrically normal. The bridge between the two completions is
`exists_ringEquiv_adicCompletion_of_isHenselization`, the comparison `Â ≃ (Aʰ)^∧` of Stacks 06LJ:
`IsFormallyCatenary Aʰ` speaks about `(Aʰ)^∧` while Stacks 0C29 and 0C2E only ever speak about
`Â`. Noetherianness of `Aʰ`, which Ratliff's criterion needs, is
`isNoetherianRing_of_isHenselization`.

Tag 0C2F binds the universes of `A` and of its henselization separately, while Stacks 0C29,
0C2E and the comparison isomorphism all need the two rings in one universe. So the argument is
carried out for a henselization living in the universe of `A`, produced by
`IsLocalRing.exists_henselization`, and transported to the given one along
`nonempty_henselization_algEquiv`: two henselizations of the same local ring are isomorphic over
it whatever their universes, because the universal property can be moved to the base
`ULift A` by `ind_etale_restrictScalars`. Universal catenarity is invariant under a ring
equivalence between arbitrary universes (`isUniversallyCatenary_of_ringEquiv`), a finite-type
algebra over the target being shrunk into the source's universe.

## References

* [Heinzer, Rotthaus, and Wiegand, Corollary 2.3][Heinzer-Rotthaus-Wiegand]
* [The Stacks Project, Tag 0C2F](https://stacks.math.columbia.edu/tag/0C2F)
-/

universe u v

open IsLocalRing CategoryTheory CategoryTheory.Limits

namespace StacksDraft.Catenary

/-! ### Henselizations in different universes are isomorphic -/

/-- Restriction of scalars along a ring map, as a functor between categories of commutative
algebras. -/
private def restrictScalars {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) :
    CommAlgCat.{v} S ⥤ CommAlgCat.{v} R where
  obj A :=
    let : Algebra R A := Algebra.compHom _ f
    CommAlgCat.of R A
  map {A B} g :=
    let : Algebra R A := Algebra.compHom _ f
    let : Algebra R B := Algebra.compHom _ f
    CommAlgCat.ofHom { g.hom with commutes' := fun r => g.hom.commutes (f r) }

set_option backward.isDefEq.respectTransparency false in
/-- Restriction of scalars along the identity is the identity functor. -/
private def restrictScalarsId {R : Type*} [CommRing R] (f : R →+* R) (hf : f = .id R) :
    restrictScalars.{v} f ≅ 𝟭 _ :=
  NatIso.ofComponents
    (fun A ↦ CommAlgCat.isoMk <|
      @AlgEquiv.ofRingEquiv (f := RingEquiv.refl _) _ _ _ _ _ _
        ((restrictScalars f).obj A).algebra _ fun _ ↦ by subst hf; rfl) (by intros; ext; rfl)

set_option backward.isDefEq.respectTransparency false in
/-- Restriction of scalars along a composite is the composite of the restrictions. -/
private def restrictScalarsComp {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    (f : R →+* S) (g : S →+* T) (gf : R →+* T) (hfg : gf = g.comp f) :
    restrictScalars.{v} gf ≅ restrictScalars.{v} g ⋙ restrictScalars.{v} f :=
  NatIso.ofComponents
    (fun A ↦ CommAlgCat.isoMk <|
      @AlgEquiv.ofRingEquiv (f := RingEquiv.refl _) _ _ _ _ _ _
        ((restrictScalars gf).obj A).algebra
        ((restrictScalars f).obj ((restrictScalars g).obj A)).algebra
        fun _ ↦ by subst hfg; rfl) (by intros; ext; rfl)

/-- Changing the base along a ring equivalence is an equivalence of algebra categories. -/
private def restrictScalarsEquivalence {R S : Type*} [CommRing R] [CommRing S]
    (e : R ≃+* S) : CommAlgCat.{v} S ≌ CommAlgCat.{v} R where
  functor := restrictScalars e.toRingHom
  inverse := restrictScalars e.symm.toRingHom
  unitIso := (restrictScalarsId _ rfl).symm ≪≫
    restrictScalarsComp _ _ _ e.toRingHom_comp_symm_toRingHom.symm
  counitIso := (restrictScalarsComp _ _ _ e.symm_toRingHom_comp_toRingHom.symm).symm ≪≫
    restrictScalarsId _ rfl
  functor_unitIso_comp := by intro X; ext; rfl

/-- Ind-étaleness is invariant under an isomorphism of the base ring. -/
private theorem ind_etale_restrictScalars {R S : Type*} [CommRing R] [CommRing S]
    (e : R ≃+* S) (C : CommAlgCat.{v} S)
    (h : (CommAlgCat.etale S).ind.{v} C) :
    (CommAlgCat.etale R).ind.{v} ((restrictScalars e.toRingHom).obj C) := by
  obtain ⟨J, _, _, pres, hp⟩ := h
  refine ⟨J, inferInstance, inferInstance, pres.map (restrictScalarsEquivalence e).functor,
    fun j => ?_⟩
  let : Algebra R S := e.toRingHom.toAlgebra
  let : Algebra R (pres.diag.obj j) := Algebra.compHom _ e.toRingHom
  let : IsScalarTower R S (pres.diag.obj j) := IsScalarTower.of_algebraMap_eq' rfl
  have : Algebra.Etale R S := RingHom.etale_algebraMap.1 (RingHom.Etale.of_bijective e.bijective)
  have : Algebra.Etale S (pres.diag.obj j) := hp j
  exact Algebra.Etale.comp R S (pres.diag.obj j)

/-- Surjectivity of a residue field map is transported along a square of ring equivalences. -/
private theorem residueFieldMap_surjective_of_equiv
    {R S R' S' : Type*} [CommRing R] [IsLocalRing R] [CommRing S] [IsLocalRing S]
    [CommRing R'] [IsLocalRing R'] [CommRing S'] [IsLocalRing S']
    [Algebra R S] [Algebra R' S']
    [IsLocalHom (algebraMap R S)] [IsLocalHom (algebraMap R' S')]
    (eR : R' ≃+* R) (eS : S' ≃+* S)
    (he : ∀ r, eS (algebraMap R' S' r) = algebraMap R S (eR r))
    (h : Function.Surjective (ResidueField.map (algebraMap R S))) :
    Function.Surjective (ResidueField.map (algebraMap R' S')) := by
  intro y
  obtain ⟨s, rfl⟩ := residue_surjective y
  obtain ⟨r, hr⟩ := h (residue S (eS s))
  obtain ⟨a, rfl⟩ := residue_surjective r
  refine ⟨residue R' (eR.symm a), ?_⟩
  let : IsLocalHom eS.toRingHom := isLocalHom_of_leftInverse eS.symm eS.left_inv
  apply (ResidueField.map eS.toRingHom).injective
  simp only [ResidueField.map_residue]
  show residue S (eS (algebraMap R' S' (eR.symm a))) = residue S (eS s)
  rw [he, eR.apply_symm_apply]
  simpa only [ResidueField.map_residue] using hr

/-- The universal property of the henselization with all three rings in independent universes:
there is exactly one local `R`-algebra map from a henselization of `R` to a henselian local
`R`-algebra with local structure map. -/
@[sga "4 VIII 4.1" "partial"]
private theorem existsUnique_henselization_map
    (R : Type u) (S : Type v) (T : Type*)
    [CommRing R] [IsLocalRing R] [CommRing S] [IsLocalRing S] [Algebra R S]
    [IsHenselization R (ResidueField R) S]
    [CommRing T] [HenselianLocalRing T] [Algebra R T] [IsLocalHom (algebraMap R T)] :
    ∃! f : S →ₐ[R] T, IsLocalHom f := by
  let R' := ULift.{v} R
  let S' := ULift.{u} S
  let eR : R' ≃+* R := ULift.ringEquiv
  let eS : S' ≃+* S := ULift.ringEquiv
  let : IsLocalHom eR.toRingHom := isLocalHom_of_leftInverse eR.symm eR.left_inv
  let : IsLocalHom eS.toRingHom := isLocalHom_of_leftInverse eS.symm eS.left_inv
  let : IsLocalHom eS.symm.toRingHom := isLocalHom_of_leftInverse eS eS.right_inv
  let : IsLocalRing R' := eR.symm.isLocalRing
  let : IsLocalRing S' := eS.symm.isLocalRing
  let : IsLocalHom (algebraMap R S) := IsHenselization.isLocalHom (L := ResidueField R)
  let : IsLocalHom (algebraMap R S') :=
    show IsLocalHom (eS.symm.toRingHom.comp (algebraMap R S)) from RingHom.isLocalHom_comp _ _
  let : Algebra R' S' := Algebra.compHom S' eR.toRingHom
  let : Algebra R' T := Algebra.compHom T eR.toRingHom
  let : IsLocalHom (algebraMap R' S') :=
    show IsLocalHom ((algebraMap R S').comp eR.toRingHom) from RingHom.isLocalHom_comp _ _
  let : IsLocalHom (algebraMap R' T) :=
    show IsLocalHom ((algebraMap R T).comp eR.toRingHom) from RingHom.isLocalHom_comp _ _
  have hind : (CommAlgCat.etale R').ind.{max u v} (CommAlgCat.of R' S') :=
    ind_etale_restrictScalars eR (CommAlgCat.of R S')
      (IsHenselization.ind_etale (R := R) (L := ResidueField R) (Rh := S))
  have hres := residueFieldMap_surjective_of_equiv eR eS (fun _ => rfl)
    (IsHenselization.residueField_map_bijective (R := R) (Rh := S)).2
  have hind' := (CommAlgCat.etale R').ind.prop_of_iso
    (CommAlgCat.isoMk (ULift.algEquiv (R := R') (A := S')).symm) hind
  let f : S' →ₐ[R'] T :=
    HenselianLocalRing.indEtaleAlgHom (R := R') (Rh := S') (Sh := T) hind' hres
  have hf : IsLocalHom f :=
    HenselianLocalRing.isLocalHom_indEtaleAlgHom (R := R') (Rh := S') (Sh := T) hind' hres
  have hfu : ∀ g : S' →ₐ[R'] T, IsLocalHom g → g = f :=
    HenselianLocalRing.indEtaleAlgHom_unique (R := R') (Rh := S') (Sh := T) hind' hres
  let : IsLocalHom f := hf
  let : IsLocalHom f.toRingHom := ⟨hf.map_nonunit⟩
  let f' : S →ₐ[R] T :=
    { toRingHom := f.toRingHom.comp eS.symm.toRingHom
      commutes' := fun r => f.commutes (eR.symm r) }
  have hf' : IsLocalHom f'.toRingHom := RingHom.isLocalHom_comp _ _
  refine ⟨f', ⟨hf'.map_nonunit⟩, ?_⟩
  intro g hg
  let : IsLocalHom g := hg
  let : IsLocalHom g.toRingHom := ⟨hg.map_nonunit⟩
  let g' : S' →ₐ[R'] T :=
    { toRingHom := g.toRingHom.comp eS.toRingHom
      commutes' := fun r => g.commutes (eR r) }
  have hg' : IsLocalHom g'.toRingHom := RingHom.isLocalHom_comp _ _
  have heq : g' = f := hfu g' ⟨hg'.map_nonunit⟩
  ext s
  exact congrArg (fun k : S' →ₐ[R'] T => k (eS.symm s)) heq

/-- Two henselizations of the same local ring are isomorphic over it, whatever their
universes. -/
private theorem nonempty_henselization_algEquiv
    (A R S : Type*) [CommRing A] [IsLocalRing A]
    [CommRing R] [IsLocalRing R] [Algebra A R] [IsHenselization A (ResidueField A) R]
    [CommRing S] [IsLocalRing S] [Algebra A S] [IsHenselization A (ResidueField A) S] :
    Nonempty (R ≃ₐ[A] S) := by
  let : HenselianLocalRing R := IsHenselization.henselian (R := A) (L := ResidueField A)
  let : HenselianLocalRing S := IsHenselization.henselian (R := A) (L := ResidueField A)
  let : IsLocalHom (algebraMap A R) := IsHenselization.isLocalHom (L := ResidueField A)
  let : IsLocalHom (algebraMap A S) := IsHenselization.isLocalHom (L := ResidueField A)
  obtain ⟨f, hf, -⟩ := existsUnique_henselization_map A R S
  obtain ⟨g, hg, -⟩ := existsUnique_henselization_map A S R
  have hR := existsUnique_henselization_map A R R
  have hS := existsUnique_henselization_map A S S
  refine ⟨AlgEquiv.ofAlgHom f g (hS.unique ?_ ?_) (hR.unique ?_ ?_)⟩
  · exact ⟨fun x hx => hg.map_nonunit x (hf.map_nonunit (g x) hx)⟩
  · exact ⟨fun _ hx => hx⟩
  · exact ⟨fun x hx => hf.map_nonunit x (hg.map_nonunit (f x) hx)⟩
  · exact ⟨fun _ hx => hx⟩

/-! ### Invariance of universal catenarity under ring equivalences -/

/-- Catenarity is invariant under ring equivalences: the prime spectra are order isomorphic. -/
public theorem isCatenary_of_ringEquiv {R S : Type*} [CommRing R] [CommRing S]
    (e : R ≃+* S) (h : Ring.IsCatenary R) : Ring.IsCatenary S := by
  let f : PrimeSpectrum S ≃o PrimeSpectrum R := PrimeSpectrum.comapEquiv e.symm
  intro p q hpq
  exact Stacks.Catenary.SurjectiveImage.IsCatenaryAt.of_image f.toOrderEmbedding
    (by
      rw [show Set.range f.toOrderEmbedding = Set.univ from Set.range_eq_univ.2 f.surjective]
      exact Set.ordConnected_univ)
    (h (f p) (f q) (f.monotone hpq))

/-- Universal catenarity is invariant under ring equivalences between arbitrary universes. -/
private theorem isUniversallyCatenary_of_ringEquiv
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (e : R ≃+* S) (h : Ring.IsUniversallyCatenary R) : Ring.IsUniversallyCatenary S := by
  let : Algebra R S := e.toRingHom.toAlgebra
  have : Algebra.FiniteType R S := Algebra.FiniteType.of_surjective (Algebra.ofId R S) e.surjective
  intro T _ _ _
  let : Algebra R T := ((algebraMap S T).comp (algebraMap R S)).toAlgebra
  have : IsScalarTower R S T := IsScalarTower.of_algebraMap_eq' rfl
  have : Algebra.FiniteType R T :=
    Algebra.FiniteType.trans (inferInstance : Algebra.FiniteType R S) inferInstance
  have : Small.{u} T := Algebra.FiniteType.small (R := R) (S := T)
  have : Algebra.FiniteType R (Shrink.{u} T) :=
    Algebra.FiniteType.equiv inferInstance (Shrink.algEquiv R T).symm
  exact isCatenary_of_ringEquiv (Shrink.algEquiv R T).toRingEquiv (h (Shrink.{u} T))

/-! ### The Krull dimension of a henselization -/

/-- A Noetherian local ring and a henselization of it have the same Krull dimension: both have
the same completion, by `exists_ringEquiv_adicCompletion_of_isHenselization`, and completion
preserves the dimension of a Noetherian local ring.

This is the ordinary-henselization half of Stacks 06LK, whose home in the conceptual tree
belongs elsewhere and is deliberately left free: the statement is asserted here untagged, and
the tag is not claimed by this file. The strict-henselization half, `dim R = dim Rˢʰ`, does
*not* follow this way — a strict henselization has residue field `κ^sep`, so its completion is
not the completion of `R`. -/
@[sga "5 I 3.1.3" "special case"]
theorem ringKrullDim_eq_ringKrullDim_of_isHenselization
    (A Ah : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    [CommRing Ah] [IsLocalRing Ah] [Algebra A Ah]
    [IsHenselization A (ResidueField A) Ah] :
    ringKrullDim A = ringKrullDim Ah := by
  have : IsNoetherianRing Ah := isNoetherianRing_of_isHenselization A Ah
  obtain ⟨e, -⟩ := exists_ringEquiv_adicCompletion_of_isHenselization A Ah
  rw [_root_.ringKrullDim_adicCompletion_maximalIdeal (A := A),
    _root_.ringKrullDim_adicCompletion_maximalIdeal (A := Ah)]
  exact ringKrullDim_eq_of_ringEquiv e

/-! ### Universal catenarity from geometrically normal formal fibres -/

/-- If the radical of an ideal is prime, the spectrum of the quotient is equidimensional: it is
irreducible. -/
private theorem equidimensional_quotient_of_radical_isPrime {R : Type*} [CommRing R]
    (I : Ideal R) (hI : I.radical.IsPrime) :
    TopologicalSpace.Equidimensional (PrimeSpectrum (R ⧸ I)) := by
  let : I.radical.IsPrime := hI
  have hp : (I.radical.map (Ideal.Quotient.mk I)).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective
      (by rw [Ideal.mk_ker]; exact Ideal.le_radical)
  rw [Ideal.map_radical_of_surjective Ideal.Quotient.mk_surjective
    (by rw [Ideal.mk_ker]), Ideal.map_quotient_self] at hp
  have : IrreducibleSpace (PrimeSpectrum (R ⧸ I)) :=
    PrimeSpectrum.irreducibleSpace_iff_isPrime_nilradical.mpr hp
  exact TopologicalSpace.Equidimensional.of_preirreducibleSpace _

/-- A henselization `Rh` of `R` has a local `Rh`-algebra which is a henselization of `R` with
residue field the separable closure of that of `R`. -/
private theorem exists_isHenselization_separableClosure (R Rh : Type u) [CommRing R]
    [IsLocalRing R] [CommRing Rh] [IsLocalRing Rh] [Algebra R Rh]
    [IsHenselization R (ResidueField R) Rh] :
    ∃ (S : Type u) (_ : CommRing S) (_ : IsLocalRing S) (_ : Algebra R S) (_ : Algebra Rh S)
      (_ : IsScalarTower R Rh S) (_ : IsLocalHom (algebraMap Rh S)),
      IsHenselization R (SeparableClosure (ResidueField R)) S := by
  have : IsLocalHom (algebraMap R Rh) := IsHenselization.isLocalHom (L := ResidueField R)
  obtain ⟨S, h1, h2, h3, h4, h5, h6, hH, -, hInd, -, e⟩ :=
    IsLocalRing.exists_strictHenselization R Rh
    (IsHenselization.ind_etale_of_universe_le (R := R) (L := ResidueField R) (Rh := Rh))
    (IsHenselization.residueField_map_bijective (R := R) (Rh := Rh)).2
    (SeparableClosure (ResidueField R))
  let : CommRing S := h1
  let : IsLocalRing S := h2
  let : Algebra R S := h3
  exact ⟨S, h1, h2, h3, h4, h5, h6, IsHenselization.of_ind_etale hH hInd e⟩

/-- The case of Stacks 0C2F in which the henselization lives in the universe of the base ring. -/
private theorem isUniversallyCatenary_henselization_and_of_isUnibranch_sameUniverse
    (A Ah : Type u)
    [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    [CommRing Ah] [IsLocalRing Ah] [Algebra A Ah]
    [IsHenselization A (ResidueField A) Ah]
    (hformal : ∀ q : PrimeSpectrum A,
      Algebra.IsGeometricallyNormal q.asIdeal.ResidueField
        (q.asIdeal.Fiber (AdicCompletion (maximalIdeal A) A))) :
    Ring.IsUniversallyCatenary Ah ∧ (IsUnibranch A → Ring.IsUniversallyCatenary A) := by
  have : IsLocalHom (algebraMap A Ah) := IsHenselization.isLocalHom (L := ResidueField A)
  have : IsNoetherianRing Ah := isNoetherianRing_of_isHenselization A Ah
  let κsep := SeparableClosure (ResidueField A)
  obtain ⟨Ash, _, _, _, _, _, _, _⟩ := exists_isHenselization_separableClosure A Ah
  let B := AdicCompletion (maximalIdeal A) A
  let : HenselianLocalRing B :=
    henselianLocalRing_adicCompletion A (maximalIdeal A).fg_of_isNoetherianRing
  let : IsHenselization B (ResidueField B) B := isHenselization_self B
  let κBsep := SeparableClosure (ResidueField B)
  obtain ⟨Bsh, _, _, _, -, -, -, _⟩ := exists_isHenselization_separableClosure B B
  have hcount :=
    (isNagataRing_and_numberOfBranches_and_numberOfGeometricBranches_eq_adicCompletion
      A Ah B Ash Bsh κsep κBsep hformal).2.1
  obtain ⟨_, _, f, hf, _, hcriterion⟩ :=
    numberOfBranches_eq_completion_iff_radical_map_minimalPrime_isPrime A Ah
  obtain ⟨e, he⟩ := exists_ringEquiv_adicCompletion_of_isHenselization A Ah
  -- the comparison map of Stacks 0C29 is the one coming from `e`
  let f' : Ah →ₐ[A] B := { f with commutes' := hf }
  let g : Ah →ₐ[A] B :=
    { toRingHom := e.symm.toRingHom.comp (algebraMap Ah (AdicCompletion (maximalIdeal Ah) Ah))
      commutes' := fun x => e.injective (by simpa using (he x).symm) }
  have huniq := HenselianLocalRing.indEtaleAlgHom_unique (Sh := B)
    (IsHenselization.ind_etale (R := A) (L := ResidueField A) (Rh := Ah))
    (IsHenselization.residueField_map_bijective (R := A) (Rh := Ah)).2
  have hfg : f' = g :=
    (huniq f' ⟨(isLocalHom_of_isHenselization_algHom f').map_nonunit⟩).trans
      (huniq g ⟨(isLocalHom_of_isHenselization_algHom g).map_nonunit⟩).symm
  have hrad : ∀ q ∈ minimalPrimes Ah,
      (Ideal.map (algebraMap Ah (AdicCompletion (maximalIdeal Ah) Ah)) q).radical.IsPrime := by
    intro q hq
    have h := hcriterion.mp hcount q hq
    change (Ideal.map f'.toRingHom q).radical.IsPrime at h
    rw [hfg] at h
    have hm : Ideal.map e.toRingHom (Ideal.map g.toRingHom q) =
        Ideal.map (algebraMap Ah (AdicCompletion (maximalIdeal Ah) Ah)) q := by
      rw [Ideal.map_map]
      exact congrArg (fun k : Ah →+* AdicCompletion (maximalIdeal Ah) Ah => Ideal.map k q)
        (RingHom.ext fun x => e.apply_symm_apply _)
    have hker : RingHom.ker e.toRingHom = ⊥ := (RingHom.injective_iff_ker_eq_bot _).mp e.injective
    rw [← hm, ← Ideal.map_radical_of_surjective e.surjective (by rw [hker]; exact bot_le)]
    exact Ideal.map_isPrime_of_surjective (f := e.toRingHom) e.surjective
      (by rw [hker]; exact bot_le)
  refine ⟨(isUniversallyCatenary_iff_isFormallyCatenary Ah).2 fun q hq =>
    equidimensional_quotient_of_radical_isPrime _ (hrad q hq), fun huni => ?_⟩
  -- the unibranch case
  obtain ⟨q, hq, hqu⟩ := (isUnibranch_iff_henselization_has_unique_minimalPrime A Ah).1 huni
  apply (isUniversallyCatenary_iff_isFormallyCatenary A).2
  intro p hp
  have hsing : minimalPrimes Ah = {q} := Set.eq_singleton_iff_unique_mem.mpr ⟨hq, hqu⟩
  have hBcard : (minimalPrimes B).encard = 1 := by
    change (minimalPrimes Ah).encard = (minimalPrimes B).encard at hcount
    rw [← hcount, hsing, Set.encard_singleton]
  obtain ⟨Q, hQ⟩ := Set.encard_eq_one.mp hBcard
  have hnilBp : (nilradical B).IsPrime := by
    have hnilB : nilradical B = Q := by
      show (⊥ : Ideal B).radical = Q
      rw [← Ideal.sInf_minimalPrimes]
      show sInf (minimalPrimes B) = Q
      rw [hQ, sInf_singleton]
    rw [hnilB]
    exact (show Q ∈ minimalPrimes B by rw [hQ]; exact Set.mem_singleton Q).isPrime
  have hnilA : (nilradical A).IsPrime :=
    (Ideal.Quotient.isDomain_iff_prime (I := nilradical A)).mp huni.1
  have hp_eq : p = nilradical A := le_antisymm
    (hp.2 ⟨hnilA, bot_le⟩ (@nilradical_le_prime A _ p hp.isPrime))
    (@nilradical_le_prime A _ p hp.isPrime)
  have hmap : p.map (algebraMap A B) ≤ nilradical B := by
    rw [hp_eq]
    exact Ideal.map_le_iff_le_comap.mpr fun x hx => (show IsNilpotent x from hx).map _
  have hrad_eq : (p.map (algebraMap A B)).radical = nilradical B :=
    le_antisymm ((Ideal.IsPrime.radical_le_iff hnilBp).2 hmap) (Ideal.radical_mono bot_le)
  apply equidimensional_quotient_of_radical_isPrime
  exact hrad_eq ▸ hnilBp

/-- **Stacks 0C2F.** A Noetherian local ring with geometrically normal formal fibres has a
universally catenary henselization, and is itself universally catenary if it is unibranch. -/
@[stacks 0C2F]
public lemma isUniversallyCatenary_henselization_and_of_isUnibranch
    (A : Type u) (Ah : Type v)
    [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    [CommRing Ah] [IsLocalRing Ah] [Algebra A Ah]
    [IsHenselization A (ResidueField A) Ah]
    (hformal : ∀ q : PrimeSpectrum A,
      Algebra.IsGeometricallyNormal q.asIdeal.ResidueField
        (q.asIdeal.Fiber (AdicCompletion (maximalIdeal A) A))) :
    Ring.IsUniversallyCatenary Ah ∧ (IsUnibranch A → Ring.IsUniversallyCatenary A) := by
  obtain ⟨Rh, hRing, hAlg, hLocal, hMap, hHenselian, hInd, -, hRes⟩ :=
    IsLocalRing.exists_henselization A
  let : CommRing Rh := hRing
  let : Algebra A Rh := hAlg
  let : IsLocalRing Rh := hLocal
  let : IsLocalHom (algebraMap A Rh) := hMap
  let : IsHenselization A (ResidueField A) Rh := IsHenselization.of_ind_etale hHenselian hInd
    ⟨RingEquiv.ofBijective (ResidueField.map (algebraMap A Rh)) hRes,
      fun x => ResidueField.map_residue (algebraMap A Rh) x⟩
  obtain ⟨hRh, hA⟩ :=
    isUniversallyCatenary_henselization_and_of_isUnibranch_sameUniverse A Rh hformal
  obtain ⟨e⟩ := nonempty_henselization_algEquiv A Rh Ah
  exact ⟨isUniversallyCatenary_of_ringEquiv e.toRingEquiv hRh, hA⟩

end StacksDraft.Catenary

end
