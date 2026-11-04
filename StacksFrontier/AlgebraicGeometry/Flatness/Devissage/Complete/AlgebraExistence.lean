module

public import Mathlib.RingTheory.TensorProduct.Finite
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Flatness.Devissage.Complete.Existence
public import StacksFrontier.AlgebraicGeometry.Flatness.Devissage.Complete.SpecTranslation
public import StacksFrontier.RingTheory.Flat.ElementaryEtaleNeighborhood
public import StacksFrontier.AlgebraicGeometry.Modules.QuasicoherentPullbackScheme

/-!
# Existence of a complete dévissage after an elementary étale localization

Stacks 05I1 is the ring-level form of Stacks 05HR: for a finite type ring map `R → S`, a finite
`S`-module `M` and a prime `q` of `S`, there is an elementary étale localization `R → R'`,
`S → S'`, `q'`, `p'` of `R → S` at `q` (Stacks 05HW,
`Algebra.ElementaryEtaleLocalization`) such that `(M ⊗_S S')/S'/R'` has a complete dévissage at
`q'` in the sense of Stacks 05HZ (`Module.CompleteDevissageAt`).

The source proves it in one sentence: it is Stacks 05HR read through the dictionary of
Stacks 05I0. Both halves are available here —
`AlgebraicGeometry.hasEtaleNeighborhoodCompleteDevissageAt` is Stacks 05HR and
`AlgebraicGeometry.geometricCompleteDevissageAtGivesAlgebraic` is Stacks 05I0 (2) for a
ring map — so what this file supplies is the step the dictionary needs and the geometric statement
does not provide: the two elementary étale neighbourhoods of Stacks 05HR must be **affine**
before their rings of functions can be named.

That costs one lemma. A *nonempty* complete dévissage already forces its source and its base to
be affine, since the one-step dévissage of its first stage carries
`AlgebraicGeometry.OneStepDevissage.affine_X` and
`AlgebraicGeometry.OneStepDevissage.affine_S`; so only the empty dévissage has to be moved, and
there the module is zero and survives any shrinking. `U` and `V` are therefore replaced by
affine opens around their distinguished points, which are again elementary étale neighbourhoods
by `AlgebraicGeometry.EtaleNeighborhood.IsElementary.comp`, the source being shrunk inside the
inverse image of the shrunken target so that the comparison morphism restricts.

With both neighbourhoods affine, `R' = Γ(V, ⊤)` and `S' = Γ(U, ⊤)` and the elementary étale
localization is assembled from the square of rings of functions: the étale conditions are
`HasRingHomProperty.Spec_iff` for `AlgebraicGeometry.Etale`, and the two residue field
conditions are the scheme-theoretic ones read on `Spec` by
`AlgebraicGeometry.specResidueFieldMap_bridge`.

## Main definitions

* `AlgebraicGeometry.elementaryEtaleLocalizationOfSquare`: **the elementary étale localization
  of `R → S` at `q` attached to a compatible pair of affine elementary étale neighbourhoods**
  of the point of `q` and of its image.

## Main results

* `AlgebraicGeometry.residueFieldMap_bijective_of_specMap`: the map of residue fields which `f`
  induces on the corresponding primes is a bijection as soon as the geometric residue field map
  of `Spec f` at the point is an isomorphism.
* `AlgebraicGeometry.exists_isAffine_etaleNeighborhood_square`: a compatible pair of elementary
  étale neighbourhoods of a point and of its image may be shrunk to affine ones.
* `AlgebraicGeometry.isAffine_of_nonemptyCompleteDevissageAt`: a nonempty complete dévissage
  forces its source and its base to be affine.
* `AlgebraicGeometry.exists_isAffine_etaleNeighborhood_completeDevissageAt`: **Stacks 05HR with
  both neighbourhoods affine.**
* `AlgebraicGeometry.finiteType_appTop_of_isAffine`: a morphism of affine schemes locally of
  finite type is the spectrum of a ring map of finite type.
* `Module.exists_elementaryEtaleLocalization_completeDevissageAt`: **Stacks 05I1.**

## Implementation notes

Everything lives in a single universe. Stacks 05HR is a statement about `Scheme.{u}`, and the
rings of functions of a `Scheme.{u}` are in `Type u`, so the two upper rings of the localization
land in the universe of `R` and `S` whatever the universes those are given; a polymorphic
statement would have to resize them and would say nothing more.

The module `M` is also taken in that universe, because the dictionary of Stacks 05I0 for a ring
map, `AlgebraicGeometry.geometricCompleteDevissageAtGivesAlgebraic`, is stated for a module in
the universe of the rings — `AlgebraicGeometry.tilde` of a module over `R : CommRingCat.{u}` is
a `Scheme.{u}`-module only for a module in `Type u`.

The base change `M ⊗_S S'` is `TensorProduct S S' M`, whose `S'`-module structure is the one on
the left factor; the comparison with the inverse image of `AlgebraicGeometry.tilde M` is
`AlgebraicGeometry.pullbackTildeIso` (Stacks 01I9), whose value is `ModuleCat.extendScalars`,
and that agrees with `TensorProduct S S' M` on the nose because the algebra structure of the
localization is `RingHom.toAlgebra` of a concrete ring map.

The finite-type hypothesis of `Module.CompleteDevissageAt` for `R' → S'` is not available to a
consumer before the localization is chosen, so it is returned as part of the conclusion rather
than assumed.

## References

* [Stacks Project, Tag 05I1](https://stacks.math.columbia.edu/tag/05I1)
* [Stacks Project, Tag 05HR](https://stacks.math.columbia.edu/tag/05HR)
* [Stacks Project, Tag 05HW](https://stacks.math.columbia.edu/tag/05HW)
* [Stacks Project, Tag 05HZ](https://stacks.math.columbia.edu/tag/05HZ)
* [Stacks Project, Tag 05I0](https://stacks.math.columbia.edu/tag/05I0)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-! ### Residue fields on spectra -/

/-- An isomorphism of residue fields at a point of a spectrum is a bijection of the residue
fields of the two primes. -/
theorem residueFieldMap_bijective_of_specMap {R T : CommRingCat.{u}} (f : R ⟶ T) (z : Spec T)
    [IsIso ((Spec.map f).residueFieldMap z)] (p : Ideal R) [p.IsPrime]
    (hp : p = z.asIdeal.comap f.hom) :
    Function.Bijective (Ideal.ResidueField.map p z.asIdeal f.hom hp) := by
  have hc : (Spec.map f z).asIdeal = z.asIdeal.comap f.hom := by
    simpa only [Spec.map_apply] using PrimeSpectrum.comap_asIdeal f.hom z
  obtain rfl : p = (Spec.map f z).asIdeal := hp.trans hc.symm
  rw [← specResidueFieldMap_bridge f z]
  exact ConcreteCategory.bijective_of_isIso _

/-- The canonical identification of an affine scheme with the spectrum of its ring of functions
is étale, being an isomorphism and hence an open immersion. -/
theorem etale_isoSpec_inv (X : Scheme.{u}) [IsAffine X] : Etale X.isoSpec.inv := by
  have : IsOpenImmersion X.isoSpec.inv := inferInstance
  infer_instance

/-! ### Shrinking an elementary étale square to affine neighbourhoods -/

/-- Two compatible elementary étale neighbourhoods of a point and of its image may be shrunk to
affine ones: an affine open of the target around its distinguished point, and an affine open of
the inverse image of that open around the distinguished point of the source. An open subscheme
is an elementary étale neighbourhood of each of its points, so the shrunken neighbourhoods are
again elementary. -/
theorem exists_isAffine_etaleNeighborhood_square {X Y : Scheme.{u}} {x : X} {y : Y} (f : X ⟶ Y)
    (U : EtaleNeighborhood X x) (V : EtaleNeighborhood Y y) (h : U.scheme ⟶ V.scheme)
    (hsq : U.toBase ≫ f = h ≫ V.toBase) (hpt : h U.point = V.point)
    (hU : U.IsElementary) (hV : V.IsElementary) :
    ∃ (U' : EtaleNeighborhood X x) (V' : EtaleNeighborhood Y y) (g : U'.scheme ⟶ V'.scheme),
      U'.IsElementary ∧ V'.IsElementary ∧ (U'.toBase ≫ f = g ≫ V'.toBase) ∧
        (g U'.point = V'.point) ∧ IsAffine U'.scheme ∧ IsAffine V'.scheme ∧
        Nonempty (U' ⟶ U) := by
  obtain ⟨W, hWaff, hWmem, -⟩ :=
    exists_isAffineOpen_mem_and_subset (X := V.scheme) (x := V.point) (U := ⊤) trivial
  let V' : EtaleNeighborhood Y y :=
    V.comp (EtaleNeighborhood.ofEtale W.ι (⟨V.point, hWmem⟩ : W.toScheme))
  have hV' : V'.IsElementary :=
    hV.comp (EtaleNeighborhood.isElementary_ofEtale_of_isOpenImmersion W.ι _)
  have hqmem : U.point ∈ h ⁻¹ᵁ W := by
    show h U.point ∈ W
    rwa [hpt]
  obtain ⟨P, hPaff, hPmem, -⟩ :=
    exists_isAffineOpen_mem_and_subset (X := (h ⁻¹ᵁ W).toScheme)
      (x := (⟨U.point, hqmem⟩ : (h ⁻¹ᵁ W).toScheme)) (U := ⊤) trivial
  let U' : EtaleNeighborhood X x :=
    U.comp (EtaleNeighborhood.ofEtale (P.ι ≫ (h ⁻¹ᵁ W).ι)
      (⟨(⟨U.point, hqmem⟩ : (h ⁻¹ᵁ W).toScheme), hPmem⟩ : P.toScheme))
  have hU' : U'.IsElementary :=
    hU.comp (EtaleNeighborhood.isElementary_ofEtale_of_isOpenImmersion
      (P.ι ≫ (h ⁻¹ᵁ W).ι) _)
  refine ⟨U', V', P.ι ≫ (h ∣_ W), hU', hV', ?_, ?_, hPaff, hWaff,
    ⟨⟨P.ι ≫ (h ⁻¹ᵁ W).ι, rfl, rfl⟩⟩⟩
  · show ((P.ι ≫ (h ⁻¹ᵁ W).ι) ≫ U.toBase) ≫ f = _ ≫ W.ι ≫ V.toBase
    rw [Category.assoc, hsq]
    calc (P.ι ≫ (h ⁻¹ᵁ W).ι) ≫ h ≫ V.toBase
        = P.ι ≫ ((h ⁻¹ᵁ W).ι ≫ h) ≫ V.toBase := by simp
      _ = P.ι ≫ ((h ∣_ W) ≫ W.ι) ≫ V.toBase := by rw [morphismRestrict_ι]
      _ = (P.ι ≫ (h ∣_ W)) ≫ W.ι ≫ V.toBase := by simp
  · apply W.ι.isOpenEmbedding.injective
    show ((P.ι ≫ (h ∣_ W)) ≫ W.ι) U'.point = W.ι V'.point
    rwa [Category.assoc, morphismRestrict_ι]

/-- A nonempty complete dévissage forces its source and its base to be affine: the one-step
dévissage of the first stage of the chain has both. -/
theorem isAffine_of_nonemptyCompleteDevissageAt {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType] (x : X)
    (D : NonemptyCompleteDevissageAt f F x) : IsAffine X ∧ IsAffine S := by
  obtain ⟨⟨chain⟩, pointed⟩ := D
  cases pointed with
  | last _ stage _ _ | more _ stage _ _ _ _ _ _ =>
    exact ⟨stage.oneStep.affine_X, stage.oneStep.affine_S⟩

/-- **Stacks Project, Tag 05HR with affine neighbourhoods.** A finite type quasi-coherent module
on a scheme locally of finite type over `S` acquires a complete dévissage at a chosen point
after elementary étale neighbourhoods of that point and of its image which are *affine*.

A nonempty dévissage already has affine source and base; an empty one says that the module
pulls back to zero, which survives the shrinking of the neighbourhoods to affine opens. -/
theorem exists_isAffine_etaleNeighborhood_completeDevissageAt {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType] (x : X) :
    ∃ (U : EtaleNeighborhood X x) (V : EtaleNeighborhood S (f x)) (h : U.scheme ⟶ V.scheme),
      U.IsElementary ∧ V.IsElementary ∧ (U.toBase ≫ f = h ≫ V.toBase) ∧
        (h U.point = V.point) ∧ IsAffine U.scheme ∧ IsAffine V.scheme ∧
        ∃ (hft : LocallyOfFiniteType h)
          (hq : ((Scheme.Modules.pullback U.toBase).obj F).IsQuasicoherent)
          (hf : ((Scheme.Modules.pullback U.toBase).obj F).IsFiniteType),
          letI : LocallyOfFiniteType h := hft
          letI : ((Scheme.Modules.pullback U.toBase).obj F).IsQuasicoherent := hq
          letI : ((Scheme.Modules.pullback U.toBase).obj F).IsFiniteType := hf
          Nonempty (CompleteDevissageAt h ((Scheme.Modules.pullback U.toBase).obj F) U.point) := by
  obtain ⟨U, V, h, hU, hV, hsq, hpt, hft, hq, hf, ⟨D⟩⟩ :=
    hasEtaleNeighborhoodCompleteDevissageAt f F x
  let : LocallyOfFiniteType h := hft
  let : ((Scheme.Modules.pullback U.toBase).obj F).IsQuasicoherent := hq
  let : ((Scheme.Modules.pullback U.toBase).obj F).IsFiniteType := hf
  cases D with
  | nonempty D =>
      obtain ⟨hX, hS⟩ := isAffine_of_nonemptyCompleteDevissageAt h _ U.point D
      exact ⟨U, V, h, hU, hV, hsq, hpt, hX, hS, hft, hq, hf, ⟨.nonempty D⟩⟩
  | empty hzero =>
      obtain ⟨U', V', g, hU', hV', hsq', hpt', hXa, hSa, ⟨j⟩⟩ :=
        exists_isAffine_etaleNeighborhood_square f U V h hsq hpt hU hV
      have : LocallyOfFiniteType (g ≫ V'.toBase) := by
        rw [← hsq']
        infer_instance
      have hftg : LocallyOfFiniteType g := locallyOfFiniteType_of_comp g V'.toBase
      have hq' : ((Scheme.Modules.pullback U'.toBase).obj F).IsQuasicoherent :=
        Stacks.Modules.isQuasicoherent_pullback U'.toBase F inferInstance
      have hf' : ((Scheme.Modules.pullback U'.toBase).obj F).IsFiniteType :=
        SheafOfModules.pullback_isFiniteType U'.toBase.toLRSHom.toShHom F
      refine ⟨U', V', g, hU', hV', hsq', hpt', hXa, hSa, hftg, hq', hf', ⟨.empty ?_⟩⟩
      exact ((Scheme.Modules.pullback j.hom).map_isZero hzero).of_iso
        (((Scheme.Modules.pullbackCongr j.over).app F).symm ≪≫
          ((Scheme.Modules.pullbackComp j.hom U.toBase).app F).symm)

/-! ### The square of rings of functions -/

/-- The spectrum of the ring map on global sections of a morphism of affine schemes, read
through the canonical identifications of the two schemes with the spectra of their rings of
functions. -/
theorem specMap_appTop_eq {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y] (f : X ⟶ Y) :
    Spec.map f.appTop = X.isoSpec.inv ≫ f ≫ Y.isoSpec.hom := by
  rw [← Scheme.isoSpec_hom_naturality]
  simp

/-- The spectrum of the ring map attached to a morphism from an affine scheme to an affine
spectrum is that morphism, read through the identification of the source with the spectrum of
its ring of functions. -/
theorem specMap_comp_appTop_eq {A : CommRingCat.{u}} {X : Scheme.{u}} [IsAffine X]
    (f : X ⟶ Spec A) :
    Spec.map ((Scheme.ΓSpecIso A).inv ≫ f.appTop) = X.isoSpec.inv ≫ f := by
  rw [Spec.map_comp, specMap_appTop_eq, ← Scheme.isoSpec_Spec_inv]
  simp

/-- A morphism of affine schemes locally of finite type is the spectrum of a ring map of finite
type. -/
theorem finiteType_appTop_of_isAffine {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y] (f : X ⟶ Y)
    [LocallyOfFiniteType f] :
    letI : Algebra ↥Γ(Y, ⊤) ↥Γ(X, ⊤) := f.appTop.hom.toAlgebra
    Algebra.FiniteType ↥Γ(Y, ⊤) ↥Γ(X, ⊤) := by
  let : Algebra ↥Γ(Y, ⊤) ↥Γ(X, ⊤) := f.appTop.hom.toAlgebra
  have : LocallyOfFiniteType (Spec.map f.appTop) := by
    rw [specMap_appTop_eq]
    infer_instance
  exact RingHom.finiteType_algebraMap.mp
    ((HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).1 this)

/-- **The elementary étale localization of `R → S` at `q` attached to a compatible pair of
affine elementary étale neighbourhoods** of the point of `q` in `Spec S` and of its image in
`Spec R`: the square of rings of functions, with the primes of the two distinguished points. -/
def elementaryEtaleLocalizationOfSquare {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (q : Ideal S) [q.IsPrime]
    (U : EtaleNeighborhood (Spec (.of S)) (⟨q, inferInstance⟩ : PrimeSpectrum S))
    (V : EtaleNeighborhood (Spec (.of R))
      (Spec.map (CommRingCat.ofHom (algebraMap R S)) (⟨q, inferInstance⟩ : PrimeSpectrum S)))
    [IsAffine U.scheme] [IsAffine V.scheme] (h : U.scheme ⟶ V.scheme)
    (hU : U.IsElementary) (hV : V.IsElementary)
    (hsq : U.toBase ≫ Spec.map (CommRingCat.ofHom (algebraMap R S)) = h ≫ V.toBase)
    (hpt : h U.point = V.point) :
    Algebra.ElementaryEtaleLocalization.{u, u, u, u} R S (q.under R) q := by
  let a : CommRingCat.of R ⟶ CommRingCat.of ↥Γ(V.scheme, ⊤) :=
    (Scheme.ΓSpecIso (.of R)).inv ≫ V.toBase.appTop
  let b : CommRingCat.of S ⟶ CommRingCat.of ↥Γ(U.scheme, ⊤) :=
    (Scheme.ΓSpecIso (.of S)).inv ≫ U.toBase.appTop
  let p' : PrimeSpectrum ↥Γ(V.scheme, ⊤) := V.scheme.isoSpec.hom V.point
  let q' : PrimeSpectrum ↥Γ(U.scheme, ⊤) := U.scheme.isoSpec.hom U.point
  have hap : Spec.map a = V.scheme.isoSpec.inv ≫ V.toBase := specMap_comp_appTop_eq _
  have hbp : Spec.map b = U.scheme.isoSpec.inv ≫ U.toBase := specMap_comp_appTop_eq _
  have hep : V.scheme.isoSpec.inv p' = V.point := by simp [p']
  have heq : U.scheme.isoSpec.inv q' = U.point := by simp [q']
  have hp : p'.asIdeal.comap a.hom = q.under R := by
    change ((Spec.map a) p').asIdeal = _
    rw [hap]
    change (V.toBase (V.scheme.isoSpec.inv p')).asIdeal = _
    rw [hep]
    exact congrArg PrimeSpectrum.asIdeal V.map_point
  have hq : q'.asIdeal.comap b.hom = q := by
    change ((Spec.map b) q').asIdeal = _
    rw [hbp]
    change (U.toBase (U.scheme.isoSpec.inv q')).asIdeal = _
    rw [heq]
    exact congrArg PrimeSpectrum.asIdeal U.map_point
  have hpq : q'.asIdeal.comap h.appTop.hom = p'.asIdeal := by
    change ((Spec.map h.appTop) q').asIdeal = _
    rw [specMap_appTop_eq]
    change (V.scheme.isoSpec.hom (h (U.scheme.isoSpec.inv q'))).asIdeal = _
    rw [heq, hpt]
  have hcomm : b.hom.comp (algebraMap R S) = h.appTop.hom.comp a.hom := by
    suffices he : CommRingCat.ofHom (algebraMap R S) ≫ b = a ≫ h.appTop from
      congrArg CommRingCat.Hom.hom he
    dsimp only [a, b]
    rw [← Category.assoc, Scheme.ΓSpecIso_inv_naturality, Category.assoc,
      ← Scheme.Hom.comp_appTop, hsq, Scheme.Hom.comp_appTop, Category.assoc]
  have hbres : IsIso ((Spec.map b).residueFieldMap q') := by
    rw [hbp, Scheme.residueFieldMap_comp]
    exact IsIso.comp_isIso'
      ((U.toBase.isIso_residueFieldMap_congr heq).mpr
        ((EtaleNeighborhood.isElementary_iff U).mp hU)) inferInstance
  have hares : IsIso ((Spec.map a).residueFieldMap p') := by
    rw [hap, Scheme.residueFieldMap_comp]
    exact IsIso.comp_isIso'
      ((V.toBase.isIso_residueFieldMap_congr hep).mpr
        ((EtaleNeighborhood.isElementary_iff V).mp hV)) inferInstance
  have hae : Etale (Spec.map a) := by
    rw [hap]
    exact @Etale.etale_comp _ _ V.scheme.isoSpec.inv _ V.toBase
      (etale_isoSpec_inv V.scheme) V.etale_toBase
  have hbe : Etale (Spec.map b) := by
    rw [hbp]
    exact @Etale.etale_comp _ _ U.scheme.isoSpec.inv _ U.toBase
      (etale_isoSpec_inv U.scheme) U.etale_toBase
  exact
    { R' := ↥Γ(V.scheme, ⊤)
      S' := ↥Γ(U.scheme, ⊤)
      algebraRR' := a.hom.toAlgebra
      algebraSS' := b.hom.toAlgebra
      algebraR'S' := h.appTop.hom.toAlgebra
      commutes := hcomm
      etale_R' := ((HasRingHomProperty.Spec_iff (P := @Etale)).mp hae).toAlgebra
      etale_S' := ((HasRingHomProperty.Spec_iff (P := @Etale)).mp hbe).toAlgebra
      p' := p'.asIdeal
      q' := q'.asIdeal
      p'_isPrime := p'.isPrime
      q'_isPrime := q'.isPrime
      p'_liesOver := hp.symm
      q'_liesOver_q := hq.symm
      q'_liesOver_p' := hpq.symm
      residueFieldMap_p_bijective := residueFieldMap_bijective_of_specMap a p' _ hp.symm
      residueFieldMap_q_bijective := residueFieldMap_bijective_of_specMap b q' _ hq.symm }

end AlgebraicGeometry

namespace Module

/-- **Stacks Project, Tag 05I1.** Let `R → S` be a ring map of finite type, let `M` be a finite
`S`-module and let `q` be a prime of `S`. There is an elementary étale localization of `R → S`
at `q` — rings `R'` and `S'`, primes `p'` and `q'` — such that `(M ⊗_S S')/S'/R'` has a complete
dévissage at `q'`.

The localized ring map `R' → S'` is again of finite type, which the definition of a complete
dévissage at a prime requires; it is returned with the dévissage because no consumer can state
it in advance of the localization. -/
@[stacks 05I1]
theorem exists_elementaryEtaleLocalization_completeDevissageAt (R S M : Type u) [CommRing R]
    [CommRing S] [Algebra R S] [Algebra.FiniteType R S] [AddCommGroup M] [Module S M]
    [Module.Finite S M] (q : Ideal S) [q.IsPrime] :
    ∃ E : Algebra.ElementaryEtaleLocalization.{u, u, u, u} R S (q.under R) q,
      ∃ hFiniteType : Algebra.FiniteType E.R' E.S',
        letI := hFiniteType
        Nonempty (Module.CompleteDevissageAt E.R' E.S' (TensorProduct S E.S' M) E.q') := by
  let f : Spec (.of S) ⟶ Spec (.of R) := Spec.map (CommRingCat.ofHom (algebraMap R S))
  let N : ModuleCat.{u} (CommRingCat.of S) := ModuleCat.of S M
  let F : (Spec (.of S)).Modules := tilde N
  let x : Spec (.of S) := ⟨q, inferInstance⟩
  have : LocallyOfFiniteType f := locallyOfFiniteType_specMap_algebraMap R S
  have : F.IsFiniteType := (tilde_isFiniteType_iff N).2 inferInstance
  obtain ⟨U, V, h, hU, hV, hsq, hpt, hUa, hVa, hft, hq, hf, ⟨D⟩⟩ :=
    exists_isAffine_etaleNeighborhood_completeDevissageAt f F x
  let : IsAffine U.scheme := hUa
  let : IsAffine V.scheme := hVa
  let : LocallyOfFiniteType h := hft
  let : ((Scheme.Modules.pullback U.toBase).obj F).IsQuasicoherent := hq
  let : ((Scheme.Modules.pullback U.toBase).obj F).IsFiniteType := hf
  let E := elementaryEtaleLocalizationOfSquare q U V h hU hV hsq hpt
  have hFT : Algebra.FiniteType E.R' E.S' := finiteType_appTop_of_isAffine h
  refine ⟨E, hFT, ?_⟩
  let : Algebra.FiniteType E.R' E.S' := hFT
  have hMfin : Module.Finite E.S' (TensorProduct S E.S' M) := Module.Finite.base_change S E.S' M
  -- The two identifications of the affine neighbourhoods with spectra.
  let eX : Spec (.of E.S') ≅ U.scheme := U.scheme.isoSpec.symm
  let eY : Spec (.of E.R') ≅ V.scheme := V.scheme.isoSpec.symm
  let b : CommRingCat.of S ⟶ CommRingCat.of E.S' :=
    (Scheme.ΓSpecIso (.of S)).inv ≫ U.toBase.appTop
  let q' : PrimeSpectrum E.S' := U.scheme.isoSpec.hom U.point
  -- The structure morphism of the localized situation, read on spectra.
  have hhom : eX.hom ≫ h ≫ eY.inv = Spec.map (CommRingCat.ofHom (algebraMap E.R' E.S')) :=
    (specMap_appTop_eq h).symm
  have : LocallyOfFiniteType (h ≫ eY.inv) := inferInstanceAs
    (LocallyOfFiniteType (h ≫ V.scheme.isoSpec.hom))
  have : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap E.R' E.S'))) :=
    locallyOfFiniteType_specMap_algebraMap E.R' E.S'
  have : (tilde (ModuleCat.of E.S' (TensorProduct S E.S' M))).IsFiniteType :=
    (tilde_isFiniteType_iff (ModuleCat.of E.S' (TensorProduct S E.S' M))).2 hMfin
  -- The module on the shrunken source is the base change of `M`.
  have hb : eX.hom ≫ U.toBase = Spec.map b :=
    (specMap_comp_appTop_eq U.toBase).symm
  let eF : (Scheme.Modules.pullback eX.hom).obj ((Scheme.Modules.pullback U.toBase).obj F) ≅
      tilde (ModuleCat.of E.S' (TensorProduct S E.S' M)) :=
    (Scheme.Modules.pullbackComp eX.hom U.toBase).app F ≪≫
      (Scheme.Modules.pullbackCongr hb).app F ≪≫
      (pullbackTildeIso (.of S) (.of E.S') b).app N
  -- Transport the dévissage to the spectra and read it algebraically.
  have hxpt : eX.hom q' = U.point := by
    show (U.scheme.isoSpec.hom ≫ U.scheme.isoSpec.inv) U.point = U.point
    rw [U.scheme.isoSpec.hom_inv_id]
    rfl
  exact geometricCompleteDevissageAtGivesAlgebraic E.R' E.S' (TensorProduct S E.S' M) q'
    ⟨(D.ofBaseIsoHom eY (by simp)).ofSourceIso eX hhom eF hxpt⟩

end Module

end
