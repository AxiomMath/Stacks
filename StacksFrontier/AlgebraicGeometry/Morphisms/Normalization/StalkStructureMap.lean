module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Normalization.StalkBaseChange

/-!
# The local rings of the normalization, compatibly with an affine structure morphism

Let `X` be a scheme whose quasi-compact opens have finitely many irreducible components, let `ν`
be its normalization and let `y` be a point of the normalization lying over `x`.  The local ring
`𝒪_{Y,y}` is a localization at a prime ideal of the integral closure `T` of `𝒪_{X,x}` in the
product of the residue fields of the minimal primes of `𝒪_{X,x}`.  **If moreover `X` is a scheme
over an affine scheme `Spec R`, that identification can be chosen compatibly with the two
structure maps of `R`**, the one into `𝒪_{Y,y}` given by the germ at `y` of the structure
morphism of `Y`, and the one into the localization of `T` given by the germ at `x` of the
structure morphism of `X` followed by the inclusion of `𝒪_{X,x}` into `T`.

## Main results

* `AlgebraicGeometry.Scheme.germ_stalkMap_square`: the commuting square of structure maps of `R`
  attached to a fibre product over `Spec 𝒪_{X,x}` whose source is identified with the spectrum
  of a ring over `𝒪_{X,x}`.
* `AlgebraicGeometry.Scheme`:
  `exists_ringEquiv_stalk_normalizationScheme_localizationAtPrime_germ`, the local ring of the
  normalization at a point over `x` is a localization at a prime of the integral closure of
  `𝒪_{X,x}` in the product of the residue fields of its minimal primes, by an isomorphism
  compatible with the structure maps of `R`.
* `exists_ringEquiv_localizationAtPrime_of_ringEquiv` and
  `exists_ringEquiv_localizationAtPrime_of_localizationAlgEquiv`: the two transports of a
  localization at a prime, along a ring isomorphism and through a localization of the base.
* `AlgebraicGeometry.Scheme`:
  `exists_ringEquiv_stalk_normalizationScheme_localizationAtPrime_germ_of_isLocalization`, the
  same conclusion with the integral closure of a ring `S` of which `𝒪_{X,x}` is a localization.
* `AlgebraicGeometry.Scheme`:
  `exists_ringEquiv_stalk_normalizationScheme_pullback_localizationAtPrime_germ`, the case of the
  base change of `X` along `Spec B ⟶ Spec A`, with the compatibility over `B`.

## References

* [Stacks Project, Tag 0C3B](https://stacks.math.columbia.edu/tag/0C3B)
* [Stacks Project, Tag 09IL](https://stacks.math.columbia.edu/tag/09IL)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

/-- **Transporting a localization at a prime along a ring isomorphism.** An isomorphism
`e : A ≃+* B` carries a prime `q` of `A` to a prime `p` of `B`, and the localization of `A` at
`q` is isomorphic to the localization of `B` at `p` by an isomorphism commuting with the two
localization maps and `e`. -/
theorem exists_ringEquiv_localizationAtPrime_of_ringEquiv {A B : Type u} [CommRing A]
    [CommRing B] (e : A ≃+* B) (q : PrimeSpectrum A) :
    ∃ p : PrimeSpectrum B, ∃ ψ : Localization.AtPrime q.asIdeal ≃+*
        Localization.AtPrime p.asIdeal,
      ∀ a : A, ψ (algebraMap A (Localization.AtPrime q.asIdeal) a) =
        algebraMap B (Localization.AtPrime p.asIdeal) (e a) := by
  let p : Ideal B := q.asIdeal.comap e.symm
  have hmap : q.asIdeal.primeCompl.map e.toMonoidHom = p.primeCompl := by
    ext z
    simp only [Submonoid.mem_map, Ideal.mem_primeCompl_iff, p, Ideal.mem_comap]
    refine ⟨?_, fun hz ↦ ⟨e.symm z, hz, e.apply_symm_apply z⟩⟩
    rintro ⟨a, ha, rfl⟩
    simpa using ha
  exact ⟨⟨p, Ideal.IsPrime.comap _⟩,
    IsLocalization.ringEquivOfRingEquiv (Localization.AtPrime q.asIdeal)
      (Localization.AtPrime p) e hmap, fun a => IsLocalization.ringEquivOfRingEquiv_eq hmap a⟩

/-- **Descending a localization at a prime through a localization of the base.** Let `C` be an
`S`-algebra, let `E` be an `S`-algebra and let `W` be the localization of `E` at the image of a
submonoid `M` of `S`, an algebra over both `C` and `E` compatibly with `S`.  If a ring `D` over
`C` is isomorphic to `W` as a `C`-algebra, then every prime `q` of `D` comes from a prime `p` of
`E` with the localization of `D` at `q` isomorphic to the localization of `E` at `p`, by an
isomorphism carrying the image of an element of `S` to the image of that element. -/
theorem exists_ringEquiv_localizationAtPrime_of_localizationAlgEquiv
    (S C D E W : Type u) [CommRing S] [CommRing C] [CommRing D] [CommRing E]
    [CommRing W] [Algebra S C] [Algebra C D] [Algebra S E] [Algebra C W] [Algebra E W]
    [Algebra S W] [IsScalarTower S C W] [IsScalarTower S E W] (M : Submonoid S)
    [IsLocalization (Algebra.algebraMapSubmonoid E M) W]
    (g : D ≃ₐ[C] W) (q : PrimeSpectrum D) :
    ∃ p : PrimeSpectrum E, ∃ ψ : Localization.AtPrime q.asIdeal ≃+*
        Localization.AtPrime p.asIdeal,
      ∀ s : S, ψ (algebraMap D (Localization.AtPrime q.asIdeal)
          (algebraMap C D (algebraMap S C s))) =
        algebraMap E (Localization.AtPrime p.asIdeal) (algebraMap S E s) := by
  classical
  obtain ⟨p₀, ψ₀, hψ₀⟩ := exists_ringEquiv_localizationAtPrime_of_ringEquiv g.toRingEquiv q
  have _hloc : IsLocalization.AtPrime (Localization.AtPrime p₀.asIdeal)
      (p₀.asIdeal.comap (algebraMap E W)) :=
    IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
      (Algebra.algebraMapSubmonoid E M) (Localization.AtPrime p₀.asIdeal) p₀.asIdeal
  refine ⟨⟨p₀.asIdeal.comap (algebraMap E W), Ideal.IsPrime.comap _⟩, ψ₀.trans
    (IsLocalization.algEquiv (p₀.asIdeal.comap (algebraMap E W)).primeCompl
      (Localization.AtPrime p₀.asIdeal)
      (Localization.AtPrime (p₀.asIdeal.comap (algebraMap E W)))).toRingEquiv, fun s => ?_⟩
  have hgc : g.toRingEquiv (algebraMap C D (algebraMap S C s)) =
      algebraMap C W (algebraMap S C s) := g.commutes _
  rw [RingEquiv.trans_apply, hψ₀, hgc, ← IsScalarTower.algebraMap_apply S C W,
    IsScalarTower.algebraMap_apply S E W,
    ← IsScalarTower.algebraMap_apply E W (Localization.AtPrime p₀.asIdeal)]
  exact (IsLocalization.algEquiv (p₀.asIdeal.comap (algebraMap E W)).primeCompl
    (Localization.AtPrime p₀.asIdeal)
    (Localization.AtPrime (p₀.asIdeal.comap (algebraMap E W)))).commutes _

namespace AlgebraicGeometry.Scheme

/-- **The structure maps of an affine base across a fibre product over a local ring.** Let
`h : X ⟶ Spec R` be a scheme over `Spec R`, let `x` be a point of `X`, let `ν : Y ⟶ X` be a
morphism and let `P` together with `pr : P ⟶ Y` and `sn : P ⟶ Spec 𝒪_{X,x}` be a commuting
square over `X`.  Suppose `P` is identified with `Spec T` for a ring `T` over `𝒪_{X,x}`, by an
isomorphism over `Spec 𝒪_{X,x}`.  Then at any point `w` of `P` the germ at `pr w` of the
structure map of `R` on `Y`, followed by the stalk map of `pr`, agrees with the germ at `x` of
the structure map of `R` on `X`, followed by the inclusion of `𝒪_{X,x}` into `T`, the map of `T`
into its localization at `w`, and the two isomorphisms identifying that localization with the
local ring of `P` at `w`. -/
theorem germ_stalkMap_square {X Y P : Scheme.{u}} {R : CommRingCat.{u}}
    (h : X ⟶ Spec R) (x : X) (ν : Y ⟶ X)
    (pr : P ⟶ Y) (sn : P ⟶ Spec (X.presheaf.stalk x))
    (hcond : pr ≫ ν = sn ≫ X.fromSpecStalk x)
    {T : CommRingCat.{u}} (ψ : X.presheaf.stalk x ⟶ T)
    (e : P ≅ Spec T) (he : e.hom ≫ Spec.map ψ = sn) (w : P) :
    haveI : (e.hom.base w).asIdeal.IsPrime := (e.hom.base w).isPrime
    ((Scheme.ΓSpecIso R).inv ≫ (ν ≫ h).appTop ≫
        Y.presheaf.germ ⊤ (pr.base w) trivial) ≫ pr.stalkMap w =
      ((Scheme.ΓSpecIso R).inv ≫ h.appTop ≫ X.presheaf.germ ⊤ x trivial) ≫ ψ ≫
        CommRingCat.ofHom (algebraMap T (Localization.AtPrime (e.hom.base w).asIdeal)) ≫
        (Spec.stalkIso T (e.hom.base w)).inv ≫ e.hom.stalkMap w := by
  simp only [Category.assoc]
  rw [Spec.algebraMap_stalkIso_inv_assoc (R := T) (x := e.hom.base w),
    Scheme.Hom.germ_stalkMap e.hom ⊤ w trivial]
  simp only [Hom.preimage_top]
  rw [Scheme.ΓSpecIso_inv_naturality_assoc, ← Scheme.Hom.comp_appTop_assoc, he,
    Scheme.Hom.germ_stalkMap pr ⊤ w trivial]
  simp only [Hom.preimage_top]
  rw [← Scheme.Hom.comp_appTop_assoc, ← Category.assoc pr ν h, hcond,
    Category.assoc sn (X.fromSpecStalk x) h, Scheme.Hom.comp_appTop_assoc,
    ← specMap_stalkStructureMap, ← Scheme.ΓSpecIso_inv_naturality_assoc]
  simp only [Category.assoc]

/-- **The local rings of the normalization, compatibly with an affine structure morphism.** Let
`X` be a scheme whose quasi-compact opens have finitely many irreducible components, let `x` be a
point of `X`, let `y` be a point of the normalization of `X` lying over `x`, and let
`h : X ⟶ Spec R` be a structure morphism to an affine scheme.  Then the local ring of the
normalization at `y` is the localization at a prime ideal of the integral closure of `𝒪_{X,x}` in
the product of the residue fields of the minimal primes of `𝒪_{X,x}`, by an isomorphism carrying
the germ at `y` of the structure map of `R` to the image of the germ at `x` of the structure map
of `R`. -/
theorem exists_ringEquiv_stalk_normalizationScheme_localizationAtPrime_germ (X : Scheme.{u})
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite)
    (x : X) (y : X.normalizationScheme hX) (hy : (normalization X hX).base y = x)
    {R : CommRingCat.{u}} (h : X ⟶ Spec R) :
    ∃ p : PrimeSpectrum ↥(integralClosure (X.presheaf.stalk x)
        (minimalPrimes.residueFieldProduct (X.presheaf.stalk x))),
      ∃ φ : (X.normalizationScheme hX).presheaf.stalk y ≃+* Localization.AtPrime p.asIdeal,
        ∀ r : R, φ (((Scheme.ΓSpecIso R).inv ≫ (normalization X hX ≫ h).appTop ≫
            (X.normalizationScheme hX).presheaf.germ ⊤ y trivial).hom r) =
          algebraMap ↥(integralClosure (X.presheaf.stalk x)
              (minimalPrimes.residueFieldProduct (X.presheaf.stalk x)))
            (Localization.AtPrime p.asIdeal)
            (algebraMap (X.presheaf.stalk x)
              ↥(integralClosure (X.presheaf.stalk x)
                (minimalPrimes.residueFieldProduct (X.presheaf.stalk x)))
              (((Scheme.ΓSpecIso R).inv ≫ h.appTop ≫
                X.presheaf.germ ⊤ x trivial).hom r)) := by
  obtain ⟨w, hw, hiso⟩ :=
    exists_point_pullback_fromSpecStalk_isIso_stalkMap (normalization X hX) x y hy
  have key₀ : ∃ e : (pullback (normalization X hX) (X.fromSpecStalk x) : Scheme.{u}) ≅
        Spec (CommRingCat.of ↥(integralClosure (X.presheaf.stalk x)
          (minimalPrimes.residueFieldProduct (X.presheaf.stalk x)))),
      e.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap (X.presheaf.stalk x)
        ↥(integralClosure (X.presheaf.stalk x)
          (minimalPrimes.residueFieldProduct (X.presheaf.stalk x))))) =
        pullback.snd (normalization X hX) (X.fromSpecStalk x) :=
    exists_iso_pullback_normalization_fromSpecStalk X hX x
  obtain ⟨e, he⟩ := key₀
  subst hw
  refine ⟨e.hom.base w,
    ((asIso ((pullback.fst (normalization X hX) (X.fromSpecStalk x)).stalkMap w)).trans
      ((asIso (e.hom.stalkMap w)).symm.trans
        (Spec.stalkIso _ (e.hom.base w)))).commRingCatIsoToRingEquiv, fun r => ?_⟩
  have hsq := germ_stalkMap_square (Y := X.normalizationScheme hX)
    (P := pullback (normalization X hX) (X.fromSpecStalk x)) h x (normalization X hX)
    (pullback.fst (normalization X hX) (X.fromSpecStalk x))
    (pullback.snd (normalization X hX) (X.fromSpecStalk x)) pullback.condition
    (CommRingCat.ofHom (algebraMap (X.presheaf.stalk x)
      ↥(integralClosure (X.presheaf.stalk x)
        (minimalPrimes.residueFieldProduct (X.presheaf.stalk x))))) e he w
  have h₂ := (Iso.eq_comp_inv (asIso ((pullback.fst (normalization X hX)
    (X.fromSpecStalk x)).stalkMap w))).mpr hsq
  refine Eq.trans (congrArg _ (DFunLike.congr_fun (CommRingCat.hom_ext_iff.mp h₂) r)) ?_
  exact RingEquiv.apply_symm_apply _ _

/-- **The local rings of the normalization described downstairs of a localization, compatibly
with an affine structure morphism.** Suppose in addition that `𝒪_{X,x}` is the localization at a
submonoid `M` of a ring `S` whose reduction has an artinian total ring of fractions, and that the
germ at `x` of the structure map of `R` factors through `S` by a ring map `ι`.  Then the local
ring of the normalization of `X` at a point `y` over `x` is the localization at a prime ideal of
the integral closure of `S` in the total ring of fractions of the reduction of `S`, by an
isomorphism carrying the germ at `y` of the structure map of `R` to the image of `ι`. -/
theorem exists_ringEquiv_stalk_normalizationScheme_localizationAtPrime_germ_of_isLocalization
    (X : Scheme.{u})
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite)
    (x : X) (S : Type u) [CommRing S] [Algebra S (X.presheaf.stalk x)] (M : Submonoid S)
    [IsLocalization M (X.presheaf.stalk x)]
    [IsArtinianRing (FractionRing (S ⧸ _root_.nilradical S))]
    (y : X.normalizationScheme hX) (hy : (normalization X hX).base y = x)
    {R : CommRingCat.{u}} (h : X ⟶ Spec R) (ι : R ⟶ CommRingCat.of S)
    (hι : ∀ r : R, ((Scheme.ΓSpecIso R).inv ≫ h.appTop ≫ X.presheaf.germ ⊤ x trivial).hom r =
      algebraMap S (X.presheaf.stalk x) (ι.hom r)) :
    ∃ p : PrimeSpectrum ↥(integralClosure S (FractionRing (S ⧸ _root_.nilradical S))),
      ∃ φ : (X.normalizationScheme hX).presheaf.stalk y ≃+* Localization.AtPrime p.asIdeal,
        ∀ r : R, φ (((Scheme.ΓSpecIso R).inv ≫ (normalization X hX ≫ h).appTop ≫
            (X.normalizationScheme hX).presheaf.germ ⊤ y trivial).hom r) =
          algebraMap ↥(integralClosure S (FractionRing (S ⧸ _root_.nilradical S)))
            (Localization.AtPrime p.asIdeal)
            (algebraMap S ↥(integralClosure S (FractionRing (S ⧸ _root_.nilradical S)))
              (ι.hom r)) := by
  classical
  obtain ⟨q, φ₀, hφ₀⟩ :=
    exists_ringEquiv_stalk_normalizationScheme_localizationAtPrime_germ X hX x y hy h
  obtain ⟨eLoc⟩ :=
    nonempty_algEquiv_integralClosure_fractionRing_reduction S (X.presheaf.stalk x) M
  let _ : Algebra (X.presheaf.stalk x) (Localization (Algebra.algebraMapSubmonoid
      ↥(integralClosure S (FractionRing (S ⧸ _root_.nilradical S))) M)) :=
    localizationAlgebra M ↥(integralClosure S (FractionRing (S ⧸ _root_.nilradical S)))
  have _ : IsScalarTower S (X.presheaf.stalk x) (Localization (Algebra.algebraMapSubmonoid
      ↥(integralClosure S (FractionRing (S ⧸ _root_.nilradical S))) M)) :=
    isScalarTower_localizationAlgebra M
      ↥(integralClosure S (FractionRing (S ⧸ _root_.nilradical S)))
  obtain ⟨p, ψ, hψ⟩ := exists_ringEquiv_localizationAtPrime_of_localizationAlgEquiv S
    (X.presheaf.stalk x)
    ↥(integralClosure (X.presheaf.stalk x)
      (minimalPrimes.residueFieldProduct (X.presheaf.stalk x)))
    ↥(integralClosure S (FractionRing (S ⧸ _root_.nilradical S)))
    (Localization (Algebra.algebraMapSubmonoid
      ↥(integralClosure S (FractionRing (S ⧸ _root_.nilradical S))) M)) M
    ((minimalPrimes.reductionFractionRingAlgEquivResidueFieldProduct (X.presheaf.stalk x)
      (finite_minimalPrimes_stalk X hX x)).mapIntegralClosure.symm.trans eLoc) q
  refine ⟨p, φ₀.trans ψ, fun r => ?_⟩
  have hcomp := (hφ₀ r).trans (congrArg (fun z : X.presheaf.stalk x =>
    algebraMap ↥(integralClosure (X.presheaf.stalk x)
        (minimalPrimes.residueFieldProduct (X.presheaf.stalk x)))
      (Localization.AtPrime q.asIdeal)
      (algebraMap (X.presheaf.stalk x) ↥(integralClosure (X.presheaf.stalk x)
        (minimalPrimes.residueFieldProduct (X.presheaf.stalk x))) z)) (hι r))
  exact (congrArg ψ hcomp).trans (hψ (ι.hom r))

section BaseChange

open scoped nonZeroDivisors TensorProduct

variable (A O K F B L : Type u) [CommRing A] [CommRing O] [CommRing K] [CommRing F]
  [CommRing B] [CommRing L] [Algebra A O] [Algebra A K] [Algebra A F] [Algebra A B]
  [Algebra A L] [Algebra K F] [Algebra K L] [Algebra O F] [Algebra B L]
  [IsScalarTower A O F] [IsScalarTower A K F] [IsScalarTower A B L] [IsScalarTower A K L]
  [IsArtinianRing F] [IsDomain O] [Module.Flat A B] [Module.Finite A B] [Module.Finite K L]
  [IsLocalization (nonZeroDivisors A) K]
  [IsLocalization (Algebra.algebraMapSubmonoid B (nonZeroDivisors A)) L]
  [IsLocalization (nonZeroDivisors O) F]

/-- **The local rings of the normalization of a base change, compatibly with the base.** Let `A`
be a ring with total ring of fractions `K`, let `B` be a finite flat `A`-algebra with `L` its
localization at the nonzero elements of `A`, let `f : X ⟶ Spec A` be a scheme over `A` and let
`W = X ×_{Spec A} Spec B` with first projection `pr` and second projection `sn`.  Assume the
quasi-compact opens of `W` have finitely many irreducible components, let `w` be a point of `W`
and suppose the local ring of `X` at `pr w` is isomorphic to a domain `O` over `A` with fraction
field `F`, by an isomorphism compatible with the structure maps of `A`.  Then the local ring of
the normalization of `W` at a point `y` over `w` is the localization at a prime ideal of the
integral closure of `O` in the reduction of `F ⊗[K] L`, by an isomorphism carrying the germ at
`y` of the structure map of `B` to the image of `B` in that integral closure. -/
theorem exists_ringEquiv_stalk_normalizationScheme_pullback_localizationAtPrime_germ
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A))
    (hW : ∀ U : (pullback f (Spec.map (CommRingCat.ofHom (algebraMap A B))) : Scheme.{u}).Opens,
      IsCompact (U : Set (pullback f (Spec.map (CommRingCat.ofHom (algebraMap A B)))
        : Scheme.{u})) → (irreducibleComponents U).Finite)
    (w : (pullback f (Spec.map (CommRingCat.ofHom (algebraMap A B))) : Scheme.{u}))
    (e : O ≃+* X.presheaf.stalk
      (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap A B))) w))
    (he : ∀ a : A, e (algebraMap A O a) =
      ((Scheme.ΓSpecIso (.of A)).inv ≫ f.appTop ≫ X.presheaf.germ ⊤
        (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap A B))) w) trivial).hom a)
    (y : (pullback f (Spec.map (CommRingCat.ofHom (algebraMap A B)))
      : Scheme.{u}).normalizationScheme hW)
    (hy : (normalization _ hW).base y = w) :
    letI := integralClosureTensorProductAlgebra A O K F B L
    ∃ p : PrimeSpectrum ↥(integralClosure O ((F ⊗[K] L) ⧸ _root_.nilradical (F ⊗[K] L))),
      ∃ φ : ((pullback f (Spec.map (CommRingCat.ofHom (algebraMap A B)))
          : Scheme.{u}).normalizationScheme hW).presheaf.stalk y ≃+*
          Localization.AtPrime p.asIdeal,
        ∀ b : B, φ (((Scheme.ΓSpecIso (.of B)).inv ≫ (normalization _ hW ≫
              pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap A B)))).appTop ≫
            ((pullback f (Spec.map (CommRingCat.ofHom (algebraMap A B)))
              : Scheme.{u}).normalizationScheme hW).presheaf.germ ⊤ y trivial).hom b) =
          algebraMap ↥(integralClosure O ((F ⊗[K] L) ⧸ _root_.nilradical (F ⊗[K] L)))
            (Localization.AtPrime p.asIdeal)
            (algebraMap (O ⊗[A] B)
              ↥(integralClosure O ((F ⊗[K] L) ⧸ _root_.nilradical (F ⊗[K] L)))
              ((Algebra.TensorProduct.includeRight : B →ₐ[A] O ⊗[A] B) b)) := by
  classical
  have _ := isArtinianRing_fractionRing_nilradicalQuotient_tensorProduct A O K F B L
  let _ := tensorProductFractionRingAlgebra A O K F B L
  let _ := integralClosureTensorProductAlgebra A O K F B L
  obtain ⟨ρ, M, hM, hι⟩ :
      ∃ (ρ : O ⊗[A] B →+* (pullback f (Spec.map (CommRingCat.ofHom (algebraMap A B)))
          : Scheme.{u}).presheaf.stalk w)
        (M : Submonoid (O ⊗[A] B)),
        @IsLocalization _ _ M _ _ ρ.toAlgebra ∧
        ∀ b : B, ((Scheme.ΓSpecIso (.of B)).inv ≫
            (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap A B)))).appTop ≫
            (pullback f (Spec.map (CommRingCat.ofHom (algebraMap A B)))
            : Scheme.{u}).presheaf.germ ⊤ w trivial).hom b =
          ρ ((Algebra.TensorProduct.includeRight : B →ₐ[A] O ⊗[A] B) b) := by
    let _ : Algebra A (X.presheaf.stalk
        (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap A B))) w)) :=
      ((Scheme.ΓSpecIso (.of A)).inv ≫ f.appTop ≫ X.presheaf.germ ⊤
        (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap A B))) w) trivial).hom.toAlgebra
    obtain ⟨ψ, -, hψr, hψloc⟩ := exists_isLocalization_atPrime_stalk_tensorProduct A B X f w
    let ea : O ≃ₐ[A] X.presheaf.stalk
        (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap A B))) w) :=
      AlgEquiv.ofRingEquiv (f := e) he
    let t := Algebra.TensorProduct.congr ea (AlgEquiv.refl : B ≃ₐ[A] B)
    let _ : Algebra (X.presheaf.stalk
        (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap A B))) w) ⊗[A] B)
        ((pullback f (Spec.map (CommRingCat.ofHom (algebraMap A B)))
          : Scheme.{u}).presheaf.stalk w) := ψ.toAlgebra
    have hlocS : IsLocalization (Ideal.comap ψ (IsLocalRing.maximalIdeal
        ((pullback f (Spec.map (CommRingCat.ofHom (algebraMap A B)))
          : Scheme.{u}).presheaf.stalk w))).primeCompl
        ((pullback f (Spec.map (CommRingCat.ofHom (algebraMap A B)))
          : Scheme.{u}).presheaf.stalk w) := hψloc
    let ρ : O ⊗[A] B →+* (pullback f (Spec.map (CommRingCat.ofHom (algebraMap A B)))
        : Scheme.{u}).presheaf.stalk w :=
      ψ.comp t.toRingEquiv.toRingHom
    let := ρ.toAlgebra
    refine ⟨ρ, _, IsLocalization.of_ringEquiv_left t.toRingEquiv
      (Submonoid.map_comap_eq_of_surjective t.toRingEquiv.surjective
        (Ideal.comap ψ (IsLocalRing.maximalIdeal
          ((pullback f (Spec.map (CommRingCat.ofHom (algebraMap A B)))
            : Scheme.{u}).presheaf.stalk w))).primeCompl)
      fun _ => rfl, fun b => ?_⟩
    have ht : t ((Algebra.TensorProduct.includeRight : B →ₐ[A] O ⊗[A] B) b) =
        (Algebra.TensorProduct.includeRight : B →ₐ[A] X.presheaf.stalk
          (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap A B))) w) ⊗[A] B) b := by
      simp [t, Algebra.TensorProduct.includeRight_apply]
    exact (DFunLike.congr_fun hψr b).symm.trans (congrArg ψ ht.symm)
  let := ρ.toAlgebra
  obtain ⟨p₀, φ₀, hφ₀⟩ :=
    exists_ringEquiv_stalk_normalizationScheme_localizationAtPrime_germ_of_isLocalization
    (pullback f (Spec.map (CommRingCat.ofHom (algebraMap A B)))) hW w (O ⊗[A] B) M y hy
    (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap A B))))
    (CommRingCat.ofHom (Algebra.TensorProduct.includeRight : B →ₐ[A] O ⊗[A] B).toRingHom) hι
  obtain ⟨gT⟩ := nonempty_algEquiv_integralClosure_fractionRing_tensorProduct A O K F B L
  obtain ⟨p, ψ₂, hψ₂⟩ := exists_ringEquiv_localizationAtPrime_of_ringEquiv gT.toRingEquiv p₀
  refine ⟨p, φ₀.trans ψ₂, fun b => ?_⟩
  have hgt : gT.toRingEquiv (algebraMap (O ⊗[A] B)
        ↥(integralClosure (O ⊗[A] B)
          (FractionRing ((O ⊗[A] B) ⧸ _root_.nilradical (O ⊗[A] B))))
        ((Algebra.TensorProduct.includeRight : B →ₐ[A] O ⊗[A] B) b)) =
      algebraMap (O ⊗[A] B) ↥(integralClosure O
        ((F ⊗[K] L) ⧸ _root_.nilradical (F ⊗[K] L)))
        ((Algebra.TensorProduct.includeRight : B →ₐ[A] O ⊗[A] B) b) := gT.commutes _
  exact ((congrArg ψ₂ (hφ₀ b)).trans (hψ₂ _)).trans
    (congrArg (algebraMap _ (Localization.AtPrime p.asIdeal)) hgt)

end BaseChange

end AlgebraicGeometry.Scheme

end
