module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.Restricted.FiniteTypeComposition
public import StacksFrontier.RingTheory.Rig.ClosedPoint.RestrictedPowerSeriesFlat
public import
  StacksFrontier.Topology.Algebra.AdicTopology.CompletedTensorProduct.RestrictedPowerSeriesMap

/-!
# Flatness of a completed tensor product at a rig-closed point

Let `A → B` be an adic homomorphism of Noetherian adic topological rings, complete along an
ideal of definition `I` of `A` and its extension `J = I · B`, and assume `A → B` is naively
rig-flat.  Let `C = A{σ}` be the restricted power series ring on a finite set of variables.
Then `C → B ⊗̂[A] C` is flat after localizing at any rig-closed prime whose contraction to `A`
is rig-closed.

## Main results

* `Rig.isMaximalAmongPrimesAvoiding_comap_of_isIntegral`: a prime of an intermediate ring is
  maximal among the primes avoiding the extended ideal once its contraction to the base is and
  the residue extension is integral.
* `Rig.isClosedPointAwayFrom_comap_of_isClosedPointAwayFrom`: rig-closedness passes to the
  prime cut out on an intermediate ring.
* `Rig.isClosedPointAwayFrom_comap_restrictedPowerSeries`: a rig-closed prime of `B{σ}` whose
  contraction to `A` is rig-closed cuts out rig-closed primes on `B` and on `A{σ}`.
* `Rig.flat_atPrime_comap_of_ringEquiv`: flatness of a localization at a prime travels along an
  isomorphism of the ring being localized.
* `Rig.flat_atPrime_completedTensorProduct_restrictedPowerSeries`: flatness of
  `A{σ} → B ⊗̂[A] A{σ}` at a rig-closed point.

## References

* [Stacks Project, Tag 0GGR](https://stacks.math.columbia.edu/tag/0GGR)
* [Stacks Project, Tag 0GGB](https://stacks.math.columbia.edu/tag/0GGB)
* [Stacks Project, Tag 0AMU](https://stacks.math.columbia.edu/tag/0AMU)
-/

@[expose] public section

open TopologicalRing RestrictedPowerSeries

namespace Rig

universe u

/-! ### Rig-closedness of the primes cut out on an intermediate ring -/

/-- **A prime of an intermediate ring is maximal among the primes avoiding the extended
ideal.**  For `A →+* S →+* T` and a prime `q` of `T`, the prime `q ∩ S` is maximal among the
primes of `S` avoiding `I · S` as soon as `q ∩ A` is maximal among the primes of `A` avoiding
`I` and the extension `A/(q ∩ A) → T/q` of residue rings is integral. -/
public theorem isMaximalAmongPrimesAvoiding_comap_of_isIntegral
    {A S T : Type*} [CommRing A] [CommRing S] [CommRing T]
    (I : Ideal A) (φ : A →+* S) (ψ : S →+* T)
    (q : Ideal T) [q.IsPrime]
    (hp : Ideal.IsMaximalAmongPrimesAvoiding I (q.comap (ψ.comp φ)))
    (hint : (Ideal.quotientMap (I := q.comap (ψ.comp φ)) q (ψ.comp φ) le_rfl).IsIntegral) :
    Ideal.IsMaximalAmongPrimesAvoiding (I.map φ) (q.comap ψ) := by
  have : (q.comap ψ).IsPrime := Ideal.comap_isPrime ψ q
  have hsφ : (q.comap ψ).comap φ = q.comap (ψ.comp φ) := Ideal.comap_comap φ ψ
  let πS : A ⧸ q.comap (ψ.comp φ) →+* S ⧸ q.comap ψ :=
    Ideal.quotientMap (q.comap ψ) φ (le_of_eq hsφ.symm)
  let ρ : S ⧸ q.comap ψ →+* T ⧸ q := Ideal.quotientMap q ψ le_rfl
  have hcomp : ρ.comp πS = Ideal.quotientMap (I := q.comap (ψ.comp φ)) q (ψ.comp φ) le_rfl :=
    Ideal.Quotient.ringHom_ext (RingHom.ext fun _ ↦ rfl)
  have hintS : πS.IsIntegral :=
    RingHom.IsIntegral.tower_bot πS ρ Ideal.quotientMap_injective (by rwa [hcomp])
  refine ⟨fun hle' ↦ hp.1 (hsφ ▸ Ideal.map_le_iff_le_comap.mp hle'), ?_⟩
  intro t ht hst htavoid
  have : t.IsPrime := ht
  have hcomapeq : t.comap φ = q.comap (ψ.comp φ) :=
    hp.2 _ (Ideal.comap_isPrime φ t) (hsφ ▸ Ideal.comap_mono hst)
      fun h ↦ htavoid (Ideal.map_le_iff_le_comap.mpr h)
  have : (q.comap (ψ.comp φ)).IsPrime := Ideal.comap_isPrime (ψ.comp φ) q
  let : Algebra (A ⧸ q.comap (ψ.comp φ)) (S ⧸ q.comap ψ) := πS.toAlgebra
  have : Algebra.IsIntegral (A ⧸ q.comap (ψ.comp φ)) (S ⧸ q.comap ψ) := ⟨hintS⟩
  have hkers : Ideal.comap (Ideal.Quotient.mk (q.comap ψ)) (⊥ : Ideal (S ⧸ q.comap ψ)) =
      q.comap ψ := by
    rw [← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
  have hKcomap : (t.map (Ideal.Quotient.mk (q.comap ψ))).comap
      (Ideal.Quotient.mk (q.comap ψ)) = t := by
    rw [Ideal.comap_map_of_surjective (Ideal.Quotient.mk (q.comap ψ))
      Ideal.Quotient.mk_surjective, hkers]
    exact sup_eq_left.mpr hst
  have hbot : (t.map (Ideal.Quotient.mk (q.comap ψ))).comap
      (algebraMap (A ⧸ q.comap (ψ.comp φ)) (S ⧸ q.comap ψ)) = ⊥ := by
    refine le_antisymm (fun x hx ↦ ?_) bot_le
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [Ideal.mem_comap, πS.algebraMap_toAlgebra] at hx
    rwa [Submodule.mem_bot, Ideal.Quotient.eq_zero_iff_mem, ← hcomapeq, Ideal.mem_comap,
      ← hKcomap]
  rw [← hKcomap, Ideal.eq_bot_of_under_eq_bot hbot, hkers]

/-- Closedness away from an adic ideal is closedness away from the topological nilradical. -/
private theorem isClosedPointAwayFrom_topologicalNilradical_iff
    {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
    (I : Ideal A) (hI : _root_.IsAdic I) (q : Ideal A) [q.IsPrime] :
    Ideal.IsClosedPointAwayFrom I q ↔ Ideal.IsClosedPointAwayFrom (topologicalNilradical A) q :=
  isClosedPointAwayFrom_congr_radical _ _ _
    ((radical_eq_topologicalNilradical_of_isAdic I hI).trans
      TopologicalRing.isRadical_topologicalNilradical.radical.symm)

/-- **Rig-closedness passes to the prime cut out on an intermediate ring.**  Let `A →+* S →+* T`
be homomorphisms whose composite `Φ` is adic, continuous and topologically of finite type
between Noetherian adic topological rings complete along `I` and `I · T`.  If a prime `q` of `T`
is rig-closed and so is its contraction to `A`, then `q ∩ S` is rig-closed for `I · S`. -/
public theorem isClosedPointAwayFrom_comap_of_isClosedPointAwayFrom
    {A S T : Type u} [CommRing A] [CommRing S] [CommRing T]
    [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A] [IsNoetherianRing A]
    [TopologicalSpace T] [IsTopologicalRing T] [IsLinearTopology T T] [IsNoetherianRing T]
    (I : Ideal A) (hI : _root_.IsAdic I) [IsAdicComplete I A]
    (φ : A →+* S) (ψ : S →+* T) (Φ : A →+* T) (hΦ : Φ = ψ.comp φ)
    (hmap : _root_.IsAdic (I.map Φ))
    (hcomplete : IsAdicComplete (I.map Φ) T)
    (hcont : Continuous Φ)
    (hft : TopologicalRing.IsTopologicallyOfFiniteType Φ)
    (q : Ideal T) [q.IsPrime]
    (hq : Ideal.IsClosedPointAwayFrom (I.map Φ) q)
    (hpA : Ideal.IsClosedPointAwayFrom I (q.comap Φ)) :
    letI : (q.comap ψ).IsPrime := Ideal.comap_isPrime ψ q
    Ideal.IsClosedPointAwayFrom (I.map φ) (q.comap ψ) := by
  subst hΦ
  let : IsAdicComplete (I.map (ψ.comp φ)) T := hcomplete
  have : (q.comap ψ).IsPrime := Ideal.comap_isPrime ψ q
  have hrel := rigPoint_relative_tfae
    (isWeaklyAdmissible_of_isAdicComplete I hI (isIdealOfDefinition_of_isAdic hI))
    (isWeaklyAdmissible_of_isAdicComplete (I.map (ψ.comp φ)) hmap
      (isIdealOfDefinition_of_isAdic hmap))
    (ψ.comp φ) hcont ⟨I, hI, hmap⟩ hft q
    ((isClosedPointAwayFrom_topologicalNilradical_iff _ hmap q).mp hq)
  have hfin := (hrel.out 2 3 (by rfl) (by rfl) (by decide) (by decide)).mp
    ((isClosedPointAwayFrom_topologicalNilradical_iff I hI _).mp hpA)
  exact (isClosedPointAway_iff_isMaximalAmongPrimesAvoiding (I.map φ) (q.comap ψ)).mpr
    (isMaximalAmongPrimesAvoiding_comap_of_isIntegral I φ ψ q
      ((isClosedPointAway_iff_isMaximalAmongPrimesAvoiding I (q.comap (ψ.comp φ))).mp hpA)
      (RingHom.IsIntegral.of_finite hfin))

/-- **The primes cut out on `B` and on `A{σ}` by a rig-closed prime of `B{σ}` whose contraction
to `A` is rig-closed are themselves rig-closed.** -/
public theorem isClosedPointAwayFrom_comap_restrictedPowerSeries
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A] [IsNoetherianRing A]
    [TopologicalSpace B] [IsTopologicalRing B] [IsLinearTopology B B] [IsNoetherianRing B]
    (I : Ideal A) (hI : _root_.IsAdic I) [IsAdicComplete I A]
    (hJ : _root_.IsAdic (I.map (algebraMap A B)))
    (σ : Type u) [Finite σ]
    (hcont : Continuous (algebraMap A B))
    (hft : TopologicalRing.IsTopologicallyOfFiniteType (algebraMap A B))
    (q : Ideal (RestrictedPowerSeries (I.map (algebraMap A B)) σ)) [q.IsPrime]
    (hq : Ideal.IsClosedPointAwayFrom
      ((I.map (algebraMap A B)).map (coefficientRingHom (I.map (algebraMap A B)) σ)) q)
    (hpA : Ideal.IsClosedPointAwayFrom I
      ((q.comap (TopologicalRing.restrictedPowerSeriesMap (B := B) I σ)).comap
        (coefficientRingHom I σ))) :
    Ideal.IsClosedPointAwayFrom (I.map (algebraMap A B))
        (q.comap (coefficientRingHom (I.map (algebraMap A B)) σ)) ∧
      Ideal.IsClosedPointAwayFrom (I.map (coefficientRingHom I σ))
        (q.comap (TopologicalRing.restrictedPowerSeriesMap (B := B) I σ)) := by
  classical
  let : TopologicalSpace (RestrictedPowerSeries (I.map (algebraMap A B)) σ) :=
    adicTopology (I.map (algebraMap A B)) σ
  let : IsTopologicalRing (RestrictedPowerSeries (I.map (algebraMap A B)) σ) :=
    adicIsTopologicalRing (I.map (algebraMap A B)) σ
  let : IsLinearTopology (RestrictedPowerSeries (I.map (algebraMap A B)) σ)
      (RestrictedPowerSeries (I.map (algebraMap A B)) σ) :=
    ((I.map (algebraMap A B)).map
      (coefficientRingHom (I.map (algebraMap A B)) σ)).isLinearTopology
  let : IsNoetherianRing (RestrictedPowerSeries (I.map (algebraMap A B)) σ) :=
    isNoetherianRing_restrictedPowerSeries (I.map (algebraMap A B)) σ
  have hIΦ : I.map ((coefficientRingHom (I.map (algebraMap A B)) σ).comp (algebraMap A B)) =
      (I.map (algebraMap A B)).map (coefficientRingHom (I.map (algebraMap A B)) σ) :=
    (Ideal.map_map (algebraMap A B) (coefficientRingHom (I.map (algebraMap A B)) σ)).symm
  have hmap : _root_.IsAdic
      (I.map ((coefficientRingHom (I.map (algebraMap A B)) σ).comp (algebraMap A B))) := by
    rw [hIΦ]; exact rfl
  have hcomplete : IsAdicComplete
      (I.map ((coefficientRingHom (I.map (algebraMap A B)) σ).comp (algebraMap A B)))
      (RestrictedPowerSeries (I.map (algebraMap A B)) σ) := by
    rw [hIΦ]; exact isAdicComplete_restrictedPowerSeries (I.map (algebraMap A B)) σ
  have hγcont : Continuous (coefficientRingHom (I.map (algebraMap A B)) σ) := by
    have h := (RingHom.continuous_adic_iff (coefficientRingHom (I.map (algebraMap A B)) σ)
        (I.map (algebraMap A B))
        ((I.map (algebraMap A B)).map (coefficientRingHom (I.map (algebraMap A B)) σ))).2
      ⟨1, by decide, fun x hx ↦
        Ideal.mem_map_of_mem (coefficientRingHom (I.map (algebraMap A B)) σ) (by simpa using hx)⟩
    exact Eq.mpr (congrArg (fun t ↦ @Continuous B (RestrictedPowerSeries
      (I.map (algebraMap A B)) σ) t (adicTopology (I.map (algebraMap A B)) σ)
      (coefficientRingHom (I.map (algebraMap A B)) σ)) hJ) h
  have hγft : TopologicalRing.IsTopologicallyOfFiniteType
      (coefficientRingHom (I.map (algebraMap A B)) σ) :=
    isTopologicallyOfFiniteType_coefficientRingHom (I.map (algebraMap A B)) σ
  have hΦcont : Continuous
      ((coefficientRingHom (I.map (algebraMap A B)) σ).comp (algebraMap A B)) :=
    hγcont.comp hcont
  have hΦft : TopologicalRing.IsTopologicallyOfFiniteType
      ((coefficientRingHom (I.map (algebraMap A B)) σ).comp (algebraMap A B)) :=
    isTopologicallyOfFiniteType_comp (coefficientRingHom (I.map (algebraMap A B)) σ)
      (algebraMap A B) hγcont hγft hft
  have hq' : Ideal.IsClosedPointAwayFrom
      (I.map ((coefficientRingHom (I.map (algebraMap A B)) σ).comp (algebraMap A B))) q := by
    rwa [hIΦ]
  have hΦ2 : (TopologicalRing.restrictedPowerSeriesMap (B := B) I σ).comp
      (coefficientRingHom I σ) =
      (coefficientRingHom (I.map (algebraMap A B)) σ).comp (algebraMap A B) :=
    RingHom.ext fun a ↦ TopologicalRing.restrictedPowerSeriesMap_coefficientRingHom I σ a
  have : (q.comap ((coefficientRingHom (I.map (algebraMap A B)) σ).comp
      (algebraMap A B))).IsPrime := Ideal.comap_isPrime _ _
  have hpA' : Ideal.IsClosedPointAwayFrom I
      (q.comap ((coefficientRingHom (I.map (algebraMap A B)) σ).comp (algebraMap A B))) := by
    refine (isClosedPointAway_iff_isMaximalAmongPrimesAvoiding I _).mpr ?_
    have h := (isClosedPointAway_iff_isMaximalAmongPrimesAvoiding I
      ((q.comap (TopologicalRing.restrictedPowerSeriesMap (B := B) I σ)).comap
        (coefficientRingHom I σ))).mp hpA
    rwa [Ideal.comap_comap, hΦ2] at h
  exact ⟨isClosedPointAwayFrom_comap_of_isClosedPointAwayFrom I hI (algebraMap A B)
      (coefficientRingHom (I.map (algebraMap A B)) σ) _ rfl hmap hcomplete hΦcont hΦft q hq' hpA',
    isClosedPointAwayFrom_comap_of_isClosedPointAwayFrom I hI (coefficientRingHom I σ)
      (TopologicalRing.restrictedPowerSeriesMap (B := B) I σ) _ hΦ2.symm hmap hcomplete
      hΦcont hΦft q hq' hpA'⟩

/-! ### Flatness of the completed tensor product -/

/-- **Flatness of a localization at a prime travels along an isomorphism of the ring being
localized.** -/
public theorem flat_atPrime_comap_of_ringEquiv {R R' S : Type u} [CommRing R] [CommRing R']
    [CommRing S] (e : R ≃+* R') (ι : S →+* R) (q : Ideal R') [q.IsPrime]
    (h : _root_.RingHom.Flat
      ((algebraMap R' (Localization.AtPrime q)).comp (e.toRingHom.comp ι))) :
    letI : (q.comap e.toRingHom).IsPrime := Ideal.comap_isPrime _ _
    _root_.RingHom.Flat
      ((algebraMap R (Localization.AtPrime (q.comap e.toRingHom))).comp ι) := by
  let : (q.comap e.toRingHom).IsPrime := Ideal.comap_isPrime _ _
  have hmon : (q.comap e.toRingHom).primeCompl.map (e : R ≃* R').toMonoidHom = q.primeCompl := by
    refine le_antisymm ?_ ?_
    · rintro y ⟨x, hx, rfl⟩
      exact hx
    · intro y hy
      refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
      change e.symm y ∉ q.comap e.toRingHom
      rwa [Ideal.mem_comap, show e.toRingHom (e.symm y) = y from e.apply_symm_apply y]
  let E : Localization.AtPrime (q.comap e.toRingHom) ≃+* Localization.AtPrime q :=
    IsLocalization.ringEquivOfRingEquiv (Localization.AtPrime (q.comap e.toRingHom))
      (Localization.AtPrime q) e hmon
  have hE : E.toRingHom.comp
      ((algebraMap R (Localization.AtPrime (q.comap e.toRingHom))).comp ι) =
      (algebraMap R' (Localization.AtPrime q)).comp (e.toRingHom.comp ι) :=
    RingHom.ext fun x ↦ IsLocalization.ringEquivOfRingEquiv_eq hmon (ι x)
  have hcancel : E.symm.toRingHom.comp (E.toRingHom.comp
      ((algebraMap R (Localization.AtPrime (q.comap e.toRingHom))).comp ι)) =
      (algebraMap R (Localization.AtPrime (q.comap e.toRingHom))).comp ι :=
    RingHom.ext fun x ↦ E.symm_apply_apply _
  have h' : _root_.RingHom.Flat (E.symm.toRingHom.comp
      ((algebraMap R' (Localization.AtPrime q)).comp (e.toRingHom.comp ι))) :=
    RingHom.Flat.respectsIso.1 _ E.symm h
  rwa [← hE, hcancel] at h'

open scoped TensorProduct

/-- **Flatness of `A{σ} → B ⊗̂[A] A{σ}` at a rig-closed point.**  Let `A → B` be a continuous
adic and naively rig-flat homomorphism of Noetherian adic topological rings, complete along an
ideal of definition `I` of `A` and its extension to `B`, and let `C = A{σ}` be the restricted
power series ring on a finite set of variables.  If `q` is a rig-closed prime of the
identification `B{σ}` of `B ⊗̂[A] C` whose contraction to `A` is rig-closed, then
`C → B ⊗̂[A] C` is flat after localizing at the prime `q` cuts out. -/
@[stacks 0GGR "the last step only: for `C` the restricted power series ring `A{σ}` on a finite \
set of variables rather than an arbitrary adic `A → C` of topologically finite type, and \
flatness of `C → B ⊗̂_A C` localized at one rig-closed prime whose contraction to `A` is also \
rig-closed, rather than rig-flatness of `C → B ⊗̂_A C`"]
public theorem flat_atPrime_completedTensorProduct_restrictedPowerSeries
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A] [IsNoetherianRing A]
    [TopologicalSpace B] [IsTopologicalRing B] [IsLinearTopology B B] [IsNoetherianRing B]
    (I : Ideal A) (hI : _root_.IsAdic I) [IsAdicComplete I A]
    (hJ : _root_.IsAdic (I.map (algebraMap A B)))
    [IsAdicComplete (I.map (algebraMap A B)) B]
    (σ : Type u) [Finite σ]
    (hcont : Continuous (algebraMap A B))
    (hflat : RingHom.IsNaivelyRigFlat (algebraMap A B))
    (q : Ideal (RestrictedPowerSeries (I.map (algebraMap A B)) σ)) [q.IsPrime]
    (hq : Ideal.IsClosedPointAwayFrom
      ((I.map (algebraMap A B)).map (coefficientRingHom (I.map (algebraMap A B)) σ)) q)
    (hpA : Ideal.IsClosedPointAwayFrom I
      ((q.comap (TopologicalRing.restrictedPowerSeriesMap (B := B) I σ)).comap
        (coefficientRingHom I σ))) :
    letI : IsLinearTopology (RestrictedPowerSeries I σ) (RestrictedPowerSeries I σ) :=
      RestrictedPowerSeries.isLinearTopology_restrictedPowerSeries I
        (Ideal.fg_of_isNoetherianRing I) σ
    letI : TopologicalSpace (B ⊗[A] RestrictedPowerSeries I σ) :=
      tensorProductTopology (R := A) (M := B) (N := RestrictedPowerSeries I σ)
    letI : UniformSpace (B ⊗[A] RestrictedPowerSeries I σ) :=
      tensorProductUniformSpace (R := A) (M := B) (N := RestrictedPowerSeries I σ)
    letI : IsTopologicalRing (B ⊗[A] RestrictedPowerSeries I σ) :=
      tensorProduct_isTopologicalRing (R := A) (A := B) (B := RestrictedPowerSeries I σ)
    letI : IsUniformAddGroup (B ⊗[A] RestrictedPowerSeries I σ) :=
      tensorProduct_isUniformAddGroup (R := A) (M := B) (N := RestrictedPowerSeries I σ)
    let e := completedTensorProductRestrictedEquiv I (Ideal.fg_of_isNoetherianRing I) σ hJ
    let ι : RestrictedPowerSeries I σ →+*
        CompletedTensorProduct (R := A) (M := B) (N := RestrictedPowerSeries I σ) :=
      (UniformSpace.Completion.coeRingHom).comp
        (Algebra.TensorProduct.includeRight (R := A) (A := B)
          (B := RestrictedPowerSeries I σ)).toRingHom
    letI : (q.comap e.toRingHom).IsPrime := Ideal.comap_isPrime _ _
    _root_.RingHom.Flat
      ((algebraMap (CompletedTensorProduct (R := A) (M := B) (N := RestrictedPowerSeries I σ))
        (Localization.AtPrime (q.comap e.toRingHom))).comp ι) := by
  let : IsLinearTopology (RestrictedPowerSeries I σ) (RestrictedPowerSeries I σ) :=
    RestrictedPowerSeries.isLinearTopology_restrictedPowerSeries I
      (Ideal.fg_of_isNoetherianRing I) σ
  let : TopologicalSpace (B ⊗[A] RestrictedPowerSeries I σ) :=
    tensorProductTopology (R := A) (M := B) (N := RestrictedPowerSeries I σ)
  let : UniformSpace (B ⊗[A] RestrictedPowerSeries I σ) :=
    tensorProductUniformSpace (R := A) (M := B) (N := RestrictedPowerSeries I σ)
  let : IsTopologicalRing (B ⊗[A] RestrictedPowerSeries I σ) :=
    tensorProduct_isTopologicalRing (R := A) (A := B) (B := RestrictedPowerSeries I σ)
  let : IsUniformAddGroup (B ⊗[A] RestrictedPowerSeries I σ) :=
    tensorProduct_isUniformAddGroup (R := A) (M := B) (N := RestrictedPowerSeries I σ)
  obtain ⟨hqB, hp⟩ := isClosedPointAwayFrom_comap_restrictedPowerSeries I hI hJ σ hcont
    hflat.2.1 q hq hpA
  refine flat_atPrime_comap_of_ringEquiv
    (completedTensorProductRestrictedEquiv I (Ideal.fg_of_isNoetherianRing I) σ hJ)
    ((UniformSpace.Completion.coeRingHom).comp
      (Algebra.TensorProduct.includeRight (R := A) (A := B)
        (B := RestrictedPowerSeries I σ)).toRingHom) q ?_
  rw [show (completedTensorProductRestrictedEquiv I
        (Ideal.fg_of_isNoetherianRing I) σ hJ).toRingHom.comp
        ((UniformSpace.Completion.coeRingHom).comp
          (Algebra.TensorProduct.includeRight (R := A) (A := B)
            (B := RestrictedPowerSeries I σ)).toRingHom) =
      restrictedPowerSeriesMap (B := B) I σ from
    RingHom.ext fun f ↦ completedTensorProductRestrictedEquiv_tmul_one I
      (Ideal.fg_of_isNoetherianRing I) σ hJ f]
  exact flat_atPrime_restrictedPowerSeriesMap_of_isNaivelyRigFlat I hI hJ σ hcont
    (isWeaklyAdmissible_of_isAdicComplete I hI (isIdealOfDefinition_of_isAdic hI))
    (isWeaklyAdmissible_of_isAdicComplete (I.map (algebraMap A B)) hJ
      (isIdealOfDefinition_of_isAdic hJ))
    ⟨I, hI, hJ⟩ hflat q hq hqB hp hpA

end Rig

end
