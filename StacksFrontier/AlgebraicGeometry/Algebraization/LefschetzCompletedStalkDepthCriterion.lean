module

public import StacksFrontier.AlgebraicGeometry.Algebraization.LefschetzSerreConditionSpecialCases
public import StacksFrontier.AlgebraicGeometry.Algebraization.DepthInequalities
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.FinitenessLocalCohomology.DepthDimAdicCompletion
public import StacksFrontier.AlgebraicGeometry.Variety.CohenMacaulayDepthDimensionBound
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteType.DimensionFormula
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Lipman.ExcellentStalks
public import StacksFrontier.RingTheory.Dualizing.UbiquityStability
public import StacksFrontier.RingTheory.Dualizing.Ubiquity
public import StacksFrontier.Algebra.Module.LocalizedRingEquiv
public import StacksFrontier.RingTheory.Depth.RingEquiv
public import StacksFrontier.AlgebraicGeometry.Chow.FibreCycles.StalkPrimes
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartierStalk.Stalkwise
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.Stabilization
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AlgebraizationDimensionBounds

/-!
# The criterion of Stacks 0EL5 from a pointwise depth bound

Let `X` be a scheme locally of finite type over a field `k`, `𝓘` a quasi-coherent sheaf of ideals
and `(𝓕ₙ)` an object of `Coh(X, 𝓘)`. The algebraization criterion of [Stacks, Tag 0EL5] asks, at
every `q ∈ V(𝓘)` and every prime `𝔭` of the `𝓘`-adic completion `𝒪_{X,q}^∧` not containing
`𝓘𝒪_{X,q}^∧`, that

`depth((𝓕_q^∧)_𝔭) + dim(𝒪_{X,q}^∧/𝔭) + dim({q}‾) > 2`.

This file derives that bound from the pointwise bound `depth(𝒪_{X,x}) + dim({x}‾) > 2` off `V(𝓘)`
when the completed stalks are free.

## Main results

* `Stacks.Algebraization.ringKrullDim_quotient_add_dimClosureAt` — for a prime `P` of `𝒪_{X,q}`
  defining a generization `x` of `q`, `dim(𝒪_{X,q}/P) + dim({q}‾) = dim({x}‾)`.
* `Stacks.Algebraization.depth_add_ringKrullDim_add_dimClosureAt_completedLocalRing` —
  `depth((𝒪_{X,q}^∧)_𝔭) + dim(𝒪_{X,q}^∧/𝔭) + dim({q}‾) = depth(𝒪_{X,x}) + dim({x}‾)` for the
  generization `x` cut out by `𝔭 ∩ 𝒪_{X,q}`: Stacks 0EHW read on `X`.
* `Stacks.Algebraization.two_lt_completedStalkDepth_add_of_two_lt_localDepthAddDimClosure` —
  the criterion of Stacks 0EL5 at `q` from the pointwise bound off `V(𝓘)` and freeness of the
  completed stalk.
* `Stacks.Algebraization.two_lt_enatToEInt_add_krullDimToEInt_add` — the same inequality read in
  the extended integers.

## References

* [Stacks Project, Tag 0EL5](https://stacks.math.columbia.edu/tag/0EL5), the criterion.
* [Stacks Project, Tag 0EL6](https://stacks.math.columbia.edu/tag/0EL6) and
  [Stacks Project, Tag 0EL7](https://stacks.math.columbia.edu/tag/0EL7), its applications.
* [Stacks Project, Tag 0EHW](https://stacks.math.columbia.edu/tag/0EHW), depth under completion.
* [Stacks Project, Tag 0BFR](https://stacks.math.columbia.edu/tag/0BFR), dualizing complexes.
* [Stacks Project, Tag 0A21](https://stacks.math.columbia.edu/tag/0A21), the dimension formula.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace AlgebraicGeometry IsLocalRing



attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.Algebraization

/-- The dimension of a subspace homeomorphic to a space through an embedding with that range. -/
theorem topologicalKrullDim_eq_of_isEmbedding {α β : Type*} [TopologicalSpace α]
    [TopologicalSpace β] {e : α → β} (he : Topology.IsEmbedding e) {S : Set β}
    (hS : Set.range e = S) : topologicalKrullDim α = topologicalKrullDim S := by
  subst hS
  exact IsHomeomorph.topologicalKrullDim_eq _ he.toHomeomorph.isHomeomorph

/-- The generic point of the reduced closure of `z` is `z` itself. -/
theorem subschemeι_genericPoint_reducedPointClosure (X : Scheme.{u}) (z : X)
    [IrreducibleSpace (reducedPointClosure X z).subscheme] :
    (reducedPointClosure X z).subschemeι
        (genericPoint (reducedPointClosure X z).subscheme) = z := by
  have hrange : Set.range (reducedPointClosure X z).subschemeι = (closure {z} : Set X) := by
    rw [Scheme.IdealSheafData.range_subschemeι, reducedPointClosure_support]
  have hgen := (genericPoint_spec (reducedPointClosure X z).subscheme).image
    (reducedPointClosure X z).subschemeι.continuous
  rw [show closure ((reducedPointClosure X z).subschemeι ''
      (Set.univ : Set (reducedPointClosure X z).subscheme)) = (closure {z} : Set X) by
    rw [Set.image_univ, hrange, closure_closure]] at hgen
  exact hgen.eq isGenericPoint_closure

/-- Let `P` be a prime of `𝒪_{X,q}` and `x` the point of `X` it defines. The local ring at `q` of
an integral closed subscheme `Z` of `X` with generic point `x` is `𝒪_{X,q} ⧸ P`. -/
theorem nonempty_ringEquiv_stalk_reducedPointClosure {X : Scheme.{u}} (q : X)
    (P : PrimeSpectrum (X.presheaf.stalk q)) (I : X.IdealSheafData) [IsIntegral I.subscheme]
    (hgen : I.subschemeι (genericPoint I.subscheme) = X.fromSpecStalk q P)
    (z : I.subscheme) (hz : I.subschemeι z = q) :
    Nonempty ((X.presheaf.stalk q ⧸ P.asIdeal) ≃+* I.subscheme.presheaf.stalk z) := by
  set φcat := (X.presheaf.stalkCongr (Inseparable.of_eq hz.symm)).hom ≫
    I.subschemeι.stalkMap z with hφcat
  have hsurj : Function.Surjective φcat.hom :=
    (I.subschemeι.stalkMap_surjective z).comp
      (ConcreteCategory.bijective_of_isIso
        (X.presheaf.stalkCongr (Inseparable.of_eq hz.symm)).hom).2
  have hpoint : X.fromSpecStalk q
      ((Spec.map φcat) (genericPoint (Spec (I.subscheme.presheaf.stalk z)))) =
      I.subschemeι (genericPoint I.subscheme) := by
    have hcongr : Spec.map (X.presheaf.stalkCongr (Inseparable.of_eq hz.symm)).hom ≫
        X.fromSpecStalk q = X.fromSpecStalk (I.subschemeι z) := by
      simpa [TopCat.Presheaf.stalkCongr] using
        (Scheme.SpecMap_stalkSpecializes_fromSpecStalk
          (X := X) (Inseparable.of_eq hz.symm).ge)
    have hdiag : Spec.map φcat ≫ X.fromSpecStalk q =
        I.subscheme.fromSpecStalk z ≫ I.subschemeι := by
      rw [hφcat, Spec.map_comp, Category.assoc, hcongr,
        Scheme.SpecMap_stalkMap_fromSpecStalk I.subschemeι]
    calc
      X.fromSpecStalk q
            ((Spec.map φcat) (genericPoint (Spec (I.subscheme.presheaf.stalk z)))) =
          (I.subscheme.fromSpecStalk z ≫ I.subschemeι)
            (genericPoint (Spec (I.subscheme.presheaf.stalk z))) := by
              rw [← Scheme.Hom.comp_apply, hdiag]
      _ = I.subschemeι (genericPoint I.subscheme) := by
            rw [Scheme.Hom.comp_apply, fromSpecStalk_genericPoint]
  have hpt : (Spec.map φcat) (genericPoint (Spec (I.subscheme.presheaf.stalk z))) = P :=
    (X.fromSpecStalk q).isEmbedding.injective (hpoint.trans hgen)
  have hq : P.asIdeal = RingHom.ker φcat.hom := by
    rw [← hpt, genericPoint_eq_bot_of_affine]
    show (PrimeSpectrum.comap φcat.hom
      (⊥ : PrimeSpectrum (I.subscheme.presheaf.stalk z))).asIdeal = _
    rw [PrimeSpectrum.comap_asIdeal, RingHom.ker_eq_comap_bot]
    rfl
  exact ⟨(Ideal.quotEquivOfEq hq).trans
    (RingHom.quotientKerEquivOfSurjective (f := φcat.hom) hsurj)⟩

/-- The point of `X` defined by a prime of `𝒪_{X,q}` specializes to `q`. -/
private theorem fromSpecStalk_specializes {X : Scheme.{u}} (q : X)
    (P : PrimeSpectrum (X.presheaf.stalk q)) : X.fromSpecStalk q P ⤳ q :=
  (Scheme.range_fromSpecStalk (x := q)).subset ⟨P, rfl⟩

/-- The local ring at the point defined by a prime `P` of `𝒪_{X,q}` is the localization at `P`. -/
private theorem isLocalization_stalk_fromSpecStalk {X : Scheme.{u}} (q : X)
    (P : PrimeSpectrum (X.presheaf.stalk q)) :
    letI : Algebra (X.presheaf.stalk q) (X.presheaf.stalk (X.fromSpecStalk q P)) :=
      (X.presheaf.stalkSpecializes (fromSpecStalk_specializes q P)).hom.toAlgebra
    IsLocalization.AtPrime (X.presheaf.stalk (X.fromSpecStalk q P)) P.asIdeal :=
  Chow.isLocalization_stalk_of_specializes _ P rfl

/-- **The dimension of a quotient of a local ring, along a generization.** Let `X` be locally of
finite type over a field, `q ∈ X`, and `P` a prime of `𝒪_{X,q}`, defining a generization `x` of
`q`. Then `dim(𝒪_{X,q} ⧸ P) + dim({q}‾) = dim({x}‾)`. -/
theorem ringKrullDim_quotient_add_dimClosureAt (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] (q : X)
    (P : PrimeSpectrum (X.presheaf.stalk q)) :
    ringKrullDim (X.presheaf.stalk q ⧸ P.asIdeal) + dimClosureAt X q =
      dimClosureAt X (X.fromSpecStalk q P) := by
  set x := X.fromSpecStalk q P with hx
  set Z := reducedPointClosure X x with hZ
  have hxq := fromSpecStalk_specializes q P
  have hrange : Set.range Z.subschemeι = closure ({x} : Set X) := by
    rw [Scheme.IdealSheafData.range_subschemeι, reducedPointClosure_support]
  have : IrreducibleSpace Z.subscheme :=
    Scheme.IdealSheafData.irreducibleSpace_subscheme X _ (by
      rw [hrange]; exact isIrreducible_singleton.closure)
  have : IsReduced Z.subscheme := Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal _
  have : IsIntegral Z.subscheme := isIntegral_of_irreducibleSpace_of_isReduced _
  obtain ⟨z, hz⟩ : q ∈ Set.range Z.subschemeι := by
    rw [hrange]; exact specializes_iff_mem_closure.mp hxq
  have hdim := ringKrullDim_stalk_add_dimClosureAt k Z.subscheme (Z.subschemeι ≫ f) z
  have hemb : Topology.IsClosedEmbedding Z.subschemeι.base :=
    IsClosedImmersion.isClosedEmbedding Z.subschemeι
  have hZdim : topologicalKrullDim Z.subscheme = dimClosureAt X x :=
    topologicalKrullDim_eq_of_isEmbedding hemb.isEmbedding hrange
  have hzdim : dimClosureAt Z.subscheme z = dimClosureAt X q := by
    refine topologicalKrullDim_eq_of_isEmbedding
      (hemb.isEmbedding.comp Topology.IsEmbedding.subtypeVal) ?_
    rw [Set.range_comp, Subtype.range_coe, ← hemb.closure_image_eq, Set.image_singleton]
    exact congrArg (fun t => closure ({t} : Set X)) hz
  obtain ⟨e⟩ := nonempty_ringEquiv_stalk_reducedPointClosure q P Z
    (subschemeι_genericPoint_reducedPointClosure X x) z hz
  rw [← hZdim, ← hzdim, ← hdim, ringKrullDim_eq_of_ringEquiv e]

/-- **Depth plus dimension at a prime of the completed local ring** ([Stacks, Tag 0EHW] read on a
scheme locally of finite type over a field). Let `q` be a point of the support of `𝓘`, `A` the
`𝓘`-adic completion of `𝒪_{X,q}`, `𝔭` a prime of `A` and `x` the point of `X` defined by the prime
`𝔭 ∩ 𝒪_{X,q}`. Then

`depth(A_𝔭) + dim(A/𝔭) + dim({q}‾) = depth(𝒪_{X,x}) + dim({x}‾)`. -/
theorem depth_add_ringKrullDim_add_dimClosureAt_completedLocalRing (k : Type u) [Field k]
    {X : Scheme.{u}} [IsLocallyNoetherian X] (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f]
    (J : X.IdealSheafData) {q : X} (hq : q ∈ J.support)
    (p : PrimeSpectrum (completedLocalRing J q)) :
    (Module.depth (Localization.AtPrime p.asIdeal) (maximalIdeal (Localization.AtPrime p.asIdeal))
          (LocalizedModule p.asIdeal.primeCompl (completedLocalRing J q)) : WithBot ℕ∞) +
        ringKrullDim (completedLocalRing J q ⧸ p.asIdeal) + dimClosureAt X q =
      (Module.depth (X.presheaf.stalk (X.fromSpecStalk q
            (PrimeSpectrum.comap (algebraMap (X.presheaf.stalk q) (completedLocalRing J q)) p)))
          (maximalIdeal (X.presheaf.stalk (X.fromSpecStalk q
            (PrimeSpectrum.comap (algebraMap (X.presheaf.stalk q) (completedLocalRing J q)) p))))
          (X.presheaf.stalk (X.fromSpecStalk q
            (PrimeSpectrum.comap (algebraMap (X.presheaf.stalk q) (completedLocalRing J q))
              p))) : WithBot ℕ∞) +
        dimClosureAt X (X.fromSpecStalk q
          (PrimeSpectrum.comap (algebraMap (X.presheaf.stalk q) (completedLocalRing J q)) p)) := by
  set P := PrimeSpectrum.comap (algebraMap (X.presheaf.stalk q) (completedLocalRing J q)) p
    with hP
  set x := X.fromSpecStalk q P with hx
  have hφ := AlgebraicGeometry.essFiniteType_stalkStructureMap f q
  let _ : Algebra k (X.presheaf.stalk q) := ((f.stalkMap q).hom.comp
    ((Scheme.ΓSpecIso (.of k)).inv ≫
      (Spec (.of k)).presheaf.germ ⊤ (f.base q) (by simp)).hom).toAlgebra
  obtain ⟨_, K, hK⟩ := Dualizing.exists_isDualizingComplex_of_essentiallyOfFiniteType
    (AlgebraicGeometry.isEssentiallyOfFiniteType_of_essFiniteType hφ)
    (Dualizing.exists_isDualizingComplex k)
  have hJ : IdealSheafData.stalk J q ≤ maximalIdeal (X.presheaf.stalk q) :=
    le_maximalIdeal fun h => (IdealSheafData.stalk_eq_top_iff_notMem_support J q).mp h hq
  have : p.asIdeal.LiesOver P.asIdeal := ⟨rfl⟩
  have h0EHW := Module.depth_add_ringKrullDim_quotient_adicCompletion (X.presheaf.stalk q)
    ⟨K, hK⟩ (IdealSheafData.stalk J q) hJ (X.presheaf.stalk q) P.asIdeal p.asIdeal
  have hxq := fromSpecStalk_specializes q P
  let _ : Algebra (X.presheaf.stalk q) (X.presheaf.stalk x) :=
    (X.presheaf.stalkSpecializes hxq).hom.toAlgebra
  have hloc := isLocalization_stalk_fromSpecStalk q P
  have hdepthP : Module.depth (Localization.AtPrime P.asIdeal)
        (maximalIdeal (Localization.AtPrime P.asIdeal))
        (LocalizedModule P.asIdeal.primeCompl (X.presheaf.stalk q)) =
      Module.depth (X.presheaf.stalk x) (maximalIdeal (X.presheaf.stalk x))
        (X.presheaf.stalk x) := by
    rw [Module.depth_eq_depth_of_linearEquiv _ (localizedRingEquiv P.asIdeal)]
    exact Module.depth_self_eq_of_ringEquiv
      (IsLocalization.algEquiv P.asIdeal.primeCompl (Localization.AtPrime P.asIdeal)
        (X.presheaf.stalk x)).toRingEquiv
  have hdim := ringKrullDim_quotient_add_dimClosureAt k f q P
  calc _ = ((Module.depth (Localization.AtPrime P.asIdeal)
            (maximalIdeal (Localization.AtPrime P.asIdeal))
            (LocalizedModule P.asIdeal.primeCompl (X.presheaf.stalk q)) : WithBot ℕ∞) +
          ringKrullDim (X.presheaf.stalk q ⧸ P.asIdeal)) + dimClosureAt X q :=
        congrArg (· + dimClosureAt X q) h0EHW
    _ = _ := by rw [hdepthP, add_assoc, hdim]

/-- **The generization defined by a prime off the completed ideal lies off the support.** If `𝔭`
is a prime of the `𝓘`-adic completion of `𝒪_{X,q}` not containing `𝓘𝒪_{X,q}^∧`, the point of `X`
defined by `𝔭 ∩ 𝒪_{X,q}` is not in the support of `𝓘`. -/
theorem fromSpecStalk_comap_notMem_support {X : Scheme.{u}} [IsLocallyNoetherian X]
    (J : X.IdealSheafData) (q : X) (p : PrimeSpectrum (completedLocalRing J q))
    (hp : ¬ completedLocalIdeal J q ≤ p.asIdeal) :
    X.fromSpecStalk q
        (PrimeSpectrum.comap (algebraMap (X.presheaf.stalk q) (completedLocalRing J q)) p) ∉
      J.support := by
  set P := PrimeSpectrum.comap (algebraMap (X.presheaf.stalk q) (completedLocalRing J q)) p
    with hP
  set x := X.fromSpecStalk q P with hx
  have hxq := fromSpecStalk_specializes q P
  let _ : Algebra (X.presheaf.stalk q) (X.presheaf.stalk x) :=
    (X.presheaf.stalkSpecializes hxq).hom.toAlgebra
  have hloc := isLocalization_stalk_fromSpecStalk q P
  obtain ⟨a, haJ, hap⟩ : ∃ a ∈ IdealSheafData.stalk J q, a ∉ P.asIdeal := by
    by_contra hcon
    push Not at hcon
    exact hp (Ideal.map_le_iff_le_comap.mpr hcon)
  rw [← IdealSheafData.stalk_eq_top_iff_notMem_support,
    Chow.idealStalk_eq_map_stalkSpecializes J hxq]
  refine Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_map_of_mem _ haJ) ?_
  exact IsLocalization.map_units (M := P.asIdeal.primeCompl) (X.presheaf.stalk x) ⟨a, hap⟩

/-- **The criterion of Stacks 0EL5 from the pointwise depth bound**. Let `X` be locally of finite
type over a field, `𝓘` a sheaf of ideals and `(𝓕ₙ)` an object of `Coh(X, 𝓘)` with free completed
stalk at `q ∈ V(𝓘)`. If `depth(𝒪_{X,x}) + dim({x}‾) > 2` at every point off `V(𝓘)`, then for every
prime `𝔭` of `𝒪_{X,q}^∧` not containing `𝓘𝒪_{X,q}^∧`,

`depth((𝓕_q^∧)_𝔭) + dim(𝒪_{X,q}^∧/𝔭) + dim({q}‾) > 2`. -/
theorem two_lt_completedStalkDepth_add_of_two_lt_localDepthAddDimClosure (k : Type u)
    [Field k] {X : Scheme.{u}} [IsLocallyNoetherian X] (f : X ⟶ Spec (.of k))
    [LocallyOfFiniteType f] (J : X.IdealSheafData) (F : Stacks.Coherent.CoherentAdicSystems J)
    (hdepth : ∀ x : X, x ∉ J.support → ((2 : ℕ) : WithBot ℕ∞) < localDepthAddDimClosure X x)
    {q : X} (hq : q ∈ J.support)
    (hfree : Module.Free (completedLocalRing J q) (completedStalk J F q))
    (p : PrimeSpectrum (completedLocalRing J q)) (hp : ¬ completedLocalIdeal J q ≤ p.asIdeal) :
    ((2 : ℕ) : WithBot ℕ∞) < (completedStalkDepth J F q p : WithBot ℕ∞) +
      ringKrullDim (completedLocalRing J q ⧸ p.asIdeal) + dimClosureAt X q := by
  have hx := hdepth _ (fromSpecStalk_comap_notMem_support J q p hp)
  rw [localDepthAddDimClosure,
    ← depth_add_ringKrullDim_add_dimClosureAt_completedLocalRing k f J hq p] at hx
  refine hx.trans_le (add_le_add_left (add_le_add_left (WithBot.coe_le_coe.mpr ?_) _) _)
  have : Module.Finite (completedLocalRing J q) (completedStalk J F q) :=
    finite_completedStalk J F q
  have : Module.Free (Localization.AtPrime p.asIdeal)
      (LocalizedModule p.asIdeal.primeCompl (completedStalk J F q)) :=
    Module.free_of_isLocalizedModule p.asIdeal.primeCompl
      (LocalizedModule.mkLinearMap p.asIdeal.primeCompl (completedStalk J F q))
  rw [completedStalkDepth, Module.depth_eq_depth_of_linearEquiv _ (localizedRingEquiv p.asIdeal)]
  exact AlgebraicGeometry.depth_le_depth_of_free _ _

/-! ### Reading the criterion in the extended integers -/

/-- On extended naturals, `krullDimToEInt` is `enatToEInt`. -/
theorem krullDimToEInt_coe (a : ℕ∞) : krullDimToEInt (a : WithBot ℕ∞) = enatToEInt a := by
  cases a using ENat.recTopCoe <;> rfl

/-- `krullDimToEInt` is additive. -/
theorem krullDimToEInt_add (b c : WithBot ℕ∞) :
    krullDimToEInt (b + c) = krullDimToEInt b + krullDimToEInt c := by
  cases b using WithBot.recBotCoe with
  | bot => rw [WithBot.bot_add]; rfl
  | coe b =>
  cases c using WithBot.recBotCoe with
  | bot =>
    rw [WithBot.add_bot]
    cases b using ENat.recTopCoe <;> rfl
  | coe c =>
  rw [← WithBot.coe_add]
  cases b using ENat.recTopCoe with
  | top =>
    rw [top_add]
    cases c using ENat.recTopCoe <;> rfl
  | coe b =>
    cases c using ENat.recTopCoe with
    | top => rw [add_top]; rfl
    | coe c =>
      show (((b + c : ℕ) : ℤ) : EInt) = ((b : ℤ) : EInt) + ((c : ℤ) : EInt)
      push_cast
      rfl

/-- **The criterion of Stacks 0EL5 in the extended integers.** A bound `2 < a + b + c` between a
depth `a` and two dimensions `b`, `c` in `WithBot ℕ∞` is the same bound after the passage to
`EInt` through `enatToEInt` and `krullDimToEInt`. -/
theorem two_lt_enatToEInt_add_krullDimToEInt_add {a : ℕ∞} {b c : WithBot ℕ∞}
    (h : ((2 : ℕ) : WithBot ℕ∞) < (a : WithBot ℕ∞) + b + c) :
    (2 : EInt) < enatToEInt a + krullDimToEInt b + krullDimToEInt c := by
  have h3 : ((3 : ℕ) : WithBot ℕ∞) ≤ (a : WithBot ℕ∞) + b + c := by
    generalize (a : WithBot ℕ∞) + b + c = v at h ⊢
    cases v using WithBot.recBotCoe with
    | bot => exact absurd h not_lt_bot
    | coe w => exact WithBot.coe_le_coe.mpr (Order.add_one_le_of_lt (WithBot.coe_lt_coe.mp h))
  have hm := krullDimToEInt_mono h3
  rw [krullDimToEInt_add, krullDimToEInt_add, krullDimToEInt_coe] at hm
  refine lt_of_lt_of_le ?_ hm
  show ((2 : ℤ) : EInt) < ((3 : ℤ) : EInt)
  exact WithBotTop.coe_lt_coe.mpr (by norm_num)

end Stacks.Algebraization

end
