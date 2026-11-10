module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LaumonFourierLineLisseFibre
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LaumonFourierLineLisseLattice
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ModuleTensor.ProjectionFormulaBaseChange

/-!
# The generic lisse locus of the Fourier family over the `(a, t)`-plane

Laumon's Fourier family ([Tag 03VH](https://stacks.math.columbia.edu/tag/03VH)) at fixed
`(k', a)` is `G_V = R¹g'_!(K|_{U'})`, `K = pr₁^*ℱ_σ ⊗ L_ψ'(a xⁿ + x t)` on `Spec k'[x][t]`. This
file shows that the family is lisse generically on the `(a, t)`-plane, uniformly in the finite
extension `k'` of `k` and in `a ∈ k'`, and on the generic part of each of the finitely many
special lines (`Stacks.EtaleCohomology.LaumonFourierLineLisseFibreInput`), assuming the lattice
comparison `Stacks.EtaleCohomology.LaumonFourierLineLatticeInput`: there are finitely many
constructible sheaves `Qᵢ` killed by `ℓ` on the model `Spec k[a][x][t]` over `k` such that, for
every `k'` and every `a₀ ∈ k'`, the level zero of the flat model of the `(k', a₀)`-family lies in
the closure under extensions and summands of the pullbacks of the `Qᵢ` along `a ↦ a₀`.

## Main definitions

* `Stacks.EtaleCohomology.laumonRingPlanePr₂`: the projection `Spec A[x][t] → Spec A[t]`.
* `Stacks.EtaleCohomology.laumonParamPlaneHom`: the morphism `Spec k'[x][t] → Spec k[a][x][t]`,
  `a ↦ a₀`, of the big étale site.
* `Stacks.EtaleCohomology.LaumonFourierLineLatticeInput`: the lattice comparison over the
  `(a, t)`-plane.

## Main results

* `Stacks.EtaleCohomology.isPullback_laumonRingPlane`: the plane over `A'` is the base change of
  the plane over `A` along the `t`-line.
* `Stacks.EtaleCohomology.laumonFourierLineLisseFibreInput_of_lattice`: the lattice comparison
  implies `Stacks.EtaleCohomology.LaumonFourierLineLisseFibreInput`.

## Implementation notes

`Stacks.EtaleCohomology.lowerShriekHomology` lives in the standard model
`HasDerivedCategory.standard` of the derived category, hence so do the statements of the last
section.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.SmallEtale Matrix
open CategoryTheory.LAdicTower

universe u

namespace Stacks.EtaleCohomology

section RingPlane

open Polynomial

variable {A A' : Type u} [CommRing A] [CommRing A'] (φ : A →+* A')

/-- **`A'[x][t]` is the pushout of `A[x][t] ← A[t] → A'[t]`**, for any ring map `φ : A → A'`: a
pair of ring maps from `A[x][t]` and `A'[t]` agreeing on `A[t]` extends uniquely to `A'[x][t]`. -/
public theorem isPushout_laumonRingPlane :
    IsPushout (CommRingCat.ofHom (mapRingHom (algebraMap A (Polynomial A))))
      (CommRingCat.ofHom (mapRingHom φ))
      (CommRingCat.ofHom (mapRingHom (mapRingHom φ)))
      (CommRingCat.ofHom (mapRingHom (algebraMap A' (Polynomial A')))) := by
  have hw : CommRingCat.ofHom (mapRingHom (algebraMap A (Polynomial A))) ≫
      CommRingCat.ofHom (mapRingHom (mapRingHom φ)) =
      CommRingCat.ofHom (mapRingHom φ) ≫
        CommRingCat.ofHom (mapRingHom (algebraMap A' (Polynomial A'))) := by
    ext : 1
    refine Polynomial.ringHom_ext (fun c => ?_) ?_ <;> simp
  refine IsPushout.of_isColimit (c := PushoutCocone.mk _ _ hw) ?_
  have hcond : ∀ s : PushoutCocone (CommRingCat.ofHom (mapRingHom (algebraMap A (Polynomial A))))
      (CommRingCat.ofHom (mapRingHom φ)), ∀ q : Polynomial A,
      s.inl.hom (q.map (algebraMap A (Polynomial A))) = s.inr.hom (q.map φ) :=
    fun s q => congrArg (fun ψ => ψ.hom q) s.condition
  let inner : ∀ s : PushoutCocone (CommRingCat.ofHom (mapRingHom (algebraMap A (Polynomial A))))
      (CommRingCat.ofHom (mapRingHom φ)), Polynomial A' →+* s.pt := fun s =>
    eval₂RingHom (s.inr.hom.comp Polynomial.C) (s.inl.hom (Polynomial.C Polynomial.X))
  refine PushoutCocone.IsColimit.mk _
    (fun s => CommRingCat.ofHom (eval₂RingHom (inner s) (s.inr.hom Polynomial.X)))
    (fun s => ?_) (fun s => ?_) (fun s m h₁ h₂ => ?_)
  · ext : 1
    refine Polynomial.ringHom_ext (fun q => ?_) ?_
    · refine RingHom.congr_fun (Polynomial.ringHom_ext (f := ((CommRingCat.ofHom
        (mapRingHom (mapRingHom φ)) ≫ CommRingCat.ofHom (eval₂RingHom (inner s)
          (s.inr.hom Polynomial.X))).hom.comp Polynomial.C))
        (g := s.inl.hom.comp Polynomial.C) (fun c => ?_) ?_) q
      · have := hcond s (Polynomial.C c)
        simp only [Polynomial.map_C, Polynomial.algebraMap_apply, Algebra.algebraMap_self,
          RingHom.id_apply] at this
        simp [inner, this]
      · simp [inner]
    · have := hcond s Polynomial.X
      simp only [Polynomial.map_X] at this
      simp [this]
  · ext : 1
    refine Polynomial.ringHom_ext (fun q => ?_) ?_
    · simp [inner]
    · simp
  · ext : 1
    refine Polynomial.ringHom_ext (fun q => ?_) ?_
    · refine RingHom.congr_fun (Polynomial.ringHom_ext (f := m.hom.comp Polynomial.C)
        (g := (eval₂RingHom (inner s) (s.inr.hom Polynomial.X)).comp Polynomial.C)
        (fun c => ?_) ?_) q
      · have := congrArg (fun ψ => ψ.hom (Polynomial.C c)) h₂
        simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.coe_comp,
          Function.comp_apply, coe_mapRingHom, Polynomial.map_C, Polynomial.algebraMap_apply,
          Algebra.algebraMap_self, RingHom.id_apply] at this
        simp [inner, this]
      · have := congrArg (fun ψ => ψ.hom (Polynomial.C Polynomial.X)) h₁
        simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.coe_comp,
          Function.comp_apply, coe_mapRingHom, Polynomial.map_C, Polynomial.map_X] at this
        simp [inner, this]
    · have := congrArg (fun ψ => ψ.hom Polynomial.X) h₂
      simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.coe_comp,
        Function.comp_apply, coe_mapRingHom, Polynomial.map_X] at this
      simp [this]

variable (A) in
/-- The second projection `pr₂ : Spec A[x][t] → Spec A[t]`, for a commutative ring `A`. -/
public abbrev laumonRingPlanePr₂ :
    Spec (.of (Polynomial (Polynomial A))) ⟶ Spec (.of (Polynomial A)) :=
  Spec.map (CommRingCat.ofHom (mapRingHom (algebraMap A (Polynomial A))))

/-- **The plane over `A'` is the base change of the plane over `A` along the `t`-line.** -/
public theorem isPullback_laumonRingPlane :
    IsPullback (Spec.map (CommRingCat.ofHom (mapRingHom (mapRingHom φ))))
      (laumonRingPlanePr₂ A') (laumonRingPlanePr₂ A)
      (Spec.map (CommRingCat.ofHom (mapRingHom φ))) :=
  isPullback_SpecMap_of_isPushout _ _ _ _ (isPushout_laumonRingPlane φ)

variable (A) in
/-- `A[t] → A[x][t]` is of finite type. -/
public theorem finiteType_mapRingHom_algebraMap_ring :
    (mapRingHom (algebraMap A (Polynomial A))).FiniteType := by
  refine RingHom.FiniteType.of_comp_finiteType (f := algebraMap A (Polynomial A)) ?_
  have h : (mapRingHom (algebraMap A (Polynomial A))).comp (algebraMap A (Polynomial A)) =
      algebraMap A (Polynomial (Polynomial A)) :=
    RingHom.ext fun _ => by simp
  rw [h]
  exact RingHom.finiteType_algebraMap.2 inferInstance

variable (A) in
/-- `pr₂ : Spec A[x][t] → Spec A[t]` is locally of finite type. -/
public theorem locallyOfFiniteType_laumonRingPlanePr₂ :
    LocallyOfFiniteType (laumonRingPlanePr₂ A) := by
  rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
  exact finiteType_mapRingHom_algebraMap_ring A

/-- **The preimage of `D(D₀)` along `Spec A'[t] → Spec A[t]`**: if a morphism `j` to
`Spec A'[t]` lands in `D(D₀ ⊗ A')`, then `j` followed by `Spec A'[t] → Spec A[t]` lands in
`D(D₀)`. -/
public theorem range_comp_specMap_mapRingHom_subset {X : Scheme.{u}}
    (j : X ⟶ Spec (.of (Polynomial A'))) (D₀ : Polynomial A)
    (h : Set.range j ⊆ (PrimeSpectrum.basicOpen (D₀.map φ) :
      Set (PrimeSpectrum (Polynomial A')))) :
    Set.range (j ≫ Spec.map (CommRingCat.ofHom (mapRingHom φ))) ⊆
      (PrimeSpectrum.basicOpen D₀ : Set (PrimeSpectrum (Polynomial A))) := by
  rintro _ ⟨y, rfl⟩
  exact h ⟨y, rfl⟩

/-- **The plane over `A'` is below the cutoff when the plane over `A` is, for `φ` surjective.** -/
public theorem schemeSizeBelow_laumonRingPlane_of_surjective (hφ : Function.Surjective φ)
    {κ : Cardinal.{u}} (hS : schemeSizeBelow κ (Spec (.of (Polynomial (Polynomial A))))) :
    schemeSizeBelow κ (Spec (.of (Polynomial (Polynomial A')))) := by
  change (Spec (.of (Polynomial (Polynomial A')))).size < κ
  change (Spec (.of (Polynomial (Polynomial A)))).size < κ at hS
  rw [Scheme.size_Spec] at hS ⊢
  refine lt_of_le_of_lt (max_le_max le_rfl ?_) hS
  exact Cardinal.mk_le_of_surjective (f := mapRingHom (mapRingHom φ))
    (Polynomial.map_surjective _ (Polynomial.map_surjective _ hφ))

variable (A) in
/-- **The line over `A` is below the cutoff when the plane over `A` is.** -/
public theorem schemeSizeBelow_laumonRingLine_of_laumonRingPlane {κ : Cardinal.{u}}
    (hS : schemeSizeBelow κ (Spec (.of (Polynomial (Polynomial A))))) :
    schemeSizeBelow κ (Spec (.of (Polynomial A))) := by
  change (Spec (.of (Polynomial A))).size < κ
  change (Spec (.of (Polynomial (Polynomial A)))).size < κ at hS
  rw [Scheme.size_Spec] at hS ⊢
  refine lt_of_le_of_lt (max_le_max le_rfl ?_) hS
  exact Cardinal.mk_le_of_injective
    (f := (Polynomial.C : Polynomial A →+* Polynomial (Polynomial A))) Polynomial.C_injective

end RingPlane

section ParamPlane

open Polynomial

variable (k k' : Type u) [Field k] [Field k'] [Algebra k k']

/-- **The model `Spec k[a][x][t]` is below the cutoff when the plane over `k'` is**: both rings
have cardinality `max #k ℵ₀ ≤ #k'[x][t]`. -/
public theorem schemeSizeBelow_laumonParamPlane_of_fieldExtension {κ : Cardinal.{u}}
    (hS : schemeSizeBelow κ (Spec (.of (Polynomial (Polynomial k'))))) :
    schemeSizeBelow κ (Spec (.of (Polynomial (Polynomial (Polynomial k))))) := by
  change (Spec (.of (Polynomial (Polynomial (Polynomial k))))).size < κ
  change (Spec (.of (Polynomial (Polynomial k')))).size < κ at hS
  rw [Scheme.size_Spec] at hS ⊢
  refine lt_of_le_of_lt (max_le (le_max_left _ _) ?_) hS
  have h1 : Cardinal.mk (Polynomial (Polynomial (Polynomial k))) ≤
      max (Cardinal.mk k) Cardinal.aleph0 := by
    refine Polynomial.cardinalMk_le_max.trans (max_le ?_ (le_max_right _ _))
    refine Polynomial.cardinalMk_le_max.trans (max_le ?_ (le_max_right _ _))
    exact Polynomial.cardinalMk_le_max
  have h2 : Cardinal.mk k ≤ Cardinal.mk (Polynomial (Polynomial k')) :=
    Cardinal.mk_le_of_injective (f := fun c : k => (C (C (algebraMap k k' c)) :
      Polynomial (Polynomial k')))
      (fun c c' h => (algebraMap k k').injective (C_injective (C_injective h)))
  exact h1.trans (max_le (h2.trans (le_max_right _ _)) (le_max_left _ _))

variable (B : BigEtaleSite.{u}) (a : k')
  (hS : schemeSizeBelow B.cutoff (Spec (.of (Polynomial (Polynomial k')))))
  (hS₀ : schemeSizeBelow B.cutoff (Spec (.of (Polynomial (Polynomial (Polynomial k))))))

/-- **`Spec k'[x][t] → Spec k[a][x][t]`, `a ↦ a₀`**, as a morphism of the big étale site: the
inclusion of the plane `a = a₀` of the model of the Fourier family over `k`, composed with the
constant field extension. -/
public abbrev laumonParamPlaneHom :
    Stacks.ArtinSchreier.specObject (Polynomial (Polynomial k')) B hS ⟶
      Stacks.ArtinSchreier.specObject (Polynomial (Polynomial (Polynomial k))) B hS₀ :=
  ObjectProperty.homMk (Spec.map (CommRingCat.ofHom
    (mapRingHom (mapRingHom (eval₂RingHom (algebraMap k k') a)))))

end ParamPlane

section Lattice

attribute [local instance] HasDerivedCategory.standard
  etaleModuleInverseImage_preservesFiniteLimits etaleModuleInverseImage_preservesFiniteColimits

/-- **The lattice comparison over the `(a, t)`-plane**: under the hypotheses of
`Stacks.EtaleCohomology.LaumonFourierLineLisseInput`, for every `n` (and when the model
`Spec k[a][x][t]` is below the cutoff of the site) there are finitely many constructible sheaves
`Qᵢ` on `Spec k[a][x][t]` killed by `ℓ` such that, for every finite extension `k'` of `k`, every
`a₀ ∈ k'` and all the data of the Fourier family `K` at `(k', a₀)`, the level zero of the flat
model of `K` lies in the closure under extensions and summands
(`Stacks.EtaleCohomology.IsExtensionSummandClosure`) of the pullbacks of the `Qᵢ` along
`a ↦ a₀` (`Stacks.EtaleCohomology.laumonParamPlaneHom`). -/
public def LaumonFourierLineLatticeInput : Prop :=
  ∀ (B : BigEtaleSite.{u}) (U : B.Scheme) (ℓ : ℕ)
    [∀ (n : ℕ) (S T : B.Scheme) (g : T ⟶ S),
      ((AlgebraicGeometry.smallEtaleBaseChange B g).sheafPushforwardContinuous
        (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
        (SmallEtale.topology B S.1 S.property)
        (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
    [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
      HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
        (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
    [∀ n : ℕ, HasWeakSheafify (SmallEtale.topology B U.1 U.property)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
    [IsNoetherian U.1] [Fact ℓ.Prime] [ConnectedSpace U.1]
    (k : Type u) [Field k] [Fintype k] (f : U.1 ⟶ Spec (.of k))
    [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f] [SmoothOfRelativeDimension 1 f]
    [IsAffine U.1] (e : U.1 ⟶ Spec (.of (Polynomial k))) [IsOpenImmersion e] [IsIso e]
    (_ : e ≫ Spec.map (CommRingCat.ofHom (algebraMap k (Polynomial k))) = f)
    (j : CompactificationOf (Over.mk f)) (kbar : Type u) [Field kbar] [Algebra k kbar]
    [IsAlgClosure k kbar]
    [ConnectedSpace ↥(Limits.pullback f (Spec.map (CommRingCat.ofHom (algebraMap k kbar))))]
    (p n : ℕ) [Fact p.Prime] [CharP k p] (_ : Fintype.card k = p ^ n) (_ : ℓ ≠ p)
    (x : GeometricPoint U.1)
    (E : Type) [Field E] [Algebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E] {d : ℕ}
    (b : Module.Basis (Fin d) ℚ_[ℓ] E) {m : ℕ} (σ : EtaleFundamentalGroup U.1 x →* GL (Fin m) E)
    (hσ : Continuous (restrictScalarsRep b σ)) (K : Type) [Field K] [IsAlgClosed K] [Algebra E K],
    (∀ W : Submodule K (Fin m → K),
      (∀ g, ∀ v ∈ W, (σ g).val.map (algebraMap E K) *ᵥ v ∈ W) → W = ⊥ ∨ W = ⊤) →
    LaumonStablyAbsIrr k e x σ → (∃ ζ : E, IsPrimitiveRoot ζ p) →
    ∀ (ι' : E →+* ℂ) (β : ℤ)
    [FiniteDimensional ℚ_[ℓ] (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B U ℓ f j
          kbar (LAdicSheaf.representationSheaf B U x (restrictScalarsRep b σ) hσ) 1)],
    (∀ (y : closedPoints U.1) (z : ℂ),
        ((σ (geometricFrobeniusFamily f x y)).val.charpoly.map ι').IsRoot z →
        ‖z‖ = ((p ^ n : ℕ) : ℝ) ^ (((residueDegree f y.1 : ℤ) * β : ℝ) / 2)) →
    ∀ ψ : AddChar k E, ψ ≠ 1 → ∀ n : ℕ,
    ∀ hS₀ : schemeSizeBelow B.cutoff (Spec (.of (Polynomial (Polynomial (Polynomial k))))),
    ∃ (ι : Type) (_ : Fintype ι)
      (Q : ι → EtaleModules.{u, 0} ℤ_[ℓ]
        (Stacks.ArtinSchreier.specObject (Polynomial (Polynomial (Polynomial k))) B hS₀).1),
      (∀ i, IsBigSiteConstructibleEtaleModule B _ ℤ_[ℓ] (Q i)) ∧ (∀ i, ℓ • 𝟙 (Q i) = 0) ∧
      ∀ (k' : Type u) [Field k'] [Fintype k'] [Algebra k k'] (a : k')
        (hS : schemeSizeBelow B.cutoff (Spec (.of (Polynomial (Polynomial k')))))
        (z : GeometricPoint (Spec (.of (Polynomial (Polynomial k')))))
        (hz : (z.map (laumonFamilyPr₁ k')).map (Spec.map (CommRingCat.ofHom
          (Polynomial.mapRingHom (algebraMap k k'))) ≫ inv e) = x)
        (pz : (finiteEtaleFiberFunctor z).obj
          (Stacks.ArtinSchreier.cover k' (Polynomial (Polynomial k'))
            (laumonFourierKernel k' n a)))
        (hσ₁ : Continuous (restrictScalarsRep b (σ.comp (hz ▸ (etaleFundamentalGroupMap
          (Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom (algebraMap k k'))) ≫ inv e)
            (z.map (laumonFamilyPr₁ k'))).toMonoidHom)))),
        haveI : IsNoetherian
            (Stacks.ArtinSchreier.specObject (Polynomial (Polynomial k')) B hS).1 :=
          inferInstanceAs (IsNoetherian (Spec (.of (Polynomial (Polynomial k')))))
        IsExtensionSummandClosure (fun A => ∃ i, Nonempty (A ≅
            (etaleModuleInverseImage.{u, 0} ℤ_[ℓ]
              (B.inclusion.map (laumonParamPlaneHom k k' B a hS hS₀))).obj (Q i)))
          (towerObj (LAdicSheaf.padicTower B _ ℓ (LAdicSheaf.flatModel B ℓ
            (laumonFourierFamilySheaf k' B hS b
              (ψ.compAddMonoidHom (Algebra.trace k k').toAddMonoidHom) n a z pz _
                hσ₁).toLAdicSheaf)) 0)

/-- **`m(a)` divides a lift of `P` only if `P` vanishes modulo `m`**: if `m(a) ∣ P(a, t)` in
`k[a, t]`, then the image of `P ∈ k[a][t]` in `(k[a]/(m))[t]` is zero. -/
public theorem map_quotient_eq_zero_of_aeval_X_zero_dvd {k : Type u} [Field k]
    (mk : Polynomial k) (P : Polynomial (Polynomial k))
    (h : Polynomial.aeval (MvPolynomial.X 0 : MvPolynomial (Fin 2) k) mk ∣ laumonIterToPlane P) :
    P.map (Ideal.Quotient.mk (Ideal.span {mk})) = 0 := by
  obtain ⟨g, hg⟩ := h
  have h1 := congrArg laumonPlaneToIter hg
  rw [laumonPlaneToIter_laumonIterToPlane, map_mul, ← laumonIterToPlane_C,
    laumonPlaneToIter_laumonIterToPlane] at h1
  rw [h1, Polynomial.map_mul, Polynomial.map_C,
    Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self mk), map_zero, zero_mul]

/-- **The Fourier family is lisse generically on the `(a, t)`-plane and on the special lines, from
the lattice comparison**: `Stacks.EtaleCohomology.LaumonFourierLineLatticeInput` implies
`Stacks.EtaleCohomology.LaumonFourierLineLisseFibreInput` (with `N = 0`). -/
public theorem laumonFourierLineLisseFibreInput_of_lattice
    (H : LaumonFourierLineLatticeInput.{u}) : LaumonFourierLineLisseFibreInput.{u} := by
  intro B U ℓ _ _ _ _ _ _ k _ _ f _ _ _ _ _ e _ _ hef j kbar _ _ _ _ p q _ _ hcard hℓp x E _ _ _
    d b m σ hσ K _ _ _ hirr hstab hζ ι' β hV hpure ψ hψ
  refine ⟨0, fun n _ _ mk hmk => ?_⟩
  classical
  let I : Ideal (Polynomial k) := Ideal.span {mk}
  have hIp : I.IsPrime := by
    rcases hmk with rfl | hirr'
    · rw [show I = ⊥ from Ideal.span_singleton_eq_bot.2 rfl]
      exact Ideal.isPrime_bot
    · exact (PrincipalIdealRing.isMaximal_of_irreducible hirr').isPrime
  by_cases hS₀ : schemeSizeBelow B.cutoff (Spec (.of (Polynomial (Polynomial (Polynomial k)))))
  swap
  · refine ⟨1, fun h1 => ?_, ?_⟩
    · have h2 := map_quotient_eq_zero_of_aeval_X_zero_dvd mk 1 (by rwa [map_one])
      rw [Polynomial.map_one] at h2
      exact one_ne_zero h2
    · intro k' _ _ _ a _ hS
      exact absurd (schemeSizeBelow_laumonParamPlane_of_fieldExtension k k' hS) hS₀
  have hSA : schemeSizeBelow B.cutoff (Spec (.of (Polynomial (Polynomial (Polynomial k ⧸ I))))) :=
    schemeSizeBelow_laumonRingPlane_of_surjective (Ideal.Quotient.mk I)
      Ideal.Quotient.mk_surjective hS₀
  have hLA := schemeSizeBelow_laumonRingLine_of_laumonRingPlane (Polynomial k ⧸ I) hSA
  obtain ⟨ι, _, Q, hQc, hQ, hcl⟩ := H B U ℓ k f e hef j kbar p q hcard hℓp x E b σ hσ K hirr
    hstab hζ ι' β hpure ψ hψ n hS₀
  let PA := Stacks.ArtinSchreier.specObject (Polynomial (Polynomial (Polynomial k ⧸ I))) B hSA
  let LA := Stacks.ArtinSchreier.specObject (Polynomial (Polynomial k ⧸ I)) B hLA
  let πρ : PA ⟶ Stacks.ArtinSchreier.specObject (Polynomial (Polynomial (Polynomial k))) B hS₀ :=
    ObjectProperty.homMk (Spec.map (CommRingCat.ofHom
      (Polynomial.mapRingHom (Polynomial.mapRingHom (Ideal.Quotient.mk I)))))
  let gA : PA ⟶ LA := ObjectProperty.homMk (laumonRingPlanePr₂ (Polynomial k ⧸ I))
  have : IsNoetherian PA.1 :=
    inferInstanceAs (IsNoetherian (Spec (.of (Polynomial (Polynomial (Polynomial k ⧸ I))))))
  have : LocallyOfFiniteType (B.inclusion.map gA) :=
    locallyOfFiniteType_laumonRingPlanePr₂ (Polynomial k ⧸ I)
  have : QuasiCompact (B.inclusion.map gA) :=
    inferInstanceAs (QuasiCompact (laumonRingPlanePr₂ (Polynomial k ⧸ I)))
  have : IsSeparated (B.inclusion.map gA) :=
    inferInstanceAs (IsSeparated (laumonRingPlanePr₂ (Polynomial k ⧸ I)))
  let Q' : ι → EtaleModules.{u, 0} ℤ_[ℓ] PA.1 := fun i =>
    (etaleModuleInverseImage.{u, 0} ℤ_[ℓ] (B.inclusion.map πρ)).obj (Q i)
  have hQ'c : ∀ i, IsBigSiteConstructibleEtaleModule B PA ℤ_[ℓ] (Q' i) := fun i =>
    isConstructibleEtaleModule_inverseImage B ℤ_[ℓ] πρ (hQc i)
  have hQ' : ∀ i, ℓ • 𝟙 (Q' i) = 0 := fun i => by
    simp only [Q']
    rw [← CategoryTheory.Functor.map_id, ← Functor.map_nsmul, hQ i, Functor.map_zero]
  obtain ⟨f₀, hf₀, hD⟩ := exists_ne_zero_forall_isFiniteTypeLocallyConstant_lowerShriekHomology B
    hLA gA Q' hQ'c ℓ (Fact.out : ℓ.Prime).pos hQ'
  obtain ⟨P, rfl⟩ := Polynomial.map_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective f₀
  refine ⟨laumonIterToPlane P, fun h => hf₀ (map_quotient_eq_zero_of_aeval_X_zero_dvd mk P h), ?_⟩
  intro k' _ _ _ a ha hS hL z hz pz hσ₁ V' U' _ _ jV' jU g' _ _ _ jg' hopen hrange hpb
  have : IsNoetherian (Stacks.ArtinSchreier.specObject (Polynomial (Polynomial k')) B hS).1 :=
    inferInstanceAs (IsNoetherian (Spec (.of (Polynomial (Polynomial k')))))
  have hIa : ∀ r ∈ I, Polynomial.eval₂RingHom (algebraMap k k') a r = 0 := by
    intro r hr
    obtain ⟨s, rfl⟩ := Ideal.mem_span_singleton'.1 hr
    have ha' : Polynomial.eval₂ (algebraMap k k') a mk = 0 := by rwa [← Polynomial.aeval_def]
    rw [map_mul, Polynomial.coe_eval₂RingHom, ha', mul_zero]
  let φ : Polynomial k ⧸ I →+* k' :=
    Ideal.Quotient.lift I (Polynomial.eval₂RingHom (algebraMap k k') a) hIa
  have hφ : φ.comp (Ideal.Quotient.mk I) = Polynomial.eval₂RingHom (algebraMap k k') a :=
    Ideal.Quotient.lift_comp_mk I _ hIa
  let π : Stacks.ArtinSchreier.specObject (Polynomial (Polynomial k')) B hS ⟶ PA :=
    ObjectProperty.homMk
      (Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom (Polynomial.mapRingHom φ))))
  let πt : Stacks.ArtinSchreier.specObject (Polynomial k') B hL ⟶ LA :=
    ObjectProperty.homMk (Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom φ)))
  let Pr : ObjectProperty (EtaleModules.{u, 0} ℤ_[ℓ] V'.1) :=
    Stacks.ConstantSheaf.IsFiniteTypeLocallyConstantModuleSheaf.{u, u + 1, 0}
      V'.1.smallEtaleTopology ℤ_[ℓ]
  have hpb' : IsPullback (B.inclusion.map (jU ≫ π)) (B.inclusion.map g')
      (B.inclusion.map gA) (B.inclusion.map (jV' ≫ πt)) :=
    hpb.paste_horiz (isPullback_laumonRingPlane φ)
  have hrange' : Set.range (B.inclusion.map (jV' ≫ πt)) ⊆
      (PrimeSpectrum.basicOpen (P.map (Ideal.Quotient.mk I)) :
        Set (PrimeSpectrum (Polynomial (Polynomial k ⧸ I)))) := by
    refine range_comp_specMap_mapRingHom_subset φ (B.inclusion.map jV') _ ?_
    rw [eval₂_laumonLine_eq_map, laumonPlaneToIter_laumonIterToPlane] at hrange
    rw [Polynomial.map_map, hφ]
    exact hrange
  let S' : ObjectProperty (EtaleModules.{u, 0} ℤ_[ℓ] U'.1) := fun A =>
    ∃ i, Nonempty (A ≅ (etaleModuleInverseImage.{u, 0} ℤ_[ℓ] (B.inclusion.map (jU ≫ π))).obj (Q' i))
  have hS' : ∀ A, S' A → ∀ s : ℤ,
      Pr ((lowerShriekHomology ℤ_[ℓ] (B.inclusion.map g') jg' s).obj A) := by
    rintro A ⟨i, ⟨eA⟩⟩ s
    exact Pr.prop_of_iso ((lowerShriekHomology ℤ_[ℓ] (B.inclusion.map g') jg' s).mapIso eA).symm
      (hD V' U' (jV' ≫ πt) (jU ≫ π) g' jg' hrange' hpb' i s)
  have hfac : B.inclusion.map (laumonParamPlaneHom k k' B a hS hS₀) =
      B.inclusion.map π ≫ B.inclusion.map πρ := by
    change Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, Polynomial.mapRingHom_comp,
      Polynomial.mapRingHom_comp, hφ]
  have hcl' := IsExtensionSummandClosure.map
    (etaleModuleInverseImage.{u, 0} ℤ_[ℓ] (B.inclusion.map jU)) (S' := S')
    (fun A ⟨i, ⟨eA⟩⟩ => .of_mem ⟨i, ⟨(etaleModuleInverseImage.{u, 0} ℤ_[ℓ]
      (B.inclusion.map jU)).mapIso (eA ≪≫ (etaleModuleInverseImageCompIso'.{u, 0} ℤ_[ℓ]
        (B.inclusion.map π) (B.inclusion.map πρ) _ hfac).app (Q i)) ≪≫
      ((etaleModuleInverseImageCompIso ℤ_[ℓ]
        (B.inclusion.map jU) (B.inclusion.map π)).app (Q' i)).symm⟩⟩)
    (hcl k' a hS z hz pz hσ₁)
  refine LAdicSheaf.isLisse_higherDirectImageShriek_of_levelZero B ℓ g' jg' _ (fun s => ?_) 1
  exact Pr.prop_of_iso
    ((lowerShriekHomology ℤ_[ℓ] (B.inclusion.map g') jg' s).mapIso
      (LAdicSheaf.flatModelLevelZeroInverseImageIso B ℓ jU _).symm)
    (forall_isFiniteTypeLocallyConstant_lowerShriekHomology_of_closure (B.inclusion.map g') jg'
      ℤ_[ℓ] hS' hcl' s)

end Lattice

end Stacks.EtaleCohomology

end
