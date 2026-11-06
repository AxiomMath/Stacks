module

public import StacksFrontier.Homology.DerivedCategory.InverseSystem.PerfectTower.Finiteness
import all StacksFrontier.Homology.DerivedCategory.InverseSystem.PerfectTower.PadicTrace
import all StacksFrontier.Homology.DerivedCategory.InverseSystem.PerfectTower.Finiteness

/-!
# The alternating trace formula for a perfect tower

The alternating sum of the traces of `πⁱ_∞` on `Hⁱ_∞ ⊗_{ℤ_[ℓ]} ℚ_[ℓ]` is `t_∞`
(Stacks 03V4, part (3)), and the whole lemma, parts (1), (2) and (3) together.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Stacks.Trace
open scoped BigOperators TensorProduct

universe u w v

namespace Stacks.InverseSystem

open CategoryTheory.FilteredDerived (finite_nonzero_degrees)

attribute [local instance] HasDerivedCategory.standard

/-! ### Part (3): the alternating trace formula -/

private lemma epi_productDifference_of_finite {R : Type u} [Ring R]
    (X : ℕ → ModuleCat.{v} R) (t : ∀ n, X (n + 1) ⟶ X n)
    [∀ n, Finite (X n)] :
    Epi (Pi.lift (fun n => Pi.π X n - Pi.π X (n + 1) ≫ t n)) := by
  apply (ModuleCat.epi_iff_surjective _).mpr
  intro y
  let F : ℕᵒᵖ ⥤ Type v := Functor.ofOpSequence (X := fun n => (X n : Type v))
    (fun n => ↾fun x => (t n).hom x + (Pi.π X n).hom y)
  have (n : ℕᵒᵖ) : Finite (F.obj n) := inferInstanceAs (Finite (X n.unop))
  have (n : ℕᵒᵖ) : Nonempty (F.obj n) := inferInstanceAs (Nonempty (X n.unop))
  obtain ⟨s, hs⟩ := nonempty_sections_of_finite_inverse_system F
  -- Named at the type `piIsoPi` expects: `s ⟨n⟩` is literally of type `F.obj ⟨n⟩`, which is
  -- `X n` only after `Functor.ofOpSequence` is unfolded.
  let σ : ∀ n : ℕ, (X n : Type v) := fun n => s ⟨n⟩
  let x := (ModuleCat.piIsoPi X).inv.hom σ
  refine ⟨x, ?_⟩
  apply (ModuleCat.piIsoPi X).toLinearEquiv.injective
  funext n
  show (ModuleCat.piIsoPi X).hom.hom _ n = (ModuleCat.piIsoPi X).hom.hom y n
  rw [ModuleCat.piIsoPi_hom_ker_subtype_apply,
    ModuleCat.piIsoPi_hom_ker_subtype_apply]
  -- Stated at the goal's shape: `congrArg` alone phrases the left side through the composite
  -- `Pi.lift _ ≫ Pi.π X n`, which `rw` cannot see past.
  have hd : (Pi.π X n).hom ((Pi.lift (fun n => Pi.π X n - Pi.π X (n + 1) ≫ t n)).hom x) =
      (Pi.π X n - Pi.π X (n + 1) ≫ t n).hom x :=
    congrArg (fun f => f.hom x) (Pi.lift_comp_π (fun n => Pi.π X n - Pi.π X (n + 1) ≫ t n) n)
  rw [hd]
  show (Pi.π X n).hom x - (t n).hom ((Pi.π X (n + 1)).hom x) = _
  dsimp only [x]
  rw [ModuleCat.piIsoPi_inv_kernel_ι_apply, ModuleCat.piIsoPi_inv_kernel_ι_apply]
  dsimp only [σ]
  have hn := hs (homOfLE (Nat.le_succ n)).op
  change F.map (homOfLE (Nat.le_succ n)).op (s ⟨n + 1⟩) = s ⟨n⟩ at hn
  simp only [F, Functor.ofOpSequence_map_homOfLE_succ] at hn
  change (t n).hom (s ⟨n + 1⟩) + (Pi.π X n).hom y = s ⟨n⟩ at hn
  rw [← hn]
  abel

private lemma finite_restrictedHomology {ℓ : ℕ} [Fact ℓ.Prime]
    (T : PerfectTower.{v} ℓ) (i : ℤ) (n : ℕ) :
    Finite ((DerivedCategory.homologyFunctor (ModuleCat.{v} ℤ_[ℓ]) i).obj
      (restrictedTowerObj T n)) := by
  have : NeZero (ℓ ^ (n + 1)) := ⟨pow_ne_zero _ (Fact.out : ℓ.Prime).ne_zero⟩
  have := finite_homology_of_perfect (T.obj n) (T.isPerfect n) i
  have : Finite (levelCohomology T i n) := Module.finite_of_finite (ZMod (ℓ ^ (n + 1)))
  let e :=
    ((restrictHomologyIsoOfHom.{v} (PadicInt.toZModPow (n + 1)) i).app (T.obj n)).toLinearEquiv
  have : Finite ((ModuleCat.restrictScalars.{v} (PadicInt.toZModPow (n + 1))).obj
      (levelCohomology T i n)) := ‹Finite (levelCohomology T i n)›
  exact Finite.of_injective (β := levelCohomology T i n) e e.injective

private def restrictedTowerEndo {ℓ : ℕ} [Fact ℓ.Prime] (T : PerfectTower.{v} ℓ) :
    restrictedTower T ⟶ restrictedTower T :=
  NatTrans.ofOpSequence (fun n => (padicRestriction.{v} (ℓ := ℓ) n).map (T.endo n)) (by
    intro n
    simp only [restrictedTower, Functor.ofOpSequence_map_homOfLE_succ]
    -- As in `cohomologyDiagramIso`: name the objects the transition sits between.
    change restrictedTowerTransition T n ≫ (padicRestriction.{v} (ℓ := ℓ) n).map (T.endo n) =
      (padicRestriction.{v} (ℓ := ℓ) (n + 1)).map (T.endo (n + 1)) ≫
        restrictedTowerTransition T n
    dsimp only [restrictedTowerTransition]
    rw [Category.assoc, ← NatTrans.naturality, Functor.comp_map, ← Category.assoc,
      ← Functor.map_comp, ← T.endo_compatible, Functor.map_comp, Category.assoc])

private lemma productDifference_comm {C : Type*} [Category C] [Preadditive C]
    (F : ℕᵒᵖ ⥤ C) [HasProduct (fun n : ℕ => F.obj ⟨n⟩)] (η : F ⟶ F) :
    let X := fun n : ℕ => F.obj ⟨n⟩
    let d := Pi.lift (fun n => Pi.π X n - Pi.π X (n + 1) ≫
      F.map (homOfLE (Nat.le_succ n)).op)
    d ≫ Limits.Pi.map (f := X) (g := X) (fun n => η.app ⟨n⟩) =
      Limits.Pi.map (f := X) (g := X) (fun n => η.app ⟨n⟩) ≫ d := by
  dsimp only
  apply Pi.hom_ext
  intro n
  simp only [Category.assoc, Pi.map_π, Pi.lift_comp_π, Preadditive.comp_sub]
  rw [← Category.assoc, Pi.lift_comp_π, Preadditive.sub_comp,
    Category.assoc, η.naturality, Pi.map_π_assoc]


private lemma exists_perfect_limit_with_homology {ℓ : ℕ} [Fact ℓ.Prime]
    (T : PerfectTower.{v} ℓ) [HasProduct (restrictedTowerObj T)] :
    ∃ (K : DerivedCategory (ModuleCat.{v} ℤ_[ℓ]))
      (p : K ⟶ ∏ᶜ (restrictedTowerObj T)) (κ : K ⟶ K),
      StacksDraft.Perfect.IsPerfect K ∧
      (∀ n, IsIso (StacksDraft.DerivedInverseLimit.derivedBaseChangeComparison
        (PadicInt.toZModPow (n + 1)) (p ≫ Pi.π (restrictedTowerObj T) n))) ∧
      (∀ n, κ ≫ p ≫ Pi.π (restrictedTowerObj T) n =
        p ≫ Pi.π (restrictedTowerObj T) n ≫
          (padicRestriction.{v} (ℓ := ℓ) n).map (T.endo n)) ∧
      ∀ i, ∃ e : (DerivedCategory.homologyFunctor (ModuleCat.{v} ℤ_[ℓ]) i).obj K ≅
          ModuleCat.of ℤ_[ℓ] (limitCohomology T i),
        ∀ n, e.hom ≫ ModuleCat.ofHom (limitCohomologyProjection T i n) =
          (DerivedCategory.homologyFunctor (ModuleCat.{v} ℤ_[ℓ]) i).map
            (p ≫ Pi.π (restrictedTowerObj T) n) ≫
          (restrictedHomologyIso T i n).hom := by
  let : HasExactLimitsOfShape (Discrete ℕ) (ModuleCat.{v} ℤ_[ℓ]) :=
    moduleCat_hasExactLimitsOfShape_discrete ℤ_[ℓ] ℕ
  obtain ⟨K, hperf, hK⟩ := exists_perfect_derivedLimit T
  obtain ⟨p, δ, htri, hH⟩ :=
    DerivedCategory.isDerivedLimit_homology_shortExact (restrictedTower T) K hK
  -- `p` is born with its codomain spelled `∏ᶜ fun n => (restrictedTower T).obj ⟨n⟩`; every
  -- composite below is written against `∏ᶜ restrictedTowerObj T`, so name it that way once.
  change K ⟶ ∏ᶜ (restrictedTowerObj T) at p
  let d := Pi.lift (fun n => Pi.π (restrictedTowerObj T) n -
    Pi.π (restrictedTowerObj T) (n + 1) ≫ restrictedTowerTransition T n)
  have htri' : Pretriangulated.Triangle.mk p d δ ∈ distTriang _ := by
    simp only [restrictedTower, Functor.ofOpSequence_map_homOfLE_succ] at htri
    exact htri
  let u := Limits.Pi.map (f := restrictedTowerObj T) (g := restrictedTowerObj T)
    (fun n => (padicRestriction.{v} (ℓ := ℓ) n).map (T.endo n))
  have hu : d ≫ u = u ≫ d := by
    have h := productDifference_comm (restrictedTower T) (restrictedTowerEndo T)
    simp only [restrictedTower, Functor.ofOpSequence_map_homOfLE_succ] at h
    exact h
  obtain ⟨κ, hκ₀, -⟩ := Pretriangulated.complete_distinguished_triangle_morphism₁
    (Pretriangulated.Triangle.mk p d δ) (Pretriangulated.Triangle.mk p d δ) htri' htri' u u hu
  -- Restated off the triangle's projections: `Triangle.mk p d δ |>.mor₁` is `p` only after
  -- the structure is unfolded, which is what the rewrites below need to see.
  have hκ : p ≫ u = κ ≫ p := hκ₀
  refine ⟨K, p, κ, hperf, (isPerfect_and_baseChange_isIso T K p δ htri').2, ?_, ?_⟩
  · intro n
    have h := congrArg (fun a => a ≫ Pi.π (restrictedTowerObj T) n) hκ
    simpa [u, Category.assoc] using h.symm
  · intro i
    obtain ⟨e₀, j, q, w, he₀, hj, hq, hs⟩ := hH i
    have hfin (n : ℕ) := finite_restrictedHomology T (i - 1) n
    let := hfin
    have hepi := epi_productDifference_of_finite
      (fun n => (DerivedCategory.homologyFunctor (ModuleCat.{v} ℤ_[ℓ]) (i - 1)).obj
        (restrictedTowerObj T n))
      (fun n => (DerivedCategory.homologyFunctor (ModuleCat.{v} ℤ_[ℓ]) (i - 1)).map
        (restrictedTowerTransition T n))
    have : IsIso q := hs.isIso_g_iff.mpr (by
      simp only [Functor.comp_map, restrictedTower, Functor.ofOpSequence_map_homOfLE_succ]
      have hz {X Y : ModuleCat.{v} ℤ_[ℓ]} (f : X ⟶ Y) (hf : Epi f) :
          IsZero (cokernel f) := isZero_cokernel_of_epi f
      exact hz _ hepi)
    let e := asIso q ≪≫ HasLimit.isoOfNatIso (cohomologyDiagramIso T i) ≪≫
      (limit.isLimit (cohomologyDiagram T i)).conePointUniqueUpToIso
        (limitCohomologyConeIsLimit T i)
    -- Restated with `p` composed inside a single `Functor.map`: `p` is born with its codomain
    -- spelled `∏ᶜ fun n => (restrictedTower T).obj ⟨n⟩`, so a `rw [Functor.map_comp]` on the
    -- goal's `∏ᶜ restrictedTowerObj T` spelling has nothing to match.
    have hq' (m : ℕ) : q ≫ limit.π (restrictedTower T ⋙
          DerivedCategory.homologyFunctor (ModuleCat.{v} ℤ_[ℓ]) i) ⟨m⟩ =
        (DerivedCategory.homologyFunctor (ModuleCat.{v} ℤ_[ℓ]) i).map
          (p ≫ Pi.π (restrictedTowerObj T) m) := by
      rw [Functor.map_comp]
      exact hq m
    refine ⟨e, fun n => ?_⟩
    show e.hom ≫ (limitCohomologyCone T i).π.app ⟨n⟩ = _
    dsimp only [e, Iso.trans_hom, asIso_hom]
    rw [Category.assoc, Category.assoc, IsLimit.conePointUniqueUpToIso_hom_comp]
    show q ≫ (HasLimit.isoOfNatIso (cohomologyDiagramIso T i)).hom ≫
      limit.π (cohomologyDiagram T i) ⟨n⟩ = _
    rw [HasLimit.isoOfNatIso_hom_π, ← Category.assoc, hq' n]
    rfl

private lemma trace_eq_of_intertwining {R : Type u} [CommRing R]
    {X Y : ModuleCat.{v} R} (e : X ≅ Y) (f : X ⟶ X) (g : Y ⟶ Y)
    (h : f ≫ e.hom = e.hom ≫ g) :
    LinearMap.trace R X f.hom = LinearMap.trace R Y g.hom := by
  have hg : e.inv ≫ f ≫ e.hom = g := by rw [h, e.inv_hom_id_assoc]
  rw [← LinearMap.trace_conj' f.hom e.toLinearEquiv]
  show LinearMap.trace R Y (e.inv ≫ f ≫ e.hom).hom = _
  rw [hg]

/-- `Hⁱ` of an endomorphism of a derived object intertwines with the homology of a lift. -/
private lemma homologyMap_comp_homologyFactors_trans {C : Type u} [Category.{v} C] [Abelian C]
    [HasDerivedCategory.{w} C] {P : CochainComplex C ℤ} {K : DerivedCategory C}
    (e : DerivedCategory.Q.obj P ≅ K) (g : P ⟶ P) (f : K ⟶ K)
    (hg : DerivedCategory.Q.map g = e.hom ≫ f ≫ e.inv) (i : ℤ) :
    HomologicalComplex.homologyMap g i ≫
        (homologyFactors P i ≪≫ (DerivedCategory.homologyFunctor C i).mapIso e).hom =
      (homologyFactors P i ≪≫ (DerivedCategory.homologyFunctor C i).mapIso e).hom ≫
        (DerivedCategory.homologyFunctor C i).map f := by
  dsimp only [Iso.trans_hom, Functor.mapIso_hom]
  rw [← Category.assoc, homologyMap_comp_homologyFactors g i, Category.assoc, hg,
    Functor.map_comp, Functor.map_comp]
  simp

private lemma exists_zero_differential_perfect_model {k : Type} [Field k]
    (K : FilteredDerived.PerfectDerivedCategory.{0, v} k) :
    ∃ (E : CochainComplex (ModuleCat.{v} k) ℤ)
      (_hE : FilteredDerived.finiteProjectiveComplex k E),
      (∀ i j, E.d i j = 0) ∧ Nonempty (DerivedCategory.Q.obj E ≅ K.obj) := by
  obtain ⟨P, hP, ⟨eP⟩⟩ := (FilteredDerived.isPerfect_iff _ _).mp K.property
  have hfin (i : ℤ) : Module.Finite k (P.homology i) := by
    have : Module.Finite k (P.X i) := (hP.2 i).2
    have : Module.Finite k (P.cycles i) := Module.Finite.of_injective (P.iCycles i).hom
      ((ModuleCat.mono_iff_injective _).mp inferInstance)
    exact Module.Finite.of_surjective (P.homologyπ i).hom
      ((ModuleCat.epi_iff_surjective _).mp inferInstance)
  have (i : ℤ) : Projective (P.homology i) :=
    ModuleCat.projective_of_free (Module.Free.chooseBasis k _)
  obtain ⟨E, j, hz, hi, hj⟩ := StacksDraft.Perfect.exists_zero_differential_representative P
  let := hj
  refine ⟨E, ?_, hz, ⟨asIso (DerivedCategory.Q.map j) ≪≫ eP⟩⟩
  refine ⟨?_, fun i => ⟨inferInstance, Module.Finite.equiv (hi i).some.symm.toLinearEquiv⟩⟩
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := hP.1
  have := ha
  have := hb
  constructor
  · refine ⟨a, (CochainComplex.isStrictlyGE_iff E a).mpr fun i hia => ?_⟩
    exact (P.isZero_of_isGE a i hia).of_iso (hi i).some
  · refine ⟨b, (CochainComplex.isStrictlyLE_iff E b).mpr fun i hib => ?_⟩
    exact (P.isZero_of_isLE b i hib).of_iso (hi i).some

lemma alternatingTrace_eval_eq_sum_trace {R : Type} [CommRing R]
    (P : CochainComplex (ModuleCat.{v} R) ℤ)
    (hP : FilteredDerived.finiteProjectiveComplex R P) [∀ i, Module.Free R (P.X i)] (g : P ⟶ P) :
    commutativeAdditiveCommutatorQuotientEval R (FilteredDerived.alternatingTrace R P hP g) =
      ∑ᶠ i : ℤ, (if Even i then (1 : R) else -1) * LinearMap.trace R (P.X i) (g.f i).hom := by
  classical
  let t : ℤ → FilteredDerived.AdditiveCommutatorQuotient R := fun i => by
    let : Module.Projective R (P.X i) := (hP.2 i).1
    let : Module.Finite R (P.X i) := (hP.2 i).2
    exact if Even i then projectiveModuleTrace R (P.X i) (g.f i).hom
      else -projectiveModuleTrace R (P.X i) (g.f i).hom
  have ht : Function.HasFiniteSupport t := by
    apply (finite_nonzero_degrees _ P hP).subset
    intro i hi
    change t i ≠ 0 at hi
    by_contra hz
    have hzero : IsZero (P.X i) := not_not.mp hz
    let : Module.Projective R (P.X i) := (hP.2 i).1
    let : Module.Finite R (P.X i) := (hP.2 i).2
    have : Subsingleton (P.X i) := ModuleCat.subsingleton_of_isZero hzero
    have hzero' := projectiveTrace_zero_of_subsingleton (P.X i) (g.f i).hom
    simp [t, hzero'] at hi
  show commutativeAdditiveCommutatorQuotientEval R (∑ᶠ i, t i) = _
  rw [AddMonoidHom.map_finsum _ ht]
  apply finsum_congr
  intro i
  have : Module.Finite R (P.X i) := (hP.2 i).2
  have : Module.Projective R (P.X i) := (hP.2 i).1
  have he := projectiveTrace_eval_eq_trace_of_split (R := R) (P.X i) (g.f i).hom
    (P.X i) LinearMap.id LinearMap.id (by simp)
  simp only [LinearMap.comp_id, LinearMap.id_comp] at he
  by_cases hi : Even i <;> simp [t, hi, he]

private lemma perfectTrace_eq_sum_homology {k : Type} [Field k]
    (K : FilteredDerived.PerfectDerivedCategory.{0, v} k) (f : K.obj ⟶ K.obj) :
    commutativeAdditiveCommutatorQuotientEval k (FilteredDerived.perfectDerivedTrace k K f) =
      ∑ᶠ i : ℤ, (if Even i then (1 : k) else -1) *
        LinearMap.trace k ((DerivedCategory.homologyFunctor (ModuleCat.{v} k) i).obj K.obj)
          ((DerivedCategory.homologyFunctor (ModuleCat.{v} k) i).map f).hom := by
  obtain ⟨E, hE, hz, ⟨e⟩⟩ := exists_zero_differential_perfect_model K
  obtain ⟨g, hg⟩ := exists_cochainEndo E hE K.obj e f
  rw [FilteredDerived.perfectDerivedTrace_eq_alternatingTrace k K f E hE e g hg,
    alternatingTrace_eval_eq_sum_trace]
  apply finsum_congr
  intro i
  congr 1
  have : IsIso (E.iCycles i) := E.isIso_iCycles _ _ rfl (hz _ _)
  have : IsIso (E.homologyπ i) := E.isIso_homologyπ _ _ rfl (hz _ _)
  let s : E.X i ≅ E.homology i := (asIso (E.iCycles i)).symm ≪≫ asIso (E.homologyπ i)
  have ht : LinearMap.trace k (E.X i) (g.f i).hom =
      LinearMap.trace k (E.homology i) (HomologicalComplex.homologyMap g i).hom := by
    apply trace_eq_of_intertwining s
    rw [← cancel_epi (E.iCycles i)]
    dsimp only [s, Iso.trans_hom, Iso.symm_hom, asIso_hom]
    rw [← Category.assoc, ← HomologicalComplex.cyclesMap_i, Category.assoc]
    simp [HomologicalComplex.homologyπ_naturality]
  rw [ht]
  exact trace_eq_of_intertwining _ _ _ (homologyMap_comp_homologyFactors_trans e g f hg i)

private lemma adjointTranspose_endo_compatible {C D : Type*} [Category C] [Category D]
    {F : C ⥤ D} {G : D ⥤ C} (a : F ⊣ G) {X : C} {Y : D}
    (f : X ⟶ X) (g : Y ⟶ Y) (p : X ⟶ G.obj Y)
    (h : f ≫ p = p ≫ G.map g) :
    F.map f ≫ (a.homEquiv X Y).symm p = (a.homEquiv X Y).symm p ≫ g := by
  apply (a.homEquiv X Y).injective
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right,
    Equiv.apply_symm_apply]
  exact h

private lemma limitCohomology_iso_endo {ℓ : ℕ} [Fact ℓ.Prime] (T : PerfectTower.{v} ℓ)
    [HasProduct (restrictedTowerObj T)] (K : DerivedCategory (ModuleCat.{v} ℤ_[ℓ]))
    (p : K ⟶ ∏ᶜ (restrictedTowerObj T)) (κ : K ⟶ K)
    (hκ : ∀ n, κ ≫ p ≫ Pi.π (restrictedTowerObj T) n =
      p ≫ Pi.π (restrictedTowerObj T) n ≫
        (padicRestriction.{v} (ℓ := ℓ) n).map (T.endo n))
    (i : ℤ) (e : (DerivedCategory.homologyFunctor (ModuleCat.{v} ℤ_[ℓ]) i).obj K ≅
      ModuleCat.of ℤ_[ℓ] (limitCohomology T i))
    (he : ∀ n, e.hom ≫ ModuleCat.ofHom (limitCohomologyProjection T i n) =
      (DerivedCategory.homologyFunctor (ModuleCat.{v} ℤ_[ℓ]) i).map
        (p ≫ Pi.π (restrictedTowerObj T) n) ≫ (restrictedHomologyIso T i n).hom) :
    (DerivedCategory.homologyFunctor (ModuleCat.{v} ℤ_[ℓ]) i).map κ ≫ e.hom =
      e.hom ≫ ModuleCat.ofHom (limitCohomologyEndo T i) := by
  let H := DerivedCategory.homologyFunctor (ModuleCat.{v} ℤ_[ℓ]) i
  apply (limitCohomologyConeIsLimit T i).hom_ext
  rintro ⟨n⟩
  show (H.map κ ≫ e.hom) ≫ ModuleCat.ofHom (limitCohomologyProjection T i n) =
    (e.hom ≫ ModuleCat.ofHom (limitCohomologyEndo T i)) ≫
      ModuleCat.ofHom (limitCohomologyProjection T i n)
  have hproj : ModuleCat.ofHom (limitCohomologyEndo T i) ≫
      ModuleCat.ofHom (limitCohomologyProjection T i n) =
    ModuleCat.ofHom (limitCohomologyProjection T i n) ≫
      ModuleCat.ofHom (levelCohomologyEndoₗ T i n) := by ext x; rfl
  rw [Category.assoc, Category.assoc, hproj, he n, ← Category.assoc e.hom,
    he n, Category.assoc, ← H.map_comp_assoc, hκ n, H.map_comp, Category.assoc]
  simp only [H.map_comp, Category.assoc]
  have hn := (restrictHomologyIsoOfHom.{v} (PadicInt.toZModPow (n + 1)) i).hom.naturality (T.endo n)
  dsimp only [Functor.comp_map] at hn
  have ht := congrArg (fun f ↦ H.map (p ≫ Pi.π (restrictedTowerObj T) n) ≫ f) hn
  simp only [H, Functor.map_comp, Category.assoc] at ht ⊢
  exact ht

private lemma perfect_limit_trace {ℓ : ℕ} [Fact ℓ.Prime] (T : PerfectTower.{v} ℓ)
    [HasProduct (restrictedTowerObj T)] (K : FilteredDerived.PerfectDerivedCategory.{0, v} ℤ_[ℓ])
    (p : K.obj ⟶ ∏ᶜ (restrictedTowerObj T)) (κ : K.obj ⟶ K.obj)
    (hb : ∀ n, IsIso (StacksDraft.DerivedInverseLimit.derivedBaseChangeComparison
      (PadicInt.toZModPow (n + 1)) (p ≫ Pi.π (restrictedTowerObj T) n)))
    (hκ : ∀ n, κ ≫ p ≫ Pi.π (restrictedTowerObj T) n =
      p ≫ Pi.π (restrictedTowerObj T) n ≫
        (padicRestriction.{v} (ℓ := ℓ) n).map (T.endo n)) :
    commutativeAdditiveCommutatorQuotientEval ℤ_[ℓ]
      (FilteredDerived.perfectDerivedTrace ℤ_[ℓ] K κ) = padicTrace T := by
  apply (exists_unique_padicTrace T).choose_spec.2
  intro n
  let φ := PadicInt.toZModPow (p := ℓ) (n + 1)
  let D := CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{0, 0, v} φ
  let a := @CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsAdjunction.{0, 0, v}
    _ _ _ _ φ _ _ D.functor D.comparison D.isLeftDerived
  let β := (a.homEquiv K.obj (T.obj n)).symm (p ≫ Pi.π (restrictedTowerObj T) n)
  have : IsIso β := hb n
  exact perfectTrace_baseChange φ K (T.perfectObj n) κ (T.endo n) β
    (adjointTranspose_endo_compatible a κ (T.endo n) _ (by simpa only [Category.assoc] using hκ n))

/-- **Stacks 03V4, part (3).** The alternating sum of the traces of `πⁱ_∞` on
`Hⁱ_∞ ⊗_{ℤ_[ℓ]} ℚ_[ℓ]` is the ℓ-adic trace `t_∞` of the tower. -/
public theorem alternating_trace_eq_padicTrace {ℓ : ℕ} [Fact ℓ.Prime]
    (T : PerfectTower.{v} ℓ) :
    ∑ᶠ i : ℤ, (if Even i then (1 : ℚ_[ℓ]) else -1) *
        LinearMap.trace ℚ_[ℓ] (ℚ_[ℓ] ⊗[ℤ_[ℓ]] limitCohomology T i)
          (LinearMap.baseChange ℚ_[ℓ] (limitCohomologyEndo T i)) =
      (padicTrace T : ℚ_[ℓ]) := by
  classical
  let : HasExactLimitsOfShape (Discrete ℕ) (ModuleCat.{v} ℤ_[ℓ]) :=
    moduleCat_hasExactLimitsOfShape_discrete ℤ_[ℓ] ℕ
  let : HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{v} ℤ_[ℓ])) :=
    Stacks.DerivedProducts.hasProductsOfShape_derivedCategory
  obtain ⟨K, p, κ, hK, hb, hκ, hH⟩ := exists_perfect_limit_with_homology T
  let MK : FilteredDerived.PerfectDerivedCategory.{0, v} ℤ_[ℓ] := ⟨K, hK⟩
  have htrace := perfect_limit_trace T MK p κ hb hκ
  obtain ⟨P, hP, ⟨eP⟩⟩ := (FilteredDerived.isPerfect_iff _ _).mp hK
  obtain ⟨g, hg⟩ := exists_cochainEndo P hP K eP κ
  let φ := algebraMap ℤ_[ℓ] ℚ_[ℓ]
  let F := ModuleCat.extendScalars.{0, 0, v} φ
  have hflat : φ.Flat := RingHom.flat_algebraMap_iff.mpr inferInstance
  have : F.PreservesHomology := extendScalars_preservesHomology_of_flat φ hflat
  let Pq := (F.mapHomologicalComplex (.up ℤ)).obj P
  let gq : Pq ⟶ Pq := (F.mapHomologicalComplex (.up ℤ)).map g
  let hPq := finiteProjectiveComplex_extendScalars φ P hP
  let L : FilteredDerived.PerfectDerivedCategory.{0, v} ℚ_[ℓ] :=
    ⟨DerivedCategory.Q.obj Pq, (FilteredDerived.isPerfect_iff _ _).mpr ⟨Pq, hPq, ⟨Iso.refl _⟩⟩⟩
  have hsum : (∑ᶠ i : ℤ, (if Even i then (1 : ℚ_[ℓ]) else -1) *
      LinearMap.trace ℚ_[ℓ] (ℚ_[ℓ] ⊗[ℤ_[ℓ]] limitCohomology T i)
        (LinearMap.baseChange ℚ_[ℓ] (limitCohomologyEndo T i))) =
    ∑ᶠ i : ℤ, (if Even i then (1 : ℚ_[ℓ]) else -1) *
      LinearMap.trace ℚ_[ℓ]
        ((DerivedCategory.homologyFunctor (ModuleCat.{v} ℚ_[ℓ]) i).obj L.obj)
        ((DerivedCategory.homologyFunctor (ModuleCat.{v} ℚ_[ℓ]) i).map
          (DerivedCategory.Q.map gq)).hom := by
    apply finsum_congr
    intro i
    congr 1
    obtain ⟨e, he⟩ := hH i
    have heκ := limitCohomology_iso_endo T K p κ hκ i e he
    let H := DerivedCategory.homologyFunctor (ModuleCat.{v} ℤ_[ℓ]) i
    let a : P.homology i ≅ ModuleCat.of ℤ_[ℓ] (limitCohomology T i) :=
      (homologyFactors P i ≪≫ H.mapIso eP) ≪≫ e
    have ha : HomologicalComplex.homologyMap g i ≫ a.hom =
        a.hom ≫ ModuleCat.ofHom (limitCohomologyEndo T i) := by
      dsimp only [a]
      rw [Iso.trans_hom, ← Category.assoc, homologyMap_comp_homologyFactors_trans eP g κ hg i,
        Category.assoc, heκ, Category.assoc]
    let b : (DerivedCategory.homologyFunctor (ModuleCat.{v} ℚ_[ℓ]) i).obj
          (DerivedCategory.Q.obj Pq) ≅ F.obj (ModuleCat.of ℤ_[ℓ] (limitCohomology T i)) :=
      (homologyFactors Pq i).symm ≪≫ mapHomologyFactors F P i ≪≫ F.mapIso a
    have hb' : (DerivedCategory.homologyFunctor (ModuleCat.{v} ℚ_[ℓ]) i).map
        (DerivedCategory.Q.map gq) ≫ b.hom =
      b.hom ≫ F.map (ModuleCat.ofHom (limitCohomologyEndo T i)) := by
      have hn : (DerivedCategory.homologyFunctor (ModuleCat.{v} ℚ_[ℓ]) i).map
            (DerivedCategory.Q.map gq) ≫ (homologyFactors Pq i).inv =
          (homologyFactors Pq i).inv ≫ HomologicalComplex.homologyMap gq i :=
        DerivedCategory.homologyFunctorFactors_hom_naturality gq i
      have hm : HomologicalComplex.homologyMap gq i ≫ (mapHomologyFactors F P i).hom =
          (mapHomologyFactors F P i).hom ≫ F.map (HomologicalComplex.homologyMap g i) :=
        ShortComplex.mapHomologyIso_hom_naturality
          ((HomologicalComplex.shortComplexFunctor (ModuleCat.{v} ℤ_[ℓ]) (.up ℤ) i).map g) F
      dsimp only [b, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom]
      rw [← Category.assoc, hn, Category.assoc,
        ← Category.assoc (HomologicalComplex.homologyMap gq i), hm,
        Category.assoc, ← F.map_comp, ha, F.map_comp]
      simp only [Category.assoc]
    have ht := trace_eq_of_intertwining b
      ((DerivedCategory.homologyFunctor (ModuleCat.{v} ℚ_[ℓ]) i).map (DerivedCategory.Q.map gq))
      (F.map (ModuleCat.ofHom (limitCohomologyEndo T i))) hb'
    convert ht.symm using 1
    rfl
  rw [hsum, ← perfectTrace_eq_sum_homology L (DerivedCategory.Q.map gq)]
  rw [FilteredDerived.perfectDerivedTrace_eq_alternatingTrace ℚ_[ℓ] L
    (DerivedCategory.Q.map gq) Pq hPq (Iso.refl _) gq (by exact (Category.comp_id _).symm)]
  rw [alternatingTrace_eval_baseChange φ P hP g]
  have htraceP := FilteredDerived.perfectDerivedTrace_eq_alternatingTrace ℤ_[ℓ] MK κ P hP eP g hg
  rw [← htraceP, htrace]
  rfl

/-! ### The lemma -/

/-- An element of `Hⁱ_∞` is determined by its projections to the level cohomologies. -/
private theorem limitCohomology_ext {ℓ : ℕ} [Fact ℓ.Prime] (T : PerfectTower.{v} ℓ) (i : ℤ)
    {x y : limitCohomology T i}
    (h : ∀ n : ℕ, limitCohomologyProjection T i n x = limitCohomologyProjection T i n y) :
    x = y :=
  Subtype.ext (funext fun n => h n)

/-- The only endomorphism of `Hⁱ_∞` induced by the family `Hⁱ(πₙ)` is `πⁱ_∞`. -/
private theorem eq_limitCohomologyEndo {ℓ : ℕ} [Fact ℓ.Prime] (T : PerfectTower.{v} ℓ)
    (π : ∀ i : ℤ, limitCohomology T i →ₗ[ℤ_[ℓ]] limitCohomology T i)
    (hπ : ∀ (i : ℤ) (n : ℕ) (a : limitCohomology T i),
      limitCohomologyProjection T i n (π i a) =
        levelCohomologyEndoₗ T i n (limitCohomologyProjection T i n a)) :
    π = fun i => limitCohomologyEndo T i := by
  funext i
  refine LinearMap.ext fun a => limitCohomology_ext T i fun n => ?_
  rw [hπ i n a, limitCohomologyProjection_limitCohomologyEndo]

/-- **Stacks 03V4.** Let `ℓ` be a prime.  Suppose we have `Kₙ ∈ D_perf(ℤ/ℓⁿ⁺¹ℤ)`,
`πₙ : Kₙ → Kₙ` and isomorphisms `φₙ : Kₙ₊₁ ⊗ᴸ_{ℤ/ℓⁿ⁺²ℤ} ℤ/ℓⁿ⁺¹ℤ → Kₙ` compatible with `πₙ₊₁`
and `πₙ` — that is, a `PerfectTower ℓ`.  Then

1. the elements `tₙ = Tr(πₙ | Kₙ) ∈ ℤ/ℓⁿ⁺¹ℤ` form an element `t_∞ = {tₙ}` of `ℤ_[ℓ]`, namely
   there is exactly one `t_∞ ∈ ℤ_[ℓ]` reducing to `tₙ` modulo `ℓⁿ⁺¹` for every `n`;
2. the `ℤ_[ℓ]`-module `Hⁱ_∞ = limₙ Hⁱ(Kₙ)` is finite and is nonzero for finitely many `i`
   only; and
3. the operators `Hⁱ(πₙ) : Hⁱ(Kₙ) → Hⁱ(Kₙ)` are compatible with the transitions of the
   inverse system, hence define a unique `πⁱ_∞ : Hⁱ_∞ → Hⁱ_∞` lying over them, and every such
   family satisfies `∑ᵢ (-1)ⁱ Tr(πⁱ_∞ | Hⁱ_∞ ⊗_{ℤ_[ℓ]} ℚ_[ℓ]) = t_∞`.

Levels are indexed so that level `n` carries coefficients in `ℤ/ℓⁿ⁺¹ℤ`, avoiding the zero
ring; `(-1)ⁱ` for `i : ℤ` is written as `if Even i then 1 else -1`. -/
@[stacks 03V4 "parts (1), (2) and (3)"]
public theorem perfectTower_padicTrace_eq_alternating_trace_limitCohomology
    {ℓ : ℕ} [Fact ℓ.Prime] (T : PerfectTower.{v} ℓ) :
    -- (1) the traces `tₙ` form an element `t_∞` of `ℤ_[ℓ]`
    (∃! t : ℤ_[ℓ], ∀ n : ℕ, PadicInt.toZModPow (n + 1) t = traceAtLevel T n) ∧
    -- (2) each `Hⁱ_∞` is a finite `ℤ_[ℓ]`-module, and only finitely many are nonzero
    (∀ i : ℤ, Module.Finite ℤ_[ℓ] (limitCohomology T i)) ∧
    {i : ℤ | Nontrivial (limitCohomology T i)}.Finite ∧
    -- (3) the `Hⁱ(πₙ)` are compatible with the transitions of the inverse system
    (∀ (i : ℤ) (n : ℕ), levelCohomologyEndoHom T i (n + 1) ≫ levelCohomologyTransition T i n =
        levelCohomologyTransition T i n ≫
          (ModuleCat.restrictScalars.{v} (levelCast ℓ n)).map (levelCohomologyEndoHom T i n)) ∧
    -- (3) and so define a unique family `πⁱ_∞` of endomorphisms of the `Hⁱ_∞`
    (∃! π : ∀ i : ℤ, limitCohomology T i →ₗ[ℤ_[ℓ]] limitCohomology T i,
        ∀ (i : ℤ) (n : ℕ) (a : limitCohomology T i),
          limitCohomologyProjection T i n (π i a) =
            levelCohomologyEndoₗ T i n (limitCohomologyProjection T i n a)) ∧
    -- (3) which satisfies `∑ᵢ (-1)ⁱ Tr(πⁱ_∞ | Hⁱ_∞ ⊗ ℚ_[ℓ]) = t_∞`
    (∀ t : ℤ_[ℓ], (∀ n : ℕ, PadicInt.toZModPow (n + 1) t = traceAtLevel T n) →
      ∀ π : ∀ i : ℤ, limitCohomology T i →ₗ[ℤ_[ℓ]] limitCohomology T i,
        (∀ (i : ℤ) (n : ℕ) (a : limitCohomology T i),
            limitCohomologyProjection T i n (π i a) =
              levelCohomologyEndoₗ T i n (limitCohomologyProjection T i n a)) →
          ∑ᶠ i : ℤ, (if Even i then (1 : ℚ_[ℓ]) else -1) *
              LinearMap.trace ℚ_[ℓ] (ℚ_[ℓ] ⊗[ℤ_[ℓ]] limitCohomology T i)
                (LinearMap.baseChange ℚ_[ℓ] (π i)) =
            (t : ℚ_[ℓ])) := by
  refine ⟨exists_unique_padicTrace T, finite_limitCohomology T,
    finite_setOf_nontrivial_limitCohomology T, levelCohomologyEndoHom_transition T,
    ⟨fun i => limitCohomologyEndo T i, fun _ _ _ => rfl, eq_limitCohomologyEndo T⟩,
    fun t ht π hπ => ?_⟩
  rw [eq_limitCohomologyEndo T π hπ,
    (exists_unique_padicTrace T).unique ht (toZModPow_padicTrace T)]
  exact alternating_trace_eq_padicTrace T

end Stacks.InverseSystem

end
