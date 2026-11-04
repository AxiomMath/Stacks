module

public import StacksFrontier.AlgebraicGeometry.Cohomology.Cech.HgroupAlternatingCech
public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.PullbackHgroupNaturality
public import StacksFrontier.AlgebraicGeometry.DeRham.PoincareDuality.TopDifferentialCechBaseChange
public import StacksFrontier.AlgebraicGeometry.Modules.AlternatingCechModulePushforward
public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.TransverseBaseChangeArrow
public import StacksFrontier.Algebra.Homology.FlatComplexTopDegreeFibres

/-!
# Classes of differential forms killed by the pullback to a closed base change

Let `f : X ⟶ Spec A` be separated with a finite covering `U` by affine opens, let `A ⟶ A'` be a
ring map such that the base change `g : X' = X ×_{Spec A} Spec A' ⟶ X` is a homeomorphism onto a
closed subset (for instance a quotient map `A ⟶ A/𝔪`), and let `y` be an alternating Čech
cocycle of `Ω^p_{X/A}` for `U`, with class `[y] ∈ H^{q+1}(X, Ω^p_{X/A})`. If the pullback map
of [Stacks, Tag 01F9]

`H^{q+1}(X, Ω^p_{X/A}) ⟶ H^{q+1}(X', Ω^p_{X'/A'})`

along the base change of forms (the vertical arrow of [Stacks, Tag 0G8D]) kills `[y]`, then
`1 ⊗ y` is a coboundary of the base change `Č(U, Ω^p_{X/A}) ⊗_A A'` of the Čech complex.

The pullback map is `H^{q+1}(X, -)` of `Ω^p_{X/A} ⟶ g_*Ω^p_{X'/A'}` followed by the
identification `H^{q+1}(X, g_*Ω^p_{X'/A'}) ≅ H^{q+1}(X', Ω^p_{X'/A'})`, an isomorphism because
`g` is a closed embedding; on the Čech side `H^{q+1}(X, -)` of a morphism of quasi-coherent modules
is computed on `U`, the Čech complex of `g_*Ω^p_{X'/A'}` for `U` is that of `Ω^p_{X'/A'}` for
`g⁻¹U`, and the latter is the base change of `Č(U, Ω^p_{X/A})` ([Stacks, Tag 0FL5]).

## Main results

* `Stacks.Cech.exists_extendScalars_d_eq_one_tmul_of_pullbackHgroup_eq_zero`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite AlgebraicGeometry
open RingedSpaceModuleAdjunction Stacks.DeRham.GysinCohomologyBaseChange

universe u

namespace Stacks.Cech

section Classes

variable {R : Type u} [Ring R]

/-- The inclusion of cycles into a complex of modules is injective. -/
private theorem iCycles_hom_injective (K : CochainComplex (ModuleCat.{u} R) ℕ) (n : ℕ) :
    Function.Injective (K.iCycles n).hom :=
  (ModuleCat.mono_iff_injective (K.iCycles n)).mp inferInstance

/-- A morphism of complexes of modules commutes with the differentials elementwise. -/
private theorem d_f_apply {K L : CochainComplex (ModuleCat.{u} R) ℕ} (φ : K ⟶ L) (q : ℕ)
    (v : K.X q) : L.d q (q + 1) (φ.f q v) = φ.f (q + 1) (K.d q (q + 1) v) := by
  have h := congrArg (fun k => k.hom v) (φ.comm q (q + 1))
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using h

/-- A homology class of a complex of modules indexed by `ℕ` vanishes in a positive degree exactly
when the cocycle representing it is a coboundary. -/
theorem homologyπ_succ_eq_zero_iff (K : CochainComplex (ModuleCat.{u} R) ℕ) (q : ℕ)
    (z : K.cycles (q + 1)) :
    (K.homologyπ (q + 1)).hom z = 0 ↔ ∃ v : K.X q, K.d q (q + 1) v = (K.iCycles (q + 1)).hom z := by
  let S := ShortComplex.mk (K.toCycles q (q + 1)) (K.homologyπ (q + 1))
    (K.toCycles_comp_homologyπ q (q + 1))
  have hS : S.Exact := ShortComplex.exact_of_g_is_cokernel S
    (K.homologyIsCokernel q (q + 1) (CochainComplex.prev_nat_succ q))
  constructor
  · intro hz
    obtain ⟨v, hv⟩ := (ShortComplex.moduleCat_exact_iff S).mp hS z hz
    exact ⟨v, (congrArg (fun k : K.X q ⟶ K.X (q + 1) => k.hom v)
      (K.toCycles_i q (q + 1))).symm.trans (congrArg (K.iCycles (q + 1)).hom hv)⟩
  · rintro ⟨v, hv⟩
    have hz : (K.toCycles q (q + 1)).hom v = z :=
      iCycles_hom_injective K (q + 1)
        ((congrArg (fun k : K.X q ⟶ K.X (q + 1) => k.hom v) (K.toCycles_i q (q + 1))).trans hv)
    rw [← hz]
    exact congrArg (fun k => k.hom v) (K.toCycles_comp_homologyπ q (q + 1))

/-- The cycle of a complex of modules given by an element killed by the differential. -/
def cycleOf (K : CochainComplex (ModuleCat.{u} R) ℕ) (q : ℕ) (y : K.X (q + 1))
    (hy : K.d (q + 1) (q + 1 + 1) y = 0) : K.cycles (q + 1) :=
  K.cyclesMk (C := ModuleCat.{u} R) y (q + 1 + 1) (CochainComplex.next ℕ (q + 1)) hy

/-- The cycle `cycleOf K q y hy` has underlying element `y`. -/
theorem iCycles_cycleOf (K : CochainComplex (ModuleCat.{u} R) ℕ) (q : ℕ) (y : K.X (q + 1))
    (hy : K.d (q + 1) (q + 1 + 1) y = 0) :
    (K.iCycles (q + 1)).hom (cycleOf K q y hy) = y :=
  K.i_cyclesMk (C := ModuleCat.{u} R) y (q + 1 + 1) (CochainComplex.next ℕ (q + 1)) hy

/-- A morphism of complexes carries an element killed by the differential to one. -/
theorem d_f_apply_eq_zero {K L : CochainComplex (ModuleCat.{u} R) ℕ} (φ : K ⟶ L) (q : ℕ)
    (y : K.X (q + 1)) (hy : K.d (q + 1) (q + 1 + 1) y = 0) :
    L.d (q + 1) (q + 1 + 1) (φ.f (q + 1) y) = 0 := by
  rw [d_f_apply, hy, map_zero]

/-- The map on cycles induced by a morphism of complexes `φ` sends `cycleOf K q y hy` to the
cycle of `φ y`. -/
theorem cyclesMap_cycleOf {K L : CochainComplex (ModuleCat.{u} R) ℕ} (φ : K ⟶ L) (q : ℕ)
    (y : K.X (q + 1)) (hy : K.d (q + 1) (q + 1 + 1) y = 0) :
    (HomologicalComplex.cyclesMap φ (q + 1)).hom (cycleOf K q y hy) =
      cycleOf L q (φ.f (q + 1) y) (d_f_apply_eq_zero φ q y hy) := by
  apply iCycles_hom_injective L (q + 1)
  rw [iCycles_cycleOf, ← LinearMap.comp_apply, ← ModuleCat.hom_comp,
    HomologicalComplex.cyclesMap_i, ModuleCat.hom_comp, LinearMap.comp_apply, iCycles_cycleOf]

/-- The homology class of an element killed by the differential. -/
def homologyClassOf (K : CochainComplex (ModuleCat.{u} R) ℕ) (q : ℕ) (y : K.X (q + 1))
    (hy : K.d (q + 1) (q + 1 + 1) y = 0) : K.homology (q + 1) :=
  (K.homologyπ (q + 1)).hom (cycleOf K q y hy)

/-- The map on homology induced by a morphism of complexes `φ` sends the class of `y` to the
class of `φ y`. -/
theorem homologyMap_homologyClassOf {K L : CochainComplex (ModuleCat.{u} R) ℕ} (φ : K ⟶ L)
    (q : ℕ) (y : K.X (q + 1)) (hy : K.d (q + 1) (q + 1 + 1) y = 0) :
    (HomologicalComplex.homologyMap φ (q + 1)).hom (homologyClassOf K q y hy) =
      homologyClassOf L q (φ.f (q + 1) y) (d_f_apply_eq_zero φ q y hy) := by
  unfold homologyClassOf
  rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, HomologicalComplex.homologyπ_naturality,
    ModuleCat.hom_comp, LinearMap.comp_apply, cyclesMap_cycleOf]

/-- The homology class of an element `y` killed by the differential vanishes exactly when `y` is
a coboundary. -/
theorem homologyClassOf_eq_zero_iff (K : CochainComplex (ModuleCat.{u} R) ℕ) (q : ℕ)
    (y : K.X (q + 1)) (hy : K.d (q + 1) (q + 1 + 1) y = 0) :
    homologyClassOf K q y hy = 0 ↔ ∃ v : K.X q, K.d q (q + 1) v = y := by
  rw [homologyClassOf, homologyπ_succ_eq_zero_iff, iCycles_cycleOf]

/-- If an isomorphism of complexes `e` carries `x` to a coboundary `d v'`, then `x` is the
coboundary of `e⁻¹ v'`. -/
theorem d_inv_f_apply_of_d_eq {K L : CochainComplex (ModuleCat.{u} R) ℕ} (e : K ≅ L) (q : ℕ)
    (x : K.X (q + 1)) (v' : L.X q) (h : L.d q (q + 1) v' = e.hom.f (q + 1) x) :
    K.d q (q + 1) (e.inv.f q v') = x := by
  apply (ConcreteCategory.bijective_of_isIso (e.hom.f (q + 1))).1
  rw [← d_f_apply]
  rwa [show (e.hom.f q) ((e.inv.f q) v') = v' from
    congrArg (fun k => k.hom v') (HomologicalComplex.congr_hom e.inv_hom_id q)]

end Classes

section Kernel

variable {A A' : Type u} [CommRing A] [CommRing A'] (φ : A →+* A') {X X' : Scheme.{u}}
  (f : X ⟶ Spec (.of A)) (f' : X' ⟶ Spec (.of A')) (g : X' ⟶ X)
  (hsq : IsPullback g f' f (Spec.map (CommRingCat.ofHom φ)))
  {I : Type u} [Finite I] [LinearOrder I] [IsSeparated f] (U : I → X.Opens)
  (hU : (⊤ : X.Opens) = ⨆ i, U i) (hUaff : ∀ i, IsAffineOpen (U i))

attribute [local instance] Scheme.Hom.isQuasicoherent_relativeDifferentialForms

omit [Finite I] [LinearOrder I] [IsSeparated f] in
/-- The alternating Čech differential on the underlying cochains. -/
theorem alternatingCechModuleComplex_d_apply_val (F : X.Modules) (n : ℕ)
    (s : (alternatingCechModuleComplex f U F).X n) :
    ((alternatingCechModuleComplex f U F).d n (n + 1) s).1 =
      CechCochains.cechD U F.presheaf n s.1 := by
  rw [alternatingCechModuleComplex_d]
  rfl

omit [LinearOrder I] in
/-- Transporting along `g` the image of a Čech cochain `t` of `Ω^p_{X/A}` under the base change
of forms gives the cochain `1 ⊗ t` under `formsCechBaseChangeIso`. -/
theorem cochainPushforward_formsBaseChangeHom (p n : ℕ)
    (t : alternatingCechModuleObj f U (f.relativeDifferentialForms (p : ℤ)) n) :
    cochainPushforward g U (fun i => g ⁻¹ᵁ U i) (fun _ => rfl)
        (f'.relativeDifferentialForms (p : ℤ)) n
        ((alternatingCechModuleComplexMap f U
          (Stacks.Gysin.formsBaseChangeHom g f f' (Spec.map (CommRingCat.ofHom φ)) hsq.w
            (p : ℤ))).f n t).1 =
      (((formsCechBaseChangeIso φ f f' g hsq U hUaff p).hom.f n) ((1 : A') ⊗ₜ[A] t)).1 := by
  funext i
  rw [formsCechBaseChangeIso_hom_one_tmul]
  exact Stacks.Cohomology.CechOne.restr_app (Scheme.Modules.Hom.mapPresheaf
    (Scheme.Hom.relativeDifferentialFormsMap g f f' (Spec.map (CommRingCat.ofHom φ)) hsq.w
      (p : ℤ))) _ _

include hU hUaff in
/-- **A Čech cocycle of `Ω^p_{X/A}` whose class dies under the pullback map to `X'` becomes a
coboundary after base change to `A'`.** -/
theorem exists_extendScalars_d_eq_one_tmul_of_pullbackHgroup_eq_zero
    [Fact (Topology.IsClosedEmbedding g.toLRSHom.toShHom.hom.base)] (p q : ℕ)
    [(pushforwardModule g (f'.relativeDifferentialForms (p : ℤ))).IsQuasicoherent]
    (y : (alternatingCechModuleComplex f U (f.relativeDifferentialForms (p : ℤ))).X (q + 1))
    (hy : (alternatingCechModuleComplex f U (f.relativeDifferentialForms (p : ℤ))).d (q + 1)
      (q + 1 + 1) y = 0)
    (h : (pullbackHgroup (CohomologyPullbackComparison.canonical g.toLRSHom.toShHom) 0
        ((q + 1 : ℕ) : ℤ) (q + 1) (by simp)
        (Stacks.Gysin.formsBaseChangeHom g f f' (Spec.map (CommRingCat.ofHom φ)) hsq.w
          (p : ℤ))).hom
        ((hgroupIsoAlternatingCechModuleHomology f U hU (fun _ s => inter_isAffineOpen f U hUaff s)
          (f.relativeDifferentialForms (p : ℤ)) (q + 1)).inv
          (homologyClassOf _ q y hy)) = 0) :
    ∃ w : (ModuleCat.extendScalars φ).obj
        ((alternatingCechModuleComplex f U (f.relativeDifferentialForms (p : ℤ))).X q),
      (ModuleCat.extendScalars φ).map
          ((alternatingCechModuleComplex f U (f.relativeDifferentialForms (p : ℤ))).d q (q + 1)) w =
        Stacks.FlatComplexTopDegree.toRingModule φ 1 ⊗ₜ[A] y := by
  classical
  set φF := Stacks.Gysin.formsBaseChangeHom g f f' (Spec.map (CommRingCat.ofHom φ)) hsq.w (p : ℤ)
  set haff : ∀ (r : ℕ) (s : Fin (r + 1) → I), IsAffineOpen (⨅ k, U (s k)) :=
    fun _ s => inter_isAffineOpen f U hUaff s
  set ŷ := (hgroupIsoAlternatingCechModuleHomology f U hU haff
    (f.relativeDifferentialForms (p : ℤ)) (q + 1)).inv (homologyClassOf _ q y hy)
  have h₁ : ((Hfunctor X.ringCatSheaf ⊤ (q + 1)).map φF).hom ŷ = 0 := by
    have hfac := congrArg (fun k => k.hom ŷ) (pullbackHgroup_eq_map_comp
      (CohomologyPullbackComparison.canonical g.toLRSHom.toShHom) 0 ((q + 1 : ℕ) : ℤ) (q + 1)
      (by simp) φF)
    have := isIso_pullbackHgroup_canonical_id g.toLRSHom.toShHom 0 ((q + 1 : ℕ) : ℤ) (q + 1)
      (by simp) (f'.relativeDifferentialForms (p : ℤ))
    have hinj := (ConcreteCategory.bijective_of_isIso
      (pullbackHgroup (CohomologyPullbackComparison.canonical g.toLRSHom.toShHom) 0
        ((q + 1 : ℕ) : ℤ) (q + 1) _
        (𝟙 ((modulePushforward g.toLRSHom.toShHom).obj
          (f'.relativeDifferentialForms (p : ℤ)))))).1
    exact hinj ((hfac.symm.trans h).trans (map_zero _).symm)
  have h₂ : (HomologicalComplex.homologyMap (alternatingCechModuleComplexMap f U φF) (q + 1)).hom
      (homologyClassOf _ q y hy) = 0 := by
    have hn := congrArg (fun k => k.hom ŷ)
      (hgroupIsoAlternatingCechModuleHomology_naturality f U hU haff φF (q + 1))
    change (hgroupIsoAlternatingCechModuleHomology f U hU haff _ (q + 1)).hom
        (((Hfunctor X.ringCatSheaf ⊤ (q + 1)).map φF).hom ŷ) =
      (HomologicalComplex.homologyMap (alternatingCechModuleComplexMap f U φF) (q + 1)).hom
        ((hgroupIsoAlternatingCechModuleHomology f U hU haff _ (q + 1)).hom ŷ) at hn
    rw [h₁, map_zero, Iso.inv_hom_id_apply] at hn
    exact hn.symm
  rw [homologyMap_homologyClassOf, homologyClassOf_eq_zero_iff] at h₂
  obtain ⟨v, hv⟩ := h₂
  set e := formsCechBaseChangeIso φ f f' g hsq U hUaff p
  let v' : (alternatingCechModuleComplex f' (fun i => g ⁻¹ᵁ U i)
      (f'.relativeDifferentialForms (p : ℤ))).X q :=
    ⟨cochainPushforward g U (fun i => g ⁻¹ᵁ U i) (fun _ => rfl)
      (f'.relativeDifferentialForms (p : ℤ)) q v.1,
      cochainPushforward_isAlternating g U _ (fun _ => rfl) _ q v.1 v.2⟩
  have hdv' : (alternatingCechModuleComplex f' (fun i => g ⁻¹ᵁ U i)
      (f'.relativeDifferentialForms (p : ℤ))).d q (q + 1) v' =
        (e.hom.f (q + 1)) ((1 : A') ⊗ₜ[A] y) := by
    refine Subtype.ext ?_
    rw [alternatingCechModuleComplex_d_apply_val]
    refine (cochainPushforward_cechD g U _ (fun _ => rfl) _ q v.1).trans ?_
    refine Eq.trans ?_ (cochainPushforward_formsBaseChangeHom φ f f' g hsq U hUaff p (q + 1) y)
    congr 1
    exact (alternatingCechModuleComplex_d_apply_val f U
      (pushforwardModule g (f'.relativeDifferentialForms (p : ℤ))) q v).symm.trans
      (congrArg Subtype.val hv)
  exact ⟨e.inv.f q v', d_inv_f_apply_of_d_eq e q _ v' hdv'⟩

end Kernel

end Stacks.Cech

end
