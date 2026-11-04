module

public import StacksFrontier.AlgebraicGeometry.DeRham.RelativePoincareDuality.FormsClosedFibreKernel
public import StacksFrontier.AlgebraicGeometry.CohomologyGlobalSectionScalar.Basic
public import StacksFrontier.Algebra.Homology.FlatComplexTopDegreeGenerator

/-!
# A generator of top cohomology of differential forms, detected on closed fibres

Let `f : X ⟶ Spec A` be separated with a finite covering `U` by affine opens. Global functions
coming from the base act on the cohomology groups `H^q(X, ℱ)` through multiplication of `ℱ`, and on
the alternating Čech complex as the scalar action. Multiplication by a base function commutes with
the base change of forms along a cartesian square, so the pullback map of [Stacks, Tag 01F9]
to a base change is semilinear.

The main result says how a generator of the top cohomology `H^{q+1}(X, Ω^p_{X/A})` over a
Noetherian `A` is detected on closed fibres: if for every maximal ideal `𝔪` every class on the
fibre `X_𝔪` is a multiple of the pullback of `ξ`, and `H^{>q+1}` vanishes on the Čech complex,
then every class on `X` is a multiple of `ξ`. This is the claim "`ξ` is a basis element" of the
proof of [Stacks, Tag 0G8J], from top-degree base change and Nakayama's lemma; the input on the
fibres is supplied by [Stacks, Tag 0G8D] and [Stacks, Tag 0G8E].

## Main results

* `Stacks.Cech.alternatingCechModuleComplexMap_globalSmul`: on Čech cochains, multiplication by a
  base function is the scalar action.
* `Stacks.Cech.formsBaseChangeHom_comp_globalSmul`: the base change of forms is linear over the
  base.
* `Stacks.Cech.pullbackHgroup_formsBaseChangeHom_globalSmul`: the pullback map is semilinear.
* `Stacks.Cech.exists_sub_smul_eq_d_of_forall_closedFibre`: the generator criterion.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite AlgebraicGeometry
open RingedSpaceModuleAdjunction Stacks.DeRham.GysinCohomologyBaseChange

universe u

namespace Stacks.Cech

section Scalars

variable {A : Type u} [CommRing A] {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) {I : Type u}
  (U : I → X.Opens)

/-- **On Čech cochains, multiplication of the module by a function from the base is the scalar
action of the base.** -/
theorem alternatingCechModuleComplexMap_globalSmul_apply (F : X.Modules) (a : A) (n : ℕ)
    (s : (alternatingCechModuleComplex f U F).X n) :
    (alternatingCechModuleComplexMap f U (globalSmul ((globalRingHom f).hom a) F)).f n s =
      a • s := by
  refine Subtype.ext (funext fun i => ?_)
  show (globalSmul _ F).app (CechCochains.inter U i) (s.1 i) =
    (baseRingHom f (CechCochains.inter U i)).hom a • s.1 i
  rw [globalSmul_app]
  rfl

/-- A morphism of complexes of modules acting as a scalar in every degree acts as that scalar on
homology. -/
theorem homologyMap_apply_eq_smul_of_f {R : Type u} [CommRing R]
    {K : CochainComplex (ModuleCat.{u} R) ℕ} (Φ : K ⟶ K) (a : R)
    (hΦ : ∀ n (s : K.X n), Φ.f n s = a • s) (n : ℕ) (x : K.homology n) :
    (HomologicalComplex.homologyMap Φ n).hom x = a • x := by
  obtain ⟨z, rfl⟩ := (ModuleCat.epi_iff_surjective (K.homologyπ n)).1 inferInstance x
  rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, HomologicalComplex.homologyπ_naturality,
    ModuleCat.hom_comp, LinearMap.comp_apply, ← map_smul]
  congr 1
  apply (ModuleCat.mono_iff_injective (K.iCycles n)).mp inferInstance
  rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, HomologicalComplex.cyclesMap_i,
    ModuleCat.hom_comp, LinearMap.comp_apply, hΦ, map_smul]

/-- Multiplication by a function from the base acts on the homology of the Čech complex as the
scalar action. -/
theorem homologyMap_alternatingCechModuleComplexMap_globalSmul_apply (F : X.Modules) (a : A)
    (n : ℕ) (x : (alternatingCechModuleComplex f U F).homology n) :
    (HomologicalComplex.homologyMap
      (alternatingCechModuleComplexMap f U (globalSmul ((globalRingHom f).hom a) F)) n).hom x =
      a • x :=
  homologyMap_apply_eq_smul_of_f _ a (alternatingCechModuleComplexMap_globalSmul_apply f U F a) n x

variable [LinearOrder I] (hU : (⊤ : X.Opens) = ⨆ i, U i)
  (haff : ∀ (r : ℕ) (s : Fin (r + 1) → I), IsAffineOpen (⨅ k, U (s k)))

/-- **The identification of `H^q(X, ℱ)` with Čech cohomology carries multiplication by a base
function to the scalar action.** -/
theorem hgroupIsoAlternatingCechModuleHomology_hom_globalSmul (F : X.Modules)
    [F.IsQuasicoherent] (a : A) (q : ℕ) (x : Hgroup X.ringCatSheaf ⊤ q F) :
    (show (alternatingCechModuleComplex f U F).homology q from
        (hgroupIsoAlternatingCechModuleHomology f U hU haff F q).hom
          (((Hfunctor X.ringCatSheaf ⊤ q).map (globalSmul ((globalRingHom f).hom a) F)).hom x)) =
      a • (show (alternatingCechModuleComplex f U F).homology q from
        (hgroupIsoAlternatingCechModuleHomology f U hU haff F q).hom x) := by
  have hn := congrArg (fun k => k.hom x)
    (hgroupIsoAlternatingCechModuleHomology_naturality f U hU haff
      (globalSmul ((globalRingHom f).hom a) F) q)
  exact hn.trans (homologyMap_alternatingCechModuleComplexMap_globalSmul_apply f U F a q _)

/-- The inverse identification carries the scalar action to multiplication by a base function. -/
theorem hgroupIsoAlternatingCechModuleHomology_inv_smul (F : X.Modules) [F.IsQuasicoherent]
    (a : A) (q : ℕ) (x : (alternatingCechModuleComplex f U F).homology q) :
    (hgroupIsoAlternatingCechModuleHomology f U hU haff F q).inv
        (show (forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u}).obj
          ((alternatingCechModuleComplex f U F).homology q) from
          (a • x : (alternatingCechModuleComplex f U F).homology q)) =
      ((Hfunctor X.ringCatSheaf ⊤ q).map (globalSmul ((globalRingHom f).hom a) F)).hom
        ((hgroupIsoAlternatingCechModuleHomology f U hU haff F q).inv x) := by
  apply (ConcreteCategory.bijective_of_isIso
    (hgroupIsoAlternatingCechModuleHomology f U hU haff F q).hom).1
  have h₁ := hgroupIsoAlternatingCechModuleHomology_hom_globalSmul f U hU haff F a q
    ((hgroupIsoAlternatingCechModuleHomology f U hU haff F q).inv x)
  rw [Iso.inv_hom_id_apply] at h₁
  exact (Iso.inv_hom_id_apply _ _).trans h₁.symm

end Scalars

section Semilinear

variable {A A' : Type u} [CommRing A] [CommRing A'] (φ : A →+* A') {X X' : Scheme.{u}}
  (f : X ⟶ Spec (.of A)) (f' : X' ⟶ Spec (.of A')) (g : X' ⟶ X)
  (hsq : IsPullback g f' f (Spec.map (CommRingCat.ofHom φ)))

/-- **The base change of forms is linear over the base**: it carries multiplication by `c ∈ A`
on `Ω^p_{X/A}` to multiplication by `φ c` on `g_*Ω^p_{X'/A'}`. -/
theorem formsBaseChangeHom_comp_globalSmul (p : ℤ) (c : A) :
    Stacks.Gysin.formsBaseChangeHom g f f' (Spec.map (CommRingCat.ofHom φ)) hsq.w p ≫
        (modulePushforward g.toLRSHom.toShHom).map
          (globalSmul ((globalRingHom f').hom (φ c)) (f'.relativeDifferentialForms p)) =
      globalSmul ((globalRingHom f).hom c) (f.relativeDifferentialForms p) ≫
        Stacks.Gysin.formsBaseChangeHom g f f' (Spec.map (CommRingCat.ofHom φ)) hsq.w p := by
  ext V t
  show (globalSmul ((globalRingHom f').hom (φ c)) (f'.relativeDifferentialForms p)).app
      (g ⁻¹ᵁ V)
      ((Stacks.Gysin.formsBaseChangeHom g f f' (Spec.map (CommRingCat.ofHom φ)) hsq.w p).app V t) =
    (Stacks.Gysin.formsBaseChangeHom g f f' (Spec.map (CommRingCat.ofHom φ)) hsq.w p).app V
      ((globalSmul ((globalRingHom f).hom c) (f.relativeDifferentialForms p)).app V t)
  refine (globalSmul_app _ _ _ _).trans ?_
  refine Eq.trans ?_ (congrArg _ (globalSmul_app _ _ _ _)).symm
  refine Eq.trans ?_ (Scheme.Modules.Hom.app_smul
    (N := pushforwardModule g (f'.relativeDifferentialForms p))
    (Stacks.Gysin.formsBaseChangeHom g f f' (Spec.map (CommRingCat.ofHom φ)) hsq.w p) _ _).symm
  have hb : g.app V (restrictTop ((globalRingHom f).hom c) V) =
      restrictTop ((globalRingHom f').hom (φ c)) (g ⁻¹ᵁ V) := by
    have h := congr($(baseRingHom_comp_app φ f f' g hsq V).hom c)
    rw [CommRingCat.hom_comp, CommRingCat.hom_comp] at h
    exact h
  rw [← hb]
  rfl

/-- **The pullback map along a base change of forms is semilinear over the base.** -/
theorem pullbackHgroup_formsBaseChangeHom_globalSmul (p : ℤ) (c : A) (a m : ℤ) (n : ℕ)
    (hn : m - a = n) (x : Hgroup X.ringCatSheaf ⊤ n (f.relativeDifferentialForms p)) :
    (pullbackHgroup (CohomologyPullbackComparison.canonical g.toLRSHom.toShHom) a m n hn
        (Stacks.Gysin.formsBaseChangeHom g f f' (Spec.map (CommRingCat.ofHom φ)) hsq.w p)).hom
        (((Hfunctor X.ringCatSheaf ⊤ n).map
          (globalSmul ((globalRingHom f).hom c) (f.relativeDifferentialForms p))).hom x) =
      ((Hfunctor X'.ringCatSheaf ⊤ n).map
          (globalSmul ((globalRingHom f').hom (φ c)) (f'.relativeDifferentialForms p))).hom
        ((pullbackHgroup (CohomologyPullbackComparison.canonical g.toLRSHom.toShHom) a m n hn
          (Stacks.Gysin.formsBaseChangeHom g f f' (Spec.map (CommRingCat.ofHom φ)) hsq.w p)).hom
          x) :=
  congrArg (fun k => k.hom x) (pullbackHgroup_naturality
    (CohomologyPullbackComparison.canonical g.toLRSHom.toShHom) a m n hn
    (globalSmul ((globalRingHom f).hom c) (f.relativeDifferentialForms p))
    (globalSmul ((globalRingHom f').hom (φ c)) (f'.relativeDifferentialForms p)) _ _
    (formsBaseChangeHom_comp_globalSmul φ f f' g hsq p c))

end Semilinear

section Cocycles

/-- **Top-degree cocycles of the base change of a flat complex come from cocycles.** Let `K` be
a bounded complex of flat `R`-modules with no cohomology above `q + 1`. Every `(q+1)`-cocycle of
`K ⊗ R/𝔪` is `1 ⊗ y` for a `(q+1)`-cocycle `y` of `K`. -/
theorem exists_one_tmul_eq_of_extendScalars_d_eq_zero {R : Type u} [CommRing R]
    {K : CochainComplex (ModuleCat.{u} R) ℕ} (q n : ℕ) [∀ i, Module.Flat R (K.X i)]
    (hKn : ∀ i, n ≤ i → Subsingleton (K.X i))
    (hK : ∀ i, q + 1 < i → IsZero (K.homology i)) (m : Ideal R)
    (w : (ModuleCat.extendScalars (Ideal.Quotient.mk m)).obj (K.X (q + 1)))
    (hw : (ModuleCat.extendScalars (Ideal.Quotient.mk m)).map (K.d (q + 1) (q + 1 + 1)) w = 0) :
    ∃ y : K.X (q + 1), K.d (q + 1) (q + 1 + 1) y = 0 ∧
      Stacks.FlatComplexTopDegree.toRingModule (Ideal.Quotient.mk m) 1 ⊗ₜ[R] y = w := by
  have hexK : ∀ i, q + 1 ≤ i →
      Function.Exact (K.d i (i + 1)).hom (K.d (i + 1) (i + 1 + 1)).hom :=
    fun i hi => Stacks.FlatComplexTopDegree.exact_of_isZero_homology K i (hK (i + 1) (by omega))
  have hr := Stacks.FlatComplexTopDegree.range_lTensor_ker_subtype (C := fun i => K.X i)
    (fun i => (K.d i (i + 1)).hom) (q + 1) n hKn hexK
    (Stacks.FlatComplexTopDegree.ringModule (Ideal.Quotient.mk m))
  let w' : TensorProduct R (Stacks.FlatComplexTopDegree.ringModule (Ideal.Quotient.mk m))
    (K.X (q + 1)) := w
  have hw' : w' ∈ LinearMap.ker ((K.d (q + 1) (q + 1 + 1)).hom.lTensor
      (Stacks.FlatComplexTopDegree.ringModule (Ideal.Quotient.mk m))) :=
    LinearMap.mem_ker.mpr
      ((Stacks.FlatComplexTopDegree.extendScalars_map_apply _ _ w).symm.trans hw)
  rw [← hr] at hw'
  obtain ⟨t, ht⟩ := hw'
  obtain ⟨y', hy'⟩ := Stacks.FlatComplexTopDegree.exists_one_tmul_eq (Ideal.Quotient.mk m)
    Ideal.Quotient.mk_surjective
    (M := ModuleCat.of R (LinearMap.ker (K.d (q + 1) (q + 1 + 1)).hom)) t
  refine ⟨y'.1, y'.2, ?_⟩
  show _ = w'
  rw [← ht, ← hy']
  rfl

end Cocycles

section Generator

variable {A : Type u} [CommRing A] [IsNoetherianRing A] {X : Scheme.{u}} (f : X ⟶ Spec (.of A))
  [IsProper f] {I : Type u} [Fintype I] [LinearOrder I] (U : I → X.Opens)
  (hU : (⊤ : X.Opens) = ⨆ i, U i) (hUaff : ∀ i, IsAffineOpen (U i))

attribute [local instance] Scheme.Hom.isQuasicoherent_relativeDifferentialForms

include hU hUaff in
/-- **A generator of the top cohomology of differential forms is detected on the closed fibres.**
Let `A` be Noetherian, `f : X ⟶ Spec A` proper with fibres of dimension `≤ q + 1`, `Ω^p_{X/A}`
coherent and flat over `A`, and `U` a finite affine covering. Let `z` be a `(q+1)`-cocycle of the
alternating Čech complex of `Ω^p_{X/A}`, with class `ξ ∈ H^{q+1}(X, Ω^p_{X/A})`. Suppose that for
every maximal ideal `𝔪` and every cartesian square `X' = X ×_{Spec A} Spec A/𝔪`, every class of
`H^{q+1}(X', Ω^p_{X'/(A/𝔪)})` is a multiple, by a function from the base, of the pullback of `ξ`.
Then every `(q+1)`-cocycle is, up to a coboundary, a multiple of `z`. -/
theorem exists_sub_smul_eq_d_of_forall_closedFibre (p q : ℕ)
    (hflat : IsFlatOver f.toLRSHom.toShHom (f.relativeDifferentialForms (p : ℤ)))
    [(f.relativeDifferentialForms (p : ℤ)).IsCoherent]
    (hfib : ∀ t : Spec (.of A), topologicalKrullDim (f.fiber t) ≤ ((q + 1 : ℕ) : WithBot ℕ∞))
    (z : (alternatingCechModuleComplex f U (f.relativeDifferentialForms (p : ℤ))).X (q + 1))
    (hz : (alternatingCechModuleComplex f U (f.relativeDifferentialForms (p : ℤ))).d (q + 1)
      (q + 1 + 1) z = 0)
    (hgen : ∀ (m : Ideal A), m.IsMaximal → ∀ (X' : Scheme.{u}) (f' : X' ⟶ Spec (.of (A ⧸ m)))
      (g : X' ⟶ X) (hsq : IsPullback g f' f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk m))))
      (y' : Hgroup X'.ringCatSheaf ⊤ (q + 1) (f'.relativeDifferentialForms (p : ℤ))),
      ∃ c : A, y' = ((Hfunctor X'.ringCatSheaf ⊤ (q + 1)).map
        (globalSmul ((globalRingHom f').hom (Ideal.Quotient.mk m c))
          (f'.relativeDifferentialForms (p : ℤ)))).hom
        ((pullbackHgroup (CohomologyPullbackComparison.canonical g.toLRSHom.toShHom) 0
          ((q + 1 : ℕ) : ℤ) (q + 1) (by simp)
          (Stacks.Gysin.formsBaseChangeHom g f f'
            (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk m))) hsq.w (p : ℤ))).hom
          ((hgroupIsoAlternatingCechModuleHomology f U hU
            (fun _ s => inter_isAffineOpen f U hUaff s) (f.relativeDifferentialForms (p : ℤ))
            (q + 1)).inv (homologyClassOf _ q z hz))))
    (y : (alternatingCechModuleComplex f U (f.relativeDifferentialForms (p : ℤ))).X (q + 1))
    (hy : (alternatingCechModuleComplex f U (f.relativeDifferentialForms (p : ℤ))).d (q + 1)
      (q + 1 + 1) y = 0) :
    ∃ (a : A) (v : (alternatingCechModuleComplex f U (f.relativeDifferentialForms (p : ℤ))).X q),
      (alternatingCechModuleComplex f U (f.relativeDifferentialForms (p : ℤ))).d q (q + 1) v =
        y - a • z := by
  classical
  let K := alternatingCechModuleComplex f U (f.relativeDifferentialForms (p : ℤ))
  set haff : ∀ (r : ℕ) (s : Fin (r + 1) → I), IsAffineOpen (⨅ k, U (s k)) :=
    fun _ s => inter_isAffineOpen f U hUaff s
  have : ∀ i, Module.Flat A
      (K.X i) :=
    alternatingCechModuleComplex_flat f U _ hUaff hflat
  have hKn : ∀ i, Fintype.card I ≤ i → Subsingleton (K.X i) :=
    fun i hi => subsingleton_alternatingSubmodule f U _ hi
  have hK : ∀ i, q + 1 < i → IsZero (K.homology i) :=
    fun i hi => isZero_homology_alternatingCechModuleComplex f U hU _ hUaff hfib hi
  have : Module.Finite A (K.homology (q + 1)) :=
    moduleFinite_homology_alternatingCechModuleComplex f U hU _ hUaff (q + 1)
  refine Stacks.FlatComplexTopDegree.exists_sub_smul_eq_d_of_forall_isMaximal q (Fintype.card I)
    hKn hK z hz ?_ y hy
  intro m hm w hw
  obtain ⟨y₀, hy₀, rfl⟩ := exists_one_tmul_eq_of_extendScalars_d_eq_zero q (Fintype.card I) hKn hK
    m w hw
  -- the closed fibre
  let φm : A →+* A ⧸ m := Ideal.Quotient.mk m
  let g := pullback.fst f (Spec.map (CommRingCat.ofHom φm))
  let f' := pullback.snd f (Spec.map (CommRingCat.ofHom φm))
  have hsq : IsPullback g f' f (Spec.map (CommRingCat.ofHom φm)) := IsPullback.of_hasPullback _ _
  have hspec : IsClosedImmersion (Spec.map (CommRingCat.ofHom φm)) :=
    IsClosedImmersion.spec_of_surjective (CommRingCat.ofHom φm) Ideal.Quotient.mk_surjective
  have : IsClosedImmersion g :=
    MorphismProperty.of_isPullback (P := @IsClosedImmersion) hsq.flip hspec
  have : Fact (Topology.IsClosedEmbedding g.toLRSHom.toShHom.hom.base) :=
    ⟨g.isClosedEmbedding⟩
  have : (pushforwardModule g (f'.relativeDifferentialForms (p : ℤ))).IsQuasicoherent :=
    inferInstanceAs ((Scheme.Modules.pushforward g).obj
      (f'.relativeDifferentialForms (p : ℤ))).IsQuasicoherent
  set e := hgroupIsoAlternatingCechModuleHomology f U hU haff (f.relativeDifferentialForms (p : ℤ))
    (q + 1)
  set φF := Stacks.Gysin.formsBaseChangeHom g f f' (Spec.map (CommRingCat.ofHom φm)) hsq.w (p : ℤ)
  set P := pullbackHgroup (CohomologyPullbackComparison.canonical g.toLRSHom.toShHom) 0
    ((q + 1 : ℕ) : ℤ) (q + 1) (by simp) φF
  obtain ⟨c, hc⟩ := hgen m hm _ f' g hsq (P.hom (e.inv (homologyClassOf K q y₀ hy₀)))
  -- the class of `y₀ - c z` dies on the fibre
  have hyz : K.d (q + 1) (q + 1 + 1) (y₀ - c • z) = 0 := by
    rw [map_sub, map_smul, hy₀, hz, smul_zero, sub_zero]
  have hcyc : cycleOf K q (y₀ - c • z) hyz = cycleOf K q y₀ hy₀ - c • cycleOf K q z hz := by
    apply (ModuleCat.mono_iff_injective (K.iCycles (q + 1))).mp inferInstance
    rw [map_sub, map_smul, iCycles_cycleOf, iCycles_cycleOf, iCycles_cycleOf]
  have hcz : homologyClassOf K q (y₀ - c • z) hyz =
      homologyClassOf K q y₀ hy₀ - c • homologyClassOf K q z hz := by
    unfold homologyClassOf
    rw [hcyc, map_sub, map_smul]
  have hinv : e.inv (homologyClassOf K q (y₀ - c • z) hyz) =
      e.inv (homologyClassOf K q y₀ hy₀) -
        ((Hfunctor X.ringCatSheaf ⊤ (q + 1)).map
          (globalSmul ((globalRingHom f).hom c) (f.relativeDifferentialForms (p : ℤ)))).hom
          (e.inv (homologyClassOf K q z hz)) := by
    rw [hcz, map_sub]
    congr 1
    exact hgroupIsoAlternatingCechModuleHomology_inv_smul f U hU haff _ c (q + 1) _
  have hzero : P.hom (e.inv (homologyClassOf K q (y₀ - c • z) hyz)) = 0 := by
    rw [hinv]
    refine (AddMonoidHom.map_sub P.hom _ _).trans ?_
    rw [pullbackHgroup_formsBaseChangeHom_globalSmul φm f f' g hsq (p : ℤ) c, ← hc, sub_self]
  obtain ⟨v, hv⟩ := exists_extendScalars_d_eq_one_tmul_of_pullbackHgroup_eq_zero φm f f' g hsq U
    hU hUaff p q (y₀ - c • z) hyz hzero
  refine ⟨Ideal.Quotient.mk m c, v, ?_⟩
  rw [hv, TensorProduct.tmul_sub, TensorProduct.tmul_smul]
  congr 1

end Generator

end Stacks.Cech

end
