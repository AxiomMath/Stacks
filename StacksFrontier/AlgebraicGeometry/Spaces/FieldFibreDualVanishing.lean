module

public import StacksFrontier.AlgebraicGeometry.Quot.NegativeExtLocusFromDual
public import StacksFrontier.AlgebraicGeometry.Spaces.PseudoCoherent.AffineChartModelBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedIsoLocal
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentEtaleChart
public import StacksFrontier.Algebra.Homology.PseudoCoherentNakayamaModels
public import StacksFrontier.Homology.Tor.DerivedTensorTopDegree
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PseudoCoherent.DerivedPullbackCompositionCanonical
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleStalkAsPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedModulePullbackBounded
public import StacksFrontier.Algebra.Homology.DerivedCategory.LeftDerivedOfExactFunctor
public import StacksFrontier.AlgebraicGeometry.Spaces.EtalePermanence

/-!
# The fibre-to-stalk step of Stacks 0DLC on an algebraic space

Let `Y` be an algebraic space over a scheme `S` and `L` a pseudo-coherent object of `D(𝒪_Y)`, on
the small étale site.  If `Ext^i(L_y, 𝒪_y) = Hom(Ly^*L, 𝒪[i]) = 0` for every `i < 0` and every
point `y : Spec(k) ⟶ Y` with values in a field, then `L` has no cohomology in positive degrees.
This is the step of the proof of Stacks 0DLC, part (2), which the source attributes to
Stacks 0BCC ("from fibres to stalks"), and which
`StacksFrontier/AlgebraicGeometry/Quot/NegativeExtLocusFromDual.lean` carries as the hypothesis
`AlgebraicGeometry.Space.FieldFibreDualVanishingIsLE`.  This file proves that hypothesis.

## Main results

* `Space.fieldFibreDualVanishingIsLE`: the proposition `Space.FieldFibreDualVanishingIsLE`,
  exactly as stated there.
* `Space.negativeExtVanishesOfFibres_of_quasiCompact_of_quasiSeparated_of_dualExists`:
  Stacks 0DLC, part (2), in the case `W = Y`, over a quasi-compact and quasi-separated base,
  granted Stacks 0DKY alone.
* `Space.isLE_zero_of_chartModel_of_forall_field`: the step on an affine étale chart,
  where `L` is modelled by a bounded above complex of finite free modules.

## The argument

Amplitude in `D(𝒪_Y)` is étale local
(`AlgebraicGeometry.Space.isLE_of_isLE_smallEtaleDerivedModulePullback_chartToSpace`), so one may
work on an affine étale chart `h_{Spec A} ⟶ Y`, where `L` is `ε^*(P~)` for a bounded above complex
`P` of finite free `A`-modules
(`AlgebraicGeometry.Space.exists_isBoundedAboveFiniteFree_etaleModulePullback_iso`).  If `P` had
cohomology in a positive degree, let `n > 0` be the top one; `P` may be taken to vanish above `n`.
Nakayama's lemma, applied to the cokernel of the last differential, gives a maximal ideal `m`
with `H^n(P ⊗_A k) ≠ 0`, `k = A/m`.  Over the field `k`, the complex `k[-n]` is a retract of
`P ⊗_A k`.  The derived pullback of `L` to the point `Spec k ⟶ Spec A ⟶ Y` is `ε^*((P ⊗_A k)~)`
(`AlgebraicGeometry.Space.nonempty_smallEtaleDerivedModulePullback_chartModel_iso`), and
`ε^*(k~[-n]) = 𝒪[-n]`; so `𝒪[-n]` is a retract of `L_y`, and `Hom(L_y, 𝒪[-n]) = 0` forces
`𝒪 = 0` on the spectrum of a field, which is absurd.

Nothing is registered: 0DLC itself is not complete (Stacks 0DKY is pending), and 0BCC is
registered at the generality of local rings
(`StacksDraft.Perfect.exists_unique_boundedAbove_free_complex_representing`); what is used here is
its Nakayama core at the top degree.

## Implementation notes

The chart model, the derived pullback of algebraic spaces and the functor `ε^*` are all built at
the standard model of the derived categories involved, so that model is pinned (at the priority
the files of the chart model use; at the default priority the global model of `SheafOfModules`
wins and the chart model's statements no longer elaborate).

## References

* [Stacks Project, Tag 0DLC](https://stacks.math.columbia.edu/tag/0DLC)
* [Stacks Project, Tag 0BCC](https://stacks.math.columbia.edu/tag/0BCC)
* [Stacks Project, Tag 064T](https://stacks.math.columbia.edu/tag/064T)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

universe u

namespace AlgebraicGeometry.Space

/-! ### Two facts of linear algebra -/

section Algebra

variable {A : Type u} [CommRing A]

/-- **Nakayama's lemma at every maximal ideal, for a map onto a finite module.**  A map `g` onto
a finite `A`-module which becomes surjective after extension of scalars to `A ⧸ m` for every
maximal ideal `m` is surjective. -/
theorem epi_of_forall_epi_extendScalars_quotient {N M : ModuleCat.{u} A} [Module.Finite A M]
    (g : N ⟶ M)
    (hg : ∀ m : Ideal A, m.IsMaximal →
      Epi ((ModuleCat.extendScalars.{u, u, u} (algebraMap A (A ⧸ m))).map g)) :
    Epi g := by
  let Q : ModuleCat.{u} A := ModuleCat.of A (M ⧸ LinearMap.range g.hom)
  let π : M ⟶ Q := ModuleCat.ofHom (LinearMap.range g.hom).mkQ
  have hgπ : g ≫ π = 0 := by
    ext x
    exact (Submodule.Quotient.mk_eq_zero _).2 ⟨x, rfl⟩
  have hQ : Subsingleton (M ⧸ LinearMap.range g.hom) := by
    refine StacksDraft.Nakayama.subsingleton_of_forall_subsingleton_tensor_quotient (A := A) _
      fun m hm => ?_
    let φ : A →+* A ⧸ m := algebraMap A (A ⧸ m)
    have hφ : Function.Surjective φ := Ideal.Quotient.mk_surjective
    let : (ModuleCat.extendScalars.{u, u, u} φ).IsLeftAdjoint :=
      (ModuleCat.extendRestrictScalarsAdj.{u, u, u} φ).isLeftAdjoint
    let F := ModuleCat.extendScalars.{u, u, u} φ
    have := hg m hm
    have hFπ : F.map π = 0 := by
      rw [← cancel_epi (F.map g), ← F.map_comp, hgπ, F.map_zero, comp_zero]
    have hπepi : Epi π :=
      (ModuleCat.epi_iff_surjective π).2 (Submodule.mkQ_surjective _)
    have hFπepi : Epi (F.map π) := inferInstance
    rw [hFπ] at hFπepi
    have hFQ : IsZero (F.obj Q) := IsZero.of_epi_zero (F.obj M) (F.obj Q)
    let Bφ := (ModuleCat.restrictScalars.{u} φ).obj (ModuleCat.of (A ⧸ m) (A ⧸ m))
    have hsub : Subsingleton (TensorProduct A Bφ Q) := ModuleCat.subsingleton_of_isZero hFQ
    let ℓ₀ : A →ₗ[A] Bφ := LinearMap.toSpanSingleton A Bφ (1 : A ⧸ m)
    have hℓ₀ : ∀ x : A, ℓ₀ x = φ x := fun x => mul_one (φ x)
    have hker : RingHom.ker φ ≤ LinearMap.ker ℓ₀ := fun x hx => by
      rwa [LinearMap.mem_ker, hℓ₀]
    let ℓ : (A ⧸ RingHom.ker φ) →ₗ[A] Bφ := (RingHom.ker φ).liftQ ℓ₀ hker
    have hℓ : Function.Bijective ℓ := by
      constructor
      · rw [← LinearMap.ker_eq_bot, Submodule.ker_liftQ, eq_bot_iff]
        intro y hy
        obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.1 hy
        rw [Submodule.mem_bot, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
        rwa [LinearMap.mem_ker, hℓ₀] at hx
      · intro b
        obtain ⟨x, rfl⟩ := hφ b
        exact ⟨Submodule.Quotient.mk x, hℓ₀ x⟩
    let eℓ := LinearEquiv.ofBijective ℓ hℓ
    have hsub' : Subsingleton ((A ⧸ RingHom.ker φ) ⊗[A] Q) :=
      (LinearEquiv.rTensor Q eℓ).toEquiv.injective.subsingleton
    have hquot : Subsingleton (Q ⧸ RingHom.ker φ • (⊤ : Submodule A Q)) :=
      (TensorProduct.quotTensorEquivQuotSMul Q (RingHom.ker φ)).toEquiv.surjective.subsingleton
    have hkerφ : RingHom.ker φ = m := Ideal.mk_ker
    rw [hkerφ] at hquot
    have h₂ : Subsingleton ((A ⧸ m) ⊗[A] Q) :=
      (TensorProduct.quotTensorEquivQuotSMul Q m).toEquiv.injective.subsingleton
    exact (TensorProduct.comm A Q (A ⧸ m)).toEquiv.injective.subsingleton
  have hrange : LinearMap.range g.hom = ⊤ := by
    rw [eq_top_iff]
    intro x _
    exact (Submodule.Quotient.mk_eq_zero _).1 (Subsingleton.elim _ _)
  exact (ModuleCat.epi_iff_surjective g).2 (LinearMap.range_eq_top.1 hrange)

/-- **The field in degree `n` is a retract of a complex of vector spaces with nonzero top
cohomology.**  If `K` is a complex of vector spaces over a field `k` with `K^{n+1} = 0` and
`H^n(K) ≠ 0`, then `k[-n]` (the field placed in degree `n`) is a retract of `K` as a complex:
a vector `v ∈ K^n` outside the image of the differential spans a copy of `k` in `K^n`, made of
cycles since `K^{n+1} = 0`, and a linear form killing the image of the differential with value
`1` at `v` splits it. -/
theorem exists_single_retract_of_not_isZero_homology {k : Type u} [Field k]
    (K : CochainComplex (ModuleCat.{u} k) ℤ) (n : ℤ) (hK : IsZero (K.X (n + 1)))
    (hH : ¬ IsZero (K.homology n)) :
    ∃ (s : (HomologicalComplex.single (ModuleCat.{u} k) (ComplexShape.up ℤ) n).obj
        (ModuleCat.of k k) ⟶ K)
      (r : K ⟶ (HomologicalComplex.single (ModuleCat.{u} k) (ComplexShape.up ℤ) n).obj
        (ModuleCat.of k k)), s ≫ r = 𝟙 _ := by
  classical
  have hne : ¬ Epi (K.d (n - 1) n) := fun h =>
    hH ((StacksDraft.PseudoCoherence.isZero_homology_iff_epi_d_of_isZero K n hK).2 h)
  rw [ModuleCat.epi_iff_surjective] at hne
  let W := LinearMap.range (K.d (n - 1) n).hom
  obtain ⟨v, hv⟩ : ∃ v, v ∉ W := by
    by_contra! h
    exact hne h
  have hv' : (Submodule.Quotient.mk v : K.X n ⧸ W) ≠ 0 := by
    rwa [Ne, Submodule.Quotient.mk_eq_zero]
  obtain ⟨f, hf⟩ : ∃ f : Module.Dual k (K.X n ⧸ W), f (Submodule.Quotient.mk v) ≠ 0 := by
    by_contra! h
    exact hv' ((Module.forall_dual_apply_eq_zero_iff k _).mp h)
  let ψ : K.X n →ₗ[k] k := (f (Submodule.Quotient.mk v))⁻¹ • (f.comp W.mkQ)
  have hψv : ψ v = 1 := by
    simp [ψ, inv_mul_cancel₀ hf]
  have hψW : ∀ w ∈ W, ψ w = 0 := fun w hw => by
    simp [ψ, (Submodule.Quotient.mk_eq_zero W).2 hw]
  refine ⟨HomologicalComplex.mkHomFromSingle
      (ModuleCat.ofHom (LinearMap.toSpanSingleton k (K.X n) v)) (fun j hj => ?_),
    HomologicalComplex.mkHomToSingle (ModuleCat.ofHom ψ) (fun i hi => ?_), ?_⟩
  · obtain rfl : j = n + 1 := by simpa using hj.symm
    exact hK.eq_of_tgt _ _
  · obtain rfl : i = n - 1 := by simp at hi; omega
    ext a
    exact hψW _ ⟨a, rfl⟩
  · refine HomologicalComplex.from_single_hom_ext ?_
    rw [HomologicalComplex.comp_f, HomologicalComplex.mkHomFromSingle_f,
      HomologicalComplex.mkHomToSingle_f, HomologicalComplex.id_f]
    have h1 : ModuleCat.ofHom (LinearMap.toSpanSingleton k (K.X n) v) ≫ ModuleCat.ofHom ψ =
        𝟙 (ModuleCat.of k k) := by
      ext
      simp [hψv]
    simp only [Category.assoc]
    rw [reassoc_of% h1]
    simp

/-- **Nakayama's lemma for the top cohomology of a complex of finite modules.**  If `P` is a
complex of finite `A`-modules with `P^{n+1} = 0` and `H^n(P) ≠ 0`, then `H^n(P ⊗_A A/m) ≠ 0` for
some maximal ideal `m`: otherwise the last differential would become surjective modulo every
maximal ideal, hence be surjective. -/
theorem exists_isMaximal_not_isZero_homology_extendScalars
    (P : CochainComplex (ModuleCat.{u} A) ℤ) (n : ℤ) (hfin : Module.Finite A (P.X n))
    (hP : IsZero (P.X (n + 1))) (hH : ¬ IsZero (P.homology n)) :
    ∃ m : Ideal A, m.IsMaximal ∧
      ¬ IsZero (((CochainComplex.extendScalars (algebraMap A (A ⧸ m))).obj P).homology n) := by
  by_contra! h
  refine hH ((StacksDraft.PseudoCoherence.isZero_homology_iff_epi_d_of_isZero P n hP).2 ?_)
  refine epi_of_forall_epi_extendScalars_quotient _ fun m hm => ?_
  exact (StacksDraft.PseudoCoherence.isZero_homology_iff_epi_d_of_isZero
    ((CochainComplex.extendScalars (algebraMap A (A ⧸ m))).obj P) n
    ((ModuleCat.extendScalars (algebraMap A (A ⧸ m))).map_isZero hP)).1 (h m hm)

end Algebra

/-! ### The chart model of a derived category of modules -/

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

attribute [local instance 10000] HasDerivedCategory.standard

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The functor `ε^* ∘ (-)~ : D(A) ⥤ D(𝒪_{h_{Spec A}})` through which
`AlgebraicGeometry.Space.exists_isBoundedAboveFiniteFree_etaleModulePullback_iso` models a
pseudo-coherent object on an affine étale chart `h_{Spec A}`. -/
abbrev chartModelFunctor {A : Type u} [CommRing A] (hA : B.Contains (Spec (CommRingCat.of A)))
    (g : B.obj hA ⟶ B.obj hS) :
    DerivedCategory (ModuleCat.{u} A) ⥤
      DerivedCategory (Modules.{u, u} B S hS (yoneda.obj (specFppfOver B S hS hA g))
        (isAlgebraicSpace_yoneda B S hS _)) :=
  (tilde.functor (CommRingCat.of A) ⋙ Scheme.Modules.restrictFunctor
      (Iso.refl ((BigFppfOver.toScheme B S hS).obj (specFppfOver B S hS hA g))).hom
      ).mapDerivedCategory ⋙
    representedDerivedAssociatedModule B S hS (specFppfOver B S hS hA g)

/-- **The chart model of the structure sheaf.**  The chart model of `A` placed in degree `n` is
the structure sheaf of `h_{Spec A}` placed in degree `n`: `Ã = 𝒪_{Spec A}` and `ε^*𝒪 = 𝒪`. -/
def chartModelFunctorSingleIso {A : Type u} [CommRing A]
    (hA : B.Contains (Spec (CommRingCat.of A))) (g : B.obj hA ⟶ B.obj hS) (n : ℤ) :
    (chartModelFunctor B S hS hA g).obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) n).obj (ModuleCat.of A A)) ≅
      (structureObject B S hS (schemeSpace (specFppfOver B S hS hA g)))⟦-n⟧ :=
  let T := specFppfOver B S hS hA g
  let G₁ := tilde.functor (CommRingCat.of A) ⋙ Scheme.Modules.restrictFunctor
      (Iso.refl ((BigFppfOver.toScheme B S hS).obj T)).hom
  let eA : G₁.obj (ModuleCat.of A A) ≅
      SheafOfModules.unit ((BigFppfOver.toScheme B S hS).obj T).ringCatSheaf :=
    (Scheme.Modules.restrictFunctor
      (Iso.refl ((BigFppfOver.toScheme B S hS).obj T)).hom).mapIso tildeSelf ≪≫
      Scheme.Modules.restrictUnitIso _
  (representedDerivedAssociatedModule B S hS T).mapIso
      ((Functor.mapDerivedCategorySingleFunctor G₁ n).app (ModuleCat.of A A)) ≪≫
    (Functor.mapDerivedCategorySingleFunctor
      (representedAssociatedModule B S hS T (isAlgebraicSpace_yoneda B S hS T)) n).app
      (G₁.obj (ModuleCat.of A A)) ≪≫
    (DerivedCategory.singleFunctor _ n).mapIso
      ((representedAssociatedModule B S hS T (isAlgebraicSpace_yoneda B S hS T)).mapIso eA ≪≫
        representedAssociatedModuleObjUnitIso B S hS T (isAlgebraicSpace_yoneda B S hS T)) ≪≫
    (((DerivedCategory.singleFunctors _).shiftIso (-n) n 0 (by omega)).app _).symm

/-- **The structure sheaf of the spectrum of a field is not zero**, as an object of the derived
category of its small étale site: its sections over the spectrum itself are the field. -/
theorem not_isZero_structureObject_specFppfOver {k : Type u} [Field k]
    (hk : B.Contains (Spec (CommRingCat.of k))) (g : B.obj hk ⟶ B.obj hS) :
    ¬ IsZero (structureObject B S hS (schemeSpace (specFppfOver B S hS hk g))) := by
  intro h
  let T := specFppfOver B S hS hk g
  let R := ringedToposStructureRingSheaf B S hS (schemeSpace T)
  have h₀ : IsZero (SheafOfModules.unit R) :=
    ((DerivedCategory.homologyFunctor _ 0).map_isZero h).of_iso
      ((DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).app _).symm
  have hsub : Subsingleton (R.obj.obj (Opposite.op (idChart B S hS T))) :=
    ModuleCat.subsingleton_of_isZero
      ((SheafOfModules.evaluation R (Opposite.op (idChart B S hS T))).map_isZero h₀)
  let ψ : RingCat.of k ⟶ R.obj.obj (Opposite.op (idChart B S hS T)) :=
    (forget₂ CommRingCat RingCat).map (Scheme.ΓSpecIso (.of k)).inv
  let χ : R.obj.obj (Opposite.op (idChart B S hS T)) ⟶ RingCat.of k :=
    (forget₂ CommRingCat RingCat).map (Scheme.ΓSpecIso (.of k)).hom
  have hψχ : ∀ x : k, χ (ψ x) = x := fun x => by
    show (Scheme.ΓSpecIso (.of k)).hom ((Scheme.ΓSpecIso (.of k)).inv x) = x
    simp
  exact zero_ne_one (α := k) ((hψχ 0).symm.trans
    ((congrArg χ (Subsingleton.elim (ψ 0) (ψ 1))).trans (hψχ 1)))

/-! ### The fibre-to-stalk step on an affine chart -/

/-- Conjugating a retraction by two isomorphisms gives a retraction. -/
theorem comp_retract_eq_id {C : Type*} [Category C] {X Y Z W : C} (u : W ≅ Z) (e : X ≅ Y)
    (s : Z ⟶ Y) (r : Y ⟶ Z) (h : s ≫ r = 𝟙 Z) :
    (u.hom ≫ s ≫ e.inv) ≫ (e.hom ≫ r ≫ u.inv) = 𝟙 W := by
  simp [reassoc_of% h]

/-- A retract `Y` of an object `X` with `Hom(X, Y)` a subsingleton has a subsingleton
endomorphism set. -/
theorem subsingleton_hom_of_retract {C : Type*} [Category C] {X Y : C} (i : Y ⟶ X) (p : X ⟶ Y)
    (h : i ≫ p = 𝟙 Y) (hX : Subsingleton (X ⟶ Y)) : Subsingleton (Y ⟶ Y) :=
  ⟨fun f g => by
    rw [← Category.id_comp f, ← Category.id_comp g, ← h, Category.assoc, Category.assoc]
    exact congrArg _ (hX.elim _ _)⟩

variable {B S hS}

/-- **The fibre-to-stalk step on an affine étale chart.**  Let `φ : h_{Spec A} ⟶ Y` be étale and
let `L ∈ D(𝒪_Y)` be modelled on the chart by a bounded above complex `P` of finite free
`A`-modules, `Lφ^*L ≅ ε^*(P~)`.  If `Ext^i(L_y, 𝒪_y) = 0` for every `i < 0` and every point
`y : Spec(k) ⟶ Y` with values in a field, then `P` has no cohomology in positive degrees.

Otherwise let `n > 0` be the top degree of the cohomology of `P`; after replacing `P` by a
complex of finite free modules vanishing above `n` (Stacks 064T), Nakayama's lemma gives a
maximal ideal `m` with `H^n(P ⊗_A A/m) ≠ 0`.  Then `k = A/m` placed in degree `n` is a retract of
`P ⊗_A k`, the derived pullback of `L` to the point `Spec k ⟶ Spec A ⟶ Y` is the chart model of
`P ⊗_A k` (`AlgebraicGeometry.Space.nonempty_smallEtaleDerivedModulePullback_chartModel_iso`),
and the chart model of `k[-n]` is `𝒪[-n]`; the retraction gives a nonzero map
`L_y ⟶ 𝒪_y[-n]`. -/
theorem isLE_zero_of_chartModel_of_forall_field {Y : AlgebraicSpaces B S hS}
    (L : derivedModules B S hS Y) {A : Type u} [CommRing A]
    (hA : B.Contains (Spec (CommRingCat.of A))) (gA : B.obj hA ⟶ B.obj hS)
    (φ : (⟨yoneda.obj (specFppfOver B S hS hA gA), isAlgebraicSpace_yoneda B S hS _⟩ :
      AlgebraicSpaces B S hS) ⟶ Y)
    (P : CochainComplex (ModuleCat.{u} A) ℤ)
    (hP : StacksDraft.PseudoCoherence.IsBoundedAboveFiniteFree P)
    (eP : ((smallEtaleDerivedPullbackData B S hS).pull φ).obj L ≅
      (chartModelFunctor B S hS hA gA).obj (DerivedCategory.Q.obj P))
    (hfib : ∀ T₀ : SchemesOver Y, Stack.IsFieldObject B S hS T₀.left → ∀ i : ℤ, i < 0 →
      Subsingleton (((smallEtaleDerivedPullbackData B S hS).pull T₀.hom).obj L ⟶
        (structureObject B S hS ((schemeSpaceFunctor B S hS).obj T₀.left))⟦i⟧)) :
    (DerivedCategory.Q.obj P).IsLE 0 := by
  classical
  by_contra hne
  obtain ⟨b, hb⟩ := hP.upperBound
  have hQb : (DerivedCategory.Q.obj P).IsLE b := inferInstance
  have hne' : ∃ n : ℤ, 0 < n ∧
      ¬ IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) n).obj
        (DerivedCategory.Q.obj P)) := by
    by_contra! h
    exact hne ((DerivedCategory.isLE_iff _ 0).2 h)
  obtain ⟨n, ⟨hn0, hn⟩, htop⟩ := Int.exists_greatest_of_bdd (P := fun n => 0 < n ∧
      ¬ IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) n).obj
        (DerivedCategory.Q.obj P)))
    ⟨b, fun n hn => by
      by_contra hlt
      exact hn.2 (DerivedCategory.isZero_of_isLE (DerivedCategory.Q.obj P) b n (by omega))⟩ hne'
  have hvan : ∀ i, n < i → IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj
      (DerivedCategory.Q.obj P)) := fun i hi => by
    by_contra h
    have := htop i ⟨by omega, h⟩
    omega
  obtain ⟨P', α, hP'fin, hP'le, hα⟩ :=
    StacksDraft.PseudoCoherence.IsPseudoCoherentIn.exists_finiteFree_representative_le
      ⟨P, hP, ⟨Iso.refl _⟩⟩ n hvan
  have hH' : ¬ IsZero (P'.homology n) := fun h => hn
    ((h.of_iso (StacksDraft.PseudoCoherence.homologyQObjIso P' n)).of_iso
      ((DerivedCategory.homologyFunctor _ n).mapIso (asIso α)).symm)
  have hP'1 : IsZero (P'.X (n + 1)) := P'.isZero_of_isStrictlyLE n (n + 1) (by omega)
  obtain ⟨m, hm, hmH⟩ := exists_isMaximal_not_isZero_homology_extendScalars P' n
    (hP'fin n).1 hP'1 hH'
  let : Field (A ⧸ m) := Ideal.Quotient.field m
  have : _root_.AlgebraicGeometry.IsClosedImmersion
      (Spec.map (CommRingCat.ofHom (algebraMap A (A ⧸ m)))) :=
    _root_.AlgebraicGeometry.IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  have hk : B.Contains (Spec (CommRingCat.of (A ⧸ m))) :=
    lt_of_le_of_lt (Scheme.size_le_of_mono_quasiCompact
      (Spec.map (CommRingCat.ofHom (algebraMap A (A ⧸ m))))) hA
  let gk : B.obj hk ⟶ B.obj hS :=
    (ObjectProperty.homMk (Spec.map (CommRingCat.ofHom (algebraMap A (A ⧸ m)))) :
      B.obj hk ⟶ B.obj hA) ≫ gA
  let rg := representedSpaceMap B S hS (specFppfOverMap B S hS hA gA hk gk rfl)
  let T₀ : SchemesOver Y := CostructuredArrow.mk
    (show (schemeSpaceFunctor B S hS).obj (specFppfOver B S hS hk gk) ⟶ Y from rg ≫ φ)
  have hT₀ : Stack.IsFieldObject B S hS T₀.left := ⟨A ⧸ m, inferInstance, ⟨Iso.refl _⟩⟩
  have hsub := hfib T₀ hT₀ (-n) (by omega)
  let eP' : ((smallEtaleDerivedPullbackData B S hS).pull φ).obj L ≅
      (chartModelFunctor B S hS hA gA).obj (DerivedCategory.Q.obj P') :=
    eP ≪≫ (chartModelFunctor B S hS hA gA).mapIso (asIso α).symm
  obtain ⟨e₆⟩ := nonempty_smallEtaleDerivedModulePullback_chartModel_iso B S hS hA gA hk gk rfl
    P' ⟨⟨n, hP'le⟩, hP'fin⟩
  let K := (CochainComplex.extendScalars (algebraMap A (A ⧸ m))).obj P'
  let E : ((smallEtaleDerivedPullbackData B S hS).pull T₀.hom).obj L ≅
      (chartModelFunctor B S hS hk gk).obj (DerivedCategory.Q.obj K) :=
    ((smallEtaleDerivedPullbackData B S hS).compIso rg φ).app L ≪≫
      ((smallEtaleDerivedPullbackData B S hS).pull rg).mapIso eP' ≪≫ e₆
  obtain ⟨s, r, hsr⟩ := exists_single_retract_of_not_isZero_homology K n
    ((ModuleCat.extendScalars (algebraMap A (A ⧸ m))).map_isZero hP'1) hmH
  let ι := (DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{u} (A ⧸ m)) n).app
    (ModuleCat.of (A ⧸ m) (A ⧸ m))
  let s' := ι.hom ≫ DerivedCategory.Q.map s
  let r' := DerivedCategory.Q.map r ≫ ι.inv
  have hQsr : DerivedCategory.Q.map s ≫ DerivedCategory.Q.map r = 𝟙 _ :=
    ((Retract.mk s r hsr).map DerivedCategory.Q).retract
  have hsr' : s' ≫ r' = 𝟙 _ := by simp [s', r', reassoc_of% hQsr]
  let Fk := chartModelFunctor B S hS hk gk
  let U := chartModelFunctorSingleIso B S hS hk gk n
  have hip := comp_retract_eq_id U.symm E (Fk.map s') (Fk.map r')
    ((Retract.mk s' r' hsr').map Fk).retract
  have hEnd := subsingleton_hom_of_retract _ _ hip hsub
  have hEnd' : Subsingleton (structureObject B S hS (schemeSpace (specFppfOver B S hS hk gk)) ⟶
      structureObject B S hS (schemeSpace (specFppfOver B S hS hk gk))) :=
    ⟨fun f g => (shiftFunctor (derivedModules B S hS (schemeSpace (specFppfOver B S hS hk gk)))
      (-n)).map_injective (hEnd.elim _ _)⟩
  exact not_isZero_structureObject_specFppfOver B S hS hk gk
    ((IsZero.iff_id_eq_zero _).2 (Subsingleton.elim _ _))

/-! ### The fibre-to-stalk step -/

variable (B S hS) in
/-- **The fibre-to-stalk step of the proof of Stacks 0DLC.**  A pseudo-coherent object `L` of
`D(𝒪_Y)` on an algebraic space `Y` such that `Ext^i(L_y, 𝒪_y) = 0` for every `i < 0` and every
point `y : Spec(k) ⟶ Y` with values in a field has no cohomology in positive degrees.

The question is étale local on `Y`
(`AlgebraicGeometry.Space.isLE_of_isLE_smallEtaleDerivedModulePullback_chartToSpace`), and the
affine étale charts cover `Y`.  On an affine chart `h_{Spec A} ⟶ Y`, `L` is modelled by a bounded
above complex of finite free `A`-modules
(`AlgebraicGeometry.Space.exists_isBoundedAboveFiniteFree_etaleModulePullback_iso`, through
Stacks 08JL, 071Q, 08HE, 06Z0 and 08E7), and there
`AlgebraicGeometry.Space.isLE_zero_of_chartModel_of_forall_field` applies: this is Stacks 0BCC's
reading of the cohomology of a pseudo-coherent complex off its fibres, by Nakayama's lemma at the
top degree. -/
theorem fieldFibreDualVanishingIsLE : FieldFibreDualVanishingIsLE B S hS := by
  intro Y L hL hfib
  refine isLE_of_isLE_smallEtaleDerivedModulePullback_chartToSpace B S hS
    (SmallEtale.coversTop_affineCharts B S hS Y.1) L 0 fun ⟨V, hV⟩ => ?_
  let U := (SmallEtale.toOver B S hS Y.1).obj V
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj U) := hV
  let e := ((BigFppfOver.toScheme B S hS).obj U).isoSpec
  have hA : B.Contains (Spec (CommRingCat.of Γ((BigFppfOver.toScheme B S hS).obj U, ⊤))) :=
    lt_of_le_of_lt (Scheme.size_le_of_mono_quasiCompact e.inv) U.left.2
  let gA : B.obj hA ⟶ B.obj hS := ObjectProperty.homMk e.inv ≫ U.hom
  let eV : specFppfOver B S hS hA gA ≅ U :=
    Over.isoMk (B.inclusion.preimageIso e.symm) (B.inclusion.map_injective (by
      rw [Functor.map_comp, Functor.preimageIso_hom, Functor.map_preimage]
      rfl))
  let c := chartToSpace B S hS Y V
  let φ := representedSpaceMap B S hS eV.hom ≫ c
  have hφ : IsEtale B S hS φ.hom :=
    isEtale_comp B S hS (isEtale_of_isIso B S hS (yoneda.map eV.hom))
      (isEtale_chartToSpace B S hS Y V)
  obtain ⟨P, hP, ⟨eP⟩⟩ :=
    exists_isBoundedAboveFiniteFree_etaleModulePullback_iso B S hS hA gA φ hφ L hL
  obtain ⟨e₁⟩ := nonempty_etaleModulePullback_mapDerivedCategory_iso φ hφ L
  have hPLE := isLE_zero_of_chartModel_of_forall_field L hA gA φ P hP (e₁.symm ≪≫ eP) hfib
  have hM : ((chartModelFunctor B S hS hA gA).obj (DerivedCategory.Q.obj P)).IsLE 0 := by
    have := Stacks.Homology.isLE_mapDerivedCategory_obj
      (tilde.functor (CommRingCat.of Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)) ⋙
        Scheme.Modules.restrictFunctor
          (Iso.refl ((BigFppfOver.toScheme B S hS).obj (specFppfOver B S hS hA gA))).hom)
      (DerivedCategory.Q.obj P) 0
    exact Stacks.Homology.isLE_mapDerivedCategory_obj (representedAssociatedModule B S hS
      (specFppfOver B S hS hA gA) (isAlgebraicSpace_yoneda B S hS _)) _ 0
  have hφLE : (((smallEtaleDerivedPullbackData B S hS).pull φ).obj L).IsLE 0 := by
    have : ((representedDerivedAssociatedModule B S hS (specFppfOver B S hS hA gA)).obj
        ((tilde.functor (CommRingCat.of Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)) ⋙
          Scheme.Modules.restrictFunctor
            (Iso.refl ((BigFppfOver.toScheme B S hS).obj (specFppfOver B S hS hA gA))).hom
            ).mapDerivedCategory.obj (DerivedCategory.Q.obj P))).IsLE 0 := hM
    exact DerivedCategory.TStructure.t.isLE_of_iso (e₁.symm ≪≫ eP).symm 0
  have hc : representedSpaceMap B S hS eV.inv ≫ φ = c := by
    refine ObjectProperty.hom_ext _ ?_
    show yoneda.map eV.inv ≫ yoneda.map eV.hom ≫ c.hom = c.hom
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ c.hom)
      ((yoneda.map_comp _ _).symm.trans ((congrArg yoneda.map eV.inv_hom_id).trans
        (yoneda.map_id _)))).trans (Category.id_comp _))
  have h₂ : (((smallEtaleDerivedPullbackData B S hS).pull φ ⋙
      (smallEtaleDerivedPullbackData B S hS).pull
        (representedSpaceMap B S hS eV.inv)).obj L).IsLE 0 :=
    isLE_smallEtaleDerivedModulePullback_obj (representedSpaceMap B S hS eV.inv) _ 0 hφLE
  exact DerivedCategory.TStructure.t.isLE_of_iso
    (((smallEtaleDerivedPullbackData B S hS).triangle hc).app L).symm 0

section QuasiCompactBase

/- The instances under which `AlgebraicGeometry.Space.RelativeDerivedHomDualExists` and the
statement of
`AlgebraicGeometry.Space.negativeExtVanishesOfFibres_of_quasiCompact_of_quasiSeparated` are
elaborated. -/
attribute [local instance] AlgebraicGeometry.Space.inverseImageRingedSite_hasWeakSheafify_over
  AlgebraicGeometry.Space.inverseImageRingedSite_wEqualsLocallyBijective_over
  AlgebraicGeometry.Space.inverseImageRingedSite_hasDerivedCategory
  Stacks.hasSheafCompose_forget₂_commRingCat
  AlgebraicGeometry.RingedSite.sliceHasSheafify
  AlgebraicGeometry.RingedSite.sliceWEqualsLocallyBijective
  AlgebraicGeometry.RingedSite.sliceRestrictionPreservesFiniteLimits
  AlgebraicGeometry.RingedSite.sliceRestrictionPreservesFiniteColimits
  AlgebraicGeometry.Space.inverseImageRingedSite_slice_hasDerivedCategory
  AlgebraicGeometry.RingedSite.sliceHasDerivedCategory
  Stacks.SheafOfModules.DerivedTensorProduct.sliceDerived
  AlgebraicGeometry.Space.inverseImageRingedSite_slice_sheafTensor_additive
  AlgebraicGeometry.Space.inverseImageRingedSite_slice_sheafTensor_obj_additive
  AlgebraicGeometry.Space.inverseImageRingedSite_slice_hasMapBifunctor
  Stacks.SheafOfModules.DerivedTensorProduct.sliceTensorAdditive
  Stacks.SheafOfModules.DerivedTensorProduct.sliceTensorObjAdditive
  Stacks.SheafOfModules.DerivedTensorProduct.sliceHasMapBifunctor
  AlgebraicGeometry.Space.instModulesHasDerivedCategory

/-- **Stacks 0DLC, part (2), in the case `W = Y`, over a quasi-compact and quasi-separated
base, granted Stacks 0DKY alone.**  This is
`AlgebraicGeometry.Space.negativeExtVanishesOfFibres_of_quasiCompact_of_quasiSeparated` with its
fibre-to-stalk hypothesis discharged by `AlgebraicGeometry.Space.fieldFibreDualVanishingIsLE`.
The hypothesis `h0DKY` is Stacks 0DKY, not yet proved here. -/
theorem negativeExtVanishesOfFibres_of_quasiCompact_of_quasiSeparated_of_dualExists
    (h0DKY : RelativeDerivedHomDualExists B S hS)
    (hZ : B.Contains (⊤_ Scheme.{u})) {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (hqc : IsQuasiCompactSpace B S hS Y.1)
    (hqs : IsAbsolutelyQuasiSeparated B S hS hZ Y.1) (hp : IsProper B S hS f.hom)
    (hflat : IsFlat B S hS f.hom) (hfp : IsFinitePresentation B S hS f.hom)
    (K E : derivedModules B S hS X)
    (hK : (smallEtaleRingedSite B S hS X.1 X.2).IsPseudoCoherent K)
    (hE : IsPerfectRelativeToCanonical B S hS f hflat hfp.1 E)
    (hfib : ∀ T₀ : SchemesOver Y, Stack.IsFieldObject B S hS T₀.left → HasNoNegativeExtAt f K E T₀)
    (V : Over Y) (i : ℤ) (hi : i < 0) :
    Subsingleton (((smallEtaleDerivedPullbackData B S hS).pull (overProjection f V)).obj K ⟶
      (((smallEtaleDerivedPullbackData B S hS).pull (overProjection f V)).obj E)⟦i⟧) :=
  negativeExtVanishesOfFibres_of_quasiCompact_of_quasiSeparated h0DKY
    (fieldFibreDualVanishingIsLE B S hS) hZ f hqc hqs hp hflat hfp K E hK hE hfib V i hi

end QuasiCompactBase

end AlgebraicGeometry.Space
