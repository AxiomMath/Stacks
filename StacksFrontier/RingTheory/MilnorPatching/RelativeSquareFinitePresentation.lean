module

public import StacksFrontier.RingTheory.MilnorPatching.BaseChangeGlueing
public import StacksFrontier.RingTheory.MilnorPatching.RelativeProperties

/-!
# Finite presentation in a relative Milnor square

In the relative Milnor square `MilnorPatching.IsRelativeSquare` (the situation of Stacks 08KK,
with the rings given up to isomorphism), a `D'`-module `L` flat over `B'` whose base changes to
`D` and to `C'` are of finite presentation is itself of finite presentation over `D'`, as soon as
`B' → D'` is of finite presentation.  This is Stacks 08KP for the trivial factorization of
`B' → D'`, transported from the library's fibre-product situation.

## References

* [Stacks Project, Tag 08KP](https://stacks.math.columbia.edu/tag/08KP)
* [Stacks Project, Tag 08KR](https://stacks.math.columbia.edu/tag/08KR)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct ChangeOfRings

universe u

namespace MilnorPatching

variable {B' B A' A D' D C' C : Type u} [CommRing B'] [CommRing B] [CommRing A'] [CommRing A]
  [CommRing D'] [CommRing D] [CommRing C'] [CommRing C]
  {σ : B' →+* B} {σ' : B' →+* A'} {τ : B →+* A} {π : A' →+* A}
  {ρ : B' →+* D'} {δ : D' →+* D} {βD : B →+* D} {γ : D' →+* C'} {αC : A' →+* C'}
  {ε : D →+* C} {ε' : C' →+* C} {κ : A →+* C}

/-- If `p : L → N` exhibits `N` as the base change of `L` along `δ : R → S`, `N` is finitely
presented over `S`, and `T` is an `R`-algebra through `S`, then `T ⊗[R] L` is finitely presented
over `T`. -/
private theorem finitePresentation_tensor_of_isBaseChangeAlong {R S T : Type u} [CommRing R]
    [CommRing S] [CommRing T] [Algebra R T] {δ : R →+* S} {φ : S →+* T}
    (hφ : φ.comp δ = algebraMap R T) {L N : Type u} [AddCommGroup L] [Module R L]
    [AddCommGroup N] [Module S N] {p : L →ₛₗ[δ] N} (hp : IsBaseChangeAlong δ p)
    [Module.FinitePresentation S N] : Module.FinitePresentation T (T ⊗[R] L) := by
  let : Algebra R S := δ.toAlgebra
  let : Algebra S T := φ.toAlgebra
  have : IsScalarTower R S T := IsScalarTower.of_algebraMap_eq' (by exact hφ.symm)
  let e₀ : S ⊗[R] L ≃ₗ[S] N := LinearEquiv.ofBijective (liftAlong δ p) hp
  exact Module.FinitePresentation.of_equiv
    ((TensorProduct.AlgebraTensorModule.cancelBaseChange R S T T L).symm ≪≫ₗ
      TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl T T) e₀).symm

/-- The `R`-linear identification of `T`, viewed as an `R`-module through its algebra structure,
with `T`. -/
private def restrictScalarsSelfEquiv {R T : Type u} [CommRing R] [CommRing T] [Algebra R T] :
    (ModuleCat.restrictScalars (algebraMap R T)).obj (ModuleCat.of T T) ≃ₗ[R] T :=
  { Equiv.refl T with
    map_add' := fun _ _ => rfl
    map_smul' := fun r x => (Algebra.smul_def r (show T from x)).symm }

/-- A module `M` additively identified with `X ⊗[R] L`, where `X ≃ₗ[R] T`, compatibly with the
`T`-action on pure tensors, is finitely presented over `T` as soon as `T ⊗[R] L` is. -/
private theorem finitePresentation_of_addEquiv_tensor {R T L M X : Type u} [CommRing R]
    [CommRing T] [Algebra R T] [AddCommGroup L] [Module R L] [AddCommGroup M] [Module T M]
    [AddCommGroup X] [Module R X] [Module.FinitePresentation T (T ⊗[R] L)] (e₁ : X ≃ₗ[R] T)
    (e : M ≃+ X ⊗[R] L)
    (h : ∀ (c : T) (t : X) (m : L), e (c • e.symm (t ⊗ₜ m)) = e₁.symm (c * e₁ t) ⊗ₜ m) :
    Module.FinitePresentation T M := by
  let eT := TensorProduct.congr e₁ (LinearEquiv.refl R L)
  refine Module.FinitePresentation.of_equiv
    ({ e.trans eT.toAddEquiv with map_smul' := fun c x => ?_ } : M ≃ₗ[T] T ⊗[R] L).symm
  obtain ⟨y, rfl⟩ := e.symm.surjective x
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add y z hy hz => simp_all [smul_add]
  | tmul t m => simp [eT, h, TensorProduct.smul_tmul']

/-- **A relatively flat module with finitely presented base changes is finitely presented**
(Stacks 08KP, for `B' → D'` of finite presentation): in a relative Milnor square, a `D'`-module
`L` flat over `B'` whose base changes `D ⊗_{D'} L` and `C' ⊗_{D'} L` are finitely presented over
`D` and over `C'` is finitely presented over `D'`. -/
theorem IsRelativeSquare.finitePresentation_of_flat
    (h : IsRelativeSquare σ σ' τ π ρ δ βD γ αC ε ε' κ) (hρ : ρ.FinitePresentation)
    {L : Type u} [AddCommGroup L] [Module D' L] (hL : @Module.Flat B' L _ _ (Module.compHom L ρ))
    {N N' : Type u} [AddCommGroup N] [Module D N] [AddCommGroup N'] [Module C' N']
    {p : L →ₛₗ[δ] N} {p' : L →ₛₗ[γ] N'} (hp : IsBaseChangeAlong δ p)
    (hp' : IsBaseChangeAlong γ p') (hN : Module.FinitePresentation D N)
    (hN' : Module.FinitePresentation C' N') :
    Module.FinitePresentation D' L := by
  classical
  let base : RingFibreProduct.Situation τ π (RingHom.ker π) := ⟨h.fibre.surjective, rfl⟩
  let κ₀ : B' →+* base.fibreProduct :=
    RingHom.codRestrict (σ.prod σ') (RingHom.pullback τ π)
      (fun x => DFunLike.congr_fun h.fibre.comm x)
  have hκ : Function.Bijective κ₀ := ⟨fun x y hxy => h.fibre.injective x y
    (congrArg (fun z : base.fibreProduct => z.1.1) hxy)
    (congrArg (fun z : base.fibreProduct => z.1.2) hxy), h.fibre.surjective_toPullback⟩
  let eκ : B' ≃+* base.fibreProduct := RingEquiv.ofBijective κ₀ hκ
  let s : RelativeModuleFibreProductSituation (D' := D') base := ⟨ρ.comp eκ.symm.toRingHom⟩
  obtain ⟨F, -, adj, -, -, hcounit, -, hunit, q, ⟨eq⟩, -⟩ :=
    relativelyFlatModulesEquivalenceOverFibreProduct s
  let E := (let : Algebra base.fibreProduct D' := s.toD'.toAlgebra
    let : Algebra base.fibreProduct B := (τ.pullbackFst π).toAlgebra
    let : Algebra base.fibreProduct A' := (τ.pullbackSnd π).toAlgebra
    let : Algebra base.fibreProduct A := (τ.comp (τ.pullbackFst π)).toAlgebra
    extensionOfScalarsToTensorProductPullback (D' := D')
      ({ τ with commutes' := fun _ => rfl } : B →ₐ[base.fibreProduct] A)
      ({ π with commutes' := fun r => r.property.symm } : A' →ₐ[base.fibreProduct] A))
  let L' : ModuleCat.{u} D' := ModuleCat.of D' L
  have hL' : Module.Flat base.fibreProduct ((ModuleCat.restrictScalars s.toD').obj L') := by
    let : Module B' L := Module.compHom L ρ
    let : Algebra base.fibreProduct B' := eκ.symm.toRingHom.toAlgebra
    let : Module base.fibreProduct L := Module.compHom L s.toD'
    have : IsScalarTower base.fibreProduct B' L :=
      IsScalarTower.of_algebraMap_smul fun _ _ => rfl
    have : Module.Flat base.fibreProduct B' := RingHom.Flat.of_bijective eκ.symm.bijective
    have : Module.Flat B' L := hL
    exact Module.Flat.trans base.fibreProduct B' L
  let e₁ := eq.app ⟨L', hL'⟩
  have hfl₁ : Module.Flat B ((ModuleCat.restrictScalars s.BtoD).obj (E.obj L').fst) :=
    @Module.Flat.of_linearEquiv _ _ _ _ _ _ _ _ (q.functor.obj ⟨L', hL'⟩).property.1
      ((ModuleCat.restrictScalars s.BtoD).mapIso
        ((CategoricalPullback.π₁ _ _).mapIso e₁)).toLinearEquiv
  have hfl₂ : Module.Flat A' ((ModuleCat.restrictScalars s.A'toC').obj (E.obj L').snd) :=
    @Module.Flat.of_linearEquiv _ _ _ _ _ _ _ _ (q.functor.obj ⟨L', hL'⟩).property.2
      ((ModuleCat.restrictScalars s.A'toC').mapIso
        ((CategoricalPullback.π₂ _ _).mapIso e₁)).toLinearEquiv
  have hκρ : ∀ x : B', s.toD' (κ₀ x) = ρ x := fun x => congrArg ρ (eκ.symm_apply_apply x)
  have hfp₁ : Module.FinitePresentation s.D (E.obj L').fst := by
    have hw : CommRingCat.ofHom σ ≫ CommRingCat.ofHom s.BtoD =
        CommRingCat.ofHom ρ ≫ CommRingCat.ofHom s.toD := by
      ext x
      have := DFunLike.congr_fun s.toD_toD' (κ₀ x)
      simp only [RingHom.coe_comp, Function.comp_apply, hκρ] at this
      exact this.symm
    have := finitePresentation_tensor_of_isBaseChangeAlong (T := s.D)
      (φ := (h.pushD.desc _ _ hw).hom) (congrArg CommRingCat.Hom.hom (h.pushD.inr_desc _ _ hw)) hp
    exact finitePresentation_of_addEquiv_tensor (T := s.D) restrictScalarsSelfEquiv
      (AddEquiv.refl _) fun _ _ _ => rfl
  have hfp₂ : Module.FinitePresentation s.C' (E.obj L').snd := by
    have hw : CommRingCat.ofHom σ' ≫ CommRingCat.ofHom s.A'toC' =
        CommRingCat.ofHom ρ ≫ CommRingCat.ofHom s.toC' := by
      ext x
      have := DFunLike.congr_fun s.toC'_toD' (κ₀ x)
      simp only [RingHom.coe_comp, Function.comp_apply, hκρ] at this
      exact this.symm
    have := finitePresentation_tensor_of_isBaseChangeAlong (T := s.C')
      (φ := (h.pushC'.desc _ _ hw).hom)
      (congrArg CommRingCat.Hom.hom (h.pushC'.inr_desc _ _ hw)) hp'
    exact finitePresentation_of_addEquiv_tensor (T := s.C') restrictScalarsSelfEquiv
      (AddEquiv.refl _) fun _ _ _ => rfl
  have : Module.FinitePresentation D' ((E ⋙ F).obj L') :=
    finitePresentation_rightAdjoint_obj_of_factorization s F adj hcounit (E.obj L')
    hfp₁ hfl₁ hfp₂ hfl₂ (RingHom.id base.fibreProduct) s.toD' (RingHom.comp_id _)
    (inferInstanceAs (Module.Flat base.fibreProduct base.fibreProduct))
    (hρ.comp (RingHom.FinitePresentation.of_bijective eκ.symm.bijective))
  have := hunit L' hL'
  exact Module.FinitePresentation.of_equiv (asIso (adj.unit.app L')).toLinearEquiv.symm

end MilnorPatching

end
