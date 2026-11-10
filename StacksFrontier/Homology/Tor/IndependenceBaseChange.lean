module

public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Module.ULift
public import Mathlib.CategoryTheory.Monoidal.Tor
public import Mathlib.RingTheory.IsTensorProduct
public import StacksFrontier.Homology.KFlat.Flat
public import StacksFrontier.Homology.KFlat.Resolution
public import StacksFrontier.Homology.Tor.DerivedChangeOfRings
public import StacksFrontier.Homology.Tor.DerivedTensorLargeUniverse
public import StacksFrontier.Homology.Tor.Independence
public import StacksCore.Tactic.StacksAttribute
import StacksFrontier.Algebra.Homology.Embedding.ExtendMap
public import StacksFrontier.Homology.TensorComplex.TensorUnitIso

@[expose] public noncomputable section

set_option maxRecDepth 4096

/-!
# Tor-independent base change

Let `R → A` and `R → R'` be homomorphisms of commutative rings and let `A'` be a pushout of the
square, so `A' = A ⊗[R] R'`. For a complex `K` of `A`-modules there is a canonical comparison
`K ⊗ᴸ_R R' ⟶ K ⊗ᴸ_A A'` in `D(R')`, relating base change over the base ring to base change over
the algebra.

This comparison is an isomorphism when `A` and `R'` are Tor independent over `R`, that is when
`Torᵢ^R(A, R')` vanishes for every `i > 0`.

## Main definitions

There are no new definitions.

## Main results

* `RingTheory.TorIndependence.derivedBaseChangeComparison_isIso_of_torIndependent`: Tor
  independence makes the canonical derived base-change comparison invertible.

## Implementation notes

The identification `A' = A ⊗[R] R'` is expressed by `Algebra.IsPushout`, so the statement covers
every realization of the base-change square, including `R' ⊗[R] A` itself. The two scalar towers
express commutativity of the square, and the pushout condition says that the canonical map from
`A ⊗[R] R'` to `A'` is an isomorphism. The conclusion is stated for the natural transformation
supplied by the canonical comparison, so it applies simultaneously at every object of the derived
category and records functoriality.

The proof reduces to K-flat complexes of `A`-modules, which represent every object of `D(A)`. On
such a complex `K` the counit of derived extension of scalars along `A → A'` is invertible, and
so is the counit of derived extension of scalars along `R → R'` at the restriction of `K` to an
`R`-complex: Tor independence provides a K-flat resolution of `A`, viewed as an `R`-complex,
which extension of scalars along `R → R'` carries to a quasi-isomorphism. The underived
comparison is itself invertible because the pushout square identifies `R' ⊗_R M` with
`A' ⊗_A M` for every `A`-module `M`.

The four rings and the module size carry independent universe parameters. The comparison is
formulated for arbitrary derived-category models, so the transfer of an invertibility statement
between two localizations of the same category is proved once, abstractly.

## References

* [The Stacks Project, Tag 0661](https://stacks.math.columbia.edu/tag/0661)
* [The Stacks Project, Tag 0660](https://stacks.math.columbia.edu/tag/0660)
* [The Stacks Project, Tag 065Z](https://stacks.math.columbia.edu/tag/065Z)
-/

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct ChangeOfRings

namespace RingTheory.TorIndependence

universe uR uA uB uRp uAp v w

/-- Extension of scalars along a bare ring homomorphism is additive. -/
private theorem extendScalarsAdditive {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) : (ModuleCat.extendScalars.{_, _, w} f).Additive := by
  let := f.toAlgebra
  constructor
  intro X Y a b
  ext x
  change (1 : S) ⊗ₜ[R,f] ((a + b) x) =
    (1 : S) ⊗ₜ[R,f] a x + (1 : S) ⊗ₜ[R,f] b x
  rw [show (a + b : X ⟶ Y) x = a x + b x by rfl, TensorProduct.tmul_add]

attribute [local instance] extendScalarsAdditive

/-- A transformation of functors on a localization is invertible as soon as it is invertible on
the images of the objects of a class through which every object admits a resolution. -/
private theorem isIso_of_isIso_app_of_left_resolutions
    {C D H : Type*} [Category* C] [Category* D] [Category* H]
    (Q : C ⥤ D) (W : MorphismProperty C) [Q.IsLocalization W]
    (P : ObjectProperty C)
    (hP : ∀ X : C, ∃ (Y : C), P Y ∧ ∃ f : Y ⟶ X, W f)
    {F G : D ⥤ H} (τ : F ⟶ G)
    (hτ : ∀ X : C, P X → IsIso (τ.app (Q.obj X))) : IsIso τ := by
  have : Q.EssSurj := Localization.essSurj Q W
  have : ∀ X, IsIso (τ.app X) := by
    intro X
    obtain ⟨Y, hY, f, hf⟩ := hP (Q.objPreimage X)
    have : IsIso (Q.map f) := Localization.inverts Q W f hf
    have h := (NatTrans.isIso_app_iff_of_iso τ (asIso (Q.map f))).1 (hτ Y hY)
    exact (NatTrans.isIso_app_iff_of_iso τ (Q.objObjPreimageIso X)).1 h
  exact NatIso.isIso_of_isIso_app τ

/-- If the `n`-th left derived functor vanishes at `X`, then the image of a projective
resolution of `X` is exact in degree `n`. -/
private theorem exactAt_map_projectiveResolution_of_isZero_leftDerived
    {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
    [HasProjectiveResolutions C] (F : C ⥤ D) [F.Additive]
    {X : C} (P : ProjectiveResolution X) (n : ℕ)
    (h : IsZero ((F.leftDerived n).obj X)) :
    ((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex).ExactAt n := by
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  exact h.of_iso (P.isoLeftDerivedObj F n).symm

set_option backward.isDefEq.respectTransparency false in
/-- If every positive-degree left derived functor of a right exact functor vanishes at `X`, then
the functor carries a projective resolution of `X` to a quasi-isomorphism. -/
public theorem quasiIso_map_projectiveResolution_of_isZero_leftDerived
    {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
    [HasProjectiveResolutions C] (F : C ⥤ D) [F.Additive]
    [PreservesFiniteColimits F] {X : C} (P : ProjectiveResolution X)
    (h : ∀ n : ℕ, 0 < n → IsZero ((F.leftDerived n).obj X)) :
    QuasiIso ((F.mapHomologicalComplex (ComplexShape.down ℕ)).map P.π) := by
  constructor
  intro n
  cases n with
  | zero =>
    rw [ChainComplex.quasiIsoAt₀_iff]
    apply (ShortComplex.quasiIso_iff_of_zeros' _ (by simp) (by simp) (by simp)).2
    constructor
    · exact P.exact₀.map_of_epi_of_preservesCokernel F inferInstance inferInstance
    · change Epi (F.map (P.π.f 0))
      infer_instance
  | succ n =>
    apply (quasiIsoAt_iff_exactAt' _ _ ?_).2
    · exact exactAt_map_projectiveResolution_of_isZero_leftDerived F P (n + 1)
        (h (n + 1) (Nat.succ_pos n))
    · rw [HomologicalComplex.exactAt_iff]
      exact ShortComplex.exact_of_isZero_X₂ _
        (F.map_isZero (HomologicalComplex.isZero_single_obj_X _ _ _ _ (by omega)))

/-- The canonical map `B ⊗[R] M → (A ⊗[R] B) ⊗[A] M`, for an `A`-module `M` regarded as an
`R`-module, is bijective: both sides are `A ⊗[R] B ⊗[A] M` after reassociating. -/
private theorem bijective_tensorProduct_baseChange
    {R A B M : Type*} [CommSemiring R] [CommSemiring A] [CommSemiring B]
    [Algebra R A] [Algebra R B] [AddCommMonoid M]
    [Module R M] [Module A M] [IsScalarTower R A M]
    (φ : B ⊗[R] M →+ (A ⊗[R] B) ⊗[A] M)
    (hφ : ∀ b m, φ (b ⊗ₜ[R] m) = (1 ⊗ₜ[R] b) ⊗ₜ[A] m) :
    Function.Bijective φ := by
  let e : B ⊗[R] M ≃ₗ[R] (A ⊗[R] B) ⊗[A] M :=
    TensorProduct.comm R B M ≪≫ₗ
      TensorProduct.congr ((TensorProduct.rid A M).symm.restrictScalars R)
        (LinearEquiv.refl R B) ≪≫ₗ
      (TensorProduct.AlgebraTensorModule.assoc R A A M A B).restrictScalars R ≪≫ₗ
      (TensorProduct.comm A M (A ⊗[R] B)).restrictScalars R
  have he : ∀ x, φ x = e x := by
    intro x
    induction x using TensorProduct.inductionOn with
    | tmul b m => simpa [e] using hφ b m
    | add x y hx hy => simp [hx, hy]
  exact (show (φ : B ⊗[R] M → (A ⊗[R] B) ⊗[A] M) = e from funext he) ▸ e.bijective

/-- Vanishing of the positive Tor groups makes tensoring with `X` carry a projective resolution
of `Y` to a quasi-isomorphism. -/
public theorem quasiIso_tensor_map_projectiveResolution_of_isZero_Tor
    {C : Type*} [Category* C] [Abelian C] [MonoidalCategory C]
    [MonoidalPreadditive C] [HasProjectiveResolutions C] (X Y : C)
    [PreservesFiniteColimits ((MonoidalCategory.tensoringLeft C).obj X)]
    (P : ProjectiveResolution Y)
    (h : ∀ n : ℕ, 0 < n → IsZero (((Tor C n).obj X).obj Y)) :
    QuasiIso ((((MonoidalCategory.tensoringLeft C).obj X).mapHomologicalComplex
      (ComplexShape.down ℕ)).map P.π) :=
  quasiIso_map_projectiveResolution_of_isZero_leftDerived _ P h

set_option backward.isDefEq.respectTransparency false in
/-- The underived comparison for a pushout square is invertible: for an `A`-module `M`, the
canonical map `R' ⊗_R M → A' ⊗_A M` is bijective because `A' = A ⊗[R] R'`. -/
private theorem isIso_baseChange_of_isPushout
    {R : Type uR} {A : Type uA} {B : Type uB} {S : Type uAp}
    [CommRing R] [CommRing A] [CommRing B] [CommRing S]
    [Algebra R A] [Algebra R B] [Algebra R S] [Algebra A S] [Algebra B S]
    [IsScalarTower R A S] [IsScalarTower R B S] [Algebra.IsPushout R A B S]
    (τ : ModuleCat.restrictScalars.{max v uR uA uB uAp} (algebraMap R A) ⋙
        ModuleCat.extendScalars (algebraMap R B) ⟶
      ModuleCat.extendScalars (algebraMap A S) ⋙
        ModuleCat.restrictScalars (algebraMap B S))
    (hτ : ∀ (M : ModuleCat.{max v uR uA uB uAp} A) (b : B) (m : M),
      τ.app M (b ⊗ₜ[R,algebraMap R B] m) =
        (algebraMap B S b) ⊗ₜ[A,algebraMap A S] m) : IsIso τ := by
  have : ∀ M, IsIso (τ.app M) := by
    intro M
    rw [ConcreteCategory.isIso_iff_bijective]
    let : Module R M := Module.compHom M (algebraMap R A)
    let : IsScalarTower R A M := ⟨fun r a m => by
      rw [Algebra.smul_def]
      change ((algebraMap R A r) * a) • m = (algebraMap R A r) • a • m
      exact mul_smul _ _ _⟩
    let eB : (ModuleCat.restrictScalars (algebraMap R B)).obj (ModuleCat.of B B) ≃ₗ[R] B :=
      { AddEquiv.refl B with
        map_smul' := fun r b => (Algebra.smul_def (R := R) (A := B) r b).symm }
    let eS : (ModuleCat.restrictScalars (algebraMap A S)).obj
        (ModuleCat.of S S) ≃ₗ[A] S :=
      { AddEquiv.refl S with
        map_smul' := fun a x => (Algebra.smul_def (R := A) (A := S) a x).symm }
    let eA := eS.trans (Algebra.IsPushout.equiv R A B S).symm.toLinearEquiv
    let u := TensorProduct.congr eB (LinearEquiv.refl R M)
    let w := TensorProduct.congr eA (LinearEquiv.refl A M)
    let ψ := w.toAddEquiv.toAddMonoidHom.comp
      ((τ.app M).hom.toAddMonoidHom.comp u.symm.toAddEquiv.toAddMonoidHom)
    have hψ : Function.Bijective ψ := by
      apply bijective_tensorProduct_baseChange
      intro b m
      change w (τ.app M (u.symm (b ⊗ₜ[R] m))) = ((1 : A) ⊗ₜ[R] b) ⊗ₜ[A] m
      change w (τ.app M (b ⊗ₜ[R,algebraMap R B] m)) = _
      rw [hτ]
      change (Algebra.IsPushout.equiv R A B S).symm (algebraMap B S b) ⊗ₜ[A] m = _
      rw [Algebra.IsPushout.equiv_symm_algebraMap_right]
    have he : (τ.app M : _ → _) = w.symm ∘ ψ ∘ u := by
      funext x
      change τ.app M x = w.symm (w (τ.app M (u.symm (u x))))
      rw [LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply]
    rw [he]
    exact w.symm.bijective.comp (hψ.comp u.bijective)
  exact NatIso.isIso_of_isIso_app τ

section TensorComparison

open CochainComplex.DerivedTensor

attribute [local instance] ModuleCat.liftedModuleMonoidalStruct
  ModuleCat.liftedModuleMonoidal ModuleCat.liftedModuleMonoidalPreadditive

/-- Whether a functor carries a given map to a quasi-isomorphism only depends on the functor up
to isomorphism. -/
private theorem quasiIso_map_iff_of_natIso
    {C D ι : Type*} [Category* C] [Category* D] [Abelian D]
    {c : ComplexShape ι} {F G : C ⥤ HomologicalComplex D c} (e : F ≅ G) {X Y : C} (f : X ⟶ Y) :
    QuasiIso (F.map f) ↔ QuasiIso (G.map f) :=
  quasiIso_iff_of_arrow_mk_iso _ _
    (Arrow.isoMk (e.app X) (e.app Y) (e.hom.naturality f).symm)

/-- Tensoring over `R` with the restriction of a complex of `A`-modules agrees with extending
scalars, tensoring over `A`, and restricting back. -/
private theorem exists_tensor_restrictScalars_iso
    {R : Type uR} {A : Type uA} [CommRing R] [CommRing A] (f : R →+* A)
    (K : CochainComplex (ModuleCat.{max v uR uA} A) ℤ) :
    letI : MonoidalCategoryStruct (ModuleCat.{max v uR uA} R) :=
      ModuleCat.liftedModuleMonoidalStruct.{uR, max v uA}
    letI : MonoidalCategory (ModuleCat.{max v uR uA} R) :=
      ModuleCat.liftedModuleMonoidal.{uR, max v uA}
    letI : MonoidalCategoryStruct (ModuleCat.{max v uR uA} A) :=
      ModuleCat.liftedModuleMonoidalStruct.{uA, max v uR}
    letI : MonoidalCategory (ModuleCat.{max v uR uA} A) :=
      ModuleCat.liftedModuleMonoidal.{uA, max v uR}
    Nonempty (TrightCochain ((CochainComplex.restrictScalarsLarge.{v, uR, uA} f).obj K) ≅
      CochainComplex.extendScalarsLarge.{v, uR, uA} f ⋙ TrightCochain K ⋙
        CochainComplex.restrictScalarsLarge.{v, uR, uA} f) := by
  let : HasDerivedCategory (ModuleCat.{max v uR uA} R) := HasDerivedCategory.standard _
  let : HasDerivedCategory (ModuleCat.{max v uR uA} A) := HasDerivedCategory.standard _
  obtain ⟨N, eu, ec, _⟩ := exists_derived_tensor_change_of_rings.{uR, uA, v} f K
  exact ⟨eu.symm ≪≫
    Functor.isoWhiskerRight ec (CochainComplex.restrictScalarsLarge.{v, uR, uA} f) ≪≫
    Functor.associator _ _ _⟩

/-- Extension of scalars carries a map to a quasi-isomorphism exactly when tensoring over `R`
with the restriction of the unit complex does. -/
private theorem quasiIso_tensor_restrictScalars_of_kFlat
    {R : Type uR} {A : Type uA} [CommRing R] [CommRing A] (f : R →+* A)
    (K : CochainComplex (ModuleCat.{max v uR uA} A) ℤ)
    (hK : CochainComplex.KFlat.{uA, max v uR} K)
    {E F : CochainComplex (ModuleCat.{max v uR uA} R) ℤ} (q : E ⟶ F)
    [QuasiIso ((CochainComplex.extendScalarsLarge.{v, uR, uA} f).map q)] :
    letI : MonoidalCategoryStruct (ModuleCat.{max v uR uA} R) :=
      ModuleCat.liftedModuleMonoidalStruct.{uR, max v uA}
    letI : MonoidalCategory (ModuleCat.{max v uR uA} R) :=
      ModuleCat.liftedModuleMonoidal.{uR, max v uA}
    letI : MonoidalCategoryStruct (ModuleCat.{max v uR uA} A) :=
      ModuleCat.liftedModuleMonoidalStruct.{uA, max v uR}
    letI : MonoidalCategory (ModuleCat.{max v uR uA} A) :=
      ModuleCat.liftedModuleMonoidal.{uA, max v uR}
    QuasiIso ((TrightCochain
      ((CochainComplex.restrictScalarsLarge.{v, uR, uA} f).obj K)).map q) := by
  obtain ⟨e⟩ := exists_tensor_restrictScalars_iso.{uR, uA, v} f K
  rw [quasiIso_map_iff_of_natIso e]
  have : QuasiIso ((TrightCochain K).map
      ((CochainComplex.extendScalarsLarge.{v, uR, uA} f).map q)) :=
    CochainComplex.DerivedTensor.quasiIso_tright_map.{uA, max v uR} K hK _
  change QuasiIso (((ModuleCat.restrictScalars f).mapHomologicalComplex
    (ComplexShape.up ℤ)).map _)
  infer_instance

/-- The two tensoring variables invert the same maps: the flip isomorphism of the total tensor
product identifies them. -/
private theorem quasiIso_tleft_map_iff_tright_map
    {R : Type uR} [CommRing R]
    (K : CochainComplex (ModuleCat.{max v uR} R) ℤ)
    {E F : CochainComplex (ModuleCat.{max v uR} R) ℤ} (q : E ⟶ F) :
    QuasiIso ((TleftCochain K).map q) ↔ QuasiIso ((TrightCochain K).map q) := by
  apply quasiIso_iff_of_arrow_mk_iso
  exact Arrow.isoMk (CochainComplex.DerivedTensor.tensorFlipIso.{uR, v} K E)
    (CochainComplex.DerivedTensor.tensorFlipIso.{uR, v} K F)
    (CochainComplex.DerivedTensor.tensorFlipIso_naturality.{uR, v} K q).symm

/-- Tensoring with a quasi-isomorphism stays a quasi-isomorphism once a K-flat resolution of one
factor is available: the interchange square reduces it to the two K-flat cases. -/
private theorem quasiIso_tleft_map_of_resolution
    {R : Type uR} [CommRing R]
    {E K P N : CochainComplex (ModuleCat.{max v uR} R) ℤ}
    (e : E ⟶ K) [QuasiIso e] (q : P ⟶ N) [QuasiIso q]
    (hE : CochainComplex.KFlat.{uR, v} E) (hP : CochainComplex.KFlat.{uR, v} P)
    [hqK : QuasiIso ((TrightCochain K).map q)] :
    QuasiIso ((TleftCochain N).map e) := by
  have hqE : QuasiIso ((TrightCochain E).map q) :=
    CochainComplex.DerivedTensor.quasiIso_tright_map.{uR, v} E hE q
  have hpE : QuasiIso ((TleftCochain P).map e) :=
    (quasiIso_tleft_map_iff_tright_map P e).2
      (CochainComplex.DerivedTensor.quasiIso_tright_map.{uR, v} P hP e)
  apply (quasiIso_iff_comp_left ((TrightCochain E).map q) _).1
  have h : (TrightCochain E).map q ≫ (TleftCochain N).map e =
      (TleftCochain P).map e ≫ (TrightCochain K).map q := by
    exact (((CategoryTheory.MonoidalCategory.curriedTensor
      (ModuleCat.{max v uR} R)).map₂CochainComplex).map q).naturality e |>.symm
  rw [h]
  exact quasiIso_comp (hφ := hpE) (hφ' := hqK) _ _

/-- Extension of scalars along `g` inverts a map exactly when tensoring over `R` with the
restriction of the tensor unit does: the unit of the monoidal structure over `B`, restricted to
`R`, computes the base change. -/
private theorem quasiIso_extendScalars_map_iff_tensor_unit
    {R : Type uR} {B : Type uB} [CommRing R] [CommRing B] (g : R →+* B)
    {E K : CochainComplex (ModuleCat.{max v uR uB} R) ℤ} (e : E ⟶ K) :
    letI : MonoidalCategoryStruct (ModuleCat.{max v uR uB} R) :=
      ModuleCat.liftedModuleMonoidalStruct.{uR, max v uB}
    letI : MonoidalCategory (ModuleCat.{max v uR uB} R) :=
      ModuleCat.liftedModuleMonoidal.{uR, max v uB}
    letI : MonoidalCategoryStruct (ModuleCat.{max v uR uB} B) :=
      ModuleCat.liftedModuleMonoidalStruct.{uB, max v uR}
    letI : MonoidalCategory (ModuleCat.{max v uR uB} B) :=
      ModuleCat.liftedModuleMonoidal.{uB, max v uR}
    QuasiIso ((CochainComplex.extendScalarsLarge.{v, uR, uB} g).map e) ↔
      QuasiIso ((TrightCochain ((CochainComplex.restrictScalarsLarge.{v, uR, uB} g).obj
        (HomologicalComplex.tensorUnit (ModuleCat.{max v uR uB} B)
          (ComplexShape.up ℤ)))).map e) := by
  let : MonoidalCategoryStruct (ModuleCat.{max v uR uB} B) :=
    ModuleCat.liftedModuleMonoidalStruct.{uB, max v uR}
  let : MonoidalCategory (ModuleCat.{max v uR uB} B) :=
    ModuleCat.liftedModuleMonoidal.{uB, max v uR}
  obtain ⟨t⟩ := exists_tensor_restrictScalars_iso.{uR, uB, v} g
    (HomologicalComplex.tensorUnit (ModuleCat.{max v uR uB} B) (ComplexShape.up ℤ))
  let t' := t ≪≫ Functor.isoWhiskerLeft (CochainComplex.extendScalarsLarge.{v, uR, uB} g)
    (Functor.isoWhiskerRight (trightCochainTensorUnitIso _)
      (CochainComplex.restrictScalarsLarge.{v, uR, uB} g) ≪≫ Functor.leftUnitor _)
  rw [quasiIso_map_iff_of_natIso t']
  exact (HomologicalComplex.quasiIso_map_iff_of_preservesHomology _
    (ModuleCat.restrictScalars g)).symm

end TensorComparison

/-- An invertibility statement about the counit of a left derived functor at a fixed object does
not depend on the chosen localizations: it transfers along the comparison equivalences. -/
private theorem isIso_leftDerivedCounit_app_of_localizations
    {C C' D D' D₀ D₀' : Type*}
    [Category* C] [Category* C'] [Category* D] [Category* D']
    [Category* D₀] [Category* D₀']
    (Q : C ⥤ D) (Q₀ : C ⥤ D₀) (T : C' ⥤ D') (T₀ : C' ⥤ D₀')
    (W : MorphismProperty C) (W' : MorphismProperty C')
    [Q.IsLocalization W] [Q₀.IsLocalization W]
    [T.IsLocalization W'] [T₀.IsLocalization W']
    (F : C ⥤ C') (L : D ⥤ D') (α : Q ⋙ L ⟶ F ⋙ T)
    [L.IsLeftDerivedFunctor α W] (K : C)
    (h : ∀ (L₀ : D₀ ⥤ D₀') (α₀ : Q₀ ⋙ L₀ ⟶ F ⋙ T₀),
      L₀.IsLeftDerivedFunctor α₀ W → IsIso (α₀.app K)) : IsIso (α.app K) := by
  let E := (Localization.uniq Q₀ Q W).functor
  let G := (Localization.uniq T T₀ W').functor
  let e := Localization.compUniqFunctor Q₀ Q W
  let t := Localization.compUniqFunctor T T₀ W'
  let β : Q ⋙ (L ⋙ G) ⟶ (F ⋙ T) ⋙ G :=
    (Functor.associator _ _ _).inv ≫ Functor.whiskerRight α G
  let d : (F ⋙ T) ⋙ G ≅ F ⋙ T₀ :=
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft F t
  let β' := β ≫ d.hom
  have hβ : (L ⋙ G).IsRightKanExtension β :=
    Functor.IsLeftDerivedFunctor.isRightKanExtension (L ⋙ G) β W
  have hβ' : (L ⋙ G).IsRightKanExtension β' :=
    (Functor.isRightKanExtension_iff_of_iso₂ β β' d (Iso.refl _) (by simp [β'])).1 hβ
  let α₀ : Q₀ ⋙ (E ⋙ L ⋙ G) ⟶ F ⋙ T₀ :=
    (Functor.associator _ _ _).inv ≫ Functor.whiskerRight e.hom (L ⋙ G) ≫ β'
  have : (E ⋙ L ⋙ G).IsLeftDerivedFunctor α₀ W :=
    ⟨(Functor.isRightKanExtension_iff_postcomp₁ E e β').1 hβ'⟩
  have h₀ := h (E ⋙ L ⋙ G) α₀ inferInstance
  have heq : α₀.app K = G.map (L.map (e.hom.app K)) ≫
      G.map (α.app K) ≫ t.hom.app (F.obj K) := by
    simp [α₀, β', β, d, Category.assoc]
  rw [heq] at h₀
  have : IsIso (G.map (α.app K)) := by
    have : IsIso (G.map (α.app K) ≫ t.hom.app (F.obj K)) :=
      IsIso.of_isIso_comp_left (G.map (L.map (e.hom.app K))) _
    exact IsIso.of_isIso_comp_right _ (t.hom.app (F.obj K))
  exact isIso_of_reflects_iso (α.app K) G

/-- The counit of any total left derived extension of scalars is invertible on a K-flat complex,
for an arbitrary choice of derived categories. -/
private theorem isIso_extendScalarsCounit_app_of_kFlat
    {R : Type uR} {A : Type uA} [CommRing R] [CommRing A]
    [HasDerivedCategory (ModuleCat.{max v uR uA} R)]
    [HasDerivedCategory (ModuleCat.{max v uR uA} A)] (f : R →+* A)
    (L : DerivedCategory (ModuleCat.{max v uR uA} R) ⥤
      DerivedCategory (ModuleCat.{max v uR uA} A))
    (α : DerivedCategory.Q ⋙ L ⟶
      CochainComplex.extendScalarsLarge.{v, uR, uA} f ⋙ DerivedCategory.Q)
    [L.IsLeftDerivedFunctor α
      (HomologicalComplex.quasiIso (ModuleCat.{max v uR uA} R) (ComplexShape.up ℤ))]
    (K : CochainComplex (ModuleCat.{max v uR uA} R) ℤ)
    (hK : CochainComplex.KFlat.{uR, max v uA} K) : IsIso (α.app K) := by
  let Q₀ := @DerivedCategory.Q (ModuleCat.{max v uR uA} R) _ _
    (HasDerivedCategory.standard _)
  let T₀ := @DerivedCategory.Q (ModuleCat.{max v uR uA} A) _ _
    (HasDerivedCategory.standard _)
  apply isIso_leftDerivedCounit_app_of_localizations DerivedCategory.Q Q₀
    DerivedCategory.Q T₀
    (HomologicalComplex.quasiIso _ (ComplexShape.up ℤ))
    (HomologicalComplex.quasiIso _ (ComplexShape.up ℤ))
    (CochainComplex.extendScalarsLarge.{v, uR, uA} f) L α K
  intro L₀ α₀ h₀
  have := h₀
  let : HasDerivedCategory (ModuleCat.{max v uR uA} R) := HasDerivedCategory.standard _
  let : HasDerivedCategory (ModuleCat.{max v uR uA} A) := HasDerivedCategory.standard _
  exact CochainComplex.DerivedTensor.KFlatDerived.isIso_extensionCounit_app_of_kFlat.{uR, uA, v}
    f L₀ α₀ K hK

/-- An additive functor carries the extension of a quasi-isomorphism along an embedding of
shapes to a quasi-isomorphism, whenever it does so for the original map. -/
private theorem quasiIso_map_extendMap
    {C D ι ι' : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
    (F : C ⥤ D) [F.Additive] {c : ComplexShape ι} {c' : ComplexShape ι'}
    (e : c.Embedding c') [e.IsRelIff]
    {K L : HomologicalComplex C c} (f : K ⟶ L)
    [QuasiIso ((F.mapHomologicalComplex c).map f)] :
    QuasiIso ((F.mapHomologicalComplex c').map (HomologicalComplex.extendMap f e)) := by
  apply (quasiIso_iff_of_arrow_mk_iso _ _
    (Arrow.isoMk (HomologicalComplex.mapHomologicalComplexExtendIso F K e).symm
      (HomologicalComplex.mapHomologicalComplexExtendIso F L e).symm
      (HomologicalComplex.mapHomologicalComplexExtendIso_inv_naturality F K f e).symm)).2
  exact (HomologicalComplex.quasiIso_extendMap_iff _ _).2 inferInstance

section LiftedTensor

attribute [local instance] RingHomInvPair.of_ringEquiv RingHomInvPair.of_ringEquiv_symm

/-- Restricting along a ring isomorphism and then lifting the module universe is compatible with
tensor products. -/
private def uliftRestrictTensorEquiv
    {R S : Type*} [CommRing R] [CommRing S] (e : R ≃+* S)
    (X Y : ModuleCat.{v} S) :
    let J := ModuleCat.restrictScalars.{v} e.toRingHom ⋙ ModuleCat.uliftFunctor.{uA} R
    (J.obj X) ⊗[R] (J.obj Y) ≃ₗ[R] J.obj (ModuleCat.of S (X ⊗[S] Y)) := by
  let J := ModuleCat.restrictScalars.{v} e.toRingHom ⋙ ModuleCat.uliftFunctor.{uA} R
  have : RingHomInvPair e.toRingHom e.symm.toRingHom := RingHomInvPair.of_ringEquiv e
  have : RingHomInvPair e.symm.toRingHom e.toRingHom := RingHomInvPair.of_ringEquiv_symm e
  let ex : LinearEquiv (σ' := e.symm.toRingHom) e.toRingHom (J.obj X) X :=
    { toFun := ULift.down
      invFun := ULift.up
      left_inv _ := rfl
      right_inv _ := rfl
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  let ey : LinearEquiv (σ' := e.symm.toRingHom) e.toRingHom (J.obj Y) Y :=
    { toFun := ULift.down
      invFun := ULift.up
      left_inv _ := rfl
      right_inv _ := rfl
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  let t := TensorProduct.congr ex ey
  let u : (X ⊗[S] Y) ≃+ ULift.{uA} (X ⊗[S] Y) :=
    { toFun := ULift.up
      invFun := ULift.down
      left_inv _ := rfl
      right_inv _ := rfl
      map_add' _ _ := rfl }
  exact
    { __ := t.toAddEquiv.trans u
      map_smul' := fun r x => by
        change ULift.up (t (r • x)) = ULift.up (e r • t x)
        rw [t.map_smulₛₗ]
        rfl }

set_option backward.isDefEq.respectTransparency false in
-- The naturality square is checked on pure tensors, where both sides reduce to the same
-- element only after the universe lift and the two scalar restrictions are unfolded; the
-- resulting goal is then closed by two `change`s, which the flexible linter does not allow
-- after a `simp` that performs that unfolding.
set_option linter.flexible false in
/-- Lifting the ring and its modules to a common universe identifies extension of scalars
followed by restriction with tensoring with the lifted algebra. -/
private def extendScalarsRestrictUliftIso
    {R : Type uR} {A : Type uA} [CommRing R] [CommRing A] [Algebra R A] :
    let R₀ := ULift.{max uR uA uB} R
    let A₀ := ULift.{max uR uA uB} A
    letI : Algebra R₀ A₀ := ULift.algebra' R A₀
    let J := ModuleCat.restrictScalars.{max uR uA uB}
        (ULift.ringEquiv.symm : R ≃+* R₀).toRingHom ⋙ ModuleCat.uliftFunctor.{v} R
    J ⋙ ModuleCat.extendScalars.{uR, uA, max v uR uA uB} (algebraMap R A) ⋙
        ModuleCat.restrictScalars (algebraMap R A) ≅
      ((CategoryTheory.MonoidalCategory.tensoringLeft (ModuleCat.{max uR uA uB} R₀)).obj
        (ModuleCat.of R₀ A₀)) ⋙ J := by
  intro R₀ A₀ J
  let e := (ULift.ringEquiv.symm : R ≃+* R₀)
  let a : (ModuleCat.restrictScalars (algebraMap R A)).obj (ModuleCat.of A A) ≃ₗ[R]
      J.obj (ModuleCat.of R₀ A₀) :=
    { toFun := fun x => ULift.up (ULift.up x)
      invFun := fun x => x.down.down
      left_inv _ := rfl
      right_inv _ := rfl
      map_add' _ _ := rfl
      map_smul' := fun r x =>
        congrArg (fun z : A => ULift.up (ULift.up z))
          (Algebra.smul_def (R := R) (A := A) r x).symm }
  refine NatIso.ofComponents (fun M => ?_) ?_
  · apply LinearEquiv.toModuleIso
    exact TensorProduct.congr a (LinearEquiv.refl R (J.obj M)) ≪≫ₗ
      uliftRestrictTensorEquiv e (ModuleCat.of R₀ A₀) M
  · intro M N f
    ext : 1
    apply TensorProduct.ext'
    intro x m
    change (uliftRestrictTensorEquiv e (ModuleCat.of R₀ A₀) N)
        ((TensorProduct.congr a (LinearEquiv.refl R (J.obj N)))
          (((ModuleCat.extendScalars.{uR, uA, max v uR uA uB} (algebraMap R A)).map
            (J.map f)) (x ⊗ₜ[R,algebraMap R A] m))) = _
    rw [ModuleCat.ExtendScalars.map_tmul, TensorProduct.congr_tmul]
    change ULift.up ((ULift.up x : A₀) ⊗ₜ[R₀] f m.down) =
      J.map (((CategoryTheory.MonoidalCategory.tensoringLeft
        (ModuleCat.{max uR uA uB} R₀)).obj (ModuleCat.of R₀ A₀)).map f)
        ((uliftRestrictTensorEquiv e (ModuleCat.of R₀ A₀) M)
          ((TensorProduct.congr a (LinearEquiv.refl R (J.obj M))) (x ⊗ₜ[R] m)))
    simp [uliftRestrictTensorEquiv, TensorProduct.map_tmul, J, e, a,
      ModuleCat.uliftFunctor]
    change (ULift.up x : A₀) ⊗ₜ[R₀] f m.down =
      (f.hom.lTensor A₀) ((ULift.up x : A₀) ⊗ₜ[R₀] m.down)
    rw [LinearMap.lTensor_tmul]

/-- Under Tor independence, extension of scalars along `R → A` carries the universe-lifted
projective resolution of `B` to a quasi-isomorphism. -/
private theorem quasiIso_extendScalars_map_lifted_resolution
    {R : Type uR} {A : Type uA} {B : Type uB}
    [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    (hTor : TorIndependent R A B) :
    let R₀ := ULift.{max uR uA uB} R
    let A₀ := ULift.{max uR uA uB} A
    let B₀ := ULift.{max uR uA uB} B
    letI : Algebra R₀ A₀ := ULift.algebra' R A₀
    letI : Algebra R₀ B₀ := ULift.algebra' R B₀
    let J := ModuleCat.restrictScalars.{max uR uA uB}
        (ULift.ringEquiv.symm : R ≃+* R₀).toRingHom ⋙ ModuleCat.uliftFunctor.{v} R
    ∀ P : ProjectiveResolution (ModuleCat.of R₀ B₀),
      QuasiIso (((ModuleCat.extendScalars.{uR, uA, max v uR uA uB}
        (algebraMap R A)).mapHomologicalComplex (ComplexShape.down ℕ)).map
          ((J.mapHomologicalComplex (ComplexShape.down ℕ)).map P.π)) := by
  intro R₀ A₀ B₀ J P
  let : Algebra R₀ A₀ := ULift.algebra' R A₀
  let : Algebra R₀ B₀ := ULift.algebra' R B₀
  let T := (CategoryTheory.MonoidalCategory.tensoringLeft
    (ModuleCat.{max uR uA uB} R₀)).obj (ModuleCat.of R₀ A₀)
  have ht : QuasiIso ((T.mapHomologicalComplex (ComplexShape.down ℕ)).map P.π) :=
    quasiIso_tensor_map_projectiveResolution_of_isZero_Tor _ _ P hTor
  have hj : QuasiIso ((J.mapHomologicalComplex (ComplexShape.down ℕ)).map
      ((T.mapHomologicalComplex (ComplexShape.down ℕ)).map P.π)) := inferInstance
  have he := quasiIso_map_iff_of_natIso
    (NatIso.mapHomologicalComplex (extendScalarsRestrictUliftIso.{uR, uA, uB, v}
      (R := R) (A := A)) (ComplexShape.down ℕ)) P.π
  have hx := he.2 hj
  exact (HomologicalComplex.quasiIso_map_iff_of_preservesHomology _
    (ModuleCat.restrictScalars (algebraMap R A))).1 hx

end LiftedTensor

section UnitResolution

open CochainComplex.DerivedTensor CochainComplex.KFlat

attribute [local instance] ModuleCat.liftedModuleMonoidalStruct
  ModuleCat.liftedModuleMonoidal ModuleCat.liftedModuleMonoidalPreadditive

/-- Under Tor independence, the restriction to an `R`-complex of the tensor unit over `B` admits
a K-flat resolution which extension of scalars along `R → A` carries to a
quasi-isomorphism. -/
private theorem exists_kFlat_resolution_tensor_unit_of_torIndependent
    {R : Type uR} {A : Type uA} {B : Type uB}
    [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    (hTor : TorIndependent R A B) :
    letI : MonoidalCategoryStruct (ModuleCat.{max v uR uA uB} B) :=
      ModuleCat.liftedModuleMonoidalStruct.{uB, max v uR uA}
    letI : MonoidalCategory (ModuleCat.{max v uR uA uB} B) :=
      ModuleCat.liftedModuleMonoidal.{uB, max v uR uA}
    let N := (CochainComplex.restrictScalarsLarge.{max v uA, uR, uB} (algebraMap R B)).obj
      (HomologicalComplex.tensorUnit (ModuleCat.{max v uR uA uB} B) (ComplexShape.up ℤ))
    ∃ (P : CochainComplex (ModuleCat.{max v uR uA uB} R) ℤ) (q : P ⟶ N),
      CochainComplex.KFlat.{uR, max v uA uB} P ∧ QuasiIso q ∧
        QuasiIso ((CochainComplex.extendScalarsLarge.{max v uB, uR, uA}
          (algebraMap R A)).map q) := by
  let : MonoidalCategoryStruct (ModuleCat.{max v uR uA uB} B) :=
    ModuleCat.liftedModuleMonoidalStruct.{uB, max v uR uA}
  let : MonoidalCategory (ModuleCat.{max v uR uA uB} B) :=
    ModuleCat.liftedModuleMonoidal.{uB, max v uR uA}
  let R₀ := ULift.{max uR uA uB} R
  let A₀ := ULift.{max uR uA uB} A
  let B₀ := ULift.{max uR uA uB} B
  let : Algebra R₀ A₀ := ULift.algebra' R A₀
  let : Algebra R₀ B₀ := ULift.algebra' R B₀
  let J := ModuleCat.restrictScalars.{max uR uA uB}
      (ULift.ringEquiv.symm : R ≃+* R₀).toRingHom ⋙ ModuleCat.uliftFunctor.{v} R
  let P₀ := projectiveResolution (ModuleCat.of R₀ B₀)
  let P : ProjectiveResolution (J.obj (ModuleCat.of R₀ B₀)) :=
    { complex := (J.mapHomologicalComplex (ComplexShape.down ℕ)).obj P₀.complex
      projective n := J.projective_obj_of_projective (P₀.projective n)
      π := (J.mapHomologicalComplex (ComplexShape.down ℕ)).map P₀.π ≫
        (HomologicalComplex.singleMapHomologicalComplex J (ComplexShape.down ℕ) 0).hom.app _
      quasiIso := inferInstance }
  let Ext := ModuleCat.extendScalars.{uR, uA, max v uR uA uB} (algebraMap R A)
  have h₀ : QuasiIso ((Ext.mapHomologicalComplex (ComplexShape.down ℕ)).map
      ((J.mapHomologicalComplex (ComplexShape.down ℕ)).map P₀.π)) :=
    quasiIso_extendScalars_map_lifted_resolution.{uR, uA, uB, v} hTor P₀
  have hπ : QuasiIso ((Ext.mapHomologicalComplex (ComplexShape.down ℕ)).map P.π) := by
    dsimp only [P]
    rw [Functor.map_comp]
    infer_instance
  let q₀ := HomologicalComplex.extendMap P.π ComplexShape.embeddingDownNat ≫
    (HomologicalComplex.extendSingleIso ComplexShape.embeddingDownNat
      (J.obj (ModuleCat.of R₀ B₀)) 0 0 (by simp)).hom
  have hq₀ : QuasiIso q₀ := by
    have : QuasiIso (HomologicalComplex.extendMap P.π ComplexShape.embeddingDownNat) :=
      (HomologicalComplex.quasiIso_extendMap_iff _ _).2 P.quasiIso
    exact quasiIso_comp _ _
  have hExtq₀ : QuasiIso ((Ext.mapHomologicalComplex (ComplexShape.up ℤ)).map q₀) := by
    have : QuasiIso ((Ext.mapHomologicalComplex (ComplexShape.up ℤ)).map
        (HomologicalComplex.extendMap P.π ComplexShape.embeddingDownNat)) :=
      quasiIso_map_extendMap Ext ComplexShape.embeddingDownNat P.π
    dsimp only [q₀]
    rw [Functor.map_comp]
    infer_instance
  let : Module R (ULift.{max v uR uA} B) :=
    Module.compHom (ULift.{max v uR uA} B) (algebraMap R B)
  let b : J.obj (ModuleCat.of R₀ B₀) ≅
      (ModuleCat.restrictScalars (algebraMap R B)).obj
        (CategoryTheory.MonoidalCategory.tensorUnit (ModuleCat.{max v uR uA uB} B)) := by
    change J.obj (ModuleCat.of R₀ B₀) ≅
      (ModuleCat.restrictScalars (algebraMap R B)).obj
        (ModuleCat.of B (ULift.{max v uR uA} B))
    apply LinearEquiv.toModuleIso
    exact
      { toFun := fun x => ULift.up x.down.down
        invFun := fun x => ULift.up (ULift.up x.down)
        left_inv _ := rfl
        right_inv _ := rfl
        map_add' _ _ := rfl
        map_smul' := fun r x => congrArg ULift.up
          (Algebra.smul_def (R := R) (A := B) r x.down.down) }
  let t := (HomologicalComplex.single (ModuleCat.{max v uR uA uB} R)
      (ComplexShape.up ℤ) 0).mapIso b ≪≫
    ((HomologicalComplex.singleMapHomologicalComplex
      (ModuleCat.restrictScalars (algebraMap R B)) (ComplexShape.up ℤ) 0).app
        (CategoryTheory.MonoidalCategory.tensorUnit (ModuleCat.{max v uR uA uB} B))).symm
  refine ⟨P.complex.extend ComplexShape.embeddingDownNat, q₀ ≫ t.hom, ?_, ?_, ?_⟩
  · have : ∀ n, Module.Flat R ((P.complex.extend ComplexShape.embeddingDownNat).X n) := by
      intro n
      have hp : Projective ((P.complex.extend ComplexShape.embeddingDownNat).X n) := by
        by_cases hn : ∃ m, ComplexShape.embeddingDownNat.f m = n
        · obtain ⟨m, hm⟩ := hn
          exact Projective.of_iso
            (P.complex.extendXIso ComplexShape.embeddingDownNat hm).symm (P.projective m)
        · exact (P.complex.isZero_extend_X ComplexShape.embeddingDownNat n
            (by simpa using hn)).projective
      have : Module.Projective R ((P.complex.extend ComplexShape.embeddingDownNat).X n) :=
        ModuleCat.projective_of_module_projective _
      exact Module.Flat.of_projective
    exact kFlat_of_flat _ 0
  · exact quasiIso_comp (hφ := hq₀) (hφ' := quasiIso_of_isIso t.hom) _ _
  · change QuasiIso ((Ext.mapHomologicalComplex (ComplexShape.up ℤ)).map (q₀ ≫ t.hom))
    rw [Functor.map_comp]
    infer_instance

/-- Under Tor independence, extension of scalars along `R → B` carries a quasi-isomorphism from a
K-flat `R`-complex to the restriction of a K-flat `A`-complex to a quasi-isomorphism. -/
private theorem quasiIso_extendScalars_map_of_torIndependent
    {R : Type uR} {A : Type uA} {B : Type uB}
    [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    (hTor : TorIndependent R A B)
    (K : CochainComplex (ModuleCat.{max v uR uA uB} A) ℤ)
    (hK : CochainComplex.KFlat.{uA, max v uR uB} K)
    {E : CochainComplex (ModuleCat.{max v uR uA uB} R) ℤ}
    (hE : CochainComplex.KFlat.{uR, max v uA uB} E)
    (e : E ⟶ (CochainComplex.restrictScalarsLarge.{max v uB, uR, uA} (algebraMap R A)).obj K)
    [QuasiIso e] :
    QuasiIso ((CochainComplex.extendScalarsLarge.{max v uA, uR, uB} (algebraMap R B)).map e) := by
  obtain ⟨P, q, hP, hq, hfq⟩ :=
    exists_kFlat_resolution_tensor_unit_of_torIndependent.{uR, uA, uB, v} hTor
  have := hq
  have := hfq
  have : QuasiIso ((TrightCochain
      ((CochainComplex.restrictScalarsLarge.{max v uB, uR, uA} (algebraMap R A)).obj K)).map q) :=
    quasiIso_tensor_restrictScalars_of_kFlat.{uR, uA, max v uB}
      (algebraMap R A) K hK q
  apply (quasiIso_extendScalars_map_iff_tensor_unit.{uR, uB, max v uA}
    (algebraMap R B) e).2
  apply (quasiIso_tleft_map_iff_tright_map _ e).1
  exact quasiIso_tleft_map_of_resolution e q hE hP

/-- Under Tor independence, the counit of derived extension of scalars along `R → B` is
invertible at the restriction of any K-flat complex of `A`-modules. -/
private theorem isIso_extendScalarsCounit_app_restrict_of_torIndependent
    {R : Type uR} {A : Type uA} {B : Type uB}
    [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    [HasDerivedCategory (ModuleCat.{max v uR uA uB} R)]
    [HasDerivedCategory (ModuleCat.{max v uR uA uB} B)]
    (hTor : TorIndependent R A B)
    (L : DerivedCategory (ModuleCat.{max v uR uA uB} R) ⥤
      DerivedCategory (ModuleCat.{max v uR uA uB} B))
    (α : DerivedCategory.Q ⋙ L ⟶
      CochainComplex.extendScalarsLarge.{max v uA, uR, uB} (algebraMap R B) ⋙ DerivedCategory.Q)
    [L.IsLeftDerivedFunctor α
      (HomologicalComplex.quasiIso (ModuleCat.{max v uR uA uB} R) (ComplexShape.up ℤ))]
    (K : CochainComplex (ModuleCat.{max v uR uA uB} A) ℤ)
    (hK : CochainComplex.KFlat.{uA, max v uR uB} K) :
    IsIso (α.app ((CochainComplex.restrictScalarsLarge.{max v uB, uR, uA}
      (algebraMap R A)).obj K)) := by
  obtain ⟨E, e, hE, _, he, _⟩ := exists_kFlat_resolution.{uR, max v uA uB}
    ((CochainComplex.restrictScalarsLarge.{max v uB, uR, uA} (algebraMap R A)).obj K)
  have := he
  have : QuasiIso ((CochainComplex.extendScalarsLarge.{max v uA, uR, uB}
      (algebraMap R B)).map e) :=
    quasiIso_extendScalars_map_of_torIndependent.{uR, uA, uB, v} hTor K hK hE e
  have : IsIso (α.app E) :=
    isIso_extendScalarsCounit_app_of_kFlat.{uR, uB, max v uA} (algebraMap R B) L α E hE
  have : IsIso ((DerivedCategory.Q ⋙ L).map e) := by
    dsimp only [Functor.comp_map]
    infer_instance
  have hnat := α.naturality e
  have : IsIso ((DerivedCategory.Q ⋙ L).map e ≫ α.app _) := by
    rw [hnat]
    dsimp only [Functor.comp_map]
    infer_instance
  exact IsIso.of_isIso_comp_left ((DerivedCategory.Q ⋙ L).map e) _

/-- A morphism whose composite with an isomorphism is an isomorphism is itself one. -/
private theorem isIso_of_comp_eq
    {C : Type*} [Category* C] {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (h : X ⟶ Z)
    [IsIso g] [IsIso h] (heq : f ≫ g = h) : IsIso f := by
  have : IsIso (f ≫ g) := heq.symm ▸ inferInstance
  exact IsIso.of_isIso_comp_right f g


end UnitResolution

section Main

open CochainComplex.KFlat

set_option backward.isDefEq.respectTransparency false in
/-- **Stacks 0661.** If `A` and `R'` are Tor independent over `R`, then the canonical comparison
from derived base change over `R` to derived base change over `A` is an isomorphism, for every
pushout square with upper-right corner `A'`. -/
@[stacks 0661]
public theorem derivedBaseChangeComparison_isIso_of_torIndependent
    {R : Type uR} {A : Type uA} {R' : Type uRp} {A' : Type uAp}
    [CommRing R] [CommRing A] [CommRing R'] [CommRing A']
    [Algebra R A] [Algebra R R'] [Algebra R A'] [Algebra A A'] [Algebra R' A']
    [IsScalarTower R A A'] [IsScalarTower R R' A'] [Algebra.IsPushout R A R' A']
    [HasDerivedCategory (ModuleCat.{max v uR uA uRp uAp} R)]
    [HasDerivedCategory (ModuleCat.{max v uR uA uRp uAp} A)]
    [HasDerivedCategory (ModuleCat.{max v uR uA uRp uAp} R')]
    [HasDerivedCategory (ModuleCat.{max v uR uA uRp uAp} A')]
    (hTor : TorIndependent R A R') :
    let f : R →+* A := algebraMap R A
    let g : R →+* R' := algebraMap R R'
    let h : A →+* A' := algebraMap A A'
    let i : R' →+* A' := algebraMap R' A'
    let sq : h.comp f = i.comp g := by
      exact (IsScalarTower.algebraMap_eq R A A').symm.trans
        (IsScalarTower.algebraMap_eq R R' A')
    let Ext_g := ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp uAp} g
    let Ext_h := ModuleCat.extendScalars.{uA, uAp, max v uR uA uRp uAp} h
    letI : Ext_g.IsLeftAdjoint :=
      (ModuleCat.extendRestrictScalarsAdj.{max v uR uA uRp uAp, uR, uRp}
        g).isLeftAdjoint
    letI : Ext_h.IsLeftAdjoint :=
      (ModuleCat.extendRestrictScalarsAdj.{max v uR uA uRp uAp, uA, uAp}
        h).isLeftAdjoint
    let U_g := Ext_g.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
      DerivedCategory.Q (C := ModuleCat.{max v uR uA uRp uAp} R')
    let U_h := Ext_h.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
      DerivedCategory.Q (C := ModuleCat.{max v uR uA uRp uAp} A')
    ∀ (L_g : DerivedCategory (ModuleCat.{max v uR uA uRp uAp} R) ⥤
          DerivedCategory (ModuleCat.{max v uR uA uRp uAp} R'))
      (L_h : DerivedCategory (ModuleCat.{max v uR uA uRp uAp} A) ⥤
          DerivedCategory (ModuleCat.{max v uR uA uRp uAp} A'))
      (alpha_g : DerivedCategory.Q (C := ModuleCat.{max v uR uA uRp uAp} R) ⋙ L_g ⟶ U_g)
      (alpha_h : DerivedCategory.Q (C := ModuleCat.{max v uR uA uRp uAp} A) ⋙ L_h ⟶ U_h),
      [L_g.IsLeftDerivedFunctor alpha_g
        (HomologicalComplex.quasiIso (ModuleCat.{max v uR uA uRp uAp} R)
          (ComplexShape.up ℤ))] →
      [L_h.IsLeftDerivedFunctor alpha_h
        (HomologicalComplex.quasiIso (ModuleCat.{max v uR uA uRp uAp} A)
          (ComplexShape.up ℤ))] →
      let comparison := derivedBaseChangeComparison f g h i sq
        L_g L_h alpha_g alpha_h
      IsIso comparison.2.1 := by
  dsimp only
  intro L_g L_h alpha_g alpha_h h_g h_h
  have := h_g
  have := h_h
  let f := algebraMap R A
  let g := algebraMap R R'
  let h := algebraMap A A'
  let i := algebraMap R' A'
  let sq : h.comp f = i.comp g :=
    (IsScalarTower.algebraMap_eq R A A').symm.trans (IsScalarTower.algebraMap_eq R R' A')
  change IsIso (derivedBaseChangeComparison f g h i sq
    L_g L_h alpha_g alpha_h).2.1
  generalize hc_eq : derivedBaseChangeComparison f g h i sq
    L_g L_h alpha_g alpha_h = c
  have hc : IsIso c.1 := isIso_baseChange_of_isPushout c.1 c.2.2.1
  refine isIso_of_isIso_app_of_left_resolutions DerivedCategory.Q
    (HomologicalComplex.quasiIso (ModuleCat.{max v uR uA uRp uAp} A) (ComplexShape.up ℤ))
    (fun K => CochainComplex.KFlat.{uA, max v uR uRp uAp} K) ?_ c.2.1 ?_
  · intro X
    obtain ⟨Y, p, hY, _, hp, _⟩ :=
      exists_kFlat_resolution.{uA, max v uR uRp uAp} X
    exact ⟨Y, hY, p, hp⟩
  · intro K hK
    have hh : IsIso (alpha_h.app K) :=
      isIso_extendScalarsCounit_app_of_kFlat.{uA, uAp, max v uR uRp}
        h L_h alpha_h K hK
    have hg : IsIso (alpha_g.app
        ((CochainComplex.restrictScalarsLarge.{max v uRp uAp, uR, uA} f).obj K)) :=
      isIso_extendScalarsCounit_app_restrict_of_torIndependent.{uR, uA, uRp, max v uAp}
        hTor L_g alpha_g K hK
    change IsIso (alpha_g.app
      (((ModuleCat.restrictScalars f).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)) at hg
    have ht : IsIso ((NatTrans.mapHomologicalComplex c.1 (ComplexShape.up ℤ)).app K) := by
      change IsIso ((NatIso.mapHomologicalComplex (asIso c.1) (ComplexShape.up ℤ)).hom.app K)
      infer_instance
    have hfac := congr_app c.2.2.2 K
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.associator_hom_app, Functor.associator_inv_app,
      Category.id_comp, Category.assoc] at hfac
    exact IsIso.of_isIso_fac_right hfac

end Main

end RingTheory.TorIndependence

end
