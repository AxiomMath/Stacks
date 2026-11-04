module

public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import Mathlib.RingTheory.Polynomial.Basic
public import StacksFrontier.Homology.KFlat.BaseChange
public import StacksFrontier.Homology.KFlat.Resolution
public import StacksFrontier.Homology.TorAmplitude.Defs

@[expose] public section

/-!
# Derived tensor product along evaluation of a polynomial ring at zero

Let `R[x] → R` be evaluation at zero. An object `K` of `D(R)`, regarded as an object of `D(R[x])`
through that map, has derived tensor product with `R` isomorphic, in `D(R)`, to the biproduct of
`K` and its shift by one. So `R` is a retract of its own base change along `R[x] → R`, up to the
shift, and nothing is lost by adjoining a variable and evaluating it at zero.

## Main definitions

* `PseudoCoherence.DerivedTensoringDatum`, `PseudoCoherence.KFlatDerivedTensoringDatum`: the
  data of a derived tensor product on `D(R)`, as the lemma's hypothesis.

## Main results

* `PseudoCoherence.derivedTensorPolynomialEvalZeroIso` (Stacks 065F).

## Implementation notes

Mathlib does not package the derived tensor product on `D(R)`, so it is a hypothesis: a
bifunctor together with the comparison maps to termwise tensor product and the universal
property making each `- ⊗ᴸ M[0]` the total left derived functor of `- ⊗ M`. Those data pin the
bifunctor down as *the* derived tensor product, and the K-flat computation rule is what lets it
be evaluated on a resolution. The statement quantifies over every such datum, so a caller
holding any construction of the derived tensor product can apply it.

The argument is the short exact sequence `0 → R[x] --·x--> R[x] → R → 0` of `R[x]`-modules,
tensored with a K-flat resolution of `K` extended along `R → R[x]`. Multiplication by `x`
becomes zero after tensoring with `R`, so the resulting distinguished triangle splits, and
tag 06Y1 supplies K-flatness of the extended resolution while 06Y4 supplies the resolution.

Tags 06Y1 and 06Y4 belong to Chapter 15 sections 59 and 60, and 0652 to section 66; their
providers are `StacksFrontier/Homology/KFlat/{BaseChange,Resolution}.lean` and
`StacksFrontier/Homology/TorAmplitude/Defs.lean`, which this module cites rather than restating.

## References

* [The Stacks Project, Lemma 15.82.1 (065F)](https://stacks.math.columbia.edu/tag/065F)
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.Pretriangulated
open StacksDraft.TorAmplitude
open scoped TensorProduct ChangeOfRings

namespace PseudoCoherence

attribute [local instance] HasDerivedCategory.standard

section Datum

universe u v

/-- The functor from complexes to the derived category obtained by tensoring each term on the
right with `M` and then localizing at quasi-isomorphisms. -/
public noncomputable abbrev tensorRightComplexToDerived {R : Type u} [CommRing R]
    (M : ModuleCat.{v} R) :
    CochainComplex (ModuleCat.{v} R) ℤ ⥤ DerivedCategory (ModuleCat.{v} R) :=
  (tensorModuleRight M).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
    DerivedCategory.Q

/-- A derived tensor product on `D(R)`: a bifunctor whose restriction to a module in degree zero
is the total left derived functor of termwise tensor product, together with the comparison
morphisms that identify it as such, and the shift and triangulated structures on those
restrictions. -/
public structure DerivedTensoringDatum (R : Type u) [CommRing R] where
  /-- The bifunctor `(K, L) ↦ K ⊗ᴸ[R] L`. -/
  tensor :
    DerivedCategory (ModuleCat.{v} R) ⥤
      DerivedCategory (ModuleCat.{v} R) ⥤ DerivedCategory (ModuleCat.{v} R)
  /-- The comparison from tensoring after localization to termwise tensor product followed by
  localization. -/
  comparison : ∀ M : ModuleCat.{v} R,
    DerivedCategory.Q ⋙
        tensor.flip.obj ((DerivedCategory.singleFunctor (ModuleCat.{v} R) 0).obj M) ⟶
      tensorRightComplexToDerived M
  /-- Tensoring with `M[0]`, together with `comparison M`, is the total left derived functor of
  termwise tensoring with `M`. -/
  isLeftDerived : ∀ M : ModuleCat.{v} R,
    (tensor.flip.obj
      ((DerivedCategory.singleFunctor (ModuleCat.{v} R) 0).obj M)).IsLeftDerivedFunctor
      (comparison M) (HomologicalComplex.quasiIso _ (ComplexShape.up ℤ))
  /-- Tensoring on the right with a module in degree zero commutes with shifts. -/
  commShift : ∀ M : ModuleCat.{v} R,
    (tensor.flip.obj
      ((DerivedCategory.singleFunctor (ModuleCat.{v} R) 0).obj M)).CommShift ℤ
  /-- Tensoring on the right with a module in degree zero preserves distinguished triangles. -/
  triangulated : ∀ M : ModuleCat.{v} R, letI := commShift M;
    (tensor.flip.obj
      ((DerivedCategory.singleFunctor (ModuleCat.{v} R) 0).obj M)).IsTriangulated

/-- A derived tensor product for which the comparison with termwise tensor product is an
isomorphism on K-flat complexes; this is the computation rule that lets it be evaluated on a
K-flat resolution. -/
public structure KFlatDerivedTensoringDatum (R : Type u) [CommRing R]
    extends DerivedTensoringDatum.{u, max u v} R where
  /-- On a K-flat complex, the comparison with ordinary tensor product is an isomorphism. -/
  comparison_isIso_of_kFlat : ∀ (M : ModuleCat.{max u v} R)
      (P : CochainComplex (ModuleCat.{max u v} R) ℤ), P.KFlat →
        IsIso ((comparison M).app P)

end Datum

noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u

variable {R : Type u} [CommRing R]

private abbrev ev : Polynomial R →+* R := Polynomial.eval₂RingHom (RingHom.id R) 0
private abbrev extend : ModuleCat.{u} R ⥤ ModuleCat.{u} (Polynomial R) :=
  ModuleCat.extendScalars Polynomial.C
private abbrev restrict : ModuleCat.{u} R ⥤ ModuleCat.{u} (Polynomial R) :=
  ModuleCat.restrictScalars ev

private def restrictEvalIso :
    restrict (R := R) ⋙ ModuleCat.restrictScalars Polynomial.C ≅ 𝟭 (ModuleCat.{u} R) :=
  (ModuleCat.restrictScalarsComp' Polynomial.C ev (RingHom.id R)
    (by ext r; simp [ev])).symm ≪≫ ModuleCat.restrictScalarsId R

private def mulX : extend (R := R) ⟶ extend where
  app M := (Polynomial.X : Polynomial R) • 𝟙 (extend.obj M)
  naturality M N f := by
    simp only [Linear.comp_smul, Linear.smul_comp, Category.comp_id, Category.id_comp]

private def augmentationMap (M : ModuleCat.{u} R) : extend.obj M ⟶ restrict.obj M :=
  ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars Polynomial.C
    (restrictEvalIso.inv.app M)

private lemma augmentationMap_tmul (M : ModuleCat.{u} R) (p : Polynomial R) (m : M) :
    (augmentationMap M) (p ⊗ₜ[R, Polynomial.C] m) = p.coeff 0 • m := by
  simp [augmentationMap, ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars,
    ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.evalAt, restrictEvalIso,
    ModuleCat.restrictScalars.smul_def, ev, Polynomial.eval₂_at_zero]

private def augmentation : extend (R := R) ⟶ restrict where
  app := augmentationMap
  naturality M N f := by
    apply ModuleCat.ExtendScalars.hom_ext
    intro m
    change augmentationMap N ((extend.map f) ((1 : Polynomial R) ⊗ₜ[R, Polynomial.C] m)) =
      f (augmentationMap M ((1 : Polynomial R) ⊗ₜ[R, Polynomial.C] m))
    rw [ModuleCat.ExtendScalars.map_tmul, augmentationMap_tmul, augmentationMap_tmul]
    simp

private lemma augmentation_tmul (M : ModuleCat.{u} R) (p : Polynomial R) (m : M) :
    (augmentation.app M) (p ⊗ₜ[R, Polynomial.C] m) = p.coeff 0 • m := augmentationMap_tmul M p m

private lemma mulX_tmul (M : ModuleCat.{u} R) (p : Polynomial R) (m : M) :
    (mulX.app M) (p ⊗ₜ[R, Polynomial.C] m) = (Polynomial.X * p) ⊗ₜ[R, Polynomial.C] m := by
  change (Polynomial.X : Polynomial R) • (p ⊗ₜ[R, Polynomial.C] m) = _
  exact ModuleCat.ExtendScalars.smul_tmul Polynomial.C Polynomial.X p m

private lemma mulX_augmentation (M : ModuleCat.{u} R) :
    mulX.app M ≫ augmentation.app M = 0 := by
  apply ModuleCat.ExtendScalars.hom_ext
  intro m
  change augmentation.app M (mulX.app M ((1 : Polynomial R) ⊗ₜ[R, Polynomial.C] m)) = 0
  rw [mulX_tmul, augmentation_tmul]
  simp

private abbrev polynomialModule : ModuleCat.{u} R :=
  (ModuleCat.restrictScalars Polynomial.C).obj (ModuleCat.of (Polynomial R) (Polynomial R))

private def mulXLinear : polynomialModule (R := R) →ₗ[R] polynomialModule (R := R) :=
  ((ModuleCat.restrictScalars Polynomial.C).map
    (ModuleCat.ofHom (LinearMap.mulLeft (Polynomial R) Polynomial.X))).hom

private def coeffZeroLinear : polynomialModule (R := R) →ₗ[R] R where
  toFun p := (p : Polynomial R).coeff 0
  map_add' p q := Polynomial.coeff_add p q 0
  map_smul' r p := by
    change Polynomial R at p
    change (Polynomial.C r * (p : Polynomial R)).coeff 0 = r * (p : Polynomial R).coeff 0
    simp

private lemma mulX_eq_rTensor (M : ModuleCat.{u} R) (z : extend.obj M) :
    (mulX.app M) z = (mulXLinear (R := R)).rTensor M z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | tmul p m => rfl

private lemma augmentation_eq_rTensor (M : ModuleCat.{u} R) (z : extend.obj M) :
    (augmentation.app M) z =
      TensorProduct.lid R M ((coeffZeroLinear (R := R)).rTensor M z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | tmul p m =>
    change augmentation.app M ((p : Polynomial R) ⊗ₜ[R, Polynomial.C] m) = _
    rw [augmentation_tmul]
    rfl

private lemma polynomial_exact :
    Function.Exact (mulXLinear (R := R))
      (coeffZeroLinear (R := R)) := by
  intro p
  constructor
  · intro hp
    refine ⟨(p : Polynomial R).divX, ?_⟩
    change Polynomial.X * (p : Polynomial R).divX = p
    simpa [show (p : Polynomial R).coeff 0 = 0 from hp] using
      Polynomial.X_mul_divX_add (p : Polynomial R)
  · rintro ⟨q, rfl⟩
    change Polynomial R at q
    change (Polynomial.X * (q : Polynomial R)).coeff 0 = 0
    simp

private lemma polynomial_mulX_injective :
    Function.Injective (mulXLinear (R := R)) := by
  intro p q h
  change Polynomial R at p q
  apply Polynomial.ext
  intro n
  have := congrArg (fun f : Polynomial R => f.coeff (n + 1)) h
  change (Polynomial.X * (p : Polynomial R)).coeff (n + 1) =
    (Polynomial.X * (q : Polynomial R)).coeff (n + 1) at this
  simpa using this

private lemma polynomial_shortExact (M : ModuleCat.{u} R) [Module.Flat R M] :
    (ShortComplex.mk (mulX.app M) (augmentation.app M) (mulX_augmentation M)).ShortExact where
  mono_f := by
    rw [ModuleCat.mono_iff_injective]
    intro x y h
    apply Module.Flat.rTensor_preserves_injective_linearMap (M := M)
      (mulXLinear (R := R)) polynomial_mulX_injective
    exact (mulX_eq_rTensor M x).symm.trans (h.trans (mulX_eq_rTensor M y))
  epi_g := by
    rw [ModuleCat.epi_iff_surjective]
    intro m
    exact ⟨(1 : Polynomial R) ⊗ₜ[R, Polynomial.C] m, by simp [augmentation_tmul]⟩
  exact := by
    rw [ShortComplex.moduleCat_exact_iff]
    intro z hz
    have hz' : (coeffZeroLinear (R := R)).rTensor M z = 0 := by
      apply (TensorProduct.lid R M).injective
      simpa only [map_zero, ← augmentation_eq_rTensor] using hz
    obtain ⟨y, hy⟩ := (Module.Flat.rTensor_exact M polynomial_exact z).mp hz'
    exact ⟨y, (mulX_eq_rTensor M y).trans hy⟩

private abbrev evaluationModule : ModuleCat.{u} (Polynomial R) :=
  restrict.obj (ModuleCat.of R R)

private def baseChangeIso (M : ModuleCat.{u} R) :
    (ModuleCat.restrictScalars Polynomial.C).obj
      ((tensorModuleRight (evaluationModule (R := R))).obj (extend.obj M)) ≅ M :=
  (ModuleCat.restrictScalars Polynomial.C).mapIso (β_ (extend.obj M) evaluationModule) ≪≫
    projectionFormulaIso Polynomial.C evaluationModule M ≪≫
    ((tensoringRight (ModuleCat R)).obj M).mapIso (restrictEvalIso.app (ModuleCat.of R R)) ≪≫
    λ_ M

private lemma baseChangeIso_naturality {M N : ModuleCat.{u} R} (f : M ⟶ N) :
    (ModuleCat.restrictScalars Polynomial.C).map
      ((tensorModuleRight evaluationModule).map (extend.map f)) ≫
        (baseChangeIso N).hom = (baseChangeIso M).hom ≫ f := by
  change (ModuleCat.restrictScalars Polynomial.C).map (extend.map f ▷ evaluationModule) ≫
    _ = _
  dsimp only [baseChangeIso, Iso.trans_hom, Functor.mapIso_hom]
  rw [← Functor.map_comp_assoc, BraidedCategory.braiding_naturality_left,
    Functor.map_comp, Category.assoc,
    reassoc_of% (projectionFormulaIso_natural_right Polynomial.C evaluationModule f)]
  change _ ≫ _ ≫ ((ModuleCat.restrictScalars Polynomial.C).obj evaluationModule ◁ f) ≫
    ((restrictEvalIso.app (ModuleCat.of R R)).hom ▷ N) ≫ (λ_ N).hom =
      (_ ≫ _ ≫ ((restrictEvalIso.app (ModuleCat.of R R)).hom ▷ M) ≫ (λ_ M).hom) ≫ f
  rw [MonoidalCategory.whisker_exchange_assoc]
  have h : (𝟭 (ModuleCat R)).obj (ModuleCat.of R R) ◁ f ≫ (λ_ N).hom =
      (λ_ M).hom ≫ f := MonoidalCategory.leftUnitor_naturality f
  rw [h]
  simp only [Category.assoc]

private def baseChangeComplexIso (P : CochainComplex (ModuleCat.{u} R) ℤ) :
    ((ModuleCat.restrictScalars Polynomial.C).mapHomologicalComplex (.up ℤ)).obj
      (((tensorModuleRight (evaluationModule (R := R))).mapHomologicalComplex
        (.up ℤ)).obj ((CochainComplex.extendScalars Polynomial.C).obj P)) ≅ P :=
  HomologicalComplex.Hom.isoOfComponents (fun i => baseChangeIso (P.X i))
    (fun i j _ => (baseChangeIso_naturality (P.d i j)).symm)

private lemma tensor_mulX_zero (M : ModuleCat.{u} R) :
    (tensorModuleRight (evaluationModule (R := R))).map (mulX.app M) = 0 := by
  apply ModuleCat.hom_ext
  apply TensorProduct.ext
  ext z r
  change ((Polynomial.X : Polynomial R) • z) ⊗ₜ[Polynomial R] r = 0
  rw [TensorProduct.smul_tmul]
  have h : (Polynomial.X : Polynomial R) • r = (0 : evaluationModule (R := R)) := by
    change R at r
    change ev Polynomial.X * r = 0
    simp [ev]
  rw [h, TensorProduct.tmul_zero]

private def polynomialSequence (P : CochainComplex (ModuleCat.{u} R) ℤ) :
    ShortComplex (CochainComplex (ModuleCat.{u} (Polynomial R)) ℤ) :=
  ShortComplex.mk (((mulX (R := R)).mapHomologicalComplex (.up ℤ)).app P)
    (((augmentation (R := R)).mapHomologicalComplex (.up ℤ)).app P) (by
      ext i : 1
      exact mulX_augmentation (P.X i))

private lemma polynomialSequence_shortExact (P : CochainComplex (ModuleCat.{u} R) ℤ)
    (hP : ∀ i, Module.Flat R (P.X i)) : (polynomialSequence P).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro i
  let := hP i
  exact polynomial_shortExact (P.X i)

private lemma tensor_polynomialSequence_f_zero (P : CochainComplex (ModuleCat.{u} R) ℤ) :
    ((tensorModuleRight (evaluationModule (R := R))).mapHomologicalComplex
      (.up ℤ)).map (polynomialSequence P).f = 0 := by
  ext i : 1
  exact tensor_mulX_zero (P.X i)

/-- **Stacks 065F.** If `R[X] → R` evaluates `X` at zero, then for every `K ∈ D(R)`,
the derived tensor product of `K`, regarded as an `R[X]`-complex, with `R` is isomorphic in
`D(R)` to `K ⊞ K[1]`. -/
@[stacks 065F]
public theorem derivedTensorPolynomialEvalZeroIso
    {R : Type u} [CommRing R]
    (D : KFlatDerivedTensoringDatum (Polynomial R))
    (K : DerivedCategory (ModuleCat.{u} R)) :
    let ev : Polynomial R →+* R := Polynomial.eval₂RingHom (RingHom.id R) 0
    letI : Module (Polynomial R) R := ev.toAlgebra.toModule
    Nonempty
      ((ModuleCat.restrictScalars
          (Polynomial.C : R →+* Polynomial R)).mapDerivedCategory.obj
            ((D.tensor.obj ((ModuleCat.restrictScalars ev).mapDerivedCategory.obj K)).obj
              ((DerivedCategory.singleFunctor (ModuleCat.{u} (Polynomial R)) 0).obj
                (ModuleCat.of (Polynomial R) R))) ≅
        Limits.biprod K
          ((shiftFunctor (DerivedCategory (ModuleCat.{u} R)) (1 : ℤ)).obj K)) := by
  let N := evaluationModule (R := R)
  let T := D.tensor.flip.obj
    ((DerivedCategory.singleFunctor (ModuleCat.{u} (Polynomial R)) 0).obj N)
  let : T.CommShift ℤ := D.commShift N
  let : T.IsTriangulated := D.triangulated N
  let F := (ModuleCat.restrictScalars (Polynomial.C : R →+* Polynomial R)).mapDerivedCategory
  let H := T ⋙ F
  let L := DerivedCategory.Q.objPreimage K
  obtain ⟨P, p, hP, hflat, hp, -⟩ := CochainComplex.KFlat.exists_kFlat_resolution L
  let := hp
  let e : DerivedCategory.Q.obj P ≅ K :=
    asIso (DerivedCategory.Q.map p) ≪≫ DerivedCategory.Q.objObjPreimageIso K
  let E := (CochainComplex.extendScalars (Polynomial.C : R →+* Polynomial R)).obj P
  have hE : E.KFlat := kFlat_baseChange Polynomial.C P hP
  let : IsIso ((D.comparison N).app E) := D.comparison_isIso_of_kFlat N E hE
  let a : H.obj (DerivedCategory.Q.obj E) ≅ DerivedCategory.Q.obj P :=
    F.mapIso (asIso ((D.comparison N).app E)) ≪≫
      (ModuleCat.restrictScalars Polynomial.C).mapDerivedCategoryFactors.app
        (((tensorModuleRight N).mapHomologicalComplex (.up ℤ)).obj E) ≪≫
      DerivedCategory.Q.mapIso (baseChangeComplexIso P)
  let S := polynomialSequence P
  have hs : S.ShortExact := polynomialSequence_shortExact P hflat
  have hz : T.map (DerivedCategory.Q.map S.f) = 0 := by
    apply (cancel_mono ((D.comparison N).app E)).mp
    rw [zero_comp]
    have hn := (D.comparison N).naturality S.f
    change T.map (DerivedCategory.Q.map S.f) ≫ (D.comparison N).app E =
      (D.comparison N).app E ≫
        DerivedCategory.Q.map
          (((tensorModuleRight N).mapHomologicalComplex (.up ℤ)).map S.f) at hn
    rw [tensor_polynomialSequence_f_zero P, Functor.map_zero, comp_zero] at hn
    exact hn
  let U := H.mapTriangle.obj (DerivedCategory.triangleOfSES hs)
  have hU : U ∈ distTriang _ :=
    Functor.IsTriangulated.map_distinguished _ (DerivedCategory.triangleOfSES_distinguished hs)
  have hU₁ : U.mor₁ = 0 := by
    change F.map (T.map (DerivedCategory.Q.map S.f)) = 0
    rw [hz, Functor.map_zero]
  obtain ⟨s, -, -⟩ := exists_iso_binaryBiproduct_of_distTriang U.rotate
    (rot_of_distTriang U hU) (by simp [Triangle.rotate_mor₃, hU₁])
  let b : DerivedCategory.Q.obj ((CochainComplex.restrictScalars ev).obj P) ≅
      (ModuleCat.restrictScalars ev).mapDerivedCategory.obj K :=
    ((ModuleCat.restrictScalars ev).mapDerivedCategoryFactors.app P).symm ≪≫
      (ModuleCat.restrictScalars ev).mapDerivedCategory.mapIso e
  exact ⟨(H.mapIso b).symm ≪≫ s ≪≫
    biprod.mapIso (a ≪≫ e) ((shiftFunctor _ (1 : ℤ)).mapIso (a ≪≫ e))⟩

end
end PseudoCoherence
