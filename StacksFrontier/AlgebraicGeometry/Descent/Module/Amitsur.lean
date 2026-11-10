module

public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Homology.Augment
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
public import Mathlib.AlgebraicTopology.CechNerve
public import StacksFrontier.AlgebraicGeometry.Descent.Module.CechConerve
public import StacksFrontier.AlgebraicTopology.ConstantCofaceMapComplex

/-!
# Exactness of the Amitsur complex for a split algebra

For a commutative algebra `A` over `R` and an `R`-module `M`, we form the augmented
Amitsur cochain complex by applying `- ⊗[R] M` to the augmented Čech conerve of
`R → A` and then taking the alternating coface-map complex.

## Main definitions

* `AlgebraicTopology.amitsurExtendedCochainComplex`: the extended Amitsur cochain complex.
* `AlgebraicTopology.extendedAlternatingCofaceMapComplex`: the alternating coface-map complex
  of an augmented cosimplicial object, extended on the left.

## Main results

* `AlgebraicTopology.amitsurExtendedCochainComplex_acyclic_of_section`: the extended Amitsur
  complex is exact when `R → A` admits a section.

## Implementation notes

The rings and coefficient module have independent universes. We lift `R` and `A`
to a common universe to form the Čech conerve over the lifted `R`, tensor with `M`,
and restrict scalars back to `R`. The initial term is `ULift M`, identified with
the tensor of the lifted `R` and `M` by the canonical lift equivalence and left
unitor. Thus, up to these canonical identifications, the complex is indexed in
nonnegative degrees as
`M → A ⊗[R] M → A ⊗[R] A ⊗[R] M → ⋯`; this shifts the source's nonzero
terms by one. Exactness is expressed by `HomologicalComplex.Acyclic`.

The retraction supplied by the section induces a map from the Čech conerve to the constant
cosimplicial object on the base; it and its compatibilities with the augmentation are the
general facts in `CategoryTheory.Arrow.cechSectionMap` and its neighbours, so the argument here
only has to transport them along the coefficient functor and compare homology.  The exactness in
positive degrees of the Moore complex of that constant cosimplicial object — its differentials
being `0, 1, 0, 1, …` — is
`AlgebraicTopology.constantAlternatingCofaceMapComplex_exactAt` of
`StacksFrontier/AlgebraicTopology/ConstantCofaceMapComplex.lean`, where it is proved for an
arbitrary abelian category; it used to be four private lemmas here.

## References

* [Stacks, Tag 023L](https://stacks.math.columbia.edu/tag/023L)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Arrow

universe u v w

namespace AlgebraicTopology

private lemma augmentation_condition {C : Type u} [Category.{v} C] [Preadditive C]
    (X : CosimplicialObject.Augmented C) :
    X.hom.app (.mk 0) ≫ ((alternatingCofaceMapComplex C).obj X.right).d 0 1 = 0 := by
  rw [show ((alternatingCofaceMapComplex C).obj X.right).d 0 1 =
      AlternatingCofaceMapComplex.objD X.right 0 by
    change (CochainComplex.of _ _ (AlternatingCofaceMapComplex.d_squared X.right)).d
      0 (0 + 1) = _
    exact CochainComplex.of_d (fun n : ℕ ↦ X.right.obj (.mk n))
      (AlternatingCofaceMapComplex.objD X.right) 0]
  simp only [AlternatingCofaceMapComplex.objD]
  rw [Fin.sum_univ_two]
  simp only [Fin.val_zero, pow_zero, one_zsmul, Fin.val_one, pow_one, neg_zsmul]
  dsimp only [CosimplicialObject.δ]
  have h₀ : X.hom.app (.mk 0) ≫ X.right.map (SimplexCategory.δ (0 : Fin 2)) =
      X.hom.app (.mk 1) := by
    simpa using (X.hom.naturality (SimplexCategory.δ (0 : Fin 2))).symm
  have h₁ : X.hom.app (.mk 0) ≫ X.right.map (SimplexCategory.δ (1 : Fin 2)) =
      X.hom.app (.mk 1) := by
    simpa using (X.hom.naturality (SimplexCategory.δ (1 : Fin 2))).symm
  calc
    _ = (X.hom.app (.mk 0) ≫ X.right.map (SimplexCategory.δ (0 : Fin 2))) +
        -(X.hom.app (.mk 0) ≫ X.right.map (SimplexCategory.δ (1 : Fin 2))) :=
      (Preadditive.comp_add _ _ _ _ _ _).trans (congrArg (_ + ·) (Preadditive.comp_neg _ _))
    _ = 0 := by rw [h₀, h₁, add_neg_cancel]

/-- The alternating coface-map complex of an augmented cosimplicial object, extended on
the left along a morphism to its augmentation object. -/
def extendedAlternatingCofaceMapComplex {C : Type u} [Category.{v} C] [Preadditive C]
    (X : CosimplicialObject.Augmented C) (Y : C) (e : Y ⟶ X.left) :
    CochainComplex C ℕ :=
  CochainComplex.augment ((alternatingCofaceMapComplex C).obj X.right)
    (e ≫ X.hom.app (.mk 0)) (by
      calc
        (e ≫ X.hom.app (.mk 0)) ≫ _ =
            e ≫ (X.hom.app (.mk 0) ≫ _) := Category.assoc _ _ _
        _ = e ≫ 0 := congrArg (e ≫ ·) (augmentation_condition X)
        _ = 0 := comp_zero)

variable (R : Type u) (A : Type v) (M : Type w) [CommRing R] [CommRing A] [Algebra R A]
  [AddCommGroup M] [Module R M]

/-- Tensor an algebra with a coefficient module, allowing independent universes. -/
def tensorModuleFunctor : CommAlgCat.{v} R ⥤ ModuleCat.{max v w} R where
  obj S := ModuleCat.of R (TensorProduct R S M)
  map f := ModuleCat.ofHom (LinearMap.rTensor M f.hom.toLinearMap)
  map_id S := by
    apply ModuleCat.hom_ext
    apply TensorProduct.ext
    ext s m
    rfl
  map_comp f g := by
    apply ModuleCat.hom_ext
    apply TensorProduct.ext
    ext s m
    rfl

/-- The algebra map, with both rings lifted to a common universe. -/
def algebraMapArrow : Arrow (CommAlgCat.{max u v} (ULift.{v} R)) := by
  letI : Algebra (ULift.{v} R) (ULift.{u} A) := ULift.algebra' R (ULift.{u} A)
  exact Arrow.mk (CommAlgCat.ofHom (Algebra.ofId (ULift.{v} R) (ULift.{u} A)))

/-- The augmented cosimplicial `R`-module obtained from the Čech conerve of `R → A` by
tensoring with the coefficient module. -/
noncomputable def amitsurAugmentation :
    CosimplicialObject.Augmented (ModuleCat.{max u v w} R) :=
  (CosimplicialObject.Augmented.whiskeringObj _ _
    (tensorModuleFunctor (ULift.{v} R) M ⋙
      ModuleCat.restrictScalars (algebraMap R (ULift.{v} R)))).obj
    (algebraMapArrow R A).augmentedCechConerve

/-- The extended Amitsur cochain complex
`M → A ⊗[R] M → A ⊗[R] A ⊗[R] M → ⋯`, up to canonical universe lifts. -/
noncomputable def amitsurExtendedCochainComplex :
    CochainComplex (ModuleCat.{max u v w} R) ℕ :=
  extendedAlternatingCofaceMapComplex (amitsurAugmentation R A M)
    (ModuleCat.of R (ULift.{max u v} M))
    ((ModuleCat.restrictScalars (algebraMap R (ULift.{v} R))).map
      (ModuleCat.ofHom ((ULift.moduleEquiv : ULift.{max u v} M ≃ₗ[ULift.{v} R] M).trans
        (TensorProduct.lid (ULift.{v} R) M).symm).toLinearMap))

/-- **Stacks Lemma 023L.** If `R → A` admits a section, then the extended Amitsur
cochain complex with coefficients in any `R`-module `M` is exact. -/
@[stacks 023L]
theorem amitsurExtendedCochainComplex_acyclic_of_section
    (h : Nonempty (A →ₐ[R] R)) :
    (amitsurExtendedCochainComplex R A M).Acyclic := by
  rcases h with ⟨h⟩
  let : Algebra (ULift.{v} R) (ULift.{u} A) := ULift.algebra' R (ULift.{u} A)
  let f := algebraMapArrow R A
  let s' : ULift.{u} A →ₐ[ULift.{v} R] ULift.{v} R := {
    toRingHom := {
      toFun := fun x => ⟨h x.down⟩
      map_one' := by ext; exact h.map_one
      map_mul' x y := by ext; exact h.map_mul x.down y.down
      map_zero' := by ext; exact h.map_zero
      map_add' x y := by ext; exact h.map_add x.down y.down
    }
    commutes' x := by ext; exact h.commutes x.down
  }
  let F : CommAlgCat.{max u v} (ULift.{v} R) ⥤ ModuleCat.{max u v w} R :=
    tensorModuleFunctor (ULift.{v} R) M ⋙
      ModuleCat.restrictScalars (algebraMap R (ULift.{v} R))
  let s : f.right ⟶ f.left := CommAlgCat.ofHom s'
  have hsf : f.hom ≫ s = 𝟙 f.left := by ext
  let XconstRight := (CosimplicialObject.const _).obj f.left
  let pAlg : XconstRight ⟶ f.cechConerve := f.augmentedCechConerve.hom
  let p : XconstRight ⋙ F ⟶ f.cechConerve ⋙ F := Functor.whiskerRight pAlg F
  let q : f.cechConerve ⋙ F ⟶ XconstRight ⋙ F :=
    Functor.whiskerRight (Arrow.cechSectionMap s hsf) F
  have hpq : p ≫ q = 𝟙 _ := by
    calc
      p ≫ q = Functor.whiskerRight (pAlg ≫ Arrow.cechSectionMap s hsf) F := by simp [p, q]
      _ = Functor.whiskerRight (𝟙 XconstRight) F :=
        congrArg (fun t => Functor.whiskerRight t F)
          (Arrow.cechAugmentation_section_comp (f := f) s hsf)
      _ = 𝟙 (XconstRight ⋙ F) := Functor.whiskerRight_id' F
  let 𝒜 := alternatingCofaceMapComplex (ModuleCat.{max u v w} R)
  have hH : Homotopy (𝒜.map q ≫ 𝒜.map p) (𝟙 (𝒜.obj (f.cechConerve ⋙ F))) := by
    refine Nonempty.some ?_
    obtain ⟨H, Hnat, Hzero, Hone⟩ := Arrow.exists_homotopy_mapCechConerve_id
      (Arrow.cechRetractionEndomorphism s hsf) (by simp [Arrow.cechRetractionEndomorphism])
    rw [← 𝒜.map_comp, ← 𝒜.map_id]
    refine homotopic_alternatingCofaceMapComplex_map (Relation.EqvGen.rel _ _
      ⟨fun n α => F.map (H n α), fun ⦃n m⦄ g α => ?_, fun n => ?_, fun n => ?_⟩)
    · change F.map (f.cechConerve.map g) ≫ F.map (H m α) =
        F.map (H n ((SSet.stdSimplex.obj (SimplexCategory.mk 1)).map g.op α)) ≫
          F.map (f.cechConerve.map g)
      rw [← F.map_comp, Hnat g α, F.map_comp]
    · dsimp [p, q]
      rw [Hzero n, ← F.map_comp, ← NatTrans.comp_app]
      exact congrArg (fun t => F.map (NatTrans.app t n))
        (Arrow.cechSection_augmentation_comp s hsf).symm
    · dsimp
      rw [Hone n]
      simp
  have hpqC : 𝒜.map p ≫ 𝒜.map q = 𝟙 _ := by rw [← 𝒜.map_comp, hpq, 𝒜.map_id]
  let eEquiv : ULift.{max u v} M ≃ₗ[ULift.{v} R] TensorProduct (ULift.{v} R) (ULift.{v} R) M :=
    (ULift.moduleEquiv : ULift.{max u v} M ≃ₗ[ULift.{v} R] M).trans
      (TensorProduct.lid (ULift.{v} R) M).symm
  let e : ModuleCat.of R (ULift.{max u v} M) ⟶ (𝒜.obj (XconstRight ⋙ F)).X 0 :=
    (ModuleCat.restrictScalars (algebraMap R (ULift.{v} R))).map
      (ModuleCat.ofHom eEquiv.toLinearMap)
  have hV (n : ℕ) (hn : 0 < n) : (𝒜.obj (XconstRight ⋙ F)).ExactAt n := by
    let eV := 𝒜.mapIso (Functor.constComp SimplexCategory f.left F)
    exact (exactAt_iff_of_quasiIsoAt eV.hom n).mpr (by
      simpa [𝒜, eV, constantAlternatingCofaceMapComplex] using
        constantAlternatingCofaceMapComplex_exactAt (F.obj f.left) n hn)
  have key : ∀ {U V : CochainComplex (ModuleCat.{max u v w} R) ℕ} (p : V ⟶ U) (q : U ⟶ V),
      p ≫ q = 𝟙 V → Homotopy (q ≫ p) (𝟙 U) → (∀ n, 0 < n → V.ExactAt n) →
      ∀ {Y : ModuleCat.{max u v w} R} (e : Y ⟶ V.X 0), Function.Bijective e →
      ∀ (w : (e ≫ p.f 0) ≫ U.d 0 1 = 0), (CochainComplex.augment U (e ≫ p.f 0) w).Acyclic := by
    intro U V p q hpq H hV Y e he w
    have hcomp : (e ≫ p.f 0) ≫ q.f 0 = e := by
      rw [Category.assoc, ← HomologicalComplex.comp_f, hpq, HomologicalComplex.id_f,
        Category.comp_id]
    rw [HomologicalComplex.acyclic_iff]
    rintro (_ | _ | n)
    · rw [HomologicalComplex.exactAt_iff' _ 0 0 1 (by simp) (by simp),
        ShortComplex.moduleCat_exact_iff]
      change ∀ x : Y, (e ≫ p.f 0) x = 0 → ∃ y : Y, (0 : Y ⟶ Y) y = x
      intro x hx
      have hz : q.f 0 ((e ≫ p.f 0) x) = e x := by
        simpa using congrArg (fun g : Y ⟶ V.X 0 => g x) hcomp
      rw [hx] at hz
      have hx0 : x = 0 := he.1 (by simpa using hz.symm)
      exact ⟨0, by simp [hx0]⟩
    · rw [HomologicalComplex.exactAt_iff' _ 0 1 2 (by simp) (by simp),
        ShortComplex.moduleCat_exact_iff]
      change ∀ x : U.X 0, (U.d 0 1) x = 0 → ∃ y : Y, (e ≫ p.f 0) y = x
      intro x hx
      have hc : (q ≫ p).f 0 = U.d 0 1 ≫ H.hom 1 0 + 𝟙 (U.X 0) := by
        rw [H.comm 0, dNext_eq H.hom (by simp : (ComplexShape.up ℕ).Rel 0 1)]
        simp [prevD]
      obtain ⟨y, hy⟩ := he.2 (q.f 0 x)
      refine ⟨y, ?_⟩
      calc
        (e ≫ p.f 0) y = p.f 0 (e y) := rfl
        _ = p.f 0 (q.f 0 x) := by rw [hy]
        _ = x := by simpa [hx] using congrArg (fun g : U.X 0 ⟶ U.X 0 => g x) hc
    · have : QuasiIsoAt q (n + 1) :=
        (⟨q, p, H, .ofEq hpq⟩ : HomotopyEquiv U V).quasiIsoAt_hom (n + 1)
      have hu := (quasiIsoAt_iff_exactAt' q (n + 1) (hV (n + 1) (by omega))).mp this
      rw [HomologicalComplex.exactAt_iff' _ (n + 1) (n + 2) (n + 3) (by simp) (by simp)]
      rwa [HomologicalComplex.exactAt_iff' U n (n + 1) (n + 2) (by simp) (by simp)] at hu
  exact key (𝒜.map p) (𝒜.map q) hpqC hH hV e
    ⟨fun _ _ hab => eEquiv.injective hab, fun y => eEquiv.surjective y⟩ <|
      (Category.assoc _ _ _).trans <|
        (congrArg (e ≫ ·) (augmentation_condition (amitsurAugmentation R A M))).trans comp_zero

end AlgebraicTopology
