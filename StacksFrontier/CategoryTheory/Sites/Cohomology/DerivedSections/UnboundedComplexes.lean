module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.Existence
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Localization.RestrictionOfModules
public import StacksFrontier.CategoryTheory.Sites.Cohomology.UnboundedDerivedFunctor.Exactness
public import StacksFrontier.CategoryTheory.Sites.Modules.ExtensionByZeroGenerators
public import StacksFrontier.Algebra.Homology.DerivedCategory.KInjective.Locality
import StacksCore.Tactic.StacksAttribute

/-! # Cohomology of unbounded complexes on a ringed site

Let `(C, O)` be a ringed site. Stacks 07A5 observes that `Mod(O)` is a Grothendieck abelian
category, with generator `⨁_{U ∈ Ob(C)} j_{U!}O_U`, so that every complex of `O`-modules has a
functorial injective quasi-isomorphism into a K-injective complex (Stacks 079P); by Stacks 070K
every exact functor out of `K(Mod(O))` into a triangulated category, and every additive functor
out of `Mod(O)` into an abelian category, then has a right derived functor on the unbounded
derived category `D(O)`, computed on the chosen K-injective resolutions. The three examples the
source lists are `RΓ(C, -) : D(O) ⥤ D(Γ(C, O))`, `RΓ(U, -) : D(O) ⥤ D(O(U))` and
`Rf_* : D(O) ⥤ D(O')`.

This file collects all of this in one statement,
`Stacks.Cohomology.UnboundedComplexes.ringedSite_unboundedComplexes`, and defines the module of
global sections over the ring of global sections, which the first example needs.

## Main definitions

* `Stacks.Cohomology.UnboundedComplexes.globalSectionsRing`: the ring `Γ(C, O)`.
* `Stacks.Cohomology.UnboundedComplexes.globalSectionsModule`: the functor
  `Γ(C, -) : Mod(O) ⥤ Mod_{Γ(C, O)}`.

## Main results

* `Stacks.Cohomology.UnboundedComplexes.isSeparator_sigma_extensionByZero`: the direct sum of the
  `j_{U!}O_U` over all objects `U` is a generator of `Mod(O)`.
* `Stacks.Cohomology.UnboundedComplexes.ringedSite_unboundedComplexes`: Stacks 07A5.

## Implementation notes

The source asks for exactness of `F : K(Mod(O)) ⥤ D` only to call `RF` an exact functor; the
existence of `RF` and the identity `RF(F^•) = F(I^•)` hold for every functor, and are stated so.
That `RF` is exact is stated for the canonical shift-commutation of
`CategoryTheory.Functor.IsRightDerivedFunctor.commShift`.

`RF(F^•) = F(I^•)` is stated as two isomorphisms: the unit of `RF` at the chosen resolution
`I^• = T(F^•)` is invertible, and so is the image under `RF` of the class of the resolution map
`F^• ⟶ I^•`.

The direct image is that of a morphism of ringed topoi in the sense of
`AlgebraicGeometry.RingedToposHom`, out of the ringed topos underlying the ringed site; the
functor `Rf_*` itself is `Stacks.Cohomology.DerivedPushforward.derivedPushforward`.

## References

* [Stacks Project, Tag 07A5](https://stacks.math.columbia.edu/tag/07A5)
* [Stacks Project, Tag 079P](https://stacks.math.columbia.edu/tag/079P)
* [Stacks Project, Tag 070K](https://stacks.math.columbia.edu/tag/070K)
* [Stacks Project, Tag 03EW](https://stacks.math.columbia.edu/tag/03EW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated AlgebraicGeometry
  Opposite

namespace Stacks.Cohomology.UnboundedComplexes

universe u w wA vA uA vD uD

variable (X : RingedSite.{u, u, u})

/-- The ring `Γ(C, O)` of global sections of the structure sheaf of a ringed site: the compatible
families of sections. -/
abbrev globalSectionsRing : Type u :=
  RingCat.sectionsSubring (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj

/-- The global sections of a sheaf of `O`-modules, as a `Γ(C, O)`-submodule of the product of
all its modules of sections. -/
def globalSectionsSubmodule
    (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    Submodule (globalSectionsRing X) (∀ U : X.Cᵒᵖ, M.val.obj U) where
  carrier := {s | ∀ ⦃U V : X.Cᵒᵖ⦄ (f : U ⟶ V), M.val.map f (s U) = s V}
  zero_mem' := by
    intro U V f
    exact map_zero _
  add_mem' := by
    intro s t hs ht U V f
    change M.val.map f (s U + t U) = s V + t V
    rw [map_add, hs f, ht f]
    rfl
  smul_mem' := by
    intro r s hs U V f
    change M.val.map f (r.1 U • s U) = r.1 V • s V
    have hr : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.map f (r.1 U) = r.1 V := r.2 f
    rw [PresheafOfModules.map_smul, hs f, hr]
    rfl

/-- **The global sections functor `Γ(C, -) : Mod(O) ⥤ Mod_{Γ(C, O)}`.** -/
def globalSectionsModule :
    SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ⥤
      ModuleCat.{u} (globalSectionsRing X) where
  obj M := ModuleCat.of _ (globalSectionsSubmodule X M)
  map {M N} φ := ModuleCat.ofHom
    { toFun := fun s => ⟨fun U => φ.val.app U (s.1 U), fun U V f => by
        change N.val.map f (φ.val.app U (s.1 U)) = φ.val.app V (s.1 V)
        rw [← s.2 f]
        exact (PresheafOfModules.naturality_apply φ.val f (s.1 U)).symm⟩
      map_add' := fun s t => Subtype.ext (funext fun U => map_add _ _ _)
      map_smul' := fun r s => Subtype.ext (funext fun U => (φ.val.app U).hom.map_smul _ _) }
  map_id M := by
    ext s
    rfl
  map_comp φ ψ := by
    ext s
    rfl

instance globalSectionsModule_additive : (globalSectionsModule X).Additive where
  map_add := by
    intros
    ext
    rfl

/-- **The direct sum of the extensions by zero `j_{U!}O_U` over all objects `U` of the site is a
generator of `Mod(O)`.** Every sheaf of `O`-modules is a quotient of a direct sum of such
(Stacks 03EW), so two morphisms agreeing after every map out of some `j_{U!}O_U` agree. -/
theorem isSeparator_sigma_extensionByZero :
    IsSeparator (∐ fun U : X.C =>
      (SheafOfModules.extensionByZero.{u, u, u, u}
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).obj
          (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U))) := by
  rw [isSeparator_sigma]
  intro A B g h hgh
  let R := Stacks.SheafOfModules.Tensor.ringSheaf X.O
  have hπ : SheafOfModules.fromGenerators R A ≫ g = SheafOfModules.fromGenerators R A ≫ h := by
    refine Sigma.hom_ext _ _ fun i => ?_
    simp only [SheafOfModules.fromGenerators, colimit.ι_desc_assoc, Discrete.functor_obj_eq_as]
    exact hgh _ ⟨i.1⟩ _
  exact (cancel_epi _).1 hπ

/-- Taking sections over an object is an additive functor. -/
instance evaluation_additive (U : X.Cᵒᵖ) :
    (SheafOfModules.evaluation (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).Additive where
  map_add := by
    intros
    rfl

/-- Every exact functor out of `K(Mod(O))` has a right derived functor; each of its right derived
functors is exact and is computed on the chosen K-injective resolutions. -/
theorem rightDerived_of_triangulated
    [HasDerivedCategory.{w} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))]
    (D : Type uD) [Category.{vD} D] [HasZeroObject D] [HasShift D ℤ]
    [Preadditive D] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
    (F : HomotopyCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
      (ComplexShape.up ℤ) ⥤ D) [F.CommShift ℤ] [F.IsTriangulated] :
    F.HasRightDerivedFunctor (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ)) ∧
    ∀ (RF : DerivedCategory (SheafOfModules.{u}
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ⥤ D)
      (α : F ⟶ DerivedCategory.Qh ⋙ RF)
      [RF.IsRightDerivedFunctor α (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))],
      (letI := Functor.IsRightDerivedFunctor.commShift RF α
        (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ)) ℤ
      RF.IsTriangulated) ∧
      ∀ K, IsIso (α.app ((HomotopyCategory.quotient _ _).obj
          ((Stacks.Injectives.kInjectiveResolutionFunctor _).obj K))) ∧
        IsIso (RF.map (DerivedCategory.Q.map
          ((Stacks.Injectives.kInjectiveResolutionInclusion _).app K))) := by
  have hres : ∀ K : CochainComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ,
      ∃ (I : CochainComplex _ ℤ) (f : K ⟶ I), I.IsKInjective ∧ QuasiIso f :=
    fun K => ⟨_, (Stacks.Injectives.kInjectiveResolutionInclusion _).app K, inferInstance,
      inferInstance⟩
  refine ⟨inferInstance, fun RF α _ => ⟨?_, fun K => ⟨?_, inferInstance⟩⟩⟩
  · exact Stacks.DerivedFunctor.isTriangulated_of_isRightDerivedFunctor hres F RF α
  · exact (F.hasPointwiseRightDerivedFunctor_and_isIso_app_of_exists_quasiIso_isKInjective
      hres).2 DerivedCategory.Qh RF α _ inferInstance

/-- **Stacks 07A5.** Let `(C, O)` be a ringed site.

* `Mod(O)` is a Grothendieck abelian category: it has all colimits, filtered colimits are exact,
  and `⨁_{U ∈ Ob(C)} j_{U!}O_U` is a generator.
* There is a functor `T` on complexes of `O`-modules with a natural transformation `id ⟶ T`
  which at every complex `F^•` is a quasi-isomorphism, injective in every degree, into the
  K-injective complex `T(F^•)`.
* (1) Every exact functor `F : K(Mod(O)) ⥤ D` into a triangulated category has a right derived
  functor `RF : D(O) ⥤ D`; every right derived functor `RF` of `F` is exact, and
  `RF(F^•) = F(T(F^•))`.
* (2) The same holds for the functor `K(Mod(O)) ⥤ D(A)` induced by an additive functor
  `F : Mod(O) ⥤ A` into an abelian category.
* The examples: `RΓ(C, -) : D(O) ⥤ D(Γ(C, O))`, `RΓ(U, -) : D(O) ⥤ D(O(U))` for every object
  `U`, and `Rf_* : D(O) ⥤ D(O')` for every morphism of ringed topoi
  `f : (Sh(C), O) ⟶ (Sh(D), O')` exist. -/
@[stacks 07A5]
theorem ringedSite_unboundedComplexes
    [HasDerivedCategory.{w} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))] :
    (HasColimitsOfSize.{u, u}
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ∧
      AB5OfSize.{u, u} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ∧
      IsSeparator (∐ fun U : X.C =>
        (SheafOfModules.extensionByZero.{u, u, u, u}
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).obj
            (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U))) ∧
      IsGrothendieckAbelian.{u}
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) ∧
    ∃ (T : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ ⥤
        CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
      (η : 𝟭 _ ⟶ T),
      (∀ K, QuasiIso (η.app K) ∧ (∀ n, Mono ((η.app K).f n)) ∧ (T.obj K).IsKInjective) ∧
      (∀ (D : Type uD) [Category.{vD} D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
          [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
          (F : HomotopyCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
            (ComplexShape.up ℤ) ⥤ D) [F.CommShift ℤ] [F.IsTriangulated],
        F.HasRightDerivedFunctor (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ)) ∧
        ∀ (RF : DerivedCategory (SheafOfModules.{u}
              (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ⥤ D)
          (α : F ⟶ DerivedCategory.Qh ⋙ RF)
          [RF.IsRightDerivedFunctor α (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))],
          (letI := Functor.IsRightDerivedFunctor.commShift RF α
            (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ)) ℤ
          RF.IsTriangulated) ∧
          ∀ K, IsIso (α.app ((HomotopyCategory.quotient _ _).obj (T.obj K))) ∧
            IsIso (RF.map (DerivedCategory.Q.map (η.app K)))) ∧
      (∀ (A : Type uA) [Category.{vA} A] [Abelian A] [HasDerivedCategory.{wA} A]
          (F : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ⥤ A) [F.Additive],
        (F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).HasRightDerivedFunctor
          (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ)) ∧
        ∀ (RF : DerivedCategory (SheafOfModules.{u}
              (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ⥤ DerivedCategory A)
          (α : F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
            DerivedCategory.Qh ⋙ RF)
          [RF.IsRightDerivedFunctor α (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))],
          (letI := Functor.IsRightDerivedFunctor.commShift RF α
            (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ)) ℤ
          RF.IsTriangulated) ∧
          ∀ K, IsIso (α.app ((HomotopyCategory.quotient _ _).obj (T.obj K))) ∧
            IsIso (RF.map (DerivedCategory.Q.map (η.app K)))) ∧
      (∀ [HasDerivedCategory.{wA} (ModuleCat.{u} (globalSectionsRing X))],
        ((globalSectionsModule X).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
          DerivedCategory.Qh).HasRightDerivedFunctor
            (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))) ∧
      (∀ (U : X.C)
          [HasDerivedCategory.{wA} (ModuleCat.{u}
            ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op U)))],
        ((SheafOfModules.evaluation (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
            (op U)).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
          DerivedCategory.Qh).HasRightDerivedFunctor
            (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))) ∧
      (∀ (Y : RingedTopos.{u, u, u})
          (f : RingedToposHom ({ C := X.C, J := X.J, O := X.O } : RingedTopos.{u, u, u}) Y),
        (DerivedPushforward.pushforwardOnHomotopy f).HasRightDerivedFunctor
          (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))) := by
  refine ⟨⟨inferInstance, inferInstance, isSeparator_sigma_extensionByZero X, inferInstance⟩,
    Stacks.Injectives.kInjectiveResolutionFunctor _,
    Stacks.Injectives.kInjectiveResolutionInclusion _,
    fun K => ⟨inferInstance, fun n => inferInstance, inferInstance⟩,
    fun D _ _ _ _ _ _ F _ _ => rightDerived_of_triangulated X D F, ?_,
    ?_, ?_, fun _ _ => inferInstance⟩
  · intro A _ _ _ F _
    exact rightDerived_of_triangulated X (DerivedCategory A)
      (F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
  · intro _
    infer_instance
  · intro U _
    infer_instance

end Stacks.Cohomology.UnboundedComplexes

end
