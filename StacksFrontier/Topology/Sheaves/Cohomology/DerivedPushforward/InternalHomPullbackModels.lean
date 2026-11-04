module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.InternalHomPullbackModelAbstract
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.InternalHomPullbackTensorModels
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.InternalHomPullbackHomComplexMap
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.StrictlyPerfectHomRepresentation
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedApplicationKFlatSource
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.InternalHomStalkTransportClauses
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedCurryingTransposeClauses
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafTensorAdditiveOnOpens
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.AssociatedSheafComparison

/-!
# The canonical map of Tag 08I3 on representatives

Let `h : (X, 𝒪_X) ⟶ (Y, 𝒪_Y)` be a morphism of ringed spaces and let `E`, `F` be K-flat complexes
of `𝒪_Y`-modules whose internal Hom complex `𝓗om^•(E, F)` is K-flat.  The canonical map

`Lh^* R𝓗om(QE, QF) ⟶ R𝓗om(Lh^*QE, Lh^*QF)`

of Tag 08I3, precomposed with `Lh^*` of the comparison `σ : Q𝓗om^•(E, F) ⟶ R𝓗om(QE, QF)` of
Tag 08DM, is the class of the comparison `h^*𝓗om^•(E, F) ⟶ 𝓗om^•(h^*E, h^*F)` of internal Hom
complexes, read through `Lh^*Q ⟶ Q h^*` and through `σ` on `X`.

## Main results

* `Stacks.Cohomology.DerivedInternalHomPullback.derivedPullbackSheafHomMap_eq_site`: the map of
  Tag 08I3 read at the ringed site of the opens.
* `Stacks.Cohomology.DerivedInternalHomPullback.isIso_derivedPullbackSheafHomMap_of_models`:
  Tag 08I3 is invertible at a K-flat source, through the models of this file.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open scoped CategoryTheory.Prod Stacks.Topology.SheafTensorAdditiveOnOpens
open Stacks.Cohomology.DerivedPullbackTensor

namespace Stacks.Cohomology.DerivedInternalHomPullback

universe u

attribute [local instance] HasDerivedCategory.standard

-- The derived pullback and the derived internal hom name the structure sheaf of a ringed space
-- differently, by `structureSheafRing` and by `Stacks.SheafOfModules.Tensor.ringSheaf`; the two
-- are the same sheaf of rings by `rfl`, and every statement below mixes them.
-- `structureSheafRing` is `@[instance_reducible]` already, so it is unfolded both by instance
-- search and at `implicit` transparency, and it is deliberately absent from the list below: a
-- local `implicit_reducible` on it would only remove the former.
attribute [local implicit_reducible] CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf TopCat.Sheaf TopCat.Presheaf.IsSheaf

-- `Tensor.ringSheaf` is seated at `instance_reducible` and *not* at `implicit_reducible`:
-- `implicitReducible` unfolds at `TransparencyMode.implicit`, which is strictly *above*
-- `.instances`, whereas `instanceReducible` unfolds at `.instances` and at every level above it.
-- `.instances` is the transparency at which instance search runs and at which the congruence
-- `convert` builds compares the instance arguments of a coercion, so a `Tensor.ringSheaf` opened
-- only at `.implicit` stays shut in the one place this file needs it open — the residual goal of
-- `tensorHomBijection_homComplexComparison` below, whose two sides differ only by this naming.
attribute [local instance_reducible] Stacks.SheafOfModules.Tensor.ringSheaf

-- Sheafification of presheaves of abelian groups on the open-cover site of a space, and the
-- description of its weak equivalences, are the two hypotheses the additivity of `⊗_{𝒪_Z}` is
-- proved from.  Instance search does not find them on its own, because the category level of
-- `Opens Z` has to be guessed before they can even be looked for; they are seated by name.
attribute [local instance] Stacks.AssociatedSheaf.hasModuleSheafify
  Stacks.AssociatedSheaf.moduleSheafifyWEqualsLocallyBijective

-- The additivity of `⊗_{𝒪_Z}` in each variable, and the existence of the total tensor complexes,
-- are taken from their shared home over an arbitrary space and sheaf of rings on it, which is
-- opened above: they are `scoped` instances there, and all three are stated at
-- `Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Rc` for
-- `Rc : TopCat.Sheaf CommRingCat Y`, which reads the space `Y` off the *type* of the sheaf of
-- rings.  This is why every total tensor complex below names the tensor product at `Z.sheaf` with
-- all five universes pinned, and not at the anonymous constructor `⟨Z.presheaf, Z.IsSheaf⟩`: only
-- `Z.sheaf` has `TopCat.Sheaf _ Z` there syntactically, so at the anonymous spelling instance
-- search would have to unfold `TopCat.Sheaf`, which it cannot do at `.instances` transparency, and
-- it falls through to the general `Stacks.SheafOfModules.Tensor.sheafTensor_obj_additive`, whose
-- `WEqualsLocallyBijective` side goal then exhausts the heartbeat budget.

variable (Z : RingedSpace.{u, u})

/-- The internal Hom complex of Tag 0A8Z on a ringed space. -/
abbrev homComplexObj
    (A B : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Z) ℤ) :
    CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Z) ℤ :=
  (AlgebraicGeometry.RingedSite.sheafHomComplex (Stacks.SheafOfModules.ringedSite Z.sheaf) A B).obj

/-- The values of the internal Hom complex bifunctor are the internal Hom complexes. -/
theorem homComplexBifunctor_obj_obj
    (A B : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Z) ℤ) :
    ((AlgebraicGeometry.RingedSite.sheafHomComplexBifunctor
        (Stacks.SheafOfModules.ringedSite Z.sheaf)).obj (op A)).obj B = homComplexObj Z A B := rfl

/-- The comparison `Q𝓗om^•(A, B) ⟶ R𝓗om(QA, QB)` of Tag 08DM on a ringed space. -/
abbrev homComplexComparison
    (A B : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Z) ℤ) :
    DerivedCategory.Q.obj (AlgebraicGeometry.RingedSite.sheafHomComplex
        (Stacks.SheafOfModules.ringedSite Z.sheaf) A B).obj ⟶
      ((Stacks.SheafOfModules.derivedSheafHom Z.sheaf).obj (op (DerivedCategory.Q.obj A))).obj
        (DerivedCategory.Q.obj B) :=
  RingedSite.strictlyPerfectHomComparison (Stacks.SheafOfModules.ringedSite Z.sheaf)
    (RingedSite.derivedInternalHomOfBifunctor (Stacks.SheafOfModules.ringedSite Z.sheaf)) A B

/-- The transpose of the comparison of Tag 08DM at a K-flat source, on a ringed space. -/
theorem derivedCurryHomEquiv_homComplexComparison
    (A B : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Z) ℤ)
    (hA : AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.KFlat Z A) :
    RingedSite.derivedCurryHomEquiv (Stacks.SheafOfModules.ringedSite Z.sheaf)
        (DerivedCategory.Q.obj (AlgebraicGeometry.RingedSite.sheafHomComplex
          (Stacks.SheafOfModules.ringedSite Z.sheaf) A B).obj)
        (DerivedCategory.Q.obj A) (DerivedCategory.Q.obj B) (homComplexComparison Z A B) =
      internalHomToTensor Z (AlgebraicGeometry.RingedSite.sheafHomComplex
          (Stacks.SheafOfModules.ringedSite Z.sheaf) A B).obj A ≫
        DerivedCategory.Q.map (AlgebraicGeometry.RingedSite.cochainEvaluation
          (Stacks.SheafOfModules.ringedSite Z.sheaf) A B) := by
  convert RingedSite.derivedCurryHomEquiv_strictlyPerfectHomComparison
    (Stacks.SheafOfModules.ringedSite Z.sheaf) A B hA using 1
  rfl

/-- `derivedCurryHomEquiv_homComplexComparison` with the bijection read as a bijection of types. -/
theorem derivedCurryHomEquiv_toEquiv_homComplexComparison
    (A B : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Z) ℤ)
    (hA : AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.KFlat Z A) :
    (RingedSite.derivedCurryHomEquiv (Stacks.SheafOfModules.ringedSite Z.sheaf)
        (DerivedCategory.Q.obj (AlgebraicGeometry.RingedSite.sheafHomComplex
          (Stacks.SheafOfModules.ringedSite Z.sheaf) A B).obj)
        (DerivedCategory.Q.obj A) (DerivedCategory.Q.obj B)).toEquiv
        (homComplexComparison Z A B) =
      internalHomToTensor Z (AlgebraicGeometry.RingedSite.sheafHomComplex
          (Stacks.SheafOfModules.ringedSite Z.sheaf) A B).obj A ≫
        DerivedCategory.Q.map (AlgebraicGeometry.RingedSite.cochainEvaluation
          (Stacks.SheafOfModules.ringedSite Z.sheaf) A B) :=
  derivedCurryHomEquiv_homComplexComparison Z A B hA

/-- The cochain-level evaluation of Tag 0A90, with its source written as a total tensor complex
on pairs. -/
abbrev cochainEvaluationPair
    (A B : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Z) ℤ) :
    (totalComplexPair (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z.sheaf)).obj
        (homComplexObj Z A B, A) ⟶ B :=
  AlgebraicGeometry.RingedSite.cochainEvaluation (Stacks.SheafOfModules.ringedSite Z.sheaf) A B

/-- The evaluation of the internal Hom complex bifunctor of Tag 0A8Z is the cochain-level
evaluation.

The right-hand side is `cochainEvaluationPair`, and not
`AlgebraicGeometry.RingedSite.cochainEvaluation` itself, and that is what makes the statement
elaborate.  `cochainEvaluation` has the source of its type written as
`((Tensor.tensorComplex Z.sheaf).obj 𝓗om^•(A, B)).obj A`, whereas the type of
`Transpose.evaluation` writes it as
`(totalComplexPair (sheafTensor Z.sheaf)).obj ((Hc.obj (op A)).obj B, A)`; the two differ *twice
at once*, in the curried-versus-pair spelling of the tensor product and in the
bifunctor-versus-`sheafHomComplex` spelling of the internal Hom complex.  Each difference is
`rfl` on its own — the second is `homComplexBifunctor_obj_obj` above — and one `isDefEq` on both
at once exhausts the heartbeat budget at `whnf`, which is reported against the line the
declaration's type begins on.  `cochainEvaluationPair` is the type ascription that pays the
tensor one in advance, so only the internal-Hom one is left here. -/
theorem evaluation_sheafHomComplexBifunctor
    (A B : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Z) ℤ) :
    Transpose.evaluation (AlgebraicGeometry.RingedSite.sheafHomComplexBifunctor
        (Stacks.SheafOfModules.ringedSite Z.sheaf))
      (totalComplexPair (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z.sheaf))
      (AlgebraicGeometry.RingedSite.curryHomEquivPair
        (Stacks.SheafOfModules.ringedSite Z.sheaf)) A B =
      cochainEvaluationPair Z A B := by
  have h := (AlgebraicGeometry.RingedSite.curryHomEquiv
    (Stacks.SheafOfModules.ringedSite Z.sheaf)
    (AlgebraicGeometry.RingedSite.sheafHomComplex
      (Stacks.SheafOfModules.ringedSite Z.sheaf) A B).obj A B).apply_symm_apply
    (AlgebraicGeometry.RingedSite.cochainEvaluation (Stacks.SheafOfModules.ringedSite Z.sheaf) A B)
  rw [AlgebraicGeometry.RingedSite.curryHomEquiv_symm_cochainEvaluation] at h
  exact h

/-- `derivedCurryHomEquiv_toEquiv_homComplexComparison` at the internal Hom complex object. -/
theorem tensorHomBijection_homComplexComparison
    (A B : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Z) ℤ)
    (hA : AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.KFlat Z A) :
    tensorHomBijection Z (DerivedCategory.Q.obj (homComplexObj Z A B)) (DerivedCategory.Q.obj A)
        (DerivedCategory.Q.obj B) (homComplexComparison Z A B) =
      internalHomToTensor Z (homComplexObj Z A B) A ≫
        DerivedCategory.Q.map (cochainEvaluationPair Z A B) := by
  convert derivedCurryHomEquiv_toEquiv_homComplexComparison Z A B hA using 1

/-- Precomposing with the image of an identity written as `eqToHom`. -/
private lemma map_eqToHom_prod_id_comp {C D : Type*} [Category C] [Category D] (T : C × C ⥤ D)
    (x E : C) (e : x = x) {W : D} (ev : T.obj (x, E) ⟶ W) :
    T.map (eqToHom e ×ₘ 𝟙 E) ≫ ev = ev := by
  simp

/-- The cochain-level evaluation, precomposed with the identity of the internal Hom complex
written as `eqToHom`, is the evaluation of the internal Hom complex bifunctor. -/
theorem map_eqToHom_comp_cochainEvaluation
    (A B : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Z) ℤ) :
    (totalComplexPair (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z.sheaf)).map
        (eqToHom (homComplexBifunctor_obj_obj Z A B) ×ₘ 𝟙 A) ≫ cochainEvaluationPair Z A B =
      Transpose.evaluation (AlgebraicGeometry.RingedSite.sheafHomComplexBifunctor
          (Stacks.SheafOfModules.ringedSite Z.sheaf))
        (totalComplexPair (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z.sheaf))
        (AlgebraicGeometry.RingedSite.curryHomEquivPair
          (Stacks.SheafOfModules.ringedSite Z.sheaf)) A B :=
  (map_eqToHom_prod_id_comp _ _ _ _ _).trans (evaluation_sheafHomComplexBifunctor Z A B).symm

/-- The currying bijection of Tag 0A90 at the ringed site of the opens is natural in its source
variable, in the shape `Transpose.TensorHomEquivNaturalLeft` is stated at. -/
theorem curryHomEquivPair_naturalLeft :
    Transpose.TensorHomEquivNaturalLeft
      (AlgebraicGeometry.RingedSite.sheafHomComplexBifunctor
        (Stacks.SheafOfModules.ringedSite Z.sheaf))
      (totalComplexPair (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z.sheaf))
      (AlgebraicGeometry.RingedSite.curryHomEquivPair
        (Stacks.SheafOfModules.ringedSite Z.sheaf)) := by
  intro A A' B C φ ψ
  rw [CategoryTheory.uncurry_map_mkHom_id
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z.sheaf).map₂HomologicalComplexReg
      (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)) φ B]
  exact AlgebraicGeometry.RingedSite.curryHomEquiv_naturality_source
    (Stacks.SheafOfModules.ringedSite Z.sheaf) φ B C ψ

/-- The canonical map of the derived tensor product of the internal hom is natural in its first
variable. -/
theorem internalHomToTensor_naturality_left
    {A A' : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Z) ℤ}
    (B : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Z) ℤ)
    (g : A ⟶ A') :
    (internalHomTensorUncurried Z).map (DerivedCategory.Q.map g ×ₘ 𝟙 (DerivedCategory.Q.obj B)) ≫
        internalHomToTensor Z A' B =
      internalHomToTensor Z A B ≫ DerivedCategory.Q.map
        ((totalComplexPair (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z.sheaf)).map (g ×ₘ 𝟙 B)) := by
  have h := internalHomToTensor_naturality Z g (𝟙 B)
  rw [CategoryTheory.Functor.map_id] at h
  exact h

variable {X Y : RingedSpace.{u, u}}

/-- The comparison of internal Hom complexes along `h`, at the ringed site of the opens. -/
abbrev pullbackHomComplexMapSite (h : X ⟶ Y)
    (E F : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y) ℤ) :=
  Transpose.homComparison (pullbackComplex h)
    (AlgebraicGeometry.RingedSite.sheafHomComplexBifunctor
      (Stacks.SheafOfModules.ringedSite Y.sheaf))
    (AlgebraicGeometry.RingedSite.sheafHomComplexBifunctor
      (Stacks.SheafOfModules.ringedSite X.sheaf))
    (totalComplexPair (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.sheaf))
    (totalComplexPair (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf))
    (AlgebraicGeometry.RingedSite.curryHomEquivPair (Stacks.SheafOfModules.ringedSite Y.sheaf))
    (AlgebraicGeometry.RingedSite.curryHomEquivPair (Stacks.SheafOfModules.ringedSite X.sheaf))
    (pullbackTensorComplexNatIso h) E F

/-- The canonical map of Tag 08I3, with the bijection of Tag 08DI at the ringed site of the
opens. -/
theorem derivedPullbackSheafHomMap_eq_site (h : X ⟶ Y)
    (K L : DerivedCategory (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y)) :
    derivedPullbackSheafHomMap h K L =
      Transpose.homComparison (derivedPullbackFunctor h)
        (Stacks.SheafOfModules.derivedSheafHom Y.sheaf)
        (Stacks.SheafOfModules.derivedSheafHom X.sheaf) (internalHomTensorUncurried Y)
        (internalHomTensorUncurried X)
        (tensorHomBijection Y) (tensorHomBijection X)
        (pullbackTensorIso h) K L := rfl

/-- **The canonical map of Tag 08I3 on representatives.**  Let `E`, `F` be K-flat complexes of
`𝒪_Y`-modules whose internal Hom complex is K-flat and whose pullback `h^*E` is K-flat.  If the
comparisons `Q𝓗om^•(E, F) ⟶ R𝓗om(QE, QF)` and `Q𝓗om^•(h^*E, h^*F) ⟶ R𝓗om(Qh^*E, Qh^*F)` of
Tag 08DM are invertible and the comparison `h^*𝓗om^•(E, F) ⟶ 𝓗om^•(h^*E, h^*F)` of internal
Hom complexes is a quasi-isomorphism, then the canonical map
`Lh^*R𝓗om(QE, QF) ⟶ R𝓗om(Lh^*QE, Lh^*QF)` of Tag 08I3 is invertible.  This is the identity of
the two composites `Lh^*Q𝓗om^•(E, F) ⟶ R𝓗om(Lh^*QE, Lh^*QF)`, one through Tag 08I3 and one
through the comparison of internal Hom complexes. -/
theorem isIso_derivedPullbackSheafHomMap_of_models (h : X ⟶ Y)
    (E F : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y) ℤ)
    (hE : AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.KFlat Y E)
    (hF : AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.KFlat Y F)
    (hpE : AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.KFlat X ((pullbackComplex h).obj E))
    (hH : AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.KFlat Y
      (AlgebraicGeometry.RingedSite.sheafHomComplex (Stacks.SheafOfModules.ringedSite Y.sheaf)
        E F).obj)
    [IsIso (homComplexComparison Y E F)]
    [IsIso (homComplexComparison X ((pullbackComplex h).obj E) ((pullbackComplex h).obj F))]
    [QuasiIso (pullbackHomComplexMapSite h E F)] :
    IsIso (derivedPullbackSheafHomMap h (DerivedCategory.Q.obj E) (DerivedCategory.Q.obj F)) := by
  haveI := isIso_derivedPullbackNatTrans_app h F hF
  haveI : IsIso ((derivedPullbackNatTrans h).app
      (((AlgebraicGeometry.RingedSite.sheafHomComplexBifunctor
        (Stacks.SheafOfModules.ringedSite Y.sheaf)).obj (op E)).obj F)) :=
    isIso_derivedPullbackNatTrans_app h _ hH
  haveI := isIso_derivedPullbackNatTrans_app h E hE
  haveI : IsIso (DerivedCategory.Q.map (pullbackHomComplexMapSite h E F)) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 inferInstance
  refine Transpose.isIso_homComparison_of_models (P := derivedPullbackFunctor h)
    (H₁ := Stacks.SheafOfModules.derivedSheafHom Y.sheaf)
    (H₂ := Stacks.SheafOfModules.derivedSheafHom X.sheaf)
    (T₁ := internalHomTensorUncurried Y) (T₂ := internalHomTensorUncurried X)
    (e₁ := tensorHomBijection Y) (e₂ := tensorHomBijection X)
    (m := pullbackTensorIso h) (p := pullbackComplex h)
    (Hc₁ := AlgebraicGeometry.RingedSite.sheafHomComplexBifunctor
      (Stacks.SheafOfModules.ringedSite Y.sheaf))
    (Hc₂ := AlgebraicGeometry.RingedSite.sheafHomComplexBifunctor
      (Stacks.SheafOfModules.ringedSite X.sheaf))
    (Tc₁ := totalComplexPair (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.sheaf))
    (Tc₂ := totalComplexPair (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf))
    (ec₁ := AlgebraicGeometry.RingedSite.curryHomEquivPair
      (Stacks.SheafOfModules.ringedSite Y.sheaf))
    (ec₂ := AlgebraicGeometry.RingedSite.curryHomEquivPair
      (Stacks.SheafOfModules.ringedSite X.sheaf))
    (mc := pullbackTensorComplexNatIso h) (Q₁ := DerivedCategory.Q) (Q₂ := DerivedCategory.Q)
    (ν := derivedPullbackNatTrans h)
    (tensorHomEquivNaturalLeft_ringedSpace Y) (tensorHomEquivNaturalLeft_ringedSpace X)
    (tensorHomEquivDinatural_ringedSpace X) (curriedTargetNatural_ringedSpace X)
    (curryHomEquivPair_naturalLeft X)
    (homComplexObj Y) (homComplexBifunctor_obj_obj Y) (homComplexObj X)
    (homComplexBifunctor_obj_obj X)
    (homComplexComparison Y) (homComplexComparison X) (internalHomToTensor Y)
    (internalHomToTensor X) ?_ ?_ E F
    (cochainEvaluationPair Y E F) ?_
    (cochainEvaluationPair X ((pullbackComplex h).obj E) ((pullbackComplex h).obj F))
    ?_ ?_ ?_ ?_
  · exact fun B g => internalHomToTensor_naturality_left Y B g
  · exact fun B g => internalHomToTensor_naturality_left X B g
  · exact map_eqToHom_comp_cochainEvaluation Y E F
  · exact map_eqToHom_comp_cochainEvaluation X _ _
  · convert tensorHomBijection_homComplexComparison Y E F hE using 1
  · convert tensorHomBijection_homComplexComparison X _ _ hpE using 1
  · exact pullbackTensorIso_inv_app_comp_toTensor_of_kFlat h _ E hH hE

end Stacks.Cohomology.DerivedInternalHomPullback

end
