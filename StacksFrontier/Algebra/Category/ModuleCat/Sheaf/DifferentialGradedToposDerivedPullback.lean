module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedToposPullbackAcyclic
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedToposDerivedPushforwardComp
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ConeDifferentialGradedModuleToposPullback
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedModuleTransportHomotopy
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedDerivedPullbackTensorFunctor
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GoodAcyclicDifferentialGradedPullbackTensor
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedTensorUnit
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The derived pullback along a morphism of ringed topoi

Let `(f, f♯) : (Sh(C), O_C) ⟶ (Sh(D), O_D)` be a morphism of ringed topoi, let `A` be a sheaf of
differential graded `O_C`-algebras, let `B` be a sheaf of differential graded `O_D`-algebras and
let `φ : B ⟶ f_*A` be a homomorphism of sheaves of differential graded algebras. The pullback of
a right differential graded `B`-module `M` is `f^*M ⊗_{f^*B} A`, the extension of scalars along
the adjoint transpose `f^*B ⟶ A` of `φ` of the pullback `f^*M` of sheaves of modules; it is the
pullback of `M` along `(f, A, φ)`, corepresenting `Q ↦ Hom_B(M, f_*Q)`. This file constructs the
**derived pullback**

`Lf^* : D(B, d) ⥤ D(A, d)`

of [Stacks, Tag 0FTG](https://stacks.math.columbia.edu/tag/0FTG) (2): the left derived extension
(Tag 0FTF) of `K(Mod(B, d)) ⥤ K(Mod(A, d))`, `M ↦ f^*M ⊗_{f^*B} A`, followed by the localization
`K(Mod(A, d)) ⥤ D(A, d)`. Its value on a good module `P` (Tag 0FSA) is `f^*P ⊗_{f^*B} A`.

The same argument gives Tag 0FTF for the functor `M ↦ f^*M ⊗_A 𝒩` of Tag 0FTE, with an
arbitrary differential graded `(A, A')`-bimodule `𝒩`: the pullback of a good module is flat and
K-flat over `A` (condition (3) of Tag 0FSA at the base change `(f, A, φ)`), so the tensor product
with `𝒩` inverts the quasi-isomorphisms between pullbacks of good modules.

## Main definitions

* `SheafOfModules.DifferentialGradedModule.goodLeftDerived`: the left derived extension
  `D(B, d) ⥤ D(A', d)` of a functor of right differential graded modules which preserves homotopy
  and carries quasi-isomorphisms of good modules to quasi-isomorphisms, with its comparison map
  `goodLeftDerivedCounit`.
* `SheafOfModules.DifferentialGradedModule.toposDGPullback`: the pullback
  `M ↦ f^*M ⊗_{f^*B} A` of right differential graded modules along `(f, A, φ)`, and
  `homotopyToposDGPullback` the functor it induces on homotopy categories.
* `SheafOfModules.DifferentialGradedModule.derivedToposPullback`: the left derived extension of
  `M ↦ f^*M ⊗_{f^*B} A`, with `derivedToposPullbackCounit` and `derivedToposPullbackObjIso`.
* `SheafOfModules.DifferentialGradedModule.homotopyToposPullbackTensor`: the functor
  `K(Mod(B, d)) ⥤ K(Mod(A', d))`, `M ↦ f^*M ⊗_A 𝒩` of Tag 0FTE, and
  `derivedToposPullbackTensor` its left derived extension `D(B, d) ⥤ D(A', d)` (Tag 0FTF), with
  its comparison map `derivedToposPullbackTensorCounit`.
* `SheafOfModules.DifferentialGradedModule.derivedPullbackTensorRingedTopos`: **the functor of
  Tag 0FTF**, `derivedToposPullbackTensor` with the compatibilities of the forgetful functors with
  sheaves discharged, at a morphism of ringed topoi in one universe.
* `SheafOfModules.DifferentialGradedModule.derivedPullbackRingedTopos`: **the derived pullback
  `Lf^* : D(B, d) ⥤ D(A, d)`** of Tag 0FTG (2), the functor of Tag 0FTF for the diagonal
  bimodule `{}_A A_A`, with `derivedPullbackRingedToposObjIso` its value `f^*P` on a good module.

## Main results

* `SheafOfModules.DifferentialGradedModule.quasiIso_toposDGPullback_map_of_isGood`: the
  computation of the proof of Tag 0FTF for the pullback. A quasi-isomorphism `ψ` of good modules
  goes to a quasi-isomorphism: the pullback `f^*ψ` of sheaves of modules is a quasi-isomorphism of
  flat and K-flat modules because its cone is the pullback of the cone of `ψ`, which is good
  (Tag 0FSC) and acyclic, hence acyclic after pullback (Tag 0FSI (2)); and the tensor product of
  a flat K-flat acyclic module is acyclic (Tag 0FSI (1)).
* `SheafOfModules.DifferentialGradedModule.isLeftDerivedFunctor_derivedToposPullback`: the
  derived pullback with its comparison map is the left derived functor of
  `M ↦ f^*M ⊗_{f^*B} A` followed by the localization.
* `SheafOfModules.DifferentialGradedModule.isIso_derivedToposPullbackCounit_app`: the comparison
  map is invertible at a good module.
* `SheafOfModules.DifferentialGradedModule.isIso_derivedToposPullbackTensorCounit_app`: the
  comparison map of the functor of Tag 0FTF is invertible at a good module. Tag 0FTF itself,
  with the exactness of the derived functor, is
  `SheafOfModules.DifferentialGradedModule.isLeftDerived_derivedPullbackTensorRingedTopos` of
  `DifferentialGradedToposDerivedPullbackTriangulated.lean`.

## Implementation notes

The ringed topoi have their sites, morphisms and structure sheaves in one universe `u`, and the
modules have their sections there too: this is the setting of the derived pushforward of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/DifferentialGradedToposDerivedPushforward.lean`, in
which the homotopy category of right differential graded modules has a calculus of fractions for
the quasi-isomorphisms and the relative tensor product is constructed. The homomorphism `φ` is
unital (`hφ`), as a homomorphism of differential graded algebras is in the source. Goodness is the
whole of Tag 0FSA, `SheafOfModules.IsGoodToposBaseChange`, and the good resolutions are those of
Tag 0FSH, `SheafOfModules.DifferentialGradedModule.exists_good_quasiIso`.

Many universe arguments are written out: `RingedToposHom X Y` does not determine all the
universes of the declarations about it, and left implicit they default to `0`.

## References

* [Stacks Project, Tag 0FTG](https://stacks.math.columbia.edu/tag/0FTG)
* [Stacks Project, Tag 0FTF](https://stacks.math.columbia.edu/tag/0FTF)
* [Stacks Project, Tag 0FTE](https://stacks.math.columbia.edu/tag/0FTE)
* [Stacks Project, Tag 0FSI](https://stacks.math.columbia.edu/tag/0FSI)
* [Stacks Project, Tag 0FSA](https://stacks.math.columbia.edu/tag/0FSA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Sheaf
open Stacks.Sheaves.RingedToposModules

universe u

namespace SheafOfModules.DifferentialGradedModule

attribute [local instance] Stacks.TensorSheafWorld.monoidalCategory

variable {X Y : AlgebraicGeometry.RingedTopos.{u, u, u}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [X.J.HasSheafCompose (CategoryTheory.forget RingCat.{u})]
  [Y.J.HasSheafCompose (CategoryTheory.forget RingCat.{u})]
  [X.J.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{u})]
  [Y.J.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{u})]
  (f : RingedToposHom X Y) {B : DifferentialGradedAlgebra.{u, u} (toRingCat Y.J Y.O)}

/-! ### The pullback of sheaves of modules -/


/-- The pullback of sheaves of modules `M ↦ f^*M`, applied to right differential graded
`B`-modules: a functor to right differential graded `f^*B`-modules. -/
abbrev toposPullbackFunctor :
    DifferentialGradedModule.{u, u, u} B ⥤
      DifferentialGradedModule.{u, u, u} (toposPullbackAlgebra.{u, u, u, u, u} f B) :=
  transportFunctor.{u, u, u, u, u} (A := B) (toposInverseImageModules.{u, u, u, u, u} f)
    (Stacks.SheafOfModules.TensorEncodings.isSheaf_structureRingPresheaf Y.O)
    (Stacks.SheafOfModules.TensorEncodings.isSheaf_structureRingPresheaf X.O)

/-- The cone of the pullback of `ψ` has acyclic complex exactly when the pullback of the cone of
`ψ` has: both complexes are the mapping cone of `f^*ψ`, the pullback of sheaves of modules being
additive. -/
theorem acyclic_cone_toposPullbackFunctor_map_iff {M M₂ : DifferentialGradedModule.{u, u, u} B}
    (ψ : M ⟶ M₂) :
    (cone ((toposPullbackFunctor f).map ψ)).complex.Acyclic ↔
      ((toposPullbackFunctor f).obj (cone ψ)).complex.Acyclic := by
  rw [(conePackage ((toposPullbackFunctor f).map ψ)).cone_complex]
  show _ ↔ (((toposInverseImageModules.{u, u, u, u, u} f).mapHomologicalComplex _).obj
    (cone ψ).complex).Acyclic
  rw [(conePackage ψ).cone_complex]
  let e := CochainComplex.mappingCone.mapHomologicalComplexIso ψ.toHomologicalComplex
    (toposInverseImageModules.{u, u, u, u, u} f)
  exact ⟨fun h n => (h n).of_iso e.symm, fun h n => (h n).of_iso e⟩

/-- The pullback of sheaves of modules of a good right differential graded `B`-module is flat as
a graded module and K-flat: it is the pullback along the base change `(f, f^*B, η)`, to which
condition (3) of Tag 0FSA applies. -/
theorem isGradedFlat_and_isKFlat_toposPullbackFunctor_obj
    {P : DifferentialGradedModule.{u, u, u} B} (hP : IsGoodToposBaseChange.{u, u, u} P) :
    RelativeTensor.IsGradedFlat
        (GradedModule.ofDifferentialGraded (toposPullbackModule.{u, u, u, u, u} f P)) ∧
      RelativeTensor.IsKFlat (toposPullbackModule.{u, u, u, u, u} f P) :=
  (hP.baseChange f (toposPullbackAlgebra.{u, u, u, u, u} f B)
    (toposPullbackUnit.{u, u, u, u, u} f B)
    (isUnital_toposPullbackUnit.{u, u, u, u, u} f B)).2 _
      (toposPullbackCorepresentableBy.{u, u, u, u, u} f P)

/-- **Tag 0FSI (2) at a quasi-isomorphism of good modules.** The pullback of sheaves of modules
carries a quasi-isomorphism of good right differential graded `B`-modules to a
quasi-isomorphism: its cone is the pullback of the cone, which is good (Tag 0FSC) and acyclic,
so acyclic after pullback. -/
theorem quasiIso_toposPullbackFunctor_map_of_isGood {M M₂ : DifferentialGradedModule.{u, u, u} B}
    (ψ : M ⟶ M₂) (hM : IsGoodToposBaseChange.{u, u, u} M)
    (hM₂ : IsGoodToposBaseChange.{u, u, u} M₂) (hψ : QuasiIso ψ.toHomologicalComplex) :
    QuasiIso ((toposPullbackFunctor f).map ψ).toHomologicalComplex :=
  (acyclic_cone_iff_quasiIso _ _).1 ((acyclic_cone_toposPullbackFunctor_map_iff f ψ).2
    (acyclic_toposPullbackModule_of_isGoodToposBaseChange f
      (cone_isGoodToposBaseChange.{u, u, u, u, u} ψ hM hM₂)
      ((acyclic_cone_iff_quasiIso B ψ).2 hψ)))

/-! ### Left derived extensions computed on good modules -/

section GoodDerived

variable {A' : DifferentialGradedAlgebra.{u, u} (toRingCat X.J X.O)}
  (F : DifferentialGradedModule.{u, u, u} B ⥤ DifferentialGradedModule.{u, u, u} A')
  (hF : PreservesHomotopic F)
  (hq : ∀ {M M₂ : DifferentialGradedModule.{u, u, u} B} (ψ : M ⟶ M₂),
    IsGoodToposBaseChange.{u, u, u} M → IsGoodToposBaseChange.{u, u, u} M₂ →
      QuasiIso ψ.toHomologicalComplex → QuasiIso (F.map ψ).toHomologicalComplex)

/-- A functor of right differential graded modules preserving homotopy, on homotopy categories,
followed by the localization `K(A') ⥤ D(A', d)`. -/
abbrev goodDerivedSource :
    HomotopyCategory.{u, u, u} B ⥤ derivedCategory.{u, u, u} A' :=
  HomotopyCategory.descend F hF ⋙ toDerivedCategory A'

include hq in
/-- If the functor carries quasi-isomorphisms of good modules to quasi-isomorphisms, then on
homotopy categories followed by the localization it inverts the quasi-isomorphisms between good
objects. -/
theorem isIso_goodDerivedSource_map {Z Z' : HomotopyCategory.{u, u, u} B} (s : Z ⟶ Z')
    (hs : quasiIsomorphisms.{u, u, u} B s) (hZ : IsGoodObj Z) (hZ' : IsGoodObj Z') :
    IsIso ((goodDerivedSource F hF).map s) := by
  obtain ⟨ψ, rfl⟩ : ∃ ψ : Z.as ⟶ Z'.as, (HomotopyCategory.quotient B).map ψ = s :=
    ⟨(HomotopyCategory.quotient B).preimage s, (HomotopyCategory.quotient B).map_preimage s⟩
  exact (quasiIsomorphisms.{u, u, u} A').Q_inverts _ ((quasiIsomorphisms_quotient_map_iff _).2
    (hq ψ hZ hZ' (hs ψ rfl)))

omit [Y.J.HasSheafCompose (CategoryTheory.forget RingCat)] in
/-- The good objects resolve every object of `K(Mod(B, d))` (Tag 0FSH). -/
theorem exists_isGoodObj_quasiIso (Z : HomotopyCategory.{u, u, u} B) :
    ∃ (Z' : HomotopyCategory.{u, u, u} B) (_ : IsGoodObj Z') (s : Z' ⟶ Z),
      quasiIsomorphisms.{u, u, u} B s := by
  obtain ⟨P, s, hs, hP⟩ := exists_quasiIso_isGoodObj B Z
  exact ⟨P, hP, s, hs⟩

attribute [local instance] quasiIsomorphisms_hasRightCalculusOfFractions_topos

include hq in
/-- **Tag 0FTF, existence, for a functor inverting quasi-isomorphisms of good modules.** It has a
pointwise left derived functor with respect to the quasi-isomorphisms of `K(Mod(B, d))`: the good
modules resolve every object (Tag 0FSH) and the functor inverts the quasi-isomorphisms between
them. -/
theorem hasPointwiseLeftDerivedFunctor_goodDerivedSource :
    (goodDerivedSource F hF).HasPointwiseLeftDerivedFunctor (quasiIsomorphisms.{u, u, u} B) :=
  LeftDerivedByResolutions.hasPointwiseLeftDerivedFunctor_of_resolutions
    (quasiIsomorphisms.{u, u, u} B) IsGoodObj (exists_isGoodObj_quasiIso (B := B)) _
    (fun s hs hZ hZ' => isIso_goodDerivedSource_map F hF hq s hs hZ hZ')

include hq in
/-- A functor inverting quasi-isomorphisms of good modules has a left derived functor with respect
to the quasi-isomorphisms of `K(Mod(B, d))`. -/
theorem hasLeftDerivedFunctor_goodDerivedSource :
    (goodDerivedSource F hF).HasLeftDerivedFunctor (quasiIsomorphisms.{u, u, u} B) :=
  have := hasPointwiseLeftDerivedFunctor_goodDerivedSource F hF hq
  Functor.hasLeftDerivedFunctor_of_hasPointwiseLeftDerivedFunctor _ _

/-- **The left derived extension `D(B, d) ⥤ D(A', d)`** of a functor inverting
quasi-isomorphisms of good modules. -/
def goodLeftDerived : derivedCategory.{u, u, u} B ⥤ derivedCategory.{u, u, u} A' :=
  haveI := hasLeftDerivedFunctor_goodDerivedSource F hF hq
  Functor.totalLeftDerived (goodDerivedSource F hF) (toDerivedCategory B)
    (quasiIsomorphisms.{u, u, u} B)

/-- The comparison map of the left derived extension. -/
def goodLeftDerivedCounit :
    toDerivedCategory B ⋙ goodLeftDerived F hF hq ⟶ goodDerivedSource F hF :=
  haveI := hasLeftDerivedFunctor_goodDerivedSource F hF hq
  Functor.totalLeftDerivedCounit (goodDerivedSource F hF) (toDerivedCategory B)
    (quasiIsomorphisms.{u, u, u} B)

/-- The left derived extension, with its comparison map, is the left derived functor. -/
theorem isLeftDerivedFunctor_goodLeftDerived :
    (goodLeftDerived F hF hq).IsLeftDerivedFunctor (goodLeftDerivedCounit F hF hq)
      (quasiIsomorphisms.{u, u, u} B) :=
  have := hasLeftDerivedFunctor_goodDerivedSource F hF hq
  inferInstanceAs ((Functor.totalLeftDerived (goodDerivedSource F hF)
    (toDerivedCategory B) (quasiIsomorphisms.{u, u, u} B)).IsLeftDerivedFunctor
      (Functor.totalLeftDerivedCounit (goodDerivedSource F hF) (toDerivedCategory B)
        (quasiIsomorphisms.{u, u, u} B)) (quasiIsomorphisms.{u, u, u} B))

/-- **Tag 0FTF, the value on a good module.** The comparison map of the left derived extension is
invertible at a good right differential graded `B`-module. -/
theorem isIso_goodLeftDerivedCounit_app {P : DifferentialGradedModule.{u, u, u} B}
    (hP : IsGoodToposBaseChange.{u, u, u} P) :
    IsIso ((goodLeftDerivedCounit F hF hq).app ((HomotopyCategory.quotient B).obj P)) :=
  have := isLeftDerivedFunctor_goodLeftDerived F hF hq
  LeftDerivedByResolutions.isIso_app_of_resolutions (quasiIsomorphisms.{u, u, u} B) IsGoodObj
    (exists_isGoodObj_quasiIso (B := B)) _
    (fun s hs hZ hZ' => isIso_goodDerivedSource_map F hF hq s hs hZ hZ')
    (toDerivedCategory B) _ (goodLeftDerivedCounit F hF hq) _ hP

end GoodDerived

/-! ### The pullback `M ↦ f^*M ⊗_{f^*B} A` -/

section DGPullback

variable {A : DifferentialGradedAlgebra.{u, u} (toRingCat X.J X.O)}
  (φ : B ⟶ toposPushforwardAlgebra (toposDirectImageModules f) A) (hφ : φ.IsUnital)

/-- The algebra `A` as a differential graded `(f^*B, A)`-bimodule, through the adjoint transpose
`f^*B ⟶ A` of `φ`. -/
abbrev toposBaseChangeBimodule :
    DifferentialGradedBimodule.{u, u, u} (toposPullbackAlgebra.{u, u, u, u, u} f B) A :=
  (toposBaseChangeStructureMap.{u, u, u, u} f φ).toBimodule
    (isUnital_toposBaseChangeStructureMap.{u, u, u, u} f φ hφ)

/-- Extension of scalars `- ⊗_{f^*B} A` along the adjoint transpose of `φ`, as a tensor product
functor. -/
abbrev toposBaseChangeData :=
  RelativeTensor.tensorFunctorDataDgTensorRight (toposBaseChangeBimodule f φ hφ)

/-- **The pullback `M ↦ f^*M ⊗_{f^*B} A` of right differential graded modules** along
`(f, A, φ)`. -/
abbrev toposDGPullback :
    DifferentialGradedModule.{u, u, u} B ⥤ DifferentialGradedModule.{u, u, u} A :=
  toposPullbackFunctor f ⋙ (toposBaseChangeData f φ hφ).functor

/-- The value of the pullback at `P` is the pullback of `P` along `(f, A, φ)`: it corepresents
`Q ↦ Hom_B(P, f_{*,φ}Q)`. -/
def toposDGPullbackCorepresentableBy (P : DifferentialGradedModule.{u, u, u} B) :
    (toposPushforward (toposDirectImageModules f) φ hφ ⋙
        coyoneda.obj (Opposite.op P)).CorepresentableBy
      ((toposDGPullback f φ hφ).obj P) :=
  toposBaseChangeCorepresentableBy.{u, u, u, u} f φ hφ P

/-- The pullback carries homotopic morphisms to homotopic morphisms. -/
theorem preservesHomotopic_toposDGPullback : PreservesHomotopic (toposDGPullback f φ hφ) :=
  PreservesHomotopic.comp (preservesHomotopic_transportFunctor _ _ _)
    (toposBaseChangeData f φ hφ).preservesHomotopic

/-- The pullback of a good module is flat as a graded module and K-flat: this is condition (3) of
Tag 0FSA at the base change `(f, A, φ)`. -/
theorem isGradedFlat_and_isKFlat_toposDGPullback_obj
    {P : DifferentialGradedModule.{u, u, u} B} (hP : IsGoodToposBaseChange.{u, u, u} P) :
    RelativeTensor.IsGradedFlat
        (GradedModule.ofDifferentialGraded ((toposDGPullback f φ hφ).obj P)) ∧
      RelativeTensor.IsKFlat ((toposDGPullback f φ hφ).obj P) :=
  (hP.baseChange f A φ hφ).2 _ (toposDGPullbackCorepresentableBy f φ hφ P)

/-- A tensor product functor carries a quasi-isomorphism between flat K-flat modules to a
quasi-isomorphism: the cone is flat, K-flat and acyclic, and its tensor product is the cone of the
tensored homomorphism. -/
private theorem quasiIso_tensorFunctorData_map_of_isGradedFlat_and_isKFlat
    {X : AlgebraicGeometry.RingedTopos.{u, u, u}}
    [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    [X.J.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{u})]
    {𝒜 𝒜' : DifferentialGradedAlgebra.{u, u} (toRingCat X.J X.O)}
    {N : DifferentialGradedBimodule.{u, u, u} 𝒜 𝒜'} (D : TensorFunctorData.{u, u, u, u, u} 𝒜 𝒜' N)
    {P Q : DifferentialGradedModule.{u, u, u} 𝒜} (s : P ⟶ Q)
    (hP : RelativeTensor.IsGradedFlat (GradedModule.ofDifferentialGraded P) ∧
      RelativeTensor.IsKFlat P)
    (hQ : RelativeTensor.IsGradedFlat (GradedModule.ofDifferentialGraded Q) ∧
      RelativeTensor.IsKFlat Q)
    (hs : QuasiIso s.toHomologicalComplex) :
    QuasiIso (D.functor.map s).toHomologicalComplex :=
  (acyclic_cone_iff_quasiIso _ _).1 fun n =>
    (acyclic_of_isTensorProduct_of_isKFlat_of_acyclic (isGradedFlat_and_isKFlat_cone s hP hQ).2
      ((acyclic_cone_iff_quasiIso _ s).2 hs) (D.isTensorProduct _) n).of_iso
        (D.coneComplexIso s).symm

/-- **The computation in the proof of Tag 0FTF for the pullback.** The pullback
`M ↦ f^*M ⊗_{f^*B} A` carries a quasi-isomorphism of good right differential graded `B`-modules
to a quasi-isomorphism: the pullback of sheaves of modules of the quasi-isomorphism is a
quasi-isomorphism between flat and K-flat modules, whose cone is flat, K-flat and acyclic, so that
its tensor product with `A` — the cone of the tensor product — is acyclic (Tag 0FSI (1)). -/
theorem quasiIso_toposDGPullback_map_of_isGood {M M₂ : DifferentialGradedModule.{u, u, u} B}
    (ψ : M ⟶ M₂) (hM : IsGoodToposBaseChange.{u, u, u} M)
    (hM₂ : IsGoodToposBaseChange.{u, u, u} M₂) (hψ : QuasiIso ψ.toHomologicalComplex) :
    QuasiIso ((toposDGPullback f φ hφ).map ψ).toHomologicalComplex := by
  exact quasiIso_tensorFunctorData_map_of_isGradedFlat_and_isKFlat (toposBaseChangeData f φ hφ)
    _ (isGradedFlat_and_isKFlat_toposPullbackFunctor_obj f hM)
    (isGradedFlat_and_isKFlat_toposPullbackFunctor_obj f hM₂)
    (quasiIso_toposPullbackFunctor_map_of_isGood f ψ hM hM₂ hψ)

/-- **The pullback on homotopy categories** `K(Mod(B, d)) ⥤ K(Mod(A, d))`. -/
def homotopyToposDGPullback :
    HomotopyCategory.{u, u, u} B ⥤ HomotopyCategory.{u, u, u} A :=
  HomotopyCategory.descend (toposDGPullback f φ hφ) (preservesHomotopic_toposDGPullback f φ hφ)

/-! ### The derived pullback, Tag 0FTG (2) -/

/-- **The derived pullback** `Lf^* : D(B, d) ⥤ D(A, d)` along a morphism of ringed topoi
`(f, f♯)` and a homomorphism `φ : B ⟶ f_*A` of sheaves of differential graded algebras: the left
derived extension (Tag 0FTF) of `M ↦ f^*M ⊗_{f^*B} A` followed by the localization
`K(A) ⥤ D(A, d)`. It is the left derived functor of that composite
(`isLeftDerivedFunctor_derivedToposPullback`), and its value on a good module `P` is
`f^*P ⊗_{f^*B} A` (`derivedToposPullbackObjIso`). -/
def derivedToposPullback : derivedCategory.{u, u, u} B ⥤ derivedCategory.{u, u, u} A :=
  goodLeftDerived (toposDGPullback f φ hφ)
    (preservesHomotopic_toposDGPullback f φ hφ) (quasiIso_toposDGPullback_map_of_isGood f φ hφ)

/-- The comparison map `Lf^*M ⟶ f^*M ⊗_{f^*B} A` of the derived pullback, natural in the object
of `K(Mod(B, d))`. -/
def derivedToposPullbackCounit :
    toDerivedCategory B ⋙ derivedToposPullback f φ hφ ⟶
      homotopyToposDGPullback f φ hφ ⋙ toDerivedCategory A :=
  goodLeftDerivedCounit (toposDGPullback f φ hφ)
    (preservesHomotopic_toposDGPullback f φ hφ) (quasiIso_toposDGPullback_map_of_isGood f φ hφ)

/-- The derived pullback, with its comparison map, is the left derived functor of
`M ↦ f^*M ⊗_{f^*B} A` followed by the localization. -/
instance isLeftDerivedFunctor_derivedToposPullback :
    (derivedToposPullback f φ hφ).IsLeftDerivedFunctor (derivedToposPullbackCounit f φ hφ)
      (quasiIsomorphisms.{u, u, u} B) :=
  isLeftDerivedFunctor_goodLeftDerived (toposDGPullback f φ hφ)
    (preservesHomotopic_toposDGPullback f φ hφ) (quasiIso_toposDGPullback_map_of_isGood f φ hφ)

/-- On a good module the derived pullback is the pullback: the comparison map is invertible. -/
theorem isIso_derivedToposPullbackCounit_app {P : DifferentialGradedModule.{u, u, u} B}
    (hP : IsGoodToposBaseChange.{u, u, u} P) :
    IsIso ((derivedToposPullbackCounit f φ hφ).app ((HomotopyCategory.quotient B).obj P)) :=
  isIso_goodLeftDerivedCounit_app (toposDGPullback f φ hφ)
    (preservesHomotopic_toposDGPullback f φ hφ) (quasiIso_toposDGPullback_map_of_isGood f φ hφ) hP

/-- **The value of the derived pullback on a good module**: at the image in `D(B, d)` of a good
right differential graded `B`-module `P`, the derived pullback is the image in `D(A, d)` of
`f^*P ⊗_{f^*B} A`. -/
def derivedToposPullbackObjIso {P : DifferentialGradedModule.{u, u, u} B}
    (hP : IsGoodToposBaseChange.{u, u, u} P) :
    (derivedToposPullback f φ hφ).obj
        ((toDerivedCategory B).obj ((HomotopyCategory.quotient B).obj P)) ≅
      (toDerivedCategory A).obj
        ((HomotopyCategory.quotient A).obj ((toposDGPullback f φ hφ).obj P)) :=
  @asIso _ _ _ _ _ (isIso_derivedToposPullbackCounit_app f φ hφ hP)

/-! ### The functor `M ↦ f^*M ⊗_A 𝒩`, Tag 0FTF -/

section PullbackTensor

variable {A' : DifferentialGradedAlgebra.{u, u} (toRingCat X.J X.O)}
  (N : DifferentialGradedBimodule.{u, u, u} A A')

/-- The tensor product `- ⊗_A 𝒩` with a differential graded `(A, A')`-bimodule, as a tensor
product functor. -/
abbrev toposPullbackTensorData :=
  RelativeTensor.tensorFunctorDataDgTensorRight N

/-- **The functor `M ↦ f^*M ⊗_A 𝒩`** of right differential graded modules of Tag 0FTE, for a
differential graded `(A, A')`-bimodule `𝒩`; here `f^*M = f^*M ⊗_{f^*B} A` is the pullback along
`(f, A, φ)`. -/
abbrev toposPullbackTensor :
    DifferentialGradedModule.{u, u, u} B ⥤ DifferentialGradedModule.{u, u, u} A' :=
  toposDGPullback f φ hφ ⋙ (toposPullbackTensorData N).functor

/-- The functor `M ↦ f^*M ⊗_A 𝒩` carries homotopic morphisms to homotopic morphisms. -/
theorem preservesHomotopic_toposPullbackTensor :
    PreservesHomotopic (toposPullbackTensor f φ hφ N) :=
  PreservesHomotopic.comp (preservesHomotopic_toposDGPullback f φ hφ)
    (toposPullbackTensorData N).preservesHomotopic

/-- **The functor `K(Mod(B, d)) ⥤ K(Mod(A', d))`, `M ↦ f^*M ⊗_A 𝒩`** of Tag 0FTE. -/
def homotopyToposPullbackTensor :
    HomotopyCategory.{u, u, u} B ⥤ HomotopyCategory.{u, u, u} A' :=
  HomotopyCategory.descend (toposPullbackTensor f φ hφ N)
    (preservesHomotopic_toposPullbackTensor f φ hφ N)

/-- On an object represented by a module `M`, the induced functor is `f^*M ⊗_A 𝒩`. -/
@[simp]
theorem homotopyToposPullbackTensor_obj (M : DifferentialGradedModule.{u, u, u} B) :
    (homotopyToposPullbackTensor f φ hφ N).obj ((HomotopyCategory.quotient B).obj M) =
      (HomotopyCategory.quotient A').obj ((toposPullbackTensor f φ hφ N).obj M) :=
  rfl

/-- **The computation in the proof of Tag 0FTF.** The functor `M ↦ f^*M ⊗_A 𝒩` carries a
quasi-isomorphism of good right differential graded `B`-modules to a quasi-isomorphism: the
pullback of the quasi-isomorphism is a quasi-isomorphism between flat and K-flat `A`-modules
(condition (3) of Tag 0FSA), whose cone is therefore flat, K-flat and acyclic; its tensor product
with `𝒩`, which is the cone of the tensor product, is acyclic by Tag 0FSI (1). -/
theorem quasiIso_toposPullbackTensor_map_of_isGood {M M₂ : DifferentialGradedModule.{u, u, u} B}
    (ψ : M ⟶ M₂) (hM : IsGoodToposBaseChange.{u, u, u} M)
    (hM₂ : IsGoodToposBaseChange.{u, u, u} M₂) (hψ : QuasiIso ψ.toHomologicalComplex) :
    QuasiIso ((toposPullbackTensor f φ hφ N).map ψ).toHomologicalComplex := by
  exact quasiIso_tensorFunctorData_map_of_isGradedFlat_and_isKFlat (toposPullbackTensorData N)
    _ (isGradedFlat_and_isKFlat_toposDGPullback_obj f φ hφ hM)
    (isGradedFlat_and_isKFlat_toposDGPullback_obj f φ hφ hM₂)
    (quasiIso_toposDGPullback_map_of_isGood f φ hφ ψ hM hM₂ hψ)

/-- **The left derived extension `D(B, d) ⥤ D(A', d)` of `M ↦ f^*M ⊗_A 𝒩`** (Tag 0FTF): the
functor `K(Mod(B, d)) ⟶ K(Mod(A', d))` of Tag 0FTE followed by the localization, derived along
the localization `K(Mod(B, d)) ⥤ D(B, d)`. -/
def derivedToposPullbackTensor : derivedCategory.{u, u, u} B ⥤ derivedCategory.{u, u, u} A' :=
  goodLeftDerived (toposPullbackTensor f φ hφ N) (preservesHomotopic_toposPullbackTensor f φ hφ N)
    (quasiIso_toposPullbackTensor_map_of_isGood f φ hφ N)

/-- The comparison map `L(f^*M ⊗_A 𝒩) ⟶ f^*M ⊗_A 𝒩` of the left derived extension, natural in
the object of `K(Mod(B, d))`. -/
def derivedToposPullbackTensorCounit :
    toDerivedCategory B ⋙ derivedToposPullbackTensor f φ hφ N ⟶
      homotopyToposPullbackTensor f φ hφ N ⋙ toDerivedCategory A' :=
  goodLeftDerivedCounit (toposPullbackTensor f φ hφ N)
    (preservesHomotopic_toposPullbackTensor f φ hφ N)
    (quasiIso_toposPullbackTensor_map_of_isGood f φ hφ N)

/-- The left derived extension, with its comparison map, is the left derived functor of
`M ↦ f^*M ⊗_A 𝒩` followed by the localization. -/
instance isLeftDerivedFunctor_derivedToposPullbackTensor :
    (derivedToposPullbackTensor f φ hφ N).IsLeftDerivedFunctor
      (derivedToposPullbackTensorCounit f φ hφ N) (quasiIsomorphisms.{u, u, u} B) :=
  isLeftDerivedFunctor_goodLeftDerived (toposPullbackTensor f φ hφ N)
    (preservesHomotopic_toposPullbackTensor f φ hφ N)
    (quasiIso_toposPullbackTensor_map_of_isGood f φ hφ N)

/-- The comparison map of the left derived extension is invertible at a good module. -/
theorem isIso_derivedToposPullbackTensorCounit_app {P : DifferentialGradedModule.{u, u, u} B}
    (hP : IsGoodToposBaseChange.{u, u, u} P) :
    IsIso ((derivedToposPullbackTensorCounit f φ hφ N).app
      ((HomotopyCategory.quotient B).obj P)) :=
  isIso_goodLeftDerivedCounit_app (toposPullbackTensor f φ hφ N)
    (preservesHomotopic_toposPullbackTensor f φ hφ N)
    (quasiIso_toposPullbackTensor_map_of_isGood f φ hφ N) hP

/-- The value of the left derived extension at a good module `P` is `f^*P ⊗_A 𝒩`, by the
comparison map. -/
def derivedToposPullbackTensorObjIso {P : DifferentialGradedModule.{u, u, u} B}
    (hP : IsGoodToposBaseChange.{u, u, u} P) :
    (derivedToposPullbackTensor f φ hφ N).obj
        ((toDerivedCategory B).obj ((HomotopyCategory.quotient B).obj P)) ≅
      (toDerivedCategory A').obj
        ((HomotopyCategory.quotient A').obj ((toposPullbackTensor f φ hφ N).obj P)) :=
  @asIso _ _ _ _ _ (isIso_derivedToposPullbackTensorCounit_app f φ hφ N hP)

/-- **Tag 0FTF, with the compatibilities of the forgetful functors with sheaves as instance
arguments**, in existential form: the functor `M ↦ f^*M ⊗_A 𝒩` followed by the localization has
a left derived extension whose comparison map is invertible at every good module. The tag is
registered on
`SheafOfModules.DifferentialGradedModule.isLeftDerived_derivedPullbackTensorRingedTopos`,
in which those compatibilities are discharged. -/
theorem exists_leftDerivedExtension_toposPullbackTensor :
    ∃ (Λ : derivedCategory.{u, u, u} B ⥤ derivedCategory.{u, u, u} A')
      (β : toDerivedCategory B ⋙ Λ ⟶
        homotopyToposPullbackTensor f φ hφ N ⋙ toDerivedCategory A'),
      Λ.IsLeftDerivedFunctor β (quasiIsomorphisms.{u, u, u} B) ∧
        ∀ P : DifferentialGradedModule.{u, u, u} B, IsGoodToposBaseChange.{u, u, u} P →
          IsIso (β.app ((HomotopyCategory.quotient B).obj P)) :=
  ⟨derivedToposPullbackTensor f φ hφ N, derivedToposPullbackTensorCounit f φ hφ N,
    inferInstance, fun _ hP => isIso_derivedToposPullbackTensorCounit_app f φ hφ N hP⟩

end PullbackTensor

end DGPullback

/-! ### The tags, at a morphism of ringed topoi in one universe -/

section Tags

attribute [local instance] AlgebraicGeometry.RingedTopos.hasSheafCompose_forget₂_ringCat

variable {X Y : AlgebraicGeometry.RingedTopos.{u, u, u}} (f : RingedToposHom X Y)
  {A : DifferentialGradedAlgebra.{u, u} (toRingCat X.J X.O)}
  {B : DifferentialGradedAlgebra.{u, u} (toRingCat Y.J Y.O)}
  (φ : B ⟶ toposPushforwardAlgebra (Osharp := X.O) (Psharp := Y.O)
    (toposDirectImageModules (X := X) (Y := Y) f) A) (hφ : φ.IsUnital)

/-! #### Tag 0FTF -/

section PullbackTensor

variable {A' : DifferentialGradedAlgebra.{u, u} (toRingCat X.J X.O)}
  (N : DifferentialGradedBimodule.{u, u, u} A A')

/-- **The left derived extension `D(B, d) ⥤ D(A', d)` of `M ↦ f^*M ⊗_A 𝒩`** (Tag 0FTF), along a
morphism of ringed topoi `(f, f♯)`, a homomorphism `φ : B ⟶ f_*A` and a differential graded
`(A, A')`-bimodule `𝒩`: `derivedToposPullbackTensor`, with the compatibilities of the forgetful
functors with sheaves discharged. -/
@[sga "4 XVII 4.2.12" "more general"]
def derivedPullbackTensorRingedTopos :
    derivedCategory.{u, u, u} B ⥤ derivedCategory.{u, u, u} A' :=
  derivedToposPullbackTensor f φ hφ N

/-- The comparison map `L(f^*M ⊗_A 𝒩) ⟶ f^*M ⊗_A 𝒩` of `derivedPullbackTensorRingedTopos`. -/
def derivedPullbackTensorRingedToposCounit :
    toDerivedCategory B ⋙ derivedPullbackTensorRingedTopos f φ hφ N ⟶
      homotopyToposPullbackTensor f φ hφ N ⋙ toDerivedCategory A' :=
  derivedToposPullbackTensorCounit f φ hφ N

/-- `derivedPullbackTensorRingedTopos`, with `derivedPullbackTensorRingedToposCounit`, is the left
derived functor of `M ↦ f^*M ⊗_A 𝒩` followed by the localization. -/
instance isLeftDerivedFunctor_derivedPullbackTensorRingedTopos :
    (derivedPullbackTensorRingedTopos f φ hφ N).IsLeftDerivedFunctor
      (derivedPullbackTensorRingedToposCounit f φ hφ N) (quasiIsomorphisms.{u, u, u} B) :=
  isLeftDerivedFunctor_derivedToposPullbackTensor f φ hφ N

/-- The value of `derivedPullbackTensorRingedTopos` at a good module `P` is `f^*P ⊗_A 𝒩`. -/
def derivedPullbackTensorRingedToposObjIso {P : DifferentialGradedModule.{u, u, u} B}
    (hP : IsGoodToposBaseChange.{u, u, u} P) :
    (derivedPullbackTensorRingedTopos f φ hφ N).obj
        ((toDerivedCategory B).obj ((HomotopyCategory.quotient B).obj P)) ≅
      (toDerivedCategory A').obj
        ((HomotopyCategory.quotient A').obj ((toposPullbackTensor f φ hφ N).obj P)) :=
  derivedToposPullbackTensorObjIso f φ hφ N hP

end PullbackTensor

/-! #### Tag 0FTG (2) -/

/-- **The derived pullback** `Lf^* : D(B, d) ⥤ D(A, d)` along a morphism of ringed topoi
`(f, f♯) : (Sh(C), O_C) ⟶ (Sh(D), O_D)` and a homomorphism `φ : B ⟶ f_*A` of sheaves of
differential graded algebras: the functor of Tag 0FTF for the diagonal bimodule `{}_A A_A`, that
is `derivedPullbackTensorRingedTopos f φ hφ A.diagonalBimodule`. It is the left derived functor
of `M ↦ f^*M ⊗_A A` followed by the localization
(`isLeftDerivedFunctor_derivedPullbackRingedTopos`), and its value on a good module `P` is
`f^*P = f^*P ⊗_{f^*B} A` (`derivedPullbackRingedToposObjIso`). -/
@[stacks 0FTG "(2) derived pullback Lf^*", sga "4 XVII 4.2.12" "Lg*, special case"]
def derivedPullbackRingedTopos : derivedCategory.{u, u, u} B ⥤ derivedCategory.{u, u, u} A :=
  derivedPullbackTensorRingedTopos f φ hφ A.diagonalBimodule

/-- The comparison map `Lf^*M ⟶ f^*M ⊗_A A` of the derived pullback. -/
def derivedPullbackRingedToposCounit :
    toDerivedCategory B ⋙ derivedPullbackRingedTopos f φ hφ ⟶
      homotopyToposPullbackTensor f φ hφ A.diagonalBimodule ⋙ toDerivedCategory A :=
  derivedPullbackTensorRingedToposCounit f φ hφ A.diagonalBimodule

/-- The derived pullback, with its comparison map, is the left derived functor of
`M ↦ f^*M ⊗_A A` followed by the localization. -/
instance isLeftDerivedFunctor_derivedPullbackRingedTopos :
    (derivedPullbackRingedTopos f φ hφ).IsLeftDerivedFunctor
      (derivedPullbackRingedToposCounit f φ hφ) (quasiIsomorphisms.{u, u, u} B) :=
  isLeftDerivedFunctor_derivedPullbackTensorRingedTopos f φ hφ A.diagonalBimodule

/-- On a good module the comparison map of the derived pullback is invertible. -/
theorem isIso_derivedPullbackRingedToposCounit_app {P : DifferentialGradedModule.{u, u, u} B}
    (hP : IsGoodToposBaseChange.{u, u, u} P) :
    IsIso ((derivedPullbackRingedToposCounit f φ hφ).app ((HomotopyCategory.quotient B).obj P)) :=
  isIso_derivedToposPullbackTensorCounit_app f φ hφ A.diagonalBimodule hP

/-- `f^*P ⊗_A {}_A A_A ≅ f^*P`: the tensor product with the diagonal bimodule is the module
itself, the identity functor being a tensor product functor for `{}_A A_A`. -/
def toposPullbackTensorDiagonalIso (P : DifferentialGradedModule.{u, u, u} B) :
    (toposPullbackTensor f φ hφ A.diagonalBimodule).obj P ≅ (toposDGPullback f φ hφ).obj P :=
  TensorFunctorData.uniqueIso (toposPullbackTensorData A.diagonalBimodule)
    (tensorFunctorDataDiagonal A) ((toposDGPullback f φ hφ).obj P)

/-- **The value of the derived pullback on a good module**: at the image in `D(B, d)` of a good
right differential graded `B`-module `P`, the derived pullback is the image in `D(A, d)` of
`f^*P = f^*P ⊗_{f^*B} A` — the comparison map followed by `f^*P ⊗_A A ≅ f^*P`. -/
def derivedPullbackRingedToposObjIso {P : DifferentialGradedModule.{u, u, u} B}
    (hP : IsGoodToposBaseChange.{u, u, u} P) :
    (derivedPullbackRingedTopos f φ hφ).obj
        ((toDerivedCategory B).obj ((HomotopyCategory.quotient B).obj P)) ≅
      (toDerivedCategory A).obj
        ((HomotopyCategory.quotient A).obj ((toposDGPullback f φ hφ).obj P)) :=
  derivedToposPullbackTensorObjIso f φ hφ A.diagonalBimodule hP ≪≫
    (toDerivedCategory A).mapIso ((HomotopyCategory.quotient A).mapIso
      (toposPullbackTensorDiagonalIso f φ hφ P))

end Tags

end SheafOfModules.DifferentialGradedModule

end
