module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedAlgebraHomUnital
public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.BaseChange
public import StacksFrontier.AlgebraicGeometry.Modules.PullbackCompTranspose
public import StacksFrontier.AlgebraicGeometry.SymmetricPullback.TransposeHom
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjPoint.EtaleCoherence
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjPoint.ZariskiBaseChangeModule

/-!
# The restriction maps of the restricted algebras `f^*𝒜`

In Situation 0849 let `𝒜` be the graded algebra on the algebraic space `X`, and for a scheme
point `f : T ⟶ X` let `f^*𝒜` be its restriction to `T`
(`AlgebraicGeometry.Space.RelativeProjSituation.pointAlgebra`).  For a morphism `τ : T' ⟶ T` of
test objects this file constructs the comparison

`τ^*(f^*𝒜) ⟶ (f ∘ τ)^*𝒜`

of graded algebras on `T'`.  It is the adjoint transpose, along `τ^* ⊣ τ_*`, of the restriction map
`f^*𝒜 ⟶ τ_*((f ∘ τ)^*𝒜)`, which on sections over a Zariski open `O` of `T` is the restriction map
of the étale pullbacks along the chart of `τ⁻¹(O)` lying over the chart of `O`.

## Main definitions

* `AlgebraicGeometry.Space.pointRestriction`: the restriction map
  `f^*𝒜 ⟶ τ_*((f ∘ τ)^*𝒜)`, read on the Zariski reading of the étale pullbacks.
* `AlgebraicGeometry.Space.pointComparison`: its adjoint transpose `τ^*(f^*𝒜) ⟶ (f ∘ τ)^*𝒜`.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite
open Stacks.Sheaves.GradedAlgebraEssentiallySmall (gradedPull gradedPush)
open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf (ringedSpaceHom baseAlgebra)

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X : AlgebraicSpaces B S hS}

/-- The morphism of represented algebraic spaces of a morphism of test objects, as a morphism
over `X` between two scheme points. -/
theorem pointHom_comp {T T' : BigFppfOver B S hS} (τ : T' ⟶ T) {f : yoneda.obj T ⟶ X.1}
    {f' : yoneda.obj T' ⟶ X.1} (hf : yoneda.map τ ≫ f = f') :
    representedSpaceMap B S hS τ ≫ pointHom f = pointHom f' :=
  ObjectProperty.hom_ext _ hf

/-- **The restriction map of the restricted algebras.** For a morphism `τ : T' ⟶ T` of test
objects and scheme points `f` of `X` at `T` and `f'` at `T'` with `f' = f ∘ τ`, the morphism
`f^*𝒜 ⟶ τ_*(f'^*𝒜)` of graded algebras on the Zariski site of `T`: the Zariski reading of the
étale restriction map `f^*𝒜 ⟶ φ_*(f'^*𝒜)`, followed by the identification of the Zariski
reading of a direct image along `τ`. -/
def pointRestriction (A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf B S hS X))
    {T T' : BigFppfOver B S hS} (τ : T' ⟶ T) (f : yoneda.obj T ⟶ X.1)
    (f' : yoneda.obj T' ⟶ X.1) (hf : yoneda.map τ ≫ f = f') :
    SheafOfModules.GradedAlgebra.Hom (zariskiReading T (etalePointAlgebra A T f))
      (Stacks.RingedSpace.pushforwardAlgebra (ringedSpaceHom ((BigFppfOver.toScheme B S hS).map τ))
        (zariskiReading T' (etalePointAlgebra A T' f'))) :=
  haveI := isContinuous_selfOpensFunctor B S hS T
  (SheafOfModules.GradedAlgebra.Hom.pushforward (selfOpensStructureMap B S hS T)
      (gradedPullRestriction (representedSpaceMap B S hS τ) (pointHom f) (pointHom f')
        (pointHom_comp τ hf) A)).comp
    (zariskiDirectImageHom τ (etalePointAlgebra A T' f')).toHom

/-- **The comparison of restricted algebras along a morphism of test objects**,
`τ^*(f^*𝒜) ⟶ (f ∘ τ)^*𝒜`: the adjoint transpose of `AlgebraicGeometry.Space.pointRestriction`. -/
def pointComparison (A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf B S hS X))
    {T T' : BigFppfOver B S hS} (τ : T' ⟶ T) (f : yoneda.obj T ⟶ X.1)
    (f' : yoneda.obj T' ⟶ X.1) (hf : yoneda.map τ ≫ f = f') :
    SheafOfModules.GradedAlgebra.Hom
      (baseAlgebra ((BigFppfOver.toScheme B S hS).map τ)
        (zariskiReading T (etalePointAlgebra A T f)))
      (zariskiReading T' (etalePointAlgebra A T' f')) :=
  Stacks.RingedSpace.transposeHom _ (pointRestriction A τ f f' hf)

/-- The comparison of direct images of modules of a composite is, on underlying sheaves of sets,
the comparison of direct images of the small étale topoi. -/
theorem pushforwardModulesCompAt_hom_app_val_app {X Y Z : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (g : Y ⟶ Z) (M : Modules.{u, u} B S hS X.1 X.2) (U) (x) :
    ((pushforwardModulesCompAt B S hS f g).hom.app M).val.app U x =
      ((smallToposMorphismTypeU_comp B S hS f g).hom.app
        ((Sheaf.moduleSheafFunctor
          ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O))).obj
            M)).hom.app U x := by
  have h : (Sheaf.moduleSheafFunctor
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Z.1 Z.2).O))).map
        ((pushforwardModulesCompAt B S hS f g).hom.app M) =
      (smallToposMorphismTypeU_comp B S hS f g).hom.app
        ((Sheaf.moduleSheafFunctor
          ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O))).obj
            M) := by
    simp only [pushforwardModulesCompAt, Iso.trans_hom, Iso.symm_hom,
      pushforwardModulesCompTransport, RingedToposHom.pushforwardModulesIsoOfNatIso,
      RingedToposHom.pushforwardModulesCompIso]
    exact Category.id_comp ((smallToposMorphismTypeU_comp B S hS f g).hom.app _)
  exact congrArg (fun k => k.hom.app U x) h

/-- **The coherence of the identification of sections with composition.**  Reading the sections
over a Zariski open of an iterated direct image through the composite is reading them through
the two factors in turn.  Both sides are natural in the sheaf, and the sheaf corepresenting the
sections over the open is subterminal, so they agree. -/
theorem directImageSelfOpensSection_comp {T T' T'' : BigFppfOver B S hS} (τ : T' ⟶ T)
    (τ' : T'' ⟶ T') (O : (chartScheme (idEtaleChart B S hS T)).Opens)
    (F : Sheaf (SmallEtale.topology B S hS (yoneda.obj T'')) (Type u))
    (y : ((testToposHom τ).toToposHom.pushforward.obj
      ((testToposHom τ').toToposHom.pushforward.obj F)).obj.obj
        (op ((selfOpensFunctor B S hS T).obj O))) :
    directImageSelfOpensSection (τ' ≫ τ) O F
        (((smallToposMorphismTypeU_comp B S hS (representedSpaceMap B S hS τ')
          (representedSpaceMap B S hS τ)).hom.app F).hom.app _ y) =
      directImageSelfOpensSection τ' (preimageOpens τ O) F
        (directImageSelfOpensSection τ O _ y) := by
  let adj := (testToposHom τ).toToposHom.adj.comp (testToposHom τ').toToposHom.adj
  have := (testToposHom τ).toToposHom.preservesFiniteLimits
  have := (testToposHom τ').toToposHom.preservesFiniteLimits
  have : Subsingleton
      ((((testToposHom τ).toToposHom.inverseImage ⋙ (testToposHom τ').toToposHom.inverseImage).obj
        ((presheafToSheaf (smallEtaleRingedTopos B S hS (yonedaSpace B S hS T)).J (Type u)).obj
          (Stacks.Sites.SheafSection.smallYoneda.{u}
            (unop (op ((selfOpensFunctor B S hS T).obj O)))))).obj.obj
        (op ((selfOpensFunctor B S hS T'').obj (preimageOpens (τ' ≫ τ) O)))) :=
    Stacks.Sites.SheafSection.subsingleton_obj_of_subsingleton_hom
      (L := (testToposHom τ).toToposHom.inverseImage ⋙ (testToposHom τ').toToposHom.inverseImage)
      (op ((selfOpensFunctor B S hS T).obj O))
      (fun W => subsingleton_hom_selfOpensFunctor B S hS T W O) _
  refine Stacks.Sites.SheafSection.natural_family_ext adj (op ((selfOpensFunctor B S hS T).obj O))
    (fun F y => directImageSelfOpensSection (τ' ≫ τ) O F
        (((smallToposMorphismTypeU_comp B S hS (representedSpaceMap B S hS τ')
          (representedSpaceMap B S hS τ)).hom.app F).hom.app _ y))
    (fun F y => directImageSelfOpensSection τ' (preimageOpens τ O) F
        (directImageSelfOpensSection τ O _ y))
    (fun g y => ?_) (fun g y => ?_) F y
  · dsimp only
    have hn := congrArg (fun k => k.hom.app (op ((selfOpensFunctor B S hS T).obj O)) y)
      ((smallToposMorphismTypeU_comp B S hS (representedSpaceMap B S hS τ')
          (representedSpaceMap B S hS τ)).hom.naturality g)
    exact (congrArg (directImageSelfOpensSection (τ' ≫ τ) O _) hn).trans
      (directImageSelfOpensSection_map (τ' ≫ τ) O g _)
  · exact (congrArg (directImageSelfOpensSection τ' (preimageOpens τ O) _)
      (directImageSelfOpensSection_map τ O
        ((testToposHom τ').toToposHom.pushforward.map g) y)).trans
      (directImageSelfOpensSection_map τ' (preimageOpens τ O) g _)

/-- **The cocycle law of the restriction maps**, on sections: restricting along `τ' ≫ τ` is
restricting along `τ` and then along `τ'`. -/
theorem pointRestriction_comp
    (A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf B S hS X))
    {T T' T'' : BigFppfOver B S hS} (τ : T' ⟶ T) (τ' : T'' ⟶ T') (f : yoneda.obj T ⟶ X.1)
    (f' : yoneda.obj T' ⟶ X.1) (f'' : yoneda.obj T'' ⟶ X.1) (hf : yoneda.map τ ≫ f = f')
    (hf' : yoneda.map τ' ≫ f' = f'') (hf'' : yoneda.map (τ' ≫ τ) ≫ f = f'') (n : ℤ)
    (O : (chartScheme (idEtaleChart B S hS T)).Opens)
    (x : ((zariskiReading T (etalePointAlgebra A T f)).piece n).val.obj (op O)) :
    ((pointRestriction A (τ' ≫ τ) f f'' hf'').app n).val.app (op O) x =
      ((pointRestriction A τ' f' f'' hf').app n).val.app (op (preimageOpens τ O))
        (((pointRestriction A τ f f' hf).app n).val.app (op O) x) := by
  have hc := congrArg (fun k => (k.app n).val.app (op ((selfOpensFunctor B S hS T).obj O)) x)
    (gradedPullRestriction_comp (representedSpaceMap B S hS τ') (representedSpaceMap B S hS τ)
      (pointHom f) (pointHom f') (pointHom f'') (pointHom_comp τ hf) (pointHom_comp τ' hf')
      (pointHom_comp (τ' ≫ τ) hf'') A)
  let E'' := etalePointAlgebra A T'' f''
  let U := op ((selfOpensFunctor B S hS T).obj O)
  let a := ((gradedPullRestriction (representedSpaceMap B S hS τ' ≫ representedSpaceMap B S hS τ)
    (pointHom f) (pointHom f'') (pointHom_comp (τ' ≫ τ) hf'') A).app n).val.app U x
  let b := (((gradedAlgebraPushforwardCompIso B S hS (representedSpaceMap B S hS τ')
    (representedSpaceMap B S hS τ)).inv.app E'').app n).val.app U a
  have hab : ((pushforwardModulesCompAt B S hS (representedSpaceMap B S hS τ')
      (representedSpaceMap B S hS τ)).hom.app (E''.piece n)).val.app U b = a :=
    congrArg (fun k => ((k.app E'').app n).val.app U a)
      (gradedAlgebraPushforwardCompIso B S hS (representedSpaceMap B S hS τ')
        (representedSpaceMap B S hS τ)).inv_hom_id
  let r := gradedPullRestriction (representedSpaceMap B S hS τ) (pointHom f) (pointHom f')
    (pointHom_comp τ hf) A
  let r' := gradedPullRestriction (representedSpaceMap B S hS τ') (pointHom f') (pointHom f'')
    (pointHom_comp τ' hf') A
  have hb : b = (((testToposHom τ).pushforwardModules.map (r'.app n)).val.app U
      ((r.app n).val.app U x)) := hc
  have e1 : ((pointRestriction A (τ' ≫ τ) f f'' hf'').app n).val.app (op O) x =
      directImageSelfOpensSection (τ' ≫ τ) O ((Sheaf.moduleSheafFunctor (testRing T'')).obj
        (E''.piece n)) a := rfl
  have e2 : directImageSelfOpensSection (τ' ≫ τ) O ((Sheaf.moduleSheafFunctor (testRing T'')).obj
        (E''.piece n)) a =
      directImageSelfOpensSection (τ' ≫ τ) O ((Sheaf.moduleSheafFunctor (testRing T'')).obj
        (E''.piece n))
        (((smallToposMorphismTypeU_comp B S hS (representedSpaceMap B S hS τ')
          (representedSpaceMap B S hS τ)).hom.app
            ((Sheaf.moduleSheafFunctor (testRing T'')).obj (E''.piece n))).hom.app U b) :=
    congrArg _ (hab.symm.trans (pushforwardModulesCompAt_hom_app_val_app _ _ _ _ _))
  have e3 := directImageSelfOpensSection_comp τ τ' O
    ((Sheaf.moduleSheafFunctor (testRing T'')).obj (E''.piece n)) b
  have e4 : directImageSelfOpensSection τ O ((testToposHom τ').toToposHom.pushforward.obj
        ((Sheaf.moduleSheafFunctor (testRing T'')).obj (E''.piece n))) b =
      ((Sheaf.moduleSheafFunctor (testRing T')).map (r'.app n)).hom.app _
        (directImageSelfOpensSection τ O ((Sheaf.moduleSheafFunctor (testRing T')).obj
          ((etalePointAlgebra A T' f').piece n)) ((r.app n).val.app U x)) := by
    rw [hb]
    exact directImageSelfOpensSection_map τ O
      ((Sheaf.moduleSheafFunctor (testRing T')).map (r'.app n)) _
  refine e1.trans (e2.trans (e3.trans ?_))
  rw [e4]
  rfl

/-- The transpose of the comparison is the restriction map. -/
theorem homEquiv_pointComparison_app
    (A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf B S hS X))
    {T T' : BigFppfOver B S hS} (τ : T' ⟶ T) (f : yoneda.obj T ⟶ X.1)
    (f' : yoneda.obj T' ⟶ X.1) (hf : yoneda.map τ ≫ f = f') (n : ℤ) :
    (Scheme.Modules.pullbackPushforwardAdjunction
        ((BigFppfOver.toScheme B S hS).map τ)).homEquiv _ _
      ((pointComparison A τ f f' hf).app n) = (pointRestriction A τ f f' hf).app n :=
  Equiv.apply_symm_apply _ _

/-- **The cocycle law of the comparisons**: comparing along `τ' ≫ τ` is comparing along `τ` and
then along `τ'`, through the composition law of inverse images. -/
theorem pointComparison_comp_app
    (A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf B S hS X))
    {T T' T'' : BigFppfOver B S hS} (τ : T' ⟶ T) (τ' : T'' ⟶ T') (f : yoneda.obj T ⟶ X.1)
    (f' : yoneda.obj T' ⟶ X.1) (f'' : yoneda.obj T'' ⟶ X.1) (hf : yoneda.map τ ≫ f = f')
    (hf' : yoneda.map τ' ≫ f' = f'') (hf'' : yoneda.map (τ' ≫ τ) ≫ f = f'') (n : ℤ) :
    (pointComparison A (τ' ≫ τ) f f'' hf'').app n =
      (Scheme.Modules.pullbackComp ((BigFppfOver.toScheme B S hS).map τ')
          ((BigFppfOver.toScheme B S hS).map τ)).inv.app _ ≫
        (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map τ')).map
          ((pointComparison A τ f f' hf).app n) ≫ (pointComparison A τ' f' f'' hf').app n := by
  refine Scheme.Modules.eq_pullbackComp_inv_comp_of_sections ((BigFppfOver.toScheme B S hS).map τ')
    ((BigFppfOver.toScheme B S hS).map τ) ((pointComparison A τ f f' hf).app n)
    ((pointComparison A τ' f' f'' hf').app n) ((pointComparison A (τ' ≫ τ) f f'' hf'').app n)
    (fun O x => ?_)
  refine (congrArg (fun k => k.val.app (op O) x)
    (homEquiv_pointComparison_app A (τ' ≫ τ) f f'' hf'' n)).trans ?_
  simp only [homEquiv_pointComparison_app]
  exact pointRestriction_comp A τ τ' f f' f'' hf hf' hf'' n O x

end AlgebraicGeometry.Space
