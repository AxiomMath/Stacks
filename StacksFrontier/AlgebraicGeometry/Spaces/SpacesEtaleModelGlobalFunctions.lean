module

public import StacksFrontier.AlgebraicGeometry.Spaces.BaseRingTensorModule
public import StacksFrontier.AlgebraicGeometry.Spaces.SpacesEtaleModelModules
public import StacksFrontier.CategoryTheory.Sites.DenseSubsiteTerminalSections

/-!
# Global functions of the model of the spaces-étale site

Let `X` be an algebraic space.  The model `AlgebraicGeometry.Space.spacesEtaleModelRingedTopos X`
of its ringed spaces-étale site has a terminal object, the image of `X` itself, and the sections of
its structure sheaf over it are the global regular functions of `X`.  The model of the small étale
site of `X` has no terminal object; its ring of global functions
`AlgebraicGeometry.Space.modelGlobalFunctions X` is the ring of compatible families of sections of
its structure sheaf.  The two agree: the small étale model is a dense subsite of the spaces-étale
model (Stacks 03G1), on which the two structure sheaves agree, and sections over a terminal object
are the compatible families on a dense subsite.

This is the identification of base-ring data under which a ring map `R ⟶ Γ(X, 𝒪_X)` read on the
small étale model (the datum of `AlgebraicGeometry.Space.baseRingTensorModule`) and the same map
read on the spaces-étale model (the datum of a morphism to the punctual ringed topos `(pt, R)`)
correspond.

## Main definitions

* `AlgebraicGeometry.Space.spacesEtaleModelGlobalFunctionsEquiv`: the ring isomorphism between the
  sections of the structure sheaf of the spaces-étale model over its terminal object and the global
  functions of the small étale model.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (X : AlgebraicSpaces B S hS)

/-- The restriction of a section over the terminal object of the spaces-étale model to the
objects of the small étale model, read in the structure sheaf of the small étale model. -/
def spacesEtaleModelTerminalRestrict
    (x : (spacesEtaleModelStructureSheaf B S hS X).obj.obj (op (spacesEtaleModelTerminal B S hS X)))
    (V : (SmallModel.{u} (SmallEtale B S hS X.1))ᵒᵖ) :
    (smallEtaleModelStructureSheaf B S hS X).obj.obj V :=
  (spacesEtaleModelStructureRestrictionIso B S hS X).hom.hom.app V
    ((spacesEtaleModelStructureSheaf B S hS X).obj.map
      ((isTerminal_spacesEtaleModelTerminal B S hS X).from
        ((spacesEtaleModelComparison B S hS X).obj V.unop)).op x)

/-- **The global functions of the two models agree**: restriction from the terminal object of the
spaces-étale model to the objects of the small étale model is a ring isomorphism onto the
compatible families of sections of the structure sheaf of the small étale model. -/
def spacesEtaleModelGlobalFunctionsEquiv :
    (spacesEtaleModelStructureSheaf B S hS X).obj.obj (op (spacesEtaleModelTerminal B S hS X)) ≃+*
      modelGlobalFunctions B S hS X := by
  let hT := isTerminal_spacesEtaleModelTerminal B S hS X
  let e := spacesEtaleModelStructureRestrictionIso B S hS X
  let g : (spacesEtaleModelStructureSheaf B S hS X).obj.obj
      (op (spacesEtaleModelTerminal B S hS X)) →+* modelGlobalFunctions B S hS X :=
    { toFun := fun x => ⟨spacesEtaleModelTerminalRestrict B S hS X x, fun {V V'} h => by
        refine (ConcreteCategory.congr_hom (e.hom.hom.naturality h) _).symm.trans ?_
        refine congrArg (e.hom.hom.app V').hom ?_
        refine (ConcreteCategory.congr_hom
          ((spacesEtaleModelStructureSheaf B S hS X).obj.map_comp _ _) x).symm.trans ?_
        exact congrArg (fun k => ((spacesEtaleModelStructureSheaf B S hS X).obj.map k).hom x)
          (Quiver.Hom.unop_inj (hT.hom_ext _ _))⟩
      map_one' := Subtype.ext (funext fun V =>
        (congrArg (e.hom.hom.app V).hom (RingHom.map_one _)).trans (RingHom.map_one _))
      map_mul' x y := Subtype.ext (funext fun V =>
        (congrArg (e.hom.hom.app V).hom (RingHom.map_mul _ x y)).trans (RingHom.map_mul _ _ _))
      map_zero' := Subtype.ext (funext fun V =>
        (congrArg (e.hom.hom.app V).hom (RingHom.map_zero _)).trans (RingHom.map_zero _))
      map_add' x y := Subtype.ext (funext fun V =>
        (congrArg (e.hom.hom.app V).hom (RingHom.map_add _ x y)).trans (RingHom.map_add _ _ _)) }
  haveI := Functor.IsDenseSubsite.isCoverDense (smallEtaleModelTopology B S hS X.1)
    (smallModelTopology B S hS X) (spacesEtaleModelComparison B S hS X)
  haveI := Functor.IsDenseSubsite.isLocallyFull (smallEtaleModelTopology B S hS X.1)
    (smallModelTopology B S hS X) (spacesEtaleModelComparison B S hS X)
  have hb := Functor.IsCoverDense.bijective_terminalSectionsRestrict
    (spacesEtaleModelComparison B S hS X) (smallModelTopology B S hS X)
    ((sheafCompose _ (forget CommRingCat.{u})).obj (spacesEtaleModelStructureSheaf B S hS X)) hT
  let ei : ∀ V, _ ≃+* _ := fun V =>
    (((sheafToPresheaf _ _).mapIso e).app V).commRingCatIsoToRingEquiv
  refine RingEquiv.ofBijective g ⟨fun x y h => hb.1 (Subtype.ext (funext fun V =>
    (ei V).injective (congrFun (congrArg Subtype.val h) V))), fun s => ?_⟩
  obtain ⟨x, hx⟩ := hb.2 ⟨fun V => (ei V).symm (s.val V), fun {V V'} k => by
    apply (ei V').injective
    refine ((ConcreteCategory.congr_hom (e.hom.hom.naturality k) _).trans ?_).trans
      ((ei V').apply_symm_apply _).symm
    refine (congrArg ((smallEtaleModelStructureSheaf B S hS X).obj.map k).hom
      ((ei V).apply_symm_apply _)).trans ?_
    exact s.property k⟩
  exact ⟨x, Subtype.ext (funext fun V =>
    (congrArg (ei V) (congrFun (congrArg Subtype.val hx) V)).trans ((ei V).apply_symm_apply _))⟩

end AlgebraicGeometry.Space

end
