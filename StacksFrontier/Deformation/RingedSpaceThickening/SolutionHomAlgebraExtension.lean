module

public import StacksFrontier.Deformation.RingedSpaceThickening.SolutionAlgebraExtensionBridge

/-!
# Morphisms of solutions as maps of square-zero extensions

Let `Q₁` and `Q₂` be two solutions of the deformation problem of **Stacks 08U7** for
`t : S ⟶ S'`, `f : X ⟶ S`, `𝒢` and `c`. Each of them is read as a square-zero extension
`Qⱼ.toAlgebraExtension` of `(f ∘ t)⁻¹𝒪_{S'}`-algebras on the opens of `X`
(`StacksFrontier/Deformation/RingedSpaceThickening/SolutionAlgebraExtensionBridge.lean`). This file
shows that a morphism of solutions `Q₂ ⟶ Q₁` is the same as a map of these extensions compatible
with the algebra structures, the reductions and the identifications of the ideals with `𝒢`.

## Main definitions

* `AlgebraicGeometry.RingedSpaceThickening.DeformationSolution.toSpace` and
  `AlgebraicGeometry.RingedSpaceThickening.DeformationSolution.fromSpace`: the two mutually
  inverse isomorphisms between the deformed space `X'` of a solution and the ringed space
  `(X, 𝒪_{X'})` of its extension.
* `AlgebraicGeometry.RingedSpaceThickening.AlgebraSquareZeroExtension.spaceHom`: the morphism of
  ringed spaces `(X, 𝒪_{X'₂}) ⟶ (X, 𝒪_{X'₁})` attached to a map `𝒪_{X'₁} ⟶ 𝒪_{X'₂}` of extensions.
* `AlgebraicGeometry.RingedSpaceThickening.DeformationSolution.solutionHomOfExtensionHom`: the
  morphism of solutions attached to a compatible map of extensions.
* `AlgebraicGeometry.RingedSpaceThickening.SolutionHom.extensionHom`: the map of extensions
  attached to a morphism of solutions.

## Main results

* `AlgebraicGeometry.RingedSpaceThickening.SolutionHom.exists_extensionHom`: a morphism of
  solutions gives a compatible map of extensions.
* `AlgebraicGeometry.RingedSpaceThickening.DeformationSolution.nonempty_solutionHom_iff`: a
  morphism of solutions `Q₂ ⟶ Q₁` exists if and only if there is a map
  `Q₁.toAlgebraExtension ⟶ Q₂.toAlgebraExtension` compatible with the algebra structures, the
  reductions and the identifications of the ideals with `𝒢`.

## Implementation notes

The deformed space `X'` of a solution is isomorphic, by the homeomorphism underlying its
thickening, to `(X, 𝒪_{X'})`, the ringed space of its extension
(`AlgebraSquareZeroExtension.space`). Under these isomorphisms the thickening, the morphism to
`S'` and the ideal of a solution become the reduction, the algebra structure and the ideal of the
extension, so a morphism of solutions is a morphism of ringed spaces over `X` and under `S'`
between the spaces of the two extensions, the identity on underlying spaces.

## References

* [Stacks Project, Tag 08U7](https://stacks.math.columbia.edu/tag/08U7)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.Sites.Conormal (IdealRestriction kernelIdeal kernelIdeal_le_comap hom_of_comp_eq)

universe u

namespace AlgebraicGeometry.RingedSpaceThickening

/-! ### The morphism of ringed spaces attached to a map of extensions -/

/-- Two morphisms of ringed spaces are equal when they have the same base map and their
comorphisms agree on every open, up to the restriction along the equality of preimages. -/
private theorem ringedSpace_hom_ext_app {Y Z : RingedSpace.{u, u}} {a b : Y ⟶ Z}
    (w : a.hom.base = b.hom.base)
    (h : ∀ V, a.hom.c.app V ≫ Y.presheaf.map
      (eqToHom (congrArg (fun g => op ((Opens.map g).obj V.unop)) w)) = b.hom.c.app V) :
    a = b :=
  SheafedSpace.ext _ _ w (NatTrans.ext (funext fun V => by
    rw [NatTrans.comp_app, Functor.whiskerRight_app, eqToHom_app]
    exact h V))

namespace AlgebraSquareZeroExtension

variable {X S S' : RingedSpace.{u, u}} {t : S ⟶ S'} {f : X ⟶ S}
  {G : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
    (J := Opens.grothendieckTopology X.carrier) X.sheaf)}
  {P₁ P₂ : AlgebraSquareZeroExtension (f ≫ t) G} (θ : P₁.sheaf ⟶ P₂.sheaf)

/-- The morphism of ringed spaces `(X, 𝒪_{X'₂}) ⟶ (X, 𝒪_{X'₁})` attached to a map
`θ : 𝒪_{X'₁} ⟶ 𝒪_{X'₂}`: the identity on the space, and `θ` on structure sheaves. -/
def spaceHom : P₂.space ⟶ P₁.space :=
  ⟨{ base := 𝟙 X.carrier, c := θ.hom }⟩

/-- The morphism attached to a map compatible with the reductions is a morphism under `X`. -/
theorem thickening_comp_spaceHom (hred : θ ≫ P₂.reduction = P₁.reduction) :
    P₂.thickening ≫ spaceHom θ = P₁.thickening := by
  have h := congrArg (fun k => k.hom) hred
  refine ringedSpace_hom_ext_app (Category.id_comp _) fun V => ?_
  rw [eqToHom_map]
  have hV := congrArg (fun k => k.app V) h
  exact (congrArg (· ≫ _) hV).trans (Category.comp_id _)

/-- The morphism attached to a map compatible with the algebra structures is a morphism
over `S'`. -/
theorem spaceHom_comp_over (hbase : P₁.base ≫ θ = P₂.base) :
    spaceHom θ ≫ P₁.over = P₂.over := by
  have h : P₁.adjointBase ≫ (TopCat.Sheaf.pushforward CommRingCat.{u} (f ≫ t).hom.base).map θ =
      P₂.adjointBase :=
    ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u}
      (f ≫ t).hom.base).homEquiv_naturality_right P₁.base θ).symm.trans
        (congrArg ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u}
          (f ≫ t).hom.base).homEquiv _ _) hbase)
  refine ringedSpace_hom_ext_app (Category.id_comp _) fun V => ?_
  rw [eqToHom_map]
  have hV := congrArg (fun k => k.hom.app V) h
  exact (congrArg (· ≫ _) hV).trans (Category.comp_id _)

end AlgebraSquareZeroExtension

/-! ### The deformed space of a solution and the space of its extension -/

namespace DeformationSolution

variable {X S S' : RingedSpace.{u, u}} {t : S ⟶ S'} {ht : IsFirstOrderThickening t}
  {f : X ⟶ S} {G : SheafOfModules.{u} (structureSheafRing X)}
  {c : (modulePullback f).obj
    ((modulePullback t).obj (AlgebraicGeometry.SheafOfModules.idealSheaf t)) ⟶ G}
  (Q : DeformationSolution t ht f G c)

/-- The deformed space `X'` of a solution maps to the space `(X, 𝒪_{X'})` of its extension by
the inverse of the homeomorphism underlying the thickening; on structure sheaves this is the
identity, the structure sheaf of the target being the pushforward of `𝒪_{X'}`. -/
def toSpace : Q.X' ⟶ Q.toAlgebraExtension.space :=
  ⟨{ base := Q.baseIso.inv, c := 𝟙 _ }⟩

/-- Restricting along a morphism of a preorder and back is the identity. -/
theorem functor_map_comp_map_eq_id {C : Type*} [Preorder C] {D : Type*} [Category D]
    (F : Cᵒᵖ ⥤ D) {A B : Cᵒᵖ} (a : A ⟶ B) (b : B ⟶ A) : F.map a ≫ F.map b = 𝟙 _ :=
  (F.map_comp a b).symm.trans ((congrArg F.map (Subsingleton.elim _ (𝟙 A))).trans (F.map_id A))

/-- Restricting along an open and back is the identity of the sections. -/
theorem presheaf_map_comp_map_eq_id {Y : RingedSpace.{u, u}} {A B : (Opens Y.carrier)ᵒᵖ}
    (a : A ⟶ B) (b : B ⟶ A) : Y.presheaf.map a ≫ Y.presheaf.map b = 𝟙 _ :=
  functor_map_comp_map_eq_id Y.presheaf a b

/-- The comorphism of `fromSpace`: restriction of `𝒪_{X'}` along the round trip of opens. -/
def fromSpaceComorphism :
    Q.X'.presheaf ⟶ (TopCat.Presheaf.pushforward CommRingCat.{u} Q.baseIso.hom).obj
      Q.thickenedPresheaf where
  app W := Q.X'.presheaf.map (eqToHom (congrArg op (Q.opens_roundTrip' W.unop)).symm)
  naturality {_W _W'} _k :=
    (Q.X'.presheaf.map_comp _ _).symm.trans
      ((congrArg Q.X'.presheaf.map (Subsingleton.elim _ _)).trans (Q.X'.presheaf.map_comp _ _))

/-- The space `(X, 𝒪_{X'})` of the extension of a solution maps to its deformed space `X'` by the
homeomorphism underlying the thickening. -/
def fromSpace : Q.toAlgebraExtension.space ⟶ Q.X' :=
  ⟨{ base := Q.baseIso.hom, c := Q.fromSpaceComorphism }⟩

/-- The component of `fromSpaceComorphism` at an open `W` of `X'` is the restriction of `𝒪_{X'}`
along the equality of `W` with its round trip. -/
theorem fromSpaceComorphism_app (W : (Opens Q.X'.carrier)ᵒᵖ) :
    Q.fromSpaceComorphism.app W =
      Q.X'.presheaf.map (eqToHom (congrArg op (Q.opens_roundTrip' W.unop)).symm) :=
  rfl

/-- `toSpace` followed by `fromSpace` is the identity of `X'`. -/
theorem toSpace_fromSpace : Q.toSpace ≫ Q.fromSpace = 𝟙 Q.X' := by
  refine ringedSpace_hom_ext_app Q.baseIso.inv_hom_id fun W => ?_
  exact (congrArg (· ≫ _) (Category.comp_id _)).trans (presheaf_map_comp_map_eq_id _ _)

/-- `fromSpace` followed by `toSpace` is the identity of `(X, 𝒪_{X'})`. -/
theorem fromSpace_toSpace : Q.fromSpace ≫ Q.toSpace = 𝟙 Q.toAlgebraExtension.space := by
  refine ringedSpace_hom_ext_app Q.baseIso.hom_inv_id fun V => ?_
  exact (congrArg (· ≫ _) (Category.id_comp _)).trans (presheaf_map_comp_map_eq_id _ _)

/-- The thickening of a solution followed by `toSpace` is the thickening of its extension. -/
theorem i_comp_toSpace : Q.i ≫ Q.toSpace = Q.toAlgebraExtension.thickening := by
  refine ringedSpace_hom_ext_app Q.baseIso.hom_inv_id fun U => ?_
  exact (congrArg (· ≫ _) (Category.id_comp _)).trans
    (congrArg (Q.i.hom.c.app _ ≫ ·) ((congrArg X.presheaf.map (Subsingleton.elim _ _)).trans
      (Q.pushforwardRoundTrip_hom_app U).symm))

/-- `toSpace` followed by the morphism of the extension to `S'` is the morphism `f'` of the
solution. -/
theorem toSpace_comp_over : Q.toSpace ≫ Q.toAlgebraExtension.over = Q.f' := by
  have hadj : Q.toAlgebraExtension.adjointBase = Q.deformedBaseSheafMap :=
    Q.adjoint_thickenedSheafBase
  refine ringedSpace_hom_ext_app Q.baseIso_inv_comp_base fun V => ?_
  refine (congrArg (fun k => (k.hom.app V ≫ 𝟙 _) ≫ Q.X'.presheaf.map _) hadj).trans ?_
  exact (congrArg (· ≫ _) (Category.comp_id _)).trans ((Category.assoc _ _ _).trans
    ((congrArg (Q.f'.hom.c.app V ≫ ·) (presheaf_map_comp_map_eq_id _ _)).trans
      (Category.comp_id _)))

end DeformationSolution

/-! ### A compatible map of extensions gives a morphism of solutions -/

namespace DeformationSolution

variable {X S S' : RingedSpace.{u, u}} {t : S ⟶ S'} {ht : IsFirstOrderThickening t}
  {f : X ⟶ S} {G : SheafOfModules.{u} (structureSheafRing X)}
  {c : (modulePullback f).obj
    ((modulePullback t).obj (AlgebraicGeometry.SheafOfModules.idealSheaf t)) ⟶ G}
  {Q₁ Q₂ : DeformationSolution t ht f G c}
  (θ : Q₁.toAlgebraExtension.sheaf ⟶ Q₂.toAlgebraExtension.sheaf)

/-- The morphism `X'₂ ⟶ X'₁` of deformed spaces attached to a map `𝒪_{X'₁} ⟶ 𝒪_{X'₂}` of the
extensions of two solutions, read on the opens of `X`. -/
def extensionHomSpace : Q₂.X' ⟶ Q₁.X' :=
  Q₂.toSpace ≫ AlgebraSquareZeroExtension.spaceHom θ ≫ Q₁.fromSpace

/-- The morphism attached to a map compatible with the reductions is a morphism under `X`. -/
theorem i_comp_extensionHomSpace
    (hred : θ ≫ Q₂.toAlgebraExtension.reduction = Q₁.toAlgebraExtension.reduction) :
    Q₂.i ≫ extensionHomSpace θ = Q₁.i := by
  rw [extensionHomSpace, ← Category.assoc, i_comp_toSpace, ← Category.assoc,
    AlgebraSquareZeroExtension.thickening_comp_spaceHom θ hred, ← i_comp_toSpace,
    Category.assoc, toSpace_fromSpace, Category.comp_id]

/-- The morphism attached to a map compatible with the algebra structures is a morphism
over `S'`. -/
theorem extensionHomSpace_comp_f'
    (hbase : Q₁.toAlgebraExtension.base ≫ θ = Q₂.toAlgebraExtension.base) :
    extensionHomSpace θ ≫ Q₁.f' = Q₂.f' := by
  rw [← toSpace_comp_over Q₁, ← toSpace_comp_over Q₂, extensionHomSpace, Category.assoc,
    Category.assoc, ← Category.assoc Q₁.fromSpace, fromSpace_toSpace, Category.id_comp,
    AlgebraSquareZeroExtension.spaceHom_comp_over θ hbase]

/-- On sections, the comparison `(Q₁.i)_* 𝒢 ≅ φ_* (Q₂.i)_* 𝒢` of a morphism `φ` under `X` is
restriction along the equality of opens given by `Q₂.i ≫ φ = Q₁.i`. -/
theorem pushforwardIsoOfComp_hom_app_val_app {φ : Q₂.X' ⟶ Q₁.X'} (h : Q₂.i ≫ φ = Q₁.i)
    (W : (Opens Q₁.X'.carrier)ᵒᵖ) (u : ((modulePushforward Q₁.i).obj G).val.obj W) :
    (((pushforwardIsoOfComp Q₂.i φ Q₁.i h).hom.app G).val.app W).hom u =
      G.val.map (eqToHom (by rw [← h]; rfl) : op ((Opens.map Q₁.i.hom.base).obj W.unop) ⟶
        op ((Opens.map Q₂.i.hom.base).obj ((Opens.map φ.hom.base).obj W.unop))) u := by
  have e : (pushforwardIsoOfComp Q₂.i φ Q₁.i h).hom.app G =
      eqToHom (congrArg (fun m => (modulePushforward m).obj G) h.symm) := by
    simp only [pushforwardIsoOfComp, Iso.trans_hom, NatTrans.comp_app,
      modulePushforwardCompSymm, Iso.symm_hom, modulePushforwardComp_inv_app, eqToIso.hom,
      eqToHom_app]
    exact Category.comp_id _
  rw [e]
  exact pushforward_eqToHom_val_app h.symm G W u

/-- The comorphism of `extensionHomSpace θ`, on sections: restriction along the round trip of
opens, followed by `θ`. -/
theorem extensionHomSpace_c_app (W : (Opens Q₁.X'.carrier)ᵒᵖ) (x : Q₁.X'.presheaf.obj W) :
    ((extensionHomSpace θ).hom.c.app W).hom x =
      (θ.hom.app (op ((Opens.map Q₁.baseIso.hom).obj W.unop))).hom
        ((Q₁.X'.presheaf.map
          (eqToHom (congrArg op (Q₁.opens_roundTrip' W.unop)).symm)).hom x) :=
  rfl

/-- A section of the prescribed module over the open of `X` matching an open of `X'`, included
into `𝒪_{X'}` and restricted along the round trip of opens, lies in the ideal of the extension. -/
theorem incl_mem_kernelIdeal (Q : DeformationSolution t ht f G c) {U : (Opens X.carrier)ᵒᵖ}
    (g : ((modulePushforward Q.i).obj G).val.obj ((Opens.map Q.baseIso.inv).op.obj U)) :
    Q.incl g ∈ kernelIdeal Q.thickenedSheafReduction.hom U := by
  change (Q.thickenedReduction.app U).hom (Q.incl g) = 0
  rw [thickenedReduction_app]
  exact (congrArg _ (Q.reduction_incl g)).trans (map_zero _)

/-- A map of extensions compatible with the reductions and the ideals carries the inclusion of a
section of `𝒢` into `𝒪_{X'₁}` to its inclusion into `𝒪_{X'₂}`, on the opens of `X`. -/
theorem θ_incl
    (hred : θ ≫ Q₂.toAlgebraExtension.reduction = Q₁.toAlgebraExtension.reduction)
    (hideal : ∀ (V : (Opens X.carrier)ᵒᵖ)
      (y : ↥(kernelIdeal Q₁.toAlgebraExtension.reduction.hom V)),
      Q₂.toAlgebraExtension.ideal.app V ⟨θ.hom.app V y, kernelIdeal_le_comap
        Q₁.toAlgebraExtension.reduction.hom _ θ.hom (hom_of_comp_eq hred) V y.2⟩ =
        Q₁.toAlgebraExtension.ideal.app V y)
    (V : (Opens X.carrier)ᵒᵖ)
    (g : ((modulePushforward Q₁.i).obj G).val.obj ((Opens.map Q₁.baseIso.inv).op.obj V))
    (r : V ⟶ (Opens.map Q₂.i.hom.base).op.obj ((Opens.map Q₂.baseIso.inv).op.obj V)) :
    (θ.hom.app V).hom (Q₁.incl g) = Q₂.incl (G.val.map r (Q₁.descendSection g)) := by
  set y : ↥(kernelIdeal Q₁.toAlgebraExtension.reduction.hom V) :=
    ⟨Q₁.incl g, Q₁.incl_mem_kernelIdeal g⟩
  have h₁ : Q₁.toAlgebraExtension.ideal.app V y = Q₁.descendSection g :=
    congrArg Q₁.descendSection (Q₁.kernelSection_eq y g rfl)
  have h₂ := (hideal V y).trans h₁
  set z : ↥(kernelIdeal Q₂.thickenedSheafReduction.hom V) := ⟨θ.hom.app V y, _⟩
  have h₃ : G.val.map (Q₂.roundTripHom V) (Q₂.kernelSection z) = Q₁.descendSection g := h₂
  have h₄ : Q₂.kernelSection z = G.val.map r (Q₁.descendSection g) := by
    rw [← h₃]
    exact ((map_map_eq_map G (Q₂.roundTripHom V) r (𝟙 _) (Q₂.kernelSection z)).trans
      (map_self_eq G _ _)).symm
  exact (Q₂.incl_kernelSection z).symm.trans (congrArg Q₂.incl h₄)

variable (hred : θ ≫ Q₂.toAlgebraExtension.reduction = Q₁.toAlgebraExtension.reduction)
  (hideal : ∀ (V : (Opens X.carrier)ᵒᵖ) (y : ↥(kernelIdeal Q₁.toAlgebraExtension.reduction.hom V)),
      Q₂.toAlgebraExtension.ideal.app V ⟨θ.hom.app V y, kernelIdeal_le_comap
        Q₁.toAlgebraExtension.reduction.hom _ θ.hom (hom_of_comp_eq hred) V y.2⟩ =
        Q₁.toAlgebraExtension.ideal.app V y)

/-- The left-hand side of the ideal condition, on a section. -/
private theorem kernel_comm_lhs (W : (Opens Q₁.X'.carrier)ᵒᵖ)
    (u : ((modulePushforward Q₁.i).obj G).val.obj W) :
    ((Q₁.idealInclusion ≫ SheafOfModules.unitToPushforwardObjUnit
        (structureSheafHom (extensionHomSpace θ))).val.app W).hom u =
      ((extensionHomSpace θ).hom.c.app W).hom (Q₁.incl u) :=
  rfl

/-- The right-hand side of the ideal condition, on a section. -/
private theorem kernel_comm_rhs (W : (Opens Q₁.X'.carrier)ᵒᵖ)
    (u : ((modulePushforward Q₁.i).obj G).val.obj W) :
    (((pushforwardIsoOfComp Q₂.i (extensionHomSpace θ) Q₁.i
        (i_comp_extensionHomSpace θ hred)).hom.app G ≫
        (modulePushforward (extensionHomSpace θ)).map Q₂.idealInclusion).val.app W).hom u =
      Q₂.incl ((((pushforwardIsoOfComp Q₂.i (extensionHomSpace θ) Q₁.i
        (i_comp_extensionHomSpace θ hred)).hom.app G).val.app W).hom u) :=
  rfl

include hideal in
/-- The morphism attached to a map compatible with the reductions and the ideals is the identity
on the prescribed ideal. -/
theorem extensionHomSpace_kernel_comm :
    Q₁.idealInclusion ≫ SheafOfModules.unitToPushforwardObjUnit
        (structureSheafHom (extensionHomSpace θ)) =
      (pushforwardIsoOfComp Q₂.i (extensionHomSpace θ) Q₁.i
          (i_comp_extensionHomSpace θ hred)).hom.app G ≫
        (modulePushforward (extensionHomSpace θ)).map Q₂.idealInclusion := by
  ext W u
  refine (kernel_comm_lhs θ W u).trans (Eq.trans ?_ (kernel_comm_rhs θ hred W u).symm)
  refine Eq.trans ?_ (congrArg Q₂.incl
    (pushforwardIsoOfComp_hom_app_val_app (i_comp_extensionHomSpace θ hred) W u).symm)
  refine (extensionHomSpace_c_app θ W _).trans ?_
  refine (congrArg (θ.hom.app _).hom (Q₁.incl_naturality _ u).symm).trans ?_
  refine (θ_incl θ hred hideal _ _ (eqToHom (congrArg op (Q₂.opens_roundTrip _).symm))).trans
    (congrArg Q₂.incl ?_)
  refine congrArg (G.val.map _) ?_
  exact (map_map_eq_map G ((Opens.map Q₁.i.hom.base).op.map
    (eqToHom (congrArg op (Q₁.opens_roundTrip' W.unop)).symm))
      (Q₁.roundTripHom (op ((Opens.map Q₁.baseIso.hom).obj W.unop))) (𝟙 _) u).trans
    (map_self_eq G _ u)

/-- **The morphism of solutions attached to a compatible map of extensions.** A map
`θ : 𝒪_{X'₁} ⟶ 𝒪_{X'₂}` of the extensions of two solutions, compatible with the algebra
structures, the reductions and the identifications of the ideals with `𝒢`, gives a morphism of
solutions `Q₂ ⟶ Q₁`. -/
def solutionHomOfExtensionHom
    (hbase : Q₁.toAlgebraExtension.base ≫ θ = Q₂.toAlgebraExtension.base) :
    SolutionHom Q₂ Q₁ where
  hom := extensionHomSpace θ
  thickening_comm := i_comp_extensionHomSpace θ hred
  base_comm := extensionHomSpace_comp_f' θ hbase
  kernel_comm := extensionHomSpace_kernel_comm θ hred hideal

end DeformationSolution

/-! ### A morphism of solutions gives a compatible map of extensions -/

namespace SolutionHom

variable {X S S' : RingedSpace.{u, u}} {t : S ⟶ S'} {ht : IsFirstOrderThickening t}
  {f : X ⟶ S} {G : SheafOfModules.{u} (structureSheafRing X)}
  {c : (modulePullback f).obj
    ((modulePullback t).obj (AlgebraicGeometry.SheafOfModules.idealSheaf t)) ⟶ G}
  {Q₁ Q₂ : DeformationSolution t ht f G c} (e : SolutionHom Q₂ Q₁)

/-- The ideal condition of a morphism of solutions, on sections: the comorphism carries the
inclusion of a section of `𝒢` into `𝒪_{X'₁}` to its inclusion into `𝒪_{X'₂}`. -/
theorem c_app_incl (W : (Opens Q₁.X'.carrier)ᵒᵖ)
    (u : ((modulePushforward Q₁.i).obj G).val.obj W) :
    (e.hom.hom.c.app W).hom (Q₁.incl u) =
      Q₂.incl (G.val.map (eqToHom (by rw [← e.thickening_comm]; rfl) :
        op ((Opens.map Q₁.i.hom.base).obj W.unop) ⟶
          op ((Opens.map Q₂.i.hom.base).obj ((Opens.map e.hom.hom.base).obj W.unop))) u) :=
  (congrArg (fun k : (modulePushforward Q₁.i).obj G ⟶
      (modulePushforward e.hom).obj (SheafOfModules.unit (structureSheafRing Q₂.X')) =>
    (k.val.app W).hom u) e.kernel_comm).trans
    (congrArg Q₂.incl (DeformationSolution.pushforwardIsoOfComp_hom_app_val_app
      e.thickening_comm W u))

/-- The morphism `(X, 𝒪_{X'₂}) ⟶ (X, 𝒪_{X'₁})` of the spaces of the two extensions attached to a
morphism of solutions. -/
def spaceMap : Q₂.toAlgebraExtension.space ⟶ Q₁.toAlgebraExtension.space :=
  Q₂.fromSpace ≫ e.hom ≫ Q₁.toSpace

/-- The morphism of spaces of extensions is the identity on the underlying space. -/
theorem spaceMap_base : e.spaceMap.hom.base = 𝟙 X.carrier := by
  have h : Q₂.baseIso.hom ≫ e.hom.hom.base = Q₁.baseIso.hom :=
    congrArg (fun k : X ⟶ Q₁.X' => k.hom.base) e.thickening_comm
  change Q₂.baseIso.hom ≫ e.hom.hom.base ≫ Q₁.baseIso.inv = 𝟙 X.carrier
  rw [← Category.assoc, h, Iso.hom_inv_id]

/-- The morphism of spaces of extensions is a morphism under `X`. -/
theorem thickening_comp_spaceMap :
    Q₂.toAlgebraExtension.thickening ≫ e.spaceMap = Q₁.toAlgebraExtension.thickening := by
  rw [spaceMap, ← DeformationSolution.i_comp_toSpace, ← DeformationSolution.i_comp_toSpace,
    Category.assoc, ← Category.assoc Q₂.toSpace, DeformationSolution.toSpace_fromSpace,
    Category.id_comp, ← Category.assoc, e.thickening_comm]

/-- The morphism of spaces of extensions is a morphism over `S'`. -/
theorem spaceMap_comp_over :
    e.spaceMap ≫ Q₁.toAlgebraExtension.over = Q₂.toAlgebraExtension.over := by
  rw [spaceMap, Category.assoc, Category.assoc, DeformationSolution.toSpace_comp_over,
    e.base_comm, ← DeformationSolution.toSpace_comp_over Q₂, ← Category.assoc,
    DeformationSolution.fromSpace_toSpace, Category.id_comp]

/-- The morphism of spaces of extensions moves no open set. -/
theorem spaceMap_opens (V : Opens X.carrier) : (Opens.map e.spaceMap.hom.base).obj V = V := by
  rw [spaceMap_base]
  rfl

/-- The comorphism of the morphism of spaces of extensions, followed by the identification of the
preimage of an open with the open itself. -/
def extensionHomApp (V : (Opens X.carrier)ᵒᵖ) :
    Q₁.thickenedPresheaf.obj V ⟶ Q₂.thickenedPresheaf.obj V :=
  e.spaceMap.hom.c.app V ≫
    Q₂.thickenedPresheaf.map (eqToHom (congrArg op (e.spaceMap_opens V.unop)))

/-- The map `𝒪_{X'₁} ⟶ 𝒪_{X'₂}` of extensions attached to a morphism of solutions: the
comorphism of the morphism of spaces of extensions. -/
def extensionHom : Q₁.toAlgebraExtension.sheaf ⟶ Q₂.toAlgebraExtension.sheaf :=
  ObjectProperty.homMk
    { app := e.extensionHomApp
      naturality := fun {V _W} k =>
        (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) (e.spaceMap.hom.c.naturality k)).trans
          ((Category.assoc _ _ _).trans ((congrArg (e.spaceMap.hom.c.app V ≫ ·)
            ((Q₂.thickenedPresheaf.map_comp _ _).symm.trans
              ((congrArg Q₂.thickenedPresheaf.map (Subsingleton.elim _ _)).trans
                (Q₂.thickenedPresheaf.map_comp _ _)))).trans (Category.assoc _ _ _).symm))) }

/-- The component of `extensionHom` at an open `V` is `extensionHomApp V`. -/
theorem extensionHom_app (V : (Opens X.carrier)ᵒᵖ) :
    e.extensionHom.hom.app V = e.extensionHomApp V :=
  rfl

/-- The map of extensions attached to a morphism of solutions is compatible with the
reductions. -/
theorem extensionHom_comp_reduction :
    e.extensionHom ≫ Q₂.toAlgebraExtension.reduction = Q₁.toAlgebraExtension.reduction := by
  refine ObjectProperty.hom_ext _ (NatTrans.ext (funext fun V => ?_))
  have hc := SheafedSpace.congr_hom_app e.thickening_comp_spaceMap V
  exact (Category.assoc _ _ _).trans ((congrArg (e.spaceMap.hom.c.app V ≫ ·)
    (Q₂.toAlgebraExtension.reduction.hom.naturality _)).trans ((Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ _) hc).trans ((Category.assoc _ _ _).trans
        ((congrArg (_ ≫ ·) (DeformationSolution.functor_map_comp_map_eq_id X.presheaf _ _)).trans
          (Category.comp_id _))))))

/-- The map of extensions attached to a morphism of solutions is compatible with the algebra
structures. -/
theorem base_comp_extensionHom :
    Q₁.toAlgebraExtension.base ≫ e.extensionHom = Q₂.toAlgebraExtension.base := by
  refine ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u}
    (f ≫ t).hom.base).homEquiv _ _).injective ?_
  refine ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u}
    (f ≫ t).hom.base).homEquiv_naturality_right _ _).trans ?_
  refine ObjectProperty.hom_ext _ (NatTrans.ext (funext fun V => ?_))
  have hc := SheafedSpace.congr_hom_app e.spaceMap_comp_over V
  exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) hc).trans
    ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·)
      (DeformationSolution.functor_map_comp_map_eq_id Q₂.thickenedPresheaf _ _)).trans
        (Category.comp_id _))))

/-- The comorphism of the morphism of spaces of extensions, on sections. -/
theorem extensionHom_app_apply (V : (Opens X.carrier)ᵒᵖ)
    (x : Q₁.thickenedPresheaf.obj V) :
    (e.extensionHom.hom.app V).hom x =
      (Q₂.thickenedPresheaf.map (eqToHom (congrArg op (e.spaceMap_opens V.unop)))).hom
        ((Q₂.X'.presheaf.map (eqToHom (congrArg op
          (Q₂.opens_roundTrip' ((Opens.map e.hom.hom.base).obj
            ((Opens.map Q₁.baseIso.inv).obj V.unop)))).symm)).hom
          ((e.hom.hom.c.app (op ((Opens.map Q₁.baseIso.inv).obj V.unop))).hom x)) :=
  rfl

/-- Four restrictions of `𝒢` in a row are one restriction. -/
theorem map_four {A B C' D' E : (Opens X.carrier)ᵒᵖ} (k₁ : A ⟶ B) (k₂ : B ⟶ C') (k₃ : C' ⟶ D')
    (k₄ : D' ⟶ E) (k : A ⟶ E) (x : G.val.obj A) :
    G.val.map k₄ (G.val.map k₃ (G.val.map k₂ (G.val.map k₁ x))) = G.val.map k x := by
  rw [map_map_eq_map G k₁ k₂ (k₁ ≫ k₂), map_map_eq_map G _ k₃ (k₁ ≫ k₂ ≫ k₃),
    map_map_eq_map G _ k₄ k]

/-- The map of extensions attached to a morphism of solutions is compatible with the
identifications of the ideals with `𝒢`. -/
theorem extensionHom_ideal (V : (Opens X.carrier)ᵒᵖ)
    (y : ↥(kernelIdeal Q₁.toAlgebraExtension.reduction.hom V)) :
    Q₂.toAlgebraExtension.ideal.app V ⟨e.extensionHom.hom.app V y, kernelIdeal_le_comap
        Q₁.toAlgebraExtension.reduction.hom _ e.extensionHom.hom
        (hom_of_comp_eq e.extensionHom_comp_reduction) V y.2⟩ =
      Q₁.toAlgebraExtension.ideal.app V y := by
  set g := Q₁.kernelSection y
  have hy : (e.extensionHom.hom.app V).hom y.1 = Q₂.incl
      (((modulePushforward Q₂.i).obj G).val.map ((Opens.map Q₂.baseIso.inv).op.map
        (eqToHom (congrArg op (e.spaceMap_opens V.unop))))
        (((modulePushforward Q₂.i).obj G).val.map (eqToHom (congrArg op
          (Q₂.opens_roundTrip' ((Opens.map e.hom.hom.base).obj
            ((Opens.map Q₁.baseIso.inv).obj V.unop)))).symm)
          (G.val.map (eqToHom (by rw [← e.thickening_comm]; rfl) :
            op ((Opens.map Q₁.i.hom.base).obj ((Opens.map Q₁.baseIso.inv).obj V.unop)) ⟶
              op ((Opens.map Q₂.i.hom.base).obj ((Opens.map e.hom.hom.base).obj
                ((Opens.map Q₁.baseIso.inv).obj V.unop)))) g))) := by
    refine (e.extensionHom_app_apply V y.1).trans ?_
    refine (congrArg (fun z => (Q₂.thickenedPresheaf.map
      (eqToHom (congrArg op (e.spaceMap_opens V.unop)))).hom ((Q₂.X'.presheaf.map _).hom
        ((e.hom.hom.c.app (op ((Opens.map Q₁.baseIso.inv).obj V.unop))).hom z)))
          (Q₁.incl_kernelSection y).symm).trans ?_
    refine (congrArg (fun z => (Q₂.thickenedPresheaf.map
      (eqToHom (congrArg op (e.spaceMap_opens V.unop)))).hom ((Q₂.X'.presheaf.map _).hom z))
        (e.c_app_incl _ g)).trans ?_
    exact (congrArg _ (Q₂.incl_naturality _ _).symm).trans (Q₂.incl_naturality _ _).symm
  refine (congrArg Q₂.descendSection (Q₂.kernelSection_eq _ _ hy.symm)).trans ?_
  exact map_four _ _ _ _ (Q₁.roundTripHom V) g

include e in
/-- **A morphism of solutions gives a compatible map of extensions.** -/
theorem exists_extensionHom :
    ∃ (θ : Q₁.toAlgebraExtension.sheaf ⟶ Q₂.toAlgebraExtension.sheaf)
      (_ : Q₁.toAlgebraExtension.base ≫ θ = Q₂.toAlgebraExtension.base)
      (hred : θ ≫ Q₂.toAlgebraExtension.reduction = Q₁.toAlgebraExtension.reduction),
      ∀ (V : (Opens X.carrier)ᵒᵖ) (y : ↥(kernelIdeal Q₁.toAlgebraExtension.reduction.hom V)),
        Q₂.toAlgebraExtension.ideal.app V ⟨θ.hom.app V y, kernelIdeal_le_comap
          Q₁.toAlgebraExtension.reduction.hom _ θ.hom (hom_of_comp_eq hred) V y.2⟩ =
          Q₁.toAlgebraExtension.ideal.app V y :=
  ⟨e.extensionHom, e.base_comp_extensionHom, e.extensionHom_comp_reduction, e.extensionHom_ideal⟩

end SolutionHom

namespace DeformationSolution

variable {X S S' : RingedSpace.{u, u}} {t : S ⟶ S'} {ht : IsFirstOrderThickening t}
  {f : X ⟶ S} {G : SheafOfModules.{u} (structureSheafRing X)}
  {c : (modulePullback f).obj
    ((modulePullback t).obj (AlgebraicGeometry.SheafOfModules.idealSheaf t)) ⟶ G}

/-- **Morphisms of solutions are compatible maps of their extensions.** For two solutions `Q₁`
and `Q₂` of the deformation problem of Stacks 08U7, there is a morphism of solutions `Q₂ ⟶ Q₁`
if and only if there is a map `𝒪_{X'₁} ⟶ 𝒪_{X'₂}` of their extensions on the opens of `X`
compatible with the algebra structures, the reductions and the identifications of the ideals
with `𝒢`. -/
theorem nonempty_solutionHom_iff (Q₁ Q₂ : DeformationSolution t ht f G c) :
    Nonempty (SolutionHom Q₂ Q₁) ↔
      ∃ (θ : Q₁.toAlgebraExtension.sheaf ⟶ Q₂.toAlgebraExtension.sheaf)
        (_ : Q₁.toAlgebraExtension.base ≫ θ = Q₂.toAlgebraExtension.base)
        (hred : θ ≫ Q₂.toAlgebraExtension.reduction = Q₁.toAlgebraExtension.reduction),
        ∀ (V : (Opens X.carrier)ᵒᵖ) (y : ↥(kernelIdeal Q₁.toAlgebraExtension.reduction.hom V)),
          Q₂.toAlgebraExtension.ideal.app V ⟨θ.hom.app V y, kernelIdeal_le_comap
            Q₁.toAlgebraExtension.reduction.hom _ θ.hom (hom_of_comp_eq hred) V y.2⟩ =
            Q₁.toAlgebraExtension.ideal.app V y :=
  ⟨fun ⟨e⟩ => SolutionHom.exists_extensionHom e, fun ⟨θ, hbase, hred, hideal⟩ =>
    ⟨solutionHomOfExtensionHom θ hred hideal hbase⟩⟩

end DeformationSolution

end AlgebraicGeometry.RingedSpaceThickening

end
