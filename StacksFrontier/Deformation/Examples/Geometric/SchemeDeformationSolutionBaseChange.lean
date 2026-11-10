module

public import StacksFrontier.Deformation.RingedSpaceThickening.SolutionHomAlgebraExtension
public import StacksFrontier.Deformation.RingedSpaceThickening.SolutionBaseChangeUniversal
public import StacksFrontier.Deformation.RingedSpaceThickening.ThickeningBaseDescent
public import StacksFrontier.Deformation.Examples.Geometric.SchemeDeformationSolution
public import StacksFrontier.Deformation.Examples.Geometric.SchemeMorphismSixTermExactInterior

/-!
# Base change of the solution attached to a first-order deformation of a scheme

Let `X` be a scheme over a field `k`, let `g : V ⟶ W` be a map of finite-dimensional `k`-vector
spaces and `k[g] : k[V] ⟶ k[W]` the induced map of square-zero extensions. A deformation `x` of `X`
over `k[V]` and a deformation `y` over `k[W]` related by an arrow `a : x ⟶ y` over `k[g]` of the
deformation category of `X` are related by a cartesian square
`y.scheme ⟶ x.scheme` over `Spec k[W] ⟶ Spec k[V]`. This file shows that the solution of the
deformation problem of Stacks 08U7 attached to `y` is the base change, along
`Spec k[W] ⟶ Spec k[V]`, of the solution attached to `x`.

The ringed space part is general. For two solutions `Q₁` over `t₁ : S ⟶ S'₁` and `Q₂` over
`t₂ : S ⟶ S'₂` and a morphism `φ : X'₂ ⟶ X'₁` of the deformed spaces under `X` and over
`h' : S'₂ ⟶ S'₁`, the comorphism of `φ`, read on the opens of `X`, is a map
`𝒪_{X'₁} ⟶ 𝒪_{X'₂}` of the attached square-zero extensions compatible with the reductions and
with the algebra structures through `h'`; when the prescribed map `c₁` is invertible it induces on
the ideals the comparison `ν : 𝒢₁ ⟶ 𝒢₂` of the two prescribed maps.

## Main definitions

* `AlgebraicGeometry.RingedSpaceThickening.DeformationSolution.extensionHomOfMap`: the map of
  extensions attached to a morphism of deformed spaces under `X`.

## Main results

* `AlgebraicGeometry.RingedSpaceThickening.DeformationSolution.adjointBase_comp_extensionHomOfMap`:
  compatibility with the algebra structures through `h'`.
* `DeformationSolution.idealInclusion_comp_structureSheafModuleHom_of_map` (in
  `AlgebraicGeometry.RingedSpaceThickening`): on the ideals the comorphism of `φ` is `ν`.
* `AlgebraicGeometry.RingedSpaceThickening.DeformationSolution.extensionHomOfMap_ideal`: the same,
  read on the extensions.
* `Deformation.Examples.isomorphic_fiberSolution_baseChange`: the solution attached to `y` is the
  base change (`DeformationSolution.baseChange`) of the solution attached to `x`.

## Implementation notes

The final statement is the universal property
`AlgebraicGeometry.RingedSpaceThickening.DeformationSolution.isomorphic_baseChange_of_hom` of the
base change of a solution, applied to the map of extensions attached to the morphism `a.map` of
total spaces. The comparison of ideals is checked after the epimorphism `f'^*𝒥₁ ⟶ i_*𝒢₁` of
Stacks 08KZ, where it is the compatibility of `h'^♯` with the two base ideals.

## References

* [Stacks Project, Tag 08U7](https://stacks.math.columbia.edu/tag/08U7)
* [Stacks Project, Tag 0DY9](https://stacks.math.columbia.edu/tag/0DY9)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.Sites.Conormal (IdealRestriction kernelIdeal kernelIdeal_le_comap hom_of_comp_eq)

universe u

namespace AlgebraicGeometry.RingedSpaceThickening

/-- The structure-sheaf map of a morphism of ringed spaces depends on the morphism only through
an equality of morphisms, up to transport of the target. -/
theorem structureSheafModuleHom_eq_of_eq {Y Z : RingedSpace.{u, u}} {g₁ g₂ : Y ⟶ Z}
    (h : g₁ = g₂) :
    structureSheafModuleHom g₁ = structureSheafModuleHom g₂ ≫
      eqToHom (congrArg (fun g => (modulePushforward g).obj
        (SheafOfModules.unit (structureSheafRing Y))) h.symm) := by
  subst h
  simp

/-- The comparison `j_* ≅ b_* a_*` of a factorization `a ≫ b = j` is, at a sheaf of modules, the
transport along the factorization. -/
theorem pushforwardIsoOfComp_hom_app_eq {Y₁ Y₂ Y₃ : RingedSpace.{u, u}} (a : Y₁ ⟶ Y₂)
    (b : Y₂ ⟶ Y₃) (j : Y₁ ⟶ Y₃) (hj : a ≫ b = j) (M : SheafOfModules.{u} (structureSheafRing Y₁)) :
    (pushforwardIsoOfComp a b j hj).hom.app M =
      eqToHom (congrArg (fun m => (modulePushforward m).obj M) hj.symm) := by
  subst hj
  exact Category.comp_id _

namespace DeformationSolution

variable {X S S₁ S₂ : RingedSpace.{u, u}} {t₁ : S ⟶ S₁} {t₂ : S ⟶ S₂}
  {ht₁ : IsFirstOrderThickening t₁} {ht₂ : IsFirstOrderThickening t₂} {f : X ⟶ S}
  {G₁ G₂ : SheafOfModules.{u} (structureSheafRing X)}
  {c₁ : (modulePullback f).obj
    ((modulePullback t₁).obj (AlgebraicGeometry.SheafOfModules.idealSheaf t₁)) ⟶ G₁}
  {c₂ : (modulePullback f).obj
    ((modulePullback t₂).obj (AlgebraicGeometry.SheafOfModules.idealSheaf t₂)) ⟶ G₂}
  {Q₁ : DeformationSolution t₁ ht₁ f G₁ c₁} {Q₂ : DeformationSolution t₂ ht₂ f G₂ c₂}
  (φ : Q₂.X' ⟶ Q₁.X') (th : Q₂.i ≫ φ = Q₁.i)

/-! ### The map of extensions attached to a morphism of deformed spaces -/

/-- The morphism `(X, 𝒪_{X'₂}) ⟶ (X, 𝒪_{X'₁})` of the spaces of the two extensions attached to a
morphism `φ : X'₂ ⟶ X'₁` of deformed spaces. -/
def spaceMapOfMap : Q₂.toAlgebraExtension.space ⟶ Q₁.toAlgebraExtension.space :=
  Q₂.fromSpace ≫ φ ≫ Q₁.toSpace

include th in
/-- For `φ` under `X`, the morphism of spaces of extensions is the identity on the underlying
space. -/
theorem spaceMapOfMap_base : (spaceMapOfMap φ).hom.base = 𝟙 X.carrier := by
  have h : Q₂.baseIso.hom ≫ φ.hom.base = Q₁.baseIso.hom :=
    congrArg (fun k : X ⟶ Q₁.X' => k.hom.base) th
  change Q₂.baseIso.hom ≫ φ.hom.base ≫ Q₁.baseIso.inv = 𝟙 X.carrier
  rw [← Category.assoc, h, Iso.hom_inv_id]

include th in
/-- For `φ` under `X`, the morphism of spaces of extensions is a morphism under `X`. -/
theorem thickening_comp_spaceMapOfMap :
    Q₂.toAlgebraExtension.thickening ≫ spaceMapOfMap φ = Q₁.toAlgebraExtension.thickening := by
  rw [spaceMapOfMap, ← i_comp_toSpace, ← i_comp_toSpace, Category.assoc,
    ← Category.assoc Q₂.toSpace, toSpace_fromSpace, Category.id_comp, ← Category.assoc, th]

/-- For `φ` over `h' : S'₂ ⟶ S'₁`, the morphism of spaces of extensions is a morphism over
`h'`. -/
theorem spaceMapOfMap_comp_over (h' : S₂ ⟶ S₁) (bh : φ ≫ Q₁.f' = Q₂.f' ≫ h') :
    spaceMapOfMap φ ≫ Q₁.toAlgebraExtension.over = Q₂.toAlgebraExtension.over ≫ h' := by
  rw [spaceMapOfMap, Category.assoc, Category.assoc, toSpace_comp_over, bh,
    ← toSpace_comp_over Q₂, ← Category.assoc, ← Category.assoc, fromSpace_toSpace,
    Category.id_comp]

include th in
/-- The morphism of spaces of extensions moves no open set. -/
theorem spaceMapOfMap_opens (V : Opens X.carrier) :
    (Opens.map (spaceMapOfMap φ).hom.base).obj V = V := by
  rw [spaceMapOfMap_base φ th]
  rfl

/-- The comorphism of the morphism of spaces of extensions, followed by the identification of the
preimage of an open with the open itself. -/
def extensionHomOfMapApp (V : (Opens X.carrier)ᵒᵖ) :
    Q₁.thickenedPresheaf.obj V ⟶ Q₂.thickenedPresheaf.obj V :=
  (spaceMapOfMap φ).hom.c.app V ≫
    Q₂.thickenedPresheaf.map (eqToHom (congrArg op (spaceMapOfMap_opens φ th V.unop)))

/-- **The map `𝒪_{X'₁} ⟶ 𝒪_{X'₂}` of extensions attached to a morphism `φ : X'₂ ⟶ X'₁` of
deformed spaces under `X`**: the comorphism of `φ`, read on the opens of `X`. -/
def extensionHomOfMap : Q₁.toAlgebraExtension.sheaf ⟶ Q₂.toAlgebraExtension.sheaf :=
  ObjectProperty.homMk
    { app := extensionHomOfMapApp φ th
      naturality := fun {V _} k =>
        (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _)
          ((spaceMapOfMap φ).hom.c.naturality k)).trans
          ((Category.assoc _ _ _).trans ((congrArg ((spaceMapOfMap φ).hom.c.app V ≫ ·)
            ((Q₂.thickenedPresheaf.map_comp _ _).symm.trans
              ((congrArg Q₂.thickenedPresheaf.map (Subsingleton.elim _ _)).trans
                (Q₂.thickenedPresheaf.map_comp _ _)))).trans (Category.assoc _ _ _).symm))) }

/-- The component of the map of extensions attached to `φ` at an open `V` is
`extensionHomOfMapApp φ th V`. -/
theorem extensionHomOfMap_app (V : (Opens X.carrier)ᵒᵖ) :
    (extensionHomOfMap φ th).hom.app V = extensionHomOfMapApp φ th V :=
  rfl

/-- The map of extensions attached to `φ`, on sections: the comorphism of `φ` followed by the
restrictions along the round trips of opens. -/
theorem extensionHomOfMap_app_apply (V : (Opens X.carrier)ᵒᵖ) (x : Q₁.thickenedPresheaf.obj V) :
    ((extensionHomOfMap φ th).hom.app V).hom x =
      (Q₂.thickenedPresheaf.map (eqToHom (congrArg op (spaceMapOfMap_opens φ th V.unop)))).hom
        ((Q₂.X'.presheaf.map (eqToHom (congrArg op
          (Q₂.opens_roundTrip' ((Opens.map φ.hom.base).obj
            ((Opens.map Q₁.baseIso.inv).obj V.unop)))).symm)).hom
          ((φ.hom.c.app (op ((Opens.map Q₁.baseIso.inv).obj V.unop))).hom x)) :=
  rfl

/-- The map of extensions attached to `φ` is compatible with the reductions. -/
theorem extensionHomOfMap_comp_reduction :
    extensionHomOfMap φ th ≫ Q₂.toAlgebraExtension.reduction =
      Q₁.toAlgebraExtension.reduction := by
  refine ObjectProperty.hom_ext _ (NatTrans.ext (funext fun V => ?_))
  have hc := SheafedSpace.congr_hom_app (thickening_comp_spaceMapOfMap φ th) V
  exact (Category.assoc _ _ _).trans ((congrArg ((spaceMapOfMap φ).hom.c.app V ≫ ·)
    (Q₂.toAlgebraExtension.reduction.hom.naturality _)).trans ((Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ _) hc).trans ((Category.assoc _ _ _).trans
        ((congrArg (_ ≫ ·) (functor_map_comp_map_eq_id X.presheaf _ _)).trans
          (Category.comp_id _))))))

/-- **The map of extensions attached to `φ` is compatible with the algebra structures through
`h'`**: the adjoint `𝒪_{S'₁} ⟶ (f ∘ t₁)_* 𝒪_{X'₂}` of the algebra structure of `𝒪_{X'₁}` followed
by the map of extensions is `h'^♯` followed by `h'_*` of the adjoint of the algebra structure of
`𝒪_{X'₂}`. -/
theorem adjointBase_comp_extensionHomOfMap (h' : S₂ ⟶ S₁) (comm : t₂ ≫ h' = t₁)
    (bh : φ ≫ Q₁.f' = Q₂.f' ≫ h') :
    Q₁.toAlgebraExtension.adjointBase ≫
        (TopCat.Sheaf.pushforward CommRingCat.{u} (f ≫ t₁).hom.base).map
          (extensionHomOfMap φ th) =
      thickeningSharp h' ≫ (TopCat.Sheaf.pushforward CommRingCat.{u} h'.hom.base).map
          Q₂.toAlgebraExtension.adjointBase ≫
        eqToHom (by subst comm; rfl) := by
  subst comm
  refine ObjectProperty.hom_ext _ (NatTrans.ext (funext fun V => ?_))
  have hc := SheafedSpace.congr_hom_app (spaceMapOfMap_comp_over φ h' bh) V
  refine (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) hc).trans
    ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·)
      (functor_map_comp_map_eq_id Q₂.thickenedPresheaf _ _)).trans ?_)))
  exact (Category.comp_id _).trans (Category.comp_id _).symm

/-! ### The comorphism on the ideals -/

/-- **A solution over `t₂` read over `t₁ = t₂ ≫ h'`**: for the square `(i₂, f'₂ ≫ h')` over
`t₂ ≫ h'`, the reduction map of Stacks 08KZ followed by `i₂_*` of `baseChangeIdealMap ≫ c₂` and the
ideal inclusion of `Q₂` is the restriction of `(f'₂ ≫ h')^♯` to the pulled-back ideal. -/
theorem firstOrderSurjection_comp_baseChangeIdealMap_comp (Q : DeformationSolution t₂ ht₂ f G₂ c₂)
    (h' : S₂ ⟶ S₁) (ht : IsFirstOrderThickening (t₂ ≫ h')) (F : Q.X' ⟶ S₁) (hF : Q.f' ≫ h' = F)
    (comm' : Q.i ≫ F = f ≫ t₂ ≫ h') :
    (thickeningSquare ht Q.i F Q.i_firstOrder comm').firstOrderSurjection Q.i_firstOrder ht ≫
        (modulePushforward Q.i).map (baseChangeIdealMap f h' rfl ≫ c₂) ≫ Q.idealInclusion =
      (thickeningSquare ht Q.i F Q.i_firstOrder comm').ambientIdealMap := by
  refine ((modulePullbackPushforwardAdjunction F).homEquiv _ _).injective ?_
  rw [← Category.assoc, Adjunction.homEquiv_naturality_right]
  refine (congrArg (· ≫ (modulePushforward F).map Q.idealInclusion)
    ((thickeningSquare ht Q.i F Q.i_firstOrder comm').homEquiv_firstOrderSurjection
      Q.i_firstOrder ht _)).trans ?_
  refine Eq.trans ?_ (homEquiv_map_comp_pullbackUnitToUnit F _ _).symm
  ext V z
  have hF' := congrArg (fun k => k.hom ((Stacks.ClosedImmersion.idealSheafι (t₂ ≫ h')).val.app V z))
    (SheafedSpace.congr_hom_app hF.symm V)
  have F2 := congrArg (fun k => (k.val.app V).hom z)
    (homEquiv_baseIdealSheafMap_comp h' (rfl : t₂ ≫ h' = t₂ ≫ h'))
  have hx := congrArg (fun k => (k.val.app V).hom z)
    (prescribedIdealMap_baseChangeIdealMap_comp f h' c₂)
  let W : (Opens S₂.carrier)ᵒᵖ := op ((Opens.map h'.hom.base).obj V.unop)
  let w : (AlgebraicGeometry.SheafOfModules.idealSheaf t₂).val.obj W :=
    (((modulePullbackPushforwardAdjunction h').homEquiv _ _
    (baseIdealSheafMap h' rfl)).val.app V).hom z
  let ρ : op ((Opens.map (Q.f' ≫ h').hom.base).obj V.unop) ⟶
      op ((Opens.map F.hom.base).obj V.unop) :=
    eqToHom (congrArg (fun m : Q.X' ⟶ S₁ => op ((Opens.map m.hom.base).obj V.unop)) hF)
  let ρL : op ((Opens.map (f ≫ t₂ ≫ h').hom.base).obj V.unop) ⟶
      (Opens.map Q.i.hom.base).op.obj (op ((Opens.map F.hom.base).obj V.unop)) :=
    eqToHom (congrArg (fun m : X ⟶ S₁ => op ((Opens.map m.hom.base).obj V.unop)) comm'.symm)
  let ρR : op ((Opens.map (f ≫ t₂).hom.base).obj W.unop) ⟶
      (Opens.map Q.i.hom.base).op.obj (op ((Opens.map Q.f'.hom.base).obj W.unop)) :=
    eqToHom (congrArg (fun m : X ⟶ S₂ => op ((Opens.map m.hom.base).obj W.unop)) Q.comm.symm)
  have R4 : (Q.idealMapTranspose.val.app W).hom w =
      G₂.val.map ρR (((prescribedIdealMap c₂).val.app W).hom w) := by
    rw [Q.idealMapTranspose_eq]
    exact Q.toMorphismOfThickenings.pushforwardComparison_val_app G₂ W _
  have L2 := pushforward_eqToHom_val_app comm'.symm G₂ V
    (((prescribedIdealMap (t := t₂ ≫ h') (baseChangeIdealMap f h' rfl ≫ c₂)).val.app V).hom z)
  calc _ = Q.incl (G₂.val.map ρL
        (((prescribedIdealMap (t := t₂ ≫ h')
          (baseChangeIdealMap f h' rfl ≫ c₂)).val.app V).hom z)) :=
        congrArg Q.incl L2
    _ = Q.incl (G₂.val.map ρL (((prescribedIdealMap c₂).val.app W).hom w)) :=
        congrArg (fun x => Q.incl (G₂.val.map ρL x)) hx
    _ = Q.incl (((modulePushforward Q.i).obj G₂).val.map ρ
          (G₂.val.map ρR (((prescribedIdealMap c₂).val.app W).hom w))) :=
        congrArg Q.incl (map_map_eq_map G₂ ρR _ ρL _).symm
    _ = (Q.X'.presheaf.map ρ).hom
          (Q.incl (G₂.val.map ρR (((prescribedIdealMap c₂).val.app W).hom w))) :=
        Q.incl_naturality ρ _
    _ = (Q.X'.presheaf.map ρ).hom (Q.incl ((Q.idealMapTranspose.val.app W).hom w)) := by rw [R4]
    _ = (Q.X'.presheaf.map ρ).hom ((Q.f'.hom.c.app W).hom
          (((Stacks.ClosedImmersion.idealSheafι t₂).val.app W).hom w)) :=
        congrArg (Q.X'.presheaf.map ρ).hom (Q.incl_idealMapTranspose W w)
    _ = (Q.X'.presheaf.map ρ).hom ((Q.f'.hom.c.app W).hom ((h'.hom.c.app V).hom
          (((Stacks.ClosedImmersion.idealSheafι (t₂ ≫ h')).val.app V).hom z))) :=
        congrArg (fun y => (Q.X'.presheaf.map ρ).hom ((Q.f'.hom.c.app W).hom y)) F2
    _ = (F.hom.c.app V).hom (((Stacks.ClosedImmersion.idealSheafι (t₂ ≫ h')).val.app V).hom z) :=
        hF'.symm

/-- **On the ideals, the comorphism of a morphism of deformed spaces under `X` and over `h'` is
the comparison `ν` of the prescribed maps**, when the prescribed map `c₁` is invertible: the
restriction of `φ^♯` to the ideal `𝒢₁` of `X'₁` is `ν : 𝒢₁ ⟶ 𝒢₂` followed by the inclusion of
the ideal `𝒢₂` of `X'₂`. -/
theorem idealInclusion_comp_structureSheafModuleHom_of_map [IsIso c₁] (h' : S₂ ⟶ S₁)
    (comm : t₂ ≫ h' = t₁) (ν : G₁ ⟶ G₂) (hν : baseChangeIdealMap f h' comm ≫ c₂ = c₁ ≫ ν)
    (bh : φ ≫ Q₁.f' = Q₂.f' ≫ h') :
    Q₁.idealInclusion ≫ structureSheafModuleHom φ =
      (modulePushforward Q₁.i).map ν ≫ (pushforwardIsoOfComp Q₂.i φ Q₁.i th).hom.app G₂ ≫
        (modulePushforward φ).map Q₂.idealInclusion := by
  subst comm
  obtain ⟨X'₁, i₁, f'₁, hi₁, comm₁, kI₁, compat₁⟩ := Q₁
  dsimp only at φ th bh ⊢
  subst th
  have key := comp_structureSheafModuleHom_eq_of_ambient (ht := ht₁) Q₂.i Q₂.i_firstOrder f'₁ φ
    (by rw [← Category.assoc]; exact comm₁) hi₁ comm₁
    ((modulePushforward Q₂.i).map (baseChangeIdealMap f h' rfl ≫ c₂) ≫ Q₂.idealInclusion)
    (firstOrderSurjection_comp_baseChangeIdealMap_comp Q₂ h' ht₁ (φ ≫ f'₁) bh.symm _)
    ((modulePushforward (Q₂.i ≫ φ)).map c₁ ≫
      DeformationSolution.idealInclusion ⟨X'₁, Q₂.i ≫ φ, f'₁, hi₁, comm₁, kI₁, compat₁⟩)
    (DeformationSolution.firstOrderSurjection_comp_idealInclusion
      ⟨X'₁, Q₂.i ≫ φ, f'₁, hi₁, comm₁, kI₁, compat₁⟩)
  rw [pushforwardIsoOfComp_hom_app_eq] at key ⊢
  refine (cancel_epi ((modulePushforward (Q₂.i ≫ φ)).map c₁)).1 ?_
  refine ((Category.assoc _ _ _).symm.trans key).trans ?_
  have e2 : (modulePushforward φ).map ((modulePushforward Q₂.i).map
      (baseChangeIdealMap f h' rfl ≫ c₂) ≫ Q₂.idealInclusion) =
      (modulePushforward (Q₂.i ≫ φ)).map c₁ ≫ (modulePushforward (Q₂.i ≫ φ)).map ν ≫
        (modulePushforward φ).map Q₂.idealInclusion := by
    rw [hν, Functor.map_comp, Functor.map_comp, Functor.map_comp, Category.assoc]
    rfl
  exact (Category.id_comp _).trans (e2.trans (by simp only [eqToHom_refl]; rfl))

/-- `idealInclusion_comp_structureSheafModuleHom_of_map`, on sections: the comorphism of `φ`
carries the inclusion of a section `u` of `𝒢₁` into `𝒪_{X'₁}` to the inclusion of `ν u` into
`𝒪_{X'₂}`. -/
theorem c_app_incl_of_map [IsIso c₁] (h' : S₂ ⟶ S₁) (comm : t₂ ≫ h' = t₁) (ν : G₁ ⟶ G₂)
    (hν : baseChangeIdealMap f h' comm ≫ c₂ = c₁ ≫ ν) (bh : φ ≫ Q₁.f' = Q₂.f' ≫ h')
    (W : (Opens Q₁.X'.carrier)ᵒᵖ) (u : ((modulePushforward Q₁.i).obj G₁).val.obj W) :
    (φ.hom.c.app W).hom (Q₁.incl u) =
      Q₂.incl (G₂.val.map (eqToHom (by rw [← th]; rfl) :
        op ((Opens.map Q₁.i.hom.base).obj W.unop) ⟶
          op ((Opens.map Q₂.i.hom.base).obj ((Opens.map φ.hom.base).obj W.unop)))
        ((ν.val.app _).hom u)) := by
  have K := idealInclusion_comp_structureSheafModuleHom_of_map φ th h' comm ν hν bh
  rw [pushforwardIsoOfComp_hom_app_eq] at K
  exact (congrArg (fun k => (k.val.app W).hom u) K).trans
    (congrArg Q₂.incl (pushforward_eqToHom_val_app th.symm G₂ W _))

/-- **The map of extensions attached to `φ` induces `ν` on the ideals**, when `c₁` is
invertible. -/
theorem extensionHomOfMap_ideal [IsIso c₁] (h' : S₂ ⟶ S₁) (comm : t₂ ≫ h' = t₁) (ν : G₁ ⟶ G₂)
    (hν : baseChangeIdealMap f h' comm ≫ c₂ = c₁ ≫ ν) (bh : φ ≫ Q₁.f' = Q₂.f' ≫ h')
    (V : (Opens X.carrier)ᵒᵖ) (y : ↥(kernelIdeal Q₁.toAlgebraExtension.reduction.hom V)) :
    Q₂.toAlgebraExtension.ideal.app V ⟨(extensionHomOfMap φ th).hom.app V y, kernelIdeal_le_comap
        Q₁.toAlgebraExtension.reduction.hom _ (extensionHomOfMap φ th).hom
        (hom_of_comp_eq (extensionHomOfMap_comp_reduction φ th)) V y.2⟩ =
      ν.val.app V (Q₁.toAlgebraExtension.ideal.app V y) := by
  set g := Q₁.kernelSection y
  have hy := (extensionHomOfMap_app_apply φ th V y.1).trans
    ((congrArg (fun z => (Q₂.thickenedPresheaf.map
      (eqToHom (congrArg op (spaceMapOfMap_opens φ th V.unop)))).hom ((Q₂.X'.presheaf.map
        (eqToHom (congrArg op (Q₂.opens_roundTrip' ((Opens.map φ.hom.base).obj
          ((Opens.map Q₁.baseIso.inv).obj V.unop)))).symm)).hom
        ((φ.hom.c.app (op ((Opens.map Q₁.baseIso.inv).obj V.unop))).hom z)))
          (Q₁.incl_kernelSection y).symm).trans
    ((congrArg (fun z => (Q₂.thickenedPresheaf.map
      (eqToHom (congrArg op (spaceMapOfMap_opens φ th V.unop)))).hom ((Q₂.X'.presheaf.map
        (eqToHom (congrArg op (Q₂.opens_roundTrip' ((Opens.map φ.hom.base).obj
          ((Opens.map Q₁.baseIso.inv).obj V.unop)))).symm)).hom z))
      (c_app_incl_of_map φ th h' comm ν hν bh _ g)).trans
    ((congrArg _ (Q₂.incl_naturality _ _).symm).trans (Q₂.incl_naturality _ _).symm)))
  refine (congrArg Q₂.descendSection (Q₂.kernelSection_eq _ _ hy.symm)).trans ?_
  refine Eq.trans ?_ (PresheafOfModules.naturality_apply ν.val (Q₁.roundTripHom V) g).symm
  exact SolutionHom.map_four _ _ _ _ _ _

end DeformationSolution

end AlgebraicGeometry.RingedSpaceThickening

namespace Deformation.Examples

open AlgebraicGeometry.RingedSpaceThickening

variable {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k] {X : Over (Spec (CommRingCat.of k))}

/-- The closed points of the spectra of `𝒞_Λ` are compatible with the maps of spectra, as a
commutative triangle of ringed spaces. -/
theorem residueSpecMap_toShHom_comp_baseSpecMap {A B : ArtinianLocalAlgCat.{u, u, u} Λ k}
    (e : A ⟶ B) :
    (residueSpecMap B).toLRSHom.toShHom ≫ (baseSpecMap e).toLRSHom.toShHom =
      (residueSpecMap A).toLRSHom.toShHom :=
  congrArg (fun p : Spec (CommRingCat.of k) ⟶ baseSpec A => p.toLRSHom.toShHom)
    (residueSpecMap_naturality e)

/-- An arrow of the deformation category of `X` over `e : A ⟶ B` gives a map of total spaces
`y ⟶ x` over `Spec e`, compatibly with the rebased structure morphisms. -/
theorem map_comp_toBase_of_isHomLift {A B : ArtinianLocalAlgCat.{u, u, u} Λ k} (e : A ⟶ B)
    (x : (schemeDeformationCategoryProjection (Λ := Λ) (k := k) X).Fiber A)
    (y : (schemeDeformationCategoryProjection (Λ := Λ) (k := k) X).Fiber B)
    (a : x.1 ⟶ y.1) [(schemeDeformationCategoryProjection X).IsHomLift e a] :
    a.map ≫ x.1.toBase ≫ eqToHom (congrArg baseSpec x.2) =
      (y.1.toBase ≫ eqToHom (congrArg baseSpec y.2)) ≫ baseSpecMap e := by
  have hb : a.base = eqToHom x.2 ≫ e ≫ eqToHom y.2.symm :=
    IsHomLift.fac' (schemeDeformationCategoryProjection (Λ := Λ) (k := k) X) e a
  rw [← Category.assoc, a.cartesian.w, hb, baseSpecMap_comp, baseSpecMap_comp,
    baseSpecMap_eqToHom, baseSpecMap_eqToHom]
  simp

/-- **Base change of the solution attached to a first-order deformation of a scheme.** Let
`g : V ⟶ W` be a map of finite-dimensional `k`-vector spaces, `x` a deformation of `X` over
`k[V]`, `y` a deformation over `k[W]` and `a : x ⟶ y` an arrow of the deformation category over
`k[g]`. Then the solution of the deformation problem of Stacks 08U7 attached to `y` is isomorphic
to the base change along `Spec k[W] ⟶ Spec k[V]` of the solution attached to `x`, the comparison
of the prescribed maps being the map `f^*𝒥_V ⟶ f^*𝒥_W` of pulled back ideals. -/
theorem isomorphic_fiberSolution_baseChange {V W : FGModuleCat.{u} k} (g : V ⟶ W)
    (x : (schemeDeformationCategoryProjection (Λ := Λ) (k := k) X).Fiber
      ((squareZeroExtensionArtinian.{u, u, u} Λ k).obj V))
    (y : (schemeDeformationCategoryProjection (Λ := Λ) (k := k) X).Fiber
      ((squareZeroExtensionArtinian.{u, u, u} Λ k).obj W))
    (a : x.1 ⟶ y.1)
    [(schemeDeformationCategoryProjection X).IsHomLift
      ((squareZeroExtensionArtinian.{u, u, u} Λ k).map g) a] :
    Isomorphic (fiberSolution (maximalIdeal_squareZeroExtensionArtinian_pow_two W) y)
      ((fiberSolution (maximalIdeal_squareZeroExtensionArtinian_pow_two V) x).baseChange
        (residueSpecMap_isFirstOrderThickening _
          (maximalIdeal_squareZeroExtensionArtinian_pow_two W))
        (𝟙 _) (baseSpecMap ((squareZeroExtensionArtinian.{u, u, u} Λ k).map g)).toLRSHom.toShHom
        (residueSpecMap_toShHom_comp_baseSpecMap _)
        (baseChangeIdealMap X.hom.toLRSHom.toShHom _ (residueSpecMap_toShHom_comp_baseSpecMap _))
        ((Category.comp_id _).trans (Category.id_comp _).symm)) := by
  have th := congrArg (fun p : X.left ⟶ x.1.scheme => p.toLRSHom.toShHom) a.special_compat
  have bh := congrArg (fun p => p.toLRSHom.toShHom) (map_comp_toBase_of_isHomLift
    ((squareZeroExtensionArtinian.{u, u, u} Λ k).map g) x y a)
  exact DeformationSolution.isomorphic_baseChange_of_hom _ _ _ _ _ _ _ _
    (DeformationSolution.extensionHomOfMap a.map.toLRSHom.toShHom th)
    (DeformationSolution.extensionHomOfMap_comp_reduction _ th)
    (DeformationSolution.extensionHomOfMap_ideal _ th _
      (residueSpecMap_toShHom_comp_baseSpecMap _) _
      ((Category.comp_id _).trans (Category.id_comp _).symm) bh)
    (DeformationSolution.adjointBase_comp_extensionHomOfMap _ th _
      (residueSpecMap_toShHom_comp_baseSpecMap _) bh)

end Deformation.Examples

end
