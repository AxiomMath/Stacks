module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.LevelSheafHColimit
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.BaseChangeColimitVanishing

/-!
# Stacks 03Q6: the étale cohomology of a limit of base changes is the colimit

Let `T` be affine, `X ⟶ T` quasi-compact and quasi-separated, `(Z_i)` a directed system of
affine schemes over `T`, `Y_i = Z_i ×_T X` with a limit `Y`, `p : Y ⟶ X` the projection and `F`
an abelian sheaf on `X_étale`. Then for every `n` the restriction maps

`H^n(Y_i, π_i⁻¹ F) ⟶ H^n(Y, p⁻¹ F)`

exhibit `H^n(Y, p⁻¹ F)` as the colimit of the `H^n(Y_i, π_i⁻¹ F)` along the restriction maps
(`Stacks.EtaleCohomology.ColimitBaseChange.isIso_colimitDesc_cohomologyCocone`). The cohomology is
Mathlib's `CategoryTheory.Sheaf.H`, and the restriction maps are
`Stacks.EtaleCohomology.ColimitBaseChange.sheafHRestriction`: `Ext` along the inverse image,
followed by `f⁻¹ ℤ ≅ ℤ` and the composition comparisons of inverse images.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

namespace Stacks.EtaleCohomology.ColimitBaseChange

universe u

open Stacks.EtaleCohomology.BaseChangeAlgebraSystem Stacks.EtaleCohomology.AffineLimitCohomology
  Stacks.EtaleCohomology.TransitionBaseChange Stacks.EtaleCohomology.QcqsBaseChange Stacks.Homology

/-- Sheafification of abelian groups at the object universe of the small étale site. -/
local instance hasSheafify_smallEtale_objectUniverse'' (Y : Scheme.{u}) :
    HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u + 1} :=
  Scheme.hasSheafify_smallEtaleTopology.{u, u + 1} Y

variable {I : Type u} [Preorder I] (T : Scheme.{u}) (X : Over T) (Z : Iᵒᵖ ⥤ Over T)
  (F : Sheaf X.left.smallEtaleTopology Ab.{u + 1})

/-- The composition comparison along a transition of the system of base changes. -/
abbrev levelComp {i j : Iᵒᵖ} (f : i ⟶ j) :=
  smallEtalePullbackAbCompIso' ((baseChange T X Z).map f) (levelProj T X Z j) (levelProj T X Z i)
    (levelProj_transition T X Z f)

/-- The restriction map `H^n(Y_j, G_j) ⟶ H^n(Y_i, G_i)` along a transition `f : i ⟶ j`. -/
abbrev cohomologyTransition {i j : Iᵒᵖ} (f : i ⟶ j) (n : ℕ) :=
  sheafHRestriction ((baseChange T X Z).map f) ((levelComp T X Z f).hom.app F) n

/-- The associativity pentagon of the inverse image comparison, read on components as a formula
for the composition comparison of `q = j ≫ i` followed by `f`. -/
private theorem pullbackAbCompIso'_hom_app_eq {X₀ X₁ X₂ X₃ : Scheme.{u}} (f : X₁ ⟶ X₀)
    (i : X₂ ⟶ X₁) (j : X₃ ⟶ X₂) (a : X₂ ⟶ X₀) (ha : a = i ≫ f) (q : X₃ ⟶ X₁) (hq : q = j ≫ i)
    (p : X₃ ⟶ X₀) (hp₁ : p = q ≫ f) (hp₂ : p = j ≫ a) (G : Sheaf X₀.smallEtaleTopology Ab.{u + 1}) :
    (smallEtalePullbackAbCompIso' q f p hp₁).hom.app G =
      (smallEtalePullbackAbCompIso' j i q hq).inv.app ((smallEtalePullbackAb f).obj G) ≫
        (smallEtalePullbackAb j).map ((smallEtalePullbackAbCompIso' i f a ha).hom.app G) ≫
          (smallEtalePullbackAbCompIso' j a p hp₂).hom.app G := by
  have h1 := congrArg (fun e => e.hom.app G)
    (smallEtalePullbackAbCompIso'_assoc f i j a ha q hq p hp₁ hp₂)
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
    Functor.associator_inv_app, Category.id_comp] at h1
  rw [← h1, Iso.inv_hom_id_app_assoc]

/-- The restriction maps compose along transitions: restricting along `f'` and then along `f` is
restricting along the composite `f'' : i ⟶ k`. -/
theorem cohomologyTransition_comp {i j k : Iᵒᵖ} (f : i ⟶ j) (f' : j ⟶ k) (f'' : i ⟶ k) (n : ℕ)
    (x : Sheaf.H.{u + 1, u + 1} (levelSheaf T X Z F k) n) :
    cohomologyTransition T X Z F f n (cohomologyTransition T X Z F f' n x) =
      cohomologyTransition T X Z F f'' n x := by
  obtain rfl : f'' = f ≫ f' := Subsingleton.elim _ _
  refine sheafHRestriction_comp _ _ _ ((baseChange T X Z).map_comp f f') _ _ _ ?_ n x
  exact pullbackAbCompIso'_hom_app_eq (levelProj T X Z k) ((baseChange T X Z).map f')
    ((baseChange T X Z).map f) (levelProj T X Z j) (levelProj_transition T X Z f')
    ((baseChange T X Z).map (f ≫ f')) ((baseChange T X Z).map_comp f f') (levelProj T X Z i)
    (levelProj_transition T X Z (f ≫ f')) (levelProj_transition T X Z f) F

/-- The restriction map `H^n(Y_i, G_i) ⟶ H^n(Y_i, G_i)` along the identity of `i` is the
identity. -/
theorem cohomologyTransition_id (i : Iᵒᵖ) (n : ℕ)
    (x : Sheaf.H.{u + 1, u + 1} (levelSheaf T X Z F i) n) :
    cohomologyTransition T X Z F (𝟙 i) n x = x :=
  (bijective_sheafHRestriction_of_eq_id ((baseChange T X Z).map (𝟙 i))
    ((baseChange T X Z).map_id i) ((levelComp T X Z (𝟙 i)).hom.app F) n).1
    (cohomologyTransition_comp T X Z F (𝟙 i) (𝟙 i) (𝟙 i) n x)

/-- **The diagram `a ↦ H^n(Y_a, G_a)` of the étale cohomology of the levels**, with the restriction
maps. -/
def cohomologyDiagram (n : ℕ) : Iᵒᵖᵒᵖ ⥤ Ab.{u + 1} where
  obj a := AddCommGrpCat.of (Sheaf.H.{u + 1, u + 1} (levelSheaf T X Z F a.unop) n)
  map g := AddCommGrpCat.ofHom (cohomologyTransition T X Z F g.unop n)
  map_id a := by
    ext x
    exact cohomologyTransition_id T X Z F a.unop n x
  map_comp g g' := by
    ext x
    exact (cohomologyTransition_comp T X Z F g'.unop g.unop (g ≫ g').unop n x).symm

variable {T X Z} (cY : Cone (baseChange T X Z)) (p : cY.pt ⟶ X.left)
  (hp : ∀ i, p = cY.π.app i ≫ levelProj T X Z i)

/-- The restriction map `H^n(Y_a, G_a) ⟶ H^n(Y, p⁻¹ F)` along the leg of the limit cone. -/
abbrev cohomologyLeg (i : Iᵒᵖ) (n : ℕ) :=
  sheafHRestriction (cY.π.app i)
    ((smallEtalePullbackAbCompIso' (cY.π.app i) (levelProj T X Z i) p (hp i)).hom.app F) n

/-- The restrictions to the limit are compatible with the transitions: restricting along
`f : i ⟶ j` and then along the leg at `i` is restricting along the leg at `j`. -/
theorem cohomologyLeg_transition {i j : Iᵒᵖ} (f : i ⟶ j) (n : ℕ)
    (x : Sheaf.H.{u + 1, u + 1} (levelSheaf T X Z F j) n) :
    cohomologyLeg F cY p hp i n (cohomologyTransition T X Z F f n x) =
      cohomologyLeg F cY p hp j n x := by
  refine sheafHRestriction_comp _ _ _ (cY.w f).symm _ _ _ ?_ n x
  exact pullbackAbCompIso'_hom_app_eq (levelProj T X Z j) ((baseChange T X Z).map f) (cY.π.app i)
    (levelProj T X Z i) (levelProj_transition T X Z f) (cY.π.app j) (cY.w f).symm p (hp j) (hp i) F

variable (T X Z) in
/-- **The cocone of restrictions to the limit**, with vertex `H^n(Y, p⁻¹ F)`. -/
def cohomologyCocone (n : ℕ) : Cocone (cohomologyDiagram T X Z F n) where
  pt := AddCommGrpCat.of (Sheaf.H.{u + 1, u + 1} ((smallEtalePullbackAb p).obj F) n)
  ι :=
    { app a := AddCommGrpCat.ofHom (cohomologyLeg F cY p hp a.unop n)
      naturality a b g := by
        ext x
        exact (cohomologyLeg_transition F cY p hp g.unop n x).trans rfl }

/-- The component of `cohomologyCocone` at `a` is the restriction map `cohomologyLeg` at
`a.unop`. -/
theorem cohomologyCocone_ι_app (n : ℕ) (a : Iᵒᵖᵒᵖ) (x) :
    (cohomologyCocone T X Z F cY p hp n).ι.app a x = cohomologyLeg F cY p hp a.unop n x := rfl

variable (T X Z) in
/-- **Stacks 03Q6.** For `T` affine, `X ⟶ T` quasi-compact and quasi-separated, a directed system
`(Z_i)` of affine schemes over `T` and a limit `Y` of the base changes `Y_i = Z_i ×_T X`, the
restriction maps `H^n(Y_i, π_i⁻¹ F) ⟶ H^n(Y, p⁻¹ F)` exhibit `H^n(Y, p⁻¹ F)` as the colimit of the
`H^n(Y_i, π_i⁻¹ F)`, for every abelian sheaf `F` on `X_étale` and every `n`. -/
theorem isIso_colimitDesc_cohomologyCocone [Nonempty I] [IsDirected I (· ≤ ·)] [IsAffine T]
    [∀ i, IsAffine (Z.obj i).left] [QuasiCompact X.hom] [QuasiSeparated X.hom] (hcY : IsLimit cY)
    (n : ℕ) :
    IsIso (colimit.desc (cohomologyDiagram T X Z F n) (cohomologyCocone T X Z F cY p hp n)) := by
  obtain ⟨B, hD, hY⟩ := exists_bigEtaleSite_contains T X Z cY
  let E := affineEtaleSiteColimit.{u, u} (baseChange T X Z) cY B hD hY hcY
  let d := baseChangeCoconeToX T X Z
  let i₀ : (sys.{u, u} (baseChange T X Z) cY B hD hY hcY).I :=
    E.indexEquiv.inverse.obj (Opposite.op (Classical.arbitrary I))
  have : CompactSpace (levelScheme.{u, u} (baseChange T X Z) cY B hD hY hcY i₀) :=
    compactSpace_baseChange_obj T X Z _
  have : QuasiSeparatedSpace (levelScheme.{u, u} (baseChange T X Z) cY B hD hY hcY i₀) :=
    quasiSeparatedSpace_baseChange_obj T X Z _
  have hp' : ∀ i : (sys.{u, u} (baseChange T X Z) cY B hD hY hcY).I,
      p = coneProj E i ≫ stageProj E d i := fun i => hp _
  obtain ⟨h⟩ := nonempty_isColimit_stageExtCocone.{u, u} (baseChange T X Z) cY B hD hY hcY d p hp'
    F i₀ n
  let e := E.indexEquiv.op
  let α : stageExtDiagram.{u, u} (baseChange T X Z) cY B hD hY hcY d (constZ d.pt) F n ≅
      e.functor ⋙ cohomologyDiagram T X Z F n :=
    NatIso.ofComponents (fun j => (extPullbackConstIso (stageProj E d j.unop) _ n).toAddCommGrpIso)
      (fun {j k} a => by
        ext y
        exact extPullbackConstIso_naturality (stageMor E a.unop) (stageProj E d j.unop)
          (stageProj E d k.unop) (stageProj_eq E d a.unop) _ n y)
  let c' := (cohomologyCocone T X Z F cY p hp n).whisker e.functor
  let iso : stageExtCocone.{u, u} (baseChange T X Z) cY B hD hY hcY d p hp' (constZ d.pt) F n ≅
      (Cocone.precompose α.hom).obj c' :=
    Cocone.ext (extPullbackConstIso p _ n).toAddCommGrpIso (fun j => by
      ext y
      exact (extPullbackConstIso_naturality (coneProj E j.unop) (stageProj E d j.unop) p
        (hp' j.unop) _ n y))
  exact (Stacks.Cohomology.ColimitLongExact.isIso_colimitDesc_iff _).2
    ⟨IsColimit.ofWhiskerEquivalence e
      ((IsColimit.precomposeHomEquiv α c').1 (IsColimit.ofIsoColimit h iso))⟩

end Stacks.EtaleCohomology.ColimitBaseChange

end
