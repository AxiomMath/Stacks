module

public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleSupportInvariance
public import StacksFrontier.AlgebraicGeometry.Spaces.WeaklyAssociatedChart

/-!
# Germs in the stalk of a module at a geometric point

Let `X` be an algebraic space over `S`, let `F` be an `𝒪_X`-module and let `x̄` be a geometric
point of `X`. A section of `F` over a small étale neighbourhood of `x̄` has a germ in the
geometric stalk `F_{x̄}`. This file supplies that germ map, with the facts which characterise
it: it is additive, semilinear along the germ map of the structure sheaf, compatible with
restriction to a smaller neighbourhood, jointly surjective, and injective exactly up to
restriction. The same API is given one layer down, for the stalk of a sheaf of modules at a
point of an arbitrary site.

## Main definitions

* `Stacks.moduleStalkLargeGerm` is the germ map into `Stacks.moduleStalkLarge`, the stalk of a
  sheaf of modules at a point of a site.
* `AlgebraicGeometry.Space.geometricModuleStalkAddEquiv` is the extension of scalars defining
  the geometric stalk, read on the underlying additive groups.
* `AlgebraicGeometry.Space.geometricModuleStalkGerm` is the germ map into
  `AlgebraicGeometry.Space.geometricModuleStalk`.

## Main results

* `Stacks.moduleStalkLargeGerm_smul`, `Stacks.moduleStalkLargeGerm_w`,
  `Stacks.moduleStalkLargeGerm_jointly_surjective` and `Stacks.moduleStalkLargeGerm_eq_iff`:
  the germ map is semilinear along `CategoryTheory.GrothendieckTopology.Point.toPresheafFiber`,
  it is compatible with restriction, every element of the stalk is a germ, and two sections over
  one neighbourhood have the same germ exactly when they agree after restriction.
* `AlgebraicGeometry.Space.geometricModuleStalkGerm_smul`: the geometric germ map is semilinear
  along `AlgebraicGeometry.Space.etaleLocalRingGerm`.
* `AlgebraicGeometry.Space.geometricModuleStalkGerm_eq_iff` and
  `AlgebraicGeometry.Space.geometricModuleStalkGerm_eq_zero_iff`: the equality and vanishing
  criteria read on small étale neighbourhoods.
* `AlgebraicGeometry.Space.nontrivial_geometricModuleStalk_iff`: the geometric stalk is nonzero
  exactly when some section over some neighbourhood has nonzero germ.
* `AlgebraicGeometry.Space.geometricModuleStalkGerm_etaleModulePullback_eq_iff` and
  `AlgebraicGeometry.Space.nontrivial_geometricModuleStalk_etaleModulePullback_iff`: germs in
  the stalk of an étale pullback at a geometric point of the source are germs in the stalk of
  the original module at the image point.

## Implementation notes

`Stacks.moduleStalkLarge` is a `ModuleCat.restrictScalars` of a filtered colimit over a small
final model of the category of neighbourhoods of the point, and the geometric stalk is a
`ModuleCat.extendScalars` of that along `AlgebraicGeometry.Space.pointStalkRingEquiv`. The germ
map is therefore built in two steps. Over the neighbourhoods it is Mathlib's
`CategoryTheory.GrothendieckTopology.Point.toPresheafFiber` for the lifted sections, carried to
the final model along `CategoryTheory.Functor.Final.colimitIso`; semilinearity is the colimit
scalar action `CategoryTheory.Limits.IsColimit.ι_smul` on the final model, transported to an
arbitrary neighbourhood along a structured arrow. The extension of scalars is then crossed once,
by `ModuleCat.extendScalarsRingEquivAddEquiv`, which is an isomorphism of additive groups
because the ring map is one; joint surjectivity, the equality criterion and the vanishing
criterion all transport along it, with no flatness input.

The étale pullback comparison carries no map of stalks: the two stalks are modules over
different, though isomorphic, étale local rings. What is compared is germs, and a germ of a
pullback section *is* a germ of the original section, because the sections agree on the nose
(`AlgebraicGeometry.Space.etaleModulePullback_obj_val_obj`). The equality criterion reduces both
sides to a refinement of neighbourhoods, and the two systems of refinements are compared by
`AlgebraicGeometry.Space.bijective_colimitTypePrecomp_smallEtaleNeighborhoodPostcomp`, which is
where the initiality of postcomposition enters.

## References

* [Stacks Project, Tag 05VQ](https://stacks.math.columbia.edu/tag/05VQ)
* [Stacks Project, Tag 04KG](https://stacks.math.columbia.edu/tag/04KG)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u m v w t

attribute [local instance] FinallySmall.preservesColimitsOfShape_of_isFiltered

namespace Stacks

variable {C : Type t} [Category.{v} C] [LocallySmall.{w} C]
  {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  (p : J.Point.{w}) (O : Sheaf J CommRingCat.{w})
  (F : SheafOfModules.{m} (commRingSheafToRingSheaf O))

/-! ### Germs in the stalk at a point of a site -/

/-- The sections of `F` as a presheaf of abelian groups, raised to the universe `max w m` in
which the stalk `Stacks.moduleStalkLarge` is formed. -/
noncomputable abbrev liftedSectionPresheaf : Cᵒᵖ ⥤ AddCommGrpCat.{max w m} :=
  F.val.presheaf ⋙ AddCommGrpCat.uliftFunctor.{w}

/-- The comparison of the colimit of the lifted sections of `F` over a small final model of
the neighbourhoods of `p` — the colimit `Stacks.moduleStalkLarge` is formed from — with their
colimit over all neighbourhoods, which is the stalk of the lifted sections as a presheaf of
abelian groups. -/
noncomputable abbrev moduleStalkLargeFinalIso :=
  Functor.Final.colimitIso (FinallySmall.fromFilteredFinalModel.{w} p.fiber.Elementsᵒᵖ)
    ((CategoryOfElements.π p.fiber).op ⋙ liftedSectionPresheaf.{m} O F)

/-- The germ map `F(U) →+ F_p` attached to a neighbourhood `(U, x)` of a point `p` of a site:
a section over `U` is sent to its class in the stalk. -/
noncomputable def moduleStalkLargeGerm (U : C) (x : p.fiber.obj U) :
    F.val.obj (op U) →+ moduleStalkLarge.{m} p O F :=
  (moduleStalkLargeFinalIso.{m} p O F).inv.hom.comp
    ((p.toPresheafFiber U x (liftedSectionPresheaf.{m} O F)).hom.comp
      (AddEquiv.ulift.symm : _ ≃+ ULift.{w} _).toAddMonoidHom)

/-- The germ of a section is its image in the colimit over the neighbourhoods of the point,
transported to the colimit over the small final model which carries the stalk. -/
theorem moduleStalkLargeGerm_apply (U : C) (x : p.fiber.obj U) (s : F.val.obj (op U)) :
    moduleStalkLargeGerm p O F U x s =
      (moduleStalkLargeFinalIso.{m} p O F).inv
        (p.toPresheafFiber U x (liftedSectionPresheaf.{m} O F) (ULift.up s)) :=
  rfl

/-- The germ maps are compatible with restriction along a morphism of neighbourhoods. -/
theorem moduleStalkLargeGerm_w {U V : C} (f : U ⟶ V) (x : p.fiber.obj U)
    (s : F.val.obj (op V)) :
    moduleStalkLargeGerm p O F U x (F.val.map f.op s) =
      moduleStalkLargeGerm p O F V (p.fiber.map f x) s :=
  congrArg (moduleStalkLargeFinalIso.{m} p O F).inv.hom
    (p.toPresheafFiber_w_apply f x (liftedSectionPresheaf.{m} O F) (ULift.up s))

/-- Every element of the stalk is the germ of a section over some neighbourhood. -/
theorem moduleStalkLargeGerm_jointly_surjective (z : moduleStalkLarge.{m} p O F) :
    ∃ (U : C) (x : p.fiber.obj U) (s : F.val.obj (op U)),
      moduleStalkLargeGerm p O F U x s = z := by
  let : PreservesFilteredColimitsOfSize.{w, w} (forget AddCommGrpCat.{max w m}) :=
    preservesFilteredColimitsOfSize_shrink _
  obtain ⟨U, x, ⟨a⟩, ha⟩ := p.toPresheafFiber_jointly_surjective
    (P := liftedSectionPresheaf.{m} O F) ((moduleStalkLargeFinalIso.{m} p O F).hom z)
  refine ⟨U, x, a, ?_⟩
  show (moduleStalkLargeFinalIso.{m} p O F).inv
    (p.toPresheafFiber U x (liftedSectionPresheaf.{m} O F) (ULift.up a)) = z
  rw [ha]
  exact ConcreteCategory.congr_hom (moduleStalkLargeFinalIso.{m} p O F).hom_inv_id z

/-- The germ map is semilinear along the germ map of the sheaf of rings: the germ of `r • s`
is the germ of `r` acting on the germ of `s`. -/
theorem moduleStalkLargeGerm_smul (U : C) (x : p.fiber.obj U)
    (r : (commRingSheafToRingSheaf O).obj.obj (op U)) (s : F.val.obj (op U)) :
    moduleStalkLargeGerm p O F U x (r • s) =
      p.toPresheafFiber U x O.obj r • moduleStalkLargeGerm p O F U x s := by
  let K : FinallySmall.FilteredFinalModel.{w} (p.fiber.Elementsᵒᵖ) ⥤ p.fiber.Elementsᵒᵖ :=
    FinallySmall.fromFilteredFinalModel _
  let R₀ := (CategoryOfElements.π p.fiber).op ⋙ (commRingSheafToRingSheaf O).obj
  let R := K ⋙ R₀
  let M := K ⋙ (CategoryOfElements.π p.fiber).op ⋙ liftedSectionPresheaf.{m} O F
  let (j : _) : Module (R.obj j) (M.obj j) := by
    show Module _ (ULift (F.val.obj _))
    let : Module ((commRingSheafToRingSheaf O).obj.obj
        ((CategoryOfElements.π p.fiber).op.obj (K.obj j)))
        (F.val.obj ((CategoryOfElements.π p.fiber).op.obj (K.obj j))) :=
      (F.val.obj _).isModule
    infer_instance
  have H : ∀ {j k} (f : j ⟶ k) (a : R.obj j) (b : M.obj j),
      M.map f (a • b) = R.map f a • M.map f b := by
    intro j k f a b
    let : Module (R.obj j)
        (F.val.presheaf.obj ((CategoryOfElements.π p.fiber).op.obj (K.obj j))) :=
      (F.val.obj _).isModule
    show ULift.up (F.val.map _ (a • b.down)) = ULift.up (_ • F.val.map _ b.down)
    exact congrArg ULift.up (F.val.map_smul _ _ _)
  let : Module (colimit R : RingCat.{w}) (colimit M : AddCommGrpCat.{max w m}) :=
    IsColimit.module R M (fun f a b => H f a b) (colimit.isColimit R) (colimit.isColimit M)
  let eR : (colimit R : RingCat.{w}) ≅ (forget₂ CommRingCat RingCat).obj
      ((p.presheafFiber (A := CommRingCat.{w})).obj O.obj) :=
    Functor.Final.colimitIso K R₀ ≪≫
      (preservesColimitIso (forget₂ CommRingCat RingCat)
        ((CategoryOfElements.π p.fiber).op ⋙ O.obj)).symm
  have heM : ∀ (j : _) (b : F.val.obj (op (K.obj j).unop.1)),
      moduleStalkLargeGerm p O F (K.obj j).unop.1 (K.obj j).unop.2 b =
        colimit.ι M j (ULift.up b) := fun j b =>
    ConcreteCategory.congr_hom (Functor.Final.ι_colimitIso_inv K
      ((CategoryOfElements.π p.fiber).op ⋙ liftedSectionPresheaf.{m} O F) j) (ULift.up b)
  have heR : ∀ (j : _) (a : R.obj j),
      eR.inv (p.toPresheafFiber (K.obj j).unop.1 (K.obj j).unop.2 O.obj a) =
        colimit.ι R j a := by
    intro j a
    apply (ConcreteCategory.bijective_of_isIso eR.hom).1
    simp only [← ConcreteCategory.comp_apply, eR.inv_hom_id, ConcreteCategory.id_apply]
    symm
    show (colimit.ι R j ≫ (Functor.Final.colimitIso K R₀).hom ≫
      (preservesColimitIso (forget₂ CommRingCat RingCat)
        ((CategoryOfElements.π p.fiber).op ⋙ O.obj)).inv) a = _
    show _ = ((forget₂ CommRingCat RingCat).map
      (colimit.ι ((CategoryOfElements.π p.fiber).op ⋙ O.obj) (K.obj j))) a
    apply ConcreteCategory.congr_hom
    exact (Functor.Final.ι_colimitIso_hom_assoc K R₀ j _).trans
      (ι_preservesColimitIso_inv (forget₂ CommRingCat RingCat)
        ((CategoryOfElements.π p.fiber).op ⋙ O.obj) (K.obj j))
  have hfinal : ∀ (j : _) (a : R.obj j) (b : F.val.obj (op (K.obj j).unop.1)),
      moduleStalkLargeGerm p O F (K.obj j).unop.1 (K.obj j).unop.2 (a • b) =
        p.toPresheafFiber (K.obj j).unop.1 (K.obj j).unop.2 O.obj a •
          moduleStalkLargeGerm p O F (K.obj j).unop.1 (K.obj j).unop.2 b := by
    intro j a b
    rw [heM, heM]
    show colimit.ι M j (ULift.up (a • b)) =
      eR.inv (p.toPresheafFiber (K.obj j).unop.1 (K.obj j).unop.2 O.obj a) •
        colimit.ι M j (ULift.up b)
    rw [heR]
    exact IsColimit.ι_smul R M (fun f c d => H f c d) (colimit.isColimit R)
      (colimit.isColimit M) j a (ULift.up b)
  obtain ⟨A⟩ := (inferInstance : Nonempty (StructuredArrow (op (p.fiber.elementsMk U x)) K))
  have hgy : p.fiber.map A.hom.unop.1 (K.obj A.right).unop.2 = x := A.hom.unop.2
  have hw : ∀ (b : F.val.obj (op U)),
      moduleStalkLargeGerm p O F (K.obj A.right).unop.1 (K.obj A.right).unop.2
          (F.val.map A.hom.unop.1.op b) = moduleStalkLargeGerm p O F U x b := fun b =>
    (moduleStalkLargeGerm_w p O F A.hom.unop.1 (K.obj A.right).unop.2 b).trans
      (congrArg (fun z => moduleStalkLargeGerm p O F U z b) hgy)
  have hr : p.toPresheafFiber (K.obj A.right).unop.1 (K.obj A.right).unop.2 O.obj
        ((commRingSheafToRingSheaf O).obj.map A.hom.unop.1.op r) =
      p.toPresheafFiber U x O.obj r :=
    (p.toPresheafFiber_w_apply A.hom.unop.1 (K.obj A.right).unop.2 O.obj r).trans
      (congrArg (fun z => p.toPresheafFiber U z O.obj r) hgy)
  calc moduleStalkLargeGerm p O F U x (r • s)
      = moduleStalkLargeGerm p O F (K.obj A.right).unop.1 (K.obj A.right).unop.2
          (F.val.map A.hom.unop.1.op (r • s)) := (hw (r • s)).symm
    _ = moduleStalkLargeGerm p O F (K.obj A.right).unop.1 (K.obj A.right).unop.2
          ((commRingSheafToRingSheaf O).obj.map A.hom.unop.1.op r •
            F.val.map A.hom.unop.1.op s) :=
          congrArg (moduleStalkLargeGerm p O F (K.obj A.right).unop.1 (K.obj A.right).unop.2)
            (F.val.map_smul A.hom.unop.1.op r s)
    _ = p.toPresheafFiber (K.obj A.right).unop.1 (K.obj A.right).unop.2 O.obj
            ((commRingSheafToRingSheaf O).obj.map A.hom.unop.1.op r) •
          moduleStalkLargeGerm p O F (K.obj A.right).unop.1 (K.obj A.right).unop.2
            (F.val.map A.hom.unop.1.op s) := hfinal A.right _ _
    _ = p.toPresheafFiber U x O.obj r • moduleStalkLargeGerm p O F U x s := by
          rw [hr, hw]

/-- Two sections over the same neighbourhood have the same germ exactly when they agree after
restriction to a smaller neighbourhood. -/
theorem moduleStalkLargeGerm_eq_iff (U : C) (x : p.fiber.obj U) (s t : F.val.obj (op U)) :
    moduleStalkLargeGerm p O F U x s = moduleStalkLargeGerm p O F U x t ↔
      ∃ (V : C) (f : V ⟶ U) (y : p.fiber.obj V), p.fiber.map f y = x ∧
        F.val.map f.op s = F.val.map f.op t := by
  let : PreservesFilteredColimitsOfSize.{w, w} (forget AddCommGrpCat.{max w m}) :=
    preservesFilteredColimitsOfSize_shrink _
  refine Iff.trans
    (ConcreteCategory.bijective_of_isIso (moduleStalkLargeFinalIso.{m} p O F).inv).1.eq_iff
    ((p.toPresheafFiber_eq_iff' (P := liftedSectionPresheaf.{m} O F) U x
      (ULift.up s) (ULift.up t)).trans ?_)
  exact ⟨fun ⟨V, f, y, hy, heq⟩ => ⟨V, f, y, hy, congrArg ULift.down heq⟩,
    fun ⟨V, f, y, hy, heq⟩ => ⟨V, f, y, hy, congrArg ULift.up heq⟩⟩

end Stacks

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section Germs

variable (X : AlgebraicSpaces B S hS) (x : GeometricPoint B S hS X.1)
  (F : Modules.{u, m} B S hS X.1 X.2)

/-! ### Germs in the stalk at a geometric point of an algebraic space -/

/-- The extension of scalars along `AlgebraicGeometry.Space.pointStalkRingEquiv` defining the
geometric module stalk, as an isomorphism of the underlying additive groups. -/
noncomputable def geometricModuleStalkAddEquiv :
    Stacks.moduleStalkLarge (etaleSitePoint B S hS X.1 x X.2)
        (smallEtaleRingedTopos B S hS X).O F ≃+ geometricModuleStalk B S hS X x F :=
  ModuleCat.extendScalarsRingEquivAddEquiv (pointStalkRingEquiv B S hS X x) _

/-- The additive comparison with the stalk before the extension of scalars is semilinear along
`AlgebraicGeometry.Space.pointStalkRingEquiv`. -/
theorem geometricModuleStalkAddEquiv_smul
    (r : ((etaleSitePoint B S hS X.1 x X.2).presheafFiber (A := CommRingCat.{u})).obj
      (smallEtaleRingedTopos B S hS X).O.obj)
    (z : Stacks.moduleStalkLarge (etaleSitePoint B S hS X.1 x X.2)
      (smallEtaleRingedTopos B S hS X).O F) :
    geometricModuleStalkAddEquiv B S hS X x F (r • z) =
      pointStalkRingEquiv B S hS X x r • geometricModuleStalkAddEquiv B S hS X x F z :=
  ModuleCat.extendScalarsRingEquivAddEquiv_smul _ _ r z

/-- The germ map `F(N) →+ F_x̄` attached to a small étale neighbourhood `N` of a geometric
point `x̄`: a section of `F` over the chart of `N` is sent to its germ in the geometric stalk. -/
noncomputable def geometricModuleStalkGerm (N : SmallEtaleNeighborhood x) :
    F.val.obj (Opposite.op N.chart) →+ geometricModuleStalk B S hS X x F :=
  (geometricModuleStalkAddEquiv B S hS X x F).toAddMonoidHom.comp
    (Stacks.moduleStalkLargeGerm (etaleSitePoint B S hS X.1 x X.2)
      (smallEtaleRingedTopos B S hS X).O F N.chart ⟨N.point, N.point_comp⟩)

/-- The geometric germ of a section is its germ in the stalk before the extension of scalars,
read through `AlgebraicGeometry.Space.geometricModuleStalkAddEquiv`. -/
theorem geometricModuleStalkGerm_apply (N : SmallEtaleNeighborhood x)
    (s : F.val.obj (Opposite.op N.chart)) :
    geometricModuleStalkGerm B S hS X x F N s =
      geometricModuleStalkAddEquiv B S hS X x F
        (Stacks.moduleStalkLargeGerm (etaleSitePoint B S hS X.1 x X.2)
          (smallEtaleRingedTopos B S hS X).O F N.chart ⟨N.point, N.point_comp⟩ s) :=
  rfl

/-- The germ of `r • s` is the germ of the regular function `r` acting on the germ of `s`: the
germ map is semilinear along `AlgebraicGeometry.Space.etaleLocalRingGerm`. -/
theorem geometricModuleStalkGerm_smul (N : SmallEtaleNeighborhood x)
    (r : ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)).obj.obj
      (Opposite.op N.chart))
    (s : F.val.obj (Opposite.op N.chart)) :
    geometricModuleStalkGerm B S hS X x F N (r • s) =
      etaleLocalRingGerm B S hS X.1 x (Opposite.op N) r •
        geometricModuleStalkGerm B S hS X x F N s := by
  refine ((congrArg (geometricModuleStalkAddEquiv B S hS X x F)
      (Stacks.moduleStalkLargeGerm_smul (etaleSitePoint B S hS X.1 x X.2)
        (smallEtaleRingedTopos B S hS X).O F N.chart ⟨N.point, N.point_comp⟩ r s)).trans
    (geometricModuleStalkAddEquiv_smul B S hS X x F _ _)).trans ?_
  exact congrArg (fun c => c • geometricModuleStalkGerm B S hS X x F N s)
    (pointStalkRingEquiv_germ_neighborhood B S hS X x N r)

/-- The germ maps are compatible with restriction to a smaller neighbourhood. -/
theorem geometricModuleStalkGerm_map {N M : SmallEtaleNeighborhood x} (f : M ⟶ N)
    (s : F.val.obj (Opposite.op N.chart)) :
    geometricModuleStalkGerm B S hS X x F M (F.val.map f.hom.op s) =
      geometricModuleStalkGerm B S hS X x F N s :=
  congrArg (geometricModuleStalkAddEquiv B S hS X x F)
    ((Stacks.moduleStalkLargeGerm_w (etaleSitePoint B S hS X.1 x X.2)
      (smallEtaleRingedTopos B S hS X).O F f.hom ⟨M.point, M.point_comp⟩ s).trans
      (congrArg (fun z => Stacks.moduleStalkLargeGerm (etaleSitePoint B S hS X.1 x X.2)
        (smallEtaleRingedTopos B S hS X).O F N.chart z s) (Subtype.ext f.point_comp)))

/-- Every element of the geometric stalk is the germ of a section over some small étale
neighbourhood. -/
theorem geometricModuleStalkGerm_jointly_surjective (z : geometricModuleStalk B S hS X x F) :
    ∃ (N : SmallEtaleNeighborhood x) (s : F.val.obj (Opposite.op N.chart)),
      geometricModuleStalkGerm B S hS X x F N s = z := by
  obtain ⟨V, y, s, hs⟩ := Stacks.moduleStalkLargeGerm_jointly_surjective
    (etaleSitePoint B S hS X.1 x X.2) (smallEtaleRingedTopos B S hS X).O F
    ((geometricModuleStalkAddEquiv B S hS X x F).symm z)
  exact ⟨⟨V, y.1, y.2⟩, s, (congrArg (geometricModuleStalkAddEquiv B S hS X x F) hs).trans
    ((geometricModuleStalkAddEquiv B S hS X x F).apply_symm_apply z)⟩

/-- Two sections over the same neighbourhood have the same germ exactly when they agree after
restriction to some smaller neighbourhood. -/
theorem geometricModuleStalkGerm_eq_iff (N : SmallEtaleNeighborhood x)
    (s t : F.val.obj (Opposite.op N.chart)) :
    geometricModuleStalkGerm B S hS X x F N s = geometricModuleStalkGerm B S hS X x F N t ↔
      ∃ (M : SmallEtaleNeighborhood x) (f : M ⟶ N),
        F.val.map f.hom.op s = F.val.map f.hom.op t := by
  refine Iff.trans (geometricModuleStalkAddEquiv B S hS X x F).injective.eq_iff
    ((Stacks.moduleStalkLargeGerm_eq_iff (etaleSitePoint B S hS X.1 x X.2)
      (smallEtaleRingedTopos B S hS X).O F N.chart ⟨N.point, N.point_comp⟩ s t).trans ?_)
  constructor
  · rintro ⟨V, f, y, hy, heq⟩
    exact ⟨⟨V, y.1, y.2⟩, ⟨f, congrArg Subtype.val hy⟩, heq⟩
  · rintro ⟨M, f, heq⟩
    exact ⟨M.chart, f.hom, ⟨M.point, M.point_comp⟩, Subtype.ext f.point_comp, heq⟩

/-- A section has zero germ exactly when it restricts to zero on some smaller neighbourhood. -/
theorem geometricModuleStalkGerm_eq_zero_iff (N : SmallEtaleNeighborhood x)
    (s : F.val.obj (Opposite.op N.chart)) :
    geometricModuleStalkGerm B S hS X x F N s = 0 ↔
      ∃ (M : SmallEtaleNeighborhood x) (f : M ⟶ N), F.val.map f.hom.op s = 0 := by
  have hzero : ∀ (M : SmallEtaleNeighborhood x) (f : M ⟶ N),
      F.val.map f.hom.op (0 : F.val.obj (Opposite.op N.chart)) = 0 :=
    fun M f => map_zero (ConcreteCategory.hom (F.val.map f.hom.op))
  simpa [hzero] using geometricModuleStalkGerm_eq_iff B S hS X x F N s 0

/-- The geometric stalk is nonzero exactly when some section over some small étale
neighbourhood has nonzero germ. -/
theorem nontrivial_geometricModuleStalk_iff :
    Nontrivial (geometricModuleStalk B S hS X x F) ↔
      ∃ (N : SmallEtaleNeighborhood x) (s : F.val.obj (Opposite.op N.chart)),
        geometricModuleStalkGerm B S hS X x F N s ≠ 0 := by
  refine ⟨fun _ => ?_, fun ⟨N, s, hs⟩ => ⟨_, 0, hs⟩⟩
  obtain ⟨z, hz⟩ := exists_ne (0 : geometricModuleStalk B S hS X x F)
  obtain ⟨N, s, rfl⟩ := geometricModuleStalkGerm_jointly_surjective B S hS X x F z
  exact ⟨N, s, hz⟩

end Germs

/-! ### The stalk of an étale pullback -/

section EtalePullback

variable {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (hf : IsEtale B S hS f.hom)
  (y : GeometricPoint B S hS X.1) (G : Modules.{u, m} B S hS Y.1 Y.2)
  (N : SmallEtaleNeighborhood y)

/-- Two sections of an étale pullback have the same germ at a geometric point of the source
exactly when they have the same germ at its image: the sections are the same, and
postcomposition with an étale morphism is initial on small étale neighbourhoods. -/
theorem geometricModuleStalkGerm_etaleModulePullback_eq_iff
    (s t : ((etaleModulePullback B S hS f hf).obj G).val.obj (Opposite.op N.chart)) :
    geometricModuleStalkGerm B S hS X y ((etaleModulePullback B S hS f hf).obj G) N s =
        geometricModuleStalkGerm B S hS X y ((etaleModulePullback B S hS f hf).obj G) N t ↔
      geometricModuleStalkGerm B S hS Y (geometricPointMap f.hom y) G
          ((SmallEtaleNeighborhood.postcomp B S hS f hf y).obj N) s =
        geometricModuleStalkGerm B S hS Y (geometricPointMap f.hom y) G
          ((SmallEtaleNeighborhood.postcomp B S hS f hf y).obj N) t := by
  let : IsCofiltered (SmallEtaleNeighborhood y) :=
    isCofiltered_smallEtaleNeighborhood B S hS X.1 X.2 y
  let : IsCofiltered (SmallEtaleNeighborhood (geometricPointMap f.hom y)) :=
    isCofiltered_smallEtaleNeighborhood B S hS Y.1 Y.2 (geometricPointMap f.hom y)
  let T := (SmallEtaleNeighborhood.postcomp B S hS f hf y).op
  let D := SmallEtaleNeighborhood.sections (x := geometricPointMap f.hom y)
    (G.val.presheaf ⋙ forget AddCommGrpCat.{m})
  have hbij := bijective_colimitTypePrecomp_smallEtaleNeighborhoodPostcomp B S hS f hf y
    (G.val.presheaf ⋙ forget AddCommGrpCat.{m})
  refine Iff.trans (geometricModuleStalkGerm_eq_iff B S hS X y _ N s t)
    (Iff.trans ?_ (geometricModuleStalkGerm_eq_iff B S hS Y (geometricPointMap f.hom y) G
      ((SmallEtaleNeighborhood.postcomp B S hS f hf y).obj N) s t).symm)
  have h : (T ⋙ D).ιColimitType (Opposite.op N) s = (T ⋙ D).ιColimitType (Opposite.op N) t ↔
      D.ιColimitType (Opposite.op ((SmallEtaleNeighborhood.postcomp B S hS f hf y).obj N)) s =
        D.ιColimitType (Opposite.op ((SmallEtaleNeighborhood.postcomp B S hS f hf y).obj N)) t :=
    hbij.1.eq_iff.symm
  have key : (∃ (k : (SmallEtaleNeighborhood y)ᵒᵖ) (g : Opposite.op N ⟶ k),
        (T ⋙ D).map g s = (T ⋙ D).map g t) ↔
      ∃ (k : (SmallEtaleNeighborhood (geometricPointMap f.hom y))ᵒᵖ)
        (g : Opposite.op ((SmallEtaleNeighborhood.postcomp B S hS f hf y).obj N) ⟶ k),
        D.map g s = D.map g t :=
    (Functor.ιColimitType_eq_iff_of_isFiltered' (F := T ⋙ D) (j := Opposite.op N) s t).symm.trans
      (h.trans (Functor.ιColimitType_eq_iff_of_isFiltered' (F := D)
        (j := Opposite.op ((SmallEtaleNeighborhood.postcomp B S hS f hf y).obj N)) s t))
  constructor
  · rintro ⟨M, g, hg⟩
    obtain ⟨W, k, hk⟩ := key.mp ⟨Opposite.op M, g.op, hg⟩
    exact ⟨W.unop, k.unop, hk⟩
  · rintro ⟨W, k, hk⟩
    obtain ⟨M, g, hg⟩ := key.mpr ⟨Opposite.op W, k.op, hk⟩
    exact ⟨M.unop, g.unop, hg⟩

/-- A section of an étale pullback has zero germ at a geometric point of the source exactly
when it has zero germ at the image point. -/
theorem geometricModuleStalkGerm_etaleModulePullback_eq_zero_iff
    (s : ((etaleModulePullback B S hS f hf).obj G).val.obj (Opposite.op N.chart)) :
    geometricModuleStalkGerm B S hS X y ((etaleModulePullback B S hS f hf).obj G) N s = 0 ↔
      geometricModuleStalkGerm B S hS Y (geometricPointMap f.hom y) G
        ((SmallEtaleNeighborhood.postcomp B S hS f hf y).obj N) s = 0 :=
  Iff.trans ⟨fun h => h.trans (map_zero _).symm, fun h => h.trans (map_zero _)⟩
    (Iff.trans (geometricModuleStalkGerm_etaleModulePullback_eq_iff B S hS f hf y G N s 0)
      ⟨fun h => h.trans (map_zero _), fun h => h.trans (map_zero _).symm⟩)

/-- The stalk of an étale pullback at a geometric point of the source is nonzero exactly when
the stalk of the original module at the image point is. -/
theorem nontrivial_geometricModuleStalk_etaleModulePullback_iff :
    Nontrivial (geometricModuleStalk B S hS X y ((etaleModulePullback B S hS f hf).obj G)) ↔
      Nontrivial (geometricModuleStalk B S hS Y (geometricPointMap f.hom y) G) := by
  have := SmallEtaleNeighborhood.initial_postcomp B S hS f hf y
  rw [nontrivial_geometricModuleStalk_iff, nontrivial_geometricModuleStalk_iff]
  constructor
  · rintro ⟨M, s, hs⟩
    exact ⟨(SmallEtaleNeighborhood.postcomp B S hS f hf y).obj M, s, fun h => hs
      ((geometricModuleStalkGerm_etaleModulePullback_eq_zero_iff B S hS f hf y G M s).mpr h)⟩
  · rintro ⟨W, s, hs⟩
    obtain ⟨A⟩ := (inferInstance :
      Nonempty (CostructuredArrow (SmallEtaleNeighborhood.postcomp B S hS f hf y) W))
    refine ⟨A.left, G.val.map A.hom.hom.op s, fun h => hs ?_⟩
    rw [← geometricModuleStalkGerm_map B S hS Y (geometricPointMap f.hom y) G A.hom s]
    exact (geometricModuleStalkGerm_etaleModulePullback_eq_zero_iff B S hS f hf y G A.left
      (G.val.map A.hom.hom.op s)).mp h

end EtalePullback

end AlgebraicGeometry.Space

end
