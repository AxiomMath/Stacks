module

public import Mathlib.Algebra.Category.Grp.Ulift
public import Mathlib.Algebra.Category.ModuleCat.Stalk
public import StacksFrontier.AlgebraicGeometry.Spaces.RingedSite
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleRingedToposHom
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleSitePoint
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ModuleStalkFunctor

/-!
# The stalk of a module at a geometric point of an algebraic space

Let `X` be an algebraic space and `x̄` a geometric point of it. The small étale site of `X`
has a point `Φ_x̄` whose fibre functor sends an étale chart to the lifts of `x̄` into it, and
the stalk of the structure sheaf at `Φ_x̄` is therefore the étale local ring `𝒪_{X, x̄}` of
Stacks 04KG, up to the universe lift separating the two models of that colimit. This file
supplies that comparison and uses it to present the stalk of an `𝒪_X`-module `F` at `Φ_x̄` as
a module over `𝒪_{X, x̄}` itself.

## Main definitions

* `Stacks.moduleStalkLarge` is the stalk of a sheaf of modules at a point of a site, with the
  universe of the module sections independent of the universe of the sheaf of rings.
* `AlgebraicGeometry.Space.pointStalkRingEquiv` is the isomorphism between the stalk of the
  structure sheaf at the point of the small étale site and the étale local ring.
* `AlgebraicGeometry.Space.geometricModuleStalk` is the stalk of an `𝒪_X`-module at a
  geometric point, as a module over the étale local ring.

## Main results

* `AlgebraicGeometry.Space.pointStalkRingEquiv_germ` and
  `AlgebraicGeometry.Space.pointStalkRingEquiv_germ_neighborhood`: the comparison sends the
  germ of a regular function to the germ of the same function, so it is the identity in
  germs.

## Implementation notes

The two models of the stalk of the structure sheaf differ only in the indexing category of
the colimit — the elements of the geometric fibre functor on one side, the small étale
neighbourhoods on the other — and in a universe lift, since the étale local ring is formed in
`CommRingCat.{u + 1}` while the fibre of a point of the site is formed in `CommRingCat.{u}`.
The comparison is produced as a bijective ring map out of the neighbourhood colimit, and it is
packaged together with its normalisation on germs, since nothing about the colimit presentation
is needed downstream beyond that normalisation.

The module stalk is the stalk at the point of the site, carried along the comparison by
extension of scalars, which is the categorical form of the tensor product.

`Stacks.moduleStalk` pins the universe of the module sections to the universe of the sheaf of
rings, whereas an `𝒪_X`-module in the sense of `AlgebraicGeometry.Space.Modules` has its
sections in an independent universe `m`. `Stacks.moduleStalkLarge` is therefore formed here
directly: the colimit of the module sections over a small final model of the category of
neighbourhoods of the point, raised to `max w m` by `AddCommGrpCat.uliftFunctor`, with its
scalars restricted along the comparison of the ring colimit with the `CommRingCat`-valued
stalk of the sheaf of rings.

## References

* [Stacks Project, Tag 05VQ](https://stacks.math.columbia.edu/tag/05VQ)
* [Stacks Project, Tag 04KG](https://stacks.math.columbia.edu/tag/04KG)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u m v w t

attribute [local instance] FinallySmall.preservesColimitsOfShape_of_isFiltered

namespace Stacks

variable {C : Type t} [Category.{v} C] [LocallySmall.{w} C]
  {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]

/-- The stalk at a point `p` of a site of a sheaf of modules over the ring sheaf of a sheaf of
commutative rings `O`, as a module over the `CommRingCat`-valued stalk of `O`, with the
universe `m` of the module sections independent of the universe `w` of `O`.

It is the filtered colimit of the module sections over a small final model of the category of
neighbourhoods of `p`, with the sections raised to `max w m`, and with its scalars restricted
along the comparison of the colimit of the section rings with the stalk of `O`.
`Stacks.moduleStalk` is the same colimit at `m = w`, where the universe lift is vacuous. -/
noncomputable def moduleStalkLarge (p : J.Point.{w}) (O : Sheaf J CommRingCat.{w})
    (F : SheafOfModules.{m} (commRingSheafToRingSheaf O)) :
    ModuleCat.{max w m} ((p.presheafFiber (A := CommRingCat.{w})).obj O.obj) :=
  let D := FinallySmall.FilteredFinalModel.{w} (p.fiber.Elementsᵒᵖ)
  let G : D ⥤ p.fiber.Elementsᵒᵖ := FinallySmall.fromFilteredFinalModel _
  let R := G ⋙ (Functor.Elements.π p.fiber).op ⋙ (commRingSheafToRingSheaf O).obj
  let M := G ⋙ (Functor.Elements.π p.fiber).op ⋙
    F.val.presheaf ⋙ AddCommGrpCat.uliftFunctor.{w}
  let cR := colimit.cocone R
  let hR : IsColimit cR := colimit.isColimit R
  let cM := colimit.cocone M
  let hM : IsColimit cM := colimit.isColimit M
  letI (i : D) : Module (R.obj i) (M.obj i) := by
    change Module _ (ULift (F.val.obj _))
    letI : Module ((commRingSheafToRingSheaf O).obj.obj
        ((Functor.Elements.π p.fiber).op.obj (G.obj i)))
        (F.val.obj ((Functor.Elements.π p.fiber).op.obj (G.obj i))) :=
      (F.val.obj _).isModule
    infer_instance
  letI : Module cR.pt cM.pt :=
    IsColimit.module R M (fun {i j} f r x => by
      let : Module (R.obj i)
          (F.val.presheaf.obj ((Functor.Elements.π p.fiber).op.obj (G.obj i))) :=
        (F.val.obj _).isModule
      let : Module (R.obj j)
          (F.val.presheaf.obj ((Functor.Elements.π p.fiber).op.obj (G.obj j))) :=
        (F.val.obj _).isModule
      change ULift.up (F.val.map _ (r • x.down)) = ULift.up (_ • F.val.map _ x.down)
      congr 1
      exact F.val.map_smul _ _ _) hR hM
  let e : cR.pt ≅ (forget₂ CommRingCat RingCat).obj
      ((p.presheafFiber (A := CommRingCat.{w})).obj O.obj) :=
    Functor.Final.colimitIso G _ ≪≫
      (preservesColimitIso (forget₂ CommRingCat RingCat)
        ((Functor.Elements.π p.fiber).op ⋙ O.obj)).symm
  (ModuleCat.restrictScalars e.inv.hom).obj (ModuleCat.of cR.pt cM.pt)

end Stacks

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The comparison of the stalk of the structure sheaf at the point of the small étale site
with the étale local ring, together with its normalisation on every germ of a regular
function on a small étale neighbourhood. -/
noncomputable def pointStalkRingEquivData (X : AlgebraicSpaces B S hS)
    (x : GeometricPoint B S hS X.1) :
    { e : ((etaleSitePoint B S hS X.1 x X.2).presheafFiber (A := CommRingCat.{u})).obj
        (smallEtaleRingedTopos B S hS X).O.obj ≃+* etaleLocalRing B S hS X.1 x //
      ∀ (U : SmallEtaleNeighborhood x)
        (a : (structurePresheaf B S hS X.1).obj (Opposite.op U.chart)),
        e ((etaleSitePoint B S hS X.1 x X.2).toPresheafFiber U.chart ⟨U.point, U.point_comp⟩
            (smallEtaleRingedTopos B S hS X).O.obj a) =
          etaleLocalRingGerm B S hS X.1 x (Opposite.op U) a } := by
  let p := etaleSitePoint B S hS X.1 x X.2
  let O := (smallEtaleRingedTopos B S hS X).O.obj
  let D := SmallEtaleNeighborhood.sections (x := x) (liftedStructurePresheaf B S hS X.1)
  letI : IsCofiltered (SmallEtaleNeighborhood x) :=
    isCofiltered_smallEtaleNeighborhood B S hS X.1 X.2 x
  letI : PreservesColimitsOfShape (SmallEtaleNeighborhood x)ᵒᵖ
      (forget CommRingCat.{u + 1}) :=
    preservesColimitsOfShape_of_equiv
      (AsSmall.equiv.{u, u + 1, u + 1}
        (C := (SmallEtaleNeighborhood x)ᵒᵖ)).symm _
  let c : Cocone D :=
    { pt := CommRingCat.of
        (ULift.{u + 1} ((p.presheafFiber (A := CommRingCat.{u})).obj O))
      ι :=
        { app := fun U => CommRingCat.ofHom
            (p.toPresheafFiber U.unop.chart
              ⟨U.unop.point, U.unop.point_comp⟩ O).hom.ulift
          naturality := by
            intro U V f
            ext a
            change ULift.up (p.toPresheafFiber V.unop.chart
                ⟨V.unop.point, V.unop.point_comp⟩ O
                (O.map f.unop.hom.op a.down)) =
              ULift.up (p.toPresheafFiber U.unop.chart
                ⟨U.unop.point, U.unop.point_comp⟩ O a.down)
            congr 1
            have hp : p.fiber.map f.unop.hom
                ⟨V.unop.point, V.unop.point_comp⟩ =
                ⟨U.unop.point, U.unop.point_comp⟩ :=
              Subtype.ext f.unop.point_comp
            simpa only [hp] using p.toPresheafFiber_w_apply f.unop.hom
              ⟨V.unop.point, V.unop.point_comp⟩ O a.down } }
  let q := (colimit.desc D c).hom
  have hq (U : (SmallEtaleNeighborhood x)ᵒᵖ) (a : D.obj U) :
      q (colimit.ι D U a) =
        ULift.up (p.toPresheafFiber U.unop.chart
          ⟨U.unop.point, U.unop.point_comp⟩ O a.down) :=
    ConcreteCategory.congr_hom (colimit.ι_desc c U) a
  have hbij : Function.Bijective q := by
    refine ⟨fun a b hab => ?_, fun a => ?_⟩
    · obtain ⟨U, a, b, rfl, rfl⟩ :=
        Types.FilteredColimit.jointly_surjective_of_isColimit₂
          (isColimitOfPreserves (forget CommRingCat.{u + 1}) (colimit.isColimit D)) a b
      have hab' := congrArg ULift.down hab
      change (q (colimit.ι D U a)).down = (q (colimit.ι D U b)).down at hab'
      rw [hq, hq] at hab'
      obtain ⟨V, f, v, hv, hab''⟩ :=
        (p.toPresheafFiber_eq_iff' U.unop.chart
          ⟨U.unop.point, U.unop.point_comp⟩ a.down b.down).mp hab'
      let W : SmallEtaleNeighborhood x := ⟨V, v.1, v.2⟩
      let g : W ⟶ U.unop := ⟨f, congrArg Subtype.val hv⟩
      exact (ConcreteCategory.congr_hom (colimit.w D g.op) a).symm.trans
        ((congrArg (colimit.ι D (Opposite.op W))
          (show D.map g.op a = D.map g.op b from congrArg ULift.up hab'')).trans
          (ConcreteCategory.congr_hom (colimit.w D g.op) b))
    · obtain ⟨U, v, s, hs⟩ := p.toPresheafFiber_jointly_surjective a.down
      refine ⟨colimit.ι D (Opposite.op ⟨U, v.1, v.2⟩) (ULift.up s), ?_⟩
      rw [hq]
      change ULift.up (p.toPresheafFiber U v O s) = a
      exact congrArg ULift.up hs
  let e := RingEquiv.ofBijective q hbij
  refine ⟨ULift.ringEquiv.symm.trans e.symm, fun U a => e.injective ?_⟩
  change e (e.symm (ULift.up (p.toPresheafFiber U.chart
      ⟨U.point, U.point_comp⟩ O a))) =
    q (colimit.ι D (Opposite.op U) (ULift.up a))
  rw [e.apply_symm_apply, hq]

/-- The stalk of the structure sheaf at the point of the small étale site determined by a
geometric point is the étale local ring at that geometric point. -/
noncomputable def pointStalkRingEquiv (X : AlgebraicSpaces B S hS)
    (x : GeometricPoint B S hS X.1) :
    ((etaleSitePoint B S hS X.1 x X.2).presheafFiber (A := CommRingCat.{u})).obj
      (smallEtaleRingedTopos B S hS X).O.obj ≃+* etaleLocalRing B S hS X.1 x :=
  (pointStalkRingEquivData B S hS X x).1

/-- The comparison with the étale local ring sends the germ at a lift of the geometric point
of a regular function on an étale chart to the germ of that function on the corresponding
small étale neighbourhood. -/
theorem pointStalkRingEquiv_germ_neighborhood (X : AlgebraicSpaces B S hS)
    (x : GeometricPoint B S hS X.1) (U : SmallEtaleNeighborhood x)
    (a : (structurePresheaf B S hS X.1).obj (Opposite.op U.chart)) :
    pointStalkRingEquiv B S hS X x
        ((etaleSitePoint B S hS X.1 x X.2).toPresheafFiber U.chart ⟨U.point, U.point_comp⟩
          (smallEtaleRingedTopos B S hS X).O.obj a) =
      etaleLocalRingGerm B S hS X.1 x (Opposite.op U) a :=
  (pointStalkRingEquivData B S hS X x).2 U a

/-- The comparison with the étale local ring read off a lift of the geometric point into an
étale chart rather than a small étale neighbourhood. -/
theorem pointStalkRingEquiv_germ (X : AlgebraicSpaces B S hS)
    (x : GeometricPoint B S hS X.1) (U : SmallEtale B S hS X.1)
    (p : GeometricFiber B S hS X.1 x U)
    (a : (structurePresheaf B S hS X.1).obj (Opposite.op U)) :
    pointStalkRingEquiv B S hS X x
        ((etaleSitePoint B S hS X.1 x X.2).toPresheafFiber U p
          (structurePresheaf B S hS X.1) a) =
      etaleLocalRingGerm B S hS X.1 x (Opposite.op ⟨U, p.1, p.2⟩) a :=
  pointStalkRingEquiv_germ_neighborhood B S hS X x ⟨U, p.1, p.2⟩ a

/-- **Stacks 05VQ.** The stalk of an `𝒪_X`-module at a geometric point `x̄` of an algebraic
space, as a module over the étale local ring `𝒪_{X, x̄}`: the stalk at the point of the small
étale site determined by `x̄`, with its scalars extended along
`AlgebraicGeometry.Space.pointStalkRingEquiv`. -/
@[stacks 05VQ "the module stalk at a geometric point"]
noncomputable def geometricModuleStalk (X : AlgebraicSpaces B S hS)
    (x : GeometricPoint B S hS X.1) (F : Modules.{u, m} B S hS X.1 X.2) :
    ModuleCat (etaleLocalRing B S hS X.1 x) :=
  (ModuleCat.extendScalars (pointStalkRingEquiv B S hS X x).toRingHom).obj
    (Stacks.moduleStalkLarge (etaleSitePoint B S hS X.1 x X.2)
      (smallEtaleRingedTopos B S hS X).O F)

end AlgebraicGeometry.Space

end
