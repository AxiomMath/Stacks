module

public import StacksFrontier.AlgebraicGeometry.Spaces.GlobalFunctionsSmall
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleSmallModel
public import StacksFrontier.AlgebraicGeometry.Spaces.SpacesEtaleEssentiallySmall
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SpacesEtaleStructureSheaf
public import StacksFrontier.CategoryTheory.Sites.Modules.PointRingedTopos
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedToposHom
public import StacksFrontier.CategoryTheory.Sites.MorphismOfSitesLimits
public import StacksFrontier.CategoryTheory.Sites.Topos.ToposReplacement
public import Mathlib.Algebra.Ring.Shrink

/-!
# A `Type u`-presented model of the ringed spaces-étale site of an algebraic space

Let `X` be an algebraic space over a scheme `S` of universe `u`.  Its spaces-étale site
`X_{spaces,étale}` (Stacks 03G0) has objects and morphisms in `Type (u + 1)`, and the ring of
global regular functions of an algebraic space étale over `X` is, as written, a `Type (u + 1)`.
The site is essentially small at `u` (`AlgebraicGeometry.Space.essentiallySmall_spacesEtale`) and
every ring of global functions is `u`-small (`AlgebraicGeometry.Space.small_globalFunctions`), so
the ringed site has a model in which objects, morphisms and rings of sections all lie in `Type u`:
an `AlgebraicGeometry.RingedTopos.{u, u, u}`.

The point of this model, as opposed to the model
`AlgebraicGeometry.Space.smallEtaleModelRingedTopos` of the small étale site of *schemes* étale
over `X`, is functoriality.  A morphism `f : X ⟶ Y` induces the base-change functor
`V ↦ V ×_Y X` from the spaces-étale site of `Y` to that of `X` (Stacks 03G2, part (1)), which is a
morphism of sites; the fibre product of a scheme étale over `Y` with `X` is in general only an
algebraic space, so no such functor exists between the small étale sites of schemes.  On the
models the base change becomes an `AlgebraicGeometry.RingedToposSiteHom` whose functor is a
morphism of sites, which is the form in which the derived pullback of Stacks 07A6, its tensor
compatibility of Stacks 07A4 and the projection formula map of Stacks 0B56 are available.

## Main definitions

* `CategoryTheory.shrinkCommRingPresheaf`: the sectionwise `m`-small model of a presheaf of
  commutative rings with `m`-small values.
* `AlgebraicGeometry.Space.SpacesEtale.smallStructureSheaf`: the structure sheaf of the
  spaces-étale site with values in `CommRingCat.{u}`.
* `AlgebraicGeometry.Space.spacesEtaleModelRingedTopos`: **the model**, a
  `RingedTopos.{u, u, u}`.
* `AlgebraicGeometry.Space.spacesEtaleModelHom`: the morphism of models induced by a morphism of
  algebraic spaces: base change on the sites and pullback of regular functions along the
  cartesian projections on the structure sheaves.
* `AlgebraicGeometry.Space.spacesEtaleModelToPoint`: the morphism from the model to the punctual
  ringed topos `(pt, R)` given by a ring map `R ⟶ Γ(X, 𝒪_X)`; its functor of sites picks out the
  terminal object `X` of the spaces-étale site.

## Main results

* `CategoryTheory.isSheaf_shrinkCommRingPresheaf`: shrinking preserves the sheaf condition.
* `AlgebraicGeometry.Space.isDenseSubsite_spacesEtaleModelComparison`: the comparison
  `AlgebraicGeometry.Space.spacesEtaleModelComparison` of the model of the small étale site of `X`
  with the model of its spaces-étale site (Stacks 03G1) exhibits the former as a dense subsite.
* `AlgebraicGeometry.Space.isMorphismOfSites_spacesEtaleModelHom` and
  `AlgebraicGeometry.Space.isMorphismOfSites_spacesEtaleModelToPoint`: the functors underlying
  these two morphisms are morphisms of sites (Stacks 00X1).

## References

* [Stacks Project, Tag 03G0](https://stacks.math.columbia.edu/tag/03G0)
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe m t v₁ u₁ u

/-! ### Shrinking a presheaf of commutative rings with small values -/

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C]

/-- The sectionwise `m`-small model of a presheaf of commutative rings whose values are
`m`-small: the sections over `X` become `Shrink (P(X))`, with the restriction maps conjugated by
`Shrink.ringEquiv`. -/
def shrinkCommRingPresheaf (P : Cᵒᵖ ⥤ CommRingCat.{max m t}) [∀ X, Small.{m} (P.obj X)] :
    Cᵒᵖ ⥤ CommRingCat.{m} where
  obj X := CommRingCat.of (Shrink.{m} (P.obj X))
  map {X Y} f := CommRingCat.ofHom ((Shrink.ringEquiv (P.obj Y)).symm.toRingHom.comp
    ((P.map f).hom.comp (Shrink.ringEquiv (P.obj X)).toRingHom))
  map_id X := by ext x; simp
  map_comp f g := by ext x; simp

/-- Under `Shrink.ringEquiv`, the restriction maps of `CategoryTheory.shrinkCommRingPresheaf P`
are those of `P`. -/
@[simp]
theorem shrinkCommRingPresheaf_map_apply (P : Cᵒᵖ ⥤ CommRingCat.{max m t})
    [∀ X, Small.{m} (P.obj X)] {X Y : Cᵒᵖ} (f : X ⟶ Y)
    (x : (shrinkCommRingPresheaf.{m, t} P).obj X) :
    Shrink.ringEquiv (P.obj Y) ((shrinkCommRingPresheaf.{m, t} P).map f x) =
      (P.map f).hom (Shrink.ringEquiv (P.obj X) x) :=
  (Shrink.ringEquiv (P.obj Y)).apply_symm_apply _

/-- Shrinking a morphism of presheaves of commutative rings with small values. -/
def shrinkCommRingPresheafMap {P Q : Cᵒᵖ ⥤ CommRingCat.{max m t}} [∀ X, Small.{m} (P.obj X)]
    [∀ X, Small.{m} (Q.obj X)] (τ : P ⟶ Q) :
    shrinkCommRingPresheaf.{m, t} P ⟶ shrinkCommRingPresheaf.{m, t} Q where
  app X := CommRingCat.ofHom ((Shrink.ringEquiv (Q.obj X)).symm.toRingHom.comp
    ((τ.app X).hom.comp (Shrink.ringEquiv (P.obj X)).toRingHom))
  naturality X Y f := CommRingCat.hom_ext (RingHom.ext fun x => by
    apply (Shrink.ringEquiv (Q.obj Y)).injective
    change Shrink.ringEquiv (Q.obj Y) ((Shrink.ringEquiv (Q.obj Y)).symm ((τ.app Y).hom
        (Shrink.ringEquiv (P.obj Y) ((Shrink.ringEquiv (P.obj Y)).symm
          ((P.map f).hom (Shrink.ringEquiv (P.obj X) x)))))) =
      Shrink.ringEquiv (Q.obj Y) ((Shrink.ringEquiv (Q.obj Y)).symm ((Q.map f).hom
        (Shrink.ringEquiv (Q.obj X) ((Shrink.ringEquiv (Q.obj X)).symm
          ((τ.app X).hom (Shrink.ringEquiv (P.obj X) x))))))
    simp only [RingEquiv.apply_symm_apply]
    exact congrArg (fun g => g.hom (Shrink.ringEquiv (P.obj X) x)) (τ.naturality f))

/-- Shrinking preserves the sheaf condition: a ring map from `E` into `Shrink (P(X))` is a ring
map from `ULift E` into `P(X)`, naturally in `X`. -/
theorem isSheaf_shrinkCommRingPresheaf {J : GrothendieckTopology C}
    (P : Cᵒᵖ ⥤ CommRingCat.{max m t}) [∀ X, Small.{m} (P.obj X)] (hP : Presheaf.IsSheaf J P) :
    Presheaf.IsSheaf J (shrinkCommRingPresheaf.{m, t} P) := by
  intro E
  refine Presieve.isSheaf_of_nat_equiv
    (P₁ := P ⋙ coyoneda.obj (op (CommRingCat.of (ULift.{max m t} E))))
    (fun X => {
      toFun := fun g => CommRingCat.ofHom ((Shrink.ringEquiv (P.obj (op X))).symm.toRingHom.comp
        (g.hom.comp (ULift.ringEquiv (R := E)).symm.toRingHom))
      invFun := fun g => CommRingCat.ofHom ((Shrink.ringEquiv (P.obj (op X))).toRingHom.comp
        (g.hom.comp (ULift.ringEquiv (R := E)).toRingHom))
      left_inv := fun g => CommRingCat.hom_ext (RingHom.ext fun x => by
        show Shrink.ringEquiv (P.obj (op X)) ((Shrink.ringEquiv (P.obj (op X))).symm
          (g.hom ((ULift.ringEquiv (R := E)).symm (ULift.ringEquiv.{m, max m t} x)))) = g.hom x
        simp only [RingEquiv.apply_symm_apply, RingEquiv.symm_apply_apply])
      right_inv := fun g => CommRingCat.hom_ext (RingHom.ext fun x => by
        show (Shrink.ringEquiv (P.obj (op X))).symm (Shrink.ringEquiv (P.obj (op X))
          (g.hom (ULift.ringEquiv.{m, max m t} ((ULift.ringEquiv (R := E)).symm x)))) = g.hom x
        rw [RingEquiv.apply_symm_apply]
        exact (Shrink.ringEquiv (P.obj (op X))).symm_apply_apply (g.hom x)) })
    (fun X Y f x => ?_) (hP _)
  refine CommRingCat.hom_ext (RingHom.ext fun r => ?_)
  apply (Shrink.ringEquiv (P.obj (op X))).injective
  show Shrink.ringEquiv (P.obj (op X)) ((Shrink.ringEquiv (P.obj (op X))).symm
      ((P.map f.op).hom (x.hom ((ULift.ringEquiv.{m, max m t} (R := E)).symm r)))) =
    Shrink.ringEquiv (P.obj (op X)) ((Shrink.ringEquiv (P.obj (op X))).symm ((P.map f.op).hom
      (Shrink.ringEquiv (P.obj (op Y)) ((Shrink.ringEquiv (P.obj (op Y))).symm
        (x.hom ((ULift.ringEquiv.{m, max m t} (R := E)).symm r))))))
  simp only [RingEquiv.apply_symm_apply]

end CategoryTheory

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The structure sheaf of the spaces-étale site in `Type u` -/

namespace SpacesEtale

variable (X : AlgebraicSpaces B S hS)

/-- The ring of global regular functions of an algebraic space étale over `X` is `u`-small. -/
instance small_structurePresheaf_obj (V : (SpacesEtale B S hS X)ᵒᵖ) :
    Small.{u} ((structurePresheaf B S hS X).obj V) :=
  small_globalFunctions B S hS ((toSpaces B S hS X).obj V.unop)

/-- The structure sheaf of the spaces-étale site of `X` with values in `CommRingCat.{u}`: the
ring of global regular functions of an algebraic space étale over `X`, which is `u`-small, read
in `Type u`. -/
def smallStructureSheaf : Sheaf (topology B S hS X) CommRingCat.{u} :=
  ⟨shrinkCommRingPresheaf.{u, u + 1} (structurePresheaf B S hS X),
    isSheaf_shrinkCommRingPresheaf _ (structurePresheaf_isSheaf B S hS X)⟩

end SpacesEtale

/-! ### The model -/

variable (X : AlgebraicSpaces B S hS)

/-- The structure sheaf of the model of the spaces-étale site of `X`: the restriction of
`AlgebraicGeometry.Space.SpacesEtale.smallStructureSheaf` along the comparison with the small
model. -/
abbrev spacesEtaleModelStructureSheaf :
    Sheaf (smallModelTopology B S hS X) CommRingCat.{u} :=
  ((equivSmallModel.{u} (SpacesEtale B S hS X)).inverse.sheafPushforwardContinuous
    CommRingCat.{u} (smallModelTopology B S hS X) (SpacesEtale.topology B S hS X)).obj
      (SpacesEtale.smallStructureSheaf B S hS X)

/-- **The `Type u`-presented model of the ringed spaces-étale site of `X`.**  Its site is the
small model of `X_{spaces,étale}` with the induced topology and its structure sheaf the
`u`-small structure sheaf restricted to it. -/
def spacesEtaleModelRingedTopos : RingedTopos.{u, u, u} where
  C := SmallModel.{u} (SpacesEtale B S hS X)
  J := smallModelTopology B S hS X
  O := spacesEtaleModelStructureSheaf B S hS X

/-- The site of `AlgebraicGeometry.Space.spacesEtaleModelRingedTopos` is the small model of the
spaces-étale site of `X`. -/
@[simp]
theorem spacesEtaleModelRingedTopos_C :
    (spacesEtaleModelRingedTopos B S hS X).C = SmallModel.{u} (SpacesEtale B S hS X) := rfl

/-- The topology of `AlgebraicGeometry.Space.spacesEtaleModelRingedTopos` is the topology
induced on the small model. -/
@[simp]
theorem spacesEtaleModelRingedTopos_J :
    (spacesEtaleModelRingedTopos B S hS X).J = smallModelTopology B S hS X := rfl

/-- The structure sheaf of `AlgebraicGeometry.Space.spacesEtaleModelRingedTopos` is
`AlgebraicGeometry.Space.spacesEtaleModelStructureSheaf`. -/
@[simp]
theorem spacesEtaleModelRingedTopos_O :
    (spacesEtaleModelRingedTopos B S hS X).O = spacesEtaleModelStructureSheaf B S hS X := rfl

/-! ### Functoriality -/

variable {X} {Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)

/-- The structure map of base change on the spaces-étale sites, read on the model of `X`: a
regular function on `V` étale over `Y` is pulled back along the cartesian projection
`V ×_Y X ⟶ V`, and then along the comparison of `V ×_Y X` with its image in the small model. -/
def spacesEtaleBaseChangeSharp :
    SpacesEtale.structurePresheaf B S hS Y ⟶
      (spacesBaseChange B S hS f).functor.op ⋙
        ((equivSmallModel.{u} (SpacesEtale B S hS X)).functor ⋙
          (equivSmallModel.{u} (SpacesEtale B S hS X)).inverse).op ⋙
            SpacesEtale.structurePresheaf B S hS X :=
  Functor.whiskerRight (NatTrans.op (spacesBaseChange B S hS f).projection)
      (globalFunctionsPresheaf B S hS) ≫
    Functor.whiskerLeft (spacesBaseChange B S hS f).functor.op
      (Functor.whiskerRight (NatTrans.op (Functor.whiskerRight
        (equivSmallModel.{u} (SpacesEtale B S hS X)).unitIso.inv
        (SpacesEtale.toSpaces B S hS X))) (globalFunctionsPresheaf B S hS))

/-- The functor of models underlying `AlgebraicGeometry.Space.spacesEtaleModelHom` is a morphism
of sites (Stacks 00X1): base change on the spaces-étale sites is representably flat, and so are
the two comparisons with the small models, being equivalences. -/
theorem isMorphismOfSites_smallModelBaseChange :
    (smallModelBaseChange B S hS f).IsMorphismOfSites (smallModelTopology B S hS Y)
      (smallModelTopology B S hS X) :=
  Functor.isMorphismOfSites_of_representablyFlat _ _ _

/-- **The morphism of models of ringed spaces-étale sites induced by `f : X ⟶ Y`.**  The
underlying functor is base change `V ↦ V ×_Y X` (Stacks 03G2, part (1)) transported to the small
models, and the structure map pulls a regular function back along the cartesian projection
(Stacks 03G8). -/
def spacesEtaleModelHom :
    RingedToposSiteHom (spacesEtaleModelRingedTopos B S hS X)
      (spacesEtaleModelRingedTopos B S hS Y) :=
  haveI : ∀ V, Small.{u} (((spacesBaseChange B S hS f).functor.op ⋙
      ((equivSmallModel.{u} (SpacesEtale B S hS X)).functor ⋙
        (equivSmallModel.{u} (SpacesEtale B S hS X)).inverse).op ⋙
          SpacesEtale.structurePresheaf B S hS X).obj V) := fun _ =>
    small_globalFunctions B S hS _
  { u := smallModelBaseChange B S hS f
    isContinuous := isContinuous_smallModelBaseChange B S hS f
    fSharp := ⟨Functor.whiskerLeft (equivSmallModel.{u} (SpacesEtale B S hS Y)).inverse.op
      (shrinkCommRingPresheafMap.{u, u + 1} (spacesEtaleBaseChangeSharp B S hS f))⟩ }

/-- The functor of sites underlying `AlgebraicGeometry.Space.spacesEtaleModelHom f` is
`AlgebraicGeometry.Space.smallModelBaseChange`. -/
@[simp]
theorem spacesEtaleModelHom_u :
    (spacesEtaleModelHom B S hS f).u = smallModelBaseChange B S hS f := rfl

/-- The functor underlying `AlgebraicGeometry.Space.spacesEtaleModelHom` is a morphism of
sites. -/
theorem isMorphismOfSites_spacesEtaleModelHom :
    (spacesEtaleModelHom B S hS f).u.IsMorphismOfSites (spacesEtaleModelRingedTopos B S hS Y).J
      (spacesEtaleModelRingedTopos B S hS X).J :=
  isMorphismOfSites_smallModelBaseChange B S hS f

/-! ### The morphism to the punctual ringed topos of a ring -/

variable (X) in
/-- The image in the model of the terminal object `X` of the spaces-étale site of `X`. -/
abbrev spacesEtaleModelTerminal : SmallModel.{u} (SpacesEtale B S hS X) :=
  (equivSmallModel.{u} (SpacesEtale B S hS X)).functor.obj (SpacesEtale.idObj B S hS X)

variable (X) in
/-- `AlgebraicGeometry.Space.spacesEtaleModelTerminal` is terminal in the model. -/
def isTerminal_spacesEtaleModelTerminal : IsTerminal (spacesEtaleModelTerminal B S hS X) :=
  (SpacesEtale.isTerminal_idObj B S hS X).isTerminalObj _

/-- A ring map `ψ : R → Γ(X, 𝒪_X)` read as a ring map into the sections of the structure sheaf of
the model over its terminal object. -/
def spacesEtaleModelGlobalHom {R : CommRingCat.{u}}
    (ψ : R →+* (SpacesEtale.structurePresheaf B S hS X).obj (op (SpacesEtale.idObj B S hS X))) :
    R ⟶ (spacesEtaleModelStructureSheaf B S hS X).obj.obj
      (op (spacesEtaleModelTerminal B S hS X)) :=
  CommRingCat.ofHom ((Shrink.ringEquiv _).symm.toRingHom.comp
    (((SpacesEtale.structurePresheaf B S hS X).map
      ((equivSmallModel.{u} (SpacesEtale B S hS X)).unitIso.inv.app
        (SpacesEtale.idObj B S hS X)).op).hom.comp ψ))

/-- **The morphism of ringed topoi `(X_{spaces,étale}, 𝒪_X) ⟶ (pt, R)` given by a ring map
`ψ : R ⟶ Γ(X, 𝒪_X)`**, presented on the model: its functor of sites picks out the terminal
object `X`, so that its direct image is the global sections functor read as `R`-modules, and its
structure map is `ψ`.  For `ψ` the ring map of a morphism `X ⟶ Spec(R)` this is the morphism
whose projection formula is the case of Stacks 08IN used in the proof of Stacks 0D3F. -/
def spacesEtaleModelToPoint {R : CommRingCat.{u}}
    (ψ : R →+* (SpacesEtale.structurePresheaf B S hS X).obj (op (SpacesEtale.idObj B S hS X))) :
    RingedToposSiteHom (spacesEtaleModelRingedTopos B S hS X) (pointRingedTopos R) :=
  toPointRingedTopos (spacesEtaleModelRingedTopos B S hS X) (spacesEtaleModelGlobalHom B S hS ψ)

/-- The functor underlying `AlgebraicGeometry.Space.spacesEtaleModelToPoint` is a morphism of
sites (Stacks 00X1). -/
theorem isMorphismOfSites_spacesEtaleModelToPoint {R : CommRingCat.{u}}
    (ψ : R →+* (SpacesEtale.structurePresheaf B S hS X).obj (op (SpacesEtale.idObj B S hS X))) :
    (spacesEtaleModelToPoint B S hS ψ).u.IsMorphismOfSites (pointRingedTopos R).J
      (spacesEtaleModelRingedTopos B S hS X).J :=
  isMorphismOfSites_toPointRingedTopos (spacesEtaleModelRingedTopos B S hS X)
    (isTerminal_spacesEtaleModelTerminal B S hS X) _

/-! ### Comparison with the model of the small étale site -/

variable (X) in
/-- The comparison functor of Stacks 03G1, an étale scheme chart of `X` being an algebraic space
étale over `X`, transported to the two small models. -/
abbrev spacesEtaleModelComparison :
    SmallModel.{u} (SmallEtale B S hS X.1) ⥤ SmallModel.{u} (SpacesEtale B S hS X) :=
  (smallEtaleModelEquiv B S hS X).inverse ⋙ comparisonFunctor B S hS X ⋙
    (equivSmallModel.{u} (SpacesEtale B S hS X)).functor

variable (X) in
/-- **Stacks 03G1 on the models.** The model of the small étale site of `X` is a dense subsite of
the model of its spaces-étale site: the comparison is a composite of two equivalences with the
dense inclusion of the small étale site into the spaces-étale site. -/
instance isDenseSubsite_spacesEtaleModelComparison :
    (spacesEtaleModelComparison B S hS X).IsDenseSubsite (smallEtaleModelTopology B S hS X.1)
      (smallModelTopology B S hS X) :=
  have : (comparisonFunctor B S hS X ⋙
      (equivSmallModel.{u} (SpacesEtale B S hS X)).functor).IsDenseSubsite
      (SmallEtale.topology B S hS X.1) (smallModelTopology B S hS X) :=
    Functor.isDenseSubsite_comp _ (SpacesEtale.topology B S hS X) _ _ _
  Functor.isDenseSubsite_comp _ (SmallEtale.topology B S hS X.1) _ _ _

end AlgebraicGeometry.Space

end
