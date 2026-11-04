module

public import StacksFrontier.CategoryTheory.Sites.Modules.PointRingedSite
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedToposHom
public import StacksFrontier.CategoryTheory.Sites.MorphismOfSitesLimits

/-!
# The punctual ringed topos of a ring, and global sections as a morphism of ringed topoi

For a commutative ring `R` the punctual ringed topos `(pt, R)` is the one-object site with the
trivial topology and the constant structure sheaf `R`.  If a ringed site `(C, 𝒪)` has a terminal
object `T`, a ring map `φ : R ⟶ 𝒪(T)` is a morphism of ringed topoi `(Sh(C), 𝒪) ⟶ (pt, R)`
presented by the functor of sites `pt ⥤ C` picking out `T`.  Its direct image is the global
sections functor `F ↦ F(T)` read as an `R`-module, and its inverse image sends an `R`-module `M`
to the sheaf associated with `U ↦ 𝒪(U) ⊗_R M`.

The functor picking out a terminal object is a morphism of sites: every comma category `V ↓ T`
has the initial object `V ⟶ T`, so it is representably flat.

## Main definitions

* `AlgebraicGeometry.pointRingedTopos`: the punctual ringed topos of a commutative ring, the
  one-point ringed site `Stacks.PointRingedSite.site` read as a ringed topos.
* `AlgebraicGeometry.toPointRingedTopos`: the morphism to it given by a terminal object and a
  ring map into the sections over it.

## Main results

* `AlgebraicGeometry.representablyFlat_const_of_isTerminal`: the functor picking out a terminal
  object is representably flat.
* `AlgebraicGeometry.isMorphismOfSites_toPointRingedTopos`: the functor underlying
  `AlgebraicGeometry.toPointRingedTopos` is a morphism of sites.

## References

* [Stacks Project, Tag 00X1](https://stacks.math.columbia.edu/tag/00X1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

/-- The punctual ringed topos of a commutative ring `R`: the one-point ringed site
`Stacks.PointRingedSite.site R` (one object, the trivial topology and the constant structure
sheaf `R`), as a `RingedTopos`. -/
def pointRingedTopos (R : CommRingCat.{u}) : RingedTopos.{u, u, u} where
  C := (Stacks.PointRingedSite.site R).C
  J := (Stacks.PointRingedSite.site R).J
  O := (Stacks.PointRingedSite.site R).O

/-- The underlying category of `pointRingedTopos R` is the one-object category `Discrete PUnit`. -/
@[simp]
theorem pointRingedTopos_C (R : CommRingCat.{u}) :
    (pointRingedTopos R).C = Discrete PUnit.{u + 1} := rfl

/-- The topology of `pointRingedTopos R` is the trivial topology `⊥`. -/
@[simp]
theorem pointRingedTopos_J (R : CommRingCat.{u}) :
    (pointRingedTopos R).J = ⊥ := rfl

variable (X : RingedTopos.{u, u, u}) {T : X.C} (hT : IsTerminal T)

/-- Every functor out of the punctual site is continuous: every presheaf on it is a sheaf. -/
instance isContinuous_const_pointRingedTopos (R : CommRingCat.{u}) :
    ((Functor.const (pointRingedTopos R).C).obj T).IsContinuous (pointRingedTopos R).J X.J :=
  ⟨fun _ => Presieve.isSheaf_bot⟩

include hT in
/-- The functor of sites picking out a terminal object is representably flat: the comma
category `V ↓ T` has the initial object `V ⟶ T`. -/
theorem representablyFlat_const_of_isTerminal (R : CommRingCat.{u}) :
    RepresentablyFlat ((Functor.const (pointRingedTopos R).C).obj T) where
  cofiltered V := IsCofiltered.of_isInitial _
    (X := StructuredArrow.mk (T := (Functor.const (pointRingedTopos R).C).obj T)
      (Y := (⟨PUnit.unit⟩ : Discrete PUnit.{u + 1}))
      (hT.from V : V ⟶ ((Functor.const (pointRingedTopos R).C).obj T).obj ⟨PUnit.unit⟩))
    (IsInitial.ofUniqueHom
      (fun _ => StructuredArrow.homMk (Discrete.eqToHom (Subsingleton.elim _ _))
        (hT.hom_ext _ _))
      (fun _ _ => StructuredArrow.ext _ _
        (@Subsingleton.elim _ (Discrete.instSubsingletonDiscreteHom _ _) _ _)))

/-- The morphism of ringed topoi `(Sh(C), 𝒪) ⟶ (pt, R)` given by a terminal object `T` of the
site and a ring map `φ : R ⟶ 𝒪(T)`: its functor of sites picks out `T`, and its structure map
is `φ`. -/
def toPointRingedTopos {R : CommRingCat.{u}} (φ : R ⟶ X.O.obj.obj (op T)) :
    RingedToposSiteHom X (pointRingedTopos R) where
  u := (Functor.const (pointRingedTopos R).C).obj T
  fSharp := ⟨{
    app := fun _ => φ
    naturality := fun _ _ _ => by
      change 𝟙 R ≫ φ = φ ≫ X.O.obj.map (𝟙 (op T))
      simp }⟩

/-- The functor of sites underlying `toPointRingedTopos X φ` is the constant functor at `T`. -/
@[simp]
theorem toPointRingedTopos_u {R : CommRingCat.{u}} (φ : R ⟶ X.O.obj.obj (op T)) :
    (toPointRingedTopos X φ).u = (Functor.const (pointRingedTopos R).C).obj T := rfl

include hT in
/-- If `T` is terminal, the functor underlying `AlgebraicGeometry.toPointRingedTopos` is a
morphism of sites. -/
theorem isMorphismOfSites_toPointRingedTopos {R : CommRingCat.{u}}
    (φ : R ⟶ X.O.obj.obj (op T)) :
    (toPointRingedTopos X φ).u.IsMorphismOfSites (pointRingedTopos R).J X.J :=
  have : RepresentablyFlat (toPointRingedTopos X φ).u :=
    representablyFlat_const_of_isTerminal X hT R
  Functor.isMorphismOfSites_of_representablyFlat _ _ _

end AlgebraicGeometry

end
