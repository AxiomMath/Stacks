module

public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.RingCohomologyMapConstruction
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedModulePullback
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleStalkStructureMap
public import StacksFrontier.CategoryTheory.Sites.Point.ModuleStalkDerived
public import StacksCore.Tactic.StacksAttribute

/-!
# The pointwise base-change map on geometric stalkwise cohomology of algebraic spaces

Let

```
X' --g'--> X
|          |
f'         f
v          v
Y' --g---> Y
```

be a commutative square of algebraic spaces over a scheme `S` contained in a big fppf site `B`,
let `K` be an object of `D(𝒪_X)`, let `K'` be an object of `D(𝒪_{X'})` and let
`φ : L(g')^*K ⟶ K'`.  For a geometric point `x̄'` of `X'` with images `x̄ = g'(x̄')`,
`ȳ' = f'(x̄')` and `ȳ = f(x̄) = g(ȳ')`, Equation 0DKF is the map

`H^i(K_x̄ ⊗ᴸ_{𝒪_{Y,ȳ}} 𝒪_{Y',ȳ'}) ⊗_{(𝒪_{X,x̄} ⊗_{𝒪_{Y,ȳ}} 𝒪_{Y',ȳ'})} 𝒪_{X',x̄'} ⟶ H^i(K'_x̄')`

of `𝒪_{X',x̄'}`-modules.  This file constructs it.  No cartesianness, Tor independence,
quasi-coherence or finiteness is required; the square need only commute, exactly as in the
scheme-level Equation 0DJ7 of
`StacksFrontier/AlgebraicGeometry/BaseChange/TorIndependence/StalkCohomologyMap.lean`.

## Main definitions

* `AlgebraicGeometry.Space.geometricDerivedStalk` is the derived geometric stalk
  `D(𝒪_X) ⥤ D(𝒪_{X,x̄})` at a geometric point.
* `AlgebraicGeometry.Space.geometricBaseStalkMap` is the map `𝒪_{Y,ȳ} ⟶ 𝒪_{Y',ȳ'}` of the
  square, the stalk map of `g` transported along the agreement of the two images of `x̄'` in
  `Y`.
* `AlgebraicGeometry.Space.geometricStalkBaseChangeCohomologyMap` is the map of Equation 0DKF.

## Main results

* `AlgebraicGeometry.Space.geometricPointMap_square`: the two images of `x̄'` in `Y` agree.
* `AlgebraicGeometry.Space.stalkStructureMap_square`: the four geometric stalk maps of the
  square commute, which is what makes the four geometric stalks a commutative square of rings.

## Implementation notes

*The shape.*  The map is a morphism in `ModuleCat 𝒪_{X',x̄'}`, one for each `x̄'` and each `i`.
That is what its consumers need: Stacks 0DKG and 0DKH use Equation 0DKF only through the
condition *"for any `x̄'` and `i` the map (0DKF) is an isomorphism"*, so `IsIso` has to apply to
it.  A bundled isomorphism candidate would beg their question, and a natural transformation
would be the wrong object: naturality holds in `K'`, whereas `x̄'` and `i` vary pointwise and
not along any functor.

*The geometric stalks.*  The four rings are `AlgebraicGeometry.Space.geometricStalkRing`, the
fibre of the structure sheaf at the point of the small étale site attached to the geometric
point by Stacks 04K0.  These are objects of `CommRingCat.{u}`, in the same universe as the
modules, which is what lets the ring-level construction apply; the étale local ring of
Stacks 04KG is the same ring one universe up, and
`AlgebraicGeometry.Space.pointStalkRingEquiv` is the comparison.  The derived geometric stalk
is `Stacks.derivedModuleFiber`, whose module universe is independent of the two universes of
the site — the small étale site has its objects in `Type (u + 1)` and its structure sheaf's
sections in `Type u`.

*The ring maps.*  The four maps of geometric stalks are
`AlgebraicGeometry.Space.stalkStructureMap`, the fibres of the inverse-image structure maps of
the morphisms of small étale ringed topoi of Stacks 03G8.  `stalkStructureMap_square` proves
that they commute, by transporting them to the étale local rings with
`AlgebraicGeometry.Space.stalkStructureMapAsEtaleLocalRingMap_eq` and applying the composition
law `AlgebraicGeometry.Space.etaleLocalRingMap_comp` of Stacks 04NG on each way round.  The
two images of `x̄'` in `Y` are equal rather than identical, so the leg along `g` carries a
transport; this is the analogue of the use of `TopCat.Presheaf.stalkCongr` in the scheme-level
file.

*What is constructed and what is assumed.*  The map is **constructed**, not chosen: its body is
`RingTheory.TorIndependence.ringBaseChangeCohomologyMap`, the image under the
extension/restriction-of-scalars adjunction of an `𝒪_{X,x̄} ⊗_{𝒪_{Y,ȳ}} 𝒪_{Y',ȳ'}`-linear
comparison.  Two premises are carried in the signature.

The first is the instance argument
`Functor.HasLeftDerivedFunctor`, carried exactly as
`AlgebraicGeometry.Space.smallEtaleDerivedModulePullback` carries it: `L(g')^*` of Stacks 06YY
exists once `g'^*` has a resolving datum, and the resolving half at the K-flat class is
Stacks 06YS, which this tree states only for a site which is
`CategoryTheory.SmallCategory`.  The small étale site is only *essentially* small, and the pin
is mathematics and not convenience — 077J's ladder is indexed by sections over the site's
objects, which on the small étale site live one universe above the modules, so the direct sum
indexing it does not exist in `SheafOfModules.{u}`.  See the implementation notes of
`StacksFrontier/CategoryTheory/Sites/Cohomology/DerivedPullback/StalkCriterionPartOne.lean` and of
`StacksFrontier/AlgebraicGeometry/Spaces/DerivedModulePushforward.lean`, which record the same
pin.

The second is the morphism `ps`, the derived pullback-stalk comparison
`K_x̄ ⊗ᴸ_{𝒪_{X,x̄}} 𝒪_{X',x̄'} ⟶ (L(g')^*K)_x̄'`.  The source states this as an equality,
`(L(g')^*K)_x̄' = K_x̄ ⊗ᴸ_{𝒪_{X,x̄}} 𝒪_{X',x̄'}`, and for *schemes* it is
`AlgebraicGeometry.derivedPullbackStalkIso`; for algebraic spaces nothing in this tree
constructs it at any universe, so it is a hypothesis here and the construction is complete
relative to it.  It is the only piece of Equation 0DKF's input that is assumed: everything
downstream of it — the module structure on the source, the Stacks 065Z comparison, the
adjunction — is built.

## References

* [Stacks Project, Tag 0DKF](https://stacks.math.columbia.edu/tag/0DKF)
* [Stacks Project, Tag 0DJ7](https://stacks.math.columbia.edu/tag/0DJ7)
* [Stacks Project, Tag 06YY](https://stacks.math.columbia.edu/tag/06YY)
* [Stacks Project, Tag 04NG](https://stacks.math.columbia.edu/tag/04NG)
* [Stacks Project, Tag 04K0](https://stacks.math.columbia.edu/tag/04K0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open RingTheory.TorIndependence
open scoped TensorProduct
open scoped ChangeOfRings

namespace AlgebraicGeometry.Space

universe u

attribute [local instance 10000] HasDerivedCategory.standard

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The derived geometric stalk -/

/-- **The derived geometric stalk of an algebraic space.** The functor
`D(𝒪_X) ⥤ D(𝒪_{X,x̄})` induced by the exact stalk functor at the point of the small étale site
of Stacks 04K0 attached to a geometric point `x̄`.  It sends an object `K` of `D(𝒪_X)` to the
object the source writes `K_x̄`. -/
abbrev geometricDerivedStalk {X : AlgebraicSpaces B S hS} (x : GeometricPoint B S hS X.1) :
    DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) ⥤
      DerivedCategory (ModuleCat.{u} (geometricStalkRing B S hS x)) :=
  Stacks.derivedModuleFiber (etaleSitePoint B S hS X.1 x X.2)
    (smallEtaleRingedTopos B S hS X).O

/-! ### The commutative square of geometric stalks -/

variable {X X' Y Y' : AlgebraicSpaces B S hS}

/-- The two images in `Y` of a geometric point of `X'`, one along `g' ≫ f` and one along
`f' ≫ g`, agree. -/
theorem geometricPointMap_square (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X)
    (w : g' ≫ f = f' ≫ g) (x' : GeometricPoint B S hS X'.1) :
    geometricPointMap f.hom (geometricPointMap g'.hom x') =
      geometricPointMap g.hom (geometricPointMap f'.hom x') :=
  congrArg (fun m : X' ⟶ Y => geometricPointMap m.hom x') w

/-- **The base stalk map of a commutative square of algebraic spaces.** The fibre of the
structure map of `g` at `ȳ' = f'(x̄')`, read as a homomorphism out of the geometric stalk of `Y`
at `ȳ = f(g'(x̄'))` by transport along `geometricPointMap_square`. -/
def geometricBaseStalkMap (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X)
    (w : g' ≫ f = f' ≫ g) (x' : GeometricPoint B S hS X'.1) :
    geometricStalkRing B S hS (geometricPointMap f.hom (geometricPointMap g'.hom x')) ⟶
      geometricStalkRing B S hS (geometricPointMap f'.hom x') :=
  eqToHom (congrArg (fun z : GeometricPoint B S hS Y.1 => geometricStalkRing B S hS (X := Y) z)
      (geometricPointMap_square B S hS f g f' g' w x')) ≫
    stalkStructureMap B S hS g (geometricPointMap f'.hom x')

/-- The fibre of the structure map, read through the comparison of Stacks 05VQ, is the
canonical homomorphism of étale local rings of Stacks 04NG.  This is the pointwise form of
`AlgebraicGeometry.Space.stalkStructureMapAsEtaleLocalRingMap_eq`. -/
private theorem pointStalkRingEquiv_stalkStructureMap (f : X ⟶ Y)
    (x : GeometricPoint B S hS X.1)
    (z : geometricStalkRing B S hS (geometricPointMap f.hom x)) :
    pointStalkRingEquiv B S hS X x ((stalkStructureMap B S hS f x).hom z) =
      etaleLocalRingMap X.2 f.hom x
        (pointStalkRingEquiv B S hS Y (geometricPointMap f.hom x) z) := by
  rw [← stalkStructureMapAsEtaleLocalRingMap_eq B S hS f x]
  exact congrArg
    (fun t => pointStalkRingEquiv B S hS X x ((stalkStructureMap B S hS f x).hom t))
    (RingEquiv.symm_apply_apply
      (pointStalkRingEquiv B S hS Y (geometricPointMap f.hom x)) z).symm

/-- Transporting a geometric stalk along an equality of geometric points agrees, under the
comparison of Stacks 05VQ, with transporting the étale local ring. -/
private theorem pointStalkRingEquiv_eqToHom {Z : AlgebraicSpaces B S hS}
    {z₁ z₂ : GeometricPoint B S hS Z.1} (h : z₁ = z₂)
    (t : geometricStalkRing B S hS z₁) :
    pointStalkRingEquiv B S hS Z z₂
        ((eqToHom (congrArg (fun z : GeometricPoint B S hS Z.1 =>
          geometricStalkRing B S hS (X := Z) z) h)).hom t) =
      (eqToHom (congrArg (etaleLocalRing B S hS Z.1) h)).hom
        (pointStalkRingEquiv B S hS Z z₁ t) := by
  subst h
  simp

/-- The canonical homomorphism of étale local rings of Stacks 04NG, transported along an
equality of the inducing morphisms. -/
private theorem etaleLocalRingMap_eq_of_morphism_eq
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hF : IsAlgebraicSpace B S hS F)
    {m m' : F ⟶ G} (h : m = m') (x : GeometricPoint B S hS F)
    (t : etaleLocalRing B S hS G (geometricPointMap m x)) :
    etaleLocalRingMap hF m x t =
      etaleLocalRingMap hF m' x
        ((eqToHom (congrArg (etaleLocalRing B S hS G)
          (congrArg (fun k => geometricPointMap k x) h))).hom t) := by
  subst h
  simp

/-- The canonical homomorphisms of étale local rings of Stacks 04NG compose, pointwise. -/
private theorem etaleLocalRingMap_comp_apply {F G H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F) (hG : IsAlgebraicSpace B S hS G) (f : F ⟶ G) (g : G ⟶ H)
    (x : GeometricPoint B S hS F) (t : etaleLocalRing B S hS H (geometricPointMap g
      (geometricPointMap f x))) :
    etaleLocalRingMap hF f x (etaleLocalRingMap hG g (geometricPointMap f x) t) =
      etaleLocalRingMap hF (f ≫ g) x t :=
  RingHom.congr_fun (etaleLocalRingMap_comp hF hG f g x) t

/-- **The square of geometric stalk rings of a commutative square of algebraic spaces
commutes.** Going round by `X` and going round by `Y'` give the same homomorphism
`𝒪_{Y,ȳ} ⟶ 𝒪_{X',x̄'}`.  This is what makes the four geometric stalks a commutative square of
rings, and it is the scalar tower the ring-level construction of Equation 0DKF consumes.

The four fibres of the structure maps are compared to the canonical homomorphisms of étale
local rings of Stacks 04NG by
`AlgebraicGeometry.Space.stalkStructureMapAsEtaleLocalRingMap_eq`, where the composition law
`AlgebraicGeometry.Space.etaleLocalRingMap_comp` applies on each way round.  The two images of
`x̄'` in `Y` are equal rather than identical, so the leg along `g` carries a transport. -/
theorem stalkStructureMap_square (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X)
    (w : g' ≫ f = f' ≫ g) (x' : GeometricPoint B S hS X'.1) :
    (stalkStructureMap B S hS g' x').hom.comp
        (stalkStructureMap B S hS f (geometricPointMap g'.hom x')).hom =
      (stalkStructureMap B S hS f' x').hom.comp
        (geometricBaseStalkMap B S hS f g f' g' w x').hom := by
  have hw : g'.hom ≫ f.hom = f'.hom ≫ g.hom := congrArg (fun m : X' ⟶ Y => m.hom) w
  refine RingHom.ext fun z => (pointStalkRingEquiv B S hS X' x').injective ?_
  have hpt : geometricPointMap f.hom (geometricPointMap g'.hom x') =
      geometricPointMap g.hom (geometricPointMap f'.hom x') :=
    geometricPointMap_square B S hS f g f' g' w x'
  set eY := pointStalkRingEquiv B S hS Y
    (geometricPointMap f.hom (geometricPointMap g'.hom x')) with heY
  -- the two ways round, pushed to the étale local rings
  have hC := pointStalkRingEquiv_stalkStructureMap B S hS g' x'
    ((stalkStructureMap B S hS f (geometricPointMap g'.hom x')).hom z)
  have hA := pointStalkRingEquiv_stalkStructureMap B S hS f
    (geometricPointMap g'.hom x') z
  have hE := pointStalkRingEquiv_stalkStructureMap B S hS f' x'
    ((geometricBaseStalkMap B S hS f g f' g' w x').hom z)
  have hG := pointStalkRingEquiv_stalkStructureMap B S hS g
    (geometricPointMap f'.hom x')
    ((eqToHom (congrArg (fun zz : GeometricPoint B S hS Y.1 =>
        geometricStalkRing B S hS (X := Y) zz) hpt)).hom z)
  have hT := pointStalkRingEquiv_eqToHom B S hS (Z := Y) hpt z
  have hL := etaleLocalRingMap_comp_apply B S hS X'.2 X.2 g'.hom f.hom x' (eY z)
  have hR := etaleLocalRingMap_comp_apply B S hS X'.2 Y'.2 f'.hom g.hom x'
    ((eqToHom (congrArg (etaleLocalRing B S hS Y.1) hpt)).hom (eY z))
  have hM := etaleLocalRingMap_eq_of_morphism_eq B S hS X'.2 hw x' (eY z)
  rw [RingHom.comp_apply, RingHom.comp_apply, hC, hA, hE, geometricBaseStalkMap,
    CommRingCat.hom_comp, RingHom.comp_apply, hG, hT, hL, hR]
  exact hM

/-! ### Equation 0DKF -/

/-- **Stacks Project, Equation 0DKF.** The canonical map

`H^n(K_x̄ ⊗ᴸ_{𝒪_{Y,ȳ}} 𝒪_{Y',ȳ'}) ⊗_{(𝒪_{X,x̄} ⊗_{𝒪_{Y,ȳ}} 𝒪_{Y',ȳ'})} 𝒪_{X',x̄'} ⟶ H^n(K'_x̄')`

of `𝒪_{X',x̄'}`-modules attached to a commutative square of algebraic spaces, a geometric point
`x̄'` of `X'`, objects `K` of `D(𝒪_X)` and `K'` of `D(𝒪_{X'})` and a morphism
`φ : L(g')^*K ⟶ K'`.  No cartesianness, Tor independence or quasi-coherence is required.

It is built, not chosen: the `𝒪_{X,x̄} ⊗_{𝒪_{Y,ȳ}} 𝒪_{Y',ȳ'}`-module structure on the source is
`RingTheory.TorIndependence.baseChangeCohomologyModule` and the map is
`RingTheory.TorIndependence.ringBaseChangeCohomologyMap`, the adjoint of the Stacks 065Z
comparison followed by `φ`.

Two premises are carried, and the construction is complete relative to them.  The instance
argument `Functor.HasLeftDerivedFunctor` is the existence of `L(g')^*` itself, carried as
`AlgebraicGeometry.Space.smallEtaleDerivedModulePullback` carries it, because the K-flat
resolutions of Stacks 06YS are available in this tree only on a site which is
`CategoryTheory.SmallCategory`.  The morphism `ps` is the derived pullback-stalk comparison
`K_x̄ ⊗ᴸ_{𝒪_{X,x̄}} 𝒪_{X',x̄'} ⟶ (L(g')^*K)_x̄'`, which the source states as an equality and
which nothing in this tree constructs for algebraic spaces. -/
@[stacks 0DKF "the map, given the derived pullback-stalk comparison `ps`"]
def geometricStalkBaseChangeCohomologyMap
    (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X) (w : g' ≫ f = f' ≫ g)
    (x' : GeometricPoint B S hS X'.1)
    [(smallEtaleModulePullbackOnHomotopy B S hS g').HasLeftDerivedFunctor
      (smallEtaleModuleQuasiIso B S hS X)]
    (K : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
    (K' : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X')))
    (φ : (smallEtaleDerivedModulePullback B S hS g').obj K ⟶ K')
    (ps : (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
          (stalkStructureMap B S hS g' x').hom).functor.obj
        ((geometricDerivedStalk B S hS (geometricPointMap g'.hom x')).obj K) ⟶
      (geometricDerivedStalk B S hS x').obj
        ((smallEtaleDerivedModulePullback B S hS g').obj K))
    (n : ℤ) :=
  let R := geometricStalkRing B S hS (geometricPointMap f.hom (geometricPointMap g'.hom x'))
  let A := geometricStalkRing B S hS (geometricPointMap g'.hom x')
  let R' := geometricStalkRing B S hS (geometricPointMap f'.hom x')
  let A' := geometricStalkRing B S hS x'
  let a := (stalkStructureMap B S hS f (geometricPointMap g'.hom x')).hom
  let b := (geometricBaseStalkMap B S hS f g f' g' w x').hom
  let c := (stalkStructureMap B S hS g' x').hom
  let e := (stalkStructureMap B S hS f' x').hom
  letI : Algebra R A := a.toAlgebra
  letI : Algebra R R' := b.toAlgebra
  letI : Algebra R A' := (c.comp a).toAlgebra
  letI : Algebra A A' := c.toAlgebra
  letI : Algebra R' A' := e.toAlgebra
  letI : IsScalarTower R A A' := IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower R R' A' :=
    IsScalarTower.of_algebraMap_eq' (stalkStructureMap_square B S hS f g f' g' w x')
  ringBaseChangeCohomologyMap (R := R) (A := A) (R' := R') (A' := A')
    ((geometricDerivedStalk B S hS (geometricPointMap g'.hom x')).obj K)
    ((geometricDerivedStalk B S hS x').obj K')
    (ps ≫ (geometricDerivedStalk B S hS x').map φ) n

end AlgebraicGeometry.Space

end
