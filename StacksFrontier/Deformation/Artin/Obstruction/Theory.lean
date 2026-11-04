module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Module.RingHom
public import Mathlib.CategoryTheory.Linear.LinearFunctor
public import StacksCore.CategoryTheory.FiberedInGroupoidsEquiv
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.FiberedCategory.ChoiceOfPullbacks
public import StacksFrontier.Deformation.Artin.SquareZeroDifference

/-!
# Obstruction theories

An *obstruction theory* for a category fibred in groupoids over the big fppf site of a base
scheme `S` assigns, to every object `x` of the category lying over the spectrum of an
`S`-algebra `A` whose structure morphism maps into an affine open of `S`, an `A`-linear
endofunctor `𝒪_x` of the category of `A`-modules — the *obstruction modules* at `x`. These
endofunctors are functorial in the triple `(x, A, M)`, and every deformation situation
`(x, A' → A)` carries an *obstruction element* in the obstruction module of the kernel
`I = Ker(A' → A)`, which vanishes exactly when `x` extends to an object over `Spec A'`.

## Main definitions

* `Deformation.Artin.LinearEndofunctor` — an `A`-linear endofunctor of `Mod_A`: a functor of
  obstruction modules.
* `Deformation.Artin.SiteAlgebra` — an `S`-algebra whose spectrum is an object of the chosen
  big fppf site, with its structure morphism, and `Deformation.Artin.SiteAlgebra.Hom` a map
  of such algebras.
* `Deformation.Artin.MapsIntoAffineOpen` — the condition that `Spec A → S` maps into an
  affine open.
* `Deformation.Artin.AffineObject` — an object of the fibred category over the spectrum of
  such an algebra, and `Deformation.Artin.AffineObject.Hom` a morphism of such.
* `Deformation.Artin.DeformationSituation` — the bundled algebraic datum of a deformation
  situation over a site algebra: a square-zero surjection `A' → A` in the site; its kernel
  is `Deformation.Artin.DeformationSituation.kernelObj`.
* `Deformation.Artin.AffineObject.HasLift` — the category of lifts of an object across a
  deformation situation is nonempty.
* `Deformation.Artin.ObstructionTheory` — an obstruction theory.

## References

* [Stacks Project, Tag 07YG](https://stacks.math.columbia.edu/tag/07YG)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u v w

namespace Deformation.Artin

/-! ### Linear functors of obstruction modules -/

/-- An `A`-linear endofunctor of the category of `A`-modules. -/
@[ega "III 7.1.2"]
public structure LinearEndofunctor (A : Type u) [CommRing A] where
  /-- The underlying functor `Mod_A ⥤ Mod_A`. -/
  functor : ModuleCat.{u} A ⥤ ModuleCat.{u} A
  [additive : functor.Additive]
  [linear : functor.Linear A]

attribute [instance] LinearEndofunctor.additive LinearEndofunctor.linear

/-! ### Algebras and deformation situations in the site -/

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A morphism of schemes to `S` maps into an affine open of `S`. -/
public def MapsIntoAffineOpen {Y : Scheme.{u}} (f : Y ⟶ S) : Prop :=
  ∃ U : S.Opens, IsAffineOpen U ∧ ∀ y : Y, f.base y ∈ U

/-- An `S`-algebra whose spectrum is an object of the chosen big fppf site. -/
public structure SiteAlgebra where
  /-- The underlying ring. -/
  carrier : Type u
  [commRing : CommRing carrier]
  /-- Its spectrum occurs in the chosen big fppf site. -/
  mem : B.Contains (Spec (.of carrier))
  /-- The structure morphism to the base, inside the site. -/
  toBase : B.obj mem ⟶ B.obj hS

attribute [instance] SiteAlgebra.commRing

namespace SiteAlgebra

variable {B S hS}

/-- The spectrum of a site algebra as an object of the big fppf site over `S`. -/
public abbrev over (a : SiteAlgebra B S hS) : BigFppfOver B S hS := Over.mk a.toBase

/-- The structure morphism of a site algebra, as a morphism of schemes. -/
public abbrev toScheme (a : SiteAlgebra B S hS) : Spec (.of a.carrier) ⟶ S :=
  B.inclusion.map a.toBase

/-- A map of `S`-algebras between site algebras: the ring map together with the morphism
over `S` that it induces on spectra. -/
public structure Hom (a b : SiteAlgebra B S hS) where
  /-- The underlying ring map. -/
  ringMap : a.carrier →+* b.carrier
  /-- The induced morphism of spectra over `S`. -/
  specMap : b.over ⟶ a.over
  /-- The morphism of spectra is the one determined by the ring map. -/
  specMap_spec : B.inclusion.map specMap.left = Spec.map (CommRingCat.ofHom ringMap)

/-- The identity map of `S`-algebras. -/
public abbrev Hom.id (a : SiteAlgebra B S hS) : Hom a a where
  ringMap := RingHom.id a.carrier
  specMap := 𝟙 a.over
  specMap_spec := by
    rw [Over.id_left, CategoryTheory.Functor.map_id, CommRingCat.ofHom_id, Spec.map_id]
    rfl

/-- The composition of two maps of `S`-algebras. -/
public abbrev Hom.comp {a b c : SiteAlgebra B S hS} (f : Hom a b) (g : Hom b c) : Hom a c where
  ringMap := g.ringMap.comp f.ringMap
  specMap := g.specMap ≫ f.specMap
  specMap_spec := by
    rw [Over.comp_left, CategoryTheory.Functor.map_comp, f.specMap_spec, g.specMap_spec,
      CommRingCat.ofHom_comp, Spec.map_comp]

end SiteAlgebra

/-- The algebraic datum of a deformation situation over a site algebra `A`: a surjection
`A' → A` of `S`-algebras in the site whose kernel has square zero. -/
public structure DeformationSituation (a : SiteAlgebra B S hS) where
  /-- The thickened algebra `A'`. -/
  top : SiteAlgebra B S hS
  /-- The surjection `A' → A`, as a map of `S`-algebras. -/
  hom : SiteAlgebra.Hom top a
  /-- The map `A' → A` is surjective. -/
  surjective : Function.Surjective hom.ringMap
  /-- The kernel of `A' → A` has square zero. -/
  sq_eq_bot : RingHom.ker hom.ringMap ^ 2 = ⊥

namespace DeformationSituation

variable {B S hS} {a : SiteAlgebra B S hS}

/-- The canonical module structure of the quotient ring on the kernel of a deformation
situation. -/
@[instance_reducible]
public def kernelModule (t : DeformationSituation B S hS a) :
    Module a.carrier (RingHom.ker t.hom.ringMap) :=
  Stacks.Smooth.kerModule t.surjective t.sq_eq_bot

/-- The kernel `I = Ker(A' → A)` of a deformation situation as an object of `Mod_A`. -/
public def kernelObj (t : DeformationSituation B S hS a) : ModuleCat.{u} a.carrier :=
  letI := t.kernelModule
  ModuleCat.of a.carrier (RingHom.ker t.hom.ringMap)

/-- The element of `A'` underlying an element of the kernel of a deformation situation. -/
public def kernelVal (t : DeformationSituation B S hS a) (z : (t.kernelObj : Type u)) :
    t.top.carrier :=
  z.1

end DeformationSituation

/-! ### Objects over an affine base in the site -/

variable {X : Type v} [Category.{w} X] (p : X ⥤ BigFppfOver B S hS)

/-- An object of the fibred category over the spectrum of an `S`-algebra `A`, where `Spec A`
lies in the site and `Spec A → S` maps into an affine open of `S`. -/
public structure AffineObject where
  /-- The `S`-algebra `A`. -/
  alg : SiteAlgebra B S hS
  /-- The structure morphism `Spec A → S` maps into an affine open. -/
  mapsIntoAffineOpen : MapsIntoAffineOpen S alg.toScheme
  /-- The object `x` of the fibred category over `Spec A`. -/
  obj : p.Fiber alg.over

namespace AffineObject

variable {B S hS} {X : Type v} [Category.{w} X] {p : X ⥤ BigFppfOver B S hS}

/-- A morphism `(x, A) → (y, A₁)`: a map of `S`-algebras `A → A₁` together with a morphism
`y ⟶ x` of the fibred category lifting `Spec A₁ ⟶ Spec A`. -/
public structure Hom (P Q : AffineObject B S hS p) where
  /-- The underlying map of `S`-algebras. -/
  alg : SiteAlgebra.Hom P.alg Q.alg
  /-- The morphism of the fibred category. -/
  objMap : Q.obj.1 ⟶ P.obj.1
  /-- It lifts the morphism of spectra. -/
  objMap_isHomLift : p.IsHomLift alg.specMap objMap

/-- The identity morphism of an object over an `S`-algebra. -/
public abbrev Hom.id (P : AffineObject B S hS p) : Hom P P where
  alg := SiteAlgebra.Hom.id P.alg
  objMap := 𝟙 P.obj.1
  objMap_isHomLift := IsHomLift.id P.obj.2

/-- The composition of two morphisms of objects over `S`-algebras. -/
public abbrev Hom.comp {P Q R : AffineObject B S hS p} (h : Hom P Q) (k : Hom Q R) :
    Hom P R where
  alg := h.alg.comp k.alg
  objMap := k.objMap ≫ h.objMap
  objMap_isHomLift := by
    have := h.objMap_isHomLift
    have := k.objMap_isHomLift
    infer_instance

/-- The object `x` over `Spec A` extends across the deformation situation `A' → A`: some
object over `Spec A'` pulls back to an object isomorphic to `x`. -/
public def HasLift (hp : p.IsFiberedInGroupoids) (P : AffineObject B S hS p)
    (t : DeformationSituation B S hS P.alg) : Prop :=
  letI : p.IsFibered := hp.isFibered
  ∃ x' : p.Fiber t.top.over,
    Nonempty (((p.chosenPullbacks).pullbackFunctor t.hom.specMap).obj x' ≅ P.obj)

end AffineObject

/-- A morphism of deformation situations from `(x, A' → A)` to `(y, A₁' → A₁)`: a morphism
`(x, A) → (y, A₁)` together with a map `A' → A₁'` of thickened algebras compatible with it. -/
public structure DeformationSituation.Hom {P Q : AffineObject B S hS p}
    (s : DeformationSituation B S hS P.alg) (t : DeformationSituation B S hS Q.alg) where
  /-- The morphism `(x, A) → (y, A₁)` of objects over `S`-algebras. -/
  base : AffineObject.Hom P Q
  /-- The map `A' → A₁'` of thickened algebras. -/
  top : SiteAlgebra.Hom s.top t.top
  /-- The square of `S`-algebras commutes. -/
  comm : t.hom.ringMap.comp top.ringMap = base.alg.ringMap.comp s.hom.ringMap

/-! ### Obstruction theories -/

/-- An obstruction theory for a category fibred in groupoids over the big fppf site of `S`: a
linear functor of obstruction modules at every object over the spectrum of an `S`-algebra
mapping into an affine open, functorial in the triple `(x, A, M)`, together with an obstruction
element for every deformation situation whose vanishing is equivalent to the existence of a
lift. -/
@[stacks 07YG]
public structure ObstructionTheory (hp : p.IsFiberedInGroupoids) where
  /-- The `A`-linear functor of obstruction modules at every object over the spectrum of an
  `S`-algebra mapping into an affine open. -/
  obstruction : ∀ P : AffineObject B S hS p, LinearEndofunctor P.alg.carrier
  /-- The induced map of obstruction modules along a morphism of triples `(x, A, M)`. -/
  map : ∀ (P Q : AffineObject B S hS p) (h : AffineObject.Hom P Q)
      (M : ModuleCat.{u} P.alg.carrier) (N : ModuleCat.{u} Q.alg.carrier)
      (_φ : letI : Module P.alg.carrier (N : Type u) := Module.compHom _ h.alg.ringMap
        (M : Type u) →ₗ[P.alg.carrier] (N : Type u)),
    letI : Module P.alg.carrier ((obstruction Q).functor.obj N : Type u) :=
      Module.compHom _ h.alg.ringMap
    ((obstruction P).functor.obj M : Type u) →ₗ[P.alg.carrier]
      ((obstruction Q).functor.obj N : Type u)
  /-- For a morphism of modules at a fixed `(x, A)`, the map on triples restricts to the map
  of the local linear functor of obstruction modules. -/
  map_local : ∀ (P : AffineObject B S hS p)
      (M N : ModuleCat.{u} P.alg.carrier) (f : M ⟶ N),
    ∃ φ : (letI : Module P.alg.carrier (N : Type u) :=
        Module.compHom _ (AffineObject.Hom.id P).alg.ringMap
      (M : Type u) →ₗ[P.alg.carrier] (N : Type u)),
      (∀ m : (M : Type u), φ m = f m) ∧
        ∀ o : ((obstruction P).functor.obj M : Type u),
          map P P (AffineObject.Hom.id P) M N φ o = ((obstruction P).functor.map f) o
  /-- The induced map along an identity morphism of triples is the identity. -/
  map_id : ∀ (P : AffineObject B S hS p) (M : ModuleCat.{u} P.alg.carrier),
    ∃ φ : (letI : Module P.alg.carrier (M : Type u) :=
        Module.compHom _ (AffineObject.Hom.id P).alg.ringMap
      (M : Type u) →ₗ[P.alg.carrier] (M : Type u)),
      (∀ m : (M : Type u), φ m = m) ∧
        ∀ o : ((obstruction P).functor.obj M : Type u),
          map P P (AffineObject.Hom.id P) M M φ o = o
  /-- The induced map along a composition of morphisms of triples is the composition of the
  induced maps. -/
  map_comp : ∀ (P Q R : AffineObject B S hS p) (h : AffineObject.Hom P Q)
      (k : AffineObject.Hom Q R) (M : ModuleCat.{u} P.alg.carrier)
      (N : ModuleCat.{u} Q.alg.carrier) (L : ModuleCat.{u} R.alg.carrier)
      (φ : letI : Module P.alg.carrier (N : Type u) := Module.compHom _ h.alg.ringMap
        (M : Type u) →ₗ[P.alg.carrier] (N : Type u))
      (ψ : letI : Module Q.alg.carrier (L : Type u) := Module.compHom _ k.alg.ringMap
        (N : Type u) →ₗ[Q.alg.carrier] (L : Type u)),
    ∃ χ : (letI : Module P.alg.carrier (L : Type u) :=
        Module.compHom _ (h.comp k).alg.ringMap
      (M : Type u) →ₗ[P.alg.carrier] (L : Type u)),
      (∀ m : (M : Type u), χ m = ψ (φ m)) ∧
        ∀ o : ((obstruction P).functor.obj M : Type u),
          map P R (h.comp k) M L χ o = map Q R k N L ψ (map P Q h M N φ o)
  /-- The obstruction element of a deformation situation, in the obstruction module of its
  kernel. -/
  obs : ∀ (P : AffineObject B S hS p) (t : DeformationSituation B S hS P.alg),
    ((obstruction P).functor.obj t.kernelObj : Type u)
  /-- A morphism of deformation situations carries the obstruction element of its source to
  the obstruction element of its target. -/
  obs_naturality : ∀ (P Q : AffineObject B S hS p)
      (s : DeformationSituation B S hS P.alg) (t : DeformationSituation B S hS Q.alg)
      (m : DeformationSituation.Hom B S hS p s t),
    ∃ φ : (letI : Module P.alg.carrier (t.kernelObj : Type u) :=
        Module.compHom _ m.base.alg.ringMap
      (s.kernelObj : Type u) →ₗ[P.alg.carrier] (t.kernelObj : Type u)),
      (∀ z : (s.kernelObj : Type u), t.kernelVal (φ z) = m.top.ringMap (s.kernelVal z)) ∧
        map P Q m.base s.kernelObj t.kernelObj φ (obs P s) = obs Q t
  /-- The obstruction element of a deformation situation vanishes exactly when the object
  extends over the thickening. -/
  hasLift_iff_obs_eq_zero : ∀ (P : AffineObject B S hS p)
      (t : DeformationSituation B S hS P.alg),
    AffineObject.HasLift hp P t ↔ obs P t = 0

end Deformation.Artin
