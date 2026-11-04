module

public import StacksFrontier.AlgebraicGeometry.AffineAlgebraEquivalence.Basic
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleCounit
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleRingedToposHom

/-!
# Quasi-coherent algebras on the small étale site of a scheme, restricted to the Zariski site

Let `S` be a scheme of a big étale site `B`.  A sheaf of commutative algebras on the small étale
site of `S` is an object of `CategoryTheory.Under` of the structure sheaf of commutative rings
there, and restricting it along the inclusion of the small Zariski site of `S` produces a sheaf
of commutative `𝒪_S`-algebras, that is, a `Stacks.RelativeSpec.AlgebraSheaf`.  This file builds
that restriction and shows that it **preserves quasi-coherence**, which is what carries an
algebra on the small étale site into the category in which the scheme-level Stacks 01SA states
its anti-equivalence.

The restriction is `ε_*` for the morphism of ringed sites
`ε : (S_étale, 𝒪) ⟶ (S_Zar, 𝒪_S)` of Stacks 070R, whose structure map
`AlgebraicGeometry.SmallEtale.commRingStructureMap` is already given at `CommRingCat`; the
algebra-level functor is `CategoryTheory.Under.post` of that restriction followed by
`CategoryTheory.Under.map` of the structure map.

## Main definitions

* `AlgebraicGeometry.SmallEtale.algebraStructureMap` and
  `AlgebraicGeometry.SmallEtale.algebraUnderlyingModule`: the structure morphism of such an
  algebra read on sheaves of rings, and the module it underlies.
* `AlgebraicGeometry.SmallEtale.AlgebraIsQuasicoherent`: quasi-coherence of that module on the
  site.
* `AlgebraicGeometry.SmallEtale.restrictAlgebraToZariski` and
  `AlgebraicGeometry.SmallEtale.restrictQuasicoherentAlgebraToZariski`: the restriction functor,
  on all algebras and on the quasi-coherent ones.

## Main results

* `AlgebraicGeometry.SmallEtale.underlyingModule_restrictAlgebraToZariski`: **the module
  underlying the restriction of an algebra is the restriction of the module underlying it**, by
  `rfl`.  Restriction along the inclusion of the small Zariski site is precomposition on
  underlying presheaves, and it is the same precomposition whether the algebra's sections are
  read as a ring or as a module over the structure sheaf.
* `AlgebraicGeometry.SmallEtale.isQuasicoherent_restrictAlgebraToZariski`: **the restriction of
  a quasi-coherent algebra is quasi-coherent.**  This is the preceding identification together
  with `AlgebraicGeometry.SmallEtale.isQuasicoherent_restrictModule`, the module statement, which
  is proved unconditionally.

## Implementation notes

**Only one direction is built, and the other is not reachable here.**  On *modules* restriction
is one half of an equivalence: Descent, Proposition 03DX (2) at `τ = étale` is
`AlgebraicGeometry.SmallEtale.associatedModuleEquivalence'`, and
`AlgebraicGeometry.SmallEtale.isIso_counit` together with
`AlgebraicGeometry.SmallEtale.isQuasicoherent_restrictModule` exhibit
`AlgebraicGeometry.SmallEtale.restrictModule` as an inverse to it on the quasi-coherent
subcategories.  Neither half of that transports to algebras as it stands:

* *Fullness* would need a morphism of modules between two algebras, obtained from a morphism of
  their Zariski restrictions, to be multiplicative.  Multiplicativity is not module data, and
  reading it off the monoidal structure would need the multiplication of an algebra as a
  morphism `A ⊗_𝒪 A ⟶ A` out of the tensor product.  That morphism exists in this development
  only for a scheme's *Zariski* site, as `Stacks.RelativeSpec.AlgebraSheaf.multiplication`, and
  there is no identification anywhere of `CategoryTheory.Under` of a sheaf of commutative rings
  with the monoid objects of its sheaves of modules — so the monoidality of
  `AlgebraicGeometry.SmallEtale.associatedModule`, which *is* available as
  `AlgebraicGeometry.SmallEtale.associatedModuleTensorIso` (Stacks 03EL at `ε`), has nothing to
  act on.
* *Essential surjectivity* would need the left adjoint at the algebra level, which is
  `CategoryTheory.Under.post` of the inverse image of sheaves of commutative rings followed by
  `CategoryTheory.Under.pushout` of the structure map — the recipe
  `Stacks.AffineAlgebraEquivalence.algebraPullback` uses for a morphism of schemes — together
  with the identification of *its* underlying module with
  `AlgebraicGeometry.SmallEtale.associatedModule` of the underlying module.  That identification
  is exactly invertibility of `Stacks.SheafOfModules.AlgebraPushout.extendScalarsComparison`,
  which is unproved; the implementation notes there set out the three steps it needs and record
  that it is not formal.  It is in addition stated only for a
  `CategoryTheory.SmallCategory` site, whereas the small étale site has its objects one universe
  above its morphisms, so it does not apply here even in principle as it stands.

So what is built is the functor, not an equivalence.  That is still the direction the
construction of Stacks 081V uses it in: there one restricts a quasi-coherent algebra to an étale
chart and applies the scheme-level Stacks 01SA to the result, and it is the *image* of this
functor that 01SA consumes.

No declaration here carries a `stacks` tag.  Stacks 03DX (2) is the equivalence for modules and
is already covered in the tree; nothing below asserts an equivalence for algebras.

## References

* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 070R](https://stacks.math.columbia.edu/tag/070R)
* [Stacks Project, Tag 01SA](https://stacks.math.columbia.edu/tag/01SA)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The module underlying an algebra on the small étale site -/

/-- The structure morphism of a sheaf of commutative algebras on the small étale site of `S`,
read as a morphism of sheaves of rings out of the structure sheaf of Stacks 03DU. -/
def algebraStructureMap (A : Under (ringedTopos B S hS).O) :
    structureSheaf B S hS ⟶ Stacks.SheafOfModules.Tensor.ringSheaf A.right :=
  letI := Stacks.hasSheafCompose_forget₂_commRingCat.{u, u, u + 1} (topology B S hS)
  (sheafCompose (topology B S hS) (forget₂ CommRingCat.{u} RingCat.{u})).map A.hom

/-- The module underlying a sheaf of commutative algebras on the small étale site of `S`: its own
sheaf of rings, viewed as a module over itself and restricted along the structure morphism.  This
is the same construction as `Stacks.RelativeSpec.AlgebraSheaf.underlyingModule`, read on the
small étale site rather than on the Zariski site. -/
def algebraUnderlyingModule (A : Under (ringedTopos B S hS).O) :
    SheafOfModules.{u} (structureSheaf B S hS) :=
  (SheafOfModules.restrictScalars.{u} (algebraStructureMap B S hS A)).obj
    (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf A.right))

/-- Quasi-coherence of a sheaf of commutative algebras on the small étale site of `S`:
quasi-coherence on the site of its underlying module.  This is the condition
`Stacks.RelativeSpec.AlgebraSheaf.IsQuasicoherent` imposes, read on the small étale site. -/
abbrev AlgebraIsQuasicoherent : ObjectProperty (Under (ringedTopos B S hS).O) :=
  fun A => (algebraUnderlyingModule B S hS A).IsQuasicoherentOnSite

/-! ### Restriction to the Zariski site -/

/-- **Restriction of a sheaf of commutative algebras from the small étale site of `S` to its
Zariski site.**  This is `ε_*` on algebras for the morphism of ringed sites
`ε : (S_étale, 𝒪) ⟶ (S_Zar, 𝒪_S)` of Stacks 070R: restriction of the underlying sheaf of
commutative rings along the inclusion of the small Zariski site, with the structure morphism
composed with `AlgebraicGeometry.SmallEtale.commRingStructureMap`. -/
def restrictAlgebraToZariski :
    Under (ringedTopos B S hS).O ⥤ Stacks.RelativeSpec.AlgebraSheaf S :=
  Under.post ((opensToSmallEtale B S hS).sheafPushforwardContinuous CommRingCat.{u}
      (Opens.grothendieckTopology ↥S) (topology B S hS)) ⋙
    Under.map (commRingStructureMap B S hS)

/-- **The module underlying the restriction of an algebra is the restriction of the module
underlying it.**  Both are the algebra's sections over the Zariski opens of `S`, with scalars
restricted along the structure morphism: restriction along the inclusion of the small Zariski
site is precomposition on underlying presheaves, and that is the same operation whether the
sections are read as a ring or as a module. -/
theorem underlyingModule_restrictAlgebraToZariski (A : Under (ringedTopos B S hS).O) :
    Stacks.RelativeSpec.AlgebraSheaf.underlyingModule
        ((restrictAlgebraToZariski B S hS).obj A) =
      (restrictModule B S hS).obj (algebraUnderlyingModule B S hS A) :=
  rfl

/-- **The Zariski restriction of a quasi-coherent algebra on the small étale site of `S` is a
quasi-coherent `𝒪_S`-algebra.**

This is `AlgebraicGeometry.SmallEtale.underlyingModule_restrictAlgebraToZariski` together with
`AlgebraicGeometry.SmallEtale.isQuasicoherent_restrictModule`, the module statement of Descent,
Proposition 03DX (2) at `τ = étale`, which is proved with no hypothesis. -/
theorem isQuasicoherent_restrictAlgebraToZariski (A : Under (ringedTopos B S hS).O)
    (hA : AlgebraIsQuasicoherent B S hS A) :
    Stacks.RelativeSpec.AlgebraSheaf.IsQuasicoherent
      ((restrictAlgebraToZariski B S hS).obj A) := by
  rw [Stacks.RelativeSpec.AlgebraSheaf.IsQuasicoherent,
    underlyingModule_restrictAlgebraToZariski]
  exact isQuasicoherent_restrictModule B S hS (algebraUnderlyingModule B S hS A) hA

/-- **Restriction carries the quasi-coherent algebras on the small étale site of `S` to the
quasi-coherent `𝒪_S`-algebras**, i.e. into the category in which the scheme-level Stacks 01SA
states its anti-equivalence.

This is the functor the construction of Stacks 081V applies 01SA through.  It is not asserted to
be an equivalence; see the implementation notes for the two statements that would be needed. -/
def restrictQuasicoherentAlgebraToZariski :
    (AlgebraIsQuasicoherent B S hS).FullSubcategory ⥤
      Stacks.AffineAlgebraEquivalence.QuasicoherentAlgebra S :=
  ObjectProperty.lift _
    ((AlgebraIsQuasicoherent B S hS).ι ⋙ restrictAlgebraToZariski B S hS)
    fun A => isQuasicoherent_restrictAlgebraToZariski B S hS A.obj A.property

end AlgebraicGeometry.SmallEtale

end
