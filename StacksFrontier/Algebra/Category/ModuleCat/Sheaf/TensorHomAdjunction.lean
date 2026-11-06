module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.MonoidalSheafTensor
public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.InternalHomMonoidalComparison
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InternalHomVariance

/-!
# The tensor--internal-Hom adjunction for sheaves of modules

Let `O` be a sheaf of commutative rings on a site `(C, J)` and let `F` be a sheaf of
`O`-modules. For sheaves of `O`-modules `G`, `H`, morphisms out of the sheaf tensor product
are canonically identified with morphisms into the internal Hom sheaf of Stacks 03EM,

`Hom(F ⊗_O G, H) = Hom(G, Hom_O(F, H))`,

naturally in `G` and in `H`. This is the sheaf clause of Stacks 03EO, recorded here as an
adjunction: tensoring by `F` is left adjoint to internal Hom out of `F`.

The mathematics is the presheaf clause of Stacks 03EO
(`Stacks.PresheafOfModules.InternalHom.presheafTensorHomAdjunction`) plus two formal facts: the
sheaf tensor product is the sheafification of the presheaf tensor product, and the internal Hom
of Stacks 03EM is *already* a sheaf. Composing the presheaf adjunction with the sheafification
adjunction gives an adjunction with left adjoint on presheaves of modules; restricting it along
the fully faithful forgetful functor from sheaves of modules then lands it where it is wanted,
because the right adjoint of the composite already takes values in sheaves on the nose.

## Main definitions

* `Stacks.SheafOfModules.InternalHom.sheafifyForgetAdjunction`: the sheafification adjunction
  for modules, with the restriction of scalars along an identity erased from the right adjoint.
* `Stacks.SheafOfModules.InternalHom.tensorLeftAdjunction`: the adjunction re-seated so that
  its left adjoint is the tensor product of the monoidal structure on sheaves of modules.

## Main results

* `Stacks.SheafOfModules.InternalHom.sheafTensorHomAdjunction`: **the sheaf clause of Stacks
  03EO.** `(Stacks.SheafOfModules.Tensor.sheafTensor R).obj F` is left adjoint to
  `internalHomSecondFunctor J R F`.
* `Stacks.SheafOfModules.InternalHom.sheafTensorRightHomAdjunction` and
  `sheafTensorHomEquiv`: **the same clause in the handedness Stacks 03EO displays**, tensoring
  on the right by `G` against internal Hom with source `G`, and the resulting correspondence
  `Hom(F ⊗_O G, H) = Hom(F, Hom_O(G, H))`.
* `Stacks.SheafOfModules.InternalHom.sheafTensorHomEquiv_apply`: on sections that
  correspondence is the usual currying formula, which pins it down.
* `Stacks.SheafOfModules.InternalHom.tensorLeft_sheafTensor`: the left adjoint is the
  `tensorLeft` of the re-seated monoidal structure on sheaves of modules, by `rfl`.
* `Stacks.SheafOfModules.InternalHom.ihomIsoInternalHomSecondFunctor` and
  `ihomIsoInternalHom`: the internal hom of the monoidal closed structure on sheaves of
  modules is Stacks 03EM's internal Hom sheaf.

## Implementation notes

The three defeq identifications the construction rests on are each a single `rfl`:

* the right adjoint of `PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)` is
  `SheafOfModules.forget R ⋙ PresheafOfModules.restrictScalars (𝟙 R.obj)`, and
  `restrictScalars (𝟙 _)` is the identity functor definitionally — Mathlib relies on exactly
  this in its own `Full` instance for that functor. `sheafifyForgetAdjunction` performs that
  identification once, at the functor level, so no other declaration here crosses the
  `restrictScalars` spelling: the comparison is cheap at the object level and expensive at the
  morphism level.
* `(Stacks.SheafOfModules.Tensor.sheafTensor R).obj F` is
  `SheafOfModules.forget _ ⋙ tensorLeft F.val ⋙
  PresheafOfModules.sheafification (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf R).obj)`,
  which is the `comm1` of `Adjunction.restrictFullyFaithful`.
* the right adjoint of the composite adjunction,
  `SheafOfModules.forget _ ⋙ internalHomSecondFunctor R.obj F.val`, *equals*
  `internalHomSecondFunctor J R F ⋙ SheafOfModules.forget _`, which is the `comm2`. Both
  `comm1` and `comm2` are therefore `Iso.refl`, and nothing about either construction is
  unfolded beyond that.

Two monoidal structures on sheaves of modules are in play, as in
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/MonoidalSheafTensor.lean`: the localized one,
whose `curriedTensor` is `Localization.Monoidal.tensorBifunctor`, and the re-seated one, whose
`curriedTensor` *is* `Stacks.SheafOfModules.Tensor.sheafTensor R`. The adjunction is proved for
`Stacks.SheafOfModules.Tensor.sheafTensor R`, which is the re-seated `tensorLeft` by `rfl`
(`tensorLeft_sheafTensor`); the localized form `tensorLeftAdjunction` is obtained from it by
`SheafOfModules.sheafTensorIsoApp`. `MonoidalClosed.ihom` is the same functor for both
structures (`CategoryTheory.MonoidalCategory.reseatClosed` re-uses it).

The statements below are at ring universe `max u v` and module universe `max u v` for a site
with objects in `Type u` and morphisms in `Type v`, the universes at which
`Stacks.PresheafOfModules.InternalHom.presheafTensorHomAdjunction` is stated and at which the
monoidal structure on sheaves of modules (`SheafOfModules.monoidalCategorySheafTensor`) is
available.

## References

* [Stacks Project, Tag 03EO](https://stacks.math.columbia.edu/tag/03EO)
* [Stacks Project, Tag 03EM](https://stacks.math.columbia.edu/tag/03EM)
-/


@[expose] public section

open CategoryTheory MonoidalCategory
open Stacks.PresheafOfModules.InternalHom

noncomputable section

universe v u

namespace Stacks.SheafOfModules.InternalHom

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable (R : Sheaf J CommRingCat.{max u v})
  [HasWeakSheafify J AddCommGrpCat.{max u v}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]

/-- **The sheafification adjunction for sheaves of modules, in the forgetful spelling.** The
right adjoint of `PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)` is the forgetful
functor composed with restriction of scalars along an identity; that restriction of scalars is
the identity functor definitionally, and this declaration is the one place where the
identification is made. -/
def sheafifyForgetAdjunction :
    PresheafOfModules.sheafification
        (R₀ := (Stacks.SheafOfModules.Tensor.ringSheaf R).obj)
        (R := Stacks.SheafOfModules.Tensor.ringSheaf R)
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf R).obj) ⊣
      _root_.SheafOfModules.forget (Stacks.SheafOfModules.Tensor.ringSheaf R) :=
  PresheafOfModules.sheafificationAdjunction (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf R).obj)

variable (F : _root_.SheafOfModules.{max u v} (Stacks.SheafOfModules.Tensor.ringSheaf R))

/-- **Stacks 03EO, sheaf case.** Tensoring by the sheaf of modules `F` is left adjoint to the
internal-Hom functor with source `F`. Packaging the canonical correspondence
`Hom(F ⊗_O G, H) = Hom(G, Hom_O(F, H))` as an adjunction records its naturality in both
remaining variables.

The presheaf clause of Stacks 03EO is composed with the sheafification adjunction and the
result restricted along the fully faithful forgetful functor; this is legitimate because the
right adjoint of the composite already takes values in sheaves, the internal Hom of Stacks
03EM being a sheaf as soon as its target is. -/
def sheafTensorHomAdjunction :
    (Stacks.SheafOfModules.Tensor.sheafTensor R).obj F ⊣
      internalHomSecondFunctor.{v, u, max u v, u} J R F :=
  Adjunction.restrictFullyFaithful
    ((tensorLeftInternalHomAdjunction R.obj F.val).comp (sheafifyForgetAdjunction R))
    (_root_.SheafOfModules.fullyFaithfulForget _) (Functor.FullyFaithful.id _)
    (Iso.refl _) (Iso.refl _)

/-- The left adjoint of `sheafTensorHomAdjunction` is tensoring on the left by `F` for the
monoidal structure on sheaves of modules whose tensor product is
  `Stacks.SheafOfModules.Tensor.sheafTensor`. -/
lemma tensorLeft_sheafTensor :
    @tensorLeft _ _ (_root_.SheafOfModules.monoidalCategorySheafTensor R) F =
      (Stacks.SheafOfModules.Tensor.sheafTensor R).obj F :=
  rfl

/-- **Stacks 03EO, sheaf case, for the re-seated monoidal structure.** The same adjunction read
with `F ⊗_O -` spelled as the `tensorLeft` of the monoidal structure on sheaves of modules
whose tensor product is `Stacks.SheafOfModules.Tensor.sheafTensor`. -/
def reseatedTensorLeftAdjunction :
    @tensorLeft _ _ (_root_.SheafOfModules.monoidalCategorySheafTensor R) F ⊣
      internalHomSecondFunctor.{v, u, max u v, u} J R F :=
  sheafTensorHomAdjunction R F

section Displayed

variable (G H : _root_.SheafOfModules.{max u v} (Stacks.SheafOfModules.Tensor.ringSheaf R))

set_option maxHeartbeats 1600000 in
/-- **Stacks 03EO, sheaf case, in the handedness Stacks 03EO displays.** Tensoring on the right
by `G` is left adjoint to the internal-Hom functor with source `G`.

This is built from the presheaf clause of Stacks 03EO directly, not from
`sheafTensorHomAdjunction` by the braiding, so that its hom-equivalence is literally the
sheafification correspondence followed by presheaf currying — which is what
`sheafTensorHomEquiv_apply` below reads off. -/
def sheafTensorRightHomAdjunction :
    (Stacks.SheafOfModules.Tensor.sheafTensor R).flip.obj G ⊣
      internalHomSecondFunctor.{v, u, max u v, u} J R G :=
  Adjunction.restrictFullyFaithful
    ((presheafTensorHomAdjunction R.obj G.val).comp (sheafifyForgetAdjunction R))
    (_root_.SheafOfModules.fullyFaithfulForget _) (Functor.FullyFaithful.id _)
    (Iso.refl _) (Iso.refl _)

/-- **Stacks 03EO, sheaf case, as displayed.** The canonical tensor--internal-Hom
correspondence `Hom(F ⊗_O G, H) = Hom(F, Hom_O(G, H))` on sheaves of modules, as the
hom-equivalence of `sheafTensorRightHomAdjunction`. -/
def sheafTensorHomEquiv :
    (((Stacks.SheafOfModules.Tensor.sheafTensor R).obj F).obj G ⟶ H) ≃
      (F ⟶ (internalHomSecondFunctor.{v, u, max u v, u} J R G).obj H) :=
  (sheafTensorRightHomAdjunction R G).homEquiv F H

/-- The hom-equivalence of `sheafifyForgetAdjunction` is the sheafification unit followed by
the given morphism of sheaves. -/
lemma sheafifyForgetAdjunction_homEquiv
    (P : PresheafOfModules.{max u v} (Stacks.SheafOfModules.Tensor.ringSheaf R).obj)
    (f : (PresheafOfModules.sheafification
        (R₀ := (Stacks.SheafOfModules.Tensor.ringSheaf R).obj)
        (R := Stacks.SheafOfModules.Tensor.ringSheaf R)
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf R).obj)).obj P ⟶ H) :
    (sheafifyForgetAdjunction R).homEquiv P H f =
      (sheafifyForgetAdjunction R).unit.app P ≫ f.val :=
  (sheafifyForgetAdjunction R).homEquiv_unit P H f

/-- **Stacks 03EO, sheaf case, on sections.** The correspondence is the canonical currying map:
a morphism `b` out of the sheafified tensor product is sent to the map taking a section `x` of
`F` over `U` and a section `y` of `G` over `T ⟶ U` to the value of `b` on the image of the pure
tensor `x|_T ⊗ y`.

The right-hand side is the composite of `b` with the sheafification unit, read on pure tensors;
`sheafifyForgetAdjunction_homEquiv` rewrites it into that form. This pins the equivalence
down. -/
theorem sheafTensorHomEquiv_apply
    (b : ((Stacks.SheafOfModules.Tensor.sheafTensor R).obj F).obj G ⟶ H) (U : C)
    (x : F.val.obj (Opposite.op U)) {T : C} (q : T ⟶ U)
    (y : G.val.obj (Opposite.op T)) :
    sectionOfRestr R.obj H.val U q
        (((((sheafTensorHomEquiv R F G H b).val.app (Opposite.op U)).hom x).app
          (Opposite.op (Over.mk q))).hom (restrSection R.obj G.val U q y)) =
      globalTensorHom R.obj F.val G.val H.val
        ((sheafifyForgetAdjunction R).homEquiv (F.val ⊗ G.val) H b) T
        (F.val.restrictₛₗ q.op x ⊗ₜ y) :=
  presheafTensorHomEquiv_apply R.obj F.val G.val H.val
    ((sheafifyForgetAdjunction R).homEquiv (F.val ⊗ G.val) H b) U x q y

end Displayed

attribute [local instance] _root_.SheafOfModules.monoidalCategory
  _root_.SheafOfModules.monoidalClosed

/-- **Stacks 03EO, sheaf case, for the localized monoidal structure.** The adjunction with its
left adjoint re-seated along `SheafOfModules.sheafTensorIsoApp`, so that it is `tensorLeft F`
for the monoidal structure obtained by localizing the one on presheaves of modules. This is the
handedness and the structure for which `MonoidalClosed.ihom` is defined. -/
def tensorLeftAdjunction :
    tensorLeft F ⊣ internalHomSecondFunctor.{v, u, max u v, u} J R F :=
  Adjunction.ofNatIsoLeft (sheafTensorHomAdjunction R F)
    (_root_.SheafOfModules.sheafTensorIsoApp R F).symm

/-- **The internal hom of sheaves of modules is the internal Hom sheaf.** The internal hom of
the monoidal closed structure on sheaves of `O`-modules and Stacks 03EM's internal Hom sheaf out
of `F` are both right adjoint to `F ⊗_O -`, so they agree as functors.

The internal hom is unchanged by re-seating the monoidal structure
(`CategoryTheory.MonoidalCategory.reseatClosed`), so this identifies the internal hom of either
structure on sheaves of modules. -/
def ihomIsoInternalHomSecondFunctor :
    ihom F ≅ internalHomSecondFunctor.{v, u, max u v, u} J R F :=
  Adjunction.rightAdjointUniq (ihom.adjunction F) (tensorLeftAdjunction R F)

/-- **The internal hom of sheaves of modules is the internal Hom sheaf, object level.** The
internal hom `(ihom F).obj G` of the monoidal closed structure on sheaves of `O`-modules is the
internal Hom sheaf of Stacks 03EM, whose sections over `U` are the morphisms `F|_U ⟶ G|_U` of
`O|_U`-modules on the slice site. -/
def ihomIsoInternalHom
    (G : _root_.SheafOfModules.{max u v} (Stacks.SheafOfModules.Tensor.ringSheaf R)) :
    (ihom F).obj G ≅ (internalHomSecondFunctor.{v, u, max u v, u} J R F).obj G :=
  (ihomIsoInternalHomSecondFunctor R F).app G

end Stacks.SheafOfModules.InternalHom

end

end
