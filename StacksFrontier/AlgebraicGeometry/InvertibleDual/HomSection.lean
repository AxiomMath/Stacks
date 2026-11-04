module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InvertibleDualEvaluation
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorDualSheafHom
public import StacksFrontier.AlgebraicGeometry.InternalHomCoherent.TopSections

/-!
# A morphism out of an invertible module, read as a global section of the twist

Let `L` be an invertible sheaf of modules on a ringed site and `L'` an arbitrary one. The
canonical rank-one morphism `L' ⊗ L^∨ ⟶ SheafHom(L, L')` is then an isomorphism, because an
invertible sheaf of modules is locally a direct summand of a finite free one. On a scheme the
global sections of `SheafHom(L, L')` are the morphisms `L ⟶ L'`, so a morphism `L ⟶ L'` *is* a
global section of `L' ⊗ L^∨`.

That reading is what lets the divisor machinery be applied to a morphism of invertible modules:
[Stacks, Tag 01X0] attaches an effective Cartier divisor to a regular global section of an
invertible module, and the morphisms out of `L` are not sections of anything until the twist is
formed.

## Main definitions

* `Stacks.SheafOfModules.tensorDualIsoSheafHom`: the isomorphism `F ⊗ E^∨ ≅ SheafHom(E, F)` for
  `E` invertible and `F` arbitrary, on a ringed site.
* `Stacks.SheafOfModules.valAddEquivOfIso`: an isomorphism of sheaves of modules, read on the
  sections over an object.
* `Stacks.SheafOfModules.Scheme.tensorDualTwist`: the twist `L' ⊗ L^∨` on a scheme.
* `Stacks.SheafOfModules.Scheme.homTensorDualSectionEquiv`: **the comparison**, the additive
  bijection between the morphisms `L ⟶ L'` and the global sections of `L' ⊗ L^∨`.

## Main results

* `Stacks.SheafOfModules.isIso_tensorDualToSheafHom_of_isInvertible`: the canonical rank-one
  morphism `F ⊗ E^∨ ⟶ SheafHom(E, F)` is an isomorphism when `E` is invertible.

## Implementation notes

The rank-one morphism and its inversion under a local finite free splitting are
`Stacks.SheafOfModules.tensorDualToSheafHom` and
`Stacks.SheafOfModules.isIso_tensorDualToSheafHom`, step (5) of the proof of Tag 08JJ. What is
added here is the splitting data for an invertible module: Tag 0B8N (b) supplies it, packaged as
`Stacks.SheafOfModules.coversTop_invertibleSummandObj` and
`Stacks.SheafOfModules.invertibleSummandRetract`, and these are the same inputs that
`Stacks.SheafOfModules.exactPairingDualSheafOfIsInvertible` consumes. The per-object hypothesis
`Stacks.SheafOfModules.IsLocallyDirectSummandOfFiniteFree` is *not* used: it asks for a splitting
on every member of a covering sieve, and deducing that from Tag 0B8N (b) is a
restriction-of-a-retract step that the sectionwise form of the hypothesis does not need.

On a scheme the two spellings `Stacks.SheafOfModules.sheafHom X.sheaf.obj X.ringCatSheaf.property`
and `Stacks.Algebraization.sheafHomFunctor X` agree definitionally — both are Tag 03EM's
`internalHom` of the same two presheaves of modules, with a proof-irrelevant sheaf condition — so
no transport is needed between the isomorphism of this file and the global-section comparison
`Stacks.Algebraization.internalHomSectionsTopMapAddEquiv` of Tag 0882.

**No `@[stacks]` attribute.** The isomorphism is the case `E` invertible of a step of the proof of
Tag 08JJ, which carries its attribute where it is stated; the global-section comparison is the
degenerate case of Tag 0882, which carries its attribute in
`StacksFrontier/AlgebraicGeometry/InternalHomCoherent/TopSections.lean`. Neither composite is an
assertion of a tag of its own.

## References

* [Stacks Project, Tag 08JJ](https://stacks.math.columbia.edu/tag/08JJ)
* [Stacks Project, Tag 0B8N](https://stacks.math.columbia.edu/tag/0B8N)
* [Stacks Project, Tag 0882](https://stacks.math.columbia.edu/tag/0882)
* [Stacks Project, Tag 01X0](https://stacks.math.columbia.edu/tag/01X0)
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory Opposite SheafOfModules

universe v u

namespace Stacks.SheafOfModules

/-! ### The twist of an invertible module on a ringed site -/

section RingedSite

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (𝒪 : Cᵒᵖ ⥤ CommRingCat.{max u v})
  (h𝒪 : Presheaf.IsSheaf J (TensorSheafification.structureRingPresheaf 𝒪))
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
  [HasWeakSheafify J AddCommGrpCat.{max u v}]
  [∀ V : C, HasWeakSheafify (J.over V) AddCommGrpCat.{max u v}]
  [∀ V : C, (J.over V).WEqualsLocallyBijective AddCommGrpCat.{max u v}]
  (E F : SheafOfModules.{max u v} (TensorSheafification.structureSheaf 𝒪 h𝒪))

/-- **The canonical morphism `F ⊗ E^∨ ⟶ SheafHom(E, F)` is an isomorphism for `E` invertible.**
An invertible sheaf of modules is locally a direct summand of a finite free one by Tag 0B8N (b),
which is the hypothesis of step (5) of the proof of Tag 08JJ. -/
theorem isIso_tensorDualToSheafHom_of_isInvertible [IsInvertible 𝒪 h𝒪 E] :
    IsIso (tensorDualToSheafHom 𝒪 h𝒪 E F) :=
  isIso_tensorDualToSheafHom 𝒪 h𝒪 (coversTop_invertibleSummandObj 𝒪 h𝒪 E)
    (I := fun k => ULift.{max u v} (Fin (invertibleSummandRank k)))
    (fun k => FiniteDualBasis.ofRetract 𝒪 h𝒪 (invertibleSummandRetract k)) F

/-- **The isomorphism `F ⊗ E^∨ ≅ SheafHom(E, F)` for `E` invertible**, whose underlying morphism
is the canonical rank-one map `Stacks.SheafOfModules.tensorDualToSheafHom`. -/
def tensorDualIsoSheafHom [IsInvertible 𝒪 h𝒪 E] :
    (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨𝒪, Presheaf.isSheaf_of_isSheaf_comp _ (𝒪)
      (forget₂ CommRingCat RingCat) (h𝒪)⟩).obj (F)).obj ((dualSheaf 𝒪 h𝒪 E))) ≅
      sheafHom 𝒪 h𝒪 E F :=
  have := isIso_tensorDualToSheafHom_of_isInvertible 𝒪 h𝒪 E F
  asIso (tensorDualToSheafHom 𝒪 h𝒪 E F)

/-- The underlying morphism of `Stacks.SheafOfModules.tensorDualIsoSheafHom` is the canonical
rank-one morphism `Stacks.SheafOfModules.tensorDualToSheafHom`. -/
@[simp] theorem tensorDualIsoSheafHom_hom [IsInvertible 𝒪 h𝒪 E] :
    (tensorDualIsoSheafHom 𝒪 h𝒪 E F).hom = tensorDualToSheafHom 𝒪 h𝒪 E F :=
  rfl

end RingedSite

/-! ### Sections across an isomorphism -/

/-- **An isomorphism of sheaves of modules read on sections**: it is an additive bijection of the
sections over every object, inverted by the sections of the inverse isomorphism. -/
def valAddEquivOfIso {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{max u v}} {A B : SheafOfModules.{max u v} R} (e : A ≅ B) (U : Cᵒᵖ) :
    A.val.obj U ≃+ B.val.obj U where
  toFun := (e.hom.val.app U).hom
  invFun := (e.inv.val.app U).hom
  left_inv x := congrArg (fun φ : A ⟶ A => (φ.val.app U).hom x) e.hom_inv_id
  right_inv y := congrArg (fun φ : B ⟶ B => (φ.val.app U).hom y) e.inv_hom_id
  map_add' := map_add _

/-! ### The comparison on a scheme -/

section Scheme

open _root_.AlgebraicGeometry

variable {X : Scheme.{u}} (L L' : X.Modules) [IsInvertible X.sheaf.obj X.ringCatSheaf.property L]

/-- **The twist `L' ⊗ L^∨`** of an `𝒪_X`-module by the dual of an invertible one. -/
abbrev Scheme.tensorDualTwist : X.Modules :=
  (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.sheaf.obj, Presheaf.isSheaf_of_isSheaf_comp _
    (X.sheaf.obj) (forget₂ CommRingCat RingCat) (X.ringCatSheaf.property)⟩).obj (L')).obj
    ((dualSheaf X.sheaf.obj X.ringCatSheaf.property L)))

/-- **The isomorphism `L' ⊗ L^∨ ≅ SheafHom(L, L')` on a scheme**, for `L` invertible. -/
def Scheme.tensorDualIsoSheafHom :
    Scheme.tensorDualTwist L L' ≅ (Stacks.Algebraization.sheafHomFunctor X L).obj L' :=
  _root_.Stacks.SheafOfModules.tensorDualIsoSheafHom X.sheaf.obj X.ringCatSheaf.property L L'

/-- **A morphism `L ⟶ L'` out of an invertible module is a global section of `L' ⊗ L^∨`.**
Composing the comparison `SheafHom(L, L') ≅ L' ⊗ L^∨` with the identification of the global
sections of the internal hom with the morphisms (Tag 0882 at `U = ⊤`). -/
def Scheme.homTensorDualSectionEquiv :
    (L ⟶ L') ≃+ (Scheme.tensorDualTwist L L').val.obj (op (⊤ : X.Opens)) :=
  (Stacks.Algebraization.internalHomSectionsTopMapAddEquiv L L').trans
    (valAddEquivOfIso (Scheme.tensorDualIsoSheafHom L L') (op (⊤ : X.Opens))).symm

end Scheme

end Stacks.SheafOfModules

end
