module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFullyFaithful.TowerHoms
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.ExtendedEtaleAlgebra
public import StacksFrontier.AlgebraicGeometry.AlgebraSheafModuleFunctor.Basic

/-!
# The pullback of the structure module, and the two spellings of a hom into a structure sheaf

Let `g : Z ⟶ S` be a morphism of schemes. The pullback `g^* 𝒪_S` of the structure module of `S` is
the structure module of `Z`: the pullback of modules is extension of scalars, and extension of
scalars takes the free module of rank one to the free module of rank one. This file records that
identification and the bijection it produces between the two ways of writing a morphism of
modules into a structure sheaf:

* over `Z`, as a morphism `g^* N ⟶ g^* 𝒪_S` of `𝒪_Z`-modules — the spelling used by
  `Stacks.Algebraization.InfinitesimalTower.IsHomsComplete`, hence by condition (4) of
  [Stacks, Tag 0EK2];
* over `S`, as a morphism `N ⟶ g_* 𝒪_Z` of `𝒪_S`-modules — the spelling produced by the universal
  property of the relative spectrum, hence the one in which a section of an affine morphism
  appears, through `Stacks.AffineAlgebraEquivalence.pushforwardAlgebra`.

The two are exchanged by the pullback–pushforward adjunction. That exchange is what lets the
completion hypothesis of [Stacks, Tag 0EK2], which is stated in the first spelling, be applied to
the direct image algebra of a finite étale cover, which lives in the second.

## Main definitions

* `Stacks.FundamentalGroup.pullbackUnitIso` — the identification `g^* 𝒪_S ≅ 𝒪_Z`, for an
  arbitrary morphism of schemes `g`.
* `Stacks.FundamentalGroup.pushforwardHomEquivPullbackHom` — the bijection between the two
  spellings, with `Stacks.FundamentalGroup.pushforwardHomOfPullbackHom` and
  `Stacks.FundamentalGroup.pullbackHomOfPushforwardHom` its two directions.

## Main results

* `Stacks.FundamentalGroup.pullbackUnitIso_hom` — the identification is the canonical comparison
  `SheafOfModules.pullbackObjUnitToUnit`, so nothing is chosen.
* `Stacks.FundamentalGroup.homEquiv_pullbackUnitIso_hom` — under the adjunction it corresponds to
  the canonical map `𝒪_S ⟶ g_* 𝒪_Z`.
* `Stacks.FundamentalGroup.pushforwardHomOfPullbackHom_eq_unit_comp` — the passage written with
  the unit of the adjunction, which is the form a compatibility with a further base change is
  proved in.
* `Stacks.FundamentalGroup.eq_of_pushforwardHomOfPullbackHom_eq` — injectivity, which is the half
  used to transport a uniqueness statement from one spelling to the other.

## Implementation notes

`SheafOfModules.pullbackObjUnitToUnit` is invertible as soon as the functor between the two sites
is final, and for the functor underlying a morphism of schemes — `Opens.map g.base` — finality is
immediate: the opens of a scheme have a top element, so the comma categories are nonempty, and the
poset is a preorder, so they are connected.

The `IsIso` instance has to be handed to `CategoryTheory.asIso` positionally rather than found by
instance search. `SheafOfModules.pullbackObjUnitToUnit` takes the `IsRightAdjoint` instance as an
argument, so writing the morphism a second time inside `asIso` elaborates a term whose instance
argument is whatever search returns; that need not be the one the `IsIso` hypothesis was stated
for, and then the hypothesis does not apply. Passing the instance positionally forces every
argument to come from it. For the same reason the `IsRightAdjoint` instance below is stated with
its universe pinned: left implicit it is auto-bound at `max u ?`, and the adjunction of
`AlgebraicGeometry.Scheme.Modules` does not have that type.

The bijection is assembled as an `Equiv` first and the two directions are defined from it, so that
the two round trips are `Equiv.apply_symm_apply` and `Equiv.symm_apply_apply` rather than
calculations inside the hom sets, where the projection separating a module from its presheaf
blocks rewriting.

## References

* [Stacks Project, Tag 0EK2](https://stacks.math.columbia.edu/tag/0EK2)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.FundamentalGroup

variable {Z S : Scheme.{u}}

/-- The opens of a scheme, mapped along a morphism, form a final functor: the index categories
are nonempty because the opens have a top element, and connected because the poset is a
preorder. -/
public instance final_opens_map_base (g : Z ⟶ S) :
    (TopologicalSpace.Opens.map g.base).Final :=
  Functor.final_of_exists_of_isFiltered _ (fun _ => ⟨⊤, ⟨homOfLE le_top⟩⟩)
    (fun {_ V} _ _ => ⟨V, 𝟙 V, Subsingleton.elim _ _⟩)

/-- The pushforward of sheaves of modules along a morphism of schemes is a right adjoint, by the
pullback–pushforward adjunction. -/
public instance isRightAdjoint_sheafOfModules_pushforward (g : Z ⟶ S) :
    (SheafOfModules.pushforward.{u} g.toRingCatSheafHom).IsRightAdjoint :=
  (Scheme.Modules.pullbackPushforwardAdjunction g).isRightAdjoint

/-- **The pullback of the structure module is the structure module.** For an arbitrary morphism
of schemes `g : Z ⟶ S` the canonical comparison `g^* 𝒪_S ⟶ 𝒪_Z` is invertible. -/
public def pullbackUnitIso (g : Z ⟶ S) :
    (Scheme.Modules.pullback g).obj (SheafOfModules.unit S.ringCatSheaf) ≅
      SheafOfModules.unit Z.ringCatSheaf :=
  @asIso _ _ _ _ _
    (SheafOfModules.instIsIsoPullbackObjUnitToUnitOfFinal.{u} g.toRingCatSheafHom)

/-- The identification `g^* 𝒪_S ≅ 𝒪_Z` is the canonical comparison; nothing is chosen. -/
public theorem pullbackUnitIso_hom (g : Z ⟶ S) :
    (pullbackUnitIso g).hom = SheafOfModules.pullbackObjUnitToUnit g.toRingCatSheafHom :=
  rfl

/-- Under the adjunction, the identification `g^* 𝒪_S ≅ 𝒪_Z` corresponds to the canonical map
`𝒪_S ⟶ g_* 𝒪_Z`. -/
public theorem homEquiv_pullbackUnitIso_hom (g : Z ⟶ S) :
    (Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv
        (SheafOfModules.unit S.ringCatSheaf) (SheafOfModules.unit Z.ringCatSheaf)
        (pullbackUnitIso g).hom =
      SheafOfModules.unitToPushforwardObjUnit g.toRingCatSheafHom :=
  SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit _

/-- **The two spellings of a morphism of modules into a structure sheaf.** A morphism
`g^* N ⟶ g^* 𝒪_S` of `𝒪_Z`-modules is the same thing as a morphism `N ⟶ g_* 𝒪_Z` of
`𝒪_S`-modules: compose with the identification `g^* 𝒪_S ≅ 𝒪_Z` and apply the adjunction. -/
public def pushforwardHomEquivPullbackHom (N : S.Modules) (g : Z ⟶ S) :
    ((Scheme.Modules.pullback g).obj N ⟶
        (Scheme.Modules.pullback g).obj (SheafOfModules.unit S.ringCatSheaf)) ≃
      (N ⟶ (Scheme.Modules.pushforward g).obj (SheafOfModules.unit Z.ringCatSheaf)) :=
  (Iso.homToEquiv (pullbackUnitIso g)).trans
    ((Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv N
      (SheafOfModules.unit Z.ringCatSheaf))

/-- **From the pullback spelling to the pushforward spelling.** -/
public def pushforwardHomOfPullbackHom (N : S.Modules) (g : Z ⟶ S)
    (ψ : (Scheme.Modules.pullback g).obj N ⟶
      (Scheme.Modules.pullback g).obj (SheafOfModules.unit S.ringCatSheaf)) :
    N ⟶ (Scheme.Modules.pushforward g).obj (SheafOfModules.unit Z.ringCatSheaf) :=
  pushforwardHomEquivPullbackHom N g ψ

/-- **From the pushforward spelling to the pullback spelling.** -/
public def pullbackHomOfPushforwardHom (N : S.Modules) (g : Z ⟶ S)
    (φ : N ⟶ (Scheme.Modules.pushforward g).obj (SheafOfModules.unit Z.ringCatSheaf)) :
    (Scheme.Modules.pullback g).obj N ⟶
      (Scheme.Modules.pullback g).obj (SheafOfModules.unit S.ringCatSheaf) :=
  (pushforwardHomEquivPullbackHom N g).symm φ

/-- The passage to the pushforward spelling is the adjunction applied to the composite with the
identification `g^* 𝒪_S ≅ 𝒪_Z`. -/
public theorem pushforwardHomOfPullbackHom_eq (N : S.Modules) (g : Z ⟶ S)
    (ψ : (Scheme.Modules.pullback g).obj N ⟶
      (Scheme.Modules.pullback g).obj (SheafOfModules.unit S.ringCatSheaf)) :
    pushforwardHomOfPullbackHom N g ψ =
      (Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv N
        (SheafOfModules.unit Z.ringCatSheaf) (ψ ≫ (pullbackUnitIso g).hom) :=
  rfl

/-- The passage to the pushforward spelling, written with the unit of the adjunction. This is the
form in which a compatibility with a further base change is proved. -/
public theorem pushforwardHomOfPullbackHom_eq_unit_comp (N : S.Modules) (g : Z ⟶ S)
    (ψ : (Scheme.Modules.pullback g).obj N ⟶
      (Scheme.Modules.pullback g).obj (SheafOfModules.unit S.ringCatSheaf)) :
    pushforwardHomOfPullbackHom N g ψ =
      (Scheme.Modules.pullbackPushforwardAdjunction g).unit.app N ≫
        (Scheme.Modules.pushforward g).map (ψ ≫ (pullbackUnitIso g).hom) :=
  (pushforwardHomOfPullbackHom_eq N g ψ).trans (Adjunction.homEquiv_unit _ _ _ _)

/-- **The two spellings are in bijection.** -/
public theorem bijective_pushforwardHomOfPullbackHom (N : S.Modules) (g : Z ⟶ S) :
    Function.Bijective (pushforwardHomOfPullbackHom N g) :=
  (pushforwardHomEquivPullbackHom N g).bijective

/-- The passage to the pushforward spelling undone by the passage back. -/
public theorem pushforwardHomOfPullbackHom_pullbackHomOfPushforwardHom (N : S.Modules)
    (g : Z ⟶ S)
    (φ : N ⟶ (Scheme.Modules.pushforward g).obj (SheafOfModules.unit Z.ringCatSheaf)) :
    pushforwardHomOfPullbackHom N g (pullbackHomOfPushforwardHom N g φ) = φ :=
  (pushforwardHomEquivPullbackHom N g).apply_symm_apply φ

/-- The passage back undone by the passage to the pushforward spelling. -/
public theorem pullbackHomOfPushforwardHom_pushforwardHomOfPullbackHom (N : S.Modules)
    (g : Z ⟶ S)
    (ψ : (Scheme.Modules.pullback g).obj N ⟶
      (Scheme.Modules.pullback g).obj (SheafOfModules.unit S.ringCatSheaf)) :
    pullbackHomOfPushforwardHom N g (pushforwardHomOfPullbackHom N g ψ) = ψ :=
  (pushforwardHomEquivPullbackHom N g).symm_apply_apply ψ

/-- Two morphisms in the pullback spelling which agree in the pushforward spelling agree. -/
public theorem eq_of_pushforwardHomOfPullbackHom_eq (N : S.Modules) (g : Z ⟶ S)
    {ψ ψ' : (Scheme.Modules.pullback g).obj N ⟶
      (Scheme.Modules.pullback g).obj (SheafOfModules.unit S.ringCatSheaf)}
    (h : pushforwardHomOfPullbackHom N g ψ = pushforwardHomOfPullbackHom N g ψ') : ψ = ψ' :=
  (bijective_pushforwardHomOfPullbackHom N g).1 h

/-- A morphism in the pushforward spelling comes from one in the pullback spelling. -/
public theorem exists_pullbackHom (N : S.Modules) (g : Z ⟶ S)
    (φ : N ⟶ (Scheme.Modules.pushforward g).obj (SheafOfModules.unit Z.ringCatSheaf)) :
    ∃ ψ : (Scheme.Modules.pullback g).obj N ⟶
      (Scheme.Modules.pullback g).obj (SheafOfModules.unit S.ringCatSheaf),
      pushforwardHomOfPullbackHom N g ψ = φ :=
  ⟨pullbackHomOfPushforwardHom N g φ,
    pushforwardHomOfPullbackHom_pullbackHomOfPushforwardHom N g φ⟩

/-! ### The transition map in the pushforward spelling

A factorization `h ≫ g = a` induces a map `g_* 𝒪_Z ⟶ a_* 𝒪_{Z'}`, and it has two descriptions:
the geometric one, as the canonical map of direct image algebras attached to `h` read as a
morphism of schemes over `S`, and the adjunction-theoretic one. The geometric one is the map that
a section of an affine morphism restricts along, so it is the one the fundamental-group chapter
meets; it is recorded here. -/

/-- **The transition map of direct images of structure sheaves attached to a factorization.** For
`h ≫ g = a` this is the canonical map `g_* 𝒪_Z ⟶ a_* 𝒪_{Z'}` of `𝒪_S`-modules underlying the
canonical map of direct image algebras attached to `h`, read as a morphism of schemes over
`S`. -/
public def pushforwardUnitTransGeom {Z Z' S : Scheme.{u}} (g : Z ⟶ S) (h : Z' ⟶ Z) (a : Z' ⟶ S)
    (hh : h ≫ g = a) :
    (Scheme.Modules.pushforward g).obj (SheafOfModules.unit Z.ringCatSheaf) ⟶
      (Scheme.Modules.pushforward a).obj (SheafOfModules.unit Z'.ringCatSheaf) :=
  Stacks.RelativeSpec.AlgebraSheaf.underlyingModuleMap
    (Stacks.AffineAlgebraEquivalence.pushforwardAlgebraMap
      (Over.homMk h hh : (Over.mk a : Over S) ⟶ Over.mk g))

/-- The transition map is the underlying morphism of modules of the canonical map of direct image
algebras; this is the form in which a restriction of sections produces it. -/
public theorem pushforwardUnitTransGeom_eq {Z Z' S : Scheme.{u}} (g : Z ⟶ S) (h : Z' ⟶ Z)
    (a : Z' ⟶ S) (hh : h ≫ g = a) :
    pushforwardUnitTransGeom g h a hh =
      Stacks.RelativeSpec.AlgebraSheaf.underlyingModuleMap
        (Stacks.AffineAlgebraEquivalence.pushforwardAlgebraMap
          (Over.homMk h hh : (Over.mk a : Over S) ⟶ Over.mk g)) :=
  rfl

/-- The transition map attached to the identity factorization is the identity. -/
public theorem pushforwardUnitTransGeom_id {Z S : Scheme.{u}} (g : Z ⟶ S) :
    pushforwardUnitTransGeom g (𝟙 Z) g (Category.id_comp g) = 𝟙 _ :=
  have h1 : (Over.homMk (𝟙 Z) (Category.id_comp g) : (Over.mk g : Over S) ⟶ Over.mk g) = 𝟙 _ :=
    Over.OverMorphism.ext rfl
  (congrArg (fun m => Stacks.RelativeSpec.AlgebraSheaf.underlyingModuleMap
      (Stacks.AffineAlgebraEquivalence.pushforwardAlgebraMap m)) h1).trans
    ((congrArg Stacks.RelativeSpec.AlgebraSheaf.underlyingModuleMap
        (Stacks.AffineAlgebraEquivalence.pushforwardAlgebraMap_id (Over.mk g))).trans
      ((Stacks.RelativeSpec.AlgebraSheaf.underlyingModuleFunctor S).map_id _))

/-- The transition maps compose: a factorization in two steps induces the composite of the two
transition maps. -/
public theorem pushforwardUnitTransGeom_comp {Z Z' Z'' S : Scheme.{u}} (g : Z ⟶ S) (h : Z' ⟶ Z)
    (k : Z'' ⟶ Z') (a : Z' ⟶ S) (b : Z'' ⟶ S) (hh : h ≫ g = a) (hk : k ≫ a = b)
    (hkh : (k ≫ h) ≫ g = b) :
    pushforwardUnitTransGeom g h a hh ≫ pushforwardUnitTransGeom a k b hk =
      pushforwardUnitTransGeom g (k ≫ h) b hkh :=
  have h1 : (Over.homMk k hk : (Over.mk b : Over S) ⟶ Over.mk a) ≫
        (Over.homMk h hh : (Over.mk a : Over S) ⟶ Over.mk g) =
      (Over.homMk (k ≫ h) hkh : (Over.mk b : Over S) ⟶ Over.mk g) :=
    Over.OverMorphism.ext rfl
  ((Stacks.RelativeSpec.AlgebraSheaf.underlyingModuleFunctor S).map_comp _ _).symm.trans
    (congrArg Stacks.RelativeSpec.AlgebraSheaf.underlyingModuleMap
      ((Stacks.AffineAlgebraEquivalence.pushforwardAlgebraMap_comp
          (Over.homMk k hk : (Over.mk b : Over S) ⟶ Over.mk a)
          (Over.homMk h hh : (Over.mk a : Over S) ⟶ Over.mk g)).symm.trans
        (congrArg Stacks.AffineAlgebraEquivalence.pushforwardAlgebraMap h1)))

/-- The factorization that `Stacks.FundamentalGroup.pushforwardUnitTransGeom_comp` asks for:
a factorization in two steps is a factorization. -/
public theorem pushforwardUnitTransGeom_comp_fac {Z Z' Z'' S : Scheme.{u}} {g : Z ⟶ S} {h : Z' ⟶ Z}
    {k : Z'' ⟶ Z'} {a : Z' ⟶ S} {b : Z'' ⟶ S} (hh : h ≫ g = a) (hk : k ≫ a = b) :
    (k ≫ h) ≫ g = b := by
  rw [Category.assoc, hh, hk]

end Stacks.FundamentalGroup

end
