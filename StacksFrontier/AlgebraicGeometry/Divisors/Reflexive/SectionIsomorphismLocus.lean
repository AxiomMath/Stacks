module

public import Mathlib.AlgebraicGeometry.Noetherian
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FiniteTypeLocallySurjective
public import StacksFrontier.AlgebraicGeometry.CoherentAbelian.Basic
public import StacksFrontier.AlgebraicGeometry.LocalIso.Basic
public import StacksFrontier.AlgebraicGeometry.Properties.Normal
public import StacksCore.Tactic.StacksAttribute

/-!
# The locus where a global section trivializes a coherent module

Let `ℱ` be a coherent module on a scheme `X` and let `s` be a global section of `ℱ`.  The
section corresponds to a morphism `𝒪_X ⟶ ℱ` (Mathlib's `SheafOfModules.unitHomEquiv`), and the
set of points where that morphism induces an isomorphism `𝒪_{X, x} ⟶ ℱ_x` of stalks is open.
This is the first of the two assertions of [Stacks, Tag 0EBN]: the set

`U = {x ∈ X | s : 𝒪_{X, x} → ℱ_x is an isomorphism}`

is an open subscheme of `X`.  The open subscheme itself is `sectionIsomorphismOpen`, whose
inclusion `(sectionIsomorphismOpen X ℱ s).ι` is the morphism `j : U → X` of the source.

## Main definitions

* `AlgebraicGeometry.sectionIsomorphismLocus ℱ s`: the set `U` above.
* `AlgebraicGeometry.sectionIsomorphismOpen X ℱ s`: the same set as an element of `X.Opens`,
  i.e. as an open subscheme of `X` with its inclusion into `X`.

## Main results

* `AlgebraicGeometry.isOpen_isIso_stalkFunctor_map`: on a ringed space, the locus where a
  morphism from a finite-type module to a coherent module is a stalkwise isomorphism is open.
* `AlgebraicGeometry.isOpen_sectionIsomorphismLocus`: the openness assertion of
  [Stacks, Tag 0EBN].

## Implementation notes

**Why openness is a stalkwise statement about an abelian-group map.** The locus is phrased with
`TopCat.Presheaf.stalkFunctor AddCommGrpCat`, which is the spelling in which this library states
[Stacks, Tag 01B8] and [Stacks, Tag 01C0], the two inputs the source cites.  The stalk map is
`𝒪_{X, x}`-linear, and a bijective linear map is a linear isomorphism, so invertibility as a map
of abelian groups is invertibility as a map of `𝒪_{X, x}`-modules; that is the content of the
source's condition.  `mem_sectionIsomorphismLocus_iff` records the bijectivity form, so the
meaning of membership is pinned down and not left to the categorical predicate.

**Why the general lemma lives on a ringed space.** The surjectivity input, Tag 01B8's
`Stacks.SheafOfModules.LocallySurjective.main_theorem`, is stated for a `RingedSpace`, while the
injectivity input, Tag 01C0's `exists_forall_stalk_isZero_of_stalk_isZero` together with
`stalk_injective_of_kernel_stalk_isZero`, is stated for a sheaf of rings on a `TopCat`.  Stating
the general lemma over a `RingedSpace` makes both available with no transport, and a scheme
supplies one.

Both halves are used in their *pointwise* form.  Tag 01B8 already concludes surjectivity at
every point of a neighbourhood, and Tag 01C0's neighbourhood is one on which every stalk of
`kernel φ` vanishes, which is again a condition at the points of that neighbourhood.  So no
statement about a restricted morphism — which would live in a different category for each open
— is needed, and the intersection of the two neighbourhoods is contained in the locus.

**The colimit assertion.** [Stacks, Tag 0EBN] also asserts that `j_*𝒪_U` is the colimit of
the reflexive powers `𝒪_X → ℱ → ℱ^{[2]} → ⋯` under multiplication by `s`.  That assertion is
proved in `StacksFrontier/AlgebraicGeometry/Divisors/Reflexive/ReflexivePowerColimit.lean`, where
the whole tag is registered on
`AlgebraicGeometry.CoherentReflexive.isOpen_sectionIsomorphismLocus_and_nonempty_isColimit`; the
openness lemma below is one of its two components and carries no attribute of its own.

Neither the rank-one hypothesis nor reflexivity of `ℱ` is used for openness, so neither is
assumed; the openness assertion holds for an arbitrary coherent `ℱ`.  Integrality, local
Noetherianity and normality of `X` are the standing hypotheses of the source's section and are
kept as instance binders on the statement even though openness does not use them.

## References

* [Stacks Project, Tag 0EBN](https://stacks.math.columbia.edu/tag/0EBN)
* [Stacks Project, Tag 01B8](https://stacks.math.columbia.edu/tag/01B8)
* [Stacks Project, Tag 01C0](https://stacks.math.columbia.edu/tag/01C0)
* [Stacks Project, Tag 01Y3](https://stacks.math.columbia.edu/tag/01Y3)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.AlgebraicGeometry.Tag01Y3LocalIso

universe u v

namespace AlgebraicGeometry

/-! ### The open locus of a stalkwise isomorphism -/

section RingedSpace

variable {Y : RingedSpace.{v, u}}
  {R : Sheaf (Opens.grothendieckTopology ↑↑Y.toPresheafedSpace) RingCat.{u}}

/-- The locus on which a morphism from a finite-type module to a coherent module induces an
isomorphism of stalks is open.

Injectivity propagates by [Stacks, Tag 01C0]: the stalk of `kernel φ` vanishes at a point of the
locus, `kernel φ` is of finite type because `φ` has finite-type source and coherent target, and
a finite-type module whose stalk vanishes at a point has vanishing stalks on a neighbourhood.
Surjectivity propagates by [Stacks, Tag 01B8], which concludes stalkwise surjectivity at every
point of a neighbourhood.  The intersection of the two neighbourhoods is an open subset of the
locus containing the point. -/
theorem isOpen_isIso_stalkFunctor_map {F G : SheafOfModules.{u} R} [G.IsFiniteType]
    [F.IsCoherent] (φ : G ⟶ F) :
    IsOpen {x : ↑↑Y.toPresheafedSpace | IsIso
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
        ((PresheafOfModules.toPresheaf R.obj).map φ.val))} := by
  have hFft : F.IsFiniteType := _root_.SheafOfModules.IsCoherent.isFiniteType
  have hKft : (kernel φ).IsFiniteType :=
    AlgebraicGeometry.CoherentAbelian.isFiniteType_kernel_of_isCoherent φ
  rw [isOpen_iff_forall_mem_open]
  intro x hx
  have hbij := (ConcreteCategory.isIso_iff_bijective _).1 hx
  have hmono : Mono ((SheafOfModules.toSheaf R).map (kernel.ι φ)) := by
    rw [Sheaf.Hom.mono_iff_presheaf_mono, NatTrans.mono_iff_mono_app]
    intro U
    show Mono ((forget₂ (ModuleCat (R.obj.obj U)) AddCommGrpCat).map
      ((SheafOfModules.evaluation R U).map (kernel.ι φ)))
    exact Functor.map_mono (forget₂ (ModuleCat (R.obj.obj U)) AddCommGrpCat)
      ((SheafOfModules.evaluation R U).map (kernel.ι φ))
  have hkinj : Function.Injective (ConcreteCategory.hom
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
        (((SheafOfModules.toSheaf R).map (kernel.ι φ)).hom))) :=
    (AddCommGrpCat.mono_iff_injective _).1
      (@TopCat.Presheaf.stalk_mono_of_mono _ _ _ _ _ _ _ _ _ _ _ _ _ _
        ((SheafOfModules.toSheaf R).map (kernel.ι φ)) hmono x)
  have hKx : IsZero ((TopCat.Presheaf.stalkFunctor Ab.{u} x).obj (kernel φ).val.presheaf) := by
    have hsub : Subsingleton ((SheafOfModules.stalkAddCommGroupFunctor R x).obj (kernel φ)) := by
      refine ⟨fun a b => hkinj (hbij.1 ?_)⟩
      have hk : ∀ z : (SheafOfModules.stalkAddCommGroupFunctor R x).obj (kernel φ),
          (ConcreteCategory.hom ((SheafOfModules.stalkAddCommGroupFunctor R x).map φ))
            ((ConcreteCategory.hom
              ((SheafOfModules.stalkAddCommGroupFunctor R x).map (kernel.ι φ))) z) = 0 := by
        intro z
        rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, kernel.condition,
          Functor.map_zero]
        rfl
      exact (hk a).trans (hk b).symm
    exact @AddCommGrpCat.isZero_of_subsingleton _ hsub
  obtain ⟨U₁, hxU₁, hU₁⟩ := exists_forall_stalk_isZero_of_stalk_isZero (kernel φ) x hKx
  obtain ⟨U₂, hxU₂, hU₂⟩ :=
    Stacks.SheafOfModules.LocallySurjective.main_theorem (X := Y) φ hFft x hbij.2
  refine ⟨↑(U₁ ⊓ U₂), fun y hy => ?_, (U₁ ⊓ U₂).isOpen, ⟨hxU₁, hxU₂⟩⟩
  exact (ConcreteCategory.isIso_iff_bijective _).2
    ⟨stalk_injective_of_kernel_stalk_isZero φ y (hU₁ y hy.1), hU₂ y hy.2⟩

end RingedSpace

/-! ### The locus where a global section trivializes a module on a scheme -/

variable {X : Scheme.{u}}

/-- The set of points at which a global section `s` of an `𝒪_X`-module `ℱ` induces an
isomorphism `𝒪_{X, x} ⟶ ℱ_x`, i.e. the set `U` of [Stacks, Tag 0EBN].  The morphism
`𝒪_X ⟶ ℱ` determined by `s` is `ℱ.unitHomEquiv.symm s`. -/
def sectionIsomorphismLocus (F : X.Modules) (s : F.sections) : Set X :=
  {x : X | IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
    ((PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map (F.unitHomEquiv.symm s).val))}

/-- Membership of `sectionIsomorphismLocus` is bijectivity of the stalk map at the point.  The
stalk map is `𝒪_{X, x}`-linear, so this is the source's condition that `s` induce an
isomorphism `𝒪_{X, x} → ℱ_x` of `𝒪_{X, x}`-modules. -/
theorem mem_sectionIsomorphismLocus_iff (F : X.Modules) (s : F.sections) (x : X) :
    x ∈ sectionIsomorphismLocus F s ↔ Function.Bijective (ConcreteCategory.hom
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
        ((PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map (F.unitHomEquiv.symm s).val))) :=
  ConcreteCategory.isIso_iff_bijective _

/-- **The openness assertion of [Stacks, Tag 0EBN].** For a coherent `𝒪_X`-module `ℱ` and a
global section `s` of `ℱ`, the set of points at which `s` induces an isomorphism
`𝒪_{X, x} ⟶ ℱ_x` is open.

The hypotheses that `ℱ` be reflexive of rank one are not needed and are not assumed; the
integrality, local Noetherianity and normality of `X` are the standing hypotheses of the
source's section.  The whole tag, including the colimit assertion, is
`AlgebraicGeometry.CoherentReflexive.isOpen_sectionIsomorphismLocus_and_nonempty_isColimit`. -/
theorem isOpen_sectionIsomorphismLocus (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] (F : X.Modules) [F.IsCoherent] (s : F.sections) :
    IsOpen (sectionIsomorphismLocus F s) :=
  isOpen_isIso_stalkFunctor_map (Y := X.toRingedSpace) (F.unitHomEquiv.symm s)

/-- The open subscheme `U` of [Stacks, Tag 0EBN], whose inclusion
`(sectionIsomorphismOpen X F s).ι` is the morphism `j : U → X` of the source. -/
def sectionIsomorphismOpen (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    (F : X.Modules) [F.IsCoherent] (s : F.sections) : X.Opens :=
  ⟨sectionIsomorphismLocus F s, isOpen_sectionIsomorphismLocus X F s⟩

/-- The open subscheme of [Stacks, Tag 0EBN] has the isomorphism locus as its underlying set. -/
@[simp]
theorem coe_sectionIsomorphismOpen (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] (F : X.Modules) [F.IsCoherent] (s : F.sections) :
    (sectionIsomorphismOpen X F s : Set X) = sectionIsomorphismLocus F s :=
  rfl

end AlgebraicGeometry

end
