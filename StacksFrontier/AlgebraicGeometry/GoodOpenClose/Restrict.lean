module

public import StacksFrontier.AlgebraicGeometry.SheafDescent.Basic

/-!
# Invertibility of a module on an open subscheme from a trivializing cover

Let `X` be a scheme, `U` an open of `X` and `M` a sheaf of `𝒪_X`-modules. If a family of opens
covering the open subscheme `U` has images in `X` over which `M` is sectionwise trivial, then the
pullback of `M` along `U.ι` is invertible. Each `Stacks.SheafDescent.Trivialization` of `M` is
transported along `U.ι`, and `Stacks.SheafDescent.isInvertible_of_trivialization` applies on the
site of the open subscheme, where the inverse module is the dual.

## Main definitions

* `Stacks.AlgebraicGeometry.GoodOpenClose.trivRestrictEquiv` and
  `Stacks.AlgebraicGeometry.GoodOpenClose.trivRestrict`: the transported trivialization.

## Main results

* `Stacks.AlgebraicGeometry.GoodOpenClose.isInvertible_of_iso`: invertibility is invariant under
  isomorphism of sheaves of modules.
* `Stacks.AlgebraicGeometry.GoodOpenClose.isInvertible_restrictFunctor_of_trivialization`: the
  restriction of `M` to `U` is invertible if it is sectionwise trivial over a cover of `U`.
* `Stacks.AlgebraicGeometry.GoodOpenClose.isInvertible_pullback_of_trivializing_cover`: if the
  opens `U.ι ''ᵁ Y i` of a family `Y` covering the open subscheme carry sectionwise
  trivializations of `M`, then the pullback of `M` to `U` is invertible.

## Implementation notes

`AlgebraicGeometry.Scheme.Modules.restrictAppIso` is `Iso.refl`, so the sections of
`(Scheme.Modules.restrictFunctor U.ι).obj M` over an open `W` of `U` are the same type as the
sections of `M` over `U.ι ''ᵁ W`, and so are the two rings of scalars. Only the scalar action
differs, by `(U.ι.appIso W).inv`, which is the identity propositionally
(`AlgebraicGeometry.Scheme.Opens.ι_appIso`) but not definitionally; so the transported
trivialization re-proves `map_smul'` by rewriting the action with
`Scheme.Modules.smul_restrictAppIso_hom_apply` and then with `ι_appIso`.

The module structure that `Stacks.SheafDescent.Trivialization` asks for is indexed by
`Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf U.toScheme.presheaf`, whereas the
one carried by the sections of the restriction is indexed by `U.toScheme.ringCatSheaf.obj`. These
are `rfl`-equal but instance search is keyed syntactically, so the local instance
`moduleRestrictSections` supplies the first spelling.

Invertibility is proved for `Scheme.Modules.restrictFunctor`, which has the good definitional
behaviour on sections, and carried to `Scheme.Modules.pullback` along
`Scheme.Modules.restrictFunctorIsoPullback` by `isInvertible_of_iso`. That lemma is stated on a
bare site: at the scheme spelling the rewrite with
`isInvertible_iff_tensorLeftFunctor_isEquivalence` fails, `X.ringCatSheaf.obj` and
`Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf X.presheaf` being `rfl`-equal but
not syntactically equal.

## References

* [Stacks Project, Tag 0B8M](https://stacks.math.columbia.edu/tag/0B8M)
* [Stacks Project, Tag 01CS](https://stacks.math.columbia.edu/tag/01CS)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite
open AlgebraicGeometry

namespace Stacks.AlgebraicGeometry.GoodOpenClose

universe u

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose
  Stacks.SheafOfModules.TensorSheafification.structureSheaf

/-! ### Transporting a trivialization along an open immersion -/

/-- The module structure on the sections of a restriction, at the spelling in which
`Stacks.SheafDescent.Trivialization` asks for it. The two spellings of the ring presheaf are
`rfl`-equal, but instance search does not see through them. -/
local instance moduleRestrictSections {X : Scheme.{u}} (U : X.Opens) (M : X.Modules)
    (W : U.toScheme.Opens) :
    Module ((Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf
      U.toScheme.presheaf).obj (op W) : Type u)
      ((((Scheme.Modules.restrictFunctor U.ι).obj M).val.obj (op W)) : Type u) :=
  (((Scheme.Modules.restrictFunctor U.ι).obj M).val.obj (op W)).isModule

/-- One component of the transported trivialization: the given isomorphism of sections over the
image open, read as an isomorphism over the open of the subscheme. The scalar action on the
restriction is the original one composed with `(U.ι.appIso W).inv`, which is the identity. -/
def trivRestrictEquiv {X : Scheme.{u}} (U : X.Opens) (M : X.Modules) {V : X.Opens}
    (t : Stacks.SheafDescent.Trivialization X.presheaf M.val V)
    (W : U.toScheme.Opens) (hW : U.ι ''ᵁ W ≤ V) :
    (((Scheme.Modules.restrictFunctor U.ι).obj M).val.obj (op W) : Type u) ≃ₗ[
      ((Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf U.toScheme.presheaf).obj
        (op W) : Type u)]
      ((Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf U.toScheme.presheaf).obj
        (op W) : Type u) where
  toFun m := t.θ (U.ι ''ᵁ W) (homOfLE hW) m
  map_add' m m' := (t.θ (U.ι ''ᵁ W) (homOfLE hW)).map_add m m'
  map_smul' r m := by
    have hsm := Scheme.Modules.smul_restrictAppIso_hom_apply U.ι M W r m
    rw [Scheme.Opens.ι_appIso] at hsm
    exact (congrArg (t.θ (U.ι ''ᵁ W) (homOfLE hW)) hsm).trans
      ((t.θ (U.ι ''ᵁ W) (homOfLE hW)).map_smul _ _)
  invFun s := (t.θ (U.ι ''ᵁ W) (homOfLE hW)).symm s
  left_inv m := (t.θ (U.ι ''ᵁ W) (homOfLE hW)).left_inv m
  right_inv s := (t.θ (U.ι ''ᵁ W) (homOfLE hW)).right_inv s

/-- A sectionwise trivialization of `M` over an open `V` of `X` transports to a sectionwise
trivialization of the restriction of `M` to `U` over the preimage of `V`. -/
def trivRestrict {X : Scheme.{u}} (U : X.Opens) (M : X.Modules) {V : X.Opens}
    (t : Stacks.SheafDescent.Trivialization X.presheaf M.val V) :
    Stacks.SheafDescent.Trivialization U.toScheme.presheaf
      ((Scheme.Modules.restrictFunctor U.ι).obj M).val (U.ι ⁻¹ᵁ V) where
  θ W h := trivRestrictEquiv U M t W
    ((U.ι.image_mono (leOfHom h)).trans (U.ι.image_preimage_le V))
  θ_naturality {_ _} h h' m :=
    t.θ_naturality (homOfLE ((U.ι.image_mono (leOfHom h)).trans (U.ι.image_preimage_le V)))
      (homOfLE (U.ι.image_mono (leOfHom h'))) m

/-! ### Invertibility -/

/-- Invertibility is invariant under isomorphism of sheaves of modules: isomorphic modules have
isomorphic tensor functors. -/
theorem isInvertible_of_iso {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    (O : Cᵒᵖ ⥤ CommRingCat.{u})
    (hO : Presheaf.IsSheaf J (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf O))
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify J AddCommGrpCat.{u}]
    {L L' : SheafOfModules.{u} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)} (e
      : L ≅ L')
    (h : SheafOfModules.IsInvertible O hO L) :
    SheafOfModules.IsInvertible O hO L' := by
  rw [SheafOfModules.isInvertible_iff_tensorLeftFunctor_isEquivalence] at h ⊢
  exact Functor.isEquivalence_of_iso
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat) hO⟩).mapIso
        (X := L) (Y := L') e)

/-- Invertibility of the restriction of a module to an open subscheme, from a family of
sectionwise trivializations over a cover of the subscheme. -/
theorem isInvertible_restrictFunctor_of_trivialization {X : Scheme.{u}} (U : X.Opens)
    (M : X.Modules) {I : Type u} (Y : I → U.toScheme.Opens) (hY : iSup Y = ⊤)
    (t : ∀ i, Stacks.SheafDescent.Trivialization U.toScheme.presheaf
      ((Scheme.Modules.restrictFunctor U.ι).obj M).val (Y i)) :
    SheafOfModules.IsInvertible U.toScheme.presheaf U.toScheme.ringCatSheaf.2
      ((Scheme.Modules.restrictFunctor U.ι).obj M) :=
  Stacks.SheafDescent.isInvertible_of_trivialization U.toScheme.presheaf
    U.toScheme.ringCatSheaf.2 _ ((Opens.coversTop_iff _ Y).mpr
      (TopologicalSpace.IsOpenCover.mk hY)) t

/-- If a family `Y` of opens covers the open subscheme `U` and `M` is sectionwise trivial over
each image open `U.ι ''ᵁ Y i`, then the pullback of `M` along `U.ι` is invertible. -/
theorem isInvertible_pullback_of_trivializing_cover {X : Scheme.{u}} (U : X.Opens)
    (M : X.Modules) {I : Type u} (Y : I → U.toScheme.Opens) (hY : iSup Y = ⊤)
    (V : I → X.Opens) (hV : ∀ i, Y i ≤ U.ι ⁻¹ᵁ V i)
    (t : ∀ i, Stacks.SheafDescent.Trivialization X.presheaf M.val (V i)) :
    SheafOfModules.IsInvertible U.toScheme.presheaf U.toScheme.ringCatSheaf.2
      ((Scheme.Modules.pullback U.ι).obj M) :=
  isInvertible_of_iso U.toScheme.presheaf U.toScheme.ringCatSheaf.2
    ((Scheme.Modules.restrictFunctorIsoPullback U.ι).app M)
    (isInvertible_restrictFunctor_of_trivialization U M Y hY
      fun i => (trivRestrict U M (t i)).comp (homOfLE (hV i)))

end Stacks.AlgebraicGeometry.GoodOpenClose

end
