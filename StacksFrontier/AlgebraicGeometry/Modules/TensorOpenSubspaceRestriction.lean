module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorSheafCoherence
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorSheafWorldBridge
public import StacksFrontier.AlgebraicGeometry.Modules.OpenSubspaceRestrictionTransport

/-!
# The tensor product crosses restriction to an open subspace

Let `X` be a ringed space and `U ⊆ X` open. `SheafOfModules.openSubspaceRestriction` is
restriction of sheaves of `𝒪_X`-modules to the open subspace written as the slice restriction
followed by the transport to the open subspace — the spelling at which the exterior algebra
crosses restriction definitionally
(`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorPowerRestrictOpenFunctorial`). The
localization of [Stacks, Section 0FMK] needs the tensor product to cross the *same* functor, and
this file supplies the isomorphism.

**Nothing here is a new construction.** `Stacks.SheafOfModules.TensorPower.restrictTensorSheafIso`
already identifies `(M ⊗ L)|_U` with `M|_U ⊗ L|_U` for restriction along the open-image functor
of `U`, `Stacks.Cohomology.HigherDirectImage.moduleRestriction`, and that functor is
`SheafOfModules.openSubspaceRestriction` — the same functor, not merely an isomorphic one. So the
isomorphism below *is* `restrictTensorSheafIso`, read at the composite spelling; what the file
contributes is the reading, the measurements that say which readings are affordable, and the
morphism half of the tensor-world bridge that a consumer in the bifunctor spelling needs.

## Main definitions

* `SheafOfModules.openSubspaceTensorIso`: **`(M ⊗ L)|_U ≅ M|_U ⊗ L|_U` at the composite
  spelling of restriction to the open subspace**, and
  `SheafOfModules.openSubspaceTensorBifunctorIso`: the same isomorphism with the tensor product
  `Stacks.SheafOfModules.Tensor.sheafTensor` read as a bifunctor on pairs over `X.sheaf`, the
  spelling the wedge-product morphism and the multiplication of a sheaf of graded algebras are
  stated at.

## Main results

* `SheafOfModules.openSubspaceTensorIso_naturality` and
  `openSubspaceTensorBifunctorIso_naturality`: **the identification is natural in both
  variables**, in each of the two spellings of the tensor product. This is what a consumer
  tensoring a morphism with an identity needs.

## Implementation notes

**Naturality, and why the identification is conjugated rather than ascribed.**
`Stacks.SheafOfModules.TensorPower.restrictTensorSheafIso` has its naturality in both variables,
`Stacks.SheafOfModules.TensorPower.restrictTensorSheafIso_naturality`, and a consumer tensoring a
morphism with an identity needs it at the composite spelling. Reading that statement across the
two spellings of restriction by ascription runs far past the heartbeat budget. So the
identification is **conjugated** by `SheafOfModules.openSubspaceRestrictionIsoModuleRestriction`,
the natural isomorphism between the two spellings of restriction. With it, naturality is a formal
consequence of naturality at `moduleRestriction`, of naturality of the comparison, and of
functoriality of the tensor bifunctor, and no composite in the proof crosses a spelling.

**Why the reassociations are term-mode.** The two spellings of the restricted structure sheaf
make the `CategoryTheory.Category` instance of a composition in a statement differ syntactically
from the instance of a composition produced by rewriting, so `simp only [Category.assoc]` does
not fire on the result and a `rw` naming an intermediate object is refused as not type-correct at
`implicit` transparency. The associativity shuffle therefore happens inside two lemmas stated in
abstract categories, `conjugatedNaturalitySquare` and `bifunctorMap_square`, applied by term.

**No `@[stacks]` attribute.** Tags 01CA and 05NA are carried by the declarations this file reads;
a second reading of a statement is not a second statement.

## References

* [Stacks Project, Tag 01AD](https://stacks.math.columbia.edu/tag/01AD)
* [Stacks Project, Tag 05NA](https://stacks.math.columbia.edu/tag/05NA)
* [Stacks Project, Section 0FMK](https://stacks.math.columbia.edu/tag/0FMK)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf AlgebraicGeometry
open TopologicalSpace PresheafOfModules
open Stacks.Cohomology.HigherDirectImage (moduleRestriction restrictToOpen)
open Stacks.SheafOfModules.TensorPower (restrictTensorSheafIso)
open Stacks.SheafOfModules.Tensor (sheafTensor)

attribute [local instance_reducible] AlgebraicGeometry.SheafedSpace.sheaf

universe u

/-- **The abstract shape of a conjugated naturality square.** Given a comparison `p ≫ q = r ≫ s`
between two readings of one morphism, a naturality square `s ≫ t' = t ≫ w` for the second
reading, and a square `w ≫ u' = u ≫ v` transporting the comparison back along the target, the
three combine into a single square.

Stated in an abstract category so that it can be applied by `exact` to composites whose
intermediate objects agree only up to unfolding the structure sheaf of the open subspace — which
is what blocks `rw` and `simp` here; see the implementation notes. -/
private theorem conjugatedNaturalitySquare {D : Type*} [Category D]
    {W W' V V' A' B Y Z : D}
    (p : W ⟶ W') (q : W' ⟶ V') (r : W ⟶ V) (s : V ⟶ V') (t' : V' ⟶ A') (u' : A' ⟶ Z)
    (t : V ⟶ B) (w : B ⟶ A') (u : B ⟶ Y) (v : Y ⟶ Z)
    (h₁ : p ≫ q = r ≫ s) (h₂ : s ≫ t' = t ≫ w) (h₃ : w ≫ u' = u ≫ v) :
    p ≫ q ≫ t' ≫ u' = (r ≫ t ≫ u) ≫ v := by
  rw [← Category.assoc p q, h₁, Category.assoc, ← Category.assoc s t', h₂, Category.assoc, h₃]
  simp

/-- **A tensor product of two commuting squares commutes.** For a bifunctor `F`, squares
`f ≫ a' = a ≫ f'` and `g ≫ b' = b ≫ g'` give the square of the morphisms `F` induces on pairs,
each written as its first-variable component followed by its second-variable one. Stated at an
abstract bifunctor, so that nothing concrete is unfolded. -/
private theorem bifunctorMap_square {C₁ D₁ E₁ : Type*} [Category C₁] [Category D₁] [Category E₁]
    (F : C₁ ⥤ D₁ ⥤ E₁) {M M' N N' : C₁} {L L' K K' : D₁} (f : M ⟶ M') (g : L ⟶ L')
    (a : M ⟶ N) (b : L ⟶ K) (a' : M' ⟶ N') (b' : L' ⟶ K') (f' : N ⟶ N') (g' : K ⟶ K')
    (ha : f ≫ a' = a ≫ f') (hb : g ≫ b' = b ≫ g') :
    ((F.map f).app L ≫ (F.obj M').map g) ≫ (F.map a').app L' ≫ (F.obj N').map b' =
      ((F.map a).app L ≫ (F.obj N).map b) ≫ (F.map f').app K ≫ (F.obj N').map g' := by
  simp only [Category.assoc, NatTrans.naturality_assoc]
  rw [← NatTrans.comp_app_assoc, ← F.map_comp, ← Functor.map_comp, ha, hb, F.map_comp,
    NatTrans.comp_app_assoc, Functor.map_comp]

namespace SheafOfModules

variable {X : RingedSpace.{u, u}} (U : Opens X.carrier)

/-- **`(M ⊗ L)|_U ≅ M|_U ⊗ L|_U` for restriction to the open subspace `U`**, at the composite
spelling `SheafOfModules.openSubspaceRestriction` — the slice restriction followed by the
transport to the open subspace, which is the spelling the exterior algebra crosses
definitionally.

It is `Stacks.SheafOfModules.TensorPower.restrictTensorSheafIso` — that identification is stated
for restriction along the open-image functor of `U`,
`Stacks.Cohomology.HigherDirectImage.moduleRestriction` — **conjugated** by the comparison
`SheafOfModules.openSubspaceRestrictionIsoModuleRestriction` between the two spellings of
restriction, and stated at the same spelling of the tensor product as `restrictTensorSheafIso`.
No argument is repeated here. The conjugation rather than an ascription is what makes
`SheafOfModules.openSubspaceTensorIso_naturality` affordable; see the implementation notes. -/
def openSubspaceTensorIso (M L : SheafOfModules.{u} (structureSheafRing X)) :
    (openSubspaceRestriction U).obj
        (((sheafTensor.{u, u, u, u, u} ⟨X.presheaf, X.IsSheaf⟩).obj M).obj L) ≅
      ((sheafTensor.{u, u, u, u, u}
          ⟨(restrictToOpen X U).presheaf, (restrictToOpen X U).IsSheaf⟩).obj
        ((openSubspaceRestriction U).obj M)).obj ((openSubspaceRestriction U).obj L) :=
  (openSubspaceRestrictionIsoModuleRestriction U).app
      (((sheafTensor.{u, u, u, u, u} ⟨X.presheaf, X.IsSheaf⟩).obj M).obj L) ≪≫
    restrictTensorSheafIso X U M L ≪≫
      ((sheafTensor.{u, u, u, u, u}
          ⟨(restrictToOpen X U).presheaf, (restrictToOpen X U).IsSheaf⟩).mapIso
        ((openSubspaceRestrictionIsoModuleRestriction U).app M).symm).app _ ≪≫
      ((sheafTensor.{u, u, u, u, u}
          ⟨(restrictToOpen X U).presheaf, (restrictToOpen X U).IsSheaf⟩).obj _).mapIso
        ((openSubspaceRestrictionIsoModuleRestriction U).app L).symm

/-- The legs of `SheafOfModules.openSubspaceTensorIso`, written out. -/
theorem openSubspaceTensorIso_hom (M L : SheafOfModules.{u} (structureSheafRing X)) :
    (openSubspaceTensorIso U M L).hom =
      (openSubspaceRestrictionIsoModuleRestriction U).hom.app
          (((sheafTensor.{u, u, u, u, u} ⟨X.presheaf, X.IsSheaf⟩).obj M).obj L) ≫
        (restrictTensorSheafIso X U M L).hom ≫
          ((sheafTensor.{u, u, u, u, u}
              ⟨(restrictToOpen X U).presheaf, (restrictToOpen X U).IsSheaf⟩).map
            ((openSubspaceRestrictionIsoModuleRestriction U).inv.app M)).app _ ≫
          ((sheafTensor.{u, u, u, u, u}
              ⟨(restrictToOpen X U).presheaf, (restrictToOpen X U).IsSheaf⟩).obj _).map
            ((openSubspaceRestrictionIsoModuleRestriction U).inv.app L) :=
  rfl

/-- **`(M ⊗ L)|_U ≅ M|_U ⊗ L|_U` is natural in both variables**, at the composite spelling
`SheafOfModules.openSubspaceRestriction` of restriction to the open subspace: the identification
carries the restriction of the morphism induced by `f : M ⟶ M'` and `g : L ⟶ L'` to the morphism
induced by their restrictions.

The square is the conjugate, by
`SheafOfModules.openSubspaceRestrictionIsoModuleRestriction`, of the same square at the
`Stacks.Cohomology.HigherDirectImage.moduleRestriction` spelling,
`Stacks.SheafOfModules.TensorPower.restrictTensorSheafIso_naturality`: the comparison is natural,
so it carries that square to this one, the transport along the target being functoriality of the
tensor bifunctor applied to naturality of the inverse comparison. -/
theorem openSubspaceTensorIso_naturality
    {M M' L L' : SheafOfModules.{u} (structureSheafRing X)} (f : M ⟶ M') (g : L ⟶ L') :
    (openSubspaceRestriction U).map
          (((sheafTensor.{u, u, u, u, u} ⟨X.presheaf, X.IsSheaf⟩).map f).app L ≫
            ((sheafTensor.{u, u, u, u, u} ⟨X.presheaf, X.IsSheaf⟩).obj M').map g) ≫
        (openSubspaceTensorIso U M' L').hom =
      (openSubspaceTensorIso U M L).hom ≫
        ((sheafTensor.{u, u, u, u, u}
            ⟨(restrictToOpen X U).presheaf, (restrictToOpen X U).IsSheaf⟩).map
              ((openSubspaceRestriction U).map f)).app ((openSubspaceRestriction U).obj L) ≫
          ((sheafTensor.{u, u, u, u, u}
            ⟨(restrictToOpen X U).presheaf, (restrictToOpen X U).IsSheaf⟩).obj
              ((openSubspaceRestriction U).obj M')).map ((openSubspaceRestriction U).map g) :=
  conjugatedNaturalitySquare _ _ _ _ _ _ _ _ _ _
    ((openSubspaceRestrictionIsoModuleRestriction U).hom.naturality _)
    (Stacks.SheafOfModules.TensorPower.restrictTensorSheafIso_naturality X U f g)
    (bifunctorMap_square _ _ _ _ _ _ _ _ _
      ((openSubspaceRestrictionIsoModuleRestriction U).inv.naturality f)
      ((openSubspaceRestrictionIsoModuleRestriction U).inv.naturality g))

/-- **`(M ⊗ L)|_U ≅ M|_U ⊗ L|_U` with the tensor product read as a bifunctor on pairs over the
structure sheaves `X.sheaf`**, the spelling the wedge-product morphism
`SheafOfModules.prodWedgeHom` and the multiplication `SheafOfModules.GradedAlgebra.mulSheaf` of a
sheaf of graded algebras are stated at. This **is** `SheafOfModules.openSubspaceTensorIso`: the
two spellings of the tensor product are the same object, so the ascription is all that is
needed. -/
def openSubspaceTensorBifunctorIso (M L : SheafOfModules.{u} (structureSheafRing X)) :
    (openSubspaceRestriction U).obj
        ((Functor.uncurry.obj (sheafTensor.{u, u, u, u, u} X.sheaf)).obj (M, L)) ≅
      (Functor.uncurry.obj (sheafTensor.{u, u, u, u, u} (restrictToOpen X U).sheaf)).obj
        ((openSubspaceRestriction U).obj M, (openSubspaceRestriction U).obj L) :=
  openSubspaceTensorIso U M L

/-- **`(M ⊗ L)|_U ≅ M|_U ⊗ L|_U` is natural in both variables, in the bifunctor spelling.** This
is `SheafOfModules.openSubspaceTensorIso_naturality`, read by ascription. -/
theorem openSubspaceTensorBifunctorIso_naturality
    {M M' L L' : SheafOfModules.{u} (structureSheafRing X)} (f : M ⟶ M') (g : L ⟶ L') :
    (openSubspaceRestriction U).map
          ((Functor.uncurry.obj (sheafTensor.{u, u, u, u, u} X.sheaf)).map
            ((f, g) : (M, L) ⟶ (M', L'))) ≫
        (openSubspaceTensorBifunctorIso U M' L').hom =
      (openSubspaceTensorBifunctorIso U M L).hom ≫
        (Functor.uncurry.obj (sheafTensor.{u, u, u, u, u} (restrictToOpen X U).sheaf)).map
          (((openSubspaceRestriction U).map f, (openSubspaceRestriction U).map g) :
            ((openSubspaceRestriction U).obj M, (openSubspaceRestriction U).obj L) ⟶
              ((openSubspaceRestriction U).obj M', (openSubspaceRestriction U).obj L')) :=
  openSubspaceTensorIso_naturality U f g

end SheafOfModules

end
