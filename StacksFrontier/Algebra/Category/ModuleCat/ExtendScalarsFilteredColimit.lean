module

public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts
public import Mathlib.CategoryTheory.Monoidal.Limits.Preserves
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Pi
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Extension of scalars as a colimit of copowers

Let `φ : A →+* B` be a homomorphism of commutative rings and let `H` be an `A`-module.  The
chain of identifications

```
B ⊗_A H = colim_j (M_j ⊗_A H)        (B = colim_j M_j, and `- ⊗_A H` preserves colimits)
        = colim_j H^{n_j}            (each M_j finite free of rank n_j)
```

is the purely formal half of the argument of **Stacks 073K, part (2)**, which computes
`H^i(X, 𝓕) ⊗_A B` by writing `B` as a filtered colimit of finite free `A`-modules, moving the
colimit and the finite direct sums through `H^i(X, -)`, and invoking Stacks 073E.  This file
proves the three formal links and records the uniqueness criterion that pins the comparison map
down.  Nothing here is geometric, and nothing here mentions cohomology.

The first link is the observation — already exploited by
`ModuleCat.preservesFiniteLimits_extendScalars_of_flat` in Mathlib — that
`ModuleCat.extendScalars φ` followed by `ModuleCat.restrictScalars φ` *is* the functor
`B ⊗_A -` on `ModuleCat A`, on the nose.  Read as a functor of the left tensor factor instead,
it is `MonoidalCategory.tensorRight H`, which is a left adjoint and therefore preserves every
colimit; so a colimit presentation of `B` as an `A`-module is carried to one of `B ⊗_A H`.
Filteredness of the index category plays no role at this stage; see the implementation notes.

## Main definitions

* `ModuleCat.extendRestrictScalarsIsoTensorLeft`: **extension of scalars is tensoring with the
  target ring** — a natural isomorphism `extendScalars φ ⋙ restrictScalars φ ≅ tensorLeft B` of
  endofunctors of `ModuleCat A`, where `B` carries the `A`-module structure given by `φ`.
* `ModuleCat.extendScalarsObjIsoColimit`: **the first link** — if `B`, as an `A`-module, is the
  colimit of a diagram `D` in `ModuleCat A`, then `B ⊗_A H` is the colimit of `D ⋙ (- ⊗_A H)`.
* `ModuleCat.tensorIsoBiproductOfBasis` and `ModuleCat.tensorFreeIsoBiproduct`: **the second
  link** — a module with a finite basis, tensored with `H`, is a finite copower of `H`.
* `CategoryTheory.Functor.mapBiproductConst`: **the third link** — an additive functor commutes
  with finite copowers.  This is the constant-family case of Mathlib's
  `CategoryTheory.Functor.mapBiproduct`.

## Main results

* `ModuleCat.extendScalars_hom_ext` and `ModuleCat.extendScalars_hom_ext_unit`: **two maps out
  of an extension of scalars are equal as soon as their transposes are.**  This is the
  uniqueness criterion for the comparison map of Stacks 073K, part (2): that map is pinned by
  `AlgebraicGeometry.Space.BaseChangeDiagram.affineCohomologyBaseChangeMap_adjoint`, which
  names its image under the hom-equivalence of
  `ModuleCat.extendRestrictScalarsAdj`, and a hom-equivalence is a bijection.

## Implementation notes

`ModuleCat.extendRestrictScalarsIsoTensorLeft` is `Iso.refl`: the two endofunctors of
`ModuleCat A` are definitionally equal, objects and morphisms alike.  The `A`-module structure
on `B ⊗_A H` obtained by restricting the `B`-module structure along `φ` and the one obtained
from the `A`-module structure on `B` agree because both act through the left factor, and `φ`
is how `B` became an `A`-module in the first place.  The isomorphism is stated anyway, because
the two spellings have very different `simp` normal forms and a named isomorphism is what one
rewrites with.

**Filteredness is not assumed.** `MonoidalCategory.tensorRight H` is a left adjoint on
`ModuleCat A` (through `ModuleCat.monoidalClosed` and the braiding), so it preserves *all*
colimits, not merely filtered ones.  Stacks 073K needs the colimit to be filtered for a
different reason — cohomology only commutes with filtered colimits — and that is not this
file's business.  Likewise the diagram `D` is not required to take finite free values for
`ModuleCat.extendScalarsObjIsoColimit`; finite freeness is used only by the second link, which
is stated for one module at a time.

The index type of the copowers is kept in `Type 0`.  Both `ModuleCat.biproductIsoPi` and the
`CategoryTheory.Functor.preservesFiniteBiproductsOfAdditive` instance quantify over
`J : Type`, so a basis indexed by `Module.Free.ChooseBasisIndex A M` — which lives in the
universe of `M` — has to be reindexed along `Fintype.equivFin` before any of this applies.
That is what `ModuleCat.tensorFreeIsoBiproduct` does, and it is why its index type is
`Fin (Fintype.card (Module.Free.ChooseBasisIndex A M))` rather than `Module.finrank A M`:
identifying the two needs `StrongRankCondition A`, which a general commutative ring — possibly
the zero ring — does not satisfy.

Mathlib's `ModuleCat.ExtendScalars.hom_ext` is a different extensionality principle for maps
out of an extension of scalars: it compares them on the elements `1 ⊗ₜ m`.  The criterion here
is the categorical one, and it is the one that applies to a map which was *defined* as the
transpose of something.
-/

@[expose] public section

noncomputable section

universe v v₁ v₂ u₁ u₂ u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

namespace CategoryTheory.Functor

/-- **An additive functor commutes with finite copowers**: for a finite index type `ι` and an
object `X`, an additive functor `G` carries the copower `⨁ (i : ι), X` to `⨁ (i : ι), G.obj X`.

This is the constant-family case of `CategoryTheory.Functor.mapBiproduct`, which is the general
statement that an additive functor commutes with finite biproducts; the additivity of `G` is
what supplies the `CategoryTheory.Limits.PreservesBiproduct` instance it asks for, through
`CategoryTheory.Functor.preservesFiniteBiproductsOfAdditive`. -/
def mapBiproductConst {C : Type u₁} [Category.{v₁} C] [Preadditive C] [HasFiniteBiproducts C]
    {D : Type u₂} [Category.{v₂} D] [Preadditive D] (G : C ⥤ D) [G.Additive] {ι : Type}
    [Finite ι] (X : C) :
    G.obj (⨁ fun _ : ι ↦ X) ≅ ⨁ fun _ : ι ↦ G.obj X :=
  G.mapBiproduct fun _ ↦ X

end CategoryTheory.Functor

namespace ModuleCat

section ExtendScalars

variable {A Bring : Type u} [CommRing A] [CommRing Bring] (φ : A →+* Bring)

/-- **Extension of scalars is tensoring with the target ring.**  Extending scalars along
`φ : A →+* B` and restricting them back is the endofunctor `B ⊗_A -` of `ModuleCat A`, where
`B` is read as an `A`-module through `φ`.

The two functors are definitionally equal, so this is `Iso.refl`; it is given a name because
that definitional equality is not something to rely on at the point of use. -/
def extendRestrictScalarsIsoTensorLeft :
    extendScalars.{u, u, u} φ ⋙ restrictScalars.{u, u, u} φ ≅
      tensorLeft ((restrictScalars φ).obj (ModuleCat.of Bring Bring)) :=
  Iso.refl _

/-- **Extension of scalars along a colimit presentation of the target ring.**  If the
`A`-module `B` is the colimit of a diagram `D` in `ModuleCat A` — witnessed by a colimit cocone
`c` together with an identification `e` of its tip with `B` — then for every `A`-module `H` the
scalar extension `B ⊗_A H`, read over `A`, is the colimit of `D ⋙ (- ⊗_A H)`.

This is the first link in the chain of **Stacks 073K, part (2)**: tensoring commutes with
colimits.  Filteredness of the index category is not needed, since `- ⊗_A H` preserves every
colimit; see the implementation notes of this file. -/
@[ega "IV 8.5.2.1"]
def extendScalarsObjIsoColimit {J : Type u} [Category.{u} J] {D : J ⥤ ModuleCat.{u} A}
    {c : Cocone D} (hc : IsColimit c)
    (e : c.pt ≅ (restrictScalars φ).obj (ModuleCat.of Bring Bring)) (H : ModuleCat.{u} A)
    [HasColimit (D ⋙ tensorRight H)] :
    (restrictScalars φ).obj ((extendScalars φ).obj H) ≅ colimit (D ⋙ tensorRight H) :=
  (extendRestrictScalarsIsoTensorLeft φ).app H ≪≫ ((tensorRight H).mapIso e).symm ≪≫
    (isColimitOfPreserves (tensorRight H) hc).coconePointUniqueUpToIso (colimit.isColimit _)

end ExtendScalars

section Copower

variable {A : Type u} [CommRing A]

/-- **A module with a finite basis, tensored with `H`, is a copower of `H`.**  A basis of `M`
indexed by a finite type `ι` identifies `M ⊗_A H` with the biproduct of `ι` copies of `H`.

This is the second link in the chain of **Stacks 073K, part (2)**, in the form that does not
have to choose a basis.  The summand indexed by `i` is the image of `b i ⊗ₜ -`. -/
def tensorIsoBiproductOfBasis {ι : Type} [Fintype ι] {M : ModuleCat.{u} A}
    (b : Module.Basis ι A M) (H : ModuleCat.{u} A) : M ⊗ H ≅ ⨁ fun _ : ι ↦ H := by
  classical
  exact (((TensorProduct.congr b.equivFun (LinearEquiv.refl A H)).trans
      ((TensorProduct.comm A (ι → A) H).trans
        (TensorProduct.piScalarRight A A H ι))).toModuleIso) ≪≫
    (biproductIsoPi fun _ : ι ↦ H).symm

/-- **A finite free module, tensored with `H`, is a finite copower of `H`.**  For `M` free of
finite rank over `A`, the module `M ⊗_A H` is the biproduct of `Fintype.card
(Module.Free.ChooseBasisIndex A M)` copies of `H`.

This is `ModuleCat.tensorIsoBiproductOfBasis` applied to the basis `Module.Free.chooseBasis`,
reindexed along `Fintype.equivFin` so that the index type lands in `Type 0`.  The rank is
spelled as the cardinality of the chosen basis index rather than as `Module.finrank A M`
because the two agree only under `StrongRankCondition A`. -/
def tensorFreeIsoBiproduct (M H : ModuleCat.{u} A) [Module.Free A M] [Module.Finite A M] :
    M ⊗ H ≅ ⨁ fun _ : Fin (Fintype.card (Module.Free.ChooseBasisIndex A M)) ↦ H :=
  tensorIsoBiproductOfBasis
    ((Module.Free.chooseBasis A M).reindex
      (Fintype.equivFin (Module.Free.ChooseBasisIndex A M))) H

end Copower

section HomExt

variable {A : Type u₁} {Bring : Type u₂} [CommRing A] [CommRing Bring] (φ : A →+* Bring)

/-- **Two maps out of an extension of scalars are equal as soon as their transposes are.**
The hom-equivalence of `ModuleCat.extendRestrictScalarsAdj` is a bijection
`((extendScalars φ).obj H ⟶ N) ≃ (H ⟶ (restrictScalars φ).obj N)`, so a map out of
`(extendScalars φ).obj H` is determined by its image under it.

This is the uniqueness criterion for the comparison map of **Stacks 073K, part (2)**: that map
is *defined* as a transpose, and
`AlgebraicGeometry.Space.BaseChangeDiagram.affineCohomologyBaseChangeMap_adjoint` names its
image under this bijection, so any other map with the same image is it. -/
theorem extendScalars_hom_ext {H : ModuleCat.{max v u₂} A} {N : ModuleCat.{max v u₂} Bring}
    (α β : (extendScalars φ).obj H ⟶ N)
    (h : (extendRestrictScalarsAdj φ).homEquiv H N α =
      (extendRestrictScalarsAdj φ).homEquiv H N β) :
    α = β :=
  ((extendRestrictScalarsAdj φ).homEquiv H N).injective h

/-- **Two maps out of an extension of scalars are equal as soon as they agree after the
adjunction unit.**  The transpose of `α : (extendScalars φ).obj H ⟶ N` is the composite of the
unit `H ⟶ (restrictScalars φ).obj ((extendScalars φ).obj H)` with the restriction of `α`, so
`ModuleCat.extendScalars_hom_ext` can be read entirely inside `ModuleCat A`. -/
theorem extendScalars_hom_ext_unit {H : ModuleCat.{max v u₂} A} {N : ModuleCat.{max v u₂} Bring}
    (α β : (extendScalars φ).obj H ⟶ N)
    (h : (extendRestrictScalarsAdj φ).unit.app H ≫ (restrictScalars φ).map α =
      (extendRestrictScalarsAdj φ).unit.app H ≫ (restrictScalars φ).map β) :
    α = β :=
  extendScalars_hom_ext φ α β <| by
    rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
    exact h

end HomExt

end ModuleCat

end

end
