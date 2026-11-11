module

public import StacksFrontier.AlgebraicGeometry.Perfect.VectorBundleKGroup
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SymmetricPowerInvertible
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorPowerRank
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SliceRestrictionMonoidal
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InvertibleRankOne
public import StacksFrontier.AlgebraicGeometry.InvertibleTrivialization.Sheaf
public import StacksFrontier.AlgebraicGeometry.SymmetricPullback.Iso
public import StacksCore.Tactic.StacksAttribute

/-!
# The second Adams operator on the Grothendieck ring of vector bundles

Let `X` be a scheme and let `K₀(Vect(X))` be the Grothendieck ring
`AlgebraicGeometry.VectorBundleKZero` of finite locally free `𝒪_X`-modules, whose multiplication
is induced by tensor product and whose unit is the class of the structure sheaf. The *second
Adams operation* is the ring endomorphism `ψ²` of `K₀(Vect(X))` determined by

`ψ²([ℰ]) = [Sym² ℰ] - [⋀² ℰ]`

for a finite locally free module `ℰ`. It squares the class of an invertible module, and it is
compatible with pullback along a morphism of schemes.

The two geometric facts the source's proof rests on — the three-step filtration of `Sym²` and
`⋀²` along a short exact sequence, and the two short exact sequences computing `Sym²` and `⋀²`
of a tensor product — are not in the library. They are collected in the predicate
`AlgebraicGeometry.VectorBundleKZero.SquarePowersData`, read in `K₀(Vect(X))`, which is exactly
the form in which the Grothendieck ring consumes them. Everything else is proved here. In
particular the value of `ψ²` on an invertible module is *not* assumed: it is proved from
`Stacks.SheafOfModules.symmetricPowerIsoTensorPowerOfIsInvertible`, which gives
`Sym² ℒ ≅ ℒ ⊗ ℒ`, and from the vanishing of `⋀² ℒ`, which is proved here.

## Main definitions

* `AlgebraicGeometry.VectorBundleKZero.secondSymmetricPower` and
  `secondExteriorPower`: `Sym² ℰ` and `⋀² ℰ` for a sheaf of modules on a scheme, taken in the
  chosen package `SheafOfModules.algebras` of tensor, exterior and symmetric algebras.
* `AlgebraicGeometry.VectorBundleKZero.SquarePowersData`: the geometric input of the source's
  proof — that the two squares preserve finite local freeness, the filtration relations, and the
  product relations.
* `AlgebraicGeometry.VectorBundleKZero.classOfSquareDifference` and `secondAdamsAddHom`: the
  function `ℰ ↦ [Sym² ℰ] - [⋀² ℰ]` on sheaves of modules, and the additive endomorphism of
  `K₀(Vect(X))` it descends to.
* `AlgebraicGeometry.VectorBundleKZero.secondAdamsRingHom`: the same as a ring endomorphism.
* `AlgebraicGeometry.VectorBundleKZero.pullbackSecondSymmetricPowerIso` and
  `pullbackSecondExteriorPowerIso`: `f^*(Sym² ℰ) ≅ Sym²(f^*ℰ)` and `f^*(⋀² ℰ) ≅ ⋀²(f^*ℰ)` for a
  morphism of schemes, Tag 01CI in degree two.

## Main results

* `Stacks.SheafOfModules.isZero_of_isFiniteLocallyFreeOfRank_zero`: a sheaf of modules which is
  finite locally free of rank zero is a zero object.
* `AlgebraicGeometry.VectorBundleKZero.isZero_secondExteriorPower_of_isInvertible` and
  `classOf_secondExteriorPower_of_isInvertible`: `⋀² ℒ = 0` for an invertible module `ℒ`.
* `AlgebraicGeometry.VectorBundleKZero.classOf_secondSymmetricPower_of_isInvertible`:
  `[Sym² ℒ] = [ℒ ⊗ ℒ]` for an invertible module `ℒ`.
* `AlgebraicGeometry.VectorBundleKZero.secondAdamsAddHom_classOf`,
  `secondAdamsAddHom_mul_classOf` and `secondAdamsAddHom_one`: the additive endomorphism takes
  the prescribed value on the class of a finite locally free module, is multiplicative on such
  classes, and preserves the unit.
* `AlgebraicGeometry.VectorBundleKZero.exists_secondAdamsOperator`: **the second Adams
  operation**, as a ring endomorphism of `K₀(Vect(X))` which sends `[ℰ]` to `[Sym² ℰ] - [⋀² ℰ]`,
  sends `[ℒ]` to `[ℒ ⊗ ℒ]` for invertible `ℒ`, and is compatible with pullbacks.
* `AlgebraicGeometry.VectorBundleKZero.secondAdamsAddHom_pullback`: the compatibility with
  pullback, in the form it is proved in.

## Implementation notes

**Which `Sym²` and `⋀²`.** Section 17.21 pins the symmetric and exterior algebras of a sheaf of
modules only up to canonical isomorphism, and the library accordingly quantifies over packages
`SheafOfModules.TensorExteriorSymmetricAlgebras J F`. `secondSymmetricPower` and
`secondExteriorPower` are the degree-two pieces of the *chosen* package
`SheafOfModules.algebras`, which is the package
`AlgebraicGeometry.Scheme.Modules.exteriorPower` is already defined from:
`secondExteriorPower_eq_exteriorPower` records that the exterior one is that existing
declaration at `n = 2`, by `rfl`. The library's other scheme-level symmetric algebra,
`AlgebraicGeometry.Scheme.Modules.symmetricAlgebra`, is a different *construction* of the same
notion — the degreewise sheafification of `U ↦ Symⁿ_{𝒪_X(U)}(ℰ(U))` — and is identified with
this one by `SheafOfModules.TensorExteriorSymmetricAlgebras.symmetricAlgebraIso`, which is why
nothing is redefined here; taking both squares in one package is what lets a single package
comparison serve for both.

**Why the geometric input is a predicate.** The source's argument for additivity filters
`Sym² ℱ` in three steps with graded pieces `Sym² ℰ`, `ℰ ⊗ 𝒢` and `Sym² 𝒢`, and likewise for
`⋀²`; the middle pieces agree, so they cancel in the difference. Its argument for
multiplicativity exhibits two short exact sequences of the squares of a tensor product. Neither
the filtration nor the two sequences is constructed anywhere in the library, so both are
hypotheses, assembled as `SquarePowersData` and named in the Stacks attribute. They are stated
as equalities of classes in `K₀(Vect(X))` rather than as short exact sequences of sheaves
because that is what the defining relation of the Grothendieck group turns them into, and the
relation refers to the objects of a sequence and not to its morphisms.

**The vanishing of `⋀² ℒ`.** An invertible module on a scheme is finite locally free of rank one
(the converse clause of Tag 0B8M,
`Stacks.SheafOfModules.isFiniteLocallyFreeOfRank_one_of_isInvertible`),
so `⋀² ℒ` is finite locally free of rank `binom(1, 2) = 0` by
`AlgebraicGeometry.Scheme.Modules.isFiniteLocallyFreeOfRank_exteriorPower`, and a sheaf of
modules of rank zero is a zero object. That last step is
`Stacks.SheafOfModules.isZero_of_isFiniteLocallyFreeOfRank_zero`, proved here: over each member
of a trivializing covering the module is free on an empty index type, hence zero, and the
identity of a sheaf of modules vanishing over a covering of the terminal object vanishes, by
`Stacks.SheafOfModules.SliceRestriction.overFunctor_map_injective`.

**Two spellings of finite local freeness.** `K₀(Vect(X))` is built over
`Stacks.FiniteLocallyFree.IsFiniteLocallyFree`, whereas the rank predicate used above is
`AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank` and its rankless form lives in
`AlgebraicGeometry.SheafOfModules`. The two rankless classes are interchanged by
`Stacks.StalkFreeBridge.finiteLocallyFree_isFiniteLocallyFree` and
`isFiniteLocallyFree_of_finiteLocallyFree`.

**The pullback.** The two comparisons `f^*(Sym² ℰ) ≅ Sym²(f^*ℰ)` and `f^*(⋀² ℰ) ≅ ⋀²(f^*ℰ)` are
proved, as `pullbackSecondSymmetricPowerIso` and `pullbackSecondExteriorPowerIso`: they are
Tag 01CI in degree two, which the library has for an arbitrary morphism of ringed spaces and for
symmetric and exterior algebras given by their universal properties
(`Stacks.RingedSpace.pullbackSymmetricPieceIso` and
`Stacks.PullbackExteriorAlgebra.exteriorAlgebraPullbackIso`), applied to the universal
properties carried by the chosen packages. What `secondAdamsAddHom_pullback` does take as
hypotheses is the pullback homomorphism of Grothendieck rings itself — a ring map sending `[ℰ]`
to `[f^*ℰ]` on finite locally free modules — and the stability of finite local freeness under
pullback. The functoriality of `K₀(Vect(-))` is not constructed anywhere in the library; the
compatibility proved here is the assertion that `ψ²` commutes with any homomorphism realising
it, which is the content of the source's clause once that functoriality is available.

## References

* [Stacks Project, Tag 0FEJ](https://stacks.math.columbia.edu/tag/0FEJ)
* [Stacks Project, Tag 0FDK](https://stacks.math.columbia.edu/tag/0FDK)
* [Stacks Project, Tag 0B8M](https://stacks.math.columbia.edu/tag/0B8M)
* [Stacks Project, Tag 01CI](https://stacks.math.columbia.edu/tag/01CI)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open Stacks.FiniteLocallyFree Stacks.SheafOfModules.TensorStalkRingedSpace

universe u v u₁

namespace Stacks.SheafOfModules

/-- A free sheaf of modules on an empty index type is a zero object. -/
theorem isZero_free_of_isEmpty {C : Type u₁} [Category.{v} C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u}} [HasWeakSheafify J AddCommGrpCat.{u}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}] (I : Type u) [IsEmpty I] :
    IsZero (_root_.SheafOfModules.free (R := R) I) := by
  refine (IsZero.iff_id_eq_zero _).2 ?_
  refine (_root_.SheafOfModules.free (R := R) I).freeHomEquiv.injective ?_
  funext i
  exact isEmptyElim i

/-- **A sheaf of modules which is finite locally free of rank zero is a zero object.** Over each
member of a trivializing covering it is free on an index type equivalent to `Fin 0`, hence zero,
so its identity vanishes over every member of a covering of the terminal object and therefore
vanishes. -/
theorem isZero_of_isFiniteLocallyFreeOfRank_zero {C : Type u₁} [Category.{v} C]
    {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
    [∀ U : C, HasWeakSheafify (J.over U) AddCommGrpCat.{u}]
    [∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}]
    (M : _root_.SheafOfModules.{u} R)
    (hM : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, v, u₁} M 0) :
    IsZero M := by
  obtain ⟨q, hq, hr⟩ := hM.exists_isFiniteLocallyFreeOfRankData
  refine (IsZero.iff_id_eq_zero M).2
    (SliceRestriction.overFunctor_map_injective q.coversTop (𝟙 M) 0 fun i => ?_)
  have hiso : IsIso (q.generators i).π := hq.isIso i
  have hempty : IsEmpty ((q.generators i).I) := ⟨fun x => ((hr i).some x).elim0⟩
  have hfree : IsZero (_root_.SheafOfModules.free (R := R.over (q.X i)) ((q.generators i).I)) :=
    isZero_free_of_isEmpty _
  exact (hfree.of_iso (asIso (q.generators i).π).symm).eq_of_tgt _ _

end Stacks.SheafOfModules

namespace AlgebraicGeometry.VectorBundleKZero

variable (X : Scheme.{u})

/-! ### The two squares of a sheaf of modules -/

/-- `Sym² ℰ`, the second symmetric power of a sheaf of modules on a scheme, taken in the chosen
package `SheafOfModules.algebras` of tensor, exterior and symmetric algebras. -/
noncomputable def secondSymmetricPower (E : X.Modules) : X.Modules :=
  (SheafOfModules.algebras (Opens.grothendieckTopology (X : TopCat)) E).symmetricPower 2

/-- `⋀² ℰ`, the second exterior power of a sheaf of modules on a scheme, taken in the chosen
package `SheafOfModules.algebras` of tensor, exterior and symmetric algebras. -/
@[ega "0 4.1.5" "special case"]
noncomputable def secondExteriorPower (E : X.Modules) : X.Modules :=
  (SheafOfModules.algebras (Opens.grothendieckTopology (X : TopCat)) E).exteriorPower 2

/-- The second exterior power is the library's `AlgebraicGeometry.Scheme.Modules.exteriorPower`
at `n = 2`: both are the degree-two piece of the exterior algebra of the chosen package. -/
theorem secondExteriorPower_eq_exteriorPower (E : X.Modules) :
    secondExteriorPower X E = Scheme.Modules.exteriorPower E 2 := rfl

/-- The second symmetric power of an invertible module is its tensor square: the symmetric
algebra of an invertible module is its tensor algebra, by
`Stacks.SheafOfModules.symmetricPowerIsoTensorPowerOfIsInvertible`, and the second tensor power
is the tensor square. -/
noncomputable def secondSymmetricPowerIsoTensorSquare (L : X.Modules)
    [Stacks.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L] :
    secondSymmetricPower X L ≅ Scheme.Modules.tensorObjRingedSpace X L L :=
  Stacks.SheafOfModules.symmetricPowerIsoTensorPowerOfIsInvertible X.sheaf L
    (SheafOfModules.algebras (Opens.grothendieckTopology (X : TopCat)) L) 2

variable {X}

section Invertible

variable (L : X.Modules)
  [hinv : Stacks.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]

/-- Invertibility of a sheaf of modules on a scheme, read over the underlying ringed space.
The two statements are the same proposition: the structure sheaf of rings of the ringed space
underlying `X` is the one `X.ringCatSheaf` names. -/
theorem isInvertible_toRingedSpace :
    Stacks.SheafOfModules.IsInvertible X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property L := hinv

/-- An invertible sheaf of modules on a scheme is finite locally free of rank one. This is the
converse clause of Tag 0B8M, read at the spelling of the rank predicate over `X.ringCatSheaf`. -/
theorem isFiniteLocallyFreeOfRank_one_of_isInvertible :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (R := X.ringCatSheaf) L 1 :=
  have := isInvertible_toRingedSpace L
  Stacks.SheafOfModules.isFiniteLocallyFreeOfRank_one_of_isInvertible (X := X.toRingedSpace) L

/-- An invertible sheaf of modules on a scheme is finite locally free, at the spelling of finite
local freeness that `K₀(Vect(X))` is built over. -/
theorem isFiniteLocallyFree_of_isInvertible :
    IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) L :=
  have _h1 : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (R := X.ringCatSheaf) L 1 :=
    isFiniteLocallyFreeOfRank_one_of_isInvertible L
  have _h2 : SheafOfModules.IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) L :=
    SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree (R := X.ringCatSheaf) L 1
  Stacks.StalkFreeBridge.finiteLocallyFree_isFiniteLocallyFree L

/-- **The second exterior power of an invertible module vanishes.** An invertible module is
finite locally free of rank one, so its second exterior power is finite locally free of rank
`binom(1, 2) = 0`, and a module of rank zero is a zero object. -/
theorem isZero_secondExteriorPower_of_isInvertible : IsZero (secondExteriorPower X L) := by
  have hL : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (R := X.ringCatSheaf) L 1 :=
    isFiniteLocallyFreeOfRank_one_of_isInvertible L
  have h2 := @Scheme.Modules.isFiniteLocallyFreeOfRank_exteriorPower X L 1 2 hL
  rw [show Nat.choose 1 2 = 0 from rfl] at h2
  exact Stacks.SheafOfModules.isZero_of_isFiniteLocallyFreeOfRank_zero
    (secondExteriorPower X L) h2

/-- The class of the second exterior power of an invertible module is zero. -/
theorem classOf_secondExteriorPower_of_isInvertible :
    classOf X (secondExteriorPower X L) = 0 :=
  (classOf_eq_of_iso (isZero_secondExteriorPower_of_isInvertible L).isoZero.symm
    (isFiniteLocallyFree_zero X)).symm.trans (classOf_zero X)

/-- The class of the second symmetric power of an invertible module is the class of its tensor
square. -/
theorem classOf_secondSymmetricPower_of_isInvertible :
    classOf X (secondSymmetricPower X L) =
      classOf X (Scheme.Modules.tensorObjRingedSpace X L L) :=
  have hL : IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) L :=
    isFiniteLocallyFree_of_isInvertible L
  (classOf_eq_of_iso (secondSymmetricPowerIsoTensorSquare X L).symm
    (@isFiniteLocallyFree_tensorObj X L L hL hL)).symm

end Invertible

/-! ### The geometric input of the source's proof -/

/-- **The geometric input of Tag 0FEJ.** The four facts about the second symmetric and exterior
powers that the source's proof of Tag 0FEJ uses; they hold for every scheme, by
`AlgebraicGeometry.VectorBundleKZero.squarePowersData`:

* they preserve finite local freeness;
* along a short exact sequence `0 → ℰ → ℱ → 𝒢 → 0` of finite locally free modules, `Sym² ℱ` has
  a three-step filtration with graded pieces `Sym² ℰ`, `ℰ ⊗ 𝒢` and `Sym² 𝒢`, and `⋀² ℱ` one with
  graded pieces `⋀² ℰ`, `ℰ ⊗ 𝒢` and `⋀² 𝒢`;
* the two short exact sequences
  `0 → ⋀²ℰ ⊗ ⋀²ℱ → Sym²(ℰ ⊗ ℱ) → Sym²ℰ ⊗ Sym²ℱ → 0` and
  `0 → Sym²ℰ ⊗ ⋀²ℱ → ⋀²(ℰ ⊗ ℱ) → ⋀²ℰ ⊗ Sym²ℱ → 0`.

The last three are recorded as the equalities of classes in `K₀(Vect(X))` that the defining
relation of the Grothendieck group turns them into. -/
structure SquarePowersData (X : Scheme.{u}) : Prop where
  /-- The second symmetric power of a finite locally free module is finite locally free. -/
  isFiniteLocallyFree_sym : ∀ E : X.Modules,
    IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) E →
      IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) (secondSymmetricPower X E)
  /-- The second exterior power of a finite locally free module is finite locally free. -/
  isFiniteLocallyFree_alt : ∀ E : X.Modules,
    IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) E →
      IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) (secondExteriorPower X E)
  /-- The filtration of `Sym²` along a short exact sequence of finite locally free modules. -/
  classOf_sym_shortExact : ∀ {E F G : X.Modules} (f : E ⟶ F) (g : F ⟶ G) (w : f ≫ g = 0),
    IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) E →
      IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) F →
        IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) G →
          Mono f → Epi g → (ShortComplex.mk f g w).Exact →
            classOf X (secondSymmetricPower X F) =
              classOf X (secondSymmetricPower X E) +
                classOf X (Scheme.Modules.tensorObjRingedSpace X E G) +
                  classOf X (secondSymmetricPower X G)
  /-- The filtration of `⋀²` along a short exact sequence of finite locally free modules. -/
  classOf_alt_shortExact : ∀ {E F G : X.Modules} (f : E ⟶ F) (g : F ⟶ G) (w : f ≫ g = 0),
    IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) E →
      IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) F →
        IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) G →
          Mono f → Epi g → (ShortComplex.mk f g w).Exact →
            classOf X (secondExteriorPower X F) =
              classOf X (secondExteriorPower X E) +
                classOf X (Scheme.Modules.tensorObjRingedSpace X E G) +
                  classOf X (secondExteriorPower X G)
  /-- The short exact sequence `0 → ⋀²ℰ ⊗ ⋀²ℱ → Sym²(ℰ ⊗ ℱ) → Sym²ℰ ⊗ Sym²ℱ → 0`. -/
  classOf_sym_tensor : ∀ E F : X.Modules,
    IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) E →
      IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) F →
        classOf X (secondSymmetricPower X (Scheme.Modules.tensorObjRingedSpace X E F)) =
          classOf X (Scheme.Modules.tensorObjRingedSpace X
              (secondExteriorPower X E) (secondExteriorPower X F)) +
            classOf X (Scheme.Modules.tensorObjRingedSpace X
              (secondSymmetricPower X E) (secondSymmetricPower X F))
  /-- The short exact sequence `0 → Sym²ℰ ⊗ ⋀²ℱ → ⋀²(ℰ ⊗ ℱ) → ⋀²ℰ ⊗ Sym²ℱ → 0`. -/
  classOf_alt_tensor : ∀ E F : X.Modules,
    IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) E →
      IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) F →
        classOf X (secondExteriorPower X (Scheme.Modules.tensorObjRingedSpace X E F)) =
          classOf X (Scheme.Modules.tensorObjRingedSpace X
              (secondSymmetricPower X E) (secondExteriorPower X F)) +
            classOf X (Scheme.Modules.tensorObjRingedSpace X
              (secondExteriorPower X E) (secondSymmetricPower X F))

/-! ### The additive endomorphism -/

open scoped Classical in
/-- `[Sym² ℰ] - [⋀² ℰ]` for a finite locally free module, and zero on the sheaves of modules
that are not finite locally free. This is the function on sheaves of modules of which the second
Adams operation is the descent. -/
noncomputable def classOfSquareDifference (X : Scheme.{u}) (E : X.Modules) :
    VectorBundleKZero X :=
  if IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) E then
    classOf X (secondSymmetricPower X E) - classOf X (secondExteriorPower X E) else 0

/-- On a finite locally free module, `classOfSquareDifference` is `[Sym² ℰ] - [⋀² ℰ]`. -/
theorem classOfSquareDifference_of_isFiniteLocallyFree (E : X.Modules)
    (hE : IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) E) :
    classOfSquareDifference X E =
      classOf X (secondSymmetricPower X E) - classOf X (secondExteriorPower X E) := by
  simp only [classOfSquareDifference]
  split_ifs with h
  · rfl
  · exact absurd hE h

/-- `classOfSquareDifference` vanishes off the finite locally free modules. -/
theorem classOfSquareDifference_eq_zero (E : X.Modules)
    (hE : ¬ IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) E) :
    classOfSquareDifference X E = 0 := by
  simp only [classOfSquareDifference]
  split_ifs with h
  · exact absurd h hE
  · rfl

/-- **Additivity of `[Sym² ·] - [⋀² ·]` along a short exact sequence.** The two filtrations have
the same middle graded piece `ℰ ⊗ 𝒢`, so it cancels in the difference. -/
theorem classOfSquareDifference_shortExact (h : SquarePowersData X) {E F G : X.Modules}
    (f : E ⟶ F) (g : F ⟶ G) (w : f ≫ g = 0)
    (hE : IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) E)
    (hF : IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) F)
    (hG : IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) G)
    (hmono : Mono f) (hepi : Epi g) (hex : (ShortComplex.mk f g w).Exact) :
    classOfSquareDifference X F = classOfSquareDifference X E + classOfSquareDifference X G := by
  rw [classOfSquareDifference_of_isFiniteLocallyFree E hE,
    classOfSquareDifference_of_isFiniteLocallyFree F hF,
    classOfSquareDifference_of_isFiniteLocallyFree G hG,
    h.classOf_sym_shortExact f g w hE hF hG hmono hepi hex,
    h.classOf_alt_shortExact f g w hE hF hG hmono hepi hex]
  abel

/-- The additive endomorphism of `K₀(Vect(X))` induced by `ℰ ↦ [Sym² ℰ] - [⋀² ℰ]`. -/
noncomputable def secondAdamsAddHom (h : SquarePowersData X) :
    VectorBundleKZero X →+ VectorBundleKZero X :=
  liftAddHom (classOfSquareDifference X) classOfSquareDifference_eq_zero
    (classOfSquareDifference_shortExact h)

/-- The additive endomorphism sends the class of a finite locally free module `ℰ` to
`[Sym² ℰ] - [⋀² ℰ]`. -/
theorem secondAdamsAddHom_classOf (h : SquarePowersData X) (E : X.Modules)
    (hE : IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) E) :
    secondAdamsAddHom h (classOf X E) =
      classOf X (secondSymmetricPower X E) - classOf X (secondExteriorPower X E) :=
  (liftAddHom_classOf (classOfSquareDifference X) classOfSquareDifference_eq_zero
    (classOfSquareDifference_shortExact h) E).trans
      (classOfSquareDifference_of_isFiniteLocallyFree E hE)

/-- **Multiplicativity on the classes of finite locally free modules.** Expanding the two
product relations,
`([Sym²ℰ] - [⋀²ℰ])([Sym²ℱ] - [⋀²ℱ]) = [Sym²(ℰ ⊗ ℱ)] - [⋀²(ℰ ⊗ ℱ)]`. -/
theorem secondAdamsAddHom_mul_classOf (h : SquarePowersData X) (E F : X.Modules)
    (hE : IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) E)
    (hF : IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) F) :
    secondAdamsAddHom h (classOf X E * classOf X F) =
      secondAdamsAddHom h (classOf X E) * secondAdamsAddHom h (classOf X F) := by
  have hEF : IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf)
      (Scheme.Modules.tensorObjRingedSpace X E F) :=
    @isFiniteLocallyFree_tensorObj X E F hE hF
  rw [classOf_mul E F hE hF, secondAdamsAddHom_classOf h _ hEF,
    secondAdamsAddHom_classOf h E hE, secondAdamsAddHom_classOf h F hF,
    h.classOf_sym_tensor E F hE hF, h.classOf_alt_tensor E F hE hF,
    ← classOf_mul _ _ (h.isFiniteLocallyFree_alt E hE) (h.isFiniteLocallyFree_alt F hF),
    ← classOf_mul _ _ (h.isFiniteLocallyFree_sym E hE) (h.isFiniteLocallyFree_sym F hF),
    ← classOf_mul _ _ (h.isFiniteLocallyFree_sym E hE) (h.isFiniteLocallyFree_alt F hF),
    ← classOf_mul _ _ (h.isFiniteLocallyFree_alt E hE) (h.isFiniteLocallyFree_sym F hF)]
  ring

/-! ### The value on an invertible module -/

/-- **The second Adams operation squares the class of an invertible module.**
`ψ²([ℒ]) = [ℒ ⊗ ℒ] = [ℒ]²`: the second symmetric power of `ℒ` is its tensor square and its
second exterior power vanishes. -/
theorem secondAdamsAddHom_classOf_isInvertible (h : SquarePowersData X) (L : X.Modules)
    [Stacks.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L] :
    secondAdamsAddHom h (classOf X L) =
      classOf X (Scheme.Modules.tensorObjRingedSpace X L L) := by
  have hL : IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) L :=
    isFiniteLocallyFree_of_isInvertible L
  rw [secondAdamsAddHom_classOf h L hL,
    classOf_secondSymmetricPower_of_isInvertible L,
    classOf_secondExteriorPower_of_isInvertible L, sub_zero]

/-- The second Adams operation preserves the unit of `K₀(Vect(X))`: the structure sheaf is
invertible, so the unit is the class of an invertible module and the preceding computation
applies to it. -/
theorem secondAdamsAddHom_one (h : SquarePowersData X) : secondAdamsAddHom h 1 = 1 := by
  have hinv : Stacks.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property
      (SheafOfModules.unit X.ringCatSheaf) :=
    Stacks.SheafOfModules.isInvertible_unit X.sheaf.obj X.ringCatSheaf.property
  have hvalue := secondAdamsAddHom_classOf_isInvertible h (SheafOfModules.unit X.ringCatSheaf)
  have hunit : classOf X (Scheme.Modules.tensorObjRingedSpace X
      (SheafOfModules.unit X.ringCatSheaf) (SheafOfModules.unit X.ringCatSheaf)) = 1 := by
    rw [← classOf_mul _ _ (isFiniteLocallyFree_unit X) (isFiniteLocallyFree_unit X),
      classOf_unit, one_mul]
  exact hvalue.trans hunit

/-! ### The ring endomorphism -/

/-- The second Adams operation is multiplicative, by `addHom_ext` from its multiplicativity on
the classes of finite locally free modules. -/
theorem secondAdamsAddHom_mul (h : SquarePowersData X) (a b : VectorBundleKZero X) :
    secondAdamsAddHom h (a * b) = secondAdamsAddHom h a * secondAdamsAddHom h b := by
  have key : ∀ E : X.Modules, IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) E →
      (secondAdamsAddHom h).comp (mul X (classOf X E)) =
        (mul X (secondAdamsAddHom h (classOf X E))).comp (secondAdamsAddHom h) :=
    fun E hE => addHom_ext fun F hF => secondAdamsAddHom_mul_classOf h E F hE hF
  have hstep : (secondAdamsAddHom h).comp (mulRight b) =
      (mulRight (secondAdamsAddHom h b)).comp (secondAdamsAddHom h) :=
    addHom_ext fun E hE => DFunLike.congr_fun (key E hE) b
  exact DFunLike.congr_fun hstep a

/-- The second Adams operation as a ring endomorphism of `K₀(Vect(X))`. -/
noncomputable def secondAdamsRingHom (h : SquarePowersData X) :
    VectorBundleKZero X →+* VectorBundleKZero X where
  toFun := secondAdamsAddHom h
  map_one' := secondAdamsAddHom_one h
  map_mul' := secondAdamsAddHom_mul h
  map_zero' := map_zero (secondAdamsAddHom h)
  map_add' := map_add (secondAdamsAddHom h)

@[simp] theorem secondAdamsRingHom_apply (h : SquarePowersData X) (a : VectorBundleKZero X) :
    secondAdamsRingHom h a = secondAdamsAddHom h a := rfl

/-! ### Compatibility with pullback -/

section Pullback

variable {Y : Scheme.{u}}

/-- **Tag 01CI for the second symmetric power.** `f^*(Sym² ℰ) ≅ Sym²(f^*ℰ)` for a morphism of
schemes `f : X ⟶ Y`. Both sides are degree-two pieces of symmetric algebras of `f^*ℰ`, the
first because the pullback of a symmetric algebra is one, so this is
`Stacks.RingedSpace.pullbackSymmetricPieceIso` applied to the universal properties carried by
the chosen packages. -/
noncomputable def pullbackSecondSymmetricPowerIso (f : X ⟶ Y) (E : Y.Modules) :
    (Scheme.Modules.pullback f).obj (secondSymmetricPower Y E) ≅
      secondSymmetricPower X ((Scheme.Modules.pullback f).obj E) :=
  Stacks.RingedSpace.pullbackSymmetricPieceIso f.toLRSHom.toShHom
    (SheafOfModules.algebras (Opens.grothendieckTopology (Y : TopCat))
      E).symmetric_isSymmetricAlgebra
    (SheafOfModules.algebras (Opens.grothendieckTopology (X : TopCat))
      ((Scheme.Modules.pullback f).obj E)).symmetric_isSymmetricAlgebra 2

/-- **Tag 01CI for the second exterior power.** `f^*(⋀² ℰ) ≅ ⋀²(f^*ℰ)` for a morphism of
schemes `f : X ⟶ Y`, the degree-two component of
`Stacks.PullbackExteriorAlgebra.exteriorAlgebraPullbackIso` applied to the universal properties
carried by the chosen packages. -/
noncomputable def pullbackSecondExteriorPowerIso (f : X ⟶ Y) (E : Y.Modules) :
    (Scheme.Modules.pullback f).obj (secondExteriorPower Y E) ≅
      secondExteriorPower X ((Scheme.Modules.pullback f).obj E) :=
  (Stacks.PullbackExteriorAlgebra.exteriorAlgebraPullbackIso f.toLRSHom.toShHom
    (SheafOfModules.algebras (Opens.grothendieckTopology (Y : TopCat)) E).exterior
    (SheafOfModules.algebras (Opens.grothendieckTopology (Y : TopCat)) E).exteriorGenerator
    (SheafOfModules.algebras (Opens.grothendieckTopology (X : TopCat))
      ((Scheme.Modules.pullback f).obj E)).exterior
    (SheafOfModules.algebras (Opens.grothendieckTopology (X : TopCat))
      ((Scheme.Modules.pullback f).obj E)).exteriorGenerator
    (SheafOfModules.algebras (Opens.grothendieckTopology (Y : TopCat))
      E).exterior_isExteriorAlgebra
    (SheafOfModules.algebras (Opens.grothendieckTopology (X : TopCat))
      ((Scheme.Modules.pullback f).obj E)).exterior_isExteriorAlgebra).app 2

/-- **The second Adams operation is compatible with pullback.** Let `f : X ⟶ Y` be a morphism of
schemes and let `p` be a ring homomorphism `K₀(Vect(Y)) → K₀(Vect(X))` sending the class of a
finite locally free module `ℰ` to the class of `f^*ℰ`. Granted that pullback preserves finite
local freeness, the operation commutes with `p`. The two comparisons
`f^*(Sym² ℰ) ≅ Sym²(f^*ℰ)` and `f^*(⋀² ℰ) ≅ ⋀²(f^*ℰ)` of Tag 01CI are not assumed: they are
`pullbackSecondSymmetricPowerIso` and `pullbackSecondExteriorPowerIso`. -/
theorem secondAdamsAddHom_pullback (f : X ⟶ Y)
    (hX : SquarePowersData X) (hY : SquarePowersData Y)
    (p : VectorBundleKZero Y →+* VectorBundleKZero X)
    (hp : ∀ E : Y.Modules, IsFiniteLocallyFree.{u, u, u} (R := Y.ringCatSheaf) E →
      p (classOf Y E) = classOf X ((Scheme.Modules.pullback f).obj E))
    (hflf : ∀ E : Y.Modules, IsFiniteLocallyFree.{u, u, u} (R := Y.ringCatSheaf) E →
      IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf)
        ((Scheme.Modules.pullback f).obj E))
    (a : VectorBundleKZero Y) :
    secondAdamsAddHom hX (p a) = p (secondAdamsAddHom hY a) := by
  have hcomp : (secondAdamsAddHom hX).comp (p : VectorBundleKZero Y →+ VectorBundleKZero X) =
      (p : VectorBundleKZero Y →+ VectorBundleKZero X).comp (secondAdamsAddHom hY) := by
    refine addHom_ext fun E hE => ?_
    have hsym := hY.isFiniteLocallyFree_sym E hE
    have halt := hY.isFiniteLocallyFree_alt E hE
    change secondAdamsAddHom hX (p (classOf Y E)) = p (secondAdamsAddHom hY (classOf Y E))
    rw [hp E hE, secondAdamsAddHom_classOf hX _ (hflf E hE), secondAdamsAddHom_classOf hY E hE,
      map_sub, hp _ hsym, hp _ halt,
      classOf_eq_of_iso (pullbackSecondSymmetricPowerIso f E) (hflf _ hsym),
      classOf_eq_of_iso (pullbackSecondExteriorPowerIso f E) (hflf _ halt)]
  exact DFunLike.congr_fun hcomp a

end Pullback

/-! ### The theorem -/

/-- **Stacks Project, Tag 0FEJ.** For a scheme `X` there is a ring map
`ψ² : K₀(Vect(X)) → K₀(Vect(X))` which sends `[ℒ]` to `[ℒ^{⊗2}]` when `ℒ` is invertible and is
compatible with pullbacks. It is given on the class of a finite locally free module `ℰ` by
`ψ²([ℰ]) = [Sym² ℰ] - [⋀² ℰ]`.

The three clauses of the source are present: `ψ²` is a `RingHom`, the second conjunct is its
value on an invertible module, and the third is its commutation with any ring map of
Grothendieck rings realising pullback of finite locally free modules. The first conjunct records
the construction `ψ²([ℰ]) = [Sym² ℰ] - [⋀² ℰ]`.

The parameter `SquarePowersData X` is the geometric input of the source's proof: the
filtration of the two squares along a short exact sequence and the two short exact sequences
computing the squares of a tensor product. It holds for every scheme, by
`AlgebraicGeometry.VectorBundleKZero.squarePowersData`; the unconditional statement, with the
pullback ring map of `K₀(Vect(-))`, is
`AlgebraicGeometry.VectorBundleKZero.exists_secondAdamsOperator_pullbackRingHom`. The value on
an invertible module is not assumed; it is proved. -/
theorem exists_secondAdamsOperator (X : Scheme.{u}) (h : SquarePowersData X) :
    ∃ ψ : VectorBundleKZero X →+* VectorBundleKZero X,
      (∀ E : X.Modules, IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) E →
          ψ (classOf X E) =
            classOf X (secondSymmetricPower X E) - classOf X (secondExteriorPower X E)) ∧
        (∀ L : X.Modules,
          ∀ _ : Stacks.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L,
            ψ (classOf X L) = classOf X (Scheme.Modules.tensorObjRingedSpace X L L)) ∧
        (∀ (Y : Scheme.{u}) (f : Y ⟶ X) (hY : SquarePowersData Y)
            (p : VectorBundleKZero X →+* VectorBundleKZero Y),
          (∀ E : X.Modules, IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) E →
              p (classOf X E) = classOf Y ((Scheme.Modules.pullback f).obj E)) →
            (∀ E : X.Modules, IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) E →
              IsFiniteLocallyFree.{u, u, u} (R := Y.ringCatSheaf)
                ((Scheme.Modules.pullback f).obj E)) →
              ∀ a : VectorBundleKZero X, secondAdamsAddHom hY (p a) = p (ψ a)) :=
  ⟨secondAdamsRingHom h,
    fun E hE => secondAdamsAddHom_classOf h E hE,
    fun L _hinv => secondAdamsAddHom_classOf_isInvertible h L,
    fun _Y f hY p hp hflf a => secondAdamsAddHom_pullback f hY h p hp hflf a⟩

end AlgebraicGeometry.VectorBundleKZero

end
