module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.Completion
public import StacksFrontier.AlgebraicGeometry.Spaces.SchemeAsSpace
public import StacksFrontier.AlgebraicGeometry.Spaces.SubspacePreimage
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.Order

/-!
# Completion of an algebraic space along a closed subspace

Let `S` be a scheme contained in a big fppf site `B`, let `X` be an algebraic space over `S`
and let `Z ⊂ X` be a closed subspace. The *completion* `X^∧_Z` of `X` along `Z` is the colimit
of the infinitesimal neighbourhoods `Z_n ⊂ X`, formed in fppf sheaves.

This file constructs that completion and proves that it is compatible with base change: for a
morphism `f : X' ⟶ X` of algebraic spaces over `S` and `Z' = f⁻¹(Z) = X' ×_X Z`, the square

```
  (X')^∧_{Z'} ⟶ X'
       |          |
       v          v
    X^∧_Z     ⟶  X
```

is a cartesian square of sheaves, and consequently `(X')^∧_{Z'} ⟶ X^∧_Z` is representable by
algebraic spaces.

## Main definitions

* `AlgebraicGeometry.Space.IsUniversalNthOrderThickening` is the condition on a subfunctor of
  a representable presheaf that each of its base changes along a morphism out of a
  representable presheaf is an `n`th-order thickening.
* `AlgebraicGeometry.Space.completionSubspaceSubfunctor` is the subfunctor of the universe
  lift of `X` whose sections are those whose inverse image of `Z` is universally a
  finite-order thickening, that is, the union of the infinitesimal neighbourhoods `Z_n`.
* `AlgebraicGeometry.Space.completionSubspace` is **Stacks 0GXU**, the completion `X^∧_Z`:
  the fppf sheafification of that subfunctor. Its canonical morphism to the ambient sheaf of
  `X` is `AlgebraicGeometry.Space.completionSubspaceToAmbient`, and the morphism of
  completions induced by a morphism of algebraic spaces is
  `AlgebraicGeometry.Space.completionSubspaceMap`.

## Main results

* `AlgebraicGeometry.Space.isPullback_completionSubspaceMap`: **Stacks 0GXV**, the completion
  square of a morphism of algebraic spaces is cartesian.
* `AlgebraicGeometry.Space.isRepresentableByAlgebraicSpacesULift_completionSubspaceMap`:
  **Stacks 0GXV**, the induced morphism of completions is representable by algebraic spaces.
* `AlgebraicGeometry.Space.preimage_yonedaEquiv_symm`: the inverse image of `Z` along a
  section of `X'` is the inverse image of `Z'` along the corresponding section of `X`, which
  is what makes the completion square cartesian.

## Implementation notes

The `n`th infinitesimal neighbourhood `Z_n ⊂ X` is the closed subspace cut out by the
`(n+1)`st power of the ideal of `Z`; a scheme-valued point `g : T ⟶ X` therefore factors
through `Z_n` exactly when the `(n+1)`st power of the ideal of `g⁻¹(Z) ⊂ T` vanishes, that is
exactly when `g⁻¹(Z) ⊂ T` is an `n`th-order thickening in the sense of Stacks 05ZK part (4),
namely `AlgebraicGeometry.Space.IsNthOrderThickening`. Note that the power condition forces
the inverse image to be a thickening, so nothing is lost by using the bundled notion. The
neighbourhoods are therefore *defined* here by that functor of points, which avoids
constructing powers of the quasi-coherent ideal sheaf of a closed subspace of an algebraic
space — machinery this library does not have, see the implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/ClosedSubspaceIdealBijection.lean`.

The one place where that absence is felt is restriction-stability: `Z_n` is a subfunctor of
`X`, so the condition cutting it out must be inherited by restrictions of a section, which is
base change of an `n`th-order thickening, Stacks 09ZX parts (2) to (4). That statement is not
available here either (see the implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/Thickenings/BaseChange.lean`), so the condition is
quantified over all base changes from the outset: `IsUniversalNthOrderThickening` asks every
base change of the inverse image to be an `n`th-order thickening. Taking the identity base
change recovers the unquantified condition
(`AlgebraicGeometry.Space.IsUniversalNthOrderThickening.isNthOrderThickening`), and conversely
a section factoring through the subfunctor `Z_n` has all of its restrictions factoring through
`Z_n` as well, so the two conditions cut out the same subfunctor of `X`; the quantified one is
manifestly stable under restriction
(`AlgebraicGeometry.Space.IsUniversalNthOrderThickening.preimage`).

The colimit over `n` of the `Z_n` is an increasing union of subfunctors of `X`, so it is taken
here as the single condition that *some* `n` works, uniformly in the base change. Sheafifying
that union is the colimit in sheaves, since sheafification is a left adjoint.

The completion square is cartesian already before sheafifying. Indeed the inverse image of `Z`
along a section `g` of `X'` and the inverse image of `Z' = f⁻¹(Z)` along the corresponding
section `f ∘ g` of `X` are *the same* subfunctor, by `CategoryTheory.Subfunctor.preimage_comp`
and `CategoryTheory.yonedaEquiv_symm_naturality_right`; hence the sections of the completion
of `X'` along `Z'` over an object of the site are exactly the sections of `X'` whose image in
`X` is a section of the completion of `X` along `Z`, which is the cartesian square sectionwise.
Sheafification preserves fibre products, so the square of sheaves is cartesian too, and
representability then follows from Stacks 0APZ exactly as in
`StacksFrontier/AlgebraicGeometry/FormalSpace/Completion.lean`.

That `Z' = f⁻¹(Z)` really is the fibre product `X' ×_X Z` of the source is not assumed: the
inverse image is `CategoryTheory.Subfunctor.preimage`, which
`CategoryTheory.Subfunctor.isPullback_preimage` (Stacks 083Q) exhibits as that fibre product,
and `AlgebraicGeometry.Space.isClosedSubspace_preimage` (Stacks 083Q) shows it is again a
closed subspace.

Closedness of `Z` is used nowhere below, exactly as for the completion along a set of points
in `StacksFrontier/AlgebraicGeometry/FormalSpace/Completion.lean`: it is what makes the
completion a formal algebraic space, which is a separate assertion, so both statements are
proved for an arbitrary subfunctor `Z` of `X`.

## References

* [Stacks Project, Tag 0GXU](https://stacks.math.columbia.edu/tag/0GXU)
* [Stacks Project, Tag 0GXV](https://stacks.math.columbia.edu/tag/0GXV)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Thickenings

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Universal `n`th-order thickenings of an object of the site -/

/-- A subfunctor `G` of the presheaf represented by an object `U` of the big fppf site of `S`
is a *universal `n`th-order thickening* when every base change of `G` along a morphism out of
a representable presheaf is an `n`th-order thickening of that representable presheaf. -/
def IsUniversalNthOrderThickening (n : ℕ) (U : BigFppfOver B S hS)
    (G : Subfunctor (yoneda.obj U)) : Prop :=
  ∀ (V : BigFppfOver B S hS) (k : yoneda.obj V ⟶ yoneda.obj U),
    IsNthOrderThickening B S hS n ((schemeSpaceFunctor B S hS).obj V)
      (G.preimage k : Subfunctor (yoneda.obj V))

/-- A universal `n`th-order thickening is an `n`th-order thickening: take the identity base
change. Together with `AlgebraicGeometry.Space.IsUniversalNthOrderThickening.preimage` this
says that the quantification over base changes adds nothing beyond restriction-stability. -/
theorem IsUniversalNthOrderThickening.isNthOrderThickening {n : ℕ}
    {U : BigFppfOver B S hS} {G : Subfunctor (yoneda.obj U)}
    (hG : IsUniversalNthOrderThickening B S hS n U G) :
    IsNthOrderThickening B S hS n ((schemeSpaceFunctor B S hS).obj U) G := by
  simpa only [Subfunctor.preimage_id] using hG U (𝟙 _)

/-- A base change of a universal `n`th-order thickening is a universal `n`th-order
thickening: a base change of a base change is a base change. -/
theorem IsUniversalNthOrderThickening.preimage {n : ℕ} {U V : BigFppfOver B S hS}
    {G : Subfunctor (yoneda.obj U)} (hG : IsUniversalNthOrderThickening B S hS n U G)
    (l : yoneda.obj V ⟶ yoneda.obj U) :
    IsUniversalNthOrderThickening B S hS n V (G.preimage l) := by
  intro W k
  simpa only [Subfunctor.preimage_comp] using hG W (k ≫ l)

/-! ### The completion of an algebraic space along a closed subspace -/

/-- The inverse image of a subfunctor `Z` of `X` along the section of `X` determined by a
section `g` of `X'` and a morphism `f : X' ⟶ X` is the inverse image along `g` of the inverse
image of `Z` along `f`. -/
theorem preimage_yonedaEquiv_symm {X' X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X' ⟶ X)
    (Z : Subfunctor X) {U : BigFppfOver B S hS} (g : X'.obj (op U)) :
    (Z.preimage f).preimage (yonedaEquiv.symm g) =
      Z.preimage (yonedaEquiv.symm (f.app (op U) g)) := by
  rw [← Subfunctor.preimage_comp, yonedaEquiv_symm_naturality_right]

/-- The subfunctor of the universe lift of an algebraic space `X` whose sections over an
object of the big fppf site of `S` are those sections whose inverse image of `Z` is a
universal `n`th-order thickening for some `n`; that is, the union of the infinitesimal
neighbourhoods of `Z` in `X`.

Restriction preserves the condition because a base change of a universal `n`th-order
thickening is one, with the same `n`. -/
def completionSubspaceSubfunctor (X : AlgebraicSpaces B S hS) (Z : Subfunctor X.1) :
    Subfunctor (X.1 ⋙ uliftFunctor.{u + 1}) where
  obj U := {g | ∃ n, IsUniversalNthOrderThickening B S hS n U.unop
    (Z.preimage (yonedaEquiv.symm g.down : yoneda.obj U.unop ⟶ X.1))}
  map {U V} i g hg := by
    obtain ⟨n, hn⟩ := hg
    refine ⟨n, ?_⟩
    have hres : (yonedaEquiv.symm ((X.1 ⋙ uliftFunctor.{u + 1}).map i g).down
        : yoneda.obj V.unop ⟶ X.1) = yoneda.map i.unop ≫ yonedaEquiv.symm g.down :=
      yonedaEquiv_symm_map i g.down
    rw [hres, Subfunctor.preimage_comp]
    exact hn.preimage B S hS (yoneda.map i.unop)

/-- **Stacks 0GXU.** The completion `X^∧_Z` of an algebraic space `X` over `S` along a closed
subspace `Z`: the fppf sheafification of the union of the infinitesimal neighbourhoods of `Z`
in `X`, which is their colimit in fppf sheaves. -/
@[stacks 0GXU "the completion along a closed subspace"]
def completionSubspace (X : AlgebraicSpaces B S hS) (Z : Subfunctor X.1) :
    Sheaf (BigFppfOver.topology B S hS) (Type (u + 1)) :=
  ⟨(BigFppfOver.topology B S hS).sheafify (completionSubspaceSubfunctor B S hS X Z).toFunctor,
    (BigFppfOver.topology B S hS).sheafify_isSheaf _⟩

/-- The canonical morphism `X^∧_Z ⟶ X` from the completion of `X` along `Z` into `X` itself,
sheafified in `Type (u + 1)`. -/
def completionSubspaceToAmbient (X : AlgebraicSpaces B S hS) (Z : Subfunctor X.1) :
    completionSubspace B S hS X Z ⟶ sheafifiedULift B S hS X.1 :=
  ObjectProperty.homMk ((BigFppfOver.topology B S hS).sheafifyMap
    (completionSubspaceSubfunctor B S hS X Z).ι)

/-! ### Functoriality of the completion -/

/-- A section of `X'` lies in the completion subfunctor of `X'` along `f⁻¹(Z)` exactly when
its image in `X` lies in the completion subfunctor of `X` along `Z`: the two conditions are
imposed on one and the same subfunctor of the representable presheaf. -/
theorem mem_completionSubspaceSubfunctor_preimage {X' X : AlgebraicSpaces B S hS} (f : X' ⟶ X)
    (Z : Subfunctor X.1) (U : (BigFppfOver B S hS)ᵒᵖ)
    (g : (X'.1 ⋙ uliftFunctor.{u + 1}).obj U) :
    g ∈ (completionSubspaceSubfunctor B S hS X' (Z.preimage f.hom)).obj U ↔
      (ULift.up (f.hom.app U g.down) : (X.1 ⋙ uliftFunctor.{u + 1}).obj U) ∈
        (completionSubspaceSubfunctor B S hS X Z).obj U := by
  change (∃ n, IsUniversalNthOrderThickening B S hS n U.unop
      ((Z.preimage f.hom).preimage (yonedaEquiv.symm g.down))) ↔
    (∃ n, IsUniversalNthOrderThickening B S hS n U.unop
      (Z.preimage (yonedaEquiv.symm (f.hom.app (op U.unop) g.down))))
  rw [preimage_yonedaEquiv_symm]

/-- The morphism of completion subfunctors induced by a morphism `f : X' ⟶ X` of algebraic
spaces over `S`, the source being completed along the inverse image of the closed subspace of
the target. -/
def completionSubspaceSubfunctorMap {X' X : AlgebraicSpaces B S hS} (f : X' ⟶ X)
    (Z : Subfunctor X.1) :
    (completionSubspaceSubfunctor B S hS X' (Z.preimage f.hom)).toFunctor ⟶
      (completionSubspaceSubfunctor B S hS X Z).toFunctor where
  app U := ↾fun x => ⟨ULift.up (f.hom.app U x.1.down),
    (mem_completionSubspaceSubfunctor_preimage B S hS f Z U x.1).mp x.2⟩
  naturality := by
    intro U V i
    ext x
    apply Subtype.ext
    apply ULift.ext
    exact NatTrans.naturality_apply f.hom i x.1.down

/-- The morphism of completions `(X')^∧_{f⁻¹(Z)} ⟶ X^∧_Z` induced by a morphism
`f : X' ⟶ X` of algebraic spaces over `S`. -/
def completionSubspaceMap {X' X : AlgebraicSpaces B S hS} (f : X' ⟶ X) (Z : Subfunctor X.1) :
    completionSubspace B S hS X' (Z.preimage f.hom) ⟶ completionSubspace B S hS X Z :=
  ObjectProperty.homMk ((BigFppfOver.topology B S hS).sheafifyMap
    (completionSubspaceSubfunctorMap B S hS f Z))

/-! ### The completion square -/

/-- The completion square of a morphism of algebraic spaces is cartesian already before
sheafifying: it is a cartesian square of presheaves of `Type (u + 1)`, checked on sections
over each object of the site, where it says that the completion condition on a section of `X'`
is the completion condition on its image in `X`. -/
private theorem completionSubspaceSubfunctor_square_isPullback
    {X' X : AlgebraicSpaces B S hS} (f : X' ⟶ X) (Z : Subfunctor X.1) :
    IsPullback
      (completionSubspaceSubfunctor B S hS X' (Z.preimage f.hom)).ι
      (completionSubspaceSubfunctorMap B S hS f Z)
      (Functor.whiskerRight f.hom uliftFunctor.{u + 1})
      (completionSubspaceSubfunctor B S hS X Z).ι := by
  apply IsPullback.of_forall_isPullback_app
  intro U
  apply (Types.isPullback_iff
    (t := NatTrans.app (completionSubspaceSubfunctor B S hS X' (Z.preimage f.hom)).ι U)
    (r := NatTrans.app (Functor.whiskerRight f.hom uliftFunctor.{u + 1}) U)
    (l := NatTrans.app (completionSubspaceSubfunctorMap B S hS f Z) U)
    (b := NatTrans.app (completionSubspaceSubfunctor B S hS X Z).ι U)).2
  refine ⟨by ext z; rfl, fun a b h => Subtype.ext h.left, ?_⟩
  intro x y h
  have hval : f.hom.app U x.down = y.1.down := congrArg ULift.down h
  refine ⟨⟨x, ?_⟩, rfl, Subtype.ext (ULift.ext hval)⟩
  exact (mem_completionSubspaceSubfunctor_preimage B S hS f Z U x).2
    ((ULift.ext hval : (ULift.up (f.hom.app U x.down) : _) = y.1) ▸ y.2)

/-- **Stacks 0GXV.** Completion along a closed subspace is compatible with base change: for a
morphism `f : X' ⟶ X` of algebraic spaces over `S` and a subfunctor `Z` of `X`, in the source a
closed subspace, the square formed by the completion of `X'` along `Z' = f⁻¹(Z) = X' ×_X Z`,
the completion of `X` along `Z` and the two ambient sheaves is a cartesian square of fppf
sheaves. -/
@[stacks 0GXV "the square is cartesian"]
theorem isPullback_completionSubspaceMap {X' X : AlgebraicSpaces B S hS} (f : X' ⟶ X)
    (Z : Subfunctor X.1) :
    IsPullback
      (completionSubspaceToAmbient B S hS X' (Z.preimage f.hom))
      (completionSubspaceMap B S hS f Z)
      (sheafifiedULiftMap B S hS f.hom)
      (completionSubspaceToAmbient B S hS X Z) :=
  (completionSubspaceSubfunctor_square_isPullback B S hS f Z).map
    (CategoryTheory.plusPlusSheaf (BigFppfOver.topology B S hS) (Type (u + 1)))

/-- **Stacks 0GXV.** For a morphism `f : X' ⟶ X` of algebraic spaces over `S` and a subfunctor
`Z` of `X`, in the source a closed subspace, the induced morphism of completions
`(X')^∧_{f⁻¹(Z)} ⟶ X^∧_Z` is representable by algebraic spaces. -/
@[stacks 0GXV "representable by algebraic spaces"]
theorem isRepresentableByAlgebraicSpacesULift_completionSubspaceMap
    {X' X : AlgebraicSpaces B S hS} (f : X' ⟶ X) (Z : Subfunctor X.1) :
    IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS
      (completionSubspaceMap B S hS f Z).hom := by
  let C := BigFppfOver B S hS
  let J := BigFppfOver.topology B S hS
  let H := (Functor.whiskeringRight Cᵒᵖ (Type u) (Type (u + 1))).obj uliftFunctor.{u + 1}
  have hlarge : IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS (H.map f.hom) :=
    (isRepresentableByAlgebraicSpacesULift_whiskerRight_iff B S hS f.hom).mpr fun U ξ =>
      isAlgebraicSpace_pullback B S hS ξ f.hom (isAlgebraicSpace_yoneda B S hS U)
        X'.property X.property
  let e (Y : AlgebraicSpaces B S hS) : H.obj Y.1 ≅ (sheafifiedULift B S hS Y.1).obj :=
    J.isoSheafify ((isAlgebraicSpaceULift_comp_uliftFunctor_iff B S hS Y.1).mpr Y.property).isSheaf
  have hcomm : (sheafifiedULiftMap B S hS f.hom).hom ≫ (e X).inv = (e X').inv ≫ H.map f.hom := by
    have hn' : H.map f.hom ≫ (e X).hom = (e X').hom ≫ (sheafifiedULiftMap B S hS f.hom).hom := by
      change (Functor.whiskerRight f.hom uliftFunctor.{u + 1}) ≫
          J.toSheafify (X.1 ⋙ uliftFunctor.{u + 1}) =
        J.toSheafify (X'.1 ⋙ uliftFunctor.{u + 1}) ≫
          J.sheafifyMap (Functor.whiskerRight f.hom uliftFunctor.{u + 1})
      exact J.toSheafify_naturality _
    rw [Iso.comp_inv_eq, Category.assoc, Iso.eq_inv_comp, hn']
  have hp : IsPullback
      ((completionSubspaceToAmbient B S hS X' (Z.preimage f.hom)).hom ≫ (e X').inv)
      (completionSubspaceMap B S hS f Z).hom
      (H.map f.hom)
      ((completionSubspaceToAmbient B S hS X Z).hom ≫ (e X).inv) :=
    IsPullback.of_iso ((isPullback_completionSubspaceMap B S hS f Z).map
      (sheafToPresheaf J (Type (u + 1)))) (Iso.refl _) (e X').symm (Iso.refl _) (e X).symm
      (by simp) (by simp) hcomm (by simp)
  exact isRepresentableByAlgebraicSpacesULift_of_isPullback B S hS _ _ _ _ hp hlarge

end AlgebraicGeometry.Space

end
