module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.FromAffineSpace
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.RestrictExact

/-!
# Relative pseudo-coherence for a morphism of schemes

Let `f : X ⟶ S` be a morphism of schemes locally of finite type. An object `E` of the derived
category of `𝒪_X`-modules is *relatively `m`-pseudo-coherent* when there are an affine open cover
`V` of `S` and, for each member, an affine open cover `U` of `f⁻¹(V)` such that on each `U j` the
restriction of `E` becomes `m`-pseudo-coherent after derived pushforward along some closed
immersion of `U j` into an affine space over `V i` compatible with `f`. It is *relatively
pseudo-coherent* when this holds for every integer `m`. A sheaf of modules is called relatively
`m`-pseudo-coherent, resp. relatively pseudo-coherent, when it is so as a complex concentrated in
degree zero.

## Main definitions

* `AlgebraicGeometry.Scheme.Hom.IsPseudoCoherentFrom` and
  `AlgebraicGeometry.Scheme.Hom.IsPseudoCoherent` for objects of the derived category.
* `AlgebraicGeometry.Scheme.Hom.IsModulePseudoCoherentFrom` and
  `AlgebraicGeometry.Scheme.Hom.IsModulePseudoCoherent` for sheaves of modules.

## Implementation notes

Affine open covers are presented as families `V : ι → S.affineOpens` indexed by a type in the
universe of the schemes whose supremum is the top open, which is also the universe in which index
types of affine spaces live, so the coordinates of the closed immersions are indexed by
`ULift (Fin n)`.

The closed immersions asked for here do exist: that is the content of
`AlgebraicGeometry.exists_isClosedImmersion_affineSpace_resLE`, the remark the source makes
immediately before this definition, so the definition is not vacuous on any affine open. The
local condition itself is
`AlgebraicGeometry.Scheme.Modules.IsPseudoCoherentFromAfterPushforward`, the first of the
equivalent conditions of Stacks 09VC; by that lemma the choice of closed immersion does not
matter, but the definition commits to none.

Restriction of `E` to an affine open `U j` is through
`AlgebraicGeometry.Scheme.Modules.restrictFunctor`, whose exactness —
`AlgebraicGeometry.Scheme.Modules.restrictFunctor_additive` and
`AlgebraicGeometry.Scheme.Modules.restrictFunctor_preservesFiniteLimits` — is what makes the
induced functor on derived categories available.

The derived categories are the ones provided by `CategoryTheory.HasDerivedCategory.standard`,
which is made a local instance; there is no global instance, so a user of these definitions makes
the same declaration.

## References

* [The Stacks Project, Definition 36.61.1 (09UI)](https://stacks.math.columbia.edu/tag/09UI)
* [The Stacks Project, Lemma 36.61.2 (09VC)](https://stacks.math.columbia.edu/tag/09VC)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry.Scheme.Hom

universe u

attribute [local instance] HasDerivedCategory.standard

/-- An object `E` of the derived category of `𝒪_X`-modules is relatively `m`-pseudo-coherent for
`f : X ⟶ S` locally of finite type if there are an affine open cover `V` of `S` and, for each
`V i`, an affine open cover `U` of `f⁻¹(V i)` such that the restriction of `E` to each `U j`
becomes `m`-pseudo-coherent after derived pushforward along some closed immersion
`U j ⟶ 𝔸ⁿ_{V i}` over `V i` through which `f` restricted to `U j` factors. -/
@[stacks 09UI "part (1)"]
public abbrev IsPseudoCoherentFrom {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] (E : DerivedCategory X.Modules) (m : ℤ) : Prop :=
  ∃ (ι : Type u) (V : ι → S.affineOpens),
    (⨆ i, (V i : S.Opens)) = ⊤ ∧
      ∀ i, ∃ (κ : Type u) (U : κ → X.affineOpens),
        (⨆ j, (U j : X.Opens)) = f ⁻¹ᵁ (V i).1 ∧
          ∀ j, ∃ (h : (U j).1 ≤ f ⁻¹ᵁ (V i).1),
            ∃ (n : ℕ)
              (e : (U j).1.toScheme ⟶ AffineSpace (ULift.{u} (Fin n)) (V i).1.toScheme),
              IsClosedImmersion e ∧
                e ≫ (AffineSpace.over (ULift.{u} (Fin n)) (V i).1.toScheme).hom =
                  f.resLE (V i).1 (U j).1 h ∧
                Scheme.Modules.IsPseudoCoherentFromAfterPushforward e
                  ((Scheme.Modules.restrictFunctor (U j).1.ι).mapDerivedCategory.obj E) m

/-- An object of the derived category of `𝒪_X`-modules is relatively pseudo-coherent for `f` if it
is relatively `m`-pseudo-coherent for every integer `m`. -/
@[stacks 09UI "part (2)"]
public abbrev IsPseudoCoherent {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] (E : DerivedCategory X.Modules) : Prop :=
  ∀ m : ℤ, IsPseudoCoherentFrom f E m

/-- A sheaf of `𝒪_X`-modules is relatively `m`-pseudo-coherent for `f` if it is so as an object of
the derived category concentrated in degree zero. -/
@[stacks 09UI "part (3)"]
public abbrev IsModulePseudoCoherentFrom {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] (F : X.Modules) (m : ℤ) : Prop :=
  IsPseudoCoherentFrom f ((DerivedCategory.singleFunctor X.Modules 0).obj F) m

/-- A sheaf of `𝒪_X`-modules is relatively pseudo-coherent for `f` if it is so as an object of the
derived category concentrated in degree zero. -/
@[stacks 09UI "part (4)"]
public abbrev IsModulePseudoCoherent {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] (F : X.Modules) : Prop :=
  IsPseudoCoherent f ((DerivedCategory.singleFunctor X.Modules 0).obj F)

end AlgebraicGeometry.Scheme.Hom

end
