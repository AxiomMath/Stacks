module

public import Mathlib.Algebra.Homology.ShortComplex.Exact
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalModuleBaseChangeEpi
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalModuleCompositionLaw
public import StacksFrontier.AlgebraicGeometry.Spaces.IdealSheafMapVanishing
-- Not `public`: the middle exactness of the conormal complex of a chain of closed subspaces is
-- used only in the proof below, and re-exporting its closure puts the generic abelian structure
-- of sheaves of modules on a site ahead of the one the module categories need in the instance
-- search of every importer.  This is the convention of
-- `StacksFrontier/AlgebraicGeometry/Spaces/SummandSubspaceConormal.lean`, whose implementation notes
-- record what a public import of that closure breaks.
import StacksFrontier.AlgebraicGeometry.Spaces.SummandSubspaceConormal

/-!
# The conormal sequence of a closed subspace inside the inverse image of a closed subspace

Let `g : X ⟶ X''` be a morphism of algebraic spaces over a scheme `S` contained in a big fppf
site `B`, let `Z'' ⊆ X''` be a closed subspace, and let `Z ⊆ X` be a closed subspace which `g`
carries into `Z''`, by a morphism `f : Z ⟶ Z''` making the square of [Stacks Project, Tag 04CP]
commute.  Write `W = g⁻¹(Z'')` for the inverse image, `j : W ⟶ X` for its inclusion and
`p : j⁻¹(Z) ⟶ Z` for the projection.  This file proves that the conormal complex

`p^*(f^*𝒞_{Z''/X''}) ⟶ p^*𝒞_{Z/X} ⟶ 𝒞_{j⁻¹(Z)/W}`

is **exact in the middle**.

The middle exactness of [Stacks Project, Tag 06BD],
`AlgebraicGeometry.Space.exact_conormalShortComplex`, is the same assertion for a *chain of
closed subspaces of one ambient space*: it is the complex above with `f^*𝒞_{Z''/X''}` replaced by
`ι^*𝒞_{W/X}`, where `ι : Z ⟶ W` is the inclusion.  The two complexes have the same right-hand
arrow, and their left-hand arrows differ by precomposition with an epimorphism — the composition
law of part (3) of [Stacks Project, Tag 04G2] factors the conormal map of the outer rectangle
through the conormal map of the lower square, and the remaining factor is the conormal map at an
inverse-image square, which is surjective by the surjectivity clause of [Stacks Project,
Tag 04CQ].  Precomposing the first arrow of a complex with an epimorphism does not change
exactness in the middle, so the exactness transfers.

## Main results

* `CategoryTheory.ShortComplex.exact_mk_of_eq_epi_comp`: a short complex whose first arrow
  factors as an epimorphism followed by the first arrow of an exact short complex, with the same
  second arrow, is itself exact.
* `AlgebraicGeometry.Space.le_preimage_of_subspaceInclusion_square`: the commutative square of
  [Stacks Project, Tag 04CP] puts `Z` inside the inverse image `g⁻¹(Z'')`.
* `AlgebraicGeometry.Space.homMk_homOfLe_comp_preimageProjection_eq`: and makes `f` the inclusion
  of `Z` into that inverse image followed by the projection to `Z''`.
* `AlgebraicGeometry.Space.exists_epi_conormalMap_eq_comp_conormalMap_homOfLe`: **the conormal map
  of the square factors through the conormal map of the chain by an epimorphism.**
* `AlgebraicGeometry.Space.exact_conormalShortComplex_preimage`: **the conormal complex above is
  exact in the middle.**  This is what discharges the exactness in the middle that
  [Stacks Project, Tag 06CC] takes from [Stacks Project, Tag 06BD] for the conormal sequence of a
  composition, where the sequence is read on the fibre product of a pair of universal first-order
  thickenings.

## Implementation notes

**Why the morphism of ambient spaces is a variable and the factorization a hypothesis.**  The
composition law of part (3) of [Stacks Project, Tag 04G2],
`AlgebraicGeometry.Space.conormalMap_comp`, reads the conormal map of the outer rectangle at the
composites `𝟙 X ≫ g` and `ι ≫ p'` of the two edges of the two squares, and a consumer has the
map `g` and the morphism `f` themselves.  Crossing between the two spellings inside the argument
of `AlgebraicGeometry.Space.conormalMap` is a dependent rewrite — the commutativity proof of the
square is an argument too — so the two composites are taken as variables with their defining
equations as hypotheses and substituted, which replaces the rewrite by a substitution.  The
commutativity proofs then agree by proof irrelevance.

**Why the vanishing of the composite is a hypothesis.**  `CategoryTheory.ShortComplex.mk` takes
it as an argument, and a consumer arrives with a proof of its own; since it is a proof of an
equation, any two are definitionally equal and the statement below instantiates at the
consumer's complex verbatim.  Nothing about the conclusion depends on which proof is supplied.

**Why the inverse image, its inclusion and the two arrows are variables too.**  A consumer of
the exactness has its own names for all four — the inverse image of a closed subspace along a
morphism of ambient spaces is a fibre product in its situation, and the two arrows carry names
of their own — and each of its names is only *definitionally* the spelling this file would
produce.  Crossing a single one of those spellings is cheap, and `AlgebraicGeometry.Space.Modules`
is where crossing *two at once inside a composition* is not: comparing two
`CategoryTheory.CategoryStruct.comp` applications whose arrows have two spellings each sends the
unifier through the composition law of the category of sheaves of modules, which the heartbeat
budget does not survive.  This is the hazard the implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/ConormalModuleBaseChangeEpi.lean` record for the defining
equation of the conormal map, and it bites here at exactly the same place.  Taking the four as
variables with their defining equations as hypotheses, and substituting, moves every crossing
*outside* the composition: the consumer supplies its own terms for the arrows, so the short
complex in the conclusion is literally its own, and each hypothesis is an equation of single
arrows that its own structural lemmas discharge.  Making
`AlgebraicGeometry.Space.modulePullback` irreducible does not help on its own — the kernel does
not honour the attribute, so a proof that elaborates then fails to be checked.

**The inverse image of the chain is spelled as the consumer's.**  The closed subspace of `X`
playing the part of the upper subspace in the chain is written
`AlgebraicGeometry.Space.preimageSubspace` of `g` at `Z''` throughout the proof, so the inverse
image functor along the projection has one spelling there and the crossing of
`AlgebraicGeometry.Space.exact_conormalShortComplex_mk` is reached with nothing to respell.

## References

* [Stacks Project, Tag 06BD](https://stacks.math.columbia.edu/tag/06BD)
* [Stacks Project, Tag 04CP](https://stacks.math.columbia.edu/tag/04CP)
* [Stacks Project, Tag 04CQ](https://stacks.math.columbia.edu/tag/04CQ)
* [Stacks Project, Tag 04G2](https://stacks.math.columbia.edu/tag/04G2)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace CategoryTheory.ShortComplex

/-- **Exactness in the middle survives precomposing the first arrow with an epimorphism.**  Let
`f' = e ≫ f` with `e` an epimorphism, and let the short complex formed by `f` and `g` be exact.
Then the short complex formed by `f'` and `g` is exact.

The two complexes are compared by the morphism which is `e` at the first term and the identity at
the other two, and `CategoryTheory.ShortComplex.exact_iff_of_epi_of_isIso_of_mono` transports
exactness along such a morphism. -/
theorem exact_mk_of_eq_epi_comp {C : Type*} [Category C] [HasZeroMorphisms C]
    {A A' M N : C} {f' : A' ⟶ M} {f : A ⟶ M} {g : M ⟶ N} (e : A' ⟶ A) (hepi : Epi e)
    (hf : f' = e ≫ f) (w' : f' ≫ g = 0) (w : f ≫ g = 0)
    (hex : (ShortComplex.mk f g w).Exact) :
    (ShortComplex.mk f' g w').Exact := by
  let φ : ShortComplex.mk f' g w' ⟶ ShortComplex.mk f g w :=
    { τ₁ := e, τ₂ := 𝟙 M, τ₃ := 𝟙 N
      comm₁₂ := by simp [hf]
      comm₂₃ := by simp }
  have : Epi φ.τ₁ := hepi
  have : IsIso φ.τ₂ := inferInstanceAs (IsIso (𝟙 M))
  have : Mono φ.τ₃ := inferInstanceAs (Mono (𝟙 N))
  exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).mpr hex

end CategoryTheory.ShortComplex

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X X'' : AlgebraicSpaces B S hS} (g : X ⟶ X'')
    (Z'' : ClosedSubspaces B S hS X''.1) (Z : ClosedSubspaces B S hS X.1)

/-! ### The square puts the subspace inside the inverse image -/

/-- The square of closed subspaces, read on the underlying morphisms of functors. -/
private theorem hom_ι_comp_eq_of_subspaceInclusion_square
    (f : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) ⟶
      (⟨Z''.1.toFunctor, Z''.2.1⟩ : AlgebraicSpaces B S hS))
    (hsq : subspaceInclusion B S hS X Z ≫ g = f ≫ subspaceInclusion B S hS X'' Z'') :
    Z.1.ι ≫ g.hom = f.hom ≫ Z''.1.ι :=
  congrArg (fun k : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) ⟶ X'' => k.hom) hsq

/-- **A commutative square of closed subspaces puts the upstairs subspace inside the inverse
image of the downstairs one.**  If the inclusion of `Z ⊆ X` followed by `g : X ⟶ X''` is a
morphism `f : Z ⟶ Z''` followed by the inclusion of `Z'' ⊆ X''`, then `Z ⊆ g⁻¹(Z'')`.

The image of `Z` under `g` is the range of the composite `Z ⟶ X ⟶ X''`, which the square
rewrites as the range of `Z ⟶ Z'' ⟶ X''`; that is contained in the range of the inclusion of
`Z''`, which is `Z''`. -/
theorem le_preimage_of_subspaceInclusion_square
    (f : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) ⟶
      (⟨Z''.1.toFunctor, Z''.2.1⟩ : AlgebraicSpaces B S hS))
    (hsq : subspaceInclusion B S hS X Z ≫ g = f ≫ subspaceInclusion B S hS X'' Z'') :
    Z.1 ≤ (preimageSubspace B S hS g Z'').1 := by
  have h := hom_ι_comp_eq_of_subspaceInclusion_square B S hS g Z'' Z f hsq
  change Z.1 ≤ Z''.1.preimage g.hom
  rw [← Subfunctor.image_le_iff]
  calc Z.1.image g.hom
      = Subfunctor.range (Z.1.ι ≫ g.hom) := by
        rw [Subfunctor.range_comp, Subfunctor.range_ι]
    _ = Subfunctor.range (f.hom ≫ Z''.1.ι) := by rw [h]
    _ ≤ Subfunctor.range Z''.1.ι := Subfunctor.range_comp_le _ _
    _ = Z''.1 := Subfunctor.range_ι _

/-- **The vertical morphism of the square is the inclusion into the inverse image followed by the
projection.**  With `Z ⊆ g⁻¹(Z'')` as above, the morphism `f : Z ⟶ Z''` of the square is the
inclusion of `Z` into `g⁻¹(Z'')` followed by the projection `g⁻¹(Z'') ⟶ Z''`.

Both sides followed by the inclusion of `Z''` are the inclusion of `Z` followed by `g`, by
`CategoryTheory.Subfunctor.fromPreimage_ι` and `CategoryTheory.Subfunctor.homOfLe_ι` on one side
and by the square on the other, and the inclusion of a subfunctor is a monomorphism. -/
theorem homMk_homOfLe_comp_preimageProjection_eq
    (f : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) ⟶
      (⟨Z''.1.toFunctor, Z''.2.1⟩ : AlgebraicSpaces B S hS))
    (hsq : subspaceInclusion B S hS X Z ≫ g = f ≫ subspaceInclusion B S hS X'' Z'')
    (hle : Z.1 ≤ (preimageSubspace B S hS g Z'').1) :
    (ObjectProperty.homMk (Subfunctor.homOfLe hle) :
          (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) ⟶
            (⟨(preimageSubspace B S hS g Z'').1.toFunctor,
              (preimageSubspace B S hS g Z'').2.1⟩ : AlgebraicSpaces B S hS)) ≫
        preimageProjection B S hS g Z'' = f := by
  have h := hom_ι_comp_eq_of_subspaceInclusion_square B S hS g Z'' Z f hsq
  refine ObjectProperty.hom_ext _ ?_
  change Subfunctor.homOfLe hle ≫ Z''.1.fromPreimage g.hom = f.hom
  rw [← cancel_mono Z''.1.ι, Category.assoc, Subfunctor.fromPreimage_ι, ← Category.assoc,
    Subfunctor.homOfLe_ι, h]

/-! ### The conormal map of the square factors through the conormal map of the chain -/

/-- The composition law of part (3) of [Stacks Project, Tag 04G2] for the outer rectangle formed
by the square of `Z ⊆ X` over `g` and the inverse-image square of `g⁻¹(Z'') ⊆ X`, with the two
composite edges of the rectangle taken as variables carrying their defining equations.  The
implementation notes of this file say why they are variables. -/
private theorem exists_epi_conormalMap_eq_comp_aux
    (hle : Z.1 ≤ (preimageSubspace B S hS g Z'').1)
    (f : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) ⟶
      (⟨Z''.1.toFunctor, Z''.2.1⟩ : AlgebraicSpaces B S hS))
    (hf : (ObjectProperty.homMk (Subfunctor.homOfLe hle) :
          (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) ⟶
            (⟨(preimageSubspace B S hS g Z'').1.toFunctor,
              (preimageSubspace B S hS g Z'').2.1⟩ : AlgebraicSpaces B S hS)) ≫
        preimageProjection B S hS g Z'' = f)
    (gg : X ⟶ X'') (hg : (𝟙 X : X ⟶ X) ≫ g = gg)
    (hsq : subspaceInclusion B S hS X Z ≫ gg = f ≫ subspaceInclusion B S hS X'' Z'') :
    ∃ e, Epi e ∧ conormalMap B S hS Z Z'' gg f hsq =
      e ≫ conormalMap B S hS Z (preimageSubspace B S hS g Z'') (𝟙 X)
        (ObjectProperty.homMk (Subfunctor.homOfLe hle))
        (subspaceInclusion_homOfLe_square B S hS (preimageSubspace B S hS g Z'') Z hle) := by
  subst hf hg
  have hepi : Epi (conormalMap B S hS (preimageSubspace B S hS g Z'') Z'' g
      (preimageProjection B S hS g Z'') (conormalEtaleRestrictionSquare B S hS g Z'')) :=
    epi_conormalMap B S hS g Z''
  have hpres : (modulePullback B S hS
      (ObjectProperty.homMk (Subfunctor.homOfLe hle) :
        (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) ⟶
          (⟨(preimageSubspace B S hS g Z'').1.toFunctor,
            (preimageSubspace B S hS g Z'').2.1⟩ :
            AlgebraicSpaces B S hS))).PreservesEpimorphisms :=
    Functor.preservesEpimorphisms_of_adjunction (modulePullbackAdjunction B S hS _)
  refine ⟨_, ?_, (conormalMap_comp B S hS (𝟙 X) g Z (preimageSubspace B S hS g Z'') Z''
    (ObjectProperty.homMk (Subfunctor.homOfLe hle)) (preimageProjection B S hS g Z'')
    (subspaceInclusion_homOfLe_square B S hS (preimageSubspace B S hS g Z'') Z hle)
    (conormalEtaleRestrictionSquare B S hS g Z'') hsq).trans (Category.assoc _ _ _).symm⟩
  infer_instance

/-- **The conormal map of the square factors through the conormal map of the chain by an
epimorphism.**  Let `f : Z ⟶ Z''` make the square of [Stacks Project, Tag 04CP] over `g` commute
and let `W = g⁻¹(Z'')`.  The map `f^*𝒞_{Z''/X''} ⟶ 𝒞_{Z/X}` of that tag is an epimorphism
followed by the map `ι^*𝒞_{W/X} ⟶ 𝒞_{Z/X}` attached to the chain `Z ⊆ W ⊆ X`.

By the composition law of part (3) of [Stacks Project, Tag 04G2] the map of the outer rectangle
is the inverse image along `ι` of the map of the upper square, read through the composition
comparison of [Stacks Project, Tag 03LU], followed by the map of the lower square — which is the
map of the chain.  The upper square is the inverse-image square of `g` at `Z''`, so its map is an
epimorphism by the surjectivity clause of [Stacks Project, Tag 04CQ]; the inverse image of
modules is a left adjoint, so it carries that epimorphism to an epimorphism, and the comparison
is an isomorphism. -/
theorem exists_epi_conormalMap_eq_comp_conormalMap_homOfLe
    (f : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) ⟶
      (⟨Z''.1.toFunctor, Z''.2.1⟩ : AlgebraicSpaces B S hS))
    (hsq : subspaceInclusion B S hS X Z ≫ g = f ≫ subspaceInclusion B S hS X'' Z'')
    (hle : Z.1 ≤ (preimageSubspace B S hS g Z'').1) :
    ∃ e, Epi e ∧ conormalMap B S hS Z Z'' g f hsq =
      e ≫ conormalMap B S hS Z (preimageSubspace B S hS g Z'') (𝟙 X)
        (ObjectProperty.homMk (Subfunctor.homOfLe hle))
        (subspaceInclusion_homOfLe_square B S hS (preimageSubspace B S hS g Z'') Z hle) :=
  exists_epi_conormalMap_eq_comp_aux B S hS g Z'' Z hle f
    (homMk_homOfLe_comp_preimageProjection_eq B S hS g Z'' Z f hsq hle) g (Category.id_comp g) hsq

/-! ### Exactness in the middle -/

/-- **Exactness in the middle of the conormal complex of a closed subspace inside the inverse
image of a closed subspace.**  Let `g : X ⟶ X''` be a morphism of algebraic spaces, let
`Z'' ⊆ X''` and `Z ⊆ X` be closed subspaces and let `f : Z ⟶ Z''` make the square of
[Stacks Project, Tag 04CP] commute.  Let `W ⊆ X` be the inverse image `g⁻¹(Z'')`, let
`j : W ⟶ X` be its inclusion and let `p : j⁻¹(Z) ⟶ Z` be the projection.  Then the conormal
complex

`p^*(f^*𝒞_{Z''/X''}) ⟶ p^*𝒞_{Z/X} ⟶ 𝒞_{j⁻¹(Z)/W}`

is exact in the middle: its first arrow is `p^*` of the map of [Stacks Project, Tag 04CP] at the
square, and its second is the map of that tag at the inverse-image square of `j` at `Z`.

This is the middle clause of [Stacks Project, Tag 06BD] in the presentation a composition of
morphisms produces, where the two conormal modules on the left live over *different* ambient
spaces.  The middle exactness of that tag,
`AlgebraicGeometry.Space.exact_conormalShortComplex`, is stated for a chain of closed subspaces
of one ambient space, and is reached here through
`AlgebraicGeometry.Space.exact_conormalShortComplex_mk`: the two complexes have the same
right-hand arrow, and the left-hand arrow of this one is the inverse image along `p` of an
epimorphism followed by the left-hand arrow of that one, by
`AlgebraicGeometry.Space.exists_epi_conormalMap_eq_comp_conormalMap_homOfLe`.  Precomposing with
an epimorphism does not change exactness in the middle,
`CategoryTheory.ShortComplex.exact_mk_of_eq_epi_comp`.

The inverse image, its inclusion and the two arrows are variables carrying their defining
equations, and the vanishing of the composite is a hypothesis; the implementation notes of this
file say why. -/
theorem exact_conormalShortComplex_preimage
    (f : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) ⟶
      (⟨Z''.1.toFunctor, Z''.2.1⟩ : AlgebraicSpaces B S hS))
    (hsq : subspaceInclusion B S hS X Z ≫ g = f ≫ subspaceInclusion B S hS X'' Z'')
    (W : ClosedSubspaces B S hS X.1) (hW : W = preimageSubspace B S hS g Z'')
    (J : (⟨W.1.toFunctor, W.2.1⟩ : AlgebraicSpaces B S hS) ⟶ X)
    (hJ : J = subspaceInclusion B S hS X W)
    (C : (modulePullback B S hS f).obj (conormalModule B S hS X'' Z'') ⟶
      conormalModule B S hS X Z)
    (hC : C = conormalMap B S hS Z Z'' g f hsq)
    (L : (modulePullback B S hS (preimageProjection B S hS J Z)).obj
          ((modulePullback B S hS f).obj (conormalModule B S hS X'' Z'')) ⟶
        (modulePullback B S hS (preimageProjection B S hS J Z)).obj
          (conormalModule B S hS X Z))
    (hL : L = (modulePullback B S hS (preimageProjection B S hS J Z)).map C)
    (R : (modulePullback B S hS (preimageProjection B S hS J Z)).obj
          (conormalModule B S hS X Z) ⟶
        conormalModule B S hS (⟨W.1.toFunctor, W.2.1⟩ : AlgebraicSpaces B S hS)
          (preimageSubspace B S hS J Z))
    (hR : R = conormalMap B S hS (preimageSubspace B S hS J Z) Z J
      (preimageProjection B S hS J Z) (conormalEtaleRestrictionSquare B S hS J Z))
    (w : L ≫ R = 0) :
    (ShortComplex.mk L R w).Exact := by
  subst hL hC hR hJ hW
  have hle : Z.1 ≤ (preimageSubspace B S hS g Z'').1 :=
    le_preimage_of_subspaceInclusion_square B S hS g Z'' Z f hsq
  obtain ⟨e, he, hfac⟩ :=
    exists_epi_conormalMap_eq_comp_conormalMap_homOfLe B S hS g Z'' Z f hsq hle
  have hpres : (modulePullback B S hS
      (preimageProjection B S hS
        (subspaceInclusion B S hS X (preimageSubspace B S hS g Z'')) Z)).PreservesEpimorphisms :=
    Functor.preservesEpimorphisms_of_adjunction (modulePullbackAdjunction B S hS _)
  refine CategoryTheory.ShortComplex.exact_mk_of_eq_epi_comp
    ((modulePullback B S hS
      (preimageProjection B S hS
        (subspaceInclusion B S hS X (preimageSubspace B S hS g Z'')) Z)).map e)
    inferInstance ?_ w
    (conormalMap_comp_conormalMap_eq_zero B S hS (preimageSubspace B S hS g Z'') Z hle)
    (exact_conormalShortComplex_mk B S hS (preimageSubspace B S hS g Z'') Z hle)
  rw [hfac, Functor.map_comp]

end AlgebraicGeometry.Space

end
