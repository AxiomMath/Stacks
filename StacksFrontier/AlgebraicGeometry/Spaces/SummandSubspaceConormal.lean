module

public import Mathlib.Algebra.Homology.ShortComplex.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.Exact
public import Mathlib.Algebra.Homology.ShortComplex.Preadditive
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalModuleBaseChangeEpi
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.QuasicoherentAbelian
public import StacksFrontier.AlgebraicGeometry.Spaces.IdealSheafMapIdentity
-- Not `public`: the exactness clause is used only in the proofs below, and re-exporting its
-- closure puts the generic abelian structure of sheaves of modules on a site ahead of the one the
-- module categories need in the instance search of every importer.  See the implementation notes.
import StacksFrontier.AlgebraicGeometry.Spaces.IdealSheafSequenceExact

/-!
# The conormal module of the subspace cut out by a summand of a conormal module

Let `X` be an algebraic space over a scheme `S` contained in a big fppf site `B` and let
`Z ⊆ Y ⊆ X` be closed subspaces.
`StacksFrontier/AlgebraicGeometry/Spaces/IdealSheafMapVanishing.lean` builds the conormal complex of
that chain,

`p^*(ι^*𝒞_{Y/X}) --L--> p^*𝒞_{Z/X} --R--> 𝒞_{j⁻¹(Z)/Y}`,

`j : Y ⟶ X` and `ι : Z ⟶ Y` the inclusions and `p : j⁻¹(Z) ⟶ Z` the projection, and shows that
it is a complex; `StacksFrontier/AlgebraicGeometry/Spaces/ConormalModuleBaseChangeEpi.lean` shows
that `R` is an epimorphism, and
`StacksFrontier/AlgebraicGeometry/Spaces/IdealSheafSequenceExact.lean` shows that it is exact in the
middle, so all three clauses of [Stacks Project, Tag 06BD] are available here.  This file
identifies a *complementary summand* of the left-hand map inside `𝒞_{Z/X}` with the conormal
module `𝒞_{Z/Y}` of the new pair.

That identification is the second half of the paragraph of [Stacks Project, Tag 06D8] which reads

> Let `Z' ⊂ Z''` be the closed subscheme cut out by `𝒞_{Z/X} ⊂ 𝓘` […].  Note that by construction
> `𝒞_{Z/Z'} = i^*𝒞_{X/X'}`

at the level of algebraic spaces.  There `Z ⊂ Z''` is the universal first order thickening of `Z`
over `X'`, `𝓘` its defining ideal sheaf, and `𝓘 = i^*𝒞_{X/X'} ⊕ 𝒞_{Z/X}` the chosen splitting; the
subspace `Z'` is the one
`AlgebraicGeometry.Space.exists_isFirstOrderThickening_definingIdealSheaf_eq_of_le` of
`StacksFrontier/AlgebraicGeometry/Spaces/SummandSubspaceFirstOrderThickening.lean` produces, so the
chain `Z ⊆ Z' ⊆ Z''` is exactly the configuration below.

## Main results

* `CategoryTheory.ShortComplex.epi_comp_of_splitting_data`: in a preadditive category, let
  `A --α--> M --γ--> D` carry a splitting and let `R : M ⟶ Q` be an epimorphism which kills the
  section `s : D ⟶ M` up to an isomorphism of its source.  Then `α ≫ R` is an epimorphism.
* `CategoryTheory.ShortComplex.isIso_comp_of_splitting_data`: in an abelian category the same
  composite is an *isomorphism* as soon as the pair `(l, R)` — `l` the morphism the section is
  identified with — is exact in the middle.
* `CategoryTheory.ShortComplex.epi_map_comp_of_splitting_data` and
  `CategoryTheory.ShortComplex.isIso_map_comp_of_splitting_data`: the two lemmas with the
  splitting given upstream of an additive functor and the epimorphism downstream of it, which is
  the shape the conormal complex presents.
* `AlgebraicGeometry.Space.epi_modulePullback_comp_conormalMap_of_splitting`: **the surjectivity
  half of the identification**, for a splitting whose section is identified with the left-hand
  map of the conormal complex by a given isomorphism.  The two remaining inputs are proved and
  unconditional: `AlgebraicGeometry.Space.epi_conormalMap_closedSubspaces`, the exactness at the
  right term of [Stacks Project, Tag 06BD], and
  `AlgebraicGeometry.Space.conormalMap_comp_conormalMap_eq_zero`, its vanishing clause.
* `AlgebraicGeometry.Space.exact_conormalShortComplex_mk`: exactness in the middle of the conormal
  complex of the chain, the middle clause of [Stacks Project, Tag 06BD], restated at the spelling
  of the inverse image along `AlgebraicGeometry.Space.preimageProjection` that the two statements
  below present.
* `AlgebraicGeometry.Space.isIso_modulePullback_comp_conormalMap_of_splitting`: **the
  identification**, `𝒞_{Z/Y} ≅` the complementary summand, with nothing assumed beyond the
  splitting and that identification of the section: exactness in the middle is
  `AlgebraicGeometry.Space.exact_conormalShortComplex`.
* `AlgebraicGeometry.Space.epi_modulePullback_comp_conormalMap_of_definingIdealSheafSplitting`:
  the same surjectivity **with nothing assumed beyond the splitting**, for the splitting the
  source chooses — the one whose section is the inverse image along `i : Z ⟶ X` of the inclusion
  `𝓘_Y ⊆ 𝓘_Z` of defining ideal sheaves.  The isomorphism the previous statement takes as a
  parameter is `AlgebraicGeometry.Space.exists_iso_comp_eq_conormalMap_homOfLe` of
  `StacksFrontier/AlgebraicGeometry/Spaces/IdealSheafMapIdentity.lean`.
* `AlgebraicGeometry.Space.isIso_modulePullback_comp_conormalMap_of_definingIdealSheafSplitting`:
  **the identification at the configuration of [Stacks Project, Tag 06D8]**, whose only hypothesis
  is the splitting.

## Implementation notes

**Where `𝒞_{Z/Y}` lives.**  The right-hand map of the conormal complex is the one of
[Stacks Project, Tag 04CP] at the inverse-image square, so `𝒞_{Z/Y}` is read as the conormal
module of the inverse image `j⁻¹(Z)` of [Stacks Project, Tag 083Q] along the inclusion
`j : Y ⟶ X`, the map starts at the inverse image `p^*𝒞_{Z/X}` along the projection
`p : j⁻¹(Z) ⟶ Z`, and the summand is carried there by `p^*` as well.  That is the spelling the
epimorphy `AlgebraicGeometry.Space.epi_conormalMap_closedSubspaces` and the
vanishing `AlgebraicGeometry.Space.conormalMap_comp_conormalMap_eq_zero` are stated in.  The
splitting itself is taken on `Z`, where the source states it, and transported:
`AlgebraicGeometry.Space.modulePullback_additive` makes `p^*` additive, so the decomposition of
the identity is carried along with the two one-sided inverses.

A closed subspace of `Y` is also attached to `Z` by another route:
`AlgebraicGeometry.Space.isClosedSubspace_of_le`, [Stacks Project, Tag 02YX], makes the range of
`CategoryTheory.Subfunctor.homOfLe` a closed subspace of `Y` outright.  Nothing here is stated at
that spelling, because the epimorphy and the vanishing of the complex are not; identifying the two
subspaces of `Y` would be the first step of a restatement at it.

**Why the comparison of the section with the left-hand map is a parameter of the general
statements.**  Inlining it times out: writing the isomorphism into the statement forces the
definitional unifier through the inverse-image functor of the small étale ringed site.  The
comparison is therefore a parameter with its equation a hypothesis, and discharged at the
configuration that matters by `AlgebraicGeometry.Space.exists_iso_comp_eq_conormalMap_homOfLe`,
which exhibits the left-hand map of the conormal complex as the inverse image of the inclusion of
defining ideal sheaves.  The scheme-level analogue of that discharge is
`Stacks.Thickenings.exists_iso_comp_eq_conormalLeftMap` of
`StacksFrontier/AlgebraicGeometry/Thickenings/SummandSubschemeConormal.lean`, which goes through
pushforwards and the full faithfulness of [Stacks Project, Tag 08KS]; the space-level route taken
here is shorter, because `AlgebraicGeometry.Space.conormalMap` is *defined* as an inverse image of
`AlgebraicGeometry.Space.idealSheafMap` after an isomorphism, so no pushforward is needed.

**Why the category-theoretic content is separated out.**  The argument that a complementary summand
of the left-hand map of an exact pair maps isomorphically to the quotient is formal: it uses only
the splitting identities, the epimorphy of `R` and exactness in the middle.  Stated in a
preadditive, respectively abelian, category it elaborates in no time; stated at the concrete
modules it would have to be elaborated against the inverse-image functor at every step.  The
abstract lemmas take the splitting as four morphism identities rather than as a
`CategoryTheory.ShortComplex.Splitting`, so that the transported data can be handed to them
without building a transported splitting object.

**The additivity instance is supplied by hand.**  `AlgebraicGeometry.Space.modulePullback_additive`
is an instance, but it is not found by instance resolution at the concrete inverse image along
`AlgebraicGeometry.Space.preimageProjection`; the two proofs below introduce it by hand.

**Why exactness in the middle is restated.**  `AlgebraicGeometry.Space.modulePullback` carries the
source and target of its morphism as implicit arguments, and the projection of the fibre-product
square has two definitionally equal spellings of them: the one the two closed subspaces give, which
is the one `AlgebraicGeometry.Space.exact_conormalShortComplex` is stated at, and the
one the type of `AlgebraicGeometry.Space.preimageProjection` declares, which is the one the
composite below presents, because `AlgebraicGeometry.Space.conormalMap` names its own source that
way.  Inside `CategoryTheory.Functor.map` the unifier crosses between the two by unfolding the
inverse image, which does not finish.  `AlgebraicGeometry.Space.exact_conormalShortComplex_mk`
therefore does the crossing once, in a section where `AlgebraicGeometry.Space.modulePullback` is
`local irreducible`, so that the two functors are matched argument by argument instead; that
respelling is then handed to the abstract lemma verbatim.
`StacksFrontier/AlgebraicGeometry/Spaces/IdealSheafMapVanishing.lean` uses the same device, and
`StacksFrontier/AlgebraicGeometry/Spaces/IdealSheafSequenceExact.lean` records the same obstruction
on `AlgebraicGeometry.Space.conormalMap_comp_conormalMap_eq_zero_chain`.

**The abelian structure is given a raised priority, and the exactness clause is imported without
`public`.**  With the closure of
`StacksFrontier/AlgebraicGeometry/Spaces/IdealSheafSequenceExact.lean` in scope, instance search for
the abelian structure of the module categories meets the generic form of
`SheafOfModules.instAbelian` on a site first, whose module universe is a join that is never the
universe of the schemes, and ends in an unsolvable universe constraint rather than in a recoverable
failure.  Raising the priority of that instance locally is the device of
`StacksFrontier/AlgebraicGeometry/Spaces/ClosedImmersionModulePushforwardRightExact.lean`.  The
exactness clause is used only in the proofs here, so its import is not `public` and importers of
this file do not inherit the search order it imposes.

## What is not proved

* **No `@[stacks]` attribute is placed.**  These statements are not any tag of the source: they are
  the space-level replacement for a sentence inside the proof of [Stacks Project, Tag 06D8], and
  that tag needs much more than this — in particular the space-level form of [Stacks Project,
  Tag 06CC], which is a separate gap.

## References

* [Stacks Project, Tag 06D8](https://stacks.math.columbia.edu/tag/06D8)
* [Stacks Project, Tag 06BD](https://stacks.math.columbia.edu/tag/06BD)
* [Stacks Project, Tag 04CP](https://stacks.math.columbia.edu/tag/04CP)
* [Stacks Project, Tag 04CQ](https://stacks.math.columbia.edu/tag/04CQ)
* [Stacks Project, Tag 083Q](https://stacks.math.columbia.edu/tag/083Q)
* [Stacks Project, Tag 02YX](https://stacks.math.columbia.edu/tag/02YX)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace CategoryTheory.ShortComplex

/-! ### The formal content: a complementary summand of an exact pair -/

section Preadditive

variable {𝒜 : Type u} [Category.{v} 𝒜] [Preadditive 𝒜] {A M D L Q : 𝒜}

/-- **A complementary summand surjects onto the quotient.**  Let `A --α--> M --γ--> D` be a split
short complex, presented by its section `s : D ⟶ M`, its retraction `r : M ⟶ A` and the resulting
decomposition `r ≫ α + γ ≫ s = 𝟙 M` of the identity.  Let `R : M ⟶ Q` be an epimorphism, let
`l : L ⟶ M` be a morphism with `l ≫ R = 0`, and suppose `s` is `l` up to an isomorphism `φ` of its
source.  Then `α ≫ R` is an epimorphism.

Composing the decomposition of the identity with `R` on the right kills the second term, because
`s ≫ R = φ⁻¹ ≫ l ≫ R = 0`, and leaves `r ≫ (α ≫ R) = R`.  An epimorphism factoring through
`α ≫ R` makes it one. -/
theorem epi_comp_of_splitting_data (α : A ⟶ M) (γ : M ⟶ D) (r : M ⟶ A) (s : D ⟶ M)
    (hid : r ≫ α + γ ≫ s = 𝟙 M) (R : M ⟶ Q) (hR : Epi R)
    (l : L ⟶ M) (hl : l ≫ R = 0) (φ : L ≅ D) (hφ : φ.hom ≫ s = l) :
    Epi (α ≫ R) := by
  have hsR : s ≫ R = 0 := by
    rw [← Iso.inv_hom_id_assoc φ s, hφ, Category.assoc, hl, comp_zero]
  have hfac : r ≫ α ≫ R = R := by
    have h : (r ≫ α + γ ≫ s) ≫ R = R := by rw [hid, Category.id_comp]
    rwa [Preadditive.add_comp, Category.assoc, Category.assoc, hsR, comp_zero, add_zero] at h
  have : Epi (r ≫ α ≫ R) := by rwa [hfac]
  exact epi_of_epi r (α ≫ R)

end Preadditive

section Abelian

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜] {A M D L Q : 𝒜}

/-- **A complementary summand of an exact pair maps isomorphically to the quotient.**  In the
situation of `CategoryTheory.ShortComplex.epi_comp_of_splitting_data`, if moreover the pair
`L --l--> M --R--> Q` is exact in the middle, then `α ≫ R` is an isomorphism.

Surjectivity is `CategoryTheory.ShortComplex.epi_comp_of_splitting_data`.  For injectivity, a
morphism `u` with `u ≫ α ≫ R = 0` has `u ≫ α` factoring as `v ≫ l` by exactness — `l` is a
monomorphism, being the isomorphism `φ` followed by the split monomorphism `s` — and `l ≫ r` is
zero because `s ≫ r` is, so `u = u ≫ α ≫ r = v ≫ l ≫ r = 0`.  An abelian category is balanced,
so the two together give invertibility. -/
theorem isIso_comp_of_splitting_data (α : A ⟶ M) (γ : M ⟶ D) (r : M ⟶ A) (s : D ⟶ M)
    (hαr : α ≫ r = 𝟙 A) (hsγ : s ≫ γ = 𝟙 D) (hsr : s ≫ r = 0)
    (hid : r ≫ α + γ ≫ s = 𝟙 M) (R : M ⟶ Q) (hR : Epi R)
    (l : L ⟶ M) (hl : l ≫ R = 0) (hex : (ShortComplex.mk l R hl).Exact)
    (φ : L ≅ D) (hφ : φ.hom ≫ s = l) :
    IsIso (α ≫ R) := by
  have : Epi (α ≫ R) := epi_comp_of_splitting_data α γ r s hid R hR l hl φ hφ
  have hlr : l ≫ r = 0 := by rw [← hφ, Category.assoc, hsr, comp_zero]
  have : Mono (α ≫ R) := by
    have : IsSplitMono s := ⟨⟨⟨γ, hsγ⟩⟩⟩
    have hml : Mono l := by rw [← hφ]; exact mono_comp _ _
    have : Mono (ShortComplex.mk l R hl).f := hml
    rw [Preadditive.mono_iff_cancel_zero]
    intro T u hu
    obtain ⟨w, hw⟩ := hex.lift' (u ≫ α) ((Category.assoc u α R).trans hu)
    have hw' : w ≫ l = u ≫ α := hw
    rw [← Category.comp_id u, ← hαr, ← Category.assoc, ← hw', Category.assoc, hlr, comp_zero]
  exact isIso_of_mono_of_epi _

end Abelian

section Transport

variable {C : Type*} [Category C] [Preadditive C] {A M D L : C}

/-- An additive functor carries a decomposition `r ≫ α + γ ≫ s = 𝟙 M` of the identity to one. -/
private theorem map_decomposition_id {𝒜 : Type*} [Category 𝒜] [Preadditive 𝒜] (F : C ⥤ 𝒜)
    [F.Additive] {α : A ⟶ M} {γ : M ⟶ D} {r : M ⟶ A} {s : D ⟶ M}
    (hid : r ≫ α + γ ≫ s = 𝟙 M) :
    F.map r ≫ F.map α + F.map γ ≫ F.map s = 𝟙 (F.obj M) := by
  rw [← F.map_comp, ← F.map_comp, ← F.map_add, hid, F.map_id]

/-- **A complementary summand surjects onto the quotient, after an additive functor.**  The
transport of `CategoryTheory.ShortComplex.epi_comp_of_splitting_data` along an additive functor
`F`: the splitting and the isomorphism identifying its section with `l` are given upstream, and
only the epimorphism `R` out of `F.obj M` is given downstream.

An additive functor carries the decomposition of the identity to a decomposition of the identity
and the two composites to composites, so nothing but the functor laws is used. -/
theorem epi_map_comp_of_splitting_data {𝒜 : Type*} [Category 𝒜] [Preadditive 𝒜] (F : C ⥤ 𝒜)
    [F.Additive] {Q : 𝒜} (α : A ⟶ M) (γ : M ⟶ D) (r : M ⟶ A) (s : D ⟶ M)
    (hid : r ≫ α + γ ≫ s = 𝟙 M) (R : F.obj M ⟶ Q) (hR : Epi R)
    (l : L ⟶ M) (hl : F.map l ≫ R = 0) (φ : L ≅ D) (hφ : φ.hom ≫ s = l) :
    Epi (F.map α ≫ R) :=
  epi_comp_of_splitting_data (F.map α) (F.map γ) (F.map r) (F.map s)
    (map_decomposition_id F hid) R hR (F.map l) hl
    (F.mapIso φ) (by rw [Functor.mapIso_hom, ← F.map_comp, hφ])

/-- **A complementary summand of an exact pair maps isomorphically to the quotient, after an
additive functor.**  The transport of
`CategoryTheory.ShortComplex.isIso_comp_of_splitting_data` along an additive functor, in the same
shape as `CategoryTheory.ShortComplex.epi_map_comp_of_splitting_data`: exactness is asked of the
pair downstream, which is where it is available, and the splitting upstream. -/
theorem isIso_map_comp_of_splitting_data {𝒜 : Type*} [Category 𝒜] [Abelian 𝒜] (F : C ⥤ 𝒜)
    [F.Additive] {Q : 𝒜} (α : A ⟶ M) (γ : M ⟶ D) (r : M ⟶ A) (s : D ⟶ M)
    (hαr : α ≫ r = 𝟙 A) (hsγ : s ≫ γ = 𝟙 D) (hsr : s ≫ r = 0)
    (hid : r ≫ α + γ ≫ s = 𝟙 M) (R : F.obj M ⟶ Q) (hR : Epi R)
    (l : L ⟶ M) (hl : F.map l ≫ R = 0) (hex : (ShortComplex.mk (F.map l) R hl).Exact)
    (φ : L ≅ D) (hφ : φ.hom ≫ s = l) :
    IsIso (F.map α ≫ R) :=
  isIso_comp_of_splitting_data (F.map α) (F.map γ) (F.map r) (F.map s)
    (by rw [← F.map_comp, hαr, F.map_id]) (by rw [← F.map_comp, hsγ, F.map_id])
    (by rw [← F.map_comp, hsr, F.map_zero])
    (map_decomposition_id F hid) R hR (F.map l) hl hex
    (F.mapIso φ) (by rw [Functor.mapIso_hom, ← F.map_comp, hφ])

end Transport

end CategoryTheory.ShortComplex

namespace AlgebraicGeometry.Space

-- The abelian structure of the module categories is reached through
-- `SheafOfModules.instAbelian`, whose generic form on a site leaves the module universe a
-- join that is never the universe of the schemes; a search that meets that form first ends in an
-- unsolvable universe constraint rather than in a recoverable failure.  Raising its priority is
-- the device of
-- `StacksFrontier/AlgebraicGeometry/Spaces/ClosedImmersionModulePushforwardRightExact.lean`.
attribute [local instance 5000] SheafOfModules.instAbelian

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : AlgebraicSpaces B S hS} (Y Z : ClosedSubspaces B S hS X.1) (hZY : Z.1 ≤ Y.1)

/-! ### Exactness in the middle, at the spelling of the projection -/

section Respelling

-- The inverse image of modules carries the source and target of its morphism as implicit
-- arguments, and the projection of the fibre-product square has two definitionally equal
-- spellings of them.  Left reducible, the unifier crosses between them by unfolding
-- `AlgebraicGeometry.Space.modulePullback`, which does not finish; made irreducible it matches
-- the two functors argument by argument, which is immediate.  This is the device of
-- `StacksFrontier/AlgebraicGeometry/Spaces/IdealSheafMapVanishing.lean`.  The attribute is confined
-- to this section: the `Abelian` instance of the module categories is not found while it is in
-- force, so the two identifications below are proved with the inverse image reducible again.
attribute [local irreducible] modulePullback

/-- **Exactness in the middle of the conormal complex of a chain of closed subspaces**, at the
spelling `AlgebraicGeometry.Space.preimageProjection` produces.  This is
`AlgebraicGeometry.Space.exact_conormalShortComplex`, the middle clause of [Stacks Project,
Tag 06BD], restated with the source and target of the inverse-image functor along the projection
taken from the type of the projection itself rather than from the two closed subspaces, and with
the vanishing given by `AlgebraicGeometry.Space.conormalMap_comp_conormalMap_eq_zero`, the
clause-one instance, rather than by its form at a variable upper subspace.  The two statements are
definitionally the same; crossing between them has to be done where
`AlgebraicGeometry.Space.modulePullback` is irreducible, so that the two inverse images are
matched argument by argument instead of unfolded. -/
theorem exact_conormalShortComplex_mk :
    (CategoryTheory.ShortComplex.mk
      ((modulePullback B S hS
          (preimageProjection B S hS (subspaceInclusion B S hS X Y) Z)).map
        (conormalMap B S hS Z Y (𝟙 X) (ObjectProperty.homMk (Subfunctor.homOfLe hZY))
          (subspaceInclusion_homOfLe_square B S hS Y Z hZY)))
      (conormalMap B S hS (preimageSubspace B S hS (subspaceInclusion B S hS X Y) Z) Z
        (subspaceInclusion B S hS X Y)
        (preimageProjection B S hS (subspaceInclusion B S hS X Y) Z)
        (conormalEtaleRestrictionSquare B S hS (subspaceInclusion B S hS X Y) Z))
      (conormalMap_comp_conormalMap_eq_zero B S hS Y Z hZY)).Exact :=
  exact_conormalShortComplex B S hS Y Z hZY

end Respelling

/-! ### The identification at a chain of closed subspaces -/

section General

variable {A D : Modules.{u, u} B S hS Z.1.toFunctor Z.2.1}
    (α : A ⟶ conormalModule B S hS X Z) (γ : conormalModule B S hS X Z ⟶ D)
    (hz : α ≫ γ = 0) (σ : (CategoryTheory.ShortComplex.mk α γ hz).Splitting)
    (ρ : (modulePullback B S hS
            (ObjectProperty.homMk (Subfunctor.homOfLe hZY) :
              (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) ⟶
                (⟨Y.1.toFunctor, Y.2.1⟩ : AlgebraicSpaces B S hS))).obj
          (conormalModule B S hS X Y) ≅ D)
    (hρ : ρ.hom ≫ σ.s =
      conormalMap B S hS Z Y (𝟙 X) (ObjectProperty.homMk (Subfunctor.homOfLe hZY))
        (subspaceInclusion_homOfLe_square B S hS Y Z hZY))

include γ hz σ ρ hρ in
/-- **The summand complementary to the inclusion of defining ideal sheaves surjects onto the
conormal module of the new pair.**  Let `Z ⊆ Y ⊆ X` be closed subspaces of an algebraic space, let
`𝒞_{Z/X} = A ⊕ D` be a split decomposition of the conormal module of `Z` in `X`, and suppose the
section `D ⟶ 𝒞_{Z/X}` of the splitting is the left-hand map `ι^*𝒞_{Y/X} ⟶ 𝒞_{Z/X}` of the conormal
complex of the chain up to an isomorphism of its source.  Then the complementary summand `A`,
carried to the inverse image `j⁻¹(Z)` and followed by the right-hand map `p^*𝒞_{Z/X} ⟶ 𝒞_{Z/Y}` of
that complex, is an epimorphism.

Nothing is assumed beyond the splitting and that identification.  The right-hand map is an
epimorphism by `AlgebraicGeometry.Space.epi_conormalMap_closedSubspaces`, the exactness at the
right term of [Stacks Project, Tag 06BD], and the left-hand map is killed by it by
`AlgebraicGeometry.Space.conormalMap_comp_conormalMap_eq_zero`, its vanishing clause; both are
unconditional.  The splitting is transported along `p^*`, which is additive. -/
theorem epi_modulePullback_comp_conormalMap_of_splitting :
    Epi ((modulePullback B S hS
          (preimageProjection B S hS (subspaceInclusion B S hS X Y) Z)).map α ≫
      conormalMap B S hS (preimageSubspace B S hS (subspaceInclusion B S hS X Y) Z) Z
        (subspaceInclusion B S hS X Y)
        (preimageProjection B S hS (subspaceInclusion B S hS X Y) Z)
        (conormalEtaleRestrictionSquare B S hS (subspaceInclusion B S hS X Y) Z)) := by
  have : (modulePullback B S hS
      (preimageProjection B S hS (subspaceInclusion B S hS X Y) Z)).Additive :=
    modulePullback_additive _
  exact CategoryTheory.ShortComplex.epi_map_comp_of_splitting_data
    (modulePullback B S hS (preimageProjection B S hS (subspaceInclusion B S hS X Y) Z))
    α γ σ.r σ.s σ.id
    (conormalMap B S hS (preimageSubspace B S hS (subspaceInclusion B S hS X Y) Z) Z
      (subspaceInclusion B S hS X Y)
      (preimageProjection B S hS (subspaceInclusion B S hS X Y) Z)
      (conormalEtaleRestrictionSquare B S hS (subspaceInclusion B S hS X Y) Z))
    (epi_conormalMap_closedSubspaces B S hS Y Z hZY)
    (conormalMap B S hS Z Y (𝟙 X) (ObjectProperty.homMk (Subfunctor.homOfLe hZY))
      (subspaceInclusion_homOfLe_square B S hS Y Z hZY))
    (conormalMap_comp_conormalMap_eq_zero B S hS Y Z hZY) ρ hρ

include γ hz σ ρ hρ in
/-- **The conormal module of the new pair is the complementary summand.**  In the situation of
`AlgebraicGeometry.Space.epi_modulePullback_comp_conormalMap_of_splitting`, the summand `A`
complementary to the left-hand map maps isomorphically onto `𝒞_{Z/Y}`.

This is the space-level form of the sentence "by construction `𝒞_{Z/Z'} = i^*𝒞_{X/X'}`" in the
proof of [Stacks Project, Tag 06D8], the chain being `Z ⊆ Z' ⊆ Z''` for the subspace `Z'` that
`AlgebraicGeometry.Space.exists_isFirstOrderThickening_definingIdealSheaf_eq_of_le` cuts out of the
universal first order thickening `Z''`.

**Nothing is assumed beyond the splitting and the identification of its section.**  Injectivity
needs exactness in the middle of the conormal complex of the chain, the middle clause of
[Stacks Project, Tag 06BD], and that is
`AlgebraicGeometry.Space.exact_conormalShortComplex`, taken here through
`AlgebraicGeometry.Space.exact_conormalShortComplex_mk`; the implementation notes of this file say
why the respelling is needed. -/
theorem isIso_modulePullback_comp_conormalMap_of_splitting :
    IsIso ((modulePullback B S hS
          (preimageProjection B S hS (subspaceInclusion B S hS X Y) Z)).map α ≫
      conormalMap B S hS (preimageSubspace B S hS (subspaceInclusion B S hS X Y) Z) Z
        (subspaceInclusion B S hS X Y)
        (preimageProjection B S hS (subspaceInclusion B S hS X Y) Z)
        (conormalEtaleRestrictionSquare B S hS (subspaceInclusion B S hS X Y) Z)) := by
  have : (modulePullback B S hS
      (preimageProjection B S hS (subspaceInclusion B S hS X Y) Z)).Additive :=
    modulePullback_additive _
  exact CategoryTheory.ShortComplex.isIso_map_comp_of_splitting_data
    (modulePullback B S hS (preimageProjection B S hS (subspaceInclusion B S hS X Y) Z))
    α γ σ.r σ.s σ.f_r σ.s_g σ.s_r σ.id
    (conormalMap B S hS (preimageSubspace B S hS (subspaceInclusion B S hS X Y) Z) Z
      (subspaceInclusion B S hS X Y)
      (preimageProjection B S hS (subspaceInclusion B S hS X Y) Z)
      (conormalEtaleRestrictionSquare B S hS (subspaceInclusion B S hS X Y) Z))
    (epi_conormalMap_closedSubspaces B S hS Y Z hZY)
    (conormalMap B S hS Z Y (𝟙 X) (ObjectProperty.homMk (Subfunctor.homOfLe hZY))
      (subspaceInclusion_homOfLe_square B S hS Y Z hZY))
    (conormalMap_comp_conormalMap_eq_zero B S hS Y Z hZY)
    (exact_conormalShortComplex_mk B S hS Y Z hZY) ρ hρ

end General

/-! ### The identification at the configuration of Tag 06D8 -/

section IdealSheafSummand

variable {A : Modules.{u, u} B S hS Z.1.toFunctor Z.2.1}
    (α : A ⟶ conormalModule B S hS X Z)
    (γ : conormalModule B S hS X Z ⟶
      (modulePullback B S hS (subspaceInclusion B S hS X Z)).obj
        (definingIdealSheaf B S hS X Y).toSheafOfModules)
    (hz : α ≫ γ = 0) (σ : (CategoryTheory.ShortComplex.mk α γ hz).Splitting)
    (hs : σ.s =
      (show (modulePullback B S hS (subspaceInclusion B S hS X Z)).obj
            (definingIdealSheaf B S hS X Y).toSheafOfModules ⟶
          conormalModule B S hS X Z from
        (modulePullback B S hS (subspaceInclusion B S hS X Z)).map
          (definingIdealSheafHomOfLe B S hS Y Z hZY)))

include γ hz σ hs in
/-- **The summand complementary to `i^*𝓘_Y` inside `𝒞_{Z/X}` surjects onto `𝒞_{Z/Y}`.**  Let
`Z ⊆ Y ⊆ X` be closed subspaces of an algebraic space and let
`𝒞_{Z/X} = A ⊕ i^*𝓘_Y` be a split decomposition of the conormal module of `Z` in `X` whose section
is the inverse image along `i : Z ⟶ X` of the inclusion `𝓘_Y ⊆ 𝓘_Z` of defining ideal sheaves.
Then the complementary summand `A`, carried to the inverse image `j⁻¹(Z)` and followed by the
canonical map `p^*𝒞_{Z/X} ⟶ 𝒞_{Z/Y}` of [Stacks Project, Tag 04CP], is an epimorphism.

**Nothing at all is assumed beyond the splitting.**  The comparison that
`AlgebraicGeometry.Space.epi_modulePullback_comp_conormalMap_of_splitting` takes as a parameter is
discharged here by `AlgebraicGeometry.Space.exists_iso_comp_eq_conormalMap_homOfLe`: the left-hand
map of the conormal complex of the chain *is* the inverse image of that inclusion, up to an
isomorphism of its source.

This is the configuration of the paragraph of [Stacks Project, Tag 06D8] that cuts `Z'` out of the
universal first order thickening `Z''` by the summand `𝒞_{Z/X} ⊆ 𝓘`: there `Y` is `Z'`, whose
defining ideal sheaf is that summand by
`AlgebraicGeometry.Space.exists_isFirstOrderThickening_definingIdealSheaf_eq_of_le`, and the
splitting is the one the source chooses. -/
theorem epi_modulePullback_comp_conormalMap_of_definingIdealSheafSplitting :
    Epi ((modulePullback B S hS
          (preimageProjection B S hS (subspaceInclusion B S hS X Y) Z)).map α ≫
      conormalMap B S hS (preimageSubspace B S hS (subspaceInclusion B S hS X Y) Z) Z
        (subspaceInclusion B S hS X Y)
        (preimageProjection B S hS (subspaceInclusion B S hS X Y) Z)
        (conormalEtaleRestrictionSquare B S hS (subspaceInclusion B S hS X Y) Z)) := by
  obtain ⟨ρ, hρ⟩ := exists_iso_comp_eq_conormalMap_homOfLe B S hS Y Z hZY
  exact epi_modulePullback_comp_conormalMap_of_splitting B S hS Y Z hZY α γ hz σ ρ
    ((congrArg (fun m ↦ ρ.hom ≫ m) hs).trans hρ)

include γ hz σ hs in
/-- **`𝒞_{Z/Y}` is the summand of `𝒞_{Z/X}` complementary to `i^*𝓘_Y`.**  In the situation of
`AlgebraicGeometry.Space.epi_modulePullback_comp_conormalMap_of_definingIdealSheafSplitting`, the
summand `A` maps isomorphically onto `𝒞_{Z/Y}`.

This is the space-level form of the sentence "by construction `𝒞_{Z/Z'} = i^*𝒞_{X/X'}`" in the
proof of [Stacks Project, Tag 06D8].  **The splitting is the only hypothesis.**  Exactness in the
middle of the conormal complex of the chain, the middle clause of [Stacks Project, Tag 06BD], is
`AlgebraicGeometry.Space.exact_conormalShortComplex`, and the identification of the
section with the left-hand map is
`AlgebraicGeometry.Space.exists_iso_comp_eq_conormalMap_homOfLe`. -/
theorem isIso_modulePullback_comp_conormalMap_of_definingIdealSheafSplitting :
    IsIso ((modulePullback B S hS
          (preimageProjection B S hS (subspaceInclusion B S hS X Y) Z)).map α ≫
      conormalMap B S hS (preimageSubspace B S hS (subspaceInclusion B S hS X Y) Z) Z
        (subspaceInclusion B S hS X Y)
        (preimageProjection B S hS (subspaceInclusion B S hS X Y) Z)
        (conormalEtaleRestrictionSquare B S hS (subspaceInclusion B S hS X Y) Z)) := by
  obtain ⟨ρ, hρ⟩ := exists_iso_comp_eq_conormalMap_homOfLe B S hS Y Z hZY
  exact isIso_modulePullback_comp_conormalMap_of_splitting B S hS Y Z hZY α γ hz σ ρ
    ((congrArg (fun m ↦ ρ.hom ≫ m) hs).trans hρ)

end IdealSheafSummand

end AlgebraicGeometry.Space

end
