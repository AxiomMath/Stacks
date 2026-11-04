module

public import Mathlib.CategoryTheory.Discrete.Basic
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Products
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.Descent.QuasicoherentTensor
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.Descent.Smallness
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.Modules
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.FibreProducts

/-!
# The site hypotheses of the tensor clause, at the fibred fppf site of Stacks 06WG

`Stacks.SheafOfModules.TensorProduct.isQuasicoherentOnSite_tensorSheaf` proves the tensor
clause of Stacks 06WV (5) and Stacks 06WN (2) for the quasi-coherence of Stacks 03DL (6), on
an arbitrary ringed site satisfying five conditions: a size hypothesis `UnivLE`, fibre
products, binary products, and sheafification on the site and on each of its localizations.
The source states the clause for `QCoh(𝒪_𝒳)` of Stacks 06WG, which is quasi-coherence on the
*fibred fppf site* of a category fibred in groupoids over `(Sch/S)_fppf`.  This file settles
which of the five conditions that site satisfies.

Three of them it does satisfy, and two it does not.  Fibre products are Stacks 06WY,
`AlgebraicGeometry.BigFppfOver.hasPullbacks_of_isFiberedInGroupoids`; sheafification on the
site is `AlgebraicGeometry.FibredSite.hasWeakSheafify_associatedTopology`, and on the
localizations it is proved below from essential smallness.  The two that fail are the size
hypothesis, which at the universes of the fibred site reads `UnivLE.{u + 1, u}` and is
therefore false, and binary products, which fail because a category fibred in groupoids
generally has no final object — the tensor clause needs them only to refine two coverings of
the final object, which is a feature of Mathlib's quasi-coherence predicate and not of the
source's.

## Main results

* `AlgebraicGeometry.FibredSite.hasSheafify_associatedTopology_over` and
  `AlgebraicGeometry.FibredSite.wEqualsLocallyBijective_associatedTopology_over`: the two
  sheafification conditions hold on every localization of every associated site of an
  essentially small category fibred in groupoids.
* `AlgebraicGeometry.FibredSite.not_univLE_associatedSite`: the size hypothesis fails at the
  universes of the fibred fppf site, where it reads `UnivLE.{u + 1, u}`.  It is the only
  condition of the tensor clause that fails there: binary products of the big fppf category
  over `S` are `AlgebraicGeometry.hasBinaryProducts_bigFppfOver`.
* `AlgebraicGeometry.FibredSite.not_hasBinaryProducts_twoLabel`: binary products genuinely
  fail for a category fibred in groupoids over `(Sch/S)_fppf` — namely for
  `AlgebraicGeometry.FibredSite.TwoLabel`, the big fppf category tagged by a two-element
  discrete groupoid, which by
  `AlgebraicGeometry.FibredSite.isFiberedInGroupoids_twoLabelProjection` is fibred in
  groupoids and by `AlgebraicGeometry.FibredSite.hasPullbacks_twoLabel` has fibre products.

## Implementation notes

The universes, side by side.  `AlgebraicGeometry.FibredSite.quasicoherentModules` takes
`B : BigFppfSite.{u}`, `S : Scheme.{u}`, a category `𝒳 : Type v` with `Category.{w} 𝒳` and
module sections in `Type m`, and its coefficient sheaf of rings
`AlgebraicGeometry.FibredSite.ringStructureSheafCore` is a sheaf of `RingCat.{u}`.  So the
size hypothesis of the tensor clause, `UnivLE.{max u' v' w', w'}` for a site `C : Type u'`
with `Category.{v'} C` and sections in `Type w'`, reads `UnivLE.{max v w m, m}` there.  The
objects of the big fppf category are a full subcategory of `Scheme.{u}` and so live in
`Type (u + 1)`, while its morphisms live in `Type u`.  A category fibred in groupoids over it
has, by the lifting axiom, an object over every object of the base admitting a morphism into
one of its own objects, which is why the development states the fibred site at
`𝒳 : Type (u + 1)` with `Category.{u} 𝒳` — see
`AlgebraicGeometry.FibredSite.hasWeakSheafify_associatedTopology`, whose essential-smallness
hypothesis is stated at exactly those levels.  With the module sections at the universe of the
structure sheaf, `m = u`, the hypothesis is therefore `UnivLE.{u + 1, u}`.  The same count for
the big fppf site itself, the case `𝒳 = BigFppfOver B S hS` of the identity fibred category,
gives the same `UnivLE.{u + 1, u}`.

The size hypothesis is satisfiable at the fibred fppf site, but only by raising the module
sections one universe above the structure sheaf: at `m = u + 1` it reads
`UnivLE.{u + 1, u + 1}`, which holds by Mathlib's instance `UnivLE.self`.  That instantiation of
`AlgebraicGeometry.FibredSite.quasicoherentModules` is not the one the tensor clause can be
applied at, because `Stacks.SheafOfModules.TensorProduct.isQuasicoherentOnSite_tensorSheaf` takes
its coefficients and its sections in one and the same universe.

Nothing here carries a `stacks` attribute: which hypotheses a site satisfies is a fact about
this development's encoding, not a statement of the source.

## References

* [Stacks Project, Tag 06WG](https://stacks.math.columbia.edu/tag/06WG)
* [Stacks Project, Tag 06WV](https://stacks.math.columbia.edu/tag/06WV)
* [Stacks Project, Tag 06WN](https://stacks.math.columbia.edu/tag/06WN)
* [Stacks Project, Tag 06WY](https://stacks.math.columbia.edu/tag/06WY)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.FibredSite

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The three conditions the fibred fppf site satisfies -/

section Satisfied

variable {𝒳 : Type (u + 1)} [Category.{u} 𝒳] [EssentiallySmall.{u} 𝒳]
  (p : 𝒳 ⥤ BigFppfOver B S hS)

/-- Sheafification into abelian groups exists on every localization at an object of each of the
five sites associated with an essentially small category fibred in groupoids over the schemes
over `S`.  This is the localized companion of
`AlgebraicGeometry.FibredSite.hasWeakSheafify_associatedTopology`, and it holds for the same
reason: the localization of an essentially small category at an object is essentially
small. -/
public theorem hasSheafify_associatedTopology_over (τ : SiteKind) (X : 𝒳) :
    HasSheafify ((BigFppfOver.associatedTopology B S hS p τ).over X) AddCommGrpCat.{u} :=
  hasSheafifyEssentiallySmallSite.{u} _ _

/-- Weak equivalences of abelian presheaves on every localization at an object of each of the
five sites associated with an essentially small category fibred in groupoids are the locally
bijective maps. -/
public theorem wEqualsLocallyBijective_associatedTopology_over (τ : SiteKind) (X : 𝒳) :
    GrothendieckTopology.WEqualsLocallyBijective
      ((BigFppfOver.associatedTopology B S hS p τ).over X) AddCommGrpCat.{u} :=
  GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall _

end Satisfied

/-! ### The size hypothesis -/

/-- **The size hypothesis of the tensor clause fails at the fibred fppf site of Stacks 06WG.**
The objects of that site live in `Type (u + 1)`, its morphisms and its structure sheaf in
`Type u`; with the module sections taken at the universe of the structure sheaf the hypothesis
`UnivLE.{max v w m, m}` of
`Stacks.SheafOfModules.TensorProduct.isQuasicoherentOnSite_tensorSheaf` reads
`UnivLE.{u + 1, u}`, which `not_univLE_succ` refutes. -/
public theorem not_univLE_associatedSite : ¬ UnivLE.{max (u + 1) u u, u} :=
  not_univLE_succ

/-! ### Binary products -/

/-- The big fppf category over `S` with its objects tagged by a two-element set, a category
fibred in groupoids over `(Sch/S)_{fppf}` whose fibres are the discrete groupoid on two
objects. -/
public abbrev TwoLabel := BigFppfOver B S hS × Discrete (Fin 2)

/-- The structure functor of `AlgebraicGeometry.FibredSite.TwoLabel`: forget the tag. -/
public abbrev twoLabelProjection : TwoLabel B S hS ⥤ BigFppfOver B S hS :=
  CategoryTheory.Prod.fst _ _

/-- `AlgebraicGeometry.FibredSite.TwoLabel` is fibred in groupoids over the big fppf category
over `S`: a base morphism lifts by keeping the tag, and a fill-in is unique because the tag
component of a morphism of a discrete category is determined by its endpoints. -/
public theorem isFiberedInGroupoids_twoLabelProjection :
    (twoLabelProjection B S hS).IsFiberedInGroupoids where
  exists_lift := by
    rintro V U f x rfl
    exact ⟨(V, x.2), (f, 𝟙 x.2), CategoryTheory.IsHomLift.of_fac _ _ _ rfl rfl (by simp)⟩
  unique_lift := by
    intro x y z φ ψ f h
    refine ⟨(f, eqToHom (Discrete.ext
      ((Discrete.eq_of_hom ψ.2).trans (Discrete.eq_of_hom φ.2).symm))), ⟨rfl, ?_⟩, ?_⟩
    · exact Prod.ext h (Subsingleton.elim _ _)
    · rintro ⟨χ₁, χ₂⟩ ⟨hχ, -⟩
      exact Prod.ext hχ (Subsingleton.elim _ _)

/-- `AlgebraicGeometry.FibredSite.TwoLabel` has fibre products, by Stacks 06WY. -/
public theorem hasPullbacks_twoLabel : HasPullbacks (TwoLabel B S hS) :=
  BigFppfOver.hasPullbacks_of_isFiberedInGroupoids B S hS _
    (isFiberedInGroupoids_twoLabelProjection B S hS)

/-- **Binary products fail for a category fibred in groupoids over `(Sch/S)_{fppf}`.**  An
object of `AlgebraicGeometry.FibredSite.TwoLabel` admitting morphisms to two objects with
different tags would have to carry both tags, so the two objects have no product, and no
object of the category tagged `0` has a product with one tagged `1`.

This is the second condition of
`Stacks.SheafOfModules.TensorProduct.isQuasicoherentOnSite_tensorSheaf` that the site of
Stacks 06WG does not satisfy, and unlike the size hypothesis it is not an artefact of
universes: the clause uses binary products only to refine two coverings of the final object,
which is what Mathlib's quasi-coherence predicate asks for, whereas the quasi-coherence of
Stacks 03DL (6) asks for a covering of *each* object and needs no such refinement. -/
public theorem not_hasBinaryProducts_twoLabel : ¬ HasBinaryProducts (TwoLabel B S hS) := by
  intro _
  set X₀ : BigFppfOver B S hS := Over.mk (𝟙 (B.obj hS)) with hX₀
  have h₁ := Discrete.eq_of_hom ((CategoryTheory.Prod.snd (BigFppfOver B S hS)
    (Discrete (Fin 2))).map (prod.fst (X := (X₀, ⟨0⟩)) (Y := (X₀, ⟨(1 : Fin 2)⟩))))
  have h₂ := Discrete.eq_of_hom ((CategoryTheory.Prod.snd (BigFppfOver B S hS)
    (Discrete (Fin 2))).map (prod.snd (X := (X₀, ⟨0⟩)) (Y := (X₀, ⟨(1 : Fin 2)⟩))))
  have h₀₁ : (0 : Fin 2) = 1 := h₁.symm.trans h₂
  exact absurd h₀₁ (by decide)

end AlgebraicGeometry.FibredSite

end
