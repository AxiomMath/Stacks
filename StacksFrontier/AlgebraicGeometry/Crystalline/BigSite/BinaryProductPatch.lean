module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import StacksFrontier.AlgebraicGeometry.Crystalline.BigSite.Functoriality
public import StacksFrontier.AlgebraicGeometry.Crystalline.BigSite.SituationRestrict

/-!
# Affine patches for a pair of objects of the big crystalline category

Fix a global crystalline situation `(p, (S, I, γ), X)` and two objects `A = (U_A, T_A, δ_A)` and
`B = (U_B, T_B, δ_B)` of `CRIS(X/S)`.  A *product patch* for the pair is a choice of affine opens
`W ⊆ S`, `V ⊆ X`, `U ⊆ T_A` and `U' ⊆ T_B` such that the image of `V` in `S` lies in `W`, the
ambient structure maps of `A` and `B` carry `U` and `U'` into `W`, and the two maps to `X` carry
the thickened parts of `U` and `U'` into `V`.  Over such a patch the whole situation is affine, so
the affine model of products, [Stacks, Tag 07HN], applies to the restrictions `A|_U` and `B|_{U'}`.

The results here are the combinatorial half of the globalisation step for products of pairs in
`CRIS(X/S)`: every point of a thickened scheme lies in a patch, and consequently the preimages of
the patches cover the ambient scheme of any object mapping to both `A` and `B`.  This is what makes
the local products glue.

## Main definitions

* `Crystalline.GlobalCrystallineSituation.ProductPatch` — a quadruple of affine opens adapted to a
  pair of objects of `CRIS(X/S)`.
* `Crystalline.GlobalCrystallineSituation.ProductPatch.preimage` — the open of the ambient scheme
  of `T` on which a cone `T ⟶ A`, `T ⟶ B` factors through the patch.

## Main results

* `Crystalline.GlobalCrystallineSituation.exists_productPatch` — a point of `U_A` and a point of
  `U_B` with the same image in `X` lie in a common patch.
* `Crystalline.GlobalCrystallineSituation.exists_productPatch_le` — two patches containing a
  common pair of points are refined by a third; this is the local directedness of the diagram of
  patches.
* `Crystalline.GlobalCrystallineSituation.ProductPatch.iSup_preimage_eq_top` — the preimages of
  the patches cover the ambient scheme of the vertex of any cone over the pair.
* `AlgebraicGeometry.Scheme.isNilpotent_of_forall_isNilpotent_germ` — a global section of a
  quasi-compact scheme which is nilpotent in every local ring is nilpotent.
* `Crystalline.GlobalCrystallineSituation.isNilpotent_prime_sections_of_isAffineOpen` and
  `Crystalline.GlobalCrystallineSituation.isNilpotent_prime_sections_of_isAffine` — the fixed
  prime of a
  global crystalline situation is nilpotent on the sections of any affine open of `X`, and on
  global sections when `X` is affine.

## What is and is not proved

No tag attribute is placed in this file.  **This is not [Stacks, Tag 07I9]**: nothing here asserts
that any product exists.  What is proved is only that the affine patches adapted to a pair of
objects are plentiful enough to cover, which is the indexing data the construction of the product
is glued over.  The construction itself, and the universal property, are elsewhere.

The nilpotence results are independent of products and are stated here because this is where the
affine patches are produced.
`Crystalline.GlobalCrystallineSituation.isNilpotent_prime_sections_of_isAffine`
discharges the hypothesis carried as an explicit argument `hp` throughout the affine comparison
stack — `Crystalline.GlobalCrystallineSituation.affineSituation` and everything downstream of it —
whose docstring states that the implication from local nilpotence "is not proved here".  Nothing
in this file changes those signatures; the hypothesis is simply now derivable.

## References

* [Stacks Project, Tag 07HN](https://stacks.math.columbia.edu/tag/07HN)
* [Stacks Project, Tag 07I9](https://stacks.math.columbia.edu/tag/07I9)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

/-- **A global section of a quasi-compact scheme which is nilpotent in every local ring is
nilpotent.**  The basic open of the section is the locus where it is a unit, and a nilpotent
element of a local ring is not a unit, so that locus is empty; on a quasi-compact scheme a section
with empty basic open is nilpotent.

For a general scheme the statement fails, which is why a `Crystalline.GlobalCrystallineSituation`
asks only for nilpotence of `p` in every local ring. -/
theorem isNilpotent_of_forall_isNilpotent_germ {X : Scheme.{u}} [CompactSpace X] (f : Γ(X, ⊤))
    (h : ∀ x : X, IsNilpotent ((X.presheaf.germ ⊤ x trivial) f)) : IsNilpotent f := by
  rw [Scheme.isNilpotent_iff_basicOpen_eq_bot]
  refine le_antisymm (fun x hx ↦ ?_) bot_le
  exact absurd ((X.mem_basicOpen_top f x).mp hx) (h x).not_isUnit

end AlgebraicGeometry.Scheme

namespace Crystalline

namespace GlobalCrystallineSituation

/-- **The fixed prime of a global crystalline situation is nilpotent on every affine open of `X`.**
A `Crystalline.GlobalCrystallineSituation` asks only that `p` be nilpotent in every local ring of
`X`; on a quasi-compact open — in particular an affine one — that upgrades to nilpotence of `p` in
the ring of sections, by
`AlgebraicGeometry.Scheme.isNilpotent_of_forall_isNilpotent_germ`.  The local rings of an open
subscheme are those of the ambient scheme, by `AlgebraicGeometry.Scheme.Opens.stalkIso`.

This is the hypothesis called `hp` throughout the affine comparison stack, where it is carried as
an explicit argument; the docstring of `Crystalline.GlobalCrystallineSituation.affineSituation`
says the implication "is not proved here". -/
theorem isNilpotent_prime_sections_of_isAffineOpen (S : GlobalCrystallineSituation.{u})
    (V : S.X.Opens) (hV : IsAffineOpen V) : IsNilpotent ((S.p : ℕ) : Γ(V.toScheme, ⊤)) := by
  have : IsAffine V.toScheme := hV
  refine AlgebraicGeometry.Scheme.isNilpotent_of_forall_isNilpotent_germ _ fun y ↦ ?_
  rw [map_natCast]
  have hstalk := (S.prime_locallyNilpotent y.1).map
    (CommRingCat.Hom.hom (AlgebraicGeometry.Scheme.Opens.stalkIso V y).inv)
  rwa [map_natCast] at hstalk

/-- **The fixed prime of a global crystalline situation with affine `X` is nilpotent on global
sections.**  `X` is then quasi-compact, so
`AlgebraicGeometry.Scheme.isNilpotent_of_forall_isNilpotent_germ` applies directly to the
situation's local nilpotence. -/
theorem isNilpotent_prime_sections_of_isAffine (S : GlobalCrystallineSituation.{u}) [IsAffine S.X] :
    IsNilpotent ((S.p : ℕ) : Γ(S.X, ⊤)) := by
  refine AlgebraicGeometry.Scheme.isNilpotent_of_forall_isNilpotent_germ _ fun x ↦ ?_
  rw [map_natCast]
  exact S.prime_locallyNilpotent x

end GlobalCrystallineSituation

namespace SchemeThickening

variable (D : SchemeThickening.{u})

/-- **The immersion of a divided power thickening of schemes is an open embedding.**  It is a
closed embedding and surjective, hence a homeomorphism onto the whole space. -/
theorem isOpenEmbedding_immersion : Topology.IsOpenEmbedding D.immersion :=
  D.immersion.isClosedEmbedding.isEmbedding.isOpenEmbedding_of_surjective D.isThickening.2

/-- The image of an open of the thickened scheme as an open of the ambient scheme.  The immersion
is an open embedding, so the image of an open is open. -/
def imageOpen (V : D.source.Opens) : D.target.scheme.Opens :=
  ⟨D.immersion '' V, D.isOpenEmbedding_immersion.isOpenMap _ V.2⟩

/-- The preimage of the image of an open of the thickened scheme is that open again: the immersion
is injective. -/
theorem preimage_imageOpen (V : D.source.Opens) :
    D.immersion ⁻¹ᵁ D.imageOpen V = V := by
  ext x
  change D.immersion x ∈ D.immersion '' (V : Set D.source) ↔ x ∈ V
  refine ⟨?_, fun hx ↦ ⟨x, hx, rfl⟩⟩
  rintro ⟨y, hy, h⟩
  exact D.immersion.isClosedEmbedding.injective h ▸ hy

end SchemeThickening

namespace GlobalCrystallineSituation

variable {S : GlobalCrystallineSituation.{u}}

/-- **An affine open of the ambient scheme of an object of `CRIS(X/S)` adapted to a pair of opens
downstairs, and inside a prescribed open.**  Given a point of the thickened scheme whose image in
`S` lies in `W`, whose image in `X` lies in `V`, and whose image in the ambient scheme lies in `Z`,
there is an affine open of the ambient scheme containing that image, contained in `Z`, carried into
`W` by the structure map and whose thickened part is carried into `V`.

The extra open `Z` is what makes the patches of a pair of objects refine: two patches can be
refined to a third below both, by taking `Z` to be the intersection of their two opens. -/
theorem exists_affineOpen_ambient_le (A : Thickening S) (x : A.thickening.source)
    (W : S.S.scheme.Opens) (V : S.X.Opens) (Z : A.thickening.target.scheme.Opens)
    (hxW : sourceToBase S (A.toX x) ∈ W) (hxV : A.toX x ∈ V)
    (hxZ : A.thickening.immersion x ∈ Z) :
    ∃ U : A.thickening.target.scheme.affineOpens,
      A.thickening.immersion x ∈ (U : A.thickening.target.scheme.Opens) ∧
      (U : A.thickening.target.scheme.Opens) ≤ Z ∧
      (U : A.thickening.target.scheme.Opens) ≤ A.toBase.hom ⁻¹ᵁ W ∧
      A.thickening.immersion ⁻¹ᵁ (U : A.thickening.target.scheme.Opens) ≤ A.toX ⁻¹ᵁ V := by
  set P := Z ⊓ ((A.toBase.hom ⁻¹ᵁ W) ⊓ A.thickening.imageOpen (A.toX ⁻¹ᵁ V)) with hP
  have hx : A.thickening.immersion x ∈ P := by
    refine ⟨hxZ, ?_, ⟨x, hxV, rfl⟩⟩
    have h := congrArg (fun f ↦ f x) A.over_base
    change A.toBase.hom (A.thickening.immersion x) = sourceToBase S (A.toX x) at h
    change A.toBase.hom (A.thickening.immersion x) ∈ W
    rw [h]
    exact hxW
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUP⟩ :=
    A.thickening.target.scheme.isBasis_affineOpens.exists_subset_of_mem_open hx P.2
  refine ⟨⟨U, hU⟩, hxU, hUP.trans inf_le_left,
    hUP.trans (inf_le_right.trans inf_le_left), ?_⟩
  rw [← A.thickening.preimage_imageOpen (A.toX ⁻¹ᵁ V)]
  exact (TopologicalSpace.Opens.map A.thickening.immersion.base).monotone
    (hUP.trans (inf_le_right.trans inf_le_right))

/-- **An affine open of the ambient scheme of an object of `CRIS(X/S)` adapted to a pair of opens
downstairs.**  The case `Z = ⊤` of
`Crystalline.GlobalCrystallineSituation.exists_affineOpen_ambient_le`. -/
theorem exists_affineOpen_ambient (A : Thickening S) (x : A.thickening.source)
    (W : S.S.scheme.Opens) (V : S.X.Opens)
    (hxW : sourceToBase S (A.toX x) ∈ W) (hxV : A.toX x ∈ V) :
    ∃ U : A.thickening.target.scheme.affineOpens,
      A.thickening.immersion x ∈ (U : A.thickening.target.scheme.Opens) ∧
      (U : A.thickening.target.scheme.Opens) ≤ A.toBase.hom ⁻¹ᵁ W ∧
      A.thickening.immersion ⁻¹ᵁ (U : A.thickening.target.scheme.Opens) ≤ A.toX ⁻¹ᵁ V := by
  obtain ⟨U, hxU, _, hUW, hUV⟩ :=
    exists_affineOpen_ambient_le A x W V ⊤ hxW hxV trivial
  exact ⟨U, hxU, hUW, hUV⟩

/-- **A product patch for a pair of objects of `CRIS(X/S)`.**  Affine opens `W ⊆ S` and `V ⊆ X`
over which the situation is affine, together with affine opens of the two ambient schemes adapted
to them: the two structure maps to the divided power base carry them into `W`, and the two maps to
`X` carry their thickened parts into `V`.  Restricting `A` and `B` to such a pair of opens gives
objects of the restricted, affine, situation. -/
structure ProductPatch (A B : Thickening S) where
  /-- An affine open of the divided power base. -/
  baseOpen : S.S.scheme.affineOpens
  /-- An affine open of `X` lying over `baseOpen`. -/
  sourceOpen : S.X.affineOpens
  /-- The affine open of `X` lies over the affine open of the base. -/
  source_le : (sourceOpen : S.X.Opens) ≤ sourceToBase S ⁻¹ᵁ (baseOpen : S.S.scheme.Opens)
  /-- An affine open of the ambient scheme of the first object. -/
  leftOpen : A.thickening.target.scheme.affineOpens
  /-- An affine open of the ambient scheme of the second object. -/
  rightOpen : B.thickening.target.scheme.affineOpens
  /-- The first affine open lies over the affine open of the base. -/
  left_base : (leftOpen : A.thickening.target.scheme.Opens) ≤
    A.toBase.hom ⁻¹ᵁ (baseOpen : S.S.scheme.Opens)
  /-- The second affine open lies over the affine open of the base. -/
  right_base : (rightOpen : B.thickening.target.scheme.Opens) ≤
    B.toBase.hom ⁻¹ᵁ (baseOpen : S.S.scheme.Opens)
  /-- The thickened part of the first affine open is carried into the affine open of `X`. -/
  left_source : A.thickening.immersion ⁻¹ᵁ (leftOpen : A.thickening.target.scheme.Opens) ≤
    A.toX ⁻¹ᵁ (sourceOpen : S.X.Opens)
  /-- The thickened part of the second affine open is carried into the affine open of `X`. -/
  right_source : B.thickening.immersion ⁻¹ᵁ (rightOpen : B.thickening.target.scheme.Opens) ≤
    B.toX ⁻¹ᵁ (sourceOpen : S.X.Opens)

namespace ProductPatch

variable {A B : Thickening S}

/-- The image of the first affine open of a patch lies in the affine open of the base. -/
theorem range_left_base (P : ProductPatch A B) :
    Set.range ((A.restrictOpen (P.leftOpen : A.thickening.target.scheme.Opens)).toBase.hom) ⊆
      (P.baseOpen : S.S.scheme.Opens) := by
  rintro _ ⟨x, rfl⟩
  exact P.left_base x.property

/-- The image of the second affine open of a patch lies in the affine open of the base. -/
theorem range_right_base (P : ProductPatch A B) :
    Set.range ((B.restrictOpen (P.rightOpen : B.thickening.target.scheme.Opens)).toBase.hom) ⊆
      (P.baseOpen : S.S.scheme.Opens) := by
  rintro _ ⟨x, rfl⟩
  exact P.right_base x.property

/-- The image in `X` of the thickened part of the first affine open of a patch lies in the affine
open of `X`. -/
theorem range_left_source (P : ProductPatch A B) :
    Set.range ((A.restrictOpen (P.leftOpen : A.thickening.target.scheme.Opens)).toX) ⊆
      (P.sourceOpen : S.X.Opens) := by
  rintro _ ⟨x, rfl⟩
  exact P.left_source x.property

/-- The image in `X` of the thickened part of the second affine open of a patch lies in the affine
open of `X`. -/
theorem range_right_source (P : ProductPatch A B) :
    Set.range ((B.restrictOpen (P.rightOpen : B.thickening.target.scheme.Opens)).toX) ⊆
      (P.sourceOpen : S.X.Opens) := by
  rintro _ ⟨x, rfl⟩
  exact P.right_source x.property

/-- **The open of the ambient scheme of `T` on which a pair of morphisms `T ⟶ A`, `T ⟶ B` factors
through a patch**: the intersection of the preimages of the patch's two affine opens. -/
def preimage {T : Thickening S} (f : T ⟶ A) (g : T ⟶ B) (P : ProductPatch A B) :
    T.thickening.target.scheme.Opens :=
  (f.targetHom.hom ⁻¹ᵁ (P.leftOpen : A.thickening.target.scheme.Opens)) ⊓
    (g.targetHom.hom ⁻¹ᵁ (P.rightOpen : B.thickening.target.scheme.Opens))

/-- **Refinement of product patches.**  One patch refines another when each of its two ambient
affine opens is contained in the other's.  The local products over the patches are indexed by this
order: a refinement induces a map of local products, and that map is an open immersion. -/
instance instPreorder : Preorder (ProductPatch A B) where
  le P Q := (P.leftOpen : A.thickening.target.scheme.Opens) ≤ Q.leftOpen ∧
    (P.rightOpen : B.thickening.target.scheme.Opens) ≤ Q.rightOpen
  le_refl _ := ⟨le_rfl, le_rfl⟩
  le_trans _ _ _ h k := ⟨h.1.trans k.1, h.2.trans k.2⟩

/-- A refinement of patches contains the first ambient affine open in the second. -/
theorem leftOpen_le_of_le {P Q : ProductPatch A B} (h : P ≤ Q) :
    (P.leftOpen : A.thickening.target.scheme.Opens) ≤ Q.leftOpen := h.1

/-- A refinement of patches contains the first ambient affine open in the second, on the right. -/
theorem rightOpen_le_of_le {P Q : ProductPatch A B} (h : P ≤ Q) :
    (P.rightOpen : B.thickening.target.scheme.Opens) ≤ Q.rightOpen := h.2

end ProductPatch

/-- Affine opens `W ⊆ S` and `V ⊆ X` over `W` containing the images of two points with the same
image in `X`. -/
private theorem exists_affineOpens_around {A B : Thickening S} (a : A.thickening.source)
    (b : B.thickening.source) (hab : A.toX a = B.toX b) :
    ∃ (W : S.S.scheme.affineOpens) (V : S.X.affineOpens),
      (V : S.X.Opens) ≤ sourceToBase S ⁻¹ᵁ (W : S.S.scheme.Opens) ∧
      sourceToBase S (A.toX a) ∈ (W : S.S.scheme.Opens) ∧ A.toX a ∈ (V : S.X.Opens) ∧
      sourceToBase S (B.toX b) ∈ (W : S.S.scheme.Opens) ∧ B.toX b ∈ (V : S.X.Opens) := by
  obtain ⟨_, ⟨W, hW, rfl⟩, hxW, _⟩ :=
    S.S.scheme.isBasis_affineOpens.exists_subset_of_mem_open
      (show sourceToBase S (A.toX a) ∈ (⊤ : S.S.scheme.Opens) from trivial) isOpen_univ
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVW⟩ :=
    S.X.isBasis_affineOpens.exists_subset_of_mem_open hxW (sourceToBase S ⁻¹ᵁ W).2
  exact ⟨⟨W, hW⟩, ⟨V, hV⟩, hVW, hxW, hxV, hab ▸ hxW, hab ▸ hxV⟩

/-- **A point of the thickened scheme of `A` and a point of that of `B` with the same image in `X`
lie in a common product patch.**  Choose an affine open of `S` around the common image in the base,
an affine open of `X` inside its preimage around the common image in `X`, and then an adapted
affine open of each of the two ambient schemes by
`Crystalline.GlobalCrystallineSituation.exists_affineOpen_ambient`. -/
theorem exists_productPatch {A B : Thickening S} (a : A.thickening.source)
    (b : B.thickening.source) (hab : A.toX a = B.toX b) :
    ∃ P : ProductPatch A B,
      A.thickening.immersion a ∈ (P.leftOpen : A.thickening.target.scheme.Opens) ∧
      B.thickening.immersion b ∈ (P.rightOpen : B.thickening.target.scheme.Opens) := by
  obtain ⟨W, V, hVW, hxW, hxV, hbW, hbV⟩ := exists_affineOpens_around a b hab
  obtain ⟨UA, ha, haW, haV⟩ := exists_affineOpen_ambient A a W V hxW hxV
  obtain ⟨UB, hb, hbW', hbV'⟩ := exists_affineOpen_ambient B b W V hbW hbV
  exact ⟨⟨W, V, hVW, UA, UB, haW, hbW', haV, hbV'⟩, ha, hb⟩

/-- **Two product patches containing a common pair of points are refined by a third.**  Choose a
fresh affine open of `S` around the common image in the base and a fresh affine open of `X` inside
its preimage, then apply
`Crystalline.GlobalCrystallineSituation.exists_affineOpen_ambient_le` to each of the two objects
with the intersection of the two patches' ambient opens as the prescribed open.

This is the local directedness of the diagram of patches, and it is what makes the local products
glue: the two local products agree, over the refinement, with the same third local product. -/
theorem exists_productPatch_le {A B : Thickening S} (P Q : ProductPatch A B)
    (a : A.thickening.source) (b : B.thickening.source) (hab : A.toX a = B.toX b)
    (haP : A.thickening.immersion a ∈ (P.leftOpen : A.thickening.target.scheme.Opens))
    (haQ : A.thickening.immersion a ∈ (Q.leftOpen : A.thickening.target.scheme.Opens))
    (hbP : B.thickening.immersion b ∈ (P.rightOpen : B.thickening.target.scheme.Opens))
    (hbQ : B.thickening.immersion b ∈ (Q.rightOpen : B.thickening.target.scheme.Opens)) :
    ∃ R : ProductPatch A B, R ≤ P ∧ R ≤ Q ∧
      A.thickening.immersion a ∈ (R.leftOpen : A.thickening.target.scheme.Opens) ∧
      B.thickening.immersion b ∈ (R.rightOpen : B.thickening.target.scheme.Opens) := by
  obtain ⟨W, V, hVW, hxW, hxV, hbW, hbV⟩ := exists_affineOpens_around a b hab
  obtain ⟨UA, ha, haZ, haW, haV⟩ :=
    exists_affineOpen_ambient_le A a W V
      ((P.leftOpen : A.thickening.target.scheme.Opens) ⊓ Q.leftOpen) hxW hxV ⟨haP, haQ⟩
  obtain ⟨UB, hb, hbZ, hbW', hbV'⟩ :=
    exists_affineOpen_ambient_le B b W V
      ((P.rightOpen : B.thickening.target.scheme.Opens) ⊓ Q.rightOpen) hbW hbV ⟨hbP, hbQ⟩
  refine ⟨⟨W, V, hVW, UA, UB, haW, hbW', haV, hbV'⟩,
    ⟨haZ.trans inf_le_left, hbZ.trans inf_le_left⟩,
    ⟨haZ.trans inf_le_right, hbZ.trans inf_le_right⟩, ha, hb⟩

/-- A morphism of thickenings commutes with the immersions, pointwise. -/
private theorem targetHom_immersion_apply {T A : Thickening S} (f : T ⟶ A)
    (y : T.thickening.source) :
    f.targetHom.hom (T.thickening.immersion y) = A.thickening.immersion (f.sourceHom y) :=
  congrArg (fun k ↦ k y) f.immersion_naturality

namespace ProductPatch

/-- **The preimages of the product patches cover the ambient scheme of the vertex of any cone over
the pair.**  A point of the ambient scheme of `T` is the image of a point of its thickened scheme,
since the immersion of a thickening is surjective; the two images of that point in the thickened
schemes of `A` and `B` have the same image in `X`, so they lie in a common patch, and the original
point lies in the preimage of that patch. -/
theorem iSup_preimage_eq_top {T A B : Thickening S} (f : T ⟶ A) (g : T ⟶ B) :
    ⨆ P : ProductPatch A B, preimage f g P = ⊤ := by
  apply top_unique
  intro x _
  obtain ⟨y, rfl⟩ := T.thickening.isThickening.2 x
  have he : A.toX (f.sourceHom y) = B.toX (g.sourceHom y) :=
    (congrArg (fun k ↦ k y) f.toX_naturality).trans
      (congrArg (fun k ↦ k y) g.toX_naturality).symm
  obtain ⟨P, hP, hQ⟩ := exists_productPatch (f.sourceHom y) (g.sourceHom y) he
  refine TopologicalSpace.Opens.mem_iSup.mpr ⟨P, ?_, ?_⟩
  · change f.targetHom.hom (T.thickening.immersion y) ∈
      (P.leftOpen : A.thickening.target.scheme.Opens)
    rwa [targetHom_immersion_apply]
  · change g.targetHom.hom (T.thickening.immersion y) ∈
      (P.rightOpen : B.thickening.target.scheme.Opens)
    rwa [targetHom_immersion_apply]

end ProductPatch

end GlobalCrystallineSituation

end Crystalline

end
