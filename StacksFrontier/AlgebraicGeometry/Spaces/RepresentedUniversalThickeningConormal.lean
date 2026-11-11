module

public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalFiniteLocallyFree
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.UniversalRepresentableConverse
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversalThickeningOfFormallyUnramified

/-!
# The universal first-order thickening of a morphism of representable spaces

Let `B` be a big fppf site containing a scheme `S`, let `g : V ⟶ U` be a morphism of algebraic
spaces over `S` whose source and target are representable — presented by isomorphisms
`eV : yoneda.obj V₀ ≅ V.obj` and `eU : yoneda.obj U₀ ≅ U.obj` with objects `V₀`, `U₀` of the
big fppf category over `S` — and let `s` be a universal first-order thickening of `g`, in the
space-level sense of `AlgebraicGeometry.Space.UniversalFirstOrderThickening` (Stacks 0607).
The ambient algebraic space of `s` is then **representable**, by an object `W` of the site which
makes `V₀ ⟶ W ⟶ U₀` a universal first-order thickening of `V₀` over `U₀` at the level of
*schemes*, in the sense of `Stacks.Thickenings.IsUniversalFirstOrderThickening` (Stacks 04F3);
and the conormal sheaf `𝒞_{V/U}` of Stacks 0607 of `s` is the conormal module of Stacks 04CN
of the represented closed subspace `V₀ ⊆ W` of the representable algebraic space
`yoneda.obj W`, transported along the identification of the source with that subspace.

The morphism of schemes this presents is
`(BigFppfOver.toScheme B S hS).map (yoneda.preimage (eV.hom ≫ g.hom ≫ eU.inv))`, which at
`eV = V.obj.reprW` and `eU = U.obj.reprW` is the morphism
`AlgebraicGeometry.Space.RepresentableConormalSheafComparison` is stated against; that
instantiation is
`AlgebraicGeometry.Space.exists_schemeThickening_conormalSheafIso_of_isRepresentable`.

This is the identification recorded as missing by the section *What this leaves owed* of
`StacksFrontier/AlgebraicGeometry/Spaces/RepresentedClosedSubspace.lean` — "nor is the
identification of the space-level universal first-order thickening of a morphism of
representable spaces with the scheme-level one in the tree; clause (2) needs that too" — and by
item 2 of the carry note of `ConormalShortExact.lean`, in the directory
`StacksFrontier/AlgebraicGeometry/Spaces/Morphisms/PseudoCoherent/LocalCompleteIntersection/`.

## Main results

* `AlgebraicGeometry.Space.IsUniversalFirstOrderThickening.ofBaseIso`: being a universal
  first-order thickening is carried along an isomorphism of the base algebraic space.  This is
  the space-level counterpart of
  `Stacks.Thickenings.IsUniversalFirstOrderThickening.ofAmbientIso`, which moves the *ambient*
  space, and it is what lets a thickening of a representable target be read over the representing
  object of the site.
* `AlgebraicGeometry.Space.exists_schemeThickening_of_universalFirstOrderThickening`: **the
  thickening identification.**  A space-level universal first-order thickening of a morphism of
  representable algebraic spaces is, up to an isomorphism of its ambient presheaf with a
  representable one, the Yoneda image of a scheme-level universal first-order thickening of the
  underlying morphism of schemes.  The isomorphism carries `yoneda.map i` to the inclusion of the
  smaller space and carries the structure morphism of the thickening to `yoneda.map p`, so it is
  an isomorphism of thickenings over the base and not merely of ambient spaces.
* `AlgebraicGeometry.Space.nonempty_conormalSheafIsoRepresented`: given that identification, the
  conormal sheaf of Stacks 0607 of the space-level thickening is the conormal module of
  Stacks 04CN of the closed subspace `Subfunctor.range (yoneda.map i)` of `yoneda.obj W`, pulled
  back along the identification of the source with it.
* `AlgebraicGeometry.Space.exists_schemeThickening_conormalSheafIso` and
  `AlgebraicGeometry.Space.exists_schemeThickening_conormalSheafIso_of_isRepresentable`: the two
  combined, the second at the representable presentation `Functor.reprW`.

## Implementation notes

**Why the ambient space is representable at all.**  Stacks 05ZR, which would make a thickening of
a scheme a scheme, is not available in this development; the implementation notes of the module
`Conormal` (in
`StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PseudoCoherent.LocalCompleteIntersection`)
record that, and it is why the étale chart used there is taken on the ambient space of the
thickening and pulled back rather than extended across it.  The route here does not need 05ZR:
the scheme-level universal first-order thickening of the underlying morphism of schemes exists by
Stacks 04F3, its ambient is bounded by the big site's size cutoff, so
`Stacks.Spaces.UniversalThickening.exists_site_isUniversalFirstOrderThickening` presents it by
morphisms of the site, and
`AlgebraicGeometry.Space.isUniversalFirstOrderThickening_range_yoneda_map` makes its Yoneda image
a space-level universal first-order thickening of the *same* morphism.  Space-level uniqueness,
`AlgebraicGeometry.Space.IsUniversalFirstOrderThickening.exists_ambientIso`, then identifies the
given thickening with it.  This is the same device as the one used for the converse implication in
`StacksFrontier/AlgebraicGeometry/Spaces/Thickenings/UniversalRepresentableConverse.lean`, run here
to produce the isomorphism rather than to transport a property along it.  Space-level uniqueness
compares two thickenings over *one* base, which is why
`AlgebraicGeometry.Space.IsUniversalFirstOrderThickening.ofBaseIso` is proved first: the given
thickening lies over `U` and the represented one over `yoneda.obj U₀`.

**Why the source and target are presented by isomorphisms rather than taken to be Yoneda
presheaves.**  A representable algebraic space of this development is one carrying an isomorphism
with a Yoneda presheaf, not one that is a Yoneda presheaf; `Functor.reprW` is that isomorphism.
Everything below is therefore stated with the two presentations as arguments, and the composite
`eV.inv ≫ Subfunctor.toRange (yoneda.map i)` — an isomorphism of `V` with the closed subspace —
is what plays the role the identification of the source with the smaller space plays for a
thickening of a Yoneda presheaf.

**Why the conormal step goes through an abstract transport.**  The conormal sheaf is an inverse
image of a conormal module along the identification of the source with the smaller space, and what
the identification above provides is the conormal module of a *different* closed subspace, of the
representable ambient space.  The two are compared by Stacks 060D (3),
`AlgebraicGeometry.Space.conormalModuleEtaleLocalizationIso`, at the isomorphism of ambient
spaces — an isomorphism being étale, and a square whose two horizontal arrows are isomorphisms
being a pullback.  Composing that with the comparison of inverse images
`AlgebraicGeometry.Space.modulePullbackCompIso` is where the heartbeat budget goes if it is done
in place: the objects involved are modules on small étale sites and `whnf` on them is expensive.
`AlgebraicGeometry.Space.factoredModulePullbackObjIso` does the composition once, for arbitrary
algebraic spaces and an arbitrary factorisation, with the comparison of the two conormal objects
taken as an uninspected hypothesis; instantiating it is then unification of a statement and costs
nothing.  For the same reason the conormal statement is proved first in the written-out spelling
of `AlgebraicGeometry.Space.conormalSheaf` and only then transported to the folded one by
`AlgebraicGeometry.Space.conormalSheaf_eq`.

## What this leaves owed

The comparison `AlgebraicGeometry.Space.RepresentableConormalSheafComparison` itself is proved,
by another route, as `AlgebraicGeometry.Space.representableConormalSheafComparison`, from
`AlgebraicGeometry.Space.isFiniteLocallyFreeOnSite_conormalSheaf_of_scheme` of
`StacksFrontier/AlgebraicGeometry/Spaces/Thickenings/RepresentableConormal.lean`; what follows is
what this file's own route would still need.

This identifies the space-level thickening with the scheme-level one and reads the conormal sheaf
at a *represented* closed subspace of a *representable* algebraic space.  It is not clause (2) of
`AlgebraicGeometry.Space.RepresentableConormalSheafComparison`.  What remains between the two is
the comparison of `AlgebraicGeometry.Space.conormalModule` of a represented closed subspace with
`Stacks.Thickenings.universalConormalSheaf` of the representing closed immersion of schemes.  Its
inputs are all available, and the assembly of them is what is not done here:

* the assembled structure-projection square
  `AlgebraicGeometry.Space.representedAssociatedModule_structureProjection_square`, which carries
  the Zariski structure projection of a morphism of schemes to
  `AlgebraicGeometry.Space.structureProjectionOfHom` of the represented morphism;
* the dictionary `AlgebraicGeometry.Space.subspaceInclusion_eq_representedSpaceMap` of
  `StacksFrontier/AlgebraicGeometry/Spaces/RepresentedClosedSubspace.lean`, which presents the
  inclusion of a closed subspace of a representable algebraic space as a represented morphism up
  to an isomorphism of its source, together with
  `AlgebraicGeometry.Space.structureProjectionOfHom_comp` and
  `AlgebraicGeometry.Space.isIso_structureProjectionOfHom`, which say how the structure
  projection reacts to that isomorphism;
* the two kernel presentations `AlgebraicGeometry.Space.definingIdealSheafIsoKernel` and
  `Stacks.AlgebraicGeometry.RegularIdealSheaf.definingIdealOfHomIso`, which put the two defining
  ideal sheaves in the same shape, with the sections comparison
  `AlgebraicGeometry.Space.definingIdealOfHom_obj_selfChart_eq_openChartIdeal` beside them;
* the pullback comparison
  `AlgebraicGeometry.Space.representedQuasicoherentSchemePullbackIso`, which carries the
  identification of the ideal sheaves to one of the conormal objects, and — for the conormal
  *maps* rather than the objects — the reduction
  `AlgebraicGeometry.Space.conormalMap_comparison_square`.

Nothing of the scheme-level category of modules is named here, and no statement below mentions a
sheaf of modules on a scheme.

## References

* [Stacks Project, Tag 04CN](https://stacks.math.columbia.edu/tag/04CN)
* [Stacks Project, Tag 04F3](https://stacks.math.columbia.edu/tag/04F3)
* [Stacks Project, Tag 049T](https://stacks.math.columbia.edu/tag/049T)
* [Stacks Project, Tag 0602](https://stacks.math.columbia.edu/tag/0602)
* [Stacks Project, Tag 0607](https://stacks.math.columbia.edu/tag/0607)
* [Stacks Project, Tag 060D](https://stacks.math.columbia.edu/tag/060D)
* [Stacks Project, Tag 06CB](https://stacks.math.columbia.edu/tag/06CB)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

/-! ### Two readings of an isomorphism inverted on one side -/

/-- Precomposing with an isomorphism `r` the isomorphism `(asIso r).symm ≪≫ a` out of its target
gives back `a`, read with a further arrow `k` appended.

Both this and `AlgebraicGeometry.Space.comp_asIso_symm_trans_hom` are recorded because a goal in
which the folded `(asIso r).symm.trans a` meets the written-out `inv r ≫ a.hom` is not matched by
`rw`, the two differing by the spelling of the source of `a`; these abstract statements are
matched by unification instead. -/
private theorem asIso_symm_trans_hom_assoc {C : Type*} [Category C] {A R T W : C}
    (r : A ⟶ R) [IsIso r] (a : A ≅ T) (k : T ⟶ W) :
    r ≫ ((asIso r).symm.trans a).hom ≫ k = a.hom ≫ k := by
  rw [Iso.trans_hom, Iso.symm_hom, asIso_inv, Category.assoc, IsIso.hom_inv_id_assoc]

/-- `AlgebraicGeometry.Space.asIso_symm_trans_hom_assoc` with no arrow appended: the
factorisation of `a` through `r`. -/
private theorem comp_asIso_symm_trans_hom {C : Type*} [Category C] {A R T : C}
    (r : A ⟶ R) [IsIso r] (a : A ≅ T) :
    r ≫ ((asIso r).symm.trans a).hom = a.hom := by
  rw [Iso.trans_hom, Iso.symm_hom, asIso_inv, IsIso.hom_inv_id_assoc]

/-- Comparing two arrows out of a subobject `R` of `M` and out of its parametrisation `t` by `Y`,
where `eV.inv ≫ t` is invertible. -/
private theorem range_comp_eq_iff {C : Type*} [Category C] {Y A R M T X : C} (eV : Y ≅ A)
    (t : Y ⟶ R) (ι : R ⟶ M) {f : Y ⟶ M} (ht : t ≫ ι = f) [IsIso (eV.inv ≫ t)] (sI : A ≅ T)
    (k : M ⟶ X) (m : T ⟶ X) :
    ι ≫ k = ((asIso (eV.inv ≫ t)).symm.trans sI).hom ≫ m ↔ f ≫ k = eV.hom ≫ sI.hom ≫ m := by
  subst ht
  rw [← cancel_epi (eV.inv ≫ t), asIso_symm_trans_hom_assoc, Category.assoc, Category.assoc,
    eV.inv_comp_eq]

/-! ### Transporting a module comparison along a factorisation of the inverse image -/

/-- **The inverse image along a composite, read through a comparison at the middle term.**  Let
`w = r ≫ c` be a factorisation of a morphism of algebraic spaces over `S`, let `M` be a module on
the target, and let the inverse image of `M` along `c` be identified with a module `N` on the
middle space.  Then the inverse image of `M` along `w` is the inverse image of `N` along `r`.

The comparison `hN` is a hypothesis and is never inspected, which is the point of stating this for
arbitrary algebraic spaces: the objects at the corners are modules on small étale sites, and the
composition comparison `AlgebraicGeometry.Space.modulePullbackCompIso` cannot be pasted onto them
in place within the heartbeat budget.  Here there is nothing to unfold, and the concrete statement
below is obtained by instantiation. -/
private noncomputable def factoredModulePullbackObjIso
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {A R T : AlgebraicSpaces B S hS} {w : A ⟶ T} {r : A ⟶ R} {c : R ⟶ T}
    (h : r ≫ c = w) (M : Modules.{u, u} B S hS T.obj T.property)
    {N : Modules.{u, u} B S hS R.obj R.property}
    (hN : (modulePullback B S hS c).obj M ≅ N) :
    (modulePullback B S hS w).obj M ≅ (modulePullback B S hS r).obj N :=
  eqToIso (congrArg (fun k => (modulePullback B S hS k).obj M) h.symm) ≪≫
    ((modulePullbackCompIso B S hS r c).app M).symm ≪≫
    (modulePullback B S hS r).mapIso hN

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Changing the base of a universal first-order thickening along an isomorphism -/

/-- **Being a universal first-order thickening is carried along an isomorphism of the base.**  Let
`Z ⊂ Z'` be a universal first-order thickening of `Z` over `X` with structure morphism
`p : Z' ⟶ X`, and let `bh : X ⟶ X₁` be an isomorphism of algebraic spaces over `S`, given by its
two underlying morphisms of presheaves and their two identities.  Then `Z ⊂ Z'` is a universal
first-order thickening over `X₁` with structure morphism any `p₁` whose underlying morphism is
`p` followed by `bh`.

The isomorphism is given as a pair of morphisms rather than as a
`CategoryTheory.Iso` of algebraic spaces so that every arrow in the statement, and hence in the
proof, is a morphism of presheaves: the two spellings of the underlying presheaf of an object of
the full subcategory of algebraic spaces agree at default transparency but not at the transparency
at which `rw` matches.

This is the space-level counterpart of
`Stacks.Thickenings.IsUniversalFirstOrderThickening.ofAmbientIso`, which moves the ambient scheme;
no condition on `Z ⊂ Z'` is needed here, the base playing no part in the first-order condition. -/
theorem IsUniversalFirstOrderThickening.ofBaseIso
    {X X₁ Z' : AlgebraicSpaces B S hS} {Z : Subfunctor Z'.obj} {p : Z' ⟶ X} {p₁ : Z' ⟶ X₁}
    (bh : X.obj ⟶ X₁.obj) (bi : X₁.obj ⟶ X.obj)
    (hbi : bh ≫ bi = 𝟙 X.obj) (hib : bi ≫ bh = 𝟙 X₁.obj)
    (hp : p.hom ≫ bh = p₁.hom)
    (hZ : IsUniversalFirstOrderThickening B S hS Z p) :
    IsUniversalFirstOrderThickening B S hS Z p₁ where
  firstOrder := hZ.firstOrder
  existsUnique_lift := by
    intro T' T hT a β hβ
    obtain ⟨c, hc, hcu⟩ := hZ.existsUnique_lift T hT a (β ≫ bi) (by
      rw [← Category.assoc, hβ, ← hp, Category.assoc, Category.assoc, Category.assoc, hbi,
        Category.comp_id])
    refine ⟨c, ⟨hc.1, ?_⟩, fun d hd => hcu d ⟨hd.1, ?_⟩⟩
    · rw [← hp, ← Category.assoc, hc.2, Category.assoc, hib, Category.comp_id]
    · rw [← hd.2, ← hp, Category.assoc, Category.assoc, hbi, Category.comp_id]

/-! ### The thickening identification -/

/-- **A space-level universal first-order thickening of a morphism of representable algebraic
spaces is the Yoneda image of a scheme-level one.**  Let `g : V ⟶ U` be a morphism of algebraic
spaces over `S`, let `eV : yoneda.obj V₀ ≅ V.obj` and `eU : yoneda.obj U₀ ≅ U.obj` present the
source and the target by objects of the big fppf category over `S`, and let `s` be a universal
first-order thickening of `g` in the sense of Stacks 0607.  Then there are an object `W` of the
site and morphisms `i : V₀ ⟶ W`, `p : W ⟶ U₀` composing to the morphism of the site that
`eV`, `eU` make out of `g`, such that

* `V₀ ⟶ W` is a square-zero closed immersion of schemes and `V₀ ⊂ W` is a universal first-order
  thickening of `V₀` over `U₀` at the level of schemes, in the sense of Stacks 04F3;
* the ambient presheaf of `s` is isomorphic to `yoneda.obj W`, by an isomorphism carrying
  `yoneda.map i` to the inclusion of the smaller space of `s` — read through `eV` and the
  identification `s.sourceIso` of the source with that smaller space — and carrying the structure
  morphism of `s`, read over `yoneda.obj U₀` through `eU`, to `yoneda.map p`.

In particular the ambient algebraic space of `s` is representable, which Stacks 05ZR would give
and which this development does not have; see the implementation notes for the route taken
instead.  The two compatibilities say that the isomorphism is one of thickenings of `V₀` over
`U₀`, so the scheme-level datum below is a presentation of `s` itself and not merely of some
thickening of the same morphism. -/
theorem exists_schemeThickening_of_universalFirstOrderThickening
    {V U : AlgebraicSpaces B S hS} {V₀ U₀ : BigFppfOver B S hS}
    (eV : yoneda.obj V₀ ≅ V.obj) (eU : yoneda.obj U₀ ≅ U.obj)
    {g : V ⟶ U} (s : UniversalFirstOrderThickening B S hS g) :
    ∃ (W : BigFppfOver B S hS) (i : V₀ ⟶ W) (p : W ⟶ U₀),
      i ≫ p = yoneda.preimage (eV.hom ≫ g.hom ≫ eU.inv) ∧
      Stacks.Thickenings.IsFirstOrderThickening ((BigFppfOver.toScheme B S hS).map i) ∧
      Stacks.Thickenings.IsUniversalFirstOrderThickening
        ((BigFppfOver.toScheme B S hS).map (yoneda.preimage (eV.hom ≫ g.hom ≫ eU.inv)))
        ((BigFppfOver.toScheme B S hS).map i)
        ((BigFppfOver.toScheme B S hS).map p) ∧
      ∃ e : yoneda.obj W ≅ s.ambient.obj,
        yoneda.map i ≫ e.hom = eV.hom ≫ s.sourceIso.hom ≫ s.sub.ι ∧
        e.hom ≫ s.toBase.hom ≫ eU.inv = yoneda.map p := by
  classical
  set q : V₀ ⟶ U₀ := yoneda.preimage (eV.hom ≫ g.hom ≫ eU.inv)
  have hq : yoneda.map q = eV.hom ≫ g.hom ≫ eU.inv := yoneda.map_preimage _
  -- Formal unramifiedness of `g` passes to the morphism of schemes, Stacks 049T.
  have hFUy : FormallyUnramified (yoneda.map q) := by
    rw [hq]
    have : Mono eV.hom := IsIso.mono_of_iso _
    have : Mono eU.inv := IsIso.mono_of_iso _
    exact formallyUnramified_comp _ _ (formallyUnramified_of_mono eV.hom)
      (formallyUnramified_comp _ _ s.formallyUnramified
        (formallyUnramified_of_mono eU.inv))
  have hFU : _root_.AlgebraicGeometry.FormallyUnramified
      ((BigFppfOver.toScheme B S hS).map q) :=
    (formallyUnramified_yoneda_map_iff_formallyUnramified_map B S hS q).1 hFUy
  -- The scheme-level universal first-order thickening of Stacks 04F3, presented by the site.
  obtain ⟨t⟩ := Stacks.Thickenings.nonempty_universalFirstOrderThickening
    ((BigFppfOver.toScheme B S hS).map q)
  obtain ⟨W, j, p, hcomp, -, -, -, hfirst, huniv, huS⟩ :=
    Stacks.Spaces.UniversalThickening.exists_site_isUniversalFirstOrderThickening B S hS q t
  have : Mono (yoneda.map j) := mono_of_isClosedImmersion B S hS (yoneda.map j)
    ((BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS
      (@_root_.AlgebraicGeometry.IsClosedImmersion.{u}) j).2 hfirst.1)
  have hIsoRho : IsIso (eV.inv ≫ Subfunctor.toRange (yoneda.map j)) := inferInstance
  -- The structure morphism of `s`, read over the representing object of the target.
  have hbase : IsUniversalFirstOrderThickening B S hS s.sub
      (ObjectProperty.homMk (s.toBase.hom ≫ eU.inv) : s.ambient ⟶ schemeSpace U₀) :=
    IsUniversalFirstOrderThickening.ofBaseIso B S hS eU.inv eU.hom eU.inv_hom_id eU.hom_inv_id
      rfl s.isUniversal
  -- The two thickenings lie over the same base and agree on the smaller space.
  have he : (Subfunctor.range (yoneda.map j)).ι ≫ (schemeSpaceMap p).hom
      = ((asIso (eV.inv ≫ Subfunctor.toRange (yoneda.map j))).symm.trans s.sourceIso).hom ≫
        s.sub.ι ≫ (ObjectProperty.homMk (s.toBase.hom ≫ eU.inv) :
          s.ambient ⟶ schemeSpace U₀).hom :=
    (range_comp_eq_iff eV _ _ (Subfunctor.toRange_ι (yoneda.map j)) s.sourceIso _ _).2 (by
      change yoneda.map j ≫ yoneda.map p = _ ≫ _ ≫ _ ≫ s.toBase.hom ≫ eU.inv
      rw [← yoneda.map_comp, hcomp, hq]
      simp only [← Category.assoc, s.sourceIso_ι_toBase])
  -- Space-level uniqueness of the universal first-order thickening, Stacks 0602.
  obtain ⟨e, hei, heb⟩ := IsUniversalFirstOrderThickening.exists_ambientIso B S hS
    (X := schemeSpace U₀) (Y' := s.ambient) (Z' := schemeSpace W)
    (Y := s.sub) (Z := Subfunctor.range (yoneda.map j))
    (p := (ObjectProperty.homMk (s.toBase.hom ≫ eU.inv) : s.ambient ⟶ schemeSpace U₀))
    (q := schemeSpaceMap p) hbase huniv
    ((asIso (eV.inv ≫ Subfunctor.toRange (yoneda.map j))).symm.trans s.sourceIso) he
  refine ⟨W, j, p, hcomp, hfirst, by rwa [← hcomp], e, ?_, heb⟩
  exact (range_comp_eq_iff eV _ _ (Subfunctor.toRange_ι (yoneda.map j)) s.sourceIso _ _).1 hei

/-! ### The conormal sheaf at the represented thickening -/

/-- `AlgebraicGeometry.Space.nonempty_conormalSheafIsoRepresented` in the written-out spelling of
`AlgebraicGeometry.Space.conormalSheaf`.  The folded and the written-out spellings do not meet in
one goal within the heartbeat budget, so the content is proved here and transported there. -/
private theorem nonempty_modulePullback_conormalModule_iso
    {V U : AlgebraicSpaces B S hS} {V₀ W : BigFppfOver B S hS} {i : V₀ ⟶ W}
    (eV : yoneda.obj V₀ ≅ V.obj)
    {g : V ⟶ U} (s : UniversalFirstOrderThickening B S hS g)
    (hci : _root_.AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map i))
    (hcs : IsClosedSubspace B S hS (Subfunctor.range (yoneda.map i)))
    (e : yoneda.obj W ≅ s.ambient.obj)
    (hcompat : yoneda.map i ≫ e.hom = eV.hom ≫ s.sourceIso.hom ≫ s.sub.ι) :
    Nonempty ((modulePullback B S hS s.sourceInclusion).obj
        (conormalModule B S hS s.ambient s.closedSub) ≅
      (modulePullback B S hS (ObjectProperty.homMk
          (eV.inv ≫ Subfunctor.toRange (yoneda.map i)) :
          V ⟶
            (⟨(Subfunctor.range (yoneda.map i)).toFunctor, hcs.1⟩ : AlgebraicSpaces B S hS))).obj
        (conormalModule B S hS (schemeSpace W)
          ⟨Subfunctor.range (yoneda.map i), hcs⟩)) := by
  have : Mono (yoneda.map i) := mono_of_isClosedImmersion B S hS (yoneda.map i)
    ((BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS
      (@_root_.AlgebraicGeometry.IsClosedImmersion.{u}) i).2 hci)
  have hIsoRho : IsIso (eV.inv ≫ Subfunctor.toRange (yoneda.map i)) := inferInstance
  -- The isomorphism of ambient spaces is cartesian over the inclusion of the smaller space.
  have hsq : IsPullback
      ((asIso (eV.inv ≫ Subfunctor.toRange (yoneda.map i))).symm.trans s.sourceIso).hom
      (Subfunctor.range (yoneda.map i)).ι s.sub.ι e.hom :=
    IsPullback.of_horiz_isIso ⟨((range_comp_eq_iff eV _ _ (Subfunctor.toRange_ι (yoneda.map i))
      s.sourceIso _ _).2 hcompat).symm⟩
  -- Stacks 060D (3) at that isomorphism, which is étale.
  have hloc := conormalModuleEtaleLocalizationIso B S hS s.closedSub
    (ObjectProperty.homMk e.hom : schemeSpace W ⟶ s.ambient)
    (isEtale_of_isIso B S hS e.hom)
    (Subfunctor.range (yoneda.map i)) hcs
    ((asIso (eV.inv ≫ Subfunctor.toRange (yoneda.map i))).symm.trans s.sourceIso).hom hsq
  -- The identification of the source with the smaller space factors through the range.
  have hmor : (ObjectProperty.homMk (eV.inv ≫ Subfunctor.toRange (yoneda.map i)) :
        V ⟶ (⟨(Subfunctor.range (yoneda.map i)).toFunctor, hcs.1⟩ : AlgebraicSpaces B S hS)) ≫
      (ObjectProperty.homMk
          ((asIso (eV.inv ≫ Subfunctor.toRange (yoneda.map i))).symm.trans s.sourceIso).hom :
        (⟨(Subfunctor.range (yoneda.map i)).toFunctor, hcs.1⟩ : AlgebraicSpaces B S hS) ⟶
          s.subSpace) = s.sourceInclusion := by
    apply ObjectProperty.hom_ext
    exact comp_asIso_symm_trans_hom (eV.inv ≫ Subfunctor.toRange (yoneda.map i)) s.sourceIso
  exact ⟨factoredModulePullbackObjIso B S hS hmor
    (conormalModule B S hS s.ambient s.closedSub) hloc⟩

/-- **The conormal sheaf of a space-level universal first-order thickening of a morphism of
representable spaces, read at the represented thickening.**  Let `i : V₀ ⟶ W` be a closed
immersion of the site whose Yoneda image presents the ambient space of the thickening `s`,
compatibly with the presentation `eV` of the source and the identification of the source with the
smaller space.  Then the conormal sheaf `𝒞_{V/U}` of Stacks 0607 of `s` is the conormal module of
Stacks 04CN of the closed subspace `Subfunctor.range (yoneda.map i)` of the representable
algebraic space `yoneda.obj W`, pulled back along the identification of `V` with that subspace.

Both sides are modules on the small étale site of `V`; nothing about the Zariski site of the
representing scheme, or about a sheaf of modules on a scheme, enters.  What is still owed between
this and clause (2) of `AlgebraicGeometry.Space.RepresentableConormalSheafComparison` is recorded
in the section *What this leaves owed* of this file. -/
theorem nonempty_conormalSheafIsoRepresented
    {V U : AlgebraicSpaces B S hS} {V₀ W : BigFppfOver B S hS} {i : V₀ ⟶ W}
    (eV : yoneda.obj V₀ ≅ V.obj)
    {g : V ⟶ U} (s : UniversalFirstOrderThickening B S hS g)
    (hci : _root_.AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map i))
    (hcs : IsClosedSubspace B S hS (Subfunctor.range (yoneda.map i)))
    (e : yoneda.obj W ≅ s.ambient.obj)
    (hcompat : yoneda.map i ≫ e.hom = eV.hom ≫ s.sourceIso.hom ≫ s.sub.ι) :
    Nonempty (conormalSheaf B S hS s ≅
      (modulePullback B S hS (ObjectProperty.homMk
          (eV.inv ≫ Subfunctor.toRange (yoneda.map i)) :
          V ⟶
            (⟨(Subfunctor.range (yoneda.map i)).toFunctor, hcs.1⟩ : AlgebraicSpaces B S hS))).obj
        (conormalModule B S hS (schemeSpace W)
          ⟨Subfunctor.range (yoneda.map i), hcs⟩)) := by
  rw [conormalSheaf_eq]
  exact nonempty_modulePullback_conormalModule_iso B S hS eV s hci hcs e hcompat

/-- **The identification, with the scheme-level thickening and the conormal sheaf together.**  For
a morphism `g : V ⟶ U` of algebraic spaces over `S` whose source and target are presented by
objects `V₀`, `U₀` of the big fppf category over `S`, and a space-level universal first-order
thickening `s` of `g`, there are an object `W` of the site and morphisms `i : V₀ ⟶ W`,
`p : W ⟶ U₀` composing to the morphism of the site that the two presentations make out of `g`,
which make `V₀ ⊂ W` a scheme-level universal first-order thickening of `V₀` over `U₀`
(Stacks 04F3) and for which the conormal sheaf of `s` is the conormal module of the closed
subspace `Subfunctor.range (yoneda.map i)` of `yoneda.obj W`, pulled back along the identification
of `V` with it.

This is `AlgebraicGeometry.Space.exists_schemeThickening_of_universalFirstOrderThickening`
followed by `AlgebraicGeometry.Space.nonempty_conormalSheafIsoRepresented`; the closed subspace
datum is bound in the statement because the type of the comparison depends on it. -/
theorem exists_schemeThickening_conormalSheafIso
    {V U : AlgebraicSpaces B S hS} {V₀ U₀ : BigFppfOver B S hS}
    (eV : yoneda.obj V₀ ≅ V.obj) (eU : yoneda.obj U₀ ≅ U.obj)
    {g : V ⟶ U} (s : UniversalFirstOrderThickening B S hS g) :
    ∃ (W : BigFppfOver B S hS) (i : V₀ ⟶ W) (p : W ⟶ U₀)
        (hcs : IsClosedSubspace B S hS (Subfunctor.range (yoneda.map i))),
      i ≫ p = yoneda.preimage (eV.hom ≫ g.hom ≫ eU.inv) ∧
      Stacks.Thickenings.IsUniversalFirstOrderThickening
        ((BigFppfOver.toScheme B S hS).map (yoneda.preimage (eV.hom ≫ g.hom ≫ eU.inv)))
        ((BigFppfOver.toScheme B S hS).map i)
        ((BigFppfOver.toScheme B S hS).map p) ∧
      Nonempty (conormalSheaf B S hS s ≅
        (modulePullback B S hS (ObjectProperty.homMk
            (eV.inv ≫ Subfunctor.toRange (yoneda.map i)) :
            V ⟶
              (⟨(Subfunctor.range (yoneda.map i)).toFunctor, hcs.1⟩ :
                AlgebraicSpaces B S hS))).obj
          (conormalModule B S hS (schemeSpace W)
            ⟨Subfunctor.range (yoneda.map i), hcs⟩)) := by
  obtain ⟨W, j, p, hcomp, hfirst, huS, e, hcompat, -⟩ :=
    exists_schemeThickening_of_universalFirstOrderThickening B S hS eV eU s
  have hcs : IsClosedSubspace B S hS (Subfunctor.range (yoneda.map j)) :=
    (IsNthOrderThickening.isThickening B S hS
      (isFirstOrderThickening_range_yoneda_map B S hS j ⟨hfirst.1, hfirst.2⟩)).1
  exact ⟨W, j, p, hcs, hcomp, huS,
    nonempty_conormalSheafIsoRepresented B S hS eV s hfirst.1 hcs e hcompat⟩

/-- `AlgebraicGeometry.Space.exists_schemeThickening_conormalSheafIso` at the canonical
presentation of a representable algebraic space, `CategoryTheory.Functor.reprW`.

The morphism of schemes it is stated against is the one
`AlgebraicGeometry.Space.RepresentableConormalSheafComparison` is stated against, so this is the
form clause (2) of Stacks 06CB consumes. -/
theorem exists_schemeThickening_conormalSheafIso_of_isRepresentable
    {V U : AlgebraicSpaces B S hS} [V.obj.IsRepresentable] [U.obj.IsRepresentable]
    {g : V ⟶ U} (s : UniversalFirstOrderThickening B S hS g) :
    ∃ (W : BigFppfOver B S hS) (i : V.obj.reprX ⟶ W) (p : W ⟶ U.obj.reprX)
        (hcs : IsClosedSubspace B S hS (Subfunctor.range (yoneda.map i))),
      i ≫ p = yoneda.preimage (V.obj.reprW.hom ≫ g.hom ≫ U.obj.reprW.inv) ∧
      Stacks.Thickenings.IsUniversalFirstOrderThickening
        ((BigFppfOver.toScheme B S hS).map
          (yoneda.preimage (V.obj.reprW.hom ≫ g.hom ≫ U.obj.reprW.inv)))
        ((BigFppfOver.toScheme B S hS).map i)
        ((BigFppfOver.toScheme B S hS).map p) ∧
      Nonempty (conormalSheaf B S hS s ≅
        (modulePullback B S hS (ObjectProperty.homMk
            (V.obj.reprW.inv ≫ Subfunctor.toRange (yoneda.map i)) :
            V ⟶
              (⟨(Subfunctor.range (yoneda.map i)).toFunctor, hcs.1⟩ :
                AlgebraicSpaces B S hS))).obj
          (conormalModule B S hS (schemeSpace W)
            ⟨Subfunctor.range (yoneda.map i), hcs⟩)) :=
  exists_schemeThickening_conormalSheafIso B S hS V.obj.reprW U.obj.reprW s

end AlgebraicGeometry.Space

end
