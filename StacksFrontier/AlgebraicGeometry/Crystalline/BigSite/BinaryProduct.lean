module

public import StacksFrontier.AlgebraicGeometry.Crystalline.BigSite.BinaryProductGlue
public import StacksFrontier.AlgebraicGeometry.Crystalline.BigSite.BinaryProductLocal
public import StacksFrontier.AlgebraicGeometry.Crystalline.BigSite.BinaryProductPatch
public import StacksFrontier.AlgebraicGeometry.Crystalline.BigSite.BinaryProductRestrict

/-!
# Products of pairs in the big crystalline category

Fix a global crystalline situation `(p, (S, I, γ), X)` and two objects `A`, `B` of the big
crystalline category `CRIS(X/S)`.  This file assembles the product `A × B` from the five layers
that precede it.

The construction is the one of [Stacks, Tag 07I9] clause (1).  A *product patch* for the pair,
`Crystalline.GlobalCrystallineSituation.ProductPatch`, is a quadruple of affine opens — one of the
divided power base, one of `X`, one in each of the two ambient schemes — adapted to each other.
Over a patch the whole situation is affine, so the affine model of products applies and `A` and `B`
restricted to the patch have a product; this is
`Crystalline.GlobalCrystallineSituation.ProductPatch.hasBinaryProduct_leftObj_rightObj`, obtained
from `Crystalline.GlobalCrystallineSituation.hasBinaryProduct_of_affine_localization` and the
affine case `Crystalline.GlobalCrystallineSituation.AffineBinaryProducts`.

The patches are ordered by refinement and the local products form a functor on that preorder.  The
transition map attached to a refinement `P ≤ Q` is, up to a canonical isomorphism, the structure
morphism of a restriction of the `Q`-product
(`Crystalline.GlobalCrystallineSituation.ProductPatch.transIso`); since the structure morphism of a
restriction is an induced open immersion on ambient schemes and an open immersion on thickened
schemes, the diagram of local products is a
`Crystalline.GlobalCrystallineSituation.ThickeningPresentation`, and the gluing of the previous
layer produces a single object `C` with two morphisms to `A` and to `B`.

That `C` is a product is the universal property: uniqueness of a morphism into `C` is Zariski-local
on the source and reduces, chart by chart, to the universal property of a local product; existence
needs the compatible family of local lifts to be glued, which is the one input not yet available
(see below).

## Main definitions

* `Crystalline.GlobalCrystallineSituation.Thickening.restrictOpenIncl` — the morphism `T|_U ⟶ T|_V`
  attached to an inclusion `U ≤ V` of opens of the ambient scheme of `T`.
* `Crystalline.GlobalCrystallineSituation.Thickening.restrictOpenRestrictIso` — a restriction of a
  restriction is a restriction.
* `Crystalline.GlobalCrystallineSituation.ZariskiGluing` — the Zariski gluing property for
  morphisms out of an object of `CRIS(X/S)`, carried as a hypothesis throughout.
* `Crystalline.GlobalCrystallineSituation.AffineBinaryProducts` — binary products in an affine
  situation, carried as a hypothesis throughout.
* `Crystalline.GlobalCrystallineSituation.ProductPatch.prodObj` — the product of the two
  restrictions of `A` and `B` to a patch, with projections `.fstHom` and `.sndHom`.
* `Crystalline.GlobalCrystallineSituation.ProductPatch.functor` — the diagram of local products
  over the preorder of patches.
* `Crystalline.GlobalCrystallineSituation.ProductPatch.presentation` — that diagram as a
  `Crystalline.GlobalCrystallineSituation.ThickeningPresentation`.
* `Crystalline.GlobalCrystallineSituation.ProductPatch.gluedProd`, `.gluedFst` and `.gluedSnd` —
  the glued object and its two projections.

## Main results

* `Crystalline.GlobalCrystallineSituation.Thickening.hom_ext_of_restrictOpen_iSup` and
  `.restrictOpen_hom_ext_of_cover` — a morphism out of an object of `CRIS(X/S)`, or out of a
  restriction of one, is determined by its restrictions to an open cover of the ambient scheme.
* `Crystalline.DividedPowerScheme.isInducedOpen_restrictι` — the morphism from a restriction of a
  divided power scheme to an open subscheme is an induced open immersion.
* `Crystalline.GlobalCrystallineSituation.ProductPatch.gluedProd_hom_ext` — a morphism into the
  glued object is determined by its composites with the two projections.
* **`Crystalline.GlobalCrystallineSituation.hasBinaryProduct_of_glue`** and
  **`Crystalline.GlobalCrystallineSituation.hasBinaryProducts_thickening_of_glue`** — two objects
  of `CRIS(X/S)`, and hence any two, have a binary product, granted
  `Crystalline.GlobalCrystallineSituation.ZariskiGluing` and
  `Crystalline.GlobalCrystallineSituation.AffineBinaryProducts`.

## What is and is not proved

No tag attribute is placed in this file.

Everything above is proved outright except for two inputs, which are carried as explicit
hypotheses of the two main results and nowhere assumed silently.

The first is `Crystalline.GlobalCrystallineSituation.ZariskiGluing`: that a family of morphisms out
of the restrictions of an object `T` of `CRIS(X/S)` to the members of an open cover of its ambient
scheme, agreeing on the pairwise intersections, is the family of restrictions of a single morphism
out of `T`.  Only existence of the glued morphism is assumed; its uniqueness is proved here
(`Crystalline.GlobalCrystallineSituation.Thickening.hom_ext_of_restrictOpen_iSup`), as is the
compatibility of the family that the construction feeds to it.  That hypothesis is Zariski descent
for morphisms of `CRIS(X/S)`, and it will be discharged by the descent layer
`StacksFrontier/AlgebraicGeometry/Crystalline/BigSite/BinaryProductDescent.lean`, whose `glueHom`
glues the maps on ambient divided power schemes by
`Crystalline.DividedPowerScheme.glueRestrict` and the maps on thickened schemes over the preimage
cover.

The second is `Crystalline.GlobalCrystallineSituation.AffineBinaryProducts`, the affine case of
[Stacks, Tag 07I9]: two objects of `CRIS(X/S)` with affine thickened and ambient schemes, over an
affine situation on which the fixed prime is nilpotent, have a binary product.  This is *proved*,
as `Crystalline.GlobalCrystallineSituation.hasBinaryProduct_of_isAffine`, in
`StacksFrontier/AlgebraicGeometry/Crystalline/BigSite/BinaryProductAffine.lean`.

Both hypotheses are discharged, and the unconditional instance
`Crystalline.GlobalCrystallineSituation.instHasBinaryProductsThickening` stated, in
`StacksFrontier/AlgebraicGeometry/Crystalline/BigSite/BinaryProductInstance.lean`.  They are
hypotheses *here* so that this module states what the gluing argument needs, independently of how
the two inputs are obtained; a reader wanting the instance should go to that module.

Nothing in this module is claimed about limits of other shapes.  Fibre products are
`Crystalline.GlobalCrystallineSituation.instHasPullbacksThickening` of
`StacksFrontier/AlgebraicGeometry/Crystalline/BigSite/FibreProduct.lean`, and all nonempty finite
limits — clause (1) of [Stacks, Tag 07I9] in full — follow in `BinaryProductInstance.lean`.

## References

* [Stacks Project, Tag 07I9](https://stacks.math.columbia.edu/tag/07I9)
* [Stacks Project, Tag 07HN](https://stacks.math.columbia.edu/tag/07HN)
* [Stacks Project, Tag 07I6](https://stacks.math.columbia.edu/tag/07I6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped AlgebraicGeometry

universe u

namespace Crystalline

namespace DividedPowerScheme

/-- **The morphism from the restriction of a divided power scheme to an open subscheme is an
induced open immersion.**  Its underlying morphism of schemes is the open immersion of `W`, and the
square of closed fibres is Cartesian: the closed fibre of `X|_W` is the open `closedFiberι X ⁻¹ᵁ W`
of the closed fibre of `X`, by
`Crystalline.DividedPowerScheme.restrictClosedFiberIso_inv_closedFiberMap`, so the map of closed
fibres is an open immersion with exactly that image.  The criterion
`Crystalline.DividedPowerScheme.isInducedOpen_of_closedFiber_isPullback` then applies. -/
theorem isInducedOpen_restrictι (X : DividedPowerScheme.{u}) (W : X.scheme.Opens) :
    IsInducedOpen (X.restrictι W) := by
  have hmap : (restrictClosedFiberIso X W).hom ≫ (closedFiberι X ⁻¹ᵁ W).ι =
      closedFiberMap (X.restrictι W) := by
    rw [← restrictClosedFiberIso_inv_closedFiberMap X W, Iso.hom_inv_id_assoc]
  have hopen : IsOpenImmersion (closedFiberMap (X.restrictι W)) := by
    rw [← hmap]; infer_instance
  refine isInducedOpen_of_closedFiber_isPullback (X.restrictι W) ?_
  rw [← hmap]
  refine IsOpenImmersion.isPullback (closedFiberι (X.restrict W))
    ((restrictClosedFiberIso X W).hom ≫ (closedFiberι X ⁻¹ᵁ W).ι) (X.restrictι W).hom
    (closedFiberι X) ?_ ?_
  · rw [hmap]
    exact closedFiberMap_comp_closedFiberι (X.restrictι W)
  · change closedFiberι X ⁻¹ᵁ W.ι.opensRange = _
    rw [Scheme.Hom.opensRange_comp_of_isIso, Scheme.Opens.opensRange_ι,
      Scheme.Opens.opensRange_ι]

end DividedPowerScheme

namespace GlobalCrystallineSituation

namespace Thickening

variable {S : GlobalCrystallineSituation.{u}}

/-! ### Restrictions of an object to opens of its ambient scheme -/

/-- A composite of morphisms of `CRIS(X/S)`, read on a point of the ambient scheme. -/
theorem targetHom_comp_apply {D E F : Thickening S} (k : D ⟶ E) (l : E ⟶ F)
    (x : D.thickening.target.scheme) :
    (k ≫ l).targetHom.hom x = l.targetHom.hom (k.targetHom.hom x) := by
  rw [comp_targetHom, DividedPowerScheme.Hom.comp_hom, Scheme.Hom.comp_apply]

/-- **A morphism into a restriction lands in the preimage of any open containing the image of the
composite.**  The open immersion of `V` carries the image of the morphism into the restriction to
the image of the composite with the structure morphism. -/
theorem mem_preimage_of_comp_restrictOpenHom {A D : Thickening S}
    {V : A.thickening.target.scheme.Opens} (k : D ⟶ A.restrictOpen V) {e : D ⟶ A}
    (hk : k ≫ A.restrictOpenHom V = e) {W : A.thickening.target.scheme.Opens}
    (x : D.thickening.target.scheme) (hx : e.targetHom.hom x ∈ W) :
    k.targetHom.hom x ∈ V.ι ⁻¹ᵁ W := by
  change (k ≫ A.restrictOpenHom V).targetHom.hom x ∈ W
  rw [hk]
  exact hx

/-- **The inclusion of a smaller restriction into a bigger one.**  The structure morphism of
`T|_U` has image inside `V`, so it factors through `T|_V` by
`Crystalline.GlobalCrystallineSituation.Thickening.restrictOpenLift`. -/
def restrictOpenIncl (T : Thickening S) {U V : T.thickening.target.scheme.Opens} (h : U ≤ V) :
    T.restrictOpen U ⟶ T.restrictOpen V :=
  restrictOpenLift (T.restrictOpenHom U) V (by
    rintro _ ⟨x, rfl⟩
    exact h x.2)

/-- The inclusion of restrictions is compatible with the structure morphisms. -/
@[reassoc]
theorem restrictOpenIncl_restrictOpenHom (T : Thickening S)
    {U V : T.thickening.target.scheme.Opens} (h : U ≤ V) :
    T.restrictOpenIncl h ≫ T.restrictOpenHom V = T.restrictOpenHom U :=
  restrictOpenLift_restrictOpenHom _ _ _

/-- **The inclusion of restrictions is the unique morphism compatible with the structure
morphisms**, the structure morphism of a restriction being a monomorphism. -/
theorem eq_restrictOpenIncl (T : Thickening S) {U V : T.thickening.target.scheme.Opens} (h : U ≤ V)
    {k : T.restrictOpen U ⟶ T.restrictOpen V}
    (hk : k ≫ T.restrictOpenHom V = T.restrictOpenHom U) : k = T.restrictOpenIncl h :=
  restrictOpen_hom_ext (hk.trans (restrictOpenIncl_restrictOpenHom T h).symm)

/-- The inclusion of a restriction into itself is the identity. -/
@[simp]
theorem restrictOpenIncl_rfl (T : Thickening S) (U : T.thickening.target.scheme.Opens) :
    T.restrictOpenIncl (le_refl U) = 𝟙 _ :=
  (eq_restrictOpenIncl T le_rfl (Category.id_comp _)).symm

/-- The inclusions of restrictions compose. -/
@[reassoc]
theorem restrictOpenIncl_restrictOpenIncl (T : Thickening S)
    {U V W : T.thickening.target.scheme.Opens} (h : U ≤ V) (h' : V ≤ W) :
    T.restrictOpenIncl h ≫ T.restrictOpenIncl h' = T.restrictOpenIncl (h.trans h') :=
  eq_restrictOpenIncl T _ (by
    rw [Category.assoc, restrictOpenIncl_restrictOpenHom, restrictOpenIncl_restrictOpenHom])

/-- **Two morphisms out of an object of `CRIS(X/S)` which agree on the restrictions to the members
of an open cover of the ambient scheme are equal.**  A morphism of `CRIS(X/S)` is determined by its
map on ambient schemes, and a morphism of schemes is determined by its restrictions to an open
cover. -/
theorem hom_ext_of_restrictOpen_iSup {T C : Thickening S} {ι : Type*}
    (U : ι → T.thickening.target.scheme.Opens) (hU : ⨆ i, U i = ⊤) {a b : T ⟶ C}
    (e : ∀ i, T.restrictOpenHom (U i) ≫ a = T.restrictOpenHom (U i) ≫ b) : a = b := by
  refine hom_ext_of_targetHom (Scheme.hom_ext_of_forall _ _ fun x ↦ ?_)
  have hx : x ∈ ⨆ i, U i := by rw [hU]; trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
  exact ⟨U i, hi, congrArg (fun m : T.restrictOpen (U i) ⟶ C ↦ m.targetHom.hom) (e i)⟩

/-- **A restriction of a restriction is a restriction.**  For `U ≤ V` the object `T|_U` is the
restriction of `T|_V` to the preimage of `U` in `V`: the two objects dominate each other over `T`,
and the structure morphism of a restriction is a monomorphism. -/
def restrictOpenRestrictIso (T : Thickening S) {U V : T.thickening.target.scheme.Opens}
    (h : U ≤ V) : T.restrictOpen U ≅ (T.restrictOpen V).restrictOpen (V.ι ⁻¹ᵁ U) where
  hom := restrictOpenLift (T.restrictOpenIncl h) (V.ι ⁻¹ᵁ U) (by
    rintro _ ⟨x, rfl⟩
    exact mem_preimage_of_comp_restrictOpenHom (T.restrictOpenIncl h)
      (restrictOpenIncl_restrictOpenHom T h) x x.2)
  inv := restrictOpenLift
    ((T.restrictOpen V).restrictOpenHom (V.ι ⁻¹ᵁ U) ≫ T.restrictOpenHom V) U (by
      rintro _ ⟨x, rfl⟩
      exact x.2)
  hom_inv_id := by
    refine restrictOpen_hom_ext ?_
    rw [Category.id_comp, Category.assoc, restrictOpenLift_restrictOpenHom, ← Category.assoc,
      restrictOpenLift_restrictOpenHom, restrictOpenIncl_restrictOpenHom]
  inv_hom_id := by
    refine restrictOpen_hom_ext ?_
    rw [Category.id_comp, Category.assoc, restrictOpenLift_restrictOpenHom]
    refine restrictOpen_hom_ext ?_
    rw [Category.assoc, restrictOpenIncl_restrictOpenHom, restrictOpenLift_restrictOpenHom]

/-- The identification of a restriction of a restriction with a restriction is compatible with the
structure morphisms. -/
@[reassoc]
theorem restrictOpenRestrictIso_hom_restrictOpenHom (T : Thickening S)
    {U V : T.thickening.target.scheme.Opens} (h : U ≤ V) :
    (T.restrictOpenRestrictIso h).hom ≫ (T.restrictOpen V).restrictOpenHom (V.ι ⁻¹ᵁ U) =
      T.restrictOpenIncl h :=
  restrictOpenLift_restrictOpenHom _ _ _

/-- **Two morphisms out of a restriction which agree on the restrictions to the members of an open
cover of that open are equal.**  A restriction of the restriction is a restriction, by
`Crystalline.GlobalCrystallineSituation.Thickening.restrictOpenRestrictIso`, so this is
`Crystalline.GlobalCrystallineSituation.Thickening.hom_ext_of_restrictOpen_iSup` for the
restriction. -/
theorem restrictOpen_hom_ext_of_cover {T C : Thickening S} {ι : Type*}
    {V : T.thickening.target.scheme.Opens} (U : ι → T.thickening.target.scheme.Opens)
    (hUV : ∀ i, U i ≤ V) (hcov : V ≤ ⨆ i, U i)
    {a b : T.restrictOpen V ⟶ C}
    (e : ∀ i, T.restrictOpenIncl (hUV i) ≫ a = T.restrictOpenIncl (hUV i) ≫ b) : a = b := by
  refine hom_ext_of_restrictOpen_iSup (fun i ↦ V.ι ⁻¹ᵁ U i) ?_ fun i ↦ ?_
  · refine top_unique fun x _ ↦ ?_
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp (hcov x.2)
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨i, hi⟩
  · refine (cancel_epi (T.restrictOpenRestrictIso (hUV i)).hom).mp ?_
    rw [← Category.assoc, ← Category.assoc, restrictOpenRestrictIso_hom_restrictOpenHom]
    exact e i

/-- The structure morphism of a restriction is an open immersion on thickened schemes: it is the
open immersion of the preimage of the open. -/
instance isOpenImmersion_sourceHom_restrictOpenHom (T : Thickening S)
    (V : T.thickening.target.scheme.Opens) :
    IsOpenImmersion (T.restrictOpenHom V).sourceHom :=
  inferInstanceAs (IsOpenImmersion (T.thickening.immersion ⁻¹ᵁ V).ι)

/-! ### The two components of an isomorphism of `CRIS(X/S)` -/

/-- The map on thickened schemes of an isomorphism of `CRIS(X/S)` is an isomorphism. -/
theorem isIso_sourceHom_of_iso {D E : Thickening S} (θ : D ≅ E) : IsIso θ.hom.sourceHom :=
  ⟨⟨θ.inv.sourceHom, by rw [← comp_sourceHom, θ.hom_inv_id, id_sourceHom],
    by rw [← comp_sourceHom, θ.inv_hom_id, id_sourceHom]⟩⟩

/-- The map on ambient divided power schemes of an isomorphism of `CRIS(X/S)` is an
isomorphism. -/
theorem isIso_targetHom_of_iso {D E : Thickening S} (θ : D ≅ E) : IsIso θ.hom.targetHom :=
  ⟨⟨θ.inv.targetHom, by rw [← comp_targetHom, θ.hom_inv_id, id_targetHom],
    by rw [← comp_targetHom, θ.inv_hom_id, id_targetHom]⟩⟩

/-- The map on ambient schemes of an isomorphism of `CRIS(X/S)` is an isomorphism. -/
theorem isIso_targetHom_hom_of_iso {D E : Thickening S} (θ : D ≅ E) :
    IsIso θ.hom.targetHom.hom :=
  ⟨⟨θ.inv.targetHom.hom,
    by rw [← DividedPowerScheme.Hom.comp_hom, ← comp_targetHom, θ.hom_inv_id, id_targetHom,
      DividedPowerScheme.Hom.id_hom],
    by rw [← DividedPowerScheme.Hom.comp_hom, ← comp_targetHom, θ.inv_hom_id, id_targetHom,
      DividedPowerScheme.Hom.id_hom]⟩⟩

/-- A pair of morphisms out of `T`, read on a point of its thickened scheme: the images agree in
`X`, and each image is carried by the immersion to the image of the immersion of `T`. -/
private theorem toX_immersion_naturality {T A B : Thickening S} (f : T ⟶ A) (g : T ⟶ B)
    (y : T.thickening.source) :
    A.toX (f.sourceHom y) = B.toX (g.sourceHom y) ∧
      A.thickening.immersion (f.sourceHom y) = f.targetHom.hom (T.thickening.immersion y) ∧
      B.thickening.immersion (g.sourceHom y) = g.targetHom.hom (T.thickening.immersion y) :=
  ⟨(congrArg (fun k ↦ k y) f.toX_naturality).trans (congrArg (fun k ↦ k y) g.toX_naturality).symm,
    (congrArg (fun k ↦ k y) f.immersion_naturality).symm,
    (congrArg (fun k ↦ k y) g.immersion_naturality).symm⟩

end Thickening

/-! ### The gluing hypothesis -/

/-- **Zariski descent for morphisms out of an object of `CRIS(X/S)`.**  A family of morphisms out
of the restrictions of `T` to the members of an open cover of its ambient scheme, agreeing on the
pairwise intersections, is the family of restrictions of a morphism out of `T`.

The agreement condition is phrased for *any* pair of morphisms from the restriction to the
intersection which are compatible with the structure morphisms; such a pair exists and is unique
(`Crystalline.GlobalCrystallineSituation.Thickening.restrictOpenIncl` and
`Crystalline.GlobalCrystallineSituation.Thickening.eq_restrictOpenIncl`), so this says no more and
no less than agreement on the intersection.  Only existence is asked for: the glued morphism is
automatically unique, by
`Crystalline.GlobalCrystallineSituation.Thickening.hom_ext_of_restrictOpen_iSup`.

This is *not* proved in this file; it is the hypothesis of
`Crystalline.GlobalCrystallineSituation.hasBinaryProduct_of_glue` and of
`Crystalline.GlobalCrystallineSituation.hasBinaryProducts_thickening_of_glue`. -/
def ZariskiGluing (S : GlobalCrystallineSituation.{u}) : Prop :=
  ∀ {T C : Thickening S} {ι : Type u} (U : ι → T.thickening.target.scheme.Opens),
    ⨆ i, U i = ⊤ → ∀ g : ∀ i, T.restrictOpen (U i) ⟶ C,
      (∀ (i j : ι) (a : T.restrictOpen (U i ⊓ U j) ⟶ T.restrictOpen (U i))
          (b : T.restrictOpen (U i ⊓ U j) ⟶ T.restrictOpen (U j)),
          a ≫ T.restrictOpenHom (U i) = T.restrictOpenHom (U i ⊓ U j) →
          b ≫ T.restrictOpenHom (U j) = T.restrictOpenHom (U i ⊓ U j) →
          a ≫ g i = b ≫ g j) →
      ∃ k : T ⟶ C, ∀ i, T.restrictOpenHom (U i) ≫ k = g i

/-- **Binary products in the affine case**, the affine half of [Stacks, Tag 07I9]: two objects of
`CRIS(X'/S')` whose thickened and ambient schemes are affine, over a situation whose base and
thickened space are affine and on which the fixed prime is nilpotent on global sections, have a
binary product.

This is the shape in which
`Crystalline.GlobalCrystallineSituation.hasBinaryProduct_of_affine_localization` asks for the
affine case.  It is *proved* as
`Crystalline.GlobalCrystallineSituation.hasBinaryProduct_of_isAffine` in
`StacksFrontier/AlgebraicGeometry/Crystalline/BigSite/BinaryProductAffine.lean`; it is a hypothesis
here only because that module and
`StacksFrontier/AlgebraicGeometry/Crystalline/BigSite/BinaryProductPatch.lean` both declare
`Crystalline.GlobalCrystallineSituation.isNilpotent_prime_sections`, so they cannot be imported
together.  See the module documentation. -/
class AffineBinaryProducts : Prop where
  /-- Two objects of an affine situation with affine thickened and ambient schemes have a binary
  product. -/
  out : ∀ S' : GlobalCrystallineSituation.{u}, IsAffine S'.X → IsAffine S'.S.scheme →
    IsNilpotent (S'.p : Γ(S'.X, ⊤)) → ∀ A' B' : Thickening S',
      IsAffine A'.thickening.source → IsAffine A'.thickening.target.scheme →
      IsAffine B'.thickening.source → IsAffine B'.thickening.target.scheme →
      HasBinaryProduct A' B'

namespace ProductPatch

variable {S : GlobalCrystallineSituation.{u}} {A B : Thickening S}
  [AffineBinaryProducts.{u}]

/-! ### The local product over a patch -/

/-- The restriction of the first object to the ambient affine open of a patch. -/
abbrev leftObj (P : ProductPatch A B) : Thickening S :=
  A.restrictOpen (P.leftOpen : A.thickening.target.scheme.Opens)

/-- The restriction of the second object to the ambient affine open of a patch. -/
abbrev rightObj (P : ProductPatch A B) : Thickening S :=
  B.restrictOpen (P.rightOpen : B.thickening.target.scheme.Opens)

/-- **The restrictions of a pair of objects of `CRIS(X/S)` to a product patch have a binary
product.**  Over the patch the base, the thickened space and the two ambient schemes are all
affine and the fixed prime is nilpotent on the sections of the affine open of `X`
(`Crystalline.GlobalCrystallineSituation.isNilpotent_prime_sections_of_isAffineOpen`), so the
affine case `Crystalline.GlobalCrystallineSituation.AffineBinaryProducts` discharges the
hypothesis of
`Crystalline.GlobalCrystallineSituation.hasBinaryProduct_of_affine_localization`. -/
theorem hasBinaryProduct_leftObj_rightObj (P : ProductPatch A B) :
    HasBinaryProduct P.leftObj P.rightObj := by
  have h1 : IsAffine P.leftObj.thickening.target.scheme := P.leftOpen.2
  have h2 : IsAffine P.rightObj.thickening.target.scheme := P.rightOpen.2
  refine hasBinaryProduct_of_affine_localization S (P.baseOpen : S.S.scheme.Opens)
    (P.sourceOpen : S.X.Opens) P.source_le AffineBinaryProducts.out P.baseOpen.2 P.sourceOpen.2
    (S.isNilpotent_prime_sections_of_isAffineOpen (P.sourceOpen : S.X.Opens) P.sourceOpen.2)
    P.leftObj P.rightObj ?_ ?_ ?_ ?_
  · rintro _ ⟨x, rfl⟩
    exact P.left_base x.2
  · rintro _ ⟨x, rfl⟩
    exact P.left_source x.2
  · rintro _ ⟨x, rfl⟩
    exact P.right_base x.2
  · rintro _ ⟨x, rfl⟩
    exact P.right_source x.2

/-- A limit cone presenting the local product over a patch. -/
def prodCone (P : ProductPatch A B) : LimitCone (pair P.leftObj P.rightObj) :=
  (P.hasBinaryProduct_leftObj_rightObj).exists_limit.some

/-- The binary fan presenting the local product over a patch. -/
abbrev prodFan (P : ProductPatch A B) : BinaryFan P.leftObj P.rightObj := P.prodCone.cone

/-- The local product over a patch is a limit. -/
abbrev prodIsLimit (P : ProductPatch A B) : IsLimit P.prodFan := P.prodCone.isLimit

/-- **The local product over a patch**: the product, in `CRIS(X/S)`, of the restrictions of the two
objects to the ambient affine opens of the patch. -/
abbrev prodObj (P : ProductPatch A B) : Thickening S := P.prodFan.pt

/-- The first projection of the local product over a patch, as a morphism to the first object. -/
def fstHom (P : ProductPatch A B) : P.prodObj ⟶ A :=
  P.prodFan.fst ≫ A.restrictOpenHom (P.leftOpen : A.thickening.target.scheme.Opens)

/-- The second projection of the local product over a patch, as a morphism to the second
object. -/
def sndHom (P : ProductPatch A B) : P.prodObj ⟶ B :=
  P.prodFan.snd ≫ B.restrictOpenHom (P.rightOpen : B.thickening.target.scheme.Opens)

/-- The first projection of a local product lands in the ambient affine open of the patch. -/
theorem fstHom_mem (P : ProductPatch A B) (x : P.prodObj.thickening.target.scheme) :
    P.fstHom.targetHom.hom x ∈ (P.leftOpen : A.thickening.target.scheme.Opens) :=
  (P.prodFan.fst.targetHom.hom x).2

/-- The second projection of a local product lands in the ambient affine open of the patch. -/
theorem sndHom_mem (P : ProductPatch A B) (x : P.prodObj.thickening.target.scheme) :
    P.sndHom.targetHom.hom x ∈ (P.rightOpen : B.thickening.target.scheme.Opens) :=
  (P.prodFan.snd.targetHom.hom x).2

/-- **A morphism into a local product is determined by its composites with the two projections**,
the structure morphisms of the two restrictions being monomorphisms. -/
theorem prod_hom_ext {T : Thickening S} (P : ProductPatch A B) {a b : T ⟶ P.prodObj}
    (hf : a ≫ P.fstHom = b ≫ P.fstHom) (hg : a ≫ P.sndHom = b ≫ P.sndHom) : a = b := by
  refine BinaryFan.IsLimit.hom_ext P.prodIsLimit ?_ ?_
  · refine Thickening.restrictOpen_hom_ext ?_
    exact hf
  · refine Thickening.restrictOpen_hom_ext ?_
    exact hg

/-- The factorization through the restriction of the first object of a morphism landing in the
ambient affine open of a patch. -/
def liftLeft {T : Thickening S} (P : ProductPatch A B) (f : T ⟶ A)
    (hf : ∀ x : T.thickening.target.scheme,
      f.targetHom.hom x ∈ (P.leftOpen : A.thickening.target.scheme.Opens)) :
    T ⟶ P.leftObj :=
  Thickening.restrictOpenLift f _ (by rintro _ ⟨x, rfl⟩; exact hf x)

/-- The factorization through the restriction of the second object of a morphism landing in the
ambient affine open of a patch. -/
def liftRight {T : Thickening S} (P : ProductPatch A B) (g : T ⟶ B)
    (hg : ∀ x : T.thickening.target.scheme,
      g.targetHom.hom x ∈ (P.rightOpen : B.thickening.target.scheme.Opens)) :
    T ⟶ P.rightObj :=
  Thickening.restrictOpenLift g _ (by rintro _ ⟨x, rfl⟩; exact hg x)

omit [AffineBinaryProducts.{u}] in
/-- The factorization through the restriction of the first object recovers the morphism. -/
@[reassoc]
theorem liftLeft_restrictOpenHom {T : Thickening S} (P : ProductPatch A B) (f : T ⟶ A) (hf) :
    P.liftLeft f hf ≫ A.restrictOpenHom (P.leftOpen : A.thickening.target.scheme.Opens) = f :=
  Thickening.restrictOpenLift_restrictOpenHom _ _ _

omit [AffineBinaryProducts.{u}] in
/-- The factorization through the restriction of the second object recovers the morphism. -/
@[reassoc]
theorem liftRight_restrictOpenHom {T : Thickening S} (P : ProductPatch A B) (g : T ⟶ B) (hg) :
    P.liftRight g hg ≫ B.restrictOpenHom (P.rightOpen : B.thickening.target.scheme.Opens) = g :=
  Thickening.restrictOpenLift_restrictOpenHom _ _ _

/-- **The morphism into the local product over a patch determined by a pair of morphisms to the two
objects whose ambient maps land in the patch.** -/
def patchLift {T : Thickening S} (P : ProductPatch A B) (f : T ⟶ A) (g : T ⟶ B)
    (hf : ∀ x : T.thickening.target.scheme,
      f.targetHom.hom x ∈ (P.leftOpen : A.thickening.target.scheme.Opens))
    (hg : ∀ x : T.thickening.target.scheme,
      g.targetHom.hom x ∈ (P.rightOpen : B.thickening.target.scheme.Opens)) :
    T ⟶ P.prodObj :=
  P.prodIsLimit.lift (BinaryFan.mk (P.liftLeft f hf) (P.liftRight g hg))

/-- The morphism into a local product, followed by the first projection of the fan. -/
theorem patchLift_prodFan_fst {T : Thickening S} (P : ProductPatch A B) (f : T ⟶ A) (g : T ⟶ B)
    (hf) (hg) : P.patchLift f g hf hg ≫ P.prodFan.fst = P.liftLeft f hf :=
  P.prodIsLimit.fac _ ⟨WalkingPair.left⟩

/-- The morphism into a local product, followed by the second projection of the fan. -/
theorem patchLift_prodFan_snd {T : Thickening S} (P : ProductPatch A B) (f : T ⟶ A) (g : T ⟶ B)
    (hf) (hg) : P.patchLift f g hf hg ≫ P.prodFan.snd = P.liftRight g hg :=
  P.prodIsLimit.fac _ ⟨WalkingPair.right⟩

/-- The morphism into a local product recovers the first of the two given morphisms. -/
@[reassoc]
theorem patchLift_fstHom {T : Thickening S} (P : ProductPatch A B) (f : T ⟶ A) (g : T ⟶ B)
    (hf) (hg) : P.patchLift f g hf hg ≫ P.fstHom = f := by
  change P.patchLift f g hf hg ≫ (P.prodFan.fst ≫ A.restrictOpenHom _) = f
  rw [← Category.assoc, patchLift_prodFan_fst, liftLeft_restrictOpenHom]

/-- The morphism into a local product recovers the second of the two given morphisms. -/
@[reassoc]
theorem patchLift_sndHom {T : Thickening S} (P : ProductPatch A B) (f : T ⟶ A) (g : T ⟶ B)
    (hf) (hg) : P.patchLift f g hf hg ≫ P.sndHom = g := by
  change P.patchLift f g hf hg ≫ (P.prodFan.snd ≫ B.restrictOpenHom _) = g
  rw [← Category.assoc, patchLift_prodFan_snd, liftRight_restrictOpenHom]

/-! ### The diagram of local products -/

/-- **The transition morphism of local products attached to a refinement of patches.** -/
def productMap {P Q : ProductPatch A B} (h : P ≤ Q) : P.prodObj ⟶ Q.prodObj :=
  Q.patchLift P.fstHom P.sndHom (fun x ↦ leftOpen_le_of_le h (P.fstHom_mem x))
    (fun x ↦ rightOpen_le_of_le h (P.sndHom_mem x))

/-- The transition morphism is compatible with the first projections. -/
@[reassoc]
theorem productMap_fstHom {P Q : ProductPatch A B} (h : P ≤ Q) :
    productMap h ≫ Q.fstHom = P.fstHom :=
  patchLift_fstHom _ _ _ _ _

/-- The transition morphism is compatible with the second projections. -/
@[reassoc]
theorem productMap_sndHom {P Q : ProductPatch A B} (h : P ≤ Q) :
    productMap h ≫ Q.sndHom = P.sndHom :=
  patchLift_sndHom _ _ _ _ _

/-- The transition morphism of the identity refinement is the identity. -/
@[simp]
theorem productMap_rfl (P : ProductPatch A B) : productMap (le_refl P) = 𝟙 P.prodObj :=
  P.prod_hom_ext (by rw [productMap_fstHom, Category.id_comp])
    (by rw [productMap_sndHom, Category.id_comp])

/-- The transition morphisms of local products compose. -/
@[reassoc]
theorem productMap_productMap {P Q R : ProductPatch A B} (h : P ≤ Q) (h' : Q ≤ R) :
    productMap h ≫ productMap h' = productMap (h.trans h') :=
  R.prod_hom_ext
    (by rw [Category.assoc, productMap_fstHom, productMap_fstHom, productMap_fstHom])
    (by rw [Category.assoc, productMap_sndHom, productMap_sndHom, productMap_sndHom])

/-- **The diagram of local products over the preorder of product patches.** -/
def functor (A B : Thickening S) : ProductPatch A B ⥤ Thickening S where
  obj P := P.prodObj
  map h := productMap (leOfHom h)
  map_id P := productMap_rfl P
  map_comp _ _ := (productMap_productMap _ _).symm

/-- A transition morphism of the diagram of local products. -/
theorem functor_map {P Q : ProductPatch A B} (h : P ⟶ Q) :
    (functor A B).map h = productMap (leOfHom h) := rfl

/-! ### A transition morphism is the structure morphism of a restriction -/

/-- **The open of the ambient scheme of the `Q`-product over which it lands in the patch `P`.** -/
def transOpen (P Q : ProductPatch A B) : Q.prodObj.thickening.target.scheme.Opens :=
  ProductPatch.preimage Q.fstHom Q.sndHom P

/-- Membership in `Crystalline.GlobalCrystallineSituation.ProductPatch.transOpen`. -/
theorem mem_transOpen_iff (P Q : ProductPatch A B) (x : Q.prodObj.thickening.target.scheme) :
    x ∈ transOpen P Q ↔
      Q.fstHom.targetHom.hom x ∈ (P.leftOpen : A.thickening.target.scheme.Opens) ∧
      Q.sndHom.targetHom.hom x ∈ (P.rightOpen : B.thickening.target.scheme.Opens) :=
  Iff.rfl

/-- The transition morphism of a refinement lands in the open over which the bigger product sits
inside the smaller patch. -/
theorem productMap_mem_transOpen {P Q : ProductPatch A B} (h : P ≤ Q)
    (x : P.prodObj.thickening.target.scheme) :
    (productMap h).targetHom.hom x ∈ transOpen P Q := by
  refine (mem_transOpen_iff P Q _).mpr ⟨?_, ?_⟩
  · rw [← Thickening.targetHom_comp_apply, productMap_fstHom]
    exact P.fstHom_mem x
  · rw [← Thickening.targetHom_comp_apply, productMap_sndHom]
    exact P.sndHom_mem x

/-- The factorization of the transition morphism of a refinement through the restriction of the
bigger product. -/
def transHom {P Q : ProductPatch A B} (h : P ≤ Q) :
    P.prodObj ⟶ Q.prodObj.restrictOpen (transOpen P Q) :=
  Thickening.restrictOpenLift (productMap h) (transOpen P Q) (by
    rintro _ ⟨x, rfl⟩
    exact productMap_mem_transOpen h x)

/-- The morphism from the restriction of the bigger product to the smaller product, given by the
universal property of the latter. -/
def transInv (P Q : ProductPatch A B) :
    Q.prodObj.restrictOpen (transOpen P Q) ⟶ P.prodObj :=
  P.patchLift (Q.prodObj.restrictOpenHom (transOpen P Q) ≫ Q.fstHom)
    (Q.prodObj.restrictOpenHom (transOpen P Q) ≫ Q.sndHom)
    (fun x ↦ by rw [Thickening.targetHom_comp_apply]; exact x.2.1)
    (fun x ↦ by rw [Thickening.targetHom_comp_apply]; exact x.2.2)

/-- The factorization of the transition morphism recovers the transition morphism. -/
@[reassoc]
theorem transHom_restrictOpenHom {P Q : ProductPatch A B} (h : P ≤ Q) :
    transHom h ≫ Q.prodObj.restrictOpenHom (transOpen P Q) = productMap h :=
  Thickening.restrictOpenLift_restrictOpenHom _ _ _

/-- The morphism out of the restriction of the bigger product is compatible with the first
projections. -/
@[reassoc]
theorem transInv_fstHom (P Q : ProductPatch A B) :
    transInv P Q ≫ P.fstHom = Q.prodObj.restrictOpenHom (transOpen P Q) ≫ Q.fstHom :=
  patchLift_fstHom _ _ _ _ _

/-- The morphism out of the restriction of the bigger product is compatible with the second
projections. -/
@[reassoc]
theorem transInv_sndHom (P Q : ProductPatch A B) :
    transInv P Q ≫ P.sndHom = Q.prodObj.restrictOpenHom (transOpen P Q) ≫ Q.sndHom :=
  patchLift_sndHom _ _ _ _ _

/-- **A transition morphism of local products identifies the smaller product with a restriction of
the bigger one.**  Both composites are identities: one by the universal property of the smaller
product, the other because the structure morphism of a restriction is a monomorphism. -/
def transIso {P Q : ProductPatch A B} (h : P ≤ Q) :
    P.prodObj ≅ Q.prodObj.restrictOpen (transOpen P Q) where
  hom := transHom h
  inv := transInv P Q
  hom_inv_id := by
    refine P.prod_hom_ext ?_ ?_
    · rw [Category.id_comp, Category.assoc, transInv_fstHom, ← Category.assoc,
        transHom_restrictOpenHom, productMap_fstHom]
    · rw [Category.id_comp, Category.assoc, transInv_sndHom, ← Category.assoc,
        transHom_restrictOpenHom, productMap_sndHom]
  inv_hom_id := by
    refine Thickening.restrictOpen_hom_ext ?_
    rw [Category.id_comp, Category.assoc, transHom_restrictOpenHom]
    refine Q.prod_hom_ext ?_ ?_
    · rw [Category.assoc, productMap_fstHom, transInv_fstHom]
    · rw [Category.assoc, productMap_sndHom, transInv_sndHom]

/-- The identification of the smaller product with a restriction of the bigger one is compatible
with the transition morphism. -/
@[reassoc]
theorem transIso_hom_restrictOpenHom {P Q : ProductPatch A B} (h : P ≤ Q) :
    (transIso h).hom ≫ Q.prodObj.restrictOpenHom (transOpen P Q) = productMap h :=
  transHom_restrictOpenHom h

/-- **A transition morphism of local products is an open immersion on thickened schemes**: up to an
isomorphism it is the open immersion of the preimage of an open. -/
theorem isOpenImmersion_productMap_sourceHom {P Q : ProductPatch A B} (h : P ≤ Q) :
    IsOpenImmersion (productMap h).sourceHom := by
  have hiso : IsIso (transIso h).hom.sourceHom := Thickening.isIso_sourceHom_of_iso (transIso h)
  have he : (productMap h).sourceHom = (transIso h).hom.sourceHom ≫
      (Q.prodObj.restrictOpenHom (transOpen P Q)).sourceHom := by
    rw [← Thickening.comp_sourceHom, transIso_hom_restrictOpenHom]
  rw [he]
  exact IsOpenImmersion.comp _ _

/-- **A transition morphism of local products is an induced open immersion on ambient divided power
schemes**: up to an isomorphism it is the morphism from a restriction, which is an induced open
immersion by `Crystalline.DividedPowerScheme.isInducedOpen_restrictι`. -/
theorem isInducedOpen_productMap_targetHom {P Q : ProductPatch A B} (h : P ≤ Q) :
    DividedPowerScheme.IsInducedOpen (productMap h).targetHom := by
  have := Thickening.isIso_targetHom_of_iso (transIso h)
  have he : (productMap h).targetHom = (transIso h).hom.targetHom ≫
      Q.prodObj.thickening.target.restrictι (transOpen P Q) := by
    rw [← Thickening.restrictOpenHom_targetHom, ← Thickening.comp_targetHom,
      transIso_hom_restrictOpenHom]
  rw [he]
  exact (DividedPowerScheme.isInducedOpen_of_isIso _).comp
    (DividedPowerScheme.isInducedOpen_restrictι _ _)

/-- A transition morphism of local products is injective on points of the ambient scheme. -/
theorem productMap_targetHom_injective {P Q : ProductPatch A B} (h : P ≤ Q) :
    Function.Injective (productMap h).targetHom.hom.base := by
  have := (isInducedOpen_productMap_targetHom h).isOpenImmersion
  exact (Scheme.Hom.isOpenEmbedding (productMap h).targetHom.hom).injective

/-- **A point of the bigger product lying in the smaller patch comes from the smaller product.** -/
theorem exists_productMap_eq {P Q : ProductPatch A B} (h : P ≤ Q)
    (y : Q.prodObj.thickening.target.scheme) (hy : y ∈ transOpen P Q) :
    ∃ x : P.prodObj.thickening.target.scheme, (productMap h).targetHom.hom x = y := by
  have key : (transIso h).inv ≫ productMap h = Q.prodObj.restrictOpenHom (transOpen P Q) := by
    rw [← transIso_hom_restrictOpenHom h, ← Category.assoc, (transIso h).inv_hom_id,
      Category.id_comp]
  refine ⟨(transIso h).inv.targetHom.hom ⟨y, hy⟩, ?_⟩
  exact congrArg (fun m : Q.prodObj.restrictOpen (transOpen P Q) ⟶ Q.prodObj ↦
    m.targetHom.hom.base ⟨y, hy⟩) key

/-! ### The presentation and the glued object -/

/-- **A point of a local product determines a point of the thickened scheme of the first object**:
lift it through the surjective immersion and push it forward. -/
theorem exists_source_point (P : ProductPatch A B) (x : P.prodObj.thickening.target.scheme) :
    ∃ (a : A.thickening.source) (b : B.thickening.source), A.toX a = B.toX b ∧
      A.thickening.immersion a = P.fstHom.targetHom.hom x ∧
      B.thickening.immersion b = P.sndHom.targetHom.hom x := by
  obtain ⟨y, rfl⟩ := P.prodObj.thickening.isThickening.2 x
  exact ⟨_, _, Thickening.toX_immersion_naturality P.fstHom P.sndHom y⟩

/-- **A point of a local product lying in the ambient opens of another patch lies in the image of
a refined product.**  A common refinement `L` of the two patches exists by
`Crystalline.GlobalCrystallineSituation.exists_productPatch_le`, and the point comes from the
`L`-product by `Crystalline.GlobalCrystallineSituation.ProductPatch.exists_productMap_eq`. -/
private theorem exists_productMap_eq_of_mem {P Q : ProductPatch A B}
    (y : Q.prodObj.thickening.target.scheme)
    (hf : Q.fstHom.targetHom.hom y ∈ (P.leftOpen : A.thickening.target.scheme.Opens))
    (hg : Q.sndHom.targetHom.hom y ∈ (P.rightOpen : B.thickening.target.scheme.Opens)) :
    ∃ L : ProductPatch A B, L ≤ P ∧ ∃ (hLQ : L ≤ Q) (x : L.prodObj.thickening.target.scheme),
      (productMap hLQ).targetHom.hom x = y := by
  obtain ⟨a, b, hab, ha, hb⟩ := Q.exists_source_point y
  obtain ⟨L, hLP, hLQ, haL, hbL⟩ := exists_productPatch_le P Q a b hab
    (by rw [ha]; exact hf) (ha ▸ Q.fstHom_mem y) (by rw [hb]; exact hg) (hb ▸ Q.sndHom_mem y)
  obtain ⟨x, hx⟩ := exists_productMap_eq hLQ y
    ((mem_transOpen_iff L Q y).mpr ⟨ha ▸ haL, hb ▸ hbL⟩)
  exact ⟨L, hLP, hLQ, x, hx⟩

/-- **The diagram of local products is locally directed.**  Two points of two local products with
the same image in a third have the same images in the thickened schemes of `A` and of `B`; those
two points lie in a common refinement of the two patches by
`Crystalline.GlobalCrystallineSituation.exists_productPatch_le`, and the given points come from a
point of the refined product. -/
theorem directed_functor {P Q R : ProductPatch A B} (fi : P ⟶ R) (fj : Q ⟶ R)
    (xi : P.prodObj.thickening.target.scheme) (xj : Q.prodObj.thickening.target.scheme)
    (hx : (productMap (leOfHom fi)).targetHom.hom xi =
      (productMap (leOfHom fj)).targetHom.hom xj) :
    ∃ (L : ProductPatch A B) (gi : L ≤ P) (gj : L ≤ Q)
      (x : L.prodObj.thickening.target.scheme),
      (productMap gi).targetHom.hom x = xi ∧ (productMap gj).targetHom.hom x = xj := by
  have hfst : P.fstHom.targetHom.hom xi = Q.fstHom.targetHom.hom xj := by
    rw [← productMap_fstHom (leOfHom fi), ← productMap_fstHom (leOfHom fj),
      Thickening.targetHom_comp_apply, Thickening.targetHom_comp_apply, hx]
  have hsnd : P.sndHom.targetHom.hom xi = Q.sndHom.targetHom.hom xj := by
    rw [← productMap_sndHom (leOfHom fi), ← productMap_sndHom (leOfHom fj),
      Thickening.targetHom_comp_apply, Thickening.targetHom_comp_apply, hx]
  obtain ⟨L, hLQ, hLP, x, hxP⟩ := exists_productMap_eq_of_mem (P := Q) xi
    (hfst ▸ Q.fstHom_mem xj) (hsnd ▸ Q.sndHom_mem xj)
  refine ⟨L, hLP, hLQ, x, hxP, ?_⟩
  refine productMap_targetHom_injective (leOfHom fj) ?_
  have e1 : (productMap (leOfHom fj)).targetHom.hom ((productMap hLQ).targetHom.hom x) =
      (productMap (hLQ.trans (leOfHom fj))).targetHom.hom x := by
    rw [← Thickening.targetHom_comp_apply, productMap_productMap]
  have e2 : (productMap (hLQ.trans (leOfHom fj))).targetHom.hom x =
      (productMap (leOfHom fi)).targetHom.hom ((productMap hLP).targetHom.hom x) := by
    rw [← Thickening.targetHom_comp_apply, productMap_productMap]
  rw [e1, e2, hxP, hx]

/-- **The diagram of local products over the preorder of product patches is a presentation of an
object of `CRIS(X/S)`.** -/
def presentation (A B : Thickening S) : ThickeningPresentation S (ProductPatch A B) where
  functor := functor A B
  induced h := isInducedOpen_productMap_targetHom (leOfHom h)
  isOpenImmersion_sourceHom h := isOpenImmersion_productMap_sourceHom (leOfHom h)
  directed fi fj xi xj h := by
    obtain ⟨L, gi, gj, x, h1, h2⟩ := directed_functor fi fj xi xj h
    exact ⟨L, homOfLE gi, homOfLE gj, x, h1, h2⟩

/-- **The glued object**: the object of `CRIS(X/S)` obtained by gluing the local products over all
product patches. -/
def gluedProd (A B : Thickening S) : Thickening S := (presentation A B).glued

/-- The chart morphism of a patch into the glued object. -/
def gluedChart (P : ProductPatch A B) : P.prodObj ⟶ gluedProd A B :=
  (presentation A B).gluedι P

/-- The chart morphisms into the glued object are compatible with the transition morphisms. -/
@[reassoc]
theorem productMap_gluedChart {P Q : ProductPatch A B} (h : P ≤ Q) :
    productMap h ≫ gluedChart Q = gluedChart P :=
  (presentation A B).map_gluedι (homOfLE h)

/-- **The first projection of the glued object**, glued from the first projections of the local
products. -/
def gluedFst (A B : Thickening S) : gluedProd A B ⟶ A :=
  (presentation A B).gluedHom A (fun P ↦ P.fstHom) fun h ↦ productMap_fstHom (leOfHom h)

/-- **The second projection of the glued object**, glued from the second projections of the local
products. -/
def gluedSnd (A B : Thickening S) : gluedProd A B ⟶ B :=
  (presentation A B).gluedHom B (fun P ↦ P.sndHom) fun h ↦ productMap_sndHom (leOfHom h)

/-- The first projection of the glued object restricts to the first projection of each local
product. -/
@[reassoc]
theorem gluedChart_gluedFst (P : ProductPatch A B) :
    gluedChart P ≫ gluedFst A B = P.fstHom :=
  (presentation A B).gluedι_gluedHom A (fun P ↦ P.fstHom)
    (fun h ↦ productMap_fstHom (leOfHom h)) P

/-- The second projection of the glued object restricts to the second projection of each local
product. -/
@[reassoc]
theorem gluedChart_gluedSnd (P : ProductPatch A B) :
    gluedChart P ≫ gluedSnd A B = P.sndHom :=
  (presentation A B).gluedι_gluedHom B (fun P ↦ P.sndHom)
    (fun h ↦ productMap_sndHom (leOfHom h)) P

/-- Each chart morphism into the glued object is Cartesian: this is the Cartesian chart square of
the presentation. -/
theorem isCartesian_gluedChart (P : ProductPatch A B) :
    Thickening.IsCartesian (gluedChart P) :=
  ((presentation A B).isPullback_chart P).flip

/-- Each chart morphism into the glued object is an open immersion on ambient schemes. -/
instance isOpenImmersion_gluedChart_targetHom (P : ProductPatch A B) :
    IsOpenImmersion (gluedChart P).targetHom.hom :=
  (presentation A B).isOpenImmersion_gluedι_targetHom P

/-- **The charts cover the ambient scheme of the glued object.** -/
theorem gluedChart_jointly_surjective (z : (gluedProd A B).thickening.target.scheme) :
    ∃ (Q : ProductPatch A B) (y : Q.prodObj.thickening.target.scheme),
      (gluedChart Q).targetHom.hom y = z :=
  (presentation A B).gluedι_jointly_surjective z

/-- **A point of the glued object whose two images lie in a patch lies in the image of that
patch's chart.**  The point comes from some chart `Q`; the two images then lie in both patches, so
a common refinement `L` of the two patches contains them, the point comes from the `L`-chart, and
the `L`-chart factors through the `P`-chart. -/
theorem mem_range_gluedChart_targetHom (P : ProductPatch A B)
    (z : (gluedProd A B).thickening.target.scheme)
    (hf : (gluedFst A B).targetHom.hom z ∈ (P.leftOpen : A.thickening.target.scheme.Opens))
    (hg : (gluedSnd A B).targetHom.hom z ∈ (P.rightOpen : B.thickening.target.scheme.Opens)) :
    z ∈ Set.range (gluedChart P).targetHom.hom.base := by
  obtain ⟨Q, y, rfl⟩ := gluedChart_jointly_surjective (A := A) (B := B) z
  have hQf : Q.fstHom.targetHom.hom y = (gluedFst A B).targetHom.hom
      ((gluedChart Q).targetHom.hom y) := by
    rw [← Thickening.targetHom_comp_apply, gluedChart_gluedFst]
  have hQg : Q.sndHom.targetHom.hom y = (gluedSnd A B).targetHom.hom
      ((gluedChart Q).targetHom.hom y) := by
    rw [← Thickening.targetHom_comp_apply, gluedChart_gluedSnd]
  obtain ⟨L, hLP, hLQ, x, hx⟩ := exists_productMap_eq_of_mem (P := P) y
    (by rw [hQf]; exact hf) (by rw [hQg]; exact hg)
  refine ⟨(productMap hLP).targetHom.hom x, ?_⟩
  rw [← Thickening.targetHom_comp_apply, productMap_gluedChart, ← productMap_gluedChart hLQ,
    Thickening.targetHom_comp_apply, hx]

/-- **A morphism into the glued object factors, over the open where its two composites land in a
patch, through that patch's chart.**  The chart morphisms are Cartesian open immersions, so
`Crystalline.GlobalCrystallineSituation.Thickening.pullbackLiftHom` applies. -/
theorem exists_comp_gluedChart (P : ProductPatch A B) {Z : Thickening S} (r : Z ⟶ gluedProd A B)
    (V : Z.thickening.target.scheme.Opens)
    (hV : ∀ x : Z.thickening.target.scheme, x ∈ V →
      r.targetHom.hom x ∈ Set.range (gluedChart P).targetHom.hom.base) :
    ∃ p : Z.restrictOpen V ⟶ P.prodObj, p ≫ gluedChart P = Z.restrictOpenHom V ≫ r := by
  have hle : V ≤ Thickening.pullbackOpen (gluedChart P) r := fun x hx ↦ hV x hx
  refine ⟨Z.restrictOpenIncl hle ≫
    Thickening.pullbackLiftHom (gluedChart P) r (isCartesian_gluedChart P), ?_⟩
  rw [Category.assoc, Thickening.pullbackLiftHom_comp, ← Category.assoc,
    Thickening.restrictOpenIncl_restrictOpenHom]

/-- **A morphism into the glued object is determined by its composites with the two
projections.**  The opens on which the two composites land in a patch cover the ambient scheme of
the source, and over each of them both morphisms factor through that patch's chart, where the
universal property of the local product applies. -/
theorem gluedProd_hom_ext {Z : Thickening S} {m l : Z ⟶ gluedProd A B}
    (hf : m ≫ gluedFst A B = l ≫ gluedFst A B) (hg : m ≫ gluedSnd A B = l ≫ gluedSnd A B) :
    m = l := by
  refine Thickening.hom_ext_of_restrictOpen_iSup
    (fun P : ProductPatch A B ↦ ProductPatch.preimage (m ≫ gluedFst A B) (m ≫ gluedSnd A B) P)
    (ProductPatch.iSup_preimage_eq_top _ _) fun P ↦ ?_
  have hmem : ∀ n : Z ⟶ gluedProd A B, m ≫ gluedFst A B = n ≫ gluedFst A B →
      m ≫ gluedSnd A B = n ≫ gluedSnd A B → ∀ x : Z.thickening.target.scheme,
      x ∈ ProductPatch.preimage (m ≫ gluedFst A B) (m ≫ gluedSnd A B) P →
      n.targetHom.hom x ∈ Set.range (gluedChart P).targetHom.hom.base := by
    intro n hnf hng x hx
    refine mem_range_gluedChart_targetHom P _ ?_ ?_
    · rw [← Thickening.targetHom_comp_apply, ← hnf]; exact hx.1
    · rw [← Thickening.targetHom_comp_apply, ← hng]; exact hx.2
  obtain ⟨p, hp⟩ := exists_comp_gluedChart P m _ (hmem m rfl rfl)
  obtain ⟨q, hq⟩ := exists_comp_gluedChart P l _ (hmem l hf hg)
  have hpq : p = q := by
    refine P.prod_hom_ext ?_ ?_
    · rw [← gluedChart_gluedFst P, ← Category.assoc, ← Category.assoc, hp, hq, Category.assoc,
        Category.assoc, hf]
    · rw [← gluedChart_gluedSnd P, ← Category.assoc, ← Category.assoc, hp, hq, Category.assoc,
        Category.assoc, hg]
  rw [← hp, ← hq, hpq]

/-! ### The universal property -/

/-- The local morphism into the chart of a patch determined by a cone over the pair, on the open
where the cone lands in the patch. -/
def coneLift {T : Thickening S} (f : T ⟶ A) (g : T ⟶ B) (P : ProductPatch A B) :
    T.restrictOpen (ProductPatch.preimage f g P) ⟶ P.prodObj :=
  P.patchLift (T.restrictOpenHom (ProductPatch.preimage f g P) ≫ f)
    (T.restrictOpenHom (ProductPatch.preimage f g P) ≫ g)
    (fun x ↦ by rw [Thickening.targetHom_comp_apply]; exact x.2.1)
    (fun x ↦ by rw [Thickening.targetHom_comp_apply]; exact x.2.2)

/-- The local morphism into a chart is compatible with the first projection. -/
@[reassoc]
theorem coneLift_fstHom {T : Thickening S} (f : T ⟶ A) (g : T ⟶ B) (P : ProductPatch A B) :
    coneLift f g P ≫ P.fstHom = T.restrictOpenHom (ProductPatch.preimage f g P) ≫ f :=
  patchLift_fstHom _ _ _ _ _

/-- The local morphism into a chart is compatible with the second projection. -/
@[reassoc]
theorem coneLift_sndHom {T : Thickening S} (f : T ⟶ A) (g : T ⟶ B) (P : ProductPatch A B) :
    coneLift f g P ≫ P.sndHom = T.restrictOpenHom (ProductPatch.preimage f g P) ≫ g :=
  patchLift_sndHom _ _ _ _ _

/-- **The local morphisms into the charts are compatible with refinement of patches.**  Both sides
are morphisms into a local product with the same composites with the two projections. -/
theorem restrictOpenIncl_coneLift {T : Thickening S} (f : T ⟶ A) (g : T ⟶ B)
    {L P : ProductPatch A B} (h : L ≤ P)
    (hle : ProductPatch.preimage f g L ≤ ProductPatch.preimage f g P) :
    T.restrictOpenIncl hle ≫ coneLift f g P = coneLift f g L ≫ productMap h := by
  refine P.prod_hom_ext ?_ ?_
  · rw [Category.assoc, coneLift_fstHom, Category.assoc, productMap_fstHom, coneLift_fstHom,
      ← Category.assoc, Thickening.restrictOpenIncl_restrictOpenHom]
  · rw [Category.assoc, coneLift_sndHom, Category.assoc, productMap_sndHom, coneLift_sndHom,
      ← Category.assoc, Thickening.restrictOpenIncl_restrictOpenHom]

omit [AffineBinaryProducts.{u}] in
/-- A refinement of patches shrinks the open on which a cone lands in the patch. -/
theorem preimage_mono {T : Thickening S} (f : T ⟶ A) (g : T ⟶ B) {L P : ProductPatch A B}
    (h : L ≤ P) : ProductPatch.preimage f g L ≤ ProductPatch.preimage f g P :=
  fun _ hx ↦ ⟨leftOpen_le_of_le h hx.1, rightOpen_le_of_le h hx.2⟩

omit [AffineBinaryProducts.{u}] in
/-- **The opens on which a cone lands in a common refinement of two patches cover the overlap of
the two opens attached to those patches.**  A point of the overlap lifts through the surjective
immersion of `T` and its two images lie in both patches, so
`Crystalline.GlobalCrystallineSituation.exists_productPatch_le` produces the refinement. -/
theorem le_iSup_preimage_refine {T : Thickening S} (f : T ⟶ A) (g : T ⟶ B)
    (P Q : ProductPatch A B) :
    ProductPatch.preimage f g P ⊓ ProductPatch.preimage f g Q ≤
      ⨆ L : {L : ProductPatch A B // L ≤ P ∧ L ≤ Q}, ProductPatch.preimage f g L.1 := by
  intro w hw
  obtain ⟨y, rfl⟩ := T.thickening.isThickening.2 w
  obtain ⟨he, hfa, hgb⟩ := Thickening.toX_immersion_naturality f g y
  obtain ⟨L, hLP, hLQ, haL, hbL⟩ := exists_productPatch_le P Q (f.sourceHom y) (g.sourceHom y) he
    (hfa ▸ hw.1.1) (hfa ▸ hw.2.1) (hgb ▸ hw.1.2) (hgb ▸ hw.2.2)
  have h1 : f.targetHom.hom (T.thickening.immersion y) ∈
      (L.leftOpen : A.thickening.target.scheme.Opens) := by rw [← hfa]; exact haL
  have h2 : g.targetHom.hom (T.thickening.immersion y) ∈
      (L.rightOpen : B.thickening.target.scheme.Opens) := by rw [← hgb]; exact hbL
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨L, hLP, hLQ⟩, h1, h2⟩

/-- **A cone over the pair lifts to the glued object**, granted the Zariski gluing property.  The
local morphisms into the charts agree on the overlaps, because over the open where a common
refinement of two patches applies both are the local morphism into the refined chart, and the
charts are compatible with refinement. -/
theorem exists_lift_of_zariskiGluing (hglue : ZariskiGluing S) {T : Thickening S} (f : T ⟶ A)
    (g : T ⟶ B) :
    ∃ k : T ⟶ gluedProd A B, k ≫ gluedFst A B = f ∧ k ≫ gluedSnd A B = g := by
  obtain ⟨k, hk⟩ := hglue (fun P : ProductPatch A B ↦ ProductPatch.preimage f g P)
    (ProductPatch.iSup_preimage_eq_top f g)
    (fun P ↦ coneLift f g P ≫ gluedChart P) (by
      intro P Q a b ha hb
      rw [Thickening.eq_restrictOpenIncl T inf_le_left ha,
        Thickening.eq_restrictOpenIncl T inf_le_right hb]
      refine Thickening.restrictOpen_hom_ext_of_cover
        (fun L : {L : ProductPatch A B // L ≤ P ∧ L ≤ Q} ↦ ProductPatch.preimage f g L.1)
        (fun L ↦ le_inf (preimage_mono f g L.2.1) (preimage_mono f g L.2.2))
        (le_iSup_preimage_refine f g P Q) fun L ↦ ?_
      simp only [← Category.assoc]
      rw [Thickening.restrictOpenIncl_restrictOpenIncl,
        Thickening.restrictOpenIncl_restrictOpenIncl,
        restrictOpenIncl_coneLift f g L.2.1 (preimage_mono f g L.2.1),
        restrictOpenIncl_coneLift f g L.2.2 (preimage_mono f g L.2.2)]
      simp only [Category.assoc]
      rw [productMap_gluedChart, productMap_gluedChart])
  refine ⟨k, ?_, ?_⟩
  all_goals
    refine Thickening.hom_ext_of_restrictOpen_iSup
      (fun P : ProductPatch A B ↦ ProductPatch.preimage f g P)
      (ProductPatch.iSup_preimage_eq_top f g) fun P ↦ ?_
    rw [← Category.assoc, hk, Category.assoc]
  · rw [gluedChart_gluedFst, coneLift_fstHom]
  · rw [gluedChart_gluedSnd, coneLift_sndHom]

/-- **The glued object, with its two projections, is a binary product of the pair**, granted the
Zariski gluing property.  Existence of a lift is
`Crystalline.GlobalCrystallineSituation.ProductPatch.exists_lift_of_zariskiGluing` and uniqueness
is `Crystalline.GlobalCrystallineSituation.ProductPatch.gluedProd_hom_ext`. -/
def isLimitGluedProd (hglue : ZariskiGluing S) (A B : Thickening S) :
    IsLimit (BinaryFan.mk (gluedFst A B) (gluedSnd A B)) := by
  classical
  choose L hL1 hL2 using fun (T : Thickening S) (f : T ⟶ A) (g : T ⟶ B) ↦
    exists_lift_of_zariskiGluing hglue f g
  refine BinaryFan.IsLimit.mk _ (fun {T} f g ↦ L T f g) (fun f g ↦ hL1 _ f g)
    (fun f g ↦ hL2 _ f g) fun {T} f g m hm1 hm2 ↦ ?_
  refine gluedProd_hom_ext ?_ ?_
  · rw [hL1]; exact hm1
  · rw [hL2]; exact hm2

end ProductPatch

/-- **Stacks Project, Tag 07I9 (1).**  Two objects of the big crystalline category `CRIS(X/S)` have
a binary product, granted the affine case
`Crystalline.GlobalCrystallineSituation.AffineBinaryProducts` and the Zariski gluing property
`Crystalline.GlobalCrystallineSituation.ZariskiGluing` for morphisms out of an object.

The product is glued from the products of the restrictions of the two objects to the affine product
patches of the pair; see the module documentation. -/
theorem hasBinaryProduct_of_glue {S : GlobalCrystallineSituation.{u}}
    (haff : AffineBinaryProducts.{u}) (hglue : ZariskiGluing S) (A B : Thickening S) :
    HasBinaryProduct A B :=
  have := haff
  ⟨⟨_, ProductPatch.isLimitGluedProd hglue A B⟩⟩

/-- **Stacks Project, Tag 07I9 (1).**  The big crystalline category `CRIS(X/S)` has binary
products, granted the affine case
`Crystalline.GlobalCrystallineSituation.AffineBinaryProducts` and the Zariski gluing property
`Crystalline.GlobalCrystallineSituation.ZariskiGluing` for morphisms out of an object. -/
theorem hasBinaryProducts_thickening_of_glue {S : GlobalCrystallineSituation.{u}}
    (haff : AffineBinaryProducts.{u}) (hglue : ZariskiGluing S) :
    HasBinaryProducts (Thickening S) := by
  have : ∀ A B : Thickening S, HasBinaryProduct A B := hasBinaryProduct_of_glue haff hglue
  exact hasBinaryProducts_of_hasLimit_pair _

end GlobalCrystallineSituation

end Crystalline

end
