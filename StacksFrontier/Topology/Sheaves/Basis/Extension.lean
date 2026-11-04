module

public import StacksFrontier.Topology.Sheaves.AlgebraicStructure.Defs
public import Mathlib.Topology.Category.TopCat.OpenNhds

public import StacksFrontier.Topology.Sheaves.Basis.Sheaf
public import StacksFrontier.Topology.Sheaves.Basis.ModuleRestriction
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Stacks 009Q — Extension of a sheaf on a basis to a sheaf on the space

Let `(C, F)` be a type of algebraic structure (Stacks 007M: a category `C` together with a
forgetful functor `F : C ⥤ Set` that is faithful, preserves small limits, preserves filtered
colimits and reflects isomorphisms), and let `B` be a basis for the topology of `X`. Stacks 009Q
says that every sheaf with values in `C` on `B` extends to a sheaf with values in `C` on `X`,
uniquely up to unique isomorphism, whose restriction to `B` recovers it. This is
`extension_of_sheaf_on_basis`, assembled from `extension_exists` and `extension_uniqueness`.

The statement is set up from: `CPresheafOnBasis` and `CSheafOnBasis`, presheaves and sheaves with
values in `C` on `B`, the latter being functors `(BasisCat B)ᵒᵖ ⥤ C` whose underlying set-valued
presheaf (`underlyingStruct`, `typeStruct`) satisfies the Stacks 009J basis-sheaf condition;
`CSheaf`, the same notion on all of `Opens X`; `restrictToBasis` and `restrictIso`, restriction of
a presheaf or of an isomorphism along the inclusion of basis opens; and `stalk`, the filtered
colimit of a basis presheaf over the basis-open neighbourhoods of a point.

The proof runs through `csheafEquiv`: the inclusion `BasisCat B ⥤ Opens X` is a dense subsite
inclusion, so restriction along it is an equivalence between `C`-valued sheaves on the basis site
and on `X`. Existence is then essential surjectivity of that equivalence and uniqueness is its
full faithfulness; the bridge lemmas identify the elementary sheaf conditions above with sheaf
conditions for the corresponding Grothendieck topologies.

## Universe note

A type of algebraic structure is modelled as `AlgebraicStructureType.{u, w}`, bundling a
category `A.C : Type w` with `Hom`-types in `Type u` together with a forgetful functor
`A.F : A.C ⥤ Type u`. For `X : TopCat.{u}` the points of `X` live in `Type u`, and the
underlying-set machinery requires `A.F` to land in that same universe, since sections and stalks
are built out of underlying sets indexed by points of `X`. The object universe `w` remains
arbitrary, so examples such as abelian groups or `R`-modules in an arbitrary `Type w` are covered.
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite Limits

-- The basis-site vocabulary this file builds on lives in the `Stacks.BasisRestriction` namespace.
-- Only the four names used here are opened, so no other declaration of that namespace can
-- shadow one of ours.
open Stacks.BasisRestriction (BasisCat basisInclusion basisGrothendieckTopology
  basisInclusion_isDenseSubsite)

namespace Stacks.BasisExtension

universe u w

variable {X : TopCat.{u}} {B : Set (Opens X)}

/-! ## Type of algebraic structure (Stacks 007M)

This is already available in the library as `AlgebraicStructureType`, a structure bundling
a category `C`, a forgetful functor `F : C ⥤ Type` which is faithful, preserves limits,
preserves filtered colimits, and reflects isomorphisms.  We keep it universe polymorphic as
`A : AlgebraicStructureType.{u, w}`, where `A.F : A.C ⥤ Type u` and the topological space
`X : TopCat.{u}` lives in the same universe `u`. -/

/-! ## Presheaf with values in `C` on a basis (Stacks 009P (1))

We model a presheaf with values in `A.C` on the basis `B` as a functor from the opposite of
the full subcategory `BasisCat B` of `Opens X` (ordered by inclusion), to `A.C`.  This is
exactly the "functor from the poset `B`, ordered by reverse inclusion, to `C`" formulation. -/

/-- A presheaf with values in `A.C` on the basis `B`. -/
abbrev CPresheafOnBasis (A : AlgebraicStructureType.{u, w}) (B : Set (Opens X)) :=
  (BasisCat B)ᵒᵖ ⥤ A.C

/-- The underlying set-valued presheaf-on-basis structure of a presheaf with values in `A.C`
on the basis `B`, obtained by post-composing with the forgetful functor `A.F`.  This lets us
reuse the library's set-valued sheaf-on-basis condition `IsSheafOnBasis`. -/
noncomputable def underlyingStruct (A : AlgebraicStructureType.{u, w})
    (P : CPresheafOnBasis A B) : PresheafOnBasisOpenStruct B where
  obj U hU := (P ⋙ A.F).obj (op ⟨U, hU⟩)
  res {U V} hU hV h :=
    (P ⋙ A.F).map (Quiver.Hom.op (⟨homOfLE h⟩ : (⟨V, hV⟩ : BasisCat B) ⟶ ⟨U, hU⟩))
  res_id {U} hU s := by
    have h1 : (Quiver.Hom.op (⟨homOfLE (le_refl U)⟩ : (⟨U, hU⟩ : BasisCat B) ⟶ ⟨U, hU⟩))
        = 𝟙 (op (⟨U, hU⟩ : BasisCat B)) := rfl
    rw [h1, CategoryTheory.Functor.map_id]
    rfl
  res_comp {U V W} hU hV hW hVU hWV s := by
    rw [← Functor.map_comp_apply]
    rfl

/-- The canonical set-valued presheaf-on-basis structure of a `Type`-valued presheaf
`P : (BasisCat B)ᵒᵖ ⥤ Type u` on the basis `B`.  Its objects and restriction maps are those of
`P` over basis opens.  This is the *full* data of `P` repackaged as a `PresheafOnBasisOpenStruct`
(objects **and** restriction maps), so the basis-sheaf condition `IsSheafOnBasis hB (typeStruct P)`
genuinely concerns `P`: a structure agreeing with `P` on objects alone would not, since the
restriction maps are what the gluing axiom quantifies over.  By construction
`underlyingStruct A P = typeStruct (P ⋙ A.F)` definitionally. -/
@[implicit_reducible]
noncomputable def typeStruct (P : (BasisCat B)ᵒᵖ ⥤ Type u) : PresheafOnBasisOpenStruct B where
  obj U hU := P.obj (op ⟨U, hU⟩)
  res {U V} hU hV h :=
    P.map (Quiver.Hom.op (⟨homOfLE h⟩ : (⟨V, hV⟩ : BasisCat B) ⟶ ⟨U, hU⟩))
  res_id {U} hU s := by
    have h1 : (Quiver.Hom.op (⟨homOfLE (le_refl U)⟩ : (⟨U, hU⟩ : BasisCat B) ⟶ ⟨U, hU⟩))
        = 𝟙 (op (⟨U, hU⟩ : BasisCat B)) := rfl
    rw [h1, CategoryTheory.Functor.map_id]
    rfl
  res_comp {U V W} hU hV hW hVU hWV s := by
    rw [← Functor.map_comp_apply]
    rfl

/-- The restriction map of `typeStruct P` from `U` to `V` is the map `P.map` along the inclusion
`V ≤ U`. -/
lemma typeStruct_res (P : (BasisCat B)ᵒᵖ ⥤ Type u) {U V : Opens X} (hU : U ∈ B) (hV : V ∈ B)
    (h : V ≤ U) (s : P.obj (op ⟨U, hU⟩)) :
    (typeStruct P).res hU hV h s =
      P.map (Quiver.Hom.op (⟨homOfLE h⟩ : (⟨V, hV⟩ : BasisCat B) ⟶ ⟨U, hU⟩)) s :=
  rfl

/-! ## Sheaf with values in `C` on a basis (Stacks 009J / 009P)

A presheaf with values in `A.C` on `B` is a *sheaf* iff its underlying presheaf of sets is a
sheaf on the basis `B`, i.e. satisfies the library predicate `IsSheafOnBasis`. -/

/-- A presheaf with values in `A.C` on `B` is a sheaf with values in `A.C` on `B`. -/
def IsCSheafOnBasis (A : AlgebraicStructureType.{u, w}) (hB : Opens.IsBasis B)
    (P : CPresheafOnBasis A B) : Prop :=
  IsSheafOnBasis hB (underlyingStruct A P)

/-- A sheaf with values in `A.C` on the basis `B`: a basis presheaf together with the sheaf
condition. -/
structure CSheafOnBasis (A : AlgebraicStructureType.{u, w}) (hB : Opens.IsBasis B) where
  /-- The underlying presheaf with values in `A.C` on `B`. -/
  presheaf : CPresheafOnBasis A B
  /-- The sheaf condition (on underlying sets). -/
  isSheaf : IsCSheafOnBasis A hB presheaf

/-! ## Presheaf and sheaf with values in `C` on `X`

A presheaf with values in `A.C` on `X` is just a `TopCat.Presheaf A.C X`, i.e. a functor
`(Opens X)ᵒᵖ ⥤ A.C`.  It is a sheaf iff its underlying presheaf of sets `G ⋙ A.F` is a sheaf
on `X` in the usual sense. -/

/-- A presheaf with values in `A.C` on `X` is a sheaf with values in `A.C` on `X`. -/
def IsCSheaf (A : AlgebraicStructureType.{u, w}) (G : TopCat.Presheaf A.C X) : Prop :=
  TopCat.Presheaf.IsSheaf (G ⋙ A.F)

/-- A sheaf with values in `A.C` on `X`. -/
structure CSheaf (A : AlgebraicStructureType.{u, w}) (X : TopCat.{u}) where
  /-- The underlying presheaf with values in `A.C` on `X`. -/
  presheaf : TopCat.Presheaf A.C X
  /-- The sheaf condition (on underlying sets). -/
  isSheaf : IsCSheaf A presheaf

/-! ## Restriction of an `X`-presheaf to the basis `B`

Restrict a presheaf with values in `A.C` on `X` to the basis by pre-composing with the
opposite of the inclusion functor `BasisCat B ⥤ Opens X`. -/

/-- The restriction `G|_B` of a presheaf with values in `A.C` on `X` to the basis `B`. -/
noncomputable def restrictToBasis (A : AlgebraicStructureType.{u, w})
    (B : Set (Opens X)) (G : TopCat.Presheaf A.C X) : CPresheafOnBasis A B :=
  (ObjectProperty.ι (fun U => U ∈ B : ObjectProperty (Opens X))).op ⋙ G

/-- Restricting a natural isomorphism of `X`-presheaves to the basis `B`. -/
noncomputable def restrictIso (A : AlgebraicStructureType.{u, w}) (B : Set (Opens X))
    {G H : TopCat.Presheaf A.C X} (Φ : G ≅ H) :
    restrictToBasis A B G ≅ restrictToBasis A B H :=
  Functor.isoWhiskerLeft (ObjectProperty.ι (fun U => U ∈ B : ObjectProperty (Opens X))).op Φ

/-! ## Stalk of a basis presheaf (Stacks 009P)

The full subcategory of `OpenNhds x` consisting of basis opens, together with the diagram
restricting a basis presheaf to it. The stalk is the (filtered) colimit of this diagram.
Because `A.C` has all filtered colimits and this diagram is filtered, the colimit exists. -/

/-- The basis opens that are neighbourhoods of `x`, as a full subcategory of `OpenNhds x`. -/
def BasisNhds (B : Set (Opens X)) (x : X) : ObjectProperty (OpenNhds x) :=
  fun U => (OpenNhds.inclusion x).obj U ∈ B

/-- The functor including the basis-neighbourhood category of `x` into `BasisCat B`. -/
noncomputable def basisNhdsToBasis (B : Set (Opens X)) (x : X) :
    (BasisNhds B x).FullSubcategory ⥤ BasisCat B where
  obj U := ⟨(OpenNhds.inclusion x).obj U.obj, U.property⟩
  map f := ⟨(OpenNhds.inclusion x).map f.hom⟩
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The diagram of a basis presheaf over the basis-open neighbourhoods of `x`. -/
noncomputable def stalkDiagram (A : AlgebraicStructureType.{u, w})
    (P : CPresheafOnBasis A B) (x : X) :
    (BasisNhds B x).FullSubcategoryᵒᵖ ⥤ A.C :=
  (basisNhdsToBasis B x).op ⋙ P

/-- The stalk of a basis presheaf `P` at a point `x`: the filtered colimit over the basis-open
neighbourhoods of `x`.  (It exists in `A.C` because `A.C` has filtered colimits; here we take
it under the corresponding `HasColimit` instance.) -/
noncomputable def stalk (A : AlgebraicStructureType.{u, w})
    (P : CPresheafOnBasis A B) (x : X) [HasColimit (stalkDiagram A P x)] : A.C :=
  colimit (stalkDiagram A P x)

/-! ## Reduction to the dense-subsite equivalence

Mathematical strategy, mirroring Stacks 009U but generic over a type of algebraic structure `A`.
The inclusion `basisInclusion B : BasisCat B ⥤ Opens X` is a *dense subsite*
inclusion for the Grothendieck topologies `basisGrothendieckTopology hB` on `BasisCat B` and
`Opens.grothendieckTopology X` on `Opens X` (these instances are already provided by the
library, `basisInclusion_isDenseSubsite`).  By the general dense-subsite theorem
(`CategoryTheory.Functor.IsDenseSubsite.sheafEquiv`), restriction along this inclusion is an
*equivalence of categories* between `A.C`-valued sheaves on `BasisCat B` and on `Opens X` —
**provided** the codomain `A.C` has limits of the relevant structured-arrow shapes.  That
hypothesis is supplied by `A.has_limits` (a `AlgebraicStructureType` has all small limits in
the universe of the space).  Concretely we obtain

  `csheafEquiv : Sheaf (basisGrothendieckTopology hB) A.C ≌ Sheaf (Opens.grothendieckTopology X)
  A.C`

whose `inverse` is *definitionally* the restriction (sheaf-pushforward) functor
(`sheafEquiv_inverse`).

The remaining work is purely *encoding glue* between this category-theoretic statement and the
elementary encodings of the sheaf conditions used above:

* `IsCSheaf A G` is `TopCat.Presheaf.IsSheaf (G ⋙ A.F)`, i.e. the *underlying set* presheaf
  is a sheaf.  Because `A.F` preserves limits and reflects isomorphisms (it is a
  `AlgebraicStructureType` forgetful functor), `Presheaf.isSheaf_iff_isSheaf_comp` gives that
  this is equivalent to `G` itself being an `A.C`-valued sheaf for `Opens.grothendieckTopology X`.

* `IsCSheafOnBasis A hB P` is `IsSheafOnBasis hB (underlyingStruct A P)`, the Stacks-009J
  set-valued basis-sheaf condition on the underlying sets.  Again by
  `isSheaf_iff_isSheaf_comp` this reduces to a *set-valued* basis-sheaf condition on
  `P ⋙ A.F`, and that set-valued basis condition is in turn equivalent to `P ⋙ A.F` being a
  sheaf for `basisGrothendieckTopology hB`; hence `P` is an `A.C`-valued sheaf for
  `basisGrothendieckTopology hB`.

* `restrictToBasis A B G` (precompose with the opposite inclusion) agrees with the
  category-theoretic restriction functor `(basisInclusion B).sheafPushforwardContinuous` on
  underlying presheaves, so the two notions of "restriction to the basis" coincide up to
  natural isomorphism.

Existence then comes from essential surjectivity of `csheafEquiv.functor` (equivalently:
applying `csheafEquiv.functor` to the basis sheaf `F` produces `Fext` with `Fext|_B ≅ F`), and
uniqueness comes from full faithfulness of the equivalence (`Functor.FullyFaithful` API:
`preimageIso`, `map_preimage`, `map_injective`). -/

section Bridges

variable {X : TopCat.{u}} {B : Set (Opens X)}

/-- **Helper (limits of structured-arrow shape).**  For a type of algebraic structure `A`,
the category `A.C` has limits of the structured-arrow shapes appearing in the dense-subsite
theorem.  This is the only "hypothesis on the codomain" required by
`Functor.IsDenseSubsite.instIsEquivalenceSheafSheafPushforwardContinuous`.

*Argument.*  The structured-arrow category `StructuredArrow Y (basisInclusion B).op` is a
`Category.{u, u}` (its objects and homs are built from the `u`-small posets `Opens X` /
`BasisCat B`).  `A.has_limits : HasLimitsOfSize.{u,u,u,w} A.C` provides `HasLimitsOfShape J A.C`
for every such `u`-small shape `J`.  In Lean this is `A.has_limits.has_limits_of_shape _`,
modulo aligning the ambient `Category A.C` instance with `A.inst_cat` (use
`haveI := A.inst_cat`). -/
lemma hasLimitsOfShape_structuredArrow (A : AlgebraicStructureType.{u, w})
    (Y : (Opens X)ᵒᵖ) :
    letI := A.inst_cat
    HasLimitsOfShape (StructuredArrow Y (basisInclusion B).op) A.C := by
  let := A.inst_cat
  exact A.has_limits.has_limits_of_shape _

/-- **The dense-subsite equivalence in `A.C`.**  Restriction along the basis inclusion is an
equivalence of categories between `A.C`-valued sheaves on the basis site and on `X`.

*Argument.*  `basisInclusion_isDenseSubsite hB` makes `basisInclusion B` an
`IsDenseSubsite (basisGrothendieckTopology hB) (Opens.grothendieckTopology X)`.  Feeding the
limit hypothesis `hasLimitsOfShape_structuredArrow A` into
`Functor.IsDenseSubsite.instIsEquivalenceSheafSheafPushforwardContinuous` discharges
`((basisInclusion B).sheafPushforwardContinuous A.C _ _).IsEquivalence`, and then
`Functor.IsDenseSubsite.sheafEquiv (basisInclusion B) (basisGrothendieckTopology hB)
(Opens.grothendieckTopology X) A.C` is the desired equivalence.  By `sheafEquiv_inverse`, its
`inverse` is *definitionally* the restriction functor. -/
noncomputable def csheafEquiv (A : AlgebraicStructureType.{u, w}) (hB : Opens.IsBasis B) :
    letI := A.inst_cat
    Sheaf (basisGrothendieckTopology hB) A.C ≌ Sheaf (Opens.grothendieckTopology X) A.C := by
  letI := A.inst_cat
  haveI : ∀ (Y : (Opens X)ᵒᵖ),
      HasLimitsOfShape (StructuredArrow Y (basisInclusion B).op) A.C :=
    hasLimitsOfShape_structuredArrow A
  exact Functor.IsDenseSubsite.sheafEquiv (basisGrothendieckTopology hB)
    (Opens.grothendieckTopology X) (basisInclusion B) A.C

/-- A presheaf on a small site with values in `A.C` is a sheaf iff its underlying set-valued
presheaf is. -/
private lemma isSheaf_comp_forget_iff (A : AlgebraicStructureType.{u, w}) {D : Type u}
    [SmallCategory D] (J : GrothendieckTopology D) (P : Dᵒᵖ ⥤ A.C) :
    letI := A.inst_cat
    Presheaf.IsSheaf J (P ⋙ A.F) ↔ Presheaf.IsSheaf J P := by
  let := A.inst_cat
  have := A.faithful
  have := A.has_limits
  have := A.preserves_limits
  have := A.reflects_iso
  exact (Presheaf.isSheaf_iff_isSheaf_comp J P A.F).symm

/-- **Bridge: `C`-valued sheaf condition on `X` ↔ set-valued sheaf condition.**  A presheaf
`G` with values in `A.C` on `X` is a sheaf (`IsCSheaf`, i.e. `G ⋙ A.F` is a set sheaf) iff
`G` is a sheaf for the Grothendieck topology `Opens.grothendieckTopology X` directly in `A.C`.

*Argument.*  Unfolding, `IsCSheaf A G = Presheaf.IsSheaf (Opens.grothendieckTopology X)
(G ⋙ A.F)`.  The forgetful functor `A.F` satisfies the hypotheses of
`Presheaf.isSheaf_iff_isSheaf_comp` (the category `A.C` has all limits via `A.has_limits`, `A.F`
preserves limits via `A.preserves_limits`, and `A.F` reflects isomorphisms via
`A.reflects_iso`).  That lemma states precisely
`Presheaf.IsSheaf J P ↔ Presheaf.IsSheaf J (P ⋙ A.F)`, which is the claimed equivalence with
`J := Opens.grothendieckTopology X` and `P := G`. -/
lemma isCSheaf_iff_isSheaf (A : AlgebraicStructureType.{u, w}) (G : TopCat.Presheaf A.C X) :
    letI := A.inst_cat
    IsCSheaf A G ↔ Presheaf.IsSheaf (Opens.grothendieckTopology X) G := by
  exact isSheaf_comp_forget_iff A (Opens.grothendieckTopology X) G

/-- Any two morphisms with the same (basis) source and target in `BasisCat B` are equal: the
homset is a subsingleton because `BasisCat B` is a full subcategory of the poset `Opens X`. -/
theorem basiscat_hom_ext {W U : Opens X} {hW : W ∈ B} {hU : U ∈ B}
    (f g : (⟨W, hW⟩ : BasisCat B) ⟶ ⟨U, hU⟩) : f = g := by
  obtain ⟨_⟩ := f
  obtain ⟨_⟩ := g
  congr 1
  apply Subsingleton.elim

/-- Mapping along an arrow of `BasisCat B` is the restriction map of `typeStruct P`. -/
private lemma map_op_eq_typeStruct_res (P : (BasisCat B)ᵒᵖ ⥤ Type u) {W T : BasisCat B}
    (f : W ⟶ T) (s : P.obj (op T)) :
    P.map f.op s = (typeStruct P).res T.property W.property (leOfHom f.hom) s :=
  congrArg (fun g : W ⟶ T => P.map g.op s) (basiscat_hom_ext _ _)

/-- Every open set is the supremum of the basis opens it contains. -/
lemma eq_iSup_basisSubsets (hB : Opens.IsBasis B) (U : Opens X) :
    U = ⨆ V : {V : Opens X // V ∈ B ∧ V ≤ U}, V.1 := by
  refine le_antisymm (fun y hy => ?_) (iSup_le fun V => V.2.2)
  obtain ⟨V', hV'B, hyV', hV'le⟩ := (Opens.isBasis_iff_nbhd.mp hB) hy
  exact Opens.mem_iSup.mpr ⟨⟨V', hV'B, hV'le⟩, hyV'⟩

/-- An open set contained in a union `⨆ k, V k` is covered by the basis opens lying both in it and
in one of the `V k`. -/
lemma le_iSup_basisSubsets_of_le_iSup (hB : Opens.IsBasis B) {W : Opens X} {K : Type*}
    (V : K → Opens X) (hW : W ≤ ⨆ k, V k) :
    W ≤ ⨆ W' : {W' : Opens X // W' ∈ B ∧ W' ≤ W ∧ ∃ k, W' ≤ V k}, W'.1 := by
  intro y hy
  obtain ⟨k, hyk⟩ := Opens.mem_iSup.mp (hW hy)
  obtain ⟨W', hW'B, hyW', hW'le⟩ :=
    (Opens.isBasis_iff_nbhd.mp hB) (show y ∈ V k ⊓ W from ⟨hyk, hy⟩)
  exact Opens.mem_iSup.mpr
    ⟨⟨W', hW'B, hW'le.trans inf_le_right, k, hW'le.trans inf_le_left⟩, hyW'⟩

/-- The sieve of a basis open `U` generated by a family of arrows whose sources cover `U` is a
covering sieve for the topology the basis site inherits from `X`. -/
lemma mem_basisGrothendieckTopology_ofArrows (hB : Opens.IsBasis B) {U : Opens X} {hU : U ∈ B}
    {I : Type*} (Uι : I → BasisCat B) (f : ∀ i, Uι i ⟶ (⟨U, hU⟩ : BasisCat B))
    (hcover : U ≤ ⨆ i, (Uι i).obj) :
    Sieve.ofArrows Uι f ∈ basisGrothendieckTopology hB ⟨U, hU⟩ := by
  rw [← (basisInclusion_isDenseSubsite hB).functorPushforward_mem_iff
    (X := ⟨U, hU⟩) (S := Sieve.ofArrows Uι f)]
  intro y hy
  obtain ⟨i, hyi⟩ := Opens.mem_iSup.mp (hcover (show y ∈ U from hy))
  exact ⟨(Uι i).obj, (basisInclusion B).map (f i), Sieve.image_mem_functorPushforward
    (basisInclusion B) (Sieve.ofArrows Uι f) (Sieve.ofArrows_mk Uι f i), hyi⟩

/-- The sources of the arrows of a covering sieve of a basis open `U` cover `U`. -/
lemma eq_iSup_of_mem_basisGrothendieckTopology (hB : Opens.IsBasis B) {U : Opens X} {hU : U ∈ B}
    (S : Sieve (⟨U, hU⟩ : BasisCat B)) (hS : S ∈ basisGrothendieckTopology hB ⟨U, hU⟩) :
    U = ⨆ i : Σ W : BasisCat B, {f : W ⟶ (⟨U, hU⟩ : BasisCat B) // S.arrows f}, i.1.obj := by
  have hpf : Sieve.functorPushforward (basisInclusion B) S ∈ Opens.grothendieckTopology X U :=
    ((basisInclusion_isDenseSubsite hB).functorPushforward_mem_iff
      (X := ⟨U, hU⟩) (S := S)).mpr hS
  refine le_antisymm (fun y hy => ?_) (iSup_le fun ⟨_, f, _⟩ => leOfHom f.hom)
  obtain ⟨_, _, ⟨Z, g, k, hSg, _⟩, hyW'⟩ := hpf y hy
  exact Opens.mem_iSup.mpr ⟨⟨Z, ⟨g, hSg⟩⟩, (leOfHom k) hyW'⟩

/-- Every arrow of a sieve generated by a family of arrows in `BasisCat B` has source contained in
the source of one of the generators. -/
lemma exists_le_of_ofArrows_arrows {T : BasisCat B} {I : Type*} (Uι : I → BasisCat B)
    (f : ∀ i, Uι i ⟶ T) {W : BasisCat B} {g : W ⟶ T}
    (hg : (Sieve.ofArrows Uι f).arrows g) : ∃ i, W.obj ≤ (Uι i).obj := by
  obtain ⟨i, a, _⟩ := (Sieve.mem_ofArrows_iff _ _ g).mp hg
  exact ⟨i, leOfHom a.hom⟩

/-- **Separatedness upgrade.**  Let `P` be separated for the basis topology and let `s₁`, `s₂` be
sections over basis opens `U₁`, `U₂` that agree on every member of a family of basis opens covering
`U₁ ⊓ U₂`.  Then `s₁` and `s₂` agree on *every* basis open contained in `U₁ ⊓ U₂`. -/
lemma res_eq_of_res_eq_on_cover (hB : Opens.IsBasis B) {P : (BasisCat B)ᵒᵖ ⥤ Type u}
    (hP : Presieve.IsSeparated (basisGrothendieckTopology hB) P)
    {U₁ U₂ : Opens X} (hU₁ : U₁ ∈ B) (hU₂ : U₂ ∈ B)
    {s₁ : (typeStruct P).obj U₁ hU₁} {s₂ : (typeStruct P).obj U₂ hU₂}
    {K : Type u} {V : K → Opens X} (hV : ∀ k, V k ∈ B) (hVle : ∀ k, V k ≤ U₁ ⊓ U₂)
    (hVcover : U₁ ⊓ U₂ ≤ ⨆ k, V k)
    (hagree : ∀ k, (typeStruct P).res hU₁ (hV k) ((hVle k).trans inf_le_left) s₁
      = (typeStruct P).res hU₂ (hV k) ((hVle k).trans inf_le_right) s₂)
    {W : Opens X} (hW : W ∈ B) (hW₁ : W ≤ U₁) (hW₂ : W ≤ U₂) :
    (typeStruct P).res hU₁ hW hW₁ s₁ = (typeStruct P).res hU₂ hW hW₂ s₂ := by
  set SW : Sieve (⟨W, hW⟩ : BasisCat B) :=
    Sieve.ofArrows (fun W' : {W' : Opens X // W' ∈ B ∧ W' ≤ W ∧ ∃ k, W' ≤ V k} =>
      (⟨W'.1, W'.2.1⟩ : BasisCat B)) (fun W' => ⟨homOfLE W'.2.2.1⟩) with hSWdef
  have hSW : SW ∈ basisGrothendieckTopology hB ⟨W, hW⟩ :=
    mem_basisGrothendieckTopology_ofArrows hB _ _
      (le_iSup_basisSubsets_of_le_iSup hB V fun y hy => hVcover ⟨hW₁ hy, hW₂ hy⟩)
  apply (hP SW hSW).ext
  intro Z f hf
  rw [hSWdef] at hf
  obtain ⟨_, h, _, hg, _⟩ := hf
  obtain ⟨⟨_, _, _, k, hk⟩⟩ := hg
  have hZW : Z.obj ≤ W := leOfHom f.hom
  have hZk : Z.obj ≤ V k := (leOfHom h.hom).trans hk
  rw [map_op_eq_typeStruct_res, map_op_eq_typeStruct_res,
      (typeStruct P).res_comp hU₁ hW Z.property hW₁ hZW s₁,
      (typeStruct P).res_comp hU₂ hW Z.property hW₂ hZW s₂,
      ← (typeStruct P).res_comp hU₁ (hV k) Z.property ((hVle k).trans inf_le_left) hZk s₁,
      ← (typeStruct P).res_comp hU₂ (hV k) Z.property ((hVle k).trans inf_le_right) hZk s₂,
      hagree k]

/-- Sections over a family of basis opens contained in `U` that agree on every basis open contained
in a pairwise intersection determine a compatible family of elements on the sieve they generate. -/
lemma exists_compatible_family_of_res_eq {P : (BasisCat B)ᵒᵖ ⥤ Type u} {U : Opens X} {hU : U ∈ B}
    {I : Type u} (Uι : I → Opens X) (hUι : ∀ i, Uι i ∈ B)
    (fι : ∀ i, (⟨Uι i, hUι i⟩ : BasisCat B) ⟶ (⟨U, hU⟩ : BasisCat B))
    (s : ∀ i, (typeStruct P).obj (Uι i) (hUι i))
    (hs : ∀ (i j : I) (W : Opens X) (hW : W ∈ B) (hWi : W ≤ Uι i) (hWj : W ≤ Uι j),
      (typeStruct P).res (hUι i) hW hWi (s i) = (typeStruct P).res (hUι j) hW hWj (s j)) :
    ∃ x : Presieve.FamilyOfElements P
        (Sieve.ofArrows (fun i => (⟨Uι i, hUι i⟩ : BasisCat B)) fι).arrows,
      x.Compatible ∧ ∀ {W : BasisCat B} (f : W ⟶ (⟨U, hU⟩ : BasisCat B)) (hf) (i : I)
        (hi : W.obj ≤ Uι i), x f hf = (typeStruct P).res (hUι i) W.property hi (s i) := by
  classical
  refine ⟨fun W f hf => (typeStruct P).res (hUι (exists_le_of_ofArrows_arrows _ _ hf).choose)
    W.property (exists_le_of_ofArrows_arrows _ _ hf).choose_spec
    (s (exists_le_of_ofArrows_arrows _ _ hf).choose), ?_, ?_⟩
  · intro Y₁ Y₂ Z g₁ g₂ f₁ f₂ h₁ h₂ _
    set i₁ := (exists_le_of_ofArrows_arrows _ _ h₁).choose with hi₁def
    set i₂ := (exists_le_of_ofArrows_arrows _ _ h₂).choose with hi₂def
    have hi₁ : Y₁.obj ≤ Uι i₁ := hi₁def ▸ (exists_le_of_ofArrows_arrows _ _ h₁).choose_spec
    have hi₂ : Y₂.obj ≤ Uι i₂ := hi₂def ▸ (exists_le_of_ofArrows_arrows _ _ h₂).choose_spec
    rw [map_op_eq_typeStruct_res, map_op_eq_typeStruct_res,
        (typeStruct P).res_comp (hUι i₁) Y₁.property Z.property hi₁ (leOfHom g₁.hom) (s i₁),
        (typeStruct P).res_comp (hUι i₂) Y₂.property Z.property hi₂ (leOfHom g₂.hom) (s i₂)]
    exact hs i₁ i₂ Z.obj Z.property ((leOfHom g₁.hom).trans hi₁) ((leOfHom g₂.hom).trans hi₂)
  · exact fun f hf i hi => hs _ i _ _ _ hi

/-- **Gluing from agreement on all basis opens.**  A sheaf on the basis site glues a family of
sections over a cover of a basis open `U` by basis opens, provided the sections agree on every
basis open contained in a pairwise intersection. -/
lemma existsUnique_glue_of_res_eq (hB : Opens.IsBasis B) {P : (BasisCat B)ᵒᵖ ⥤ Type u}
    (hP : Presieve.IsSheaf (basisGrothendieckTopology hB) P)
    {U : Opens X} (hU : U ∈ B) {I : Type u} (Uι : I → Opens X) (hUι : ∀ i, Uι i ∈ B)
    (hUle : ∀ i, Uι i ≤ U) (hcover : U ≤ ⨆ i, Uι i)
    (s : ∀ i, (typeStruct P).obj (Uι i) (hUι i))
    (hs : ∀ (i j : I) (W : Opens X) (hW : W ∈ B) (hWi : W ≤ Uι i) (hWj : W ≤ Uι j),
      (typeStruct P).res (hUι i) hW hWi (s i) = (typeStruct P).res (hUι j) hW hWj (s j)) :
    ∃! t : (typeStruct P).obj U hU, ∀ i, (typeStruct P).res hU (hUι i) (hUle i) t = s i := by
  set fι : ∀ i, ((⟨Uι i, hUι i⟩ : BasisCat B) ⟶ ⟨U, hU⟩) := fun i => ⟨homOfLE (hUle i)⟩
  obtain ⟨x, hxcompat, hxval⟩ := exists_compatible_family_of_res_eq Uι hUι fι s hs
  have hgenS : ∀ i, (Sieve.ofArrows (fun i => (⟨Uι i, hUι i⟩ : BasisCat B)) fι).arrows (fι i) :=
    fun i => Sieve.ofArrows_mk _ _ i
  have hSfor : Presieve.IsSheafFor P
      (Sieve.ofArrows (fun i => (⟨Uι i, hUι i⟩ : BasisCat B)) fι).arrows :=
    hP _ (mem_basisGrothendieckTopology_ofArrows hB _ _ hcover)
  refine ⟨hSfor.amalgamate x hxcompat, fun i => ?_, fun t' ht' => ?_⟩
  · rw [show (typeStruct P).res hU (hUι i) (hUle i) (hSfor.amalgamate x hxcompat)
          = P.map (fι i).op (hSfor.amalgamate x hxcompat) from rfl,
        hSfor.isAmalgamation hxcompat (fι i) (hgenS i),
        hxval (fι i) (hgenS i) i (le_refl (Uι i)), (typeStruct P).res_id (hUι i) (s i)]
  · refine hSfor.isSeparatedFor x t' _ (fun W f hf => ?_) (hSfor.isAmalgamation hxcompat)
    obtain ⟨i, hi⟩ := exists_le_of_ofArrows_arrows _ _ hf
    rw [hxval f hf i hi, map_op_eq_typeStruct_res, ← ht' i,
      (typeStruct P).res_comp hU (hUι i) W.property (hUle i) hi t']

/-- **Direction ⟸ of the basis-sheaf bridge: a Grothendieck-topology sheaf restricts to a
basis sheaf.**  If `P` is a sheaf for `basisGrothendieckTopology hB`, then `typeStruct P`
satisfies the Stacks-009J basis gluing axiom `IsSheafOnBasis`.

*Argument.*  Fix `U ∈ B`, a basis cover
`(Uᵢ)` of `U`, basis double-covers `Vᵢⱼₖ` of `Uᵢ ⊓ Uⱼ`, and sections `sᵢ` agreeing on the
`Vᵢⱼₖ` (`∗∗`).  The cover `(Uᵢ)` generates a covering sieve `S ∈ basisGrothendieckTopology hB`
of `⟨U, hU⟩` (covering-sieve correspondence, via
`Functor.IsDenseSubsite.functorPushforward_mem_iff` + the `Opens.grothendieckTopology` cover
description).  Step 1: upgrade `∗∗` to `∗` (agreement on *every* basis open `W ≤ Uᵢ ⊓ Uⱼ`) using
the *separated* half of the sheaf property of `P` on the covering sieve `S_W` of `W` generated
by the basis cover `(Vᵢⱼₖ ⊓ W)` refined to basis opens.  Step 2: `∗` makes the family `x` on
`S` determined by `(sᵢ)` `Presieve.FamilyOfElements.Compatible`; the sheaf property gives a
unique amalgamation `t` with `P(Uᵢ ≤ U) t = sᵢ`.  Step 3: uniqueness of the glue follows from
uniqueness of the amalgamation.  Amalgamation = glue is pure functoriality via `typeStruct`. -/
lemma isSheafOnBasis_of_isSheaf (hB : Opens.IsBasis B)
    (P : (BasisCat B)ᵒᵖ ⥤ Type u)
    (hP : Presheaf.IsSheaf (basisGrothendieckTopology hB) P) :
    IsSheafOnBasis hB (typeStruct P) := by
  rw [isSheaf_iff_isSheaf_of_type] at hP
  intro U hU I Uι hUι hcover J V hV hVcover s hagree
  have hUle : ∀ i, Uι i ≤ U := fun i => hcover ▸ le_iSup Uι i
  have hVle : ∀ i j k, V i j k ≤ Uι i ⊓ Uι j :=
    fun i j k => (le_iSup (V i j) k).trans (hVcover i j).ge
  exact existsUnique_glue_of_res_eq hB hP hU Uι hUι hUle hcover.le s
    fun i j W hW hWi hWj => res_eq_of_res_eq_on_cover hB hP.isSeparated (hUι i) (hUι j)
      (hV i j) (hVle i j) (hVcover i j).le (hagree i j) hW hWi hWj

/-- **Direction ⟹ of the basis-sheaf bridge: a basis sheaf extends to a Grothendieck-topology
sheaf.**  If `typeStruct P` satisfies `IsSheafOnBasis`, then `P` is a sheaf for
`basisGrothendieckTopology hB`.

*Argument.*  Use the `Type`-valued criterion
(`Presheaf.isSheaf_iff_isSheaf'` + `Presieve.IsSheafFor`): for every `⟨U, hU⟩` and every
covering sieve `S ∈ basisGrothendieckTopology hB`, index `S` by its basis-open members `(Uᵢ)`,
a basis cover of `U` (covering-sieve correspondence).  A compatible family `x` on `S` gives
sections `sᵢ := x` over the `Uᵢ` satisfying `∗` (agreement on every basis open below `Uᵢ ⊓ Uⱼ`),
hence `∗∗` for any chosen basis double-cover `(Vᵢⱼₖ)` of `Uᵢ ⊓ Uⱼ`.  Apply `IsSheafOnBasis` to
get a unique `t` with `P(Uᵢ ≤ U) t = sᵢ`; functoriality shows `t` amalgamates `x`, and the
`∃!`-uniqueness clause of `IsSheafOnBasis` gives uniqueness of the amalgamation. -/
lemma isSheaf_of_isSheafOnBasis (hB : Opens.IsBasis B)
    (P : (BasisCat B)ᵒᵖ ⥤ Type u)
    (hP : IsSheafOnBasis hB (typeStruct P)) :
    Presheaf.IsSheaf (basisGrothendieckTopology hB) P := by
  rw [isSheaf_iff_isSheaf_of_type]
  rintro ⟨U, hU⟩ S hS x hx
  -- Index the cover by the members of the covering sieve `S`.
  set I := Σ W : BasisCat B, {f : W ⟶ (⟨U, hU⟩ : BasisCat B) // S.arrows f}
  set Uι : I → Opens X := fun i => i.1.obj
  have hUι : ∀ i, Uι i ∈ B := fun i => i.1.property
  have hcover : U = ⨆ i, Uι i := eq_iSup_of_mem_basisGrothendieckTopology hB S hS
  set s : ∀ i, (typeStruct P).obj (Uι i) (hUι i) := fun ⟨_, f, hf⟩ => x f hf
  -- Double-cover `Uι i ⊓ Uι j` by *all* the basis opens it contains.
  set Vdc : (i j : I) → {V : Opens X // V ∈ B ∧ V ≤ Uι i ⊓ Uι j} → Opens X := fun _ _ k => k.1
  have hVdcmem : ∀ i j k, Vdc i j k ∈ B := fun _ _ ⟨_, hVB, _⟩ => hVB
  have hVdcle : ∀ i j k, Vdc i j k ≤ Uι i ⊓ Uι j := fun _ _ ⟨_, _, hVle⟩ => hVle
  have hVcover : ∀ i j, Uι i ⊓ Uι j = ⨆ k, Vdc i j k :=
    fun i j => eq_iSup_basisSubsets hB (Uι i ⊓ Uι j)
  -- The sections agree on each piece of the double-cover, by compatibility of `x`.
  have hagree : ∀ i j k,
      (typeStruct P).res (hUι i) (hVdcmem i j k) ((hVdcle i j k).trans inf_le_left) (s i)
        = (typeStruct P).res (hUι j) (hVdcmem i j k) ((hVdcle i j k).trans inf_le_right) (s j) := by
    rintro ⟨Wi, fi, hfi⟩ ⟨Wj, fj, hfj⟩ k
    exact hx (Y₁ := Wi) (Y₂ := Wj) (Z := ⟨Vdc _ _ k, hVdcmem _ _ k⟩)
      (g₁ := ⟨homOfLE ((hVdcle _ _ k).trans inf_le_left)⟩)
      (g₂ := ⟨homOfLE ((hVdcle _ _ k).trans inf_le_right)⟩)
      (f₁ := fi) (f₂ := fj) hfi hfj (basiscat_hom_ext _ _)
  obtain ⟨t, ht, htuniq⟩ := hP hU Uι hUι hcover Vdc hVdcmem hVcover s hagree
  exact ⟨t, fun _ f hf => ht ⟨_, f, hf⟩, fun t' ht' => htuniq _ fun ⟨_, f, hf⟩ => ht' f hf⟩

/-- **Bridge: the set-valued basis-sheaf condition `IsSheafOnBasis` ↔ the Grothendieck-topology
sheaf condition on the basis site (set-valued).**  For a set-valued presheaf
`P : (BasisCat B)ᵒᵖ ⥤ Type u`, the Stacks-009J basis-sheaf condition on the associated
`PresheafOnBasisOpenStruct` is equivalent to `P` being a sheaf for `basisGrothendieckTopology hB`.

*Argument.*  Both conditions express the same gluing axiom.  `basisGrothendieckTopology hB` is
the topology induced on `BasisCat B` by `Opens.grothendieckTopology X` along the (cover-dense)
inclusion; its covering sieves of `U ∈ B` are generated by families `{Uᵢ → U}` of basis opens
with `U = ⨆ Uᵢ`.  The Mathlib sheaf condition for such a topology (equalizer / unique-amalgam
form) says: every compatible family of sections over a covering family has a unique
amalgamation.  This is exactly the `IsSheafOnBasis` condition of `PresheafOnBasisOpenStruct`,
once one observes that compatibility "on the chosen double-covers `Uᵢ ⊓ Uⱼ = ⨆ₖ V i j k` by
basis opens" is equivalent to compatibility "on the sieve-theoretic pullbacks", because the
basis opens contained in `Uᵢ ⊓ Uⱼ` are cofinal (every open, in particular `Uᵢ ⊓ Uⱼ`, is a union
of basis opens — that is what `Opens.IsBasis B` provides) and the presheaf is determined on
basis opens.  The two directions are `isSheafOnBasis_of_isSheaf` and
`isSheaf_of_isSheafOnBasis`.

Note that the left-hand side must be stated for the canonical `typeStruct P`, which carries the
restriction maps of `P`; a variant quantifying only over structures agreeing with `P` on objects
is strictly weaker and the equivalence fails for it. -/
lemma isSheafOnBasis_iff_isSheaf_type (hB : Opens.IsBasis B)
    (P : (BasisCat B)ᵒᵖ ⥤ Type u) :
    IsSheafOnBasis hB (typeStruct P) ↔ Presheaf.IsSheaf (basisGrothendieckTopology hB) P :=
  ⟨isSheaf_of_isSheafOnBasis hB P, isSheafOnBasis_of_isSheaf hB P⟩

/-- **Bridge: `C`-valued basis-sheaf condition ↔ Grothendieck-topology sheaf condition on the
basis site.**  `IsCSheafOnBasis A hB P` (the underlying-set Stacks-009J condition) holds iff
`P` is a sheaf for `basisGrothendieckTopology hB` directly in `A.C`.

*Argument.*  `IsCSheafOnBasis A hB P = IsSheafOnBasis hB (underlyingStruct A P)`, and
`underlyingStruct A P` is by definition the `PresheafOnBasisOpenStruct` whose objects are
`(P ⋙ A.F).obj (op ⟨U, hU⟩)` with the induced restriction maps.  By
`isSheafOnBasis_iff_isSheaf_type` (applied to the set presheaf `P ⋙ A.F`, which matches
`underlyingStruct A P` on objects by construction), this is equivalent to `P ⋙ A.F` being a
sheaf for `basisGrothendieckTopology hB`.  By `Presheaf.isSheaf_iff_isSheaf_comp` (with `s :=
A.F`, hypotheses from `A.has_limits` / `A.preserves_limits` / `A.reflects_iso`), this is
in turn equivalent to `P` being an `A.C`-valued sheaf for `basisGrothendieckTopology hB`. -/
lemma isCSheafOnBasis_iff_isSheaf (A : AlgebraicStructureType.{u, w}) (hB : Opens.IsBasis B)
    (P : CPresheafOnBasis A B) :
    letI := A.inst_cat
    IsCSheafOnBasis A hB P ↔ Presheaf.IsSheaf (basisGrothendieckTopology hB) P := by
  rw [IsCSheafOnBasis, show underlyingStruct A P = typeStruct (P ⋙ A.F) from rfl,
    isSheafOnBasis_iff_isSheaf_type hB (P ⋙ A.F)]
  exact isSheaf_comp_forget_iff A (basisGrothendieckTopology hB) P

/-- **Bridge: `restrictToBasis` agrees with the dense-subsite restriction functor.**  For a
sheaf `G` on `X` (as an object of `Sheaf (Opens.grothendieckTopology X) A.C`), the basis
presheaf `restrictToBasis A B G.val` equals the underlying presheaf of the categorical
restriction `csheafEquiv.inverse.obj G` (which by `sheafEquiv_inverse` is the
sheaf-pushforward along `basisInclusion B`).

*Argument.*  Both are "precompose with the opposite inclusion `BasisCat B ⥤ Opens X`":
`restrictToBasis` is defined as `(ObjectProperty.ι (· ∈ B)).op ⋙ G`, and the dense-subsite
restriction / `sheafPushforwardContinuous` of `basisInclusion B = ObjectProperty.ι (· ∈ B)` is
also "compose with `(basisInclusion B).op`" on underlying presheaves.  Since `basisInclusion B`
is *reducibly* `ObjectProperty.ι (· ∈ B)`, the two presheaves are literally equal. -/
lemma restrictToBasis_eq_pushforward (A : AlgebraicStructureType.{u, w})
    (G : TopCat.Presheaf A.C X) :
    letI := A.inst_cat
    restrictToBasis A B G = (basisInclusion B).op ⋙ G := by
  let := A.inst_cat
  rfl

end Bridges

/-! ## Existence and uniqueness sub-lemmas

The two halves of the main theorem, each obtained from the category equivalence `csheafEquiv`
together with the encoding bridges above. -/

section ExistenceUniqueness

variable {X : TopCat.{u}} {B : Set (Opens X)}

/-- Cancelling an isomorphism on the right: `f ≪≫ g = h` iff `f = h ≪≫ g.symm`. -/
lemma trans_eq_iff_eq_trans_symm {C : Type*} [Category C] {Y Z W : C}
    (f : Y ≅ Z) (g : Z ≅ W) (h : Y ≅ W) : f ≪≫ g = h ↔ f = h ≪≫ g.symm := by
  refine ⟨fun hfg => ?_, fun hfg => ?_⟩
  · rw [← hfg, Iso.trans_assoc, Iso.self_symm_id, Iso.trans_refl]
  · rw [hfg, Iso.trans_assoc, Iso.symm_self_id, Iso.trans_refl]

/-- Let `Uf` and `Rf` be fully faithful functors out of a category `𝒜`, and let `t` carry an
isomorphism between objects of the `Uf`-image to one between the corresponding objects of the
`Rf`-image, compatibly with `Uf` and `Rf` on isomorphisms.  Then every isomorphism
`Rf.obj a ≅ Rf.obj b` is `t` of a unique isomorphism `Uf.obj a ≅ Uf.obj b`. -/
lemma existsUnique_iso_of_fullyFaithful {𝒜 ℬ 𝒞 : Type*} [Category 𝒜] [Category ℬ] [Category 𝒞]
    {Uf : 𝒜 ⥤ ℬ} {Rf : 𝒜 ⥤ 𝒞} (hU : Uf.FullyFaithful) (hR : Rf.FullyFaithful) {a b : 𝒜}
    (t : (Uf.obj a ≅ Uf.obj b) → (Rf.obj a ≅ Rf.obj b))
    (ht : ∀ Φ : a ≅ b, t (Uf.mapIso Φ) = Rf.mapIso Φ) (K : Rf.obj a ≅ Rf.obj b) :
    ∃! Φ : Uf.obj a ≅ Uf.obj b, t Φ = K := by
  refine ⟨Uf.mapIso (hR.preimageIso K), (ht _).trans (hR.isoEquiv.apply_symm_apply K),
    fun Φ hΦ => ?_⟩
  have hΦ' : Uf.mapIso (hU.preimageIso Φ) = Φ := hU.isoEquiv.apply_symm_apply Φ
  have hK : Rf.mapIso (hU.preimageIso Φ) = K := by rw [← ht, hΦ']; exact hΦ
  exact hΦ'.symm.trans (congrArg Uf.mapIso
    (hR.isoEquiv.injective (hK.trans (hR.isoEquiv.apply_symm_apply K).symm)))

/-- **Existence half of Stacks 009Q.**  There is a sheaf `Fext` on `X` whose restriction to the
basis is isomorphic to `F`.

*Argument.*  Package `F` as an object `Fb : Sheaf (basisGrothendieckTopology hB) A.C`: its
underlying presheaf is `F.presheaf`, and the Grothendieck-topology sheaf condition holds by
`isCSheafOnBasis_iff_isSheaf` applied to `F.isSheaf`.  Set
`Sext := csheafEquiv A hB |>.functor.obj Fb : Sheaf (Opens.grothendieckTopology X) A.C`.
Define `Fext.presheaf := Sext.val` and obtain `Fext.isSheaf : IsCSheaf A Sext.val` from
`isCSheaf_iff_isSheaf` applied to `Sext.cond` (an object of the sheaf category is, by
definition, a presheaf together with the sheaf condition).  For `θ`: the equivalence's unit
gives `Fb ≅ csheafEquiv.inverse.obj Sext = csheafEquiv.inverse.obj (csheafEquiv.functor.obj Fb)`
via `csheafEquiv.unitIso`; since `csheafEquiv.inverse` is (by `sheafEquiv_inverse`) the
restriction `sheafPushforwardContinuous`, taking underlying presheaves (`Sheaf.forget` /
`.val`) and using `restrictToBasis_eq_pushforward` turns this into a natural isomorphism
`restrictToBasis A B Fext.presheaf ≅ F.presheaf`, i.e. `θ`. -/
lemma extension_exists (A : AlgebraicStructureType.{u, w}) (hB : Opens.IsBasis B)
    (F : CSheafOnBasis A hB) :
    ∃ (Fext : CSheaf A X), Nonempty (restrictToBasis A B Fext.presheaf ≅ F.presheaf) := by
  let := A.inst_cat
  let Fb : Sheaf (basisGrothendieckTopology hB) A.C :=
    ⟨F.presheaf, (isCSheafOnBasis_iff_isSheaf A hB F.presheaf).mp F.isSheaf⟩
  let Sext : Sheaf (Opens.grothendieckTopology X) A.C := (csheafEquiv A hB).functor.obj Fb
  let Fext : CSheaf A X :=
    { presheaf := Sext.obj
      isSheaf := (isCSheaf_iff_isSheaf A Sext.obj).mpr Sext.property }
  exact ⟨Fext, ⟨((sheafToPresheaf _ _).mapIso ((csheafEquiv A hB).unitIso.app Fb)).symm⟩⟩

/-- **Uniqueness half of Stacks 009Q.**  Given *any* sheaf `Fext` on `X` together with an
isomorphism `θ : restrictToBasis A B Fext.presheaf ≅ F.presheaf`, every other sheaf `G` on `X`
equipped with `η : restrictToBasis A B G.presheaf ≅ F.presheaf` admits a *unique* isomorphism
`Φ : G.presheaf ≅ Fext.presheaf` with `restrictIso A B Φ ≪≫ θ = η`.

*Argument.*  Package `Fext` and `G` as objects `Sext`, `Sg` of
`Sheaf (Opens.grothendieckTopology X) A.C` (sheaf conditions via `isCSheaf_iff_isSheaf`).  The
maps `θ`, `η` are isomorphisms of basis presheaves which, via `restrictToBasis_eq_pushforward`
and `sheafEquiv_inverse`, are precisely isomorphisms
`(csheafEquiv A hB).inverse.obj Sg ≅ Fb` and `(csheafEquiv A hB).inverse.obj Sext ≅ Fb`
(where `Fb` packages `F`).  Composing, `η ≪≫ θ.symm` is an isomorphism
`(csheafEquiv A hB).inverse.obj Sg ≅ (csheafEquiv A hB).inverse.obj Sext`.  Because
`csheafEquiv.inverse` is part of an equivalence it is fully faithful
(`Equivalence.fullyFaithfulInverse`), so `Functor.FullyFaithful.preimageIso` lifts this to a
*unique* isomorphism `Φ' : Sg ≅ Sext` of sheaves, hence a unique iso
`Φ : G.presheaf ≅ Fext.presheaf` of underlying presheaves (the forgetful functor
`Sheaf → presheaf` is fully faithful).  Uniqueness: any `Φ` with `restrictIso A B Φ ≪≫ θ = η`
maps, under `csheafEquiv.inverse` (= restriction), to `η ≪≫ θ.symm`; full faithfulness
(`Functor.FullyFaithful.isoEquiv`, the bijection between isomorphisms and their images) forces
`Φ` to equal the lift, giving the `∃!`. -/
@[ega "0 3.2.5" "partial"]
lemma extension_uniqueness (A : AlgebraicStructureType.{u, w}) (hB : Opens.IsBasis B)
    (F : CSheafOnBasis A hB)
    (Fext : CSheaf A X) (θ : restrictToBasis A B Fext.presheaf ≅ F.presheaf)
    (G : CSheaf A X) (η : restrictToBasis A B G.presheaf ≅ F.presheaf) :
    ∃! Φ : G.presheaf ≅ Fext.presheaf, restrictIso A B Φ ≪≫ θ = η := by
  let := A.inst_cat
  let Sext : Sheaf (Opens.grothendieckTopology X) A.C :=
    ⟨Fext.presheaf, (isCSheaf_iff_isSheaf A Fext.presheaf).mp Fext.isSheaf⟩
  let Sg : Sheaf (Opens.grothendieckTopology X) A.C :=
    ⟨G.presheaf, (isCSheaf_iff_isSheaf A G.presheaf).mp G.isSheaf⟩
  exact (existsUnique_congr fun Φ =>
    trans_eq_iff_eq_trans_symm (restrictIso A B Φ) θ η).mpr <| existsUnique_iso_of_fullyFaithful
    (Uf := sheafToPresheaf (Opens.grothendieckTopology X) A.C)
    (Rf := (csheafEquiv A hB).inverse ⋙ sheafToPresheaf (basisGrothendieckTopology hB) A.C)
    (fullyFaithfulSheafToPresheaf _ _)
    (((csheafEquiv A hB).fullyFaithfulInverse).comp (fullyFaithfulSheafToPresheaf _ _))
    (a := Sg) (b := Sext) (restrictIso A B) (fun _ => rfl) (η ≪≫ θ.symm)

end ExistenceUniqueness

/-! ## Main Statement (Stacks 009Q / Lemma 6.30.9)

Existence and uniqueness (up to unique isomorphism) of the extension of a sheaf on a basis to
a sheaf on the whole space. -/

/-- **Extension of a sheaf on a basis (Stacks 009Q / Lemma 6.30.9).**

Let `(C, F)` be a type of algebraic structure, `B` a basis for `X`, and `F` a sheaf with
values in `C` on `B`.  Then there is a sheaf `Fᵉˣᵗ` with values in `C` on `X`, unique up to
unique isomorphism, whose restriction to `B` is isomorphic to `F`.

* *Existence*: there is a sheaf `Fext` on `X` together with an isomorphism
  `θ : Fext|_B ≅ F.presheaf`.
* *Uniqueness*: any sheaf `G` on `X` equipped with an isomorphism `η : G|_B ≅ F.presheaf`
  admits a unique isomorphism `Φ : G ≅ Fext` compatible with the identifications over `B`,
  i.e. `(restrictIso Φ) ≪≫ θ = η`. -/
@[stacks 009Q, ega "0 3.2.5" "1st para: F ≅ F₁'"]
theorem extension_of_sheaf_on_basis
    (A : AlgebraicStructureType.{u, w}) (hB : Opens.IsBasis B)
    (F : CSheafOnBasis A hB) :
    ∃ (Fext : CSheaf A X)
      (θ : restrictToBasis A B Fext.presheaf ≅ F.presheaf),
      ∀ (G : CSheaf A X) (η : restrictToBasis A B G.presheaf ≅ F.presheaf),
        ∃! Φ : G.presheaf ≅ Fext.presheaf,
          restrictIso A B Φ ≪≫ θ = η := by
  -- Assemble from the two named sub-lemmas.  `extension_exists` provides `Fext` and (the
  -- nonempty class of) `θ`; `extension_uniqueness` provides, for that `Fext`/`θ`, the universal
  -- property for every competitor `(G, η)`.
  obtain ⟨Fext, ⟨θ⟩⟩ := extension_exists A hB F
  exact ⟨Fext, θ, extension_uniqueness A hB F Fext θ⟩

end Stacks.BasisExtension
