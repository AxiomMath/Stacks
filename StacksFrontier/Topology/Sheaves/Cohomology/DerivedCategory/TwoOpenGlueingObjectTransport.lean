module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.RestrictionComparisonCoherence
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.TwoOpenGlueingInput
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.OpenImmersionRestrictionNaturality
public import StacksFrontier.Topology.Sheaves.Cohomology.GlueingComplexes.TwoOpens

/-!
# Transporting the glueing lemma for two opens into Situation 0D67

Let `(X, 𝒪_X)` be a ringed space and `S` a system of locally given derived objects on it, as in
Situation 0D67.  The glueing lemma [Stacks, Tag 08DG] is
`Stacks.Cohomology.GlueingComplexes.exists_glueing`: it is stated for a Cartesian square of open
*immersions of ringed spaces* and for derived pullback.  Situation 0D67 instead carries abstract
restriction functors `Stacks.DerivedGlueing.LocallyGiven.restriction` between the categories
`Stacks.DerivedGlueing.OpenDerivedCategory X U`, pinned to extension by zero followed by
restriction.  This file supplies the dictionary between the two vocabularies, builds the
Cartesian square that the glueing lemma needs at two opens of a space, and deduces the *object*
part of the two-open glueing statement of Situation 0D67, with nothing assumed.  The full
statement, compatibility clause included, is reduced to the case of the open `⊤`.

## Main definitions

* `Stacks.DerivedGlueing.LocallyGiven.restrictionIsoDerivedRestrict`: **the dictionary.** The
  restriction displayed by a system, from an open `O` to a smaller open `U`, is extension by zero
  along `O` followed by the derived pullback along the open immersion
  `j_U : (U, 𝒪_X|_U) ⟶ (X, 𝒪_X)` — the functor Tag 08DG is stated in.
* `Stacks.DerivedGlueing.topExtensionDerivedEquivalence`: the derived category of the open
  subspace `⊤` is the derived category of `𝒪_X`-modules on `X`, by extension by zero along `⊤`.
* `Stacks.DerivedGlueing.restrictIncl`: the inclusion of one open subspace of a ringed space into
  a larger one, as a morphism of ringed spaces.
* `Stacks.DerivedGlueing.overlapIsoOfRestriction`: the overlap identification of Situation 0D67,
  read as the glueing datum of Tag 08DG.
* `Stacks.DerivedGlueing.TwoOpenGlueingOver`: the two-open glueing problem of Situation 0D67,
  with the glued object sought over a prescribed open `P` containing both members.
* `Stacks.DerivedGlueing.TwoOpenGlueingObjectsOver`: the same problem with its compatibility
  clause dropped.

## Main results

* `Stacks.DerivedGlueing.restrictedRingSheaf_eq` and
  `Stacks.DerivedGlueing.openDerivedCategory_eq`: the two spellings of the structure sheaf of an
  open subspace, and hence the two spellings of its derived category of modules, agree.
* `Stacks.DerivedGlueing.derivedRestrictJShriekIso`: restricting to `U` the extension by zero
  from `U` is the identity, on unbounded derived categories.
* `Stacks.DerivedGlueing.isPullback_restrictIncl`: **the Cartesian square.** The open subspace
  `U ∩ V`, with its two inclusions, is the pullback of the open immersions of the open subspaces
  `U` and `V` in the category of ringed spaces.  This is the hypothesis of Tag 08DG at two opens
  of a space.
* `Stacks.DerivedGlueing.twoOpenGlueingObjectsOver_top` and
  `Stacks.DerivedGlueing.exists_glueing_two_opens_objects`: **the glued object exists**, over `⊤`
  and hence over `U ∪ V`, with nothing assumed.  This is Tag 08DG transported.
* `Stacks.DerivedGlueing.twoOpenGlueingOver_of_le`: **the reduction of the full statement.** A
  solution of the two-open glueing problem, compatibility clause included, over a larger open
  restricts to one over a smaller open containing both members.
* `Stacks.DerivedGlueing.exists_glueing_two_opens_of_top`: the two-open glueing statement of
  Situation 0D67, deduced from its case at `⊤`.

## Implementation notes

Two spellings of the structure sheaf of an open subspace meet here,
`structureSheafRing (X.restrict U.isOpenEmbedding)` and
`ExtensionByZeroModules.resRing U (structureSheafRing X)`.  They are definitionally equal, both
semireducible, so a goal mixing them is not type-correct at `instances` transparency: the two
routes to the `CategoryTheory.Preadditive` instance of the category of modules on `U` differ, and
the `CategoryTheory.Functor.Additive` instance found for one is not the one declared against the
other.  The crossing is therefore paid in term mode, where the conversion check runs at default
transparency — in `Stacks.DerivedGlueing.restrictionIsoDerivedRestrict` and
`Stacks.DerivedGlueing.derivedRestrictJShriekIso`, each a composite of isomorphisms with no
tactic in it.

The reduction `Stacks.DerivedGlueing.twoOpenGlueingOver_of_le` is a diagram chase among objects
of three different derived categories, and the rewriting tactics are unreliable there: a goal
that prints the pattern `Category.assoc` can still be reported as having no occurrence of it.
The chase is therefore isolated as `Stacks.DerivedGlueing.glueTransport_eq`, stated in a single
arbitrary category with every object and every morphism a variable, and applied with `exact`.

Mathlib builds the factorization of a morphism through an open immersion only for *presheafed*
spaces (`AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.lift`).  Morphisms of sheafed spaces
are morphisms of the underlying presheafed spaces — the category of sheafed spaces is a
`CategoryTheory.InducedCategory` — so `Stacks.DerivedGlueing.restrictIncl` and
`Stacks.DerivedGlueing.infLift` transport that factorization with
`CategoryTheory.InducedCategory.homMk`, and the equations between the transported morphisms are
proved by `CategoryTheory.InducedCategory.hom_ext`.

## References

* [Stacks Project, Tag 08DG](https://stacks.math.columbia.edu/tag/08DG)
* [Stacks Project, Tag 0D5S](https://stacks.math.columbia.edu/tag/0D5S)
* [Stacks Project, Tag 0D67](https://stacks.math.columbia.edu/tag/0D67)
* [Stacks Project, Tag 0D6A](https://stacks.math.columbia.edu/tag/0D6A)
* [Stacks Project, Tag 00AB](https://stacks.math.columbia.edu/tag/00AB)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open ExtensionByZeroModules RingedSpaceModuleAdjunction

namespace Stacks.DerivedGlueing

universe u

attribute [local instance 10000] HasDerivedCategory.standard

variable {X : RingedSpace.{u, u}}

/-! ### The two spellings of the structure sheaf of an open subspace -/

/-- **The sheaf of rings underlying the restriction of the structure sheaf of `X` to `U` is the
structure sheaf of the open subspace `U`.** The restriction `𝒪_X|_U` used by extension by zero
and the structure sheaf of the ringed space `X.restrict U.isOpenEmbedding` used by the derived
pullback are two spellings of one sheaf of rings. -/
theorem restrictedRingSheaf_eq (U : Opens X.carrier) :
    restrictedRingSheaf X U = structureSheafRing (X.restrict U.isOpenEmbedding) :=
  rfl

/-- **The derived category of an open subspace in Situation 0D67 is the derived category of
modules on that open subspace as a ringed space.** This is
`Stacks.DerivedGlueing.restrictedRingSheaf_eq` carried through the derived category. -/
theorem openDerivedCategory_eq (U : Opens X.carrier) :
    OpenDerivedCategory X U =
      Stacks.Cohomology.GlueingComplexes.DerivedModules (X.restrict U.isOpenEmbedding) :=
  rfl

/-- **Restriction from `O` to `U ≤ O` is extension by zero along `O` followed by restriction to
`U`.** This holds by definition of `Stacks.DerivedGlueing.openModuleRestriction`. -/
theorem openModuleRestriction_eq_jShriek_comp_jStar (O U : Opens X.carrier) (hUO : U ≤ O) :
    openModuleRestriction X U O hUO =
      jShriek O (underlyingRingSheaf X) ⋙ jStar U (underlyingRingSheaf X) :=
  rfl

/-! ### The dictionary between the two vocabularies -/

/-- The unit of `j_! ⊣ j^*` is invertible: extension by zero from `U` followed by restriction
to `U` is the identity on modules over the open subspace. -/
def jShriekUnitIso (U : Opens X.carrier) :
    𝟭 (SheafOfModules.{u} (restrictedRingSheaf X U)) ≅
      jShriek U (underlyingRingSheaf X) ⋙ jStar U (underlyingRingSheaf X) :=
  @asIso _ _ _ _ (jShriekAdjunction U (underlyingRingSheaf X)).unit
    (isIso_jShriekAdjunction_unit U (underlyingRingSheaf X))

open Stacks.Cohomology.DerivedOpenImmersion in
/-- **The restriction displayed by a system of locally given derived objects is derived
restriction along an open immersion of ringed spaces.** For an open `O` and an open `U ≤ O`, the
functor `Stacks.DerivedGlueing.LocallyGiven.restriction` from `O` to `U` is: extend by zero
along `O` to the whole of `X`, then take the derived pullback along the canonical open immersion
`j_U : (U, 𝒪_X|_U) ⟶ (X, 𝒪_X)`, built from
`Stacks.Cohomology.GlueingComplexes.derivedRestrict`. -/
def LocallyGiven.restrictionIsoDerivedRestrict (S : LocallyGiven X) (O U : Opens X.carrier)
    (hUO : U ≤ O) :
    S.restriction U O hUO ≅
      (jShriek O (underlyingRingSheaf X)).mapDerivedCategory ⋙
        Stacks.Cohomology.GlueingComplexes.derivedRestrict
          (X.ofRestrict U.isOpenEmbedding) :=
  restrictionIsoMapDerivedCategory S U O hUO ≪≫
    (mapDerivedCategoryCompIso (jShriek O (underlyingRingSheaf X))
      (jStar U (underlyingRingSheaf X))).symm ≪≫
    Functor.isoWhiskerLeft (jShriek O (underlyingRingSheaf X)).mapDerivedCategory
      (derivedPullbackOpenRestrictionIso X U).symm

open Stacks.Cohomology.DerivedOpenImmersion in
/-- **Restricting to `U` the extension by zero from `U` is the identity**, on unbounded derived
categories of modules.  Both functors are exact, so this is the derived category of the unit
isomorphism `Stacks.DerivedGlueing.jShriekUnitIso`, with derived restriction identified with the
degreewise one by
`Stacks.Cohomology.DerivedOpenImmersion.derivedPullbackOpenRestrictionIso`. -/
def derivedRestrictJShriekIso (U : Opens X.carrier) :
    (jShriek U (underlyingRingSheaf X)).mapDerivedCategory ⋙
        Stacks.Cohomology.GlueingComplexes.derivedRestrict
          (X.ofRestrict U.isOpenEmbedding) ≅
      𝟭 (OpenDerivedCategory X U) :=
  Functor.isoWhiskerLeft (jShriek U (underlyingRingSheaf X)).mapDerivedCategory
      (derivedPullbackOpenRestrictionIso X U) ≪≫
    mapDerivedCategoryCompIso (jShriek U (underlyingRingSheaf X))
      (jStar U (underlyingRingSheaf X)) ≪≫
    mapDerivedCategoryCongr (jShriekUnitIso U).symm ≪≫
    Stacks.Homology.mapDerivedCategoryIdIso

/-! ### The open subspace `⊤` -/

/-- The counit of `j_! ⊣ j^*` at the open `⊤` is invertible: there is no point off `⊤` at which
the stalk of a sheaf of modules would have to vanish, so
`ExtensionByZeroModules.counit_isIso_of_stalk_isZero` applies to every sheaf of modules. -/
theorem isIso_topJShriekAdjunction_counit :
    IsIso (jShriekAdjunction (⊤ : Opens X.carrier) (underlyingRingSheaf X)).counit := by
  have h : ∀ G : SheafOfModules.{u} (underlyingRingSheaf X),
      IsIso ((jShriekAdjunction (⊤ : Opens X.carrier)
        (underlyingRingSheaf X)).counit.app G) := by
    intro G
    refine counit_isIso_of_stalk_isZero _ _ G fun x hx => ?_
    simp at hx
  exact NatIso.isIso_of_isIso_app _

/-- **Extension by zero along `⊤` is an equivalence on modules**, with quasi-inverse restriction
to `⊤`: its unit is invertible for every open
(`ExtensionByZeroModules.isIso_jShriekAdjunction_unit`) and its counit is invertible at `⊤`
(`Stacks.DerivedGlueing.isIso_topJShriekAdjunction_counit`).  This is the case `U = ⊤` of
[Stacks, Tag 00AB]: the essential image of `j_!` is cut out by vanishing of stalks off `U`, which
at `U = ⊤` is no condition. -/
def topExtensionModuleEquivalence :
    SheafOfModules.{u} (restrictedRingSheaf X ⊤) ≌ SheafOfModules.{u} (underlyingRingSheaf X) :=
  haveI := isIso_topJShriekAdjunction_counit (X := X)
  haveI := isIso_jShriekAdjunction_unit (⊤ : Opens X.carrier) (underlyingRingSheaf X)
  (jShriekAdjunction (⊤ : Opens X.carrier) (underlyingRingSheaf X)).toEquivalence

/-- Restriction to `⊤` followed by extension by zero along `⊤` is the identity, on unbounded
derived categories: the derived category of the counit isomorphism. -/
def topJShriekCounitDerivedIso :
    (jStar (⊤ : Opens X.carrier) (underlyingRingSheaf X)).mapDerivedCategory ⋙
        (jShriek (⊤ : Opens X.carrier) (underlyingRingSheaf X)).mapDerivedCategory ≅
      𝟭 (DerivedCategory (SheafOfModules.{u} (underlyingRingSheaf X))) :=
  mapDerivedCategoryCompIso (jStar (⊤ : Opens X.carrier) (underlyingRingSheaf X))
      (jShriek (⊤ : Opens X.carrier) (underlyingRingSheaf X)) ≪≫
    mapDerivedCategoryCongr
      (@asIso _ _ _ _ (jShriekAdjunction (⊤ : Opens X.carrier) (underlyingRingSheaf X)).counit
        isIso_topJShriekAdjunction_counit) ≪≫
    Stacks.Homology.mapDerivedCategoryIdIso

/-- **The derived category of the open subspace `⊤` is the derived category of `𝒪_X`-modules on
`X`.** Extension by zero along `⊤` is an exact equivalence with exact quasi-inverse, so it
induces an equivalence of unbounded derived categories. -/
def topExtensionDerivedEquivalence :
    OpenDerivedCategory X ⊤ ≌ DerivedCategory (SheafOfModules.{u} (underlyingRingSheaf X)) :=
  CategoryTheory.Equivalence.mk
    (jShriek (⊤ : Opens X.carrier) (underlyingRingSheaf X)).mapDerivedCategory
    (jStar (⊤ : Opens X.carrier) (underlyingRingSheaf X)).mapDerivedCategory
    (Stacks.Homology.mapDerivedCategoryIdIso.symm ≪≫
      mapDerivedCategoryCongr (jShriekUnitIso (⊤ : Opens X.carrier)) ≪≫
      (mapDerivedCategoryCompIso (jShriek (⊤ : Opens X.carrier) (underlyingRingSheaf X))
        (jStar (⊤ : Opens X.carrier) (underlyingRingSheaf X))).symm)
    topJShriekCounitDerivedIso

/-! ### The two-open glueing problem, and its reduction to a larger open -/

/-- **The two-open glueing problem of Situation 0D67, with the glued object sought over the open
`P`.** Given a system `S` of locally given derived objects on `X`, two opens `U` and `V` both
contained in `P`, an object `A` over `U`, an object `B` over `V` and an identification `c` of
their restrictions to `U ∩ V`, there is an object `F` over `P` whose restrictions to `U` and to
`V` are `A` and `B`, compatibly with `c`.

Nothing is assumed about the displayed collection `S.opens`: the problem is about arbitrary
objects over `U` and `V`, as in [Stacks, Tag 08DG]. -/
def TwoOpenGlueingOver (S : LocallyGiven X) (U V P : Opens X.carrier)
    (hUP : U ≤ P) (hVP : V ≤ P) : Prop :=
  ∀ (A : OpenDerivedCategory X U) (B : OpenDerivedCategory X V)
    (c : (S.restriction (U ⊓ V) U inf_le_left).obj A ≅
      (S.restriction (U ⊓ V) V inf_le_right).obj B),
  ∃ (F : OpenDerivedCategory X P)
    (f : (S.restriction U P hUP).obj F ≅ A)
    (g : (S.restriction V P hVP).obj F ≅ B),
    (S.restrictionComp (U ⊓ V) U P inf_le_left hUP).hom.app F ≫
        (S.restriction (U ⊓ V) U inf_le_left).map f.hom ≫ c.hom =
      (S.restrictionComp (U ⊓ V) V P inf_le_right hVP).hom.app F ≫
        (S.restriction (U ⊓ V) V inf_le_right).map g.hom

/-- **The chase behind `Stacks.DerivedGlueing.twoOpenGlueingOver_of_le`**, in a single arbitrary
category with every object and every morphism a variable.

Read `m` as the comparison of restriction to `U ∩ V` in one and in two steps, `hU` and `hV` as
the associativity of those comparisons on the `U` and the `V` side, and `hgl` as the
compatibility of the glueing over the larger open; the conclusion is the compatibility over the
smaller one.  The two morphisms `φ` and `ψ` are the restrictions of the transported
identifications, given by `hφ` and `hψ` as the restriction of a composite. -/
theorem glueTransport_eq {C : Type*} [Category C] {p₀ p₁ u₀ u₁ v₀ v₁ a b : C}
    (m : p₀ ≅ p₁) (kU : p₁ ⟶ u₁) (nU : p₀ ⟶ u₀) (rU : u₀ ≅ u₁) (α : u₀ ⟶ a) (γ : a ⟶ b)
    (kV : p₁ ⟶ v₁) (nV : p₀ ⟶ v₀) (rV : v₀ ≅ v₁) (β : v₀ ⟶ b) {φ : u₁ ⟶ a} {ψ : v₁ ⟶ b}
    (hU : m.hom ≫ kU = nU ≫ rU.hom) (hV : m.hom ≫ kV = nV ≫ rV.hom)
    (hgl : nU ≫ α ≫ γ = nV ≫ β) (hφ : φ = rU.inv ≫ α) (hψ : ψ = rV.inv ≫ β) :
    kU ≫ φ ≫ γ = kV ≫ ψ := by
  rw [hφ, hψ, m.eq_inv_comp.2 hU, m.eq_inv_comp.2 hV]
  simp [hgl]

/-- **A solution of the two-open glueing problem over a larger open gives one over a smaller
open containing both members.** Restrict the glued object from `Q` to `P`; the comparison of
restriction in one and in two steps turns its restrictions to `U` and to `V` back into the
prescribed objects, and the compatibility is carried along by the associativity of those
comparisons, `Stacks.DerivedGlueing.LocallyGiven.restrictionComp_pentagon`.

Nothing is assumed beyond `P ≤ Q`; in particular neither `P` nor `Q` need belong to `S.opens`. -/
theorem twoOpenGlueingOver_of_le (S : LocallyGiven X) (U V P Q : Opens X.carrier)
    (hUP : U ≤ P) (hVP : V ≤ P) (hPQ : P ≤ Q)
    (h : TwoOpenGlueingOver S U V Q (hUP.trans hPQ) (hVP.trans hPQ)) :
    TwoOpenGlueingOver S U V P hUP hVP := by
  intro A B c
  obtain ⟨G, a, b, hab⟩ := h A B c
  refine ⟨(S.restriction P Q hPQ).obj G,
    ((S.restrictionComp U P Q hUP hPQ).app G).symm ≪≫ a,
    ((S.restrictionComp V P Q hVP hPQ).app G).symm ≪≫ b, ?_⟩
  exact glueTransport_eq
    ((S.restrictionComp (U ⊓ V) P Q (inf_le_left.trans hUP) hPQ).app G)
    ((S.restrictionComp (U ⊓ V) U P inf_le_left hUP).hom.app _)
    ((S.restrictionComp (U ⊓ V) U Q inf_le_left (hUP.trans hPQ)).hom.app G)
    ((S.restriction (U ⊓ V) U inf_le_left).mapIso
      ((S.restrictionComp U P Q hUP hPQ).app G))
    ((S.restriction (U ⊓ V) U inf_le_left).map a.hom) c.hom
    ((S.restrictionComp (U ⊓ V) V P inf_le_right hVP).hom.app _)
    ((S.restrictionComp (U ⊓ V) V Q inf_le_right (hVP.trans hPQ)).hom.app G)
    ((S.restriction (U ⊓ V) V inf_le_right).mapIso
      ((S.restrictionComp V P Q hVP hPQ).app G))
    ((S.restriction (U ⊓ V) V inf_le_right).map b.hom)
    (S.restrictionComp_pentagon (U ⊓ V) U P Q inf_le_left hUP hPQ G)
    (S.restrictionComp_pentagon (U ⊓ V) V P Q inf_le_right hVP hPQ G)
    hab
    ((S.restriction (U ⊓ V) U inf_le_left).map_comp _ _)
    ((S.restriction (U ⊓ V) V inf_le_right).map_comp _ _)

/-- **The two-open glueing statement of Situation 0D67, deduced from its case at the open `⊤`.**
If the two-open glueing problem is solvable with the glued object sought over `⊤`
(`Stacks.DerivedGlueing.TwoOpenGlueingOver S U V ⊤`), then it is solvable with the glued object
sought over `U ∪ V`. -/
theorem exists_glueing_two_opens_of_top (S : LocallyGiven X) (U V : Opens X.carrier)
    (hTop : TwoOpenGlueingOver S U V ⊤ le_top le_top)
    (A : OpenDerivedCategory X U) (B : OpenDerivedCategory X V)
    (c : (S.restriction (U ⊓ V) U inf_le_left).obj A ≅
      (S.restriction (U ⊓ V) V inf_le_right).obj B) :
    ∃ (F : OpenDerivedCategory X (U ⊔ V))
      (f : (S.restriction U (U ⊔ V) le_sup_left).obj F ≅ A)
      (g : (S.restriction V (U ⊔ V) le_sup_right).obj F ≅ B),
      (S.restrictionComp (U ⊓ V) U (U ⊔ V) inf_le_left le_sup_left).hom.app F ≫
          (S.restriction (U ⊓ V) U inf_le_left).map f.hom ≫ c.hom =
        (S.restrictionComp (U ⊓ V) V (U ⊔ V) inf_le_right le_sup_right).hom.app F ≫
          (S.restriction (U ⊓ V) V inf_le_right).map g.hom :=
  twoOpenGlueingOver_of_le S U V (U ⊔ V) ⊤ le_sup_left le_sup_right le_top hTop A B c

/-! ### Open subspaces of a space, and the Cartesian square at two opens -/

/-- The image of the canonical inclusion of the open subspace `W` is `W`. -/
theorem range_ofRestrict (W : Opens X.carrier) :
    Set.range (X.ofRestrict W.isOpenEmbedding).hom.base = (W : Set X.carrier) :=
  Subtype.range_val

/-- The image of a composite of continuous maps is contained in the image of the second. -/
theorem range_comp_subset_range {A B C : TopCat.{u}} (p : A ⟶ B) (q : B ⟶ C) :
    Set.range (p ≫ q) ⊆ Set.range q := by
  rintro y ⟨x, rfl⟩
  exact ⟨p x, by simp⟩

/-- The canonical inclusion of an open subspace is an open immersion of presheafed spaces.
This is `AlgebraicGeometry.SheafedSpace.IsOpenImmersion.ofRestrict`, stated for the underlying
morphism of presheafed spaces. -/
instance isOpenImmersion_hom_ofRestrict (W : Opens X.carrier) :
    PresheafedSpace.IsOpenImmersion (X.ofRestrict W.isOpenEmbedding).hom :=
  SheafedSpace.IsOpenImmersion.ofRestrict X W.isOpenEmbedding

/-- For `U ≤ V` the open subspace `U` lands inside the open subspace `V`. -/
theorem range_ofRestrict_subset {U V : Opens X.carrier} (hUV : U ≤ V) :
    Set.range (X.ofRestrict U.isOpenEmbedding).hom.base ⊆
      Set.range (X.ofRestrict V.isOpenEmbedding).hom.base :=
  fun _ hy => (range_ofRestrict V).ge (hUV ((range_ofRestrict U).le hy))

/-- **The inclusion of one open subspace of a ringed space into a larger one.** For `U ≤ V` the
canonical inclusion of the open subspace `U` factors, uniquely, through the open immersion of the
open subspace `V`; the factorization is this morphism of ringed spaces.

Mathlib builds the factorization at the level of presheafed spaces
(`AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.lift`); morphisms of sheafed spaces are
morphisms of the underlying presheafed spaces, so it is transported by
`CategoryTheory.InducedCategory.homMk`. -/
def restrictIncl {U V : Opens X.carrier} (hUV : U ≤ V) :
    X.restrict U.isOpenEmbedding ⟶ X.restrict V.isOpenEmbedding :=
  InducedCategory.homMk (PresheafedSpace.IsOpenImmersion.lift
    (X.ofRestrict V.isOpenEmbedding).hom (X.ofRestrict U.isOpenEmbedding).hom
    (range_ofRestrict_subset hUV))

/-- **The inclusion of open subspaces is compatible with the inclusions into the ambient
space.** This is the defining property of `Stacks.DerivedGlueing.restrictIncl`. -/
@[simp]
theorem restrictIncl_comp {U V : Opens X.carrier} (hUV : U ≤ V) :
    restrictIncl (X := X) hUV ≫ X.ofRestrict V.isOpenEmbedding =
      X.ofRestrict U.isOpenEmbedding :=
  InducedCategory.hom_ext (PresheafedSpace.IsOpenImmersion.lift_fac
    (X.ofRestrict V.isOpenEmbedding).hom (X.ofRestrict U.isOpenEmbedding).hom
    (range_ofRestrict_subset hUV))

/-- A cone over the two open immersions of `U` and of `V` has its image inside `U ∩ V`: inside
`U` because it factors through the inclusion of `U`, and inside `V` because, by the cone
condition, it also factors through the inclusion of `V`. -/
theorem range_cone_subset (U V : Opens X.carrier)
    (s : Limits.PullbackCone (X.ofRestrict U.isOpenEmbedding)
      (X.ofRestrict V.isOpenEmbedding)) :
    Set.range (s.fst ≫ X.ofRestrict U.isOpenEmbedding).hom.base ⊆
      Set.range (X.ofRestrict (U ⊓ V).isOpenEmbedding).hom.base := by
  intro y hy
  refine (range_ofRestrict (U ⊓ V)).ge ?_
  have hyU : y ∈ (U : Set X.carrier) :=
    (range_ofRestrict U).le (range_comp_subset_range s.fst.hom.base
      (X.ofRestrict U.isOpenEmbedding).hom.base hy)
  have hyV : y ∈ (V : Set X.carrier) := by
    rw [s.condition] at hy
    exact (range_ofRestrict V).le (range_comp_subset_range s.snd.hom.base
      (X.ofRestrict V.isOpenEmbedding).hom.base hy)
  exact ⟨hyU, hyV⟩

/-- The factorization of a cone over the two open immersions through the open subspace `U ∩ V`,
given by `Stacks.DerivedGlueing.range_cone_subset`. -/
def infLift (U V : Opens X.carrier)
    (s : Limits.PullbackCone (X.ofRestrict U.isOpenEmbedding)
      (X.ofRestrict V.isOpenEmbedding)) :
    s.pt ⟶ X.restrict (U ⊓ V).isOpenEmbedding :=
  InducedCategory.homMk (PresheafedSpace.IsOpenImmersion.lift
    (X.ofRestrict (U ⊓ V).isOpenEmbedding).hom
    (s.fst ≫ X.ofRestrict U.isOpenEmbedding).hom (range_cone_subset U V s))

/-- The factorization `Stacks.DerivedGlueing.infLift` is compatible with the inclusions into the
ambient space. -/
theorem infLift_fac (U V : Opens X.carrier)
    (s : Limits.PullbackCone (X.ofRestrict U.isOpenEmbedding)
      (X.ofRestrict V.isOpenEmbedding)) :
    infLift U V s ≫ X.ofRestrict (U ⊓ V).isOpenEmbedding =
      s.fst ≫ X.ofRestrict U.isOpenEmbedding :=
  InducedCategory.hom_ext (PresheafedSpace.IsOpenImmersion.lift_fac
    (X.ofRestrict (U ⊓ V).isOpenEmbedding).hom
    (s.fst ≫ X.ofRestrict U.isOpenEmbedding).hom (range_cone_subset U V s))

/-- **The square of open subspaces attached to two opens of a ringed space is Cartesian.** The
open subspace `U ∩ V`, with its two inclusions into the open subspaces `U` and `V`, is the
pullback of the two open immersions `j_U` and `j_V` in the category of ringed spaces.

This is the hypothesis `h : IsPullback iU iV jU jV` of
`Stacks.Cohomology.GlueingComplexes.exists_glueing` at two opens of a space.

A cone over `j_U` and `j_V` has its image inside `U ∩ V`
(`Stacks.DerivedGlueing.range_cone_subset`), so it factors through the inclusion of that open
subspace; the factorization is unique because an open immersion is a monomorphism. -/
theorem isPullback_restrictIncl (U V : Opens X.carrier) :
    IsPullback (restrictIncl (X := X) (inf_le_left : U ⊓ V ≤ U))
      (restrictIncl (X := X) (inf_le_right : U ⊓ V ≤ V))
      (X.ofRestrict U.isOpenEmbedding) (X.ofRestrict V.isOpenEmbedding) := by
  have hw : restrictIncl (X := X) (inf_le_left : U ⊓ V ≤ U) ≫
        X.ofRestrict U.isOpenEmbedding =
      restrictIncl (X := X) (inf_le_right : U ⊓ V ≤ V) ≫ X.ofRestrict V.isOpenEmbedding := by
    rw [restrictIncl_comp, restrictIncl_comp]
  refine IsPullback.of_isLimit' ⟨hw⟩
    (Limits.PullbackCone.IsLimit.mk hw (infLift U V) (fun s => ?_) (fun s => ?_)
      (fun s m h₁ _ => ?_))
  · rw [← cancel_mono (X.ofRestrict U.isOpenEmbedding), Category.assoc, restrictIncl_comp,
      infLift_fac]
  · rw [← cancel_mono (X.ofRestrict V.isOpenEmbedding), Category.assoc, restrictIncl_comp,
      infLift_fac, s.condition]
  · rw [← cancel_mono (X.ofRestrict (U ⊓ V).isOpenEmbedding), infLift_fac,
      ← restrictIncl_comp (X := X) (inf_le_left : U ⊓ V ≤ U), ← Category.assoc, h₁]

/-! ### The glueing datum of Situation 0D67, transported -/

open Stacks.Cohomology.GlueingComplexes in
/-- **Derived restriction to the open subspace `W ≤ U` is derived restriction to `U` followed by
derived restriction along the inclusion of open subspaces.** This is the composition isomorphism
of [Stacks, Tag 0D5S] at the factorization
`Stacks.DerivedGlueing.restrictIncl_comp` of the inclusion of `W`. -/
def restrictInclDerivedIso {W U : Opens X.carrier} (hWU : W ≤ U) :
    derivedRestrict (X.ofRestrict W.isOpenEmbedding) ≅
      derivedRestrict (X.ofRestrict U.isOpenEmbedding) ⋙
        derivedRestrict (restrictIncl (X := X) hWU) :=
  (restrictEqIso (restrictIncl_comp (X := X) hWU)).symm ≪≫
    (Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical
      (restrictIncl (X := X) hWU) (X.ofRestrict U.isOpenEmbedding)).symm

open Stacks.Cohomology.GlueingComplexes in
/-- **The overlap identification of Situation 0D67, read in the vocabulary of [Stacks, Tag
08DG].** An identification `c` of the restrictions of `A` and `B` to `U ∩ V`, in the restriction
functors displayed by a system of locally given derived objects, is an identification of their
derived restrictions along the two inclusions of the open subspace `U ∩ V` into the open subspaces
`U` and `V` — which is the glueing datum
`Stacks.Cohomology.GlueingComplexes.exists_glueing` takes. -/
def overlapIsoOfRestriction (S : LocallyGiven X) (U V : Opens X.carrier)
    (A : OpenDerivedCategory X U) (B : OpenDerivedCategory X V)
    (c : (S.restriction (U ⊓ V) U inf_le_left).obj A ≅
      (S.restriction (U ⊓ V) V inf_le_right).obj B) :
    (derivedRestrict (restrictIncl (X := X) (inf_le_left : U ⊓ V ≤ U))).obj A ≅
      (derivedRestrict (restrictIncl (X := X) (inf_le_right : U ⊓ V ≤ V))).obj B :=
  ((derivedRestrict (restrictIncl (X := X) (inf_le_left : U ⊓ V ≤ U))).mapIso
      ((derivedRestrictJShriekIso U).app A)).symm ≪≫
    ((restrictInclDerivedIso (inf_le_left : U ⊓ V ≤ U)).app
      ((jShriek U (underlyingRingSheaf X)).mapDerivedCategory.obj A)).symm ≪≫
    ((S.restrictionIsoDerivedRestrict U (U ⊓ V) inf_le_left).app A).symm ≪≫
    c ≪≫
    (S.restrictionIsoDerivedRestrict V (U ⊓ V) inf_le_right).app B ≪≫
    (restrictInclDerivedIso (inf_le_right : U ⊓ V ≤ V)).app
      ((jShriek V (underlyingRingSheaf X)).mapDerivedCategory.obj B) ≪≫
    (derivedRestrict (restrictIncl (X := X) (inf_le_right : U ⊓ V ≤ V))).mapIso
      ((derivedRestrictJShriekIso V).app B)

/-! ### The glued object exists -/

/-- **The two-open glueing problem of Situation 0D67 with its compatibility clause dropped**: the
glued object over `P` is only required to have *some* identification of each of its two
restrictions with the prescribed objects, not identifications that agree over `U ∩ V` through
`c`. -/
def TwoOpenGlueingObjectsOver (S : LocallyGiven X) (U V P : Opens X.carrier)
    (hUP : U ≤ P) (hVP : V ≤ P) : Prop :=
  ∀ (A : OpenDerivedCategory X U) (B : OpenDerivedCategory X V),
    ((S.restriction (U ⊓ V) U inf_le_left).obj A ≅
      (S.restriction (U ⊓ V) V inf_le_right).obj B) →
  ∃ F : OpenDerivedCategory X P,
    Nonempty ((S.restriction U P hUP).obj F ≅ A) ∧
      Nonempty ((S.restriction V P hVP).obj F ≅ B)

open Stacks.Cohomology.GlueingComplexes in
/-- **The glued object of the two-open problem of Situation 0D67 exists over `⊤`.** This is the
glueing lemma [Stacks, Tag 08DG] transported: the Cartesian square it needs is
`Stacks.DerivedGlueing.isPullback_restrictIncl`, the glueing datum it needs is
`Stacks.DerivedGlueing.overlapIsoOfRestriction`, and its conclusion — an object of `D(𝒪_X)`
restricting to `A` and to `B` — is read back into
`Stacks.DerivedGlueing.OpenDerivedCategory X ⊤` by restriction to `⊤`, which is quasi-inverse to
extension by zero along `⊤` (`Stacks.DerivedGlueing.topJShriekCounitDerivedIso`), and into the
displayed restriction functors by the dictionary
`Stacks.DerivedGlueing.LocallyGiven.restrictionIsoDerivedRestrict`. -/
theorem twoOpenGlueingObjectsOver_top (S : LocallyGiven X) (U V : Opens X.carrier) :
    TwoOpenGlueingObjectsOver S U V ⊤ le_top le_top := by
  intro A B c
  obtain ⟨D⟩ := exists_glueing (X.ofRestrict U.isOpenEmbedding)
    (X.ofRestrict V.isOpenEmbedding) (restrictIncl (X := X) (inf_le_left : U ⊓ V ≤ U))
    (restrictIncl (X := X) (inf_le_right : U ⊓ V ≤ V)) (isPullback_restrictIncl U V) A B
    (overlapIsoOfRestriction S U V A B c)
  refine ⟨(jStar (⊤ : Opens X.carrier) (underlyingRingSheaf X)).mapDerivedCategory.obj D.F,
    ⟨?_⟩, ⟨?_⟩⟩
  · exact (S.restrictionIsoDerivedRestrict ⊤ U le_top).app _ ≪≫
      (derivedRestrict (X.ofRestrict U.isOpenEmbedding)).mapIso
        (topJShriekCounitDerivedIso.app D.F) ≪≫ D.f
  · exact (S.restrictionIsoDerivedRestrict ⊤ V le_top).app _ ≪≫
      (derivedRestrict (X.ofRestrict V.isOpenEmbedding)).mapIso
        (topJShriekCounitDerivedIso.app D.F) ≪≫ D.g

/-- **A glued object over a larger open restricts to one over a smaller open containing both
members**, in the version with the compatibility clause dropped.  This is
`Stacks.DerivedGlueing.twoOpenGlueingOver_of_le` without the diagram chase: the comparison of
restriction in one and in two steps is all that is needed to turn the restrictions of the
restricted object back into the prescribed ones. -/
theorem twoOpenGlueingObjectsOver_of_le (S : LocallyGiven X) (U V P Q : Opens X.carrier)
    (hUP : U ≤ P) (hVP : V ≤ P) (hPQ : P ≤ Q)
    (h : TwoOpenGlueingObjectsOver S U V Q (hUP.trans hPQ) (hVP.trans hPQ)) :
    TwoOpenGlueingObjectsOver S U V P hUP hVP := by
  intro A B c
  obtain ⟨G, ⟨a⟩, ⟨b⟩⟩ := h A B c
  exact ⟨(S.restriction P Q hPQ).obj G,
    ⟨((S.restrictionComp U P Q hUP hPQ).app G).symm ≪≫ a⟩,
    ⟨((S.restrictionComp V P Q hVP hPQ).app G).symm ≪≫ b⟩⟩

/-- **The object part of the two-open glueing statement of Situation 0D67, with nothing
assumed.** For a system of locally given derived objects on a ringed space, two opens `U` and
`V`, objects `A` over `U` and `B` over `V` and an identification of their restrictions to
`U ∩ V`, there is an object `F` over `U ∪ V` whose restriction to `U` is `A` and whose
restriction to `V` is `B`. -/
theorem exists_glueing_two_opens_objects (S : LocallyGiven X) (U V : Opens X.carrier)
    (A : OpenDerivedCategory X U) (B : OpenDerivedCategory X V)
    (c : (S.restriction (U ⊓ V) U inf_le_left).obj A ≅
      (S.restriction (U ⊓ V) V inf_le_right).obj B) :
    ∃ F : OpenDerivedCategory X (U ⊔ V),
      Nonempty ((S.restriction U (U ⊔ V) le_sup_left).obj F ≅ A) ∧
        Nonempty ((S.restriction V (U ⊔ V) le_sup_right).obj F ≅ B) :=
  twoOpenGlueingObjectsOver_of_le S U V (U ⊔ V) ⊤ le_sup_left le_sup_right le_top
    (twoOpenGlueingObjectsOver_top S U V) A B c

end Stacks.DerivedGlueing

end
