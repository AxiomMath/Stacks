module

public import StacksFrontier.AlgebraicGeometry.OpensCoverHom
public import StacksFrontier.Deformation.Examples.Geometric.SchemesTwoOpenCover
public import StacksFrontier.Deformation.Examples.Geometric.SchemesTwoOpenCoverGlue

/-!
# The deformation category of a scheme covered by two opens

Let `X` be a scheme over the residue field `k` covered by two opens `U₁` and `U₂`. The
comparison functor `Deformation.Examples.twoOpenComparisonFunctor` from the deformation
category of `X` to the 2-fibre product `Def_{U₁} ×_{Def_{U₁ ⊓ U₂}} Def_{U₂}` over `𝒞_Λ` is an
equivalence of categories.

It is faithful and full because a morphism of deformations of `X` is determined by, and glues
from, its two restrictions: the two opens that `U₁` and `U₂` cut out in the total space cover
it, because the special-fibre immersion is a homeomorphism, and they meet in the open that
`U₁ ⊓ U₂` cuts out, because that immersion is injective. The agreement of the two restrictions
on the overlap, which is what the glueing needs, is exactly the square that the comparison
isomorphism of a morphism of the 2-fibre product is asked to make commute. Cartesianness of the
glued morphism is checked chart by chart, being local on the target.

It is essentially surjective because the deformation glued from a datum restricts to the two
charts of that datum, compatibly with the datum's comparison isomorphism: the glueing
construction `Deformation.Examples.glueDeformation` and its two chart isomorphisms assemble
into a single isomorphism of the 2-fibre product, the compatibility being the statement that
the overlap chart of the glued scheme is reached the same way through either chart.

## Main definitions

* `Deformation.Examples.restrictedOpenHom`: the morphism of total spaces underlying a morphism
  of two restricted deformations, read between the opens they cut out.
* `Deformation.Examples.glueTwoOpenMap`: the morphism of total spaces glued from two morphisms
  of the restrictions which agree on the overlap.
* `Deformation.Examples.glueTwoOpenHom`: that morphism as a morphism of deformations of `X`.
* `Deformation.Examples.glueDeformationComparisonIso`: the isomorphism of the 2-fibre product
  between the pair of restrictions of a glued deformation and the datum it was glued from.
* `Deformation.Examples.twoOpenDeformationsEquivalence` and
  `Deformation.Examples.GluingSituation.deformationEquivalence`: the equivalence
  `Def_X ≌ Def_{U₁} ×_{Def_{U₁ ⊓ U₂}} Def_{U₂}`.

## Main results

* `Deformation.Examples.restrictedOpen_sup`, `Deformation.Examples.restrictedOpen_top` and
  `Deformation.Examples.restrictedOpen_mono`: the open which an open of the special fibre cuts
  out in the total space of a deformation respects unions, the whole space and inclusions
  (intersections: `Deformation.Examples.restrictedOpen_inf`).
* `Deformation.Examples.existsUnique_glueTwoOpenMap`: **a morphism of deformations glues from
  its two restrictions.**
* `Deformation.Examples.overlap_compat_of_comparison_square`: **the comparison square of the
  2-fibre product says that the two components agree on the overlap.**
* `Deformation.Examples.faithful_twoOpenComparisonFunctor`,
  `Deformation.Examples.full_twoOpenComparisonFunctor` and
  `Deformation.Examples.essSurj_twoOpenComparisonFunctor`: the three halves of the equivalence.
* `Deformation.Examples.isEquivalence_twoOpenComparisonFunctor` and
  `Deformation.Examples.GluingSituation.isEquivalence_comparisonFunctor`: **the comparison
  functor is an equivalence**, in general and in Situation 0DYY.

## Implementation notes

The total space of `Deformation.Examples.restrictDeformation U P` is the open
`Deformation.Examples.restrictedOpen P U` of the total space of `P` only up to unfolding a
semireducible definition, and the same holds one level down for
`Deformation.Examples.openRestrictionLEFunctor`. A composition one factor of which is written
through a restricted deformation and another through the open it cuts out is therefore
type-correct only at default transparency, which rewriting tactics do not use; worse, the
unification through the restriction functor is expensive enough to exhaust the heartbeat
budget. Every statement here is therefore written in one spelling throughout, with
`Deformation.Examples.restrictedOpenHom` and the `rfl`-equalities at the head of the proofs of
`Deformation.Examples.openRestrictionLE_map_comp_nestedι` and
`Deformation.Examples.overlap_restrictGlueDeformationLeft` as the places where the spellings
meet, and the ambient object of `Over (Spec (.of k))` is passed explicitly to
`Deformation.Examples.restrictDeformationHom_map_comp_restrictDeformationι`, because inferring
it from the open `U.ι ⁻¹ᵁ V` is the higher-order problem `?X.left ≟ U.toScheme`.

The equivalence is established as fullness, faithfulness and essential surjectivity rather than
by exhibiting the glueing as a functor and two natural isomorphisms. Essential surjectivity
needs no naturality, and fullness is where the glueing of morphisms happens, so the three
statements together use the glueing construction only on objects and on single morphisms.

Passing from the deformation categories of the two opens to those of their coordinate rings is
`Deformation.Examples.SchemeRingDeformation.equivalenceOver`, which takes the hypothesis
`Deformation.Examples.SchemeRingDeformation.ThickeningIsAffine`; the equivalence proved here is
the one the source's proof establishes first, and it uses no affineness.

## References

* [Stacks Project, Tag 01JA](https://stacks.math.columbia.edu/tag/01JA)
* [Stacks Project, Tag 0DYW](https://stacks.math.columbia.edu/tag/0DYW)
* [Stacks Project, Tag 0DYY](https://stacks.math.columbia.edu/tag/0DYY)
* [Stacks Project, Tag 0DYZ](https://stacks.math.columbia.edu/tag/0DYZ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Deformation.Examples

variable {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k] {X : Over (Spec (.of k))}

/-! ### The opens of a deformation cut out by a family of opens of the special fibre -/

/-- The open cut out by a union is the union of the opens cut out. -/
theorem restrictedOpen_sup (P : SchemeDeformationCategory (Λ := Λ) (k := k) X)
    (U₁ U₂ : X.left.Opens) :
    restrictedOpen P (U₁ ⊔ U₂) = restrictedOpen P U₁ ⊔ restrictedOpen P U₂ :=
  TopologicalSpace.Opens.ext (Set.image_union _ _ _)

/-- The open cut out by the whole special fibre is the whole total space: the special-fibre
immersion is surjective. -/
theorem restrictedOpen_top (P : SchemeDeformationCategory (Λ := Λ) (k := k) X) :
    restrictedOpen P (⊤ : X.left.Opens) = ⊤ :=
  TopologicalSpace.Opens.ext <| by
    show (⇑P.specialMap) '' ((⊤ : X.left.Opens) : Set X.left) = ((⊤ : P.scheme.Opens) : Set _)
    rw [TopologicalSpace.Opens.coe_top, TopologicalSpace.Opens.coe_top, Set.image_univ,
      (deformationSpecialMap_surjective P).range_eq]

/-- The open cut out by a smaller open is contained in the open cut out by a larger one. -/
theorem restrictedOpen_mono (P : SchemeDeformationCategory (Λ := Λ) (k := k) X)
    {U V : X.left.Opens} (h : V ≤ U) : restrictedOpen P V ≤ restrictedOpen P U :=
  Set.image_mono h

/-- Inside the total space of a deformation, the inclusion of the open cut out by `V` into the
open cut out by a larger `U`, read through the restricted deformations, is the inclusion of the
two opens. -/
theorem nestedOpenIso_inv_comp_nestedι (P : SchemeDeformationCategory (Λ := Λ) (k := k) X)
    {U V : X.left.Opens} (h : V ≤ U) :
    (nestedOpenIso P h).inv ≫ nestedι P h = P.scheme.homOfLE (restrictedOpen_mono P h) :=
  (cancel_mono (restrictedOpen P U).ι).mp <|
    (Category.assoc _ _ _).trans <|
      (nestedOpenIso_inv_comp P h).trans
        (Scheme.homOfLE_ι P.scheme (restrictedOpen_mono P h)).symm

/-- Every point of the total space of a deformation lies in one of the two opens cut out by two
opens covering the special fibre. -/
theorem exists_mem_restrictedOpen (P : SchemeDeformationCategory (Λ := Λ) (k := k) X)
    {U₁ U₂ : X.left.Opens} (hcover : U₁ ⊔ U₂ = ⊤) (y : P.scheme) :
    ∃ b : Bool, y ∈ restrictedOpen P (bif b then U₂ else U₁) := by
  have hy : y ∈ restrictedOpen P U₁ ⊔ restrictedOpen P U₂ := by
    rw [restrictedOpen_sup_eq_top P hcover]
    trivial
  rcases hy with h | h
  · exact ⟨false, h⟩
  · exact ⟨true, h⟩

/-- Two morphisms out of the total space of a deformation agree if they agree on each of the two
opens cut out by two opens covering the special fibre. -/
private theorem hom_ext_of_restrictedOpen_cover (Q : SchemeDeformationCategory (Λ := Λ) (k := k) X)
    {U₁ U₂ : X.left.Opens} (hcover : U₁ ⊔ U₂ = ⊤) {T : Scheme} {f g : Q.scheme ⟶ T}
    (h₁ : (restrictedOpen Q U₁).ι ≫ f = (restrictedOpen Q U₁).ι ≫ g)
    (h₂ : (restrictedOpen Q U₂).ι ≫ f = (restrictedOpen Q U₂).ι ≫ g) : f = g := by
  refine Scheme.hom_ext_of_forall _ _ fun y => ?_
  obtain ⟨c, hc⟩ := exists_mem_restrictedOpen Q hcover y
  cases c
  exacts [⟨_, hc, h₁⟩, ⟨_, hc, h₂⟩]

/-! ### Glueing a morphism of deformations from its two restrictions -/

section Glue

variable {P Q : SchemeDeformationCategory (Λ := Λ) (k := k) X}

/-- The morphism of total spaces underlying a morphism of the restrictions of two deformations
of `X` to an open `U`, read as a morphism of the opens those restrictions cut out in the two
total spaces.

This is the same morphism as `CategoryTheory.SchemeDeformationCategory.Hom.map`, with its type
written through the opens of the two total spaces rather than through the restricted
deformations. The two forms agree only up to unfolding the semireducible
`Deformation.Examples.restrictDeformation`, so a composition whose middle object is written in
the other form is not type-correct below default transparency; glueing along an open covering
consumes the form written here. -/
def restrictedOpenHom {U : X.left.Opens}
    (f : restrictDeformation U P ⟶ restrictDeformation U Q) :
    (restrictedOpen Q U).toScheme ⟶ (restrictedOpen P U).toScheme := f.map

variable {U₁ U₂ : X.left.Opens}
  (a : restrictDeformation U₁ P ⟶ restrictDeformation U₁ Q)
  (b : restrictDeformation U₂ P ⟶ restrictDeformation U₂ Q)
  (hab : Q.scheme.homOfLE (restrictedOpen_mono Q (inf_le_left : U₁ ⊓ U₂ ≤ U₁)) ≫
      restrictedOpenHom a ≫ (restrictedOpen P U₁).ι =
    Q.scheme.homOfLE (restrictedOpen_mono Q (inf_le_right : U₁ ⊓ U₂ ≤ U₂)) ≫
      restrictedOpenHom b ≫ (restrictedOpen P U₂).ι)
  (hcover : U₁ ⊔ U₂ = ⊤)

include hab hcover in
/-- **A morphism of deformations glues from its two restrictions.** Two morphisms of the
restrictions of two deformations of `X` to two opens covering `X` which agree on the
intersection of the opens they cut out come from a unique morphism of the total spaces, because
those two opens cover the total space. -/
theorem existsUnique_glueTwoOpenMap :
    ∃! f : Q.scheme ⟶ P.scheme,
      (restrictedOpen Q U₁).ι ≫ f = restrictedOpenHom a ≫ (restrictedOpen P U₁).ι ∧
        (restrictedOpen Q U₂).ι ≫ f = restrictedOpenHom b ≫ (restrictedOpen P U₂).ι := by
  have hab' : Q.scheme.homOfLE
        (inf_le_left : restrictedOpen Q U₁ ⊓ restrictedOpen Q U₂ ≤ restrictedOpen Q U₁) ≫
      restrictedOpenHom a ≫ (restrictedOpen P U₁).ι =
    Q.scheme.homOfLE
        (inf_le_right : restrictedOpen Q U₁ ⊓ restrictedOpen Q U₂ ≤ restrictedOpen Q U₂) ≫
      restrictedOpenHom b ≫ (restrictedOpen P U₂).ι := by
    have h := congrArg
      (fun m : (restrictedOpen Q (U₁ ⊓ U₂)).toScheme ⟶ P.scheme =>
        (Q.scheme.isoOfEq (restrictedOpen_inf Q U₁ U₂)).inv ≫ m) hab
    simpa only [Scheme.isoOfEq_inv, ← Category.assoc, Scheme.homOfLE_homOfLE] using h
  have hba : Q.scheme.homOfLE
        (inf_le_left : restrictedOpen Q U₂ ⊓ restrictedOpen Q U₁ ≤ restrictedOpen Q U₂) ≫
      restrictedOpenHom b ≫ (restrictedOpen P U₂).ι =
    Q.scheme.homOfLE
        (inf_le_right : restrictedOpen Q U₂ ⊓ restrictedOpen Q U₁ ≤ restrictedOpen Q U₁) ≫
      restrictedOpenHom a ≫ (restrictedOpen P U₁).ι := by
    have h := congrArg
      (fun m : (restrictedOpen Q U₁ ⊓ restrictedOpen Q U₂).toScheme ⟶ P.scheme =>
        (Q.scheme.isoOfEq (inf_comm (restrictedOpen Q U₂) (restrictedOpen Q U₁))).hom ≫ m)
      hab'.symm
    simpa only [Scheme.isoOfEq_hom, ← Category.assoc, Scheme.homOfLE_homOfLE] using h
  obtain ⟨f, hf, huniq⟩ := Scheme.existsUnique_hom_of_opens_cover
    (fun c : Bool => restrictedOpen Q (bif c then U₂ else U₁))
    (exists_mem_restrictedOpen Q hcover)
    (fun c => match c with
      | false => restrictedOpenHom a ≫ (restrictedOpen P U₁).ι
      | true => restrictedOpenHom b ≫ (restrictedOpen P U₂).ι)
    (by
      intro i j
      cases i <;> cases j
      · rfl
      · exact hab'
      · exact hba
      · rfl)
  refine ⟨f, ⟨hf false, hf true⟩, fun g hg => huniq g ?_⟩
  rintro (_ | _)
  exacts [hg.1, hg.2]

/-- The morphism of total spaces glued from the two restrictions: on the open cut out by `U₁`
it is the first restriction, on the open cut out by `U₂` the second, and the two agree on the
intersection by hypothesis. -/
def glueTwoOpenMap : Q.scheme ⟶ P.scheme :=
  (existsUnique_glueTwoOpenMap a b hab hcover).choose

/-- On the open cut out by `U₁`, the glued morphism is the first restriction. -/
@[reassoc]
theorem ι_glueTwoOpenMap_left :
    (restrictedOpen Q U₁).ι ≫ glueTwoOpenMap a b hab hcover =
      restrictedOpenHom a ≫ (restrictedOpen P U₁).ι :=
  (existsUnique_glueTwoOpenMap a b hab hcover).choose_spec.1.1

/-- On the open cut out by `U₂`, the glued morphism is the second restriction. -/
@[reassoc]
theorem ι_glueTwoOpenMap_right :
    (restrictedOpen Q U₂).ι ≫ glueTwoOpenMap a b hab hcover =
      restrictedOpenHom b ≫ (restrictedOpen P U₂).ι :=
  (existsUnique_glueTwoOpenMap a b hab hcover).choose_spec.1.2

include hab hcover in
/-- The glued morphism of total spaces is compatible with the two identifications of the
special fibre, because the two opens cover the special fibre. -/
theorem specialMap_comp_glueTwoOpenMap :
    Q.specialMap ≫ glueTwoOpenMap a b hab hcover = P.specialMap := by
  have key : ∀ (U : X.left.Opens) (c : restrictDeformation U P ⟶ restrictDeformation U Q),
      (restrictedOpen Q U).ι ≫ glueTwoOpenMap a b hab hcover =
        restrictedOpenHom c ≫ (restrictedOpen P U).ι →
      (U.ι ≫ Q.specialMap) ≫ glueTwoOpenMap a b hab hcover = U.ι ≫ P.specialMap := by
    intro U c hc
    have hs : Q.specialMap.resLE (restrictedOpen Q U) U
          (le_specialMap_preimage_restrictedOpen Q U) ≫ restrictedOpenHom c =
        P.specialMap.resLE (restrictedOpen P U) U
          (le_specialMap_preimage_restrictedOpen P U) := c.special_compat
    rw [← Scheme.Hom.resLE_comp_ι Q.specialMap (le_specialMap_preimage_restrictedOpen Q U),
      Category.assoc, hc, ← Category.assoc, hs,
      Scheme.Hom.resLE_comp_ι P.specialMap (le_specialMap_preimage_restrictedOpen P U)]
  refine (coverOfTwoOpens X U₁ U₂ hcover).hom_ext _ _ ?_
  intro c
  cases c
  · exact key U₁ a (ι_glueTwoOpenMap_left a b hab hcover)
  · exact key U₂ b (ι_glueTwoOpenMap_right a b hab hcover)

include hab hcover in
/-- The glued morphism of total spaces carries the open cut out by an open of the special fibre
onto the open cut out by the same open: the two identifications of the underlying space with
that of the special fibre agree. -/
theorem glueTwoOpenMap_preimage_restrictedOpen (U : X.left.Opens) :
    glueTwoOpenMap a b hab hcover ⁻¹ᵁ restrictedOpen P U = restrictedOpen Q U := by
  have hpt : ∀ x : X.left,
      glueTwoOpenMap a b hab hcover (Q.specialMap x) = P.specialMap x := fun x => by
    simpa using congrArg (fun g : X.left ⟶ P.scheme => g x)
      (specialMap_comp_glueTwoOpenMap a b hab hcover)
  ext y
  show (∃ x ∈ U, P.specialMap x = glueTwoOpenMap a b hab hcover y) ↔
    ∃ x ∈ U, Q.specialMap x = y
  constructor
  · rintro ⟨x, hxU, hx⟩
    obtain ⟨x', hx'⟩ := deformationSpecialMap_surjective Q y
    have hinj : x' = x := (deformationSpecialMap_isHomeomorph P).bijective.injective
      (by rw [← hpt x', hx', hx])
    exact ⟨x, hxU, by rw [← hinj, hx']⟩
  · rintro ⟨x, hxU, hx⟩
    exact ⟨x, hxU, by rw [← hpt x, hx]⟩

variable (hbase : b.base = a.base)

include hab hcover hbase in
/-- The glued morphism of total spaces exhibits the second deformation as the base change of the
first: being cartesian is local on the target, and over each of the two opens the square is the
cartesian square of the corresponding restriction. -/
theorem isPullback_glueTwoOpenMap :
    IsPullback (glueTwoOpenMap a b hab hcover) Q.toBase P.toBase (baseSpecMap a.base) := by
  have hca : IsPullback (restrictedOpenHom a) ((restrictedOpen Q U₁).ι ≫ Q.toBase)
      ((restrictedOpen P U₁).ι ≫ P.toBase) (baseSpecMap a.base) := a.cartesian
  have hcb : IsPullback (restrictedOpenHom b) ((restrictedOpen Q U₂).ι ≫ Q.toBase)
      ((restrictedOpen P U₂).ι ≫ P.toBase) (baseSpecMap a.base) := by
    rw [← hbase]
    exact b.cartesian
  have hw : glueTwoOpenMap a b hab hcover ≫ P.toBase =
      Q.toBase ≫ baseSpecMap a.base := by
    refine hom_ext_of_restrictedOpen_cover Q hcover ?_ ?_
    · rw [ι_glueTwoOpenMap_left_assoc, hca.w, Category.assoc]
      rfl
    · rw [ι_glueTwoOpenMap_right_assoc, hcb.w, Category.assoc]
      rfl
  have key : ∀ (U : X.left.Opens)
      (f : (restrictedOpen Q U).toScheme ⟶ (restrictedOpen P U).toScheme),
      IsPullback f ((restrictedOpen Q U).ι ≫ Q.toBase) ((restrictedOpen P U).ι ≫ P.toBase)
          (baseSpecMap a.base) →
        (restrictedOpen Q U).ι ≫ glueTwoOpenMap a b hab hcover = f ≫ (restrictedOpen P U).ι →
        IsPullback (glueTwoOpenMap a b hab hcover ∣_ restrictedOpen P U)
          ((glueTwoOpenMap a b hab hcover ⁻¹ᵁ restrictedOpen P U).ι ≫ Q.toBase)
          ((restrictedOpen P U).ι ≫ P.toBase) (baseSpecMap a.base) := by
    intro U f hf hcomm
    refine hf.of_iso
      (Q.scheme.isoOfEq (glueTwoOpenMap_preimage_restrictedOpen a b hab hcover U)).symm
      (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
    · rw [Iso.refl_hom, Category.comp_id, Iso.symm_hom,
        ← cancel_mono (restrictedOpen P U).ι, Category.assoc, morphismRestrict_ι,
        Scheme.isoOfEq_inv_ι_assoc, hcomm]
    · rw [Iso.refl_hom, Category.comp_id, Iso.symm_hom, Scheme.isoOfEq_inv_ι_assoc]
    · rw [Iso.refl_hom, Iso.refl_hom, Category.comp_id, Category.id_comp]
    · rw [Iso.refl_hom, Iso.refl_hom, Category.comp_id, Category.id_comp]
  refine isPullback_of_iSup_eq_top hw
    (fun c : Bool => restrictedOpen P (bif c then U₂ else U₁)) ?_ ?_
  · rw [iSup_bool_eq, sup_comm]
    exact restrictedOpen_sup_eq_top P hcover
  · rintro (_ | _)
    exacts [key U₁ (restrictedOpenHom a) hca (ι_glueTwoOpenMap_left a b hab hcover),
      key U₂ (restrictedOpenHom b) hcb (ι_glueTwoOpenMap_right a b hab hcover)]

include hab hcover hbase in
/-- **A morphism of deformations is glued from its two restrictions.** Two morphisms of the
restrictions of a deformation of `X` to two opens covering `X`, lying over the same morphism of
`𝒞_Λ` and agreeing on the intersection, come from a morphism of the deformations of `X`. -/
def glueTwoOpenHom : P ⟶ Q where
  base := a.base
  map := glueTwoOpenMap a b hab hcover
  cartesian := isPullback_glueTwoOpenMap a b hab hcover hbase
  special_compat := specialMap_comp_glueTwoOpenMap a b hab hcover

end Glue

/-! ### The comparison isomorphism of the 2-fibre product is agreement on the overlap -/

section Overlap

variable {P Q : SchemeDeformationCategory (Λ := Λ) (k := k) X}

/-- Restricting a morphism of deformations of an open `U` to a smaller open `V` is compatible
with the inclusions of the restricted total spaces. -/
private theorem openRestrictionLE_map_comp_restrictDeformationι (U V : X.left.Opens)
    {A B : SchemeDeformationCategory (Λ := Λ) (k := k) (Over.mk (U.ι ≫ X.hom))} (f : A ⟶ B) :
    (restrictDeformationHom (X := Over.mk (U.ι ≫ X.hom)) (U.ι ⁻¹ᵁ V) f).map ≫
        restrictDeformationι (X := Over.mk (U.ι ≫ X.hom)) (U.ι ⁻¹ᵁ V) A =
      restrictDeformationι (X := Over.mk (U.ι ≫ X.hom)) (U.ι ⁻¹ᵁ V) B ≫ f.map :=
  restrictDeformationHom_map_comp_restrictDeformationι (X := Over.mk (U.ι ≫ X.hom)) _ f

/-- Restricting a morphism of deformations of an open `U` to a smaller open `V` is compatible
with the inclusions of the twice-restricted total spaces.

`Deformation.Examples.nestedι_naturality` is this for a morphism restricted from a deformation
of `X`; the statement here is for an arbitrary morphism of deformations of `U`. The ambient
object of `Over (Spec (.of k))` is given explicitly because inferring it from the open
`U.ι ⁻¹ᵁ V` alone is the higher-order problem `?X.left ≟ U.toScheme`, and every factor is
rewritten through the restricted deformations before the lemma is applied, because a
composition one factor of which is written through the restriction functor and another through
the restricted deformation is type-correct only up to unfolding that functor. -/
theorem openRestrictionLE_map_comp_nestedι {U V : X.left.Opens} (h : V ≤ U)
    (a : restrictDeformation U P ⟶ restrictDeformation U Q) :
    ((openRestrictionLEFunctor h).map a).map ≫ nestedι P h = nestedι Q h ≫ a.map := by
  exact openRestrictionLE_map_comp_restrictDeformationι U V a

variable {U₁ U₂ : X.left.Opens}
  (a : restrictDeformation U₁ P ⟶ restrictDeformation U₁ Q)
  (b : restrictDeformation U₂ P ⟶ restrictDeformation U₂ Q)

include a b in
/-- **The comparison square of the 2-fibre product is agreement on the overlap.** The square
that a morphism of `Deformation.Examples.TwoOpenDeformations` is asked to make commute says
that the two components restrict to the same morphism of the deformations of `U₁ ⊓ U₂`. That
says the same thing as an equation of morphisms out of the open which `U₁ ⊓ U₂` cuts out in the
total space, which is the form in which glueing along an open covering consumes it. -/
theorem overlap_compat_of_comparison_square
    (hw : (openRestrictionLEFunctor (inf_le_left : U₁ ⊓ U₂ ≤ U₁)).map a ≫
        (restrictDeformationLEIso Q (inf_le_left : U₁ ⊓ U₂ ≤ U₁) ≪≫
          (restrictDeformationLEIso Q (inf_le_right : U₁ ⊓ U₂ ≤ U₂)).symm).hom =
      (restrictDeformationLEIso P (inf_le_left : U₁ ⊓ U₂ ≤ U₁) ≪≫
          (restrictDeformationLEIso P (inf_le_right : U₁ ⊓ U₂ ≤ U₂)).symm).hom ≫
        (openRestrictionLEFunctor (inf_le_right : U₁ ⊓ U₂ ≤ U₂)).map b) :
    Q.scheme.homOfLE (restrictedOpen_mono Q (inf_le_left : U₁ ⊓ U₂ ≤ U₁)) ≫
        restrictedOpenHom a ≫ (restrictedOpen P U₁).ι =
      Q.scheme.homOfLE (restrictedOpen_mono Q (inf_le_right : U₁ ⊓ U₂ ≤ U₂)) ≫
        restrictedOpenHom b ≫ (restrictedOpen P U₂).ι := by
  have hnat : ∀ {U : X.left.Opens} (hU : U₁ ⊓ U₂ ≤ U)
      (c : restrictDeformation U P ⟶ restrictDeformation U Q),
      ((openRestrictionLEFunctor hU).map c).map ≫ nestedι P hU ≫ restrictDeformationι U P =
        nestedι Q hU ≫ c.map ≫ restrictDeformationι U P := fun hU c => by
    rw [← Category.assoc, openRestrictionLE_map_comp_nestedι, Category.assoc]
  have hwm : ((nestedOpenIso Q (inf_le_right : U₁ ⊓ U₂ ≤ U₂)).hom ≫
        (nestedOpenIso Q (inf_le_left : U₁ ⊓ U₂ ≤ U₁)).inv) ≫
      ((openRestrictionLEFunctor (inf_le_left : U₁ ⊓ U₂ ≤ U₁)).map a).map =
    ((openRestrictionLEFunctor (inf_le_right : U₁ ⊓ U₂ ≤ U₂)).map b).map ≫
      ((nestedOpenIso P (inf_le_right : U₁ ⊓ U₂ ≤ U₂)).hom ≫
        (nestedOpenIso P (inf_le_left : U₁ ⊓ U₂ ≤ U₁)).inv) :=
    congrArg SchemeDeformationCategory.Hom.map hw
  have key : ((nestedOpenIso Q (inf_le_left : U₁ ⊓ U₂ ≤ U₁)).inv ≫
        nestedι Q (inf_le_left : U₁ ⊓ U₂ ≤ U₁)) ≫ a.map ≫ restrictDeformationι U₁ P =
      ((nestedOpenIso Q (inf_le_right : U₁ ⊓ U₂ ≤ U₂)).inv ≫
        nestedι Q (inf_le_right : U₁ ⊓ U₂ ≤ U₂)) ≫ b.map ≫ restrictDeformationι U₂ P := by
    have h := congrArg
      (fun m => m ≫ nestedι P (inf_le_left : U₁ ⊓ U₂ ≤ U₁) ≫ restrictDeformationι U₁ P) hwm
    simp only [Category.assoc, nestedOpenIso_inv_comp, nestedOpenIso_hom_comp] at h
    rw [hnat, hnat] at h
    rw [← cancel_epi (nestedOpenIso Q (inf_le_right : U₁ ⊓ U₂ ≤ U₂)).hom]
    simpa only [Category.assoc, Iso.hom_inv_id_assoc] using h
  exact ((congrArg (fun m => m ≫ a.map ≫ restrictDeformationι U₁ P)
      (nestedOpenIso_inv_comp_nestedι Q (inf_le_left : U₁ ⊓ U₂ ≤ U₁)).symm).trans key).trans
    (congrArg (fun m => m ≫ b.map ≫ restrictDeformationι U₂ P)
      (nestedOpenIso_inv_comp_nestedι Q (inf_le_right : U₁ ⊓ U₂ ≤ U₂)))

end Overlap

/-! ### The comparison functor is fully faithful -/

section FullyFaithful

variable (X) (U₁ U₂ : X.left.Opens) (hcover : U₁ ⊔ U₂ = ⊤)

include hcover in
/-- **The comparison functor of a two-open cover is faithful.** A morphism of deformations of
`X` is determined by its two restrictions, because the two opens they cut out cover the total
space. -/
theorem faithful_twoOpenComparisonFunctor :
    (twoOpenComparisonFunctor (Λ := Λ) (k := k) X U₁ U₂).Faithful where
  map_injective {P Q} {f g} h := by
    have hbase : f.base = g.base := congrArg TwoFibreProductOver.Hom.hbase h
    have ha : restrictDeformationHom U₁ f = restrictDeformationHom U₁ g :=
      congrArg TwoFibreProductOver.Hom.a h
    have hb : restrictDeformationHom U₂ f = restrictDeformationHom U₂ g :=
      congrArg TwoFibreProductOver.Hom.b h
    refine SchemeDeformationCategory.Hom.ext hbase ?_
    refine hom_ext_of_restrictedOpen_cover Q hcover ?_ ?_
    · change restrictDeformationι U₁ Q ≫ f.map = restrictDeformationι U₁ Q ≫ g.map
      rw [← restrictDeformationHom_map_comp_restrictDeformationι U₁ f,
        ← restrictDeformationHom_map_comp_restrictDeformationι U₁ g, ha]
    · change restrictDeformationι U₂ Q ≫ f.map = restrictDeformationι U₂ Q ≫ g.map
      rw [← restrictDeformationHom_map_comp_restrictDeformationι U₂ f,
        ← restrictDeformationHom_map_comp_restrictDeformationι U₂ g, hb]

include hcover in
/-- **The comparison functor of a two-open cover is full.** The two components of a morphism of
the 2-fibre product agree on the overlap, so they glue to a morphism of deformations of `X`
whose restrictions they are. -/
theorem full_twoOpenComparisonFunctor :
    (twoOpenComparisonFunctor (Λ := Λ) (k := k) X U₁ U₂).Full where
  map_surjective {P Q} φ := by
    have hAB : φ.a.base = φ.b.base := by
      have h : φ.a.base ≫ (𝟙 _ ≫ 𝟙 _) = (𝟙 _ ≫ 𝟙 _) ≫ φ.b.base :=
        congrArg SchemeDeformationCategory.Hom.base φ.w
      simpa only [Category.id_comp, Category.comp_id] using h
    have hab := overlap_compat_of_comparison_square φ.a φ.b φ.w
    have ea : restrictDeformationHom U₁
        (glueTwoOpenHom φ.a φ.b hab hcover hAB.symm) = φ.a := by
      refine SchemeDeformationCategory.Hom.ext rfl ?_
      refine (cancel_mono (restrictDeformationι U₁ P)).mp ?_
      rw [restrictDeformationHom_map_comp_restrictDeformationι]
      exact ι_glueTwoOpenMap_left φ.a φ.b hab hcover
    have eb : restrictDeformationHom U₂
        (glueTwoOpenHom φ.a φ.b hab hcover hAB.symm) = φ.b := by
      refine SchemeDeformationCategory.Hom.ext hAB ?_
      refine (cancel_mono (restrictDeformationι U₂ P)).mp ?_
      rw [restrictDeformationHom_map_comp_restrictDeformationι]
      exact ι_glueTwoOpenMap_right φ.a φ.b hab hcover
    exact ⟨glueTwoOpenHom φ.a φ.b hab hcover hAB.symm,
      TwoFibreProductOver.Hom.ext' ea eb⟩

end FullyFaithful

/-! ### The comparison functor is essentially surjective -/

section EssSurj

variable (X) (U₁ U₂ : X.left.Opens) (Q : TwoOpenDeformations (Λ := Λ) X U₁ U₂)
  (hcover : U₁ ⊔ U₂ = ⊤)

/-- The first chart of the glued deformation, read on the overlap, is the first overlap chart of
the datum sitting inside the glued scheme. -/
theorem overlap_restrictGlueDeformationLeft :
    ((openRestrictionLEFunctor (inf_le_left : U₁ ⊓ U₂ ≤ U₁)).map
          (restrictGlueDeformationLeft X U₁ U₂ Q hcover).hom).map ≫
        (nestedι (glueDeformation X U₁ U₂ Q hcover) (inf_le_left : U₁ ⊓ U₂ ≤ U₁) ≫
          restrictDeformationι U₁ (glueDeformation X U₁ U₂ Q hcover)) =
      glueOverlapι₁ X U₁ U₂ Q ≫ glueι₁ X U₁ U₂ Q := by
  have hA : ((openRestrictionLEFunctor (inf_le_left : U₁ ⊓ U₂ ≤ U₁)).map
        (restrictGlueDeformationLeft X U₁ U₂ Q hcover).hom).map ≫
      nestedι (glueDeformation X U₁ U₂ Q hcover) (inf_le_left : U₁ ⊓ U₂ ≤ U₁) =
    glueOverlapι₁ X U₁ U₂ Q ≫ (restrictGlueDeformationLeft X U₁ U₂ Q hcover).hom.map := by
    exact openRestrictionLE_map_comp_restrictDeformationι U₁ (U₁ ⊓ U₂)
      (restrictGlueDeformationLeft X U₁ U₂ Q hcover).hom
  have e₄ : (restrictGlueDeformationLeft X U₁ U₂ Q hcover).hom.map =
    (glueChartLeftIso X U₁ U₂ Q hcover).hom := rfl
  rw [← Category.assoc, hA, Category.assoc, e₄, glueChartLeftIso_hom_comp_ι]
  rfl

/-- The second chart of the glued deformation, read on the overlap, is the second overlap chart
of the datum sitting inside the glued scheme. -/
theorem overlap_restrictGlueDeformationRight :
    ((openRestrictionLEFunctor (inf_le_right : U₁ ⊓ U₂ ≤ U₂)).map
          (restrictGlueDeformationRight X U₁ U₂ Q hcover).hom).map ≫
        (nestedι (glueDeformation X U₁ U₂ Q hcover) (inf_le_right : U₁ ⊓ U₂ ≤ U₂) ≫
          restrictDeformationι U₂ (glueDeformation X U₁ U₂ Q hcover)) =
      glueOverlapι₂ X U₁ U₂ Q ≫ glueι₂ X U₁ U₂ Q := by
  have hB : ((openRestrictionLEFunctor (inf_le_right : U₁ ⊓ U₂ ≤ U₂)).map
        (restrictGlueDeformationRight X U₁ U₂ Q hcover).hom).map ≫
      nestedι (glueDeformation X U₁ U₂ Q hcover) (inf_le_right : U₁ ⊓ U₂ ≤ U₂) =
    glueOverlapι₂ X U₁ U₂ Q ≫ (restrictGlueDeformationRight X U₁ U₂ Q hcover).hom.map := by
    exact openRestrictionLE_map_comp_restrictDeformationι U₂ (U₁ ⊓ U₂)
      (restrictGlueDeformationRight X U₁ U₂ Q hcover).hom
  have e₄ : (restrictGlueDeformationRight X U₁ U₂ Q hcover).hom.map =
    (glueChartRightIso X U₁ U₂ Q hcover).hom := rfl
  rw [← Category.assoc, hB, Category.assoc, e₄, glueChartRightIso_hom_comp_ι]
  rfl

/-- The comparison isomorphism of a datum identifies the inverse isomorphism of bases with the
comparison of the two ways of reading the base of the datum. -/
theorem glueBaseIsoInv_eq_eqToHom :
    glueBaseIsoInv X U₁ U₂ Q = eqToHom Q.hx ≫ eqToHom Q.hy.symm := by
  rw [← cancel_epi (glueBaseIso X U₁ U₂ Q), glueBaseIso_comp_glueBaseIsoInv,
    ← Category.assoc, glueBaseIso_comp_eqToHom, eqToHom_trans, eqToHom_refl]

/-- The first chart of the glued scheme, read on the overlap through the comparison isomorphism
of the datum, is the overlap chart of the glued scheme. -/
theorem isoHom_map_comp_glueι₀ :
    Q.iso.hom.map ≫ glueι₀ X U₁ U₂ Q = glueOverlapι₂ X U₁ U₂ Q ≫ glueι₂ X U₁ U₂ Q := by
  have htr : Q.iso.hom.map ≫ glueTransition X U₁ U₂ Q = 𝟙 _ :=
    congrArg SchemeDeformationCategory.Hom.map Q.iso.inv_hom_id
  rw [← glueOverlapι₂_comp_glueι₂, ← Category.assoc, htr, Category.id_comp]

/-- **The glued deformation restricts to the datum it was glued from, compatibly with the
comparison isomorphism.** This is the square which makes the two chart isomorphisms a single
isomorphism of the 2-fibre product. -/
theorem glueDeformation_comparison_square :
    (openRestrictionLEFunctor (inf_le_left : U₁ ⊓ U₂ ≤ U₁)).map
        (restrictGlueDeformationLeft X U₁ U₂ Q hcover).hom ≫ Q.iso.hom =
      (restrictDeformationLEIso (glueDeformation X U₁ U₂ Q hcover)
            (inf_le_left : U₁ ⊓ U₂ ≤ U₁) ≪≫
          (restrictDeformationLEIso (glueDeformation X U₁ U₂ Q hcover)
            (inf_le_right : U₁ ⊓ U₂ ≤ U₂)).symm).hom ≫
        (openRestrictionLEFunctor (inf_le_right : U₁ ⊓ U₂ ≤ U₂)).map
          (restrictGlueDeformationRight X U₁ U₂ Q hcover).hom := by
  refine SchemeDeformationCategory.Hom.ext ?_ ?_
  · have h0 : glueBaseIso X U₁ U₂ Q ≫ Q.iso.hom.base = 𝟙 Q.y.base :=
      congrArg SchemeDeformationCategory.Hom.base Q.iso.inv_hom_id
    show glueBaseIso X U₁ U₂ Q ≫ Q.iso.hom.base = (𝟙 _ ≫ 𝟙 _) ≫ 𝟙 _
    rw [h0, Category.id_comp, Category.comp_id]
  · refine (cancel_mono
      (nestedι (glueDeformation X U₁ U₂ Q hcover) (inf_le_left : U₁ ⊓ U₂ ≤ U₁) ≫
        restrictDeformationι U₁ (glueDeformation X U₁ U₂ Q hcover))).mp ?_
    show (Q.iso.hom.map ≫
        ((openRestrictionLEFunctor (inf_le_left : U₁ ⊓ U₂ ≤ U₁)).map
          (restrictGlueDeformationLeft X U₁ U₂ Q hcover).hom).map) ≫
        (nestedι (glueDeformation X U₁ U₂ Q hcover) (inf_le_left : U₁ ⊓ U₂ ≤ U₁) ≫
          restrictDeformationι U₁ (glueDeformation X U₁ U₂ Q hcover)) =
      (((openRestrictionLEFunctor (inf_le_right : U₁ ⊓ U₂ ≤ U₂)).map
            (restrictGlueDeformationRight X U₁ U₂ Q hcover).hom).map ≫
          ((nestedOpenIso (glueDeformation X U₁ U₂ Q hcover)
              (inf_le_right : U₁ ⊓ U₂ ≤ U₂)).hom ≫
            (nestedOpenIso (glueDeformation X U₁ U₂ Q hcover)
              (inf_le_left : U₁ ⊓ U₂ ≤ U₁)).inv)) ≫
        (nestedι (glueDeformation X U₁ U₂ Q hcover) (inf_le_left : U₁ ⊓ U₂ ≤ U₁) ≫
          restrictDeformationι U₁ (glueDeformation X U₁ U₂ Q hcover))
    rw [Category.assoc, overlap_restrictGlueDeformationLeft, glueOverlapι₁_comp_glueι₁,
      Category.assoc, Category.assoc, nestedOpenIso_inv_comp, nestedOpenIso_hom_comp,
      overlap_restrictGlueDeformationRight]
    exact isoHom_map_comp_glueι₀ X U₁ U₂ Q

/-- The inverse square: the datum is recovered from the glued deformation compatibly with the
comparison isomorphism. -/
theorem glueDeformation_comparison_square_inv :
    (openRestrictionLEFunctor (inf_le_left : U₁ ⊓ U₂ ≤ U₁)).map
        (restrictGlueDeformationLeft X U₁ U₂ Q hcover).inv ≫
      (restrictDeformationLEIso (glueDeformation X U₁ U₂ Q hcover)
            (inf_le_left : U₁ ⊓ U₂ ≤ U₁) ≪≫
          (restrictDeformationLEIso (glueDeformation X U₁ U₂ Q hcover)
            (inf_le_right : U₁ ⊓ U₂ ≤ U₂)).symm).hom =
      Q.iso.hom ≫ (openRestrictionLEFunctor (inf_le_right : U₁ ⊓ U₂ ≤ U₂)).map
        (restrictGlueDeformationRight X U₁ U₂ Q hcover).inv := by
  rw [← cancel_epi ((openRestrictionLEFunctor (inf_le_left : U₁ ⊓ U₂ ≤ U₁)).map
    (restrictGlueDeformationLeft X U₁ U₂ Q hcover).hom)]
  simp only [← Category.assoc]
  rw [Iso.map_hom_inv_id, Category.id_comp, glueDeformation_comparison_square X U₁ U₂ Q hcover,
    Category.assoc, Iso.map_hom_inv_id, Category.comp_id]

/-- **Stacks 0DYZ**, the glueing quasi-inverse on objects, as an isomorphism of the 2-fibre
product: the two chart isomorphisms of the glued deformation are a single isomorphism
`Def_X ∋ glueDeformation Q ↦ Q` in `Def_{U₁} ×_{Def_{U₁ ⊓ U₂}} Def_{U₂}`. -/
def glueDeformationComparisonIso :
    (twoOpenComparisonFunctor (Λ := Λ) (k := k) X U₁ U₂).obj
      (glueDeformation X U₁ U₂ Q hcover) ≅ Q where
  hom :=
    { hbase := eqToHom Q.hy
      a := (restrictGlueDeformationLeft X U₁ U₂ Q hcover).hom
      b := (restrictGlueDeformationRight X U₁ U₂ Q hcover).hom
      ha := by
        refine CategoryTheory.IsHomLift.of_fac' _ (eqToHom Q.hy) _ rfl Q.hx ?_
        change glueBaseIso X U₁ U₂ Q = 𝟙 Q.y.base ≫ eqToHom Q.hy ≫ eqToHom Q.hx.symm
        rw [Category.id_comp, ← glueBaseIso_comp_eqToHom X U₁ U₂ Q, Category.assoc,
          eqToHom_trans, eqToHom_refl, Category.comp_id]
      hb := by
        refine CategoryTheory.IsHomLift.of_fac' _ (eqToHom Q.hy) _ rfl Q.hy ?_
        change 𝟙 Q.y.base = 𝟙 Q.y.base ≫ eqToHom Q.hy ≫ eqToHom Q.hy.symm
        rw [Category.id_comp, eqToHom_trans, eqToHom_refl]
      w := glueDeformation_comparison_square X U₁ U₂ Q hcover }
  inv :=
    { hbase := eqToHom Q.hy.symm
      a := (restrictGlueDeformationLeft X U₁ U₂ Q hcover).inv
      b := (restrictGlueDeformationRight X U₁ U₂ Q hcover).inv
      ha := by
        refine CategoryTheory.IsHomLift.of_fac' _ (eqToHom Q.hy.symm) _ Q.hx rfl ?_
        exact glueBaseIsoInv_eq_eqToHom X U₁ U₂ Q
      hb := by
        refine CategoryTheory.IsHomLift.of_fac' _ (eqToHom Q.hy.symm) _ Q.hy rfl ?_
        change 𝟙 Q.y.base = eqToHom Q.hy ≫ eqToHom Q.hy.symm
        rw [eqToHom_trans, eqToHom_refl]
        rfl
      w := glueDeformation_comparison_square_inv X U₁ U₂ Q hcover }
  hom_inv_id := TwoFibreProductOver.Hom.ext'
    (restrictGlueDeformationLeft X U₁ U₂ Q hcover).hom_inv_id
    (restrictGlueDeformationRight X U₁ U₂ Q hcover).hom_inv_id
  inv_hom_id := TwoFibreProductOver.Hom.ext'
    (restrictGlueDeformationLeft X U₁ U₂ Q hcover).inv_hom_id
    (restrictGlueDeformationRight X U₁ U₂ Q hcover).inv_hom_id

end EssSurj

/-! ### The comparison functor is an equivalence -/

section Equivalence

variable (X) (U₁ U₂ : X.left.Opens) (hcover : U₁ ⊔ U₂ = ⊤)

include hcover in
/-- **The comparison functor of a two-open cover is essentially surjective.** Every object of
the 2-fibre product is the pair of restrictions of the deformation glued from it. -/
theorem essSurj_twoOpenComparisonFunctor :
    (twoOpenComparisonFunctor (Λ := Λ) (k := k) X U₁ U₂).EssSurj where
  mem_essImage Q :=
    ⟨glueDeformation X U₁ U₂ Q hcover, ⟨glueDeformationComparisonIso X U₁ U₂ Q hcover⟩⟩

include hcover in
/-- **Stacks 0DYZ.** Let `X` be a scheme over the residue field `k` covered by two opens `U₁`
and `U₂`. The comparison functor from the deformation category of `X` to the 2-fibre product
`Def_{U₁} ×_{Def_{U₁ ⊓ U₂}} Def_{U₂}` over `𝒞_Λ` is an equivalence: it is faithful and full
because a morphism of deformations of `X` is determined by, and glues from, its two
restrictions, and it is essentially surjective because every object of the 2-fibre product is
the pair of restrictions of the deformation glued from it. -/
theorem isEquivalence_twoOpenComparisonFunctor :
    (twoOpenComparisonFunctor (Λ := Λ) (k := k) X U₁ U₂).IsEquivalence where
  faithful := faithful_twoOpenComparisonFunctor X U₁ U₂ hcover
  full := full_twoOpenComparisonFunctor X U₁ U₂ hcover
  essSurj := essSurj_twoOpenComparisonFunctor X U₁ U₂ hcover

/-- **Stacks 0DYZ**, as an equivalence of categories: the deformation category of a scheme
covered by two opens is the 2-fibre product of the deformation categories of the two opens over
that of their intersection. -/
def twoOpenDeformationsEquivalence (hcov : U₁ ⊔ U₂ = ⊤) :
    SchemeDeformationCategory (Λ := Λ) (k := k) X ≌
      TwoOpenDeformations (Λ := Λ) (k := k) X U₁ U₂ :=
  haveI := isEquivalence_twoOpenComparisonFunctor (Λ := Λ) (k := k) X U₁ U₂ hcov
  (twoOpenComparisonFunctor (Λ := Λ) (k := k) X U₁ U₂).asEquivalence

end Equivalence

/-! ### The equivalence in Situation 0DYY -/

/-- **Stacks 0DYZ** in Situation 0DYY: the comparison functor of the two-open cover of the
glueing situation is an equivalence of deformation categories. No affineness of the two opens
or of their intersection is used. -/
theorem GluingSituation.isEquivalence_comparisonFunctor (S : GluingSituation Λ k) :
    (GluingSituation.comparisonFunctor S).IsEquivalence :=
  isEquivalence_twoOpenComparisonFunctor S.X S.U₁ S.U₂ S.cover

/-- **Stacks 0DYZ** in Situation 0DYY, as an equivalence of categories. -/
def GluingSituation.deformationEquivalence (S : GluingSituation Λ k) :
    SchemeDeformationCategory (Λ := Λ) (k := k) S.X ≌
      TwoOpenDeformations (Λ := Λ) (k := k) S.X S.U₁ S.U₂ :=
  twoOpenDeformationsEquivalence S.X S.U₁ S.U₂ S.cover

end Deformation.Examples

end
