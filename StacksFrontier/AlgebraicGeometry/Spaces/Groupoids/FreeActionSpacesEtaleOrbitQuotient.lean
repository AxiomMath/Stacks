module

public import StacksFrontier.AlgebraicGeometry.Spaces.AlternatingCech.DiagonalComplement
public import StacksFrontier.AlgebraicGeometry.Spaces.CoproductDecomposition
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatFieldCover
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.FreeActionQuotientEtaleProjection
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.More.UnibranchIdentityArrow
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.SpacesEtaleSignTwist
public import StacksFrontier.CategoryTheory.Sites.FreeActionOrbitQuotientTorsor

/-!
# The quotient of a free action is the orbit quotient on the spaces-étale site

Let `W` be an algebraic space over a scheme `S` carrying a free action of an abstract group
`G`, and let `U = W/G` be the quotient, which is an algebraic space by Tag 071S. The quotient
morphism `q : W ⟶ U` is surjective and étale, so `W` is an object of the *spaces-étale site*
of `U`. This file proves that `q` exhibits the final object of that site as the quotient of
`W` by `G` in the sense of `CategoryTheory.IsOrbitQuotient`, hence — the action being free —
that `W` is a `G`-torsor over the final object there.

The content is a refinement from the fppf topology to the étale one. Tag 071S identifies `U`
with the quotient of `W` by `G` as a sheaf on the **big fppf** site: two points of `W` over a
test object with the same image in `U` are translates of each other by a single group element
only locally for the fppf topology
(`AlgebraicGeometry.Space.orbitSieve_mem`). `CategoryTheory.IsOrbitQuotient` at the
spaces-étale site of `U` asks for the same statement with étale-local replaced for
fppf-local, which is a strictly stronger demand. What supplies it is that the covering may be
taken to consist of the *open equalizer loci* of the two morphisms: for each `g ∈ G` the locus
in an object `V` of the site where one morphism `V ⟶ W` agrees with the `g`-translate of
another is the fibre product of `V` with `W` over `W ×_U W`, hence again an object of the
site, and the fppf statement is exactly what makes those finitely many loci cover `V` *on
points*. Since a jointly point-surjective family is a covering family of the spaces-étale
site, that is the required étale covering.

## Main definitions

* `AlgebraicGeometry.Space.translationPair` is the morphism `⟨ψ, g · φ⟩ : V ⟶ Y ×_X Y`
  attached to two morphisms `φ ψ : V ⟶ Y` of a spaces-étale site, an action of `G` on `Y` by
  automorphisms and a group element, and `AlgebraicGeometry.Space.translationLocus` is the
  **open equalizer locus** where the two agree: the fibre product of that morphism with the
  diagonal of `Y ×_X Y`.
* `AlgebraicGeometry.Space.orbitQuotientSpace` is the quotient `U = W/G` as an algebraic
  space, and `AlgebraicGeometry.Space.toOrbitQuotientSpace` the quotient morphism.
* `AlgebraicGeometry.Space.orbitQuotientEtaleSource` is `W` read as an object of the
  spaces-étale site of `U`, with `AlgebraicGeometry.Space.orbitQuotientActionEtale` and
  `AlgebraicGeometry.Space.orbitQuotientAut` the action of `G` on it by automorphisms.

## Main results

* `AlgebraicGeometry.Space.exists_fieldValuedPoint_sieve_arrow`: **a covering sieve of the big
  fppf site over `S` on the field spectrum of a field-valued point contains an arrow from the
  field spectrum of a field-valued point refining it.** This is what turns a covering sieve
  into a statement about one point.
* `AlgebraicGeometry.Space.FieldValuedPoint.map_congr_app` and
  `AlgebraicGeometry.Space.FieldValuedPoint.class_map_eq_of_app_eq`: two morphisms of
  presheaves agreeing on the section of a field-valued point carry that point to the same
  point.
* `AlgebraicGeometry.Space.SpacesEtale.prodTwo_section_ext`: a section of `Y ×_X Y` over a
  test object is determined by its two projections.
* `AlgebraicGeometry.Space.translationLocus_fst_mem_translationSieve`: on the open equalizer
  locus the two morphisms are translates of each other.
* `AlgebraicGeometry.Space.exists_translation_point` and
  `AlgebraicGeometry.Space.translationSieve_mem_of_orbitSieve`: **the fppf-to-étale
  refinement.** If two sections of `Y` with the same image in `X` become translates of each
  other along a covering sieve of the big fppf site, then two morphisms `V ⟶ Y` of the
  spaces-étale site of `X` become translates of each other on an *étale* covering of `V`,
  namely the open equalizer loci, which cover `V` on points.
* `AlgebraicGeometry.Space.SpacesEtale.splittingSieve_mem_of_isSurjective`: the morphisms to
  `Y` cover every object of the spaces-étale site of `X` when the structure morphism of `Y` is
  surjective on points.
* `AlgebraicGeometry.Space.actsFreelyOnObject_of_eq_one_of_nonempty`: an action free on the
  sections over the test objects with nonempty underlying scheme is free on the objects of the
  spaces-étale site, in the sense of `CategoryTheory.ActsFreelyOnObject`.
* `AlgebraicGeometry.Space.eq_one_of_smul_eq`,
  `AlgebraicGeometry.Space.actsFreelyOnObject_orbitQuotientAut`,
  `AlgebraicGeometry.Space.splittingSieve_mem_spacesEtale` and
  `AlgebraicGeometry.Space.translationSieve_mem_spacesEtale`: those three hypotheses
  discharged for the quotient of a free action, the last from
  `AlgebraicGeometry.Space.orbitSieve_mem`.
* `AlgebraicGeometry.Space.isTorsorObject_orbitQuotientAut` and
  `AlgebraicGeometry.Space.isOrbitQuotient_orbitQuotientAut`: **the quotient morphism exhibits
  the final object of the spaces-étale site of `U` as `W/G`, and `W` is a `G`-torsor over
  it.**

## Implementation notes

Freeness of the action is `AlgebraicGeometry.Space.IsFreeOnNonemptyPoints`, as in Tag 071S:
cancellativity on the points over the test objects whose underlying scheme is nonempty.
Asking for it over every test object would force `G` to be trivial. Note that this hypothesis
is about arbitrary test objects of the big fppf site, whereas
`CategoryTheory.ActsFreelyOnObject` is about the objects of the spaces-étale site; the former
implies the latter, through the field-valued points of an object of the site, and that is
`AlgebraicGeometry.Space.actsFreelyOnObject_orbitQuotientAut`.

The fibre square `W ×_U W` and its diagonal are the ones of
`AlgebraicGeometry.Space.SpacesEtale.prodTwo` and
`AlgebraicGeometry.Space.SpacesEtale.diagTwo`: products in the spaces-étale site of `U` are
fibre products over `U`, the final object of the site being the identity of `U`.

No finiteness of `G` is used. Finiteness enters the geometry of Stacks 0727 only through the
étaleness of the quotient morphism, which is a hypothesis here by way of
`AlgebraicGeometry.Space.isEtale_toOrbitQuotient`, itself proved without finiteness.

## References

* [Stacks Project, Tag 071S](https://stacks.math.columbia.edu/tag/071S)
* [Stacks Project, Tag 03G0](https://stacks.math.columbia.edu/tag/03G0)
* [Stacks Project, Tag 03H4](https://stacks.math.columbia.edu/tag/03H4)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

/-! ### Refining a field-valued point along a covering sieve -/

section SieveArrow

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A covering sieve on the field spectrum of a field-valued point contains an arrow from
the field spectrum of a field-valued point refining it.**

A covering sieve of the big fppf site is jointly surjective on the points of the underlying
schemes, and the field spectrum has a point; so the sieve contains an arrow whose source has a
point, and a field spectrum in the site maps onto that point. Restricting the given section
along the composite gives the refining field-valued point. -/
theorem exists_fieldValuedPoint_sieve_arrow {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (p : FieldValuedPoint B S hS F) {R : Sieve (FieldValuedPoint.siteObject B S hS F p)}
    (hR : R ∈ BigFppfOver.topology B S hS (FieldValuedPoint.siteObject B S hS F p)) :
    ∃ (q : FieldValuedPoint B S hS F)
      (f : FieldValuedPoint.siteObject B S hS F q ⟶
        FieldValuedPoint.siteObject B S hS F p),
      R.arrows f ∧ F.map f.op p.value = q.value := by
  classical
  obtain ⟨Y, f, hf, z, hz⟩ := BigFppfOver.exists_mem_arrows_mem_range B S hS hR
    (IsLocalRing.closedPoint p.carrier)
  obtain ⟨K, _, hK, ρ, -⟩ := exists_fieldSpec_at_point B Y.left.property z
  refine ⟨{ carrier := K, contained := hK, toBase := ρ ≫ B.inclusion.map Y.hom,
            value := F.map (Over.homMk (ObjectProperty.homMk ρ) rfl ≫ f).op p.value },
    Over.homMk (ObjectProperty.homMk ρ) rfl ≫ f, R.downward_closed hf _, rfl⟩

/-- Two morphisms of presheaves agreeing on the section of a field-valued point send it to the
same field-valued point: the two images differ only in that section. -/
theorem FieldValuedPoint.map_congr_app {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (α β : F ⟶ G) (p : FieldValuedPoint B S hS F)
    (h : α.app (op (FieldValuedPoint.siteObject B S hS F p)) p.value =
      β.app (op (FieldValuedPoint.siteObject B S hS F p)) p.value) :
    FieldValuedPoint.map B S hS F α p = FieldValuedPoint.map B S hS F β p := by
  unfold FieldValuedPoint.map
  rw [h]

/-- **Two morphisms of presheaves agreeing on the section of a field-valued point carry that
point to the same point.** -/
theorem FieldValuedPoint.class_map_eq_of_app_eq {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (α β : F ⟶ G) (p : FieldValuedPoint B S hS F)
    (h : α.app (op (FieldValuedPoint.siteObject B S hS F p)) p.value =
      β.app (op (FieldValuedPoint.siteObject B S hS F p)) p.value) :
    pointsMap B S hS F α (FieldValuedPoint.class B S hS F p) =
      pointsMap B S hS F β (FieldValuedPoint.class B S hS F p) := by
  rw [pointsMap_class, pointsMap_class]
  exact congrArg (FieldValuedPoint.class B S hS G)
    (FieldValuedPoint.map_congr_app B S hS α β p h)

end SieveArrow

/-! ### Sections of a fibre square of the spaces-étale site -/

namespace SpacesEtale

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (X : AlgebraicSpaces B S hS)

/-- **A section of `U ×_X U` is determined by its two projections.** The algebraic space
underlying the fibre square is the presheaf fibre product, where a section is a compatible
pair of sections. -/
theorem prodTwo_section_ext (U : SpacesEtale B S hS X) {T : (BigFppfOver B S hS)ᵒᵖ}
    {a b : (underlying B S hS X (prodTwo B S hS X U)).1.obj T}
    (h₁ : ((toSpaces B S hS X).map
        (pullback.fst (toFinal B S hS U) (toFinal B S hS U))).hom.app T a =
      ((toSpaces B S hS X).map
        (pullback.fst (toFinal B S hS U) (toFinal B S hS U))).hom.app T b)
    (h₂ : ((toSpaces B S hS X).map
        (pullback.snd (toFinal B S hS U) (toFinal B S hS U))).hom.app T a =
      ((toSpaces B S hS X).map
        (pullback.snd (toFinal B S hS U) (toFinal B S hS U))).hom.app T b) :
    a = b := by
  have hsq := AlgebraicSpaces.isPullback_hom B S hS (isPullback_toSpaces_prodTwo B S hS X U)
  have hT := ((evaluation ((BigFppfOver B S hS)ᵒᵖ) (Type u)).obj T).map_isPullback hsq
  exact (((Types.isPullback_iff _ _ _ _).mp hT).2.1 a b ⟨h₁, h₂⟩)

end SpacesEtale

/-! ### The open equalizer loci, and the fppf-to-étale refinement -/

section Refinement

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {X : AlgebraicSpaces B S hS} {G : Type u} [Group G] {Y : SpacesEtale B S hS X}

/-- The morphism `⟨ψ, g · φ⟩ : V ⟶ Y ×_X Y` attached to two morphisms `φ ψ : V ⟶ Y` of the
spaces-étale site of `X`, an action of `G` on `Y` by automorphisms and a group element. -/
def translationPair (act : G →* Aut Y) {V : SpacesEtale B S hS X} (φ ψ : V ⟶ Y) (g : G) :
    V ⟶ SpacesEtale.prodTwo B S hS X Y :=
  pullback.lift ψ (φ ≫ (act g).asIso.hom) ((SpacesEtale.final_isTerminal B S hS X).hom_ext _ _)

/-- The first component of `translationPair act φ ψ g` is `ψ`. -/
@[simp]
theorem translationPair_comp_fst (act : G →* Aut Y) {V : SpacesEtale B S hS X}
    (φ ψ : V ⟶ Y) (g : G) :
    translationPair act φ ψ g ≫
        pullback.fst (SpacesEtale.toFinal B S hS Y) (SpacesEtale.toFinal B S hS Y) = ψ :=
  pullback.lift_fst _ _ _

/-- The second component of `translationPair act φ ψ g` is `φ ≫ (act g).asIso.hom`. -/
@[simp]
theorem translationPair_comp_snd (act : G →* Aut Y) {V : SpacesEtale B S hS X}
    (φ ψ : V ⟶ Y) (g : G) :
    translationPair act φ ψ g ≫
        pullback.snd (SpacesEtale.toFinal B S hS Y) (SpacesEtale.toFinal B S hS Y) =
      φ ≫ (act g).asIso.hom :=
  pullback.lift_snd _ _ _

/-- **The locus in `V` where `ψ` agrees with the `g`-translate of `φ`**: the fibre product of
`⟨ψ, g · φ⟩` with the diagonal of `Y ×_X Y`. It is again an object of the spaces-étale site of
`X`, that site having fibre products, and it is the *open equalizer locus* of the two
morphisms, the diagonal of an object of the site being an open immersion. -/
def translationLocus (act : G →* Aut Y) {V : SpacesEtale B S hS X} (φ ψ : V ⟶ Y) (g : G) :
    SpacesEtale B S hS X :=
  pullback (translationPair act φ ψ g) (SpacesEtale.diagTwo B S hS X Y)

/-- **On the open equalizer locus the two morphisms are translates of each other**, so the
projection of that locus to `V` belongs to the sieve of arrows along which `φ` and `ψ` become
translates. -/
theorem translationLocus_fst_mem_translationSieve (act : G →* Aut Y)
    {V : SpacesEtale B S hS X} (φ ψ : V ⟶ Y) (g : G) :
    translationSieve act φ ψ
      (pullback.fst (translationPair act φ ψ g) (SpacesEtale.diagTwo B S hS X Y)) := by
  refine ⟨g, ?_⟩
  have h := pullback.condition (f := translationPair act φ ψ g)
    (g := SpacesEtale.diagTwo B S hS X Y)
  have h₁ := congrArg (fun k => k ≫ pullback.fst
    (SpacesEtale.toFinal B S hS Y) (SpacesEtale.toFinal B S hS Y)) h
  have h₂ := congrArg (fun k => k ≫ pullback.snd
    (SpacesEtale.toFinal B S hS Y) (SpacesEtale.toFinal B S hS Y)) h
  simp only [Category.assoc, translationPair_comp_fst, translationPair_comp_snd,
    SpacesEtale.diagTwo_comp_fst, SpacesEtale.diagTwo_comp_snd, Category.comp_id] at h₁ h₂
  exact h₁.trans h₂.symm

/-- The map on sections over a test object of a composite of morphisms of the spaces-étale
site of `X` is the composite of the maps on sections. -/
private theorem toSpaces_map_app_comp_apply {V W Z : SpacesEtale B S hS X} (f : V ⟶ W) (g : W ⟶ Z)
    {k : V ⟶ Z} (h : f ≫ g = k) (T : (BigFppfOver B S hS)ᵒᵖ)
    (x : (SpacesEtale.underlying B S hS X V).1.obj T) :
    ((SpacesEtale.toSpaces B S hS X).map g).hom.app T
        (((SpacesEtale.toSpaces B S hS X).map f).hom.app T x) =
      ((SpacesEtale.toSpaces B S hS X).map k).hom.app T x := by
  subst h
  rw [SpacesEtale.hom_toSpaces_map_comp]
  rfl

/-- A point of `A` and a point of `C` with the same image in `D` lift to a point of the fibre
product `A ×_D C`, which maps to the point of `A`. -/
private theorem exists_point_pullback_fst {A C D : SpacesEtale B S hS X} (f : A ⟶ D) (g : C ⟶ D)
    (x : points B S hS (SpacesEtale.underlying B S hS X A).1)
    (w : points B S hS (SpacesEtale.underlying B S hS X C).1)
    (hw : pointsMap B S hS _ ((SpacesEtale.toSpaces B S hS X).map f).hom x =
      pointsMap B S hS _ ((SpacesEtale.toSpaces B S hS X).map g).hom w) :
    ∃ y, pointsMap B S hS _
      ((SpacesEtale.toSpaces B S hS X).map (pullback.fst f g)).hom y = x := by
  obtain ⟨y, hy, -⟩ := exists_point_of_isPullback B S hS
    ((IsPullback.of_hasPullback f g).map (SpacesEtale.toSpaces B S hS X)) x w hw
  exact ⟨y, hy⟩

/-- **The morphisms to `Y` cover every object of the spaces-étale site of `X`** when the
structure morphism of `Y` is surjective on points: the fibre product of an object `V` with `Y`
over `X` is again an object of the site, it maps to `Y`, and it is surjective on the points of
`V` by Tag 03H4. -/
theorem SpacesEtale.splittingSieve_mem_of_isSurjective
    (hsurj : IsSurjective B S hS Y.1.hom.hom) (V : SpacesEtale B S hS X) :
    splittingSieve Y V ∈ SpacesEtale.topology B S hS X V := by
  classical
  rw [SpacesEtale.mem_topology_iff_sievePointwiseCover]
  intro x
  refine ⟨pullback (SpacesEtale.toFinal B S hS V) (SpacesEtale.toFinal B S hS Y),
    pullback.fst _ _, ⟨pullback.snd _ _⟩, ?_⟩
  obtain ⟨w, hw⟩ := hsurj (pointsMap B S hS _
    ((SpacesEtale.toSpaces B S hS X).map (SpacesEtale.toFinal B S hS V)).hom x)
  exact exists_point_pullback_fst _ _ x w hw.symm

/-- **An action free on the sections over the test objects with nonempty underlying scheme is
free on the objects of the spaces-étale site.** An object of the site that the empty sieve does
not cover has a point, and a point is a field-valued point, whose field spectrum is such a test
object. -/
theorem actsFreelyOnObject_of_eq_one_of_nonempty (act : G →* Aut Y)
    (hfr : ∀ {T : (BigFppfOver B S hS)ᵒᵖ} (ξ : (SpacesEtale.underlying B S hS X Y).1.obj T),
      Nonempty ((BigFppfOver.toScheme B S hS).obj T.unop) →
      ∀ g : G, ((SpacesEtale.toSpaces B S hS X).map (act g).asIso.hom).hom.app T ξ = ξ → g = 1) :
    ActsFreelyOnObject act (SpacesEtale.topology B S hS X) := by
  classical
  intro V φ g hφ
  by_cases hV : IsEmpty (points B S hS (SpacesEtale.underlying B S hS X V).1)
  · exact Or.inl (SpacesEtale.bot_mem_topology_of_isEmpty_points B S hS X V hV)
  refine Or.inr ?_
  obtain ⟨x⟩ := not_isEmpty_iff.mp hV
  obtain ⟨p, rfl⟩ := Quot.exists_rep x
  refine hfr (((SpacesEtale.toSpaces B S hS X).map φ).hom.app
      (op (FieldValuedPoint.siteObject B S hS _ p)) p.value)
    ⟨IsLocalRing.closedPoint p.carrier⟩ g ?_
  exact toSpaces_map_app_comp_apply φ (act g).asIso.hom hφ _ _

/-- **The fppf-to-étale refinement, on points.** Suppose that two sections of `Y` over a test
object with the same image in `X` become translates of each other by a single group element
along the arrows of some covering sieve of the **big fppf** site. Then for two morphisms
`φ ψ : V ⟶ Y` of the spaces-étale site of `X` and a point of `V`, some group element `g`
carries that point into the open equalizer locus of `ψ` and the `g`-translate of `φ`: the pair
`⟨ψ, g · φ⟩` sends the point into the diagonal of `Y ×_X Y`.

A point of `V` is the class of a field-valued point; over its field spectrum `φ` and `ψ` give
two sections of `Y` with the same image in `X`, both being morphisms over `X`. The hypothesis
makes those two sections translates of each other after an fppf covering of the field
spectrum, and a covering sieve of the big fppf site is jointly surjective on the points of the
underlying schemes, so the covering may be refined to a single morphism from the field spectrum
of another field-valued point of `V` defining the *same* point. Over that field spectrum the
two sections are translates of each other, which is the assertion. -/
theorem exists_translation_point (act : G →* Aut Y)
    (horb : ∀ {T : (BigFppfOver B S hS)ᵒᵖ}
      (ξ η : (SpacesEtale.underlying B S hS X Y).1.obj T),
      Y.1.hom.hom.app T ξ = Y.1.hom.hom.app T η →
      ∃ R : Sieve T.unop, R ∈ BigFppfOver.topology B S hS T.unop ∧
        ∀ ⦃b : BigFppfOver B S hS⦄ (f : b ⟶ T.unop), R.arrows f →
          ∃ g : G, ((SpacesEtale.toSpaces B S hS X).map (act g).asIso.hom).hom.app (op b)
              ((SpacesEtale.underlying B S hS X Y).1.map f.op η) =
            (SpacesEtale.underlying B S hS X Y).1.map f.op ξ)
    {V : SpacesEtale B S hS X} (φ ψ : V ⟶ Y)
    (x : points B S hS (SpacesEtale.underlying B S hS X V).1) :
    ∃ (g : G) (w : points B S hS (SpacesEtale.underlying B S hS X Y).1),
      pointsMap B S hS _
          ((SpacesEtale.toSpaces B S hS X).map (translationPair act φ ψ g)).hom x =
        pointsMap B S hS _
          ((SpacesEtale.toSpaces B S hS X).map (SpacesEtale.diagTwo B S hS X Y)).hom w := by
  classical
  obtain ⟨p, rfl⟩ := Quot.exists_rep x
  have hstr := fun χ : V ⟶ Y => ConcreteCategory.congr_hom (NatTrans.congr_app
    (SpacesEtale.hom_toSpaces_map_comp_structure B S hS X χ)
    (op (FieldValuedPoint.siteObject B S hS _ p))) p.value
  obtain ⟨R, hR, hRtr⟩ := horb _ _ ((hstr φ).trans (hstr ψ).symm)
  obtain ⟨p', f, hf, hval⟩ := exists_fieldValuedPoint_sieve_arrow B S hS p hR
  obtain ⟨g, hg⟩ := hRtr f hf
  have hnat : ∀ χ : V ⟶ Y, ((SpacesEtale.toSpaces B S hS X).map χ).hom.app
        (op (FieldValuedPoint.siteObject B S hS _ p')) p'.value =
      (SpacesEtale.underlying B S hS X Y).1.map f.op
        (((SpacesEtale.toSpaces B S hS X).map χ).hom.app
          (op (FieldValuedPoint.siteObject B S hS _ p)) p.value) := fun χ => by
    rw [← hval]
    exact NatTrans.naturality_apply ((SpacesEtale.toSpaces B S hS X).map χ).hom f.op p.value
  have hcancel : (act g).asIso.hom ≫ (act g⁻¹).asIso.hom = 𝟙 Y := by
    rw [← act_hom_mul, inv_mul_cancel, act_hom_one]
  have hkey : ((SpacesEtale.toSpaces B S hS X).map ψ).hom.app
        (op (FieldValuedPoint.siteObject B S hS _ p')) p'.value =
      ((SpacesEtale.toSpaces B S hS X).map (act g⁻¹).asIso.hom).hom.app
        (op (FieldValuedPoint.siteObject B S hS _ p'))
        (((SpacesEtale.toSpaces B S hS X).map φ).hom.app
          (op (FieldValuedPoint.siteObject B S hS _ p')) p'.value) := by
    refine (toSpaces_map_app_comp_apply _ _ hcancel _ _).symm.trans ?_
    rw [hnat φ]
    exact congrArg _ ((congrArg _ (hnat ψ)).trans hg)
  refine ⟨g⁻¹, pointsMap B S hS _ ((SpacesEtale.toSpaces B S hS X).map ψ).hom
    (FieldValuedPoint.class B S hS _ p'), ?_⟩
  refine (congrArg (pointsMap B S hS _
      ((SpacesEtale.toSpaces B S hS X).map (translationPair act φ ψ g⁻¹)).hom)
    (FieldValuedPoint.class_eq_class_of_dominates B S hS p' p ⟨f, hval⟩).symm).trans ?_
  refine (FieldValuedPoint.class_map_eq_of_app_eq B S hS
      ((SpacesEtale.toSpaces B S hS X).map (translationPair act φ ψ g⁻¹)).hom
      (((SpacesEtale.toSpaces B S hS X).map ψ).hom ≫
        ((SpacesEtale.toSpaces B S hS X).map (SpacesEtale.diagTwo B S hS X Y)).hom)
      p' ?_).trans
    (congrFun (pointsMap_comp B S hS _ ((SpacesEtale.toSpaces B S hS X).map ψ).hom
      ((SpacesEtale.toSpaces B S hS X).map (SpacesEtale.diagTwo B S hS X Y)).hom)
      (FieldValuedPoint.class B S hS _ p'))
  refine SpacesEtale.prodTwo_section_ext B S hS X Y ?_ ?_
  · exact (toSpaces_map_app_comp_apply _ _ (translationPair_comp_fst act φ ψ g⁻¹) _ _).trans
      (toSpaces_map_app_comp_apply _ _ (SpacesEtale.diagTwo_comp_fst B S hS X Y) _ _).symm
  · refine (toSpaces_map_app_comp_apply _ _ (translationPair_comp_snd act φ ψ g⁻¹) _ _).trans ?_
    exact ((toSpaces_map_app_comp_apply _ _ rfl _ _).symm.trans hkey.symm).trans
      (toSpaces_map_app_comp_apply _ _ (SpacesEtale.diagTwo_comp_snd B S hS X Y) _ _).symm

/-- **The fppf-to-étale refinement.** Under the same hypothesis, two morphisms `φ ψ : V ⟶ Y`
of the spaces-étale site of `X` become translates of each other on a covering of `V`: the open
equalizer loci of `ψ` with the translates of `φ` cover `V` on points, and a jointly
point-surjective family is a covering family of the spaces-étale site.

This is what upgrades the fppf-local statement of Tag 071S to the étale-local statement that
`CategoryTheory.IsOrbitQuotient` asks for. -/
theorem translationSieve_mem_of_orbitSieve (act : G →* Aut Y)
    (horb : ∀ {T : (BigFppfOver B S hS)ᵒᵖ}
      (ξ η : (SpacesEtale.underlying B S hS X Y).1.obj T),
      Y.1.hom.hom.app T ξ = Y.1.hom.hom.app T η →
      ∃ R : Sieve T.unop, R ∈ BigFppfOver.topology B S hS T.unop ∧
        ∀ ⦃b : BigFppfOver B S hS⦄ (f : b ⟶ T.unop), R.arrows f →
          ∃ g : G, ((SpacesEtale.toSpaces B S hS X).map (act g).asIso.hom).hom.app (op b)
              ((SpacesEtale.underlying B S hS X Y).1.map f.op η) =
            (SpacesEtale.underlying B S hS X Y).1.map f.op ξ)
    {V : SpacesEtale B S hS X} (φ ψ : V ⟶ Y) :
    translationSieve act φ ψ ∈ SpacesEtale.topology B S hS X V := by
  classical
  rw [SpacesEtale.mem_topology_iff_sievePointwiseCover]
  intro x
  obtain ⟨g, w, hw⟩ := exists_translation_point act horb φ ψ x
  refine ⟨translationLocus act φ ψ g, pullback.fst _ _,
    translationLocus_fst_mem_translationSieve act φ ψ g, ?_⟩
  exact exists_point_pullback_fst _ _ x w hw

end Refinement

/-! ### The quotient of a free action, read on its own spaces-étale site -/

section Quotient

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {G : Type u} [Group G]
    {W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} [∀ T, MulAction G (W.obj T)]
    [HasSheafify (BigFppfOver.topology B S hS) (Type u)]
    (hnat : IsNaturalAction B S hS G W) (hW : IsAlgebraicSpace B S hS W)
    (hfree : IsFreeOnNonemptyPoints B S hS G W)

/-- **Tag 071S.** The quotient `U = W/G` of an algebraic space by a free action of an abstract
group, as an algebraic space over `S`. -/
def orbitQuotientSpace : AlgebraicSpaces B S hS :=
  ⟨(orbitQuotientSheaf B S hS G W hnat).obj,
    isAlgebraicSpace_orbitQuotientSheaf_of_isFreeOnNonemptyPoints hnat hW hfree⟩

/-- The quotient morphism `W ⟶ W/G`, as a morphism of algebraic spaces over `S`. -/
def toOrbitQuotientSpace :
    (⟨W, hW⟩ : AlgebraicSpaces B S hS) ⟶ orbitQuotientSpace hnat hW hfree :=
  ObjectProperty.homMk (toOrbitQuotient B S hS G W hnat)

/-- **The quotient morphism of a free action is invariant.** -/
theorem actionHom_comp_toOrbitQuotientSpace (g : G) :
    actionHom B S hS G W hnat g ≫ (toOrbitQuotientSpace hnat hW hfree).hom =
      (toOrbitQuotientSpace hnat hW hfree).hom := by
  refine NatTrans.ext (funext fun T => ?_)
  exact ConcreteCategory.hom_ext _ _ fun x => toOrbitQuotient_smul B S hS G W hnat g x

/-- **`W` as an object of the spaces-étale site of its own quotient `W/G`**: the quotient
morphism of a free action is étale. -/
def orbitQuotientEtaleSource : SpacesEtale B S hS (orbitQuotientSpace hnat hW hfree) :=
  etaleObject B S hS (toOrbitQuotientSpace hnat hW hfree)
    (isEtale_toOrbitQuotient hnat hW hfree)

/-- The endomorphism of `W`, as an object of the spaces-étale site of `W/G`, given by the
action of a group element. -/
def orbitQuotientActionEtale (g : G) :
    orbitQuotientEtaleSource hnat hW hfree ⟶ orbitQuotientEtaleSource hnat hW hfree :=
  actionEtale (isEtale_toOrbitQuotient hnat hW hfree)
    (actionHom_comp_toOrbitQuotientSpace hnat hW hfree) g

/-- The presheaf morphism underlying the action of a group element on `W`, read in the
spaces-étale site of `W/G`, is the action on the points of `W`. -/
@[simp]
theorem toSpaces_map_orbitQuotientActionEtale (g : G) :
    ((SpacesEtale.toSpaces B S hS (orbitQuotientSpace hnat hW hfree)).map
      (orbitQuotientActionEtale hnat hW hfree g)).hom = actionHom B S hS G W hnat g :=
  rfl

/-- Acting by `g` and then by `g'` is acting by `g' * g`. -/
theorem orbitQuotientActionEtale_comp (g g' : G) :
    orbitQuotientActionEtale hnat hW hfree g ≫ orbitQuotientActionEtale hnat hW hfree g' =
      orbitQuotientActionEtale hnat hW hfree (g' * g) := by
  refine ObjectProperty.hom_ext _ (Over.OverMorphism.ext (ObjectProperty.hom_ext _ ?_))
  show actionHom B S hS G W hnat g ≫ actionHom B S hS G W hnat g' =
    actionHom B S hS G W hnat (g' * g)
  refine NatTrans.ext (funext fun T => ?_)
  exact ConcreteCategory.hom_ext _ _ fun x => (mul_smul g' g x).symm

/-- The unit acts as the identity. -/
@[simp]
theorem orbitQuotientActionEtale_one :
    orbitQuotientActionEtale hnat hW hfree (1 : G) = 𝟙 _ := by
  refine ObjectProperty.hom_ext _ (Over.OverMorphism.ext (ObjectProperty.hom_ext _ ?_))
  show actionHom B S hS G W hnat (1 : G) = 𝟙 W
  refine NatTrans.ext (funext fun T => ?_)
  exact ConcreteCategory.hom_ext _ _ fun x => one_smul G x

/-- **The action of `G` by automorphisms of `W` in the spaces-étale site of `W/G`.** -/
def orbitQuotientAut : G →* Aut (orbitQuotientEtaleSource hnat hW hfree) where
  toFun g := Aut.of
    { hom := orbitQuotientActionEtale hnat hW hfree g
      inv := orbitQuotientActionEtale hnat hW hfree g⁻¹
      hom_inv_id := by
        rw [orbitQuotientActionEtale_comp, inv_mul_cancel, orbitQuotientActionEtale_one]
      inv_hom_id := by
        rw [orbitQuotientActionEtale_comp, mul_inv_cancel, orbitQuotientActionEtale_one] }
  map_one' := Aut.ext (Iso.ext (orbitQuotientActionEtale_one hnat hW hfree))
  map_mul' g g' := Aut.ext (Iso.ext (orbitQuotientActionEtale_comp hnat hW hfree g' g).symm)

/-- The automorphism `orbitQuotientAut hnat hW hfree g` has underlying morphism
`orbitQuotientActionEtale hnat hW hfree g`. -/
@[simp]
theorem orbitQuotientAut_hom (g : G) :
    (orbitQuotientAut hnat hW hfree g).asIso.hom = orbitQuotientActionEtale hnat hW hfree g :=
  rfl

/-! ### The hypotheses of the general refinement, for the quotient of a free action -/

include hfree in
omit [HasSheafify (BigFppfOver.topology B S hS) (Type u)] in
/-- **A section of `W` fixed by a group element forces that element to be trivial**, over a
test object whose underlying scheme is nonempty. This is freeness on the points over such a
test object, read on a section. -/
theorem eq_one_of_smul_eq {T : (BigFppfOver B S hS)ᵒᵖ} (ξ : W.obj T)
    (hT : Nonempty ((BigFppfOver.toScheme B S hS).obj T.unop)) {g : G} (h : g • ξ = ξ) :
    g = 1 :=
  have := hfree T hT
  IsCancelSMul.right_cancel g 1 ξ (h.trans (one_smul G ξ).symm)

/-- **The action of `G` on `W` in the spaces-étale site of `W/G` is free** in the sense of
`CategoryTheory.ActsFreelyOnObject`: a morphism `φ : V ⟶ W` of the site fixed by `g` forces
`g = 1`, unless the empty sieve covers `V`. -/
theorem actsFreelyOnObject_orbitQuotientAut :
    ActsFreelyOnObject (orbitQuotientAut hnat hW hfree)
      (SpacesEtale.topology B S hS (orbitQuotientSpace hnat hW hfree)) :=
  actsFreelyOnObject_of_eq_one_of_nonempty (orbitQuotientAut hnat hW hfree)
    fun ξ hT _ h => eq_one_of_smul_eq hfree ξ hT h

/-- **The morphisms to `W` cover every object of the spaces-étale site of `W/G`**, the
quotient morphism of a free action being surjective on points. -/
theorem splittingSieve_mem_spacesEtale
    (V : SpacesEtale B S hS (orbitQuotientSpace hnat hW hfree)) :
    splittingSieve (orbitQuotientEtaleSource hnat hW hfree) V ∈
      SpacesEtale.topology B S hS (orbitQuotientSpace hnat hW hfree) V :=
  SpacesEtale.splittingSieve_mem_of_isSurjective
    (isSurjective_toOrbitQuotient hnat hW hfree) V

/-- **The fppf-to-étale refinement for the quotient of a free action.** Two morphisms
`φ ψ : V ⟶ W` of the spaces-étale site of `W/G` become translates of each other on a covering
of `V` by the open equalizer loci. The fppf input is
`AlgebraicGeometry.Space.orbitSieve_mem`, the fact that two sections of `W` with the same
image in `W/G` are translates of each other along a covering sieve of the big fppf site. -/
theorem translationSieve_mem_spacesEtale
    {V : SpacesEtale B S hS (orbitQuotientSpace hnat hW hfree)}
    (φ ψ : V ⟶ orbitQuotientEtaleSource hnat hW hfree) :
    translationSieve (orbitQuotientAut hnat hW hfree) φ ψ ∈
      SpacesEtale.topology B S hS (orbitQuotientSpace hnat hW hfree) V :=
  translationSieve_mem_of_orbitSieve (orbitQuotientAut hnat hW hfree)
    (fun ξ η hξη => ⟨orbitSieve B S hS G W hnat ξ η,
      orbitSieve_mem B S hS G W hnat ξ η hξη, fun _ _ hf => hf⟩) φ ψ

/-! ### The torsor and the orbit quotient -/

/-- **`W` is a `G`-torsor over the final object of the spaces-étale site of `W/G`.** -/
theorem isTorsorObject_orbitQuotientAut :
    IsTorsorObject (orbitQuotientAut hnat hW hfree)
      (SpacesEtale.topology B S hS (orbitQuotientSpace hnat hW hfree)) where
  splittingSieve_mem := splittingSieve_mem_spacesEtale hnat hW hfree
  translationSieve_mem φ ψ := translationSieve_mem_spacesEtale hnat hW hfree φ ψ
  eq_one_of_comp_act φ g h := actsFreelyOnObject_orbitQuotientAut hnat hW hfree φ g h

/-- **The quotient morphism exhibits the final object of the spaces-étale site of `W/G` as the
quotient `W/G`**, in the sense of `CategoryTheory.IsOrbitQuotient`.

This is the statement that the étale-site projection `W ⟶ W/G` is the orbit quotient *in the
spaces-étale site of the algebraic space `W/G`*, so that the torsor theory of
`CategoryTheory.IsOrbitQuotient` and the character twist of Stacks 0727 may be instantiated
there. -/
theorem isOrbitQuotient_orbitQuotientAut :
    IsOrbitQuotient (orbitQuotientAut hnat hW hfree)
      (SpacesEtale.topology B S hS (orbitQuotientSpace hnat hW hfree))
      ((SpacesEtale.final_isTerminal B S hS (orbitQuotientSpace hnat hW hfree)).from
        (orbitQuotientEtaleSource hnat hW hfree)) :=
  (isTorsorObject_orbitQuotientAut hnat hW hfree).isOrbitQuotient
    (SpacesEtale.final_isTerminal B S hS (orbitQuotientSpace hnat hW hfree))

end Quotient

end AlgebraicGeometry.Space

end
