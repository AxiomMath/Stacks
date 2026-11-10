module

public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateFunctors.DomainRestriction
public import StacksFrontier.AlgebraicGeometry.Duality.AdequateSheafOfModules
public import StacksFrontier.AlgebraicGeometry.Morphisms.Syntomic.OpenImmersion
public import StacksFrontier.AlgebraicGeometry.Topologies.BigSites.StandardCoveringSieves
public import StacksFrontier.AlgebraicGeometry.Topologies.ExtendingFunctorsStandardAffineStage

/-!
# Adequacy of a sheaf of modules is detected on every affine over the base

Adequacy of a sheaf of modules `F` on a big `τ`-site over `S`, namely
`Stacks.Adequate.IsAdequate`, asks only for *some* `τ`-covering of `S` by affine schemes
`Spec Aᵢ` belonging to the site on which the affine-section functors `F_{F, Aᵢ}` are adequate
module-valued functors. [Stacks, Tag 06VI] upgrades this to *every* affine scheme `Spec A` over
`S`, and this module states that upgrade together with the converse implication.

## Main definitions

The three steps of the source's proof of Tag 06VI are named separately. The first two are
proved here, by `Stacks.Adequate.standardAffineRefinement` and
`Stacks.Adequate.affineSectionRestriction`; the third is proved by
`Stacks.Adequate.standardAffineDescent`, in
`StacksFrontier/AlgebraicGeometry/Adequate/AdequateModules/StandardAffineProductAdequacy.lean`.

* `Stacks.Adequate.StandardAffineRefinement` — a `τ`-covering of `S` by affines of the site can
  be refined, over any affine `Spec A` of the site over `S`, by a finite standard affine
  `τ`-covering of `Spec A` whose members factor through members of the given covering.
* `Stacks.Adequate.AffineSectionRestriction` — identifies `F_{F, A'}` with the restriction of
  `F_{F, A}` to `A'`-algebras along a ring map `A → A'`. It is a statement about the functors
  only, with no reference to adequacy, and it is what carries [Stacks, Tag 06V9] to the
  geometric side; `Stacks.Adequate.AffineBaseChangeAdequacy` is the resulting stability of
  adequacy, derived from it.
* `Stacks.Adequate.StandardAffineDescent` — adequacy of the affine-section functors descends
  along a finite standard affine `τ`-covering of an affine of the site over `S`.

## Main results

* `Stacks.Adequate.isAdequate_of_forall_affineSectionFunctor` — the converse of Tag 06VI: if the
  affine-section functor is adequate at every affine scheme of the site over `S`, then the sheaf
  of modules is adequate. This is proved outright, by evaluating the hypothesis on the affine
  open cover of `S`.
* `Stacks.Adequate.BigSite.size_lt_of_isStandardCovering` — a member of a standard `τ`-covering
  of an affine scheme of a chosen big site is again a scheme of that site.
* `Stacks.Adequate.standardAffineRefinement` — `Stacks.Adequate.StandardAffineRefinement` holds
  for every chosen big site.
* `Stacks.Adequate.affineSpecOver_obj_siteRestrict` — the object half of
  `Stacks.Adequate.AffineSectionRestriction`: the two index functors of that statement agree on
  objects. `Stacks.Adequate.affineSpecOver_obj_left_obj` and
  `Stacks.Adequate.affineSpecOver_obj_left_obj_siteRestrict` reduce each side to the common
  normal form that makes it cheap.
* `Stacks.Adequate.affineSpecOver_eq_siteRestrict` — the two index functors of
  `Stacks.Adequate.AffineSectionRestriction` are **equal**, not merely isomorphic.
* `Stacks.Adequate.affineSectionRestriction` — `Stacks.Adequate.AffineSectionRestriction` holds
  for every chosen big site and every sheaf of modules on it.
* `Stacks.Adequate.affineBaseChangeAdequacy` — adequacy of the affine-section functors is
  stable along a ring map between affines of the site over `S`. This is
  [Stacks, Tag 06V9], `AdequateFunctor.IsAdequate.restrictBaseOn`, transported along
  `Stacks.Adequate.affineSectionRestriction`;
  `Stacks.Adequate.affineBaseChangeAdequacy_of_affineSectionRestriction` is the transport
  itself, which isolates the appeal to Tag 06V9 from the identification it is transported
  along.

[Stacks, Tag 06VI] itself is `Stacks.Adequate.isAdequate_affineSectionFunctor`, in
`StacksFrontier/AlgebraicGeometry/Adequate/AdequateModules/AffineLocalUnconditional.lean`. It is
stated there rather than here because the proof of `Stacks.Adequate.StandardAffineDescent`,
the third step of its proof, is built on this module and so lies above it.

## Implementation notes

`Stacks.Adequate.coveringMorphismProperty_of_isOpenImmersion` records that an open immersion has
the covering morphism property of each of the five topologies, which is what makes an affine open
cover of `S` a `τ`-covering for every `τ`.

The affine scheme `Spec A` is required to belong to the chosen big site. This is implicit in the
source's phrase "affine scheme `Spec(A)` over `S`" on `(Sch/S)_τ`; the site's cardinal cutoff
makes the membership explicit. The topology `τ` is a parameter throughout, exactly as in the
source, and is never specialized.

`Stacks.Adequate.isAdequate_of_forall_affineSectionFunctor` is stated for an arbitrary value
universe. From `Stacks.Adequate.AffineSectionRestriction` onwards the value universe is
`max u m`, because [Stacks, Tag 06V9] raises the values of a functor to include the universe of
the source ring when it restricts the base ring, and `max u (max u m) = max u m` absorbs that.

The three steps of the source's proof of Tag 06VI are:

* `StandardAffineRefinement` is the opening sentence, "we can find a standard affine
  `τ`-covering `{Spec(A'ⱼ) → Spec(A)}` such that `Spec(A'ⱼ) → Spec(A) → S` factors through
  `Spec(A_{i(j)})`"; it is a statement about schemes alone, with no reference to `F`. It is
  **proved** by `Stacks.Adequate.standardAffineRefinement`: the given covering of `S` is base
  changed along `Spec A ⟶ S`, which stays a `τ`-covering because
  `AlgebraicGeometry.coveringMorphismProperty` is stable under base change, and the result is
  refined by [Stacks, Tag 03XA],
  `AlgebraicGeometry.exists_standardCovering_refinement`. The members of the refinement lie in
  the site by `Stacks.Adequate.BigSite.size_lt_of_isStandardCovering`, and each of them maps
  to the corresponding member of the base-changed family, hence over `S` to a member of the
  given covering; the maps between affines are `Spec` of ring maps by `Spec.map_preimage`.
* `AffineSectionRestriction` is the clause "`F_{F, A'ⱼ}` is the restriction of
  `F_{F, A_{i(j)}}` to the category of `A'ⱼ`-algebras" in the next sentence. Its companion
  clause, "hence `F_{F, A'ⱼ}` is adequate by Lemma 06V9", is *not* assumed: Tag 06V9 is
  `AdequateFunctor.IsAdequate.restrictBaseOn`, and
  `affineBaseChangeAdequacy_of_affineSectionRestriction` is that lemma applied here. It is
  **proved**, by `Stacks.Adequate.affineSectionRestriction`. What is not already available is
  only the identification of the two functors, which is a comparison of pushforwards
  along two index functors. The two functors agree on the underlying scheme of each object of
  the site, but their structure morphisms to `S` differ by `AlgebraicGeometry.Spec.map_comp`,
  so the two objects of the site are not equal syntactically.

  They are nevertheless equal, and so are the two index functors: see
  `Stacks.Adequate.affineSpecOver_obj_siteRestrict` and
  `Stacks.Adequate.affineSpecOver_eq_siteRestrict`. Since the scalar comparison an
  affine-section functor carries does not mention the structure morphism, the two scalar
  comparisons are then equal as well, and the identification of the module-valued functors is
  `CategoryTheory.PresheafOfModules.pushforwardComp` transported along those two equalities,
  with the `ULift` of the values absorbed by `AdequateFunctor.presheafOfModulesUliftIso`. No
  natural isomorphism and no `eqToHom` survives into the statement.

  What makes this delicate is only the cost of the defeq. A `rfl` pitting the two sides against
  each other exhausts the kernel at about two
  and a half minutes — the reduction would run through `AlgebraicGeometry.algSpec`,
  `CategoryTheory.Over.opEquivOpUnder` and `AlgebraicGeometry.commAlgCatEquivUnder` — but that
  is an artifact of the comparison order, not a real cost: each side *separately* reduces to
  the common normal form `Spec (CommRingCat.of X)` by `rfl` at once, which is
  `Stacks.Adequate.affineSpecOver_obj_left_obj` and
  `Stacks.Adequate.affineSpecOver_obj_left_obj_siteRestrict`. So every comparison here goes
  through a normal form, one side at a time, and the two sides are never compared against each
  other: on objects by `Stacks.Adequate.affineSpecOver_obj_siteRestrict`, on morphisms by
  `Stacks.Adequate.affineSpecOver_map_left_heq_siteRestrict`, and on scalars by
  `Stacks.Adequate.affineRingMap_app_heq_siteRestrict`.

  That discipline is not enough by itself: each *step* must also be stated over abstract
  functors and instantiated exactly once, because anything that lets the elaborator recover an
  argument by unifying against a concrete subterm reintroduces the comparison. Three such steps
  cost the full two and a half minutes on their own, each as a kernel
  deterministic timeout that `set_option` is not permitted to relieve, and each is replaced by
  a generic lemma above: `simp only [Over.comp_left, Over.eqToHom_left]`, whose motive is
  type-correct only up to the forbidden defeq, by
  `Stacks.Adequate.over_comp_left_eqToHom`; recovery of an implicit morphism argument through
  the projection pattern `?s.left`, by passing it explicitly in
  `Stacks.Adequate.functor_eq_of_left_heq`; and the defeq between `(F ⋙ G).op ⋙ R` and
  `F.op ⋙ G.op ⋙ R`, which times out in the elaborator rather than the kernel, by
  `Stacks.Adequate.op_comp_comp_eq`. With all three replaced, the chain checks in under a
  second, and `CategoryTheory.Functor.ext` — whose `h_map` auto-parameter does fail, but which
  is perfectly usable with `h_map` supplied — is what delivers the equality of functors.
* `StandardAffineDescent` is the remainder, the passage through the product
  `A' = A'₁ × … × A'ₘ` of Lemma 06VB and the descent of Lemma 06VH. Both tags are available, as
  `AdequateFunctor.adequateFunctorProductEquivalence` and
  `AdequateFunctor.isAdequate_of_descent`, but both are stated for module-valued functors on
  *all* algebras over the base ring, while an affine-section functor is defined only on the
  algebras of the site.

  It has four inputs. The first three are in
  `StacksFrontier/AlgebraicGeometry/Adequate/AdequateModules/StandardAffineDescentReduction.lean`
  and the modules it rests on, and
  `Stacks.Adequate.standardAffineDescent_of_productAdequacy` reduces `StandardAffineDescent` to
  the fourth alone, `Stacks.Adequate.StandardAffineProductAdequacy`, which
  `Stacks.Adequate.standardAffineProductAdequacy` then proves:

  - Lemma 06VH on the site's domain of algebras is
    `AdequateFunctor.isAdequate_of_descent_on`, and
    `Stacks.Adequate.isAdequate_affineSectionFunctor_of_cechExactOn` is its geometric form.
  - Lemma 06VA, which the Čech terms of that descent need on the same domain, is
    `AdequateFunctor.isAdequate_pushforwardOn`.
  - The Čech-exactness hypothesis `hexact` is
    `Stacks.Adequate.cechExactOn_affineSectionFunctor_pi`, in
    `StacksFrontier/AlgebraicGeometry/Adequate/AdequateModules/CechExactStandardCovering.lean`,
    which deduces it from the `τ`-sheaf condition `F` carries by definition along the single
    covering `Spec A' ⟶ Spec A`, with no hypothesis on `F` and no appeal to [Stacks, Tag 03O1].
    It is stated as `AdequateFunctor.CechExactOn` on the site domain;
    `AdequateFunctor.cechExact_of_cechExactOn` is the corresponding passage on the full domain
    of all `A`-algebras.
  - The fourth is adequacy of `F_{F, A'}` for `A' = A'₁ × … × A'ₘ`, which is
    `Stacks.Adequate.standardAffineProductAdequacy`, in
    `StacksFrontier/AlgebraicGeometry/Adequate/AdequateModules/StandardAffineProductAdequacy.lean`.
    Lemma 06VB is *not* what that needs on this domain:
    `AdequateFunctor.isAdequate_pushforwardOn` already makes `C ↦ F_{F, A'ⱼ}(C ⊗_{A'} A'ⱼ)`
    adequate on the `A'`-algebras of the site, and
    `Stacks.Adequate.affineAdequateFiniteProducts` makes a finite product of those adequate, so
    the whole of the remainder is the identification of `F_{F, A'}` with that product — the
    Zariski sheaf condition for the decomposition `Spec A' = ⊔ⱼ Spec A'ⱼ`.

## References

* [Stacks Project, Tag 06VI](https://stacks.math.columbia.edu/tag/06VI)
* [Stacks Project, Tag 06VG](https://stacks.math.columbia.edu/tag/06VG)
* [Stacks Project, Tag 06V9](https://stacks.math.columbia.edu/tag/06V9)
* [Stacks Project, Tag 03X9](https://stacks.math.columbia.edu/tag/03X9)
* [Stacks Project, Tag 03XA](https://stacks.math.columbia.edu/tag/03XA)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u v m

namespace Stacks.Adequate

/-- An open immersion has the covering morphism property of every one of the five topologies
admitting standard affine coverings. -/
public theorem coveringMorphismProperty_of_isOpenImmersion
    (τ : CoveringTopology) {X Y : Scheme.{u}} (g : X ⟶ Y) [IsOpenImmersion g] :
    coveringMorphismProperty τ g := by
  cases τ with
  | zariski => infer_instance
  | etale => infer_instance
  | smooth => infer_instance
  | fppf => exact ⟨inferInstance, inferInstance⟩
  | syntomic => exact AlgebraicGeometry.syntomic_of_isOpenImmersion g

/-- The converse of [Stacks, Tag 06VI]: a sheaf of modules whose affine-section functor is
adequate at *every* affine scheme of the site over `S` is adequate, because the affine open
cover of `S` is a `τ`-covering by affine schemes of the site. -/
public theorem isAdequate_of_forall_affineSectionFunctor
    {τ : CoveringTopology} {S : Scheme.{u}} (B : BigSite τ S)
    (F : SheafOfModules.{m} B.structureSheaf)
    (hF : ∀ (A : CommRingCat.{u}) (f : Spec A ⟶ S),
      schemeSizeBelow B.cutoff (Spec A) →
        AdequateFunctor.IsAdequate
          (AdequateFunctor.siteAlgebraInclusion A (schemeSizeBelow B.cutoff))
          (affineSectionFunctor B F A f)) :
    IsAdequate B F := by
  refine ⟨ULift.{u + 1} S.affineOpenCover.I₀,
    fun i => S.affineOpenCover.X i.down,
    fun i => S.affineOpenCover.f i.down,
    fun i => coveringMorphismProperty_of_isOpenImmersion τ _, ?_, ?_⟩
  · apply Set.eq_univ_of_forall
    intro x
    obtain ⟨i, y, hy⟩ := S.affineOpenCover.openCover.exists_eq x
    exact Set.mem_iUnion.mpr ⟨⟨i⟩, y, hy⟩
  · intro i
    have hi := Scheme.size_lt_of_isOpenImmersion (S.affineOpenCover.f i.down) B.base_mem
    exact ⟨hi, hF _ _ hi⟩

/-- For every ring map `φ : A ⟶ A'` between affine schemes of the site over `S`, the
affine-section functor of `F` at `A'` is the restriction to `A'`-algebras, in the sense of
`AdequateFunctor.restrictFunctorOn`, of its affine-section functor at `A`. This is the sentence
"`F_{F, A'}` is the restriction of `F_{F, A}` to the category of `A'`-algebras" of the source's
proof of [Stacks, Tag 06VI], and is a statement about the two functors only. -/
public abbrev AffineSectionRestriction
    {τ : CoveringTopology} {S : Scheme.{u}} (B : BigSite τ S)
    (F : SheafOfModules.{max u m} B.structureSheaf) : Prop :=
  ∀ (A A' : CommRingCat.{u}) (φ : A ⟶ A') (f : Spec A ⟶ S),
    Nonempty (affineSectionFunctor B F A' (Spec.map φ ≫ f) ≅
      (AdequateFunctor.restrictFunctorOn.{max u m, u} φ.hom (schemeSizeBelow B.cutoff)).obj
        ((AdequateFunctor.presheafOfModulesUliftFunctor.{u, max u m}
          (AdequateFunctor.algebraRingDiagramOn
            (AdequateFunctor.siteAlgebraInclusion A (schemeSizeBelow B.cutoff)))).obj
          (affineSectionFunctor B F A f)))

/-! ### The index comparison underlying `Stacks.Adequate.AffineSectionRestriction`

The two index functors of `Stacks.Adequate.AffineSectionRestriction` send an `A'`-algebra of
the site to the spectrum of one and the same ring; they differ only in the structure morphism
to `S`, by `AlgebraicGeometry.Spec.map_comp` and associativity. The object equality is recorded
here, together with the reduction of each side to a common normal form that makes it cheap. -/

/-- The scheme underlying the value of `Stacks.Adequate.affineSpecOver` at an algebra of the
site is the spectrum of that algebra, independently of the structure morphism. -/
public theorem affineSpecOver_obj_left_obj {τ : CoveringTopology} {S : Scheme.{u}}
    (B : BigSite τ S) (A : CommRingCat.{u}) (f : Spec A ⟶ S)
    (X : (AdequateFunctor.AlgebrasInSite A (schemeSizeBelow B.cutoff))ᵒᵖ) :
    ((affineSpecOver B A f).obj X).left.obj = Spec (CommRingCat.of X.unop.obj) := rfl

/-- Reading an `A'`-algebra of the site as an `A`-algebra along `φ` does not change the scheme
underlying the value of `Stacks.Adequate.affineSpecOver`, because
`AdequateFunctor.restrictAlgebras` leaves the underlying ring alone. -/
public theorem affineSpecOver_obj_left_obj_siteRestrict {τ : CoveringTopology} {S : Scheme.{u}}
    (B : BigSite τ S) (A A' : CommRingCat.{u}) (φ : A ⟶ A') (f : Spec A ⟶ S)
    (X : (AdequateFunctor.AlgebrasInSite A' (schemeSizeBelow B.cutoff))ᵒᵖ) :
    ((affineSpecOver B A f).obj
        ((AdequateFunctor.siteRestrictAlgebras.{u} φ.hom
          (schemeSizeBelow B.cutoff)).op.obj X)).left.obj =
      Spec (CommRingCat.of X.unop.obj) := rfl

/-- **The object half of `Stacks.Adequate.AffineSectionRestriction`.** The value at an
`A'`-algebra of the site of the index functor over `A'` agrees with the value over `A` of that
algebra read along `φ : A ⟶ A'`: both are the spectrum of the same ring, and the two structure
morphisms to `S` agree because
`Spec.map (algebraMap A X) = Spec.map (algebraMap A' X) ≫ Spec.map φ`.

The proof is assembled structurally, from `AlgebraicGeometry.algSpec_obj_hom` and
`AlgebraicGeometry.Spec.map_comp`; it must not be proved by `rfl`, which pits the two sides
against each other and exhausts the kernel. Each side separately reduces cheaply to the common
normal form of `Stacks.Adequate.affineSpecOver_obj_left_obj`. -/
public theorem affineSpecOver_obj_siteRestrict {τ : CoveringTopology} {S : Scheme.{u}}
    (B : BigSite τ S) (A A' : CommRingCat.{u}) (φ : A ⟶ A') (f : Spec A ⟶ S)
    (X : (AdequateFunctor.AlgebrasInSite A' (schemeSizeBelow B.cutoff))ᵒᵖ) :
    (affineSpecOver B A' (Spec.map φ ≫ f)).obj X =
      (affineSpecOver B A f).obj
        ((AdequateFunctor.siteRestrictAlgebras.{u} φ.hom
          (schemeSizeBelow B.cutoff)).op.obj X) := by
  change Over.mk _ = Over.mk _
  congr 1
  apply ObjectProperty.hom_ext (schemeSizeBelow B.cutoff)
  let : Algebra (A : Type u) (X.unop.obj : Type u) := Algebra.compHom _ φ.hom
  change Spec.map (CommRingCat.ofHom (algebraMap (A' : Type u) (X.unop.obj : Type u))) ≫
      (Spec.map φ ≫ f) =
    Spec.map (CommRingCat.ofHom (algebraMap (A : Type u) (X.unop.obj : Type u))) ≫ f
  have hring : CommRingCat.ofHom (algebraMap (A : Type u) (X.unop.obj : Type u)) =
      φ ≫ CommRingCat.ofHom (algebraMap (A' : Type u) (X.unop.obj : Type u)) := rfl
  rw [hring, Spec.map_comp, Category.assoc]

/-! ### `Stacks.Adequate.AffineSectionRestriction`, proved

The two index functors are not merely isomorphic but **equal**, and the scalar comparisons they
carry are then equal too, so the identification of the two module-valued functors is Mathlib's
`CategoryTheory.PresheafOfModules.pushforwardComp` and nothing more.

Every step is stated over *abstract* functors and instantiated exactly once. That is not a
matter of taste: the two concrete index functors agree on objects only up to
`AlgebraicGeometry.Spec.map_comp`, so any step that lets the elaborator recover an argument by
unifying against a concrete subterm — an implicit morphism found through a projection, a
`simp`-generated motive, a defeq between `(F ⋙ G).op ⋙ R` and `F.op ⋙ G.op ⋙ R` — pits the two
sides against each other and exhausts the kernel. Each of the generic lemmas below replaces one
such step, and the whole chain then checks in under a second. -/

/-- An equation between morphisms with `eqToHom` at both ends, from a heterogeneous equality of
the two morphisms. Stated over a plain category: this is the shape
`CategoryTheory.Functor.ext` asks for in its `h_map` argument. -/
private lemma eq_of_heq_comp {C : Type*} [Category C] {L R L' R' : C}
    (h : L = R) (h' : R' = L') (s : L ⟶ L') (t : R ⟶ R') (hst : HEq s t) :
    s = eqToHom h ≫ t ≫ eqToHom h' := by
  cases h; cases h'; obtain rfl := eq_of_heq hst; simp

/-- The underlying morphism of a composite with `eqToHom` at both ends in a slice category. -/
private lemma over_comp_left_eqToHom {C : Type*} [Category C] {T : C}
    {O₁ O₂ O₁' O₂' : Over T} (h : O₁ = O₂) (h' : O₂' = O₁') (t : O₂ ⟶ O₂') :
    (eqToHom h ≫ t ≫ eqToHom h').left =
      eqToHom (congrArg Over.left h) ≫ t.left ≫ eqToHom (congrArg Over.left h') := by
  cases h; cases h'; simp

/-- Two functors into a slice category are **equal** as soon as they agree on objects and their
values on morphisms agree as heterogeneous equalities of the underlying morphisms. A morphism of
a slice category is determined by its underlying morphism, so no comparison of the structure
morphisms is required, which is what makes this usable where the objects agree only
definitionally. -/
private lemma functor_eq_of_left_heq {C : Type*} [Category C] {D : Type*} [Category D] {T : D}
    (Φ₁ Φ₂ : C ⥤ Over T) (hobj : ∀ X, Φ₁.obj X = Φ₂.obj X)
    (hmap : ∀ (X Y : C) (m : X ⟶ Y), HEq ((Φ₁.map m).left) ((Φ₂.map m).left)) :
    Φ₁ = Φ₂ :=
  CategoryTheory.Functor.ext hobj fun X Y m =>
    Over.OverMorphism.ext
      ((eq_of_heq_comp (congrArg Over.left (hobj X)) (congrArg Over.left (hobj Y).symm)
          ((Φ₁.map m).left) ((Φ₂.map m).left) (hmap X Y m)).trans
        (over_comp_left_eqToHom (hobj X) (hobj Y).symm (Φ₂.map m)).symm)

/-- Taking opposites and precomposing distributes over a composite of functors. Needed as an
equation, rather than as the isomorphism `CategoryTheory.Functor.opComp`, so that the
instantiation below never asks the elaborator for this defeq. -/
private lemma op_comp_comp_eq {C : Type*} [Category C] {D : Type*} [Category D]
    {E : Type*} [Category E] {Z : Type*} [Category Z]
    (Fc : C ⥤ D) (G : D ⥤ E) (R : Eᵒᵖ ⥤ Z) :
    (Fc ⋙ G).op ⋙ R = Fc.op ⋙ G.op ⋙ R := rfl

/-- Two natural transformations with equal targets are heterogeneously equal as soon as their
components are. -/
private lemma natTrans_heq_of_app {C : Type*} [Category C] {D : Type*} [Category D]
    {Sr G₁ G₂ : C ⥤ D} (h : G₁ = G₂) (α₁ : Sr ⟶ G₁) (α₂ : Sr ⟶ G₂)
    (happ : ∀ X, HEq (α₁.app X) (α₂.app X)) : HEq α₁ α₂ := by
  cases h
  exact heq_of_eq (NatTrans.ext (funext fun X => eq_of_heq (happ X)))

/-- A pushforward of presheaves of modules along an index functor that is *equal* to a
composite, and along a scalar comparison heterogeneously equal to the corresponding composite,
is the composite of the two pushforwards. This is
`CategoryTheory.PresheafOfModules.pushforwardComp` transported along those two equalities. -/
private noncomputable def pushforwardCompIsoOfEq {C : Type*} [Category C]
    {D : Type*} [Category D] {E : Type*} [Category E]
    {T : Eᵒᵖ ⥤ RingCat.{u}} {R : Dᵒᵖ ⥤ RingCat.{u}} {Sr : Cᵒᵖ ⥤ RingCat.{u}}
    {Fc : C ⥤ D} {G : D ⥤ E} {Φ : C ⥤ E} (h : Φ = Fc ⋙ G)
    (ψ : R ⟶ G.op ⋙ T) (χ : Sr ⟶ Fc.op ⋙ R) (α : Sr ⟶ Φ.op ⋙ T)
    (hα : HEq α (χ ≫ Functor.whiskerLeft Fc.op ψ))
    (M : PresheafOfModules.{v} T) :
    (PresheafOfModules.pushforward α).obj M ≅
      (PresheafOfModules.pushforward χ).obj ((PresheafOfModules.pushforward ψ).obj M) := by
  cases h
  obtain rfl := eq_of_heq hα
  exact ((PresheafOfModules.pushforwardComp χ ψ).app M).symm

section Restriction

variable {τ : CoveringTopology} {S : Scheme.{u}} (B : BigSite τ S)
    (A A' : CommRingCat.{u}) (φ : A ⟶ A') (f : Spec A ⟶ S)

/-- The common normal form of the two index functors on morphisms: `Spec` of the ring map
underlying the given morphism of algebras, between the spectra of the two algebras. -/
private noncomputable def nfMap
    {X Y : (AdequateFunctor.AlgebrasInSite A' (schemeSizeBelow B.cutoff))ᵒᵖ} (g : X ⟶ Y) :
    (⟨Spec (CommRingCat.of (X.unop.obj : Type u)), X.unop.property⟩ : SchemeBelow B.cutoff) ⟶
      ⟨Spec (CommRingCat.of (Y.unop.obj : Type u)), Y.unop.property⟩ :=
  ObjectProperty.homMk (Spec.map (CommRingCat.ofHom g.unop.hom.hom.toRingHom))

/-- **The morphism half of `Stacks.Adequate.AffineSectionRestriction`.** The two index functors
send a morphism of `A'`-algebras of the site to `Spec` of one and the same ring map.

The two sides are compared as a heterogeneous equality, and only ever through the common normal
form `Stacks.Adequate.nfMap`: each of the two reductions to it is a `rfl` that unfolds one side
alone, which is cheap for the same reason `Stacks.Adequate.affineSpecOver_obj_left_obj` is. The
two sides are never compared against each other. -/
private theorem affineSpecOver_map_left_heq_siteRestrict
    {X Y : (AdequateFunctor.AlgebrasInSite A' (schemeSizeBelow B.cutoff))ᵒᵖ} (g : X ⟶ Y) :
    HEq (((affineSpecOver B A' (Spec.map φ ≫ f)).map g).left)
      ((((AdequateFunctor.siteRestrictAlgebras.{u} φ.hom (schemeSizeBelow B.cutoff)).op ⋙
        affineSpecOver B A f).map g).left) :=
  HEq.trans (b := nfMap B A' g)
    (heq_of_eq (show (((affineSpecOver B A' (Spec.map φ ≫ f)).map g).left :
      (⟨Spec (CommRingCat.of (X.unop.obj : Type u)), X.unop.property⟩ :
        SchemeBelow B.cutoff) ⟶
          ⟨Spec (CommRingCat.of (Y.unop.obj : Type u)), Y.unop.property⟩) =
      nfMap B A' g from rfl))
    (heq_of_eq (show nfMap B A' g =
      ((((AdequateFunctor.siteRestrictAlgebras.{u} φ.hom (schemeSizeBelow B.cutoff)).op ⋙
        affineSpecOver B A f).map g).left :
      (⟨Spec (CommRingCat.of (X.unop.obj : Type u)), X.unop.property⟩ :
        SchemeBelow B.cutoff) ⟶
          ⟨Spec (CommRingCat.of (Y.unop.obj : Type u)), Y.unop.property⟩) from rfl))

/-- **The two index functors of `Stacks.Adequate.AffineSectionRestriction` are equal.** Reading
an `A'`-algebra of the site as an `A`-algebra along `φ` and then taking its spectrum over `S` is
the same functor as taking its spectrum over `S` directly along `Spec φ ≫ f`, and not merely an
isomorphic one.

The object halves agree by `Stacks.Adequate.affineSpecOver_obj_siteRestrict` and the morphism
halves by `Stacks.Adequate.affineSpecOver_map_left_heq_siteRestrict`; the passage from those two
to the equality of functors is `Stacks.Adequate.functor_eq_of_left_heq`. -/
public theorem affineSpecOver_eq_siteRestrict :
    affineSpecOver B A' (Spec.map φ ≫ f) =
      (AdequateFunctor.siteRestrictAlgebras.{u} φ.hom (schemeSizeBelow B.cutoff)).op ⋙
        affineSpecOver B A f :=
  functor_eq_of_left_heq _ _ (fun X => affineSpecOver_obj_siteRestrict B A A' φ f X)
    (fun _ _ g => affineSpecOver_map_left_heq_siteRestrict B A A' φ f g)

/-- The common normal form of the two scalar comparisons: the inverse of the canonical
identification of an algebra with the global functions on its spectrum. -/
private noncomputable def nfApp
    (X : ((AdequateFunctor.AlgebrasInSite A' (schemeSizeBelow B.cutoff))ᵒᵖ)ᵒᵖ) :
    (AdequateFunctor.algebraRingDiagramOn
      (AdequateFunctor.siteAlgebraInclusion A' (schemeSizeBelow B.cutoff))).obj X ⟶
    (forget₂ CommRingCat RingCat).obj
      (Scheme.Γ.obj (Opposite.op (Spec (CommRingCat.of (X.unop.unop.obj : Type u))))) :=
  (forget₂ CommRingCat RingCat).map
    (Scheme.ΓSpecIso (CommRingCat.of (X.unop.unop.obj : Type u))).inv

/-- The two scalar comparisons agree at each `A'`-algebra of the site: both are the inverse of
the identification of that algebra with the global functions on its spectrum, the structure
morphism to `S` playing no part. Compared through the common normal form
`Stacks.Adequate.nfApp`, one side at a time. -/
private theorem affineRingMap_app_heq_siteRestrict
    (X : ((AdequateFunctor.AlgebrasInSite A' (schemeSizeBelow B.cutoff))ᵒᵖ)ᵒᵖ) :
    HEq ((affineRingMap B A' (Spec.map φ ≫ f)).app X)
      ((AdequateFunctor.siteRestrictRingDiagram.{u} φ.hom (schemeSizeBelow B.cutoff) ≫
        Functor.whiskerLeft
          (AdequateFunctor.siteRestrictAlgebras.{u} φ.hom (schemeSizeBelow B.cutoff)).op.op
          (affineRingMap B A f)).app X) :=
  HEq.trans (b := nfApp B A' X)
    (heq_of_eq (show ((affineRingMap B A' (Spec.map φ ≫ f)).app X :
      (AdequateFunctor.algebraRingDiagramOn
        (AdequateFunctor.siteAlgebraInclusion A' (schemeSizeBelow B.cutoff))).obj X ⟶
      (forget₂ CommRingCat RingCat).obj
        (Scheme.Γ.obj (Opposite.op (Spec (CommRingCat.of (X.unop.unop.obj : Type u)))))) =
      nfApp B A' X from rfl))
    (heq_of_eq (show nfApp B A' X =
      ((AdequateFunctor.siteRestrictRingDiagram.{u} φ.hom (schemeSizeBelow B.cutoff) ≫
        Functor.whiskerLeft
          (AdequateFunctor.siteRestrictAlgebras.{u} φ.hom (schemeSizeBelow B.cutoff)).op.op
          (affineRingMap B A f)).app X :
      (AdequateFunctor.algebraRingDiagramOn
        (AdequateFunctor.siteAlgebraInclusion A' (schemeSizeBelow B.cutoff))).obj X ⟶
      (forget₂ CommRingCat RingCat).obj
        (Scheme.Γ.obj (Opposite.op (Spec (CommRingCat.of (X.unop.unop.obj : Type u))))))
      from rfl))

/-- The structure sheaf read along the two index functors is one and the same ring-valued
presheaf, by `Stacks.Adequate.affineSpecOver_eq_siteRestrict`. -/
private theorem structureSheafComp_eq_siteRestrict :
    (affineSpecOver B A' (Spec.map φ ≫ f)).op ⋙ B.structureSheaf.obj =
      (AdequateFunctor.siteRestrictAlgebras.{u} φ.hom (schemeSizeBelow B.cutoff)).op.op ⋙
        ((affineSpecOver B A f).op ⋙ B.structureSheaf.obj) := by
  rw [affineSpecOver_eq_siteRestrict B A A' φ f]
  exact op_comp_comp_eq _ _ _

/-- The scalar comparison over `A'` is the composite of the comparison of scalar rings under
restriction of the base ring along `φ` with the scalar comparison over `A`. -/
private theorem affineRingMap_heq_siteRestrict :
    HEq (affineRingMap B A' (Spec.map φ ≫ f))
      (AdequateFunctor.siteRestrictRingDiagram.{u} φ.hom (schemeSizeBelow B.cutoff) ≫
        Functor.whiskerLeft
          (AdequateFunctor.siteRestrictAlgebras.{u} φ.hom (schemeSizeBelow B.cutoff)).op.op
          (affineRingMap B A f)) :=
  natTrans_heq_of_app (structureSheafComp_eq_siteRestrict B A A' φ f) _ _
    (fun X => affineRingMap_app_heq_siteRestrict B A A' φ f X)

end Restriction

/-- **The second step of the source's proof of [Stacks, Tag 06VI].** For every ring map
`φ : A ⟶ A'` between affine schemes of the site over `S`, the affine-section functor of `F` at
`A'` *is* the restriction to `A'`-algebras of its affine-section functor at `A`. This is the
sentence "`F_{F, A'}` is the restriction of `F_{F, A}` to the category of `A'`-algebras" of the
source's proof.

An affine-section functor is a pushforward of `F` along its index functor, carrying the scalar
comparison of that functor. The two index functors are equal, by
`Stacks.Adequate.affineSpecOver_eq_siteRestrict`, and the two scalar comparisons are then equal
as well, by `Stacks.Adequate.affineRingMap_heq_siteRestrict`; the identification is therefore
Mathlib's `CategoryTheory.PresheafOfModules.pushforwardComp`, transported along those two
equalities. The `ULift` of the values that [Stacks, Tag 06V9] introduces is absorbed by
`AdequateFunctor.presheafOfModulesUliftIso`, because `max u (max u m) = max u m`. -/
public theorem affineSectionRestriction {τ : CoveringTopology} {S : Scheme.{u}}
    (B : BigSite τ S) (F : SheafOfModules.{max u m} B.structureSheaf) :
    AffineSectionRestriction.{u, m} B F := by
  intro A A' φ f
  exact ⟨(pushforwardCompIsoOfEq (affineSpecOver_eq_siteRestrict B A A' φ f)
      (affineRingMap B A f)
      (AdequateFunctor.siteRestrictRingDiagram.{u} φ.hom (schemeSizeBelow B.cutoff))
      (affineRingMap B A' (Spec.map φ ≫ f))
      (affineRingMap_heq_siteRestrict B A A' φ f) F.val).trans
    ((AdequateFunctor.restrictFunctorOn.{max u m, u} φ.hom
        (schemeSizeBelow B.cutoff)).mapIso
      (AdequateFunctor.presheafOfModulesUliftIso.{u, max u m} _
        (affineSectionFunctor B F A f)).symm)⟩

/-- Adequacy of the affine-section functors of `F` is stable along a ring map between two
affine schemes of the site over `S`. -/
public abbrev AffineBaseChangeAdequacy
    {τ : CoveringTopology} {S : Scheme.{u}} (B : BigSite τ S)
    (F : SheafOfModules.{max u m} B.structureSheaf) : Prop :=
  ∀ (A A' : CommRingCat.{u}) (φ : A ⟶ A') (f : Spec A ⟶ S),
    AdequateFunctor.IsAdequate
      (AdequateFunctor.siteAlgebraInclusion A (schemeSizeBelow B.cutoff))
      (affineSectionFunctor B F A f) →
    AdequateFunctor.IsAdequate
      (AdequateFunctor.siteAlgebraInclusion A' (schemeSizeBelow B.cutoff))
      (affineSectionFunctor B F A' (Spec.map φ ≫ f))

/-- Once `F_{F, A'}` is known to be the restriction of `F_{F, A}` to `A'`-algebras, adequacy of
the affine-section functors is stable along a ring map `A ⟶ A'`: this is
[Stacks, Tag 06V9], `AdequateFunctor.IsAdequate.restrictBaseOn`, transported along that
identification.

The hypothesis `hres` is supplied for every chosen big site and every sheaf of modules by
`Stacks.Adequate.affineSectionRestriction`, so the conclusion holds outright; that is
`Stacks.Adequate.affineBaseChangeAdequacy`. This statement separates the appeal to Tag 06V9
from the identification along which it is transported. -/
public theorem affineBaseChangeAdequacy_of_affineSectionRestriction
    {τ : CoveringTopology} {S : Scheme.{u}} (B : BigSite τ S)
    (F : SheafOfModules.{max u m} B.structureSheaf)
    (hres : AffineSectionRestriction.{u, m} B F) :
    AffineBaseChangeAdequacy.{u, m} B F := by
  intro A A' φ f hadq
  obtain ⟨e⟩ := hres A A' φ f
  exact (AdequateFunctor.IsAdequate.restrictBaseOn.{max u m, u} φ.hom
    (schemeSizeBelow B.cutoff) _ hadq).of_iso e

/-- **Adequacy of the affine-section functors is stable along any ring map between affines of
the site over `S`.** This is [Stacks, Tag 06V9],
`AdequateFunctor.IsAdequate.restrictBaseOn`, transported along
`Stacks.Adequate.affineSectionRestriction`. -/
public theorem affineBaseChangeAdequacy {τ : CoveringTopology} {S : Scheme.{u}}
    (B : BigSite τ S) (F : SheafOfModules.{max u m} B.structureSheaf) :
    AffineBaseChangeAdequacy.{u, m} B F :=
  affineBaseChangeAdequacy_of_affineSectionRestriction B F
    (affineSectionRestriction.{u, m} B F)

/-- Every `τ`-covering of `S` by affine schemes of the site can be refined, over any affine
scheme `Spec A` of the site over `S`, by a finite standard affine `τ`-covering of `Spec A` by
affine schemes of the site, each member of which factors over `S` through a member of the given
covering. This is the opening step of the source's proof of [Stacks, Tag 06VI]. -/
public abbrev StandardAffineRefinement
    {τ : CoveringTopology} {S : Scheme.{u}} (B : BigSite τ S) : Prop :=
  ∀ (I : Type (u + 1)) (A₀ : I → CommRingCat.{u}) (f₀ : ∀ i, Spec (A₀ i) ⟶ S),
    (∀ i, coveringMorphismProperty τ (f₀ i)) →
    (⋃ i, Set.range (f₀ i)) = Set.univ →
    (∀ i, schemeSizeBelow B.cutoff (Spec (A₀ i))) →
    ∀ (A : CommRingCat.{u}) (f : Spec A ⟶ S), schemeSizeBelow B.cutoff (Spec A) →
      ∃ (n : ℕ) (A' : Fin n → CommRingCat.{u}) (g : ∀ j, Spec (A' j) ⟶ Spec A),
        IsStandardCovering τ (fun j => Spec (A' j)) g ∧
        (∀ j, schemeSizeBelow B.cutoff (Spec (A' j))) ∧
        ∀ j, ∃ (i : I) (φ : A₀ i ⟶ A' j), Spec.map φ ≫ f₀ i = g j ≫ f

/-- A standard `τ`-covering reindexed along an equivalence of index types is a standard
`τ`-covering. Only the reindexing to `Fin n` demanded by
`Stacks.Adequate.StandardAffineRefinement` is needed. -/
private theorem isStandardCovering_reindex {τ : CoveringTopology} {T : Scheme.{u}} [IsAffine T]
    {I : Type v} {J : Type*} (eqv : J ≃ I) {U : I → Scheme.{u}} {f : ∀ i, U i ⟶ T}
    (h : IsStandardCovering τ U f) :
    IsStandardCovering τ (fun j => U (eqv j)) (fun j => f (eqv j)) := by
  have : Finite I := h.finite_index
  refine ⟨Finite.of_equiv _ eqv.symm, fun j => h.affine_source _, ?_, fun j => ?_⟩
  · refine Set.eq_univ_of_forall fun x => ?_
    have hx : x ∈ ⋃ i, Set.range (f i) := h.jointly_surjective ▸ Set.mem_univ x
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
    exact Set.mem_iUnion.mpr ⟨eqv.symm i, by rwa [eqv.apply_symm_apply]⟩
  · have hj := h.standard (eqv j)
    cases τ <;> exact hj

/-- A member of a standard `τ`-covering of an affine scheme of a chosen big site is again a
scheme of that site. This is
`AlgebraicGeometry.size_lt_cutoff_of_isStandardCovering` read through the five-way eliminator
of `Stacks.Adequate.BigSite.chosen`. -/
public theorem BigSite.size_lt_of_isStandardCovering {τ : CoveringTopology} {S : Scheme.{u}}
    (B : BigSite τ S) {T : Scheme.{u}} [IsAffine T] {I : Type v} {U : I → Scheme.{u}}
    {f : ∀ i, U i ⟶ T} (h : IsStandardCovering τ U f)
    (hT : schemeSizeBelow B.cutoff T) (i : I) : schemeSizeBelow B.cutoff (U i) := by
  obtain ⟨cut, base_mem, J, isSheaf, chosen⟩ := B
  rcases chosen with ⟨hτ, C, hC, he, hJ⟩ | ⟨hτ, C, hC, he, hJ⟩ | ⟨hτ, C, hC, he, hJ⟩ |
    ⟨hτ, C, hC, he, hJ⟩ | ⟨hτ, C, hC, he, hJ⟩
  all_goals
    subst hτ; subst he
    exact size_lt_cutoff_of_isStandardCovering _ _ h hT i

/-- **The opening step of the source's proof of [Stacks, Tag 06VI].** A `τ`-covering of
`S` by affine schemes of a chosen big site is refined, over any affine scheme `Spec A` of the
site over `S`, by a finite standard affine `τ`-covering of `Spec A` whose members again belong
to the site and factor over `S` through members of the given covering.

The refinement is the base change of the given covering along `Spec A ⟶ S`, which is a
`τ`-covering of `Spec A` because `AlgebraicGeometry.coveringMorphismProperty` is stable under
base change, followed by [Stacks, Tag 03XA]. Its members lie in the site by
`Stacks.Adequate.BigSite.size_lt_of_isStandardCovering`, and each of them maps to the
corresponding member of the base-changed family, hence over `S` to a member of the given
covering. -/
public theorem standardAffineRefinement {τ : CoveringTopology} {S : Scheme.{u}}
    (B : BigSite τ S) : StandardAffineRefinement B := by
  classical
  intro I A₀ f₀ hcov hsurj _hmem A f hA
  have hbc : (coveringMorphismProperty.{u} τ).IsStableUnderBaseChange :=
    ExtendingFunctors.isStableUnderBaseChange_coveringMorphismProperty τ
  let E : PreZeroHypercover.{u + 1} (Spec A) :=
    { I₀ := I, X := fun i => pullback f (f₀ i), f := fun i => pullback.fst f (f₀ i) }
  have hE : E.presieve₀ ∈ Scheme.precoverage (coveringMorphismProperty τ) (Spec A) := by
    refine (Scheme.ofArrows_mem_precoverage_iff (coveringMorphismProperty τ)).mpr
      ⟨fun x => ?_, fun i => ?_⟩
    · have hx : f.base x ∈ ⋃ i, Set.range (f₀ i) := hsurj ▸ Set.mem_univ _
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
      exact ⟨i, by rw [Scheme.Pullback.range_fst]; exact hi⟩
    · exact MorphismProperty.pullback_fst f (f₀ i) (hcov i)
  obtain ⟨V, r, hstd⟩ := exists_standardCovering_refinement τ E hE
  have hfin : Finite V.I₀ := hstd.finite_index
  let eqv : Fin (Nat.card V.I₀) ≃ V.I₀ := (Finite.equivFin V.I₀).symm
  have haff : ∀ j, IsAffine (V.X (eqv j)) := fun j => hstd.affine_source _
  let A' : Fin (Nat.card V.I₀) → CommRingCat.{u} := fun j => Γ(V.X (eqv j), ⊤)
  let ε : ∀ j, Spec (A' j) ≅ V.X (eqv j) := fun j =>
    have := haff j; (Scheme.isoSpec (V.X (eqv j))).symm
  have hstd' : IsStandardCovering τ (fun j => Spec (A' j))
      (fun j => (ε j).hom ≫ V.f (eqv j)) :=
    (isStandardCovering_reindex eqv hstd).of_iso_source ε _ fun _ => rfl
  refine ⟨Nat.card V.I₀, A', fun j => (ε j).hom ≫ V.f (eqv j), hstd',
    fun j => B.size_lt_of_isStandardCovering hstd' hA j, fun j => ?_⟩
  refine ⟨r.s₀ (eqv j), Spec.preimage ((ε j).hom ≫ r.h₀ (eqv j) ≫
    pullback.snd f (f₀ (r.s₀ (eqv j)))), ?_⟩
  rw [Spec.map_preimage, Category.assoc, Category.assoc, Category.assoc,
    ← pullback.condition, ← Category.assoc (r.h₀ (eqv j)), r.w₀ (eqv j)]

/-- Adequacy of the affine-section functors of `F` descends along a finite standard affine
`τ`-covering of an affine scheme of the site over `S`. This is the passage through the product
of the covering algebras in [Stacks, Tag 06VB] followed by the descent of
[Stacks, Tag 06VH].

It is the third step of the source's proof of [Stacks, Tag 06VI], and it holds:
`Stacks.Adequate.standardAffineDescent`, in
`StacksFrontier/AlgebraicGeometry/Adequate/AdequateModules/StandardAffineProductAdequacy.lean`. -/
public abbrev StandardAffineDescent
    {τ : CoveringTopology} {S : Scheme.{u}} (B : BigSite τ S)
    (F : SheafOfModules.{max u m} B.structureSheaf) : Prop :=
  ∀ (A : CommRingCat.{u}) (f : Spec A ⟶ S), schemeSizeBelow B.cutoff (Spec A) →
    ∀ (n : ℕ) (A' : Fin n → CommRingCat.{u}) (g : ∀ j, Spec (A' j) ⟶ Spec A),
      IsStandardCovering τ (fun j => Spec (A' j)) g →
      (∀ j, schemeSizeBelow B.cutoff (Spec (A' j))) →
      (∀ j, AdequateFunctor.IsAdequate
        (AdequateFunctor.siteAlgebraInclusion (A' j) (schemeSizeBelow B.cutoff))
        (affineSectionFunctor B F (A' j) (g j ≫ f))) →
      AdequateFunctor.IsAdequate
        (AdequateFunctor.siteAlgebraInclusion A (schemeSizeBelow B.cutoff))
        (affineSectionFunctor B F A f)

end Stacks.Adequate

end
