module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Quot.PicardStackFibered
public import StacksFrontier.AlgebraicGeometry.Quot.PicardStackRigidification
public import StacksFrontier.AlgebraicGeometry.Stacks.Algebraic.MorphismRepresentableBySpaces.Criterion
public import StacksFrontier.AlgebraicGeometry.Stacks.Representability
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.TwoCategory

/-!
# The Picard category, its rigidification, and the forgetful 1-morphism

In Situation 0D25, with a section `σ : B ⟶ X` of `f : X ⟶ B`, this file constructs the
categories `Picardstack_{X/B}` of Section 0372 and `Picardstack_{X/B, σ}` of Stacks 0D29 as
genuine `CategoryTheory.Category` instances on the objects written down in
`StacksFrontier/AlgebraicGeometry/Quot/PicardStack.lean` and
`StacksFrontier/AlgebraicGeometry/Quot/PicardStackRigidification.lean`, exhibits both as
categories fibred in groupoids over the big fppf site of `S`, and constructs the 1-morphism
between them that forgets the trivialisation along the section.

## Main definitions

* `AlgebraicGeometry.Space.picardCategory` and
  `AlgebraicGeometry.Space.picardCategoryData`: **Section 0372**, the category
  `Picardstack_{X/B}`, and the value of the specification
  `AlgebraicGeometry.Space.PicardCategoryData` it provides.
* `AlgebraicGeometry.Space.picardBasedCategory` and `AlgebraicGeometry.Space.picardCFG`:
  **Stacks 04WN**, `Picardstack_{X/B}` as a category over the big fppf site of `S` and as an
  object of the 2-category of categories fibred in groupoids over it.
* `AlgebraicGeometry.Space.SectionTransportCoherence`: the pseudofunctoriality of the
  restriction `σ_T^*` along the section with respect to the comparisons of Stacks 03LU, in the
  form the identity and the composition of `Picardstack_{X/B, σ}` need.
* `AlgebraicGeometry.Space.sectionedPicardCategory`,
  `AlgebraicGeometry.Space.sectionedPicardBasedCategory` and
  `AlgebraicGeometry.Space.sectionedPicardCFG`: **Stacks 0D29**, the rigidified category
  `Picardstack_{X/B, σ}`, as a category, as a category over the site, and as an object of the
  2-category of categories fibred in groupoids over it.
* `AlgebraicGeometry.Space.forgetTrivializationBased` and
  `AlgebraicGeometry.Space.forgetTrivialization`: **Stacks 0D29**, the functor
  `Picardstack_{X/B, σ} ⟶ Picardstack_{X/B}` forgetting the trivialisation, as a functor over
  the site and as a 1-morphism of the 2-category of categories fibred in groupoids.  This is the
  1-morphism of **Stacks 0D2A**.
* `AlgebraicGeometry.Space.forgetTrivializationFibreEquiv`: **Stacks 0D2A**, the identification
  of the fibre of that 1-morphism over an object `(T, h, L)` with the trivialisations
  `𝒪_T ≅ σ_T^*L`, that is with `Isom_T(𝒪_T, σ_T^*L)`.

## Main results

* `AlgebraicGeometry.Space.PicardHom.id_comp`, `AlgebraicGeometry.Space.PicardHom.comp_id` and
  `AlgebraicGeometry.Space.PicardHom.comp_assoc`: **the three category laws of Section 0372**
  for the identities and the composition of `AlgebraicGeometry.Space.PicardHom`.
* `AlgebraicGeometry.Space.sectionedPicardProjection_isFiberedInGroupoids_schemesOver` and
  `AlgebraicGeometry.Space.sectionedPicardProjection_isFiberedInGroupoids`: the projection of
  `Picardstack_{X/B, σ}` to the test schemes over the base, and to the schemes of the site, is
  fibred in groupoids.
* `AlgebraicGeometry.Space.forgetTrivializationBased_faithful` and
  `AlgebraicGeometry.Space.forgetTrivialization_inducedFiberFunctor_faithful`: the functor
  forgetting the trivialisation is faithful, and so is the functor it induces on every fibre.
  The second is the faithfulness half of the criterion of Stacks 02ZY.
* `AlgebraicGeometry.Space.exists_sectionedPicardObject_iff`: **Stacks 0D2A**, an object
  `(T, h, L)` of `Picardstack_{X/B}` lifts along the 1-morphism exactly when `σ_T^*[L] = 0` in
  `Pic(T)`, which is the object-level content of its surjectivity clause.

## Implementation notes

**The three category laws.**  Each law is one application of the composition calculus of
`StacksFrontier/AlgebraicGeometry/Quot/CoherentStack.lean` —
`CategoryTheory.Functor.fibreComp_id_left`, `CategoryTheory.Functor.fibreComp_id_right` and
`CategoryTheory.Functor.fibreComp_assoc` — at the three coherences
`AlgebraicGeometry.Space.baseChangeIdComparison_comp_fac`,
`AlgebraicGeometry.Space.baseChangeComp_idComparison_fac` and
`AlgebraicGeometry.Space.baseChangeCompComparison_assoc` of
`StacksFrontier/AlgebraicGeometry/Quot/PicardStack.lean`.  The reduction is carried out through
equalities whose two sides are *written out in full*: a comparison of two
`CategoryTheory.Functor.fibreComp` terms whose data differ only by an unfolding of
`AlgebraicGeometry.Space.PicardHom.id` or `AlgebraicGeometry.Space.PicardHom.comp` is decided
by congruence and is cheap, whereas leaving part of one side to be inferred makes the
elaborator compare `CategoryTheory.Functor.obj` applications of
`AlgebraicGeometry.Space.modulePullback` with a metavariable in the argument, which unfolds that
definition.  The named steps `AlgebraicGeometry.Space.PicardHom.comp_fibre` and its companions
are therefore stated and not inlined.

**What the rigidified category needs beyond the Picard category.**  Its hom-sets are the
morphisms of `Picardstack_{X/B}` compatible with the chosen trivialisations, a condition which
is a proposition, so the three laws transport from `Picardstack_{X/B}` through
`AlgebraicGeometry.Space.PicardSituation.SectionedPicardHom.ext`.  What does not transport is
the existence of the identity and of the composition: both ask that
`AlgebraicGeometry.Space.PicardSituation.transportTrivialization` be pseudofunctorial, and that
is a coherence of the comparisons of Stacks 03LU for the section square, carried here as
`AlgebraicGeometry.Space.SectionTransportCoherence`.  It cannot be derived from
`AlgebraicGeometry.Space.ModulePushforwardCoherence`: the identification
`AlgebraicGeometry.Space.structureModulePullbackIso` of the inverse image of a structure sheaf
is the unit of the adjunction of Stacks 03LU, while the unit law
`AlgebraicGeometry.Space.ModulePushforwardCoherence.idIso` of that coherence is unconstrained
data, so no equation between the two is available; the same holds of the composite, which asks
the inverse image of a structure sheaf to be compatible with the comparison of a composite.  The
hypothesis mentions neither Picard objects nor trivialisations.

**What of Stacks 0D2A is here.**  The source's proof rests on one identification: the fibre of
the 1-morphism over an object `(T, h, L)` is the set of trivialisations of `L` along the section,
that is `Isom_T(𝒪_T, σ_T^*L)`.  That identification is
`AlgebraicGeometry.Space.forgetTrivializationFibreEquiv` and it is unconditional, as is the
criterion `AlgebraicGeometry.Space.exists_sectionedPicardObject_iff` for an object to lift,
which reads it through Stacks 0D2B.  The full statement of Stacks 0D2A — the 1-morphism is
representable, surjective and smooth — is
`AlgebraicGeometry.Space.forgetTrivialization_representable_surjective_smooth` of
`StacksFrontier/AlgebraicGeometry/Quot/PicardForgetTrivializationRepresentable.lean`.

**Universes.**  The objects of `Picardstack_{X/B}` form a type in `Type (u + 1)` and so do its
hom-sets, as in `StacksFrontier/AlgebraicGeometry/Quot/PicardStack.lean`; the same holds of the
rigidified category, whose objects and morphisms add to those of `Picardstack_{X/B}` a datum in
the modules and a proposition.  Both are therefore
`CategoryTheory.BasedCategory.{u + 1, u + 1}` over the big fppf site of `S`, whose objects form
a type in `Type (u + 1)` with hom-sets in `Type u`.

## References

* [Stacks Project, Section 0372](https://stacks.math.columbia.edu/tag/0372)
* [Stacks Project, Tag 0D25](https://stacks.math.columbia.edu/tag/0D25)
* [Stacks Project, Tag 0D29](https://stacks.math.columbia.edu/tag/0D29)
* [Stacks Project, Tag 0D2A](https://stacks.math.columbia.edu/tag/0D2A)
* [Stacks Project, Tag 04WN](https://stacks.math.columbia.edu/tag/04WN)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 02XS](https://stacks.math.columbia.edu/tag/02XS)
* [Stacks Project, Tag 0B8P](https://stacks.math.columbia.edu/tag/0B8P)
* [Stacks Project, Tag 08K9](https://stacks.math.columbia.edu/tag/08K9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Space

universe u

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-! ### A cancellation of transports -/

/-- A transport followed by a transport back is no transport at all. -/
theorem eqToHom_comp_eqToHom_comp_picard {C : Type*} [Category* C] {X Y W : C}
    (p : X = Y) (q : Y = X) (g : X ⟶ W) : eqToHom p ≫ eqToHom q ≫ g = g := by
  rw [← Category.assoc, eqToHom_trans, eqToHom_refl, Category.id_comp]

/-- A transport along an equality of an object with itself is no transport at all. -/
theorem eqToHom_refl_comp_picard {C : Type*} [Category* C] {X W : C} (p : X = X)
    (g : X ⟶ W) : eqToHom p ≫ g = g := by
  simp

/-- Transports along equalities of an object with itself are no transports at all. -/
theorem eqToHom_refl_comp_eqToHom_refl_picard {C : Type*} [Category* C] {X Y : C}
    (p : X = X) (q : Y = Y) (g : X ⟶ Y) : eqToHom p ≫ g ≫ eqToHom q = g := by
  simp

/-! ### The three category laws of `Picardstack_{X/B}` -/

namespace PicardHom

variable {s : PicardSituation B S hS}

/-- The comparison of modules of a composite is the composite of the comparisons along the
comparison of Stacks 03LU for the composite of the base maps. -/
theorem comp_fibre {A C D : PicardObject s} (m : PicardHom A C) (n : PicardHom C D) :
    (PicardHom.comp m n).fibre =
      Functor.fibreComp (baseChangeCompComparison s.f m.base n.base) m.fibre n.fibre :=
  rfl

/-- The data of a composite with an identity on the left, written out. -/
private theorem comp_id_left_data {hc : ModulePushforwardCoherence B S hS}
    {A C : PicardObject s} (m : PicardHom A C) :
    Functor.fibreComp (baseChangeCompComparison s.f (PicardHom.id hc A).base m.base)
        (PicardHom.id hc A).fibre m.fibre =
      Functor.fibreComp (baseChangeCompComparison s.f (𝟙 A.T) m.base)
        ((baseChangeIdComparison hc s.f A.T).hom.app A.lineBundle) m.fibre :=
  rfl

/-- The data of a composite with an identity on the right, written out. -/
private theorem comp_id_right_data {hc : ModulePushforwardCoherence B S hS}
    {A C : PicardObject s} (m : PicardHom A C) :
    Functor.fibreComp (baseChangeCompComparison s.f m.base (PicardHom.id hc C).base) m.fibre
        (PicardHom.id hc C).fibre =
      Functor.fibreComp (baseChangeCompComparison s.f m.base (𝟙 C.T)) m.fibre
        ((baseChangeIdComparison hc s.f C.T).hom.app C.lineBundle) :=
  rfl

/-- The data of a left-bracketed triple composite, written out. -/
private theorem comp_assoc_left_data {A C D E : PicardObject s} (m : PicardHom A C)
    (n : PicardHom C D) (p : PicardHom D E) :
    Functor.fibreComp (baseChangeCompComparison s.f (PicardHom.comp m n).base p.base)
        (Functor.fibreComp (baseChangeCompComparison s.f m.base n.base) m.fibre n.fibre)
        p.fibre =
      Functor.fibreComp (baseChangeCompComparison s.f (m.base ≫ n.base) p.base)
        (Functor.fibreComp (baseChangeCompComparison s.f m.base n.base) m.fibre n.fibre)
        p.fibre :=
  rfl

/-- The data of a right-bracketed triple composite, written out. -/
private theorem comp_assoc_right_data {A C D E : PicardObject s} (m : PicardHom A C)
    (n : PicardHom C D) (p : PicardHom D E) :
    Functor.fibreComp (baseChangeCompComparison s.f m.base (PicardHom.comp n p).base) m.fibre
        (Functor.fibreComp (baseChangeCompComparison s.f n.base p.base) n.fibre p.fibre) =
      Functor.fibreComp (baseChangeCompComparison s.f m.base (n.base ≫ p.base)) m.fibre
        (Functor.fibreComp (baseChangeCompComparison s.f n.base p.base) n.fibre p.fibre) :=
  rfl

/-- The comparison of modules of a composite with the identity on the left is the one of the
remaining factor, transported along the identity law of the base maps. -/
theorem comp_id_left_fibre (hc : ModulePushforwardCoherence B S hS) {A C : PicardObject s}
    (m : PicardHom A C) :
    (PicardHom.comp (PicardHom.id hc A) m).fibre =
      (baseChangeMapComparison s.f (Category.id_comp m.base)).hom.app C.lineBundle ≫ m.fibre :=
  (comp_fibre _ m).trans ((comp_id_left_data m).trans
    (Functor.fibreComp_id_left (baseChangeIdComparison hc s.f A.T)
      (baseChangeCompComparison s.f (𝟙 A.T) m.base)
      (baseChangeMapComparison s.f (Category.id_comp m.base))
      (baseChangeIdComparison_comp_fac hc s.f m.base) m.fibre))

/-- The comparison of modules of a composite with the identity on the right is the one of the
remaining factor, transported along the identity law of the base maps. -/
theorem comp_id_right_fibre (hc : ModulePushforwardCoherence B S hS) {A C : PicardObject s}
    (m : PicardHom A C) :
    (PicardHom.comp m (PicardHom.id hc C)).fibre =
      (baseChangeMapComparison s.f (Category.comp_id m.base)).hom.app C.lineBundle ≫ m.fibre :=
  (comp_fibre m _).trans ((comp_id_right_data m).trans
    (Functor.fibreComp_id_right (baseChangeIdComparison hc s.f C.T)
      (baseChangeCompComparison s.f m.base (𝟙 C.T))
      (baseChangeMapComparison s.f (Category.comp_id m.base))
      (baseChangeComp_idComparison_fac hc s.f m.base) m.fibre))

/-- The comparison of Stacks 03LU for equal base maps is a transport. -/
private theorem baseChangeMapComparison_hom_app_comp {T T' : s.SchemesOver} {g g' : T ⟶ T'}
    (e : g = g') (L : Modules.{u, u} B S hS (baseChangeSpace s.f T').1 (baseChangeSpace s.f T').2)
    {N : Modules.{u, u} B S hS (baseChangeSpace s.f T).1 (baseChangeSpace s.f T).2}
    (φ : (modulePullback B S hS (baseChangeMap s.f g')).obj L ⟶ N) :
    (baseChangeMapComparison s.f e).hom.app L ≫ φ = eqToHom (by rw [e]) ≫ φ := by
  subst e
  simp [baseChangeMapComparison]

/-- **Section 0372, the identity law at the source.**  Composing a morphism of
`Picardstack_{X/B}` with the identity of its source returns it. -/
@[stacks 0372 "the identity law at the source for the composition of the Picard stack"]
theorem id_comp (hc : ModulePushforwardCoherence B S hS) {A C : PicardObject s}
    (m : PicardHom A C) : PicardHom.comp (PicardHom.id hc A) m = m := by
  refine PicardHom.ext (Category.id_comp m.base) ?_
  rw [comp_id_left_fibre]
  rw [baseChangeMapComparison_hom_app_comp]
  exact eqToHom_comp_eqToHom_comp_picard _ _ _

/-- **Section 0372, the identity law at the target.**  Composing a morphism of
`Picardstack_{X/B}` with the identity of its target returns it. -/
@[stacks 0372 "the identity law at the target for the composition of the Picard stack"]
theorem comp_id (hc : ModulePushforwardCoherence B S hS) {A C : PicardObject s}
    (m : PicardHom A C) : PicardHom.comp m (PicardHom.id hc C) = m := by
  refine PicardHom.ext (Category.comp_id m.base) ?_
  rw [comp_id_right_fibre]
  rw [baseChangeMapComparison_hom_app_comp]
  exact eqToHom_comp_eqToHom_comp_picard _ _ _

/-- **Section 0372, associativity.**  The composition of `Picardstack_{X/B}` is associative. -/
@[stacks 0372 "associativity of the composition of the Picard stack"]
theorem comp_assoc (hc : ModulePushforwardCoherence B S hS) {A C D E : PicardObject s}
    (m : PicardHom A C) (n : PicardHom C D) (p : PicardHom D E) :
    PicardHom.comp (PicardHom.comp m n) p = PicardHom.comp m (PicardHom.comp n p) := by
  refine PicardHom.ext (Category.assoc m.base n.base p.base) ?_
  rw [comp_fibre (PicardHom.comp m n) p, comp_fibre m n, comp_assoc_left_data,
    Functor.fibreComp_assoc (baseChangeCompComparison s.f m.base n.base)
      (baseChangeCompComparison s.f (m.base ≫ n.base) p.base)
      (baseChangeCompComparison s.f n.base p.base)
      (baseChangeCompComparison s.f m.base (n.base ≫ p.base))
      (baseChangeMapComparison s.f (Category.assoc m.base n.base p.base))
      (baseChangeCompComparison_assoc hc s.f m.base n.base p.base) m.fibre n.fibre p.fibre,
    comp_fibre m (PicardHom.comp n p), comp_fibre n p, comp_assoc_right_data]
  rw [baseChangeMapComparison_hom_app_comp]
  exact eqToHom_comp_eqToHom_comp_picard _ _ _

end PicardHom

/-! ### The Picard category and its projection -/

/-- **Section 0372, the category `Picardstack_{X/B}`.**  The objects are the triples `(U, b, L)`,
the morphisms are the pairs `(f, g)` of a morphism of test schemes over the base and an
isomorphism `f^*L' ≅ L`, and the identities and the composition are the ones of Section 0372. -/
@[instance_reducible, stacks 0372 "the category Picardstack_{X/B}, conditional on the \
pseudofunctoriality of the direct images of Stacks 03LU that its identity already needs"]
def picardCategory (hc : ModulePushforwardCoherence B S hS) (s : PicardSituation B S hS) :
    Category.{u + 1} (PicardObject s) where
  Hom A C := PicardHom A C
  id A := PicardHom.id hc A
  comp m n := PicardHom.comp m n
  id_comp m := PicardHom.id_comp hc m
  comp_id m := PicardHom.comp_id hc m
  assoc m n p := PicardHom.comp_assoc hc m n p

/-- **Section 0372, the functor `p`.**  The projection of `Picardstack_{X/B}` to the test schemes
over the base, forgetting the invertible module. -/
@[stacks 0372 "the projection of the Picard stack to the test schemes over the base"]
def picardProjection (hc : ModulePushforwardCoherence B S hS) (s : PicardSituation B S hS) :
    letI : Category.{u + 1} (PicardObject s) := picardCategory hc s
    PicardObject s ⥤ s.SchemesOver :=
  letI : Category.{u + 1} (PicardObject s) := picardCategory hc s
  { obj := fun A ↦ A.T
    map := fun m ↦ m.base
    map_id := fun _ ↦ rfl
    map_comp := fun _ _ ↦ rfl }

/-- **Section 0372.**  The category `Picardstack_{X/B}` together with its projection satisfies
the specification `AlgebraicGeometry.Space.PicardCategoryData`: its hom-sets, identities,
composition and projection are the ones of Section 0372. -/
@[stacks 0372 "a value of the specification of the category Picardstack_{X/B} with its \
projection, conditional on the pseudofunctoriality of the direct images of Stacks 03LU"]
def picardCategoryData (hc : ModulePushforwardCoherence B S hS)
    (s : PicardSituation B S hS) : PicardCategoryData hc s where
  category := picardCategory hc s
  projection := picardProjection hc s
  hom_type _ _ := rfl
  identity _ := rfl
  composition _ _ := rfl
  projection_obj _ := rfl
  projection_map _ := (eqToHom_refl_comp_eqToHom_refl_picard _ _ _).symm

/-- **Stacks 04WN.**  `Picardstack_{X/B}` as a category over the big fppf site of `S`: its
projection to the test schemes over the base, followed by the projection of those to the schemes
of the site. -/
def picardBasedCategory (hc : ModulePushforwardCoherence B S hS)
    (s : PicardSituation B S hS) : BasedCategory.{u + 1, u + 1} (BigFppfOver B S hS) :=
  letI : Category.{u + 1} (PicardObject s) := (picardCategoryData hc s).category
  BasedCategory.ofFunctor
    ((picardCategoryData hc s).projection ⋙
      CostructuredArrow.proj (schemeSpaceFunctor B S hS) s.base)

/-- **Condition (1) of Stacks 02ZI for the functor of Stacks 04WN**, for the category
constructed here: the projection of `Picardstack_{X/B}` to the schemes of the big fppf site is
fibred in groupoids. -/
theorem picardBasedCategory_isFiberedInGroupoids (hc : ModulePushforwardCoherence B S hS)
    (s : PicardSituation B S hS) :
    (picardBasedCategory hc s).p.IsFiberedInGroupoids :=
  picardProjection_isFiberedInGroupoids hc (picardCategoryData hc s)

/-- **Stacks 04WN.**  `Picardstack_{X/B}` as an object of the 2-category of categories fibred in
groupoids over the big fppf site of `S`. -/
def picardCFG (hc : ModulePushforwardCoherence B S hS) (s : PicardSituation B S hS) :
    CatFiberedInGroupoids.{u, u + 1, u + 1, u + 1} (BigFppfOver B S hS) :=
  CatFiberedInGroupoids.mk (picardBasedCategory hc s)
    (picardBasedCategory_isFiberedInGroupoids hc s)

/-! ### The rigidified Picard category -/

/-- **The pseudofunctoriality of the restriction along the section**: transporting a
trivialisation along an identity of `Picardstack_{X/B}` returns it, and transporting along a
composite is transporting along its two factors in turn.

This is the coherence of the comparisons of Stacks 03LU for the section square, in the form the
identity and the composition of `Picardstack_{X/B, σ}` need; it speaks of modules, test schemes
and the section alone. -/
structure SectionTransportCoherence (hc : ModulePushforwardCoherence B S hS)
    {s : PicardSituation B S hS} (σ : s.base ⟶ s.X) (hσ : σ ≫ s.f = 𝟙 s.base) : Prop where
  /-- Transporting along an identity returns the trivialisation. -/
  transport_id : ∀ (A : PicardObject s)
    (α : structureModule (s.baseSpaceAt A.T) ⟶
      (PicardSituation.sectionPullback σ hσ A.T).obj A.lineBundle),
    PicardSituation.transportTrivialization (σ := σ) (hσ := hσ) (PicardHom.id hc A) α = α
  /-- Transporting along a composite is transporting along its two factors in turn. -/
  transport_comp : ∀ {A C D : PicardObject s} (m : PicardHom A C) (n : PicardHom C D)
    (α : structureModule (s.baseSpaceAt D.T) ⟶
      (PicardSituation.sectionPullback σ hσ D.T).obj D.lineBundle),
    PicardSituation.transportTrivialization (σ := σ) (hσ := hσ) (PicardHom.comp m n) α =
      PicardSituation.transportTrivialization (σ := σ) (hσ := hσ) m
        (PicardSituation.transportTrivialization (σ := σ) (hσ := hσ) n α)

section Sectioned

variable {s : PicardSituation B S hS} {σ : s.base ⟶ s.X} {hσ : σ ≫ s.f = 𝟙 s.base}

/-- **Stacks 0D29, the category `Picardstack_{X/B, σ}`.**  The objects are the quadruples
`(T, h, L, α)` and the morphisms are the morphisms of `Picardstack_{X/B}` compatible with the
trivialisations; the identities and the composition are those of `Picardstack_{X/B}`. -/
@[instance_reducible, stacks 0D29 "the rigidified category Picardstack_{X/B, sigma}, \
conditional on the pseudofunctoriality of the restriction along the section"]
def sectionedPicardCategory (hc : ModulePushforwardCoherence B S hS)
    (ht : SectionTransportCoherence hc σ hσ) :
    Category.{u + 1} (PicardSituation.SectionedPicardObject σ hσ) where
  Hom A C := PicardSituation.SectionedPicardHom A C
  id A := { toPicardHom := PicardHom.id hc A.toPicardObject
            compatible := ht.transport_id _ _ }
  comp m n := { toPicardHom := PicardHom.comp m.toPicardHom n.toPicardHom
                compatible := by
                  rw [ht.transport_comp, n.compatible, m.compatible] }
  id_comp m := PicardSituation.SectionedPicardHom.ext (PicardHom.id_comp hc m.toPicardHom)
  comp_id m := PicardSituation.SectionedPicardHom.ext (PicardHom.comp_id hc m.toPicardHom)
  assoc m n p :=
    PicardSituation.SectionedPicardHom.ext
      (PicardHom.comp_assoc hc m.toPicardHom n.toPicardHom p.toPicardHom)

/-- **Stacks 0D29, the projection of `Picardstack_{X/B, σ}`** to the test schemes over the base,
forgetting the invertible module and its trivialisation. -/
def sectionedPicardProjection (hc : ModulePushforwardCoherence B S hS)
    (ht : SectionTransportCoherence hc σ hσ) :
    letI : Category.{u + 1} (PicardSituation.SectionedPicardObject σ hσ) :=
      sectionedPicardCategory hc ht
    PicardSituation.SectionedPicardObject σ hσ ⥤ s.SchemesOver :=
  letI : Category.{u + 1} (PicardSituation.SectionedPicardObject σ hσ) :=
    sectionedPicardCategory hc ht
  { obj := fun A ↦ A.testScheme
    map := fun m ↦ m.toPicardHom.base
    map_id := fun _ ↦ rfl
    map_comp := fun _ _ ↦ rfl }

/-- **The projection of `Picardstack_{X/B, σ}` to the test schemes over the base is fibred in
groupoids.**  The lift of a morphism of test schemes is the inverse image of the object with its
transported trivialisation, and the fill-in is the one of `Picardstack_{X/B}`, which is
compatible with the trivialisations because transporting is pseudofunctorial. -/
theorem sectionedPicardProjection_isFiberedInGroupoids_schemesOver
    (hc : ModulePushforwardCoherence B S hS) (ht : SectionTransportCoherence hc σ hσ) :
    letI : Category.{u + 1} (PicardSituation.SectionedPicardObject σ hσ) :=
      sectionedPicardCategory hc ht
    (sectionedPicardProjection hc ht).IsFiberedInGroupoids := by
  let _ : Category.{u + 1} (PicardSituation.SectionedPicardObject σ hσ) :=
    sectionedPicardCategory hc ht
  constructor
  · intro V U f x hx
    refine ⟨x.pullback (f ≫ eqToHom hx.symm),
      x.pullbackSectionedHom (f ≫ eqToHom hx.symm),
      IsHomLift.of_fac' (sectionedPicardProjection hc ht) f _ rfl hx ?_⟩
    exact (eqToHom_refl_comp_picard _ _).symm
  · intro x y z Φ Ψ f hf
    obtain ⟨Ψpic, Ψcompat⟩ := Ψ
    obtain ⟨Ψb, Ψf, Ψi⟩ := Ψpic
    change f ≫ Φ.toPicardHom.base = Ψb at hf
    subst hf
    refine ⟨⟨@PicardSituation.fillIn _ _ _ _ _ _ z.toPicardObject Φ.toPicardHom f Ψf Ψi, ?_⟩,
      ⟨rfl, ?_⟩, ?_⟩
    · rw [← Φ.compatible, ← ht.transport_comp,
        PicardSituation.fillIn_comp (z := z.toPicardObject) Φ.toPicardHom f Ψf Ψi]
      exact Ψcompat
    · exact PicardSituation.SectionedPicardHom.ext
        (PicardSituation.fillIn_comp (z := z.toPicardObject) Φ.toPicardHom f Ψf Ψi)
    · intro χ hχ
      refine PicardSituation.SectionedPicardHom.ext
        (PicardSituation.eq_fillIn (z := z.toPicardObject) Φ.toPicardHom f Ψf Ψi hχ.1 ?_)
      exact congrArg PicardSituation.SectionedPicardHom.toPicardHom hχ.2

/-- **Stacks 0D29.**  `Picardstack_{X/B, σ}` as a category over the big fppf site of `S`. -/
def sectionedPicardBasedCategory (hc : ModulePushforwardCoherence B S hS)
    (ht : SectionTransportCoherence hc σ hσ) :
    BasedCategory.{u + 1, u + 1} (BigFppfOver B S hS) :=
  letI : Category.{u + 1} (PicardSituation.SectionedPicardObject σ hσ) :=
    sectionedPicardCategory hc ht
  BasedCategory.ofFunctor
    (sectionedPicardProjection hc ht ⋙
      CostructuredArrow.proj (schemeSpaceFunctor B S hS) s.base)

/-- **The projection of `Picardstack_{X/B, σ}` to the schemes of the big fppf site is fibred in
groupoids**: the relative statement composed with the projection of the test schemes over the
base to the schemes of the site. -/
theorem sectionedPicardProjection_isFiberedInGroupoids
    (hc : ModulePushforwardCoherence B S hS) (ht : SectionTransportCoherence hc σ hσ) :
    (sectionedPicardBasedCategory hc ht).p.IsFiberedInGroupoids :=
  let _ : Category.{u + 1} (PicardSituation.SectionedPicardObject σ hσ) :=
    sectionedPicardCategory hc ht
  Functor.IsFiberedInGroupoids.comp (sectionedPicardProjection hc ht)
    (CostructuredArrow.proj (schemeSpaceFunctor B S hS) s.base)
    (sectionedPicardProjection_isFiberedInGroupoids_schemesOver hc ht)
    (Functor.IsFiberedInGroupoids.costructuredArrow_proj (schemeSpaceFunctor B S hS) s.base)

/-- **Stacks 0D29.**  `Picardstack_{X/B, σ}` as an object of the 2-category of categories fibred
in groupoids over the big fppf site of `S`. -/
def sectionedPicardCFG (hc : ModulePushforwardCoherence B S hS)
    (ht : SectionTransportCoherence hc σ hσ) :
    CatFiberedInGroupoids.{u, u + 1, u + 1, u + 1} (BigFppfOver B S hS) :=
  CatFiberedInGroupoids.mk (sectionedPicardBasedCategory hc ht)
    (sectionedPicardProjection_isFiberedInGroupoids hc ht)

/-! ### The 1-morphism forgetting the trivialisation -/

/-- **Stacks 0D29, the functor `Picardstack_{X/B, σ} ⟶ Picardstack_{X/B}`** forgetting the
trivialisation along the section, as a functor over the big fppf site of `S`. -/
@[stacks 0D29 "the functor forgetting the trivialization along the section, as a functor over \
the big fppf site"]
def forgetTrivializationBased (hc : ModulePushforwardCoherence B S hS)
    (ht : SectionTransportCoherence hc σ hσ) :
    sectionedPicardBasedCategory hc ht ⥤ᵇ picardBasedCategory hc s where
  toFunctor :=
    letI : Category.{u + 1} (PicardSituation.SectionedPicardObject σ hσ) :=
      sectionedPicardCategory hc ht
    letI : Category.{u + 1} (PicardObject s) := picardCategory hc s
    { obj := fun A ↦ A.toPicardObject
      map := fun m ↦ m.toPicardHom
      map_id := fun _ ↦ rfl
      map_comp := fun _ _ ↦ rfl }
  w := rfl

/-- **The functor forgetting the trivialisation is faithful**, a morphism of
`Picardstack_{X/B, σ}` being determined by its underlying morphism of `Picardstack_{X/B}`. -/
theorem forgetTrivializationBased_faithful (hc : ModulePushforwardCoherence B S hS)
    (ht : SectionTransportCoherence hc σ hσ) :
    (forgetTrivializationBased hc ht).toFunctor.Faithful :=
  ⟨fun h ↦ PicardSituation.SectionedPicardHom.ext h⟩

/-- **Stacks 0D29, the 1-morphism `Picardstack_{X/B, σ} ⟶ Picardstack_{X/B}`** of the 2-category
of categories fibred in groupoids over the big fppf site of `S`. -/
@[stacks 0D29 "the 1-morphism of categories fibred in groupoids forgetting the trivialization \
along the section"]
def forgetTrivialization (hc : ModulePushforwardCoherence B S hS)
    (ht : SectionTransportCoherence hc σ hσ) :
    sectionedPicardCFG hc ht ⟶ picardCFG hc s :=
  Bicategory.InducedBicategory.mkHom (forgetTrivializationBased hc ht)

/-! ### The fibre of the forgetful 1-morphism -/

/-- The forgetful functor sends an object of `Picardstack_{X/B, σ}` to its underlying triple. -/
theorem forgetTrivializationBased_obj (hc : ModulePushforwardCoherence B S hS)
    (ht : SectionTransportCoherence hc σ hσ)
    (A : PicardSituation.SectionedPicardObject σ hσ) :
    (forgetTrivializationBased hc ht).toFunctor.obj A = A.toPicardObject :=
  rfl

/-- **The fibre of the 1-morphism of Stacks 0D2A is the set of trivialisations along the
section.**  The objects of `Picardstack_{X/B, σ}` lying over an object `(T, h, L)` of
`Picardstack_{X/B}` are the quadruples `(T, h, L, α)`, so they correspond bijectively to the
trivialisations `α : 𝒪_T ≅ σ_T^*L`; the fibre is `Isom_T(𝒪_T, σ_T^*L)`, which is the
identification the source's proof of Stacks 0D2A rests on. -/
@[stacks 0D2A "ONLY the fibre identification the proof rests on: the fibre of \
Picardstack_{X/B,sigma} -> Picardstack_{X/B} over (T,h,L) is the set of trivializations \
O_T = sigma_T^*L, that is Isom_T(O_T, sigma_T^*L). NONE of the three clauses - representable, \
surjective, smooth - is proved; see the implementation notes of this file for the three \
obstructions"]
def forgetTrivializationFibreEquiv (A : PicardObject s) :
    (structureModule (s.baseSpaceAt A.T) ≅
        (PicardSituation.sectionPullback σ hσ A.T).obj A.lineBundle) ≃
      {A' : PicardSituation.SectionedPicardObject σ hσ // A'.toPicardObject = A} where
  toFun α := ⟨⟨A, α⟩, rfl⟩
  invFun A' := A'.2 ▸ A'.1.trivialization
  left_inv _ := rfl
  right_inv A' := by
    obtain ⟨⟨A₀, α⟩, h⟩ := A'
    change A₀ = A at h
    subst h
    rfl

/-- **An object of `Picardstack_{X/B}` lies in the image of the 1-morphism of Stacks 0D2A exactly
when the class of its invertible module is killed by `σ_T^*`.**  By the fibre identification a
lift is a trivialisation of `L` along the section, and by Stacks 0D2B such a trivialisation
exists exactly when `σ_T^*[L] = 0` in `Pic(T)`. -/
@[stacks 0D2A "ONLY the object-level content of clause (2): an object (T,h,L) of \
Picardstack_{X/B} lifts along the 1-morphism of this tag exactly when sigma_T^*[L] = 0 in \
Pic(T). The three clauses themselves - representable, surjective and smooth in the sense of \
Stacks 02ZW and 03YK - are NOT proved; see the implementation notes of this file"]
theorem exists_sectionedPicardObject_iff (A : PicardObject s) :
    (∃ A' : PicardSituation.SectionedPicardObject σ hσ, A'.toPicardObject = A) ↔
      PicardSituation.sectionPicardPullback σ hσ A.T
        (picardClass (s.baseChange A.T) A.lineBundle A.invertible) = 0 := by
  rw [PicardSituation.sectionPicardPullback_picardClass_eq_zero_iff]
  constructor
  · rintro ⟨A', h⟩
    exact ⟨(forgetTrivializationFibreEquiv A).symm ⟨A', h⟩ |>.symm⟩
  · rintro ⟨β⟩
    exact ⟨⟨A, β.symm⟩, rfl⟩

/-! ### Clause (1) of Stacks 0D2A -/

/-- **The functors on fibres of the 1-morphism forgetting the trivialisation are faithful**: a
morphism of `Picardstack_{X/B, σ}` is determined by its underlying morphism of
`Picardstack_{X/B}`, so the induced functor on every fibre is injective on morphisms.  This is
the faithfulness half of the criterion of Stacks 02ZY. -/
theorem forgetTrivialization_inducedFiberFunctor_faithful
    (hc : ModulePushforwardCoherence B S hS) (ht : SectionTransportCoherence hc σ hσ)
    (U : BigFppfOver B S hS) :
    (Stacks.RepresentableMorphism.inducedFiberFunctor
        (sectionedPicardCFG hc ht).val.p (picardCFG hc s).val.p
        (CatFiberedInGroupoids.homFunctor (forgetTrivialization hc ht))
        (CatFiberedInGroupoids.homFunctor_comp_p (forgetTrivialization hc ht))
        U).Faithful :=
  Stacks.RepresentableMorphism.inducedFiberFunctor_faithful_of_fiberHom_injective _ _ _ _ U
    fun _ _ h ↦ PicardSituation.SectionedPicardHom.ext h

end Sectioned

end AlgebraicGeometry.Space

end
