module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStack
public import StacksFrontier.AlgebraicGeometry.Quot.PicardFunctor

/-!
# The Picard stack of a morphism of algebraic spaces

Let `π : X ⟶ B` be a morphism of algebraic spaces over a scheme `S` of a big fppf site.
Stacks, Section 0372 introduces the category `Picardstack_{X/B}` whose objects are the triples
`(U, b, L)` with `U` a scheme of the site over `S`, `b : U ⟶ B` a morphism to the base and `L`
an invertible module on the base change `X_U`, and whose morphisms
`(f, g) : (U, b, L) ⟶ (U', b', L')` are a morphism `f : U ⟶ U'` of schemes over `B` together
with an isomorphism `g : f^*L' ⟶ L`.  Composition composes the base maps and the inverse images
of the module isomorphisms.  This file writes down those four pieces of data — the objects, the
morphisms, the identities and the composition — and the three comparisons of inverse images that
the identities and the composition are built from.

The pair `(U, b)` of the source is an object of `AlgebraicGeometry.Space.SchemesOver`, a
costructured arrow of the inclusion of schemes as algebraic spaces, so a morphism of such pairs
is a morphism of schemes together with the commutation with the two morphisms to the base —
exactly the datum `f` of the source.  The base change `X_U` and the induced morphism
`X_f : X_U ⟶ X_{U'}` are `AlgebraicGeometry.Space.baseChangeSpace` and
`AlgebraicGeometry.Space.baseChangeMap`; the second is the morphism *induced by the universal
property*, so `AlgebraicGeometry.Space.baseChangeMap_comp` is an honest equality of morphisms
and no cartesian-square condition has to be carried in the morphism structure.  The source
writes the base change as `U ×_{b, B} X` and this development as `X ×_B U`; the two differ by
the symmetry of a fibre product, and the second is the convention already fixed by
`AlgebraicGeometry.Space.PicardSituation` of Stacks 0D25.

## Main definitions

* `AlgebraicGeometry.Space.baseChangeMapComparison`,
  `AlgebraicGeometry.Space.baseChangeIdComparison` and
  `AlgebraicGeometry.Space.baseChangeCompComparison`: the comparisons of Stacks 03LU for the
  morphisms of base changes induced by an equality of base maps, by an identity and by a
  composite.
* `AlgebraicGeometry.Space.PicardObject` and `AlgebraicGeometry.Space.PicardHom`: **Section
  0372**, the objects and the morphisms of `Picardstack_{X/B}`.
* `AlgebraicGeometry.Space.PicardHom.id` and `AlgebraicGeometry.Space.PicardHom.comp`:
  **Section 0372**, the identities and the composition.
* `AlgebraicGeometry.Space.PicardCategoryData`: the *specification* of the category
  `Picardstack_{X/B}` of Section 0372 together with its projection to the test schemes over the
  base, pinning its hom-sets, identities, composition and projection to the four pieces of data
  above.

## Main results

* `AlgebraicGeometry.Space.baseChangeIdComparison_comp_fac`,
  `AlgebraicGeometry.Space.baseChangeComp_idComparison_fac` and
  `AlgebraicGeometry.Space.baseChangeCompComparison_assoc`: the unit laws and the associativity
  coherence of those comparisons.  They are exactly the input the three category laws of
  `Picardstack_{X/B}` need.
* `AlgebraicGeometry.Space.PicardHom.ext`: a morphism is determined by its base map and its
  comparison of modules.

## Implementation notes

**What is here and what is not.**  The objects, the morphisms, the identities and the
composition are the data of Section 0372 and they are unconditional except for the identity,
which is the unit law of Stacks 03LU.  The three *category laws* are not verified here, and
therefore neither is the category, nor the functor `p` of the section, nor the groupoid
structure of its fibre categories.  The laws reduce, through the composition calculus
`CategoryTheory.Functor.fibreComp` of
`StacksFrontier/AlgebraicGeometry/Quot/CoherentStack.lean` and the three coherences above, to
`CategoryTheory.Functor.fibreComp_id_left`, `CategoryTheory.Functor.fibreComp_id_right` and
`CategoryTheory.Functor.fibreComp_assoc`, and that reduction elaborates; what does not finish is
the *kernel's* check of the resulting proof terms, which is the behaviour the implementation
notes of
`StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleModulePushforwardCoherence.lean` record for any
statement that projects the underlying morphism of one of these comparisons.  The three
coherences are stated and proved here so that a later proof of the laws needs nothing further
about the comparisons themselves.

**The category is therefore specified rather than constructed.**  Section 0372 names
`Picardstack_{X/B}` a category by designation and verifies nothing, so what is recorded here is
`AlgebraicGeometry.Space.PicardCategoryData`: a category structure on the objects, a projection
to the test schemes over the base, and the identifications of its hom-sets, identities,
composition and projection with `AlgebraicGeometry.Space.PicardHom`,
`AlgebraicGeometry.Space.PicardHom.id` and `AlgebraicGeometry.Space.PicardHom.comp`.  No value
of it is constructed.  Because those identifications pin all four pieces of data, a statement
about `AlgebraicGeometry.Space.PicardCategoryData.projection` is a statement about the functor
`p` of the source and not about some other functor on the same objects.  This is the same device
as `AlgebraicGeometry.Space.CoherentCategoryData` of
`StacksFrontier/AlgebraicGeometry/Quot/CoherentStack.lean`, whose category of Stacks 08KB is
introduced by the source in the same way.

**Why the comparisons are kept variable.**  The comparisons of Stacks 03LU contain
`CategoryTheory.eqToIso` factors, which is the source of the behaviour just described; every
statement about them here keeps the comparison a variable or is an equation between two
comparisons, never a projection of one.

**On `public import` of `StacksFrontier/AlgebraicGeometry/Quot/CoherentStack.lean`.**  The body of
`AlgebraicGeometry.Space.PicardHom.comp` *is* `CategoryTheory.Functor.fibreComp`, so that name
appears in this module's exposed interface and the import cannot be a plain one.  Writing the
body out instead and keeping the import private was tried and does not work: the rewrites by
`CategoryTheory.Functor.fibreComp_id_left` and its companions then have nothing to match, and
bridging the written-out form to the abstract one is an equality the kernel does not finish
checking.  That file records that this calculus "belongs in a file of its own"; this is its
second consumer, which is the case for extracting it.

**The comparisons are stated for a bare morphism of algebraic spaces.**  The three of them are
the ones `StacksFrontier/AlgebraicGeometry/Quot/CoherentStack.lean` states for a
`AlgebraicGeometry.Space.CoherentSituation`, which carries a finite-presentation hypothesis that
nothing here has; they are restated for a bare `f : X ⟶ Y` and
`AlgebraicGeometry.Space.SchemesOver`, which is strictly more general and subsumes those.  Their
right home is beside `AlgebraicGeometry.Space.baseChangeMap` in
`StacksFrontier/AlgebraicGeometry/Quot/RelativeHom.lean`.

**Universes.**  An invertible module on the small étale site of an algebraic space is a
`AlgebraicGeometry.Space.Modules.{u, u}`, as it is in
`StacksFrontier/AlgebraicGeometry/Quot/PicardFunctor.lean`, so the objects of `Picardstack_{X/B}`
form a type in `Type (u + 1)`; there is no second module universe to be polymorphic in.

## References

* [Stacks Project, Section 0372](https://stacks.math.columbia.edu/tag/0372)
* [Stacks Project, Tag 04WN](https://stacks.math.columbia.edu/tag/04WN)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 0D25](https://stacks.math.columbia.edu/tag/0D25)
* [Stacks Project, Tag 08KB](https://stacks.math.columbia.edu/tag/08KB)
-/
@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits


namespace AlgebraicGeometry.Space

universe u

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {X Y : AlgebraicSpaces B S hS}

/-! ### The comparisons of inverse images along morphisms of base changes -/

/-- The identification of the inverse images along the morphisms of base changes induced by
two equal morphisms of test schemes. -/
def baseChangeMapComparison (f : X ⟶ Y) {T T' : SchemesOver Y} {g g' : T ⟶ T'} (e : g = g') :
    modulePullback B S hS (baseChangeMap f g) ≅ modulePullback B S hS (baseChangeMap f g') :=
  eqToIso (congrArg (fun k : T ⟶ T' ↦ modulePullback B S hS (baseChangeMap f k)) e)

/-- The identification `(X_{𝟙 T})^* ≅ 𝟭`. -/
def baseChangeIdComparison (hc : ModulePushforwardCoherence B S hS) (f : X ⟶ Y)
    (T : SchemesOver Y) :
    modulePullback B S hS (baseChangeMap f (𝟙 T)) ≅
      𝟭 (Modules.{u, u} B S hS (baseChangeSpace f T).1 (baseChangeSpace f T).2) :=
  eqToIso (congrArg (modulePullback B S hS) (baseChangeMap_id f T)) ≪≫
    hc.modulePullbackIdIso (baseChangeSpace f T)

/-- The comparison `(X_{g ≫ g'})^* ≅ (X_{g'})^* ⋙ (X_g)^*`. -/
def baseChangeCompComparison (f : X ⟶ Y) {T T' T'' : SchemesOver Y} (g : T ⟶ T')
    (g' : T' ⟶ T'') :
    modulePullback B S hS (baseChangeMap f (g ≫ g')) ≅
      modulePullback B S hS (baseChangeMap f g') ⋙ modulePullback B S hS (baseChangeMap f g) :=
  modulePullbackTriangle B S hS (baseChangeMap_comp f g g').symm

/-- The comparison for a composite, written as the triangle comparison of `baseChangeMap_comp`. -/
private theorem baseChangeCompComparison_eq (f : X ⟶ Y) {T T' T'' : SchemesOver Y} (g : T ⟶ T')
    (g' : T' ⟶ T'') :
    baseChangeCompComparison f g g' =
      modulePullbackTriangle B S hS (baseChangeMap_comp f g g').symm := rfl

/-- The comparison for a composite whose first factor is an identity is the identity law. -/
theorem baseChangeIdComparison_comp_fac (hc : ModulePushforwardCoherence B S hS) (f : X ⟶ Y)
    {T T' : SchemesOver Y} (g : T ⟶ T') :
    baseChangeCompComparison f (𝟙 T) g ≪≫
        Functor.isoWhiskerLeft (modulePullback B S hS (baseChangeMap f g))
          (baseChangeIdComparison hc f T) ≪≫
        Functor.rightUnitor (modulePullback B S hS (baseChangeMap f g)) =
      baseChangeMapComparison f (Category.id_comp g) := by
  have hff : baseChangeMap f (𝟙 T) = 𝟙 (baseChangeSpace f T) := baseChangeMap_id f T
  have hk : baseChangeMap f (𝟙 T) ≫ baseChangeMap f g = baseChangeMap f (𝟙 T ≫ g) :=
    (baseChangeMap_comp f (𝟙 T) g).symm
  have hk1 : 𝟙 (baseChangeSpace f T) ≫ baseChangeMap f g = baseChangeMap f (𝟙 T ≫ g) := by
    rw [← hff]; exact hk
  have hkk : baseChangeMap f (𝟙 T ≫ g) = baseChangeMap f g :=
    congrArg (baseChangeMap f) (Category.id_comp g)
  have hk2 : 𝟙 (baseChangeSpace f T) ≫ baseChangeMap f g = baseChangeMap f g :=
    Category.id_comp _
  rw [baseChangeCompComparison_eq, modulePullbackTriangle_congr_left hff hk hk1,
    modulePullbackTriangle_congr hk1 hk2 hkk, modulePullbackTriangle_eq hk2,
    hc.modulePullbackCompIso_id_left (baseChangeMap f g)]
  simp only [baseChangeIdComparison]
  rw [Functor.isoWhiskerLeft_trans]
  simp only [← Iso.trans_assoc, Functor.trans_isoWhiskerLeft_trans, eqToIso_trans, eqToIso_refl,
    Iso.refl_trans, Iso.trans_refl, Functor.isoWhiskerLeft_refl, baseChangeMapComparison]
  simp only [Iso.trans_assoc, Iso.symm_self_id, Iso.trans_refl]

/-- The comparison for a composite whose second factor is an identity is the identity law. -/
theorem baseChangeComp_idComparison_fac (hc : ModulePushforwardCoherence B S hS) (f : X ⟶ Y)
    {T T' : SchemesOver Y} (g : T ⟶ T') :
    baseChangeCompComparison f g (𝟙 T') ≪≫
        Functor.isoWhiskerRight (baseChangeIdComparison hc f T')
          (modulePullback B S hS (baseChangeMap f g)) ≪≫
        Functor.leftUnitor (modulePullback B S hS (baseChangeMap f g)) =
      baseChangeMapComparison f (Category.comp_id g) := by
  have hff : baseChangeMap f (𝟙 T') = 𝟙 (baseChangeSpace f T') := baseChangeMap_id f T'
  have hk : baseChangeMap f g ≫ baseChangeMap f (𝟙 T') = baseChangeMap f (g ≫ 𝟙 T') :=
    (baseChangeMap_comp f g (𝟙 T')).symm
  have hk1 : baseChangeMap f g ≫ 𝟙 (baseChangeSpace f T') = baseChangeMap f (g ≫ 𝟙 T') := by
    rw [← hff]; exact hk
  have hkk : baseChangeMap f (g ≫ 𝟙 T') = baseChangeMap f g :=
    congrArg (baseChangeMap f) (Category.comp_id g)
  have hk2 : baseChangeMap f g ≫ 𝟙 (baseChangeSpace f T') = baseChangeMap f g :=
    Category.comp_id _
  rw [baseChangeCompComparison_eq, modulePullbackTriangle_congr_right hff hk hk1,
    modulePullbackTriangle_congr hk1 hk2 hkk, modulePullbackTriangle_eq hk2,
    hc.modulePullbackCompIso_id_right (baseChangeMap f g)]
  apply Iso.ext
  ext M
  simp [baseChangeIdComparison, baseChangeMapComparison]

/-- The associativity coherence of the comparisons. -/
theorem baseChangeCompComparison_assoc (hc : ModulePushforwardCoherence B S hS) (f : X ⟶ Y)
    {T T' T'' T''' : SchemesOver Y} (g : T ⟶ T') (g' : T' ⟶ T'') (g'' : T'' ⟶ T''') :
    baseChangeCompComparison f (g ≫ g') g'' ≪≫
        Functor.isoWhiskerLeft (modulePullback B S hS (baseChangeMap f g''))
          (baseChangeCompComparison f g g') =
      baseChangeMapComparison f (Category.assoc g g' g'') ≪≫
        baseChangeCompComparison f g (g' ≫ g'') ≪≫
        Functor.isoWhiskerRight (baseChangeCompComparison f g' g'')
          (modulePullback B S hS (baseChangeMap f g)) ≪≫
        Functor.associator (modulePullback B S hS (baseChangeMap f g''))
          (modulePullback B S hS (baseChangeMap f g'))
          (modulePullback B S hS (baseChangeMap f g)) := by
  have hk : baseChangeMap f g ≫ baseChangeMap f g' = baseChangeMap f (g ≫ g') :=
    (baseChangeMap_comp f g g').symm
  have hq : baseChangeMap f g' ≫ baseChangeMap f g'' = baseChangeMap f (g' ≫ g'') :=
    (baseChangeMap_comp f g' g'').symm
  have hkr : baseChangeMap f (g ≫ g') ≫ baseChangeMap f g'' =
      baseChangeMap f ((g ≫ g') ≫ g'') := (baseChangeMap_comp f (g ≫ g') g'').symm
  have hr' : baseChangeMap f g ≫ baseChangeMap f (g' ≫ g'') =
      baseChangeMap f (g ≫ g' ≫ g'') := (baseChangeMap_comp f g (g' ≫ g'')).symm
  have hrr : baseChangeMap f ((g ≫ g') ≫ g'') = baseChangeMap f (g ≫ g' ≫ g'') :=
    congrArg (baseChangeMap f) (Category.assoc g g' g'')
  have hr : baseChangeMap f g ≫ baseChangeMap f (g' ≫ g'') =
      baseChangeMap f ((g ≫ g') ≫ g'') := hr'.trans hrr.symm
  rw [baseChangeCompComparison_eq f (g ≫ g') g'', baseChangeCompComparison_eq f g g',
    baseChangeCompComparison_eq f g' g'', baseChangeCompComparison_eq f g (g' ≫ g''),
    hc.modulePullbackTriangle_comp hk hq hr hkr,
    modulePullbackTriangle_congr hr hr' hrr, Iso.trans_assoc]
  rfl

/-! ### The Picard category -/

/-- **Section 0372, the objects of `Picardstack_{X/B}`.**  A triple `(U, b, L)`: a scheme `U` of
the site with a morphism `b : U ⟶ B` to the base, and an invertible module `L` on the base
change `X_U`. -/
@[stacks 0372 "the objects of the Picard stack"]
structure PicardObject (s : PicardSituation B S hS) where
  /-- The test scheme together with its morphism to the base: the pair `(U, b)`. -/
  T : s.SchemesOver
  /-- The invertible module on the base change `X_U`. -/
  lineBundle : Modules.{u, u} B S hS (s.baseChange T).1 (s.baseChange T).2
  /-- It is invertible. -/
  invertible : IsInvertibleModule (s.baseChange T) lineBundle

/-- **Section 0372, the morphisms of `Picardstack_{X/B}`.**  A pair `(f, g)`: a morphism
`f : U ⟶ U'` of schemes over the base, and an isomorphism `g : f^*L' ⟶ L` of modules on
`X_U`. -/
@[stacks 0372 "the morphisms of the Picard stack"]
structure PicardHom {s : PicardSituation B S hS} (A C : PicardObject s) where
  /-- The morphism `f : U ⟶ U'` of test schemes over the base. -/
  base : A.T ⟶ C.T
  /-- The isomorphism `g : f^*L' ⟶ L`. -/
  fibre : (modulePullback B S hS (baseChangeMap s.f base)).obj C.lineBundle ⟶ A.lineBundle
  /-- It is an isomorphism. -/
  isIso_fibre : IsIso fibre

namespace PicardHom

variable {s : PicardSituation B S hS} {A C D E : PicardObject s}

attribute [instance] isIso_fibre

/-- Two morphisms with the same base map and the same comparison are equal. -/
@[ext (iff := false)]
theorem ext {m n : PicardHom A C} (hbase : m.base = n.base)
    (hfibre : eqToHom (by rw [hbase]) ≫ m.fibre = n.fibre) : m = n := by
  obtain ⟨mb, mf, mi⟩ := m
  obtain ⟨nb, nf, ni⟩ := n
  change mb = nb at hbase
  subst hbase
  simp only [eqToHom_refl, Category.id_comp] at hfibre
  subst hfibre
  rfl

/-- **Section 0372, the identity of an object.**  The identity of its pair `(U, b)`, with the
unit law `(X_{𝟙 U})^* ≅ 𝟭` of Stacks 03LU as its comparison of modules. -/
@[stacks 0372 "the identity, conditional on the pseudofunctoriality of the direct images of \
Stacks 03LU"]
def id (hc : ModulePushforwardCoherence B S hS) (A : PicardObject s) : PicardHom A A where
  base := 𝟙 A.T
  fibre := (baseChangeIdComparison hc s.f A.T).hom.app A.lineBundle
  isIso_fibre := inferInstance

/-- **Section 0372, the composition `(f, g)` with `(f', g')` is `(f' ∘ f, g ∘ f^*(g'))`.**  The
composite of the base maps, with the inverse image of the second comparison followed by the
first, read through the comparison of Stacks 03LU for the composite. -/
@[stacks 0372 "the composition"]
def comp (m : PicardHom A C) (n : PicardHom C D) : PicardHom A D where
  base := m.base ≫ n.base
  fibre := Functor.fibreComp (baseChangeCompComparison s.f m.base n.base) m.fibre n.fibre
  isIso_fibre := by
    have h : IsIso ((baseChangeCompComparison s.f m.base n.base).hom.app D.lineBundle ≫
      (modulePullback B S hS (baseChangeMap s.f m.base)).map n.fibre ≫ m.fibre) := inferInstance
    exact h

end PicardHom

/-! ### The category and its projection -/

/-- The category structure on the objects of `Picardstack_{X/B}` together with its projection to
the test schemes over the base, and the identification of its hom-sets, identities, composition
and projection with `AlgebraicGeometry.Space.PicardHom`,
`AlgebraicGeometry.Space.PicardHom.id` and `AlgebraicGeometry.Space.PicardHom.comp`.

Bundling the category with those identifications is what makes it the category of Section 0372
rather than some category on the same objects. -/
structure PicardCategoryData (hc : ModulePushforwardCoherence B S hS)
    (s : PicardSituation B S hS) where
  /-- The category structure on the objects. -/
  category : Category.{u + 1} (PicardObject s)
  /-- The projection to the test schemes over the base. -/
  projection : letI : Category.{u + 1} (PicardObject s) := category
    PicardObject s ⥤ s.SchemesOver
  /-- The hom-sets are the pairs of a base map and a comparison of invertible modules. -/
  hom_type : letI : Category.{u + 1} (PicardObject s) := category
    ∀ A C : PicardObject s, (A ⟶ C) = PicardHom A C
  /-- The identity is the one of `AlgebraicGeometry.Space.PicardHom.id`. -/
  identity : letI : Category.{u + 1} (PicardObject s) := category
    ∀ A : PicardObject s, (Equiv.cast (hom_type A A)) (𝟙 A) = PicardHom.id hc A
  /-- Composition is the one of `AlgebraicGeometry.Space.PicardHom.comp`. -/
  composition : letI : Category.{u + 1} (PicardObject s) := category
    ∀ {A C D : PicardObject s} (m : A ⟶ C) (n : C ⟶ D),
      (Equiv.cast (hom_type A D)) (m ≫ n) =
        PicardHom.comp ((Equiv.cast (hom_type A C)) m) ((Equiv.cast (hom_type C D)) n)
  /-- The projection forgets the invertible module. -/
  projection_obj : ∀ A : PicardObject s, projection.obj A = A.T
  /-- The projection acts on morphisms by taking the base map. -/
  projection_map : letI : Category.{u + 1} (PicardObject s) := category
    ∀ {A C : PicardObject s} (m : A ⟶ C),
      projection.map m = eqToHom (projection_obj A) ≫
        ((Equiv.cast (hom_type A C)) m).base ≫ eqToHom (projection_obj C).symm

end AlgebraicGeometry.Space

end
