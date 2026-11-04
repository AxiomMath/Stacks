module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposPullbackUnit
public import StacksFrontier.AlgebraicGeometry.Quot.PicardStack
public import StacksFrontier.AlgebraicGeometry.Quot.PicardStackSection

/-!
# Descent for the Picard stack rigidified by a section (Stacks 0D29)

Let `f : X ⟶ B` be a morphism of algebraic spaces over a scheme `S` of a big fppf site, the
standing data of Stacks 0D25, and let `σ : B ⟶ X` be a section of `f`.  Every test scheme `T`
over the base inherits a section `σ_T : T ⟶ X_T` of the projection of the base change, and the
*rigidified Picard category* `Picardstack_{X/B, σ}` has as its objects the quadruples
`(T, h, L, α)` with `(T, h, L)` an object of `Picardstack_{X/B}` and `α : 𝒪_T ≅ σ_T^*L` a
trivialisation of the restriction of `L` along the section, and as its morphisms those morphisms
`(g, φ)` of `Picardstack_{X/B}` which satisfy `σ_T^*φ ∘ g^*α' = α`.  Forgetting the
trivialisation is a faithful functor to `Picardstack_{X/B}`.  Stacks 0D29 asserts that this
category is a stack in groupoids over the big fppf site.

This file carries the data of that assertion and the restriction of homomorphisms of modules
used to glue trivialisations; the stack condition itself is
`AlgebraicGeometry.Space.sectionedPicardCFG_isStackInGroupoids` of
`StacksFrontier/AlgebraicGeometry/Quot/PicardStackSectionedIsStack.lean`.  The section `σ_T` itself
and the structure sheaf as a module are taken from
`StacksFrontier/AlgebraicGeometry/Quot/PicardStackSection.lean`, where they are introduced for
Stacks 0D2B; what is added here is the comparison of inverse images along the section square,
the objects and morphisms of the rigidified category, and the inverse image of an object along a
morphism of test schemes.

## Main definitions

* `AlgebraicGeometry.Space.structureModulePullbackIso`: the identification `𝒪_W ≅ q^*𝒪_V` of the
  inverse image of a structure sheaf with the structure sheaf.
* `AlgebraicGeometry.Space.PicardSituation.sectionPullback`: the restriction `σ_T^*` of modules
  along the section of a base change.
* `AlgebraicGeometry.Space.PicardSituation.sectionSquareIso`: the comparison
  `σ_U^*(X_g)^* ≅ g^*σ_T^*` attached to a morphism `g : U ⟶ T` of test schemes.
* `AlgebraicGeometry.Space.PicardSituation.SectionedPicardObject`: **the objects
  `(T, h, L, α)` of `Picardstack_{X/B, σ}`**.
* `AlgebraicGeometry.Space.PicardSituation.transportTrivialization`,
  `AlgebraicGeometry.Space.PicardSituation.transportTrivializationIso` and
  `AlgebraicGeometry.Space.PicardSituation.SectionedPicardHom`: the trivialisation
  `σ_T^*φ ∘ g^*α'` transported along a morphism of `Picardstack_{X/B}`, the same composite read
  as an isomorphism, and **the morphisms of `Picardstack_{X/B, σ}`**, namely those morphisms of
  `Picardstack_{X/B}` for which the transported trivialisation is the given one.
* `AlgebraicGeometry.Space.PicardObject.pullback`,
  `AlgebraicGeometry.Space.PicardObject.pullbackHom` and
  `AlgebraicGeometry.Space.PicardSituation.SectionedPicardObject.pullback`: the inverse image of
  an object of `Picardstack_{X/B}` along a morphism of test schemes, the morphism of
  `Picardstack_{X/B}` it carries, and the inverse image of an object of
  `Picardstack_{X/B, σ}`, whose trivialisation is the transported one;
  `AlgebraicGeometry.Space.PicardSituation.SectionedPicardObject.pullbackSectionedHom` is the
  resulting morphism of `Picardstack_{X/B, σ}`.
* `AlgebraicGeometry.Space.moduleHomRefine`: the restriction of a homomorphism `q^*M ⟶ q^*N` of
  inverse images to a refinement `a ≫ q = k`, and
  `AlgebraicGeometry.Space.ModuleHomFamilyCompatible` the compatibility of a family of such
  homomorphisms on common refinements.
* `AlgebraicGeometry.Space.ModuleHomFppfDescent`: the assertion that homomorphisms of modules on
  the small étale site of a scheme of the site satisfy the sheaf condition for fppf covering
  families, which is the form in which the proof of Stacks 0D29 uses Descent,
  Proposition 023T.
* `AlgebraicGeometry.Space.PicardSituation.trivializationHom`: a trivialisation of the inverse
  image of an object of `Picardstack_{X/B}` along a morphism `g` of test schemes, read through
  the two comparisons as a homomorphism of the inverse images along `g` of `𝒪_T` and of
  `σ_T^*L`.

## Main results

* `AlgebraicGeometry.Space.PicardSituation.baseChangeSection_naturality`: the commuting section
  square `σ_U ≫ X_g = g ≫ σ_T` for a morphism `g` of test schemes.
* `AlgebraicGeometry.Space.PicardSituation.SectionedPicardHom.toPicardHom_injective`: **the
  functor forgetting the trivialisation is faithful**, the assertion made by the source when
  `Picardstack_{X/B, σ}` is introduced.
* `AlgebraicGeometry.Space.PicardSituation.SectionedPicardObject`'s
  `transportTrivialization_pullbackHom`: the inverse image of an object of
  `Picardstack_{X/B, σ}` along a morphism of test schemes is compatible with the
  trivialisations, so the morphism of `Picardstack_{X/B}` it carries is a morphism of
  `Picardstack_{X/B, σ}`.
* `AlgebraicGeometry.Space.moduleHomRefine_comp`,
  `AlgebraicGeometry.Space.moduleHomRefine_id`,
  `AlgebraicGeometry.Space.moduleHomRefine_inv` and
  `AlgebraicGeometry.Space.moduleHomRefine_map`: restriction to a refinement is compatible with
  composition, carries identities to identities and inverses to inverses, and does not change a
  homomorphism that is already the inverse image of one defined on the target.
* `AlgebraicGeometry.Space.ModuleHomFppfDescent.injective`: restriction along an fppf covering
  family is injective on homomorphisms of modules — the uniqueness half of the descent
  hypothesis.

## Implementation notes

**What is reused.**  The section `σ_T` is
`AlgebraicGeometry.Space.PicardSituation.baseChangeSection` and the structure sheaf as a module
is `AlgebraicGeometry.Space.structureModule`, both from
`StacksFrontier/AlgebraicGeometry/Quot/PicardStackSection.lean`, together with the two projection
identities `AlgebraicGeometry.Space.PicardSituation.baseChangeSection_comp_projection` and
`AlgebraicGeometry.Space.PicardSituation.baseChangeSection_comp_inclusion`, which are what the
section square below is proved from.  The objects and morphisms of `Picardstack_{X/B}` are
`AlgebraicGeometry.Space.PicardObject` and `AlgebraicGeometry.Space.PicardHom` of
`StacksFrontier/AlgebraicGeometry/Quot/PicardStack.lean`.

**Where the stack condition is proved.**  The source proves the stack condition for
`Picardstack_{X/B, σ}` in two steps.  Descent for objects it reduces to descent for objects for
`Picardstack_{X/B}` (Examples of Stacks, Lemma 04WN) followed by the gluing of the
trivialisations by Descent, Proposition 023T; descent for morphisms it omits.  Both steps are
carried out in `StacksFrontier/AlgebraicGeometry/Quot/PicardStackSectionedIsStack.lean`, whose
`AlgebraicGeometry.Space.sectionedPicardCFG_isStackInGroupoids` is Stacks 0D29; the gluing there
uses Proposition 023T for quasi-coherent modules,
`AlgebraicGeometry.Space.existsUnique_modulePullback_map_eq_of_moduleHomFamilyCompatible` of
`StacksFrontier/AlgebraicGeometry/Quot/PicardStackModuleHomDescent.lean`.  This file supplies the
data that argument is about and the restriction to a refinement it glues along.

**The predicate `AlgebraicGeometry.Space.ModuleHomFppfDescent`.**  It is Descent,
Proposition 023T — the sheaf condition for the presheaf of homomorphisms of modules — on the
small étale site of a scheme of the big fppf site, stated for *all* modules and only for families
of schemes of the site.  Its uniqueness half,
`AlgebraicGeometry.Space.ModuleHomFppfDescent.injective`, is derived here; for quasi-coherent
modules, the generality of the source, the statement is proved in
`StacksFrontier/AlgebraicGeometry/Quot/PicardStackModuleHomDescent.lean`.

**Where invertibility of inverse images enters.**
`AlgebraicGeometry.Space.modulePullbackInvertible` of
`StacksFrontier/AlgebraicGeometry/Quot/PicardFunctor.lean` is used here only to form the inverse
image of an *object* of `Picardstack_{X/B}`, whose module must stay invertible.  It is not
needed for the trivialisations themselves, nor for the restriction of homomorphisms.

**The two comparisons.**  Typing `σ_T^*φ ∘ g^*α' = α` needs an identification of `g^*𝒪_{T'}`
with `𝒪_T` and an identification of `σ_T^*(X_g)^*L'` with `g^*σ_{T'}^*L'`.  The first is
`AlgebraicGeometry.Space.structureModulePullbackIso`, the inverse image of the structure sheaf
along a morphism of ringed topoi of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/RingedToposPullbackUnit.lean`, read at the
morphism of small étale ringed topoi; the second is
`AlgebraicGeometry.Space.PicardSituation.sectionSquareIso`, the comparison of Stacks 03LU for
the two sides of the commuting square `σ_U ≫ X_g = g ≫ σ_T`, which is *proved* here from the
defining projections of `X_U ⟶ X_T`, so that a morphism of `Picardstack_{X/B, σ}` carries no
comparison data beyond that of a morphism of `Picardstack_{X/B}`.

**Gluing isomorphisms.**  Descent of homomorphisms glues *homomorphisms*, so a trivialisation
glued from local ones has to be shown invertible.  That is where uniqueness is used: the inverses
of the local trivialisations are again a compatible family
(`AlgebraicGeometry.Space.ModuleHomFamilyCompatible.inv`), their glueing is a homomorphism the
other way, and the two composites agree with the identity on the covering family, hence are the
identity.  Compatibility of the inverses, in turn, comes from restriction to a refinement being
compatible with composition and identities, which is
`CategoryTheory.Functor.conjHom` read at the comparison of Stacks 03LU.

**Universes.**  An invertible module on the small étale site of an algebraic space is an
`AlgebraicGeometry.Space.Modules.{u, u}`, as in
`StacksFrontier/AlgebraicGeometry/Quot/PicardStack.lean`, so there is no second module universe to
be polymorphic in; the covering families of `AlgebraicGeometry.Space.ModuleHomFppfDescent` are
indexed by a type in the universe `u` of the schemes, which is the indexing the big fppf site
uses.

## References

* [Stacks Project, Tag 0D29](https://stacks.math.columbia.edu/tag/0D29)
* [Stacks Project, Tag 0D25](https://stacks.math.columbia.edu/tag/0D25)
* [Stacks Project, Tag 04WN](https://stacks.math.columbia.edu/tag/04WN)
* [Stacks Project, Tag 023T](https://stacks.math.columbia.edu/tag/023T)
* [Stacks Project, Tag 0372](https://stacks.math.columbia.edu/tag/0372)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 0D27](https://stacks.math.columbia.edu/tag/0D27)
* [Stacks Project, Tag 0B8P](https://stacks.math.columbia.edu/tag/0B8P)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Space

universe u

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-! ### The inverse image of a structure sheaf -/

/-- **The inverse image of a structure sheaf is the structure sheaf**: for a morphism
`q : W ⟶ V` of algebraic spaces the inverse image `q^*𝒪_V` of Stacks 03LU is canonically
isomorphic to `𝒪_W`.

This is `Stacks.Sheaves.RingedToposModules.pullbackModulesObjUnitIso` at the morphism of small
étale ringed topoi of `q`. -/
def structureModulePullbackIso {V W : AlgebraicSpaces B S hS} (q : W ⟶ V) :
    structureModule W ≅ (modulePullback B S hS q).obj (structureModule V) :=
  Stacks.Sheaves.RingedToposModules.pullbackModulesObjUnitIso
    (smallEtaleRingedToposModulesHom B S hS q)

/-! ### The section square and the restriction along the section -/

namespace PicardSituation

variable {s : PicardSituation B S hS} (σ : s.base ⟶ s.X) (hσ : σ ≫ s.f = 𝟙 s.base)

/-- **The section square commutes**: for a morphism `g : U ⟶ T` of test schemes over the base,
the induced morphism `X_g : X_U ⟶ X_T` of base changes satisfies `σ_U ≫ X_g = g ≫ σ_T`. -/
theorem baseChangeSection_naturality {U T : s.SchemesOver} (g : U ⟶ T) :
    baseChangeSection σ hσ U ≫ baseChangeMap s.f g =
      (schemeSpaceFunctor B S hS).map g.left ≫ baseChangeSection σ hσ T := by
  refine baseChange_hom_ext s.f ?_ ?_
  · rw [Category.assoc, baseChangeMap_comp_projection, Category.assoc,
      baseChangeSection_comp_projection σ hσ, baseChangeSection_comp_projection σ hσ,
      ← Category.assoc, CostructuredArrow.w g]
  · simp

/-- **The restriction `σ_T^*` of modules along the section of a base change**: the inverse image
of `𝒪_{X_T}`-modules along `σ_T : T ⟶ X_T`. -/
abbrev sectionPullback (T : s.SchemesOver) :
    Modules.{u, u} B S hS (s.baseChange T).1 (s.baseChange T).2 ⥤
      Modules.{u, u} B S hS (s.baseSpaceAt T).1 (s.baseSpaceAt T).2 :=
  modulePullback B S hS (baseChangeSection σ hσ T)

/-- **The comparison `σ_U^*(X_g)^* ≅ g^*σ_T^*`** attached to a morphism `g : U ⟶ T` of test
schemes over the base: the comparison of Stacks 03LU for the two sides of the commuting section
square `σ_U ≫ X_g = g ≫ σ_T`. -/
def sectionSquareIso {U T : s.SchemesOver} (g : U ⟶ T) :
    modulePullback B S hS (baseChangeMap s.f g) ⋙ sectionPullback σ hσ U ≅
      sectionPullback σ hσ T ⋙
        modulePullback B S hS ((schemeSpaceFunctor B S hS).map g.left) :=
  modulePullbackSquare B S hS (baseChangeSection_naturality σ hσ g) rfl

/-! ### The objects and morphisms of the rigidified Picard category -/

/-- **The objects of `Picardstack_{X/B, σ}`.**  A quadruple `(T, h, L, α)`: an object
`(T, h, L)` of `Picardstack_{X/B}` together with a trivialisation `α : 𝒪_T ≅ σ_T^*L` of the
restriction of its invertible module along the section of the base change. -/
structure SectionedPicardObject where
  /-- The underlying triple `(T, h, L)` of `Picardstack_{X/B}`. -/
  toPicardObject : PicardObject s
  /-- The trivialisation `α : 𝒪_T ≅ σ_T^*L` along the section. -/
  trivialization : structureModule (s.baseSpaceAt toPicardObject.T) ≅
    (sectionPullback σ hσ toPicardObject.T).obj toPicardObject.lineBundle

end PicardSituation

namespace PicardSituation

variable {s : PicardSituation B S hS} {σ : s.base ⟶ s.X} {hσ : σ ≫ s.f = 𝟙 s.base}

/-- The test scheme over the base that an object of `Picardstack_{X/B, σ}` lies over. -/
abbrev SectionedPicardObject.testScheme (A : SectionedPicardObject σ hσ) : s.SchemesOver :=
  A.toPicardObject.T

/-- **The trivialisation `σ_T^*φ ∘ g^*α'` transported along a morphism of
`Picardstack_{X/B}`.**  For a morphism `(g, φ) : (T, h, L) ⟶ (T', h', L')` of
`Picardstack_{X/B}` and a trivialisation `α'` of `L'` along `σ_{T'}`, the composite of the
identification `𝒪_T ≅ g^*𝒪_{T'}`, the inverse image `g^*α'`, the comparison
`g^*σ_{T'}^*L' ≅ σ_T^*(X_g)^*L'` and the restriction `σ_T^*φ` of the comparison of modules. -/
def transportTrivialization {A C : PicardObject s} (m : PicardHom A C)
    (α : structureModule (s.baseSpaceAt C.T) ⟶ (sectionPullback σ hσ C.T).obj C.lineBundle) :
    structureModule (s.baseSpaceAt A.T) ⟶ (sectionPullback σ hσ A.T).obj A.lineBundle :=
  (structureModulePullbackIso ((schemeSpaceFunctor B S hS).map m.base.left)).hom ≫
    (modulePullback B S hS ((schemeSpaceFunctor B S hS).map m.base.left)).map α ≫
    (sectionSquareIso σ hσ m.base).inv.app C.lineBundle ≫
    (sectionPullback σ hσ A.T).map m.fibre

/-- **The transported trivialisation of a trivialisation is again a trivialisation**: the same
composite as `AlgebraicGeometry.Space.PicardSituation.transportTrivialization`, with every
factor read as an isomorphism, the comparison of modules of a morphism of `Picardstack_{X/B}`
being invertible. -/
def transportTrivializationIso {A C : PicardObject s} (m : PicardHom A C)
    (α : structureModule (s.baseSpaceAt C.T) ≅ (sectionPullback σ hσ C.T).obj C.lineBundle) :
    structureModule (s.baseSpaceAt A.T) ≅ (sectionPullback σ hσ A.T).obj A.lineBundle :=
  structureModulePullbackIso ((schemeSpaceFunctor B S hS).map m.base.left) ≪≫
    (modulePullback B S hS ((schemeSpaceFunctor B S hS).map m.base.left)).mapIso α ≪≫
    ((sectionSquareIso σ hσ m.base).app C.lineBundle).symm ≪≫
    (sectionPullback σ hσ A.T).mapIso (asIso m.fibre)

/-- The isomorphism of `AlgebraicGeometry.Space.PicardSituation.transportTrivializationIso` has
`AlgebraicGeometry.Space.PicardSituation.transportTrivialization` as its underlying
homomorphism. -/
theorem transportTrivializationIso_hom {A C : PicardObject s} (m : PicardHom A C)
    (α : structureModule (s.baseSpaceAt C.T) ≅ (sectionPullback σ hσ C.T).obj C.lineBundle) :
    (transportTrivializationIso (σ := σ) (hσ := hσ) m α).hom =
      transportTrivialization (σ := σ) (hσ := hσ) m α.hom :=
  rfl

/-- **The morphisms of `Picardstack_{X/B, σ}`.**  A morphism `(g, φ)` of `Picardstack_{X/B}`
which is compatible with the chosen trivialisations, in the sense that the trivialisation it
transports from the target is the trivialisation of the source. -/
structure SectionedPicardHom (A C : SectionedPicardObject σ hσ) where
  /-- The underlying morphism `(g, φ)` of `Picardstack_{X/B}`. -/
  toPicardHom : PicardHom A.toPicardObject C.toPicardObject
  /-- The compatibility `σ_T^*φ ∘ g^*α' = α`. -/
  compatible :
    transportTrivialization toPicardHom C.trivialization.hom = A.trivialization.hom

namespace SectionedPicardHom

variable {A C : SectionedPicardObject σ hσ}

/-- A morphism of `Picardstack_{X/B, σ}` is determined by its underlying morphism of
`Picardstack_{X/B}`, the compatibility being a proposition. -/
@[ext (iff := false)]
theorem ext {m n : SectionedPicardHom A C} (h : m.toPicardHom = n.toPicardHom) : m = n := by
  cases m
  cases n
  subst h
  rfl

/-- **The forgetful map to `Picardstack_{X/B}` is injective on morphisms**: this is the
faithfulness of the functor forgetting the trivialisation, asserted by the source when
`Picardstack_{X/B, σ}` is introduced. -/
theorem toPicardHom_injective :
    Function.Injective (SectionedPicardHom.toPicardHom (A := A) (C := C)) :=
  fun _ _ h ↦ ext h

end SectionedPicardHom

end PicardSituation

/-! ### The inverse image of an object along a morphism of test schemes -/

namespace PicardObject

variable {s : PicardSituation B S hS}

/-- **The inverse image of an object of `Picardstack_{X/B}` along a morphism of test schemes**:
the triple whose test scheme is the source of the morphism and whose module is the inverse image
of the given one along the induced morphism `X_U ⟶ X_T` of base changes. -/
def pullback (A : PicardObject s) {U : s.SchemesOver} (g : U ⟶ A.T) : PicardObject s where
  T := U
  lineBundle := (modulePullback B S hS (baseChangeMap s.f g)).obj A.lineBundle
  invertible := modulePullbackInvertible _ _ A.invertible

/-- **The morphism of `Picardstack_{X/B}` carried by an inverse image**: the given morphism of
test schemes, with the identity as its comparison of modules. -/
def pullbackHom (A : PicardObject s) {U : s.SchemesOver} (g : U ⟶ A.T) :
    PicardHom (A.pullback g) A where
  base := g
  fibre := 𝟙 _
  isIso_fibre := IsIso.id _

end PicardObject

namespace PicardSituation

variable {s : PicardSituation B S hS} {σ : s.base ⟶ s.X} {hσ : σ ≫ s.f = 𝟙 s.base}

namespace SectionedPicardObject

/-- **The inverse image of an object of `Picardstack_{X/B, σ}` along a morphism of test
schemes**: the inverse image of the triple, with the transported trivialisation of the morphism
of `Picardstack_{X/B}` that the inverse image carries. -/
def pullback (A : SectionedPicardObject σ hσ) {U : s.SchemesOver} (g : U ⟶ A.testScheme) :
    SectionedPicardObject σ hσ where
  toPicardObject := A.toPicardObject.pullback g
  trivialization :=
    transportTrivializationIso (A.toPicardObject.pullbackHom g) A.trivialization

/-- **The inverse image of an object of `Picardstack_{X/B, σ}` is compatible with the
trivialisations**, so the morphism of `Picardstack_{X/B}` it carries is a morphism of
`Picardstack_{X/B, σ}`. -/
theorem transportTrivialization_pullbackHom (A : SectionedPicardObject σ hσ)
    {U : s.SchemesOver} (g : U ⟶ A.testScheme) :
    transportTrivialization (A.toPicardObject.pullbackHom g) A.trivialization.hom =
      (A.pullback g).trivialization.hom :=
  (transportTrivializationIso_hom _ _).symm

/-- **The cartesian lift of an object of `Picardstack_{X/B, σ}` along a morphism of test
schemes**: the morphism of `Picardstack_{X/B, σ}` from the inverse image to the object. -/
def pullbackSectionedHom (A : SectionedPicardObject σ hσ) {U : s.SchemesOver}
    (g : U ⟶ A.testScheme) : SectionedPicardHom (A.pullback g) A where
  toPicardHom := A.toPicardObject.pullbackHom g
  compatible := A.transportTrivialization_pullbackHom g

end SectionedPicardObject

end PicardSituation

/-! ### Descent of trivialisations along a covering family -/

/-- Conjugating a composite of morphisms by a comparison of a functor with a composite is the
composite of the conjugates. -/
private theorem conjHom_comp_hom {C D₁ D₂ : Type*} [Category* C] [Category* D₁] [Category* D₂]
    {P₁ : C ⥤ D₁} {P₂ : C ⥤ D₂} {L : D₁ ⥤ D₂} (e : P₂ ≅ P₁ ⋙ L) {M N P : C}
    (v : P₁.obj M ⟶ P₁.obj N) (w : P₁.obj N ⟶ P₁.obj P) :
    Functor.conjHom e (v ≫ w) = Functor.conjHom e v ≫ Functor.conjHom e w := by
  simp [Functor.conjHom]

/-- Conjugating the inverse image of a homomorphism of modules by a comparison of a functor
with a composite is the inverse image of that homomorphism: the comparison is natural. -/
private theorem conjHom_map {C D₁ D₂ : Type*} [Category* C] [Category* D₁] [Category* D₂]
    {P₁ : C ⥤ D₁} {P₂ : C ⥤ D₂} {L : D₁ ⥤ D₂} (e : P₂ ≅ P₁ ⋙ L) {M N : C} (v : M ⟶ N) :
    Functor.conjHom e (P₁.map v) = P₂.map v := by
  simp [Functor.conjHom, ← Functor.comp_map, ← Category.assoc]

/-- **The restriction of a homomorphism of inverse images to a refinement.**  For a
factorisation `a ≫ q = k` of morphisms of algebraic spaces, a homomorphism `q^*M ⟶ q^*N`
restricts to a homomorphism `k^*M ⟶ k^*N`: its inverse image along `a`, read through the
comparison `k^* ≅ a^*q^*` of Stacks 03LU. -/
def moduleHomRefine {V W Z : AlgebraicSpaces B S hS} {a : W ⟶ V} {q : V ⟶ Z} {k : W ⟶ Z}
    (hk : a ≫ q = k) (M N : Modules.{u, u} B S hS Z.1 Z.2)
    (v : (modulePullback B S hS q).obj M ⟶ (modulePullback B S hS q).obj N) :
    (modulePullback B S hS k).obj M ⟶ (modulePullback B S hS k).obj N :=
  Functor.conjHom (modulePullbackTriangle B S hS hk) v

/-- Restriction to a refinement is compatible with composition of homomorphisms. -/
theorem moduleHomRefine_comp {V W Z : AlgebraicSpaces B S hS} {a : W ⟶ V} {q : V ⟶ Z}
    {k : W ⟶ Z} (hk : a ≫ q = k) (M N P : Modules.{u, u} B S hS Z.1 Z.2)
    (v : (modulePullback B S hS q).obj M ⟶ (modulePullback B S hS q).obj N)
    (w : (modulePullback B S hS q).obj N ⟶ (modulePullback B S hS q).obj P) :
    moduleHomRefine hk M P (v ≫ w) = moduleHomRefine hk M N v ≫ moduleHomRefine hk N P w :=
  conjHom_comp_hom _ v w

/-- Restriction to a refinement carries an identity to an identity. -/
theorem moduleHomRefine_id {V W Z : AlgebraicSpaces B S hS} {a : W ⟶ V} {q : V ⟶ Z}
    {k : W ⟶ Z} (hk : a ≫ q = k) (M : Modules.{u, u} B S hS Z.1 Z.2) :
    moduleHomRefine hk M M (𝟙 _) = 𝟙 _ :=
  by simpa [moduleHomRefine] using conjHom_map (modulePullbackTriangle B S hS hk) (𝟙 M)

/-- Restriction to a refinement carries an isomorphism to an isomorphism. -/
instance isIso_moduleHomRefine {V W Z : AlgebraicSpaces B S hS} {a : W ⟶ V} {q : V ⟶ Z}
    {k : W ⟶ Z} (hk : a ≫ q = k) (M N : Modules.{u, u} B S hS Z.1 Z.2)
    (v : (modulePullback B S hS q).obj M ⟶ (modulePullback B S hS q).obj N) [IsIso v] :
    IsIso (moduleHomRefine hk M N v) :=
  ⟨moduleHomRefine hk N M (inv v), by
    rw [← moduleHomRefine_comp, IsIso.hom_inv_id, moduleHomRefine_id], by
    rw [← moduleHomRefine_comp, IsIso.inv_hom_id, moduleHomRefine_id]⟩

/-- Restriction to a refinement carries the inverse of an isomorphism to the inverse of its
restriction. -/
theorem moduleHomRefine_inv {V W Z : AlgebraicSpaces B S hS} {a : W ⟶ V} {q : V ⟶ Z}
    {k : W ⟶ Z} (hk : a ≫ q = k) (M N : Modules.{u, u} B S hS Z.1 Z.2)
    (v : (modulePullback B S hS q).obj M ⟶ (modulePullback B S hS q).obj N) [IsIso v] :
    moduleHomRefine hk N M (inv v) = inv (moduleHomRefine hk M N v) :=
  IsIso.eq_inv_of_hom_inv_id <| by
    rw [← moduleHomRefine_comp, IsIso.hom_inv_id, moduleHomRefine_id]

/-- **The restriction of the inverse image of a homomorphism of modules is its inverse image**:
restriction to a refinement does not change a homomorphism that is already defined on the
target. -/
theorem moduleHomRefine_map {V W Z : AlgebraicSpaces B S hS} {a : W ⟶ V} {q : V ⟶ Z}
    {k : W ⟶ Z} (hk : a ≫ q = k) (M N : Modules.{u, u} B S hS Z.1 Z.2) (v : M ⟶ N) :
    moduleHomRefine hk M N ((modulePullback B S hS q).map v) =
      (modulePullback B S hS k).map v :=
  conjHom_map _ v

/-- **Compatibility of a family of homomorphisms of inverse images.**  For a family
`p i : W i ⟶ Z` of morphisms of algebraic spaces and homomorphisms `α i : p_i^*M ⟶ p_i^*N`, the
assertion that any two members agree after restriction to a common refinement: whenever
`a : Y ⟶ W i` and `b : Y ⟶ W j` satisfy `a ∘ p_i = b ∘ p_j`, the restrictions of `α i` along
`a` and of `α j` along `b` are the same homomorphism of inverse images along that common
composite. -/
def ModuleHomFamilyCompatible {Z : AlgebraicSpaces B S hS}
    (M N : Modules.{u, u} B S hS Z.1 Z.2) {ι : Type*} {W : ι → AlgebraicSpaces B S hS}
    (p : ∀ i, W i ⟶ Z)
    (α : ∀ i, (modulePullback B S hS (p i)).obj M ⟶ (modulePullback B S hS (p i)).obj N) :
    Prop :=
  ∀ (Y : AlgebraicSpaces B S hS) (i j : ι) (a : Y ⟶ W i) (b : Y ⟶ W j)
      (h : a ≫ p i = b ≫ p j),
    moduleHomRefine (a := a) (q := p i) (k := a ≫ p i) rfl M N (α i) =
      moduleHomRefine (a := b) (q := p j) (k := a ≫ p i) h.symm M N (α j)

/-- The family of identities is compatible. -/
theorem moduleHomFamilyCompatible_id {Z : AlgebraicSpaces B S hS}
    (M : Modules.{u, u} B S hS Z.1 Z.2) {ι : Type*} {W : ι → AlgebraicSpaces B S hS}
    (p : ∀ i, W i ⟶ Z) :
    ModuleHomFamilyCompatible M M p (fun i ↦ 𝟙 ((modulePullback B S hS (p i)).obj M)) :=
  fun _ _ _ _ _ _ ↦ (moduleHomRefine_id _ M).trans (moduleHomRefine_id _ M).symm

/-- The family of inverse images of a single homomorphism is compatible. -/
theorem moduleHomFamilyCompatible_map {Z : AlgebraicSpaces B S hS}
    (M N : Modules.{u, u} B S hS Z.1 Z.2) {ι : Type*} {W : ι → AlgebraicSpaces B S hS}
    (p : ∀ i, W i ⟶ Z) (v : M ⟶ N) :
    ModuleHomFamilyCompatible M N p
      (fun i ↦ (modulePullback B S hS (p i)).map v) :=
  fun _ _ _ _ _ _ ↦
    (moduleHomRefine_map _ M N v).trans (moduleHomRefine_map _ M N v).symm

/-- The family of inverses of a compatible family of isomorphisms is compatible. -/
theorem ModuleHomFamilyCompatible.inv {Z : AlgebraicSpaces B S hS}
    {M N : Modules.{u, u} B S hS Z.1 Z.2} {ι : Type*} {W : ι → AlgebraicSpaces B S hS}
    {p : ∀ i, W i ⟶ Z}
    {α : ∀ i, (modulePullback B S hS (p i)).obj M ⟶ (modulePullback B S hS (p i)).obj N}
    (hα : ModuleHomFamilyCompatible M N p α) (hiso : ∀ i, IsIso (α i)) :
    ModuleHomFamilyCompatible N M p (fun i ↦ CategoryTheory.inv (α i)) := by
  intro Y i j a b h
  have := hiso i
  have := hiso j
  rw [moduleHomRefine_inv, moduleHomRefine_inv, IsIso.inv_eq_inv]
  exact hα Y i j a b h

/-- **Descent of homomorphisms of modules along fppf covering families of test schemes:
Descent, Proposition 023T on the small étale sites of the schemes of the big fppf site.**  The
assertion that for a scheme `V` of the site, two `𝒪_V`-modules `M` and `N` on its small étale
site, and a family `r i : U i ⟶ V` of morphisms of schemes generating a covering sieve for the
fppf topology, every compatible family of homomorphisms `r_i^*M ⟶ r_i^*N` is the family of
restrictions of exactly one homomorphism `M ⟶ N`.

This is the full-faithfulness half of Descent, Proposition 023T.  See the implementation
notes: it is a theorem of the source and it is not proved in this development, where the
corresponding statement is available for `AlgebraicGeometry.Scheme.Modules` but not for the
modules on the small étale site of an algebraic space. -/
def ModuleHomFppfDescent (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) : Prop :=
  ∀ (V : BigFppfOver B S hS)
      (M N : Modules.{u, u} B S hS ((schemeSpaceFunctor B S hS).obj V).1
        ((schemeSpaceFunctor B S hS).obj V).2)
      (ι : Type u) (U : ι → BigFppfOver B S hS) (r : ∀ i, U i ⟶ V),
    Sieve.generate (Presieve.ofArrows U r) ∈ BigFppfOver.topology B S hS V →
    ∀ α : ∀ i, (modulePullback B S hS ((schemeSpaceFunctor B S hS).map (r i))).obj M ⟶
        (modulePullback B S hS ((schemeSpaceFunctor B S hS).map (r i))).obj N,
      ModuleHomFamilyCompatible M N (fun i ↦ (schemeSpaceFunctor B S hS).map (r i)) α →
      ∃! b : M ⟶ N, ∀ i,
        (modulePullback B S hS ((schemeSpaceFunctor B S hS).map (r i))).map b = α i

/-- **Restriction along an fppf covering family of test schemes is injective on homomorphisms of
modules.**  This is the uniqueness half of
`AlgebraicGeometry.Space.ModuleHomFppfDescent`, isolated: two homomorphisms with the same
restrictions to the members of a covering family are equal. -/
theorem ModuleHomFppfDescent.injective (hd : ModuleHomFppfDescent B S hS)
    (V : BigFppfOver B S hS)
    (M N : Modules.{u, u} B S hS ((schemeSpaceFunctor B S hS).obj V).1
      ((schemeSpaceFunctor B S hS).obj V).2)
    (ι : Type u) (U : ι → BigFppfOver B S hS) (r : ∀ i, U i ⟶ V)
    (hr : Sieve.generate (Presieve.ofArrows U r) ∈ BigFppfOver.topology B S hS V)
    (v w : M ⟶ N)
    (h : ∀ i, (modulePullback B S hS ((schemeSpaceFunctor B S hS).map (r i))).map v =
      (modulePullback B S hS ((schemeSpaceFunctor B S hS).map (r i))).map w) :
    v = w := by
  obtain ⟨e, -, hu⟩ := hd V M N ι U r hr
    (fun i ↦ (modulePullback B S hS ((schemeSpaceFunctor B S hS).map (r i))).map v)
    (moduleHomFamilyCompatible_map M N (fun i ↦ (schemeSpaceFunctor B S hS).map (r i)) v)
  exact (hu v fun _ ↦ rfl).trans (hu w fun i ↦ (h i).symm).symm

namespace PicardSituation

variable {s : PicardSituation B S hS} {σ : s.base ⟶ s.X} {hσ : σ ≫ s.f = 𝟙 s.base}

/-- The morphism of algebraic spaces underlying a morphism of test schemes over the base. -/
abbrev spaceMap {U T : s.SchemesOver} (g : U ⟶ T) : s.baseSpaceAt U ⟶ s.baseSpaceAt T :=
  (schemeSpaceFunctor B S hS).map g.left

/-- **A trivialisation of the inverse image of an object of `Picardstack_{X/B}`, read as a
homomorphism of inverse images along the morphism of test schemes.**  Its two comparisons are
the identification `𝒪_U ≅ g^*𝒪_T` of inverse images of structure sheaves and the comparison
`σ_U^*(X_g)^*L ≅ g^*σ_T^*L` of the section square. -/
def trivializationHom (A : PicardObject s) {U : s.SchemesOver} (g : U ⟶ A.T)
    (α : structureModule (s.baseSpaceAt U) ⟶
      (sectionPullback σ hσ U).obj
        ((modulePullback B S hS (baseChangeMap s.f g)).obj A.lineBundle)) :
    (modulePullback B S hS (spaceMap g)).obj (structureModule (s.baseSpaceAt A.T)) ⟶
      (modulePullback B S hS (spaceMap g)).obj
        ((sectionPullback σ hσ A.T).obj A.lineBundle) :=
  (structureModulePullbackIso (spaceMap g)).inv ≫ α ≫
    (sectionSquareIso σ hσ g).hom.app A.lineBundle

/-- The homomorphism attached to a trivialisation is an isomorphism. -/
instance isIso_trivializationHom (A : PicardObject s) {U : s.SchemesOver} (g : U ⟶ A.T)
    (α : structureModule (s.baseSpaceAt U) ⟶
      (sectionPullback σ hσ U).obj
        ((modulePullback B S hS (baseChangeMap s.f g)).obj A.lineBundle)) [IsIso α] :
    IsIso (trivializationHom (σ := σ) (hσ := hσ) A g α) := by
  rw [trivializationHom]
  infer_instance

end PicardSituation

end AlgebraicGeometry.Space

end
