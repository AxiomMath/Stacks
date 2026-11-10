module

public import StacksFrontier.Deformation.RingedSpaceThickening.TrivialExtension
public import StacksFrontier.Deformation.RingedSpaceThickening.TrivialSquareZeroThickening
import StacksCore.Tactic.StacksAttribute

/-!
# Trivialized first order thickenings of a ringed space (Stacks 08L9)

Let `(X, 𝒪_X)` be a ringed space. A first order thickening `i : (X, 𝒪_X) ⟶ (X', 𝒪_{X'})` is
*trivial* when `i` admits a retraction `π` in the category of ringed spaces, and such a `π` is
a *trivialization*. Given `π` the surjection `𝒪_{X'} ⟶ 𝒪_X` splits, so that

    𝒪_{X'} = 𝒪_X ⊕ ℐ

as sheaves of algebras on `X`, and conversely such a splitting determines `π`. Those three
clauses of the remark are
`AlgebraicGeometry.RingedSpaceThickening.structureSheafSplitEpi`,
`Deformation.RingThickening.splittingFromTrivialization` and
`Deformation.RingThickening.retractionFromSplitting`. This file proves the fourth and last:
the category of trivialized first order thickenings of `(X, 𝒪_X)` is equivalent to the
category of `𝒪_X`-modules.

## Main definitions

* `AlgebraicGeometry.RingedSpaceThickening.TrivializedThickening`: the category of trivialized
  first order thickenings of `(X, 𝒪_X)` — objects are a first order thickening `i : X ⟶ X'`
  together with a retraction of `i`, morphisms are morphisms `X'₁ ⟶ X'₂` of ringed spaces
  compatible with both the thickenings and the trivializations.
* `AlgebraicGeometry.RingedSpaceThickening.trivialThickeningObj` and
  `AlgebraicGeometry.RingedSpaceThickening.trivialThickeningFunctor`: the trivialized
  thickening `(X, 𝒪_X ⋉ 𝒢)` attached to an `𝒪_X`-module `𝒢`, and its functoriality.
* `AlgebraicGeometry.RingedSpaceThickening.trivializedIdeal`: the ideal `ℐ = Ker(i^♯)` of a
  trivialized thickening, read as an `𝒪_X`-module along the trivialization.
* `AlgebraicGeometry.RingedSpaceThickening.splittingMorphism`: **Stacks 08LA**, the splitting
  `𝒪_{X'} = 𝒪_X ⊕ ℐ` as a morphism of ringed spaces `X' ⟶ (X, 𝒪_X ⋉ ℐ)`.

## Main results

* `AlgebraicGeometry.RingedSpaceThickening.trivializedThickeningEquivalence`: **Stacks 08L9**,
  the category of trivialized first order thickenings of `(X, 𝒪_X)` is equivalent to the
  category of `𝒪_X`-modules.
* `AlgebraicGeometry.RingedSpaceThickening.trivialThickeningObjIso`: every trivialized first
  order thickening is isomorphic to the trivial square-zero extension of its ideal — the
  essential surjectivity half of the equivalence, and the content of the splitting.
* `AlgebraicGeometry.RingedSpaceThickening.moduleOfSqZeroExtMap`: the map of `𝒪_X`-modules
  underlying a morphism of trivial square-zero extensions — the fullness half.

## Variance

**The Hom of `TrivializedThickening X` runs in the geometric direction**: a morphism `A ⟶ B`
is a morphism `X'_A ⟶ X'_B` of *ringed spaces* over `(X, 𝒪_X)`, compatible with the
thickenings and the trivializations. That is the source's own convention: Stacks 08LD fixes a
morphism of trivialized first order thickenings of `(X, 𝒪_X)` to be a morphism
`h : (X'₁, 𝒪_{X'₁}) ⟶ (X'₂, 𝒪_{X'₂})` of ringed spaces with `π₂ ∘ h = π₁`, and Stacks 08LC
observes that `h^♯ : 𝒪_{X'₂} ⟶ 𝒪_{X'₁}` induces `ℐ₂ ⟶ ℐ₁` on the ideals.

So `𝒢 ↦ (X, 𝒪_X ⋉ 𝒢)` is *contravariant* for that convention, and the equivalence is stated as
`Mod(𝒪_X)ᵒᵖ ≌ TrivializedThickening X`. Since `Mod(𝒪_X)` is not equivalent to its opposite the
`ᵒᵖ` is not cosmetic: dropping it would state a false theorem. The same convention is already
in force in `StacksFrontier.Deformation.RingedSpaceThickening.TrivializedFunctoriality`, where a
morphism of trivialized thickenings `h : X'₁ ⟶ X'₂` induces `ℐ₂ ⟶ ℐ₁`. The remark's own
sentence says "equivalent" rather than "anti-equivalent"; with the morphisms the source itself
uses two remarks later, the anti-equivalence is what it asserts.

### Relation to the ringed topos form, Stacks 08MG

Stacks 08MG is this same remark for ringed topoi, and
`Deformation.ToposThickening.TrivializedThickening.moduleEquivalence`, in
`StacksFrontier/Deformation/ToposThickening/Trivialization/ModuleEquivalence.lean`, states it
*without* an `ᵒᵖ`:

    SheafOfModules (underlyingRingSheafOfSite O) ≌ TrivializedThickening O

**The two do not disagree, because the two categories use opposite Homs.** There is no category
of ringed topoi in this repo to take morphisms in — `AlgebraicGeometry.RingedToposHom.comp` has
no strict unit and associativity laws — so that file presents a trivialized thickening by its
structure sheaf `A` on the site and takes a morphism `T ⟶ S` to be a morphism `A_T ⟶ A_S` of
*sheaves of rings*, i.e. the direction of `h^♯`, opposite to the direction of `h` used here.
Its category is therefore the opposite of the source's, and `Mod(𝒪)ᵒᵖ ≌ 𝒯` and
`Mod(𝒪) ≌ 𝒯ᵒᵖ` are one statement. Neither file may be read as licence to drop or add an `ᵒᵖ`
in the other: the `ᵒᵖ` tracks the Hom direction, and the Hom directions differ.

## Implementation notes

The equivalence is proved by showing that `𝒢 ↦ (X, 𝒪_X ⋉ 𝒢)` is fully faithful and essentially
surjective, rather than by constructing an inverse functor: the ideal of a thickening lives on
`X'`, so a functor out of `TrivializedThickening X` would have to carry a module along `h_*`
for every morphism `h`, and the three spaces `X`, `X'₁`, `X'₂` have different sites.

Fullness and faithfulness are `Prop`s, so a morphism between two trivial square-zero extensions
can be destructured and its base map — which the compatibility with the thickenings forces to
be the identity — substituted, after which no transport along an identification of opens is
needed. Essential surjectivity does need one such transport, in
`AlgebraicGeometry.RingedSpaceThickening.thickening_comp_splittingMorphism`: the base map of
`i ≫ π` is the identity only propositionally, and
`AlgebraicGeometry.RingedSpaceThickening.ringedSpaceHom_ext'` is the form of
`AlgebraicGeometry.SheafedSpace.ext` that absorbs it.

Every computation inside a trivial square-zero extension is done over abstract data
(`AlgebraicGeometry.RingedSpaceThickening.sqZeroLift`,
`AlgebraicGeometry.RingedSpaceThickening.snd_apply` and the lemmas beside them) and applied in
term mode: the `TrivSqZeroExt` lemmas are stated for the instances of `TrivSqZeroExt R M`,
while a goal about sections carries the instances of the bundled `CommRingCat` object, and
`rw` cannot pass between the two even though the elaborator can.

## References

* [Stacks Project, Tag 08L9](https://stacks.math.columbia.edu/tag/08L9)
* [Stacks Project, Tag 08LA](https://stacks.math.columbia.edu/tag/08LA)
* [Stacks Project, Tag 08LC](https://stacks.math.columbia.edu/tag/08LC) — `h^♯` induces
  `ℐ₂ ⟶ ℐ₁`
* [Stacks Project, Tag 08LD](https://stacks.math.columbia.edu/tag/08LD) — what a morphism of
  trivialized first order thickenings is
* [Stacks Project, Tag 08MG](https://stacks.math.columbia.edu/tag/08MG) — the ringed topos form
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.Smooth
open scoped AlgebraicGeometry.SheafOfModules

attribute [local instance] Stacks.Smooth.moduleMulOpposite

universe u

namespace AlgebraicGeometry.RingedSpaceThickening

variable {X : RingedSpace.{u, u}}

/-- A *trivialized first order thickening* of a ringed space `(X, 𝒪_X)`: a first order
thickening `i : X ⟶ X'` together with a trivialization, that is, a retraction of `i` in the
category of ringed spaces. -/
structure TrivializedThickening (X : RingedSpace.{u, u}) where
  /-- The thickened ringed space `X'`. -/
  ambient : RingedSpace.{u, u}
  /-- The thickening `i : X ⟶ X'`. -/
  i : X ⟶ ambient
  /-- The trivialization: a retraction of `i`. -/
  trivialization : SplitMono i
  /-- The thickening is first order. -/
  isFirstOrder : IsFirstOrderThickening i

namespace TrivializedThickening

/-- A morphism of trivialized first order thickenings of `(X, 𝒪_X)`: a morphism of the
thickened spaces compatible with both the thickenings and the trivializations. It runs in the
geometric direction, that of `h` rather than of `h^♯`. -/
@[ext]
structure Hom (A B : TrivializedThickening X) where
  /-- The underlying morphism of ringed spaces. -/
  hom : A.ambient ⟶ B.ambient
  /-- It is a morphism of thickenings of `(X, 𝒪_X)`. -/
  i_comp : A.i ≫ hom = B.i
  /-- It is compatible with the trivializations. -/
  comp_retraction :
    hom ≫ B.trivialization.retraction = A.trivialization.retraction

attribute [reassoc] Hom.i_comp Hom.comp_retraction

/-- Trivialized first order thickenings of `(X, 𝒪_X)` form a category, with composition that of
the underlying morphisms of ringed spaces. -/
instance : Category (TrivializedThickening X) where
  Hom A B := Hom A B
  id A := ⟨𝟙 A.ambient, Category.comp_id _, Category.id_comp _⟩
  comp f g :=
    ⟨f.hom ≫ g.hom, by rw [← Category.assoc, f.i_comp, g.i_comp], by
      rw [Category.assoc, g.comp_retraction, f.comp_retraction]⟩

/-- The underlying morphism of the identity is the identity. -/
@[simp]
theorem id_hom (A : TrivializedThickening X) : (𝟙 A : A ⟶ A).hom = 𝟙 A.ambient := rfl

/-- The underlying morphism of a composite is the composite of the underlying morphisms. -/
@[simp]
theorem comp_hom {A B C : TrivializedThickening X} (f : A ⟶ B) (g : B ⟶ C) :
    (f ≫ g).hom = f.hom ≫ g.hom := rfl

/-- Two morphisms of trivialized thickenings with the same underlying morphism are equal. -/
@[ext]
theorem hom_ext {A B : TrivializedThickening X} {f g : A ⟶ B} (h : f.hom = g.hom) : f = g :=
  Hom.ext h

/-- A morphism of trivialized thickenings whose underlying morphism of ringed spaces is an
isomorphism is an isomorphism. -/
noncomputable def isoOfIsIso {A B : TrivializedThickening X} (f : A ⟶ B) [IsIso f.hom] :
    A ≅ B where
  hom := f
  inv :=
    ⟨inv f.hom, by rw [← f.i_comp, Category.assoc, IsIso.hom_inv_id, Category.comp_id], by
      rw [← f.comp_retraction, IsIso.inv_hom_id_assoc]⟩
  hom_inv_id := hom_ext (by simp)
  inv_hom_id := hom_ext (by simp)

end TrivializedThickening

/-- Two morphisms of ringed spaces with the same base map and the same map on structure
sheaves are equal. -/
theorem ringedSpaceHom_ext {Y Z : RingedSpace.{u, u}} {f g : Y ⟶ Z}
    (w : f.hom.base = g.hom.base) (h : f.hom.c ≍ g.hom.c) : f = g :=
  InducedCategory.hom_ext (PresheafedSpace.hext _ _ w h)

/-- Two morphisms of ringed spaces with the same base map are equal when their maps on sections
agree. -/
private theorem ringedSpaceHom_ext_app {Y Z : RingedSpace.{u, u}} {f g : Y ⟶ Z}
    (w : f.hom.base = g.hom.base)
    (h : ∀ (U : (Opens Z.carrier)ᵒᵖ) (z : Z.presheaf.obj U),
      (f.hom.c.app U).hom z ≍ (g.hom.c.app U).hom z) : f = g := by
  obtain ⟨⟨b, c⟩⟩ := f
  obtain ⟨⟨b', c'⟩⟩ := g
  cases w
  exact ringedSpaceHom_ext rfl (heq_of_eq (NatTrans.ext (funext fun U =>
    CommRingCat.hom_ext (RingHom.ext fun z => eq_of_heq (h U z)))))

/-- Two morphisms of ringed spaces are equal when their base maps agree and their maps on
sections agree after the identification of opens induced by that agreement. -/
theorem ringedSpaceHom_ext' {Y Z : RingedSpace.{u, u}} {f g : Y ⟶ Z}
    (w : f.hom.base = g.hom.base)
    (h : ∀ (U : (Opens Z.carrier)ᵒᵖ) (z : Z.presheaf.obj U),
      (Y.presheaf.map (eqToHom (show (Opens.map f.hom.base).op.obj U =
          (Opens.map g.hom.base).op.obj U by rw [w]))).hom ((f.hom.c.app U).hom z) =
        (g.hom.c.app U).hom z) : f = g := by
  refine SheafedSpace.ext _ _ w (NatTrans.ext (funext fun U =>
    CommRingCat.hom_ext (RingHom.ext fun z => ?_)))
  refine Eq.trans ?_ (h U z)
  rw [NatTrans.comp_app, CommRingCat.comp_apply]
  exact congrArg (fun k => (Y.presheaf.map k).hom ((f.hom.c.app U).hom z))
    (Subsingleton.elim _ _)

/-- A restriction map of the structure sheaf along an identification of opens is injective. -/
theorem presheaf_map_eqToHom_injective {U V : (Opens X.carrier)ᵒᵖ} (e : U = V) :
    Function.Injective (X.presheaf.map (eqToHom e)).hom := by
  subst e
  intro a b hab
  simpa using hab

/-- Two restriction maps of the structure sheaf along inverse identifications of opens
compose to the identity. -/
theorem presheaf_map_eqToHom_self {U V : (Opens X.carrier)ᵒᵖ} (e₁ : U = V) (e₂ : V = U)
    (b : X.presheaf.obj U) :
    (X.presheaf.map (eqToHom e₂)).hom ((X.presheaf.map (eqToHom e₁)).hom b) = b := by
  subst e₁
  simp

open Stacks.Deformation.TrivialSqZero in
/-- The object of trivialized first order thickenings attached to an `𝒪_X`-module `𝒢`: the
ringed space `(X, 𝒪_X ⋉ 𝒢)`, thickened by the projection and trivialized by the zero
section. -/
noncomputable def trivialThickeningObj (X : RingedSpace.{u, u})
    (G : SheafOfModules.{u} (structureSheafRing X)) : TrivializedThickening X where
  ambient := space X G
  i := thickening X G
  trivialization :=
    { retraction := over (G := G) (𝟙 X)
      id := thickening_comp_over (G := G) (𝟙 X) }
  isFirstOrder := isFirstOrderThickening_thickening X G

/-! ### Functoriality of the trivial square-zero extension

A map `φ : 𝒢₂ ⟶ 𝒢₁` of `𝒪_X`-modules induces the map `(a, m) ↦ (a, φ m)` of sheaves of
algebras `𝒪_X ⋉ 𝒢₂ ⟶ 𝒪_X ⋉ 𝒢₁`, hence a morphism of ringed spaces in the *opposite*
direction, `(X, 𝒪_X ⋉ 𝒢₁) ⟶ (X, 𝒪_X ⋉ 𝒢₂)`. This is why the construction `𝒢 ↦ (X, 𝒪_X ⋉ 𝒢)`
is a functor out of the opposite of the category of `𝒪_X`-modules.
-/

/-- The sections of an `𝒪_X`-module over an open form a module over the commutative ring of
sections of `𝒪_X`. -/
@[instance_reducible]
noncomputable def sectionModule (G : SheafOfModules.{u} (structureSheafRing X))
    (U : (Opens X.carrier)ᵒᵖ) : Module ↥(X.sheaf.obj.obj U) ↥(G.val.obj U) :=
  (G.val.obj U).isModule

attribute [local instance] sectionModule

/-- The first component of a restriction in `𝒪_X ⋉ 𝒢`. This is
`AlgebraicGeometry.SheafOfModules.sqZeroPresheaf_map_fst` at the spelling
`RingedSpaceModuleAdjunction.structureSheafRing X` of the ring of scalars of `𝒢`. -/
theorem sqZeroExt_map_fst {G : SheafOfModules.{u} (structureSheafRing X)}
    {U V : (Opens X.carrier)ᵒᵖ} (f : U ⟶ V)
    (z : (AlgebraicGeometry.SheafOfModules.sqZeroPresheaf X.sheaf G).obj U) :
    (((AlgebraicGeometry.SheafOfModules.sqZeroPresheaf X.sheaf G).map f).hom z).fst =
      (X.sheaf.obj.map f).hom z.fst :=
  AlgebraicGeometry.SheafOfModules.sqZeroPresheaf_map_fst (O := X.sheaf) (N := G) f z

/-- The second component of a restriction in `𝒪_X ⋉ 𝒢`. This is
`AlgebraicGeometry.SheafOfModules.sqZeroPresheaf_map_snd` at the spelling
`RingedSpaceModuleAdjunction.structureSheafRing X` of the ring of scalars of `𝒢`. -/
theorem sqZeroExt_map_snd {G : SheafOfModules.{u} (structureSheafRing X)}
    {U V : (Opens X.carrier)ᵒᵖ} (f : U ⟶ V)
    (z : (AlgebraicGeometry.SheafOfModules.sqZeroPresheaf X.sheaf G).obj U) :
    (((AlgebraicGeometry.SheafOfModules.sqZeroPresheaf X.sheaf G).map f).hom z).snd =
      G.val.map f z.snd :=
  (AlgebraicGeometry.SheafOfModules.sqZeroPresheaf_map_snd (O := X.sheaf) (N := G) f z).trans rfl

section SqZeroFunctoriality

variable {G₂ G₁ : SheafOfModules.{u} (structureSheafRing X)} (φ : G₂ ⟶ G₁)

/-- A map of `𝒪_X`-modules is linear for the module structure on sections over an open. -/
theorem app_smul (U : (Opens X.carrier)ᵒᵖ) (r : ↥(X.sheaf.obj.obj U))
    (m : ↥(G₂.val.obj U)) :
    (φ.val.app U).hom.toAddMonoidHom (r • m) =
      (RingHom.id ↥(X.sheaf.obj.obj U)) r • (φ.val.app U).hom.toAddMonoidHom m :=
  map_smul (φ.val.app U).hom r m

/-- The map `(a, m) ↦ (a, φ m)` of square-zero extensions, on sections over one open. -/
noncomputable def sqZeroExtMapApp (U : (Opens X.carrier)ᵒᵖ) :
    (AlgebraicGeometry.SheafOfModules.sqZeroPresheaf X.sheaf G₂).obj U ⟶
      (AlgebraicGeometry.SheafOfModules.sqZeroPresheaf X.sheaf G₁).obj U :=
  CommRingCat.ofHom
    (sqZeroMap (RingHom.id ↥(X.sheaf.obj.obj U)) (φ.val.app U).hom.toAddMonoidHom
      (app_smul φ U))

/-- The map `(a, m) ↦ (a, φ m)` preserves first components. -/
@[simp]
theorem sqZeroExtMapApp_fst (U : (Opens X.carrier)ᵒᵖ)
    (z : (AlgebraicGeometry.SheafOfModules.sqZeroPresheaf X.sheaf G₂).obj U) :
    ((sqZeroExtMapApp φ U).hom z).fst = z.fst :=
  sqZeroMap_fst _ _ (app_smul φ U) z

/-- The map `(a, m) ↦ (a, φ m)` applies `φ` to second components. -/
@[simp]
theorem sqZeroExtMapApp_snd (U : (Opens X.carrier)ᵒᵖ)
    (z : (AlgebraicGeometry.SheafOfModules.sqZeroPresheaf X.sheaf G₂).obj U) :
    ((sqZeroExtMapApp φ U).hom z).snd = (φ.val.app U).hom z.snd :=
  sqZeroMap_snd _ _ (app_smul φ U) z

/-- The map `(a, m) ↦ (a, φ m)` of square-zero extensions, as a morphism of presheaves of
commutative rings on `X`. -/
noncomputable def sqZeroExtMapNatTrans :
    AlgebraicGeometry.SheafOfModules.sqZeroPresheaf X.sheaf G₂ ⟶
      AlgebraicGeometry.SheafOfModules.sqZeroPresheaf X.sheaf G₁ where
  app := sqZeroExtMapApp φ
  naturality U V f := CommRingCat.hom_ext (RingHom.ext fun z => by
    rw [CommRingCat.comp_apply, CommRingCat.comp_apply]
    refine TrivSqZeroExt.ext ?_ ?_
    · rw [sqZeroExtMapApp_fst, sqZeroExt_map_fst, sqZeroExt_map_fst, sqZeroExtMapApp_fst]
    · rw [sqZeroExtMapApp_snd, sqZeroExt_map_snd, sqZeroExt_map_snd, sqZeroExtMapApp_snd]
      exact PresheafOfModules.naturality_apply φ.val f z.snd)

/-- The map `(a, m) ↦ (a, φ m)` of square-zero extensions, as a morphism of sheaves of
commutative rings on `X`. -/
noncomputable def sqZeroExtMap :
    AlgebraicGeometry.SheafOfModules.sqZeroSheaf X.sheaf G₂ ⟶
      AlgebraicGeometry.SheafOfModules.sqZeroSheaf X.sheaf G₁ :=
  ObjectProperty.homMk (sqZeroExtMapNatTrans φ)

/-- The components of `sqZeroExtMap φ` are the maps `sqZeroExtMapApp φ U`. -/
@[simp]
theorem sqZeroExtMap_app (U : (Opens X.carrier)ᵒᵖ) :
    (sqZeroExtMap φ).hom.app U = sqZeroExtMapApp φ U := rfl

open Stacks.Deformation.TrivialSqZero in
/-- The morphism of ringed spaces `(X, 𝒪_X ⋉ 𝒢₁) ⟶ (X, 𝒪_X ⋉ 𝒢₂)` induced by a map
`φ : 𝒢₂ ⟶ 𝒢₁` of `𝒪_X`-modules: the identity on the underlying space, and `(a, m) ↦ (a, φ m)`
on structure sheaves. -/
noncomputable def trivialThickeningMap : space X G₁ ⟶ space X G₂ :=
  ⟨{ base := 𝟙 X.carrier
     c := (sqZeroExtMap φ).hom }⟩

open Stacks.Deformation.TrivialSqZero in
/-- The induced morphism is a morphism of thickenings of `(X, 𝒪_X)`. -/
theorem thickening_comp_trivialThickeningMap :
    thickening X G₁ ≫ trivialThickeningMap φ = thickening X G₂ :=
  ringedSpaceHom_ext_app (Category.comp_id _) fun U z => heq_of_eq (sqZeroExtMapApp_fst φ U z)

open Stacks.Deformation.TrivialSqZero in
/-- The induced morphism is compatible with the trivializations. -/
theorem trivialThickeningMap_comp_over :
    trivialThickeningMap φ ≫ over (G := G₂) (𝟙 X) = over (G := G₁) (𝟙 X) :=
  ringedSpaceHom_ext_app (Category.comp_id _) fun U a => heq_of_eq (by
    refine TrivSqZeroExt.ext ?_ ?_
    · exact sqZeroExtMapApp_fst φ U (TrivSqZeroExt.inl a)
    · refine (sqZeroExtMapApp_snd φ U (TrivSqZeroExt.inl a)).trans ?_
      exact (congrArg (fun x => (φ.val.app U).hom x) (TrivSqZeroExt.snd_inl _ _)).trans
        (map_zero (φ.val.app U).hom))

end SqZeroFunctoriality

section Functoriality

variable {G₃ G₂ G₁ : SheafOfModules.{u} (structureSheafRing X)}

/-- The identity of a module induces the identity of `𝒪_X ⋉ 𝒢` on sections. -/
theorem sqZeroExtMapApp_id (G : SheafOfModules.{u} (structureSheafRing X)) (U : (Opens X.carrier)ᵒᵖ)
    (z : (AlgebraicGeometry.SheafOfModules.sqZeroPresheaf X.sheaf G).obj U) :
    (sqZeroExtMapApp (𝟙 G) U).hom z = z :=
  TrivSqZeroExt.ext (sqZeroExtMapApp_fst (𝟙 G) U z) (sqZeroExtMapApp_snd (𝟙 G) U z)

/-- A composite of maps of modules induces the composite of the induced maps on sections. -/
theorem sqZeroExtMapApp_comp (ψ : G₃ ⟶ G₂) (φ : G₂ ⟶ G₁) (U : (Opens X.carrier)ᵒᵖ)
    (z : (AlgebraicGeometry.SheafOfModules.sqZeroPresheaf X.sheaf G₃).obj U) :
    (sqZeroExtMapApp (ψ ≫ φ) U).hom z =
      (sqZeroExtMapApp φ U).hom ((sqZeroExtMapApp ψ U).hom z) :=
  TrivSqZeroExt.ext
    (by rw [sqZeroExtMapApp_fst, sqZeroExtMapApp_fst, sqZeroExtMapApp_fst])
    (by rw [sqZeroExtMapApp_snd, sqZeroExtMapApp_snd, sqZeroExtMapApp_snd]; rfl)

open Stacks.Deformation.TrivialSqZero in
/-- The identity of a module induces the identity of `(X, 𝒪_X ⋉ 𝒢)`. -/
theorem trivialThickeningMap_id (G : SheafOfModules.{u} (structureSheafRing X)) :
    trivialThickeningMap (𝟙 G) = 𝟙 (space X G) :=
  ringedSpaceHom_ext_app rfl fun U z => heq_of_eq (sqZeroExtMapApp_id G U z)

open Stacks.Deformation.TrivialSqZero in
/-- A composite `ψ ≫ φ` of maps of modules induces the composite of the induced morphisms of
ringed spaces, in the opposite order. -/
theorem trivialThickeningMap_comp (ψ : G₃ ⟶ G₂) (φ : G₂ ⟶ G₁) :
    trivialThickeningMap (ψ ≫ φ) = trivialThickeningMap φ ≫ trivialThickeningMap ψ :=
  ringedSpaceHom_ext_app (Category.comp_id _).symm fun U z =>
    heq_of_eq (sqZeroExtMapApp_comp ψ φ U z)

end Functoriality

open Stacks.Deformation.TrivialSqZero in
/-- The trivial square-zero extension as a functor: an `𝒪_X`-module `𝒢` goes to the trivialized
first order thickening `(X, 𝒪_X ⋉ 𝒢)`, and a map `φ : 𝒢₂ ⟶ 𝒢₁` of modules to the morphism of
thickenings `(X, 𝒪_X ⋉ 𝒢₁) ⟶ (X, 𝒪_X ⋉ 𝒢₂)` it induces on sheaves of algebras. -/
noncomputable def trivialThickeningFunctor (X : RingedSpace.{u, u}) :
    (SheafOfModules.{u} (structureSheafRing X))ᵒᵖ ⥤ TrivializedThickening X where
  obj G := trivialThickeningObj X G.unop
  map f :=
    { hom := trivialThickeningMap f.unop
      i_comp := thickening_comp_trivialThickeningMap f.unop
      comp_retraction := trivialThickeningMap_comp_over f.unop }
  map_id G := TrivializedThickening.hom_ext (trivialThickeningMap_id G.unop)
  map_comp f g := TrivializedThickening.hom_ext (trivialThickeningMap_comp g.unop f.unop)

/-- The underlying morphism of ringed spaces of the image of `f` is `trivialThickeningMap f.unop`.
-/
@[simp]
theorem trivialThickeningFunctor_map_hom (X : RingedSpace.{u, u})
    {G₁ G₂ : (SheafOfModules.{u} (structureSheafRing X))ᵒᵖ} (f : G₁ ⟶ G₂) :
    ((trivialThickeningFunctor X).map f).hom = trivialThickeningMap f.unop := rfl

/-! ### The functor is fully faithful

A morphism of trivialized thickenings between two trivial square-zero extensions is the
identity on the underlying space, because both thickenings are; its map on structure sheaves
preserves first components (compatibility with the thickenings) and the zero section
(compatibility with the trivializations), so it is `(a, m) ↦ (a, φ m)` for a unique map
`φ` of `𝒪_X`-modules.
-/

section FullyFaithful

variable {G₂ G₁ : SheafOfModules.{u} (structureSheafRing X)}

/-- A restriction map of an `𝒪_X`-module along a morphism from an open to itself is the
identity: between two opens there is at most one morphism. -/
theorem val_map_self (G : SheafOfModules.{u} (structureSheafRing X)) {U : (Opens X.carrier)ᵒᵖ}
    (f : U ⟶ U) (m : G.val.obj U) : G.val.map f m = m := by
  rw [Subsingleton.elim f (𝟙 U)]
  change (G.val.presheaf.map (𝟙 U)).hom m = m
  rw [CategoryTheory.Functor.map_id]
  rfl

/-- A restriction map of the structure sheaf along a morphism from an open to itself is the
identity. -/
theorem presheaf_map_self {U : (Opens X.carrier)ᵒᵖ} (f : U ⟶ U) (r : X.presheaf.obj U) :
    (X.presheaf.map f).hom r = r := by
  rw [Subsingleton.elim f (𝟙 U), CategoryTheory.Functor.map_id]
  rfl

/-- A restriction map of `𝒪_X ⋉ 𝒢` along a morphism from an open to itself is the identity. -/
theorem sqZeroExt_map_self (G : SheafOfModules.{u} (structureSheafRing X)) {U : (Opens X.carrier)ᵒᵖ}
    (f : U ⟶ U) (z : (AlgebraicGeometry.SheafOfModules.sqZeroPresheaf X.sheaf G).obj U) :
    (((AlgebraicGeometry.SheafOfModules.sqZeroPresheaf X.sheaf G).map f).hom z) = z :=
  TrivSqZeroExt.ext ((sqZeroExt_map_fst f z).trans (presheaf_map_self f z.fst))
    ((sqZeroExt_map_snd f z).trans (val_map_self G f z.snd))

/-- The trivial square-zero extension functor is faithful. -/
instance : (trivialThickeningFunctor X).Faithful where
  map_injective {G₁' G₂'} f g w := by
    have hw : trivialThickeningMap f.unop = trivialThickeningMap g.unop :=
      congrArg TrivializedThickening.Hom.hom w
    have key : ∀ {k l : Stacks.Deformation.TrivialSqZero.space X G₁'.unop ⟶
          Stacks.Deformation.TrivialSqZero.space X G₂'.unop}, k = l →
        ∀ (U : (Opens X.carrier)ᵒᵖ) (z : (AlgebraicGeometry.SheafOfModules.sqZeroPresheaf
            X.sheaf G₂'.unop).obj U),
          TrivSqZeroExt.snd ((k.hom.c.app U).hom z) ≍
            TrivSqZeroExt.snd ((l.hom.c.app U).hom z) := by
      rintro k l rfl U z
      rfl
    refine Quiver.Hom.unop_inj ?_
    ext U m
    refine (sqZeroExtMapApp_snd f.unop U (TrivSqZeroExt.inr m)).symm.trans ?_
    refine Eq.trans ?_ (sqZeroExtMapApp_snd g.unop U (TrivSqZeroExt.inr m))
    exact eq_of_heq (key hw U (TrivSqZeroExt.inr m))

/-! #### Recovering the map of modules

A morphism of sheaves of algebras `𝒪_X ⋉ 𝒢₂ ⟶ 𝒪_X ⋉ 𝒢₁` which preserves first components and
fixes the zero section is `(a, m) ↦ (a, φ m)` for a map `φ : 𝒢₂ ⟶ 𝒢₁` of `𝒪_X`-modules, namely
`φ m = (c (0, m)).snd`; linearity of `φ` is multiplicativity of `c` together with
`(a, 0) · (0, m) = (0, a m)`.

The four statements below concern one ring homomorphism of trivial square-zero extensions
`R ⋉ M ⟶ R ⋉ N`.
-/

section SqZeroAlgebra

variable {R M N : Type u} [CommRing R] [AddCommGroup M] [AddCommGroup N]
  [Module R M] [Module R N] (f : TrivSqZeroExt R M →+* TrivSqZeroExt R N)

/-- A ring homomorphism of trivial square-zero extensions is additive on second components of
the second summand. -/
theorem snd_apply_inr_add (m m' : M) :
    (f (TrivSqZeroExt.inr (m + m'))).snd =
      (f (TrivSqZeroExt.inr m)).snd + (f (TrivSqZeroExt.inr m')).snd := by
  rw [TrivSqZeroExt.inr_add, map_add, TrivSqZeroExt.snd_add]

/-- A ring homomorphism of trivial square-zero extensions fixing the first summand is linear on
second components of the second summand: `(a, 0) · (0, m) = (0, a m)`. -/
theorem snd_apply_inr_smul (hinl : ∀ a : R, f (TrivSqZeroExt.inl a) = TrivSqZeroExt.inl a)
    (r : R) (m : M) :
    (f (TrivSqZeroExt.inr (r • m))).snd = r • (f (TrivSqZeroExt.inr m)).snd := by
  rw [← TrivSqZeroExt.inl_mul_inr, map_mul, hinl, TrivSqZeroExt.snd_mul, TrivSqZeroExt.fst_inl,
    TrivSqZeroExt.snd_inl, smul_zero, add_zero]

/-- A ring homomorphism of trivial square-zero extensions fixing the first summand is determined
on a section by its value on the second summand. -/
theorem apply_eq_inl_add_apply_inr
    (hinl : ∀ a : R, f (TrivSqZeroExt.inl a) = TrivSqZeroExt.inl a) (z : TrivSqZeroExt R M) :
    f z = TrivSqZeroExt.inl z.fst + f (TrivSqZeroExt.inr z.snd) := by
  rw [← hinl z.fst, ← map_add, TrivSqZeroExt.inl_fst_add_inr_snd_eq]

/-- The second component of the image of a section under a ring homomorphism of trivial
square-zero extensions fixing the first summand. -/
theorem snd_apply (hinl : ∀ a : R, f (TrivSqZeroExt.inl a) = TrivSqZeroExt.inl a)
    (z : TrivSqZeroExt R M) :
    (f z).snd = (f (TrivSqZeroExt.inr z.snd)).snd := by
  rw [apply_eq_inl_add_apply_inr f hinl z, TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, zero_add]

end SqZeroAlgebra

/-- The map of `𝒪_X`-modules underlying a morphism of trivial square-zero extensions which
fixes the zero section: `φ m = (c (0, m)).snd`. -/
noncomputable def moduleOfSqZeroExtMap
    (c : AlgebraicGeometry.SheafOfModules.sqZeroPresheaf X.sheaf G₂ ⟶
      AlgebraicGeometry.SheafOfModules.sqZeroPresheaf X.sheaf G₁)
    (hinl : ∀ (U : (Opens X.carrier)ᵒᵖ) (a : X.presheaf.obj U),
      (c.app U).hom (TrivSqZeroExt.inl a) = TrivSqZeroExt.inl a) :
    G₂ ⟶ G₁ := by
  refine ⟨{
    app := fun U => ModuleCat.ofHom
      (X := G₂.val.obj U) (Y := G₁.val.obj U)
      { toFun := fun m => ((c.app U).hom (TrivSqZeroExt.inr m)).snd
        map_add' := fun m m' => snd_apply_inr_add (c.app U).hom m m'
        map_smul' := fun r m => snd_apply_inr_smul (c.app U).hom (hinl U) r m }
    naturality := ?_ }⟩
  intro U V f
  ext m
  have hnat := congrArg (fun t : (AlgebraicGeometry.SheafOfModules.sqZeroPresheaf
      X.sheaf G₂).obj U ⟶ (AlgebraicGeometry.SheafOfModules.sqZeroPresheaf X.sheaf G₁).obj V =>
    TrivSqZeroExt.snd (t.hom (TrivSqZeroExt.inr m))) (c.naturality f)
  refine Eq.trans ?_ (Eq.trans hnat ?_)
  · exact congrArg (fun w => TrivSqZeroExt.snd ((c.app V).hom w))
      (Stacks.Deformation.TrivialSqZero.sqZeroPresheaf_map_inr X G₂ f m).symm
  · exact sqZeroExt_map_snd f ((c.app U).hom (TrivSqZeroExt.inr m))

/-- The map recovered by `AlgebraicGeometry.RingedSpaceThickening.moduleOfSqZeroExtMap`
reproduces the morphism of square-zero extensions it came from. -/
theorem sqZeroExtMapApp_moduleOfSqZeroExtMap
    (c : AlgebraicGeometry.SheafOfModules.sqZeroPresheaf X.sheaf G₂ ⟶
      AlgebraicGeometry.SheafOfModules.sqZeroPresheaf X.sheaf G₁)
    (hfst : ∀ (U : (Opens X.carrier)ᵒᵖ)
      (z : (AlgebraicGeometry.SheafOfModules.sqZeroPresheaf X.sheaf G₂).obj U),
      ((c.app U).hom z).fst = z.fst)
    (hinl : ∀ (U : (Opens X.carrier)ᵒᵖ) (a : X.presheaf.obj U),
      (c.app U).hom (TrivSqZeroExt.inl a) = TrivSqZeroExt.inl a)
    (U : (Opens X.carrier)ᵒᵖ)
    (z : (AlgebraicGeometry.SheafOfModules.sqZeroPresheaf X.sheaf G₂).obj U) :
    (sqZeroExtMapApp (moduleOfSqZeroExtMap c hinl) U).hom z = (c.app U).hom z := by
  refine TrivSqZeroExt.ext ?_ ?_
  · rw [sqZeroExtMapApp_fst, hfst]
  · rw [sqZeroExtMapApp_snd]
    exact (snd_apply (c.app U).hom (hinl U) z).symm

/-- The trivial square-zero extension functor is full. -/
instance : (trivialThickeningFunctor X).Full where
  map_surjective {G₁' G₂'} h := by
    obtain ⟨k, hi, hr⟩ := h
    obtain ⟨⟨b, c⟩⟩ := k
    have hb : b = 𝟙 X.carrier :=
      (Category.id_comp b).symm.trans (congrArg
        (fun t : X ⟶ Stacks.Deformation.TrivialSqZero.space X G₂'.unop => t.hom.base) hi)
    subst hb
    have hfst : ∀ (U : (Opens X.carrier)ᵒᵖ)
        (z : (AlgebraicGeometry.SheafOfModules.sqZeroPresheaf X.sheaf G₂'.unop).obj U),
        ((c.app U).hom z).fst = z.fst := fun U z =>
      (congrArg (fun t : (AlgebraicGeometry.SheafOfModules.sqZeroPresheaf
            X.sheaf G₂'.unop).obj U ⟶ X.presheaf.obj U => t.hom z)
        (SheafedSpace.congr_hom_app hi U)).trans (presheaf_map_self _ z.fst)
    have hinl : ∀ (U : (Opens X.carrier)ᵒᵖ) (a : X.presheaf.obj U),
        (c.app U).hom (TrivSqZeroExt.inl a) = TrivSqZeroExt.inl a := fun U a =>
      (congrArg (fun t : X.presheaf.obj U ⟶ (AlgebraicGeometry.SheafOfModules.sqZeroPresheaf
            X.sheaf G₁'.unop).obj U => t.hom a)
        (SheafedSpace.congr_hom_app hr U)).trans (sqZeroExt_map_self _ _ _)
    refine ⟨Quiver.Hom.op (moduleOfSqZeroExtMap c hinl), TrivializedThickening.hom_ext ?_⟩
    exact ringedSpaceHom_ext rfl (heq_of_eq (NatTrans.ext (funext fun U =>
      CommRingCat.hom_ext (RingHom.ext fun z =>
        sqZeroExtMapApp_moduleOfSqZeroExtMap c hfst hinl U z))))

end FullyFaithful

/-! ### Every trivialized first order thickening is a trivial square-zero extension

This is the splitting `𝒪_{X'} = 𝒪_X ⊕ ℐ` of **Stacks 08LA**, read as an isomorphism of ringed
spaces `X' ≅ (X, 𝒪_X ⋉ ℐ)` compatible with the thickening and the trivialization. The map is
`(a, x) ↦ π^♯ a + x` on sections; it is a ring map because the ideal is square-zero, it is
bijective because `a` is recovered as `i^♯` of the section and `x` as the remainder, and it is
an isomorphism of ringed spaces because the base map of a trivialization is a homeomorphism.
-/

section EssSurj

variable {X' : RingedSpace.{u, u}} (i : X ⟶ X') (π : SplitMono i)
  (hi : IsFirstOrderThickening i)

/-- The inverse image along the trivialization of an open of `X`. -/
abbrev retractionOpen (U : (Opens X.carrier)ᵒᵖ) : (Opens X'.carrier)ᵒᵖ :=
  (Opens.map π.retraction.hom.base).op.obj U

/-- **The ideal of a trivialized first order thickening, as an `𝒪_X`-module.** The ideal
`ℐ = Ker(i^♯)` is a sheaf of `𝒪_{X'}`-modules; the trivialization reads it on `X` as the
pushforward `π_* ℐ`, whose sections over `U` are `ℐ(π^{-1} U)` with `𝒪_X` acting through
`π^♯`. -/
noncomputable def trivializedIdeal : SheafOfModules.{u} (structureSheafRing X) :=
  (modulePushforward π.retraction).obj (AlgebraicGeometry.SheafOfModules.idealSheaf i)

/-- The structure-sheaf map of the trivialization on sections, read in `𝒪_{X'}`. -/
noncomputable def retrApp (U : (Opens X.carrier)ᵒᵖ) (a : X.presheaf.obj U) :
    X'.presheaf.obj (retractionOpen i π U) :=
  (π.retraction.hom.c.app U).hom a

/-- The inclusion of the ideal on sections over an open `U` of `X`: a section of
`trivializedIdeal` over `U` read as a section of `𝒪_{X'}` over `π⁻¹ U`. -/
noncomputable def trivializedIdealIncl (U : (Opens X.carrier)ᵒᵖ)
    (x : (trivializedIdeal i π).val.obj U) :
    X'.presheaf.obj (retractionOpen i π U) :=
  idealSection i (retractionOpen i π U) x

/-- The inclusion of the ideal sends zero to zero. -/
theorem trivializedIdealIncl_zero (U : (Opens X.carrier)ᵒᵖ) : trivializedIdealIncl i π U 0 = 0 :=
  idealSection_zero i _

/-- The inclusion of the ideal is additive. -/
theorem trivializedIdealIncl_add (U : (Opens X.carrier)ᵒᵖ)
    (x y : (trivializedIdeal i π).val.obj U) :
    trivializedIdealIncl i π U (x + y) =
      trivializedIdealIncl i π U x + trivializedIdealIncl i π U y :=
  idealSection_add i _ x y

/-- The action of `𝒪_X` on the ideal read along the trivialization is the action of `𝒪_{X'}`
through `π^♯`. -/
theorem trivializedIdealIncl_smul (U : (Opens X.carrier)ᵒᵖ) (r : X.sheaf.obj.obj U)
    (x : (trivializedIdeal i π).val.obj U) :
    trivializedIdealIncl i π U (r • x) = retrApp i π U r * trivializedIdealIncl i π U x :=
  idealSection_smul i (retractionOpen i π U) _ _

/-- The inclusion of the ideal commutes with restriction. -/
theorem trivializedIdealIncl_naturality {U V : (Opens X.carrier)ᵒᵖ} (f : U ⟶ V)
    (x : (trivializedIdeal i π).val.obj U) :
    (X'.presheaf.map ((Opens.map π.retraction.hom.base).op.map f)).hom
        (trivializedIdealIncl i π U x) =
      trivializedIdealIncl i π V ((trivializedIdeal i π).val.map f x) :=
  (idealSection_naturality i ((Opens.map π.retraction.hom.base).op.map f) x).symm

include hi in
/-- Two sections of the ideal multiply to zero, the thickening being first order. -/
theorem trivializedIdealIncl_mul_trivializedIdealIncl (U : (Opens X.carrier)ᵒᵖ)
    (x y : (trivializedIdeal i π).val.obj U) :
    trivializedIdealIncl i π U x * trivializedIdealIncl i π U y = 0 :=
  idealSection_mul_idealSection i hi.2 (retractionOpen i π U) _ _
    (structureSheafApp_idealSection i _ x) (structureSheafApp_idealSection i _ y)

/-! #### The lift out of a trivial square-zero extension

A ring map `p : R ⟶ A` and a `p`-semilinear additive map `j : M ⟶ A` whose
image consists of elements multiplying to zero assemble into the ring map `(a, x) ↦ p a + j x`
out of `R ⋉ M`.
-/

section SplittingAlgebra

variable {R M A : Type u} [CommRing R] [CommRing A] [AddCommGroup M] [Module R M]
  (p : R →+* A) (j : M →+ A)
  (hj : ∀ (r : R) (m : M), j (r • m) = p r * j m)
  (hjj : ∀ m m' : M, j m * j m' = 0)

/-- The ring homomorphism `(a, x) ↦ p a + j x` out of a trivial square-zero extension. -/
def sqZeroLift : TrivSqZeroExt R M →+* A where
  toFun z := p z.fst + j z.snd
  map_one' := by
    rw [TrivSqZeroExt.fst_one, TrivSqZeroExt.snd_one, map_one, map_zero, add_zero]
  map_zero' := by
    rw [TrivSqZeroExt.fst_zero, TrivSqZeroExt.snd_zero, map_zero, map_zero, add_zero]
  map_add' x y := by
    rw [TrivSqZeroExt.fst_add, TrivSqZeroExt.snd_add, map_add, map_add]
    abel
  map_mul' x y := by
    rw [TrivSqZeroExt.fst_mul, TrivSqZeroExt.snd_mul, map_mul, map_add, op_smul_eq_smul, hj, hj,
      add_mul, mul_add, mul_add, hjj]
    ring

/-- The value of `sqZeroLift` at `z` is `p z.fst + j z.snd`. -/
theorem sqZeroLift_apply (z : TrivSqZeroExt R M) :
    sqZeroLift p j hj hjj z = p z.fst + j z.snd := rfl

end SplittingAlgebra

/-- The inclusion of the ideal on sections, as an additive map into `𝒪_{X'}`. -/
noncomputable def trivializedIdealInclHom (U : (Opens X.carrier)ᵒᵖ) :
    ↥((trivializedIdeal i π).val.obj U) →+ ↥(X'.presheaf.obj (retractionOpen i π U)) :=
  AddMonoidHom.mk' (trivializedIdealIncl i π U) (trivializedIdealIncl_add i π U)

/-- The splitting `𝒪_X ⋉ ℐ ⟶ π_* 𝒪_{X'}` on sections: `(a, x) ↦ π^♯ a + x`. -/
noncomputable def splittingApp (U : (Opens X.carrier)ᵒᵖ)
    (z : (AlgebraicGeometry.SheafOfModules.sqZeroPresheaf X.sheaf (trivializedIdeal i π)).obj U) :
    X'.presheaf.obj (retractionOpen i π U) :=
  retrApp i π U z.fst + trivializedIdealIncl i π U z.snd

/-- The splitting sends `(a, x)` to `π^♯ a + x`. -/
theorem splittingApp_eq (U : (Opens X.carrier)ᵒᵖ)
    (z : (AlgebraicGeometry.SheafOfModules.sqZeroPresheaf X.sheaf
      (trivializedIdeal i π)).obj U) :
    splittingApp i π U z = retrApp i π U z.fst + trivializedIdealIncl i π U z.snd := rfl

/-- The splitting `𝒪_X ⋉ ℐ ⟶ π_* 𝒪_{X'}`, on sections over one open, as a ring
homomorphism. -/
noncomputable def splittingHomApp (U : (Opens X.carrier)ᵒᵖ) :
    (AlgebraicGeometry.SheafOfModules.sqZeroPresheaf X.sheaf (trivializedIdeal i π)).obj U ⟶
      X'.presheaf.obj (retractionOpen i π U) :=
  CommRingCat.ofHom
    (sqZeroLift (π.retraction.hom.c.app U).hom (trivializedIdealInclHom i π U)
      (trivializedIdealIncl_smul i π U) (trivializedIdealIncl_mul_trivializedIdealIncl i π hi U))

/-- The ring homomorphism `splittingHomApp` is the map `splittingApp`. -/
theorem splittingHomApp_apply (U : (Opens X.carrier)ᵒᵖ)
    (z : (AlgebraicGeometry.SheafOfModules.sqZeroPresheaf X.sheaf
      (trivializedIdeal i π)).obj U) :
    (splittingHomApp i π hi U).hom z = splittingApp i π U z := rfl

/-- The splitting commutes with restriction. -/
theorem splittingApp_naturality {U V : (Opens X.carrier)ᵒᵖ} (f : U ⟶ V)
    (z : (AlgebraicGeometry.SheafOfModules.sqZeroPresheaf X.sheaf
      (trivializedIdeal i π)).obj U) :
    (X'.presheaf.map ((Opens.map π.retraction.hom.base).op.map f)).hom
        (splittingApp i π U z) =
      splittingApp i π V (((AlgebraicGeometry.SheafOfModules.sqZeroPresheaf X.sheaf
        (trivializedIdeal i π)).map f).hom z) := by
  have hρ : (X'.presheaf.map ((Opens.map π.retraction.hom.base).op.map f)).hom
        (retrApp i π U z.fst) = retrApp i π V ((X.sheaf.obj.map f).hom z.fst) :=
    (ConcreteCategory.congr_hom (π.retraction.hom.c.naturality f) z.fst).symm
  rw [splittingApp_eq, splittingApp_eq, map_add, hρ, trivializedIdealIncl_naturality,
    sqZeroExt_map_fst, sqZeroExt_map_snd]

/-- The splitting `𝒪_X ⋉ ℐ ⟶ π_* 𝒪_{X'}` as a morphism of presheaves of commutative rings. -/
noncomputable def splittingNatTrans :
    AlgebraicGeometry.SheafOfModules.sqZeroPresheaf X.sheaf (trivializedIdeal i π) ⟶
      (Opens.map π.retraction.hom.base).op ⋙ X'.presheaf where
  app := splittingHomApp i π hi
  naturality U V f := CommRingCat.hom_ext (RingHom.ext fun z => by
    rw [CommRingCat.comp_apply, CommRingCat.comp_apply]
    exact (splittingApp_naturality i π f z).symm)

/-- The splitting `𝒪_{X'} = 𝒪_X ⊕ ℐ` of a trivialized first order thickening, as a morphism of
ringed spaces `X' ⟶ (X, 𝒪_X ⋉ ℐ)`: the base map is that of the trivialization and the map on
structure sheaves is `(a, x) ↦ π^♯ a + x`. -/
noncomputable def splittingMorphism :
    X' ⟶ Stacks.Deformation.TrivialSqZero.space X (trivializedIdeal i π) :=
  ⟨{ base := π.retraction.hom.base
     c := splittingNatTrans i π hi }⟩

/-! #### The splitting is an isomorphism -/

/-- The structure-sheaf map of the thickening kills the ideal. -/
theorem structureSheaf_trivializedIdealIncl (U : (Opens X.carrier)ᵒᵖ)
    (x : (trivializedIdeal i π).val.obj U) :
    (i.hom.c.app (retractionOpen i π U)).hom (trivializedIdealIncl i π U x) = 0 :=
  structureSheafApp_idealSection i (retractionOpen i π U) x

/-- The structure-sheaf map of the thickening undoes the trivialization. -/
theorem structureSheaf_retrApp (U : (Opens X.carrier)ᵒᵖ) (a : X.sheaf.obj.obj U) :
    (i.hom.c.app (retractionOpen i π U)).hom (retrApp i π U a) =
      (X.presheaf.map (eqToHom (thickening_opens_op_obj i π U).symm)).hom a :=
  ConcreteCategory.congr_hom (retraction_comp_structureSheaf_app_of_opens i π U) a

/-- The structure-sheaf map of the thickening recovers the first component of a section. -/
theorem structureSheaf_splittingApp (U : (Opens X.carrier)ᵒᵖ)
    (z : (AlgebraicGeometry.SheafOfModules.sqZeroPresheaf X.sheaf
      (trivializedIdeal i π)).obj U) :
    (i.hom.c.app (retractionOpen i π U)).hom (splittingApp i π U z) =
      (X.presheaf.map (eqToHom (thickening_opens_op_obj i π U).symm)).hom z.fst := by
  rw [splittingApp_eq, map_add, structureSheaf_retrApp, structureSheaf_trivializedIdealIncl,
    add_zero]

/-- The splitting is injective on sections. -/
theorem splittingApp_injective (U : (Opens X.carrier)ᵒᵖ) :
    Function.Injective (splittingApp i π U) := by
  intro z w h
  have h1 : (X.presheaf.map (eqToHom (thickening_opens_op_obj i π U).symm)).hom z.fst =
      (X.presheaf.map (eqToHom (thickening_opens_op_obj i π U).symm)).hom w.fst := by
    rw [← structureSheaf_splittingApp, ← structureSheaf_splittingApp, h]
  have hfst : z.fst = w.fst := presheaf_map_eqToHom_injective _ h1
  have h2 : retrApp i π U z.fst + trivializedIdealIncl i π U z.snd =
      retrApp i π U z.fst + trivializedIdealIncl i π U w.snd := by
    refine h.trans ?_
    rw [hfst]
    rfl
  have h3 : trivializedIdealIncl i π U z.snd = trivializedIdealIncl i π U w.snd :=
    add_left_cancel h2
  exact TrivSqZeroExt.ext hfst (idealSection_injective i (retractionOpen i π U) h3)

/-- The splitting is surjective on sections. -/
theorem splittingApp_surjective (U : (Opens X.carrier)ᵒᵖ) :
    Function.Surjective (splittingApp i π U) := by
  intro y
  obtain ⟨a, ha⟩ : ∃ a : X.sheaf.obj.obj U,
      (structureSheafApp i (retractionOpen i π U)).hom (retrApp i π U a) =
        (structureSheafApp i (retractionOpen i π U)).hom y :=
    ⟨(X.presheaf.map (eqToHom (thickening_opens_op_obj i π U))).hom
        ((i.hom.c.app (retractionOpen i π U)).hom y),
      (structureSheaf_retrApp i π U _).trans (presheaf_map_eqToHom_self _ _ _)⟩
  have hker : (structureSheafApp i (retractionOpen i π U)).hom (y - retrApp i π U a) = 0 :=
    (map_sub (structureSheafApp i (retractionOpen i π U)).hom _ _).trans (by rw [ha, sub_self])
  obtain ⟨x, hx⟩ : ∃ x : (trivializedIdeal i π).val.obj U,
      trivializedIdealIncl i π U x = y - retrApp i π U a :=
    Stacks.ClosedImmersion.exists_idealSheaf_section_of_app_eq_zero i
      (retractionOpen i π U).unop _ hker
  refine ⟨TrivSqZeroExt.inl a + TrivSqZeroExt.inr x, ?_⟩
  have hf : (TrivSqZeroExt.inl a + TrivSqZeroExt.inr x :
      (AlgebraicGeometry.SheafOfModules.sqZeroPresheaf X.sheaf
        (trivializedIdeal i π)).obj U).fst = a := fst_inl_add_inr a x
  have hs : (TrivSqZeroExt.inl a + TrivSqZeroExt.inr x :
      (AlgebraicGeometry.SheafOfModules.sqZeroPresheaf X.sheaf
        (trivializedIdeal i π)).obj U).snd = x := snd_inl_add_inr a x
  rw [splittingApp_eq, hf, hs, hx]
  abel

include hi in
/-- The splitting is an isomorphism of rings on sections over every open. -/
theorem isIso_splittingHomApp (U : (Opens X.carrier)ᵒᵖ) :
    IsIso (splittingHomApp i π hi U) :=
  (ConcreteCategory.isIso_iff_bijective _).2
    ⟨splittingApp_injective i π U, splittingApp_surjective i π U⟩

include hi in
/-- The splitting `X' ⟶ (X, 𝒪_X ⋉ ℐ)` is an isomorphism of ringed spaces. -/
theorem isIso_splittingMorphism : IsIso (splittingMorphism i π hi) := by
  have : IsIso (splittingMorphism i π hi).hom.base := isIso_retraction_base i π hi.1.1
  have : ∀ U, IsIso ((splittingMorphism i π hi).hom.c.app U) := fun U =>
    isIso_splittingHomApp i π hi U
  have : IsIso (splittingMorphism i π hi).hom.c := NatIso.isIso_of_isIso_app _
  have : IsIso (splittingMorphism i π hi).hom := PresheafedSpace.isIso_of_components _
  exact ⟨⟨InducedCategory.homMk (inv (splittingMorphism i π hi).hom),
    InducedCategory.hom_ext (IsIso.hom_inv_id (splittingMorphism i π hi).hom),
    InducedCategory.hom_ext (IsIso.inv_hom_id (splittingMorphism i π hi).hom)⟩⟩

/-! #### The splitting respects the thickening and the trivialization -/

include hi in
/-- The splitting carries the thickening to the thickening of the trivial square-zero
extension. -/
theorem thickening_comp_splittingMorphism :
    i ≫ splittingMorphism i π hi =
      Stacks.Deformation.TrivialSqZero.thickening X (trivializedIdeal i π) := by
  have w0 : (i ≫ π.retraction).hom.base = (𝟙 X : X ⟶ X).hom.base :=
    congrArg (fun k : X ⟶ X => k.hom.base) π.id
  have w : (i ≫ splittingMorphism i π hi).hom.base =
      (Stacks.Deformation.TrivialSqZero.thickening X (trivializedIdeal i π)).hom.base := w0
  refine ringedSpaceHom_ext' w (fun U z => ?_)
  rw [show ((i ≫ splittingMorphism i π hi).hom.c.app U).hom z =
      (X.presheaf.map (eqToHom (thickening_opens_op_obj i π U).symm)).hom z.fst from
    structureSheaf_splittingApp i π U z]
  exact presheaf_map_eqToHom_self _ _ z.fst

/-- The splitting sends `(a, 0)` to `π^♯ a`. -/
theorem splittingApp_inl (U : (Opens X.carrier)ᵒᵖ) (a : X.sheaf.obj.obj U) :
    splittingApp i π U (TrivSqZeroExt.inl a) = retrApp i π U a := by
  have h1 : splittingApp i π U (TrivSqZeroExt.inl a) =
      retrApp i π U a + trivializedIdealIncl i π U
        (TrivSqZeroExt.inl a : (AlgebraicGeometry.SheafOfModules.sqZeroPresheaf X.sheaf
          (trivializedIdeal i π)).obj U).snd :=
    splittingApp_eq i π U (TrivSqZeroExt.inl a)
  have h2 : (TrivSqZeroExt.inl a : (AlgebraicGeometry.SheafOfModules.sqZeroPresheaf X.sheaf
      (trivializedIdeal i π)).obj U).snd = 0 := TrivSqZeroExt.snd_inl _ a
  rw [h1, h2, trivializedIdealIncl_zero, add_zero]

include hi in
/-- The splitting carries the trivialization to the zero section. -/
theorem splittingMorphism_comp_over :
    splittingMorphism i π hi ≫
        Stacks.Deformation.TrivialSqZero.over (G := trivializedIdeal i π) (𝟙 X) =
      π.retraction :=
  ringedSpaceHom_ext_app (Category.comp_id _) fun U a => heq_of_eq (splittingApp_inl i π U a)

/-- The splitting of a trivialized first order thickening, read as a morphism of trivialized
thickenings onto the trivial square-zero extension of its ideal. -/
noncomputable def splittingThickeningHom (A : TrivializedThickening X) :
    A ⟶ trivialThickeningObj X (trivializedIdeal A.i A.trivialization) where
  hom := splittingMorphism A.i A.trivialization A.isFirstOrder
  i_comp := thickening_comp_splittingMorphism A.i A.trivialization A.isFirstOrder
  comp_retraction := splittingMorphism_comp_over A.i A.trivialization A.isFirstOrder

end EssSurj

/-- **Every trivialized first order thickening of `(X, 𝒪_X)` is isomorphic to the trivial
square-zero extension `𝒪_X ⋉ ℐ` of its ideal.** -/
@[ega "0 18.2.3" "partial"]
noncomputable def trivialThickeningObjIso (A : TrivializedThickening X) :
    trivialThickeningObj X (trivializedIdeal A.i A.trivialization) ≅ A :=
  haveI : IsIso (splittingThickeningHom A).hom :=
    isIso_splittingMorphism A.i A.trivialization A.isFirstOrder
  (TrivializedThickening.isoOfIsIso (splittingThickeningHom A)).symm

/-- The trivial square-zero extension functor is essentially surjective. -/
instance : (trivialThickeningFunctor X).EssSurj where
  mem_essImage A := ⟨op (trivializedIdeal A.i A.trivialization), ⟨trivialThickeningObjIso A⟩⟩

/-- The trivial square-zero extension functor is an equivalence. -/
instance : (trivialThickeningFunctor X).IsEquivalence where

/-- The category of trivialized first order thickenings of a ringed space `(X, 𝒪_X)` is
equivalent to the opposite of the category of `𝒪_X`-modules.

A trivialization `π` of a first order thickening `i : X ⟶ X'` splits the surjection
`𝒪_{X'} ⟶ 𝒪_X`, giving `𝒪_{X'} = 𝒪_X ⊕ ℐ` as sheaves of algebras on `X`, and conversely such a
splitting determines `π`. The equivalence sends an `𝒪_X`-module `𝒢` to the trivial square-zero
extension `(X, 𝒪_X ⋉ 𝒢)` with the zero section as trivialization, and a trivialized thickening
back to its ideal read along the trivialization.

It is contravariant for the source's own convention for morphisms: `TrivializedThickening X`
has its Hom in the geometric direction, a morphism of thickenings of `(X, 𝒪_X)` being a
morphism `X'₁ ⟶ X'₂` of ringed spaces (Stacks 08LD), and that is a morphism
`𝒪_{X'₂} ⟶ 𝒪_{X'₁}` of sheaves of algebras on `X`, hence a morphism `ℐ₂ ⟶ ℐ₁` of the ideals
(Stacks 08LC). -/
@[stacks 08L9 "the category of trivialized first order thickenings of (X, 𝒪_X) is equivalent \
to the category of 𝒪_X-modules; morphisms of thickenings run in the geometric direction \
(X'₁ ⟶ X'₂ of ringed spaces, Stacks 08LD), so the module side carries ᵒᵖ"]
noncomputable def trivializedThickeningEquivalence (X : RingedSpace.{u, u}) :
    (SheafOfModules.{u} (structureSheafRing X))ᵒᵖ ≌ TrivializedThickening X :=
  (trivialThickeningFunctor X).asEquivalence

end AlgebraicGeometry.RingedSpaceThickening

end
