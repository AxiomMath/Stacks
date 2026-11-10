module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Ideal.Quotient.Noetherian
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Polynomial.Basic
public import Mathlib.RingTheory.PrincipalIdealDomain
public import StacksFrontier.CategoryTheory.Preadditive.Injective.Basic
public import StacksFrontier.Homology.Injectives.Sheaf.PresheavesOfModules

/-!
# The category of presented pairs, and presheaves of modules on it

Tag 099D asks for a complex `K(A, I)` of `A`-modules attached to a pair of a commutative ring
and a finitely generated ideal, with maps `K(A, I) ⟶ K(B, IB)` for every ring map `φ : A → B`
that compose **on the nose**. The chosen-generating-family shortcut is refuted
(`Stacks.FunctorialCechFamily.isEmpty_functorialGenerators`), and the route named in that
file's docstring is the one developed here: `K(A, I)` is to be the value at `(A, I)` of a
complex of presheaves of modules on the category of pairs.

This file builds that category and the presheaf-of-modules setting on it. It registers no
`@[stacks]` attribute: it is infrastructure for tag 099D, not a clause of it.

## Main definitions

* `Stacks.PairSite.Pair` — a *presented pair*: a presentation `ℤ[x₁, …, xₙ]/J` of a
  finite-type `ℤ`-algebra together with an ideal of it.
* `Stacks.PairSite.Pair.Hom`, and the `CategoryTheory.Category` instance — a morphism of pairs
  is a ring map `φ` with `J₀ = I₀.map φ` *on the nose*.
* `Stacks.PairSite.ringFunctor` — the covariant functor `(A₀, I₀) ↦ A₀` on pairs.
* `Stacks.PairSite.structureRings` — the same functor read as a presheaf of rings on the site
  `Pairᵒᵖ`, which is the form Mathlib's `PresheafOfModules` consumes.
* `Stacks.PairSite.PairModule` — presheaves of modules on the site of pairs.
* `Stacks.PairSite.PairModule.value`, `Stacks.PairSite.PairModule.restriction` — the value of
  such a presheaf at a pair, and its restriction map along a morphism of pairs.
* `Stacks.PairSite.structureModule`, `Stacks.PairSite.idealSubmodule`,
  `Stacks.PairSite.idealModule` — the structure presheaf as a module over itself, the
  subpresheaf `(A₀, I₀) ↦ I₀`, and that subpresheaf as a presheaf of modules in its own right.
* `Stacks.PairSite.Pair.ofEval` — the pair presented by a finite family of elements of a ring
  `A` and a finite family of polynomials in those variables, together with the induced
  injection of its ring into `A`.

## Main results

* `Stacks.PairSite.PairModule.restriction_comp` and
  `Stacks.PairSite.PairModule.restriction_comp_apply` — **the restriction maps of a presheaf of
  modules on pairs compose strictly.** This is exactly the shape of condition (b) of tag 099D
  (`Stacks.LocalCohomology.FunctorialCechData.map_map`), and it is the whole reason the pair
  category is the right index: a comparison "up to isomorphism in `D(A)`" cannot serve there.
* `Stacks.PairSite.Pair.instIsNoetherianRingRing`, `Stacks.PairSite.Pair.ideal_fg` — the ring of
  a pair is Noetherian, so its ideals are automatically finitely generated; finite generation
  is therefore not a field of `Pair`.
* `Stacks.PairSite.Pair.instFiniteTypeIntRing` — the ring of a pair is a finite-type
  `ℤ`-algebra, which is what identifies this category with the one tag 099D's construction
  indexes over.
* `Stacks.PairSite.enoughInjectives_pairModule`,
  `Stacks.PairSite.hasFunctorialInjectiveEmbeddings_pairModule` — presheaves of modules on
  pairs have (functorial) injective embeddings.
* `Stacks.PairSite.sheafOfModulesBotEquiv` — on a small site with the chaotic topology, sheaves
  of modules are presheaves of modules. Stated for an arbitrary small site, and instantiated at
  the site of pairs as `Stacks.PairSite.sheafOfModulesChaoticEquiv`, so that results available
  only for sheaves of modules can be used on pairs.

## Implementation notes

**Why presented pairs, and not bundled ones.** The objects are presentations
`(n, J ⊆ ℤ[x₁, …, xₙ], I ⊆ ℤ[x₁, …, xₙ]/J)` rather than tuples `(A₀, I₀)` of a carrier type
with a `CommRing` instance and `Algebra.FiniteType ℤ A₀`. A bundled object type quantifies over
`Type u` and therefore lands in `Type (u + 1)`: the category is then only *essentially* small,
and every statement about presheaves on it has to be routed through `EssentiallySmall` or
`AsSmall`, exactly the detour that
`Stacks.Injectives.presheafOfModules_hasFunctorialInjectiveEmbeddings` has to take internally.
Presenting the objects instead makes `Pair.{u} : Type u` with `Category.{u, u}`, i.e. a genuinely
small site, so the Grothendieck-abelian and injectives results apply with no universe surgery
and the sheafification machinery is available if a later piece wants it. The cost is that a
*given* ring `A` is not an object: it is approximated by pairs mapping into it, which is the
filtered-colimit step (and is anyway forced — `A` need not be of finite type over `ℤ`).

**Why `ULift.{u} ℤ` coefficients.** `MvPolynomial (Fin n) ℤ` lives in `Type 0`, so a pair
category built on it would give a presheaf of rings in `RingCat.{0}` while
`Stacks.LocalCohomology.FunctorialCechData.{u}` needs modules over rings in `Type u`. Taking
the coefficients to be `ULift.{u} ℤ` puts the pairs, the site, the rings and the modules all in
a single universe `u`, so `PresheafOfModules.{u} structureRings` is uniform and
`PresheafOfModules.unit` and `PresheafOfModules.Submodule` can be used on it directly. The
alternative — rings in `Type 0` and modules in `Type u` — would make the structure presheaf and
its ideal subpresheaf live at module universe `0` while the complexes live at `u`, and every
comparison between them would need a universe lift.

**Why the site is `Pairᵒᵖ`, and not `Pair`.** Mathlib's `PresheafOfModules R` for
`R : Cᵒᵖ ⥤ RingCat` has, for `f : X ⟶ Y` in `Cᵒᵖ`, a map
`M.obj X ⟶ (ModuleCat.restrictScalars (R.map f)).obj (M.obj Y)`. Tag 099D's datum is covariant
in the pair: a ring map `φ : A₀ → B₀` must induce `K(A₀, I₀) ⟶ K(B₀, J₀)` as a map of
`A₀`-modules. Taking `C := Pairᵒᵖ` makes `Cᵒᵖ`'s morphisms the morphisms of `Pair` and puts the
restriction maps in precisely that shape, with Mathlib's `map_comp` as the strict composition
law. The price is that presheaves are indexed by `Pairᵒᵖᵒᵖ`; `PairModule.value` and
`PairModule.restriction` hide the double opposite, and every lemma below is stated through them,
so a consumer never writes `op (op P)`.

**Finite generation is derived, not assumed.** The ring of a pair is a quotient of a polynomial
ring in finitely many variables over a Noetherian ring, hence Noetherian, so every ideal of it
is finitely generated (`Pair.ideal_fg`). Carrying `I₀.FG` as a field of `Pair` would be pure
redundancy, and would force a coherence check in the composition of morphisms.

**What this duplicates, and what it does not.** The library has no category of ring--ideal
pairs. `Crystalline.IdealPair.Hom` is a morphism type only — no object type and no `Category`
instance — and its condition is the inclusion `I₀.map φ ≤ J₀`, not the equality `J₀ = I₀.map φ`
that makes `(A₀, I₀) ↦ I₀` a *sub*presheaf stable under restriction and that is what tag 099D's
`IB` is. The `Pairs` of `StacksFrontier/RingTheory/Henselian/Pair/Henselization.lean` is a private
abbreviation for étale algebras over a fixed ring augmented to `R ⧸ I`, and is unrelated.

**Why the injectives come from the presheaf side.** `SheafOfModules.enoughInjectivesU`
carries `[HasWeakSheafify J AddCommGrpCat]` and `[J.WEqualsLocallyBijective AddCommGrpCat]`
as hypotheses, and neither is available for `J = ⊥` without further work;
`Stacks.Injectives.presheafOfModules_hasFunctorialInjectiveEmbeddings` has no such hypothesis
and applies to `PairModule` directly. `sheafOfModulesChaoticEquiv` is therefore for transporting
*other* sheaf-side results onto pair-modules, not for the injectives.

## References

* [Stacks Project, Tag 099D](https://stacks.math.columbia.edu/tag/099D)
* [Stacks Project, Tag 01DV](https://stacks.math.columbia.edu/tag/01DV)
* [Stacks Project, Tag 07GE](https://stacks.math.columbia.edu/tag/07GE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace Stacks.PairSite

/-- The polynomial ring `ℤ[x₁, …, xₙ]` in which the pairs below are presented. The coefficients
are `ULift.{u} ℤ` rather than `ℤ` so that the ring lives in the universe `u` in which
`Stacks.LocalCohomology.FunctorialCechData.{u}` quantifies over rings. -/
abbrev presentationRing (n : ℕ) : Type u := MvPolynomial (Fin n) (ULift.{u} ℤ)

/-- The ring `ULift ℤ` is Noetherian. -/
instance isNoetherianRing_uliftInt : IsNoetherianRing (ULift.{u} ℤ) :=
  isNoetherianRing_of_ringEquiv ℤ ULift.ringEquiv.symm

/-- **A presented pair.** A finite-type `ℤ`-algebra given by a presentation
`ℤ[x₁, …, xₙ]/J`, together with an ideal of it. Every ideal of such a ring is finitely
generated (`Stacks.PairSite.Pair.ideal_fg`), so no finiteness hypothesis is carried. -/
structure Pair : Type u where
  /-- The number of variables in the presentation. -/
  numVars : ℕ
  /-- The relations of the presentation. -/
  relations : Ideal (presentationRing.{u} numVars)
  /-- The distinguished ideal of the pair. -/
  ideal : Ideal (presentationRing.{u} numVars ⧸ relations)

namespace Pair

/-- The ring of a presented pair. -/
abbrev ring (P : Pair.{u}) : Type u := presentationRing.{u} P.numVars ⧸ P.relations

/-- The ring of a pair is Noetherian. -/
instance (P : Pair.{u}) : IsNoetherianRing P.ring :=
  inferInstanceAs (IsNoetherianRing (presentationRing.{u} P.numVars ⧸ P.relations))

/-- The distinguished ideal of a pair is finitely generated: the ring of a pair is Noetherian. -/
theorem ideal_fg (P : Pair.{u}) : P.ideal.FG := IsNoetherian.noetherian _

/-- The ring of a pair is a finite-type `ℤ`-algebra: this is what makes the category below
the category of pairs `(A₀, I₀)` with `A₀` of finite type over `ℤ`. -/
instance (P : Pair.{u}) : Algebra.FiniteType ℤ P.ring := by
  have h₁ : Algebra.FiniteType ℤ (ULift.{u} ℤ) := by
    have he : (algebraMap ℤ (ULift.{u} ℤ) : ℤ →+* ULift.{u} ℤ) =
        ULift.ringEquiv.symm.toRingHom := RingHom.ext_int _ _
    refine ⟨⟨∅, le_antisymm le_top fun z _ => ?_⟩⟩
    have hz : z = algebraMap ℤ (ULift.{u} ℤ) z.down := by rw [he]; rfl
    rw [hz]
    exact Subalgebra.algebraMap_mem _ _
  have h₃ := Algebra.FiniteType.trans h₁
    (inferInstance : Algebra.FiniteType (ULift.{u} ℤ) (presentationRing.{u} P.numVars))
  exact Algebra.FiniteType.quotient ℤ P.relations

/-- **A morphism of pairs**: a ring map carrying the ideal of the source *onto* the ideal of the
target, `J₀ = I₀.map φ`. The equality is on the nose, not an inclusion: it is what makes the
ideal `(A₀, I₀) ↦ I₀` a subpresheaf of the structure presheaf and what tag 099D's `IB`
is. -/
structure Hom (P Q : Pair.{u}) where
  /-- The underlying ring map. -/
  toRingHom : P.ring →+* Q.ring
  /-- The ideal of the target is the image of the ideal of the source. -/
  map_ideal : Q.ideal = P.ideal.map toRingHom

/-- A morphism of pairs is determined by its underlying ring map. -/
theorem Hom.ext' {P Q : Pair.{u}} :
    ∀ {f g : Hom P Q}, f.toRingHom = g.toRingHom → f = g
  | ⟨_, _⟩, ⟨_, _⟩, rfl => rfl

/-- **The category of pairs.** Objects are presented pairs, morphisms are ring maps carrying
the source ideal onto the target ideal. It is a small category: `Pair.{u} : Type u` and both
objects and morphisms live in `Type u`. -/
instance : Category.{u, u} Pair.{u} where
  Hom P Q := Hom P Q
  id P := ⟨RingHom.id P.ring, (Ideal.map_id P.ideal).symm⟩
  comp {P Q R} f g := ⟨g.toRingHom.comp f.toRingHom, by
    rw [← Ideal.map_map, ← f.map_ideal, ← g.map_ideal]⟩
  id_comp f := Hom.ext' (RingHom.comp_id f.toRingHom)
  comp_id f := Hom.ext' (RingHom.id_comp f.toRingHom)
  assoc f g h := Hom.ext' (RingHom.comp_assoc f.toRingHom g.toRingHom h.toRingHom).symm

/-- The ring map underlying the identity of a pair is the identity. -/
@[simp]
theorem id_toRingHom (P : Pair.{u}) : Hom.toRingHom (𝟙 P) = RingHom.id P.ring := rfl

/-- The ring map underlying a composite of morphisms of pairs is the composite of ring maps. -/
@[simp]
theorem comp_toRingHom {P Q R : Pair.{u}} (f : P ⟶ Q) (g : Q ⟶ R) :
    (f ≫ g).toRingHom = g.toRingHom.comp f.toRingHom := rfl

/-- The ring map underlying `f ≫ g` sends `x` to `g (f x)`. -/
@[simp]
theorem comp_toRingHom_apply {P Q R : Pair.{u}} (f : P ⟶ Q) (g : Q ⟶ R) (x : P.ring) :
    (f ≫ g).toRingHom x = g.toRingHom (f.toRingHom x) := rfl

/-- A morphism of pairs carries the ideal of the source into the ideal of the target. -/
theorem Hom.map_mem_ideal {P Q : Pair.{u}} (f : Hom P Q) {x : P.ring} (hx : x ∈ P.ideal) :
    f.toRingHom x ∈ Q.ideal := f.map_ideal ▸ Ideal.mem_map_of_mem _ hx

/-- A morphism of pairs carries each power of the ideal of the source *onto* the corresponding
power of the ideal of the target. This is what makes the `ℐ`-power-torsion condition stable
under restriction. -/
theorem Hom.map_ideal_pow {P Q : Pair.{u}} (f : Hom P Q) (n : ℕ) :
    Q.ideal ^ n = (P.ideal ^ n).map f.toRingHom := by
  rw [Ideal.map_pow, f.map_ideal]

/-- A pair, read as an index for the values of a presheaf on the site of pairs. The site is
`Pairᵒᵖ`, so presheaves on it are indexed by `Pairᵒᵖᵒᵖ`; nothing below mentions this double
opposite except through `Pair.ix` and `Pair.Hom.ix`. -/
abbrev ix (P : Pair.{u}) : Pair.{u}ᵒᵖᵒᵖ := op (op P)

/-- A morphism of pairs, read as a morphism of indices for a presheaf on the site of pairs.
Note that it goes the same way as the morphism of pairs: a presheaf on `Pairᵒᵖ` is a
*covariant* functor on pairs. -/
abbrev Hom.ix {P Q : Pair.{u}} (f : P ⟶ Q) : P.ix ⟶ Q.ix := (Quiver.Hom.op f).op

/-- The index morphism of the identity of a pair is the identity. -/
@[simp]
theorem Hom.ix_id (P : Pair.{u}) : Hom.ix (𝟙 P) = 𝟙 P.ix := rfl

/-- The index morphism of a composite is the composite of the index morphisms. -/
@[simp]
theorem Hom.ix_comp {P Q R : Pair.{u}} (f : P ⟶ Q) (g : Q ⟶ R) :
    Hom.ix (f ≫ g) = Hom.ix f ≫ Hom.ix g := rfl

end Pair

/-! ### The structure presheaf of rings -/

/-- **The ring of a pair, functorially**: the covariant functor `(A₀, I₀) ↦ A₀` on the category
of pairs. -/
def ringFunctor : Pair.{u} ⥤ RingCat.{u} where
  obj P := RingCat.of P.ring
  map f := RingCat.ofHom f.toRingHom
  map_id _ := rfl
  map_comp _ _ := rfl

/-- **The structure presheaf of rings on the site of pairs**, `(A₀, I₀) ↦ A₀`. This is
`ringFunctor` read as a presheaf on `Pairᵒᵖ`, which is the form that Mathlib's
`PresheafOfModules` consumes. -/
def structureRings : Pair.{u}ᵒᵖᵒᵖ ⥤ RingCat.{u} :=
  unopUnop Pair.{u} ⋙ ringFunctor.{u}

/-- The value of the structure presheaf of rings at a pair is the ring of the pair. -/
@[simp]
theorem structureRings_obj (P : Pair.{u}) :
    structureRings.obj P.ix = RingCat.of P.ring := rfl

/-- The structure presheaf of rings sends a morphism of pairs to its underlying ring map. -/
@[simp]
theorem structureRings_map {P Q : Pair.{u}} (f : P ⟶ Q) :
    (structureRings.map (Pair.Hom.ix f)).hom = f.toRingHom := rfl

/-! ### Presheaves of modules on the site of pairs -/

/-- **A presheaf of modules on the category of pairs.** By construction a `PairModule` `M`
assigns to a pair `(A₀, I₀)` an `A₀`-module `M.value (A₀, I₀)` and to a morphism of pairs
`φ : (A₀, I₀) ⟶ (B₀, J₀)` an `A₀`-linear map `M.value (A₀, I₀) ⟶ M.value (B₀, J₀)`, these maps
composing strictly (`PairModule.restriction_comp`). That is the datum tag 099D asks for, in
each degree. -/
abbrev PairModule : Type (u + 1) := PresheafOfModules.{u} structureRings.{u}

namespace PairModule

/-- The value of a presheaf of modules on pairs at a pair: a module over the pair's ring. -/
abbrev value (M : PairModule.{u}) (P : Pair.{u}) : ModuleCat.{u} P.ring := M.obj P.ix

/-- **Evaluation at a pair**, as a functor `PairModule ⥤ ModuleCat A₀`. It preserves colimits
of every shape (`PresheafOfModules.evaluation_preservesColimitsOfSize`), so a filtered colimit
of pair-modules is computed pair by pair. -/
abbrev evaluation (P : Pair.{u}) : PairModule.{u} ⥤ ModuleCat.{u} P.ring :=
  PresheafOfModules.evaluation structureRings.{u} P.ix

/-- **The restriction map of a presheaf of modules on pairs**, along a morphism of pairs
`f : P ⟶ Q`: a map of `P.ring`-modules from the value at `P` to the value at `Q`, the latter
read as a `P.ring`-module along `f`. This is the shape of the datum (3) of tag 099D. -/
abbrev restriction (M : PairModule.{u}) {P Q : Pair.{u}} (f : P ⟶ Q) :
    M.value P ⟶ (ModuleCat.restrictScalars f.toRingHom).obj (M.value Q) :=
  M.map (Pair.Hom.ix f)

/-- Restriction along the identity of a pair is the identity, as a map of modules. -/
theorem restriction_id (M : PairModule.{u}) (P : Pair.{u}) :
    M.restriction (𝟙 P) =
      (ModuleCat.restrictScalarsId' (RingHom.id P.ring) rfl).inv.app (M.value P) :=
  M.map_id P.ix

/-- Restriction along the identity of a pair fixes every element. -/
@[simp]
theorem restriction_id_apply (M : PairModule.{u}) (P : Pair.{u}) (m : M.value P) :
    M.restriction (𝟙 P) m = m := by
  rw [restriction_id]
  rfl

/-- **The restriction maps compose strictly.** Pointwise form; the hom-level form is
`restriction_comp`. -/
@[simp]
theorem restriction_comp_apply (M : PairModule.{u}) {P Q R : Pair.{u}} (f : P ⟶ Q) (g : Q ⟶ R)
    (m : M.value P) :
    M.restriction (f ≫ g) m = M.restriction g (M.restriction f m) :=
  M.map_comp_apply (Pair.Hom.ix f) (Pair.Hom.ix g) m

/-- A morphism of pair-modules commutes with the restriction maps. -/
@[simp]
theorem naturality_apply {M N : PairModule.{u}} (α : M ⟶ N) {P Q : Pair.{u}} (f : P ⟶ Q)
    (m : M.value P) :
    PresheafOfModules.Hom.app α Q.ix (M.restriction f m) =
      N.restriction f (PresheafOfModules.Hom.app α P.ix m) :=
  PresheafOfModules.naturality_apply α (Pair.Hom.ix f) m

/-- **The restriction maps of a presheaf of modules on pairs compose on the nose.** This is
condition (b) of tag 099D (`Stacks.LocalCohomology.FunctorialCechData.map_map`) for a single
degree: the equality is between maps of complexes, not a commutativity in a derived category,
and it is available here because the restriction maps are the structure maps of a functor on
pairs rather than comparisons between Čech complexes of different generating families. -/
theorem restriction_comp (M : PairModule.{u}) {P Q R : Pair.{u}} (f : P ⟶ Q) (g : Q ⟶ R) :
    M.restriction (f ≫ g) =
      M.restriction f ≫ (ModuleCat.restrictScalars f.toRingHom).map (M.restriction g) ≫
        (ModuleCat.restrictScalarsComp' f.toRingHom g.toRingHom
          (g.toRingHom.comp f.toRingHom) rfl).inv.app (M.value R) :=
  M.map_comp (Pair.Hom.ix f) (Pair.Hom.ix g)

end PairModule

/-! ### The structure presheaf as a module, and the ideal subpresheaf -/

/-- **The structure presheaf of pairs, as a presheaf of modules over itself**: the pair-module
`(A₀, I₀) ↦ A₀`. -/
abbrev structureModule : PairModule.{u} := PresheafOfModules.unit structureRings.{u}

/-- Restriction in the structure presheaf along a morphism of pairs is its underlying ring map. -/
@[simp]
theorem structureModule_restriction_apply {P Q : Pair.{u}} (f : P ⟶ Q) (x : P.ring) :
    structureModule.restriction f x = f.toRingHom x := rfl

/-- **The ideal of a pair, as a subpresheaf of the structure presheaf**: the family of ideals
`(A₀, I₀) ↦ I₀`, stable under restriction because a morphism of pairs carries `I₀` into
`J₀` (indeed onto it). This is what makes "the pair's ideal" an object of the type that a
complex of pair-modules can be torsion for. -/
def idealSubmodule : structureModule.{u}.Submodule where
  obj X := X.unop.unop.ideal
  map {X Y} f := by
    intro x hx
    change f.unop.unop.toRingHom x ∈ Y.unop.unop.ideal
    rw [f.unop.unop.map_ideal]
    exact Ideal.mem_map_of_mem _ hx

/-- An element of the ring of a pair lies in the value of the ideal subpresheaf exactly when it
lies in the ideal of the pair. -/
@[simp]
theorem mem_idealSubmodule_obj (P : Pair.{u}) (x : P.ring) :
    x ∈ idealSubmodule.{u}.obj P.ix ↔ x ∈ P.ideal := Iff.rfl

/-- **The ideal subpresheaf as a presheaf of modules on pairs**: `(A₀, I₀) ↦ I₀`, an object of
`PairModule`. -/
abbrev idealModule : PairModule.{u} := idealSubmodule.{u}.toPresheafOfModules

/-- The inclusion `ℐ ⟶ 𝒪` of the ideal subpresheaf into the structure presheaf; it is a
monomorphism of pair-modules. -/
abbrev idealInclusion : idealModule.{u} ⟶ structureModule.{u} := idealSubmodule.{u}.ι

/-- The inclusion of the ideal subpresheaf into the structure presheaf is a monomorphism. -/
instance : Mono idealInclusion.{u} := inferInstanceAs (Mono idealSubmodule.{u}.ι)

/-- The value of the ideal subpresheaf at a pair is the pair's ideal. -/
theorem idealModule_value (P : Pair.{u}) :
    idealModule.{u}.value P = ModuleCat.of P.ring P.ideal := rfl

/-! ### Abelianness, colimits, injectives

`PairModule` inherits from Mathlib everything a complex of pair-modules needs: it is abelian
(`PresheafOfModules.instAbelian`), it has colimits of every shape — in particular filtered
ones — (`PresheafOfModules.hasColimitsOfSize`), and evaluation at a pair preserves them
(`PresheafOfModules.evaluation_preservesColimitsOfSize`), so a filtered colimit of
pair-modules may be computed pairwise. Only the injectives need a result from this
repository. -/

/-- **Presheaves of modules on pairs have functorial injective embeddings** (Stacks 01DV);
all three universes of `Stacks.Injectives.presheafOfModules_hasFunctorialInjectiveEmbeddings`
coincide here, because the site of pairs is small and its structure presheaf of rings lands in
the same universe. -/
theorem hasFunctorialInjectiveEmbeddings_pairModule :
    HasFunctorialInjectiveEmbeddings PairModule.{u} :=
  Stacks.Injectives.presheafOfModules_hasFunctorialInjectiveEmbeddings
    Pair.{u}ᵒᵖ structureRings.{u}

/-- **Presheaves of modules on pairs have enough injectives.** -/
theorem enoughInjectives_pairModule : EnoughInjectives PairModule.{u} :=
  enoughInjectives_of_hasFunctorialInjectiveEmbeddings _
    hasFunctorialInjectiveEmbeddings_pairModule.{u}

/-! ### The chaotic topology

A presheaf is a sheaf for the chaotic (bottom) topology (Stacks 07GE, `Presheaf.isSheaf_bot`),
so sheaves of modules on a small site carrying the chaotic topology are just presheaves of
modules. This is what lets a result stated only for sheaves of modules — on a ringed site, say
— be applied to pair-modules. The statement is `private` in
`StacksFrontier/Homology/Injectives/Sheaf/PresheavesOfModules.lean`, so it is proved again here,
publicly. -/

/-- **Sheaves of modules for the chaotic topology on a small site are presheaves of modules.**
Both functors are the identity on underlying data. -/
def sheafOfModulesBotEquiv {C : Type u} [SmallCategory C] (R : Cᵒᵖ ⥤ RingCat.{u}) :
    SheafOfModules.{u} (⟨R, Presheaf.isSheaf_bot R⟩ : Sheaf (⊥ : GrothendieckTopology C) _) ≌
      PresheafOfModules.{u} R where
  functor := SheafOfModules.forget _
  inverse :=
    { obj := fun M => ⟨M, Presheaf.isSheaf_bot M.presheaf⟩
      map := fun f => ⟨f⟩ }
  unitIso := NatIso.ofComponents (fun _ => Iso.refl _)
  counitIso := NatIso.ofComponents (fun _ => Iso.refl _)

/-- **Pair-modules are the sheaves of modules on the chaotically topologized site of pairs.** -/
def sheafOfModulesChaoticEquiv :
    SheafOfModules.{u} (⟨structureRings.{u}, Presheaf.isSheaf_bot _⟩ :
        Sheaf (⊥ : GrothendieckTopology Pair.{u}ᵒᵖ) _) ≌
      PairModule.{u} :=
  sheafOfModulesBotEquiv structureRings.{u}

/-! ### Presenting a pair inside a given ring

Tag 099D's `K(A, I)` is to be read off from the pairs mapping into `(A, I)`, and `A` itself is
not an object of `Pair`. The constructions below are the bridge: a finite family of elements of
`A` and a finite family of polynomials in those variables present a pair whose ring embeds in
`A`, carrying the pair's ideal onto the ideal of `A` generated by the evaluated polynomials. -/

namespace Pair

variable {A : Type u} [CommRing A]

/-- The ring map `ℤ[x₁, …, xₙ] → A` sending `xᵢ` to `x i`. -/
def eval {n : ℕ} (x : Fin n → A) : presentationRing.{u} n →+* A :=
  MvPolynomial.eval₂Hom ((Int.castRingHom A).comp (ULift.ringEquiv.toRingHom)) x

/-- The ring map `eval x` sends the variable `xᵢ` to `x i`. -/
@[simp]
theorem eval_X {n : ℕ} (x : Fin n → A) (i : Fin n) : eval x (MvPolynomial.X i) = x i := by
  simp [eval]

/-- **The pair presented by a finite family of elements of `A` and a finite family of
polynomials.** Its ring is `ℤ[x₁, …, xₙ]` modulo the relations satisfied by `x` in `A`, so it
is the `ℤ`-subalgebra of `A` generated by the `x i` (see `ofEvalHom_injective`), and its ideal
is generated by the classes of the `y j`. -/
def ofEval {n m : ℕ} (x : Fin n → A) (y : Fin m → presentationRing.{u} n) : Pair.{u} where
  numVars := n
  relations := RingHom.ker (eval x)
  ideal := (Ideal.span (Set.range y)).map (Ideal.Quotient.mk (RingHom.ker (eval x)))

/-- The number of variables of `ofEval x y` is the length of the family `x`. -/
@[simp]
theorem ofEval_numVars {n m : ℕ} (x : Fin n → A) (y : Fin m → presentationRing.{u} n) :
    (ofEval x y).numVars = n := rfl

/-- The relations of `ofEval x y` are the kernel of `eval x`. -/
@[simp]
theorem ofEval_relations {n m : ℕ} (x : Fin n → A) (y : Fin m → presentationRing.{u} n) :
    (ofEval x y).relations = RingHom.ker (eval x) := rfl

/-- The ring of `ofEval x y` is `ℤ[x₁, …, xₙ]` modulo the kernel of `eval x`. -/
theorem ofEval_ring {n m : ℕ} (x : Fin n → A) (y : Fin m → presentationRing.{u} n) :
    (ofEval x y).ring = (presentationRing.{u} n ⧸ RingHom.ker (eval x)) := rfl

/-- The injection of the ring of `ofEval x y` into `A`, exhibiting it as the `ℤ`-subalgebra of
`A` generated by the `x i`. -/
def ofEvalHom {n : ℕ} (x : Fin n → A) : (presentationRing.{u} n ⧸ RingHom.ker (eval x)) →+* A :=
  RingHom.kerLift (eval x)

/-- The ring map `ofEvalHom x` is injective. -/
theorem ofEvalHom_injective {n : ℕ} (x : Fin n → A) : Function.Injective (ofEvalHom x) :=
  RingHom.kerLift_injective _

/-- The map `ofEvalHom x` sends the class of a polynomial `p` to `eval x p`. -/
@[simp]
theorem ofEvalHom_mk {n : ℕ} (x : Fin n → A) (p : presentationRing.{u} n) :
    ofEvalHom x (Ideal.Quotient.mk (RingHom.ker (eval x)) p) = eval x p := rfl

/-- The composite of the quotient map with `ofEvalHom x` is `eval x`. -/
theorem ofEvalHom_comp_mk {n : ℕ} (x : Fin n → A) :
    (ofEvalHom x).comp (Ideal.Quotient.mk (RingHom.ker (eval x))) = eval x :=
  RingHom.ext fun _ => rfl

/-- The ideal of `ofEval x y`, pushed into `A`, is the ideal generated by the evaluations of
the `y j`. This is what makes `ofEval x y` a pair *over* `(A, span (eval x ∘ y))`. -/
theorem map_ideal_ofEvalHom {n m : ℕ} (x : Fin n → A) (y : Fin m → presentationRing.{u} n) :
    (ofEval x y).ideal.map (ofEvalHom x) = Ideal.span (Set.range fun j => eval x (y j)) := by
  change ((Ideal.span (Set.range y)).map
    (Ideal.Quotient.mk (RingHom.ker (eval x)))).map (ofEvalHom x) = _
  rw [Ideal.map_map, ofEvalHom_comp_mk, Ideal.map_span, ← Set.range_comp]
  rfl

end Pair

end Stacks.PairSite

end
