module

public import Mathlib.Algebra.Category.Grp.Ulift
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.Limits
public import Mathlib.Algebra.Category.ModuleCat.Ulift
public import Mathlib.Algebra.Homology.Additive
public import Mathlib.Algebra.Homology.CochainComplexPlus
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.CategoryTheory.Sites.Point.Comap
public import Mathlib.CategoryTheory.Sites.Point.OfIsCofiltered
public import Mathlib.CategoryTheory.Sites.Point.Over
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatStalk
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorExactness
public import StacksFrontier.Algebra.Homology.HomotopyCategory.Minus
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GeometricPointStalkMap
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Sweep.EtaleStalkFunctor
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.Limits
public import StacksFrontier.CategoryTheory.Sites.Modules.FlatMorphisms.RingedSites
public import StacksFrontier.Homology.Perfect.Defs

/-!
# Sheaves of modules over the constant coefficient ring on a small étale site

Fix a coefficient ring `Λ` and a scheme `X` in a big étale site `B`. A sheaf of `Λ`-modules on
the small étale site of `X` carries an action of the *locally constant* `Λ`-valued functions,
not merely of the constant ones: the constant presheaf of rings sheafifies, and the module
action extends across that sheafification. This file builds the resulting sheaf of modules over
the constant coefficient ring sheaf, and the stalk of such a sheaf at a geometric point, as a
functor and degreewise on complexes.

The construction lifts the coefficients and the module sections into one universe containing
the site, leaving the scheme universe, the coefficient universe and the module universe
independent of each other. The map from the constant presheaf of rings to the sheafified one
is locally bijective, which is what lets `PresheafOfModules.sheafification` be applied to it.

The file closes with the structure of those stalks for a bounded complex of *constructible*
sheaves of modules which are flat over the constant coefficient ring sheaf. A constructible
sheaf is finite locally constant after inverse image to each stratum of a constructible
stratification of an affine open; a geometric point lands in one stratum, the stalk is unchanged
by passing to that stratum, and over the stratum the stalk is the finite value of the locally
constant sheaf. Flatness of the stalk over `Λ` comes from flatness of the stalk over the stalk
of the constant coefficient ring sheaf, which is `Λ` itself. A finite flat module over a
Noetherian ring is projective, so the stalk complex is a bounded complex of finite projective
modules, hence perfect.

## Main definitions

* `AlgebraicGeometry.constantCoefficientSheaf` — the constant coefficient ring sheaf on the
  small étale site, with coefficients lifted into the site's universe.
* `AlgebraicGeometry.constantCoefficientRingMap` — the comparison from the constant presheaf
  of rings to the underlying ring presheaf of that sheaf.
* `AlgebraicGeometry.modulePresheafOverConstantCoefficients` — a sheaf of `Λ`-modules read as a
  presheaf of modules over the constant presheaf of rings.
* `AlgebraicGeometry.moduleSheafOverConstantCoefficients` — its sheafification, a sheaf of
  modules over `constantCoefficientSheaf`.
* `AlgebraicGeometry.etaleModuleStalkFunctor` — the module-valued stalk at a geometric point of
  the small étale site.
* `AlgebraicGeometry.etaleModuleStalkComplex` — that stalk applied degreewise to a cochain
  complex of sheaves of modules.

## Main results

* `AlgebraicGeometry.SheafOfModules.wEqualsLocallyBijective_commRingCat` — on any site, the
  sheafification equivalences of presheaves of commutative rings are exactly the locally
  bijective morphisms, in any universe of sections containing the site.
* `AlgebraicGeometry.stalk_finite` — every term of the stalk of a complex of constructible
  sheaves of `Λ`-modules is a finite `Λ`-module.
* `AlgebraicGeometry.stalk_projective` — if those sheaves are moreover flat over the constant
  coefficient ring sheaf, every term of the stalk is a projective `Λ`-module.
* `AlgebraicGeometry.stalk_isPerfect_of_finite_projective` — a bounded complex whose stalk
  modules are finite and projective has a perfect stalk complex.
* `AlgebraicGeometry.stalk_isPerfect` — the stalk of a bounded such complex is a perfect object
  of the derived category of `Λ`-modules.

## Implementation notes

**The coefficient ring.**  The file is in three parts, by what each needs of `Λ`. The constant
coefficient ring sheaf and the sheaves of modules over it are formed for a *commutative* `Λ`:
they are the structure sheaf of the ringed site of Tag 03TR and its modules, and the structure
sheaf of an `AlgebraicGeometry.RingedSite` takes values in `CommRingCat`. The stalk of a sheaf
of `Λ`-modules, its finiteness for a stratumwise finite-type locally constant sheaf, and the
perfection criterion `AlgebraicGeometry.stalk_isPerfect_of_finite_projective` need only that `Λ`
be a ring, possibly noncommutative, and are stated that way: that is the generality the trace
material of Tag 03TX needs, where `Λ` is a finite ring such as the group ring `(ℤ/ℓⁿℤ)[G]` of a
finite group. Flatness returns to a commutative Noetherian `Λ` — Mathlib's `Module.Flat` is
available over a commutative ring, and `Stacks.SheafOfModules.IsFlat` is exactness of a tensor
product of sheaves of modules — so `AlgebraicGeometry.stalk_projective` and
`AlgebraicGeometry.stalk_isPerfect` are the commutative statements. The route to perfection that
avoids flatness, through local constancy with finite projective values, is
`AlgebraicGeometry.stalk_isPerfect_of_isConstructibleFlatModuleSheaf` and holds for a general
ring.

Correspondingly `AlgebraicGeometry.stalk_finite` takes stratumwise local constancy with
finitely generated values as its hypothesis rather than
`AlgebraicGeometry.IsConstructibleModuleSheaf`, which is the same condition but defined — as in
Tag 03RW part (3) — for a Noetherian commutative ring only; the two are definitionally equal
whenever both are available.

Sheafification of presheaves of commutative rings and of abelian groups in a universe of
sections larger than the site is provided by the lemmas
`AlgebraicGeometry.SheafOfModules.hasSheafify_commRingCat`,
`CategoryTheory.GrothendieckTopology.hasSheafify_addCommGrpCat`,
`AlgebraicGeometry.SheafOfModules.wEqualsLocallyBijective_addCommGrpCat` and
`AlgebraicGeometry.SheafOfModules.wEqualsLocallyBijective_commRingCat`. They are *lemmas*
rather than global instances: Mathlib's own instance for the small étale site covers only
coefficients in `Type u`-sized categories, and the étale cohomology files carry sheafification
as hypotheses. Here the four facts are installed as `local instance`s.

The module presheaf is built by hand from the composite
`F.obj ⋙ ModuleCat.uliftFunctor ⋙ ModuleCat.restrictScalars` rather than by a functor
construction, because the restriction of scalars is along the ring equivalence
`ULift.ringEquiv` and the resulting `PresheafOfModules` needs its `map_id` and `map_comp`
fields checked elementwise.

The stalk of a module sheaf is formed in the module universe `w`, which is unrelated to the
universe `u` of the schemes, so the colimit defining it is not a priori a `u`-small one. The
proof of `stalk_finite` observes that a nonzero object of `ModuleCat.{w} Λ` with `u`-indexed
coproducts forces `UnivLE.{u, w}`, and discharges the stalk of a zero module separately; this
is why no universe inequality appears in the statement.

## References

* [Stacks Project, Tag 03TR](https://stacks.math.columbia.edu/tag/03TR)
* [Stacks Project, Tag 03ER](https://stacks.math.columbia.edu/tag/03ER)
* [Stacks Project, Tag 04FN](https://stacks.math.columbia.edu/tag/04FN)
* [Stacks Project, Tag 05VB](https://stacks.math.columbia.edu/tag/05VB)
* [Stacks Project, Tag 0657](https://stacks.math.columbia.edu/tag/0657)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u w r

namespace AlgebraicGeometry.SheafOfModules

/-- Sheafification equivalences of presheaves of commutative rings are exactly the locally
bijective morphisms, in every universe of sections containing the site. The companion of
`AlgebraicGeometry.SheafOfModules.hasSheafify_commRingCat`. -/
lemma wEqualsLocallyBijective_commRingCat.{z, u', v'}
    {C : Type u'} [Category.{v'} C] (J : GrothendieckTopology C)
    [UnivLE.{u', z}] [UnivLE.{v', z}] :
    J.WEqualsLocallyBijective CommRingCat.{z} :=
  GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall.{v', z, u', z + 1, z} J

end AlgebraicGeometry.SheafOfModules

namespace AlgebraicGeometry

/-! ### Fibres of constant sheaves and of inverse images

The three isomorphisms below are the general site-theoretic input to `stalk_finite`: the fibre
of a constant sheaf is its value, the fibre of an inverse image to a slice site is the fibre
of the original sheaf, and the fibre functor of a point transports along an isomorphism of
fibre functors through a continuous morphism of sites. -/

section

universe z uC vC uD vD uA vA

variable {C : Type uC} [Category.{vC} C] {J : GrothendieckTopology C}

/-- The fibre at a point of a site of the constant sheaf with value `M` is `M` itself. The
neighbourhoods of a point are cofiltered, hence connected, so the colimit of the constant
presheaf is `M`, and the fibre functor does not distinguish a presheaf from its
sheafification. -/
private def constantSheafFiberIso (p : J.Point.{z})
    {A : Type uA} [Category.{vA} A] [HasProducts.{z} A] [HasColimitsOfSize.{z, z} A]
    [HasWeakSheafify J A] (M : A) :
    p.sheafFiber.obj ((constantSheaf J A).obj M) ≅ M := by
  have : IsConnected p.fiber.Elementsᵒᵖ := IsFiltered.isConnected _
  exact (p.presheafToSheafCompSheafFiberIso A).app ((Functor.const _).obj M) ≪≫
    ((isColimitConstCocone p.fiber.Elementsᵒᵖ M).coconePointUniqueUpToIso
      (p.isColimitPresheafFiberCocone ((Functor.const _).obj M))).symm

/-- An element of the subfunctor of lifts of `x` over an object of `Over X` is the same datum as
an object of the category of elements of `F` equipped with a morphism to `x`. -/
private def overFunctorElementsEquivalence (F : C ⥤ Type z) {Y : C} (x : F.obj Y) :
    (FunctorToTypes.fromOverFunctor F x).Elements ≌ Over (F.elementsMk Y x) where
  functor.obj u := Over.mk (Functor.Elements.homMk (x := F.elementsMk u.obj.left u.val.1)
    (y := F.elementsMk Y x) u.obj.hom
    ((FunctorToTypes.mem_fromOverSubfunctor_iff _ _ _).mp u.val.2))
  functor.map f := Over.homMk
    (Functor.Elements.homMk f.hom.left (Subtype.ext_iff.1 f.map_val))
    (Functor.Elements.hom_ext (Over.w f.hom))
  inverse.obj u := Functor.elementsMk _ (Over.mk u.hom.hom)
    ⟨u.left.val, (FunctorToTypes.mem_fromOverSubfunctor_iff _ _ _).mpr u.hom.map_val⟩
  inverse.map f := Functor.Elements.homMk
    (Over.homMk f.left.hom (congrArg Functor.Elements.Hom.hom (Over.w f)))
    (Subtype.ext f.left.map_val)
  unitIso := Iso.refl _
  counitIso := Iso.refl _
  functor_unitIso_comp u := Over.OverMorphism.ext (Functor.Elements.hom_ext (Category.comp_id _))

/-- The fibre, at the point of a slice site induced by a lift `x` of a point `p` to `U`, of the
inverse image of a sheaf to that slice site is the fibre of the sheaf at `p`. The pointed
neighbourhoods of the lift are cofinal among those of `p`. -/
private def overPullbackSheafFiberIso [LocallySmall.{z} C] (p : J.Point.{z})
    {U : C} (x : p.fiber.obj U)
    {A : Type uA} [Category.{vA} A] [HasColimitsOfSize.{z, z} A] (F : Sheaf J A) :
    (p.over x).sheafFiber.obj ((J.overPullback A U).obj F) ≅ p.sheafFiber.obj F :=
  Functor.Final.colimitIso
    ((overFunctorElementsEquivalence p.fiber x).functor ⋙
      Over.forget (p.fiber.elementsMk U x)).op
    ((Functor.Elements.π p.fiber).op ⋙ F.obj)

/-- A continuous functor `G` of sites, together with an isomorphism between the fibre functor of
a point `q` of the target pulled back along `G` and the fibre functor of a point `p` of the
source, identifies ANY left adjoint of the direct image along `G`, followed by the fibre at `q`,
with the fibre at `p`. Both are left adjoints of the skyscraper functor at the relevant point, and
the isomorphism of fibre functors makes the two skyscraper functors agree.  The inverse image is
the case `L = G.sheafPullback A J K`. -/
public def sheafFiberIsoOfAdjOfFiberIso {D : Type uD} [Category.{vD} D]
    {K : GrothendieckTopology D} (p : J.Point.{z}) (q : K.Point.{z}) (G : C ⥤ D)
    [G.IsContinuous J K] (e : G ⋙ q.fiber ≅ p.fiber)
    {A : Type uA} [Category.{vA} A] [HasProducts.{z} A] [HasColimitsOfSize.{z, z} A]
    {L : Sheaf J A ⥤ Sheaf K A} (adj : L ⊣ G.sheafPushforwardContinuous A J K) :
    L ⋙ q.sheafFiber ≅ p.sheafFiber := by
  let ee := Functor.flipping.functor.mapIso
    (Functor.isoWhiskerRight (NatIso.op e.symm) (piConst (C := A)).flip)
  let e' : q.skyscraperSheafFunctor ⋙ G.sheafPushforwardContinuous A J K ≅
      p.skyscraperSheafFunctor := NatIso.ofComponents
    (fun M => (fullyFaithfulSheafToPresheaf J A).preimageIso (ee.app M))
    (by intro M N f; ext U; exact congrArg (fun k => k.app U) (ee.hom.naturality f))
  exact ((conjugateIsoEquiv (adj.comp q.skyscraperSheafAdjunction)
    p.skyscraperSheafAdjunction).symm e').symm

/-- The fibre of a locally constant sheaf of modules is isomorphic to one of its constant
values: a neighbourhood of the point meets a member of the trivialising cover, and over that
member the sheaf is constant. -/
public lemma exists_constantValue_iso_sheafFiber [LocallySmall.{z} C]
    (p : J.Point.{z}) (R : Type r) [Ring R]
    [HasColimitsOfSize.{z, z} (ModuleCat.{w} R)] [HasProducts.{z} (ModuleCat.{w} R)]
    [∀ U : C, HasWeakSheafify (J.over U) (ModuleCat.{w} R)]
    (Q : ModuleCat.{w} R → Prop) (F : Sheaf J (ModuleCat.{w} R))
    (hF : Stacks.ConstantSheaf.IsLocallyConstantWith R J Q F) :
    ∃ E : ModuleCat.{w} R, Q E ∧
      Nonempty (E ≅ (p.sheafFiber (A := ModuleCat.{w} R)).obj F) := by
  obtain @⟨U, x⟩ := Classical.choice (IsCofiltered.nonempty (C := p.fiber.Elements))
  obtain ⟨I, V, f, hf, hV⟩ := hF U
  obtain ⟨W, g, hg, y, hy⟩ := p.jointly_surjective _ hf x
  obtain ⟨_, k, _, ⟨i⟩, rfl⟩ := hg
  obtain ⟨M, hM, ⟨e⟩⟩ := hV i
  exact ⟨M, hM, ⟨(constantSheafFiberIso (p.over (p.fiber.map k y)) M).symm ≪≫
    (p.over (p.fiber.map k y)).sheafFiber.mapIso e ≪≫
    overPullbackSheafFiberIso p (p.fiber.map k y) F⟩⟩

/-- The fibre of a locally constant sheaf of modules with finitely generated values is a finite
module. -/
private lemma finite_sheafFiber_of_isFiniteTypeLocallyConstant [LocallySmall.{z} C]
    (p : J.Point.{z}) (R : Type r) [Ring R]
    [HasColimitsOfSize.{z, z} (ModuleCat.{w} R)] [HasProducts.{z} (ModuleCat.{w} R)]
    [∀ U : C, HasWeakSheafify (J.over U) (ModuleCat.{w} R)]
    (F : Sheaf J (ModuleCat.{w} R))
    (hF : Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant R J F) :
    Module.Finite R ((p.sheafFiber (A := ModuleCat.{w} R)).obj F) := by
  obtain ⟨M, hM, ⟨e⟩⟩ := exists_constantValue_iso_sheafFiber p R (ModuleCat.isFG R) F hF
  have : Module.Finite R M := hM
  exact Module.Finite.equiv e.toLinearEquiv

/-- A category with `z`-indexed coproducts and a single object whose identity is nonzero has
`UnivLE.{z, v}` for its universe `v` of morphisms: the coprojections into a `z`-indexed
coproduct of that object are pairwise distinct, so the index type embeds into a type of
morphisms. -/
public lemma univLE_of_coproducts {A : Type uA} [Category.{vA} A]
    [HasZeroMorphisms A] [HasCoproducts.{z} A] (M : A) (hM : 𝟙 M ≠ 0) :
    UnivLE.{z, vA} where
  small I := by
    classical
    apply small_of_injective.{vA, vA, z} (f := (fun i : I => Sigma.ι (fun _ : I => M) i :
      I → (M ⟶ ∐ (fun _ : I => M))))
    intro i j h
    by_contra hij
    let g : I → (M ⟶ M) := fun k => if k = i then 𝟙 M else 0
    exact hM (by simpa [g, Ne.symm hij] using congrArg (· ≫ Sigma.desc g) h)

/-- A nontrivial module category with `z`-indexed coproducts has `UnivLE.{z, w}`. -/
private lemma _root_.ModuleCat.univLE_of_not_subsingleton {R : Type r} [Ring R]
    [HasCoproducts.{z} (ModuleCat.{w} R)] {M : ModuleCat.{w} R} (hM : ¬Subsingleton M) :
    UnivLE.{z, w} :=
  univLE_of_coproducts M fun h => hM ⟨fun x y => (congrArg (fun f : M ⟶ M => f x) h).trans
    (congrArg (fun f : M ⟶ M => f y) h).symm⟩

end

variable (B : BigEtaleSite.{u}) (X : B.Scheme)

attribute [local instance] SheafOfModules.hasSheafify_commRingCat
  SheafOfModules.wEqualsLocallyBijective_commRingCat
  GrothendieckTopology.hasSheafify_addCommGrpCat
  SheafOfModules.wEqualsLocallyBijective_addCommGrpCat

/-! ### The constant coefficient ring sheaf

The structure sheaf of a ringed site takes values in `CommRingCat`, so the constant coefficient
ring sheaf and the sheaves of modules over it are available for a commutative `Λ` only. Nothing
about the *stalks* of a sheaf of `Λ`-modules depends on that, and the stalk section below is
stated for a general, possibly noncommutative, coefficient ring. -/

section CommutativeCoefficients

variable (Λ : Type r) [CommRing Λ]

/-- The constant coefficient ring sheaf on the small étale site of `X`. The lift places the
coefficients in a universe containing both the site and the module sections, without
restricting the universe of either. -/
@[sga "4 Vbis 4.3.0" "partial"]
abbrev constantCoefficientSheaf :
    Sheaf (SmallEtale.topology B X.obj X.property) CommRingCat.{max (u + 1) w r} :=
  (constantSheaf (SmallEtale.topology B X.obj X.property) _).obj
    (CommRingCat.of (ULift.{max (u + 1) w} Λ))

/-- The comparison from the constant presheaf of rings on the small étale site to the ring
presheaf underlying the constant coefficient ring sheaf. -/
abbrev constantCoefficientRingMap :
    (Functor.const (SmallEtale B X.obj X.property)ᵒᵖ).obj
      (RingCat.of (ULift.{max (u + 1) w} Λ)) ⟶
        (Stacks.commRingSheafToRingSheaf.{u, u + 1, max (u + 1) w r}
          (constantCoefficientSheaf.{u, w, r} B X Λ)).obj :=
  Functor.whiskerRight (toSheafify (SmallEtale.topology B X.obj X.property)
    ((Functor.const _).obj (CommRingCat.of (ULift.{max (u + 1) w} Λ))))
      (forget₂ CommRingCat RingCat)

/-- The comparison `constantCoefficientRingMap` from the constant presheaf of rings to the
constant coefficient ring sheaf is locally injective. -/
instance constantCoefficientRingMap_isLocallyInjective :
    Presheaf.IsLocallyInjective (SmallEtale.topology B X.obj X.property)
      (constantCoefficientRingMap.{u, w, r} B X Λ) := by
  apply (Presheaf.isLocallyInjective_forget_iff _ _).mp
  change Presheaf.IsLocallyInjective _ (Functor.whiskerRight (toSheafify _
    ((Functor.const _).obj (CommRingCat.of (ULift.{max (u + 1) w} Λ))))
      (forget CommRingCat))
  infer_instance

/-- The comparison `constantCoefficientRingMap` from the constant presheaf of rings to the
constant coefficient ring sheaf is locally surjective. -/
instance constantCoefficientRingMap_isLocallySurjective :
    Presheaf.IsLocallySurjective (SmallEtale.topology B X.obj X.property)
      (constantCoefficientRingMap.{u, w, r} B X Λ) := by
  apply (Presheaf.isLocallySurjective_iff_whisker_forget _ _).mpr
  change Presheaf.IsLocallySurjective _ (Functor.whiskerRight (toSheafify _
    ((Functor.const _).obj (CommRingCat.of (ULift.{max (u + 1) w} Λ))))
      (forget CommRingCat))
  infer_instance

/-- A sheaf of `Λ`-modules on the small étale site, read as a presheaf of modules over the
constant presheaf of rings: the sections are lifted into the ambient universe and the scalars
are restricted along `ULift.ringEquiv`. -/
def modulePresheafOverConstantCoefficients
    (F : Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{w} Λ)) :
    PresheafOfModules.{max (u + 1) w r}
      ((Functor.const (SmallEtale B X.obj X.property)ᵒᵖ).obj
        (RingCat.of (ULift.{max (u + 1) w} Λ))) := by
  let G := F.obj ⋙ ModuleCat.uliftFunctor.{max (u + 1) r} Λ ⋙
    ModuleCat.restrictScalars (ULift.ringEquiv.{r, max (u + 1) w} (R := Λ)).toRingHom
  exact {
    obj := G.obj
    map := fun f => G.map f
    map_id := fun U => by ext x; exact congrArg (fun f => f x) (G.map_id U)
    map_comp := fun f g => by ext x; exact congrArg (fun f => f x) (G.map_comp f g) }

/-- A sheaf of `Λ`-modules regarded as a sheaf of modules over the constant coefficient ring
sheaf. Sheafification extends the action of the constant sections to the locally constant
ones. -/
def moduleSheafOverConstantCoefficients
    (F : Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{w} Λ)) :
    SheafOfModules.{max (u + 1) w r}
      (Stacks.commRingSheafToRingSheaf.{u, u + 1, max (u + 1) w r}
        (constantCoefficientSheaf.{u, w, r} B X Λ)) :=
  (PresheafOfModules.sheafification.{max (u + 1) w r}
      (constantCoefficientRingMap.{u, w, r} B X Λ)).obj
    (modulePresheafOverConstantCoefficients B X Λ F)

end CommutativeCoefficients

/-! ### Stalks of sheaves of modules over a general coefficient ring

The coefficient ring is an arbitrary, possibly noncommutative, ring from here to the end of the
section: the stalk of a sheaf of `Λ`-modules at a geometric point, and the finiteness and
perfection statements about it, never multiply two scalars. This is the generality the trace
material needs, where `Λ` is a finite ring such as the group ring `(ℤ/ℓⁿℤ)[G]` of a finite
group. -/

section GeneralCoefficients

variable (Λ : Type r) [Ring Λ] [HasColimitsOfSize.{u, u} (ModuleCat.{w} Λ)]

/-- The module-valued stalk at a geometric point of the small étale site of `X`. -/
abbrev etaleModuleStalkFunctor (s : GeometricPoint X.obj) :
    Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{w} Λ) ⥤
      ModuleCat.{w} Λ :=
  sheafToPresheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{w} Λ) ⋙
    etaleStalkPresheafFunctor (s := s) B X.obj X.property (ModuleCat.{w} Λ)

/-- The module-valued stalk is an additive functor: the zero morphism of sheaves induces the
zero morphism on each term of the colimit defining the stalk. -/
instance etaleModuleStalkFunctor_preservesZeroMorphisms (s : GeometricPoint X.obj) :
    (etaleModuleStalkFunctor B X Λ s).PreservesZeroMorphisms where
  map_zero F G := by
    have h : (etaleModuleStalkFunctor B X Λ s).map (0 : F ⟶ G) =
        colimMap (Functor.whiskerLeft
          (Functor.Elements.π (geometricPointFiber B X.obj X.property s)).op
          ((sheafToPresheaf (SmallEtale.topology B X.obj X.property)
            (ModuleCat.{w} Λ)).map (0 : F ⟶ G))) := rfl
    rw [h]
    apply colimit.hom_ext
    intro j
    rw [ι_colimMap]
    simp only [ObjectProperty.ι_obj, Functor.comp_obj, Functor.op_obj,
      ObjectProperty.ι_map, ObjectProperty.zero_hom,
      Functor.whiskerLeft_app, zero_app, zero_comp]
    exact comp_zero.symm

/-- The complex obtained from a cochain complex of sheaves of `Λ`-modules by taking the stalk
of each term and of each differential at a geometric point. -/
def etaleModuleStalkComplex
    (s : GeometricPoint X.obj)
    (K : CochainComplex
      (Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{w} Λ)) ℤ) :
    CochainComplex (ModuleCat.{w} Λ) ℤ :=
  ((etaleModuleStalkFunctor B X Λ s).mapHomologicalComplex (.up ℤ)).obj K

/-! ### The geometric point as a point of the small étale site -/

section

variable {B X}

/-- A morphism of the small étale site is, as a morphism of schemes, the image under the site
inclusion of the morphism underlying it in the slice category. -/
private lemma smallEtale_toScheme_map {U V : SmallEtale B X.obj X.property} (f : U ⟶ V) :
    (SmallEtale.toScheme B X.obj X.property).map f = B.inclusion.map f.hom.left :=
  rfl

end

/-- The topology on a category with a cofiltered category of elements over a functor `F` whose
covering sieves are those containing, for every element of the fibre over the target, a
morphism carrying an element of the fibre over its source to it. It is an auxiliary
construction: a topology coarser than this one has jointly surjective maps on `F`-fibres, which
is the remaining axiom for a point of a site. -/
private def geometricFiberTopology.{uF, vF, zF} {C : Type uF} [Category.{vF} C]
    (F : C ⥤ Type zF) [IsCofiltered F.Elements] : GrothendieckTopology C where
  sieves U := {R | ∀ x : F.obj U, ∃ (V : C) (f : V ⟶ U), R f ∧
    ∃ y : F.obj V, F.map f y = x}
  top_mem' U x := ⟨U, 𝟙 U, trivial, x, by simp⟩
  pullback_stable' {U V} {R} f h x := by
    obtain ⟨W, g, hg, y, hy⟩ := h (F.map f x)
    let a : F.elementsMk V x ⟶ F.elementsMk U (F.map f x) := ⟨f, rfl⟩
    let b : F.elementsMk W y ⟶ F.elementsMk U (F.map f x) := ⟨g, hy⟩
    obtain ⟨Q, p, q, hpq⟩ := IsCofiltered.cospan a b
    refine ⟨Q.obj, p.hom, ?_, Q.val, p.map_val⟩
    change R (p.hom ≫ f)
    rw [show p.hom ≫ f = q.hom ≫ g from congrArg Functor.Elements.Hom.hom hpq]
    exact R.downward_closed hg q.hom
  transitive' {U} {R} hR T h x := by
    obtain ⟨V, f, hf, y, hy⟩ := hR x
    obtain ⟨W, g, hg, z, hz⟩ := h hf y
    refine ⟨W, g ≫ f, hg, z, ?_⟩
    simpa [Functor.map_comp, hz] using hy

/-- A geometric point of `X` as a point of the small étale site of `X`: its fibre functor sends
an étale neighbourhood to the set of lifts of the geometric point to it. Joint surjectivity on
fibres holds because an étale covering of a neighbourhood admits a lift of the geometric point
through one of its members, the source of the geometric point being the spectrum of a
separably closed field. -/
def geometricSitePoint (s : GeometricPoint X.obj) :
    (SmallEtale.topology B X.obj X.property).Point.{u} where
  fiber := geometricPointFiber B X.obj X.property s
  jointly_surjective {U} R h x := by
    have hle : SmallEtale.topology B X.obj X.property ≤
        geometricFiberTopology (geometricPointFiber B X.obj X.property s) := by
      apply Precoverage.toGrothendieck_le_iff_le_toPrecoverage.mpr
      intro V R hR
      obtain ⟨E, rfl, hE⟩ := hR
      intro y
      have hcover := (Scheme.presieve₀_mem_precoverage_iff _).mp hE.1
      obtain ⟨i, z, hz⟩ := hcover.1 (y.1 default)
      have hi : Etale ((SmallEtale.toScheme B X.obj X.property).map (E.f i)) := hcover.2 i
      obtain ⟨l, hl, _⟩ := Scheme.exists_fac_of_etale_of_isSepClosed
        ((SmallEtale.toScheme B X.obj X.property).map (E.f i)) y.1 z hz
      have hl' : l ≫ B.inclusion.map (E.f i).hom.left = y.1 := hl
      refine ⟨E.X i, E.f i, Sieve.ofArrows_mk _ _ i, ⟨l, ?_⟩, ?_⟩
      · change l ≫ B.inclusion.map (E.X i).obj.hom = s.hom
        rw [← Over.w (E.f i).hom, Functor.map_comp, ← Category.assoc, hl']
        exact y.2
      · exact Subtype.ext hl
    obtain ⟨V, f, hf, y, hy⟩ := hle _ h x
    exact ⟨V, f, hf, y, hy⟩

/-! ### Finiteness of the stalks of a constructible complex -/

omit [HasColimitsOfSize.{u, u} (ModuleCat.{w} Λ)] in
/-- A geometric point of `X` lies in some stratum of a constructible stratification of an affine
open neighbourhood of its image, on which the inverse image of a stratumwise locally constant
sheaf is locally constant. -/
private lemma exists_constructible_stratum_through
    [∀ (S T : B.Scheme) (f : T ⟶ S),
      ((smallEtaleBaseChange B f).sheafPushforwardContinuous
        (ModuleCat.{w} Λ) (SmallEtale.topology B S.obj S.property)
        (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
    [∀ (T : B.Scheme) (V : SmallEtale B T.obj T.property),
      HasWeakSheafify ((SmallEtale.topology B T.obj T.property).over V) (ModuleCat.{w} Λ)]
    (Q : ModuleCat.{w} Λ → Prop)
    (F : Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{w} Λ))
    (hF : IsStratifiedLocallyConstantWith B X Λ Q F) (x : X.obj) :
    ∃ U : X.obj.affineOpens, x ∈ U.1 ∧
      ∃ (σ : ConstructibleStratification B X U.1) (i : Fin σ.n),
        x ∈ Set.range (B.inclusion.map (σ.inclusion i)).base ∧
        Stacks.ConstantSheaf.IsLocallyConstantWith Λ
          (SmallEtale.topology B (σ.piece i).obj (σ.piece i).property) Q
          (((smallEtaleBaseChange B (σ.inclusion i)).sheafPullback
            (ModuleCat.{w} Λ) (SmallEtale.topology B X.obj X.property)
            (SmallEtale.topology B (σ.piece i).obj (σ.piece i).property)).obj F) := by
  obtain ⟨V, hV, hxV, _⟩ := exists_isAffineOpen_mem_and_subset
    (X := X.obj) (x := x) (U := ⊤) (by simp)
  let U : X.obj.affineOpens := ⟨V, hV⟩
  obtain ⟨σ, hσ⟩ := hF U
  have hxU : x ∈ (U : Set X.obj) := hxV
  rw [σ.covers] at hxU
  obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hxU
  exact ⟨U, hxV, σ, i, hxi, hσ i⟩

/-- A preimmersion induces an isomorphism on residue fields: the map on stalks is surjective
and the map of residue fields is injective. -/
private lemma preimmersion_residueFieldMap_isIso {Y Z : Scheme.{u}}
    (f : Y ⟶ Z) [IsPreimmersion f] (y : Y) : IsIso (f.residueFieldMap y) := by
  rw [ConcreteCategory.isIso_iff_bijective]
  constructor
  · exact (f.residueFieldMap y).hom.injective
  · intro z
    obtain ⟨b, hb⟩ : ∃ b : Y.presheaf.stalk y, IsLocalRing.residue _ b = z :=
      IsLocalRing.residue_surjective _
    obtain ⟨a, ha⟩ := f.stalkMap_surjective y b
    refine ⟨IsLocalRing.residue _ a, ?_⟩
    change IsLocalRing.ResidueField.map (f.stalkMap y).hom (IsLocalRing.residue _ a) = z
    rw [IsLocalRing.ResidueField.map_residue, ha, hb]

/-- The embedding of residue fields recorded by a morphism `l` from the spectrum of a field that
corresponds to the pair `⟨y, a⟩` is `a`, up to the identification of residue fields at `y`. -/
private lemma descResidueField_stalkClosedPointTo_of_specToEquivOfField_eq {Ω : Type u} [Field Ω]
    {Y : Scheme.{u}} (l : Spec (.of Ω) ⟶ Y) (y : Y) (a : Y.residueField y ⟶ CommRingCat.of Ω)
    (hl : Scheme.SpecToEquivOfField Ω Y l = ⟨y, a⟩) (h : l (IsLocalRing.closedPoint Ω) = y) :
    Y.descResidueField (Scheme.stalkClosedPointTo l) = (Y.residueFieldCongr h).hom ≫ a := by
  obtain ⟨hfst, hsnd⟩ := Scheme.SpecToEquivOfField_eq_iff.mp hl
  change l (IsLocalRing.closedPoint Ω) = y at hfst
  rw [Subsingleton.elim hfst h] at hsnd
  have hsource := congrArg (fun z : Y => Y.residueField z ⟶ CommRingCat.of Ω)
    (Scheme.SpecToEquivOfField_apply_fst Ω Y l)
  convert hsnd using 1
  · exact hsource.symm
  · rfl
  · exact HEq.rfl

/-- A morphism from the spectrum of a separably closed field whose image lies in the range of an
immersion factors through that immersion. The lift is the morphism to the source determined by
the point of the source and the induced embedding of its residue field. -/
private theorem exists_fac_of_isImmersion_of_mem_range {Y Z : Scheme.{u}}
    (f : Y ⟶ Z) [IsImmersion f] {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (s : Spec (.of Ω) ⟶ Z) (hs : s (default : Spec (.of Ω)) ∈ Set.range f.base) :
    ∃ l : Spec (.of Ω) ⟶ Y, l ≫ f = s := by
  obtain ⟨y, hy⟩ := hs
  let eZ := Scheme.SpecToEquivOfField Ω Z s
  have hy' : eZ.1 = f y := by
    dsimp [eZ, Scheme.SpecToEquivOfField]
    exact (congrArg s (Subsingleton.elim _ _)).trans hy.symm
  have hres : IsIso (f.residueFieldMap y) := preimmersion_residueFieldMap_isIso f y
  let aY : CommRingCat.of (Y.residueField y) ⟶ CommRingCat.of Ω :=
    (asIso (f.residueFieldMap y)).inv ≫ (Z.residueFieldCongr hy').inv ≫ eZ.2
  let l := (Scheme.SpecToEquivOfField Ω Y).symm ⟨y, aY⟩
  have hlpoint : l (IsLocalRing.closedPoint Ω) = y := by
    simpa only [l, Scheme.SpecToEquivOfField_apply_fst] using
      congrArg (fun z => z.1) ((Scheme.SpecToEquivOfField Ω Y).apply_symm_apply ⟨y, aY⟩)
  have hclosed : f (l (IsLocalRing.closedPoint Ω)) =
      s (IsLocalRing.closedPoint Ω) := by
    rw [hlpoint]
    exact hy.trans (congrArg s (Subsingleton.elim _ _))
  refine ⟨l, ?_⟩
  apply (Scheme.SpecToEquivOfField Ω Z).injective
  rw [Scheme.SpecToEquivOfField_eq_iff]
  refine ⟨hclosed, ?_⟩
  rw [Scheme.SpecToEquivOfField_apply_snd, Scheme.SpecToEquivOfField_apply_snd]
  refine (Scheme.descResidueField_stalkClosedPointTo_comp (f := f) (g := l)).trans ?_
  rw [descResidueField_stalkClosedPointTo_of_specToEquivOfField_eq l y aY
      ((Scheme.SpecToEquivOfField Ω Y).apply_symm_apply ⟨y, aY⟩) hlpoint,
    ← Category.assoc, Scheme.Hom.residueFieldMap_congr' hlpoint]
  simp only [Category.assoc, aY, asIso_inv, IsIso.hom_inv_id_assoc]
  rw [Scheme.residueFieldCongr_inv, Scheme.residueFieldCongr_trans_hom_assoc]
  rfl

/-- Base change along `f : Y ⟶ X` identifies the lifts of a geometric point `t` of `Y` to the
base-changed étale neighbourhoods with the lifts of its image in `X` to the original ones: a
lift to a fibre product is the same datum as a lift to the first factor compatible with `t`. -/
private def baseChangeFiberIso {Y : B.Scheme} (f : Y ⟶ X) (t : GeometricPoint Y.obj) :
    smallEtaleBaseChange B f ⋙ geometricPointFiber B Y.obj Y.property t ≅
      geometricPointFiber B X.obj X.property (t.map (B.inclusion.map f)) := by
  have := hasPullbacks_bigEtaleSite B
  have := preservesPullbacks_bigEtaleSiteInclusion B
  dsimp only [smallEtaleBaseChange, geometricPointFiber, SmallEtale.toScheme,
    BigEtaleOver.toScheme, ObjectProperty.lift, Functor.comp_obj, Over.pullback_obj_hom,
    Over.pullback_obj_left]
  let h (U : SmallEtale B X.obj X.property) :=
    (IsPullback.of_hasPullback U.obj.hom f).map B.inclusion
  refine NatIso.ofComponents (fun U => Equiv.toIso {
    toFun := fun a => ⟨a.1 ≫ B.inclusion.map (pullback.fst U.obj.hom f), by
      rw [Category.assoc, ← B.inclusion.map_comp, pullback.condition,
        B.inclusion.map_comp, ← Category.assoc]
      exact congrArg (fun k => k ≫ B.inclusion.map f) a.2⟩
    invFun := fun a => ⟨(h U).lift a.1 t.hom a.2, (h U).lift_snd _ _ _⟩
    left_inv := fun a => by
      apply Subtype.ext
      apply (h U).hom_ext
      · exact (h U).lift_fst _ _ _
      · exact ((h U).lift_snd _ _ _).trans a.2.symm
    right_inv := fun a => by
      apply Subtype.ext
      exact (h U).lift_fst _ _ _ }) ?_
  intro U V g
  ext a
  change (a.1 ≫ B.inclusion.map ((Over.pullback f).map g.hom).left) ≫
      B.inclusion.map (pullback.fst V.obj.hom f) =
    (a.1 ≫ B.inclusion.map (pullback.fst U.obj.hom f)) ≫ B.inclusion.map g.hom.left
  simp only [Over.pullback_map_left, Category.assoc, ← B.inclusion.map_comp,
    pullback.lift_fst]

/-- **The stalks of a stratumwise locally constant sheaf.**  A property of `Λ`-modules which
holds of the zero module and passes along isomorphisms holds of the stalk at every geometric
point of a sheaf which, on a constructible stratification of every affine open, is locally
constant with constant values satisfying it. -/
public theorem stalk_prop_of_isStratifiedLocallyConstantWith
    [∀ (S T : B.Scheme) (f : T ⟶ S),
      ((smallEtaleBaseChange B f).sheafPushforwardContinuous
        (ModuleCat.{w} Λ) (SmallEtale.topology B S.obj S.property)
        (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
    [∀ (T : B.Scheme) (V : SmallEtale B T.obj T.property),
      HasWeakSheafify ((SmallEtale.topology B T.obj T.property).over V) (ModuleCat.{w} Λ)]
    (Q : ModuleCat.{w} Λ → Prop)
    (hQiso : ∀ {E E' : ModuleCat.{w} Λ}, (E ≅ E') → Q E → Q E')
    (hQzero : ∀ E : ModuleCat.{w} Λ, Subsingleton E → Q E)
    (F : Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{w} Λ))
    (hF : IsStratifiedLocallyConstantWith B X Λ Q F) (s : GeometricPoint X.obj) :
    Q ((etaleModuleStalkFunctor B X Λ s).obj F) := by
  by_cases hM : Subsingleton ((etaleModuleStalkFunctor B X Λ s).obj F)
  · exact hQzero _ hM
  have : UnivLE.{u, w} := ModuleCat.univLE_of_not_subsingleton hM
  have : HasLimitsOfSize.{u, u} (ModuleCat.{w} Λ) := ModuleCat.hasLimitsOfSize
  obtain ⟨U, hU, σ, j, hj, hFσ⟩ :=
    exists_constructible_stratum_through B X Λ Q F hF (s.hom default)
  have := σ.isImmersion j
  obtain ⟨l, hl⟩ := exists_fac_of_isImmersion_of_mem_range
    (B.inclusion.map (σ.inclusion j)) s.hom hj
  let t : GeometricPoint (σ.piece j).obj :=
    { residueField := s.residueField, hom := l }
  let p := geometricSitePoint B X (t.map (B.inclusion.map (σ.inclusion j)))
  let q := geometricSitePoint B (σ.piece j) t
  let e := sheafFiberIsoOfAdjOfFiberIso p q (smallEtaleBaseChange B (σ.inclusion j))
    (baseChangeFiberIso B X (σ.inclusion j) t) (A := ModuleCat.{w} Λ)
    ((smallEtaleBaseChange B (σ.inclusion j)).sheafAdjunctionContinuous (ModuleCat.{w} Λ) _ _)
  obtain ⟨E, hE, ⟨eE⟩⟩ := exists_constantValue_iso_sheafFiber q Λ Q _ hFσ
  let a : GeometricPoint.Hom s (t.map (B.inclusion.map (σ.inclusion j))) :=
    ⟨𝟙 _, by simpa [t, GeometricPoint.map] using hl⟩
  have := geometricPointStalkMap_isIso B X.obj X.property a (ModuleCat.{w} Λ)
  exact hQiso (eE ≪≫ e.app F ≪≫
    (asIso (geometricPointStalkMap B X.obj X.property a (ModuleCat.{w} Λ))).app F.obj) hE

/-- Every term of the stalk at a geometric point of a complex of constructible sheaves of
`Λ`-modules is a finite `Λ`-module.

The constructibility hypothesis is spelled out as stratumwise local constancy with finitely
generated values, which is what `AlgebraicGeometry.IsConstructibleModuleSheaf` — Tag 03RW part
(3) — unfolds to; stating it this way is what makes the statement available for a coefficient
ring that is not commutative, the definition of Tag 03RW being given for a Noetherian ring. -/
@[stacks 03TR "finiteness in each degree"]
theorem stalk_finite
    [∀ (S T : B.Scheme) (f : T ⟶ S),
      ((smallEtaleBaseChange B f).sheafPushforwardContinuous
        (ModuleCat.{w} Λ) (SmallEtale.topology B S.obj S.property)
        (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
    [∀ (T : B.Scheme) (V : SmallEtale B T.obj T.property),
      HasWeakSheafify ((SmallEtale.topology B T.obj T.property).over V) (ModuleCat.{w} Λ)]
    (K : CochainComplex
      (Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{w} Λ)) ℤ)
    (hconstructible : ∀ i : ℤ,
      IsStratifiedLocallyConstantWith B X Λ (ModuleCat.isFG Λ) (K.X i))
    (s : GeometricPoint X.obj) (i : ℤ) :
    Module.Finite Λ ((etaleModuleStalkFunctor B X Λ s).obj (K.X i)) := by
  have h := stalk_prop_of_isStratifiedLocallyConstantWith B X Λ (ModuleCat.isFG Λ)
    (fun {_ _} e hE => by
      rw [ModuleCat.isFG_iff] at hE ⊢
      have := hE
      exact Module.Finite.equiv e.toLinearEquiv)
    (fun _ hE => by
      rw [ModuleCat.isFG_iff]
      have := hE
      infer_instance)
    (K.X i) (hconstructible i) s
  rwa [ModuleCat.isFG_iff] at h

/-- **The perfection criterion for a stalk complex.** The stalk at a geometric point of a bounded
complex of sheaves of `Λ`-modules is a perfect object of the derived category of `Λ`-modules as
soon as each of its stalk modules is finite and projective: the stalk functor is additive, so the
bounds on the degrees of `K` are inherited by the stalk complex, which is then a bounded complex
of finite projective modules representing it.

This is the part of [Stacks, Tag 03TR] which does not depend on *why* the stalk modules are
finite projective.  `AlgebraicGeometry.stalk_isPerfect` supplies the two from constructibility
and flatness over the constant coefficient ring sheaf, and
`AlgebraicGeometry.stalk_isPerfect_of_isConstructibleFlatModuleSheaf` supplies them from
constructible flatness. -/
theorem stalk_isPerfect_of_finite_projective
    [∀ (S T : B.Scheme) (f : T ⟶ S),
      ((smallEtaleBaseChange B f).sheafPushforwardContinuous
        (ModuleCat.{w} Λ) (SmallEtale.topology B S.obj S.property)
        (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
    [∀ (T : B.Scheme) (V : SmallEtale B T.obj T.property),
      HasWeakSheafify ((SmallEtale.topology B T.obj T.property).over V) (ModuleCat.{w} Λ)]
    (K : CochainComplex
      (Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{w} Λ)) ℤ)
    (hbounded : (CochainComplex.plus _ K) ∧ (CochainComplex.minus _ K))
    (s : GeometricPoint X.obj)
    (hfinite : ∀ i : ℤ,
      Module.Finite Λ ((etaleModuleStalkFunctor B X Λ s).obj (K.X i)))
    (hprojective : ∀ i : ℤ,
      Module.Projective Λ ((etaleModuleStalkFunctor B X Λ s).obj (K.X i)))
    [HasDerivedCategory (ModuleCat.{w} Λ)] :
    StacksDraft.Perfect.IsPerfect
      (DerivedCategory.Q.obj (etaleModuleStalkComplex B X Λ s K)) := by
  obtain ⟨a, ha⟩ := (CochainComplex.plus_iff _ K).mp hbounded.1
  obtain ⟨b, hb⟩ := (CochainComplex.minus_iff K).mp hbounded.2
  have hvanish (c : ℤ) (hc : IsZero (K.X c)) :
      IsZero ((etaleModuleStalkFunctor B X Λ s).obj (K.X c)) :=
    (etaleModuleStalkFunctor B X Λ s).map_isZero hc
  have hGE : (etaleModuleStalkComplex B X Λ s K).IsStrictlyGE a := by
    rw [CochainComplex.isStrictlyGE_iff]
    intro c hc
    exact hvanish c ((CochainComplex.isStrictlyGE_iff K a).mp ha c hc)
  have hLE : (etaleModuleStalkComplex B X Λ s K).IsStrictlyLE b := by
    rw [CochainComplex.isStrictlyLE_iff]
    intro c hc
    exact hvanish c ((CochainComplex.isStrictlyLE_iff K b).mp hb c hc)
  exact ⟨etaleModuleStalkComplex B X Λ s K, a, b, hGE, hLE, hfinite, hprojective,
    ⟨Iso.refl _⟩⟩

end GeneralCoefficients

/-! ### Flatness, projectivity and perfection of the stalks

Flatness of a stalk is measured against the constant coefficient ring sheaf of Tag 03TR, so
these results return to a commutative coefficient ring. -/

section

universe z uC vC uA vA rr

variable {C : Type uC} [Category.{vC} C] {J : GrothendieckTopology C}

/-- Flatness transfers along a ring isomorphism together with an additive isomorphism which is
semilinear over it. -/
public lemma flat_of_semilinear_equiv {R S N₀ N₁ : Type*}
    [CommRing R] [CommRing S] [AddCommGroup N₀] [AddCommGroup N₁]
    [Module R N₀] [Module S N₁] (e : R ≃+* S) (f : N₀ ≃+ N₁)
    (hf : ∀ r m, f (r • m) = e r • f m) [Module.Flat S N₁] :
    Module.Flat R N₀ := by
  apply Module.Flat.of_forall_isTrivialRelation
  intro l a x h
  have h' : ∑ i, e (a i) • f (x i) = 0 := by
    simpa only [map_sum, hf, map_zero] using congrArg f h
  obtain ⟨k, b, y, hb, hy⟩ := Module.Flat.isTrivialRelation_of_sum_smul_eq_zero h'
  refine ⟨k, fun i j => e.symm (b i j), fun j => f.symm (y j), ?_, ?_⟩
  · intro i
    apply f.injective
    simpa only [map_sum, hf, e.apply_symm_apply, f.apply_symm_apply] using hb i
  · intro j
    apply e.injective
    simpa only [map_sum, map_mul, e.apply_symm_apply, map_zero] using hy j

/-- The germ at a neighbourhood of a constant section is the inverse of
`constantSheafFiberIso`: that comparison was built from the colimit of a constant diagram, whose
coprojections are all the identity. -/
private lemma toSheafify_comp_toPresheafFiber (p : J.Point.{z})
    {A : Type uA} [Category.{vA} A] [HasProducts.{z} A] [HasColimitsOfSize.{z, z} A]
    [HasWeakSheafify J A] (T : A) (U : C) (x : p.fiber.obj U) :
    (toSheafify J ((Functor.const _).obj T)).app (op U) ≫
        p.toPresheafFiber U x ((constantSheaf J A).obj T).obj =
      (constantSheafFiberIso p T).inv := by
  refine (p.toPresheafFiber_naturality (toSheafify J ((Functor.const Cᵒᵖ).obj T)) U x).symm.trans ?_
  dsimp only [constantSheafFiberIso, Iso.trans_inv, Iso.symm_inv]
  congr 1
  exact ((isColimitConstCocone p.fiber.Elementsᵒᵖ T).comp_coconePointUniqueUpToIso_hom
    (p.isColimitPresheafFiberCocone ((Functor.const _).obj T))
      (op (p.fiber.elementsMk U x))).symm.trans
    (Category.id_comp _)

/-- The projection from the category of elements of the fibre functor of a point satisfies the
covering condition of `GrothendieckTopology.Point.ofIsCofiltered`. -/
private lemma exists_comp_eq_of_mem_point_elements (p : J.Point.{z}) ⦃U : C⦄ (R : Sieve U)
    (hR : R ∈ J U) ⦃V : p.fiber.Elements⦄ (f : (Functor.Elements.π p.fiber).obj V ⟶ U) :
    ∃ (Y : C) (g : Y ⟶ U) (_ : R g) (W : p.fiber.Elements) (q : W ⟶ V)
      (b : (Functor.Elements.π p.fiber).obj W ⟶ Y),
      b ≫ g = (Functor.Elements.π p.fiber).map q ≫ f := by
  obtain ⟨Y, g, hg, y, hy⟩ := p.jointly_surjective _ (J.pullback_stable f hR) V.val
  refine ⟨Y, g ≫ f, hg, p.fiber.elementsMk Y y, ⟨g, hy⟩, 𝟙 _, ?_⟩
  exact Category.id_comp _

/-- Flatness of the stalk of a sheaf of modules at a point of the site transfers to the fibre of
a presheaf of `R`-modules mapping to it, provided the map is inverted by the fibre functor and
carries the action of `R` to the one given on sections by `a` and on the stalk by `e`. -/
private lemma flat_presheafFiber_of_isFlatModuleStalk [LocallySmall.{z} C]
    [J.HasSheafCompose (forget₂ CommRingCat.{z} RingCat.{z})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{z}] [HasSheafify J AddCommGrpCat.{z}]
    (Φ : J.Point.{z}) (O : Sheaf J CommRingCat.{z})
    (M : SheafOfModules.{z} (Stacks.commRingSheafToRingSheaf O))
    (R : Type rr) [CommRing R] (P : Cᵒᵖ ⥤ ModuleCat.{z} R)
    (e : R ≃+* (Φ.presheafFiber (A := CommRingCat.{z})).obj O.obj)
    (a : ∀ U : Cᵒᵖ, R →+* O.obj.obj U)
    (ha : ∀ (U : C) (x : Φ.fiber.obj U) (r : R),
      Stacks.ringStalkGerm Φ O U x (a (op U) r) = e r)
    (τ : P ⋙ forget₂ (ModuleCat.{z} R) AddCommGrpCat ⟶ M.val.presheaf)
    (hτ : ∀ (U : Cᵒᵖ) (r : R) (m : P.obj U),
      letI : Module (O.obj.obj U) (M.val.presheaf.obj U) := (M.val.obj U).isModule
      τ.app U (r • m) = a U r • τ.app U m)
    [IsIso (Φ.presheafFiber.map τ)] (hflat : Stacks.IsFlatModuleStalk Φ O M) :
    Module.Flat R ((Φ.presheafFiber (A := ModuleCat.{z} R)).obj P) := by
  classical
  let A := forget₂ (ModuleCat.{z} R) AddCommGrpCat
  let φ₀ : A.obj ((Φ.presheafFiber (A := ModuleCat.{z} R)).obj P) ≅
      (Φ.presheafFiber (A := AddCommGrpCat.{z})).obj (P ⋙ A) :=
    preservesColimitIso A ((Functor.Elements.π Φ.fiber).op ⋙ P)
  let φ : A.obj ((Φ.presheafFiber (A := ModuleCat.{z} R)).obj P) ≅
      (Φ.presheafFiber (A := AddCommGrpCat.{z})).obj M.val.presheaf :=
    φ₀ ≪≫ asIso (Φ.presheafFiber.map τ)
  -- The fibre of `P` composed with `τ` is the germ map into the module stalk.
  have key : ∀ (U : C) (x : Φ.fiber.obj U) (m : P.obj (op U)),
      φ.hom (Φ.toPresheafFiber U x P m) =
        Stacks.moduleStalkGerm Φ O M U x (τ.app (op U) m) := by
    intro U x m
    have h₀ : φ₀.hom (A.map (Φ.toPresheafFiber U x P) m) =
        Φ.toPresheafFiber U x (P ⋙ A) m :=
      ConcreteCategory.congr_hom
        (ι_preservesColimitIso_hom A ((Functor.Elements.π Φ.fiber).op ⋙ P)
          (op (Φ.fiber.elementsMk U x))) m
    have h₁ := Φ.toPresheafFiber_naturality_apply τ U x m
    change (Φ.presheafFiber.map τ) (φ₀.hom (A.map (Φ.toPresheafFiber U x P) m)) = _
    rw [h₀, h₁]
    rfl
  let : Module ((Φ.presheafFiber (A := CommRingCat.{z})).obj O.obj)
      ↑((Φ.presheafFiber (A := AddCommGrpCat.{z})).obj M.val.presheaf) :=
    (Stacks.moduleStalk Φ O M).isModule
  have : Module.Flat ((Φ.presheafFiber (A := CommRingCat.{z})).obj O.obj)
      ↑((Φ.presheafFiber (A := AddCommGrpCat.{z})).obj M.val.presheaf) := hflat
  let ψ : ↑((Φ.presheafFiber (A := ModuleCat.{z} R)).obj P) ≃+
      ↑((Φ.presheafFiber (A := AddCommGrpCat.{z})).obj M.val.presheaf) :=
    φ.addCommGroupIsoToAddEquiv
  apply flat_of_semilinear_equiv e ψ
  intro r n
  have hpres : PreservesColimit ((Functor.Elements.π Φ.fiber).op ⋙ P)
      (forget (ModuleCat.{z} R)) := by
    change PreservesColimit _ (forget₂ (ModuleCat.{z} R) AddCommGrpCat ⋙ forget AddCommGrpCat)
    infer_instance
  obtain ⟨j, m, rfl⟩ :=
    Concrete.colimit_exists_rep ((Functor.Elements.π Φ.fiber).op ⋙ P) n
  obtain ⟨@⟨U, x⟩⟩ := j
  change ↑(P.obj (op U)) at m
  change φ.hom (r • Φ.toPresheafFiber U x P m) = e r • φ.hom (Φ.toPresheafFiber U x P m)
  rw [← map_smul (ConcreteCategory.hom (Φ.toPresheafFiber U x P)) r m, key, key, hτ, ← ha U x r]
  exact Stacks.moduleStalkGerm_smul Φ O M U x (a (op U) r) (τ.app (op U) m)

end

section CommutativeFlatness

variable (Λ : Type r) [CommRing Λ] [IsNoetherianRing Λ]
  [HasColimitsOfSize.{u, u} (ModuleCat.{w} Λ)]

omit [HasColimitsOfSize.{u, u} (ModuleCat.{w} Λ)] in
/-- A finite flat module over a Noetherian ring is projective: it is finitely presented, and a
flat finitely presented module is projective. -/
@[ega "III 7.7.12" "(i)"]
private lemma projective_of_finite_flat {N : Type w} [AddCommGroup N] [Module Λ N]
    (hfinite : Module.Finite Λ N) (hflat : Module.Flat Λ N) : Module.Projective Λ N := by
  have := hfinite
  have := hflat
  have : Module.FinitePresentation Λ N := Module.finitePresentation_of_finite Λ N
  exact Module.Flat.projective_of_finitePresentation

omit [IsNoetherianRing Λ] in
/-- The stalk at a geometric point of a sheaf of `Λ`-modules which is flat over the constant
coefficient ring sheaf is a flat `Λ`-module. Stalkwise flatness over the stalk of the constant
sheaf is Stacks 05VB, and the stalk of the constant sheaf is `Λ` itself. -/
private lemma etaleModuleStalk_flat
    (F : Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{w} Λ))
    (hF : Stacks.SheafOfModules.IsFlat.{u, u + 1, max (u + 1) w r, max (u + 1) w r}
      (moduleSheafOverConstantCoefficients.{u, w, r} B X Λ F))
    (s : GeometricPoint X.obj) :
    Module.Flat Λ ((etaleModuleStalkFunctor B X Λ s).obj F) := by
  by_cases hM : Subsingleton ((etaleModuleStalkFunctor B X Λ s).obj F)
  · have := hM
    infer_instance
  have : UnivLE.{u, w} := ModuleCat.univLE_of_not_subsingleton hM
  have : HasColimitsOfSize.{u, u} AddCommGrpCat.{w} := inferInstance
  let p₀ := geometricSitePoint B X s
  let Q := Functor.Elements.π p₀.fiber
  have hQ : ∀ ⦃U⦄ (R : Sieve U) (_ : R ∈ SmallEtale.topology B X.obj X.property U)
      ⦃V : p₀.fiber.Elements⦄ (f : Q.obj V ⟶ U),
      ∃ (Y : SmallEtale B X.obj X.property) (g : Y ⟶ U) (_ : R g)
        (W : p₀.fiber.Elements) (q : W ⟶ V) (b : Q.obj W ⟶ Y),
        b ≫ g = Q.map q ≫ f :=
    exists_comp_eq_of_mem_point_elements p₀
  have : InitiallySmall.{max (u + 1) w r} p₀.fiber.Elements :=
    initiallySmall_of_essentiallySmall _
  let Φ : (SmallEtale.topology B X.obj X.property).Point.{max (u + 1) w r} :=
    GrothendieckTopology.Point.ofIsCofiltered.{max (u + 1) w r} Q hQ
  let P := F.obj ⋙ ModuleCat.uliftFunctor.{max (u + 1) r} Λ
  let O := constantCoefficientSheaf.{u, w, r} B X Λ
  let M := moduleSheafOverConstantCoefficients.{u, w, r} B X Λ F
  let T := CommRingCat.of (ULift.{max (u + 1) w} Λ)
  let e : Λ ≃+* (Φ.presheafFiber (A := CommRingCat.{max (u + 1) w r})).obj O.obj :=
    (ULift.ringEquiv (R := Λ)).symm.trans
      (constantSheafFiberIso Φ T).symm.commRingCatIsoToRingEquiv
  let a (U : (SmallEtale B X.obj X.property)ᵒᵖ) : Λ →+* O.obj.obj U :=
    ((constantCoefficientRingMap.{u, w, r} B X Λ).app U).hom.comp
      (ULift.ringEquiv (R := Λ)).symm.toRingHom
  let τ : P ⋙ forget₂ (ModuleCat.{max (u + 1) w r} Λ) AddCommGrpCat ⟶ M.val.presheaf :=
    toSheafify (SmallEtale.topology B X.obj X.property)
      (modulePresheafOverConstantCoefficients B X Λ F).presheaf
  have : IsIso (Φ.presheafFiber.map τ) :=
    Φ.W_isInvertedBy_presheafFiber _ (GrothendieckTopology.W_toSheafify _ _)
  -- Flatness of the fibre of `P`, from Stacks 05VB for `M` and the constant-sheaf comparison.
  have hf : Module.Flat Λ ((Φ.presheafFiber (A := ModuleCat.{max (u + 1) w r} Λ)).obj P) :=
    flat_presheafFiber_of_isFlatModuleStalk Φ O M Λ P e a
      (fun U x r => ConcreteCategory.congr_hom
        (toSheafify_comp_toPresheafFiber Φ T U x) (ULift.up r))
      τ
      (fun U r m => ((PresheafOfModules.toSheafify
        (constantCoefficientRingMap.{u, w, r} B X Λ)
        (CategoryTheory.toSheafify (SmallEtale.topology B X.obj X.property)
          (modulePresheafOverConstantCoefficients B X Λ F).presheaf)).app U).hom.map_smul
        (ULift.up r) m)
      (Stacks.SheafOfModules.isFlatModuleStalk_of_isFlat.{max (u + 1) w r, u, u + 1}
        Φ O M hF)
  -- Transport across the small cofinal index category and across the universe lift.
  let eP : (Φ.presheafFiber (A := ModuleCat.{max (u + 1) w r} Λ)).obj P ≅
      colimit (Q.op ⋙ P) :=
    (GrothendieckTopology.Point.isColimitPresheafFiberOfIsCofilteredCocone.{max (u + 1) w r}
      Q hQ P).coconePointUniqueUpToIso (colimit.isColimit (Q.op ⋙ P))
  have : PreservesColimit (Q.op ⋙ F.obj) (ModuleCat.uliftFunctor.{max (u + 1) r} Λ) := by
    have : PreservesColimit (Q.op ⋙ F.obj)
        (ModuleCat.uliftFunctor.{max (u + 1) r} Λ ⋙
          forget₂ (ModuleCat.{max (u + 1) w r} Λ) AddCommGrpCat) := by
      change PreservesColimit (Q.op ⋙ F.obj)
        (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat ⋙ AddCommGrpCat.uliftFunctor.{max (u + 1) r})
      infer_instance
    exact preservesColimit_of_reflects_of_preserves
      (ModuleCat.uliftFunctor.{max (u + 1) r, w} Λ)
      (forget₂ (ModuleCat.{max (u + 1) w r} Λ) AddCommGrpCat)
  have : Module.Flat Λ (ULift.{max (u + 1) r} ((etaleModuleStalkFunctor B X Λ s).obj F)) :=
    (Module.Flat.equiv_iff
      (preservesColimitIso (ModuleCat.uliftFunctor.{max (u + 1) r} Λ)
        (Q.op ⋙ F.obj)).toLinearEquiv).mpr ((Module.Flat.equiv_iff eP.toLinearEquiv).mp hf)
  exact Module.Flat.of_ulift

/-- Every term of the stalk at a geometric point of a complex of constructible sheaves of
`Λ`-modules which are flat over the constant coefficient ring sheaf is a projective
`Λ`-module. -/
@[stacks 03TR "projectivity in each degree"]
theorem stalk_projective
    [∀ (S T : B.Scheme) (f : T ⟶ S),
      ((smallEtaleBaseChange B f).sheafPushforwardContinuous
        (ModuleCat.{w} Λ) (SmallEtale.topology B S.obj S.property)
        (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
    [∀ (T : B.Scheme) (V : SmallEtale B T.obj T.property),
      HasWeakSheafify ((SmallEtale.topology B T.obj T.property).over V) (ModuleCat.{w} Λ)]
    (K : CochainComplex
      (Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{w} Λ)) ℤ)
    (hconstructible : ∀ i : ℤ, IsConstructibleModuleSheaf B X Λ (K.X i))
    (hflat : ∀ i : ℤ, Stacks.SheafOfModules.IsFlat.{u, u + 1, max (u + 1) w r, max (u + 1) w r}
      (moduleSheafOverConstantCoefficients.{u, w, r} B X Λ (K.X i)))
    (s : GeometricPoint X.obj) (i : ℤ) :
    Module.Projective Λ ((etaleModuleStalkFunctor B X Λ s).obj (K.X i)) :=
  projective_of_finite_flat Λ (stalk_finite B X Λ K hconstructible s i)
    (etaleModuleStalk_flat B X Λ (K.X i) (hflat i) s)

/-- The stalk at a geometric point of a bounded complex of constructible sheaves of `Λ`-modules
which are flat over the constant coefficient ring sheaf is a perfect object of the derived
category of `Λ`-modules. -/
@[stacks 03TR "perfection of the stalk complex"]
theorem stalk_isPerfect
    [∀ (S T : B.Scheme) (f : T ⟶ S),
      ((smallEtaleBaseChange B f).sheafPushforwardContinuous
        (ModuleCat.{w} Λ) (SmallEtale.topology B S.obj S.property)
        (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
    [∀ (T : B.Scheme) (V : SmallEtale B T.obj T.property),
      HasWeakSheafify ((SmallEtale.topology B T.obj T.property).over V) (ModuleCat.{w} Λ)]
    (K : CochainComplex
      (Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{w} Λ)) ℤ)
    (hbounded : (CochainComplex.plus _ K) ∧ (CochainComplex.minus _ K))
    (hconstructible : ∀ i : ℤ, IsConstructibleModuleSheaf B X Λ (K.X i))
    (hflat : ∀ i : ℤ, Stacks.SheafOfModules.IsFlat.{u, u + 1, max (u + 1) w r, max (u + 1) w r}
      (moduleSheafOverConstantCoefficients.{u, w, r} B X Λ (K.X i)))
    (s : GeometricPoint X.obj)
    [HasDerivedCategory (ModuleCat.{w} Λ)] :
    StacksDraft.Perfect.IsPerfect
      (DerivedCategory.Q.obj (etaleModuleStalkComplex B X Λ s K)) :=
  stalk_isPerfect_of_finite_projective B X Λ K hbounded s
    (fun c => stalk_finite B X Λ K hconstructible s c)
    (fun c => stalk_projective B X Λ K hconstructible hflat s c)

end CommutativeFlatness

end AlgebraicGeometry

end

/-! ### Further declarations -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u w r

namespace AlgebraicGeometry

attribute [local instance] SheafOfModules.hasSheafify_commRingCat
  SheafOfModules.wEqualsLocallyBijective_commRingCat
  GrothendieckTopology.hasSheafify_addCommGrpCat
  SheafOfModules.wEqualsLocallyBijective_addCommGrpCat

/-- **The stalks of the terms of a complex of sheaves of `Λ`-modules which are termwise flat over
the constant coefficient ring sheaf are flat `Λ`-modules**, at every geometric point. Stalkwise
flatness over the stalk of the constant sheaf is Stacks 05VB, and the stalk of the constant sheaf
is `Λ` itself. -/
public theorem etaleModuleStalk_flat_of_isFlat_terms (B : BigEtaleSite.{u}) (X : B.Scheme)
    (Λ : Type r) [CommRing Λ] [HasColimitsOfSize.{u, u} (ModuleCat.{w} Λ)]
    (K : CochainComplex
      (Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{w} Λ)) ℤ)
    (hflat : ∀ i : ℤ, Stacks.SheafOfModules.IsFlat.{u, u + 1, max (u + 1) w r, max (u + 1) w r}
      (moduleSheafOverConstantCoefficients.{u, w, r} B X Λ (K.X i)))
    (i : ℤ) (s : GeometricPoint X.obj) :
    Module.Flat Λ ((etaleModuleStalkFunctor B X Λ s).obj (K.X i)) :=
  etaleModuleStalk_flat B X Λ (K.X i) (hflat i) s

end AlgebraicGeometry

end
