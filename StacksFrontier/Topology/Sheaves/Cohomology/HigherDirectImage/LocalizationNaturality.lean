module

public import StacksFrontier.Algebra.Homology.StrictlyPerfectRestrictionOfLE
public import StacksFrontier.Topology.Sheaves.Cohomology.HigherDirectImage.LocalizationInDegreeZero
public import StacksFrontier.Topology.Sheaves.Cohomology.HigherDirectImage.LocalizationIsomorphisms
public import StacksCore.Tactic.StacksAttribute

/-!
# Localization of higher direct images: compatibility across nested opens

Let `f : (X, 𝒪_X) ⟶ (Y, 𝒪_Y)` be a morphism of ringed spaces.  For an open `V ⊆ Y` with
`U = f⁻¹(V)`, Stacks 01E5 asserts the *equality* of sheaves

  `(R^p f_* ℱ)|_V = R^p (f|_U)_* (ℱ|_U)`,

realised in
`StacksFrontier/Topology/Sheaves/Cohomology/HigherDirectImage/LocalizationIsomorphisms.lean` as the
isomorphism `higherDirectImageRestrictIso f V p`, for one fixed `V`.  Because the source asserts
an equality of sheaves, the comparisons attached to two nested opens `V' ≤ V` must agree; that
clause is what this file proves.  It is the "localizing" half of the construction Stacks 02O7
calls *localizing and then sheafifying*, which is what turns the family of maps
`R^p f_*(ℐ^m ℱ) ⟶ R^p f_*(ℐ^{n + m} ℱ)` over the opens of `Y` into a map of sheaves on `Y`.

The obstruction to stating the compatibility at all is that the *codomain* of
`moduleRestriction Y V` depends on `V`: it is
`SheafOfModules (structureSheafRing (restrictToOpen Y V))`. So the comparison square first needs
restriction functors along `V' ≤ V` on both sides, and the transitivity isomorphisms identifying
"restrict to `V`, then along `V' ≤ V`" with "restrict to `V'`". Those are `moduleRestrictionOfLE`
and `moduleRestrictionOfLEIso` below, which are the generic
`Stacks.SheafOfModules.restrictSheafOfModulesOfLE` read in the vocabulary of `moduleRestriction`.

## Main definitions

* `moduleRestrictionOfLE X h` is restriction of sheaves of modules along an inclusion `V' ≤ V`
  of opens of a ringed space, from `𝒪_X|_V`-modules to `𝒪_X|_{V'}`-modules.
* `restrictOpensIsoOfLE` identifies the two ways of reading an open of `V'` as an open of
  `f⁻¹(V)`: take the inverse image under `f|_{f⁻¹(V')}` and include into `f⁻¹(V)`, or take the
  image in `V` and then the inverse image under `f|_{f⁻¹(V)}`.
* `modulePushforwardRestrictionOfLEIso` is the comparison, before deriving, between the two
  routes from `𝒪_X|_{f⁻¹(V)}`-modules to `𝒪_Y|_{V'}`-modules: restrict along
  `f⁻¹(V') ≤ f⁻¹(V)` then push forward along `f|_{f⁻¹(V')}`, or push forward along
  `f|_{f⁻¹(V)}` then restrict along `V' ≤ V`.
* `higherDirectImageRestrictionOfLEIso` is the same comparison after deriving, in every
  degree: it is Stacks 01E5 for the restricted morphism `f|_{f⁻¹(V)}` and the open `V'` of `V`,
  read in the `ofLE` vocabulary.

## Main results

* `moduleRestrictionOfLEIso X h`: restricting to `V` and then along `V' ≤ V` is restricting to
  `V'`, naturally in the sheaf of modules.  Together with
  `moduleRestrictionOfLE_preservesHomology` — restriction along `V' ≤ V` is exact — this is the
  two-step transitivity of `moduleRestriction` used on both sides of the square.
* `modulePushforwardRestrictIso_ofLE` is **Stacks 01E5, compatibility across nested opens**:
  the comparison before deriving attached to `V'` is the comparison attached to `V`, carried
  along the three isomorphisms above.  Equivalently, the two routes from
  `ℱ ↦ (f|_{f⁻¹(V')})_*(ℱ|_{f⁻¹(V')})` to `ℱ ↦ (f_* ℱ)|_{V'}` agree.
* `higherDirectImageRestrictIso_zero_ofLE` is the same clause for the derived comparison
  `higherDirectImageRestrictIso` in degree zero, read through the canonical maps to the zeroth
  right derived functors.
* `moduleRestrictionOfLE_preservesInjectiveObjects` is **Stacks 01E1 for an inclusion of
  opens**: restriction along `V' ≤ V` takes injectives to injectives.  It is what makes
  `higherDirectImageRestrictionOfLEIso` available in positive degree.
* `higherDirectImageRestrictionOfLEIso_zero_compatibility` pins the derived middle comparison
  down in degree zero: it is `modulePushforwardRestrictionOfLEIso`.

## Implementation notes

**Everything is a pushforward along a functor of sites, and the comparisons are `eqToIso`.**
`moduleRestriction X V` is `SheafOfModules.pushforward` along `V.isOpenEmbedding.functor`, and
`moduleRestrictionOfLE X h` is `SheafOfModules.pushforward` along the image functor of
`inclusionOfLE h`; the two composites in each square are therefore pushforwards along two
functors `Opens V' ⥤ Opens f⁻¹(V)` with the same source and target, so
`SheafOfModules.pushforwardCongr₂` applies.  The natural isomorphism it wants is objectwise
`eqToIso` with naturality by `Subsingleton.elim`, because `Opens` of a space is a thin poset.
The one genuine computation is `isOpenEmbeddingFunctorOfLE_obj_map_restrictedMorphismBase`, the
equality of opens underlying `restrictOpensIsoOfLE`, which is proved pointwise; the
compatibility of the structure-sheaf comparisons reduces, after one use of the naturality of
`f^♯`, to `Subsingleton.elim` in `Opens X`, exactly as in
`structureSheafHom_restrictedMorphism_compatible`.

**The cocycle identity is checked on sections.** Each of the four isomorphisms in
`modulePushforwardRestrictIso_ofLE` is, on sections over an open, the restriction map of the
sheaf of modules along an *equality* of opens, hence the identity up to the transport of the
type of sections (`heq_val_map_of_hom`).  Both sides of the identity are maps between the same
two types, so both being heterogeneously equal to the identity forces them to be equal.

**What is not proved here, but is proved**, is the *cocycle identity* for
`higherDirectImageRestrictIsoSucc` in positive degree — the analogue of
`modulePushforwardRestrictIso_ofLE` with the derived comparison in place of
`modulePushforwardRestrictIso`.  It is
`Stacks.Cohomology.HigherDirectImage.higherDirectImageRestrictIsoSucc_ofLE` in
`StacksFrontier/Topology/Sheaves/Cohomology/HigherDirectImage/LocalizationCocycle.lean`, which is a
leaf beside this file rather than part of it because it needs the composition laws for the two
engines and this file's import closure does not carry them.  Every *object* it needs is here:
the middle comparison is `higherDirectImageRestrictionOfLEIso`, which positive degree gets from
`moduleRestrictionOfLE_preservesInjectiveObjects`, and the two transitivity isomorphisms are
`moduleRestrictionOfLEIso`.

Unfolding both sides of that identity reduces it to a composition law of the form

  `Functor.whiskerRight (rightDerivedCompIso F G H e p) G' ≫ rightDerivedCompIso H G' H' e' p
     = rightDerivedCompIso F (G ⋙ G') H' _ p`

for `G` and `G'` both exact, together with the corresponding congruence in the outer variable,
since there `G ⋙ G'` is only *isomorphic* to the single functor appearing on the other side.
That is `Stacks.Cohomology.DerivedCompTransport.rightDerivedCompIso_comp` and
`...rightDerivedCompIso_comp_congr`.  Identifying the middle comparison of that cocycle with
`higherDirectImageRestrictionOfLEIso` — which matters because the latter is natural in the
module over the *smaller* open — needs in addition the compatibility of the two engines
themselves,
`Stacks.Cohomology.DerivedCompTransport.rightDerivedCompIso_comp_compRightDerivedNatIso`; the
identification is `...higherDirectImageRestrictIsoSuccOfLE_hom_eq`, in the same leaf.
Degree zero, proved below, needs none of them: the degree-zero normalizations
`rightDerivedCompIso_zero` and `compRightDerivedNatIso_zero` settle it directly.

## References

* [The Stacks Project, Tag 01E5](https://stacks.math.columbia.edu/tag/01E5)
* [The Stacks Project, Tag 02O7](https://stacks.math.columbia.edu/tag/02O7)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.SheafOfModules (functorCompIsoOfLE isOpenEmbedding_inclusionOfLE
  restrictSheafOfModulesOfLE restrictSheafOfModulesOfLEIso restrictSheafOfRingsHomOfLE)

universe u

namespace Stacks.Cohomology.HigherDirectImage

/-! ### Sections over an open, up to transport -/

section Transport

variable {T : Type u} [TopologicalSpace T]
  {R : Sheaf (Opens.grothendieckTopology T) RingCat.{u}} (M : SheafOfModules.{u} R)

/-- The restriction map of a sheaf of modules along *any* morphism between two opens that
happen to be equal is the identity, up to the transport of the type of sections.  Morphisms in
`Opens T` are inequalities, so a morphism in each direction forces the two opens to be equal,
and then `heq_val_map_eqToHom` applies: the morphism is `eqToHom` by `Subsingleton.elim`.

This is the computational engine behind the cocycle identity
`modulePushforwardRestrictIso_ofLE` of Stacks 01E5, every factor of which is such a
restriction map. -/
theorem heq_val_map_of_hom {A B : Opens T} (p : (op B : (Opens T)ᵒᵖ) ⟶ op A)
    (q : (op A : (Opens T)ᵒᵖ) ⟶ op B) (x : M.val.obj (op B)) :
    HEq (M.val.map p x) x := by
  have hAB : A = B := le_antisymm (leOfHom p.unop) (leOfHom q.unop)
  have hp : p = (eqToHom hAB).op := Subsingleton.elim _ _
  rw [hp]
  exact heq_val_map_eqToHom M hAB x

end Transport

/-! ### Restriction of sheaves of modules along an inclusion of opens -/

section OfLE

variable (X : RingedSpace.{u, u}) {V' V : Opens X} (h : V' ≤ V)

/-- Restriction of sheaves of modules along an inclusion `V' ≤ V` of opens of a ringed space,
from `𝒪_X|_V`-modules to `𝒪_X|_{V'}`-modules.  This is the generic
`Stacks.SheafOfModules.restrictSheafOfModulesOfLE` for the structure sheaf of rings of `X`,
whose source and target are definitionally those of `moduleRestriction X V` and
`moduleRestriction X V'`.

It is the functor that lets Stacks 01E5 be stated for two nested opens at once: the codomain of
`moduleRestriction Y V` depends on `V`, so without it the comparisons for `V` and for `V'`
cannot even be compared. -/
noncomputable def moduleRestrictionOfLE :
    SheafOfModules.{u} (structureSheafRing (restrictToOpen X V)) ⥤
      SheafOfModules.{u} (structureSheafRing (restrictToOpen X V')) :=
  restrictSheafOfModulesOfLE (structureSheafRing X) h

/-- **Transitivity of restriction to an open subspace.**  Restricting a sheaf of
`𝒪_X`-modules to `V` and then along `V' ≤ V` is restricting it to `V'`, naturally in the sheaf
of modules.  This is the identification that makes the two comparisons of Stacks 01E5 attached
to `V' ≤ V` comparable. -/
noncomputable def moduleRestrictionOfLEIso :
    moduleRestriction X V ⋙ moduleRestrictionOfLE X h ≅ moduleRestriction X V' :=
  restrictSheafOfModulesOfLEIso (structureSheafRing X) h

/-- Restriction along `V' ≤ V` is additive. -/
instance moduleRestrictionOfLE_additive : (moduleRestrictionOfLE X h).Additive :=
  inferInstanceAs (restrictSheafOfModulesOfLE (structureSheafRing X) h).Additive

/-- Restriction along `V' ≤ V` preserves finite limits: it is a pushforward of sheaves of
modules along a continuous functor of sites. -/
instance moduleRestrictionOfLE_preservesFiniteLimits :
    PreservesFiniteLimits (moduleRestrictionOfLE X h) :=
  Stacks.SheafOfModules.preservesFiniteLimits_restrictSheafOfModulesOfLE (structureSheafRing X) h

/-- Restriction along `V' ≤ V` preserves finite colimits, being a left adjoint. -/
instance moduleRestrictionOfLE_preservesFiniteColimits :
    PreservesFiniteColimits (moduleRestrictionOfLE X h) :=
  Stacks.SheafOfModules.preservesFiniteColimits_restrictSheafOfModulesOfLE (structureSheafRing X) h

/-- Restriction along `V' ≤ V` is exact, hence preserves homology.  This is the exactness input
that carries restriction along `V' ≤ V` through the right derived functors of `f_*` in
`higherDirectImageRestrictIso_zero_ofLE`. -/
instance moduleRestrictionOfLE_preservesHomology :
    (moduleRestrictionOfLE X h).PreservesHomology :=
  Functor.preservesHomologyOfExact _

/-- **Stacks 01E1 for an inclusion of opens.**  Restriction of sheaves of modules along
`V' ≤ V` takes injective objects to injective objects.

Stacks 01E1 is available directly only for restriction to an open subspace of the ambient space
(`moduleRestriction_preservesInjectiveObjects`), via the extension-by-zero adjunction; so the
proof goes through that case.  Restriction to `V` is left adjoint to `jPush`, which therefore
takes an injective `I` on `V` to an injective `J` on `X`; and the counit
`ExtensionByZeroModules.jStarPushIso` identifies `J|_V` with `I`, because restricting a
pushforward along an open immersion gives back the original sheaf.  So
`I|_{V'} ≅ (J|_V)|_{V'} ≅ J|_{V'}` by `moduleRestrictionOfLEIso`, and the right-hand side is
injective because restriction to `V'` preserves injectives.

This is the exactness-plus-injectives input that
`Stacks.Cohomology.CompositeRightDerived.compRightDerivedNatIso` needs in order to turn the
right derived functors of a composite into a composite with right derived functors, and it is
what makes `higherDirectImageRestrictionOfLEIso` available in every degree. -/
instance moduleRestrictionOfLE_preservesInjectiveObjects :
    (moduleRestrictionOfLE X h).PreservesInjectiveObjects where
  injective_obj {I} hI := by
    have hmono : (ExtensionByZeroModules.jStar V (structureSheafRing X)).PreservesMonomorphisms :=
      inferInstanceAs (moduleRestriction X V).PreservesMonomorphisms
    have hJ : Injective ((ExtensionByZeroModules.jPush V (structureSheafRing X)).obj I) :=
      (Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
        (ExtensionByZeroModules.jStarAdjunction V (structureSheafRing X))).injective_obj hI
    have e : (moduleRestrictionOfLE X h).obj I ≅
        (moduleRestriction X V').obj
          ((ExtensionByZeroModules.jPush V (structureSheafRing X)).obj I) :=
      (moduleRestrictionOfLE X h).mapIso
          ((ExtensionByZeroModules.jStarPushIso V (structureSheafRing X)).app I).symm ≪≫
        (moduleRestrictionOfLEIso X h).app _
    exact Injective.of_iso e.symm
      ((moduleRestriction_preservesInjectiveObjects X V').injective_obj hJ)

variable (M : SheafOfModules.{u} (structureSheafRing X))

/-- On sections over an open `O ⊆ V'`, the transitivity isomorphism
`moduleRestrictionOfLEIso` is the restriction map of the sheaf of modules along the
identification of the image of `O` in `X`, computed in two steps or in one.  It is therefore
the identity on sections; see `heq_moduleRestrictionOfLEIso_hom_app_val_app`. -/
theorem moduleRestrictionOfLEIso_hom_app_val_app
    (O : (Opens ((restrictToOpen X V' : TopCat) : Type u))ᵒᵖ)
    (y : ((moduleRestriction X V ⋙ moduleRestrictionOfLE X h).obj M).val.obj O) :
    ((moduleRestrictionOfLEIso X h).hom.app M).val.app O y =
      M.val.map ((functorCompIsoOfLE h).inv.app O.unop).op y :=
  rfl

/-- The inverse of the transitivity isomorphism `moduleRestrictionOfLEIso`, on sections. -/
theorem moduleRestrictionOfLEIso_inv_app_val_app
    (O : (Opens ((restrictToOpen X V' : TopCat) : Type u))ᵒᵖ)
    (y : ((moduleRestriction X V').obj M).val.obj O) :
    ((moduleRestrictionOfLEIso X h).inv.app M).val.app O y =
      M.val.map ((functorCompIsoOfLE h).hom.app O.unop).op y :=
  rfl

/-- The transitivity isomorphism `moduleRestrictionOfLEIso` is the identity on sections, in the
form of a heterogeneous equality: both types of sections over an open `O ⊆ V'` are the sections
of the sheaf of modules over the image of `O` in `X`, written in two ways. -/
theorem heq_moduleRestrictionOfLEIso_hom_app_val_app
    (O : (Opens ((restrictToOpen X V' : TopCat) : Type u))ᵒᵖ)
    (y : ((moduleRestriction X V ⋙ moduleRestrictionOfLE X h).obj M).val.obj O) :
    HEq (((moduleRestrictionOfLEIso X h).hom.app M).val.app O y) y := by
  exact heq_val_map_of_hom M _ ((functorCompIsoOfLE h).hom.app O.unop).op y

/-- The inverse of the transitivity isomorphism `moduleRestrictionOfLEIso` is the identity on
sections, up to the transport of the type of sections. -/
theorem heq_moduleRestrictionOfLEIso_inv_app_val_app
    (O : (Opens ((restrictToOpen X V' : TopCat) : Type u))ᵒᵖ)
    (y : ((moduleRestriction X V').obj M).val.obj O) :
    HEq (((moduleRestrictionOfLEIso X h).inv.app M).val.app O y) y := by
  exact heq_val_map_of_hom M _ ((functorCompIsoOfLE h).inv.app O.unop).op y

end OfLE

/-! ### The comparison before deriving, for nested opens -/

section Comparison

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y) {V' V : Opens Y}

/-- Taking inverse images under `f` is monotone: the inverse image of a smaller open is
smaller. -/
theorem preimageOpen_mono (h : V' ≤ V) : preimageOpen f V' ≤ preimageOpen f V :=
  fun _ hx => h hx

variable (h : V' ≤ V)

/-- **The two ways of reading an open `W ⊆ V'` as an open of `f⁻¹(V)` agree.**  Taking the
inverse image of `W` under the restricted morphism `f|_{f⁻¹(V')}` and then its image in
`f⁻¹(V)` is taking the image of `W` in `V` and then its inverse image under `f|_{f⁻¹(V)}`.
Both are the set of points of `f⁻¹(V)` whose image lies in `W`.

This is the equality of opens along which the two composites of pushforward functors in
`modulePushforwardRestrictionOfLEIso` agree, and is the nested-open analogue of
`isOpenEmbeddingFunctor_obj_map_restrictedMorphismBase`. -/
theorem isOpenEmbeddingFunctorOfLE_obj_map_restrictedMorphismBase
    (W : Opens ((Opens.toTopCat (Y : TopCat)).obj V')) :
    (isOpenEmbedding_inclusionOfLE (preimageOpen_mono f h)).functor.obj
        ((Opens.map (restrictedMorphismBase f V')).obj W) =
      (Opens.map (restrictedMorphismBase f V)).obj
        ((isOpenEmbedding_inclusionOfLE h).functor.obj W) := by
  ext ⟨x, hx⟩
  constructor
  · rintro ⟨⟨z, hz⟩, hzW, hzeq⟩
    obtain rfl : z = x := congrArg Subtype.val hzeq
    exact ⟨⟨f.hom.base z, hz⟩, hzW, rfl⟩
  · rintro ⟨⟨y, hy⟩, hyW, hyeq⟩
    obtain rfl : f.hom.base x = y := (congrArg Subtype.val hyeq).symm
    exact ⟨⟨x, hy⟩, hyW, rfl⟩

/-- The identification of the two composite functors of sites `Opens V' ⥤ Opens f⁻¹(V)`
underlying `modulePushforwardRestrictionOfLEIso`, from
`isOpenEmbeddingFunctorOfLE_obj_map_restrictedMorphismBase`.  Since `Opens f⁻¹(V)` is a poset,
naturality is automatic. -/
noncomputable def restrictOpensIsoOfLE :
    (isOpenEmbedding_inclusionOfLE h).functor ⋙ opensMap (restrictedMorphism f V) ≅
      opensMap (restrictedMorphism f V') ⋙
        (isOpenEmbedding_inclusionOfLE (preimageOpen_mono f h)).functor :=
  NatIso.ofComponents
    (fun W => eqToIso (isOpenEmbeddingFunctorOfLE_obj_map_restrictedMorphismBase f h W).symm)
    (fun _ => Subsingleton.elim _ _)

/-- **Before deriving, the restricted pushforwards for two nested opens agree.**  Restricting a
sheaf of `𝒪_X|_{f⁻¹(V)}`-modules along `f⁻¹(V') ≤ f⁻¹(V)` and pushing forward along
`f|_{f⁻¹(V')}` agrees with pushing forward along `f|_{f⁻¹(V)}` and restricting along `V' ≤ V`,
naturally in the sheaf of modules.

Both composites are pushforwards along the two composite functors `Opens V' ⥤ Opens f⁻¹(V)`
identified by `restrictOpensIsoOfLE`, and this is the induced
`SheafOfModules.pushforwardCongr₂`; the compatibility of the structure-sheaf comparisons it
requires reduces, by the naturality of `f^♯`, to `Subsingleton.elim` in `Opens X`.  This is the
middle isomorphism of the square of Stacks 01E5 for `V' ≤ V`. -/
noncomputable def modulePushforwardRestrictionOfLEIso :
    moduleRestrictionOfLE X (preimageOpen_mono f h) ⋙
        modulePushforward (restrictedMorphism f V') ≅
      modulePushforward (restrictedMorphism f V) ⋙ moduleRestrictionOfLE Y h := by
  letI iX : Functor.IsContinuous
      (isOpenEmbedding_inclusionOfLE (preimageOpen_mono f h)).functor
      (Opens.grothendieckTopology _) (Opens.grothendieckTopology _) :=
    (isOpenEmbedding_inclusionOfLE (preimageOpen_mono f h)).functor_isContinuous
  letI iY : Functor.IsContinuous (isOpenEmbedding_inclusionOfLE h).functor
      (Opens.grothendieckTopology _) (Opens.grothendieckTopology _) :=
    (isOpenEmbedding_inclusionOfLE h).functor_isContinuous
  refine SheafOfModules.pushforwardComp (structureSheafHom (restrictedMorphism f V'))
      (restrictSheafOfRingsHomOfLE (structureSheafRing X) (preimageOpen_mono f h)) ≪≫ ?_ ≪≫
    (SheafOfModules.pushforwardComp (restrictSheafOfRingsHomOfLE (structureSheafRing Y) h)
      (structureSheafHom (restrictedMorphism f V))).symm
  refine SheafOfModules.pushforwardCongr₂ _ (restrictOpensIsoOfLE f h) ?_
  refine Sheaf.hom_ext (NatTrans.ext (funext fun W => ?_))
  change ((forget₂ CommRingCat.{u} RingCat.{u}).map ((restrictedMorphismSheafHom f V').app W) ≫
        (forget₂ CommRingCat.{u} RingCat.{u}).map (X.presheaf.map
          ((functorCompIsoOfLE (preimageOpen_mono f h)).hom.app
            ((Opens.map (restrictedMorphismBase f V')).obj W.unop)).op)) ≫
      (forget₂ CommRingCat.{u} RingCat.{u}).map (X.presheaf.map
        ((preimageOpen f V).isOpenEmbedding.functor.op.map
          ((restrictOpensIsoOfLE f h).hom.app W.unop).op)) =
    (forget₂ CommRingCat.{u} RingCat.{u}).map (Y.presheaf.map
        ((functorCompIsoOfLE h).hom.app W.unop).op) ≫
      (forget₂ CommRingCat.{u} RingCat.{u}).map ((restrictedMorphismSheafHom f V).app
        (op ((isOpenEmbedding_inclusionOfLE h).functor.obj W.unop)))
  have key : (restrictedMorphismSheafHom f V').app W ≫
      X.presheaf.map ((functorCompIsoOfLE (preimageOpen_mono f h)).hom.app
          ((Opens.map (restrictedMorphismBase f V')).obj W.unop)).op ≫
        X.presheaf.map ((preimageOpen f V).isOpenEmbedding.functor.op.map
          ((restrictOpensIsoOfLE f h).hom.app W.unop).op) =
      Y.presheaf.map ((functorCompIsoOfLE h).hom.app W.unop).op ≫
        (restrictedMorphismSheafHom f V).app
          (op ((isOpenEmbedding_inclusionOfLE h).functor.obj W.unop)) := by
    rw [restrictedMorphismSheafHom_app, restrictedMorphismSheafHom_app, Category.assoc]
    refine Eq.trans ?_ (f.hom.c.naturality_assoc _ _).symm
    congr 1
    rw [← X.presheaf.map_comp, ← X.presheaf.map_comp]
    exact (congrArg X.presheaf.map (Subsingleton.elim _ _)).trans (X.presheaf.map_comp _ _)
  rw [← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp, Category.assoc]
  exact congrArg (forget₂ CommRingCat.{u} RingCat.{u}).map key

variable (M : SheafOfModules.{u} (structureSheafRing (restrictToOpen X (preimageOpen f V))))

/-- On sections over an open `W ⊆ V'`, the comparison
`modulePushforwardRestrictionOfLEIso` is the restriction map of the sheaf of modules along the
identification `restrictOpensIsoOfLE` of opens of `f⁻¹(V)` — that is, the identity on
sections.  This characterizes the comparison and rules out multiplication by an
automorphism. -/
theorem modulePushforwardRestrictionOfLEIso_hom_app_val_app
    (W : (Opens ((restrictToOpen Y V' : TopCat) : Type u))ᵒᵖ)
    (y : ((moduleRestrictionOfLE X (preimageOpen_mono f h) ⋙
      modulePushforward (restrictedMorphism f V')).obj M).val.obj W) :
    ((modulePushforwardRestrictionOfLEIso f h).hom.app M).val.app W y =
      M.val.map ((restrictOpensIsoOfLE f h).hom.app W.unop).op y :=
  rfl

/-- The comparison `modulePushforwardRestrictionOfLEIso` is the identity on sections, in the
form of a heterogeneous equality. -/
theorem heq_modulePushforwardRestrictionOfLEIso_hom_app_val_app
    (W : (Opens ((restrictToOpen Y V' : TopCat) : Type u))ᵒᵖ)
    (y : ((moduleRestrictionOfLE X (preimageOpen_mono f h) ⋙
      modulePushforward (restrictedMorphism f V')).obj M).val.obj W) :
    HEq (((modulePushforwardRestrictionOfLEIso f h).hom.app M).val.app W y) y := by
  exact heq_val_map_of_hom M _ ((restrictOpensIsoOfLE f h).inv.app W.unop).op y

end Comparison

/-! ### The middle comparison after deriving -/

section DerivedComparison

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y) {V' V : Opens Y} (h : V' ≤ V)

/-- **Stacks 01E5 for the restricted morphism and an inclusion of opens.**  Higher direct
images along `f|_{f⁻¹(V)}` commute with restriction along `V' ≤ V`: restricting a sheaf of
`𝒪_X|_{f⁻¹(V)}`-modules along `f⁻¹(V') ≤ f⁻¹(V)` and taking the `p`-th higher direct image
along `f|_{f⁻¹(V')}` agrees with taking the `p`-th higher direct image along `f|_{f⁻¹(V)}` and
restricting along `V' ≤ V`.

This is the `ofLE` form of `higherDirectImageRestrictIso`, built by the same two engines:
restriction along `V' ≤ V` is exact, so by
`Stacks.Cohomology.ModuleComparison.rightDerivedCompIso` the right-hand side computes the
`p`-th right derived functor of the composite, and restriction along `f⁻¹(V') ≤ f⁻¹(V)` is
exact and preserves injectives by `moduleRestrictionOfLE_preservesInjectiveObjects`, so
`Stacks.Cohomology.CompositeRightDerived.compRightDerivedNatIso` turns that into the left-hand
side.  It carries no Stacks attribute of its own, being an instance of the clause already
carried by `higherDirectImageRestrictIso` — transported to the `ofLE` vocabulary — rather than
a new assertion of the tag.

Unlike `higherDirectImageRestrictIso`, no separate degree-zero construction is needed: both
pushforwards are left exact, so the degree-zero value of this comparison is already the
normalized one, which is `higherDirectImageRestrictionOfLEIso_zero_compatibility`. -/
@[sga "4 V 5.1" "Clause 3), special case"]
noncomputable def higherDirectImageRestrictionOfLEIso (p : ℕ) :
    moduleRestrictionOfLE X (preimageOpen_mono f h) ⋙
        (modulePushforward (restrictedMorphism f V')).rightDerived p ≅
      (modulePushforward (restrictedMorphism f V)).rightDerived p ⋙
        moduleRestrictionOfLE Y h :=
  (Stacks.Cohomology.ModuleComparison.rightDerivedCompIso
      (modulePushforward (restrictedMorphism f V)) (moduleRestrictionOfLE Y h) _
      (modulePushforwardRestrictionOfLEIso f h).symm p ≪≫
    Stacks.Cohomology.CompositeRightDerived.compRightDerivedNatIso
      (moduleRestrictionOfLE X (preimageOpen_mono f h))
      (modulePushforward (restrictedMorphism f V')) p).symm

/-- **The middle comparison in degree zero is the undeived one.**  After the canonical maps to
the zeroth right derived functors, `higherDirectImageRestrictionOfLEIso f h 0` is
`modulePushforwardRestrictionOfLEIso f h`.  This rules out multiplying the degree-zero
comparison by an automorphism, and is what makes the degree-zero clause
`higherDirectImageRestrictIso_zero_ofLE` a statement about the same comparison that
`modulePushforwardRestrictIso_ofLE` uses. -/
theorem higherDirectImageRestrictionOfLEIso_zero_compatibility :
    Functor.whiskerLeft (moduleRestrictionOfLE X (preimageOpen_mono f h))
          (modulePushforward (restrictedMorphism f V')).toRightDerivedZero ≫
        (higherDirectImageRestrictionOfLEIso f h 0).hom =
      (modulePushforwardRestrictionOfLEIso f h).hom ≫
        Functor.whiskerRight (modulePushforward (restrictedMorphism f V)).toRightDerivedZero
          (moduleRestrictionOfLE Y h) := by
  dsimp only [higherDirectImageRestrictionOfLEIso]
  rw [Iso.symm_hom, Iso.trans_inv,
    compRightDerivedNatIso_inv_comp_rightDerivedCompIso_inv_zero,
    Iso.trans_hom, Iso.trans_hom, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Iso.symm_hom, Functor.rightDerivedZeroIsoSelf_inv, ← Category.assoc,
    ← Functor.whiskerLeft_comp, Functor.rightDerivedZeroIsoSelf_inv_hom_id,
    Functor.whiskerLeft_id', Category.id_comp]

end DerivedComparison

/-! ### Stacks 01E5 across nested opens -/

section Nested

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y) {V' V : Opens Y} (h : V' ≤ V)

/-- **Stacks 01E5, compatibility across nested opens, before deriving.**  Stacks 01E5 asserts
an *equality* of
sheaves, so the comparisons it attaches to two nested opens `V' ≤ V` of `Y` must agree.  Before
deriving that is this cocycle identity: the comparison
`(f|_{f⁻¹(V')})_*(ℱ|_{f⁻¹(V')}) ≅ (f_* ℱ)|_{V'}` is the comparison for `V`, whiskered by
restriction along `V' ≤ V`, composed with the middle comparison
`modulePushforwardRestrictionOfLEIso` and the two transitivity isomorphisms
`moduleRestrictionOfLEIso` on the `X` and the `Y` side.  Equivalently: the two routes from
`ℱ|_{f⁻¹(V)} ↦ ((f|_{f⁻¹(V)})_*(ℱ|_{f⁻¹(V)}))|_{V'}` to `(f_* ℱ)|_{V'}` agree.

This is the "localizing" input to the construction Stacks 02O7 calls *localizing and then
sheafifying*: it is what makes the comparisons over the opens of `Y` fit together into a
statement about sheaves on `Y`, rather than one open at a time.

Every factor is, on sections, a restriction map along an equality of opens, hence the identity
up to the transport of the type of sections; both sides are maps between the same two types, so
`heq_val_map_of_hom` four times forces them to agree. -/
@[stacks 01E5 "compatibility across nested opens, before deriving"]
theorem modulePushforwardRestrictIso_ofLE :
    (modulePushforwardRestrictIso f V').hom =
      Functor.whiskerRight (moduleRestrictionOfLEIso X (preimageOpen_mono f h)).inv
          (modulePushforward (restrictedMorphism f V')) ≫
        Functor.whiskerLeft (moduleRestriction X (preimageOpen f V))
          (modulePushforwardRestrictionOfLEIso f h).hom ≫
        Functor.whiskerRight (modulePushforwardRestrictIso f V).hom
          (moduleRestrictionOfLE Y h) ≫
        Functor.whiskerLeft (modulePushforward f) (moduleRestrictionOfLEIso Y h).hom := by
  ext M W x
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app]
  refine eq_of_heq
    ((modulePushforwardRestrictIso_hom_app_val_app_heq f V' M W x).trans (HEq.symm ?_))
  refine HEq.trans
    (heq_moduleRestrictionOfLEIso_hom_app_val_app Y h ((modulePushforward f).obj M) W _) ?_
  refine HEq.trans (modulePushforwardRestrictIso_hom_app_val_app_heq f V M
    ((isOpenEmbedding_inclusionOfLE h).functor.op.obj W) _) ?_
  refine HEq.trans (heq_modulePushforwardRestrictionOfLEIso_hom_app_val_app f h
    ((moduleRestriction X (preimageOpen f V)).obj M) W _) ?_
  exact heq_moduleRestrictionOfLEIso_inv_app_val_app X (preimageOpen_mono f h) M
    ((opensMap (restrictedMorphism f V')).op.obj W) x

/-- **Stacks 01E5, compatibility across nested opens in degree zero.**  The degree-zero
derived comparison `higherDirectImageRestrictIso f V' 0` is compatible with shrinking `V` to
`V'`: after the canonical maps to the zeroth right derived functors it is the degree-zero
comparison for `V`, carried along the three isomorphisms of
`modulePushforwardRestrictIso_ofLE`.

In degree zero both pushforwards are left exact, so the derived comparison is normalized to the
undeived one (`higherDirectImageRestrictIso_zero_compatibility`) and the clause reduces to the
cocycle identity before deriving.  No analogue of Stacks 01E1 for an inclusion of opens is
needed; see the implementation notes for why positive degree is not proved here. -/
@[stacks 01E5 "compatibility across nested opens, degree zero"]
theorem higherDirectImageRestrictIso_zero_ofLE :
    Functor.whiskerLeft (moduleRestriction X (preimageOpen f V'))
          (modulePushforward (restrictedMorphism f V')).toRightDerivedZero ≫
        (higherDirectImageRestrictIso f V' 0).hom =
      Functor.whiskerRight (moduleRestrictionOfLEIso X (preimageOpen_mono f h)).inv
          (modulePushforward (restrictedMorphism f V')) ≫
        Functor.whiskerLeft (moduleRestriction X (preimageOpen f V))
          (modulePushforwardRestrictionOfLEIso f h).hom ≫
        Functor.whiskerRight (modulePushforwardRestrictIso f V).hom
          (moduleRestrictionOfLE Y h) ≫
        Functor.whiskerLeft (modulePushforward f) (moduleRestrictionOfLEIso Y h).hom ≫
        Functor.whiskerRight (modulePushforward f).toRightDerivedZero
          (moduleRestriction Y V') := by
  rw [higherDirectImageRestrictIso_zero_compatibility f V',
    modulePushforwardRestrictIso_ofLE f h, Category.assoc, Category.assoc, Category.assoc]

end Nested

end Stacks.Cohomology.HigherDirectImage

end
