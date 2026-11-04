module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.HypercohomologyEdge.SectionsRestriction
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.ConnectivityOnABasis

/-! # Restriction in the open, on derived sections over an inverse image

Let `f : X ⟶ Y` be a morphism of ringed spaces and `V' ⊆ V` opens of `Y`.  Derived sections over
the inverse image, `Stacks.Cohomology.DerivedSectionsLeray.derivedPreimageSections f V`, take
values in `DerivedCategory (ModuleCat Γ(V, 𝒪_Y))` — a category which **depends on the open**.  So
"restriction along `V' ≤ V`" is not a natural transformation between two functors with a common
target; it becomes one only after composing with restriction of scalars along
`ρ : Γ(V, 𝒪_Y) ⟶ Γ(V', 𝒪_Y)`.  This file provides that shape, for the three functors of
[Stacks, Tag 0D5W]: termwise sections over an inverse image, their total right derived functor,
and — by instantiating the ringed-site construction of
`StacksFrontier.CategoryTheory.Sites.Cohomology.HypercohomologyEdge.SectionsRestriction` — derived
sections over an open of `Y`.

Without these the naturality in the open of the Leray isomorphism
`Stacks.Cohomology.DerivedSectionsLeray.derivedSectionsPushforwardIso` and of
`Stacks.Cohomology.HypercohomologyEdge.sectionsEvaluationIso` cannot even be *stated*, and those
two squares are what the restriction compatibility of
`Stacks.Cohomology.UnboundedHigherDirectImage.derivedPreimageHomPresheafValueEquiv` — hence
clause (a) of [Stacks, Tag 0D68] — rests on.  See the section *What is granted, and why* of
`StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.UniquenessOfASolution`.

## Main definitions

* `Stacks.Cohomology.DerivedSectionsLeray.sectionsOverOpenRestrict`: restriction of sections over
  an open of `X`, `Γ(U, -) ⟶ Γ(U', -) ⋙ Res_ρ`.
* `Stacks.Cohomology.DerivedSectionsLeray.preimageSectionsRestrict`: restriction of sections over
  an inverse image, `Γ(f⁻¹ V, -) ⟶ Γ(f⁻¹ V', -) ⋙ Res_ρ`, where both sides are read as modules
  over the ring of functions on the open of `Y`.
* `Stacks.Cohomology.DerivedSectionsLeray.derivedPreimageSectionsRestrict`: the same on the total
  right derived functors, `RΓ(f⁻¹ V, -) ⟶ RΓ(f⁻¹ V', -) ⋙ R Res_ρ`.
* `Stacks.Cohomology.DerivedSectionsLeray.derivedSectionsOverOpenRestrict`: the same for derived
  sections over an open of `Y`.

## Main results

* `Stacks.Cohomology.DerivedSectionsLeray.structureSheafHom_comp_map`: the square of rings
  relating `f^♯` over `V` and over `V'` with the two restriction maps.  This is the only
  substantive input to `preimageSectionsRestrict`; everything else is bookkeeping.
* `Stacks.Cohomology.DerivedSectionsLeray.derivedPreimageSectionsRestrict_fac` and
  `derivedPreimageSectionsRestrict_ext`: the equation characterizing the derived restriction, and
  the uniqueness it gives.  A square involving the derived restriction is proved by composing
  with the unit and descending to the homotopy category, where restriction of sections is
  termwise; the same route the Leray comparison of Tag 0D5W itself is built and identified by.
* `Stacks.Cohomology.DerivedSectionsLeray.preimageSectionsKInjectiveIso_hom`: the comparison of
  Tag 0D5W at a K-injective complex, written out as a composite of its four legs.

## Implementation notes

*Two restrictions of scalars, in the two orders.*  Sections over `f⁻¹ V` are read as
`Γ(V, 𝒪_Y)`-modules along `f^♯_V : Γ(V, 𝒪_Y) ⟶ Γ(f⁻¹ V, 𝒪_X)`.  Restricting to `V'` therefore
restricts scalars twice, and in the two possible orders: once along `f^♯_V` and the restriction
`Γ(f⁻¹ V, 𝒪_X) ⟶ Γ(f⁻¹ V', 𝒪_X)`, once along the restriction `Γ(V, 𝒪_Y) ⟶ Γ(V', 𝒪_Y)` and
`f^♯_{V'}`.  The two composites are the *same ring map*, because `structureSheafHom f` is a
natural transformation; `preimageRestrictScalarsIso` is the resulting isomorphism of functors,
assembled from `CategoryTheory.ModuleCat.restrictScalarsComp'` applied twice **to one and the
same composite** — once with `rfl`, once with that square — so no transport along an equality of
functors occurs and the comparison is the identity on underlying elements.

*Nothing is re-derived from the ringed site.*  Sections over an open of a ringed space are
evaluation of a sheaf of modules at an object of the site of opens, and
`Stacks.Cohomology.HypercohomologyEdge.derivedSections (structureSheafRing X) U` is
`derivedSectionsOverOpen X U` on the nose.  So `sectionsOverOpenRestrict` and
`derivedSectionsOverOpenRestrict` are instantiations of the ringed-site constructions rather than
second copies of them; only the inverse-image versions, which carry the extra restriction of
scalars along `f^♯`, are new here.

*Where the layer-2 square stands.*  The square still owed is

```
theorem preimageSectionsKInjectiveIso_restrict (f : X ⟶ Y) {V V' : Opens Y.carrier} (hV : V' ≤ V)
    (W : CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ) (hW : W.IsKInjective) :
    (preimageSectionsKInjectiveIso f V W hW).hom ≫
        (derivedPreimageSectionsRestrict f hV).app (DerivedCategory.Q.obj W) =
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex (preimageSectionsRestrict f hV)
            (ComplexShape.up ℤ)).app W) ≫
        (ModuleCat.restrictScalars ρ).mapDerivedCategoryFactors.inv.app
            (((preimageSections f V').mapHomologicalComplex (ComplexShape.up ℤ)).obj W) ≫
          (restrictScalarsDerived Y hV).map (preimageSectionsKInjectiveIso f V' W hW).hom
```

(`mapDerivedCategoryFactors.inv`, not `.hom`.)  Two of its three steps are carried here and are
not the obstruction.  Writing both comparisons as composites with
`preimageSectionsKInjectiveIso_hom`, the last leg of the left-hand side is pushed past the
derived restriction by the *naturality* of `derivedPreimageSectionsRestrict` along
`(DerivedCategory.quotientCompQhIso _).hom.app W`, and the unit that is then exposed is absorbed
by `derivedPreimageSectionsRestrict_fac_app`.  What is left is a single identity among the
canonical comparisons alone — `DerivedCategory.quotientCompQhIso`,
`CategoryTheory.Functor.mapHomotopyCategoryFactors`,
`CategoryTheory.Functor.mapHomotopyCategoryCompIso` and the two
`mapDerivedCategoryFactors`/`mapDerivedCategoryFactorsh` — in which neither derived sections nor
the restriction maps appear.  Its content is
`CategoryTheory.Functor.mapDerivedCategoryFactorsh_hom_app`, which expresses `Factorsh` at an
object of the form `quotient.obj K` through `Factors`, `quotientCompQhIso` and
`mapHomotopyCategoryFactors`; the one step that lemma does not supply directly is that the object
occurring here is `(preimageSections f V').mapHomotopyCategory c` applied to `quotient.obj W`
rather than `quotient.obj` of a complex, so the naturality of `Factorsh` along
`mapHomotopyCategoryFactors` is needed first.

This is what makes that identity shorter than it looks:
`CategoryTheory.Functor.mapHomotopyCategoryFactors` is `Quotient.lift.isLift`, whose components
are identities, so that leg of `preimageSectionsKInjectiveIso_hom` contributes nothing — flipping
it between `hom` and `inv` leaves the statement `rfl`, which is why it is no use as a control.
The legs that do carry content are `DerivedCategory.quotientCompQhIso` and the unit.

The next point changes where the difficulty sits.  The displayed statement does
elaborate, and the reduction described above does run: with `hnat` the naturality of
`derivedPreimageSectionsRestrict` along `(DerivedCategory.quotientCompQhIso _).hom.app W` taken as
a *closed* `have` and rewritten (as an open `rw` of `NatTrans.naturality` it is a
200000-heartbeat `whnf` timeout), followed by `derivedPreimageSectionsRestrict_fac_app` and the
expansion of `preimageSectionsRestrictUnit`, the square becomes an identity in which neither
derived sections nor the derived restriction occurs — the whole reduction checks in under a
second.  Three of its legs are identities and are `rfl`:
`(preimageSections f V₀).mapHomotopyCategoryFactors c |>.inv.app W` for `V₀ = V` and `V₀ = V'`,
and `Functor.mapHomotopyCategoryCompIso (Iso.refl _) c |>.inv.app ((quotient _ c).obj W)`.

**The obstruction is not `mapDerivedCategoryFactorsh_hom_app`; it comes before it.**  Those three
legs are morphisms *between two spellings of one object* — `(quotient ⋙ F.mapHomotopyCategory).obj
W` and `(F.mapHomologicalComplex ⋙ quotient).obj W` — and the two spellings are `rfl`-equal but
**not interchangeable by any rewriting tactic here**: `HomologicalComplexUpToQuasiIso.Qh` is not
exposed, so the crossing is invisible at the `implicit` transparency `rw`, `simp only` and
`dsimp only` re-check at.  The consequences:
`CategoryTheory.Functor.map_id` does not fire on `DerivedCategory.Qh.map (𝟙 _)`;
`rw [DerivedCategory.Qh.map_id]` is an `isDefEq` timeout; once the leg has been replaced by `𝟙`,
`Category.id_comp` reports *no progress*, and so do `dsimp only` and `simp only [h]` for
`h : <one spelling> = <the other> := rfl`.  What *does* cross it is `rfl` and `exact`.  So the
route for this square is term mode throughout, or an upstream normal form for
`preimageSectionsKInjectiveIso` from which the three identity legs are already absent — not a
tactic rewrite of the composite.  (The name clash to watch for while doing it: with
`open CategoryTheory`, plain `Functor.map_id` resolves to the *monad* lemma, not
`CategoryTheory.Functor.map_id`, and silently does nothing in a `simp only` set.)

*Exactness of restriction of scalars.*  The structure ring is an object of `RingCat`, so
Mathlib's exactness instances — stated for commutative rings — do not apply, and the general ones
are installed from
`Stacks.Cohomology.HypercohomologyEdge.restrictScalars_preservesFiniteLimits` and
`restrictScalars_preservesFiniteColimits` with `attribute [local instance]`.  See the
implementation notes of that file for why they are theorems rather than global instances.

## References

* [Stacks Project, Tag 0D5W](https://stacks.math.columbia.edu/tag/0D5W)
* [Stacks Project, Tag 0D5X](https://stacks.math.columbia.edu/tag/0D5X)
* [Stacks Project, Tag 0D68](https://stacks.math.columbia.edu/tag/0D68)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction

namespace Stacks.Cohomology.DerivedSectionsLeray

universe u

attribute [local instance] HasDerivedCategory.standard
  Stacks.Cohomology.HypercohomologyEdge.restrictScalars_preservesFiniteLimits
  Stacks.Cohomology.HypercohomologyEdge.restrictScalars_preservesFiniteColimits

/-! ### Sections over an open of `X` -/

/-- **Restriction of sections over an open.**  For `g : U' ⟶ U` the restriction map
`M(U) ⟶ M(U')` of a sheaf of `𝒪_X`-modules is semilinear over `ρ : Γ(U, 𝒪_X) ⟶ Γ(U', 𝒪_X)`, so it
is a morphism of `Γ(U, 𝒪_X)`-modules into restriction of scalars along `ρ`.

This is the ringed-site construction
`Stacks.Cohomology.HypercohomologyEdge.sectionsRestrict`, read on the site of opens. -/
abbrev sectionsOverOpenRestrict (X : RingedSpace.{u, u}) {U U' : Opens X.carrier} (g : U' ⟶ U) :
    sectionsOverOpen X U ⟶
      sectionsOverOpen X U' ⋙ ModuleCat.restrictScalars ((structureSheafRing X).obj.map g.op).hom :=
  Stacks.Cohomology.HypercohomologyEdge.sectionsRestrict (structureSheafRing X) g

/-- **Restriction of scalars along `ρ : Γ(V, 𝒪_Y) ⟶ Γ(V', 𝒪_Y)`, on unbounded derived
categories.**  Restriction of scalars is exact, so it induces a functor on derived categories;
this is the functor through which restriction in the open becomes a natural transformation. -/
abbrev restrictScalarsDerived (Z : RingedSpace.{u, u}) {V V' : Opens Z.carrier} (hV : V' ≤ V) :
    DerivedCategory (ModuleCat.{u} ((structureSheafRing Z).obj.obj (op V'))) ⥤
      DerivedCategory (ModuleCat.{u} ((structureSheafRing Z).obj.obj (op V))) :=
  Stacks.Cohomology.HypercohomologyEdge.restrictScalarsDerived (structureSheafRing Z) hV.hom

/-- **Restriction in the open, on derived sections over an open of a ringed space.**
`RΓ(U, -) ⟶ RΓ(U', -) ⋙ R Res_ρ`.

This is the ringed-site construction
`Stacks.Cohomology.HypercohomologyEdge.derivedSectionsRestrict`, read on the site of opens:
derived sections over an open of a ringed space are derived sections over an object of that
site, on the nose. -/
abbrev derivedSectionsOverOpenRestrict (Z : RingedSpace.{u, u}) {V V' : Opens Z.carrier}
    (hV : V' ≤ V) :
    derivedSectionsOverOpen Z V ⟶ derivedSectionsOverOpen Z V' ⋙ restrictScalarsDerived Z hV :=
  Stacks.Cohomology.HypercohomologyEdge.derivedSectionsRestrict (structureSheafRing Z) hV.hom

/-! ### Sections over an inverse image -/

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)

/-- **The square of rings behind restriction on an inverse image.**  Pulling a function back
along `f` over `V` and then restricting to `f⁻¹ V'` is restricting to `V'` and then pulling back
over `V'`: this is the naturality of `AlgebraicGeometry.structureSheafHom`, read as an equation
of ring homomorphisms `Γ(V, 𝒪_Y) ⟶ Γ(f⁻¹ V', 𝒪_X)`.

It is the only substantive input to `preimageSectionsRestrict`. -/
theorem structureSheafHom_comp_map {V V' : Opens Y.carrier} (g : V' ⟶ V) :
    (((structureSheafRing X).obj.map ((opensMap f).map g).op).hom).comp
        (((structureSheafHom f).hom.app (op V)).hom) =
      (((structureSheafHom f).hom.app (op V')).hom).comp
        ((structureSheafRing Y).obj.map g.op).hom := by
  have h : (structureSheafRing Y).obj.map g.op ≫ (structureSheafHom f).hom.app (op V') =
      (structureSheafHom f).hom.app (op V) ≫
        (structureSheafRing X).obj.map ((opensMap f).map g).op :=
    (structureSheafHom f).hom.naturality g.op
  exact congrArg RingCat.Hom.hom h.symm

/-- **The two orders of restricting scalars agree.**  Restricting scalars along `f^♯_V` after
restricting along `Γ(f⁻¹ V, 𝒪_X) ⟶ Γ(f⁻¹ V', 𝒪_X)` is restricting along
`ρ : Γ(V, 𝒪_Y) ⟶ Γ(V', 𝒪_Y)` after restricting along `f^♯_{V'}`.

Both are restriction of scalars along the one composite of `structureSheafHom_comp_map`, so the
comparison is the identity on underlying elements: no transport along an equality of functors
occurs. -/
def preimageRestrictScalarsIso {V V' : Opens Y.carrier} (g : V' ⟶ V) :
    ModuleCat.restrictScalars ((structureSheafRing X).obj.map ((opensMap f).map g).op).hom ⋙
        ModuleCat.restrictScalars (((structureSheafHom f).hom.app (op V)).hom) ≅
      ModuleCat.restrictScalars (((structureSheafHom f).hom.app (op V')).hom) ⋙
        ModuleCat.restrictScalars ((structureSheafRing Y).obj.map g.op).hom :=
  (ModuleCat.restrictScalarsComp'.{u} (((structureSheafHom f).hom.app (op V)).hom)
      ((structureSheafRing X).obj.map ((opensMap f).map g).op).hom _ rfl).symm ≪≫
    ModuleCat.restrictScalarsComp'.{u} ((structureSheafRing Y).obj.map g.op).hom
      (((structureSheafHom f).hom.app (op V')).hom) _ (structureSheafHom_comp_map f g)

/-- **Restriction of sections over an inverse image.**  For `V' ≤ V`, the restriction map of a
sheaf of `𝒪_X`-modules from `f⁻¹ V` to `f⁻¹ V'`, read on both sides as a module over the ring of
functions on the open of `Y`: a morphism of `Γ(V, 𝒪_Y)`-modules into restriction of scalars along
`ρ : Γ(V, 𝒪_Y) ⟶ Γ(V', 𝒪_Y)`.

This is the restriction map of the sheaf of modules over `f⁻¹ V' ⊆ f⁻¹ V` and nothing more; the
only content is that the two orders of restricting scalars agree,
`preimageRestrictScalarsIso`. -/
def preimageSectionsRestrict {V V' : Opens Y.carrier} (hV : V' ≤ V) :
    preimageSections f V ⟶
      preimageSections f V' ⋙
        ModuleCat.restrictScalars ((structureSheafRing Y).obj.map hV.hom.op).hom :=
  Functor.whiskerRight (sectionsOverOpenRestrict X ((opensMap f).map hV.hom))
      (ModuleCat.restrictScalars (((structureSheafHom f).hom.app (op V)).hom)) ≫
    Functor.whiskerLeft (sectionsOverOpen X ((opensMap f).obj V'))
      (preimageRestrictScalarsIso f hV.hom).hom

/-! ### Derived sections over an inverse image -/

/-- The transformation prescribing `derivedPreimageSectionsRestrict` through the universal
property of `RΓ(f⁻¹ V, -)`: on the homotopy category, restrict the complex of sections termwise,
then compare the termwise image with the value of `RΓ(f⁻¹ V', -)` there. -/
def preimageSectionsRestrictUnit {V V' : Opens Y.carrier} (hV : V' ≤ V) :
    homotopyPreimageSections f V ⟶
      DerivedCategory.Qh ⋙
        (derivedPreimageSections f V' ⋙ restrictScalarsDerived Y hV) :=
  Functor.whiskerRight (NatTrans.mapHomotopyCategory (preimageSectionsRestrict f hV)
      (ComplexShape.up ℤ)) DerivedCategory.Qh ≫
    Functor.whiskerRight (Functor.mapHomotopyCategoryCompIso
      (Iso.refl (preimageSections f V' ⋙
        ModuleCat.restrictScalars ((structureSheafRing Y).obj.map hV.hom.op).hom))
        (ComplexShape.up ℤ)).inv DerivedCategory.Qh ≫
    Functor.whiskerLeft ((preimageSections f V').mapHomotopyCategory (ComplexShape.up ℤ))
      (ModuleCat.restrictScalars
        ((structureSheafRing Y).obj.map hV.hom.op).hom).mapDerivedCategoryFactorsh.inv ≫
    Functor.whiskerRight (derivedPreimageSectionsUnit f V') (restrictScalarsDerived Y hV)

/-- **Restriction in the open, on derived sections over an inverse image.**
`RΓ(f⁻¹ V, -) ⟶ RΓ(f⁻¹ V', -) ⋙ R Res_ρ`, the transformation induced by
`preimageSectionsRestrictUnit` through the universal property of the right derived functor of
sections over `f⁻¹ V`.  By `derivedPreimageSectionsRestrict_fac` its composite with
`Stacks.Cohomology.DerivedSectionsLeray.derivedPreimageSectionsUnit` is that transformation, and
by `derivedPreimageSectionsRestrict_ext` that equation determines it. -/
def derivedPreimageSectionsRestrict {V V' : Opens Y.carrier} (hV : V' ≤ V) :
    derivedPreimageSections f V ⟶
      derivedPreimageSections f V' ⋙ restrictScalarsDerived Y hV :=
  (derivedPreimageSections f V).rightDerivedDesc (derivedPreimageSectionsUnit f V)
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing X)) (ComplexShape.up ℤ)) _
    (preimageSectionsRestrictUnit f hV)

/-- The equation characterizing the derived restriction: composing it with the unit of
`RΓ(f⁻¹ V, -)` recovers the termwise restriction of sections. -/
theorem derivedPreimageSectionsRestrict_fac {V V' : Opens Y.carrier} (hV : V' ≤ V) :
    derivedPreimageSectionsUnit f V ≫
        Functor.whiskerLeft DerivedCategory.Qh (derivedPreimageSectionsRestrict f hV) =
      preimageSectionsRestrictUnit f hV :=
  (derivedPreimageSections f V).rightDerived_fac (derivedPreimageSectionsUnit f V)
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing X)) (ComplexShape.up ℤ)) _
    (preimageSectionsRestrictUnit f hV)

/-- The equation of `derivedPreimageSectionsRestrict_fac` determines the derived restriction: two
transformations out of `RΓ(f⁻¹ V, -)` that agree after composition with the unit are equal.

This is how a square involving the derived restriction is proved: not by a diagram chase on
derived-category objects, but on the homotopy category, where restriction of sections is
termwise. -/
theorem derivedPreimageSectionsRestrict_ext {V : Opens Y.carrier}
    {G : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)) ⥤
      DerivedCategory (ModuleCat.{u} ((structureSheafRing Y).obj.obj (op V)))}
    (τ₁ τ₂ : derivedPreimageSections f V ⟶ G)
    (h : derivedPreimageSectionsUnit f V ≫ Functor.whiskerLeft DerivedCategory.Qh τ₁ =
      derivedPreimageSectionsUnit f V ≫ Functor.whiskerLeft DerivedCategory.Qh τ₂) :
    τ₁ = τ₂ :=
  (derivedPreimageSections f V).rightDerived_ext (derivedPreimageSectionsUnit f V)
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing X)) (ComplexShape.up ℤ))
    _ _ _ h

/-- `derivedPreimageSectionsRestrict_fac` at an object of the homotopy category.  This is the
form in which the layer-2 square of the module documentation consumes it. -/
theorem derivedPreimageSectionsRestrict_fac_app {V V' : Opens Y.carrier} (hV : V' ≤ V)
    (Z : HomotopyCategory (SheafOfModules.{u} (structureSheafRing X)) (ComplexShape.up ℤ)) :
    (derivedPreimageSectionsUnit f V).app Z ≫
        (derivedPreimageSectionsRestrict f hV).app (DerivedCategory.Qh.obj Z) =
      (preimageSectionsRestrictUnit f hV).app Z :=
  (derivedPreimageSections f V).rightDerived_fac_app (derivedPreimageSectionsUnit f V)
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing X)) (ComplexShape.up ℤ)) _
    (preimageSectionsRestrictUnit f hV) Z

/-- **The comparison of Tag 0D5W at a K-injective complex, as an explicit composite.**
`Stacks.Cohomology.UnboundedHigherDirectImage.preimageSectionsKInjectiveIso` is built as a chain
of four isomorphisms; this spells its forward direction out, so that a statement about it can be
reduced to statements about the four canonical comparisons separately.  It holds by `rfl`: the
only content is that the composite of a chain of isomorphisms is the composite of its legs. -/
theorem preimageSectionsKInjectiveIso_hom (V : Opens Y.carrier)
    (W : CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ) (hW : W.IsKInjective) :
    (Stacks.Cohomology.UnboundedHigherDirectImage.preimageSectionsKInjectiveIso
          f V W hW).hom =
      (DerivedCategory.quotientCompQhIso
            (ModuleCat.{u} ((structureSheafRing Y).obj.obj (op V)))).inv.app
          (((preimageSections f V).mapHomologicalComplex (ComplexShape.up ℤ)).obj W) ≫
        DerivedCategory.Qh.map
            (((preimageSections f V).mapHomotopyCategoryFactors
              (ComplexShape.up ℤ)).inv.app W) ≫
          (derivedPreimageSectionsUnit f V).app
              ((HomotopyCategory.quotient (SheafOfModules.{u} (structureSheafRing X))
                (ComplexShape.up ℤ)).obj W) ≫
            (derivedPreimageSections f V).map
              ((DerivedCategory.quotientCompQhIso
                (SheafOfModules.{u} (structureSheafRing X))).hom.app W) :=
  rfl

end Stacks.Cohomology.DerivedSectionsLeray

end
