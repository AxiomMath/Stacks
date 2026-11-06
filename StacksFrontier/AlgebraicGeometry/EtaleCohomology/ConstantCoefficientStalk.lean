module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SitePointStalkAdditive
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.StalkSemilinearComparison
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPushforwardModules.HasSheafComposeForget
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSite
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstantCoefficientsExact
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TorAmplitude.LocallyFiniteTorDimension
public import StacksFrontier.CategoryTheory.Sites.Localization.RingedSiteLocalization
public import StacksFrontier.CategoryTheory.Sites.Point.ConstantSheafFiber
public import StacksFrontier.CategoryTheory.Sites.Point.LocalizedPoint
public import StacksFrontier.CategoryTheory.Sites.Point.UniverseChange
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPushforwardModules.HasSheafComposeForget

/-!
# The stalk of a sheaf of modules over the constant coefficient ring sheaf

Let `Λ` be a coefficient ring and `X` a scheme in a big étale site `B`. A sheaf of `Λ`-modules on
the small étale site of `X` becomes a sheaf of modules over the constant coefficient ring sheaf
by sheafifying the action of the constant sections, and the stalk of that sheaf of modules at a
point `Φ` of the site is a module over the stalk of the constant coefficient ring sheaf, which is
`Λ` itself. This file identifies that stalk with the fibre of the original sheaf of `Λ`-modules,
naturally in the sheaf, and degreewise on cochain complexes.

## Main definitions

* `AlgebraicGeometry.constantCoefficientRingFiberEquiv` : the fibre of the constant coefficient
  ring sheaf at a point of the small étale site is `Λ`.
* `AlgebraicGeometry.upliftedEtaleFiberFunctor` : the fibre at a point of the small étale site of
  a sheaf of `Λ`-modules, with its sections lifted into the universe of the site.
* `AlgebraicGeometry.toModuleSheafOverConstantCoefficients` : the sheafification map carrying the
  ulifted sections of a sheaf of `Λ`-modules to the sections of the associated sheaf of modules
  over the constant coefficient ring sheaf.

## Main results

* `AlgebraicGeometry.moduleSheafOverConstantCoefficientsFiberIso` : **the stalk of the sheaf of
  modules over the constant coefficient ring sheaf is the fibre of the sheaf of `Λ`-modules**, as
  an isomorphism of `Λ`-modules through the identification of the stalk of the constant
  coefficient ring sheaf with `Λ`.
* `AlgebraicGeometry.moduleSheafOverConstantCoefficientsFiberNatIso` : the same, as an isomorphism
  of functors.
* `AlgebraicGeometry.moduleSheafOverConstantCoefficientsFiberComplexIso` : the same applied
  degreewise to a cochain complex.
* `AlgebraicGeometry.preservesColimit_moduleCatUliftFunctor` : the universe lift of the sections
  of a module preserves every colimit whose shape is finally small for those sections.
* `AlgebraicGeometry.uliftPointPresheafFiberIso` : the fibre at the universe lift of a point of
  the ulifted sections of a presheaf of modules is the uplift of its fibre at the point itself.
* `AlgebraicGeometry.upliftedEtaleFiberIso` : at the universe lift of the point of a geometric
  point, that fibre is the uplift of the étale stalk.
* `AlgebraicGeometry.etaleModuleStalkFiberIso` : **the étale stalk at a geometric point is the
  stalk of the associated sheaf of modules over the constant coefficient ring sheaf**, up to the
  universe lift of its sections.
* `AlgebraicGeometry.presheafFiberOverIso_hom_toPresheafFiber` : the comparison of Stacks 04H2
  takes a germ at the lift of a point to a slice site to the germ at the point itself.
* `AlgebraicGeometry.constantCoefficientRingOverFiberEquiv` : the fibre of the structure sheaf
  of the localized ringed site, at a lift of a point to the slice, is again `Λ`.
* `AlgebraicGeometry.moduleSheafOverConstantCoefficientsOverFiberIso` : **the restriction to a
  slice of the sheaf of modules over the constant coefficient ring sheaf has, as its stalk at a
  lift of the point, the fibre of the sheaf of `Λ`-modules** — the change of coefficients
  commutes with `SheafOfModules.overFunctor`, read at a point of the slice.
* `AlgebraicGeometry.moduleSheafOverConstantCoefficientsOverFiberNatIso` and
  `AlgebraicGeometry.moduleSheafOverConstantCoefficientsOverFiberComplexIso` : the same, as an
  isomorphism of functors and degreewise on cochain complexes.
* `AlgebraicGeometry.moduleCatUliftFunctorIdIso` : the universe lift of the sections of a module
  into their own universe is the identity functor.
* `AlgebraicGeometry.upliftedEtaleFiberFunctorIso` : at module universe `max (u + 1) r` the
  comparison's source `AlgebraicGeometry.upliftedEtaleFiberFunctor` is the fibre functor on
  sheaves.
* `AlgebraicGeometry.moduleSheafOverConstantCoefficientsSheafFiberComplexIso` : the slice
  comparison on cochain complexes, read through the fibre functor on sheaves.
* `AlgebraicGeometry.exists_hasTorAmplitude_derivedRestriction_of_point` : an object of locally
  finite Tor dimension has Tor amplitude in a concrete interval after restriction to some object
  above one carrying a lift of a given point of the site.

## Implementation notes

The target of the comparison is the fibre of the *ulifted* presheaf
`F.obj ⋙ ModuleCat.uliftFunctor`, not `Φ.sheafFiber` of `F` itself: a point of the small étale
site of a `u`-scheme has its fibres in the universe `max (u + 1) w r` containing the site, the
coefficients and the module sections, and the sections of `F` live in `w` alone. Identifying the
fibre of the ulifted presheaf with the uplift of `Φ.sheafFiber` of `F` needs the module universe
`w` to receive `max (u + 1) r`, so it is not available at this generality; where it is available,
`CategoryTheory.Limits.preservesColimitIso` supplies it, as in the proof of
`AlgebraicGeometry.stalk_projective`.

For a point which is the universe lift of a point whose fibres already live in the universe of
the site, however, no inequality is needed: the fibre is computed by the colimit over the
unlifted category of pointed neighbourhoods, which is cofinal in the lifted one, and over such a
shape the universe lift of the sections preserves colimits. The points of the small étale site
coming from geometric points are of this form, so for them the identification holds outright,
and the comparison reads as a statement about `AlgebraicGeometry.etaleModuleStalkFunctor`
itself.

The functors compared are the ones already in the library:
`AlgebraicGeometry.moduleSheafOverConstantCoefficientsFunctor` of
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/ConstantCoefficientsExact.lean`, which is the
functor the Tor-amplitude conditions on the small étale site are stated through, and
`Stacks.sheafModuleFiberOfCommRing`. The two spellings of the ring sheaf of the site — the
ringed-site one, `Stacks.SheafOfModules.Tensor.ringSheaf` of the structure sheaf of
`AlgebraicGeometry.constantCoefficientRingedSite`, and `Stacks.commRingSheafToRingSheaf` — are
definitionally equal, so no bridge between them is needed; they are not equal at the
transparency of instance search, so `AlgebraicGeometry.toModuleSheafOverConstantCoefficients`
states its target in the spelling of `Stacks.moduleStalkIso`, and the composite with
`Stacks.sheafModuleFiberOfCommRing` gets its zero-morphism instance from the comparison itself.

The comparison itself is `Stacks.moduleStalkIso`, whose hypotheses are discharged here: the ring
identification is `AlgebraicGeometry.constantCoefficientRingFiberEquiv`, the semilinear
comparison morphism is the sheafification map of presheaves of modules, and the fibre functor
inverts it because it is locally bijective. In particular this comparison *is* the statement that
the fibre does not see the sheafification along
`AlgebraicGeometry.constantCoefficientRingMap`.

The comparisons on the localized ringed site `(constantCoefficientRingedSite B X Λ).over V` need
no new colimit computation: the fibre functor at the lift `Φ.over x` of a point to the slice
agrees with the fibre functor at `Φ` on restricted presheaves, which is Stacks 04H2 in the form
`CategoryTheory.GrothendieckTopology.Point.presheafFiberOverIso`. Both the identification of the
fibre of the localized structure sheaf with `Λ` and the inversion of the restricted
sheafification map by the slice fibre functor are read off from that one natural isomorphism, and
the module comparison is again `Stacks.moduleStalkIso`, now at `Φ.over x`.

The slice site has the same universes as the site itself, `RingedSite.over` sending
`RingedSite.{u + 1, u, max (u + 1) w r}` to `RingedSite.{u + 1, u, max (u + 1) w r}`, so the
comparisons are stated at the same universes as the unsliced ones.

The comparisons are stated with the fibre of the *ulifted* sections, which is what is available
at a free module universe `w`. The trivialization chain of Stacks 09BI instead works at module
universe `max (u + 1) r`, and reads fibres through `GrothendieckTopology.Point.sheafFiber`. At
that universe the two agree, because `ModuleCat.uliftFunctor` into the same universe is the
identity; `AlgebraicGeometry.upliftedEtaleFiberFunctorIso` is that identification and
`AlgebraicGeometry.moduleSheafOverConstantCoefficientsSheafFiberComplexIso` is the slice
comparison transported across it.

## References

* [Stacks Project, Tag 03TR](https://stacks.math.columbia.edu/tag/03TR)
* [Stacks Project, Tag 04EQ](https://stacks.math.columbia.edu/tag/04EQ)
* [Stacks Project, Tag 04H2](https://stacks.math.columbia.edu/tag/04H2)
* [Stacks Project, Tag 04IX](https://stacks.math.columbia.edu/tag/04IX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u w r

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) (X : B.Scheme) (Λ : Type r) [CommRing Λ]

attribute [local instance] SheafOfModules.hasSheafify_commRingCat
  SheafOfModules.wEqualsLocallyBijective_commRingCat
  GrothendieckTopology.hasSheafify_addCommGrpCat
  SheafOfModules.wEqualsLocallyBijective_addCommGrpCat

/-! ### The fibre of the constant coefficient ring sheaf -/

/-- The fibre at a point of the small étale site of the constant coefficient ring sheaf is the
coefficient ring `Λ` itself: the fibre of a constant sheaf is its value. -/
def constantCoefficientRingFiberEquiv
    (Φ : (SmallEtale.topology B X.obj X.property).Point.{max (u + 1) w r}) :
    Λ ≃+* (Φ.presheafFiber (A := CommRingCat.{max (u + 1) w r})).obj
      (constantCoefficientSheaf.{u, w, r} B X Λ).obj :=
  (ULift.ringEquiv (R := Λ)).symm.trans
    (Sites.constantSheafFiberIso Φ
      (CommRingCat.of (ULift.{max (u + 1) w} Λ))).symm.commRingCatIsoToRingEquiv

/-- If an isomorphism of commutative rings sends `x` to `y`, its inverse sends `y` back to `x`. -/
private lemma eq_inv_apply_of_hom_apply_eq {A B : CommRingCat.{w}} (e : A ≅ B) {x : A} {y : B}
    (h : e.hom x = y) : x = e.inv y :=
  (ConcreteCategory.congr_hom e.hom_inv_id x).symm.trans (congrArg e.inv h)

/-- The germ at any neighbourhood of a point of the image of a constant under
`AlgebraicGeometry.constantCoefficientRingMap` is that constant, read through
`AlgebraicGeometry.constantCoefficientRingFiberEquiv`. -/
lemma ringStalkGerm_constantCoefficientRingMap
    (Φ : (SmallEtale.topology B X.obj X.property).Point.{max (u + 1) w r})
    (U : SmallEtale B X.obj X.property) (x : Φ.fiber.obj U) (c : Λ) :
    Stacks.ringStalkGerm Φ (constantCoefficientSheaf.{u, w, r} B X Λ) U x
        ((constantCoefficientRingMap.{u, w, r} B X Λ).app (op U) (ULift.up c)) =
      constantCoefficientRingFiberEquiv.{u, w, r} B X Λ Φ c := by
  exact eq_inv_apply_of_hom_apply_eq
    (Sites.constantSheafFiberIso Φ (CommRingCat.of (ULift.{max (u + 1) w} Λ)))
    (Sites.constantSheafFiberIso_toSheafify_app Φ
      (CommRingCat.of (ULift.{max (u + 1) w} Λ)) U x (ULift.up c))

/-! ### The fibre of a sheaf of `Λ`-modules -/

/-- The fibre at a point of the small étale site of a sheaf of `Λ`-modules, with its sections
lifted into the universe containing the site, the coefficients and the sections. -/
def upliftedEtaleFiberFunctor
    (Φ : (SmallEtale.topology B X.obj X.property).Point.{max (u + 1) w r}) :
    Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{w} Λ) ⥤
      ModuleCat.{max (u + 1) w r} Λ :=
  sheafToPresheaf _ _ ⋙
    (Functor.whiskeringRight _ _ _).obj (ModuleCat.uliftFunctor.{max (u + 1) r} Λ) ⋙
      Φ.presheafFiber (A := ModuleCat.{max (u + 1) w r} Λ)

/-! ### The stalk of the sheaf of modules over the constant coefficient ring sheaf -/

/-- The sheafification map of the module presheaf over the constant presheaf of rings, read as a
morphism of presheaves of abelian groups from the ulifted sections of a sheaf of `Λ`-modules to
the sections of the associated sheaf of modules over the constant coefficient ring sheaf. -/
def toModuleSheafOverConstantCoefficients
    (F : Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{w} Λ)) :
    (F.obj ⋙ ModuleCat.uliftFunctor.{max (u + 1) r} Λ) ⋙
        forget₂ (ModuleCat.{max (u + 1) w r} Λ) AddCommGrpCat.{max (u + 1) w r} ⟶
      (_root_.SheafOfModules.val
        (R := Stacks.commRingSheafToRingSheaf.{u, u + 1, max (u + 1) w r}
          (constantCoefficientSheaf.{u, w, r} B X Λ))
        ((moduleSheafOverConstantCoefficientsFunctor.{u, w, r} B X Λ).obj F)).presheaf :=
  CategoryTheory.toSheafify (SmallEtale.topology B X.obj X.property)
    (modulePresheafOverConstantCoefficients.{u, w, r} B X Λ F).presheaf

/-- The fibre functor at a point of the small étale site inverts the sheafification map of the
module presheaf over the constant presheaf of rings: that map is locally bijective. -/
instance isIso_presheafFiber_map_toModuleSheafOverConstantCoefficients
    (Φ : (SmallEtale.topology B X.obj X.property).Point.{max (u + 1) w r})
    (F : Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{w} Λ)) :
    IsIso (Φ.presheafFiber.map (toModuleSheafOverConstantCoefficients.{u, w, r} B X Λ F)) :=
  Φ.W_isInvertedBy_presheafFiber _ (GrothendieckTopology.W_toSheafify _ _)

/-- The family of ring maps from `Λ` to the sections of the constant coefficient ring sheaf
which the module structure of a sheaf of `Λ`-modules is semilinear over. -/
def constantCoefficientSections
    (U : (SmallEtale B X.obj X.property)ᵒᵖ) :
    Λ →+* (constantCoefficientSheaf.{u, w, r} B X Λ).obj.obj U :=
  ((constantCoefficientRingMap.{u, w, r} B X Λ).app U).hom.comp
    (ULift.ringEquiv.{r, max (u + 1) w} (R := Λ)).symm.toRingHom

/-- **The stalk of the sheaf of modules over the constant coefficient ring sheaf is the fibre of
the sheaf of `Λ`-modules.** The identification is through
`AlgebraicGeometry.constantCoefficientRingFiberEquiv`, and it sends a germ of a section to the
germ of its image under the sheafification map. -/
def moduleSheafOverConstantCoefficientsFiberIso
    (Φ : (SmallEtale.topology B X.obj X.property).Point.{max (u + 1) w r})
    (F : Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{w} Λ)) :
    (upliftedEtaleFiberFunctor.{u, w, r} B X Λ Φ).obj F ≅
      (ModuleCat.restrictScalars
          (constantCoefficientRingFiberEquiv.{u, w, r} B X Λ Φ).toRingHom).obj
        (Stacks.moduleStalk Φ (constantCoefficientSheaf.{u, w, r} B X Λ)
          ((moduleSheafOverConstantCoefficientsFunctor.{u, w, r} B X Λ).obj F)) :=
  Stacks.moduleStalkIso Φ (constantCoefficientSheaf.{u, w, r} B X Λ)
    (F.obj ⋙ ModuleCat.uliftFunctor.{max (u + 1) r} Λ)
    ((moduleSheafOverConstantCoefficientsFunctor.{u, w, r} B X Λ).obj F)
    (toModuleSheafOverConstantCoefficients.{u, w, r} B X Λ F)
    (constantCoefficientRingFiberEquiv.{u, w, r} B X Λ Φ)
    (constantCoefficientSections.{u, w, r} B X Λ)
    (ringStalkGerm_constantCoefficientRingMap.{u, w, r} B X Λ Φ)
    (fun U c m => ((PresheafOfModules.toSheafify
      (constantCoefficientRingMap.{u, w, r} B X Λ)
      (CategoryTheory.toSheafify (SmallEtale.topology B X.obj X.property)
        (modulePresheafOverConstantCoefficients.{u, w, r} B X Λ F).presheaf)).app U).hom.map_smul
      (ULift.up c) m)

/-- **The comparison is an isomorphism of functors.** The stalk of the sheaf of modules over the
constant coefficient ring sheaf is the fibre of the sheaf of `Λ`-modules, naturally in the sheaf
of `Λ`-modules. -/
def moduleSheafOverConstantCoefficientsFiberNatIso
    (Φ : (SmallEtale.topology B X.obj X.property).Point.{max (u + 1) w r}) :
    upliftedEtaleFiberFunctor.{u, w, r} B X Λ Φ ≅
      moduleSheafOverConstantCoefficientsFunctor.{u, w, r} B X Λ ⋙
        Stacks.sheafModuleFiberOfCommRing Φ (constantCoefficientSheaf.{u, w, r} B X Λ) ⋙
          ModuleCat.restrictScalars
            (constantCoefficientRingFiberEquiv.{u, w, r} B X Λ Φ).toRingHom :=
  NatIso.ofComponents (moduleSheafOverConstantCoefficientsFiberIso.{u, w, r} B X Λ Φ)
    (fun {F F'} f => by
      refine Stacks.moduleStalkIso_naturality Φ (constantCoefficientSheaf.{u, w, r} B X Λ)
        (constantCoefficientRingFiberEquiv.{u, w, r} B X Λ Φ)
        (constantCoefficientSections.{u, w, r} B X Λ)
        (ringStalkGerm_constantCoefficientRingMap.{u, w, r} B X Λ Φ)
        (toModuleSheafOverConstantCoefficients.{u, w, r} B X Λ F)
        (toModuleSheafOverConstantCoefficients.{u, w, r} B X Λ F') _ _
        (Functor.whiskerRight
          ((sheafToPresheaf (SmallEtale.topology B X.obj X.property)
            (ModuleCat.{w} Λ)).map f) (ModuleCat.uliftFunctor.{max (u + 1) r} Λ))
        ((moduleSheafOverConstantCoefficientsFunctor.{u, w, r} B X Λ).map f) ?_
      intro U m
      exact ConcreteCategory.congr_hom
        (congrArg (fun k => PresheafOfModules.Hom.app k U)
          ((PresheafOfModules.sheafificationAdjunction.{max (u + 1) w r}
            (constantCoefficientRingMap.{u, w, r} B X Λ)).unit.naturality
              ((modulePresheafOverConstantCoefficientsFunctor.{u, w, r} B X Λ).map f))) m)

/-! ### The comparison degreewise on complexes -/

/-- The ulifted fibre functor `upliftedEtaleFiberFunctor B X Λ Φ` on sheaves of `Λ`-modules
preserves zero morphisms. -/
instance upliftedEtaleFiberFunctor_preservesZeroMorphisms
    (Φ : (SmallEtale.topology B X.obj X.property).Point.{max (u + 1) w r}) :
    (upliftedEtaleFiberFunctor.{u, w, r} B X Λ Φ).PreservesZeroMorphisms :=
  inferInstanceAs (sheafToPresheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{w} Λ) ⋙
    (Functor.whiskeringRight _ _ _).obj (ModuleCat.uliftFunctor.{max (u + 1) r} Λ) ⋙
      Φ.presheafFiber (A := ModuleCat.{max (u + 1) w r} Λ)).PreservesZeroMorphisms

/-- The functor sending a sheaf of `Λ`-modules to the stalk at `Φ` of the associated sheaf of
modules over the constant coefficient ring sheaf, with scalars restricted to `Λ`, preserves zero
morphisms. -/
instance moduleSheafOverConstantCoefficientsFiber_preservesZeroMorphisms
    (Φ : (SmallEtale.topology B X.obj X.property).Point.{max (u + 1) w r}) :
    (moduleSheafOverConstantCoefficientsFunctor.{u, w, r} B X Λ ⋙
      Stacks.sheafModuleFiberOfCommRing Φ (constantCoefficientSheaf.{u, w, r} B X Λ) ⋙
        ModuleCat.restrictScalars
          (constantCoefficientRingFiberEquiv.{u, w, r} B X Λ
            Φ).toRingHom).PreservesZeroMorphisms :=
  Functor.preservesZeroMorphisms_of_iso
    (moduleSheafOverConstantCoefficientsFiberNatIso.{u, w, r} B X Λ Φ)

/-- **The comparison applied degreewise to cochain complexes.** The complex of fibres of a
cochain complex of sheaves of `Λ`-modules is the complex of stalks of the associated complex of
sheaves of modules over the constant coefficient ring sheaf. -/
def moduleSheafOverConstantCoefficientsFiberComplexIso
    (Φ : (SmallEtale.topology B X.obj X.property).Point.{max (u + 1) w r}) :
    (upliftedEtaleFiberFunctor.{u, w, r} B X Λ Φ).mapHomologicalComplex (ComplexShape.up ℤ) ≅
      (moduleSheafOverConstantCoefficientsFunctor.{u, w, r} B X Λ ⋙
        Stacks.sheafModuleFiberOfCommRing Φ (constantCoefficientSheaf.{u, w, r} B X Λ) ⋙
          ModuleCat.restrictScalars
            (constantCoefficientRingFiberEquiv.{u, w, r} B X Λ
              Φ).toRingHom).mapHomologicalComplex (ComplexShape.up ℤ) :=
  NatIso.mapHomologicalComplex
    (moduleSheafOverConstantCoefficientsFiberNatIso.{u, w, r} B X Λ Φ) (ComplexShape.up ℤ)

/-! ### The fibre at the universe lift of a point -/

section UniverseLift

universe z z' w' uA vA uK vK uC vC rr

variable {C : Type uC} [Category.{vC} C] {J : GrothendieckTopology C}

/-- The universe lift of the sections of a module preserves every colimit whose shape is finally
small for the universe of the sections: either some value of the diagram is nonzero, and then
that universe receives the universe of the shape, or every value is zero and both colimits are
zero. No inequality between the two universes is assumed. -/
lemma preservesColimit_moduleCatUliftFunctor {K : Type uK} [Category.{vK} K]
    [FinallySmall.{z} K] (R : Type rr) [Ring R]
    [HasColimitsOfSize.{z, z} (ModuleCat.{w} R)]
    [HasColimitsOfSize.{z, z} AddCommGrpCat.{max w w'}] (D : K ⥤ ModuleCat.{w} R) :
    PreservesColimit D (ModuleCat.uliftFunctor.{w'} R) := by
  by_cases hD : ∀ k, IsZero (D.obj k)
  · refine ⟨fun {c} hc => ⟨?_⟩⟩
    have hpt : IsZero c.pt := by
      rw [IsZero.iff_id_eq_zero]
      refine hc.hom_ext fun k => ?_
      rw [Category.comp_id, comp_zero]
      exact (hD k).eq_zero_of_src _
    exact
      { desc := fun _ => 0
        fac := fun s k => by
          have h := ((ModuleCat.uliftFunctor.{w'} R).map_isZero (hD k)).eq_zero_of_src
            (s.ι.app k)
          rw [comp_zero, h]
        uniq := fun _ m _ =>
          ((ModuleCat.uliftFunctor.{w'} R).map_isZero hpt).eq_zero_of_src m }
  · simp only [not_forall] at hD
    obtain ⟨k, hk⟩ := hD
    have : UnivLE.{z, w} := univLE_of_coproducts (D.obj k)
      (fun h => hk ((IsZero.iff_id_eq_zero _).mpr h))
    have : HasColimitsOfSize.{z, z} AddCommGrpCat.{w} := inferInstance
    have : HasColimitsOfShape K AddCommGrpCat.{w} :=
      hasColimitsOfShape_of_finallySmall K _
    have : HasColimitsOfShape K AddCommGrpCat.{max w w'} :=
      hasColimitsOfShape_of_finallySmall K _
    have : PreservesColimit D (ModuleCat.uliftFunctor.{w'} R ⋙
        forget₂ (ModuleCat.{max w w'} R) AddCommGrpCat.{max w w'}) := by
      show PreservesColimit D (forget₂ (ModuleCat.{w} R) AddCommGrpCat.{w} ⋙
        AddCommGrpCat.uliftFunctor.{w'})
      infer_instance
    exact preservesColimit_of_reflects_of_preserves (ModuleCat.uliftFunctor.{w'} R)
      (forget₂ (ModuleCat.{max w w'} R) AddCommGrpCat.{max w w'})

variable (p : J.Point.{z}) {R : Type rr} [Ring R]
  [HasColimitsOfSize.{z, z} (ModuleCat.{w} R)]
  [HasColimitsOfSize.{z, z} AddCommGrpCat.{max w w'}]
  [HasColimitsOfSize.{max z z', max z z'} (ModuleCat.{max w w'} R)]
  (P : Cᵒᵖ ⥤ ModuleCat.{w} R)

/-- **The fibre at the universe lift of a point of the ulifted sections of a presheaf of modules
is the uplift of its fibre at the point itself.** The elements of the lifted fibre functor are
the elements of the fibre functor, and the uplift of the sections commutes with the colimit over
them. -/
def uliftPointPresheafFiberIso :
    ((p.ulift.{z'}).presheafFiber (A := ModuleCat.{max w w'} R)).obj
        (P ⋙ ModuleCat.uliftFunctor.{w'} R) ≅
      (ModuleCat.uliftFunctor.{w'} R).obj ((p.presheafFiber (A := ModuleCat.{w} R)).obj P) :=
  haveI : (Functor.Elements.ulift.{z'} p.fiber).Initial :=
    Functor.initial_of_adjunction (Functor.Elements.uliftEquiv.{z'} p.fiber).toAdjunction
  haveI : PreservesColimit ((CategoryOfElements.π p.fiber).op ⋙ P)
      (ModuleCat.uliftFunctor.{w'} R) :=
    preservesColimit_moduleCatUliftFunctor R ((CategoryOfElements.π p.fiber).op ⋙ P)
  haveI hshape : HasColimitsOfShape ((p.ulift.{z'}).fiber.Elementsᵒᵖ)
      (ModuleCat.{max w w'} R) := hasColimitsOfShape_of_finallySmall _ _
  (@Functor.Final.colimitIso _ _ _ _ (Functor.Elements.ulift.{z'} p.fiber).op _ _ _
      ((CategoryOfElements.π (p.ulift.{z'}).fiber).op ⋙ P ⋙
        ModuleCat.uliftFunctor.{w'} R) (hshape.has_colimit _)).symm ≪≫
    (preservesColimitIso (ModuleCat.uliftFunctor.{w'} R)
      ((CategoryOfElements.π p.fiber).op ⋙ P)).symm

/-- The comparison takes the germ at a lift of the point of a ulifted section to the uplift of
the germ of that section. -/
lemma uliftPointPresheafFiberIso_hom_toPresheafFiber (X : C) (x : p.fiber.obj X) :
    (p.ulift.{z'}).toPresheafFiber X (ULift.up x) (P ⋙ ModuleCat.uliftFunctor.{w'} R) ≫
        (uliftPointPresheafFiberIso p P).hom =
      (ModuleCat.uliftFunctor.{w'} R).map (p.toPresheafFiber X x P) :=
  have : (Functor.Elements.ulift.{z'} p.fiber).Initial :=
    Functor.initial_of_adjunction (Functor.Elements.uliftEquiv.{z'} p.fiber).toAdjunction
  have : PreservesColimit ((CategoryOfElements.π p.fiber).op ⋙ P)
      (ModuleCat.uliftFunctor.{w'} R) :=
    preservesColimit_moduleCatUliftFunctor R ((CategoryOfElements.π p.fiber).op ⋙ P)
  have hshape : HasColimitsOfShape ((p.ulift.{z'}).fiber.Elementsᵒᵖ)
      (ModuleCat.{max w w'} R) := hasColimitsOfShape_of_finallySmall _ _
  Eq.trans (Category.assoc _ _ _).symm
    (Eq.trans
      (congrArg (fun k => k ≫ (preservesColimitIso (ModuleCat.uliftFunctor.{w'} R)
          ((CategoryOfElements.π p.fiber).op ⋙ P)).inv)
        (@Functor.Final.ι_colimitIso_inv _ _ _ _ (Functor.Elements.ulift.{z'} p.fiber).op _ _ _
          ((CategoryOfElements.π (p.ulift.{z'}).fiber).op ⋙ P ⋙
            ModuleCat.uliftFunctor.{w'} R) (hshape.has_colimit _) (op (Functor.elementsMk _ X x))))
      (ι_preservesColimitIso_inv (ModuleCat.uliftFunctor.{w'} R)
        ((CategoryOfElements.π p.fiber).op ⋙ P) (op (Functor.elementsMk _ X x))))

end UniverseLift

/-! ### The fibre at a geometric point of the small étale site -/

section EtaleStalk

variable [HasColimitsOfSize.{u, u} (ModuleCat.{w} Λ)]

/-- **The fibre of the ulifted sections at the universe lift of a geometric point is the uplift
of the étale stalk at that point.** The étale neighbourhoods of a geometric point are the same
whether its fibres are formed in the universe of the site or in the larger universe of the
coefficients and the sections. -/
def upliftedEtaleFiberIso (s : GeometricPoint X.obj)
    (F : Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{w} Λ)) :
    (upliftedEtaleFiberFunctor.{u, w, r} B X Λ
        ((geometricSitePoint B X s).ulift.{max (u + 1) w r})).obj F ≅
      (ModuleCat.uliftFunctor.{max (u + 1) r} Λ).obj
        ((etaleModuleStalkFunctor B X Λ s).obj F) :=
  uliftPointPresheafFiberIso.{w, u, max (u + 1) w r, max (u + 1) r}
    (geometricSitePoint B X s) F.obj

/-- **The étale stalk at a geometric point of a sheaf of `Λ`-modules is the stalk of the
associated sheaf of modules over the constant coefficient ring sheaf**, as `Λ`-modules through
`AlgebraicGeometry.constantCoefficientRingFiberEquiv`, after lifting the sections of the étale
stalk into the universe of the comparison. -/
def etaleModuleStalkFiberIso (s : GeometricPoint X.obj)
    (F : Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{w} Λ)) :
    (ModuleCat.uliftFunctor.{max (u + 1) r} Λ).obj
        ((etaleModuleStalkFunctor B X Λ s).obj F) ≅
      (ModuleCat.restrictScalars
          (constantCoefficientRingFiberEquiv.{u, w, r} B X Λ
            ((geometricSitePoint B X s).ulift.{max (u + 1) w r})).toRingHom).obj
        (Stacks.moduleStalk ((geometricSitePoint B X s).ulift.{max (u + 1) w r})
          (constantCoefficientSheaf.{u, w, r} B X Λ)
          ((moduleSheafOverConstantCoefficientsFunctor.{u, w, r} B X Λ).obj F)) :=
  (upliftedEtaleFiberIso.{u, w, r} B X Λ s F).symm ≪≫
    moduleSheafOverConstantCoefficientsFiberIso.{u, w, r} B X Λ
      ((geometricSitePoint B X s).ulift.{max (u + 1) w r}) F

end EtaleStalk

/-! ### The fibre at a lift of a point to a slice site -/

section SliceSite

universe uC vC uA vA zz

variable {C : Type uC} [Category.{vC} C] {J : GrothendieckTopology C} [LocallySmall.{zz} C]
  (Φ : J.Point.{zz}) {V : C} (x : Φ.fiber.obj V)
  (A : Type uA) [Category.{vA} A] [HasColimitsOfSize.{zz, zz} A]

/-- The comparison of Stacks 04H2 takes the germ, at a neighbourhood of the lift `Φ.over x` of a
point to the slice site over `V`, of a section of a restricted presheaf to the germ of that
section at `Φ` itself: the pointed neighbourhoods of the lift are initial among those of `Φ`. -/
lemma presheafFiberOverIso_hom_toPresheafFiber (P : Cᵒᵖ ⥤ A) (W : Over V)
    (y : (Φ.over x).fiber.obj W) :
    (Φ.over x).toPresheafFiber W y ((Over.forget V).op ⋙ P) ≫
        ((GrothendieckTopology.Point.presheafFiberOverIso Φ x A).app P).hom =
      Φ.toPresheafFiber W.left y.val P :=
  Functor.Final.ι_colimitIso_hom (GrothendieckTopology.Point.overElements Φ x).op
    ((CategoryOfElements.π Φ.fiber).op ⋙ P) (op (Functor.elementsMk _ W y))

/-- A morphism of presheaves which the fibre functor at `Φ` inverts is inverted, after
restriction to the slice site over `V`, by the fibre functor at the lift `Φ.over x`: the two
fibre functors agree, by Stacks 04H2. -/
lemma isIso_presheafFiber_over_map_whiskerLeft {P Q : Cᵒᵖ ⥤ A} (τ : P ⟶ Q)
    [IsIso (Φ.presheafFiber.map τ)] :
    IsIso ((Φ.over x).presheafFiber.map (Functor.whiskerLeft (Over.forget V).op τ)) :=
  (NatIso.isIso_map_iff (GrothendieckTopology.Point.presheafFiberOverIso Φ x A) τ).2
    inferInstance

end SliceSite

/-! ### The two comparisons on the localized ringed site -/

section Localized

variable (Φ : (SmallEtale.topology B X.obj X.property).Point.{max (u + 1) w r})
  {V : SmallEtale B X.obj X.property} (x : Φ.fiber.obj V)

/-- **The fibre of the structure sheaf of the localized ringed site is the coefficient ring.**
At the lift `Φ.over x` of a point of the small étale site to the slice over `V`, the fibre of
`(constantCoefficientRingedSite B X Λ).over V`'s structure sheaf — the restriction of the
constant coefficient ring sheaf — is `Λ` itself. -/
def constantCoefficientRingOverFiberEquiv :
    Λ ≃+* ((Φ.over x).presheafFiber (A := CommRingCat.{max (u + 1) w r})).obj
      ((constantCoefficientRingedSite.{u, w, r} B X Λ).over V).O.obj :=
  (constantCoefficientRingFiberEquiv.{u, w, r} B X Λ Φ).trans
    ((GrothendieckTopology.Point.presheafFiberOverIso Φ x
      CommRingCat.{max (u + 1) w r}).app
        (constantCoefficientSheaf.{u, w, r} B X Λ).obj).symm.commRingCatIsoToRingEquiv

/-- The germ at any neighbourhood of `Φ.over x` of the image of a constant under
`AlgebraicGeometry.constantCoefficientRingMap` is that constant, read through
`AlgebraicGeometry.constantCoefficientRingOverFiberEquiv`. -/
lemma ringStalkGerm_over_constantCoefficientRingMap (W : Over V)
    (y : (Φ.over x).fiber.obj W) (c : Λ) :
    Stacks.ringStalkGerm (Φ.over x)
        ((constantCoefficientRingedSite.{u, w, r} B X Λ).over V).O W y
        ((constantCoefficientRingMap.{u, w, r} B X Λ).app (op W.left) (ULift.up c)) =
      constantCoefficientRingOverFiberEquiv.{u, w, r} B X Λ Φ x c := by
  exact eq_inv_apply_of_hom_apply_eq
    ((GrothendieckTopology.Point.presheafFiberOverIso Φ x
      CommRingCat.{max (u + 1) w r}).app (constantCoefficientSheaf.{u, w, r} B X Λ).obj)
    ((ConcreteCategory.congr_hom
      (presheafFiberOverIso_hom_toPresheafFiber Φ x CommRingCat.{max (u + 1) w r}
        (constantCoefficientSheaf.{u, w, r} B X Λ).obj W y)
      ((constantCoefficientRingMap.{u, w, r} B X Λ).app (op W.left) (ULift.up c))).trans
      (ringStalkGerm_constantCoefficientRingMap.{u, w, r} B X Λ Φ W.left y.val c))

/-- **The change of coefficients commutes with restriction to a slice, read at a point.** The
stalk at `Φ.over x` of the restriction to the slice over `V` of the sheaf of modules over the
constant coefficient ring sheaf is the fibre at `Φ` of the sheaf of `Λ`-modules, as `Λ`-modules
through `AlgebraicGeometry.constantCoefficientRingOverFiberEquiv`. -/
def moduleSheafOverConstantCoefficientsOverFiberIso
    (F : Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{w} Λ)) :
    (upliftedEtaleFiberFunctor.{u, w, r} B X Λ Φ).obj F ≅
      (ModuleCat.restrictScalars
          (constantCoefficientRingOverFiberEquiv.{u, w, r} B X Λ Φ x).toRingHom).obj
        (Stacks.moduleStalk (Φ.over x)
          ((constantCoefficientRingedSite.{u, w, r} B X Λ).over V).O
          ((SheafOfModules.overFunctor
              (Stacks.commRingSheafToRingSheaf.{u, u + 1, max (u + 1) w r}
                (constantCoefficientSheaf.{u, w, r} B X Λ)) V).obj
            ((moduleSheafOverConstantCoefficientsFunctor.{u, w, r} B X Λ).obj F))) :=
  ((GrothendieckTopology.Point.presheafFiberOverIso Φ x
      (ModuleCat.{max (u + 1) w r} Λ)).app
        (F.obj ⋙ ModuleCat.uliftFunctor.{max (u + 1) r} Λ)).symm ≪≫
    @Stacks.moduleStalkIso _ _ _ _ _ (Φ.over x)
      ((constantCoefficientRingedSite.{u, w, r} B X Λ).over V).O _ _
      ((Over.forget V).op ⋙ (F.obj ⋙ ModuleCat.uliftFunctor.{max (u + 1) r} Λ))
      ((SheafOfModules.overFunctor
          (Stacks.commRingSheafToRingSheaf.{u, u + 1, max (u + 1) w r}
            (constantCoefficientSheaf.{u, w, r} B X Λ)) V).obj
        ((moduleSheafOverConstantCoefficientsFunctor.{u, w, r} B X Λ).obj F))
      (Functor.whiskerLeft (Over.forget V).op
        (toModuleSheafOverConstantCoefficients.{u, w, r} B X Λ F))
      (constantCoefficientRingOverFiberEquiv.{u, w, r} B X Λ Φ x)
      (fun (W : (Over V)ᵒᵖ) => constantCoefficientSections.{u, w, r} B X Λ (op W.unop.left))
      (isIso_presheafFiber_over_map_whiskerLeft Φ x _
        (toModuleSheafOverConstantCoefficients.{u, w, r} B X Λ F))
      (ringStalkGerm_over_constantCoefficientRingMap.{u, w, r} B X Λ Φ x)
      (fun (W : (Over V)ᵒᵖ) c m => ((PresheafOfModules.toSheafify
        (constantCoefficientRingMap.{u, w, r} B X Λ)
        (CategoryTheory.toSheafify (SmallEtale.topology B X.obj X.property)
          (modulePresheafOverConstantCoefficients.{u, w, r} B X Λ F).presheaf)).app
            (op W.unop.left)).hom.map_smul (ULift.up c) m)

/-- **The slice comparison is an isomorphism of functors.** The stalk at `Φ.over x` of the
restriction to the slice over `V` of the sheaf of modules over the constant coefficient ring
sheaf is the fibre at `Φ` of the sheaf of `Λ`-modules, naturally in the sheaf of
`Λ`-modules. -/
def moduleSheafOverConstantCoefficientsOverFiberNatIso :
    upliftedEtaleFiberFunctor.{u, w, r} B X Λ Φ ≅
      moduleSheafOverConstantCoefficientsFunctor.{u, w, r} B X Λ ⋙
        SheafOfModules.overFunctor
            (Stacks.commRingSheafToRingSheaf.{u, u + 1, max (u + 1) w r}
              (constantCoefficientSheaf.{u, w, r} B X Λ)) V ⋙
          Stacks.sheafModuleFiberOfCommRing (Φ.over x)
              ((constantCoefficientRingedSite.{u, w, r} B X Λ).over V).O ⋙
            ModuleCat.restrictScalars
              (constantCoefficientRingOverFiberEquiv.{u, w, r} B X Λ Φ x).toRingHom :=
  NatIso.ofComponents
    (moduleSheafOverConstantCoefficientsOverFiberIso.{u, w, r} B X Λ Φ x)
    (fun {F F'} f => by
      have hfiber : (upliftedEtaleFiberFunctor.{u, w, r} B X Λ Φ).map f ≫
            ((GrothendieckTopology.Point.presheafFiberOverIso Φ x
              (ModuleCat.{max (u + 1) w r} Λ)).app
                (F'.obj ⋙ ModuleCat.uliftFunctor.{max (u + 1) r} Λ)).inv =
          ((GrothendieckTopology.Point.presheafFiberOverIso Φ x
              (ModuleCat.{max (u + 1) w r} Λ)).app
                (F.obj ⋙ ModuleCat.uliftFunctor.{max (u + 1) r} Λ)).inv ≫
            (Φ.over x).presheafFiber.map (Functor.whiskerLeft (Over.forget V).op
              (Functor.whiskerRight ((sheafToPresheaf
                (SmallEtale.topology B X.obj X.property) (ModuleCat.{w} Λ)).map f)
                  (ModuleCat.uliftFunctor.{max (u + 1) r} Λ))) :=
        (GrothendieckTopology.Point.presheafFiberOverIso Φ x
          (ModuleCat.{max (u + 1) w r} Λ)).inv.naturality _
      have hstalk := @Stacks.moduleStalkIso_naturality _ _ _ _ _ (Φ.over x)
        ((constantCoefficientRingedSite.{u, w, r} B X Λ).over V).O _ _
        (constantCoefficientRingOverFiberEquiv.{u, w, r} B X Λ Φ x)
        (fun (W : (Over V)ᵒᵖ) => constantCoefficientSections.{u, w, r} B X Λ (op W.unop.left))
        (ringStalkGerm_over_constantCoefficientRingMap.{u, w, r} B X Λ Φ x)
        ((Over.forget V).op ⋙ (F.obj ⋙ ModuleCat.uliftFunctor.{max (u + 1) r} Λ))
        ((Over.forget V).op ⋙ (F'.obj ⋙ ModuleCat.uliftFunctor.{max (u + 1) r} Λ))
        ((SheafOfModules.overFunctor
            (Stacks.commRingSheafToRingSheaf.{u, u + 1, max (u + 1) w r}
              (constantCoefficientSheaf.{u, w, r} B X Λ)) V).obj
          ((moduleSheafOverConstantCoefficientsFunctor.{u, w, r} B X Λ).obj F))
        ((SheafOfModules.overFunctor
            (Stacks.commRingSheafToRingSheaf.{u, u + 1, max (u + 1) w r}
              (constantCoefficientSheaf.{u, w, r} B X Λ)) V).obj
          ((moduleSheafOverConstantCoefficientsFunctor.{u, w, r} B X Λ).obj F'))
        (Functor.whiskerLeft (Over.forget V).op
          (toModuleSheafOverConstantCoefficients.{u, w, r} B X Λ F))
        (Functor.whiskerLeft (Over.forget V).op
          (toModuleSheafOverConstantCoefficients.{u, w, r} B X Λ F'))
        (isIso_presheafFiber_over_map_whiskerLeft Φ x _
          (toModuleSheafOverConstantCoefficients.{u, w, r} B X Λ F))
        (isIso_presheafFiber_over_map_whiskerLeft Φ x _
          (toModuleSheafOverConstantCoefficients.{u, w, r} B X Λ F'))
        (fun (W : (Over V)ᵒᵖ) c m => ((PresheafOfModules.toSheafify
          (constantCoefficientRingMap.{u, w, r} B X Λ)
          (CategoryTheory.toSheafify (SmallEtale.topology B X.obj X.property)
            (modulePresheafOverConstantCoefficients.{u, w, r} B X Λ F).presheaf)).app
              (op W.unop.left)).hom.map_smul (ULift.up c) m)
        (fun (W : (Over V)ᵒᵖ) c m => ((PresheafOfModules.toSheafify
          (constantCoefficientRingMap.{u, w, r} B X Λ)
          (CategoryTheory.toSheafify (SmallEtale.topology B X.obj X.property)
            (modulePresheafOverConstantCoefficients.{u, w, r} B X Λ F').presheaf)).app
              (op W.unop.left)).hom.map_smul (ULift.up c) m)
        (Functor.whiskerLeft (Over.forget V).op
          (Functor.whiskerRight ((sheafToPresheaf
            (SmallEtale.topology B X.obj X.property) (ModuleCat.{w} Λ)).map f)
              (ModuleCat.uliftFunctor.{max (u + 1) r} Λ)))
        ((SheafOfModules.overFunctor
            (Stacks.commRingSheafToRingSheaf.{u, u + 1, max (u + 1) w r}
              (constantCoefficientSheaf.{u, w, r} B X Λ)) V).map
          ((moduleSheafOverConstantCoefficientsFunctor.{u, w, r} B X Λ).map f))
        (fun W m => ConcreteCategory.congr_hom
          (congrArg (fun k => PresheafOfModules.Hom.app k (op W.unop.left))
            ((PresheafOfModules.sheafificationAdjunction.{max (u + 1) w r}
              (constantCoefficientRingMap.{u, w, r} B X Λ)).unit.naturality
                ((modulePresheafOverConstantCoefficientsFunctor.{u, w, r} B X Λ).map f))) m)
      refine Eq.trans (Category.assoc _ _ _).symm (Eq.trans (hfiber =≫ _) ?_)
      exact Eq.trans (Category.assoc _ _ _)
        (Eq.trans (_ ≫= hstalk) (Category.assoc _ _ _).symm))

/-- The functor sending a sheaf of `Λ`-modules to the stalk at `Φ.over x` of the restriction to
the slice over `V` of the associated sheaf of modules over the constant coefficient ring sheaf,
with scalars restricted to `Λ`, preserves zero morphisms. -/
instance moduleSheafOverConstantCoefficientsOverFiber_preservesZeroMorphisms :
    (moduleSheafOverConstantCoefficientsFunctor.{u, w, r} B X Λ ⋙
      SheafOfModules.overFunctor
          (Stacks.commRingSheafToRingSheaf.{u, u + 1, max (u + 1) w r}
            (constantCoefficientSheaf.{u, w, r} B X Λ)) V ⋙
        Stacks.sheafModuleFiberOfCommRing (Φ.over x)
            ((constantCoefficientRingedSite.{u, w, r} B X Λ).over V).O ⋙
          ModuleCat.restrictScalars
            (constantCoefficientRingOverFiberEquiv.{u, w, r} B X Λ Φ
              x).toRingHom).PreservesZeroMorphisms :=
  Functor.preservesZeroMorphisms_of_iso
    (moduleSheafOverConstantCoefficientsOverFiberNatIso.{u, w, r} B X Λ Φ x)

/-- **The slice comparison applied degreewise to cochain complexes.** The complex of fibres at
`Φ` of a cochain complex of sheaves of `Λ`-modules is the complex of stalks at `Φ.over x` of the
restriction to the slice over `V` of the associated complex of sheaves of modules over the
constant coefficient ring sheaf. -/
def moduleSheafOverConstantCoefficientsOverFiberComplexIso :
    (upliftedEtaleFiberFunctor.{u, w, r} B X Λ Φ).mapHomologicalComplex (ComplexShape.up ℤ) ≅
      (moduleSheafOverConstantCoefficientsFunctor.{u, w, r} B X Λ ⋙
        SheafOfModules.overFunctor
            (Stacks.commRingSheafToRingSheaf.{u, u + 1, max (u + 1) w r}
              (constantCoefficientSheaf.{u, w, r} B X Λ)) V ⋙
          Stacks.sheafModuleFiberOfCommRing (Φ.over x)
              ((constantCoefficientRingedSite.{u, w, r} B X Λ).over V).O ⋙
            ModuleCat.restrictScalars
              (constantCoefficientRingOverFiberEquiv.{u, w, r} B X Λ Φ
                x).toRingHom).mapHomologicalComplex (ComplexShape.up ℤ) :=
  NatIso.mapHomologicalComplex
    (moduleSheafOverConstantCoefficientsOverFiberNatIso.{u, w, r} B X Λ Φ x) (ComplexShape.up ℤ)

end Localized

/-! ### The universe lift collapses at the module universe of the trivialization chain -/

section UliftCollapse

/-- The universe lift of the sections of a module into their own universe is the identity
functor: the lift of a module is linearly isomorphic to it, naturally in the module. -/
def moduleCatUliftFunctorIdIso (R : Type r) [Ring R] :
    ModuleCat.uliftFunctor.{w, w} R ≅ 𝟭 (ModuleCat.{w} R) :=
  NatIso.ofComponents (fun M => (ULift.moduleEquiv (R := R) (M := M)).toModuleIso)
    (fun _ => rfl)

/-- **The fibre of the ulifted sections is the fibre of the sheaf** once the module sections are
taken in the universe `max (u + 1) r` of the comparison: there the universe lift of the sections
is the identity, so `AlgebraicGeometry.upliftedEtaleFiberFunctor` is the fibre functor on
sheaves. -/
def upliftedEtaleFiberFunctorIso
    (Φ : (SmallEtale.topology B X.obj X.property).Point.{max (u + 1) r}) :
    upliftedEtaleFiberFunctor.{u, max (u + 1) r, r} B X Λ Φ ≅
      Φ.sheafFiber (A := ModuleCat.{max (u + 1) r} Λ) :=
  Functor.isoWhiskerLeft
    (sheafToPresheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{max (u + 1) r} Λ))
    (Functor.isoWhiskerRight
        ((Functor.whiskeringRight _ _ _).mapIso (moduleCatUliftFunctorIdIso Λ) ≪≫
          Functor.whiskeringRightObjIdIso)
        (Φ.presheafFiber (A := ModuleCat.{max (u + 1) r} Λ)) ≪≫
      (Φ.presheafFiber (A := ModuleCat.{max (u + 1) r} Λ)).leftUnitor)

/-- The fibre functor on sheaves of `Λ`-modules preserves zero morphisms, at the module universe
of the comparison: it is isomorphic to `AlgebraicGeometry.upliftedEtaleFiberFunctor`, which
does. -/
lemma sheafFiber_preservesZeroMorphisms
    (Φ : (SmallEtale.topology B X.obj X.property).Point.{max (u + 1) r}) :
    (Φ.sheafFiber (A := ModuleCat.{max (u + 1) r} Λ)).PreservesZeroMorphisms :=
  Functor.preservesZeroMorphisms_of_iso (upliftedEtaleFiberFunctorIso B X Λ Φ)

/-- The collapse of the universe lift, degreewise on cochain complexes. -/
def upliftedEtaleFiberSheafFiberComplexIso
    (Φ : (SmallEtale.topology B X.obj X.property).Point.{max (u + 1) r}) :
    (upliftedEtaleFiberFunctor.{u, max (u + 1) r, r} B X Λ Φ).mapHomologicalComplex
        (ComplexShape.up ℤ) ≅
      (Φ.sheafFiber (A := ModuleCat.{max (u + 1) r} Λ)).mapHomologicalComplex
        (ComplexShape.up ℤ) :=
  letI := sheafFiber_preservesZeroMorphisms B X Λ Φ
  NatIso.mapHomologicalComplex (upliftedEtaleFiberFunctorIso B X Λ Φ) (ComplexShape.up ℤ)

/-- **The slice comparison in the spelling the trivialization chain uses.** The complex of
fibres at `Φ` of a cochain complex of sheaves of `Λ`-modules — read through the fibre functor on
sheaves, not through the ulifted sections — is the complex of stalks at `Φ.over x` of the
restriction to the slice over `V` of the associated complex of sheaves of modules over the
constant coefficient ring sheaf. -/
def moduleSheafOverConstantCoefficientsSheafFiberComplexIso
    (Φ : (SmallEtale.topology B X.obj X.property).Point.{max (u + 1) r})
    {V : SmallEtale B X.obj X.property} (x : Φ.fiber.obj V) :
    (Φ.sheafFiber (A := ModuleCat.{max (u + 1) r} Λ)).mapHomologicalComplex
        (ComplexShape.up ℤ) ≅
      (moduleSheafOverConstantCoefficientsFunctor.{u, max (u + 1) r, r} B X Λ ⋙
        SheafOfModules.overFunctor
            (Stacks.commRingSheafToRingSheaf.{u, u + 1, max (u + 1) r}
              (constantCoefficientSheaf.{u, max (u + 1) r, r} B X Λ)) V ⋙
          Stacks.sheafModuleFiberOfCommRing (Φ.over x)
              ((constantCoefficientRingedSite.{u, max (u + 1) r, r} B X Λ).over V).O ⋙
            ModuleCat.restrictScalars
              (constantCoefficientRingOverFiberEquiv.{u, max (u + 1) r, r} B X Λ Φ
                x).toRingHom).mapHomologicalComplex (ComplexShape.up ℤ) :=
  (upliftedEtaleFiberSheafFiberComplexIso B X Λ Φ).symm ≪≫
    moduleSheafOverConstantCoefficientsOverFiberComplexIso.{u, max (u + 1) r, r} B X Λ Φ x

end UliftCollapse

/-! ### Locally finite Tor dimension read at an object carrying a point -/

section LocalTorAmplitude

universe uR vR wR dR zR

attribute [local instance] Stacks.hasSheafCompose_forget₂_commRingCat

variable {Y : RingedSite.{uR, vR, wR}}
  [HasSheafify Y.J AddCommGrpCat.{wR}]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{wR}]
  [∀ U : Y.C, HasSheafify (Y.J.over U) AddCommGrpCat.{wR}]
  [∀ U : Y.C, (Y.J.over U).WEqualsLocallyBijective AddCommGrpCat.{wR}]

attribute [local instance] RingedSite.sliceHasSheafify RingedSite.sliceWEqualsLocallyBijective

variable [HasDerivedCategory.{dR} (RingedSite.Modules.{uR, vR, wR} Y)]
  [hSliceDerived : ∀ U : Y.C,
    HasDerivedCategory.{dR} (RingedSite.Modules.{max uR vR, vR, wR} (Y.over U))]

attribute [local instance] Stacks.SheafOfModules.DerivedTensorProduct.sliceDerived

variable
  [∀ U : Y.C,
    (Stacks.SheafOfModules.Tensor.sheafTensor.{max uR vR, vR, wR, wR, wR} (Y.over U).O).Additive]
  [∀ (U : Y.C) M,
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{max uR vR, vR, wR, wR, wR}
      (Y.over U).O).obj M).Additive]
  [∀ (U : Y.C) (K L : CochainComplex (RingedSite.Modules.{max uR vR, vR, wR} (Y.over U)) ℤ),
    HomologicalComplex.HasMapBifunctor K L
      (Stacks.SheafOfModules.Tensor.sheafTensor (Y.over U).O) (ComplexShape.up ℤ)]

open Stacks.SheafOfModules.DerivedTensorProduct in
/-- **Locally finite Tor dimension, read at an object carrying a point of the site.** If `E`
locally has finite Tor dimension and the point `Φ` lifts to `U`, then some arrow `V ⟶ U` through
which the lift factors has `E|_V` of Tor amplitude in a concrete interval `[a, b]`: the fibre
functor at a point takes a covering sieve to a surjection, and finite Tor dimension is Tor
amplitude in some interval. -/
theorem exists_hasTorAmplitude_derivedRestriction_of_point
    (T : ∀ U : Y.C,
      Stacks.SheafOfModules.DerivedTensorProduct.{max uR vR, vR, wR, dR} (Y.over U))
    (E : RingedSite.DerivedModules.{uR, vR, wR, dR} Y)
    (hE : LocallyHasFiniteTorDimension T E)
    (Φ : Y.J.Point.{zR}) {U : Y.C} (x : Φ.fiber.obj U) :
    ∃ (V : Y.C) (f : V ⟶ U) (y : Φ.fiber.obj V) (a b : ℤ),
      Φ.fiber.map f y = x ∧
      HasTorAmplitude (T V) ((RingedSite.derivedRestriction.{uR, vR, wR, dR} Y V).obj E) a b := by
  obtain ⟨S, hS, htor⟩ := hE U
  obtain ⟨W, g, hg, z₀, hz₀⟩ := Φ.jointly_surjective _ hS x
  obtain ⟨Z, p, q, hq, hpq⟩ := hg
  obtain ⟨a, b, hab⟩ := htor q hq
  refine ⟨Z, q, Φ.fiber.map p z₀, a, b, ?_, hab⟩
  rw [← hz₀, ← hpq]
  simp

end LocalTorAmplitude

end AlgebraicGeometry

end
