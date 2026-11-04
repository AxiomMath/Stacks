module

public import StacksFrontier.AlgebraicGeometry.Duality.RightAdjointLemmas.ExactSupportKInjective
public import StacksFrontier.AlgebraicGeometry.Duality.RightAdjointLemmas.ExactSupportPushforwardInternalHom
public import StacksFrontier.AlgebraicGeometry.Duality.RightAdjointLemmas.ExactSupportSheafHomComplex
public import StacksFrontier.CategoryTheory.Localization.ExtendFromResolutions
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.FromTheStructureSheaf
public import StacksFrontier.Homology.Injectives.KInjective.FunctorialResolution
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedInternalHom
import StacksCore.Tactic.StacksAttribute

/-!
# Derived internal Hom out of a pushforward along a closed quotient morphism

Let `i : Z ⟶ X` be a closed quotient morphism of ringed spaces, so that pushforward
`i_* : Mod(𝒪_Z) ⥤ Mod(𝒪_X)` is left adjoint to sheaf Hom with exact support
`ℰom(𝒪_Z, -) : Mod(𝒪_X) ⥤ Mod(𝒪_Z)`.  Pushforward is exact and so induces `Ri_*` directly,
while the right adjoint acquires a total right derived functor `R ℰom(𝒪_Z, -)`.  For an object
`M` of `D(𝒪_Z)` the derived internal Hom out of `Ri_* M` is then computed on `Z`:

`R ℰom_X(Ri_* M, -) ≅ Ri_* R ℰom_Z(M, R ℰom(𝒪_Z, -))`,

which is [Stacks, Tag 0E2I]; taking `M = 𝒪_Z` and using that the derived internal Hom out of the
structure sheaf is the identity functor gives `Ri_* R ℰom(𝒪_Z, -) ≅ R ℰom_X(Ri_* 𝒪_Z, -)`, which
is [Stacks, Tag 0A77].

The proof evaluates both sides on the class of a K-injective cochain complex `I` of
`𝒪_X`-modules and a cochain complex `M` of `𝒪_Z`-modules.  A K-injective target computes the
derived internal Hom, so the left-hand side is the class of `SheafHom^•_X(i_* M, I)`.  On the
right, `ℰom(𝒪_Z, -)` applied degreewise preserves K-injectivity by the adjoint criterion of
[Stacks, Tag 08BJ], so `R ℰom(𝒪_Z, I)` is the class of `ℰom^•(𝒪_Z, I)`, the derived internal Hom
on `Z` out of `M` into it is the class of `SheafHom^•_Z(M, ℰom^•(𝒪_Z, I))`, and `Ri_*` of that is
the class of its pushforward.  The complex-level identification

`i_* SheafHom^•_Z(M, ℰom^•(𝒪_Z, I)) ≅ SheafHom^•_X(i_* M, I)`

therefore identifies the two sides, and naturality in `I` among K-injective complexes extends the
identification along the chosen functorial K-injective resolution to an isomorphism of functors
on all of `D(𝒪_X)`.  An arbitrary object of `D(𝒪_Z)` is the class of a cochain complex up to
isomorphism, and both sides are functorial in that object, so the isomorphism transports.

All names below live in the namespace `RingedSpaceModuleAdjunction`, the ones depending on a
closed quotient morphism in `RingedSpaceModuleAdjunction.ClosedQuotientMorphismOfRingedSpaces`.

## Main definitions

* `sheafHomComplexHomMap` is the map of internal Hom complexes on a ringed space induced by
  precomposition and postcomposition, as a morphism between the canonical internal Hom complexes
  of the space.
* `ClosedQuotientMorphismOfRingedSpaces.derivedSheafHomPushforward` and
  `ClosedQuotientMorphismOfRingedSpaces.pushforwardDerivedSheafHomExactSupport` are the two sides
  of [Stacks, Tag 0E2I], as functors `D(𝒪_X) ⥤ D(𝒪_X)`.
* `ClosedQuotientMorphismOfRingedSpaces.PushforwardSheafHomComplex` is the complex-level
  identification `i_* SheafHom^•_Z(M, ℰom^•(𝒪_Z, I)) ≅ SheafHom^•_X(i_* M, I)` of
  [Stacks, Tag 0E2I], bundled with its naturality in `I`, and
  `ClosedQuotientMorphismOfRingedSpaces.pushforwardSheafHomComplex` constructs it from the
  underived identification
  `ClosedQuotientMorphismOfRingedSpaces.pushforwardInternalHom` of [Stacks, Tag 0E2I].
* `ClosedQuotientMorphismOfRingedSpaces.derivedSheafHomPushforwardModelIso` and
  `ClosedQuotientMorphismOfRingedSpaces.derivedSheafHomPushforwardObjModelIso` are the resulting
  identifications of the two sides at the class of a K-injective cochain complex, for a cochain
  complex and for an arbitrary object of `D(𝒪_Z)` respectively.
* `ClosedQuotientMorphismOfRingedSpaces.derivedSheafHomPushforwardNatIso` is the isomorphism of
  [Stacks, Tag 0E2I] and
  `ClosedQuotientMorphismOfRingedSpaces.derivedSheafHomExactSupportPushforwardNatIso` the
  isomorphism of [Stacks, Tag 0A77].

## Main results

* `derivedSheafHomComparison_naturality`, `derivedSheafHomComparison_naturality_target` and
  `derivedSheafHomComparison_naturality_source`: the K-injective model of the derived internal
  Hom on a ringed space is natural, in both variables and in each one alone.
* `ClosedQuotientMorphismOfRingedSpaces.derivedSheafHomPushforwardModelIso_natural`: the
  identification at a K-injective representative is natural in that representative, which is
  what lets it be extended to the whole derived category.
* `ClosedQuotientMorphismOfRingedSpaces.pushforwardSheafHomComplex_natural_left` and
  `ClosedQuotientMorphismOfRingedSpaces.derivedSheafHomPushforwardModelIso_natural_source`: the
  complex-level identification and the identification at a K-injective representative are
  natural in the *source* complex as well.
* `ClosedQuotientMorphismOfRingedSpaces.derivedSheafHomPushforwardModelIso_natural_source_derived`:
  that source-naturality for an arbitrary morphism of the derived category between the classes
  of two cochain complexes, obtained by factoring the morphism through a K-injective resolution
  of its target.
* `ClosedQuotientMorphismOfRingedSpaces.derivedSheafHomPushforwardNatIso_app` and
  `ClosedQuotientMorphismOfRingedSpaces.derivedSheafHomExactSupportPushforwardNatIso_app` pin the
  two isomorphisms down by naming their components: the first is the identification on
  K-injective representatives, the second is the first at `𝒪_Z` composed with the identification
  of `R ℰom_Z(𝒪_Z, -)` with the identity functor.
* `ClosedQuotientMorphismOfRingedSpaces.derivedSheafHomPushforwardNatIso_app_cochain`: **at the
  class of a cochain complex the component is the identification on K-injective representatives
  of that very complex**, not only of the complex `CategoryTheory.Functor.objPreimage` chooses.
  This is what makes the isomorphism of [Stacks, Tag 0E2I] computable at a *named* source, such
  as the structure sheaf of the closed subspace in degree zero.
* `ClosedQuotientMorphismOfRingedSpaces.derivedSheafHomExactSupportPushforwardNatIso_app_isKInjective`:
  the component of the isomorphism of [Stacks, Tag 0A77] at a K-injective class, written with
  the identification on K-injective representatives of `RingedSite.structureSheafComplex` — no
  chosen representative anywhere in the formula.

## Implementation notes

**The underived input.** Everything below rests on the underived identification
`Hom_{𝒪_X}(i_*N, -) ≅ i_* Hom_{𝒪_Z}(N, ℰom(𝒪_Z, -))` together with its naturality in `N`
expressed as precomposition on internal Hom sheaves, which is
`ClosedQuotientMorphismOfRingedSpaces.pushforwardInternalHom`; the complex-level identification
`PushforwardSheafHomComplex` is constructed from it by `pushforwardSheafHomComplex`, and that
is the only input to the derived statements beyond the K-injective machinery.  The structure
`PushforwardInternalHom` is still what the complex-level constructions of
`StacksFrontier.AlgebraicGeometry.Duality.RightAdjointLemmas.ExactSupportSheafHomComplex` take as
a parameter, since nothing else about the underived identification is used there; here it is
always the canonical one.

The source displays the isomorphism of [Stacks, Tag 0E2I] "in `D(𝒪_Z)`", but both of its sides
are complexes of `𝒪_X`-modules — the inner derived internal Hom on `Z` is followed by a
pushforward — so the isomorphism recorded here is an isomorphism of functors with values in
`D(𝒪_X)`.

`DerivedCategory.Q` is essentially surjective but has no section, so passing from a cochain
complex of `𝒪_Z`-modules to an arbitrary object of `D(𝒪_Z)` uses the chosen preimage
`Functor.objPreimage` and the chosen isomorphism `Functor.objObjPreimageIso`.  Conjugating by the
latter is what `derivedSheafHomPushforwardRepresentative` and
`pushforwardDerivedSheafHomExactSupportRepresentative` do, and it is why the component formula
for an arbitrary object is stated in terms of `derivedSheafHomPushforwardObjModelIso`, which
carries the same conjugation.

That conjugation is removable when the object *is* the class of a named cochain complex, which
is what `derivedSheafHomPushforwardNatIso_app_cochain` says, and the input is the
source-naturality of the identification on K-injective representatives.  For a morphism of
complexes that is `derivedSheafHomPushforwardModelIso_natural_source`, six squares composed; for
a morphism of the derived category it is
`derivedSheafHomPushforwardModelIso_natural_source_derived`, which composes with a K-injective
resolution `ρ` of the target to make the morphism the class of a chain map
(`exists_Q_map_eq_of_isKInjective`) and then cancels the invertible contribution of `Qρ`.  The
chain is cut into several small declarations and its reassociations are written as terms: at
these types a `rw [← Category.assoc]` and a `show` across the folded and unfolded spellings of
the `Representative` isomorphisms each exhaust the heartbeat budget on their own.

The category of `𝒪_X`-modules carries two definitionally equal spellings: sheaf Hom with exact
support is stated over `structureSheafRing`, which reduces to `X.presheaf ⋙ forget₂ _ _`, and
the internal Hom complex over `Stacks.SheafOfModules.StructureSheafModules`, which unfolds to
`(sheafCompose _ (forget₂ _ _)).obj X.sheaf`; the ringed-site constructions the latter are read
off from are stated over `Stacks.SheafOfModules.Tensor.ringSheaf X.O`, which unfolds to
`⟨X.sheaf.obj ⋙ forget₂ _ _, _⟩`.  The three meet only once
`Stacks.SheafOfModules.Tensor.ringSheaf`, `sheafCompose` and
`AlgebraicGeometry.SheafedSpace.sheaf` are unfolded, so all three are made locally
`instance_reducible`, and the preservation of K-injectivity by sheaf Hom with exact support is
restated once in the second spelling so that instance search finds it there.  For the same reason
the maps of internal Hom complexes are bundled as `sheafHomComplexHomMap`, whose ascribed source
and target are the space-level internal Hom complexes: the ringed-site construction they unfold
to is not exposed, so a goal mixing the two spellings is not one `rw` can act on.

## References

* [Stacks Project, Tag 0A77](https://stacks.math.columbia.edu/tag/0A77)
* [Stacks Project, Tag 0E2I](https://stacks.math.columbia.edu/tag/0E2I)
* [Stacks Project, Tag 0A76](https://stacks.math.columbia.edu/tag/0A76)
* [Stacks Project, Tag 08DI](https://stacks.math.columbia.edu/tag/08DI)
* [Stacks Project, Tag 08BJ](https://stacks.math.columbia.edu/tag/08BJ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

attribute [local instance] HasDerivedCategory.standard

attribute [local instance_reducible] CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf Stacks.SheafOfModules.Tensor.ringSheaf

universe u

namespace RingedSpaceModuleAdjunction

/-- One step of the verification that a composite of commuting squares commutes: if the first
square commutes and the rest of the composite does, then so does the whole. -/
private theorem comp_naturality_step {C : Type*} [Category C] {a a' b b' z : C}
    {f : a ⟶ a'} {u : a ⟶ b} {u' : a' ⟶ b'} {g : b ⟶ b'} {t' : b' ⟶ z} {t : b ⟶ z}
    (h₁ : f ≫ u' = u ≫ g) (h₂ : g ≫ t' = t) : f ≫ u' ≫ t' = u ≫ t := by
  rw [← Category.assoc, h₁, Category.assoc, h₂]

/-- A commuting square of forward maps of two isomorphisms gives the commuting square of their
inverses. -/
private theorem inv_comp_eq_of_comp_hom_eq {C : Type*} [Category C] {X Y X' Y' : C}
    {e : X ≅ Y} {e' : X' ≅ Y'} {f : X ⟶ X'} {g : Y ⟶ Y'} (h : f ≫ e'.hom = e.hom ≫ g) :
    g ≫ e'.inv = e.inv ≫ f := by
  rw [Iso.comp_inv_eq, Category.assoc, h, Iso.inv_hom_id_assoc]

/-- Every morphism of the derived category into the class of a K-injective cochain complex is
the class of a morphism of complexes: the Hom groups out of the homotopy category into a
K-injective complex are already the derived ones, and the quotient onto the homotopy category is
full. Stated for an arbitrary abelian category with a derived category, which is how the
`structureSheafRing` spelling of the modules on the closed subspace reaches it; the ringed-site form
`AlgebraicGeometry.RingedSite.exists_Q_map_eq_of_isKInjective` does not unify with that spelling
without unfolding `structureSheafRing`. -/
private theorem exists_Q_map_eq_of_isKInjective {C : Type*} [Category* C] [Abelian C]
    [HasDerivedCategory C] {A I : CochainComplex C ℤ} [I.IsKInjective]
    (φ : DerivedCategory.Q.obj A ⟶ DerivedCategory.Q.obj I) :
    ∃ h : A ⟶ I, DerivedCategory.Q.map h = φ := by
  obtain ⟨g, hg⟩ := (CochainComplex.IsKInjective.Qh_map_bijective
      ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj A) I).surjective
    ((DerivedCategory.quotientCompQhIso C).hom.app A ≫ φ ≫
      (DerivedCategory.quotientCompQhIso C).inv.app I)
  obtain ⟨g, rfl⟩ := (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map_surjective g
  refine ⟨g, ?_⟩
  apply (cancel_epi ((DerivedCategory.quotientCompQhIso C).hom.app A)).mp
  rw [← DerivedCategory.quotientCompQhIso_hom_naturality, hg]
  simp

/-- The map of internal Hom complexes on a ringed space induced by precomposition with
`g : A' ⟶ A` and postcomposition with `f : I ⟶ J`, as a morphism between the canonical internal
Hom complexes of the space. -/
def sheafHomComplexHomMap (W : AlgebraicGeometry.RingedSpace.{u, u})
    {A A' I J : CochainComplex (SheafOfModules.{u} (structureSheafRing W)) ℤ}
    (g : A' ⟶ A) (f : I ⟶ J) :
    (Stacks.SheafOfModules.sheafHomComplex W.sheaf A I).obj ⟶
      (Stacks.SheafOfModules.sheafHomComplex W.sheaf A' J).obj :=
  RingedSite.homMap (Stacks.SheafOfModules.ringedSite W.sheaf) g f

/-- **The K-injective model of the derived internal Hom on a ringed space is natural.** It
intertwines the maps induced on derived internal Hom with the maps of internal Hom complexes, in
the source and in the K-injective target at once. -/
theorem derivedSheafHomComparison_naturality (W : AlgebraicGeometry.RingedSpace.{u, u})
    {A A' I J : CochainComplex (SheafOfModules.{u} (structureSheafRing W)) ℤ}
    [I.IsKInjective] [J.IsKInjective] (g : A' ⟶ A) (f : I ⟶ J) :
    ((Stacks.SheafOfModules.derivedSheafHom W.sheaf).map
            (DerivedCategory.Q.map g).op).app (DerivedCategory.Q.obj I) ≫
        ((Stacks.SheafOfModules.derivedSheafHom W.sheaf).obj
            (op (DerivedCategory.Q.obj A'))).map (DerivedCategory.Q.map f) ≫
          (Stacks.SheafOfModules.derivedSheafHomComparison W.sheaf A' J).hom =
      (Stacks.SheafOfModules.derivedSheafHomComparison W.sheaf A I).hom ≫
        DerivedCategory.Q.map (sheafHomComplexHomMap W g f) :=
  RingedSite.derivedSheafHomComparison_naturality
    (Stacks.SheafOfModules.ringedSite W.sheaf) g f

/-- The K-injective model of the derived internal Hom on a ringed space is natural in its
target: a morphism `f : I ⟶ J` of K-injective cochain complexes acts on `RSheafHom(A, -)` by
postcomposition with `f` on internal Hom complexes. -/
theorem derivedSheafHomComparison_naturality_target (W : AlgebraicGeometry.RingedSpace.{u, u})
    (A : CochainComplex (SheafOfModules.{u} (structureSheafRing W)) ℤ)
    {I J : CochainComplex (SheafOfModules.{u} (structureSheafRing W)) ℤ}
    [I.IsKInjective] [J.IsKInjective] (f : I ⟶ J) :
    ((Stacks.SheafOfModules.derivedSheafHom W.sheaf).obj
          (op (DerivedCategory.Q.obj A))).map (DerivedCategory.Q.map f) ≫
        (Stacks.SheafOfModules.derivedSheafHomComparison W.sheaf A J).hom =
      (Stacks.SheafOfModules.derivedSheafHomComparison W.sheaf A I).hom ≫
        DerivedCategory.Q.map (sheafHomComplexHomMap W (𝟙 A) f) := by
  simpa only [CategoryTheory.Functor.map_id, op_id, NatTrans.id_app, Category.id_comp]
    using derivedSheafHomComparison_naturality W (𝟙 A) f

/-- The K-injective model of the derived internal Hom on a ringed space is natural in its
source: a morphism `g : A' ⟶ A` of cochain complexes acts on `RSheafHom(-, I)` by
precomposition with `g` on internal Hom complexes. -/
theorem derivedSheafHomComparison_naturality_source (W : AlgebraicGeometry.RingedSpace.{u, u})
    {A A' : CochainComplex (SheafOfModules.{u} (structureSheafRing W)) ℤ} (g : A' ⟶ A)
    (I : CochainComplex (SheafOfModules.{u} (structureSheafRing W)) ℤ) [I.IsKInjective] :
    ((Stacks.SheafOfModules.derivedSheafHom W.sheaf).map
            (DerivedCategory.Q.map g).op).app (DerivedCategory.Q.obj I) ≫
        (Stacks.SheafOfModules.derivedSheafHomComparison W.sheaf A' I).hom =
      (Stacks.SheafOfModules.derivedSheafHomComparison W.sheaf A I).hom ≫
        DerivedCategory.Q.map (sheafHomComplexHomMap W g (𝟙 I)) := by
  simpa only [CategoryTheory.Functor.map_id, Category.id_comp]
    using derivedSheafHomComparison_naturality W g (𝟙 I)

namespace ClosedQuotientMorphismOfRingedSpaces

variable (S : ClosedQuotientMorphismOfRingedSpaces.{u})

/-- Sheaf Hom with exact support carries a K-injective cochain complex of `𝒪_X`-modules to a
K-injective cochain complex of `𝒪_Z`-modules, read in the vocabulary of the internal Hom
complex: the category of `𝒪_Z`-modules appears there as
`Stacks.SheafOfModules.StructureSheafModules S.Z.sheaf`. -/
instance isKInjective_sheafHomExactSupport_structureSheafModules
    (I : CochainComplex (SheafOfModules.{u} (structureSheafRing S.X)) ℤ) [I.IsKInjective] :
    CochainComplex.IsKInjective
      (C := Stacks.SheafOfModules.StructureSheafModules S.Z.sheaf)
      ((S.sheafHomExactSupport.mapHomologicalComplex (ComplexShape.up ℤ)).obj I) :=
  S.isKInjective_sheafHomExactSupport I

/-- The functor `K ↦ RSheafHom_X(Ri_* M, K)` on `D(𝒪_X)`: the derived internal Hom out of the
derived pushforward of an object `M` of `D(𝒪_Z)`. -/
abbrev derivedSheafHomPushforward
    (M : DerivedCategory (SheafOfModules.{u} (structureSheafRing S.Z))) :
    DerivedCategory (SheafOfModules.{u} (structureSheafRing S.X)) ⥤
      DerivedCategory (SheafOfModules.{u} (structureSheafRing S.X)) :=
  (Stacks.SheafOfModules.derivedSheafHom S.X.sheaf).obj
    (op ((modulePushforward S.i).mapDerivedCategory.obj M))

/-- The functor `K ↦ Ri_* RSheafHom_Z(M, R ℰom(𝒪_Z, K))` on `D(𝒪_X)`: derived sheaf Hom with
exact support, then the derived internal Hom out of `M` on `Z`, then derived pushforward. -/
abbrev pushforwardDerivedSheafHomExactSupport
    (M : DerivedCategory (SheafOfModules.{u} (structureSheafRing S.Z))) :
    DerivedCategory (SheafOfModules.{u} (structureSheafRing S.X)) ⥤
      DerivedCategory (SheafOfModules.{u} (structureSheafRing S.X)) :=
  S.derivedSheafHomExactSupport ⋙
    (Stacks.SheafOfModules.derivedSheafHom S.Z.sheaf).obj (op M) ⋙
      (modulePushforward S.i).mapDerivedCategory

/-- The comparison of `RSheafHom_X(Ri_* M, -)` with its value at the chosen cochain complex
representing `M`, induced by the chosen isomorphism of `M` with the class of that complex. -/
def derivedSheafHomPushforwardRepresentative
    (M : DerivedCategory (SheafOfModules.{u} (structureSheafRing S.Z))) :
    S.derivedSheafHomPushforward M ≅
      S.derivedSheafHomPushforward (DerivedCategory.Q.obj (DerivedCategory.Q.objPreimage M)) :=
  (Stacks.SheafOfModules.derivedSheafHom S.X.sheaf).mapIso
    (Iso.op ((modulePushforward S.i).mapDerivedCategory.mapIso
      (DerivedCategory.Q.objObjPreimageIso M)))

/-- The comparison of `Ri_* RSheafHom_Z(M, R ℰom(𝒪_Z, -))` with its value at the chosen cochain
complex representing `M`, induced by the chosen isomorphism of `M` with the class of that
complex. -/
def pushforwardDerivedSheafHomExactSupportRepresentative
    (M : DerivedCategory (SheafOfModules.{u} (structureSheafRing S.Z))) :
    S.pushforwardDerivedSheafHomExactSupport M ≅
      S.pushforwardDerivedSheafHomExactSupport
        (DerivedCategory.Q.obj (DerivedCategory.Q.objPreimage M)) :=
  Functor.isoWhiskerLeft S.derivedSheafHomExactSupport
    (Functor.isoWhiskerRight
      ((Stacks.SheafOfModules.derivedSheafHom S.Z.sheaf).mapIso
        (Iso.op (DerivedCategory.Q.objObjPreimageIso M)))
      (modulePushforward S.i).mapDerivedCategory)

/-- The complex-level form of [Stacks, Tag 0E2I]: an isomorphism of complexes of `𝒪_X`-modules
`i_* SheafHom^•_Z(M, ℰom^•(𝒪_Z, I)) ≅ SheafHom^•_X(i_* M, I)`, natural in the target complex
`I`. -/
structure PushforwardSheafHomComplex where
  /-- The isomorphism `i_* SheafHom^•_Z(M, ℰom^•(𝒪_Z, I)) ≅ SheafHom^•_X(i_* M, I)`. -/
  iso : ∀ (M : CochainComplex (SheafOfModules.{u} (structureSheafRing S.Z)) ℤ)
      (I : CochainComplex (SheafOfModules.{u} (structureSheafRing S.X)) ℤ),
    ((modulePushforward S.i).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (Stacks.SheafOfModules.sheafHomComplex S.Z.sheaf M
          ((S.sheafHomExactSupport.mapHomologicalComplex (ComplexShape.up ℤ)).obj I)).obj ≅
      (Stacks.SheafOfModules.sheafHomComplex S.X.sheaf
        (((modulePushforward S.i).mapHomologicalComplex (ComplexShape.up ℤ)).obj M) I).obj
  /-- The isomorphism is natural in the target complex: postcomposition with `f : I ⟶ J` on `Z`,
  after sheaf Hom with exact support and then pushed forward, is postcomposition with `f` on
  `X`. -/
  natural_right : ∀ (M : CochainComplex (SheafOfModules.{u} (structureSheafRing S.Z)) ℤ)
      {I J : CochainComplex (SheafOfModules.{u} (structureSheafRing S.X)) ℤ} (f : I ⟶ J),
    ((modulePushforward S.i).mapHomologicalComplex (ComplexShape.up ℤ)).map
          (sheafHomComplexHomMap S.Z (𝟙 M)
            ((S.sheafHomExactSupport.mapHomologicalComplex (ComplexShape.up ℤ)).map f)) ≫
        (iso M J).hom =
      (iso M I).hom ≫
        sheafHomComplexHomMap S.X
          (𝟙 (((modulePushforward S.i).mapHomologicalComplex (ComplexShape.up ℤ)).obj M)) f

/-- **The complex-level form of [Stacks, Tag 0E2I] follows from the underived form.** The
isomorphism is the comparison of the realization of `SheafHom^•_X(i_* M, I)` by
`i_* SheafHom^•_Z(M, ℰom^•(𝒪_Z, I))`, which the underived identification provides, with the
canonical internal Hom complex; its naturality in the target complex is the naturality of that
comparison. -/
def pushforwardSheafHomComplex : S.PushforwardSheafHomComplex where
  iso M I :=
    pushforwardSheafHomComplexIso S.pushforwardInternalHom
      (Stacks.SheafOfModules.sheafHomComplexComparison _) M I
  natural_right := fun M {_ _} f =>
    pushforwardSheafHomComplexIso_natural_right_homMap S.pushforwardInternalHom _ M f

/-- **The complex-level form of [Stacks, Tag 0E2I] is natural in the source complex too.** The
structure `…PushforwardSheafHomComplex` records only the naturality in the target, which is what
extends the derived identification along a K-injective resolution of the target; this is the
other naturality, needed to move the identification between two cochain complexes representing
the same object of `D(𝒪_Z)`. It holds of the canonical construction
`…pushforwardSheafHomComplex`, by
`…pushforwardSheafHomComplexIso_natural_left_homMap`. -/
theorem pushforwardSheafHomComplex_natural_left
    {M M' : CochainComplex (SheafOfModules.{u} (structureSheafRing S.Z)) ℤ} (g : M' ⟶ M)
    (I : CochainComplex (SheafOfModules.{u} (structureSheafRing S.X)) ℤ) :
    ((modulePushforward S.i).mapHomologicalComplex (ComplexShape.up ℤ)).map
          (sheafHomComplexHomMap S.Z g
            (𝟙 ((S.sheafHomExactSupport.mapHomologicalComplex (ComplexShape.up ℤ)).obj I))) ≫
        ((pushforwardSheafHomComplex S).iso M' I).hom =
      ((pushforwardSheafHomComplex S).iso M I).hom ≫
        sheafHomComplexHomMap S.X
          (((modulePushforward S.i).mapHomologicalComplex (ComplexShape.up ℤ)).map g) (𝟙 I) :=
  pushforwardSheafHomComplexIso_natural_left_homMap S.pushforwardInternalHom _ g I

/-- **Stacks 0E2I on K-injective representatives.** For a cochain complex `M` of `𝒪_Z`-modules
and a K-injective cochain complex `I` of `𝒪_X`-modules, both `RSheafHom_X(Ri_* M, I)` and
`Ri_* RSheafHom_Z(M, R ℰom(𝒪_Z, I))` are the class of a complex, and the complex-level
identification derived from `h` identifies the two. -/
def derivedSheafHomPushforwardModelIso
    (M : CochainComplex (SheafOfModules.{u} (structureSheafRing S.Z)) ℤ)
    (I : CochainComplex (SheafOfModules.{u} (structureSheafRing S.X)) ℤ) [I.IsKInjective] :
    (S.derivedSheafHomPushforward (DerivedCategory.Q.obj M)).obj (DerivedCategory.Q.obj I) ≅
      (S.pushforwardDerivedSheafHomExactSupport (DerivedCategory.Q.obj M)).obj
        (DerivedCategory.Q.obj I) :=
  ((Stacks.SheafOfModules.derivedSheafHom S.X.sheaf).mapIso
        ((modulePushforward S.i).mapDerivedCategoryFactors.app M).symm.op).app
      (DerivedCategory.Q.obj I) ≪≫
    Stacks.SheafOfModules.derivedSheafHomComparison S.X.sheaf
        (((modulePushforward S.i).mapHomologicalComplex (ComplexShape.up ℤ)).obj M) I ≪≫
      (DerivedCategory.Q.mapIso ((pushforwardSheafHomComplex S).iso M I)).symm ≪≫
        ((modulePushforward S.i).mapDerivedCategoryFactors.app
            (Stacks.SheafOfModules.sheafHomComplex S.Z.sheaf M
              ((S.sheafHomExactSupport.mapHomologicalComplex
                (ComplexShape.up ℤ)).obj I)).obj).symm ≪≫
          (modulePushforward S.i).mapDerivedCategory.mapIso
              (Stacks.SheafOfModules.derivedSheafHomComparison S.Z.sheaf M
                ((S.sheafHomExactSupport.mapHomologicalComplex
                  (ComplexShape.up ℤ)).obj I)).symm ≪≫
            (modulePushforward S.i).mapDerivedCategory.mapIso
              (((Stacks.SheafOfModules.derivedSheafHom S.Z.sheaf).obj
                  (op (DerivedCategory.Q.obj M))).mapIso
                (S.derivedSheafHomExactSupportKInjectiveIso I).symm)

/-- Naturality of the identification on K-injective representatives in the target complex: the
six identifications it is composed of are each natural in that complex. -/
theorem derivedSheafHomPushforwardModelIso_natural
    (M : CochainComplex (SheafOfModules.{u} (structureSheafRing S.Z)) ℤ)
    {I J : CochainComplex (SheafOfModules.{u} (structureSheafRing S.X)) ℤ}
    [I.IsKInjective] [J.IsKInjective] (f : I ⟶ J) :
    (S.derivedSheafHomPushforward (DerivedCategory.Q.obj M)).map (DerivedCategory.Q.map f) ≫
        (derivedSheafHomPushforwardModelIso S M J).hom =
      (derivedSheafHomPushforwardModelIso S M I).hom ≫
        (S.pushforwardDerivedSheafHomExactSupport (DerivedCategory.Q.obj M)).map
          (DerivedCategory.Q.map f) := by
  have h1 := ((Stacks.SheafOfModules.derivedSheafHom S.X.sheaf).map
    ((modulePushforward S.i).mapDerivedCategoryFactors.app M).symm.op.hom).naturality
      (DerivedCategory.Q.map f)
  have h2 := derivedSheafHomComparison_naturality_target S.X
    (((modulePushforward S.i).mapHomologicalComplex (ComplexShape.up ℤ)).obj M) f
  have h3c := inv_comp_eq_of_comp_hom_eq ((pushforwardSheafHomComplex S).natural_right M f)
  have h4 := (modulePushforward S.i).mapDerivedCategoryFactors.inv.naturality
    (sheafHomComplexHomMap S.Z (𝟙 M)
      ((S.sheafHomExactSupport.mapHomologicalComplex (ComplexShape.up ℤ)).map f))
  have h5i := inv_comp_eq_of_comp_hom_eq (derivedSheafHomComparison_naturality_target S.Z M
    ((S.sheafHomExactSupport.mapHomologicalComplex (ComplexShape.up ℤ)).map f))
  have h6i := inv_comp_eq_of_comp_hom_eq (S.derivedSheafHomExactSupportKInjectiveIso_natural f)
  have h3 := congrArg (fun φ => DerivedCategory.Q.map φ) h3c
  have h5 := congrArg (fun φ => (modulePushforward S.i).mapDerivedCategory.map φ) h5i
  have h6 := congrArg (fun φ => (modulePushforward S.i).mapDerivedCategory.map
    (((Stacks.SheafOfModules.derivedSheafHom S.Z.sheaf).obj
      (op (DerivedCategory.Q.obj M))).map φ)) h6i
  simp only [Functor.map_comp] at h3 h5 h6
  dsimp only [derivedSheafHomPushforwardModelIso, derivedSheafHomPushforward,
    pushforwardDerivedSheafHomExactSupport, Iso.trans_hom, Iso.symm_hom, Iso.app_hom,
    Iso.app_inv, Functor.mapIso_hom, Functor.mapIso_inv, Iso.op_hom, Functor.comp_map]
  simp only [Category.assoc]
  exact comp_naturality_step h1 (comp_naturality_step h2 (comp_naturality_step h3
    (comp_naturality_step h4 (comp_naturality_step h5 h6))))

/-- **Naturality of the identification on K-injective representatives in the source complex.**
The six identifications it is composed of are each natural in that complex: the first is the
defining factorisation of derived pushforward, the second and fifth the K-injective model of the
derived internal Hom on `X` and on `Z`, the third the complex-level [Stacks, Tag 0E2I]
(`…pushforwardSheafHomComplex_natural_left`), the fourth again the factorisation of derived
pushforward, and the sixth the naturality of the derived internal Hom bifunctor in its two
variables.

The naturality in the *target* complex is what extends the identification along a K-injective
resolution; this one is what lets the identification be read at *any* cochain complex
representing a given object of `D(𝒪_Z)`, the construction of
`…derivedSheafHomPushforwardNatIso` using the chosen representative. -/
theorem derivedSheafHomPushforwardModelIso_natural_source
    {M M' : CochainComplex (SheafOfModules.{u} (structureSheafRing S.Z)) ℤ} (g : M' ⟶ M)
    (I : CochainComplex (SheafOfModules.{u} (structureSheafRing S.X)) ℤ) [I.IsKInjective] :
    ((Stacks.SheafOfModules.derivedSheafHom S.X.sheaf).map
            ((modulePushforward S.i).mapDerivedCategory.map
              (DerivedCategory.Q.map g)).op).app (DerivedCategory.Q.obj I) ≫
        (derivedSheafHomPushforwardModelIso S M' I).hom =
      (derivedSheafHomPushforwardModelIso S M I).hom ≫
        (modulePushforward S.i).mapDerivedCategory.map
          (((Stacks.SheafOfModules.derivedSheafHom S.Z.sheaf).map
              (DerivedCategory.Q.map g).op).app
            (S.derivedSheafHomExactSupport.obj (DerivedCategory.Q.obj I))) := by
  have hop : ((modulePushforward S.i).mapDerivedCategory.map (DerivedCategory.Q.map g)).op ≫
        ((modulePushforward S.i).mapDerivedCategoryFactors.inv.app M').op =
      ((modulePushforward S.i).mapDerivedCategoryFactors.inv.app M).op ≫
        (DerivedCategory.Q.map
          (((modulePushforward S.i).mapHomologicalComplex (ComplexShape.up ℤ)).map g)).op :=
    congrArg Quiver.Hom.op
      ((modulePushforward S.i).mapDerivedCategoryFactors.inv.naturality g).symm
  have h1 := congrArg
    (fun φ => ((Stacks.SheafOfModules.derivedSheafHom S.X.sheaf).map φ).app
      (DerivedCategory.Q.obj I)) hop
  simp only [CategoryTheory.Functor.map_comp, NatTrans.comp_app] at h1
  have h2 := derivedSheafHomComparison_naturality_source S.X
    (((modulePushforward S.i).mapHomologicalComplex (ComplexShape.up ℤ)).map g) I
  have h3c := inv_comp_eq_of_comp_hom_eq (pushforwardSheafHomComplex_natural_left S g I)
  have h4 := (modulePushforward S.i).mapDerivedCategoryFactors.inv.naturality
    (sheafHomComplexHomMap S.Z g
      (𝟙 ((S.sheafHomExactSupport.mapHomologicalComplex (ComplexShape.up ℤ)).obj I)))
  have h5i := inv_comp_eq_of_comp_hom_eq (derivedSheafHomComparison_naturality_source S.Z g
    ((S.sheafHomExactSupport.mapHomologicalComplex (ComplexShape.up ℤ)).obj I))
  have h6c := (((Stacks.SheafOfModules.derivedSheafHom S.Z.sheaf).map
    (DerivedCategory.Q.map g).op).naturality
      (S.derivedSheafHomExactSupportKInjectiveIso I).inv).symm
  have h3 := congrArg (fun φ => DerivedCategory.Q.map φ) h3c
  have h5 := congrArg (fun φ => (modulePushforward S.i).mapDerivedCategory.map φ) h5i
  have h6 := congrArg (fun φ => (modulePushforward S.i).mapDerivedCategory.map φ) h6c
  simp only [CategoryTheory.Functor.map_comp] at h3 h5 h6
  dsimp only [derivedSheafHomPushforwardModelIso, derivedSheafHomPushforward,
    pushforwardDerivedSheafHomExactSupport, Iso.trans_hom, Iso.symm_hom, Iso.app_hom,
    Iso.app_inv, Functor.mapIso_hom, Functor.mapIso_inv, Iso.op_hom, Functor.comp_map]
  simp only [Category.assoc]
  exact comp_naturality_step h1 (comp_naturality_step h2 (comp_naturality_step h3
    (comp_naturality_step h4 (comp_naturality_step h5 h6))))

/-- The identifications on K-injective representatives assemble into an isomorphism of functors
on the whole derived category, whose components at K-injective complexes are the given ones. -/
theorem exists_derivedSheafHomPushforwardCochainNatIso
    (M : CochainComplex (SheafOfModules.{u} (structureSheafRing S.Z)) ℤ) :
    ∃ e : S.derivedSheafHomPushforward (DerivedCategory.Q.obj M) ≅
        S.pushforwardDerivedSheafHomExactSupport (DerivedCategory.Q.obj M),
      ∀ (I : CochainComplex (SheafOfModules.{u} (structureSheafRing S.X)) ℤ) (hI : I.IsKInjective),
        e.hom.app (DerivedCategory.Q.obj I) =
          (@derivedSheafHomPushforwardModelIso S M I hI).hom := by
  have hiso (c : CochainComplex (SheafOfModules.{u} (structureSheafRing S.X)) ℤ) :
      IsIso (DerivedCategory.Q.map
        ((Stacks.Injectives.kInjectiveResolutionInclusion
          (SheafOfModules.{u} (structureSheafRing S.X))).app c)) := by
    rw [DerivedCategory.isIso_Q_map_iff_quasiIso]
    infer_instance
  exact exists_natIso_of_isoOnResolutions DerivedCategory.Q
    (HomologicalComplex.quasiIso (SheafOfModules.{u} (structureSheafRing S.X)) (ComplexShape.up ℤ))
    (Stacks.Injectives.kInjectiveResolutionFunctor (SheafOfModules.{u} (structureSheafRing S.X)))
    (Stacks.Injectives.kInjectiveResolutionInclusion (SheafOfModules.{u} (structureSheafRing S.X)))
    (fun I => I.IsKInjective)
    (fun c => Stacks.Injectives.kInjectiveResolutionFunctor_obj_isKInjective
      (SheafOfModules.{u} (structureSheafRing S.X)) c)
    _ _ (fun c hc => @derivedSheafHomPushforwardModelIso S M c hc)
    (fun hc hc' g => @derivedSheafHomPushforwardModelIso_natural S M _ _ hc hc' g)

/-- **Stacks 0E2I for a cochain complex on the closed subspace.** For a cochain complex `M` of
`𝒪_Z`-modules, the derived internal Hom out of `Ri_* M` on `X` is derived sheaf Hom with exact
support followed by the derived internal Hom out of `M` on `Z` followed by derived
pushforward. -/
def derivedSheafHomPushforwardCochainNatIso
    (M : CochainComplex (SheafOfModules.{u} (structureSheafRing S.Z)) ℤ) :
    S.derivedSheafHomPushforward (DerivedCategory.Q.obj M) ≅
      S.pushforwardDerivedSheafHomExactSupport (DerivedCategory.Q.obj M) :=
  (exists_derivedSheafHomPushforwardCochainNatIso S M).choose

/-- On the class of a K-injective cochain complex, the isomorphism for a cochain complex `M` is
the identification on K-injective representatives. This is what makes it canonical. -/
theorem derivedSheafHomPushforwardCochainNatIso_app
    (M : CochainComplex (SheafOfModules.{u} (structureSheafRing S.Z)) ℤ)
    (I : CochainComplex (SheafOfModules.{u} (structureSheafRing S.X)) ℤ) [I.IsKInjective] :
    (derivedSheafHomPushforwardCochainNatIso S M).hom.app (DerivedCategory.Q.obj I) =
      (derivedSheafHomPushforwardModelIso S M I).hom :=
  (exists_derivedSheafHomPushforwardCochainNatIso S M).choose_spec I inferInstance

/-- The identification on K-injective representatives for an arbitrary object `M` of `D(𝒪_Z)`:
the one for the chosen cochain complex representing `M`, conjugated by the chosen isomorphism of
`M` with the class of that complex. -/
def derivedSheafHomPushforwardObjModelIso
    (M : DerivedCategory (SheafOfModules.{u} (structureSheafRing S.Z)))
    (I : CochainComplex (SheafOfModules.{u} (structureSheafRing S.X)) ℤ) [I.IsKInjective] :
    (S.derivedSheafHomPushforward M).obj (DerivedCategory.Q.obj I) ≅
      (S.pushforwardDerivedSheafHomExactSupport M).obj (DerivedCategory.Q.obj I) :=
  (S.derivedSheafHomPushforwardRepresentative M).app (DerivedCategory.Q.obj I) ≪≫
    derivedSheafHomPushforwardModelIso S (DerivedCategory.Q.objPreimage M) I ≪≫
      ((S.pushforwardDerivedSheafHomExactSupportRepresentative M).app
        (DerivedCategory.Q.obj I)).symm

/-- **Stacks Project, Tag 0E2I.** For every object `M` of `D(𝒪_Z)`, the derived internal Hom out
of the derived pushforward `Ri_* M` is derived sheaf Hom with exact support, followed by the
derived internal Hom out of `M` on `Z`, followed by derived pushforward:
`R ℰom_X(Ri_* M, -) ≅ Ri_* R ℰom_Z(M, R ℰom(𝒪_Z, -))`. -/
@[stacks 0E2I "the derived isomorphism, unconditionally"]
def derivedSheafHomPushforwardNatIso
    (M : DerivedCategory (SheafOfModules.{u} (structureSheafRing S.Z))) :
    (Stacks.SheafOfModules.derivedSheafHom S.X.sheaf).obj
        (op ((modulePushforward S.i).mapDerivedCategory.obj M)) ≅
      S.derivedSheafHomExactSupport ⋙
        (Stacks.SheafOfModules.derivedSheafHom S.Z.sheaf).obj (op M) ⋙
          (modulePushforward S.i).mapDerivedCategory :=
  S.derivedSheafHomPushforwardRepresentative M ≪≫
    derivedSheafHomPushforwardCochainNatIso S (DerivedCategory.Q.objPreimage M) ≪≫
      (S.pushforwardDerivedSheafHomExactSupportRepresentative M).symm

/-- The source-naturality of the identification on K-injective representatives for an arbitrary
morphism of the derived category, precomposed with a resolution of its target by a K-injective
complex.  A derived morphism `α : Q(A) ⟶ Q(B)` need not be the class of a morphism of complexes,
but it becomes one after composing with `ρ : B ⟶ J`: then `α ≫ Qρ = Qa` for a morphism of
complexes `a : A ⟶ J` (`…exists_Q_map_eq_of_isKInjective`), and the naturality at `a` and at `ρ`
give this. -/
private theorem derivedSheafHomPushforwardModelIso_natural_source_comp_resolution
    {A B J : CochainComplex (SheafOfModules.{u} (structureSheafRing S.Z)) ℤ} [J.IsKInjective]
    (ρ : B ⟶ J) (α : DerivedCategory.Q.obj A ⟶ DerivedCategory.Q.obj B)
    (I : CochainComplex (SheafOfModules.{u} (structureSheafRing S.X)) ℤ) [I.IsKInjective] :
    ((Stacks.SheafOfModules.derivedSheafHom S.X.sheaf).map
            ((modulePushforward S.i).mapDerivedCategory.map
              (DerivedCategory.Q.map ρ)).op).app (DerivedCategory.Q.obj I) ≫
        (((Stacks.SheafOfModules.derivedSheafHom S.X.sheaf).map
                ((modulePushforward S.i).mapDerivedCategory.map α).op).app
              (DerivedCategory.Q.obj I) ≫
            (derivedSheafHomPushforwardModelIso S A I).hom) =
      ((Stacks.SheafOfModules.derivedSheafHom S.X.sheaf).map
            ((modulePushforward S.i).mapDerivedCategory.map
              (DerivedCategory.Q.map ρ)).op).app (DerivedCategory.Q.obj I) ≫
        ((derivedSheafHomPushforwardModelIso S B I).hom ≫
          (modulePushforward S.i).mapDerivedCategory.map
            (((Stacks.SheafOfModules.derivedSheafHom S.Z.sheaf).map α.op).app
              (S.derivedSheafHomExactSupport.obj (DerivedCategory.Q.obj I)))) := by
  refine Exists.elim
    (exists_Q_map_eq_of_isKInjective (A := A) (I := J) (α ≫ DerivedCategory.Q.map ρ)) fun a ha => ?_
  have hA := derivedSheafHomPushforwardModelIso_natural_source S a I
  rw [ha] at hA
  simp only [CategoryTheory.Functor.map_comp, op_comp, NatTrans.comp_app,
    Category.assoc] at hA
  have hB := derivedSheafHomPushforwardModelIso_natural_source S ρ I
  exact hA.trans ((Category.assoc _ _ _).symm.trans
    ((congrArg (fun t : _ ⟶ _ => t ≫ (modulePushforward S.i).mapDerivedCategory.map
          (((Stacks.SheafOfModules.derivedSheafHom S.Z.sheaf).map α.op).app
            (S.derivedSheafHomExactSupport.obj (DerivedCategory.Q.obj I))))
        hB.symm).trans
      (Category.assoc _ _ _)))

/-- The source-naturality for an arbitrary derived morphism, by cancelling the invertible
contribution of the resolution. -/
private theorem derivedSheafHomPushforwardModelIso_natural_source_of_resolution
    {A B J : CochainComplex (SheafOfModules.{u} (structureSheafRing S.Z)) ℤ} [J.IsKInjective]
    (ρ : B ⟶ J) (hρ : IsIso (DerivedCategory.Q.map ρ))
    (α : DerivedCategory.Q.obj A ⟶ DerivedCategory.Q.obj B)
    (I : CochainComplex (SheafOfModules.{u} (structureSheafRing S.X)) ℤ) [I.IsKInjective] :
    ((Stacks.SheafOfModules.derivedSheafHom S.X.sheaf).map
            ((modulePushforward S.i).mapDerivedCategory.map α).op).app
          (DerivedCategory.Q.obj I) ≫
        (derivedSheafHomPushforwardModelIso S A I).hom =
      (derivedSheafHomPushforwardModelIso S B I).hom ≫
        (modulePushforward S.i).mapDerivedCategory.map
          (((Stacks.SheafOfModules.derivedSheafHom S.Z.sheaf).map α.op).app
            (S.derivedSheafHomExactSupport.obj (DerivedCategory.Q.obj I))) := by
  haveI := hρ
  haveI : IsIso (((Stacks.SheafOfModules.derivedSheafHom S.X.sheaf).map
      ((modulePushforward S.i).mapDerivedCategory.map (DerivedCategory.Q.map ρ)).op).app
        (DerivedCategory.Q.obj I)) :=
    (((Stacks.SheafOfModules.derivedSheafHom S.X.sheaf).mapIso
      (Iso.op ((modulePushforward S.i).mapDerivedCategory.mapIso
        (asIso (DerivedCategory.Q.map ρ))))).app (DerivedCategory.Q.obj I)).isIso_hom
  exact (cancel_epi _).mp
    (derivedSheafHomPushforwardModelIso_natural_source_comp_resolution S ρ α I)

/-- **Naturality of the identification on K-injective representatives for an arbitrary morphism
of the derived category between the classes of two cochain complexes.** The chosen functorial
K-injective resolution of the target supplies the resolution the argument needs. -/
theorem derivedSheafHomPushforwardModelIso_natural_source_derived
    {A B : CochainComplex (SheafOfModules.{u} (structureSheafRing S.Z)) ℤ}
    (α : DerivedCategory.Q.obj A ⟶ DerivedCategory.Q.obj B)
    (I : CochainComplex (SheafOfModules.{u} (structureSheafRing S.X)) ℤ) [I.IsKInjective] :
    ((Stacks.SheafOfModules.derivedSheafHom S.X.sheaf).map
            ((modulePushforward S.i).mapDerivedCategory.map α).op).app
          (DerivedCategory.Q.obj I) ≫
        (derivedSheafHomPushforwardModelIso S A I).hom =
      (derivedSheafHomPushforwardModelIso S B I).hom ≫
        (modulePushforward S.i).mapDerivedCategory.map
          (((Stacks.SheafOfModules.derivedSheafHom S.Z.sheaf).map α.op).app
            (S.derivedSheafHomExactSupport.obj (DerivedCategory.Q.obj I))) :=
  derivedSheafHomPushforwardModelIso_natural_source_of_resolution S
    ((Stacks.Injectives.kInjectiveResolutionInclusion
      (SheafOfModules.{u} (structureSheafRing S.Z))).app B)
    (by rw [DerivedCategory.isIso_Q_map_iff_quasiIso]; infer_instance) α I

/-- The component of the isomorphism of [Stacks, Tag 0E2I] at the class of a K-injective cochain
complex is the identification on K-injective representatives. Together with naturality this
determines the isomorphism. -/
theorem derivedSheafHomPushforwardNatIso_app
    (M : DerivedCategory (SheafOfModules.{u} (structureSheafRing S.Z)))
    (I : CochainComplex (SheafOfModules.{u} (structureSheafRing S.X)) ℤ) [I.IsKInjective] :
    (derivedSheafHomPushforwardNatIso S M).hom.app (DerivedCategory.Q.obj I) =
      (derivedSheafHomPushforwardObjModelIso S M I).hom := by
  dsimp only [derivedSheafHomPushforwardNatIso, derivedSheafHomPushforwardObjModelIso,
    Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Iso.app_inv, NatTrans.comp_app]
  rw [derivedSheafHomPushforwardCochainNatIso_app]

/-- **The isomorphism of [Stacks, Tag 0E2I] at the class of a cochain complex, evaluated at the
class of a K-injective complex, is the identification on K-injective representatives of that
very complex** — not only of the complex chosen by `CategoryTheory.Functor.objPreimage`.

`…derivedSheafHomPushforwardNatIso` is built at the chosen representative, so its component at
an arbitrary source is the identification at an unknown complex conjugated by an unknown derived
isomorphism. The source-naturality for derived morphisms moves it to the given complex, the two
conjugating isomorphisms cancelling. -/
theorem derivedSheafHomPushforwardNatIso_app_cochain
    (M₀ : CochainComplex (SheafOfModules.{u} (structureSheafRing S.Z)) ℤ)
    (I : CochainComplex (SheafOfModules.{u} (structureSheafRing S.X)) ℤ) [I.IsKInjective] :
    (derivedSheafHomPushforwardNatIso S (DerivedCategory.Q.obj M₀)).hom.app
        (DerivedCategory.Q.obj I) =
      (derivedSheafHomPushforwardModelIso S M₀ I).hom := by
  have hgen : ((S.derivedSheafHomPushforwardRepresentative
            (DerivedCategory.Q.obj M₀)).app (DerivedCategory.Q.obj I)).hom ≫
        (derivedSheafHomPushforwardModelIso S
          (DerivedCategory.Q.objPreimage (DerivedCategory.Q.obj M₀)) I).hom =
      (derivedSheafHomPushforwardModelIso S M₀ I).hom ≫
        ((S.pushforwardDerivedSheafHomExactSupportRepresentative
          (DerivedCategory.Q.obj M₀)).app (DerivedCategory.Q.obj I)).hom :=
    derivedSheafHomPushforwardModelIso_natural_source_derived S
      (DerivedCategory.Q.objObjPreimageIso (DerivedCategory.Q.obj M₀)).hom I
  rw [derivedSheafHomPushforwardNatIso_app]
  show ((S.derivedSheafHomPushforwardRepresentative
          (DerivedCategory.Q.obj M₀)).app (DerivedCategory.Q.obj I)).hom ≫
      (derivedSheafHomPushforwardModelIso S
          (DerivedCategory.Q.objPreimage (DerivedCategory.Q.obj M₀)) I).hom ≫
        ((S.pushforwardDerivedSheafHomExactSupportRepresentative
          (DerivedCategory.Q.obj M₀)).app (DerivedCategory.Q.obj I)).inv = _
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun t : _ ⟶ _ => t ≫
          ((S.pushforwardDerivedSheafHomExactSupportRepresentative
            (DerivedCategory.Q.obj M₀)).app (DerivedCategory.Q.obj I)).inv) hgen).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (fun t : _ ⟶ _ =>
              (derivedSheafHomPushforwardModelIso S M₀ I).hom ≫ t)
            ((S.pushforwardDerivedSheafHomExactSupportRepresentative
              (DerivedCategory.Q.obj M₀)).app (DerivedCategory.Q.obj I)).hom_inv_id).trans
          (Category.comp_id _))))

/-- The backward component of `derivedSheafHomPushforwardNatIso_app_cochain`: an isomorphism is
determined by its forward map. -/
theorem derivedSheafHomPushforwardNatIso_inv_app_cochain
    (M₀ : CochainComplex (SheafOfModules.{u} (structureSheafRing S.Z)) ℤ)
    (I : CochainComplex (SheafOfModules.{u} (structureSheafRing S.X)) ℤ) [I.IsKInjective] :
    (derivedSheafHomPushforwardNatIso S (DerivedCategory.Q.obj M₀)).inv.app
        (DerivedCategory.Q.obj I) =
      (derivedSheafHomPushforwardModelIso S M₀ I).inv :=
  (Iso.inv_eq_inv
      ((derivedSheafHomPushforwardNatIso S (DerivedCategory.Q.obj M₀)).app
        (DerivedCategory.Q.obj I))
      (derivedSheafHomPushforwardModelIso S M₀ I)).mpr
    (derivedSheafHomPushforwardNatIso_app_cochain S M₀ I)

/-- **Stacks Project, Tag 0A77.** Derived sheaf Hom with exact support followed by derived
pushforward is the derived internal Hom out of the derived pushforward of the structure sheaf of
the closed subspace: `Ri_* R ℰom(𝒪_Z, -) ≅ R ℰom_X(Ri_* 𝒪_Z, -)`. -/
@[stacks 0A77 "via the derived internal Hom bifunctor"]
def derivedSheafHomExactSupportPushforwardNatIso :
    S.derivedSheafHomExactSupport ⋙ (modulePushforward S.i).mapDerivedCategory ≅
      (Stacks.SheafOfModules.derivedSheafHom S.X.sheaf).obj
        (op ((modulePushforward S.i).mapDerivedCategory.obj
          (RingedSite.derivedStructureSheaf (Stacks.SheafOfModules.ringedSite S.Z.sheaf)))) :=
  (Functor.isoWhiskerLeft S.derivedSheafHomExactSupport
      (Functor.leftUnitor (modulePushforward S.i).mapDerivedCategory)).symm ≪≫
    (Functor.isoWhiskerLeft S.derivedSheafHomExactSupport
        (Functor.isoWhiskerRight
          (RingedSite.derivedStructureSheafHomNatIso
            (Stacks.SheafOfModules.ringedSite S.Z.sheaf))
          (modulePushforward S.i).mapDerivedCategory)).symm ≪≫
      (derivedSheafHomPushforwardNatIso S
        (RingedSite.derivedStructureSheaf
          (Stacks.SheafOfModules.ringedSite S.Z.sheaf))).symm

/-- The isomorphism of [Stacks, Tag 0A77] is the isomorphism of [Stacks, Tag 0E2I] at the
structure sheaf of the closed subspace, composed with the identification of the derived internal
Hom out of the structure sheaf with the identity functor. -/
theorem derivedSheafHomExactSupportPushforwardNatIso_app
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing S.X))) :
    (derivedSheafHomExactSupportPushforwardNatIso S).hom.app K =
      (modulePushforward S.i).mapDerivedCategory.map
          ((RingedSite.derivedStructureSheafHomNatIso
            (Stacks.SheafOfModules.ringedSite S.Z.sheaf)).inv.app
              (S.derivedSheafHomExactSupport.obj K)) ≫
        (derivedSheafHomPushforwardNatIso S
          (RingedSite.derivedStructureSheaf
            (Stacks.SheafOfModules.ringedSite S.Z.sheaf))).inv.app K := by
  dsimp only [derivedSheafHomExactSupportPushforwardNatIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_inv,
    Functor.whiskerLeft_app, Functor.whiskerRight_app]
  rw [Functor.leftUnitor_inv_app]
  exact Category.id_comp _

/-- **The component of the isomorphism of [Stacks, Tag 0A77] at the class of a K-injective
cochain complex, in terms of the identification on K-injective representatives of the structure
sheaf of the closed subspace in degree zero.** `RingedSite.derivedStructureSheaf` is by
definition the class of `RingedSite.structureSheafComplex`, so
`derivedSheafHomPushforwardNatIso_inv_app_cochain` applies at that source with no choice of
representative left in the formula.

This is the form in which a computation of the [Stacks, Tag 0A77] isomorphism against the trace
of [Stacks, Tag 0A76] can proceed: everything on the right is a named composite of
identifications, the only one of them not determined by general nonsense being the complex-level
[Stacks, Tag 0E2I] isomorphism `pushforwardSheafHomComplex`. -/
theorem derivedSheafHomExactSupportPushforwardNatIso_app_isKInjective
    (I : CochainComplex (SheafOfModules.{u} (structureSheafRing S.X)) ℤ) [I.IsKInjective] :
    (derivedSheafHomExactSupportPushforwardNatIso S).hom.app (DerivedCategory.Q.obj I) =
      (modulePushforward S.i).mapDerivedCategory.map
          ((RingedSite.derivedStructureSheafHomNatIso
            (Stacks.SheafOfModules.ringedSite S.Z.sheaf)).inv.app
              (S.derivedSheafHomExactSupport.obj (DerivedCategory.Q.obj I))) ≫
        (derivedSheafHomPushforwardModelIso S
          (RingedSite.structureSheafComplex
            (Stacks.SheafOfModules.ringedSite S.Z.sheaf)) I).inv := by
  rw [derivedSheafHomExactSupportPushforwardNatIso_app,
    derivedSheafHomPushforwardNatIso_inv_app_cochain]

end ClosedQuotientMorphismOfRingedSpaces

end RingedSpaceModuleAdjunction

end
