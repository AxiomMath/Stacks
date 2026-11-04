module

public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackPushforwardQuasiFinite
public import StacksFrontier.AlgebraicGeometry.Quot.QuotFunctorPushforward
public import StacksFrontier.CategoryTheory.Functor.ConjugateQuotientOfHom
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleAffineBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleBaseChangePaste
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleAffinePushforwardExactness
public import StacksFrontier.AlgebraicGeometry.Spaces.AffinePushforwardQuasicoherentUnconditional

/-!
# The direct image along an affine morphism as a morphism of Quot functors

Let `B` be an algebraic space, let `π : X ⟶ Y` be an affine quasi-finite morphism of algebraic
spaces which are separated and of finite presentation over `B`, and let `F` be a quasi-coherent
`𝒪_X`-module, with direct image `G = π_*F`.  Stacks 0DP1 asserts that `π_*` induces a morphism
`Quot_{F/X/B} ⟶ Quot_{G/Y/B}`.  For a scheme `T` over `B` write `π_T : X_T ⟶ Y_T` for the base
change.  The proof of the source sends a quotient `F_T ⟶ Q` to `G_T ⟶ π_{T,*}Q`, and uses four
facts about this construction:

* by Stacks 07U8 the base change map `G_T ⟶ π_{T,*}F_T` is an isomorphism, `π` being affine and
  `F` quasi-coherent;
* `π_T` is affine, so `π_{T,*}` transforms surjections of quasi-coherent modules into
  surjections, and `G_T ⟶ π_{T,*}Q` is again a quotient;
* for a morphism `T' ⟶ T` of test schemes, forming `π_{T,*}Q` commutes with pulling back to
  `T'`, which is part (b) of the proof of Stacks 0DN9 and is Stacks 07U8 again, for `π_T`;
* if `Q` is quasi-coherent, of finite presentation, flat over `T` and has support proper over
  `T`, so has `π_{T,*}Q`, which is claim (a) of the proof of Stacks 0DN9.

This file proves the first three and takes the fourth from
`AlgebraicGeometry.Space.CoherentPushforwardSituation.isCoherentModule_pushforward`.  A quotient
is recorded by its kernel, as in `AlgebraicGeometry.Space.QuotientSituation.quotients`, so the
construction is the kernel of the composite `G_T ⟶ π_{T,*}F_T ⟶ π_{T,*}(F_T/K)`.

## Main definitions

* `AlgebraicGeometry.Space.QuotPushforwardSituation.directImageSituation`: the quotient situation
  `G/Y/B`, the target situation of Stacks 0DP1 with the quasi-coherence of `G` supplied by
  Stacks 07U8.
* `AlgebraicGeometry.Space.QuotPushforwardSituation.directImageQuotient`: **the direct image of
  a quotient**, `K ↦ ker(G_T ⟶ π_{T,*}(F_T/K))`.
* `AlgebraicGeometry.Space.QuotPushforwardSituation.directImageQuotientCokernelIso`: the
  quotient of `G_T` by the direct image of a quasi-coherent quotient `F_T/K` is
  `π_{T,*}(F_T/K)`.
* `AlgebraicGeometry.Space.QuotPushforwardSituation.toCoherentPushforwardSituation`: the standing
  data of Stacks 0DN9 underlying that of Stacks 0DP1.
* `AlgebraicGeometry.Space.QuotPushforwardSituation.directImageQuotFunctorMap`: the morphism of
  Quot functors built from claim (a) of the proof of Stacks 0DN9.
* `AlgebraicGeometry.Space.QuotPushforwardSituation.pushforwardQuotFunctorMap`: the morphism
  `Quot_{F/X/B} ⟶ Quot_{π_*F/Y/B}` induced by `π_*`.

## Main results

* `AlgebraicGeometry.Space.moduleBaseChangeMap_paste_triangle`: the pasting identity for the
  base change maps of `𝒪`-modules of two stacked squares of algebraic spaces.
* `AlgebraicGeometry.Space.epi_conjQuotientProjectionOfHom_moduleBaseChangeMap`: for a cartesian
  square with affine right column, the base change map followed by the direct image of a
  surjection onto a quasi-coherent quotient is surjective.
* `AlgebraicGeometry.Space.conjSubobjectOfHom_moduleBaseChangeMap_conjSubobject`: the direct
  image of quotients commutes with a further base change.
* `AlgebraicGeometry.Space.QuotPushforwardSituation.epi_directImageQuotientProjection` and
  `AlgebraicGeometry.Space.QuotPushforwardSituation.directImageQuotient_quotientPullback`: the
  last two read in the Quot situation of Stacks 0DP1.
* `AlgebraicGeometry.Space.QuotPushforwardSituation.directImageQuotient_mem`: the direct image
  of a member of `Quot_{F/X/B}(T)` is a member of `Quot_{G/Y/B}(T)`.

## Implementation notes

The base change map `G_T ⟶ π_{T,*}F_T` is a natural transformation of functors on all
`𝒪_X`-modules, but it is invertible only at quasi-coherent ones, and `π_{T,*}` is right exact
only on quasi-coherent modules.  So the direct image of a quotient is built from the comparison
*morphism* by `CategoryTheory.Functor.conjSubobjectOfHom`, and invertibility and exactness are used
exactly where the source uses them, at `F` and at the quasi-coherent quotient.

The standing data of Stacks 0DP1 records the structure morphism of `X` as a morphism with
`π ≫ (Y ⟶ B) = (X ⟶ B)`, while that of Stacks 0DN9 takes it to be the composite.  The two are
matched by substituting along that equation, which is how claim (a) of Stacks 0DN9 is read on the
base changes `X_T` of Stacks 0DP1
(`QuotPushforwardSituation.isQuotModule_modulePushforward_of_isCoherentModule`).

The instances `Stacks.Cohomology.SiteModules.moduleSheavesAbelian` and
`Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck`, whose module universe is not
determined by their conclusion, are switched off: with them, instance search for the abelian
structure on the modules of an algebraic space stops on an unsolvable universe constraint
instead of finding `SheafOfModules.instAbelian`.

## References

* [Stacks Project, Tag 0DP1](https://stacks.math.columbia.edu/tag/0DP1)
* [Stacks Project, Tag 0DN9](https://stacks.math.columbia.edu/tag/0DN9)
* [Stacks Project, Tag 07U8](https://stacks.math.columbia.edu/tag/07U8)
* [Stacks Project, Tag 09TR](https://stacks.math.columbia.edu/tag/09TR)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

namespace AlgebraicGeometry.Space

universe u

attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The pasting law for base change maps, with the two composite horizontal morphisms given as
morphisms equal to the composites, read through
`AlgebraicGeometry.Space.modulePullbackTriangle`. -/
theorem moduleBaseChangeMap_paste_triangle {X X' X'' Y Y' Y'' : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X) (h : Y'' ⟶ Y') (f'' : X'' ⟶ Y'')
    (h' : X'' ⟶ X') {k : Y'' ⟶ Y} {k' : X'' ⟶ X} (hk : h ≫ g = k) (hk' : h' ≫ g' = k')
    (comm₁ : g' ≫ f = f' ≫ g) (comm₂ : h' ≫ f' = f'' ≫ h) (w : k' ≫ f = f'' ≫ k)
    (K : Modules.{u, u} B S hS X.1 X.2) :
    (modulePullbackTriangle B S hS hk).hom.app ((modulePushforward B S hS f).obj K) ≫
        (modulePullback B S hS h).map ((moduleBaseChangeMap f g f' g' comm₁).app K) ≫
        (moduleBaseChangeMap f' h f'' h' comm₂).app ((modulePullback B S hS g').obj K) =
      (moduleBaseChangeMap f k f'' k' w).app K ≫
        (modulePushforward B S hS f'').map ((modulePullbackTriangle B S hS hk').hom.app K) := by
  subst hk hk'
  rw [moduleBaseChangeMap_paste f g f' g' h f'' h' comm₁ comm₂ w K, modulePullbackTriangle_rfl,
    modulePullbackTriangle_rfl]
  simp only [Iso.symm_hom, Category.assoc, ← Functor.map_comp, Iso.hom_inv_id_app]
  have e := (modulePushforward B S hS f'').map_id
    ((modulePullback B S hS g' ⋙ modulePullback B S hS h').obj K)
  rw [e]
  exact (Category.comp_id _).symm

/-- For a cartesian square with `f` affine, a quasi-coherent `F` and a quasi-coherent quotient
`(g')^*F/K`, the projection of `g^*f_*F` onto `f'_*((g')^*F/K)` through the base change map is an
epimorphism. -/
theorem epi_conjQuotientProjectionOfHom_moduleBaseChangeMap {X Y X' Y' : AlgebraicSpaces B S hS}
    {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X} (sq : IsPullback g' f' f g)
    (hf : IsAffineHom B S hS f.hom) (F : Modules.{u, u} B S hS X.1 X.2)
    (hF : F.IsQuasicoherentOnSite) (K : Subobject ((modulePullback B S hS g').obj F))
    (hK : (cokernel K.arrow : Modules.{u, u} B S hS X'.1 X'.2).IsQuasicoherentOnSite) :
    Epi (Functor.conjQuotientProjectionOfHom (moduleBaseChangeMap f g f' g' sq.w) K) := by
  have h1 := isIso_moduleBaseChangeMap_app_of_isAffineHom sq hf F hF
  have hf' := isAffineHom_hom_of_isPullback sq hf
  have hF' := isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS g' F hF
  have h2 := @epi_modulePushforward_map_of_isAffineHom _ _ _ _ _ f' hf' _ _ hF' hK
    (cokernel.π K.arrow) coequalizer.π_epi
  exact @epi_comp _ _ _ _ _ _ (@IsIso.epi_of_iso _ _ _ _ _ h1) _ h2

/-- **The direct image of quotients commutes with a further base change** (part (b) of the
proof of Stacks 0DN9, read on quotients). -/
theorem conjSubobjectOfHom_moduleBaseChangeMap_conjSubobject
    {X X' X'' Y Y' Y'' : AlgebraicSpaces B S hS} {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'}
    {g' : X' ⟶ X} {h : Y'' ⟶ Y'} {f'' : X'' ⟶ Y''} {h' : X'' ⟶ X'} {k : Y'' ⟶ Y}
    {k' : X'' ⟶ X} (sq₁ : IsPullback g' f' f g) (sq₂ : IsPullback h' f'' f' h)
    (hk : h ≫ g = k) (hk' : h' ≫ g' = k') (w : k' ≫ f = f'' ≫ k)
    (hf : IsAffineHom B S hS f.hom) (F : Modules.{u, u} B S hS X.1 X.2)
    (hF : F.IsQuasicoherentOnSite) (K : Subobject ((modulePullback B S hS g').obj F))
    (hK : (cokernel K.arrow : Modules.{u, u} B S hS X'.1 X'.2).IsQuasicoherentOnSite) :
    Functor.conjSubobjectOfHom (moduleBaseChangeMap f k f'' k' w)
        (Functor.conjSubobject (modulePullbackTriangle B S hS hk') K) =
      Functor.conjSubobject (modulePullbackTriangle B S hS hk)
        (Functor.conjSubobjectOfHom (moduleBaseChangeMap f g f' g' sq₁.w) K) :=
  Functor.conjSubobjectOfHom_conjSubobject _ (moduleBaseChangeMap f' h f'' h' sq₂.w) _ _ _ F
    (moduleBaseChangeMap_paste_triangle f g f' g' h f'' h' hk hk' sq₁.w sq₂.w w F) K
    (epi_conjQuotientProjectionOfHom_moduleBaseChangeMap sq₁ hf F hF K hK)
    (isIso_moduleBaseChangeMap_app_of_isAffineHom sq₂
      (isAffineHom_hom_of_isPullback sq₁ hf) _ hK)

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.Space

namespace QuotPushforwardSituation

universe u

attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  (D : QuotPushforwardSituation B S hS)

/-- The base change `π_T : X_T ⟶ Y_T` of the affine morphism of the situation is affine. -/
theorem isAffineHom_baseChangeOfMap (T : SchemesOver D.base) :
    IsAffineHom B S hS (D.baseChangeOfMap T).hom :=
  isAffineHom_hom_of_isPullback (D.isPullback_baseChangeOfMap T).flip D.affine

/-- The base changes of the morphism of the situation along a morphism `m : T' ⟶ T` of test
schemes commute with the induced morphisms of base changes. -/
@[reassoc]
theorem baseChangeMap_comp_baseChangeOfMap {T' T : SchemesOver D.base} (m : T' ⟶ T) :
    baseChangeMap D.structureX m ≫ D.baseChangeOfMap T =
      D.baseChangeOfMap T' ≫ baseChangeMap D.structureY m := by
  refine baseChange_hom_ext D.structureY ?_ ?_
  · simp only [Category.assoc, baseChangeOfMap_comp_projection, baseChangeMap_comp_projection,
      baseChangeMap_comp_projection_assoc]
  · simp only [Category.assoc, baseChangeOfMap_comp_inclusion, baseChangeMap_comp_inclusion,
      baseChangeOfMap_comp_inclusion_assoc]

/-- The square of `π_{T'}` over `π_T` is cartesian: `X_{T'} = Y_{T'} ×_{Y_T} X_T`. -/
theorem isPullback_baseChangeMap_baseChangeOfMap {T' T : SchemesOver D.base} (m : T' ⟶ T) :
    IsPullback (baseChangeMap D.structureX m) (D.baseChangeOfMap T') (D.baseChangeOfMap T)
      (baseChangeMap D.structureY m) := by
  refine IsPullback.of_right ?_ (D.baseChangeMap_comp_baseChangeOfMap m)
    (D.isPullback_baseChangeOfMap T).flip
  rw [baseChangeMap_comp_projection, baseChangeMap_comp_projection]
  exact (D.isPullback_baseChangeOfMap T').flip

/-- The quotient situation `G/Y/B` of Stacks 09TR for the direct image `G = π_*F`: the
quotient situation `AlgebraicGeometry.Space.QuotPushforwardSituation.targetSituation`, with the
quasi-coherence of `G` supplied by Stacks 07U8. -/
abbrev directImageSituation : QuotSituation B S hS :=
  D.targetSituation (schemeTargetAffinePushforwardQuasicoherent B S hS)

/-- The base change map `G_T ⟶ π_{T,*}F_T` of the cartesian square of `π_T` over `π`. -/
abbrev directImageBaseChange (T : SchemesOver D.base) :=
  moduleBaseChangeMap D.π (baseChangeProjection D.structureY T) (D.baseChangeOfMap T)
    (baseChangeProjection D.structureX T) (D.isPullback_baseChangeOfMap T).flip.w

/-- **The direct image of a quotient.**  A quotient `F_T ⟶ F_T/K` is sent to the quotient
`G_T ⟶ π_{T,*}(F_T/K)` of `G_T`, the base change map of Stacks 07U8 followed by the direct image
of the projection, recorded — as the quotients themselves are — by its kernel. -/
def directImageQuotient (T : SchemesOver D.base)
    (K : Subobject (D.sourceSituation.baseChangeModule T)) :
    Subobject (D.directImageSituation.baseChangeModule T) :=
  Functor.conjSubobjectOfHom (D.directImageBaseChange T) K

/-- The projection of `G_T` onto the direct image of a quasi-coherent quotient of `F_T` is an
epimorphism: the base change map is an isomorphism by Stacks 07U8 and the direct image along the
affine `π_T` is exact on quasi-coherent modules. -/
theorem epi_directImageQuotientProjection (T : SchemesOver D.base)
    (K : Subobject (D.sourceSituation.baseChangeModule T))
    (hK : (D.sourceSituation.quotientModule T K).IsQuasicoherentOnSite) :
    Epi (Functor.conjQuotientProjectionOfHom (D.directImageBaseChange T) K) :=
  epi_conjQuotientProjectionOfHom_moduleBaseChangeMap (D.isPullback_baseChangeOfMap T).flip
    D.affine D.F D.quasicoherent K hK

/-- **The quotient of `G_T` by the direct image of a quotient is the direct image of that
quotient**: `G_T / directImageQuotient T K ≅ π_{T,*}(F_T/K)`. -/
def directImageQuotientCokernelIso (T : SchemesOver D.base)
    (K : Subobject (D.sourceSituation.baseChangeModule T))
    (hK : (D.sourceSituation.quotientModule T K).IsQuasicoherentOnSite) :
    D.directImageSituation.quotientModule T (D.directImageQuotient T K) ≅
      (modulePushforward B S hS (D.baseChangeOfMap T)).obj
        (D.sourceSituation.quotientModule T K) :=
  Functor.conjSubobjectOfHomCokernelIso (D.directImageBaseChange T) K
    (D.epi_directImageQuotientProjection T K hK)

/-- **The direct image of quotients is compatible with pullback along a morphism of test
schemes** (part (b) of the proof of Stacks 0DN9, read on quotients). -/
theorem directImageQuotient_quotientPullback {T' T : SchemesOver D.base} (m : T' ⟶ T)
    (K : Subobject (D.sourceSituation.baseChangeModule T))
    (hK : (D.sourceSituation.quotientModule T K).IsQuasicoherentOnSite) :
    D.directImageQuotient T' (D.sourceSituation.quotientPullback m K) =
      D.directImageSituation.quotientPullback m (D.directImageQuotient T K) :=
  conjSubobjectOfHom_moduleBaseChangeMap_conjSubobject (D.isPullback_baseChangeOfMap T).flip
    (D.isPullback_baseChangeMap_baseChangeOfMap m) (baseChangeMap_comp_projection D.structureY m)
    (baseChangeMap_comp_projection D.structureX m) (D.isPullback_baseChangeOfMap T').flip.w
    D.affine D.F D.quasicoherent K hK

end QuotPushforwardSituation

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.Space

namespace QuotPushforwardSituation

universe u

attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  (D : QuotPushforwardSituation B S hS)

/-- The standing data of Stacks 0DN9 underlying that of Stacks 0DP1: the quasi-finite morphism
`π : X ⟶ Y` of algebraic spaces separated and of finite presentation over `B`. -/
def toCoherentPushforwardSituation : CoherentPushforwardSituation B S hS where
  base := D.base
  X := D.X
  Y := D.Y
  π := D.π
  f := D.structureY
  quasiFinite := D.quasiFinite
  separated_source := D.comp ▸ D.separatedX
  finitePresentation_source := D.comp ▸ D.finitePresentationX
  separated_target := D.separatedY
  finitePresentation_target := D.finitePresentationY

/-- **Claim (a) of the proof of Stacks 0DN9 gives the four conditions of Stacks 09TR on a direct
image.**  If `π_{T,*}` carries objects of `Coh_{X/B}` to objects of `Coh_{Y/B}`, then the direct
image along `π_T` of a module satisfying the four conditions of Stacks 09TR over `T` satisfies
them again. -/
theorem isQuotModule_modulePushforward_of_isCoherentModule
    (H : ∀ A : CoherentObject D.toCoherentPushforwardSituation.source,
      D.toCoherentPushforwardSituation.target.IsCoherentModule A.T
        ((modulePushforward B S hS (D.toCoherentPushforwardSituation.mapAt A.T)).obj A.F))
    (T : SchemesOver D.base)
    (Q : Modules.{u, u} B S hS (D.sourceSituation.space T).1 (D.sourceSituation.space T).2)
    (hQ : D.sourceSituation.IsQuotModule T Q) :
    D.directImageSituation.IsQuotModule T
      ((modulePushforward B S hS (D.baseChangeOfMap T)).obj Q) := by
  obtain ⟨base, X, Y, π, sX, sY, comp, F, qc, aff, qf, sepX, sepY, fpX, fpY⟩ := D
  subst comp
  obtain ⟨hcl, hpr⟩ := hQ.2.2.2
  have h := H ⟨T, Q, hQ.1, hQ.2.2.1, hQ.2.1, ⟨_, hcl, hpr⟩⟩
  obtain ⟨_, hcl', hpr'⟩ := h.properSupport
  exact ⟨h.quasicoherent, h.flat, h.finitePresentation, hcl', hpr'⟩

/-- Claim (a) of the proof of Stacks 0DN9 for the situation, as a proposition. -/
abbrev PushforwardIsCoherent : Prop :=
  ∀ A : CoherentObject D.toCoherentPushforwardSituation.source,
    D.toCoherentPushforwardSituation.target.IsCoherentModule A.T
      ((modulePushforward B S hS (D.toCoherentPushforwardSituation.mapAt A.T)).obj A.F)

/-- The direct image of a member of `Quot_{F/X/B}(T)` is a member of `Quot_{π_*F/Y/B}(T)`, granted
claim (a) of the proof of Stacks 0DN9. -/
theorem directImageQuotient_mem (H : D.PushforwardIsCoherent) (T : SchemesOver D.base)
    (K : Subobject (D.sourceSituation.baseChangeModule T))
    (hK : K ∈ D.sourceSituation.properlySupportedQuotients T) :
    D.directImageQuotient T K ∈ D.directImageSituation.properlySupportedQuotients T :=
  (D.directImageSituation.mem_properlySupportedQuotients_iff T _).mpr
    (QuotSituation.IsQuotModule.of_iso (D.directImageQuotientCokernelIso T K hK.1.1.1).symm
      (D.isQuotModule_modulePushforward_of_isCoherentModule H T _
        ((D.sourceSituation.mem_properlySupportedQuotients_iff T K).mp hK)))

/-- The morphism of Quot functors `Quot_{F/X/B} ⟶ Quot_{π_*F/Y/B}` induced by the direct image,
granted claim (a) of the proof of Stacks 0DN9: over a test scheme it sends a quotient `F_T ⟶ Q`
to `G_T ⟶ π_{T,*}Q`. -/
def directImageQuotFunctorMap (H : D.PushforwardIsCoherent) :
    D.sourceSituation.quotFunctor ⟶ D.directImageSituation.quotFunctor where
  app T := ↾fun K ↦ ⟨D.directImageQuotient T.unop K.1, D.directImageQuotient_mem H T.unop K.1 K.2⟩
  naturality _ _ m := ConcreteCategory.hom_ext _ _ fun K ↦
    Subtype.ext (D.directImageQuotient_quotientPullback m.unop K.1 K.2.1.1.1)

end QuotPushforwardSituation

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.Space

namespace QuotPushforwardSituation

universe u

attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  (D : QuotPushforwardSituation B S hS)

/-- **Claim (a) of the proof of Stacks 0DN9 for the situation**: `π_{T,*}` carries the objects of
`Coh_{X/B}` to objects of `Coh_{Y/B}`, `π` being quasi-finite and `X`, `Y` separated and of finite
presentation over `B`. -/
theorem pushforwardIsCoherent : D.PushforwardIsCoherent :=
  D.toCoherentPushforwardSituation.isCoherentModule_pushforward

/-- Let `B` be an algebraic space, let `π : X ⟶ Y` be an affine quasi-finite morphism of
algebraic spaces which are separated and of finite presentation over `B`, and let `F` be a
quasi-coherent `𝒪_X`-module.  Then `π_*` induces a morphism
`Quot_{F/X/B} ⟶ Quot_{π_*F/Y/B}`: over a scheme `T` over `B` it sends a quotient `F_T ⟶ Q` to the
quotient `(π_*F)_T ≅ π_{T,*}F_T ⟶ π_{T,*}Q`. -/
@[stacks 0DP1]
def pushforwardQuotFunctorMap :
    D.sourceSituation.quotFunctor ⟶ D.directImageSituation.quotFunctor :=
  D.directImageQuotFunctorMap D.pushforwardIsCoherent

/-- Over a test scheme `T`, the morphism of Stacks 0DP1 sends the quotient of `F_T` with kernel
`K` to the quotient of `(π_*F)_T` with kernel `directImageQuotient T K`. -/
theorem pushforwardQuotFunctorMap_app_val (T : SchemesOver D.base)
    (K : Subobject (D.sourceSituation.baseChangeModule T))
    (hK : K ∈ D.sourceSituation.properlySupportedQuotients T) :
    (D.pushforwardQuotFunctorMap.app (Opposite.op T) ⟨K, hK⟩).1 = D.directImageQuotient T K :=
  rfl

end QuotPushforwardSituation

end AlgebraicGeometry.Space

end
