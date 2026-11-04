module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.Coherent
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPullbackProperties
public import StacksFrontier.AlgebraicGeometry.Cohomology.Coherent.FiniteTilde
public import StacksFrontier.AlgebraicGeometry.AffinePushforward.Basic
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FinitePresentationPullback
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.CoherentFinitePresentation
public import StacksFrontier.Topology.Sheaves.Modules.FiniteType

/-!
# Finite type across the slice sites of a scheme

Finiteness of a sheaf of modules on a scheme `X` is defined by local generating sections indexed
by objects of the site `Opens X`, so `M.over U` is a sheaf of modules on the slice site
`(Opens.grothendieckTopology X).over U`, whereas `M.restrict U.ι` is a sheaf of modules on the
*scheme* `U`. The two are related by the equivalence `Scheme.Modules.overEquiv U`, and the
finiteness class has to be carried across it. This file does that, and deduces that being of
finite type is local on an open cover of `X`.

The transport is an instance of a more general statement: a continuous and cocontinuous functor
of sites which is a left adjoint and which identifies the two structure sheaves carries finite
type along its pushforward of modules. That is proved here for an arbitrary such functor and then
specialised to `Scheme.Opens.overEquivalence`.

## Main results

* `Stacks.AlgebraicGeometry.CoherentTFAE.isFiniteType_pushforward`: the pushforward of modules
  along a continuous, cocontinuous, left-adjoint functor of sites which identifies the structure
  sheaves preserves finite type.
* `Stacks.AlgebraicGeometry.CoherentTFAE.isContinuous_overPost_of_isEquivalence`: the slice of an
  equivalence of sites is continuous.
* `Stacks.AlgebraicGeometry.CoherentTFAE.isFiniteType_overEquiv_inverse`: an `𝒪_U`-module of
  finite type on the scheme `U` is of finite type as a sheaf of modules on the slice site over
  `U`.
* `Stacks.AlgebraicGeometry.CoherentTFAE.isFinitePresentation_restrict`: finite presentation is
  preserved by restriction along an open immersion of schemes.
* `Stacks.AlgebraicGeometry.CoherentTFAE.isFiniteType_of_cover`: being of finite type is local on
  an open cover.

## Implementation notes

The generating sections of the pushforward are indexed by triples `(Y, i, v)` consisting of an
object `Y` of the source site, an index `i` of a chosen family of local generating sections of
`M`, and a morphism `G.obj Y ⟶ P.X i`; the covering condition is the cover lifting property of a
cocontinuous functor. Finiteness of that family is finiteness of the original one, index by
index, which is why the index type gains two components without gaining elements in any fibre.

Invertibility of the comparison `φ` of structure sheaves, and the finiteness hypothesis on `M`,
are explicit arguments rather than instances. Instance synthesis unfolds only reducible
definitions, and at the two use sites the ambient sheaf of rings is spelled
`Scheme.ringCatSheaf` of an open subscheme on one side and
`Opens.sheafRestrict _ |>.obj _` on the other; those agree only after unfolding semireducible
definitions, which ordinary unification does and instance search does not. Passing the
hypotheses positionally lets the expected type drive the unification instead; inside each proof
they are re-introduced with `have` so that synthesis can use them again.

`SheafOfModules.IsFiniteType.mk` is applied with its universe arguments written out: the
universes of the local generating data are not determined by the goal, and elaboration defaults
them to `0`, which is a universe mismatch over a site in universe `u`.

There is deliberately no finite-presentation analogue of `isFiniteType_pushforward` here. It
would be the same construction with `SheafOfModules.QuasicoherentData.pushforward` in place of
the local generating data, but that definition builds its comparison of structure sheaves through
a type-ascribed `letI`, so recognising the transported presentation as the image of the original
one is a definitional unfolding which neither instance search nor `whnf` within the default
heartbeat budget performs. The characterisation of coherence in
`StacksFrontier.AlgebraicGeometry.Cohomology.LocallyNoetherian.Coherent` therefore closes its cycle
of implications through coherence rather than through finite presentation, and needs only the
finite-type transport.

## References

* [Stacks Project, Tag 01XZ](https://stacks.math.columbia.edu/tag/01XZ)
* [Stacks Project, Tag 01BW](https://stacks.math.columbia.edu/tag/01BW)
* [Stacks Project, Tag 01BQ](https://stacks.math.columbia.edu/tag/01BQ)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.AlgebraicGeometry.CoherentTFAE

section OverPost

variable {C D : Type u} [Category.{u} C] [Category.{u} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}

/-- **The slice of an equivalence of sites is continuous.** Composition with the functor of an
equivalence is downwards closed up to isomorphism, so the compatible-preserving condition holds
for formal reasons, and cover preservation is inherited from the equivalence. -/
theorem isContinuous_overPost_of_isEquivalence
    (e : C ≌ D) [e.functor.IsContinuous J K] (V : C) :
    (Over.post (X := V) e.functor).IsContinuous (J.over V) (K.over (e.functor.obj V)) := by
  let d := Over.postEquiv (X := V) e
  let := d.isEquivalence_functor
  exact Functor.isContinuous_of_coverPreserving
    (compatiblePreservingOfDownwardsClosed (K.over (e.functor.obj V)) (Over.post e.functor)
      fun {_ b} _ ↦ ⟨d.inverse.obj b, d.counitIso.app b⟩)
    (CoverPreserving.overPost V (CoverPreserving.of_isContinuous e.functor J K))

end OverPost

section Sites

variable {C D : Type u} [Category.{u} C] [Category.{u} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  {R : Sheaf J RingCat.{u}} {S : Sheaf K RingCat.{u}}

/-- **Finite type is preserved by the pushforward along a functor of sites** which is continuous,
cocontinuous, a left adjoint, an isomorphism on structure sheaves, and whose slices are
continuous. The generating sections of the image are the generating sections of `M`, reindexed
along the cover lifting property. -/
theorem isFiniteType_pushforward
    [∀ X, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]
    [∀ X, HasSheafify (K.over X) AddCommGrpCat.{u}]
    [∀ X, (K.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]
    (G : D ⥤ C) [G.IsContinuous K J] [G.IsCocontinuous K J]
    (φ : S ⟶ (G.sheafPushforwardContinuous RingCat.{u} K J).obj R) (hφ : IsIso φ)
    (η : (SheafOfModules.pushforward φ).obj (SheafOfModules.unit R) ≅
      SheafOfModules.unit S)
    [G.IsLeftAdjoint]
    [∀ X, (Over.post (X := X) G).IsContinuous (K.over X) (J.over (G.obj X))]
    [HasPullbacks C] [HasPullbacks D]
    (M : SheafOfModules.{u} R) (hM : M.IsFiniteType) :
    ((SheafOfModules.pushforward φ).obj M).IsFiniteType := by
  have := hφ
  have := hM
  obtain ⟨P, hP⟩ := SheafOfModules.IsFiniteType.exists_localGeneratorsData M
  let Q : ((SheafOfModules.pushforward φ).obj M).LocalGeneratorsData := {
    I := Σ (X : D) (i : P.I), G.obj X ⟶ P.X i
    X i := i.1
    coversTop Y := by
      refine K.superset_covering ?_ (G.cover_lift K _ (P.coversTop (G.obj Y)))
      intro Z g ⟨i, ⟨v⟩⟩
      exact ⟨⟨Z, i, v⟩, ⟨𝟙 _⟩⟩
    generators i := by
      have := hφ
      let G' := Over.post (X := i.1) G ⋙ Over.map i.2.2
      have : G'.IsContinuous (K.over i.1) (J.over (P.X i.2.1)) :=
        Functor.isContinuous_comp _ _ _ (J.over _) _
      have : G'.IsCocontinuous (K.over i.1) (J.over (P.X i.2.1)) :=
        isCocontinuous_comp _ _ _ (J.over _)
      let ψ : S.over i.1 ⟶ (G'.sheafPushforwardContinuous RingCat.{u}
          (K.over i.1) (J.over (P.X i.2.1))).obj (R.over (P.X i.2.1)) :=
        ((Over.forget i.1).sheafPushforwardContinuous RingCat.{u} (K.over i.1) K).map φ
      have : IsIso ψ := by
        dsimp only [ψ]
        exact (((Over.forget i.1).sheafPushforwardContinuous RingCat.{u}
          (K.over i.1) K).mapIso (@asIso _ _ _ _ φ hφ)).isIso_hom
      have : (SheafOfModules.pushforward.{u} ψ).IsLeftAdjoint :=
        SheafOfModules.isLeftAdjoint_pushforward_of_isIso ψ
      let overS : SheafOfModules.{u} S ⥤ SheafOfModules.{u} (S.over i.1) :=
        SheafOfModules.pushforward (𝟙 _)
      let e : (SheafOfModules.pushforward ψ).obj (SheafOfModules.unit (R.over (P.X i.2.1))) ≅
          SheafOfModules.unit (S.over i.1) := overS.mapIso η
      exact (P.generators i.2.1).map (SheafOfModules.pushforward ψ) e.symm }
  refine SheafOfModules.IsFiniteType.mk.{u, u, u} ⟨Q, ?_⟩
  constructor
  intro i
  constructor
  exact (hP.isFiniteType i.2.1).finite

end Sites

/-- **Finite presentation is preserved by restriction along an open immersion of schemes.** The
restriction functor is isomorphic to the pullback functor, and the pullback of a module of finite
presentation along a morphism of ringed spaces is of finite presentation. -/
theorem isFinitePresentation_restrict {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsOpenImmersion f] (M : Y.Modules) [M.IsFinitePresentation] :
    (M.restrict f).IsFinitePresentation :=
  have h : ((Scheme.Modules.pullback f).obj M).IsFinitePresentation :=
    @Stacks.SheafOfModules.modulePullback_isFinitePresentation _ _ f.toLRSHom.toShHom M
      ‹M.IsFinitePresentation›
  (SheafOfModules.isFinitePresentation.{u, u, u} _).prop_of_iso
    ((Scheme.Modules.restrictFunctorIsoPullback f).app M).symm h

/-- **An `𝒪_U`-module of finite type on an open subscheme is of finite type over the slice
site.** -/
theorem isFiniteType_overEquiv_inverse {X : Scheme.{u}} (U : X.Opens)
    (M : U.toScheme.Modules) [M.IsFiniteType] :
    ((Scheme.Modules.overEquiv U).inverse.obj M).IsFiniteType := by
  have := isContinuous_overPost_of_isEquivalence (J := (Opens.grothendieckTopology X).over U)
    (K := Opens.grothendieckTopology (↥(U : Opens X))) U.overEquivalence
  exact isFiniteType_pushforward U.overEquivalence.functor
    (U.sheafRestrictSheafEquivOver.app X.ringCatSheaf).inv (Iso.isIso_inv _)
    (U.sheafOfModulesEquivOverInverseUnit X.ringCatSheaf) M ‹M.IsFiniteType›

/-- **Being of finite type is local on an open cover.** -/
theorem isFiniteType_of_cover {X : Scheme.{u}} (M : X.Modules)
    {ι : Type u} (U : ι → X.Opens) (hU : IsOpenCover U)
    (hM : ∀ i, (M.restrict (U i).ι).IsFiniteType) : M.IsFiniteType := by
  have hlocal (i : ι) : (M.over (U i)).IsFiniteType := by
    have := hM i
    have := isFiniteType_overEquiv_inverse (U i) (M.restrict (U i).ι)
    exact Stacks.SheafOfModules.isFiniteType_of_iso.{u}
      (AffinePushforward.overInverseIso (U i) M).symm
  exact Stacks.SheafOfModules.isFiniteType_of_coversTop M U ((Opens.coversTop_iff X U).2 hU)

end Stacks.AlgebraicGeometry.CoherentTFAE

end
