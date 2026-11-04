module

public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.SectionsColimit.Basic
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.Algebra
public import StacksFrontier.AlgebraicGeometry.Modules.TildeFiniteness
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FinitePresentationPullback

/-!
# Descent of finitely presented modules through a limit of affine schemes

Let `D` be a cofiltered diagram of schemes with affine transition morphisms, one of whose
stages is affine, and let `S = lim D` be its limit.  This file proves that every sheaf of
`𝒪_S`-modules of finite presentation is the pullback of a sheaf of finite presentation at some
stage of the diagram.  This is the affine case of [Stacks Project, Tag 01ZR] (1), from which
the general quasi-compact quasi-separated statement is obtained in the source by Zariski
glueing.

## Main results

* `Stacks.AlgebraicGeometry.ModuleLimits.exists_isFinitePresentation_pullback_iso_of_isLimit`:
  for a cofiltered diagram `D` of affine schemes with limit cone `c`, every
  `F : c.pt.Modules` of finite presentation is isomorphic to the pullback along `c.π.app i`
  of some `Fᵢ : (D.obj i).Modules` of finite presentation.
* `..._pullback_iso_of_isLimit_of_isAffine_stage`, in the same namespace: the same conclusion
  when only the transition morphisms are affine and a single stage is affine.

## Implementation notes

The hypotheses of the source — affine transition morphisms and quasi-compact, quasi-separated
stages — are all implied by the stages being affine, so the first statement omits them; the
second assumes only what it needs, and in particular never needs quasi-compactness or
quasi-separatedness.  It is deduced from the first by restricting the diagram to `Over i₀`,
whose forgetful functor to a cofiltered category is initial, so the whiskered cone is still a
limit, and every stage above `i₀` is affine because an affine morphism to an affine scheme has
affine source.

Three inputs are combined in the first statement.  The ring-level comparison is Mathlib's
`AlgebraicGeometry.preservesLimit_rightOp_Γ`: global sections turn a limit of affine schemes
into a colimit of rings, so `Γ(S, ⊤)` is the filtered colimit of the `Γ(D.obj i, ⊤)`.  The
module-level descent over that colimit is
`Stacks.ModuleDescent.exists_extendScalars_iso_of_isColimit`.  The passage between modules and
quasi-coherent sheaves is `AlgebraicGeometry.tilde_isFinitePresentation_iff` in one direction
and `Stacks.AlgebraicGeometry.SectionsColimit.tildePullbackIso` — the identification of
`(Spec.map φ)^* (M^~)` with `(T ⊗_R M)^~` — for the compatibility with pullback.

The index category is left with arbitrary object and morphism universes, unrelated to the
universe `u` of the schemes.  That is possible here, where Mathlib's `AffineTransitionLimit`
API is stated only for `I : Type u` with `Category.{u} I`, because every input used is
universe-polymorphic in the shape: `preservesLimit_rightOp_Γ` is, and the joint surjectivity
of a filtered colimit of rings is proved in `StacksFrontier.AlgebraicGeometry.ModuleLimits.Algebra`
through the universal property, which needs no smallness.  The generality is not idle — the second
statement applies the first to the index category `Over i₀`, whose object universe is
`max u v`.  The quasi-compact quasi-separated case cannot currently be done this way: it rests
on `AlgebraicGeometry.nonempty_isColimit_Γ_mapCocone`, whose proof goes through
`PreservesColimit D.op (forget CommRingCat)` and so through
`HasColimitsOfShape I CommRingCat.{u}`, which Mathlib provides only for `I : Type u` with
`Category.{u} I`.

## References

* [Stacks Project, Tag 01ZR](https://stacks.math.columbia.edu/tag/01ZR)
* [Stacks Project, Tag 05N7](https://stacks.math.columbia.edu/tag/05N7)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe v u w

namespace Stacks.AlgebraicGeometry.ModuleLimits

variable {I : Type w} [Category.{v} I] (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)

/-- Pullback of a sheaf of modules of finite presentation along a morphism of schemes is of
finite presentation.  This is [Stacks Project, Tag 01BQ] transported from ringed spaces to
schemes. -/
theorem isFinitePresentation_pullback {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Y.Modules)
    [M.IsFinitePresentation] :
    ((Scheme.Modules.pullback f).obj M).IsFinitePresentation :=
  let g : X.toRingedSpace ⟶ Y.toRingedSpace := f.toLRSHom.toShHom
  @Stacks.SheafOfModules.modulePullback_isFinitePresentation _ _ g M ‹M.IsFinitePresentation›

include hc in
/-- **Stacks Project, Tag 01ZR (1), affine case.**  A sheaf of modules of finite presentation
on the limit of a cofiltered diagram of affine schemes is the pullback of a sheaf of modules of
finite presentation at some stage of the diagram. -/
theorem exists_isFinitePresentation_pullback_iso_of_isLimit [IsCofiltered I]
    [∀ i, IsAffine (D.obj i)] (F : c.pt.Modules) [F.IsFinitePresentation] :
    ∃ (i : I) (Fᵢ : (D.obj i).Modules),
      Fᵢ.IsFinitePresentation ∧
        Nonempty (F ≅ (Scheme.Modules.pullback (c.π.app i)).obj Fᵢ) := by
  have : IsAffine c.pt := Scheme.isAffine_of_isLimit c hc
  have : ∀ j, IsAffine (D.op.obj j).unop := by dsimp; infer_instance
  -- `Γ(c.pt, ⊤)` is the filtered colimit of the `Γ(D.obj i, ⊤)`.
  have hΓ : IsColimit (Scheme.Γ.mapCocone c.op) := isColimitOfPreserves Scheme.Γ hc.op
  -- Transport `F` to `Spec Γ(c.pt, ⊤)` and take its global sections.
  let F' : (Spec Γ(c.pt, ⊤)).Modules := (Scheme.Modules.pullback c.pt.isoSpec.inv).obj F
  have hF' : F'.IsFinitePresentation := isFinitePresentation_pullback _ F
  have hqc : F'.IsQuasicoherent := by
    obtain ⟨σ, -⟩ := SheafOfModules.IsFinitePresentation.exists_quasicoherentData F'
    exact σ.isQuasicoherent
  have hiso : IsIso (Scheme.Modules.fromTildeΓ F') :=
    @Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent _ F' hqc
  let M : ModuleCat.{u} Γ(c.pt, ⊤) := moduleSpecΓFunctor.obj F'
  let eF' : (tilde.functor Γ(c.pt, ⊤)).obj M ≅ F' :=
    @asIso _ _ _ _ (Scheme.Modules.fromTildeΓ F') hiso
  have : ((tilde.functor Γ(c.pt, ⊤)).obj M).IsFinitePresentation :=
    (SheafOfModules.isFinitePresentation (Spec Γ(c.pt, ⊤)).ringCatSheaf).prop_of_iso eF'.symm hF'
  have hfp : Module.FinitePresentation Γ(c.pt, ⊤) M := (tilde_isFinitePresentation_iff M).mp ‹_›
  -- Descend `M` along the colimit of rings.
  obtain ⟨j, M₀, hM₀, ⟨eM⟩⟩ :=
    @Stacks.ModuleDescent.exists_extendScalars_iso_of_isColimit _ _ _ _ _ hΓ M hfp
  obtain ⟨i, rfl⟩ : ∃ i : I, j = Opposite.op i := ⟨j.unop, rfl⟩
  have : ((tilde.functor Γ(D.obj i, ⊤)).obj M₀).IsFinitePresentation :=
    (tilde_isFinitePresentation_iff M₀).mpr hM₀
  refine ⟨i, (Scheme.Modules.pullback (D.obj i).isoSpec.hom).obj
    ((tilde.functor Γ(D.obj i, ⊤)).obj M₀), isFinitePresentation_pullback _ _, ⟨?_⟩⟩
  -- Assemble the isomorphism.
  have e1 := (Scheme.Modules.pullbackComp (c.π.app i) (D.obj i).isoSpec.hom).app
    ((tilde.functor Γ(D.obj i, ⊤)).obj M₀)
  have hcomp : c.π.app i ≫ (D.obj i).isoSpec.hom =
      c.pt.isoSpec.hom ≫ Spec.map ((c.π.app i).appTop) :=
    (Scheme.isoSpec_hom_naturality (X := c.pt) (c.π.app i)).symm
  have e2 := (Scheme.Modules.pullbackCongr hcomp).app ((tilde.functor Γ(D.obj i, ⊤)).obj M₀)
  have e3 := (Scheme.Modules.pullbackComp c.pt.isoSpec.hom (Spec.map ((c.π.app i).appTop))).app
    ((tilde.functor Γ(D.obj i, ⊤)).obj M₀)
  have e4 := (Stacks.AlgebraicGeometry.SectionsColimit.tildePullbackIso
    ((c.π.app i).appTop)).app M₀
  have e5 := (Scheme.Modules.pullbackComp c.pt.isoSpec.hom c.pt.isoSpec.inv).app F ≪≫
    (Scheme.Modules.pullbackCongr c.pt.isoSpec.hom_inv_id).app F ≪≫
    (Scheme.Modules.pullbackId c.pt).app F
  exact e5.symm ≪≫ (Scheme.Modules.pullback c.pt.isoSpec.hom).mapIso
      (eF'.symm ≪≫ (tilde.functor Γ(c.pt, ⊤)).mapIso eM.symm ≪≫ e4.symm) ≪≫
    e3 ≪≫ e2.symm ≪≫ e1.symm

include hc in
/-- **Stacks Project, Tag 01ZR (1)** for a cofiltered system with affine transition morphisms
one of whose stages is affine: every sheaf of modules of finite presentation on the limit is
the pullback of one of finite presentation at some stage.  The quasi-compactness and
quasi-separatedness hypotheses of the source are not needed in this case. -/
theorem exists_isFinitePresentation_pullback_iso_of_isLimit_of_isAffine_stage [IsCofiltered I]
    [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)] (i₀ : I) [IsAffine (D.obj i₀)]
    (F : c.pt.Modules) [F.IsFinitePresentation] :
    ∃ (i : I) (Fᵢ : (D.obj i).Modules),
      Fᵢ.IsFinitePresentation ∧
        Nonempty (F ≅ (Scheme.Modules.pullback (c.π.app i)).obj Fᵢ) := by
  have : ∀ j : Over i₀, IsAffine ((Over.forget i₀ ⋙ D).obj j) := fun j =>
    isAffine_of_isAffineHom (D.map j.hom)
  obtain ⟨j, Fⱼ, hFⱼ, ⟨e⟩⟩ := exists_isFinitePresentation_pullback_iso_of_isLimit
    (D := Over.forget i₀ ⋙ D) (c := c.whisker (Over.forget i₀))
    (hc := (Functor.Initial.isLimitWhiskerEquiv (Over.forget i₀) c).symm hc) (F := F)
  exact ⟨j.left, Fⱼ, hFⱼ, ⟨e⟩⟩

end Stacks.AlgebraicGeometry.ModuleLimits

end
