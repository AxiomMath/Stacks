module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.Etale.NeighborhoodStalkFiber
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.FlatLocus
public import StacksFrontier.AlgebraicGeometry.Morphisms.Flat.IsoTransport
public import StacksFrontier.AlgebraicGeometry.Morphisms.Flat.OpenLocus
public import StacksFrontier.AlgebraicGeometry.Morphisms.FlatMorphisms.BaseChange
public import StacksFrontier.AlgebraicGeometry.Morphisms.FlatMorphisms.PullbackFlatness
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FinitePresentationPullback

/-!
# Flatness is free once finite presentation is known, after an elementary étale neighbourhood

Stacks Tag 05I5 says: for `f : X ⟶ S` locally of finite presentation and `F` a finite type
quasi-coherent `𝒪_X`-module which is flat over `S` at `x`, there are an elementary étale
neighbourhood `U` of `(S, f x)` and an open `V ⊆ X ×_S Spec 𝒪_{U, u}` containing the unique
point over `x` such that the pullback of `F` to `V` is of finite presentation *and* flat over
`Spec 𝒪_{U, u}`.

This file shows that the flatness half of that conclusion is a formal consequence of the
finite-presentation half. Suppose one is handed an open `W` of a base change of `f` which
contains a point over `x` and on which the pullback of `F` is of finite presentation. Then:

* the pullback of `F` is flat over the new base *at* that point, because flatness over the base
  at a point is preserved by base change (Tag 01U8,
  `AlgebraicGeometry.modulePullback_isFlatOverAt`);
* the locus inside `W` where the pullback of `F` is flat over the new base is open, because the
  pullback is of finite presentation there and the new structure morphism is locally of finite
  presentation (Tag 0399, `AlgebraicGeometry.isOpen_setOf_flatOverAt`);
* shrinking `W` to that locus keeps finite presentation, because pullback preserves finite
  presentation (Tag 01BQ, `Stacks.SheafOfModules.modulePullback_isFinitePresentation`), and
  turns pointwise flatness into flatness on the whole open (Tag 02JZ,
  `AlgebraicGeometry.isFlatOverAt_iff_modulePullback_isFlatOverAt`).

Combining this with the uniqueness of the point over `x`
(`AlgebraicGeometry.EtaleNeighborhood.preimage_fst_eq_singleton_of_apply_eq`) leaves exactly one
obligation for Tag 05I5: produce an elementary étale neighbourhood together with an open of the
base change to its local ring which contains a point over `x` and on which the pullback of `F`
is of finite presentation. That obligation is the hypothesis `hfp` of the second main result
below.

## Main results

* `AlgebraicGeometry.exists_open_isFinitePresentation_isFlatOver_of_isFinitePresentation`: in an
  arbitrary base change square, an open on which the pullback of a flat-at-`x` quasi-coherent
  module is of finite presentation can be shrunk, keeping a point over `x`, so that the pullback
  becomes flat over the new base on all of it.
* `exists_elementaryEtaleNeighborhood_isFinitePresentation_isFlatOver_of_isFinitePresentation`
  is the conclusion of Tag 05I5, assuming only its finite-presentation half.
* `AlgebraicGeometry.exists_elementaryEtaleNeighborhood_isFlatOver_of_isFinitePresentation` is
  Tag 05I5 itself for a module which is already of finite presentation, with no hypothesis left:
  there the finite-presentation half is immediate, with the trivial neighbourhood `𝟙 S`.

## Implementation notes

The base change is presented by an arbitrary pullback square `IsPullback p q f b` rather than by
Mathlib's chosen pullback object, so that the two projections are variables and the goals stay
small; Tag 05I5 is then the instance `IsPullback.of_hasPullback`.

Flatness over the base at a point is not visibly invariant under an isomorphism of modules:
`AlgebraicGeometry.IsFlatOverAt` is flatness of the module stalk, and an isomorphism of sheaves
of modules only induces an isomorphism of the underlying abelian-group stalks.
`AlgebraicGeometry.isFlatOverAt_iff_of_moduleIso` upgrades that to a linear equivalence, which
is what is needed to move flatness across the comparison isomorphism
`AlgebraicGeometry.Scheme.Modules.pullbackComp` between a pullback along a composite and the
composite of pullbacks.

## References

* [Stacks Project, Tag 05I5](https://stacks.math.columbia.edu/tag/05I5)
* [Stacks Project, Tag 0399](https://stacks.math.columbia.edu/tag/0399)
* [Stacks Project, Tag 01BQ](https://stacks.math.columbia.edu/tag/01BQ)
* [Stacks Project, Tag 01U8](https://stacks.math.columbia.edu/tag/01U8)
* [Stacks Project, Tag 02JZ](https://stacks.math.columbia.edu/tag/02JZ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open RingedSpaceModuleAdjunction

universe u

namespace AlgebraicGeometry

section Helpers

variable {X S : Scheme.{u}}

/-- A sheaf of modules of finite presentation on a scheme is quasi-coherent.

Mathlib has this as an instance for a sheaf of modules on a site, but the universe of the
quasi-coherent data is a parameter of both classes and is not determined by the goal, so the
instance is not found by `inferInstance` here. -/
private theorem isQuasicoherent_of_isFinitePresentation (G : X.Modules)
    (h : G.IsFinitePresentation) : G.IsQuasicoherent := by
  obtain ⟨σ, -⟩ := SheafOfModules.IsFinitePresentation.exists_quasicoherentData G (self := h)
  exact σ.isQuasicoherent

end Helpers

/-- Shrinking an open on which the pullback of a module is of finite presentation to the locus
where it is also flat over the new base.

The square `IsPullback p q f b` presents `P` as a base change of `f : X ⟶ S` along
`b : T ⟶ S`. If `F` is quasi-coherent and flat over `S` at `x`, and `W` is an open of `P`
carrying a point over `x` on which the pullback of `F` along `W ⟶ X` is of finite presentation,
then `W` contains an open `V`, still carrying a point over `x`, on which the pullback of `F` is
of finite presentation *and* flat over `T`. -/
theorem exists_open_isFinitePresentation_isFlatOver_of_isFinitePresentation
    {X S T P : Scheme.{u}} {f : X ⟶ S} {b : T ⟶ S} {p : P ⟶ X} {q : P ⟶ T}
    [LocallyOfFinitePresentation f] (hpb : IsPullback p q f b)
    (F : X.Modules) [hFqc : F.IsQuasicoherent] (x : X)
    (hF : IsFlatOverAt f.toLRSHom.toShHom F x)
    (W : P.Opens) (w : W) (hwx : p (W.ι w) = x)
    (hWfp : ((Scheme.Modules.pullback (W.ι ≫ p)).obj F).IsFinitePresentation) :
    ∃ (V : P.Opens) (v : V), p (V.ι v) = x ∧
      ((Scheme.Modules.pullback (V.ι ≫ p)).obj F).IsFinitePresentation ∧
      IsFlatOver (V.ι ≫ q).toLRSHom.toShHom
        ((Scheme.Modules.pullback (V.ι ≫ p)).obj F) := by
  classical
  -- the pullback of `F` to `W`
  set G : W.toScheme.Modules := (Scheme.Modules.pullback (W.ι ≫ p)).obj F with hG
  have hGfp : G.IsFinitePresentation := hWfp
  have hGqc : G.IsQuasicoherent := isQuasicoherent_of_isFinitePresentation G hGfp
  -- the new structure morphism is locally of finite presentation
  have hq : LocallyOfFinitePresentation q :=
    MorphismProperty.of_isPullback (P := @LocallyOfFinitePresentation) hpb inferInstance
  have hWq : LocallyOfFinitePresentation (W.ι ≫ q) :=
    MorphismProperty.comp_mem @LocallyOfFinitePresentation _ _ inferInstance hq
  -- `G` is flat over `T` at `w`, by base change of the flatness of `F` over `S` at `x`
  have : SheafOfModules.IsQuasicoherent (R := structureSheafRing X.toRingedSpace) F := hFqc
  have hbase : IsFlatOverAt q.toLRSHom.toShHom
      ((modulePullback p.toLRSHom.toShHom).obj F) (W.ι w) :=
    modulePullback_isFlatOverAt hpb F (W.ι w) (by rw [hwx]; exact hF)
  have hcomp : IsFlatOverAt (W.ι ≫ q).toLRSHom.toShHom
      ((Scheme.Modules.pullback W.ι).obj
        ((Scheme.Modules.pullback p).obj F)) w :=
    (isFlatOverAt_iff_modulePullback_isFlatOverAt W.ι q _ w (Flat.stalkMap W.ι w)).mp hbase
  have hwflat : IsFlatOverAt (W.ι ≫ q).toLRSHom.toShHom G w := by
    rw [hG]
    exact (isFlatOverAt_iff_of_moduleIso (W.ι ≫ q).toLRSHom.toShHom
      ((Scheme.Modules.pullbackComp W.ι p).app F) w).mp hcomp
  -- the flat locus inside `W` is open
  have hopen : IsOpen {t : W.toScheme | IsFlatOverAt (W.ι ≫ q).toLRSHom.toShHom G t} :=
    isOpen_setOf_flatOverAt (W.ι ≫ q) G
  set Ω : W.toScheme.Opens :=
    ⟨{t : W.toScheme | IsFlatOverAt (W.ι ≫ q).toLRSHom.toShHom G t}, hopen⟩ with hΩ
  have hwΩ : w ∈ Ω := hwflat
  -- the corresponding open of `P`, and the morphism from it to `W`
  set V : P.Opens := W.ι ''ᵁ Ω with hV
  have hVW : V ≤ W := Scheme.Opens.ι_image_le W Ω
  set i : V.toScheme ⟶ W.toScheme := P.homOfLE hVW with hi
  have hiι : i ≫ W.ι = V.ι := P.homOfLE_ι hVW
  have hfac {Y : Scheme.{u}} (r : P ⟶ Y) : V.ι ≫ r = i ≫ (W.ι ≫ r) := by
    rw [← Category.assoc, hiι]
  -- every point of `V` maps into the flat locus `Ω`
  have hmemΩ : ∀ v : V.toScheme, i v ∈ Ω := by
    rw [Scheme.Opens.forall_toScheme]
    intro z hz
    have hz' := hz
    rw [hV] at hz'
    obtain ⟨t, htΩ, hteq⟩ := hz'
    have hieq : i ⟨z, hz⟩ = t := by
      rw [hi, Scheme.homOfLE_apply' hVW z hz]
      exact (Subtype.ext (by exact hteq)).symm
    rw [hieq]
    exact htΩ
  -- the module on `V`
  have hVmod : (Scheme.Modules.pullback (V.ι ≫ p)).obj F ≅
      (Scheme.Modules.pullback i).obj G := by
    rw [hfac p, hG]
    exact ((Scheme.Modules.pullbackComp i (W.ι ≫ p)).app F).symm
  refine ⟨V, ⟨W.ι w, ⟨w, hwΩ, rfl⟩⟩, ?_, ?_, ?_⟩
  · show p (V.ι _) = x
    rw [show (V.ι ⟨W.ι w, ⟨w, hwΩ, rfl⟩⟩ : P) = W.ι w from rfl]
    exact hwx
  · refine (SheafOfModules.isFinitePresentation V.toScheme.ringCatSheaf).prop_of_iso
      hVmod.symm ?_
    exact @Stacks.SheafOfModules.modulePullback_isFinitePresentation _ _
      i.toLRSHom.toShHom G hGfp
  · intro v
    rw [(isFlatOverAt_iff_of_moduleIso (V.ι ≫ q).toLRSHom.toShHom hVmod v), hfac q]
    exact (isFlatOverAt_iff_modulePullback_isFlatOverAt i (W.ι ≫ q) G v
      (Flat.stalkMap i v)).mp (hmemΩ v)

/-- **Stacks Project, Tag 05I5, granted its finite-presentation half.** Let `f : X ⟶ S` be
locally of finite presentation and let `F` be a finite type quasi-coherent `𝒪_X`-module which is
flat over `S` at `x`. Assume that after some elementary étale neighbourhood `U` of `(S, f x)` the
pullback of `F` to the base change `X ×_S Spec 𝒪_{U, u}` is of finite presentation on an open
carrying a point over `x`. Then the full conclusion of Tag 05I5 holds: the open may be taken to
contain the unique point of `X ×_S Spec 𝒪_{U, u}` over `x`, and on it the pullback of `F` is of
finite presentation *and* flat over `Spec 𝒪_{U, u}`. -/
theorem
    exists_elementaryEtaleNeighborhood_isFinitePresentation_isFlatOver_of_isFinitePresentation
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFinitePresentation f]
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType] (x : X)
    (hF : IsFlatOverAt (LocallyRingedSpace.forgetToSheafedSpace.map f.toLRSHom) F x)
    (hfp : ∃ (U : EtaleNeighborhood S (f x)) (_ : U.IsElementary),
      let b : Spec (U.scheme.presheaf.stalk U.point) ⟶ S :=
        U.scheme.fromSpecStalk U.point ≫ U.toBase
      ∃ (W : (pullback f b).Opens) (w : W),
        pullback.fst f b (W.ι w) = x ∧
        ((Scheme.Modules.pullback (W.ι ≫ pullback.fst f b)).obj F).IsFinitePresentation) :
    ∃ (U : EtaleNeighborhood S (f x)) (_ : U.IsElementary),
      let b : Spec (U.scheme.presheaf.stalk U.point) ⟶ S :=
        U.scheme.fromSpecStalk U.point ≫ U.toBase
      ∃ (V : (pullback f b).Opens) (v : V),
        pullback.fst f b ⁻¹' {x} = {V.ι v} ∧
        ((Scheme.Modules.pullback (V.ι ≫ pullback.fst f b)).obj F).IsFinitePresentation ∧
        IsFlatOver
          (LocallyRingedSpace.forgetToSheafedSpace.map
            (V.ι ≫ pullback.snd f b).toLRSHom)
          ((Scheme.Modules.pullback (V.ι ≫ pullback.fst f b)).obj F) := by
  obtain ⟨U, hU, W, w, hwx, hWfp⟩ := hfp
  obtain ⟨V, v, hvx, hVfp, hVflat⟩ :=
    exists_open_isFinitePresentation_isFlatOver_of_isFinitePresentation
      (IsPullback.of_hasPullback f (U.scheme.fromSpecStalk U.point ≫ U.toBase))
      F x hF W w hwx hWfp
  exact ⟨U, hU, V, v,
    EtaleNeighborhood.preimage_fst_eq_singleton_of_apply_eq f x U hU hvx, hVfp, hVflat⟩

/-- **Stacks Project, Tag 05I5 for a module which is already of finite presentation.** For a
quasi-coherent `𝒪_X`-module of finite presentation which is flat over `S` at `x`, the conclusion
of Tag 05I5 holds unconditionally, and with the trivial elementary étale neighbourhood `𝟙 S`:
the whole base change `X ×_S Spec 𝒪_{S, f x}` carries the pullback of `F` as a module of finite
presentation, so the previous theorem shrinks it to an open on which that pullback is also flat.

The content of Tag 05I5 is exactly that a module of *finite type* can be brought into this
situation after an elementary étale change of the base.

The finite type hypothesis is redundant here, being implied by finite presentation; it is kept
as a hypothesis only because Mathlib's instance deriving it is not found by instance search, the
universe of the local generating data being a parameter of both classes. -/
theorem exists_elementaryEtaleNeighborhood_isFlatOver_of_isFinitePresentation
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFinitePresentation f]
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType] [hFfp : F.IsFinitePresentation]
    (x : X)
    (hF : IsFlatOverAt (LocallyRingedSpace.forgetToSheafedSpace.map f.toLRSHom) F x) :
    ∃ (U : EtaleNeighborhood S (f x)) (_ : U.IsElementary),
      let b : Spec (U.scheme.presheaf.stalk U.point) ⟶ S :=
        U.scheme.fromSpecStalk U.point ≫ U.toBase
      ∃ (V : (pullback f b).Opens) (v : V),
        pullback.fst f b ⁻¹' {x} = {V.ι v} ∧
        ((Scheme.Modules.pullback (V.ι ≫ pullback.fst f b)).obj F).IsFinitePresentation ∧
        IsFlatOver
          (LocallyRingedSpace.forgetToSheafedSpace.map
            (V.ι ≫ pullback.snd f b).toLRSHom)
          ((Scheme.Modules.pullback (V.ι ≫ pullback.fst f b)).obj F) := by
  refine exists_elementaryEtaleNeighborhood_isFinitePresentation_isFlatOver_of_isFinitePresentation
    f F x hF ?_
  refine ⟨EtaleNeighborhood.self S (f x), EtaleNeighborhood.isElementary_self S (f x), ?_⟩
  obtain ⟨v, hv⟩ := EtaleNeighborhood.exists_preimage_fst_eq_singleton f x
    (EtaleNeighborhood.self S (f x)) (EtaleNeighborhood.isElementary_self S (f x))
  have hvx : pullback.fst f ((EtaleNeighborhood.self S (f x)).scheme.fromSpecStalk
      (EtaleNeighborhood.self S (f x)).point ≫
        (EtaleNeighborhood.self S (f x)).toBase) v = x := by
    have : v ∈ ({v} : Set _) := rfl
    rw [← hv] at this
    exact this
  exact ⟨⊤, ⟨v, trivial⟩, hvx, @Stacks.SheafOfModules.modulePullback_isFinitePresentation _ _ _
    F hFfp⟩

end AlgebraicGeometry

end
