module

public import StacksFrontier.AlgebraicGeometry.Morphisms.DescentLocusClosed0BF0
public import StacksFrontier.AlgebraicGeometry.Morphisms.DescentLocusLocality
public import StacksFrontier.AlgebraicGeometry.ProjectionFormula.LocalityRingedSpace
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.RankFromBasis
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.Pullback
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.Sheaf
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.SchemeRestriction
public import StacksFrontier.AlgebraicGeometry.Perfect.BottomRankStratum

/-!
# Freeness of a module along the base, and the descent condition along a base change

Let `f : X ⟶ S` be a morphism of schemes and `ℰ` a sheaf of modules on `X`. A sheaf `ℰ` is *free of
rank `n` along* `g : T ⟶ S` when its pullback to `X_T = X ×_S T` is the free module of rank `n`.
If `ℰ` descends along `g` (`AlgebraicGeometry.DescendsFromBase f ℰ g`: the pullback of `ℰ` to
`X_T` comes from a finite locally free `𝒪_T`-module), it is free of finite rank along a
neighbourhood of every point of `T`. For `φ : U ⟶ S`, the descent condition along `a ≫ φ` is the
descent condition along `a` for the base change `X ×_S U ⟶ U`.

These are inputs of the proof of [Stacks, Tag 0BF2](https://stacks.math.columbia.edu/tag/0BF2).

## Main results

* `AlgebraicGeometry.IsFreeAlong`: freeness of rank `n` along a morphism `T ⟶ S`, inherited by
  precomposites (`AlgebraicGeometry.IsFreeAlong.comp`).
* `AlgebraicGeometry.DescendsFromBase.exists_isFreeAlong`: along a morphism where `ℰ` descends,
  it is free of finite rank over a neighbourhood of every point of the test scheme.
* `AlgebraicGeometry.descendsFromBase_comp_iff`: the descent condition along `a ≫ φ` is the
  descent condition along `a` for the base change of `f` along `φ`.

## References

* [Stacks Project, Tag 0BDP](https://stacks.math.columbia.edu/tag/0BDP)
* [Stacks Project, Tag 0BF2](https://stacks.math.columbia.edu/tag/0BF2)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.Cohomology.HigherDirectImage Stacks.AffineProjectionFormula Stacks.RingedSpace

universe u

namespace AlgebraicGeometry

open RingedSpaceModuleAdjunction
open AlgebraicGeometry.BottomRankStratum (comp_toLRSHom_toShHom)

variable {X S : Scheme.{u}} (f : X ⟶ S)
  (E : SheafOfModules.{u} (structureSheafRing X.toRingedSpace))

/-- The morphism `X_{T'} ⟶ X_T` of base changes induced by `k : T' ⟶ T`. -/
noncomputable abbrev descentBaseChangeMap {T T' : Scheme.{u}} (g : T ⟶ S) (k : T' ⟶ T) :
    pullback f (k ≫ g) ⟶ pullback f g :=
  pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ k)
    (by rw [pullback.condition, Category.assoc])

/-- The pullback of `ℰ` to `X_{T'}` is the pullback along `X_{T'} ⟶ X_T` of its pullback to
`X_T`. -/
noncomputable def modulePullbackFstCompIso {T T' : Scheme.{u}} (g : T ⟶ S) (k : T' ⟶ T) :
    (modulePullback (pullback.fst f (k ≫ g)).toLRSHom.toShHom).obj E ≅
      (modulePullback (descentBaseChangeMap f g k).toLRSHom.toShHom).obj
        ((modulePullback (pullback.fst f g).toLRSHom.toShHom).obj E) :=
  (modulePullbackCongr (by rw [← comp_toLRSHom_toShHom, pullback.lift_fst])).app E ≪≫
    (modulePullbackComp (descentBaseChangeMap f g k).toLRSHom.toShHom
      (pullback.fst f g).toLRSHom.toShHom).app E

/-- The pullback to `X_{T'}` of the pullback `k^*N` of a module on `T` is the pullback along
`X_{T'} ⟶ X_T` of the pullback of `N` to `X_T`. -/
noncomputable def modulePullbackSndCompIso {T T' : Scheme.{u}} (g : T ⟶ S) (k : T' ⟶ T)
    (N : SheafOfModules.{u} (structureSheafRing T.toRingedSpace)) :
    (modulePullback (pullback.snd f (k ≫ g)).toLRSHom.toShHom).obj
        ((modulePullback k.toLRSHom.toShHom).obj N) ≅
      (modulePullback (descentBaseChangeMap f g k).toLRSHom.toShHom).obj
        ((modulePullback (pullback.snd f g).toLRSHom.toShHom).obj N) :=
  ((modulePullbackComp (pullback.snd f (k ≫ g)).toLRSHom.toShHom
      k.toLRSHom.toShHom).app N).symm ≪≫
    (modulePullbackCongr (by rw [← comp_toLRSHom_toShHom, ← comp_toLRSHom_toShHom,
      pullback.lift_snd])).app N ≪≫
    (modulePullbackComp (descentBaseChangeMap f g k).toLRSHom.toShHom
      (pullback.snd f g).toLRSHom.toShHom).app N

/-- `ℰ` is *free of rank `n` along* `g : T ⟶ S` when its pullback to `X_T` is the free module of
rank `n`. -/
def IsFreeAlong {T : Scheme.{u}} (g : T ⟶ S) (n : ℕ) : Prop :=
  Nonempty ((modulePullback (pullback.fst f g).toLRSHom.toShHom).obj E ≅
    SheafOfModules.free (R := structureSheafRing (pullback f g).toRingedSpace)
      (ULift.{u} (Fin n)))

/-- Freeness along `g` is inherited by every precomposite `k ≫ g`. -/
theorem IsFreeAlong.comp {T T' : Scheme.{u}} {g : T ⟶ S} {n : ℕ} (h : IsFreeAlong f E g n)
    (k : T' ⟶ T) : IsFreeAlong f E (k ≫ g) n :=
  ⟨modulePullbackFstCompIso f E g k ≪≫
    (modulePullback (descentBaseChangeMap f g k).toLRSHom.toShHom).mapIso h.some ≪≫
    modulePullbackObjFreeIso _ _⟩

/-- **A descended module is locally free along the base.** If `ℰ` descends along `g : T ⟶ S`,
then every point `t` of `T` has an open neighbourhood `V` along which `ℰ` is free of some finite
rank: the descended module is free of finite rank on a neighbourhood of `t`, and so is its
pullback to `X_V`. -/
theorem DescendsFromBase.exists_isFreeAlong {T : Scheme.{u}} {g : T ⟶ S}
    (h : DescendsFromBase f E g) (t : T) :
    ∃ (V : T.Opens) (_ : t ∈ V) (n : ℕ), IsFreeAlong f E (V.ι ≫ g) n := by
  obtain ⟨N, hN, ⟨e⟩⟩ := h
  obtain ⟨V₀, hV', I, hI, ⟨eN⟩⟩ :=
    @Stacks.AffineProjectionFormula.exists_moduleRestriction_iso_free_of_isFiniteLocallyFree
      T.toRingedSpace N hN t
  let V' : T.Opens := V₀
  let eI : SheafOfModules.free (R := structureSheafRing (restrictToOpen
      T.toRingedSpace V')) I ≅
      SheafOfModules.free (ULift.{u} (Fin (Nat.card I))) :=
    SheafOfModules.freeFunctor.mapIso
      (Equiv.toIso ((Finite.equivFin I).trans Equiv.ulift.symm))
  have hι : V'.ι.toLRSHom.toShHom = openSubspaceInclusion T.toRingedSpace V' := rfl
  exact ⟨V', hV', Nat.card I,
    ⟨modulePullbackFstCompIso f E g V'.ι ≪≫
      (modulePullback (descentBaseChangeMap f g V'.ι).toLRSHom.toShHom).mapIso e.symm ≪≫
      (modulePullbackSndCompIso f g V'.ι N).symm ≪≫
      (modulePullback (pullback.snd f (V'.ι ≫ g)).toLRSHom.toShHom).mapIso
        ((modulePullbackCongr hι).app N ≪≫ ((moduleRestrictionIsoPullback _ _).app N).symm ≪≫
          eN ≪≫ eI) ≪≫ modulePullbackObjFreeIso _ _⟩⟩

/-- **The descent condition along a base change of the family.** For `φ : U ⟶ S` and
`a : T ⟶ U`, `ℰ` descends along `a ≫ φ` for `f` exactly when its pullback to `X ×_S U` descends
along `a` for the base change `X ×_S U ⟶ U`: both base changes of `X` to `T` are identified by
`pullbackLeftPullbackSndIso`. -/
theorem descendsFromBase_comp_iff {U T : Scheme.{u}} (φ : U ⟶ S) (a : T ⟶ U) :
    DescendsFromBase f E (a ≫ φ) ↔
      DescendsFromBase (pullback.snd f φ)
        ((modulePullback (pullback.fst f φ).toLRSHom.toShHom).obj E) a := by
  open BottomRankStratum in
  let ψ := pullbackLeftPullbackSndIso f φ a
  have hfst : ψ.hom ≫ pullback.fst f (a ≫ φ) =
      pullback.fst (pullback.snd f φ) a ≫ pullback.fst f φ :=
    pullbackLeftPullbackSndIso_hom_fst f φ a
  have hsnd : ψ.hom ≫ pullback.snd f (a ≫ φ) = pullback.snd (pullback.snd f φ) a :=
    pullbackLeftPullbackSndIso_hom_snd f φ a
  constructor
  · rintro ⟨N, hN, ⟨e⟩⟩
    exact ⟨N, hN, ⟨(modulePullbackCongr (by rw [← hsnd, comp_toLRSHom_toShHom])).app N ≪≫
      (modulePullbackComp _ _).app N ≪≫ (modulePullback _).mapIso e ≪≫
      ((modulePullbackComp _ _).app E).symm ≪≫
      (modulePullbackCongr (by rw [← comp_toLRSHom_toShHom, hfst,
        comp_toLRSHom_toShHom])).app E ≪≫ (modulePullbackComp _ _).app E⟩⟩
  · rintro ⟨N, hN, ⟨e⟩⟩
    exact ⟨N, hN, ⟨(modulePullbackCongr
      (by rw [(Iso.eq_inv_comp ψ).mpr hsnd, comp_toLRSHom_toShHom])).app N ≪≫
      (modulePullbackComp _ _).app N ≪≫ (modulePullback _).mapIso e ≪≫
      (modulePullback _).mapIso ((modulePullbackComp _ _).app E).symm ≪≫
      ((modulePullbackComp _ _).app E).symm ≪≫
      (modulePullbackCongr (by rw [(Iso.eq_inv_comp ψ).mpr hfst,
        comp_toLRSHom_toShHom, comp_toLRSHom_toShHom])).app E⟩⟩

end AlgebraicGeometry

end
