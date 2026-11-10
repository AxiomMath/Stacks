module

public import Mathlib.AlgebraicGeometry.Geometrically.Irreducible
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.Topology.Sober
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.Invertible
public import StacksFrontier.AlgebraicGeometry.ComponentDegrees.Rank
public import StacksFrontier.AlgebraicGeometry.Flatness.BaseChangeTransition
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.NoetherianFibre
public import StacksFrontier.Topology.Sober.Defs

/-!
# Modules free at the generic points of fibres

For a smooth family with geometrically irreducible fibres and a finite type quasi-coherent
module on its source, this file defines the subterminal functor testing whether every fibre's
generic point has a neighbourhood on which the pulled-back module is free of a prescribed
finite rank.

## Main definitions

* `AlgebraicGeometry.FreeAtPointOfRank` expresses freeness of fixed finite rank on a
  neighbourhood of a point.
* `AlgebraicGeometry.FreeAtGenericPointsSituation` packages the standing family and module.
* `AlgebraicGeometry.FreeAtGenericPointsSituation.Condition` is the generic-point condition
  after an arbitrary base change.
* `AlgebraicGeometry.FreeAtGenericPointsSituation.freeAtGenericPointsFunctor` is the
  resulting subterminal functor.

## Main results

* `AlgebraicGeometry.FreeAtGenericPointsSituation.condition_of_hom` states stability of the
  generic-point condition under further base change.

## Implementation notes

An open neighbourhood is represented by an open subscheme, and restriction of the module is
the pullback along its canonical open immersion. Rather than choosing the unique generic
point of an irreducible fibre, the condition is imposed on every point generic for the whole
fibre; uniqueness makes this equivalent and avoids a noncanonical choice. The values of the
functor are `PLift` of the condition, hence are singletons when it holds and empty otherwise.

Base-change stability rests on two transfer lemmas for the rank: `pullback_rank` carries
finite local freeness of a fixed rank along an arbitrary pullback, and `rank_of_module_iso`
carries it along an isomorphism of modules. The first is the sheaf-theoretic statement
`Stacks.AlgebraicGeometry.ComponentDegrees.rankPullbackData` applied to the underlying
continuous map and ring-sheaf morphism; the second transports the local generating sections
along the isomorphism, which leaves their index types unchanged.

## References

* [Stacks Project, Tag 05MP](https://stacks.math.columbia.edu/tag/05MP)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- A module is free of rank `p` near `x` if its restriction to some open neighbourhood of
`x` is finite locally free of rank `p`. -/
abbrev FreeAtPointOfRank {X : Scheme.{u}} (F : X.Modules) (x : X) (p : ℕ) : Prop :=
  ∃ U : X.Opens, x ∈ U ∧
    Stacks.SheafOfModules.Invertible.IsFiniteLocallyFreeOfRank
      ((Scheme.Modules.pullback U.ι).obj F) p

/-- The standing situation of a smooth morphism with geometrically irreducible fibres and a
finite type quasi-coherent module on its source. -/
@[stacks 05MP "the situation"]
structure FreeAtGenericPointsSituation where
  /-- The base scheme. -/
  S : Scheme.{u}
  /-- The total space. -/
  X : Scheme.{u}
  /-- The smooth family. -/
  f : X ⟶ S
  /-- The family is smooth. -/
  [smooth : Smooth f]
  /-- Every fibre is geometrically irreducible. -/
  geometricallyIrreducibleFibers : ∀ s : S,
    GeometricallyIrreducible (f.fiberToSpecResidueField s)
  /-- The module on the total space. -/
  F : X.Modules
  /-- The module is quasi-coherent. -/
  [isQuasicoherent : F.IsQuasicoherent]
  /-- The module is of finite type. -/
  [isFiniteType : F.IsFiniteType]

namespace FreeAtGenericPointsSituation

attribute [instance] smooth isQuasicoherent isFiniteType

/-- The base change `X ×_S T → T` of the family in the situation. -/
noncomputable abbrev baseChangeMap (D : FreeAtGenericPointsSituation.{u}) (T : Over D.S) :
    pullback D.f T.hom ⟶ T.left :=
  pullback.snd D.f T.hom

/-- The pullback of the module to `X ×_S T`. -/
noncomputable abbrev baseChangeModule
    (D : FreeAtGenericPointsSituation.{u}) (T : Over D.S) :
    (pullback D.f T.hom).Modules :=
  (Scheme.Modules.pullback (pullback.fst D.f T.hom)).obj D.F

/-- The module pulled back to `X ×_S T` is free of rank `p` near the generic point of
every fibre over `T`. -/
@[stacks 05MP "the fibrewise condition"]
abbrev Condition (D : FreeAtGenericPointsSituation.{u}) (p : ℕ)
    (T : Over D.S) : Prop :=
  ∀ (t : T.left) (ξ : (D.baseChangeMap T).fiber t),
    IsGenericPoint ξ Set.univ →
      FreeAtPointOfRank (D.baseChangeModule T) ((D.baseChangeMap T).fiberι t ξ) p

/-- Finite local freeness of a fixed rank is stable under pullback. -/
private theorem pullback_rank
    {X Y : Scheme.{u}} (f : Y ⟶ X) (M : X.Modules) (p : ℕ)
    [h : Stacks.SheafOfModules.Invertible.IsFiniteLocallyFreeOfRank.{u, u, u} M p] :
    Stacks.SheafOfModules.Invertible.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback f).obj M) p := by
  have : (SheafOfModules.pushforward.{u} f.toRingCatSheafHom).IsRightAdjoint :=
    (Scheme.Modules.pullbackPushforwardAdjunction f).isRightAdjoint
  have h' : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} M p :=
    { exists_isFiniteLocallyFreeOfRankData := h.exists_isFiniteLocallyFreeOfRankData }
  have hres : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback f).obj M) p :=
    Stacks.AlgebraicGeometry.ComponentDegrees.rankPullbackData f.base
      f.toRingCatSheafHom M p h'
  exact { exists_isFiniteLocallyFreeOfRankData :=
    hres.exists_isFiniteLocallyFreeOfRankData }

/-- Finite local freeness of a fixed rank is invariant under an isomorphism of modules: the
local generating sections transport along the isomorphism with the same index types. -/
private theorem rank_of_module_iso
    {X : Scheme.{u}} {M N : X.Modules} (e : M ≅ N) (p : ℕ)
    [h : Stacks.SheafOfModules.Invertible.IsFiniteLocallyFreeOfRank.{u, u, u} M p] :
    Stacks.SheafOfModules.Invertible.IsFiniteLocallyFreeOfRank.{u, u, u} N p := by
  obtain ⟨q, hq, hrank⟩ := h.exists_isFiniteLocallyFreeOfRankData
  let q' : SheafOfModules.LocalGeneratorsData.{u, u, u, u} N :=
    { I := q.I
      X := q.X
      coversTop := q.coversTop
      generators i := (q.generators i).ofEpi
        ((SheafOfModules.overFunctor X.ringCatSheaf (q.X i)).mapIso e).hom }
  have hfree : q'.IsLocallyFreeData.{u, u, u, u} := by
    constructor
    intro i
    have h0 : IsIso (q.generators i).π := hq.isIso i
    have h2 : IsIso ((q.generators i).π ≫
        ((SheafOfModules.overFunctor X.ringCatSheaf (q.X i)).mapIso e).hom) := inferInstance
    exact Eq.mpr (congrArg IsIso (SheafOfModules.GeneratingSections.ofEpi_π
      (q.generators i)
      ((SheafOfModules.overFunctor X.ringCatSheaf (q.X i)).mapIso e).hom)) h2
  exact { exists_isFiniteLocallyFreeOfRankData := ⟨q', hfree, hrank⟩ }

/-- A surjective continuous map takes a generic point of the whole space to a generic point
of the whole space. -/
private theorem genericPoint_map_of_surjective
    {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) (hf : Continuous f) (hsurj : Function.Surjective f)
    {ξ : X} (hξ : IsGenericPoint ξ Set.univ) :
    IsGenericPoint (f ξ) Set.univ := by
  obtain ⟨_, hcl⟩ := (isGenericPoint_iff Set.univ ξ).mpr hξ
  apply (isGenericPoint_iff Set.univ (f ξ)).mp
  constructor
  · exact Set.mem_univ _
  · symm
    apply Set.eq_univ_iff_forall.mpr
    intro y
    obtain ⟨x, rfl⟩ := hsurj y
    have hx : x ∈ closure {ξ} := by rw [← hcl]; exact Set.mem_univ x
    have himage := image_closure_subset_closure_image hf (s := {ξ})
    have hy : f x ∈ closure (f '' ({ξ} : Set X)) := himage ⟨x, hx, rfl⟩
    simpa using hy

/-- Comparison of the base-changed modules along a transition morphism of base changes. -/
private noncomputable def baseChangeModuleIso
    (D : FreeAtGenericPointsSituation.{u}) {T T' : Over D.S}
    (φ : pullback D.f T'.hom ⟶ pullback D.f T.hom)
    (hφ : φ ≫ pullback.fst D.f T.hom = pullback.fst D.f T'.hom) :
    (Scheme.Modules.pullback φ).obj (D.baseChangeModule T) ≅ D.baseChangeModule T' := by
  let hobj : ((Scheme.Modules.pullback (φ ≫ pullback.fst D.f T.hom)).obj D.F) =
      ((Scheme.Modules.pullback (pullback.fst D.f T'.hom)).obj D.F) :=
    congrArg (fun f : pullback D.f T'.hom ⟶ D.X =>
      (Scheme.Modules.pullback f).obj D.F) hφ
  exact (Scheme.Modules.pullbackComp φ (pullback.fst D.f T.hom)).app D.F ≪≫
    eqToIso hobj

/-- The fibrewise generic-point condition is preserved by a further base change. -/
@[stacks 05MP "base-change stability"]
theorem condition_of_hom (D : FreeAtGenericPointsSituation.{u}) (p : ℕ)
    {T T' : Over D.S} (g : T' ⟶ T) (h : D.Condition p T) :
    D.Condition p T' := by
  classical
  intro t' ξ' hξ'
  let t := g.left t'
  let ρ : Spec (T'.left.residueField t') ⟶ Spec (T.left.residueField t) :=
    Spec.map (Scheme.Hom.residueFieldMap g.left t')
  let φ : pullback D.f T'.hom ⟶ pullback D.f T.hom := Stacks.BaseChange.transition D.f g
  let ψ : (D.baseChangeMap T').fiber t' ⟶ (D.baseChangeMap T).fiber t :=
    pullback.map _ _ _ _ φ ρ g.left (Stacks.BaseChange.transition_isPullback D.f g).w.symm
      (Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField g.left t').symm
  have hfib := isPullback_fiberToSpecResidueField_of_isPullback
    (Stacks.BaseChange.transition_isPullback D.f g) t'
  have hρ : Surjective ρ := by
    rw [surjective_iff]
    intro z
    have : Unique (PrimeSpectrum (T'.left.residueField t')) := PrimeSpectrum.instUnique
    have : Unique (PrimeSpectrum (T.left.residueField t)) := PrimeSpectrum.instUnique
    exact ⟨default, Subsingleton.elim _ _⟩
  have hψ : Surjective ψ := MorphismProperty.of_isPullback hfib.flip hρ
  have hξ : IsGenericPoint (ψ ξ') Set.univ :=
    genericPoint_map_of_surjective ψ ψ.continuous hψ.surj hξ'
  have hpoint : φ ((D.baseChangeMap T').fiberι t' ξ') =
      (D.baseChangeMap T).fiberι t (ψ ξ') := by
    have hc : ψ ≫ (D.baseChangeMap T).fiberι t =
        (D.baseChangeMap T').fiberι t' ≫ φ := by
      dsimp [ψ, φ, Scheme.Hom.fiberι, Scheme.Hom.fiber, pullback.map]
      simp only [pullback.lift_fst]
    simpa using
      (congrArg (fun k : (D.baseChangeMap T').fiber t' ⟶ pullback D.f T.hom => k ξ') hc).symm
  obtain ⟨U, hU, hRank⟩ := h t (ψ ξ') hξ
  let V : (pullback D.f T'.hom).Opens := φ ⁻¹ᵁ U
  have hV : (D.baseChangeMap T').fiberι t' ξ' ∈ V := by
    change φ ((D.baseChangeMap T').fiberι t' ξ') ∈ U
    rw [hpoint]
    exact hU
  let k : V.toScheme ⟶ U.toScheme := φ.resLE U V le_rfl
  have hk : k ≫ U.ι = V.ι ≫ φ := Scheme.Hom.resLE_comp_ι φ le_rfl
  have : IsOpenImmersion U.ι := inferInstance
  have : IsOpenImmersion V.ι := inferInstance
  have hLocal : Stacks.SheafOfModules.Invertible.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback k).obj ((Scheme.Modules.pullback U.ι).obj
        (D.baseChangeModule T))) p :=
    pullback_rank k _ p
  have hfst : φ ≫ pullback.fst D.f T.hom = pullback.fst D.f T'.hom :=
    Stacks.BaseChange.transition_comp_fst D.f g
  let eTotal := baseChangeModuleIso D φ hfst
  have hobj : ((Scheme.Modules.pullback (V.ι ≫ φ)).obj (D.baseChangeModule T)) =
      ((Scheme.Modules.pullback (k ≫ U.ι)).obj (D.baseChangeModule T)) :=
    congrArg (fun f : V.toScheme ⟶ pullback D.f T.hom =>
      (Scheme.Modules.pullback f).obj (D.baseChangeModule T)) hk.symm
  let eRestrict : (Scheme.Modules.pullback V.ι).obj (D.baseChangeModule T') ≅
      (Scheme.Modules.pullback k).obj ((Scheme.Modules.pullback U.ι).obj
        (D.baseChangeModule T)) :=
    (Scheme.Modules.pullback V.ι).mapIso eTotal.symm ≪≫
      (Scheme.Modules.pullbackComp V.ι φ).app (D.baseChangeModule T) ≪≫
      eqToIso hobj ≪≫
      ((Scheme.Modules.pullbackComp k U.ι).app (D.baseChangeModule T)).symm
  exact ⟨V, hV, rank_of_module_iso eRestrict.symm p⟩

/-- The subterminal set-valued functor recording whether the pulled-back module is free of
rank `p` near the generic point of every fibre. -/
@[stacks 05MP "the functor"]
noncomputable def freeAtGenericPointsFunctor
    (D : FreeAtGenericPointsSituation.{u}) (p : ℕ) :
    (Over D.S)ᵒᵖ ⥤ Type u where
  obj T := ULift.{u} (PLift (D.Condition p T.unop))
  map {T T'} g := ↾(fun h : ULift.{u} (PLift (D.Condition p T.unop)) ↦
    ⟨⟨D.condition_of_hom p g.unop h.down.down⟩⟩)
  map_id := by intros; rfl
  map_comp := by intros; rfl

end FreeAtGenericPointsSituation

end AlgebraicGeometry
