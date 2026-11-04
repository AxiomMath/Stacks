module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ConstantSheafHom
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ConstantSheafIsoDescent
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocallyConstantSerreClass
public import StacksFrontier.AlgebraicGeometry.ProEtale.Constructible.Stratification
public import StacksFrontier.AlgebraicGeometry.ProEtale.ConstructibleSheaves
public import StacksFrontier.AlgebraicGeometry.Spaces.ProetaleComparison
public import StacksFrontier.CategoryTheory.Sites.ConstantSheaf.FinalFunctor

/-!
# Constructible constant sheaves on the pro-étale site

Let `X` be a nonempty scheme and `Λ` a Noetherian ring. If the constant sheaf `\underline{M}` of a
`Λ`-module `M` on `X_proét` is constructible, then `M` is a finite `Λ`-module.

Indeed, a point of `X` lies on a stratum `Z` of a constructible stratification of an affine
neighbourhood along which the inverse image of `\underline{M}` is locally constant of finite type.
That inverse image is the constant sheaf `\underline{M}` on `Z_proét`, pro-étale base change
being final, and over a nonempty member of a trivializing covering of `Z` the constant sheaf of
`M` is the constant sheaf of a finite module; so `M` is finite.

## Main results

* `AlgebraicGeometry.Scheme.ProEt.exists_mem_range_of_mem_topology`: a covering sieve of an
  object of the small pro-étale site is jointly surjective.
* `AlgebraicGeometry.Scheme.ProEt.bot_notMem_topology_of_nonempty`: the empty sieve does not
  cover an object with a point.
* `AlgebraicGeometry.ProEtale.isClosedUnderIsomorphisms_isConstructibleModuleSheaf'`:
  constructibility is invariant under isomorphism.
* `AlgebraicGeometry.ProEtale.proetaleModuleInverseImageConstantSheafIso`: inverse image of a
  constant sheaf is constant.
* `AlgebraicGeometry.ProEtale.finite_of_isConstructibleModuleSheaf'_constantSheaf`: the value of a
  constructible constant sheaf on a nonempty scheme is finite.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v w

namespace AlgebraicGeometry

namespace Scheme.ProEt

variable {X : Scheme.{u}}

/-- A covering sieve of an object of the small pro-étale site is jointly surjective on underlying
schemes. -/
theorem exists_mem_range_of_mem_topology {U : X.ProEt} {S : Sieve U}
    (hS : S ∈ Scheme.ProEt.topology X U) (x : U.left) :
    ∃ (V : X.ProEt) (g : V ⟶ U), S g ∧ x ∈ Set.range g.left := by
  let : (Scheme.ProEt.precoverage X).IsStableUnderComposition := by
    dsimp [Scheme.ProEt.precoverage]; infer_instance
  let : (Scheme.ProEt.precoverage X).IsStableUnderBaseChange := by
    dsimp [Scheme.ProEt.precoverage]; infer_instance
  let : (Scheme.ProEt.precoverage X).HasIsos := by
    dsimp [Scheme.ProEt.precoverage]; infer_instance
  obtain ⟨R, hR, hRS⟩ := Precoverage.mem_toGrothendieck_iff_of_isStableUnderComposition.mp hS
  let q := Scheme.ProEt.forget X ⋙ Over.forget X
  have hR' : Presieve.map q R ∈ Scheme.precoverage @WeaklyEtale U.left :=
    Scheme.propQCPrecoverage_le_precoverage _ hR
  obtain ⟨Y, g, hg, hx⟩ :=
    (Presieve.mem_comap_jointlySurjectivePrecoverage_iff Scheme.forget).1 hR'.1 x
  obtain ⟨V, rfl, g', hg', hgg'⟩ := Presieve.map_iff.1 hg
  have hgg : g'.left = g := hgg'.trans (Category.id_comp _)
  refine ⟨V, g', hRS _ _ hg', ?_⟩
  rw [hgg]
  exact hx

/-- The empty sieve does not cover an object of the small pro-étale site whose underlying scheme
is nonempty. -/
theorem bot_notMem_topology_of_nonempty {V : X.ProEt} (x : V.left) :
    (⊥ : Sieve V) ∉ Scheme.ProEt.topology X V := fun h => by
  obtain ⟨W, g, hg, -⟩ := exists_mem_range_of_mem_topology h x
  exact hg

/-- The slice of the small pro-étale site over an object with a point is not sheaf theoretically
empty: its final object is not covered by the empty sieve. -/
theorem exists_bot_notMem_over {V : X.ProEt} (y : V.left) :
    ∃ U : Over V, (⊥ : Sieve U) ∉ (Scheme.ProEt.topology X).over V U := by
  refine ⟨Over.mk (𝟙 V), fun h => bot_notMem_topology_of_nonempty y ?_⟩
  rw [GrothendieckTopology.mem_over_iff] at h
  simpa using h

end Scheme.ProEt

namespace ProEtale

local instance hasSheafify_proEt_over_moduleCat' (R : Type v) [CommRing R] {Y : Scheme.{u}}
    (U : Y.ProEt) :
    HasSheafify ((Scheme.ProEt.topology Y).over U) (ModuleCat.{max (u + 1) v w} R) :=
  hasSheafify_moduleCat.{u + 1, u, max v w, v} _ _

local instance wEqualsLocallyBijective_proEt_over_moduleCat (R : Type v) [CommRing R]
    {Y : Scheme.{u}} (U : Y.ProEt) :
    ((Scheme.ProEt.topology Y).over U).WEqualsLocallyBijective (ModuleCat.{max (u + 1) v w} R) :=
  Stacks.ConstantSheaf.wEqualsLocallyBijective_moduleCat.{u, u + 1, max v w, v} _ R

/-- Constructibility of a pro-étale sheaf of modules is invariant under isomorphism. -/
instance isClosedUnderIsomorphisms_isConstructibleModuleSheaf' (X : Scheme.{u})
    (Λ : Type v) [CommRing Λ] [IsNoetherianRing Λ] :
    ObjectProperty.IsClosedUnderIsomorphisms (IsConstructibleModuleSheaf'.{u, v, w} X Λ) where
  of_iso e hF U := by
    obtain ⟨s, hs⟩ := hF U
    exact ⟨s, fun i ↦ ObjectProperty.prop_of_iso _ (Functor.mapIso _ e) (hs i)⟩

variable {Z X : Scheme.{u}} (g : Z ⟶ X) (Λ : Type v) [CommRing Λ]

/-- **The inverse image of a constant sheaf of modules is constant.** Pro-étale base change
preserves the final object, so it is a final functor, and inverse image along a final continuous
functor carries constant sheaves to constant sheaves. -/
def proetaleModuleInverseImageConstantSheafIso (M : ModuleCat.{max (u + 1) v w} Λ) :
    (proetaleModuleInverseImage.{u, v, w} g Λ).obj
        ((constantSheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) v w} Λ)).obj M) ≅
      (constantSheaf (Scheme.ProEt.topology Z) (ModuleCat.{max (u + 1) v w} Λ)).obj M :=
  ((Functor.sheafPullbackConstruction.sheafPullbackIso (Scheme.proetaleBaseChange g)
      (ModuleCat.{max (u + 1) v w} Λ) (Scheme.ProEt.topology X)
      (Scheme.ProEt.topology Z)).app _).symm ≪≫
    Stacks.ConstantSheaf.sheafPullbackConstantSheafIsoOfFinal (Scheme.proetaleBaseChange g)
      (Scheme.ProEt.topology X) (Scheme.ProEt.topology Z) (ModuleCat.{max (u + 1) v w} Λ) M

/-- **The value of a constructible constant sheaf is finite.** On a nonempty scheme `X`, over a
Noetherian ring `Λ`, a `Λ`-module whose constant sheaf on `X_proét` is constructible is a finite
`Λ`-module. -/
theorem finite_of_isConstructibleModuleSheaf'_constantSheaf [IsNoetherianRing Λ] [Nonempty X]
    (M : ModuleCat.{max (u + 1) v w} Λ)
    (hM : IsConstructibleModuleSheaf'.{u, v, w} X Λ
      ((constantSheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) v w} Λ)).obj M)) :
    Module.Finite Λ M := by
  obtain ⟨x⟩ := ‹Nonempty X›
  obtain ⟨U, hU, hxU, -⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens)
    (show x ∈ (⊤ : X.Opens) from trivial)
  obtain ⟨s, hs⟩ := hM ⟨U, hU⟩
  have hx : x ∈ ⋃ i, Set.range (s.inclusion i).base := by
    rw [← s.covers]
    exact hxU
  obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hx
  obtain ⟨z, -⟩ := hi
  let JZ := Scheme.ProEt.topology (s.piece i)
  have hc := ObjectProperty.prop_of_iso _
    (proetaleModuleInverseImageConstantSheafIso.{u, v, w} (s.inclusion i) Λ M) (hs i)
  obtain ⟨I, V, f, hf, hV⟩ := hc (Scheme.ProEt.mk (𝟙 (s.piece i)))
  obtain ⟨W, g', hg', ⟨w', -⟩⟩ := Scheme.ProEt.exists_mem_range_of_mem_topology hf
    (show (Scheme.ProEt.mk (𝟙 (s.piece i))).left from z)
  obtain ⟨j, h, rfl⟩ := (Sieve.mem_ofArrows_iff _ _ _).mp hg'
  obtain ⟨E, hE, ⟨e⟩⟩ := hV j
  have : Module.Finite Λ E := (ModuleCat.isFG_iff _).mp hE
  have := Module.finitePresentation_of_finite Λ E
  exact Stacks.ConstantSheaf.finite_of_constantSheaf_iso.{u + 1, u, v, max (u + 1) v w}
    (JZ.over (V j))
    (Scheme.ProEt.exists_bot_notMem_over (h.left w')) E M
    (e ≪≫ ((Stacks.ConstantSheaf.overPullbackConstantSheafIso JZ
      (ModuleCat.{max (u + 1) v w} Λ) (V j)).app M).symm)

end ProEtale

end AlgebraicGeometry

end
