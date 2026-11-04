module

public import StacksFrontier.AlgebraicGeometry.Divisors.Reflexive.ConstantRank
public import StacksFrontier.AlgebraicGeometry.Divisors.Reflexive.DivisorClassFaithful
public import StacksFrontier.AlgebraicGeometry.Divisors.Reflexive.NormalCriterion
public import StacksFrontier.AlgebraicGeometry.Divisors.Reflexive.RankOneTensorMonoid
public import StacksFrontier.AlgebraicGeometry.Divisors.WeilDivisorClass.RestrictMeromorphic
public import StacksFrontier.AlgebraicGeometry.ReflexiveHull.CoherentReflexive
public import StacksFrontier.AlgebraicGeometry.ReflexiveOpenEquivalence.Pushforward

/-!
# Rank one coherent reflexive modules and invertible modules on a codimension two open

Let `X` be an integral locally Noetherian normal scheme.  A coherent reflexive `𝒪_X`-module is
finite locally free outside a closed subset of codimension at least two, by [Stacks, Tag 0AY6]
(1) ⇒ (3); if it has rank one then its restriction there is invertible.  Conversely restriction
to such an open is an equivalence on coherent reflexive modules, by [Stacks, Tag 0EBJ], so every
invertible module on such an open extends to a rank one coherent reflexive module on `X`, and
that module is determined up to isomorphism.

## Main results

* `AlgebraicGeometry.CoherentReflexive.exists_codimTwo_isInvertible_restrict` — a rank one
  coherent reflexive module is invertible on an open whose complement has codimension at least
  two.
* `AlgebraicGeometry.CoherentReflexive.exists_rankOne_of_isInvertible` — an invertible module on
  such an open is the restriction of a rank one coherent reflexive module.
* `AlgebraicGeometry.CoherentReflexive.nonempty_iso_restrict_iff` — two rank one coherent
  reflexive modules are isomorphic exactly when their restrictions to such an open are.

## References

* [Stacks Project, Tag 0AY6](https://stacks.math.columbia.edu/tag/0AY6)
* [Stacks Project, Tag 0EBJ](https://stacks.math.columbia.edu/tag/0EBJ)
* [Stacks Project, Tag 0EBM](https://stacks.math.columbia.edu/tag/0EBM)
-/

@[expose] public noncomputable section

open CategoryTheory Order TopologicalSpace
open Stacks.AlgebraicGeometry.ReflexiveModules (IsReflexive ReflexiveCoherentModules
  reflexiveCoherentEquivalence)
open Stacks.AlgebraicGeometry.ReflexiveHull (CoherentReflexiveModules)

universe u

namespace AlgebraicGeometry.CoherentReflexive

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]

/-- The `𝒪_X`-module underlying a rank one coherent reflexive module. -/
abbrev RankOneReflexiveModules.module (F : RankOneReflexiveModules X) : X.Modules :=
  F.obj.obj.obj

/-- The underlying module of a rank one coherent reflexive module is coherent. -/
theorem RankOneReflexiveModules.isCoherent (F : RankOneReflexiveModules X) :
    _root_.SheafOfModules.IsCoherent F.module :=
  F.obj.obj.property

/-- The underlying module of a rank one coherent reflexive module is reflexive. -/
theorem RankOneReflexiveModules.isReflexive (F : RankOneReflexiveModules X) :
    IsReflexive F.module :=
  F.obj.property

/-- The underlying module of a rank one coherent reflexive module has fibre rank one at the
generic point. -/
theorem RankOneReflexiveModules.fiberRank_genericPoint (F : RankOneReflexiveModules X) :
    Scheme.Modules.fiberRank F.module (genericPoint X) = 1 :=
  F.property

/-- A rank one coherent reflexive module, as an object of `ReflexiveCoherentModules X`. -/
def RankOneReflexiveModules.flatten (F : RankOneReflexiveModules X) :
    ReflexiveCoherentModules X :=
  ⟨F.module, F.isCoherent, F.isReflexive⟩

/-- A coherent module and its restriction to an open are coherent and of finite type. -/
private theorem isCoherent_isFiniteType_restrict {Y : Scheme.{u}} [IsLocallyNoetherian Y]
    (U : Y.Opens) (F : Y.Modules) (hF : F.IsCoherent) :
    (F.restrict U.ι).IsCoherent ∧ F.IsFiniteType ∧ (F.restrict U.ι).IsFiniteType := by
  have h : (F.restrict U.ι).IsCoherent :=
    Stacks.AlgebraicGeometry.ReflexiveModules.isCoherent_restrict_of_isCoherent Y U F hF
  have := hF
  exact ⟨h, _root_.IsCoherent.toIsFiniteType _, _root_.IsCoherent.toIsFiniteType _⟩

/-! ### Invertibility on a codimension two open -/

/-- **A rank one coherent reflexive module is invertible outside a closed subset of codimension
at least two.** -/
theorem exists_codimTwo_isInvertible_restrict [IsNormal X] (F : RankOneReflexiveModules X) :
    ∃ U : X.Opens,
      (∀ x : X, x ∉ U → (2 : ℕ∞) ≤ codimension (IrreducibleCloseds.closureSingleton x)) ∧
        SheafOfModules.IsInvertible U.toScheme.sheaf.obj U.toScheme.ringCatSheaf.property
          (F.module.restrict U.ι) := by
  have : _root_.SheafOfModules.IsCoherent F.module := F.isCoherent
  obtain ⟨U, hU, hfree, -⟩ :=
    ((isReflexive_isTorsionFree_propertyS2_extension_tfae X F.module).out 1 3).mp F.isReflexive
  have : IsIntegral U.toScheme := isIntegral_of_two_le_codimension_compl U hU
  have : IsLocallyNoetherian U.toScheme := isLocallyNoetherian_of_isOpenImmersion U.ι
  have : IsDominant U.ι := isDominant_opensι (U := U)
  have := hfree
  obtain ⟨_, _, _⟩ := isCoherent_isFiniteType_restrict U F.module F.isCoherent
  exact ⟨U, hU, (Scheme.Modules.isInvertible_of_fiberRank_eq_one (F.module.restrict U.ι)
    (genericPoint U.toScheme) ((fiberRank_genericPoint_restrict U.ι F.module).trans
      F.fiberRank_genericPoint)).toAlgebraicGeometry⟩

/-! ### Extension from a codimension two open -/

variable (U : X.Opens)
  (hU : ∀ x : X, x ∉ U → (2 : ℕ∞) ≤ codimension (IrreducibleCloseds.closureSingleton x))

include hU

/-- **An invertible module on an open whose complement has codimension at least two is the
restriction of a rank one coherent reflexive module.** -/
theorem exists_rankOne_of_isInvertible [IsNormal X] (L : U.toScheme.Modules)
    (hL : SheafOfModules.IsInvertible U.toScheme.sheaf.obj
      U.toScheme.ringCatSheaf.property L) :
    ∃ F : RankOneReflexiveModules X, Nonempty (F.module.restrict U.ι ≅ L) := by
  have : IsIntegral U.toScheme := isIntegral_of_two_le_codimension_compl U hU
  have : IsLocallyNoetherian U.toScheme := isLocallyNoetherian_of_isOpenImmersion U.ι
  have : IsDominant U.ι := isDominant_opensι (U := U)
  have := hL
  have : Stacks.SheafOfModules.IsInvertible U.toScheme.sheaf.obj
      U.toScheme.ringCatSheaf.property L :=
    (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ _).mpr hL
  have : L.IsCoherent :=
    Stacks.AlgebraicGeometry.CoherenceCriteria.isCoherent_of_isInvertible U.toScheme L
  have hLrefl : IsReflexive L := isReflexive_of_isInvertible U.toScheme L
  obtain ⟨E, hpull, -⟩ := reflexiveCoherentEquivalence X U
    (two_le_depth_stalk_of_notMem_of_two_le_codimension U hU)
  set L' : ReflexiveCoherentModules U.toScheme := ⟨L, inferInstance, hLrefl⟩ with hL'
  set G : ReflexiveCoherentModules X := E.inverse.obj L' with hG
  have e : G.obj.restrict U.ι ≅ L :=
    (Scheme.Modules.restrictFunctorIsoPullback U.ι).app G.obj ≪≫
      (hpull.app G).symm ≪≫ (ObjectProperty.ι _).mapIso (E.counitIso.app L')
  have : G.obj.IsCoherent := G.property.1
  obtain ⟨_, _, _⟩ := isCoherent_isFiniteType_restrict U G.obj G.property.1
  have : L.IsFiniteType := _root_.IsCoherent.toIsFiniteType _
  have hres : SheafOfModules.IsInvertible U.toScheme.sheaf.obj
      U.toScheme.ringCatSheaf.property (G.obj.restrict U.ι) :=
    Stacks.UFDExtensionGlobal.isInvertible_of_iso e.symm hL
  have : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (G.obj.restrict U.ι) 1 :=
    (Scheme.Modules.isFiniteLocallyFreeOfRank_iff _ 1).mp
      ((Stacks.UFDExtensionGlobal.isInvertible_iff_isFiniteLocallyFreeOfRank_one _).1 hres)
  exact ⟨⟨⟨⟨G.obj, G.property.1⟩, G.property.2⟩,
    (fiberRank_genericPoint_restrict U.ι G.obj).symm.trans
      (Scheme.Modules.fiberRank_eq_of_isFiniteLocallyFreeOfRank _ 1 _)⟩, ⟨e⟩⟩

/-! ### Isomorphism is detected on the open -/

/-- **Two rank one coherent reflexive modules are isomorphic exactly when their restrictions to
an open whose complement has codimension at least two are.** -/
theorem nonempty_iso_restrict_iff [IsNormal X] (F G : RankOneReflexiveModules X) :
    Nonempty (F.module.restrict U.ι ≅ G.module.restrict U.ι) ↔
      Nonempty (F.module ≅ G.module) :=
  ⟨nonempty_iso_of_nonempty_restrict_iso U (two_le_depth_stalk_of_notMem_of_two_le_codimension U hU)
    _ _ F.isCoherent F.isReflexive G.isCoherent G.isReflexive,
    fun ⟨i⟩ => ⟨(Scheme.Modules.restrictFunctor U.ι).mapIso i⟩⟩

end AlgebraicGeometry.CoherentReflexive

end
