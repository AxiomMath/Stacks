module

public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Geometrically.Reduced
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.AlgebraicClosureBaseChange
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.GaloisCategories.FiberFunctorComplete
public import StacksFrontier.AlgebraicGeometry.Morphisms.FinitePresentationPoint

/-!
# The homotopy sequence of a proper flat family with connected reduced fibres

Let `f : X ⟶ S` be flat, proper and of finite presentation with geometrically connected and
geometrically reduced fibres, let `S` be connected and let `s` be a geometric point of `S`. The
geometric fibre `X_s = X ×_S s` carries the projection `p : X_s ⟶ X`, and a geometric point `z`
of `X_s` gives compatible base points `z`, `z ∘ p` and `z ∘ p ∘ f` of the three schemes. The
sequence

```
π₁(X_s, z) ⟶ π₁(X, z ∘ p) ⟶ π₁(S, z ∘ p ∘ f) ⟶ 1
```

is exact. Two of its three assertions are proved here: surjectivity of the second map, and
triviality of the composite.

## Main results

* `AlgebraicGeometry.connectedSpace_of_geometricallyConnected_of_flat` and
  `AlgebraicGeometry.connectedSpace_pullback_geometricPoint_of_geometricallyConnected`:
  connectedness of `X` and of `X_s`.
* `AlgebraicGeometry.isConnected_finiteEtaleBaseChange_of_geometricallyConnected` and
  `AlgebraicGeometry.fullyFaithful_finiteEtaleBaseChange_of_geometricallyConnected`: a connected
  finite étale cover of `S` stays connected over `X`, and base change of finite étale covers
  along `f` is fully faithful.
* `AlgebraicGeometry.surjective_etaleFundamentalGroupMap_of_properFlat`: surjectivity of
  `π₁(X) ⟶ π₁(S)`.
* `AlgebraicGeometry.isFiniteCoproductOfTerminal_finiteEtaleBaseChange_geometricFibre`: a finite
  étale cover of `S` splits on the geometric fibre.
* `AlgebraicGeometry.etaleFundamentalGroupMap_comp_eq_one_of_properFlat`: the composite
  `π₁(X_s) ⟶ π₁(X) ⟶ π₁(S)` is trivial.

## References

* [Stacks Project, Tag 0C0J](https://stacks.math.columbia.edu/tag/0C0J)
* [Stacks Project, Tag 0BN6](https://stacks.math.columbia.edu/tag/0BN6)
* [Stacks Project, Tag 0BS8](https://stacks.math.columbia.edu/tag/0BS8)
* [Stacks Project, Tag 0BS9](https://stacks.math.columbia.edu/tag/0BS9)
* [Stacks Project, Tag 0BUN](https://stacks.math.columbia.edu/tag/0BUN)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Stacks.FundamentalGroup

universe u

namespace AlgebraicGeometry

/-- The geometric fibre of a flat morphism, locally of finite presentation, with geometrically
connected fibres is connected. -/
theorem connectedSpace_pullback_geometricPoint_of_geometricallyConnected {X S : Scheme.{u}}
    (f : X ⟶ S) [Flat f] [LocallyOfFinitePresentation f] [GeometricallyConnected f]
    (s : GeometricPoint S) : ConnectedSpace ↥(pullback f s.hom) := by
  let : MorphismProperty.IsStableUnderBaseChangeAlong (P := @GeometricallyConnected) s.hom :=
    ⟨fun pb h ↦ MorphismProperty.IsStableUnderBaseChange.of_isPullback pb h⟩
  let : GeometricallyConnected (pullback.snd f s.hom) :=
    MorphismProperty.pullback_snd f s.hom (inferInstance : GeometricallyConnected f)
  exact GeometricallyConnected.connectedSpace (pullback.snd f s.hom)
      (pullback.snd f s.hom).isOpenMap

/-- A categorically connected finite étale cover of the base stays categorically connected after
base change along a flat morphism, locally of finite presentation, with geometrically connected
fibres. -/
theorem isConnected_finiteEtaleBaseChange_of_geometricallyConnected {X S : Scheme.{u}}
    (f : X ⟶ S) [Flat f] [LocallyOfFinitePresentation f] [GeometricallyConnected f]
    (V : FiniteEtaleOver S) (hV : PreGaloisCategory.IsConnected V) :
    PreGaloisCategory.IsConnected ((finiteEtaleBaseChange f).obj V) := by
  have : ConnectedSpace ↥V.left := connectedSpace_left_of_isConnected V hV
  let : MorphismProperty.IsStableUnderBaseChangeAlong (P := @GeometricallyConnected) V.hom :=
    ⟨fun pb h ↦ MorphismProperty.IsStableUnderBaseChange.of_isPullback pb h⟩
  let : MorphismProperty.IsStableUnderBaseChangeAlong (P := @Flat) V.hom :=
    ⟨fun pb h ↦ MorphismProperty.IsStableUnderBaseChange.of_isPullback pb h⟩
  let : Flat (pullback.fst V.hom f) :=
    MorphismProperty.pullback_fst V.hom f (inferInstance : Flat f)
  have : ConnectedSpace ↥((finiteEtaleBaseChange f).obj V).left :=
    @GeometricallyConnected.connectedSpace _ _ (pullback.fst V.hom f)
      (MorphismProperty.pullback_fst V.hom f (inferInstance : GeometricallyConnected f))
      ‹ConnectedSpace ↥V.left› (pullback.fst V.hom f).isOpenMap
  exact isConnected_of_connectedSpace_left ((finiteEtaleBaseChange f).obj V)

/-- Base change of finite étale covers along a flat morphism, locally of finite presentation,
with geometrically connected fibres over a connected base is fully faithful. -/
theorem fullyFaithful_finiteEtaleBaseChange_of_geometricallyConnected {X S : Scheme.{u}}
    (f : X ⟶ S) [Flat f] [LocallyOfFinitePresentation f] [GeometricallyConnected f]
    [ConnectedSpace ↥S] (x : GeometricPoint X) :
    Nonempty (finiteEtaleBaseChange f).FullyFaithful := by
  have : ConnectedSpace ↥X := GeometricallyConnected.connectedSpace f f.isOpenMap
  let H := finiteEtaleBaseChange f
  let F := finiteEtaleFiberFintypeFunctor S (x.map f)
  let F' := finiteEtaleFiberFintypeFunctor X x
  let t := finiteEtaleFiberFintypeFunctorBaseChangeIso f x
  let d := galoisFunctorDataOfFiberIso F F' H t
  let _gF : IsGaloisCategory (setValuedFiberFunctor F) :=
    isGaloisCategory_setValuedFiberFunctor_finiteEtaleFiberFintypeFunctor S (x.map f)
  let _gF' : IsGaloisCategory (setValuedFiberFunctor F') :=
    isGaloisCategory_setValuedFiberFunctor_finiteEtaleFiberFintypeFunctor X x
  let star := finiteEtaleOverTerminal S
  let star' := finiteEtaleOverTerminal X
  have hs : IsTerminal star := MorphismProperty.Over.mkIdTerminal _ _
  have hs' : IsTerminal star' := MorphismProperty.Over.mkIdTerminal _ _
  have hH := exactFunctor_finiteEtaleBaseChange f x
  have : PreservesFiniteLimits H := hH.1
  have hHs : IsTerminal (H.obj star) := hs.isTerminalObj H star
  exact ((surjective_inducedHom_tfae F F' H hH t d star star' hs hs' hHs).out 3 2).mp
    (isConnected_finiteEtaleBaseChange_of_geometricallyConnected f)

/-- For a flat proper morphism of finite presentation with geometrically connected and
geometrically reduced fibres over a connected base, the fundamental group of the total space maps
onto the fundamental group of the base, at the base points coming from a geometric point of a
geometric fibre. -/
@[stacks 0C0J "surjectivity of `π₁(X) → π₁(S)`, the assertion `→ 1` of the homotopy sequence; \
triviality of the composite and exactness at `π₁(X)` are separate", sga "1 XIII 4.4" "(X)"]
theorem surjective_etaleFundamentalGroupMap_of_properFlat {X S : Scheme.{u}} (f : X ⟶ S)
    [Flat f] [IsProper f] (hfp : FinitePresentation f) [GeometricallyConnected f]
    [GeometricallyReduced f] [ConnectedSpace ↥S] (s : GeometricPoint S)
    (z : GeometricPoint (pullback f s.hom)) :
    letI : LocallyOfFinitePresentation f := hfp.1
    letI : ConnectedSpace ↥X := GeometricallyConnected.connectedSpace f f.isOpenMap
    Function.Surjective (etaleFundamentalGroupMap f (z.map (pullback.fst f s.hom))) := by
  have : LocallyOfFinitePresentation f := hfp.1
  have : ConnectedSpace ↥X := GeometricallyConnected.connectedSpace f f.isOpenMap
  set x := z.map (pullback.fst f s.hom)
  let H := finiteEtaleBaseChange f
  let F := finiteEtaleFiberFintypeFunctor S (x.map f)
  let F' := finiteEtaleFiberFintypeFunctor X x
  let t := finiteEtaleFiberFintypeFunctorBaseChangeIso f x
  let d := galoisFunctorDataOfFiberIso F F' H t
  let _gF : IsGaloisCategory (setValuedFiberFunctor F) :=
    isGaloisCategory_setValuedFiberFunctor_finiteEtaleFiberFintypeFunctor S (x.map f)
  let _gF' : IsGaloisCategory (setValuedFiberFunctor F') :=
    isGaloisCategory_setValuedFiberFunctor_finiteEtaleFiberFintypeFunctor X x
  let star := finiteEtaleOverTerminal S
  let star' := finiteEtaleOverTerminal X
  have hs : IsTerminal star := MorphismProperty.Over.mkIdTerminal _ _
  have hs' : IsTerminal star' := MorphismProperty.Over.mkIdTerminal _ _
  have hH := exactFunctor_finiteEtaleBaseChange f x
  have : PreservesFiniteLimits H := hH.1
  have hHs : IsTerminal (H.obj star) := hs.isTerminalObj H star
  have hdsurj : Function.Surjective d.hom :=
    ((surjective_inducedHom_tfae F F' H hH t d star star' hs hs' hHs).out 3 1).mp
      (isConnected_finiteEtaleBaseChange_of_geometricallyConnected f)
  intro ρ
  obtain ⟨σ, hσ⟩ := hdsurj ((autMulEquivEtaleFundamentalGroup S (x.map f)).symm ρ)
  refine ⟨autMulEquivEtaleFundamentalGroup X x σ, ?_⟩
  rw [← autMulEquivEtaleFundamentalGroup_galoisFunctorData_hom f x d σ, hσ]
  exact (autMulEquivEtaleFundamentalGroup S (x.map f)).apply_symm_apply ρ

/-- A finite étale cover of the base becomes a finite coproduct of copies of a geometric fibre
after base change to that fibre. -/
theorem isFiniteCoproductOfTerminal_finiteEtaleBaseChange_geometricFibre {X S : Scheme.{u}}
    (f : X ⟶ S) [Flat f] [LocallyOfFinitePresentation f] [GeometricallyConnected f]
    [ConnectedSpace ↥S] (s : GeometricPoint S) (z : GeometricPoint (pullback f s.hom))
    (V : FiniteEtaleOver S) :
    IsFiniteCoproductOfTerminal
      ((finiteEtaleBaseChange (pullback.fst f s.hom)).obj ((finiteEtaleBaseChange f).obj V)) := by
  have : ConnectedSpace ↥(pullback f s.hom) :=
    connectedSpace_pullback_geometricPoint_of_geometricallyConnected f s
  have : IsSepClosed (IsLocalRing.ResidueField s.residueField) :=
    have : IsAlgClosed (IsLocalRing.ResidueField s.residueField) :=
      IsAlgClosed.of_ringEquiv s.residueField _
        ((RingEquiv.quotientBot s.residueField).symm.trans
          (Ideal.quotEquivOfEq IsLocalRing.maximalIdeal_eq_bot.symm))
    inferInstance
  have hex := exactFunctor_finiteEtaleBaseChange (pullback.snd f s.hom) z
  have : PreservesFiniteLimits (finiteEtaleBaseChange (pullback.snd f s.hom)) := hex.1
  have : PreservesFiniteColimits (finiteEtaleBaseChange (pullback.snd f s.hom)) := hex.2
  have hsplit : IsFiniteCoproductOfTerminal
      ((finiteEtaleBaseChange (pullback.snd f s.hom)).obj
        ((finiteEtaleBaseChange s.hom).obj V)) :=
    isFiniteCoproductOfTerminal_map _
      (isFiniteCoproductOfTerminal_of_henselian_isSepClosed s.residueField _)
  exact isFiniteCoproductOfTerminal_of_iso (((finiteEtaleBaseChangeComp (pullback.snd f s.hom)
      s.hom (pullback.fst f s.hom ≫ f) pullback.condition).app V).symm ≪≫
    (finiteEtaleBaseChangeComp (pullback.fst f s.hom) f (pullback.fst f s.hom ≫ f) rfl).app V)
    hsplit

/-- For a flat proper morphism of finite presentation with geometrically connected and
geometrically reduced fibres over a connected base, the composite of the maps on fundamental
groups from a geometric fibre to the total space and from there to the base is trivial. -/
@[stacks 0C0J "triviality of the composite `π₁(X_s) → π₁(X) → π₁(S)`, the complex condition of \
the homotopy sequence; surjectivity and exactness at `π₁(X)` are separate"]
theorem etaleFundamentalGroupMap_comp_eq_one_of_properFlat {X S : Scheme.{u}} (f : X ⟶ S)
    [Flat f] [IsProper f] (hfp : FinitePresentation f) [GeometricallyConnected f]
    [GeometricallyReduced f] [ConnectedSpace ↥S] (s : GeometricPoint S)
    (z : GeometricPoint (pullback f s.hom)) :
    letI : LocallyOfFinitePresentation f := hfp.1
    letI : ConnectedSpace ↥X := GeometricallyConnected.connectedSpace f f.isOpenMap
    letI : ConnectedSpace ↥(pullback f s.hom) :=
      connectedSpace_pullback_geometricPoint_of_geometricallyConnected f s
    (etaleFundamentalGroupMap f (z.map (pullback.fst f s.hom))).toMonoidHom.comp
        (etaleFundamentalGroupMap (pullback.fst f s.hom) z).toMonoidHom = 1 := by
  have : LocallyOfFinitePresentation f := hfp.1
  have : ConnectedSpace ↥X := GeometricallyConnected.connectedSpace f f.isOpenMap
  have : ConnectedSpace ↥(pullback f s.hom) :=
    connectedSpace_pullback_geometricPoint_of_geometricallyConnected f s
  exact etaleFundamentalGroupMap_comp_eq_one_of_isFiniteCoproductOfTerminal _ f z
    (isFiniteCoproductOfTerminal_finiteEtaleBaseChange_geometricFibre f s z)

end AlgebraicGeometry

end
