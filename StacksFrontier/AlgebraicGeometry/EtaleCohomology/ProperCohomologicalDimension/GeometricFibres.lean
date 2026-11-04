module

public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtalePointUniverse
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleStalkBaseChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.GeometricPointStalkCohomology
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TopologicalInvarianceCohomology
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionInverseImage
public import StacksFrontier.AlgebraicGeometry.FibreDimensionBaseChange.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.UniversalHomeomorphism.PurelyInseparableField
public import StacksFrontier.Topology.Dimension.LocalKrullDim

/-!
# Reducing the vanishing of higher direct images to geometric fibres

Let `p : S ⟶ T` be a proper morphism all of whose fibres have dimension at most `N`, and suppose
that cohomology commutes with base change for `p` (the proper base change theorem,
[Stacks, Tag 095T]). By [Stacks, Tag 0DDF] the stalk of `R^q p_* F` at a geometric point `ȳ` of
`T` is `H^q(S_ȳ, F|_{S_ȳ})`, and the geometric fibre `S_ȳ` is a proper scheme of dimension at most
`N` over a separably closed field. So the vanishing of `R^q p_* F` for `q > 2N` reduces to the
vanishing of `H^q(X, F)` for `q > 2N`, `X` proper of dimension at most `N` over a separably closed
field. This is the first step of the proof of [Stacks, Tag 095U]. The source reduces further to
algebraically closed fields, which is the content of the second result: over a separably closed
field `Ω`, the base change of `X` to an algebraic closure of `Ω` is a universal homeomorphism onto
`X`, so étale cohomology does not change ([Stacks, Tag 03SI]).

## Main results

* `Stacks.EtaleCohomology.topologicalKrullDim_pullback_le_of_fiber`: a geometric fibre of a
  morphism locally of finite type whose fibres have dimension at most `N` has dimension at most
  `N`.
* `Stacks.EtaleCohomology.isZero_of_forall_isZero_sheafFiber_residueGeometricPoint`: an abelian
  sheaf on `T_étale` vanishes if its stalks at the residue geometric points do.
* `Stacks.EtaleCohomology.isZero_rightDerived_etaleAbelianDirectImage_of_geometricFibres`: the
  reduction of the vanishing of `R^q p_* F` to the geometric fibres.
* `Stacks.EtaleCohomology.subsingleton_sheafH_of_isSepClosed_of_isAlgClosed`: the reduction from
  separably closed to algebraically closed base fields.

## References

* [Stacks Project, Tag 0DDF](https://stacks.math.columbia.edu/tag/0DDF)
* [Stacks Project, Tag 03SI](https://stacks.math.columbia.edu/tag/03SI)
* [Stacks Project, Tag 095U](https://stacks.math.columbia.edu/tag/095U)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open ZeroObject

universe u v

namespace Stacks.EtaleCohomology

/-- The Krull dimension of a scheme `X` over the spectrum of a field is at most `N` if, at every
point `x`, the local dimension at `x` of the fibre of `π` through `x` is at most `N`. -/
theorem topologicalKrullDim_le_of_forall_topologicalKrullDimAt_fiber_le {X : Scheme.{u}}
    {Ω : Type u} [Field Ω] (π : X ⟶ Spec (.of Ω)) (N : WithBot ℕ∞)
    (h : ∀ x : X, topologicalKrullDimAt ↥(π.fiber (π x)) (π.asFiber x) ≤ N) :
    topologicalKrullDim X ≤ N := by
  rw [TopologicalSpace.topologicalKrullDim_eq_iSup_localKrullDim]
  refine iSup_le fun x ↦ ?_
  have hset : (π : X → Spec (.of Ω)) ⁻¹' {π x} = Set.univ :=
    Set.eq_univ_of_forall fun z ↦ Subsingleton.elim (π z) (π x)
  let e : X ≃ₜ ((π : X → Spec (.of Ω)) ⁻¹' {π x}) :=
    (Homeomorph.Set.univ X).symm.trans (Homeomorph.setCongr hset.symm)
  rw [← TopologicalSpace.topologicalKrullDimAt_eq_localKrullDim,
    topologicalKrullDimAt_eq_of_homeomorph e x]
  exact (topologicalKrullDimAt_fiber_asFiber_eq_preimage π x).symm.trans_le (h x)

/-- **A geometric fibre of a morphism whose fibres have dimension at most `N` has dimension at most
`N`.** For `p : S ⟶ T` locally of finite type and `y : Spec Ω ⟶ T` with `Ω` a field, the base
change `S ×_T Spec Ω` has dimension at most `N` if every fibre of `p` does. -/
theorem topologicalKrullDim_pullback_le_of_fiber {S T : Scheme.{u}} (p : S ⟶ T)
    [LocallyOfFiniteType p] (N : WithBot ℕ∞) (hN : ∀ t : T, topologicalKrullDim (p.fiber t) ≤ N)
    {Ω : Type u} [Field Ω] (y : Spec (.of Ω) ⟶ T) :
    topologicalKrullDim ↥(pullback p y) ≤ N := by
  refine topologicalKrullDim_le_of_forall_topologicalKrullDimAt_fiber_le (pullback.snd p y) N
    fun x ↦ ?_
  rw [topologicalKrullDimAt_fiber_eq_of_isPullback (IsPullback.of_hasPullback p y) x]
  exact (topologicalKrullDimAt_le_topologicalKrullDim _).trans (hN _)

/-- The residue geometric points of a scheme, as points of its small étale site relative to the
coefficient universe. -/
abbrev residueGeometricPoints (X : Scheme.{u}) :
    ObjectProperty (GrothendieckTopology.Point.{max (u + 1) v} X.smallEtaleTopology) :=
  ObjectProperty.ofObj
    (fun x : X ↦ (Scheme.pointSmallEtale (residueGeometricPoint X x)).ulift.{max (u + 1) v})

/-- The residue geometric points of a scheme form a conservative family of points of its small
étale site. -/
theorem isConservativeFamilyOfPoints_residueGeometricPoints (X : Scheme.{u}) :
    (residueGeometricPoints.{u, v} X).IsConservativeFamilyOfPoints :=
  Scheme.isConservative_pointSmallEtale_ulift.{v, u} (residueGeometricPoint X)
    (Set.eq_univ_of_forall fun x ↦ Set.mem_iUnion.2
      ⟨x, default, residueGeometricPoint_apply X x default⟩)

/-- **Geometric stalks detect the zero sheaf.** An abelian sheaf on the small étale site of `T`
whose stalks at the residue geometric points vanish is zero. -/
theorem isZero_of_forall_isZero_sheafFiber_residueGeometricPoint {T : Scheme.{u}}
    (G : Sheaf T.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})
    (h : ∀ t : T, IsZero ((((pointSmallEtale (residueGeometricPoint T t)).ulift.{max (u + 1) v}
      ).sheafFiber (A := AddCommGrpCat.{max (u + 1) v})).obj G)) :
    IsZero G := by
  have hiso : IsIso (0 : G ⟶ 0) := by
    refine (((isConservativeFamilyOfPoints_residueGeometricPoints.{u, v}
      T).jointlyReflectIsomorphisms AddCommGrpCat.{max (u + 1) v}).isIso_iff _).2 ?_
    rintro ⟨_, ⟨t⟩⟩
    exact isIso_of_source_target_iso_zero _ (h t).isoZero
      ((Functor.map_isZero _ (isZero_zero _)).isoZero)
  exact (isZero_zero _).of_iso (asIso (0 : G ⟶ 0))

/-- **The vanishing of the higher direct images of a proper morphism, from its geometric fibres**
(the first step of the proof of [Stacks, Tag 095U], through [Stacks, Tag 0DDF]). Let `p : S ⟶ T`
be proper, with every fibre of dimension at most `N`, and suppose cohomology commutes with base
change for `p`. If `H^q(X, G) = 0` for every `q > 2N`, every proper scheme `X` of dimension at most
`N` over a separably closed field and every torsion abelian sheaf `G` on `X_étale`, then
`R^q p_* F = 0` for every torsion abelian sheaf `F` on `S_étale` and every `q > 2N`. -/
theorem isZero_rightDerived_etaleAbelianDirectImage_of_geometricFibres
    [∀ S : Scheme.{u},
      HasExt.{max (u + 1) v} (Sheaf S.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]
    {S T : Scheme.{u}} (p : S ⟶ T) [IsProper p] (hp : CohomologyCommutesWithBaseChange.{u, v} p)
    (N : ℕ) (hN : ∀ t : T, topologicalKrullDim (p.fiber t) ≤ N)
    (habs : ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (X : Scheme.{u})
      (π : X ⟶ Spec (.of Ω)) [IsProper π], topologicalKrullDim X ≤ N →
      ∀ G : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v},
        Stacks.Torsion.torsionSheafProperty X.smallEtaleTopology G →
        ∀ q : ℕ, 2 * N < q → Subsingleton (Sheaf.H.{max (u + 1) v} G q))
    (F : Sheaf S.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})
    (hF : Stacks.Torsion.torsionSheafProperty S.smallEtaleTopology F) (q : ℕ) (hq : 2 * N < q) :
    IsZero (((etaleAbelianDirectImage.{u, v} p).rightDerived q).obj F) := by
  refine isZero_of_forall_isZero_sheafFiber_residueGeometricPoint.{u, v} _ fun t ↦ ?_
  let y := residueGeometricPoint T t
  have hsub := habs _ (pullback p y) (pullback.snd p y)
    (topologicalKrullDim_pullback_le_of_fiber p N hN y)
    ((etaleAbelianInverseImage.{u, v} (pullback.fst p y)).obj F)
    (torsionSheafProperty_etaleAbelianInverseImage.{u, v} _ F hF) q hq
  exact (AddCommGrpCat.isZero_of_subsingleton _).of_iso
    (etaleAbelianSheafFiberRightDerivedDirectImageIso.{u, v} p y hp F hF q)

/-- **From algebraically closed to separably closed base fields** ([Stacks, Tag 03SI]). If
`H^q(X, G) = 0` for every `q > 2N`, every proper scheme `X` of dimension at most `N` over an
algebraically closed field and every torsion abelian sheaf `G`, the same holds over separably
closed fields. -/
theorem subsingleton_sheafH_of_isSepClosed_of_isAlgClosed
    [∀ S : Scheme.{u},
      HasExt.{max (u + 1) v} (Sheaf S.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]
    (N : ℕ)
    (hac : ∀ (k : Type u) [Field k] [IsAlgClosed k] (X : Scheme.{u})
      (π : X ⟶ Spec (.of k)) [IsProper π], topologicalKrullDim X ≤ N →
      ∀ G : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v},
        Stacks.Torsion.torsionSheafProperty X.smallEtaleTopology G →
        ∀ q : ℕ, 2 * N < q → Subsingleton (Sheaf.H.{max (u + 1) v} G q))
    (Ω : Type u) [Field Ω] [IsSepClosed Ω] (X : Scheme.{u}) (π : X ⟶ Spec (.of Ω)) [IsProper π]
    (hX : topologicalKrullDim X ≤ N) (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})
    (hG : Stacks.Torsion.torsionSheafProperty X.smallEtaleTopology G) (q : ℕ) (hq : 2 * N < q) :
    Subsingleton (Sheaf.H.{max (u + 1) v} G q) := by
  let g : Spec (.of (AlgebraicClosure Ω)) ⟶ Spec (.of Ω) :=
    Spec.map (CommRingCat.ofHom (algebraMap Ω (AlgebraicClosure Ω)))
  have hg : UniversalHomeomorphism (pullback.fst π g) :=
    ⟨MorphismProperty.of_isPullback (IsPullback.of_hasPullback π g).flip
      (inferInstance : UniversalHomeomorphism g).1⟩
  have hhomeo : IsHomeomorph (pullback.fst π g).base := MorphismProperty.universally_le _ _ hg.1
  have hsub := hac (AlgebraicClosure Ω) (pullback π g) (pullback.snd π g)
    (hhomeo.topologicalKrullDim_eq.trans_le hX)
    ((etaleAbelianInverseImage.{u, v} (pullback.fst π g)).obj G)
    (torsionSheafProperty_etaleAbelianInverseImage.{u, v} _ G hG) q hq
  exact (Equiv.ofBijective _
    (etaleCohomologyRestrictionMap_bijective_of_universalHomeomorphism.{u, v, max (u + 1) v}
      (pullback.fst π g) G q)).subsingleton

end Stacks.EtaleCohomology

end
