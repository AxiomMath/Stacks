module

public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.QuasiCoherent.RefinementCanonical

/-!
# Pullback of quasi-coherent descent data is compatible with composition of morphisms of families

Stacks 04W4 pulls a descent datum for quasi-coherent modules back along a morphism of families of
morphisms with fixed target of Stacks 00VT.  This file proves that the pullback is compatible with
composition of such morphisms: for `Φ : 𝒰 ⟶ 𝒱` over `g : U ⟶ V` and `Ψ : 𝒱 ⟶ 𝒲` over
`h : V ⟶ W` the two successive pullbacks of a descent datum for `𝒲` agree with the pullback along
the composite.

## Main definitions

* `AlgebraicGeometry.Space.QuasiCoherentDescent.pullbackDatumCompComparison` is the comparison of
  the component modules: the comparison of inverse images of Stacks 03LU at the factorization
  `Φ.h₀ i ≫ Ψ.h₀ (Φ.s₀ i)` of the `h₀` of the composite.
* `AlgebraicGeometry.Space.QuasiCoherentDescent.pullbackDatumCompIso` is the isomorphism of
  descent data it assembles into.

## Main results

* `AlgebraicGeometry.Space.QuasiCoherentDescent.familyPairMap_comp`: the induced morphism of
  pairwise fibre products of a composite of morphisms of families is the composite of the two
  induced morphisms.
* `AlgebraicGeometry.Space.QuasiCoherentDescent.pullbackDatumCompComparison_transition`: **the
  comparison of the component modules commutes with the pairwise isomorphisms of Stacks 04W3**, as
  an equality of isomorphisms.
* `AlgebraicGeometry.Space.QuasiCoherentDescent.pullbackDatumCompIso`: **the pullback of a
  quasi-coherent descent datum along a composite of morphisms of families is the composite of the
  two pullbacks.**

## Implementation notes

The compatibility is stated and proved at the level of *isomorphisms*, and is handed to
`AlgebraicGeometry.Space.QuasiCoherentDescent.DescentDatum.isoMkOfTransitionEq` so that the
reconciliation with the compatibility field of
`AlgebraicGeometry.Space.QuasiCoherentDescent.DescentDatum.Hom` never happens underneath a
composition of morphisms of modules; that is the constraint recorded in the implementation notes
of `StacksFrontier/AlgebraicGeometry/Spaces/Descent/QuasiCoherent/RefinementCanonical.lean`.

The two spellings `(q ≫ Φ.h₀ i) ≫ Ψ.h₀ (Φ.s₀ i)` and `q ≫ (Φ.h₀ i ≫ Ψ.h₀ (Φ.s₀ i))` of the leg
of the pairwise fibre product occur on the two sides of the compatibility.  Composition in
`AlgebraicGeometry.AlgebraicSpaces` is associative by definitional unfolding, so the inverse
images along them are the same object, and the two sides are compared with no transport; what
makes that affordable is that the identification is asked for in the arguments of
`CategoryTheory.Iso.trans` and `CategoryTheory.Functor.mapIso`, which are ordinary definitions,
and never in the arguments of `CategoryTheory.CategoryStruct.comp`, which is a projection.

## References

* [Stacks Project, Tag 04W4](https://stacks.math.columbia.edu/tag/04W4)
* [Stacks Project, Tag 04W3](https://stacks.math.columbia.edu/tag/04W3)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 00VT](https://stacks.math.columbia.edu/tag/00VT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v v' v''

namespace AlgebraicGeometry.Space.QuasiCoherentDescent

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A pairwise isomorphism read on a test space depends on the morphism to the pairwise fibre
product only through its two composites.**  Replacing that morphism by an equal one leaves the
reading unchanged; the two compatibility proofs are irrelevant.

This is what lets a reading taken along a *composite* of two induced morphisms of pairwise fibre
products be matched with the reading along the induced morphism of the composite, which is
`AlgebraicGeometry.Space.QuasiCoherentDescent.familyPairMap_comp`: the two morphisms are only
propositionally equal, and `CategoryTheory.Iso.trans` is where the substitution has to happen,
since the proof obligations of
`AlgebraicGeometry.Space.QuasiCoherentDescent.transitionOn` depend on it. -/
theorem transitionOn_congr_map {I : Type v} {X : AlgebraicSpaces B S hS}
    (Y : I → AlgebraicSpaces B S hS) (f : ∀ i, Y i ⟶ X)
    (F : ∀ i, Modules.{u, u} B S hS (Y i).1 (Y i).2)
    (φ : ∀ i j, (modulePullback B S hS (pairFst B S hS Y f i j)).obj (F i) ≅
      (modulePullback B S hS (pairSnd B S hS Y f i j)).obj (F j))
    {T : AlgebraicSpaces B S hS} (i j : I) {v v' : T ⟶ pair B S hS Y f i j} (hv : v = v')
    (vi : T ⟶ Y i) (vj : T ⟶ Y j) (hi : v ≫ pairFst B S hS Y f i j = vi)
    (hj : v ≫ pairSnd B S hS Y f i j = vj)
    (hi' : v' ≫ pairFst B S hS Y f i j = vi)
    (hj' : v' ≫ pairSnd B S hS Y f i j = vj) :
    transitionOn B S hS Y f F φ i j v vi vj hi hj =
      transitionOn B S hS Y f F φ i j v' vi vj hi' hj' := by
  subst hv
  rfl

/-- **The comparison of iterated inverse images of Stacks 03LU, inserted on the two sides of an
isomorphism of inverse images along two triple composites.**  Breaking each of the two triple
composites `q ≫ f ≫ e` and `q' ≫ f' ≫ e'` into its three inverse images in the two possible
orders gives the same isomorphism.

This is the associativity coherence of Stacks 03LU — `modulePullback_mapIso_compIso` — applied
once on each side and the resulting comparisons cancelled.  It is stated at variable morphisms,
variable modules and a *variable* middle isomorphism, so that the kernel is asked for no
reduction in it; a consumer whose middle isomorphism is a pairwise isomorphism of a descent
datum read on a test space instantiates it with nothing to compute. -/
theorem compIso_trans_cancel {A A' P T T' T₂ T₂' : AlgebraicSpaces B S hS}
    (q : P ⟶ T) (f : T ⟶ T') (e : T' ⟶ A) (q' : P ⟶ T₂) (f' : T₂ ⟶ T₂') (e' : T₂' ⟶ A')
    (N : Modules.{u, u} B S hS A.1 A.2) (N' : Modules.{u, u} B S hS A'.1 A'.2)
    (Tm : (modulePullback B S hS (q ≫ f ≫ e)).obj N ≅
      (modulePullback B S hS (q' ≫ f' ≫ e')).obj N') :
    (modulePullback B S hS q).mapIso ((modulePullbackCompIso B S hS f e).app N) ≪≫
        (modulePullbackCompIso B S hS q (f ≫ e)).app N ≪≫ Tm ≪≫
        ((modulePullbackCompIso B S hS q' (f' ≫ e')).app N').symm =
      ((modulePullbackCompIso B S hS q f).app ((modulePullback B S hS e).obj N) ≪≫
          ((modulePullbackCompIso B S hS (q ≫ f) e).app N ≪≫ Tm ≪≫
            ((modulePullbackCompIso B S hS (q' ≫ f') e').app N').symm) ≪≫
          ((modulePullbackCompIso B S hS q' f').app
            ((modulePullback B S hS e').obj N')).symm) ≪≫
        (modulePullback B S hS q').mapIso ((modulePullbackCompIso B S hS f' e').app N') := by
  rw [modulePullback_mapIso_compIso (modulePullbackCompIsoAssoc B S hS) q f e N,
    modulePullback_mapIso_compIso (modulePullbackCompIsoAssoc B S hS) q' f' e' N']
  simp only [Iso.trans_assoc, Iso.symm_self_id_assoc]

section FamilyComp

variable {U V W : AlgebraicSpaces B S hS} {𝒰 : PreZeroHypercover.{v} U}
  {𝒱 : PreZeroHypercover.{v'} V} {𝒲 : PreZeroHypercover.{v''} W}
  {g : U ⟶ V} {h : V ⟶ W} {k : U ⟶ W}

/-- The first projection of the composite of the two induced morphisms of pairwise fibre
products is the first projection of the source followed by the `h₀` of the composite. -/
theorem familyPairMap_comp_fst (Φ : 𝒰.HomOver 𝒱 g) (Ψ : 𝒱.HomOver 𝒲 h) (hk : g ≫ h = k)
    (i j : 𝒰.I₀) :
    (familyPairMap B S hS Φ Φ i j ≫
          familyPairMap B S hS Ψ Ψ (Φ.s₀ i) (Φ.s₀ j)) ≫
        pairFst B S hS 𝒲.X 𝒲.f (Ψ.s₀ (Φ.s₀ i)) (Ψ.s₀ (Φ.s₀ j)) =
      pairFst B S hS 𝒰.X 𝒰.f i j ≫ (Φ.comp Ψ hk).h₀ i := by
  rw [Category.assoc, familyPairMap_fst B S hS Ψ Ψ (Φ.s₀ i) (Φ.s₀ j),
    ← Category.assoc, familyPairMap_fst B S hS Φ Φ i j, Category.assoc]
  rfl

/-- The second projection of the composite of the two induced morphisms of pairwise fibre
products is the second projection of the source followed by the `h₀` of the composite. -/
theorem familyPairMap_comp_snd (Φ : 𝒰.HomOver 𝒱 g) (Ψ : 𝒱.HomOver 𝒲 h) (hk : g ≫ h = k)
    (i j : 𝒰.I₀) :
    (familyPairMap B S hS Φ Φ i j ≫
          familyPairMap B S hS Ψ Ψ (Φ.s₀ i) (Φ.s₀ j)) ≫
        pairSnd B S hS 𝒲.X 𝒲.f (Ψ.s₀ (Φ.s₀ i)) (Ψ.s₀ (Φ.s₀ j)) =
      pairSnd B S hS 𝒰.X 𝒰.f i j ≫ (Φ.comp Ψ hk).h₀ j := by
  rw [Category.assoc, familyPairMap_snd B S hS Ψ Ψ (Φ.s₀ i) (Φ.s₀ j),
    ← Category.assoc, familyPairMap_snd B S hS Φ Φ i j, Category.assoc]
  rfl

/-- **The induced morphisms of pairwise fibre products compose.**  The morphism of pairwise fibre
products induced by a composite of morphisms of families is the composite of the two induced
morphisms, both being determined by their two projections. -/
theorem familyPairMap_comp (Φ : 𝒰.HomOver 𝒱 g) (Ψ : 𝒱.HomOver 𝒲 h) (hk : g ≫ h = k)
    (i j : 𝒰.I₀) :
    familyPairMap B S hS (Φ.comp Ψ hk) (Φ.comp Ψ hk) i j =
      familyPairMap B S hS Φ Φ i j ≫
        familyPairMap B S hS Ψ Ψ (Φ.s₀ i) (Φ.s₀ j) :=
  (AlgebraicSpaces.isPullback_fiberProduct B S hS
      (𝒲.f (Ψ.s₀ (Φ.s₀ i))) (𝒲.f (Ψ.s₀ (Φ.s₀ j)))).hom_ext
    ((familyPairMap_fst B S hS (Φ.comp Ψ hk) (Φ.comp Ψ hk) i j).trans
      (familyPairMap_comp_fst B S hS Φ Ψ hk i j).symm)
    ((familyPairMap_snd B S hS (Φ.comp Ψ hk) (Φ.comp Ψ hk) i j).trans
      (familyPairMap_comp_snd B S hS Φ Ψ hk i j).symm)

/-- The comparison of the component modules of the two pullbacks: the `i`-th component of the
pullback along `Φ` of the pullback along `Ψ` is the iterated inverse image along `Φ.h₀ i` and
`Ψ.h₀ (Φ.s₀ i)`, and the `i`-th component of the pullback along the composite is the inverse
image along the composite of those two morphisms. -/
def pullbackDatumCompComparison (Φ : 𝒰.HomOver 𝒱 g) (Ψ : 𝒱.HomOver 𝒲 h) (hk : g ≫ h = k)
    (D : DescentDatum B S hS 𝒲.X 𝒲.f) (i : 𝒰.I₀) :
    (modulePullback B S hS (Φ.h₀ i)).obj
        ((modulePullback B S hS (Ψ.h₀ (Φ.s₀ i))).obj (D.F (Ψ.s₀ (Φ.s₀ i)))) ≅
      (modulePullback B S hS ((Φ.comp Ψ hk).h₀ i)).obj (D.F ((Φ.comp Ψ hk).s₀ i)) :=
  (pullbackComparison B S hS (Φ.h₀ i) (Ψ.h₀ (Φ.s₀ i))
    (Φ.h₀ i ≫ Ψ.h₀ (Φ.s₀ i)) rfl (D.F (Ψ.s₀ (Φ.s₀ i)))).symm

/-- The comparison of the component modules, written through the comparison of iterated inverse
images of Stacks 03LU. -/
theorem pullbackDatumCompComparison_eq (Φ : 𝒰.HomOver 𝒱 g) (Ψ : 𝒱.HomOver 𝒲 h)
    (hk : g ≫ h = k) (D : DescentDatum B S hS 𝒲.X 𝒲.f) (i : 𝒰.I₀) :
    pullbackDatumCompComparison B S hS Φ Ψ hk D i =
      (modulePullbackCompIso B S hS (Φ.h₀ i) (Ψ.h₀ (Φ.s₀ i))).app
        (D.F (Ψ.s₀ (Φ.s₀ i))) := by
  rw [pullbackDatumCompComparison, pullbackComparison_rfl, Iso.symm_symm_eq]

/-- **The comparison of the component modules of the two pullbacks commutes with the pairwise
isomorphisms of Stacks 04W3.**  Stated as an equality of isomorphisms, which is the form
`AlgebraicGeometry.Space.QuasiCoherentDescent.DescentDatum.isoMkOfTransitionEq` consumes. -/
theorem pullbackDatumCompComparison_transition (Φ : 𝒰.HomOver 𝒱 g) (Ψ : 𝒱.HomOver 𝒲 h)
    (hk : g ≫ h = k) (D : DescentDatum B S hS 𝒲.X 𝒲.f) (i j : 𝒰.I₀) :
    (modulePullback B S hS (pairFst B S hS 𝒰.X 𝒰.f i j)).mapIso
          (pullbackDatumCompComparison B S hS Φ Ψ hk D i) ≪≫
        pullbackTransition B S hS (Φ.comp Ψ hk) D i j =
      pullbackTransition B S hS Φ (pullbackDatum B S hS Ψ D) i j ≪≫
        (modulePullback B S hS (pairSnd B S hS 𝒰.X 𝒰.f i j)).mapIso
          (pullbackDatumCompComparison B S hS Φ Ψ hk D j) := by
  have hcast : transitionOn B S hS 𝒱.X 𝒱.f (pullbackDatum B S hS Ψ D).F
        (pullbackDatum B S hS Ψ D).transition (Φ.s₀ i) (Φ.s₀ j)
        (familyPairMap B S hS Φ Φ i j) (pairFst B S hS 𝒰.X 𝒰.f i j ≫ Φ.h₀ i)
        (pairSnd B S hS 𝒰.X 𝒰.f i j ≫ Φ.h₀ j) (familyPairMap_fst B S hS Φ Φ i j)
        (familyPairMap_snd B S hS Φ Φ i j) =
      transitionOn B S hS 𝒱.X 𝒱.f
        (fun t => (modulePullback B S hS (Ψ.h₀ t)).obj (D.F (Ψ.s₀ t)))
        (pullbackTransition B S hS Ψ D) (Φ.s₀ i) (Φ.s₀ j)
        (familyPairMap B S hS Φ Φ i j) (pairFst B S hS 𝒰.X 𝒰.f i j ≫ Φ.h₀ i)
        (pairSnd B S hS 𝒰.X 𝒰.f i j ≫ Φ.h₀ j) (familyPairMap_fst B S hS Φ Φ i j)
        (familyPairMap_snd B S hS Φ Φ i j) :=
    rfl
  have hcomp : pullbackTransition B S hS (Φ.comp Ψ hk) D i j =
      (pullbackComparison B S hS (pairFst B S hS 𝒰.X 𝒰.f i j)
          (Φ.h₀ i ≫ Ψ.h₀ (Φ.s₀ i))
          (pairFst B S hS 𝒰.X 𝒰.f i j ≫ (Φ.h₀ i ≫ Ψ.h₀ (Φ.s₀ i))) rfl
          (D.F (Ψ.s₀ (Φ.s₀ i)))).symm ≪≫
        transitionOn B S hS 𝒲.X 𝒲.f D.F D.transition (Ψ.s₀ (Φ.s₀ i)) (Ψ.s₀ (Φ.s₀ j))
          (familyPairMap B S hS (Φ.comp Ψ hk) (Φ.comp Ψ hk) i j)
          (pairFst B S hS 𝒰.X 𝒰.f i j ≫ (Φ.h₀ i ≫ Ψ.h₀ (Φ.s₀ i)))
          (pairSnd B S hS 𝒰.X 𝒰.f i j ≫ (Φ.h₀ j ≫ Ψ.h₀ (Φ.s₀ j)))
          (familyPairMap_fst B S hS (Φ.comp Ψ hk) (Φ.comp Ψ hk) i j)
          (familyPairMap_snd B S hS (Φ.comp Ψ hk) (Φ.comp Ψ hk) i j) ≪≫
        pullbackComparison B S hS (pairSnd B S hS 𝒰.X 𝒰.f i j)
          (Φ.h₀ j ≫ Ψ.h₀ (Φ.s₀ j))
          (pairSnd B S hS 𝒰.X 𝒰.f i j ≫ (Φ.h₀ j ≫ Ψ.h₀ (Φ.s₀ j))) rfl
          (D.F (Ψ.s₀ (Φ.s₀ j))) :=
    rfl
  rw [hcomp, pullbackTransition, hcast,
    transitionOn_pullbackTransition B S hS Ψ D
      (Φ.s₀ i) (Φ.s₀ j) (familyPairMap B S hS Φ Φ i j)
      (pairFst B S hS 𝒰.X 𝒰.f i j ≫ Φ.h₀ i)
      (pairSnd B S hS 𝒰.X 𝒰.f i j ≫ Φ.h₀ j)
      (familyPairMap_fst B S hS Φ Φ i j) (familyPairMap_snd B S hS Φ Φ i j),
    transitionOn_congr_map B S hS 𝒲.X 𝒲.f D.F D.transition
      (Ψ.s₀ (Φ.s₀ i)) (Ψ.s₀ (Φ.s₀ j)) (familyPairMap_comp B S hS Φ Ψ hk i j)
      (pairFst B S hS 𝒰.X 𝒰.f i j ≫ (Φ.h₀ i ≫ Ψ.h₀ (Φ.s₀ i)))
      (pairSnd B S hS 𝒰.X 𝒰.f i j ≫ (Φ.h₀ j ≫ Ψ.h₀ (Φ.s₀ j)))
      (familyPairMap_fst B S hS (Φ.comp Ψ hk) (Φ.comp Ψ hk) i j)
      (familyPairMap_snd B S hS (Φ.comp Ψ hk) (Φ.comp Ψ hk) i j)
      (familyPairMap_comp_fst B S hS Φ Ψ hk i j)
      (familyPairMap_comp_snd B S hS Φ Ψ hk i j),
    pullbackDatumCompComparison_eq, pullbackDatumCompComparison_eq]
  simp only [pullbackComparison_rfl, Iso.symm_symm_eq]
  exact compIso_trans_cancel B S hS (pairFst B S hS 𝒰.X 𝒰.f i j) (Φ.h₀ i) (Ψ.h₀ (Φ.s₀ i))
    (pairSnd B S hS 𝒰.X 𝒰.f i j) (Φ.h₀ j) (Ψ.h₀ (Φ.s₀ j)) (D.F (Ψ.s₀ (Φ.s₀ i)))
    (D.F (Ψ.s₀ (Φ.s₀ j))) _

/-- **The pullback of a quasi-coherent descent datum along a composite of morphisms of families
is the composite of the two pullbacks.**  This is the pseudofunctoriality in the morphism of
families of the pullback of Stacks 04W4, and it carries no hypothesis: the associativity
coherence of the comparison of inverse images of Stacks 03LU that the compatibility rests on is
`AlgebraicGeometry.Space.modulePullbackCompIsoAssoc`. -/
def pullbackDatumCompIso (Φ : 𝒰.HomOver 𝒱 g) (Ψ : 𝒱.HomOver 𝒲 h) (hk : g ≫ h = k)
    (D : DescentDatum B S hS 𝒲.X 𝒲.f) :
    pullbackDatum B S hS Φ (pullbackDatum B S hS Ψ D) ≅
      pullbackDatum B S hS (Φ.comp Ψ hk) D :=
  DescentDatum.isoMkOfTransitionEq B S hS (pullbackDatumCompComparison B S hS Φ Ψ hk D)
    (fun i j => pullbackTransition B S hS Φ (pullbackDatum B S hS Ψ D) i j)
    (fun i j => pullbackTransition B S hS (Φ.comp Ψ hk) D i j)
    (pullbackDatum_transition B S hS Φ (pullbackDatum B S hS Ψ D))
    (pullbackDatum_transition B S hS (Φ.comp Ψ hk) D)
    (pullbackDatumCompComparison_transition B S hS Φ Ψ hk D)

end FamilyComp

end AlgebraicGeometry.Space.QuasiCoherentDescent

end
