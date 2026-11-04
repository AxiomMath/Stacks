module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.StalkwiseCriterion
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.DerivedPushforwardStalkStrictHenselization
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedPushforwardStalkSpecialization
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GlobalSectionsAlongIsomorphism
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.StrictHenselizationStalkCohomology
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedExactFunctor
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ClosedPointDirectSumCohomology
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LocalAcyclicity.DerivedGlobalSectionsAdditive
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmoothBaseChange.LocalAcyclicity.ConstantRestriction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.ConstantPrimeToCharacteristicCurve
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Cohomology over strict henselizations of the two sides of a base change map

Consider the cartesian square
```
X  ←-h-  X ×_S T
|f          |e
S  ←-g-     T
```
with `g` quasi-compact and quasi-separated, an abelian sheaf `F` on `T_étale`, `q ≥ 0` and a
geometric point `x̄` of `X` with image `s̄`. If the base change map
`f⁻¹ R^q g_* F ⟶ R^q h_* e⁻¹ F` is an isomorphism, then

`H^q(Spec(𝒪^{sh}_{X,x̄}) ×_S T, F) ≅ H^q(Spec(𝒪^{sh}_{S,s̄}) ×_S T, F)`.

This is the existence half of what the source reads off Lemma 0EZU in the proof of
Proposition 0GJQ: the stalk of `f⁻¹ R^q g_* F` at `x̄` is the stalk of `R^q g_* F` at `s̄`, which
is `H^q(T ×_S Spec(𝒪^{sh}_{S,s̄}), F)` by Tag 03Q9, and the stalk of `R^q h_* e⁻¹ F` at `x̄` is
`H^q((X ×_S T) ×_X Spec(𝒪^{sh}_{X,x̄}), e⁻¹F)` by Tag 03Q9 again; the base change map is an
isomorphism on stalks by Tag 0EZU. Only the existence of an isomorphism is asserted: the proof
of 0GJQ combines it with a computation on the closed fibre which identifies the canonical map.

The statements are about the unbounded derived functors of the small étale site
(`Stacks.EtaleCohomology.smallEtaleDerivedGlobalSections` and its companions), which are defined
in the model `HasDerivedCategory.standard`; that model is therefore the local instance here.

## Main results

* `Stacks.EtaleCohomology.homologyDerivedSectionsPullbackIsoOfIso` — derived sections of an
  inverse image along an isomorphism of schemes over the base.
* `Stacks.EtaleCohomology.stalkRightDerivedPushforwardIsoStrictHenselization` — Tag 03Q9 for the
  classical higher direct images `R^q g_* F`.
* `Stacks.EtaleCohomology.nonempty_homology_strictHenselization_iso_of_isIso_higherBaseChangeMapAb`
  — the isomorphism displayed above.

## References

* [Stacks Project, Tag 0EZU](https://stacks.math.columbia.edu/tag/0EZU)
* [Stacks Project, Tag 03Q9](https://stacks.math.columbia.edu/tag/03Q9)
* [Stacks Project, Tag 0GJQ](https://stacks.math.columbia.edu/tag/0GJQ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

section Transport

variable {Z A A' : Scheme.{u}}

/-- **Derived sections of an inverse image along an isomorphism of schemes over the base.** For an
isomorphism `φ : A ≅ A'` of schemes over `Z`, with structure morphisms `a` and `a'`, and an
object `K` of `D(Z_étale)`, the degree-`q` cohomology of `RΓ(A, a⁻¹K)` is that of
`RΓ(A', a'⁻¹K)`: restriction along `φ` is invertible, and `φ⁻¹ a'⁻¹ K = a⁻¹ K`. -/
def homologyDerivedSectionsPullbackIsoOfIso (φ : A ≅ A') {a : A ⟶ Z} {a' : A' ⟶ Z}
    (hφ : φ.hom ≫ a' = a) (K : smallEtaleDerivedCategory Z) (q : ℤ) :
    (DerivedCategory.homologyFunctor Ab.{u + 1} q).obj
        ((smallEtaleDerivedGlobalSections A).obj ((smallEtaleDerivedPullbackAb a).obj K)) ≅
      (DerivedCategory.homologyFunctor Ab.{u + 1} q).obj
        ((smallEtaleDerivedGlobalSections A').obj ((smallEtaleDerivedPullbackAb a').obj K)) :=
  haveI := isIso_smallEtaleDerivedGlobalSectionsRestriction φ.hom
  (DerivedCategory.homologyFunctor Ab.{u + 1} q).mapIso
    ((smallEtaleDerivedGlobalSections A).mapIso
        ((smallEtaleDerivedPullbackAbCompIsoQhLift
            (smallEtalePullbackAbCompIso φ.hom a')).app K ≪≫
          (eqToIso (congrArg (fun m : A ⟶ Z => smallEtaleDerivedPullbackAb m) hφ)).app K).symm ≪≫
      (asIso ((smallEtaleDerivedGlobalSectionsRestriction φ.hom).app
        ((smallEtaleDerivedPullbackAb a').obj K))).symm)

end Transport

section Stalk

variable (B : BigEtaleSite.{u}) {T S : Scheme.{u}} (hS : B.Contains S) (g : T ⟶ S)
  [QuasiCompact g] [QuasiSeparated g] (s : GeometricPoint S)

/-- **Tag 03Q9 for the classical higher direct images.** For `g : T ⟶ S` quasi-compact and
quasi-separated, a geometric point `s` of `S` and an abelian sheaf `F` on `T_étale`,
`(R^q g_* F)_s ≅ H^q(T ×_S Spec 𝒪^{sh}_{S,s}, p⁻¹F)`, the left side being the `q`-th right
derived functor of direct image (`CategoryTheory.Functor.rightDerived`). -/
@[sga "4 IX 4.1.1" "more general", sga "4 VIII 5.2", sga "4½ Arcata 2.3.3" "special case"]
def stalkRightDerivedPushforwardIsoStrictHenselization
    (F : Sheaf (smallEtaleTopology T) Ab.{u + 1}) (q : ℕ) :
    (smallEtaleStalkAb s.hom).obj (((smallEtalePushforwardAb g).rightDerived q).obj F) ≅
      (DerivedCategory.homologyFunctor Ab.{u + 1} (q : ℤ)).obj
        ((smallEtaleDerivedGlobalSections (strictHenselizationBaseChange B hS g s)).obj
          ((smallEtaleDerivedPullbackAb (strictHenselizationBaseChangeToSource B hS g s)).obj
            ((DerivedCategory.singleFunctor _ 0).obj F))) :=
  haveI := isGrothendieckAbelian_sheaf_smallEtale_objectUniverse T
  (smallEtaleStalkAb s.hom).mapIso
      (Stacks.DerivedFunctor.homologyTotalRightDerivedSingleIso (smallEtalePushforwardAb g)
        (smallEtaleDerivedPushforwardAb g) (smallEtaleDerivedPushforwardAbUnit g)
        (Stacks.DerivedFunctor.exists_quasiIso_isKInjective.{u + 1, u + 2}) F q).symm ≪≫
    stalkDerivedPushforwardHomologyIsoStrictHenselization B hS g s
      ((DerivedCategory.singleFunctor _ 0).obj F) 0 (q : ℤ)

end Stalk

section SeparablyClosed

/-- **Derived sections over the spectrum of a separably closed field have no higher cohomology.**
Global sections there are an equivalence onto the coefficients
(`Stacks.EtaleCohomology.isEquivalence_sheafSections_final_of_isSepClosed`), hence exact, so their
higher right derived functors vanish. -/
@[sga "4 VIII 2.4"]
theorem isZero_homology_smallEtaleDerivedGlobalSections_single_of_isSepClosed (k : Type u)
    [Field k] [IsSepClosed k] (G : Sheaf (smallEtaleTopology (Spec (.of k))) Ab.{u + 1}) (q : ℕ)
    (hq : 0 < q) :
    IsZero ((DerivedCategory.homologyFunctor Ab.{u + 1} (q : ℤ)).obj
      ((smallEtaleDerivedGlobalSections (Spec (.of k))).obj
        ((DerivedCategory.singleFunctor _ 0).obj G))) := by
  have := isGrothendieckAbelian_sheaf_smallEtale_objectUniverse (Spec (.of k))
  have := isEquivalence_sheafSections_final_of_isSepClosed k Ab.{u + 1}
  have : PreservesFiniteColimits (Sheaf.Γ (smallEtaleTopology (Spec (.of k))) Ab.{u + 1}) :=
    preservesFiniteColimits_of_natIso
      (Sheaf.ΓNatIsoSheafSections (smallEtaleTopology (Spec (.of k))) Ab.{u + 1}
        (isTerminalEtaleMkId _)).symm
  exact (Functor.isZero_rightDerived_of_exact (Sheaf.Γ (smallEtaleTopology (Spec (.of k)))
      Ab.{u + 1}) G q hq).of_iso
    (Stacks.DerivedFunctor.homologyTotalRightDerivedSingleIso
      (Sheaf.Γ (smallEtaleTopology (Spec (.of k))) Ab.{u + 1})
      (smallEtaleDerivedGlobalSections (Spec (.of k)))
      (smallEtaleDerivedGlobalSectionsUnit (Spec (.of k)))
      (Stacks.DerivedFunctor.exists_quasiIso_isKInjective.{u + 1, u + 2}) G q)

/-- **Degree-zero derived sections of a constant sheaf over the spectrum of a separably closed
field are its value**: degree-zero cohomology of `RΓ` at a sheaf is global sections, and the
constants are the global sections of the constant sheaf there. -/
def homologyZeroSmallEtaleDerivedGlobalSectionsConstantIso (k : Type u) [Field k]
    [IsSepClosed k] (A : Ab.{u + 1}) :
    (DerivedCategory.homologyFunctor Ab.{u + 1} ((0 : ℕ) : ℤ)).obj
      ((smallEtaleDerivedGlobalSections (Spec (.of k))).obj
        (smallEtaleConstantComplexAb (Spec (.of k)) A)) ≅ A :=
  haveI := isGrothendieckAbelian_sheaf_smallEtale_objectUniverse (Spec (.of k))
  haveI := isIso_constantSheafAdj_unit_app_of_isSepClosed k A
  Stacks.DerivedFunctor.homologyTotalRightDerivedSingleIso
      (Sheaf.Γ (smallEtaleTopology (Spec (.of k))) Ab.{u + 1})
      (smallEtaleDerivedGlobalSections (Spec (.of k)))
      (smallEtaleDerivedGlobalSectionsUnit (Spec (.of k)))
      (Stacks.DerivedFunctor.exists_quasiIso_isKInjective.{u + 1, u + 2})
      ((constantSheaf (smallEtaleTopology (Spec (.of k))) Ab.{u + 1}).obj A) 0 ≪≫
    (Sheaf.Γ (smallEtaleTopology (Spec (.of k))) Ab.{u + 1}).rightDerivedZeroIsoSelf.app _ ≪≫
    (Sheaf.ΓNatIsoSheafSections (smallEtaleTopology (Spec (.of k))) Ab.{u + 1}
      (isTerminalEtaleMkId _)).app _ ≪≫
    (asIso ((constantSheafAdj (smallEtaleTopology (Spec (.of k))) Ab.{u + 1}
      (isTerminalEtaleMkId _)).unit.app A)).symm

/-- Restriction to a nonempty scheme `Q` from a scheme `P ≅ Spec Ω`, `Ω` algebraically closed, is
injective on the cohomology of a constant sheaf: it is split by restriction to a geometric
point. -/
private theorem injective_homology_smallEtaleDerivedGlobalSectionsRestriction_of_nonempty
    {Q P : Scheme.{u}} (m : Q ⟶ P) {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (σ : P ⟶ Spec (.of Ω)) [IsIso σ] (A : Ab.{u + 1}) (q : ℤ) [Nonempty Q] :
    Function.Injective ((DerivedCategory.homologyFunctor Ab.{u + 1} q).map
      ((smallEtaleDerivedGlobalSectionsRestriction m).app (smallEtaleConstantComplexAb P A))) := by
  let H := DerivedCategory.homologyFunctor Ab.{u + 1} q
  have := isIso_smallEtaleDerivedGlobalSectionsRestriction σ
  obtain ⟨y⟩ := ‹Nonempty Q›
  let Ω' := AlgebraicClosure (Q.residueField y)
  let v : Spec (.of Ω') ⟶ Q :=
    Spec.map (CommRingCat.ofHom (algebraMap (Q.residueField y) Ω')) ≫ Q.fromSpecResidueField y
  have := StrictlyHenselianLocalRing.of_isSepClosed Ω
  have hw : IsIso ((smallEtaleDerivedGlobalSectionsRestriction ((v ≫ m) ≫ σ)).app
      (smallEtaleConstantComplexAb (Spec (.of Ω)) A)) :=
    isIso_smallEtaleDerivedGlobalSectionsRestriction_app_constantComplex_of_strictlyHenselian
      (R := Ω) (𝟙 _) (Subsingleton.elim _ _) _ A
  have : IsIso ((smallEtaleDerivedGlobalSectionsRestriction (v ≫ m)).app
      (smallEtaleConstantComplexAb P A)) :=
    (isIso_smallEtaleDerivedGlobalSectionsRestriction_comp_app_constantComplex_iff (v ≫ m) σ
      A).1 hw
  obtain ⟨τ, hτ⟩ : ∃ τ, (smallEtaleDerivedGlobalSectionsRestriction (v ≫ m)).app
      (smallEtaleConstantComplexAb P A) =
        (smallEtaleDerivedGlobalSectionsRestriction m).app (smallEtaleConstantComplexAb P A) ≫ τ :=
    ⟨_, by rw [smallEtaleDerivedGlobalSectionsRestriction_comp]; rfl⟩
  let ρ := (smallEtaleDerivedGlobalSectionsRestriction m).app (smallEtaleConstantComplexAb P A)
  have : IsIso (ρ ≫ τ) := by
    rw [← hτ]
    infer_instance
  refine Function.Injective.of_comp (f := H.map τ) ?_
  simpa using (ConcreteCategory.bijective_of_isIso (H.map (ρ ≫ τ))).1

/-- **Restriction to a scheme `Q` from a scheme `P ≅ Spec Ω`, `Ω` algebraically closed, is
invertible on the cohomology of a finite constant sheaf as soon as the two cohomology groups are
isomorphic.** Restriction from `P` to a geometric point of `Q` is invertible on constant
coefficients (both are the spectra of separably closed fields up to isomorphism), so restriction
from `P` to `Q` is a split monomorphism; in positive degrees the source vanishes, and in degree
zero it is the finite group `A`, so an injection into an isomorphic group is bijective. If `Q` is
empty both groups vanish. -/
theorem isIso_homology_smallEtaleDerivedGlobalSectionsRestriction_of_iso
    {Q P : Scheme.{u}} (m : Q ⟶ P) {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (σ : P ⟶ Spec (.of Ω)) [IsIso σ] (A : Ab.{u + 1}) [Finite A] (q : ℕ)
    (E : (DerivedCategory.homologyFunctor Ab.{u + 1} (q : ℤ)).obj
        ((smallEtaleDerivedGlobalSections Q).obj
          ((smallEtaleDerivedPullbackAb m).obj (smallEtaleConstantComplexAb P A))) ≅
      (DerivedCategory.homologyFunctor Ab.{u + 1} (q : ℤ)).obj
        ((smallEtaleDerivedGlobalSections P).obj (smallEtaleConstantComplexAb P A))) :
    IsIso ((DerivedCategory.homologyFunctor Ab.{u + 1} (q : ℤ)).map
      ((smallEtaleDerivedGlobalSectionsRestriction m).app (smallEtaleConstantComplexAb P A))) := by
  let H := DerivedCategory.homologyFunctor Ab.{u + 1} (q : ℤ)
  have := isIso_smallEtaleDerivedGlobalSectionsRestriction σ
  let eP : (smallEtaleDerivedGlobalSections P).obj (smallEtaleConstantComplexAb P A) ≅
      (smallEtaleDerivedGlobalSections (Spec (.of Ω))).obj
        (smallEtaleConstantComplexAb (Spec (.of Ω)) A) :=
    (smallEtaleDerivedGlobalSections P).mapIso
        (smallEtaleDerivedPullbackAbConstantComplexIso σ A).symm ≪≫
      (asIso ((smallEtaleDerivedGlobalSectionsRestriction σ).app
        (smallEtaleConstantComplexAb (Spec (.of Ω)) A))).symm
  by_cases hQ : IsEmpty Q
  · have hQz : IsZero (H.obj ((smallEtaleDerivedGlobalSections Q).obj
        ((smallEtaleDerivedPullbackAb m).obj (smallEtaleConstantComplexAb P A)))) := by
      refine H.map_isZero ((smallEtaleDerivedGlobalSections Q).map_isZero ?_)
      refine IsZero.of_iso ?_ (smallEtaleDerivedPullbackAbConstantComplexIso m A)
      exact (DerivedCategory.singleFunctor _ 0).map_isZero (isZero_of_isEmpty.{u, 0} _)
    exact (hQz.of_iso E.symm).isIso hQz _
  have : Nonempty Q := not_isEmpty_iff.mp hQ
  have hinj := injective_homology_smallEtaleDerivedGlobalSectionsRestriction_of_nonempty m σ A q
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · let eA : H.obj ((smallEtaleDerivedGlobalSections P).obj (smallEtaleConstantComplexAb P A)) ≅
        A := H.mapIso eP ≪≫ homologyZeroSmallEtaleDerivedGlobalSectionsConstantIso Ω A
    have : Finite (H.obj ((smallEtaleDerivedGlobalSections P).obj
        (smallEtaleConstantComplexAb P A))) :=
      Finite.of_equiv _ eA.symm.addCommGroupIsoToAddEquiv.toEquiv
    rw [ConcreteCategory.isIso_iff_bijective]
    exact ⟨hinj, (Finite.injective_iff_surjective_of_equiv
      E.symm.addCommGroupIsoToAddEquiv.toEquiv).1 hinj⟩
  · have hPz : IsZero (H.obj ((smallEtaleDerivedGlobalSections P).obj
        (smallEtaleConstantComplexAb P A))) :=
      (isZero_homology_smallEtaleDerivedGlobalSections_single_of_isSepClosed Ω _ q hq).of_iso
        (H.mapIso eP)
    exact hPz.isIso (hPz.of_iso E) _

end SeparablyClosed

section Main

variable (B : BigEtaleSite.{u}) {X S T : Scheme.{u}} (hX : B.Contains X) (hS : B.Contains S)
  (f : X ⟶ S) (g : T ⟶ S) [QuasiCompact g] [QuasiSeparated g] (x : GeometricPoint X)
  (F : Sheaf (smallEtaleTopology T) Ab.{u + 1}) (q : ℕ)

/-- **The two cohomology groups of Lemma 0EZU agree when the base change map is invertible.** In
the cartesian square `X ← X ×_S T → T` over `g : T ⟶ S` quasi-compact and quasi-separated, if
the base change map `f⁻¹ R^q g_* F ⟶ R^q h_* e⁻¹ F` is an isomorphism at an abelian sheaf `F` on
`T_étale`, then for every geometric point `x̄` of `X` with image `s̄`

`H^q(Spec(𝒪^{sh}_{X,x̄}) ×_S T, F) ≅ H^q(Spec(𝒪^{sh}_{S,s̄}) ×_S T, F)`.

The isomorphism is the composite of Tag 03Q9 for `h` at `x̄`, the stalk at `x̄` of the base change
map, the identification `(f⁻¹G)_{x̄} = G_{s̄}` (Tag 03Q1) and Tag 03Q9 for `g` at `s̄`, read
through the isomorphisms `(X ×_S T) ×_X Spec(𝒪^{sh}_{X,x̄}) ≅ Spec(𝒪^{sh}_{X,x̄}) ×_S T` and
`T ×_S Spec(𝒪^{sh}_{S,s̄}) ≅ Spec(𝒪^{sh}_{S,s̄}) ×_S T` over `T`. -/
theorem nonempty_homology_strictHenselization_iso_of_isIso_higherBaseChangeMapAb
    (hbc : IsIso ((higherBaseChangeMapAb f g (pullback.fst f g) (pullback.snd f g)
      pullback.condition q).app F)) :
    Nonempty ((DerivedCategory.homologyFunctor Ab.{u + 1} (q : ℤ)).obj
        ((smallEtaleDerivedGlobalSections
            (pullback (strictHenselizationToBase B X hX x ≫ f) g)).obj
          ((smallEtaleDerivedPullbackAb
              (pullback.snd (strictHenselizationToBase B X hX x ≫ f) g)).obj
            ((DerivedCategory.singleFunctor _ 0).obj F))) ≅
      (DerivedCategory.homologyFunctor Ab.{u + 1} (q : ℤ)).obj
        ((smallEtaleDerivedGlobalSections
            (pullback (strictHenselizationToBase B S hS (x.map f)) g)).obj
          ((smallEtaleDerivedPullbackAb
              (pullback.snd (strictHenselizationToBase B S hS (x.map f)) g)).obj
            ((DerivedCategory.singleFunctor _ 0).obj F)))) := by
  let πX := strictHenselizationToBase B X hX x
  let πS := strictHenselizationToBase B S hS (x.map f)
  let h := pullback.fst f g
  let e := pullback.snd f g
  let φ : pullback (πX ≫ f) g ≅ pullback h πX :=
    (pullbackRightPullbackFstIso f g πX).symm ≪≫ pullbackSymmetry πX h
  have hφ : φ.hom ≫ (pullback.fst h πX ≫ e) = pullback.snd (πX ≫ f) g := by
    simp [φ, h, e]
  let cX : (smallEtaleDerivedPullbackAb (pullback.fst h πX ≫ e)).obj
        ((DerivedCategory.singleFunctor _ 0).obj F) ≅
      (smallEtaleDerivedPullbackAb (pullback.fst h πX)).obj
        ((DerivedCategory.singleFunctor _ 0).obj ((smallEtalePullbackAb e).obj F)) :=
    ((smallEtaleDerivedPullbackAbCompIsoQhLift
        (smallEtalePullbackAbCompIso (pullback.fst h πX) e)).app _).symm ≪≫
      (smallEtaleDerivedPullbackAb (pullback.fst h πX)).mapIso
        (((smallEtalePullbackAb e).mapDerivedCategorySingleFunctor 0).app F)
  let e1 := homologyDerivedSectionsPullbackIsoOfIso φ hφ
      ((DerivedCategory.singleFunctor _ 0).obj F) (q : ℤ) ≪≫
    (DerivedCategory.homologyFunctor Ab.{u + 1} (q : ℤ)).mapIso
      ((smallEtaleDerivedGlobalSections (pullback h πX)).mapIso cX)
  let e2 := (stalkRightDerivedPushforwardIsoStrictHenselization B hX h x
    ((smallEtalePullbackAb e).obj F) q).symm
  let e3 := (asIso ((smallEtaleStalkAb x.hom).map
    ((higherBaseChangeMapAb f g h e pullback.condition q).app F))).symm
  let e4 := (smallEtalePullbackStalkAbIso f x.hom).app
    (((smallEtalePushforwardAb g).rightDerived q).obj F)
  let e5 := stalkRightDerivedPushforwardIsoStrictHenselization B hS g (x.map f) F q
  let e6 := homologyDerivedSectionsPullbackIsoOfIso (pullbackSymmetry g πS)
    (pullbackSymmetry_hom_comp_snd g πS) ((DerivedCategory.singleFunctor _ 0).obj F) (q : ℤ)
  exact ⟨e1 ≪≫ e2 ≪≫ e3 ≪≫ e4 ≪≫ e5 ≪≫ e6⟩

end Main

end Stacks.EtaleCohomology
