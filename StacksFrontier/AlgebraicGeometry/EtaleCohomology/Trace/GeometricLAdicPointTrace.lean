module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.StalkComparisonNaturality
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GeometricFrobeniusClosedPointRational
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GeometricLAdicTower
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.PullbackStalkFrobenius
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.TraceFormulaDimensionOne
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LAdicSheaves.FrobeniusStalk
public import StacksFrontier.Homology.DerivedCategory.InverseSystem.SingleDegreeTrace
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.ShortExactTrace
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.RationalPointsDegreeOne
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The local terms of the trace formula for an ℓ-adic sheaf, level by level

For an ℓ-adic sheaf with levels `Fₙ`, a rational point `y` over a finite field and the closed point
`x` hit by `y`, the level-`n` local term at `y` of the trace formula of [Stacks, Tag 03V3] for `Fₙ`
placed in degree `0`, a trace of the geometric Frobenius of `y` on a stalk on Mathlib's small étale
site, is the trace of the action `frobeniusPointHom X x` on the finite-level stalk at `x` of the
bounded small étale site of [Stacks, Tag 021B].

## Main results

* `Stacks.EtaleCohomology.exists_finiteLevelStalk_iso_frobenius_comm`: the two stalks are
  isomorphic, compatibly with the two geometric Frobenius actions.
* `Stacks.EtaleCohomology.eval_perfectDerivedTrace_rationalPointStalkFrobenius_single`: the local
  term of a sheaf placed in degree `0` with finite free stalk is the ordinary trace on the stalk.
* `Stacks.EtaleCohomology.trace_finiteLevelStalkEnd_eq_eval_localTerm`: the trace of
  `frobeniusPointHom X x` on the level-`n` stalk is the level-`n` local term at `y`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.SmallEtale
open Stacks.Frobenius

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] moduleCat_hasLimitsOfSize

variable (B : BigEtaleSite.{u}) (X : B.Scheme) (ℓ : ℕ)

variable [∀ (n : ℕ) (S T : B.Scheme) (f : T ⟶ S),
  ((AlgebraicGeometry.smallEtaleBaseChange B f).sheafPushforwardContinuous
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
    (SmallEtale.topology B S.1 S.property)
    (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
variable [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
  HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
variable [∀ n : ℕ, HasWeakSheafify
  (SmallEtale.topology B X.1 X.property)
  (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
variable [IsNoetherian X.1] [Fact ℓ.Prime]

variable (x : X.1) [Finite (X.1.residueField x)] {k : Type u} [Field k] [Fintype k]
  (kbar : Type u) [Field kbar] [IsAlgClosed kbar] [Algebra k kbar] (p q : ℕ) [Fact p.Prime]
  [CharP kbar p]

/-- The comparison of the level-`n` stalk of an ℓ-adic sheaf at the geometric point at `x`, on
the bounded small étale site, with the stalk of its level on Mathlib's small étale site at the
geometric point over a rational point `y`, through a morphism `θ` of geometric points: the stalk
comparison of the two sites followed by the isomorphism of stalk functors induced by `θ`. -/
def finiteLevelStalkRationalPointIso (F : LAdicSheaf.{u, u + 1} B X ℓ) (n : ℕ)
    (y : Spec (.of k) ⟶ X.1)
    (θ : GeometricPoint.Hom (rationalGeometricPoint kbar y) (geometricPointAt X.1 x)) :
    finiteLevelStalk B X ℓ F (geometricPointAt X.1 x) n ≅
      (rationalPointStalkFunctor (ZMod (ℓ ^ (n + 1))) kbar y).obj
        (LAdicSheaf.etaleLevel B X ℓ F n) :=
  haveI := smallEtalePointHom_isIso X.1 θ
  ((sheafEquivCompSheafFiberIso.{u, u + 1, 0} B X (ZMod (ℓ ^ (n + 1)))
      (geometricPointAt X.1 x)).app (F.level n)).symm ≪≫
    (GrothendieckTopology.Point.sheafFiberIsoOfIso (A := ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (asIso (smallEtalePointHom X.1 θ))).app (LAdicSheaf.etaleLevel B X ℓ F n)

/-- **The geometric Frobenius at a closed point and at a rational point over it, level by
level.**  Let `x` be a point with finite residue field and `y` a rational point over a finite field
`k` with `#κ(x) = #k`, with a morphism `θ` from the geometric point over `y` to the geometric point
at `x`.  The level-`n` stalk of an ℓ-adic sheaf at the geometric point at `x`, on the bounded small
étale site, is isomorphic to the stalk of the level on Mathlib's small étale site at the geometric
point over `y`, by an isomorphism intertwining the geometric Frobenius `frobeniusPointHom X x` with
the geometric Frobenius of `y`.  The isomorphism is the stalk comparison of the two sites followed
by the isomorphism of stalk functors induced by `θ`; it intertwines the two actions, the stalk
comparison by its naturality in the geometric point, `θ` by
`Stacks.Frobenius.frobeniusStalkFunctor_comm_of_hom_to`. -/
@[sga "4½ Rapport 1.5" "special case"]
theorem exists_finiteLevelStalk_iso_frobenius_comm (hcard : Fintype.card k = p ^ q)
    (F : LAdicSheaf.{u, u + 1} B X ℓ) (n : ℕ) (y : Spec (.of k) ⟶ X.1)
    (θ : GeometricPoint.Hom (rationalGeometricPoint kbar y) (geometricPointAt X.1 x))
    (hres : Nat.card (X.1.residueField x) = Fintype.card k) :
    ∃ e : finiteLevelStalk B X ℓ F (geometricPointAt X.1 x) n ≅
        (rationalPointStalkFunctor (ZMod (ℓ ^ (n + 1))) kbar y).obj
          (LAdicSheaf.etaleLevel B X ℓ F n),
      finiteLevelStalkEnd B X ℓ F (frobeniusPointHom X.1 x) n ≫ e.hom =
        e.hom ≫ (geometricFrobeniusStalkFunctor (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1)))) kbar p q
          hcard y).app (LAdicSheaf.etaleLevel B X ℓ F n) := by
  have := smallEtalePointHom_isIso X.1 θ
  let e₁ := ((sheafEquivCompSheafFiberIso.{u, u + 1, 0} B X (ZMod (ℓ ^ (n + 1)))
      (geometricPointAt X.1 x)).app (F.level n)).symm
  let e₂ := (GrothendieckTopology.Point.sheafFiberIsoOfIso
      (A := ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (asIso (smallEtalePointHom X.1 θ))).app (LAdicSheaf.etaleLevel B X ℓ F n)
  have h₁ := congrArg (fun α => α.app (F.level n))
    (sheafEquivCompSheafFiberIso_inv_naturality.{u, u + 1, 0} B X (ZMod (ℓ ^ (n + 1)))
      (frobeniusPointHom X.1 x))
  have h₂ := congrArg (fun α => α.app (LAdicSheaf.etaleLevel B X ℓ F n))
    (frobeniusStalkFunctor_comm_of_hom_to (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1)))) X.1 x kbar
      p q hcard y θ hres)
  dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app] at h₁ h₂
  exact ⟨e₁ ≪≫ e₂, (congrArg (_ ≫ ·) (Iso.trans_hom e₁ e₂)).trans
    ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ e₂.hom) h₁.symm).trans
      ((Category.assoc _ _ _).trans ((congrArg (e₁.hom ≫ ·) h₂.symm).trans
        (Category.assoc _ _ _).symm))))⟩

/-- The trace of an endomorphism of a module is the trace of an endomorphism it is conjugate to
through an isomorphism in `ModuleCat`. -/
theorem trace_hom_eq_of_comm {R : Type*} [CommRing R] {M N : ModuleCat.{u + 1} R} (e : M ≅ N)
    (g : M ⟶ M) (g' : N ⟶ N) (h : g ≫ e.hom = e.hom ≫ g') :
    LinearMap.trace R M g.hom = LinearMap.trace R N g'.hom := by
  let e' := e.toLinearEquiv
  have hconj : e'.conj g.hom = g'.hom := by
    ext v
    have hv := congrArg (fun φ => φ.hom (e'.symm v)) h
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hv
    simp only [LinearEquiv.conj_apply, LinearMap.comp_apply, LinearEquiv.coe_coe]
    exact hv.trans (congrArg _ (e'.apply_symm_apply v))
  exact (LinearMap.trace_conj' _ e').symm.trans (congrArg _ hconj)

/-- The trace of the geometric Frobenius at a closed point on a level-`n` stalk of an ℓ-adic
sheaf on the bounded small étale site is the trace of the geometric Frobenius of a rational point
over it on the stalk of the level on Mathlib's small étale site. -/
theorem trace_finiteLevelStalkEnd_frobeniusPointHom (hcard : Fintype.card k = p ^ q)
    (F : LAdicSheaf.{u, u + 1} B X ℓ) (n : ℕ) (y : Spec (.of k) ⟶ X.1)
    (θ : GeometricPoint.Hom (rationalGeometricPoint kbar y) (geometricPointAt X.1 x))
    (hres : Nat.card (X.1.residueField x) = Fintype.card k) :
    LinearMap.trace (ZMod (ℓ ^ (n + 1))) _
        (finiteLevelStalkEnd B X ℓ F (frobeniusPointHom X.1 x) n).hom =
      LinearMap.trace (ZMod (ℓ ^ (n + 1))) _
        ((geometricFrobeniusStalkFunctor (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1)))) kbar p q hcard
          y).app (LAdicSheaf.etaleLevel B X ℓ F n)).hom := by
  obtain ⟨e, he⟩ := exists_finiteLevelStalk_iso_frobenius_comm B X ℓ x kbar p q hcard F n y θ hres
  exact trace_hom_eq_of_comm e _ _ he

section SingleDegree

open CategoryTheory.FilteredDerived Stacks.Trace

attribute [local instance] HasDerivedCategory.standard

variable {X' : Scheme.{u}} (Λ : Type) [CommRing Λ]

omit [Fintype k] in
/-- The geometric Frobenius on the stalk complex at a rational point of a sheaf placed in degree
`0` is, under the identification of that stalk complex with the stalk placed in degree `0`, the
geometric Frobenius on the stalk placed in degree `0`. -/
theorem rationalPointStalkFrobenius_single_comm [Fintype k] (hcard : Fintype.card k = p ^ q)
    (y : Spec (.of k) ⟶ X') (M : EtaleModules.{u, 0} Λ X') :
    rationalPointStalkFrobenius.{u, 0} Λ kbar p q hcard y
        ⟨(CochainComplex.singleFunctor _ 0).obj M, CochainComplex.plus_singleFunctor_obj _⟩ ≫
      ((HomologicalComplex.singleMapHomologicalComplex (rationalPointStalkFunctor.{u, 0} Λ kbar y)
        (ComplexShape.up ℤ) 0).app M).hom =
    ((HomologicalComplex.singleMapHomologicalComplex (rationalPointStalkFunctor.{u, 0} Λ kbar y)
        (ComplexShape.up ℤ) 0).app M).hom ≫
      (CochainComplex.singleFunctor _ 0).map
        ((geometricFrobeniusStalkFunctor (ModuleCat.{u + 1} Λ) kbar p q hcard y).app M) := by
  apply HomologicalComplex.to_single_hom_ext
  let S := rationalPointStalkFunctor.{u, 0} Λ kbar y
  let α := geometricFrobeniusStalkFunctor (ModuleCat.{u + 1} Λ) kbar p q hcard y
  let s := HomologicalComplex.singleObjXSelf (V := EtaleModules.{u, 0} Λ X')
    (ComplexShape.up ℤ) 0 M
  let s' := HomologicalComplex.singleObjXSelf (V := ModuleCat.{u + 1} Λ)
    (ComplexShape.up ℤ) 0 (S.obj M)
  have h₁ := HomologicalComplex.singleMapHomologicalComplex_hom_app_self S (ComplexShape.up ℤ) 0 M
  have h₂ := HomologicalComplex.single_map_f_self (V := ModuleCat.{u + 1} Λ)
    (ComplexShape.up ℤ) 0 (α.app M)
  refine (HomologicalComplex.comp_f _ _ 0).trans ?_
  refine (congrArg (α.app _ ≫ ·) h₁).trans ?_
  refine Eq.trans ?_ (congrArg (· ≫ _) h₁).symm
  refine Eq.trans ?_ (congrArg (_ ≫ ·) h₂).symm
  simp only [Category.assoc]
  exact (α.naturality_assoc s.hom s'.inv).symm

/-- A finite projective module placed in degree `0` is a perfect object of the derived category. -/
theorem isPerfect_Q_single_of_projective {R : Type} [CommRing R] (P : ModuleCat.{u + 1} R)
    [Module.Finite R P] [Module.Projective R P] :
    StacksDraft.Perfect.IsPerfect (DerivedCategory.Q.obj
      ((CochainComplex.singleFunctor (ModuleCat.{u + 1} R) 0).obj P)) := by
  have hs (i : ℤ) (hi : i ≠ 0) :
      Subsingleton (((CochainComplex.singleFunctor (ModuleCat.{u + 1} R) 0).obj P).X i) :=
    ModuleCat.subsingleton_of_isZero
      (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 P i hi)
  refine ⟨(CochainComplex.singleFunctor (ModuleCat.{u + 1} R) 0).obj P, 0, 0, inferInstance,
    inferInstance, fun i => ?_, fun i => ?_, ⟨Iso.refl _⟩⟩
  · by_cases hi : i = 0
    · subst hi
      exact Module.Finite.equiv
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 P).symm.toLinearEquiv
    · have := hs i hi
      exact Module.Finite.of_finite
  · by_cases hi : i = 0
    · subst hi
      exact Module.Projective.of_equiv
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 P).symm.toLinearEquiv
    · have := hs i hi
      exact Module.Projective.of_free

omit [Fintype k] in
/-- The stalk complex at a rational point of a sheaf placed in degree `0` whose stalk there is
finite free is perfect. -/
theorem isPerfect_rationalPointStalkComplex_single (y : Spec (.of k) ⟶ X')
    (M : EtaleModules.{u, 0} Λ X')
    [Module.Free Λ ((rationalPointStalkFunctor.{u, 0} Λ kbar y).obj M)]
    [Module.Finite Λ ((rationalPointStalkFunctor.{u, 0} Λ kbar y).obj M)] :
    StacksDraft.Perfect.IsPerfect (DerivedCategory.Q.obj
      (rationalPointStalkComplex.{u, 0} Λ kbar y
        ⟨(CochainComplex.singleFunctor _ 0).obj M, CochainComplex.plus_singleFunctor_obj _⟩)) := by
  obtain ⟨P, a, b, ha, hb, hf, hp, ⟨e'⟩⟩ :=
    isPerfect_Q_single_of_projective ((rationalPointStalkFunctor.{u, 0} Λ kbar y).obj M)
  exact ⟨P, a, b, ha, hb, hf, hp, ⟨DerivedCategory.Q.mapIso
    ((HomologicalComplex.singleMapHomologicalComplex (rationalPointStalkFunctor.{u, 0} Λ kbar y)
      (ComplexShape.up ℤ) 0).app M) ≪≫ e'⟩⟩

/-- **The local term of a sheaf placed in degree `0`.**  For a sheaf `M` of `Λ`-modules whose stalk
at the geometric point over a rational point `y` is finite free, the trace of the geometric
Frobenius on the stalk complex of `M` placed in degree `0`, evaluated in `Λ`, is the ordinary trace
of the geometric Frobenius on the stalk. -/
theorem eval_perfectDerivedTrace_rationalPointStalkFrobenius_single
    (hcard : Fintype.card k = p ^ q) (y : Spec (.of k) ⟶ X') (M : EtaleModules.{u, 0} Λ X')
    [Module.Free Λ ((rationalPointStalkFunctor.{u, 0} Λ kbar y).obj M)]
    [Module.Finite Λ ((rationalPointStalkFunctor.{u, 0} Λ kbar y).obj M)]
    (hM : StacksDraft.Perfect.IsPerfect (DerivedCategory.Q.obj
      (rationalPointStalkComplex.{u, 0} Λ kbar y
        ⟨(CochainComplex.singleFunctor _ 0).obj M, CochainComplex.plus_singleFunctor_obj _⟩))) :
    commutativeAdditiveCommutatorQuotientEval Λ (perfectDerivedTrace Λ ⟨_, hM⟩
        (DerivedCategory.Q.map (rationalPointStalkFrobenius.{u, 0} Λ kbar p q hcard y
          ⟨(CochainComplex.singleFunctor _ 0).obj M, CochainComplex.plus_singleFunctor_obj _⟩))) =
      LinearMap.trace Λ _
        ((geometricFrobeniusStalkFunctor (ModuleCat.{u + 1} Λ) kbar p q hcard y).app M).hom := by
  let e := DerivedCategory.Q.mapIso ((HomologicalComplex.singleMapHomologicalComplex
    (rationalPointStalkFunctor.{u, 0} Λ kbar y) (ComplexShape.up ℤ) 0).app M)
  have hM' : StacksDraft.Perfect.IsPerfect (DerivedCategory.Q.obj
      ((CochainComplex.singleFunctor (ModuleCat.{u + 1} Λ) 0).obj
        ((rationalPointStalkFunctor.{u, 0} Λ kbar y).obj M))) := by
    obtain ⟨P, a, b, ha, hb, hf, hp, ⟨e'⟩⟩ := hM
    exact ⟨P, a, b, ha, hb, hf, hp, ⟨e.symm ≪≫ e'⟩⟩
  rw [perfectDerivedTrace_congr Λ ⟨_, hM⟩ ⟨_, hM'⟩ e _
    (DerivedCategory.Q.map ((CochainComplex.singleFunctor (ModuleCat.{u + 1} Λ) 0).map
      ((geometricFrobeniusStalkFunctor (ModuleCat.{u + 1} Λ) kbar p q hcard y).app M)))
    ((DerivedCategory.Q.map_comp _ _).symm.trans
      ((congrArg DerivedCategory.Q.map
        (rationalPointStalkFrobenius_single_comm kbar p q Λ hcard y M)).trans
        (DerivedCategory.Q.map_comp _ _)))]
  exact eval_perfectDerivedTrace_single _ hM' _

/-- **The level-`n` local term of an ℓ-adic sheaf at a rational point.**  Let `y` be a rational
point of `X` over a finite field `k`, hitting the point `x`, of residue degree one.  If the
level-`n` stalk of an ℓ-adic sheaf at the geometric point at `x` is finite free over `ℤ/ℓⁿ⁺¹ℤ`,
the trace of the geometric Frobenius `frobeniusPointHom X x` on it is the local term at `y` of
[Stacks, Tag 03V3] for the level-`n` sheaf placed in degree `0`: the trace of the geometric
Frobenius of `y` on the stalk complex, evaluated in `ℤ/ℓⁿ⁺¹ℤ`. -/
theorem trace_finiteLevelStalkEnd_eq_eval_localTerm (hcard : Fintype.card k = p ^ q)
    (f : X.1 ⟶ Spec (.of k)) (F : LAdicSheaf.{u, u + 1} B X ℓ) (n : ℕ)
    (y : Spec (.of k) ⟶ X.1) (hy : (Scheme.SpecToEquivOfField k X.1 y).1 = x)
    (hdeg : residueDegree f x = 1)
    [Module.Free (ZMod (ℓ ^ (n + 1))) (finiteLevelStalk B X ℓ F (geometricPointAt X.1 x) n)]
    [Module.Finite (ZMod (ℓ ^ (n + 1))) (finiteLevelStalk B X ℓ F (geometricPointAt X.1 x) n)]
    (hM : StacksDraft.Perfect.IsPerfect (DerivedCategory.Q.obj
      (rationalPointStalkComplex.{u, 0} (ZMod (ℓ ^ (n + 1))) kbar y
        (LAdicSheaf.levelComplex B X ℓ F n)))) :
    LinearMap.trace (ZMod (ℓ ^ (n + 1))) _
        (finiteLevelStalkEnd B X ℓ F (frobeniusPointHom X.1 x) n).hom =
      commutativeAdditiveCommutatorQuotientEval (ZMod (ℓ ^ (n + 1)))
        (perfectDerivedTrace (ZMod (ℓ ^ (n + 1))) ⟨_, hM⟩
          (DerivedCategory.Q.map (rationalPointStalkFrobenius.{u, 0} (ZMod (ℓ ^ (n + 1))) kbar p q
            hcard y (LAdicSheaf.levelComplex B X ℓ F n)))) := by
  subst hy
  obtain ⟨e, he⟩ := exists_finiteLevelStalk_iso_frobenius_comm B X ℓ _ kbar p q hcard F n y
    (rationalGeometricPointHom kbar y)
    (natCard_residueField_of_residueDegree_eq_one f _ hdeg)
  have := Module.Free.of_equiv e.toLinearEquiv
  have := Module.Finite.equiv e.toLinearEquiv
  rw [trace_hom_eq_of_comm e _ _ he]
  exact (eval_perfectDerivedTrace_rationalPointStalkFrobenius_single kbar p q _ hcard y _ hM).symm

end SingleDegree

end Stacks.EtaleCohomology
