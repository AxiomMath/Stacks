module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleSheaves.ProperSmoothCurveSplitting
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PullbackStalk.SmallEtaleSpecializationBridge
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PullbackStalk.SpecializationFiniteLocallyConstant
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LocalAcyclicity.SmoothProperSpecializationHigherDirectImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.ProperCurveFamilyStalkFinite
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteLocallyConstantIsConstructible
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FirstCohomologyKilling.FiniteEtaleCover
public import StacksFrontier.CategoryTheory.Sites.LocallyConstant.AbelianUnderlyingSets
public import StacksFrontier.CategoryTheory.Sites.Point.ConstantSheafFiber

/-!
# [Stacks, Tag 0GKV] over a Noetherian base

Let `S` be a Noetherian scheme, `f : X ⟶ S` a proper smooth morphism with geometrically connected
fibres of dimension at most one and `ℓ` a prime. Then `Rᵠ f_* 𝐙/ℓ` is a constructible sheaf of
`𝔽_ℓ`-modules on `S_étale`, for every `q`.

This is the second paragraph of the proof of [Stacks, Tag 0GKV]. The base splits as the open
locus where `ℓ` is invertible and the closed locus where it vanishes (in `Stacks.EtaleCohomology`,
see `isConstructibleEtaleModule_rightDerivedConstantUnit_of_isNoetherian_of_invertible`); the
second is case (b) of the source; the first is case (a), proved here.

**Case (a).** If `ℓ` is invertible on `S`, then `Rᵠ f_* 𝐙/ℓ` is finite locally constant. Its stalks
are finite by proper base change and finiteness ([Stacks, Tags 0DDF and 03SC],
`Stacks.EtaleCohomology.finite_smallEtaleStalkAb_rightDerived_constantSheaf_of_isProper`), and
its specialization maps are bijective ([Stacks, Tag 0GKD],
`AlgebraicGeometry.isIso_specializationMap_of_smooth_of_isProper_unconditional`, read on the
cohomology sheaves). On a scheme whose quasi-compact opens have finitely many irreducible
components this makes the underlying sheaf of sets finite locally constant
([Stacks, Tag 0GJ7], the form of [Stacks, Tag 0GKC] for sheaves of sets), hence the abelian
sheaf finite locally constant (`Stacks.ConstantSheaf.isFiniteLocallyConstant_of_forget`), hence
constructible; a sheaf of `𝔽_ℓ`-modules whose underlying abelian sheaf is constructible is
constructible.

## Main results

* `Stacks.EtaleCohomology.isConstructibleEtaleModule_rightDerivedConstantUnit_of_isUnit`:
  case (a) of [Stacks, Tag 0GKV], over a Noetherian base.
* `Stacks.EtaleCohomology.isConstructibleEtaleModule_rightDerivedConstantUnit_of_isNoetherian`:
  [Stacks, Tag 0GKV] over a Noetherian base (unregistered: the tag allows any base).
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] moduleCat_hasLimitsOfSize SmallEtale.hasWeakSheafify_over_moduleCat_ring
  SmallEtale.isRightAdjoint_smallEtalePushforward_moduleCat_ring

/-- The torsion condition of [Stacks, Tag 0GKD] for the constant sheaf `𝐙/ℓ` on a scheme over
which `ℓ` is invertible: every element of every stalk is killed by `ℓ`, which is prime to the
characteristic of the residue field of the geometric point. -/
theorem constantSheaf_zmod_stalk_torsion {X : Scheme.{u}} (ℓ : ℕ) [Fact ℓ.Prime]
    (hℓ : IsUnit ((ℓ : ℕ) : Γ(X, ⊤))) (x : GeometricPoint X)
    (a : (smallEtaleStalkAb x.hom).obj
      ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
        (AddCommGrpCat.of (ULift.{u + 1} (ZMod ℓ))))) :
    ∃ n : ℕ, 0 < n ∧
      (ringChar x.residueField = 0 ∨ Nat.Coprime n (ringChar x.residueField)) ∧ n • a = 0 := by
  have hp : ℓ.Prime := Fact.out
  refine ⟨ℓ, hp.pos, ?_, ?_⟩
  · have hu : IsUnit (ℓ : x.residueField) := by
      have h1 := isUnit_natCast_of_hom x.hom hℓ
      rw [natCast_ΓSpec] at h1
      have h2 := h1.map (Scheme.ΓSpecIso (CommRingCat.of x.residueField)).hom.hom
      rwa [← CategoryTheory.comp_apply, Iso.inv_hom_id, CategoryTheory.id_apply] at h2
    rcases CharP.char_is_prime_or_zero x.residueField (ringChar x.residueField) with hc | hc
    · refine Or.inr ((Nat.coprime_primes hp hc).2 fun h => ?_)
      have : ((ℓ : ℕ) : x.residueField) = 0 := by
        rw [h]
        exact ringChar.Nat.cast_ringChar
      exact hu.ne_zero this
    · exact Or.inl hc
  · let e := (Sites.constantSheafFiberNatIso (D := AddCommGrpCat.{u + 1})
      (Scheme.pointSmallEtale x.hom)).app (AddCommGrpCat.of (ULift.{u + 1} (ZMod ℓ)))
    let ε := e.addCommGroupIsoToAddEquiv
    apply ε.injective
    rw [map_nsmul, map_zero]
    apply ULift.ext
    change ℓ • (ε a).down = 0
    rw [nsmul_eq_mul, ZMod.natCast_self, zero_mul]

section CaseA

variable (B : BigEtaleSite.{u}) {X S : B.Scheme} (f : X.obj ⟶ S.obj) [IsProper f] [Smooth f]
  (hdim : ∀ s : S.obj, topologicalKrullDim (f.fiber s) ≤ 1) [IsNoetherian S.obj]
  (ℓ : ℕ) [Fact ℓ.Prime] (q : ℕ)

include hdim in
/-- **[Stacks, Tag 0GKV], case (a), over a Noetherian base.** Let `S` be a Noetherian scheme on
which the prime `ℓ` is invertible and `f : X ⟶ S` proper and smooth with fibres of dimension at
most one. Then `Rᵠ f_* 𝐙/ℓ` is a constructible sheaf of `𝔽_ℓ`-modules for every `q`: its underlying
abelian sheaf is finite locally constant, its stalks being finite ([Stacks, Tags 0DDF, 03SC]) and
its specialization maps bijective ([Stacks, Tag 0GKD]), by [Stacks, Tag 0GJ7]. -/
theorem isConstructibleEtaleModule_rightDerivedConstantUnit_of_isUnit
    (hℓ : IsUnit ((ℓ : ℕ) : Γ(S.obj, ⊤))) :
    IsBigSiteConstructibleEtaleModule B S (ZMod ℓ) (rightDerivedConstantUnit f q (ZMod ℓ)) := by
  have hp : ℓ.Prime := Fact.out
  have : NeZero ℓ := ⟨hp.ne_zero⟩
  have := SmallEtale.isRightAdjoint_smallEtalePushforward_addCommGrpCat.{u, 0} B
  have := SmallEtale.hasWeakSheafify_over_addCommGrpCat.{u, 0} B
  let A := AddCommGrpCat.of (ULift.{u + 1} (ZMod ℓ))
  have : Finite A := inferInstanceAs (Finite (ULift.{u + 1} (ZMod ℓ)))
  let C := (constantSheaf X.obj.smallEtaleTopology AddCommGrpCat.{u + 1}).obj A
  let K := ((etaleAbelianDirectImage.{u, 0} f).rightDerived q).obj C
  refine Stacks.ArtinSchreier.isConstructibleEtaleModule_zmod_of_forget B S ℓ _ K
    (rightDerivedConstantUnitForgetIso f q (ZMod ℓ)) ?_
  -- the sheaf of sets underlying the transport of `K` is finite locally constant (Tag 0GJ7)
  have hScomp : ∀ V : S.obj.Opens, IsCompact (V : Set S.obj) →
      (irreducibleComponents V).Finite := fun V _ =>
    TopologicalSpace.NoetherianSpace.finite_irreducibleComponents
  have hlc : Stacks.ConstantSheaf.IsLocallyConstant X.obj.smallEtaleTopology C := by
    have := isFiniteLocallyConstant_constantSheaf_smallEtale X.obj A
    infer_instance
  have hset := isFiniteLocallyConstant_of_finite_etaleStalk_of_bijective_specializationMap B S.obj
    S.property hScomp (forgetSheafTransport B S.obj S.property K)
    (fun s => finite_etaleStalk_transport B S.obj S.property K s
      (finite_smallEtaleStalkAb_rightDerived_constantSheaf_of_isProper f hdim s A q))
    (fun s σ => by
      rw [geometricSpecialization_eq_ofPoint B S.obj S.property σ]
      exact bijective_specializationMapOnStalks_transport B S.obj S.property K s σ.point
        (isIso_smallEtaleSpecializationStalkAb_app_rightDerived_of_smooth_of_isProper B S.obj
          S.property s σ.point X.property f C hlc
          (fun x a => constantSheaf_zmod_stalk_torsion ℓ (isUnit_natCast_of_hom f hℓ) x a) q))
  have := Stacks.ConstantSheaf.isFiniteLocallyConstant_of_forget _
    ((SmallEtale.sheafEquiv B S.obj S.property AddCommGrpCat.{u + 1}).inverse.obj K) hset
  exact isConstructibleAbelianSheaf_of_isFiniteLocallyConstant B S _

end CaseA

section Noetherian

variable (B : BigEtaleSite.{u}) {X S : B.Scheme} (f : X.obj ⟶ S.obj) [IsProper f] [Smooth f]
  [GeometricallyConnected f] (hdim : ∀ s : S.obj, topologicalKrullDim (f.fiber s) ≤ 1)
  [IsNoetherian S.obj] (ℓ : ℕ) [Fact ℓ.Prime] (q : ℕ)

include hdim in
/-- **[Stacks, Tag 0GKV] over a Noetherian base.** Let `S` be a Noetherian scheme, `f : X ⟶ S` a
proper smooth morphism with geometrically connected fibres of dimension at most one, and `ℓ` a
prime. Then `Rᵠ f_* 𝐙/ℓ` is a constructible sheaf of `𝔽_ℓ`-modules on `S_étale` for every `q`.

Not registered under the tag, whose statement allows any base `S`: this is the Noetherian case to
which the source reduces by absolute Noetherian approximation. -/
theorem isConstructibleEtaleModule_rightDerivedConstantUnit_of_isNoetherian :
    IsBigSiteConstructibleEtaleModule B S (ZMod ℓ) (rightDerivedConstantUnit f q (ZMod ℓ)) :=
  isConstructibleEtaleModule_rightDerivedConstantUnit_of_isNoetherian_of_invertible B f hdim ℓ q
    (fun X' S' f' _ _ _ hdim' hN hu => by
      have := hN
      exact isConstructibleEtaleModule_rightDerivedConstantUnit_of_isUnit B f' hdim' ℓ q hu)

end Noetherian

end Stacks.EtaleCohomology

end
