module

public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Dimension.Localization
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.RingTheory.Artinian.Module
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Localization.Free
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFreeRank.AffineTarget
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteLocallyFreeOfRank
public import StacksFrontier.AlgebraicGeometry.Morphisms.QuasiFinite.ResidueDegree
public import StacksFrontier.RingTheory.Module.LocallyFree.Field
public import StacksFrontier.RingTheory.Module.LocallyFree.SheafBridge

/-!
# A degree bound bounds the sum of residue degrees in a fibre

If every field-valued base change of a morphism of schemes is finite locally free of degree at
most `n`, then the sum of the residue-field degrees of any finite family of distinct points in
such a base change is at most `n`.

## Main results

* `AlgebraicGeometry.sum_finrank_residueField_le_of_degree_le` bounds the sum of the
  residue-field degrees of distinct points in a field-valued base change.

## Implementation notes

The degree condition is expressed by the existence of a rank `r ≤ n` for the finite locally free
structural morphism of each base change. The ground-field algebra structure on each residue field
is induced by the structural morphism followed by evaluation at the point. The statement is given
for any injective finite family of points; this is slightly more general than choosing an
enumeration of all points of the fibre.

The passage from the sheaf-level rank condition of
`Stacks.Morphisms.IsFiniteLocallyFreeOfRank` to finite dimension exactly `r` for the global
sections of the base change is
`AlgebraicGeometry.finite_and_finrank_sections_of_isFiniteLocallyFreeOfRank`. The points of the
base change then correspond to maximal ideals of that finite-dimensional algebra and
`Algebra.sum_finrank_residueField_le_finrank` applies.

## References

* [Stacks Project, Tag 03J5](https://stacks.math.columbia.edu/tag/03J5)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- A sheaf of modules isomorphic to one that is finite locally free of rank `r` is itself
finite locally free of rank `r`: the transported local data has the same index types. -/
private lemma isFiniteLocallyFreeOfRank_of_iso {S : Scheme.{u}} {M N : S.Modules} (e : M ≅ N)
    (r : ℕ) [h : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} M r] :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} N r := by
  obtain ⟨q, hfree, hrank⟩ := h.exists_isFiniteLocallyFreeOfRankData
  let q' : SheafOfModules.LocalGeneratorsData.{u, u, u, u} N := {
    I := q.I
    X := q.X
    coversTop := q.coversTop
    generators i := (q.generators i).ofEpi
      ((SheafOfModules.overFunctor _ (q.X i)).mapIso e).hom }
  have hfree' : q'.IsLocallyFreeData.{u, u, u, u} := by
    refine ⟨fun i => ?_⟩
    have := hfree.isIso i
    have h : IsIso ((q.generators i).π ≫
        ((SheafOfModules.overFunctor _ (q.X i)).mapIso e).hom) := inferInstance
    exact (congrArg IsIso (SheafOfModules.GeneratingSections.ofEpi_π
      (q.generators i) ((SheafOfModules.overFunctor _ (q.X i)).mapIso e).hom)).mpr h
  exact { exists_isFiniteLocallyFreeOfRankData := ⟨q', hfree', hrank⟩ }

private lemma isQuasicoherent_of_isFiniteLocallyFreeOfRank {X : Scheme.{u}} (M : X.Modules) (r : ℕ)
    [h : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} M r] : M.IsQuasicoherent := by
  obtain ⟨q, hfree, hrank⟩ := h.exists_isFiniteLocallyFreeOfRankData
  let : q.IsLocallyFreeData := hfree
  exact q.quasiCoherentData.isQuasicoherent

/-- The sheaf-level finite-local-freeness of rank `r` of Tag 01C6 gives the pointwise one: a
member of the covering through a given point, with its local free presentation rewritten as an
isomorphism with a free sheaf on that open. -/
private lemma isFiniteLocallyFreeOfRank_pointwise {X : Scheme.{u}} (M : X.Modules) (r : ℕ)
    [h : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} M r] :
    Scheme.Modules.IsFiniteLocallyFreeOfRank M r := by
  intro x
  obtain ⟨q, hfree, hrank⟩ := h.exists_isFiniteLocallyFreeOfRankData
  have hcover : TopologicalSpace.IsOpenCover q.X :=
    (Opens.coversTop_iff X q.X).mp q.coversTop
  have hmem : x ∈ (⨆ i, q.X i) := by
    unfold TopologicalSpace.IsOpenCover at hcover
    rw [hcover]
    trivial
  rw [TopologicalSpace.Opens.mem_iSup] at hmem
  obtain ⟨i, hi⟩ := hmem
  let U : X.Opens := q.X i
  obtain ⟨eI⟩ := hrank i
  let F := Scheme.Modules.overEquiv (X := X) U
  have hFeq : F.functor.IsEquivalence := F.isEquivalence_functor
  have hdisc : Limits.PreservesColimitsOfShape (Discrete (ULift.{u, 0} (Fin r))) F.functor :=
    Limits.preservesColimitsOfShape_of_discrete F.functor
  have := hfree.isIso i
  let eFree := @SheafOfModules.mapFreeIso _ _ _ _ _ _ _ _ _ _ _ _ F.functor
    (ULift.{u, 0} (Fin r)) hdisc (Iso.refl _)
  let eM := (F.functor.mapIso (asIso (q.generators i).π)) ≪≫
    (Scheme.Modules.overFunctorEquiv (X := X) U).app M |>.symm
  let eI' := (SheafOfModules.freeFunctor (R := X.ringCatSheaf.over U)).mapIso
    (Equiv.toIso (eI.trans ((Equiv.ulift (α := Fin r)).symm)))
  exact ⟨U, hi, ⟨eM ≪≫ F.functor.mapIso eI' ≪≫ eFree.symm⟩⟩

/-- **Stacks Project, Tag 03J5.** In a field-valued base change whose degree is uniformly bounded
by `n`, the sum of the residue degrees at any finite family of distinct points is at most `n`. -/
@[stacks 03J5 "sum_residue_degrees_le_bound"]
public theorem sum_finrank_residueField_le_of_degree_le
    {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ)
    (h : ∀ (k : Type u) [Field k] (g : Spec (.of k) ⟶ Y),
      ∃ r ≤ n, Stacks.Morphisms.IsFiniteLocallyFreeOfRank (pullback.fst g f) r) :
    ∀ (k : Type u) [Field k] (g : Spec (.of k) ⟶ Y) {t : ℕ}
      (x : Fin t → (pullback g f : Scheme.{u})), Function.Injective x →
      (∑ i,
        letI := ((Scheme.ΓSpecIso (.of k)).inv ≫ (pullback.fst g f).appTop ≫
          (pullback g f).Γevaluation (x i)).hom.toAlgebra
        Module.finrank k ((pullback g f).residueField (x i))) ≤ n := by
  intro k _ g t x hx
  let Z := pullback g f
  let p := pullback.fst g f
  obtain ⟨r, hrn, hr⟩ := h k g
  have : Stacks.Morphisms.IsFiniteLocallyFreeOfRank p r := hr
  have : IsAffineHom p := hr.toIsAffineHom
  have : IsAffine Z := isAffine_of_isAffineHom p
  let A : Type u := Γ(Z, ⊤)
  let φ : CommRingCat.of k ⟶ Γ(Z, ⊤) := (Scheme.ΓSpecIso (.of k)).inv ≫ p.appTop
  let : Algebra k A := φ.hom.toAlgebra
  have hdim := finite_and_finrank_sections_of_isFiniteLocallyFreeOfRank p r
  have : Module.Finite k A := hdim.1
  have : IsArtinianRing A := IsArtinianRing.of_finite k A
  let e := Z.isoSpec
  let m : Fin t → MaximalSpectrum A := fun i =>
    ⟨(e.hom (x i)).asIdeal, @Ideal.isMaximal_of_isPrime _ _ _ _ (e.hom (x i)).isPrime⟩
  have (i : Fin t) : (m i).asIdeal.IsPrime := (m i).isMaximal.isPrime
  have hm : Function.Injective m := fun i j hij =>
    hx (e.hom.homeomorph.injective (PrimeSpectrum.ext (congrArg MaximalSpectrum.asIdeal hij)))
  have hdeg (i : Fin t) :
      let := (φ ≫ Z.Γevaluation (x i)).hom.toAlgebra
      Module.finrank k (Z.residueField (x i)) = Module.finrank k (m i).asIdeal.ResidueField := by
    let : Algebra k (Z.residueField (x i)) := (φ ≫ Z.Γevaluation (x i)).hom.toAlgebra
    let e1 := (asIso (e.hom.residueFieldMap (x i))).commRingCatIsoToRingEquiv
    let e2 := (Scheme.Spec.residueFieldIso Γ(Z, ⊤) (e.hom (x i))).commRingCatIsoToRingEquiv
    refine Algebra.finrank_eq_of_equiv_equiv (RingEquiv.refl k) (e1.symm.trans e2) ?_
    ext a
    have hcancel : e.hom.appTop ((Scheme.ΓSpecIso Γ(Z, ⊤)).inv (φ a)) = φ a := by
      simp [e, Scheme.isoSpec, Scheme.toSpecΓ_appTop]
    have hn := Scheme.Γevaluation_naturality_apply e.hom (x i)
      ((Scheme.ΓSpecIso Γ(Z, ⊤)).inv (φ a))
    rw [hcancel] at hn
    have h₁ : e1.symm (Z.Γevaluation (x i) (φ a)) = (Spec Γ(Z, ⊤)).Γevaluation (e.hom (x i))
        ((Scheme.ΓSpecIso Γ(Z, ⊤)).inv (φ a)) :=
      e1.symm_apply_eq.mpr hn.symm
    have h₂ : (Scheme.ΓSpecIso Γ(Z, ⊤)).inv ≫ (Spec Γ(Z, ⊤)).Γevaluation (e.hom (x i)) ≫
        (Scheme.Spec.residueFieldIso Γ(Z, ⊤) (e.hom (x i))).hom =
          CommRingCat.ofHom (algebraMap Γ(Z, ⊤) (m i).asIdeal.ResidueField) := by
      rw [← Category.assoc, ← Iso.eq_comp_inv]
      exact (Scheme.Spec.algebraMap_residueFieldIso_inv _ _).symm
    show _ = e2 (e1.symm (Z.Γevaluation (x i) (φ a)))
    rw [h₁]
    exact (congrArg (fun f => f.hom (φ a)) h₂).symm
  calc
    _ = ∑ i, Module.finrank k (m i).asIdeal.ResidueField := Finset.sum_congr rfl fun i _ => hdeg i
    _ ≤ Module.finrank k A := Algebra.sum_finrank_residueField_le_finrank k A m hm
    _ = r := hdim.2
    _ ≤ n := hrn

end AlgebraicGeometry

end
