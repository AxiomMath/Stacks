module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.FieldValuedPointSum
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.FiniteCoefficientLFunctionInverse
public import StacksFrontier.LinearAlgebra.Matrix.PerfectComplexCharSeriesDetection

/-!
# A criterion for `L(X, ℱ) = det(1 - f T | K)⁻¹` through the key lemma

Let `ℱ` be a constructible flat sheaf of `Λ`-modules on a scheme `X` of finite type over a finite
field, and `f` an endomorphism of a perfect complex `K` of `Λ`-modules. Suppose that for every `N`
there are a ring `R`, an additive functor `Φ : Mod_R ⥤ Mod_Λ` with `Φ(O)` free over `Λ` for a free
`R`-module `O` of rank one, a bounded complex `Q` of finite projective `R`-modules with an
endomorphism `g` and an identification `Φ(Q) ≅ K` carrying `Φ(g)` to `f`, such that the torsion
hypothesis `(H_N)` of the key lemma holds for `φ = functorRep Φ eO b`, and elements `gₓ ∈ R` at
the closed points of degree at most `N` with

* `Tr(g ^ m | Q) = ∑_{deg x ∣ m} deg x · [gₓ ^ (m / deg x)]` in `R^♮` for `1 ≤ m ≤ N`, and
* `det(1 - π_x^* T ^ (deg x) | ℱ_x̄) = det(1 - φ(gₓ) T ^ (deg x))`.

Then `det(1 - f T | K) · L(X, ℱ) = 1`. This is the shape in which the lisse case of
[Stacks, Tag 03UZ] is proved: `Q` is a perfect complex computing `RΓ_c` of a Galois cover with
coefficients `ℤ/ℓ^M[G]`, `Φ` the twist by the stalk, the trace identities are the trace formula
over the extensions `k_m`, and the `gₓ` are the Frobenius elements of the cover.

## Main results

All names are in the namespace `Stacks.EtaleCohomology`.

* `perfectDerivedCharSeries_mul_lFunctionOfFiniteProjectiveStalks_eq_one`: the criterion for a
  sheaf with finite projective stalks.
* `perfectDerivedCharSeries_mul_constructibleFlatLFunction_eq_one`: the criterion for a
  constructible flat sheaf.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Frobenius
open CategoryTheory.FilteredDerived Stacks.CharSeriesTraceDetection

universe u w w' r

namespace Stacks.EtaleCohomology

variable (B : BigEtaleSite.{u}) (X : B.Scheme) (Λ : Type r) [CommRing Λ]
  [HasColimitsOfSize.{u, u} (ModuleCat.{w} Λ)] [HasLimitsOfSize.{u, u} (ModuleCat.{w} Λ)]
  (F : Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{w} Λ))
  {k : Type u} [Field k] [Finite k] (f : X.obj ⟶ Spec (.of k)) [LocallyOfFiniteType f]
  [∀ (S T : B.Scheme) (g : T ⟶ S),
    ((smallEtaleBaseChange B g).sheafPushforwardContinuous (ModuleCat.{w} Λ)
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
  [∀ (T : B.Scheme) (V : SmallEtale B T.obj T.property),
    HasWeakSheafify ((SmallEtale.topology B T.obj T.property).over V) (ModuleCat.{w} Λ)]

omit [∀ (S T : B.Scheme) (g : T ⟶ S),
    ((smallEtaleBaseChange B g).sheafPushforwardContinuous (ModuleCat.{w} Λ)
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
  [∀ (T : B.Scheme) (V : SmallEtale B T.obj T.property),
    HasWeakSheafify ((SmallEtale.topology B T.obj T.property).over V) (ModuleCat.{w} Λ)] in
/-- **The key-lemma criterion for `det(1 - f T | K) · L(X, ℱ) = 1`**, for a sheaf with finite
projective stalks. -/
theorem perfectDerivedCharSeries_mul_lFunctionOfFiniteProjectiveStalks_eq_one [QuasiCompact f]
    [HasDerivedCategory.{w'} (ModuleCat.{w} Λ)]
    (hfin : ∀ s : GeometricPoint X.obj,
      Module.Finite Λ ((etaleModuleStalkFunctor B X Λ s).obj F))
    (hproj : ∀ s : GeometricPoint X.obj,
      Module.Projective Λ ((etaleModuleStalkFunctor B X Λ s).obj F))
    (K : DerivedCategory (ModuleCat.{w} Λ)) (hK : StacksDraft.Perfect.IsPerfect K) (fK : K ⟶ K)
    (hdata : ∀ N : ℕ, ∃ (R : Type) (_ : Ring R) (Φ : ModuleCat.{w} R ⥤ ModuleCat.{w} Λ)
      (_ : Φ.Additive) (O : ModuleCat.{w} R) (eO : R ≃ₗ[R] O) (r : ℕ)
      (b : Φ.obj O ≃ₗ[Λ] (Fin r → Λ)) (Q : CochainComplex (ModuleCat.{w} R) ℤ)
      (hQ : finiteProjectiveComplex R Q) (g : Q ⟶ Q)
      (e : DerivedCategory.Q.obj ((Φ.mapHomologicalComplex (ComplexShape.up ℤ)).obj Q) ≅ K)
      (_ : DerivedCategory.Q.map ((Φ.mapHomologicalComplex (ComplexShape.up ℤ)).map g) ≫ e.hom =
        e.hom ≫ fK)
      (_ : TraceDetectionHypothesis (functorRep Φ eO b) N) (gP : closedPoints X.obj → R),
      (∀ m, 0 < m → m ≤ N → ∃ h : Q ⟶ Q, (∀ i, (h.f i).hom = (g.f i).hom ^ m) ∧
        alternatingTrace R Q hQ h = ∑ x ∈ closedPointsDegreeLE f N,
          if residueDegree f x.1 ∣ m then
            residueDegree f x.1 • q R (gP x ^ (m / residueDegree f x.1)) else 0) ∧
      ∀ x ∈ closedPointsDegreeLE f N, finiteProjectiveLocalCharSeries B X Λ F f hfin hproj x =
        (1 - (PowerSeries.X : PowerSeries Λ) ^ residueDegree f x.1 •
          (functorRep Φ eO b (gP x)).map (PowerSeries.C (R := Λ))).det) :
    (perfectDerivedCharSeries Λ K hK fK : PowerSeries Λ) *
      lFunctionOfFiniteProjectiveStalks B X Λ F f hfin hproj = 1 := by
  refine mul_lFunctionOfFiniteProjectiveStalks_eq_one B X Λ F f hfin hproj _ fun N => ?_
  obtain ⟨R, _, Φ, _, O, eO, r, b, Q, hQ, g, e, he, H, gP, htr, hloc⟩ := hdata N
  refine ⟨closedPointsDegreeLE f N, fun x hx => ?_, fun j hj => ?_⟩
  · simpa only [closedPointsDegreeLE, Set.Finite.mem_toFinset, Set.mem_ofPred_eq] using hx
  · rw [coeff_perfectDerivedCharSeries_eq_prod Φ eO b Q hQ g H K hK fK e he
      (closedPointsDegreeLE f N) (fun x => residueDegree f x.1)
      (fun x _ => residueDegree_pos f x.1 x.2) gP htr j hj]
    congr 1
    exact (Finset.prod_congr rfl hloc).symm

/-- **The key-lemma criterion for `det(1 - f T | K) · L(X, ℱ) = 1`.** -/
theorem perfectDerivedCharSeries_mul_constructibleFlatLFunction_eq_one [QuasiCompact f]
    [HasDerivedCategory.{w'} (ModuleCat.{w} Λ)] (hF : IsConstructibleFlatModuleSheaf B X Λ F)
    (K : DerivedCategory (ModuleCat.{w} Λ)) (hK : StacksDraft.Perfect.IsPerfect K) (fK : K ⟶ K)
    (hdata : ∀ N : ℕ, ∃ (R : Type) (_ : Ring R) (Φ : ModuleCat.{w} R ⥤ ModuleCat.{w} Λ)
      (_ : Φ.Additive) (O : ModuleCat.{w} R) (eO : R ≃ₗ[R] O) (r : ℕ)
      (b : Φ.obj O ≃ₗ[Λ] (Fin r → Λ)) (Q : CochainComplex (ModuleCat.{w} R) ℤ)
      (hQ : finiteProjectiveComplex R Q) (g : Q ⟶ Q)
      (e : DerivedCategory.Q.obj ((Φ.mapHomologicalComplex (ComplexShape.up ℤ)).obj Q) ≅ K)
      (_ : DerivedCategory.Q.map ((Φ.mapHomologicalComplex (ComplexShape.up ℤ)).map g) ≫ e.hom =
        e.hom ≫ fK)
      (_ : TraceDetectionHypothesis (functorRep Φ eO b) N) (gP : closedPoints X.obj → R),
      (∀ m, 0 < m → m ≤ N → ∃ h : Q ⟶ Q, (∀ i, (h.f i).hom = (g.f i).hom ^ m) ∧
        alternatingTrace R Q hQ h = ∑ x ∈ closedPointsDegreeLE f N,
          if residueDegree f x.1 ∣ m then
            residueDegree f x.1 • q R (gP x ^ (m / residueDegree f x.1)) else 0) ∧
      ∀ x ∈ closedPointsDegreeLE f N, finiteProjectiveLocalCharSeries B X Λ F f
          (finite_etaleModuleStalk_of_isConstructibleFlatModuleSheaf B X Λ F hF)
          (projective_etaleModuleStalk_of_isConstructibleFlatModuleSheaf B X Λ F hF) x =
        (1 - (PowerSeries.X : PowerSeries Λ) ^ residueDegree f x.1 •
          (functorRep Φ eO b (gP x)).map (PowerSeries.C (R := Λ))).det) :
    (perfectDerivedCharSeries Λ K hK fK : PowerSeries Λ) *
      constructibleFlatLFunction B X Λ F f hF = 1 :=
  perfectDerivedCharSeries_mul_lFunctionOfFiniteProjectiveStalks_eq_one B X Λ F f
    (finite_etaleModuleStalk_of_isConstructibleFlatModuleSheaf B X Λ F hF)
    (projective_etaleModuleStalk_of_isConstructibleFlatModuleSheaf B X Λ F hF) K hK fK hdata

end Stacks.EtaleCohomology
