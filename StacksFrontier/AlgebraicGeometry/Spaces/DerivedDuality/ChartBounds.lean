module

public import StacksFrontier.AlgebraicGeometry.Spaces.DerivedDuality.SchemeDualBound

/-!
# Boundedness of duals on a ringed site covered by finitely many duality charts

Let `(C, O)` be a ringed site covered by **finitely many** objects `V i`, each carrying a duality
chart for `K` at the class of all objects. Then `D = R𝓗om(-, K)` carries objects of `D_Coh(O)`
bounded below to objects bounded above, and objects bounded above to objects bounded below,
with bounds uniform in the object: on the chart `V i` the dual is `ε^* R𝓗om(L', ω_i)`, and
`ω_i` has finite injective dimension and is bounded below (Stacks 0A89); finiteness of the
covering makes the bounds uniform. This is the quasi-compact clause of Stacks 0E51.

## Main results

* `AlgebraicGeometry.RingedSite.exists_upper_bound_dual_of_charts`.
* `AlgebraicGeometry.RingedSite.exists_lower_bound_dual_of_charts`.

## References

* [Stacks Project, Tag 0E51](https://stacks.math.columbia.edu/tag/0E51)
* [Stacks Project, Tag 0A89](https://stacks.math.columbia.edu/tag/0A89)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.RingedSite

/-- **A lower bound for the dual of a bounded-above object** on an affine Noetherian scheme with a
dualizing complex `ω`: `ω` is bounded below, say in degrees `≥ a`, and then
`R𝓗om(X, ω)` lies in degrees `≥ a - m` for `X` in degrees `≤ m`. -/
theorem exists_lower_bound_schemeDual (T : Scheme.{u}) [IsAffine T] [IsNoetherian T]
    (ω : SchemeStdDerived T)
    (hω : letI : HasDerivedCategory T.Modules := HasDerivedCategory.standard _
      Stacks.Duality.IsDualizingComplex ω) :
    ∃ a : ℤ, ∀ (m : ℤ) (X : SchemeStdDerived T),
      (∀ i : ℤ, m < i → IsZero ((schemeStdHomology T i).obj X)) →
        ∀ j : ℤ, j < a - m → IsZero ((schemeStdHomology T j).obj (schemeDual T ω X)) := by
  let : HasDerivedCategory T.Modules := HasDerivedCategory.standard _
  obtain ⟨n₀, hn₀⟩ := Stacks.Duality.isBoundedBelow_of_isDualizingComplex ω hω
  have hge : ω.IsGE n₀ := (DerivedCategory.isGE_iff ω n₀).2 fun i hi => hn₀ i hi
  refine ⟨n₀, fun m X hX j hj => ?_⟩
  have hle : X.IsLE m := (DerivedCategory.isLE_iff X m).2 fun i hi => hX i hi
  let : HasDerivedCategory (Stacks.SheafOfModules.StructureSheafModules T.sheaf) :=
    HasDerivedCategory.standard _
  exact (DerivedCategory.isGE_iff _ (n₀ - m)).1
    (Stacks.SheafOfModules.isGE_derivedSheafHom T.sheaf X ω m n₀ hle hge) j hj

variable (Y : RingedSite.{u, u, u})
  [HasSheafify Y.J AddCommGrpCat.{u}]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} Y.O)) (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor Y.O)
      (ComplexShape.up ℤ)]
  [∀ U : Y.C, HasSheafify (Y.over U).J AddCommGrpCat.{u}]
  [∀ U : Y.C, (Y.over U).J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ U : Y.C, (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (Y.over U).O).Additive]
  [∀ U : Y.C, ∀ A,
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (Y.over U).O).obj A).Additive]
  [∀ U : Y.C, ∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} (Y.over U).O)) (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂
      (Stacks.SheafOfModules.Tensor.sheafTensor (Y.over U).O) (ComplexShape.up ℤ)]

variable {Y} in
omit [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} Y.O)) (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor Y.O)
      (ComplexShape.up ℤ)]
  [∀ U : Y.C, (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (Y.over U).O).Additive]
  [∀ U : Y.C, ∀ A,
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (Y.over U).O).obj A).Additive]
  [∀ U : Y.C, ∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} (Y.over U).O)) (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂
      (Stacks.SheafOfModules.Tensor.sheafTensor (Y.over U).O) (ComplexShape.up ℤ)] in
/-- The vanishing of a cohomology sheaf of an object of `D(O)` restricted to a slice. -/
theorem isZero_homology_stdRestrict {U : Y.C} {L : StdDerived Y} {n : ℤ}
    (h : IsZero ((stdHomology Y n).obj L)) :
    IsZero ((stdHomology (Y.over U) n).obj ((stdRestrict Y U).obj L)) :=
  (Functor.map_isZero (SheafOfModules.overFunctor.{u}
    (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) U) h).of_iso (stdRestrictHomologyIso Y U n L)

variable {Y} in
omit [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} Y.O)) (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor Y.O)
      (ComplexShape.up ℤ)]
  [∀ U : Y.C, (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (Y.over U).O).Additive]
  [∀ U : Y.C, ∀ A,
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (Y.over U).O).obj A).Additive]
  [∀ U : Y.C, ∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} (Y.over U).O)) (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂
      (Stacks.SheafOfModules.Tensor.sheafTensor (Y.over U).O) (ComplexShape.up ℤ)] in
/-- A model on a chart of an object whose cohomology vanishes in degree `n` has vanishing
cohomology in degree `n`. -/
theorem DualityChart.isZero_homology_model {U : Y.C} {K : StdDerived (Y.over U)}
    {P : ChartClass.{u}}
    (c : DualityChart (Y.over U) K P) {L : StdDerived Y} {L' : SchemeStdDerived c.T}
    (hq : ∀ n : ℤ, ((schemeStdHomology c.T n).obj L').IsQuasicoherent)
    (e : c.derived.obj L' ≅ (stdRestrict Y U).obj L) {n : ℤ}
    (h : IsZero ((stdHomology Y n).obj L)) : IsZero ((schemeStdHomology c.T n).obj L') :=
  c.isZero_of_isZero _ (hq n) ((isZero_homology_stdRestrict h).of_iso
    ((c.derivedHomologyIso n L').symm ≪≫ (stdHomology (Y.over U) n).mapIso e))

/-- **The dual of an object of `D^+_Coh` is bounded above, uniformly**, on a ringed site covered
by finitely many duality charts. -/
theorem exists_upper_bound_dual_of_charts {ι : Type*} [Finite ι] {V : ι → Y.C}
    (hV : Y.J.CoversTop V) {K : StdDerived Y}
    (c : ∀ i, DualityChart (Y.over (V i)) ((stdRestrict Y (V i)).obj K) ChartClass.all) :
    ∃ b : ℤ, ∀ (m : ℤ) (L : StdDerived Y), coherentDerived Y L →
      (∀ n : ℤ, n < m → IsZero ((stdHomology Y n).obj L)) →
        ∀ j : ℤ, b - m < j →
          IsZero ((stdHomology Y j).obj (((stdSheafHom Y).obj (op L)).obj K)) := by
  have hb : ∀ i, ∃ b : ℤ, ∀ (m : ℤ) (X : SchemeStdDerived (c i).T),
      SchemeCoherent (c i).T X →
      (∀ n : ℤ, n < m → IsZero ((schemeStdHomology (c i).T n).obj X)) →
        ∀ j : ℤ, b - m < j →
          IsZero ((schemeStdHomology (c i).T j).obj (schemeDual (c i).T (c i).ω X)) := fun i =>
    have := (c i).isAffine
    have := (c i).isNoetherian
    exists_bound_schemeDual (c i).T (c i).ω (c i).isDualizing
  choose bs hbs using hb
  obtain ⟨b, hbmax⟩ := (Set.finite_range bs).bddAbove
  refine ⟨b, fun m L hL hm j hj => ?_⟩
  refine Stacks.SheafOfModules.isZero_of_coversTop hV _ fun i => ?_
  obtain ⟨L', hL', -, hq, ⟨e⟩⟩ :=
    (c i).models_of_coherentDerived (coherentDerived_stdRestrict Y (V i) hL)
  obtain ⟨d⟩ := (c i).restrict_dual_iso hL' trivial e
  have hbi : bs i ≤ b := hbmax ⟨i, rfl⟩
  have hz := hbs i m L' hL' (fun n hn => (c i).isZero_homology_model hq e (hm n hn)) j
    (by omega)
  have := (c i).additive
  exact ((Functor.map_isZero (c i).Φ hz).of_iso ((c i).derivedHomologyIso j _)).of_iso
    ((stdRestrictHomologyIso Y (V i) j _).symm ≪≫ (stdHomology (Y.over (V i)) j).mapIso d)

/-- **The dual of an object of `D^-_Coh` is bounded below, uniformly**, on a ringed site covered
by finitely many duality charts. -/
theorem exists_lower_bound_dual_of_charts {ι : Type*} [Finite ι] {V : ι → Y.C}
    (hV : Y.J.CoversTop V) {K : StdDerived Y}
    (c : ∀ i, DualityChart (Y.over (V i)) ((stdRestrict Y (V i)).obj K) ChartClass.all) :
    ∃ a : ℤ, ∀ (m : ℤ) (L : StdDerived Y), coherentDerived Y L →
      (∀ n : ℤ, m < n → IsZero ((stdHomology Y n).obj L)) →
        ∀ j : ℤ, j < a - m →
          IsZero ((stdHomology Y j).obj (((stdSheafHom Y).obj (op L)).obj K)) := by
  have ha : ∀ i, ∃ a : ℤ, ∀ (m : ℤ) (X : SchemeStdDerived (c i).T),
      (∀ n : ℤ, m < n → IsZero ((schemeStdHomology (c i).T n).obj X)) →
        ∀ j : ℤ, j < a - m →
          IsZero ((schemeStdHomology (c i).T j).obj (schemeDual (c i).T (c i).ω X)) := fun i =>
    have := (c i).isAffine
    have := (c i).isNoetherian
    exists_lower_bound_schemeDual (c i).T (c i).ω (c i).isDualizing
  choose as has using ha
  obtain ⟨a, hamin⟩ := (Set.finite_range as).bddBelow
  refine ⟨a, fun m L hL hm j hj => ?_⟩
  refine Stacks.SheafOfModules.isZero_of_coversTop hV _ fun i => ?_
  obtain ⟨L', hL', -, hq, ⟨e⟩⟩ :=
    (c i).models_of_coherentDerived (coherentDerived_stdRestrict Y (V i) hL)
  obtain ⟨d⟩ := (c i).restrict_dual_iso hL' trivial e
  have hai : a ≤ as i := hamin ⟨i, rfl⟩
  have hz := has i m L' (fun n hn => (c i).isZero_homology_model hq e (hm n hn)) j (by omega)
  have := (c i).additive
  exact ((Functor.map_isZero (c i).Φ hz).of_iso ((c i).derivedHomologyIso j _)).of_iso
    ((stdRestrictHomologyIso Y (V i) j _).symm ≪≫ (stdHomology (Y.over (V i)) j).mapIso d)

end AlgebraicGeometry.RingedSite

end
