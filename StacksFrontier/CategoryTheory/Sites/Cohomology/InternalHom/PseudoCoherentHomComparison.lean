module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.LocalizedHomComparison
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.StrictlyPerfectDerivedPairing
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.InternalHomPullbackPseudoCoherent
public import StacksFrontier.Homology.DerivedCategory.MapHomologyIso
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The comparison of a monoidal t-exact functor at a pseudo-coherent approximation

Let `Ψ : D(O_X) ⥤ D(O_Y)` be a monoidal triangulated functor between derived categories of
ringed sites which preserves the bounds `D^{≤ n}`, `D^{≥ n}` and invertibility on each
cohomology sheaf — the derived functor of an exact monoidal functor, for instance. This file
proves the two steps of the proof of Stacks 08JP, case (1), that happen on one open:

* **the base case**: the comparison `Ψ RSheafHom(Q P, M) ⟶ RSheafHom(Ψ Q P, Ψ M)` is an
  isomorphism for a strictly perfect complex `P`, which is dualizable in `D(O_X)`
  (`Stacks.SheafOfModules.Strict.exactPairingQStrictlyPerfect`) — Lemma A;
* **the truncation estimate**: if `α : P ⟶ E` is invertible on cohomology in degrees `> m` and
  surjective in degree `m`, and `M` is bounded below by `a`, the comparison at `(Q E, M)` is
  invertible on cohomology in every degree `j < a - m`. This is the argument of the ringed-space
  clause (2) of Stacks 0GM7 (`isIso_homologyMap_derivedPullbackSheafHomMap_of_distTriang`), with
  the derived pullback along a flat morphism replaced by `Ψ`.

## Main results

* `CategoryTheory.Functor.isGE_mapDerivedCategory_obj`,
  `CategoryTheory.Functor.isLE_mapDerivedCategory_obj`,
  `CategoryTheory.Functor.isIso_homologyMap_mapDerivedCategory_map`: an exact functor is t-exact
  on derived categories.
* `AlgebraicGeometry.RingedSite.isIso_homologyMap_homComparisonMonoidal_of_distTriang`.
* `AlgebraicGeometry.RingedSite.isIso_homologyMap_homComparisonMonoidal_of_approximation`.

## References

* [Stacks Project, Tag 08JP](https://stacks.math.columbia.edu/tag/08JP)
* [Stacks Project, Tag 0GM7](https://stacks.math.columbia.edu/tag/0GM7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open CategoryTheory.Pretriangulated
open Stacks.Cohomology.DerivedInternalHomPullback

universe u

namespace CategoryTheory.Functor

variable {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

/-- An exact functor carries a morphism invertible on the `j`-th cohomology to one. -/
theorem isIso_homologyMap_mapDerivedCategory_map {K L : DerivedCategory C} (g : K ⟶ L) (j : ℤ)
    (hg : IsIso ((DerivedCategory.homologyFunctor C j).map g)) :
    IsIso ((DerivedCategory.homologyFunctor D j).map (F.mapDerivedCategory.map g)) := by
  have : IsIso ((DerivedCategory.homologyFunctor C j ⋙ F).map g) :=
    Functor.map_isIso F ((DerivedCategory.homologyFunctor C j).map g)
  exact (NatIso.isIso_map_iff
    (StacksDraft.DerivedCategoryHomology.mapDerivedCategoryHomologyIso F j) g).2 this

/-- An exact functor preserves vanishing of cohomology in a degree. -/
@[sga "6 I 2.13" "special case"]
theorem isZero_homology_mapDerivedCategory_obj (K : DerivedCategory C) (j : ℤ)
    (hK : IsZero ((DerivedCategory.homologyFunctor C j).obj K)) :
    IsZero ((DerivedCategory.homologyFunctor D j).obj (F.mapDerivedCategory.obj K)) :=
  (Functor.map_isZero F hK).of_iso
    ((StacksDraft.DerivedCategoryHomology.mapDerivedCategoryHomologyIso F j).app K)

/-- An exact functor preserves lower bounds of cohomology. -/
theorem isGE_mapDerivedCategory_obj (K : DerivedCategory C) (n : ℤ) (hK : K.IsGE n) :
    (F.mapDerivedCategory.obj K).IsGE n := by
  rw [DerivedCategory.isGE_iff] at hK ⊢
  exact fun i hi => isZero_homology_mapDerivedCategory_obj F K i (hK i hi)

/-- An exact functor preserves upper bounds of cohomology. -/
@[sga "6 I 2.13" "special case"]
theorem isLE_mapDerivedCategory_obj (K : DerivedCategory C) (n : ℤ) (hK : K.IsLE n) :
    (F.mapDerivedCategory.obj K).IsLE n := by
  rw [DerivedCategory.isLE_iff] at hK ⊢
  exact fun i hi => isZero_homology_mapDerivedCategory_obj F K i (hK i hi)

end CategoryTheory.Functor

namespace AlgebraicGeometry.RingedSite

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance] Stacks.SheafOfModules.DerivedMonoidal.derivedMonoidal

variable {X Y : RingedSite.{u, u, u}}
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.O)) (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]
  [HasSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} Y.O)) (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor Y.O)
      (ComplexShape.up ℤ)]
  (Ψ : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ⥤
    DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)))
  [Ψ.Monoidal] [Ψ.CommShift ℤ] [Ψ.IsTriangulated]
  (hLE : ∀ K n, K.IsLE n → (Ψ.obj K).IsLE n)
  (hGE : ∀ K n, K.IsGE n → (Ψ.obj K).IsGE n)
  (hH : ∀ {K L} (g : K ⟶ L) (j : ℤ), IsIso ((DerivedCategory.homologyFunctor _ j).map g) →
    IsIso ((DerivedCategory.homologyFunctor _ j).map (Ψ.map g)))

include hLE hGE hH in
/-- **The truncation step for a monoidal t-exact functor.** Let `A ⟶ K ⟶ C ⟶ A[1]` be a
distinguished triangle with `C` bounded above by `n`, and `M` bounded below by `a`. If the
comparison of `Ψ` is invertible at `(A, M)`, it is invertible on cohomology at `(K, M)` in every
degree `j` with `j + 1 < a - n`: the map `A ⟶ K` induces on both sides maps invertible on
cohomology in those degrees, by the truncation estimate of the derived internal Hom on each site,
and the comparison is natural in its first argument. -/
theorem isIso_homologyMap_homComparisonMonoidal_of_distTriang
    (T : Triangle (DerivedCategory (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O))))
    (hT : T ∈ distTriang _) (n : ℤ) (hC : T.obj₃.IsLE n)
    (M : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (a : ℤ) (hM : M.IsGE a) (hA : IsIso (homComparisonMonoidal Ψ T.obj₁ M)) (j : ℤ)
    (hj : j + 1 < a - n) :
    IsIso ((DerivedCategory.homologyFunctor _ j).map (homComparisonMonoidal Ψ T.obj₂ M)) := by
  have sq := homComparisonMonoidal_naturality_source Ψ T.mor₁ M
  have hX := isIso_homologyMap_derivedSheafHom_map_of_isLE₃ X T hT n hC M a hM j hj
  have hY := isIso_homologyMap_derivedSheafHom_map_of_isLE₃ Y (Ψ.mapTriangle.obj T)
    (Ψ.map_distinguished T hT) n (hLE _ n hC) (Ψ.obj M) a (hGE M a hM) j hj
  have hPX := hH _ j hX
  have hsq := congrArg (DerivedCategory.homologyFunctor _ j).map sq
  rw [Functor.map_comp, Functor.map_comp] at hsq
  have hrhs : IsIso ((DerivedCategory.homologyFunctor _ j).map
      (homComparisonMonoidal Ψ T.obj₂ M) ≫ (DerivedCategory.homologyFunctor _ j).map
        (((derivedSheafHomBifunctor Y).map (Ψ.map T.mor₁).op).app (Ψ.obj M))) := by
    refine (congrArg IsIso hsq).mp ?_
    have : IsIso ((DerivedCategory.homologyFunctor _ j).map (homComparisonMonoidal Ψ T.obj₁ M)) :=
      Functor.map_isIso _ _
    exact IsIso.comp_isIso' hPX this
  exact @IsIso.of_isIso_comp_right _ _ _ _ _ _ _ hY hrhs

include hLE hGE hH in
/-- **The comparison of a monoidal t-exact functor at a pseudo-coherent approximation.** Let
`α : P ⟶ E` be a morphism of complexes of `O_X`-modules inducing isomorphisms on cohomology in
degrees `> m` and a surjection in degree `m`, with `P` strictly perfect, and let `M` be bounded
below by `a`. Then the comparison of `Ψ` at `(Q E, M)` is invertible on cohomology in every degree
`j < a - m`. At `(Q P, M)` it is an isomorphism, `Q P` being dualizable (Lemma A); the truncation
step concludes. -/
theorem isIso_homologyMap_homComparisonMonoidal_of_approximation
    [∀ V : X.C, HasWeakSheafify (X.J.over V) AddCommGrpCat.{u}]
    [∀ V : X.C, (X.J.over V).WEqualsLocallyBijective AddCommGrpCat.{u}]
    [∀ V : X.C, HasSheafify (X.J.over V) AddCommGrpCat.{u}] [HasBinaryProducts X.C]
    {P E : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (hP : IsStrictlyPerfect (Stacks.SheafOfModules.Tensor.ringSheaf X.O) P)
    (α : P ⟶ E) (m : ℤ) (hiso : ∀ i : ℤ, m < i → IsIso (HomologicalComplex.homologyMap α i))
    (hepi : Epi (HomologicalComplex.homologyMap α m))
    (M : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (a : ℤ) (hM : M.IsGE a) (j : ℤ) (hj : j < a - m) :
    IsIso ((DerivedCategory.homologyFunctor _ j).map
      (homComparisonMonoidal Ψ (DerivedCategory.Q.obj E) M)) := by
  let := Stacks.SheafOfModules.Strict.exactPairingQStrictlyPerfect X hP
  have hPiso : IsIso (homComparisonMonoidal Ψ (DerivedCategory.Q.obj P) M) :=
    isIso_homComparisonMonoidal_of_exactPairing Ψ _ (DerivedCategory.Q.obj
      (Stacks.SheafOfModules.Strict.dualComplexOfLocallyStrictlyPerfect X.O P
        (Stacks.SheafOfModules.Strict.isLocallyStrictlyPerfect_of_isStrictlyPerfect X.O hP))) M
  obtain ⟨Z, g, δ, hT⟩ := distinguished_cocone_triangle (DerivedCategory.Q.map α)
  have hC := DerivedCategory.isLE_three_of_homologyMap_mor₁ _ hT m
    (fun i hi => (DerivedCategory.isIso_homologyFunctor_map_Q_map_iff α i).2 (hiso i hi))
    ((DerivedCategory.epi_homologyFunctor_map_Q_map_iff α m).2 hepi)
  exact isIso_homologyMap_homComparisonMonoidal_of_distTriang Ψ hLE hGE hH _ hT (m - 1) hC M a hM
    hPiso j (by omega)

end AlgebraicGeometry.RingedSite

end
