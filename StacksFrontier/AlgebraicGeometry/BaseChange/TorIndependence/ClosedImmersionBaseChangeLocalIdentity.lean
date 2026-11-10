module

public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.ClosedImmersionBaseChangeAssembly
public import StacksFrontier.Homology.Tor.BaseChangeIndependence.ComparisonComplexEquations

/-!
# The residual local identity of Stacks 0E23, reduced to a merge coherence

`Stacks.Cohomology.ClosedImmersionBaseChange.LocalBaseChangeIdentityAt` is an identity between
morphisms built from the four local rings of a cartesian square `i' ≫ f = g ≫ i` with `i` a
closed immersion. This file states three successively simpler identities, each implying the
previous one: the first removes the unit of the germ adjunction for `i'` and the underived
comparison of Stacks 065Z, the second also the counit of the germ adjunction for `i`, and the
third also the two comparisons of derived with degreewise extension of scalars.

## Main definitions

* `Stacks.Cohomology.ClosedImmersionBaseChange.MergeCounitIdentityAt`: the residual identity
  with the unit of the germ adjunction for `i'` and the underived comparison removed.
* `Stacks.Cohomology.ClosedImmersionBaseChange.MergeIdentityAt`: the same with the counit of the
  germ adjunction for `i` removed as well.
* `Stacks.Cohomology.ClosedImmersionBaseChange.MergeCoherenceAt`: the same with the two
  comparisons of derived with degreewise extension of scalars removed as well, so that nothing
  is left on either side but the merges, the transports and the source chain.

## Main results

* `Stacks.Cohomology.ClosedImmersionBaseChange.localBaseChangeIdentityAt_of_mergeCounit`:
  `MergeCounitIdentityAt` implies `LocalBaseChangeIdentityAt`.
* `Stacks.Cohomology.ClosedImmersionBaseChange.mergeCounitIdentityAt_of_merge`:
  `MergeIdentityAt` implies `MergeCounitIdentityAt`.
* `Stacks.Cohomology.ClosedImmersionBaseChange.localBaseChangeIdentityAt_of_merge`:
  `MergeIdentityAt` implies `LocalBaseChangeIdentityAt`.
* `Stacks.Cohomology.ClosedImmersionBaseChange.mergeIdentityAt_of_coherence`:
  `MergeCoherenceAt` implies `MergeIdentityAt`.

## Implementation notes

The reductions are instances of the equational lemmas of
`StacksDraft.DerivedStalkLocalIdentityChase`, stated at free objects so that the geometric terms
arrive by unification.

The comparisons of derived with degreewise extension of scalars are spelled two ways, through
`CochainComplex.DerivedExtensionScalars.extensionOfScalarsComplex` and through
`(ModuleCat.extendScalars _).mapHomologicalComplex _ ⋙ DerivedCategory.Q`: the same functor, but
not the same term. Unifying the two inside the chase exhausts the heartbeat budget, so both
characterizing equations are quoted at the unfolded spelling of the degreewise merge.

## References

* [Stacks Project, Tag 065Z](https://stacks.math.columbia.edu/tag/065Z)
* [Stacks Project, Tag 0661](https://stacks.math.columbia.edu/tag/0661)
* [Stacks Project, Tag 0E23](https://stacks.math.columbia.edu/tag/0E23)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open RingedSpaceModuleAdjunction
open CochainComplex.DerivedExtensionScalars
open RingTheory.TorIndependence
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces

noncomputable section

universe u

namespace StacksDraft.DerivedStalkLocalIdentityChase

variable {A : Type*} [Category A]

/-- If `A₀ ≫ B₁ ≫ B₂ ≫ B₃ = pi ≫ RR`, `SI ≫ L = A₀ ≫ B₁ ≫ (B₂ ≫ B₃) ≫ u₁ ≫ u₂` and
`pi' ≫ pi = 𝟙`, then `RR ≫ u₁ ≫ u₂ ≫ z = pi' ≫ SI ≫ L ≫ z`. -/
theorem rhsReduce {a₀ aT c₀ c₁ c₂ c₃ cE cE' cL cF : A}
    (pi : a₀ ⟶ aT) (pi' : aT ⟶ a₀) (A₀ : a₀ ⟶ c₀) (B₁ : c₀ ⟶ c₁) (B₂ : c₁ ⟶ c₂) (B₃ : c₂ ⟶ c₃)
    (RR : aT ⟶ c₃) (u₁ : c₃ ⟶ cE) (u₂ : cE ⟶ cE') (SI : a₀ ⟶ cL) (L : cL ⟶ cE') (z : cE' ⟶ cF)
    (hA : A₀ ≫ B₁ ≫ B₂ ≫ B₃ = pi ≫ RR)
    (hB : SI ≫ L = A₀ ≫ B₁ ≫ (B₂ ≫ B₃) ≫ u₁ ≫ u₂)
    (hinv : pi' ≫ pi = CategoryStruct.id aT) :
    RR ≫ u₁ ≫ u₂ ≫ z = pi' ≫ SI ≫ L ≫ z := by
  rw [reassoc_of% hB, reassoc_of% hA, reassoc_of% hinv]

variable {B : Type*} [Category B]

/-- For an adjunction `adj : Td ⊣ Rd`, the equation `BIG = Ta ≫ cd ≫ mQ` with
`Ta = Td.map (p1 ≫ p2 ≫ p3)` implies `adj.unit.app Y ≫ Rd.map BIG ≫ Fh3 = p1 ≫ p2 ≫ p3 ≫ z`,
given the factorization `z = zU ≫ zR`, the unit equation `hu`, the retraction `Fi ≫ Fh1 = 𝟙`
and the square `hF`. -/
theorem unitReduce (Rd : B ⥤ A) (Td : A ⥤ B) (adj : Td ⊣ Rd)
    {Y y1 y2 xc q₁ tgt : A} {b₁ b₃ : B}
    (BIG : Td.obj Y ⟶ b₃) (Ta : Td.obj Y ⟶ Td.obj xc)
    (p1 : Y ⟶ y1) (p2 : y1 ⟶ y2) (p3 : y2 ⟶ xc)
    (z : xc ⟶ tgt) (zU : xc ⟶ q₁) (zR : q₁ ⟶ tgt)
    (cd : Td.obj xc ⟶ b₁) (mQ : b₁ ⟶ b₃)
    (Fi : q₁ ⟶ Rd.obj b₁) (Fh1 : Rd.obj b₁ ⟶ q₁) (Fh3 : Rd.obj b₃ ⟶ tgt)
    (hz : z = zU ≫ zR)
    (hu : adj.unit.app xc ≫ Rd.map cd = zU ≫ Fi)
    (hinv2 : Fi ≫ Fh1 = CategoryStruct.id q₁)
    (hF : Rd.map mQ ≫ Fh3 = Fh1 ≫ zR)
    (hTa : Td.map (p1 ≫ p2 ≫ p3) = Ta)
    (hres : BIG = Ta ≫ cd ≫ mQ) :
    adj.unit.app Y ≫ Rd.map BIG ≫ Fh3 = p1 ≫ p2 ≫ p3 ≫ z := by
  simp [hres, ← hTa, reassoc_of% hu, hF, reassoc_of% hinv2, hz]

variable {I J K : Type*} [Category I] [Category J] [Category K]

/-- Given the factorizations `hth` of `theta`, `heps` of `eps` and `hsplit` of `zz`, and the
squares `hnat` and `hcmp`, the identity `hres` implies
`m1 ≫ e ≫ m2 ≫ Th.map (Ta.map k1 ≫ k2) ≫ Th.map k3 ≫ cmpC = A ≫ Bm ≫ zz`. -/
theorem counitReduce (Th : J ⥤ K) (Ta : I ⥤ J) (Ra : J ⥤ I)
    {x0 x1 x2 a1 a2 c1 c2 : K} {p q r : J} {s t : I}
    (m1 : x0 ⟶ x1) (e : x1 ⟶ x2) (m2 : x2 ⟶ Th.obj (Ta.obj s))
    (k1 : s ⟶ Ra.obj p) (k2 : Ta.obj (Ra.obj p) ⟶ p) (k3 : p ⟶ q)
    (eps : Ta.obj (Ra.obj q) ⟶ q) (facA : Ra.obj q ⟶ t) (cmpA : Ta.obj t ⟶ r)
    (qeps : r ⟶ q) (cmpC : Th.obj q ⟶ c1) (cmpC' : Th.obj r ⟶ c2) (qext : c2 ⟶ c1)
    (theta : s ⟶ t) (A : x0 ⟶ a1) (Bm : a1 ⟶ a2) (zz : a2 ⟶ c1) (zM : a2 ⟶ c2)
    (hth : theta = k1 ≫ Ra.map k3 ≫ facA)
    (hnat : Ta.map (Ra.map k3) ≫ eps = k2 ≫ k3)
    (heps : eps = Ta.map facA ≫ cmpA ≫ qeps)
    (hcmp : Th.map qeps ≫ cmpC = cmpC' ≫ qext)
    (hsplit : zz = zM ≫ qext)
    (hres : m1 ≫ e ≫ m2 ≫ Th.map (Ta.map theta) ≫ Th.map cmpA ≫ cmpC' = A ≫ Bm ≫ zM) :
    m1 ≫ e ≫ m2 ≫ Th.map (Ta.map k1 ≫ k2) ≫ Th.map k3 ≫ cmpC = A ≫ Bm ≫ zz := by
  have hin : Ta.map k1 ≫ k2 ≫ k3 = Ta.map theta ≫ cmpA ≫ qeps := by
    rw [hth, Ta.map_comp, Ta.map_comp, ← hnat, heps]
    simp
  rw [hsplit, ← reassoc_of% hres, ← hcmp]
  simp only [← Functor.map_comp_assoc, Category.assoc, hin]

variable {L M N : Type*} [Category L] [Category M] [Category N]

/-- If `k₄ ≫ k₃ = 𝟙`, the equations `hbrL`, `hnat`, `hev`, `hbrR` and `htr` and the identity
`hres` imply `n₁ ≫ n₂ ≫ n₃ ≫ uS ≫ A₁ ≫ A₂ = G.map (s₁ ≫ s₂ ≫ s₃ ≫ s₄) ≫ B₁ ≫ F.map (k₁ ≫ k₂ ≫ k₃)`.
-/
theorem mergeReduce (F : M ⥤ L) (G : N ⥤ L)
    {d₁ d₂ d₃ d₄ : M} (k₁ : d₁ ⟶ d₂) (k₂ : d₂ ⟶ d₃) (k₃ : d₃ ⟶ d₄) (k₄ : d₄ ⟶ d₃)
    {e₁ e₂ e₃ e₄ e₅ : N} (s₁ : e₁ ⟶ e₂) (s₂ : e₂ ⟶ e₃) (s₃ : e₃ ⟶ e₄) (s₄ : e₄ ⟶ e₅)
    {p₁ p₂ p₃ p₄ p₅ v₁ v₂ v₂' : L}
    (n₁ : G.obj e₁ ⟶ p₁) (n₂ : p₁ ⟶ p₂) (n₃ : p₂ ⟶ p₃)
    (uS : p₃ ⟶ p₄) (A₁ : p₄ ⟶ p₅) (A₂ : p₅ ⟶ F.obj d₄)
    (Mh : p₄ ⟶ v₂) (cphi : v₂ ⟶ F.obj d₃)
    (Mh₁ : p₃ ⟶ v₁) (vS : v₁ ⟶ v₂) (ev : p₂ ⟶ v₁)
    (B₁ : G.obj e₅ ⟶ F.obj d₁)
    (Mh' : G.obj e₄ ⟶ v₂') (cphi' : v₂' ⟶ F.obj d₂) (ev' : v₂' ⟶ v₂)
    (hk : k₄ ≫ k₃ = CategoryStruct.id d₄)
    (hbrL : A₁ ≫ A₂ ≫ F.map k₄ = Mh ≫ cphi)
    (hnat : uS ≫ Mh = Mh₁ ≫ vS)
    (hev : n₃ ≫ Mh₁ = ev)
    (hbrR : G.map s₄ ≫ B₁ ≫ F.map k₁ = Mh' ≫ cphi')
    (htr : cphi' ≫ F.map k₂ = ev' ≫ cphi)
    (hres : n₁ ≫ n₂ ≫ ev ≫ vS = G.map (s₁ ≫ s₂ ≫ s₃) ≫ Mh' ≫ ev') :
    n₁ ≫ n₂ ≫ n₃ ≫ uS ≫ A₁ ≫ A₂ =
      G.map (s₁ ≫ s₂ ≫ s₃ ≫ s₄) ≫ B₁ ≫ F.map (k₁ ≫ k₂ ≫ k₃) := by
  have hFk : F.map k₄ ≫ F.map k₃ = CategoryStruct.id (F.obj d₄) := by
    rw [← F.map_comp, hk, F.map_id]
  rw [← Category.comp_id A₂, ← hFk, reassoc_of% hbrL, reassoc_of% hnat, reassoc_of% hev,
    reassoc_of% hres, ← reassoc_of% htr, ← reassoc_of% hbrR]
  simp

end StacksDraft.DerivedStalkLocalIdentityChase

namespace Stacks.Cohomology.ClosedImmersionBaseChange

attribute [local instance] HasDerivedCategory.standard

section Square

variable {Z' X' Z X : Scheme.{u}} {i' : Z' ⟶ X'} {g : Z' ⟶ Z} {f : X' ⟶ X} {i : Z ⟶ X}

attribute [local instance] isLeftDerived_alphaG isLeftDerived_alphaH

open Stacks.Cohomology.DerivedBaseChange in
/-- The *merge–counit identity* at `w` and `P`: the residual local identity of Stacks 0E23 with
the unit of the germ adjunction for `i'` and the underived comparison of Stacks 065Z removed.

On the left, the merge of the extensions of scalars for `i'` and `f`, the transport along the
diagonal of the square, the merge for `g` and `i` read backwards, the counit of the germ
adjunction for `i` at `g w` and the two factorizations that bring the derived stalk at `g w` down
to `DerivedCategory.Q` of the stalk complex — that is, the argument of derived restriction of
scalars in `Stacks.Cohomology.ClosedImmersionBaseChange.LocalBaseChangeIdentityAt`.

On the right, derived extension of scalars along the germ map of `i'` of the source chain of
Stacks 0661 read against its comparison, then the comparison of derived with degreewise extension
of scalars along that germ map, and then `DerivedCategory.Q` of the *degreewise* merge and counit
that `RingTheory.TorIndependence.derivedBaseChangeComparison_fst_mapHomologicalComplex_app`
exhibits the underived comparison as. -/
abbrev MergeCounitIdentityAt (sq : IsPullback i' g f i)
    [AlgebraicGeometry.IsClosedImmersion i] (w : Z')
    (P : CochainComplex Z.Modules ℤ) : Prop :=
  letI := isClosedImmersion_of_isPullback sq
  (AlgebraicGeometry.derivedStalkExtensionCompIso i' f w).hom.app
        ((AlgebraicGeometry.derivedStalkFunctor (f (i' w))).obj
          ((derivedPushforward i.toLRSHom.toShHom).obj (DerivedCategory.Q.obj P))) ≫
      eqToHom (congrArg (fun ψ : Z' ⟶ X =>
          (totalDerivedExtensionScalars.{u, u, u} (ψ.stalkMap w).hom).functor.obj
            ((AlgebraicGeometry.derivedStalkFunctor (ψ w)).obj
              ((derivedPushforward i.toLRSHom.toShHom).obj
                (DerivedCategory.Q.obj P)))) sq.w) ≫
        (AlgebraicGeometry.derivedStalkExtensionCompIso g i w).inv.app
            ((AlgebraicGeometry.derivedStalkFunctor (i (g w))).obj
              ((derivedPushforward i.toLRSHom.toShHom).obj (DerivedCategory.Q.obj P))) ≫
          (totalDerivedExtensionScalars.{u, u, u} (g.stalkMap w).hom).functor.map
              ((totalDerivedExtensionScalars.{u, u, u} (i.stalkMap (g w)).hom).functor.map
                  ((AlgebraicGeometry.derivedStalkDerivedPushforwardIsoOfSchemesLocalRing
                    i (g w)).hom.app (DerivedCategory.Q.obj P)) ≫
                (AlgebraicGeometry.derivedStalkGermAdjunction i (g w)).counit.app
                  ((AlgebraicGeometry.derivedStalkFunctor (g w)).obj
                    (DerivedCategory.Q.obj P))) ≫
            (totalDerivedExtensionScalars.{u, u, u} (g.stalkMap w).hom).functor.map
                ((Stacks.ModuleSkyscraper.modulesStalkFunctor Z
                  (g w)).mapDerivedCategoryFactors.hom.app P) ≫
              (totalDerivedExtensionScalars.{u, u, u} (g.stalkMap w).hom).comparison.app
                (((Stacks.ModuleSkyscraper.modulesStalkFunctor Z
                  (g w)).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) =
    (totalDerivedExtensionScalars.{u, u, u} (i'.stalkMap w).hom).functor.map
        ((AlgebraicGeometry.derivedPullbackStalkIso f (i' w)).inv.app
            ((derivedPushforward i.toLRSHom.toShHom).obj (DerivedCategory.Q.obj P)) ≫
          (derivedStalkSourceIso w (ptEq sq w)).hom.app (DerivedCategory.Q.obj P) ≫
            (Lg w (ptEq sq w)).map
                ((ModuleCat.restrictScalars.{u, u, u}
                    (i.stalkMap (g w)).hom).mapDerivedCategory.map
                    ((Stacks.ModuleSkyscraper.modulesStalkFunctor Z
                      (g w)).mapDerivedCategoryFactors.hom.app P) ≫
                  (ModuleCat.restrictScalars.{u, u, u}
                      (i.stalkMap (g w)).hom).mapDerivedCategoryFactors.hom.app
                    (((Stacks.ModuleSkyscraper.modulesStalkFunctor Z
                      (g w)).mapHomologicalComplex (ComplexShape.up ℤ)).obj P)) ≫
              (alphaG w (ptEq sq w)).app
                (((ModuleCat.restrictScalars.{u, u, u}
                    (i.stalkMap (g w)).hom).mapHomologicalComplex (ComplexShape.up ℤ)).obj
                  (((Stacks.ModuleSkyscraper.modulesStalkFunctor Z
                    (g w)).mapHomologicalComplex (ComplexShape.up ℤ)).obj P))) ≫
      (AlgebraicGeometry.germAlpha i' w).app
          (((ModuleCat.extendScalars.{u, u, u} (ringRR' w (ptEq sq w))).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj
            (((ModuleCat.restrictScalars.{u, u, u} (i.stalkMap (g w)).hom).mapHomologicalComplex
                (ComplexShape.up ℤ)).obj
              (((Stacks.ModuleSkyscraper.modulesStalkFunctor Z
                (g w)).mapHomologicalComplex (ComplexShape.up ℤ)).obj P))) ≫
        DerivedCategory.Q.map
          (((Functor.mapHomologicalComplexCompIso
                      (ModuleCat.extendScalarsComp (ringRR' w (ptEq sq w))
                        (i'.stalkMap w).hom).symm (ComplexShape.up ℤ)).hom.app
                (((ModuleCat.restrictScalars.{u, u, u}
                    (i.stalkMap (g w)).hom).mapHomologicalComplex (ComplexShape.up ℤ)).obj
                  (((Stacks.ModuleSkyscraper.modulesStalkFunctor Z
                    (g w)).mapHomologicalComplex (ComplexShape.up ℤ)).obj P)) ≫
              eqToHom (congrArg (fun φ =>
                  ((ModuleCat.extendScalars.{u, u, u} φ).mapHomologicalComplex
                      (ComplexShape.up ℤ)).obj
                    (((ModuleCat.restrictScalars.{u, u, u}
                        (i.stalkMap (g w)).hom).mapHomologicalComplex (ComplexShape.up ℤ)).obj
                      (((Stacks.ModuleSkyscraper.modulesStalkFunctor Z
                        (g w)).mapHomologicalComplex (ComplexShape.up ℤ)).obj P)))
                (stalkMap_ringHom_square sq w (ptEq sq w)).symm) ≫
                (Functor.mapHomologicalComplexCompIso
                        (ModuleCat.extendScalarsComp (i.stalkMap (g w)).hom
                          (g.stalkMap w).hom).symm (ComplexShape.up ℤ)).inv.app
                  (((ModuleCat.restrictScalars.{u, u, u}
                      (i.stalkMap (g w)).hom).mapHomologicalComplex (ComplexShape.up ℤ)).obj
                    (((Stacks.ModuleSkyscraper.modulesStalkFunctor Z
                      (g w)).mapHomologicalComplex (ComplexShape.up ℤ)).obj P))) ≫
            ((ModuleCat.extendScalars.{u, u, u} (g.stalkMap w).hom).mapHomologicalComplex
                  (ComplexShape.up ℤ)).map
              (((ModuleCat.extendRestrictScalarsAdj.{u, u, u}
                      (i.stalkMap (g w)).hom).mapHomologicalComplex (ComplexShape.up ℤ)).counit.app
                (((Stacks.ModuleSkyscraper.modulesStalkFunctor Z
                  (g w)).mapHomologicalComplex (ComplexShape.up ℤ)).obj P)))

open Stacks.Cohomology.DerivedBaseChange StacksDraft.DerivedStalkLocalIdentityChase in
/-- The merge–counit identity implies the residual local identity
`LocalBaseChangeIdentityAt`. -/
theorem localBaseChangeIdentityAt_of_mergeCounit (sq : IsPullback i' g f i)
    [AlgebraicGeometry.IsClosedImmersion i] (w : Z')
    (P : CochainComplex Z.Modules ℤ) (hmc : MergeCounitIdentityAt sq w P) :
    LocalBaseChangeIdentityAt sq w P := by
  refine Eq.trans ?_ (rhsReduce _
    ((AlgebraicGeometry.derivedPullbackStalkIso f (i' w)).inv.app
      ((derivedPushforward i.toLRSHom.toShHom).obj (DerivedCategory.Q.obj P)))
    _ _ _ _ _ _ _ _ _ _
    (rhsChaseGeom (i' := i') (f := f) (i := i) w P)
    (derivedStalkSourceIso_hom_app_Q_comp_alphaG (i' := i') (f := f) w (ptEq sq w) P)
    ((AlgebraicGeometry.derivedPullbackStalkIso f (i' w)).inv_hom_id_app
      ((derivedPushforward i.toLRSHom.toShHom).obj (DerivedCategory.Q.obj P)))).symm
  have hA1 := derivedBaseChangeComparison_fst_mapHomologicalComplex_app.{u}
    (i.stalkMap (g w)).hom (ringRR' w (ptEq sq w)) (g.stalkMap w).hom (i'.stalkMap w).hom
    (stalkMap_ringHom_square sq w (ptEq sq w)) (Lg w (ptEq sq w)) (Lh w)
    (alphaG w (ptEq sq w)) (alphaH w)
    (((Stacks.ModuleSkyscraper.modulesStalkFunctor Z (g w)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj P)
  have hz := (congrArg DerivedCategory.Q.map hA1).trans (DerivedCategory.Q.map_comp _ _)
  have hu := derivedExtensionScalarsAdjunction_unit_app.{u, u, u} (i'.stalkMap w).hom
    (totalDerivedExtensionScalars.{u, u, u} (i'.stalkMap w).hom).functor
    (AlgebraicGeometry.germAlpha i' w)
    (((ModuleCat.extendScalars.{u, u, u} (ringRR' w (ptEq sq w))).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj
      (((ModuleCat.restrictScalars.{u, u, u} (i.stalkMap (g w)).hom).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj
        (((Stacks.ModuleSkyscraper.modulesStalkFunctor Z (g w)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj P)))
  exact unitReduce _ _ (AlgebraicGeometry.derivedStalkGermAdjunction i' w)
    _ _ _ _ _ _ _ _ _ _ _ _ _ hz hu (Iso.inv_hom_id_app _ _)
    ((ModuleCat.restrictScalars.{u, u, u}
      (i'.stalkMap w).hom).mapDerivedCategoryFactors.hom.naturality _) rfl hmc

open Stacks.Cohomology.DerivedBaseChange in
/-- The *merge identity* at `w` and `P`: `MergeCounitIdentityAt` with the counit of the germ
adjunction for `i` removed as well.

On the left, the merge of the extensions of scalars for `i'` and `f`, the transport along the
diagonal of the square, the merge for `g` and `i` read backwards, and then — all under derived
extension of scalars along the germ map of `g` — the derived stalk of `Ri_*` on the image, the
two factorizations that bring the derived stalk at `g w` down to `DerivedCategory.Q` of the stalk
complex, and the comparisons of derived with degreewise extension of scalars along the germ maps
of `i` and of `g`.

On the right, the same as in `MergeCounitIdentityAt`, with the degreewise counit removed from the
trailing `DerivedCategory.Q`: only the two degreewise merges and the transport along the square
of germ maps are left there. -/
abbrev MergeIdentityAt (sq : IsPullback i' g f i)
    [AlgebraicGeometry.IsClosedImmersion i] (w : Z')
    (P : CochainComplex Z.Modules ℤ) : Prop :=
  letI := isClosedImmersion_of_isPullback sq
  (AlgebraicGeometry.derivedStalkExtensionCompIso i' f w).hom.app
        ((AlgebraicGeometry.derivedStalkFunctor (f (i' w))).obj
          ((derivedPushforward i.toLRSHom.toShHom).obj (DerivedCategory.Q.obj P))) ≫
      eqToHom (congrArg (fun ψ : Z' ⟶ X =>
          (totalDerivedExtensionScalars.{u, u, u} (ψ.stalkMap w).hom).functor.obj
            ((AlgebraicGeometry.derivedStalkFunctor (ψ w)).obj
              ((derivedPushforward i.toLRSHom.toShHom).obj
                (DerivedCategory.Q.obj P)))) sq.w) ≫
        (AlgebraicGeometry.derivedStalkExtensionCompIso g i w).inv.app
            ((AlgebraicGeometry.derivedStalkFunctor (i (g w))).obj
              ((derivedPushforward i.toLRSHom.toShHom).obj (DerivedCategory.Q.obj P))) ≫
          (totalDerivedExtensionScalars.{u, u, u} (g.stalkMap w).hom).functor.map
              ((totalDerivedExtensionScalars.{u, u, u} (i.stalkMap (g w)).hom).functor.map
                ((AlgebraicGeometry.derivedStalkDerivedPushforwardIsoOfSchemesLocalRing
                      i (g w)).hom.app (DerivedCategory.Q.obj P) ≫
                  (ModuleCat.restrictScalars.{u, u, u}
                      (i.stalkMap (g w)).hom).mapDerivedCategory.map
                      ((Stacks.ModuleSkyscraper.modulesStalkFunctor Z
                        (g w)).mapDerivedCategoryFactors.hom.app P) ≫
                    (ModuleCat.restrictScalars.{u, u, u}
                        (i.stalkMap (g w)).hom).mapDerivedCategoryFactors.hom.app
                      (((Stacks.ModuleSkyscraper.modulesStalkFunctor Z
                        (g w)).mapHomologicalComplex (ComplexShape.up ℤ)).obj P))) ≫
            (totalDerivedExtensionScalars.{u, u, u} (g.stalkMap w).hom).functor.map
                ((AlgebraicGeometry.germAlpha i (g w)).app
                  (((ModuleCat.restrictScalars.{u, u, u}
                      (i.stalkMap (g w)).hom).mapHomologicalComplex
                      (ComplexShape.up ℤ)).obj
                    (((Stacks.ModuleSkyscraper.modulesStalkFunctor Z
                      (g w)).mapHomologicalComplex (ComplexShape.up ℤ)).obj P))) ≫
              (totalDerivedExtensionScalars.{u, u, u} (g.stalkMap w).hom).comparison.app
                (((ModuleCat.extendScalars.{u, u, u}
                    (i.stalkMap (g w)).hom).mapHomologicalComplex (ComplexShape.up ℤ)).obj
                  (((ModuleCat.restrictScalars.{u, u, u}
                      (i.stalkMap (g w)).hom).mapHomologicalComplex (ComplexShape.up ℤ)).obj
                    (((Stacks.ModuleSkyscraper.modulesStalkFunctor Z
                      (g w)).mapHomologicalComplex (ComplexShape.up ℤ)).obj P))) =
    (totalDerivedExtensionScalars.{u, u, u} (i'.stalkMap w).hom).functor.map
        ((AlgebraicGeometry.derivedPullbackStalkIso f (i' w)).inv.app
            ((derivedPushforward i.toLRSHom.toShHom).obj (DerivedCategory.Q.obj P)) ≫
          (derivedStalkSourceIso w (ptEq sq w)).hom.app (DerivedCategory.Q.obj P) ≫
            (Lg w (ptEq sq w)).map
                ((ModuleCat.restrictScalars.{u, u, u}
                    (i.stalkMap (g w)).hom).mapDerivedCategory.map
                    ((Stacks.ModuleSkyscraper.modulesStalkFunctor Z
                      (g w)).mapDerivedCategoryFactors.hom.app P) ≫
                  (ModuleCat.restrictScalars.{u, u, u}
                      (i.stalkMap (g w)).hom).mapDerivedCategoryFactors.hom.app
                    (((Stacks.ModuleSkyscraper.modulesStalkFunctor Z
                      (g w)).mapHomologicalComplex (ComplexShape.up ℤ)).obj P)) ≫
              (alphaG w (ptEq sq w)).app
                (((ModuleCat.restrictScalars.{u, u, u}
                    (i.stalkMap (g w)).hom).mapHomologicalComplex (ComplexShape.up ℤ)).obj
                  (((Stacks.ModuleSkyscraper.modulesStalkFunctor Z
                    (g w)).mapHomologicalComplex (ComplexShape.up ℤ)).obj P))) ≫
      (AlgebraicGeometry.germAlpha i' w).app
          (((ModuleCat.extendScalars.{u, u, u} (ringRR' w (ptEq sq w))).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj
            (((ModuleCat.restrictScalars.{u, u, u} (i.stalkMap (g w)).hom).mapHomologicalComplex
                (ComplexShape.up ℤ)).obj
              (((Stacks.ModuleSkyscraper.modulesStalkFunctor Z
                (g w)).mapHomologicalComplex (ComplexShape.up ℤ)).obj P))) ≫
        DerivedCategory.Q.map
          ((Functor.mapHomologicalComplexCompIso
                    (ModuleCat.extendScalarsComp (ringRR' w (ptEq sq w))
                      (i'.stalkMap w).hom).symm (ComplexShape.up ℤ)).hom.app
                (((ModuleCat.restrictScalars.{u, u, u}
                    (i.stalkMap (g w)).hom).mapHomologicalComplex (ComplexShape.up ℤ)).obj
                  (((Stacks.ModuleSkyscraper.modulesStalkFunctor Z
                    (g w)).mapHomologicalComplex (ComplexShape.up ℤ)).obj P)) ≫
              eqToHom (congrArg (fun φ =>
                  ((ModuleCat.extendScalars.{u, u, u} φ).mapHomologicalComplex
                      (ComplexShape.up ℤ)).obj
                    (((ModuleCat.restrictScalars.{u, u, u}
                        (i.stalkMap (g w)).hom).mapHomologicalComplex (ComplexShape.up ℤ)).obj
                      (((Stacks.ModuleSkyscraper.modulesStalkFunctor Z
                        (g w)).mapHomologicalComplex (ComplexShape.up ℤ)).obj P)))
                (stalkMap_ringHom_square sq w (ptEq sq w)).symm) ≫
                (Functor.mapHomologicalComplexCompIso
                        (ModuleCat.extendScalarsComp (i.stalkMap (g w)).hom
                          (g.stalkMap w).hom).symm (ComplexShape.up ℤ)).inv.app
                  (((ModuleCat.restrictScalars.{u, u, u}
                      (i.stalkMap (g w)).hom).mapHomologicalComplex (ComplexShape.up ℤ)).obj
                    (((Stacks.ModuleSkyscraper.modulesStalkFunctor Z
                      (g w)).mapHomologicalComplex (ComplexShape.up ℤ)).obj P)))

open Stacks.Cohomology.DerivedBaseChange StacksDraft.DerivedStalkLocalIdentityChase in
/-- The merge identity implies the merge–counit identity. -/
theorem mergeCounitIdentityAt_of_merge (sq : IsPullback i' g f i)
    [AlgebraicGeometry.IsClosedImmersion i] (w : Z')
    (P : CochainComplex Z.Modules ℤ) (hm : MergeIdentityAt sq w P) :
    MergeCounitIdentityAt sq w P := by
  have := isClosedImmersion_of_isPullback sq
  exact counitReduce _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ rfl
    (Adjunction.counit_naturality (AlgebraicGeometry.derivedStalkGermAdjunction i (g w))
      ((Stacks.ModuleSkyscraper.modulesStalkFunctor Z (g w)).mapDerivedCategoryFactors.hom.app P))
    (derivedExtensionScalarsAdjunction_counit_app_eq.{u, u, u} (i.stalkMap (g w)).hom
      (totalDerivedExtensionScalars.{u, u, u} (i.stalkMap (g w)).hom).functor
      (AlgebraicGeometry.germAlpha i (g w))
      (((Stacks.ModuleSkyscraper.modulesStalkFunctor Z (g w)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj P))
    ((totalDerivedExtensionScalars.{u, u, u} (g.stalkMap w).hom).comparison.naturality _)
    (DerivedCategory.Q.map_comp _ _) hm

open Stacks.Cohomology.DerivedBaseChange in
/-- The *merge coherence* at `w` and `P`: `MergeIdentityAt` with the two comparisons of derived
with degreewise extension of scalars removed as well.

On the left, the merge of the extensions of scalars for `i'` and `f`, the transport along the
diagonal of the square, the transport along `Stacks.ModuleSkyscraper.stalkMap_hom_comp` for `g`
and `i`, and — under derived extension of scalars along the germ map of `g ≫ i` — the derived
stalk of `Ri_*` on the image together with the two factorizations that bring the derived stalk at
`g w` down to `DerivedCategory.Q` of the stalk complex.

On the right, derived extension of scalars along the germ map of `i'` of the source chain of
Stacks 0661 read against its comparison, then the *untransported* composition isomorphism
`StacksDraft.DerivedExtensionScalarsComp.derivedExtensionScalarsCompIso` for the germ map of `f`
through the comparison of the two presentations of the image point and the germ map of `i'`, and
then the transport along
`Stacks.Cohomology.ClosedImmersionBaseChange.stalkMap_ringHom_square`.

Neither side carries a unit, a counit or a comparison. -/
abbrev MergeCoherenceAt (sq : IsPullback i' g f i)
    [AlgebraicGeometry.IsClosedImmersion i] (w : Z')
    (P : CochainComplex Z.Modules ℤ) : Prop :=
  letI := isClosedImmersion_of_isPullback sq
  (AlgebraicGeometry.derivedStalkExtensionCompIso i' f w).hom.app
        ((AlgebraicGeometry.derivedStalkFunctor (f (i' w))).obj
          ((derivedPushforward i.toLRSHom.toShHom).obj (DerivedCategory.Q.obj P))) ≫
      eqToHom (congrArg (fun ψ : Z' ⟶ X =>
          (totalDerivedExtensionScalars.{u, u, u} (ψ.stalkMap w).hom).functor.obj
            ((AlgebraicGeometry.derivedStalkFunctor (ψ w)).obj
              ((derivedPushforward i.toLRSHom.toShHom).obj
                (DerivedCategory.Q.obj P)))) sq.w) ≫
        eqToHom (congrArg (fun φ =>
            (totalDerivedExtensionScalars.{u, u, u} φ).functor.obj
              ((AlgebraicGeometry.derivedStalkFunctor (i (g w))).obj
                ((derivedPushforward i.toLRSHom.toShHom).obj (DerivedCategory.Q.obj P))))
          (Stacks.ModuleSkyscraper.stalkMap_hom_comp g i w)) ≫
          (totalDerivedExtensionScalars.{u, u, u}
                ((g.stalkMap w).hom.comp (i.stalkMap (g w)).hom)).functor.map
              ((AlgebraicGeometry.derivedStalkDerivedPushforwardIsoOfSchemesLocalRing
                    i (g w)).hom.app (DerivedCategory.Q.obj P) ≫
                (ModuleCat.restrictScalars.{u, u, u}
                    (i.stalkMap (g w)).hom).mapDerivedCategory.map
                    ((Stacks.ModuleSkyscraper.modulesStalkFunctor Z
                      (g w)).mapDerivedCategoryFactors.hom.app P) ≫
                  (ModuleCat.restrictScalars.{u, u, u}
                      (i.stalkMap (g w)).hom).mapDerivedCategoryFactors.hom.app
                    (((Stacks.ModuleSkyscraper.modulesStalkFunctor Z
                      (g w)).mapHomologicalComplex (ComplexShape.up ℤ)).obj P)) =
    (totalDerivedExtensionScalars.{u, u, u} (i'.stalkMap w).hom).functor.map
        ((AlgebraicGeometry.derivedPullbackStalkIso f (i' w)).inv.app
            ((derivedPushforward i.toLRSHom.toShHom).obj (DerivedCategory.Q.obj P)) ≫
          (derivedStalkSourceIso w (ptEq sq w)).hom.app (DerivedCategory.Q.obj P) ≫
            (Lg w (ptEq sq w)).map
              ((ModuleCat.restrictScalars.{u, u, u}
                  (i.stalkMap (g w)).hom).mapDerivedCategory.map
                  ((Stacks.ModuleSkyscraper.modulesStalkFunctor Z
                    (g w)).mapDerivedCategoryFactors.hom.app P) ≫
                (ModuleCat.restrictScalars.{u, u, u}
                    (i.stalkMap (g w)).hom).mapDerivedCategoryFactors.hom.app
                  (((Stacks.ModuleSkyscraper.modulesStalkFunctor Z
                    (g w)).mapHomologicalComplex (ComplexShape.up ℤ)).obj P))) ≫
      (StacksDraft.DerivedExtensionScalarsComp.derivedExtensionScalarsCompIso
            (ringRR' w (ptEq sq w)) (i'.stalkMap w).hom).hom.app
          (DerivedCategory.Q.obj
            (((ModuleCat.restrictScalars.{u, u, u} (i.stalkMap (g w)).hom).mapHomologicalComplex
                (ComplexShape.up ℤ)).obj
              (((Stacks.ModuleSkyscraper.modulesStalkFunctor Z
                (g w)).mapHomologicalComplex (ComplexShape.up ℤ)).obj P))) ≫
        eqToHom (congrArg (fun χ =>
            (totalDerivedExtensionScalars.{u, u, u} χ).functor.obj
              (DerivedCategory.Q.obj
                (((ModuleCat.restrictScalars.{u, u, u}
                    (i.stalkMap (g w)).hom).mapHomologicalComplex (ComplexShape.up ℤ)).obj
                  (((Stacks.ModuleSkyscraper.modulesStalkFunctor Z
                    (g w)).mapHomologicalComplex (ComplexShape.up ℤ)).obj P))))
          (stalkMap_ringHom_square sq w (ptEq sq w)).symm)

open Stacks.Cohomology.DerivedBaseChange StacksDraft.DerivedStalkLocalIdentityChase in
/-- The merge coherence implies the merge identity. -/
theorem mergeIdentityAt_of_coherence (sq : IsPullback i' g f i)
    [AlgebraicGeometry.IsClosedImmersion i] (w : Z')
    (P : CochainComplex Z.Modules ℤ) (hc : MergeCoherenceAt sq w P) :
    MergeIdentityAt sq w P := by
  have := isClosedImmersion_of_isPullback sq
  open StacksDraft.DerivedExtensionScalarsComp in
  exact mergeReduce (F := DerivedCategory.Q)
    (G := (totalDerivedExtensionScalars.{u, u, u} (i'.stalkMap w).hom).functor)
    (hk := Iso.hom_inv_id_app
      (Functor.mapHomologicalComplexCompIso
        (ModuleCat.extendScalarsComp (i.stalkMap (g w)).hom (g.stalkMap w).hom).symm
        (ComplexShape.up ℤ)) _)
    (hbrL := comparison_comp_comparison_comp_mapHomologicalComplexCompIso.{u}
        (i.stalkMap (g w)).hom (g.stalkMap w).hom _)
    (hnat := (StacksDraft.DerivedExtensionScalarsComp.derivedExtensionScalarsCompIso
      (i.stalkMap (g w)).hom (g.stalkMap w).hom).hom.naturality _)
    (hev := AlgebraicGeometry.derivedStalkExtensionCompIso_inv_app_comp_compIso_hom_app g i w _)
    (hbrR := comparison_comp_comparison_comp_mapHomologicalComplexCompIso.{u}
        (ringRR' w (ptEq sq w)) (i'.stalkMap w).hom _)
    (htr := StacksDraft.DerivedExtensionScalarsComp.comparison_app_comp_Q_map_eqToHom
      ((i'.stalkMap w).hom.comp (ringRR' w (ptEq sq w)))
      ((g.stalkMap w).hom.comp (i.stalkMap (g w)).hom)
      (stalkMap_ringHom_square sq w (ptEq sq w)).symm _)
    (hres := hc)

open Stacks.Cohomology.DerivedBaseChange in
/-- The merge identity implies the residual local identity `LocalBaseChangeIdentityAt`. -/
theorem localBaseChangeIdentityAt_of_merge (sq : IsPullback i' g f i)
    [AlgebraicGeometry.IsClosedImmersion i] (w : Z')
    (P : CochainComplex Z.Modules ℤ) (hm : MergeIdentityAt sq w P) :
    LocalBaseChangeIdentityAt sq w P :=
  localBaseChangeIdentityAt_of_mergeCounit sq w P (mergeCounitIdentityAt_of_merge sq w P hm)

end Square

end Stacks.Cohomology.ClosedImmersionBaseChange

end

end
