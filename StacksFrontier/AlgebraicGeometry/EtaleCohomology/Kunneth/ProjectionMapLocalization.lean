module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Kunneth.ProjectionMapColimit
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Kunneth.EtaleCoefficientsAbelianPullback
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.CoverTriangle
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Kunneth.EtaleCoefficientsOpenImmersionBaseChange
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryHomology

/-!
# The projection map of Tag 0F1J is local on `X`

The step "This question is local on `X` hence we may assume `X` is affine" of the proof of
[Stacks, Tag 0F1J], and with it Tag 0F1J for `n = ℓ` prime over an arbitrary `X`, from derived
base change.

* **Isomorphisms are local.** A morphism of `D(X_étale, ℤ/m)` is an isomorphism as soon as its
  inverse images along a jointly surjective family are (`isIso_of_forall_isIso_pullback_map`):
  on the underlying abelian sheaves this is the joint conservativity of inverse images
  (`Stacks.EtaleCohomology.isIso_of_isIso_etaleAbelianInverseImage_family`).
* **The projection map restricts to opens.** For an open immersion `ι : V ⟶ X'` and
  `VY = Y ×_{X'} V`, the inverse image along `ι` of the projection map of `h` is the projection
  map of `VY ⟶ V`, up to the comparisons of Tag 07A4 and base change maps along open immersions
  (`isIso_pullback_map_projectionMap_iff`). The compatibility is
  `Stacks.ProjectionFormula.projectionMap_baseChange_square`, the variant of Tag 0E48 with the
  counit in the second factor, and base change along an open immersion holds on `D⁺`
  (`isIso_baseChangeMap_app_of_isOpenImmersion`).

## Main results

* `isIso_projectionMap_pullback_singleFunctor_of_forall_isAffine`
  — the projection map of Tag 0F1J at single sheaves of `𝔽_ℓ`-vector spaces, for an arbitrary `X`.
* `Stacks.EtaleCohomology.EtaleCoefficients.isIso_tensorBaseChangeMap_of_derivedBaseChangeHolds`
  — Tag 0F1J for `n = ℓ` prime.

Not registered: derived base change along `X ⟶ S` and along the finite schemes over the affine
opens of `X` are explicit arguments ([Stacks, Tag 0F1I] for `S = Spec K`), and the passage from
`ℤ/nℤ` to `𝔽_ℓ` coefficients of the source's proof is not formalized here.

## References

* [Stacks Project, Tag 0F1J](https://stacks.math.columbia.edu/tag/0F1J)
* [Stacks Project, Tag 0E48](https://stacks.math.columbia.edu/tag/0E48)
* [Stacks Project, Tag 0F02](https://stacks.math.columbia.edu/tag/0F02)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.Prod

universe u

namespace Stacks.ProjectionFormula

section Square

variable {S : Type*} {T : Type*} {S' : Type*} {T' : Type*}
  [Category S] [Category T] [Category S'] [Category T']
  {Lf : S ⥤ T} {Rf : T ⥤ S} {Lf' : S' ⥤ T'} {Rf' : T' ⥤ S'}
  {Lg : S ⥤ S'} {Lg' : T ⥤ T'} {Lc : S ⥤ T'}
  (adjf : Lf ⊣ Rf) (adjf' : Lf' ⊣ Rf') (eg : Lg ⋙ Lf' ≅ Lc) (ef : Lf ⋙ Lg' ≅ Lc)
  (A : S × S ⥤ S) (A' : S' × S' ⥤ S') (B : T × T ⥤ T) (B' : T' × T' ⥤ T')
  (αf : A ⋙ Lf ⟶ Lf.prod Lf ⋙ B) (αf' : A' ⋙ Lf' ⟶ Lf'.prod Lf' ⋙ B')
  (αg : A ⋙ Lg ⟶ Lg.prod Lg ⋙ A') (αg' : B ⋙ Lg' ⟶ Lg'.prod Lg' ⋙ B')

/-- **The projection map `K ⊗ Rf E ⟶ Rf(Lf K ⊗ E)` is compatible with base change** around a
square of adjunctions whose two composites are identified with one functor: the variant of
[Stacks, Tag 0E48] (`Stacks.AffineProjectionFormula.adjunctionTensorMap_baseChange_square`) with
the counit in the second factor. The one input is the compatibility of the four comparisons
around the square, at `(K, Rf E)`. Both sides are maps into `Rf'`-of-something; their adjuncts
under `Lf' ⊣ Rf'` are both the comparison along `Lg` and then along `Lf'`, followed by the
counit of `Lf ⊣ Rf` read through the square in the second factor. -/
theorem projectionMap_baseChange_square (K : S) (E : T)
    (hsq : Stacks.AffineProjectionFormula.TensorComparisonCompatible eg ef A A' B B' αf αf' αg αg'
      K (Rf.obj E)) :
    αg.app (K, Rf.obj E) ≫
        A'.map (𝟙 (Lg.obj K) ×ₘ Stacks.CategoryTheory.BaseChange.map adjf adjf' eg ef E) ≫
          Stacks.Cohomology.AbstractKunnethMap.projectionMap A' B' adjf' αf' (Lg.obj K)
            (Lg'.obj E) =
      Lg.map (Stacks.Cohomology.AbstractKunnethMap.projectionMap A B adjf αf K E) ≫
        Stacks.CategoryTheory.BaseChange.map adjf adjf' eg ef (B.obj (Lf.obj K, E)) ≫
          Rf'.map (αg'.app (Lf.obj K, E) ≫
            B'.map ((Stacks.AffineProjectionFormula.squareCompositeIso eg ef).inv.app K ×ₘ
              𝟙 (Lg'.obj E))) := by
  rw [Stacks.AffineProjectionFormula.TensorComparisonCompatible] at hsq
  have h1 : Lf'.map (A'.map
        (𝟙 (Lg.obj K) ×ₘ Stacks.CategoryTheory.BaseChange.map adjf adjf' eg ef E)) ≫
      αf'.app (Lg.obj K, Rf'.obj (Lg'.obj E)) =
      αf'.app (Lg.obj K, Lg.obj (Rf.obj E)) ≫
        B'.map (𝟙 (Lf'.obj (Lg.obj K)) ×ₘ
          Lf'.map (Stacks.CategoryTheory.BaseChange.map adjf adjf' eg ef E)) := by
    have h := αf'.naturality
      (X := ((Lg.obj K, Lg.obj (Rf.obj E)) : S' × S'))
      (Y := ((Lg.obj K, Rf'.obj (Lg'.obj E)) : S' × S'))
      (𝟙 (Lg.obj K) ×ₘ Stacks.CategoryTheory.BaseChange.map adjf adjf' eg ef E)
    simpa using h
  have h2 : Lf'.map (Lg.map (Stacks.Cohomology.AbstractKunnethMap.projectionMap A B adjf αf K E)) ≫
      (Stacks.AffineProjectionFormula.squareCompositeIso eg ef).hom.app
        (Rf.obj (B.obj (Lf.obj K, E))) =
      (Stacks.AffineProjectionFormula.squareCompositeIso eg ef).hom.app (A.obj (K, Rf.obj E)) ≫
        Lg'.map (Lf.map (Stacks.Cohomology.AbstractKunnethMap.projectionMap A B adjf αf K E)) := by
    have h := (Stacks.AffineProjectionFormula.squareCompositeIso eg ef).hom.naturality
      (Stacks.Cohomology.AbstractKunnethMap.projectionMap A B adjf αf K E)
    simpa using h
  have h3 : Lg'.map (B.map (𝟙 (Lf.obj K) ×ₘ adjf.counit.app E)) ≫ αg'.app (Lf.obj K, E) =
      αg'.app (Lf.obj K, Lf.obj (Rf.obj E)) ≫
        B'.map (𝟙 (Lg'.obj (Lf.obj K)) ×ₘ Lg'.map (adjf.counit.app E)) := by
    have h := αg'.naturality
      (X := ((Lf.obj K, Lf.obj (Rf.obj E)) : T × T))
      (Y := ((Lf.obj K, E) : T × T))
      (𝟙 (Lf.obj K) ×ₘ adjf.counit.app E)
    simpa using h
  refine (adjf'.homEquiv _ _).symm.injective ?_
  simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc,
    Stacks.Cohomology.AbstractKunnethMap.map_projectionMap_comp_counit,
    Adjunction.counit_naturality, Adjunction.counit_naturality_assoc,
    Stacks.AffineProjectionFormula.map_baseChangeMap_comp_counit_assoc]
  conv_lhs => rw [reassoc_of% h1, ← Functor.map_comp, prod_comp, Category.comp_id,
    Stacks.AffineProjectionFormula.map_baseChangeMap_comp_counit]
  conv_rhs => rw [reassoc_of% h2, ← Functor.map_comp_assoc,
    Stacks.Cohomology.AbstractKunnethMap.map_projectionMap_comp_counit, Functor.map_comp,
    Category.assoc, reassoc_of% h3, ← Functor.map_comp, prod_comp, Category.comp_id,
    ← reassoc_of% hsq, ← Functor.map_comp, prod_comp]
  simp

end Square

end Stacks.ProjectionFormula

namespace Stacks.EtaleCohomology.EtaleCoefficients

-- `derivedPullback` and `derivedPushforward`
-- (`StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.AdjunctionForRingedTopoi`),
-- through `pullback` and `pushforward`, are stated for the standard model of the derived
-- category.
attribute [local instance] HasDerivedCategory.standard

-- The imports bring `SheafOfModules.hasDerivedCategory`
-- (`StacksFrontier.Homology.DerivedCategory.LocallySmall`), the locally small model, which
-- would otherwise be found before `HasDerivedCategory.standard`.

attribute [local instance] Stacks.DerivedIndexing.commShiftRightDerivedFunctorPlus
attribute [local instance] Stacks.DerivedIndexing.isTriangulated_rightDerivedFunctorPlus

variable (m : ℕ)

/-- **A morphism of `D(X_étale, ℤ/m)` is an isomorphism as soon as its inverse images along a
jointly surjective family of morphisms are.** -/
theorem isIso_of_forall_isIso_pullback_map {X : Scheme.{u}} {ι : Type u} {V : ι → Scheme.{u}}
    (j : ∀ a, V a ⟶ X) (hj : ⋃ a, Set.range (j a).base = Set.univ)
    {K L : DerivedModules (ULift.{u + 1} (ZMod m)) X} (φ : K ⟶ L)
    (h : ∀ a, IsIso ((pullback (ULift.{u + 1} (ZMod m)) (j a)).map φ)) : IsIso φ := by
  rw [isIso_iff_isIso_forgetDerived_map, DerivedCategory.isIso_iff]
  intro n
  refine isIso_of_isIso_etaleAbelianInverseImage_family.{u, 0} j hj _ fun a => ?_
  have h₁ : IsIso ((forgetDerived (ULift.{u + 1} (ZMod m)) (V a)).map
      ((pullback (ULift.{u + 1} (ZMod m)) (j a)).map φ)) := inferInstance
  have h₂ : IsIso ((smallEtalePullbackAb (j a)).mapDerivedCategory.map
      ((forgetDerived (ULift.{u + 1} (ZMod m)) X).map φ)) :=
    (NatIso.isIso_map_iff (pullbackForgetIso m (j a)) φ).1 h₁
  exact (NatIso.isIso_map_iff (Adjunction.leftAdjointUniq (smallEtaleAdjunctionAb (j a))
    (etaleAbelianInverseImageDirectImageAdj.{u, 0} (j a))) _).1
    (((smallEtalePullbackAb (j a)).isIso_mapDerivedCategory_map_iff _).1 h₂ n)

/-- A morphism is invertible iff its image under a commuting square with invertible horizontal
sides is. -/
private theorem isIso_iff_of_comp_eq {C : Type*} [Category C] {P Q P' Q' : C} (f : P ⟶ Q)
    (f' : P' ⟶ Q') (l : P ⟶ P') (r : Q ⟶ Q') [IsIso l] [IsIso r] (e : l ≫ f' = f ≫ r) :
    IsIso f ↔ IsIso f' := by
  rw [← isIso_comp_left_iff l, e, isIso_comp_right_iff]

/-- **The projection map restricts to opens.** For a cartesian square `hV ≫ ι = ιY ≫ h` with
`ι` an open immersion, `E` bounded below and `h⁻¹A ⊗^L E` bounded below, the inverse image along
`ι` of the projection map of `h` at `(A, E)` is invertible exactly when the projection map of
`hV` at `(ι⁻¹A, ιY⁻¹E)` is: by `Stacks.ProjectionFormula.projectionMap_baseChange_square` they
differ by the comparisons of Tag 07A4 and the base change maps at `E` and at `h⁻¹A ⊗^L E`, which
are invertible (`isIso_baseChangeMap_app_of_isOpenImmersion`). -/
theorem isIso_pullback_map_projectionMap_iff {X' Y V VY : Scheme.{u}} (h : Y ⟶ X') (ι : V ⟶ X')
    [IsOpenImmersion ι] (hV : VY ⟶ V) (ιY : VY ⟶ Y) (sq : IsPullback hV ιY ι h)
    (A : DerivedModules (ULift.{u + 1} (ZMod m)) X') (E : DerivedModules (ULift.{u + 1} (ZMod m)) Y)
    (b c : ℤ) (hE : E.IsGE b)
    (hAE : (((tensor (ULift.{u + 1} (ZMod m)) Y).obj ((pullback _ h).obj A)).obj E).IsGE c) :
    IsIso ((pullback (ULift.{u + 1} (ZMod m)) ι).map (projectionMap _ h A E)) ↔
      IsIso (projectionMap (ULift.{u + 1} (ZMod m)) hV ((pullback _ ι).obj A)
        ((pullback _ ιY).obj E)) := by
  have key := Stacks.ProjectionFormula.projectionMap_baseChange_square
    (adjunction (ULift.{u + 1} (ZMod m)) h) (adjunction (ULift.{u + 1} (ZMod m)) hV)
    (pullbackCompIso _ hV ι ≪≫ eqToIso (congrArg (fun m => pullback _ m) sq.w))
    (pullbackCompIso _ ιY h)
    (Functor.uncurry.obj (tensor (ULift.{u + 1} (ZMod m)) X'))
    (Functor.uncurry.obj (tensor (ULift.{u + 1} (ZMod m)) V))
    (Functor.uncurry.obj (tensor (ULift.{u + 1} (ZMod m)) Y))
    (Functor.uncurry.obj (tensor (ULift.{u + 1} (ZMod m)) VY))
    (pullbackTensorIso _ h).hom (pullbackTensorIso _ hV).hom (pullbackTensorIso _ ι).hom
    (pullbackTensorIso _ ιY).hom A E
    (tensorComparisonCompatible_pullbackTensorIso _ hV ι ιY h sq.w A ((pushforward _ h).obj E))
  have hbc : ∀ (Z : DerivedModules (ULift.{u + 1} (ZMod m)) Y) (d : ℤ) (hZ : Z.IsGE d),
      IsIso (Stacks.CategoryTheory.BaseChange.map (adjunction (ULift.{u + 1} (ZMod m)) h)
        (adjunction (ULift.{u + 1} (ZMod m)) hV)
        (pullbackCompIso _ hV ι ≪≫ eqToIso (congrArg (fun m => pullback _ m) sq.w))
        (pullbackCompIso _ ιY h) Z) := by
    intro Z d hZ
    rw [baseChange_map_eq_baseChangeMap_app_left _ h ι ιY hV sq.w]
    let P : DerivedCategory.Plus (SheafOfModules.{u + 1} (Stacks.SheafOfModules.Tensor.ringSheaf
        (ringedTopos (ULift.{u + 1} (ZMod m)) Y).O)) := ⟨Z, d, hZ⟩
    exact (NatTrans.isIso_app_iff_of_iso (baseChangeMap _ ι h hV ιY sq.w)
      (X := DerivedCategory.Plus.ι.obj P) (Y := Z) (Iso.refl Z)).1
      (isIso_baseChangeMap_app_of_isOpenImmersion m ι h hV ιY sq P)
  have h₁ := hbc E b hE
  have h₂ := hbc ((Functor.uncurry.obj (tensor (ULift.{u + 1} (ZMod m)) Y)).obj
    ((pullback _ h).obj A, E)) c hAE
  have key' := (Category.assoc _ _ _).trans key
  have : IsIso (𝟙 ((pullback (ULift.{u + 1} (ZMod m)) ι).obj A) ×ₘ
      Stacks.CategoryTheory.BaseChange.map (adjunction (ULift.{u + 1} (ZMod m)) h)
        (adjunction (ULift.{u + 1} (ZMod m)) hV)
        (pullbackCompIso _ hV ι ≪≫ eqToIso (congrArg (fun m => pullback _ m) sq.w))
        (pullbackCompIso _ ιY h) E) :=
    (isIso_prod_iff (f := (𝟙 _ ×ₘ _))).2 ⟨inferInstance, h₁⟩
  have : IsIso ((Stacks.AffineProjectionFormula.squareCompositeIso
      (pullbackCompIso _ hV ι ≪≫ eqToIso (congrArg (fun m => pullback _ m) sq.w))
      (pullbackCompIso (ULift.{u + 1} (ZMod m)) ιY h)).inv.app A ×ₘ
        𝟙 ((pullback (ULift.{u + 1} (ZMod m)) ιY).obj E)) :=
    (isIso_prod_iff (f := (_ ×ₘ 𝟙 _))).2 ⟨inferInstance, inferInstance⟩
  exact isIso_iff_of_comp_eq _ _ _ _ key'

/-- The projection map is invertible at isomorphic second variables together. -/
theorem isIso_projectionMap_iff_of_iso_right {X' Y : Scheme.{u}} (h : Y ⟶ X')
    (A : DerivedModules (ULift.{u + 1} (ZMod m)) X')
    {B B' : DerivedModules (ULift.{u + 1} (ZMod m)) Y}
    (b : B ≅ B') :
    IsIso (projectionMap (ULift.{u + 1} (ZMod m)) h A B) ↔
      IsIso (projectionMap (ULift.{u + 1} (ZMod m)) h A B') := by
  have e := Stacks.Cohomology.AbstractKunnethMap.projectionMap_naturality
    (Functor.uncurry.obj (tensor (ULift.{u + 1} (ZMod m)) X'))
    (Functor.uncurry.obj (tensor (ULift.{u + 1} (ZMod m)) Y)) (adjunction _ h)
    (pullbackTensorIso _ h).hom (𝟙 A) b.hom
  have : IsIso (𝟙 A ×ₘ (pushforward (ULift.{u + 1} (ZMod m)) h).map b.hom) :=
    (isIso_prod_iff (f := (𝟙 _ ×ₘ _))).2 ⟨inferInstance, inferInstance⟩
  have : IsIso ((pullback (ULift.{u + 1} (ZMod m)) h).map (𝟙 A) ×ₘ b.hom) :=
    (isIso_prod_iff (f := (_ ×ₘ _))).2 ⟨inferInstance, inferInstance⟩
  exact isIso_iff_of_comp_eq _ _ _ _ e

open Stacks.EtaleCohomology.BaseChangeOverField in
/-- **The projection map of [Stacks, Tag 0F1J] at single sheaves of `𝔽_ℓ`-vector spaces, for an
arbitrary `X`.** In the setting of Tag 0F1J (`X' = X ×_S S'`, `Y = X' ×_{S'} T`, `g`
quasi-compact and quasi-separated), for every sheaf `ℰ` of `𝔽_ℓ̲`-modules on `X_étale` and every
sheaf `𝒢` of `𝔽_ℓ̲`-modules on `T_étale`, the projection map

`p⁻¹ℰ[-k] ⊗^L Rh_*(e⁻¹𝒢[-j]) ⟶ Rh_*(h⁻¹p⁻¹ℰ[-k] ⊗^L e⁻¹𝒢[-j])`

is invertible. "This question is local on `X` hence we may assume `X` is affine": invertibility
is checked after restriction to the opens `p⁻¹U` for `U ⊆ X` affine
(`isIso_of_forall_isIso_pullback_map`), there the projection map restricts to the one of the
diagram over `U` (`isIso_pullback_map_projectionMap_iff`), and over the affine `U` it is
`isIso_projectionMap_pullback_singleFunctor_of_compactSpace`.

Not registered: derived base change along every finite scheme over an affine open of `X`
(including the affine open itself) is the explicit argument `hBC`. -/
theorem isIso_projectionMap_pullback_singleFunctor_of_forall_isAffine (ℓ : ℕ) [Fact ℓ.Prime]
    {S X X' S' T Y : Scheme.{u}} (πX : X ⟶ S)
    (s : S' ⟶ S) (p : X' ⟶ X) (f' : X' ⟶ S') (hX' : IsPullback p f' πX s) (g : T ⟶ S')
    (h : Y ⟶ X') (e : Y ⟶ T) (hY : IsPullback h e f' g) [QuasiCompact g] [QuasiSeparated g]
    (hBC : ∀ {U Z : Scheme.{u}} (ιU : U ⟶ X) [IsOpenImmersion ιU] [IsAffine U] (π : Z ⟶ U)
      [IsFinite π], DerivedBaseChangeHolds (π ≫ ιU ≫ πX) ℓ)
    (M : SheafOfModules.{u + 1} (Stacks.SheafOfModules.Tensor.ringSheaf
      (ringedTopos (ULift.{u + 1} (ZMod ℓ)) X).O))
    (G : SheafOfModules.{u + 1} (Stacks.SheafOfModules.Tensor.ringSheaf
      (ringedTopos (ULift.{u + 1} (ZMod ℓ)) T).O)) (k j : ℤ) :
    IsIso (projectionMap (ULift.{u + 1} (ZMod ℓ)) h
      ((pullback (ULift.{u + 1} (ZMod ℓ)) p).obj ((DerivedCategory.singleFunctor _ k).obj M))
      ((pullback (ULift.{u + 1} (ZMod ℓ)) e).obj ((DerivedCategory.singleFunctor _ j).obj G))) := by
  refine isIso_of_forall_isIso_pullback_map ℓ (ι := X.affineOpens)
    (fun U => (p ⁻¹ᵁ U.1).ι) ?_ _ fun U => ?_
  · refine Set.eq_univ_of_forall fun x => ?_
    obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset (x := p x) (U := ⊤) trivial
    refine Set.mem_iUnion.2 ⟨⟨U, hU⟩, ?_⟩
    rw [Scheme.Opens.range_ι]
    exact hxU
  · obtain ⟨U, hU⟩ := U
    have : IsAffine U := hU
    have sqX : IsPullback (p ∣_ U) (p ⁻¹ᵁ U).ι U.ι p := isPullback_morphismRestrict p U
    have sq : IsPullback (h ∣_ (p ⁻¹ᵁ U)) (h ⁻¹ᵁ (p ⁻¹ᵁ U)).ι (p ⁻¹ᵁ U).ι h :=
      isPullback_morphismRestrict h (p ⁻¹ᵁ U)
    have hA : HasTorAmplitudeGE (ULift.{u + 1} (ZMod ℓ)) ((pullback _ h).obj
        ((pullback (ULift.{u + 1} (ZMod ℓ)) p).obj ((DerivedCategory.singleFunctor _ k).obj M)))
        k :=
      hasTorAmplitudeGE_pullback_obj _ h _ k (hasTorAmplitudeGE_pullback_obj _ p _ k
        (hasTorAmplitudeGE_singleFunctor_obj _ M (isFlat_of_fact_prime ℓ M) k))
    have hE : ((pullback (ULift.{u + 1} (ZMod ℓ)) e).obj
        ((DerivedCategory.singleFunctor _ j).obj G)).IsGE j :=
      isGE_pullback_obj _ e _ j inferInstance
    refine (isIso_pullback_map_projectionMap_iff ℓ h (p ⁻¹ᵁ U).ι (h ∣_ (p ⁻¹ᵁ U))
      (h ⁻¹ᵁ (p ⁻¹ᵁ U)).ι sq _ _ j (k + j) hE
      (isGE_tensor_obj_of_hasTorAmplitudeGE _ _ _ k j hA hE)).2 ?_
    refine (isIso_projectionMap_iff_of_iso _ _
      ((pullbackCompIso _ (p ⁻¹ᵁ U).ι p).app _ ≪≫
        (pullbackCongr _ sqX.w.symm).app _ ≪≫
        ((pullbackCompIso _ (p ∣_ U) U.ι).app _).symm ≪≫
        (pullback _ (p ∣_ U)).mapIso (pullbackObjSingleFunctorObjIso ℓ U.ι k M)) _).2 ?_
    refine (isIso_projectionMap_iff_of_iso_right ℓ _ _
      ((pullbackCompIso _ (h ⁻¹ᵁ (p ⁻¹ᵁ U)).ι e).app _)).2 ?_
    have hBCU : DerivedBaseChangeHolds (U.ι ≫ πX) ℓ := by
      have := hBC U.ι (𝟙 _)
      rwa [Category.id_comp] at this
    exact isIso_projectionMap_pullback_singleFunctor_of_compactSpace ℓ (U.ι ≫ πX) s (p ∣_ U)
      ((p ⁻¹ᵁ U).ι ≫ f') (sqX.paste_vert hX') g (h ∣_ (p ⁻¹ᵁ U))
      ((h ⁻¹ᵁ (p ⁻¹ᵁ U)).ι ≫ e) (sq.paste_vert hY) hBCU (fun π _ => hBC U.ι π) _ G k j

open Stacks.EtaleCohomology.BaseChangeOverField in
/-- **[Stacks, Tag 0F1J] for `n = ℓ` prime, from derived base change.** In the setting of
Tag 0F1J (`X' = X ×_S S'`, `Y = X' ×_{S'} T`, `g` quasi-compact and quasi-separated), the
canonical map

`p⁻¹E ⊗^L_{𝔽_ℓ} (f')⁻¹Rg_*F ⟶ Rh_*(h⁻¹p⁻¹E ⊗^L_{𝔽_ℓ} e⁻¹F)`

is invertible for `E ∈ D(X_étale, 𝔽_ℓ)` of Tor amplitude in `[a, ∞]` and `F ∈ D⁺(T_étale, 𝔽_ℓ)`.
The first two paragraphs of the source's proof reduce to a single flat sheaf `ℰ` and a single
sheaf `𝒢` (`isIso_tensorBaseChangeMap_of_isIso_single`); there the base change map is invertible
(`hBC`), and the projection map is
`isIso_projectionMap_pullback_singleFunctor_of_forall_isAffine`.

Not registered: derived base change along `X ⟶ S` (`hBC`) and along every finite scheme over an
affine open of `X`, the affine open itself included (`hBCaff`), are explicit arguments; for
`S = Spec K` with `ℓ` invertible in `K` they are the content of [Stacks, Tag 0F1I]. -/
theorem isIso_tensorBaseChangeMap_of_derivedBaseChangeHolds (ℓ : ℕ) [Fact ℓ.Prime]
    {S X X' S' T Y : Scheme.{u}} (πX : X ⟶ S)
    (s : S' ⟶ S) (p : X' ⟶ X) (f' : X' ⟶ S') (hX' : IsPullback p f' πX s) (g : T ⟶ S')
    (h : Y ⟶ X') (e : Y ⟶ T) (hY : IsPullback h e f' g) [QuasiCompact g] [QuasiSeparated g]
    (hBC : DerivedBaseChangeHolds πX ℓ)
    (hBCaff : ∀ {U Z : Scheme.{u}} (ιU : U ⟶ X) [IsOpenImmersion ιU] [IsAffine U] (π : Z ⟶ U)
      [IsFinite π], DerivedBaseChangeHolds (π ≫ ιU ≫ πX) ℓ)
    (E : DerivedModules (ULift.{u + 1} (ZMod ℓ)) X) (a : ℤ)
    (hE : HasTorAmplitudeGE (ULift.{u + 1} (ZMod ℓ)) E a)
    (F : DerivedModules (ULift.{u + 1} (ZMod ℓ)) T) (b : ℤ) (hF : F.IsGE b) :
    IsIso (tensorBaseChangeMap (ULift.{u + 1} (ZMod ℓ)) f' g h e hY.w
      ((pullback (ULift.{u + 1} (ZMod ℓ)) p).obj E) F) :=
  isIso_tensorBaseChangeMap_of_isIso_single _ p f' g h e hY.w
    (fun M _ G i j => (isIso_tensorBaseChangeMap_iff_isIso_projectionMap _ f' g h e hY.w _ _
      (isIso_baseChangeMap_app_singleFunctor_of_derivedBaseChangeHolds ℓ πX hBC s p f' hX' g h e
        hY G j)).2
      (isIso_projectionMap_pullback_singleFunctor_of_forall_isAffine ℓ πX s p f' hX' g h e hY
        hBCaff M G i j))
    E a hE F b hF

end Stacks.EtaleCohomology.EtaleCoefficients

end
