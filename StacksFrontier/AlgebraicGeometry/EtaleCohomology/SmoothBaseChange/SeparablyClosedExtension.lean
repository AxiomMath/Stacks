module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmoothBaseChange.AffineEtaleDetection
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmoothBaseChange.DerivedBaseChangeUnit
public import
StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmoothBaseChange.SepClosedFieldPullbackEquivalence
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmoothBaseChange.FieldExtensionBaseChange

/-!
# Étale cohomology is invariant under extension of separably closed base field

Let `K/k` be an extension of separably closed fields, let `X` be a scheme over `k` with
`X_K = X ×_k Spec K` and projection `p : X_K ⟶ X`, and let `E ∈ D⁺(X_étale)` have cohomology
sheaves whose stalks are torsion of orders invertible in `k`. [Stacks, Tag 0F0B] asserts, for
`X` quasi-compact and quasi-separated, that

1. the maps `H^q_ét(X, E) ⟶ H^q_ét(X_K, E|_{X_K})` are isomorphisms, and
2. `E ⟶ Rp_*(E|_{X_K})` is an isomorphism.

The results here take the smooth base change theorem in the form of [Stacks, Tag 0F09], the
proposition `Stacks.EtaleCohomology.SmoothLimitBaseChange`, as the argument `hSmoothLimit`.

## Main results

* `Stacks.EtaleCohomology.bijective_smallEtalePullbackAb_map_of_isSepClosed` — for `X`
  quasi-compact and quasi-separated over `k` and every `M ∈ D⁺((Spec k)_étale)`, pullback along
  `p` is bijective on `Hom(f⁻¹M, E)`.
* `Stacks.EtaleCohomology.bijective_etaleCohomology_restriction_of_isSepClosed` — **part (1)**:
  restriction `H^q(X, E) ⟶ H^q(X_K, E|_{X_K})` is bijective, `H^q(X, E)` being the group of
  morphisms in `D⁺(X_étale)` out of the constant sheaf `ℤ` placed in degree `-q`.
* `Stacks.EtaleCohomology.isIso_derivedUnit_app_of_isSepClosed` — **part (2)**: the unit
  `E ⟶ Rp_*p⁻¹E` of the derived adjunction is an isomorphism, for every scheme `X` over `k`.

## References

* [Stacks Project, Tag 0F0B](https://stacks.math.columbia.edu/tag/0F0B)
* [Stacks Project, Tag 0F09](https://stacks.math.columbia.edu/tag/0F09)
* [Stacks Project, Tag 0F1C](https://stacks.math.columbia.edu/tag/0F1C)
* [Stacks Project, Tag 0EYU](https://stacks.math.columbia.edu/tag/0EYU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

/-- A natural number which is a unit in a field is prime to its exponential characteristic. -/
theorem coprime_ringExpChar_of_isUnit {k : Type*} [Field k] {n : ℕ} (hn : IsUnit (n : k)) :
    n.Coprime (ringExpChar k) := by
  rcases CharP.char_is_prime_or_zero k (ringChar k) with hp | hp
  · rw [ringExpChar, max_eq_left hp.one_le]
    exact (hp.coprime_iff_not_dvd.mpr ((CharP.isUnit_natCast_iff hp).mp hn)).symm
  · rw [ringExpChar, hp]
    exact Nat.coprime_one_right n

/-- An abelian sheaf with torsion of orders invertible on `Spec k` is torsion prime to the
exponential characteristic of `k`. -/
theorem isPrimeToCharacteristicTorsion_of_hasTorsionOrdersInvertibleOn {k : Type u} [Field k]
    {X : Scheme.{u}} {F : Sheaf (smallEtaleTopology X) Ab.{u + 1}}
    (hF : HasTorsionOrdersInvertibleOn (Spec (.of k)) F) :
    Stacks.Torsion.IsPrimeToCharacteristicTorsion (smallEtaleTopology X) (ringExpChar k) F := by
  rw [isPrimeToCharacteristicTorsion_iff_locallyAnnihilated]
  intro U x
  obtain ⟨R, hR, h⟩ := hF U x
  refine ⟨R, hR, fun V f hf ↦ ?_⟩
  obtain ⟨n, ⟨hn, hu⟩, hx⟩ := h V f hf
  refine ⟨n, ⟨hn, coprime_ringExpChar_of_isUnit ?_⟩, hx⟩
  simpa only [map_natCast] using hu.map (Scheme.ΓSpecIso (CommRingCat.of k)).hom.hom

/-- **Pullback to `X_K` is bijective on morphisms out of a pullback from `Spec k`.** For `K/k` an
extension of separably closed fields, `X` quasi-compact and quasi-separated over `k`, `E` in
`D⁺(X_étale)` with torsion cohomology of orders invertible in `k` and `M` in `D⁺((Spec k)_étale)`,
pullback along `p : X_K ⟶ X` is bijective on `Hom(f⁻¹M, E)`. Conditional on Tag 0F09. -/
theorem bijective_smallEtalePullbackAb_map_of_isSepClosed
    (hSmoothLimit : SmoothLimitBaseChange.{u})
    {k K : Type u} [Field k] [Field K] [Algebra k K] [IsSepClosed k] [IsSepClosed K]
    {X XK : Scheme.{u}} (f : X ⟶ Spec (.of k)) [QuasiCompact f] [QuasiSeparated f]
    (p : XK ⟶ X) (fK : XK ⟶ Spec (.of K))
    (sq : IsPullback p fK f (Spec.map (CommRingCat.ofHom (algebraMap k K))))
    (E : DerivedCategory.Plus (Sheaf (smallEtaleTopology X) Ab.{u + 1}))
    (hE : ∀ q : ℤ, HasTorsionOrdersInvertibleOn (Spec (.of k))
      ((DerivedCategory.Plus.homologyFunctor (Sheaf (smallEtaleTopology X) Ab.{u + 1}) q).obj E))
    (M : DerivedCategory.Plus (Sheaf (smallEtaleTopology (Spec (.of k))) Ab.{u + 1})) :
    Function.Bijective (fun φ : (smallEtalePullbackAb f).rightDerivedFunctorPlus.obj M ⟶ E ↦
      (smallEtalePullbackAb p).rightDerivedFunctorPlus.map φ) := by
  have hβ := FieldExtensionBaseChange.isIso_of_isPullback k K (𝟙 _) f f (Category.comp_id f)
    hSmoothLimit (IsPullback.id_horiz _) sq.flip fK (Category.comp_id fK) sq.flip.w E
    (fun q ↦ isPrimeToCharacteristicTorsion_of_hasTorsionOrdersInvertibleOn (hE q))
  exact bijective_smallEtaleDerivedPullback_map_of_isIso _ f fK p sq.flip.w M E hβ
    (bijective_smallEtalePullbackAb_rightDerivedFunctorPlus_map_of_isSepClosed _ M _)

/-- Bijectivity of a functor on morphisms out of `A'` gives it on morphisms out of `A ≅ A'`. -/
theorem bijective_map_of_iso_left {𝒞 𝒟 : Type*} [Category* 𝒞] [Category* 𝒟] (G : 𝒞 ⥤ 𝒟)
    {A A' B : 𝒞} (ι : A ≅ A') (h : Function.Bijective (fun y : A' ⟶ B ↦ G.map y)) :
    Function.Bijective (fun y : A ⟶ B ↦ G.map y) := by
  have e : (fun y : A ⟶ B ↦ G.map y) =
      (G.mapIso ι).symm.homFromEquiv ∘ (fun y : A' ⟶ B ↦ G.map y) ∘ ι.homFromEquiv := by
    funext y
    simp [Iso.homFromEquiv]
  rw [e]
  exact (Equiv.bijective _).comp (h.comp (Equiv.bijective _))

/-- If `v ≫ β` is the unit followed by `R(θ)`, then precomposing `v ≫ β` with `y` is the
transpose of `L(y) ≫ θ`. -/
theorem comp_comp_eq_homEquiv {𝒞 𝒟 : Type*} [Category* 𝒞] [Category* 𝒟] {L : 𝒞 ⥤ 𝒟}
    {R : 𝒟 ⥤ 𝒞} (adj : L ⊣ R) {A B B' : 𝒞} {C : 𝒟} (v : B ⟶ B') (β : B' ⟶ R.obj C)
    (θ : L.obj B ⟶ C) (h : v ≫ β = adj.unit.app B ≫ R.map θ) (y : A ⟶ B) :
    y ≫ v ≫ β = adj.homEquiv _ _ (L.map y ≫ θ) := by
  rw [h, Adjunction.homEquiv_unit, Functor.map_comp, ← Category.assoc, ← adj.unit_naturality,
    Category.assoc]

/-- If `v ≫ β` is the unit followed by `R(θ)` with `β`, `θ` isomorphisms, then bijectivity of
`L` on morphisms `A ⟶ B` gives bijectivity of postcomposition with `v`. -/
private theorem bijective_comp_of_comp_eq_unit_comp {𝒞 𝒟 : Type*} [Category* 𝒞] [Category* 𝒟]
    {L : 𝒞 ⥤ 𝒟} {R : 𝒟 ⥤ 𝒞} (adj : L ⊣ R) {A B B' : 𝒞} {C : 𝒟} (v : B ⟶ B')
    (β : B' ⟶ R.obj C) [IsIso β] (θ : L.obj B ⟶ C) [IsIso θ]
    (h : v ≫ β = adj.unit.app B ≫ R.map θ)
    (hL : Function.Bijective (fun y : A ⟶ B ↦ L.map y)) :
    Function.Bijective (fun y : A ⟶ B ↦ y ≫ v) := by
  have key : (fun y ↦ y ≫ β) ∘ (fun y : A ⟶ B ↦ y ≫ v) =
      adj.homEquiv _ _ ∘ (fun z ↦ z ≫ θ) ∘ (fun y : A ⟶ B ↦ L.map y) := by
    funext y
    simp only [Function.comp_apply, Category.assoc]
    exact comp_comp_eq_homEquiv adj v β θ h y
  have hb : Function.Bijective ((fun y ↦ y ≫ β) ∘ (fun y : A ⟶ B ↦ y ≫ v)) := by
    rw [key]
    exact (Equiv.bijective _).comp ((asIso θ).homToEquiv.bijective.comp hL)
  exact (Function.Bijective.of_comp_iff' (asIso β).homToEquiv.bijective _).1 hb

/-- **Base change along an étale morphism, from Tag 0F09.** For `j : U ⟶ X` étale, `p : X_K ⟶ X`
quasi-compact and quasi-separated and `E` in `D⁺(X_K)` torsion prime to the exponential
characteristic of `k` (`X` being over `k`), the base change map `j⁻¹Rp_*E ⟶ Rp_{U,*}(E|_{U_K})` is
an isomorphism. -/
theorem isIso_derivedBaseChange_of_etale (hSmoothLimit : SmoothLimitBaseChange.{u})
    {k : Type u} [Field k] {X XK U UK : Scheme.{u}} (f : X ⟶ Spec (.of k)) (p : XK ⟶ X)
    [QuasiCompact p] [QuasiSeparated p] (j : U ⟶ X) [Etale j] (πU : UK ⟶ U) (jK : UK ⟶ XK)
    (sqU : IsPullback πU jK j p)
    (E : DerivedCategory.Plus (Sheaf (smallEtaleTopology XK) Ab.{u + 1}))
    (hE : ∀ q : ℤ, Stacks.Torsion.IsPrimeToCharacteristicTorsion (smallEtaleTopology XK)
      (ringExpChar k) ((DerivedCategory.Plus.homologyFunctor _ q).obj E)) :
    IsIso ((smallEtaleDerivedBaseChangeAb j p πU jK sqU.w).app E) := by
  let c : Cone ((Functor.const PUnit.{u + 1}ᵒᵖ).obj U) :=
    { pt := U
      π := 𝟙 _ }
  have hc : IsLimit c :=
    { lift := fun s ↦ s.π.app (op PUnit.unit)
      fac := fun s i ↦ by simp [c]
      uniq := fun s m hm ↦ by simpa [c] using hm (op PUnit.unit) }
  exact hSmoothLimit PUnit.{u + 1} X ((Functor.const _).obj U) ((Functor.const _).map j)
    (fun _ ↦ inferInstanceAs (Smooth j)) (fun _ _ _ ↦ inferInstanceAs (IsAffineHom (𝟙 U))) c hc j
    (fun _ ↦ Category.id_comp j) XK UK p πU jK sqU E
    (fun q ↦ FieldExtensionBaseChange.hasTorsionOrdersInvertibleOn_of_isPrimeToCharacteristicTorsion
      f (hE q))

/-- The derived inverse image of the constant sheaf `ℤ` placed in degree `n` is the constant sheaf
`ℤ` placed in degree `n`. -/
def singleConstantZPullbackIso {Y X : Scheme.{u}} (g : Y ⟶ X) (n : ℤ) :
    (DerivedCategory.Plus.singleFunctor _ n).obj (constantZ Y) ≅
      (smallEtalePullbackAb g).rightDerivedFunctorPlus.obj
        ((DerivedCategory.Plus.singleFunctor _ n).obj (constantZ X)) :=
  (DerivedCategory.Plus.singleFunctor _ n).mapIso
      ((FirstFailureFunctionField.smallEtalePullbackAbConstantIso g).app _).symm ≪≫
    (Stacks.DerivedFunctor.exactSingleFunctorRightDerivedPlusIso (smallEtalePullbackAb g) n).app _

/-- Under the hypotheses of Tag 0F0B, pullback along `p` is bijective on morphisms out of the
constant sheaf `ℤ` placed in degree `n`. -/
private theorem bijective_map_single_constantZ_of_isSepClosed
    (hSmoothLimit : SmoothLimitBaseChange.{u})
    {k K : Type u} [Field k] [Field K] [Algebra k K] [IsSepClosed k] [IsSepClosed K]
    {X XK : Scheme.{u}} (f : X ⟶ Spec (.of k)) [QuasiCompact f] [QuasiSeparated f]
    (p : XK ⟶ X) (fK : XK ⟶ Spec (.of K))
    (sq : IsPullback p fK f (Spec.map (CommRingCat.ofHom (algebraMap k K))))
    (E : DerivedCategory.Plus (Sheaf (smallEtaleTopology X) Ab.{u + 1}))
    (hE : ∀ q : ℤ, HasTorsionOrdersInvertibleOn (Spec (.of k))
      ((DerivedCategory.Plus.homologyFunctor (Sheaf (smallEtaleTopology X) Ab.{u + 1}) q).obj E))
    (n : ℤ) :
    Function.Bijective
      (fun φ : (DerivedCategory.Plus.singleFunctor _ n).obj (constantZ X) ⟶ E ↦
        (smallEtalePullbackAb p).rightDerivedFunctorPlus.map φ) :=
  bijective_map_of_iso_left _ (singleConstantZPullbackIso f n)
    (bijective_smallEtalePullbackAb_map_of_isSepClosed hSmoothLimit f p fK sq E hE _)

/-- **[Stacks, Tag 0F0B] part (2), conditional on Tag 0F09.** For `K/k` an extension of separably
closed fields, `X` any scheme over `k`, `p : X_K ⟶ X` the base change and `E` in `D⁺(X_étale)`
whose cohomology sheaves have stalks which are torsion of orders invertible in `k`, the unit
`E ⟶ Rp_*p⁻¹E` of the derived adjunction is an isomorphism. -/
theorem isIso_derivedUnit_app_of_isSepClosed (hSmoothLimit : SmoothLimitBaseChange.{u})
    {k K : Type u} [Field k] [Field K] [Algebra k K] [IsSepClosed k] [IsSepClosed K]
    {X XK : Scheme.{u}} (f : X ⟶ Spec (.of k)) (p : XK ⟶ X) (fK : XK ⟶ Spec (.of K))
    (sq : IsPullback p fK f (Spec.map (CommRingCat.ofHom (algebraMap k K))))
    (E : DerivedCategory.Plus (Sheaf (smallEtaleTopology X) Ab.{u + 1}))
    (hE : ∀ q : ℤ, HasTorsionOrdersInvertibleOn (Spec (.of k))
      ((DerivedCategory.Plus.homologyFunctor (Sheaf (smallEtaleTopology X) Ab.{u + 1}) q).obj E)) :
    IsIso ((smallEtaleAdjunctionAb p).rightDerivedFunctorPlus.unit.app E) := by
  have : IsAffineHom p := MorphismProperty.of_isPullback sq.flip inferInstance
  have hE' := fun q ↦ isPrimeToCharacteristicTorsion_of_hasTorsionOrdersInvertibleOn (hE q)
  apply isIso_of_forall_isAffine_bijective
  intro U hU n
  have := hU
  let j := U.hom
  have sqU := IsPullback.of_hasPullback j p
  let πU := pullback.fst j p
  let jK := pullback.snd j p
  let u := (smallEtaleAdjunctionAb p).rightDerivedFunctorPlus.unit.app E
  let G := (smallEtalePullbackAb j).rightDerivedFunctorPlus
  let adjU := (smallEtaleAdjunctionAb πU).rightDerivedFunctorPlus
  let θ := (smallEtaleDerivedPullbackSquareIso j p πU jK sqU.w).hom.app E
  let β := (smallEtaleDerivedBaseChangeAb j p πU jK sqU.w).app
    ((smallEtalePullbackAb p).rightDerivedFunctorPlus.obj E)
  have hβ : IsIso β := isIso_derivedBaseChange_of_etale hSmoothLimit f p j πU jK sqU _
    (fun q ↦ FieldExtensionBaseChange.isPrimeToCharacteristicTorsion_homology_derivedPullback p
      E q (hE' q))
  have hfU : IsAffineHom (j ≫ f) := @isAffineHom_of_isAffine _ _ (j ≫ f) hU inferInstance
  have h1' := bijective_map_single_constantZ_of_isSepClosed hSmoothLimit (j ≫ f) πU (jK ≫ fK)
    (sqU.paste_vert sq) (G.obj E)
    (fun q ↦ FieldExtensionBaseChange.hasTorsionOrdersInvertibleOn_of_isPrimeToCharacteristicTorsion
      (𝟙 _) (FieldExtensionBaseChange.isPrimeToCharacteristicTorsion_homology_derivedPullback j
        E q (hE' q))) n
  exact bijective_comp_of_comp_eq_unit_comp adjU (G.map u) β θ
    (map_derivedUnit_comp_smallEtaleDerivedBaseChangeAb_app j p πU jK sqU.w E) h1'

/-- **[Stacks, Tag 0F0B] part (1), conditional on Tag 0F09.** For `K/k` an extension of separably
closed fields, `X` quasi-compact and quasi-separated over `k`, `p : X_K ⟶ X` the base change and
`E` in `D⁺(X_étale)` whose cohomology sheaves have stalks which are torsion of orders invertible in
`k`, restriction `H^q_ét(X, E) ⟶ H^q_ét(X_K, E|_{X_K})` is bijective for every `q`. Here
`H^q_ét(X, E)` is the group of morphisms in `D⁺(X_étale)` out of the constant sheaf `ℤ` placed in
degree `-q`, and restriction is pullback along `p` followed by the identification of the
pullback of `ℤ_X` with `ℤ_{X_K}`. -/
theorem bijective_etaleCohomology_restriction_of_isSepClosed
    (hSmoothLimit : SmoothLimitBaseChange.{u})
    {k K : Type u} [Field k] [Field K] [Algebra k K] [IsSepClosed k] [IsSepClosed K]
    {X XK : Scheme.{u}} (f : X ⟶ Spec (.of k)) [QuasiCompact f] [QuasiSeparated f]
    (p : XK ⟶ X) (fK : XK ⟶ Spec (.of K))
    (sq : IsPullback p fK f (Spec.map (CommRingCat.ofHom (algebraMap k K))))
    (E : DerivedCategory.Plus (Sheaf (smallEtaleTopology X) Ab.{u + 1}))
    (hE : ∀ q : ℤ, HasTorsionOrdersInvertibleOn (Spec (.of k))
      ((DerivedCategory.Plus.homologyFunctor (Sheaf (smallEtaleTopology X) Ab.{u + 1}) q).obj E))
    (q : ℤ) :
    Function.Bijective
      (fun φ : (DerivedCategory.Plus.singleFunctor _ (-q)).obj (constantZ X) ⟶ E ↦
        (singleConstantZPullbackIso p (-q)).hom ≫
          (smallEtalePullbackAb p).rightDerivedFunctorPlus.map φ) := by
  have h1' := bijective_map_single_constantZ_of_isSepClosed hSmoothLimit f p fK sq E hE (-q)
  exact ((singleConstantZPullbackIso p (-q)).symm.homFromEquiv).bijective.comp h1'

end Stacks.EtaleCohomology
