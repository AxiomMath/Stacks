module

public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.CrystalOfStratification
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.CrystalPairConnection07J6
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.CrystalPairFunctor07JG
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.StratifiedCrystalRestriction
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.StratifiedCrystalSections
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.WholeSpaceTaylorData

/-!
# Crystals in quasi-coherent modules are pairs: [Stacks, Proposition 60.17.4, Tag 07JH]

In the situation of [Stacks, Section 60.17, Tag 07J7] (`X = Spec(C)`, `S = Spec(A)` affine, `p`
nilpotent on `C`, any surjective polynomial presentation `P = A[x_i : i ∈ ι] → C` — the instance
`...SmallSite.WholeSpacePresentation S hp`, by default `A[x_c : c ∈ C] → C` — `D` the `p`-adically
completed divided power envelope with its completed divided power differentials `Ω_D`), the
functor of
[Stacks, Lemma 60.17.3, Tag 07JG], `...SmallSite.crystalPairFunctor`, from crystals in
quasi-coherent `𝒪_{X/S}`-modules on `Cris(X/S)` to pairs `(M, ∇)` satisfying (07JB)–(07JE), is
an equivalence of categories.

The proof follows the source.  A pair `(M, ∇)` has Taylor operators `θ_K` (the composites of
minus the coordinates of `∇`), and its Taylor stratification
`c(m) = ∑_K ξ^{[K]} ⊗ θ_K(m)` over the levels `T(1)_e` of the system of [Stacks, Tag 07JN] is a
stratification in the sense of descent along that system (unital, a cocycle, compatible with the
levels).  Descending it gives a crystal in quasi-coherent modules whose limit module is `M`; this
is the quasi-inverse `...SmallSite.pairCrystalFunctor`.

* The counit: a crystal is the crystal of the Taylor stratification of its pair, because its own
  Taylor expansion over `T(1)_e` has the operators of its pair as coefficients.
* Fully faithful: a horizontal map of pairs commutes with the Taylor operators, hence with the
  stratifications, and so descends to a morphism of crystals.
* Essentially surjective: the Taylor operators of the crystal of a pair are the pair's (by
  uniqueness of the coefficients of a Taylor expansion), so the identification of its limit
  module with `M` is horizontal.

## Main results

* `...SmallSite.crystalPairFunctor_isEquivalence` — **[Stacks, Tag 07JH]**: the functor of
  [Stacks, Tag 07JG] is an equivalence of categories.
* `...SmallSite.pairCrystalFunctor` — the quasi-inverse, from pairs to crystals.
* `...SmallSite.crystalPairCounitIso` — a crystal is the crystal of its pair.

## References

* [Stacks Project, Proposition 60.17.4, Tag 07JH](https://stacks.math.columbia.edu/tag/07JH)
* [Stacks Project, Lemma 60.17.3, Tag 07JG](https://stacks.math.columbia.edu/tag/07JG)
-/

@[expose] public section

open CategoryTheory Opposite AlgebraicGeometry Simplicial
open scoped TensorProduct

universe u

namespace Crystalline.GlobalCrystallineSituation.SmallSite

open Crystalline Crystalline.StratifiedDescent

variable {S : GlobalCrystallineSituation.{u}} [IsAffine S.X] [IsAffine S.S.scheme]
  (hp : IsNilpotent (S.p : Γ(S.X, ⊤))) [WholeSpacePresentation S hp]

/-! ### The Taylor operators of the pair of a crystal are the crystal's -/

section CrystalSide

variable (Fc : QuasiCoherentCrystal S)

/-- The Taylor operators of a pair are the operators whose negatives are the coordinates of its
connection, given a dual family of coordinate functionals. -/
private theorem taylorTheta_eq_of_isCoordinateExpansion {p : ℕ} {D : Type*} [CommRing D]
    {Omega : Type*} [AddCommGroup Omega] [Module D Omega] {ι : Type*} {dx : ι → Omega}
    {dd : D → Omega} {coord : ι → (Omega →ₗ[D] D)} (P : Pair p D Omega dx dd)
    (hc : IsCoordinateDual dx coord) {θ : ι → P.carrier → P.carrier}
    (hθ : IsCoordinateExpansion p D Omega dx P.nabla fun c m ↦ -θ c m) (c : ι) (m : P.carrier) :
    P.taylorTheta c m = θ c m :=
  (congrArg Neg.neg (congrFun (congrFun (eq_of_isCoordinateExpansion_of_isCoordinateDual p D Omega
    P.carrier P.hasCoordinateOperators.choose_spec hθ hc
    P.isPAdicallyComplete.toIsHausdorff) c) m)).trans (neg_neg _)

/-- The composite Taylor operators of a pair are any family of composites of operators equal to
its Taylor operators. -/
private theorem taylorThetaPow_eq_of_isThetaMonomialFamily {p : ℕ} {D : Type*} [CommRing D]
    {Omega : Type*} [AddCommGroup Omega] [Module D Omega] {ι : Type*} {dx : ι → Omega}
    {dd : D → Omega} {coord : ι → (Omega →ₗ[D] D)} (P : Pair p D Omega dx dd)
    (hc : IsCoordinateDual dx coord) {θ : ι → P.carrier → P.carrier}
    {θK : (ι →₀ ℕ) → P.carrier → P.carrier} (hθK : IsThetaMonomialFamily P.carrier θ θK)
    (h : ∀ c m, P.taylorTheta c m = θ c m) (K : ι →₀ ℕ) (m : P.carrier) :
    P.taylorThetaPow hc K m = θK K m := by
  rw [show θ = P.taylorTheta from funext fun c ↦ funext fun m ↦ (h c m).symm] at hθK
  exact congrFun (congrFun (IsThetaMonomialFamily.unique
    (P.isThetaMonomialFamily_taylorThetaPow hc) hθK) K) m

/-- **The Taylor operators of the pair of a crystal are the operators `θ_c` of the crystal's
Taylor expansion**: both are minus the coordinates of the connection. -/
theorem taylorTheta_crystalPair (c : wholeSpaceIndex S hp)
    (m : wholeSpaceSections hp Fc ⦋0⦌) :
    ((crystalPairFunctor hp).obj Fc).taylorTheta c m =
      crystalTheta hp Fc (Finsupp.single c 1) m :=
  taylorTheta_eq_of_isCoordinateExpansion ((crystalPairFunctor hp).obj Fc)
    (isCoordinateDual_pairDx hp)
    (isCoordinateExpansion_pairConnection hp Fc) c m

/-- The crystal's operators form a family of composites of its first-order operators. -/
theorem isThetaMonomialFamily_crystalTheta :
    IsThetaMonomialFamily (wholeSpaceSections hp Fc ⦋0⦌)
      (fun c ↦ crystalTheta hp Fc (Finsupp.single c 1)) (fun K ↦ crystalTheta hp Fc K) := by
  refine ⟨funext fun m ↦ crystalTheta_zero hp Fc m, fun c K ↦ funext fun m ↦ ?_⟩
  exact (crystalTheta_crystalTheta hp Fc K _ m).symm

/-- **The composite Taylor operators of the pair of a crystal are the crystal's `θ_K`.** -/
theorem taylorThetaPow_crystalPair (K : wholeSpaceIndex S hp →₀ ℕ)
    (m : wholeSpaceSections hp Fc ⦋0⦌) :
    ((crystalPairFunctor hp).obj Fc).taylorThetaPow (isCoordinateDual_pairDx hp) K m =
      crystalTheta hp Fc K m :=
  taylorThetaPow_eq_of_isThetaMonomialFamily ((crystalPairFunctor hp).obj Fc)
    (isCoordinateDual_pairDx hp) (isThetaMonomialFamily_crystalTheta hp Fc)
    (taylorTheta_crystalPair hp Fc) K m

end CrystalSide

/-! ### The pairs over the completed envelope of the system -/

section PairE

/-- The forms `Ω_D` as a module over `D` read as the completed envelope of the system; the two
rings are the same. -/
noncomputable instance instModuleEnvDPairForms : Module (envD S hp) (pairForms hp) :=
  inferInstanceAs (Module (pairRing hp) (pairForms hp))

/-- The derivation `d : D → Ω_D`, with `D` read as the completed envelope of the system. -/
noncomputable def pairDD : envD S hp → pairForms hp := fun x ↦ pairDerivation hp x

/-- The coordinate functionals of `Ω_D`, with `D` read as the completed envelope of the system. -/
noncomputable def pairCoordE (c : wholeSpaceIndex S hp) :
    pairForms hp →ₗ[envD S hp] envD S hp where
  toFun := pairCoord hp c
  map_add' := (pairCoord hp c).map_add
  map_smul' := (pairCoord hp c).map_smul

omit [IsAffine S.X] [IsAffine S.S.scheme] in
/-- The coordinates `pairCoordE` are dual to the differentials `d x_c`. -/
theorem isCoordinateDual_pairCoordE : IsCoordinateDual (pairDx hp) (pairCoordE hp) where
  self := (isCoordinateDual_pairDx hp).self
  of_ne := (isCoordinateDual_pairDx hp).of_ne

/-- **The category of pairs `(M, ∇)` over the completed envelope of the system**, which is the
target category of `crystalPairFunctor` read over the same ring under its other name. -/
abbrev PairE := Pair.{u, u, u, u} S.p (envD S hp) (pairForms hp) (pairDx hp) (pairDD hp)

/-- The target category of `crystalPairFunctor`. -/
abbrev PairCat :=
  Pair.{u, u, u, u} S.p (pairRing hp) (pairForms hp) (pairDx hp)
    (derivationFun ((affineSituation S hp).A : Type u) (pairRing hp) _ (pairForms hp)
      (pairDerivation hp))

/-- Reading a pair over `D` as a pair over the completed envelope of the system. -/
noncomputable def toPairE : PairCat hp ⥤ PairE hp where
  obj P := P
  map f := f

/-- Reading a pair over the completed envelope of the system as a pair over `D`. -/
noncomputable def ofPairE : PairE hp ⥤ PairCat hp where
  obj P := P
  map f := f

/-- The two readings are inverse equivalences, both being the identity. -/
noncomputable def pairEEquivalence : PairCat hp ≌ PairE hp :=
  CategoryTheory.Equivalence.mk (toPairE hp) (ofPairE hp) (Iso.refl _) (Iso.refl _)

/-- Reading a pair over the completed envelope of the system is an equivalence. -/
instance : (toPairE hp).IsEquivalence :=
  inferInstanceAs (pairEEquivalence hp).functor.IsEquivalence

end PairE

/-! ### The quasi-inverse functor -/

section QuasiInverse

open scoped Classical in
/-- The Taylor stratification of a pair, as a functor to stratified modules. -/
noncomputable def pairStratFunctorE : PairE hp ⥤ StratModule S hp :=
  pairStratFunctor (wholeSpaceTaylorData S hp) (isCoordinateDual_pairCoordE hp)
    (isThetaMonomialFamily_wholeSpaceTaylorData_delta S hp)
    (fun c f ↦ pairCoord_pairDerivation S hp c f)

/-- **The quasi-inverse of the functor of [Stacks, Tag 07JG]**: a pair `(M, ∇)` goes to the
crystal descended from its Taylor stratification `m ↦ ∑_K ξ^{[K]} ⊗ θ_K(m)`. -/
noncomputable def pairCrystalFunctor : PairE hp ⥤ QuasiCoherentCrystal S :=
  pairStratFunctorE hp ⋙ stratCrystalFunctor

end QuasiInverse

/-! ### The isomorphism of a crystal with the crystal of its stratification, on limit modules -/

section General

variable {Fc : QuasiCoherentCrystal S}
  {E : Stratification (wholeSpaceDescentSystem S hp) (wholeSpaceSections hp Fc ⦋0⦌)}
  (hE : ∀ e m, crystalPointMap hp Fc ((wholeSpaceDescentSystem S hp).v e 0).hom (E.str e m) =
    crysRestrict Fc.obj ((wholeSpaceDescentSystem S hp).v e 1).hom
      (wholeSpaceSectionsVal hp Fc m e))
  (hM : IsPAdicallyComplete S.p (envD S hp) (wholeSpaceSections hp Fc ⦋0⦌))

include hE in
/-- **On the limit modules, the isomorphism of a crystal with the crystal of its stratification is
the identification `...SmallSite.stratLimitEquiv`**: the section of `m` goes to `m`. -/
theorem sectionsMap_stratCrystalIso_hom (m : wholeSpaceSections hp Fc ⦋0⦌) :
    (wholeSpaceLevelScalars hp 0).sectionsMap (stratCrystalIso Fc E hE).hom
      ((stratLimitEquiv E hM).symm m) = m := by
  refine wholeSpaceSectionsVal_injective hp Fc fun e ↦ ?_
  have h := stratCrystalIso_hom_app (F := Fc) (E := E) hE (affineLevel S hp 0 e) (𝟙 _)
    (stratLevelMap E e m)
  have h2 := evalEquiv_stratLevelSec_stratLevelMap E e m
  refine (h.trans (congrArg (crystalPointMap hp Fc _) h2)).trans ?_
  exact (one_smul _ _).trans (crysRestrict_id Fc.obj _ _)

end General

/-! ### A crystal is the crystal of its pair -/

section Counit

variable (Fc : QuasiCoherentCrystal S)

/-- The pair of a crystal, read over the completed envelope of the system. -/
noncomputable abbrev crystalPairE : PairE hp := (toPairE hp).obj ((crystalPairFunctor hp).obj Fc)

/-- The connection of the pair of a crystal has coordinates minus the crystal's `θ_c`. -/
theorem isCoordinateExpansion_crystalPairE :
    IsCoordinateExpansion S.p (envD S hp) (pairForms hp) (pairDx hp) (crystalPairE hp Fc).nabla
      (fun c m ↦ -crystalTheta hp Fc (Finsupp.single c 1) m) :=
  isCoordinateExpansion_pairConnection hp Fc

/-- The Taylor operators of the pair of a crystal are the crystal's. -/
theorem taylorTheta_crystalPairE (c : wholeSpaceIndex S hp)
    (m : wholeSpaceSections hp Fc ⦋0⦌) :
    (crystalPairE hp Fc).taylorTheta c m = crystalTheta hp Fc (Finsupp.single c 1) m :=
  taylorTheta_eq_of_isCoordinateExpansion (crystalPairE hp Fc) (isCoordinateDual_pairCoordE hp)
    (isCoordinateExpansion_crystalPairE hp Fc) c m

/-- The composite Taylor operators of the pair of a crystal are the crystal's `θ_K`. -/
theorem taylorThetaPow_crystalPairE (K : wholeSpaceIndex S hp →₀ ℕ)
    (m : wholeSpaceSections hp Fc ⦋0⦌) :
    (crystalPairE hp Fc).taylorThetaPow (isCoordinateDual_pairCoordE hp) K m =
      crystalTheta hp Fc K m :=
  taylorThetaPow_eq_of_isThetaMonomialFamily (crystalPairE hp Fc)
    (isCoordinateDual_pairCoordE hp) (isThetaMonomialFamily_crystalTheta hp Fc)
    (taylorTheta_crystalPairE hp Fc) K m

/-- **An identification of the limit module of a crystal with the module of a pair, carrying the
Taylor operators of the crystal to those of the pair, is an isomorphism of the pair of the crystal
with the pair.** -/
noncomputable def crystalPairEIso (P : PairE hp)
    (φ : wholeSpaceSections hp Fc ⦋0⦌ ≃ₗ[envD S hp] P.carrier)
    (h : ∀ c m, φ (crystalTheta hp Fc (Finsupp.single c 1) m) = P.taylorTheta c (φ m)) :
    crystalPairE hp Fc ≅ P :=
  Pair.isoOfLinearEquivTaylorTheta φ fun c m ↦
    (congrArg φ (taylorTheta_crystalPairE hp Fc c m)).trans (h c m)

/-- The term `ξ^{[K]} ⊗ θ_K(m)` of the Taylor stratification of the pair of a crystal, mapped to
the sections over `T(1)_e`, is `ξ^{[K]} · p₀^* θ_K(m)`. -/
theorem crystalPointMap_term (e : ℕ) (m : wholeSpaceSections hp Fc ⦋0⦌)
    (K : wholeSpaceIndex S hp →₀ ℕ) :
    crystalPointMap hp Fc ((wholeSpaceDescentSystem S hp).v e 0).hom
        (TaylorStratification.term ((wholeSpaceDescentSystem S hp).ptRing
          ((wholeSpaceDescentSystem S hp).v e 0)) (levelTaylorMonomial hp e)
          ((crystalPairE hp Fc).taylorThetaPowHom (isCoordinateDual_pairCoordE hp)) m K) =
      levelTaylorMonomial hp e K •
        crysRestrict Fc.obj (wholeSpaceTrans hp (SimplexCategory.δ (n := 0) 1) e)
          ((levelTaylorExpansion hp Fc e).coeffs (wholeSpaceSectionsVal hp Fc m e) K) := by
  have h0 : ((wholeSpaceDescentSystem S hp).v e 0).hom =
      wholeSpaceTrans hp (SimplexCategory.δ (n := 0) 1) e := wholeSpaceVertex_one_zero hp e
  have h1 : wholeSpaceSectionsVal hp Fc
      ((crystalPairE hp Fc).taylorThetaPow (isCoordinateDual_pairCoordE hp) K m) e =
      (levelTaylorExpansion hp Fc e).coeffs (wholeSpaceSectionsVal hp Fc m e) K := by
    rw [taylorThetaPow_crystalPairE, wholeSpaceSectionsVal_crystalTheta]
    rfl
  calc _ = levelTaylorMonomial hp e K • crysRestrict Fc.obj
        ((wholeSpaceDescentSystem S hp).v e 0).hom (wholeSpaceSectionsVal hp Fc
          ((crystalPairE hp Fc).taylorThetaPow (isCoordinateDual_pairCoordE hp) K m) e) := rfl
    _ = _ := by rw [h1, h0]

open scoped Classical in
/-- **The Taylor stratification of the pair of a crystal is the crystal's own stratification**:
the restriction of `m` along the second projection `T(1)_e ⟶ T(0)_e`, written in the
trivialisation of the first, is `∑_K ξ^{[K]} ⊗ θ_K(m)`. -/
theorem crystalPointMap_pairStr (e : ℕ) (m : wholeSpaceSections hp Fc ⦋0⦌) :
    crystalPointMap hp Fc ((wholeSpaceDescentSystem S hp).v e 0).hom
        (pairStr (wholeSpaceTaylorData S hp) (crystalPairE hp Fc) (isCoordinateDual_pairCoordE hp)
          (isThetaMonomialFamily_wholeSpaceTaylorData_delta S hp)
          (fun c f ↦ pairCoord_pairDerivation S hp c f) e m) =
      crysRestrict Fc.obj ((wholeSpaceDescentSystem S hp).v e 1).hom
        (wholeSpaceSectionsVal hp Fc m e) := by
  obtain ⟨s, hs⟩ := exists_finset_term_eq_zero (wholeSpaceTaylorData S hp) (crystalPairE hp Fc)
    (isCoordinateDual_pairCoordE hp) e m
  have h1 : ((wholeSpaceDescentSystem S hp).v e 1).hom =
      wholeSpaceTrans hp (SimplexCategory.δ (n := 0) 0) e := wholeSpaceVertex_one_one hp e
  have hrhs := (crysRestrict_δ_zero_eq_sum hp Fc e (wholeSpaceSectionsVal hp Fc m e)).trans
    (Finsupp.sum_of_support_subset _ (Finset.subset_union_right (s₁ := s)) _
      fun K _ ↦ by rw [map_zero, smul_zero])
  rw [← h1] at hrhs
  rw [hrhs]
  have hsum := TaylorStratification.taylorMap_eq_sum (q₀ := (wholeSpaceDescentSystem S hp).ptRing
    ((wholeSpaceDescentSystem S hp).v e 0)) (ξ := (wholeSpaceTaylorData S hp).xi e)
    (θ := (crystalPairE hp Fc).taylorThetaPowHom (isCoordinateDual_pairCoordE hp)) (m := m)
    (s ∪ ((levelTaylorExpansion hp Fc e).coeffs (wholeSpaceSectionsVal hp Fc m e)).support)
    (fun K (hK : K ∉ s ∪ _) ↦ hs K fun h ↦ hK (Finset.mem_union_left _ h))
  refine (congrArg (crystalPointMap hp Fc ((wholeSpaceDescentSystem S hp).v e 0).hom) hsum).trans ?_
  refine (map_sum (crystalPointMap hp Fc ((wholeSpaceDescentSystem S hp).v e 0).hom) _ _).trans ?_
  exact Finset.sum_congr rfl fun K _ ↦ crystalPointMap_term hp Fc e m K

/-- The stratified module of the pair of a crystal. -/
noncomputable abbrev crystalStratModule (Fc : QuasiCoherentCrystal S) : StratModule S hp :=
  (pairStratFunctorE hp).obj (crystalPairE hp Fc)

/-- The Taylor stratification of the pair of a crystal, on the crystal's limit module. -/
noncomputable abbrev crystalStrat (Fc : QuasiCoherentCrystal S) :
    Stratification (wholeSpaceDescentSystem S hp) (wholeSpaceSections hp Fc ⦋0⦌) :=
  (crystalStratModule hp Fc).strat

/-- **A crystal is the crystal of its pair**: the crystal descended from the Taylor stratification
of the pair of `ℱ` is `ℱ`. -/
noncomputable def crystalPairCounitIso :
    (pairCrystalFunctor hp).obj (crystalPairE hp Fc) ≅ Fc :=
  stratCrystalIso Fc (crystalStrat hp Fc) (crystalPointMap_pairStr hp Fc)

open scoped Classical in
/-- **The counit is natural**: for a morphism `ψ : ℱ ⟶ 𝒢` of crystals, the image of the induced
morphism of pairs under the quasi-inverse, followed by the counit of `𝒢`, is the counit of `ℱ`
followed by `ψ`. -/
theorem crystalPairCounitIso_naturality {Gc : QuasiCoherentCrystal S} (ψ : Fc ⟶ Gc) :
    (pairCrystalFunctor hp).map ((toPairE hp).map ((crystalPairFunctor hp).map ψ)) ≫
        (crystalPairCounitIso hp Gc).hom = (crystalPairCounitIso hp Fc).hom ≫ ψ :=
  stratCrystalIso_naturality (F := Fc) (G := Gc) (crystalStrat hp Fc) (E' := crystalStrat hp Gc)
    (crystalPointMap_pairStr hp Fc) (crystalPointMap_pairStr hp Gc) ψ
    ((toPairE hp).map ((crystalPairFunctor hp).map ψ)).toLinearMap
    (pairStr_map (wholeSpaceTaylorData S hp) (crystalPairE hp Fc) (isCoordinateDual_pairCoordE hp)
      (isThetaMonomialFamily_wholeSpaceTaylorData_delta S hp)
      (fun c f ↦ pairCoord_pairDerivation S hp c f)
      ((toPairE hp).map ((crystalPairFunctor hp).map ψ))) (fun _ ↦ rfl)

end Counit

/-! ### Full and faithful -/

section FullyFaithful

/-- The functor of [Stacks, Tag 07JG], with its target read over the completed envelope of the
system. -/
noncomputable abbrev crystalPairFunctorE : QuasiCoherentCrystal S ⥤ PairE hp :=
  crystalPairFunctor hp ⋙ toPairE hp

/-- **The functor of [Stacks, Tag 07JG] is faithful**: a morphism of crystals in quasi-coherent
modules is determined by the map it induces on `M = lim_e Γ(T_e, ℱ)`. -/
instance faithful_crystalPairFunctorE : (crystalPairFunctorE hp).Faithful where
  map_injective {Fc Gc} := Function.Injective.of_comp
    (f := fun f : (crystalPairFunctorE hp).obj Fc ⟶ (crystalPairFunctorE hp).obj Gc ↦
      ⇑f.toLinearMap)
    (Function.Injective.comp
      (f := fun ψ : Fc ⟶ Gc ↦ (wholeSpaceLevelScalars hp 0).sectionsMap ψ)
      DFunLike.coe_injective
      (@eq_of_wholeSpaceSectionsMap_eq S _ _ hp _ Fc Gc))

/-- On limit modules, the map of `α.hom` undoes the map of `α.inv`. -/
theorem sectionsMap_inv_hom_apply {Fc Gc : QuasiCoherentCrystal S} (α : Fc ≅ Gc)
    (m : wholeSpaceSections hp Gc ⦋0⦌) :
    (wholeSpaceLevelScalars hp 0).sectionsMap α.hom
      ((wholeSpaceLevelScalars hp 0).sectionsMap α.inv m) = m := by
  have h := LinearMap.congr_fun ((wholeSpaceLevelScalars hp 0).sectionsMap_comp α.inv α.hom) m
  rw [α.inv_hom_id, (wholeSpaceLevelScalars hp 0).sectionsMap_id] at h
  exact h.symm

/-- On limit modules, the map of `α.inv` undoes the map of `α.hom`. -/
theorem sectionsMap_hom_inv_apply {Fc Gc : QuasiCoherentCrystal S} (α : Fc ≅ Gc)
    (m : wholeSpaceSections hp Fc ⦋0⦌) :
    (wholeSpaceLevelScalars hp 0).sectionsMap α.inv
      ((wholeSpaceLevelScalars hp 0).sectionsMap α.hom m) = m :=
  sectionsMap_inv_hom_apply hp α.symm m

/-- The limit module of the crystal of the pair of a crystal is the crystal's limit module. -/
noncomputable abbrev crystalStratLimitEquiv (Fc : QuasiCoherentCrystal S) :=
  stratLimitEquiv (crystalStratModule hp Fc).strat (crystalPairE hp Fc).isPAdicallyComplete

/-- On the limit modules, the counit is `crystalStratLimitEquiv`. -/
theorem sectionsMap_crystalPairCounitIso_hom (Fc : QuasiCoherentCrystal S)
    (m : wholeSpaceSections hp Fc ⦋0⦌) :
    (wholeSpaceLevelScalars hp 0).sectionsMap (crystalPairCounitIso hp Fc).hom
      ((crystalStratLimitEquiv hp Fc).symm m) = m :=
  sectionsMap_stratCrystalIso_hom hp (crystalPointMap_pairStr hp Fc)
    (crystalPairE hp Fc).isPAdicallyComplete m

/-- On the limit modules, the inverse of the counit is the inverse of `crystalStratLimitEquiv`. -/
theorem sectionsMap_crystalPairCounitIso_inv (Fc : QuasiCoherentCrystal S)
    (m : wholeSpaceSections hp Fc ⦋0⦌) :
    (wholeSpaceLevelScalars hp 0).sectionsMap (crystalPairCounitIso hp Fc).inv m =
      (crystalStratLimitEquiv hp Fc).symm m :=
  (congrArg ((wholeSpaceLevelScalars hp 0).sectionsMap (crystalPairCounitIso hp Fc).inv)
      (sectionsMap_crystalPairCounitIso_hom hp Fc m)).symm.trans
    (sectionsMap_hom_inv_apply hp (crystalPairCounitIso hp Fc) _)

/-- On the limit modules, the quasi-inverse applied to a morphism of pairs of crystals is the
morphism, read through `crystalStratLimitEquiv`. -/
theorem sectionsMap_pairCrystalFunctor_map {Fc Gc : QuasiCoherentCrystal S}
    (φ : (crystalPairFunctorE hp).obj Fc ⟶ (crystalPairFunctorE hp).obj Gc)
    (m : wholeSpaceSections hp Fc ⦋0⦌) :
    (wholeSpaceLevelScalars hp 0).sectionsMap ((pairCrystalFunctor hp).map φ)
        ((crystalStratLimitEquiv hp Fc).symm m) =
      (crystalStratLimitEquiv hp Gc).symm (φ.toLinearMap m) := by
  refine (LinearEquiv.eq_symm_apply _).mpr ?_
  have key := stratLimitEquiv_naturality ((pairStratFunctorE hp).map φ)
    (crystalPairE hp Fc).isPAdicallyComplete (crystalPairE hp Gc).isPAdicallyComplete
    ((crystalStratLimitEquiv hp Fc).symm m)
  exact key.trans (congrArg φ.toLinearMap ((crystalStratLimitEquiv hp Fc).apply_symm_apply m))

/-- **The functor of [Stacks, Tag 07JG] is full**: a horizontal map of the pairs of two crystals is
induced by the morphism of crystals `α_𝒢 ∘ G(φ) ∘ α_ℱ⁻¹`, where `G` is the quasi-inverse and `α`
the counit. -/
theorem crystalPairFunctorE_map_apply {Fc Gc : QuasiCoherentCrystal S} (ψ : Fc ⟶ Gc)
    (m : wholeSpaceSections hp Fc ⦋0⦌) :
    ((crystalPairFunctorE hp).map ψ).toLinearMap m =
      (wholeSpaceLevelScalars hp 0).sectionsMap ψ m := rfl

/-- The preimage of a morphism of pairs of crystals: `α_𝒢 ∘ G(φ) ∘ α_ℱ⁻¹`. -/
noncomputable def crystalPairPreimage {Fc Gc : QuasiCoherentCrystal S}
    (φ : (crystalPairFunctorE hp).obj Fc ⟶ (crystalPairFunctorE hp).obj Gc) : Fc ⟶ Gc :=
  (crystalPairCounitIso hp Fc).inv ≫ (pairCrystalFunctor hp).map φ ≫
    (crystalPairCounitIso hp Gc).hom

/-- On limit modules, the preimage of a horizontal map of pairs is that map. -/
theorem sectionsMap_crystalPairPreimage {Fc Gc : QuasiCoherentCrystal S}
    (φ : (crystalPairFunctorE hp).obj Fc ⟶ (crystalPairFunctorE hp).obj Gc)
    (m : wholeSpaceSections hp Fc ⦋0⦌) :
    (wholeSpaceLevelScalars hp 0).sectionsMap (crystalPairPreimage hp φ) m = φ.toLinearMap m := by
  rw [crystalPairPreimage, (wholeSpaceLevelScalars hp 0).sectionsMap_comp,
    (wholeSpaceLevelScalars hp 0).sectionsMap_comp]
  refine (congrArg ((wholeSpaceLevelScalars hp 0).sectionsMap (crystalPairCounitIso hp Gc).hom)
    ((congrArg ((wholeSpaceLevelScalars hp 0).sectionsMap ((pairCrystalFunctor hp).map φ))
      (sectionsMap_crystalPairCounitIso_inv hp Fc m)).trans
        (sectionsMap_pairCrystalFunctor_map hp φ m))).trans ?_
  exact sectionsMap_crystalPairCounitIso_hom hp Gc _

/-- **The functor of [Stacks, Tag 07JG] is full**: a horizontal map of the pairs of two crystals is
induced by the morphism of crystals `α_𝒢 ∘ G(φ) ∘ α_ℱ⁻¹`, where `G` is the quasi-inverse and `α`
the counit. -/
instance full_crystalPairFunctorE : (crystalPairFunctorE hp).Full where
  map_surjective φ := ⟨crystalPairPreimage hp φ, PairHom.ext (LinearMap.ext fun m ↦
    (crystalPairFunctorE_map_apply hp _ m).trans (sectionsMap_crystalPairPreimage hp φ m))⟩

end FullyFaithful

/-! ### The pair of the crystal of a pair is the pair -/

section Unit

variable (P : PairE hp)

/-- The crystal of a pair. -/
noncomputable abbrev pairCrystal : QuasiCoherentCrystal S := (pairCrystalFunctor hp).obj P

/-- The limit module of the crystal of a pair is the pair's module. -/
noncomputable abbrev pairCrystalLimitEquiv :
    wholeSpaceSections hp (pairCrystal hp P) ⦋0⦌ ≃ₗ[envD S hp] P.carrier :=
  stratLimitEquiv ((pairStratFunctorE hp).obj P).strat P.isPAdicallyComplete

/-- The level component of the element of the limit module of a stratified module corresponding to
an element of `p^{N+e} M` vanishes. -/
private theorem wholeSpaceSectionsVal_stratLimitEquiv_symm_eq_zero {M : Type u} [AddCommGroup M]
    [Module (envD S hp) M] (E : Stratification (wholeSpaceDescentSystem S hp) M)
    (hM : IsPAdicallyComplete S.p (envD S hp) M) (e : ℕ) {y : M}
    (hy : y ∈ pPowSmul S.p (envD S hp) M
      (_root_.Crystalline.uniformLevel (affineSituation S hp) + e)) :
    wholeSpaceSectionsVal hp (stratCrystal E) ((stratLimitEquiv E hM).symm y) e = 0 := by
  have h0 : (stratLevelSubmodule hp M e).mkQ y = 0 := (Submodule.Quotient.mk_eq_zero _).mpr hy
  exact (congrArg (stratLevelEquiv E e).symm h0).trans (map_zero _)

/-- The level component of the element of the limit module corresponding to an element of
`p^{N+e} M` vanishes. -/
theorem wholeSpaceSectionsVal_pairCrystalLimitEquiv_symm_eq_zero (e : ℕ) {y : P.carrier}
    (hy : y ∈ pPowSmul S.p (envD S hp) P.carrier
      (_root_.Crystalline.uniformLevel (affineSituation S hp) + e)) :
    wholeSpaceSectionsVal hp (pairCrystal hp P) ((pairCrystalLimitEquiv hp P).symm y) e = 0 :=
  wholeSpaceSectionsVal_stratLimitEquiv_symm_eq_zero hp _ _ e hy

end Unit

/-! ### The Taylor operators of the crystal of a Taylor-stratified module -/

section TaylorStratified

open scoped Classical in
/-- **The Taylor operators of the crystal of a stratified module whose stratification is the Taylor
map of a family `θ` are `θ`**, at each level: by uniqueness of the coefficients of the Taylor
expansion of the crystal over `T(1)_e`. -/
theorem levelTheta_stratCrystal {M : Type u} [AddCommGroup M] [Module (envD S hp) M]
    (E : Stratification (wholeSpaceDescentSystem S hp) M)
    (hM : IsPAdicallyComplete S.p (envD S hp) M)
    (θ : (wholeSpaceIndex S hp →₀ ℕ) → M →+ M)
    (hE : ∀ e m, E.str e m = TaylorStratification.taylorMap
      ((wholeSpaceDescentSystem S hp).ptRing ((wholeSpaceDescentSystem S hp).v e 0))
      ((wholeSpaceTaylorData S hp).xi e) θ m)
    (hfin : ∀ e m, {L | θ L m ∉ pPowSmul S.p (envD S hp) M
      (_root_.Crystalline.uniformLevel (affineSituation S hp) + e)}.Finite)
    (e : ℕ) (K : wholeSpaceIndex S hp →₀ ℕ) (m : M) :
    levelTheta hp (stratCrystal E) e K
        (wholeSpaceSectionsVal hp (stratCrystal E) ((stratLimitEquiv E hM).symm m) e) =
      wholeSpaceSectionsVal hp (stratCrystal E) ((stratLimitEquiv E hM).symm (θ K m)) e := by
  set n := _root_.Crystalline.uniformLevel (affineSituation S hp) + e
  set ι := stratLimitEquiv E hM
  set s := (hfin e m).toFinset
  have hout : ∀ L ∉ s, θ L m ∈ pPowSmul S.p (envD S hp) M n := fun L hL ↦ by
    rw [Set.Finite.mem_toFinset, Set.mem_ofPred_eq, not_not] at hL
    exact hL
  have hterm : ∀ L ∉ s, TaylorStratification.term
      ((wholeSpaceDescentSystem S hp).ptRing ((wholeSpaceDescentSystem S hp).v e 0))
      ((wholeSpaceTaylorData S hp).xi e) θ m L = 0 := fun L hL ↦ by
    obtain ⟨y, hy⟩ := exists_eq_pow_smul_of_mem_pPowSmul (hout L hL)
    refine TaylorStratification.term_eq_zero_of_smul (d := (S.p : envD S hp) ^ n) ?_ hy
    rw [map_pow, map_natCast]
    exact (wholeSpaceTaylorData S hp).nil_one e
  set T := levelTaylorExpansion hp (stratCrystal E) e
  let g : (wholeSpaceIndex S hp →₀ ℕ) →₀ (stratCrystal E).obj.val.obj (op (levelObj hp 0 e)) :=
    ∑ L ∈ s, Finsupp.single L (wholeSpaceSectionsVal hp (stratCrystal E) (ι.symm (θ L m)) e)
  have h1 : ((wholeSpaceDescentSystem S hp).v e 1).hom =
      wholeSpaceTrans hp (SimplexCategory.δ (n := 0) 0) e := wholeSpaceVertex_one_one hp e
  have h10 := crystalPointMap_stratCrystal E hM e m
  have key : crystalPointMap hp (stratCrystal E) ((wholeSpaceDescentSystem S hp).v e 0).hom
      (LinearMap.lTensor _ ι.symm.toLinearMap (E.str e m)) =
      ∑ L ∈ s, levelTaylorMonomial hp e L • crysRestrict (stratCrystal E).obj
        (wholeSpaceVertex S hp 1 e 0)
          (wholeSpaceSectionsVal hp (stratCrystal E) (ι.symm (θ L m)) e) := by
    rw [hE, TaylorStratification.taylorMap_eq_sum s hterm]
    exact (congrArg (crystalPointMap hp (stratCrystal E) ((wholeSpaceDescentSystem S hp).v e 0).hom)
      (map_sum (LinearMap.lTensor _ ι.symm.toLinearMap) _ s)).trans
        ((map_sum (crystalPointMap hp (stratCrystal E) ((wholeSpaceDescentSystem S hp).v e 0).hom)
          _ s).trans (Finset.sum_congr rfl fun L _ ↦ rfl))
  rw [key] at h10
  have hg : taylorSum T.a₀ T.xi g =
      T.a₁ (wholeSpaceSectionsVal hp (stratCrystal E) (ι.symm m) e) := by
    have ha₁ : T.a₁ (wholeSpaceSectionsVal hp (stratCrystal E) (ι.symm m) e) =
        crysRestrict (stratCrystal E).obj ((wholeSpaceDescentSystem S hp).v e 1).hom
          (wholeSpaceSectionsVal hp (stratCrystal E) (ι.symm m) e) := by
      rw [h1]
      rfl
    rw [ha₁, ← h10]
    simp only [g, map_sum, taylorSum_single]
    refine Finset.sum_congr rfl fun L _ ↦ ?_
    have ha₀ : ∀ y, T.a₀ y = crysRestrict (stratCrystal E).obj
        (wholeSpaceVertex S hp 1 e 0) y := fun y ↦ by
      rw [wholeSpaceVertex_one_zero hp e]
      rfl
    rw [ha₀]
    rfl
  rw [levelTheta, TaylorExpansion.theta_apply, T.coeffs_eq_of_taylorSum hg]
  simp only [g, Finsupp.finsetSum_apply, Finsupp.single_apply]
  rw [Finset.sum_ite_eq']
  split_ifs with hK
  · rfl
  · exact (wholeSpaceSectionsVal_stratLimitEquiv_symm_eq_zero hp E hM e (hout K hK)).symm

end TaylorStratified

/-! ### Essential surjectivity -/

section EssSurj

variable (P : PairE hp)

/-- **The Taylor operators of the crystal of a pair are the pair's**, read through
`pairCrystalLimitEquiv`. -/
theorem crystalTheta_pairCrystal (K : wholeSpaceIndex S hp →₀ ℕ) (m : P.carrier) :
    crystalTheta hp (pairCrystal hp P) K ((pairCrystalLimitEquiv hp P).symm m) =
      (pairCrystalLimitEquiv hp P).symm
        (P.taylorThetaPow (isCoordinateDual_pairCoordE hp) K m) :=
  wholeSpaceSectionsVal_injective hp (pairCrystal hp P) fun e ↦ by
    rw [wholeSpaceSectionsVal_crystalTheta]
    exact levelTheta_stratCrystal hp ((pairStratFunctorE hp).obj P).strat P.isPAdicallyComplete
      (P.taylorThetaPowHom (isCoordinateDual_pairCoordE hp)) (fun _ _ ↦ rfl)
      (fun e m ↦ P.finite_taylorThetaPow_notMem (isCoordinateDual_pairCoordE hp) _ m) e K m

/-- The first-order case of `crystalTheta_pairCrystal`. -/
theorem crystalTheta_single_pairCrystal (c : wholeSpaceIndex S hp) (m : P.carrier) :
    crystalTheta hp (pairCrystal hp P) (Finsupp.single c 1) ((pairCrystalLimitEquiv hp P).symm m) =
      (pairCrystalLimitEquiv hp P).symm (P.taylorTheta c m) := by
  rw [crystalTheta_pairCrystal, (P.isThetaMonomialFamily_taylorThetaPow
    (isCoordinateDual_pairCoordE hp)).single, Function.iterate_one]

/-- **The pair of the crystal of a pair is isomorphic to the pair**, through
`pairCrystalLimitEquiv`, which carries the Taylor operators of the crystal to those of the
pair. -/
noncomputable def crystalPairFunctorEPairCrystalIso :
    crystalPairE hp (pairCrystal hp P) ≅ P :=
  crystalPairEIso hp (pairCrystal hp P) P (pairCrystalLimitEquiv hp P) fun c x ↦ by
    obtain ⟨m, rfl⟩ := (pairCrystalLimitEquiv hp P).symm.surjective x
    rw [crystalTheta_single_pairCrystal, LinearEquiv.apply_symm_apply,
      LinearEquiv.apply_symm_apply]

/-- **The functor of [Stacks, Tag 07JG] is essentially surjective**: every pair is the pair of the
crystal of its Taylor stratification. -/
instance essSurj_crystalPairFunctorE : (crystalPairFunctorE hp).EssSurj where
  mem_essImage P := ⟨pairCrystal hp P, ⟨crystalPairFunctorEPairCrystalIso hp P⟩⟩

end EssSurj

/-- The functor of [Stacks, Tag 07JG], with its target read over the completed envelope of the
system, is an equivalence. -/
instance isEquivalence_crystalPairFunctorE : (crystalPairFunctorE hp).IsEquivalence :=
  Functor.IsEquivalence.mk

/-- **[Stacks, Proposition 60.17.4, Tag 07JH]: the functor of [Stacks, Lemma 60.17.3, Tag 07JG]**

`{crystals in quasi-coherent 𝒪_{X/S}-modules on Cris(X/S)} ⟶ {pairs (M, ∇) satisfying (07JB),
(07JC), (07JD) and (07JE)}`

**is an equivalence of categories.**  This is the functor `...SmallSite.crystalPairFunctor` of
the tag 07JG, in the situation of [Stacks, Section 60.17, Tag 07J7]: `X = Spec(C)`,
`S = Spec(A)` affine with `p` nilpotent on `C`, any surjective polynomial presentation
`P = A[x_i : i ∈ ι] → C` (the instance `...SmallSite.WholeSpacePresentation S hp` the system of
thickenings is built from; by default the tautological `A[x_c : c ∈ C] → C`), `D`
the `p`-adically completed divided power envelope and `Ω_D` its completed module of divided power
differentials.  It sends `ℱ` to `M = lim_e Γ((X, T_e, δ̄), ℱ)` with its specified canonical
crystalline connection: the canonical connection of [Stacks, Tag 07J6] evaluated on the finite
thickenings `(X, T_e, δ̄)`, which is
`...SmallSite.pairTensorLevel_crystalPairFunctor_nabla`. -/
@[stacks 07JH "for any surjective polynomial presentation g : P = A[x_i : i ∈ ι] → C, supplied \
as the WholeSpacePresentation instance (the default instance is the tautological one): the \
functor of 07JG, from the crystals in quasi-coherent \
O_{X/S}-modules on Cris(X/S) to the pairs (M, ∇) over D satisfying (07JB), (07JC), (07JD) and \
(07JE), with its connection \
the canonical connection of 07J6 evaluated on the finite thickenings \
(pairTensorLevel_crystalPairFunctor_nabla), is an equivalence of categories"]
theorem crystalPairFunctor_isEquivalence : (crystalPairFunctor hp).IsEquivalence :=
  Functor.isEquivalence_of_comp_right (crystalPairFunctor hp) (toPairE hp)

end Crystalline.GlobalCrystallineSituation.SmallSite

end
