module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactificationIndependence.Refinement
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.ProperBaseChangeTheoremUnconditional
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.ProperPushforwardBaseChangeUnconditional
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.CompositeMorphismBaseChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.IntegralDirectImageAcyclic
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.AcyclicResolutionBaseChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.CoverTriangle
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryHomology
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.EtaleModuleExtForgetPullback
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.EtaleModuleRestrictScalars
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.ModuleProperVanishing
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.BoundednessTorsion
public import StacksFrontier.AlgebraicGeometry.Properties.ExtendFiniteType.LerayDegreewise
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Direct image along a refinement of compactifications of a sheaf supported on the interior

Let `j : X ⟶ A` and `k : X ⟶ B` be open immersions and `g : A ⟶ B` a proper morphism with
`j ≫ g = k`, and let `N` be an abelian sheaf on `A_étale` which vanishes away from `X`: its
inverse image along every morphism whose image misses `j(X)` is zero (an extension by zero
from `X`, for instance). This file proves the two facts about `Rg_* N` used in the proof of
[Stacks, Tag 0F7G]:

* `g_* N` vanishes on the complement `Z` of `k(X)` in `B`; this is the proper base change
  theorem in degree zero, [Stacks, Tag 0A3U], for the closed immersion `Z ⟶ B`, since the
  preimage of `Z` in `A` misses `j(X)`;
* if `N` is torsion, `R^q g_* N = 0` for `q > 0`: on `Z` by the proper base change theorem
  [Stacks, Tag 095T] as before, and on `X` by [Stacks, Tag 095T] for `k`, since over `X` the
  scheme `A ×_B X` contains `X` as an open and closed subscheme carrying all of `N`, and the
  direct image along the closed immersion of `X` followed by `A ×_B X ⟶ X` is the identity.

## Main results

* `Stacks.EtaleCohomology.isZero_etaleAbelianInverseImage_directImage_of_refinement`.
* `Stacks.EtaleCohomology.rightAcyclic_etaleAbelianDirectImage_of_refinement`.

## References

* [Stacks Project, Tag 0F7G](https://stacks.math.columbia.edu/tag/0F7G)
* [Stacks Project, Tag 0A3U](https://stacks.math.columbia.edu/tag/0A3U)
* [Stacks Project, Tag 095T](https://stacks.math.columbia.edu/tag/095T)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

/-! ### The closed complement of an open immersion -/

section Complement

variable {X B : Scheme.{u}} (k : X ⟶ B) [IsOpenImmersion k]

/-- The complement of the image of an open immersion, as a closed set. -/
abbrev openImmersionComplementCloseds : TopologicalSpace.Closeds B :=
  ⟨(Set.range k.base)ᶜ, isClosed_compl_iff.2 k.isOpenEmbedding.isOpen_range⟩

/-- The reduced closed subscheme on the complement of the image of an open immersion. -/
abbrev openImmersionComplement : Scheme.{u} :=
  (Scheme.IdealSheafData.vanishingIdeal (openImmersionComplementCloseds k)).subscheme

/-- The closed immersion of the complement of the image of an open immersion. -/
abbrev openImmersionComplementι : openImmersionComplement k ⟶ B :=
  (Scheme.IdealSheafData.vanishingIdeal (openImmersionComplementCloseds k)).subschemeι

/-- The underlying set of the complement of an open immersion is the complement of its image. -/
lemma range_openImmersionComplementι :
    Set.range (openImmersionComplementι k).base = (Set.range k.base)ᶜ := by
  rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal]
  rfl

/-- The image of an open immersion is the complement of the image of its closed complement. -/
lemma range_eq_compl_range_openImmersionComplementι :
    Set.range k.base = (Set.range (openImmersionComplementι k).base)ᶜ := by
  rw [range_openImmersionComplementι, compl_compl]

end Complement

/-! ### The direct image of a sheaf supported on the interior -/

section Refinement

variable {X A B : Scheme.{u}} {j : X ⟶ A} {k : X ⟶ B} {g : A ⟶ B} [IsOpenImmersion j]
  [IsOpenImmersion k] (hjk : j ≫ g = k)
  (N : Sheaf A.smallEtaleTopology AddCommGrpCat.{u + 1})
  (hN : ∀ ⦃T : Scheme.{u}⦄ (t : T ⟶ A), Disjoint (Set.range t.base) (Set.range j.base) →
    IsZero ((etaleAbelianInverseImage.{u, 0} t).obj N))

omit [IsOpenImmersion j] in
include hjk in
/-- The preimage in `A` of the complement of `k(X)` misses `j(X)`. -/
lemma disjoint_range_pullback_fst_openImmersionComplementι :
    Disjoint (Set.range (pullback.fst g (openImmersionComplementι k)).base)
      (Set.range j.base) := by
  rw [Set.disjoint_left]
  rintro _ ⟨p, rfl⟩ ⟨x, hx⟩
  have h1 : (openImmersionComplementι k).base ((pullback.snd g (openImmersionComplementι k)).base p)
      ∈ Set.range (openImmersionComplementι k).base := ⟨_, rfl⟩
  rw [range_openImmersionComplementι] at h1
  refine h1 ⟨x, ?_⟩
  rw [← Scheme.Hom.comp_apply, ← pullback.condition, Scheme.Hom.comp_apply, ← hx,
    ← Scheme.Hom.comp_apply, hjk]

omit [IsOpenImmersion j] in
include hjk hN in
/-- **`g_* N` vanishes on the complement of `X`**: by proper base change in degree zero
([Stacks, Tag 0A3U]) its inverse image to the complement `Z` is the direct image of the inverse
image of `N` to `g⁻¹(Z)`, which misses `j(X)`. -/
theorem isZero_etaleAbelianInverseImage_directImage_of_refinement [IsProper g] :
    IsZero ((etaleAbelianInverseImage.{u, 0} (openImmersionComplementι k)).obj
      ((etaleAbelianDirectImage.{u, 0} g).obj N)) := by
  let i := openImmersionComplementι k
  have sq := IsPullback.of_hasPullback g i
  have := isIso_etaleAbelianBaseChange_of_isProper g i (pullback.fst g i) (pullback.snd g i) sq
  refine IsZero.of_iso ?_ ((asIso (etaleAbelianBaseChange.{u, 0} g i (pullback.fst g i)
    (pullback.snd g i) sq.w)).app N)
  exact (etaleAbelianDirectImage.{u, 0} (pullback.snd g i)).map_isZero
    (hN _ (disjoint_range_pullback_fst_openImmersionComplementι hjk))

section Higher

/- The abelian derived direct and inverse images of this part are those of
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleAbelianDerivedFunctors`, defined in the
standard model of the derived category. The lemmas that leave this section are stated without
derived categories. -/
attribute [local instance] HasDerivedCategory.standard

/-- The cohomology sheaves of `Rf_*` of `N[0]` vanish in a degree `q` as soon as the inverse
image of `N` along `g'` vanishes, for a proper base change square. -/
private lemma isZero_inverseImage_homology_of_isZero {X' Y Y' : Scheme.{u}} {f : A ⟶ Y}
    [IsProper f] {g₀ : Y' ⟶ Y} {g' : X' ⟶ A} {f' : X' ⟶ Y'} (sq : IsPullback g' f' f g₀)
    (hT : Stacks.Torsion.torsionSheafProperty A.smallEtaleTopology N) (q : ℤ)
    (h : ∀ M : DerivedCategory (Sheaf X'.smallEtaleTopology AddCommGrpCat.{u + 1}),
      (M ≅ (etaleAbelianDerivedInverseImage.{u, 0} g').obj
        ((DerivedCategory.singleFunctor (Sheaf A.smallEtaleTopology AddCommGrpCat.{u + 1}) 0).obj
          N)) →
      IsZero ((DerivedCategory.homologyFunctor _ q).obj
        ((etaleAbelianDerivedDirectImage.{u, 0} f').obj M))) :
    IsZero ((etaleAbelianInverseImage.{u, 0} g₀).obj
      ((DerivedCategory.homologyFunctor (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) q).obj
        ((etaleAbelianDerivedDirectImage.{u, 0} f).obj
          ((DerivedCategory.singleFunctor _ 0).obj N)))) := by
  have := isIso_etaleAbelianSheafDerivedBaseChange_of_isProper f g₀ g' f' sq N hT
  refine IsZero.of_iso ?_ (((etaleAbelianInverseImage.{u, 0} g₀).mapDerivedCategoryHomologyIso
    q).app _).symm
  refine IsZero.of_iso ?_ ((DerivedCategory.homologyFunctor _ q).mapIso
    (asIso (etaleAbelianSheafDerivedBaseChange.{u, 0} f g₀ g' f' sq.w N)))
  exact h _ (Iso.refl _)

include hjk hN in
/-- **`R^q g_* N` vanishes on `X` for `q > 0`**, by proper base change along `k` and the
splitting of `X` off `A ×_B X`. -/
private theorem isZero_etaleAbelianInverseImage_homology_derivedDirectImage_of_refinement
    [IsProper g] (hT : Stacks.Torsion.torsionSheafProperty A.smallEtaleTopology N) (q : ℤ)
    (hq : 0 < q) :
    IsZero ((etaleAbelianInverseImage.{u, 0} k).obj
      ((DerivedCategory.homologyFunctor (Sheaf B.smallEtaleTopology AddCommGrpCat.{u + 1}) q).obj
        ((etaleAbelianDerivedDirectImage.{u, 0} g).obj
          ((DerivedCategory.singleFunctor _ 0).obj N)))) := by
  refine isZero_inverseImage_homology_of_isZero N (IsPullback.of_hasPullback g k) hT q
    fun M e => ?_
  let s := refinementSection j k g hjk
  let O := refinementComplement hjk
  let N' := (etaleAbelianInverseImage.{u, 0} (pullback.fst g k)).obj N
  have hO' : IsZero ((etaleRestriction.{u, 0} O.ι).obj N') := by
    refine IsZero.of_iso ?_ ((etaleAbelianInverseImageRestrictionIso.{u, 0} O.ι).symm.app N')
    refine IsZero.of_iso ?_ ((etaleAbelianInverseImageCompIso.{u, 0} O.ι
      (pullback.fst g k)).symm.app N)
    exact hN _ (disjoint_range_refinementComplement hjk)
  obtain ⟨_, hS⟩ := shortExact_extensionByZero_etaleAbelianDirectImage.{u, 0} s O.ι
    (range_refinementComplement hjk) N'
  have hunit : IsIso ((etaleAbelianInverseImageDirectImageAdj.{u, 0} s).unit.app N') :=
    hS.isIso_g_iff.2 ((extensionByZero.{u, 0} O.ι).map_isZero hO')
  let P := (etaleAbelianInverseImage.{u, 0} s).obj N'
  have e₁ : M ≅ (etaleAbelianDerivedDirectImage.{u, 0} s).obj
      ((DerivedCategory.singleFunctor _ 0).obj P) :=
    e ≪≫ ((etaleAbelianInverseImage.{u, 0} (pullback.fst g k)).mapDerivedCategorySingleFunctor
      0).app N ≪≫ (DerivedCategory.singleFunctor _ 0).mapIso
        (asIso ((etaleAbelianInverseImageDirectImageAdj.{u, 0} s).unit.app N')) ≪≫
      (((etaleAbelianDirectImage.{u, 0} s).mapDerivedCategorySingleFunctor 0).app P).symm ≪≫
      (etaleAbelianDerivedDirectImageIso_of_isIntegralHom.{u, 0} s).symm.app _
  refine IsZero.of_iso ?_ ((DerivedCategory.homologyFunctor _ q).mapIso
    ((etaleAbelianDerivedDirectImage.{u, 0} (pullback.snd g k)).mapIso e₁))
  refine IsZero.of_iso ?_ ((DerivedCategory.homologyFunctor _ q).mapIso
    ((etaleAbelianDerivedDirectImageCompIso'.{u, 0} s (pullback.snd g k) (𝟙 X)
      (refinementSection_snd hjk).symm).symm.app _))
  refine IsZero.of_iso ?_ ((DerivedCategory.homologyFunctor _ q).mapIso
    ((etaleAbelianDerivedDirectImageIso_of_isIntegralHom.{u, 0} (𝟙 X)).app _ ≪≫
      ((etaleAbelianDirectImage.{u, 0} (𝟙 X)).mapDerivedCategorySingleFunctor 0).app P))
  exact DerivedCategory.isZero_of_isLE
    ((DerivedCategory.singleFunctor (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) 0).obj
      ((etaleAbelianDirectImage.{u, 0} (𝟙 X)).obj P)) 0 q hq

include hjk hN in
/-- **`R^q g_* N = 0` for `q > 0`**, for a torsion sheaf `N` on `A` vanishing away from `X`, by
the proper base change theorem on the complement of `X` and on `X`. -/
theorem isZero_homology_etaleAbelianDerivedDirectImage_of_refinement [IsProper g]
    (hT : Stacks.Torsion.torsionSheafProperty A.smallEtaleTopology N) (q : ℤ) (hq : 0 < q) :
    IsZero ((DerivedCategory.homologyFunctor (Sheaf B.smallEtaleTopology AddCommGrpCat.{u + 1})
      q).obj ((etaleAbelianDerivedDirectImage.{u, 0} g).obj
        ((DerivedCategory.singleFunctor _ 0).obj N))) := by
  have hU :=
    isZero_etaleAbelianInverseImage_homology_derivedDirectImage_of_refinement hjk N hN hT q hq
  set H := (DerivedCategory.homologyFunctor (Sheaf B.smallEtaleTopology AddCommGrpCat.{u + 1})
      q).obj ((etaleAbelianDerivedDirectImage.{u, 0} g).obj
        ((DerivedCategory.singleFunctor _ 0).obj N))
  let i := openImmersionComplementι k
  -- the closed part
  have hZ : IsZero ((etaleAbelianInverseImage.{u, 0} i).obj H) := by
    refine isZero_inverseImage_homology_of_isZero N (IsPullback.of_hasPullback g i) hT q
      fun M e => ?_
    refine (etaleAbelianDerivedDirectImage.{u, 0} _ ⋙
      DerivedCategory.homologyFunctor _ q).map_isZero ?_
    refine IsZero.of_iso ?_ (e ≪≫ ((etaleAbelianInverseImage.{u, 0}
      (pullback.fst g i)).mapDerivedCategorySingleFunctor 0).app N)
    exact (DerivedCategory.singleFunctor _ 0).map_isZero
      (hN _ (disjoint_range_pullback_fst_openImmersionComplementι hjk))
  have : IsIso ((etaleAbelianInverseImage.{u, 0} i).map (0 : H ⟶ H)) := hZ.isIso hZ _
  have : IsIso ((etaleAbelianInverseImage.{u, 0} k).map (0 : H ⟶ H)) := hU.isIso hU _
  have := isIso_of_isIso_etaleAbelianInverseImage.{u, 0} i k
    (range_eq_compl_range_openImmersionComplementι k) (0 : H ⟶ H)
  rw [IsZero.iff_id_eq_zero, ← IsIso.inv_hom_id (0 : H ⟶ H), comp_zero]

end Higher

end Refinement

/-! ### Sheaves of modules -/

section Modules

variable (Λ : Type) [Ring Λ]

/-- The abelian sheaf underlying a sheaf of `Λ`-modules is the one underlying its restriction of
scalars to `ℤ`. -/
def etaleModuleForgetIsoRestrictScalarsInt (X : Scheme.{u}) :
    etaleModuleForgetAb.{u, 0} Λ X ≅
      etaleModuleRestrictScalars (Int.castRingHom Λ) X ⋙ etaleModuleUnderlyingAbelian X ℤ :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => rfl)

/-- **Inverse image commutes with forgetting the module structure**, for an arbitrary ring `Λ`:
read through the restriction of scalars to `ℤ`, where it is
`Stacks.EtaleCohomology.etaleModuleUnderlyingAbelianInverseImageIso`. -/
def etaleModuleForgetInverseImageObjIso {X Y : Scheme.{u}} (t : Y ⟶ X)
    (M : EtaleModules.{u, 0} Λ X) :
    (etaleModuleForgetAb.{u, 0} Λ Y).obj ((etaleModuleInverseImage.{u, 0} Λ t).obj M) ≅
      (etaleAbelianInverseImage.{u, 0} t).obj ((etaleModuleForgetAb.{u, 0} Λ X).obj M) :=
  (etaleModuleForgetIsoRestrictScalarsInt Λ Y).app _ ≪≫
    (etaleModuleUnderlyingAbelian Y ℤ).mapIso
      ((etaleModuleInverseImageRestrictScalars (Int.castRingHom Λ) t).symm.app M) ≪≫
    ((etaleModuleUnderlyingAbelianInverseImageIso ℤ t).app _).symm ≪≫
    (etaleAbelianInverseImage.{u, 0} t).mapIso
      ((etaleModuleForgetIsoRestrictScalarsInt Λ X).app M).symm

/-- A sheaf of `Λ`-modules is zero if its underlying abelian sheaf is zero. -/
lemma isZero_of_isZero_etaleModuleForget {X : Scheme.{u}} {M : EtaleModules.{u, 0} Λ X}
    (h : IsZero ((etaleModuleForgetAb.{u, 0} Λ X).obj M)) : IsZero M := by
  rw [IsZero.iff_id_eq_zero]
  exact (etaleModuleForgetAb.{u, 0} Λ X).map_injective (by simpa using h.eq_of_src _ _)

variable {X A B : Scheme.{u}} {j : X ⟶ A} {k : X ⟶ B} {g : A ⟶ B} [IsOpenImmersion j]
  [IsOpenImmersion k] (hjk : j ≫ g = k)

/-- The abelian sheaf underlying `j_! F` vanishes away from `X`. -/
lemma isZero_etaleAbelianInverseImage_forget_extensionByZero (F : EtaleModules.{u, 0} Λ X)
    {T : Scheme.{u}} (t : T ⟶ A) (ht : Disjoint (Set.range t.base) (Set.range j.base)) :
    IsZero ((etaleAbelianInverseImage.{u, 0} t).obj
      ((etaleModuleForgetAb.{u, 0} Λ A).obj ((etaleModuleExtensionByZero.{u, 0} Λ j).obj F))) :=
  IsZero.of_iso ((etaleModuleForgetAb.{u, 0} Λ T).map_isZero
      (isZero_etaleModuleInverseImage_extensionByZero_of_disjoint Λ t j ht F))
    (etaleModuleForgetInverseImageObjIso Λ t _).symm

include hjk in
/-- **`g_* j_! F` vanishes on the complement of `X`**, for `g` proper. -/
theorem isZero_etaleModuleInverseImage_directImage_extensionByZero [IsProper g]
    (F : EtaleModules.{u, 0} Λ X) :
    IsZero ((etaleModuleInverseImage.{u, 0} Λ (openImmersionComplementι k)).obj
      ((etaleModuleDirectImage.{u, 0} Λ g).obj ((etaleModuleExtensionByZero.{u, 0} Λ j).obj F))) :=
  isZero_of_isZero_etaleModuleForget Λ (IsZero.of_iso
    (isZero_etaleAbelianInverseImage_directImage_of_refinement hjk _
      (fun _ t ht => isZero_etaleAbelianInverseImage_forget_extensionByZero Λ F t ht))
    (etaleModuleForgetInverseImageObjIso Λ _ _))

include hjk in
/-- **`R^q g_* (j_! F) = 0` for `q > 0`**, for `g` proper and `F` torsion. -/
theorem isZero_rightDerived_etaleModuleDirectImage_extensionByZero [IsProper g]
    (F : EtaleModules.{u, 0} Λ X) (hF : IsTorsionEtaleModule.{u, 0} Λ X F) (p : ℕ) (hp : 0 < p) :
    IsZero (((etaleModuleDirectImage.{u, 0} Λ g).rightDerived p).obj
      ((etaleModuleExtensionByZero.{u, 0} Λ j).obj F)) := by
  let : HasDerivedCategory (Sheaf A.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
    HasDerivedCategory.standard _
  let : HasDerivedCategory (Sheaf B.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
    HasDerivedCategory.standard _
  let M := (etaleModuleExtensionByZero.{u, 0} Λ j).obj F
  have hab : (etaleAbelianDirectImage.{u, 0} g).rightAcyclic
      ((etaleModuleForgetAb.{u, 0} Λ A).obj M) :=
    (rightAcyclic_etaleAbelianDirectImage_iff.{u, 0} g _).2 fun q hq =>
      isZero_homology_etaleAbelianDerivedDirectImage_of_refinement hjk _
        (fun _ t ht => isZero_etaleAbelianInverseImage_forget_extensionByZero Λ F t ht)
        (torsionSheafProperty_etaleModuleForget_obj_of_isTorsionEtaleModule Λ A
          (isTorsionEtaleModule_etaleModuleExtensionByZero_obj Λ j F hF)) q hq
  rw [Stacks.Cohomology.LerayDegreewise.rightAcyclic_iff_isZero_rightDerived] at hab
  exact isZero_of_isZero_etaleModuleForget Λ
    ((hab p hp).of_iso (etaleModuleForgetRightDerivedDirectImageIso Λ g M p))

include hjk in
/-- **`θ_g : k_! ⟶ g_* j_!` is an isomorphism** for `g` proper: it is invertible over `X` by
construction, and `g_* j_! F` vanishes on the complement of `X`, so it is the extension by zero
of its restriction to `X` (Tags 0F79 and 0F51 in this situation). -/
@[sga "4 XVII 3.3.2.1" "(iii)"]
theorem isIso_etaleModuleRefinementComparison [IsProper g] :
    IsIso (etaleModuleRefinementComparison Λ hjk) := by
  refine @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ fun F => ?_
  let G := (etaleModuleDirectImage.{u, 0} Λ g).obj ((etaleModuleExtensionByZero.{u, 0} Λ j).obj F)
  have e : (etaleModuleRefinementComparison Λ hjk).app F =
      (etaleModuleExtensionByZero.{u, 0} Λ k).map ((refinementComparisonAdj Λ hjk).app F) ≫
        (etaleModuleExtensionByZeroAdj.{u, 0} Λ k).counit.app G :=
    Adjunction.homEquiv_counit _ _ _ _
  have h₁ : IsIso ((refinementTarget Λ hjk).app F) := by
    simp only [refinementTarget, NatTrans.comp_app, Functor.whiskerRight_app, Functor.map_comp]
    infer_instance
  have h₂ : IsIso ((refinementComparisonAdj Λ hjk).app F) := by
    have := isIso_refinementRestrictedInclusion Λ hjk
    simp only [refinementComparisonAdj, NatTrans.comp_app]
    infer_instance
  obtain ⟨_, hS⟩ := shortExact_etaleModuleExtensionByZero_directImage Λ
    (openImmersionComplementι k) k (range_eq_compl_range_openImmersionComplementι k) G
  have h₃ : IsIso ((etaleModuleExtensionByZeroAdj.{u, 0} Λ k).counit.app G) :=
    hS.isIso_f_iff.2 ((etaleModuleDirectImage.{u, 0} Λ (openImmersionComplementι k)).map_isZero
      (isZero_etaleModuleInverseImage_directImage_extensionByZero Λ hjk F))
  rw [e]
  infer_instance

end Modules

end Stacks.EtaleCohomology

end
