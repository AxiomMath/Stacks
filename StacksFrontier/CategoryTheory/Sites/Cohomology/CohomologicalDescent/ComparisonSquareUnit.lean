module

public import StacksFrontier.Algebra.Homology.DerivedCategory.BoundedBelowExactAdjunctionEquivalence
public import StacksFrontier.Algebra.Homology.DerivedCategory.LerayDerivedUnitComparison
public import StacksFrontier.CategoryTheory.Abelian.RightDerivedPostcompose
public import StacksFrontier.Homology.CompositeCollapse
public import StacksFrontier.CategoryTheory.Sites.UniverseLiftDerived

/-!
# Cohomological descent through a commutative square of comparison morphisms

Let `a : 𝒰 → 𝒳`, `h : 𝒯 → 𝒰`, `a' : 𝒯 → 𝒴` and `h₋₁ : 𝒴 → 𝒳` be four adjunctions
`a⁻¹ ⊣ a_*`, `h⁻¹ ⊣ h_*`, `a'⁻¹ ⊣ a'_*` and `h₋₁⁻¹ ⊣ h₋₁,*` between abelian categories with
enough injectives, forming a square
```
  𝒯 --h--> 𝒰
  | a'      | a
  𝒴 -h₋₁-> 𝒳
```
which commutes in the sense that `h⁻¹ a⁻¹ ≅ a'⁻¹ h₋₁⁻¹`. This is the shape of the proofs of
Stacks 09XS (with the square of Stacks 0DAF) and of Stacks 0DH7 (with the square of Stacks 0DH5):
there `𝒳`, `𝒰` are the abelian sheaves on the small site of `X` and of `U`, `𝒴`, `𝒯` those on a
big site of `X` and on the total site of `U` in it, `h₋₁` and the components of `h` are the
comparisons of a big and a small site, and `a'` is the augmentation of a hypercovering of `X` in
the big site.

The source's computation `Ra_*a⁻¹ = Ra_*Rh_*h⁻¹a⁻¹ = Rh₋₁,*Ra'_*a'⁻¹h₋₁⁻¹ = Rh₋₁,*h₋₁⁻¹ = id`
is read here on a single object `F` of `𝒳`. With `M = a'⁻¹h₋₁⁻¹F`, it needs exactly:

* the unit of `h` to be invertible (`h⁻¹` fully faithful), and `M` to be right acyclic for `h_*`;
* the unit of `a'` to be invertible at `h₋₁⁻¹F`, and `M` to be right acyclic for `a'_*`
  (Stacks 0D8N, 0DA8 for a hypercovering);
* the unit of `h₋₁` to be invertible at `F`, and `h₋₁⁻¹F` to be right acyclic for `h₋₁,*`
  (Stacks 0DGG read on a single sheaf, resp. Stacks 0D91).

Then `F ⟶ a_*a⁻¹F` is an isomorphism and `R^q a_*(a⁻¹F) = 0` for `q > 0`; by Leray's acyclicity
lemma (Stacks 015E) the derived unit `K ⟶ Ra_*(a⁻¹K)` is an isomorphism for every `K` of
`D⁺(𝒳)`, and `RΓ(𝒳, K) = RΓ(𝒰, a⁻¹K)` for global sections functors with `Γ_𝒳 ∘ a_* = Γ_𝒰`
(Stacks 08J6).

## Main results

* `CategoryTheory.Adjunction.isIso_unit_app_of_comparisonSquare`: `F ≅ a_*a⁻¹F`.
* `CategoryTheory.Adjunction.isZero_rightDerived_of_comparisonSquare`: `R^q a_*(a⁻¹F) = 0`.
* `CategoryTheory.Adjunction.isIso_derivedPlusAdjunction_unit_app_of_comparisonSquare`: the
  derived unit `K ⟶ Ra_*(a⁻¹K)` is invertible on `D⁺(𝒳)`.
* `CategoryTheory.Adjunction.isIso_lerayPullback_app_of_comparisonSquare`: the pullback on
  derived global sections `RΓ(𝒳, K) ⟶ RΓ(𝒰, a⁻¹K)` is invertible.

## References

* [Stacks Project, Tag 0DH7](https://stacks.math.columbia.edu/tag/0DH7)
* [Stacks Project, Tag 0DH8](https://stacks.math.columbia.edu/tag/0DH8)
* [Stacks Project, Tag 09XS](https://stacks.math.columbia.edu/tag/09XS)
* [Stacks Project, Tag 015E](https://stacks.math.columbia.edu/tag/015E)
* [Stacks Project, Tag 08J6](https://stacks.math.columbia.edu/tag/08J6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Adjunction

variable {𝒳 𝒰 𝒴 𝒯 : Type*} [Category* 𝒳] [Category* 𝒰] [Category* 𝒴] [Category* 𝒯]
  [Abelian 𝒳] [Abelian 𝒰] [Abelian 𝒴] [Abelian 𝒯]
  [HasInjectiveResolutions 𝒰] [HasInjectiveResolutions 𝒴] [HasInjectiveResolutions 𝒯]
  {aInv : 𝒳 ⥤ 𝒰} {aDir : 𝒰 ⥤ 𝒳} (aAdj : aInv ⊣ aDir)
  {hInv : 𝒰 ⥤ 𝒯} {hDir : 𝒯 ⥤ 𝒰} (hAdj : hInv ⊣ hDir)
  {fInv : 𝒴 ⥤ 𝒯} {fDir : 𝒯 ⥤ 𝒴} (fAdj : fInv ⊣ fDir)
  {bInv : 𝒳 ⥤ 𝒴} {bDir : 𝒴 ⥤ 𝒳} (bAdj : bInv ⊣ bDir)
  (e : aInv ⋙ hInv ≅ bInv ⋙ fInv)

/-! ### Degreewise criteria for the comparison of total sites -/

section Degreewise

variable {ι : Type*} {𝒰ₙ 𝒯ₙ : ι → Type*} [∀ n, Category* (𝒰ₙ n)] [∀ n, Category* (𝒯ₙ n)]
  [∀ n, Abelian (𝒰ₙ n)] [∀ n, Abelian (𝒯ₙ n)] [∀ n, HasInjectiveResolutions (𝒯ₙ n)]
  (r : ∀ n, 𝒰 ⥤ 𝒰ₙ n) (s : ∀ n, 𝒯 ⥤ 𝒯ₙ n)
  {hnInv : ∀ n, 𝒰ₙ n ⥤ 𝒯ₙ n} {hnDir : ∀ n, 𝒯ₙ n ⥤ 𝒰ₙ n} (hnAdj : ∀ n, hnInv n ⊣ hnDir n)
  (α : ∀ n, r n ⋙ hnInv n ≅ hInv ⋙ s n)

/-- The direct-image square of degree `n`, `(h_* -)|_n ≅ h_{n,*}(-|_n)`, as the mate of the
inverse-image square `(h⁻¹ -)|_n ≅ h_n⁻¹(-|_n)`, when that mate is invertible. -/
def degreeDirectImageIso (n : ι) [IsIso (mateEquiv hAdj (hnAdj n) (α n).hom)] :
    hDir ⋙ r n ≅ s n ⋙ hnDir n :=
  asIso (mateEquiv hAdj (hnAdj n) (α n).hom)

omit [Abelian 𝒰] [Abelian 𝒯] [HasInjectiveResolutions 𝒰] [HasInjectiveResolutions 𝒯]
  [∀ n, Abelian (𝒰ₙ n)] [∀ n, Abelian (𝒯ₙ n)] [∀ n, HasInjectiveResolutions (𝒯ₙ n)] in
include hAdj in
/-- **The unit of `h` is invertible as soon as it is in every degree**: if the restrictions to
the degrees jointly reflect isomorphisms, the inverse-image squares of the degrees are invertible
with invertible mates (Stacks 0D96), and the unit of `h_n` is invertible at `G|_n` for every `n`,
then `G ⟶ h_* h⁻¹ G` is an isomorphism. The restriction of the unit of `h` to degree `n` is the
unit of `h_n` up to the two squares. -/
theorem isIso_unit_app_of_degreewise
    (hcons : ∀ {X Y : 𝒰} (f : X ⟶ Y), (∀ n, IsIso ((r n).map f)) → IsIso f)
    [∀ n, IsIso (mateEquiv hAdj (hnAdj n) (α n).hom)] (G : 𝒰)
    (hu : ∀ n, IsIso ((hnAdj n).unit.app ((r n).obj G))) :
    IsIso (hAdj.unit.app G) := by
  refine hcons _ fun n ↦ ?_
  have : IsIso ((mateEquiv hAdj (hnAdj n) (α n).hom).app (hInv.obj G)) :=
    NatIso.isIso_app_of_isIso (mateEquiv hAdj (hnAdj n) (α n).hom) (hInv.obj G)
  have : IsIso ((r n).map (hAdj.unit.app G) ≫
      (mateEquiv hAdj (hnAdj n) (α n).hom).app (hInv.obj G)) := by
    rw [unit_mateEquiv hAdj (hnAdj n) (α n).hom G]
    exact IsIso.comp_isIso' (hu n) inferInstance
  exact IsIso.of_isIso_comp_right _ ((mateEquiv hAdj (hnAdj n) (α n).hom).app (hInv.obj G))

variable [hDir.Additive] [∀ n, (hnDir n).Additive] [∀ n, (r n).Additive]
  [∀ n, (r n).PreservesHomology] [∀ n, (s n).Additive] [∀ n, PreservesFiniteLimits (s n)]
  [∀ n, PreservesFiniteColimits (s n)] [∀ n, (s n).PreservesInjectiveObjects]

omit [HasInjectiveResolutions 𝒰] in
include hAdj in
/-- **The higher direct images of `h` vanish at `M` as soon as those of every `h_n` vanish at
`M|_n`** (Stacks 0D97, read on a single object): restriction to a degree is exact and the
restriction on the source preserves injective objects, so `(R^q h_* M)|_n = R^q h_{n,*}(M|_n)`
through the direct-image square of degree `n`, and the restrictions jointly reflect zero
objects. -/
theorem isZero_rightDerived_of_degreewise
    (hcons : ∀ {X Y : 𝒰} (f : X ⟶ Y), (∀ n, IsIso ((r n).map f)) → IsIso f)
    [∀ n, IsIso (mateEquiv hAdj (hnAdj n) (α n).hom)] (M : 𝒯) (q : ℕ)
    (hz : ∀ n, IsZero (((hnDir n).rightDerived q).obj ((s n).obj M))) :
    IsZero ((hDir.rightDerived q).obj M) := by
  have hn : ∀ n, IsZero ((r n).obj ((hDir.rightDerived q).obj M)) := fun n ↦
    (hz n).of_iso ((Functor.rightDerivedIsoOfSquare (s n) hDir (hnDir n) (r n)
      (degreeDirectImageIso hAdj r s hnAdj α n) q).app M)
  let Z : 𝒰 := (hDir.rightDerived q).obj M
  have : IsIso (0 : Z ⟶ Z) :=
    hcons _ fun n ↦ ⟨⟨0, (hn n).eq_of_src _ _, (hn n).eq_of_src _ _⟩⟩
  rw [IsZero.iff_id_eq_zero, ← IsIso.inv_hom_id (0 : Z ⟶ Z), comp_zero]

end Degreewise

/-- The direct images around a commutative square: `h₋₁,* a'_* ≅ a_* h_*`, the conjugate of the
square `h⁻¹ a⁻¹ ≅ a'⁻¹ h₋₁⁻¹` of inverse images. -/
def comparisonSquareDirectImageIso : fDir ⋙ bDir ≅ hDir ⋙ aDir :=
  conjugateIsoEquiv (bAdj.comp fAdj) (aAdj.comp hAdj) e

include aAdj hAdj fAdj bAdj e

omit [Abelian 𝒳] [Abelian 𝒰] [Abelian 𝒴] [Abelian 𝒯] [HasInjectiveResolutions 𝒰]
  [HasInjectiveResolutions 𝒴] [HasInjectiveResolutions 𝒯] in
/-- **`F ⟶ a_*a⁻¹F` is an isomorphism** when the units of `h`, of `a'` at `h₋₁⁻¹F` and of `h₋₁` at
`F` are: the unit of the composite `h⁻¹ a⁻¹ ⊣ a_* h_*` is that of `a'⁻¹ h₋₁⁻¹ ⊣ h₋₁,* a'_*`
transported along the square. -/
theorem isIso_unit_app_of_comparisonSquare (F : 𝒳) (hUnitH : IsIso (hAdj.unit.app (aInv.obj F)))
    (hUnitF : IsIso (fAdj.unit.app (bInv.obj F))) (hUnitB : IsIso (bAdj.unit.app F)) :
    IsIso (aAdj.unit.app F) := by
  have : IsIso ((bAdj.comp fAdj).unit.app F) := by
    rw [comp_unit_app]
    infer_instance
  have : IsIso ((conjugateEquiv (bAdj.comp fAdj) (aAdj.comp hAdj) e.hom).app
      ((bInv ⋙ fInv).obj F)) :=
    ((comparisonSquareDirectImageIso aAdj hAdj fAdj bAdj e).app _).isIso_hom
  have : IsIso ((aAdj.comp hAdj).unit.app F ≫ (hDir ⋙ aDir).map (e.hom.app F)) := by
    rw [← unit_conjugateEquiv (bAdj.comp fAdj) (aAdj.comp hAdj) e.hom F]
    infer_instance
  have h : IsIso ((aAdj.comp hAdj).unit.app F) :=
    IsIso.of_isIso_comp_right _ ((hDir ⋙ aDir).map (e.hom.app F))
  rw [comp_unit_app] at h
  exact IsIso.of_isIso_comp_right _ (aDir.map (hAdj.unit.app (aInv.obj F)))

variable [aDir.Additive] [hDir.Additive] [fDir.Additive] [bDir.Additive]
  [hInv.PreservesMonomorphisms] [fInv.PreservesMonomorphisms]

/-- **`R^q a_*(a⁻¹F) = 0` for `q > 0`**, the computation
`Ra_*a⁻¹F = Ra_*Rh_*M = Rh₋₁,*Ra'_*M = Rh₋₁,*h₋₁⁻¹F` with `M = h⁻¹a⁻¹F = a'⁻¹h₋₁⁻¹F`, given that
the unit of `h` is invertible at `a⁻¹F`, that `M` is right acyclic for `h_*` and for `a'_*`, that
the unit of `a'` is invertible at `h₋₁⁻¹F` and that `h₋₁⁻¹F` is right acyclic for `h₋₁,*`. The
direct images `h_*`, `a'_*` preserve injective objects, being right adjoint to functors
preserving monomorphisms. -/
theorem isZero_rightDerived_of_comparisonSquare (F : 𝒳)
    (hUnitH : IsIso (hAdj.unit.app (aInv.obj F)))
    (hVanH : ∀ q : ℕ, 0 < q → IsZero ((hDir.rightDerived q).obj (fInv.obj (bInv.obj F))))
    (hUnitF : IsIso (fAdj.unit.app (bInv.obj F)))
    (hVanF : ∀ q : ℕ, 0 < q → IsZero ((fDir.rightDerived q).obj (fInv.obj (bInv.obj F))))
    (hVanB : ∀ q : ℕ, 0 < q → IsZero ((bDir.rightDerived q).obj (bInv.obj F)))
    (q : ℕ) (hq : 0 < q) :
    IsZero ((aDir.rightDerived q).obj (aInv.obj F)) := by
  have : PreservesFiniteLimits hDir := by
    have : PreservesLimitsOfSize.{0, 0} hDir := hAdj.rightAdjoint_preservesLimits
    exact PreservesLimitsOfSize.preservesFiniteLimits _
  have : PreservesFiniteLimits fDir := by
    have : PreservesLimitsOfSize.{0, 0} fDir := fAdj.rightAdjoint_preservesLimits
    exact PreservesLimitsOfSize.preservesFiniteLimits _
  have : hDir.PreservesInjectiveObjects :=
    Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms hAdj
  have : fDir.PreservesInjectiveObjects :=
    Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms fAdj
  let M := fInv.obj (bInv.obj F)
  have eG : aInv.obj F ≅ hDir.obj M :=
    asIso (hAdj.unit.app (aInv.obj F)) ≪≫ hDir.mapIso (e.app F)
  exact (hVanB q hq).of_iso ((aDir.rightDerived q).mapIso eG ≪≫
    (Stacks.RightDerivedComp.objIso hDir (injectiveResolution M) hVanH aDir q).symm ≪≫
    (Functor.rightDerivedIsoOfNatIso
      (comparisonSquareDirectImageIso aAdj hAdj fAdj bAdj e).symm q).app M ≪≫
    Stacks.RightDerivedComp.objIso fDir (injectiveResolution M) hVanF bDir q ≪≫
    (bDir.rightDerived q).mapIso (asIso (fAdj.unit.app (bInv.obj F))).symm)

section Derived

attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

variable [HasDerivedCategory 𝒳] [HasDerivedCategory 𝒰] [EnoughInjectives 𝒰] [aInv.Additive]
  [PreservesFiniteLimits aInv] [PreservesFiniteColimits aInv]

/-- **The derived unit `K ⟶ Ra_*(a⁻¹K)` is invertible on `D⁺(𝒳)`** for a commutative square of
comparison morphisms whose three other sides satisfy the hypotheses of
`isIso_unit_app_of_comparisonSquare` and `isZero_rightDerived_of_comparisonSquare` on every
object: by Leray's acyclicity lemma (Stacks 015E). This is the shape of Stacks 0DH7 and of
Stacks 09XS. -/
theorem isIso_derivedPlusAdjunction_unit_app_of_comparisonSquare
    (hUnitH : ∀ F, IsIso (hAdj.unit.app (aInv.obj F)))
    (hVanH : ∀ F (q : ℕ), 0 < q → IsZero ((hDir.rightDerived q).obj (fInv.obj (bInv.obj F))))
    (hUnitF : ∀ F, IsIso (fAdj.unit.app (bInv.obj F)))
    (hVanF : ∀ F (q : ℕ), 0 < q → IsZero ((fDir.rightDerived q).obj (fInv.obj (bInv.obj F))))
    (hUnitB : ∀ F, IsIso (bAdj.unit.app F))
    (hVanB : ∀ F (q : ℕ), 0 < q → IsZero ((bDir.rightDerived q).obj (bInv.obj F)))
    (K : DerivedCategory.Plus 𝒳) :
    IsIso ((Stacks.ComparingTopologies.derivedPlusAdjunction aAdj).unit.app K) :=
  isIso_derivedPlusAdjunction_unit_app_of_isZero_rightDerived aAdj
    (fun F ↦ isIso_unit_app_of_comparisonSquare aAdj hAdj fAdj bAdj e F (hUnitH F) (hUnitF F)
      (hUnitB F))
    (fun F q hq ↦ isZero_rightDerived_of_comparisonSquare aAdj hAdj fAdj bAdj e F (hUnitH F)
      (hVanH F) (hUnitF F) (hVanF F) (hVanB F) q hq) K

variable {𝒜 : Type*} [Category* 𝒜] [Abelian 𝒜] [HasDerivedCategory 𝒜] [EnoughInjectives 𝒳]
  (ΓX : 𝒳 ⥤ 𝒜) (ΓU : 𝒰 ⥤ 𝒜) [ΓX.Additive] [ΓU.Additive]
  [PreservesFiniteLimits ΓX] [aDir.PreservesInjectiveObjects] (eΓ : aDir ⋙ ΓX ≅ ΓU)

/-- **`RΓ(𝒳, K) ⟶ RΓ(𝒰, a⁻¹K)` is an isomorphism on `D⁺(𝒳)`** for a commutative square of
comparison morphisms as in `isIso_derivedPlusAdjunction_unit_app_of_comparisonSquare` and global
sections functors with `Γ_𝒳 ∘ a_* = Γ_𝒰`: the map is `RΓ(𝒳, -)` of the derived unit followed by
the Leray factorization `RΓ(𝒰, -) = RΓ(𝒳, -) ∘ Ra_*` (Stacks 08J6). This is the shape of
Stacks 0DH8 and of Stacks 09XC. -/
theorem isIso_lerayPullback_app_of_comparisonSquare
    (hUnitH : ∀ F, IsIso (hAdj.unit.app (aInv.obj F)))
    (hVanH : ∀ F (q : ℕ), 0 < q → IsZero ((hDir.rightDerived q).obj (fInv.obj (bInv.obj F))))
    (hUnitF : ∀ F, IsIso (fAdj.unit.app (bInv.obj F)))
    (hVanF : ∀ F (q : ℕ), 0 < q → IsZero ((fDir.rightDerived q).obj (fInv.obj (bInv.obj F))))
    (hUnitB : ∀ F, IsIso (bAdj.unit.app F))
    (hVanB : ∀ F (q : ℕ), 0 < q → IsZero ((bDir.rightDerived q).obj (bInv.obj F)))
    (K : DerivedCategory.Plus 𝒳) :
    IsIso ((Stacks.LerayPullbackComparison.lerayPullback aAdj ΓX ΓU eΓ).app K) := by
  have : IsIso ((Stacks.LerayPullbackComparison.derivedUnit aAdj).app K) := by
    rw [Stacks.LerayPullbackComparison.derivedUnit_eq_derivedPlusAdjunction_unit]
    exact isIso_derivedPlusAdjunction_unit_app_of_comparisonSquare aAdj hAdj fAdj bAdj e hUnitH
      hVanH hUnitF hVanF hUnitB hVanB K
  exact Stacks.LerayPullbackComparison.isIso_lerayPullback_app _ _ _ _ K

/-- **`RΓ(𝒳, K) = RΓ(𝒰, a⁻¹K)`** on `D⁺(𝒳)`, naturally in `K`, for a commutative square of
comparison morphisms as in `isIso_lerayPullback_app_of_comparisonSquare`; the forward map is the
pullback on derived global sections. -/
def derivedGlobalSectionsIsoOfComparisonSquare
    (hUnitH : ∀ F, IsIso (hAdj.unit.app (aInv.obj F)))
    (hVanH : ∀ F (q : ℕ), 0 < q → IsZero ((hDir.rightDerived q).obj (fInv.obj (bInv.obj F))))
    (hUnitF : ∀ F, IsIso (fAdj.unit.app (bInv.obj F)))
    (hVanF : ∀ F (q : ℕ), 0 < q → IsZero ((fDir.rightDerived q).obj (fInv.obj (bInv.obj F))))
    (hUnitB : ∀ F, IsIso (bAdj.unit.app F))
    (hVanB : ∀ F (q : ℕ), 0 < q → IsZero ((bDir.rightDerived q).obj (bInv.obj F))) :
    ΓX.rightDerivedFunctorPlus ≅ aInv.mapDerivedCategoryPlus ⋙ ΓU.rightDerivedFunctorPlus :=
  have : ∀ K, IsIso ((Stacks.LerayPullbackComparison.lerayPullback aAdj ΓX ΓU eΓ).app K) :=
    isIso_lerayPullback_app_of_comparisonSquare aAdj hAdj fAdj bAdj e ΓX ΓU eΓ hUnitH hVanH
      hUnitF hVanF hUnitB hVanB
  have := NatIso.isIso_of_isIso_app (Stacks.LerayPullbackComparison.lerayPullback aAdj ΓX ΓU eΓ)
  asIso (Stacks.LerayPullbackComparison.lerayPullback aAdj ΓX ΓU eΓ)

end Derived

/-! ### The assembly from the degreewise comparisons -/

section DegreewiseDerived

attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

variable {ι : Type*} {𝒰ₙ 𝒯ₙ : ι → Type*} [∀ n, Category* (𝒰ₙ n)] [∀ n, Category* (𝒯ₙ n)]
  [∀ n, Abelian (𝒰ₙ n)] [∀ n, Abelian (𝒯ₙ n)] [∀ n, HasInjectiveResolutions (𝒯ₙ n)]
  (r : ∀ n, 𝒰 ⥤ 𝒰ₙ n) (s : ∀ n, 𝒯 ⥤ 𝒯ₙ n)
  {hnInv : ∀ n, 𝒰ₙ n ⥤ 𝒯ₙ n} {hnDir : ∀ n, 𝒯ₙ n ⥤ 𝒰ₙ n} (hnAdj : ∀ n, hnInv n ⊣ hnDir n)
  (α : ∀ n, r n ⋙ hnInv n ≅ hInv ⋙ s n)
  [∀ n, IsIso (mateEquiv hAdj (hnAdj n) (α n).hom)]
  [∀ n, (hnDir n).Additive] [∀ n, (r n).Additive]
  [∀ n, (r n).PreservesHomology] [∀ n, (s n).Additive] [∀ n, PreservesFiniteLimits (s n)]
  [∀ n, PreservesFiniteColimits (s n)] [∀ n, (s n).PreservesInjectiveObjects]
  (hcons : ∀ {X Y : 𝒰} (f : X ⟶ Y), (∀ n, IsIso ((r n).map f)) → IsIso f)
  (hAcycU : ∀ n (G : 𝒰ₙ n), IsIso ((hnAdj n).unit.app G) ∧
    ∀ q : ℕ, 0 < q → IsZero (((hnDir n).rightDerived q).obj ((hnInv n).obj G)))
  (hAcycX : ∀ F : 𝒳, IsIso (bAdj.unit.app F) ∧
    ∀ q : ℕ, 0 < q → IsZero ((bDir.rightDerived q).obj (bInv.obj F)))
  (hDescent : ∀ N : 𝒴, IsIso (fAdj.unit.app N) ∧
    ∀ q : ℕ, 0 < q → IsZero ((fDir.rightDerived q).obj (fInv.obj N)))

omit [Abelian 𝒳] [Abelian 𝒰] [Abelian 𝒴] [Abelian 𝒯] [HasInjectiveResolutions 𝒰]
  [HasInjectiveResolutions 𝒴] [HasInjectiveResolutions 𝒯] [aDir.Additive] [hDir.Additive]
  [fDir.Additive] [bDir.Additive] [hInv.PreservesMonomorphisms] [fInv.PreservesMonomorphisms]
  [∀ n, (r n).Additive] [∀ n, (r n).PreservesHomology] [∀ n, (s n).Additive]
  [∀ n, PreservesFiniteLimits (s n)] [∀ n, PreservesFiniteColimits (s n)]
  [∀ n, (s n).PreservesInjectiveObjects] [Category 𝒴] aAdj fAdj bAdj e in
include r s hnAdj α hcons hAcycU in
/-- The unit of `h` is invertible at every `a⁻¹F`, from the degreewise units. -/
theorem isIso_unit_app_inverseImage_of_degreewise (F : 𝒳) :
    IsIso (hAdj.unit.app (aInv.obj F)) :=
  isIso_unit_app_of_degreewise hAdj r s hnAdj α hcons _ fun n ↦ (hAcycU n _).1

omit [Abelian 𝒳] [Abelian 𝒴] [HasInjectiveResolutions 𝒰] [HasInjectiveResolutions 𝒴]
  [aDir.Additive] [fDir.Additive] [bDir.Additive] [hInv.PreservesMonomorphisms]
  [fInv.PreservesMonomorphisms] aAdj fAdj bAdj in
include r s hnAdj α hcons hAcycU in
/-- `M = a'⁻¹h₋₁⁻¹F` is right acyclic for `h_*`: its restriction to degree `n` is
`h_n⁻¹((a⁻¹F)|_n)` by the square and the inverse-image square of degree `n`, at which the higher
direct images of `h_n` vanish. -/
theorem isZero_rightDerived_inverseImage_of_degreewise (F : 𝒳) (q : ℕ) (hq : 0 < q) :
    IsZero ((hDir.rightDerived q).obj (fInv.obj (bInv.obj F))) :=
  isZero_rightDerived_of_degreewise hAdj r s hnAdj α hcons _ q fun n ↦
    ((hAcycU n ((r n).obj (aInv.obj F))).2 q hq).of_iso
      ((hnDir n).rightDerived q |>.mapIso ((s n).mapIso (e.app F).symm ≪≫ ((α n).app _).symm))

variable [HasDerivedCategory 𝒳] [HasDerivedCategory 𝒰] [EnoughInjectives 𝒰] [aInv.Additive]
  [PreservesFiniteLimits aInv] [PreservesFiniteColimits aInv]

include r s hnAdj α hcons hAcycU hAcycX hDescent in
/-- **The shape of Stacks 0DH7.** Given the commutative square `h⁻¹a⁻¹ ≅ a'⁻¹h₋₁⁻¹` (Stacks 0DH5),
the degreewise description of `h` by comparisons `h_n` (Stacks 0D96, 0D97), the statement of
Stacks 0DGG on single objects for `h₋₁` and for every `h_n`, and the statement of Stacks 0D8N /
0DA8 on single objects for `a'`, the map `K ⟶ Ra_*(a⁻¹K)` is an isomorphism for every `K` of
`D⁺(𝒳)`. -/
theorem isIso_derivedPlusAdjunction_unit_app_of_degreewise (K : DerivedCategory.Plus 𝒳) :
    IsIso ((Stacks.ComparingTopologies.derivedPlusAdjunction aAdj).unit.app K) :=
  isIso_derivedPlusAdjunction_unit_app_of_comparisonSquare aAdj hAdj fAdj bAdj e
    (isIso_unit_app_inverseImage_of_degreewise hAdj r s hnAdj α hcons hAcycU)
    (isZero_rightDerived_inverseImage_of_degreewise hAdj e r s hnAdj α hcons hAcycU)
    (fun _ ↦ (hDescent _).1) (fun _ ↦ (hDescent _).2) (fun F ↦ (hAcycX F).1)
    (fun F ↦ (hAcycX F).2) K

variable {𝒜 : Type*} [Category* 𝒜] [Abelian 𝒜] [HasDerivedCategory 𝒜] [EnoughInjectives 𝒳]
  (ΓX : 𝒳 ⥤ 𝒜) (ΓU : 𝒰 ⥤ 𝒜) [ΓX.Additive] [ΓU.Additive]
  [PreservesFiniteLimits ΓX] [aDir.PreservesInjectiveObjects] (eΓ : aDir ⋙ ΓX ≅ ΓU)

/-- **The shape of Stacks 0DH8.** Under the hypotheses of
`isIso_derivedPlusAdjunction_unit_app_of_degreewise` and for global sections functors with
`Γ_𝒳 ∘ a_* = Γ_𝒰`, `RΓ(𝒳, K) = RΓ(𝒰, a⁻¹K)` naturally in `K` of `D⁺(𝒳)`; the forward map is the
pullback on derived global sections, through the factorization of Stacks 08J6. -/
def derivedGlobalSectionsIsoOfDegreewise :
    ΓX.rightDerivedFunctorPlus ≅ aInv.mapDerivedCategoryPlus ⋙ ΓU.rightDerivedFunctorPlus :=
  derivedGlobalSectionsIsoOfComparisonSquare aAdj hAdj fAdj bAdj e ΓX ΓU eΓ
    (isIso_unit_app_inverseImage_of_degreewise hAdj r s hnAdj α hcons hAcycU)
    (isZero_rightDerived_inverseImage_of_degreewise hAdj e r s hnAdj α hcons hAcycU)
    (fun _ ↦ (hDescent _).1) (fun _ ↦ (hDescent _).2) (fun F ↦ (hAcycX F).1)
    (fun F ↦ (hAcycX F).2)

end DegreewiseDerived

end CategoryTheory.Adjunction

end
