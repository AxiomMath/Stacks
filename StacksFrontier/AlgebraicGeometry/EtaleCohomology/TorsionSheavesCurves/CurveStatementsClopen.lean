module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.CoverTriangle
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.CurveStatementsFiniteDirectImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.CurveStatementsShortExactConstructible
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The eight statements of Situation 0A52 along isomorphisms and open and closed decompositions

The proof of Theorem 03SC repeatedly says "since `X` is a disjoint union of ..., we may assume
...". This file supplies the formal steps behind that phrase for the bundle
`Stacks.EtaleCohomology.CurveStatements`: the statements hold for a zero sheaf, they are invariant
under isomorphism, they pass from a sheaf on an open and closed subscheme to its extension by
zero, and they hold for a sheaf as soon as they hold for its restrictions to the two halves of a
decomposition of the scheme into two disjoint open subschemes.

## Main results

* `Stacks.EtaleCohomology.CurveStatements.of_isZero`: the statements hold for a zero sheaf.
* `Stacks.EtaleCohomology.CurveStatements.of_iso`: they are invariant under isomorphism.
* `Stacks.EtaleCohomology.CurveStatements.extensionByZero_of_isCompl`: for a decomposition
  `X = U ⊔ V` into disjoint opens and `F` killed by a prime with `F|_V` constructible, they pass
  from `F|_V` to `j_{V!} F|_V`, which is the direct image along the closed immersion `V ⟶ X`, so
  that Lemma 0A5D applies.
* `Stacks.EtaleCohomology.CurveStatements.of_isCompl`: for such a decomposition, they hold for
  `F` once they hold for `F|_U` and `F|_V`.
* `Stacks.EtaleCohomology.CurveStatements.of_finite_isCompl_cover`: the same for a finite
  decomposition into pairwise disjoint open and closed subschemes.
* `Stacks.EtaleCohomology.curveStatements_of_finite`: they hold for every sheaf on a finite
  scheme locally of finite type over a separably closed field.

## Implementation notes

The coefficients are `AddCommGrpCat.{u + 1}` and the `Ext`-universe is `u + 1`, the universes of
Lemmas 0A5C and 0A5D in this library.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open ZeroObject

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] hasExt_sheaf_smallEtale_succ

variable {k : Type u} [Field k] {X : Scheme.{u}} (π : X ⟶ Spec (.of k))

/-- **The eight statements hold for a zero sheaf**: every cohomology group vanishes and every
restriction map is a map between zero groups. -/
theorem CurveStatements.of_isZero {F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (hF : IsZero F) : CurveStatements.{u, 0, u + 1} π F where
  vanishing q _ := subsingleton_sheafH_of_isZero hF q
  affineVanishing _ q _ := subsingleton_sheafH_of_isZero hF q
  primePowerVanishing _ _ _ _ q _ := subsingleton_sheafH_of_isZero hF q
  finite_of_isPrimeToCharacteristicTorsion _ _ _ _ _ _ q :=
    have := subsingleton_sheafH_of_isZero hF q
    Finite.of_subsingleton
  finite_of_isProper _ _ _ _ _ _ q :=
    have := subsingleton_sheafH_of_isZero hF q
    Finite.of_subsingleton
  bijective_of_isPrimeToCharacteristicTorsion _ _ _ _ _ _ _ q :=
    bijective_etaleCohomologyRestrictionMap_of_isZero _ hF q
  bijective_of_isProper _ _ _ _ _ _ _ q :=
    bijective_etaleCohomologyRestrictionMap_of_isZero _ hF q
  surjective U _ := (bijective_etaleCohomologyRestrictionMap_of_isZero U.ι hF 2).2

/-- The images of the two halves of a decomposition into disjoint opens are disjoint. -/
private theorem disjoint_range_ι_of_isCompl {U V : X.Opens} (hUV : IsCompl U V) :
    Disjoint (Set.range U.ι.base) (Set.range V.ι.base) := by
  rw [Scheme.Opens.range_ι, Scheme.Opens.range_ι]
  exact TopologicalSpace.Opens.coe_disjoint.2 hUV.disjoint

/-- The counit `j_! j^{-1} F ⟶ F` of an open `W` becomes invertible after restriction to any
smaller open `Z`. -/
private theorem isIso_inverseImage_map_counit_of_le {Z W : X.Opens} (hle : Z ≤ W)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    IsIso ((etaleAbelianInverseImage.{u, 0} Z.ι).map
      ((extensionByZeroAdj.{u, 0} W.ι).counit.app F)) :=
  isIso_etaleAbelianInverseImage_map_counit_of_factors.{u, 0} Z.ι W.ι (X.homOfLE hle)
    (X.homOfLE_ι hle) F

variable {π} [IsNoetherian X]

/-- An open subscheme of a Noetherian scheme is Noetherian. -/
private instance isNoetherian_opens (U : X.Opens) : IsNoetherian (U : Scheme.{u}) :=
  have : TopologicalSpace.NoetherianSpace (U : Scheme.{u}) :=
    TopologicalSpace.NoetherianSpace.set (U : Set X)
  ⟨⟩

/-- A short complex `0 ⟶ G ⟶ F ⟶ 0`-shaped: zero first term and invertible second map is short
exact. -/
private theorem shortExact_of_isZero_of_isIso {C : Type*} [Category C] [Abelian C]
    (S : ShortComplex C) (h₁ : IsZero S.X₁) [IsIso S.g] : S.ShortExact where
  exact := (S.exact_iff_mono (h₁.eq_of_src _ _)).2 inferInstance
  mono_f := ⟨fun _ _ _ ↦ h₁.eq_of_tgt _ _⟩

/-- The eight statements pass to the middle term of a short exact sequence whose first term is
zero. -/
theorem CurveStatements.of_shortExact_of_isZero
    {S : ShortComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})} (hS : S.ShortExact)
    (h₁ : IsZero S.X₁) (h₃ : CurveStatements.{u, 0, u + 1} π S.X₃) :
    CurveStatements.{u, 0, u + 1} π S.X₂ :=
  CurveStatements.of_shortExact hS (CurveStatements.of_isZero π h₁) h₃

/-- **The eight statements are invariant under isomorphism.** -/
theorem CurveStatements.of_iso {F G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (e : F ≅ G) (h : CurveStatements.{u, 0, u + 1} π F) : CurveStatements.{u, 0, u + 1} π G :=
  CurveStatements.of_shortExact_of_isZero
    (shortExact_of_isZero_of_isIso (ShortComplex.mk (0 : 0 ⟶ G) e.inv (zero_comp)) (isZero_zero _))
    (isZero_zero _) h

/-- Being killed by `ℓ` is invariant under isomorphism. -/
theorem nsmul_id_eq_zero_of_iso {C : Type*} [Category C] [Preadditive C] {F G : C} (e : F ≅ G)
    {ℓ : ℕ} (h : ℓ • 𝟙 F = 0) : ℓ • 𝟙 G = 0 := by
  calc ℓ • 𝟙 G = e.inv ≫ (ℓ • 𝟙 F) ≫ e.hom := by simp
    _ = 0 := by rw [h]; simp

/-- Constructibility, read on Mathlib's small étale site, with respect to every ambient big étale
site containing the scheme: the form in which statements (4) and (5) of
`Stacks.EtaleCohomology.CurveStatements` quantify it. -/
def IsConstructibleOnEveryBigSite {S : Scheme.{u}}
    (F : Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}) : Prop :=
  ∀ (B : BigEtaleSite.{u}) (hS : B.Contains S)
    [∀ (T T' : B.Scheme) (f : T' ⟶ T),
      ((AlgebraicGeometry.smallEtaleBaseChange B f).sheafPushforwardContinuous
        AddCommGrpCat.{u + 1}
        (AlgebraicGeometry.SmallEtale.topology B T.obj T.property)
        (AlgebraicGeometry.SmallEtale.topology B T'.obj T'.property)).IsRightAdjoint]
    [∀ (T : B.Scheme) (V : AlgebraicGeometry.SmallEtale B T.obj T.property),
      HasWeakSheafify
        ((AlgebraicGeometry.SmallEtale.topology B T.obj T.property).over V)
        AddCommGrpCat.{u + 1}],
    IsConstructibleEtaleAbelianSheaf.{u, 0} B S hS F

/-- Constructibility on every big étale site passes to subsheaves on a Noetherian scheme
(Proposition 09BH (2)). -/
theorem IsConstructibleOnEveryBigSite.of_mono {S : Scheme.{u}} [IsNoetherian S]
    {F G : Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}} (i : G ⟶ F) [Mono i]
    (hF : IsConstructibleOnEveryBigSite F) : IsConstructibleOnEveryBigSite G :=
  fun B hS _ _ ↦ isConstructibleEtaleAbelianSheaf_of_mono B hS i (hF B hS)

/-- Constructibility on every big étale site is invariant under isomorphism. -/
theorem IsConstructibleOnEveryBigSite.of_iso {S : Scheme.{u}} [IsNoetherian S]
    {F G : Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}} (e : F ≅ G)
    (hF : IsConstructibleOnEveryBigSite F) : IsConstructibleOnEveryBigSite G :=
  hF.of_mono e.inv

/-- An additive functor carries a sheaf killed by `ℓ` to a sheaf killed by `ℓ`. -/
theorem nsmul_id_eq_zero_map {C D : Type*} [Category C] [Category D] [Preadditive C]
    [Preadditive D] (Φ : C ⥤ D) [Φ.Additive] {F : C} {ℓ : ℕ} (h : ℓ • 𝟙 F = 0) :
    ℓ • 𝟙 (Φ.obj F) = 0 := by
  simpa using congrArg Φ.map h

section Clopen

variable {U V : X.Opens} (hUV : IsCompl U V)

omit [AlgebraicGeometry.IsNoetherian X] in
include hUV in
/-- The two halves of a decomposition into disjoint opens have complementary images. -/
theorem range_ι_eq_compl_of_isCompl : Set.range V.ι.base = (Set.range U.ι.base)ᶜ := by
  rw [Scheme.Opens.range_ι, Scheme.Opens.range_ι]
  have hd : Disjoint (V : Set X) U := by
    rw [Set.disjoint_iff_inter_eq_empty, ← TopologicalSpace.Opens.coe_inf, inf_comm,
      hUV.inf_eq_bot, TopologicalSpace.Opens.coe_bot]
  have hc : Codisjoint (V : Set X) U := by
    rw [codisjoint_iff]
    show ((V ⊔ U : X.Opens) : Set X) = Set.univ
    rw [sup_comm, hUV.sup_eq_top]
    rfl
  exact IsCompl.eq_compl ⟨hd, hc⟩

omit [AlgebraicGeometry.IsNoetherian X] in
include hUV in
/-- An open subscheme which has an open complement is a closed immersion. -/
theorem isClosedImmersion_ι_of_isCompl : IsClosedImmersion U.ι := by
  refine IsClosedImmersion.of_isPreimmersion _ ?_
  rw [← compl_compl (Set.range U.ι.base), ← range_ι_eq_compl_of_isCompl hUV]
  exact V.ι.isOpenEmbedding.isOpen_range.isClosed_compl

variable {ℓ : ℕ} (hℓ : ℓ.Prime)

omit [AlgebraicGeometry.IsNoetherian X] in
include hUV hℓ in
/-- **The eight statements on the closed half.** For an open `U` with open complement, a
constructible sheaf `G` on `U` killed by a prime satisfying the eight statements gives the
statements for its direct image along the closed immersion `U ⟶ X` (Lemma 0A5D). -/
theorem CurveStatements.directImage_ι_of_isCompl
    {G : Sheaf (U : Scheme.{u}).smallEtaleTopology AddCommGrpCat.{u + 1}} (hℓG : ℓ • 𝟙 G = 0)
    (hc : IsConstructibleOnEveryBigSite G) (h : CurveStatements.{u, 0, u + 1} (U.ι ≫ π) G) :
    CurveStatements.{u, 0, u + 1} π ((etaleAbelianDirectImage.{u, 0} U.ι).obj G) := by
  have := isClosedImmersion_ι_of_isCompl hUV
  exact CurveStatements.directImage_of_nsmul_eq_zero π U.ι hℓ hℓG hc h

include hUV hℓ in
/-- **Extension by zero from the open half.** For `X = U ⊔ V` with `U`, `V` disjoint opens and
`F` a sheaf on `X_étale` killed by a prime whose restriction to `V` is constructible: if
statements (1) -- (8) of Situation 0A52 hold for `F|_V`, they hold for `j_{V!} F|_V`. Indeed
`j_{V!} F|_V` vanishes on `U`, so it is the direct image of `F|_V` along the closed immersion
`V ⟶ X`. -/
theorem CurveStatements.extensionByZero_of_isCompl
    {F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}} (hℓF : ℓ • 𝟙 F = 0)
    (hcV : IsConstructibleOnEveryBigSite ((etaleAbelianInverseImage.{u, 0} V.ι).obj F))
    (hV : CurveStatements.{u, 0, u + 1} (V.ι ≫ π)
      ((etaleAbelianInverseImage.{u, 0} V.ι).obj F)) :
    CurveStatements.{u, 0, u + 1} π
      ((extensionByZero.{u, 0} V.ι).obj ((etaleRestriction.{u, 0} V.ι).obj F)) := by
  have hVU : IsCompl V U := hUV.symm
  have := isClosedImmersion_ι_of_isCompl hVU
  set H := (extensionByZero.{u, 0} V.ι).obj ((etaleRestriction.{u, 0} V.ι).obj F)
  obtain ⟨_, hS'⟩ := shortExact_extensionByZero_etaleAbelianDirectImage.{u, 0} V.ι U.ι
    (range_ι_eq_compl_of_isCompl hVU) H
  have hzero : IsZero ((etaleRestriction.{u, 0} U.ι).obj H) :=
    IsZero.of_iso (isZero_etaleAbelianInverseImage_extensionByZero_of_disjoint.{u, 0} U.ι V.ι
      (disjoint_range_ι_of_isCompl hUV) _)
      ((etaleAbelianInverseImageRestrictionIso.{u, 0} U.ι).app H).symm
  have e : (etaleAbelianInverseImage.{u, 0} V.ι).obj H ≅
      (etaleAbelianInverseImage.{u, 0} V.ι).obj F :=
    have := isIso_inverseImage_map_counit_of_le (le_refl V) F
    asIso ((etaleAbelianInverseImage.{u, 0} V.ι).map ((extensionByZeroAdj.{u, 0} V.ι).counit.app F))
  exact CurveStatements.of_shortExact_of_isZero hS'
    ((extensionByZero.{u, 0} U.ι).map_isZero hzero)
    (CurveStatements.directImage_ι_of_isCompl hVU hℓ
      (nsmul_id_eq_zero_of_iso e.symm (nsmul_id_eq_zero_map _ hℓF)) (hcV.of_iso e.symm)
      (hV.of_iso e.symm))

include hUV hℓ in
/-- **The eight statements for a sheaf from those on the closed half and its extension by zero
from the open half**, through `0 → j_{V!} F|_V → F → i_{U*} F|_U → 0` (Tag 095L), Lemma 0A5D for
the closed immersion `U ⟶ X`, and Lemma 0A5C. -/
theorem CurveStatements.of_isCompl_of_extensionByZero
    {F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}} (hℓF : ℓ • 𝟙 F = 0)
    (hcU : IsConstructibleOnEveryBigSite ((etaleAbelianInverseImage.{u, 0} U.ι).obj F))
    (hU : CurveStatements.{u, 0, u + 1} (U.ι ≫ π) ((etaleAbelianInverseImage.{u, 0} U.ι).obj F))
    (hV : CurveStatements.{u, 0, u + 1} π
      ((extensionByZero.{u, 0} V.ι).obj ((etaleRestriction.{u, 0} V.ι).obj F))) :
    CurveStatements.{u, 0, u + 1} π F := by
  have := isClosedImmersion_ι_of_isCompl hUV
  obtain ⟨_, hS⟩ := shortExact_extensionByZero_etaleAbelianDirectImage.{u, 0} U.ι V.ι
    (range_ι_eq_compl_of_isCompl hUV) F
  exact CurveStatements.of_shortExact hS hV
    (CurveStatements.directImage_ι_of_isCompl hUV hℓ (nsmul_id_eq_zero_map _ hℓF) hcU hU)

include hUV hℓ in
/-- **The eight statements for a sheaf from its two restrictions to an open and closed
decomposition.** Let `X = U ⊔ V` with `U`, `V` disjoint opens and `F` a sheaf on `X_étale`
killed by a prime `ℓ` whose restrictions to `U` and `V` are constructible. If statements
(1) -- (8) of Situation 0A52 hold for `F|_U` and `F|_V`, they hold for `F`. -/
theorem CurveStatements.of_isCompl {F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (hℓF : ℓ • 𝟙 F = 0)
    (hcU : IsConstructibleOnEveryBigSite ((etaleAbelianInverseImage.{u, 0} U.ι).obj F))
    (hcV : IsConstructibleOnEveryBigSite ((etaleAbelianInverseImage.{u, 0} V.ι).obj F))
    (hU : CurveStatements.{u, 0, u + 1} (U.ι ≫ π) ((etaleAbelianInverseImage.{u, 0} U.ι).obj F))
    (hV : CurveStatements.{u, 0, u + 1} (V.ι ≫ π)
      ((etaleAbelianInverseImage.{u, 0} V.ι).obj F)) :
    CurveStatements.{u, 0, u + 1} π F :=
  CurveStatements.of_isCompl_of_extensionByZero hUV hℓ hℓF hcU hU
    (CurveStatements.extensionByZero_of_isCompl hUV hℓ hℓF hcV hV)

end Clopen

section FiniteCover

variable {ℓ : ℕ} (hℓ : ℓ.Prime) {ι : Type u} [Finite ι] (Z W : ι → X.Opens)
  (hZW : ∀ i, IsCompl (Z i) (W i)) (hdisj : Pairwise fun i j ↦ Disjoint (Z i) (Z j))
  (hcov : ∀ x : X, ∃ i, x ∈ Z i)

include hℓ hZW hdisj hcov in
/-- **The eight statements for a sheaf from its restrictions to the pieces of a finite
decomposition into disjoint open and closed subschemes.** Let `X = ⨆ Z i` be a finite cover by
pairwise disjoint opens each having an open complement `W i`, and `F` a sheaf on `X_étale` killed
by a prime whose restrictions to the `Z i` are constructible. If statements (1) -- (8) of
Situation 0A52 hold for every `F|_{Z i}`, they hold for `F`.

The proof is an induction on the number of pieces on which `F` does not vanish: if there is none
`F` is zero, and otherwise `F` is cut along one such piece `Z i` by
`Stacks.EtaleCohomology.CurveStatements.of_isCompl_of_extensionByZero`, the remaining sheaf
`j_{W i!} F|_{W i}` vanishing on `Z i` and agreeing with `F` on every other piece. -/
theorem CurveStatements.of_finite_isCompl_cover :
    ∀ (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}), ℓ • 𝟙 F = 0 →
      (∀ i, IsConstructibleOnEveryBigSite ((etaleAbelianInverseImage.{u, 0} (Z i).ι).obj F)) →
      (∀ i, CurveStatements.{u, 0, u + 1} ((Z i).ι ≫ π)
        ((etaleAbelianInverseImage.{u, 0} (Z i).ι).obj F)) →
      CurveStatements.{u, 0, u + 1} π F := by
  classical
  have := Fintype.ofFinite ι
  suffices h : ∀ (n : ℕ) (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}),
      (Finset.univ.filter fun i ↦ ¬ IsZero ((etaleAbelianInverseImage.{u, 0} (Z i).ι).obj F)).card
        ≤ n → ℓ • 𝟙 F = 0 →
      (∀ i, IsConstructibleOnEveryBigSite ((etaleAbelianInverseImage.{u, 0} (Z i).ι).obj F)) →
      (∀ i, CurveStatements.{u, 0, u + 1} ((Z i).ι ≫ π)
        ((etaleAbelianInverseImage.{u, 0} (Z i).ι).obj F)) →
      CurveStatements.{u, 0, u + 1} π F from fun F ↦ h _ F le_rfl
  intro n
  induction n with
  | zero =>
    intro F hn _ _ _
    refine CurveStatements.of_isZero π ?_
    have hz : ∀ i, IsZero ((etaleAbelianInverseImage.{u, 0} (Z i).ι).obj F) := fun i ↦ by
      by_contra hi
      have : i ∈ Finset.univ.filter
          fun i ↦ ¬ IsZero ((etaleAbelianInverseImage.{u, 0} (Z i).ι).obj F) := by simp [hi]
      simp_all
    have : IsIso (0 : F ⟶ 0) := isIso_of_isIso_etaleAbelianInverseImage_family.{u, 0}
      (fun i ↦ (Z i).ι) (by
        refine Set.eq_univ_of_forall fun x ↦ ?_
        obtain ⟨i, hi⟩ := hcov x
        exact Set.mem_iUnion.2 ⟨i, by rw [Scheme.Opens.range_ι]; exact hi⟩)
      0 fun i ↦ ⟨⟨0, (hz i).eq_of_src _ _,
        ((etaleAbelianInverseImage.{u, 0} (Z i).ι).map_isZero (isZero_zero _)).eq_of_src _ _⟩⟩
    exact IsZero.of_iso (isZero_zero _) (asIso (0 : F ⟶ 0))
  | succ n ih =>
    intro F hn hℓF hc h
    by_cases hall : ∀ i, IsZero ((etaleAbelianInverseImage.{u, 0} (Z i).ι).obj F)
    · exact ih F (by simp [hall]) hℓF hc h
    push Not at hall
    obtain ⟨i₀, hi₀⟩ := hall
    set F' := (extensionByZero.{u, 0} (W i₀).ι).obj ((etaleRestriction.{u, 0} (W i₀).ι).obj F)
    -- on `Z i₀` the sheaf `F'` vanishes, on every other piece it is `F`
    have hzero : IsZero ((etaleAbelianInverseImage.{u, 0} (Z i₀).ι).obj F') :=
      isZero_etaleAbelianInverseImage_extensionByZero_of_disjoint.{u, 0} (Z i₀).ι (W i₀).ι
        (disjoint_range_ι_of_isCompl (hZW i₀)) _
    have hiso : ∀ i, i ≠ i₀ → IsIso ((etaleAbelianInverseImage.{u, 0} (Z i).ι).map
        ((extensionByZeroAdj.{u, 0} (W i₀).ι).counit.app F)) := fun i hi ↦ by
      have hle : Z i ≤ W i₀ := by
        intro x hx
        have hx' : x ∉ Z i₀ := fun h' ↦ (hdisj hi).le_bot ⟨hx, h'⟩
        have : x ∈ (Z i₀ ⊔ W i₀ : X.Opens) := by rw [(hZW i₀).sup_eq_top]; trivial
        exact this.resolve_left hx'
      exact isIso_inverseImage_map_counit_of_le hle F
    have e : ∀ i, i ≠ i₀ → ((etaleAbelianInverseImage.{u, 0} (Z i).ι).obj F' ≅
        (etaleAbelianInverseImage.{u, 0} (Z i).ι).obj F) := fun i hi ↦
      have := hiso i hi
      asIso ((etaleAbelianInverseImage.{u, 0} (Z i).ι).map
        ((extensionByZeroAdj.{u, 0} (W i₀).ι).counit.app F))
    have hcF' : ∀ i, IsConstructibleOnEveryBigSite
        ((etaleAbelianInverseImage.{u, 0} (Z i).ι).obj F') := fun i ↦ by
      by_cases hi : i = i₀
      · subst hi
        have : Mono (0 : (etaleAbelianInverseImage.{u, 0} (Z i).ι).obj F' ⟶
            (etaleAbelianInverseImage.{u, 0} (Z i).ι).obj F) := ⟨fun _ _ _ ↦ hzero.eq_of_tgt _ _⟩
        exact (hc i).of_mono 0
      · exact (hc i).of_iso (e i hi).symm
    refine CurveStatements.of_isCompl_of_extensionByZero (hZW i₀) hℓ hℓF (hc i₀) (h i₀) ?_
    refine ih F' ?_ (nsmul_id_eq_zero_map _ (nsmul_id_eq_zero_map _ hℓF)) hcF' fun i ↦ ?_
    · refine Nat.le_of_lt_succ (lt_of_lt_of_le (Finset.card_lt_card ?_) hn)
      refine ⟨fun i hi ↦ ?_, fun hsub ↦ ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
        by_cases h' : i = i₀
        · subst h'; exact absurd hzero hi
        · exact fun hF ↦ hi (IsZero.of_iso hF (e i h'))
      · have := hsub (show i₀ ∈ Finset.univ.filter fun i ↦
            ¬ IsZero ((etaleAbelianInverseImage.{u, 0} (Z i).ι).obj F) by simp [hi₀])
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at this
        exact this hzero
    · by_cases hi : i = i₀
      · subst hi; exact CurveStatements.of_isZero _ hzero
      · exact (h i).of_iso (e i hi).symm

end FiniteCover

section Finite

/-- **The eight statements hold for every sheaf on a finite scheme over a separably closed
field.** Such a scheme is the closed complement of the empty open subscheme, which is a finite
set of points, so the closed part of the comparison of Tag 0GJA is everything: its cohomology
vanishes in positive degrees (Tag 09AY), is finite in degree zero for a constructible sheaf, and
does not change under extension of the separably closed ground field (Tag 0A3I). This is the
case of the zero-dimensional components in Lemmas 0A5B and 03SG. -/
@[sga "4 XII 5.4" "(i), (ii), (iii)"]
theorem curveStatements_of_finite {k : Type u} [Field k] [IsSepClosed k] {X : Scheme.{u}}
    (π : X ⟶ Spec (.of k)) [LocallyOfFiniteType π] [QuasiCompact π] [Finite X]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    CurveStatements.{u, 0, u + 1} π F := by
  have : Finite (closedComplement (⊥ : X.Opens).ι) :=
    Finite.of_injective _ (closedComplementι (⊥ : X.Opens).ι).isClosedEmbedding.injective
  refine curveStatements_of_curveStatements_extensionByZero.{u, 0, u + 1} π
    (⊥ : X.Opens).ι F (CurveStatements.of_isZero π ((extensionByZero.{u, 0} _).map_isZero ?_))
  have : IsEmpty ((⊥ : X.Opens) : Scheme.{u}) := ⟨fun x ↦ x.2⟩
  exact isZero_of_forall_isZero_sections.{u, 0} _ fun V ↦
    isZero_sections_of_isEmpty.{u, 0} _ V
      ⟨fun x ↦ IsEmpty.false (α := ((⊥ : X.Opens) : Scheme.{u})) (V.hom.base x)⟩

end Finite

end Stacks.EtaleCohomology

end
