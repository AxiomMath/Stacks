module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.MapBijective
public import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorInjective
public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateModules.AffineCohomologyVanishingUnconditional
public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateModules.ZariskiInclusion
public import StacksFrontier.AlgebraicGeometry.AffineHigherDirectImage.Vanishing
public import StacksFrontier.AlgebraicGeometry.Size.EssentiallySmall
public import StacksFrontier.CategoryTheory.Abelian.RightDerivedPostcompose
public import StacksFrontier.CategoryTheory.Sites.Cocontinuous.LowerShriekExactness
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChangeOfTopology.BigSiteSheafCohomology
public import StacksFrontier.CategoryTheory.Sites.FunctorialInjectiveEmbeddings
public import StacksFrontier.Homology.DerivedIndexing.Basic

/-!
# Zariski and big-site cohomology of an adequate module agree

Let `S` be a scheme and let `𝓕` be an adequate `𝒪`-module on a chosen big `τ`-site
`(Sch/S)_τ` over `S`, for `τ` any of the five topologies. There is a canonical isomorphism

`H^q(S, 𝓕|_{S_Zar}) ≅ H^q((Sch/S)_τ, 𝓕)`

in every degree `q`. This is **[Stacks, Tag 06VM] (4)**.

The source deduces (4) from (3) — the vanishing `H^q(U, 𝓕) = 0` for `q > 0` and `U` affine over
`S` — "in exactly the same way as in the proof of [Stacks, Tag 03DW]". That deduction is carried
out here. First, (3) read on the affine opens of `S` kills the higher direct images `R^q g_* 𝓕`
along the morphism of sites `g : (Sch/S)_τ → S_Zar`, because `R^q g_* 𝓕` is the Zariski
sheafification of `V ↦ H^q(V, 𝓕)` and the affine opens form a basis. Second, global sections on
the big site are global sections on `S_Zar` of the restriction, so with the higher direct images
gone the Grothendieck edge isomorphism identifies the two derived-functor cohomologies; and, in
the `Ext` model of cohomology, the vanishing makes the canonical `Ext`-comparison bijective, by
dimension shifting against the exact left adjoint `g_!` of restriction.

## Main definitions

* `Stacks.Cohomology.AdjointExt.adjointExtMap` — for an adjunction `L ⊣ R` with `L` exact, the
  canonical map `Ext_C(X, R Y) → Ext_D(L X, Y)`: apply `L` to the extension and compose with the
  counit.
* `Stacks.Cohomology.AdjointExt.adjointExtComparisonMap` — the same map read through an
  identification `L X ≅ Z`, which is the shape a cohomology comparison takes.
* `Stacks.Adequate.BigSite.zariskiLowerShriek` and `Stacks.Adequate.BigSite.zariskiAdjunction` —
  the left adjoint `g_!` of restriction to the small Zariski site of `S`, and the adjunction.
* `Stacks.Adequate.BigSite.constantSheafZariskiIso` — `g_!` carries the constant abelian sheaf
  `ℤ` of `S_Zar` to the constant abelian sheaf `ℤ` of the big site.
* `Stacks.Adequate.BigSite.zariskiSheafHMap` — the canonical comparison
  `H^q(S, g_* 𝓖) → H^q((Sch/S)_τ, 𝓖)` of an abelian sheaf `𝓖` on the big site.
* `Stacks.Adequate.BigSite.AffineOpenAcyclicity` and
  `Stacks.Adequate.BigSite.AdequateAffineOpenAcyclicity` — the vanishing of positive-degree
  cohomology on the affine opens of `S`, for an abelian sheaf and for an adequate `𝒪`-module.

## Main results

* `Stacks.Adequate.BigSite.adequateAffineOpenAcyclicity` — (3) read on the affine opens of `S`.
* `Stacks.Adequate.BigSite.isZero_rightDerived_zariskiRestriction` and
  `Stacks.Adequate.BigSite.higherZariskiRestrictionVanishing` — the vanishing of the higher
  direct images `R^q g_* 𝓖` for `q > 0`, the step the source takes from [Stacks, Tag 03DW].
* `Stacks.Adequate.BigSite.adequateCohomologyIso` — **[Stacks, Tag 06VM] (4)**, cohomology being
  the right derived functor of global sections.
* `Stacks.Adequate.BigSite.bijective_zariskiSheafHMap` and
  `Stacks.Adequate.BigSite.zariskiSheafHEquiv` — the canonical `Ext`-comparison is bijective for
  an abelian sheaf acyclic on the affine opens of `S`, with
  `Stacks.Adequate.BigSite.zariskiSheafHEquiv_apply`,
  `Stacks.Adequate.BigSite.zariskiSheafHEquiv_naturality` and
  `Stacks.Adequate.BigSite.zariskiSheafHMap_mk₀` pinning it down as canonical.
* `Stacks.Adequate.BigSite.adequateSheafHEquiv` — (4) in the `Ext` model of cohomology.

## Implementation notes

*Why the comparison is not an instance of the general change-of-topology lemmas.* The inclusion
of the small Zariski site of `S` into a big site is continuous but not cocontinuous, so
restriction `g_*` is not right exact, and every comparison in
`StacksFrontier/CategoryTheory/Sites/Cohomology/` that transports `Ext` along a functor — including
`Stacks.Cohomology.BiggerSite.sheafCohomologyIso` and
`Stacks.Cohomology.BiggerSiteGlobal.sheafCohomologyIsoOfAcyclic` — needs that right exactness,
because it reads [Stacks, Tag 015Z] through derived functors. The argument used here needs only
that `g_!` is exact and that the *one* sheaf `𝓖` is `g_*`-acyclic.

*Typeclass hypotheses.* Sheafification and enough injectives for abelian sheaves on the big site
are the instances `Stacks.Adequate.BigSite.hasSheafify_addCommGrpCat` and
`Stacks.Adequate.BigSite.enoughInjectives_sheaf_addCommGrpCat`. Exactness of `g_!` is proved: the
inclusion of the small Zariski site is representably flat
(`AlgebraicGeometry.representablyFlat_opensBelowToOver`), hence preserves the finite limits that
`Stacks.Sites.LowerShriek.gShriek_preservesFiniteLimits` asks for. Only the `Ext` model carries
`HasExt.{w}` instance arguments, the universe of its `Ext`-groups, as Mathlib's
`CategoryTheory.Sheaf.H` does.

## References

* [Stacks Project, Tag 06VM](https://stacks.math.columbia.edu/tag/06VM)
* [Stacks Project, Tag 03DW](https://stacks.math.columbia.edu/tag/03DW)
* [Stacks Project, Tag 015Z](https://stacks.math.columbia.edu/tag/015Z)
* [Stacks Project, Tag 04BH](https://stacks.math.columbia.edu/tag/04BH)
* [Stacks Project, Tag 06VN](https://stacks.math.columbia.edu/tag/06VN)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open Opposite TopologicalSpace

universe w u u₁ u₂ v₁ v₂ w₁ w₂

/-! ### `Ext` across an adjunction with an exact left adjoint -/

namespace Stacks.Cohomology.AdjointExt

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
  [Abelian C] [Abelian D] [HasExt.{w₁} C] [HasExt.{w₂} D]
  {L : C ⥤ D} {R : D ⥤ C} [L.Additive] [R.Additive]
  [PreservesFiniteLimits L] [PreservesFiniteColimits L]

/-- **The canonical map `Ext_C(X, R Y) → Ext_D(L X, Y)` of an adjunction `L ⊣ R` with `L`
exact.** Apply the exact functor `L` to the extension class and compose with the counit of the
adjunction. In degree zero it is the hom-set bijection of the adjunction. -/
public def adjointExtMap (adj : L ⊣ R) (X : C) (Y : D) (n : ℕ) :
    Ext X (R.obj Y) n →+ Ext (L.obj X) Y n :=
  (Ext.postcomp (Ext.mk₀ (adj.counit.app Y)) (L.obj X) (add_zero n)).comp
    (L.mapExtAddHom X (R.obj Y) n)

omit [R.Additive] in
private lemma adjointExtMap_mk₀ (adj : L ⊣ R) (X : C) (Y : D) (f : X ⟶ R.obj Y) :
    adjointExtMap adj X Y 0 (Ext.mk₀ f) = Ext.mk₀ ((adj.homEquiv X Y).symm f) := by
  simp [adjointExtMap, Ext.mapExactFunctor_mk₀, Ext.mk₀_comp_mk₀,
    Adjunction.homEquiv_counit]

omit [R.Additive] in
private lemma adjointExtMap_naturality (adj : L ⊣ R) (X : C) {Y Z : D}
    (g : Y ⟶ Z) (n : ℕ) (x : Ext X (R.obj Y) n) :
    adjointExtMap adj X Z n (x.comp (Ext.mk₀ (R.map g)) (add_zero n)) =
      (adjointExtMap adj X Y n x).comp (Ext.mk₀ g) (add_zero n) := by
  show ((x.comp (Ext.mk₀ (R.map g)) (add_zero n)).mapExactFunctor L).comp
      (Ext.mk₀ (adj.counit.app Z)) (add_zero n) =
    ((x.mapExactFunctor L).comp (Ext.mk₀ (adj.counit.app Y)) (add_zero n)).comp
      (Ext.mk₀ g) (add_zero n)
  simp only [Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀,
    Ext.comp_assoc_of_second_deg_zero, Ext.mk₀_comp_mk₀]
  exact congrArg (fun f => (x.mapExactFunctor L).comp (Ext.mk₀ f) (add_zero n))
    (adj.counit.naturality g)

private lemma adjointExtMap_delta (adj : L ⊣ R) (X : C)
    (T : ShortComplex D) (hT : T.ShortExact) (hR : (T.map R).ShortExact)
    (n : ℕ) (x : Ext X (R.obj T.X₃) n) :
    adjointExtMap adj X T.X₁ (n + 1) (x.comp hR.extClass rfl) =
      (adjointExtMap adj X T.X₃ n x).comp hT.extClass rfl := by
  let φ : (T.map R).map L ⟶ T :=
    { τ₁ := adj.counit.app T.X₁
      τ₂ := adj.counit.app T.X₂
      τ₃ := adj.counit.app T.X₃
      comm₁₂ := (adj.counit.naturality T.f).symm
      comm₂₃ := (adj.counit.naturality T.g).symm }
  show ((x.comp hR.extClass rfl).mapExactFunctor L).comp
      (Ext.mk₀ (adj.counit.app T.X₁)) (add_zero (n + 1)) =
    ((x.mapExactFunctor L).comp (Ext.mk₀ (adj.counit.app T.X₃)) (add_zero n)).comp
      hT.extClass rfl
  simp only [Ext.mapExactFunctor_comp, Ext.mapExactFunctor_extClass, Ext.comp_assoc]
  exact congrArg (fun y => (x.mapExactFunctor L).comp y (rfl : n + 1 = n + 1))
    (ShortComplex.ShortExact.extClass_naturality (hR.map_of_exact L) hT φ)

/-- **Dimension shifting for `adjointExtMap`.** The canonical map is bijective at every object of
a class containing the injective objects and closed under the two outer terms of a short exact
sequence which `R` keeps short exact. -/
private theorem adjointExtMap_bijective (adj : L ⊣ R) [EnoughInjectives D]
    [R.PreservesInjectiveObjects] (P : D → Prop)
    (hI : ∀ (I : D), Injective I → P I)
    (hP : ∀ (T : ShortComplex D), T.ShortExact → P T.X₁ → P T.X₂ →
      P T.X₃ ∧ (T.map R).ShortExact)
    (X : C) (Y : D) (hY : P Y) (n : ℕ) :
    Function.Bijective (adjointExtMap adj X Y n) := by
  induction n generalizing Y with
  | zero =>
    have he : (adjointExtMap adj X Y 0 : _ → _) =
        Ext.homEquiv₀.symm ∘ (adj.homEquiv X Y).symm ∘ Ext.homEquiv₀ := by
      funext x
      obtain ⟨f, rfl⟩ := (Ext.mk₀_bijective X (R.obj Y)).surjective x
      have hf : Ext.homEquiv₀ (Ext.mk₀ f) = f := Ext.homEquiv₀.apply_symm_apply f
      simpa only [Function.comp_apply, hf, Ext.homEquiv₀_symm_apply] using
        adjointExtMap_mk₀ adj X Y f
    rw [he]
    exact Ext.homEquiv₀.symm.bijective.comp
      ((adj.homEquiv X Y).symm.bijective.comp Ext.homEquiv₀.bijective)
  | succ n hn =>
    let I : InjectivePresentation Y := Classical.arbitrary _
    let T := ShortComplex.mk _ _ (cokernel.condition I.f)
    have hT : T.ShortExact := { exact := ShortComplex.exact_cokernel I.f }
    obtain ⟨hZ, hR⟩ := hP T hT hY (hI I.J I.injective)
    have : Injective (T.map R).X₂ :=
      Functor.PreservesInjectiveObjects.injective_obj I.injective
    let := Ext.subsingleton_of_injective (L.obj X) T.X₂ n
    let := Ext.subsingleton_of_injective X (T.map R).X₂ n
    exact AddMonoidHom.bijective_of_surjective_of_bijective_of_right_exact _ _ _ _
      (adjointExtMap adj X T.X₂ n) (adjointExtMap adj X T.X₃ n)
      (adjointExtMap adj X T.X₁ (n + 1))
      (by ext x; exact (adjointExtMap_naturality adj X T.g n x).symm)
      (by ext x; exact (adjointExtMap_delta adj X T hT hR n x).symm)
      ((ShortComplex.ab_exact_iff_function_exact _).mp
        (Ext.covariant_sequence_exact₃' X hR n (n + 1) rfl))
      ((ShortComplex.ab_exact_iff_function_exact _).mp
        (Ext.covariant_sequence_exact₃' (L.obj X) hT n (n + 1) rfl))
      (hn _ (hI I.J I.injective)).surjective (hn _ hZ)
      (fun x₁ => Ext.covariant_sequence_exact₁ _ hR x₁ (by subsingleton) rfl)
      (fun y₁ => Ext.covariant_sequence_exact₁ _ hT y₁ (by subsingleton) rfl)

/-- **The canonical map is bijective at an `R`-acyclic object.** The right-acyclic objects of `R`
form a class to which dimension shifting applies, so an object whose higher right derived images
vanish has its `Ext` computed on the other side of the adjunction. -/
private theorem adjointExtMap_bijective_of_acyclic (adj : L ⊣ R)
    [EnoughInjectives D] [R.PreservesInjectiveObjects] [PreservesFiniteLimits R]
    (X : C) (Y : D)
    (hY : ∀ n, 0 < n → IsZero ((R.rightDerived n).obj Y)) (n : ℕ) :
    Function.Bijective (adjointExtMap adj X Y n) := by
  let := HasDerivedCategory.standard C
  let := HasDerivedCategory.standard D
  let := HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso
    (R.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh)
  apply adjointExtMap_bijective adj R.rightAcyclic _ _ X Y _ n
  · intro I hI
    let := hI
    exact ((Functor.rightAcyclic_iff_isIso_and_isZero_rightDerivedPlus R I).2
      inferInstance).mpr fun i hi =>
        Functor.isZero_rightDerivedPlus_obj_injective R i (ne_of_gt hi) I
  · intro T hT h₁ h₂
    exact (Functor.rightAcyclic_and_shortExact_map_of_shortExact R T hT).2.1 h₁ h₂
  · apply ((Functor.rightAcyclic_iff_isIso_and_isZero_rightDerivedPlus R Y).2
      inferInstance).mpr
    intro i hi
    obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le (le_of_lt hi)
    exact (Stacks.DerivedIndexing.isZero_rightDerived_obj_iff R k Y).mp
      (hY k (by exact_mod_cast hi))

/-- **The canonical `Ext`-comparison through an identification of the image of the left
adjoint.** The form `adjointExtMap` is used in: the object `Z` whose `Ext` is wanted is given
only up to an isomorphism `L X ≅ Z`. -/
public def adjointExtComparisonMap (adj : L ⊣ R) {X : C} {Z : D} (e : L.obj X ≅ Z) (Y : D)
    (n : ℕ) : Ext X (R.obj Y) n →+ Ext Z Y n :=
  (Ext.precomp (Ext.mk₀ e.inv) Y (zero_add n)).comp (adjointExtMap adj X Y n)

/-- **The canonical `Ext`-comparison is bijective at an `R`-acyclic object.** -/
public theorem bijective_adjointExtComparisonMap (adj : L ⊣ R) [EnoughInjectives D]
    [R.PreservesInjectiveObjects] [PreservesFiniteLimits R] {X : C} {Z : D} (e : L.obj X ≅ Z)
    (Y : D) (hY : ∀ n, 0 < n → IsZero ((R.rightDerived n).obj Y)) (n : ℕ) :
    Function.Bijective (adjointExtComparisonMap adj e Y n) := by
  have he : Function.Bijective (fun x : Ext (L.obj X) Y n =>
      (Ext.mk₀ e.inv).comp x (zero_add n)) :=
    ConcreteCategory.bijective_of_isIso (((extFunctor n).map e.inv.op).app Y)
  exact he.comp (adjointExtMap_bijective_of_acyclic adj X Y hY n)

omit [R.Additive] in
/-- **The canonical `Ext`-comparison in degree zero is the hom-set bijection of the
adjunction**, read through the identification `e`. -/
public theorem adjointExtComparisonMap_mk₀ (adj : L ⊣ R) {X : C} {Z : D} (e : L.obj X ≅ Z)
    (Y : D) (f : X ⟶ R.obj Y) :
    adjointExtComparisonMap adj e Y 0 (Ext.mk₀ f) =
      Ext.mk₀ (e.inv ≫ (adj.homEquiv X Y).symm f) := by
  show (Ext.mk₀ e.inv).comp (adjointExtMap adj X Y 0 (Ext.mk₀ f)) (zero_add 0) = _
  rw [adjointExtMap_mk₀, Ext.mk₀_comp_mk₀]

omit [R.Additive] in
/-- **The canonical `Ext`-comparison commutes with morphisms of the second variable.** -/
public theorem adjointExtComparisonMap_naturality (adj : L ⊣ R) {X : C} {Z : D}
    (e : L.obj X ≅ Z) {Y Y' : D} (g : Y ⟶ Y') (n : ℕ) (x : Ext X (R.obj Y) n) :
    adjointExtComparisonMap adj e Y' n (x.comp (Ext.mk₀ (R.map g)) (add_zero n)) =
      (adjointExtComparisonMap adj e Y n x).comp (Ext.mk₀ g) (add_zero n) := by
  show (Ext.mk₀ e.inv).comp (adjointExtMap adj X Y' n
      (x.comp (Ext.mk₀ (R.map g)) (add_zero n))) (zero_add n) =
    ((Ext.mk₀ e.inv).comp (adjointExtMap adj X Y n x) (zero_add n)).comp
      (Ext.mk₀ g) (add_zero n)
  rw [adjointExtMap_naturality adj X g n x]
  exact (Ext.comp_assoc_of_third_deg_zero _ _ _ (zero_add n)).symm

end Stacks.Cohomology.AdjointExt

namespace Stacks.Adequate

variable {τ : CoveringTopology} {S : Scheme.{u}}

/-! ### The inclusion of the small Zariski site as a morphism of sites -/

section Comparison

variable (B : BigSite τ S)

local instance preservesFiniteLimits_opensToBig : PreservesFiniteLimits B.opensToBig :=
  preservesFiniteLimits_of_flat _

/-- Lower shriek `g_!` from abelian sheaves on the small Zariski site of `S` to abelian sheaves
on a chosen big site over `S`: the left adjoint of restriction, the sheafification of the
left Kan extension along the inclusion of the small Zariski site. -/
public abbrev BigSite.zariskiLowerShriek :
    Sheaf (Opens.grothendieckTopology ↥S) AddCommGrpCat.{u} ⥤
      Sheaf B.topology AddCommGrpCat.{u} :=
  Functor.sheafPullbackConstruction.sheafPullback B.opensToBig AddCommGrpCat.{u}
    (Opens.grothendieckTopology ↥S) B.topology

/-- The adjunction `g_! ⊣ g_*` between abelian sheaves on the small Zariski site of `S` and
abelian sheaves on a chosen big site over `S`. -/
public abbrev BigSite.zariskiAdjunction :
    B.zariskiLowerShriek ⊣ B.zariskiRestriction :=
  Functor.sheafPullbackConstruction.sheafAdjunctionContinuous B.opensToBig AddCommGrpCat.{u}
    (Opens.grothendieckTopology ↥S) B.topology

/-- **Lower shriek along the inclusion of the small Zariski site is exact.** This is
[Stacks, Tag 04BH]: the inclusion is representably flat, hence preserves the finite limits of
the opens of `S`, which are a complete lattice. -/
public theorem BigSite.preservesFiniteLimits_zariskiLowerShriek :
    PreservesFiniteLimits B.zariskiLowerShriek :=
  Stacks.Sites.LowerShriek.gShriek_preservesFiniteLimits B.opensToBig
    (Opens.grothendieckTopology ↥S) B.topology

local instance preservesFiniteLimits_zariskiLowerShriek_inst :
    PreservesFiniteLimits B.zariskiLowerShriek :=
  B.preservesFiniteLimits_zariskiLowerShriek

local instance preservesFiniteColimits_zariskiLowerShriek :
    PreservesFiniteColimits B.zariskiLowerShriek :=
  have := B.zariskiAdjunction.isLeftAdjoint
  inferInstance

local instance additive_zariskiLowerShriek : B.zariskiLowerShriek.Additive :=
  Functor.additive_of_preserves_binary_products _

local instance preservesFiniteLimits_zariskiRestriction :
    PreservesFiniteLimits B.zariskiRestriction :=
  have := B.zariskiAdjunction.isRightAdjoint
  inferInstance

/-- **Restriction to the small Zariski site preserves injective abelian sheaves.** This is
[Stacks, Tag 015Z]: its left adjoint `g_!` is exact, hence preserves monomorphisms. -/
public theorem BigSite.preservesInjectiveObjects_zariskiRestriction :
    B.zariskiRestriction.PreservesInjectiveObjects :=
  Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms B.zariskiAdjunction

local instance preservesInjectiveObjects_zariskiRestriction_inst :
    B.zariskiRestriction.PreservesInjectiveObjects :=
  B.preservesInjectiveObjects_zariskiRestriction

/-! ### Assertion (3) read on the affine opens of the base -/

/-- **Acyclicity on the affine opens of `S`.** The positive-degree cohomology of
an abelian sheaf `𝓖` on a chosen big site over `S` vanishes over every affine open of `S`,
where `H^q(U, −)` is the `q`-th right derived functor of sections over the object of the site
given by `U`. An affine open of `S` is an affine scheme over `S` belonging to the site, so this
is a consequence of [Stacks, Tag 06VM] (3), by
`Stacks.Adequate.BigSite.adequateAffineOpenAcyclicity`. -/
public abbrev BigSite.AffineOpenAcyclicity (G : Sheaf B.topology AddCommGrpCat.{u}) : Prop :=
  ∀ U : S.Opens, IsAffineOpen U → ∀ q : ℕ, 0 < q →
    IsZero ((((sheafSections B.topology AddCommGrpCat.{u}).obj
      (op (B.opensToBig.obj U))).rightDerived q).obj G)

/-- **The higher direct images along `g : (Sch/S)_τ → S_Zar` of a sheaf acyclic on the affine
opens of `S` vanish.** This is the step the source of [Stacks, Tag 06VM] takes "in exactly the
same way as in the proof of [Stacks, Tag 03DW]": the presheaf underlying `R^q g_* 𝓖` sends an
open `V` of `S` to `H^q(V, 𝓖)`, which the hypothesis kills on the affine opens, and the affine
opens form a basis, so the Zariski sheafification of that presheaf is zero. -/
public theorem BigSite.isZero_rightDerived_zariskiRestriction
    (G : Sheaf B.topology AddCommGrpCat.{u}) (hG : B.AffineOpenAcyclicity G)
    (q : ℕ) (hq : 0 < q) :
    IsZero ((B.zariskiRestriction.rightDerived q).obj G) := by
  set J := Opens.grothendieckTopology ↥S with hJ
  set P := B.zariskiRestriction ⋙ sheafToPresheaf J AddCommGrpCat.{u} with hP
  have hbasis (U : S.Opens) (hU : U ∈ S.affineOpens) :
      IsZero (((P.rightDerived q).obj G).obj (op U)) := by
    have he : IsZero (((P ⋙ (evaluation S.Opensᵒᵖ AddCommGrpCat.{u}).obj
        (op U)).rightDerived q).obj G) := hG U hU q hq
    exact he.of_iso
      ((Functor.rightDerivedCompIso P
        ((evaluation S.Opensᵒᵖ AddCommGrpCat.{u}).obj (op U)) q).app G).symm
  have hzero : IsZero ((presheafToSheaf J AddCommGrpCat.{u}).obj ((P.rightDerived q).obj G)) :=
    Stacks.AffineHigherDirectImage.isZero_sheafification_of_isZero_on_basis
      S.isBasis_affineOpens _ hbasis
  have α : P ⋙ presheafToSheaf J AddCommGrpCat.{u} ≅ B.zariskiRestriction :=
    Functor.isoWhiskerLeft B.zariskiRestriction
      (asIso (sheafificationAdjunction J AddCommGrpCat.{u}).counit) ≪≫
      B.zariskiRestriction.rightUnitor
  have e : P.rightDerived q ⋙ presheafToSheaf J AddCommGrpCat.{u} ≅
      B.zariskiRestriction.rightDerived q :=
    (Functor.rightDerivedCompIso P (presheafToSheaf J AddCommGrpCat.{u}) q).symm ≪≫
      Functor.rightDerivedIsoOfNatIso α q
  exact hzero.of_iso (e.app G).symm

/-- **Acyclicity on the affine opens of `S` of an adequate `𝒪`-module**:
`Stacks.Adequate.BigSite.AffineOpenAcyclicity` of the underlying abelian sheaf, asserted of the
adequate ones. It holds, by `Stacks.Adequate.BigSite.adequateAffineOpenAcyclicity`. -/
public abbrev BigSite.AdequateAffineOpenAcyclicity (F : SheafOfModules.{u} B.structureSheaf) :
    Prop :=
  IsAdequate B F → B.AffineOpenAcyclicity ((SheafOfModules.toSheaf B.structureSheaf).obj F)

/-- **[Stacks, Tag 06VM] (3) read on the affine opens of `S`.** An affine open `U` of `S` is an
affine object of the site, namely `Stacks.Adequate.BigSite.opensToBig` applied to `U`, so the
vanishing `Stacks.Adequate.BigSite.isZero_rightDerived_sections_of_isAdequate` on the affine
objects of the site specializes to it. -/
public theorem BigSite.adequateAffineOpenAcyclicity (F : SheafOfModules.{u} B.structureSheaf) :
    B.AdequateAffineOpenAcyclicity F := by
  intro hF U hU q hq
  have : IsAffine (B.opensToBig.obj U).left.obj := hU
  exact B.isZero_rightDerived_sections_of_isAdequate.{u, u} F hF (B.opensToBig.obj U) q hq

/-- **The higher direct images of an adequate `𝒪`-module along `g : (Sch/S)_τ → S_Zar` vanish**
in positive degrees. This is the step the source of [Stacks, Tag 06VM] takes "in exactly the same
way as in the proof of [Stacks, Tag 03DW]", from assertion (3) read on the affine opens of `S`. -/
public theorem BigSite.higherZariskiRestrictionVanishing (F : SheafOfModules.{u} B.structureSheaf) :
    B.HigherZariskiRestrictionVanishing F := fun hF q hq =>
  B.isZero_rightDerived_zariskiRestriction _ (B.adequateAffineOpenAcyclicity F hF) q hq

/-- **[Stacks, Tag 06VM] (4).** For an adequate `𝒪`-module `𝓕` on a chosen big `τ`-site
`(Sch/S)_τ` over a scheme `S`, the canonical isomorphism

`H^q(S, 𝓕|_{S_Zar}) ≅ H^q((Sch/S)_τ, 𝓕)`

in every degree `q`, where `𝓕|_{S_Zar}` is `Stacks.Adequate.BigSite.zariskiRestrictModule` and
cohomology is the right derived functor of global sections of the underlying abelian sheaves.
It is the Grothendieck edge isomorphism of the composite `Γ(S_Zar, −) ∘ (−)|_{S_Zar} = Γ`, the
higher direct images of `𝓕` vanishing by
`Stacks.Adequate.BigSite.higherZariskiRestrictionVanishing`. -/
@[stacks 06VM "(4): for an adequate 𝒪-module F on (Sch/S)_τ, the canonical isomorphism
H^q(S, F|_{S_Zar}) = H^q((Sch/S)_τ, F) in every degree q, cohomology being the right derived
functor of global sections"]
public noncomputable def BigSite.adequateCohomologyIso (F : SheafOfModules.{u} B.structureSheaf)
    (hF : IsAdequate B F) (q : ℕ) :
    ((zariskiGlobalSections S).rightDerived q).obj
        ((SheafOfModules.toSheaf S.ringCatSheaf).obj (B.zariskiRestrictModule.obj F)) ≅
      (B.globalSections.rightDerived q).obj ((SheafOfModules.toSheaf B.structureSheaf).obj F) :=
  (B.zariskiCohomologyIso F hF (B.higherZariskiRestrictionVanishing F) q).symm

/-! ### The canonical comparison of cohomology -/

/-- **Lower shriek carries the constant abelian sheaf `ℤ` to the constant abelian sheaf `ℤ`.**
The inclusion of the small Zariski site of `S` carries the terminal open `⊤ ⊆ S` to a terminal
object of the big site, so the two constant-sheaf functors are left adjoint to the same
functor. -/
public def BigSite.constantSheafZariskiIso :
    B.zariskiLowerShriek.obj ((constantSheaf (Opens.grothendieckTopology ↥S)
        AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift.{u} ℤ))) ≅
      (constantSheaf B.topology AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift.{u} ℤ)) :=
  (Stacks.Cohomology.BiggerSite.constantSheafCompSheafPullbackIso
    (Opens.grothendieckTopology ↥S) B.topology B.opensToBig AddCommGrpCat.{u}
    isTerminalTop B.isTerminal_opensToBig_top rfl).app (AddCommGrpCat.of (ULift.{u} ℤ))

variable [HasExt.{w} (Sheaf (Opens.grothendieckTopology ↥S) AddCommGrpCat.{u})]
  [HasExt.{w} (Sheaf B.topology AddCommGrpCat.{u})]

/-- **The canonical comparison `H^q(S, 𝓖|_{S_Zar}) → H^q((Sch/S)_τ, 𝓖)`.** Cohomology is the
`Ext`-group out of the constant abelian sheaf `ℤ`; the map applies the exact functor `g_!` to an
extension class, composes with the counit of `g_! ⊣ g_*`, and reads the result through the
identification `Stacks.Adequate.BigSite.constantSheafZariskiIso` of the two constant sheaves. -/
public def BigSite.zariskiSheafHMap (G : Sheaf B.topology AddCommGrpCat.{u}) (q : ℕ) :
    Sheaf.H.{w} (B.zariskiRestriction.obj G) q →+ Sheaf.H.{w} G q :=
  Stacks.Cohomology.AdjointExt.adjointExtComparisonMap B.zariskiAdjunction
    B.constantSheafZariskiIso G q

/-- **The bijectivity of the `Ext`-comparison.** The canonical comparison of the cohomology of an
abelian sheaf on a chosen big site over `S` with the cohomology of its restriction to the
small Zariski site of `S` is bijective in every degree, as soon as the sheaf is acyclic on the
affine opens of `S`. -/
public theorem BigSite.bijective_zariskiSheafHMap (G : Sheaf B.topology AddCommGrpCat.{u})
    (hG : B.AffineOpenAcyclicity G) (q : ℕ) :
    Function.Bijective (B.zariskiSheafHMap.{w} G q) :=
  Stacks.Cohomology.AdjointExt.bijective_adjointExtComparisonMap B.zariskiAdjunction
    B.constantSheafZariskiIso G
    (fun n hn => B.isZero_rightDerived_zariskiRestriction G hG n hn) q

/-- **The `Ext`-comparison as an equivalence.** For an abelian sheaf `𝓖` on a chosen big site over
`S` which is acyclic on the affine opens of `S`, the canonical additive equivalence

`H^q(S, 𝓖|_{S_Zar}) ≃+ H^q((Sch/S)_τ, 𝓖)`

in every degree `q`, where cohomology is the `Ext`-group out of the constant abelian sheaf `ℤ`.
It is the canonical comparison map `Stacks.Adequate.BigSite.zariskiSheafHMap`, by
`Stacks.Adequate.BigSite.zariskiSheafHEquiv_apply`. -/
public def BigSite.zariskiSheafHEquiv (G : Sheaf B.topology AddCommGrpCat.{u})
    (hG : B.AffineOpenAcyclicity G) (q : ℕ) :
    Sheaf.H.{w} (B.zariskiRestriction.obj G) q ≃+ Sheaf.H.{w} G q :=
  AddEquiv.ofBijective (B.zariskiSheafHMap.{w} G q) (B.bijective_zariskiSheafHMap.{w} G hG q)

/-- **The `Ext`-equivalence is the canonical comparison map.** This is what
pins down its normalization. -/
public theorem BigSite.zariskiSheafHEquiv_apply (G : Sheaf B.topology AddCommGrpCat.{u})
    (hG : B.AffineOpenAcyclicity G) (q : ℕ)
    (x : Sheaf.H.{w} (B.zariskiRestriction.obj G) q) :
    B.zariskiSheafHEquiv.{w} G hG q x = B.zariskiSheafHMap.{w} G q x :=
  rfl

/-- **The `Ext`-comparison commutes with morphisms of abelian sheaves.** -/
public theorem BigSite.zariskiSheafHEquiv_naturality
    {G G' : Sheaf B.topology AddCommGrpCat.{u}} (hG : B.AffineOpenAcyclicity G)
    (hG' : B.AffineOpenAcyclicity G') (f : G ⟶ G') (q : ℕ)
    (x : Sheaf.H.{w} (B.zariskiRestriction.obj G) q) :
    B.zariskiSheafHEquiv.{w} G' hG' q
        (Sheaf.H.map.{w, u} (B.zariskiRestriction.map f) q x) =
      Sheaf.H.map.{w, u} f q (B.zariskiSheafHEquiv.{w} G hG q x) := by
  show Stacks.Cohomology.AdjointExt.adjointExtComparisonMap B.zariskiAdjunction
      B.constantSheafZariskiIso G' q
      (x.comp (Ext.mk₀ (B.zariskiRestriction.map f)) (add_zero q)) =
    (Stacks.Cohomology.AdjointExt.adjointExtComparisonMap B.zariskiAdjunction
      B.constantSheafZariskiIso G q x).comp (Ext.mk₀ f) (add_zero q)
  exact Stacks.Cohomology.AdjointExt.adjointExtComparisonMap_naturality
    B.zariskiAdjunction B.constantSheafZariskiIso f q x

/-- **In degree zero the `Ext`-comparison is the hom-set bijection of
`g_! ⊣ g_*`.** Every class in `H^0` is the class of a morphism out of the constant sheaf `ℤ`, and
the comparison sends it to the morphism adjoint to it, read through the identification
`Stacks.Adequate.BigSite.constantSheafZariskiIso` of the two constant sheaves. Together with
`Stacks.Adequate.BigSite.zariskiSheafHEquiv_apply` this fixes the normalization of the
comparison. -/
public theorem BigSite.zariskiSheafHMap_mk₀ (G : Sheaf B.topology AddCommGrpCat.{u})
    (f : (constantSheaf (Opens.grothendieckTopology ↥S) AddCommGrpCat.{u}).obj
      (AddCommGrpCat.of (ULift.{u} ℤ)) ⟶ B.zariskiRestriction.obj G) :
    B.zariskiSheafHMap.{w} G 0 (Ext.mk₀ f) =
      Ext.mk₀ (B.constantSheafZariskiIso.inv ≫
        (B.zariskiAdjunction.homEquiv _ G).symm f) :=
  Stacks.Cohomology.AdjointExt.adjointExtComparisonMap_mk₀ B.zariskiAdjunction
    B.constantSheafZariskiIso G f

/-- **[Stacks, Tag 06VM] (4) in the `Ext` model of cohomology.** For an adequate `𝒪`-module `𝓕`
on a chosen big `τ`-site over `S`, the canonical additive equivalence

`H^q(S, 𝓕|_{S_Zar}) ≃+ H^q((Sch/S)_τ, 𝓕)`

in every degree `q`, where cohomology is Mathlib's `CategoryTheory.Sheaf.H`, the `Ext`-groups
out of the constant abelian sheaf `ℤ`, of the underlying abelian sheaves. The tag is carried by
`Stacks.Adequate.BigSite.adequateCohomologyIso`, the same statement with cohomology the right
derived functor of global sections, which is the source's definition and needs no `HasExt`
universe. -/
public def BigSite.adequateSheafHEquiv (F : SheafOfModules.{u} B.structureSheaf)
    (hF : IsAdequate B F) (q : ℕ) :
    Sheaf.H.{w} ((SheafOfModules.toSheaf S.ringCatSheaf).obj (B.zariskiRestrictModule.obj F)) q ≃+
      Sheaf.H.{w} ((SheafOfModules.toSheaf B.structureSheaf).obj F) q :=
  B.zariskiSheafHEquiv.{w} _ (B.adequateAffineOpenAcyclicity F hF) q

end Comparison

end Stacks.Adequate

end
