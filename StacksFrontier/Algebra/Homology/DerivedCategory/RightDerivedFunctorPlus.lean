module

public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import Mathlib.Algebra.Homology.Factorizations.CM5a
public import Mathlib.Algebra.Homology.HomotopyCategory.Plus
public import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Constructor
public import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Data.Int.ConditionallyCompleteOrder
public import Mathlib.Order.CompletePartialOrder
import StacksCore.Tactic.EgaSgaAttribute

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-
# Problem Description

This is Stacks project Tag 05TI (`lemma-enough-injectives-right-derived`), in the
chapter *Derived Categories*.

Throughout, $A$ denotes an abelian category with **enough injectives** (every object
admits a monomorphism into an injective object).

## Main Definitions (informal)

- $K^{+}(A)$ is the bounded-below homotopy category of cochain complexes in $A$: objects
  are bounded-below complexes ($K^n = 0$ for $n \ll 0$), morphisms are chain-homotopy
  classes of chain maps. It is a triangulated category.
- $\mathrm{Qis}^{+}(A)$ is the class of quasi-isomorphisms in $K^{+}(A)$ (morphisms
  inducing isomorphisms on all cohomology objects $H^n$); it is a saturated
  multiplicative system compatible with the triangulation.
- The bounded-below derived category is the Verdier localization
  $D^{+}(A) = K^{+}(A)[\mathrm{Qis}^{+}(A)^{-1}]$ with localization functor
  $Q^{+} : K^{+}(A) \to D^{+}(A)$.
- An **exact** (= triangulated) functor between triangulated categories is additive,
  commutes with the shift, and sends distinguished triangles to distinguished triangles.
- For an exact functor $F : K \to D$ and a saturated multiplicative system $S$, the right
  derived functor $RF$ is **defined at $X$** if the pointwise left Kan extension of $F$
  along the localization $q : K \to K[S^{-1}]$ exists at $X$; $RF$ is **everywhere
  defined** if this holds for all $X$. In Mathlib this predicate is
  `CategoryTheory.Functor.HasRightDerivedFunctor F W`, the existence of a left Kan
  extension of $F$ along the localization functor for the morphism property $W = S$.

## Main Statements (informal)

Let $A$ be abelian with enough injectives.

- **Statement 1 (Tag 05TI, part 1).** For every triangulated category $D$ and every exact
  functor $F : K^{+}(A) \to D$, the right derived functor
  $RF : D^{+}(A) \to D$ is everywhere defined.

- **Statement 2 (Tag 05TI, part 2).** For every abelian category $B$ and every additive
  functor $F : A \to B$, the right derived functor $RF : D^{+}(A) \to D^{+}(B)$ is
  everywhere defined. Here $RF$ is the right derived functor of the composite
  $Q^{+}_{B} \circ K^{+}(F) : K^{+}(A) \to D^{+}(B)$, where $K^{+}(F)$ is the exact
  functor induced by applying $F$ degreewise.

## Formalization notes

- $K^{+}(A)$ is `CategoryTheory.HomotopyCategory.Plus A` (the full subcategory of
  bounded-below complexes), and $\mathrm{Qis}^{+}(A)$ is
  `CategoryTheory.HomotopyCategory.Plus.quasiIso A : MorphismProperty (HomotopyCategory.Plus A)`.
- "Everywhere defined" is exactly `Functor.HasRightDerivedFunctor`; this predicate
  only refers to the source category $K^{+}(A)$ and the morphism property
  $\mathrm{Qis}^{+}(A)$, so the target need not be the named $D^{+}(A)$.
- In Statement 1 the target $D$ is an arbitrary triangulated category and $F$ is an
  exact functor (`F.CommShift ℤ` together with `F.IsTriangulated`).
- In Statement 2 the target $D^{+}(B)$ is realized as the localization
  `(HomotopyCategory.Plus.quasiIso B).Localization` with localization functor
  `(HomotopyCategory.Plus.quasiIso B).Q`, and $K^{+}(F)$ is the induced functor
  `mapPlus F` defined below.
- "Bounded below" is `∃ n, K.IsStrictlyGE n` (cohomological, increasing-differential
  indexing $d^n : K^n \to K^{n+1}$). "Exact functor" between triangulated categories is
  unrelated to exactness of additive functors between abelian categories; in part 2,
  $F$ is merely additive.
-/

open CategoryTheory CategoryTheory.Limits

-- Main Definition(s)

/-- An additive functor `F : A ⥤ B` preserves the bounded-below property of objects of
the homotopy category. This is the object-level compatibility needed to restrict
`F.mapHomotopyCategory` to the bounded-below subcategory `K^{+}`. -/
theorem mapHomotopyCategory_plus {A B : Type*} [Category A] [Category B] [Abelian A]
    [Abelian B] (F : A ⥤ B) [F.Additive]
    (X : HomotopyCategory A (ComplexShape.up ℤ)) (hX : (HomotopyCategory.plus A) X) :
    (HomotopyCategory.plus B) ((F.mapHomotopyCategory (ComplexShape.up ℤ)).obj X) := by
  obtain ⟨Y, rfl⟩ := HomotopyCategory.quotient_obj_surjective X
  rw [HomotopyCategory.plus_quotient_obj_iff] at hX
  obtain ⟨n, hn⟩ := hX
  rw [Functor.mapHomotopyCategory_obj, HomotopyCategory.plus_quotient_obj_iff]
  refine ⟨n, ?_⟩
  rw [CochainComplex.isStrictlyGE_iff]
  intro i hi
  have hz : IsZero (Y.X i) := (CochainComplex.isStrictlyGE_iff Y n).mp hn i hi
  exact F.map_isZero hz

/-- The exact functor `K^{+}(F) : K^{+}(A) ⥤ K^{+}(B)` induced by an additive functor
`F : A ⥤ B`, obtained by restricting `F.mapHomotopyCategory` to the bounded-below
subcategory. -/
@[sga "4 Vbis 2.4.4" "more general"]
noncomputable def mapPlus {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    (F : A ⥤ B) [F.Additive] :
    HomotopyCategory.Plus A ⥤ HomotopyCategory.Plus B :=
  ObjectProperty.lift (HomotopyCategory.plus B)
    (HomotopyCategory.Plus.ι A ⋙ F.mapHomotopyCategory (ComplexShape.up ℤ))
    (fun X => mapHomotopyCategory_plus F X.1 X.2)

-- Supporting construction: the injective derivability structure on `K^{+}(A)`.

/-- The object property on `K^{+}(A)` of being (represented by) a K-injective cochain
complex.  Since `A` has enough injectives, every bounded-below complex of injectives is
K-injective (`CochainComplex.isKInjective_of_injective`); these objects form a
right-resolving subcategory `K^{+}(Inj A) ⊆ K^{+}(A)`. -/
def plusInjective (A : Type*) [Category A] [Abelian A] :
    ObjectProperty (HomotopyCategory.Plus A) :=
  fun X => CochainComplex.IsKInjective (((HomotopyCategory.Plus.ι A).obj X)).as

/-- The inclusion functor `K^{+}(Inj A) ↪ K^{+}(A)`. -/
noncomputable def plusInjΦFunctor (A : Type*) [Category A] [Abelian A] :
    (plusInjective A).FullSubcategory ⥤ HomotopyCategory.Plus A :=
  (plusInjective A).ι

/-- The localizer morphism `Φ : K^{+}(Inj A) → K^{+}(A)` underlying the injective
derivability structure: the inclusion of the K-injective subcategory, with the source
quasi-isomorphisms `W₁` defined as the inverse image of `Qis^{+}(A)`. -/
noncomputable def plusInjΦ (A : Type*) [Category A] [Abelian A] :
    LocalizerMorphism
      ((HomotopyCategory.Plus.quasiIso A).inverseImage (plusInjΦFunctor A))
      (HomotopyCategory.Plus.quasiIso A) :=
  LocalizerMorphism.mk (plusInjΦFunctor A) (le_refl _)

/- **Analytic kernel (Stacks 05T9 → 05TG).**  The inclusion of the K-injective
subcategory `K^{+}(Inj A) ↪ K^{+}(A)` is a *right derivability structure*.

We do not use a global functorial K-injective resolution functor
`ρ : K^{+}(A) ⥤ K^{+}(Inj A)` fed to `isRightDerivabilityStructure_of_functorial_resolutions`:
that would require building a Cartan–Eilenberg functorial resolution and descending it to the
homotopy category — the accessible CM5a factorization machinery is `_private`, factors a single
fixed map (not an object-functor), and there is no `ModelCategory (CochainComplex.Plus A)`
instance.  Instead we use `LocalizerMorphism.IsRightDerivabilityStructure.mk'`, which needs
no functor, only the existence of resolutions plus K-injective orthogonality.  Its hypotheses:
* `[W₂.ContainsIdentities]` — synthesizes automatically.
* `[Φ.arrow.HasRightResolutions]` — (B2) below; for every arrow `g : X ⟶ Y` in `K^{+}(A)`
  a compatible square into `K^{+}(Inj A)` with both legs quasi-isos.  From `cm5a`
  (object case, with `CochainComplex.isKInjective_of_injective`) and K-injective
  orthogonality (arrow case).
* `[∀ X₂, IsConnected (Φ.RightResolution X₂)]` — (B3) below; nonempty (object case of the
  resolution lemma) + connected (K-injective orthogonality: any two resolutions of `X₂`
  are joined by a direct map, since `Hom(−, I)` sends quasi-isos to bijections for
  K-injective `I`).
* `[Φ.IsLocalizedEquivalence]` — (B4) below; `K^{+}(Inj A)[W₁⁻¹] ≃ D^{+}(A)`: ess-surj from
  the object resolution lemma, fully-faithful from K-injective orthogonality together with
  `W₁ ⊆ Iso` (a quasi-iso between K-injectives is an iso, `IsKInjective.quasiIso_iff` +
  `HomotopyCategory.isoOfHomotopyEquiv`).

The single substantive standalone obligation underlying (B3)/(B4) is K-injective
orthogonality (Stacks 070G). -/

/-- **(B2 keystone — object case, descended to `K^{+}(A)`).**  Every object `Y` of `K^{+}(A)`
admits a quasi-isomorphism `s : Y ⟶ Φ Y'` into a K-injective object `Y'` of `K^{+}(Inj A)`.

Proof sketch: write `Y` as the image of a complex `W` with `W.IsStrictlyGE m`, and factor the
zero map `W ⟶ 0` by `CochainComplex.Plus.modelCategoryQuillen.cm5a` as a mono quasi-isomorphism
`ι : W ⟶ K'` followed by a degreewise epimorphism `π : K' ⟶ 0` with injective kernels. The
kernel of `π.f i` is `K'.X i`, so `K'` is a bounded-below complex of injectives, hence
K-injective (`CochainComplex.isKInjective_of_injective`), and `ι` descends to the required
quasi-isomorphism. -/
lemma plusInjΦ_exists_resolution (A : Type*) [Category A] [Abelian A] [EnoughInjectives A]
    (Y : HomotopyCategory.Plus A) :
    ∃ (Y' : (plusInjective A).FullSubcategory) (s : Y ⟶ (plusInjΦFunctor A).obj Y'),
      (HomotopyCategory.Plus.quasiIso A) s := by
  obtain ⟨W, hYW⟩ := HomotopyCategory.Plus.quotient_obj_surjective Y
  subst hYW
  obtain ⟨m, hm⟩ := W.2
  obtain ⟨Z, hZ⟩ := (HasZeroObject.zero (C := CochainComplex A ℤ))
  have hWGE : W.obj.IsStrictlyGE (m - 1 + 1) := by rw [sub_add_cancel]; exact hm
  have hZi (i : ℤ) : IsZero (Z.X i) :=
    (HomologicalComplex.eval A (ComplexShape.up ℤ) i).map_isZero hZ
  have hZGE : Z.IsStrictlyGE (m - 1) :=
    (CochainComplex.isStrictlyGE_iff Z (m-1)).mpr fun i _ => hZi i
  obtain ⟨K', hK'GE, ι, π, hMono, hQiso, hEpiKer, hcomp⟩ :=
    CochainComplex.Plus.modelCategoryQuillen.cm5a (0 : W.obj ⟶ Z) (m - 1)
  have : K'.IsStrictlyGE (m - 1) := hK'GE
  have hInj : ∀ i, Injective (K'.X i) := by
    intro i
    have hk : Injective (kernel (π.f i)) := (hEpiKer i).2
    rw [(hZi i).eq_zero_of_tgt (π.f i)] at hk
    exact Injective.of_iso kernelZeroIsoSource hk
  have : K'.IsKInjective := CochainComplex.isKInjective_of_injective K' (m - 1)
  let K'plus : CochainComplex.Plus A := ⟨K', ⟨m - 1, hK'GE⟩⟩
  refine ⟨⟨(HomotopyCategory.Plus.quotient A).obj K'plus, ?_⟩,
    (HomotopyCategory.Plus.quotient A).map
      (ObjectProperty.homMk ι : W ⟶ K'plus), ?_⟩
  · show CochainComplex.IsKInjective (((HomotopyCategory.Plus.quotient A).obj K'plus).obj.as)
    rw [HomotopyCategory.Plus.quotient_obj_obj_as]
    exact (inferInstance : K'.IsKInjective)
  · rw [HomotopyCategory.Plus.quasiIso_iff, HomotopyCategory.Plus.quotient_map_hom]
    exact (HomotopyCategory.quotient_map_mem_quasiIso_iff ι).mpr hQiso

/-- **(B2 keystone — arrow case, descended to `K^{+}(A)`).**  Given an arrow `g : X ⟶ Y` of
`K^{+}(A)` and a chosen resolution `qY : Y ⟶ Φ Y'` (`Y'` K-injective, `qY` a quasi-iso), there is
a compatible resolution `qX : X ⟶ Φ X'` (`X'` K-injective, `qX` a quasi-iso) together with a map
`g' : X' ⟶ Y'` making the square commute on the nose: `qX ≫ Φ g' = g ≫ qY`.

Proof sketch: resolve `X` by `plusInjΦ_exists_resolution` to get a quasi-isomorphism
`qX : X ⟶ Φ X'`. Since `Φ Y'` is K-injective, it is right-orthogonal to the acyclic complexes in
the homotopy category, hence local with respect to quasi-isomorphisms (Stacks 070G), so
`g ≫ qY` factors through `qX` there; lifting the factorization through the fully faithful
inclusions gives `g'`. -/
lemma plusInjΦ_arrow_exists_resolution (A : Type*) [Category A] [Abelian A] [EnoughInjectives A]
    {X Y : HomotopyCategory.Plus A} (g : X ⟶ Y)
    (Y' : (plusInjective A).FullSubcategory) (qY : Y ⟶ (plusInjΦFunctor A).obj Y') :
    ∃ (X' : (plusInjective A).FullSubcategory) (qX : X ⟶ (plusInjΦFunctor A).obj X')
      (g' : X' ⟶ Y'), (HomotopyCategory.Plus.quasiIso A) qX ∧
        qX ≫ (plusInjΦFunctor A).map g' = g ≫ qY := by
  obtain ⟨X', qX, hqX⟩ := plusInjΦ_exists_resolution A X
  have hlocal : (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)).isLocal
      ((HomotopyCategory.Plus.ι A).obj ((plusInjΦFunctor A).obj Y')) := by
    rw [HomotopyCategory.quasiIso_eq_trW_subcategoryAcyclic,
      (HomotopyCategory.subcategoryAcyclic A).isLocal_trW]
    have hKI : CochainComplex.IsKInjective
        ((HomotopyCategory.Plus.ι A).obj ((plusInjΦFunctor A).obj Y')).as := Y'.2
    rwa [CochainComplex.isKInjective_iff_rightOrthogonal] at hKI
  obtain ⟨h₀, hh₀⟩ := (hlocal ((HomotopyCategory.Plus.ι A).map qX) hqX).surjective
    ((HomotopyCategory.Plus.ι A).map (g ≫ qY))
  -- transfer `h₀` to a `K⁺(A)`-morphism, then lift through `Φ` (both fully faithful).
  let ffΦ := (plusInjective A).fullyFaithfulι
  set h₁ : (plusInjΦFunctor A).obj X' ⟶ (plusInjΦFunctor A).obj Y' :=
    (HomotopyCategory.Plus.fullyFaithfulι A).preimage h₀ with hh₁
  refine ⟨X', qX, ffΦ.preimage h₁, hqX, ?_⟩
  apply (HomotopyCategory.Plus.fullyFaithfulι A).map_injective
  rw [Functor.map_comp]
  show (HomotopyCategory.Plus.ι A).map qX ≫
    (HomotopyCategory.Plus.ι A).map ((plusInjΦFunctor A).map _) = _
  rw [show (plusInjΦFunctor A).map (ffΦ.preimage h₁) = h₁ from ffΦ.map_preimage h₁]
  simp only [hh₁]
  rw [(HomotopyCategory.Plus.fullyFaithfulι A).map_preimage]
  exact hh₀

/-- **(B2)** `Φ.arrow.HasRightResolutions`: every arrow `g : X ⟶ Y` of `K^{+}(A)` admits a
right resolution by an arrow of `K^{+}(Inj A)` with quasi-iso legs, assembled from the two
keystone lemmas: resolve the target `g.right` via
`plusInjΦ_exists_resolution`, then resolve the source `g.left` compatibly via
`plusInjΦ_arrow_exists_resolution`, and package the resulting commuting square (with both legs
quasi-isos) as a `LocalizerMorphism.RightResolution` of the arrow `g`. -/
instance plusInjΦ_arrow_hasRightResolutions (A : Type*) [Category A] [Abelian A]
    [EnoughInjectives A] : (plusInjΦ A).arrow.HasRightResolutions := by
  intro g
  obtain ⟨Y', qY, hqY⟩ := plusInjΦ_exists_resolution A g.right
  obtain ⟨X', qX, g', hqX, hcomm⟩ :=
    plusInjΦ_arrow_exists_resolution A g.hom Y' qY
  exact ⟨LocalizerMorphism.RightResolution.mk
    (X₁ := Arrow.mk g') (Arrow.homMk qX qY hcomm) ⟨hqX, hqY⟩⟩

/-- **(B3)** `IsConnected (Φ.RightResolution X₂)` for every `X₂`.  The category of right
resolutions of `X₂` is nonempty (object case of (B2): `cm5a` applied to `X̃ ⟶ 0` gives a
quasi-iso `X₂ ⟶ Φ X'` with `X'` K-injective) and connected: given two resolutions
`(X', s)`, `(X'', s')`, K-injectivity of `X''` makes `s* : Hom(Φ X', X'') → Hom(X₂, X'')`
bijective (K-injective orthogonality, Stacks 070G), yielding a unique `u : X' ⟶ X''` with
`Φ u ∘ s = s'`, i.e. a direct morphism `(X', s) ⟶ (X'', s')` in `Φ.RightResolution X₂`. -/
instance plusInjΦ_rightResolution_isConnected (A : Type*) [Category A] [Abelian A]
    [EnoughInjectives A] (X₂ : HomotopyCategory.Plus A) :
    IsConnected ((plusInjΦ A).RightResolution X₂) := by
  -- Nonemptiness from the object resolution lemma.
  obtain ⟨Y', s, hs⟩ := plusInjΦ_exists_resolution A X₂
  have : Nonempty ((plusInjΦ A).RightResolution X₂) :=
    ⟨{ X₁ := Y', w := s, hw := hs }⟩
  -- Connectedness: any two resolutions admit a direct morphism (K-injective orthogonality).
  -- Given `R R'`, since `Φ R'.X₁` is K-injective, precomposition by the quasi-iso `R.w`
  -- is bijective on `Hom(−, Φ R'.X₁)`, yielding `f : R.X₁ ⟶ R'.X₁` with `R.w ≫ Φ f = R'.w`.
  have key : ∀ (R R' : (plusInjΦ A).RightResolution X₂), R ⟶ R' := by
    intro R R'
    have hlocal : (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)).isLocal
        ((HomotopyCategory.Plus.ι A).obj ((plusInjΦFunctor A).obj R'.X₁)) := by
      rw [HomotopyCategory.quasiIso_eq_trW_subcategoryAcyclic,
        (HomotopyCategory.subcategoryAcyclic A).isLocal_trW]
      have hKI : CochainComplex.IsKInjective
          ((HomotopyCategory.Plus.ι A).obj ((plusInjΦFunctor A).obj R'.X₁)).as := R'.X₁.2
      rwa [CochainComplex.isKInjective_iff_rightOrthogonal] at hKI
    have hex := (hlocal ((HomotopyCategory.Plus.ι A).map R.w) R.hw).surjective
      ((HomotopyCategory.Plus.ι A).map R'.w)
    let h₀ := hex.choose
    have hh₀ : (HomotopyCategory.Plus.ι A).map R.w ≫ h₀ = (HomotopyCategory.Plus.ι A).map R'.w :=
      hex.choose_spec
    let ffΦ := (plusInjective A).fullyFaithfulι
    set h₁ : (plusInjΦFunctor A).obj R.X₁ ⟶ (plusInjΦFunctor A).obj R'.X₁ :=
      (HomotopyCategory.Plus.fullyFaithfulι A).preimage h₀ with hh₁
    refine LocalizerMorphism.RightResolution.Hom.mk (ffΦ.preimage h₁) ?_
    apply (HomotopyCategory.Plus.fullyFaithfulι A).map_injective
    rw [Functor.map_comp]
    change (HomotopyCategory.Plus.ι A).map R.w ≫
      (HomotopyCategory.Plus.ι A).map ((plusInjΦFunctor A).map _) = _
    rw [show (plusInjΦFunctor A).map (ffΦ.preimage h₁) = h₁ from ffΦ.map_preimage h₁]
    simp only [hh₁]
    rw [(HomotopyCategory.Plus.fullyFaithfulι A).map_preimage]
    exact hh₀
  exact zigzag_isConnected (fun R R' => Zigzag.of_hom (key R R'))

/-- **(B4)** `Φ.IsLocalizedEquivalence`: the inclusion induces an equivalence
`K^{+}(Inj A)[W₁⁻¹] ≃ K^{+}(A)[W₂⁻¹] = D^{+}(A)` (Stacks 06XL).  Ess-surj: every `X₂` is
quasi-isomorphic to a K-injective `Φ X'` (object case of (B2)).  Fully faithful: `W₁` on
`K^{+}(Inj A)` consists of quasi-isos between K-injectives, hence isos
(`CochainComplex.IsKInjective.quasiIso_iff` + `HomotopyCategory.isoOfHomotopyEquiv`), so
`K^{+}(Inj A)[W₁⁻¹] ≃ K^{+}(Inj A)`; full faithfulness of the induced functor then follows
from K-injective orthogonality via the calculus of fractions for `W₂`. -/
instance plusInjΦ_isLocalizedEquivalence (A : Type*) [Category A] [Abelian A]
    [EnoughInjectives A] : (plusInjΦ A).IsLocalizedEquivalence := by
  -- Stacks 06XL.  Strategy: the inclusion `J = Φ.functor ⋙ Q⁺ : K^+(Inj A) ⥤ D^+(A)` is an
  -- equivalence, hence (as `W₁ ⊆ isomorphisms`) a localization of `K^+(Inj A)` at `W₁`,
  -- whence `Φ` is a localized equivalence by `of_isLocalization_of_isLocalization`.
  set Q := (HomotopyCategory.Plus.quasiIso A).Q
  -- `P` is the (triangulated) preimage of the acyclic subcategory; `P.trW = Qis⁺(A)`.
  set P := (HomotopyCategory.subcategoryAcyclic A).inverseImage (HomotopyCategory.Plus.ι A) with hP
  have hPtrw : P.trW = HomotopyCategory.Plus.quasiIso A := by
    ext X Y s
    rw [hP, ObjectProperty.inverseImage_trW_iff,
      ← HomotopyCategory.quasiIso_eq_trW_subcategoryAcyclic, HomotopyCategory.Plus.quasiIso_iff]
    rfl
  have hQloc : Q.IsLocalization P.trW := by
    rw [hPtrw]
    infer_instance
  -- K-injective objects are right-orthogonal to acyclics; hence `Q⁺` is bijective on homs into
  -- them.
  have hbij : ∀ (Y' : (plusInjective A).FullSubcategory) (X : HomotopyCategory.Plus A),
      Function.Bijective (Q.map : (X ⟶ (plusInjΦFunctor A).obj Y') → _) := by
    intro Y' X
    have hortho : P.rightOrthogonal ((plusInjΦFunctor A).obj Y') := by
      have hKortho : (HomotopyCategory.subcategoryAcyclic A).rightOrthogonal
          ((HomotopyCategory.Plus.ι A).obj ((plusInjΦFunctor A).obj Y')) := by
        have hKI : CochainComplex.IsKInjective
            ((HomotopyCategory.Plus.ι A).obj ((plusInjΦFunctor A).obj Y')).as := Y'.2
        rwa [CochainComplex.isKInjective_iff_rightOrthogonal] at hKI
      rw [ObjectProperty.rightOrthogonal_iff]
      intro X f hX
      rw [ObjectProperty.rightOrthogonal_iff] at hKortho
      have hf0 : (HomotopyCategory.Plus.ι A).map f = 0 :=
        hKortho ((HomotopyCategory.Plus.ι A).map f) hX
      exact (HomotopyCategory.Plus.fullyFaithfulι A).map_injective (by simpa using hf0)
    exact hortho.map_bijective_of_isTriangulated Q X
  -- every object of `K^+(A)` has a K-injective resolution: `Φ.HasRightResolutions`.
  have hHRR : (plusInjΦ A).HasRightResolutions := by
    intro Y
    obtain ⟨Y', s, hs⟩ := plusInjΦ_exists_resolution A Y
    exact ⟨{ X₁ := Y', w := s, hw := hs }⟩
  -- `J = Φ.functor ⋙ Q⁺` is fully faithful (from `hbij` and full faithfulness of `Φ.functor`)…
  let J := (plusInjΦ A).functor ⋙ Q
  have : J.Faithful := ⟨fun {_ Y'} _ _ huv ↦
    (plusInjective A).fullyFaithfulι.map_injective ((hbij Y' _).injective huv)⟩
  have : J.Full := by
    refine ⟨fun {_ Y'} g ↦ ?_⟩
    obtain ⟨h, hh⟩ := (hbij Y' _).surjective g
    exact ⟨(plusInjective A).fullyFaithfulι.preimage h, by
      simp only [Functor.comp_map, J]
      rw [show (plusInjΦ A).functor.map ((plusInjective A).fullyFaithfulι.preimage h) = h from
        (plusInjective A).fullyFaithfulι.map_preimage h]
      exact hh⟩
  -- …and essentially surjective (from the resolutions).  Hence `J` is an equivalence.
  have : J.EssSurj := (plusInjΦ A).essSurj_of_hasRightResolutions Q
  have : J.IsEquivalence := { }
  -- `W₁ ⊆ isomorphisms`: a quasi-iso between K-injectives is an iso.
  have hW1 : (HomotopyCategory.Plus.quasiIso A).inverseImage (plusInjΦFunctor A)
      ≤ MorphismProperty.isomorphisms _ := by
    intro X Y f hf
    rw [MorphismProperty.inverseImage_iff, HomotopyCategory.Plus.quasiIso_iff] at hf
    rw [MorphismProperty.isomorphisms.iff]
    have hkinj : IsIso ((HomotopyCategory.Plus.ι A).map ((plusInjΦFunctor A).map f)) := by
      -- reflect the underlying complex-level homotopy equivalence into `K(A)`.
      have hgen : ∀ (SX SY : HomotopyCategory A (ComplexShape.up ℤ)) (g₀ : SX ⟶ SY),
          CochainComplex.IsKInjective SX.as → CochainComplex.IsKInjective SY.as →
          HomotopyCategory.quasiIso A (ComplexShape.up ℤ) g₀ → IsIso g₀ := by
        intro SX SY g₀ hgX hgY hg₀
        obtain ⟨SX, rfl⟩ := HomotopyCategory.quotient_obj_surjective SX
        obtain ⟨SY, rfl⟩ := HomotopyCategory.quotient_obj_surjective SY
        obtain ⟨g, rfl⟩ := (HomotopyCategory.quotient _ _).map_surjective g₀
        simp only [HomotopyCategory.quotient_obj_as] at hgX hgY
        have := hgX
        have := hgY
        have hg : QuasiIso g := by rwa [HomotopyCategory.quotient_map_mem_quasiIso_iff] at hg₀
        obtain ⟨e, rfl⟩ := (CochainComplex.IsKInjective.quasiIso_iff g).1 hg
        exact (HomotopyCategory.isoOfHomotopyEquiv e).isIso_hom
      exact hgen _ _ _ X.2 Y.2 hf
    have h2 : IsIso ((plusInjΦFunctor A).map f) :=
      (HomotopyCategory.Plus.fullyFaithfulι A).isIso_of_isIso_map _
    have h3 : IsIso ((plusInjective A).ι.map f) := h2
    exact (plusInjective A).fullyFaithfulι.isIso_of_isIso_map _
  -- `J` is therefore a localization of `K^+(Inj A)` at `W₁`, so `Φ` is a localized equivalence.
  have hid : (Functor.id _).IsLocalization
      ((HomotopyCategory.Plus.quasiIso A).inverseImage (plusInjΦFunctor A)) :=
    Functor.IsLocalization.for_id _ hW1
  have hJloc : J.IsLocalization
      ((HomotopyCategory.Plus.quasiIso A).inverseImage (plusInjΦFunctor A)) :=
    Functor.IsLocalization.of_equivalence_target (Functor.id _) _ J J.asEquivalence
      (Functor.leftUnitor _)
  exact LocalizerMorphism.IsLocalizedEquivalence.of_isLocalization_of_isLocalization (plusInjΦ A) Q

/-- The injective derivability structure (Stacks 05TG), assembled from (B2)–(B4) plus the
automatic `W₂.ContainsIdentities` via `IsRightDerivabilityStructure.mk'`. -/
@[sga "4½ Etat_0 4.2.3.1" "Corollary 1"]
instance plusInjΦ_isRightDerivabilityStructure (A : Type*) [Category A] [Abelian A]
    [EnoughInjectives A] : (plusInjΦ A).IsRightDerivabilityStructure :=
  LocalizerMorphism.IsRightDerivabilityStructure.mk' (plusInjΦ A)

/-- The localizer morphism `Φ` *derives* every functor out of `K^{+}(A)`: the
quasi-isomorphisms `W₁` on `K^{+}(Inj A)` are inverted by `Φ.functor ⋙ F` for an
arbitrary `F`.

Proof (Stacks 05TH; uses only `CochainComplex.IsKInjective.quasiIso_iff`): let
`f : X ⟶ Y` be a morphism of `K^{+}(Inj A)` with `W₁ f`, i.e. `Φ.functor.map f` is a
quasi-isomorphism in `K^{+}(A)`.  Its underlying morphism is a quasi-isomorphism of
cochain complexes between two K-injective complexes `X.as`, `Y.as`.  By
`CochainComplex.IsKInjective.quasiIso_iff`, such a quasi-isomorphism is a homotopy
equivalence, hence becomes an **isomorphism in the homotopy category** `K(A)`, and
therefore in the full subcategory `K^{+}(A)`.  So `Φ.functor.map f` is an isomorphism;
any functor `F` preserves isomorphisms, whence `(Φ.functor ⋙ F).map f = F.map
(Φ.functor.map f)` is an isomorphism.  This is exactly `W₁.IsInvertedBy (Φ.functor ⋙ F)`. -/
theorem plusInjΦ_derives {A : Type*} [Category A] [Abelian A]
    {H : Type*} [Category H] (F : HomotopyCategory.Plus A ⥤ H) :
    (plusInjΦ A).Derives F := by
  -- `Derives` is definitionally `W₁.IsInvertedBy (Φ.functor ⋙ F)`.
  intro X Y f hf
  rw [MorphismProperty.inverseImage_iff, HomotopyCategory.Plus.quasiIso_iff] at hf
  have hkinj : IsIso ((HomotopyCategory.Plus.ι A).map ((plusInjΦFunctor A).map f)) := by
    have hgen : ∀ (SX SY : HomotopyCategory A (ComplexShape.up ℤ)) (g₀ : SX ⟶ SY),
        CochainComplex.IsKInjective SX.as → CochainComplex.IsKInjective SY.as →
        HomotopyCategory.quasiIso A (ComplexShape.up ℤ) g₀ → IsIso g₀ := by
      intro SX SY g₀ hgX hgY hg₀
      obtain ⟨SX, rfl⟩ := HomotopyCategory.quotient_obj_surjective SX
      obtain ⟨SY, rfl⟩ := HomotopyCategory.quotient_obj_surjective SY
      obtain ⟨g, rfl⟩ := (HomotopyCategory.quotient _ _).map_surjective g₀
      simp only [HomotopyCategory.quotient_obj_as] at hgX hgY
      have := hgX
      have := hgY
      have hg : QuasiIso g := by rwa [HomotopyCategory.quotient_map_mem_quasiIso_iff] at hg₀
      obtain ⟨e, rfl⟩ := (CochainComplex.IsKInjective.quasiIso_iff g).1 hg
      exact (HomotopyCategory.isoOfHomotopyEquiv e).isIso_hom
    exact hgen _ _ _ X.2 Y.2 hf
  have h2 : IsIso ((plusInjΦFunctor A).map f) :=
    (HomotopyCategory.Plus.fullyFaithfulι A).isIso_of_isIso_map _
  have hiso : IsIso ((plusInjΦ A).functor.map f) := h2
  rw [Functor.comp_map]
  exact F.map_isIso _

/-- **Generic existence result.**  For an abelian category `A` with enough injectives and
*any* functor `F : K^{+}(A) ⥤ H` (to an arbitrary category `H`), the right derived functor
of `F` with respect to `Qis^{+}(A)` is everywhere defined.

This is the common core of both statements of Tag 05TI. No triangulated hypothesis
on `F` or `H` is needed: the injective derivability structure
(`plusInjΦ_isRightDerivabilityStructure`) and `Φ.Derives F` (`plusInjΦ_derives`) give a
pointwise right derived functor directly via
`LocalizerMorphism.Derives.hasPointwiseRightDerivedFunctor`. Pointwise existence is the
formal meaning of "everywhere defined" used in the source. -/
theorem hasPointwiseRightDerivedFunctor_of_enoughInjectives
    {A : Type*} [Category A] [Abelian A]
    [EnoughInjectives A] {H : Type*} [Category H] (F : HomotopyCategory.Plus A ⥤ H) :
    F.HasPointwiseRightDerivedFunctor (HomotopyCategory.Plus.quasiIso A) :=
  (plusInjΦ_derives F).hasPointwiseRightDerivedFunctor

-- Main Statement(s)

/-- **Statement 1 (Stacks Tag 05TI, part 1).** Let `A` be an abelian category with enough
injectives. For every triangulated category `D` and every exact (triangulated) functor
`F : K^{+}(A) ⥤ D`, the right derived functor `RF : D^{+}(A) ⥤ D` of `F` with respect to
the quasi-isomorphisms is everywhere defined. -/
@[stacks 05TI "(1)", sga "4 XVII 1.2.7" "enough injectives (RF)"]
theorem hasPointwiseRightDerivedFunctor_of_isTriangulated {A : Type*} [Category A] [Abelian A]
  [EnoughInjectives A]
    {D : Type*} [Category D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
    [∀ (n : ℤ), (shiftFunctor D n).Additive] [Pretriangulated D]
    (F : HomotopyCategory.Plus A ⥤ D) [F.CommShift ℤ] [F.IsTriangulated] :
    F.HasPointwiseRightDerivedFunctor (HomotopyCategory.Plus.quasiIso A) :=
  -- The exact/triangulated hypotheses on `F` are not needed for existence; apply the
  -- generic existence result directly.
  hasPointwiseRightDerivedFunctor_of_enoughInjectives F

/-- **Statement 2 (Stacks Tag 05TI, part 2).** Let `A` be an abelian category with enough
injectives. For every abelian category `B` and every additive functor `F : A ⥤ B`, the
right derived functor `RF : D^{+}(A) ⥤ D^{+}(B)` of the composite
`K^{+}(F) ⋙ Q^{+}_{B} : K^{+}(A) ⥤ D^{+}(B)` is everywhere defined. -/
@[stacks 05TI "(2)",
  ega "0 13.6.1" "existence of R^pT",
  sga "4 XVII 1.2.7" "enough injectives (RF)"]
theorem hasPointwiseRightDerivedFunctor_mapPlus {A B : Type*} [Category A] [Abelian A]
  [EnoughInjectives A]
    [Category B] [Abelian B]
    (F : A ⥤ B) [F.Additive] :
    (mapPlus F ⋙ (HomotopyCategory.Plus.quasiIso B).Q).HasPointwiseRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso A) :=
  -- Statement 2 is the generic existence result applied to the concrete (merely additive)
  -- functor `mapPlus F ⋙ Q^{+}_{B} : K^{+}(A) ⥤ D^{+}(B)`.
  hasPointwiseRightDerivedFunctor_of_enoughInjectives _
