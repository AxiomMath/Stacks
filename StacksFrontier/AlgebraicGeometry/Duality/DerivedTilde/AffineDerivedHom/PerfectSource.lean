module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import StacksFrontier.AlgebraicGeometry.InternalHomTilde.Basic
public import StacksFrontier.AlgebraicGeometry.Modules.AffineInternalHom
public import StacksFrontier.AlgebraicGeometry.Modules.TildeExactness
public import StacksFrontier.CategoryTheory.IsoNaturality
public import StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.HomComplexComparison
public import StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.HomComplexComparisonNaturality
public import StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.StrictlyPerfectHomFiniteFree
public import StacksFrontier.Homology.HomComplex.ProjectiveRHom
public import StacksFrontier.Homology.Perfect.Defs
public import StacksFrontier.Homology.PseudoCoherentRelative.TildeExact
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedInternalHom
public import StacksFrontier.AlgebraicGeometry.ModuleSpecGammaAdditive
import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.AffineDerivedHom.HomComplexTilde
import all StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.AffineDerivedHom.HomComplexTilde

/-!
# Derived internal Hom out of a perfect complex on an affine scheme

Let `R` be a commutative ring and `X = Spec R`. Sheafification `M ↦ M̃` is exact, so it
descends to derived sheafification `D(R) ⥤ D(𝒪_X)`. This file proves clause (3)(b) of
[Stacks, Tag 0A6H]: for `K` a *perfect* object of `D(R)` and `L` an arbitrary one there is a
canonical isomorphism

`R𝓗om_{𝒪_X}(K̃, L̃)  ≅  (R Hom_R(K, L))~`

in `D(𝒪_X)`, with no boundedness hypothesis on `L`.

The proof replaces `K` by a bounded complex `P` of finite projective `R`-modules. There both
sides are computed by ordinary Hom complexes: on the sheaf side because `P̃` is strictly
perfect, so [Stacks, Tag 08JH] applies, and on the module side by [Stacks, Tag 0A66] for a
bounded-above complex of projectives. The comparison is then the complex-level affine
comparison `AlgebraicGeometry.affineHomComplexTildeIso` of
`StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.AffineDerivedHom.HomComplexTilde`, which is
the totalisation of the degreewise affine comparison `SheafHom(M̃, Ñ) ≅ Hom_R(M, N)~` of
[Stacks, Tag 01I8].

## Main definitions

* `AlgebraicGeometry.affinePerfectDerivedSheafHomIso`: clause (3)(b) itself.

## Main results

* `AlgebraicGeometry.tilde_isFiniteFreeSummand` and
  `AlgebraicGeometry.tildeComplex_bounded_isFiniteFreeSummand`: the sheafification of a finite
  projective module is a direct summand of a finite free `𝒪_X`-module, which is the termwise
  half of strict perfectness of `P̃`.
* `AlgebraicGeometry.affinePerfectDerivedSheafHomIso_model` identifies the derived comparison
  on a bounded finite-projective representative with the sheafified ordinary comparison, which
  is what makes the derived isomorphism canonical rather than arbitrary.
* `AlgebraicGeometry.affinePerfectDerivedSheafHomIso_natural_left` and `_natural_right` give
  naturality in the two arguments.

## Implementation notes

**Strict perfectness is spelled by `IsFiniteFreeSummand`.** The predicate
`Stacks.StrictlyPerfect.IsStrictlyPerfect` of [Stacks, Tag 08FL] is universe-monomorphic and
cannot be named at `RingedSite.{u, u, u}`, so the 08JH comparison takes boundedness together
with `AlgebraicGeometry.RingedSite.IsFiniteFreeSummand` on every term. Those are exactly the
two clauses of 08FL, and `tilde_isFiniteFreeSummand` supplies the second one for `P̃`.

**Why the derived half rewrites at default transparency.** The two spellings `Scheme.Modules`
and `SheafOfModules (specSite R).ringSheaf` are the same category, but their `Category`,
`Abelian` and `HasZeroMorphisms` instances are produced by different synthesis paths, so they
are equal only up to unfolding. Terms mixing them — and the statement of clause (3) necessarily
mixes them, since `tilde` is stated for `Scheme.Modules` while the derived internal Hom is
stated for a ringed site — are therefore not type-correct at the `instances` transparency at
which `rewrite` builds its motive. Every rewrite in the derived half is consequently written
`rw (transparency := .default) [...]`, which is the same device
`AlgebraicGeometry.RingedSite.finSuccBiconeIsBilimit` uses. The complex-level half needs none:
it is written entirely in the `Scheme.Modules` spelling.

**The derived comparison is objectwise on models.** The derived statement is obtained by
proving the comparison on the pairs (bounded finite-projective complex, K-injective complex),
checking naturality there by lifting derived morphisms to actual chain maps, and extending
along the essentially surjective functor from those models to all pairs (perfect object,
arbitrary object). That is what makes `affinePerfectDerivedSheafHomIso` natural, and the
normalization `affinePerfectDerivedSheafHomIso_model` is read off from the extension.

**Why there is no amplitude-bound shortcut.** One might expect `R𝓗om_{𝒪_X}(M̃, Ñ)` to be
`IsLE (b - m)` as soon as `M` is `IsGE m` and `N` is `IsLE b`, with no hypothesis on `M`. That
is false. Over `R = ℤ` take `M = N = ℤ/2` in degree zero, so that `m = b = 0`: the first
cohomology sheaf is the sheaf associated to `D(f) ↦ Ext¹_{ℤ[1/f]}(ℤ/2, ℤ/2)`, which is `ℤ/2` at
the point `(2)`, so the asserted bound fails already for `n = 1`. The t-structure input such a
bound needs is the vanishing of `Hom(D^{≥m}, D^{≤m-1})`, whereas what holds is the vanishing of
`Hom(D^{≤n}, D^{≥n+1})`. The correct statement carries an injective-amplitude hypothesis on the
target, as the module-side
`StacksDraft.DerivedHom.derivedHom_isLE_of_isGE_of_injectiveAmplitude` does; and on the sheaf
side that hypothesis is not inherited from the module side, because the sheafification of an
injective module need not be an injective sheaf, by [Stacks, Tag 0CRZ].

## References

* [Stacks Project, Tag 0A6H](https://stacks.math.columbia.edu/tag/0A6H)
* [Stacks Project, Tag 01I8](https://stacks.math.columbia.edu/tag/01I8)
* [Stacks Project, Tag 0CRZ](https://stacks.math.columbia.edu/tag/0CRZ)
* [Stacks Project, Tag 08JH](https://stacks.math.columbia.edu/tag/08JH)
* [Stacks Project, Tag 0A66](https://stacks.math.columbia.edu/tag/0A66)
* [Stacks Project, Tag 08FL](https://stacks.math.columbia.edu/tag/08FL)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open AlgebraicGeometry.RingedSite Stacks.SheafOfModules

universe u

namespace AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard
  AlgebraicGeometry.tilde.preservesFiniteLimits
  Stacks.AffineTilde.preservesFiniteColimits_tildeFunctor

/-! ### Strict perfectness of the sheafification -/

/-- **The termwise half of strict perfectness of `P̃`.** The sheafification of a finite
projective `R`-module is a direct summand of a finite free `𝒪_{Spec R}`-module. -/
public lemma tilde_isFiniteFreeSummand (R : CommRingCat.{u}) (M : ModuleCat.{u} R)
    [Module.Finite R M] [Projective M] :
    IsFiniteFreeSummand (specSite R) ((tilde.functor R).obj M) := by
  obtain ⟨k, f, hf⟩ := Module.Finite.exists_fin' R M
  let eI : ModuleCat.of R (ULift.{u} (Fin k) →₀ R) ≅ ModuleCat.of R (Fin k → R) :=
    ((Finsupp.domLCongr (Equiv.ulift.{u} (α := Fin k))).trans
      (Finsupp.linearEquivFunOnFinite R R (Fin k))).toModuleIso
  have : Epi (ModuleCat.ofHom f) := (ModuleCat.epi_iff_surjective _).mpr hf
  let p : ModuleCat.of R (ULift.{u} (Fin k) →₀ R) ⟶ M := eI.hom ≫ ModuleCat.ofHom f
  have : Epi p := epi_comp _ _
  let r : Retract M (ModuleCat.of R (ULift.{u} (Fin k) →₀ R)) :=
    ⟨Projective.factorThru (𝟙 M) p, p, Projective.factorThru_comp _ _⟩
  exact isFiniteFreeSummand_of_retract_free (specSite R) (ULift.{u} (Fin k))
    ((r.map (tilde.functor R)).trans
      (Retract.ofIso (tildeFinsupp (R := R) (ULift.{u} (Fin k)))))

/-- **Strict perfectness of `P̃`, in the spelling [Stacks, Tag 08JH] consumes.** For `P` a
bounded complex of finite projective `R`-modules, the sheafified complex `P̃` is bounded with
every term a direct summand of a finite free `𝒪_{Spec R}`-module. -/
public lemma tildeComplex_bounded_isFiniteFreeSummand (R : CommRingCat.{u})
    (P : CochainComplex (ModuleCat.{u} R) ℤ)
    [∀ i, Module.Finite R (P.X i)] [∀ i, Projective (P.X i)]
    (hP : {i : ℤ | ¬ IsZero (P.X i)}.Finite) :
    {i : ℤ | ¬ IsZero (((tildeCx R).obj P).X i)}.Finite ∧
      ∀ i : ℤ, IsFiniteFreeSummand (specSite R) (((tildeCx R).obj P).X i) :=
  ⟨hP.subset (tildeC_support_subset R P), fun i => tilde_isFiniteFreeSummand R (P.X i)⟩

/-- The canonical global section of a sheafification is natural in the module. -/
private lemma tilde_toOpen_map_app_apply {R : CommRingCat.{u}} {M N : ModuleCat.{u} R}
    (h : M ⟶ N) (α : M) :
    (tilde.map h).val.app (op (⊤ : Opens (PrimeSpectrum.Top R)))
        (tilde.toOpen M ⊤ α) = tilde.toOpen N ⊤ (h.hom α) :=
  ConcreteCategory.congr_hom (tilde.toOpen_map_app h ⊤) α

/-- **The complex-level comparison is natural.** Its inverse intertwines the sheafification of
the functorial map of module Hom complexes with the canonical map of internal Hom complexes.

Both sides are pinned down by their action on canonical global sections, where
`affineHomComplexTildeIso_inv_toOpen` turns each into the sheaf map induced by the components
of the cochain and `AlgebraicGeometry.RingedSite.sectionsIso_homMap_v` turns the right-hand side
into the same pre- and postcomposition. -/
private lemma affineHomComplexTildeIso_inv_naturality (R : CommRingCat.{u})
    (P P' L L' : CochainComplex (ModuleCat.{u} R) ℤ)
    [∀ i, Projective (P.X i)] [∀ i, Module.Finite R (P.X i)]
    [∀ i, Projective (P'.X i)] [∀ i, Module.Finite R (P'.X i)]
    (hP : {i : ℤ | ¬ IsZero (P.X i)}.Finite)
    (hP' : {i : ℤ | ¬ IsZero (P'.X i)}.Finite)
    (f : P' ⟶ P) (g : L ⟶ L') :
    (tildeCx R).map (Stacks.HomComplex.TensorHomComparison.HomCxMap P P' L L' f g) ≫
        (affineHomComplexTildeIso R P' L' hP').inv =
      (affineHomComplexTildeIso R P L hP).inv ≫
        homMap (specSite R) ((tildeCx R).map f) ((tildeCx R).map g) := by
  ext n : 1
  apply tildeHom_ext_globalSections R
  intro α
  apply ((sheafHomComplex (specSite R) ((tildeCx R).obj P')
    ((tildeCx R).obj L')).sectionsEquiv ⊤ n).injective
  apply CochainComplex.HomComplex.Cochain.ext
  intro p q hpq
  refine Eq.trans (congrArg (fun z =>
      (((sheafHomComplex (specSite R) ((tildeCx R).obj P')
          ((tildeCx R).obj L')).sectionsEquiv ⊤ n)
        (((affineHomComplexTildeIso R P' L' hP').inv.f n).val.app (op ⊤) z)).v p q hpq)
    (tilde_toOpen_map_app_apply
      ((Stacks.HomComplex.TensorHomComparison.HomCxMap P P' L L' f g).f n) α)) ?_
  trans (tildeTop R).map (f.f p) ≫ (tildeTop R).map (α.v p q hpq) ≫ (tildeTop R).map (g.f q)
  · refine (affineHomComplexTildeIso_inv_toOpen R P' L' hP' n p q hpq _).trans ?_
    refine (congrArg (fun h => (tildeTop R).map h)
      (Stacks.HomComplex.TensorHomComparison.HomCxMapDeg_v P P' L L' f g n α p q hpq)).trans ?_
    exact ((tildeTop R).map_comp _ _).trans
      (congrArg (fun v => (tildeTop R).map (f.f p) ≫ v) ((tildeTop R).map_comp _ _))
  · refine Eq.trans (congrArg (fun v => (tildeTop R).map (f.f p) ≫ v ≫
      (tildeTop R).map (g.f q))
        (affineHomComplexTildeIso_inv_toOpen R P L hP n p q hpq α).symm) ?_
    exact (sectionsIso_homMap_v (specSite R) ((tildeCx R).map f) ((tildeCx R).map g) ⊤ n p q hpq
      _).symm

/-- A complex that is bounded on both sides has finite support. -/
private lemma finite_support_of_bounds {R : CommRingCat.{u}}
    (P : CochainComplex (ModuleCat.{u} R) ℤ) (a b : ℤ)
    [P.IsStrictlyGE a] [P.IsStrictlyLE b] :
    {i : ℤ | ¬ IsZero (P.X i)}.Finite :=
  (Set.finite_Icc a b).subset fun i hi =>
    ⟨not_lt.1 fun h => hi (P.isZero_of_isStrictlyGE a i h),
      not_lt.1 fun h => hi (P.isZero_of_isStrictlyLE b i h)⟩

/-! ### The derived internal Hom of `Spec R` and its K-injective resolutions -/

/-- The derived internal Hom of `Spec R`, as the datum carrying its K-injective comparison. -/
public abbrev specRHom (R : CommRingCat.{u}) :
    RingedSite.DerivedInternalHom.{u, u + 1} (specSite R) :=
  Stacks.SheafOfModules.derivedInternalHom (Spec R).sheaf

/-- The derived internal Hom of `Spec R` as a functor of the *pair* of its arguments, so that
functoriality in the two variables at once is available from `Functor.map_comp`. -/
private abbrev sheafDerivedHom (R : CommRingCat.{u}) :=
  CategoryTheory.Functor.uncurry.obj (specRHom R).hom

private instance kInjectiveResolution_isKInjective (R : CommRingCat.{u})
    (F : CochainComplex ((Spec R).Modules) ℤ) :
    ((kInjectiveResolution (specSite R)).obj F).IsKInjective :=
  Stacks.Injectives.kInjectiveResolutionFunctor_obj_isKInjective _ F

private instance kInjectiveAugmentation_quasiIso (R : CommRingCat.{u})
    (F : CochainComplex ((Spec R).Modules) ℤ) :
    QuasiIso ((kInjectiveAugmentation (specSite R)).app F) :=
  Stacks.Injectives.kInjectiveResolutionInclusion_quasiIso _ F

private instance isIso_Q_map_kInjectiveAugmentation (R : CommRingCat.{u})
    (F : CochainComplex ((Spec R).Modules) ℤ) :
    IsIso (DerivedCategory.Q.map ((kInjectiveAugmentation (specSite R)).app F)) :=
  (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 inferInstance

/-! ### The derived comparison on models -/

/-- Derived sheafification `D(R) ⥤ D(𝒪_{Spec R})`. -/
public abbrev tildeDer (R : CommRingCat.{u}) :=
  (tilde.functor R).mapDerivedCategory

/-- The sheaf side of clause (3): the derived internal Hom of the two sheafified arguments, as
a functor of the pair. -/
private abbrev affineSheafDerivedHom (R : CommRingCat.{u}) :=
  ((tildeDer R).op.prod (tildeDer R)) ⋙ sheafDerivedHom R

/-- The module side of clause (3): the sheafification of the derived Hom over `R`. -/
private abbrev affineModuleDerivedHom (R : CommRingCat.{u}) :=
  (StacksDraft.DerivedHom.derivedHomAdjunction (R := R)).hom ⋙ tildeDer R

/-- The [Stacks, Tag 08JH] comparison is invertible for the sheafification of a bounded complex of
finite projective modules. -/
private lemma isIso_strictlyPerfectHomComparison_tilde (R : CommRingCat.{u})
    (P L : CochainComplex (ModuleCat.{u} R) ℤ)
    [∀ i, Projective (P.X i)] [∀ i, Module.Finite R (P.X i)]
    (hP : {i : ℤ | ¬ IsZero (P.X i)}.Finite) :
    IsIso (strictlyPerfectHomComparison (specSite R) (specRHom R)
      ((tildeCx R).obj P) ((tildeCx R).obj L)) :=
  strictlyPerfectHomComparison_isIso (specSite R) (specRHom R) _ _
    (tildeComplex_bounded_isFiniteFreeSummand R P hP).1
    (tildeComplex_bounded_isFiniteFreeSummand R P hP).2

/-- **Clause (3)(b) on a bounded finite-projective representative.** Both sides are computed by
ordinary Hom complexes there — the sheaf side by [Stacks, Tag 08JH], the module side by
[Stacks, Tag 0A66] — and the comparison is the complex-level `affineHomComplexTildeIso`. -/
private def affineModelIso (R : CommRingCat.{u})
    (P L : CochainComplex (ModuleCat.{u} R) ℤ) (b : ℤ)
    [P.IsStrictlyLE b] [∀ i, Projective (P.X i)] [∀ i, Module.Finite R (P.X i)]
    (hP : {i : ℤ | ¬ IsZero (P.X i)}.Finite) :
    (affineSheafDerivedHom R).obj
        (op (DerivedCategory.Q.obj P), DerivedCategory.Q.obj L) ≅
      (affineModuleDerivedHom R).obj
        (op (DerivedCategory.Q.obj P), DerivedCategory.Q.obj L) := by
  have := isIso_strictlyPerfectHomComparison_tilde R P L hP
  exact (sheafDerivedHom R).mapIso
      (Iso.prod ((tilde.functor R).mapDerivedCategoryFactors.app P).symm.op
        ((tilde.functor R).mapDerivedCategoryFactors.app L)) ≪≫
    (asIso (strictlyPerfectHomComparison (specSite R) (specRHom R)
      ((tildeCx R).obj P) ((tildeCx R).obj L))).symm ≪≫
    DerivedCategory.Q.mapIso (affineHomComplexTildeIso R P L hP) ≪≫
    ((tilde.functor R).mapDerivedCategoryFactors.app (CochainComplex.HomComplexR R P L)).symm ≪≫
    (tildeDer R).mapIso (StacksDraft.DerivedHom.projectiveHomComparison.iso P L b).symm

/-- Transporting a naturality square along an equality of the morphism. -/
private lemma naturality_of_hom_eq {C D : Type*} [Category* C] [Category* D]
    (F G : C ⥤ D) {Y Z : C} {u v : Y ⟶ Z} (huv : u = v)
    (eY : F.obj Y ⟶ G.obj Y) (eZ : F.obj Z ⟶ G.obj Z)
    (h : F.map u ≫ eZ = eY ≫ G.map u) : F.map v ≫ eZ = eY ≫ G.map v :=
  huv ▸ h

/-- Dropping an identity first factor from a composite in a hypothesis. -/
public lemma comp_eq_of_fst_eq_id {C : Type*} [Category* C] {Y Z W : C}
    {a : Y ⟶ Y} (ha : a = 𝟙 Y) {b : Y ⟶ Z} {c : Z ⟶ W} {d : Y ⟶ W}
    (h : (a ≫ b) ≫ c = d) : b ≫ c = d := by
  simpa only [ha, Category.id_comp] using h

/-- Dropping an identity second factor from a composite in a hypothesis. -/
public lemma comp_eq_of_snd_eq_id {C : Type*} [Category* C] {Y Z W : C}
    {a : Y ⟶ Z} {b : Z ⟶ Z} (hb : b = 𝟙 Z) {c : Z ⟶ W} {d : Y ⟶ W}
    (h : (a ≫ b) ≫ c = d) : a ≫ c = d := by
  simpa only [hb, Category.comp_id] using h

/-- A functor carries a commuting square to a commuting square, with both composites already
expanded. -/
public lemma map_comp_naturality {C D : Type*} [Category* C] [Category* D]
    (F : C ⥤ D) {A B A' B' : C} {u : A ⟶ A'} {v : B ⟶ B'} {a : A ⟶ B} {b : A' ⟶ B'}
    (h : u ≫ b = a ≫ v) : F.map u ≫ F.map b = F.map a ≫ F.map v :=
  (F.map_comp _ _).symm.trans ((congrArg F.map h).trans (F.map_comp _ _))

/-- Pasting five naturality squares into one, for a composite isomorphism with five
factors. -/
private lemma paste_five_squares {C : Type*} [Category* C]
    {S₀ S₁ S₂ S₃ S₄ S₅ T₀ T₁ T₂ T₃ T₄ T₅ : C}
    {u : S₀ ⟶ T₀} {a : S₀ ⟶ S₁} {a' : T₀ ⟶ T₁} {u₁ : S₁ ⟶ T₁}
    {b : S₁ ⟶ S₂} {b' : T₁ ⟶ T₂} {u₂ : S₂ ⟶ T₂}
    {c : S₂ ⟶ S₃} {c' : T₂ ⟶ T₃} {u₃ : S₃ ⟶ T₃}
    {d : S₃ ⟶ S₄} {d' : T₃ ⟶ T₄} {u₄ : S₄ ⟶ T₄}
    {e : S₄ ⟶ S₅} {e' : T₄ ⟶ T₅} {v : S₅ ⟶ T₅}
    (h₁ : u ≫ a' = a ≫ u₁) (h₂ : u₁ ≫ b' = b ≫ u₂) (h₃ : u₂ ≫ c' = c ≫ u₃)
    (h₄ : u₃ ≫ d' = d ≫ u₄) (h₅ : u₄ ≫ e' = e ≫ v) :
    u ≫ a' ≫ b' ≫ c' ≫ d' ≫ e' = (a ≫ b ≫ c ≫ d ≫ e) ≫ v := by
  rw [reassoc_of% h₁, reassoc_of% h₂, reassoc_of% h₃, reassoc_of% h₄, h₅]
  simp only [Category.assoc]

/-- Cancelling the three isomorphism factors surrounding a composite. -/
private lemma cancel_iso_factors {C : Type*} [Category* C]
    {W Y Y₁ Y₂ Z Z' Z'' : C} (p : W ≅ Y) (s : Z ≅ Z') (r : Z' ≅ Z'')
    (A : Y ⟶ Y₁) (B : Y₁ ⟶ Y₂) (m : Y₂ ⟶ Z) (q : W ⟶ Z'')
    (h : A ≫ B ≫ m = p.inv ≫ q ≫ r.inv ≫ s.inv) :
    p.hom ≫ A ≫ B ≫ m ≫ s.hom ≫ r.hom = q := by
  simp [reassoc_of% h]

/-! Turning a naturality square for the forward directions into one for the inverses is
`CategoryTheory.iso_inv_naturality`, imported. -/

/-- The naturality of the model comparison, for actual chain maps in both variables. -/
private lemma affineModelIso_naturality (R : CommRingCat.{u})
    (P P' L L' : CochainComplex (ModuleCat.{u} R) ℤ) (b b' : ℤ)
    [P.IsStrictlyLE b] [P'.IsStrictlyLE b']
    [∀ i, Projective (P.X i)] [∀ i, Module.Finite R (P.X i)]
    [∀ i, Projective (P'.X i)] [∀ i, Module.Finite R (P'.X i)]
    (hP : {i : ℤ | ¬ IsZero (P.X i)}.Finite)
    (hP' : {i : ℤ | ¬ IsZero (P'.X i)}.Finite)
    (f : P' ⟶ P) (g : L ⟶ L') :
    (affineSheafDerivedHom R).map ((DerivedCategory.Q.map f).op, DerivedCategory.Q.map g) ≫
        (affineModelIso R P' L' b' hP').hom =
      (affineModelIso R P L b hP).hom ≫
        (affineModuleDerivedHom R).map
          ((DerivedCategory.Q.map f).op, DerivedCategory.Q.map g) := by
  have := isIso_strictlyPerfectHomComparison_tilde R P L hP
  have := isIso_strictlyPerfectHomComparison_tilde R P' L' hP'
  let S := sheafDerivedHom R
  let c := (tilde.functor R).mapDerivedCategoryFactors
  let e := CategoryTheory.Functor.isoWhiskerRight
    (NatIso.prod (NatIso.op c.symm) c) S
  have h₁ := e.hom.naturality (show (op P, L) ⟶ (op P', L') from (f.op, g))
  have h₂ := iso_inv_naturality
    (asIso (strictlyPerfectHomComparison (specSite R) (specRHom R)
      ((tildeCx R).obj P) ((tildeCx R).obj L)))
    (asIso (strictlyPerfectHomComparison (specSite R) (specRHom R)
      ((tildeCx R).obj P') ((tildeCx R).obj L')))
    _ _ (RingedSite.strictlyPerfectHomComparison_naturality (specSite R) (specRHom R)
      ((tildeCx R).obj P) ((tildeCx R).obj P') ((tildeCx R).obj L) ((tildeCx R).obj L')
      ((tildeCx R).map f) ((tildeCx R).map g))
  have h₃ := map_comp_naturality DerivedCategory.Q
    (iso_inv_naturality (affineHomComplexTildeIso R P L hP).symm
      (affineHomComplexTildeIso R P' L' hP').symm _ _
      (affineHomComplexTildeIso_inv_naturality R P P' L L' hP hP' f g))
  have h₄ := c.inv.naturality
    (Stacks.HomComplex.TensorHomComparison.HomCxMap P P' L L' f g)
  have h₅ := map_comp_naturality (tildeDer R)
    (iso_inv_naturality (StacksDraft.DerivedHom.projectiveHomComparison.iso P L b)
      (StacksDraft.DerivedHom.projectiveHomComparison.iso P' L' b') _ _
      (StacksDraft.DerivedHom.projectiveHomComparison.naturality P P' L L' b b' f g))
  exact paste_five_squares h₁ h₂ h₃ h₄ h₅

/-- The uncurried form of the inverse of the comparison of the two sources, as it appears in
the statement of `affinePerfectDerivedSheafHomIso_model`. -/
private lemma affineModelProdIso_inv (R : CommRingCat.{u})
    (P L : CochainComplex (ModuleCat.{u} R) ℤ) :
    ((sheafDerivedHom R).mapIso
        (Iso.prod ((tilde.functor R).mapDerivedCategoryFactors.app P).symm.op
          ((tilde.functor R).mapDerivedCategoryFactors.app L))).inv =
      ((specRHom R).hom.map ((tilde.functor R).mapDerivedCategoryFactors.hom.app P).op).app
          (DerivedCategory.Q.obj ((tildeCx R).obj L)) ≫
        ((specRHom R).hom.obj (op ((tildeDer R).obj (DerivedCategory.Q.obj P)))).map
          ((tilde.functor R).mapDerivedCategoryFactors.inv.app L) :=
  rfl

/-- Precomposing `affineModelIso` with the source comparison cancels its leading factor. -/
private lemma affineModelIso_comp_hom (R : CommRingCat.{u})
    (P L : CochainComplex (ModuleCat.{u} R) ℤ) (b : ℤ)
    [P.IsStrictlyLE b] [∀ i, Projective (P.X i)] [∀ i, Module.Finite R (P.X i)]
    (hP : {i : ℤ | ¬ IsZero (P.X i)}.Finite)
    (hiso : IsIso (strictlyPerfectHomComparison (specSite R) (specRHom R)
      ((tildeCx R).obj P) ((tildeCx R).obj L))) :
    ((specRHom R).hom.map ((tilde.functor R).mapDerivedCategoryFactors.hom.app P).op).app
          (DerivedCategory.Q.obj ((tildeCx R).obj L)) ≫
        ((specRHom R).hom.obj (op ((tildeDer R).obj (DerivedCategory.Q.obj P)))).map
          ((tilde.functor R).mapDerivedCategoryFactors.inv.app L) ≫
        (affineModelIso R P L b hP).hom =
      (@asIso _ _ _ _ (strictlyPerfectHomComparison (specSite R) (specRHom R)
          ((tildeCx R).obj P) ((tildeCx R).obj L)) hiso).inv ≫
        (DerivedCategory.Q.mapIso (affineHomComplexTildeIso R P L hP)).hom ≫
        ((tilde.functor R).mapDerivedCategoryFactors.app
          (CochainComplex.HomComplexR R P L)).inv ≫
        ((tildeDer R).mapIso
          (StacksDraft.DerivedHom.projectiveHomComparison.iso P L b)).inv :=
  (Category.assoc _ _ _).symm.trans
    ((congrArg (fun u => u ≫ (affineModelIso R P L b hP).hom)
      (affineModelProdIso_inv R P L).symm).trans (Iso.inv_hom_id_assoc _ _))

/-! ### Extension from the models -/

/-- A derived morphism out of a K-projective complex is the class of a chain map. -/
public lemma Q_map_surjective_of_isKProjective {C : Type*} [Category* C] [Abelian C]
    [HasDerivedCategory C] (P L : CochainComplex C ℤ) [P.IsKProjective] :
    Function.Surjective (DerivedCategory.Q.map : (P ⟶ L) → _) := by
  intro f
  obtain ⟨g, hg⟩ := (CochainComplex.IsKProjective.Qh_map_bijective P
    ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj L)).surjective
    ((DerivedCategory.quotientCompQhIso C).hom.app P ≫ f ≫
      (DerivedCategory.quotientCompQhIso C).inv.app L)
  obtain ⟨g, rfl⟩ := (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map_surjective g
  refine ⟨g, ?_⟩
  apply (cancel_epi ((DerivedCategory.quotientCompQhIso C).hom.app P)).mp
  rw [← DerivedCategory.quotientCompQhIso_hom_naturality, hg]
  simp

/-- A derived morphism into a K-injective complex is the class of a chain map. -/
public lemma Q_map_surjective_of_isKInjective {C : Type*} [Category* C] [Abelian C]
    [HasDerivedCategory C] (P I : CochainComplex C ℤ) [I.IsKInjective] :
    Function.Surjective (DerivedCategory.Q.map : (P ⟶ I) → _) := by
  intro f
  obtain ⟨g, hg⟩ := (CochainComplex.IsKInjective.Qh_map_bijective
    ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj P) I).surjective
    ((DerivedCategory.quotientCompQhIso C).hom.app P ≫ f ≫
      (DerivedCategory.quotientCompQhIso C).inv.app I)
  obtain ⟨g, rfl⟩ := (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map_surjective g
  refine ⟨g, ?_⟩
  apply (cancel_epi ((DerivedCategory.quotientCompQhIso C).hom.app P)).mp
  rw [← DerivedCategory.quotientCompQhIso_hom_naturality, hg]
  simp

/-- A bounded-above complex of finite projective modules representing a perfect object, with
all the data the model comparison needs. -/
private structure PerfectModel (R : CommRingCat.{u}) where
  /-- The representing complex. -/
  complex : CochainComplex (ModuleCat.{u} R) ℤ
  /-- An upper bound for its support. -/
  bound : ℤ
  /-- The complex vanishes above `bound`. -/
  upper : complex.IsStrictlyLE bound
  /-- Every term is projective. -/
  projective : ∀ i, Projective (complex.X i)
  /-- Every term is a finite module. -/
  finite : ∀ i, Module.Finite R (complex.X i)
  /-- The complex has finite support. -/
  bdd : {i : ℤ | ¬ IsZero (complex.X i)}.Finite
  /-- Its class in the derived category is perfect. -/
  perfect : StacksDraft.Perfect.IsPerfect (DerivedCategory.Q.obj complex)

attribute [local instance] PerfectModel.upper PerfectModel.projective PerfectModel.finite

/-- The full subcategory of perfect objects of `D(R)`. -/
private abbrev PerfectObjects (R : CommRingCat.{u}) :=
  ObjectProperty.FullSubcategory (StacksDraft.Perfect.IsPerfect (R := R))

/-- The inclusion of pairs (perfect object, arbitrary object) into all pairs. -/
private abbrev perfectPairInclusion (R : CommRingCat.{u}) :=
  (ObjectProperty.ι (StacksDraft.Perfect.IsPerfect (R := R))).op.prod
    (𝟭 (DerivedCategory (ModuleCat.{u} R)))

/-- The models: a bounded finite-projective representative of the source together with a
K-injective representative of the target. -/
private abbrev affineModels (R : CommRingCat.{u}) :=
  PerfectModel R × {I : CochainComplex (ModuleCat.{u} R) ℤ // I.IsKInjective}

private abbrev affineModelObject (R : CommRingCat.{u}) (A : affineModels R) :
    (PerfectObjects R)ᵒᵖ × DerivedCategory (ModuleCat.{u} R) :=
  (op ⟨DerivedCategory.Q.obj A.1.complex, A.1.perfect⟩, DerivedCategory.Q.obj A.2.val)

private abbrev affineModelsFunctor (R : CommRingCat.{u}) :=
  inducedFunctor (affineModelObject R)

private lemma affineModelsFunctor_essSurj (R : CommRingCat.{u}) :
    (affineModelsFunctor R).EssSurj := by
  constructor
  rintro ⟨K, L⟩
  obtain ⟨P, a, b, ha, hb, hfin, hproj, ⟨eP⟩⟩ := K.unop.property
  have (i : ℤ) : Projective (P.X i) := inferInstance
  let p : PerfectModel R :=
    ⟨P, b, hb, inferInstance, hfin, finite_support_of_bounds P a b,
      ⟨P, a, b, ha, hb, hfin, hproj, ⟨Iso.refl _⟩⟩⟩
  obtain ⟨I, i, hi, hI⟩ := CochainComplex.exists_quasiIso_isKInjective
    (DerivedCategory.Q.objPreimage L)
  let eI : DerivedCategory.Q.obj I ≅ L :=
    (asIso (DerivedCategory.Q.map i)).symm ≪≫ DerivedCategory.Q.objObjPreimageIso L
  exact ⟨(p, ⟨I, hI⟩),
    ⟨Iso.prod (ObjectProperty.isoMk (StacksDraft.Perfect.IsPerfect (R := R)) eP).op eI⟩⟩

/-- A natural isomorphism given on the image of an essentially surjective functor extends. -/
private def extendNatIso {C D E : Type*} [Category* C] [Category* D] [Category* E]
    (J : C ⥤ D) [J.EssSurj] (F G : D ⥤ E)
    (e : ∀ Y, F.obj (J.obj Y) ≅ G.obj (J.obj Y))
    (he : ∀ {Y Z} (f : J.obj Y ⟶ J.obj Z), F.map f ≫ (e Z).hom = (e Y).hom ≫ G.map f) :
    F ≅ G :=
  NatIso.ofComponents (fun Y => F.mapIso (J.objObjPreimageIso Y).symm ≪≫
    e (J.objPreimage Y) ≪≫ G.mapIso (J.objObjPreimageIso Y)) (by
      intro Y Z f
      have h := he ((J.objObjPreimageIso Y).hom ≫ f ≫ (J.objObjPreimageIso Z).inv)
      apply (cancel_epi (F.map (J.objObjPreimageIso Y).hom)).mp
      dsimp
      simp only [Category.assoc, ← F.map_comp_assoc, Iso.hom_inv_id,
        CategoryTheory.Functor.map_id, Category.id_comp]
      rw [reassoc_of% h]
      simp only [← G.map_comp, Category.assoc, Iso.inv_hom_id, Category.comp_id])

private theorem extendNatIso_app {C D E : Type*} [Category* C] [Category* D] [Category* E]
    (J : C ⥤ D) [J.EssSurj] (F G : D ⥤ E)
    (e : ∀ Y, F.obj (J.obj Y) ≅ G.obj (J.obj Y))
    (he : ∀ {Y Z} (f : J.obj Y ⟶ J.obj Z), F.map f ≫ (e Z).hom = (e Y).hom ≫ G.map f)
    (Y : C) : (extendNatIso J F G e he).hom.app (J.obj Y) = (e Y).hom := by
  dsimp [extendNatIso]
  rw [reassoc_of% he (J.objObjPreimageIso (J.obj Y)).inv]
  simp only [← G.map_comp, Iso.inv_hom_id, Category.comp_id, CategoryTheory.Functor.map_id]

/-- The model comparison is natural for every morphism between the chosen models, by lifting
the derived morphisms to actual chain maps. -/
private lemma affineModelIso_naturality_models (R : CommRingCat.{u})
    {A B : affineModels R}
    (f : (affineModelsFunctor R).obj A ⟶ (affineModelsFunctor R).obj B) :
    (perfectPairInclusion R ⋙ affineSheafDerivedHom R).map f ≫
        (affineModelIso R B.1.complex B.2.val B.1.bound B.1.bdd).hom =
      (affineModelIso R A.1.complex A.2.val A.1.bound A.1.bdd).hom ≫
        (perfectPairInclusion R ⋙ affineModuleDerivedHom R).map f := by
  have := B.2.property
  have := CochainComplex.isKProjective_of_projective B.1.complex B.1.bound
  obtain ⟨k, hk⟩ := Q_map_surjective_of_isKProjective B.1.complex A.1.complex f.1.unop.hom
  obtain ⟨g, hg⟩ := Q_map_surjective_of_isKInjective A.2.val B.2.val f.2
  have h := affineModelIso_naturality R A.1.complex B.1.complex A.2.val B.2.val
    A.1.bound B.1.bound A.1.bdd B.1.bdd k g
  have hm : (((DerivedCategory.Q.map k).op, DerivedCategory.Q.map g) :
        (op (DerivedCategory.Q.obj A.1.complex), DerivedCategory.Q.obj A.2.val) ⟶
          (op (DerivedCategory.Q.obj B.1.complex), DerivedCategory.Q.obj B.2.val)) =
      (f.1.unop.hom.op, f.2) := by rw [hk, hg]
  exact naturality_of_hom_eq (affineSheafDerivedHom R) (affineModuleDerivedHom R) hm _ _ h

/-- The comparison of the two bifunctors on pairs (perfect object, arbitrary object). -/
private def affinePerfectComparison (R : CommRingCat.{u}) :
    perfectPairInclusion R ⋙ affineSheafDerivedHom R ≅
      perfectPairInclusion R ⋙ affineModuleDerivedHom R :=
  have := affineModelsFunctor_essSurj R
  extendNatIso (affineModelsFunctor R) _ _
    (fun A => affineModelIso R A.1.complex A.2.val A.1.bound A.1.bdd)
    (fun {_ _} f => affineModelIso_naturality_models R f)

private lemma affinePerfectComparison_app_model (R : CommRingCat.{u})
    (P I : CochainComplex (ModuleCat.{u} R) ℤ) (b : ℤ)
    [P.IsStrictlyLE b] [∀ i, Projective (P.X i)] [∀ i, Module.Finite R (P.X i)]
    [I.IsKInjective]
    (hP : {i : ℤ | ¬ IsZero (P.X i)}.Finite)
    (hK : StacksDraft.Perfect.IsPerfect (DerivedCategory.Q.obj P)) :
    (affinePerfectComparison R).hom.app
        (op ⟨DerivedCategory.Q.obj P, hK⟩, DerivedCategory.Q.obj I) =
      (affineModelIso R P I b hP).hom := by
  let p : PerfectModel R := ⟨P, b, inferInstance, inferInstance, inferInstance, hP, hK⟩
  have := affineModelsFunctor_essSurj R
  exact extendNatIso_app (affineModelsFunctor R)
    (perfectPairInclusion R ⋙ affineSheafDerivedHom R)
    (perfectPairInclusion R ⋙ affineModuleDerivedHom R)
    (fun A => affineModelIso R A.1.complex A.2.val A.1.bound A.1.bdd)
    (fun {_ _} f => affineModelIso_naturality_models R f) (p, ⟨I, inferInstance⟩)

private lemma affinePerfectComparison_app (R : CommRingCat.{u})
    (P L : CochainComplex (ModuleCat.{u} R) ℤ) (b : ℤ)
    [P.IsStrictlyLE b] [∀ i, Projective (P.X i)] [∀ i, Module.Finite R (P.X i)]
    (hP : {i : ℤ | ¬ IsZero (P.X i)}.Finite)
    (hK : StacksDraft.Perfect.IsPerfect (DerivedCategory.Q.obj P)) :
    (affinePerfectComparison R).hom.app
        (op ⟨DerivedCategory.Q.obj P, hK⟩, DerivedCategory.Q.obj L) =
      (affineModelIso R P L b hP).hom := by
  obtain ⟨I, i, hi, hI⟩ := CochainComplex.exists_quasiIso_isKInjective L
  let k : PerfectObjects R := ⟨DerivedCategory.Q.obj P, hK⟩
  let m : (op k, DerivedCategory.Q.obj L) ⟶ (op k, DerivedCategory.Q.obj I) :=
    (𝟙 _, DerivedCategory.Q.map i)
  have : IsIso m := (isIso_prod_iff _ _).mpr ⟨inferInstance, inferInstance⟩
  have h := (affinePerfectComparison R).hom.naturality m
  rw [affinePerfectComparison_app_model R P I b hP hK] at h
  have hn := affineModelIso_naturality R P P L I b b hP hP (𝟙 P) i
  simp only [CategoryTheory.Functor.map_id, op_id] at hn
  exact (cancel_mono ((perfectPairInclusion R ⋙ affineModuleDerivedHom R).map m)).mp
    (h.symm.trans hn)

/-! ### Clause (3)(b) -/

/-- **Stacks 0A6H, clause (3), case (b).** Let `R` be a commutative ring, `X = Spec R`, and let
`K`, `L` be objects of `D(R)` with `K` perfect. Then the derived internal Hom of the derived
sheafifications is the derived sheafification of the derived Hom over `R`:

`R𝓗om_{𝒪_X}(K̃, L̃)  ≅  (R Hom_R(K, L))~`.

The object `L` is arbitrary. The isomorphism is not an arbitrary one: it is
pinned down on bounded finite-projective representatives by
`affinePerfectDerivedSheafHomIso_model`, and it is natural in both arguments by
`affinePerfectDerivedSheafHomIso_natural_left` and `_natural_right`. -/
@[stacks 0A6H "(3)(b) K perfect and L arbitrary", no_expose]
public def affinePerfectDerivedSheafHomIso (R : CommRingCat.{u})
    (K L : DerivedCategory (ModuleCat.{u} R))
    (hK : StacksDraft.Perfect.IsPerfect K) :
    ((Stacks.SheafOfModules.derivedSheafHom (Spec R).sheaf).obj
        (op ((tildeDer R).obj K))).obj ((tildeDer R).obj L) ≅
      (tildeDer R).obj
        ((StacksDraft.DerivedHom.derivedHomAdjunction (R := R)).hom.obj (op K, L)) :=
  (affinePerfectComparison R).app (op ⟨K, hK⟩, L)

/-- **The normalization of clause (3)(b).** On a bounded complex `P` of finite projective
modules the comparison is the sheafification of the ordinary Hom-complex comparison
`affineHomComplexTildeIso`, read through the [Stacks, Tag 08JH] comparison on the sheaf side and
the [Stacks, Tag 0A66] comparison on the module side. This identifies the isomorphism, not just
its source and target. -/
@[stacks 0A6H "(3)(b) K perfect and L arbitrary"]
public theorem affinePerfectDerivedSheafHomIso_model (R : CommRingCat.{u})
    (P L : CochainComplex (ModuleCat.{u} R) ℤ) (b : ℤ)
    [P.IsStrictlyLE b] [∀ i, Projective (P.X i)] [∀ i, Module.Finite R (P.X i)]
    (hP : {i : ℤ | ¬ IsZero (P.X i)}.Finite)
    (hK : StacksDraft.Perfect.IsPerfect (DerivedCategory.Q.obj P)) :
    strictlyPerfectHomComparison (specSite R) (specRHom R)
          ((tildeCx R).obj P) ((tildeCx R).obj L) ≫
        ((specRHom R).hom.map ((tilde.functor R).mapDerivedCategoryFactors.hom.app P).op).app
          (DerivedCategory.Q.obj ((tildeCx R).obj L)) ≫
        ((specRHom R).hom.obj (op ((tildeDer R).obj (DerivedCategory.Q.obj P)))).map
          ((tilde.functor R).mapDerivedCategoryFactors.inv.app L) ≫
        (affinePerfectDerivedSheafHomIso R (DerivedCategory.Q.obj P)
          (DerivedCategory.Q.obj L) hK).hom ≫
        (tildeDer R).map (StacksDraft.DerivedHom.projectiveHomComparison.iso P L b).hom ≫
        (tilde.functor R).mapDerivedCategoryFactors.hom.app
          (CochainComplex.HomComplexR R P L) =
      (DerivedCategory.Q.mapIso (affineHomComplexTildeIso R P L hP)).hom := by
  have hiso := isIso_strictlyPerfectHomComparison_tilde R P L hP
  rw [show (affinePerfectDerivedSheafHomIso R (DerivedCategory.Q.obj P)
      (DerivedCategory.Q.obj L) hK).hom = (affineModelIso R P L b hP).hom from
    affinePerfectComparison_app R P L b hP hK]
  exact cancel_iso_factors
    (@asIso _ _ _ _ (strictlyPerfectHomComparison (specSite R) (specRHom R)
      ((tildeCx R).obj P) ((tildeCx R).obj L)) hiso)
    ((tildeDer R).mapIso (StacksDraft.DerivedHom.projectiveHomComparison.iso P L b))
    ((tilde.functor R).mapDerivedCategoryFactors.app (CochainComplex.HomComplexR R P L))
    _ _ _ _ (affineModelIso_comp_hom R P L b hP hiso)

/-- **Clause (3)(b) is natural in the target.** -/
@[stacks 0A6H "(3)(b) K perfect and L arbitrary"]
public theorem affinePerfectDerivedSheafHomIso_natural_right (R : CommRingCat.{u})
    (K : DerivedCategory (ModuleCat.{u} R))
    (hK : StacksDraft.Perfect.IsPerfect K)
    {L L' : DerivedCategory (ModuleCat.{u} R)} (g : L ⟶ L') :
    ((Stacks.SheafOfModules.derivedSheafHom (Spec R).sheaf).obj
          (op ((tildeDer R).obj K))).map ((tildeDer R).map g) ≫
        (affinePerfectDerivedSheafHomIso R K L' hK).hom =
      (affinePerfectDerivedSheafHomIso R K L hK).hom ≫
        (tildeDer R).map
          ((StacksDraft.DerivedHom.derivedHomAdjunction (R := R)).hom.map (𝟙 (op K), g)) := by
  have h := (affinePerfectComparison R).hom.naturality
    (show (op (⟨K, hK⟩ : PerfectObjects R), L) ⟶
      (op (⟨K, hK⟩ : PerfectObjects R), L') from (𝟙 _, g))
  change (((specRHom R).hom.map ((tildeDer R).map (𝟙 K)).op).app ((tildeDer R).obj L) ≫
    ((specRHom R).hom.obj (op ((tildeDer R).obj K))).map ((tildeDer R).map g)) ≫
    (affinePerfectDerivedSheafHomIso R K L' hK).hom = _ at h
  have hid : ((specRHom R).hom.map ((tildeDer R).map (𝟙 K)).op).app ((tildeDer R).obj L) = 𝟙 _ :=
    (congrArg (fun u => NatTrans.app ((specRHom R).hom.map u) ((tildeDer R).obj L))
      (congrArg Quiver.Hom.op (CategoryTheory.Functor.map_id (tildeDer R) K))).trans
      (congrArg (fun u => NatTrans.app u ((tildeDer R).obj L))
        (CategoryTheory.Functor.map_id (specRHom R).hom (op ((tildeDer R).obj K))))
  exact comp_eq_of_fst_eq_id hid h

/-- **Clause (3)(b) is contravariantly natural in the perfect source.** -/
@[stacks 0A6H "(3)(b) K perfect and L arbitrary"]
public theorem affinePerfectDerivedSheafHomIso_natural_left (R : CommRingCat.{u})
    {K K' : DerivedCategory (ModuleCat.{u} R)} (f : K' ⟶ K)
    (hK : StacksDraft.Perfect.IsPerfect K)
    (hK' : StacksDraft.Perfect.IsPerfect K')
    (L : DerivedCategory (ModuleCat.{u} R)) :
    ((Stacks.SheafOfModules.derivedSheafHom (Spec R).sheaf).map
          ((tildeDer R).map f).op).app ((tildeDer R).obj L) ≫
        (affinePerfectDerivedSheafHomIso R K' L hK').hom =
      (affinePerfectDerivedSheafHomIso R K L hK).hom ≫
        (tildeDer R).map
          ((StacksDraft.DerivedHom.derivedHomAdjunction (R := R)).hom.map (f.op, 𝟙 L)) := by
  have h := (affinePerfectComparison R).hom.naturality
    (show (op (⟨K, hK⟩ : PerfectObjects R), L) ⟶
      (op (⟨K', hK'⟩ : PerfectObjects R), L) from ((ObjectProperty.homMk f).op, 𝟙 L))
  change (((specRHom R).hom.map ((tildeDer R).map f).op).app ((tildeDer R).obj L) ≫
    ((specRHom R).hom.obj (op ((tildeDer R).obj K'))).map ((tildeDer R).map (𝟙 L))) ≫
    (affinePerfectDerivedSheafHomIso R K' L hK').hom = _ at h
  have hid : ((specRHom R).hom.obj (op ((tildeDer R).obj K'))).map ((tildeDer R).map (𝟙 L)) = 𝟙 _ :=
    (congrArg (fun u => ((specRHom R).hom.obj (op ((tildeDer R).obj K'))).map u)
      (CategoryTheory.Functor.map_id (tildeDer R) L)).trans
      (CategoryTheory.Functor.map_id ((specRHom R).hom.obj (op ((tildeDer R).obj K')))
        ((tildeDer R).obj L))
  exact comp_eq_of_snd_eq_id hid h

end AlgebraicGeometry

end
