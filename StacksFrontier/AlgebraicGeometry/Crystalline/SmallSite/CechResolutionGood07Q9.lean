module

public import StacksFrontier.Algebra.Homology.TotalComplexQuasiIso
public import StacksFrontier.AlgebraicGeometry.Crystalline.Cosimplicial.DoubleComplexRow
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.AffineCohomology
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.ChaoticHigherDirectImage
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.LevelLimitAcyclicity
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Acyclicity.InjectiveSheafSections

/-!
# The Čech double complex of an injective resolution over a system of thickenings

Fix a global crystalline situation `(p, (S, I, γ), X)` and a cosimplicial system
`T(n)_e` of objects of the small crystalline site `Cris(X/S)`, carried, as in
`StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/AffineCohomology.lean`, as a
`CategoryTheory.SimplicialObject (ℕ ⥤ CrystallineThickening S)`.  For an abelian sheaf `F` the
complex `M(0) → M(1) → ⋯` with `M(n) = lim_e F(T(n)_e)` is
`Crystalline.GlobalCrystallineSituation.SmallSite.sectionsComplex T F`.

This file compares that complex for a sheaf `G` with the total complex of the double complex

`(n, a) ↦ lim_e I^a(T(n)_e)`,

`I^•` an injective resolution of `G`: Čech (that is, cosimplicial) in `n`, resolution in `a`.
This is one half of the derived Čech comparison used in the proof of [Stacks, Tag 07Q9]; the
other half maps the sections over an open into the same total complex, and is the reason the
double complex is built as a functor of an *arbitrary* complex of abelian sheaves, not only of
an injective resolution.

The argument is the standard one.  Over an object `A` the complex `I^•(A)` computes the
cohomology of the localized site `Cris(X/S)/A`, so when the higher cohomology of `G|_A`
vanishes (`VanishingOnLevels07Q9`, at the objects `A = T(n)_e`; by the conclusion `Vanishing07JJ`
of [Stacks, Tag 07JJ] this holds when they have affine ambient schemes) the augmented complex
`0 → G(A) → I^0(A) → I^1(A) → ⋯` is exact.  An injective abelian sheaf has surjective
restriction maps along a monomorphism of the site, so when the tower maps `T(n)_e ⟶ T(n)_{e+1}`
are monomorphisms each tower `e ↦ I^a(T(n)_e)` is Mittag-Leffler; if `e ↦ G(T(n)_e)` is too,
[Stacks, Tag 070E] passes the exactness to the limit over `e`, so that every column of the double
complex resolves `M(n) = lim_e G(T(n)_e)`.  [Stacks, Tag 0133] then makes the augmentation a
quasi-isomorphism onto the total complex.

## Main definitions

Everything below lives in the namespace `Crystalline.GlobalCrystallineSituation.SmallSite`.

* `cosimplicialSectionsFunctor`, `sectionsComplexFunctor` — `F ↦ M(•)` and
  `F ↦ (M(0) → M(1) → ⋯)` as functors of the abelian presheaf `F`.
* `cechCosimplicialComplex` — a complex of abelian sheaves `K^•` gives the complex of
  cosimplicial groups `a ↦ (n ↦ lim_e K^a(T(n)_e))`.
* `cechDoubleComplex` — **the double complex `(n, a) ↦ lim_e K^a(T(n)_e)`** over `ℤ × ℤ`, the
  first (outer) index the Čech degree `n` and the second the degree `a` of `K^•`, both extended
  by zero from `ℕ`; `cechDoubleComplexXXIso` identifies its terms.
* `HasAffineMonoLevels` — the hypotheses on `T`: its tower maps are monomorphisms and its
  objects have affine ambient schemes.
* `HasSurjectiveLevelTransitions` — the hypothesis on `G`: its tower restriction maps are onto.
* `VanishingOnLevels07Q9` — the hypothesis on `G`: its higher cohomology vanishes at the level
  objects `T(n)_e`; `vanishingOnLevels07Q9_of_vanishing07JJ` derives it from `Vanishing07JJ`.
* `cechAugmentation` — the augmentation `M(•) ⟶` (row `a = 0`), induced by `G ⟶ I^0`.
* **`cechComparison`** — the comparison `β : M(•) ⟶ Tot(lim_e I^•(T(•)_e))`, a morphism of
  `ℤ`-indexed complexes.

## Main results

* `sectionsResolutionHomologyIso` — `H^n(I^•(A)) ≅ H^n(Cris(X/S)/A, G|_A)`, and
  `exactAt_sections_of_vanishing07JJ`, `exact_sections_resolutionAugmentation` — the augmented
  complex `0 → G(A) → I^•(A)` is exact for `A` affine under `Vanishing07JJ`.
* `surjective_map_of_injective_of_mono`, `hasSurjectiveLevelTransitions_of_injective` — sections
  of an injective abelian sheaf are onto along monomorphisms; `mono_of_mono_targetHom` — a
  morphism of `Cris(X/S)` which is a monomorphism (for instance a closed immersion) on ambient
  schemes is a monomorphism.
* `exactAt_cechRow`, `exact_levelLimit_resolutionAugmentation` — the column of the double
  complex in Čech degree `n` resolves `M(n)`.
* `cechAugmentation_hypotheses` — the hypotheses of [Stacks, Tag 0133].
* **`quasiIso_cechComparison`** — `β` is a quasi-isomorphism, and
  **`cechComparison_naturality`** — it is natural in the pair `(G, I^•)`.

## Implementation notes

The double complex is `Crystalline.cosimplicialDoubleComplexFunctor` of
`StacksFrontier/AlgebraicGeometry/Crystalline/Cosimplicial/DoubleComplex.lean` applied to
`cechCosimplicialComplex T K`, and then flipped, so that its outer index is the Čech degree: that
is the orientation `comparisonMapP` of `StacksFrontier/Algebra/Homology/TotalComplexQuasiIso.lean`
consumes, the complex `M(•)` being resolved column by column.  `HomologicalComplex₂.totalFlipIso`
identifies its total complex with that of the unflipped double complex.

## References

* [Stacks Project, Tag 07Q9](https://stacks.math.columbia.edu/tag/07Q9)
* [Stacks Project, Tag 07JJ](https://stacks.math.columbia.edu/tag/07JJ)
* [Stacks Project, Tag 0133](https://stacks.math.columbia.edu/tag/0133)
* [Stacks Project, Tag 070E](https://stacks.math.columbia.edu/tag/070E)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicTopology Opposite Simplicial

universe u

noncomputable section

namespace Crystalline.GlobalCrystallineSituation.SmallSite

variable {S : GlobalCrystallineSituation.{u}}

/-! ### Sections over an object compute cohomology over it -/

/-- **The sections over an object of an injective resolution compute the cohomology over that
object**: for an injective resolution `I^•` of `G` and an object `A` of `Cris(X/S)`,

`H^n(I^•(A)) ≅ H^n(Cris(X/S)/A, G|_A)`

in every degree `n`.  The left side is the right derived functor of the sections over `A`
computed by `I^•`, and `overCohomologyIsoRightDerivedSections` is the localized-site bridge. -/
def sectionsResolutionHomologyIso (A : CrystallineThickening S)
    {G : Sheaf (smallTopology S) AddCommGrpCat.{u + 1}} (I : InjectiveResolution G) (n : ℕ) :
    (((sectionsFunctorOver S A).mapHomologicalComplex _).obj I.cocomplex).homology n ≅
      (overCohomologyFunctor S A n).obj ((restrictToOver S A).obj G) :=
  (I.isoRightDerivedObj (sectionsFunctorOver S A) n).symm ≪≫
    (overCohomologyIsoRightDerivedSections S A G n).symm

/-- **The augmentation `G ⟶ I^0`** of an injective resolution. -/
def resolutionAugmentation {G : Sheaf (smallTopology S) AddCommGrpCat.{u + 1}}
    (I : InjectiveResolution G) : G ⟶ I.cocomplex.X 0 :=
  (HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0 G).inv ≫ I.ι.f 0

/-- The augmentation followed by the first differential of the resolution is zero. -/
theorem resolutionAugmentation_comp_d {G : Sheaf (smallTopology S) AddCommGrpCat.{u + 1}}
    (I : InjectiveResolution G) : resolutionAugmentation I ≫ I.cocomplex.d 0 1 = 0 := by
  rw [resolutionAugmentation, Category.assoc, I.ι_f_zero_comp_complex_d, Limits.comp_zero]

/-- `0 → G → I^0 → I^1` is exact: the augmentation is a kernel of the first differential. -/
theorem exact_resolutionAugmentation {G : Sheaf (smallTopology S) AddCommGrpCat.{u + 1}}
    (I : InjectiveResolution G) :
    (ShortComplex.mk _ _ (resolutionAugmentation_comp_d I)).Exact ∧
      Mono (resolutionAugmentation I) := by
  have h := ShortComplex.exact_of_f_is_kernel
    (ShortComplex.mk (I.ι.f 0) _ I.ι_f_zero_comp_complex_d) I.isLimitKernelFork
  refine ⟨?_, by unfold resolutionAugmentation; infer_instance⟩
  refine (ShortComplex.exact_iff_of_iso ?_).1 h
  exact ShortComplex.isoMk (HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0 G)
    (Iso.refl _) (Iso.refl _) (by simp [resolutionAugmentation]; rfl) (by simp)

/-- The sections over an object preserve finite limits. -/
instance (A : CrystallineThickening S) : PreservesFiniteLimits (sectionsFunctorOver S A) :=
  inferInstanceAs (PreservesFiniteLimits (sheafToPresheaf (smallTopology S) AddCommGrpCat.{u + 1} ⋙
    (evaluation (CrystallineThickening S)ᵒᵖ AddCommGrpCat.{u + 1}).obj (op A)))

/-! ### Sections of injectives along monomorphisms -/

/-- **A morphism of `Cris(X/S)` which is a monomorphism on ambient schemes is a monomorphism**,
for instance one whose ambient map is a closed immersion.  The map on thickened schemes is then
determined by the ambient one, the immersion of a divided power thickening being a closed
immersion, hence a monomorphism. -/
theorem mono_of_mono_targetHom {A B : CrystallineThickening S} (f : A ⟶ B)
    [Mono f.hom.targetHom.hom] : Mono f := by
  refine (CrystallineThickening.ι S).mono_of_mono_map ⟨fun {Z} g h he => ?_⟩
  have ht : g.targetHom.hom = h.targetHom.hom :=
    (cancel_mono f.hom.targetHom.hom).1 (congrArg (fun k => k.targetHom.hom) he)
  refine Thickening.Hom.ext ?_ (DividedPowerScheme.Hom.ext ht)
  exact (cancel_mono (A.obj.thickening.immersion)).1 (g.immersion_naturality.symm.trans
    ((congrArg (_ ≫ ·) ht).trans h.immersion_naturality))

/-- **An injective abelian sheaf on `Cris(X/S)` has surjective restriction maps along
monomorphisms**: `H(B) ⟶ H(A)` is onto for `i : A ⟶ B` a monomorphism of the site.  This is
`Stacks.EtaleCohomology.RelativeMayerVietoris.injective_sections_map_surjective`: the free abelian
sheaf functor carries `i` to a monomorphism, against which `H` is injective. -/
theorem surjective_map_of_injective_of_mono (H : Sheaf (smallTopology S) AddCommGrpCat.{u + 1})
    [Injective H] {A B : CrystallineThickening S} (i : A ⟶ B) [Mono i] :
    Function.Surjective (ConcreteCategory.hom (H.obj.map i.op)) :=
  Stacks.EtaleCohomology.RelativeMayerVietoris.injective_sections_map_surjective (smallTopology S)
    H i

/-! ### The cosimplicial sections as a functor -/

/-- **The limit over the levels**, `F ↦ lim_e F(T_e)`, of a tower `T` of objects of
`Cris(X/S)`, as a functor of the abelian presheaf `F`. -/
abbrev levelLimitFunctor (T : ℕ ⥤ CrystallineThickening S) :
    ((CrystallineThickening S)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}) ⥤ AddCommGrpCat.{u + 1} :=
  (Functor.whiskeringLeft _ _ _).obj T.op ⋙ lim

/-- The limit over the levels of the sections of a sheaf preserves finite limits, being a
composite of three functors which do. -/
instance (T : ℕ ⥤ CrystallineThickening S) : PreservesFiniteLimits
    (sheafToPresheaf (smallTopology S) AddCommGrpCat.{u + 1} ⋙ levelLimitFunctor T) := by
  infer_instance

/-- The action of `levelLimitFunctor` on morphisms, read on the limit projections. -/
@[reassoc]
theorem levelLimitFunctor_map_π (T : ℕ ⥤ CrystallineThickening S)
    {F F' : (CrystallineThickening S)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}} (φ : F ⟶ F') (e : ℕᵒᵖ) :
    (levelLimitFunctor T).map φ ≫ limit.π (T.op ⋙ F') e =
      limit.π (T.op ⋙ F) e ≫ φ.app (op (T.obj e.unop)) :=
  limMap_π _ _

/-- The cosimplicial structure maps of `cosimplicialSections` commute with the action of
`levelLimitFunctor` on morphisms. -/
theorem limMap_whiskerRight_levelLimitFunctor_map
    (T : SimplicialObject (ℕ ⥤ CrystallineThickening S))
    {F F' : (CrystallineThickening S)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}} (φ : F ⟶ F')
    {m n : SimplexCategory} (θ : m ⟶ n) :
    limMap (Functor.whiskerRight (NatTrans.op (T.map θ.op)) F) ≫
        (levelLimitFunctor (T.obj (op n))).map φ =
      (levelLimitFunctor (T.obj (op m))).map φ ≫
        limMap (Functor.whiskerRight (NatTrans.op (T.map θ.op)) F') :=
  limit.hom_ext fun e => by simp

/-- **The cosimplicial group `M(•)`, `n ↦ lim_e F(T(n)_e)`, as a functor of the abelian
presheaf `F`**; on objects it is `cosimplicialSections T F`. -/
def cosimplicialSectionsFunctor (T : SimplicialObject (ℕ ⥤ CrystallineThickening S)) :
    ((CrystallineThickening S)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}) ⥤
      CosimplicialObject AddCommGrpCat.{u + 1} where
  obj F := cosimplicialSections T F
  map {_F _F'} φ :=
    { app n := (levelLimitFunctor (T.obj (op n))).map φ
      naturality _m _n θ := limMap_whiskerRight_levelLimitFunctor_map T φ θ }
  map_id F := NatTrans.ext (funext fun n => (levelLimitFunctor (T.obj (op n))).map_id F)
  map_comp φ ψ := NatTrans.ext (funext fun n => (levelLimitFunctor (T.obj (op n))).map_comp φ ψ)

/-- The component in degree `n` of the map induced by `φ : F ⟶ F'` is the map of limits. -/
theorem cosimplicialSectionsFunctor_map_app (T : SimplicialObject (ℕ ⥤ CrystallineThickening S))
    {F F' : (CrystallineThickening S)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}} (φ : F ⟶ F')
    (n : SimplexCategory) :
    ((cosimplicialSectionsFunctor T).map φ).app n = (levelLimitFunctor (T.obj (op n))).map φ :=
  rfl

/-- The limit over the levels is additive. -/
instance (T : ℕ ⥤ CrystallineThickening S) : (levelLimitFunctor T).Additive := by
  infer_instance

/-- The cosimplicial sections functor is additive. -/
instance (T : SimplicialObject (ℕ ⥤ CrystallineThickening S)) :
    (cosimplicialSectionsFunctor T).Additive where
  map_add {_F _F' f g} := NatTrans.ext (funext fun n =>
    (levelLimitFunctor (T.obj (op n))).map_add (f := f) (g := g))

/-- **The complex `M(0) → M(1) → ⋯` as a functor of the abelian presheaf `F`**: the alternating
coface map complex of `cosimplicialSectionsFunctor`.  On objects it is `sectionsComplex T F`. -/
def sectionsComplexFunctor (T : SimplicialObject (ℕ ⥤ CrystallineThickening S)) :
    ((CrystallineThickening S)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}) ⥤
      CochainComplex AddCommGrpCat.{u + 1} ℕ :=
  cosimplicialSectionsFunctor T ⋙ alternatingCofaceMapComplex AddCommGrpCat.{u + 1}

/-- On objects `sectionsComplexFunctor` is `sectionsComplex`. -/
theorem sectionsComplexFunctor_obj (T : SimplicialObject (ℕ ⥤ CrystallineThickening S))
    (F : (CrystallineThickening S)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}) :
    (sectionsComplexFunctor T).obj F = sectionsComplex T F := rfl

/-- The map `sectionsComplex T F ⟶ sectionsComplex T F'` induced by `φ : F ⟶ F'`. -/
abbrev sectionsComplexMap (T : SimplicialObject (ℕ ⥤ CrystallineThickening S))
    {F F' : (CrystallineThickening S)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}} (φ : F ⟶ F') :
    sectionsComplex T F ⟶ sectionsComplex T F' :=
  (sectionsComplexFunctor T).map φ

/-! ### The Čech double complex -/

/-- **The complex of cosimplicial groups of a complex of abelian sheaves**: `K^•` gives
`a ↦ (n ↦ lim_e K^a(T(n)_e))`, the cosimplicial sections applied degreewise. -/
def cechCosimplicialComplex (T : SimplicialObject (ℕ ⥤ CrystallineThickening S)) :
    CochainComplex (Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) ℕ ⥤
      CochainComplex (CosimplicialObject AddCommGrpCat.{u + 1}) ℕ :=
  (sheafToPresheaf (smallTopology S) AddCommGrpCat.{u + 1} ⋙
    cosimplicialSectionsFunctor T).mapHomologicalComplex (ComplexShape.up ℕ)

/-- **The Čech double complex `(n, a) ↦ lim_e K^a(T(n)_e)` of a complex `K^•` of abelian
sheaves**, indexed by `ℤ × ℤ` and extended by zero from `ℕ × ℕ`.  The outer (first) index is the
Čech degree `n`, with the alternating coface differential, and the inner (second) index is the
degree `a` of `K^•`, with the differential of `K^•`; `cechDoubleComplexXXIso` identifies the
terms.  It is defined for any complex `K^•`, not only an injective resolution. -/
def cechDoubleComplex (T : SimplicialObject (ℕ ⥤ CrystallineThickening S)) :
    CochainComplex (Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) ℕ ⥤
      HomologicalComplex₂ AddCommGrpCat.{u + 1} (ComplexShape.up ℤ) (ComplexShape.up ℤ) :=
  cechCosimplicialComplex T ⋙ cosimplicialDoubleComplexFunctor ⋙
    HomologicalComplex₂.flipFunctor _ _ _

/-- The Čech double complex is the flip of `Crystalline.cosimplicialDoubleComplexFunctor` of the
complex of cosimplicial groups. -/
theorem cechDoubleComplex_obj (T : SimplicialObject (ℕ ⥤ CrystallineThickening S))
    (K : CochainComplex (Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) ℕ) :
    (cechDoubleComplex T).obj K =
      (cosimplicialDoubleComplexFunctor.obj ((cechCosimplicialComplex T).obj K)).flip := rfl

/-- The Čech double complex has a total complex, being concentrated in the first quadrant. -/
instance (T : SimplicialObject (ℕ ⥤ CrystallineThickening S))
    (K : CochainComplex (Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) ℕ) :
    ((cechDoubleComplex T).obj K).HasTotal (ComplexShape.up ℤ) :=
  inferInstanceAs
    ((cosimplicialDoubleComplexFunctor.obj ((cechCosimplicialComplex T).obj K)).flip.HasTotal _)

/-- **The term of the Čech double complex in bidegree `(n, a)` is `lim_e K^a(T(n)_e)`**, the
degree-`n` term of `sectionsComplex T (K.X a).obj`. -/
def cechDoubleComplexXXIso (T : SimplicialObject (ℕ ⥤ CrystallineThickening S))
    (K : CochainComplex (Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) ℕ) (n a : ℕ) :
    (((cechDoubleComplex T).obj K).X (n : ℤ)).X (a : ℤ) ≅ (sectionsComplex T (K.X a).obj).X n :=
  (HomologicalComplex.eval _ _ (n : ℤ)).mapIso
      (cosimplicialDoubleComplexColumnIso ((cechCosimplicialComplex T).obj K) a) ≪≫
    HomologicalComplex.extendXIso _ ComplexShape.embeddingUpNat (i := n) (i' := (n : ℤ))
      (ComplexShape.embeddingUpNat_f n)

/-! ### Exactness over an object and along the levels -/

/-- **The sections of an injective resolution over an object `A` are exact in degree `n`** when
`H^n(Cris(X/S)/A, G|_A)` vanishes. -/
theorem exactAt_sections_of_isZero_overCohomology
    {G : Sheaf (smallTopology S) AddCommGrpCat.{u + 1}} (A : CrystallineThickening S)
    (I : InjectiveResolution G) (n : ℕ)
    (h : IsZero ((overCohomologyFunctor S A n).obj ((restrictToOver S A).obj G))) :
    (((sectionsFunctorOver S A).mapHomologicalComplex _).obj I.cocomplex).ExactAt n := by
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  exact h.of_iso (sectionsResolutionHomologyIso A I n)

/-- **Under [Stacks, Tag 07JJ] the sections of an injective resolution over an affine object are
exact in positive degrees**: `H^n(I^•(A)) = H^n(Cris(X/S)/A, G|_A) = 0` for `n > 0`. -/
theorem exactAt_sections_of_vanishing07JJ {G : Sheaf (smallTopology S) AddCommGrpCat.{u + 1}}
    (hG : Vanishing07JJ S G) (A : CrystallineThickening S)
    (hA : IsAffine A.obj.thickening.target.scheme) (I : InjectiveResolution G) (n : ℕ)
    (hn : 0 < n) :
    (((sectionsFunctorOver S A).mapHomologicalComplex _).obj I.cocomplex).ExactAt n :=
  exactAt_sections_of_isZero_overCohomology A I n (hG A hA n hn)

/-- **`0 → G(A) → I^0(A) → I^1(A)` is exact** for every object `A`: the sections over `A` are left
exact. -/
theorem exact_sections_resolutionAugmentation
    {G : Sheaf (smallTopology S) AddCommGrpCat.{u + 1}} (I : InjectiveResolution G)
    (A : CrystallineThickening S) :
    ((ShortComplex.mk _ _ (resolutionAugmentation_comp_d I)).map
      (sectionsFunctorOver S A)).Exact ∧
      Mono ((sectionsFunctorOver S A).map (resolutionAugmentation I)) := by
  obtain ⟨h, hm⟩ := exact_resolutionAugmentation I
  exact ⟨h.map_of_mono_of_preservesKernel _ hm inferInstance, inferInstance⟩

/-- **The hypotheses on the system of thickenings**: every tower map `T(n)_e ⟶ T(n)_{e + 1}` is
a monomorphism of `Cris(X/S)` (see `mono_of_mono_targetHom` for a criterion), and every `T(n)_e`
has affine ambient scheme. -/
structure HasAffineMonoLevels (T : SimplicialObject (ℕ ⥤ CrystallineThickening S)) : Prop where
  /-- The tower maps `T(n)_e ⟶ T(n)_{e + 1}` are monomorphisms. -/
  mono : ∀ n e : ℕ, Mono ((T.obj (op ⦋n⦌)).map (homOfLE (Nat.le_succ e)))
  /-- The objects `T(n)_e` have affine ambient schemes. -/
  isAffine : ∀ n e : ℕ, IsAffine ((T.obj (op ⦋n⦌)).obj e).obj.thickening.target.scheme

/-- **The restriction maps `G(T(n)_{e + 1}) ⟶ G(T(n)_e)` of `G` along the towers of `T` are
surjective**, for every `n` and `e`. -/
def HasSurjectiveLevelTransitions (T : SimplicialObject (ℕ ⥤ CrystallineThickening S))
    (G : Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) : Prop :=
  ∀ n e : ℕ, Function.Surjective (ConcreteCategory.hom
    (G.obj.map ((T.obj (op ⦋n⦌)).map (homOfLE (Nat.le_succ e))).op))

/-- An injective abelian sheaf has surjective restriction maps along the towers of a system whose
tower maps are monomorphisms. -/
theorem hasSurjectiveLevelTransitions_of_injective
    {T : SimplicialObject (ℕ ⥤ CrystallineThickening S)} (hT : HasAffineMonoLevels T)
    (H : Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) [Injective H] :
    HasSurjectiveLevelTransitions T H := fun n e =>
  have := hT.mono n e
  surjective_map_of_injective_of_mono H _

/-- **The higher cohomology of `G` vanishes at the level objects of `T`**:
`H^n(Cris(X/S)/T(b)_e, G|_{T(b)_e}) = 0` for all `b`, `e` and `n > 0`.  This is the only
vanishing the comparison `cechComparison` uses; it follows from the conclusion `Vanishing07JJ`
of [Stacks, Tag 07JJ] when the levels have affine ambient schemes
(`vanishingOnLevels07Q9_of_vanishing07JJ`). -/
def VanishingOnLevels07Q9 (T : SimplicialObject (ℕ ⥤ CrystallineThickening S))
    (G : Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) : Prop :=
  ∀ (b e n : ℕ), 0 < n → IsZero ((overCohomologyFunctor S ((T.obj (op ⦋b⦌)).obj e) n).obj
    ((restrictToOver S ((T.obj (op ⦋b⦌)).obj e)).obj G))

/-- Under the conclusion `Vanishing07JJ` of [Stacks, Tag 07JJ] the higher cohomology of `G`
vanishes at the level objects of a system with affine levels. -/
theorem vanishingOnLevels07Q9_of_vanishing07JJ
    {T : SimplicialObject (ℕ ⥤ CrystallineThickening S)} (hT : HasAffineMonoLevels T)
    {G : Sheaf (smallTopology S) AddCommGrpCat.{u + 1}} (hG : Vanishing07JJ S G) :
    VanishingOnLevels07Q9 T G := fun b e n hn => hG _ (hT.isAffine b e) n hn

section Column

variable {T : SimplicialObject (ℕ ⥤ CrystallineThickening S)}
  {G : Sheaf (smallTopology S) AddCommGrpCat.{u + 1}} (I : InjectiveResolution G)

/-- The tower `e ↦ F(T_e)` of sections of an abelian sheaf `F` along a tower `T`. -/
abbrev levelTower (T : ℕ ⥤ CrystallineThickening S)
    (F : Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) : ℕᵒᵖ ⥤ AddCommGrpCat.{u + 1} :=
  T.op ⋙ F.obj

/-- The map of towers of sections induced by a morphism of abelian sheaves. -/
abbrev levelTowerMap (T : ℕ ⥤ CrystallineThickening S)
    {F F' : Sheaf (smallTopology S) AddCommGrpCat.{u + 1}} (φ : F ⟶ F') :
    levelTower T F ⟶ levelTower T F' :=
  Functor.whiskerLeft T.op φ.hom

/-- Maps of towers of sections induced by morphisms with composite zero compose to zero. -/
theorem levelTowerMap_comp_app (T : ℕ ⥤ CrystallineThickening S)
    {F F' F'' : Sheaf (smallTopology S) AddCommGrpCat.{u + 1}} (φ : F ⟶ F') (ψ : F' ⟶ F'')
    (h : φ ≫ ψ = 0) (i : ℕᵒᵖ) : (levelTowerMap T φ).app i ≫ (levelTowerMap T ψ).app i = 0 := by
  rw [← NatTrans.comp_app, ← Functor.whiskerLeft_comp,
    ← ObjectProperty.FullSubcategory.comp_hom, h]
  rfl

/-- At each level the sequence `I^a(T_e) → I^{a+1}(T_e) → I^{a+2}(T_e)` is exact. -/
theorem isZero_homology_levelTower_succ (hG : VanishingOnLevels07Q9 T G)
    (b a : ℕ) (i : ℕᵒᵖ) :
    IsZero ((invSystemShortComplex (levelTowerMap (T.obj (op ⦋b⦌)) (I.cocomplex.d a (a + 1)))
      (levelTowerMap (T.obj (op ⦋b⦌)) (I.cocomplex.d (a + 1) (a + 2)))
      (levelTowerMap_comp_app _ _ _ (I.cocomplex.d_comp_d _ _ _)) i).homology) := by
  have := exactAt_sections_of_isZero_overCohomology ((T.obj (op ⦋b⦌)).obj i.unop) I (a + 1)
    (hG b i.unop (a + 1) (by omega))
  rw [HomologicalComplex.exactAt_iff_isZero_homology,
    Stacks.TowerAcyclicity.isZero_homology_iff_sc' (i := a) (k := a + 2) _ (by simp) (by simp)]
    at this
  exact this

/-- At each level the sequence `G(T_e) → I^0(T_e) → I^1(T_e)` is exact. -/
theorem isZero_homology_levelTower_zero (b : ℕ) (i : ℕᵒᵖ) :
    IsZero ((invSystemShortComplex (levelTowerMap (T.obj (op ⦋b⦌)) (resolutionAugmentation I))
      (levelTowerMap (T.obj (op ⦋b⦌)) (I.cocomplex.d 0 1))
      (levelTowerMap_comp_app _ _ _ (resolutionAugmentation_comp_d I)) i).homology) := by
  rw [← ShortComplex.exact_iff_isZero_homology]
  exact (exact_sections_resolutionAugmentation I ((T.obj (op ⦋b⦌)).obj i.unop)).1

/-- **The column of the Čech double complex in Čech degree `b` is exact in positive degrees**:
`lim_e I^•(T(b)_e)` is exact at every `a > 0`.  This is [Stacks, Tag 070E] on the four-term
windows of the complex of towers `e ↦ (G(T(b)_e) → I^0(T(b)_e) → I^1(T(b)_e) → ⋯)`, which is
exact at each level and consists of Mittag-Leffler towers. -/
theorem exactAt_cechRow (hT : HasAffineMonoLevels T) (hG : VanishingOnLevels07Q9 T G)
    (hGs : HasSurjectiveLevelTransitions T G) (b a : ℕ) (ha : 0 < a) :
    (cosimplicialRowComplex ((cechCosimplicialComplex T).obj I.cocomplex) b).ExactAt a := by
  obtain ⟨m, rfl⟩ : ∃ m, a = m + 1 := ⟨a - 1, by omega⟩
  rw [HomologicalComplex.exactAt_iff_isZero_homology,
    Stacks.TowerAcyclicity.isZero_homology_iff_sc' (i := m) (k := m + 2) _ (by simp) (by simp)]
  have hML (c : ℕ) :
      (levelTower (T.obj (op ⦋b⦌)) (I.cocomplex.X c) ⋙
        CategoryTheory.forget AddCommGrpCat.{u + 1}).IsMittagLeffler :=
    Stacks.TowerAcyclicity.isMittagLeffler_of_surjective_succ _
      (hasSurjectiveLevelTransitions_of_injective hT (I.cocomplex.X c) b)
  cases m with
  | zero =>
    exact IsZero.of_iso (Stacks.TowerAcyclicity.isZero_homology_window _ _ _ _ _
      (Stacks.TowerAcyclicity.isMittagLeffler_of_surjective_succ _ (hGs b)) (hML 0)
      (isZero_homology_levelTower_zero I b) (isZero_homology_levelTower_succ I hG b 0))
      ((ShortComplex.homologyFunctor _).mapIso (ShortComplex.isoMk (Iso.refl _) (Iso.refl _)
        (Iso.refl _) (by simp only [Iso.refl_hom]; rfl)
        (by simp only [Iso.refl_hom]; rfl)))
  | succ k =>
    exact IsZero.of_iso (Stacks.TowerAcyclicity.isZero_homology_window _ _ _ _ _ (hML k)
      (hML (k + 1)) (isZero_homology_levelTower_succ I hG b k)
      (isZero_homology_levelTower_succ I hG b (k + 1)))
      ((ShortComplex.homologyFunctor _).mapIso (ShortComplex.isoMk (Iso.refl _) (Iso.refl _)
        (Iso.refl _) (by simp only [Iso.refl_hom]; rfl)
        (by simp only [Iso.refl_hom]; rfl)))

/-- The augmentation `M(•) ⟶ lim_e I^0(T(•)_e)` of `ℕ`-indexed complexes induced by `G ⟶ I^0`. -/
def cechAugmentationNat (T : SimplicialObject (ℕ ⥤ CrystallineThickening S)) :
    sectionsComplex T G.obj ⟶ (alternatingCofaceMapComplex AddCommGrpCat.{u + 1}).obj
      (((cechCosimplicialComplex T).obj I.cocomplex).X 0) :=
  (alternatingCofaceMapComplex AddCommGrpCat.{u + 1}).map
    ((cosimplicialSectionsFunctor T).map (resolutionAugmentation I).hom)

/-- The components of `cechAugmentationNat` are the maps of limits induced by `G ⟶ I^0`. -/
theorem cechAugmentationNat_f (T : SimplicialObject (ℕ ⥤ CrystallineThickening S)) (b : ℕ) :
    (cechAugmentationNat I T).f b =
      ((cosimplicialSectionsFunctor T).map (resolutionAugmentation I).hom).app ⦋b⦌ := rfl

/-- **The augmentation of the Čech double complex**: `M(•)`, extended by zero to `ℤ`, maps to the
row `a = 0` of `cechDoubleComplex T I^•` by the map induced by `G ⟶ I^0`. -/
def cechAugmentation (T : SimplicialObject (ℕ ⥤ CrystallineThickening S)) :
    (sectionsComplex T G.obj).extend ComplexShape.embeddingUpNat ⟶
      rowZero ((cechDoubleComplex T).obj I.cocomplex) :=
  HomologicalComplex.extendMap (cechAugmentationNat I T) ComplexShape.embeddingUpNat ≫
    (cosimplicialDoubleComplexColumnIso ((cechCosimplicialComplex T).obj I.cocomplex) 0).inv

/-- The augmentation in Čech degree `b`, read through `cechDoubleComplexXXIso`. -/
theorem cechAugmentation_f_comp (b : ℕ) :
    (cechAugmentation I T).f (b : ℤ) ≫ (cechDoubleComplexXXIso T I.cocomplex b 0).hom =
      ((sectionsComplex T G.obj).extendXIso ComplexShape.embeddingUpNat (i := b) (i' := (b : ℤ))
          (ComplexShape.embeddingUpNat_f b)).hom ≫
        (cechAugmentationNat I T).f b := by
  let K' := (cechCosimplicialComplex T).obj I.cocomplex
  have k1 : (cosimplicialDoubleComplexColumnIso K' 0).inv.f (b : ℤ) ≫
      (cosimplicialDoubleComplexColumnIso K' 0).hom.f (b : ℤ) = 𝟙 _ := by
    rw [← HomologicalComplex.comp_f, Iso.inv_hom_id, HomologicalComplex.id_f]
  have k2 := HomologicalComplex.extendMap_f (cechAugmentationNat I T) ComplexShape.embeddingUpNat
    (i := b) (i' := (b : ℤ)) (ComplexShape.embeddingUpNat_f b)
  change (HomologicalComplex.extendMap (cechAugmentationNat I T) ComplexShape.embeddingUpNat).f
      (b : ℤ) ≫ ((cosimplicialDoubleComplexColumnIso K' 0).inv.f (b : ℤ) ≫
        (cosimplicialDoubleComplexColumnIso K' 0).hom.f (b : ℤ) ≫
        (((alternatingCofaceMapComplex AddCommGrpCat.{u + 1}).obj (K'.X 0)).extendXIso
          ComplexShape.embeddingUpNat (i := b) (i' := (b : ℤ))
          (ComplexShape.embeddingUpNat_f b)).hom) = _
  rw [reassoc_of% k1, k2, Category.assoc, Category.assoc, Iso.inv_hom_id,
    Category.comp_id]

/-- **The differential in the resolution direction**: under `cechDoubleComplexXXIso` the
differential `(n, a) → (n, a')` is the map of limits induced by `K^a ⟶ K^{a'}`. -/
theorem cechDoubleComplex_X_d_comp
    (K : CochainComplex (Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) ℕ) (n a a' : ℕ) :
    (((cechDoubleComplex T).obj K).X (n : ℤ)).d a a' ≫ (cechDoubleComplexXXIso T K n a').hom =
      (cechDoubleComplexXXIso T K n a).hom ≫
        ((cosimplicialSectionsFunctor T).map (K.d a a').hom).app ⦋n⦌ := by
  let K' := (cechCosimplicialComplex T).obj K
  let D := cosimplicialDoubleComplexFunctor.obj K'
  let c := (alternatingCofaceMapComplex AddCommGrpCat.{u + 1}).map (K'.d a a')
  have hd : D.d a a' = (cosimplicialDoubleComplexColumnIso K' a).hom ≫
      HomologicalComplex.extendMap c ComplexShape.embeddingUpNat ≫
        (cosimplicialDoubleComplexColumnIso K' a').inv :=
    HomologicalComplex.extend_d_eq _ _ (ComplexShape.embeddingUpNat_f a)
      (ComplexShape.embeddingUpNat_f a')
  have hd' : D.d a a' ≫ (cosimplicialDoubleComplexColumnIso K' a').hom =
      (cosimplicialDoubleComplexColumnIso K' a).hom ≫
        HomologicalComplex.extendMap c ComplexShape.embeddingUpNat := by
    rw [hd]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have h1 := congrArg (fun φ => HomologicalComplex.Hom.f φ (n : ℤ)) hd'
  simp only [HomologicalComplex.comp_f] at h1
  rw [HomologicalComplex.extendMap_f c ComplexShape.embeddingUpNat (i := n) (i' := (n : ℤ))
    (ComplexShape.embeddingUpNat_f n)] at h1
  change (D.d a a').f (n : ℤ) ≫ ((cosimplicialDoubleComplexColumnIso K' a').hom.f (n : ℤ) ≫
      (((alternatingCofaceMapComplex AddCommGrpCat.{u + 1}).obj (K'.X a')).extendXIso
        ComplexShape.embeddingUpNat (i := n) (i' := (n : ℤ))
        (ComplexShape.embeddingUpNat_f n)).hom) =
    ((cosimplicialDoubleComplexColumnIso K' a).hom.f (n : ℤ) ≫
      (((alternatingCofaceMapComplex AddCommGrpCat.{u + 1}).obj (K'.X a)).extendXIso
        ComplexShape.embeddingUpNat (i := n) (i' := (n : ℤ))
        (ComplexShape.embeddingUpNat_f n)).hom) ≫ c.f n
  rw [← Category.assoc, h1]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- **The differential in the Čech direction**: under `cechDoubleComplexXXIso` the differential
`(n, a) → (n', a)` is the differential of `sectionsComplex T (K.X a).obj`. -/
theorem cechDoubleComplex_d_f_comp
    (K : CochainComplex (Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) ℕ) (n n' a : ℕ) :
    (((cechDoubleComplex T).obj K).d (n : ℤ) (n' : ℤ)).f (a : ℤ) ≫
        (cechDoubleComplexXXIso T K n' a).hom =
      (cechDoubleComplexXXIso T K n a).hom ≫ (sectionsComplex T (K.X a).obj).d n n' := by
  let K' := (cechCosimplicialComplex T).obj K
  let L := (alternatingCofaceMapComplex AddCommGrpCat.{u + 1}).obj (K'.X a)
  have h1 := (cosimplicialDoubleComplexColumnIso K' a).hom.comm (n : ℤ) (n' : ℤ)
  rw [L.extend_d_eq ComplexShape.embeddingUpNat (ComplexShape.embeddingUpNat_f n)
    (ComplexShape.embeddingUpNat_f n')] at h1
  change ((cosimplicialDoubleComplexFunctor.obj K').X (a : ℤ)).d (n : ℤ) (n' : ℤ) ≫
      ((cosimplicialDoubleComplexColumnIso K' a).hom.f (n' : ℤ) ≫
        (L.extendXIso ComplexShape.embeddingUpNat (i := n') (i' := (n' : ℤ))
        (ComplexShape.embeddingUpNat_f n')).hom) =
    ((cosimplicialDoubleComplexColumnIso K' a).hom.f (n : ℤ) ≫
      (L.extendXIso ComplexShape.embeddingUpNat (i := n) (i' := (n : ℤ))
        (ComplexShape.embeddingUpNat_f n)).hom) ≫ L.d n n'
  rw [← Category.assoc, ← h1]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- **The action of the Čech double complex on a morphism `χ : K₁ ⟶ K₂`**: under
`cechDoubleComplexXXIso` it is, in bidegree `(n, a)`, the map of limits induced by `χ^a`. -/
theorem cechDoubleComplex_map_f_f_comp
    {K₁ K₂ : CochainComplex (Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) ℕ} (χ : K₁ ⟶ K₂)
    (n a : ℕ) :
    (((cechDoubleComplex T).map χ).f (n : ℤ)).f (a : ℤ) ≫ (cechDoubleComplexXXIso T K₂ n a).hom =
      (cechDoubleComplexXXIso T K₁ n a).hom ≫
        ((cosimplicialSectionsFunctor T).map (χ.f a).hom).app ⦋n⦌ := by
  let K₁' := (cechCosimplicialComplex T).obj K₁
  let K₂' := (cechCosimplicialComplex T).obj K₂
  let c : (alternatingCofaceMapComplex AddCommGrpCat.{u + 1}).obj (K₁'.X a) ⟶
      (alternatingCofaceMapComplex AddCommGrpCat.{u + 1}).obj (K₂'.X a) :=
    (alternatingCofaceMapComplex AddCommGrpCat.{u + 1}).map
      (((cechCosimplicialComplex T).map χ).f a)
  have hd : (cosimplicialDoubleComplexFunctor.map ((cechCosimplicialComplex T).map χ)).f
      (a : ℤ) = (cosimplicialDoubleComplexColumnIso K₁' a).hom ≫
        HomologicalComplex.extendMap c ComplexShape.embeddingUpNat ≫
        (cosimplicialDoubleComplexColumnIso K₂' a).inv :=
    HomologicalComplex.extendMap_f _ ComplexShape.embeddingUpNat (ComplexShape.embeddingUpNat_f a)
  have hd' : (cosimplicialDoubleComplexFunctor.map ((cechCosimplicialComplex T).map χ)).f
      (a : ℤ) ≫ (cosimplicialDoubleComplexColumnIso K₂' a).hom =
      (cosimplicialDoubleComplexColumnIso K₁' a).hom ≫
        HomologicalComplex.extendMap c ComplexShape.embeddingUpNat := by
    rw [hd]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have h1 := congrArg (fun φ => HomologicalComplex.Hom.f φ (n : ℤ)) hd'
  simp only [HomologicalComplex.comp_f] at h1
  rw [HomologicalComplex.extendMap_f c ComplexShape.embeddingUpNat (i := n) (i' := (n : ℤ))
    (ComplexShape.embeddingUpNat_f n)] at h1
  change ((cosimplicialDoubleComplexFunctor.map ((cechCosimplicialComplex T).map χ)).f
      (a : ℤ)).f (n : ℤ) ≫ ((cosimplicialDoubleComplexColumnIso K₂' a).hom.f (n : ℤ) ≫
      (((alternatingCofaceMapComplex AddCommGrpCat.{u + 1}).obj (K₂'.X a)).extendXIso
        ComplexShape.embeddingUpNat (i := n) (i' := (n : ℤ))
        (ComplexShape.embeddingUpNat_f n)).hom) =
    ((cosimplicialDoubleComplexColumnIso K₁' a).hom.f (n : ℤ) ≫
      (((alternatingCofaceMapComplex AddCommGrpCat.{u + 1}).obj (K₁'.X a)).extendXIso
        ComplexShape.embeddingUpNat (i := n) (i' := (n : ℤ))
        (ComplexShape.embeddingUpNat_f n)).hom) ≫ c.f n
  rw [← Category.assoc, h1]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- In an abelian category, if `f` is a monomorphism and `X ⟶ Y ⟶ Z` is exact, then the
comparison of `X` with the kernel of `g` is an isomorphism. -/
theorem isIso_kernelLift_of_exact {C : Type*} [Category C] [Abelian C] {X Y Z : C}
    (f : X ⟶ Y) (g : Y ⟶ Z) (w : f ≫ g = 0) (hS : (ShortComplex.mk f g w).Exact) [Mono f] :
    IsIso (kernel.lift g f w) := by
  have : Epi (kernel.lift g f w) := hS.epi_kernelLift
  have : Mono (kernel.lift g f w) := mono_of_mono_fac (kernel.lift_ι g f w)
  exact isIso_of_mono_of_epi _

/-- **`0 → lim_e G(T(b)_e) → lim_e I^0(T(b)_e) → lim_e I^1(T(b)_e)` is exact**: the limit over
the levels of the sections is left exact. -/
theorem exact_levelLimit_resolutionAugmentation (b : ℕ) :
    ((ShortComplex.mk _ _ (resolutionAugmentation_comp_d I)).map
      (sheafToPresheaf (smallTopology S) AddCommGrpCat.{u + 1} ⋙
        levelLimitFunctor (T.obj (op ⦋b⦌)))).Exact ∧
      Mono ((sheafToPresheaf (smallTopology S) AddCommGrpCat.{u + 1} ⋙
        levelLimitFunctor (T.obj (op ⦋b⦌))).map (resolutionAugmentation I)) := by
  obtain ⟨h, hm⟩ := exact_resolutionAugmentation I
  exact ⟨h.map_of_mono_of_preservesKernel _ hm inferInstance, inferInstance⟩

/-- In Čech degree `b` the augmentation identifies `M(b)` with the kernel of the first differential
of the column. -/
theorem cechAugmentation_inducesIsoKernel_nat (b : ℕ) :
    ∃ hα : (cechAugmentation I T).f (b : ℤ) ≫
        (((cechDoubleComplex T).obj I.cocomplex).X (b : ℤ)).d 0 1 = 0,
      IsIso (kernel.lift _ _ hα) := by
  obtain ⟨hex, hm⟩ := exact_levelLimit_resolutionAugmentation I (T := T) b
  have sq1 := cechAugmentation_f_comp I (T := T) b
  have sq2 := cechDoubleComplex_X_d_comp (T := T) I.cocomplex b 0 1
  have hz : (cechAugmentationNat I T).f b ≫
      ((cosimplicialSectionsFunctor T).map (I.cocomplex.d 0 1).hom).app ⦋b⦌ = 0 :=
    ((ShortComplex.mk _ _ (resolutionAugmentation_comp_d I)).map
      (sheafToPresheaf (smallTopology S) AddCommGrpCat.{u + 1} ⋙
        levelLimitFunctor (T.obj (op ⦋b⦌)))).zero
  have hα : (cechAugmentation I T).f (b : ℤ) ≫
      (((cechDoubleComplex T).obj I.cocomplex).X (b : ℤ)).d 0 1 = 0 := by
    have h2 : (cechAugmentation I T).f (b : ℤ) ≫
        (((cechDoubleComplex T).obj I.cocomplex).X (b : ℤ)).d 0 1 ≫
          (cechDoubleComplexXXIso T I.cocomplex b 1).hom = 0 :=
      (congrArg (_ ≫ ·) sq2).trans <| (Category.assoc _ _ _).symm.trans <|
        (congrArg (· ≫ _) sq1).trans <| (Category.assoc _ _ _).trans <|
          (congrArg (_ ≫ ·) hz).trans Limits.comp_zero
    rw [← cancel_mono (cechDoubleComplexXXIso T I.cocomplex b 1).hom, Category.assoc, h2,
      Limits.zero_comp]
  refine ⟨hα, ?_⟩
  let e : ShortComplex.mk _ _ hα ≅ (ShortComplex.mk _ _ (resolutionAugmentation_comp_d I)).map
      (sheafToPresheaf (smallTopology S) AddCommGrpCat.{u + 1} ⋙
        levelLimitFunctor (T.obj (op ⦋b⦌))) :=
    ShortComplex.isoMk ((sectionsComplex T G.obj).extendXIso ComplexShape.embeddingUpNat
      (i := b) (i' := (b : ℤ)) (ComplexShape.embeddingUpNat_f b))
      (cechDoubleComplexXXIso T I.cocomplex b 0) (cechDoubleComplexXXIso T I.cocomplex b 1)
      sq1.symm sq2.symm
  have : Mono ((cechAugmentation I T).f (b : ℤ)) := by
    have : Mono ((cechAugmentation I T).f (b : ℤ) ≫
        (cechDoubleComplexXXIso T I.cocomplex b 0).hom) := by
      rw [sq1]
      exact @mono_comp _ _ _ _ _ _ _ _ hm
    exact mono_of_mono _ (cechDoubleComplexXXIso T I.cocomplex b 0).hom
  exact isIso_kernelLift_of_exact _ _ hα ((ShortComplex.exact_iff_of_iso e).2 hex)

/-- **The Čech double complex of an injective resolution resolves `M(•)`**: the augmentation
satisfies the hypotheses of [Stacks, Tag 0133] (`Hypotheses`). -/
theorem cechAugmentation_hypotheses (hT : HasAffineMonoLevels T) (hG : VanishingOnLevels07Q9 T G)
    (hGs : HasSurjectiveLevelTransitions T G) :
    Hypotheses ((sectionsComplex T G.obj).extend ComplexShape.embeddingUpNat)
      ((cechDoubleComplex T).obj I.cocomplex) (cechAugmentation I T) := by
  let K' := (cechCosimplicialComplex T).obj I.cocomplex
  have hz : ∀ p q : ℤ, (p < 0 ∨ q < 0) →
      IsZero ((((cechDoubleComplex T).obj I.cocomplex).X p).X q) := by
    rintro p q (hp | hq)
    · exact isZero_cosimplicialDoubleComplex_X_X_of_neg K' q hp
    · exact (HomologicalComplex.eval _ _ p).map_isZero
        (isZero_cosimplicialDoubleComplex_X_of_neg K' hq)
  refine ⟨fun n => ?_, fun p q hq => hz p q (Or.inr hq), fun p q hq => ?_, fun p => ?_⟩
  · refine (Set.finite_Icc 0 n).subset fun p hp => ?_
    by_contra h
    exact hp (hz p (n - p) (by simp only [Set.mem_Icc, not_and_or, not_le] at h; omega))
  · by_cases hp : p < 0
    · exact ShortComplex.exact_of_isZero_X₂ _ (hz p q (Or.inl hp))
    · obtain ⟨b, rfl⟩ : ∃ b : ℕ, p = b := ⟨p.toNat, by omega⟩
      refine HomologicalComplex.ExactAt.of_iso ?_ (cosimplicialDoubleComplexRowIso K' b).symm
      by_cases hq' : q < 0
      · exact HomologicalComplex.extend_exactAt _ _ _
          (fun i hi => by simp only [ComplexShape.embeddingUpNat_f] at hi; omega)
      · obtain ⟨m, rfl⟩ : ∃ m : ℕ, q = m := ⟨q.toNat, by omega⟩
        exact (HomologicalComplex.extend_exactAt_iff _ _ (ComplexShape.embeddingUpNat_f m)).2
          (exactAt_cechRow I hT hG hGs b m (by omega))
  · by_cases hp : p < 0
    · have h0 : IsZero (((sectionsComplex T G.obj).extend ComplexShape.embeddingUpNat).X p) :=
        HomologicalComplex.isZero_extend_X _ _ _
          (fun i hi => by simp only [ComplexShape.embeddingUpNat_f] at hi; omega)
      refine ⟨h0.eq_of_src _ _, StacksDraft.TotalComplexQuasiIso.isIso_of_isZero _ h0 ?_⟩
      exact IsZero.of_mono (kernel.ι _) (hz p 0 (Or.inl hp))
    · obtain ⟨b, rfl⟩ : ∃ b : ℕ, p = b := ⟨p.toNat, by omega⟩
      exact cechAugmentation_inducesIsoKernel_nat I b

end Column

/-! ### The comparison map -/

section Comparison

variable {T : SimplicialObject (ℕ ⥤ CrystallineThickening S)}

/-- **The comparison `β : M(•) ⟶ Tot(lim_e I^•(T(•)_e))`** of [Stacks, Tag 0133] for the Čech
double complex of an injective resolution of `G`: in degree `n` it is the augmentation followed
by the inclusion of the summand in bidegree `(n, 0)`, `cechComparison_f`. -/
def cechComparison (hT : HasAffineMonoLevels T)
    {G : Sheaf (smallTopology S) AddCommGrpCat.{u + 1}}
    (hG : VanishingOnLevels07Q9 T G) (hGs : HasSurjectiveLevelTransitions T G)
    (I : InjectiveResolution G) :
    (sectionsComplex T G.obj).extend ComplexShape.embeddingUpNat ⟶
      ((cechDoubleComplex T).obj I.cocomplex).total (ComplexShape.up ℤ) :=
  comparisonMapP _ _ (cechAugmentation I T) (cechAugmentation_hypotheses I hT hG hGs)

/-- **The comparison `β` is a quasi-isomorphism**, by [Stacks, Tag 0133]. -/
instance quasiIso_cechComparison (hT : HasAffineMonoLevels T)
    {G : Sheaf (smallTopology S) AddCommGrpCat.{u + 1}}
    (hG : VanishingOnLevels07Q9 T G) (hGs : HasSurjectiveLevelTransitions T G)
    (I : InjectiveResolution G) : QuasiIso (cechComparison hT hG hGs I) :=
  quasiIso_comparisonMapP _ _ _ _

/-- The components of `cechComparison`. -/
theorem cechComparison_f (hT : HasAffineMonoLevels T)
    {G : Sheaf (smallTopology S) AddCommGrpCat.{u + 1}}
    (hG : VanishingOnLevels07Q9 T G) (hGs : HasSurjectiveLevelTransitions T G)
    (I : InjectiveResolution G) (n : ℤ) :
    (cechComparison hT hG hGs I).f n = (cechAugmentation I T).f n ≫
      ((cechDoubleComplex T).obj I.cocomplex).ιTotal (ComplexShape.up ℤ) n 0 n (by simp) :=
  rfl

/-- The action of the Čech double complex on a morphism, read on the row `a = 0`. -/
theorem rowZeroMap_cechDoubleComplex_map
    {K₁ K₂ : CochainComplex (Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) ℕ} (χ : K₁ ⟶ K₂) :
    rowZeroMap ((cechDoubleComplex T).map χ) =
      (cosimplicialDoubleComplexColumnIso ((cechCosimplicialComplex T).obj K₁) 0).hom ≫
        HomologicalComplex.extendMap ((alternatingCofaceMapComplex AddCommGrpCat.{u + 1}).map
          (((cechCosimplicialComplex T).map χ).f 0)) ComplexShape.embeddingUpNat ≫
        (cosimplicialDoubleComplexColumnIso ((cechCosimplicialComplex T).obj K₂) 0).inv := by
  change (cosimplicialDoubleComplexFunctor.map ((cechCosimplicialComplex T).map χ)).f
    ((0 : ℕ) : ℤ) = _
  exact HomologicalComplex.extendMap_f _ ComplexShape.embeddingUpNat (i := 0)
    (i' := ((0 : ℕ) : ℤ)) (ComplexShape.embeddingUpNat_f 0)

/-- A morphism of injective resolutions over `g` commutes with the augmentations. -/
theorem resolutionAugmentation_naturality
    {G G' : Sheaf (smallTopology S) AddCommGrpCat.{u + 1}}
    {g : G ⟶ G'} {I : InjectiveResolution G} {I' : InjectiveResolution G'}
    (φ : InjectiveResolution.Hom I I' g) :
    resolutionAugmentation I ≫ φ.hom.f 0 = g ≫ resolutionAugmentation I' := by
  rw [resolutionAugmentation, resolutionAugmentation, Category.assoc,
    φ.ι_f_zero_comp_hom_f_zero, HomologicalComplex.single_map_f_self, Category.assoc,
    Category.assoc, Iso.inv_hom_id_assoc]

/-- **The comparison `β` is natural in the pair `(G, I^•)`**: for a morphism `φ` of injective
resolutions over `g : G ⟶ G'` the square formed by `β`, `Tot` of the Čech double complex of `φ`,
and the map `M(•) ⟶ M'(•)` induced by `g` commutes. -/
theorem cechComparison_naturality (hT : HasAffineMonoLevels T)
    {G G' : Sheaf (smallTopology S) AddCommGrpCat.{u + 1}}
    (hG : VanishingOnLevels07Q9 T G) (hGs : HasSurjectiveLevelTransitions T G)
    (hG' : VanishingOnLevels07Q9 T G') (hGs' : HasSurjectiveLevelTransitions T G')
    {g : G ⟶ G'} {I : InjectiveResolution G} {I' : InjectiveResolution G'}
    (φ : InjectiveResolution.Hom I I' g) :
    cechComparison hT hG hGs I ≫
        HomologicalComplex₂.total.map ((cechDoubleComplex T).map φ.hom) (ComplexShape.up ℤ) =
      HomologicalComplex.extendMap (sectionsComplexMap T g.hom)
          ComplexShape.embeddingUpNat ≫ cechComparison hT hG' hGs' I' := by
  refine comparisonMapP_naturality _ _ _ _ _ _ _ ?_
  have hN : cechAugmentationNat I T ≫ (alternatingCofaceMapComplex AddCommGrpCat.{u + 1}).map
      (((cechCosimplicialComplex T).map φ.hom).f 0) =
        sectionsComplexMap T g.hom ≫ cechAugmentationNat I' T := by
    change (alternatingCofaceMapComplex AddCommGrpCat.{u + 1}).map
        ((cosimplicialSectionsFunctor T).map (resolutionAugmentation I).hom) ≫
      (alternatingCofaceMapComplex AddCommGrpCat.{u + 1}).map
        ((cosimplicialSectionsFunctor T).map (φ.hom.f 0).hom) =
      (alternatingCofaceMapComplex AddCommGrpCat.{u + 1}).map
        ((cosimplicialSectionsFunctor T).map g.hom) ≫
      (alternatingCofaceMapComplex AddCommGrpCat.{u + 1}).map
        ((cosimplicialSectionsFunctor T).map (resolutionAugmentation I').hom)
    rw [← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp,
      ← ObjectProperty.FullSubcategory.comp_hom, ← ObjectProperty.FullSubcategory.comp_hom,
      resolutionAugmentation_naturality]
  rw [rowZeroMap_cechDoubleComplex_map]
  let K₁ := (cechCosimplicialComplex T).obj I.cocomplex
  let K₂ := (cechCosimplicialComplex T).obj I'.cocomplex
  change (HomologicalComplex.extendMap (cechAugmentationNat I T) ComplexShape.embeddingUpNat ≫
      (cosimplicialDoubleComplexColumnIso K₁ 0).inv) ≫
      ((cosimplicialDoubleComplexColumnIso K₁ 0).hom ≫
        HomologicalComplex.extendMap ((alternatingCofaceMapComplex AddCommGrpCat.{u + 1}).map
          (((cechCosimplicialComplex T).map φ.hom).f 0)) ComplexShape.embeddingUpNat ≫
        (cosimplicialDoubleComplexColumnIso K₂ 0).inv) =
    HomologicalComplex.extendMap (sectionsComplexMap T g.hom)
        ComplexShape.embeddingUpNat ≫
      (HomologicalComplex.extendMap (cechAugmentationNat I' T) ComplexShape.embeddingUpNat ≫
        (cosimplicialDoubleComplexColumnIso K₂ 0).inv)
  rw [Category.assoc, Iso.inv_hom_id_assoc, ← HomologicalComplex.extendMap_comp_assoc,
    ← HomologicalComplex.extendMap_comp_assoc, hN]

end Comparison

end Crystalline.GlobalCrystallineSituation.SmallSite
