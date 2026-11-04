module

public import StacksFrontier.AlgebraicGeometry.Spaces.ProperGlobalSections.FormalFunctionsFibres
public import StacksFrontier.AlgebraicGeometry.Spaces.GlobalSectionsRingHomSiteSections
public import StacksFrontier.AlgebraicGeometry.Spaces.GlobalFunctionsSmall
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartBasicOpenLocalization
public import StacksFrontier.AlgebraicGeometry.Artin.ContractionVersalityOpen
public import StacksFrontier.AlgebraicGeometry.Artin.ContractionLimitSpaceOpenIso
public import StacksFrontier.AlgebraicGeometry.Spaces.AlternatingCech.DiagonalComplement
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.SpecialCoverings
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversallyClosedAffineBase

/-!
# Kernel and cokernel of the functions of a modification

Let `V` be an affine locally Noetherian object of the site, `A = Γ(V, 𝒪_V)`, `I ⊆ A` an ideal
with zero locus `Z ⊆ |V|`, and `f : X ⟶ V` a proper morphism of algebraic spaces which is an
isomorphism over `V ∖ Z`. In the "algebra, more rings" paragraph of the proof of Stacks 0GI5
(for `X = V'_μ` the descended witness over a stage) the kernel and the cokernel of the pullback
of functions `A ⟶ C = Γ(X, 𝒪_X)` are annihilated by a power of `I`: for `g ∈ I` the morphism `f`
has a section over the basic open `D(g) ⊆ V ∖ Z`, so the kernel and the cokernel die after
inverting `g`, and Algebra, Lemma 00L6 applies (`C` is a finite `A`-module by Stacks 08AS,
`AlgebraicGeometry.Space.moduleFinite_globalFunctionsOver_of_isProper`).

The localization of the cokernel at `g` is computed on an affine étale atlas of `X`: a global
function of `X` vanishing on the section over `D(g)` vanishes on the basic open of the pullback
of `g` in the atlas, hence is killed there by a power of `g`, and a global function is determined
by its values on a surjective atlas.

## Main results

* `AlgebraicGeometry.Artin.StageRings.evalAt`: the value of a global function along a morphism
  from an object of the site, with `evalAt_pullbackRingHom`, `evalAt_comp` and `evalAt_chart`.
* `AlgebraicGeometry.Artin.StageRings.exists_pow_mul_eq_zero_of_pullbackRingHom_eq_zero` and
  `AlgebraicGeometry.Artin.StageRings.exists_pullbackRingHom_eq_pow_mul`: the kernel and the
  cokernel are killed by powers of each element of `I`.
* `AlgebraicGeometry.Artin.StageRings.exists_pow_smul_ker_coker`: they are killed by a power of
  `I`.

## References

* [Stacks Project, Tag 0GI5](https://stacks.math.columbia.edu/tag/0GI5)
* [Stacks Project, Tag 00L6](https://stacks.math.columbia.edu/tag/00L6)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Artin.StageRings

open Space Stacks.Cohomology.SiteModules

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The value of a global function of `X` along a morphism `h : T ⟶ X` from an object of the
site: the pullback along `h`, read on `T` itself. -/
noncomputable def evalAt {T : BigFppfOver B S hS} {X : AlgebraicSpaces B S hS}
    (h : schemeSpace T ⟶ X) :
    ↥(Stacks.Cohomology.SiteModules.GlobalSectionRing
      (Stacks.SheafOfModules.Tensor.ringSheaf (Space.smallEtaleRingedSite B S hS X.1 X.2).O)) →+*
      Γ((BigFppfOver.toScheme B S hS).obj T, ⊤) :=
  (globalFunctionsChartRestriction B S hS (schemeSpace T) (idEtaleChart B S hS T)).comp
    (globalSectionsRingHomSite B S hS h)

/-- Along `h : T ⟶ X` over `ρ : T ⟶ V`, the pullback of a function `a` on `V` has the value
`ρ^♯ a`. -/
theorem evalAt_pullbackRingHom {T V : BigFppfOver B S hS} {X : AlgebraicSpaces B S hS}
    (h : schemeSpace T ⟶ X) (f : X ⟶ schemeSpace V) (ρ : T ⟶ V)
    (hρ : h ≫ f = schemeSpaceMap ρ) (a : Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)) :
    evalAt h (pullbackRingHom B V f a) = ((BigFppfOver.toScheme B S hS).map ρ).appTop a := by
  have h1 := congrArg (fun φ => φ a) (globalSectionsRingHomSite_comp_pullbackRingHom V h f)
  simp only [RingHom.comp_apply] at h1
  show (globalSectionsRingHomSite B S hS h (pullbackRingHom B V f a)).1
    (op (idEtaleChart B S hS T)) = _
  rw [h1, hρ]
  show (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map
    (yoneda.preimage (𝟙 _ ≫ yoneda.map ρ))).op).hom a = _
  rw [Category.id_comp, Functor.preimage_map]
  rfl


/-- `evalAt` is functorial: precomposing with `τ : T' ⟶ T` restricts the value along `τ`. -/
theorem evalAt_comp {T T' : BigFppfOver B S hS} {X : AlgebraicSpaces B S hS} (τ : T' ⟶ T)
    (h : schemeSpace T ⟶ X) (e : ↥(Stacks.Cohomology.SiteModules.GlobalSectionRing
      (Stacks.SheafOfModules.Tensor.ringSheaf (Space.smallEtaleRingedSite B S hS X.1 X.2).O))) :
    evalAt (schemeSpaceMap τ ≫ h) e =
      ((BigFppfOver.toScheme B S hS).map τ).appTop (evalAt h e) := by
  let d : ChartDiagram B S hS (schemeSpace T').1 (schemeSpace T).1 (schemeSpaceMap τ).hom :=
    ⟨idEtaleChart B S hS T', idEtaleChart B S hS T, τ, by
      show 𝟙 _ ≫ yoneda.map τ = yoneda.map τ ≫ 𝟙 _
      rw [Category.id_comp, Category.comp_id]⟩
  have h1 : globalSectionsRingHomSite B S hS (schemeSpaceMap τ ≫ h) e =
      globalSectionsRingHomSite B S hS (schemeSpaceMap τ)
        (globalSectionsRingHomSite B S hS h e) := by
    rw [globalSectionsRingHomSite_comp]
    rfl
  exact (congrArg (fun x => globalSectionEval _ (op d.U) x) h1).trans
    (globalSectionsRingHomSite_val_chartDiagram B S hS (schemeSpaceMap τ) _ d)

/-- Along an étale chart, `evalAt` is the value of the global function on that chart. -/
theorem evalAt_chart {X : AlgebraicSpaces B S hS} (U : Space.SmallEtale B S hS X.1)
    (e : ↥(Stacks.Cohomology.SiteModules.GlobalSectionRing
      (Stacks.SheafOfModules.Tensor.ringSheaf (Space.smallEtaleRingedSite B S hS X.1 X.2).O))) :
    evalAt (X := X) (ObjectProperty.homMk U.1.hom : schemeSpace U.1.left ⟶ X) e =
      globalSectionEval _ (op U) e := by
  let d : ChartDiagram B S hS (schemeSpace U.1.left).1 X.1
      (ObjectProperty.homMk U.1.hom : schemeSpace U.1.left ⟶ X).hom :=
    ⟨idEtaleChart B S hS U.1.left, U, 𝟙 _, by
      show 𝟙 _ ≫ U.1.hom = yoneda.map (𝟙 _) ≫ U.1.hom
      rw [Category.id_comp, CategoryTheory.Functor.map_id, Category.id_comp]⟩
  refine (globalSectionsRingHomSite_val_chartDiagram B S hS _ e d).trans ?_
  show (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map (𝟙 U.1.left)).op).hom (e.1 (op U)) =
    e.1 (op U)
  rw [CategoryTheory.Functor.map_id, op_id, CategoryTheory.Functor.map_id]
  rfl

/-- A global function vanishing along `σ` vanishes along every morphism factoring through `σ`. -/
theorem evalAt_eq_zero_of_eq_comp {T T' : BigFppfOver B S hS} {X : AlgebraicSpaces B S hS}
    {h : schemeSpace T' ⟶ X} {σ : schemeSpace T ⟶ X} {τ : T' ⟶ T} (hh : h = schemeSpaceMap τ ≫ σ)
    {e : ↥(Stacks.Cohomology.SiteModules.GlobalSectionRing
      (Stacks.SheafOfModules.Tensor.ringSheaf (Space.smallEtaleRingedSite B S hS X.1 X.2).O))}
    (he : evalAt σ e = 0) : evalAt h e = 0 := by
  subst hh
  rw [evalAt_comp, he, map_zero]

/-- The inclusion of an open subscheme lands in the open. -/
theorem ι_mem (Y : Scheme.{u}) (O : Y.Opens) (z : O.toScheme) : O.ι z ∈ O := by
  show O.ι z ∈ (O : Set Y)
  rw [← Scheme.Opens.range_ι O]
  exact ⟨z, rfl⟩

/-- A point of an open lies in the image of its inclusion. -/
theorem mem_range_ι_of_mem (Y : Scheme.{u}) (O : Y.Opens) (x : Y) (hx : x ∈ O) :
    x ∈ Set.range O.ι := by
  rwa [Scheme.Opens.range_ι]

/-! ### Localization on an affine scheme -/

/-- On an affine scheme, a function vanishing on `D(r)` is killed by a power of `r`. -/
theorem exists_pow_mul_eq_zero_of_appTop_ι_eq_zero (Y : Scheme.{u}) [IsAffine Y] (r : Γ(Y, ⊤))
    (a : Γ(Y, ⊤)) (h : (Y.basicOpen r).ι.appTop a = 0) : ∃ n : ℕ, r ^ n * a = 0 := by
  obtain ⟨⟨_, n, rfl⟩, hn⟩ :=
    (IsLocalization.map_eq_zero_iff (Submonoid.powers r) Γ(Y.basicOpen r, ⊤) a).1 h
  exact ⟨n, hn⟩

/-- On an affine scheme, every function on `D(r)` is a restriction divided by a power of `r`. -/
theorem exists_mul_eq_appTop_ι (Y : Scheme.{u}) [IsAffine Y] (r : Γ(Y, ⊤))
    (y : Γ(Y.basicOpen r, ⊤)) :
    ∃ (n : ℕ) (a : Γ(Y, ⊤)), y * (Y.basicOpen r).ι.appTop (r ^ n) = (Y.basicOpen r).ι.appTop a := by
  obtain ⟨⟨a, ⟨_, n, rfl⟩⟩, h⟩ := IsLocalization.surj (Submonoid.powers r) y
  exact ⟨n, a, h⟩

/-- `exists_pow_mul_eq_zero_of_appTop_ι_eq_zero` for `D(r)` read as an object of the site. -/
theorem exists_pow_mul_eq_zero_of_appTop_openSubHom_eq_zero (V : BigFppfOver B S hS)
    [IsAffine ((BigFppfOver.toScheme B S hS).obj V)]
    (r a : Γ((BigFppfOver.toScheme B S hS).obj V, ⊤))
    (h : ((BigFppfOver.toScheme B S hS).map
      (openSubHom V (((BigFppfOver.toScheme B S hS).obj V).basicOpen r))).appTop a = 0) :
    ∃ n : ℕ, r ^ n * a = 0 := by
  rw [toScheme_map_openSubHom] at h
  exact exists_pow_mul_eq_zero_of_appTop_ι_eq_zero _ r a h

/-- `exists_mul_eq_appTop_ι` for `D(r)` read as an object of the site. -/
theorem exists_mul_eq_appTop_openSubHom (V : BigFppfOver B S hS)
    [IsAffine ((BigFppfOver.toScheme B S hS).obj V)] (r : Γ((BigFppfOver.toScheme B S hS).obj V, ⊤))
    (y : Γ((BigFppfOver.toScheme B S hS).obj
      (openSub V (((BigFppfOver.toScheme B S hS).obj V).basicOpen r)), ⊤)) :
    ∃ (n : ℕ) (a : Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)),
      y * ((BigFppfOver.toScheme B S hS).map
        (openSubHom V (((BigFppfOver.toScheme B S hS).obj V).basicOpen r))).appTop (r ^ n) =
      ((BigFppfOver.toScheme B S hS).map
        (openSubHom V (((BigFppfOver.toScheme B S hS).obj V).basicOpen r))).appTop a := by
  obtain ⟨n, a, h⟩ := exists_mul_eq_appTop_ι _ r y
  exact ⟨n, a, by rwa [toScheme_map_openSubHom]⟩

/-- **A power of an ideal kills a finite module on whose elements every element of the ideal
acts nilpotently** (the module-theoretic content of Stacks 00L6). -/
theorem exists_pow_le_annihilator {A M : Type*} [CommRing A] [IsNoetherianRing A]
    [AddCommGroup M] [Module A M] [Module.Finite A M] (I : Ideal A)
    (h : ∀ g ∈ I, ∀ m : M, ∃ n : ℕ, g ^ n • m = 0) :
    ∃ N : ℕ, I ^ N ≤ Module.annihilator A M := by
  refine Ideal.exists_pow_le_of_le_radical_of_fg_radical (fun g hg => ?_)
    (IsNoetherian.noetherian _)
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := A) (M := M)
  choose n hn using h g hg
  refine ⟨s.sup n, Module.mem_annihilator.2 fun m => ?_⟩
  have hm : m ∈ Submodule.span A (s : Set M) := hs ▸ Submodule.mem_top
  induction hm using Submodule.span_induction with
  | mem x hx =>
    rw [← Nat.sub_add_cancel (Finset.le_sup (f := n) (Finset.mem_coe.1 hx)), pow_add, mul_smul,
      hn, smul_zero]
  | zero => exact smul_zero _
  | add x y _ _ hx hy => rw [smul_add, hx, hy, add_zero]
  | smul a x _ hx => rw [smul_comm, hx, smul_zero]

/-- The kernel of a ring map out of a Noetherian ring on which every element of `I` acts
nilpotently is killed by a power of `I`. -/
theorem exists_pow_mul_eq_zero_of_ideal {A : Type*} [CommRing A] [IsNoetherianRing A]
    (I J : Ideal A) (h : ∀ g ∈ I, ∀ a ∈ J, ∃ n : ℕ, g ^ n * a = 0) :
    ∃ N : ℕ, ∀ x ∈ I ^ N, ∀ a ∈ J, x * a = 0 := by
  obtain ⟨N, hN⟩ := exists_pow_le_annihilator (M := J) I (fun g hg m => by
    obtain ⟨n, hn⟩ := h g hg m m.2
    exact ⟨n, Subtype.ext hn⟩)
  exact ⟨N, fun x hx a ha => congrArg Subtype.val (Module.mem_annihilator.1 (hN hx) ⟨a, ha⟩)⟩

/-- For a finite ring map `φ : A ⟶ C` out of a Noetherian ring such that every element of `I`
multiplies each element of `C`, after a power, into the image of `φ`, a power of `I` multiplies
all of `C` into the image of `φ`. -/
theorem exists_pow_mul_mem_range_of_finite {A C : Type*} [CommRing A] [IsNoetherianRing A]
    [CommRing C] (φ : A →+* C) (hfin : letI := Module.compHom C φ; Module.Finite A C)
    (I : Ideal A) (h : ∀ g ∈ I, ∀ c : C, ∃ (n : ℕ) (a : A), φ a = φ g ^ n * c) :
    ∃ N : ℕ, ∀ x ∈ I ^ N, ∀ c : C, φ x * c ∈ φ.range := by
  let := Module.compHom C φ
  have := hfin
  let P : Submodule A C := Submodule.span A {1}
  have hP : ∀ c : C, c ∈ P ↔ c ∈ φ.range := by
    intro c
    rw [Submodule.mem_span_singleton, RingHom.mem_range]
    exact ⟨fun ⟨a, ha⟩ => ⟨a, (mul_one (φ a)).symm.trans ha⟩,
      fun ⟨a, ha⟩ => ⟨a, (mul_one (φ a)).trans ha⟩⟩
  obtain ⟨N, hN⟩ := exists_pow_le_annihilator (M := C ⧸ P) I (fun g hg m => by
    obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective P m
    obtain ⟨n, a, ha⟩ := h g hg c
    refine ⟨n, ?_⟩
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, hP, RingHom.mem_range]
    exact ⟨a, ha.trans (by rw [← map_pow]; rfl)⟩)
  refine ⟨N, fun x hx c => ?_⟩
  have := Module.mem_annihilator.1 (hN hx) (Submodule.Quotient.mk (p := P) c)
  rwa [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, hP] at this

/-! ### An affine atlas -/

/-- A quasi-compact algebraic space has a surjective étale atlas by an affine object, with its
kernel pair. -/
theorem exists_atlasKernelPairData_isAffine {X : AlgebraicSpaces B S hS}
    (hX : IsQuasiCompactSpace B S hS X.1) :
    ∃ D : AtlasKernelPairData B S hS X, IsAffine ((BigFppfOver.toScheme B S hS).obj D.U) := by
  obtain ⟨U, p, hU, hsurj, het⟩ :=
    (isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover B S hS X.1 X.2).1 hX
  have hetale := presheaf_etale_of_isEtale (B := B) (S := S) (hS := hS) het
  let hrep : yoneda.relativelyRepresentable p := hetale.1
  have hpb := hrep.isPullback' p
  exact ⟨⟨U, hrep.pullback p, p, hrep.fst' p, hrep.snd p, hsurj, hetale, hpb,
    hetale.2 p (yoneda.map (hrep.snd p)) (hrep.fst' p) hpb.flip,
    hetale.2 p (hrep.fst p) (hrep.snd p) (hrep.isPullback p)⟩, hU⟩

/-! ### A morphism which is an isomorphism over the complement of `V(I)` -/

/-- A morphism `w` from a representable presheaf into `V` missing `Z` lifts uniquely through a
morphism `f` which is an isomorphism over `V ∖ Z`. -/
private theorem existsUnique_lift_of_mem_compl {V T : BigFppfOver B S hS}
    {X : AlgebraicSpaces B S hS} {f : X.1 ⟶ yoneda.obj V}
    {Z : Set (Space.points B S hS (yoneda.obj V))}
    (hiso : IsIso (pullback.snd f (openSubspaceOfPoints B S hS (yoneda.obj V) Zᶜ).ι))
    {w : yoneda.obj T ⟶ yoneda.obj V} (hZ : ∀ p, pointsMap B S hS _ w p ∈ Zᶜ) :
    ∃! y : yoneda.obj T ⟶ X.1, y ≫ f = w :=
  (isIso_pullback_snd_ι_iff_existsUnique f _).1 hiso T
    (Subfunctor.lift w (range_le_openSubspaceOfPoints B S hS _ Zᶜ hZ))

section Torsion

variable (V : BigFppfOver B S hS) [IsAffine ((BigFppfOver.toScheme B S hS).obj V)]
  {X : AlgebraicSpaces B S hS} {f : X ⟶ schemeSpace V}
  {Z : Set (Space.points B S hS (yoneda.obj V))}
  {I : Ideal Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)}
  (hZI : ∀ x, x ∈ Z ↔ Space.pointsToScheme B S hS V x ∈
    ((BigFppfOver.toScheme B S hS).obj V).zeroLocus
      (I : Set Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)))
  (hiso : IsIso (pullback.snd f.hom (openSubspaceOfPoints B S hS (yoneda.obj V) Zᶜ).ι))

include hZI in
omit [IsAffine ((BigFppfOver.toScheme B S hS).obj V)] in
/-- A morphism into the basic open `D(g) ⊆ V` of an element `g ∈ I` misses `Z = V(I)`. -/
theorem pointsMap_comp_openSubHom_mem_compl {g : Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)}
    (hg : g ∈ I) {T : BigFppfOver B S hS}
    (τ : T ⟶ openSub V (((BigFppfOver.toScheme B S hS).obj V).basicOpen g))
    (y : points B S hS (yoneda.obj T)) :
    pointsMap B S hS _ (yoneda.map (τ ≫ openSubHom V
      (((BigFppfOver.toScheme B S hS).obj V).basicOpen g))) y ∈ Zᶜ := by
  intro hy
  rw [Functor.map_comp, pointsMap_comp_apply, hZI, pointsToScheme_pointsMap_yoneda,
    toScheme_map_openSubHom, Scheme.mem_zeroLocus_iff] at hy
  exact hy g hg (ι_mem _ _ _)

include hiso in
omit [IsAffine ((BigFppfOver.toScheme B S hS).obj V)] in
/-- Two morphisms into `X` over a morphism into `V ∖ Z` agree. -/
theorem eq_of_comp_eq {T : BigFppfOver B S hS} {y₁ y₂ : yoneda.obj T ⟶ X.1}
    (h : y₁ ≫ f.hom = y₂ ≫ f.hom) (hZ : ∀ p, pointsMap B S hS _ (y₁ ≫ f.hom) p ∈ Zᶜ) :
    y₁ = y₂ := by
  obtain ⟨y, -, hu⟩ := existsUnique_lift_of_mem_compl hiso hZ
  exact (hu y₁ rfl).trans (hu y₂ h.symm).symm

include hZI hiso in
omit [IsAffine ((BigFppfOver.toScheme B S hS).obj V)] in
/-- Over the basic open `D(g)` of an element `g ∈ I`, the morphism `f` has a section. -/
theorem exists_section_basicOpen {g : Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)} (hg : g ∈ I) :
    ∃ σ : schemeSpace (openSub V (((BigFppfOver.toScheme B S hS).obj V).basicOpen g)) ⟶ X,
      σ ≫ f =
        schemeSpaceMap (openSubHom V (((BigFppfOver.toScheme B S hS).obj V).basicOpen g)) := by
  have hZ := pointsMap_comp_openSubHom_mem_compl V hZI hg (𝟙 _)
  rw [Category.id_comp] at hZ
  obtain ⟨y, hy, -⟩ := existsUnique_lift_of_mem_compl hiso hZ
  exact ⟨ObjectProperty.homMk y, ObjectProperty.hom_ext _ hy⟩

include hZI hiso in
omit [IsAffine ((BigFppfOver.toScheme B S hS).obj V)] in
/-- A global function of `X` vanishing on the section over `D(g)`, `g ∈ I`, is killed by a power
of `g`. -/
theorem exists_pow_mul_eq_zero_of_evalAt_eq_zero (hX : IsQuasiCompactSpace B S hS X.1)
    {g : Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)} (hg : g ∈ I)
    (σ : schemeSpace (openSub V (((BigFppfOver.toScheme B S hS).obj V).basicOpen g)) ⟶ X)
    (hσ : σ ≫ f = schemeSpaceMap (openSubHom V (((BigFppfOver.toScheme B S hS).obj V).basicOpen g)))
    (e : ↥(Stacks.Cohomology.SiteModules.GlobalSectionRing
      (Stacks.SheafOfModules.Tensor.ringSheaf (Space.smallEtaleRingedSite B S hS X.1 X.2).O)))
    (he : evalAt σ e = 0) :
    ∃ n : ℕ, pullbackRingHom B V f g ^ n * e = 0 := by
  obtain ⟨D, hDa⟩ := exists_atlasKernelPairData_isAffine hX
  let Uc := atlasChart B S hS X D
  let ρ : D.U ⟶ V := yoneda.preimage (D.f ≫ f.hom)
  have hρ : D.f ≫ f.hom = yoneda.map ρ := (Functor.map_preimage yoneda _).symm
  let r : Γ((BigFppfOver.toScheme B S hS).obj D.U, ⊤) :=
    ((BigFppfOver.toScheme B S hS).map ρ).appTop g
  let O := ((BigFppfOver.toScheme B S hS).obj D.U).basicOpen r
  let ιg := openSubHom V (((BigFppfOver.toScheme B S hS).obj V).basicOpen g)
  have hιg : IsOpenImmersion ((BigFppfOver.toScheme B S hS).map ιg) := by
    rw [toScheme_map_openSubHom]
    exact inferInstanceAs (IsOpenImmersion (((BigFppfOver.toScheme B S hS).obj V).basicOpen g).ι)
  obtain ⟨τ, hτ⟩ := BigFppfOver.exists_comp_eq_of_isOpenImmersion ιg hιg
    (openSubHom D.U O ≫ ρ) (by
      rintro _ ⟨z, rfl⟩
      have hz : (BigFppfOver.toScheme B S hS).map (openSubHom D.U O) z ∈
          (BigFppfOver.toScheme B S hS).map ρ ⁻¹ᵁ
            ((BigFppfOver.toScheme B S hS).obj V).basicOpen g := by
        rw [Scheme.preimage_basicOpen_top, toScheme_map_openSubHom]
        exact ι_mem _ _ _
      rw [Functor.map_comp, Scheme.Hom.comp_apply, toScheme_map_openSubHom]
      exact mem_range_ι_of_mem _ _ _ hz)
  let Ug := openChart B S hS X.1 Uc O
  have hcomp : Ug.1.hom ≫ f.hom = yoneda.map (τ ≫ ιg) := by
    show (yoneda.map (openSubHom D.U O) ≫ D.f) ≫ f.hom = _
    rw [hτ, Functor.map_comp, Category.assoc, hρ]
    rfl
  have hUg : (ObjectProperty.homMk Ug.1.hom : schemeSpace Ug.1.left ⟶ X) =
      schemeSpaceMap τ ≫ σ := by
    apply ObjectProperty.hom_ext
    refine eq_of_comp_eq V hiso ?_ ?_
    · show Ug.1.hom ≫ f.hom = yoneda.map τ ≫ σ.hom ≫ f.hom
      rw [hcomp, Functor.map_comp]
      exact congrArg (yoneda.map τ ≫ ·) (congrArg (fun m => m.hom) hσ).symm
    · show ∀ p, pointsMap B S hS _ (Ug.1.hom ≫ f.hom) p ∈ Zᶜ
      rw [hcomp]
      exact pointsMap_comp_openSubHom_mem_compl V hZI hg τ
  have h2 : chartRestrict (hF := X.2) (openChartInclusion B S hS X.1 Uc O)
      (globalSectionEval _ (op Uc) e) = 0 :=
    (e.2 (openChartInclusion B S hS X.1 Uc O).op).trans
      ((evalAt_chart Ug e).symm.trans (evalAt_eq_zero_of_eq_comp hUg he))
  rw [chartRestrict_openChartInclusion B S hS X.2 Uc O] at h2
  obtain ⟨n, hn⟩ := exists_pow_mul_eq_zero_of_appTop_ι_eq_zero _ r _ h2
  refine ⟨n, globalFunctionsChartRestriction_injective B S hS X D ?_⟩
  show globalSectionEval _ (op Uc) (pullbackRingHom B V f g ^ n * e) =
    globalSectionEval _ (op Uc) 0
  exact ((globalSectionEval _ (op Uc)).map_mul _ _).trans
    ((congrArg (· * globalSectionEval _ (op Uc) e)
      ((globalSectionEval _ (op Uc)).map_pow _ _)).trans (hn.trans (map_zero _).symm))

include hZI hiso in
/-- **The kernel of `Γ(V) ⟶ Γ(X)` is killed by powers of the elements of `I`.** -/
theorem exists_pow_mul_eq_zero_of_pullbackRingHom_eq_zero
    {g : Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)} (hg : g ∈ I)
    {a : Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)} (ha : pullbackRingHom B V f a = 0) :
    ∃ n : ℕ, g ^ n * a = 0 := by
  obtain ⟨σ, hσ⟩ := exists_section_basicOpen V hZI hiso hg
  have h0 : ((BigFppfOver.toScheme B S hS).map
      (openSubHom V (((BigFppfOver.toScheme B S hS).obj V).basicOpen g))).appTop a = 0 :=
    (evalAt_pullbackRingHom σ f _ hσ a).symm.trans ((congrArg (evalAt σ) ha).trans (map_zero _))
  exact exists_pow_mul_eq_zero_of_appTop_openSubHom_eq_zero V g a h0

include hZI hiso in
/-- **The cokernel of `Γ(V) ⟶ Γ(X)` is killed by powers of the elements of `I`.** -/
theorem exists_pullbackRingHom_eq_pow_mul (hX : IsQuasiCompactSpace B S hS X.1)
    {g : Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)} (hg : g ∈ I)
    (c : ↥(Stacks.Cohomology.SiteModules.GlobalSectionRing
      (Stacks.SheafOfModules.Tensor.ringSheaf (Space.smallEtaleRingedSite B S hS X.1 X.2).O))) :
    ∃ (n : ℕ) (a : Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)),
      pullbackRingHom B V f a = pullbackRingHom B V f g ^ n * c := by
  obtain ⟨σ, hσ⟩ := exists_section_basicOpen V hZI hiso hg
  have hev := evalAt_pullbackRingHom σ f _ hσ
  obtain ⟨m, a, hma⟩ := exists_mul_eq_appTop_openSubHom V g (evalAt σ c)
  obtain ⟨n, hn⟩ := exists_pow_mul_eq_zero_of_evalAt_eq_zero V hZI hiso hX hg σ hσ
    (pullbackRingHom B V f g ^ m * c - pullbackRingHom B V f a) (by
      rw [map_sub, map_mul, map_pow, hev, hev, ← map_pow, mul_comm, hma, sub_self])
  refine ⟨n + m, g ^ n * a, ?_⟩
  rw [mul_sub, sub_eq_zero] at hn
  rw [map_mul, map_pow, ← hn, pow_add, mul_assoc]

include hZI hiso in
/-- **The kernel and the cokernel of `Γ(V) ⟶ Γ(X)` are killed by a power of `I`** (the
"algebra, more rings" paragraph of the proof of Stacks 0GI5): for `f : X ⟶ V` proper over an
affine Noetherian `V` and an isomorphism over `V ∖ V(I)`, some `I^N` annihilates the kernel of the
pullback of functions and multiplies every global function of `X` into its image. -/
theorem exists_pow_smul_ker_coker
    [_root_.AlgebraicGeometry.IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj V)]
    (hf : Space.IsProper B S hS f.hom) :
    ∃ N : ℕ, (∀ a, pullbackRingHom B V f a = 0 → ∀ x ∈ I ^ N, x * a = 0) ∧
      ∀ (c : ↥(Stacks.Cohomology.SiteModules.GlobalSectionRing
      (Stacks.SheafOfModules.Tensor.ringSheaf (Space.smallEtaleRingedSite B S hS X.1 X.2).O))),
      ∀ x ∈ I ^ N,
        pullbackRingHom B V f x * c ∈ (pullbackRingHom B V f).range := by
  have : IsNoetherianRing Γ((BigFppfOver.toScheme B S hS).obj V, ⊤) :=
    _root_.AlgebraicGeometry.IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top _⟩
  have hX : IsQuasiCompactSpace B S hS X.1 :=
    isQuasiCompactSpace_of_universallyClosed_of_isAffine B S hS V inferInstance X.2
      (isAlgebraicSpace_yoneda B S hS V) f.hom hf.2.2
  obtain ⟨N₁, hN₁⟩ := exists_pow_mul_eq_zero_of_ideal I (RingHom.ker (pullbackRingHom B V f))
    (fun g hg a ha => exists_pow_mul_eq_zero_of_pullbackRingHom_eq_zero V hZI hiso hg
      (RingHom.mem_ker.1 ha))
  obtain ⟨N₂, hN₂⟩ := exists_pow_mul_mem_range_of_finite (pullbackRingHom B V f)
    (moduleFinite_globalFunctionsOver_of_isProper V f hf) I
    (fun g hg c => exists_pullbackRingHom_eq_pow_mul V hZI hiso hX hg c)
  exact ⟨max N₁ N₂, fun a ha x hx =>
    hN₁ x (Ideal.pow_le_pow_right (le_max_left _ _) hx) a (RingHom.mem_ker.2 ha),
    fun c x hx => hN₂ x (Ideal.pow_le_pow_right (le_max_right _ _) hx) c⟩

end Torsion

end AlgebraicGeometry.Artin.StageRings

end
