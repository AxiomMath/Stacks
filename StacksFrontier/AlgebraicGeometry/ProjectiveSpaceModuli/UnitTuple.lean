module

public import StacksFrontier.AlgebraicGeometry.ProjectiveSpaceModuli.Basic
public import StacksFrontier.AlgebraicGeometry.Divisors.InvertibleSheafPullback
public import StacksFrontier.AlgebraicGeometry.Chow.ZeroSchemePullback.Factorization
public import StacksFrontier.AlgebraicGeometry.AmpleWire.UnitStalk
public import StacksFrontier.AlgebraicGeometry.AmplePowers.QuasiAffine
public import StacksFrontier.AlgebraicGeometry.Divisors.ZeroSchemeRegular
public import StacksFrontier.AlgebraicGeometry.AmpleImmersionReduction.Generation
public import StacksFrontier.AlgebraicGeometry.Perfect.SupportClosedSubset.FractionClassMap
public import StacksFrontier.Topology.OpensMapFinal
public import StacksFrontier.AlgebraicGeometry.TwistPullbackRatio.Comparison
public import StacksFrontier.AlgebraicGeometry.QcohRestrictEquiv.IsoLocality
public import StacksFrontier.AlgebraicGeometry.NonvanishingSpelling.Trivialize

/-!
# Points of projective space given by functions spanning the unit ideal

Tag 01NE identifies morphisms `T ⟶ ℙⁿ_ℤ` with invertible `𝒪_T`-modules carrying `n + 1`
generating global sections, up to isomorphism (`Stacks.ProjectiveSpaceModuli.pointsEquiv`). This
file records the pairs whose module is `𝒪_T` itself: functions `b₀, …, bₙ` spanning the unit ideal
of `Γ(T, 𝒪)` give the pair `(𝒪_T, b)` and hence a morphism
`Stacks.ProjectiveSpaceModuli.homOfCoords b : T ⟶ ℙⁿ_ℤ`. Every morphism to `ℙⁿ_ℤ` is locally of
this form, two such morphisms agree exactly when the functions differ by a unit, and the
construction commutes with pullback.

## Main definitions

* `Stacks.ProjectiveSpaceModuli.unitTuple`: the pair `(𝒪_T, b)`.
* `Stacks.ProjectiveSpaceModuli.homOfCoords`: the morphism `T ⟶ ℙⁿ_ℤ` it classifies.

## Main results

* `Stacks.ProjectiveSpaceModuli.homOfCoords_eq_iff`: `homOfCoords b = homOfCoords b'` exactly when
  `b' = c • b` for a unit `c` of `Γ(T, 𝒪)`.
* `Stacks.ProjectiveSpaceModuli.comp_homOfCoords`: naturality in `T`.
* `Stacks.ProjectiveSpaceModuli.exists_isAffineOpen_comp_eq_homOfCoords`: every morphism to `ℙⁿ_ℤ`
  is `homOfCoords` on an affine neighbourhood of every point.

## References

* [Stacks Project, Tag 01NE](https://stacks.math.columbia.edu/tag/01NE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

namespace Stacks.ProjectiveSpaceModuli

variable {T : Scheme.{u}} {n : ℕ}

/-- The nonvanishing locus of a function, read as a section of `𝒪_T`, is its basic open. -/
theorem nonvanishingLocus_unitModule (b : Γ(T, ⊤)) :
    Stacks.Ample.nonvanishingLocus (Stacks.Ample.unitModule T)
      (show Γ(Stacks.Ample.unitModule T, ⊤) from b) = (T.basicOpen b : Set T) := by
  have h := (Stacks.Ample.unitBasis T).nonvanishingLocus_smul_gen b
  rwa [show (b • (Stacks.Ample.unitBasis T).gen : Γ(Stacks.Ample.unitModule T, ⊤)) =
    show Γ(Stacks.Ample.unitModule T, ⊤) from b from Stacks.Ample.smul_unitModule_one T b] at h

/-- Functions spanning the unit ideal generate the structure sheaf at every stalk. -/
theorem generatesStalks_of_span_eq_top (b : Fin (n + 1) → Γ(T, ⊤))
    (hb : Ideal.span (Set.range b) = ⊤) :
    Stacks.ProjectiveFromSections.GeneratesStalks
      (L := Stacks.Ample.unitModule T) b := by
  refine Stacks.AmpleImmersionReduction.generatesStalks_of_forall_exists_mem _ fun x => ?_
  by_contra hx
  push Not at hx
  have hmem : ∀ i, T.presheaf.germ ⊤ x trivial (b i) ∈
      IsLocalRing.maximalIdeal (T.presheaf.stalk x) := by
    intro i
    by_contra hi
    refine hx i ?_
    show x ∈ Stacks.Ample.nonvanishingLocus (Stacks.Ample.unitModule T) (b i)
    rw [nonvanishingLocus_unitModule]
    exact (T.mem_basicOpen_top (b i) x).2 ((IsLocalRing.mem_maximalIdeal _).not.1 hi |> not_not.1)
  have h1 : (1 : Γ(T, ⊤)) ∈ Ideal.span (Set.range b) := hb ▸ Submodule.mem_top
  have h2 := Ideal.mem_map_of_mem (T.presheaf.germ ⊤ x trivial).hom h1
  rw [Ideal.map_span, map_one] at h2
  refine (IsLocalRing.maximalIdeal.isMaximal (T.presheaf.stalk x)).ne_top
    ((Ideal.eq_top_iff_one _).2 ?_)
  refine Ideal.span_le.2 ?_ h2
  rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
  exact hmem i

/-- **The pair `(𝒪_T, (b₀, …, bₙ))`** attached to functions spanning the unit ideal. -/
noncomputable def unitTuple (b : Fin (n + 1) → Γ(T, ⊤)) (hb : Ideal.span (Set.range b) = ⊤) :
    GeneratingTuple T n where
  bundle := Stacks.Ample.unitModule T
  isInvertible := Stacks.Ample.isInvertibleModule_unit T
  coord := b
  generates := generatesStalks_of_span_eq_top b hb

/-- The morphism to `ℙⁿ_ℤ` attached to functions spanning the unit ideal, through Tag 01NE. -/
noncomputable def homOfCoords (b : Fin (n + 1) → Γ(T, ⊤)) (hb : Ideal.span (Set.range b) = ⊤) :
    T ⟶ projectiveSpaceAtUniverse.{u} n :=
  (pointsEquiv T n).symm ⟦unitTuple b hb⟧

/-- An endomorphism of `𝒪_T` acts on global sections by multiplication by its value at `1`. -/
theorem app_top_unitModule_eq (φ : Stacks.Ample.unitModule T ⟶ Stacks.Ample.unitModule T)
    (x : Γ(T, ⊤)) :
    (show Γ(T, ⊤) from φ.app ⊤ (show Γ(Stacks.Ample.unitModule T, ⊤) from x)) =
      x * (show Γ(T, ⊤) from
        φ.app ⊤ (show Γ(Stacks.Ample.unitModule T, ⊤) from (1 : Γ(T, ⊤)))) := by
  have h := Scheme.Modules.Hom.app_smul φ x
    (show Γ(Stacks.Ample.unitModule T, ⊤) from (1 : Γ(T, ⊤)))
  rwa [Stacks.Ample.smul_unitModule_one] at h

/-- **Two unit pairs are identified exactly when their functions differ by a unit.** -/
theorem isomorphic_unitTuple_iff (b b' : Fin (n + 1) → Γ(T, ⊤))
    (hb : Ideal.span (Set.range b) = ⊤) (hb' : Ideal.span (Set.range b') = ⊤) :
    Isomorphic (unitTuple b hb) (unitTuple b' hb') ↔ ∃ c : Γ(T, ⊤)ˣ, ∀ i, b' i = c * b i := by
  constructor
  · rintro ⟨β, hβ⟩
    let w : Γ(T, ⊤) :=
      β.hom.app ⊤ (show Γ(Stacks.Ample.unitModule T, ⊤) from (1 : Γ(T, ⊤)))
    let w' : Γ(T, ⊤) :=
      β.inv.app ⊤ (show Γ(Stacks.Ample.unitModule T, ⊤) from (1 : Γ(T, ⊤)))
    have h2 : (show Γ(T, ⊤) from
        β.inv.app ⊤ (show Γ(Stacks.Ample.unitModule T, ⊤) from w)) = 1 := by
      show ((β.hom ≫ β.inv).app ⊤) _ = _
      rw [β.hom_inv_id]
      rfl
    have h1 : w * w' = 1 := (app_top_unitModule_eq β.inv w).symm.trans h2
    exact ⟨⟨w, w', h1, (mul_comm w' w).trans h1⟩, fun i =>
      (hβ i).symm.trans ((app_top_unitModule_eq β.hom (b i)).trans (mul_comm _ _))⟩
  · rintro ⟨c, hc⟩
    have hiso := Stacks.Perfect.FractionClass.isIso_smulHom c.isUnit (Stacks.Ample.unitModule T)
    refine ⟨@asIso _ _ _ _ (Stacks.Perfect.FractionClass.smulHom (c : Γ(T, ⊤))
      (Stacks.Ample.unitModule T)) hiso, fun i => ?_⟩
    refine (Stacks.Perfect.FractionClass.smulHom_app_apply _ _ _ _).trans ?_
    have hid : T.presheaf.map (homOfLE (le_top : (⊤ : T.Opens) ≤ ⊤)).op = 𝟙 _ := by
      rw [show (homOfLE (le_top : (⊤ : T.Opens) ≤ ⊤)).op = 𝟙 (op ⊤) from rfl, T.presheaf.map_id]
    rw [hid]
    exact (hc i).symm

/-- **Two unit pairs give the same morphism exactly when their functions differ by a unit.** -/
theorem homOfCoords_eq_iff (b b' : Fin (n + 1) → Γ(T, ⊤))
    (hb : Ideal.span (Set.range b) = ⊤) (hb' : Ideal.span (Set.range b') = ⊤) :
    homOfCoords b hb = homOfCoords b' hb' ↔ ∃ c : Γ(T, ⊤)ˣ, ∀ i, b' i = c * b i := by
  rw [homOfCoords, homOfCoords, (pointsEquiv T n).symm.injective.eq_iff, Quotient.eq]
  exact isomorphic_unitTuple_iff b b' hb hb'

section Pullback

variable {T' : Scheme.{u}} (c : T' ⟶ T)

/-- The bijection `pointsEquiv` turns precomposition into pullback of points. -/
private theorem pointsEquiv_comp (g : T ⟶ projectiveSpaceAtUniverse.{u} n) :
    pointsEquiv T' n (c ≫ g) = pullbackPoints c (pointsEquiv T n g) :=
  pointsOfHom_comp c g

/-- If global sections `b i` of `T` generate the unit ideal, then so do their pullbacks
`c.appTop (b i)` along a morphism `c : T' ⟶ T`. -/
theorem span_range_appTop_comp (b : Fin (n + 1) → Γ(T, ⊤)) (hb : Ideal.span (Set.range b) = ⊤) :
    Ideal.span (Set.range fun i => c.appTop (b i)) = ⊤ := by
  have h := congrArg (Ideal.map c.appTop.hom) hb
  rwa [Ideal.map_span, Ideal.map_top, ← Set.range_comp] at h

/-- **Pulling back a unit pair gives the unit pair of the pulled-back functions.** -/
theorem isomorphic_pullbackTuple_unitTuple (b : Fin (n + 1) → Γ(T, ⊤))
    (hb : Ideal.span (Set.range b) = ⊤) :
    Isomorphic (pullbackTuple c (unitTuple b hb))
      (unitTuple (fun i => c.appTop (b i)) (span_range_appTop_comp c b hb)) := by
  have : (SheafOfModules.pushforward c.toRingCatSheafHom).IsRightAdjoint :=
    inferInstanceAs (Scheme.Modules.pushforward c).IsRightAdjoint
  have : (TopologicalSpace.Opens.map c.base).Final := Stacks.Topology.final_opensMap _
  exact ⟨@asIso _ _ _ _ (SheafOfModules.pullbackObjUnitToUnit c.toRingCatSheafHom)
      (SheafOfModules.instIsIsoPullbackObjUnitToUnitOfFinal c.toRingCatSheafHom),
    fun i => Stacks.Divisors.pullbackGlobalSections_unit_appTop c (b i)⟩

/-- **Naturality of `homOfCoords` in the test scheme.** -/
theorem comp_homOfCoords (b : Fin (n + 1) → Γ(T, ⊤)) (hb : Ideal.span (Set.range b) = ⊤) :
    c ≫ homOfCoords b hb =
      homOfCoords (fun i => c.appTop (b i)) (span_range_appTop_comp c b hb) := by
  refine (pointsEquiv T' n).injective ?_
  rw [pointsEquiv_comp, homOfCoords, homOfCoords, Equiv.apply_symm_apply,
    Equiv.apply_symm_apply, pullbackPoints_mk]
  exact Quotient.sound (isomorphic_pullbackTuple_unitTuple c b hb)

end Pullback

/-- **Multiplication by a nowhere vanishing global section of an invertible module is an
isomorphism** `𝒪 ⟶ M`. -/
theorem isIso_unitHomEquiv_symm_sectionsOfTop {X : Scheme.{u}} (M : X.Modules)
    [Stacks.Ample.IsInvertibleModule X M] (s : Γ(M, ⊤))
    (hs : ∀ y : X, y ∈ Stacks.NonvanishingOpen.nonvanishingOpen X M s) :
    IsIso (M.unitHomEquiv.symm (Stacks.Divisors.sectionsOfTop M s)) := by
  refine Stacks.SheafOfModules.isIso_of_isIso_val_app _ fun A => ?_
  rw [ConcreteCategory.isIso_iff_bijective]
  have hfun : (⇑((M.unitHomEquiv.symm (Stacks.Divisors.sectionsOfTop M s)).val.app A).hom :
      Γ(X, A.unop) → Γ(M, A.unop)) =
      fun r : Γ(X, A.unop) => r • M.presheaf.map (homOfLE (le_top : A.unop ≤ ⊤)).op s :=
    funext fun r => (Scheme.Modules.unitHomEquiv_symm_app_apply M
      (Stacks.Divisors.sectionsOfTop M s) A.unop r).trans
        (by rw [Stacks.Divisors.sectionsOfTop_eval_top])
  show Function.Bijective
    (⇑((M.unitHomEquiv.symm (Stacks.Divisors.sectionsOfTop M s)).val.app A).hom :
      Γ(X, A.unop) → Γ(M, A.unop))
  rw [hfun]
  exact Stacks.NonvanishingSpelling.bijective_smul X M s (W := A.unop) fun y _ => hs y

/-- **Every morphism to projective space is, near every point, the morphism of functions
spanning the unit ideal on an affine open.** -/
theorem exists_isAffineOpen_comp_eq_homOfCoords (g : T ⟶ projectiveSpaceAtUniverse.{u} n)
    (x : T) : ∃ (W : T.Opens) (_ : x ∈ W) (_ : IsAffineOpen W) (b : Fin (n + 1) → Γ(W, ⊤))
      (hb : Ideal.span (Set.range b) = ⊤), W.ι ≫ g = homOfCoords b hb := by
  set t := tautological g
  obtain ⟨i, hi⟩ := Stacks.ProjectiveFromSections.exists_mem_nvCover_of_generatesStalks t.coord
    t.generates x
  obtain ⟨W, hW, hxW, hWi⟩ := exists_isAffineOpen_mem_and_subset hi
  set M' := (Scheme.Modules.pullback W.ι).obj t.bundle
  have : Stacks.Ample.IsInvertibleModule W M' := (pullbackTuple W.ι t).isInvertible
  set s' : Fin (n + 1) → Γ(M', ⊤) := fun k => pullbackGlobalSections W.ι t.bundle (t.coord k)
  have hnv : ∀ y : W, y ∈ Stacks.NonvanishingOpen.nonvanishingOpen W M' (s' i) := fun y =>
    Stacks.TwistPullbackPinned.mem_nonvanishingLocus_pullbackGlobalSections W.ι t.bundle
      (t.coord i) (hWi y.2)
  have hφ := isIso_unitHomEquiv_symm_sectionsOfTop M' (s' i) hnv
  set φ := M'.unitHomEquiv.symm (Stacks.Divisors.sectionsOfTop M' (s' i))
  let β : M' ≅ Stacks.Ample.unitModule W := (@asIso _ _ _ _ φ hφ).symm
  set b : Fin (n + 1) → Γ(W, ⊤) := fun k => Scheme.Modules.Hom.app β.hom ⊤ (s' k)
  have hφ1 : Scheme.Modules.Hom.app φ ⊤
      (show Γ(Stacks.Ample.unitModule W, ⊤) from (1 : Γ(W, ⊤))) = s' i := by
    refine (Scheme.Modules.unitHomEquiv_symm_app_apply M' _ ⊤ 1).trans ?_
    rw [one_smul, Stacks.Divisors.sectionsOfTop_eval_top]
    show M'.presheaf.map (𝟙 _) _ = _
    rw [M'.presheaf.map_id]
    rfl
  have hbi : b i = 1 := by
    show Scheme.Modules.Hom.app β.hom ⊤ (s' i) = _
    rw [← hφ1]
    have h1 : φ ≫ β.hom = 𝟙 _ := (@asIso _ _ _ _ φ hφ).hom_inv_id
    exact congr($(congrArg (fun ψ => Scheme.Modules.Hom.app ψ ⊤) h1)
      (show Γ(Stacks.Ample.unitModule W, ⊤) from (1 : Γ(W, ⊤))))
  have hb : Ideal.span (Set.range b) = ⊤ :=
    (Ideal.eq_top_iff_one _).2 (hbi ▸ Ideal.subset_span ⟨i, rfl⟩)
  refine ⟨W, hxW, hW, b, hb, (pointsEquiv W n).injective ?_⟩
  rw [pointsEquiv_comp, homOfCoords, Equiv.apply_symm_apply]
  exact Quotient.sound ⟨β, fun k => rfl⟩

end Stacks.ProjectiveSpaceModuli

end
