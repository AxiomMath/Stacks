module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AdicArtinRees

/-!
# The comparison map of Stacks 0EG2 on a short exact sequence

Let `I ⊆ 𝔞` be ideals of a Noetherian ring `A`, let `U = Spec(A) ∖ V(𝔞)` and let
`0 → F' → F → F'' → 0` be a short exact sequence of coherent modules on `U`. The comparison maps
of `Stacks.Algebraization.comparisonMap` are natural in the module, so they form a ladder whose
rows are the colimits of sections near the formal locus and the limits of sections of the
quotients `F / Iⁿ F`. If the comparisons for `F` and `F''` are isomorphisms, so is the one for
`F'`, and the comparison for `F` is injective as soon as those for `F'` and `F''` are.

## Main definitions

* `Stacks.Algebraization.sectionsNearVanishingMap`: the morphism of diagrams `V ↦ Γ(V, F)`
  induced by a morphism of modules.

## Main results

* `Stacks.Algebraization.exists_app_eq_of_shortExact`: sections of a short exact sequence of
  modules over any open are exact in the middle.
* `Stacks.Algebraization.colimMap_comp_comparisonMap`: the comparison map is natural in the
  module.
* `Stacks.Algebraization.exists_colimMap_sectionsNearVanishingMap_eq`: the top row of the
  ladder is exact in the middle.
* `Stacks.Algebraization.limMap_formalSectionsMap_comp_eq_zero`: the bottom row of the ladder
  is a complex.
* `Stacks.Algebraization.isIso_comparisonMap_first_of_middle_and_third`: if the comparisons for
  `F` and `F''` are isomorphisms, so is the one for `F'`.
* `Stacks.Algebraization.injective_comparisonMap_middle_of_shortExact` and
  `Stacks.Algebraization.mono_comparisonMap_middle_of_shortExact`: the comparison for `F` is
  injective as soon as those for `F'` and `F''` are.

## References

* [Stacks Project, Tag 0H48](https://stacks.math.columbia.edu/tag/0H48)
* [Stacks Project, Tag 0EG2](https://stacks.math.columbia.edu/tag/0EG2)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace Stacks.Algebraization

open Stacks.LocalCohomology

/-! ### Sections of a short exact sequence of modules -/

/-- A section of the middle term of a short exact sequence killed by the third map comes from the
first. -/
theorem exists_app_eq_of_shortExact {X : Scheme.{u}} (S : ShortComplex X.Modules)
    (hS : S.ShortExact) (U : X.Opens) (y : Γ(S.X₂, U)) (hy : S.g.app U y = 0) :
    ∃ x : Γ(S.X₁, U), S.f.app U x = y := by
  let T : X.Modules ⥤ ModuleCat Γ(X, U) := SheafOfModules.evaluation X.ringCatSheaf (op U)
  have _ : T.PreservesZeroMorphisms := ⟨by intros; rfl⟩
  have _ : PreservesFiniteLimits T :=
    SheafOfModules.Finite.evaluationPreservesFiniteLimits X.ringCatSheaf (op U)
  exact (ShortComplex.moduleCat_exact_iff _).mp
    (hS.exact.map_of_mono_of_preservesKernel T hS.mono_f inferInstance) y hy

/-! ### Sections near the formal locus are functorial in the module -/

/-- The morphism of diagrams `V ↦ Γ(V, F)` of sections near the formal locus induced by a
morphism `f : F ⟶ G` of modules on `U = Spec(A) ∖ V(𝔞)`. -/
def sectionsNearVanishingMap (A : Type u) [CommRing A] (I a : Ideal A)
    {F G : (complementZeroLocus A a : Scheme).Modules} (f : F ⟶ G) :
    sectionsNearVanishing A I a F ⟶ sectionsNearVanishing A I a G where
  app V := f.app V.openSet
  naturality _ _ g := f.mapPresheaf.naturality (homOfLE g.down).op

/-- The component at a neighbourhood of the induced morphism of diagrams of sections. -/
theorem sectionsNearVanishingMap_app (A : Type u) [CommRing A] (I a : Ideal A)
    {F G : (complementZeroLocus A a : Scheme).Modules} (f : F ⟶ G)
    (V : OpensNearVanishing A I a) :
    (sectionsNearVanishingMap A I a f).app V = f.app V.openSet :=
  rfl

/-- Shrinking the neighbourhood commutes with the map induced by `f` on sections. -/
theorem sectionsNearVanishingMap_map_apply (A : Type u) [CommRing A] (I a : Ideal A)
    {F G : (complementZeroLocus A a : Scheme).Modules} (f : F ⟶ G)
    {V W : OpensNearVanishing A I a} (g : V ⟶ W)
    (y : ToType ((sectionsNearVanishing A I a F).obj V)) :
    ConcreteCategory.hom ((sectionsNearVanishing A I a G).map g)
        (ConcreteCategory.hom ((sectionsNearVanishingMap A I a f).app V) y) =
      ConcreteCategory.hom ((sectionsNearVanishingMap A I a f).app W)
        (ConcreteCategory.hom ((sectionsNearVanishing A I a F).map g) y) := by
  have h := ConcreteCategory.congr_hom ((sectionsNearVanishingMap A I a f).naturality g) y
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at h
  exact h.symm

/-! ### Naturality of the comparison map -/

/-- The map `F / Iⁿ F ⟶ G / Iⁿ G` induced by `f`, read on sections over a neighbourhood `V` of
the formal locus. -/
def quotientMapNearVanishing (A : Type u) [CommRing A] (I a : Ideal A)
    {F G : (complementZeroLocus A a : Scheme).Modules} (f : F ⟶ G)
    (V : OpensNearVanishing A I a) (n : ℕᵒᵖ) :
    Γ((quotientSystemNearVanishing A I a F).obj n, V.openSet) ⟶
      Γ((quotientSystemNearVanishing A I a G).obj n, V.openSet) :=
  (idealPowerQuotientMap (idealSheafNearVanishing A I a) (idealSheafNearVanishing A I a)
    n.unop n.unop le_rfl f).app V.openSet

/-- Restriction from `U` to a neighbourhood `V` of the formal locus intertwines the maps induced
by `f` on the quotient towers. -/
theorem resNearVanishing_comp_quotientMapNearVanishing (A : Type u) [CommRing A] (I a : Ideal A)
    {F G : (complementZeroLocus A a : Scheme).Modules} (f : F ⟶ G)
    (V : OpensNearVanishing A I a) (n : ℕᵒᵖ) :
    resNearVanishing A I a F V n ≫ quotientMapNearVanishing A I a f V n =
      (formalSectionsMap A I a f).app n ≫ resNearVanishing A I a G V n :=
  (idealPowerQuotientMap (idealSheafNearVanishing A I a) (idealSheafNearVanishing A I a)
    n.unop n.unop le_rfl f).mapPresheaf.naturality (homOfLE (le_top (a := V.openSet))).op

/-- Reduction modulo `Iⁿ` on a neighbourhood `V` of the formal locus commutes with `f`. -/
theorem projNearVanishing_comp_quotientMapNearVanishing (A : Type u) [CommRing A] (I a : Ideal A)
    {F G : (complementZeroLocus A a : Scheme).Modules} (f : F ⟶ G)
    (V : OpensNearVanishing A I a) (n : ℕᵒᵖ) :
    projNearVanishing A I a F V n ≫ quotientMapNearVanishing A I a f V n =
      (sectionsNearVanishingMap A I a f).app V ≫ projNearVanishing A I a G V n :=
  congrArg
    (fun φ : F ⟶ idealPowerQuotient (idealSheafNearVanishing A I a) n.unop G ↦
      φ.app V.openSet)
    (idealPowerQuotientMap_π (idealSheafNearVanishing A I a) (idealSheafNearVanishing A I a)
      n.unop n.unop le_rfl f)

/-- The comparison map is natural in the module: the square formed by the comparisons for `F` and
`G`, the colimit of sections near the formal locus and the limit of sections of the adic quotients
commutes. -/
theorem colimMap_comp_comparisonMap (A : Type u) [CommRing A] (I a : Ideal A)
    {F G : (complementZeroLocus A a : Scheme).Modules} (f : F ⟶ G) :
    colimMap (sectionsNearVanishingMap A I a f) ≫ comparisonMap A I a G =
      comparisonMap A I a F ≫ limMap (formalSectionsMap A I a f) := by
  refine colimit.hom_ext fun V ↦ ?_
  rw [← Category.assoc, ι_colimMap, Category.assoc, colimit_ι_comp_comparisonMap,
    ← Category.assoc, colimit_ι_comp_comparisonMap]
  refine limit.hom_ext fun n ↦ ?_
  have : Mono (resNearVanishing A I a G V n) := IsIso.mono_of_iso _
  rw [Category.assoc, comparisonAt_π, Category.assoc, limMap_π, comparisonAt_π_assoc,
    ← cancel_mono (resNearVanishing A I a G V n)]
  simp only [Category.assoc]
  rw [IsIso.inv_hom_id (resNearVanishing A I a G V n), Category.comp_id,
    ← resNearVanishing_comp_quotientMapNearVanishing,
    ← Category.assoc (inv (resNearVanishing A I a F V n)),
    IsIso.inv_hom_id (resNearVanishing A I a F V n), Category.id_comp,
    projNearVanishing_comp_quotientMapNearVanishing]

/-- The induced map on the colimit, read on a section over a single neighbourhood. -/
theorem colimMap_ι_apply (A : Type u) [CommRing A] (I a : Ideal A)
    {F G : (complementZeroLocus A a : Scheme).Modules} (f : F ⟶ G)
    (V : OpensNearVanishing A I a) (x : ToType ((sectionsNearVanishing A I a F).obj V)) :
    ConcreteCategory.hom (colimMap (sectionsNearVanishingMap A I a f))
        (ConcreteCategory.hom (colimit.ι (sectionsNearVanishing A I a F) V) x) =
      ConcreteCategory.hom (colimit.ι (sectionsNearVanishing A I a G) V)
        (ConcreteCategory.hom ((sectionsNearVanishingMap A I a f).app V) x) := by
  have h := ConcreteCategory.congr_hom (ι_colimMap (sectionsNearVanishingMap A I a f) V) x
  rwa [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at h

/-- Naturality of the comparison map, read on elements. -/
theorem comparisonMap_apply_colimMap (A : Type u) [CommRing A] (I a : Ideal A)
    {F G : (complementZeroLocus A a : Scheme).Modules} (f : F ⟶ G)
    (z : ToType (colimit (sectionsNearVanishing A I a F))) :
    ConcreteCategory.hom (comparisonMap A I a G)
        (ConcreteCategory.hom (colimMap (sectionsNearVanishingMap A I a f)) z) =
      ConcreteCategory.hom (limMap (formalSectionsMap A I a f))
        (ConcreteCategory.hom (comparisonMap A I a F) z) := by
  have h := ConcreteCategory.congr_hom (colimMap_comp_comparisonMap A I a f) z
  rwa [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at h

/-! ### The bottom row of the ladder is a complex -/

/-- The map induced on ideal-power quotients by the zero morphism is zero. -/
theorem idealPowerQuotientMap_zero {X : Scheme.{u}} (I : X.IdealSheafData) (n : ℕ)
    (M N : X.Modules) :
    idealPowerQuotientMap I I n n le_rfl (0 : M ⟶ N) = 0 := by
  refine (cancel_epi (cokernel.π (C := X.Modules) (idealPowerMultiple I n M).ι)).1 ?_
  rw [idealPowerQuotientMap_π, comp_zero, zero_comp]

/-- At each level, the two maps of the bottom row of the ladder compose to zero. -/
theorem formalSectionsMap_app_comp_app_eq_zero (A : Type u) [CommRing A] (I a : Ideal A)
    (S : ShortComplex (complementZeroLocus A a : Scheme).Modules) (n : ℕᵒᵖ) :
    (formalSectionsMap A I a S.f).app n ≫ (formalSectionsMap A I a S.g).app n = 0 := by
  have h1 : idealPowerQuotientMap (idealSheafNearVanishing A I a)
        (idealSheafNearVanishing A I a) n.unop n.unop le_rfl S.f ≫
      idealPowerQuotientMap (idealSheafNearVanishing A I a)
        (idealSheafNearVanishing A I a) n.unop n.unop le_rfl S.g = 0 := by
    rw [← idealPowerQuotientMap_comp, S.zero, idealPowerQuotientMap_zero]
  exact congrArg
    (fun φ : idealPowerQuotient (idealSheafNearVanishing A I a) n.unop S.X₁ ⟶
      idealPowerQuotient (idealSheafNearVanishing A I a) n.unop S.X₃ ↦ φ.app ⊤) h1

/-- The maps induced by a short complex on the limits of sections of the adic quotients compose to
zero. -/
theorem limMap_formalSectionsMap_comp_eq_zero (A : Type u) [CommRing A] (I a : Ideal A)
    (S : ShortComplex (complementZeroLocus A a : Scheme).Modules) :
    limMap (formalSectionsMap A I a S.f) ≫ limMap (formalSectionsMap A I a S.g) = 0 := by
  refine limit.hom_ext fun n ↦ ?_
  rw [Category.assoc, limMap_π, ← Category.assoc, limMap_π, Category.assoc,
    formalSectionsMap_app_comp_app_eq_zero A I a S n, comp_zero, zero_comp]

/-- The bottom row of the ladder is a complex, read on elements. -/
theorem limMap_formalSectionsMap_apply_eq_zero (A : Type u) [CommRing A] (I a : Ideal A)
    (S : ShortComplex (complementZeroLocus A a : Scheme).Modules)
    (w : ToType (limit (formalSections A I a S.X₁))) :
    ConcreteCategory.hom (limMap (formalSectionsMap A I a S.g))
      (ConcreteCategory.hom (limMap (formalSectionsMap A I a S.f)) w) = 0 := by
  have h := ConcreteCategory.congr_hom (limMap_formalSectionsMap_comp_eq_zero A I a S) w
  rw [ConcreteCategory.comp_apply] at h
  simpa using h

/-! ### The top row of the ladder is left exact -/

/-- A section near the formal locus whose class in the colimit vanishes already vanishes on some
smaller neighbourhood. -/
theorem exists_map_eq_zero_of_colimit_ι_eq_zero (A : Type u) [CommRing A] (I a : Ideal A)
    (F : (complementZeroLocus A a : Scheme).Modules) (V : OpensNearVanishing A I a)
    (y : ToType ((sectionsNearVanishing A I a F).obj V))
    (hy : ConcreteCategory.hom (colimit.ι (sectionsNearVanishing A I a F) V) y = 0) :
    ∃ (W : OpensNearVanishing A I a) (g : V ⟶ W),
      ConcreteCategory.hom ((sectionsNearVanishing A I a F).map g) y = 0 := by
  have hforget : PreservesFilteredColimitsOfSize.{0, u} (forget Ab.{u}) :=
    preservesFilteredColimitsOfSize_of_univLE.{u, u, 0, u} _
  have hy0 : ConcreteCategory.hom (colimit.ι (sectionsNearVanishing A I a F) V) y =
      ConcreteCategory.hom (colimit.ι (sectionsNearVanishing A I a F) V) 0 := by
    rwa [map_zero]
  obtain ⟨W, g1, _g2, hg⟩ :=
    Concrete.colimit_exists_of_rep_eq (sectionsNearVanishing A I a F) y 0 hy0
  exact ⟨W, g1, hg.trans (map_zero _)⟩

/-- A class killed by the colimit map of `f` is represented by a section killed by `f`. -/
private theorem exists_rep_app_eq_zero_of_colimMap_eq_zero (A : Type u) [CommRing A]
    (I a : Ideal A) {F G : (complementZeroLocus A a : Scheme).Modules} (f : F ⟶ G)
    (z : ToType (colimit (sectionsNearVanishing A I a F)))
    (hz : ConcreteCategory.hom (colimMap (sectionsNearVanishingMap A I a f)) z = 0) :
    ∃ (W : OpensNearVanishing A I a) (y : ToType ((sectionsNearVanishing A I a F).obj W)),
      ConcreteCategory.hom (colimit.ι (sectionsNearVanishing A I a F) W) y = z ∧
        ConcreteCategory.hom ((sectionsNearVanishingMap A I a f).app W) y = 0 := by
  have hforget : PreservesFilteredColimitsOfSize.{0, u} (forget Ab.{u}) :=
    preservesFilteredColimitsOfSize_of_univLE.{u, u, 0, u} _
  obtain ⟨V, y, rfl⟩ := Concrete.colimit_exists_rep (sectionsNearVanishing A I a F) z
  rw [colimMap_ι_apply] at hz
  obtain ⟨W, g, hg⟩ := exists_map_eq_zero_of_colimit_ι_eq_zero A I a G V _ hz
  have hw := ConcreteCategory.congr_hom (colimit.w (sectionsNearVanishing A I a F) g) y
  rw [ConcreteCategory.comp_apply] at hw
  exact ⟨W, _, hw, (sectionsNearVanishingMap_map_apply A I a f g y).symm.trans hg⟩

/-- A monomorphism of modules induces an injective map on the colimits of sections near the formal
locus. -/
theorem injective_colimMap_sectionsNearVanishingMap (A : Type u) [CommRing A] (I a : Ideal A)
    {F G : (complementZeroLocus A a : Scheme).Modules} (f : F ⟶ G)
    (hf : Mono (C := (complementZeroLocus A a : Scheme).Modules) f) :
    Function.Injective
      (ConcreteCategory.hom (colimMap (sectionsNearVanishingMap A I a f))) := by
  refine (injective_iff_map_eq_zero _).2 fun z hz ↦ ?_
  obtain ⟨W, y, rfl, hy⟩ := exists_rep_app_eq_zero_of_colimMap_eq_zero A I a f z hz
  rw [app_injective_of_mono f hf W.openSet (hy.trans (map_zero _).symm)]
  exact map_zero _

/-- A class of sections near the formal locus of the middle term of a short exact sequence killed
by the third map comes from the first. -/
theorem exists_colimMap_sectionsNearVanishingMap_eq (A : Type u) [CommRing A] (I a : Ideal A)
    (S : ShortComplex (complementZeroLocus A a : Scheme).Modules) (hS : S.ShortExact)
    (w : ToType (colimit (sectionsNearVanishing A I a S.X₂)))
    (hw : ConcreteCategory.hom (colimMap (sectionsNearVanishingMap A I a S.g)) w = 0) :
    ∃ z, ConcreteCategory.hom (colimMap (sectionsNearVanishingMap A I a S.f)) z = w := by
  obtain ⟨W, y, rfl, hy⟩ := exists_rep_app_eq_zero_of_colimMap_eq_zero A I a S.g w hw
  obtain ⟨x, hx⟩ := exists_app_eq_of_shortExact S hS W.openSet y hy
  exact ⟨_, (colimMap_ι_apply A I a S.f W x).trans
    (congrArg (ConcreteCategory.hom (colimit.ι (sectionsNearVanishing A I a S.X₂) W)) hx)⟩

/-! ### The first comparison of Stacks 0H48 -/

/-- For a short exact sequence `0 → F' → F → F'' → 0` of
coherent modules on `U = Spec(A) ∖ V(𝔞)` with `A` Noetherian, if the comparison maps of
`Stacks.Algebraization.comparisonMap` for `F` and `F''` are isomorphisms, so is that for `F'`. -/
@[stacks 0H48 "first comparison"]
theorem isIso_comparisonMap_first_of_middle_and_third
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I a : Ideal A)
    (S : ShortComplex (complementZeroLocus A a : Scheme).Modules) (hS : S.ShortExact)
    [S.X₁.IsCoherent] [S.X₂.IsCoherent] [S.X₃.IsCoherent]
    (h₂ : IsIso (comparisonMap A I a S.X₂)) (h₃ : IsIso (comparisonMap A I a S.X₃)) :
    IsIso (comparisonMap A I a S.X₁) := by
  have hBf := injective_limMap_formalSectionsMap A I a S.f hS.mono_f
  have hAf := injective_colimMap_sectionsNearVanishingMap A I a S.f hS.mono_f
  have hc₂ := (ConcreteCategory.isIso_iff_bijective (comparisonMap A I a S.X₂)).1 h₂
  have hc₃ := (ConcreteCategory.isIso_iff_bijective (comparisonMap A I a S.X₃)).1 h₃
  rw [ConcreteCategory.isIso_iff_bijective]
  refine ⟨(injective_iff_map_eq_zero _).2 fun z hz ↦ ?_, fun w ↦ ?_⟩
  · have h1 := comparisonMap_apply_colimMap A I a S.f z
    rw [hz, map_zero] at h1
    exact hAf ((hc₂.1 (h1.trans (map_zero _).symm)).trans (map_zero _).symm)
  · obtain ⟨y, hy⟩ := hc₂.2 (ConcreteCategory.hom (limMap (formalSectionsMap A I a S.f)) w)
    have hgy : ConcreteCategory.hom (comparisonMap A I a S.X₃)
        (ConcreteCategory.hom (colimMap (sectionsNearVanishingMap A I a S.g)) y) = 0 := by
      rw [comparisonMap_apply_colimMap A I a S.g y, hy]
      exact limMap_formalSectionsMap_apply_eq_zero A I a S w
    obtain ⟨z, hz⟩ := exists_colimMap_sectionsNearVanishingMap_eq A I a S hS y
      (hc₃.1 (hgy.trans (map_zero _).symm))
    refine ⟨z, ?_⟩
    have h1 := comparisonMap_apply_colimMap A I a S.f z
    rw [hz, hy] at h1
    exact hBf h1.symm

/-! ### Injectivity of the middle comparison -/

/-- For a short exact sequence `0 → F' → F → F'' → 0` of coherent modules, if the comparison maps
for `F'` and `F''` are injective, so is the one for `F`. -/
theorem injective_comparisonMap_middle_of_shortExact
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I a : Ideal A)
    (S : ShortComplex (complementZeroLocus A a : Scheme).Modules) (hS : S.ShortExact)
    [S.X₁.IsCoherent] [S.X₂.IsCoherent] [S.X₃.IsCoherent]
    (h₁ : Function.Injective (ConcreteCategory.hom (comparisonMap A I a S.X₁)))
    (h₃ : Function.Injective (ConcreteCategory.hom (comparisonMap A I a S.X₃))) :
    Function.Injective (ConcreteCategory.hom (comparisonMap A I a S.X₂)) := by
  refine (injective_iff_map_eq_zero _).2 fun z hz ↦ ?_
  have h3 : ConcreteCategory.hom (comparisonMap A I a S.X₃)
      (ConcreteCategory.hom (colimMap (sectionsNearVanishingMap A I a S.g)) z) = 0 := by
    rw [comparisonMap_apply_colimMap A I a S.g z, hz, map_zero]
  obtain ⟨y, hy⟩ := exists_colimMap_sectionsNearVanishingMap_eq A I a S hS z
    (h₃ (h3.trans (map_zero _).symm))
  have h1 : ConcreteCategory.hom (limMap (formalSectionsMap A I a S.f))
      (ConcreteCategory.hom (comparisonMap A I a S.X₁) y) = 0 := by
    rw [← comparisonMap_apply_colimMap A I a S.f y, hy, hz]
  rw [← hy, h₁ ((injective_limMap_formalSectionsMap A I a S.f hS.mono_f
    (h1.trans (map_zero _).symm)).trans (map_zero _).symm), map_zero]

/-- The middle comparison of a short exact sequence is a monomorphism once the outer two are. -/
theorem mono_comparisonMap_middle_of_shortExact
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I a : Ideal A)
    (S : ShortComplex (complementZeroLocus A a : Scheme).Modules) (hS : S.ShortExact)
    [S.X₁.IsCoherent] [S.X₂.IsCoherent] [S.X₃.IsCoherent]
    (h₁ : Mono (comparisonMap A I a S.X₁)) (h₃ : Mono (comparisonMap A I a S.X₃)) :
    Mono (comparisonMap A I a S.X₂) :=
  ConcreteCategory.mono_of_injective _
    (injective_comparisonMap_middle_of_shortExact A I a S hS
      ((ConcreteCategory.mono_iff_injective_of_preservesPullback _).1 h₁)
      ((ConcreteCategory.mono_iff_injective_of_preservesPullback _).1 h₃))

end Stacks.Algebraization

end
