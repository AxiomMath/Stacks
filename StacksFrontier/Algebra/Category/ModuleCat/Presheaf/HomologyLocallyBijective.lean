module

public import Mathlib.Algebra.Category.Grp.EpiMono
public import Mathlib.Algebra.Homology.ShortComplex.Ab
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.SectionwiseLocallyQuasiIso

/-!
# Local bijectivity of a map of homology presheaves, by a chase of sections

A map `φ : K ⟶ L` of complexes of presheaves of modules induces maps of homology presheaves,
and `PresheafOfModules.quasiIso_sheafification_map_of_isLocallyBijective` turns their local
bijectivity into a quasi-isomorphism after sheafification. This file reduces that local
bijectivity to statements about *sections of the complexes themselves*: a cycle of `L` is locally
homologous to the image of a cycle of `K`, and a cycle of `K` whose image is a boundary is locally
a boundary.

## Main results

* `HomologicalComplex.exists_iCycles_apply_eq`, `HomologicalComplex.iCycles_apply_injective`,
  `HomologicalComplex.homologyπ_apply_surjective` and
  `HomologicalComplex.exists_toCycles_apply_eq_of_homologyπ_apply_eq_zero`: the cycles and the
  homology of a complex, read through an exact functor to abelian groups.
* `PresheafOfModules.isLocallySurjective_homologyMap`: the map of homology presheaves is locally
  surjective as soon as every cycle of `L` is locally homologous to the image of a cycle of
  `K`.
* `PresheafOfModules.isLocallyInjective_homologyMap`: it is locally injective as soon as every
  cycle of `K` whose image is a boundary is locally a boundary.
* `HomologicalComplex.exists_cycle_eq_add_d_of_quasiIsoAt` and
  `HomologicalComplex.exists_d_eq_of_quasiIsoAt`: the two conditions hold, with no covering at
  all, for a quasi-isomorphism of complexes of modules over a ring.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe w v' u' v u

namespace HomologicalComplex

section Elements

variable {A : Type u} [Category.{v} A] [Abelian A] (G : A ⥤ AddCommGrpCat.{w}) [G.Additive]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  {ι : Type*} {c : ComplexShape ι} (K : HomologicalComplex A c)

/-- **A cycle, read through an exact functor to abelian groups, comes from the cycles.** -/
theorem exists_iCycles_apply_eq {i j : ι} (hij : c.next i = j) (z : G.obj (K.X i))
    (hz : G.map (K.d i j) z = 0) : ∃ w : G.obj (K.cycles i), G.map (K.iCycles i) w = z := by
  subst hij
  have hS : (ShortComplex.mk (K.iCycles i) (K.d i (c.next i)) (K.iCycles_d _ _)).Exact :=
    ShortComplex.exact_of_f_is_kernel _ (K.cyclesIsKernel i _ rfl)
  exact (ShortComplex.ab_exact_iff _).1 (hS.map G) z hz

/-- **The inclusion of the cycles stays injective through an exact functor to abelian
groups.** -/
theorem iCycles_apply_injective (i : ι) : Function.Injective (G.map (K.iCycles i)) :=
  (AddCommGrpCat.mono_iff_injective _).1 inferInstance

/-- **The projection onto homology stays surjective through an exact functor to abelian
groups.** -/
theorem homologyπ_apply_surjective (i : ι) : Function.Surjective (G.map (K.homologyπ i)) :=
  (AddCommGrpCat.epi_iff_surjective _).1 inferInstance

/-- **A cycle with zero homology class, read through an exact functor to abelian groups, is a
boundary.** -/
theorem exists_toCycles_apply_eq_of_homologyπ_apply_eq_zero {i j : ι} (hij : c.prev j = i)
    (w : G.obj (K.cycles j)) (hw : G.map (K.homologyπ j) w = 0) :
    ∃ y : G.obj (K.X i), G.map (K.toCycles i j) y = w := by
  have hS : (ShortComplex.mk (K.toCycles i j) (K.homologyπ j)
      (K.toCycles_comp_homologyπ i j)).Exact :=
    ShortComplex.exact_of_g_is_cokernel _ (K.homologyIsCokernel i j hij)
  exact (ShortComplex.ab_exact_iff _).1 (hS.map G) w hw

omit [PreservesFiniteLimits G] [PreservesFiniteColimits G] in
/-- The homology class of `G.map (toCycles)` of an element vanishes. -/
theorem homologyπ_apply_toCycles_apply (i j : ι) (y : G.obj (K.X i)) :
    G.map (K.homologyπ j) (G.map (K.toCycles i j) y) = 0 := by
  rw [← ConcreteCategory.comp_apply, ← G.map_comp, toCycles_comp_homologyπ, G.map_zero]
  rfl

/-- Two cycles whose images in `K.X i` differ by a boundary have the same homology class. -/
theorem homologyπ_apply_eq_of_iCycles_apply_eq_add {i k : ι} (_hki : c.prev i = k)
    (w w' : G.obj (K.cycles i)) (y : G.obj (K.X k))
    (h : G.map (K.iCycles i) w = G.map (K.iCycles i) w' + G.map (K.d k i) y) :
    G.map (K.homologyπ i) w = G.map (K.homologyπ i) w' := by
  have hw : w = w' + G.map (K.toCycles k i) y := by
    refine iCycles_apply_injective G K i ?_
    rw [map_add, ← ConcreteCategory.comp_apply, ← G.map_comp, toCycles_i, h]
  rw [hw, map_add, homologyπ_apply_toCycles_apply, add_zero]

end Elements

/-- The differential kills the image of a cycle. -/
private theorem map_d_map_iCycles {A : Type u} [Category.{v} A] [Abelian A]
    (G : A ⥤ AddCommGrpCat.{w}) [G.Additive] {ι : Type*} {c : ComplexShape ι}
    (K : HomologicalComplex A c) (i j : ι) (w : G.obj (K.cycles i)) :
    G.map (K.d i j) (G.map (K.iCycles i) w) = 0 := by
  rw [← ConcreteCategory.comp_apply, ← G.map_comp, iCycles_d, G.map_zero]
  rfl

/-- `cyclesMap` is compatible with `iCycles`, elementwise. -/
private theorem map_iCycles_map_cyclesMap {A : Type u} [Category.{v} A] [Abelian A]
    (G : A ⥤ AddCommGrpCat.{w}) {ι : Type*} {c : ComplexShape ι}
    {K L : HomologicalComplex A c} (φ : K ⟶ L) (i : ι) (w : G.obj (K.cycles i)) :
    G.map (L.iCycles i) (G.map (cyclesMap φ i) w) = G.map (φ.f i) (G.map (K.iCycles i) w) := by
  rw [← ConcreteCategory.comp_apply, ← G.map_comp, cyclesMap_i, G.map_comp,
    ConcreteCategory.comp_apply]

/-- `cyclesMap` is compatible with `homologyπ`, elementwise. -/
private theorem map_homologyπ_map_cyclesMap {A : Type u} [Category.{v} A] [Abelian A]
    (G : A ⥤ AddCommGrpCat.{w}) {ι : Type*} {c : ComplexShape ι}
    {K L : HomologicalComplex A c} (φ : K ⟶ L) (i : ι) (w : G.obj (K.cycles i)) :
    G.map (L.homologyπ i) (G.map (cyclesMap φ i) w) =
      G.map (homologyMap φ i) (G.map (K.homologyπ i) w) := by
  rw [← ConcreteCategory.comp_apply, ← G.map_comp, ← homologyπ_naturality, G.map_comp,
    ConcreteCategory.comp_apply]

/-- `toCycles` followed by `iCycles` is the differential, elementwise. -/
private theorem map_iCycles_map_toCycles {A : Type u} [Category.{v} A] [Abelian A]
    (G : A ⥤ AddCommGrpCat.{w}) {ι : Type*} {c : ComplexShape ι}
    (K : HomologicalComplex A c) (i j : ι) (y : G.obj (K.X i)) :
    G.map (K.iCycles j) (G.map (K.toCycles i j) y) = G.map (K.d i j) y := by
  rw [← ConcreteCategory.comp_apply, ← G.map_comp, toCycles_i]

end HomologicalComplex

namespace PresheafOfModules

variable {C : Type u'} [Category.{v'} C] {J : GrothendieckTopology C}
  {R₀ : Cᵒᵖ ⥤ RingCat.{u}} {ι : Type*} {c : ComplexShape ι}
  {K L : HomologicalComplex (PresheafOfModules.{v} R₀) c} (φ : K ⟶ L)

/-- Sections over `V` as an abelian group: evaluation at `V` after forgetting the module
structure. -/
abbrev sectionsAb (V : Cᵒᵖ) : PresheafOfModules.{v} R₀ ⥤ AddCommGrpCat.{v} :=
  toPresheaf.{v} R₀ ⋙ (CategoryTheory.evaluation Cᵒᵖ AddCommGrpCat.{v}).obj V

/-- Restriction of sections commutes with a map of presheaves, elementwise. -/
theorem toPresheaf_map_app_restrict {M N : PresheafOfModules.{v} R₀} (f : M ⟶ N) {V W : C}
    (b : W ⟶ V) (x : ((toPresheaf.{v} R₀).obj M).obj (op V)) :
    ((toPresheaf.{v} R₀).obj N).map b.op (((toPresheaf.{v} R₀).map f).app (op V) x) =
      ((toPresheaf.{v} R₀).map f).app (op W) (((toPresheaf.{v} R₀).obj M).map b.op x) := by
  rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, NatTrans.naturality]

/-- **Local surjectivity on homology, by a chase of sections.** If every cycle `z` of `L` over
`V` is, after restriction along each arrow of some covering sieve, the image of a cycle of `K`
up to a boundary of `L`, then the map of `i`-th homology presheaves is locally surjective. -/
theorem isLocallySurjective_homologyMap (i : ι)
    (h : ∀ (V : C) (z : ((toPresheaf.{v} R₀).obj (L.X i)).obj (op V)),
      ((toPresheaf.{v} R₀).map (L.d i (c.next i))).app (op V) z = 0 →
        ∃ S : Sieve V, S ∈ J V ∧ ∀ ⦃W : C⦄ (b : W ⟶ V), S b →
          ∃ z' : ((toPresheaf.{v} R₀).obj (K.X i)).obj (op W),
            ((toPresheaf.{v} R₀).map (K.d i (c.next i))).app (op W) z' = 0 ∧
            ∃ y : ((toPresheaf.{v} R₀).obj (L.X (c.prev i))).obj (op W),
              ((toPresheaf.{v} R₀).obj (L.X i)).map b.op z =
                ((toPresheaf.{v} R₀).map (φ.f i)).app (op W) z' +
                  ((toPresheaf.{v} R₀).map (L.d (c.prev i) i)).app (op W) y) :
    Presheaf.IsLocallySurjective J
      ((toPresheaf.{v} R₀).map (HomologicalComplex.homologyMap φ i)) := by
  refine Presheaf.isLocallySurjective_of_forall_exists_mem_sieve J _ fun V s => ?_
  obtain ⟨w, rfl⟩ := HomologicalComplex.homologyπ_apply_surjective (sectionsAb (op V)) L i s
  obtain ⟨S, hS, hloc⟩ := h V _ (HomologicalComplex.map_d_map_iCycles (sectionsAb (op V)) L _ _ w)
  refine ⟨S, hS, fun W b hb => ?_⟩
  obtain ⟨z', hz', y, hy⟩ := hloc b hb
  obtain ⟨w', rfl⟩ := HomologicalComplex.exists_iCycles_apply_eq (sectionsAb (op W)) K rfl z' hz'
  refine ⟨(sectionsAb (op W)).map (K.homologyπ i) w', ?_⟩
  change (sectionsAb (op W)).map (HomologicalComplex.homologyMap φ i)
      ((sectionsAb (op W)).map (K.homologyπ i) w') =
    ((toPresheaf.{v} R₀).obj (L.homology i)).map b.op
      (((toPresheaf.{v} R₀).map (L.homologyπ i)).app (op V) w)
  rw [toPresheaf_map_app_restrict, ← HomologicalComplex.map_homologyπ_map_cyclesMap]
  refine HomologicalComplex.homologyπ_apply_eq_of_iCycles_apply_eq_add (sectionsAb (op W)) L
    rfl _ _ (-y) ?_
  rw [HomologicalComplex.map_iCycles_map_cyclesMap, map_neg]
  change _ = ((toPresheaf.{v} R₀).map (L.iCycles i)).app (op W)
      (((toPresheaf.{v} R₀).obj (L.cycles i)).map b.op w) + _
  rw [← toPresheaf_map_app_restrict]
  change _ = ((toPresheaf.{v} R₀).obj (L.X i)).map b.op
      ((sectionsAb (op V)).map (L.iCycles i) w) + _
  rw [hy]
  dsimp only [sectionsAb, Functor.comp_map, evaluation_obj_map]
  abel

/-- **Local injectivity on homology, by a chase of sections.** If every cycle `z'` of `K` over
`V` whose image in `L` is a boundary becomes, after restriction along each arrow of some
covering sieve, a boundary of `K`, then the map of `i`-th homology presheaves is locally
injective. -/
theorem isLocallyInjective_homologyMap (i : ι)
    (h : ∀ (V : C) (z' : ((toPresheaf.{v} R₀).obj (K.X i)).obj (op V)),
      ((toPresheaf.{v} R₀).map (K.d i (c.next i))).app (op V) z' = 0 →
      ∀ y : ((toPresheaf.{v} R₀).obj (L.X (c.prev i))).obj (op V),
        ((toPresheaf.{v} R₀).map (φ.f i)).app (op V) z' =
          ((toPresheaf.{v} R₀).map (L.d (c.prev i) i)).app (op V) y →
        ∃ S : Sieve V, S ∈ J V ∧ ∀ ⦃W : C⦄ (b : W ⟶ V), S b →
          ∃ y' : ((toPresheaf.{v} R₀).obj (K.X (c.prev i))).obj (op W),
            ((toPresheaf.{v} R₀).obj (K.X i)).map b.op z' =
              ((toPresheaf.{v} R₀).map (K.d (c.prev i) i)).app (op W) y') :
    Presheaf.IsLocallyInjective J
      ((toPresheaf.{v} R₀).map (HomologicalComplex.homologyMap φ i)) := by
  refine Presheaf.isLocallyInjective_of_forall_exists_mem_sieve J _ fun V s₁ s₂ hs => ?_
  obtain ⟨w, hw⟩ := HomologicalComplex.homologyπ_apply_surjective (sectionsAb (op V)) K i
    (s₁ - s₂)
  have hzero : (sectionsAb (op V)).map (L.homologyπ i)
      ((sectionsAb (op V)).map (HomologicalComplex.cyclesMap φ i) w) = 0 := by
    rw [HomologicalComplex.map_homologyπ_map_cyclesMap, hw, map_sub]
    exact sub_eq_zero.2 hs
  obtain ⟨y, hy⟩ := HomologicalComplex.exists_toCycles_apply_eq_of_homologyπ_apply_eq_zero
    (sectionsAb (op V)) L rfl _ hzero
  have hφ : (sectionsAb (op V)).map (φ.f i) ((sectionsAb (op V)).map (K.iCycles i) w) =
      (sectionsAb (op V)).map (L.d (c.prev i) i) y := by
    rw [← HomologicalComplex.map_iCycles_map_cyclesMap, ← hy,
      HomologicalComplex.map_iCycles_map_toCycles]
  obtain ⟨S, hS, hloc⟩ :=
    h V _ (HomologicalComplex.map_d_map_iCycles (sectionsAb (op V)) K _ _ w) y hφ
  refine ⟨S, hS, fun W b hb => ?_⟩
  obtain ⟨y', hy'⟩ := hloc b hb
  rw [← sub_eq_zero, ← map_sub, ← hw]
  change ((toPresheaf.{v} R₀).obj (K.homology i)).map b.op
      (((toPresheaf.{v} R₀).map (K.homologyπ i)).app (op V) w) = 0
  rw [toPresheaf_map_app_restrict]
  refine ((HomologicalComplex.homologyπ_apply_eq_of_iCycles_apply_eq_add (sectionsAb (op W)) K
    rfl _ 0 y' ?_).trans (map_zero _))
  change ((toPresheaf.{v} R₀).map (K.iCycles i)).app (op W)
      (((toPresheaf.{v} R₀).obj (K.cycles i)).map b.op w) = _
  rw [← toPresheaf_map_app_restrict, map_zero, zero_add]
  exact hy'

end PresheafOfModules

namespace HomologicalComplex

variable {A : Type v} [Ring A] {ι : Type*} {c : ComplexShape ι}
  {K L : HomologicalComplex (ModuleCat.{v} A) c} (φ : K ⟶ L)

/-- **A quasi-isomorphism of complexes of modules is surjective on cycles up to boundaries**:
every cycle of the target is the image of a cycle of the source plus a boundary. -/
theorem exists_cycle_eq_add_d_of_quasiIsoAt (i : ι) [QuasiIsoAt φ i] (z : L.X i)
    (hz : L.d i (c.next i) z = 0) :
    ∃ z' : K.X i, K.d i (c.next i) z' = 0 ∧
      ∃ y : L.X (c.prev i), z = φ.f i z' + L.d (c.prev i) i y := by
  let G := forget₂ (ModuleCat.{v} A) AddCommGrpCat.{v}
  obtain ⟨w, hw⟩ := exists_iCycles_apply_eq G L rfl (z : G.obj (L.X i)) hz
  have hiso : IsIso (homologyMap φ i) := (quasiIsoAt_iff_isIso_homologyMap φ i).1 inferInstance
  obtain ⟨t, ht⟩ := ((AddCommGrpCat.epi_iff_surjective (G.map (homologyMap φ i))).1
    inferInstance) (G.map (L.homologyπ i) w)
  obtain ⟨w', rfl⟩ := homologyπ_apply_surjective G K i t
  have he : G.map (L.homologyπ i) (G.map (cyclesMap φ i) w' - w) = 0 := by
    rw [map_sub, map_homologyπ_map_cyclesMap, ht, sub_self]
  obtain ⟨y, hy⟩ := exists_toCycles_apply_eq_of_homologyπ_apply_eq_zero G L rfl _ he
  refine ⟨G.map (K.iCycles i) w', ?_, -y, ?_⟩
  · exact map_d_map_iCycles G K _ _ w'
  · change (z : G.obj (L.X i)) = G.map (φ.f i) (G.map (K.iCycles i) w') +
      G.map (L.d (c.prev i) i) (-y)
    have h2 : G.map (L.d (c.prev i) i) y =
        G.map (L.iCycles i) (G.map (cyclesMap φ i) w') - z := by
      rw [← hw, ← map_sub, ← hy, ← ConcreteCategory.comp_apply, ← G.map_comp, toCycles_i]
    rw [map_neg, h2, ← ConcreteCategory.comp_apply, ← G.map_comp, ← cyclesMap_i, G.map_comp,
      ConcreteCategory.comp_apply]
    abel

/-- **A quasi-isomorphism of complexes of modules is injective on homology, elementwise**: a
cycle of the source whose image is a boundary is a boundary. -/
theorem exists_d_eq_of_quasiIsoAt (i : ι) [QuasiIsoAt φ i] (z' : K.X i)
    (hz' : K.d i (c.next i) z' = 0) (y : L.X (c.prev i)) (hy : φ.f i z' = L.d (c.prev i) i y) :
    ∃ y' : K.X (c.prev i), z' = K.d (c.prev i) i y' := by
  let G := forget₂ (ModuleCat.{v} A) AddCommGrpCat.{v}
  obtain ⟨w, hw⟩ := exists_iCycles_apply_eq G K rfl (z' : G.obj (K.X i)) hz'
  have hiso : IsIso (homologyMap φ i) := (quasiIsoAt_iff_isIso_homologyMap φ i).1 inferInstance
  have h0 : G.map (homologyMap φ i) (G.map (K.homologyπ i) w) = 0 := by
    rw [← map_homologyπ_map_cyclesMap]
    refine (homologyπ_apply_eq_of_iCycles_apply_eq_add G L rfl _ 0 y ?_).trans (map_zero _)
    rw [map_iCycles_map_cyclesMap, hw, map_zero, zero_add]
    exact hy
  have hπ : G.map (K.homologyπ i) w = 0 :=
    (AddCommGrpCat.mono_iff_injective _).1 inferInstance (h0.trans (map_zero _).symm)
  obtain ⟨y', hy'⟩ := exists_toCycles_apply_eq_of_homologyπ_apply_eq_zero G K rfl _ hπ
  refine ⟨y', ?_⟩
  change (z' : G.obj (K.X i)) = G.map (K.d (c.prev i) i) y'
  rw [← hw, ← hy', map_iCycles_map_toCycles]

end HomologicalComplex

end
