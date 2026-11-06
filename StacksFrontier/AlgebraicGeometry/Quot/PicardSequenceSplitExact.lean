module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Quot.PicardBaseClassDies
public import StacksFrontier.AlgebraicGeometry.Quot.PicardKernelGluing
public import StacksFrontier.AlgebraicGeometry.Quot.PicardSequenceSplitting
public import StacksFrontier.AlgebraicGeometry.Quot.SchemesOverCoveringFamily

/-!
# The relative Picard sequence of a morphism with a section is split exact (Stacks 0D28)

Let `f : X ⟶ B` be a morphism of algebraic spaces over a scheme `S`, the standing data of
Stacks 0D25, let `σ : B ⟶ X` be a section of `f`, and assume that `𝒪_T ⟶ f_{T, *}𝒪_{X_T}` is an
isomorphism for every scheme `T` over `B`.  Stacks 0D28 asserts that for every such `T`

`0 ⟶ Pic(T) ⟶ Pic(X_T) ⟶ Pic_{X/B}(T) ⟶ 0`

is a split exact sequence, with splitting `σ_T^* : Pic(X_T) ⟶ Pic(T)`; the first arrow is
pullback along the projection `f_T : X_T ⟶ T`, the second the canonical map to the fppf
sheafification of `T ↦ Pic(X_T)`.  The proof identifies `Pic_{X/B}(T)` with the kernel
`K(T)` of `σ_T^*`.

The sheafified functor `Pic_{X/B}` of Stacks 0D25 is a functor to sets, so exactness at
`Pic(X_T)` is stated as the equality of the fibre of the second arrow over the class of the
trivial module with the image of the first arrow; in fact the second arrow identifies exactly
the classes differing by a class pulled back from `T`.

## Main results

* `AlgebraicGeometry.Space.PicardSituation.eq_zero_of_sectionPicardPullback_eq_zero`: a class in
  `K(T)` which vanishes on an fppf covering of `T` vanishes — the separation of `K`.
* `AlgebraicGeometry.Space.PicardSituation.picardClassMap_eq_iff`: two classes on `X_T` have the
  same image in `Pic_{X/B}(T)` exactly when they differ by a class pulled back from `T`.
* `AlgebraicGeometry.Space.PicardSituation.surjective_picardClassMap`: every element of
  `Pic_{X/B}(T)` is the image of a class on `X_T` — the gluing of `K`.
* `AlgebraicGeometry.Space.PicardSituation.picardSequence_splitExact`: the sequence
  `0 ⟶ Pic(T) ⟶ Pic(X_T) ⟶ Pic_{X/B}(T) ⟶ 0` is split exact.

## References

* [Stacks Project, Tag 0D28](https://stacks.math.columbia.edu/tag/0D28)
* [Stacks Project, Tag 0D25](https://stacks.math.columbia.edu/tag/0D25)
* [Stacks Project, Tag 0D27](https://stacks.math.columbia.edu/tag/0D27)
* [Stacks Project, Tag 04W8](https://stacks.math.columbia.edu/tag/04W8)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

namespace AlgebraicGeometry.Space.PicardSituation

universe u

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {s : PicardSituation B S hS} (σ : s.base ⟶ s.X) (hσ : σ ≫ s.f = 𝟙 s.base)

/-! ### Naturality of the three maps in the test scheme -/

/-- Pullback of Picard classes along a morphism of test schemes is additive. -/
theorem picardMap_add {U T : s.SchemesOver} (g : U ⟶ T) (x y : s.picardAt T) :
    s.picardMap g (x + y) = s.picardMap g x + s.picardMap g y :=
  picardPullback_add _ x y

/-- Pullback of Picard classes along a morphism of test schemes commutes with subtraction. -/
theorem picardMap_sub {U T : s.SchemesOver} (g : U ⟶ T) (x y : s.picardAt T) :
    s.picardMap g (x - y) = s.picardMap g x - s.picardMap g y :=
  map_sub (picardPullbackHom (baseChangeMap s.f g)) x y

/-- The first arrow commutes with restriction along a morphism of test schemes. -/
theorem picardMap_basePicardPullback {U T : s.SchemesOver} (g : U ⟶ T) (y : s.basePicardAt T) :
    s.picardMap g (s.basePicardPullback T y) =
      s.basePicardPullback U (picardPullback (spaceMap g) y) := by
  rw [picardMap_eq, basePicardPullback, basePicardPullback, ← picardPullback_comp,
    baseChangeMap_comp_inclusion, picardPullback_comp]

/-- The splitting commutes with restriction along a morphism of test schemes. -/
theorem sectionPicardPullback_picardMap {U T : s.SchemesOver} (g : U ⟶ T) (x : s.picardAt T) :
    sectionPicardPullback σ hσ U (s.picardMap g x) =
      picardPullback (spaceMap g) (sectionPicardPullback σ hσ T x) := by
  rw [sectionPicardPullback, sectionPicardPullback, picardMap_eq, ← picardPullback_comp,
    ← picardPullback_comp, baseChangeSection_naturality]

/-- The second arrow commutes with restriction along a morphism of test schemes. -/
theorem picardClassMap_picardMap {U T : s.SchemesOver} (g : U ⟶ T) (x : s.picardAt T) :
    s.picardClassMap U (s.picardMap g x) = s.picardFunctor.map g.op (s.picardClassMap T x) :=
  ConcreteCategory.congr_hom (s.toPicardFunctor.naturality g.op) x

/-- The first arrow carries the trivial class to the trivial class. -/
theorem basePicardPullback_zero (T : s.SchemesOver) : s.basePicardPullback T 0 = 0 :=
  picardPullback_zero _

/-- The first arrow commutes with negation. -/
theorem basePicardPullback_neg (T : s.SchemesOver) (y : s.basePicardAt T) :
    s.basePicardPullback T (-y) = -s.basePicardPullback T y :=
  map_neg (picardPullbackHom (baseChangeInclusion s.f T)) y

/-- The splitting carries the trivial class to the trivial class. -/
theorem sectionPicardPullback_zero (T : s.SchemesOver) : sectionPicardPullback σ hσ T 0 = 0 :=
  picardPullback_zero _

/-- The splitting commutes with subtraction. -/
theorem sectionPicardPullback_sub (T : s.SchemesOver) (x y : s.picardAt T) :
    sectionPicardPullback σ hσ T (x - y) =
      sectionPicardPullback σ hσ T x - sectionPicardPullback σ hσ T y :=
  map_sub (picardPullbackHom (baseChangeSection σ hσ T)) x y

/-- The splitting retracts the first arrow. -/
private theorem sectionPicardPullback_basePicardPullback' (T : s.SchemesOver)
    (y : s.basePicardAt T) : sectionPicardPullback σ hσ T (s.basePicardPullback T y) = y :=
  sectionPicardPullback_basePicardPullback (modulePushforwardCoherence B S hS) σ hσ T y

/-- The projection of a class onto the kernel of the splitting along the image of the first
arrow. -/
theorem sectionPicardPullback_sub_basePicardPullback (T : s.SchemesOver) (x : s.picardAt T) :
    sectionPicardPullback σ hσ T
        (x - s.basePicardPullback T (sectionPicardPullback σ hσ T x)) = 0 := by
  rw [sectionPicardPullback_sub, sectionPicardPullback_basePicardPullback', sub_self]

/-! ### The separation of the kernel of the splitting -/

/-- **The separation of `K(T) = ker σ_T^*`.**  Assume `𝒪_U ⟶ f_{U, *}𝒪_{X_U}` is an isomorphism
for every test scheme `U`.  A class on `X_T` killed by `σ_T^*` and by restriction to every member
of an fppf covering sieve of `T` is zero. -/
theorem eq_zero_of_sectionPicardPullback_eq_zero (hstr : s.StructureSheafMapIso)
    {T : s.SchemesOver} (x : s.picardAt T) (hx : sectionPicardPullback σ hσ T x = 0)
    {R : Sieve T} (hR : R ∈ s.fppfTopology T)
    (hloc : ∀ ⦃U : s.SchemesOver⦄ (g : U ⟶ T), R.arrows g → s.picardMap g x = 0) : x = 0 := by
  obtain ⟨I, U, g, hgR, hg, -⟩ :=
    SchemesOver.exists_isFpqcCovering_ofArrows_mem_of_mem_restrictedTopology hR
  obtain ⟨L, hL, rfl⟩ := exists_picardClass (s.baseChange T) x
  obtain ⟨α⟩ := (sectionPicardPullback_picardClass_eq_zero_iff σ hσ T L hL).1 hx
  have hlocL : ∀ i, Nonempty ((modulePullback B S hS (baseChangeMap s.f (g i))).obj L ≅
      structureModule (s.baseChange (U i))) := fun i ↦ by
    have h := hloc (g i) (hgR i)
    rw [picardMap_eq, picardPullback_picardClass] at h
    exact (picardClass_eq_zero_iff _ _ _).1 h
  have hO := isInvertibleModule_structureModule (s.baseChange T)
  obtain ⟨e⟩ := nonempty_iso_of_isFpqcCovering σ hσ hstr g hg hL
    (isQuasicoherentOnSite_of_isInvertibleModule _ _ hO)
    (α ≪≫ (modulePullbackUnitIso B S hS (baseChangeSection σ hσ T)).symm)
    fun i ↦ ⟨(hlocL i).some ≪≫ (modulePullbackUnitIso B S hS (baseChangeMap s.f (g i))).symm⟩
  exact (picardClass_eq_zero_iff _ _ _).2 ⟨e⟩

/-! ### Exactness at `Pic(X_T)` -/

include σ hσ in
/-- **Two classes on `X_T` have the same image in `Pic_{X/B}(T)` exactly when they differ by a
class pulled back from `T`**, when `𝒪_U ⟶ f_{U, *}𝒪_{X_U}` is an isomorphism for every test
scheme `U` and `f` has a section. -/
theorem picardClassMap_eq_iff (hstr : s.StructureSheafMapIso) (T : s.SchemesOver)
    (x y : s.picardAt T) :
    s.picardClassMap T x = s.picardClassMap T y ↔
      x - y ∈ Set.range (s.basePicardPullback T) := by
  constructor
  · intro h
    obtain ⟨R, hR, hxy⟩ := s.exists_forall_of_picardClassMap_eq x y h
    refine ⟨sectionPicardPullback σ hσ T (x - y), ?_⟩
    have hz := eq_zero_of_sectionPicardPullback_eq_zero σ hσ hstr
      ((x - y) - s.basePicardPullback T (sectionPicardPullback σ hσ T (x - y)))
      (sectionPicardPullback_sub_basePicardPullback σ hσ T (x - y)) hR fun U g hg ↦ by
        have hd : s.picardMap g (x - y) = 0 := by rw [picardMap_sub, hxy g hg, sub_self]
        rw [picardMap_sub, hd, picardMap_basePicardPullback, ← sectionPicardPullback_picardMap,
          hd, sectionPicardPullback_zero, basePicardPullback_zero, sub_zero]
    exact (sub_eq_zero.1 hz).symm
  · rintro ⟨n, hn⟩
    have hx : x = y + s.basePicardPullback T n := by rw [hn, add_sub_cancel]
    obtain ⟨R, hR, hR0⟩ := s.exists_mem_fppfTopology_picardPullback_eq_zero T n
    refine s.picardClassMap_eq_of_forall _ _ hR fun U g hg ↦ ?_
    rw [hx, picardMap_add, picardMap_basePicardPullback, hR0 g hg, basePicardPullback_zero,
      add_zero]

/-- Two classes killed by `σ_T^*` with the same image in `Pic_{X/B}(T)` are equal. -/
theorem eq_of_picardClassMap_eq (hstr : s.StructureSheafMapIso) (T : s.SchemesOver)
    {x y : s.picardAt T} (hx : sectionPicardPullback σ hσ T x = 0)
    (hy : sectionPicardPullback σ hσ T y = 0)
    (h : s.picardClassMap T x = s.picardClassMap T y) : x = y := by
  obtain ⟨n, hn⟩ := (picardClassMap_eq_iff σ hσ hstr T x y).1 h
  have hsub := sectionPicardPullback_sub σ hσ T x y
  rw [← hn, sectionPicardPullback_basePicardPullback', hx, hy, sub_self] at hsub
  rw [← sub_eq_zero, ← hn, hsub, basePicardPullback_zero]

/-- The difference of a class and its projection to the kernel of the splitting is pulled back
from the test scheme. -/
theorem sub_projection_mem_range (T : s.SchemesOver) (x : s.picardAt T) :
    (x - s.basePicardPullback T (sectionPicardPullback σ hσ T x)) - x ∈
      Set.range (s.basePicardPullback T) :=
  ⟨-sectionPicardPullback σ hσ T x, by rw [basePicardPullback_neg]; abel⟩

/-! ### Surjectivity onto `Pic_{X/B}(T)` -/

include σ hσ in
/-- **Every element of `Pic_{X/B}(T)` is the image of a Picard class on `X_T`**, when
`𝒪_U ⟶ f_{U, *}𝒪_{X_U}` is an isomorphism for every test scheme `U` and `f` has a section. -/
theorem surjective_picardClassMap (hstr : s.StructureSheafMapIso) (T : s.SchemesOver) :
    Function.Surjective (s.picardClassMap T) := by
  classical
  intro z
  have hW := GrothendieckTopology.W_toSheafify s.fppfTopology s.picardPresheaf
  have hls := GrothendieckTopology.W.isLocallySurjective (A := Type (u + 1)) hW
  have hmem := Presheaf.imageSieve_mem s.fppfTopology
    (toSheafify s.fppfTopology s.picardPresheaf) (U := op T) z
  obtain ⟨I, U, g, hgR, hg, hof⟩ :=
    SchemesOver.exists_isFpqcCovering_ofArrows_mem_of_mem_restrictedTopology hmem
  have hpre : ∀ i, ∃ t : s.picardAt (U i), s.picardClassMap (U i) t =
      s.picardFunctor.map (g i).op z := fun i ↦ hgR i
  choose t ht using hpre
  let k : ∀ i, s.picardAt (U i) := fun i ↦
    t i - s.basePicardPullback (U i) (sectionPicardPullback σ hσ (U i) (t i))
  have hk0 : ∀ i, sectionPicardPullback σ hσ (U i) (k i) = 0 :=
    fun i ↦ sectionPicardPullback_sub_basePicardPullback σ hσ (U i) (t i)
  have hkz : ∀ i, s.picardClassMap (U i) (k i) = s.picardFunctor.map (g i).op z := fun i ↦
    ((picardClassMap_eq_iff σ hσ hstr (U i) (k i) (t i)).2
      (sub_projection_mem_range σ hσ (U i) (t i))).trans (ht i)
  choose L hL hLk using fun i ↦ exists_picardClass (s.baseChange (U i)) (k i)
  have hα : ∀ i, Nonempty ((modulePullback B S hS (baseChangeSection σ hσ (U i))).obj (L i) ≅
      (modulePullback B S hS (spaceMap (g i) ≫ baseChangeSection σ hσ T)).obj
        (structureModule (s.baseChange T))) := fun i ↦ by
    obtain ⟨α⟩ := (sectionPicardPullback_picardClass_eq_zero_iff σ hσ (U i) (L i) (hL i)).1
      (by rw [hLk i]; exact hk0 i)
    exact ⟨α ≪≫ (modulePullbackUnitIso B S hS _).symm⟩
  have hcomp : ∀ (i j : I) {V : s.SchemesOver} (a : V ⟶ U i) (b : V ⟶ U j), a ≫ g i = b ≫ g j →
      Nonempty ((modulePullback B S hS (baseChangeMap s.f a)).obj (L i) ≅
        (modulePullback B S hS (baseChangeMap s.f b)).obj (L j)) := by
    intro i j V a b hab
    have hka : s.picardMap a (k i) = s.picardMap b (k j) := by
      refine eq_of_picardClassMap_eq σ hσ hstr V ?_ ?_ ?_
      · rw [sectionPicardPullback_picardMap, hk0 i, picardPullback_zero]
      · rw [sectionPicardPullback_picardMap, hk0 j, picardPullback_zero]
      · rw [picardClassMap_picardMap, picardClassMap_picardMap, hkz i, hkz j,
          ← Functor.map_comp_apply, ← Functor.map_comp_apply, ← op_comp,
          ← op_comp, hab]
    rw [← hLk i, ← hLk j, picardMap_eq, picardMap_eq, picardPullback_picardClass,
      picardPullback_picardClass] at hka
    exact (picardClass_eq_picardClass_iff _ _ _ _ _).1 hka
  obtain ⟨M, hM, hML⟩ := exists_isInvertibleModule_glue σ hσ hstr g hg
    (structureModule (s.baseChange T)) L hL (fun i ↦ (hα i).some) hcomp
  refine ⟨picardClass _ M hM, ?_⟩
  have hsep := ((isSheaf_iff_isSheaf_of_type _ _).1 s.isSheaf_picardFunctor _ hof).isSeparatedFor
  refine hsep.ext fun V f hf ↦ ?_
  obtain ⟨i, a, rfl⟩ := (Sieve.mem_ofArrows_iff U g f).1 hf
  have hi : s.picardMap (g i) (picardClass _ M hM) = k i := by
    rw [picardMap_eq, picardPullback_picardClass, ← hLk i]
    exact (picardClass_eq_picardClass_iff _ _ _ _ _).2 ⟨(hML i).some.symm⟩
  rw [op_comp, Functor.map_comp_apply, Functor.map_comp_apply,
    ← picardClassMap_picardMap, hi, hkz i]

/-! ### Stacks 0D28 -/

/-- In Situation 0D25 let `σ : B ⟶ X` be a section of `f`, and assume that
`𝒪_T ⟶ f_{T, *}𝒪_{X_T}` is an isomorphism for every scheme `T` over `B`.  Then for every `T`

`0 ⟶ Pic(T) ⟶ Pic(X_T) ⟶ Pic_{X/B}(T) ⟶ 0`

is a split exact sequence with splitting `σ_T^* : Pic(X_T) ⟶ Pic(T)`, the first arrow being
pullback along `f_T : X_T ⟶ T` and the second the canonical map to the fppf sheafification
`Pic_{X/B}`.  Spelled out:

* the first arrow is injective;
* two classes on `X_T` have the same image in `Pic_{X/B}(T)` exactly when they differ by a class
  pulled back from `T`, and in particular (exactness at `Pic(X_T)`) a class maps to the image of
  the trivial class exactly when it is pulled back from `T`;
* the second arrow is surjective;
* `σ_T^*` is a left inverse of the first arrow;
* the second arrow restricts to a bijection from the kernel of `σ_T^*` onto `Pic_{X/B}(T)`, the
  identification `Pic_{X/B}(T) = ker(σ_T^*)` of the proof. -/
@[stacks 0D28]
theorem picardSequence_splitExact (hstr : s.StructureSheafMapIso) (T : s.SchemesOver) :
    Function.Injective (s.basePicardPullback T) ∧
      (∀ x y : s.picardAt T, s.picardClassMap T x = s.picardClassMap T y ↔
        x - y ∈ Set.range (s.basePicardPullback T)) ∧
      (∀ x : s.picardAt T, s.picardClassMap T x = s.picardClassMap T 0 ↔
        x ∈ Set.range (s.basePicardPullback T)) ∧
      Function.Surjective (s.picardClassMap T) ∧
      Function.LeftInverse (sectionPicardPullback σ hσ T) (s.basePicardPullback T) ∧
      Function.Bijective (fun x : (sectionPicardPullbackHom σ hσ T).ker ↦
        s.picardClassMap T (x : s.picardAt T)) := by
  have hleft : Function.LeftInverse (sectionPicardPullback σ hσ T) (s.basePicardPullback T) :=
    sectionPicardPullback_basePicardPullback' σ hσ T
  refine ⟨hleft.injective, picardClassMap_eq_iff σ hσ hstr T, fun x ↦ ?_,
    surjective_picardClassMap σ hσ hstr T, hleft, ⟨fun x y h ↦ ?_, fun z ↦ ?_⟩⟩
  · rw [picardClassMap_eq_iff σ hσ hstr T, sub_zero]
  · exact Subtype.ext (eq_of_picardClassMap_eq σ hσ hstr T x.2 y.2 h)
  · obtain ⟨x, rfl⟩ := surjective_picardClassMap σ hσ hstr T z
    exact ⟨⟨x - s.basePicardPullback T (sectionPicardPullback σ hσ T x),
      sectionPicardPullback_sub_basePicardPullback σ hσ T x⟩,
      (picardClassMap_eq_iff σ hσ hstr T _ x).2 (sub_projection_mem_range σ hσ T x)⟩

end AlgebraicGeometry.Space.PicardSituation

end
