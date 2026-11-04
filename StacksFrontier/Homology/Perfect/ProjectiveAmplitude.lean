module

public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Homology.DerivedCategory.KProjective
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.Algebra.Module.Projective
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLEGT
public import StacksFrontier.Algebra.Homology.DerivedCategory.Ext.Basic
public import StacksFrontier.Algebra.Homology.ProjectiveDimension.Criteria
public import StacksFrontier.Homology.HomologyColimit
public import StacksFrontier.Homology.Perfect.Basic
public import StacksFrontier.Homology.Perfect.FibreCriterion
public import StacksFrontier.Homology.PseudoCoherent.Characterization
public import StacksFrontier.Homology.PseudoCoherent.Ext
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Colimit.Module
import Mathlib.Algebra.Module.Shrink
import Mathlib.LinearAlgebra.Finsupp.Supported
import Mathlib.Algebra.Category.Grp.Ulift
import Mathlib.Algebra.Category.Grp.Zero
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Category.ModuleCat.EnoughInjectives
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexSingle
import Mathlib.Algebra.Homology.ShortComplex.FunctorEquivalence
import Mathlib.CategoryTheory.Triangulated.Yoneda
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedFunctorsOnDerivedCategories

@[expose] public section

/-!
# Projective amplitude in the derived category of a ring

Let `R` be a ring and let `D(R)` be the derived category of `R`-modules. An object of `D(R)` has
*projective amplitude in `[a, b]`* when it is represented by a complex of projective `R`-modules
whose terms vanish outside the degrees `a, …, b`. This module records the consequences of
projective amplitude for morphisms out of such an object, the splittings of a bounded above object
into two canonical truncations that Ext vanishing in a single degree produces, and the recognition
of perfect objects of bounded Tor amplitude among pseudo-coherent objects.

## Main definitions

* `StacksDraft.ProjectiveAmplitude.HasProjectiveAmplitude`: projective amplitude in `[a, b]`.

## Main results

* `StacksDraft.ProjectiveAmplitude.hom_eq_zero_and_existsUnique_iso_biprod` ([stacks 0BCG]):
  morphisms out of an object of projective amplitude in `[a, b]` into an object with cohomology
  vanishing from `a` on are zero, and the associated distinguished triangles split, uniquely
  under the stronger vanishing hypothesis.
* `StacksDraft.ProjectiveAmplitude.existsUnique_iso_biprod_truncations_of_ext_map_injective`
  ([stacks 0G97]): a bounded above object whose `Ext^{-a}` preserves injectivity of module maps
  splits uniquely as `τ_{≤ a}K ⊞ τ_{≥ a + 1}K`, the second factor having projective amplitude in
  `[a + 1, b]` for some `b`.
* `StacksDraft.ProjectiveAmplitude.existsUnique_iso_biprod_truncations_of_ext_vanishing`
  ([stacks 0G98]): the same statement with `τ_{≤ a - 1}K` in place of `τ_{≤ a}K`, under the
  stronger hypothesis that `Ext^{-a}(K, M)` vanishes for every module `M`.
* `StacksDraft.ProjectiveAmplitude.hasProjectiveAmplitude_iff_perfect_iff_ext_vanishing`
  ([stacks 0G9A]): for a pseudo-coherent object, projective amplitude in `[a, b]`, perfectness
  with Tor amplitude in `[a, b]`, and three Ext and cohomology vanishing criteria tested on
  finitely presented modules are all equivalent.

## Implementation notes

A representative of an object of `D(R)` is recorded by an isomorphism from the image of a cochain
complex under the localization functor `DerivedCategory.Q`; since `Iso` is data rather than a
proposition, the existential records `Nonempty` of it. Support in `[a, b]` is expressed by the
strict bounds `CochainComplex.IsStrictlyGE` and `CochainComplex.IsStrictlyLE`. Tor amplitude in
`[a, b]` is recorded by `StacksDraft.Perfect.HasFlatRepresentative`, which by [stacks 0654] is
precisely Tor amplitude and, unlike the derived-tensor formulation, makes sense when the carrier
universe of the modules is independent of the universe of the ring. Vanishing of an Ext group is
expressed by its underlying type being a subsingleton, and a module is placed in degree zero
before being fed to Ext.

Two auxiliary developments are carried out here as private lemmas, because the tagged results above
rest on them:

* the Ext characterization of projective amplitude, [stacks 0A5P], as
  `hasProjectiveAmplitude_iff_ext_vanishing`;
* the compatibility of Ext out of a pseudo-coherent object with filtered colimits,
  [stacks 0G8W], as `colimit_ext_comparison_isIso_of_lt_and_mono`, together with the presenting
  system realizing an arbitrary module as a filtered colimit of finitely presented modules.

`HasProjectiveAmplitude` is the definition of [stacks 0A5N]; it is stated here at source strength
but deliberately left untagged, since that tag is not realized by this module.

## References

* [Stacks Project, Tag 0A5N](https://stacks.math.columbia.edu/tag/0A5N)
* [Stacks Project, Tag 0A5P](https://stacks.math.columbia.edu/tag/0A5P)
* [Stacks Project, Tag 0BCG](https://stacks.math.columbia.edu/tag/0BCG)
* [Stacks Project, Tag 0G8W](https://stacks.math.columbia.edu/tag/0G8W)
* [Stacks Project, Tag 0G97](https://stacks.math.columbia.edu/tag/0G97)
* [Stacks Project, Tag 0G98](https://stacks.math.columbia.edu/tag/0G98)
* [Stacks Project, Tag 0G9A](https://stacks.math.columbia.edu/tag/0G9A)
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

open Stacks.HomologyColimit

namespace StacksDraft.ProjectiveAmplitude

universe w v u

/-- An object of `D(R)` has **projective amplitude in `[a, b]`** if it is represented by a
complex of projective `R`-modules whose terms vanish outside the degrees `a, …, b`. -/
def HasProjectiveAmplitude {R : Type u} [Ring R]
    [HasDerivedCategory.{w} (ModuleCat.{v} R)]
    (K : DerivedCategory (ModuleCat.{v} R)) (a b : ℤ) : Prop :=
  ∃ P : CochainComplex (ModuleCat.{v} R) ℤ,
    Nonempty (DerivedCategory.Q.obj P ≅ K) ∧
      (∀ i : ℤ, Module.Projective R (P.X i)) ∧
      P.IsStrictlyGE a ∧ P.IsStrictlyLE b

section BiproductSplitting

attribute [local instance] HasDerivedCategory.standard

/-- A morphism from an object of projective amplitude in `[a, b]` to an object concentrated in
degrees `≤ a - 1` vanishes: a projective representative supported in `[a, b]` is K-projective, so
the morphism is represented by an actual map of complexes, and that map is zero in every degree
for lack of a common degree. -/
private lemma hom_eq_zero_of_hasProjectiveAmplitude_of_isLE
    {R : Type u} [Ring R] (K L : DerivedCategory (ModuleCat.{v} R)) (a b : ℤ)
    (hL : HasProjectiveAmplitude L a b) [K.IsLE (a - 1)] :
    ∀ f : L ⟶ K, f = 0 := by
  rintro f
  obtain ⟨P, ⟨eP⟩, hPproj, hPge, hPle⟩ := hL
  obtain ⟨X, hXle, ⟨eX⟩⟩ := K.exists_iso_Q_obj_of_isLE (a - 1)
  let (i : ℤ) : Module.Projective R (P.X i) := hPproj i
  let : P.IsStrictlyGE a := hPge
  let : P.IsStrictlyLE b := hPle
  let : X.IsStrictlyLE (a - 1) := hXle
  let : P.IsKProjective := CochainComplex.isKProjective_of_projective P b
  let qf := (DerivedCategory.quotientCompQhIso (ModuleCat.{v} R)).hom.app P ≫
    eP.hom ≫ f ≫ eX.hom ≫
      (DerivedCategory.quotientCompQhIso (ModuleCat.{v} R)).inv.app X
  obtain ⟨q, hq⟩ :=
    (CochainComplex.IsKProjective.Qh_map_bijective P
      ((HomotopyCategory.quotient (ModuleCat.{v} R) (ComplexShape.up ℤ)).obj X)).surjective qf
  obtain ⟨φ, rfl⟩ :=
    (HomotopyCategory.quotient (ModuleCat.{v} R) (ComplexShape.up ℤ)).map_surjective q
  have hφ : φ = 0 := by
    apply HomologicalComplex.Hom.ext
    funext i
    by_cases hi : a ≤ i
    · apply (X.isZero_of_isStrictlyLE (a - 1) i (by omega)).eq_of_tgt
    · apply (P.isZero_of_isStrictlyGE a i (by omega)).eq_of_src
  subst φ
  dsimp [qf] at hq
  simp only [Functor.map_zero] at hq
  have hq' := congrArg (fun z ↦
    (DerivedCategory.quotientCompQhIso (ModuleCat.{v} R)).inv.app P ≫ z ≫
      (DerivedCategory.quotientCompQhIso (ModuleCat.{v} R)).hom.app X) hq
  have hf' : eP.hom ≫ f ≫ eX.hom = 0 := by simpa using hq'.symm
  rw [← cancel_epi eP.hom, ← cancel_mono eX.hom]
  simpa only [Category.assoc, comp_zero, zero_comp] using hf'

/-- Vanishing of cohomology in all degrees `≥ a` is membership in the part of the canonical
t-structure concentrated in degrees `≤ a - 1`. -/
private lemma isLE_of_vanishing
    {R : Type u} [Ring R] (K : DerivedCategory (ModuleCat.{v} R)) (a : ℤ)
    (hK : ∀ i : ℤ, a ≤ i →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).obj K)) :
    K.IsLE (a - 1) := by
  rw [DerivedCategory.isLE_iff]
  intro i hi
  exact hK i (by omega)

/-- **Stacks 0BCG.** If `L` has projective amplitude in `[a, b]`, then every morphism from `L` to
an object whose cohomology vanishes in all degrees `≥ a` is zero. A distinguished triangle
`K ⟶ M ⟶ L ⟶ K⟦1⟧` has a splitting `M ≅ K ⊞ L` compatible with its maps as soon as the
cohomology of `K` vanishes in all degrees `≥ a + 1`; if it vanishes in all degrees `≥ a`, that
compatible splitting is moreover unique. -/
@[stacks 0BCG]
theorem hom_eq_zero_and_existsUnique_iso_biprod
    {R : Type u} [Ring R] (K L : DerivedCategory (ModuleCat.{v} R)) (a b : ℤ)
    (hL : HasProjectiveAmplitude L a b) :
    ((∀ i : ℤ, a ≤ i → IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).obj K)) →
        ∀ f : L ⟶ K, f = 0) ∧
      ((∀ i : ℤ, a + 1 ≤ i →
          IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).obj K)) →
        ∀ (M : DerivedCategory (ModuleCat.{v} R)) (f : K ⟶ M) (g : M ⟶ L)
          (h : L ⟶ K⟦(1 : ℤ)⟧),
          Triangle.mk f g h ∈ distTriang _ →
            ∃ e : M ≅ K ⊞ L, f ≫ e.hom = biprod.inl ∧ g = e.hom ≫ biprod.snd) ∧
      ((∀ i : ℤ, a ≤ i → IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).obj K)) →
        ∀ (M : DerivedCategory (ModuleCat.{v} R)) (f : K ⟶ M) (g : M ⟶ L)
          (h : L ⟶ K⟦(1 : ℤ)⟧),
          Triangle.mk f g h ∈ distTriang _ →
            ∃! e : M ≅ K ⊞ L, f ≫ e.hom = biprod.inl ∧ g = e.hom ≫ biprod.snd) := by
  have vanish (K' : DerivedCategory (ModuleCat.{v} R)) [K'.IsLE (a - 1)] :
      ∀ q : L ⟶ K', q = 0 :=
    hom_eq_zero_of_hasProjectiveAmplitude_of_isLE K' L a b hL
  have split [K.IsLE a] (M : DerivedCategory (ModuleCat.{v} R)) (f : K ⟶ M) (g : M ⟶ L)
      (h : L ⟶ K⟦(1 : ℤ)⟧) (hT : Triangle.mk f g h ∈ distTriang _) :
      ∃ e : M ≅ K ⊞ L, f ≫ e.hom = biprod.inl ∧ g = e.hom ≫ biprod.snd := by
    have : (K⟦(1 : ℤ)⟧).IsLE (a - 1) :=
      DerivedCategory.TStructure.t.isLE_shift K a 1 (a - 1) (by omega)
    exact exists_iso_binaryBiproduct_of_distTriang (Triangle.mk f g h) hT (vanish _ h)
  refine ⟨fun hK ↦ @vanish K (isLE_of_vanishing K a hK), ?_, ?_⟩
  · intro hK M f g h hT
    have : K.IsLE a := by simpa using isLE_of_vanishing K (a + 1) hK
    exact split M f g h hT
  · intro hK M f g h hT
    have : K.IsLE (a - 1) := isLE_of_vanishing K a hK
    have : K.IsLE a := DerivedCategory.TStructure.t.isLE_of_le K (a - 1) a (by omega)
    obtain ⟨e, he⟩ := split M f g h hT
    exact ⟨e, he, fun e' he' ↦
      StacksDraft.Perfect.compatible_iso_unique K M L f g h hT (vanish K) e' e he' he⟩

end BiproductSplitting

/-!
### Detecting projective amplitude by Ext vanishing

The results of this section are [stacks 0A5P]. They are proved here as private lemmas because
the splitting lemmas below rest on them; see the module documentation.
-/

section ExtVanishing

variable {R : Type u} [Ring R] [HasDerivedCategory.{w} (ModuleCat.{v} R)]

open StacksDraft.ProjectiveDimension (ext_vanishes_of_hasProjectiveAmplitude
  upperVanishing_of_extOutsideVanishes extOutsideVanishes_of_upperVanishing
  endpointVanishing_of_upperVanishing homologyVanishing_of_endpointVanishing
  hasProjectiveAmplitude_of_endpointVanishing)

/-- **[stacks 0A5P].** Projective amplitude in `[a, b]` is equivalent to the vanishing of all Ext
groups outside the degrees `[-b, -a]`; equivalently it is detected by upper cohomology vanishing
together with the Ext groups above degree `-a`, or by cohomology vanishing outside `[a - 1, b]`
together with the single Ext degree `-a + 1`. -/
private theorem hasProjectiveAmplitude_iff_ext_vanishing [Small.{v} R]
    (K : DerivedCategory (ModuleCat.{v} R)) (a b : ℤ) :
    (HasProjectiveAmplitude K a b ↔
        ∀ (N : ModuleCat.{v} R) (i : ℤ), i ∉ Set.Icc (-b) (-a) →
          Subsingleton (DerivedCategory.Ext K
            ((DerivedCategory.singleFunctor (ModuleCat.{v} R) 0).obj N) i)) ∧
      ((∀ (N : ModuleCat.{v} R) (i : ℤ), i ∉ Set.Icc (-b) (-a) →
          Subsingleton (DerivedCategory.Ext K
            ((DerivedCategory.singleFunctor (ModuleCat.{v} R) 0).obj N) i)) ↔
        (∀ n : ℤ, b < n →
            IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) n).obj K)) ∧
          ∀ (N : ModuleCat.{v} R) (i : ℤ), -a < i →
            Subsingleton (DerivedCategory.Ext K
              ((DerivedCategory.singleFunctor (ModuleCat.{v} R) 0).obj N) i)) ∧
      (((∀ n : ℤ, b < n →
            IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) n).obj K)) ∧
          ∀ (N : ModuleCat.{v} R) (i : ℤ), -a < i →
            Subsingleton (DerivedCategory.Ext K
              ((DerivedCategory.singleFunctor (ModuleCat.{v} R) 0).obj N) i)) ↔
        (∀ n : ℤ, n ∉ Set.Icc (a - 1) b →
            IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) n).obj K)) ∧
          ∀ N : ModuleCat.{v} R,
            Subsingleton (DerivedCategory.Ext K
              ((DerivedCategory.singleFunctor (ModuleCat.{v} R) 0).obj N) (-a + 1))) := by
  have hproj (hend : (∀ n : ℤ, n ∉ Set.Icc (a - 1) b →
            IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) n).obj K)) ∧
          ∀ N : ModuleCat.{v} R,
            Subsingleton (DerivedCategory.Ext K
              ((DerivedCategory.singleFunctor (ModuleCat.{v} R) 0).obj N) (-a + 1))) :
      HasProjectiveAmplitude K a b :=
    hasProjectiveAmplitude_of_endpointVanishing K a b
      (homologyVanishing_of_endpointVanishing K a b hend) hend.2
  refine ⟨⟨fun h N i hi =>
      ext_vanishes_of_hasProjectiveAmplitude (K := K) (a := a) (b := b) h N i hi, fun h => ?_⟩,
    ⟨upperVanishing_of_extOutsideVanishes K a b, extOutsideVanishes_of_upperVanishing K a b⟩,
    ⟨endpointVanishing_of_upperVanishing K a b, fun hend => ?_⟩⟩
  · exact hproj (endpointVanishing_of_upperVanishing K a b
      (upperVanishing_of_extOutsideVanishes K a b h))
  · exact upperVanishing_of_extOutsideVanishes K a b
      fun N i hi => ext_vanishes_of_hasProjectiveAmplitude (hproj hend) N i hi

end ExtVanishing

/-! ### Splitting off a truncation -/

section Splitting

attribute [local instance] HasDerivedCategory.standard

/-- **Stacks 0G97.** Let `K` be a bounded above object of `D(R)` and let `a` be an integer.
Assume that for every injective `R`-module map `M ⟶ M'` the induced map
`Ext^{-a}(K, M) ⟶ Ext^{-a}(K, M')` is injective. Then `τ_{≥ a + 1}K` has projective amplitude in
`[a + 1, b]` for some `b`, and there is a *unique* direct sum decomposition
`K ≅ τ_{≤ a}K ⊞ τ_{≥ a + 1}K` compatible with the two canonical truncation maps. -/
@[stacks 0G97]
theorem existsUnique_iso_biprod_truncations_of_ext_map_injective
    {R : Type u} [Ring R] (K : DerivedCategory (ModuleCat.{max u v} R)) (a : ℤ)
    (hK : ∃ n : ℤ, K.IsLE n)
    (hExt : ∀ (M M' : ModuleCat.{max u v} R) (f : M ⟶ M'), Mono f →
      Function.Injective (fun x : DerivedCategory.Ext K
          ((DerivedCategory.singleFunctor (ModuleCat.{max u v} R) 0).obj M) (-a) ↦
        x.comp (ShiftedHom.mk₀ 0 rfl
          ((DerivedCategory.singleFunctor (ModuleCat.{max u v} R) 0).map f)) (zero_add _))) :
    ∃ b : ℤ,
      HasProjectiveAmplitude
          ((DerivedCategory.TStructure.t.truncGE (a + 1)).obj K) (a + 1) b ∧
        ∃! e : K ≅
            ((DerivedCategory.TStructure.t.truncLE a).obj K ⊞
              (DerivedCategory.TStructure.t.truncGE (a + 1)).obj K),
          (DerivedCategory.TStructure.t.truncLEι a).app K ≫ e.hom = biprod.inl ∧
            (DerivedCategory.TStructure.t.truncGEπ (a + 1)).app K =
              e.hom ≫ biprod.snd := by
  have : Small.{max u v} R := small_max R
  let t := DerivedCategory.TStructure.t (C := ModuleCat.{max u v} R)
  let L := (t.truncGE (a + 1)).obj K
  obtain ⟨n, hKn⟩ := hK
  let b := max n (a + 1)
  have hKb : K.IsLE b := by
    let : K.IsLE n := hKn
    exact t.isLE_of_le K n b (show n ≤ max n (a + 1) from le_max_left _ _)
  have hLb : L.IsLE b := by
    dsimp [L, t]
    let : K.IsLE b := hKb
    infer_instance
  have hExtL : ∀ M : ModuleCat.{max u v} R,
      Subsingleton (DerivedCategory.Ext L
        ((DerivedCategory.singleFunctor (ModuleCat.{max u v} R) 0).obj M) (-a)) := by
    intro M
    refine subsingleton_of_forall_eq 0 ?_
    intro x
    let I := Injective.under M
    let f : M ⟶ I := Injective.ι M
    have hxI : x.comp (ShiftedHom.mk₀ 0 rfl
        ((DerivedCategory.singleFunctor (ModuleCat.{max u v} R) 0).map f)) (zero_add _) = 0 := by
      obtain ⟨P, hP, ⟨e⟩⟩ := DerivedCategory.exists_iso_Q_obj_of_isGE L (a + 1)
      let eI :
          ((shiftFunctor (DerivedCategory (ModuleCat.{max u v} R)) (-a)).obj
              ((DerivedCategory.singleFunctor (ModuleCat.{max u v} R) 0).obj I)) ≅
            DerivedCategory.Q.obj
              ((CochainComplex.singleFunctor (ModuleCat.{max u v} R) a).obj I) :=
        ((DerivedCategory.singleFunctors (ModuleCat.{max u v} R)).shiftIso
            (-a) a 0 (by omega)).app I ≪≫
          (DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{max u v} R) a).app I
      apply (cancel_epi e.inv).1
      apply (cancel_mono eI.hom).1
      simpa [Category.assoc] using
        (DerivedCategory.to_singleFunctor_obj_eq_zero_of_injective
          (I := I) (K := P) (i := a) (n := a + 1)
          (e.inv ≫ (x.comp (ShiftedHom.mk₀ 0 rfl
            ((DerivedCategory.singleFunctor (ModuleCat.{max u v} R) 0).map f))
              (zero_add _)) ≫ eI.hom) (by omega))
    have hxK : (t.truncGEπ (a + 1)).app K ≫ x = 0 := by
      apply hExt M I f inferInstance
      simpa [ShiftedHom.comp, Category.assoc] using
        congrArg (fun z => (t.truncGEπ (a + 1)).app K ≫ z) hxI
    let T := (t.triangleLEGE a (a + 1) rfl).obj K
    obtain ⟨y, hy⟩ := T.yoneda_exact₃ (t.triangleLEGE_distinguished a (a + 1) rfl K) x hxK
    rw [hy]
    rw [t.zero_of_isLE_of_isGE y (a - 1) a (by omega)
      (t.isLE_shift ((t.truncLE a).obj K) a 1 (a - 1) (by omega))
      (t.isGE_shift _ 0 (-a) a (by omega))]
    exact comp_zero
  have hAmp : HasProjectiveAmplitude L (a + 1) b := by
    let : L.IsLE b := hLb
    apply (hasProjectiveAmplitude_iff_ext_vanishing L (a + 1) b).1.mpr
    apply (hasProjectiveAmplitude_iff_ext_vanishing L (a + 1) b).2.1.mpr
    apply (hasProjectiveAmplitude_iff_ext_vanishing L (a + 1) b).2.2.mpr
    constructor
    · intro m hm
      by_cases hm' : a + 1 ≤ m
      · exact DerivedCategory.isZero_of_isLE L b m (by
          have hab : a + 1 ≤ b := le_max_right _ _
          simp only [Set.mem_Icc, not_and_or] at hm
          omega)
      · exact DerivedCategory.isZero_of_isGE L (a + 1) m (by omega)
    · intro M
      simpa using hExtL M
  refine ⟨b, hAmp, ?_⟩
  exact (hom_eq_zero_and_existsUnique_iso_biprod
    ((t.truncLE a).obj K) L (a + 1) b hAmp).2.2
    (fun i hi => DerivedCategory.isZero_of_isLE _ a i (by omega)) K
    ((t.truncLEι a).app K) ((t.truncGEπ (a + 1)).app K)
    ((t.truncGEδLE a (a + 1) rfl).app K)
    (t.triangleLEGE_distinguished a (a + 1) rfl K)

/-- Transporting a compatible splitting `K ≅ A ⊞ U` along an isomorphism `ε : A ≅ B` with
`ι_A = ε ≫ ι_B` gives a compatible splitting `K ≅ B ⊞ U`. -/
private lemma compatible_biprod_mapIso {C : Type*} [Category C] [Preadditive C]
    [HasBinaryBiproducts C] {K A B U : C} (ε : A ≅ B) (ιA : A ⟶ K) (ιB : B ⟶ K) (π : K ⟶ U)
    (hι : ιA = ε.hom ≫ ιB) (e : K ≅ A ⊞ U)
    (he : ιA ≫ e.hom = biprod.inl ∧ π = e.hom ≫ biprod.snd) :
    ιB ≫ (e ≪≫ biprod.mapIso ε (Iso.refl U)).hom = biprod.inl ∧
      π = (e ≪≫ biprod.mapIso ε (Iso.refl U)).hom ≫ biprod.snd := by
  refine ⟨?_, by simpa using he.2⟩
  have h : ιB = ε.inv ≫ ιA := by simp [hι]
  simp [h, reassoc_of% he.1]

/-- **Stacks 0G98.** Let `K` be a bounded above object of `D(R)` and let `a` be an integer.
Assume `Ext^{-a}(K, M) = 0` for every `R`-module `M`. Then `τ_{≥ a + 1}K` has projective
amplitude in `[a + 1, b]` for some `b`, and there is a *unique* direct sum decomposition
`K ≅ τ_{≤ a - 1}K ⊞ τ_{≥ a + 1}K` compatible with the two canonical truncation maps. -/
@[stacks 0G98]
theorem existsUnique_iso_biprod_truncations_of_ext_vanishing
    {R : Type u} [Ring R] (K : DerivedCategory (ModuleCat.{max u v} R)) (a : ℤ)
    (hK : ∃ n : ℤ, K.IsLE n)
    (hExt : ∀ M : ModuleCat.{max u v} R,
      Subsingleton (DerivedCategory.Ext K
        ((DerivedCategory.singleFunctor (ModuleCat.{max u v} R) 0).obj M) (-a))) :
    ∃ b : ℤ,
      HasProjectiveAmplitude
          ((DerivedCategory.TStructure.t.truncGE (a + 1)).obj K) (a + 1) b ∧
        ∃! e : K ≅
            ((DerivedCategory.TStructure.t.truncLE (a - 1)).obj K ⊞
              (DerivedCategory.TStructure.t.truncGE (a + 1)).obj K),
          (DerivedCategory.TStructure.t.truncLEι (a - 1)).app K ≫ e.hom = biprod.inl ∧
            (DerivedCategory.TStructure.t.truncGEπ (a + 1)).app K =
              e.hom ≫ biprod.snd := by
  let t := DerivedCategory.TStructure.t (C := ModuleCat.{max u v} R)
  obtain ⟨b, hb, e, he, he_unique⟩ :=
    existsUnique_iso_biprod_truncations_of_ext_map_injective K a hK
      (fun M M' f _ ↦ fun x y _ ↦ (hExt M).allEq x y)
  let L := (t.truncLE a).obj K
  let U := (t.truncGE (a + 1)).obj K
  have hExtL (M : ModuleCat.{max u v} R) :
      Subsingleton (DerivedCategory.Ext L
        ((DerivedCategory.singleFunctor (ModuleCat.{max u v} R) 0).obj M) (-a)) := by
    constructor
    intro x y
    have hxy : (e.hom ≫ biprod.fst) ≫ x = (e.hom ≫ biprod.fst) ≫ y :=
      (hExt M).allEq _ _
    simpa [Category.assoc] using
      congrArg (fun q ↦ (biprod.inl ≫ e.inv) ≫ q) hxy
  have hHa : IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} R) a).obj L) := by
    let M := (DerivedCategory.homologyFunctor (ModuleCat.{max u v} R) a).obj L
    let Y := (DerivedCategory.singleFunctor (ModuleCat.{max u v} R) 0).obj M
    have hbij := DerivedCategory.bijective_homologyFunctor_shiftMap_of_isLE_of_isGE
      L Y a 0 (-a) 0 (by omega) (by omega)
    have hs : Subsingleton
        ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} R) a).obj L ⟶
          (DerivedCategory.homologyFunctor (ModuleCat.{max u v} R) 0).obj Y) :=
      ⟨fun f g ↦ by
        obtain ⟨x, rfl⟩ := hbij.2 f
        obtain ⟨y, rfl⟩ := hbij.2 g
        rw [(hExtL M).allEq x y]⟩
    change Subsingleton (M ⟶
      (DerivedCategory.homologyFunctor (ModuleCat.{max u v} R) 0).obj Y) at hs
    let q := (DerivedCategory.singleFunctorCompHomologyFunctorIso
      (ModuleCat.{max u v} R) 0).hom.app M
    refine (IsZero.iff_id_eq_zero _).2 ?_
    show 𝟙 M = 0
    simpa [q] using congrArg (fun f ↦ f ≫ q) (hs.allEq (inv q) 0)
  have hL : t.IsLE L (a - 1) := by
    show L.IsLE (a - 1)
    rw [DerivedCategory.isLE_iff]
    intro i hi
    rcases lt_or_eq_of_le (show a ≤ i by omega) with hai | rfl
    · exact DerivedCategory.isZero_of_isLE L a i hai
    · exact hHa
  let : t.IsLE L (a - 1) := hL
  let c := (t.natTransTruncLEOfLE (a - 1) a (by omega)).app K
  have hc : c ≫ (t.truncLEι a).app K = (t.truncLEι (a - 1)).app K :=
    t.natTransTruncLEOfLE_ι_app (a - 1) a (by omega) K
  let d : L ⟶ (t.truncLE (a - 1)).obj K :=
    t.liftTruncLE ((t.truncLEι a).app K) (a - 1)
  have hd : d ≫ (t.truncLEι (a - 1)).app K = (t.truncLEι a).app K :=
    t.liftTruncLE_ι ((t.truncLEι a).app K) (a - 1)
  have hcd : c ≫ d = 𝟙 _ := by
    apply t.to_truncLE_obj_ext (n := a - 1)
    simp [Category.assoc, hd, hc]
  have hdc : d ≫ c = 𝟙 _ := by
    apply t.to_truncLE_obj_ext (n := a)
    simp [Category.assoc, hc, hd]
  let ec : (t.truncLE (a - 1)).obj K ≅ L :=
    { hom := c, inv := d, hom_inv_id := hcd, inv_hom_id := hdc }
  let E : K ≅ (t.truncLE (a - 1)).obj K ⊞ U :=
    e ≪≫ (Limits.biprod.mapIso ec.symm (Iso.refl U))
  refine ⟨b, hb, E, compatible_biprod_mapIso ec.symm _ _ _ hd.symm e he, fun E' hE' => ?_⟩
  have heq := he_unique _ (compatible_biprod_mapIso ec _ _ _ hc.symm E' hE')
  have hm : biprod.mapIso ec (Iso.refl U) ≪≫ biprod.mapIso ec.symm (Iso.refl U) = Iso.refl _ := by
    ext <;> simp
  rw [show E = (E' ≪≫ biprod.mapIso ec (Iso.refl U)) ≪≫ biprod.mapIso ec.symm (Iso.refl U) by
    rw [heq], Iso.trans_assoc, hm, Iso.trans_refl]

end Splitting

/-!
### Ext out of a pseudo-coherent object and filtered colimits

The results of this section are [stacks 0G8W]. They are proved here as private lemmas because
the recognition theorem below rests on them; see the module documentation.
-/

section FilteredColimits

open CategoryTheory.Localization Opposite

attribute [local instance] HasDerivedCategory.standard

/-- A bounded complex of finite free modules is K-projective. -/
private lemma isKProjective_of_boundedFiniteFree {R : Type u} [Ring R]
    {E : CochainComplex (ModuleCat.{v} R) ℤ} (hE : PseudoCoherence.IsBoundedFiniteFree E) :
    E.IsKProjective := by
  obtain ⟨b, hb⟩ := hE.upperBound
  let : E.IsStrictlyLE b := hb
  let : ∀ i, Projective (E.X i) := fun i => by
    let : Module.Free R (E.X i) := (hE.finiteFree i).2
    infer_instance
  exact CochainComplex.isKProjective_of_projective E b

/-- Hom complexes out of a degreewise finite free complex commute with a filtered colimit degree
by degree. -/
private lemma preservesColimit_homComplexFunctor {R : Type u} [Ring R]
    {ι : Type v} [Category.{v} ι] [IsFiltered ι]
    (E : CochainComplex (ModuleCat.{v} R) ℤ)
    (hE : ∀ i : ℤ, Module.Finite R (E.X i) ∧ Module.Free R (E.X i))
    (M : ι ⥤ ModuleCat.{v} R) :
    PreservesColimit M (StacksDraft.PseudoCoherence.homComplexFunctor E) := by
  refine preservesColimit_of_preserves_colimit_cocone (colimit.isColimit M) ?_
  apply HomologicalComplex.isColimitOfEval
  intro n
  have : Module.Finite R (E.X (-n)) := (hE (-n)).1
  have : Module.Free R (E.X (-n)) := (hE (-n)).2
  have : PreservesColimit M (StacksDraft.PseudoCoherence.homF (E.X (-n))) :=
    let : IsIso (colimit.post M (StacksDraft.PseudoCoherence.homF (E.X (-n)))) :=
      StacksDraft.PseudoCoherence.comparison_isIso (E.X (-n)) M
    preservesColimit_of_isIso_post _ _
  have : PreservesColimit M
      (StacksDraft.PseudoCoherence.homComplexFunctor E ⋙
        HomologicalComplex.eval AddCommGrpCat.{v} (ComplexShape.up ℤ) n) :=
    preservesColimit_of_natIso M (StacksDraft.PseudoCoherence.homComplexEvalIso E n).symm
  show IsColimit
    ((StacksDraft.PseudoCoherence.homComplexFunctor E ⋙
      HomologicalComplex.eval AddCommGrpCat.{v} (ComplexShape.up ℤ) n).mapCocone
        (colimit.cocone M))
  exact isColimitOfPreserves _ (colimit.isColimit M)

/-- The cohomology of the Hom complex of a degreewise finite free complex commutes with filtered
colimits. -/
private lemma preservesColimit_homComplexCohomologyFunctor
    {R : Type u} [Ring R] {ι : Type v} [Category.{v} ι] [IsFiltered ι]
    (E : CochainComplex (ModuleCat.{v} R) ℤ)
    (hE : ∀ i : ℤ, Module.Finite R (E.X i) ∧ Module.Free R (E.X i))
    (M : ι ⥤ ModuleCat.{v} R) (n : ℤ) :
    PreservesColimit M
      (StacksDraft.PseudoCoherence.homComplexFunctor E ⋙
        HomologicalComplex.homologyFunctor AddCommGrpCat.{v} (ComplexShape.up ℤ) n) := by
  have : HasExactColimitsOfShape ι AddCommGrpCat.{v} := inferInstance
  have : PreservesColimit M (StacksDraft.PseudoCoherence.homComplexFunctor E) :=
    preservesColimit_homComplexFunctor E hE M
  have : PreservesColimitsOfShape ι
      (HomologicalComplex.homologyFunctor AddCommGrpCat.{v} (ComplexShape.up ℤ) n) :=
    preservesColimitsOfShape_homologyFunctor (ComplexShape.up ℤ) n
  infer_instance

private lemma homologyExtAddEquiv_naturality {R : Type u} [Ring R]
    (E : CochainComplex (ModuleCat.{v} R) ℤ) [E.IsKProjective]
    {M N : ModuleCat.{v} R} (f : M ⟶ N) (n : ℤ)
    (x : (E.HomComplex ((CochainComplex.singleFunctor (ModuleCat.{v} R) 0).obj M)).homology n) :
    StacksDraft.PseudoCoherence.homologyExtAddEquiv E N n
      (HomologicalComplex.homologyMap (StacksDraft.PseudoCoherence.homComplexMap E f) n x) =
      StacksDraft.PseudoCoherence.homologyExtAddEquiv E M n x ≫
        ((DerivedCategory.singleFunctor (ModuleCat.{v} R) 0).map f)⟦n⟧' := by
  let L := (CochainComplex.singleFunctor (ModuleCat.{v} R) 0).obj M
  let L' := (CochainComplex.singleFunctor (ModuleCat.{v} R) 0).obj N
  let H := E.HomComplex L
  let H' := E.HomComplex L'
  let h := CochainComplex.HomComplex.leftHomologyData E L n
  let h' := CochainComplex.HomComplex.leftHomologyData E L' n
  have hπ : Function.Surjective (ConcreteCategory.hom (H.homologyπ n)) :=
    (AddCommGrpCat.epi_iff_surjective _).mp inferInstance
  obtain ⟨z, rfl⟩ := hπ x
  let a : CochainComplex.HomComplex.Cocycle E L n := h.cyclesIso.hom z
  have ha : (CochainComplex.HomComplex.homologyAddEquiv E L n)
      (H.homologyπ n z) = CochainComplex.HomComplex.CohomologyClass.mk a :=
    ConcreteCategory.congr_hom
      (ShortComplex.LeftHomologyData.homologyπ_comp_homologyIso_hom (H.sc n) h) z
  have hmap :
      h'.cyclesIso.hom ((HomologicalComplex.cyclesMap
          (StacksDraft.PseudoCoherence.homComplexMap E f) n) z) =
        a.postcomp ((CochainComplex.singleFunctor (ModuleCat.{v} R) 0).map f) := by
    apply Subtype.ext
    have h1 := ConcreteCategory.congr_hom h'.cyclesIso_hom_comp_i
      ((HomologicalComplex.cyclesMap (StacksDraft.PseudoCoherence.homComplexMap E f) n) z)
    have h2 := ConcreteCategory.congr_hom
      (HomologicalComplex.cyclesMap_i (StacksDraft.PseudoCoherence.homComplexMap E f) n) z
    have h3 := ConcreteCategory.congr_hom h.cyclesIso_hom_comp_i z
    simp only [ConcreteCategory.comp_apply] at h1 h2 h3
    refine h1.trans ?_
    refine h2.trans ?_
    show ((HomologicalComplex.iCycles H n) z).comp _ (add_zero n) = a.1.comp _ (add_zero n)
    congr 1
  simp only [StacksDraft.PseudoCoherence.homologyExtAddEquiv, AddEquiv.trans_apply]
  have hnat := ConcreteCategory.congr_hom
    (HomologicalComplex.homologyπ_naturality (StacksDraft.PseudoCoherence.homComplexMap E f) n) z
  simp only [ConcreteCategory.comp_apply] at hnat
  rw [hnat]
  rw [ha]
  have hb : (CochainComplex.HomComplex.homologyAddEquiv E L' n)
      (H'.homologyπ n ((HomologicalComplex.cyclesMap
          (StacksDraft.PseudoCoherence.homComplexMap E f) n) z)) =
      CochainComplex.HomComplex.CohomologyClass.mk
        (a.postcomp ((CochainComplex.singleFunctor (ModuleCat.{v} R) 0).map f)) := by
    rw [← hmap]
    exact ConcreteCategory.congr_hom
      (ShortComplex.LeftHomologyData.homologyπ_comp_homologyIso_hom (H'.sc n) h') _
  rw [hb]
  exact StacksDraft.PseudoCoherence.cohomologyClassExtEquiv_mk_postcomp E f n a

/-- For a K-projective complex `E`, Ext out of `E` into single modules is computed by the
cohomology of the Hom complex, naturally in the module. -/
private noncomputable def extFunctorIsoHomology {R : Type u} [Ring R]
    (E : CochainComplex (ModuleCat.{v} R) ℤ) [E.IsKProjective] (n : ℤ) :
    StacksDraft.PseudoCoherence.homComplexFunctor E ⋙
        HomologicalComplex.homologyFunctor AddCommGrpCat.{v} (ComplexShape.up ℤ) n ⋙
        AddCommGrpCat.uliftFunctor.{max u (v + 1), v} ≅
      DerivedCategory.singleFunctor (ModuleCat.{v} R) 0 ⋙
        shiftFunctor (DerivedCategory (ModuleCat.{v} R)) n ⋙
        preadditiveCoyoneda.obj (op (DerivedCategory.Q.obj E)) :=
  NatIso.ofComponents
    (fun M => (AddEquiv.ulift.trans
      (StacksDraft.PseudoCoherence.homologyExtAddEquiv E M n)).toAddCommGrpIso) (by
      intro M N f
      ext x
      exact homologyExtAddEquiv_naturality E f n x.down)

/-- **[stacks 0G8W].** If `K` is `m`-pseudo-coherent, then the canonical map from the filtered
colimit of `Ext^n(K, Mᵢ)` to `Ext^n(K, colim Mᵢ)` is an isomorphism for `n < -m`, and is a
monomorphism for `n = -m`. -/
private theorem colimit_ext_comparison_isIso_of_lt_and_mono
    {R : Type u} [Ring R] {ι : Type v} [Category.{v} ι] [IsFiltered ι]
    (M : ι ⥤ ModuleCat.{v} R) (K : DerivedCategory (ModuleCat.{v} R)) (m : ℤ)
    (hK : PseudoCoherence.IsPseudoCoherentFrom K m) :
    let extFunctor (n : ℤ) :=
      DerivedCategory.singleFunctor (ModuleCat.{v} R) 0 ⋙
        shiftFunctor (DerivedCategory (ModuleCat.{v} R)) n ⋙
        preadditiveCoyoneda.obj (Opposite.op K)
    (∀ n : ℤ, n < -m →
      IsIso (colimit.desc (M ⋙ extFunctor n)
        ((extFunctor n).mapCocone (colimit.cocone M)))) ∧
      Mono (colimit.desc (M ⋙ extFunctor (-m))
        ((extFunctor (-m)).mapCocone (colimit.cocone M))) := by
  intro extFunctor
  obtain ⟨E, hE, α, hiso, hepi⟩ := hK
  have : E.IsKProjective := isKProjective_of_boundedFiniteFree hE
  have hcone : ∀ (Z : DerivedCategory (ModuleCat.{v} R)) (g : K ⟶ Z)
      (h : Z ⟶ (DerivedCategory.Q.obj E)⟦(1 : ℤ)⟧),
      Pretriangulated.Triangle.mk α g h ∈ Pretriangulated.distinguishedTriangles →
        Z.IsLE (m - 1) := fun Z g h hT =>
    StacksDraft.PseudoCoherence.cone_isLE_of_homology_iso_and_epi _ hT m hiso hepi
  let extE (n : ℤ) :=
    DerivedCategory.singleFunctor (ModuleCat.{v} R) 0 ⋙
      shiftFunctor (DerivedCategory (ModuleCat.{v} R)) n ⋙
      preadditiveCoyoneda.obj (op (DerivedCategory.Q.obj E))
  let τ (n : ℤ) : extFunctor n ⟶ extE n :=
    Functor.whiskerLeft (DerivedCategory.singleFunctor (ModuleCat.{v} R) 0 ⋙
      shiftFunctor (DerivedCategory (ModuleCat.{v} R)) n) (preadditiveCoyoneda.map α.op)
  have hτ : ∀ (n : ℤ) (N : ModuleCat.{v} R),
      (n ≤ -m → Mono ((τ n).app N)) ∧ (n < -m → IsIso ((τ n).app N)) := by
    intro n N
    have key := StacksDraft.PseudoCoherence.precomp_injective_surjective α m hcone N n
    refine ⟨fun hn => ?_, fun hn => ?_⟩
    · rw [AddCommGrpCat.mono_iff_injective]
      exact key.1 hn
    · rw [ConcreteCategory.isIso_iff_bijective]
      exact ⟨key.1 hn.le, key.2 hn⟩
  have hE' : ∀ n : ℤ, IsIso (colimit.post M (extE n)) := by
    intro n
    have := preservesColimit_homComplexCohomologyFunctor E
      (fun i => ⟨(hE.finiteFree i).1, (hE.finiteFree i).2⟩) M n
    have : PreservesColimit M
        (StacksDraft.PseudoCoherence.homComplexFunctor E ⋙
          HomologicalComplex.homologyFunctor AddCommGrpCat.{v} (ComplexShape.up ℤ) n ⋙
          AddCommGrpCat.uliftFunctor.{max u (v + 1), v}) :=
      comp_preservesColimit (StacksDraft.PseudoCoherence.homComplexFunctor E ⋙
          HomologicalComplex.homologyFunctor AddCommGrpCat.{v} (ComplexShape.up ℤ) n)
        AddCommGrpCat.uliftFunctor.{max u (v + 1), v}
    have : PreservesColimit M (extE n) :=
      preservesColimit_of_natIso M (extFunctorIsoHomology E n)
    exact inferInstanceAs (IsIso (colimit.post M (extE n)))
  have hsq : ∀ n : ℤ, colimit.post M (extFunctor n) ≫ (τ n).app (colimit M) =
      colim.map (Functor.whiskerLeft M (τ n)) ≫ colimit.post M (extE n) := fun n =>
    colimit.hom_ext fun j => by
      rw [colimit.ι_post_assoc, colim_map, ι_colimMap_assoc, colimit.ι_post]
      exact (τ n).naturality (colimit.ι M j)
  have := AB5OfSize_shrink.{v, v, max u (v + 1), max u (v + 1)}
    (C := AddCommGrpCat.{max u (v + 1)})
  constructor
  · intro n hn
    have : ∀ N, IsIso ((τ n).app N) := fun N => (hτ n N).2 hn
    have : ∀ j, IsIso ((Functor.whiskerLeft M (τ n)).app j) := fun j =>
      (hτ n (M.obj j)).2 hn
    have : IsIso (Functor.whiskerLeft M (τ n)) := NatIso.isIso_of_isIso_app _
    have := hE' n
    show IsIso (colimit.post M (extFunctor n))
    have h2 : IsIso (colimit.post M (extFunctor n) ≫ (τ n).app (colimit M)) := by
      rw [hsq]; infer_instance
    exact IsIso.of_isIso_comp_right _ ((τ n).app (colimit M))
  · have : ∀ N, Mono ((τ (-m)).app N) := fun N => (hτ (-m) N).1 le_rfl
    have := hE' (-m)
    have : ∀ j, Mono ((Functor.whiskerLeft M (τ (-m))).app j) := fun j =>
      (hτ (-m) (M.obj j)).1 le_rfl
    have : Mono (Functor.whiskerLeft M (τ (-m))) := NatTrans.mono_of_mono_app _
    show Mono (colimit.post M (extFunctor (-m)))
    have : Mono (colim.map (Functor.whiskerLeft M (τ (-m)))) := inferInstance
    have h2 : Mono (colimit.post M (extFunctor (-m)) ≫ (τ (-m)).app (colimit M)) := by
      rw [hsq]; exact mono_comp _ _
    exact mono_of_mono _ ((τ (-m)).app (colimit M))

end FilteredColimits

/-!
### Every module is a filtered colimit of finitely presented modules

The system below is indexed by pairs consisting of a finite set of generators and a finite set of
relations among them; it realizes an arbitrary module as a filtered colimit of finitely presented
modules. Together with [stacks 0G8W] this reduces Ext vanishing against all modules to Ext
vanishing against finitely presented ones.
-/

section FinitePresentationColimit

attribute [local instance] HasDerivedCategory.standard

private theorem isZero_colimit_of_isZero
    {J C : Type*} [Category J] [Category C] [HasZeroMorphisms C]
    [HasColimitsOfShape J C] (F : J ⥤ C) (h : ∀ j, IsZero (F.obj j)) :
    IsZero (colimit F) := by
  rw [IsZero.iff_id_eq_zero]
  exact colimit.hom_ext fun j => (h j).eq_of_src _ _

/-- The tautological surjection from the free module on the elements of `M` onto `M`. -/
private noncomputable def freeProj (R : Type u) [CommRing R] [Small.{v} R]
    (M : Type v) [AddCommGroup M] [Module R M] : (M →₀ Shrink.{v} R) →ₗ[R] M :=
  Finsupp.lsum R fun x ↦ LinearMap.toSpanSingleton R M x ∘ₗ
    (Shrink.linearEquiv R R).toLinearMap

@[local simp] private theorem freeProj_single (R : Type u) [CommRing R] [Small.{v} R]
    (M : Type v) [AddCommGroup M] [Module R M] (x : M) (r : Shrink.{v} R) :
    freeProj R M (Finsupp.single x r) = Shrink.linearEquiv R R r • x := by
  simp [freeProj, LinearMap.toSpanSingleton_apply]

/-- The free submodule on a finite set of elements of `M`. -/
private noncomputable abbrev freePart (R : Type u) [CommRing R] [Small.{v} R]
    (M : Type v) [AddCommGroup M] [Module R M] (T : Finset M) :
    Submodule R (M →₀ Shrink.{v} R) :=
  Finsupp.supported (Shrink.{v} R) R (↑T : Set M)

/-- The index set of the presenting system: a finite set of generators together with a finite set
of relations among them. -/
private abbrev PresentationIndex (R : Type u) [CommRing R] [Small.{v} R]
    (M : Type v) [AddCommGroup M] [Module R M] : Type v :=
  Finset M × Finset (M →₀ Shrink.{v} R)

private noncomputable instance (R : Type u) [CommRing R] [Small.{v} R]
    (M : Type v) [AddCommGroup M] [Module R M] : DecidableEq (PresentationIndex R M) :=
  Classical.decEq _

private instance (R : Type u) [CommRing R] [Small.{v} R]
    (M : Type v) [AddCommGroup M] [Module R M] : IsDirectedOrder (PresentationIndex R M) := by
  classical
  exact ⟨fun x y ↦ ⟨(x.1 ∪ y.1, x.2 ∪ y.2),
    ⟨Finset.subset_union_left, Finset.subset_union_left⟩,
    ⟨Finset.subset_union_right, Finset.subset_union_right⟩⟩⟩

private noncomputable abbrev relations (R : Type u) [CommRing R] [Small.{v} R]
    (M : Type v) [AddCommGroup M] [Module R M] (j : PresentationIndex R M) :
    Submodule R (freePart R M j.1) :=
  Submodule.span R
    {y | (y : M →₀ Shrink.{v} R) ∈ j.2 ∧ freeProj R M (y : M →₀ Shrink.{v} R) = 0}

private noncomputable instance (R : Type u) [CommRing R] [Small.{v} R]
    (M : Type v) [AddCommGroup M] [Module R M] (T : Finset M) :
    HasQuotient (freePart R M T) (Submodule R (freePart R M T)) :=
  ⟨fun p ↦ Quotient (Submodule.quotientRel (R := R) (M := freePart R M T) p)⟩

private noncomputable abbrev presentation (R : Type u) [CommRing R] [Small.{v} R]
    (M : Type v) [AddCommGroup M] [Module R M] (j : PresentationIndex R M) : Type v :=
  (freePart R M j.1) ⧸ relations R M j

private noncomputable abbrev quotientAddCommGroup
    (R : Type u) [Ring R] (A : Type v) [AddCommGroup A] [Module R A]
    (P : Submodule R A) : AddCommGroup (A ⧸ P) :=
  Submodule.Quotient.addCommGroup P

private noncomputable abbrev quotientModule
    (R : Type u) [Ring R] (A : Type v) [AddCommGroup A] [Module R A]
    (P : Submodule R A) : Module R (A ⧸ P) :=
  Submodule.Quotient.module P

private noncomputable instance (R : Type u) [CommRing R] [Small.{v} R]
    (M : Type v) [AddCommGroup M] [Module R M] (j : PresentationIndex R M) :
    AddCommGroup (presentation R M j) :=
  @quotientAddCommGroup R inferInstance (freePart R M j.1) inferInstance inferInstance
    (relations R M j)

private noncomputable instance (R : Type u) [CommRing R] [Small.{v} R]
    (M : Type v) [AddCommGroup M] [Module R M] (j : PresentationIndex R M) :
    Module R (presentation R M j) :=
  @quotientModule R inferInstance (freePart R M j.1) inferInstance inferInstance
    (relations R M j)

private theorem relations_mono (R : Type u) [CommRing R] [Small.{v} R]
    (M : Type v) [AddCommGroup M] [Module R M] {j k : PresentationIndex R M} (h : j ≤ k) :
    relations R M j ≤ (relations R M k).comap
      (Submodule.inclusion (Finsupp.supported_mono (Finset.coe_subset.2 h.1))) := by
  refine Submodule.span_le.2 ?_
  rintro y ⟨hy₁, hy₂⟩
  exact Submodule.subset_span ⟨h.2 hy₁, hy₂⟩

private noncomputable def transition (R : Type u) [CommRing R] [Small.{v} R]
    (M : Type v) [AddCommGroup M] [Module R M] (j k : PresentationIndex R M) (h : j ≤ k) :
    presentation R M j →ₗ[R] presentation R M k :=
  Submodule.mapQ _ _ (Submodule.inclusion (Finsupp.supported_mono (Finset.coe_subset.2 h.1)))
    (relations_mono R M h)

@[local simp] private theorem transition_mk (R : Type u) [CommRing R] [Small.{v} R]
    (M : Type v) [AddCommGroup M] [Module R M] (j k : PresentationIndex R M) (h : j ≤ k)
    (y : freePart R M j.1) :
    transition R M j k h (Submodule.Quotient.mk y) =
      Submodule.Quotient.mk (Submodule.inclusion
        (Finsupp.supported_mono (Finset.coe_subset.2 h.1)) y) := rfl

private instance (R : Type u) [CommRing R] [Small.{v} R]
    (M : Type v) [AddCommGroup M] [Module R M] :
    DirectedSystem (presentation R M) fun j k h ↦ (transition R M j k h : _ → _) where
  map_self j x := by
    induction x using Quotient.inductionOn with
    | _ y => exact congrArg _ (Subtype.ext rfl)
  map_map {j k l} hjk hkl x := by
    induction x using Quotient.inductionOn with
    | _ y => exact congrArg _ (Subtype.ext rfl)

private noncomputable def presentationToModule (R : Type u) [CommRing R] [Small.{v} R]
    (M : Type v) [AddCommGroup M] [Module R M] (j : PresentationIndex R M) :
    presentation R M j →ₗ[R] M :=
  Submodule.liftQ _ (freeProj R M ∘ₗ (freePart R M j.1).subtype) (by
    refine Submodule.span_le.2 ?_
    rintro y ⟨-, hy⟩
    simpa using hy)

@[local simp] private theorem presentationToModule_mk (R : Type u) [CommRing R] [Small.{v} R]
    (M : Type v) [AddCommGroup M] [Module R M] (j : PresentationIndex R M)
    (y : freePart R M j.1) :
    presentationToModule R M j (Submodule.Quotient.mk y) =
      freeProj R M (y : M →₀ Shrink.{v} R) := rfl

private theorem presentationToModule_transition (R : Type u) [CommRing R] [Small.{v} R]
    (M : Type v) [AddCommGroup M] [Module R M] (j k : PresentationIndex R M) (h : j ≤ k)
    (x : presentation R M j) :
    presentationToModule R M k (transition R M j k h x) = presentationToModule R M j x := by
  induction x using Quotient.inductionOn with
  | _ y => rfl

private theorem finitePresentation_freePart (R : Type u) [CommRing R] [Small.{v} R]
    (M : Type v) [AddCommGroup M] [Module R M] (T : Finset M) :
    Module.FinitePresentation R (freePart R M T) := by
  have hfinite : Module.Finite R ((↑T : Set M) →₀ Shrink.{v} R) :=
    Module.Finite.equiv (Finsupp.linearEquivFunOnFinite R (Shrink.{v} R) (↑T : Set M)).symm
  have : Module.FinitePresentation R ((↑T : Set M) →₀ Shrink.{v} R) :=
    Module.finitePresentation_of_projective _ _
  let : Module.FinitePresentation R ((↑T : Set M) →₀ Shrink.{v} R) := this
  exact Module.FinitePresentation.of_equiv
    (Finsupp.supportedEquivFinsupp (↑T : Set M) : _ ≃ₗ[R] ((↑T : Set M) →₀ Shrink.{v} R)).symm

private theorem finitePresentation_quotient
    (R : Type u) [Ring R] (A : Type v) [AddCommGroup A] [Module R A]
    (P : Submodule R A) (hP : P.FG) [fp : Module.FinitePresentation R A] :
    Module.FinitePresentation R (A ⧸ P) :=
  @Module.finitePresentation_of_surjective R A
    (A ⧸ P)
    inferInstance inferInstance inferInstance
    (Submodule.Quotient.addCommGroup P)
    (Submodule.Quotient.module P) fp P.mkQ P.mkQ_surjective (by rwa [Submodule.ker_mkQ])

private theorem finitePresentation_presentation (R : Type u) [CommRing R] [Small.{v} R]
    (M : Type v) [AddCommGroup M] [Module R M] (j : PresentationIndex R M) :
    Module.FinitePresentation R (presentation R M j) := by
  let : Module.FinitePresentation R (freePart R M j.1) :=
    finitePresentation_freePart R M j.1
  exact finitePresentation_quotient R (freePart R M j.1) (relations R M j) <| Submodule.fg_span
    (Set.Finite.subset (j.2.finite_toSet.preimage Subtype.coe_injective.injOn) fun _ hy ↦ hy.1)

private theorem exists_presentationToModule_eq (R : Type u) [CommRing R] [Small.{v} R]
    (M : Type v) [AddCommGroup M] [Module R M] (m : M) :
    ∃ (j : PresentationIndex R M) (x : presentation R M j),
      presentationToModule R M j x = m := by
  refine ⟨({m}, ∅), Submodule.Quotient.mk
    ⟨Finsupp.single m ((Shrink.linearEquiv R R).symm 1),
      Finsupp.single_mem_supported R _ (by simp)⟩, ?_⟩
  rw [presentationToModule_mk]
  simp

private theorem exists_transition_eq_zero (R : Type u) [CommRing R] [Small.{v} R]
    (M : Type v) [AddCommGroup M] [Module R M] (j : PresentationIndex R M)
    (x : presentation R M j) (hx : presentationToModule R M j x = 0) :
    ∃ (k : PresentationIndex R M) (h : j ≤ k), transition R M j k h x = 0 := by
  classical
  induction x using Quotient.inductionOn with
  | _ y =>
      change freeProj R M (y : M →₀ Shrink.{v} R) = 0 at hx
      refine ⟨(j.1, insert (↑y : M →₀ Shrink.{v} R) j.2),
        ⟨le_rfl, Finset.subset_insert _ _⟩, ?_⟩
      exact (Submodule.Quotient.mk_eq_zero _).2
        (Submodule.subset_span ⟨Finset.mem_insert_self _ _, by simpa using hx⟩)

private noncomputable def presentationLift (R : Type u) [CommRing R] [Small.{v} R]
    (M : Type v) [AddCommGroup M] [Module R M] :
    Module.DirectLimit (presentation R M) (transition R M) →ₗ[R] M :=
  Module.DirectLimit.lift R (PresentationIndex R M) (presentation R M) (transition R M)
    (presentationToModule R M) fun j k h x ↦ presentationToModule_transition R M j k h x

private theorem presentationLift_bijective (R : Type u) [CommRing R] [Small.{v} R]
    (M : Type v) [AddCommGroup M] [Module R M] :
    Function.Bijective (presentationLift R M) := by
  refine ⟨(injective_iff_map_eq_zero _).mpr fun z hz ↦ ?_, fun m ↦ ?_⟩
  · obtain ⟨j, x, rfl⟩ := Module.DirectLimit.exists_of z
    rw [presentationLift, Module.DirectLimit.lift_of] at hz
    obtain ⟨k, hjk, hzero⟩ := exists_transition_eq_zero R M j x hz
    rw [← Module.DirectLimit.of_f (hij := hjk), hzero, map_zero]
  · obtain ⟨j, x, hx⟩ := exists_presentationToModule_eq R M m
    exact ⟨Module.DirectLimit.of R _ _ _ j x, by
      rw [presentationLift, Module.DirectLimit.lift_of, hx]⟩

private noncomputable def presentationEquiv (R : Type u) [CommRing R] [Small.{v} R]
    (M : Type v) [AddCommGroup M] [Module R M] :
    Module.DirectLimit (presentation R M) (transition R M) ≃ₗ[R] M :=
  LinearEquiv.ofBijective (presentationLift R M) (presentationLift_bijective R M)

/-- For a pseudo-coherent object, Ext vanishing against all finitely presented modules already
gives Ext vanishing against every module. -/
private theorem ext_subsingleton_of_finitePresentation
    {R : Type u} [CommRing R] [Small.{v} R]
    (K : DerivedCategory (ModuleCat.{v} R))
    (hK : StacksDraft.PseudoCoherence.IsPseudoCoherent K) (i : ℤ)
    (h : ∀ N : ModuleCat.{v} R, Module.FinitePresentation R N →
      Subsingleton (DerivedCategory.Ext K
        ((DerivedCategory.singleFunctor (ModuleCat.{v} R) 0).obj N) i)) :
    ∀ N : ModuleCat.{v} R,
      Subsingleton (DerivedCategory.Ext K
        ((DerivedCategory.singleFunctor (ModuleCat.{v} R) 0).obj N) i) := by
  intro N
  let : Category (PresentationIndex R N) := Preorder.smallCategory _
  let M := ModuleCat.directLimitDiagram (presentation R N) (transition R N)
  let c := ModuleCat.directLimitCocone (presentation R N) (transition R N)
  let hc : IsColimit c := ModuleCat.directLimitIsColimit (presentation R N) (transition R N)
  let extFunctor :=
    DerivedCategory.singleFunctor (ModuleCat.{v} R) 0 ⋙
      shiftFunctor (DerivedCategory (ModuleCat.{v} R)) i ⋙
      preadditiveCoyoneda.obj (Opposite.op K)
  have hpc : PseudoCoherence.IsPseudoCoherentFrom K (-i - 1) :=
    (StacksDraft.PseudoCoherence.pseudoCoherent_iff_all K).1 hK (-i - 1)
  have hcomparison : IsIso (colimit.desc (M ⋙ extFunctor)
      (extFunctor.mapCocone (colimit.cocone M))) := by
    simpa [M, extFunctor] using
      (colimit_ext_comparison_isIso_of_lt_and_mono M K (-i - 1) hpc).1 i (by omega)
  let D := M ⋙ extFunctor
  have hsource : Subsingleton ((colimit D : AddCommGrpCat) : Type _) := by
    rw [← AddCommGrpCat.isZero_iff_subsingleton]
    exact isZero_colimit_of_isZero _ fun j => AddCommGrpCat.isZero_iff_subsingleton.mpr <|
      h (ModuleCat.of R (presentation R N j)) (finitePresentation_presentation R N j)
  let alpha := colimit.desc (M ⋙ extFunctor) (extFunctor.mapCocone (colimit.cocone M))
  have htarget : Subsingleton (extFunctor.obj (colimit M)) := by
    rw [← AddCommGrpCat.isZero_iff_subsingleton]
    exact IsZero.of_iso (AddCommGrpCat.isZero_iff_subsingleton.mpr hsource) (asIso alpha).symm
  let colimIso : colimit M ≅ c.pt := (colimit.isColimit M).coconePointUniqueUpToIso hc
  let eIso : c.pt ≅ N := (presentationEquiv R N).toModuleIso
  show Subsingleton (extFunctor.obj N)
  rw [← AddCommGrpCat.isZero_iff_subsingleton]
  exact IsZero.of_iso (AddCommGrpCat.isZero_iff_subsingleton.mpr htarget)
    (extFunctor.mapIso (colimIso.trans eIso)).symm

end FinitePresentationColimit

/-! ### Recognizing perfect complexes of bounded projective amplitude -/

section ProjectiveAmplitudeCriterion

attribute [local instance] HasDerivedCategory.standard

/-- **Stacks 0G9A.** Let `K` be a pseudo-coherent object of `D(R)` and let `a, b` be integers.
The following are equivalent:
(1) `K` has projective amplitude in `[a, b]`;
(2) `K` is perfect and has Tor amplitude in `[a, b]`, recorded by the existence of a flat
representative supported in `[a, b]`;
(3) `Ext^i(K, N) = 0` for every finitely presented `R`-module `N` and every `i ∉ [-b, -a]`;
(4) `H^n(K) = 0` for `n > b` and `Ext^i(K, N) = 0` for every finitely presented `N` and every
`i > -a`;
(5) `H^n(K) = 0` for `n ∉ [a - 1, b]` and `Ext^{-a + 1}(K, N) = 0` for every finitely presented
`N`. -/
@[stacks 0G9A]
theorem hasProjectiveAmplitude_iff_perfect_iff_ext_vanishing
    {R : Type u} [CommRing R] (K : DerivedCategory (ModuleCat.{max u v} R))
    (hK : StacksDraft.PseudoCoherence.IsPseudoCoherent K) (a b : ℤ) :
    let moduleObject := fun N : ModuleCat.{max u v} R ↦
      (DerivedCategory.singleFunctor (ModuleCat.{max u v} R) 0).obj N
    let projectiveAmplitude := HasProjectiveAmplitude K a b
    let perfectTorAmplitude := Perfect.IsPerfect K ∧ Perfect.HasFlatRepresentative K a b
    let extOutsideVanishes := ∀ N : ModuleCat.{max u v} R, Module.FinitePresentation R N →
      ∀ i : ℤ, i ∉ Set.Icc (-b) (-a) →
        Subsingleton (DerivedCategory.Ext K (moduleObject N) i)
    let upperVanishing :=
      (∀ n : ℤ, b < n →
          IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} R) n).obj K)) ∧
        ∀ N : ModuleCat.{max u v} R, Module.FinitePresentation R N →
          ∀ i : ℤ, -a < i → Subsingleton (DerivedCategory.Ext K (moduleObject N) i)
    let endpointVanishing :=
      (∀ n : ℤ, n ∉ Set.Icc (a - 1) b →
          IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} R) n).obj K)) ∧
        ∀ N : ModuleCat.{max u v} R, Module.FinitePresentation R N →
          Subsingleton (DerivedCategory.Ext K (moduleObject N) (-a + 1))
    (projectiveAmplitude ↔ perfectTorAmplitude) ∧
      (perfectTorAmplitude ↔ extOutsideVanishes) ∧
      (extOutsideVanishes ↔ upperVanishing) ∧
      (upperVanishing ↔ endpointVanishing) := by
  dsimp only
  have : Small.{max u v} R := small_max R
  -- `(1) ↔ (2)`: a projective representative is a flat one, and conversely [stacks 0658] turns a
  -- flat representative of a pseudo-coherent object into a finite projective one.
  have hPA : HasProjectiveAmplitude K a b ↔
      (Perfect.IsPerfect K ∧ Perfect.HasFlatRepresentative K a b) := by
    constructor
    · rintro ⟨P, ⟨e⟩, hP, hge, hle⟩
      have hflat : Perfect.HasFlatRepresentative K a b := by
        refine ⟨P, fun i => ?_, hge, hle, ⟨e.symm⟩⟩
        let : Module.Projective R (P.X i) := hP i
        infer_instance
      exact ⟨(Perfect.isPerfect_iff_pseudoCoherent_and_finiteTorDimension K).1.mpr
        ⟨hK, a, b, hflat⟩, hflat⟩
    · rintro ⟨-, hflat⟩
      obtain ⟨E, hfp, hge, hle, ⟨e⟩⟩ :=
        (Perfect.isPerfect_iff_pseudoCoherent_and_finiteTorDimension K).2 a b hK hflat
      exact ⟨E, ⟨e.symm⟩, fun i => (hfp i).2, hge, hle⟩
  -- The three Ext criteria of [stacks 0A5P] are stated for all modules; pseudo-coherence lets one
  -- test them on finitely presented modules only.
  obtain ⟨hAB, hBC, hCD⟩ := hasProjectiveAmplitude_iff_ext_vanishing K a b
  have hBfp : (∀ (N : ModuleCat.{max u v} R) (i : ℤ), i ∉ Set.Icc (-b) (-a) →
        Subsingleton (DerivedCategory.Ext K
          ((DerivedCategory.singleFunctor (ModuleCat.{max u v} R) 0).obj N) i)) ↔
      ∀ N : ModuleCat.{max u v} R, Module.FinitePresentation R N →
        ∀ i : ℤ, i ∉ Set.Icc (-b) (-a) →
          Subsingleton (DerivedCategory.Ext K
            ((DerivedCategory.singleFunctor (ModuleCat.{max u v} R) 0).obj N) i) :=
    ⟨fun h N _ i hi ↦ h N i hi,
      fun h N i hi ↦ ext_subsingleton_of_finitePresentation K hK i (fun P hP ↦ h P hP i hi) N⟩
  have hCfp : ((∀ n : ℤ, b < n →
          IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} R) n).obj K)) ∧
        ∀ (N : ModuleCat.{max u v} R) (i : ℤ), -a < i →
          Subsingleton (DerivedCategory.Ext K
            ((DerivedCategory.singleFunctor (ModuleCat.{max u v} R) 0).obj N) i)) ↔
      ((∀ n : ℤ, b < n →
          IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} R) n).obj K)) ∧
        ∀ N : ModuleCat.{max u v} R, Module.FinitePresentation R N →
          ∀ i : ℤ, -a < i → Subsingleton (DerivedCategory.Ext K
            ((DerivedCategory.singleFunctor (ModuleCat.{max u v} R) 0).obj N) i)) :=
    ⟨fun h ↦ ⟨h.1, fun N _ i hi ↦ h.2 N i hi⟩,
      fun h ↦ ⟨h.1, fun N i hi ↦ ext_subsingleton_of_finitePresentation K hK i
        (fun P hP ↦ h.2 P hP i hi) N⟩⟩
  have hDfp : ((∀ n : ℤ, n ∉ Set.Icc (a - 1) b →
          IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} R) n).obj K)) ∧
        ∀ N : ModuleCat.{max u v} R, Subsingleton (DerivedCategory.Ext K
          ((DerivedCategory.singleFunctor (ModuleCat.{max u v} R) 0).obj N) (-a + 1))) ↔
      ((∀ n : ℤ, n ∉ Set.Icc (a - 1) b →
          IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} R) n).obj K)) ∧
        ∀ N : ModuleCat.{max u v} R, Module.FinitePresentation R N →
          Subsingleton (DerivedCategory.Ext K
            ((DerivedCategory.singleFunctor (ModuleCat.{max u v} R) 0).obj N) (-a + 1))) :=
    ⟨fun h ↦ ⟨h.1, fun N _ ↦ h.2 N⟩,
      fun h ↦ ⟨h.1, ext_subsingleton_of_finitePresentation K hK (-a + 1) h.2⟩⟩
  exact ⟨hPA, hPA.symm.trans (hAB.trans hBfp),
    hBfp.symm.trans (hBC.trans hCfp), hCfp.symm.trans (hCD.trans hDfp)⟩

end ProjectiveAmplitudeCriterion

end StacksDraft.ProjectiveAmplitude
