module

public import Mathlib
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Homology.SpectralSequence.HomologicalFiltration
public import StacksFrontier.Algebra.Module.ProjResComplexFlat
public import StacksFrontier.Homology.DerivedCategory.MapHomologyIso
public import StacksFrontier.Homology.ExtendScalars.Flat
public import StacksFrontier.Homology.TorAmplitude.Comparison
public import StacksFrontier.Homology.TorAmplitude.FaithfullyFlat
public import StacksFrontier.Homology.Tor.DerivedChangeOfRings
public import StacksFrontier.Homology.TensorComplex.SingleTensor
public import StacksFrontier.Homology.KFlat.Resolution
public import StacksFrontier.Homology.TorAmplitude.ProjResKFlat
public import StacksFrontier.Homology.DerivedCategory.SubcomplexEnlargement.BoundedSubcomplexes

@[expose] public noncomputable section

/-!
# The union of an increasing chain of subcomplexes

Filtered colimits of subcomplexes, and the kernel and image conditions on cohomology at the stages
of an increasing chain of subcomplexes, in both directions: an isomorphism of filtered colimits
realizes the kernel and image witnesses of a stage at one later stage, and conversely.

## Main definitions

* `Stacks.SubcomplexEnlargement.SubcomplexFamily`: a degreewise family of submodules of the terms
  of a complex of modules, closed under the differential, together with
  `SubcomplexFamily.toComplex` and `SubcomplexFamily.ι`, the subcomplex it cuts out and its
  inclusion.
* `Stacks.SubcomplexEnlargement.familyDiagram` and `Stacks.SubcomplexEnlargement.familyCocone`: an
  increasing collection of such families, read as a diagram of subcomplexes and as a cocone on the
  ambient complex.

## Main results

* `Stacks.SubcomplexEnlargement.familyIsColimit`: a directed collection of subcomplexes covering
  every degree has the ambient complex as its colimit.
* `Stacks.SubcomplexEnlargement.isIso_colimMap_of_stagewise`: a map of filtered diagrams of modules
  from each stage of which there is a step annihilating its kernel and a step whose image it
  already covers induces an isomorphism on colimits.
* `Stacks.SubcomplexEnlargement.isColimit_familyCocone_sequence`: a sequence of maps into a complex
  whose degreewise images exhaust it presents it as the colimit of those images, indexed by
  `sequenceRangeFamily`.
* `Stacks.SubcomplexEnlargement.isIso_of_stagewise_kernel_and_image`: the conclusion of
  `isIso_colimMap_of_stagewise` read on arbitrary colimit cocones instead of on `colimit`, which
  is how the union of an increasing chain of subcomplexes arrives.
* `Stacks.SubcomplexEnlargement.isIso_comparison_of_stagewise_union`: if a comparison map between
  derived base changes satisfies the stagewise kernel and image conditions along increasing chains
  of subcomplexes exhausting its source and target, then it is an isomorphism at the union.

## References

* [Stacks Project, Tag 0GYI](https://stacks.math.columbia.edu/tag/0GYI)
-/

open CategoryTheory CategoryTheory.Limits

namespace Stacks.SubcomplexEnlargement

universe u v w t

attribute [local instance] HasDerivedCategory.standard

open Cardinal

/-- Forgetting module structure preserves filtered colimits in the module universe. -/
private lemma forget_preservesFilteredColimitsOfShape
    {R : Type u} [Ring R] {J : Type v} [SmallCategory J] [IsFiltered J] :
    PreservesColimitsOfShape J (forget (ModuleCat.{v} R)) := by
  change PreservesColimitsOfShape J
    (forget₂ (ModuleCat.{v} R) AddCommGrpCat.{v} ⋙ forget AddCommGrpCat.{v})
  infer_instance

attribute [local instance] forget_preservesFilteredColimitsOfShape

/-- An element vanishing in a filtered colimit vanishes at some later stage. -/
private lemma exists_map_eq_zero_of_isColimit
    {R : Type u} [Ring R] {J : Type v} [SmallCategory J] [IsFiltered J]
    {F : J ⥤ ModuleCat.{v} R} {c : Cocone F} (hc : IsColimit c)
    {j : J} (x : F.obj j) (hx : (c.ι.app j) x = 0) :
    ∃ (k : J) (f : j ⟶ k), (F.map f) x = 0 := by
  have h : (c.ι.app j) x = (c.ι.app j) 0 := by simpa using hx
  obtain ⟨k, f, hf⟩ := (hc.eq_iff' x 0).mp h
  exact ⟨k, f, by simpa using hf⟩

/-- A monomorphism between filtered colimits kills each stagewise kernel eventually. -/
private lemma exists_map_eq_zero_of_mono_colimitMap
    {R : Type u} [Ring R] {J : Type v} [SmallCategory J] [IsFiltered J]
    {F G : J ⥤ ModuleCat.{v} R} (α : F ⟶ G)
    {cF : Cocone F} {cG : Cocone G} (hF : IsColimit cF)
    (g : cF.pt ⟶ cG.pt) [Mono g]
    (hg : ∀ j, cF.ι.app j ≫ g = α.app j ≫ cG.ι.app j)
    {j : J} (x : F.obj j) (hx : (α.app j) x = 0) :
    ∃ (k : J) (f : j ⟶ k), (F.map f) x = 0 := by
  apply exists_map_eq_zero_of_isColimit hF x
  apply (ModuleCat.mono_iff_injective g).mp inferInstance
  calc
    g ((cF.ι.app j) x) = (cG.ι.app j) ((α.app j) x) :=
      congrArg (fun h : F.obj j ⟶ cG.pt => h x) (hg j)
    _ = g 0 := by simp [hx]

/-- An epimorphism between filtered colimits covers each stagewise element eventually. -/
private lemma exists_preimage_of_epi_colimitMap
    {R : Type u} [Ring R] {J : Type v} [SmallCategory J] [IsFiltered J]
    {F G : J ⥤ ModuleCat.{v} R} (α : F ⟶ G)
    {cF : Cocone F} {cG : Cocone G} (hF : IsColimit cF) (hG : IsColimit cG)
    (g : cF.pt ⟶ cG.pt) [Epi g]
    (hg : ∀ j, cF.ι.app j ≫ g = α.app j ≫ cG.ι.app j)
    {j : J} (y : G.obj j) :
    ∃ (k : J) (f : j ⟶ k) (x : F.obj k), (α.app k) x = (G.map f) y := by
  obtain ⟨z, hz⟩ := (ModuleCat.epi_iff_surjective g).mp inferInstance ((cG.ι.app j) y)
  obtain ⟨i, x, hx⟩ := Concrete.isColimit_exists_rep F hF z
  have he : (cG.ι.app i) ((α.app i) x) = (cG.ι.app j) y := by
    calc
      _ = g ((cF.ι.app i) x) :=
        (congrArg (fun h : F.obj i ⟶ cG.pt => h x) (hg i)).symm
      _ = _ := by rw [show (cF.ι.app i) x = z from hx, hz]
  obtain ⟨k, p, q, hpq⟩ := (hG.eq_iff G).mp he
  refine ⟨k, q, (F.map p) x, ?_⟩
  calc
    _ = (G.map p) ((α.app i) x) :=
      congrArg (fun h : F.obj i ⟶ G.obj k => h x) (α.naturality p)
    _ = _ := hpq

/-- A sufficiently directed presentation realizes all kernel and image witnesses at one stage. -/
lemma exists_stage_killing_kernel_and_covering_image
    {R : Type u} [Ring R] {J : Type v} [SmallCategory J] [IsFiltered J] [Quiver.IsThin J]
    {F G : J ⥤ ModuleCat.{v} R} (α : F ⟶ G)
    {cF : Cocone F} {cG : Cocone G} (hF : IsColimit cF) (hG : IsColimit cG)
    (g : cF.pt ⟶ cG.pt) [IsIso g]
    (hg : ∀ j, cF.ι.app j ≫ g = α.app j ≫ cG.ι.app j)
    {κ : Cardinal.{v}} (hκ : ℵ₀ ≤ κ)
    (hJ : ∀ s : Set J, #s ≤ κ → ∃ k, ∀ j ∈ s, Nonempty (j ⟶ k))
    (j : J) (hFj : #(F.obj j) ≤ κ) (hGj : #(G.obj j) ≤ κ) :
    ∃ (k : J) (p : j ⟶ k),
      (∀ x : F.obj j, (α.app j) x = 0 → (F.map p) x = 0) ∧
      (∀ y : G.obj j, ∃ x : F.obj k, (α.app k) x = (G.map p) y) := by
  classical
  have hx : ∀ x : F.obj j, ∃ (k : J) (p : j ⟶ k),
      (α.app j) x = 0 → (F.map p) x = 0 := by
    intro x
    by_cases h : (α.app j) x = 0
    · obtain ⟨k, p, hp⟩ := exists_map_eq_zero_of_mono_colimitMap α hF g hg x h
      exact ⟨k, p, fun _ => hp⟩
    · exact ⟨j, 𝟙 j, fun h' => (h h').elim⟩
  choose kx px hx using hx
  have hy := fun y : G.obj j => exists_preimage_of_epi_colimitMap α hF hG g hg y
  choose ky py xy hy using hy
  let s : Set J := {j} ∪ Set.range kx ∪ Set.range ky
  have hs : #s ≤ κ := by
    apply (mk_union_le _ _).trans
    apply add_le_of_le hκ
    · apply (mk_union_le _ _).trans
      apply add_le_of_le hκ
      · simpa only [mk_singleton] using (one_le_aleph0.trans hκ)
      · exact (mk_range_le (f := kx)).trans hFj
    · exact (mk_range_le (f := ky)).trans hGj
  obtain ⟨k, hk⟩ := hJ s hs
  let p : j ⟶ k := (hk j (Or.inl (Or.inl rfl))).some
  let qx (x : F.obj j) : kx x ⟶ k := (hk _ (Or.inl (Or.inr ⟨x, rfl⟩))).some
  let qy (y : G.obj j) : ky y ⟶ k := (hk _ (Or.inr ⟨y, rfl⟩)).some
  refine ⟨k, p, ?_, ?_⟩
  · intro x hx0
    have hp : p = px x ≫ qx x := Subsingleton.elim _ _
    rw [hp, F.map_comp]
    change (F.map (qx x)) ((F.map (px x)) x) = 0
    rw [hx x hx0, map_zero]
  · intro y
    refine ⟨(F.map (qy y)) (xy y), ?_⟩
    calc
      _ = (G.map (qy y)) ((α.app (ky y)) (xy y)) :=
        congrArg (fun h : F.obj (ky y) ⟶ G.obj k => h (xy y)) (α.naturality (qy y))
      _ = (G.map (qy y)) ((G.map (py y)) y) := by rw [hy]
      _ = (G.map (py y ≫ qy y)) y := by rw [G.map_comp]; rfl
      _ = (G.map p) y := by rw [Subsingleton.elim (py y ≫ qy y) p]

/-- Submodule families closed under the differential. -/
public abbrev SubcomplexFamily {R : Type u} [Ring R] {ι : Type w} {c : ComplexShape ι}
    (M : HomologicalComplex (ModuleCat.{v} R) c) :=
  {P : ∀ i, Submodule R (M.X i) // ∀ i j x, x ∈ P i → (M.d i j) x ∈ P j}

/-- The subcomplex cut out by a submodule family closed under the differential. -/
public abbrev SubcomplexFamily.toComplex
    {R : Type u} [Ring R] {ι : Type w} {c : ComplexShape ι}
    {M : HomologicalComplex (ModuleCat.{v} R) c} (P : SubcomplexFamily M) :=
  complexOfSubmodules M P.1 P.2

/-- The inclusion of the subcomplex cut out by a submodule family. -/
public abbrev SubcomplexFamily.ι
    {R : Type u} [Ring R] {ι : Type w} {c : ComplexShape ι}
    {M : HomologicalComplex (ModuleCat.{v} R) c} (P : SubcomplexFamily M) :=
  complexOfSubmodulesι M P.1 P.2

/-- The map of complexes associated to an inclusion of submodule families. -/
public def SubcomplexFamily.map
    {R : Type u} [Ring R] {ι : Type w} {c : ComplexShape ι}
    {M : HomologicalComplex (ModuleCat.{v} R) c} {P Q : SubcomplexFamily M} (h : P ≤ Q) :
    P.toComplex ⟶ Q.toComplex where
  f i := ModuleCat.ofHom (Submodule.inclusion (h i))
  comm' _ _ _ := rfl

/-- The map between subcomplexes cut out by an inclusion of families is compatible with the
inclusions into the ambient complex. -/
public lemma SubcomplexFamily.map_ι
    {R : Type u} [Ring R] {ι : Type w} {c : ComplexShape ι}
    {M : HomologicalComplex (ModuleCat.{v} R) c} {P Q : SubcomplexFamily M} (h : P ≤ Q) :
    SubcomplexFamily.map h ≫ Q.ι = P.ι := rfl

private lemma SubcomplexFamily.map_id
    {R : Type u} [Ring R] {ι : Type w} {c : ComplexShape ι}
    {M : HomologicalComplex (ModuleCat.{v} R) c} (P : SubcomplexFamily M) :
    SubcomplexFamily.map (le_refl P) = 𝟙 P.toComplex := rfl

private lemma SubcomplexFamily.map_comp
    {R : Type u} [Ring R] {ι : Type w} {c : ComplexShape ι}
    {M : HomologicalComplex (ModuleCat.{v} R) c} {P Q S : SubcomplexFamily M}
    (h : P ≤ Q) (h' : Q ≤ S) :
    SubcomplexFamily.map (h.trans h') = SubcomplexFamily.map h ≫ SubcomplexFamily.map h' := rfl

/-- The degreewise image of a map of complexes is a subcomplex. -/
public def rangeFamily
    {R : Type u} [Ring R] {ι : Type w} {c : ComplexShape ι}
    {K M : HomologicalComplex (ModuleCat.{v} R) c} (φ : K ⟶ M) : SubcomplexFamily M :=
  ⟨fun i => LinearMap.range (φ.f i).hom, by
    rintro i j _ ⟨x, rfl⟩
    exact ⟨(K.d i j) x, (congrArg (fun g : K.X i ⟶ M.X j => g x) (φ.comm i j)).symm⟩⟩

/-- A map of complexes factors through its degreewise image. -/
public def toRangeFamily
    {R : Type u} [Ring R] {ι : Type w} {c : ComplexShape ι}
    {K M : HomologicalComplex (ModuleCat.{v} R) c} (φ : K ⟶ M) :
    K ⟶ (rangeFamily φ).toComplex where
  f i := ModuleCat.ofHom (φ.f i).hom.rangeRestrict
  comm' i j _ := by
    ext x
    exact Subtype.ext (congrArg (fun g : K.X i ⟶ M.X j => g x) (φ.comm i j))

/-- The factorization of a map of complexes through its degreewise image is a factorization. -/
public lemma toRangeFamily_ι
    {R : Type u} [Ring R] {ι : Type w} {c : ComplexShape ι}
    {K M : HomologicalComplex (ModuleCat.{v} R) c} (φ : K ⟶ M) :
    toRangeFamily φ ≫ (rangeFamily φ).ι = φ := rfl

/-- A monomorphism identifies its domain with the degreewise image. -/
public lemma toRangeFamily_isIso
    {R : Type u} [Ring R] {ι : Type w} {c : ComplexShape ι}
    {K M : HomologicalComplex (ModuleCat.{v} R) c} (φ : K ⟶ M) [Mono φ] :
    IsIso (toRangeFamily φ) := by
  have : Mono (toRangeFamily φ) := mono_of_mono_fac (toRangeFamily_ι φ)
  have : Epi (toRangeFamily φ) := HomologicalComplex.epi_of_epi_f _ (fun i =>
    (ModuleCat.epi_iff_surjective _).mpr (φ.f i).hom.surjective_rangeRestrict)
  exact isIso_of_mono_of_epi _

attribute [local instance] toRangeFamily_isIso complexOfSubmodulesι_mono

/-- A term of the degreewise image of a map of complexes is no larger than the corresponding term
of its source. -/
public lemma mk_rangeFamily_term_le
    {R : Type u} [Ring R] {ι : Type w} {c : ComplexShape ι}
    {K M : HomologicalComplex (ModuleCat.{v} R) c} (φ : K ⟶ M) (i : ι) :
    #((rangeFamily φ).toComplex.X i) ≤ #(K.X i) :=
  mk_le_of_surjective (φ.f i).hom.surjective_rangeRestrict

/-- An increasing collection of submodule families gives a diagram of subcomplexes. -/
public def familyDiagram
    {R : Type u} [Ring R] {J : Type v} [Preorder J]
    {M : CochainComplex (ModuleCat.{v} R) ℤ}
    (P : J → SubcomplexFamily M) (hP : Monotone P) :
    J ⥤ CochainComplex (ModuleCat.{v} R) ℤ where
  obj j := (P j).toComplex
  map g := SubcomplexFamily.map (hP (leOfHom g))

/-- The inclusions of an increasing collection of subcomplexes form a cocone. -/
public def familyCocone
    {R : Type u} [Ring R] {J : Type v} [Preorder J]
    {M : CochainComplex (ModuleCat.{v} R) ℤ}
    (P : J → SubcomplexFamily M) (hP : Monotone P) : Cocone (familyDiagram P hP) where
  pt := M
  ι := { app := fun j => (P j).ι }


/-- A directed collection of subcomplexes covering every degree has the ambient complex
as colimit. -/
public noncomputable def familyIsColimit
    {R : Type u} [Ring R] {J : Type v} [Preorder J] [IsFiltered J]
    {M : CochainComplex (ModuleCat.{v} R) ℤ}
    (P : J → SubcomplexFamily M) (hP : Monotone P)
    (hcover : ∀ i (x : M.X i), ∃ j, x ∈ (P j).1 i) :
    IsColimit (familyCocone P hP) := by
  apply HomologicalComplex.isColimitOfEval
  intro i
  have : PreservesColimitsOfShape J (forget (ModuleCat.{v} R)) := by
    change PreservesColimitsOfShape J
      (forget₂ (ModuleCat.{v} R) AddCommGrpCat.{v} ⋙ forget AddCommGrpCat.{v})
    infer_instance
  have : ReflectsColimitsOfShape J (forget (ModuleCat.{v} R)) :=
    reflectsColimitsOfShape_of_reflectsIsomorphisms
  apply isColimitOfReflects (forget (ModuleCat.{v} R))
  apply Types.FilteredColimit.isColimitOf'
  · intro x
    obtain ⟨j, hj⟩ := hcover i x
    exact ⟨j, ⟨x, hj⟩, rfl⟩
  · intro j x y hxy
    refine ⟨j, 𝟙 j, ?_⟩
    have : x = y := Subtype.ext hxy
    rw [this]

/-- **A map of filtered colimits which is stagewise injective and stagewise surjective.** Let
`φ : F ⟶ G` be a map of filtered diagrams of modules such that from every stage there is a step
annihilating the kernel of `φ` at that stage, and a step whose image lies in the image of `φ` at
its target. Then `φ` induces an isomorphism on colimits.

This is the direction in which the enlargement argument of Stacks 0GYZ consumes the two conditions
that Stacks 0GYI produces at each stage of an increasing chain of subcomplexes: there they are
read off a comparison map already known to be invertible, here they are what makes the comparison
map at the union invertible. Both hypotheses are stated on elements, which is the form the
categorical conditions `kernel.ι (φ.app j) ≫ F.map p = 0` and
`imageSubobject (G.map p) ≤ imageSubobject (φ.app j')` take on applying them to an element. -/
public lemma isIso_colimMap_of_stagewise
    {S : Type u} [Ring S] {J : Type w} [SmallCategory J] [IsFiltered J]
    {F G : J ⥤ ModuleCat.{max t w} S} (φ : F ⟶ G)
    [PreservesColimit F (forget (ModuleCat.{max t w} S))]
    [PreservesColimit G (forget (ModuleCat.{max t w} S))]
    [HasColimit F] [HasColimit G]
    (hker : ∀ j : J, ∃ (j' : J) (p : j ⟶ j'),
      ∀ x : F.obj j, (φ.app j) x = 0 → (F.map p) x = 0)
    (himg : ∀ j : J, ∃ (j' : J) (p : j ⟶ j'),
      ∀ y : G.obj j, ∃ x : F.obj j', (φ.app j') x = (G.map p) y) :
    IsIso (colimMap φ) := by
  have hmono : Mono (colimMap φ) := by
    rw [ModuleCat.mono_iff_injective]
    rw [injective_iff_map_eq_zero]
    intro z hz
    obtain ⟨j, x, rfl⟩ := Concrete.colimit_exists_rep F z
    rw [← ModuleCat.comp_apply, ι_colimMap, ModuleCat.comp_apply] at hz
    obtain ⟨j₁, i, hi⟩ := Concrete.colimit_rep_eq_zero (F := G) (j := j)
      (x := (φ.app j) x) (hx := hz)
    have hnat : (φ.app j₁) ((F.map i) x) = (G.map i) ((φ.app j) x) := by
      rw [← ModuleCat.comp_apply, ← ModuleCat.comp_apply, φ.naturality i]
    obtain ⟨j₂, p, hp⟩ := hker j₁
    have hzero : (F.map (i ≫ p)) x = 0 := by
      rw [F.map_comp, ModuleCat.comp_apply]
      exact hp _ (hnat.trans hi)
    calc colimit.ι F j x
        = colimit.ι F j₂ ((F.map (i ≫ p)) x) := by
          rw [← ModuleCat.comp_apply, colimit.w F (i ≫ p)]
      _ = 0 := by rw [hzero, map_zero]
  have hepi : Epi (colimMap φ) := by
    rw [ModuleCat.epi_iff_surjective]
    intro z
    obtain ⟨j, y, rfl⟩ := Concrete.colimit_exists_rep G z
    obtain ⟨j', p, hp⟩ := himg j
    obtain ⟨x, hx⟩ := hp y
    refine ⟨colimit.ι F j' x, ?_⟩
    rw [← ModuleCat.comp_apply, ι_colimMap, ModuleCat.comp_apply, hx, ← ModuleCat.comp_apply,
      colimit.w G p]
  exact isIso_of_mono_of_epi _

/-! ### The colimit of a sequence of subcomplexes -/

section Sequence

variable {R : Type u} [Ring R] {M : CochainComplex (ModuleCat.{v} R) ℤ}
  {X : ℕ → CochainComplex (ModuleCat.{v} R) ℤ}

/-- The degreewise images in `M` of a sequence of maps `X n ⟶ M`, as a family of subcomplexes of
`M` indexed by the copy of `ℕ` in the module universe.

The index type is lifted because the shape of a colimit in `ModuleCat.{v}` must itself live in
`Type v`: `ℕ` indexes the sequence, `ULift.{v} ℕ` indexes the colimit. -/
public def sequenceRangeFamily (f : ∀ n, X n ⟶ M) (n : ULift.{v, 0} ℕ) : SubcomplexFamily M :=
  rangeFamily (f n.down)

/-- A sequence of maps into `M` compatible with a sequence of maps between its sources has
increasing degreewise images. -/
public lemma sequenceRangeFamily_monotone {q : ∀ n, X n ⟶ X (n + 1)} (f : ∀ n, X n ⟶ M)
    (hq : ∀ n, q n ≫ f (n + 1) = f n) : Monotone (sequenceRangeFamily.{u, v} f) := by
  have h : Monotone (fun n : ℕ => rangeFamily (f n)) := by
    refine monotone_nat_of_le_succ (fun n i => ?_)
    have hf : (f n).f i = (q n).f i ≫ (f (n + 1)).f i := by
      rw [← HomologicalComplex.comp_f, hq n]
    rintro y ⟨x, rfl⟩
    exact ⟨((q n).f i) x, by rw [hf, ModuleCat.hom_comp]; rfl⟩
  exact fun _ _ hab => h hab

/-- **A sequence of subcomplexes exhausting a complex presents it as a colimit.** Let
`X_0^• ⟶ X_1^• ⟶ ⋯ ⟶ M^•` be a sequence of maps into `M^•`, compatible with the maps of the
sequence, whose degreewise images exhaust `M^•`. Then `M^•` is the colimit of the degreewise
images.

This is the form in which the enlargement argument of Stacks 0GYZ produces its union: the stages
come as a sequence with an exhaustion statement, which is what
`Stacks.ModulesOnACategory.QuasiCoherentEquivalence.exists_union_of_chain` returns, and what is
needed of the union is that it is the filtered colimit of the stages, so that the cohomology of
its derived base change is computed by `derivedBaseChangeHomology_preservesFilteredColimits_ulift`.
No monomorphy of the maps is required: the images are taken, and for a monomorphism
`toRangeFamily_isIso` identifies the image with the source. -/
public noncomputable def isColimit_familyCocone_sequence {q : ∀ n, X n ⟶ X (n + 1)}
    (f : ∀ n, X n ⟶ M) (hq : ∀ n, q n ≫ f (n + 1) = f n)
    (hexh : ∀ (i : ℤ) (x : M.X i), ∃ (n : ℕ) (y : (X n).X i), ((f n).f i) y = x) :
    IsColimit (familyCocone (sequenceRangeFamily.{u, v} f)
      (sequenceRangeFamily_monotone.{u, v} (q := q) f hq)) :=
  familyIsColimit _ _ (fun i x => by
    obtain ⟨n, y, hy⟩ := hexh i x
    exact ⟨ULift.up n, y, hy⟩)

end Sequence

/-- Compatibility of maps descends to their degreewise images. -/
public lemma rangeFamily_compatible
    {A : Type u} {B : Type v} [Ring A] [Ring B]
    {M M₁ : CochainComplex (ModuleCat.{w} A) ℤ}
    {N N₁ : CochainComplex (ModuleCat.{w} B) ℤ}
    (E : CochainComplex (ModuleCat.{w} A) ℤ ⥤ CochainComplex (ModuleCat.{w} B) ℤ)
    (m : M₁ ⟶ M) (n : N₁ ⟶ N) [Mono m] [Mono n]
    (b : E.obj M ⟶ N) (b₁ : E.obj M₁ ⟶ N₁) (hb : E.map m ≫ b = b₁ ≫ n) :
    ∃ b' : E.obj (rangeFamily m).toComplex ⟶ (rangeFamily n).toComplex,
      E.map (rangeFamily m).ι ≫ b = b' ≫ (rangeFamily n).ι := by
  refine ⟨E.map (inv (toRangeFamily m)) ≫ b₁ ≫ toRangeFamily n, ?_⟩
  have hm : inv (toRangeFamily m) ≫ m = (rangeFamily m).ι := by
    rw [← cancel_epi (toRangeFamily m), ← Category.assoc, IsIso.hom_inv_id,
      Category.id_comp, toRangeFamily_ι]
  rw [Category.assoc, Category.assoc, toRangeFamily_ι, ← hb, ← Category.assoc,
    ← E.map_comp, hm]

/-- **A map of filtered colimits which is stagewise injective and stagewise surjective, read on
arbitrary colimit cocones.** This is the converse direction of
`exists_stage_all_degrees_killing_kernel_and_covering_image`: there a map already known to be
invertible produces the two stagewise conditions, here the two stagewise conditions produce the
invertibility.

The colimits are presented by arbitrary colimit cocones rather than by `colimit`, because that is
how the union of an increasing chain of subcomplexes arrives: through `familyIsColimit` and the
preservation of filtered colimits by derived base change followed by cohomology. The two stagewise
conditions are elementwise, as in `isIso_colimMap_of_stagewise`; the categorical form Stacks 0GYI
returns them in is brought to this one by `forall_of_kernel_comp_eq_zero` and
`forall_exists_of_imageSubobject_le`. -/
public lemma isIso_of_stagewise_kernel_and_image
    {R : Type u} [Ring R] {J : Type v} [SmallCategory J] [IsFiltered J]
    {F G : J ⥤ ModuleCat.{v} R} (φ : F ⟶ G)
    {cF : Cocone F} {cG : Cocone G} (hcF : IsColimit cF) (hcG : IsColimit cG)
    (g : cF.pt ⟶ cG.pt) (hg : ∀ j, cF.ι.app j ≫ g = φ.app j ≫ cG.ι.app j)
    (hker : ∀ j : J, ∃ (j' : J) (p : j ⟶ j'),
      ∀ x : F.obj j, (φ.app j) x = 0 → (F.map p) x = 0)
    (himg : ∀ j : J, ∃ (j' : J) (p : j ⟶ j'),
      ∀ y : G.obj j, ∃ x : F.obj j', (φ.app j') x = (G.map p) y) :
    IsIso g := by
  have : HasColimit F := ⟨⟨⟨cF, hcF⟩⟩⟩
  have : HasColimit G := ⟨⟨⟨cG, hcG⟩⟩⟩
  have : IsIso (colimMap φ) := isIso_colimMap_of_stagewise.{u, v, v} φ hker himg
  let eF : colimit F ≅ cF.pt := (colimit.isColimit F).coconePointUniqueUpToIso hcF
  let eG : colimit G ≅ cG.pt := (colimit.isColimit G).coconePointUniqueUpToIso hcG
  have hFi : ∀ j, colimit.ι F j ≫ eF.hom = cF.ι.app j := fun j =>
    IsColimit.comp_coconePointUniqueUpToIso_hom (colimit.isColimit F) hcF j
  have hGi : ∀ j, colimit.ι G j ≫ eG.hom = cG.ι.app j := fun j =>
    IsColimit.comp_coconePointUniqueUpToIso_hom (colimit.isColimit G) hcG j
  have hsq : eF.hom ≫ g = colimMap φ ≫ eG.hom := by
    refine colimit.hom_ext (fun j => ?_)
    rw [← Category.assoc, ← Category.assoc, hFi j, ι_colimMap, Category.assoc, hGi j, hg j]
  have hgeq : g = eF.inv ≫ colimMap φ ≫ eG.hom := by
    rw [← hsq, Iso.inv_hom_id_assoc]
  rw [hgeq]
  infer_instance

/-- Transporting a step of a chain along identifications of the stages with their images. -/
private lemma map_eq_inv_comp_of_comp_eq
    {R : Type u} [Ring R] {M X Y : CochainComplex (ModuleCat.{t} R) ℤ}
    {f : X ⟶ M} {g : Y ⟶ M} (h : rangeFamily f ≤ rangeFamily g)
    (q : X ⟶ Y) (hq : q ≫ g = f) (eX : X ≅ (rangeFamily f).toComplex)
    (eY : Y ≅ (rangeFamily g).toComplex) (hX : eX.hom ≫ (rangeFamily f).ι = f)
    (hY : eY.hom ≫ (rangeFamily g).ι = g) :
    SubcomplexFamily.map h = eX.inv ≫ q ≫ eY.hom := by
  rw [← cancel_mono (rangeFamily g).ι, SubcomplexFamily.map_ι, Category.assoc, Category.assoc, hY,
    hq]
  exact (Iso.eq_inv_comp eX).mpr hX

/-! ### Invertibility of a comparison map at the union of a chain of subcomplexes -/

/-- **Comparison maps on an increasing family of subcomplexes are automatically natural.** If each
member of an increasing family of subcomplexes of `M^•` carries a map to the corresponding member
of an increasing family of subcomplexes of `N^•`, compatibly with a fixed map `E(M^•) ⟶ N^•`, then
those maps commute with the inclusions of the families: the inclusion of a subcomplex is a
monomorphism, so the identity follows by cancelling it. -/
private lemma comparison_naturality_of_ι
    {A : Type u} {B : Type v} [Ring A] [Ring B]
    {M : CochainComplex (ModuleCat.{t} A) ℤ} {N : CochainComplex (ModuleCat.{t} B) ℤ}
    (E : CochainComplex (ModuleCat.{t} A) ℤ ⥤ CochainComplex (ModuleCat.{t} B) ℤ)
    (b : E.obj M ⟶ N)
    {J : Type t} [Preorder J] {P : J → SubcomplexFamily M} {Q : J → SubcomplexFamily N}
    (hP : Monotone P) (hQ : Monotone Q)
    (c : ∀ j, E.obj (P j).toComplex ⟶ (Q j).toComplex)
    (hc : ∀ j, E.map (P j).ι ≫ b = c j ≫ (Q j).ι)
    {j j' : J} (hjj : j ≤ j') :
    E.map (SubcomplexFamily.map (hP hjj)) ≫ c j' = c j ≫ SubcomplexFamily.map (hQ hjj) := by
  rw [← cancel_mono (Q j').ι, Category.assoc, Category.assoc, SubcomplexFamily.map_ι,
    ← hc j, ← hc j', ← Category.assoc, ← E.map_comp, SubcomplexFamily.map_ι]

/-- The stagewise kernel condition is invariant under conjugating both maps by isomorphisms. This
is why that condition is carried in elementwise form: the categorical statement
`kernel.ι φ ≫ ψ = 0` does not transport along an isomorphism of the modules involved without
rebuilding the kernel, while the elementwise one transports by moving the element. -/
private lemma stagewise_kernel_of_conj {R : Type u} [Ring R] {X Y Z X' Y' Z' : ModuleCat.{t} R}
    {φ : X ⟶ Y} {ψ : X ⟶ Z} {φ' : X' ⟶ Y'} {ψ' : X' ⟶ Z'}
    (uX : X' ≅ X) (uY : Y ≅ Y') (uZ : Z ≅ Z')
    (hφ : φ' = uX.hom ≫ φ ≫ uY.hom) (hψ : ψ' = uX.hom ≫ ψ ≫ uZ.hom)
    (h : ∀ x, φ x = 0 → ψ x = 0) (x' : X') (hx' : φ' x' = 0) : ψ' x' = 0 := by
  have hz : φ (uX.hom x') = 0 := by
    refine (ModuleCat.mono_iff_injective uY.hom).mp inferInstance ?_
    rw [map_zero, ← ModuleCat.comp_apply, ← ModuleCat.comp_apply, ← hφ]
    exact hx'
  rw [hψ, ModuleCat.comp_apply, ModuleCat.comp_apply, h _ hz, map_zero]

/-- The stagewise image condition is invariant under conjugating the three maps by isomorphisms,
for the same reason as `stagewise_kernel_of_conj`. -/
private lemma stagewise_image_of_conj {R : Type u} [Ring R] {X Y W X' Y' W' : ModuleCat.{t} R}
    {c : X ⟶ Y} {d : W ⟶ Y} {c' : X' ⟶ Y'} {d' : W' ⟶ Y'}
    (uX : X' ≅ X) (uW : W' ≅ W) (uY : Y ≅ Y')
    (hc : c' = uX.hom ≫ c ≫ uY.hom) (hd : d' = uW.hom ≫ d ≫ uY.hom)
    (h : ∀ w, ∃ x, c x = d w) (w' : W') : ∃ x', c' x' = d' w' := by
  obtain ⟨x, hx⟩ := h (uW.hom w')
  refine ⟨uX.inv x, ?_⟩
  rw [hc, hd, ModuleCat.comp_apply, ModuleCat.comp_apply, ModuleCat.comp_apply,
    ModuleCat.comp_apply, ← ModuleCat.comp_apply uX.inv uX.hom, Iso.inv_hom_id,
    ModuleCat.id_apply, hx]

/-- **Invertibility of a comparison map at the union of an increasing chain of subcomplexes.**
Let `E` be a functor on complexes of modules with `(T, α)` a left derived model of its
localization, let `b : E(M^•) ⟶ N^•`, and let `M^•` and `N^•` be exhausted by increasing chains of
subcomplexes `M_n^•` and `N_n^•` carrying compatible maps `b_n : E(M_n^•) ⟶ N_n^•`. If at every
stage the kernel of the comparison on cohomology dies at the next stage, and the image of the next
step is already covered by the comparison there, then the comparison at `M^•` and `N^•` themselves
is an isomorphism.

This is the direction in which the enlargement argument of Stacks 0GYZ consumes Stacks 0GYI: the
enlargement produces the two conditions at every stage of a countable chain, and what is wanted is
the base-change condition at the union. The two colimits are taken over the diagram of the
degreewise *images* of the stages — the shape in which `isColimit_familyCocone_sequence` presents
the union — and each stage is identified with its image by `toRangeFamily_isIso`, the comparison
map being transported by conjugation along that identification.

The index type of the colimit is `ULift ℕ` rather than `ℕ`, as it must be: a colimit of modules in
`ModuleCat.{t}` has its shape in `Type t`. Preservation of those colimits by `T` followed by
cohomology is a hypothesis, because it is the only place where the nature of `E` would enter;
`derivedBaseChangeHomology_preservesFilteredColimits_ulift` supplies it for derived base change. -/
public theorem isIso_comparison_of_stagewise_union
    {A : Type u} {B : Type v} [Ring A] [CommRing B]
    (E : CochainComplex (ModuleCat.{max u v w} A) ℤ ⥤
      CochainComplex (ModuleCat.{max u v w} B) ℤ)
    (T : DerivedCategory (ModuleCat.{max u v w} A) ⥤ DerivedCategory (ModuleCat.{max u v w} B))
    (α : DerivedCategory.Q ⋙ T ⟶ E ⋙ DerivedCategory.Q)
    (hpres : ∀ i : ℤ, PreservesColimitsOfShape (ULift.{max u v w, 0} ℕ)
      (DerivedCategory.Q ⋙ T ⋙ DerivedCategory.homologyFunctor (ModuleCat.{max u v w} B) i))
    {M : CochainComplex (ModuleCat.{max u v w} A) ℤ}
    {N : CochainComplex (ModuleCat.{max u v w} B) ℤ} (b : E.obj M ⟶ N)
    (Ms : ℕ → CochainComplex (ModuleCat.{max u v w} A) ℤ)
    (Ns : ℕ → CochainComplex (ModuleCat.{max u v w} B) ℤ)
    (cM : ∀ n, Ms n ⟶ M) (cN : ∀ n, Ns n ⟶ N)
    (pM : ∀ n, Ms n ⟶ Ms (n + 1)) (pN : ∀ n, Ns n ⟶ Ns (n + 1))
    (bs : ∀ n, E.obj (Ms n) ⟶ Ns n)
    (hmM : ∀ n, Mono (cM n)) (hmN : ∀ n, Mono (cN n))
    (hpM : ∀ n, pM n ≫ cM (n + 1) = cM n) (hpN : ∀ n, pN n ≫ cN (n + 1) = cN n)
    (hexhM : ∀ (i : ℤ) (x : M.X i), ∃ (n : ℕ) (y : (Ms n).X i), ((cM n).f i) y = x)
    (hexhN : ∀ (i : ℤ) (x : N.X i), ∃ (n : ℕ) (y : (Ns n).X i), ((cN n).f i) y = x)
    (hbs : ∀ n, E.map (cM n) ≫ b = bs n ≫ cN n)
    (hker : ∀ (n : ℕ) (i : ℤ)
      (x : (DerivedCategory.homologyFunctor (ModuleCat.{max u v w} B) i).obj
        (T.obj (DerivedCategory.Q.obj (Ms n)))),
      ((DerivedCategory.homologyFunctor (ModuleCat.{max u v w} B) i).map
          (α.app (Ms n) ≫ DerivedCategory.Q.map (bs n))) x = 0 →
        ((DerivedCategory.homologyFunctor (ModuleCat.{max u v w} B) i).map
          (T.map (DerivedCategory.Q.map (pM n)))) x = 0)
    (himg : ∀ (n : ℕ) (i : ℤ)
      (y : (DerivedCategory.homologyFunctor (ModuleCat.{max u v w} B) i).obj
        (DerivedCategory.Q.obj (Ns n))),
      ∃ x : (DerivedCategory.homologyFunctor (ModuleCat.{max u v w} B) i).obj
        (T.obj (DerivedCategory.Q.obj (Ms (n + 1)))),
        ((DerivedCategory.homologyFunctor (ModuleCat.{max u v w} B) i).map
            (α.app (Ms (n + 1)) ≫ DerivedCategory.Q.map (bs (n + 1)))) x =
          ((DerivedCategory.homologyFunctor (ModuleCat.{max u v w} B) i).map
            (DerivedCategory.Q.map (pN n))) y) :
    IsIso (α.app M ≫ DerivedCategory.Q.map b) := by
  classical
  let Hf (i : ℤ) := DerivedCategory.homologyFunctor (ModuleCat.{max u v w} B) i
  -- the diagram of the degreewise images of the stages, and its colimit
  let PM := sequenceRangeFamily.{u, max u v w} cM
  let PN := sequenceRangeFamily.{v, max u v w} cN
  have hPM : Monotone PM :=
    sequenceRangeFamily_monotone.{u, max u v w} (q := pM) cM hpM
  have hPN : Monotone PN :=
    sequenceRangeFamily_monotone.{v, max u v w} (q := pN) cN hpN
  have hcocM : IsColimit (familyCocone PM hPM) :=
    isColimit_familyCocone_sequence.{u, max u v w} (q := pM) cM hpM hexhM
  have hcocN : IsColimit (familyCocone PN hPN) :=
    isColimit_familyCocone_sequence.{v, max u v w} (q := pN) cN hpN hexhN
  -- each stage, identified with its degreewise image; the instance is passed positionally,
  -- the ascribed target type being the one in which the colimit diagram is phrased
  let eM : ∀ n : ℕ, Ms n ≅ (PM (ULift.up n)).toComplex := fun n =>
    have := hmM n
    @asIso _ _ _ _ (toRangeFamily (cM n)) (toRangeFamily_isIso (cM n))
  let eN : ∀ n : ℕ, Ns n ≅ (PN (ULift.up n)).toComplex := fun n =>
    have := hmN n
    @asIso _ _ _ _ (toRangeFamily (cN n)) (toRangeFamily_isIso (cN n))
  have hεM : ∀ n : ℕ, (eM n).hom ≫ (PM (ULift.up n)).ι = cM n := fun n => toRangeFamily_ι (cM n)
  have hεN : ∀ n : ℕ, (eN n).hom ≫ (PN (ULift.up n)).ι = cN n := fun n => toRangeFamily_ι (cN n)
  have hιM : ∀ n : ℕ, (PM (ULift.up n)).ι = (eM n).inv ≫ cM n := fun n => by
    rw [← hεM n, Iso.inv_hom_id_assoc]
  -- the comparison maps, conjugated to the images
  let bi : ∀ j : ULift.{max u v w, 0} ℕ, E.obj (PM j).toComplex ⟶ (PN j).toComplex := fun j =>
    E.map (eM j.down).inv ≫ bs j.down ≫ (eN j.down).hom
  have hbi : ∀ j, E.map (PM j).ι ≫ b = bi j ≫ (PN j).ι := by
    intro j
    obtain ⟨n⟩ := j
    rw [hιM n, E.map_comp, Category.assoc, hbs n]
    change E.map (eM n).inv ≫ bs n ≫ cN n =
      (E.map (eM n).inv ≫ bs n ≫ (eN n).hom) ≫ (PN (ULift.up n)).ι
    rw [Category.assoc, Category.assoc, hεN n]
  -- the steps of the chain, conjugated to the images
  have hsucc : ∀ n : ℕ, (ULift.up n : ULift.{max u v w, 0} ℕ) ≤ ULift.up (n + 1) :=
    fun n => Nat.le_succ n
  have hstepM : ∀ (n : ℕ) (hle : (ULift.up n : ULift.{max u v w, 0} ℕ) ≤ ULift.up (n + 1)),
      SubcomplexFamily.map (hPM hle) = (eM n).inv ≫ pM n ≫ (eM (n + 1)).hom := by
    intro n hle
    exact map_eq_inv_comp_of_comp_eq _ _ (hpM n) _ _ (hεM n) (hεM (n + 1))
  have hstepN : ∀ (n : ℕ) (hle : (ULift.up n : ULift.{max u v w, 0} ℕ) ≤ ULift.up (n + 1)),
      SubcomplexFamily.map (hPN hle) = (eN n).inv ≫ pN n ≫ (eN (n + 1)).hom := by
    intro n hle
    exact map_eq_inv_comp_of_comp_eq _ _ (hpN n) _ _ (hεN n) (hεN (n + 1))
  rw [DerivedCategory.isIso_iff]
  intro i
  -- the natural transformation of diagrams of cohomology modules
  let φ : familyDiagram PM hPM ⋙ DerivedCategory.Q ⋙ T ⋙ Hf i ⟶
      familyDiagram PN hPN ⋙ DerivedCategory.Q ⋙ Hf i :=
    { app := fun j => (Hf i).map (α.app (PM j).toComplex ≫ DerivedCategory.Q.map (bi j))
      naturality := by
        intro j k p
        have h := congrArg (Hf i).map (comparison_square α
          (SubcomplexFamily.map (hPM (leOfHom p))) (SubcomplexFamily.map (hPN (leOfHom p)))
          (bi j) (bi k) (comparison_naturality_of_ι E b hPM hPN bi hbi (leOfHom p)))
        rw [(Hf i).map_comp
              ((DerivedCategory.Q ⋙ T).map (SubcomplexFamily.map (hPM (leOfHom p))))
              (α.app (PM k).toComplex ≫ DerivedCategory.Q.map (bi k)),
            (Hf i).map_comp (α.app (PM j).toComplex ≫ DerivedCategory.Q.map (bi j))
              (DerivedCategory.Q.map (SubcomplexFamily.map (hPN (leOfHom p))))] at h
        exact h }
  have hcF : IsColimit ((DerivedCategory.Q ⋙ T ⋙ Hf i).mapCocone (familyCocone PM hPM)) := by
    have := hpres i
    exact isColimitOfPreserves _ hcocM
  have hcG : IsColimit ((DerivedCategory.Q ⋙ Hf i).mapCocone (familyCocone PN hPN)) := by
    have := homology_preservesFilteredColimits.{v, max u w} (R := B)
      (J := ULift.{max u v w, 0} ℕ) i
    have : PreservesColimitsOfShape (ULift.{max u v w, 0} ℕ) (DerivedCategory.Q ⋙ Hf i) :=
      preservesColimitsOfShape_of_natIso
        (DerivedCategory.homologyFunctorFactors (ModuleCat.{max u v w} B) i).symm
    exact isColimitOfPreserves _ hcocN
  have hg : ∀ j, ((DerivedCategory.Q ⋙ T ⋙ Hf i).mapCocone (familyCocone PM hPM)).ι.app j ≫
      (Hf i).map (α.app M ≫ DerivedCategory.Q.map b) =
        φ.app j ≫ ((DerivedCategory.Q ⋙ Hf i).mapCocone (familyCocone PN hPN)).ι.app j := by
    intro j
    have h := congrArg (Hf i).map (comparison_square α (PM j).ι (PN j).ι (bi j) b (hbi j))
    rw [(Hf i).map_comp ((DerivedCategory.Q ⋙ T).map (PM j).ι)
          (α.app M ≫ DerivedCategory.Q.map b),
        (Hf i).map_comp (α.app (PM j).toComplex ≫ DerivedCategory.Q.map (bi j))
          (DerivedCategory.Q.map (PN j).ι)] at h
    exact h
  -- the identifications of a stage with its image, read on cohomology
  let UM : ∀ n : ℕ, (familyDiagram PM hPM ⋙ DerivedCategory.Q ⋙ T ⋙ Hf i).obj (ULift.up n) ≅
      (Hf i).obj (T.obj (DerivedCategory.Q.obj (Ms n))) :=
    fun n => ((DerivedCategory.Q ⋙ T ⋙ Hf i).mapIso (eM n)).symm
  let VN : ∀ n : ℕ, (Hf i).obj (DerivedCategory.Q.obj (Ns n)) ≅
      (familyDiagram PN hPN ⋙ DerivedCategory.Q ⋙ Hf i).obj (ULift.up n) :=
    fun n => (DerivedCategory.Q ⋙ Hf i).mapIso (eN n)
  have hφ : ∀ n : ℕ, φ.app (ULift.up n) =
      (UM n).hom ≫ (Hf i).map (α.app (Ms n) ≫ DerivedCategory.Q.map (bs n)) ≫ (VN n).hom := by
    intro n
    have hcompat : E.map (eM n).inv ≫ bs n = bi (ULift.up n) ≫ (eN n).inv := by
      change E.map (eM n).inv ≫ bs n = (E.map (eM n).inv ≫ bs n ≫ (eN n).hom) ≫ (eN n).inv
      rw [Category.assoc, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    have h2 := congrArg (Hf i).map
      (comparison_square α (eM n).inv (eN n).inv (bi (ULift.up n)) (bs n) hcompat)
    rw [(Hf i).map_comp ((DerivedCategory.Q ⋙ T).map (eM n).inv)
          (α.app (Ms n) ≫ DerivedCategory.Q.map (bs n)),
        (Hf i).map_comp
          (α.app (PM (ULift.up n)).toComplex ≫ DerivedCategory.Q.map (bi (ULift.up n)))
          (DerivedCategory.Q.map (eN n).inv)] at h2
    have hA : φ.app (ULift.up n) ≫ (VN n).inv =
        (UM n).hom ≫ (Hf i).map (α.app (Ms n) ≫ DerivedCategory.Q.map (bs n)) := h2.symm
    rw [← Category.assoc, ← hA, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have hmapM : ∀ n : ℕ,
      (familyDiagram PM hPM ⋙ DerivedCategory.Q ⋙ T ⋙ Hf i).map (homOfLE (hsucc n)) =
        (UM n).hom ≫ (Hf i).map (T.map (DerivedCategory.Q.map (pM n))) ≫ (UM (n + 1)).inv := by
    intro n
    change (DerivedCategory.Q ⋙ T ⋙ Hf i).map
      (SubcomplexFamily.map (hPM (leOfHom (homOfLE (hsucc n))))) = _
    rw [hstepM n (hsucc n), Functor.map_comp, Functor.map_comp]
    rfl
  have hmapN : ∀ n : ℕ,
      (familyDiagram PN hPN ⋙ DerivedCategory.Q ⋙ Hf i).map (homOfLE (hsucc n)) =
        (VN n).inv ≫ (Hf i).map (DerivedCategory.Q.map (pN n)) ≫ (VN (n + 1)).hom := by
    intro n
    change (DerivedCategory.Q ⋙ Hf i).map
      (SubcomplexFamily.map (hPN (leOfHom (homOfLE (hsucc n))))) = _
    rw [hstepN n (hsucc n), Functor.map_comp, Functor.map_comp]
    rfl
  refine isIso_of_stagewise_kernel_and_image.{v, max u v w} φ hcF hcG _ hg ?_ ?_
  · intro j
    obtain ⟨n⟩ := j
    exact ⟨ULift.up (n + 1), homOfLE (hsucc n),
      stagewise_kernel_of_conj (UM n) (VN n) (UM (n + 1)).symm (hφ n) (hmapM n) (hker n i)⟩
  · intro j
    obtain ⟨n⟩ := j
    exact ⟨ULift.up (n + 1), homOfLE (hsucc n),
      stagewise_image_of_conj (UM (n + 1)) (VN n).symm (VN (n + 1)) (hφ (n + 1)) (hmapN n)
        (himg n i)⟩

end Stacks.SubcomplexEnlargement

end
