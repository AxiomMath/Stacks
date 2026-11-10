module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Submodule
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.SetTheory.Cardinal.Finsupp
public import Mathlib.SetTheory.Cardinal.Order
import StacksCore.Tactic.StacksAttribute

/-!
# Small subcomplexes containing prescribed sections

Let `C` be a category with the chaotic topology and `R` a sheaf of rings on it. Stacks 0GYX
produces a cardinal `κ`, depending only on `C` and `R`, such that every family of prescribed
sections `Ω^i_U ⊆ F^i(U)` of a complex `F^•` of `R`-modules is contained in a subcomplex
`H^• ⊆ F^•` whose size is at most `max κ |⋃ Ω^i_U|`.

The subcomplex is the objectwise span of the prescribed sections together with their
differentials, after restriction along every morphism of `C`. Restriction-stability makes it
a subpresheaf, closure under the differential makes the family a subcomplex, and the span
bound for a module over a ring bounds its size.

## Main definitions

* `Stacks.ModulesOnACategory.complexSectionSize`: the cardinality of all sections, in all
  degrees and over all objects, of a complex of sheaves of modules.
* `Stacks.ModulesOnACategory.sectionFamilySize`: the cardinality of an indexed family of
  prescribed sections.

## Main results

* `Stacks.ModulesOnACategory.exists_subcomplex_containing_sections_of_size_le`: the uniformly
  bounded subcomplex containing every prescribed section.

## Implementation notes

The chaotic topology is the bottom Grothendieck topology, for which the sheaf condition is
automatic — this is what makes the objectwise span a sheaf of modules without any
sheafification. A subcomplex is represented by a monomorphism of cochain complexes, and
containment of a prescribed section is stated by exhibiting a preimage under the relevant
component of that monomorphism. The coproducts defining the two cardinalities are dependent
sums of types, whose cardinals are lifted into a single universe also containing the morphisms
of the site and the rings of sections.

## References

* [Stacks Project, Tag 0GYX](https://stacks.math.columbia.edu/tag/0GYX)
-/

@[expose] public section

open CategoryTheory Opposite

universe v m r u

namespace Stacks.ModulesOnACategory

variable {C : Type u} [Category.{v} C]

private lemma finsupp_cardinal_le_max
    {α : Type u} {β : Type v} [Zero β] :
    Cardinal.mk (α →₀ β) ≤
      max Cardinal.aleph0
        (max (Cardinal.lift.{v} (Cardinal.mk α))
          (Cardinal.lift.{u} (Cardinal.mk β))) := by
  classical
  by_cases hα : Infinite α
  · by_cases hβ : Subsingleton β
    · exact le_max_of_le_left Cardinal.mk_le_aleph0
    · have : Nontrivial β := not_subsingleton_iff_nontrivial.mp hβ
      rw [Cardinal.mk_finsupp_lift_of_infinite]
      exact le_max_right _ _
  · by_cases hβ : Infinite β
    · by_cases hαne : Nonempty α
      · rw [Cardinal.mk_finsupp_lift_of_infinite']
        exact le_max_right _ _
      · have : IsEmpty α := not_nonempty_iff.mp hαne
        exact le_max_of_le_left Cardinal.mk_le_aleph0
    · have : Finite α := Finite.of_not_infinite hα
      have : Finite β := Finite.of_not_infinite hβ
      have : Fintype α := Fintype.ofFinite α
      have : Fintype β := Fintype.ofFinite β
      have : Fintype (α →₀ β) := Fintype.ofEquiv (α → β) Finsupp.equivFunOnFinite.symm
      exact le_max_of_le_left Cardinal.mk_le_aleph0

/-- If every element of a set `S` is a value of `v`, then `S` embeds into the domain of `v`. -/
private lemma embedding_of_forall_exists {α β : Type*} (v : α → β) (S : Set β)
    (h : ∀ x ∈ S, ∃ a, v a = x) : Nonempty (S ↪ α) :=
  ⟨⟨fun x => (h x.1 x.2).choose, fun x y hxy => Subtype.ext <|
    (h x.1 x.2).choose_spec.symm.trans <| (congrArg v hxy).trans (h y.1 y.2).choose_spec⟩⟩

private lemma span_cardinal_le_max
    {A : Type r} {M : Type m} [Semiring A] [AddCommMonoid M] [Module A M]
    (S : Set M) :
    Cardinal.lift.{max (max m r) (max r m)}
        (Cardinal.mk {x : M // x ∈ Submodule.span A S}) ≤
      Cardinal.lift.{max (max m r) (max r m)}
        (max Cardinal.aleph0
          (max (Cardinal.lift.{r} (Cardinal.mk {x : M // x ∈ S}))
            (Cardinal.lift.{m} (Cardinal.mk A)))) := by
  classical
  exact (Cardinal.lift_mk_le.2 (embedding_of_forall_exists
    (Finsupp.linearCombination A (Subtype.val : S → M)) _
    fun _ hx => (Finsupp.mem_span_iff_linearCombination A S _).mp hx)).trans
    ((Cardinal.lift_le).2 (finsupp_cardinal_le_max (α := {x : M // x ∈ S}) (β := A)))

/-- The generators of the subcomplex over `U` in degree `i`: the restrictions to `U` of the
prescribed sections of degree `i` and of the differentials of prescribed sections. -/
private def restrictedGenerators
    (R : Sheaf (⊥ : GrothendieckTopology C) RingCat.{r})
    (F : CochainComplex (SheafOfModules.{m} R) ℤ)
    (Omega : ∀ (i : ℤ) (U : C), Set ((F.X i).val.obj (op U)))
    (i : ℤ) (U : Cᵒᵖ) : Set ((F.X i).val.obj U) :=
  {x | ∃ (V : C) (f : op V ⟶ U) (y : (F.X i).val.obj (op V)),
    (y ∈ Omega i V ∨
      ∃ (j : ℤ) (z : (F.X j).val.obj (op V)),
        z ∈ Omega j V ∧ (F.d j i).val.app (op V) z = y) ∧
      (F.X i).val.map f y = x}

private abbrev omegaTotal
    (R : Sheaf (⊥ : GrothendieckTopology C) RingCat.{r})
    (F : CochainComplex (SheafOfModules.{m} R) ℤ)
    (Omega : ∀ (i : ℤ) (U : C), Set ((F.X i).val.obj (op U))) :=
  Σ i : ℤ, Σ U : C, {x // x ∈ Omega i U}

private abbrev siteArrowTotal (C : Type u) [Category.{v} C] :=
  Σ V : C, Σ U : C, (op V ⟶ op U)

private abbrev restrictedGeneratorData
    (R : Sheaf (⊥ : GrothendieckTopology C) RingCat.{r})
    (F : CochainComplex (SheafOfModules.{m} R) ℤ)
    (Omega : ∀ (i : ℤ) (U : C), Set ((F.X i).val.obj (op U)))
    (i : ℤ) (U : Cᵒᵖ) :=
  (Σ V : C, {y // y ∈ Omega i V} × (op V ⟶ U)) ⊕
  (Σ j : ℤ, Σ V : C, {z // z ∈ Omega j V} × (op V ⟶ U))

private noncomputable def restrictedGeneratorValue
    (R : Sheaf (⊥ : GrothendieckTopology C) RingCat.{r})
    (F : CochainComplex (SheafOfModules.{m} R) ℤ)
    (Omega : ∀ (i : ℤ) (U : C), Set ((F.X i).val.obj (op U)))
    (i : ℤ) (U : Cᵒᵖ) : restrictedGeneratorData R F Omega i U →
      (F.X i).val.obj U
  | .inl ⟨_V, y, f⟩ => (F.X i).val.map f y.1
  | .inr ⟨j, V, z, f⟩ =>
      (F.X i).val.map f ((F.d j i).val.app (op V) z.1)

private lemma restrictedGenerators_cardinal_le
    (R : Sheaf (⊥ : GrothendieckTopology C) RingCat.{r})
    (F : CochainComplex (SheafOfModules.{m} R) ℤ)
    (Omega : ∀ (i : ℤ) (U : C), Set ((F.X i).val.obj (op U)))
    (i : ℤ) (U : Cᵒᵖ) :
    Cardinal.lift.{max u v m r}
        (Cardinal.mk {x // x ∈ restrictedGenerators R F Omega i U}) ≤
      Cardinal.lift.{max u v m r}
        (Cardinal.mk (restrictedGeneratorData R F Omega i U)) := by
  classical
  refine Cardinal.lift_mk_le.{max u v m r, m, max u v m}.2 (embedding_of_forall_exists
    (restrictedGeneratorValue R F Omega i U) _ ?_)
  rintro x ⟨V, f, y, hy | ⟨j, z, hz, hzy⟩, hxy⟩
  · exact ⟨.inl ⟨V, ⟨y, hy⟩, f⟩, hxy⟩
  · exact ⟨.inr ⟨j, V, ⟨z, hz⟩, f⟩, by simp [restrictedGeneratorValue, hzy, hxy]⟩

private def restrictedGeneratorDataEmbedding
    (R : Sheaf (⊥ : GrothendieckTopology C) RingCat.{r})
    (F : CochainComplex (SheafOfModules.{m} R) ℤ)
    (Omega : ∀ (i : ℤ) (U : C), Set ((F.X i).val.obj (op U)))
    (i : ℤ) (U : Cᵒᵖ) :
    restrictedGeneratorData R F Omega i U ↪
      Bool × (omegaTotal R F Omega × siteArrowTotal C) where
  toFun
    | .inl ⟨V, y, f⟩ =>
        (true, (⟨i, V, y⟩, ⟨V, U.unop, f⟩))
    | .inr ⟨j, V, z, f⟩ =>
        (false, (⟨j, V, z⟩, ⟨V, U.unop, f⟩))
  inj' := by
    rintro (⟨V, y, f⟩ | ⟨j, V, y, f⟩) (⟨W, z, g⟩ | ⟨k, W, z, g⟩) h <;>
      simp only [omegaTotal, siteArrowTotal, Prod.mk.injEq, Sigma.mk.injEq, heq_eq_eq, true_and,
        Bool.true_eq_false, Bool.false_eq_true, false_and] at h
    · obtain ⟨⟨rfl, h₁⟩, -, h₂⟩ := h
      cases h₁
      cases h₂
      rfl
    · obtain ⟨⟨rfl, h₁⟩, -, h₂⟩ := h
      cases h₁
      cases h₂
      rfl

/-- The objectwise submodules generated by the prescribed sections and their differentials,
after restriction to the object in question. -/
private def sectionSubmodules
    (R : Sheaf (⊥ : GrothendieckTopology C) RingCat.{r})
    (F : CochainComplex (SheafOfModules.{m} R) ℤ)
    (Omega : ∀ (i : ℤ) (U : C), Set ((F.X i).val.obj (op U)))
    (i : ℤ) : (F.X i).val.Submodule where
  obj U := Submodule.span (R.obj.obj U) (restrictedGenerators R F Omega i U)
  map f := Submodule.span_le.mpr <| by
    rintro x ⟨V, g, y, hy, rfl⟩
    exact Submodule.subset_span
      ⟨V, g ≫ f, y, hy, PresheafOfModules.map_comp_apply (M := (F.X i).val) g f y⟩

private lemma sectionSubmodules_cardinal_le
    (R : Sheaf (⊥ : GrothendieckTopology C) RingCat.{r})
    (F : CochainComplex (SheafOfModules.{m} R) ℤ)
    (Omega : ∀ (i : ℤ) (U : C), Set ((F.X i).val.obj (op U)))
    (i : ℤ) (U : Cᵒᵖ) :
    Cardinal.lift.{max u v m r}
        (Cardinal.mk ((sectionSubmodules R F Omega i).obj U)) ≤
      max Cardinal.aleph0
        (max (Cardinal.lift.{max u v m r}
              (Cardinal.mk {x // x ∈ restrictedGenerators R F Omega i U}))
          (Cardinal.lift.{max u v m r} (Cardinal.mk (R.obj.obj U)))) := by
  dsimp [sectionSubmodules]
  have h := span_cardinal_le_max
    (A := R.obj.obj U) (M := (F.X i).val.obj U)
    (restrictedGenerators R F Omega i U)
  have h' :=
    (Cardinal.lift_le.{max u v, max (max m r) (max r m)}).2 h
  simpa only [Cardinal.lift_max, Cardinal.lift_aleph0, Cardinal.lift_lift] using h'

private def sectionSheafSubmodule
    (R : Sheaf (⊥ : GrothendieckTopology C) RingCat.{r})
    (F : CochainComplex (SheafOfModules.{m} R) ℤ)
    (Omega : ∀ (i : ℤ) (U : C), Set ((F.X i).val.obj (op U)))
    (i : ℤ) : (F.X i).Submodule where
  toSubmodule := sectionSubmodules R F Omega i
  isSheaf := by
    intro X s hs
    rw [GrothendieckTopology.bot_covering] at hs
    have hid : (sectionSubmodules R F Omega i).toSubfunctor.sieveOfSection s
        (𝟙 X.unop) := by
      rw [hs]
      exact Sieve.top_apply _
    have hid' : s ∈ (sectionSubmodules R F Omega i).toSubfunctor.obj X := by
      dsimp [CategoryTheory.Subfunctor.sieveOfSection] at hid
      change ConcreteCategory.hom ((F.X i).val.presheaf.map (𝟙 X)) s ∈
        (sectionSubmodules R F Omega i).toSubfunctor.obj X at hid
      have hmap : ConcreteCategory.hom ((F.X i).val.presheaf.map (𝟙 X)) =
          AddMonoidHom.id _ := by simp
      rw [hmap] at hid
      change s ∈ (sectionSubmodules R F Omega i).toSubfunctor.obj X at hid
      exact hid
    exact (PresheafOfModules.Submodule.mem_toSubfunctor_obj
      (sectionSubmodules R F Omega i) s).mp hid'

private lemma sectionSubmodules_differential
    (R : Sheaf (⊥ : GrothendieckTopology C) RingCat.{r})
    (F : CochainComplex (SheafOfModules.{m} R) ℤ)
    (Omega : ∀ (i : ℤ) (U : C), Set ((F.X i).val.obj (op U)))
    (i : ℤ) (U : C) {x : (F.X i).val.obj (op U)}
    (hx : x ∈ (sectionSubmodules R F Omega i).obj (op U)) :
    (F.d i (Int.succ i)).val.app (op U) x ∈
      (sectionSubmodules R F Omega (Int.succ i)).obj (op U) := by
  refine Submodule.span_induction (p := fun x _ =>
    (F.d i (Int.succ i)).val.app (op U) x ∈
      (sectionSubmodules R F Omega (Int.succ i)).obj (op U)) ?_ ?_ ?_ ?_ hx
  · rintro x ⟨V, f, y, hy, rfl⟩
    rw [PresheafOfModules.naturality_apply (F.d i (Int.succ i)).val f y]
    rcases hy with hy | ⟨j, z, hz, rfl⟩
    · exact Submodule.subset_span ⟨V, f, _, Or.inr ⟨i, y, hy, rfl⟩, rfl⟩
    · have hmaps : (F.d j i).val.app (op V) ≫
          (F.d i (Int.succ i)).val.app (op V) = 0 :=
        congrArg (fun g : F.X j ⟶ F.X (Int.succ i) => g.val.app (op V))
          (F.d_comp_d j i (Int.succ i))
      have hzero : (F.d i (Int.succ i)).val.app (op V)
          ((F.d j i).val.app (op V) z) = 0 := by
        rw [← ConcreteCategory.comp_apply, hmaps]
        simp
      rw [hzero]
      change (F.X (Int.succ i)).val.map f
        (0 : (F.X (Int.succ i)).val.obj (op V)) ∈
          (sectionSubmodules R F Omega (Int.succ i)).obj (op U)
      rw [map_zero]
      exact (sectionSubmodules R F Omega (Int.succ i)).obj (op U) |>.zero_mem
  · simp
  · intro x y hx hy h₁ h₂
    simpa only [map_add] using
      (sectionSubmodules R F Omega (Int.succ i)).obj (op U) |>.add_mem h₁ h₂
  · intro a x hx h
    simpa only [map_smul] using
      (sectionSubmodules R F Omega (Int.succ i)).obj (op U) |>.smul_mem a h

private lemma sectionSubmodules_contains
    (R : Sheaf (⊥ : GrothendieckTopology C) RingCat.{r})
    (F : CochainComplex (SheafOfModules.{m} R) ℤ)
    (Omega : ∀ (i : ℤ) (U : C), Set ((F.X i).val.obj (op U)))
    (i : ℤ) (U : C) {x : (F.X i).val.obj (op U)} (hx : x ∈ Omega i U) :
    x ∈ (sectionSubmodules R F Omega i).obj (op U) := by
  apply Submodule.subset_span
  refine ⟨U, 𝟙 (op U), x, Or.inl hx, ?_⟩
  simp
  rfl

private noncomputable def differentialRestrictPresheaf
    (R : Sheaf (⊥ : GrothendieckTopology C) RingCat.{r})
    (F : CochainComplex (SheafOfModules.{m} R) ℤ)
    (Omega : ∀ (i : ℤ) (U : C), Set ((F.X i).val.obj (op U)))
    (i : ℤ) :
    (sectionSubmodules R F Omega i).toPresheafOfModules ⟶
      (sectionSubmodules R F Omega (Int.succ i)).toPresheafOfModules where
  app U := by
    let L := ((F.d i (Int.succ i)).val.app U).hom.comp
      ((sectionSubmodules R F Omega i).obj U).subtype
    have hL : ∀ x, L x ∈ (sectionSubmodules R F Omega (Int.succ i)).obj U := by
      intro x
      exact sectionSubmodules_differential R F Omega i U.unop x.2
    exact ModuleCat.ofHom (L.codRestrict _ hL)
  naturality := by
    intro X Y f
    ext x
    apply Subtype.ext
    exact PresheafOfModules.naturality_apply (F.d i (Int.succ i)).val f x.val

private noncomputable def differentialRestrict
    (R : Sheaf (⊥ : GrothendieckTopology C) RingCat.{r})
    (F : CochainComplex (SheafOfModules.{m} R) ℤ)
    (Omega : ∀ (i : ℤ) (U : C), Set ((F.X i).val.obj (op U)))
    (i : ℤ) :
    (sectionSheafSubmodule R F Omega i).toSheafOfModules ⟶
      (sectionSheafSubmodule R F Omega (Int.succ i)).toSheafOfModules :=
  ⟨differentialRestrictPresheaf R F Omega i⟩

private lemma differentialRestrict_comp_ι
    (R : Sheaf (⊥ : GrothendieckTopology C) RingCat.{r})
    (F : CochainComplex (SheafOfModules.{m} R) ℤ)
    (Omega : ∀ (i : ℤ) (U : C), Set ((F.X i).val.obj (op U)))
    (i : ℤ) :
    differentialRestrict R F Omega i ≫ (sectionSheafSubmodule R F Omega (Int.succ i)).ι =
      (sectionSheafSubmodule R F Omega i).ι ≫ F.d i (Int.succ i) := by
  ext U x
  rfl

private noncomputable def sectionMonoOver
    (R : Sheaf (⊥ : GrothendieckTopology C) RingCat.{r})
    (F : CochainComplex (SheafOfModules.{m} R) ℤ)
    (Omega : ∀ (i : ℤ) (U : C), Set ((F.X i).val.obj (op U)))
    (i : ℤ) : MonoOver (F.X i) :=
  MonoOver.mk (sectionSheafSubmodule R F Omega i).ι

private lemma sectionSubobject_d_factors
    (R : Sheaf (⊥ : GrothendieckTopology C) RingCat.{r})
    (F : CochainComplex (SheafOfModules.{m} R) ℤ)
    (Omega : ∀ (i : ℤ) (U : C), Set ((F.X i).val.obj (op U)))
    (i j : ℤ) :
    (sectionMonoOver R F Omega j).Factors
      ((sectionMonoOver R F Omega i).arrow ≫ F.d i j) := by
  by_cases h : i + 1 = j
  · subst j
    exact ⟨differentialRestrict R F Omega i, differentialRestrict_comp_ι R F Omega i⟩
  · rw [F.shape i j (by simpa only [ComplexShape.up_Rel] using h)]
    exact ⟨0, by simp⟩

private lemma monoOver_factorThru_arrow
    {A : Type*} [Category A] {X Y : A} (Q : MonoOver Y) (f : X ⟶ Y)
    (h : Q.Factors f) : Q.factorThru f h ≫ Q.arrow = f := by
  simpa [MonoOver.factorThru, MonoOver.Factors] using Classical.choose_spec h

/-- A family of subobjects of the terms of a homological complex, through which every
differential factors, is itself a homological complex. -/
private noncomputable def homologicalComplexOfMonoOver
    {A : Type*} [Category A] [Limits.HasZeroMorphisms A] {I : Type*} {c : ComplexShape I}
    (L : HomologicalComplex A c) (Q : ∀ i, MonoOver (L.X i))
    (hQ : ∀ i j, (Q j).Factors ((Q i).arrow ≫ L.d i j)) : HomologicalComplex A c where
  X i := Q i
  d i j := (Q j).factorThru ((Q i).arrow ≫ L.d i j) (hQ i j)
  shape i j h := by
    apply (cancel_mono (Q j).arrow).1
    rw [monoOver_factorThru_arrow, L.shape i j h]
    simp
  d_comp_d' i j k hik hjk := by
    apply (cancel_mono (Q k).arrow).1
    rw [Category.assoc, monoOver_factorThru_arrow, ← Category.assoc, monoOver_factorThru_arrow,
      Category.assoc, L.d_comp_d]
    simp

private noncomputable def homologicalComplexOfMonoOverι
    {A : Type*} [Category A] [Limits.HasZeroMorphisms A] {I : Type*} {c : ComplexShape I}
    (L : HomologicalComplex A c) (Q : ∀ i, MonoOver (L.X i))
    (hQ : ∀ i j, (Q j).Factors ((Q i).arrow ≫ L.d i j)) :
    homologicalComplexOfMonoOver L Q hQ ⟶ L where
  f i := (Q i).arrow
  comm' i j _ := (Classical.choose_spec (hQ i j)).symm

private instance homologicalComplexOfMonoOverι_mono
    {A : Type*} [Category A] [Limits.HasZeroMorphisms A] {I : Type*} {c : ComplexShape I}
    (L : HomologicalComplex A c) (Q : ∀ i, MonoOver (L.X i))
    (hQ : ∀ i j, (Q j).Factors ((Q i).arrow ≫ L.d i j)) :
    Mono (homologicalComplexOfMonoOverι L Q hQ) :=
  HomologicalComplex.mono_of_mono_f _ fun i => inferInstanceAs (Mono (Q i).arrow)

private noncomputable def sectionSmallComplex
    (R : Sheaf (⊥ : GrothendieckTopology C) RingCat.{r})
    (F : CochainComplex (SheafOfModules.{m} R) ℤ)
    (Omega : ∀ (i : ℤ) (U : C), Set ((F.X i).val.obj (op U))) :
    CochainComplex (SheafOfModules.{m} R) ℤ :=
  homologicalComplexOfMonoOver F (sectionMonoOver R F Omega)
    (sectionSubobject_d_factors R F Omega)

private noncomputable def sectionSmallComplexι
    (R : Sheaf (⊥ : GrothendieckTopology C) RingCat.{r})
    (F : CochainComplex (SheafOfModules.{m} R) ℤ)
    (Omega : ∀ (i : ℤ) (U : C), Set ((F.X i).val.obj (op U))) :
    sectionSmallComplex R F Omega ⟶ F :=
  homologicalComplexOfMonoOverι F (sectionMonoOver R F Omega)
    (sectionSubobject_d_factors R F Omega)

/-- The size of a complex of sheaves of modules: the cardinality of the disjoint union of its
modules of sections over all objects and in all degrees. -/
def complexSectionSize
    {R : Sheaf (⊥ : GrothendieckTopology C) RingCat.{r}}
    (F : CochainComplex (SheafOfModules.{m} R) ℤ) : Cardinal.{max u v m r} :=
  Cardinal.lift.{max v r} (Cardinal.mk (Σ i : ℤ, Σ U : C, (F.X i).val.obj (op U)))

/-- The size of a family of prescribed sections, indexed by degree and by objects of the
site. -/
def sectionFamilySize
    {R : Sheaf (⊥ : GrothendieckTopology C) RingCat.{r}}
    {F : CochainComplex (SheafOfModules.{m} R) ℤ}
    (Omega : ∀ (i : ℤ) (U : C), Set ((F.X i).val.obj (op U))) :
      Cardinal.{max u v m r} :=
  Cardinal.lift.{max v r} (Cardinal.mk (Σ i : ℤ, Σ U : C, {x // x ∈ Omega i U}))

private lemma restrictedGeneratorData_cardinal_le
    (R : Sheaf (⊥ : GrothendieckTopology C) RingCat.{r})
    (F : CochainComplex (SheafOfModules.{m} R) ℤ)
    (Omega : ∀ (i : ℤ) (U : C), Set ((F.X i).val.obj (op U)))
    (i : ℤ) (U : Cᵒᵖ) :
    Cardinal.lift.{max u v m r}
        (Cardinal.mk (restrictedGeneratorData R F Omega i U)) ≤
      max Cardinal.aleph0
        (max (sectionFamilySize Omega)
          (Cardinal.lift.{max u v m r} (Cardinal.mk (siteArrowTotal C)))) := by
  classical
  let O := omegaTotal R F Omega
  let A := siteArrowTotal C
  let D := restrictedGeneratorData R F Omega i U
  let P := Bool × (O × A)
  have hD : Cardinal.mk D ≤ Cardinal.mk P :=
    Cardinal.mk_le_of_injective (restrictedGeneratorDataEmbedding R F Omega i U).injective
  have hD' : Cardinal.lift.{max u v m r} (Cardinal.mk D) ≤
      Cardinal.lift.{max u v m r} (Cardinal.mk P) :=
    Cardinal.lift_le.2 hD
  have hOA : Cardinal.lift.{max u v m r} (Cardinal.mk (O × A)) =
      Cardinal.lift.{max u v m r} (Cardinal.mk O) *
        Cardinal.lift.{max u v m r} (Cardinal.mk A) := by
    rw [Cardinal.mk_prod, Cardinal.lift_mul]
    simp only [Cardinal.lift_lift]
  have hP : Cardinal.lift.{max u v m r} (Cardinal.mk P) =
      Cardinal.lift.{max u v m r} (Cardinal.mk Bool) *
        Cardinal.lift.{max u v m r} (Cardinal.mk (O × A)) := by
    rw [Cardinal.mk_prod, Cardinal.lift_mul]
    simp only [Cardinal.lift_lift]
  have hO : Cardinal.lift.{max u v m r} (Cardinal.mk O) = sectionFamilySize Omega := by
    dsimp [sectionFamilySize, O, omegaTotal]
    rw [Cardinal.lift_umax.{max m u, max v r}]
  have hB : Cardinal.lift.{max u v m r} (Cardinal.mk Bool) = 2 := by simp
  rw [hP, hOA, hO, hB] at hD'
  have hmul :
      2 * (sectionFamilySize Omega *
        Cardinal.lift.{max u v m r} (Cardinal.mk A)) ≤
      max Cardinal.aleph0
        (max (sectionFamilySize Omega)
          (Cardinal.lift.{max u v m r} (Cardinal.mk A))) := by
    apply Cardinal.mul_le_of_le
      (le_max_left _ _) (by simp)
    simpa [max_comm] using
      (Cardinal.mul_le_max (sectionFamilySize Omega)
        (Cardinal.lift.{max u v m r} (Cardinal.mk A)))
  exact hD'.trans hmul

/-- **Stacks 0GYX.** There is a cardinal, depending only on the category and its sheaf of
rings, such that every family of prescribed sections of a complex is contained in a
subcomplex whose size is bounded by the maximum of that cardinal and the size of the
family. -/
@[stacks 0GYX]
theorem exists_subcomplex_containing_sections_of_size_le
    (R : Sheaf (⊥ : GrothendieckTopology C) RingCat.{r}) :
    ∃ kappa : Cardinal.{max u v m r},
      ∀ (F : CochainComplex (SheafOfModules.{m} R) ℤ)
        (Omega : ∀ (i : ℤ) (U : C), Set ((F.X i).val.obj (op U))),
        ∃ (H : CochainComplex (SheafOfModules.{m} R) ℤ) (inclusion : H ⟶ F),
          Mono inclusion ∧
            (∀ (i : ℤ) (U : C) (x : (F.X i).val.obj (op U)), x ∈ Omega i U →
              ∃ y : (H.X i).val.obj (op U), (inclusion.f i).val.app (op U) y = x) ∧
            complexSectionSize H ≤ max kappa (sectionFamilySize Omega) := by
  classical
  let Index := Σ i : ℤ, C
  let Arrows := siteArrowTotal C
  let RingSections := Σ U : C, R.obj.obj (op U)
  let kappa : Cardinal.{max u v m r} :=
    max Cardinal.aleph0
      (max (Cardinal.lift.{max u v m r} (Cardinal.mk Index))
        (max (Cardinal.lift.{max u v m r} (Cardinal.mk Arrows))
          (Cardinal.lift.{max u v m r} (Cardinal.mk RingSections))))
  refine ⟨kappa, ?_⟩
  intro F Omega
  let H := sectionSmallComplex R F Omega
  let inclusion := sectionSmallComplexι R F Omega
  let B : Cardinal.{max u v m r} := max kappa (sectionFamilySize Omega)
  have hAleph : Cardinal.aleph0 ≤ B := le_trans (le_max_left _ _) (le_max_left _ _)
  have hIndex : Cardinal.lift.{max u v m r} (Cardinal.mk Index) ≤ B :=
    (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_left _ _))
  have hArrows : Cardinal.lift.{max u v m r} (Cardinal.mk Arrows) ≤ B :=
    ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))).trans
      (le_max_left _ _)
  have hRingSections : Cardinal.lift.{max u v m r} (Cardinal.mk RingSections) ≤ B :=
    ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))).trans
      (le_max_left _ _)
  have hFamily : sectionFamilySize Omega ≤ B := le_max_right _ _
  have : Mono inclusion := homologicalComplexOfMonoOverι_mono F (sectionMonoOver R F Omega)
    (sectionSubobject_d_factors R F Omega)
  refine ⟨H, inclusion, this, ?_, ?_⟩
  · exact fun i U x hx => ⟨⟨x, sectionSubmodules_contains R F Omega i U hx⟩, rfl⟩
  · change complexSectionSize H ≤ B
    have hLocalRing (U : Cᵒᵖ) :
        Cardinal.lift.{max u v m r} (Cardinal.mk (R.obj.obj U)) ≤ B := by
      have hEmbed : (R.obj.obj U) ↪ RingSections :=
        ⟨fun x => ⟨U.unop, x⟩, by intro x y h; cases h; rfl⟩
      exact (Cardinal.lift_mk_le.{max u v m r, r, max u r}.2 ⟨hEmbed⟩).trans hRingSections
    have hGeneratorData (i : ℤ) (U : Cᵒᵖ) :
        Cardinal.lift.{max u v m r}
            (Cardinal.mk (restrictedGeneratorData R F Omega i U)) ≤ B := by
      apply (restrictedGeneratorData_cardinal_le R F Omega i U).trans
      exact max_le hAleph (max_le hFamily hArrows)
    have hGenerators (i : ℤ) (U : Cᵒᵖ) :
        Cardinal.lift.{max u v m r}
            (Cardinal.mk {x // x ∈ restrictedGenerators R F Omega i U}) ≤ B :=
      (restrictedGenerators_cardinal_le R F Omega i U).trans (hGeneratorData i U)
    have hSection (i : ℤ) (U : Cᵒᵖ) :
        Cardinal.lift.{max u v m r}
            (Cardinal.mk ((sectionSubmodules R F Omega i).obj U)) ≤ B := by
      apply (sectionSubmodules_cardinal_le R F Omega i U).trans
      exact max_le hAleph (max_le (hGenerators i U) (hLocalRing U))
    have hFiber (p : Index) :
        Cardinal.lift.{max u v m r}
            (Cardinal.mk ((H.X p.1).val.obj (op p.2))) ≤ B :=
      hSection p.1 (op p.2)
    let Fib := fun p : Index => (H.X p.1).val.obj (op p.2)
    have hSup : (⨆ p : Index,
        Cardinal.lift.{max u v m r} (Cardinal.mk (Fib p))) ≤ B :=
      ciSup_le' fun p => hFiber p
    have hSigmaBound : Cardinal.lift.{max u v m r}
        (Cardinal.mk (Σ p : Index, Fib p)) ≤
          Cardinal.lift.{max u v m r} (Cardinal.mk Index) *
            ⨆ p : Index, Cardinal.lift.{max u v m r} (Cardinal.mk (Fib p)) := by
      rw [Cardinal.mk_sigma, Cardinal.lift_sum]
      exact Cardinal.sum_le_lift_mk_mul_iSup _
    have hSigma : Cardinal.lift.{max u v m r}
        (Cardinal.mk (Σ p : Index, Fib p)) ≤ B :=
      hSigmaBound.trans (Cardinal.mul_le_of_le hAleph hIndex hSup)
    have hSigmaNarrow : Cardinal.lift.{max v r}
        (Cardinal.mk (Σ p : Index, Fib p)) ≤ B := by
      rwa [Cardinal.lift_umax.{max m u, max v r}] at hSigma
    let Section : ℤ → C → Type m := fun i U => ↑((H.X i).val.obj (op U))
    have hReindex : Cardinal.mk (Σ i : ℤ, Σ U : C, Section i U) =
        Cardinal.mk (Σ p : Index, Section p.1 p.2) :=
      (Cardinal.mk_congr (Equiv.sigmaAssoc Section)).symm
    unfold complexSectionSize
    rw [hReindex]
    simpa [Index, Fib, Section] using hSigmaNarrow

end Stacks.ModulesOnACategory
