module

public import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated
public import StacksFrontier.Algebra.Homology.DerivedCategory.Filtered.Defs
public import StacksFrontier.Algebra.Homology.SpectralSequence.FilteredComplex.Defs

/-!
# The mapping cone of a morphism of filtered complexes

Let `A` be an abelian category and let `w : P^• ⟶ Q^•` be a morphism of filtered complexes of `A`.
Its mapping cone is the filtered complex whose underlying complex is `C(w)` and whose `p`-th
filtration step is `C(F^pw)`, the mapping cone of the induced morphism `F^pP^• ⟶ F^pQ^•`.  The
inclusion `C(F^pw) ⟶ C(w)` is the morphism of mapping cones induced by the commutative square
expressing that `w` respects the filtration; it is a monomorphism because its two components are,
so these subcomplexes do form a filtration.

## Main definitions

* `CochainComplex.mappingCone.inl_v_map_f`, `CochainComplex.mappingCone.inr_f_map_f`: the
  compatibilities of the induced morphism of mapping cones with the two inclusions of a cone.
* `CochainComplex.mappingCone.mono_map_f`, `CochainComplex.mappingCone.epi_map_f`: the induced
  morphism is a monomorphism, resp. an epimorphism, in a degree in which both vertical maps of
  the square are.
* `CochainComplex.mappingCone.mono_map`: the morphism of mapping cones induced by a commutative
  square with monomorphic vertical maps is a monomorphism.
* `Stacks.Injectives.filteredMappingCone`: the mapping cone of a morphism of filtered complexes.
* `Stacks.Injectives.filteredMappingConeInr`: the canonical morphism from the target of `w` into
  the mapping cone, as a morphism of filtered complexes.

## Implementation notes

The mapping cone of a morphism of filtered complexes is assembled with `Filtration.ofDiagram` out
of the diagram `p ↦ C(F^pw)` and its natural transformation to the constant diagram `C(w)`; the
resulting filtration therefore has `diagram` and `ι` given on the nose by those data, which is
what makes `filteredMappingConeInr` a morphism of filtered complexes with the expected components.

The monomorphy of `mappingCone.map` is proved degreewise by cancelling against the two components
`fst` and `snd` of the cone, which is why `mappingCone.map_f_fst_v` and `mappingCone.map_f_snd_v`
are recorded first.
-/

@[expose] public noncomputable section

universe v u

open CategoryTheory CategoryTheory.Limits Opposite
open CochainComplex.HomComplex

namespace CochainComplex.mappingCone

variable {A : Type u} [Category.{v} A] [Preadditive A] [HasBinaryBiproducts A]
  {K₁ L₁ K₂ L₂ : CochainComplex A ℤ} (φ₁ : K₁ ⟶ L₁) (φ₂ : K₂ ⟶ L₂)
  (a : K₁ ⟶ K₂) (b : L₁ ⟶ L₂) (comm : φ₁ ≫ b = a ≫ φ₂)

/-- The morphism of mapping cones induced by a commutative square depends only on the two
vertical maps of that square. -/
lemma map_congr {a' : K₁ ⟶ K₂} {b' : L₁ ⟶ L₂} (ha : a = a') (hb : b = b')
    (comm' : φ₁ ≫ b' = a' ≫ φ₂) :
    map φ₁ φ₂ a b comm = map φ₁ φ₂ a' b' comm' := by
  subst ha hb
  rfl

/-- The first component of the morphism of mapping cones induced by a commutative square is the
first component composed with the map of sources. -/
lemma map_f_fst_v (n : ℤ) :
    (map φ₁ φ₂ a b comm).f n ≫ (fst φ₂).1.v n (n + 1) rfl =
      (fst φ₁).1.v n (n + 1) rfl ≫ a.f (n + 1) := by
  apply ext_from φ₁ (n + 1) n rfl <;> simp [map]

/-- The canonical morphism into a mapping cone commutes with the morphism of mapping cones
induced by a commutative square. -/
@[reassoc]
lemma inr_map : inr φ₁ ≫ map φ₁ φ₂ a b comm = b ≫ inr φ₂ := by
  simp [map]

/-- The second component of the morphism of mapping cones induced by a commutative square is the
second component composed with the map of targets. -/
lemma map_f_snd_v (n : ℤ) :
    (map φ₁ φ₂ a b comm).f n ≫ (snd φ₂).v n n (add_zero n) =
      (snd φ₁).v n n (add_zero n) ≫ b.f n := by
  apply ext_from φ₁ (n + 1) n rfl <;> simp [map]

/-- The canonical inclusion of the shifted source into a mapping cone commutes with the morphism
of mapping cones induced by a commutative square. -/
lemma inl_v_map_f (n : ℤ) :
    (inl φ₁).v (n + 1) n (by omega) ≫ (map φ₁ φ₂ a b comm).f n =
      a.f (n + 1) ≫ (inl φ₂).v (n + 1) n (by omega) := by
  simp [map, inl_v_desc_f]

/-- The canonical morphism into a mapping cone commutes degreewise with the morphism of mapping
cones induced by a commutative square. -/
lemma inr_f_map_f (n : ℤ) :
    (inr φ₁).f n ≫ (map φ₁ φ₂ a b comm).f n = b.f n ≫ (inr φ₂).f n := by
  rw [← HomologicalComplex.comp_f, ← HomologicalComplex.comp_f, inr_map]

/-- A morphism of mapping cones induced by a square whose vertical maps are monomorphisms in the
relevant degrees is a monomorphism in that degree. -/
lemma mono_map_f (n : ℤ) (ha : Mono (a.f (n + 1))) (hb : Mono (b.f n)) :
    Mono ((map φ₁ φ₂ a b comm).f n) := by
  have := ha
  have := hb
  constructor
  intro Z g h e
  rw [ext_to_iff φ₁ n (n + 1) rfl]
  refine ⟨(cancel_mono (a.f (n + 1))).1 ?_, (cancel_mono (b.f n)).1 ?_⟩
  · rw [Category.assoc, Category.assoc, ← map_f_fst_v, reassoc_of% e]
  · rw [Category.assoc, Category.assoc, ← map_f_snd_v, reassoc_of% e]

/-- A morphism of mapping cones induced by a square whose vertical maps are epimorphisms in the
relevant degrees is an epimorphism in that degree. -/
lemma epi_map_f (n : ℤ) (ha : Epi (a.f (n + 1))) (hb : Epi (b.f n)) :
    Epi ((map φ₁ φ₂ a b comm).f n) := by
  have := ha
  have := hb
  constructor
  intro Z g h e
  rw [ext_from_iff _ (n + 1) n rfl]
  refine ⟨(cancel_epi (a.f (n + 1))).1 ?_, (cancel_epi (b.f n)).1 ?_⟩
  · rw [← reassoc_of% inl_v_map_f φ₁ φ₂ a b comm n, e, reassoc_of% inl_v_map_f φ₁ φ₂ a b comm n]
  · rw [← reassoc_of% inr_f_map_f φ₁ φ₂ a b comm n, e, reassoc_of% inr_f_map_f φ₁ φ₂ a b comm n]

/-- **The morphism of mapping cones induced by a commutative square with monomorphic vertical
maps is a monomorphism.**  A map into a mapping cone is determined by its two components, and each
of them may be cancelled against the corresponding vertical map.

Unlike the lemmas above, this needs `A` abelian: it is where a monomorphism of complexes is
turned into a monomorphism in each degree. -/
lemma mono_map {B : Type u} [Category.{v} B] [Abelian B] {K₁ L₁ K₂ L₂ : CochainComplex B ℤ}
    (φ₁ : K₁ ⟶ L₁) (φ₂ : K₂ ⟶ L₂) (a : K₁ ⟶ K₂) (b : L₁ ⟶ L₂) (comm : φ₁ ≫ b = a ≫ φ₂)
    [Mono a] [Mono b] : Mono (map φ₁ φ₂ a b comm) :=
  HomologicalComplex.mono_of_mono_f _ fun n =>
    mono_map_f φ₁ φ₂ a b comm n inferInstance inferInstance

end CochainComplex.mappingCone

namespace Stacks.Injectives

variable {A : Type u} [Category.{v} A] [Abelian A]

section

variable {P Q : CochainComplex.Filtered A} (w : P ⟶ Q)

/-- The diagram `p ↦ C(F^pw)` of mapping cones of the filtration steps of `w`. -/
def filteredMappingConeDiagram : ℤᵒᵖ ⥤ CochainComplex A ℤ where
  obj i := CochainComplex.mappingCone (w.natTrans.app i)
  map α := CochainComplex.mappingCone.map _ _
    (P.filtration.diagram.map α) (Q.filtration.diagram.map α) (w.natTrans.naturality α).symm
  map_id i := (CochainComplex.mappingCone.map_congr _ _ _ _ _
    (P.filtration.diagram.map_id i) (Q.filtration.diagram.map_id i) _).trans
      (CochainComplex.mappingCone.map_id _)
  map_comp α β := (CochainComplex.mappingCone.map_congr _ _ _ _ _
    (P.filtration.diagram.map_comp α β) (Q.filtration.diagram.map_comp α β) _).trans
      (CochainComplex.mappingCone.map_comp _ _ _ _ _ _ _ _ _)

/-- The inclusions `C(F^pw) ⟶ C(w)` of the mapping cones of the filtration steps of `w` into the
mapping cone of `w`. -/
def filteredMappingConeInclusion :
    filteredMappingConeDiagram w ⟶
      (Functor.const ℤᵒᵖ).obj (CochainComplex.mappingCone w.hom) where
  app i := CochainComplex.mappingCone.map _ _
    (P.filtration.ι.app i) (Q.filtration.ι.app i) (w.comm i)
  naturality i j α :=
    (((CochainComplex.mappingCone.map_comp (w.natTrans.app i) (w.natTrans.app j) w.hom
        (P.filtration.diagram.map α) (Q.filtration.diagram.map α)
        (w.natTrans.naturality α).symm
        (P.filtration.ι.app j) (Q.filtration.ι.app j) (w.comm j)).symm).trans
      (CochainComplex.mappingCone.map_congr _ _ _ _ _
        (P.filtration.diagram_map_comp_ι_app α)
        (Q.filtration.diagram_map_comp_ι_app α) _)).trans (Category.comp_id _).symm

/-- The `p`-th component of `filteredMappingConeInclusion w` is the morphism of mapping cones
induced by the inclusions of the `p`-th filtration steps of `P` and `Q`. -/
lemma filteredMappingConeInclusion_app (i : ℤᵒᵖ) :
    (filteredMappingConeInclusion w).app i =
      CochainComplex.mappingCone.map (w.natTrans.app i) w.hom
        (P.filtration.ι.app i) (Q.filtration.ι.app i) (w.comm i) :=
  rfl

/-- Each component of `filteredMappingConeInclusion w` is a monomorphism. -/
instance mono_filteredMappingConeInclusion_app (i : ℤᵒᵖ) :
    Mono ((filteredMappingConeInclusion w).app i) :=
  CochainComplex.mappingCone.mono_map _ _ _ _ (w.comm i)

/-- **The mapping cone of a morphism of filtered complexes.**  Its underlying complex is `C(w)`
and its `p`-th filtration step is the mapping cone `C(F^pw)` of the `p`-th filtration step
of `w`. -/
def filteredMappingCone : CochainComplex.Filtered A where
  X := CochainComplex.mappingCone w.hom
  filtration := Filtration.ofDiagram _ (filteredMappingConeInclusion w)

/-- The underlying complex of `filteredMappingCone w` is the mapping cone of `w.hom`. -/
@[simp] lemma filteredMappingCone_X :
    (filteredMappingCone w).X = CochainComplex.mappingCone w.hom :=
  rfl

/-- The `p`-th filtration step of `filteredMappingCone w` is the mapping cone of the `p`-th
component of `w`. -/
@[simp] lemma filteredMappingCone_filtration_obj (i : ℤᵒᵖ) :
    (filteredMappingCone w).filtration.obj i =
      CochainComplex.mappingCone (w.natTrans.app i) :=
  rfl

/-- The canonical morphism from the target of `w` into the mapping cone of `w`, as a morphism of
filtered complexes. -/
def filteredMappingConeInr : Q ⟶ filteredMappingCone w :=
  FilteredObject.homMk (CochainComplex.mappingCone.inr w.hom)
    (fun i => CochainComplex.mappingCone.inr (w.natTrans.app i))
    (fun i => CochainComplex.mappingCone.inr_map _ _ _ _ (w.comm i))

/-- The underlying morphism of `filteredMappingConeInr w` is `CochainComplex.mappingCone.inr`. -/
@[simp] lemma filteredMappingConeInr_hom :
    (filteredMappingConeInr w).hom = CochainComplex.mappingCone.inr w.hom :=
  rfl

/-- On the `p`-th filtration step, `filteredMappingConeInr w` is the canonical morphism into the
mapping cone of the `p`-th component of `w`. -/
@[simp] lemma filteredMappingConeInr_natTrans_app (i : ℤᵒᵖ) :
    (filteredMappingConeInr w).natTrans.app i =
      CochainComplex.mappingCone.inr (w.natTrans.app i) :=
  rfl

end

end Stacks.Injectives

end
