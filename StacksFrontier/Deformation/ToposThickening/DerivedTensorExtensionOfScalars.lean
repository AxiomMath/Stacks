module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatChangeOfRings
public import StacksFrontier.Deformation.ToposThickening.ComplexMapLift
public import StacksFrontier.Deformation.ToposThickening.DerivedSheafTensorExists

/-!
# The derived tensor product at a derived base change

Let `f : O ⟶ O₀` be a morphism of sheaves of commutative rings on a site and let `M` be a
sheaf of `O₀`-modules. This file shows that the comparison
`Deformation.ComplexLift.derivedTensorRightCounitHomotopy` of the derived tensor product
`- ⊗_{O₀}^L M` with the degreewise one is invertible at the extension of scalars of a
`P`-cellular object of `K(Mod(O))`, `P` being the flat sheaves of modules.

## References

* [Stacks Project, Tag 0794](https://stacks.math.columbia.edu/tag/0794)
* [Stacks Project, Tag 0DIX](https://stacks.math.columbia.edu/tag/0DIX)
* [Stacks Project, Tag 05V4](https://stacks.math.columbia.edu/tag/05V4)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open StacksDraft.UnboundedLeftDerivedFunctor

noncomputable section

universe d d₀ v' u u'

namespace Deformation.ComplexLift

variable {C : Type u'} [Category.{v'} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
variable [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable {O O₀ : Sheaf J CommRingCat.{u}}

/-! ### Extension of scalars preserves flatness and bounds -/

/-- **Stacks 05V4 at the spelling of the lift statements**: extension of scalars takes a flat
sheaf of modules to a flat sheaf of modules. -/
theorem flatObjects_extensionOfScalars (f : O ⟶ O₀)
    {N : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)} (hN : flatObjects O N) :
    flatObjects O₀ ((extensionOfScalars f).obj N) :=
  Stacks.FlatChangeOfRings.isFlat_extendScalars f N hN

/-- A functor preserving zero morphisms takes a zero object to a zero object. -/
private theorem isZero_obj_of_isZero {A B : Type*} [Category A] [Category B]
    [HasZeroMorphisms A] [HasZeroMorphisms B] (G : A ⥤ B) [G.PreservesZeroMorphisms]
    {Z : A} (hZ : IsZero Z) : IsZero (G.obj Z) := by
  rw [IsZero.iff_id_eq_zero, ← G.map_id, hZ.eq_of_src (𝟙 Z) 0, G.map_zero]

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- Extension of scalars, read degreewise, keeps a complex bounded above. -/
theorem isStrictlyLE_map_extensionOfScalars (f : O ⟶ O₀) (a : ℤ)
    (L : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)) ℤ)
      (hLE : L.IsStrictlyLE a) :
    CochainComplex.IsStrictlyLE (((extensionOfScalars f).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj L) a := by
  have := hLE
  rw [CochainComplex.isStrictlyLE_iff]
  intro i hi
  exact isZero_obj_of_isZero (extensionOfScalars f) (L.isZero_of_isStrictlyLE a i hi)

/-! ### Extension of scalars followed by a tensor product -/

/-- Extension of scalars along `f`, followed by the tensor product with a fixed sheaf of
`O₀`-modules `M`. -/
abbrev extensionTensorRight (f : O ⟶ O₀)
  (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₀)) :
    SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O) ⥤ SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf O₀) :=
  extensionOfScalars f ⋙ tensorRight O₀ M

/-- **The hypothesis of Stacks 0794 for `(- ⊗_O O₀) ⊗_{O₀} M`**: the composite carries a
bounded above acyclic complex of flat sheaves of `O`-modules to an acyclic complex.

Extension of scalars carries such a complex to a bounded above acyclic complex of flat sheaves
of `O₀`-modules (Stacks 03EX and 05V4), and tensoring with `M` then keeps it acyclic, again by
Stacks 03EX. -/
theorem acyclic_map_extensionTensorRight (f : O ⟶ O₀)
    (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₀)) (a : ℤ)
    (L : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)) ℤ)
      (hLE : L.IsStrictlyLE a)
    (hflat : ∀ n : ℤ, flatObjects O (L.X n)) (hac : L.Acyclic) :
    (((extensionTensorRight f M).mapHomologicalComplex (ComplexShape.up ℤ)).obj L).Acyclic :=
  acyclic_map_tensorRight M a
    (((extensionOfScalars f).mapHomologicalComplex (ComplexShape.up ℤ)).obj L)
    (isStrictlyLE_map_extensionOfScalars f a L hLE)
    (fun n ↦ flatObjects_extensionOfScalars f (hflat n))
    (acyclic_map_extensionOfScalars f a L hLE hflat hac)

/-! ### Resolutions by cellular complexes -/

/-- **The degreewise tensor product with `M` inverts a quasi-isomorphism between `P`-cellular
objects of `K(Mod(R))`**, `P` being the flat sheaves of modules: this is Stacks 0794 for
`Deformation.ComplexLift.tensorRight`. -/
theorem isIso_map_tensorRightHomotopy_of_cellular (R : Sheaf J CommRingCat.{u})
    [HasDerivedCategory.{d} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf R))]
    (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf R))
    {A B : HomotopyCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf R))
      (ComplexShape.up ℤ)}
    (s : A ⟶ B)
    (hs : HomotopyCategory.quasiIso (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf R))
      (ComplexShape.up ℤ) s)
    (hA : cellular (flatObjects R) A) (hB : cellular (flatObjects R) B) :
    IsIso ((tensorRightHomotopy.{d} M).map s) := by
  have := hasExactColimitsOfShape_nat (Stacks.SheafOfModules.Tensor.ringSheaf R)
  have hder := derives_cellularLocalizerMorphism (tensorRight R M) (flatObjects R)
    (flatObjects_biprod R) (flatObjects_cover R) (acyclic_map_tensorRight M)
  exact hder (ObjectProperty.homMk (P := cellular (flatObjects R))
    (X := ⟨_, hA⟩) (Y := ⟨_, hB⟩) s) hs

/-- Every object of `K(Mod(O₀))` receives a quasi-isomorphism from a `P`-cellular object: the
ladder of flat resolutions of its canonical truncations (Stacks 06XX). -/
theorem exists_cellular_quasiIso (R : Sheaf J CommRingCat.{u})
    (T : HomotopyCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf R))
      (ComplexShape.up ℤ))
      :
    ∃
      (Y : HomotopyCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf R))
        (ComplexShape.up ℤ))
      (_ : cellular (flatObjects R) Y) (s : Y ⟶ T),
      HomotopyCategory.quasiIso (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf R))
        (ComplexShape.up ℤ) s := by
  have := hasExactColimitsOfShape_nat (Stacks.SheafOfModules.Tensor.ringSheaf R)
  obtain ⟨res⟩ := hasLeftResolutions_cellularLocalizerMorphism (flatObjects R)
    (flatObjects_biprod R) (flatObjects_cover R) T
  exact ⟨res.X₁.obj, res.X₁.property, res.w, res.hw⟩

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- A `P`-cellular complex, read in `K(Mod(O₀))`, is a `P`-cellular object. -/
theorem cellular_quotient_obj (R : Sheaf J CommRingCat.{u})
    {S : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf R)) ℤ}
    (hS : IsPCellular (flatObjects R) S) :
    cellular (flatObjects R)
      ((HomotopyCategory.quotient (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf R))
        (ComplexShape.up ℤ)).obj S) :=
  ⟨S, hS, ⟨Iso.refl _⟩⟩


/-! ### The two functors invert quasi-isomorphisms between cellular complexes -/

section Cellular

variable [HasDerivedCategory.{d} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O))]
variable [HasDerivedCategory.{d₀} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₀))]

omit [HasDerivedCategory (SheafOfModules (Stacks.SheafOfModules.Tensor.ringSheaf O₀))] in
/-- **Extension of scalars inverts the quasi-isomorphisms between `P`-cellular complexes**,
`P` being the flat sheaves of modules: this is Stacks 0794 for
`Deformation.ComplexLift.extensionOfScalars`, whose hypothesis `hFP` is
`Deformation.ComplexLift.acyclic_map_extensionOfScalars`. -/
theorem quasiIso_map_extensionOfScalars (f : O ⟶ O₀)
    {S T : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)) ℤ}
    (hS : IsPCellular (flatObjects O) S) (hT : IsPCellular (flatObjects O) T)
    (α : S ⟶ T) (hα : QuasiIso α) :
    QuasiIso (((extensionOfScalars f).mapHomologicalComplex (ComplexShape.up ℤ)).map α) := by
  have := hasExactColimitsOfShape_nat (Stacks.SheafOfModules.Tensor.ringSheaf O)
  have := hasExactColimitsOfShape_nat (Stacks.SheafOfModules.Tensor.ringSheaf O₀)
  exact quasiIso_mapHomologicalComplex_of_isPCellular (extensionOfScalars f) (flatObjects O)
    (flatObjects_biprod O) (flatObjects_cover O) (acyclic_map_extensionOfScalars f) hS hT α hα

omit [HasDerivedCategory (SheafOfModules (Stacks.SheafOfModules.Tensor.ringSheaf O₀))] in
/-- **`(- ⊗_O O₀) ⊗_{O₀} M` inverts the quasi-isomorphisms between `P`-cellular complexes**:
Stacks 0794 for the composite, whose hypothesis `hFP` is
`Deformation.ComplexLift.acyclic_map_extensionTensorRight`. -/
theorem quasiIso_map_extensionTensorRight (f : O ⟶ O₀)
    (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₀))
    {S T : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)) ℤ}
    (hS : IsPCellular (flatObjects O) S) (hT : IsPCellular (flatObjects O) T)
    (α : S ⟶ T) (hα : QuasiIso α) :
    QuasiIso (((extensionTensorRight f M).mapHomologicalComplex (ComplexShape.up ℤ)).map α) := by
  have := hasExactColimitsOfShape_nat (Stacks.SheafOfModules.Tensor.ringSheaf O)
  have := hasExactColimitsOfShape_nat (Stacks.SheafOfModules.Tensor.ringSheaf O₀)
  exact quasiIso_mapHomologicalComplex_of_isPCellular (extensionTensorRight f M) (flatObjects O)
    (flatObjects_biprod O) (flatObjects_cover O) (acyclic_map_extensionTensorRight f M) hS hT α hα

/-! ### The class on which the degreewise tensor product computes the derived one -/

/-- A morphism which becomes invertible both after composing with a morphism on the right and
after composing with one on the left is invertible: the two composites make it a split
monomorphism and a split epimorphism, and the two one-sided inverses then agree. -/
private theorem isIso_of_isIso_comp_of_isIso_comp {D : Type*} [Category D] {X Y Z W : D}
    (a : Y ⟶ Z) (b : Z ⟶ W) (c : X ⟶ Y) (hab : IsIso (a ≫ b)) (hca : IsIso (c ≫ a)) :
    IsIso a := by
  have := hab
  have := hca
  have hr : a ≫ b ≫ inv (a ≫ b) = 𝟙 Y := by
    rw [← Category.assoc, IsIso.hom_inv_id]
  have hs : (inv (c ≫ a) ≫ c) ≫ a = 𝟙 Z := by
    rw [Category.assoc, IsIso.inv_hom_id]
  refine ⟨b ≫ inv (a ≫ b), hr, ?_⟩
  have heq : b ≫ inv (a ≫ b) = inv (c ≫ a) ≫ c := by
    calc b ≫ inv (a ≫ b) = 𝟙 Z ≫ b ≫ inv (a ≫ b) := (Category.id_comp _).symm
      _ = ((inv (c ≫ a) ≫ c) ≫ a) ≫ b ≫ inv (a ≫ b) := by rw [hs]
      _ = (inv (c ≫ a) ≫ c) ≫ a ≫ b ≫ inv (a ≫ b) := by rw [Category.assoc]
      _ = inv (c ≫ a) ≫ c := by rw [hr, Category.comp_id]
  rw [heq]
  exact hs

/-- The objects of `K(Mod(O₀))` at which the degreewise tensor product with `M` already computes
the derived one: those receiving from every `P`-cellular object only quasi-isomorphisms which
stay invertible after tensoring with `M`. -/
def tensorResolving (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₀)) :
    ObjectProperty
      (HomotopyCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₀))
      (ComplexShape.up ℤ)) :=
  fun T ↦ ∀
    (Y : HomotopyCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₀))
      (ComplexShape.up ℤ))
    (w : Y ⟶ T), HomotopyCategory.quasiIso
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₀))
      (ComplexShape.up ℤ) w → cellular (flatObjects O₀) Y →
      IsIso ((tensorRightHomotopy.{d₀} M).map w)

/-- A `P`-cellular object belongs to the class. -/
theorem tensorResolving_of_cellular
  (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₀))
    {T : HomotopyCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₀))
      (ComplexShape.up ℤ)}
    (hT : cellular (flatObjects O₀) T) : tensorResolving.{d₀} M T :=
  fun _ w hw hY ↦ isIso_map_tensorRightHomotopy_of_cellular O₀ M w hw hY hT

/-- The class resolves every object, the `P`-cellular objects already doing so. -/
theorem exists_tensorResolving_quasiIso
  (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₀))
    (T : HomotopyCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₀))
      (ComplexShape.up ℤ))
      :
    ∃
      (Y : HomotopyCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₀))
        (ComplexShape.up ℤ))
      (_ : tensorResolving.{d₀} M Y) (s : Y ⟶ T),
      HomotopyCategory.quasiIso (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₀))
        (ComplexShape.up ℤ) s := by
  obtain ⟨Y, hY, s, hs⟩ := exists_cellular_quasiIso O₀ T
  exact ⟨Y, tensorResolving_of_cellular M hY, s, hs⟩

/-- **The degreewise tensor product with `M` inverts the quasi-isomorphisms between objects of
the class**: both are compared with a `P`-cellular resolution of the source. -/
theorem isIso_map_tensorRightHomotopy_of_tensorResolving
    (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₀))
    {A B : HomotopyCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₀))
      (ComplexShape.up ℤ)}
    (s : A ⟶ B)
    (hs : HomotopyCategory.quasiIso (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₀))
      (ComplexShape.up ℤ) s)
    (hA : tensorResolving.{d₀} M A) (hB : tensorResolving.{d₀} M B) :
    IsIso ((tensorRightHomotopy.{d₀} M).map s) := by
  obtain ⟨Y, hY, u, hu⟩ := exists_cellular_quasiIso O₀ A
  have h₁ : IsIso ((tensorRightHomotopy.{d₀} M).map u) := hA Y u hu hY
  have h₂ : IsIso ((tensorRightHomotopy.{d₀} M).map (u ≫ s)) :=
    hB Y (u ≫ s) (MorphismProperty.comp_mem _ _ _ hu hs) hY
  rw [Functor.map_comp] at h₂
  exact IsIso.of_isIso_comp_left ((tensorRightHomotopy.{d₀} M).map u) _

/-- A quasi-isomorphism between objects of `K(Mod(R))` which are isomorphic to quotients of
complexes comes from a quasi-isomorphism of complexes. -/
private theorem exists_quasiIso_quotient_map_eq {D : Type u'} [Category.{v'} D]
    {K : GrothendieckTopology D} [HasSheafify K AddCommGrpCat.{u}]
    [K.WEqualsLocallyBijective AddCommGrpCat.{u}] (R : Sheaf K CommRingCat.{u})
    {Y : HomotopyCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf R))
      (ComplexShape.up ℤ)}
    {A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf R)) ℤ}
    (e : Y ≅ (HomotopyCategory.quotient
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf R)) (ComplexShape.up ℤ)).obj A)
    (w : Y ⟶ (HomotopyCategory.quotient
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf R)) (ComplexShape.up ℤ)).obj B)
    (hw : HomotopyCategory.quasiIso
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf R)) (ComplexShape.up ℤ) w) :
    ∃ q : A ⟶ B, QuasiIso q ∧ (HomotopyCategory.quotient
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf R))
      (ComplexShape.up ℤ)).map q = e.inv ≫ w := by
  obtain ⟨q, hq⟩ := (HomotopyCategory.quotient
    (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf R))
    (ComplexShape.up ℤ)).map_surjective (e.inv ≫ w)
  refine ⟨q, ?_, hq⟩
  rw [← HomologicalComplex.mem_quasiIso_iff,
    ← HomotopyCategory.quotient_map_mem_quasiIso_iff, hq]
  exact MorphismProperty.comp_mem _ _ _ (MorphismProperty.of_isIso _ e.inv) hw

/-- A quasi-isomorphism of complexes becomes invertible in the derived category. -/
private theorem isIso_Qh_map_quotient_map {D : Type u'} [Category.{v'} D]
    {K : GrothendieckTopology D} [HasSheafify K AddCommGrpCat.{u}]
    [K.WEqualsLocallyBijective AddCommGrpCat.{u}] (R : Sheaf K CommRingCat.{u})
    [HasDerivedCategory.{d} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf R))]
    {A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf R)) ℤ}
    (φ : A ⟶ B) (hφ : QuasiIso φ) :
    IsIso (DerivedCategory.Qh.map ((HomotopyCategory.quotient
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf R))
      (ComplexShape.up ℤ)).map φ)) :=
  (DerivedCategory.isIso_Qh_map_iff _).2 ((HomotopyCategory.quotient_map_mem_quasiIso_iff _).2 hφ)

/-- Tensoring with `M` on the homotopy category, at a morphism coming from a morphism of
complexes: it is invertible as soon as the degreewise tensor product of that morphism of
complexes is a quasi-isomorphism. -/
theorem isIso_map_tensorRightHomotopy_quotient_map
    (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₀))
    {A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₀)) ℤ}
      (φ : A ⟶ B)
    (hφ : QuasiIso (((tensorRight O₀ M).mapHomologicalComplex (ComplexShape.up ℤ)).map φ)) :
    IsIso ((tensorRightHomotopy.{d₀} M).map
      ((HomotopyCategory.quotient (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₀))
        (ComplexShape.up ℤ)).map φ)) := by
  rw [Functor.comp_map, Functor.mapHomotopyCategory_map]
  exact isIso_Qh_map_quotient_map O₀ _ hφ

/-- **A quasi-isomorphism into the extension of scalars of a `P`-cellular complex, out of a
`P`-cellular complex, stays invertible after tensoring with `M`.**

Tag 0DIX replaces `S` by a quasi-isomorphic `G` whose extension of scalars maps to `Y₀` over
`q`; resolving `G` by a `P`-cellular `Z` (Stacks 06XX) gives a quasi-isomorphism `Z ⟶ S` of
`P`-cellular complexes and a morphism `k : O₀ ⊗_O Z ⟶ Y₀` of `K(Mod(O₀))` whose composite with
`q` is the extension of scalars of `Z ⟶ S`. Stacks 0794, applied to `(- ⊗_O O₀) ⊗_{O₀} M`,
makes that composite invertible after tensoring with `M`, so `k` becomes a split monomorphism
there; applied to `- ⊗_{O₀} M` at a `P`-cellular resolution of `O₀ ⊗_O Z`, whose composite with
`k` is a quasi-isomorphism between `P`-cellular objects, it makes `k` a split epimorphism there.
A split monomorphism which is a split epimorphism is invertible, and then so is the image of
`q`. -/
theorem isIso_map_tensorRightHomotopy_of_isPCellular (f : O ⟶ O₀)
    (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₀))
    {S : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)) ℤ}
    (hS : IsPCellular (flatObjects O) S)
    {Y₀ : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₀)) ℤ}
    (hY₀ : IsPCellular (flatObjects O₀) Y₀)
    (q : Y₀ ⟶ (extensionOfScalarsCochainComplex J f).obj S) (hq : QuasiIso q) :
    IsIso ((tensorRightHomotopy.{d₀} M).map
      ((HomotopyCategory.quotient (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₀))
        (ComplexShape.up ℤ)).map q)) := by
  -- Tag 0DIX: a quasi-isomorphism `g : G ⟶ S` whose extension of scalars factors through `q`
  obtain ⟨G, g, hg, h, hfac⟩ :=
    exists_quasiIso_with_extensionOfScalars_factorization_of_hom J f S Y₀ q hq
  -- a `P`-cellular resolution `v : Z ⟶ G`
  obtain ⟨Z₁, hZ₁, r, hr⟩ := exists_cellular_quasiIso O
    ((HomotopyCategory.quotient (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O))
      (ComplexShape.up ℤ)).obj G)
  obtain ⟨Z, hZ, ⟨eZ⟩⟩ := hZ₁
  obtain ⟨v, hvq, -⟩ := exists_quasiIso_quotient_map_eq O eZ r hr
  have hvg : QuasiIso (v ≫ g) := quasiIso_comp v g
  -- the two applications of Stacks 0794 on the `O`-side
  have hEc : QuasiIso ((extensionOfScalarsCochainComplex J f).map (v ≫ g)) := by
    rw [extensionOfScalarsCochainComplex_eq]
    exact quasiIso_map_extensionOfScalars f hZ hS (v ≫ g) hvg
  have hET : QuasiIso (((tensorRight O₀ M).mapHomologicalComplex (ComplexShape.up ℤ)).map
      ((extensionOfScalarsCochainComplex J f).map (v ≫ g))) := by
    rw [extensionOfScalarsCochainComplex_eq]
    exact quasiIso_map_extensionTensorRight f M hZ hS (v ≫ g) hvg
  -- the comparison `k` of the resolution of `G` with `Y₀`, read over `q`
  have hkfac :
    ((HomotopyCategory.quotient (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₀))
          (ComplexShape.up ℤ)).map ((extensionOfScalarsCochainComplex J f).map v) ≫ h) ≫
        (HomotopyCategory.quotient (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₀))
          (ComplexShape.up ℤ)).map q =
      (HomotopyCategory.quotient (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₀))
          (ComplexShape.up ℤ)).map ((extensionOfScalarsCochainComplex J f).map (v ≫ g)) := by
    rw [Category.assoc, ← hfac, ← Functor.map_comp, ← Functor.map_comp]
  -- `k` is a quasi-isomorphism, because its composite with `q` is one
  have hkQh : IsIso (DerivedCategory.Qh.map
      ((HomotopyCategory.quotient (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₀))
        (ComplexShape.up ℤ)).map ((extensionOfScalarsCochainComplex J f).map v) ≫ h)) := by
    have hcomp : IsIso (DerivedCategory.Qh.map
        ((HomotopyCategory.quotient (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₀))
            (ComplexShape.up ℤ)).map ((extensionOfScalarsCochainComplex J f).map v) ≫ h) ≫
          DerivedCategory.Qh.map
            ((HomotopyCategory.quotient
              (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₀))
              (ComplexShape.up ℤ)).map q)) := by
      rw [← Functor.map_comp, hkfac]
      exact isIso_Qh_map_quotient_map O₀ _ hEc
    have := isIso_Qh_map_quotient_map O₀ q hq
    have := hcomp
    exact IsIso.of_isIso_comp_right _ (DerivedCategory.Qh.map
      ((HomotopyCategory.quotient (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₀))
        (ComplexShape.up ℤ)).map q))
  have hkq := (DerivedCategory.isIso_Qh_map_iff _).1 hkQh
  -- tensoring with `M`: the composite with `q` is invertible
  have hsplitMono : IsIso ((tensorRightHomotopy.{d₀} M).map
        ((HomotopyCategory.quotient (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₀))
            (ComplexShape.up ℤ)).map ((extensionOfScalarsCochainComplex J f).map v) ≫ h) ≫
      (tensorRightHomotopy.{d₀} M).map
        ((HomotopyCategory.quotient (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₀))
          (ComplexShape.up ℤ)).map q)) := by
    rw [← Functor.map_comp, hkfac]
    exact isIso_map_tensorRightHomotopy_quotient_map M _ hET
  -- and so is its composite with a `P`-cellular resolution of `O₀ ⊗_O Z`
  obtain ⟨Y₁, hY₁, w₁, hw₁⟩ := exists_cellular_quasiIso O₀
    ((HomotopyCategory.quotient (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₀))
      (ComplexShape.up ℤ)).obj ((extensionOfScalarsCochainComplex J f).obj Z))
  have hsplitEpi : IsIso ((tensorRightHomotopy.{d₀} M).map w₁ ≫
      (tensorRightHomotopy.{d₀} M).map
        ((HomotopyCategory.quotient (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₀))
            (ComplexShape.up ℤ)).map ((extensionOfScalarsCochainComplex J f).map v) ≫ h)) := by
    rw [← Functor.map_comp]
    exact isIso_map_tensorRightHomotopy_of_cellular O₀ M _
      (MorphismProperty.comp_mem _ _ _ hw₁ hkq) hY₁ (cellular_quotient_obj O₀ hY₀)
  have hk : IsIso ((tensorRightHomotopy.{d₀} M).map
      ((HomotopyCategory.quotient (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₀))
        (ComplexShape.up ℤ)).map ((extensionOfScalarsCochainComplex J f).map v) ≫ h)) :=
    isIso_of_isIso_comp_of_isIso_comp _ _ _ hsplitMono hsplitEpi
  have := hk
  have := hsplitMono
  exact IsIso.of_isIso_comp_left ((tensorRightHomotopy.{d₀} M).map
    ((HomotopyCategory.quotient (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₀))
      (ComplexShape.up ℤ)).map ((extensionOfScalarsCochainComplex J f).map v) ≫ h)) _

/-- The class `Deformation.ComplexLift.tensorResolving` is invariant under isomorphism. -/
theorem tensorResolving_of_iso (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₀))
    {T T' : HomotopyCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₀))
      (ComplexShape.up ℤ)}
    (e : T ≅ T') (hT' : tensorResolving.{d₀} M T') : tensorResolving.{d₀} M T := by
  intro Y w hw hY
  have h : IsIso ((tensorRightHomotopy.{d₀} M).map (w ≫ e.hom)) :=
    hT' Y (w ≫ e.hom) (MorphismProperty.comp_mem _ _ _ hw (MorphismProperty.of_isIso _ e.hom)) hY
  rw [Functor.map_comp] at h
  have := h
  exact IsIso.of_isIso_comp_right ((tensorRightHomotopy.{d₀} M).map w)
    ((tensorRightHomotopy.{d₀} M).map e.hom)

/-- **The extension of scalars of a `P`-cellular object of `K(Mod(O))` lies in the class
`Deformation.ComplexLift.tensorResolving`.** -/
theorem tensorResolving_obj_mapHomotopyCategory_extensionOfScalars (f : O ⟶ O₀)
    (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₀))
    {X : HomotopyCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O))
      (ComplexShape.up ℤ)}
    (hX : cellular (flatObjects O) X) :
    tensorResolving.{d₀} M
      (((extensionOfScalars f).mapHomotopyCategory (ComplexShape.up ℤ)).obj X) := by
  obtain ⟨S, hS, ⟨eX⟩⟩ := hX
  refine tensorResolving_of_iso M
    (((extensionOfScalars f).mapHomotopyCategory (ComplexShape.up ℤ)).mapIso eX ≪≫
      ((extensionOfScalars f).mapHomotopyCategoryFactors (ComplexShape.up ℤ)).app S) ?_
  intro Y w hw hY
  obtain ⟨Y₀, hY₀, ⟨eY⟩⟩ := hY
  obtain ⟨q, hqq, hq⟩ := exists_quasiIso_quotient_map_eq O₀ eY w hw
  have h : IsIso ((tensorRightHomotopy.{d₀} M).map
      ((HomotopyCategory.quotient (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₀))
        (ComplexShape.up ℤ)).map q)) :=
    isIso_map_tensorRightHomotopy_of_isPCellular f M hS hY₀ q hqq
  rw [hq, Functor.map_comp] at h
  have := h
  exact IsIso.of_isIso_comp_left ((tensorRightHomotopy.{d₀} M).map eY.inv)
    ((tensorRightHomotopy.{d₀} M).map w)

/-- **The comparison of the derived tensor product `- ⊗_{O₀}^L M` with the degreewise tensor
product is invertible at the extension of scalars of a `P`-cellular object**, `P` being the
flat sheaves of modules.

The comparison is invertible on any class of objects which resolves `K(Mod(O₀))` and between
whose objects the degreewise tensor product inverts quasi-isomorphisms
(`CategoryTheory.LeftDerivedByResolutions.isIso_app_of_resolutions`); the class
`Deformation.ComplexLift.tensorResolving` is such a class, and it contains the extension of
scalars of a `P`-cellular object. -/
theorem isIso_derivedTensorRightCounitHomotopy_app_extensionOfScalars (f : O ⟶ O₀)
    (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₀))
    (X : HomotopyCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O))
      (ComplexShape.up ℤ))
    (hX : cellular (flatObjects O) X) :
    IsIso ((derivedTensorRightCounitHomotopy.{d₀} M).app
      (((extensionOfScalars f).mapHomotopyCategory (ComplexShape.up ℤ)).obj X)) :=
  CategoryTheory.LeftDerivedByResolutions.isIso_app_of_resolutions
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₀))
      (ComplexShape.up ℤ))
    (tensorResolving.{d₀} M) (exists_tensorResolving_quasiIso M) (tensorRightHomotopy M)
    (fun s hs hA hB ↦ isIso_map_tensorRightHomotopy_of_tensorResolving M s hs hA hB)
    DerivedCategory.Qh (derivedTensorRight M) (derivedTensorRightCounitHomotopy M) _
    (tensorResolving_obj_mapHomotopyCategory_extensionOfScalars f M hX)

end Cellular

end Deformation.ComplexLift

end

end
