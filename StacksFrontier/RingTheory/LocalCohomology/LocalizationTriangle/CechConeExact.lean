module

public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import StacksFrontier.CategoryTheory.Sites.Cohomology.MayerVietoris.CanonicalMapOfComplexes
public import StacksFrontier.RingTheory.LocalCohomology.AffineLocalizationTriangle
public import StacksFrontier.RingTheory.LocalCohomology.LocalizationTriangle
public import StacksFrontier.RingTheory.LocalCohomology.LowDegree.LocalizationData
public import StacksFrontier.RingTheory.LocalCohomology.LocalizationTriangle.CechExact
public import StacksFrontier.CategoryTheory.Sites.Cohomology.MayerVietoris.CanonicalMapOfComplexes

/-!
# Derived sections away from `V(I)` form an exact functor of the module

Let `A` be a commutative ring and `f₁, …, f_r ∈ A` generators of an ideal `I`. Derived sections on
`U = Spec A ∖ V(I)` are modelled by `Stacks.LocalCohomology.cechComplementFunctor`, the cone of the
augmentation `C^•(f₁, …, f_r; M) ⟶ M⟦0⟧` of the extended alternating Čech complex. The cone of a
morphism of cochain complexes is, in each degree, a biproduct of a term of the source shifted by
one and a term of the target, so it is an exact functor of `M` as soon as both complexes are: the
Čech complex is, and so is a module placed in degree zero.

Consequently a short exact sequence of `A`-modules gives a **distinguished triangle of derived
sections on `U`**, and therefore a long exact sequence relating the sections and the higher
cohomology of the three modules. Stacks 0EII compares `Γ(U, M̃)` with the inverse limit of
`Γ(U, (M/fⁿM)̃)`, and the kernel and cokernel of the comparison at level `n` are read off the
sequences attached to `0 → fⁿM → M → M/fⁿM → 0` and `0 → M[fⁿ] → M → fⁿM → 0`.

## Main definitions

* `Stacks.LocalCohomology.cechComplementTriangle` — the triangle of derived sections on `U`
  attached to a short exact sequence of modules.

## Main results

* `Stacks.LocalCohomology.shortExact_map_cechConeFunctor` — a short exact sequence of modules
  induces a short exact sequence of cones of the Čech augmentation.
* `Stacks.LocalCohomology.cechComplementTriangle_distinguished` — **the distinguished triangle of
  derived sections on `U` attached to a short exact sequence of modules.**
* `Stacks.LocalCohomology.cechConeFunctor_map_smul` — derived sections on `U` are an `A`-linear
  functor: multiplication by a scalar induces multiplication by that scalar.
* `Stacks.LocalCohomology.exact_homologyComplement_map`,
  `Stacks.LocalCohomology.exact_homologyComplement_δ`,
  `Stacks.LocalCohomology.exact_δ_homologyComplement`,
  `Stacks.LocalCohomology.injective_homologyComplement_zero_map` — the long exact sequence of that
  triangle, in elementwise form.

## References

* [Stacks Project, Tag 0A6R](https://stacks.math.columbia.edu/tag/0A6R)
* [Stacks Project, Tag 0EII](https://stacks.math.columbia.edu/tag/0EII)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated CochainComplex

attribute [local instance] HasDerivedCategory.standard

universe w v u

namespace Stacks.LocalCohomology

/-! ### The two coordinates of a mapping cone -/

section Cone

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasBinaryBiproducts C]
  {K₁ L₁ K₂ L₂ K₃ L₃ : CochainComplex C ℤ}
  (φ₁ : K₁ ⟶ L₁) (φ₂ : K₂ ⟶ L₂) (a : K₁ ⟶ K₂) (b : L₁ ⟶ L₂) (comm : φ₁ ≫ b = a ≫ φ₂)

/-- The map of cones induced by a commutative square is additive in the square. -/
theorem mappingConeMap_add (a' : K₁ ⟶ K₂) (b' : L₁ ⟶ L₂) (comm' : φ₁ ≫ b' = a' ≫ φ₂)
    (comms : φ₁ ≫ (b + b') = (a + a') ≫ φ₂) :
    mappingCone.map φ₁ φ₂ (a + a') (b + b') comms =
      mappingCone.map φ₁ φ₂ a b comm + mappingCone.map φ₁ φ₂ a' b' comm' := by
  ext p
  rw [mappingCone.ext_from_iff φ₁ (p + 1) p rfl]
  refine ⟨?_, ?_⟩ <;> simp [mappingCone.map]

/-- The map of cones induced by a commutative square is linear in the square. -/
theorem mappingConeMap_smul {R : Type*} [Ring R] [Linear R C] (t : R)
    (comms : φ₁ ≫ (t • b) = (t • a) ≫ φ₂) :
    mappingCone.map φ₁ φ₂ (t • a) (t • b) comms = t • mappingCone.map φ₁ φ₂ a b comm := by
  ext p
  rw [mappingCone.ext_from_iff φ₁ (p + 1) p rfl]
  refine ⟨?_, ?_⟩ <;> simp [mappingCone.map]

end Cone

/-! ### Short exactness of a map of cones, degree by degree -/

section ModuleCone

variable {A : Type u} [CommRing A]
  {K₁ L₁ K₂ L₂ K₃ L₃ : CochainComplex (ModuleCat.{w} A) ℤ}
  (φ₁ : K₁ ⟶ L₁) (φ₂ : K₂ ⟶ L₂) (φ₃ : K₃ ⟶ L₃)
  (a : K₁ ⟶ K₂) (b : L₁ ⟶ L₂) (comm : φ₁ ≫ b = a ≫ φ₂)

/-- An element of the cone is determined by its two coordinates. -/
theorem coneExt {p : ℤ} {x y : (mappingCone φ₁).X p}
    (hf : (mappingCone.fst φ₁).1.v p (p + 1) rfl x = (mappingCone.fst φ₁).1.v p (p + 1) rfl y)
    (hs : (mappingCone.snd φ₁).v p p (add_zero p) x =
      (mappingCone.snd φ₁).v p p (add_zero p) y) : x = y := by
  have hid : ∀ z : (mappingCone φ₁).X p,
      (mappingCone.inl φ₁).v (p + 1) p (by lia)
          ((mappingCone.fst φ₁).1.v p (p + 1) rfl z) +
        (mappingCone.inr φ₁).f p ((mappingCone.snd φ₁).v p p (add_zero p) z) = z := by
    intro z
    have h : (((mappingCone.fst φ₁).1.v p (p + 1) rfl ≫
          (mappingCone.inl φ₁).v (p + 1) p (by lia)) +
        ((mappingCone.snd φ₁).v p p (add_zero p) ≫ (mappingCone.inr φ₁).f p)) z =
        (𝟙 ((mappingCone φ₁).X p)) z := by
      rw [mappingCone.id_X φ₁ p (p + 1) rfl]
    simpa using h
  rw [← hid x, ← hid y, hf, hs]

/-- The first coordinate of the image of an element under a map of cones. -/
theorem coneFst_mappingConeMap (p : ℤ) (x : (mappingCone φ₁).X p) :
    (mappingCone.fst φ₂).1.v p (p + 1) rfl ((mappingCone.map φ₁ φ₂ a b comm).f p x) =
      a.f (p + 1) ((mappingCone.fst φ₁).1.v p (p + 1) rfl x) := by
  have h : ((mappingCone.map φ₁ φ₂ a b comm).f p ≫
      (mappingCone.fst φ₂).1.v p (p + 1) rfl) x =
      ((mappingCone.fst φ₁).1.v p (p + 1) rfl ≫ a.f (p + 1)) x := by
    rw [MappingCoconeAux.coneMap_f_fst_v _ _ _ _ _ _ (p + 1) rfl]
  simpa using h

/-- The second coordinate of the image of an element under a map of cones. -/
theorem coneSnd_mappingConeMap (p : ℤ) (x : (mappingCone φ₁).X p) :
    (mappingCone.snd φ₂).v p p (add_zero p) ((mappingCone.map φ₁ φ₂ a b comm).f p x) =
      b.f p ((mappingCone.snd φ₁).v p p (add_zero p) x) := by
  have h : ((mappingCone.map φ₁ φ₂ a b comm).f p ≫
      (mappingCone.snd φ₂).v p p (add_zero p)) x =
      ((mappingCone.snd φ₁).v p p (add_zero p) ≫ b.f p) x := by
    rw [MappingCoconeAux.coneMap_f_snd_v]
  simpa using h

/-- The first coordinate of the first inclusion into the cone is the identity. -/
theorem coneFst_inl (p : ℤ) (u : K₁.X (p + 1)) :
    (mappingCone.fst φ₁).1.v p (p + 1) rfl
      ((mappingCone.inl φ₁).v (p + 1) p (by lia) u) = u := by
  rw [← ConcreteCategory.comp_apply, mappingCone.inl_v_fst_v]
  simp

/-- The first coordinate of the second inclusion into the cone vanishes. -/
theorem coneFst_inr (p : ℤ) (w : L₁.X p) :
    (mappingCone.fst φ₁).1.v p (p + 1) rfl ((mappingCone.inr φ₁).f p w) = 0 := by
  rw [← ConcreteCategory.comp_apply, mappingCone.inr_f_fst_v]
  simp

/-- The second coordinate of the first inclusion into the cone vanishes. -/
theorem coneSnd_inl (p : ℤ) (u : K₁.X (p + 1)) :
    (mappingCone.snd φ₁).v p p (add_zero p)
      ((mappingCone.inl φ₁).v (p + 1) p (by lia) u) = 0 := by
  rw [← ConcreteCategory.comp_apply, mappingCone.inl_v_snd_v]
  simp

/-- The second coordinate of the second inclusion into the cone is the identity. -/
theorem coneSnd_inr (p : ℤ) (w : L₁.X p) :
    (mappingCone.snd φ₁).v p p (add_zero p) ((mappingCone.inr φ₁).f p w) = w := by
  rw [← ConcreteCategory.comp_apply, mappingCone.inr_f_snd_v]
  simp

/-- Any pair of coordinates is realized by an element of the cone. -/
theorem exists_cone_of_coordinates (p : ℤ) (u : K₁.X (p + 1)) (w : L₁.X p) :
    ∃ x : (mappingCone φ₁).X p,
      (mappingCone.fst φ₁).1.v p (p + 1) rfl x = u ∧
        (mappingCone.snd φ₁).v p p (add_zero p) x = w := by
  refine ⟨(mappingCone.inl φ₁).v (p + 1) p (by lia) u + (mappingCone.inr φ₁).f p w, ?_, ?_⟩
  · rw [map_add, coneFst_inl, coneFst_inr, add_zero]
  · rw [map_add, coneSnd_inl, coneSnd_inr, zero_add]

/-- An element of the target cone is hit as soon as both of its coordinates are. -/
theorem exists_mappingConeMap_eq (p : ℤ) {y : (mappingCone φ₂).X p}
    (u : K₁.X (p + 1)) (hu : a.f (p + 1) u = (mappingCone.fst φ₂).1.v p (p + 1) rfl y)
    (w : L₁.X p) (hw : b.f p w = (mappingCone.snd φ₂).v p p (add_zero p) y) :
    ∃ x, (mappingCone.map φ₁ φ₂ a b comm).f p x = y := by
  obtain ⟨x, hx₁, hx₂⟩ := exists_cone_of_coordinates φ₁ p u w
  exact ⟨x, coneExt φ₂ (by rw [coneFst_mappingConeMap φ₁ φ₂ a b comm, hx₁, hu])
    (by rw [coneSnd_mappingConeMap φ₁ φ₂ a b comm, hx₂, hw])⟩

/-- A degreewise injective square induces an injective map of cones. -/
theorem mappingConeMap_f_injective (p : ℤ) (ha : Function.Injective (a.f (p + 1)))
    (hb : Function.Injective (b.f p)) :
    Function.Injective ((mappingCone.map φ₁ φ₂ a b comm).f p) := by
  intro x y hxy
  refine coneExt φ₁ (ha ?_) (hb ?_)
  · rw [← coneFst_mappingConeMap φ₁ φ₂ a b comm, ← coneFst_mappingConeMap φ₁ φ₂ a b comm, hxy]
  · rw [← coneSnd_mappingConeMap φ₁ φ₂ a b comm, ← coneSnd_mappingConeMap φ₁ φ₂ a b comm, hxy]

/-- A degreewise surjective square induces a surjective map of cones. -/
theorem mappingConeMap_f_surjective (p : ℤ) (ha : Function.Surjective (a.f (p + 1)))
    (hb : Function.Surjective (b.f p)) :
    Function.Surjective ((mappingCone.map φ₁ φ₂ a b comm).f p) := fun y ↦
  let ⟨u, hu⟩ := ha ((mappingCone.fst φ₂).1.v p (p + 1) rfl y)
  let ⟨w, hw⟩ := hb ((mappingCone.snd φ₂).v p p (add_zero p) y)
  exists_mappingConeMap_eq φ₁ φ₂ a b comm p u hu w hw

/-- **A degreewise exact pair of squares induces an exact pair of maps of cones.** -/
theorem mappingConeMap_f_exact (a' : K₂ ⟶ K₃) (b' : L₂ ⟶ L₃) (comm' : φ₂ ≫ b' = a' ≫ φ₃)
    (p : ℤ) (ha : Function.Exact (a.f (p + 1)) (a'.f (p + 1)))
    (hb : Function.Exact (b.f p) (b'.f p)) :
    Function.Exact ((mappingCone.map φ₁ φ₂ a b comm).f p)
      ((mappingCone.map φ₂ φ₃ a' b' comm').f p) := by
  refine fun y ↦ ⟨fun hy ↦ ?_, ?_⟩
  · obtain ⟨u, hu⟩ := (ha ((mappingCone.fst φ₂).1.v p (p + 1) rfl y)).1 (by
      rw [← coneFst_mappingConeMap φ₂ φ₃ a' b' comm', hy, map_zero])
    obtain ⟨w, hw⟩ := (hb ((mappingCone.snd φ₂).v p p (add_zero p) y)).1 (by
      rw [← coneSnd_mappingConeMap φ₂ φ₃ a' b' comm', hy, map_zero])
    exact exists_mappingConeMap_eq φ₁ φ₂ a b comm p u hu w hw
  · rintro ⟨x, rfl⟩
    refine coneExt φ₃ ?_ ?_
    · rw [coneFst_mappingConeMap φ₂ φ₃ a' b' comm', coneFst_mappingConeMap φ₁ φ₂ a b comm,
        (ha _).2 ⟨_, rfl⟩, map_zero]
    · rw [coneSnd_mappingConeMap φ₂ φ₃ a' b' comm', coneSnd_mappingConeMap φ₁ φ₂ a b comm,
        (hb _).2 ⟨_, rfl⟩, map_zero]

end ModuleCone

/-! ### Derived sections on the complement as an exact functor -/

section Complement

variable {R : Type u} [CommRing R] {r : ℕ} (f : Fin r → R)
  {M N : ModuleCat.{max u v} R}

/-- The map of Čech cones is the cone map of any square whose sides are the induced maps. -/
private theorem cechConeFunctor_map_eq_mappingConeMap (g : M ⟶ N)
    {a : extendedCechComplex f M ⟶ extendedCechComplex f N}
    {b : (CochainComplex.singleFunctor (ModuleCat.{max u v} R) 0).obj M ⟶
      (CochainComplex.singleFunctor (ModuleCat.{max u v} R) 0).obj N}
    (ha : extendedCechComplexMap f g = a)
    (hb : (CochainComplex.singleFunctor (ModuleCat.{max u v} R) 0).map g = b) :
    (cechConeFunctor.{v} f).map g = mappingCone.map _ _ a b
      (by subst ha hb; exact (extendedCechAugmentation_naturality f g).symm) :=
  mappingCone_map_congr _ _ ha hb (extendedCechAugmentation_naturality f g).symm _

/-- The cone of the Čech augmentation is additive in the module map. -/
theorem cechConeFunctor_map_add (g h : M ⟶ N) :
    (cechConeFunctor.{v} f).map (g + h) =
      (cechConeFunctor.{v} f).map g + (cechConeFunctor.{v} f).map h := by
  rw [cechConeFunctor_map_eq_mappingConeMap f (g + h) (extendedCechComplexMap_add f g h)
    (Functor.map_add _)]
  exact mappingConeMap_add _ _ _ _ (extendedCechAugmentation_naturality f g).symm _ _
    (extendedCechAugmentation_naturality f h).symm _

/-- The cone of the Čech augmentation is an additive functor of the module. -/
instance cechConeFunctor_additive (f : Fin r → R) : (cechConeFunctor.{v} f).Additive where
  map_add {_ _ g h} := cechConeFunctor_map_add f g h

/-- **Derived sections on `U` are an `R`-linear functor of the module**: the map of cones induced
by multiplication by a scalar is multiplication by that scalar. -/
theorem cechConeFunctor_map_smul (a : R) (g : M ⟶ N) :
    (cechConeFunctor.{v} f).map (a • g) = a • (cechConeFunctor.{v} f).map g := by
  rw [cechConeFunctor_map_eq_mappingConeMap f (a • g) (extendedCechComplexMap_smul f a g)
    (Functor.map_smul _ a g)]
  exact mappingConeMap_smul _ _ _ _ (extendedCechAugmentation_naturality f g).symm a _

/-- **A short exact sequence of modules induces a short exact sequence of cones of the Čech
augmentation.** -/
theorem shortExact_map_cechConeFunctor (S : ShortComplex (ModuleCat.{max u v} R))
    (hS : S.ShortExact) : (S.map (cechConeFunctor.{v} f)).ShortExact := by
  have hC := (HomologicalComplex.shortExact_iff_degreewise_shortExact
    (S.map (extendedCechFunctor.{v} f))).1 (shortExact_map_extendedCechFunctor.{v} f S hS)
  have hM := (HomologicalComplex.shortExact_iff_degreewise_shortExact
    (S.map (HomologicalComplex.single (ModuleCat.{max u v} R) (ComplexShape.up ℤ) 0))).1
    (hS.map_of_exact (HomologicalComplex.single (ModuleCat.{max u v} R) (ComplexShape.up ℤ) 0))
  refine HomologicalComplex.shortExact_of_degreewise_shortExact _ fun p ↦ ?_
  refine ModuleCat.shortComplex_shortExact _ ?_ ?_ ?_
  · exact mappingConeMap_f_exact _ _ _ _ _
      (extendedCechAugmentation_naturality f S.f).symm _ _
      (extendedCechAugmentation_naturality f S.g).symm p
      ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1 (hC (p + 1)).exact)
      ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1 (hM p).exact)
  · exact mappingConeMap_f_injective _ _ _ _
      (extendedCechAugmentation_naturality f S.f).symm p
      (hC (p + 1)).moduleCat_injective_f (hM p).moduleCat_injective_f
  · exact mappingConeMap_f_surjective _ _ _ _
      (extendedCechAugmentation_naturality f S.g).symm p
      (hC (p + 1)).moduleCat_surjective_g (hM p).moduleCat_surjective_g

/-- **The triangle of derived sections on `U = Spec R ∖ V(I)` attached to a short exact sequence of
modules.** Its first two maps are the maps of derived sections induced by the two maps of the short
exact sequence, and its third is the connecting map of the short exact sequence of cones. -/
def cechComplementTriangle (S : ShortComplex (ModuleCat.{max u v} R)) (hS : S.ShortExact) :
    Triangle (DerivedCategory (ModuleCat.{max u v} R)) :=
  Triangle.mk ((cechComplementFunctor.{v} f).map S.f) ((cechComplementFunctor.{v} f).map S.g)
    (DerivedCategory.triangleOfSESδ (shortExact_map_cechConeFunctor.{v} f S hS))

/-- **The triangle of derived sections on `U` attached to a short exact sequence of modules is
distinguished**, so the cohomology of derived sections on `U` of the three modules forms a long
exact sequence. -/
theorem cechComplementTriangle_distinguished (S : ShortComplex (ModuleCat.{max u v} R))
    (hS : S.ShortExact) :
    cechComplementTriangle.{v} f S hS ∈ distTriang (DerivedCategory (ModuleCat.{max u v} R)) :=
  DerivedCategory.triangleOfSES_distinguished (shortExact_map_cechConeFunctor.{v} f S hS)

/-! ### The long exact sequence of derived sections on the complement -/

/-- Exactness at the middle term: in every degree the cohomology of derived sections on `U` of a
short exact sequence of modules is exact at the middle module. -/
theorem exact_homologyComplement_map (S : ShortComplex (ModuleCat.{max u v} R))
    (hS : S.ShortExact) (n : ℤ) :
    Function.Exact
      ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} R) n).map
        ((cechComplementFunctor.{v} f).map S.f))
      ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} R) n).map
        ((cechComplementFunctor.{v} f).map S.g)) :=
  (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
    (DerivedCategory.HomologySequence.exact₂ (cechComplementTriangle.{v} f S hS)
      (cechComplementTriangle_distinguished.{v} f S hS) n)

/-- Exactness at the third term: the cokernel of the map induced on degree-`n₀` cohomology of
derived sections on `U` is measured by the connecting map into degree `n₀ + 1` of the first
module. -/
theorem exact_homologyComplement_δ (S : ShortComplex (ModuleCat.{max u v} R))
    (hS : S.ShortExact) (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) :
    Function.Exact
      ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} R) n₀).map
        ((cechComplementFunctor.{v} f).map S.g))
      (DerivedCategory.HomologySequence.δ (cechComplementTriangle.{v} f S hS) n₀ n₁ h) :=
  (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
    (DerivedCategory.HomologySequence.exact₃ (cechComplementTriangle.{v} f S hS)
      (cechComplementTriangle_distinguished.{v} f S hS) n₀ n₁ h)

/-- Exactness at the first term one degree up: the kernel of the map induced on degree-`n₁`
cohomology of derived sections on `U` is the image of the connecting map. -/
theorem exact_δ_homologyComplement (S : ShortComplex (ModuleCat.{max u v} R))
    (hS : S.ShortExact) (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) :
    Function.Exact
      (DerivedCategory.HomologySequence.δ (cechComplementTriangle.{v} f S hS) n₀ n₁ h)
      ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} R) n₁).map
        ((cechComplementFunctor.{v} f).map S.f)) :=
  (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
    (DerivedCategory.HomologySequence.exact₁ (cechComplementTriangle.{v} f S hS)
      (cechComplementTriangle_distinguished.{v} f S hS) n₀ n₁ h)

/-- Derived sections on `U` in the Čech model have no negative cohomology. -/
theorem isZero_homologyComplement_of_neg (M : ModuleCat.{max u v} R) (i : ℤ) (hi : i < 0) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} R) i).obj
      ((cechComplementFunctor.{v} f).obj M)) :=
  isZero_homology_complement_of_neg
    (cechLocalizationTriangleData.{v} f (Ideal.span (Set.range f))
      (Submodule.fg_span (Set.finite_range f)) rfl) M i hi

/-- **Sections on `U = Spec R ∖ V(I)` are left exact.** For a short exact sequence of modules the
map on degree-zero cohomology of derived sections on `U` induced by the first map is injective. -/
theorem injective_homologyComplement_zero_map (S : ShortComplex (ModuleCat.{max u v} R))
    (hS : S.ShortExact) :
    Function.Injective
      ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} R) 0).map
        ((cechComplementFunctor.{v} f).map S.f)) :=
  (ModuleCat.mono_iff_injective _).1
    ((DerivedCategory.HomologySequence.mono_homologyMap_mor₁_iff
      (cechComplementTriangle.{v} f S hS)
      (cechComplementTriangle_distinguished.{v} f S hS) (-1) 0 (by lia)).2
      ((isZero_homologyComplement_of_neg.{v} f S.X₃ (-1) (by lia)).eq_of_src _ _))

end Complement

end Stacks.LocalCohomology

end
