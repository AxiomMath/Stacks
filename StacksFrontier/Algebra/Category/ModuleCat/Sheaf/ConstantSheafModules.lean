module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Kernels
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.Algebra.Module.Shrink
public import Mathlib.CategoryTheory.Linear.FunctorCategory
public import Mathlib.CategoryTheory.Linear.LinearFunctor
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.RingTheory.Flat.Tensor
public import StacksFrontier.RingTheory.Coherent.Basic
public import StacksCore.Tactic.StacksAttribute

/-!
# Sections of constant sheaves of modules

Let `(C, J)` be a site and `R` a commutative ring. The constant sheaf functor
`constantSheaf J (ModuleCat.{x} R)` sends an `R`-module to the sheafification of the constant
presheaf with that value, and composing with the sections over an object `U` of the site gives a
functor `constantSections J U : ModuleCat.{x} R ⥤ ModuleCat.{x} R`. This file establishes that
this functor is exact and deduces the two consequences recorded in Stacks Tags 093K and 093L:
tensoring with a finitely presented module commutes with taking sections of a constant sheaf, and
sections of the constant sheaf on a flat module over a coherent ring are flat.

## Main definitions

* `Stacks.ConstantSheaf.constantSections`: the functor `M ↦ Γ(U, M̲)` sending an `R`-module to the
  sections over `U` of the constant sheaf it generates.
* `Stacks.ConstantSheaf.constantSectionsMapLinear`: the action of `constantSections` on morphisms,
  as an `R`-linear map `(M →ₗ[R] N) →ₗ[R] (Γ(U, M̲) →ₗ[R] Γ(U, N̲))`.
* `Stacks.ConstantSheaf.tensorComparison`: the canonical comparison
  `Γ(U, M̲) ⊗[R] Q →ₗ[R] Γ(U, N̲)` attached to a linear equivalence `M ⊗[R] Q ≃ₗ[R] N`,
  specified on pure tensors by `s ⊗ₜ q ↦ Γ(U, (m ↦ e (m ⊗ₜ q))̲) s`.

## Main results

* `Stacks.ConstantSheaf.small_tensorProduct_of_finite`: a tensor product with a finite module has a
  representative in the universe of the first factor.
* `Stacks.ConstantSheaf.surjective_constantSections_map`: **Stacks Tag 093J**, the surjectivity
  half. `constantSections` takes surjections of modules to surjections.
* `Stacks.ConstantSheaf.range_constantSections_map_eq_ker`: **Stacks Tag 093J**. The functor
  `constantSections` is exact: it takes an exact pair of morphisms to an exact pair. The
  injectivity half is `Stacks.ConstantSheaf.injective_constantSections_map`.
* `Stacks.ConstantSheaf.bijective_tensorComparison`: **Stacks Tag 093K**. The comparison
  `Γ(U, M̲) ⊗[R] Q → Γ(U, (M ⊗[R] Q)̲)` is bijective when `Q` is finitely presented.
* `Stacks.ConstantSheaf.flat_constantSections`: **Stacks Tag 093L**. Over a coherent ring, the
  sections of the constant sheaf on a flat module are flat.

## Implementation notes

Three instance hypotheses beyond the existence of a weak sheafification are used, and all three
are genuinely needed rather than chosen for convenience.

`HasSheafify J (ModuleCat.{x} R)` (rather than only `HasWeakSheafify`) is what makes sheafification
left exact, via `Mathlib`'s instance `PreservesFiniteLimits (presheafToSheaf J A)`. Left exactness
is used for `injective_constantSections_map` and for the containment
`ker (Γ(U, β̲)) ⊆ range (Γ(U, α̲))`, which is the whole content of Tag 093J beyond formal
additivity; it cannot be derived from `HasWeakSheafify` alone.

`HasWeakSheafify J (Type x)`, `J.PreservesSheafification (forget (ModuleCat.{x} R))` and
`J.HasSheafCompose (forget (ModuleCat.{x} R))` are what make the *surjectivity* half work. The
Stacks proof of Tag 093J proves surjectivity of `Γ(U, B̲) → Γ(U, C̲)` for a surjection `B → C` by
choosing a set-theoretic section `C → B`, which is a morphism of types and not of modules; the
argument therefore has to pass through the constant sheaf of *sets*, and it is transported back
along `constantCommuteCompose J (forget (ModuleCat.{x} R))`. There is no route to this through the
module category alone: a surjection of modules is in general not split, so no module-valued
section exists.

The universes of the site (`u`, `v`), of the ring (`w`) and of the module sections (`x`) stay
independent; nothing here forces `x` to contain `max u v`. The hypotheses above are what an
instantiation must discharge, and for `x = max u v` they are all **derivable** in `Mathlib` —
but not, for a general site, by `infer_instance`. `HasSheafify J (ModuleCat.{x} R)` additionally
wants `PreservesColimitsOfShape (J.Cover X)ᵒᵖ (forget (ModuleCat.{x} R))`, which is reachable
only through `preservesFilteredColimitsOfSize_of_univLE` — a lemma, not an instance. Supplying
that once (exactly as is done for `AddCommGrpCat`) makes both `HasSheafify` and
`HasWeakSheafify` synthesize. Derivable is not automatic: a consumer that expects instance search
to discharge these hypotheses will find that it does not.

`constantSections` is a composite of functors rather than a new definition, so that its value is
definitionally the sheaf-sections of the constant sheaf and no transport is needed to compare it
with other formulations.

## References

* [Stacks Project, Tag 093J](https://stacks.math.columbia.edu/tag/093J)
* [Stacks Project, Tag 093K](https://stacks.math.columbia.edu/tag/093K)
* [Stacks Project, Tag 093L](https://stacks.math.columbia.edu/tag/093L)
-/

@[expose] public section

open CategoryTheory Limits Opposite

universe u v w x y

namespace Stacks.ConstantSheaf

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

/-! ### Left exactness of sections and of the constant sheaf

Nothing about the ring enters these two, so they are stated for an arbitrary — possibly
noncommutative — ring, which is what the finite type locally constant sheaves of Tag 093U need.
-/

section LeftExact

variable {R : Type w} [Ring R] [HasSheafify J (ModuleCat.{x} R)]

/-- Sections over a fixed object preserve finite limits: `sheafToPresheaf` is a right adjoint and
evaluation of presheaves preserves finite limits. -/
noncomputable instance sheafSections_preservesFiniteLimits (U : C) :
    PreservesFiniteLimits ((sheafSections J (ModuleCat.{x} R)).obj (op U)) :=
  comp_preservesFiniteLimits (sheafToPresheaf J (ModuleCat.{x} R))
    ((evaluation Cᵒᵖ (ModuleCat.{x} R)).obj (op U))

/-- The constant sheaf functor preserves finite limits: the constant-presheaf functor preserves
all limits, and sheafification is left exact. -/
noncomputable instance constantSheaf_preservesFiniteLimits :
    PreservesFiniteLimits (constantSheaf J (ModuleCat.{x} R)) :=
  comp_preservesFiniteLimits (Functor.const Cᵒᵖ) (presheafToSheaf J (ModuleCat.{x} R))

end LeftExact

variable {R : Type w} [CommRing R]

/-! ### Tensor products with finite modules stay small -/

/-- Tensoring with a finitely generated module does not enlarge the universe needed to represent
the first factor. In particular a representative of `M ⊗[R] Q` in the universe of `M` can always
be chosen using `Shrink`. -/
theorem small_tensorProduct_of_finite (M : ModuleCat.{x} R) (Q : ModuleCat.{y} R)
    [Module.Finite R Q] : Small.{x} (TensorProduct R M Q) := by
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' R Q
  exact small_of_surjective ((LinearMap.lTensor_surjective M hf).comp
    (TensorProduct.piScalarRight R R M (Fin n)).symm.surjective)

/-! ### Linearity and additivity of sheafification -/

section Sheafify

variable [HasWeakSheafify J (ModuleCat.{x} R)]

/-- Sheafification of presheaves of `R`-modules is `R`-linear. -/
instance presheafToSheaf_linear :
    Functor.Linear R (presheafToSheaf J (ModuleCat.{x} R)) := by
  let adj := sheafificationAdjunction J (ModuleCat.{x} R)
  constructor
  intro X Y f r
  apply (adj.homEquiv X ((presheafToSheaf J (ModuleCat.{x} R)).obj Y)).injective
  change adj.unit.app X ≫ (sheafToPresheaf J (ModuleCat.{x} R)).map
      ((presheafToSheaf J (ModuleCat.{x} R)).map (r • f)) =
    adj.unit.app X ≫ (sheafToPresheaf J (ModuleCat.{x} R)).map
      (r • (presheafToSheaf J (ModuleCat.{x} R)).map f)
  have hnat (g : X ⟶ Y) : g ≫ adj.unit.app Y =
      adj.unit.app X ≫ (sheafToPresheaf J (ModuleCat.{x} R)).map
        ((presheafToSheaf J (ModuleCat.{x} R)).map g) := by
    simpa only [Functor.comp_map, Functor.id_map] using adj.unit.naturality g
  rw [← hnat, CategoryTheory.Linear.smul_comp, hnat, Functor.map_smul,
    ← CategoryTheory.Linear.comp_smul]

/-- Sheafification of presheaves of `R`-modules is additive. -/
instance presheafToSheaf_additive :
    (presheafToSheaf J (ModuleCat.{x} R)).Additive := by
  let adj := sheafificationAdjunction J (ModuleCat.{x} R)
  constructor
  intro X Y f g
  apply (adj.homEquiv X ((presheafToSheaf J (ModuleCat.{x} R)).obj Y)).injective
  change adj.unit.app X ≫ (sheafToPresheaf J (ModuleCat.{x} R)).map
      ((presheafToSheaf J (ModuleCat.{x} R)).map (f + g)) =
    adj.unit.app X ≫ (sheafToPresheaf J (ModuleCat.{x} R)).map
      ((presheafToSheaf J (ModuleCat.{x} R)).map f +
       (presheafToSheaf J (ModuleCat.{x} R)).map g)
  have hnat (k : X ⟶ Y) : k ≫ adj.unit.app Y =
      adj.unit.app X ≫ (sheafToPresheaf J (ModuleCat.{x} R)).map
        ((presheafToSheaf J (ModuleCat.{x} R)).map k) := by
    simpa only [Functor.comp_map, Functor.id_map] using adj.unit.naturality k
  rw [← hnat, Functor.map_add, Preadditive.comp_add, ← hnat, ← hnat,
    Preadditive.add_comp]

end Sheafify

/-! ### Additivity and linearity of the pieces of the constant sheaf functor -/

/-- The constant-presheaf functor is additive. -/
instance constFunctor_additive :
    (Functor.const Cᵒᵖ : ModuleCat.{x} R ⥤ Cᵒᵖ ⥤ ModuleCat.{x} R).Additive := ⟨rfl⟩

/-- The constant-presheaf functor is `R`-linear. -/
instance constFunctor_linear : Functor.Linear R
    (Functor.const Cᵒᵖ : ModuleCat.{x} R ⥤ Cᵒᵖ ⥤ ModuleCat.{x} R) := ⟨fun _ _ => rfl⟩

/-- Taking sections of a sheaf of modules over a fixed object is additive. -/
instance sheafSections_additive [HasWeakSheafify J (ModuleCat.{x} R)] (X : Cᵒᵖ) :
    ((sheafSections J (ModuleCat.{x} R)).obj X).Additive := ⟨rfl⟩

/-- Taking sections of a sheaf of modules over a fixed object is `R`-linear. -/
instance sheafSections_linear [HasWeakSheafify J (ModuleCat.{x} R)] (X : Cᵒᵖ) :
    Functor.Linear R ((sheafSections J (ModuleCat.{x} R)).obj X) := ⟨fun _ _ => rfl⟩

/-! ### The sections of a constant sheaf -/

section Sections

variable [HasWeakSheafify J (ModuleCat.{x} R)]

/-- The sections over `U` of the constant sheaf generated by an `R`-module, as a functor of that
module. This is the functor written `M ↦ Γ(U, M̲)` in the Stacks Project. -/
noncomputable abbrev constantSections (U : C) : ModuleCat.{x} R ⥤ ModuleCat.{x} R :=
  constantSheaf J (ModuleCat.{x} R) ⋙ (sheafSections J (ModuleCat.{x} R)).obj (op U)

/-- The functor `constantSections J U` is additive. -/
instance constantSections_additive (U : C) :
    (constantSections J U (R := R)).Additive :=
  inferInstanceAs (Functor.Additive
    (Functor.const Cᵒᵖ ⋙ presheafToSheaf J (ModuleCat.{x} R) ⋙
      (sheafSections J (ModuleCat.{x} R)).obj (op U)))

/-- The functor `constantSections J U` is `R`-linear. -/
instance constantSections_linear (U : C) : Functor.Linear R (constantSections J U (R := R)) :=
  inferInstanceAs (Functor.Linear R
    (Functor.const Cᵒᵖ ⋙ presheafToSheaf J (ModuleCat.{x} R) ⋙
      (sheafSections J (ModuleCat.{x} R)).obj (op U)))

/-- The action of `constantSections` on morphisms, packaged as an `R`-linear map. -/
noncomputable def constantSectionsMapLinear (M N : ModuleCat.{x} R) (U : C) :
    (M →ₗ[R] N) →ₗ[R]
      ((constantSections J U).obj M) →ₗ[R] ((constantSections J U).obj N) :=
  ModuleCat.homLinearEquiv.toLinearMap ∘ₗ (constantSections J U).mapLinearMap R ∘ₗ
    ModuleCat.homLinearEquiv.symm.toLinearMap

/-- `constantSectionsMapLinear` sends `f` to the map `constantSections J U` induces from `f`. -/
@[simp]
theorem constantSectionsMapLinear_apply (M N : ModuleCat.{x} R) (U : C) (f : M →ₗ[R] N)
    (s : (constantSections J U).obj M) :
    constantSectionsMapLinear J M N U f s =
      ((constantSections J U).map (ModuleCat.ofHom f)).hom s :=
  rfl

end Sections

/-! ### Tag 093J, surjectivity: a surjection of modules stays surjective on sections

The Stacks proof chooses a set-theoretic section of the surjection. Such a section is a morphism
of types, not of modules, so the argument is run in the constant sheaf of *sets* and transported
back along `constantCommuteCompose`.
-/

section Surjective

variable [HasWeakSheafify J (ModuleCat.{x} R)] [HasWeakSheafify J (Type x)]
  [J.PreservesSheafification (forget (ModuleCat.{x} R))]
  [J.HasSheafCompose (forget (ModuleCat.{x} R))]

/-- The sections over `U` of the constant sheaf of sets generated by a type. -/
noncomputable abbrev typeConstantSections (U : C) : Type x ⥤ Type x :=
  constantSheaf J (Type x) ⋙ (sheafSections J (Type x)).obj (op U)

/-- Sections of a constant sheaf of sets take surjections to surjections: a surjection of types
is split, and the splitting is carried along by the functor. -/
theorem surjective_typeConstantSections_map {X Y : Type x} (g : X ⟶ Y)
    (hg : Function.Surjective g) (U : C) :
    Function.Surjective ((typeConstantSections J U).map g) := by
  intro t
  let s : Y ⟶ X := TypeCat.ofHom (Function.surjInv hg)
  refine ⟨((typeConstantSections J U).map s) t, ?_⟩
  have h : s ≫ g = 𝟙 Y := by
    ext y
    exact Function.surjInv_eq hg y
  have h2 : (typeConstantSections J U).map s ≫ (typeConstantSections J U).map g = 𝟙 _ := by
    rw [← CategoryTheory.Functor.map_comp, h, CategoryTheory.Functor.map_id]
  simpa using ConcreteCategory.congr_hom h2 t

/-- The underlying sets of the sections of a constant sheaf of modules are the sections of the
constant sheaf of sets on the underlying set. This is `constantCommuteCompose` for the forgetful
functor, read off over a fixed object of the site. -/
noncomputable def forgetConstantSectionsIso (U : C) :
    constantSections J U (R := R) ⋙ forget (ModuleCat.{x} R) ≅
      forget (ModuleCat.{x} R) ⋙ typeConstantSections J U :=
  Functor.isoWhiskerRight (constantCommuteCompose J (forget (ModuleCat.{x} R)))
    ((sheafSections J (Type x)).obj (op U))

/-- **Stacks Tag 093J**, surjectivity half. If `f : M ⟶ N` is a surjection of `R`-modules then
the induced map on the sections over `U` of the associated constant sheaves is surjective. -/
@[stacks 093J "surjectivity"]
theorem surjective_constantSections_map {M N : ModuleCat.{x} R} (f : M ⟶ N)
    (hf : Function.Surjective f.hom) (U : C) :
    Function.Surjective ((constantSections J U).map f).hom := by
  set Φ := forgetConstantSectionsIso J U (R := R)
  have hbij (X : ModuleCat.{x} R) : Function.Bijective (Φ.hom.app X) :=
    (isIso_iff_bijective (Φ.hom.app X)).mp inferInstance
  have main : Function.Surjective
      ((constantSections J U (R := R) ⋙ forget (ModuleCat.{x} R)).map f) := by
    intro t
    obtain ⟨z, hz⟩ := surjective_typeConstantSections_map J
      ((forget (ModuleCat.{x} R)).map f) hf U ((Φ.hom.app N) t)
    obtain ⟨s, hs⟩ := (hbij M).surjective z
    refine ⟨s, (hbij N).injective ?_⟩
    have hnat := ConcreteCategory.congr_hom (Φ.hom.naturality f) s
    simp only [types_comp_apply] at hnat
    rw [hnat, hs]
    exact hz
  exact main

end Surjective

/-! ### Tag 093J, exactness -/

section Exact

variable [HasSheafify J (ModuleCat.{x} R)]

/-- The functor `constantSections J U` preserves finite limits. -/
noncomputable instance constantSections_preservesFiniteLimits (U : C) :
    PreservesFiniteLimits (constantSections J U (R := R)) :=
  comp_preservesFiniteLimits _ _

/-- **Stacks Tag 093J**, injectivity half. `constantSections` takes injections of modules to
injections. -/
@[stacks 093J "injectivity"]
theorem injective_constantSections_map {M N : ModuleCat.{x} R} (f : M ⟶ N)
    (hf : Function.Injective f.hom) (U : C) :
    Function.Injective ((constantSections J U).map f).hom := by
  have hmono : Mono f := (ModuleCat.mono_iff_injective f).mpr hf
  exact (ModuleCat.mono_iff_injective _).mp ((constantSections J U (R := R)).map_mono f)

/-- Precomposing with a surjection does not change the range. -/
private theorem range_comp_of_surjective {A B D : ModuleCat.{x} R} (a : A ⟶ B) (b : B ⟶ D)
    (ha : Function.Surjective a.hom) :
    LinearMap.range (a ≫ b).hom = LinearMap.range b.hom := by
  rw [ModuleCat.hom_comp, LinearMap.range_comp, LinearMap.range_eq_top.mpr ha,
    Submodule.map_top]

/-- An isomorphism of modules is surjective. -/
private theorem surjective_of_isIso {A B : ModuleCat.{x} R} (a : A ⟶ B) [IsIso a] :
    Function.Surjective a.hom :=
  (ModuleCat.epi_iff_surjective a).mp inferInstance


/-- Precomposing with an isomorphism does not change the range. -/
private theorem range_comp_of_isIso {A B D : ModuleCat.{x} R} (a : A ⟶ B) [IsIso a] (b : B ⟶ D) :
    LinearMap.range (a ≫ b).hom = LinearMap.range b.hom :=
  range_comp_of_surjective a b ((ModuleCat.epi_iff_surjective a).mp inferInstance)

/-- Sections of a constant sheaf take the kernel of a morphism to the kernel: the image of the
sections of the kernel inclusion is exactly the kernel of the sections of the morphism. This is
where left exactness of sheafification is used. -/
theorem range_constantSections_kerSubtype (U : C) {B D : ModuleCat.{x} R} (β : B ⟶ D) :
    LinearMap.range
        ((constantSections J U).map (ModuleCat.ofHom (LinearMap.ker β.hom).subtype)).hom =
      LinearMap.ker ((constantSections J U).map β).hom := by
  set F := constantSections J U (R := R)
  -- the kernel inclusion factors the canonical `kernel.ι` through `ModuleCat.kernelIsoKer`
  have hι : ModuleCat.ofHom (LinearMap.ker β.hom).subtype =
      (ModuleCat.kernelIsoKer β).inv ≫ kernel.ι β := by
    rw [ModuleCat.kernelIsoKer_inv_kernel_ι]
  have step₁ : LinearMap.range
      (F.map (ModuleCat.ofHom (LinearMap.ker β.hom).subtype)).hom =
      LinearMap.range (F.map (kernel.ι β)).hom := by
    rw [hι, F.map_comp]
    exact range_comp_of_isIso _ _
  have step₂ : LinearMap.range (F.map (kernel.ι β)).hom =
      LinearMap.range (kernel.ι (F.map β)).hom := by
    rw [← kernelComparison_comp_ι β F]
    exact range_comp_of_isIso _ _
  have step₃ : LinearMap.range (kernel.ι (F.map β)).hom =
      LinearMap.ker (F.map β).hom := by
    rw [← ModuleCat.kernelIsoKer_hom_ker_subtype (F.map β),
      range_comp_of_isIso]
    exact Submodule.range_subtype _
  rw [step₁, step₂, step₃]

end Exact

/-! ### Tag 093J: `constantSections` is exact -/

section ExactPair

variable [HasSheafify J (ModuleCat.{x} R)] [HasWeakSheafify J (Type x)]
  [J.PreservesSheafification (forget (ModuleCat.{x} R))]
  [J.HasSheafCompose (forget (ModuleCat.{x} R))]

/-- **Stacks Tag 093J**. The functor of sections of a constant sheaf of modules is exact: an exact
pair of morphisms of `R`-modules is taken to an exact pair. -/
@[stacks 093J]
theorem range_constantSections_map_eq_ker (U : C) {A B D : ModuleCat.{x} R}
    (α : A ⟶ B) (β : B ⟶ D) (h : LinearMap.range α.hom = LinearMap.ker β.hom) :
    LinearMap.range ((constantSections J U).map α).hom =
      LinearMap.ker ((constantSections J U).map β).hom := by
  have hmem (a : A) : α.hom a ∈ LinearMap.ker β.hom := h ▸ LinearMap.mem_range_self _ a
  let α₀ : A ⟶ ModuleCat.of R (LinearMap.ker β.hom) :=
    ModuleCat.ofHom (LinearMap.codRestrict (LinearMap.ker β.hom) α.hom hmem)
  have hfac : α₀ ≫ ModuleCat.ofHom (LinearMap.ker β.hom).subtype = α := by
    ext a
    rfl
  have hsurj : Function.Surjective α₀.hom := fun y => by
    obtain ⟨a, ha⟩ : (y : B) ∈ LinearMap.range α.hom := by rw [h]; exact y.2
    exact ⟨a, Subtype.ext ha⟩
  rw [← hfac, (constantSections J U (R := R)).map_comp,
    range_comp_of_surjective _ _ (surjective_constantSections_map J α₀ hsurj U)]
  exact range_constantSections_kerSubtype J U β

end ExactPair

/-! ### Finite powers of a module -/

section Pi

variable [HasWeakSheafify J (ModuleCat.{x} R)]

/-- The `i`-th projection out of a finite power of a module. -/
noncomputable def piProj {n : ℕ} (M : ModuleCat.{x} R) (i : Fin n) :
    ModuleCat.of R (Fin n → M) ⟶ M :=
  ModuleCat.ofHom (LinearMap.proj i)

/-- The `i`-th inclusion into a finite power of a module. -/
noncomputable def piIncl {n : ℕ} (M : ModuleCat.{x} R) (i : Fin n) :
    M ⟶ ModuleCat.of R (Fin n → M) :=
  ModuleCat.ofHom (LinearMap.single R (fun _ : Fin n => (M : Type x)) i)

/-- The underlying linear map of `piProj M i` is `LinearMap.proj i`. -/
theorem piProj_hom {n : ℕ} (M : ModuleCat.{x} R) (i : Fin n) :
    (piProj M i).hom = LinearMap.proj i := rfl

/-- The underlying linear map of `piIncl M i` is `LinearMap.single R _ i`. -/
theorem piIncl_hom {n : ℕ} (M : ModuleCat.{x} R) (i : Fin n) :
    (piIncl M i).hom = LinearMap.single R (fun _ : Fin n => (M : Type x)) i := rfl

/-- The sum over `i : Fin n` of `piProj M i ≫ piIncl M i` is the identity of `Fin n → M`. -/
theorem sum_piProj_comp_piIncl {n : ℕ} (M : ModuleCat.{x} R) :
    ∑ i : Fin n, piProj M i ≫ piIncl M i = 𝟙 (ModuleCat.of R (Fin n → M)) := by
  apply ModuleCat.hom_ext
  rw [ModuleCat.hom_sum, ModuleCat.hom_id,
    Finset.sum_congr rfl fun (i : Fin n) _ =>
      show (piProj M i ≫ piIncl M i).hom =
        (LinearMap.single R (fun _ : Fin n => (M : Type x)) i) ∘ₗ LinearMap.proj i from rfl]
  ext v j
  simp [Pi.single_apply]

/-- The `i`-th inclusion followed by the `i`-th projection is the identity of `M`: that is,
`piIncl M i ≫ piProj M i = 𝟙 M`. -/
theorem piIncl_comp_piProj_self {n : ℕ} (M : ModuleCat.{x} R) (i : Fin n) :
    piIncl M i ≫ piProj M i = 𝟙 M := by
  apply ModuleCat.hom_ext
  rw [ModuleCat.hom_id,
    show (piIncl M i ≫ piProj M i).hom =
      (LinearMap.proj i) ∘ₗ LinearMap.single R (fun _ : Fin n => (M : Type x)) i from rfl]
  ext a
  simp

/-- For `i ≠ j`, the `j`-th inclusion followed by the `i`-th projection is zero. That is,
`piIncl M j ≫ piProj M i = 0`. -/
theorem piIncl_comp_piProj_of_ne {n : ℕ} (M : ModuleCat.{x} R) {i j : Fin n} (h : i ≠ j) :
    piIncl M j ≫ piProj M i = 0 := by
  apply ModuleCat.hom_ext
  rw [ModuleCat.hom_zero,
    show (piIncl M j ≫ piProj M i).hom =
      (LinearMap.proj i) ∘ₗ LinearMap.single R (fun _ : Fin n => (M : Type x)) j from rfl]
  ext a
  simp [h]

/-- A section of a constant sheaf on a finite power of `M` is the sum of the sections obtained
from its components. This is additivity of `constantSections` applied to the biproduct
decomposition of `Fin n → M`. -/
theorem constantSections_eq_sum_piIncl (U : C) {n : ℕ} (M : ModuleCat.{x} R)
    (z : (constantSections J U).obj (ModuleCat.of R (Fin n → M))) :
    z = ∑ i : Fin n, ((constantSections J U).map (piIncl M i)).hom
        (((constantSections J U).map (piProj M i)).hom z) := by
  have h : (∑ i : Fin n, (constantSections J U).map (piProj M i ≫ piIncl M i)) = 𝟙 _ := by
    rw [← CategoryTheory.Functor.map_sum, sum_piProj_comp_piIncl,
      CategoryTheory.Functor.map_id]
  simpa [CategoryTheory.Functor.map_comp] using (ConcreteCategory.congr_hom h z).symm

/-- Reading off one component of the decomposition above. -/
theorem constantSections_piProj_sum (U : C) {n : ℕ} (M : ModuleCat.{x} R)
    (s : Fin n → (constantSections J U).obj M) (i : Fin n) :
    ((constantSections J U).map (piProj M i)).hom
        (∑ j : Fin n, ((constantSections J U).map (piIncl M j)).hom (s j)) = s i := by
  rw [map_sum, Finset.sum_eq_single_of_mem i (Finset.mem_univ i)]
  · rw [← ModuleCat.comp_apply, ← CategoryTheory.Functor.map_comp, piIncl_comp_piProj_self]
    simp
  · intro j _ hj
    rw [← ModuleCat.comp_apply, ← CategoryTheory.Functor.map_comp,
      piIncl_comp_piProj_of_ne M (Ne.symm hj), CategoryTheory.Functor.map_zero]
    simp

end Pi

/-! ### Tag 093K: tensoring with a finitely presented module -/

section Tensor

/-- The inverse of `TensorProduct.piScalarRight`, written as a sum of pure tensors. -/
theorem piScalarRight_symm_apply {X : Type x} [AddCommGroup X] [Module R X]
    (n : ℕ) (v : Fin n → X) :
    (TensorProduct.piScalarRight R R X (Fin n)).symm v
      = ∑ i, v i ⊗ₜ[R] (Pi.single i 1 : Fin n → R) := by
  rw [LinearEquiv.symm_apply_eq]
  ext j
  simp [Pi.single_apply]

variable [HasWeakSheafify J (ModuleCat.{x} R)]

/-- The canonical comparison for an external module `Q`, with `e` identifying its tensor product
with `M` by a module in the universe where sections are taken. Its value on `s ⊗ₜ q` is induced
by the linear map `m ↦ e (m ⊗ₜ q)`. -/
noncomputable def tensorComparison (M : ModuleCat.{x} R) (Q : ModuleCat.{y} R)
    (N : ModuleCat.{x} R) (e : TensorProduct R M Q ≃ₗ[R] N) (U : C) :
    { f : TensorProduct R ((constantSections J U).obj M) Q →ₗ[R]
        ((constantSections J U).obj N) //
      ∀ (s : (constantSections J U).obj M) (q : Q),
        f (s ⊗ₜ[R] q) =
          ((constantSections J U).map
            (ModuleCat.ofHom (e.toLinearMap ∘ₗ (TensorProduct.mk R M Q).flip q))) s } :=
  ⟨TensorProduct.lift ((constantSectionsMapLinear J M N U ∘ₗ
      ((LinearMap.llcomp R M (TensorProduct R M Q) N e.toLinearMap) ∘ₗ
        (TensorProduct.mk R M Q).flip)).flip), fun _ _ => rfl⟩

end Tensor


/-- Writing a vector of ring elements as a combination of the standard basis. -/
theorem sum_smul_piSingle {n : ℕ} (c : Fin n → R) :
    ∑ i, c i • (Pi.single i 1 : Fin n → R) = c := by
  funext k
  rw [Finset.sum_apply]
  simp [Pi.single_apply]


/-- The `i`-th component of the image of an assembled section under a morphism of finite powers
whose matrix entries are `A`. -/
theorem constantSections_piProj_comp [HasWeakSheafify J (ModuleCat.{x} R)] (U : C)
    {n m : ℕ} (M : ModuleCat.{x} R)
    (cc : ModuleCat.of R (Fin m → M) ⟶ ModuleCat.of R (Fin n → M))
    (A : Fin m → Fin n → R)
    (hcc : ∀ j i, piIncl M j ≫ cc ≫ piProj M i = (A j i) • 𝟙 M)
    (w : Fin m → (constantSections J U).obj M) (i : Fin n) :
    ((constantSections J U).map (piProj M i)).hom
        (((constantSections J U).map cc).hom
          (∑ j, ((constantSections J U).map (piIncl M j)).hom (w j)))
      = ∑ j, A j i • w j := by
  rw [map_sum, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← ModuleCat.comp_apply, ← ModuleCat.comp_apply, ← CategoryTheory.Functor.map_comp,
    ← CategoryTheory.Functor.map_comp, hcc j i,
    CategoryTheory.Functor.map_smul, CategoryTheory.Functor.map_id]
  simp

section Bijective

variable [HasSheafify J (ModuleCat.{x} R)] [HasWeakSheafify J (Type x)]
  [J.PreservesSheafification (forget (ModuleCat.{x} R))]
  [J.HasSheafCompose (forget (ModuleCat.{x} R))]

/-- **Stacks Tag 093K.** Tensoring with a finitely presented external module commutes with taking
sections of a constant sheaf: the canonical comparison is bijective. -/
@[stacks 093K]
theorem bijective_tensorComparison (M : ModuleCat.{x} R) (Q : ModuleCat.{y} R)
    [Module.FinitePresentation R Q] (N : ModuleCat.{x} R)
    (e : TensorProduct R M Q ≃ₗ[R] N) (U : C) :
    Function.Bijective (tensorComparison J M Q N e U).1 := by
  classical
  obtain ⟨n, m, ψ, a, hψ, hexact⟩ := Module.FinitePresentation.exists_fin' R (Q : Type y)
  set T := constantSections J U (R := R) with hTdef
  set θ := (tensorComparison J M Q N e U).1 with hθdef
  -- the chosen generators of `Q` and the relations among them
  set q : Fin n → Q := fun i => ψ (Pi.single i 1) with hqdef
  set A : Fin m → Fin n → R := fun j => a (Pi.single j 1) with hAdef
  set φn := TensorProduct.piScalarRight R R (M : Type x) (Fin n) with hφn
  set φm := TensorProduct.piScalarRight R R (M : Type x) (Fin m) with hφm
  -- the presentation of `N` by a finite power of `M`
  set gg : ModuleCat.of R (Fin n → M) ⟶ N :=
    ModuleCat.ofHom (e.toLinearMap ∘ₗ LinearMap.lTensor (M : Type x) ψ ∘ₗ
      φn.symm.toLinearMap) with hggdef
  set cc : ModuleCat.of R (Fin m → M) ⟶ ModuleCat.of R (Fin n → M) :=
    ModuleCat.ofHom (φn.toLinearMap ∘ₗ LinearMap.lTensor (M : Type x) a ∘ₗ
      φm.symm.toLinearMap) with hccdef
  set gq : Fin n → (M ⟶ N) := fun i =>
    ModuleCat.ofHom (e.toLinearMap ∘ₗ (TensorProduct.mk R M Q).flip (q i)) with hgqdef
  have hgg_hom : gg.hom = e.toLinearMap ∘ₗ LinearMap.lTensor (M : Type x) ψ ∘ₗ
      φn.symm.toLinearMap := rfl
  have hcc_hom : cc.hom = φn.toLinearMap ∘ₗ LinearMap.lTensor (M : Type x) a ∘ₗ
      φm.symm.toLinearMap := rfl
  -- `gg` is the sum of the maps `m ↦ e (m ⊗ₜ q i)` composed with the projections
  have hggsum : gg = ∑ i : Fin n, piProj M i ≫ gq i := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro v
    rw [hgg_hom, ModuleCat.hom_sum, LinearMap.sum_apply]
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe]
    rw [piScalarRight_symm_apply, map_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [gq, q, piProj]
  -- `gg` is surjective
  have hggsurj : Function.Surjective gg.hom := by
    intro t
    obtain ⟨ξ, hξ⟩ := e.surjective t
    obtain ⟨η, hη⟩ := LinearMap.lTensor_surjective (M : Type x) hψ ξ
    refine ⟨φn η, ?_⟩
    rw [hgg_hom]
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.symm_apply_apply]
    rw [hη, hξ]
  -- the image of `cc` is the kernel of `gg`
  have hexactMod : LinearMap.range cc.hom = LinearMap.ker gg.hom := by
    have h1 : LinearMap.ker gg.hom =
        Submodule.map φn.toLinearMap (LinearMap.ker (LinearMap.lTensor (M : Type x) ψ)) := by
      rw [hgg_hom, LinearMap.ker_comp, LinearEquiv.ker, ← LinearMap.ker, LinearMap.ker_comp,
        Submodule.comap_equiv_eq_map_symm φn.symm, LinearEquiv.symm_symm]
    have h2 : LinearMap.range cc.hom =
        Submodule.map φn.toLinearMap (LinearMap.range (LinearMap.lTensor (M : Type x) a)) := by
      rw [hcc_hom, LinearMap.range_comp, LinearMap.range_comp,
        LinearMap.range_eq_top.mpr φm.symm.surjective, Submodule.map_top]
    rw [h1, h2, (lTensor_exact (M : Type x) hexact hψ).linearMap_ker_eq]
  -- the components of `cc`
  have hccomp : ∀ (j : Fin m) (i : Fin n),
      piIncl M j ≫ cc ≫ piProj M i = (A j i) • 𝟙 M := by
    intro j i
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro b
    simp [piIncl_hom, piProj_hom, hcc_hom, A, hφn, hφm,
      TensorProduct.piScalarRight_symm_single, LinearMap.lTensor_tmul,
      TensorProduct.piScalarRightHom_tmul]
  -- the comparison on a sum of pure tensors
  have key : ∀ s : Fin n → T.obj M,
      θ (∑ i, s i ⊗ₜ[R] q i) = (T.map gg).hom (∑ i, (T.map (piIncl M i)).hom (s i)) := by
    intro s
    rw [map_sum, hggsum, CategoryTheory.Functor.map_sum, ModuleCat.hom_sum, LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [(tensorComparison J M Q N e U).2 (s i) (q i), CategoryTheory.Functor.map_comp]
    rw [ModuleCat.comp_apply, constantSections_piProj_sum]
  -- every element of `Γ(U, M̲) ⊗ Q` is a combination of the chosen generators
  have hgen : ∀ ξ : TensorProduct R (T.obj M) Q,
      ∃ s : Fin n → T.obj M, ξ = ∑ i, s i ⊗ₜ[R] q i := by
    intro ξ
    obtain ⟨η, hη⟩ := LinearMap.lTensor_surjective (T.obj M : Type x) hψ ξ
    set sv : Fin n → T.obj M :=
      TensorProduct.piScalarRight R R (T.obj M : Type x) (Fin n) η with hsv
    refine ⟨sv, ?_⟩
    have hηsum : η = ∑ i, sv i ⊗ₜ[R] (Pi.single i 1 : Fin n → R) := by
      rw [hsv, ← piScalarRight_symm_apply]
      exact (LinearEquiv.symm_apply_apply _ η).symm
    rw [← hη, hηsum, map_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [LinearMap.lTensor_tmul]
  refine ⟨?_, ?_⟩
  · -- injectivity
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro ξ hξ
    obtain ⟨s, rfl⟩ := hgen ξ
    rw [LinearMap.mem_ker, key s] at hξ
    -- the assembled section lies in the kernel, hence in the image of `cc`
    have hz : (∑ i, (T.map (piIncl M i)).hom (s i)) ∈
        LinearMap.ker (T.map gg).hom := hξ
    rw [← range_constantSections_map_eq_ker J U cc gg hexactMod] at hz
    obtain ⟨y, hy⟩ := hz
    set yc : Fin m → T.obj M := fun j => (T.map (piProj M j)).hom y with hyc
    have hyd : y = ∑ j, (T.map (piIncl M j)).hom (yc j) :=
      constantSections_eq_sum_piIncl J U M (n := m) y
    -- read off the components
    have hs : ∀ i, s i = ∑ j, A j i • yc j := by
      intro i
      have h1 : s i = (T.map (piProj M i)).hom (∑ k, (T.map (piIncl M k)).hom (s k)) :=
        (constantSections_piProj_sum J U M s i).symm
      rw [h1, ← hy, hyd]
      exact constantSections_piProj_comp J U M cc A hccomp yc i
    -- substitute and collapse the double sum
    calc ∑ i, s i ⊗ₜ[R] q i
        = ∑ i, ∑ j, yc j ⊗ₜ[R] (A j i • q i) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [hs i, TensorProduct.sum_tmul]
          exact Finset.sum_congr rfl fun j _ => (TensorProduct.smul_tmul _ _ _)
      _ = ∑ j, yc j ⊗ₜ[R] ∑ i, A j i • q i := by
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun j _ => by rw [TensorProduct.tmul_sum]
      _ = 0 := by
          refine Finset.sum_eq_zero fun j _ => ?_
          have : (∑ i, A j i • q i) = (0 : Q) := by
            have : (∑ i, A j i • q i) = ψ (∑ i, A j i • (Pi.single i 1 : Fin n → R)) := by
              rw [map_sum]
              exact Finset.sum_congr rfl fun i _ => by rw [map_smul]
            rw [this, sum_smul_piSingle, hAdef]
            exact hexact.apply_apply_eq_zero _
          rw [this, TensorProduct.tmul_zero]
  · -- surjectivity
    intro t
    obtain ⟨z, hz⟩ := surjective_constantSections_map J gg hggsurj U t
    refine ⟨∑ i, ((T.map (piProj M i)).hom z) ⊗ₜ[R] q i, ?_⟩
    rw [key (fun i => (T.map (piProj M i)).hom z),
      ← constantSections_eq_sum_piIncl J U M z]
    exact hz

end Bijective


/-! ### Tag 093L: flatness of the sections -/

section Flat

variable [HasSheafify J (ModuleCat.{x} R)] [HasWeakSheafify J (Type x)]
  [J.PreservesSheafification (forget (ModuleCat.{x} R))]
  [J.HasSheafCompose (forget (ModuleCat.{x} R))]

/-- **Stacks Tag 093L.** On every object of a site, the sections of the constant sheaf associated
to a flat module over a coherent ring form a flat module. -/
@[stacks 093L]
instance flat_constantSections [IsCoherentRing R] (M : ModuleCat.{x} R) [Module.Flat R M]
    (U : C) : Module.Flat R ((constantSections J U).obj M) := by
  rw [Module.Flat.iff_lTensor_injective]
  intro I hI
  have : Module.Finite R (I : Submodule R R) := Module.Finite.of_fg hI
  have hIfp : Module.FinitePresentation R (I : Submodule R R) :=
    (isCoherentRing_iff_forall_fg_ideal_finitePresentation R).mp ‹_› I hI
  have : Small.{x} (TensorProduct R M (ModuleCat.of R (I : Submodule R R))) :=
    small_tensorProduct_of_finite M (ModuleCat.of R (I : Submodule R R))
  set X := (constantSections J U).obj M
  -- the two instances of the comparison of Tag 093K
  set QI := ModuleCat.of R (I : Submodule R R)
  set NI := ModuleCat.of R (Shrink.{x} (TensorProduct R M QI))
  set eI : TensorProduct R M QI ≃ₗ[R] NI := (Shrink.linearEquiv R _).symm
  set eR : TensorProduct R M (ModuleCat.of R R) ≃ₗ[R] M := TensorProduct.rid R M with heR
  set θI := (tensorComparison J M QI NI eI U).1
  set θR := (tensorComparison J M (ModuleCat.of R R) M eR U).1
  -- the morphism `M ⊗ I → M` of modules, read through the chosen representative
  set u : NI ⟶ M := ModuleCat.ofHom
    ((TensorProduct.rid R M).toLinearMap ∘ₗ LinearMap.lTensor (M : Type x)
      (I : Submodule R R).subtype ∘ₗ eI.symm.toLinearMap) with hu
  have huinj : Function.Injective u.hom :=
    (TensorProduct.rid R (M : Type x)).injective.comp
      ((Module.Flat.iff_lTensor_injective.mp ‹Module.Flat R M› hI).comp eI.symm.injective)
  -- the comparison square, checked on pure tensors
  have hsq : θR ∘ₗ LinearMap.lTensor (X : Type x) (I : Submodule R R).subtype =
      ((constantSections J U).map u).hom ∘ₗ θI := by
    refine TensorProduct.ext' fun s ι => ?_
    have hmor : ModuleCat.ofHom (eR.toLinearMap ∘ₗ
          (TensorProduct.mk R (M : Type x) (ModuleCat.of R R)).flip
            ((I : Submodule R R).subtype ι)) =
        ModuleCat.ofHom (eI.toLinearMap ∘ₗ
          (TensorProduct.mk R (M : Type x) (QI : Type w)).flip ι) ≫ u := by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro b
      simp [hu, heR, LinearMap.lTensor_tmul]
    rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.lTensor_tmul,
      (tensorComparison J M (ModuleCat.of R R) M eR U).2 s ((I : Submodule R R).subtype ι),
      (tensorComparison J M QI NI eI U).2 s ι, ← ModuleCat.comp_apply,
      ← CategoryTheory.Functor.map_comp, ← hmor]
  -- conclude
  have hinj : Function.Injective
      (θR ∘ₗ LinearMap.lTensor (X : Type x) (I : Submodule R R).subtype) := by
    rw [hsq]
    simp only [LinearMap.coe_comp]
    exact (injective_constantSections_map J u huinj U).comp
      (bijective_tensorComparison J M QI NI eI U).injective
  simp only [LinearMap.coe_comp] at hinj
  exact hinj.of_comp

end Flat

end Stacks.ConstantSheaf
