module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjAndSpecPuncturedConeProjectionFormula
import StacksCore.Tactic.StacksAttribute

/-!
# Functoriality of `RΓ(U, 𝓕_U) = ⨁_m RΓ(P, 𝓕(m))`

Let `A` be a nonnegatively graded ring, `P = Proj A` quasi-compact, `π : L ⟶ P` the cone of the
truncation algebra `B = ⨁_{d ≥ 0} A_{≥ d}` and `U ⊆ L` the punctured cone. The decomposition

  `RΓ(U, 𝓕_U) = ⨁_{m ∈ ℤ} RΓ(P, 𝓕 ⊗_{𝒪_P} 𝒪_P(m))`

of [Stacks, Tag 0EKH] is
`Stacks.AlgebraicGeometry.ProjAndSpec.derivedPushforwardPuncturedConeIsoTruncation`. The source
adds that this direct sum decomposition is functorial in `𝓕`; this file proves it.

The isomorphism is a composite of five identifications — the composition formula for derived
direct image, the collapse of `R(π|_U)_*` on a quasi-coherent module, the projection formula along
`π|_U` together with `(π|_U)_*𝒪_U = ⨁_m 𝒪_P(m)`, and two comparisons of direct sums — and each of
them is natural. The general statement
`Stacks.AlgebraicGeometry.ProjAndSpec.derivedPushforwardPuncturedConeIso_hom_comp` records how
the composite transports a morphism of modules on `U` whose direct image is a morphism of direct
sums sending the `m`-th summand to the `p m`-th one; it is used here with `p = id` and, in
`StacksFrontier.AlgebraicGeometry.Constructions.ProjAndSpecPuncturedConeModuleStructure`, with
`p = (k + ·)` for the action of a homogeneous element of degree `k`.

## Main results

* `Stacks.AlgebraicGeometry.DerivedAffinePushforward.derivedPushforwardSingleIso_hom_naturality`:
  `(f_*𝓕)[0] ≅ Rf_*(𝓕[0])` is natural in `𝓕`, for `f` affine.
* `Stacks.AlgebraicGeometry.ProjAndSpec.derivedPushforwardPuncturedConeIso_hom_comp`: the
  decomposition transports morphisms of direct sums.
* `Stacks.AlgebraicGeometry.ProjAndSpec.puncturedConePushforwardPullbackCoproductIso_hom_naturality`
  : `(π|_U)_*(π|_U)^*𝓕 ≅ ⨁_m 𝓕(m)` is natural in `𝓕`.
* `Stacks.AlgebraicGeometry.ProjAndSpec.derivedPushforwardPuncturedConeIsoTruncation_hom_naturality`
  : **the decomposition of [Stacks, Tag 0EKH] is functorial in `𝓕`.**

## Implementation notes

The identifications above are stated with several spellings of the same categories: the derived
category of `𝒪_P`-modules appears both as `DerivedCategory (Proj A).Modules` and as
`DerivedCategory (SheafOfModules (Proj A).ringCatSheaf)`, and the tensor product of sheaves of
modules is formed over several presentations of the same sheaf of rings. These agree
definitionally but not syntactically, so `rw` cannot move between them. The proofs therefore
assemble commutative squares with the lemmas of `Stacks.AlgebraicGeometry.ProjAndSpec.Glue`, which
are stated in an arbitrary category and applied with `exact`, and every naturality statement is
first restated for abstract modules in the spelling in which it is consumed.

## References

* [Stacks Project, Tag 0EKH](https://stacks.math.columbia.edu/tag/0EKH)
* [Stacks Project, Tag 01XC](https://stacks.math.columbia.edu/tag/01XC)
* [Stacks Project, Tag 0FZE](https://stacks.math.columbia.edu/tag/0FZE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe w u u' v'

attribute [local instance] SheafOfModules.hasDerivedCategory
attribute [local implicit_reducible] AlgebraicGeometry.Scheme.Modules TopCat.Sheaf sheafCompose

namespace Stacks.AlgebraicGeometry.ProjAndSpec.Glue

/-! ### Composites of commutative squares

These lemmas assemble commutative squares into larger ones in an arbitrary category. They are
applied with `exact`, so that the categories and morphisms they are instantiated at are matched up
to definitional unfolding, which `rw` does not do. -/

variable {C D : Type*} [Category C] [Category D]

/-- Two squares, the first mapped by a functor, glue into one. -/
theorem map_square_comp (S : C ⥤ D) {X₁ X₂ X₃ X₄ : C} {Y W : D} {x : X₁ ⟶ X₂} {y : X₂ ⟶ X₃}
    {z : X₁ ⟶ X₄} {t : X₄ ⟶ X₃} {v : S.obj X₃ ⟶ Y} {w : S.obj X₄ ⟶ W} {g : W ⟶ Y}
    (k₁ : x ≫ y = z ≫ t) (k₂ : w ≫ g = S.map t ≫ v) :
    S.map x ≫ S.map y ≫ v = (S.map z ≫ w) ≫ g := by
  rw [← Functor.map_comp_assoc, k₁, Functor.map_comp_assoc, Category.assoc, k₂]

/-- A commutative square, mapped by a functor. -/
theorem map_square (S : C ⥤ D) {X₁ X₂ X₃ X₄ : C} {x : X₁ ⟶ X₂} {y : X₂ ⟶ X₃}
    {z : X₁ ⟶ X₄} {t : X₄ ⟶ X₃} (k : x ≫ y = z ≫ t) :
    S.map x ≫ S.map y = S.map z ≫ S.map t := by
  rw [← Functor.map_comp, k, Functor.map_comp]

/-- A commutative square of isomorphisms, read through their inverses. -/
theorem inv_square {X₁ X₂ Y₁ Y₂ : C} (e : Y₁ ≅ Y₂) (f : X₁ ≅ X₂) {a : X₁ ⟶ Y₁} {b : X₂ ⟶ Y₂}
    (h : a ≫ e.hom = f.hom ≫ b) : b ≫ e.inv = f.inv ≫ a := by
  rw [Iso.comp_inv_eq, Category.assoc, h, Iso.inv_hom_id_assoc]

/-- A commutative square of isomorphisms, read back through their forward morphisms. -/
theorem hom_square {X₁ X₂ Y₁ Y₂ : C} (e : Y₁ ≅ Y₂) (f : X₁ ≅ X₂) {a : X₁ ⟶ Y₁} {b : X₂ ⟶ Y₂}
    (h : b ≫ e.inv = f.inv ≫ a) : a ≫ e.hom = f.hom ≫ b := by
  rw [← Iso.inv_comp_eq, ← Category.assoc, ← h, Category.assoc, Iso.inv_hom_id,
    Category.comp_id]

/-- The uncurried form of a bifunctor, on a morphism that is the identity in the first
variable. -/
theorem uncurry_map_id_left {E : Type*} [Category E] (F : C ⥤ D ⥤ E) (X : C) {Y Y' : D}
    (k : Y ⟶ Y') :
    (Functor.uncurry.obj F).map (X := (X, Y)) (Y := (X, Y')) (𝟙 X, k) = (F.obj X).map k := by
  simp

/-- The uncurried form of a bifunctor, on a morphism whose first component is the image of an
identity under a functor. -/
theorem uncurry_map_map_id_left {B E : Type*} [Category B] [Category E] (F : C ⥤ D ⥤ E)
    (S : B ⥤ C) (X : B) {Y Y' : D} (k : Y ⟶ Y') :
    (Functor.uncurry.obj F).map (X := (S.obj X, Y)) (Y := (S.obj X, Y')) (S.map (𝟙 X), k) =
      (F.obj (S.obj X)).map k := by
  simp

/-- The uncurried form of a bifunctor, on a morphism whose second component is the image of an
identity under a functor. -/
theorem uncurry_map_map_id_right {B E : Type*} [Category B] [Category E] (F : C ⥤ D ⥤ E)
    (S : B ⥤ D) {X X' : C} (f : X ⟶ X') (Y : B) :
    (Functor.uncurry.obj F).map (X := (X, S.obj Y)) (Y := (X', S.obj Y)) (f, S.map (𝟙 Y)) =
      (F.map f).app (S.obj Y) := by
  simp

/-- The uncurried form of a bifunctor, on a morphism that is the identity in the second
variable. -/
theorem uncurry_map_id_right {E : Type*} [Category E] (F : C ⥤ D ⥤ E) {X X' : C} (f : X ⟶ X')
    (Y : D) :
    (Functor.uncurry.obj F).map (X := (X, Y)) (Y := (X', Y)) (f, 𝟙 Y) = (F.map f).app Y := by
  simp

/-- Three squares glue into one. -/
theorem square_comp₃ {X₀ X₁ X₂ X₃ Y₀ Y₁ Y₂ Y₃ : C} {a : X₀ ⟶ Y₀} {i₂ : Y₀ ⟶ Y₁}
    {k₂ : Y₁ ⟶ Y₂} {s₂ : Y₂ ⟶ Y₃} {i₁ : X₀ ⟶ X₁} {k₁ : X₁ ⟶ X₂} {s₁ : X₂ ⟶ X₃}
    {p : X₁ ⟶ Y₁} {p' : X₂ ⟶ Y₂} {q : X₃ ⟶ Y₃}
    (h₁ : a ≫ i₂ = i₁ ≫ p) (h₂ : p ≫ k₂ = k₁ ≫ p') (h₃ : p' ≫ s₂ = s₁ ≫ q) :
    a ≫ i₂ ≫ k₂ ≫ s₂ = (i₁ ≫ k₁ ≫ s₁) ≫ q := by
  rw [reassoc_of% h₁, reassoc_of% h₂, h₃, Category.assoc, Category.assoc]

/-- A square, a square mapped by a functor, and a third square glue into one. -/
theorem square_map_square (G : C ⥤ D) {X₀ Y₀ X₁ Y₁ : C} {Z₀ Z₁ W₀ W₁ : D}
    {a : Z₀ ⟶ W₀} {c₁ : W₀ ⟶ G.obj Y₀} {c₂ : Z₀ ⟶ G.obj X₀} {a' : X₀ ⟶ Y₀}
    {x' : Y₀ ⟶ Y₁} {x : X₀ ⟶ X₁} {q : X₁ ⟶ Y₁} {t₂ : G.obj Y₁ ⟶ W₁} {t₁ : G.obj X₁ ⟶ Z₁}
    {b : Z₁ ⟶ W₁}
    (hC : a ≫ c₁ = c₂ ≫ G.map a') (hin : a' ≫ x' = x ≫ q) (hS : G.map q ≫ t₂ = t₁ ≫ b) :
    a ≫ c₁ ≫ G.map x' ≫ t₂ = (c₂ ≫ G.map x ≫ t₁) ≫ b := by
  rw [reassoc_of% hC, ← Functor.map_comp_assoc, hin, Functor.map_comp_assoc, hS,
    Category.assoc, Category.assoc]

/-- Three squares, the first mapped by a functor, glue into one. -/
theorem map_square_comp₂ (S : C ⥤ D) {X₁ X₂ X₃ X₄ : C} {Y₁ Y₂ Y₃ Y₄ : D}
    {x : X₁ ⟶ X₂} {y : X₂ ⟶ X₃} {z : X₁ ⟶ X₄} {t : X₄ ⟶ X₃}
    {e : S.obj X₃ ⟶ Y₁} {f : S.obj X₄ ⟶ Y₂} {g : Y₂ ⟶ Y₁} {h : Y₁ ⟶ Y₃} {i : Y₂ ⟶ Y₄}
    {T : Y₄ ⟶ Y₃}
    (hU : x ≫ y = z ≫ t) (hP : S.map t ≫ e = f ≫ g) (hB : g ≫ h = i ≫ T) :
    S.map x ≫ S.map y ≫ e ≫ h = (S.map z ≫ f ≫ i) ≫ T := by
  rw [← Functor.map_comp_assoc, hU, Functor.map_comp_assoc, reassoc_of% hP, hB,
    Category.assoc, Category.assoc]

end Stacks.AlgebraicGeometry.ProjAndSpec.Glue

namespace Stacks.AlgebraicGeometry.DerivedAffinePushforward

variable {X S : Scheme.{u}} (f : X ⟶ S)
  [HasDerivedCategory.{w} (SheafOfModules.{u} X.ringCatSheaf)]
  [HasDerivedCategory.{w} (SheafOfModules.{u} S.ringCatSheaf)]

/-- **`(f_*𝓕)[0] ≅ Rf_*(𝓕[0])` is natural in `𝓕`**, for `f` affine and `𝓕` quasi-coherent. -/
theorem derivedPushforwardSingleIso_hom_naturality [IsAffineHom f]
    {F G : SheafOfModules.{u} X.ringCatSheaf} [F.IsQuasicoherent] [G.IsQuasicoherent]
    (φ : F ⟶ G) :
    (DerivedCategory.singleFunctor (SheafOfModules.{u} S.ringCatSheaf) 0).map
          ((pushforwardSheafOfModules f).map φ) ≫ (derivedPushforwardSingleIso.{w} f G).hom =
      (derivedPushforwardSingleIso.{w} f F).hom ≫
        (AnyModel.derivedPushforward.{w} f).map
          ((DerivedCategory.singleFunctor (SheafOfModules.{u} X.ringCatSheaf) 0).map φ) := by
  simp only [derivedPushforwardSingleIso, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_inv,
    Functor.mapIso_hom, asIso_hom, Iso.app_hom, Iso.app_inv, Category.assoc]
  have h1 :=
    (DerivedCategory.singleFunctorIsoCompQ (SheafOfModules.{u} S.ringCatSheaf) 0).hom.naturality
    ((pushforwardSheafOfModules f).map φ)
  have h2 : (CochainComplex.singleFunctor (SheafOfModules.{u} S.ringCatSheaf) 0).map
        ((pushforwardSheafOfModules f).map φ) ≫
      (HomologicalComplex.singleMapHomologicalComplex (pushforwardSheafOfModules f)
        (ComplexShape.up ℤ) 0).inv.app G =
      (HomologicalComplex.singleMapHomologicalComplex (pushforwardSheafOfModules f)
        (ComplexShape.up ℤ) 0).inv.app F ≫
      ((pushforwardSheafOfModules f).mapHomologicalComplex (ComplexShape.up ℤ)).map
        ((CochainComplex.singleFunctor (SheafOfModules.{u} X.ringCatSheaf) 0).map φ) :=
    (HomologicalComplex.singleMapHomologicalComplex (pushforwardSheafOfModules f)
      (ComplexShape.up ℤ) 0).inv.naturality φ
  have h3 := (DerivedCategory.quotientCompQhIso (SheafOfModules.{u} S.ringCatSheaf)).inv.naturality
    (((pushforwardSheafOfModules f).mapHomologicalComplex (ComplexShape.up ℤ)).map
      ((CochainComplex.singleFunctor (SheafOfModules.{u} X.ringCatSheaf) 0).map φ))
  have h4 := ((pushforwardSheafOfModules f).mapHomotopyCategoryFactors
    (ComplexShape.up ℤ)).inv.naturality
      ((CochainComplex.singleFunctor (SheafOfModules.{u} X.ringCatSheaf) 0).map φ)
  have h5 := (AnyModel.derivedPushforwardUnit.{w} f).naturality
    ((HomotopyCategory.quotient (SheafOfModules.{u} X.ringCatSheaf) (ComplexShape.up ℤ)).map
      ((CochainComplex.singleFunctor (SheafOfModules.{u} X.ringCatSheaf) 0).map φ))
  have h6 := (DerivedCategory.quotientCompQhIso (SheafOfModules.{u} X.ringCatSheaf)).hom.naturality
    ((CochainComplex.singleFunctor (SheafOfModules.{u} X.ringCatSheaf) 0).map φ)
  have h7 :=
    (DerivedCategory.singleFunctorIsoCompQ (SheafOfModules.{u} X.ringCatSheaf) 0).inv.naturality
    φ
  simp only [Functor.comp_map] at h1 h3 h4 h5 h6 h7
  have h2' := (Functor.map_comp _ _ _).symm.trans
    ((congrArg (DerivedCategory.Q (C := SheafOfModules.{u} S.ringCatSheaf)).map h2).trans
      (Functor.map_comp _ _ _))
  have h4' := (Functor.map_comp _ _ _).symm.trans
    ((congrArg (DerivedCategory.Qh (C := SheafOfModules.{u} S.ringCatSheaf)).map h4).trans
      (Functor.map_comp _ _ _))
  have h6' := (Functor.map_comp _ _ _).symm.trans
    ((congrArg (AnyModel.derivedPushforward.{w} f).map h6).trans (Functor.map_comp _ _ _))
  have h7' := (Functor.map_comp _ _ _).symm.trans
    ((congrArg (AnyModel.derivedPushforward.{w} f).map h7).trans (Functor.map_comp _ _ _))
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% h1, reassoc_of% h2', reassoc_of% h3, reassoc_of% h4', reassoc_of% h5,
    reassoc_of% h6']
  exact whisker_eq _ (whisker_eq _ (whisker_eq _ (whisker_eq _ (whisker_eq _
    (whisker_eq _ h7')))))

/-- The inverse of `derivedPushforwardSingleIso` is natural as well. -/
theorem derivedPushforwardSingleIso_inv_naturality [IsAffineHom f]
    {F G : SheafOfModules.{u} X.ringCatSheaf} [F.IsQuasicoherent] [G.IsQuasicoherent]
    (φ : F ⟶ G) :
    (AnyModel.derivedPushforward.{w} f).map
          ((DerivedCategory.singleFunctor (SheafOfModules.{u} X.ringCatSheaf) 0).map φ) ≫
        (derivedPushforwardSingleIso.{w} f G).inv =
      (derivedPushforwardSingleIso.{w} f F).inv ≫
        (DerivedCategory.singleFunctor (SheafOfModules.{u} S.ringCatSheaf) 0).map
          ((pushforwardSheafOfModules f).map φ) := by
  rw [Iso.comp_inv_eq, Category.assoc, derivedPushforwardSingleIso_hom_naturality,
    Iso.inv_hom_id_assoc]

end Stacks.AlgebraicGeometry.DerivedAffinePushforward

namespace Stacks.Duality.DerivedPushforward

attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

/-- The forward morphism of `sigmaIntSingleFunctorIso`, written out. -/
theorem sigmaIntSingleFunctorIso_hom_eq {X Y : Scheme.{u}} (f : X ⟶ Y)
    [AlgebraicGeometry.QuasiCompact f] [AlgebraicGeometry.QuasiSeparated f]
    (a : ℤ) (M : ℤ → X.Modules) :
    (sigmaIntSingleFunctorIso f a M).hom =
      (Limits.Sigma.whiskerEquiv (Equiv.ulift.{u, 0} (α := ℤ)).symm
          (g := fun k : ULift.{u, 0} ℤ => (derivedPushforward f).obj
            ((DerivedCategory.singleFunctor X.Modules a).obj (M k.down)))
          (fun _ => Iso.refl _)).hom ≫
        sigmaComparison (derivedPushforward f)
          (fun k : ULift.{u, 0} ℤ => (DerivedCategory.singleFunctor X.Modules a).obj (M k.down)) ≫
        (derivedPushforward f).map
          (Limits.Sigma.whiskerEquiv (Equiv.ulift.{u, 0} (α := ℤ))
            (f := fun k : ULift.{u, 0} ℤ =>
              (DerivedCategory.singleFunctor X.Modules a).obj (M k.down))
            (g := fun m : ℤ => (DerivedCategory.singleFunctor X.Modules a).obj (M m))
            (fun _ => Iso.refl _)).hom :=
  rfl

/-- On the `m`-th summand, `sigmaIntSingleFunctorIso` is the image of the `m`-th coproduct
inclusion under the derived direct image. -/
theorem ι_sigmaIntSingleFunctorIso_hom {X Y : Scheme.{u}} (f : X ⟶ Y)
    [AlgebraicGeometry.QuasiCompact f] [AlgebraicGeometry.QuasiSeparated f]
    (a : ℤ) (M : ℤ → X.Modules) (m : ℤ) :
    Sigma.ι (fun m : ℤ => (derivedPushforward f).obj
        ((DerivedCategory.singleFunctor X.Modules a).obj (M m))) m ≫
        (sigmaIntSingleFunctorIso f a M).hom =
      (derivedPushforward f).map
        (Sigma.ι (fun m : ℤ => (DerivedCategory.singleFunctor X.Modules a).obj (M m)) m) := by
  have h1 : Sigma.ι (fun m : ℤ => (derivedPushforward f).obj
        ((DerivedCategory.singleFunctor X.Modules a).obj (M m))) m ≫
      (Limits.Sigma.whiskerEquiv (Equiv.ulift.{u, 0} (α := ℤ)).symm
          (g := fun k : ULift.{u, 0} ℤ => (derivedPushforward f).obj
            ((DerivedCategory.singleFunctor X.Modules a).obj (M k.down)))
          (fun _ => Iso.refl _)).hom =
      Sigma.ι (fun k : ULift.{u, 0} ℤ => (derivedPushforward f).obj
            ((DerivedCategory.singleFunctor X.Modules a).obj (M k.down))) ⟨m⟩ :=
    (Sigma.ι_comp_map' _ _ _).trans (Category.id_comp _)
  have h2 : Sigma.ι (fun k : ULift.{u, 0} ℤ =>
        (DerivedCategory.singleFunctor X.Modules a).obj (M k.down)) ⟨m⟩ ≫
      (Limits.Sigma.whiskerEquiv (Equiv.ulift.{u, 0} (α := ℤ))
            (f := fun k : ULift.{u, 0} ℤ =>
              (DerivedCategory.singleFunctor X.Modules a).obj (M k.down))
            (g := fun m : ℤ => (DerivedCategory.singleFunctor X.Modules a).obj (M m))
            (fun _ => Iso.refl _)).hom =
      Sigma.ι (fun m : ℤ => (DerivedCategory.singleFunctor X.Modules a).obj (M m)) m :=
    (Sigma.ι_comp_map' _ _ _).trans (Category.id_comp _)
  rw [sigmaIntSingleFunctorIso_hom_eq]
  exact ((Category.assoc _ _ _).symm.trans (eq_whisker h1 _)).trans
    ((ι_comp_sigmaComparison_assoc _ _ _ _).trans
      ((Functor.map_comp _ _ _).symm.trans (congrArg _ h2)))

/-- `ι_sigmaIntSingleFunctorIso_hom`, followed by a further morphism. -/
theorem ι_sigmaIntSingleFunctorIso_hom_assoc {X Y : Scheme.{u}} (f : X ⟶ Y)
    [AlgebraicGeometry.QuasiCompact f] [AlgebraicGeometry.QuasiSeparated f]
    (a : ℤ) (M : ℤ → X.Modules) (m : ℤ) {Z : DerivedCategory Y.Modules}
    (h : (derivedPushforward f).obj
      (∐ fun m : ℤ => (DerivedCategory.singleFunctor X.Modules a).obj (M m)) ⟶ Z) :
    Sigma.ι (fun m : ℤ => (derivedPushforward f).obj
        ((DerivedCategory.singleFunctor X.Modules a).obj (M m))) m ≫
        (sigmaIntSingleFunctorIso f a M).hom ≫ h =
      (derivedPushforward f).map
        (Sigma.ι (fun m : ℤ => (DerivedCategory.singleFunctor X.Modules a).obj (M m)) m) ≫ h := by
  rw [← Category.assoc, ι_sigmaIntSingleFunctorIso_hom]

/-- `sigmaIntSingleFunctorIso` is compatible with a morphism of `ℤ`-indexed families that moves
the index along a map `p : ℤ → ℤ`. -/
theorem sigmaIntSingleFunctorIso_hom_map' {X Y : Scheme.{u}} (f : X ⟶ Y)
    [AlgebraicGeometry.QuasiCompact f] [AlgebraicGeometry.QuasiSeparated f]
    (a : ℤ) {M N : ℤ → X.Modules} (p : ℤ → ℤ) (b : ∀ m, M m ⟶ N (p m)) :
    (sigmaIntSingleFunctorIso f a M).hom ≫
        (derivedPushforward f).map
          (Sigma.map' p fun m => (DerivedCategory.singleFunctor X.Modules a).map (b m)) =
      Sigma.map' p (fun m => (derivedPushforward f).map
          ((DerivedCategory.singleFunctor X.Modules a).map (b m))) ≫
        (sigmaIntSingleFunctorIso f a N).hom := by
  refine Sigma.hom_ext _ _ fun m => ?_
  rw [ι_sigmaIntSingleFunctorIso_hom_assoc, ← Functor.map_comp, Sigma.ι_comp_map',
    Sigma.ι_comp_map'_assoc, ι_sigmaIntSingleFunctorIso_hom, Functor.map_comp]

/-- The coproduct comparison of a functor is compatible with a morphism of `ℤ`-indexed families
that moves the index along `p : ℤ → ℤ`. -/
theorem sigmaComparison_map' {C D : Type*} [Category C] [Category D] (G : C ⥤ D)
    {M N : ℤ → C} [HasCoproduct M] [HasCoproduct N] [HasCoproduct fun m => G.obj (M m)]
    [HasCoproduct fun m => G.obj (N m)] (p : ℤ → ℤ) (b : ∀ m, M m ⟶ N (p m)) :
    sigmaComparison G M ≫ G.map (Sigma.map' p b) =
      Sigma.map' p (fun m => G.map (b m)) ≫ sigmaComparison G N := by
  refine Sigma.hom_ext _ _ fun m => ?_
  rw [ι_comp_sigmaComparison_assoc, ← Functor.map_comp, Sigma.ι_comp_map',
    Sigma.ι_comp_map'_assoc, ι_comp_sigmaComparison, Functor.map_comp]

end Stacks.Duality.DerivedPushforward

namespace Stacks.SheafOfModules

section Naturality

open MonoidalCategory

attribute [local implicit_reducible]
  TensorSheafification.structureSheaf TensorSheafification.sheafify Tensor.ringSheaf

attribute [local instance] monoidalCategoryPresheafOfModules symmetricCategoryPresheafOfModules

variable {C : Type u'} [Category.{v'} C] {J : GrothendieckTopology C}
  (O : Cᵒᵖ ⥤ CommRingCat.{w})
  (hO : Presheaf.IsSheaf J (TensorSheafification.structureRingPresheaf O))
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]

/-- **The left unit constraint of the tensor product sheaf is natural.** -/
theorem tensorSheafLeftUnitor_hom_naturality
    {M N : _root_.SheafOfModules.{w} (TensorSheafification.structureSheaf O hO)} (g : M ⟶ N) :
    ((Tensor.sheafTensor.{u', v', w, w, w}
        ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat) hO⟩).obj
        (_root_.SheafOfModules.unit (TensorSheafification.structureSheaf O hO))).map g ≫
      (tensorSheafLeftUnitor O hO N).hom = (tensorSheafLeftUnitor O hO M).hom ≫ g := by
  have h1 : ((Tensor.sheafTensor.{u', v', w, w, w}
        ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat) hO⟩).obj
        (_root_.SheafOfModules.unit (TensorSheafification.structureSheaf O hO))).map g =
      (TensorSheafification.sheafify O hO).map (𝟙_ _ ◁ g.val) := rfl
  have h2 : ∀ P : _root_.SheafOfModules.{w} (TensorSheafification.structureSheaf O hO),
      (tensorSheafLeftUnitor O hO P).hom =
        (TensorSheafification.sheafify O hO).map (λ_ P.val).hom ≫ (sheafifyValIso O hO P).hom :=
    fun _ => rfl
  rw [h1, h2, h2]
  exact Stacks.AlgebraicGeometry.ProjAndSpec.Glue.map_square_comp _
    (MonoidalCategory.leftUnitor_naturality g.val) (sheafifyValIso_hom_naturality O hO g)

/-- The inverse of the left unit constraint of the tensor product sheaf is natural. -/
theorem tensorSheafLeftUnitor_inv_naturality
    {M N : _root_.SheafOfModules.{w} (TensorSheafification.structureSheaf O hO)} (g : M ⟶ N) :
    g ≫ (tensorSheafLeftUnitor O hO N).inv =
      (tensorSheafLeftUnitor O hO M).inv ≫ ((Tensor.sheafTensor.{u', v', w, w, w}
        ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat) hO⟩).obj
        (_root_.SheafOfModules.unit (TensorSheafification.structureSheaf O hO))).map g := by
  exact Stacks.AlgebraicGeometry.ProjAndSpec.Glue.inv_square _ _
    (tensorSheafLeftUnitor_hom_naturality O hO g)

/-- **The symmetry constraint of the tensor product sheaf is natural in its second factor.** -/
theorem tensorSheafBraiding_hom_naturality_right
    (X : _root_.SheafOfModules.{w} (TensorSheafification.structureSheaf O hO))
    {M N : _root_.SheafOfModules.{w} (TensorSheafification.structureSheaf O hO)} (g : M ⟶ N) :
    ((Tensor.sheafTensor.{u', v', w, w, w}
        ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat) hO⟩).obj X).map g ≫
      (tensorSheafBraiding O hO X N).hom =
    (tensorSheafBraiding O hO X M).hom ≫ ((Tensor.sheafTensor.{u', v', w, w, w}
        ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat) hO⟩).map g).app
          X := by
  have h1 : ((Tensor.sheafTensor.{u', v', w, w, w}
        ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat) hO⟩).obj X).map g =
      (TensorSheafification.sheafify O hO).map (X.val ◁ g.val) := rfl
  have h2 : ((Tensor.sheafTensor.{u', v', w, w, w}
        ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat) hO⟩).map g).app X =
      (TensorSheafification.sheafify O hO).map (g.val ▷ X.val) := rfl
  have h3 : ∀ Y : _root_.SheafOfModules.{w} (TensorSheafification.structureSheaf O hO),
      (tensorSheafBraiding O hO X Y).hom =
        (TensorSheafification.sheafify O hO).map (β_ X.val Y.val).hom := fun _ => rfl
  rw [h1, h2, h3, h3]
  exact Stacks.AlgebraicGeometry.ProjAndSpec.Glue.map_square _
    (BraidedCategory.braiding_naturality_right X.val g.val)

/-- **The symmetry constraint of the tensor product sheaf is natural in its first factor.** -/
theorem tensorSheafBraiding_hom_naturality_left
    {M N : _root_.SheafOfModules.{w} (TensorSheafification.structureSheaf O hO)} (g : M ⟶ N)
    (X : _root_.SheafOfModules.{w} (TensorSheafification.structureSheaf O hO)) :
    ((Tensor.sheafTensor.{u', v', w, w, w}
        ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat) hO⟩).map g).app X ≫
      (tensorSheafBraiding O hO N X).hom =
    (tensorSheafBraiding O hO M X).hom ≫ ((Tensor.sheafTensor.{u', v', w, w, w}
        ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat) hO⟩).obj X).map
          g := by
  have h1 : ((Tensor.sheafTensor.{u', v', w, w, w}
        ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat) hO⟩).obj X).map g =
      (TensorSheafification.sheafify O hO).map (X.val ◁ g.val) := rfl
  have h2 : ((Tensor.sheafTensor.{u', v', w, w, w}
        ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat) hO⟩).map g).app X =
      (TensorSheafification.sheafify O hO).map (g.val ▷ X.val) := rfl
  have h3 : ∀ Y : _root_.SheafOfModules.{w} (TensorSheafification.structureSheaf O hO),
      (tensorSheafBraiding O hO Y X).hom =
        (TensorSheafification.sheafify O hO).map (β_ Y.val X.val).hom := fun _ => rfl
  rw [h1, h2, h3, h3]
  exact Stacks.AlgebraicGeometry.ProjAndSpec.Glue.map_square _
    (BraidedCategory.braiding_naturality_left g.val X.val)

end Naturality

end Stacks.SheafOfModules

namespace Stacks.AlgebraicGeometry.ProjAndSpec

attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.Duality (derivedPushforward derivedPushforwardCompIso)

/-! ### Coproducts preserved by a functor -/

section Preserves

variable {C D : Type*} [Category C] [Category D] {L L' : C ⥤ D}

/-- `PreservesCoproduct.iso` moves a morphism of families that shifts the index along `p`. -/
theorem preservesCoproductIso_hom_map' {f g : ℤ → C} [HasCoproduct f] [HasCoproduct g]
    [HasCoproduct fun m => L.obj (f m)] [HasCoproduct fun m => L.obj (g m)]
    [PreservesColimit (Discrete.functor f) L] [PreservesColimit (Discrete.functor g) L]
    (p : ℤ → ℤ) (b : ∀ m, f m ⟶ g (p m)) :
    L.map (Sigma.map' p b) ≫ (PreservesCoproduct.iso L g).hom =
      (PreservesCoproduct.iso L f).hom ≫ Sigma.map' p (fun m => L.map (b m)) := by
  exact Glue.hom_square (PreservesCoproduct.iso L g) (PreservesCoproduct.iso L f)
    (Stacks.Duality.DerivedPushforward.sigmaComparison_map' L p b).symm

/-- `PreservesCoproduct.iso` is natural in the functor. -/
theorem preservesCoproductIso_hom_naturality (α : L ⟶ L') (f : ℤ → C) [HasCoproduct f]
    [HasCoproduct fun m => L.obj (f m)] [HasCoproduct fun m => L'.obj (f m)]
    [PreservesColimit (Discrete.functor f) L] [PreservesColimit (Discrete.functor f) L'] :
    α.app (∐ f) ≫ (PreservesCoproduct.iso L' f).hom =
      (PreservesCoproduct.iso L f).hom ≫ Limits.Sigma.map (fun m => α.app (f m)) := by
  refine Glue.hom_square (PreservesCoproduct.iso L' f) (PreservesCoproduct.iso L f) ?_
  rw [PreservesCoproduct.inv_hom, PreservesCoproduct.inv_hom]
  refine Sigma.hom_ext _ _ fun m => ?_
  rw [Sigma.ι_map_assoc, ι_comp_sigmaComparison, ι_comp_sigmaComparison_assoc]
  exact (α.naturality (Sigma.ι f m)).symm

end Preserves

/-! ### The coherence constraints of the tensor product, on schemes and on `Proj`

The naturality statements of `Stacks.SheafOfModules` are stated for sheaves of modules over
`Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO`. They are restated here for
`𝒪_X`-modules on a scheme and for `𝒪_P`-modules on `P = Proj A`, with the modules and morphisms
abstract, so that each later use is at the spelling of the statement it feeds. -/

section Coherence

/-- The inverse of the left unit constraint is natural, for `𝒪_X`-modules on a scheme. -/
theorem tensorSheafLeftUnitor_inv_naturality_scheme (X : Scheme.{u}) {M N : X.Modules}
    (g : M ⟶ N) :
    g ≫ (Stacks.SheafOfModules.tensorSheafLeftUnitor X.presheaf X.ringCatSheaf.property N).inv =
      (Stacks.SheafOfModules.tensorSheafLeftUnitor X.presheaf X.ringCatSheaf.property M).inv ≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj
          (SheafOfModules.unit X.ringCatSheaf)).map g :=
  Stacks.SheafOfModules.tensorSheafLeftUnitor_inv_naturality X.presheaf X.ringCatSheaf.property g

/-- The projection formula along an affine morphism is natural in the module on the base, read
through its inverse. -/
theorem projectionFormulaIsoOfQuasicoherent_inv_naturality_right {T S : Scheme.{u}} (h : T ⟶ S)
    [IsAffineHom h] (G : T.Modules) [G.IsQuasicoherent] {H H' : S.Modules} [H.IsQuasicoherent]
    [H'.IsQuasicoherent] (k : H ⟶ H') :
    (Scheme.Modules.pushforward h).map
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          ⟨T.toRingedSpace.presheaf, T.toRingedSpace.IsSheaf⟩).obj G).map
          ((Scheme.Modules.pullback h).map k)) ≫
      (Stacks.AlgebraicGeometry.ProjectionFormula.projectionFormulaIsoOfQuasicoherent h G H'
        ‹_› ‹_›).symm.hom =
    (Stacks.AlgebraicGeometry.ProjectionFormula.projectionFormulaIsoOfQuasicoherent h G H
        ‹_› ‹_›).symm.hom ≫
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨S.toRingedSpace.presheaf, S.toRingedSpace.IsSheaf⟩).obj
        ((Scheme.Modules.pushforward h).obj G)).map k := by
  have := Stacks.AlgebraicGeometry.ProjectionFormula.isIso_projectionFormulaMap h G H ‹_› ‹_›
  have := Stacks.AlgebraicGeometry.ProjectionFormula.isIso_projectionFormulaMap h G H' ‹_› ‹_›
  have hP := Stacks.AlgebraicGeometry.ProjectionFormula.projectionFormulaIso_hom_natural h
    (G := G) (G' := G) (𝟙 _) k
  have hP2 := ((eq_whisker (Glue.uncurry_map_map_id_left _ _ _ _).symm _).trans hP).trans
    (whisker_eq _ (congrArg _ (Glue.uncurry_map_id_left _ _ _)))
  exact Glue.inv_square _ _ hP2

/-- The projection formula along an affine morphism is natural in the module on the source, read
through its inverse. -/
theorem projectionFormulaIsoOfQuasicoherent_inv_naturality_left {T S : Scheme.{u}} (h : T ⟶ S)
    [IsAffineHom h] {G G' : T.Modules} [G.IsQuasicoherent] [G'.IsQuasicoherent] (g : G ⟶ G')
    (H : S.Modules) [H.IsQuasicoherent] :
    (Scheme.Modules.pushforward h).map
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          ⟨T.toRingedSpace.presheaf, T.toRingedSpace.IsSheaf⟩).map g).app
          ((Scheme.Modules.pullback h).obj H)) ≫
      (Stacks.AlgebraicGeometry.ProjectionFormula.projectionFormulaIsoOfQuasicoherent h G' H
        ‹_› ‹_›).symm.hom =
    (Stacks.AlgebraicGeometry.ProjectionFormula.projectionFormulaIsoOfQuasicoherent h G H
        ‹_› ‹_›).symm.hom ≫
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨S.toRingedSpace.presheaf, S.toRingedSpace.IsSheaf⟩).map
        ((Scheme.Modules.pushforward h).map g)).app H := by
  have := Stacks.AlgebraicGeometry.ProjectionFormula.isIso_projectionFormulaMap h G H ‹_› ‹_›
  have := Stacks.AlgebraicGeometry.ProjectionFormula.isIso_projectionFormulaMap h G' H ‹_› ‹_›
  have hP := Stacks.AlgebraicGeometry.ProjectionFormula.projectionFormulaIso_hom_natural h
    (H := H) (H' := H) g (𝟙 _)
  have hP2 := ((eq_whisker (Glue.uncurry_map_id_right _ _ _).symm _).trans hP).trans
    (whisker_eq _ (congrArg _ (Glue.uncurry_map_map_id_right _ _ _ _)))
  exact Glue.inv_square _ _ hP2

variable {A σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ℕ → σ)
  [GradedRing 𝒜]

/-- The symmetry constraint is natural in its second factor, for `𝒪_P`-modules. -/
theorem tensorSheafBraiding_hom_naturality_right_proj (X : (AlgebraicGeometry.Proj 𝒜).Modules)
    {M N : (AlgebraicGeometry.Proj 𝒜).Modules} (g : M ⟶ N) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨(AlgebraicGeometry.Proj 𝒜).toRingedSpace.presheaf,
          (AlgebraicGeometry.Proj 𝒜).toRingedSpace.IsSheaf⟩).obj X).map g ≫
      (Stacks.SheafOfModules.tensorSheafBraiding _ (isSheaf_projStructureRingPresheaf 𝒜) X N).hom =
    (Stacks.SheafOfModules.tensorSheafBraiding _ (isSheaf_projStructureRingPresheaf 𝒜) X M).hom ≫
      ((Stacks.SheafOfModules.Tensor.sheafTensor
        (J := (Opens.grothendieckTopology (ProjectiveSpectrum.top 𝒜)))
        (ProjectiveSpectrum.Proj.structureSheaf 𝒜)).map g).app X :=
  Stacks.SheafOfModules.tensorSheafBraiding_hom_naturality_right _
    (isSheaf_projStructureRingPresheaf 𝒜) X g

/-- The symmetry constraint is natural in its first factor, for `𝒪_P`-modules. -/
theorem tensorSheafBraiding_hom_naturality_left_proj {M N : (AlgebraicGeometry.Proj 𝒜).Modules}
    (g : M ⟶ N) (X : (AlgebraicGeometry.Proj 𝒜).Modules) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨(AlgebraicGeometry.Proj 𝒜).toRingedSpace.presheaf,
          (AlgebraicGeometry.Proj 𝒜).toRingedSpace.IsSheaf⟩).map g).app X ≫
      (Stacks.SheafOfModules.tensorSheafBraiding _ (isSheaf_projStructureRingPresheaf 𝒜) N X).hom =
    (Stacks.SheafOfModules.tensorSheafBraiding _ (isSheaf_projStructureRingPresheaf 𝒜) M X).hom ≫
      (projTensorLeft 𝒜 X).map g :=
  Stacks.SheafOfModules.tensorSheafBraiding_hom_naturality_left _
    (isSheaf_projStructureRingPresheaf 𝒜) g X

end Coherence

section Cone

variable {A B σ τ : Type u} [CommRing A] [CommRing B] [SetLike σ A] [AddSubgroupClass σ A]
  [SetLike τ B] [AddSubgroupClass τ B] {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]
  (c : ConeData 𝒜 ℬ)

/-- **`derivedPushforwardPuncturedConeIso` transports morphisms.** A morphism `α : 𝓕_U ⟶ 𝓖_U`
whose direct image is carried, by the two identifications of the direct images with
`⨁_m 𝓕(m)` and `⨁_m 𝓖(m)`, to the morphism of direct sums sending the `m`-th summand to the
`p m`-th one by `b m`, induces on `RΓ(U, -)` the morphism of direct sums of derived global
sections sending the `m`-th summand to the `p m`-th one by `RΓ(P, b m)`. -/
theorem derivedPushforwardPuncturedConeIso_hom_comp [CompactSpace (AlgebraicGeometry.Proj 𝒜)]
    {F G : (AlgebraicGeometry.Proj 𝒜).Modules} [F.IsQuasicoherent] [G.IsQuasicoherent]
    (hF : (Scheme.Modules.pushforward (puncturedConeProj c)).obj
        (puncturedConePullback c F) ≅ ∐ fun m : ℤ => twistSheafOfModules 𝒜 F m)
    (hG : (Scheme.Modules.pushforward (puncturedConeProj c)).obj
        (puncturedConePullback c G) ≅ ∐ fun m : ℤ => twistSheafOfModules 𝒜 G m)
    (α : puncturedConePullback c F ⟶ puncturedConePullback c G) (p : ℤ → ℤ)
    (b : ∀ m, twistSheafOfModules 𝒜 F m ⟶ twistSheafOfModules 𝒜 G (p m))
    (h : (Scheme.Modules.pushforward (puncturedConeProj c)).map α ≫ hG.hom =
      hF.hom ≫ Sigma.map' p b) :
    (derivedPushforward (puncturedConeProj c ≫ AlgebraicGeometry.Proj.toSpecZero 𝒜)).map
          ((DerivedCategory.singleFunctor (openUInL c).toScheme.Modules 0).map α) ≫
        (derivedPushforwardPuncturedConeIso c G hG).hom =
      (derivedPushforwardPuncturedConeIso c F hF).hom ≫
        Sigma.map' p (fun m => (derivedPushforward (AlgebraicGeometry.Proj.toSpecZero 𝒜)).map
          ((DerivedCategory.singleFunctor (AlgebraicGeometry.Proj 𝒜).Modules 0).map (b m))) := by
  have : IsAffineHom (puncturedConeProj c) := isAffineHom_pi_restrict c
  have : PreservesColimitsOfShape (Discrete ℤ)
      (DerivedCategory.singleFunctor (AlgebraicGeometry.Proj 𝒜).Modules 0) :=
    Stacks.Duality.DerivedPushforward.preservesColimitsOfShape_discrete_int_singleFunctor _ 0
  have hIF : IsIso (sigmaComparison
      (DerivedCategory.singleFunctor (AlgebraicGeometry.Proj 𝒜).Modules 0)
      (fun m : ℤ => twistSheafOfModules 𝒜 F m)) :=
    isIso_sigmaComparison_of_preservesColimit _ _ inferInstance
  have hIG : IsIso (sigmaComparison
      (DerivedCategory.singleFunctor (AlgebraicGeometry.Proj 𝒜).Modules 0)
      (fun m : ℤ => twistSheafOfModules 𝒜 G m)) :=
    isIso_sigmaComparison_of_preservesColimit _ _ inferInstance
  have hσ := Stacks.Duality.DerivedPushforward.sigmaComparison_map'
    (DerivedCategory.singleFunctor (AlgebraicGeometry.Proj 𝒜).Modules 0) p b
  have hσ' := Glue.inv_square
    (asIso (sigmaComparison (DerivedCategory.singleFunctor (AlgebraicGeometry.Proj 𝒜).Modules 0)
      (fun m : ℤ => twistSheafOfModules 𝒜 G m)))
    (asIso (sigmaComparison (DerivedCategory.singleFunctor (AlgebraicGeometry.Proj 𝒜).Modules 0)
      (fun m : ℤ => twistSheafOfModules 𝒜 F m))) hσ.symm
  have hS := Stacks.Duality.DerivedPushforward.sigmaIntSingleFunctorIso_hom_map'
    (AlgebraicGeometry.Proj.toSpecZero 𝒜) 0 p b
  have hS' := Glue.inv_square _ _ hS.symm
  have hN :=
    Stacks.AlgebraicGeometry.DerivedAffinePushforward.derivedPushforwardSingleIso_inv_naturality
    (puncturedConeProj c) α
  have hC := (derivedPushforwardCompIso (puncturedConeProj c)
    (AlgebraicGeometry.Proj.toSpecZero 𝒜)).inv.naturality
      ((DerivedCategory.singleFunctor (openUInL c).toScheme.Modules 0).map α)
  simp only [Functor.comp_map] at hC
  have hh := Glue.map_square
    (DerivedCategory.singleFunctor (SheafOfModules.{u} (AlgebraicGeometry.Proj 𝒜).ringCatSheaf) 0) h
  exact Glue.square_map_square (derivedPushforward (AlgebraicGeometry.Proj.toSpecZero 𝒜)) hC
    (Glue.square_comp₃ hN hh hσ') hS'

/-- **The projection formula along `π|_U` is natural in `𝓕`.** -/
theorem puncturedConePushforwardTensorIso_hom_naturality
    {F G : (AlgebraicGeometry.Proj 𝒜).Modules} [F.IsQuasicoherent] [G.IsQuasicoherent]
    (φ : F ⟶ G) :
    (Scheme.Modules.pushforward (puncturedConeProj c)).map
          ((Scheme.Modules.pullback (puncturedConeProj c)).map φ) ≫
        (puncturedConePushforwardTensorIso c G).hom =
      (puncturedConePushforwardTensorIso c F).hom ≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor
          (J := (Opens.grothendieckTopology (ProjectiveSpectrum.top 𝒜)))
          (ProjectiveSpectrum.Proj.structureSheaf 𝒜)).map φ).app
            (puncturedConeStructurePushforward c) := by
  have : IsAffineHom (puncturedConeProj c) := isAffineHom_pi_restrict c
  have : IsIso (Stacks.AlgebraicGeometry.ProjectionFormula.projectionFormulaMap
      (puncturedConeProj c) (SheafOfModules.unit (openUInL c).toScheme.ringCatSheaf) F) :=
    Stacks.AlgebraicGeometry.ProjectionFormula.isIso_projectionFormulaMap _ _ _
      (AffineQcohPushforward.isQuasicoherent_unit _) ‹_›
  have : IsIso (Stacks.AlgebraicGeometry.ProjectionFormula.projectionFormulaMap
      (puncturedConeProj c) (SheafOfModules.unit (openUInL c).toScheme.ringCatSheaf) G) :=
    Stacks.AlgebraicGeometry.ProjectionFormula.isIso_projectionFormulaMap _ _ _
      (AffineQcohPushforward.isQuasicoherent_unit _) ‹_›
  have hU := tensorSheafLeftUnitor_inv_naturality_scheme (openUInL c).toScheme
    ((Scheme.Modules.pullback (puncturedConeProj c)).map φ)
  have hPQ := projectionFormulaIsoOfQuasicoherent_inv_naturality_right (puncturedConeProj c)
    (SheafOfModules.unit (openUInL c).toScheme.ringCatSheaf) φ
  have hB := tensorSheafBraiding_hom_naturality_right_proj 𝒜
    (puncturedConeStructurePushforward c) φ
  exact Glue.map_square_comp₂ (Scheme.Modules.pushforward (puncturedConeProj c)) hU hPQ hB

/-- **`(π|_U)_*(π|_U)^*𝓕 ≅ ⨁_m 𝓕(m)` is natural in `𝓕`**, for any identification of
`(π|_U)_*𝒪_U` with a direct sum. -/
theorem puncturedConePushforwardPullbackCoproductIso_hom_naturality
    {F G : (AlgebraicGeometry.Proj 𝒜).Modules} [F.IsQuasicoherent] [G.IsQuasicoherent]
    (φ : F ⟶ G)
    (h0 : puncturedConeStructurePushforward c ≅ ∐ fun m : ℤ => twistingSheaf 𝒜 m) :
    (Scheme.Modules.pushforward (puncturedConeProj c)).map
          ((Scheme.Modules.pullback (puncturedConeProj c)).map φ) ≫
        (puncturedConePushforwardPullbackCoproductIso c G h0).hom =
      (puncturedConePushforwardPullbackCoproductIso c F h0).hom ≫
        Limits.Sigma.map (fun m : ℤ => ((Stacks.SheafOfModules.Tensor.sheafTensor
          (J := (Opens.grothendieckTopology (ProjectiveSpectrum.top 𝒜)))
          (ProjectiveSpectrum.Proj.structureSheaf 𝒜)).map φ).app (twistingSheaf 𝒜 m)) := by
  have h1 := puncturedConePushforwardTensorIso_hom_naturality c φ
  have h2 := (((Stacks.SheafOfModules.Tensor.sheafTensor
    (J := (Opens.grothendieckTopology (ProjectiveSpectrum.top 𝒜)))
    (ProjectiveSpectrum.Proj.structureSheaf 𝒜)).map φ).naturality h0.hom).symm
  have h3 := preservesCoproductIso_hom_naturality (L := projTensorLeft 𝒜 F)
    (L' := projTensorLeft 𝒜 G) (((Stacks.SheafOfModules.Tensor.sheafTensor
    (J := (Opens.grothendieckTopology (ProjectiveSpectrum.top 𝒜)))
    (ProjectiveSpectrum.Proj.structureSheaf 𝒜)).map φ)) (fun m : ℤ => twistingSheaf 𝒜 m)
  exact Glue.square_comp₃ h1 h2 h3

end Cone

section Truncation

open Stacks.AlgebraicGeometry.ProjAndSpecTruncation

variable {A σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ℕ → σ)
  [GradedRing 𝒜]

/-- **The decomposition `RΓ(U, 𝓕_U) = ⨁_m RΓ(P, 𝓕(m))` is functorial in `𝓕`.** For a morphism
`φ : 𝓕 ⟶ 𝓖` of quasi-coherent `𝒪_P`-modules, the morphism `RΓ(U, φ_U)` induced on derived
global sections of the pullbacks to the punctured cone is carried by
`derivedPushforwardPuncturedConeIsoTruncation` to the direct sum, over all integers `m`, of the
morphisms `RΓ(P, φ ⊗ 1) : RΓ(P, 𝓕(m)) ⟶ RΓ(P, 𝓖(m))`. -/
@[stacks 0EKH "the decomposition RΓ(U, F_U) = ⊕_m RΓ(P, F ⊗ O_P(m)) is functorial in F; RΓ is \
read as derived direct image to Spec A₀"]
theorem derivedPushforwardPuncturedConeIsoTruncation_hom_naturality
    [CompactSpace (AlgebraicGeometry.Proj 𝒜)] {F G : (AlgebraicGeometry.Proj 𝒜).Modules}
    [F.IsQuasicoherent] [G.IsQuasicoherent] (φ : F ⟶ G) :
    (Stacks.Duality.derivedPushforward
          (puncturedConeProj (truncationConeData 𝒜) ≫
            AlgebraicGeometry.Proj.toSpecZero 𝒜)).map
        ((DerivedCategory.singleFunctor (openUInL (truncationConeData 𝒜)).toScheme.Modules 0).map
          ((Scheme.Modules.pullback (puncturedConeProj (truncationConeData 𝒜))).map φ)) ≫
        (derivedPushforwardPuncturedConeIsoTruncation 𝒜 G).hom =
      (derivedPushforwardPuncturedConeIsoTruncation 𝒜 F).hom ≫
        Limits.Sigma.map (fun m : ℤ => (Stacks.Duality.derivedPushforward
          (AlgebraicGeometry.Proj.toSpecZero 𝒜)).map
          ((DerivedCategory.singleFunctor (AlgebraicGeometry.Proj 𝒜).Modules 0).map
            (((Stacks.SheafOfModules.Tensor.sheafTensor
              (J := (Opens.grothendieckTopology (ProjectiveSpectrum.top 𝒜)))
              (ProjectiveSpectrum.Proj.structureSheaf 𝒜)).map φ).app (twistingSheaf 𝒜 m)))) := by
  have h := puncturedConePushforwardPullbackCoproductIso_hom_naturality (truncationConeData 𝒜) φ
    (Stacks.AlgebraicGeometry.ProjConeTwist.puncturedConeStructurePushforwardCoproductIso 𝒜)
  have h' := h.trans (congrArg (_ ≫ ·) (Sigma.map'_id _).symm)
  exact (derivedPushforwardPuncturedConeIso_hom_comp (truncationConeData 𝒜) _ _ _ id _ h').trans
    (congrArg (_ ≫ ·) (Sigma.map'_id _))

end Truncation

end Stacks.AlgebraicGeometry.ProjAndSpec
