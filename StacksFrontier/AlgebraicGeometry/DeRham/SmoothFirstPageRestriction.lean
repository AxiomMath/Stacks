module

public import StacksFrontier.AlgebraicGeometry.DeRham.SmoothFirstPageFlatIdentification
public import StacksFrontier.Topology.Sheaves.Cohomology.HigherDirectImage.UnboundedLocalizationAction
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPowerRestrictOpen

/-!
# The first page of 0FMN restricted to an open, and local morphisms of coefficient modules

Let `f : X ⟶ Y` be quasi-compact, quasi-separated and smooth over `g : Y ⟶ S`, with flat de Rham
cohomology sheaves, and let `U ⊆ Y` be open with `V = f⁻¹U`. For a morphism
`α : Ω^k_{Y/S}|_U ⟶ Ω^{k+p}_{Y/S}|_U` of `𝒪_U`-modules, a morphism of complexes over `V` compatible
with `α ⊗ 1` through the identification of the graded pieces acts on the restricted first page
`(R^{k+q}f_*gr^kΩ^•_{X/S})|_U` by `α ⊗ 1` on `(Ω^k_{Y/S} ⊗ ℋ^q_dR(X/Y))|_U`
(`restrictedHigherDirectImageAction_flatIsoNat`).

For `α : M|_U ⟶ M'|_U`, the map `α ⊗ 1` (`localTensorMap`) is the restriction to `U` of
`α♭ ⊗ 1`, where `α♭ : j_!(M|_U) ⟶ M'` is the extension of `α` by zero along `j : U ⟶ Y`, read
through the counit `j_!(M|_U) ⟶ M`, which is invertible over `U`.

## Main definitions

* `Stacks.DeRhamSmooth.coefficientTargetComplexShiftHom`:
  `f^{-1}M[-k] ⊗ Ω^• ⟶ (f^{-1}M[-(k+p)] ⊗ Ω^•)[p]`.
* `Stacks.DeRhamSmooth.localTensorMap`: `α ⊗ 1` on `(M ⊗ ℋ^q_dR(X/Y))|_U`.

## Main results

* `Stacks.DeRhamSmooth.coefficientFirstPageShiftMap_shift`: the comparisons at `k` and `k + p`
  agree through the shift, with no sign.
* `Stacks.DeRhamSmooth.coefficientFirstPageShiftMap_comp_shiftMap`.
* `Stacks.DeRhamSmooth.restrictedHigherDirectImageAction_flatIsoNat`.

## References

* [Stacks Project, Tag 0FMN](https://stacks.math.columbia.edu/tag/0FMN)
* N. Katz, T. Oda, *On the differentiation of de Rham cohomology classes with respect to
  parameters*, J. Math. Kyoto Univ. 8 (1968).
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicGeometry
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.Cohomology.FilteredComplex (higherDirectImage)

universe u

attribute [local instance 2000] HasDerivedCategory.standard
attribute [local implicit_reducible] structureSheafRing CategoryTheory.sheafCompose
  Stacks.SheafOfModules.Tensor.ringSheaf
attribute [local instance_reducible] AlgebraicGeometry.SheafedSpace.sheaf
attribute [-instance] Stacks.Cohomology.SpectralLimit.hasSheafifyOpensMax

namespace Stacks.DeRhamSmooth

open Stacks.DeRhamDirectImage

variable {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S)

/-- **The target of Section 0FMK at the cut `k` is that at the cut `k + p`, shifted by `p`**:
`f^{-1}M[-k] ⊗ Ω^•_{X/Y} ≅ (f^{-1}M[-(k + p)] ⊗ Ω^•_{X/Y})[p]`, read over `(f ∘ g)^{-1}𝒪_S`,
through the composition of shifts and the commutation of the change of coefficients with the
shift. -/
def coefficientTargetComplexShiftHom (k p : ℕ) (M : Modules Y.toRingedSpace) :
    (coefficientTargetComplex f g k).obj M ⟶
      ((coefficientTargetComplex f g (k + p)).obj M)⟦(p : ℤ)⟧ :=
  ((coefficientRestriction f g).mapHomologicalComplex (ComplexShape.up ℤ)).map
      ((shiftFunctorAdd' (CochainComplex (Modules (inverseImageBase f)) ℤ)
        (-((k + p : ℕ) : ℤ)) (p : ℤ) (-(k : ℤ)) (by push_cast; ring)).hom.app
          ((coefficientTargetTensor f).obj M)) ≫
    (((coefficientRestriction f g).mapHomologicalComplex (ComplexShape.up ℤ)).commShiftIso
      (p : ℤ)).hom.app _

section Comparison

variable [QuasiCompact f] [QuasiSeparated f] [Smooth f]
  (hflat : ∀ q : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.sheaf)
    (deRhamCohomologySheaf f q))

omit [QuasiCompact f] [QuasiSeparated f] in
/-- **The comparisons at the cuts `k` and `k + p` agree through the shift**: the comparison at
`k`, followed by `coefficientTargetComplexShiftHom` and the shift
`R^{k + q}f_*(C[p]) ≅ R^{k + p + q}f_*C` of the unbounded derived direct image, is the comparison
at `k + p`. No sign appears. -/
theorem coefficientFirstPageShiftMap_shift (k p : ℕ) (q : ℤ) (M : Modules Y.toRingedSpace) :
    coefficientFirstPageShiftMap f g hflat k q M ≫
        ((DerivedCategory.homologyFunctor _ 0).shift ((k : ℤ) + q)).map
          ((DerivedCategory.Q ⋙ derivedRelativePushforward f g).map
            (coefficientTargetComplexShiftHom f g k p M)) ≫
        (Functor.shiftSequenceCommShiftIso (DerivedCategory.Q ⋙ derivedRelativePushforward f g)
          (DerivedCategory.homologyFunctor _ 0) ((coefficientTargetComplex f g (k + p)).obj M)
          (p : ℤ) (((k + p : ℕ) : ℤ) + q) ((k : ℤ) + q) (by push_cast; ring)).inv =
      coefficientFirstPageShiftMap f g hflat (k + p) q M :=
  (Category.assoc _ _ _).trans (congrArg (coefficientFirstPageMapZero f g hflat q M ≫ ·)
    (Functor.shiftSequenceCommShiftIso_add_comp (DerivedCategory.homologyFunctor _ 0)
      ((coefficientRestriction f g).mapHomologicalComplex (ComplexShape.up ℤ))
      (DerivedCategory.Q ⋙ derivedRelativePushforward f g) ((coefficientTargetTensor f).obj M)
      (-(k : ℤ)) (p : ℤ) (-((k + p : ℕ) : ℤ)) q (((k + p : ℕ) : ℤ) + q) ((k : ℤ) + q)
      (by push_cast; ring) (by omega) (by push_cast; ring) (by push_cast; ring)))

/-- A naturality square followed by a commutative triangle. -/
private theorem nat_coh_paste {C : Type*} [Category C] {A A' B B' D E : C} {l : A ⟶ A'}
    {θ : A ⟶ B} {θ' : A' ⟶ B'} {x : B ⟶ B'} {y : B' ⟶ D} {z : D ⟶ E} {θ'' : A' ⟶ E}
    (hn : l ≫ θ' = θ ≫ x) (hc : θ' ≫ y ≫ z = θ'') : θ ≫ x ≫ y ≫ z = l ≫ θ'' := by
  rw [← hc, ← reassoc_of% hn]

/-- **A morphism of coefficient modules followed by the shift, read on the first page**: for
`β : N ⟶ M'` and an isomorphism `s : K ≅ f^{-1}M'[-(k + p)] ⊗ Ω^•_{X/Y}`, the comparison at the cut
`k` followed by the shift map of the derived direct image of
`β ≫ (shift) ≫ s⁻¹[p] : f^{-1}N[-k] ⊗ Ω^• ⟶ K[p]` and by `R f_*s`, is `β ⊗ 1` followed by the
comparison at the cut `k + p`. -/
theorem coefficientFirstPageShiftMap_comp_shiftMap (k p : ℕ) (q : ℤ)
    {N M' : Modules Y.toRingedSpace} (β : N ⟶ M')
    {K : CochainComplex (Modules (inverseImageBase (f ≫ g))) ℤ}
    (s : K ≅ (coefficientTargetComplex f g (k + p)).obj M') :
    coefficientFirstPageShiftMap f g hflat k q N ≫
        (DerivedCategory.homologyFunctor _ 0).shiftMap
          ((DerivedCategory.Q ⋙ derivedRelativePushforward f g).map
            ((coefficientTargetComplex f g k).map β ≫ coefficientTargetComplexShiftHom f g k p M' ≫
              (CategoryTheory.shiftFunctor _ (p : ℤ)).map s.inv) ≫
            ((DerivedCategory.Q ⋙ derivedRelativePushforward f g).commShiftIso (p : ℤ)).hom.app K)
          ((k : ℤ) + q) (((k + p : ℕ) : ℤ) + q) (by push_cast; ring) ≫
        ((DerivedCategory.homologyFunctor _ 0).shift (((k + p : ℕ) : ℤ) + q)).map
          ((DerivedCategory.Q ⋙ derivedRelativePushforward f g).map s.hom) =
      (coefficientFirstPageFlat f g q).map β ≫
        coefficientFirstPageShiftMap f g hflat (k + p) q M' :=
  (congrArg (coefficientFirstPageShiftMap f g hflat k q N ≫ ·)
    (Functor.shiftMap_comp_shiftSequenceCommShiftIso
      (DerivedCategory.Q ⋙ derivedRelativePushforward f g) (DerivedCategory.homologyFunctor _ 0)
      ((coefficientTargetComplex f g k).map β) (p : ℤ)
      (coefficientTargetComplexShiftHom f g k p M') s
      ((k : ℤ) + q) (((k + p : ℕ) : ℤ) + q) (by push_cast; ring))).trans
    (nat_coh_paste (coefficientFirstPageShiftMap_naturality f g hflat k q β)
      (coefficientFirstPageShiftMap_shift f g hflat k p q M'))

end Comparison

/-! ### Local morphisms of coefficient modules, through extension by zero -/

section Local

open Stacks.Cohomology.HigherDirectImage

variable (U : Opens Y.toRingedSpace)

/-- Two triangles of a unit and a counit, one of them invertible, and the naturality of the
unit. -/
private theorem triangle_naturality_paste {C : Type*} [Category C] {A A' B B' : C}
    {u : A ⟶ B} {e : B ⟶ A} {u' : A' ⟶ B'} {e' : B' ⟶ A'} {α : A ⟶ A'} {m : B ⟶ B'}
    (hu : IsIso u) (t₁ : u ≫ e = 𝟙 A) (t₂ : u' ≫ e' = 𝟙 A') (nat : α ≫ u' = u ≫ m) :
    m ≫ e' = e ≫ α := by
  rw [IsIso.eq_inv_of_hom_inv_id t₁, IsIso.eq_inv_comp, ← reassoc_of% nat, t₂, Category.comp_id]

/-- A morphism conjugate to an isomorphism by two isomorphisms is an isomorphism. -/
private theorem isIso_of_comp_hom_eq_hom_comp {C : Type*} [Category C] {A A' B B' : C}
    (e : A ≅ B) (e' : A' ≅ B') {x : A ⟶ A'} {z : B ⟶ B'} (h : x ≫ e'.hom = e.hom ≫ z)
    (hz : IsIso z) : IsIso x := by
  rw [show x = e.hom ≫ z ≫ e'.inv by rw [← reassoc_of% h, Iso.hom_inv_id, Category.comp_id]]
  infer_instance

/-- Extension by zero `j_!` from `U` is left adjoint to restriction to `U`. -/
abbrev restrictAdjunction :
    ExtensionByZeroModules.jShriek U (structureSheafRing Y.toRingedSpace) ⊣
      moduleRestriction Y.toRingedSpace U :=
  ExtensionByZeroModules.jShriekAdjunction U (structureSheafRing Y.toRingedSpace)

/-- The restriction of the counit `j_!(M|_U) ⟶ M` is an isomorphism. -/
theorem isIso_moduleRestriction_map_counit (M : Modules Y.toRingedSpace) :
    IsIso ((moduleRestriction Y.toRingedSpace U).map ((restrictAdjunction U).counit.app M)) := by
  have : IsIso (restrictAdjunction U).unit :=
    ExtensionByZeroModules.isIso_jShriekAdjunction_unit U (structureSheafRing Y.toRingedSpace)
  have : IsIso ((restrictAdjunction U).unit.app ((moduleRestriction Y.toRingedSpace U).obj M) ≫
      (moduleRestriction Y.toRingedSpace U).map ((restrictAdjunction U).counit.app M)) := by
    rw [(restrictAdjunction U).right_triangle_components M]; infer_instance
  exact IsIso.of_isIso_comp_left ((restrictAdjunction U).unit.app _) _

/-- The restriction to `U` of the extension of a morphism defined over `U` is that morphism, after
the identification `(j_!(M|_U))|_U ≅ M|_U` given by the counit. -/
theorem moduleRestriction_map_homEquiv_symm {M M' : Modules Y.toRingedSpace}
    (α : (moduleRestriction Y.toRingedSpace U).obj M ⟶
      (moduleRestriction Y.toRingedSpace U).obj M') :
    (moduleRestriction Y.toRingedSpace U).map (((restrictAdjunction U).homEquiv _ _).symm α) =
      (moduleRestriction Y.toRingedSpace U).map ((restrictAdjunction U).counit.app M) ≫ α := by
  have hu : IsIso (restrictAdjunction U).unit :=
    ExtensionByZeroModules.isIso_jShriekAdjunction_unit U (structureSheafRing Y.toRingedSpace)
  exact (congrArg (moduleRestriction Y.toRingedSpace U).map
    (Adjunction.homEquiv_counit (restrictAdjunction U) _ _ α)).trans
    (((moduleRestriction Y.toRingedSpace U).map_comp _ _).trans
      (triangle_naturality_paste (@NatIso.isIso_app_of_isIso _ _ _ _ _ _ _ hu _)
        ((restrictAdjunction U).right_triangle_components M)
        ((restrictAdjunction U).right_triangle_components M')
        ((restrictAdjunction U).unit.naturality α)))

/-- Restriction of scalars along `g^{-1}𝒪_S ⟶ 𝒪_Y` commutes with restriction to an open on the
underlying sheaves of abelian groups, so it carries morphisms which are invertible over `U` to
morphisms which are invertible over `U`. -/
theorem isIso_moduleRestriction_pushforward_map {A B : Modules Y.toRingedSpace} (x : A ⟶ B)
    (hx : IsIso ((moduleRestriction Y.toRingedSpace U).map x)) :
    IsIso ((moduleRestriction (inverseImageBase g) U).map
      ((pushforward (toInverseImageBase g)).map x)) := by
  have : IsIso ((SheafOfModules.toSheaf _).map ((moduleRestriction (inverseImageBase g) U).map
      ((pushforward (toInverseImageBase g)).map x))) :=
    Functor.map_isIso (SheafOfModules.toSheaf _) ((moduleRestriction Y.toRingedSpace U).map x)
  exact isIso_of_reflects_iso _ (SheafOfModules.toSheaf _)

/-- The restriction to `U` of `ε ⊗ 1 : j_!(M|_U) ⊗ ℋ ⟶ M ⊗ ℋ` is an isomorphism. -/
theorem isIso_moduleRestriction_tensor_counit (M H : Modules Y.toRingedSpace) :
    IsIso ((moduleRestriction Y.toRingedSpace U).map
      (((Stacks.SheafOfModules.Tensor.sheafTensor Y.sheaf).map
        ((restrictAdjunction U).counit.app M)).app H)) := by
  have := isIso_moduleRestriction_map_counit U M
  have hn := Stacks.SheafOfModules.TensorPower.restrictTensorSheafIso_naturality Y.toRingedSpace U
    ((restrictAdjunction U).counit.app M) (𝟙 H)
  simp only [CategoryTheory.Functor.map_id, Category.comp_id] at hn
  exact isIso_of_comp_hom_eq_hom_comp _ _ hn inferInstance

/-- The restriction to `U` of `j_!(M|_U) ⊗ ℋ^q_dR(X/Y) ⟶ M ⊗ ℋ^q_dR(X/Y)` is invertible. -/
theorem isIso_moduleRestriction_coefficientFirstPageFlat_map_counit (q : ℤ)
    (M : Modules Y.toRingedSpace) :
    IsIso ((moduleRestriction (inverseImageBase g) U).map
      ((coefficientFirstPageFlat f g q).map ((restrictAdjunction U).counit.app M))) :=
  isIso_moduleRestriction_pushforward_map g U _
    (isIso_moduleRestriction_tensor_counit U M (deRhamCohomologySheaf f q))

/-- **`α ⊗ 1` on `(M ⊗ ℋ^q_dR(X/Y))|_U`** for a morphism `α : M|_U ⟶ M'|_U` defined over `U`
only: the restriction to `U` of `α♭ ⊗ 1 : j_!(M|_U) ⊗ ℋ ⟶ M' ⊗ ℋ`, `α♭` the extension of `α` by
zero, read through the restriction to `U` of `j_!(M|_U) ⊗ ℋ ⟶ M ⊗ ℋ`, which is invertible. -/
def localTensorMap (q : ℤ) {M M' : Modules Y.toRingedSpace}
    (α : (moduleRestriction Y.toRingedSpace U).obj M ⟶
      (moduleRestriction Y.toRingedSpace U).obj M') :
    (moduleRestriction (inverseImageBase g) U).obj ((coefficientFirstPageFlat f g q).obj M) ⟶
      (moduleRestriction (inverseImageBase g) U).obj ((coefficientFirstPageFlat f g q).obj M') :=
  haveI := isIso_moduleRestriction_coefficientFirstPageFlat_map_counit f g U q M
  inv ((moduleRestriction (inverseImageBase g) U).map
      ((coefficientFirstPageFlat f g q).map ((restrictAdjunction U).counit.app M))) ≫
    (moduleRestriction (inverseImageBase g) U).map
      ((coefficientFirstPageFlat f g q).map (((restrictAdjunction U).homEquiv _ _).symm α))

/-- Under a functor `F`, a naturality square `hN`, a triangle `hc`, an action identity `hA` and a
square `hG` paste to an equality with `inv (F.map lε) ≫ F.map lα`, for `F.map lε` invertible. -/
private theorem final_paste {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {L₀ L₁ L₂ S₀ S₁ S₂ S₃ T' : C} {lε : L₀ ⟶ L₁} {lα : L₀ ⟶ L₂} {θk : L₁ ⟶ S₁}
    {θN : L₀ ⟶ S₀} {s₁ : S₀ ⟶ S₁} {t : S₁ ⟶ S₂} {s : S₀ ⟶ S₂} {sm : S₀ ⟶ S₃} {u : S₃ ⟶ T'}
    {act : F.obj S₂ ⟶ F.obj S₃} (e' : L₂ ≅ T')
    (hN : lε ≫ θk = θN ≫ s₁) (hc : s₁ ≫ t = s) (hA : F.map s ≫ act = F.map sm)
    (hG : θN ≫ sm ≫ u = lα ≫ e'.hom) (hε : IsIso (F.map lε)) :
    F.map (θk ≫ t) ≫ act ≫ F.map (u ≫ e'.inv) = inv (F.map lε) ≫ F.map lα := by
  rw [IsIso.eq_inv_comp, ← F.map_comp_assoc, reassoc_of% hN, hc, F.map_comp, Category.assoc,
    reassoc_of% hA, ← F.map_comp, ← F.map_comp]
  congr 1
  rw [reassoc_of% hG, Iso.hom_inv_id, Category.comp_id]

end Local

section Assembly

open Stacks.Cohomology.HigherDirectImage

variable [QuasiCompact f] [QuasiSeparated f] [Smooth f]
  (hflat : ∀ q : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.sheaf)
    (deRhamCohomologySheaf f q)) (U : Opens Y.toRingedSpace)
/-- **The action of a local morphism on the restricted first page, read through the identification
of the first page.** Let `α : Ω^k_{Y/S}|_U ⟶ Ω^{k+p}_{Y/S}|_U` be a morphism of `𝒪_U`-modules and
`μ : gr^kΩ^•_{X/S}|_V ⟶ (gr^{k+p}Ω^•_{X/S}|_V)[p]` a morphism of complexes over `V = f⁻¹U` which is
`α ⊗ 1` through the identification of the graded pieces of Section 0FMK: precisely, `hμ` asks that,
after the global maps out of `f^{-1}(j_!(Ω^k|_U))[-k] ⊗ Ω^•_{X/Y}` given by the counit and by the
extension `α♭` of `α`, the restriction of `μ` agrees with the restriction of `α♭ ⊗ 1`. Then the
action of `μ` on `(R^{k+q}f_*gr^k)|_U ⟶ (R^{k+p+q}f_*gr^{k+p})|_U`, read through
`higherDirectImageGradedPieceFlatIsoNat` at both ends, is `α ⊗ 1` on `(Ω^• ⊗ ℋ^q_dR(X/Y))|_U`
(`localTensorMap`). There is no sign. -/
theorem restrictedHigherDirectImageAction_flatIsoNat (k p : ℕ) (q : ℤ)
    (α : (moduleRestriction Y.toRingedSpace U).obj
        (AlgebraicGeometry.Scheme.Hom.relativeDifferentialForms g (k : ℤ)) ⟶
      (moduleRestriction Y.toRingedSpace U).obj
        (AlgebraicGeometry.Scheme.Hom.relativeDifferentialForms g ((k + p : ℕ) : ℤ)))
    (μ : ((moduleRestriction (inverseImageBase (f ≫ g))
            (preimageOpen (relativeBase f g) U)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj
        (gradedPiece (inverseImageBase (f ≫ g)) (k : ℤ) (deRhamSmoothFiltration f g)) ⟶
      (((moduleRestriction (inverseImageBase (f ≫ g))
            (preimageOpen (relativeBase f g) U)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj
        (gradedPiece (inverseImageBase (f ≫ g)) ((k + p : ℕ) : ℤ)
          (deRhamSmoothFiltration f g)))⟦(p : ℤ)⟧)
    (hμ : ((moduleRestriction (inverseImageBase (f ≫ g))
            (preimageOpen (relativeBase f g) U)).mapHomologicalComplex
          (ComplexShape.up ℤ)).map
        ((coefficientTargetComplex f g k).map ((restrictAdjunction U).counit.app _) ≫
          (gradedPieceIsoGradedTargetComplexOfStepSquares f g k (stepSquares f g k).1
            (stepSquares f g k).2).inv) ≫ μ =
      ((moduleRestriction (inverseImageBase (f ≫ g))
            (preimageOpen (relativeBase f g) U)).mapHomologicalComplex
          (ComplexShape.up ℤ)).map
        ((coefficientTargetComplex f g k).map (((restrictAdjunction U).homEquiv _ _).symm α) ≫
          coefficientTargetComplexShiftHom f g k p _ ≫
          (CategoryTheory.shiftFunctor _ (p : ℤ)).map
            (gradedPieceIsoGradedTargetComplexOfStepSquares f g (k + p) (stepSquares f g (k + p)).1
              (stepSquares f g (k + p)).2).inv) ≫
        (((moduleRestriction (inverseImageBase (f ≫ g))
          (preimageOpen (relativeBase f g) U)).mapHomologicalComplex
            (ComplexShape.up ℤ)).commShiftIso (p : ℤ)).hom.app _) :
    (moduleRestriction (inverseImageBase g) U).map
        (higherDirectImageGradedPieceFlatIsoNat f g hflat k q).inv ≫
      restrictedHigherDirectImageAction (relativeBase f g) U μ ((k : ℤ) + q)
        (((k + p : ℕ) : ℤ) + q) (by push_cast; ring) ≫
      (moduleRestriction (inverseImageBase g) U).map
        (higherDirectImageGradedPieceFlatIsoNat f g hflat (k + p) q).hom =
      localTensorMap f g U q α := by
  have hA := restrictedHigherDirectImageAction_of_global (relativeBase f g) U μ _ _ hμ
    ((k : ℤ) + q) (((k + p : ℕ) : ℤ) + q) (by push_cast; ring)
  have hG := coefficientFirstPageShiftMap_comp_shiftMap f g hflat k p q
    (((restrictAdjunction U).homEquiv _ _).symm α)
    (gradedPieceIsoGradedTargetComplexOfStepSquares f g (k + p) (stepSquares f g (k + p)).1
      (stepSquares f g (k + p)).2)
  have hN := coefficientFirstPageShiftMap_naturality f g hflat k q
    ((restrictAdjunction U).counit.app
      (AlgebraicGeometry.Scheme.Hom.relativeDifferentialForms g (k : ℤ)))
  have hA' := hA.trans (congrArg (fun z => (moduleRestriction (inverseImageBase g) U).map
    ((DerivedCategory.homologyFunctor _ 0).shiftMap z ((k : ℤ) + q) (((k + p : ℕ) : ℤ) + q)
      (by push_cast; ring)))
    (Functor.map_comp_commShiftIso_comp DerivedCategory.Q (derivedRelativePushforward f g)
      (p : ℤ) _))
  exact final_paste (moduleRestriction (inverseImageBase g) U)
    (coefficientFirstPageShiftIso f g hflat (k + p) q _
      (AlgebraicGeometry.Scheme.Hom.isQuasicoherent_relativeDifferentialForms g (k + p)))
    hN (((DerivedCategory.homologyFunctor _ _).map_comp _ _).symm.trans
      (congrArg (DerivedCategory.homologyFunctor _ _).map
        (((derivedRelativePushforward f g).map_comp _ _).symm.trans
          (congrArg (derivedRelativePushforward f g).map (DerivedCategory.Q.map_comp _ _).symm))))
    hA' hG (isIso_moduleRestriction_coefficientFirstPageFlat_map_counit f g U q _)

/-- `restrictedHigherDirectImageAction_flatIsoNat` read through the `ℤ`-indexed identification
`higherDirectImageGradedPieceFlatIso` of the first page. -/
theorem restrictedHigherDirectImageAction_flatIso (k p : ℕ) (q : ℤ)
    (α : (moduleRestriction Y.toRingedSpace U).obj
        (AlgebraicGeometry.Scheme.Hom.relativeDifferentialForms g (k : ℤ)) ⟶
      (moduleRestriction Y.toRingedSpace U).obj
        (AlgebraicGeometry.Scheme.Hom.relativeDifferentialForms g ((k + p : ℕ) : ℤ)))
    (μ : ((moduleRestriction (inverseImageBase (f ≫ g))
            (preimageOpen (relativeBase f g) U)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj
        (gradedPiece (inverseImageBase (f ≫ g)) (k : ℤ) (deRhamSmoothFiltration f g)) ⟶
      (((moduleRestriction (inverseImageBase (f ≫ g))
            (preimageOpen (relativeBase f g) U)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj
        (gradedPiece (inverseImageBase (f ≫ g)) ((k + p : ℕ) : ℤ)
          (deRhamSmoothFiltration f g)))⟦(p : ℤ)⟧)
    (hμ : ((moduleRestriction (inverseImageBase (f ≫ g))
            (preimageOpen (relativeBase f g) U)).mapHomologicalComplex
          (ComplexShape.up ℤ)).map
        ((coefficientTargetComplex f g k).map ((restrictAdjunction U).counit.app _) ≫
          (gradedPieceIsoGradedTargetComplexOfStepSquares f g k (stepSquares f g k).1
            (stepSquares f g k).2).inv) ≫ μ =
      ((moduleRestriction (inverseImageBase (f ≫ g))
            (preimageOpen (relativeBase f g) U)).mapHomologicalComplex
          (ComplexShape.up ℤ)).map
        ((coefficientTargetComplex f g k).map (((restrictAdjunction U).homEquiv _ _).symm α) ≫
          coefficientTargetComplexShiftHom f g k p _ ≫
          (CategoryTheory.shiftFunctor _ (p : ℤ)).map
            (gradedPieceIsoGradedTargetComplexOfStepSquares f g (k + p) (stepSquares f g (k + p)).1
              (stepSquares f g (k + p)).2).inv) ≫
        (((moduleRestriction (inverseImageBase (f ≫ g))
          (preimageOpen (relativeBase f g) U)).mapHomologicalComplex
            (ComplexShape.up ℤ)).commShiftIso (p : ℤ)).hom.app _) :
    (moduleRestriction (inverseImageBase g) U).map
        (higherDirectImageGradedPieceFlatIso f g hflat (k : ℤ) q).inv ≫
      restrictedHigherDirectImageAction (relativeBase f g) U μ ((k : ℤ) + q)
        (((k + p : ℕ) : ℤ) + q) (by push_cast; ring) ≫
      (moduleRestriction (inverseImageBase g) U).map
        (higherDirectImageGradedPieceFlatIso f g hflat ((k + p : ℕ) : ℤ) q).hom =
      localTensorMap f g U q α := by
  rw [higherDirectImageGradedPieceFlatIso_natCast, higherDirectImageGradedPieceFlatIso_natCast]
  exact restrictedHigherDirectImageAction_flatIsoNat f g hflat U k p q α μ hμ

end Assembly

end Stacks.DeRhamSmooth
