module

public import StacksFrontier.AlgebraicGeometry.Topologies.AffineSiteBaseChange
public import StacksFrontier.AlgebraicGeometry.Topologies.CechVanishingStandardCovering
public import StacksFrontier.CategoryTheory.Sites.Continuous.CoveringPullbacks
public import StacksFrontier.CategoryTheory.Sites.SlicePost.Continuous

/-!
# Čech vanishing for base-change presheaves of modules of an arbitrary universe

Let `S` be a scheme and `N` a module over `Γ(S, 𝒪)` of an arbitrary universe.  On the slice
`Over S` of all schemes over `S`, the presheaf `Z ↦ Γ(Z, 𝒪) ⊗_{Γ(S, 𝒪)} N` has vanishing
positive-degree Čech cohomology on every finite family of affine schemes which is a flat
covering of an affine object: this is [Stacks, Tag 03FJ] for the base change of a module, whose
Čech complex is the Amitsur complex of a faithfully flat ring map ([Stacks, Tag 023M]).  The
statement is transported to the slices of a site of affine schemes along `Over.post L`.

## Main results

* `Stacks.AffineSiteBaseChange.isIso_sliceTensorToSectionsApp`: the comparison
  `Γ(Z, 𝒪) ⊗_{ULift Γ(U, 𝒪)} G(U) ⟶ G(Z)` of a cartesian presheaf of modules is invertible.
* `Stacks.AffineSiteBaseChange.preservesFiniteProducts_bigBaseChange`: the base-change presheaf
  carries finite disjoint unions to products.
* `Stacks.AffineSiteBaseChange.isZero_cechCohomology_singleton_bigBaseChange`: Čech vanishing for
  a one-member faithfully flat covering of affines.
* `Stacks.AffineSiteBaseChange.isZero_cechCohomology_bigBaseChange`: Čech vanishing for a finite
  flat covering of an affine object by affines.
* `Stacks.AffineSiteBaseChange.isZero_cechCohomology_baseChangePresheaf_over`: the same on the
  slices of a site of affine schemes.

## References

* [Stacks Project, Tag 03FJ](https://stacks.math.columbia.edu/tag/03FJ)
* [Stacks Project, Tag 03FI](https://stacks.math.columbia.edu/tag/03FI)
* [Stacks Project, Tag 023M](https://stacks.math.columbia.edu/tag/023M)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped TensorProduct

namespace Stacks.AffineSiteBaseChange

universe t u

open Stacks.Sites Stacks.Sites.OverModules

variable (S : Scheme.{u})

/-- The structure presheaf of rings of the slice of all schemes over `S`. -/
abbrev overRings : (Over S)ᵒᵖ ⥤ RingCat.{u} :=
  overRingPresheaf (rings (𝟭 Scheme.{u}) ⋙ forget₂ CommRingCat RingCat) S

variable {S} (G : PresheafOfModules.{max t u} (overRings S)) (U : Over S)

/-- The sections of `G` over `U` are a module over the coordinate ring of `U`. -/
instance moduleGammaSections :
    Module (Scheme.Γ.obj (op U.left) : Type u) (G.obj (op U)) :=
  inferInstanceAs (Module ((overRings S).obj (op U)) (G.obj (op U)))

/-- The sections of `G` over an object of the slice at `U` are a module over its coordinate
algebra. -/
instance moduleGammaAlgSections (Z : (Over U)ᵒᵖ) :
    Module (((gammaAlg S (𝟭 (Over S)) U).obj Z : CommAlgCat.{u} _) : Type u)
      (G.obj (op Z.unop.left)) :=
  inferInstanceAs (Module ((overRings S).obj (op Z.unop.left)) (G.obj (op Z.unop.left)))

/-- Restriction of a section of `G` over `U` to an object of the slice at `U`. -/
abbrev sliceRestrict (Z : (Over U)ᵒᵖ) : G.obj (op U) →+ G.obj (op Z.unop.left) :=
  (G.map Z.unop.hom.op).hom.toAddMonoidHom

/-- Restriction to the slice is semilinear for the coordinate-algebra actions. -/
theorem sliceRestrict_smul (Z : (Over U)ᵒᵖ) (c : ULift.{u} (Scheme.Γ.obj (op U.left)))
    (m : G.obj (op U)) :
    sliceRestrict.{t} G U Z (c • m) =
      algebraMap (ULift.{u} (Scheme.Γ.obj (op U.left)))
          (((gammaAlg S (𝟭 (Over S)) U).obj Z : CommAlgCat.{u} _) : Type u) c •
        sliceRestrict.{t} G U Z m :=
  (G.map Z.unop.hom.op).hom.map_smul c.down m

/-- The sections of `G` over `U` are a module over the coordinate ring of `U`, in the `Γ(-, ⊤)`
spelling. -/
instance moduleGammaTopSections :
    Module (Γ(U.left, ⊤) : Type u) (G.obj (op U)) :=
  inferInstanceAs (Module ((overRings S).obj (op U)) (G.obj (op U)))

/-- The bilinear data of the coefficient comparison: `(a, m) ↦ a • m|_Z`. -/
def sliceBilin (Z : (Over U)ᵒᵖ) :
    (((gammaAlg S (𝟭 (Over S)) U).obj Z : CommAlgCat.{u} _) : Type u) →+
      (G.obj (op U) →+ G.obj (op Z.unop.left)) where
  toFun a :=
    { toFun := fun m => a • sliceRestrict.{t} G U Z m
      map_zero' := (congrArg (a • ·) (map_zero _)).trans (smul_zero a)
      map_add' := fun x y => (congrArg (a • ·) (map_add _ x y)).trans (smul_add a _ _) }
  map_zero' := AddMonoidHom.ext fun _ => zero_smul _ _
  map_add' _ _ := AddMonoidHom.ext fun _ => add_smul _ _ _

/-- The bilinear data of the coefficient comparison is balanced over the lifted base ring. -/
theorem sliceBilin_balanced (Z : (Over U)ᵒᵖ) (c : ULift.{u} (Scheme.Γ.obj (op U.left)))
    (a : (((gammaAlg S (𝟭 (Over S)) U).obj Z : CommAlgCat.{u} _) : Type u))
    (m : G.obj (op U)) :
    sliceBilin.{t} G U Z (c • a) m = sliceBilin.{t} G U Z a (c • m) := by
  show (c • a) • sliceRestrict.{t} G U Z m = a • sliceRestrict.{t} G U Z (c • m)
  rw [sliceRestrict_smul, Algebra.smul_def, mul_smul, smul_smul, smul_smul, mul_comm]

/-- The coefficient comparison at one object of the slice at `U`: `a ⊗ m ↦ a • m|_Z`. -/
def sliceTensorToSectionsApp (Z : (Over U)ᵒᵖ) :
    ((gammaAlg S (𝟭 (Over S)) U ⋙
        Stacks.Descent.amitsurCoefficients.{u, u, max t u} (Scheme.Γ.obj (op U.left) : Type u)
          (G.obj (op U))) ⋙ forget₂ _ AddCommGrpCat.{max t u}).obj Z ⟶
      ((Over.forget U).op ⋙ G.presheaf).obj Z :=
  AddCommGrpCat.ofHom (TensorProduct.liftAddHom (sliceBilin.{t} G U Z)
    (sliceBilin_balanced.{t} G U Z))

/-- The coefficient comparison on a generator. -/
theorem sliceTensorToSectionsApp_tmul (Z : (Over U)ᵒᵖ)
    (a : (((gammaAlg S (𝟭 (Over S)) U).obj Z : CommAlgCat.{u} _) : Type u))
    (m : G.obj (op U)) :
    sliceTensorToSectionsApp.{t} G U Z
        (a ⊗ₜ[ULift.{u} (Scheme.Γ.obj (op U.left))] m) = a • sliceRestrict.{t} G U Z m :=
  rfl

/-- **The coefficient comparison**, natural on the slice at `U`. -/
def sliceTensorToSections :
    (gammaAlg S (𝟭 (Over S)) U ⋙
        Stacks.Descent.amitsurCoefficients.{u, u, max t u} (Scheme.Γ.obj (op U.left) : Type u)
          (G.obj (op U))) ⋙ forget₂ _ AddCommGrpCat.{max t u} ⟶
      (Over.forget U).op ⋙ G.presheaf where
  app Z := sliceTensorToSectionsApp.{t} G U Z
  naturality Z Z' g := by
    apply AddCommGrpCat.hom_ext
    refine addHom_ext_tmul (Rr := ULift.{u} (Scheme.Γ.obj (op U.left)))
      (Mm := (((gammaAlg S (𝟭 (Over S)) U).obj Z : CommAlgCat.{u} _) : Type u))
      (Nn := G.obj (op U)) (Pp := G.obj (op Z'.unop.left)) (fun a m => ?_)
    change sliceTensorToSectionsApp.{t} G U Z'
        ((gammaAlg S (𝟭 (Over S)) U).map g a ⊗ₜ[ULift.{u} (Scheme.Γ.obj (op U.left))] m) =
      G.map g.unop.left.op (sliceTensorToSectionsApp.{t} G U Z
        (a ⊗ₜ[ULift.{u} (Scheme.Γ.obj (op U.left))] m))
    rw [sliceTensorToSectionsApp_tmul, sliceTensorToSectionsApp_tmul]
    refine Eq.trans ?_ ((G.map g.unop.left.op).hom.map_smul a _).symm
    congr 1
    change G.map Z'.unop.hom.op m = G.map g.unop.left.op (G.map Z.unop.hom.op m)
    refine Eq.trans ?_ (PresheafOfModules.map_comp_apply G Z.unop.hom.op g.unop.left.op m)
    rw [← op_comp, Over.w g.unop]

/-- The commutative-ring presheaf whose underlying presheaf of rings is `overRings S`. -/
abbrev overCommRings (S : Scheme.{u}) : (Over S)ᵒᵖ ⥤ CommRingCat.{u} :=
  (Over.forget S).op ⋙ rings (𝟭 Scheme.{u})

/-- **The coefficient comparison at `Z` is an isomorphism when the base-change comparison of `G`
along the structure morphism of `Z` is.** -/
theorem isIso_sliceTensorToSectionsApp (Z : (Over U)ᵒᵖ)
    (hG : IsIso (Stacks.PresheafOfModules.restrictionBaseChange.{u + 1, u, u, t}
      (R := overCommRings S) G Z.unop.hom.op)) :
    IsIso (sliceTensorToSectionsApp.{t} G U Z) := by
  classical
  let f : (Scheme.Γ.obj (op U.left) : Type u) →+* (Scheme.Γ.obj (op Z.unop.left.left) : Type u) :=
    ((overCommRings S).map Z.unop.hom.op).hom
  let iA : Module (Scheme.Γ.obj (op U.left) : Type u)
      (Scheme.Γ.obj (op Z.unop.left.left) : Type u) := Module.compHom _ f
  let φ := Stacks.PresheafOfModules.restrictionBaseChange.{u + 1, u, u, t}
    (R := overCommRings S) G Z.unop.hom.op
  let e := uliftBaseTensorAddEquiv (Scheme.Γ.obj (op U.left))
    (Scheme.Γ.obj (op Z.unop.left.left)) (G.obj (op U)) iA (moduleGammaSections.{t} G U)
  have hΨ : sliceTensorToSectionsApp.{t} G U Z =
      AddCommGrpCat.ofHom (φ.hom.toAddMonoidHom.comp e.toAddMonoidHom) := by
    apply AddCommGrpCat.hom_ext
    refine addHom_ext_tmul (Rr := ULift.{u} (Scheme.Γ.obj (op U.left)))
      (Mm := (((gammaAlg S (𝟭 (Over S)) U).obj Z : CommAlgCat.{u} _) : Type u))
      (Nn := G.obj (op U)) (Pp := G.obj (op Z.unop.left)) (fun a m => ?_)
    exact (Stacks.PresheafOfModules.restrictionBaseChange_tmul (R := overCommRings S) G
      Z.unop.hom.op a m).symm
  rw [hΨ]
  exact (ConcreteCategory.isIso_iff_bijective _).2
    ((ConcreteCategory.bijective_of_isIso φ).comp e.bijective)

/-! ### Finite products -/

section Products

open Stacks.TerminalBaseChange

variable (S)

/-- The coordinate ring of an object of `Over S`, as a module over the coordinate ring of `S`
through its structure morphism. -/
abbrev coordinateModule (Z : (Over S)ᵒᵖ) : ModuleCat.{u} ((overRings S).obj (op (Over.mk (𝟙 S)))) :=
  (ModuleCat.restrictScalars (rho (overRings S) (overIdTerminal S) Z)).obj
    (ModuleCat.of ((overRings S).obj Z) ((overRings S).obj Z))

/-- The restriction maps of the coordinate rings, as linear maps over the coordinate ring of
`S`. -/
def coordinateModuleMap {Z W : (Over S)ᵒᵖ} (g : Z ⟶ W) :
    coordinateModule S Z ⟶ coordinateModule S W :=
  ModuleCat.ofHom (X := coordinateModule S Z) (Y := coordinateModule S W)
    { toFun := fun a => ((overRings S).map g).hom a
      map_add' := map_add _
      map_smul' := fun r a => by
        let a' : (overRings S).obj Z := a
        change ((overRings S).map g).hom (rho (overRings S) (overIdTerminal S) Z r * a') =
          rho (overRings S) (overIdTerminal S) W r * ((overRings S).map g).hom a'
        rw [map_mul, rho_comp_apply] }

/-- The coordinate rings of the objects of `Over S`, as modules over the coordinate ring of `S`
through their structure morphisms. -/
def coordinateModules : (Over S)ᵒᵖ ⥤ ModuleCat.{u} ((overRings S).obj (op (Over.mk (𝟙 S)))) where
  obj Z := coordinateModule S Z
  map g := coordinateModuleMap S g
  map_id Z := by
    ext a
    exact congrArg (fun φ => φ.hom a) ((overRings S).map_id Z)
  map_comp f g := by
    ext a
    exact congrArg (fun φ => φ.hom a) ((overRings S).map_comp f g)

/-- Tensoring with a fixed module, from modules of one universe to abelian groups of a larger
one. -/
def tensorRightAb {R : Type u} [CommRing R] (N : ModuleCat.{max t u} R) :
    ModuleCat.{u} R ⥤ AddCommGrpCat.{max t u} where
  obj M := AddCommGrpCat.of (TensorProduct R M N)
  map g := AddCommGrpCat.ofHom (LinearMap.rTensor N g.hom).toAddMonoidHom
  map_id M :=
    AddCommGrpCat.hom_ext (AddMonoidHom.ext (LinearMap.congr_fun (LinearMap.rTensor_id N M)))
  map_comp f g := AddCommGrpCat.hom_ext
    (AddMonoidHom.ext (LinearMap.congr_fun (LinearMap.rTensor_comp N g.hom f.hom)))

/-- Tensoring with a fixed module is additive. -/
instance additive_tensorRightAb {R : Type u} [CommRing R] (N : ModuleCat.{max t u} R) :
    (tensorRightAb.{t} N).Additive where
  map_add {_ _ f g} := AddCommGrpCat.hom_ext
    (AddMonoidHom.ext (LinearMap.congr_fun (LinearMap.rTensor_add N f.hom g.hom)))

/-- The base-change presheaf is the coordinate modules tensored with `N`, on the nose. -/
theorem bigBaseChange_presheaf_eq
    (N : ModuleCat.{max t u} ((overRings S).obj (op (Over.mk (𝟙 S))))) :
    (bigBaseChange.{t} S N).presheaf = coordinateModules S ⋙ tensorRightAb.{t} N := rfl

/-- The coordinate modules, forgetting the module structure, are the coordinate rings. -/
def coordinateModulesForget₂Iso :
    coordinateModules S ⋙ forget₂ _ AddCommGrpCat ≅
      (Over.forget S).op ⋙ Scheme.Γ ⋙ forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => rfl)

/-- The coordinate modules carry finite coproducts of schemes over `S` to products. -/
instance preservesFiniteProducts_coordinateModules :
    PreservesFiniteProducts (coordinateModules S) := by
  have : PreservesFiniteProducts (coordinateModules S ⋙ forget₂ _ AddCommGrpCat) :=
    ⟨fun _ => preservesLimitsOfShape_of_natIso (coordinateModulesForget₂Iso S).symm⟩
  exact preservesFiniteProducts_of_reflects_of_preserves _ (forget₂ _ AddCommGrpCat)

/-- **The base-change presheaf on the slice of all schemes over `S` carries finite coproducts
to products.** -/
instance preservesFiniteProducts_bigBaseChange
    (N : ModuleCat.{max t u} ((overRings S).obj (op (Over.mk (𝟙 S))))) :
    PreservesFiniteProducts (bigBaseChange.{t} S N).presheaf :=
  inferInstanceAs (PreservesFiniteProducts (coordinateModules S ⋙ tensorRightAb.{t} N))

end Products

/-! ### Čech vanishing on the slice of all schemes -/

section Cech

open Stacks.TerminalBaseChange Stacks.CechSite

/-- The base-change presheaf is cartesian. -/
theorem isIso_restrictionBaseChange_bigBaseChange
    (N : ModuleCat.{max t u} ((overRings S).obj (op (Over.mk (𝟙 S))))) {X Y : (Over S)ᵒᵖ}
    (f : X ⟶ Y) :
    IsIso (Stacks.PresheafOfModules.restrictionBaseChange.{u + 1, u, u, t}
      (R := overCommRings S) (bigBaseChange.{t} S N) f) :=
  isIso_restrictionBaseChange_baseChangePresheaf.{t} _ _ N f

/-- **The comparison of the base-change presheaf on the slice at `U` with the Amitsur
coefficients of `U`.** -/
def bigBaseChangeSliceIso
    (N : ModuleCat.{max t u} ((overRings S).obj (op (Over.mk (𝟙 S))))) (U : Over S) :
    (Over.forget U).op ⋙ (bigBaseChange.{t} S N).presheaf ≅
      (gammaAlg S (𝟭 (Over S)) U ⋙
        Stacks.Descent.amitsurCoefficients.{u, u, max t u} (Scheme.Γ.obj (op U.left) : Type u)
          ((bigBaseChange.{t} S N).obj (op U))) ⋙ forget₂ _ AddCommGrpCat.{max t u} :=
  haveI : ∀ Z, IsIso ((sliceTensorToSections.{t} (bigBaseChange.{t} S N) U).app Z) := fun Z =>
    isIso_sliceTensorToSectionsApp.{t} _ U Z (isIso_restrictionBaseChange_bigBaseChange N _)
  haveI : IsIso (sliceTensorToSections.{t} (bigBaseChange.{t} S N) U) :=
    NatIso.isIso_of_isIso_app _
  (asIso (sliceTensorToSections.{t} (bigBaseChange.{t} S N) U)).symm

/-- **Čech vanishing in positive degrees for the base-change presheaf and a one-member covering
of an affine object of `Over S` by an affine object, faithfully flat on coordinate rings.**
This is [Stacks, Tag 03FJ] for the base change of a module of arbitrary universe. -/
theorem isZero_cechCohomology_singleton_bigBaseChange
    (N : ModuleCat.{max t u} ((overRings S).obj (op (Over.mk (𝟙 S))))) (U : Over S)
    [IsAffine U.left] {W : Over S} (f : W ⟶ U) [IsAffine W.left]
    (hff : letI := overAffineSliceAlgebra U f
      Module.FaithfullyFlat (Γ(U.left, ⊤) : Type u) (Γ(W.left, ⊤) : Type u)) (p : ℕ) :
    IsZero (cechCohomology (PreZeroHypercover.singleton.{max t u} f)
      (bigBaseChange.{t} S N).presheaf (p + 1)) := by
  let _halg := overAffineSliceAlgebra U f
  have := hff
  refine Stacks.CechSite.isZero_cechCohomology_singleton_of_iso.{max t u} f
    ((overAffineAlgSpec U).obj (op (overAffineAlgObj U (Γ(W.left, ⊤) : Type u)))).hom
    (mkIsoMkSpecOverAffineAlgObj U f) (bigBaseChange.{t} S N).presheaf (p + 1) ?_
  exact isZero_cechCohomology_singleton_succ_overAffine U (Γ(W.left, ⊤) : Type u)
    ((bigBaseChange.{t} S N).obj (op U)) (bigBaseChange.{t} S N).presheaf
    (gammaAlg S (𝟭 (Over S)) U ⋙
        Stacks.Descent.amitsurCoefficients.{u, u, max t u} (Γ(U.left, ⊤) : Type u)
          ((bigBaseChange.{t} S N).obj (op U)))
    (bigBaseChangeSliceIso.{t} N U) (overAffineAlgObj U (Γ(W.left, ⊤) : Type u))
    (powerSectionsAmitsurCoefficientsIso U _ ((bigBaseChange.{t} S N).obj (op U)))
    (sectionsTerminalArrowIsoAlgebraMapArrow U (Γ(W.left, ⊤) : Type u)) p

/-- **Čech vanishing in positive degrees for the base-change presheaf and a finite flat
covering of an affine object of `Over S` by affine objects.** -/
theorem isZero_cechCohomology_bigBaseChange
    (N : ModuleCat.{max t u} ((overRings S).obj (op (Over.mk (𝟙 S))))) {T : Over S}
    [IsAffine T.left] (E : PreZeroHypercover.{max t u} T) [Finite E.I₀]
    (haff : ∀ i, IsAffine (E.X i).left) (hflat : ∀ i, Flat (E.f i).left)
    (hsurj : ∀ x : T.left, ∃ i, x ∈ Set.range (E.f i).left) (p : ℕ) (hp : 0 < p) :
    IsZero (cechCohomology E (bigBaseChange.{t} S N).presheaf p) := by
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
  have hc : IsColimit (Cofan.mk ((∐ E.X).left) (fun i ↦ (Sigma.ι E.X i).left)) :=
    (isColimitMapCoconeCofanMkEquiv (Over.forget S) E.X _)
      (isColimitOfPreserves (Over.forget S) (coproductIsCoproduct E.X))
  have e : (∐ fun i ↦ (E.X i).left) ≅ (∐ E.X).left :=
    (coproductIsCoproduct (fun i ↦ (E.X i).left)).coconePointUniqueUpToIso hc
  have : IsAffine (∐ E.X).left := IsAffine.of_isIso e.inv
  have hflat' : Flat (Sigma.desc E.f).left := by
    rw [← left_sigmaDesc_eq E.X E.f]
    infer_instance
  have hsurj' : Surjective (Sigma.desc E.f).left := by
    rw [← left_sigmaDesc_eq E.X E.f]
    have : Surjective (Sigma.desc (fun i ↦ (E.f i).left)) :=
      Surjective.sigmaDesc_of_union_range_eq_univ (Set.eq_univ_iff_forall.mpr fun x =>
        Set.mem_iUnion.mpr (hsurj x))
    infer_instance
  have hff : ((Sigma.desc E.f).left).appTop.hom.FaithfullyFlat :=
    (Flat.flat_and_surjective_iff_faithfullyFlat_of_isAffine ((Sigma.desc E.f).left)).1
      ⟨hflat', hsurj'⟩
  refine (isZero_cechCohomology_singleton_bigBaseChange.{t} N T (Sigma.desc E.f) hff q).of_iso
    ((HomologicalComplex.homologyFunctor AddCommGrpCat.{max t u} (ComplexShape.up ℕ)
      (q + 1)).mapIso (cechComplexIsoCoproduct E (bigBaseChange.{t} S N).presheaf)).symm

end Cech

/-! ### Čech vanishing on the slices of an affine site -/

section Site

open Stacks.TerminalBaseChange Stacks.CechSite

universe v w

variable {C : Type v} [Category.{w} C] (L : C ⥤ Scheme.{u}) [HasPullbacks C]
  [PreservesLimitsOfShape WalkingCospan L] [∀ X, IsAffine (L.obj X)]

/-- **Čech vanishing in positive degrees for the base-change presheaf on the slice at `x` of a
site of affine schemes, along a finite family which is a flat covering of schemes.** -/
theorem isZero_cechCohomology_baseChangePresheaf_over (x : C)
    (N : ModuleCat.{max t u}
      ((overRingPresheaf (rings L ⋙ forget₂ CommRingCat RingCat) x).obj (op (Over.mk (𝟙 x)))))
    {V : Over x} (E : PreZeroHypercover.{max t u} V) [Finite E.I₀]
    (hE : (E.map (Over.forget x ⋙ L)).presieve₀ ∈ Scheme.precoverage @Flat (L.obj V.left))
    (p : ℕ) (hp : 0 < p) :
    letI := fun n i => hasProduct_fibreProducts E (fun _ _ _ => inferInstance) n i
    IsZero (cechCohomology E ((baseChangePresheaf.{t}
      (overRingPresheaf (rings L ⋙ forget₂ CommRingCat RingCat) x) (overIdTerminal x)).obj
        N).presheaf p) := by
  let := fun n i => hasProduct_fibreProducts E (fun _ _ _ => inferInstance) n i
  let := fun n i => hasProduct_fibreProducts (E.map (Over.post L)) (fun _ _ _ => inferInstance)
    n i
  obtain ⟨hcover, hflat⟩ := (Scheme.presieve₀_mem_precoverage_iff
    (E.map (Over.forget x ⋙ L))).mp hE
  have h : ∀ (n : ℕ) (i : Fin (n + 1) → E.I₀),
      IsIso (cechProductMapOfFunctor (Over.post L) E n i) := fun n i => by
    let := Stacks.Sites.preservesLimit_fibreProducts_overPost (Over.post L) E
      (fun _ _ _ => inferInstance) (fun _ _ _ => inferInstance) n i
    exact isIso_cechProductMapOfFunctor (Over.post L) E n i
  have : IsAffine ((Over.post L).obj V).left := inferInstanceAs (IsAffine (L.obj V.left))
  have : Finite (E.map (Over.post L)).I₀ := inferInstanceAs (Finite E.I₀)
  refine (isZero_cechCohomology_bigBaseChange.{t} N (E.map (Over.post L)) (fun i =>
    inferInstanceAs (IsAffine (L.obj (E.X i).left))) (fun i => hflat i) (fun y => hcover y)
      p hp).of_iso ?_
  exact (cechCohomologyIsoOfFunctor (Over.post L) E (bigBaseChange.{t} (L.obj x) N).presheaf
    h p).symm

end Site

end Stacks.AffineSiteBaseChange
