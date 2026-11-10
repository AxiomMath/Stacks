module

public import StacksFrontier.AlgebraicGeometry.Duality.CurveFamilyDualizing.TransitionTransport
public import StacksFrontier.AlgebraicGeometry.Blowup.PerfectHomomorphism
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.TopDegreeTensorNaturality
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EpiLocallySurjective
public import StacksFrontier.Topology.Sheaves.RingedSpace.ModuleUnitEpi

/-!
# Every identification of the diagonal objects can be normalised

Let `D`, `D'` be diagonal opens of `f : X ⟶ S` and `f' : X' ⟶ S'`, and `w : W' ⟶ W` a morphism
of schemes. If `e : Lw^*Δ_*𝒪_X ≅ Δ'_*𝒪_{X'}` is any isomorphism, then `Lw^*` of the unit
`𝒪_W ⟶ Δ_*𝒪_X`, read through `e` and `Lw^*𝒪_W ≅ 𝒪_{W'}`, is the unit of `Δ'_*𝒪_{X'}` followed by
multiplication by a *unit* `c` of `Γ(X', 𝒪_{X'})`. Rescaling `e` by `c⁻¹` therefore gives a
normalised identification (`AlgebraicGeometry.Scheme.Hom.DiagonalOpen.IsUnitNormalized`).

That `c` is a unit is a statement about `H⁰`: `H⁰(Lw^*(Δ_*𝒪_X))` is `w^*Δ_*𝒪_X`, the functor
`w^*` preserves epimorphisms and the unit `𝒪_W ⟶ Δ_*𝒪_X` is an epimorphism (`Δ` is a closed
immersion), so the map `𝒪_{W'} ⟶ Δ'_*𝒪_{X'}` above is an epimorphism of sheaves; hence so is
multiplication by `c` on `Δ'_*𝒪_{X'}`, and `c` is then locally, hence globally, invertible.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.Duality.TwistedInverseImageDuality
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback)
open RingedSpaceModuleAdjunction
open DerivedCategory (homologyFunctor)

universe u

namespace AlgebraicGeometry.Scheme.Hom.DiagonalOpen

variable {X S X' S' : Scheme.{u}} {f : X ⟶ S} {f' : X' ⟶ S'}

/-- A morphism isomorphic, in the arrow category, to an epimorphism is an epimorphism. -/
theorem epi_of_comp_eq_comp_epi {C : Type*} [Category C] {A B A' B' : C} (x : A ⟶ B)
    (iA : A ⟶ A') (iB : B ⟶ B') [IsIso iA] [IsIso iB] (y : A' ⟶ B') [Epi y]
    (h : x ≫ iB = iA ≫ y) : Epi x := by
  rw [show x = (iA ≫ y) ≫ inv iB by rw [← h, Category.assoc, IsIso.hom_inv_id, Category.comp_id]]
  infer_instance

/-- **`H⁰ ∘ Lw^* ∘ (-)[0]` preserves epimorphisms**: `H⁰(Lw^*(M[0])) = w^*M` naturally in `M`,
and `w^*` is a left adjoint. -/
theorem epi_homology_derivedPullback_single_map {Y Z : RingedSpace.{u, u}} (w : Y ⟶ Z)
    {M N : SheafOfModules.{u} (structureSheafRing Z)} (φ : M ⟶ N) (hφ : Epi φ) :
    letI := HasDerivedCategory.standard (SheafOfModules (structureSheafRing Y))
    letI := HasDerivedCategory.standard (SheafOfModules (structureSheafRing Z))
    Epi ((homologyFunctor (SheafOfModules.{u} (structureSheafRing Y)) 0).map
      ((derivedPullback w).map ((DerivedCategory.singleFunctor _ 0).map φ))) := by
  let (Z : RingedSpace.{u, u}) (A : Abelian (SheafOfModules (structureSheafRing Z))) :=
    @HasDerivedCategory.standard (SheafOfModules (structureSheafRing Z)) _ A
  have hn := derivedToOrdinaryPullbackSingle_naturality w φ 0
  have hs := Stacks.AlgebraicGeometry.TopDegreeBaseChange.homologySingleIso_hom_naturality
    ((modulePullback w).map φ) 0
  have hM := Stacks.AlgebraicGeometry.TopDegreeBaseChange.isIso_homologyDerivedPullbackSingleMap
    w M 0
  have hN := Stacks.AlgebraicGeometry.TopDegreeBaseChange.isIso_homologyDerivedPullbackSingleMap
    w N 0
  have : (modulePullback w).PreservesEpimorphisms :=
    Functor.preservesEpimorphisms_of_adjunction (modulePullbackPushforwardAdjunction w)
  have : Epi ((modulePullback w).map φ) := (modulePullback w).map_epi φ
  refine epi_of_comp_eq_comp_epi _
    (Stacks.AlgebraicGeometry.TopDegreeBaseChange.homologyDerivedPullbackSingleMap w M 0)
    (Stacks.AlgebraicGeometry.TopDegreeBaseChange.homologyDerivedPullbackSingleMap w N 0)
    ((modulePullback w).map φ) ?_
  simp only [Stacks.AlgebraicGeometry.TopDegreeBaseChange.homologyDerivedPullbackSingleMap,
    ← Category.assoc, ← Functor.map_comp, hn]
  rw [Functor.map_comp, Category.assoc, hs, Category.assoc]

/-- A morphism of sheaves of modules out of the structure sheaf of a scheme is determined by the
image of the section `1` over the whole scheme. -/
theorem unit_hom_ext {Y : Scheme.{u}} {M : SheafOfModules.{u} Y.ringCatSheaf}
    {φ ψ : SheafOfModules.unit Y.ringCatSheaf ⟶ M}
    (h : (φ.val.app (op ⊤)).hom (1 : Γ(Y, ⊤)) = (ψ.val.app (op ⊤)).hom (1 : Γ(Y, ⊤))) :
    φ = ψ := by
  apply M.unitHomEquiv.injective
  apply Subtype.ext
  funext U
  have hφ := (M.unitHomEquiv φ).property (homOfLE le_top : U.unop ⟶ ⊤).op
  have hψ := (M.unitHomEquiv ψ).property (homOfLE le_top : U.unop ⟶ ⊤).op
  refine hφ.symm.trans (Eq.trans ?_ hψ)
  exact congrArg _ h

/-- Restricting `pr₁^♯ c` to an open `V` of `W` and applying `Δ^♯` is restricting `c` to `Δ⁻¹V`:
`Δ` is a section of `pr₁|_W`. -/
theorem diag_app_map_proj_appTop (D : DiagonalOpen f) (V : D.W.Opens) (c : Γ(X, ⊤)) :
    D.diag.app V (D.W.presheaf.map (homOfLE le_top : V ⟶ ⊤).op (D.proj.appTop c)) =
      X.presheaf.map ((Opens.map D.diag.base).map (homOfLE le_top : V ⟶ ⊤)).op c := by
  have hn := congrArg (fun φ : D.W.presheaf.obj (op ⊤) ⟶
      X.presheaf.obj (op (D.diag ⁻¹ᵁ V)) => φ (D.proj.appTop c))
    (D.diag.naturality (homOfLE le_top : V ⟶ ⊤).op)
  simp only [ConcreteCategory.comp_apply] at hn
  exact hn.trans <| congrArg (ConcreteCategory.hom (X.presheaf.map ((Opens.map D.diag.base).map
    (homOfLE le_top : V ⟶ ⊤)).op)) (D.diag_app_top_proj_appTop_apply c)

/-- **Multiplication by `c` is an epimorphism of `Δ_*𝒪_X` only if `c` is a unit**: locally on
`W`, the section `1` is `c` times a section, so `c` is invertible near every point of `X`. -/
theorem isUnit_of_epi_diagonalScalar (D : DiagonalOpen f) (c : Γ(X, ⊤))
    [Epi (D.diagonalScalar c)] : IsUnit c := by
  refine X.toRingedSpace.isUnit_of_isUnit_germ ⊤ c (fun x _ => ?_)
  have hS := Stacks.SheafOfModules.EpiMono.imageSieve_mem_of_epi (D.diagonalScalar c)
    (V := (⊤ : D.W.Opens)) (Stacks.RelativeSpec.AlgebraSheaf.oneSection D.diagonalAlgebra (op ⊤))
  obtain ⟨V, i, ⟨t, ht⟩, hxV⟩ := hS (D.diag.base x) trivial
  obtain rfl : i = homOfLE le_top := Subsingleton.elim _ _
  have hmul : X.presheaf.map ((Opens.map D.diag.base).map (homOfLE le_top : V ⟶ ⊤)).op c *
      (show X.presheaf.obj (op (D.diag ⁻¹ᵁ V)) from t) = 1 := by
    rw [← D.diag_app_map_proj_appTop V c]
    have ht' : ((D.diagonalScalar c).val.app (op V)).hom t =
        (1 : D.diagonalAlgebra.right.obj.obj (op V)) := by
      refine ht.trans ?_
      exact map_one (D.diagonalAlgebra.right.obj.map (homOfLE le_top : V ⟶ ⊤).op).hom
    refine Eq.trans ?_ ht'
    rfl
  have hg := (IsUnit.of_mul_eq_one _ hmul).map (X.presheaf.germ (D.diag ⁻¹ᵁ V) x hxV).hom
  rwa [X.presheaf.germ_res_apply ((Opens.map D.diag.base).map (homOfLE le_top : V ⟶ ⊤)) x hxV c]
    at hg

/-- The unit `𝒪_W ⟶ Δ_*𝒪_X` of a closed immersion is an epimorphism of `𝒪_W`-modules. -/
theorem epi_unitModuleMap_diagonalAlgebra (D : DiagonalOpen f) :
    Epi (Stacks.RelativeSpec.AlgebraSheaf.unitModuleMap D.diagonalAlgebra) := by
  refine Stacks.SheafOfModules.EpiMono.epi_of_isLocallySurjective _ ?_
  have := D.isClosedImmersion
  change TopCat.Presheaf.IsLocallySurjective _
  rw [TopCat.Presheaf.isLocallySurjective_iff]
  intro U t x hx
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ :=
    (isBasis_affineOpens D.W).exists_subset_of_mem_open hx U.isOpen
  obtain ⟨s, hs⟩ := D.diag.app_surjective V hV (TopCat.Presheaf.restrictOpen t V hVU)
  exact ⟨V, hVU, ⟨s, hs⟩, hxV⟩

/-- An image under a functor of a morphism which is an epimorphism up to isomorphisms on
both sides is an epimorphism. -/
theorem epi_homology_chase {𝒟 C : Type*} [Category 𝒟] [Category C] (H : 𝒟 ⥤ C) {A A' B B' : 𝒟}
    (n : A' ≅ A) (L : A ⟶ B) (e : B ≅ B') (hL : Epi (H.map L))
    (m : A' ⟶ B') (hm : m = n.hom ≫ L ≫ e.hom) : Epi (H.map m) := by
  subst hm
  rw [Functor.map_comp, Functor.map_comp]
  infer_instance

/-- A morphism isomorphic, in the arrow category, to an epimorphism is an epimorphism (the
epimorphism on the left). -/
theorem epi_of_comp_eq_comp_epi' {C : Type*} [Category C] {A B A' B' : C} (x : A ⟶ B)
    (iA : A ⟶ A') (iB : B ⟶ B') [IsIso iA] [IsIso iB] (y : A' ⟶ B') [Epi x]
    (h : x ≫ iB = iA ≫ y) : Epi y := by
  have : Epi (x ≫ iB) := inferInstance
  exact epi_of_epi_fac h.symm

/-- A morphism of sheaves of modules whose image under `H⁰ ∘ (-)[0]` is an epimorphism is an
epimorphism. -/
theorem epi_of_epi_homology_single {Y : RingedSpace.{u, u}}
    {M N : SheafOfModules.{u} (structureSheafRing Y)} (φ : M ⟶ N)
    (h : letI := HasDerivedCategory.standard (SheafOfModules (structureSheafRing Y))
      Epi ((homologyFunctor (SheafOfModules.{u} (structureSheafRing Y)) 0).map
        ((DerivedCategory.singleFunctor _ 0).map φ))) : Epi φ :=
  let (Z : RingedSpace.{u, u}) (A : Abelian (SheafOfModules (structureSheafRing Z))) :=
    @HasDerivedCategory.standard (SheafOfModules (structureSheafRing Z)) _ A
  epi_of_comp_eq_comp_epi' _ _ _ φ
    (Stacks.AlgebraicGeometry.TopDegreeBaseChange.homologySingleIso_hom_naturality φ 0)

/-- **The unit scalar of an identification of the diagonal objects is a unit.** For any
isomorphism `e : Lw^*Δ_*𝒪_X ≅ Δ'_*𝒪_{X'}`, `Lw^*` of the unit `𝒪_W ⟶ Δ_*𝒪_X` read through `e`
and `𝒪_{W'} ≅ Lw^*𝒪_W` is the unit of `Δ'_*𝒪_{X'}` followed by multiplication by a unit of
`Γ(X', 𝒪_{X'})`. -/
theorem exists_isUnit_unitMap_comp (D : DiagonalOpen f) (D' : DiagonalOpen f') (w : D'.W ⟶ D.W)
    (e : (pull w).obj D.diagonalObject ≅ D'.diagonalObject) :
    let := D'.proj.linearStructureSheafModules
    ∃ c : Γ(X', ⊤), IsUnit c ∧
      (unitPullIso w).inv ≫ (pull w).map D.diagonalUnitMap ≫ e.hom =
        D'.diagonalUnitMap ≫ (c • 𝟙 D'.diagonalObject) := by
  let := D'.proj.linearStructureSheafModules
  let := HasDerivedCategory.standard (Stacks.SheafOfModules.StructureSheafModules D'.W.sheaf)
  let (Z : RingedSpace.{u, u}) (A : Abelian (SheafOfModules (structureSheafRing Z))) :=
    @HasDerivedCategory.standard (SheafOfModules (structureSheafRing Z)) _ A
  let m : Stacks.DerivedTensor.RingedSite.unitObject (Stacks.SheafOfModules.ringedSite D'.W.sheaf)
      ⟶ D'.diagonalObject := (unitPullIso w).inv ≫ (pull w).map D.diagonalUnitMap ≫ e.hom
  let m₀ : SheafOfModules.unit D'.W.ringCatSheaf ⟶ D'.diagonalAlgebra.moduleOfAlgebra :=
    (DerivedCategory.singleFunctor (Stacks.SheafOfModules.StructureSheafModules D'.W.sheaf)
      0).preimage m
  have hm₀ : (DerivedCategory.singleFunctor
      (Stacks.SheafOfModules.StructureSheafModules D'.W.sheaf) 0).map m₀ = m :=
    Functor.map_preimage _ _
  let c : Γ(X', ⊤) := (m₀.val.app (op ⊤)).hom (1 : Γ(D'.W, ⊤))
  have hc : m₀ = Stacks.RelativeSpec.AlgebraSheaf.unitModuleMap D'.diagonalAlgebra ≫
      D'.diagonalScalar c := by
    apply unit_hom_ext
    have e1 : ((Stacks.RelativeSpec.AlgebraSheaf.unitModuleMap D'.diagonalAlgebra).val.app
        (op ⊤)).hom (1 : Γ(D'.W, ⊤)) = (1 : D'.diagonalAlgebra.right.obj.obj (op ⊤)) :=
      Stacks.RelativeSpec.AlgebraSheaf.structSection_one _ _
    change c = ((D'.diagonalScalar c).val.app (op ⊤)).hom
      (((Stacks.RelativeSpec.AlgebraSheaf.unitModuleMap D'.diagonalAlgebra).val.app
        (op ⊤)).hom (1 : Γ(D'.W, ⊤)))
    rw [e1]
    exact (D'.diagonalScalar_app_top_one c).symm
  refine ⟨c, ?_, ?_⟩
  · have hL := epi_homology_derivedPullback_single_map w.toLRSHom.toShHom
      (Stacks.RelativeSpec.AlgebraSheaf.unitModuleMap D.diagonalAlgebra)
      D.epi_unitModuleMap_diagonalAlgebra
    have hm' : (DerivedCategory.singleFunctor
        (SheafOfModules.{u} (structureSheafRing D'.W.toRingedSpace)) 0).map m₀ =
        (unitPullIso w).inv ≫ (derivedPullback w.toLRSHom.toShHom).map
          ((DerivedCategory.singleFunctor
            (SheafOfModules.{u} (structureSheafRing D.W.toRingedSpace)) 0).map
            (Stacks.RelativeSpec.AlgebraSheaf.unitModuleMap D.diagonalAlgebra)) ≫ e.hom := hm₀
    have hH := epi_homology_chase
      (homologyFunctor (SheafOfModules.{u} (structureSheafRing D'.W.toRingedSpace)) 0)
      (unitPullIso w).symm _ e hL _ hm'
    have hm₀' : Epi m₀ := epi_of_epi_homology_single m₀ hH
    rw [hc] at hm₀'
    have : Epi (D'.diagonalScalar c) :=
      epi_of_epi (Stacks.RelativeSpec.AlgebraSheaf.unitModuleMap D'.diagonalAlgebra) _
    exact D'.isUnit_of_epi_diagonalScalar c
  · rw [D'.smul_id_diagonalObject c]
    change m = _
    rw [← hm₀, hc]
    exact Functor.map_comp _ _ _

/-- Multiplication by the inverse of a unit, as an automorphism in a linear category. -/
def unitSmulIso {R C : Type*} [CommRing R] [Category C] [Preadditive C] [Linear R C] (A : C)
    (a : Rˣ) : A ≅ A where
  hom := a.inv • 𝟙 A
  inv := a.val • 𝟙 A
  hom_inv_id := by rw [Linear.smul_comp, Category.id_comp, smul_smul, Units.inv_val, one_smul]
  inv_hom_id := by rw [Linear.smul_comp, Category.id_comp, smul_smul, Units.val_inv, one_smul]

/-- The chase behind `exists_isUnitNormalized`, with every object a variable. -/
theorem normalize_chase {C : Type*} [Category C] {L A T U : C} (Lu : L ⟶ A) (ν : L ≅ U)
    (u' : U ⟶ T) (e : A ≅ T) (s : T ≅ T) (hc : ν.inv ≫ Lu ≫ e.hom = u' ≫ s.inv) :
    Lu ≫ (e ≪≫ s).hom = ν.hom ≫ u' := by
  rw [Iso.inv_comp_eq] at hc
  rw [Iso.trans_hom, reassoc_of% hc, Iso.inv_hom_id, Category.comp_id]

/-- **Every identification of the diagonal objects can be normalised**: rescaled by a unit of
`Γ(X', 𝒪_{X'})` it carries the unit of `Δ_*𝒪_X` to that of `Δ'_*𝒪_{X'}`. -/
theorem exists_isUnitNormalized (D : DiagonalOpen f) (D' : DiagonalOpen f') (w : D'.W ⟶ D.W)
    (e : (pull w).obj D.diagonalObject ≅ D'.diagonalObject) :
    ∃ e' : (pull w).obj D.diagonalObject ≅ D'.diagonalObject, IsUnitNormalized D D' w e' := by
  let := D'.proj.linearStructureSheafModules
  obtain ⟨c, ⟨c', rfl⟩, hc⟩ := exists_isUnit_unitMap_comp D D' w e
  let s : D'.diagonalObject ≅ D'.diagonalObject := unitSmulIso D'.diagonalObject c'
  exact ⟨e ≪≫ s, normalize_chase _ (unitPullIso w) D'.diagonalUnitMap e s hc⟩

end AlgebraicGeometry.Scheme.Hom.DiagonalOpen

end
