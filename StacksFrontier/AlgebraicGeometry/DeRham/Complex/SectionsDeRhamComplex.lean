module

public import StacksFrontier.AlgebraicGeometry.DeRham.CechCupProduct
public import StacksFrontier.AlgebraicGeometry.Perfect.Coherator.KunnethTotalCech

/-!
# The sections of the relative de Rham complex, as a complex of presheaves over the base

Let `q : X ⟶ T` be a morphism of schemes. The relative de Rham complex `Ω^•_{X/T}` is a complex
of sheaves of `q^{-1}𝒪_T`-modules, and its differential is `q^{-1}𝒪_T`-linear. Restricting the
scalars to the global functions `Γ(T, 𝒪_T)`, acting on the sections over an open `U ⊆ X` through
`q^♯ : Γ(T, 𝒪_T) ⟶ Γ(X, U)` (`AlgebraicGeometry.sectionsPresheaf`), the de Rham complex becomes a
complex of presheaves of `Γ(T, 𝒪_T)`-modules on `X`.

## Main definitions

* `AlgebraicGeometry.Scheme.Hom.sectionsDeRhamComplex`: the complex `U ↦ Γ(U, Ω^•_{X/T})` of
  presheaves of `Γ(T, 𝒪_T)`-modules on `X`.

## Main results

* `AlgebraicGeometry.Scheme.Hom.inverseImageStructureMap_app_map_inverseImageGlobalSections`:
  a global function of `T`, pulled back to `q^{-1}𝒪_T` and read in `𝒪_X` over `U`, is its image
  under `q^♯`.
* `AlgebraicGeometry.Scheme.Hom.deRhamComplex_d_appLE_smul`: the de Rham differential is linear
  over the global functions of `T`.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace Stacks.AlgebraicGeometry.SectionsBaseChange

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {X T : Scheme.{u}} (q : X ⟶ T)

/-- **A global function of the base, pulled back and read over an open `U`, is its image under
`q^♯`**: the composite `Γ(T, 𝒪_T) ⟶ Γ(X, q^{-1}𝒪_T) ⟶ Γ(U, q^{-1}𝒪_T) ⟶ Γ(U, 𝒪_X)` is
`q.appLE ⊤ U`. -/
theorem inverseImageStructureMap_app_map_inverseImageGlobalSections (U : X.Opens)
    (a : Γ(T, ⊤)) :
    (inverseImageStructureMap q).hom.app (op U)
        (((TopCat.Sheaf.pullback CommRingCat.{u} q.base).obj T.sheaf).obj.map
          (homOfLE (le_top : U ≤ ⊤)).op (inverseImageGlobalSections q a)) =
      q.appLE ⊤ U (le_preimage_top q U) a := by
  have hnat := ConcreteCategory.congr_hom
    ((inverseImageStructureMap q).hom.naturality (homOfLE (le_top : U ≤ ⊤)).op)
    (inverseImageGlobalSections q a)
  simp only [ConcreteCategory.comp_apply] at hnat
  rw [hnat]
  exact congrArg _ (ConcreteCategory.congr_hom
    (inverseImageGlobalSections_comp_inverseImageStructureMap_app q) a)

/-- **The de Rham differential is linear over the global functions of the base**, these acting on
sections over `U` through `q^♯`. -/
theorem deRhamComplex_d_appLE_smul (i j : ℕ) (U : X.Opens) (a : Γ(T, ⊤))
    (y : Γ(relativeDifferentialForms q (i : ℤ), U)) :
    (q.deRhamComplex.d i j).val.app (op U) (q.appLE ⊤ U (le_preimage_top q U) a • y) =
      q.appLE ⊤ U (le_preimage_top q U) a •
        (show Γ(relativeDifferentialForms q (j : ℤ), U) from
          (q.deRhamComplex.d i j).val.app (op U) y) := by
  rw [← inverseImageStructureMap_app_map_inverseImageGlobalSections q U a]
  exact map_smul ((q.deRhamComplex.d i j).val.app (op U)).hom
    (show ((AlgebraicGeometry.SheafOfModules.underlyingRingSheaf
        ((TopCat.Sheaf.pullback CommRingCat.{u} q.base).obj T.sheaf)).obj.obj (op U) : RingCat) from
      (((TopCat.Sheaf.pullback CommRingCat.{u} q.base).obj T.sheaf).obj.map
        (homOfLE (le_top : U ≤ ⊤)).op (inverseImageGlobalSections q a)))
    (show ((q.deRhamComplex).X i).val.obj (op U) from y)

/-- The arrow `i ⟶ j` of the de Rham complex on sections, as a morphism of presheaves of
`Γ(T, 𝒪_T)`-modules. -/
def sectionsDeRhamD (i j : ℕ) :
    sectionsPresheaf q (relativeDifferentialForms q (i : ℤ)) ⟶
      sectionsPresheaf q (relativeDifferentialForms q (j : ℤ)) where
  app U :=
    letI := baseModule q (relativeDifferentialForms q (i : ℤ)) U.unop
    letI := baseModule q (relativeDifferentialForms q (j : ℤ)) U.unop
    ModuleCat.ofHom
    { toFun := fun y => (q.deRhamComplex.d i j).val.app U y
      map_add' := fun y z => map_add ((q.deRhamComplex.d i j).val.app U).hom y z
      map_smul' := fun a y => deRhamComplex_d_appLE_smul q i j U.unop a y }
  naturality U V g := by
    refine ModuleCat.hom_ext (LinearMap.ext fun y => ?_)
    exact ConcreteCategory.congr_hom ((q.deRhamComplex.d i j).val.naturality g) y

/-- The component of `sectionsDeRhamD q i j` at `U` sends a section `y` to its image under the
de Rham differential `d : Ω^i_{X/T}(U) ⟶ Ω^j_{X/T}(U)`. -/
theorem sectionsDeRhamD_app_apply (i j : ℕ) (U : (X.Opens)ᵒᵖ)
    (y : Γ(relativeDifferentialForms q (i : ℤ), U.unop)) :
    ((sectionsDeRhamD q i j).app U).hom y = (q.deRhamComplex.d i j).val.app U y :=
  rfl

/-- **The sections of the relative de Rham complex**, `U ↦ Γ(U, Ω^•_{X/T})`, as a complex of
presheaves of `Γ(T, 𝒪_T)`-modules on `X`, the global functions of `T` acting through `q^♯`. -/
abbrev sectionsDeRhamComplex : CochainComplex ((X.Opens)ᵒᵖ ⥤ ModuleCat.{u} Γ(T, ⊤)) ℕ where
  X n := sectionsPresheaf q (relativeDifferentialForms q (n : ℤ))
  d i j := sectionsDeRhamD q i j
  shape i j h := by
    ext U : 2
    refine ModuleCat.hom_ext (LinearMap.ext fun y => ?_)
    change (q.deRhamComplex.d i j).val.app U y = 0
    rw [q.deRhamComplex.shape i j h]
    rfl
  d_comp_d' i j k _ _ := by
    ext U : 2
    refine ModuleCat.hom_ext (LinearMap.ext fun y => ?_)
    have h := congrArg (fun φ => φ.val.app U) (q.deRhamComplex.d_comp_d i j k)
    exact (ConcreteCategory.congr_hom h y).trans rfl

end AlgebraicGeometry.Scheme.Hom

end
