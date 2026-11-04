module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.CyclicCoverSections
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.EtaleModuleHomAcyclic
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.EtaleModuleRestrictScalarsAcyclic

/-!
# Cohomology with `ℤ/N'` coefficients read with `ℤ/N` coefficients

Let `N' ∣ N`, `ρ : ℤ/N → ℤ/N'` the reduction and `res` restriction of scalars along `ρ` of sheaves
of modules on the small étale site of a scheme `Y`. For a sheaf `M` of `ℤ/N'`-modules the map

`Ext^q_{ℤ/N'}(Λ'_Y, M) → Ext^q_{ℤ/N}(Λ_Y, res M)`,  `y ↦ res(y) ∘ ρ_Y`,

with `ρ_Y : Λ_Y ⟶ res Λ'_Y` the reduction of constant sheaves
(`Stacks.EtaleCohomology.ExtensionTorsor.unitSheafReduction`), is bijective
(`Stacks.EtaleCohomology.ExtensionTorsor.bijective_mk₀_unitSheafReduction_comp_mapExactFunctor`):
both sides are `H^q(Y, M)`. In degree zero both are the global sections of `M`; in positive
degree one shifts dimension along an injective presentation of `M`, `res` carrying injectives to
sheaves acyclic for the global sections
(`Stacks.EtaleCohomology.isAcyclicEverywhere_restrictScalars'`), which `Λ_Y` corepresents.

The dimension shift is the abstract
`CategoryTheory.Abelian.bijective_mk₀_comp_mapExactFunctor_of_subsingleton`.

## Main results

* `CategoryTheory.Abelian.bijective_mk₀_comp_mapExactFunctor_of_subsingleton`
* `Stacks.EtaleCohomology.ExtensionTorsor.homUnitSheafEquiv_eq_app`
* `Stacks.EtaleCohomology.ExtensionTorsor.subsingleton_ext_unitSheaf_restrictScalars_of_injective`
* `Stacks.EtaleCohomology.ExtensionTorsor.bijective_mk₀_unitSheafReduction_comp_mapExactFunctor`
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry Opposite

universe w w' u

namespace CategoryTheory.Abelian

variable {C : Type*} [Category C] [Abelian C] [HasExt.{w} C] {D : Type*} [Category D] [Abelian D]
  [HasExt.{w'} D] (F : D ⥤ C) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  {A : C} {A' : D} (ρ : A ⟶ F.obj A')

/-- The map `Ext^n(A', M) → Ext^n(A, F M)`, `y ↦ F(y) ∘ ρ`. -/
def mk₀CompMapExactFunctor (M : D) (n : ℕ) : Ext.{w'} A' M n →+ Ext.{w} A (F.obj M) n :=
  ((Ext.mk₀ ρ).precomp (F.obj M) (zero_add n)).comp (F.mapExtAddHom A' M n)

/-- The image of `y` under `mk₀CompMapExactFunctor F ρ M n` is `F(y)` precomposed with `ρ`. -/
theorem mk₀CompMapExactFunctor_apply (M : D) (n : ℕ) (y : Ext.{w'} A' M n) :
    mk₀CompMapExactFunctor F ρ M n y = (Ext.mk₀ ρ).comp (y.mapExactFunctor F) (zero_add n) :=
  rfl

/-- The map `y ↦ F(y) ∘ ρ` commutes with postcomposition by a morphism `g : M ⟶ M'` and by
`F(g)`. -/
theorem mk₀CompMapExactFunctor_comp_mk₀ {M M' : D} (g : M ⟶ M') (n : ℕ) (y : Ext.{w'} A' M n) :
    mk₀CompMapExactFunctor F ρ M' n (y.comp (Ext.mk₀ g) (add_zero n)) =
      (mk₀CompMapExactFunctor F ρ M n y).comp (Ext.mk₀ (F.map g)) (add_zero n) := by
  rw [mk₀CompMapExactFunctor_apply, mk₀CompMapExactFunctor_apply, Ext.mapExactFunctor_comp,
    Ext.mapExactFunctor_mk₀, Ext.comp_assoc_of_third_deg_zero]

/-- The map `y ↦ F(y) ∘ ρ` commutes with postcomposition by the extension class of a short
exact sequence `S` and by that of its image under `F`. -/
theorem mk₀CompMapExactFunctor_comp_extClass {S : ShortComplex D} (hS : S.ShortExact) (n : ℕ)
    (y : Ext.{w'} A' S.X₃ n) :
    mk₀CompMapExactFunctor F ρ S.X₁ (n + 1) (y.comp hS.extClass rfl) =
      (mk₀CompMapExactFunctor F ρ S.X₃ n y).comp (hS.map_of_exact F).extClass rfl := by
  rw [mk₀CompMapExactFunctor_apply, mk₀CompMapExactFunctor_apply, Ext.mapExactFunctor_comp,
    Ext.mapExactFunctor_extClass]
  exact (Ext.comp_assoc _ _ _ (zero_add n) rfl (by omega)).symm

attribute [local instance] Ext.subsingleton_of_injective in
/-- **Dimension shifting for `y ↦ F(y) ∘ ρ`.** If `F` is exact, the map is bijective in degree
zero, and `Ext^{p+1}(A, F I) = 0` for every injective `I`, then it is bijective in every
degree. -/
theorem bijective_mk₀_comp_mapExactFunctor_of_subsingleton [EnoughInjectives D]
    (h0 : ∀ M : D, Function.Bijective (mk₀CompMapExactFunctor F ρ M 0))
    (hI : ∀ (I : D) [Injective I] (p : ℕ), Subsingleton (Ext.{w} A (F.obj I) (p + 1)))
    (n : ℕ) (M : D) : Function.Bijective (mk₀CompMapExactFunctor F ρ M n) := by
  induction n generalizing M with
  | zero => exact h0 M
  | succ n hn =>
    let I : InjectivePresentation M := Classical.arbitrary _
    let S := ShortComplex.mk _ _ (cokernel.condition I.f)
    have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel I.f }
    have : Injective S.X₂ := I.injective
    have : Subsingleton (Ext.{w} A (S.map F).X₂ (n + 1)) := hI S.X₂ n
    exact AddMonoidHom.bijective_of_surjective_of_bijective_of_right_exact _ _ _ _
      (mk₀CompMapExactFunctor F ρ S.X₂ n) (mk₀CompMapExactFunctor F ρ S.X₃ n)
      (mk₀CompMapExactFunctor F ρ S.X₁ (n + 1))
      (by ext e; exact (mk₀CompMapExactFunctor_comp_mk₀ F ρ S.g n e).symm)
      (by ext e; exact (mk₀CompMapExactFunctor_comp_extClass F ρ hS n e).symm)
      ((ShortComplex.ab_exact_iff_function_exact _).mp
        (Ext.covariant_sequence_exact₃' A' hS n (n + 1) rfl))
      ((ShortComplex.ab_exact_iff_function_exact _).mp
        (Ext.covariant_sequence_exact₃' A (hS.map_of_exact F) n (n + 1) rfl))
      (hn S.X₂).surjective (hn S.X₃)
      (fun x₁ ↦ Ext.covariant_sequence_exact₁ _ hS x₁ (by subsingleton) rfl)
      (fun y₁ ↦ Ext.covariant_sequence_exact₁ _ (hS.map_of_exact F) y₁ (by subsingleton) rfl)

end CategoryTheory.Abelian

namespace Stacks.EtaleCohomology.ExtensionTorsor

variable {Y : Scheme.{u}}

/-- **A map out of `Λ_Y` is determined by the image of the section `1`**: the global section
attached to `v : Λ_Y ⟶ F` is `v` applied to the global section attached to the identity. -/
theorem homUnitSheafEquiv_eq_app (N : ℕ) (F : EtaleModules.{u, 0} (ZMod N) Y)
    (v : unitSheaf (X := Y) N ⟶ F) :
    homUnitSheafEquiv N F v = v.hom.app (op (etaleSiteTerminal Y))
      (homUnitSheafEquiv N (unitSheaf (X := Y) N) (𝟙 _)) := by
  simp only [homUnitSheafEquiv, Equiv.trans_apply, AddEquiv.toEquiv_eq_coe,
    AddEquiv.coe_toEquiv, Stacks.Cohomology.GlobalSections.moduleULiftHomAddEquiv_apply,
    Adjunction.homEquiv_unit]
  rfl

/-- A map `v : Λ_Y ⟶ F` with global section `t` sends the section `1` of `Λ_Y` to `t`. -/
private theorem symm_hom_app_homUnitSheafEquiv_id (N : ℕ) (F : EtaleModules.{u, 0} (ZMod N) Y)
    (t : F.obj.obj (op (etaleSiteTerminal Y))) :
    ((homUnitSheafEquiv N F).symm t).hom.app (op (etaleSiteTerminal Y))
      (homUnitSheafEquiv N (unitSheaf (X := Y) N) (𝟙 _)) = t := by
  rw [← homUnitSheafEquiv_eq_app]
  exact (homUnitSheafEquiv N F).apply_symm_apply _

section Reduction

variable {N N' : ℕ} (h : N' ∣ N) (Y)

/-- **The reduction `Λ_Y ⟶ res Λ'_Y`** of the constant sheaf `ℤ/N` onto the constant sheaf
`ℤ/N'` read as a sheaf of `ℤ/N`-modules, for `N' ∣ N`: the map sending the section `1` to the
section `1`. -/
def unitSheafReduction : unitSheaf (X := Y) N ⟶
    (etaleModuleRestrictScalars (ZMod.castHom h (ZMod N')) Y).obj (unitSheaf (X := Y) N') :=
  (homUnitSheafEquiv N _).symm (homUnitSheafEquiv N' (unitSheaf (X := Y) N') (𝟙 _))

/-- The global section attached to `unitSheafReduction Y h` is the section `1` of `Λ'_Y`. -/
theorem homUnitSheafEquiv_unitSheafReduction :
    homUnitSheafEquiv N _ (unitSheafReduction Y h) =
      homUnitSheafEquiv N' (unitSheaf (X := Y) N') (𝟙 _) :=
  (homUnitSheafEquiv N _).apply_symm_apply _

variable {Y}

/-- In degree zero, `y ↦ res(y) ∘ ρ_Y` is bijective: both sides are the global sections. -/
theorem bijective_mk₀CompMapExactFunctor_unitSheafReduction_zero
    (M : EtaleModules.{u, 0} (ZMod N') Y) :
    Function.Bijective (mk₀CompMapExactFunctor
      (etaleModuleRestrictScalars (ZMod.castHom h (ZMod N')) Y) (unitSheafReduction Y h) M 0) := by
  let R := etaleModuleRestrictScalars (ZMod.castHom h (ZMod N')) Y
  have key : ∀ f : unitSheaf (X := Y) N' ⟶ M, mk₀CompMapExactFunctor R (unitSheafReduction Y h)
      M 0 (Ext.mk₀ f) = Ext.mk₀ (unitSheafReduction Y h ≫ R.map f) := by
    intro f
    rw [mk₀CompMapExactFunctor_apply, Ext.mapExactFunctor_mk₀, Ext.mk₀_comp_mk₀]
  have hf : ∀ f : unitSheaf (X := Y) N' ⟶ M,
      homUnitSheafEquiv N (R.obj M) (unitSheafReduction Y h ≫ R.map f) =
        homUnitSheafEquiv N' M f := by
    intro f
    rw [homUnitSheafEquiv_eq_app, homUnitSheafEquiv_eq_app N' M f]
    show (R.map f).hom.app _ ((unitSheafReduction Y h).hom.app _ _) = _
    erw [symm_hom_app_homUnitSheafEquiv_id]
    rfl
  refine ⟨fun x y hxy => ?_, fun z => ?_⟩
  · obtain ⟨f, rfl⟩ := (Ext.mk₀_bijective _ _).2 x
    obtain ⟨g, rfl⟩ := (Ext.mk₀_bijective _ _).2 y
    rw [key, key] at hxy
    have h2 := congrArg (homUnitSheafEquiv N (R.obj M)) ((Ext.mk₀_bijective _ _).1 hxy)
    rw [hf, hf] at h2
    rw [(homUnitSheafEquiv N' M).injective h2]
  · obtain ⟨k, rfl⟩ := (Ext.mk₀_bijective _ _).2 z
    refine ⟨Ext.mk₀ ((homUnitSheafEquiv N' M).symm (homUnitSheafEquiv N (R.obj M) k)), ?_⟩
    rw [key]
    congr 1
    apply (homUnitSheafEquiv N (R.obj M)).injective
    rw [hf]
    exact (homUnitSheafEquiv N' M).apply_symm_apply _

/-- **`Λ_Y` is a retract of the free sheaf on the final object**, which corepresents the global
sections. -/
theorem exists_comp_eq_id_freeYonedaSheaf (N : ℕ) :
    ∃ (f : unitSheaf (X := Y) N ⟶ freeYonedaSheaf (Λ := ZMod N) (etaleSiteTerminal Y))
      (g : freeYonedaSheaf (Λ := ZMod N) (etaleSiteTerminal Y) ⟶ unitSheaf (X := Y) N),
      f ≫ g = 𝟙 _ := by
  let T := etaleSiteTerminal Y
  let FY := freeYonedaSheaf (Λ := ZMod N) T
  let corep := freeYonedaSheafSectionsCorepresentation (Λ := ZMod N) T
  let s := homUnitSheafEquiv N (unitSheaf (X := Y) N) (𝟙 _)
  let g : FY ⟶ unitSheaf (X := Y) N := corep.hom.app (unitSheaf (X := Y) N) s
  let f : unitSheaf (X := Y) N ⟶ FY := (homUnitSheafEquiv N FY).symm (corep.inv.app FY (𝟙 FY))
  refine ⟨f, g, (homUnitSheafEquiv N (unitSheaf (X := Y) N)).injective ?_⟩
  have hfs : f.hom.app (op T) s = corep.inv.app FY (𝟙 FY) :=
    symm_hom_app_homUnitSheafEquiv_id N FY _
  have hnat := ConcreteCategory.congr_hom (corep.inv.naturality g) (𝟙 FY)
  have hinv := ConcreteCategory.congr_hom (corep.hom_inv_id_app (unitSheaf (X := Y) N)) s
  rw [homUnitSheafEquiv_eq_app]
  show g.hom.app (op T) (f.hom.app (op T) s) = s
  rw [hfs]
  refine (hnat.symm.trans ?_).trans hinv
  show corep.inv.app _ (𝟙 FY ≫ g) = _
  rw [Category.id_comp]
  rfl

/-- **Restriction of scalars of an injective sheaf has no higher cohomology** read through `Λ_Y`:
`Ext^{p+1}_{ℤ/N}(Λ_Y, res I) = 0` for `I` an injective sheaf of `ℤ/N'`-modules. -/
theorem subsingleton_ext_unitSheaf_restrictScalars_of_injective
    (I : EtaleModules.{u, 0} (ZMod N') Y) [Injective I] (p : ℕ) :
    Subsingleton (Ext.{u + 1} (unitSheaf (X := Y) N)
      ((etaleModuleRestrictScalars (ZMod.castHom h (ZMod N')) Y).obj I) (p + 1)) := by
  have h0 := (rightAcyclic_sections_iff_ext_eq_zero _ _).1
    (isAcyclicEverywhere_restrictScalars' (ZMod.castHom h (ZMod N')) I (etaleSiteTerminal Y)) p
  obtain ⟨f, g, hfg⟩ := exists_comp_eq_id_freeYonedaSheaf (Y := Y) N
  have key : ∀ a : Ext.{u + 1} (unitSheaf (X := Y) N)
      ((etaleModuleRestrictScalars (ZMod.castHom h (ZMod N')) Y).obj I) (p + 1), a = 0 := by
    intro a
    have : a = (Ext.mk₀ f).comp ((Ext.mk₀ g).comp a (zero_add _)) (zero_add _) := by
      rw [Ext.mk₀_comp_mk₀_assoc, hfg, Ext.mk₀_id_comp]
    rw [this, h0 ((Ext.mk₀ g).comp a (zero_add _)), Ext.comp_zero]
  exact subsingleton_of_forall_eq 0 key

/-- **Cohomology with `ℤ/N'` coefficients is cohomology with `ℤ/N` coefficients**: for
`N' ∣ N` and a sheaf `M` of `ℤ/N'`-modules, `y ↦ res(y) ∘ ρ_Y` is a bijection
`Ext^q_{ℤ/N'}(Λ'_Y, M) → Ext^q_{ℤ/N}(Λ_Y, res M)`. -/
theorem bijective_mk₀_unitSheafReduction_comp_mapExactFunctor (q : ℕ)
    (M : EtaleModules.{u, 0} (ZMod N') Y) :
    Function.Bijective (fun y : Ext.{u + 1} (unitSheaf (X := Y) N') M q =>
      (Ext.mk₀ (unitSheafReduction Y h)).comp
        (y.mapExactFunctor (etaleModuleRestrictScalars (ZMod.castHom h (ZMod N')) Y))
        (zero_add q)) :=
  bijective_mk₀_comp_mapExactFunctor_of_subsingleton _ (unitSheafReduction Y h)
    (bijective_mk₀CompMapExactFunctor_unitSheafReduction_zero h)
    (fun I _ p => subsingleton_ext_unitSheaf_restrictScalars_of_injective h I p) q M

end Reduction

end Stacks.EtaleCohomology.ExtensionTorsor

end
