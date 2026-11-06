module

public import StacksFrontier.Algebra.Homology.DerivedCategory.Ext.MapAlongAcyclic
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.ExtensionTorsor

/-!
# Changing the level of the coefficients `ℤ/N`

Let `d ∣ N`. A sheaf of `ℤ/d`-modules on the small étale site of a scheme `X` is a sheaf of
`ℤ/N`-modules through `ℤ/N ↠ ℤ/d`; write `R` for this restriction of scalars. The reduction
`π : ℤ/N_X ⟶ R(ℤ/d_X)` is the image of `ℤ/N ↠ ℤ/d` under the constant sheaf functor, and

`Ext^i_{ℤ/d}(ℤ/d_X, G) ⟶ Ext^i_{ℤ/N}(ℤ/N_X, R G)`, `y ↦ π ∘ R(y)`

is bijective for every sheaf `G` of `ℤ/d`-modules
(`Stacks.EtaleCohomology.LevelChange.extMap_bijective`): in degree zero both sides are the global
sections of `G`, and in higher degrees the right hand side vanishes on injective `G`, being the
cohomology of `G` ([Stacks, Tag 03FD]). This map is compatible with the Yoneda product:
`π ∘ R(y ∘ b) = (π ∘ R y) ∘ R b` (`Stacks.EtaleCohomology.LevelChange.extMap_comp`).

For `N = d e` the reduction and multiplication by `d` fit into a short exact sequence
`0 → R(ℤ/e_X) → ℤ/N_X → R(ℤ/d_X) → 0`
(`Stacks.EtaleCohomology.LevelChange.inclusionShortComplex_shortExact`), and multiplication by `d`
on `ℤ/N_X` factors through it (`Stacks.EtaleCohomology.LevelChange.reduction_comp_inclusion`).

## Main definitions

* `Stacks.EtaleCohomology.etaleModuleRestrictScalarsConstantIso`: restriction of scalars of a
  constant sheaf is constant.
* `Stacks.EtaleCohomology.LevelChange.restrict`: restriction of scalars along `ℤ/N ↠ ℤ/d`.
* `Stacks.EtaleCohomology.LevelChange.reduction`: `ℤ/N_X ⟶ R(ℤ/d_X)`.
* `Stacks.EtaleCohomology.LevelChange.inclusion`: `R(ℤ/e_X) ⟶ ℤ/N_X`, multiplication by `d`.
* `Stacks.EtaleCohomology.LevelChange.extMap`: the comparison of `Ext` groups.

## References

* [Stacks Project, Tag 03FD](https://stacks.math.columbia.edu/tag/03FD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry Opposite

universe u

namespace Stacks.EtaleCohomology

section Constant

variable {Λ Λ' : Type} [Ring Λ] [Ring Λ'] (ρ : Λ →+* Λ') (X : Scheme.{u})

/-- **Restriction of scalars of a constant sheaf is the constant sheaf on the restriction of
scalars**, for sheaves of modules on the small étale site. -/
def etaleModuleRestrictScalarsConstantIso :
    constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ') ⋙ etaleModuleRestrictScalars ρ X ≅
      ModuleCat.restrictScalars.{u + 1} ρ ⋙
        constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ) :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (Functor.const X.Etaleᵒᵖ)
      (sheafComposeNatIso X.smallEtaleTopology (ModuleCat.restrictScalars.{u + 1} ρ)
        (sheafificationAdjunction _ _) (sheafificationAdjunction _ _)).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (Functor.compConstIso X.Etaleᵒᵖ
      (ModuleCat.restrictScalars.{u + 1} ρ)).symm _ ≪≫
    Functor.associator _ _ _

end Constant

namespace LevelChange

open ExtensionTorsor

variable (X : Scheme.{u}) {N d : ℕ} (h : d ∣ N)

/-- Restriction of scalars along `ℤ/N ↠ ℤ/d`, from sheaves of `ℤ/d`-modules to sheaves of
`ℤ/N`-modules on the small étale site of `X`. -/
abbrev restrict : EtaleModules.{u, 0} (ZMod d) X ⥤ EtaleModules.{u, 0} (ZMod N) X :=
  etaleModuleRestrictScalars (ZMod.castHom h (ZMod d)) X

/-- `ℤ/N ↠ ℤ/d` as a `ℤ/N`-linear map. -/
def reductionLinearMap :
    ModuleCat.of (ZMod N) (ULift.{u + 1} (ZMod N)) ⟶
      (ModuleCat.restrictScalars.{u + 1} (ZMod.castHom h (ZMod d))).obj
        (ModuleCat.of (ZMod d) (ULift.{u + 1} (ZMod d))) :=
  ModuleCat.ofHom (Y := (ModuleCat.restrictScalars.{u + 1} (ZMod.castHom h (ZMod d))).obj
      (ModuleCat.of (ZMod d) (ULift.{u + 1} (ZMod d))))
    ({ toFun := fun x => ULift.up (ZMod.castHom h (ZMod d) x.down)
       map_add' := fun x y => ULift.ext (map_add (ZMod.castHom h (ZMod d)) x.down y.down)
       map_smul' := fun a x => ULift.ext (map_mul (ZMod.castHom h (ZMod d)) a x.down) } :
      ULift.{u + 1} (ZMod N) →ₗ[ZMod N]
        (ModuleCat.restrictScalars.{u + 1} (ZMod.castHom h (ZMod d))).obj
          (ModuleCat.of (ZMod d) (ULift.{u + 1} (ZMod d))))

/-- `ℤ/N ↠ ℤ/d` sends `x` to its reduction. -/
theorem reductionLinearMap_apply (x : ULift.{u + 1} (ZMod N)) :
    ((reductionLinearMap.{u} h).hom x : ULift.{u + 1} (ZMod d)) =
      ULift.up (ZMod.castHom h (ZMod d) x.down) :=
  rfl

/-- `ℤ/N ↠ ℤ/d` is surjective. -/
theorem surjective_reductionLinearMap : Function.Surjective (reductionLinearMap.{u} h).hom := by
  intro y
  obtain ⟨x, hx⟩ := ZMod.ringHom_surjective (ZMod.castHom h (ZMod d)) y.down
  exact ⟨ULift.up x, (reductionLinearMap_apply h _).trans (ULift.ext hx)⟩

/-- **The reduction `ℤ/N_X ⟶ R(ℤ/d_X)`**: the constant sheaf on `ℤ/N ↠ ℤ/d`. -/
def reduction : unitSheaf (X := X) N ⟶ (restrict X h).obj (unitSheaf d) :=
  (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ZMod N))).map (reductionLinearMap h) ≫
    ((etaleModuleRestrictScalarsConstantIso (ZMod.castHom h (ZMod d)) X).app
      (ModuleCat.of (ZMod d) (ULift.{u + 1} (ZMod d)))).inv

/-- The constant sheaf functor on the small étale site is a left adjoint. -/
instance : (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ZMod N))).IsLeftAdjoint :=
  (constantSheafAdj X.smallEtaleTopology (ModuleCat.{u + 1} (ZMod N))
    (etaleSiteTerminalIsTerminal X)).isLeftAdjoint

/-- The reduction `ℤ/N_X ⟶ R(ℤ/d_X)` is an epimorphism. -/
instance epi_reduction : Epi (reduction X h) := by
  have : Epi (reductionLinearMap.{u} h) :=
    (ModuleCat.epi_iff_surjective _).2 (surjective_reductionLinearMap h)
  unfold reduction
  infer_instance

/-- Restriction of scalars along the surjection `ℤ/N ↠ ℤ/d` is full: a `ℤ/N`-linear map between
`ℤ/d`-modules is `ℤ/d`-linear. -/
instance full_restrict : (restrict X h).Full := by
  have : (ModuleCat.restrictScalars.{u + 1} (ZMod.castHom h (ZMod d))).Full :=
    { map_surjective := fun {M M'} g => by
        refine ⟨ModuleCat.ofHom
          { toFun := g.hom
            map_add' := map_add g.hom
            map_smul' := fun s x => ?_ }, rfl⟩
        obtain ⟨r, rfl⟩ := ZMod.ringHom_surjective (ZMod.castHom h (ZMod d)) s
        exact g.hom.map_smul r x }
  infer_instance

/-- Multiplication by `d` vanishes on a sheaf of `ℤ/d`-modules read as a sheaf of
`ℤ/N`-modules. -/
theorem nsmul_id_restrict (G : EtaleModules.{u, 0} (ZMod d) X) :
    d • 𝟙 ((restrict X h).obj G) = 0 := by
  ext U x
  show d • (show G.obj.obj U from x) = 0
  rw [← Nat.cast_smul_eq_nsmul (ZMod d), ZMod.natCast_self, zero_smul]

/-- The short complex `ℤ/N_X --d--> ℤ/N_X --π--> R(ℤ/d_X)`. -/
abbrev reductionShortComplex : ShortComplex (EtaleModules.{u, 0} (ZMod N) X) :=
  ShortComplex.mk (d • 𝟙 (unitSheaf (X := X) N)) (reduction X h) (by
    have e := Preadditive.comp_nsmul (reduction X h) (𝟙 _) d
    rw [Category.comp_id] at e
    rw [Preadditive.nsmul_comp, Category.id_comp, ← e, nsmul_id_restrict, comp_zero])

/-- If `y : ℤ/N` reduces to `0` in `ℤ/d`, then `y.val = d * m` for some `m : ℕ`. -/
private theorem exists_val_eq_mul_of_castHom_eq_zero [NeZero N] {y : ZMod N}
    (hy : ZMod.castHom h (ZMod d) y = 0) : ∃ m : ℕ, y.val = d * m :=
  (ZMod.natCast_eq_zero_iff _ _).1 ((ZMod.natCast_val _).trans hy)

/-- `ℤ/N --d--> ℤ/N --> ℤ/d` is exact. -/
theorem function_exact_reductionLinearMap [NeZero N] :
    Function.Exact (d • 𝟙 (ModuleCat.of (ZMod N) (ULift.{u + 1} (ZMod N)))).hom
      (reductionLinearMap.{u} h).hom := by
  intro y
  rw [reductionLinearMap_apply]
  constructor
  · intro hy
    obtain ⟨m, hm⟩ := exists_val_eq_mul_of_castHom_eq_zero h (congrArg ULift.down hy)
    refine ⟨ULift.up (m : ZMod N), ULift.ext ?_⟩
    show d • (m : ZMod N) = y.down
    rw [nsmul_eq_mul, ← Nat.cast_mul, ← hm, ZMod.natCast_zmod_val]
  · rintro ⟨x, rfl⟩
    refine ULift.ext ?_
    show ZMod.castHom h (ZMod d) (d • x.down) = 0
    rw [map_nsmul, nsmul_eq_mul, ZMod.natCast_self, zero_mul]

/-- Multiplication by `N` vanishes on `ℤ/N_X`. -/
theorem nsmul_id_unitSheaf : N • 𝟙 (unitSheaf (X := X) N) = 0 := by
  ext U x
  show N • x = 0
  rw [← Nat.cast_smul_eq_nsmul (ZMod N), ZMod.natCast_self, zero_smul]

/-- **`ℤ/N_X --d--> ℤ/N_X --π--> R(ℤ/d_X)` is exact.** -/
theorem reductionShortComplex_exact [NeZero N] : (reductionShortComplex X h).Exact := by
  let C := constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ZMod N))
  let Sm : ShortComplex (ModuleCat.{u + 1} (ZMod N)) :=
    ShortComplex.mk (d • 𝟙 (ModuleCat.of (ZMod N) (ULift.{u + 1} (ZMod N))))
      (reductionLinearMap h) (by
        ext x
        exact (function_exact_reductionLinearMap h _).2 ⟨x, rfl⟩)
  have hSm : Sm.Exact := ModuleCat.shortComplex_exact _ (function_exact_reductionLinearMap h)
  refine (ShortComplex.exact_iff_of_iso ?_).1 (hSm.map C)
  refine ShortComplex.isoMk (Iso.refl _) (Iso.refl _)
    ((etaleModuleRestrictScalarsConstantIso (ZMod.castHom h (ZMod d)) X).app
      (ModuleCat.of (ZMod d) (ULift.{u + 1} (ZMod d)))).symm ?_ ?_
  · simp [Sm, C]
  · simp [Sm, C, reduction]

/-- **In degree zero, `f ↦ π ≫ R f` is bijective**, from maps `ℤ/d_X ⟶ G` to maps
`ℤ/N_X ⟶ R G`. -/
theorem bijective_reduction_comp_map [NeZero N] (G : EtaleModules.{u, 0} (ZMod d) X) :
    Function.Bijective
      (fun f : unitSheaf (X := X) d ⟶ G => reduction X h ≫ (restrict X h).map f) := by
  refine ⟨fun f f' e => (restrict X h).map_injective ((cancel_epi (reduction X h)).1 e),
    fun g => ?_⟩
  have hg : (reductionShortComplex X h).f ≫ g = 0 := by
    show (d • 𝟙 _) ≫ g = 0
    have e := Preadditive.comp_nsmul g (𝟙 _) d
    rw [Category.comp_id] at e
    rw [Preadditive.nsmul_comp, Category.id_comp, ← e, nsmul_id_restrict, comp_zero]
  obtain ⟨k, hk⟩ := CokernelCofork.IsColimit.desc'
    (reductionShortComplex_exact X h).gIsCokernel g hg
  obtain ⟨f, rfl⟩ := (restrict X h).map_surjective k
  exact ⟨f, hk⟩

/-- `Ext^{n+1}_{ℤ/N}(ℤ/N_X, R I) = 0` for an injective sheaf `I` of `ℤ/d`-modules. -/
theorem subsingleton_ext_restrict_of_injective (I : EtaleModules.{u, 0} (ZMod d) X)
    [Injective I] (n : ℕ) :
    Subsingleton (Ext (unitSheaf (X := X) N) ((restrict X h).obj I) (n + 1)) := by
  have : Subsingleton ((extFunctorObj (Stacks.Cohomology.GlobalSections.constantModuleSheaf
      (ZMod d) X.smallEtaleTopology) (n + 1)).obj I) :=
    Ext.subsingleton_of_injective _ I n
  exact (extConstantRestrictScalarsIso (ZMod.castHom h (ZMod d)) X I
    (n + 1)).addCommGroupIsoToAddEquiv.symm.injective.subsingleton

/-- **The change of level on cohomology**, `Ext^n_{ℤ/d}(ℤ/d_X, G) ⟶ Ext^n_{ℤ/N}(ℤ/N_X, R G)`,
`y ↦ π ∘ R(y)`. -/
def extMap (G : EtaleModules.{u, 0} (ZMod d) X) (n : ℕ) :
    Ext (unitSheaf (X := X) d) G n →+ Ext (unitSheaf (X := X) N) ((restrict X h).obj G) n :=
  Stacks.Cohomology.ExtComparison.extMapAlong (restrict X h) (reduction X h) G n

/-- The change of level sends `y` to `π ∘ R(y)`. -/
theorem extMap_apply {G : EtaleModules.{u, 0} (ZMod d) X} {n : ℕ}
    (y : Ext (unitSheaf (X := X) d) G n) :
    extMap X h G n y = (Ext.mk₀ (reduction X h)).comp (y.mapExactFunctor (restrict X h))
      (zero_add n) :=
  rfl

/-- **Étale cohomology with `ℤ/d`-coefficients may be computed with `ℤ/N`-coefficients**: the
change of level `Ext^n_{ℤ/d}(ℤ/d_X, G) ⟶ Ext^n_{ℤ/N}(ℤ/N_X, R G)` is bijective. -/
theorem extMap_bijective [NeZero N] (G : EtaleModules.{u, 0} (ZMod d) X) (n : ℕ) :
    Function.Bijective (extMap X h G n) :=
  Stacks.Cohomology.ExtComparison.extMapAlong_bijective_of_subsingleton _ _
    (bijective_reduction_comp_map X h)
    (fun I _ n => subsingleton_ext_restrict_of_injective X h I n) G n

/-- The change of level is compatible with the Yoneda product:
`π ∘ R(y ∘ b) = (π ∘ R y) ∘ R b`. -/
theorem extMap_comp {G G' : EtaleModules.{u, 0} (ZMod d) X} {a b c : ℕ}
    (y : Ext (unitSheaf (X := X) d) G a) (z : Ext G G' b) (hc : a + b = c) :
    extMap X h G' c (y.comp z hc) =
      (extMap X h G a y).comp (z.mapExactFunctor (restrict X h)) hc := by
  rw [extMap_apply, extMap_apply, Ext.mapExactFunctor_comp]
  exact (Ext.comp_assoc _ _ _ (zero_add a) hc (by omega)).symm

section Inclusion

variable {e : ℕ} (hde : d * e = N)

include hde in
/-- `e ∣ N` when `N = d e`. -/
theorem dvd_of_mul_eq_left : e ∣ N := ⟨d, hde.symm.trans (mul_comm d e)⟩

/-- `ℤ/e ⟶ ℤ/N`, `x ↦ d x`, for `N = d e`, as a `ℤ/N`-linear map. -/
def inclusionLinearMap :
    (ModuleCat.restrictScalars.{u + 1} (ZMod.castHom (dvd_of_mul_eq_left hde) (ZMod e))).obj
        (ModuleCat.of (ZMod e) (ULift.{u + 1} (ZMod e))) ⟶
      ModuleCat.of (ZMod N) (ULift.{u + 1} (ZMod N)) :=
  ModuleCat.ofHom (X := (ModuleCat.restrictScalars.{u + 1}
      (ZMod.castHom (dvd_of_mul_eq_left hde) (ZMod e))).obj
      (ModuleCat.of (ZMod e) (ULift.{u + 1} (ZMod e))))
    ({ toFun := fun x => ULift.up (ZMod.lift e ⟨zmultiplesHom _ (d : ZMod N), by
          change (e : ℤ) • (d : ZMod N) = 0
          rw [natCast_zsmul, nsmul_eq_mul, ← Nat.cast_mul, mul_comm, hde, ZMod.natCast_self]⟩
          x.down)
       map_add' := fun x y => ULift.ext (map_add _ x.down y.down)
       map_smul' := fun a x => by
          obtain ⟨z, rfl⟩ := ZMod.intCast_surjective a
          rw [RingHom.id_apply, Int.cast_smul_eq_zsmul, Int.cast_smul_eq_zsmul]
          exact ULift.ext (map_zsmul _ z x.down) } :
      (ModuleCat.restrictScalars.{u + 1} (ZMod.castHom (dvd_of_mul_eq_left hde) (ZMod e))).obj
          (ModuleCat.of (ZMod e) (ULift.{u + 1} (ZMod e))) →ₗ[ZMod N] ULift.{u + 1} (ZMod N))

/-- `ℤ/e ⟶ ℤ/N` sends the class of `m` to the class of `d m`. -/
theorem inclusionLinearMap_apply_natCast (m : ℕ) :
    ((inclusionLinearMap.{u} hde).hom (ULift.up (m : ZMod e)) : ULift.{u + 1} (ZMod N)) =
      ULift.up ((d * m : ℕ) : ZMod N) := by
  rw [show (m : ZMod e) = ((m : ℤ) : ZMod e) from (Int.cast_natCast m).symm]
  refine ULift.ext ?_
  show ZMod.lift e ⟨zmultiplesHom (ZMod N) (d : ZMod N), _⟩ (((m : ℤ) : ZMod e)) = _
  rw [ZMod.lift_coe]
  show (m : ℤ) • (d : ZMod N) = _
  rw [natCast_zsmul, nsmul_eq_mul, Nat.cast_mul, mul_comm]

include hde in
/-- `d ≠ 0` when `N = d e ≠ 0`. -/
theorem neZero_left_of_mul_eq [NeZero N] : NeZero d :=
  ⟨fun h0 => NeZero.ne N (by rw [← hde, h0, zero_mul])⟩

include hde in
/-- `e ≠ 0` when `N = d e ≠ 0`. -/
theorem neZero_right_of_mul_eq [NeZero N] : NeZero e :=
  ⟨fun h0 => NeZero.ne N (by rw [← hde, h0, mul_zero])⟩

/-- Every element of `ℤ/e` is the class of its natural number representative. -/
private theorem eq_up_natCast_val [NeZero e] (x : ULift.{u + 1} (ZMod e)) :
    x = ULift.up ((x.down.val : ℕ) : ZMod e) :=
  ULift.ext (ZMod.natCast_zmod_val _).symm

/-- `ℤ/e ⟶ ℤ/N`, `x ↦ d x`, is injective. -/
theorem injective_inclusionLinearMap [NeZero N] :
    Function.Injective (inclusionLinearMap.{u} hde).hom := by
  have := neZero_left_of_mul_eq hde
  have := neZero_right_of_mul_eq hde
  rw [injective_iff_map_eq_zero]
  intro x hx
  have hx' := eq_up_natCast_val x
  rw [hx', inclusionLinearMap_apply_natCast] at hx
  have h1 := (ZMod.natCast_eq_zero_iff _ _).1 (congrArg ULift.down hx)
  rw [← hde] at h1
  have h2 : e ∣ x.down.val := Nat.dvd_of_mul_dvd_mul_left (Nat.pos_of_ne_zero (NeZero.ne d)) h1
  rw [hx']
  exact ULift.ext ((ZMod.natCast_eq_zero_iff _ _).2 h2)

/-- `ℤ/e --d--> ℤ/N --> ℤ/d` is exact. -/
theorem function_exact_inclusionLinearMap [NeZero N] :
    Function.Exact (inclusionLinearMap.{u} hde).hom
      (reductionLinearMap.{u} (Dvd.intro e hde)).hom := by
  intro y
  rw [reductionLinearMap_apply]
  constructor
  · intro hy
    obtain ⟨m, hm⟩ :=
      exists_val_eq_mul_of_castHom_eq_zero (Dvd.intro e hde) (congrArg ULift.down hy)
    refine ⟨ULift.up (m : ZMod e), ?_⟩
    rw [inclusionLinearMap_apply_natCast, ← hm]
    exact ULift.ext (ZMod.natCast_zmod_val _)
  · rintro ⟨x, rfl⟩
    have := neZero_right_of_mul_eq hde
    have hx' := eq_up_natCast_val x
    rw [hx', inclusionLinearMap_apply_natCast]
    refine ULift.ext ?_
    show ZMod.castHom (Dvd.intro e hde) (ZMod d) ((d * x.down.val : ℕ) : ZMod N) = 0
    rw [map_natCast, Nat.cast_mul, ZMod.natCast_self, zero_mul]

/-- `ℤ/N ↠ ℤ/e --d--> ℤ/N` is multiplication by `d`. -/
theorem reductionLinearMap_comp_inclusionLinearMap [NeZero N] :
    reductionLinearMap.{u} (dvd_of_mul_eq_left hde) ≫ inclusionLinearMap.{u} hde =
      d • 𝟙 (ModuleCat.of (ZMod N) (ULift.{u + 1} (ZMod N))) := by
  have := neZero_right_of_mul_eq hde
  ext y
  show ((inclusionLinearMap.{u} hde).hom (ULift.up (ZMod.castHom (dvd_of_mul_eq_left hde)
    (ZMod e) y.down))).down = d • y.down
  rw [ZMod.castHom_apply, ← ZMod.natCast_val, inclusionLinearMap_apply_natCast, nsmul_eq_mul,
    Nat.cast_mul, ZMod.natCast_zmod_val]

/-- **Multiplication by `d`, `R(ℤ/e_X) ⟶ ℤ/N_X`**, for `N = d e`: the constant sheaf on
`ℤ/e ⟶ ℤ/N`, `x ↦ d x`. -/
def inclusion : (restrict X (dvd_of_mul_eq_left hde)).obj (unitSheaf e) ⟶ unitSheaf (X := X) N :=
  ((etaleModuleRestrictScalarsConstantIso (ZMod.castHom (dvd_of_mul_eq_left hde) (ZMod e)) X).app
      (ModuleCat.of (ZMod e) (ULift.{u + 1} (ZMod e)))).hom ≫
    (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ZMod N))).map
      (inclusionLinearMap hde)

/-- **Multiplication by `d` on `ℤ/N_X` factors through the reduction to `ℤ/e_X`**. -/
theorem reduction_comp_inclusion [NeZero N] :
    reduction X (dvd_of_mul_eq_left hde) ≫ inclusion X hde = d • 𝟙 (unitSheaf (X := X) N) := by
  rw [reduction, inclusion, Category.assoc, Iso.inv_hom_id_assoc, ← Functor.map_comp,
    reductionLinearMap_comp_inclusionLinearMap, Functor.map_nsmul, CategoryTheory.Functor.map_id]

/-- The short complex `R(ℤ/e_X) --d--> ℤ/N_X --π--> R(ℤ/d_X)`. -/
abbrev inclusionShortComplex [NeZero N] : ShortComplex (EtaleModules.{u, 0} (ZMod N) X) :=
  ShortComplex.mk (inclusion X hde) (reduction X (Dvd.intro e hde)) (by
    rw [inclusion, reduction, Category.assoc, ← Functor.map_comp_assoc]
    have : inclusionLinearMap.{u} hde ≫ reductionLinearMap.{u} (Dvd.intro e hde) = 0 := by
      ext x
      exact (function_exact_inclusionLinearMap hde _).2 ⟨x, rfl⟩
    rw [this, Functor.map_zero, zero_comp, comp_zero])

/-- **`0 → R(ℤ/e_X) --d--> ℤ/N_X --π--> R(ℤ/d_X) → 0` is exact**, for `N = d e`. -/
theorem inclusionShortComplex_shortExact [NeZero N] :
    (inclusionShortComplex X hde).ShortExact := by
  let C := constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ZMod N))
  let Sm : ShortComplex (ModuleCat.{u + 1} (ZMod N)) :=
    ShortComplex.mk (inclusionLinearMap hde) (reductionLinearMap (Dvd.intro e hde)) (by
        ext x
        exact (function_exact_inclusionLinearMap hde _).2 ⟨x, rfl⟩)
  have hSm : Sm.ShortExact := ModuleCat.shortComplex_shortExact _
    (function_exact_inclusionLinearMap hde) (injective_inclusionLinearMap hde)
    (surjective_reductionLinearMap _)
  refine ShortComplex.shortExact_of_iso ?_ (hSm.map_of_exact C)
  refine ShortComplex.isoMk
    ((etaleModuleRestrictScalarsConstantIso (ZMod.castHom (dvd_of_mul_eq_left hde) (ZMod e)) X).app
      (ModuleCat.of (ZMod e) (ULift.{u + 1} (ZMod e)))).symm (Iso.refl _)
    ((etaleModuleRestrictScalarsConstantIso (ZMod.castHom (Dvd.intro e hde) (ZMod d)) X).app
      (ModuleCat.of (ZMod d) (ULift.{u + 1} (ZMod d)))).symm ?_ ?_
  · simp [Sm, C, inclusion]
  · simp [Sm, C, reduction]

end Inclusion

end LevelChange

end Stacks.EtaleCohomology

end
