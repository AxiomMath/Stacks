module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedChaoticRealization
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedConstantTriangulated
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedRightDerivedExtension
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.QuasicoherentChaoticSite

/-!
# Global sections on a chaotic site with a constant sheaf of rings, and their right derived functor

Let `C` be a small category with the chaotic topology and let `O` be the constant sheaf of rings
with value a commutative ring `R`. Since `O(U) = R` for every `U` and the restriction maps of `O`
are the identity, the sections of a sheaf of `O`-modules over each object are `R`-modules and its
restriction maps are `R`-linear: a sheaf of `O`-modules *is* an `R`-linear presheaf
`Cᵒᵖ ⥤ ModuleCat R`, and the global sections are the limit of that presheaf.

For a sheaf `ℬ` of differential graded `O`-algebras, applying the global sections degreewise to
the underlying complex of a right differential graded `ℬ`-module gives a complex of `R`-modules;
homotopic homomorphisms give homotopic maps, so this descends to the homotopy category, and its
right derived extension along the localization is the derived global sections functor
`RΓ : D(ℬ, d) ⥤ D(R)`.

## Main definitions

* `Stacks.ChaoticSite.sectionsFunctor`: a sheaf of `O`-modules as a presheaf of `R`-modules, and
  `Stacks.ChaoticSite.sectionsEquivalence` the equivalence it is, with inverse
  `Stacks.PresheafOfModules.ofFunctorSheaf`.
* `Stacks.ChaoticSite.globalSections`: the global sections functor
  `Mod(O) ⥤ ModuleCat R`, defined as `sectionsFunctor ⋙ lim`.
* `Stacks.ChaoticSite.dgGlobalSections`: the functor `M ↦ Γ(M)` from right differential graded
  `ℬ`-modules to complexes of `R`-modules, and `Stacks.ChaoticSite.homotopyGlobalSections` its
  descent to the homotopy categories.
* `Stacks.ChaoticSite.derivedGlobalSections`: **the derived global sections functor**
  `D(ℬ, d) ⥤ D(R)`, the rigidified right derived extension of `Qh ∘ K(Γ)`, with
  `Stacks.ChaoticSite.derivedGlobalSectionsUnit` its comparison map.

## Main results

* `Stacks.ChaoticSite.isRightDerivedFunctor_derivedGlobalSections`: it is the right derived
  functor of `Qh ∘ K(Γ)` along `K(Mod(ℬ, d)) ⥤ D(ℬ, d)`.
* `Stacks.ChaoticSite.derivedGlobalSections_obj_of_isDGInjective`: at a graded injective
  K-injective module `I` its value is the class of the complex `Γ(I)`, on the nose.

## Implementation notes

The sections functor is the identity on underlying types: `M.val.obj U` already carries an
`R`-module structure, the one over `O(U) = R`, recorded as `Stacks.ChaoticSite.sectionsModule`,
and it is the one used throughout. The two composites with `ofFunctorSheaf` are therefore the
identity componentwise, which is what makes the equivalence a matter of `rfl`.

The right derived extension of this library is stated over a ringed site; the chaotic site with
the constant sheaf of commutative rings is `Stacks.ChaoticSite.constRingedSite`, whose sheaf of
rings is `constRingSheaf R` on the nose, and it is passed explicitly.

## References

* [Stacks Project, Tag 0FTN](https://stacks.math.columbia.edu/tag/0FTN)
* [Stacks Project, Remark 24.35.5 (Tag 0H1E)](https://stacks.math.columbia.edu/tag/0H1E)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite Limits Stacks.PresheafOfModules

universe u

namespace Stacks.ChaoticSite

variable {C : Type u} [SmallCategory C] (R : Type u) [CommRing R]

/-! ### Sections as a presheaf of `R`-modules -/

/-- The sections of a sheaf of modules over the constant sheaf of rings with value `R` are
`R`-modules. -/
instance sectionsModule (M : _root_.SheafOfModules.{u} (constRingSheaf (C := C) R)) (U : Cᵒᵖ) :
    Module R (M.val.obj U) :=
  (M.val.obj U).isModule

/-- A sheaf of modules over the constant sheaf of rings with value `R`, read as a presheaf of
`R`-modules: the sections over `U` with their restriction maps, which are `R`-linear. -/
def sectionsFunctorObj (M : _root_.SheafOfModules.{u} (constRingSheaf (C := C) R)) :
    Cᵒᵖ ⥤ ModuleCat.{u} R where
  obj U := ModuleCat.of R (M.val.obj U)
  map {U V} f := ModuleCat.ofHom
    { toFun := fun x => M.val.map f x
      map_add' := fun x y => map_add _ x y
      map_smul' := fun r x => M.val.map_smul f r x }
  map_id U := by
    ext x
    exact congrArg (fun g => g x)
      (congrArg (fun φ => ConcreteCategory.hom φ) (M.val.presheaf.map_id U))
  map_comp f g := by
    ext x
    exact M.val.map_comp_apply f g x

/-- The restriction maps of the presheaf of sections are those of the sheaf. -/
theorem sectionsFunctorObj_map_apply (M : _root_.SheafOfModules.{u} (constRingSheaf (C := C) R))
    {U V : Cᵒᵖ} (f : U ⟶ V) (x : M.val.obj U) :
    ((sectionsFunctorObj R M).map f).hom x = M.val.map f x := rfl

/-- **The sections functor**: a sheaf of modules over the constant sheaf of rings with value `R`
as a presheaf of `R`-modules, functorially. -/
def sectionsFunctor :
    _root_.SheafOfModules.{u} (constRingSheaf (C := C) R) ⥤ (Cᵒᵖ ⥤ ModuleCat.{u} R) where
  obj M := sectionsFunctorObj R M
  map {M N} α :=
    { app U := ModuleCat.ofHom
        { toFun := fun x => α.val.app U x
          map_add' := fun x y => map_add _ x y
          map_smul' := fun r x => (α.val.app U).hom.map_smul r x }
      naturality U V f := by
        ext x
        exact PresheafOfModules.naturality_apply α.val f x }

/-- The sections functor is additive. -/
instance : (sectionsFunctor (C := C) R).Additive where
  map_add := by
    intros
    ext
    rfl

/-- The identification of a sheaf of modules with the sheaf attached to its presheaf of
sections; it is the identity on sections. -/
def sectionsUnitIso (M : _root_.SheafOfModules.{u} (constRingSheaf (C := C) R)) :
    M ≅ (ofFunctorSheaf R).obj ((sectionsFunctor R).obj M) :=
  (_root_.SheafOfModules.fullyFaithfulForget _).preimageIso
    (PresheafOfModules.isoMk (fun U => Iso.refl _) (fun U V f => by ext x; rfl))

/-- The identification of a presheaf of `R`-modules with the presheaf of sections of the sheaf
attached to it; it is the identity on sections. -/
def sectionsCounitIso (F : Cᵒᵖ ⥤ ModuleCat.{u} R) :
    (sectionsFunctor R).obj ((ofFunctorSheaf R).obj F) ≅ F :=
  NatIso.ofComponents (fun U => Iso.refl _) (fun f => by ext x; rfl)

/-- **Sheaves of modules over the constant sheaf of rings on the chaotic site are presheaves of
`R`-modules**: the sections functor is an equivalence, with inverse
`Stacks.PresheafOfModules.ofFunctorSheaf`. -/
def sectionsEquivalence :
    _root_.SheafOfModules.{u} (constRingSheaf (C := C) R) ≌ (Cᵒᵖ ⥤ ModuleCat.{u} R) where
  functor := sectionsFunctor R
  inverse := ofFunctorSheaf R
  unitIso := NatIso.ofComponents (sectionsUnitIso R) (fun f => by ext U x; rfl)
  counitIso := NatIso.ofComponents (sectionsCounitIso R) (fun f => by ext U x; rfl)
  functor_unitIso_comp M := by ext U x; rfl

/-- The sections functor is an equivalence. -/
instance : (sectionsFunctor (C := C) R).IsEquivalence :=
  (sectionsEquivalence (C := C) R).isEquivalence_functor

/-! ### Global sections -/

/-- The limit functor on presheaves of `R`-modules is additive. -/
theorem lim_map_add {F G : Cᵒᵖ ⥤ ModuleCat.{u} R} (f g : F ⟶ G) :
    lim.map (f + g) = lim.map f + lim.map g :=
  limit.hom_ext fun j => by simp [Preadditive.add_comp, Preadditive.comp_add]

/-- **The global sections functor** on sheaves of modules over the constant sheaf of rings with
value `R`: the limit of the presheaf of sections, an `R`-module. -/
def globalSections :
    _root_.SheafOfModules.{u} (constRingSheaf (C := C) R) ⥤ ModuleCat.{u} R :=
  sectionsFunctor R ⋙ lim

/-- The global sections functor is additive. -/
instance : (globalSections (C := C) R).Additive where
  map_add {_ _ f g} := by
    change lim.map ((sectionsFunctor R).map (f + g)) = _
    rw [Functor.map_add, lim_map_add]
    rfl

/-- The global sections functor preserves all limits, being an equivalence followed by `lim`. -/
instance : PreservesLimits (globalSections (C := C) R) := by
  unfold globalSections; infer_instance

/-- The global sections functor is left exact. -/
instance : PreservesFiniteLimits (globalSections (C := C) R) := by
  unfold globalSections; infer_instance

/-! ### The derived global sections of a sheaf of differential graded algebras -/

section Derived

open _root_.SheafOfModules _root_.SheafOfModules.DifferentialGradedModule

variable (ℬ : _root_.SheafOfModules.DifferentialGradedAlgebra.{u, u} (constRingSheaf (C := C) R))

/-- The global sections of a right differential graded `ℬ`-module: the global sections functor
applied degreewise to its underlying complex, `M ↦ Γ(M)`. -/
def dgGlobalSections :
    DifferentialGradedModule.{u, u, u} ℬ ⥤ CochainComplex (ModuleCat.{u} R) ℤ where
  obj M := ((globalSections R).mapHomologicalComplex _).obj M.complex
  map f := ((globalSections R).mapHomologicalComplex _).map f.toHomologicalComplex
  map_id M := ((globalSections R).mapHomologicalComplex _).map_id M.complex
  map_comp f g := ((globalSections R).mapHomologicalComplex _).map_comp
    f.toHomologicalComplex g.toHomologicalComplex

/-- The global sections on the homotopy category: homotopic homomorphisms of right differential
graded `ℬ`-modules have homotopic global sections. -/
def homotopyGlobalSections :
    HomotopyCategory.{u, u, u} ℬ ⥤ _root_.HomotopyCategory (ModuleCat.{u} R) (ComplexShape.up ℤ) :=
  CategoryTheory.Quotient.lift _ (dgGlobalSections R ℬ ⋙ _root_.HomotopyCategory.quotient _ _)
    fun _ _ _ _ ⟨h⟩ => _root_.HomotopyCategory.eq_of_homotopy _ _
      ((globalSections R).mapHomotopy h.toComplexHomotopy)

/-- The global sections on the homotopy category lift the global sections of modules. -/
theorem quotient_comp_homotopyGlobalSections :
    DifferentialGradedModule.HomotopyCategory.quotient ℬ ⋙ homotopyGlobalSections R ℬ =
      dgGlobalSections R ℬ ⋙ _root_.HomotopyCategory.quotient _ _ :=
  CategoryTheory.Quotient.lift_spec _ _ _

attribute [local instance] HasDerivedCategory.standard

/-- The functor `K(Mod(ℬ, d)) ⥤ D(R)` whose right derived functor is the derived global sections:
the global sections on the homotopy category followed by the localization. -/
def derivedGlobalSectionsAux :
    HomotopyCategory.{u, u, u} ℬ ⥤ DerivedCategory (ModuleCat.{u} R) :=
  homotopyGlobalSections R ℬ ⋙ DerivedCategory.Qh

attribute [local instance] Stacks.SheafOfModules.botWEqualsLocallyBijective

/-- **The derived global sections functor** `RΓ : D(ℬ, d) ⥤ D(R)`: the right derived extension of
the global sections, rigidified so that its value at a graded injective K-injective module `I` is
the class of `Γ(I)` on the nose. -/
def derivedGlobalSections :
    derivedCategory.{u, u, u} ℬ ⥤ DerivedCategory (ModuleCat.{u} R) :=
  rigidRightDerivedExtension.{u, u, u} (X := constRingedSite C R) (A := ℬ)
    (derivedGlobalSectionsAux R ℬ)

/-- The comparison map `Qh ∘ K(Γ) ⟶ RΓ ∘ Q` of the derived global sections. -/
def derivedGlobalSectionsUnit :
    derivedGlobalSectionsAux R ℬ ⟶ toDerivedCategory.{u, u, u} ℬ ⋙ derivedGlobalSections R ℬ :=
  rigidRightDerivedExtensionUnit.{u, u, u} (X := constRingedSite C R) (A := ℬ)
    (derivedGlobalSectionsAux R ℬ)

/-- The derived global sections functor is the right derived functor of the global sections. -/
theorem isRightDerivedFunctor_derivedGlobalSections :
    (derivedGlobalSections R ℬ).IsRightDerivedFunctor (derivedGlobalSectionsUnit R ℬ)
      (quasiIsomorphisms.{u, u, u} ℬ) :=
  isRightDerivedFunctor_rigidRightDerivedExtension.{u, u, u} (X := constRingedSite C R) (A := ℬ)
    (derivedGlobalSectionsAux R ℬ)

/-- The comparison map of the derived global sections is invertible at a graded injective
K-injective module. -/
theorem isIso_derivedGlobalSectionsUnit_app {I : DifferentialGradedModule.{u, u, u} ℬ}
    (hI : IsDGInjective I) :
    IsIso ((derivedGlobalSectionsUnit R ℬ).app
      ((DifferentialGradedModule.HomotopyCategory.quotient ℬ).obj I)) :=
  isIso_rigidRightDerivedExtensionUnit_app.{u, u, u} (X := constRingedSite C R) (A := ℬ)
    (derivedGlobalSectionsAux R ℬ) hI

/-- At a graded injective K-injective module `I` the derived global sections are the class of the
complex of global sections `Γ(I)`. -/
theorem derivedGlobalSections_obj_of_isDGInjective {I : DifferentialGradedModule.{u, u, u} ℬ}
    (hI : IsDGInjective I) :
    (derivedGlobalSections R ℬ).obj ((toDerivedCategory.{u, u, u} ℬ).obj
        ((DifferentialGradedModule.HomotopyCategory.quotient ℬ).obj I)) =
      DerivedCategory.Qh.obj ((_root_.HomotopyCategory.quotient _ _).obj
        ((dgGlobalSections R ℬ).obj I)) :=
  rigidRightDerivedExtension_obj_of_isDGInjective.{u, u, u} (X := constRingedSite C R) (A := ℬ)
    (derivedGlobalSectionsAux R ℬ) hI

end Derived

end Stacks.ChaoticSite
