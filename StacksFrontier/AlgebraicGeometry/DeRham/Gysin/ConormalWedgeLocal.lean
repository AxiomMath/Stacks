module

public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.ChartDataComparison
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.LocalDescent

/-!
# Local data for the wedge pairing at the generality of Tag 0G86

The wedge pairing of [Stacks, Tag 0G88] pairs a **local** section `ω` of `Ω^p_{X/S}` over an open
`V` with a local section of `i_*ℋ^c_Z(Ω^c_{X/S})` over `V`.  Multiplication by `ω` is a morphism
of sheaves only on `V`, so the pairing is built from the restriction of the graded multiplication
to `V` and is transported to the ambient scheme by the derived excision.  This file contains the
following formal constructions, none of which mentions local cohomology:

* the restriction of a bilinear map of sheaves of modules along an open immersion;
* a section over `V` read as a **global** section of the restriction to `V`, which is what
  `Stacks.Cohomology.rightMulHom` consumes;
* the unit `M ⟶ j_*j^*M` of `AlgebraicGeometry.Scheme.Modules.restrictAdjunction`, which becomes
  invertible after restriction to any open contained in `V`, together with the comparison of the
  units of two nested opens.

## Main definitions

* `Stacks.Gysin.restrictBilinear`: a bilinear map of sheaves of modules, restricted along an open
  immersion.
* `Stacks.Gysin.localSections`: a section of `M` over `V`, read as a global section of `M|_V`.
* `Stacks.Gysin.openUnit`: the unit `M ⟶ (V.ι)_*(M|_V)` of the restriction adjunction.
* `Stacks.Gysin.openUnitTransport`: for `V' ≤ V`, the comparison `(V.ι)_*(M|_V) ⟶ (V'.ι)_*(M|_V')`
  through which the unit of `V'` factors the unit of `V`.

## Main results

* `Stacks.Gysin.isIso_restrictFunctor_map_openUnit`: **the unit of `V` becomes invertible after
  restriction to any open `V' ≤ V`.**
* `Stacks.Gysin.openUnit_comp_openUnitTransport`: the unit of `V` followed by
  `openUnitTransport` is the unit of `V'`.

## References

* [Stacks Project, Tag 0G88](https://stacks.math.columbia.edu/tag/0G88)
* [Stacks Project, Tag 0G86](https://stacks.math.columbia.edu/tag/0G86)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
open Stacks.AlgebraicGeometry.ModuleLimits

universe u

namespace Stacks.Gysin

variable {X X' : Scheme.{u}}

/-! ### Restriction of a bilinear map along an open immersion -/

/-- **A bilinear map of sheaves of modules, restricted along an open immersion.**  The sections of
a restriction over an open `U` are the sections of the original over the image of `U`, so the
restricted bilinear map is the original one read at that image. -/
def restrictBilinear (g : X' ⟶ X) [IsOpenImmersion g] {M N P : X.Modules}
    (β : SheafOfModules.BilinearMap M N P) :
    SheafOfModules.BilinearMap ((Scheme.Modules.restrictFunctor g).obj M)
      ((Scheme.Modules.restrictFunctor g).obj N)
      ((Scheme.Modules.restrictFunctor g).obj P) where
  app U := β.app (op (g ''ᵁ U.unop))
  map_smul_left _ _ x y := β.map_smul_left _ _ x y
  map_smul_right _ _ x y := β.map_smul_right _ _ x y
  naturality h x y := β.naturality (g.opensFunctor.map h.unop).op x y

/-- The component of `restrictBilinear g β` at an open `U` is the component of `β` at `g ''ᵁ U`. -/
@[simp]
theorem restrictBilinear_app (g : X' ⟶ X) [IsOpenImmersion g] {M N P : X.Modules}
    (β : SheafOfModules.BilinearMap M N P) (U : X'.Opens)
    (x : Γ((Scheme.Modules.restrictFunctor g).obj M, U))
    (y : Γ((Scheme.Modules.restrictFunctor g).obj N, U)) :
    (restrictBilinear g β).app (op U) x y = β.app (op (g ''ᵁ U)) x y :=
  rfl

/-! ### A local section as a global section of the restriction -/

/-- **A section of `M` over `V`, read as a global section of `M|_V`.**  The sections of `M|_V` over
an open `U` of `V.toScheme` are the sections of `M` over `V.ι ''ᵁ U`, an open contained in `V`,
and the component over `U` is the restriction of the given section there. -/
def localSections (V : X.Opens) (M : X.Modules) (s : Γ(M, V)) :
    ((Scheme.Modules.restrictFunctor V.ι).obj M).val.sections :=
  PresheafOfModules.sectionsMk
    (fun U => M.presheaf.map (homOfLE (Scheme.Opens.ι_image_le V U.unop)).op s)
    (fun {U W} h => by
      change M.presheaf.map _ (M.presheaf.map _ s) = M.presheaf.map _ s
      rw [← ConcreteCategory.comp_apply, ← M.presheaf.map_comp]
      exact congrArg (fun u : op V ⟶ op (V.ι ''ᵁ W.unop) => M.presheaf.map u s)
        (Subsingleton.elim _ _))

/-- The component of `localSections V M s` at an open `U` of `V` is the restriction of `s` to
`V.ι ''ᵁ U`. -/
theorem localSections_eval (V : X.Opens) (M : X.Modules) (s : Γ(M, V)) (U : V.toScheme.Opens) :
    (localSections V M s).eval (op U) =
      M.presheaf.map (homOfLE (Scheme.Opens.ι_image_le V U)).op s :=
  rfl

/-! ### The unit of the restriction adjunction -/

/-- **The unit `M ⟶ (V.ι)_*(M|_V)` of the restriction adjunction**, whose action on the sections
over an open `U` is the restriction map to `V.ι ''ᵁ (V.ι ⁻¹ᵁ U)`, that is to `U ⊓ V`.  Wedging a
section of `Ω^c_{X/S}` with a section of `Ω^p_{X/S}` defined only on `V` is a morphism of sheaves
on the whole of `X` with this sheaf as its target, which is what makes the pairing's
compatibility with restriction formal. -/
def openUnit (V : X.Opens) (M : X.Modules) :
    M ⟶ (Scheme.Modules.pushforward V.ι).obj ((Scheme.Modules.restrictFunctor V.ι).obj M) :=
  (Scheme.Modules.restrictAdjunction V.ι).unit.app M

/-- The component of `openUnit V M` at an open `U` is the restriction map of `M` from `U` to
`V.ι ''ᵁ (V.ι ⁻¹ᵁ U)`. -/
theorem openUnit_app (V : X.Opens) (M : X.Modules) (U : X.Opens) :
    (openUnit V M).app U = M.presheaf.map (homOfLE (V.ι.image_preimage_le U)).op :=
  rfl

/-- The left triangle identity for the restriction adjunction, at the unit `openUnit V M`. -/
private theorem restrictFunctor_map_openUnit_comp_counit (V : X.Opens) (M : X.Modules) :
    (Scheme.Modules.restrictFunctor V.ι).map (openUnit V M) ≫
      (Scheme.Modules.restrictAdjunction V.ι).counit.app
        ((Scheme.Modules.restrictFunctor V.ι).obj M) = 𝟙 _ :=
  (Scheme.Modules.restrictAdjunction V.ι).left_triangle_components M

/-- The unit of `V` becomes invertible after restriction to `V` itself. -/
theorem isIso_restrictFunctor_map_openUnit_self (V : X.Opens) (M : X.Modules) :
    IsIso ((Scheme.Modules.restrictFunctor V.ι).map (openUnit V M)) := by
  have : IsIso ((Scheme.Modules.restrictFunctor V.ι).map (openUnit V M) ≫
      (Scheme.Modules.restrictAdjunction V.ι).counit.app
        ((Scheme.Modules.restrictFunctor V.ι).obj M)) := by
    rw [restrictFunctor_map_openUnit_comp_counit]; infer_instance
  exact IsIso.of_isIso_comp_right _
    ((Scheme.Modules.restrictAdjunction V.ι).counit.app
      ((Scheme.Modules.restrictFunctor V.ι).obj M))

/-- **The unit absorbs a morphism of restrictions.**  Restricting to `V` the composite of the
unit of `V` with the direct image of a morphism `ψ` of the restrictions gives `ψ` followed by the
restricted unit.  This is what makes "multiply by a section defined only on `V`" a morphism of
sheaves on the whole of `X` whose restriction to `V` is the multiplication itself. -/
theorem restrictFunctor_map_openUnit_comp (V : X.Opens) {M N : X.Modules}
    (ψ : (Scheme.Modules.restrictFunctor V.ι).obj M ⟶
      (Scheme.Modules.restrictFunctor V.ι).obj N) :
    (Scheme.Modules.restrictFunctor V.ι).map
        (openUnit V M ≫ (Scheme.Modules.pushforward V.ι).map ψ) =
      ψ ≫ (Scheme.Modules.restrictFunctor V.ι).map (openUnit V N) := by
  have hnat : (Scheme.Modules.restrictFunctor V.ι).map
        ((Scheme.Modules.pushforward V.ι).map ψ) ≫
      (Scheme.Modules.restrictAdjunction V.ι).counit.app
        ((Scheme.Modules.restrictFunctor V.ι).obj N) =
      (Scheme.Modules.restrictAdjunction V.ι).counit.app
        ((Scheme.Modules.restrictFunctor V.ι).obj M) ≫ ψ :=
    (Scheme.Modules.restrictAdjunction V.ι).counit.naturality ψ
  have : Mono ((Scheme.Modules.restrictAdjunction V.ι).counit.app
      ((Scheme.Modules.restrictFunctor V.ι).obj N)) :=
    @IsIso.mono_of_iso _ _ _ _ _ (NatIso.isIso_app_of_isIso _ _)
  refine (cancel_mono ((Scheme.Modules.restrictAdjunction V.ι).counit.app
    ((Scheme.Modules.restrictFunctor V.ι).obj N))).mp ?_
  rw [CategoryTheory.Functor.map_comp, Category.assoc, hnat, ← Category.assoc,
    restrictFunctor_map_openUnit_comp_counit V M, Category.id_comp, Category.assoc,
    restrictFunctor_map_openUnit_comp_counit V N, Category.comp_id]

/-- Restriction to a smaller open factors through restriction to the larger one. -/
def restrictFunctorLeIso {V' V : X.Opens} (e : V' ≤ V) :
    Scheme.Modules.restrictFunctor V'.ι ≅
      Scheme.Modules.restrictFunctor V.ι ⋙ Scheme.Modules.restrictFunctor (X.homOfLE e) :=
  (Scheme.Modules.restrictFunctorCongr (X.homOfLE_ι e)).symm ≪≫
    Scheme.Modules.restrictFunctorComp (X.homOfLE e) V.ι

/-- **The unit of `V` becomes invertible after restriction to any open `V' ≤ V`.** -/
theorem isIso_restrictFunctor_map_openUnit {V' V : X.Opens} (e : V' ≤ V) (M : X.Modules) :
    IsIso ((Scheme.Modules.restrictFunctor V'.ι).map (openUnit V M)) := by
  refine (NatIso.isIso_map_iff (restrictFunctorLeIso e) (openUnit V M)).mpr ?_
  have := isIso_restrictFunctor_map_openUnit_self V M
  exact inferInstanceAs (IsIso ((Scheme.Modules.restrictFunctor (X.homOfLE e)).map
    ((Scheme.Modules.restrictFunctor V.ι).map (openUnit V M))))

/-- **The comparison of the units of two nested opens.**  For `V' ≤ V` this is the transpose,
under the restriction adjunction of `V'`, of the inverse of the restriction to `V'` of the unit of
`V`; it is the map that restricts a section over `U ⊓ V` to `U ⊓ V'`. -/
def openUnitTransport {V' V : X.Opens} (e : V' ≤ V) (M : X.Modules) :
    (Scheme.Modules.pushforward V.ι).obj ((Scheme.Modules.restrictFunctor V.ι).obj M) ⟶
      (Scheme.Modules.pushforward V'.ι).obj
        ((Scheme.Modules.restrictFunctor V'.ι).obj M) :=
  haveI := isIso_restrictFunctor_map_openUnit e M
  (Scheme.Modules.restrictAdjunction V'.ι).homEquiv _ _
    (inv ((Scheme.Modules.restrictFunctor V'.ι).map (openUnit V M)))

/-- **The unit of `V'` factors the unit of `V`**: for `V' ≤ V`,
`openUnit V M ≫ openUnitTransport e M = openUnit V' M`. -/
theorem openUnit_comp_openUnitTransport {V' V : X.Opens} (e : V' ≤ V) (M : X.Modules) :
    openUnit V M ≫ openUnitTransport e M = openUnit V' M := by
  have := isIso_restrictFunctor_map_openUnit e M
  refine Eq.trans ((Scheme.Modules.restrictAdjunction V'.ι).homEquiv_naturality_left
    (openUnit V M) (inv ((Scheme.Modules.restrictFunctor V'.ι).map (openUnit V M)))).symm ?_
  refine Eq.trans (congrArg ((Scheme.Modules.restrictAdjunction V'.ι).homEquiv M _)
    (IsIso.hom_inv_id _)) ?_
  rw [Adjunction.homEquiv_unit, CategoryTheory.Functor.map_id]
  exact Category.comp_id _

end Stacks.Gysin

end
