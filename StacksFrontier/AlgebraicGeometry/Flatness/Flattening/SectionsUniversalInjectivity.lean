module

public import Mathlib
public import StacksFrontier.AlgebraicGeometry.AssociatedPointPrime.Basic
public import StacksFrontier.AlgebraicGeometry.AssociatedPointsMono.Basic
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.Depth
public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.MonoAfterBaseChange
public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.StrictTransformFlatnessShortExact
public import StacksFrontier.AlgebraicGeometry.Morphisms.FlatMorphisms.EtaleSquare
public import StacksFrontier.RingTheory.Flat.UniversallyExact

/-!
# Universal injectivity of a map of sections, and what it gives

The induction step of [Stacks, Tag 0815] constructs a map `α : 𝒪_X^{⊕ r} ⟶ ℱ` on an affine chart
and needs three things of it: that it is a monomorphism, that it stays one after every base
change of the base (so that [Stacks, Tag 080W] applies to its cokernel sequence), and that the
cokernel is still flat over the open `U` over which `ℱ` was. All three come from one algebraic
property of the map of global sections of `α`: **universal injectivity** over the ring of the
base, in the sense of [Stacks, Tag 058K].

This file is the dictionary between that property of the sections and those three conclusions.

## Main results

* `AlgebraicGeometry.mono_of_universallyInjective_sections_of_isAffine`: on an affine scheme over
  an affine base, universal injectivity of the sections makes `α` a monomorphism.
* `AlgebraicGeometry.shortExact_map_pullback_of_universallyInjective_of_isAffine`: and makes its
  cokernel sequence stay short exact after every base change of the base, which is the hypothesis
  of [Stacks, Tag 080W].
* `AlgebraicGeometry.isFlatOver_restrict_cokernel_of_universallyInjective_sections_of_isAffine`:
  and makes the cokernel flat over the open of the base over which the target is flat. This is
  the flatness half of [Stacks, Tag 058P].
* `AlgebraicGeometry.universallyInjective_moduleSpecΓ_of_sections` and
  `AlgebraicGeometry.universallyInjective_sections_of_moduleSpecΓ`: the two spellings of the
  chart hypothesis — the sections over an affine open `U ⊆ X`, and the global sections of the
  pullback to `Spec Γ(X, U)` — agree, so one hypothesis feeds all three conclusions.

## Implementation notes

The passage from sections to stalks is localization: on an affine open `U` the stalk of a
quasi-coherent module at `x ∈ U` is the localization of `Γ(M, U)` at the prime of `x`
(`Stacks.AlgebraicGeometry.AssociatedPointPrime.isLocalizedModule_germₗ`), and universal
injectivity localizes by [Stacks, Tag 05CL]
(`Stacks.UniversalInjectivity.LocalizationCriteria.universally_injective_check_stalks`). That is
`AlgebraicGeometry.universallyInjective_schemeStalk_of_sections`.

Flatness of the cokernel is then pointwise: the stalk sequence `ℱ_x → 𝒢_x → (coker α)_x → 0` is
exact because the stalk functor is exact ([Stacks, Tag 01AG]), its first map is universally
injective, and a universally exact sequence with flat middle term has flat quotient
([Stacks, Tag 058P], `Stacks.UniversallyExact.flat_of_middle_flat`).

Flatness over the base is a condition over the local ring of the base, whereas the sections
hypothesis is over the ring of an affine open of the base; the two agree because the local ring
is a localization of that ring, which is
`AlgebraicGeometry.isFlatOverAt_iff_flat_sectionsStalk`.

## References

* [Stacks Project, Tag 0815](https://stacks.math.columbia.edu/tag/0815)
* [Stacks Project, Tag 058K](https://stacks.math.columbia.edu/tag/058K)
* [Stacks Project, Tag 058P](https://stacks.math.columbia.edu/tag/058P)
* [Stacks Project, Tag 05CL](https://stacks.math.columbia.edu/tag/05CL)
* [Stacks Project, Tag 080W](https://stacks.math.columbia.edu/tag/080W)
* [Stacks Project, Tag 01AG](https://stacks.math.columbia.edu/tag/01AG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.AlgebraicGeometry.AssociatedPointsMono
open Stacks.AlgebraicGeometry.AssociatedPointPrime

universe u

namespace AlgebraicGeometry

/-- A universally injective map is injective. -/
private theorem injective_of_universallyInjective {R M N : Type u} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] {g : M →ₗ[R] N}
    (hg : _root_.UniversallyInjective g) : Function.Injective g := by
  intro a b hab
  have h : (g.rTensor R) (a ⊗ₜ[R] (1 : R)) = (g.rTensor R) (b ⊗ₜ[R] (1 : R)) := by
    simp only [LinearMap.rTensor_tmul, hab]
  simpa using congrArg (TensorProduct.rid R M) (hg R h)

/-- **Stacks 058P**, in the form needed here: in an exact sequence `M₁ → M₂ → M₃ → 0` with
`M₁ → M₂` universally injective and `M₂` flat, the quotient `M₃` is flat. -/
private theorem flat_quotient_of_universallyInjective
    {R M₁ M₂ M₃ : Type u} [CommRing R]
    [AddCommGroup M₁] [AddCommGroup M₂] [AddCommGroup M₃]
    [Module R M₁] [Module R M₂] [Module R M₃]
    (u : M₁ →ₗ[R] M₂) (v : M₂ →ₗ[R] M₃)
    (hu : _root_.UniversallyInjective u) (hex : Function.Exact u v)
    (hv : Function.Surjective v) (hM₂ : Module.Flat R M₂) :
    Module.Flat R M₃ := by
  exact (UniversallyExact.flat_of_middle_flat u v
    ⟨injective_of_universallyInjective hu, hv, hex, hu⟩ hM₂).2


/-! ### Flatness of the cokernel on stalks -/

/-- The stalk of a cokernel is the cokernel of the stalk map: the sequence
`ℱ_x → 𝒢_x → (coker α)_x` is exact. [Stacks, Tag 01AG] takes the exact cokernel sequence of
modules to an exact sequence of abelian groups. -/
private theorem exact_schemeStalkMap_cokernel {X : Scheme.{u}} {F G : X.Modules}
    (α : F ⟶ G) (x : X) :
    Function.Exact (schemeStalkMap α x) (schemeStalkMap (cokernel.π α) x) := by
  let A : X.Modules ⥤ AddCommGrpCat.{u} :=
    Scheme.Modules.toPresheaf X ⋙ TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x
  have hA : ∀ D : ShortComplex X.Modules, D.Exact → (D.map A).Exact := fun D hD ↦
    (SheafOfModules.exact_iff_stalkShortComplex_exact _ D).mp hD x
  have h := hA (ShortComplex.cokernelSequence α) (ShortComplex.cokernelSequence_exact α)
  exact (ShortComplex.ab_exact_iff_function_exact _).mp h

/-- The stalk map of the projection to a cokernel is surjective: the stalk functor preserves
finite colimits, hence epimorphisms. -/
private theorem surjective_schemeStalkMap_cokernelπ {X : Scheme.{u}} {F G : X.Modules}
    (α : F ⟶ G) (x : X) :
    Function.Surjective (schemeStalkMap (cokernel.π α) x) := by
  let A : X.Modules ⥤ AddCommGrpCat.{u} :=
    Scheme.Modules.toPresheaf X ⋙ TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x
  have : PreservesFiniteColimits A :=
    (Scheme.Modules.presheafStalk_preservesFiniteLimitsAndColimits x).2
  have hepi : Epi (A.map (cokernel.π α)) := preserves_epi_of_preservesColimit A (cokernel.π α)
  exact (AddCommGrpCat.epi_iff_surjective (A.map (cokernel.π α))).mp hepi

/-- The germ map intertwines the action of `Γ(X, U)` on sections with its action on the stalk at
a point of `U`, so the stalk map of `α` is linear over `Γ(X, U)`. -/
private theorem schemeStalkMap_smul {X : Scheme.{u}} {F G : X.Modules} (α : F ⟶ G) (x : X)
    (a : X.presheaf.stalk x) (m : F.presheaf.stalk x) :
    schemeStalkMap α x (a • m) = a • schemeStalkMap α x m :=
  (schemeStalkLinearMap α x).map_smul a m



/-- Universal injectivity transfers along linear equivalences of the source and of the target
which commute with the two maps. -/
theorem universallyInjective_of_linearEquiv
    {R : Type u} [CommRing R] {M N M' N' : Type u}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [AddCommGroup M'] [Module R M'] [AddCommGroup N'] [Module R N']
    {g : M →ₗ[R] N} {g' : M' →ₗ[R] N'}
    (eM : M ≃ₗ[R] M') (eN : N ≃ₗ[R] N')
    (hcomm : ∀ m, eN (g m) = g' (eM m))
    (hg : _root_.UniversallyInjective g) : _root_.UniversallyInjective g' := by
  intro Q _ _
  have hsq : ∀ t : TensorProduct R M Q,
      (g'.rTensor Q) ((eM.rTensor Q) t) = (eN.rTensor Q) ((g.rTensor Q) t) := by
    intro t
    induction t using TensorProduct.inductionOn with
    | add a b ha hb => simp only [map_add, ha, hb]
    | tmul m q =>
      simp only [LinearEquiv.rTensor, TensorProduct.congr_tmul, LinearEquiv.refl_apply,
        LinearMap.rTensor_tmul, hcomm]
  intro uu vv huv
  obtain ⟨a, rfl⟩ := (eM.rTensor Q).surjective uu
  obtain ⟨b, rfl⟩ := (eM.rTensor Q).surjective vv
  rw [hsq, hsq] at huv
  exact congrArg (fun t => (eM.rTensor Q) t) (hg Q ((eN.rTensor Q).injective huv))

/-- The sections of a morphism of modules over an open set, as a linear map. -/
noncomputable def schemeAppLinearMap {X : Scheme.{u}} {G F : X.Modules}
    (α : G ⟶ F) (U : X.Opens) : Γ(G, U) →ₗ[Γ(X, U)] Γ(F, U) where
  toFun := α.app U
  map_add' := map_add _
  map_smul' := fun r s => α.app_smul r s

/-- The stalk map of a morphism of modules at `x`, as a map of `Γ(X, U)`-modules for an open
set `U` containing `x`. -/
private noncomputable def schemeStalkSectionsLinearMap {X : Scheme.{u}} {G F : X.Modules}
    (α : G ⟶ F) {U : X.Opens} {x : X} (hx : x ∈ U) :
    letI := sectionsStalkModule G hx
    letI := sectionsStalkModule F hx
    G.presheaf.stalk x →ₗ[Γ(X, U)] F.presheaf.stalk x :=
  letI := sectionsStalkModule G hx
  letI := sectionsStalkModule F hx
  { toFun := schemeStalkMap α x
    map_add' := (schemeStalkMap α x).hom.map_add
    map_smul' := fun r m => by
      rw [smul_stalk_eq G hx r m, schemeStalkMap_smul α x, RingHom.id_apply,
        smul_stalk_eq F hx r] }

/-- The germ maps intertwine the map on sections with the map on stalks. -/
private theorem germₗ_comp_schemeAppLinearMap {X : Scheme.{u}} {G F : X.Modules}
    (α : G ⟶ F) {U : X.Opens} {x : X} (hx : x ∈ U) :
    letI := sectionsStalkModule G hx
    letI := sectionsStalkModule F hx
    (germₗ F hx) ∘ₗ (schemeAppLinearMap α U) =
      (schemeStalkSectionsLinearMap α hx) ∘ₗ (germₗ G hx) := by
  let := sectionsStalkModule G hx
  let := sectionsStalkModule F hx
  apply LinearMap.ext
  intro s
  exact (TopCat.Presheaf.stalkFunctor_map_germ_apply U x hx α.mapPresheaf s).symm

/-- **The chart-to-stalk comparison for universal injectivity.** Let `U` be an affine open of
`X` containing `x`, and let `R` act on `Γ(X, U)`. If the map of sections of `α` over `U` is
universally injective as a map of `R`-modules, then so is the map of stalks of `α` at `x`. -/
private theorem universallyInjective_schemeStalk_of_sections
    {X : Scheme.{u}} {G F : X.Modules} [G.IsQuasicoherent] [F.IsQuasicoherent]
    (α : G ⟶ F) {U : X.Opens} (hU : IsAffineOpen U) {x : X} (hx : x ∈ U)
    {R : Type u} [CommRing R] [Algebra R Γ(X, U)]
    [Module R Γ(G, U)] [IsScalarTower R Γ(X, U) Γ(G, U)]
    [Module R Γ(F, U)] [IsScalarTower R Γ(X, U) Γ(F, U)]
    (hα : _root_.UniversallyInjective ((schemeAppLinearMap α U).restrictScalars R)) :
    letI := sectionsStalkModule G hx
    letI := sectionsStalkModule F hx
    letI : Module R (G.presheaf.stalk x) := Module.compHom _ (algebraMap R Γ(X, U))
    letI : Module R (F.presheaf.stalk x) := Module.compHom _ (algebraMap R Γ(X, U))
    haveI : IsScalarTower R Γ(X, U) (G.presheaf.stalk x) :=
      IsScalarTower.of_algebraMap_smul fun _ _ => rfl
    haveI : IsScalarTower R Γ(X, U) (F.presheaf.stalk x) :=
      IsScalarTower.of_algebraMap_smul fun _ _ => rfl
    _root_.UniversallyInjective
      ((schemeStalkSectionsLinearMap α hx).restrictScalars R) := by
  let := sectionsStalkModule G hx
  let := sectionsStalkModule F hx
  let : Module R (G.presheaf.stalk x) := Module.compHom _ (algebraMap R Γ(X, U))
  let : Module R (F.presheaf.stalk x) := Module.compHom _ (algebraMap R Γ(X, U))
  have : IsScalarTower R Γ(X, U) (G.presheaf.stalk x) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have : IsScalarTower R Γ(X, U) (F.presheaf.stalk x) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  set q : Ideal Γ(X, U) := (hU.primeIdealOf ⟨x, hx⟩).asIdeal with hq
  have : q.IsPrime := (hU.primeIdealOf ⟨x, hx⟩).isPrime
  have : IsLocalizedModule q.primeCompl (germₗ G hx) := isLocalizedModule_germₗ G hU hx
  have : IsLocalizedModule q.primeCompl (germₗ F hx) := isLocalizedModule_germₗ F hU hx
  have hloc := (Stacks.UniversalInjectivity.LocalizationCriteria.universally_injective_check_stalks
      (schemeAppLinearMap α U) |>.out 1 2).mp hα
  have hsq : (IsLocalizedModule.iso q.primeCompl (germₗ F hx)).toLinearMap ∘ₗ
        LocalizedModule.map q.primeCompl (schemeAppLinearMap α U) =
      (schemeStalkSectionsLinearMap α hx) ∘ₗ
        (IsLocalizedModule.iso q.primeCompl (germₗ G hx)).toLinearMap := by
    apply IsLocalizedModule.linearMap_ext q.primeCompl
      (LocalizedModule.mkLinearMap q.primeCompl Γ(G, U)) (germₗ F hx)
    apply LinearMap.ext
    intro m
    simp only [LinearMap.comp_apply, LocalizedModule.mkLinearMap_apply, LinearEquiv.coe_coe,
      LinearMap.restrictScalars_apply]
    rw [LocalizedModule.map_mk, IsLocalizedModule.iso_mk_one, IsLocalizedModule.iso_mk_one]
    exact congrArg (fun t => t m) (germₗ_comp_schemeAppLinearMap α hx)
  refine universallyInjective_of_linearEquiv
    ((IsLocalizedModule.iso q.primeCompl (germₗ G hx)).restrictScalars R)
    ((IsLocalizedModule.iso q.primeCompl (germₗ F hx)).restrictScalars R) ?_ (hloc q)
  intro t
  exact congrArg (fun k => k t) hsq

/-- The chart-to-stalk comparison, in the form of injectivity: the map of sections of `α` over an
affine open `U` being universally injective makes the stalk map of `α` at `x ∈ U` injective. -/
private theorem injective_schemeStalkMap_of_sections
    {X : Scheme.{u}} {G F : X.Modules} [G.IsQuasicoherent] [F.IsQuasicoherent]
    (α : G ⟶ F) {U : X.Opens} (hU : IsAffineOpen U) {x : X} (hx : x ∈ U)
    {R : Type u} [CommRing R] [Algebra R Γ(X, U)]
    [Module R Γ(G, U)] [IsScalarTower R Γ(X, U) Γ(G, U)]
    [Module R Γ(F, U)] [IsScalarTower R Γ(X, U) Γ(F, U)]
    (hα : _root_.UniversallyInjective ((schemeAppLinearMap α U).restrictScalars R)) :
    Function.Injective (schemeStalkMap α x) := by
  let := sectionsStalkModule G hx
  let := sectionsStalkModule F hx
  let : Module R (G.presheaf.stalk x) := Module.compHom _ (algebraMap R Γ(X, U))
  let : Module R (F.presheaf.stalk x) := Module.compHom _ (algebraMap R Γ(X, U))
  have : IsScalarTower R Γ(X, U) (G.presheaf.stalk x) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have : IsScalarTower R Γ(X, U) (F.presheaf.stalk x) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  exact injective_of_universallyInjective (universallyInjective_schemeStalk_of_sections α hU hx hα)

/-- Flatness over the target at a point, read off an affine open `V` of the base: the stalk
is flat over `Γ(S, V)` exactly when it is flat over the local ring of `S` at `f x`, because the
latter is a localization of the former. -/
theorem isFlatOverAt_iff_flat_sectionsStalk
    {X S : Scheme.{u}} (f : X ⟶ S) (F : X.Modules)
    {V : S.Opens} (hV : IsAffineOpen V) (x : X) (hx : f x ∈ V) :
    AlgebraicGeometry.IsFlatOverAt f.toLRSHom.toShHom F x ↔
      letI : Module (S.presheaf.stalk (f x)) (F.presheaf.stalk x) :=
        Module.compHom _ (f.stalkMap x).hom
      letI : Module Γ(S, V) (F.presheaf.stalk x) :=
        Module.compHom _ (S.presheaf.germ V (f x) hx).hom
      Module.Flat Γ(S, V) (F.presheaf.stalk x) := by
  let : Algebra Γ(S, V) (S.presheaf.stalk (f x)) :=
    S.presheaf.algebra_section_stalk ⟨f x, hx⟩
  have : IsLocalization (hV.primeIdealOf ⟨f x, hx⟩).asIdeal.primeCompl
      (S.presheaf.stalk (f x)) := hV.isLocalization_stalk ⟨f x, hx⟩
  let : Module (S.presheaf.stalk (f x)) (F.presheaf.stalk x) :=
    Module.compHom _ (f.stalkMap x).hom
  let : Module Γ(S, V) (F.presheaf.stalk x) :=
    Module.compHom _ (S.presheaf.germ V (f x) hx).hom
  have : IsScalarTower Γ(S, V) (S.presheaf.stalk (f x)) (F.presheaf.stalk x) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  exact Module.flat_iff_of_isLocalization (S.presheaf.stalk (f x))
    (hV.primeIdealOf ⟨f x, hx⟩).asIdeal.primeCompl (F.presheaf.stalk x)

/-- The two `Γ(S, V)`-actions on a stalk agree: through the local ring of `S` at `f x`, and
through the sections of `X` over an open `U ≤ f ⁻¹ᵁ V` containing `x`. -/
theorem sectionsStalkModule_compHom_eq
    {X S : Scheme.{u}} (f : X ⟶ S) (F : X.Modules)
    {V : S.Opens} {U : X.Opens} (hUV : U ≤ f ⁻¹ᵁ V) {x : X} (hx : x ∈ U) :
    letI : Algebra Γ(S, V) Γ(X, U) := (f.appLE V U hUV).hom.toAlgebra
    letI := sectionsStalkModule F hx
    letI : Module (S.presheaf.stalk (f x)) (F.presheaf.stalk x) :=
      Module.compHom _ (f.stalkMap x).hom
    (Module.compHom (F.presheaf.stalk x) (algebraMap Γ(S, V) Γ(X, U)) :
        Module Γ(S, V) (F.presheaf.stalk x)) =
      Module.compHom (F.presheaf.stalk x) (S.presheaf.germ V (f x) (hUV hx)).hom := by
  let : Algebra Γ(S, V) Γ(X, U) := (f.appLE V U hUV).hom.toAlgebra
  let := sectionsStalkModule F hx
  let : Module (S.presheaf.stalk (f x)) (F.presheaf.stalk x) :=
    Module.compHom _ (f.stalkMap x).hom
  apply Module.ext'
  intro a m
  have hfx : f x ∈ V := hUV hx
  change (X.presheaf.germ U x hx) ((f.appLE V U hUV) a) • m =
    (f.stalkMap x) ((S.presheaf.germ V (f x) hfx) a) • m
  congr 1
  rw [Scheme.Hom.germ_stalkMap_apply]
  change (X.presheaf.germ U x hx) ((X.presheaf.map (homOfLE hUV).op) ((f.app V) a)) = _
  exact X.presheaf.germ_res_apply (homOfLE hUV) x hx ((f.app V) a)

/-- **Flatness of the cokernel at a point, from universal injectivity of the sections map on an
affine chart.** This is `isFlatOverAt_cokernel_of_universallyInjective_stalk` with the
universal injectivity hypothesis in the form the chart supplies it: over the sections
`Γ(S, V)` of the base, for one affine open `U ≤ f ⁻¹ᵁ V` containing `x`. -/
theorem isFlatOverAt_cokernel_of_universallyInjective_sections
    {X S : Scheme.{u}} (f : X ⟶ S) {G F : X.Modules}
    [G.IsQuasicoherent] [F.IsQuasicoherent] (α : G ⟶ F)
    {V : S.Opens} (hV : IsAffineOpen V) {U : X.Opens} (hU : IsAffineOpen U)
    (hUV : U ≤ f ⁻¹ᵁ V) {x : X} (hx : x ∈ U)
    (hα : letI : Algebra Γ(S, V) Γ(X, U) := (f.appLE V U hUV).hom.toAlgebra
      letI : Module Γ(S, V) Γ(G, U) := Module.compHom _ (f.appLE V U hUV).hom
      letI : Module Γ(S, V) Γ(F, U) := Module.compHom _ (f.appLE V U hUV).hom
      haveI : IsScalarTower Γ(S, V) Γ(X, U) Γ(G, U) :=
        IsScalarTower.of_algebraMap_smul fun _ _ => rfl
      haveI : IsScalarTower Γ(S, V) Γ(X, U) Γ(F, U) :=
        IsScalarTower.of_algebraMap_smul fun _ _ => rfl
      _root_.UniversallyInjective
        ((schemeAppLinearMap α U).restrictScalars Γ(S, V)))
    (hF : AlgebraicGeometry.IsFlatOverAt f.toLRSHom.toShHom F x) :
    AlgebraicGeometry.IsFlatOverAt f.toLRSHom.toShHom (cokernel α) x := by
  have hfx : f x ∈ V := hUV hx
  let : Algebra Γ(S, V) Γ(X, U) := (f.appLE V U hUV).hom.toAlgebra
  let : Module Γ(S, V) Γ(G, U) := Module.compHom _ (f.appLE V U hUV).hom
  let : Module Γ(S, V) Γ(F, U) := Module.compHom _ (f.appLE V U hUV).hom
  have : IsScalarTower Γ(S, V) Γ(X, U) Γ(G, U) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have : IsScalarTower Γ(S, V) Γ(X, U) Γ(F, U) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let : Module Γ(X, U) (G.presheaf.stalk x) := sectionsStalkModule G hx
  let : Module Γ(X, U) (F.presheaf.stalk x) := sectionsStalkModule F hx
  let : Module Γ(X, U) ((cokernel α).presheaf.stalk x) := sectionsStalkModule (cokernel α) hx
  let sG : Module Γ(S, V) (G.presheaf.stalk x) :=
    Module.compHom _ (algebraMap Γ(S, V) Γ(X, U))
  let sF : Module Γ(S, V) (F.presheaf.stalk x) :=
    Module.compHom _ (algebraMap Γ(S, V) Γ(X, U))
  let sC : Module Γ(S, V) ((cokernel α).presheaf.stalk x) :=
    Module.compHom _ (algebraMap Γ(S, V) Γ(X, U))
  have : IsScalarTower Γ(S, V) Γ(X, U) (G.presheaf.stalk x) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have : IsScalarTower Γ(S, V) Γ(X, U) (F.presheaf.stalk x) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have : IsScalarTower Γ(S, V) Γ(X, U) ((cokernel α).presheaf.stalk x) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have hstalk := universallyInjective_schemeStalk_of_sections α hU hx hα
  have hFflat : @Module.Flat Γ(S, V) (F.presheaf.stalk x) _ _ sF := by
    rw [isFlatOverAt_iff_flat_sectionsStalk f F hV x hfx] at hF
    rw [show sF = _ from sectionsStalkModule_compHom_eq f F hUV hx]
    exact hF
  have hCflat : @Module.Flat Γ(S, V) ((cokernel α).presheaf.stalk x) _ _ sC :=
    flat_quotient_of_universallyInjective
      ((schemeStalkSectionsLinearMap α hx).restrictScalars Γ(S, V))
      ((schemeStalkSectionsLinearMap (cokernel.π α) hx).restrictScalars Γ(S, V))
      hstalk (exact_schemeStalkMap_cokernel α x)
      (surjective_schemeStalkMap_cokernelπ α x) hFflat
  refine (isFlatOverAt_iff_flat_sectionsStalk f (cokernel α) hV x hfx).mpr ?_
  rw [← show sC = _ from sectionsStalkModule_compHom_eq f (cokernel α) hUV hx]
  exact hCflat

/-- **Flatness of the target and of the cokernel agree at a point, from universal injectivity of
the sections map on an affine chart**, as soon as the source is flat there. One direction is
`AlgebraicGeometry.isFlatOverAt_cokernel_of_universallyInjective_sections`. For the other, the
stalk map of `α` at `x` is injective, being universally injective by
`AlgebraicGeometry.universallyInjective_schemeStalk_of_sections`, so the stalk sequence
`0 → 𝒢_x → ℱ_x → (coker α)_x → 0` is short exact and two out of three ([Stacks, Tag 00HM])
applies. -/
theorem isFlatOverAt_iff_cokernel_of_universallyInjective_sections
    {X S : Scheme.{u}} (f : X ⟶ S) {G F : X.Modules}
    [G.IsQuasicoherent] [F.IsQuasicoherent] (α : G ⟶ F)
    {V : S.Opens} (hV : IsAffineOpen V) {U : X.Opens} (hU : IsAffineOpen U)
    (hUV : U ≤ f ⁻¹ᵁ V) {x : X} (hx : x ∈ U)
    (hα : letI : Algebra Γ(S, V) Γ(X, U) := (f.appLE V U hUV).hom.toAlgebra
      letI : Module Γ(S, V) Γ(G, U) := Module.compHom _ (f.appLE V U hUV).hom
      letI : Module Γ(S, V) Γ(F, U) := Module.compHom _ (f.appLE V U hUV).hom
      haveI : IsScalarTower Γ(S, V) Γ(X, U) Γ(G, U) :=
        IsScalarTower.of_algebraMap_smul fun _ _ => rfl
      haveI : IsScalarTower Γ(S, V) Γ(X, U) Γ(F, U) :=
        IsScalarTower.of_algebraMap_smul fun _ _ => rfl
      _root_.UniversallyInjective
        ((schemeAppLinearMap α U).restrictScalars Γ(S, V)))
    (hG : AlgebraicGeometry.IsFlatOverAt f.toLRSHom.toShHom G x) :
    AlgebraicGeometry.IsFlatOverAt f.toLRSHom.toShHom F x ↔
      AlgebraicGeometry.IsFlatOverAt f.toLRSHom.toShHom (cokernel α) x := by
  refine ⟨isFlatOverAt_cokernel_of_universallyInjective_sections f α hV hU hUV hx hα, fun hC ↦ ?_⟩
  let : Algebra Γ(S, V) Γ(X, U) := (f.appLE V U hUV).hom.toAlgebra
  let : Module Γ(S, V) Γ(G, U) := Module.compHom _ (f.appLE V U hUV).hom
  let : Module Γ(S, V) Γ(F, U) := Module.compHom _ (f.appLE V U hUV).hom
  have : IsScalarTower Γ(S, V) Γ(X, U) Γ(G, U) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have : IsScalarTower Γ(S, V) Γ(X, U) Γ(F, U) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have hinj := injective_schemeStalkMap_of_sections α hU hx hα
  let : Module (S.presheaf.stalk (f x)) (G.presheaf.stalk x) :=
    Module.compHom _ (f.stalkMap x).hom
  let : Module (S.presheaf.stalk (f x)) (F.presheaf.stalk x) :=
    Module.compHom _ (f.stalkMap x).hom
  let : Module (S.presheaf.stalk (f x)) ((cokernel α).presheaf.stalk x) :=
    Module.compHom _ (f.stalkMap x).hom
  have : Module.Flat (S.presheaf.stalk (f x)) (G.presheaf.stalk x) := hG
  have : Module.Flat (S.presheaf.stalk (f x)) ((cokernel α).presheaf.stalk x) := hC
  change Module.Flat (S.presheaf.stalk (f x)) (F.presheaf.stalk x)
  exact _root_.flat_of_flat_of_flat (baseStalkLinearMap f α x)
    (baseStalkLinearMap f (cokernel.π α) x) hinj (exact_schemeStalkMap_cokernel α x)
    (surjective_schemeStalkMap_cokernelπ α x)

/-- **Flatness of the cokernel over an open of the base, from universal injectivity of the
sections maps on affine charts.** This is
`AlgebraicGeometry.isFlatOverAt_cokernel_of_universallyInjective_sections` run at every point,
with its hypothesis in the form produced on affine charts, which is also the form
`shortExact_map_pullback_of_universallyInjective` consumes. -/
theorem isFlatOver_restrict_cokernel_of_universallyInjective_sections
    {X S : Scheme.{u}} (f : X ⟶ S) {G F : X.Modules}
    [G.IsQuasicoherent] [F.IsQuasicoherent] (α : G ⟶ F)
    [(cokernel α).IsQuasicoherent] (U₀ : S.Opens)
    (hα : ∀ (V : S.Opens) (_ : IsAffineOpen V) (U : X.Opens) (_ : IsAffineOpen U)
      (hUV : U ≤ f ⁻¹ᵁ V),
      letI : Algebra Γ(S, V) Γ(X, U) := (f.appLE V U hUV).hom.toAlgebra
      letI : Module Γ(S, V) Γ(G, U) := Module.compHom _ (f.appLE V U hUV).hom
      letI : Module Γ(S, V) Γ(F, U) := Module.compHom _ (f.appLE V U hUV).hom
      haveI : IsScalarTower Γ(S, V) Γ(X, U) Γ(G, U) :=
        IsScalarTower.of_algebraMap_smul fun _ _ => rfl
      haveI : IsScalarTower Γ(S, V) Γ(X, U) Γ(F, U) :=
        IsScalarTower.of_algebraMap_smul fun _ _ => rfl
      _root_.UniversallyInjective
        ((schemeAppLinearMap α U).restrictScalars Γ(S, V)))
    (hF : AlgebraicGeometry.IsFlatOver (f ∣_ U₀).toLRSHom.toShHom
      ((Scheme.Modules.pullback (f ⁻¹ᵁ U₀).ι).obj F)) :
    AlgebraicGeometry.IsFlatOver (f ∣_ U₀).toLRSHom.toShHom
      ((Scheme.Modules.pullback (f ⁻¹ᵁ U₀).ι).obj (cokernel α)) := by
  apply isFlatOver_restrict_of_flatOnPreimage f (cokernel α) U₀
  intro x hx
  obtain ⟨-, ⟨V : S.Opens, hV, rfl⟩, hfxV, -⟩ :=
    S.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f x)) isOpen_univ
  obtain ⟨-, ⟨U : X.Opens, hU, rfl⟩, hxU, hUV⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open
      (show x ∈ (f ⁻¹ᵁ V : X.Opens) from hfxV) (f ⁻¹ᵁ V).isOpen
  exact isFlatOverAt_cokernel_of_universallyInjective_sections f α hV hU hUV hxU
    (hα V hV U hU hUV) (isFlatOverAt_of_open_restriction f F U₀ x hx hF)


/-- For an affine open `U`, the inverse of `Scheme.ΓSpecIso Γ(X, U)` followed by the inverse of
`hU.fromSpec.appIso ⊤` is the restriction map of `X` along the equality
`hU.fromSpec ''ᵁ ⊤ = U`. -/
lemma fromSpecScalarComp {X : Scheme.{u}} (U : X.Opens) (hU : IsAffineOpen U) :
    (Scheme.ΓSpecIso Γ(X, U)).inv ≫ (hU.fromSpec.appIso ⊤).inv =
      X.presheaf.map (eqToHom (by simp [hU.opensRange_fromSpec] :
        hU.fromSpec ''ᵁ ⊤ = U)).op := by
  have he : (⊤ : (Spec Γ(X, U)).Opens) ≤ hU.fromSpec ⁻¹ᵁ U := by
    rw [hU.fromSpec_preimage_self]
  have happ : hU.fromSpec.appLE U ⊤ he = (Scheme.ΓSpecIso Γ(X, U)).inv := by
    rw [Scheme.Hom.appLE, hU.fromSpec_app_self, Category.assoc, ← Functor.map_comp]
    simp
  rw [← happ, Scheme.Hom.appLE_appIso_inv]
  rfl

/-- The sections of a module over an affine open are the global sections of its pullback to the
spectrum of the sections of the structure sheaf there. -/
def moduleSpecΓFromSpecIso {X : Scheme.{u}} (M : X.Modules)
    (U : X.Opens) (hU : IsAffineOpen U) :
    moduleSpecΓFunctor.obj (M.restrict hU.fromSpec) ≅ ModuleCat.of Γ(X, U) Γ(M, U) := by
  let hi : hU.fromSpec ''ᵁ ⊤ = U := by simp [hU.opensRange_fromSpec]
  let e := M.presheaf.mapIso (eqToIso hi.symm).op
  apply ModuleCat.isoMk e
  intro a
  ext x
  symm
  have ha := congrArg (fun z : Γ(X, U) ⟶ Γ(X, hU.fromSpec ''ᵁ ⊤) ↦ z a)
    (fromSpecScalarComp U hU)
  let x' : M.val.obj (Opposite.op (hU.fromSpec ''ᵁ ⊤)) := x
  let c : X.ringCatSheaf.obj.obj (Opposite.op (hU.fromSpec ''ᵁ ⊤)) :=
    (hU.fromSpec.appIso ⊤).inv
      ((Spec Γ(X, U)).presheaf.map (homOfLE le_top).op ((Scheme.ΓSpecIso Γ(X, U)).inv a))
  change M.val.map (eqToHom hi.symm).op (c • x') =
    (show X.ringCatSheaf.obj.obj (Opposite.op U) from a) • M.val.map (eqToHom hi.symm).op x'
  rw [show M.val.map (eqToHom hi.symm).op (c • x') =
      (show X.ringCatSheaf.obj.obj (Opposite.op U) from
        X.presheaf.map (eqToHom hi.symm).op c) • M.val.map (eqToHom hi.symm).op x'
      from M.val.map_smul _ _ _]
  congr 1
  dsimp only [c]
  simp only [homOfLE_refl, op_id]
  rw [(Spec Γ(X, U)).presheaf.map_id]
  simp only [CommRingCat.id_apply]
  rw [show (hU.fromSpec.appIso ⊤).inv ((Scheme.ΓSpecIso Γ(X, U)).inv a) =
    X.presheaf.map (eqToHom hi).op a from ha]
  change (X.presheaf.map (eqToHom hi.symm).op)
    (X.presheaf.map (eqToHom hi).op a) = a
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  simp

/-- The isomorphism `moduleSpecΓFromSpecIso` is natural in the module: it intertwines the map
induced by a morphism `g : M ⟶ N` on global sections of the restrictions to `Spec Γ(X, U)` with
the map `g` induces on sections over `U`. -/
lemma moduleSpecΓFromSpecIso_naturality {X : Scheme.{u}} {M N : X.Modules}
    (g : M ⟶ N) (U : X.Opens) (hU : IsAffineOpen U) :
    moduleSpecΓFunctor.map ((Scheme.Modules.restrictFunctor hU.fromSpec).map g) ≫
        (moduleSpecΓFromSpecIso N U hU).hom =
      (moduleSpecΓFromSpecIso M U hU).hom ≫ g.val.app (Opposite.op U) := by
  ext x
  exact (PresheafOfModules.naturality_apply g.val
    (eqToHom (by simp [hU.opensRange_fromSpec] : U = hU.fromSpec ''ᵁ ⊤)).op x).symm


/-- The sections over an affine open of the pullback to its spectrum, as an iso natural in the
module. -/
noncomputable def pullbackFromSpecSectionsIso {X : Scheme.{u}} (M : X.Modules)
    (U : X.Opens) (hU : IsAffineOpen U) :
    moduleSpecΓFunctor.obj ((Scheme.Modules.pullback hU.fromSpec).obj M) ≅
      ModuleCat.of Γ(X, U) Γ(M, U) :=
  moduleSpecΓFunctor.mapIso
      (((Scheme.Modules.restrictFunctorIsoPullback hU.fromSpec).app M).symm) ≪≫
    moduleSpecΓFromSpecIso M U hU

/-- The isomorphism `pullbackFromSpecSectionsIso` is natural in the module: it intertwines the
map induced by a morphism `g : M ⟶ N` on global sections of the pullbacks to `Spec Γ(X, U)` with
the map `schemeAppLinearMap g U` on sections over `U`. -/
lemma pullbackFromSpecSectionsIso_naturality {X : Scheme.{u}} {M N : X.Modules}
    (g : M ⟶ N) (U : X.Opens) (hU : IsAffineOpen U) :
    moduleSpecΓFunctor.map ((Scheme.Modules.pullback hU.fromSpec).map g) ≫
        (pullbackFromSpecSectionsIso N U hU).hom =
      (pullbackFromSpecSectionsIso M U hU).hom ≫
        ModuleCat.ofHom (schemeAppLinearMap g U) := by
  have hnat := (Scheme.Modules.restrictFunctorIsoPullback hU.fromSpec).inv.naturality g
  dsimp only [pullbackFromSpecSectionsIso, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom]
  simp only [Iso.app_inv]
  rw [← Category.assoc, ← Functor.map_comp, hnat, Functor.map_comp, Category.assoc,
    moduleSpecΓFromSpecIso_naturality]
  rfl


/-- **The two spellings of the chart hypothesis agree.**  Universal injectivity of the map of
sections of `α` over an affine open `U`, as a map of `Γ(S, V)`-modules, is universal injectivity
of the map of global sections of the pullback of `α` to `Spec Γ(X, U)`. -/
theorem universallyInjective_moduleSpecΓ_of_sections
    {X S : Scheme.{u}} (f : X ⟶ S) {G F : X.Modules} (α : G ⟶ F)
    {V : S.Opens} {U : X.Opens} (hU : IsAffineOpen U) (hUV : U ≤ f ⁻¹ᵁ V)
    (hα : letI : Algebra Γ(S, V) Γ(X, U) := (f.appLE V U hUV).hom.toAlgebra
      letI : Module Γ(S, V) Γ(G, U) := Module.compHom _ (f.appLE V U hUV).hom
      letI : Module Γ(S, V) Γ(F, U) := Module.compHom _ (f.appLE V U hUV).hom
      haveI : IsScalarTower Γ(S, V) Γ(X, U) Γ(G, U) :=
        IsScalarTower.of_algebraMap_smul fun _ _ => rfl
      haveI : IsScalarTower Γ(S, V) Γ(X, U) Γ(F, U) :=
        IsScalarTower.of_algebraMap_smul fun _ _ => rfl
      _root_.UniversallyInjective ((schemeAppLinearMap α U).restrictScalars Γ(S, V))) :
    letI : Algebra Γ(S, V) Γ(X, U) := (f.appLE V U hUV).hom.toAlgebra
    _root_.UniversallyInjective
      ((ModuleCat.restrictScalars (algebraMap Γ(S, V) Γ(X, U))).map
        (moduleSpecΓFunctor.map ((Scheme.Modules.pullback hU.fromSpec).map α))).hom := by
  let : Algebra Γ(S, V) Γ(X, U) := (f.appLE V U hUV).hom.toAlgebra
  let eG := (pullbackFromSpecSectionsIso G U hU).toLinearEquiv
  let eF := (pullbackFromSpecSectionsIso F U hU).toLinearEquiv
  let : Module Γ(S, V) Γ(G, U) := Module.compHom _ (algebraMap Γ(S, V) Γ(X, U))
  let : Module Γ(S, V) Γ(F, U) := Module.compHom _ (algebraMap Γ(S, V) Γ(X, U))
  have : IsScalarTower Γ(S, V) Γ(X, U) Γ(G, U) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have : IsScalarTower Γ(S, V) Γ(X, U) Γ(F, U) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let : Module Γ(S, V) (moduleSpecΓFunctor.obj
      ((Scheme.Modules.pullback hU.fromSpec).obj G)) :=
    Module.compHom _ (algebraMap Γ(S, V) Γ(X, U))
  let : Module Γ(S, V) (moduleSpecΓFunctor.obj
      ((Scheme.Modules.pullback hU.fromSpec).obj F)) :=
    Module.compHom _ (algebraMap Γ(S, V) Γ(X, U))
  have : IsScalarTower Γ(S, V) Γ(X, U) (moduleSpecΓFunctor.obj
      ((Scheme.Modules.pullback hU.fromSpec).obj G)) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have : IsScalarTower Γ(S, V) Γ(X, U) (moduleSpecΓFunctor.obj
      ((Scheme.Modules.pullback hU.fromSpec).obj F)) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  refine universallyInjective_of_linearEquiv (R := Γ(S, V))
    (eG.symm.restrictScalars Γ(S, V)) (eF.symm.restrictScalars Γ(S, V)) ?_ hα
  intro m
  have hnat := pullbackFromSpecSectionsIso_naturality α U hU
  apply eF.injective
  change eF (eF.symm (schemeAppLinearMap α U m)) = _
  rw [eF.apply_symm_apply]
  have := congrArg (fun z : moduleSpecΓFunctor.obj
      ((Scheme.Modules.pullback hU.fromSpec).obj G) ⟶
      ModuleCat.of Γ(X, U) Γ(F, U) ↦ z (eG.symm m)) hnat
  simp only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply] at this
  rw [show (ModuleCat.Hom.hom (pullbackFromSpecSectionsIso G U hU).hom) (eG.symm m) = m from
    eG.apply_symm_apply m] at this
  exact this.symm




/-- **Monomorphy from universal injectivity of the global sections.**  On an affine scheme over
an affine base, a morphism of quasi-coherent modules whose map of global sections is universally
injective over the base is a monomorphism. -/
theorem mono_of_universallyInjective_sections_of_isAffine
    {X S : Scheme.{u}} [IsAffine X] [IsAffine S] (f : X ⟶ S) {G F : X.Modules}
    [G.IsQuasicoherent] [F.IsQuasicoherent] (α : G ⟶ F)
    (hUV : (⊤ : X.Opens) ≤ f ⁻¹ᵁ (⊤ : S.Opens))
    (hα : letI : Algebra Γ(S, ⊤) Γ(X, ⊤) := (f.appLE ⊤ ⊤ hUV).hom.toAlgebra
      letI : Module Γ(S, ⊤) Γ(G, ⊤) := Module.compHom _ (f.appLE ⊤ ⊤ hUV).hom
      letI : Module Γ(S, ⊤) Γ(F, ⊤) := Module.compHom _ (f.appLE ⊤ ⊤ hUV).hom
      haveI : IsScalarTower Γ(S, ⊤) Γ(X, ⊤) Γ(G, ⊤) :=
        IsScalarTower.of_algebraMap_smul fun _ _ => rfl
      haveI : IsScalarTower Γ(S, ⊤) Γ(X, ⊤) Γ(F, ⊤) :=
        IsScalarTower.of_algebraMap_smul fun _ _ => rfl
      _root_.UniversallyInjective ((schemeAppLinearMap α ⊤).restrictScalars Γ(S, ⊤))) :
    Mono α := by
  let : Algebra Γ(S, ⊤) Γ(X, ⊤) := (f.appLE ⊤ ⊤ hUV).hom.toAlgebra
  let : Module Γ(S, ⊤) Γ(G, ⊤) := Module.compHom _ (f.appLE ⊤ ⊤ hUV).hom
  let : Module Γ(S, ⊤) Γ(F, ⊤) := Module.compHom _ (f.appLE ⊤ ⊤ hUV).hom
  have : IsScalarTower Γ(S, ⊤) Γ(X, ⊤) Γ(G, ⊤) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have : IsScalarTower Γ(S, ⊤) Γ(X, ⊤) Γ(F, ⊤) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  apply Scheme.Modules.mono_of_presheafStalk_mono
  intro x
  have hx : x ∈ (⊤ : X.Opens) := trivial
  exact (AddCommGrpCat.mono_iff_injective _).mpr
    (injective_schemeStalkMap_of_sections α (isAffineOpen_top X) hx hα)


/-- **Flatness of the cokernel over an open of the base, from universal injectivity of the
global sections.**  The affine case of
`isFlatOver_restrict_cokernel_of_universallyInjective_sections`, where the only chart needed is
the global one. -/
theorem isFlatOver_restrict_cokernel_of_universallyInjective_sections_of_isAffine
    {X S : Scheme.{u}} [IsAffine X] [IsAffine S] (f : X ⟶ S) {G F : X.Modules}
    [G.IsQuasicoherent] [F.IsQuasicoherent] (α : G ⟶ F)
    [(cokernel α).IsQuasicoherent] (U₀ : S.Opens)
    (hUV : (⊤ : X.Opens) ≤ f ⁻¹ᵁ (⊤ : S.Opens))
    (hα : letI : Algebra Γ(S, ⊤) Γ(X, ⊤) := (f.appLE ⊤ ⊤ hUV).hom.toAlgebra
      letI : Module Γ(S, ⊤) Γ(G, ⊤) := Module.compHom _ (f.appLE ⊤ ⊤ hUV).hom
      letI : Module Γ(S, ⊤) Γ(F, ⊤) := Module.compHom _ (f.appLE ⊤ ⊤ hUV).hom
      haveI : IsScalarTower Γ(S, ⊤) Γ(X, ⊤) Γ(G, ⊤) :=
        IsScalarTower.of_algebraMap_smul fun _ _ => rfl
      haveI : IsScalarTower Γ(S, ⊤) Γ(X, ⊤) Γ(F, ⊤) :=
        IsScalarTower.of_algebraMap_smul fun _ _ => rfl
      _root_.UniversallyInjective ((schemeAppLinearMap α ⊤).restrictScalars Γ(S, ⊤)))
    (hF : AlgebraicGeometry.IsFlatOver (f ∣_ U₀).toLRSHom.toShHom
      ((Scheme.Modules.pullback (f ⁻¹ᵁ U₀).ι).obj F)) :
    AlgebraicGeometry.IsFlatOver (f ∣_ U₀).toLRSHom.toShHom
      ((Scheme.Modules.pullback (f ⁻¹ᵁ U₀).ι).obj (cokernel α)) := by
  apply isFlatOver_restrict_of_flatOnPreimage f (cokernel α) U₀
  intro x hx
  exact isFlatOverAt_cokernel_of_universallyInjective_sections f α (isAffineOpen_top S)
    (isAffineOpen_top X) hUV (show x ∈ (⊤ : X.Opens) from trivial) hα
    (isFlatOverAt_of_open_restriction f F U₀ x hx hF)


/-- **The two spellings of the chart hypothesis agree, converse direction.**  Universal
injectivity of the map of global sections of the pullback of `α` to `Spec Γ(X, U)`, as a map of
`Γ(S, V)`-modules, is universal injectivity of the map of sections of `α` over the affine open
`U`.  This is the converse of `universallyInjective_moduleSpecΓ_of_sections`, obtained by
transporting along the same natural isomorphism `pullbackFromSpecSectionsIso` in the other
direction. -/
theorem universallyInjective_sections_of_moduleSpecΓ
    {X S : Scheme.{u}} (f : X ⟶ S) {G F : X.Modules} (α : G ⟶ F)
    {V : S.Opens} {U : X.Opens} (hU : IsAffineOpen U) (hUV : U ≤ f ⁻¹ᵁ V)
    (hα : letI : Algebra Γ(S, V) Γ(X, U) := (f.appLE V U hUV).hom.toAlgebra
      _root_.UniversallyInjective
        ((ModuleCat.restrictScalars (algebraMap Γ(S, V) Γ(X, U))).map
          (moduleSpecΓFunctor.map ((Scheme.Modules.pullback hU.fromSpec).map α))).hom) :
    letI : Algebra Γ(S, V) Γ(X, U) := (f.appLE V U hUV).hom.toAlgebra
    letI : Module Γ(S, V) Γ(G, U) := Module.compHom _ (f.appLE V U hUV).hom
    letI : Module Γ(S, V) Γ(F, U) := Module.compHom _ (f.appLE V U hUV).hom
    haveI : IsScalarTower Γ(S, V) Γ(X, U) Γ(G, U) :=
      IsScalarTower.of_algebraMap_smul fun _ _ => rfl
    haveI : IsScalarTower Γ(S, V) Γ(X, U) Γ(F, U) :=
      IsScalarTower.of_algebraMap_smul fun _ _ => rfl
    _root_.UniversallyInjective ((schemeAppLinearMap α U).restrictScalars Γ(S, V)) := by
  let : Algebra Γ(S, V) Γ(X, U) := (f.appLE V U hUV).hom.toAlgebra
  let eG := (pullbackFromSpecSectionsIso G U hU).toLinearEquiv
  let eF := (pullbackFromSpecSectionsIso F U hU).toLinearEquiv
  let : Module Γ(S, V) Γ(G, U) := Module.compHom _ (algebraMap Γ(S, V) Γ(X, U))
  let : Module Γ(S, V) Γ(F, U) := Module.compHom _ (algebraMap Γ(S, V) Γ(X, U))
  have : IsScalarTower Γ(S, V) Γ(X, U) Γ(G, U) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have : IsScalarTower Γ(S, V) Γ(X, U) Γ(F, U) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let : Module Γ(S, V) (moduleSpecΓFunctor.obj
      ((Scheme.Modules.pullback hU.fromSpec).obj G)) :=
    Module.compHom _ (algebraMap Γ(S, V) Γ(X, U))
  let : Module Γ(S, V) (moduleSpecΓFunctor.obj
      ((Scheme.Modules.pullback hU.fromSpec).obj F)) :=
    Module.compHom _ (algebraMap Γ(S, V) Γ(X, U))
  have : IsScalarTower Γ(S, V) Γ(X, U) (moduleSpecΓFunctor.obj
      ((Scheme.Modules.pullback hU.fromSpec).obj G)) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have : IsScalarTower Γ(S, V) Γ(X, U) (moduleSpecΓFunctor.obj
      ((Scheme.Modules.pullback hU.fromSpec).obj F)) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  refine universallyInjective_of_linearEquiv (R := Γ(S, V))
    (eG.restrictScalars Γ(S, V)) (eF.restrictScalars Γ(S, V)) ?_ hα
  intro m
  have hnat := congrArg (fun z : moduleSpecΓFunctor.obj
      ((Scheme.Modules.pullback hU.fromSpec).obj G) ⟶
      ModuleCat.of Γ(X, U) Γ(F, U) ↦ z m) (pullbackFromSpecSectionsIso_naturality α U hU)
  simp only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply,
    ModuleCat.hom_ofHom] at hnat
  exact hnat

/-- **`shortExact_map_pullback_of_universallyInjective`, against the sections hypothesis.**  A
short exact sequence of quasi-coherent modules on `X` whose first map has universally injective
sections over every affine open of `X` above an affine open of `S` stays short exact after every
base change of `S`.  The hypothesis here is verbatim the one
`isFlatOver_restrict_cokernel_of_universallyInjective_sections` takes, so a single chart
hypothesis feeds both halves of the chain. -/
theorem shortExact_map_pullback_of_universallyInjective_sections
    {X S : Scheme.{u}} (f : X ⟶ S) (C : ShortComplex X.Modules)
    [C.X₁.IsQuasicoherent] [C.X₂.IsQuasicoherent] (hC : C.ShortExact)
    (hα : ∀ (V : S.Opens) (_ : IsAffineOpen V) (U : X.Opens) (_ : IsAffineOpen U)
      (hUV : U ≤ f ⁻¹ᵁ V),
      letI : Algebra Γ(S, V) Γ(X, U) := (f.appLE V U hUV).hom.toAlgebra
      letI : Module Γ(S, V) Γ(C.X₁, U) := Module.compHom _ (f.appLE V U hUV).hom
      letI : Module Γ(S, V) Γ(C.X₂, U) := Module.compHom _ (f.appLE V U hUV).hom
      haveI : IsScalarTower Γ(S, V) Γ(X, U) Γ(C.X₁, U) :=
        IsScalarTower.of_algebraMap_smul fun _ _ => rfl
      haveI : IsScalarTower Γ(S, V) Γ(X, U) Γ(C.X₂, U) :=
        IsScalarTower.of_algebraMap_smul fun _ _ => rfl
      _root_.UniversallyInjective
        ((schemeAppLinearMap C.f U).restrictScalars Γ(S, V)))
    {T : Scheme.{u}} (g : T ⟶ S) :
    (C.map (Scheme.Modules.pullback (pullback.fst f g))).ShortExact :=
  shortExact_map_pullback_of_universallyInjective f C hC
    (fun V hV U hU hUV =>
      universallyInjective_moduleSpecΓ_of_sections f C.f hU hUV (hα V hV U hU hUV)) g
/-! ### Finiteness of the sections over an affine open -/

private theorem finite_sections_of_finite_type_on_spec
    (R : CommRingCat.{u}) (F : (Spec R).Modules)
    [F.IsQuasicoherent] [F.IsFiniteType] :
    Module.Finite R (moduleSpecΓFunctor.obj F) := by
  have : (tilde (moduleSpecΓFunctor.obj F)).IsFiniteType :=
    Stacks.SheafOfModules.isFiniteType_of_iso.{u} (asIso F.fromTildeΓ).symm
  exact (AlgebraicGeometry.tilde_isFiniteType_iff (moduleSpecΓFunctor.obj F)).mp this

/-- The sections of a quasi-coherent module of finite type over an affine open form a finite
module over the sections of the structure sheaf there. -/
theorem finite_sections_of_isAffineOpen {X : Scheme.{u}} (M : X.Modules)
    [M.IsQuasicoherent] [M.IsFiniteType] (U : X.Opens) (hU : IsAffineOpen U) :
    Module.Finite Γ(X, U) Γ(M, U) := by
  let hMqc : SheafOfModules.IsQuasicoherent (R := structureSheafRing X.toRingedSpace) M :=
    inferInstanceAs (SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) M)
  have hq : ((Scheme.Modules.pullback hU.fromSpec).obj M).IsQuasicoherent :=
    @AlgebraicGeometry.SheafOfModules.modulePullback_isQuasicoherent _ _
      hU.fromSpec.toLRSHom.toShHom M hMqc
  have hf : ((Scheme.Modules.pullback hU.fromSpec).obj M).IsFiniteType :=
    AlgebraicGeometry.SheafOfModules.pullback_isFiniteType hU.fromSpec.toLRSHom.toShHom M
  have := finite_sections_of_finite_type_on_spec Γ(X, U)
    ((Scheme.Modules.pullback hU.fromSpec).obj M)
  exact Module.Finite.equiv (pullbackFromSpecSectionsIso M U hU).toLinearEquiv

end AlgebraicGeometry

end
