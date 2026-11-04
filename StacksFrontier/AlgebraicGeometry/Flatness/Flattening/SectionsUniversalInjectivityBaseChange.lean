module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.SectionsUniversalInjectivity
public import StacksFrontier.AlgebraicGeometry.Pullback.AffineOpens
public import StacksFrontier.AlgebraicGeometry.PullbackSections.Affine
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.AffinePullbackSections
public import StacksFrontier.RingTheory.Flat.UniversallyInjectivePushout

/-!
# Universal injectivity of a map of sections after base change

Let `g : Y ⟶ S` be a morphism of affine schemes and let `α : 𝓔 ⟶ 𝓜` be a morphism of
quasi-coherent modules on `Y` whose map of global sections becomes universally injective over
`Γ(S, ⊤)` after inverting some `a ∈ Γ(S, ⊤)`. For a cartesian square

```
P --p--> Y
|        |
q        g
↓        ↓
T --h--> S
```

and an affine open `V ⊆ T` lying over the basic open `D(a)`, the preimage `q⁻¹V` is affine and
the map of sections of `p^*α` over it is universally injective over `Γ(T, V)`. This is the input
that `AlgebraicGeometry.isFlatOverAt_iff_cokernel_of_universallyInjective_sections` needs on the
base change `P ⟶ T`.

## Main results

* `AlgebraicGeometry.universallyInjective_sections_pullback_of_isPullback`: the universal
  injectivity above.

## Implementation notes

Over the affine opens `⊤ ⊆ S`, `⊤ ⊆ Y`, `V ⊆ T` and `q⁻¹V ⊆ P` the rings of sections form a
pushout square (`AlgebraicGeometry.isPushout_appLE_of_isPullback`), and the sections of
the pullback of a quasi-coherent module over `q⁻¹V` are the extension of scalars of its global
sections (`AlgebraicGeometry.affinePullbackSectionsBaseChangeIso`), naturally in the module. The
universal injectivity is then the algebraic statement
`Stacks.UniversalInjectivity.universallyInjective_baseChange_of_isPushout`.

## References

* [Stacks Project, Tag 058I](https://stacks.math.columbia.edu/tag/058I)
* [Stacks Project, Tag 01I9](https://stacks.math.columbia.edu/tag/01I9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TensorProduct

universe u

namespace AlgebraicGeometry

variable {P Y T S : Scheme.{u}} {p : P ⟶ Y} {q : P ⟶ T} {g : Y ⟶ S} {h : T ⟶ S}

/-- The image of `a` in the sections over an open lying over `D(a)` is a unit. -/
theorem isUnit_appLE_of_le_basicOpen (a : Γ(S, ⊤)) {V : T.Opens}
    (hVa : V ≤ h ⁻¹ᵁ S.basicOpen a) :
    IsUnit (h.appLE ⊤ V (fun _ _ ↦ trivial) a) := by
  refine RingedSpace.isUnit_of_isUnit_germ (X := T.toRingedSpace) V _ fun x hx ↦ ?_
  have hmem : x ∈ T.basicOpen (h.appLE ⊤ V (fun _ _ ↦ trivial) a) := by
    rw [Scheme.basicOpen_appLE h V ⊤ (fun _ _ ↦ trivial) a]
    exact ⟨hx, hVa hx⟩
  exact (T.mem_basicOpen _ x hx).mp hmem

/-- `Stacks.UniversalInjectivity.universallyInjective_baseChange_of_isPushout` for a pushout
square in `CommRingCat`, with the base change written as Mathlib's extension of scalars: if
`u_a` is universally injective over `R`, so is `C ⊗_A u` over `B`. -/
theorem universallyInjective_extendScalars_map_of_isPushout {R A B C : CommRingCat.{u}}
    {φA : R ⟶ A} {φB : R ⟶ B} {ψA : A ⟶ C} {ψB : B ⟶ C} (H : IsPushout φA φB ψA ψB)
    {M N : ModuleCat.{u} A} (v : M ⟶ N) (a : R) (ha : IsUnit (φB a))
    (hv : letI : Module R M := Module.compHom _ φA.hom
      letI : Module R N := Module.compHom _ φA.hom
      letI : Algebra R A := φA.hom.toAlgebra
      haveI : IsScalarTower R A M := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
      haveI : IsScalarTower R A N := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
      ∀ (Q : Type u) [AddCommGroup Q] [Module R Q],
        Function.Injective (((LocalizedModule.map (Submonoid.powers a)
          (v.hom.restrictScalars R)).restrictScalars R).rTensor Q)) :
    letI : Module B ((ModuleCat.extendScalars ψA.hom).obj M) := Module.compHom _ ψB.hom
    letI : Module B ((ModuleCat.extendScalars ψA.hom).obj N) := Module.compHom _ ψB.hom
    letI : Algebra B C := ψB.hom.toAlgebra
    haveI : IsScalarTower B C ((ModuleCat.extendScalars ψA.hom).obj M) :=
      IsScalarTower.of_algebraMap_smul fun _ _ => rfl
    haveI : IsScalarTower B C ((ModuleCat.extendScalars ψA.hom).obj N) :=
      IsScalarTower.of_algebraMap_smul fun _ _ => rfl
    _root_.UniversallyInjective
      (((ModuleCat.extendScalars ψA.hom).map v).hom.restrictScalars B) := by
  let : Algebra R A := φA.hom.toAlgebra
  let : Algebra R B := φB.hom.toAlgebra
  let : Algebra A C := ψA.hom.toAlgebra
  let : Algebra B C := ψB.hom.toAlgebra
  let : Algebra R C := (φA ≫ ψA).hom.toAlgebra
  have : IsScalarTower R A C := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower R B C := IsScalarTower.of_algebraMap_eq' (by
    show (φA ≫ ψA).hom = (φB ≫ ψB).hom
    rw [H.w])
  have : Algebra.IsPushout R B A C :=
    (CommRingCat.isPushout_iff_isPushout.mp H.flip)
  let : Module R M := Module.compHom _ φA.hom
  let : Module R N := Module.compHom _ φA.hom
  have : IsScalarTower R A M := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have : IsScalarTower R A N := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have hbc := Stacks.UniversalInjectivity.universallyInjective_baseChange_of_isPushout
    (R := R) (A := A) (B := B) (C := C) v.hom a ha hv
  let : Module B ((ModuleCat.extendScalars ψA.hom).obj M) := Module.compHom _ ψB.hom
  let : Module B ((ModuleCat.extendScalars ψA.hom).obj N) := Module.compHom _ ψB.hom
  have : IsScalarTower B C ((ModuleCat.extendScalars ψA.hom).obj M) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have : IsScalarTower B C ((ModuleCat.extendScalars ψA.hom).obj N) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  refine universallyInjective_of_linearEquiv
    ((extendScalarsTensorEquiv (R := A) (S := C) M).symm.restrictScalars B)
    ((extendScalarsTensorEquiv (R := A) (S := C) N).symm.restrictScalars B) (fun x ↦ ?_) hbc
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul c m => rfl

/-- In a cartesian square over affine `Y` and `S`, the preimage of an affine open of `T` in
`P` is affine. -/
private theorem isAffineOpen_preimage_of_isPullback (H : IsPullback p q g h) [IsAffine Y]
    [IsAffine S] {V : T.Opens} (hV : IsAffineOpen V) : IsAffineOpen (q ⁻¹ᵁ V) :=
  IsAffineOpen.inf_preimage_of_isPullback H (isAffineOpen_top S) (isAffineOpen_top Y)
    (fun _ _ ↦ trivial) hV (fun _ _ ↦ trivial) (by simp)

/-- **Universal injectivity of a map of sections after base change.** Let `g : Y ⟶ S` be a
morphism of affine schemes, `α` a morphism of quasi-coherent `𝒪_Y`-modules whose map of global
sections is universally injective over `Γ(S, ⊤)` after inverting `a`. In a cartesian square
`P = Y ×_S T`, for an affine open `V ⊆ T` lying over `D(a)`, the map of sections of the pullback
of `α` over `q⁻¹V` is universally injective over `Γ(T, V)`. -/
theorem universallyInjective_sections_pullback_of_isPullback (H : IsPullback p q g h)
    [IsAffine Y] [IsAffine S] {E M : Y.Modules} [E.IsQuasicoherent] [M.IsQuasicoherent]
    (α : E ⟶ M) (a : Γ(S, ⊤))
    (hα : letI : Algebra Γ(S, ⊤) Γ(Y, ⊤) := g.appTop.hom.toAlgebra
      letI : Module Γ(S, ⊤) Γ(E, ⊤) := Module.compHom _ g.appTop.hom
      letI : Module Γ(S, ⊤) Γ(M, ⊤) := Module.compHom _ g.appTop.hom
      haveI : IsScalarTower Γ(S, ⊤) Γ(Y, ⊤) Γ(E, ⊤) :=
        IsScalarTower.of_algebraMap_smul fun _ _ => rfl
      haveI : IsScalarTower Γ(S, ⊤) Γ(Y, ⊤) Γ(M, ⊤) :=
        IsScalarTower.of_algebraMap_smul fun _ _ => rfl
      ∀ (Q : Type u) [AddCommGroup Q] [Module Γ(S, ⊤) Q],
        Function.Injective (((LocalizedModule.map (Submonoid.powers a)
          ((schemeAppLinearMap α ⊤).restrictScalars Γ(S, ⊤))).restrictScalars
            Γ(S, ⊤)).rTensor Q))
    {V : T.Opens} (hV : IsAffineOpen V) (hVa : V ≤ h ⁻¹ᵁ S.basicOpen a) :
    letI : Algebra Γ(T, V) Γ(P, q ⁻¹ᵁ V) := (q.appLE V (q ⁻¹ᵁ V) le_rfl).hom.toAlgebra
    letI : Module Γ(T, V) Γ((Scheme.Modules.pullback p).obj E, q ⁻¹ᵁ V) :=
      Module.compHom _ (q.appLE V (q ⁻¹ᵁ V) le_rfl).hom
    letI : Module Γ(T, V) Γ((Scheme.Modules.pullback p).obj M, q ⁻¹ᵁ V) :=
      Module.compHom _ (q.appLE V (q ⁻¹ᵁ V) le_rfl).hom
    haveI : IsScalarTower Γ(T, V) Γ(P, q ⁻¹ᵁ V)
        Γ((Scheme.Modules.pullback p).obj E, q ⁻¹ᵁ V) :=
      IsScalarTower.of_algebraMap_smul fun _ _ => rfl
    haveI : IsScalarTower Γ(T, V) Γ(P, q ⁻¹ᵁ V)
        Γ((Scheme.Modules.pullback p).obj M, q ⁻¹ᵁ V) :=
      IsScalarTower.of_algebraMap_smul fun _ _ => rfl
    _root_.UniversallyInjective ((schemeAppLinearMap ((Scheme.Modules.pullback p).map α)
      (q ⁻¹ᵁ V)).restrictScalars Γ(T, V)) := by
  let U : P.Opens := q ⁻¹ᵁ V
  have hUeq : U = p ⁻¹ᵁ ⊤ ⊓ q ⁻¹ᵁ V := by simp [U]
  have hU : IsAffineOpen U := isAffineOpen_preimage_of_isPullback H hV
  have hUY : U ≤ p ⁻¹ᵁ ⊤ := by simp
  have htop : g.appLE ⊤ ⊤ (fun _ _ ↦ trivial) = g.appTop := Scheme.Hom.appLE_eq_app g
  let : Algebra Γ(T, V) Γ(P, U) := (q.appLE V U le_rfl).hom.toAlgebra
  -- universal injectivity of the extension of scalars of the map of global sections
  have hpo := isPushout_appLE_of_isPullback H (isAffineOpen_top S) (isAffineOpen_top Y)
    (fun _ _ ↦ trivial) hV (fun _ _ ↦ trivial) hUeq
  rw [htop] at hpo
  have hbc := universallyInjective_extendScalars_map_of_isPushout hpo
    (ModuleCat.ofHom (Scheme.Modules.sectionsLinearMap α ⊤)) a
    (isUnit_appLE_of_le_basicOpen a hVa) hα
  -- the sections of the pullback are the extension of scalars of the global sections
  let : Module Γ(T, V) Γ((Scheme.Modules.pullback p).obj E, U) :=
    Module.compHom _ (q.appLE V U le_rfl).hom
  let : Module Γ(T, V) Γ((Scheme.Modules.pullback p).obj M, U) :=
    Module.compHom _ (q.appLE V U le_rfl).hom
  have : IsScalarTower Γ(T, V) Γ(P, U) Γ((Scheme.Modules.pullback p).obj E, U) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have : IsScalarTower Γ(T, V) Γ(P, U) Γ((Scheme.Modules.pullback p).obj M, U) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let : Module Γ(T, V) ((ModuleCat.extendScalars (p.appLE ⊤ U hUY).hom).obj
      (ModuleCat.of Γ(Y, ⊤) Γ(E, ⊤))) := Module.compHom _ (q.appLE V U le_rfl).hom
  let : Module Γ(T, V) ((ModuleCat.extendScalars (p.appLE ⊤ U hUY).hom).obj
      (ModuleCat.of Γ(Y, ⊤) Γ(M, ⊤))) := Module.compHom _ (q.appLE V U le_rfl).hom
  have : IsScalarTower Γ(T, V) Γ(P, U) ((ModuleCat.extendScalars (p.appLE ⊤ U hUY).hom).obj
      (ModuleCat.of Γ(Y, ⊤) Γ(E, ⊤))) := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have : IsScalarTower Γ(T, V) Γ(P, U) ((ModuleCat.extendScalars (p.appLE ⊤ U hUY).hom).obj
      (ModuleCat.of Γ(Y, ⊤) Γ(M, ⊤))) := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have hnat := affinePullbackSectionsBaseChangeIso_natural p α (isAffineOpen_top Y) hU hUY
  refine universallyInjective_of_linearEquiv
    (LinearEquiv.restrictScalars Γ(T, V)
      (affinePullbackSectionsBaseChangeIso p E (isAffineOpen_top Y) hU hUY).toLinearEquiv)
    (LinearEquiv.restrictScalars Γ(T, V)
      (affinePullbackSectionsBaseChangeIso p M (isAffineOpen_top Y) hU hUY).toLinearEquiv)
    (fun x ↦ ?_) hbc
  have h1 := congrArg ModuleCat.Hom.hom hnat
  rw [ModuleCat.hom_comp, ModuleCat.hom_comp] at h1
  have h2 := LinearMap.congr_fun h1 x
  rw [LinearMap.comp_apply, LinearMap.comp_apply, ModuleCat.hom_ofHom] at h2
  rw [LinearEquiv.restrictScalars_apply, LinearEquiv.restrictScalars_apply,
    LinearMap.restrictScalars_apply, LinearMap.restrictScalars_apply, Iso.toLinearEquiv_apply,
    Iso.toLinearEquiv_apply]
  convert h2.symm using 1
  simp only [Scheme.Modules.sectionsLinearMap_apply]
  rfl

/-- **Flatness of the target and of the cokernel agree after base change.** In the situation of
`AlgebraicGeometry.universallyInjective_sections_pullback_of_isPullback`, for every scheme `T`
over `S` lying over `D(a)` and every point `x` of `Y ×_S T` at which the pullback of `𝓔` is flat
over `T`, the pullbacks of `𝓜` and of `coker α` are flat over `T` at `x` together. -/
theorem isFlatOverAt_pullback_iff_cokernel_of_away [IsAffine Y] [IsAffine S] (g : Y ⟶ S)
    (b : T ⟶ S) {E M : Y.Modules} [E.IsQuasicoherent] [M.IsQuasicoherent] (α : E ⟶ M)
    (a : Γ(S, ⊤))
    (hα : letI : Algebra Γ(S, ⊤) Γ(Y, ⊤) := g.appTop.hom.toAlgebra
      letI : Module Γ(S, ⊤) Γ(E, ⊤) := Module.compHom _ g.appTop.hom
      letI : Module Γ(S, ⊤) Γ(M, ⊤) := Module.compHom _ g.appTop.hom
      haveI : IsScalarTower Γ(S, ⊤) Γ(Y, ⊤) Γ(E, ⊤) :=
        IsScalarTower.of_algebraMap_smul fun _ _ => rfl
      haveI : IsScalarTower Γ(S, ⊤) Γ(Y, ⊤) Γ(M, ⊤) :=
        IsScalarTower.of_algebraMap_smul fun _ _ => rfl
      ∀ (Q : Type u) [AddCommGroup Q] [Module Γ(S, ⊤) Q],
        Function.Injective (((LocalizedModule.map (Submonoid.powers a)
          ((schemeAppLinearMap α ⊤).restrictScalars Γ(S, ⊤))).restrictScalars
            Γ(S, ⊤)).rTensor Q))
    (hb : ∀ t, b t ∈ S.basicOpen a) (x : ↑(pullback g b))
    (hE : IsFlatOverAt (pullback.snd g b).toLRSHom.toShHom
      ((Scheme.Modules.pullback (pullback.fst g b)).obj E) x) :
    IsFlatOverAt (pullback.snd g b).toLRSHom.toShHom
        ((Scheme.Modules.pullback (pullback.fst g b)).obj M) x ↔
      IsFlatOverAt (pullback.snd g b).toLRSHom.toShHom
        ((Scheme.Modules.pullback (pullback.fst g b)).obj (cokernel α)) x := by
  obtain ⟨-, ⟨V, hV, rfl⟩, hxV, -⟩ := T.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (pullback.snd g b x)) isOpen_univ
  have hVa : V ≤ b ⁻¹ᵁ S.basicOpen a := fun t _ ↦ hb t
  have H := IsPullback.of_hasPullback g b
  have hUI := universallyInjective_sections_pullback_of_isPullback H α a hα hV hVa
  have key := isFlatOverAt_iff_cokernel_of_universallyInjective_sections (pullback.snd g b)
    ((Scheme.Modules.pullback (pullback.fst g b)).map α) hV
    (isAffineOpen_preimage_of_isPullback H hV) le_rfl
    (show x ∈ pullback.snd g b ⁻¹ᵁ V from hxV) hUI hE
  exact key.trans (isFlatOverAt_iff_of_moduleIso _
    (PreservesCokernel.iso (Scheme.Modules.pullback (pullback.fst g b)) α).symm x)

end AlgebraicGeometry
