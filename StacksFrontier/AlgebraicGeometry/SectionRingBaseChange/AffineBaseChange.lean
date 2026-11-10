module

public import StacksFrontier.AlgebraicGeometry.SectionRingBaseChange.TailPullback
public import StacksFrontier.AlgebraicGeometry.SectionRingBaseChange.Composition
public import StacksFrontier.AlgebraicGeometry.PullbackSections.Transpose
public import StacksFrontier.AlgebraicGeometry.PullbackSections.Affine
public import StacksFrontier.AlgebraicGeometry.SectionRingBaseChange.FinitePresentation
public import Mathlib.RingTheory.TensorProduct.IsBaseChangePi

/-!
# The homomorphism of global section rings is a base change over affine bases

Let

```
Y' --q--> Y
|g'       |g
v         v
T' --h--> T
```

be a commutative square of schemes with `g`, `g'` quasi-compact and quasi-separated, `ℳ`, `ℳ'`
invertible modules on `Y`, `Y'` and `ε : q^*ℳ ≅ ℳ'`. Pulling sections back along `q` gives the
homomorphism of global section rings of the tail truncations
(`Stacks.AlgebraicGeometry.SectionRingBaseChange.squareRingHom`)

`Γ(T, 𝒪_T ⊕ ⨁_{n ≥ e} g_*ℳ^{⊗ n}) ⟶ Γ(T', 𝒪_{T'} ⊕ ⨁_{n ≥ e} g'_*(ℳ')^{⊗ n})`.

When `T` and `T'` are affine and the transposes `h^* 𝒜_n ⟶ 𝒜'_n` of [Stacks, Tag 0D4F] are
isomorphisms, this homomorphism exhibits its target as the base change of its source along
`Γ(T, 𝒪_T) ⟶ Γ(T', 𝒪_{T'})`: the sections of the pullback of a quasi-coherent module over an affine
are the base change of the sections (`AlgebraicGeometry.affinePullbackSectionsBaseChangeIso`),
and the transpose evaluated on the pullback of a section is the pullback of that section
(`tailPullbackHom_app_pullbackSection`).

## Main results

* `Stacks.AlgebraicGeometry.SectionRingBaseChange.tailPullbackHom_app_pullbackSection`.
* `Stacks.AlgebraicGeometry.SectionRingBaseChange.isBaseChange_tailMapLinearTop`: in each
  degree.
* `Stacks.AlgebraicGeometry.SectionRingBaseChange.isBaseChange_lmap_tailMapLinearTop` and
  `lmap_tailMapLinearTop_apply`: for the whole ring.

## References

* [Stacks Project, Tag 0D4F](https://stacks.math.columbia.edu/tag/0D4F)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open Stacks.AlgebraicGeometry.RelativeProjBridge Stacks.AlgebraicGeometry.SectionAlgebra

universe u

namespace Stacks.AlgebraicGeometry.SectionRingBaseChange

/-- Transport along an equality of sheaves of modules commutes with restriction. -/
theorem eqToHom_app_map {Z : Scheme.{u}} {A B : _root_.SheafOfModules.{u} Z.ringCatSheaf}
    (h : A = B) {U U' : (Z.Opens)ᵒᵖ} (i : U ⟶ U') (x : A.val.obj U) :
    B.val.map i ((eqToHom h).val.app U x) = (eqToHom h).val.app U' (A.val.map i x) := by
  cases h
  rfl

variable {T S : Scheme.{u}}
  {P₁ : SheafOfModules.GradedAlgebra.{u, u} T.ringCatSheaf}
  {P₂ : SheafOfModules.GradedAlgebra.{u, u} S.ringCatSheaf}
  {e d : ℕ} {he : 0 < e} {hd : 0 < d} {hde : d ≤ e} {V : T.Opens} {U U' : S.Opens}

/-- **The degreewise map of tail truncations commutes with restriction in the target.** -/
theorem map_tailMapApp (i : U' ≤ U)
    (ρ : T.ringCatSheaf.obj.obj (op V) →+* S.ringCatSheaf.obj.obj (op U))
    (Φ : ∀ n : ℤ, (P₁.piece n).val.obj (op V) →+ (P₂.piece n).val.obj (op U))
    (n : ℤ) (x : (tailPiece P₁ e n).val.obj (op V)) :
    (tailPiece P₂ d n).val.map (homOfLE i).op (tailMapApp P₁ P₂ e d he hd hde V U ρ Φ n x) =
      tailMapApp P₁ P₂ e d he hd hde V U'
        ((S.ringCatSheaf.obj.map (homOfLE i).op).hom.comp ρ)
        (fun m => (ConcreteCategory.hom ((P₂.piece m).val.map (homOfLE i).op)).toAddMonoidHom.comp
          (Φ m)) n x := by
  by_cases h0 : n = 0
  · rw [tailMapApp_zero h0 x]
    refine (eqToHom_app_map (Z := S) (tailPiece_eq_unit P₂ d h0).symm (homOfLE i).op _).trans ?_
    exact (tailMapApp_zero (P₁ := P₁) (P₂ := P₂) (e := e) (d := d) (he := he) (hd := hd)
      (hde := hde) (V := V) (U := U') (ρ := (S.ringCatSheaf.obj.map (homOfLE i).op).hom.comp ρ)
      (Φ := fun m => (ConcreteCategory.hom ((P₂.piece m).val.map
          (homOfLE i).op)).toAddMonoidHom.comp (Φ m)) h0 x).symm
  · by_cases hn : (e : ℤ) ≤ n
    · rw [tailMapApp_tail h0 hn x]
      refine (eqToHom_app_map (Z := S)
        (tailPiece_eq_piece P₂ d hd (show (d : ℤ) ≤ n by omega)).symm (homOfLE i).op _).trans ?_
      exact (tailMapApp_tail (P₁ := P₁) (P₂ := P₂) (e := e) (d := d) (he := he) (hd := hd)
        (hde := hde) (V := V) (U := U') (ρ := (S.ringCatSheaf.obj.map (homOfLE i).op).hom.comp ρ)
        (Φ := fun m => (ConcreteCategory.hom ((P₂.piece m).val.map
          (homOfLE i).op)).toAddMonoidHom.comp (Φ m)) h0 hn x).symm
    · rw [tailMapApp_null h0 hn x]
      rw [map_zero]
      exact (tailMapApp_null h0 hn x).symm

section Square

variable {Y' Y T' T : Scheme.{u}} (q : Y' ⟶ Y) (g : Y ⟶ T) (g' : Y' ⟶ T') (h : T' ⟶ T)
  (w : q ≫ g = g' ≫ h) [QuasiCompact g] [QuasiSeparated g] [QuasiCompact g'] [QuasiSeparated g']
  (M : Y.Modules) [Stacks.Ample.IsInvertibleModule Y M]
  (M' : Y'.Modules) [Stacks.Ample.IsInvertibleModule Y' M']
  (ε : (Scheme.Modules.pullback q).obj M ≅ M') (e : ℕ) (he : 0 < e)

/-- **The transpose of the pullback of sections, on the pullback of a global section, is the
degree-`n` component of the homomorphism of global section rings.** -/
theorem tailPullbackHom_app_pullbackSection (n : ℤ) (hV : (⊤ : T'.Opens) ≤ h ⁻¹ᵁ ⊤)
    (a : (tailPiece (Stacks.AlgebraicGeometry.PushforwardGradedAlgebra.pushforwardGradedAlgebra g
      (Stacks.RelativeAmple.laurentPowers M)) e n).val.obj (op ⊤)) :
    ((tailPullbackHom q g g' h w M M' ε e he).app n).val.app (op ⊤)
        (Scheme.Modules.pullbackSection h _ ⊤ ⊤ hV a) =
      tailMapApp _ _ e e he he le_rfl ⊤ ⊤ (h.appLE ⊤ ⊤ hV).hom
        (squarePieceMap q g g' h w M M' ε ⊤ ⊤ hV) n a := by
  refine (Scheme.Modules.pullbackSection_homEquiv h _ _ _ ⊤ ⊤ hV a).trans ?_
  have hh := Equiv.apply_symm_apply ((Scheme.Modules.pullbackPushforwardAdjunction h).homEquiv _ _)
    (tailPushApp q g g' h w M M' ε e he n)
  refine (congrArg (fun t => (tailPiece
    (Stacks.AlgebraicGeometry.PushforwardGradedAlgebra.pushforwardGradedAlgebra g'
      (Stacks.RelativeAmple.laurentPowers M')) e n).val.map (homOfLE hV).op (t.val.app (op ⊤) a))
    hh).trans ?_
  refine (congrArg _ (tailPushApp_app q g g' h w M M' ε e he n ⊤ a)).trans ?_
  refine (map_tailMapApp hV _ _ n a).trans ?_
  have hρ : ((T'.ringCatSheaf.obj.map (homOfLE hV).op).hom.comp (pullRingHom h ⊤)) =
      (h.appLE ⊤ ⊤ hV).hom := rfl
  have hΦ : (fun m => (ConcreteCategory.hom
      (((Stacks.AlgebraicGeometry.PushforwardGradedAlgebra.pushforwardGradedAlgebra g'
        (Stacks.RelativeAmple.laurentPowers M')).piece m).val.map
          (homOfLE hV).op)).toAddMonoidHom.comp
      (squarePieceMap q g g' h w M M' ε ⊤ (h ⁻¹ᵁ ⊤) le_rfl m)) =
      squarePieceMap q g g' h w M M' ε ⊤ ⊤ hV := by
    funext m
    exact AddMonoidHom.ext fun y => map_sectionPull q M M' ε (g ⁻¹ᵁ ⊤) m
      (preimage_le_preimage q g g' h w ⊤ (h ⁻¹ᵁ ⊤) le_rfl) (g'.preimage_mono hV) y
  exact congrArg₂ (fun ρ Φ => tailMapApp _ _ e e he he le_rfl ⊤ ⊤ ρ Φ n a) hρ hΦ

variable (V' : T'.Opens)

/-- The degree-`n` component of the homomorphism of section rings is semilinear. -/
theorem tailMapApp_smul (hV : V' ≤ h ⁻¹ᵁ ⊤) (n : ℕ) (r : Γ(T, ⊤))
    (x : (tailAlgebra g M e he).sectionPieces ⊤ n) :
    tailMapApp _ _ e e he he le_rfl ⊤ V' (h.appLE ⊤ V' hV).hom
        (squarePieceMap q g g' h w M M' ε ⊤ V' hV) n (r • x) =
      (h.appLE ⊤ V' hV r) • (show (tailAlgebra g' M' e he).sectionPieces V' n from
        tailMapApp _ _ e e he he le_rfl ⊤ V' (h.appLE ⊤ V' hV).hom
          (squarePieceMap q g g' h w M M' ε ⊤ V' hV) n x) := by
  let sq := squareRingHom q g g' h w M M' ε e e he he le_rfl ⊤ V' hV
  set y : (tailAlgebra g' M' e he).sectionPieces V' n :=
    tailMapApp _ _ e e he he le_rfl ⊤ V' (h.appLE ⊤ V' hV).hom
      (squarePieceMap q g g' h w M M' ε ⊤ V' hV) n x
  have e4 := SheafGradedAlgebra.strHom_mul_of (tailAlgebra g' M' e he) V' (h.appLE ⊤ V' hV r) y
  have key : DirectSum.of _ n (tailMapApp _ _ e e he he le_rfl ⊤ V' (h.appLE ⊤ V' hV).hom
        (squarePieceMap q g g' h w M M' ε ⊤ V' hV) n (r • x)) =
      DirectSum.of ((tailAlgebra g' M' e he).sectionPieces V') n ((h.appLE ⊤ V' hV r) • y) := by
    refine (squareRingHom_of q g g' h w M M' ε e e he he le_rfl ⊤ V' hV (r • x)).symm.trans ?_
    refine (congrArg sq
      (SheafGradedAlgebra.strHom_mul_of (tailAlgebra g M e he) ⊤ r x).symm).trans ?_
    refine (map_mul sq _ _).trans ?_
    refine (congrArg₂ (· * ·) (squareRingHom_strHom q g g' h w M M' ε e e he he le_rfl ⊤ V' hV r)
      (squareRingHom_of q g g' h w M M' ε e e he he le_rfl ⊤ V' hV x)).trans ?_
    exact e4
  exact DirectSum.of_injective (β := (tailAlgebra g' M' e he).sectionPieces V') n key

/-- The degree-`n` component of the homomorphism of global section rings, as a linear map over
the global functions of the base, the target being a module through `h`. -/
def tailMapLinearTop (hV : (⊤ : T'.Opens) ≤ h ⁻¹ᵁ ⊤) (n : ℕ) :
    letI : Module Γ(T, ⊤) ((tailAlgebra g' M' e he).sectionPieces ⊤ n) :=
      Module.compHom _ (h.appLE ⊤ ⊤ hV).hom
    (tailAlgebra g M e he).sectionPieces ⊤ n →ₗ[Γ(T, ⊤)]
      (tailAlgebra g' M' e he).sectionPieces ⊤ n :=
  letI : Module Γ(T, ⊤) ((tailAlgebra g' M' e he).sectionPieces ⊤ n) :=
    Module.compHom _ (h.appLE ⊤ ⊤ hV).hom
  { toFun := tailMapApp _ _ e e he he le_rfl ⊤ ⊤ (h.appLE ⊤ ⊤ hV).hom
      (squarePieceMap q g g' h w M M' ε ⊤ ⊤ hV) n
    map_add' := map_add _
    map_smul' := tailMapApp_smul q g g' h w M M' ε e he ⊤ hV n }

open scoped ChangeOfRings in
/-- `isBaseChange_of_extendScalars` with the algebra structure given by a ring homomorphism. -/
theorem isBaseChange_of_extendScalars_ringHom {R S : Type u} [CommRing R] [CommRing S]
    (φ : R →+* S) {M N : Type u} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module S N]
    [Module R N] :
    letI : Algebra R S := φ.toAlgebra
    ∀ [IsScalarTower R S N] (f : M →ₗ[R] N)
      (G : (ModuleCat.extendScalars φ).obj (ModuleCat.of R M) ⟶ ModuleCat.of S N),
      Function.Bijective G → (∀ m : M, G ((1 : S) ⊗ₜ[R, φ] m) = f m) → IsBaseChange S f := by
  let : Algebra R S := φ.toAlgebra
  intro _ f G hG h1
  exact isBaseChange_of_extendScalars f G hG h1

open scoped ChangeOfRings in
/-- **Over affine bases, the degree-`n` component of the homomorphism of global section rings is
a base change** as soon as the transpose `h^* 𝒜_n ⟶ 𝒜'_n` is an isomorphism. -/
theorem isBaseChange_tailMapLinearTop [IsAffine T] [IsAffine T'] (hV : (⊤ : T'.Opens) ≤ h ⁻¹ᵁ ⊤)
    (n : ℕ) (hiso : IsIso ((tailPullbackHom q g g' h w M M' ε e he).app n)) :
    letI : Algebra Γ(T, ⊤) Γ(T', ⊤) := (h.appLE ⊤ ⊤ hV).hom.toAlgebra
    letI : Module Γ(T, ⊤) ((tailAlgebra g' M' e he).sectionPieces ⊤ n) :=
      Module.compHom _ (h.appLE ⊤ ⊤ hV).hom
    haveI : IsScalarTower Γ(T, ⊤) Γ(T', ⊤) ((tailAlgebra g' M' e he).sectionPieces ⊤ n) :=
      IsScalarTower.of_algebraMap_smul fun _ _ => rfl
    IsBaseChange Γ(T', ⊤) (tailMapLinearTop q g g' h w M M' ε e he hV n) := by
  let : Algebra Γ(T, ⊤) Γ(T', ⊤) := (h.appLE ⊤ ⊤ hV).hom.toAlgebra
  let : Module Γ(T, ⊤) ((tailAlgebra g' M' e he).sectionPieces ⊤ n) :=
    Module.compHom _ (h.appLE ⊤ ⊤ hV).hom
  have : IsScalarTower Γ(T, ⊤) Γ(T', ⊤) ((tailAlgebra g' M' e he).sectionPieces ⊤ n) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let F := (tailAlgebra g M e he).piece (n : ℤ)
  let F' := (tailAlgebra g' M' e he).piece (n : ℤ)
  let α : (Scheme.Modules.pullback h).obj F ⟶ F' := (tailPullbackHom q g g' h w M M' ε e he).app n
  have : IsIso α := hiso
  let G : (ModuleCat.extendScalars (h.appLE ⊤ ⊤ hV).hom).obj
      (ModuleCat.of Γ(T, ⊤) ((tailAlgebra g M e he).sectionPieces ⊤ n)) ⟶
      ModuleCat.of Γ(T', ⊤) ((tailAlgebra g' M' e he).sectionPieces ⊤ n) :=
    (affinePullbackSectionsBaseChangeIso h F (isAffineOpen_top T) (isAffineOpen_top T') hV).hom ≫
      ModuleCat.ofHom (Scheme.Modules.sectionsLinearMap α ⊤)
  refine isBaseChange_of_extendScalars_ringHom (h.appLE ⊤ ⊤ hV).hom _ G ?_ fun m => ?_
  · have hα : Function.Bijective (Scheme.Modules.sectionsLinearMap α ⊤) :=
      Function.bijective_iff_has_inverse.mpr ⟨Scheme.Modules.sectionsLinearMap (inv α) ⊤,
        fun x => Stacks.AlgebraicGeometry.ProjChartRatioPullbackLocalMul.hom_app_inv_app
          (asIso α).symm ⊤ x,
        fun y => Stacks.AlgebraicGeometry.ProjChartRatioPullbackLocalMul.hom_app_inv_app
          (asIso α) ⊤ y⟩
    let I := affinePullbackSectionsBaseChangeIso h F (isAffineOpen_top T) (isAffineOpen_top T') hV
    have hb : Function.Bijective (ConcreteCategory.hom I.hom) := by
      refine ⟨fun x y hxy => ?_, fun z => ⟨ConcreteCategory.hom I.inv z, I.inv_hom_id_apply z⟩⟩
      have := congrArg (ConcreteCategory.hom I.inv) hxy
      rwa [I.hom_inv_id_apply, I.hom_inv_id_apply] at this
    have hG : ⇑(ConcreteCategory.hom G) = Scheme.Modules.sectionsLinearMap α ⊤ ∘
        ConcreteCategory.hom I.hom := funext fun x => CategoryTheory.comp_apply _ _ x
    rw [hG]
    exact hα.comp hb
  · have hm := affinePullbackSectionsBaseChangeIso_one_tmul h F (isAffineOpen_top T)
      (isAffineOpen_top T') hV m
    have h2 := tailPullbackHom_app_pullbackSection q g g' h w M M' ε e he n hV m
    have h5 : (tailMapLinearTop q g g' h w M M' ε e he hV n) m =
        tailMapApp _ _ e e he he le_rfl ⊤ ⊤ (h.appLE ⊤ ⊤ hV).hom
          (squarePieceMap q g g' h w M M' ε ⊤ ⊤ hV) n m := rfl
    refine Eq.trans ?_ h5.symm
    refine (CategoryTheory.comp_apply _ _ _).trans ?_
    refine Eq.trans ?_ h2
    exact congrArg (Scheme.Modules.sectionsLinearMap α ⊤) hm

attribute [local instance] Stacks.SymGraded.AffinePieces.sectionRingAlgebra in
/-- The homomorphism of global section rings, as a linear map over the global functions of the
base, the target being a module through `h`. -/
def squareLinearTop (hV : (⊤ : T'.Opens) ≤ h ⁻¹ᵁ ⊤) :
    letI : Module Γ(T, ⊤) ((tailAlgebra g' M' e he).sectionRing ⊤) :=
      Module.compHom _ (h.appLE ⊤ ⊤ hV).hom
    (tailAlgebra g M e he).sectionRing ⊤ →ₗ[Γ(T, ⊤)] (tailAlgebra g' M' e he).sectionRing ⊤ :=
  letI : Module Γ(T, ⊤) ((tailAlgebra g' M' e he).sectionRing ⊤) :=
    Module.compHom _ (h.appLE ⊤ ⊤ hV).hom
  { toFun := squareRingHom q g g' h w M M' ε e e he he le_rfl ⊤ ⊤ hV
    map_add' := map_add _
    map_smul' := fun r x => by
      change squareRingHom q g g' h w M M' ε e e he he le_rfl ⊤ ⊤ hV (r • x) =
        (h.appLE ⊤ ⊤ hV r) • squareRingHom q g g' h w M M' ε e e he he le_rfl ⊤ ⊤ hV x
      rw [Algebra.smul_def, Algebra.smul_def, map_mul,
        Stacks.SymGraded.AffinePieces.algebraMap_sectionRingAlgebra,
        Stacks.SymGraded.AffinePieces.algebraMap_sectionRingAlgebra, squareRingHom_strHom] }

/-- **Over affine bases, the homomorphism of global section rings is a base change**, read as the
direct sum of its homogeneous components, as soon as the transposes `h^* 𝒜_n ⟶ 𝒜'_n` are
isomorphisms. -/
theorem isBaseChange_lmap_tailMapLinearTop [IsAffine T] [IsAffine T']
    (hV : (⊤ : T'.Opens) ≤ h ⁻¹ᵁ ⊤)
    (hiso : ∀ n : ℤ, IsIso ((tailPullbackHom q g g' h w M M' ε e he).app n)) :
    letI : Algebra Γ(T, ⊤) Γ(T', ⊤) := (h.appLE ⊤ ⊤ hV).hom.toAlgebra
    letI : ∀ n, Module Γ(T, ⊤) ((tailAlgebra g' M' e he).sectionPieces ⊤ n) :=
      fun _ => Module.compHom _ (h.appLE ⊤ ⊤ hV).hom
    haveI : ∀ n, IsScalarTower Γ(T, ⊤) Γ(T', ⊤) ((tailAlgebra g' M' e he).sectionPieces ⊤ n) :=
      fun _ => IsScalarTower.of_algebraMap_smul fun _ _ => rfl
    IsBaseChange Γ(T', ⊤) (DirectSum.lmap fun n => tailMapLinearTop q g g' h w M M' ε e he hV n) :=
  let : Algebra Γ(T, ⊤) Γ(T', ⊤) := (h.appLE ⊤ ⊤ hV).hom.toAlgebra
  let : ∀ n, Module Γ(T, ⊤) ((tailAlgebra g' M' e he).sectionPieces ⊤ n) :=
    fun _ => Module.compHom _ (h.appLE ⊤ ⊤ hV).hom
  have : ∀ n, IsScalarTower Γ(T, ⊤) Γ(T', ⊤) ((tailAlgebra g' M' e he).sectionPieces ⊤ n) :=
    fun _ => IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  IsBaseChange.directSum fun n => isBaseChange_tailMapLinearTop q g g' h w M M' ε e he hV n (hiso n)

/-- The direct sum of the homogeneous components is the homomorphism of global section rings. -/
theorem lmap_tailMapLinearTop_apply (hV : (⊤ : T'.Opens) ≤ h ⁻¹ᵁ ⊤)
    (x : (tailAlgebra g M e he).sectionRing ⊤) :
    letI : ∀ n, Module Γ(T, ⊤) ((tailAlgebra g' M' e he).sectionPieces ⊤ n) :=
      fun _ => Module.compHom _ (h.appLE ⊤ ⊤ hV).hom
    DirectSum.lmap (fun n => tailMapLinearTop q g g' h w M M' ε e he hV n) x =
      squareRingHom q g g' h w M M' ε e e he he le_rfl ⊤ ⊤ hV x := by
  let : ∀ n, Module Γ(T, ⊤) ((tailAlgebra g' M' e he).sectionPieces ⊤ n) :=
    fun n => Module.compHom _ (h.appLE ⊤ ⊤ hV).hom
  induction x using DirectSum.induction_on with
  | zero => rw [map_zero, map_zero]
  | of n y =>
      exact (DirectSum.lmap_of _ n y).trans
        (squareRingHom_of q g g' h w M M' ε e e he he le_rfl ⊤ ⊤ hV y).symm
  | add x y hx hy => rw [map_add, map_add, hx, hy]

end Square

end Stacks.AlgebraicGeometry.SectionRingBaseChange

end
