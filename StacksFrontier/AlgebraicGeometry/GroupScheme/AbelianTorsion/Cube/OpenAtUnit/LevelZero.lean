module

public import StacksFrontier.AlgebraicGeometry.GroupScheme.AbelianTorsion.Cube.OpenAtUnit.LiftStep
public import StacksFrontier.AlgebraicGeometry.ClosedImmersionCohomology.Basic
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFullyFaithful.SectionsComplete
public import StacksFrontier.AlgebraicGeometry.AffineBaseChange.Basic

/-!
# The faces at level zero

Let `s : W ⟶ X` be a closed immersion cut out by `I · 𝒪_X`, so that `ℱ / Iℱ = s_* s^* ℱ`, and let
`ℱ` be trivial along `s`. For a face `j : F ⟶ X` (with `ℱ' = j^* ℱ`) whose own closed fibre
`s' : A ⟶ F` maps into `W` by `i : A ⟶ W` (`i ≫ s = s' ≫ j`), the face map
`H¹(X, ℱ / Iℱ) → H¹(X, j_* (ℱ' / Iℱ'))` is, up to isomorphisms, `H¹(W, 𝒪_W) → H¹(W, i_* i^* 𝒪_W)`.
So joint injectivity of the face maps of `Stacks.CubeOpenAtUnit.surjective_quoDrop_app_top`
reduces to joint injectivity on `H¹(W, 𝒪_W)` of the units of the faces, which is the degree-one
Künneth injectivity `Stacks.KunnethLowDegree.injective_H1_faces` in the cube.

## Main results

* `Stacks.CubeOpenAtUnit.unit_comp_unit`: the unit of a composite of two adjunctions
  `f^* ⊣ f_*`, compared with the composite of the units.
* `Stacks.CubeOpenAtUnit.jointlyInjective_quoMap_one`: the reduction.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Algebraization
open Stacks.Cohomology.FormalFunctions (baseIdealSheaf)

universe u

namespace Stacks.CubeOpenAtUnit

/-! ### Units of composites -/

section Units

variable {A B C : Scheme.{u}}

/-- `f^* ⊣ f_*` for `f = a ≫ b`, against the composite of the adjunctions for `a` and `b`. -/
theorem unit_comp_unit (a : A ⟶ B) (b : B ⟶ C) (M : C.Modules) :
    (Scheme.Modules.pullbackPushforwardAdjunction b).unit.app M ≫
        (Scheme.Modules.pushforward b).map
          ((Scheme.Modules.pullbackPushforwardAdjunction a).unit.app
            ((Scheme.Modules.pullback b).obj M)) ≫
        (Scheme.Modules.pushforwardComp a b).hom.app _ =
      (Scheme.Modules.pullbackPushforwardAdjunction (a ≫ b)).unit.app M ≫
        (Scheme.Modules.pushforward (a ≫ b)).map ((Scheme.Modules.pullbackComp a b).inv.app M) := by
  have h := unit_conjugateEquiv ((Scheme.Modules.pullbackPushforwardAdjunction b).comp
    (Scheme.Modules.pullbackPushforwardAdjunction a))
    (Scheme.Modules.pullbackPushforwardAdjunction (a ≫ b)) (Scheme.Modules.pullbackComp a b).inv M
  rw [Scheme.Modules.conjugateEquiv_pullbackComp_inv, Adjunction.comp_unit_app] at h
  simp only [Category.assoc] at h
  exact h

/-- **Two factorizations of one morphism give the same composite unit up to isomorphism.** -/
theorem exists_iso_unit_unit {a : A ⟶ B} {b : B ⟶ C} {B' : Scheme.{u}} {a' : A ⟶ B'}
    {b' : B' ⟶ C} (h : a ≫ b = a' ≫ b') (M : C.Modules) :
    ∃ Z : (Scheme.Modules.pushforward b').obj ((Scheme.Modules.pushforward a').obj
        ((Scheme.Modules.pullback a').obj ((Scheme.Modules.pullback b').obj M))) ≅
      (Scheme.Modules.pushforward b).obj ((Scheme.Modules.pushforward a).obj
        ((Scheme.Modules.pullback a).obj ((Scheme.Modules.pullback b).obj M))),
      (Scheme.Modules.pullbackPushforwardAdjunction b').unit.app M ≫
          (Scheme.Modules.pushforward b').map
            ((Scheme.Modules.pullbackPushforwardAdjunction a').unit.app
              ((Scheme.Modules.pullback b').obj M)) ≫ Z.hom =
        (Scheme.Modules.pullbackPushforwardAdjunction b).unit.app M ≫
          (Scheme.Modules.pushforward b).map
            ((Scheme.Modules.pullbackPushforwardAdjunction a).unit.app
              ((Scheme.Modules.pullback b).obj M)) := by
  let E : ∀ {B'' : Scheme.{u}} (a'' : A ⟶ B'') (b'' : B'' ⟶ C),
      (Scheme.Modules.pushforward (a'' ≫ b'')).obj
          ((Scheme.Modules.pullback (a'' ≫ b'')).obj M) ≅
        (Scheme.Modules.pushforward b'').obj ((Scheme.Modules.pushforward a'').obj
          ((Scheme.Modules.pullback a'').obj ((Scheme.Modules.pullback b'').obj M))) :=
    fun a'' b'' => (Scheme.Modules.pushforward (a'' ≫ b'')).mapIso
        ((Scheme.Modules.pullbackComp a'' b'').app M).symm ≪≫
      ((Scheme.Modules.pushforwardComp a'' b'').app _).symm
  have hE : ∀ {B'' : Scheme.{u}} (a'' : A ⟶ B'') (b'' : B'' ⟶ C),
      (Scheme.Modules.pullbackPushforwardAdjunction b'').unit.app M ≫
          (Scheme.Modules.pushforward b'').map
            ((Scheme.Modules.pullbackPushforwardAdjunction a'').unit.app
              ((Scheme.Modules.pullback b'').obj M)) =
        (Scheme.Modules.pullbackPushforwardAdjunction (a'' ≫ b'')).unit.app M ≫
          (E a'' b'').hom := by
    intro B'' a'' b''
    show _ = _ ≫ (Scheme.Modules.pushforward (a'' ≫ b'')).map
        ((Scheme.Modules.pullbackComp a'' b'').inv.app M) ≫
      (Scheme.Modules.pushforwardComp a'' b'').inv.app _
    rw [← Category.assoc, ← unit_comp_unit, Category.assoc, Category.assoc]
    exact (congrArg (fun t => _ ≫ _ ≫ t)
      ((Scheme.Modules.pushforwardComp a'' b'').hom_inv_id_app _)).trans (by simp)
  -- the units of the two equal composites agree up to the identification of the targets
  obtain ⟨D, hD⟩ : ∃ D : (Scheme.Modules.pushforward (a ≫ b)).obj
        ((Scheme.Modules.pullback (a ≫ b)).obj M) ≅
      (Scheme.Modules.pushforward (a' ≫ b')).obj ((Scheme.Modules.pullback (a' ≫ b')).obj M),
      (Scheme.Modules.pullbackPushforwardAdjunction (a' ≫ b')).unit.app M =
        (Scheme.Modules.pullbackPushforwardAdjunction (a ≫ b)).unit.app M ≫ D.hom := by
    generalize a ≫ b = c at h ⊢
    subst h
    exact ⟨Iso.refl _, (Category.comp_id _).symm⟩
  refine ⟨(E a' b').symm ≪≫ D.symm ≪≫ E a b, ?_⟩
  rw [← Category.assoc, hE a' b', hE a b, hD]
  simp

end Units

/-! ### Faces given by closed immersions -/

variable {R : Type u} [CommRing R] {X : Scheme.{u}} (g : X ⟶ Spec (.of R)) (m : Ideal R)
  (L : X.Modules) [L.IsQuasicoherent]

/-- The face of `(X, ℒ)` given by a closed immersion `j`, with `ℒ' = j^* ℒ` and the adjunction
unit `ℒ ⟶ j_* j^* ℒ`. -/
def Face.ofClosedImmersion {F : Scheme.{u}} (j : F ⟶ X) [IsClosedImmersion j] : Face L :=
  haveI := AlgebraicGeometry.AffineBaseChange.isQuasicoherent_pullback j L
  { F := F, j := j, G' := (Scheme.Modules.pullback j).obj L,
    u := (Scheme.Modules.pullbackPushforwardAdjunction j).unit.app L }

variable {W : Scheme.{u}} (s : W ⟶ X) [IsClosedImmersion s]
  (hs : s.ker = baseIdealSheaf R m g ^ 1)

/-- The quotient projection followed by the comparison isomorphism is the adjunction unit. -/
private theorem quoπ_comp_idealQuotientPushforwardIso_hom {Y V : Scheme.{u}}
    (g' : Y ⟶ Spec (.of R)) (M : Y.Modules) [M.IsQuasicoherent] (v : V ⟶ Y)
    [IsClosedImmersion v] (hv : v.ker = baseIdealSheaf R m g' ^ 1) :
    quoπ g' m M 1 ≫ (idealQuotientPushforwardIso (baseIdealSheaf R m g') 1 M v hv).hom =
      (Scheme.Modules.pullbackPushforwardAdjunction v).unit.app M := by
  rw [idealQuotientPushforwardIso_hom, idealQuotientPushforwardMap_π]

/-- The face map at level one factors the unit of the closed fibre of the face. -/
theorem exists_quoMap_comp {F A : Scheme.{u}} (j : F ⟶ X) [IsClosedImmersion j] (s' : A ⟶ F)
    [IsClosedImmersion s'] (hs' : s'.ker = baseIdealSheaf R m (j ≫ g) ^ 1) (i : A ⟶ W)
    (hcomm : i ≫ s = s' ≫ j) :
    ∃ ψ, (Face.ofClosedImmersion L j).quoMap (g := g) (I := m) 1 ≫ ψ =
      (idealQuotientPushforwardIso (baseIdealSheaf R m g) 1 L s hs).hom ≫
        (Scheme.Modules.pushforward s).map
          ((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app
            ((Scheme.Modules.pullback s).obj L)) := by
  have := AlgebraicGeometry.AffineBaseChange.isQuasicoherent_pullback j L
  obtain ⟨Z, hZ⟩ := exists_iso_unit_unit hcomm L
  let β := idealQuotientPushforwardIso (baseIdealSheaf R m (j ≫ g)) 1
    ((Scheme.Modules.pullback j).obj L) s' hs'
  refine ⟨(Scheme.Modules.pushforward j).map β.hom ≫ Z.hom, ?_⟩
  refine (cancel_epi (quoπ g m L 1)).1 ?_
  have hq : quoπ g m L 1 ≫ (Face.ofClosedImmersion L j).quoMap (g := g) (I := m) 1 =
      (Scheme.Modules.pullbackPushforwardAdjunction j).unit.app L ≫
        (Scheme.Modules.pushforward j).map
          (quoπ (j ≫ g) m ((Scheme.Modules.pullback j).obj L) 1) :=
    (Face.ofClosedImmersion L j).quoπ_quoMap 1
  rw [← Category.assoc, hq, ← Category.assoc, quoπ_comp_idealQuotientPushforwardIso_hom, ← hZ]
  have := congrArg (fun t => (Scheme.Modules.pullbackPushforwardAdjunction j).unit.app L ≫
    (Scheme.Modules.pushforward j).map t ≫ Z.hom)
    (quoπ_comp_idealQuotientPushforwardIso_hom (m := m) (j ≫ g)
      ((Scheme.Modules.pullback j).obj L) s' hs')
  simp only [Functor.map_comp, Category.assoc] at this ⊢
  exact this

/-- Applying `H¹` to an isomorphism gives an injective map. -/
theorem H_map_injective_of_isIso {Y : Scheme.{u}} {M N : Y.Modules} (φ : M ⟶ N) [IsIso φ] (n : ℕ) :
    Function.Injective ((H Y n).map φ).hom :=
  (ConcreteCategory.bijective_of_isIso ((H Y n).map φ)).1

include hs in
/-- **Reduction of the face condition at level one to `H¹(W, 𝒪_W)`.** Let `s : W ⟶ X` be cut out
by `𝔪 · 𝒪_X`, with `s^* ℒ ≅ 𝒪_W`, and let faces `jᵢ : Fᵢ ⟶ X` have closed fibres `s'ᵢ : Aᵢ ⟶ Fᵢ`
(cut out by `𝔪 · 𝒪_{Fᵢ}`) mapping to `W` by `aᵢ`. If the units `𝒪_W ⟶ aᵢ_* aᵢ^* 𝒪_W` are jointly
injective on `H¹(W, 𝒪_W)`, the face maps of `ℒ` at level one are jointly injective on
`H¹(X, ℒ / 𝔪ℒ)`. -/
theorem jointlyInjective_quoMap_one {ι : Type*} {F A : ι → Scheme.{u}} (j : ∀ i, F i ⟶ X)
    [∀ i, IsClosedImmersion (j i)] (s' : ∀ i, A i ⟶ F i) [∀ i, IsClosedImmersion (s' i)]
    (hs' : ∀ i, (s' i).ker = baseIdealSheaf R m (j i ≫ g) ^ 1) (a : ∀ i, A i ⟶ W)
    (hcomm : ∀ i, a i ≫ s = s' i ≫ j i)
    (τ : (Scheme.Modules.pullback s).obj L ≅ SheafOfModules.unit W.ringCatSheaf)
    (hK : ∀ c : (H W 1).obj (SheafOfModules.unit W.ringCatSheaf),
      (∀ i, ((H W 1).map ((Scheme.Modules.pullbackPushforwardAdjunction (a i)).unit.app
        (SheafOfModules.unit W.ringCatSheaf))).hom c = 0) → c = 0)
    (c : (H X 1).obj (quo g m L 1))
    (hc : ∀ i, ((H X 1).map ((Face.ofClosedImmersion L (j i)).quoMap (g := g) (I := m) 1)).hom c
      = 0) : c = 0 := by
  let α := idealQuotientPushforwardIso (baseIdealSheaf R m g) 1 L s hs
  let θI : quo g m L 1 ≅ (Scheme.Modules.pushforward s).obj (SheafOfModules.unit W.ringCatSheaf) :=
    α ≪≫ (Scheme.Modules.pushforward s).mapIso τ
  let θ := θI.hom
  let κ := (Stacks.Cohomology.ClosedImmersion.closedImmersionCohomologyIso s 1).inv
  have hκ : ∀ G, Function.Injective (κ.app G).hom := fun G =>
    (ConcreteCategory.bijective_of_isIso (κ.app G)).1
  refine H_map_injective_of_isIso θ 1 (Eq.trans ?_ (LinearMap.map_zero _).symm)
  refine hκ _ (Eq.trans ?_ (LinearMap.map_zero _).symm)
  refine hK _ fun i => ?_
  obtain ⟨ψ, hψ⟩ := exists_quoMap_comp g m L s hs (j i) (s' i) (hs' i) (a i) (hcomm i)
  have hnat := LinearMap.congr_fun (ModuleCat.hom_ext_iff.1
    (κ.naturality ((Scheme.Modules.pullbackPushforwardAdjunction (a i)).unit.app
      (SheafOfModules.unit W.ringCatSheaf)))) (((H X 1).map θ).hom c)
  simp only [Functor.comp_map, ModuleCat.hom_comp] at hnat
  refine Eq.trans hnat.symm (Eq.trans ?_ (LinearMap.map_zero (κ.app _).hom))
  refine congrArg (κ.app _).hom ?_
  have hu : τ.hom ≫ (Scheme.Modules.pullbackPushforwardAdjunction (a i)).unit.app
        (SheafOfModules.unit W.ringCatSheaf) =
      (Scheme.Modules.pullbackPushforwardAdjunction (a i)).unit.app
          ((Scheme.Modules.pullback s).obj L) ≫
        (Scheme.Modules.pushforward (a i)).map ((Scheme.Modules.pullback (a i)).map τ.hom) :=
    (Scheme.Modules.pullbackPushforwardAdjunction (a i)).unit.naturality τ.hom
  have hcomp : θ ≫ (Scheme.Modules.pushforward s).map
      ((Scheme.Modules.pullbackPushforwardAdjunction (a i)).unit.app
        (SheafOfModules.unit W.ringCatSheaf)) =
      ((Face.ofClosedImmersion L (j i)).quoMap (g := g) (I := m) 1 ≫ ψ) ≫
        (Scheme.Modules.pushforward s).map ((Scheme.Modules.pushforward (a i)).map
          ((Scheme.Modules.pullback (a i)).map τ.hom)) := by
    rw [hψ, Category.assoc, ← Functor.map_comp, ← hu]
    show α.hom ≫ (Scheme.Modules.pushforward s).map τ.hom ≫ _ = α.hom ≫ _
    exact congrArg (α.hom ≫ ·) ((Scheme.Modules.pushforward s).map_comp _ _).symm
  have := congrArg (fun t => ((H X 1).map t).hom c) hcomp
  simp only [Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply, hc i, map_zero] at this
  exact this

end Stacks.CubeOpenAtUnit

end
