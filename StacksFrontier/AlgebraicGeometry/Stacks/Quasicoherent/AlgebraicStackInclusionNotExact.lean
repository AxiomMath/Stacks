module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.CokernelFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.BaseEquivalenceFppf
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.BigSiteNotExact
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentStructureSheaf
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.AlgebraicStackColimits
public import StacksFrontier.AlgebraicGeometry.Stacks.SchemeStack
public import StacksFrontier.CategoryTheory.Sites.Modules.OverFunctorExact

/-!
# The inclusion of quasi-coherent modules on an algebraic stack is not exact

Let `𝒳` be an algebraic stack over `S`.  The inclusion `QCoh(𝒪_𝒳) → Mod(𝒪_𝒳)` is right exact,
because colimits of quasi-coherent modules are computed in `Mod(𝒪_𝒳)`, but it is **not** exact
in general.  The example is the one of Descent, Lemma 06VE (6), read on an algebraic stack: take
`𝒳 = Spec(ℤ)`.  Multiplication by `2` on `𝒪_𝒳` is a monomorphism of `QCoh(𝒪_𝒳)`, since on
`Spec(ℤ)` itself it is injective and a quasi-coherent module is determined by its restriction to
`(Sch/Spec(ℤ))_fppf`; but it is not a monomorphism of `Mod(𝒪_𝒳)`, since its value on the object
`Spec(𝔽₂) → Spec(ℤ)` is multiplication by `2` on `𝔽₂`, which is zero.

The comparison with the big site is made at a final object `x` of `𝒳`: restriction to
`𝒳_fppf/x ≅ (Sch/U)_fppf` (Stacks 06WI) is faithful when `x` is final, additive and left exact, and
carries `𝒪_𝒳` to `𝒪`.  So a monomorphism of `QCoh` on the big site lifts to one on `𝒳`, and a
morphism that fails to be a monomorphism on the big site also fails on `𝒳`.

## Main results

* `SheafOfModules.faithful_overFunctor_of_isTerminal`: restriction of sheaves of modules to the
  slice over a final object is faithful.
* `AlgebraicGeometry.FibredSite.not_preservesFiniteLimits_quasicoherentInclusion_of_isTerminal`:
  the reduction to the big site of a scheme at a final object.
* `AlgebraicGeometry.AssociatedModuleNotExact.mono_two_nsmul_unitQuasicoherentOnSite`: `2` is a
  monomorphism of `𝒪` in the quasi-coherent modules on `(Sch/Spec(ℤ))_fppf`.
* `AlgebraicGeometry.Stack.specIntStack`: `Spec(ℤ)` as an algebraic stack, and
  `AlgebraicGeometry.Stack.not_preservesFiniteLimits_quasicoherentInclusion_specIntStack`: its
  inclusion `QCoh(𝒪_𝒳) → Mod(𝒪_𝒳)` is not left exact.
* `AlgebraicGeometry.Stack.quasicoherentInclusion_rightExact_not_exact`: **Stacks 06WV (3)**.

## Implementation notes

"Not exact in general" is rendered as: on every big fppf site there is an algebraic stack for
which the inclusion fails to be exact.  A big fppf site always contains `Spec(ℤ)`, so the
counterexample exists on each of them.

## References

* [Stacks Project, Tag 06WV](https://stacks.math.columbia.edu/tag/06WV)
* [Stacks Project, Tag 06VE](https://stacks.math.columbia.edu/tag/06VE)
* [Stacks Project, Tag 06WI](https://stacks.math.columbia.edu/tag/06WI)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe w u

/-- **Restriction to the slice over a final object is faithful.**  Every object of the site maps
to the final object, so a morphism of sheaves of modules is determined by its restriction. -/
theorem SheafOfModules.faithful_overFunctor_of_isTerminal {C : Type*} [Category C]
    {J : GrothendieckTopology C} (R : Sheaf J RingCat.{u}) {X : C} (hX : IsTerminal X) :
    (SheafOfModules.overFunctor.{w} R X).Faithful where
  map_injective {M N} f g h := by
    ext Y : 3
    have := congrArg (fun k => k.val.app (op (Over.mk (hX.from Y.unop)))) h
    exact congrArg ModuleCat.Hom.hom this

/-- Conjugating `n • 𝟙 X` by an isomorphism `X ≅ Y` gives `n • 𝟙 Y`. -/
private theorem nsmul_id_eq_inv_comp_nsmul_id_comp_hom {C : Type*} [Category C] [Preadditive C]
    {X Y : C} (e : X ≅ Y) (n : ℕ) : n • 𝟙 Y = e.inv ≫ (n • 𝟙 X) ≫ e.hom := by
  simp

namespace AlgebraicGeometry.FibredSite

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type (u + 1)} [Category.{u} 𝒳]
  (p : 𝒳 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids) {x : 𝒳}

/-- The inverse image `x^*` at an object `x` of `𝒳`, as a functor from the modules on `𝒳` to the
modules on the big fppf site of the scheme `x` lies over: restriction to `𝒳_fppf/x` followed by
the equivalence of Stacks 06WI.  Its value at a module is
`AlgebraicGeometry.FibredSite.objectInverseImage`. -/
abbrev objectInverseImageFunctor (x : 𝒳) :
    SheafOfModules.{u} (ringStructureSheafCore B S hS p hp .fppf) ⥤
      SheafOfModules.{u} (BigFppfOver.structureSheaf B (baseScheme B S hS p x)
        (contains_baseScheme B S hS p x)) :=
  SheafOfModules.overFunctor.{u} (ringStructureSheafCore B S hS p hp .fppf) x ⋙
    (localizationModulesEquivalence B S hS p hp x).inverse

/-- **The reduction to the big site at a final object.**  Let `x` be a final object of `𝒳`, lying
over a scheme `U`.  If `2 : 𝒪 → 𝒪` is a monomorphism of `QCoh((Sch/U)_fppf, 𝒪)` but not of
`Mod((Sch/U)_fppf, 𝒪)`, then the inclusion `QCoh(𝒪_𝒳) → Mod(𝒪_𝒳)` does not preserve finite
limits.

The restriction `x^*` is faithful, additive and left exact, sends quasi-coherent modules to
quasi-coherent modules (Stacks 06WI), and carries `𝒪_𝒳` to `𝒪`.  Faithfulness lifts the
monomorphism to `QCoh(𝒪_𝒳)`; were the inclusion left exact, it would stay a monomorphism in
`Mod(𝒪_𝒳)`, and `x^*` would carry it to a monomorphism of `Mod((Sch/U)_fppf, 𝒪)`. -/
theorem not_preservesFiniteLimits_quasicoherentInclusion_of_isTerminal (hx : IsTerminal x)
    (hmono : Mono (2 • 𝟙 (⟨SheafOfModules.unit _, inferInstance⟩ :
      (SheafOfModules.isQuasicoherentOnSite (BigFppfOver.structureSheaf B (baseScheme B S hS p x)
        (contains_baseScheme B S hS p x))).FullSubcategory)))
    (hnot : ¬ Mono (2 • 𝟙 (SheafOfModules.unit (BigFppfOver.structureSheaf B (baseScheme B S hS p x)
        (contains_baseScheme B S hS p x))))) :
    ¬ PreservesFiniteLimits (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      (ringStructureSheafCore B S hS p hp .fppf)).ι := by
  intro hpres
  let L := localizationModulesEquivalence B S hS p hp x
  let Ψ := objectInverseImageFunctor B S hS p hp x
  have : Ψ.Faithful := by
    have := SheafOfModules.faithful_overFunctor_of_isTerminal.{u}
      (ringStructureSheafCore B S hS p hp .fppf) hx
    exact Functor.Faithful.comp _ _
  have : Ψ.Additive := by
    have : L.functor.Additive := SheafOfModules.pushforward_additive _
    have : L.inverse.Additive := L.toAdjunction.right_adjoint_additive
    have : (SheafOfModules.overFunctor.{u} (ringStructureSheafCore B S hS p hp .fppf) x).Additive :=
      SheafOfModules.pushforward_additive _
    exact Functor.instAdditiveComp _ _
  have : PreservesFiniteLimits Ψ := by
    have : PreservesFiniteLimits
        (SheafOfModules.overFunctor.{u} (ringStructureSheafCore B S hS p hp .fppf) x) :=
      Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteLimits _
    exact comp_preservesFiniteLimits _ _
  let e : Ψ.obj (SheafOfModules.unit _) ≅ SheafOfModules.unit _ :=
    (L.unitIso.app (SheafOfModules.unit _)).symm
  let Q := SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
    (ringStructureSheafCore B S hS p hp .fppf)
  let Q' := SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
    (BigFppfOver.structureSheaf B (baseScheme B S hS p x)
        (contains_baseScheme B S hS p x))
  have hι : Q.ι.Additive := ⟨rfl⟩
  have hι' : Q'.ι.Additive := ⟨rfl⟩
  let O : Q.FullSubcategory := ⟨SheafOfModules.unit _, inferInstance⟩
  have hm : Mono (2 • 𝟙 O) := by
    refine ⟨fun {Z} g h hgh => ?_⟩
    have hZ : Q' (Ψ.obj Z.obj) :=
      (isQuasicoherentOnSite_iff_forall_objectInverseImage B S hS p hp Z.obj).1 Z.property x
    let g' : (⟨Ψ.obj Z.obj, hZ⟩ : Q'.FullSubcategory) ⟶ ⟨SheafOfModules.unit _, inferInstance⟩ :=
      ObjectProperty.homMk (Ψ.map g.hom ≫ e.hom)
    let h' : (⟨Ψ.obj Z.obj, hZ⟩ : Q'.FullSubcategory) ⟶ ⟨SheafOfModules.unit _, inferInstance⟩ :=
      ObjectProperty.homMk (Ψ.map h.hom ≫ e.hom)
    have : g' = h' := by
      rw [← cancel_mono (2 • 𝟙 _)]
      apply Q'.ι.map_injective
      have := congrArg (fun k => Ψ.map (Q.ι.map k)) hgh
      simp only [Functor.map_comp, Functor.map_nsmul, CategoryTheory.Functor.map_id] at this
      have h2 := congrArg (fun k => k ≫ e.hom) this
      simp only [Category.assoc] at h2
      simp only [Functor.map_nsmul, Preadditive.comp_nsmul, Category.comp_id]
      set_option synthInstance.maxHeartbeats 400000 in
      simpa [g', h', Preadditive.comp_nsmul, Preadditive.nsmul_comp] using h2
    apply ObjectProperty.hom_ext
    apply Ψ.map_injective
    have h3 := congrArg (fun k => k.hom ≫ e.inv) this
    simpa only [g', h', ObjectProperty.homMk_hom, Category.assoc, Iso.hom_inv_id,
      Category.comp_id] using h3
  have h1 : Mono (Q.ι.map (2 • 𝟙 O)) := inferInstance
  rw [Functor.map_nsmul, CategoryTheory.Functor.map_id] at h1
  have h2 : Mono (Ψ.map (2 • 𝟙 (SheafOfModules.unit (ringStructureSheafCore B S hS p hp .fppf)))) :=
    Ψ.map_mono _
  rw [Functor.map_nsmul, CategoryTheory.Functor.map_id] at h2
  apply hnot
  rw [nsmul_id_eq_inv_comp_nsmul_id_comp_hom e]
  haveI : Mono e.inv := IsIso.mono_of_iso _
  haveI : Mono e.hom := IsIso.mono_of_iso _
  exact mono_comp _ _
end AlgebraicGeometry.FibredSite

namespace AlgebraicGeometry.AssociatedModuleNotExact

variable (B : BigFppfSite.{u})

/-- **`2 : 𝒪 → 𝒪` is a monomorphism of the quasi-coherent modules on `(Sch/Spec(ℤ))_fppf`.**  The
category of those is equivalent to `QCoh(𝒪_{Spec(ℤ)})` by `𝓕 ↦ 𝓕^a` (Stacks 03DX), which carries
`2 : 𝒪_S → 𝒪_S` to `2 : 𝒪 → 𝒪`, and there it is a monomorphism. -/
theorem mono_two_nsmul_unitQuasicoherentOnSite :
    Mono (2 • 𝟙 (⟨SheafOfModules.unit (bigStructureSheaf B .fppf), inferInstance⟩ :
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        (bigStructureSheaf B .fppf)).FullSubcategory)) := by
  let E := BigFppfOver.baseAssociatedModuleEquivalenceOnSite_fppf B specInt.{u} (contains_specInt B)
  let Q' := SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u} (bigStructureSheaf B .fppf)
  have hι' : Q'.ι.Additive := ⟨rfl⟩
  have := additive_associatedModule B .fppf
  have := mono_two_nsmul_unitQcoh.{u}
  let e0 : E.functor.obj unitQcoh.{u} ≅
      ⟨SheafOfModules.unit (bigStructureSheaf B .fppf), inferInstance⟩ :=
    Q'.isoMk (associatedModuleUnitIso B .fppf)
  have h : 2 • 𝟙 (⟨SheafOfModules.unit (bigStructureSheaf B .fppf), inferInstance⟩ :
      Q'.FullSubcategory) =
      e0.inv ≫ E.functor.map (2 • 𝟙 unitQcoh.{u}) ≫ e0.hom := by
    apply Q'.ι.map_injective
    have hE : Q'.ι.map (E.functor.map (2 • 𝟙 unitQcoh.{u})) =
        (associatedModule B .fppf).map (2 • 𝟙 unitModule.{u}) :=
      congrArg (associatedModule B .fppf).map iota_map_two_nsmul.{u}
    simp only [Functor.map_comp, hE, Functor.map_nsmul, CategoryTheory.Functor.map_id]
    show _ = (associatedModuleUnitIso B .fppf).inv ≫
      (associatedModule B .fppf).map (2 • 𝟙 unitModule.{u}) ≫
      (associatedModuleUnitIso B .fppf).hom
    rw [Functor.map_nsmul, CategoryTheory.Functor.map_id]
    exact nsmul_id_eq_inv_comp_nsmul_id_comp_hom _ _
  rw [h]
  haveI : Mono e0.inv := IsIso.mono_of_iso _
  haveI : Mono e0.hom := IsIso.mono_of_iso _
  haveI : Mono (E.functor.map (2 • 𝟙 unitQcoh.{u})) := E.functor.map_mono _
  exact mono_comp _ _

end AlgebraicGeometry.AssociatedModuleNotExact

namespace AlgebraicGeometry.Stack

open AssociatedModuleNotExact

variable (B : BigFppfSite.{u})

/-- `Spec(ℤ)` over itself, the final object of `(Sch/Spec(ℤ))_fppf`. -/
abbrev specIntOver : BigFppfOver B specInt.{u} (contains_specInt B) := Over.mk (𝟙 _)

/-- **`Spec(ℤ)` as an algebraic stack over itself**: the category fibred in groupoids represented
by the final object of `(Sch/Spec(ℤ))_fppf`, which is an algebraic stack by Stacks 04X5. -/
def specIntStack : AlgebraicStacks.{u, w} B specInt.{u} (contains_specInt B) :=
  ⟨schemeFibredCategory B _ _ (specIntOver B), isAlgebraicStack_schemeFibredCategory B _ _ _⟩

/-- **The inclusion `QCoh(𝒪_𝒳) → Mod(𝒪_𝒳)` is not left exact for `𝒳 = Spec(ℤ)`**, on every big
fppf site.  This is the example of Descent, Lemma 06VE (6), read on the algebraic stack
`AlgebraicGeometry.Stack.specIntStack`. -/
theorem not_preservesFiniteLimits_quasicoherentInclusion_specIntStack :
    ¬ PreservesFiniteLimits
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        (FibredSite.ringStructureSheafCore B specInt.{u} (contains_specInt B)
          (specIntStack.{w} B).val.val.p (specIntStack.{w} B).val.isFiberedInGroupoids
          .fppf)).ι :=
  FibredSite.not_preservesFiniteLimits_quasicoherentInclusion_of_isTerminal B _ _ _ _
    (x := (Over.mk (𝟙 (specIntOver B)) : Over (specIntOver B))) Over.mkIdTerminal
    (mono_two_nsmul_unitQuasicoherentOnSite B) (not_mono_two_nsmul_unitBig B .fppf)

/-- **Stacks 06WV (3).**  The inclusion `QCoh(𝒪_𝒳) → Mod(𝒪_𝒳)` is right exact for every
algebraic stack `𝒳`, but it is **not** exact in general: on every big fppf site there is an
algebraic stack, namely `Spec(ℤ)`, for which it is not exact. -/
@[stacks 06WV "part (3): the inclusion QCoh(𝒪_𝒳) → Mod(𝒪_𝒳) is right exact, and on every big \
  site the algebraic stack Spec(ℤ) is one for which it is not exact"]
theorem quasicoherentInclusion_rightExact_not_exact :
    (∀ (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
        (𝒳 : AlgebraicStacks.{u, w} B S hS),
        PreservesFiniteColimits
          (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
            (FibredSite.ringStructureSheafCore B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
              .fppf)).ι) ∧
      ∀ B : BigFppfSite.{u}, ∃ 𝒳 : AlgebraicStacks.{u, w} B specInt.{u} (contains_specInt B),
        ¬ (PreservesFiniteLimits
            (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
              (FibredSite.ringStructureSheafCore B specInt.{u} (contains_specInt B) 𝒳.val.val.p
                𝒳.val.isFiberedInGroupoids .fppf)).ι ∧
          PreservesFiniteColimits
            (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
              (FibredSite.ringStructureSheafCore B specInt.{u} (contains_specInt B) 𝒳.val.val.p
                𝒳.val.isFiberedInGroupoids .fppf)).ι) :=
  ⟨fun _ _ _ 𝒳 => preservesFiniteColimits_quasicoherentInclusion 𝒳,
    fun B => ⟨specIntStack B, fun h =>
      not_preservesFiniteLimits_quasicoherentInclusion_specIntStack.{w} B h.1⟩⟩

end AlgebraicGeometry.Stack

end
