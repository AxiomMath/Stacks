module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.ConstantTwistedFrobeniusFix
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.ExtensionByZeroSelfMapTwist
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.ExtensionByZeroInverseImageCounit
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.SelfMapOpenClosedTrace

/-!
# Step 9: the twisted Frobenius on a constant sheaf is the self-map twist

Let `Y` be a scheme over a finite field `k`, `σ : Y ⟶ Y` a morphism over `k`, `M` a module and
`φ = σ̄ ≫ π̄` the twisted Frobenius of `Y_k̄`. Through the identification
`Φ : (M_Y)|_{Y_k̄} ≅ M_{Y_k̄} ≅ f^{-1} M_{k̄}` (`f : Y_k̄ ⟶ Spec k̄`), the twisted Frobenius twist
of the constant sheaf `M_Y` with its canonical map `M_Y ⟶ σ_* M_Y` is the self-map twist of `φ`
over `Spec k̄`; the same holds for `j_! j^{-1} M_Y`, for an open immersion `j : V ⟶ Y` with
`σ⁻¹ V = V`, through the counit of extension by zero. This is comparison (i) of Step 9 of the proof
of [Stacks, Tag 03UG], read without transport to `M_{Y_k̄}`.

## Main definitions

* `Stacks.EtaleCohomology.fieldBaseChangeConstantIso`: `Φ`.
* `Stacks.EtaleCohomology.fieldBaseChangeExtensionByZeroConstantIso`: the identification of
  `(j_! j^{-1} M_Y)|_{Y_k̄}` with `j'_! j'^{-1} f^{-1} M_{k̄}`.

## Main results

* `Stacks.EtaleCohomology.twistedFrobeniusTwist_constant_comp_map_eq`.
* `Stacks.EtaleCohomology.twistedFrobeniusTwist_extensionByZero_comp_counit`.

## References

* [Stacks Project, Tag 03UG](https://stacks.math.columbia.edu/tag/03UG), Step 9.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme Stacks.Frobenius

universe u r

namespace Stacks.EtaleCohomology

section ConstantFix

variable (Λ : Type r) [Ring Λ] (M : ModuleCat.{max (u + 1) r} Λ) {k : Type u} [Field k]
  [Fintype k] (Y : Over (Spec (.of k))) (σ : Y ⟶ Y) (kbar : Type u) [Field kbar] [Algebra k kbar]
  (p q : ℕ) [Fact p.Prime] [CharP k p] (hcard : Fintype.card k = p ^ q)

/-- The identification `(M_Y)|_{Y_k̄} ≅ M_{Y_k̄} ≅ f^{-1} M_{k̄}` of the two pulled back constant
sheaves on `Y_k̄`, for `f : Y_k̄ ⟶ Spec k̄` the structure morphism. -/
abbrev fieldBaseChangeConstantIso :
    (etaleModuleInverseImage.{u, r} Λ (fieldBaseChangeProj Y kbar)).obj
        (etaleModuleConstantSheaf Λ M Y.left) ≅
      (etaleModuleInverseImage.{u, r} Λ (pullback.snd Y.hom (specAlgebraMap k kbar))).obj
        (etaleModuleConstantSheaf Λ M (Spec (.of kbar))) :=
  inverseImageEtaleModuleConstantSheafIso.{u, r} Λ M (fieldBaseChangeProj Y kbar) ≪≫
    (inverseImageEtaleModuleConstantSheafIso.{u, r} Λ M
      (pullback.snd Y.hom (specAlgebraMap k kbar))).symm

/-- **The twisted Frobenius twist of a constant sheaf is the self-map twist**, through
`Stacks.EtaleCohomology.fieldBaseChangeConstantIso`. -/
theorem twistedFrobeniusTwist_constant_comp_map_eq :
    twistedFrobeniusTwist.{u, r} Λ Y σ kbar p q hcard (etaleModuleConstantSheaf Λ M Y.left)
        (constantSelfMapTwist Λ M σ.left) ≫
      (etaleModuleDirectImage.{u, r} Λ (twistedGeometricFrobenius Y σ kbar p q hcard)).map
        (fieldBaseChangeConstantIso Λ M Y kbar).hom =
    (fieldBaseChangeConstantIso Λ M Y kbar).hom ≫
      (selfMapTwist.{u, r} Λ (pullback.snd Y.hom (specAlgebraMap k kbar))
        (twistedGeometricFrobenius Y σ kbar p q hcard)
        (twistedGeometricFrobenius_comp_toBase Y σ kbar p q hcard)).app
          (etaleModuleConstantSheaf Λ M (Spec (.of kbar))) := by
  have T := transportedConstantTwist_twistedFrobeniusTwist Λ M Y σ kbar p q hcard
  simp only [transportedConstantTwist] at T
  rw [← cancel_epi
    (inverseImageEtaleModuleConstantSheafIso.{u, r} Λ M (fieldBaseChangeProj Y kbar)).inv]
  simp only [fieldBaseChangeConstantIso, Iso.trans_hom, Iso.symm_hom, Functor.map_comp]
  calc _ = ((inverseImageEtaleModuleConstantSheafIso.{u, r} Λ M (fieldBaseChangeProj Y kbar)).inv ≫
        twistedFrobeniusTwist.{u, r} Λ Y σ kbar p q hcard (etaleModuleConstantSheaf Λ M Y.left)
          (constantSelfMapTwist Λ M σ.left) ≫
        (etaleModuleDirectImage.{u, r} Λ (twistedGeometricFrobenius Y σ kbar p q hcard)).map
          (inverseImageEtaleModuleConstantSheafIso.{u, r} Λ M (fieldBaseChangeProj Y kbar)).hom) ≫
        (etaleModuleDirectImage.{u, r} Λ (twistedGeometricFrobenius Y σ kbar p q hcard)).map
          (inverseImageEtaleModuleConstantSheafIso.{u, r} Λ M
            (pullback.snd Y.hom (specAlgebraMap k kbar))).inv := by
        simp only [Category.assoc]
    _ = _ := by
        rw [T]
        simp only [Category.assoc, ← Functor.map_comp, Iso.hom_inv_id,
          CategoryTheory.Functor.map_id, Category.comp_id, Iso.inv_hom_id_assoc]

end ConstantFix

section OpenFix

variable (Λ : Type) [CommRing Λ] (M : ModuleCat.{u + 1} Λ) {k : Type u} [Field k]
  [Fintype k] (Y : Over (Spec (.of k))) (σ : Y ⟶ Y) (kbar : Type u) [Field kbar] [Algebra k kbar]
  (p q : ℕ) [Fact p.Prime] [CharP k p] (hcard : Fintype.card k = p ^ q)
  {V W : Scheme.{u}} (jV : V ⟶ Y.left) [IsOpenImmersion jV] (iW : W ⟶ Y.left) [IsClosedImmersion iW]
  (hij : Set.range jV.base = (Set.range iW.base)ᶜ) (σV : V ⟶ V) [IsIntegralHom σ.left]
  (sq : IsPullback σV jV jV σ.left)
  {V' W' : Scheme.{u}} (j' : V' ⟶ fieldBaseChange Y kbar) [IsOpenImmersion j']
  (i' : W' ⟶ fieldBaseChange Y kbar) [IsClosedImmersion i']
  (hij' : Set.range j'.base = (Set.range i'.base)ᶜ)
  (gW : W' ⟶ W) (hW : i' ≫ fieldBaseChangeProj Y kbar = gW ≫ iW)
  (gV : V' ⟶ V) (hV : j' ≫ fieldBaseChangeProj Y kbar = gV ≫ jV)

/-- The identification of the restriction to `Y_k̄` of `j_! j^{-1} M_Y` with
`j'_! j'^{-1} f^{-1} M_{k̄}`, over the identification of the constant sheaves. -/
def fieldBaseChangeExtensionByZeroConstantIso :
    (etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj Y kbar)).obj
        ((etaleModuleExtensionByZero.{u, 0} Λ jV).obj
          ((etaleModuleRestriction.{u, 0} Λ jV).obj (etaleModuleConstantSheaf Λ M Y.left))) ≅
      (etaleModuleExtensionByZero.{u, 0} Λ j').obj ((etaleModuleRestriction.{u, 0} Λ j').obj
        ((etaleModuleInverseImage.{u, 0} Λ (pullback.snd Y.hom (specAlgebraMap k kbar))).obj
          (etaleModuleConstantSheaf Λ M (Spec (.of kbar))))) :=
  inverseImageExtensionByZeroCounitIso Λ (fieldBaseChangeProj Y kbar) iW jV hij i' j' hij' gW hW gV
      hV (etaleModuleConstantSheaf Λ M Y.left) ≪≫
    (etaleModuleExtensionByZero.{u, 0} Λ j').mapIso ((etaleModuleRestriction.{u, 0} Λ j').mapIso
      (fieldBaseChangeConstantIso Λ M Y kbar))

omit [Fintype k] in
/-- The identification followed by the counit is the restriction of the counit, followed by the
identification of the constant sheaves. -/
lemma fieldBaseChangeExtensionByZeroConstantIso_hom_comp_counit :
    (fieldBaseChangeExtensionByZeroConstantIso Λ M Y kbar jV iW hij j' i' hij' gW hW gV hV).hom ≫
        (etaleModuleExtensionByZeroAdj.{u, 0} Λ j').counit.app
          ((etaleModuleInverseImage.{u, 0} Λ (pullback.snd Y.hom (specAlgebraMap k kbar))).obj
            (etaleModuleConstantSheaf Λ M (Spec (.of kbar)))) =
      (etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj Y kbar)).map
          ((etaleModuleExtensionByZeroAdj.{u, 0} Λ jV).counit.app
            (etaleModuleConstantSheaf Λ M Y.left)) ≫
        (fieldBaseChangeConstantIso Λ M Y kbar).hom := by
  have hc := (etaleModuleExtensionByZeroAdj.{u, 0} Λ j').counit.naturality
    (fieldBaseChangeConstantIso Λ M Y kbar).hom
  dsimp only [Functor.comp_obj, Functor.comp_map, Functor.id_obj, Functor.id_map] at hc
  rw [fieldBaseChangeExtensionByZeroConstantIso, Iso.trans_hom, Functor.mapIso_hom,
    Functor.mapIso_hom, Category.assoc, hc, ← Category.assoc,
    inverseImageExtensionByZeroCounitIso_hom_comp_counit]

include sq in
/-- **The twisted Frobenius twist of `j_! j^{-1} M_Y` is the self-map twist through the
counit.**  With `ε` the extension by zero of the canonical map `M_Y ⟶ σ_* M_Y`, the twisted
Frobenius twist of `(j_! j^{-1} M_Y)|_{Y_k̄}`, followed by `φ_*` of the identification with
`j'_! j'^{-1} f^{-1} M_{k̄}` and of the counit, is the identification and the counit followed by
the self-map twist of `f^{-1} M_{k̄}`. -/
theorem twistedFrobeniusTwist_extensionByZero_comp_counit :
    twistedFrobeniusTwist.{u, 0} Λ Y σ kbar p q hcard
        ((etaleModuleExtensionByZero.{u, 0} Λ jV).obj
          ((etaleModuleRestriction.{u, 0} Λ jV).obj (etaleModuleConstantSheaf Λ M Y.left)))
        (extensionByZeroTwist Λ jV σV σ.left sq (etaleModuleConstantSheaf Λ M Y.left)
          (constantSelfMapTwist Λ M σ.left)) ≫
      (etaleModuleDirectImage.{u, 0} Λ (twistedGeometricFrobenius Y σ kbar p q hcard)).map
        ((fieldBaseChangeExtensionByZeroConstantIso Λ M Y kbar jV iW hij j' i' hij' gW hW gV
            hV).hom ≫
          (etaleModuleExtensionByZeroAdj.{u, 0} Λ j').counit.app
            ((etaleModuleInverseImage.{u, 0} Λ (pullback.snd Y.hom (specAlgebraMap k kbar))).obj
              (etaleModuleConstantSheaf Λ M (Spec (.of kbar))))) =
    ((fieldBaseChangeExtensionByZeroConstantIso Λ M Y kbar jV iW hij j' i' hij' gW hW gV hV).hom ≫
        (etaleModuleExtensionByZeroAdj.{u, 0} Λ j').counit.app
          ((etaleModuleInverseImage.{u, 0} Λ (pullback.snd Y.hom (specAlgebraMap k kbar))).obj
            (etaleModuleConstantSheaf Λ M (Spec (.of kbar))))) ≫
      (selfMapTwist.{u, 0} Λ (pullback.snd Y.hom (specAlgebraMap k kbar))
        (twistedGeometricFrobenius Y σ kbar p q hcard)
        (twistedGeometricFrobenius_comp_toBase Y σ kbar p q hcard)).app
          (etaleModuleConstantSheaf Λ M (Spec (.of kbar))) := by
  have hnat := twistedFrobeniusTwist_naturality Λ Y σ kbar p q hcard
    (C := (etaleModuleExtensionByZero.{u, 0} Λ jV).obj
      ((etaleModuleRestriction.{u, 0} Λ jV).obj (etaleModuleConstantSheaf Λ M Y.left)))
    (C' := etaleModuleConstantSheaf Λ M Y.left) _ (constantSelfMapTwist Λ M σ.left)
    ((etaleModuleExtensionByZeroAdj.{u, 0} Λ jV).counit.app (etaleModuleConstantSheaf Λ M Y.left))
    (extensionByZeroTwist_comp_counit Λ jV σV σ.left sq _ _).symm
  rw [fieldBaseChangeExtensionByZeroConstantIso_hom_comp_counit, Functor.map_comp,
    ← Category.assoc, ← hnat, Category.assoc, twistedFrobeniusTwist_constant_comp_map_eq,
    Category.assoc]

end OpenFix

end Stacks.EtaleCohomology

end
