module

public import StacksFrontier.AlgebraicGeometry.Divisors.InvertibleSheafPullback
public import StacksFrontier.AlgebraicGeometry.Divisors.TensorCanonicalSection
public import StacksFrontier.AlgebraicGeometry.Descent.EffectiveEpi.QuasicoherentSections
public import StacksFrontier.AlgebraicGeometry.ClosedCoverGlue.Sections

/-!
# The canonical section of `𝒪(D)` is compatible with pullback, as a morphism

Let `f : X ⟶ Y` be a morphism of schemes and `D` an effective Cartier divisor on `Y` whose pullback
is defined. [Stacks, Tag 0C4U] identifies `f^*𝒪_Y(D)` with `𝒪_X(f^{-1}D)`, carrying the pulled-back
canonical section to the canonical section, as global sections
(`Stacks.Divisors.invertibleSheafPullbackIso_canonicalSection`). This file states the same thing
for the canonical section read as a morphism `𝒪 ⟶ 𝒪(D)`: the pullback of
`Stacks.Divisors.canonicalSectionHom D`, followed by the identification, is the canonical
morphism `f^*𝒪_Y ⟶ 𝒪_X` followed by `Stacks.Divisors.canonicalSectionHom (D.comap f)`.

## Main results

* `Stacks.Divisors.pullback_canonicalSectionHom`: the compatibility above.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite AlgebraicGeometry

universe u

namespace Stacks.Divisors

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (D : Y.IdealSheafData) [IsEffectiveCartierDivisor D]
  [IsPullbackDefined f D]

/-- The value at `1` of the canonical section, read as a morphism, is the canonical section. -/
theorem canonicalSectionHom_app_one {Z : Scheme.{u}} (E : Z.IdealSheafData) (V : Z.Opens) :
    (canonicalSectionHom E).val.app (op V) (1 : Γ(Z, V)) = (canonicalSection' E).val (op V) :=
  congrArg (fun σ => σ.val (op V)) ((invertibleSheaf' E).unitHomEquiv.apply_symm_apply
    (canonicalSection' E))

/-- Two morphisms out of the structure sheaf agree as soon as they agree at `1` on the whole
space. -/
theorem unit_hom_ext {Z : Scheme.{u}} {M : Z.Modules}
    {φ ψ : SheafOfModules.unit Z.ringCatSheaf ⟶ M}
    (h : φ.val.app (op ⊤) (1 : Γ(Z, ⊤)) = ψ.val.app (op ⊤) (1 : Γ(Z, ⊤))) : φ = ψ := by
  apply M.unitHomEquiv.injective
  refine Subtype.ext (funext fun U => ?_)
  rw [← (M.unitHomEquiv φ).2 (homOfLE (le_top : U.unop ≤ ⊤)).op,
    ← (M.unitHomEquiv ψ).2 (homOfLE (le_top : U.unop ≤ ⊤)).op]
  exact congrArg _ h

/-- **The canonical section of `𝒪(D)`, as a morphism, is compatible with pullback.** -/
theorem pullback_canonicalSectionHom :
    (Scheme.Modules.pullback f).map (canonicalSectionHom D) ≫
        (invertibleSheafPullbackIso f D).hom =
      SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom ≫
        canonicalSectionHom (D.comap f) := by
  set adj := Scheme.Modules.pullbackPushforwardAdjunction f
  apply (adj.homEquiv _ _).injective
  have h1 : adj.homEquiv _ _ ((Scheme.Modules.pullback f).map (canonicalSectionHom D) ≫
      (invertibleSheafPullbackIso f D).hom) =
        canonicalSectionHom D ≫ adj.unit.app _ ≫
          (Scheme.Modules.pushforward f).map (invertibleSheafPullbackIso f D).hom :=
    (adj.homEquiv_naturality_left _ _).trans (congrArg (canonicalSectionHom D ≫ ·)
      (adj.homEquiv_unit _ _ _))
  have h2 : adj.homEquiv _ _ (SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom ≫
      canonicalSectionHom (D.comap f)) =
        SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom ≫
          (Scheme.Modules.pushforward f).map (canonicalSectionHom (D.comap f)) :=
    (adj.homEquiv_naturality_right _ _).trans (congrArg (· ≫ _)
      (SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit _))
  refine h1.trans (Eq.trans ?_ h2.symm)
  refine unit_hom_ext ?_
  show Scheme.Modules.Hom.app (invertibleSheafPullbackIso f D).hom ⊤
      ((adj.unit.app (invertibleSheaf' D)).app ⊤
        ((canonicalSectionHom D).val.app (op ⊤) (1 : Γ(Y, ⊤)))) =
    (canonicalSectionHom (D.comap f)).val.app (op ⊤) (f.appTop.hom (1 : Γ(Y, ⊤)))
  rw [canonicalSectionHom_app_one, map_one, canonicalSectionHom_app_one,
    ← invertibleSheafPullbackIso_canonicalSection]
  congr 1
  show _ = ((Scheme.Modules.pullback f).obj (invertibleSheaf' D)).presheaf.map
    (𝟙 (op (⊤ : X.Opens))) (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app
      (invertibleSheaf' D)).app ⊤ ((canonicalSection' D).eval (op ⊤)))
  exact (Functor.map_id_apply _ _ _).symm

end Stacks.Divisors

end
