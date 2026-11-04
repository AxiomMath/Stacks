module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.WeilIIDimensionStepInputs
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-!
# Realizability of the top higher direct image of a family of smooth affine curves

In the induction step of the weight bound of Weil II
([Tag 03VH](https://stacks.math.columbia.edu/tag/03VH); Deligne, Weil II 3.3) the base `W` is
fibred by smooth affine curves `g : U ⟶ W`, and the `ι`-realizability of the higher direct images
`Rʳ g_! G` of a lisse realizable `G` is reached from the trace formula on the fibres, which ties
`R⁰`, `R¹` and `R²` together, once `R⁰` (zero on affine curves) and `R²` are known to be
realizable.  The top one, `R² g_! G`, is the family of the coinvariants `(G_ū)_{π₁(U_w̄)}(-1)`
of the fibres (Tag 03VN): a quotient of a stalk of `G`, which is realizable with witness the
kernel of `s⁻¹ G ⟶ R² g_! G (1)` along a multisection `s`.  That statement concerns the genuine
`R² g_!` and is stated here, for a family `R` in the role of `Rʳ g_!`, as one proposition.

## Main definitions

* `Stacks.EtaleCohomology.LAdicSheaf.HigherDirectImageTopRealizableInput`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.SmallEtale

universe u

namespace Stacks.EtaleCohomology

variable {B : BigEtaleSite.{u}} {ℓ : ℕ} [Fact ℓ.Prime]
  [∀ (n : ℕ) (S T : B.Scheme) (g : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B g).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.1 S.property)
      (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
  [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
    HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [∀ (n : ℕ) (T : B.Scheme), HasWeakSheafify (SmallEtale.topology B T.1 T.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]

/-- **Realizability of `R² g_! G` for a family of smooth affine curves** (Weil II 1.5 and 3.3,
Tag 03VN in families): for `g : U ⟶ W` smooth of relative dimension one and affine over a finite
field `k` of characteristic `p ≠ ℓ`, with `W` reduced and irreducible and `U` nonempty, and `G`
lisse and `ι`-realizable on `U`, there is a nonempty open `V ⊆ W` such that over every open
`V' ⊆ V`, with `g' : U' ⟶ V'` the base change of `g`, the sheaf `R² g'_! (G|_{U'})` is
`ι`-realizable. -/
def LAdicSheaf.HigherDirectImageTopRealizableInput (R : LAdicSheaf.HigherDirectImageFamily B ℓ) :
    Prop :=
  ∀ (k : Type u) [Field k] [Fintype k] (p n : ℕ) [Fact p.Prime] [CharP k p],
    Fintype.card k = p ^ n → ℓ ≠ p → ∀ (ι : ℚ_[ℓ] →+* ℂ) (U W : B.Scheme)
    [IsNoetherian U.1] [IsNoetherian W.1] [IsReduced W.1] (g : U ⟶ W)
    [LocallyOfFiniteType (B.inclusion.map g)]
    [QuasiCompact (B.inclusion.map g)] [IsSeparated (B.inclusion.map g)]
    [SmoothOfRelativeDimension 1 (B.inclusion.map g)] [IsAffineHom (B.inclusion.map g)]
    (fW : W.1 ⟶ Spec (.of k)) [LocallyOfFiniteType fW] [QuasiCompact fW] [IsSeparated fW]
    (G : LAdicSheaf.{u, u + 1} B U ℓ), G.IsLisse →
    LAdicSheaf.IsIotaRealizable B U ℓ (B.inclusion.map g ≫ fW) G ι →
    IrreducibleSpace W.1 → Nonempty U.1 →
    ∃ (V : B.Scheme) (jV : V ⟶ W), IsOpenImmersion (B.inclusion.map jV) ∧
      Nonempty V.1 ∧ ∀ (V' U' : B.Scheme) [IsNoetherian V'.1] [IsNoetherian U'.1] (jV' : V' ⟶ V)
        (jU : U' ⟶ U) (g' : U' ⟶ V') [LocallyOfFiniteType (B.inclusion.map g')]
        [QuasiCompact (B.inclusion.map g')] [IsSeparated (B.inclusion.map g')]
        (jg' : CompactificationOf (Over.mk (B.inclusion.map g'))),
        IsOpenImmersion (B.inclusion.map jV') →
        IsPullback (B.inclusion.map jU) (B.inclusion.map g') (B.inclusion.map g)
          (B.inclusion.map (jV' ≫ jV)) →
        ∀ (fV' : V'.1 ⟶ Spec (.of k)) [LocallyOfFiniteType fV'],
          LAdicSheaf.IsIotaRealizable B V' ℓ fV' (R g' jg' (LAdicSheaf.inverseImage jU G) 2) ι

end Stacks.EtaleCohomology

end
