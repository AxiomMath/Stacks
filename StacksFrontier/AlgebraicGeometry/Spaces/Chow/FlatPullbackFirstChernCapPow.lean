module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.FirstChernCapPowerRationalEquivalence
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.FlatPullbackFirstChernCapCanonical
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ProjectiveBundleFormulaCanonical

/-!
# Flat pullback against the powers of the cap product, and isomorphic invertible modules

Two consequences of Stacks 0EQR and Stacks 0EQJ for the `s`-fold cap product
`c₁(ℒ)^s ∩ -` (`AlgebraicGeometry.Space.firstChernCapPowCycleMap`), in the Chow groups of
Stacks 0EQ6 at the canonical embeddings of Stacks 0ENK:

* `f^*(c₁(ℒ)^s ∩ α) = c₁(f^*ℒ)^s ∩ f^*α` for `f` flat
  (`chowClassCanonical_flatPullbackMap_firstChernCapPowCycleMap_modulePullback`),
  the base's `chowClassCanonical_flatPullbackMap_firstChernCapPowCycleMap` at `ℒ' = f^*ℒ`;
* the powers depend on `ℒ` only up to isomorphism
  (`AlgebraicGeometry.Space.chowClassCanonical_firstChernCapPowCycleMap_congr_iso`).

## References

* [Stacks Project, Tag 0EQR](https://stacks.math.columbia.edu/tag/0EQR)
* [Stacks Project, Tag 0EQJ](https://stacks.math.columbia.edu/tag/0EQJ)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

section Iso

variable (D : BaseSpaceDimensionSituation.{u})
    {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u} (sX : X ⟶ D.space)
    (hX : D.IsGood sX)

/-- **The powers of the cap product depend on the invertible module only up to isomorphism**, in
the Chow group. -/
theorem chowClassCanonical_firstChernCapPowCycleMap_congr_iso
    (M M' : Modules.{u, u} D.site D.base D.base_mem X hX.1)
    (hM : IsInvertibleModule (⟨X, hX.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) M)
    (hM' : IsInvertibleModule (⟨X, hX.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) M')
    (e : M ≅ M') (s : ℕ) :
    ∀ (m : ℤ) (α : CycleGroup D sX (m + s)),
      chowClassCanonical.{u + 1} D sX hX m (firstChernCapPowCycleMap D sX hX M hM s m α) =
        chowClassCanonical.{u + 1} D sX hX m (firstChernCapPowCycleMap D sX hX M' hM' s m α) := by
  induction s with
  | zero => intro m α; rfl
  | succ s ih =>
    intro m α
    simp only [firstChernCapPowCycleMap, AddMonoidHom.coe_comp, Function.comp_apply]
    change canonicalFirstChernCapCanonical.{u + 1} D sX hX M hM m _ =
      canonicalFirstChernCapCanonical.{u + 1} D sX hX M' hM' m _
    rw [← canonicalFirstChernCapCanonical_congr_iso hX M M' hM hM' e,
      ← canonicalFirstChernCapCanonicalChowMap_chowClassCanonical,
      ← canonicalFirstChernCapCanonicalChowMap_chowClassCanonical, ih]

end Iso

section Flat

variable (D : BaseSpaceDimensionSituation.{u})
    {X Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (sX : X ⟶ D.space) (hX : D.IsGood sX) (sY : Y ⟶ D.space) (hY : D.IsGood sY)
    (f : X ⟶ Y) (hbase : f ≫ sY = sX) (r : ℕ) (hflat : IsFlat D.site D.base D.base_mem f)
    (hr : HasRelativeDimension r D.site D.base D.base_mem f)
    (L : Modules.{u, u} D.site D.base D.base_mem Y hY.1)
    (hL : IsInvertibleModule (⟨Y, hY.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) L)

/-- **Stacks 0EQR for the `s`-fold cap product**: `f^*(c₁(ℒ)^s ∩ α) = c₁(f^*ℒ)^s ∩ f^*α` in
`CH_{m'}(X)`, `m' = m + r`, for `α ∈ Z_{m+s}(Y)`: the base's
`AlgebraicGeometry.Space.chowClassCanonical_flatPullbackMap_firstChernCapPowCycleMap` at
`ℒ' = f^*ℒ`. -/
theorem chowClassCanonical_flatPullbackMap_firstChernCapPowCycleMap_modulePullback (s : ℕ) :
    ∀ (m m' : ℤ) (h : m + (r : ℤ) = m') (h' : m + s + (r : ℤ) = m' + s)
      (α : CycleGroup D sY (m + s)),
      chowClassCanonical.{u + 1} D sX hX m'
          (flatPullbackMap D sX hX sY hY f hbase r hflat hr m m' h
            (firstChernCapPowCycleMap D sY hY L hL s m α)) =
        chowClassCanonical.{u + 1} D sX hX m'
          (firstChernCapPowCycleMap D sX hX
            ((modulePullback D.site D.base D.base_mem
              (ObjectProperty.homMk f : (⟨X, hX.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) ⟶
                ⟨Y, hY.1⟩)).obj L)
            (modulePullbackInvertible
              (ObjectProperty.homMk f : (⟨X, hX.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) ⟶
                ⟨Y, hY.1⟩) L hL) s m'
            (flatPullbackMap D sX hX sY hY f hbase r hflat hr (m + s) (m' + s) h' α)) :=
  fun m m' h h' α => chowClassCanonical_flatPullbackMap_firstChernCapPowCycleMap
    D sX hX sY hY f hbase r hflat hr L hL _ _ (Iso.refl _) s m m' h h' α

end Flat

end AlgebraicGeometry.Space

end
