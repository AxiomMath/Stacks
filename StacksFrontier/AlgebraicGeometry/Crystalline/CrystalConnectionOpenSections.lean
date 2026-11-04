module

public import StacksFrontier.AlgebraicGeometry.Crystalline.FirstOrderAmbientSplitting
public import StacksFrontier.AlgebraicGeometry.Crystalline.SecondOrderThickeningScheme

/-!
# The canonical connection of [Stacks, Tag 07J6] on the sections over an open

Fix a global crystalline situation `(p, (S, I, γ), X)` of [Stacks, Tag 07MF], let `F` be a sheaf
of `𝒪_{X/S}`-modules on the big crystalline site and let `(U, T, δ)` be an object of `CRIS(X/S)`
with first-order universal thickening `(U, T', δ')` of [Stacks, Tag 07J2] and second-order
universal thickening `(U, T'', δ'')` of [Stacks, Remark 60.14.5, Tag 07J3].

[Stacks, Tag 07J6] builds its connection on `Γ(T, F_T)` and asserts it to be integrable "as a
section of the subsheaf `F_T ⊗ Ω²_{T/S,δ}`".  Both the identification of the target and the
integrability argument are statements about **sheaves** on `T`, so they are checked on the
sections over each open `W` of `T`, not only over the whole of `T`.  The restriction `F_T` of
[Stacks, Tag 07IQ] is `W ↦ F(U ∩ W, W, δ|_W)`, so the sections of `F_T` over `W` are the sections
of `F` over the restriction `(U ∩ W, W, δ|_W)` of the object to `W`; and since the projections
`p₀, p₁ : T' ⟶ T`, the diagonal `i : T ⟶ T'` and the six morphisms of [Stacks, Tag 07J3] are all
the identity on underlying topological spaces, the sections of `F_{T'}` and of `F_{T''}` over the
preimage of `W` are the sections over the restrictions of `(U, T', δ')` and `(U, T'', δ'')` to
that same open `W`.

This module gives the connection, the vanishing of its values along the diagonal and the
curvature identity on the sections over an arbitrary open `W` of `T`. Over `W = ⊤` these are the
corresponding statements over the whole ambient scheme.

## Main definitions

* `Crystalline.GlobalCrystallineSituation.firstOrderRestrictP₀`,
  `Crystalline.GlobalCrystallineSituation.firstOrderRestrictP₁` and
  `Crystalline.GlobalCrystallineSituation.firstOrderRestrictι` — the two projections and the
  diagonal of [Stacks, Tag 07J2], restricted over an open `W` of `T`, as morphisms of
  `CRIS(X/S)` between the restrictions of the objects to `W`.
* `Crystalline.GlobalCrystallineSituation.secondOrderRestrictQ₀` and its five siblings — the six
  morphisms of [Stacks, Tag 07J3], restricted over an open.
* `Crystalline.GlobalCrystallineSituation.crystalConnectionOpen` — **the connection of
  [Stacks, Tag 07J6] on the sections over an open**, `∇(s) = p₁^* s - p₀^* s`.

## Main results

* `Crystalline.GlobalCrystallineSituation.crystalConnectionOpen_restrict_ι` — its values are
  killed by restriction along the diagonal.
* `Crystalline.GlobalCrystallineSituation.crystalConnectionOpen_naturality` — the connection
  commutes with restriction to a smaller open, so the maps over the opens are the components of
  one morphism of presheaves of abelian groups.
* `Crystalline.GlobalCrystallineSituation.crystalConnectionOpen_cocycle` — **the curvature
  identity `q₀₁^* ∇(s) + q₁₂^* ∇(s) = q₀₂^* ∇(s)`** on the sections over an open, for every sheaf
  of `𝒪_{X/S}`-modules and every open.

## References

* [Stacks Project, Tag 07J6](https://stacks.math.columbia.edu/tag/07J6)
* [Stacks Project, Tag 07J2](https://stacks.math.columbia.edu/tag/07J2)
* [Stacks Project, Tag 07J3](https://stacks.math.columbia.edu/tag/07J3)
* [Stacks Project, Tag 07IQ](https://stacks.math.columbia.edu/tag/07IQ)
* [Stacks Project, Tag 07MF](https://stacks.math.columbia.edu/tag/07MF)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace

universe u

noncomputable section

namespace Crystalline.GlobalCrystallineSituation

variable {S : GlobalCrystallineSituation.{u}}

/-! ### The morphisms of the two universal thickenings, restricted over an open

All of `p₀`, `p₁`, `i` and the six morphisms of [Stacks, Tag 07J3] are the identity on underlying
topological spaces, so the preimage of an open `W` of `T` under each of them is `W` itself.  Each
restricted morphism is therefore a morphism between the restrictions to one and the same open, and
the abbreviations below record that type. -/

variable (A : Thickening S) (W : A.thickening.target.scheme.Opens)

/-- **The first projection `p₀ : T' ⟶ T` of [Stacks, Tag 07J2], restricted over an open `W` of
`T`.** -/
abbrev firstOrderRestrictP₀ :
    (firstOrderThickeningObject S A).restrictOpen W ⟶ A.restrictOpen W :=
  Thickening.restrictOpenMap (firstOrderThickeningSiteP₀ S A) W

/-- **The second projection `p₁ : T' ⟶ T` of [Stacks, Tag 07J2], restricted over an open.** -/
abbrev firstOrderRestrictP₁ :
    (firstOrderThickeningObject S A).restrictOpen W ⟶ A.restrictOpen W :=
  Thickening.restrictOpenMap (firstOrderThickeningSiteP₁ S A) W

/-- **The diagonal `i : T ⟶ T'` of [Stacks, Tag 07J2], restricted over an open.** -/
abbrev firstOrderRestrictι :
    A.restrictOpen W ⟶ (firstOrderThickeningObject S A).restrictOpen W :=
  Thickening.restrictOpenMap (firstOrderThickeningSiteι S A) W

/-- **The morphism `q₀ : T'' ⟶ T` of [Stacks, Tag 07J3], restricted over an open.** -/
abbrev secondOrderRestrictQ₀ :
    (secondOrderThickeningObject S A).restrictOpen W ⟶ A.restrictOpen W :=
  Thickening.restrictOpenMap (secondOrderThickeningSiteQ₀ S A) W

/-- **The morphism `q₁ : T'' ⟶ T` of [Stacks, Tag 07J3], restricted over an open.** -/
abbrev secondOrderRestrictQ₁ :
    (secondOrderThickeningObject S A).restrictOpen W ⟶ A.restrictOpen W :=
  Thickening.restrictOpenMap (secondOrderThickeningSiteQ₁ S A) W

/-- **The morphism `q₂ : T'' ⟶ T` of [Stacks, Tag 07J3], restricted over an open.** -/
abbrev secondOrderRestrictQ₂ :
    (secondOrderThickeningObject S A).restrictOpen W ⟶ A.restrictOpen W :=
  Thickening.restrictOpenMap (secondOrderThickeningSiteQ₂ S A) W

/-- **The morphism `q₀₁ : T'' ⟶ T'` of [Stacks, Tag 07J3], restricted over an open.** -/
abbrev secondOrderRestrictQ₀₁ :
    (secondOrderThickeningObject S A).restrictOpen W ⟶
      (firstOrderThickeningObject S A).restrictOpen W :=
  Thickening.restrictOpenMap (secondOrderThickeningSiteQ₀₁ S A) W

/-- **The morphism `q₁₂ : T'' ⟶ T'` of [Stacks, Tag 07J3], restricted over an open.** -/
abbrev secondOrderRestrictQ₁₂ :
    (secondOrderThickeningObject S A).restrictOpen W ⟶
      (firstOrderThickeningObject S A).restrictOpen W :=
  Thickening.restrictOpenMap (secondOrderThickeningSiteQ₁₂ S A) W

/-- **The morphism `q₀₂ : T'' ⟶ T'` of [Stacks, Tag 07J3], restricted over an open.** -/
abbrev secondOrderRestrictQ₀₂ :
    (secondOrderThickeningObject S A).restrictOpen W ⟶
      (firstOrderThickeningObject S A).restrictOpen W :=
  Thickening.restrictOpenMap (secondOrderThickeningSiteQ₀₂ S A) W

/-! ### The relations between them

The restriction over an open of a composite is the composite of the restrictions, and that of an
identity is an identity, so each relation of the site restricts to the corresponding relation
over an open. -/

/-- **`p₀ ∘ i = id` over an open.** -/
theorem firstOrderRestrictι_comp_P₀ :
    firstOrderRestrictι A W ≫ firstOrderRestrictP₀ A W = 𝟙 (A.restrictOpen W) :=
  restrictOpenMap_siteι_comp_siteP₀ A W

/-- If `f ≫ g = h`, the restrictions of `f` and `g` over `W` compose to any `k` lying over `h`. -/
private theorem restrictOpenMap_comp_restrictOpenMap_eq {B C D : Thickening S}
    (f : B ⟶ C) (g : C ⟶ D) (h : B ⟶ D) (hfg : f ≫ g = h) (W : D.thickening.target.scheme.Opens)
    (k : B.restrictOpen (f.targetHom.hom ⁻¹ᵁ g.targetHom.hom ⁻¹ᵁ W) ⟶ D.restrictOpen W)
    (hk : k ≫ D.restrictOpenHom W = B.restrictOpenHom _ ≫ h) :
    Thickening.restrictOpenMap f (g.targetHom.hom ⁻¹ᵁ W) ≫ Thickening.restrictOpenMap g W = k := by
  refine (cancel_mono (D.restrictOpenHom W)).1 ?_
  rw [hk, Category.assoc, Thickening.restrictOpenMap_restrictOpenHom,
    Thickening.restrictOpenMap_restrictOpenHom_assoc, hfg]

/-- **`p₁ ∘ i = id` over an open.** -/
theorem firstOrderRestrictι_comp_P₁ :
    firstOrderRestrictι A W ≫ firstOrderRestrictP₁ A W = 𝟙 (A.restrictOpen W) :=
  restrictOpenMap_comp_restrictOpenMap_eq _ _ _ (firstOrderThickeningSiteι_comp_P₁ S A) W _
    ((Category.id_comp _).trans (Category.comp_id _).symm)

/-- **`p₀ ∘ q₀₁ = q₀` over an open.** -/
theorem secondOrderRestrictQ₀₁_comp_P₀ :
    secondOrderRestrictQ₀₁ A W ≫ firstOrderRestrictP₀ A W = secondOrderRestrictQ₀ A W :=
  restrictOpenMap_comp_restrictOpenMap_eq _ _ _ (secondOrderThickeningSiteQ₀₁_comp_P₀ S A) W _
    (Thickening.restrictOpenMap_restrictOpenHom _ W)

/-- **`p₁ ∘ q₀₁ = q₁` over an open.** -/
theorem secondOrderRestrictQ₀₁_comp_P₁ :
    secondOrderRestrictQ₀₁ A W ≫ firstOrderRestrictP₁ A W = secondOrderRestrictQ₁ A W :=
  restrictOpenMap_comp_restrictOpenMap_eq _ _ _ (secondOrderThickeningSiteQ₀₁_comp_P₁ S A) W _
    (Thickening.restrictOpenMap_restrictOpenHom _ W)

/-- **`p₀ ∘ q₁₂ = q₁` over an open.** -/
theorem secondOrderRestrictQ₁₂_comp_P₀ :
    secondOrderRestrictQ₁₂ A W ≫ firstOrderRestrictP₀ A W = secondOrderRestrictQ₁ A W :=
  restrictOpenMap_comp_restrictOpenMap_eq _ _ _ (secondOrderThickeningSiteQ₁₂_comp_P₀ S A) W _
    (Thickening.restrictOpenMap_restrictOpenHom _ W)

/-- **`p₁ ∘ q₁₂ = q₂` over an open.** -/
theorem secondOrderRestrictQ₁₂_comp_P₁ :
    secondOrderRestrictQ₁₂ A W ≫ firstOrderRestrictP₁ A W = secondOrderRestrictQ₂ A W :=
  restrictOpenMap_comp_restrictOpenMap_eq _ _ _ (secondOrderThickeningSiteQ₁₂_comp_P₁ S A) W _
    (Thickening.restrictOpenMap_restrictOpenHom _ W)

/-- **`p₀ ∘ q₀₂ = q₀` over an open.** -/
theorem secondOrderRestrictQ₀₂_comp_P₀ :
    secondOrderRestrictQ₀₂ A W ≫ firstOrderRestrictP₀ A W = secondOrderRestrictQ₀ A W :=
  restrictOpenMap_comp_restrictOpenMap_eq _ _ _ (secondOrderThickeningSiteQ₀₂_comp_P₀ S A) W _
    (Thickening.restrictOpenMap_restrictOpenHom _ W)

/-- **`p₁ ∘ q₀₂ = q₂` over an open.** -/
theorem secondOrderRestrictQ₀₂_comp_P₁ :
    secondOrderRestrictQ₀₂ A W ≫ firstOrderRestrictP₁ A W = secondOrderRestrictQ₂ A W :=
  restrictOpenMap_comp_restrictOpenMap_eq _ _ _ (secondOrderThickeningSiteQ₀₂_comp_P₁ S A) W _
    (Thickening.restrictOpenMap_restrictOpenHom _ W)

/-! ### The connection on the sections over an open -/

variable (M : SheafOfModules.{u} (crystallineStructureSheaf S))

/-- **The canonical connection of [Stacks, Lemma 60.15.1, Tag 07J6] on the sections over an
open.**  For an open `W` of the ambient scheme of an object `(U, T, δ)` it is the difference
`∇(s) = p₁^* s - p₀^* s` of the restrictions of `s` along the two projections of the first-order
universal thickening of [Stacks, Tag 07J2], read over `W`. -/
def crystalConnectionOpen :
    M.val.obj (op (A.restrictOpen W)) →+
      M.val.obj (op ((firstOrderThickeningObject S A).restrictOpen W)) :=
  AddMonoidHom.mk'
    (fun s ↦ (moduleSiteRestrict M (firstOrderRestrictP₁ A W) s :
        M.val.obj (op ((firstOrderThickeningObject S A).restrictOpen W))) -
      moduleSiteRestrict M (firstOrderRestrictP₀ A W) s)
    (fun s t ↦ by
      simp only [map_add]
      abel)

/-- The connection over `W` sends `s` to `p₁^* s - p₀^* s`. -/
theorem crystalConnectionOpen_apply (s : M.val.obj (op (A.restrictOpen W))) :
    crystalConnectionOpen A W M s =
      (moduleSiteRestrict M (firstOrderRestrictP₁ A W) s :
          M.val.obj (op ((firstOrderThickeningObject S A).restrictOpen W))) -
        moduleSiteRestrict M (firstOrderRestrictP₀ A W) s := rfl

/-- **Restricting `∇(s)` along a morphism into the first-order thickening gives the difference of
the two composites.** -/
theorem moduleSiteRestrict_crystalConnectionOpen {B : Thickening S}
    (g : B ⟶ (firstOrderThickeningObject S A).restrictOpen W) (g₀ g₁ : B ⟶ A.restrictOpen W)
    (h₀ : g ≫ firstOrderRestrictP₀ A W = g₀) (h₁ : g ≫ firstOrderRestrictP₁ A W = g₁)
    (s : M.val.obj (op (A.restrictOpen W))) :
    moduleSiteRestrict M g (crystalConnectionOpen A W M s) =
      moduleSiteRestrict M g₁ s - moduleSiteRestrict M g₀ s := by
  rw [crystalConnectionOpen_apply, map_sub, moduleSiteRestrict_comp, moduleSiteRestrict_comp,
    h₀, h₁]

/-- **The values of the connection over an open are killed by restriction along the diagonal.** -/
theorem crystalConnectionOpen_restrict_ι (s : M.val.obj (op (A.restrictOpen W))) :
    moduleSiteRestrict M (firstOrderRestrictι A W) (crystalConnectionOpen A W M s) = 0 := by
  rw [moduleSiteRestrict_crystalConnectionOpen A W M (firstOrderRestrictι A W) _ _
      (firstOrderRestrictι_comp_P₀ A W) (firstOrderRestrictι_comp_P₁ A W),
    moduleSiteRestrict_id, sub_self]

/-- **The connection commutes with restriction to a smaller open.** For `W' ≤ W`, restricting `s`
to `W'` and taking the connection there agrees with taking the connection over `W` and
restricting its value to `W'`. So the maps over the opens of `T` are the components of a morphism
of presheaves of abelian groups `F_T ⟶ p₀_* F_{T'}`. -/
theorem crystalConnectionOpen_naturality {W W' : A.thickening.target.scheme.Opens} (h : W' ≤ W)
    (s : M.val.obj (op (A.restrictOpen W))) :
    moduleSiteRestrict M ((firstOrderThickeningObject S A).restrictOpenLE h)
        (crystalConnectionOpen A W M s) =
      crystalConnectionOpen A W' M (moduleSiteRestrict M (A.restrictOpenLE h) s) := by
  have e₀ : (firstOrderThickeningObject S A).restrictOpenLE h ≫ firstOrderRestrictP₀ A W =
      firstOrderRestrictP₀ A W' ≫ A.restrictOpenLE h :=
    Thickening.restrictOpenLE_restrictOpenMap (firstOrderThickeningSiteP₀ S A) h
  have e₁ : (firstOrderThickeningObject S A).restrictOpenLE h ≫ firstOrderRestrictP₁ A W =
      firstOrderRestrictP₁ A W' ≫ A.restrictOpenLE h :=
    Thickening.restrictOpenLE_restrictOpenMap (firstOrderThickeningSiteP₁ S A) h
  show moduleSiteRestrict M ((firstOrderThickeningObject S A).restrictOpenLE h)
        ((moduleSiteRestrict M (firstOrderRestrictP₁ A W) s :
            M.val.obj (op ((firstOrderThickeningObject S A).restrictOpen W))) -
          moduleSiteRestrict M (firstOrderRestrictP₀ A W) s) =
      (moduleSiteRestrict M (firstOrderRestrictP₁ A W')
            (moduleSiteRestrict M (A.restrictOpenLE h) s) :
          M.val.obj (op ((firstOrderThickeningObject S A).restrictOpen W'))) -
        moduleSiteRestrict M (firstOrderRestrictP₀ A W')
          (moduleSiteRestrict M (A.restrictOpenLE h) s)
  rw [map_sub, moduleSiteRestrict_comp, moduleSiteRestrict_comp, moduleSiteRestrict_comp,
    moduleSiteRestrict_comp, e₀, e₁]

/-- **The curvature identity of [Stacks, Lemma 60.15.1, Tag 07J6] on the sections over an
open.**  For every sheaf of `𝒪_{X/S}`-modules, every object `(U, T, δ)`, every open `W` of `T`
and every section `s` of `F_T` over `W`,

`q₀₁^* ∇(s) + q₁₂^* ∇(s) = q₀₂^* ∇(s)`

over `W`. -/
theorem crystalConnectionOpen_cocycle (s : M.val.obj (op (A.restrictOpen W))) :
    moduleSiteRestrict M (secondOrderRestrictQ₀₁ A W) (crystalConnectionOpen A W M s) +
        moduleSiteRestrict M (secondOrderRestrictQ₁₂ A W) (crystalConnectionOpen A W M s) =
      moduleSiteRestrict M (secondOrderRestrictQ₀₂ A W) (crystalConnectionOpen A W M s) := by
  rw [moduleSiteRestrict_crystalConnectionOpen A W M (secondOrderRestrictQ₀₁ A W) _ _
      (secondOrderRestrictQ₀₁_comp_P₀ A W) (secondOrderRestrictQ₀₁_comp_P₁ A W),
    moduleSiteRestrict_crystalConnectionOpen A W M (secondOrderRestrictQ₁₂ A W) _ _
      (secondOrderRestrictQ₁₂_comp_P₀ A W) (secondOrderRestrictQ₁₂_comp_P₁ A W),
    moduleSiteRestrict_crystalConnectionOpen A W M (secondOrderRestrictQ₀₂ A W) _ _
      (secondOrderRestrictQ₀₂_comp_P₀ A W) (secondOrderRestrictQ₀₂_comp_P₁ A W)]
  abel

end Crystalline.GlobalCrystallineSituation

end

end
