module


public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Categorical.Basic
public import StacksFrontier.CategoryTheory.TwoFibreProduct.Functoriality
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.CategoryTheory.EffectiveEpi.Comp
public import Mathlib.CategoryTheory.ExtremalEpi
public import Mathlib.CategoryTheory.Monoidal.Mon
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init
import StacksCore.Tactic.EgaSgaAttribute

/-! # Stacks 02XB: properties of an induced functor of 2-fibre products

Let `Φ : 𝒳 ×_𝒵 𝒴 ⥤ 𝒜 ×_𝒞 ℬ` be the functor induced by a functoriality square `L : 𝒳 ⥤ 𝒜`,
`K : 𝒴 ⥤ ℬ`, `M : 𝒵 ⥤ 𝒞` filled by 2-cells `α : K ⋙ G ≅ I ⋙ M` and `β : H ⋙ M ≅ L ⋙ F`
(Stacks 02XA). Then `Φ` is faithful if `K` and `L` are; `Φ` is fully faithful if moreover `M`
is faithful; and `Φ` is an equivalence if `K` and `L` are equivalences and `M` is fully
faithful. The functor itself is `CategoryTheory.Limits.CategoricalPullback.map`.
-/

@[expose] public section

namespace CategoryTheory

open Limits

universe v₁ v₂ v₃ v₄ v₅ v₆ u₁ u₂ u₃ u₄ u₅ u₆

variable {𝒳 : Type u₁} {𝒴 : Type u₂} {𝒵 : Type u₃}
  {𝒜 : Type u₄} {ℬ : Type u₅} {𝒞 : Type u₆}
  [Category.{v₁} 𝒳] [Category.{v₂} 𝒴] [Category.{v₃} 𝒵]
  [Category.{v₄} 𝒜] [Category.{v₅} ℬ] [Category.{v₆} 𝒞]

/-! ## The induced functor between 2-fibre products -/

namespace Limits.CategoricalPullback

variable {F : 𝒜 ⥤ 𝒞} {G : ℬ ⥤ 𝒞} {H : 𝒳 ⥤ 𝒵} {I : 𝒴 ⥤ 𝒵}

/-- The induced functor `Φ : 𝒳 ×_𝒵 𝒴 ⥤ 𝒜 ×_𝒞 ℬ` associated with a functoriality
square as in Stacks 02XA. The natural isomorphisms `α : K ⋙ G ≅ I ⋙ M` and
`β : H ⋙ M ≅ L ⋙ F` are the 2-cells filling the two halves of the square. -/
@[simps, implicit_reducible]
def induced (L : 𝒳 ⥤ 𝒜) (K : 𝒴 ⥤ ℬ) (M : 𝒵 ⥤ 𝒞)
    (α : K ⋙ G ≅ I ⋙ M) (β : H ⋙ M ≅ L ⋙ F) :
    CategoricalPullback H I ⥤ CategoricalPullback F G where
  obj P :=
    { fst := L.obj P.fst
      snd := K.obj P.snd
      iso := β.symm.app P.fst ≪≫ M.mapIso P.iso ≪≫ α.symm.app P.snd }
  map {P Q} f :=
    { fst := L.map f.fst
      snd := K.map f.snd
      w := by
        have hβ := β.inv.naturality f.fst
        have hα := α.inv.naturality f.snd
        dsimp at hβ hα ⊢
        simp [reassoc_of% hβ, ← M.map_comp_assoc, f.w, hα] }
  map_id P := by apply Hom.ext <;> simp
  map_comp {P Q R} f g := by apply Hom.ext <;> simp

end Limits.CategoricalPullback

/-! ## Lifting compatibility and isomorphisms along the comparison functor -/

section LiftIsoAlongM

variable {F : 𝒜 ⥤ 𝒞} {G : ℬ ⥤ 𝒞} {H : 𝒳 ⥤ 𝒵} {I : 𝒴 ⥤ 𝒵}
  (L : 𝒳 ⥤ 𝒜) (K : 𝒴 ⥤ ℬ) (M : 𝒵 ⥤ 𝒞)
  (α : K ⋙ G ≅ I ⋙ M) (β : H ⋙ M ≅ L ⋙ F)

/-- Lifting compatibility via faithfulness of `M`: if `(L.map f₁, K.map f₂)`
satisfies the compatibility relation in the codomain, then `(f₁, f₂)` satisfies
it in the domain. -/
lemma compat_of_induced_compat [M.Faithful]
    {P Q : CategoricalPullback H I}
    (f₁ : P.fst ⟶ Q.fst) (f₂ : P.snd ⟶ Q.snd)
    (hcompat :
      F.map (L.map f₁) ≫ (β.inv.app Q.fst ≫ M.map Q.iso.hom ≫ α.inv.app Q.snd)
        = (β.inv.app P.fst ≫ M.map P.iso.hom ≫ α.inv.app P.snd) ≫ G.map (K.map f₂)) :
    H.map f₁ ≫ Q.iso.hom = P.iso.hom ≫ I.map f₂ := by
  have hβ := β.inv.naturality f₁
  have hα := α.inv.naturality f₂
  dsimp at hβ hα
  apply M.map_injective
  rw [← cancel_epi (β.inv.app P.fst), ← cancel_mono (α.inv.app Q.snd)]
  simp only [Functor.map_comp, Category.assoc, ← reassoc_of% hβ, hα]
  simpa using hcompat

/-- Lift an iso along fully faithful `M`: given an iso `ψ : F.obj A ≅ G.obj B`
together with isos `ε₁ : L.obj X ≅ A` and `ε₂ : K.obj Y ≅ B`, produce an iso
`H.obj X ≅ I.obj Y` in `𝒵` via `M.preimageIso`. -/
noncomputable def liftIsoAlongM [M.Faithful] [M.Full]
    {X : 𝒳} {Y : 𝒴} {A : 𝒜} {B : ℬ}
    (ψ : F.obj A ≅ G.obj B) (ε₁ : L.obj X ≅ A) (ε₂ : K.obj Y ≅ B) :
    H.obj X ≅ I.obj Y :=
  M.preimageIso (β.app X ≪≫ F.mapIso ε₁ ≪≫ ψ ≪≫ G.mapIso ε₂.symm ≪≫ α.app Y)

/-- The image of `liftIsoAlongM` under `M` unfolds to the chosen composition. -/
lemma map_liftIsoAlongM [M.Faithful] [M.Full]
    {X : 𝒳} {Y : 𝒴} {A : 𝒜} {B : ℬ}
    (ψ : F.obj A ≅ G.obj B) (ε₁ : L.obj X ≅ A) (ε₂ : K.obj Y ≅ B) :
    M.map (liftIsoAlongM L K M α β ψ ε₁ ε₂).hom =
      β.hom.app X ≫ F.map ε₁.hom ≫ ψ.hom ≫ G.map ε₂.inv ≫ α.hom.app Y := by
  simp [liftIsoAlongM, Functor.preimageIso]

/-- Compatibility of `liftIsoAlongM` with `(ε₁.hom, ε₂.hom)` in the codomain. -/
lemma liftIsoAlongM_compat [M.Faithful] [M.Full]
    {X : 𝒳} {Y : 𝒴} {A : 𝒜} {B : ℬ}
    (ψ : F.obj A ≅ G.obj B) (ε₁ : L.obj X ≅ A) (ε₂ : K.obj Y ≅ B) :
    (F.map ε₁.hom ≫ ψ.hom : F.obj (L.obj X) ⟶ G.obj B) =
      (((CategoricalPullback.map H I L K M F G α β).obj
          ⟨X, Y, liftIsoAlongM L K M α β ψ ε₁ ε₂⟩).iso.hom ≫ G.map ε₂.hom :
        F.obj (L.obj X) ⟶ G.obj B) := by
  rw [CategoricalPullback.map_obj_iso_hom, map_liftIsoAlongM]
  simp

/-- The inverse-direction compatibility for `liftIsoAlongM`. -/
lemma liftIsoAlongM_inv_compat [M.Faithful] [M.Full]
    {X : 𝒳} {Y : 𝒴} {A : 𝒜} {B : ℬ}
    (ψ : F.obj A ≅ G.obj B) (ε₁ : L.obj X ≅ A) (ε₂ : K.obj Y ≅ B) :
    (F.map ε₁.inv ≫
        ((CategoricalPullback.map H I L K M F G α β).obj
            ⟨X, Y, liftIsoAlongM L K M α β ψ ε₁ ε₂⟩).iso.hom :
        F.obj A ⟶ G.obj (K.obj Y))
      = (ψ.hom ≫ G.map ε₂.inv : F.obj A ⟶ G.obj (K.obj Y)) := by
  rw [CategoricalPullback.map_obj_iso_hom, map_liftIsoAlongM]
  simp

end LiftIsoAlongM

/-! ## Main Statements (Stacks 02XB) -/

section InducedProperties

variable {F : 𝒜 ⥤ 𝒞} {G : ℬ ⥤ 𝒞} {H : 𝒳 ⥤ 𝒵} {I : 𝒴 ⥤ 𝒵}
  (L : 𝒳 ⥤ 𝒜) (K : 𝒴 ⥤ ℬ) (M : 𝒵 ⥤ 𝒞)
  (α : K ⋙ G ≅ I ⋙ M) (β : H ⋙ M ≅ L ⋙ F)

/-- **Stacks 02XB (1)** — If `K` and `L` are faithful, then the induced functor
`𝒳 ×_𝒵 𝒴 ⥤ 𝒜 ×_𝒞 ℬ` is faithful. -/
@[stacks 02XB "(1)"]
theorem induced_faithful_of_faithful [K.Faithful] [L.Faithful] :
    (CategoricalPullback.map H I L K M F G α β).Faithful where
  map_injective h :=
    CategoricalPullback.Hom.ext (L.map_injective (congr_arg CategoricalPullback.Hom.fst h))
      (K.map_injective (congr_arg CategoricalPullback.Hom.snd h))

/-- **Stacks 02XB (2)** — If `K` and `L` are fully faithful and `M` is faithful,
then the induced functor `𝒳 ×_𝒵 𝒴 ⥤ 𝒜 ×_𝒞 ℬ` is fully faithful. -/
@[stacks 02XB "(2)", sga "1 VI 4.1"]
theorem induced_fullyFaithful_of_fullyFaithful
    [K.Faithful] [K.Full] [L.Faithful] [L.Full] [M.Faithful] :
    (CategoricalPullback.map H I L K M F G α β).Faithful ∧
      (CategoricalPullback.map H I L K M F G α β).Full := by
  refine ⟨induced_faithful_of_faithful L K M α β, ⟨fun {P Q} h ↦ ?_⟩⟩
  obtain ⟨f₁, hf₁⟩ : ∃ f₁ : P.fst ⟶ Q.fst, L.map f₁ = h.fst :=
    L.map_surjective h.fst
  obtain ⟨f₂, hf₂⟩ : ∃ f₂ : P.snd ⟶ Q.snd, K.map f₂ = h.snd :=
    K.map_surjective h.snd
  refine ⟨⟨f₁, f₂, compat_of_induced_compat L K M α β f₁ f₂ ?_⟩, ?_⟩
  · rw [hf₁, hf₂]
    exact h.w
  exact CategoricalPullback.Hom.ext hf₁ hf₂

/-- **Stacks 02XB (3)** — If `K` and `L` are equivalences and `M` is fully
faithful, then the induced functor `𝒳 ×_𝒵 𝒴 ⥤ 𝒜 ×_𝒞 ℬ` is an equivalence
of categories. -/
@[stacks 02XB "(3)"]
theorem induced_isEquivalence_of_isEquivalence
    [K.IsEquivalence] [L.IsEquivalence] [M.Faithful] [M.Full] :
    (CategoricalPullback.map H I L K M F G α β).IsEquivalence := by
  obtain ⟨hfaithful, hfull⟩ := induced_fullyFaithful_of_fullyFaithful L K M α β
  refine { faithful := hfaithful, full := hfull, essSurj := ⟨fun ⟨A, B, ψ⟩ ↦ ?_⟩ }
  set ε₁ := L.objObjPreimageIso A
  set ε₂ := K.objObjPreimageIso B
  refine ⟨⟨L.objPreimage A, K.objPreimage B, liftIsoAlongM L K M α β ψ ε₁ ε₂⟩, ?_⟩
  refine ⟨{ hom := { fst := ?_, snd := ?_, w := ?_ }
            inv := { fst := ?_, snd := ?_, w := ?_ }
            hom_inv_id := ?_
            inv_hom_id := ?_ }⟩
  · exact (show L.obj (L.objPreimage A) ⟶ A from ε₁.hom)
  · exact (show K.obj (K.objPreimage B) ⟶ B from ε₂.hom)
  · exact liftIsoAlongM_compat L K M α β ψ ε₁ ε₂
  · exact (show A ⟶ L.obj (L.objPreimage A) from ε₁.inv)
  · exact (show B ⟶ K.obj (K.objPreimage B) from ε₂.inv)
  · exact liftIsoAlongM_inv_compat L K M α β ψ ε₁ ε₂
  · apply CategoricalPullback.Hom.ext <;> simp
  · apply CategoricalPullback.Hom.ext <;> simp

end InducedProperties

end CategoryTheory
