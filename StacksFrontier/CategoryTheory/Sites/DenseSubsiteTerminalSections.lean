module

public import Mathlib.CategoryTheory.Sites.DenseSubsite.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Terminal

/-!
# Sections over a terminal object through a cover-dense functor

Let `G : C ⥤ D` be cover-dense and locally full for a topology `K` on `D`, and let `T` be a
terminal object of `D`.  For a sheaf of sets `ℱ` on `(D, K)` restriction along the unique maps
`G(Y) ⟶ T` identifies the sections of `ℱ` over `T` with the compatible families of sections of
`ℱ` over the objects `G(Y)`, i.e. with the sections of the presheaf `G.op ⋙ ℱ` on `C`.  So the
global sections of a sheaf can be computed on a dense subsite.

## Main definitions

* `CategoryTheory.Functor.IsCoverDense.terminalSectionsEquiv`: the bijection
  `ℱ(T) ≃ (G.op ⋙ ℱ).sections`.

## Main results

* `CategoryTheory.Functor.IsCoverDense.bijective_terminalSectionsRestrict`: restriction from
  `ℱ(T)` to the sections of `G.op ⋙ ℱ` is bijective.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite Limits

universe w v₁ v₂ u₁ u₂

namespace CategoryTheory.Functor.IsCoverDense

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D] (G : C ⥤ D)
  (K : GrothendieckTopology D) [G.IsCoverDense K] [G.IsLocallyFull K]
  (ℱ : Sheaf K (Type w)) {T : D} (hT : IsTerminal T)

/-- Restriction of a section over a terminal object to the objects `G(Y)`, as a compatible family:
a section of `G.op ⋙ ℱ`. -/
def terminalSectionsRestrict (x : ℱ.obj.obj (op T)) : (G.op ⋙ ℱ.obj).sections :=
  ⟨fun Y => ℱ.obj.map (hT.from (G.obj Y.unop)).op x, fun {Y Y'} g => by
    change ℱ.obj.map (G.map g.unop).op (ℱ.obj.map (hT.from (G.obj Y.unop)).op x) = _
    rw [← Functor.map_comp_apply, ← op_comp]
    exact congrArg (fun h => ℱ.obj.map h.op x) (hT.hom_ext _ _)⟩

omit [G.IsCoverDense K] [G.IsLocallyFull K] in
/-- The component at `Y` of the restriction of `x` is the image of `x` under the unique map
`G(Y) ⟶ T`. -/
@[simp]
theorem terminalSectionsRestrict_val (x : ℱ.obj.obj (op T)) (Y : Cᵒᵖ) :
    (terminalSectionsRestrict G K ℱ hT x).val Y = ℱ.obj.map (hT.from (G.obj Y.unop)).op x := rfl

/-- **Sections over a terminal object are compatible families on a dense subsite.**
Restriction along the unique maps `G(Y) ⟶ T` is a bijection from the sections of `ℱ` over `T`
to the sections of `G.op ⋙ ℱ`. -/
theorem bijective_terminalSectionsRestrict :
    Function.Bijective (terminalSectionsRestrict G K ℱ hT) := by
  refine ⟨fun x y h => IsCoverDense.ext G ℱ T fun Y f => ?_, fun s => ?_⟩
  · rw [hT.hom_ext f (hT.from (G.obj Y))]
    exact congrFun (congrArg Subtype.val h) (op Y)
  · let α : G.op ⋙ (Functor.const Dᵒᵖ).obj PUnit.{w + 1} ⟶ G.op ⋙ ℱ.obj :=
      { app := fun Y => ↾fun _ => s.val Y
        naturality := fun {Y Y'} g => by
          ext
          exact (s.property g).symm }
    refine ⟨Types.appHom α T PUnit.unit, Subtype.ext (funext fun Y => ?_)⟩
    exact Types.appHom_restrict α (hT.from (G.obj Y.unop)).op PUnit.unit

/-- `CategoryTheory.Functor.IsCoverDense.terminalSectionsRestrict` as an equivalence. -/
def terminalSectionsEquiv : ℱ.obj.obj (op T) ≃ (G.op ⋙ ℱ.obj).sections :=
  Equiv.ofBijective _ (bijective_terminalSectionsRestrict G K ℱ hT)

end CategoryTheory.Functor.IsCoverDense

end
