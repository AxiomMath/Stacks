module

public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Terminal
public import StacksFrontier.CategoryTheory.FiberedCategory.HomLift
public import StacksFrontier.Deformation.Cofibered

/-!
# Slicing a category cofibered in groupoids at an object over a terminal base

Let `p : F ⥤ C` be cofibered in groupoids and let `x` be an object of `F` whose image
`p.obj x` is a terminal object of `C`. Then the slice category `Over x` of objects of `F`
equipped with a morphism to `x` is again cofibered in groupoids over `C`, by the structure
functor `Over.forget x ⋙ p`.

This is the construction that passes from a cofibered category `p : F ⥤ 𝒞_Λ` to the
deformation category of an object of the fibre over the residue field: the residue field
is a terminal object of `𝒞_Λ`, so no further hypothesis is needed. Pushforwards are
computed in `F`, and the structure morphism of a pushed-forward object is the unique
fill-in over the unique morphism into the terminal object.

## Main results

* `Deformation.exists_unique_cofibered_factor`: existence and uniqueness of fill-ins,
  stated in the cofibered direction.
* `Deformation.isIso_of_isCofiberedInGroupoids_of_map_isIso`: a morphism of `F` whose
  image is an isomorphism is an isomorphism.
* `Deformation.isIso_of_isTerminal`: a morphism between terminal objects is invertible.
* `Deformation.isCofiberedInGroupoids_of_lifts`: a constructor for
  `IsCofiberedInGroupoids` from data in the cofibered direction.
* `Deformation.isCofiberedInGroupoids_overForget`: the slice at an object over a terminal
  base is cofibered in groupoids.

## References

* [Stacks Project, Tag 06GU](https://stacks.math.columbia.edu/tag/06GU)
-/

@[expose] public section

namespace Deformation

open CategoryTheory

universe v₁ v₂ u₁ u₂

variable {F : Type u₁} [Category.{v₁} F] {C : Type u₂} [Category.{v₂} C]

/-- Existence and uniqueness of fill-ins in a category cofibered in groupoids: given
`φ : a ⟶ b`, `ψ : a ⟶ c` and a base morphism `f : p.obj b ⟶ p.obj c` compatible with
them, there is a unique `χ : b ⟶ c` over `f` with `φ ≫ χ = ψ`. -/
theorem exists_unique_cofibered_factor {p : F ⥤ C} (hp : IsCofiberedInGroupoids p)
    {a b c : F} (φ : a ⟶ b) (ψ : a ⟶ c) (f : p.obj b ⟶ p.obj c)
    (h : p.map φ ≫ f = p.map ψ) : ∃! χ : b ⟶ c, p.map χ = f ∧ φ ≫ χ = ψ := by
  have hop : f.op ≫ p.op.map φ.op = p.op.map ψ.op := by
    change (p.map φ ≫ f).op = (p.map ψ).op
    exact congrArg Opposite.op h
  obtain ⟨χop, hχ, hχuniq⟩ := hp.unique_lift φ.op ψ.op f.op hop
  exact ⟨χop.unop, ⟨Opposite.op_injective hχ.1, Opposite.op_injective hχ.2⟩,
    fun χ hχ' => congrArg Quiver.Hom.unop
      (hχuniq χ.op ⟨congrArg Opposite.op hχ'.1, congrArg Opposite.op hχ'.2⟩)⟩

/-- In a category cofibered in groupoids a morphism out of a fixed object may be cancelled
on the left, provided the two morphisms being compared lie over the same base morphism. -/
theorem cofibered_left_cancel {p : F ⥤ C} (hp : IsCofiberedInGroupoids p)
    {a b c : F} (f : a ⟶ b) {g h : b ⟶ c}
    (hmap : p.map g = p.map h) (hcomp : f ≫ g = f ≫ h) : g = h := by
  obtain ⟨χ, _, huniq⟩ :=
    exists_unique_cofibered_factor hp f (f ≫ g) (p.map g) (by simp)
  exact (huniq g ⟨rfl, rfl⟩).trans (huniq h ⟨hmap.symm, hcomp.symm⟩).symm

/-- In a category cofibered in groupoids a morphism lying over an isomorphism is itself an
isomorphism. -/
theorem isIso_of_isCofiberedInGroupoids_of_map_isIso {p : F ⥤ C}
    (hp : IsCofiberedInGroupoids p) {a b : F} (φ : a ⟶ b) [IsIso (p.map φ)] : IsIso φ := by
  have h1 : IsIso (p.op.map φ.op) := by simpa using isIso_op (p.map φ)
  have h2 : p.op.IsStronglyCartesian (p.op.map φ.op) φ.op := hp.isStronglyCartesian _
  have : IsIso φ.op :=
    Functor.IsStronglyCartesian.isIso_of_base_isIso (p := p.op) (p.op.map φ.op) φ.op
  exact isIso_of_op φ

/-- A morphism between two terminal objects is an isomorphism. -/
theorem isIso_of_isTerminal {X Y : C} (hX : Limits.IsTerminal X) (hY : Limits.IsTerminal Y)
    (f : X ⟶ Y) : IsIso f :=
  ⟨⟨hX.from Y, hX.hom_ext _ _, hY.hom_ext _ _⟩⟩

/-- Constructor for `IsCofiberedInGroupoids` out of the data in the cofibered direction:
every base morphism out of the image of an object lifts, and fill-ins exist and are
unique. -/
theorem isCofiberedInGroupoids_of_lifts {p : F ⥤ C}
    (hlift : ∀ {A B : C} (f : A ⟶ B) (a : F), p.obj a = A →
      ∃ (b : F) (φ : a ⟶ b), p.IsHomLift f φ)
    (huniq : ∀ {a b c : F} (φ : a ⟶ b) (ψ : a ⟶ c) (f : p.obj b ⟶ p.obj c),
      p.map φ ≫ f = p.map ψ → ∃! χ : b ⟶ c, p.map χ = f ∧ φ ≫ χ = ψ) :
    IsCofiberedInGroupoids p := by
  refine ⟨?_, ?_⟩
  · intro V U f a ha
    obtain ⟨b, φ, hφ⟩ := hlift f.unop (Opposite.unop a) (congrArg Opposite.unop ha)
    exact ⟨Opposite.op b, φ.op, isHomLift_op p f.unop φ (inst := hφ)⟩
  · intro a b c φ ψ f h
    obtain ⟨χ, hχ, hχuniq⟩ :=
      huniq φ.unop ψ.unop f.unop (congrArg Quiver.Hom.unop h)
    exact ⟨χ.op, ⟨congrArg Opposite.op hχ.1, congrArg Opposite.op hχ.2⟩,
      fun χ' hχ' => congrArg Opposite.op
        (hχuniq χ'.unop ⟨congrArg Quiver.Hom.unop hχ'.1, congrArg Quiver.Hom.unop hχ'.2⟩)⟩

/-- Slicing a category cofibered in groupoids at an object whose image is terminal gives
again a category cofibered in groupoids. -/
theorem isCofiberedInGroupoids_overForget {p : F ⥤ C} (hp : IsCofiberedInGroupoids p)
    (x : F) (hx : Limits.IsTerminal (p.obj x)) :
    IsCofiberedInGroupoids (Over.forget x ⋙ p) := by
  refine isCofiberedInGroupoids_of_lifts ?_ ?_
  · intro A B f a ha
    subst ha
    obtain ⟨b, φ, hφ⟩ := exists_pushforward hp f a.left rfl
    have htri : p.map φ ≫ hx.from (p.obj b) = p.map a.hom := hx.hom_ext _ _
    obtain ⟨β, hβ, -⟩ := exists_unique_cofibered_factor hp φ a.hom (hx.from (p.obj b)) htri
    let g : a ⟶ Over.mk β := Over.homMk φ hβ.2
    exact ⟨Over.mk β, g, (Functor.isHomLift_comp_iff (Over.forget x) p f g).mpr hφ⟩
  · intro a b c φ ψ f h
    obtain ⟨χ, hχ, hχuniq⟩ := exists_unique_cofibered_factor hp φ.left ψ.left f h
    have hmap : p.map (χ ≫ c.hom) = p.map b.hom := hx.hom_ext _ _
    have hcomp : φ.left ≫ (χ ≫ c.hom) = φ.left ≫ b.hom := by
      rw [← Category.assoc, hχ.2]
      exact (Over.w ψ).trans (Over.w φ).symm
    refine ⟨Over.homMk χ (cofibered_left_cancel hp _ hmap hcomp),
      ⟨hχ.1, Over.OverMorphism.ext hχ.2⟩, fun g' hg' => ?_⟩
    exact Over.OverMorphism.ext (hχuniq g'.left ⟨hg'.1, congrArg (·.left) hg'.2⟩)

end Deformation

end
