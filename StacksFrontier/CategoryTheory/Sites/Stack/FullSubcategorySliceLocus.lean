module

public import StacksFrontier.CategoryTheory.FiberedInGroupoids.DiagonalFullSubcategory
public import StacksFrontier.CategoryTheory.Sites.Descent.IsStack
public import StacksFrontier.CategoryTheory.Sites.Stack.SlicePointComparison
public import StacksFrontier.CategoryTheory.Sites.Stack.SlicePointOfObject

/-!
# A property of objects cut out, over every point, by an object of the slice

Let `p : 𝒵 ⥤ 𝒟/X` be fibred in groupoids and let `P` be a property of the objects of `𝒵` closed
under isomorphism. Suppose that for every object `U` of `𝒟/X` and every point `W : 𝒟/U.left ⥤ 𝒵`
of `p` with values in `U` there is an object `V` of `𝒟/U.left` such that an object `T` of
`𝒟/U.left` admits a morphism to `V` exactly when `W(T)` has the property `P`. Then

* `P` is inherited along arbitrary morphisms of `𝒵`
  (`CategoryTheory.Functor.prop_of_hom_of_sliceLocus`), and consequently
* the restriction of `p` to the full subcategory cut out by `P` is again fibred in groupoids
  (`CategoryTheory.Functor.isFiberedInGroupoids_restrict_of_hom`), and
* `P` satisfies condition (1) of **Stacks 04TU**
  (`CategoryTheory.Functor.closedUnderStronglyCartesianUpToIso_of_hom`).

Every object of a fibre is the value at the terminal object of such a point, by the
essential-surjectivity half of the 2-Yoneda lemma
(`CategoryTheory.Functor.slicePointOfObject`), so the hypothesis is exactly a slicewise
description of `P`: the arrows `T ⟶ V` are the objects of the slice at which `P` holds. The base
of a morphism `φ : x ⟶ y` names an object of `𝒟/(p y).left`, which maps to the terminal object,
so `P` at `y` propagates to `P` at the value of the point of `y` there, and that value is
isomorphic to `x` because both carry strongly cartesian morphisms to `y` over the base of `φ`.

## Main results

* `CategoryTheory.Functor.prop_of_hom_of_sliceLocus`: the property is inherited along morphisms.
* `CategoryTheory.Functor.closedUnderStronglyCartesianUpToIso_of_hom`: a property inherited along
  morphisms satisfies condition (1) of Stacks 04TU.
* `CategoryTheory.Functor.isFiberedInGroupoids_restrict_of_hom`: the restriction of a category
  fibred in groupoids to the full subcategory cut out by a property inherited along morphisms is
  fibred in groupoids.

## References

* [Stacks Project, Tag 003S](https://stacks.math.columbia.edu/tag/003S)
* [Stacks Project, Tag 004B](https://stacks.math.columbia.edu/tag/004B)
* [Stacks Project, Tag 04TU](https://stacks.math.columbia.edu/tag/04TU)
-/

@[expose] public section

open CategoryTheory

universe v₁ u₁ v₂ u₂

namespace CategoryTheory.Functor

variable {D : Type u₁} [Category.{v₁} D] {X : D} {Z : Type u₂} [Category.{v₂} Z]

/-- **The comparison of the value of a point at the terminal object with the object it was built
from is an isomorphism**: it is vertical, and in a category fibred in groupoids a vertical
morphism is invertible. -/
theorem isIso_slicePointUnit (p : Z ⥤ Over X) (hp : p.IsFiberedInGroupoids) (U : Over X) (z : Z)
    (hz : p.obj z = U) :
    haveI : p.IsFibered := hp.isFibered
    IsIso (slicePointUnit p U z hz) :=
  have : p.IsFibered := hp.isFibered
  have := isHomLift_slicePointUnit p U z hz
  have : p.IsStronglyCartesian (𝟙 U) (slicePointUnit p U z hz) :=
    hp.isStronglyCartesian_homLift _ _
  IsStronglyCartesian.isIso_of_base_isIso (p := p) (f := 𝟙 U) _

/-- **Every lift of `f : V ⟶ U` at an object `z` over `U` is isomorphic to the value at
`Over.mk f.left` of the point of `p` attached to `z`.** Both carry strongly cartesian morphisms
to `z` over `f`, the one for the point being the image of the canonical arrow to the terminal
object followed by the comparison at the terminal object. -/
theorem nonempty_iso_slicePointObj (p : Z ⥤ Over X) (hp : p.IsFiberedInGroupoids) {U : Over X}
    {z : Z} (hz : p.obj z = U) {V : Over X} (f : V ⟶ U) {w : Z} (ψ : w ⟶ z)
    (hψ : p.IsHomLift f ψ) :
    haveI : p.IsFibered := hp.isFibered
    Nonempty ((slicePointOfObject p U z hz).obj (Over.mk f.left) ≅ w) := by
  have : p.IsFibered := hp.isFibered
  have hW : slicePointOfObject p U z hz ⋙ p = Over.map U.hom :=
    slicePointOfObject_comp p U z hz
  have heq : (Over.map U.hom).obj (Over.mk f.left) = V := congrArg Over.mk (Over.w f)
  have hψ0 := isHomLift_map_toMkId_comp p U (slicePointOfObject p U z hz)
    ((Functor.const (Over U.left)).obj z) hW (slicePointUnit p U z hz)
    (isHomLift_slicePointUnit p U z hz) (Over.mk f.left)
  have hbase : structHom U (Over.mk f.left) = eqToHom heq ≫ f := by
    apply Over.OverMorphism.ext
    simp
  rw [hbase] at hψ0
  generalize (slicePointOfObject p U z hz).map (toMkId U (Over.mk f.left)) ≫
    slicePointUnit p U z hz = σ at hψ0
  have := (IsHomLift.lift_eqToHom_comp_iff p f σ heq).mp hψ0
  have := hp.isStronglyCartesian_homLift f σ
  have := hψ
  have := hp.isStronglyCartesian_homLift f ψ
  exact ⟨(IsCartesian.domainUniqueUpToIso p f σ ψ).symm⟩

/-- **A property described slicewise by an object of the slice is inherited along morphisms.**
For `φ : x ⟶ y` with `P y`, read `P` at the point of `p` attached to `y`: it holds at the
terminal object of `𝒟/(p y).left`, hence that object maps to the representing object `V`, hence
so does the object named by the base of `φ`, and the value of the point there is isomorphic to
`x`. -/
theorem prop_of_hom_of_sliceLocus (p : Z ⥤ Over X) (hp : p.IsFiberedInGroupoids)
    (P : ObjectProperty Z) [P.IsClosedUnderIsomorphisms]
    (hloc : ∀ (U : Over X) (W : Over U.left ⥤ Z), W ⋙ p = Over.map U.hom →
      ∃ V : Over U.left, ∀ T : Over U.left, Nonempty (T ⟶ V) ↔ P (W.obj T))
    {x y : Z} (φ : x ⟶ y) (hy : P y) : P x := by
  have : p.IsFibered := hp.isFibered
  have hW : slicePointOfObject p (p.obj y) y rfl ⋙ p = Over.map (p.obj y).hom :=
    slicePointOfObject_comp p (p.obj y) y rfl
  obtain ⟨V, hV⟩ := hloc (p.obj y) (slicePointOfObject p (p.obj y) y rfl) hW
  have := isIso_slicePointUnit p hp (p.obj y) y rfl
  have h0 : P ((slicePointOfObject p (p.obj y) y rfl).obj (Over.mk (𝟙 (p.obj y).left))) :=
    P.prop_of_iso (asIso (slicePointUnit p (p.obj y) y rfl)).symm hy
  obtain ⟨s⟩ := (hV (Over.mk (𝟙 (p.obj y).left))).2 h0
  -- the property at the value of the point on the object named by the base of `φ`
  have h1 : P ((slicePointOfObject p (p.obj y) y rfl).obj (Over.mk (p.map φ).left)) :=
    (hV (Over.mk (p.map φ).left)).1 ⟨toMkId (p.obj y) (Over.mk (p.map φ).left) ≫ s⟩
  obtain ⟨e⟩ := nonempty_iso_slicePointObj p hp (rfl : p.obj y = p.obj y) (p.map φ) φ
    (CategoryTheory.IsHomLift.map p φ)
  exact P.prop_of_iso e h1

/-- **A property inherited along morphisms satisfies condition (1) of Stacks 04TU.** -/
theorem closedUnderStronglyCartesianUpToIso_of_hom {𝒮 : Type u₁} [Category.{v₁} 𝒮]
    (p : Z ⥤ 𝒮) (P : ObjectProperty Z)
    (hP : ∀ {a b : Z}, (a ⟶ b) → P b → P a) :
    ClosedUnderStronglyCartesianUpToIso p P :=
  fun _ φ _ hx => ⟨_, hP φ hx, ⟨Iso.refl _⟩⟩

/-- **The restriction of a category fibred in groupoids to the full subcategory cut out by a
property inherited along morphisms is fibred in groupoids.** Existence of lifts is the ambient
one, whose source has the property by hypothesis; the fill-in clause needs no condition on the
property at all (`CategoryTheory.uniqueLift_restrict`). -/
theorem isFiberedInGroupoids_restrict_of_hom {𝒮 : Type u₁} [Category.{v₁} 𝒮]
    (p : Z ⥤ 𝒮) (hp : p.IsFiberedInGroupoids) (P : ObjectProperty Z)
    (hP : ∀ {a b : Z}, (a ⟶ b) → P b → P a) :
    (Functor.restrict p P).IsFiberedInGroupoids where
  exists_lift f A hA := by
    obtain ⟨z, θ, hθ⟩ := hp.exists_lift f A.obj hA
    exact ⟨⟨z, hP θ A.property⟩,
      ObjectProperty.homMk (X := ⟨z, hP θ A.property⟩) (Y := A) θ,
      (isHomLift_restrict_iff p P f
        (ObjectProperty.homMk (X := ⟨z, hP θ A.property⟩) (Y := A) θ)).2 hθ⟩
  unique_lift φ ψ f h := uniqueLift_restrict p P hp φ ψ f h

end CategoryTheory.Functor

end
