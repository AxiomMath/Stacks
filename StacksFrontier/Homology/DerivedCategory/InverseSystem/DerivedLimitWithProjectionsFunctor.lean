module

public import StacksFrontier.Homology.DerivedCategory.InverseSystem.DerivedLimitWithProjections
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import Mathlib.CategoryTheory.Triangulated.Functor

/-!
# Derived limits with projections are carried along a triangulated functor

Let `G : D ⥤ E` be a triangulated functor between pre-triangulated categories and let
`F : ℕᵒᵖ ⥤ D` be an inverse system whose terms have a product preserved by `G`. This file proves
that `G` carries a derived-limit presentation of `F` to one of `F ⋙ G`, with the images of the
projections as projections.

`CategoryTheory.Pretriangulated.IsDerivedLimit.map_of_isTriangulated` is the same transport for
the bare predicate `CategoryTheory.Pretriangulated.IsDerivedLimit`, which pins no cone. What the
version below adds is exactly the cone: the projections of the image presentation are named, and
are the images of the given ones. That is what a localization argument needs — the restriction of
a canonical comparison map into a derived limit has to be recognised as the comparison map of the
restricted presentation, and for that the projections downstairs must be the restrictions of the
projections upstairs. The statement for the bare predicate is a consequence, through
`NoetherianAdicCompletion.IsDerivedLimitWithProjections.isDerivedLimit`.

## Main results

* `NoetherianAdicCompletion.IsDerivedLimitWithProjections.map` — **a triangulated functor
  preserving the product of the terms carries a derived-limit presentation with projections to
  one of the composite system.**
* `NoetherianAdicCompletion.hasEventualInverses_hom` — an isomorphism of inverse systems has
  eventual inverses; the transport of a derived-limit presentation along it is the base's
  `NoetherianAdicCompletion.IsDerivedLimitWithProjections.ofNatIso`.
  This is the degenerate case of the pro-isomorphism transport
  `IsDerivedLimitWithProjections.comp_of_hasEventualInverses`, the one that needs no reindexing;
  it is what identifies a presentation over one spelling of a tower with a presentation over
  another.

## Implementation notes

`NoetherianAdicCompletion.IsDerivedLimitWithProjections F K π` says that `Limits.Pi.lift π` is
the first map of a distinguished triangle whose second map is the Milnor difference of `F`. The
proof below compares the image of that triangle with the corresponding triangle for `F ⋙ G`: the
two differ only by the product comparison isomorphism
`CategoryTheory.Limits.PreservesProduct.iso` in the second and third places, and both squares
reduce, after composing with a product projection, to `Limits.Pi.lift_comp_π` and the additivity of
`G` — a triangulated functor being additive. The structural map of the image triangle is
transported by the same isomorphism, which is why no hypothesis beyond the preservation of that
one product is needed.

The product of the image family is written `fun n ↦ (F ⋙ G).obj ⟨n⟩` by the derived-limit
predicate and `fun n ↦ G.obj (F.obj ⟨n⟩)` by `PreservesProduct.iso`; the two are definitionally
equal but instance search does not cross them, and the local instance below is that crossing,
exactly as in the proof of `IsDerivedLimit.map_of_isTriangulated`.

`Limits.Pi.lift` takes its indexed family as an implicit argument, and elaborating it from the
components alone produces `fun n ↦ G.obj (F.obj ⟨n⟩)` where the goal carries
`fun n ↦ (F ⋙ G).obj ⟨n⟩`; the two are definitionally equal, so `exact` crosses them, but a
`rw` spelled the first way does not fire on a goal spelled the second way. The family is
therefore given explicitly with `(f := …)` throughout.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite

universe v₁ v₂ u₁ u₂

namespace NoetherianAdicCompletion

variable {D : Type u₁} [Category.{v₁} D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
  {E : Type u₂} [Category.{v₂} E] [HasZeroObject E] [HasShift E ℤ] [Preadditive E]
  [∀ n : ℤ, (shiftFunctor E n).Additive] [Pretriangulated E]
  (G : D ⥤ E) [G.CommShift ℤ] [G.IsTriangulated]
  {F : ℕᵒᵖ ⥤ D} [HasProduct fun n : ℕ ↦ F.obj ⟨n⟩]
  [HasProduct fun n : ℕ ↦ (F ⋙ G).obj ⟨n⟩]
  [PreservesLimit (Discrete.functor fun n : ℕ ↦ F.obj ⟨n⟩) G]

/-- The product of the images of the terms, at the spelling `fun n ↦ G.obj (F.obj ⟨n⟩)` that
`CategoryTheory.Limits.PreservesProduct.iso` produces. It is the family
`fun n ↦ (F ⋙ G).obj ⟨n⟩` whose product the derived-limit predicate for `F ⋙ G` assumes, but
the two spellings are not syntactically equal and instance search does not cross them. -/
local instance hasProduct_map_obj : HasProduct fun n : ℕ ↦ G.obj (F.obj ⟨n⟩) :=
  inferInstanceAs (HasProduct fun n : ℕ ↦ (F ⋙ G).obj ⟨n⟩)

/-- The product comparison isomorphism `G(∏ₙ Fₙ) ≅ ∏ₙ G(Fₙ)` of
`CategoryTheory.Limits.PreservesProduct.iso`, with its target ascribed into the spelling
`∏ᶜ fun n ↦ (F ⋙ G).obj ⟨n⟩` that the derived-limit predicate for `F ⋙ G` is written with.
Without the ascription every `CategoryTheory.Limits.Pi.hom_ext` below picks up the other
spelling of the family from the type of this map, and then `Limits.Pi.lift_comp_π` does not fire. -/
def productOverIso :
    G.obj (∏ᶜ fun n : ℕ ↦ F.obj ⟨n⟩) ≅ ∏ᶜ fun n : ℕ ↦ (F ⋙ G).obj ⟨n⟩ :=
  PreservesProduct.iso G (fun n : ℕ ↦ F.obj ⟨n⟩)

omit [HasZeroObject D] [HasShift D ℤ] [Preadditive D] [∀ n : ℤ, (shiftFunctor D n).Additive]
  [Pretriangulated D] [HasZeroObject E] [HasShift E ℤ] [Preadditive E]
  [∀ n : ℤ, (shiftFunctor E n).Additive] [Pretriangulated E] [G.CommShift ℤ] [G.IsTriangulated] in
/-- The product comparison isomorphism is compatible with the product projections. -/
@[reassoc]
theorem productOverIso_hom_comp_π (n : ℕ) :
    (productOverIso G (F := F)).hom ≫ Pi.π (fun n : ℕ ↦ (F ⋙ G).obj ⟨n⟩) n =
      G.map (Pi.π (fun n : ℕ ↦ F.obj ⟨n⟩) n) := by
  rw [productOverIso, PreservesProduct.iso_hom]
  exact piComparison_comp_π G (fun n : ℕ ↦ F.obj ⟨n⟩) n

variable {K : D} {π : ∀ n : ℕ, K ⟶ F.obj ⟨n⟩}

omit [HasZeroObject D] [HasShift D ℤ] [Preadditive D] [∀ n : ℤ, (shiftFunctor D n).Additive]
  [Pretriangulated D] [HasZeroObject E] [HasShift E ℤ] [Preadditive E]
  [∀ n : ℤ, (shiftFunctor E n).Additive] [Pretriangulated E] [G.CommShift ℤ] [G.IsTriangulated] in
/-- The image of the product of a family of maps into the terms is the product of the images. -/
theorem map_pi_lift_comp_productOverIso_hom :
    G.map (Pi.lift (f := fun n : ℕ ↦ F.obj ⟨n⟩) π) ≫
        (productOverIso G (F := F)).hom =
      Pi.lift (f := fun n : ℕ ↦ (F ⋙ G).obj ⟨n⟩) fun n : ℕ ↦ G.map (π n) := by
  refine Pi.hom_ext _ _ fun n ↦ ?_
  rw [Pi.lift_comp_π, Category.assoc, productOverIso_hom_comp_π, ← G.map_comp, Pi.lift_comp_π]

/-- The image of the Milnor difference map of `F` is the Milnor difference map of `F ⋙ G`,
through the product comparison isomorphism. -/
theorem map_milnorDifference_comp_productOverIso_hom :
    G.map (Pi.lift (f := fun n : ℕ ↦ F.obj ⟨n⟩) fun n : ℕ ↦
          Pi.π (fun n : ℕ ↦ F.obj ⟨n⟩) n -
            Pi.π (fun n : ℕ ↦ F.obj ⟨n⟩) (n + 1) ≫ F.map (homOfLE (Nat.le_succ n)).op) ≫
        (productOverIso G (F := F)).hom =
      (productOverIso G (F := F)).hom ≫
        Pi.lift (f := fun n : ℕ ↦ (F ⋙ G).obj ⟨n⟩) fun n : ℕ ↦
          Pi.π (fun n : ℕ ↦ (F ⋙ G).obj ⟨n⟩) n -
            Pi.π (fun n : ℕ ↦ (F ⋙ G).obj ⟨n⟩) (n + 1) ≫
              (F ⋙ G).map (homOfLE (Nat.le_succ n)).op := by
  refine Pi.hom_ext _ _ fun n ↦ ?_
  simp only [Category.assoc]
  rw [Pi.lift_comp_π, productOverIso_hom_comp_π, ← G.map_comp, Pi.lift_comp_π, G.map_sub, G.map_comp,
    Preadditive.comp_sub, productOverIso_hom_comp_π, ← Category.assoc,
    productOverIso_hom_comp_π]
  rfl

/-- **A triangulated functor preserving the product of the terms carries a derived-limit
presentation with projections to one of the composite system.** If the maps `π n : K ⟶ Fₙ` are
the projections of a derived-limit presentation of `F` at `K`, then the maps `G(π n)` are the
projections of a derived-limit presentation of `F ⋙ G` at `G(K)`.

The image of the presenting triangle is distinguished, and the product comparison isomorphism
identifies it with the triangle whose first map is the product of the `G(π n)` and whose second
map is the Milnor difference of `F ⋙ G`. -/
theorem IsDerivedLimitWithProjections.map
    (h : IsDerivedLimitWithProjections F K π) :
    IsDerivedLimitWithProjections (F ⋙ G) (G.obj K) fun n : ℕ ↦ G.map (π n) := by
  obtain ⟨δ, hT⟩ := h
  refine ⟨(productOverIso G (F := F)).inv ≫ G.map δ ≫
    (G.commShiftIso (1 : ℤ)).hom.app K, ?_⟩
  refine isomorphic_distinguished _ (G.map_distinguished _ hT) _
    (Triangle.isoMk _ _ (Iso.refl _)
      (productOverIso G (F := F)).symm (productOverIso G (F := F)).symm ?_ ?_ ?_)
  all_goals dsimp [Functor.mapTriangle]
  · rw [Iso.comp_inv_eq, Category.id_comp, map_pi_lift_comp_productOverIso_hom]
    rfl
  · rw [Iso.comp_inv_eq, Category.assoc,
      map_milnorDifference_comp_productOverIso_hom, Iso.inv_hom_id_assoc]
    rfl
  · rw [CategoryTheory.Functor.map_id, Category.comp_id]

/-! ### Transport along an isomorphism of inverse systems -/

/-- **A natural isomorphism of inverse systems has eventual inverses.** Take the later level to
be the level itself and the backward map to be the inverse; both composites are identities, which
are the transition maps at the identity step.

`NoetherianAdicCompletion.HasEventualInverses` is the form of the pro-isomorphisms of
[Stacks, Tag 0921], and this is the degenerate case of one that needs no reindexing at all —
which is what makes `NoetherianAdicCompletion.IsDerivedLimitWithProjections`
`.comp_of_hasEventualInverses` into a transport of a derived-limit presentation along an
isomorphism of the system, carrying the projections along with it. -/
theorem hasEventualInverses_hom {C : Type u₁} [Category.{v₁} C] {F G : ℕᵒᵖ ⥤ C} (α : F ≅ G) :
    HasEventualInverses α.hom := fun n ↦ ⟨n, le_rfl, α.inv.app (op n), by simp, by simp⟩

/-! ### Transport along a functor that is exact only up to a connecting map -/

section ExistsDistinguished

variable {D' : Type u₁} [Category.{v₁} D'] [HasZeroObject D'] [HasShift D' ℤ] [Preadditive D']
  [∀ n : ℤ, (shiftFunctor D' n).Additive] [Pretriangulated D']
  {E' : Type u₂} [Category.{v₂} E'] [HasZeroObject E'] [HasShift E' ℤ] [Preadditive E']
  [∀ n : ℤ, (shiftFunctor E' n).Additive] [Pretriangulated E']

/-- **A derived-limit presentation is carried along an additive functor which preserves the
product of the terms and sends each distinguished triangle to a distinguished triangle on the
same two first maps.** This is `NoetherianAdicCompletion.IsDerivedLimitWithProjections.map` for a
functor that is not known to be triangulated: only the existence of *some* connecting map for the
image of each distinguished triangle is asked, which is the form in which the library proves the
exactness of the derived internal Hom in either variable ([Stacks, Tag 08JC]), and the
presentation needs nothing more since its own connecting map is existentially bound. -/
theorem IsDerivedLimitWithProjections.map_of_exists_distinguished
    (G : D' ⥤ E') [G.Additive]
    (hG : ∀ T ∈ distTriang D', ∃ δ : G.obj T.obj₃ ⟶ (G.obj T.obj₁)⟦(1 : ℤ)⟧,
      Triangle.mk (G.map T.mor₁) (G.map T.mor₂) δ ∈ distTriang E')
    {F : ℕᵒᵖ ⥤ D'} [HasProduct fun n : ℕ ↦ F.obj ⟨n⟩]
    [HasProduct fun n : ℕ ↦ (F ⋙ G).obj ⟨n⟩]
    [PreservesLimit (Discrete.functor fun n : ℕ ↦ F.obj ⟨n⟩) G]
    {K : D'} {π : ∀ n : ℕ, K ⟶ F.obj ⟨n⟩} (h : IsDerivedLimitWithProjections F K π) :
    IsDerivedLimitWithProjections (F ⋙ G) (G.obj K) fun n : ℕ ↦ G.map (π n) := by
  have : HasProduct fun n : ℕ ↦ G.obj (F.obj ⟨n⟩) :=
    inferInstanceAs (HasProduct fun n : ℕ ↦ (F ⋙ G).obj ⟨n⟩)
  have he (n : ℕ) : (productOverIso G (F := F)).hom ≫ Pi.π (fun n : ℕ ↦ G.obj (F.obj ⟨n⟩)) n =
      G.map (Pi.π (fun n : ℕ ↦ F.obj ⟨n⟩) n) :=
    productOverIso_hom_comp_π G n
  obtain ⟨δ, hT⟩ := h
  obtain ⟨δ', hT'⟩ := hG _ hT
  refine ⟨(productOverIso G).inv ≫ δ', isomorphic_distinguished _ hT' _
    (Triangle.isoMk _ _ (Iso.refl _) (productOverIso G).symm (productOverIso G).symm ?_ ?_ ?_)⟩
  all_goals dsimp
  · rw [Iso.comp_inv_eq, Category.id_comp, map_pi_lift_comp_productOverIso_hom]
    rfl
  · rw [Iso.comp_inv_eq, Category.assoc, Iso.eq_inv_comp]
    refine Pi.hom_ext _ _ fun n ↦ ?_
    rw [Category.assoc, Pi.lift_comp_π, Preadditive.comp_sub, ← Category.assoc, he, he (n + 1),
      Category.assoc, he, ← G.map_comp, ← G.map_comp, ← G.map_sub, Pi.lift_comp_π]
  · rw [CategoryTheory.Functor.map_id, Category.comp_id]

end ExistsDistinguished

end NoetherianAdicCompletion

end
