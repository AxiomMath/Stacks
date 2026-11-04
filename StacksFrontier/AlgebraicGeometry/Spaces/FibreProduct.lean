module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.AlgebraicGeometry.Spaces.SectionFibre

/-!
# Fibre products of algebraic spaces

Let `S` be a scheme contained in a big fppf site `B`. A fibre product of two algebraic spaces
over `S`, taken over an fppf sheaf with representable diagonal, is again an algebraic space over
`S`.

## Main results

* `AlgebraicGeometry.isAlgebraicSpace_of_isPullback`: the fibre product of a cartesian square of
  this shape is an algebraic space.
* `AlgebraicGeometry.isAlgebraicSpace_pullback_of_representable_diagonal`: the chosen presheaf
  fibre product is an algebraic space.
* `CategoryTheory.MorphismProperty.prod_map_mem` and
  `CategoryTheory.MorphismProperty.diag_mem_of_prod`: a morphism property stable under base
  change and composition contains products of its morphisms, and the diagonal of a product
  whose factors have diagonals in it.

## References

* [Stacks Project, Tag 04T9](https://stacks.math.columbia.edu/tag/04T9)
* [Stacks Project, Tag 02X2](https://stacks.math.columbia.edu/tag/02X2)
* [Stacks Project, Tag 025Y](https://stacks.math.columbia.edu/tag/025Y)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Limits

universe v u

variable {C : Type u} [Category.{v} C] [HasBinaryProducts C]

/-- `prod.map f (𝟙 Z) : X ⨯ Z ⟶ Y ⨯ Z` is the base change of `f : X ⟶ Y` along the first
projection `Y ⨯ Z ⟶ Y`. -/
@[ega "I 3.3.2" "partial"]
lemma isPullback_prod_map_id_right {X Y : C} (f : X ⟶ Y) (Z : C) :
    IsPullback (prod.fst : X ⨯ Z ⟶ X) (prod.map f (𝟙 Z)) f (prod.fst : Y ⨯ Z ⟶ Y) :=
  IsPullback.of_isLimit (PullbackCone.IsLimit.mk (by simp)
    (fun s => prod.lift s.fst (s.snd ≫ prod.snd)) (fun s => by simp)
    (fun s => prod.hom_ext (by simpa using s.condition) (by simp))
    (fun s l h₁ h₂ => prod.hom_ext (by simpa using h₁)
      (by simpa using h₂ =≫ (prod.snd : Y ⨯ Z ⟶ Z))))

/-- `prod.map (𝟙 Z) f : Z ⨯ X ⟶ Z ⨯ Y` is the base change of `f : X ⟶ Y` along the second
projection `Z ⨯ Y ⟶ Y`. -/
@[ega "I 3.3.2" "partial"]
lemma isPullback_prod_map_id_left {X Y : C} (f : X ⟶ Y) (Z : C) :
    IsPullback (prod.snd : Z ⨯ X ⟶ X) (prod.map (𝟙 Z) f) f (prod.snd : Z ⨯ Y ⟶ Y) :=
  IsPullback.of_isLimit (PullbackCone.IsLimit.mk (by simp)
    (fun s => prod.lift (s.snd ≫ prod.fst) s.fst) (fun s => by simp)
    (fun s => prod.hom_ext (by simp) (by simpa using s.condition))
    (fun s l h₁ h₂ => prod.hom_ext (by simpa using h₂ =≫ (prod.fst : Z ⨯ Y ⟶ Z))
      (by simpa using h₁)))

/-- The canonical isomorphism `(X ⨯ X') ⨯ (Y ⨯ Y') ≅ (X ⨯ Y) ⨯ (X' ⨯ Y')` exchanging the two
middle factors. -/
@[simps]
noncomputable def prodProdProdComm (X X' Y Y' : C) :
    (X ⨯ X') ⨯ (Y ⨯ Y') ≅ (X ⨯ Y) ⨯ (X' ⨯ Y') where
  hom := prod.lift (prod.map prod.fst prod.fst) (prod.map prod.snd prod.snd)
  inv := prod.lift (prod.map prod.fst prod.fst) (prod.map prod.snd prod.snd)
  hom_inv_id := by ext <;> simp
  inv_hom_id := by ext <;> simp

/-- The diagonal of a binary product is the product of the diagonals, followed by the
reshuffling isomorphism `prodProdProdComm`. -/
lemma diag_prod_eq (X Y : C) :
    diag (X ⨯ Y) = prod.map (diag X) (diag Y) ≫ (prodProdProdComm X X Y Y).hom := by
  ext <;> simp

/-- The morphism `prod.lift` of the two projections of a cartesian square is a
monomorphism. -/
lemma mono_prodLift {W X Y Z : C} {f : X ⟶ W} {g : Y ⟶ W} {p : Z ⟶ X} {q : Z ⟶ Y}
    (h : IsPullback p q f g) : Mono (prod.lift p q) := by
  refine ⟨fun {T} u v huv => h.hom_ext ?_ ?_⟩
  · simpa using huv =≫ (prod.fst : X ⨯ Y ⟶ X)
  · simpa using huv =≫ (prod.snd : X ⨯ Y ⟶ Y)

end CategoryTheory.Limits

namespace CategoryTheory.MorphismProperty

universe v u

variable {C : Type u} [Category.{v} C] [HasBinaryProducts C]

/-- A morphism property stable under base change and under composition contains the product of
two of its morphisms. -/
@[sga "3 IV 3.4.1" "special case"]
lemma prod_map_mem (P : MorphismProperty C) [P.IsStableUnderBaseChange]
    [P.IsStableUnderComposition] {X Y X' Y' : C} {u : X ⟶ Y} {v : X' ⟶ Y'}
    (hu : P u) (hv : P v) : P (prod.map u v) := by
  have h : prod.map u v = prod.map u (𝟙 X') ≫ prod.map (𝟙 Y) v := by ext <;> simp
  rw [h]
  exact P.comp_mem _ _
    (IsStableUnderBaseChange.of_isPullback (isPullback_prod_map_id_right u X') hu)
    (IsStableUnderBaseChange.of_isPullback (isPullback_prod_map_id_left v Y) hv)

/-- A morphism property stable under base change and under composition contains the diagonal of
a binary product as soon as it contains the diagonals of the two factors. -/
lemma diag_mem_of_prod (P : MorphismProperty C) [P.IsStableUnderBaseChange]
    [P.IsStableUnderComposition] {X Y : C} (hX : P (diag X)) (hY : P (diag Y)) :
    P (diag (X ⨯ Y)) := by
  rw [diag_prod_eq X Y]
  exact RespectsIso.postcomp P _ _ (prod_map_mem P hX hY)

end CategoryTheory.MorphismProperty

namespace AlgebraicGeometry

universe u

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {F G H Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- Let `F` and `G` be algebraic spaces over `S`, let `H` be an fppf sheaf on the big fppf site of
`S` whose diagonal is representable, and let `f : F ⟶ H` and `g : G ⟶ H`. Then a fibre product
`Z` of `f` and `g` is an algebraic space over `S`. -/
@[stacks 04T9]
theorem isAlgebraicSpace_of_isPullback
    (hF : IsAlgebraicSpace B S hS F) (hG : IsAlgebraicSpace B S hS G)
    (hHsheaf : Presheaf.IsSheaf (BigFppfOver.topology B S hS) H)
    (hHdiag : yoneda.relativelyRepresentable (diag H))
    {f : F ⟶ H} {g : G ⟶ H} {p : Z ⟶ F} {q : Z ⟶ G} (hZ : IsPullback p q f g) :
    IsAlgebraicSpace B S hS Z := by
  have _ : HasBinaryProducts (BigFppfOver B S hS) :=
    hasBinaryProducts_of_hasTerminal_and_pullbacks _
  have hsheaf : Presheaf.IsSheaf (BigFppfOver.topology B S hS) Z := by
    refine ObjectProperty.prop_of_isLimit _ hZ.isLimit fun j ↦ ?_
    match j with
    | none => exact hHsheaf
    | some WalkingPair.left => exact hF.isSheaf
    | some WalkingPair.right => exact hG.isSheaf
  have _ : Mono (prod.lift p q) := mono_prodLift hZ
  have hdiag : yoneda.relativelyRepresentable (diag Z) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (isPullback_diag_of_mono (prod.lift p q))
      (MorphismProperty.diag_mem_of_prod _ hF.diagonal_representable hG.diagonal_representable)
  obtain ⟨U, a, ha₁, ha₂⟩ := hF.exists_atlas
  obtain ⟨V, b, hb₁, hb₂⟩ := hG.exists_atlas
  obtain ⟨W, w, wfst, hW⟩ := Functor.relativelyRepresentable.of_diag hHdiag (a ≫ f) (b ≫ g)
  have hUG : IsPullback (pullback.fst (a ≫ f) g) (pullback.snd (a ≫ f) g) (a ≫ f) g :=
    IsPullback.of_hasPullback _ _
  obtain ⟨τ, hτ⟩ : ∃ τ, IsPullback (pullback.fst (a ≫ f) g) τ a p :=
    ⟨_, IsPullback.of_bot' hUG hZ⟩
  obtain ⟨ρ, hρ⟩ : ∃ ρ, IsPullback (yoneda.map w) ρ b (pullback.snd (a ≫ f) g) :=
    ⟨_, IsPullback.of_bot' hW.flip hUG.flip⟩
  refine ⟨hsheaf, hdiag, W, ρ ≫ τ, ?_, ?_⟩ <;>
  exact MorphismProperty.comp_mem _ _ _
    ((MorphismProperty.relative_isStableUnderBaseChange (F := yoneda) _).of_isPullback hρ ‹_›)
    ((MorphismProperty.relative_isStableUnderBaseChange (F := yoneda) _).of_isPullback hτ ‹_›)

/-- The chosen presheaf fibre product of two algebraic spaces over an fppf sheaf with
representable diagonal is an algebraic space. -/
@[stacks 04T9 "the chosen presheaf fibre product"]
theorem isAlgebraicSpace_pullback_of_representable_diagonal
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F G H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : F ⟶ H) (g : G ⟶ H)
    (hF : IsAlgebraicSpace B S hS F) (hG : IsAlgebraicSpace B S hS G)
    (hH : Presheaf.IsSheaf (BigFppfOver.topology B S hS) H)
    (hdiag : yoneda.relativelyRepresentable (diag H)) :
    IsAlgebraicSpace B S hS (pullback f g) :=
  isAlgebraicSpace_of_isPullback hF hG hH hdiag (IsPullback.of_hasPullback f g)

end AlgebraicGeometry

end
