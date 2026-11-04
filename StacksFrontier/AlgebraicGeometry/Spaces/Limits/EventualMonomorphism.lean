module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Limits.RelativeApproximation.ClosedImmersionDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.DescendingProperties.Separated
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteEtaleAtlasQuasiSeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.EventualIsomorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiCompact

/-!
# Monomorphisms into a directed limit of algebraic spaces

Let `X = lim Xᵢ` be a directed inverse limit of quasi-separated algebraic spaces over a base
algebraic space, with affine transition morphisms.  A monomorphism `Y ⟶ X` whose source is
quasi-compact and locally of finite type over the base is already a monomorphism into `Xᵢ` for
all sufficiently large `i`.

## Main results

* `AlgebraicGeometry.Space.eventually_mono_comp_limitπ`: the eventual monomorphism at the
  stages of the inverse system, which is **Stacks 0828, part (4)**.

## Implementation notes

The proof follows the Stacks project.  The fibre products `Zᵢ = Y ×_{Xᵢ} Y` form an inverse
system whose transition morphisms are base changes of the relative diagonals of the affine,
hence separated, transition morphisms `Xⱼ ⟶ Xᵢ`, so they are closed immersions.  Because
`Y ⟶ X` is a monomorphism, the diagonals `Y ⟶ Zᵢ` form a limiting cone.  Over the tail of the
index preorder above a stage `i₀`, the system `Zᵢ` is a system of quasi-compact algebraic spaces
over `Z_{i₀}` whose source `Y` is locally of finite presentation over `Z_{i₀}` (the relative
diagonal of a morphism locally of finite type), so the eventual isomorphism of Stacks 0828,
part (3), applies to it: the diagonal `Y ⟶ Y ×_{Xᵢ} Y` is an isomorphism for `i` large, which
says that `Y ⟶ Xᵢ` is a monomorphism.

## References

* [Stacks Project, Tag 0828](https://stacks.math.columbia.edu/tag/0828)
* [Stacks Project, Tag 03KN](https://stacks.math.columbia.edu/tag/03KN)
* [Stacks Project, Tag 084P](https://stacks.math.columbia.edu/tag/084P)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Filter Opposite

universe u v

namespace CategoryTheory.Limits

variable {C : Type*} [Category* C] [HasPullbacks C]

/-- The comparison `Y ×_P Y' ⟶ Y ×_Q Y'` induced by a morphism `i : P ⟶ Q` is a base change of
the relative diagonal of `i`.  This is `CategoryTheory.Limits.pullback_map_diagonal_isPullback`
with the two composites `a ≫ i`, `b ≫ i` replaced by morphisms equal to them. -/
theorem isPullback_map_diagonal_of_comp_eq {Y Y' P Q : C} (a : Y ⟶ P) (b : Y' ⟶ P)
    (i : P ⟶ Q) (a' : Y ⟶ Q) (b' : Y' ⟶ Q) (ha : a ≫ i = a') (hb : b ≫ i = b') :
    IsPullback (pullback.fst a b ≫ a)
      (pullback.map a b a' b' (𝟙 Y) (𝟙 Y') i (by simp [ha]) (by simp [hb]))
      (pullback.diagonal i)
      (pullback.map a' b' i i a b (𝟙 Q) (by simp [ha]) (by simp [hb])) := by
  subst ha hb
  exact pullback_map_diagonal_isPullback a b i

namespace Cone

variable {J : Type*} [Category* J] {D : J ⥤ C} (c : Cone D) {Y : C} (f : Y ⟶ c.pt)

/-- The inverse system of the kernel pairs `Y ×_{D j} Y` of the composites `Y ⟶ c.pt ⟶ D j`,
with the transition morphisms induced by those of `D`. -/
noncomputable abbrev kernelPairDiagram : J ⥤ C where
  obj j := pullback (f ≫ c.π.app j) (f ≫ c.π.app j)
  map {j k} φ := pullback.map _ _ _ _ (𝟙 Y) (𝟙 Y) (D.map φ) (by simp) (by simp)
  map_id j := by apply pullback.hom_ext <;> simp
  map_comp φ ψ := by apply pullback.hom_ext <;> simp

/-- The transition morphisms of the system of kernel pairs commute with the first projections
`pullback.fst`. -/
@[reassoc (attr := simp)]
theorem kernelPairDiagram_map_fst {j k : J} (φ : j ⟶ k) :
    (c.kernelPairDiagram f).map φ ≫ pullback.fst _ _ = pullback.fst _ _ := by
  simp [kernelPairDiagram]

/-- The transition morphisms of the system of kernel pairs commute with the second projections
`pullback.snd`. -/
@[reassoc (attr := simp)]
theorem kernelPairDiagram_map_snd {j k : J} (φ : j ⟶ k) :
    (c.kernelPairDiagram f).map φ ≫ pullback.snd _ _ = pullback.snd _ _ := by
  simp [kernelPairDiagram]

/-- Each transition morphism of the system of kernel pairs is a base change of the relative
diagonal of the corresponding transition morphism of `D`. -/
theorem isPullback_kernelPairDiagram_map {j k : J} (φ : j ⟶ k) :
    IsPullback (pullback.fst _ _ ≫ f ≫ c.π.app j) ((c.kernelPairDiagram f).map φ)
      (pullback.diagonal (D.map φ))
      (pullback.map _ _ _ _ (f ≫ c.π.app j) (f ≫ c.π.app j) (𝟙 (D.obj k)) (by simp)
        (by simp)) :=
  isPullback_map_diagonal_of_comp_eq (f ≫ c.π.app j) (f ≫ c.π.app j) (D.map φ)
    (f ≫ c.π.app k) (f ≫ c.π.app k) (by simp) (by simp)

/-- The cone of relative diagonals `Y ⟶ Y ×_{D j} Y` over the system of kernel pairs. -/
noncomputable abbrev kernelPairDiagonalCone : Cone (c.kernelPairDiagram f) where
  pt := Y
  π :=
    { app := fun j => pullback.diagonal (f ≫ c.π.app j)
      naturality := fun j k φ => by apply pullback.hom_ext <;> simp [kernelPairDiagram] }

/-- Over a cofiltered index category, the relative diagonals of a monomorphism into the cone
point of a limiting cone form a limiting cone over the kernel pairs at the stages: the limit of
the kernel pairs is the kernel pair `Y ×_{c.pt} Y`, which is `Y` as `f` is a monomorphism. -/
noncomputable def isLimitKernelPairDiagonalCone [IsCofiltered J] (hc : IsLimit c) [Mono f] :
    IsLimit (c.kernelPairDiagonalCone f) := by
  have j₀ : J := Classical.choice IsCofiltered.nonempty
  have hfst : ∀ (σ : Cone (c.kernelPairDiagram f)) (j : J),
      σ.π.app j ≫ pullback.fst _ _ = σ.π.app j₀ ≫ pullback.fst _ _ := fun σ j => by
    rw [← σ.w (IsCofiltered.minToLeft j j₀), ← σ.w (IsCofiltered.minToRight j j₀),
      Category.assoc, Category.assoc, kernelPairDiagram_map_fst, kernelPairDiagram_map_fst]
  have hsnd : ∀ (σ : Cone (c.kernelPairDiagram f)) (j : J),
      σ.π.app j ≫ pullback.snd _ _ = σ.π.app j₀ ≫ pullback.snd _ _ := fun σ j => by
    rw [← σ.w (IsCofiltered.minToLeft j j₀), ← σ.w (IsCofiltered.minToRight j j₀),
      Category.assoc, Category.assoc, kernelPairDiagram_map_snd, kernelPairDiagram_map_snd]
  have hfstsnd : ∀ σ : Cone (c.kernelPairDiagram f),
      σ.π.app j₀ ≫ pullback.fst _ _ = σ.π.app j₀ ≫ pullback.snd _ _ := fun σ => by
    refine (cancel_mono f).1 (hc.hom_ext fun j => ?_)
    have h := σ.π.app j ≫= pullback.condition (f := f ≫ c.π.app j) (g := f ≫ c.π.app j)
    rw [reassoc_of% (hfst σ j), reassoc_of% (hsnd σ j)] at h
    simpa only [Category.assoc] using h
  exact
    { lift := fun σ => σ.π.app j₀ ≫ pullback.fst _ _
      fac := fun σ j => by
        apply pullback.hom_ext
        · simpa using (hfst σ j).symm
        · simpa [hfstsnd σ] using (hsnd σ j).symm
      uniq := fun σ m hm => by
        rw [← hm j₀]
        simp }

end Cone

end CategoryTheory.Limits

namespace AlgebraicGeometry.Space

/-- **Stacks 0828, part (4).** Let `X = lim Xᵢ` be a directed limit of algebraic spaces over an
algebraic space `Bspace`, with affine transition morphisms and quasi-separated stages, and let
`f : Y ⟶ X` be a monomorphism whose source is quasi-compact and locally of finite type over
`Bspace`.  Then `Y ⟶ Xᵢ` is a monomorphism for all sufficiently large `i`. -/
@[stacks 0828 "part (4): monomorphism"]
theorem eventually_mono_comp_limitπ
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (contains : B.Contains S)
    {I : Type v} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (Bspace : (BigFppfOver B S contains)ᵒᵖ ⥤ Type u)
    (algebraicBase : IsAlgebraicSpace B S contains Bspace)
    (D : Iᵒᵖ ⥤ (BigFppfOver B S contains)ᵒᵖ ⥤ Type u)
    (algebraicStage : ∀ i, IsAlgebraicSpace B S contains (D.obj (op i)))
    (t : D ⟶ (Functor.const Iᵒᵖ).obj Bspace)
    (c : Cone D) (isLimit : IsLimit c) (s : c.pt ⟶ Bspace)
    (commutes : c.π ≫ t = (Functor.const Iᵒᵖ).map s)
    (Y : (BigFppfOver B S contains)ᵒᵖ ⥤ Type u) (algebraic : IsAlgebraicSpace B S contains Y)
    (quasiCompact : IsQuasiCompactSpace B S contains Y)
    (f : Y ⟶ c.pt) [Mono f]
    (affine : ∀ ⦃i j : I⦄ (h : i ≤ j), IsAffineHom B S contains (D.map (homOfLE h).op))
    (quasiSeparated : ∀ i,
      IsAbsolutelyQuasiSeparated B S contains B.contains_terminal (D.obj (op i)))
    (finiteType : IsLocallyOfFiniteType B S contains (f ≫ s)) :
    ∀ᶠ i in atTop, Mono (f ≫ c.π.app (op i)) := by
  classical
  obtain ⟨i₀⟩ := ‹Nonempty I›
  -- The system `Zₐ = Y ×_{Xₐ} Y` of kernel pairs and the cone of diagonals over it.
  let Z := c.kernelPairDiagram f
  let δ := c.kernelPairDiagonalCone f
  have hδ : IsLimit δ := c.isLimitKernelPairDiagonalCone f isLimit
  -- Its transition morphisms are closed immersions.
  have hAffineOp : ∀ {a b : Iᵒᵖ} (φ : a ⟶ b), IsAffineHom B S contains (D.map φ) := by
    intro a b φ
    have h : b.unop ≤ a.unop := leOfHom φ.unop
    rw [show φ = (homOfLE h).op from Subsingleton.elim _ _]
    exact affine h
  have _ : MorphismProperty.IsStableUnderBaseChange
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@_root_.AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S contains))) :=
    MorphismProperty.relative_isStableUnderBaseChange _
  have hZclosed : ∀ {a b : Iᵒᵖ} (φ : a ⟶ b), IsClosedImmersion B S contains (Z.map φ) :=
    fun {a b} φ => MorphismProperty.of_isPullback (c.isPullback_kernelPairDiagram_map f φ)
      (isSeparated_of_isAffineHom B S contains (D.map φ) (algebraicStage a.unop)
        (algebraicStage b.unop) (hAffineOp φ))
  have hZalg : ∀ a : Iᵒᵖ, IsAlgebraicSpace B S contains (Z.obj a) := fun a =>
    isAlgebraicSpace_pullback B S contains _ _ algebraic algebraic (algebraicStage a.unop)
  -- The tail of the index preorder above `i₀`, with its inclusion into `Iᵒᵖ`.
  have : Nonempty (LimitTail I i₀) := ⟨⟨i₀, le_rfl⟩⟩
  have : IsDirected (LimitTail I i₀) (· ≤ ·) := by
    refine ⟨fun x y => ?_⟩
    obtain ⟨k, hxk, hyk⟩ := IsDirected.directed (r := (· ≤ ·)) x.1 y.1
    exact ⟨⟨k, x.2.trans hxk⟩, hxk, hyk⟩
  let G : (LimitTail I i₀)ᵒᵖ ⥤ Iᵒᵖ :=
    (limitTailOverEquiv i₀).functor ⋙ Over.forget (op i₀)
  have : G.Initial := by dsimp only [G]; infer_instance
  have hδt : IsLimit (δ.whisker G) := (Functor.Initial.isLimitWhiskerEquiv G δ).symm hδ
  -- The tail system lies over `Z_{i₀}`.
  let τ : (G ⋙ Z) ⟶ (Functor.const ((LimitTail I i₀)ᵒᵖ)).obj (Z.obj (op i₀)) :=
    { app := fun j => Z.map (homOfLE j.unop.2).op
      naturality := fun j k φ =>
        ((Z.map_comp (G.map φ) ((homOfLE k.unop.2).op)).symm.trans
            (congrArg (fun x : G.obj j ⟶ op i₀ => Z.map x) (Subsingleton.elim _ _))).trans
          (Category.comp_id _).symm }
  have hτ : (δ.whisker G).π ≫ τ =
      (Functor.const ((LimitTail I i₀)ᵒᵖ)).map (δ.π.app (op i₀)) :=
    NatTrans.ext (funext fun j => (δ.w (homOfLE j.unop.2).op).trans (Category.id_comp _).symm)
  have hgFT : IsLocallyOfFiniteType B S contains (f ≫ c.π.app (op i₀)) := by
    refine isLocallyOfFiniteType_of_comp B S contains algebraic (algebraicStage i₀)
      algebraicBase _ (t.app (op i₀)) ?_
    have hi : c.π.app (op i₀) ≫ t.app (op i₀) = s := by
      simpa using congrArg (fun η => η.app (op i₀)) commutes
    simpa only [Category.assoc, hi] using finiteType
  -- Part (3) at the tail system.
  have hres := eventually_isIso_comp_limitπ B S contains (Z.obj (op i₀)) (hZalg (op i₀))
    (G ⋙ Z) (fun j => hZalg (op j.1)) τ (δ.whisker G) hδt (δ.π.app (op i₀)) hτ Y algebraic
    (𝟙 Y) (IsIso.id Y)
    (fun j => isQuasiCompactSpace_pullback B S contains B.contains_terminal _ _ algebraic
      (algebraicStage j.1) quasiCompact quasiCompact (quasiSeparated j.1))
    (fun j => isLocallyOfFiniteType_of_isClosedImmersion B S contains _
      (hZclosed (homOfLE j.2).op))
    (fun x y h => hZclosed (G.map (homOfLE h).op))
    (by
      convert isLocallyOfFinitePresentation_pullbackDiagonal B S contains _ algebraic
        (algebraicStage i₀) hgFT using 1
      exact Category.id_comp _)
  obtain ⟨j₀, hj₀⟩ := eventually_atTop.1 hres
  refine eventually_atTop.2 ⟨j₀.1, fun i hi => ?_⟩
  have hiso : IsIso (𝟙 Y ≫ pullback.diagonal (f ≫ c.π.app (op i))) := hj₀ ⟨i, j₀.2.trans hi⟩ hi
  rw [Category.id_comp] at hiso
  exact (pullback.isIso_diagonal_iff (f ≫ c.π.app (op i))).1 hiso

end AlgebraicGeometry.Space

end
