module

public import StacksFrontier.AlgebraicGeometry.Spaces.FactorThroughClosedSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescendingFiniteTypeLimitImage
public import StacksFrontier.AlgebraicGeometry.Size.Monomorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperClosedImmersion

/-!
# Closed subspaces agreeing on one surjective étale chart

Two closed subspaces of an algebraic space `X` are equal as soon as their base changes to one
surjective étale scheme chart `W ⟶ X` cut out the same ideal sheaf of `W`; and two closed
immersions into `X` with the same image are isomorphic over `X`.  These are the two steps by which
an equality of closed subspaces is reduced to schemes.

## Main results

* `AlgebraicGeometry.Space.closedSubspaceOfIsClosedImmersion`: the image of a closed immersion
  of algebraic spaces, as a closed subspace.
* `AlgebraicGeometry.Space.closedSubspace_le_of_ker_le_chart`: a closed subspace is contained in
  another as soon as the containment holds for the ideal sheaves of their base changes to one
  surjective étale scheme chart.
* `AlgebraicGeometry.Space.exists_iso_comp_eq_of_range_eq`: two closed immersions with the same
  image are isomorphic over the target.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The image of a closed immersion of algebraic spaces, as a closed subspace. -/
def closedSubspaceOfIsClosedImmersion {Z X : AlgebraicSpaces B S hS} (i : Z ⟶ X)
    (hi : IsClosedImmersion B S hS i.hom) : ClosedSubspaces B S hS X.1 :=
  ⟨Subfunctor.range i.hom, isClosedSubspace_range_of_isClosedImmersion B S hS i.hom Z.2 hi⟩

/-- **A closed subspace is contained in another as soon as this holds on one chart.**  Let
`f : W ⟶ X` be a surjective étale scheme chart.  If the ideal sheaf of the base change
`Z₂ ×_X W ⟶ W` is contained in that of `Z₁ ×_X W ⟶ W`, then `Z₁ ⊆ Z₂`: membership in a closed
subspace is checked after the surjective étale base change along `f`, where it is the
chart-local criterion of Stacks 03MB. -/
theorem closedSubspace_le_of_ker_le_chart (X : AlgebraicSpaces B S hS)
    (Z₁ Z₂ : ClosedSubspaces B S hS X.1) {W : BigFppfOver B S hS} (f : yoneda.obj W ⟶ X.1)
    (hfE : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) f)
    (hfS : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) f)
    (hle : ((BigFppfOver.toScheme B S hS).map (Z₂.2.2.rep.snd f)).ker ≤
      ((BigFppfOver.toScheme B S hS).map (Z₁.2.2.rep.snd f)).ker) :
    Z₁.1 ≤ Z₂.1 := by
  intro T x hx
  let U : SmallEtale B S hS X.1 := ⟨CostructuredArrow.mk f, hfE⟩
  set τ : yoneda.obj T.unop ⟶ X.1 := yonedaEquiv.symm x with hτ
  have hw : yoneda.map (hfE.rep.fst' τ) ≫ f = yoneda.map (hfE.rep.snd τ) ≫ τ :=
    hfE.rep.map_fst' τ ▸ hfE.rep.w τ
  have hval : X.1.map (hfE.rep.snd τ).op x =
      U.1.hom.app (op (hfE.rep.pullback τ)) (hfE.rep.fst' τ) := by
    rw [show U.1.hom = f from rfl,
      ← yonedaEquiv_yoneda_map_comp B S hS f (hfE.rep.fst' τ), hw,
      ← yonedaEquiv_naturality, hτ, Equiv.apply_symm_apply]
  refine mem_obj_of_surjective_etale B S hS X.2.isSheaf Z₂.1 Z₂.2.1.isSheaf
    (hfE.rep.snd τ) (hfS.property_snd τ) (hfE.property_snd τ) _ ?_
  rw [hval, mem_obj_iff_ker_le]
  exact hle.trans ((mem_obj_iff_ker_le B S hS X Z₁ U (hfE.rep.fst' τ)).1 (hval ▸ Z₁.1.map _ hx))

/-- **Two closed immersions with the same image are isomorphic over the target.** -/
theorem exists_iso_comp_eq_of_range_eq {Z Z' X : AlgebraicSpaces B S hS} (i : Z ⟶ X)
    (i' : Z' ⟶ X) (hi : IsClosedImmersion B S hS i.hom) (hi' : IsClosedImmersion B S hS i'.hom)
    (h : Subfunctor.range i.hom = Subfunctor.range i'.hom) :
    ∃ e : Z ≅ Z', e.hom ≫ i' = i := by
  have := mono_of_isClosedImmersion B S hS i.hom hi
  have := mono_of_isClosedImmersion B S hS i'.hom hi'
  let a : Z.1 ⟶ Z'.1 := Subfunctor.toRange i.hom ≫ Subfunctor.homOfLe h.le ≫
    inv (Subfunctor.toRange i'.hom)
  let b : Z'.1 ⟶ Z.1 := Subfunctor.toRange i'.hom ≫ Subfunctor.homOfLe h.ge ≫
    inv (Subfunctor.toRange i.hom)
  have hi'ι : inv (Subfunctor.toRange i'.hom) ≫ i'.hom = (Subfunctor.range i'.hom).ι := by
    rw [IsIso.inv_comp_eq, Subfunctor.toRange_ι]
  have hiι : inv (Subfunctor.toRange i.hom) ≫ i.hom = (Subfunctor.range i.hom).ι := by
    rw [IsIso.inv_comp_eq, Subfunctor.toRange_ι]
  have ha : a ≫ i'.hom = i.hom := by
    simp only [a, Category.assoc, hi'ι, Subfunctor.homOfLe_ι, Subfunctor.toRange_ι]
  have hb : b ≫ i.hom = i'.hom := by
    simp only [b, Category.assoc, hiι, Subfunctor.homOfLe_ι, Subfunctor.toRange_ι]
  refine ⟨⟨ObjectProperty.homMk a, ObjectProperty.homMk b, ObjectProperty.hom_ext _ ?_,
    ObjectProperty.hom_ext _ ?_⟩, ObjectProperty.hom_ext _ ha⟩
  · exact (cancel_mono i.hom).1 (by
      show (a ≫ b) ≫ i.hom = 𝟙 _ ≫ i.hom
      rw [Category.assoc, hb, ha, Category.id_comp])
  · exact (cancel_mono i'.hom).1 (by
      show (b ≫ a) ≫ i'.hom = 𝟙 _ ≫ i'.hom
      rw [Category.assoc, ha, hb, Category.id_comp])

/-- **The ideal sheaf of the base change of a closed subspace to a chart, read off its points.**
Let `U` be an étale scheme chart of `X` and `p : Y ⟶ U` a closed immersion of schemes such that a
point `k : a ⟶ U` of the chart lands in the closed subspace `Z` exactly when `k` factors through
`p`.  Then `p` and the base change `Z ×_X U ⟶ U` have the same ideal sheaf. -/
theorem ker_snd_eq_of_mem_iff (X : AlgebraicSpaces B S hS) (Z : ClosedSubspaces B S hS X.1)
    (U : SmallEtale B S hS X.1) {Y : Scheme.{u}}
    (p : Y ⟶ (BigFppfOver.toScheme B S hS).obj U.1.left)
    [_root_.AlgebraicGeometry.IsClosedImmersion p]
    (h : ∀ {a : BigFppfOver B S hS} (k : a ⟶ U.1.left),
      U.1.hom.app (op a) k ∈ Z.1.obj (op a) ↔
        ∃ τ : (BigFppfOver.toScheme B S hS).obj a ⟶ Y,
          τ ≫ p = (BigFppfOver.toScheme B S hS).map k) :
    ((BigFppfOver.toScheme B S hS).map (Z.2.2.rep.snd U.1.hom)).ker = p.ker := by
  refine le_antisymm ?_ ?_
  · have hY : Y.size < B.cutoff :=
      lt_of_le_of_lt (Scheme.size_le_of_mono_quasiCompact p) U.1.left.left.property
    let Y' : BigFppfOver B S hS := Over.mk (B.inclusion.preimage
      (show B.inclusion.obj ⟨Y, hY⟩ ⟶ B.inclusion.obj U.1.left.left from p) ≫ U.1.left.hom)
    let kY : Y' ⟶ U.1.left := Over.homMk (B.inclusion.preimage
      (show B.inclusion.obj ⟨Y, hY⟩ ⟶ B.inclusion.obj U.1.left.left from p)) rfl
    have hkY : (BigFppfOver.toScheme B S hS).map kY = p := B.inclusion.map_preimage _
    have hmem := (h kY).2 ⟨𝟙 _, by rw [hkY, Category.id_comp]⟩
    rwa [mem_obj_iff_ker_le, hkY] at hmem
  · obtain ⟨τ, hτ⟩ := (h (Z.2.2.rep.snd U.1.hom)).1 (by rw [mem_obj_iff_ker_le])
    exact hτ ▸ Scheme.Hom.le_ker_comp τ p

end AlgebraicGeometry.Space
