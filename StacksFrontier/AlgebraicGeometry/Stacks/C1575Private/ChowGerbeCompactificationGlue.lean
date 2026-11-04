module

public import StacksFrontier.AlgebraicGeometry.Stacks.ChowFiniteCoverFactorization
public import StacksFrontier.AlgebraicGeometry.Stacks.ChowGerbeCompactificationSection
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentingMapFunctorial

/-!
# Gluing sections of a stack over an algebraic space along a covering family

Let `f : 𝒳 ⟶ Y` be a 1-morphism from an algebraic stack to an algebraic space, `g : Z ⟶ Y` a
morphism of algebraic spaces and `U i ⊆ Z` subspaces covering `Z` locally. Given 1-morphisms
`x i : U i ⟶ 𝒳` with `f ∘ x i ≅ g|_{U i}` and transition 2-morphisms `x i ⟶ x j` over
`U i ∩ U j` satisfying the cocycle condition, the glued 1-morphism `x : Z ⟶ 𝒳` of
`AlgebraicGeometry.Stack.AlgebraicStacks.exists_algebraicSpaceStack_hom_of_cocycle` again
satisfies `f ∘ x ≅ g`. This is the descent step of the last paragraph of the proof of
[Stacks, Tag 0CQ7] ("$(x_i, \varphi_{ij})$ is a descent datum and we obtain a morphism
$x : W \to \mathcal{X}$ agreeing with $x_i$ over $W_i$"), together with the fact, used there
implicitly, that $x$ is again a section of $f$ over $W$.

The second half rests on 1-morphisms between the stacks of two algebraic spaces being the
morphisms of the spaces (Stacks 04SW, `AlgebraicGeometry.Stack.representingMap`), and on two
morphisms into an fppf sheaf agreeing on a covering family being equal.

## Main results

* `ChowGerbeGlue.eq_of_comp_ι_eq_of_cover`: morphisms into an algebraic space agreeing on a
  covering family of subpresheaves are equal.
* `ChowGerbeGlue.nonempty_iso_algebraicSpaceStackMap_of_cover`: a 1-morphism `Z ⟶ Y` of space
  stacks which is `g` on each member of a covering family is `g`.
* `ChowGerbeGlue.exists_algebraicSpaceStack_hom_of_cocycle_comp_iso`: gluing sections, with the
  glued 1-morphism again a section.

## References

* [Stacks Project, Tag 0CQ7](https://stacks.math.columbia.edu/tag/0CQ7)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite CategoryTheory.PresheafOfCategories

universe u w

namespace AlgebraicGeometry.Stack.AlgebraicStacks.ChowGerbeGlue

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **Morphisms into an algebraic space agreeing on a covering family are equal.** Let
`U i ⊆ Z` be subpresheaves covering `Z` locally for the fppf topology. Two morphisms `Z ⟶ Y` into
an algebraic space with the same restriction to every `U i` are equal, since `Y` is an fppf
sheaf. -/
theorem eq_of_comp_ι_eq_of_cover {Z Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hY : IsAlgebraicSpace B S hS Y) {ι : Type*} (U : ι → Subfunctor Z) {g g' : Z ⟶ Y}
    (h : ∀ i, (U i).ι ≫ g = (U i).ι ≫ g')
    (hcov : ∀ (T : BigFppfOver B S hS) (z : Z.obj (op T)), ∃ R ∈ BigFppfOver.topology B S hS T,
      ∀ ⦃V : BigFppfOver B S hS⦄ ⦃f : V ⟶ T⦄, R.arrows f → ∃ i, Z.map f.op z ∈ (U i).obj (op V)) :
    g = g' := by
  have hsh := (isSheaf_iff_isSheaf_of_type _ Y).1 hY.isSheaf
  ext ⟨T⟩ z
  obtain ⟨R, hR, hRU⟩ := hcov T z
  refine (hsh R hR).isSeparatedFor.ext fun V m hm => ?_
  obtain ⟨i, hi⟩ := hRU hm
  have e : g.app (op V) (Z.map m.op z) = g'.app (op V) (Z.map m.op z) :=
    congrArg (fun k => k.app (op V) ⟨Z.map m.op z, hi⟩) (h i)
  exact (NatTrans.naturality_apply g m.op z).symm.trans
    (e.trans (NatTrans.naturality_apply g' m.op z))

/-- **A 1-morphism of space stacks which is `g` on a covering family is `g`.** Let `U i ⊆ Z` be
algebraic subspaces covering `Z` locally, `g : Z ⟶ Y` a morphism of algebraic spaces and
`a : Z ⟶ Y` a 1-morphism of their stacks whose restriction to every `U i` is 2-isomorphic to the
1-morphism of `g|_{U i}`. Then `a` is 2-isomorphic to the 1-morphism of `g`: both sides are read
off the morphisms of representing presheaves they induce (Stacks 04SW). -/
theorem nonempty_iso_algebraicSpaceStackMap_of_cover {Z Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hZ : IsAlgebraicSpace B S hS Z) (hY : IsAlgebraicSpace B S hS Y) {ι : Type*}
    (U : ι → Subfunctor Z) (hU : ∀ i, IsAlgebraicSpace B S hS (U i).toFunctor)
    (a : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ algebraicSpaceStack.{u, w} B S hS Y hY)
    (g : Z ⟶ Y)
    (ha : ∀ i, Nonempty (algebraicSpaceStackMap.{u, w} B S hS (hU i) hZ (U i).ι ≫ a ≅
      algebraicSpaceStackMap.{u, w} B S hS (hU i) hY ((U i).ι ≫ g)))
    (hcov : ∀ (T : BigFppfOver B S hS) (z : Z.obj (op T)), ∃ R ∈ BigFppfOver.topology B S hS T,
      ∀ ⦃V : BigFppfOver B S hS⦄ ⦃f : V ⟶ T⦄, R.arrows f → ∃ i, Z.map f.op z ∈ (U i).obj (op V)) :
    Nonempty (a ≅ algebraicSpaceStackMap.{u, w} B S hS hZ hY g) := by
  refine nonempty_iso_algebraicSpaceStackMap_of_representingMap_eq B S hS hZ hY a g
    (eq_of_comp_ι_eq_of_cover hY U (fun i => ?_) hcov)
  obtain ⟨e⟩ := ha i
  have h1 := representingMap_comp B S hS _ _ _ (StacksRepresentableCFG.EquivalenceOver.refl _)
    (StacksRepresentableCFG.EquivalenceOver.refl _)
    (StacksRepresentableCFG.EquivalenceOver.refl _)
    (associatedMap B S hS (U i).ι).1 a.hom
  rw [representingMap_associatedMap] at h1
  rw [← h1]
  refine (representingMap_congr_twoIso B S hS _ _ _ _
    { hom := e.hom.hom, inv := e.inv.hom
      hom_inv_id := congrArg Bicategory.InducedBicategory.Hom₂.hom e.hom_inv_id
      inv_hom_id := congrArg Bicategory.InducedBicategory.Hom₂.hom e.inv_hom_id }).trans ?_
  exact representingMap_associatedMap B S hS _ _ _

/-- **Gluing sections of a stack over an algebraic space** (the descent step of the last paragraph
of the proof of [Stacks, Tag 0CQ7]). Let `f : 𝒳 ⟶ Y` be a 1-morphism from an algebraic stack to an
algebraic space, `g : Z ⟶ Y` a morphism of algebraic spaces and `U i ⊆ Z` algebraic subspaces
covering `Z` locally. Given 1-morphisms `x i : U i ⟶ 𝒳` with `f ∘ x i ≅ g|_{U i}` and vertical,
natural transition morphisms `φ i j : x i ⟶ x j` over `U i ∩ U j` satisfying the cocycle
condition, there is a 1-morphism `y : Z ⟶ 𝒳` restricting to `x i` on every `U i`, and
`f ∘ y ≅ g`. -/
theorem exists_algebraicSpaceStack_hom_of_cocycle_comp_iso
    {Z Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hZ : IsAlgebraicSpace B S hS Z)
    (hY : IsAlgebraicSpace B S hS Y) {ι : Type*} (U : ι → Subfunctor Z)
    (hU : ∀ i, IsAlgebraicSpace B S hS (U i).toFunctor) {𝒳 : AlgebraicStacks.{u, w} B S hS}
    (f : 𝒳 ⟶ algebraicSpaceStack.{u, w} B S hS Y hY) (g : Z ⟶ Y)
    (x : ∀ i, algebraicSpaceStack.{u, w} B S hS (U i).toFunctor (hU i) ⟶ 𝒳)
    (hx : ∀ i, Nonempty (x i ≫ f ≅ algebraicSpaceStackMap.{u, w} B S hS (hU i) hY ((U i).ι ≫ g)))
    (φ : ∀ i j (a : (fibredCategory B S hS Z).val.obj) (hi : a.fiber.as ∈ (U i).obj (op a.base))
      (hj : a.fiber.as ∈ (U j).obj (op a.base)),
      (x i).hom.hom.obj (fibredCategorySubfunctorObj (U i) a hi) ⟶
        (x j).hom.hom.obj (fibredCategorySubfunctorObj (U j) a hj))
    (hlift : ∀ i j a hi hj, 𝒳.val.val.p.IsHomLift (𝟙 a.base) (φ i j a hi hj))
    (hnat : ∀ i j {a b : (fibredCategory B S hS Z).val.obj} (m : a ⟶ b) hai haj hbi hbj,
      (x i).hom.hom.map (fibredCategorySubfunctorHom (U i) m hai hbi) ≫ φ i j b hbi hbj =
        φ i j a hai haj ≫ (x j).hom.hom.map (fibredCategorySubfunctorHom (U j) m haj hbj))
    (hcoc : ∀ i j k a hi hj hk, φ i j a hi hj ≫ φ j k a hj hk = φ i k a hi hk)
    (hcov : ∀ (T : BigFppfOver B S hS) (z : Z.obj (op T)), ∃ R ∈ BigFppfOver.topology B S hS T,
      ∀ ⦃V : BigFppfOver B S hS⦄ ⦃f : V ⟶ T⦄, R.arrows f → ∃ i, Z.map f.op z ∈ (U i).obj (op V)) :
    ∃ y : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳,
      (∀ i, Nonempty (algebraicSpaceStackMap.{u, w} B S hS (hU i) hZ (U i).ι ≫ y ≅ x i)) ∧
        Nonempty (y ≫ f ≅ algebraicSpaceStackMap.{u, w} B S hS hZ hY g) := by
  obtain ⟨y, hy⟩ := exists_algebraicSpaceStack_hom_of_cocycle hZ U hU x φ hlift hnat hcoc hcov
  refine ⟨y, hy, nonempty_iso_algebraicSpaceStackMap_of_cover hZ hY U hU (y ≫ f) g
    (fun i => ?_) hcov⟩
  obtain ⟨e₁⟩ := hy i
  obtain ⟨e₂⟩ := hx i
  exact ⟨(Bicategory.associator _ _ _).symm ≪≫ Bicategory.whiskerRightIso e₁ f ≪≫ e₂⟩

end AlgebraicGeometry.Stack.AlgebraicStacks.ChowGerbeGlue

end
