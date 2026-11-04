module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Coproduct
public import StacksFrontier.AlgebraicGeometry.Spaces.SiteProperties
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.Subcanonical
public import StacksFrontier.CategoryTheory.Sites.CoproductUniversality

/-!
# Coproducts of sheaves on a big fppf site are disjoint

The big fppf site over `S` carries the clopen classifier `⊤ ⊔ ⊤` required by
`CategoryTheory.Sheaf.mono_cofan_inj`: the two injections of a binary coproduct of schemes are
complementary open immersions, so the fibre of a constant morphism `W ⟶ ⊤ ⟶ ⊤ ⊔ ⊤` given by
one injection along the other is the empty scheme, and the empty family is an fppf covering of
the empty scheme. Consequently the legs of a coproduct cocone in
`Sheaf (AlgebraicGeometry.BigFppfOver.topology B S hS) (Type u)` are monomorphisms and legs
with distinct indices have disjoint images: coproducts of sheaves, and in particular of
algebraic spaces, are disjoint.

## Main results

* `AlgebraicGeometry.isEmpty_toScheme_pullback_inr_inl`: the fibre of a constant morphism
  `W ⟶ ⊤ ⟶ ⊤ ⊔ ⊤` given by the right injection along the left injection has no points.
* `AlgebraicGeometry.Sheaf.mono_cofan_inj_bigFppfOver`: the legs of a coproduct cocone of
  sheaves of sets on the big fppf site over `S` are monomorphisms.
* `AlgebraicGeometry.Sheaf.isEmpty_toScheme_of_eq_of_ne`: legs with distinct indices have
  disjoint images.

## References

* [Stacks Project, Tag 02WO](https://stacks.math.columbia.edu/tag/02WO)
* [Stacks Project, Tag 0F15](https://stacks.math.columbia.edu/tag/0F15)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe w u

namespace AlgebraicGeometry

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- An object of the big fppf site with two morphisms to the terminal object whose composites
with the two injections into `⊤ ⊔ ⊤` agree has no points. -/
private lemma isEmpty_toScheme_of_comp_inl_eq_comp_inr {V : BigFppfOver B S hS}
    (f g : V ⟶ ⊤_ (BigFppfOver B S hS))
    (h : f ≫ (coprod.inl : ⊤_ (BigFppfOver B S hS) ⟶ _) = g ≫ coprod.inr) :
    IsEmpty ((BigFppfOver.toScheme B S hS).obj V) := by
  refine ⟨fun z => ?_⟩
  have h' := congrArg
    (fun m : (BigFppfOver.toScheme B S hS).obj V ⟶
      (BigFppfOver.toScheme B S hS).obj _ => m z) (congrArg (BigFppfOver.toScheme B S hS).map h)
  simp only [Functor.map_comp, Scheme.Hom.comp_apply] at h'
  exact ne_of_isColimit_binaryCofan
    (isColimitBinaryCofanToSchemeMap (B := B) (hS := hS) (⊤_ _) (⊤_ _)) _ _ h'

/-- The fibre of the constant morphism `W ⟶ ⊤ ⟶ ⊤ ⊔ ⊤` given by the right injection along
the left injection has no points. -/
lemma isEmpty_toScheme_pullback_inr_inl (W : BigFppfOver B S hS) :
    IsEmpty ((BigFppfOver.toScheme B S hS).obj
      (pullback (terminal.from W ≫ (coprod.inr : ⊤_ (BigFppfOver B S hS) ⟶ _))
        (coprod.inl : ⊤_ (BigFppfOver B S hS) ⟶ _))) := by
  exact isEmpty_toScheme_of_comp_inl_eq_comp_inr (pullback.snd _ _)
    (pullback.fst _ _ ≫ terminal.from W) (by
      rw [Category.assoc]; exact pullback.condition.symm)

/-- The legs of a coproduct cocone of sheaves of sets on the big fppf site over `S` are
monomorphisms. -/
theorem Sheaf.mono_cofan_inj_bigFppfOver {I : Type w}
    {F : I → Sheaf (BigFppfOver.topology B S hS) (Type u)}
    {P : Sheaf (BigFppfOver.topology B S hS) (Type u)} (ι : ∀ i, F i ⟶ P)
    (hP : IsColimit (Cofan.mk P ι)) (i₀ : I) : Mono (ι i₀) := by
  exact CategoryTheory.Sheaf.mono_cofan_inj _ (coprod.inl : ⊤_ (BigFppfOver B S hS) ⟶ _)
    (𝟙 _) (coprod.inr : ⊤_ (BigFppfOver B S hS) ⟶ _)
    (GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable _)
    (fun W => BigFppfOver.bot_mem_topology _ (isEmpty_toScheme_pullback_inr_inl W)) ι hP i₀

/-- Distinct legs of a coproduct cocone of sheaves on the big fppf site over `S` have
disjoint images: an object of the site carrying sections of two different members of the
family with the same image in the coproduct has no points. -/
theorem Sheaf.isEmpty_toScheme_of_eq_of_ne {I : Type w}
    {F : I → Sheaf (BigFppfOver.topology B S hS) (Type u)}
    {P : Sheaf (BigFppfOver.topology B S hS) (Type u)} (ι : ∀ i, F i ⟶ P)
    (hP : IsColimit (Cofan.mk P ι)) {i j : I} (hij : i ≠ j) {W : BigFppfOver B S hS}
    (x : (F i).obj.obj (op W)) (y : (F j).obj.obj (op W))
    (h : (ι i).hom.app (op W) x = (ι j).hom.app (op W) y) :
    IsEmpty ((BigFppfOver.toScheme B S hS).obj W) := by
  have heq := CategoryTheory.Sheaf.terminal_comp_eq_of_ne _
    (coprod.inl : ⊤_ (BigFppfOver B S hS) ⟶ _) (𝟙 _)
    (coprod.inr : ⊤_ (BigFppfOver B S hS) ⟶ _)
    (GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable _) ι hP hij x y h
  exact isEmpty_toScheme_of_comp_inl_eq_comp_inr (terminal.from W) (terminal.from W)
    (by simpa using heq)

end AlgebraicGeometry

end
