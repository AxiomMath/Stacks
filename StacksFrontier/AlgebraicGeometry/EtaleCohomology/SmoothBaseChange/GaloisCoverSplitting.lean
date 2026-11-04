module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmoothBaseChange.CurveClassKillingDefs
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.MorphismMap
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.SplitCoverFiber
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Torsors under base change, and Galois covers with a section are split

Two facts about finite étale covers used in the proof of [Stacks, Tag 0EYT].

* If a group `M` acts on a finite étale cover `V` of `Y`, simply transitively on the geometric
  fibres, then so does it on the base change of `V` along any `Y' ⟶ Y`: the geometric fibre of the
  base change at `y'` is the geometric fibre of `V` at the image of `y'`, compatibly with maps.
* If `A ⟶ Y` is a Galois cover and `y : S ⟶ Y`, with `S` connected, lifts to `A`, then `A` is
  split over `y`: the translates of the lift by the automorphisms of `A` give a map from a
  disjoint union of copies of `S` to `A ×_Y S` which is bijective on geometric fibres, hence an
  isomorphism of finite étale covers of `S`.

## Main results

* `Stacks.EtaleCohomology.existsUnique_finiteEtaleBaseChange_map`.
* `Stacks.EtaleCohomology.isIso_of_bijective_finiteEtaleFiberFunctor_map`.
* `Stacks.EtaleCohomology.isSplitOver_of_isGaloisCover`.

## References

* [Stacks Project, Tag 0EYT](https://stacks.math.columbia.edu/tag/0EYT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open _root_.AlgebraicGeometry CategoryTheory.PreGaloisCategory Stacks.FundamentalGroup

universe u

namespace Stacks.EtaleCohomology

variable {Y Y' : Scheme.{u}}

/-- The fibre projection of a base-changed finite étale cover is compatible with maps. -/
theorem finiteEtaleFiberProjection_map (g : Y' ⟶ Y) (y : GeometricPoint Y')
    {V W : FiniteEtaleOver Y} (φ : V ⟶ W)
    (a : finiteEtaleFiber y ((finiteEtaleBaseChange g).obj V)) :
    finiteEtaleFiberProjection g y W
        ((finiteEtaleFiberFunctor y).map ((finiteEtaleBaseChange g).map φ) a) =
      (finiteEtaleFiberFunctor (y.map g)).map φ (finiteEtaleFiberProjection g y V a) :=
  Subtype.ext (by
    change (a.1 ≫ ((finiteEtaleBaseChange g).map φ).left) ≫ finiteEtaleBaseChangeProj g W =
      (a.1 ≫ finiteEtaleBaseChangeProj g V) ≫ φ.left
    rw [Category.assoc, finiteEtaleBaseChangeProj_naturality, Category.assoc])

/-- **A torsor stays a torsor under base change.** If `M` acts on the geometric fibre of `V` at
the image of `y`, simply transitively, then it acts simply transitively on the geometric fibre at
`y` of the base change of `V`. -/
theorem existsUnique_finiteEtaleBaseChange_map {M : Type*} (g : Y' ⟶ Y) (y : GeometricPoint Y')
    (V : FiniteEtaleOver Y) (α : M → (V ⟶ V))
    (htors : ∀ a b : finiteEtaleFiber (y.map g) V,
      ∃! m : M, (finiteEtaleFiberFunctor (y.map g)).map (α m) a = b)
    (a b : finiteEtaleFiber y ((finiteEtaleBaseChange g).obj V)) :
    ∃! m : M, (finiteEtaleFiberFunctor y).map ((finiteEtaleBaseChange g).map (α m)) a = b := by
  let e := finiteEtaleFiberProjectionEquiv g y V
  obtain ⟨m, hm, huniq⟩ := htors (e a) (e b)
  exact ⟨m, e.injective ((finiteEtaleFiberProjection_map g y (α m) a).trans hm),
    fun m' hm' => huniq m' ((finiteEtaleFiberProjection_map g y (α m') a).symm.trans
      (congrArg e hm'))⟩

/-- **Isomorphisms of finite étale covers are detected on one geometric fibre** of a connected
scheme, the geometric fibre functor being a fibre functor of a Galois category. -/
@[sga "1 V 3.7" "more general"]
theorem isIso_of_bijective_finiteEtaleFiberFunctor_map {S : Scheme.{u}} [ConnectedSpace S]
    (x : GeometricPoint S) {A B : FiniteEtaleOver S} (φ : A ⟶ B)
    (h : Function.Bijective ((finiteEtaleFiberFunctor x).map φ)) : IsIso φ := by
  let : GaloisCategory (FiniteEtaleOver S) :=
    IsGaloisCategory.toGaloisCategory (finiteEtaleFiberFunctor x)
  let : IsGaloisCategory (finiteEtaleFiberFintypeFunctor S x ⋙ FintypeCat.incl) :=
    finiteEtaleFiberFunctor_isGaloisCategory S x
  let : FiberFunctor (finiteEtaleFiberFintypeFunctor S x) :=
    IsGaloisCategory.fiberFunctor (finiteEtaleFiberFintypeFunctor S x)
  have : IsIso (FintypeCat.incl.map ((finiteEtaleFiberFintypeFunctor S x).map φ)) :=
    (isIso_iff_bijective _).2 h
  have : IsIso ((finiteEtaleFiberFintypeFunctor S x).map φ) :=
    isIso_of_fully_faithful FintypeCat.incl _
  exact isIso_of_reflects_iso φ (finiteEtaleFiberFintypeFunctor S x)

/-- **A Galois cover with a section over a connected base is split.** Let `A ⟶ Y` be a Galois
cover of a connected scheme, `S` a connected scheme with a geometric point, and `y : S ⟶ Y` a
morphism which lifts to `A`. Then `A ×_Y S` is a finite disjoint union of copies of `S`. -/
theorem isSplitOver_of_isGaloisCover {S : Scheme.{u}} [ConnectedSpace Y] [ConnectedSpace S]
    (s : GeometricPoint S) (y : S ⟶ Y) (A : FiniteEtaleOver Y) (hA : IsGaloisCover A.hom)
    (σ₀ : S ⟶ A.left) (hσ₀ : σ₀ ≫ A.hom = y) : IsSplitOver A.hom y := by
  let ι := finiteEtaleFiber (s.map y) A
  have : Finite ι :=
    (inferInstance : IsGaloisCategory (finiteEtaleFiberFunctor (s.map y))).finite_obj A
  let c₀ : ι := ⟨s.hom ≫ σ₀, by rw [Category.assoc, hσ₀]; rfl⟩
  choose τ hτ using fun b : ι => hA.2.2.2 (s.map y) c₀ b
  have hw : ∀ b : ι, (τ b).hom.left ≫ A.hom = A.hom := fun b => Over.w (τ b).hom
  let sec : ι → (S ⟶ ((finiteEtaleBaseChange y).obj A).left) := fun b =>
    pullback.lift (σ₀ ≫ (τ b).hom.left) (𝟙 S) (by rw [Category.assoc, hw b, hσ₀, Category.id_comp])
  have hsec₁ : ∀ b, sec b ≫ finiteEtaleBaseChangeProj y A = σ₀ ≫ (τ b).hom.left := fun b =>
    pullback.lift_fst _ _ _
  let φ : splitCover S ι ⟶ (finiteEtaleBaseChange y).obj A :=
    MorphismProperty.Over.homMk (Sigma.desc sec) (Sigma.hom_ext _ _ fun b =>
      (Sigma.ι_desc_assoc sec b _).trans ((pullback.lift_snd _ _ _).trans
        (Sigma.ι_desc (fun _ : ι => 𝟙 S) b).symm))
  let e := finiteEtaleFiberProjectionEquiv y s A
  have hfun : ⇑((finiteEtaleFiberFunctor s).map φ) = e.symm ∘ splitCoverFiberEquiv s ι := by
    funext z
    obtain ⟨b, rfl⟩ := (splitCoverFiberEquiv s ι).symm.surjective z
    rw [Function.comp_apply, Equiv.apply_symm_apply, Equiv.eq_symm_apply]
    refine Subtype.ext ?_
    change ((s.hom ≫ Sigma.ι (fun _ : ι => S) b) ≫ Sigma.desc sec) ≫
      finiteEtaleBaseChangeProj y A = b.1
    simp only [Category.assoc, Sigma.ι_desc_assoc, hsec₁]
    exact (Category.assoc _ _ _).symm.trans (hτ b)
  have := isIso_of_bijective_finiteEtaleFiberFunctor_map s φ (by
    rw [hfun]
    exact e.symm.bijective.comp (splitCoverFiberEquiv s ι).bijective)
  exact ⟨ι, inferInstance,
    (MorphismProperty.Over.forget _ _ S ⋙ Over.forget S).mapIso (asIso φ),
    MorphismProperty.Over.w φ⟩

end Stacks.EtaleCohomology

end
