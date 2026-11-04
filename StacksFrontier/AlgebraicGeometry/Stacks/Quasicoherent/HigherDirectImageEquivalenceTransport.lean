module

public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.HigherDirectImageCechInduction
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.HigherDirectImageFppfWeakSerre
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.ModuleGuitartBaseChange

/-!
# Higher direct images along a 1-morphism precomposed with an equivalence

Let `e : 𝒲' ⟶ 𝒲` be a `1`-morphism of algebraic stacks whose underlying functor is an
equivalence and let `f : 𝒲 ⟶ 𝒴`. Then `Rⁱ(f ∘ e)_*(e⁻¹ℱ) ≅ Rⁱf_*ℱ` for every sheaf of modules
`ℱ` on `𝒲_étale`. Consequently, for a rule satisfying hypotheses (1) and (2) of **Stacks 076Z**,
the higher direct images along `f` carry the rule into the rule as soon as those along `f ∘ e`
do. This is how hypothesis (4) of **Stacks 076Z**, which is stated for the stacks
`AlgebraicGeometry.Stack.schemeStack` of affine schemes, reaches a stack which is only
*equivalent* to one.

## Main results

* `AlgebraicGeometry.Stack.moduleHigherDirectImageEquivalenceIso`: `Rⁱ(f ∘ e)_*(e⁻¹ℱ) ≅ Rⁱf_*ℱ`.
* `AlgebraicGeometry.Stack.StackEtaleModuleRule.preservedBy_of_isEquivalence_comp`.

## Implementation notes

The square with sides `e`, `f ∘ e`, `f` and the identity of `𝒴`, filled by the identity, is
Guitart exact because `e` is an equivalence, so this is the base change of
`AlgebraicGeometry.Stack.moduleHigherDirectImageGuitartBaseChangeIso` along the identity of the
target: `e` is faithful and the source of `e`, an algebraic stack, has equalizers
(**Stacks 06WY**).
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u t

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The inverse image of sheaves of modules along the identity functor is the identity. -/
noncomputable def modulePullbackIdIso {𝒴 : Type (u + 1)} [Category.{u} 𝒴]
    (q : 𝒴 ⥤ BigFppfOver B S hS) (hq : q.IsFiberedInGroupoids)
    (τ : GrothendieckTopology B.Schemes) (hτ : τ ≤ B.topology) :
    modulePullback.{u, u + 1, u, u + 1, u + 1, u} B S hS q q hq hq (𝟭 𝒴) rfl τ hτ ≅ 𝟭 _ :=
  Iso.refl _

variable {𝒲' 𝒲 𝒴 : AlgebraicStacks.{u, t} B S hS} (e : 𝒲' ⟶ 𝒲) (f : 𝒲 ⟶ 𝒴)

/-- The square with sides `e`, `f ∘ e`, `f` and the identity of `𝒴`, filled by the identity. -/
abbrev equivalenceSquare :
    TwoSquare (CatFiberedInGroupoids.homFunctor e.hom)
      (CatFiberedInGroupoids.homFunctor e.hom ⋙ CatFiberedInGroupoids.homFunctor f.hom)
      (CatFiberedInGroupoids.homFunctor f.hom) (𝟭 _) :=
  TwoSquare.mk _ _ _ _ (𝟙 _)

/-- **Higher direct images along a 1-morphism precomposed with an equivalence.** For `e` an
equivalence, `Rⁱ(f ∘ e)_*(e⁻¹ℱ) ≅ Rⁱf_*ℱ` on sheaves of modules on the étale sites. -/
noncomputable def moduleHigherDirectImageEquivalenceIso
    [(CatFiberedInGroupoids.homFunctor e.hom).IsEquivalence] (i : ℕ)
    (F : SheafOfModules.{u + 1} (ringStructureSheafCore B S hS
      (CatFiberedInGroupoids.homFunctor f.hom ⋙ 𝒴.val.val.p)
      (AlgebraicStacks.isFiberedInGroupoids_strict B S hS f) (etaleTopology B)
      (etaleTopology_le_topology B))) :
    letI := hasSheafify_associatedTopology_of_category_succ B S hS
      (CatFiberedInGroupoids.homFunctor e.hom ⋙ CatFiberedInGroupoids.homFunctor f.hom ⋙
        𝒴.val.val.p)
    letI := wEqualsLocallyBijective_associatedTopology_of_category_succ B S hS
      (CatFiberedInGroupoids.homFunctor e.hom ⋙ CatFiberedInGroupoids.homFunctor f.hom ⋙
        𝒴.val.val.p)
    letI := hasSheafify_associatedTopology_of_category_succ B S hS
      (CatFiberedInGroupoids.homFunctor f.hom ⋙ 𝒴.val.val.p)
    letI := wEqualsLocallyBijective_associatedTopology_of_category_succ B S hS
      (CatFiberedInGroupoids.homFunctor f.hom ⋙ 𝒴.val.val.p)
    letI := hasSheafify_associatedTopology_of_category_succ B S hS 𝒴.val.val.p
    letI := wEqualsLocallyBijective_associatedTopology_of_category_succ B S hS 𝒴.val.val.p
    (moduleSheafHigherDirectImage.{u, u + 1, u, u + 1, u} B S hS
        (CatFiberedInGroupoids.homFunctor e.hom ⋙ CatFiberedInGroupoids.homFunctor f.hom ⋙
          𝒴.val.val.p) 𝒴.val.val.p
        (AlgebraicStacks.isFiberedInGroupoids_strict₂ B S hS e f) 𝒴.val.isFiberedInGroupoids
        (CatFiberedInGroupoids.homFunctor e.hom ⋙ CatFiberedInGroupoids.homFunctor f.hom) rfl
        (etaleTopology B) (etaleTopology_le_topology B) i).obj
        ((modulePullback.{u, u + 1, u, u + 1, u + 1, u} B S hS
          (CatFiberedInGroupoids.homFunctor e.hom ⋙ CatFiberedInGroupoids.homFunctor f.hom ⋙
            𝒴.val.val.p)
          (CatFiberedInGroupoids.homFunctor f.hom ⋙ 𝒴.val.val.p)
          (AlgebraicStacks.isFiberedInGroupoids_strict₂ B S hS e f)
          (AlgebraicStacks.isFiberedInGroupoids_strict B S hS f)
          (CatFiberedInGroupoids.homFunctor e.hom) rfl (etaleTopology B)
          (etaleTopology_le_topology B)).obj F) ≅
      (moduleSheafHigherDirectImage.{u, u + 1, u, u + 1, u} B S hS
        (CatFiberedInGroupoids.homFunctor f.hom ⋙ 𝒴.val.val.p) 𝒴.val.val.p
        (AlgebraicStacks.isFiberedInGroupoids_strict B S hS f) 𝒴.val.isFiberedInGroupoids
        (CatFiberedInGroupoids.homFunctor f.hom) rfl (etaleTopology B)
        (etaleTopology_le_topology B) i).obj F := by
  letI := hasSheafify_associatedTopology_of_category_succ B S hS
    (CatFiberedInGroupoids.homFunctor e.hom ⋙ CatFiberedInGroupoids.homFunctor f.hom ⋙
      𝒴.val.val.p)
  letI := wEqualsLocallyBijective_associatedTopology_of_category_succ B S hS
    (CatFiberedInGroupoids.homFunctor e.hom ⋙ CatFiberedInGroupoids.homFunctor f.hom ⋙
      𝒴.val.val.p)
  letI := hasSheafify_associatedTopology_of_category_succ B S hS
    (CatFiberedInGroupoids.homFunctor f.hom ⋙ 𝒴.val.val.p)
  letI := wEqualsLocallyBijective_associatedTopology_of_category_succ B S hS
    (CatFiberedInGroupoids.homFunctor f.hom ⋙ 𝒴.val.val.p)
  letI := hasSheafify_associatedTopology_of_category_succ B S hS 𝒴.val.val.p
  letI := wEqualsLocallyBijective_associatedTopology_of_category_succ B S hS 𝒴.val.val.p
  have hw : TwoSquareIsVertical B S hS
      (CatFiberedInGroupoids.homFunctor e.hom ⋙ CatFiberedInGroupoids.homFunctor f.hom ⋙
        𝒴.val.val.p)
      (CatFiberedInGroupoids.homFunctor f.hom ⋙ 𝒴.val.val.p) 𝒴.val.val.p 𝒴.val.val.p
      (CatFiberedInGroupoids.homFunctor e.hom)
      (CatFiberedInGroupoids.homFunctor e.hom ⋙ CatFiberedInGroupoids.homFunctor f.hom)
      (CatFiberedInGroupoids.homFunctor f.hom) (𝟭 _) rfl rfl rfl rfl
      (equivalenceSquare B S hS e f) := fun _ => by
    simp [equivalenceSquare]
  exact (moduleHigherDirectImageGuitartBaseChangeIso B S hS _ _ _ _
      (AlgebraicStacks.isFiberedInGroupoids_strict₂ B S hS e f)
      (AlgebraicStacks.isFiberedInGroupoids_strict B S hS f) 𝒴.val.isFiberedInGroupoids
      𝒴.val.isFiberedInGroupoids _ _ _ _ rfl rfl rfl rfl (equivalenceSquare B S hS e f)
      (etaleTopology B) (etaleTopology_le_topology B) hw i F).symm ≪≫
    (modulePullbackIdIso B S hS 𝒴.val.val.p 𝒴.val.isFiberedInGroupoids (etaleTopology B)
      (etaleTopology_le_topology B)).app _

namespace StackEtaleModuleRule

/-- **Transport of the conclusion of Stacks 076Z along an equivalence of the source.** Let `M`
satisfy hypotheses (1) and (2) of **Stacks 076Z**, let `e : 𝒲' ⟶ 𝒲` be a 1-morphism whose
underlying functor is an equivalence and let `f : 𝒲 ⟶ 𝒴`. If the higher direct images along
`f ∘ e` carry `M` into `M` in degree `i`, so do those along `f`.

A member `ℱ` of `M` on `𝒲` pulls back to a member `e⁻¹ℱ` on `𝒲'` by hypothesis (2), `e` being
smooth; then `Rⁱf_*ℱ ≅ Rⁱ(f ∘ e)_*(e⁻¹ℱ)` lies in `M`, by hypothesis (1) through closure under
isomorphisms. -/
theorem preservedBy_of_isEquivalence_comp (M : StackEtaleModuleRule B S hS)
    (hserre : IsWeakSerre.{u, t} B S hS M)
    (hpull : IsStableUnderSmoothPullback.{u, t} B S hS M)
    (he : (CatFiberedInGroupoids.homFunctor e.hom).IsEquivalence) (i : ℕ)
    (h : PreservedBy B S hS M (e ≫ f) i) : PreservedBy B S hS M f i := by
  intro F hF
  have key := h ((modulePullback.{u, u + 1, u, u + 1, u + 1, u} B S hS
      (CatFiberedInGroupoids.homFunctor e.hom ⋙ CatFiberedInGroupoids.homFunctor f.hom ⋙
        𝒴.val.val.p)
      (CatFiberedInGroupoids.homFunctor f.hom ⋙ 𝒴.val.val.p)
      (AlgebraicStacks.isFiberedInGroupoids_strict₂ B S hS e f)
      (AlgebraicStacks.isFiberedInGroupoids_strict B S hS f)
      (CatFiberedInGroupoids.homFunctor e.hom) rfl (etaleTopology B)
      (etaleTopology_le_topology B)).obj F) (hpull (strictChart B S hS e f)
        (isSmooth_strictChart B S hS e f
          (AlgebraicStacks.isSmooth_of_isEquivalence B S hS e he)) F hF)
  let := hasSheafify_associatedTopology_of_category_succ B S hS 𝒴.val.val.p
  let := wEqualsLocallyBijective_associatedTopology_of_category_succ B S hS 𝒴.val.val.p
  let : Abelian (SheafOfModules.{u + 1} (ringStructureSheafCore B S hS 𝒴.val.val.p
      𝒴.val.isFiberedInGroupoids (etaleTopology B) (etaleTopology_le_topology B))) :=
    SheafOfModules.instAbelian.{u + 1, u, u, u + 1} _
  have : (toObjectProperty.{u, t} B S hS M 𝒴).IsWeakSerreClass := hserre 𝒴
  exact (toObjectProperty.{u, t} B S hS M 𝒴).prop_of_iso
    (moduleHigherDirectImageEquivalenceIso B S hS e f i F) key

/-- **The base case of the proof of Stacks 076Z.** Let `M` satisfy hypotheses (1), (2) and (4)
of **Stacks 076Z**. For a 1-morphism `f : 𝒳 ⟶ 𝒴` from an algebraic stack representable by an
affine scheme to the stack of an affine scheme, the higher direct images along `f` carry `M`
into `M`.

The source is equivalent over the site to the stack `(Sch/U)_fppf` of an affine scheme `U`, and
the backward half `e` of that equivalence is a 1-morphism `(Sch/U)_fppf ⟶ 𝒳` whose functor is an
equivalence; hypothesis (4) applies to `f ∘ e` and
`AlgebraicGeometry.Stack.StackEtaleModuleRule.preservedBy_of_isEquivalence_comp` transports it
back to `f`. -/
theorem preservedBy_of_isAffineRepresentable (M : StackEtaleModuleRule B S hS)
    (hserre : IsWeakSerre.{u, t} B S hS M)
    (hpull : IsStableUnderSmoothPullback.{u, t} B S hS M)
    (haff : PreservesHigherDirectImagesOfAffine.{u, t} B S hS M)
    {𝒳 : AlgebraicStacks.{u, t} B S hS} (h𝒳 : AlgebraicStacks.IsAffineRepresentable B S hS 𝒳)
    {X : BigFppfOver B S hS} (hX : IsAffine X.left.1)
    (f : 𝒳 ⟶ schemeStack.{u, t} B S hS X) (i : ℕ) : PreservedBy B S hS M f i := by
  obtain ⟨U, hU, ⟨E⟩⟩ := h𝒳
  let e : schemeStack.{u, t} B S hS U ⟶ 𝒳 :=
    Bicategory.InducedBicategory.mkHom (Bicategory.InducedBicategory.mkHom
      ⟨E.inv.functor, E.inv.w⟩)
  have he : (CatFiberedInGroupoids.homFunctor e.hom).IsEquivalence :=
    (CategoryTheory.Equivalence.mk E.hom.functor E.inv.functor E.unitIso
      E.counitIso).isEquivalence_inverse
  exact preservedBy_of_isEquivalence_comp B S hS e f M hserre hpull he i
    (haff U X hU hX (e ≫ f) i)

end StackEtaleModuleRule

end AlgebraicGeometry.Stack

end
