module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.Algebraic.RepresentableMorphism.Invariance
import all StacksFrontier.AlgebraicGeometry.Stacks.Algebraic.RepresentableMorphism.Invariance
public import StacksFrontier.AlgebraicGeometry.Stacks.Representability
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentabilityPostcomp
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Comp
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.DiscretePresheaf
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Fibrewise
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.OfPresheaf
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Representability.EquivalenceOverCompare
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Representability.SliceProduct
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Slice
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.TwoCategory
public import StacksFrontier.CategoryTheory.TwoFibreProductOverReindex
public import Mathlib.CategoryTheory.Groupoid.Discrete

/-!
# Representability by algebraic spaces is invariant under equivalence (Stacks 0457)

In a 2-commutative square of categories fibred in groupoids over the big fppf site of a
scheme, a vertical morphism is representable by algebraic spaces if and only if the other
is, provided both horizontal morphisms are equivalences.

The Stacks source omits the proof. The argument carried out here is the one the source
indicates: given a scheme-valued point of the target of one vertical morphism, transport it
along the horizontal equivalence of targets to a point of the other target, and compare the
two 2-fibre products by a chain of equivalences of `CategoryTheory.TwoFibreProductOver` —
postcomposition of both legs with the equivalence of targets, reindexing along the
2-commutativity isomorphism and along the comparison between the transported point and the
original one, and precomposition of the second leg with the equivalence of sources. Each of
those four comparisons commutes strictly with the first projection, so the equivalence over
the site exhibited by representability of the one morphism is carried over to the other.

## Main results

* `AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_iff_of_equivalences`: in a
  2-commutative square whose horizontal morphisms are equivalences, one vertical morphism is
  representable by algebraic spaces if and only if the other is.
* `AlgebraicGeometry.Stack.nonempty_equivalenceOver_fst_precompose_source`: precomposing the
  second factor of a 2-fibre product with an equivalence gives an equivalent first projection,
  as a category over the first factor.

## Implementation notes

The four total categories have independent object and hom universes. The 1-morphisms are
based functors, and 2-commutativity is a based natural isomorphism, so its components lie
over identities of the base. Equivalence of a horizontal morphism is expressed by
equivalence of its underlying functor.

## References

* [Stacks Project, Tag 0457](https://stacks.math.columbia.edu/tag/0457)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe baseHom baseObj testHom testObj homA homB homD objA objB objD

variable {𝒞 : Type baseObj} [Category.{baseHom} 𝒞]

universe u v₁ v₂ v₃ v₄ w₁ w₂ w₃ w₄

/-- An equivalence of categories `K` with `K ⋙ r = p` between categories fibred in groupoids over
`C` gives an equivalence over `C`. -/
private theorem nonempty_equivalenceOver_of_comp_eq {C : Type u} [Category.{v₁} C]
    {D₁ : Type w₁} [Category.{v₂} D₁] {D₂ : Type w₂} [Category.{v₃} D₂]
    {p : D₁ ⥤ C} {r : D₂ ⥤ C} (hp : p.IsFiberedInGroupoids) (hr : r.IsFiberedInGroupoids)
    (K : D₁ ⥤ D₂) (hK : K ⋙ r = p) [K.IsEquivalence] :
    Nonempty (StacksRepresentableCFG.EquivalenceOver p r) := by
  obtain ⟨Kinv, hKinv, η, ε, hη, hε⟩ :=
    Functor.IsFiberedInGroupoids.isEquivalence_over p r hp hr K hK inferInstance
  refine ⟨StacksRepresentableCFG.EquivalenceOver.ofFunctorIsEquivalenceOver hK
    { inv := Kinv, inv_over := hKinv, unitIso := η, counitIso := ε,
      unit_vertical := fun X => ?_, counit_vertical := fun X => ?_ }⟩
  · have hx : p.obj ((K ⋙ Kinv).obj X) = p.obj X := by
      change ((K ⋙ Kinv) ⋙ p).obj X = _
      rw [Functor.assoc, hKinv, hK]
    exact (congrArg (fun W => p.IsHomLift (𝟙 W) (η.hom.app X)) hx.symm).mp (hη X)
  · have hx : r.obj ((Kinv ⋙ K).obj X) = r.obj X := by
      change ((Kinv ⋙ K) ⋙ r).obj X = _
      rw [Functor.assoc, hK, hKinv]
    exact (congrArg (fun W => r.IsHomLift (𝟙 W) (ε.hom.app X)) hx.symm).mp (hε X)

/-- Representability by algebraic spaces of a morphism of categories fibred in groupoids is
invariant under horizontal equivalences in a 2-commutative square. -/
@[stacks 0457]
theorem isRepresentableByAlgebraicSpaces_iff_of_equivalences
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {𝒳' : CatFiberedInGroupoids.{u, v₁, u + 1, w₁}
      (BigFppfOver B S hS)}
    {𝒳 : CatFiberedInGroupoids.{u, v₂, u + 1, w₂}
      (BigFppfOver B S hS)}
    {𝒴' : CatFiberedInGroupoids.{u, v₃, u + 1, w₃}
      (BigFppfOver B S hS)}
    {𝒴 : CatFiberedInGroupoids.{u, v₄, u + 1, w₄}
      (BigFppfOver B S hS)}
    (f' : 𝒳'.val ⥤ᵇ 𝒴'.val) (f : 𝒳.val ⥤ᵇ 𝒴.val)
    (a : 𝒳'.val ⥤ᵇ 𝒳.val) (b : 𝒴'.val ⥤ᵇ 𝒴.val)
    (α : BasedFunctor.comp a f ≅ BasedFunctor.comp f' b)
    [Functor.IsEquivalence a.toFunctor]
    [Functor.IsEquivalence b.toFunctor] :
    IsRepresentableByAlgebraicSpaces B S hS f ↔
      IsRepresentableByAlgebraicSpaces B S hS f' := by
  let a₀ := a.toFunctor
  let b₀ := b.toFunctor
  let f₀ := f.toFunctor
  let f'₀ := f'.toFunctor
  have ha : a₀ ⋙ 𝒳.val.p = 𝒳'.val.p := a.w
  have hb : b₀ ⋙ 𝒴.val.p = 𝒴'.val.p := b.w
  have hf : f₀ ⋙ 𝒴.val.p = 𝒳.val.p := f.w
  have hf' : f'₀ ⋙ 𝒴'.val.p = 𝒳'.val.p := f'.w
  let α₀ : a₀ ⋙ f₀ ≅ f'₀ ⋙ b₀ :=
    (BasedNatTrans.forgetful 𝒳'.val 𝒴.val).mapIso α
  have hα₀symm (x : 𝒳'.val.obj) : 𝒴.val.p.IsHomLift
      (𝟙 (𝒳'.val.p.obj x)) (α₀.inv.app x) := α.inv.isHomLift' x
  -- the comparison of the two 2-fibre products, for points `G'` and `G` related by `θ`
  have key (U : BigFppfOver B S hS)
      (G' : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒴'.val.obj)
      (G : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒴.val.obj)
      (hG' : G' ⋙ 𝒴'.val.p = Over.map U.hom) (hG : G ⋙ 𝒴.val.p = Over.map U.hom)
      (θ : G' ⋙ b₀ ≅ G) (hθ : ∀ z, 𝒴.val.p.IsHomLift (𝟙 ((Over.map U.hom).obj z))
        (θ.hom.app z)) :
      Nonempty (StacksRepresentableCFG.EquivalenceOver
        (TwoFibreProductOver.fst (Over.map U.hom) 𝒳'.val.p 𝒴'.val.p G' f'₀)
        (TwoFibreProductOver.fst (Over.map U.hom) 𝒳.val.p 𝒴.val.p G f₀)) := by
    let K₁ := Stacks.RepresentableMorphism.product_postcompose (p𝒜 := 𝒳'.val.p)
      (pℬ := 𝒴'.val.p) (p𝒟 := 𝒴.val.p) (pT := Over.map U.hom) G' f'₀ b₀ hb
    let K₂ := Stacks.RepresentableMorphism.product_reindex_first (p𝒜 := Over.map U.hom)
      (pℬ := 𝒳'.val.p) (p𝒟 := 𝒴.val.p) (F := G' ⋙ b₀) (F' := G) (G := f'₀ ⋙ b₀) θ hθ
    let K₃ := Stacks.RepresentableMorphism.product_reindex_second (p𝒜 := 𝒳'.val.p)
      (p𝒟 := 𝒴.val.p) (pT := Over.map U.hom) (F := G) (G := f'₀ ⋙ b₀) (G' := a₀ ⋙ f₀)
      α₀.symm hα₀symm
    let K₄ := Stacks.RepresentableMorphism.product_precompose_source (p𝒜' := 𝒳'.val.p)
      (p𝒜 := 𝒳.val.p) (pℬ := 𝒴.val.p) (pT := Over.map U.hom) G f₀ a₀ ha
    have : K₁.IsEquivalence := Stacks.RepresentableMorphism.product_postcompose_isEquivalence hb
    have : K₂.IsEquivalence := Stacks.RepresentableMorphism.product_reindex_first_isEquivalence
      (p𝒜 := Over.map U.hom) (pℬ := 𝒳'.val.p) (p𝒟 := 𝒴.val.p)
      (F := G' ⋙ b₀) (F' := G) (G := f'₀ ⋙ b₀) θ hθ
    have : K₃.IsEquivalence := Stacks.RepresentableMorphism.product_reindex_second_isEquivalence
      (p𝒜 := 𝒳'.val.p) (p𝒟 := 𝒴.val.p) (pT := Over.map U.hom)
      (F := G) (G := f'₀ ⋙ b₀) (G' := a₀ ⋙ f₀) α₀.symm hα₀symm
    have : K₄.IsEquivalence := Stacks.RepresentableMorphism.product_precompose_source_isEquivalence
      (pT := Over.map U.hom) (p𝒜' := 𝒳'.val.p) (p𝒜 := 𝒳.val.p) (pℬ := 𝒴.val.p) (G := G) (F := f₀)
      (overMap_isFiberedInGroupoids (𝒞 := SchemeBelow B.cutoff) U.hom)
      𝒳'.isFiberedInGroupoids 𝒳.isFiberedInGroupoids ha hG hf
    have hfst : (K₁ ⋙ K₂ ⋙ K₃ ⋙ K₄) ⋙
        TwoFibreProductOver.fst (Over.map U.hom) 𝒳.val.p 𝒴.val.p G f₀ =
        TwoFibreProductOver.fst (Over.map U.hom) 𝒳'.val.p 𝒴'.val.p G' f'₀ :=
      CategoryTheory.Functor.ext (fun _ => rfl) (fun _ _ g => by
        simp only [Functor.comp_map, K₁, K₂, K₃, K₄,
          Stacks.RepresentableMorphism.product_postcompose,
          Stacks.RepresentableMorphism.product_reindex_first,
          Stacks.RepresentableMorphism.product_reindex_second,
          Stacks.RepresentableMorphism.product_precompose_source,
          Stacks.RepresentableMorphism.product_swap, TwoFibreProductOver.fst_map]
        exact Over.OverMorphism.ext ((conj_eqToHom_iff_heq' g.a.left g.a.left rfl rfl).2 HEq.rfl))
    let : Category (SchemeBelow B.cutoff) := inferInstance
    exact nonempty_equivalenceOver_of_comp_eq
      (fst_isFiberedInGroupoids_overMap (𝒞 := SchemeBelow B.cutoff) (U := U.left)
        (S := B.obj hS) (f := U.hom) (p𝒜 := 𝒳'.val.p) (p𝒟 := 𝒴'.val.p) (G := G') (F := f'₀)
        𝒳'.isFiberedInGroupoids 𝒴'.isFiberedInGroupoids hG' hf')
      (fst_isFiberedInGroupoids_overMap (𝒞 := SchemeBelow B.cutoff) (U := U.left)
        (S := B.obj hS) (f := U.hom) (p𝒜 := 𝒳.val.p) (p𝒟 := 𝒴.val.p) (G := G) (F := f₀)
        𝒳.isFiberedInGroupoids 𝒴.isFiberedInGroupoids hG hf)
      (K₁ ⋙ K₂ ⋙ K₃ ⋙ K₄) hfst
  constructor
  · intro hrepr
    dsimp only [IsRepresentableByAlgebraicSpaces] at hrepr ⊢
    intro U y' hy'
    have hG : (y' ⋙ b₀) ⋙ 𝒴.val.p = Over.map U.hom := by rw [Functor.assoc, hb, hy']
    obtain ⟨Fsp, hFsp, ⟨E⟩⟩ := hrepr U _ hG
    obtain ⟨e⟩ := key U y' _ hy' hG (Iso.refl _) fun z => IsHomLift.id (Functor.congr_obj hG z)
    exact ⟨Fsp, hFsp, ⟨e.trans E⟩⟩
  · intro hrepr
    dsimp only [IsRepresentableByAlgebraicSpaces] at hrepr ⊢
    intro U G hG
    obtain ⟨H, hH, η, ε, hη, hε⟩ :=
      Functor.IsFiberedInGroupoids.isEquivalence_over 𝒴'.val.p 𝒴.val.p
        𝒴'.isFiberedInGroupoids 𝒴.isFiberedInGroupoids b₀ hb
        (inferInstance : b₀.IsEquivalence)
    have hG' : (G ⋙ H) ⋙ 𝒴'.val.p = Over.map U.hom := by rw [Functor.assoc, hH, hG]
    let θ : (G ⋙ H) ⋙ b₀ ≅ G :=
      NatIso.ofComponents (fun z => ε.app (G.obj z)) (by
        intro z z' k
        convert ε.hom.naturality (G.map k) using 1 <;>
          simp [Functor.comp_obj, Functor.comp_map])
    obtain ⟨Fsp, hFsp, ⟨E⟩⟩ := hrepr U _ hG'
    obtain ⟨e⟩ := key U _ G hG' hG θ fun z => by
      rw [← Functor.congr_obj hG z]
      exact hε (G.obj z)
    exact ⟨Fsp, hFsp, ⟨e.symm.trans E⟩⟩

/-- **Precomposing the second factor of a 2-fibre product with an equivalence does not change
the first projection, as a category over the first factor.** For a slice `𝒞/U` as first factor
and an equivalence `a : 𝒜' ⥤ 𝒜` strictly over `𝒞`, the first projections of
`𝒞/U ×_ℬ 𝒜'` — formed along `a ⋙ F` — and of `𝒞/U ×_ℬ 𝒜` are equivalent over `𝒞/U`. -/
theorem nonempty_equivalenceOver_fst_precompose_source
    {S U : 𝒞} (f : U ⟶ S)
    {𝒜' : Type objA} {𝒜 : Type objB} {ℬ : Type objD}
    [Category.{homA} 𝒜'] [Category.{homB} 𝒜] [Category.{homD} ℬ]
    {p𝒜' : 𝒜' ⥤ Over S} {p𝒜 : 𝒜 ⥤ Over S} {pℬ : ℬ ⥤ Over S}
    (G : Over U ⥤ ℬ) (F : 𝒜 ⥤ ℬ) (a : 𝒜' ⥤ 𝒜) [Functor.IsEquivalence a]
    (hp𝒜' : p𝒜'.IsFiberedInGroupoids) (hp𝒜 : p𝒜.IsFiberedInGroupoids)
    (hpℬ : pℬ.IsFiberedInGroupoids) (hA : a ⋙ p𝒜 = p𝒜')
    (hG : G ⋙ pℬ = Over.map f) (hF : F ⋙ pℬ = p𝒜) :
    Nonempty (StacksRepresentableCFG.EquivalenceOver
      (TwoFibreProductOver.fst (Over.map f) p𝒜' pℬ G (a ⋙ F))
      (TwoFibreProductOver.fst (Over.map f) p𝒜 pℬ G F)) := by
  have hF' : (a ⋙ F) ⋙ pℬ = p𝒜' := by rw [Functor.assoc, hF, hA]
  have hfstNew : (TwoFibreProductOver.fst (Over.map f) p𝒜' pℬ G (a ⋙ F)).IsFiberedInGroupoids :=
    fst_isFiberedInGroupoids_overMap f p𝒜' pℬ G (a ⋙ F) hp𝒜' hpℬ hG hF'
  have hfstOld : (TwoFibreProductOver.fst (Over.map f) p𝒜 pℬ G F).IsFiberedInGroupoids :=
    fst_isFiberedInGroupoids_overMap f p𝒜 pℬ G F hp𝒜 hpℬ hG hF
  let K := Stacks.RepresentableMorphism.product_precompose_source (p𝒜' := p𝒜') (p𝒜 := p𝒜)
    (pℬ := pℬ) (pT := Over.map f) G F a hA
  have hK : K.IsEquivalence :=
    Stacks.RepresentableMorphism.product_precompose_source_isEquivalence (p𝒜' := p𝒜')
      (p𝒜 := p𝒜) (pℬ := pℬ) (pT := Over.map f) (overMap_isFiberedInGroupoids f) hp𝒜' hp𝒜 hA hG hF
  have hKfst : K ⋙ TwoFibreProductOver.fst (Over.map f) p𝒜 pℬ G F =
      TwoFibreProductOver.fst (Over.map f) p𝒜' pℬ G (a ⋙ F) :=
    CategoryTheory.Functor.ext (fun _ => rfl) (fun _ _ φ => by
      simp only [Functor.comp_map, K, Stacks.RepresentableMorphism.product_precompose_source,
        TwoFibreProductOver.fst_map]
      apply Over.OverMorphism.ext
      simp only [Over.comp_left]
      exact (conj_eqToHom_iff_heq' φ.a.left φ.a.left rfl rfl).2 HEq.rfl)
  exact nonempty_equivalenceOver_of_comp_eq hfstNew hfstOld K hKfst

end AlgebraicGeometry.Stack

end
