module

public import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Products
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Mono
public import Mathlib.CategoryTheory.Limits.Types.Coproducts
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.MapDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Reasonable
public import StacksFrontier.AlgebraicGeometry.Spaces.ZariskiCover
public import StacksFrontier.CategoryTheory.Sites.Representable.CoproductYonedaRefinement

/-!
# Very reasonableness is Zariski local

Stacks 03KE says that each of the properties `(α)` to `(θ)` of Stacks 03JX is local for the
Zariski topology: a presheaf on the big fppf site of `S` covered by open subspaces each
having the property has the property itself. This file proves the case `(ε)`, very
reasonableness.

Property `(ε)` asks for a jointly surjective family of étale charts by schemes whose two
self-intersection projections are quasi-compact, which is how
`AlgebraicGeometry.Space.IsVeryReasonableSpace` spells it. The total space is not assumed to be
an algebraic space.

## Main results

* `AlgebraicGeometry.Space.isQuasiCompact_of_domainIso`: quasi-compactness of a morphism of
  algebraic spaces only depends on the morphism up to an isomorphism of its source.
* `AlgebraicGeometry.Space.isVeryReasonableSpace_of_isZariskiCover`: the case `(ε)` of
  Stacks 03KE.

## References

* [Stacks Project, Tag 02YY](https://stacks.math.columbia.edu/tag/02YY)
* [Stacks Project, Tag 03JX](https://stacks.math.columbia.edu/tag/03JX)
* [Stacks Project, Tag 03KE](https://stacks.math.columbia.edu/tag/03KE)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Quasi-compactness of a morphism of algebraic spaces over `S` is invariant under an
isomorphism of its source: if `e : A ≅ A'` carries a quasi-compact `f : A ⟶ T` to
`g : A' ⟶ T`, then `g` is quasi-compact. -/
theorem isQuasiCompact_of_domainIso {A A' T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {f : A ⟶ T} {g : A' ⟶ T} (e : A ≅ A') (he : e.hom ≫ g = f)
    (hf : IsQuasiCompact B S hS f) :
    IsQuasiCompact B S hS g :=
  isQuasiCompact_of_isPullback B S hS
    (IsPullback.of_horiz_isIso (fst := e.inv) (g := 𝟙 T)
      ⟨by rw [Category.comp_id, ← he, Iso.inv_hom_id_assoc]⟩) hf

/-- **Stacks 03KE, the case `(ε)`.** Property `(ε)` of Stacks 03JX — very reasonableness — is
local for Zariski coverings: a presheaf on the big fppf site of `S` admitting a Zariski
covering by very reasonable open subspaces is itself very reasonable. -/
@[stacks 03KE "property_epsilon"]
theorem isVeryReasonableSpace_of_isZariskiCover
    (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (I : Type u) (Xᵢ : I → Subfunctor X)
    (hcover : IsZariskiCover B S hS I Xᵢ)
    (hε : ∀ i : I, IsVeryReasonableSpace B S hS (Xᵢ i).toFunctor) :
    IsVeryReasonableSpace B S hS X := by
  classical
  set J := BigFppfOver.topology B S hS with hJ
  choose A U φ hsurj hprops using hε
  set K := Σ i : I, A i with hK
  set V : K → BigFppfOver B S hS := fun k ↦ U k.1 k.2 with hV
  set ψ : ∀ k : K, yoneda.obj (V k) ⟶ X := fun k ↦ φ k.1 k.2 ≫ (Xᵢ k.1).ι with hψ
  refine ⟨K, V, ψ, ?_, ?_⟩
  · refine ⟨?_⟩
    set W₀ : I → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u := fun i ↦ (Xᵢ i).toFunctor with hW₀
    set c := Sigma.desc fun i : I ↦ (Xᵢ i).ι with hc
    set d := Sigma.desc fun k : K ↦ φ k.1 k.2 ≫ Sigma.ι W₀ k.1 with hd
    have hcloc : Presheaf.IsLocallySurjective J c := hcover.2
    have hdloc : Presheaf.IsLocallySurjective J d := by
      refine ⟨?_⟩
      intro T s
      obtain ⟨i, y, hy⟩ := Presheaf.exists_sigmaι_app_eq W₀ (op T) s
      apply J.superset_covering ?_ ((hsurj i).imageSieve_mem y)
      rintro T' f ⟨t, ht⟩
      obtain ⟨j, v, hv⟩ := Presheaf.exists_sigmaι_app_eq (fun j ↦ yoneda.obj (U i j)) (op T') t
      have hlocal : (φ i j).app (op T') v = (Xᵢ i).toFunctor.map f.op y := by
        rw [← hv] at ht
        change ((Sigma.ι (fun j ↦ yoneda.obj (U i j)) j ≫ Sigma.desc (φ i)).app
          (op T')) v = _ at ht
        simpa only [Sigma.ι_comp_desc, NatTrans.comp_app] using ht
      refine ⟨(Sigma.ι (fun k : K ↦ yoneda.obj (V k)) ⟨i, j⟩).app (op T') v, ?_⟩
      change d.app (op T')
        ((Sigma.ι (fun k : K ↦ yoneda.obj (V k)) ⟨i, j⟩).app (op T') v) = (∐ W₀).map f.op s
      calc
        d.app (op T')
            ((Sigma.ι (fun k : K ↦ yoneda.obj (V k)) ⟨i, j⟩).app (op T') v) =
            (Sigma.ι W₀ i).app (op T') ((φ i j).app (op T') v) := by
          change ((Sigma.ι (fun k : K ↦ yoneda.obj (V k)) ⟨i, j⟩ ≫
            Sigma.desc fun k : K ↦ φ k.1 k.2 ≫ Sigma.ι W₀ k.1).app (op T')) v = _
          rw [Sigma.ι_comp_desc]
          rfl
        _ = (Sigma.ι W₀ i).app (op T') ((Xᵢ i).toFunctor.map f.op y) := by rw [hlocal]
        _ = (∐ W₀).map f.op ((Sigma.ι W₀ i).app (op T) y) :=
          NatTrans.naturality_apply (Sigma.ι W₀ i) f.op y
        _ = (∐ W₀).map f.op s := by rw [hy]
    have hcomp : d ≫ c = Sigma.desc ψ := by
      refine Sigma.hom_ext _ _ fun k ↦ ?_
      calc
        Sigma.ι _ k ≫ d ≫ c = φ k.1 k.2 ≫ Sigma.ι W₀ k.1 ≫ c := by simp [hd]
        _ = φ k.1 k.2 ≫ (Xᵢ k.1).ι := by simp [hc, Sigma.ι_comp_desc]
        _ = Sigma.ι _ k ≫ Sigma.desc ψ := by simp [hψ]
    have hglobal : Presheaf.IsLocallySurjective J (Sigma.desc ψ) := by
      rw [← hcomp]
      infer_instance
    intro T x
    exact hglobal.imageSieve_mem x
  · intro k
    have hpb : IsPullback (pullback.fst (φ k.1 k.2) (φ k.1 k.2))
        (pullback.snd (φ k.1 k.2) (φ k.1 k.2)) (ψ k) (ψ k) :=
      IsPullback.of_isLimit
        (pullbackIsPullbackOfCompMono (φ k.1 k.2) (φ k.1 k.2) (Xᵢ k.1).ι)
    refine ⟨?_, ?_, ?_⟩
    · set P := MorphismProperty.inverseImage
        (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS) with hP
      have hle : MorphismProperty.inverseImage
          (@AlgebraicGeometry.IsOpenImmersion.{u} : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B S hS) ≤ P :=
        MorphismProperty.monotone_inverseImage _ fun _ _ f hf ↦ by
          have : AlgebraicGeometry.IsOpenImmersion f := hf
          infer_instance
      have hincl : P.presheaf (Xᵢ k.1).ι :=
        MorphismProperty.relative_monotone (F := yoneda) hle _ (hcover.1 k.1).2
      have : P.IsStableUnderComposition :=
        MorphismProperty.IsStableUnderComposition.inverseImage _
      have : (P.presheaf).IsStableUnderComposition :=
        MorphismProperty.relative_isStableUnderComposition (F := yoneda) P
      intro W θ hθ
      simpa only [hψ, Category.assoc] using
        MorphismProperty.comp_mem _ (θ ≫ φ k.1 k.2) (Xᵢ k.1).ι
          ((hprops k.1 k.2).1 W θ hθ) hincl
    · exact isQuasiCompact_of_domainIso B S hS hpb.isoPullback hpb.isoPullback_hom_fst
        (hprops k.1 k.2).2.1
    · exact isQuasiCompact_of_domainIso B S hS hpb.isoPullback hpb.isoPullback_hom_snd
        (hprops k.1 k.2).2.2

end AlgebraicGeometry.Space

end
