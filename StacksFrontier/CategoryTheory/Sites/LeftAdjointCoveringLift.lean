module

public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.CategoryTheory.Sites.Subcanonical
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.StrictlyHenselianTransport

/-!
# Lifting points of a left adjoint along a covering

Let `q` be a functor from sheaves of sets on a site to sets which is a left adjoint — a point of
the topos, for instance.  If a family of sections `bₖ ∈ F(Vₖ)` of a sheaf `F` generates `F`
locally, then every element of `q(F)` comes from `q(h_{Vₖ})` for some `k` along the morphism
`h_{Vₖ} ⟶ F` classifying `bₖ`.  In particular, for a covering family `Vₖ ⟶ W`, every element of
`q(h_W)` comes from some `q(h_{Vₖ})`: a point of a topos lifts along every covering.  This is a
step of the proof of Stacks 04KL.

The proof is that the morphism `∐ₖ h_{Vₖ} ⟶ F` is locally surjective, hence an epimorphism, and
`q` preserves epimorphisms and coproducts; an element of a coproduct of sets lies in one of the
summands.

## Main results

* `CategoryTheory.Sheaf.exists_map_yonedaEquiv_symm_eq`: the lift along a locally generating
  family of sections.
* `CategoryTheory.Sheaf.exists_map_yoneda_map_eq`: the lift along a covering family.

## References

* [Stacks Project, Tag 04KL](https://stacks.math.columbia.edu/tag/04KL)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe w u

namespace CategoryTheory.Sheaf

variable {C : Type u} [Category.{w} C] {J : GrothendieckTopology C} [J.Subcanonical]
  [HasSheafify J (Type w)] (q : Sheaf J (Type w) ⥤ Type w) [q.IsLeftAdjoint]

/-- **Points of a left adjoint lift along a locally generating family of sections.** If every
section of `F` is, locally, a restriction of one of the `bₖ ∈ F(Vₖ)`, then every element of
`q(F)` is the image of an element of `q(h_{Vₖ})`, for some `k`, under the morphism
`h_{Vₖ} ⟶ F` classifying `bₖ`. -/
theorem exists_map_yonedaEquiv_symm_eq {F : Sheaf J (Type w)} {K : Type w} (V : K → C)
    (b : ∀ k, F.obj.obj (op (V k)))
    (h : ∀ (W : C) (z : F.obj.obj (op W)), ∃ T : Sieve W, T ∈ J W ∧
      ∀ ⦃W' : C⦄ (i : W' ⟶ W), T i → ∃ (k : K) (φ : W' ⟶ V k),
        F.obj.map φ.op (b k) = F.obj.map i.op z)
    (σ : q.obj F) :
    ∃ (k : K) (σk : q.obj (J.yoneda.obj (V k))), q.map (J.yonedaEquiv.symm (b k)) σk = σ := by
  have : HasColimitsOfShape (Discrete K) (Sheaf J (Type w)) :=
    Sheaf.instHasColimitsOfShape
  set ψ : ∐ (fun k => J.yoneda.obj (V k)) ⟶ F := Sigma.desc fun k => J.yonedaEquiv.symm (b k)
  have : Presheaf.IsLocallySurjective J ψ.hom := by
    refine isLocallySurjective_of_exists _ fun W z ↦ ?_
    obtain ⟨T, hT, hTz⟩ := h W z
    refine ⟨T, hT, fun W' i hi ↦ ?_⟩
    obtain ⟨k, φ, hφ⟩ := hTz i hi
    set φ' : (sectionsFunctor J (op W')).obj (J.yoneda.obj (V k)) := φ
    refine ⟨(sectionsFunctor J (op W')).map (Sigma.ι (fun k => J.yoneda.obj (V k)) k) φ', ?_⟩
    show (sectionsFunctor J (op W')).map ψ
      ((sectionsFunctor J (op W')).map (Sigma.ι _ k) φ') = _
    rw [← Functor.map_comp_apply, Sigma.ι_desc]
    exact hφ
  obtain ⟨τ, rfl⟩ := surjective_map_of_isLocallySurjective q ψ σ
  obtain ⟨⟨k⟩, σk, hσk⟩ := Types.jointly_surjective_of_isColimit
    (isColimitOfPreserves q (colimit.isColimit (Discrete.functor fun k => J.yoneda.obj (V k)))) τ
  refine ⟨k, σk, ?_⟩
  rw [← hσk]
  show q.map (J.yonedaEquiv.symm (b k)) σk = q.map ψ (q.map (Sigma.ι _ k) σk)
  rw [← q.map_comp_apply, Sigma.ι_desc]

/-- **Points of a left adjoint lift along a covering.** For a covering family `πₖ : Vₖ ⟶ W`,
every element of `q(h_W)` is the image of an element of some `q(h_{Vₖ})`. -/
theorem exists_map_yoneda_map_eq {W : C} {K : Type w} (V : K → C) (π : ∀ k, V k ⟶ W)
    (hcov : Sieve.generate (Presieve.ofArrows V π) ∈ J W) (σ : q.obj (J.yoneda.obj W)) :
    ∃ (k : K) (σk : q.obj (J.yoneda.obj (V k))), q.map (J.yoneda.map (π k)) σk = σ := by
  obtain ⟨k, σk, h⟩ := exists_map_yonedaEquiv_symm_eq q V
    (F := J.yoneda.obj W) (fun k => (π k : V k ⟶ W)) (fun W₀ z ↦ by
      refine ⟨(Sieve.generate (Presieve.ofArrows V π)).pullback z, J.pullback_stable z hcov,
        fun W' i hi ↦ ?_⟩
      obtain ⟨Y, g, f, ⟨k⟩, hgf⟩ := hi
      exact ⟨k, g, hgf⟩) σ
  refine ⟨k, σk, Eq.trans ?_ h⟩
  congr 1

end CategoryTheory.Sheaf
