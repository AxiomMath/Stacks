module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.SchemeAtlas
public import StacksFrontier.CategoryTheory.Sites.QuasiCompact.LocallySurjectiveTransfer

/-!
# Joint surjectivity from étale lifts through every point

Let `S` be a scheme contained in a big fppf site `B` and let `{πₖ : Wₖ ⟶ X}` be a family of
morphisms of fppf sheaves on the big fppf site of `S`. If every point of the scheme underlying
the source of every section of `X` lies in the image of an étale morphism of the site along which
the section lifts to some `Wₖ`, then the family is jointly surjective, that is, the induced
morphism out of the coproduct is a surjection of sheaves.

## Main results

* `AlgebraicGeometry.FormalSpace.isLocallySurjective_sigmaDesc_of_forall_mem_range`: the
  criterion.

## Implementation notes

For a section `ξ` over `U` the étale morphisms `P_x ⟶ U`, one for each point `x` of `U`, are
jointly surjective, hence generate a covering sieve of the fppf topology
(`AlgebraicGeometry.FormalSpace.fppf_ofArrows_mem`), and `ξ` lifts along each of them; this is
the sectionwise form of joint surjectivity,
`CategoryTheory.Sheaf.isLocallySurjective_sigmaDesc_iff`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.FormalSpace

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Joint surjectivity from étale lifts through every point.** A family `{πₖ : Wₖ ⟶ X}` of
morphisms of fppf sheaves is jointly surjective as soon as, for every scheme-valued point
`ξ : U ⟶ X` and every point `x` of `U`, there is a morphism `p : P ⟶ U` of the site, étale on
underlying schemes and with `x` in its image, along which `ξ` lifts to some `Wₖ`. -/
theorem isLocallySurjective_sigmaDesc_of_forall_mem_range
    {K : Type (u + 1)} {W : K → FppfSheaf B S hS} {X : FppfSheaf B S hS} (π : ∀ k, W k ⟶ X)
    (h : ∀ (U : BigFppfOver B S hS) (ξ : uliftYoneda.{u + 1}.obj U ⟶ X.obj)
      (x : (BigFppfOver.toScheme B S hS).obj U),
      ∃ (k : K) (P : BigFppfOver B S hS) (p : P ⟶ U)
        (r : uliftYoneda.{u + 1}.obj P ⟶ (W k).obj),
        r ≫ (π k).hom = uliftYoneda.{u + 1}.map p ≫ ξ ∧
        Etale ((BigFppfOver.toScheme B S hS).map p) ∧
        x ∈ Set.range ((BigFppfOver.toScheme B S hS).map p)) :
    letI : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
    Sheaf.IsLocallySurjective (Sigma.desc π) := by
  let : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
  refine (Sheaf.isLocallySurjective_sigmaDesc_iff π).2 fun {U} s ↦ ?_
  obtain ⟨ξ, rfl⟩ := uliftYonedaEquiv.{u + 1}.surjective s
  choose k P p r hr hp hx using h U ξ
  refine ⟨Sieve.ofArrows P p, fppf_ofArrows_mem B S hS P p
    (fun x ↦ by have : Etale (p x).left.hom := hp x; infer_instance)
    (fun x ↦ by have : Etale (p x).left.hom := hp x; infer_instance)
    (fun x ↦ ⟨x, hx x⟩), ?_⟩
  rintro V _ ⟨Z, g, _, ⟨x⟩, rfl⟩
  refine ⟨k x, uliftYonedaEquiv (uliftYoneda.{u + 1}.map g ≫ r x), ?_⟩
  rw [← uliftYonedaEquiv_comp, Category.assoc, hr x, ← Category.assoc, ← Functor.map_comp]
  exact (uliftYonedaEquiv_naturality ξ (g ≫ p x).op).symm

end AlgebraicGeometry.FormalSpace

end
