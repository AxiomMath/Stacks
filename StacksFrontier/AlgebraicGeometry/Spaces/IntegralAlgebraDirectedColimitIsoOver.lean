module

public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.IntegralAlgebraFiniteColimitQcqs
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.IntegralAlgebraFiniteColimitOverChart
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentIsoOverOpenSubspace

/-!
# An integral algebra, finite and finitely presented over an open, as a directed colimit

The algebraic half of the source's proof of Stacks 0GUM.  Let `Y` be a quasi-compact and
quasi-separated algebraic space, `𝒜` an integral quasi-coherent `𝒪_Y`-algebra and `V ⊂ Y` a
quasi-compact open subspace over which `𝒜` is finite and of finite presentation.  Then `𝒜` is a
directed colimit of quasi-coherent algebras `𝒜_i` that are finite and of finite presentation and
such that every comparison `𝒜_i ⟶ 𝒜` is an isomorphism over `V`.

The proof is the source's.  Present the underlying module of `𝒜` as a filtered colimit of modules
of finite presentation (Stacks 07V9,
`AlgebraicGeometry.Space.exists_small_isFilteredColimit_isFinitePresentation`) and take the
system `(k, E) ↦ Sym(F_k)/(E)`.  A single affine étale chart `U` covers `V`
(`AlgebraicGeometry.Space.SmallEtale.exists_affine_ofObjects_mem_of_isOpenImmersion`); the members
that are finite and whose comparison is bijective over `U` are cofinal
(`AlgebraicGeometry.Space.exists_directed_isColimit_isFinite_bijective_of_presentation`), and for
quasi-coherent algebras bijectivity over `U` is an isomorphism over `V`
(`AlgebraicGeometry.Space.AlgebraSheaf.isIsoOver_of_bijective_of_ofObjects_mem`).

## Main results

* `AlgebraicGeometry.Space.exists_directed_isColimit_isFinite_isIsoOver`: the statement, with
  Stacks 07V9 and the colimit assertion of Stacks 0829 supplied by their unconditional forms.

## References

* [Stacks Project, Tag 0GUM](https://stacks.math.columbia.edu/tag/0GUM)
* [Stacks Project, Tag 07V9](https://stacks.math.columbia.edu/tag/07V9)
* [Stacks Project, Tag 0829](https://stacks.math.columbia.edu/tag/0829)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The algebraic half of the source's proof of Stacks 0GUM.**  On a quasi-compact and
quasi-separated algebraic space `Y`, an integral quasi-coherent algebra `A` which is finite and of
finite presentation over the affine étale charts lying in a quasi-compact open subspace `V` is the
colimit of a directed system, over a nonempty directed preorder in the universe of the schemes, of
quasi-coherent algebras that are finite and of finite presentation, each of whose comparison maps
to `A` is an isomorphism over `V`.

Stacks 07V9 enters as `AlgebraicGeometry.Space.exists_small_isFilteredColimit_isFinitePresentation`
and the colimit assertion of Stacks 0829 as
`AlgebraicGeometry.Space.nonempty_isColimit_finiteTypeQuasicoherentSubobjectCocone_of_qcqs`. -/
theorem exists_directed_isColimit_isFinite_isIsoOver
    (Y : AlgebraicSpaces B S hS) (hqc : IsQuasiCompactSpace B S hS Y.1)
    (hqs : IsAbsolutelyQuasiSeparated B S hS B.contains_terminal Y.1)
    (A : AlgebraSheaf.{u, u} B S hS Y.1 Y.2) (hA : A.IsQuasicoherent) (hint : A.IsIntegral)
    {V : Subfunctor Y.1} (hV : IsOpenImmersion B S hS V.ι)
    (hVqc : IsQuasiCompactSpace B S hS V.toFunctor)
    (hfinV : ∀ U : SmallEtale B S hS Y.1,
      IsAffine ((SmallEtale.toOver B S hS Y.1 ⋙ BigFppfOver.toScheme B S hS).obj U) →
        Subfunctor.range U.obj.hom ≤ V → RingHom.Finite (A.algebraMap (op U)))
    (hfpV : ∀ U : SmallEtale B S hS Y.1,
      IsAffine ((SmallEtale.toOver B S hS Y.1 ⋙ BigFppfOver.toScheme B S hS).obj U) →
        Subfunctor.range U.obj.hom ≤ V → RingHom.FinitePresentation (A.algebraMap (op U))) :
    ∃ (I : Type u) (_ : Preorder I) (_ : Nonempty I) (_ : IsDirected I (· ≤ ·))
      (D : I ⥤ AlgebraSheaf.{u, u} B S hS Y.1 Y.2) (t : D ⟶ (Functor.const I).obj A)
      (_ : IsColimit (Cocone.mk A t)),
      ∀ i, (D.obj i).IsQuasicoherent ∧ (D.obj i).IsFinite ∧ (D.obj i).IsFinitePresentation ∧
        AlgebraSheaf.IsIsoOver V (t.app i) := by
  have h0829 : ∀ G : Modules.{u, u} B S hS Y.1 Y.2, G.IsQuasicoherentOnSite →
      Nonempty (IsColimit (finiteTypeQuasicoherentSubobjectCocone B S hS Y.1 Y.2 G)) :=
    fun G hG =>
      have := hG
      nonempty_isColimit_finiteTypeQuasicoherentSubobjectCocone_of_qcqs B S hS B.contains_terminal
        Y.1 Y.2 hqc hqs G
  obtain ⟨K, inst, hK, D, φ, hfp, ⟨hc⟩⟩ :=
    exists_small_isFilteredColimit_isFinitePresentation B S hS B.contains_terminal Y.2 hqc hqs
      _ hA
  let _ := inst
  obtain ⟨U, hU, hUV, hUcov⟩ :=
    SmallEtale.exists_affine_ofObjects_mem_of_isOpenImmersion B S hS Y.1 Y.2 V hV hVqc
  obtain ⟨I, instI, hne, hdir, E, t, ht, hE⟩ :=
    exists_directed_isColimit_isFinite_bijective_of_presentation B S hS Y.1 Y.2 hqc A hA hint φ
      hfp hc h0829 hU (hfinV U hU hUV) (hfpV U hU hUV)
  exact ⟨I, instI, hne, hdir, E, t, ht, fun i => ⟨(hE i).1, (hE i).2.1, (hE i).2.2.1,
    AlgebraSheaf.isIsoOver_of_bijective_of_ofObjects_mem (hE i).1 hA (t.app i) hU hUcov
      (hE i).2.2.2⟩⟩

end AlgebraicGeometry.Space

end
