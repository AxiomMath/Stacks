module

public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EpiLocallySurjective
public import StacksFrontier.AlgebraicGeometry.AffineQcohPushforward.Colimits
public import StacksFrontier.AlgebraicGeometry.QcohLimits.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.WeaklyEtale.RelativeFinitePresentation.Operations
import all StacksFrontier.AlgebraicGeometry.Morphisms.WeaklyEtale.RelativeFinitePresentation.Operations

/-!
# Right exactness of the direct image along an affine morphism on quasi-coherent modules

Let `h : T ⟶ S` be an affine morphism of schemes.  The direct image `h_*` of sheaves of modules
is a right adjoint, hence left exact, and this file proves the complementary half *on
quasi-coherent modules*: it carries an epimorphism of quasi-coherent `𝒪_T`-modules to an
epimorphism, and consequently it carries the cokernel of a morphism of quasi-coherent
`𝒪_T`-modules to a cokernel.

## Main results

* `Stacks.AlgebraicGeometry.AffineQcohExactness.epi_pushforward_map`: for an affine `h`, the
  direct image of an epimorphism of quasi-coherent modules is an epimorphism.
* `Stacks.AlgebraicGeometry.AffineQcohExactness.preservesColimit_parallelPair_zero`: for an
  affine `h` and a morphism `g` of quasi-coherent modules, `h_*` preserves the colimit of
  `parallelPair g 0`, i.e. it preserves the cokernel of `g`; `preservesColimit_parallelPair` and
  `preservesColimit_walkingParallelPair` are the coequalizer and shape-free forms.

## Implementation notes

**Quasi-coherence is essential, and is not a convenience hypothesis.**  The direct image along
an affine morphism is *not* right exact on all sheaves of modules, so there is no form of these
statements with the quasi-coherence hypotheses dropped — in particular
`CategoryTheory.Limits.PreservesFiniteColimits (Scheme.Modules.pushforward h)` is false for an
affine `h`.  The counterexample is the structure morphism `h : X ⟶ Spec k` of an integral affine
scheme `X` of positive dimension over a field, say `X = 𝔸¹_k`, which is affine because both
schemes are; `h_*` is then the global-sections functor to `k`-modules.  Take a closed point
`x ∈ X` and let `K ⊆ 𝒪_X` be the subsheaf with `K(V) = 𝒪_X(V)` for `x ∉ V` and `K(V) = 0` for
`x ∈ V` — a sheaf because `X` is integral, so a section vanishing on a nonempty open vanishes.
Its stalks are `𝒪_{X,y}` for `y ≠ x` and `0` at `x`, so the quotient `𝒪_X / K` is the skyscraper
at `x` with value `𝒪_{X,x}`, whose global sections are `𝒪_{X,x}`.  The epimorphism
`𝒪_X ⟶ 𝒪_X / K` therefore has `Γ(X, 𝒪_X) = k[t] ⟶ 𝒪_{X,x} = k[t]_{(t)}` on global sections,
which is not surjective, so `h_*` does not preserve that cokernel.  `K` is of course not
quasi-coherent.

**Where the affineness and the quasi-coherence enter.**  Only through the one fact that an
epimorphism of quasi-coherent modules is *surjective on sections over an affine open* — over an
affine open the category of quasi-coherent modules is `ModuleCat Γ(X, U)` by
`AlgebraicGeometry.tildeEquiv`, where an epimorphism is a surjection.  That statement is already
proved in the library, as the private
`AlgebraicGeometry.epi_app_of_isAffineOpen` of
`StacksFrontier.AlgebraicGeometry.Morphisms.WeaklyEtale.RelativeFinitePresentation.Operations`,
and is reached here by `import all` rather than reproved.  Affineness of `h` is used exactly
once: the preimage of an affine open is affine, and the sections of `h_*M` over an open `V` of
`S` *are* the sections of `M` over `h⁻¹V`, by definition.

**From epimorphisms to cokernels.**  Right exactness is not formal from preservation of
epimorphisms, because the latter is available only between quasi-coherent modules.  The
argument factors `g` through its image `K = ker (coker.π g)`, which is quasi-coherent because
kernels and cokernels of morphisms of quasi-coherent modules are
(`Stacks.AlgebraicGeometry.QcohLimits.isQuasicoherent_kernel` and
`Stacks.AlgebraicGeometry.QuasicoherentColimits.isQuasicoherent_cokernel`).  Left exactness
makes `h_*(K ⟶ B)` a kernel of `h_*(coker.π g)`, which is an epimorphism by the first result,
so `CategoryTheory.Abelian.epiIsCokernelOfKernel` makes it a cokernel of `h_*(K ⟶ B)`; and
`CategoryTheory.Limits.isCokernelEpiComp` turns that into a cokernel of
`h_*g = h_*(A ↠ K) ≫ h_*(K ⟶ B)`, because `h_*(A ↠ K)` is again an epimorphism by the first
result.

## References

* [Stacks Project, Tag 01XC](https://stacks.math.columbia.edu/tag/01XC)
* [Stacks Project, Tag 01XB](https://stacks.math.columbia.edu/tag/01XB)
* [Stacks Project, Tag 01SB](https://stacks.math.columbia.edu/tag/01SB)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace

universe u

namespace Stacks.AlgebraicGeometry.AffineQcohExactness

variable {T S : Scheme.{u}} (h : T ⟶ S)

/-- The direct image of sheaves of modules along a morphism of schemes is left exact, being a
right adjoint. -/
instance preservesFiniteLimits_pushforward :
    PreservesFiniteLimits (Scheme.Modules.pushforward h) :=
  have : (Scheme.Modules.pushforward h).IsRightAdjoint :=
    (Scheme.Modules.pullbackPushforwardAdjunction h).isRightAdjoint
  inferInstance

/-- **Right exactness of the direct image along an affine morphism, on quasi-coherent modules.**
The direct image of an epimorphism of quasi-coherent `𝒪_T`-modules along an affine morphism
`h : T ⟶ S` is an epimorphism.

An epimorphism of sheaves of modules is a locally surjective morphism, and local surjectivity of
`h_*ψ` is checked at the affine opens of `S`, which form a basis: the sections of `h_*M` over `V`
are the sections of `M` over `h⁻¹V`, the open `h⁻¹V` is affine because `h` is, and an
epimorphism of quasi-coherent modules is surjective on sections over an affine open. -/
theorem epi_pushforward_map [IsAffineHom h]
    {M N : T.Modules} [M.IsQuasicoherent] [N.IsQuasicoherent] (ψ : M ⟶ N) [Epi ψ] :
    Epi ((Scheme.Modules.pushforward h).map ψ) := by
  apply Stacks.SheafOfModules.EpiMono.epi_of_isLocallySurjective
  refine ⟨fun {V} s => ?_⟩
  intro x hx
  obtain ⟨W, hW, hxW, hWV⟩ := Opens.isBasis_iff_nbhd.mp S.isBasis_affineOpens hx
  refine ⟨W, homOfLE hWV, ?_, hxW⟩
  obtain ⟨t, ht⟩ := _root_.AlgebraicGeometry.epi_app_of_isAffineOpen ψ (h ⁻¹ᵁ W)
    (hW.preimage h) (((Scheme.Modules.pushforward h).obj N).presheaf.map (homOfLE hWV).op s)
  exact ⟨t, ht⟩

/-- **The direct image along an affine morphism preserves cokernels of morphisms of
quasi-coherent modules.**  For an affine `h : T ⟶ S` and a morphism `g` of quasi-coherent
`𝒪_T`-modules, `h_*` preserves the colimit of `parallelPair g 0`, that is, it carries a cokernel
of `g` to a cokernel of `h_*g`. -/
theorem preservesColimit_parallelPair_zero [IsAffineHom h]
    {A B : T.Modules} [A.IsQuasicoherent] [B.IsQuasicoherent] (g : A ⟶ B) :
    PreservesColimit (parallelPair g 0) (Scheme.Modules.pushforward h) := by
  have : (cokernel g).IsQuasicoherent := inferInstance
  have : (Abelian.image g).IsQuasicoherent :=
    inferInstanceAs ((kernel (cokernel.π g)).IsQuasicoherent)
  set F := Scheme.Modules.pushforward h with hF
  have hepi : Epi (F.map (cokernel.π g)) := epi_pushforward_map h (cokernel.π g)
  have hker : IsLimit (KernelFork.ofι (F.map (kernel.ι (cokernel.π g)))
      (by simp [← F.map_comp]) : Fork (F.map (cokernel.π g)) 0) :=
    isLimitForkMapOfIsLimit' F (kernel.condition (cokernel.π g))
      (kernelIsKernel (cokernel.π g))
  have hcok := Abelian.epiIsCokernelOfKernel _ hker
  have hfac : F.map g = F.map (Abelian.factorThruImage g) ≫
      F.map (kernel.ι (cokernel.π g)) := by
    rw [← F.map_comp, Abelian.image.fac]
  have hepi2 : Epi (F.map (Abelian.factorThruImage g)) :=
    epi_pushforward_map h (Abelian.factorThruImage g)
  refine preservesColimit_of_preserves_colimit_cocone (cokernelIsCokernel g) ?_
  refine (isColimitMapCoconeCoforkEquiv' F (cokernel.condition g)).symm ?_
  exact isCokernelEpiComp hcok (F.map (Abelian.factorThruImage g)) hfac

/-- **The direct image along an affine morphism preserves coequalizers of pairs of morphisms of
quasi-coherent modules.**  In a preadditive category a coequalizer of `u` and `v` is a cokernel
of `u - v`, so this is `preservesColimit_parallelPair_zero` at the difference, transported across
`CategoryTheory.Preadditive.isColimitCoforkOfCokernelCofork` on both sides.

The universal property is checked by hand rather than by rewriting the diagram, because
`F.map (u - v) = F.map u - F.map v` is an equality of morphisms appearing in the *type* of the
cokernel cofork, so rewriting with it produces an ill-typed motive. -/
theorem preservesColimit_parallelPair [IsAffineHom h]
    {A B : T.Modules} [A.IsQuasicoherent] [B.IsQuasicoherent] (u v : A ⟶ B) :
    PreservesColimit (parallelPair u v) (Scheme.Modules.pushforward h) := by
  set F := Scheme.Modules.pushforward h with hF
  have hbase : PreservesColimit (parallelPair (u - v) 0) F :=
    preservesColimit_parallelPair_zero h _
  have hw : u ≫ cokernel.π (u - v) = v ≫ cokernel.π (u - v) := by
    rw [← sub_eq_zero, ← Preadditive.sub_comp, cokernel.condition]
  refine preservesColimit_of_preserves_colimit_cocone
    (Preadditive.isColimitCoforkOfCokernelCofork (cokernelIsCokernel (u - v))) ?_
  refine (isColimitMapCoconeCoforkEquiv F hw).symm ?_
  have hcokF : IsColimit (CokernelCofork.ofπ (F.map (cokernel.π (u - v)))
      (show F.map (u - v) ≫ F.map (cokernel.π (u - v)) = 0 by
        rw [← F.map_comp, cokernel.condition, F.map_zero]) : Cofork (F.map (u - v)) 0) :=
    isColimitOfHasCokernelOfPreservesColimit F (u - v)
  refine Cofork.IsColimit.mk' _ fun s => ?_
  have hs : F.map (u - v) ≫ s.π = 0 := by
    have hc := s.condition
    rw [Functor.map_sub, Preadditive.sub_comp, hc, sub_self]
  have hfac := hcokF.fac (CokernelCofork.ofπ s.π hs) WalkingParallelPair.one
  refine ⟨hcokF.desc (CokernelCofork.ofπ s.π hs), hfac, fun {m} hm => ?_⟩
  refine Cofork.IsColimit.hom_ext hcokF ?_
  have hm' : F.map (cokernel.π (u - v)) ≫ m = s.π := hm
  change F.map (cokernel.π (u - v)) ≫ m = F.map (cokernel.π (u - v)) ≫ _
  rw [hm']
  exact hfac.symm

/-- **The direct image along an affine morphism preserves the colimit of any diagram of shape
`WalkingParallelPair` whose two objects are quasi-coherent.**  This is the form the dévissage of
Stacks 0FZE consumes: the diagram there is a parallel pair composed with a functor, which is not
syntactically a `parallelPair`, and the shape-free statement avoids having to know that the
functor preserves the zero morphism. -/
theorem preservesColimit_walkingParallelPair [IsAffineHom h] (D : WalkingParallelPair ⥤ T.Modules)
    (h₀ : (D.obj WalkingParallelPair.zero).IsQuasicoherent)
    (h₁ : (D.obj WalkingParallelPair.one).IsQuasicoherent) :
    PreservesColimit D (Scheme.Modules.pushforward h) :=
  have := h₀
  have := h₁
  have : PreservesColimit (parallelPair (D.map WalkingParallelPairHom.left)
      (D.map WalkingParallelPairHom.right)) (Scheme.Modules.pushforward h) :=
    preservesColimit_parallelPair h _ _
  preservesColimit_of_iso_diagram _ (diagramIsoParallelPair D).symm

end Stacks.AlgebraicGeometry.AffineQcohExactness

end
