module

public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.AffineSchemeQuasicoherentEquivalence
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.QuasicoherentLocallyQuasicoherent

/-!
# Surjectivity and injectivity of sections of quasi-coherent modules over affine points

Let `𝒳` be an algebraic stack and `x` an object of `𝒳` over `Spec R`, so that
`AlgebraicGeometry.Stack.AlgebraicStacks.pointPullback` is the pullback
`f^* : QCoh(𝒪_𝒳) ⥤ Mod_R`, `M ↦ M(x)`.  These are the two facts used in the proof of
Stacks 0GRP to show that an isomorphism of tensor functors agreeing with a 2-arrow on the direct
images `g_{QCoh,*} N` along a smooth affine chart `g` agrees with it everywhere: `f^*` carries
epimorphisms to surjections, and sections of a quasi-coherent module restrict injectively along a
faithfully flat arrow between affine objects.

## Main results

* `AlgebraicGeometry.Stack.AlgebraicStacks.surjective_pointPullback_map_of_epi`: `f^*` carries
  epimorphisms of `QCoh(𝒪_𝒳)` to surjections; this is the right exactness of `f^*`,
  `AlgebraicGeometry.Stack.AlgebraicStacks.preservesColimitsOfSize_pointPullback`.
* `AlgebraicGeometry.FibredSite.injective_map_of_faithfullyFlat`: restriction of a quasi-coherent
  module along a faithfully flat arrow between affine objects is injective.

## References

* [Stacks Project, Tag 0GRP](https://stacks.math.columbia.edu/tag/0GRP)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u w

namespace AlgebraicGeometry.FibredSite

section Injective

universe v w'

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type v} [Category.{w'} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)

open scoped ChangeOfRings in
/-- **Restriction of a quasi-coherent module along a faithfully flat arrow between affine objects
is injective.**  The restriction `M(y') ⟶ M(y)` is `m ↦ 1 ⊗ m` followed by the base-change
isomorphism `Γ(y) ⊗_{Γ(y')} M(y') ≅ M(y)`, and `m ↦ 1 ⊗ m` is injective when
`Γ(y') ⟶ Γ(y)` is faithfully flat. -/
theorem injective_map_of_faithfullyFlat
    {M : SheafOfModules.{u} (ringStructureSheafCore B S hS p hp .fppf)}
    (hM : M.IsQuasicoherentOnSite) {y y' : 𝒳} (f : y ⟶ y')
    (hy : IsAffine ((BigFppfOver.toScheme B S hS).obj (p.obj y)))
    (hy' : IsAffine ((BigFppfOver.toScheme B S hS).obj (p.obj y')))
    (hf : ((structureSheaf B S hS p hp .fppf).obj.map f.op).hom.FaithfullyFlat) :
    Function.Injective (M.val.map f.op).hom := by
  let g := ((structureSheaf B S hS p hp .fppf).obj.map f.op).hom
  let β := Stacks.PresheafOfModules.restrictionBaseChange.{v, w', u, u}
    (R := (structureSheaf B S hS p hp .fppf).obj) M.val f.op
  have hβ : IsIso β := isIso_restrictionBaseChange_of_isQuasicoherentOnSite M hM f hy hy'
  let : Algebra _ _ := g.toAlgebra
  have : Module.FaithfullyFlat _ _ := hf
  let : Module ((structureSheaf B S hS p hp .fppf).obj.obj (op y')) (M.val.obj (op y')) :=
    inferInstanceAs (Module ((ringStructureSheafCore B S hS p hp .fppf).obj.obj (op y'))
      (M.val.obj (op y')))
  have hmk := Module.FaithfullyFlat.tensorProduct_mk_injective
    (A := (structureSheaf B S hS p hp .fppf).obj.obj (op y'))
    (B := (structureSheaf B S hS p hp .fppf).obj.obj (op y)) (M.val.obj (op y'))
  have hone := Stacks.PresheafOfModules.restrictionBaseChange_one_tmul.{v, w', u, u}
    (R := (structureSheaf B S hS p hp .fppf).obj) M.val f.op
  intro m m' hmm'
  exact hmk (((ConcreteCategory.isIso_iff_bijective β).1 hβ).1
    ((hone m).trans (hmm'.trans (hone m').symm)))

end Injective

end AlgebraicGeometry.FibredSite

namespace AlgebraicGeometry.Stack.AlgebraicStacks

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (𝒳 : AlgebraicStacks.{u, w} B S hS) (x : 𝒳.val.val.obj) {R : Type u} [CommRing R]
  (e : (BigFppfOver.toScheme B S hS).obj (𝒳.val.val.p.obj x) ≅ Spec (CommRingCat.of R))

/-- **An epimorphism of quasi-coherent modules is surjective on sections over a point over an
affine scheme**: `f^* : QCoh(𝒪_𝒳) ⥤ Mod_R` preserves colimits, hence epimorphisms, and the
epimorphisms of `Mod_R` are the surjections. -/
theorem surjective_pointPullback_map_of_epi {M N : quasicoherentModules B S hS 𝒳} (φ : M ⟶ N)
    [Epi φ] : Function.Surjective ((pointPullback B S hS 𝒳 x e).map φ).hom := by
  have := preservesColimitsOfSize_pointPullback B S hS 𝒳 e
  have : PreservesColimitsOfSize.{0, 0} (pointPullback B S hS 𝒳 x e) :=
    preservesColimitsOfSize_shrink.{0, u, 0, u} _
  exact (ModuleCat.epi_iff_surjective _).1 inferInstance

end AlgebraicGeometry.Stack.AlgebraicStacks

end
