module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import StacksFrontier.AlgebraicGeometry.Descent.MorphismProperty.LocalFiniteness
public import StacksFrontier.RingTheory.FormallySmooth.FaithfullyFlatDescent
import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackStalkMateComp

/-!
# Étale descent along a surjective flat morphism

Let `f : X ⟶ Y` be a surjective morphism which is flat and locally of finite presentation, and
let `q : Y ⟶ S` be a morphism of schemes. If the composition `f ≫ q` is étale, then so is `q`.
In particular étaleness descends along a surjective étale morphism.

## Main results

* `Stacks.Etale.flat_of_flat_of_faithfullyFlat` is the commutative algebra input for flatness:
  for a tower `R → B → C` with `C` faithfully flat over `B`, flatness of `C` over `R` descends
  to flatness of `B` over `R`.
* `Stacks.Etale.flat_stalkMap` descends flatness to the stalk maps of `q` along a surjective
  flat `f`, and `Stacks.Etale.formallyUnramified_stalkMap` does the same for formal
  unramifiedness along a surjective smooth `f`.
* `Stacks.Etale.etale_of_comp_surjective_etale_of_locallyOfFinitePresentation` is the descent
  statement: `q` is étale as soon as `f` is surjective étale, `f ≫ q` is étale and `q` is
  locally of finite presentation.
* `Stacks.Etale.etale_of_comp_of_fppf` descends étaleness along a surjective flat morphism
  which is locally of finite presentation, with no hypothesis on `q` at all.

## Implementation notes

Both flatness and formal unramifiedness of a morphism of schemes can be checked on stalks, by
`AlgebraicGeometry.Flat.of_stalkMap` and by
`AlgebraicGeometry.HasRingHomProperty.of_stalkMap` applied to
`RingHom.FormallyUnramified.ofLocalizationPrime`. Both are therefore reduced to a statement
about the tower of local rings `𝒪_{S, q y} → 𝒪_{Y, y} → 𝒪_{X, x}`, where `x` is any point of
`X` above `y`, which exists because `f` is surjective. The right-hand map is flat, because `f`
is flat, and local, so it is faithfully flat by
`Module.FaithfullyFlat.of_flat_of_isLocalHom`.

Flatness then descends by `flat_of_flat_of_faithfullyFlat`, which is the usual two-step
argument: tensoring an injective map of `R`-modules with `B` becomes, after applying the
faithfully flat `C ⊗[B] -`, the same map tensored with `C`, which is injective since `C` is
flat over `R`.

Formal unramifiedness descends by
`Stacks.RingTheory.FormallySmoothDescent.formallyUnramified_of_faithfullyFlat`. Its hypothesis
that `H¹(L_{C/B})` vanishes is free here: the stalk maps of a smooth morphism are formally
smooth by `AlgebraicGeometry.Scheme.Hom.smoothLocus_eq_top`, and a formally smooth algebra has
vanishing first cotangent homology.

With `Flat q` and `FormallyUnramified q` in hand, the hypothesis that `q` is locally of finite
presentation is exactly what `AlgebraicGeometry.Etale.of_formallyUnramified_of_flat` needs. It
cannot be dropped: an étale morphism is locally of finite presentation by definition, while a
non-trivial purely inseparable field extension is flat and formally unramified.

For a surjective `f` which is merely flat and locally of finite presentation, that hypothesis on
`q` nevertheless need not be assumed, because it is then provable: local finite presentation
descends along such an `f` by Tag 02KL,
`AlgebraicGeometry.locallyOfFinitePresentation_of_comp_of_fppf`. What remains is that such an
`f` is automatically étale, and this needs nothing beyond the composite: formal unramifiedness
is inherited by a morphism from any composite containing it, by
`AlgebraicGeometry.FormallyUnramified.of_comp`, so `f` is flat, locally of finite presentation
and formally unramified, hence étale. Étaleness of `f` is therefore *deduced* rather than
assumed, and the smooth analogue `Stacks.Smooth.smooth_of_comp_of_fppf` is not needed — which is
also what makes the argument available here, since
`StacksFrontier.AlgebraicGeometry.Descent.SmoothDescent` imports this file transitively through
`StacksFrontier.AlgebraicGeometry.Descent.SmoothAlgebra`.

## References

* [Stacks Project, Tag 02K6](https://stacks.math.columbia.edu/tag/02K6)
* [Stacks Project, Tag 05B5](https://stacks.math.columbia.edu/tag/05B5)
-/

@[expose] public section

open CategoryTheory TensorProduct AlgebraicGeometry

universe u

namespace Stacks.Etale

/-- **Descent of flatness along a faithfully flat ring map.** For a tower of rings
`R → B → C` with `C` faithfully flat over `B`, if `C` is flat over `R` then `B` is flat
over `R`. -/
theorem flat_of_flat_of_faithfullyFlat (R B C : Type u) [CommRing R] [CommRing B] [CommRing C]
    [Algebra R B] [Algebra B C] [Algebra R C] [IsScalarTower R B C]
    [Module.FaithfullyFlat B C] [Module.Flat R C] :
    Module.Flat R B := by
  rw [Module.Flat.iff_lTensor_preserves_injective_linearMap]
  intro N P _ _ _ _ f hf
  set g := AlgebraTensorModule.lTensor B B f with hg
  have h : Function.Injective (AlgebraTensorModule.lTensor C C g) := by
    have h' : Function.Injective
        ((AlgebraTensorModule.cancelBaseChange R B C C P).toLinearMap ∘ₗ
          AlgebraTensorModule.lTensor C C g) := by
      rw [hg, ← AlgebraTensorModule.lTensor_comp_cancelBaseChange]
      exact (Module.Flat.lTensor_preserves_injective_linearMap f hf).comp
        (AlgebraTensorModule.cancelBaseChange R B C C N).injective
    rw [LinearMap.coe_comp] at h'
    exact h'.of_comp
  exact (Module.FaithfullyFlat.lTensor_injective_iff_injective B C g).mp h

variable {X Y S : Scheme.{u}}

/-- The stalk maps of a flat morphism are faithfully flat, being flat and local. -/
private theorem faithfullyFlat_stalkMap (f : X ⟶ Y) [Flat f] (x : X) :
    (f.stalkMap x).hom.FaithfullyFlat := by
  algebraize [(f.stalkMap x).hom]
  have : Module.Flat (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) := Flat.stalkMap f x
  have : IsLocalHom (algebraMap (Y.presheaf.stalk (f x)) (X.presheaf.stalk x)) :=
    inferInstanceAs <| IsLocalHom (f.stalkMap x).hom
  exact RingHom.faithfullyFlat_algebraMap_iff.mpr Module.FaithfullyFlat.of_flat_of_isLocalHom

/-- **Stalkwise descent of flatness.** If `f : X ⟶ Y` is surjective and flat and the
composition `f ≫ q` with `q : Y ⟶ S` is flat, then every stalk map of `q` is flat. -/
theorem flat_stalkMap (f : X ⟶ Y) (q : Y ⟶ S) [Surjective f] [Flat f] [Flat (f ≫ q)] (y : Y) :
    (q.stalkMap y).hom.Flat := by
  obtain ⟨x, rfl⟩ := f.surjective y
  have hff := faithfullyFlat_stalkMap f x
  have hcf : ((f.stalkMap x).hom.comp (q.stalkMap (f x)).hom).Flat := by
    rw [← Stacks.ModuleSkyscraper.stalkMap_hom_comp]; exact Flat.stalkMap (f ≫ q) x
  algebraize [(q.stalkMap (f x)).hom, (f.stalkMap x).hom,
    (f.stalkMap x).hom.comp (q.stalkMap (f x)).hom]
  have h := RingHom.flat_algebraMap_iff.mpr
    (flat_of_flat_of_faithfullyFlat (S.presheaf.stalk (q (f x))) (Y.presheaf.stalk (f x))
      (X.presheaf.stalk x))
  rwa [RingHom.algebraMap_toAlgebra] at h

/-- **Stalkwise descent of formal unramifiedness.** If `f : X ⟶ Y` is surjective and smooth
and the composition `f ≫ q` with `q : Y ⟶ S` is formally unramified, then every stalk map of
`q` is formally unramified. -/
theorem formallyUnramified_stalkMap (f : X ⟶ Y) (q : Y ⟶ S) [Surjective f] [Smooth f]
    [FormallyUnramified (f ≫ q)] (y : Y) :
    (q.stalkMap y).hom.FormallyUnramified := by
  obtain ⟨x, rfl⟩ := f.surjective y
  have hfs : (f.stalkMap x).hom.FormallySmooth := by
    have h := f.smoothLocus_eq_top
    rw [← Scheme.Hom.mem_smoothLocus, h]
    trivial
  have hff := faithfullyFlat_stalkMap f x
  have hcu : ((f.stalkMap x).hom.comp (q.stalkMap (f x)).hom).FormallyUnramified := by
    rw [← Stacks.ModuleSkyscraper.stalkMap_hom_comp]; exact FormallyUnramified.stalkMap (f ≫ q) x
  algebraize [(q.stalkMap (f x)).hom, (f.stalkMap x).hom,
    (f.stalkMap x).hom.comp (q.stalkMap (f x)).hom]
  have h := RingHom.formallyUnramified_algebraMap.mpr
    (RingTheory.FormallySmoothDescent.formallyUnramified_of_faithfullyFlat
      (S.presheaf.stalk (q (f x))) (Y.presheaf.stalk (f x)) (X.presheaf.stalk x))
  rwa [RingHom.algebraMap_toAlgebra] at h

/-- **Stacks Project, Tag 02K6.** If `f : X ⟶ Y` is surjective and étale, the composition
`f ≫ q` is étale and `q : Y ⟶ S` is locally of finite presentation, then `q` is étale. -/
@[stacks 02K6]
theorem etale_of_comp_surjective_etale_of_locallyOfFinitePresentation (f : X ⟶ Y) (q : Y ⟶ S)
    [Surjective f] [Etale f] [Etale (f ≫ q)] [LocallyOfFinitePresentation q] :
    Etale q :=
  have : Flat q := Flat.of_stalkMap q (flat_stalkMap f q)
  have : FormallyUnramified q :=
    HasRingHomProperty.of_stalkMap RingHom.FormallyUnramified.ofLocalizationPrime
      (formallyUnramified_stalkMap f q)
  Etale.of_formallyUnramified_of_flat q

/-- **Stacks Project, Tag 05B5 (étale case).** Étaleness descends along a surjective flat
morphism which is locally of finite presentation: if `f : X ⟶ Y` is surjective, flat and locally
of finite presentation and `f ≫ q` is étale, then `q : Y ⟶ S` is étale. -/
@[stacks 05B5 "etale_permanence"]
theorem etale_of_comp_of_fppf (f : X ⟶ Y) (q : Y ⟶ S) [Surjective f] [Flat f]
    [LocallyOfFinitePresentation f] [Etale (f ≫ q)] : Etale q :=
  have : FormallyUnramified f := FormallyUnramified.of_comp f q
  have : Etale f := Etale.of_formallyUnramified_of_flat f
  have : LocallyOfFinitePresentation q := locallyOfFinitePresentation_of_comp_of_fppf f q
  etale_of_comp_surjective_etale_of_locallyOfFinitePresentation f q

end Stacks.Etale

end
