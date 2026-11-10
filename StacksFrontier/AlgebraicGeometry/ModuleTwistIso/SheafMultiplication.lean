module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjTwistModuleMultiplication
public import StacksFrontier.AlgebraicGeometry.ModuleTwistIso.Multiplication
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.TildeTensorSections
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensorComparisonIso

/-!
# Equation 03GJ restricted to a standard open of `Proj`

Let `S` be a graded ring, `X = Proj(S)`, `ℱ` a sheaf of `𝒪_X`-modules and `f` homogeneous of
degree `d`. Equation 03GJ's multiplication map `𝒪_X(n) ⊗ ℱ(m) ⟶ ℱ(n + m)` restricts to an
isomorphism on the standard open `D₊(f)` whenever the first index is a multiple of `d`. This is
the remaining clause of Tag 01MS.

## Main results

* `Stacks.AlgebraicGeometry.ModuleTwistIso.isIso_restrict_twistSheafMultiplicationMap_basicOpen`:
  **Stacks Tag 01MS**, Equation 03GJ restricted to `D₊(f)`.
* `Stacks.AlgebraicGeometry.ModuleTwistIso.isIso_restrictFunctor_map_tensorSheafMap`:
  restriction to an open takes a tensor product of two morphisms to an isomorphism as soon as it
  takes each factor to one. This is what makes a *restricted* isomorphism usable inside a tensor
  product, which the functoriality of `Stacks.SheafOfModules.Tensor.sheafTensor` alone cannot
  do: it needs its two arguments to be isomorphisms on all of `X`.

## The route

`AlgebraicGeometry.ProjectiveSpectrum.Proj.twistSheafMultiplicationMap` is by construction
`f₁ ≫ f₂ ≫ f₃ ≫ f₄` with `f₁`, `f₂`, `f₃` the inverse associator, the braiding tensored with
`𝒪(m)` and the associator — isomorphisms outright, so any functor carries them to isomorphisms —
and `f₄ = 𝟙_ℱ ⊗ (Equation 01MO)`. On `D₊(f)` the last factor is *not* an isomorphism before
restriction, and restriction is not known to commute with
`Stacks.SheafOfModules.Tensor.sheafTensor`, so `f₄` is handled by
`isIso_restrictFunctor_map_tensorSheafMap`, whose input is
`isIso_restrict_twistMultiplicationMap_basicOpen`, Tag 01MS for Equation 01MO.

That lemma is Stacks 01CD read along the open immersion: the comparison
`Stacks.RingedSpace.comparisonBifunctorIso` is a natural isomorphism *of bifunctors* between
`j^*(A ⊗ B)` and `j^*A ⊗ j^*B`, so its naturality square at `(φ, ψ)` identifies
`j^*(φ ⊗ ψ)` with `j^*φ ⊗ j^*ψ` up to two isomorphisms; the latter is an isomorphism because
the tensor bifunctor carries the pair of isomorphisms `(j^*φ, j^*ψ)` to one. The concrete
restriction is crossed to the abstract inverse image by
`AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback`, whose being a natural isomorphism
is all that is used, through `CategoryTheory.NatIso.isIso_map_iff`.

## Implementation notes

The three unconditional isomorphisms are produced with their types written out: the morphisms of
the composite live in `SheafOfModules` over `(sheafCompose …).obj (structureSheaf 𝒮)` while
`AlgebraicGeometry.Scheme.Modules.restrictFunctor` is stated over `(Proj 𝒮).ringCatSheaf`, and
the two spellings are definitionally equal but not interchangeable by instance search. For the
same reason `isIso_map_comp₄` takes the invertibility of the first three factors as *arguments*
rather than finding them, and the final step is an `exact` rather than a `rw`.

## References

* [Stacks Project, Tag 01MS](https://stacks.math.columbia.edu/tag/01MS)
* [Stacks Project, Tag 03GJ](https://stacks.math.columbia.edu/tag/03GJ)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite
open AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open RingedSpaceModuleAdjunction
open Stacks.AlgebraicGeometry.ProjInvertibleLocus
open Stacks.SheafOfModules.TensorStalkRingedSpace

namespace Stacks.AlgebraicGeometry.ModuleTwistIso

universe u w

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose
  Stacks.SheafOfModules.TensorSheafification.structureSheaf
attribute [local instance_reducible] ProjectiveSpectrum.top

/-! ### Restricting a tensor product of two morphisms -/

/-- **A tensor product of morphisms restricted to an open.** If restriction to an open
subscheme carries each of two morphisms of sheaves of modules to an isomorphism, then it carries
their tensor product to an isomorphism. Restriction is not known to commute with the sheafified
tensor product, so this is proved from Stacks 01CD for the open immersion, whose comparison is
natural in both arguments. -/
lemma isIso_restrictFunctor_map_tensorSheafMap {X Y : Scheme.{u}} (j : X ⟶ Y)
    [IsOpenImmersion j] {A A' B B' : Y.Modules} (φ : A ⟶ A') (ψ : B ⟶ B')
    (hφ : IsIso ((Scheme.Modules.restrictFunctor j).map φ))
    (hψ : IsIso ((Scheme.Modules.restrictFunctor j).map ψ)) :
    IsIso ((Scheme.Modules.restrictFunctor j).map
      (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨((Y.toRingedSpace)).presheaf, ((Y.toRingedSpace)).IsSheaf⟩)).map
        ((φ, ψ) : (_, _) ⟶ (_, _))))) := by
  set f := j.toLRSHom.toShHom with hf
  set e := Scheme.Modules.restrictFunctorIsoPullback j with he
  have hpull : ∀ {M N : Y.Modules} (χ : M ⟶ N),
      IsIso ((Scheme.Modules.restrictFunctor j).map χ) →
        IsIso ((Stacks.RingedSpace.pullbackFunctor f).map χ) :=
    fun χ h => (CategoryTheory.NatIso.isIso_map_iff e χ).mp h
  have hφ' := hpull φ hφ
  have hψ' := hpull ψ hψ
  refine (CategoryTheory.NatIso.isIso_map_iff e _).mpr ?_
  have hnat := (Stacks.RingedSpace.comparisonBifunctorIso f).hom.naturality
    ((φ, ψ) : ((A, B) : _ × _) ⟶ (A', B'))
  have h1 : IsIso ((Functor.prod (Stacks.RingedSpace.pullbackFunctor f)
      (Stacks.RingedSpace.pullbackFunctor f) ⋙
        (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩))).map
      ((φ, ψ) : ((A, B) : _ × _) ⟶ (A', B'))) :=
    ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩)).mapIso
      ((@asIso _ _ _ _ _ hφ').prod (@asIso _ _ _ _ _ hψ'))).isIso_hom
  have hcomp : ∀ P : Y.Modules × Y.Modules,
      IsIso ((Stacks.RingedSpace.comparisonBifunctorIso f).hom.app P) :=
    fun P => Stacks.RingedSpace.comparisonNatTrans_app_isIso f P
  have hright := (congrArg IsIso hnat).mpr (IsIso.comp_isIso' (hcomp (A, B)) h1)
  exact @IsIso.of_isIso_comp_right _ _ _ _ _ _
    ((Stacks.RingedSpace.comparisonBifunctorIso f).hom.app ((A', B') : _ × _))
    (hcomp (A', B')) hright

/-- A functor carries a composite of four morphisms to an isomorphism as soon as the first three
are isomorphisms and it carries the fourth to one. The three hypotheses are taken as arguments
because at the intended application the morphisms live in a definitionally equal but distinct
spelling of the category, which instance search does not cross. -/
lemma isIso_map_comp₄ {C D : Type*} [Category C] [Category D] (G : C ⥤ D) {V X Y Z T : C}
    (a : V ⟶ X) (b : X ⟶ Y) (c : Y ⟶ Z) (e : Z ⟶ T)
    (ha : IsIso a) (hb : IsIso b) (hc : IsIso c) (he : IsIso (G.map e)) :
    IsIso (G.map (a ≫ b ≫ c ≫ e)) := by
  have := ha
  have := hb
  have := hc
  rw [G.map_comp, G.map_comp, G.map_comp]
  exact IsIso.comp_isIso' inferInstance
    (IsIso.comp_isIso' inferInstance (IsIso.comp_isIso' inferInstance he))

variable {S : Type u} {σ : Type w} [CommRing S] [SetLike σ S] [AddSubgroupClass σ S]
  (𝒮 : ℕ → σ) [GradedRing 𝒮]

/-! ### Stacks Tag 01MS for Equation 03GJ -/

/-- **Stacks Tag 01MS.** Let `f` be homogeneous of degree `d` and let `ℱ` be a sheaf of
`𝒪_X`-modules. Then for all integers `n` and `m` the multiplication map of Equation 03GJ,

`𝒪_X(nd)|_{D₊(f)} ⊗_{𝒪_{D₊(f)}} ℱ(m)|_{D₊(f)} ⟶ ℱ(nd+m)|_{D₊(f)}`,

is an isomorphism. The second index is arbitrary, as in the source; the positivity of `d` is not
used. -/
theorem isIso_restrict_twistSheafMultiplicationMap_basicOpen
    (F : SheafOfModules.{u}
      ((sheafCompose (Opens.grothendieckTopology (ProjectiveSpectrum.top 𝒮))
        (forget₂ CommRingCat.{u} RingCat.{u})).obj
        (ProjectiveSpectrum.Proj.structureSheaf 𝒮)))
    {g : S} {d : ℕ} (hg : g ∈ 𝒮 d) (n m : ℤ) :
    IsIso ((Scheme.Modules.restrictFunctor (AlgebraicGeometry.Proj.basicOpen 𝒮 g).ι).map
      (twistSheafMultiplicationMap 𝒮 F ((d : ℤ) * n) m)) := by
  have h1 : IsIso (Stacks.SheafOfModules.Invertible.tensorProductAssociator
      (ProjectiveSpectrum.Proj.structureSheaf 𝒮).obj
      (hO := ((sheafCompose (Opens.grothendieckTopology (ProjectiveSpectrum.top 𝒮))
        (forget₂ CommRingCat.{u} RingCat.{u})).obj
        (ProjectiveSpectrum.Proj.structureSheaf 𝒮)).property)
      (twistingSheaf 𝒮 ((d : ℤ) * n)) F (twistingSheaf 𝒮 m)).inv := inferInstance
  have h2 : IsIso (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨(((AlgebraicGeometry.Proj 𝒮).toRingedSpace)).presheaf,
        (((AlgebraicGeometry.Proj 𝒮).toRingedSpace)).IsSheaf⟩)).map
      (((Stacks.SheafOfModules.Invertible.tensorProductBraiding
        (ProjectiveSpectrum.Proj.structureSheaf 𝒮).obj
        (hO := ((sheafCompose (Opens.grothendieckTopology (ProjectiveSpectrum.top 𝒮))
          (forget₂ CommRingCat.{u} RingCat.{u})).obj
          (ProjectiveSpectrum.Proj.structureSheaf 𝒮)).property)
        (twistingSheaf 𝒮 ((d : ℤ) * n)) F).hom, (𝟙 (twistingSheaf 𝒮 m))) : (_, _) ⟶ (_, _)))) :=
    ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨(((AlgebraicGeometry.Proj 𝒮).toRingedSpace)).presheaf,
        (((AlgebraicGeometry.Proj 𝒮).toRingedSpace)).IsSheaf⟩)).mapIso
      (Iso.prod (Stacks.SheafOfModules.Invertible.tensorProductBraiding
        (ProjectiveSpectrum.Proj.structureSheaf 𝒮).obj
        (hO := ((sheafCompose (Opens.grothendieckTopology (ProjectiveSpectrum.top 𝒮))
          (forget₂ CommRingCat.{u} RingCat.{u})).obj
          (ProjectiveSpectrum.Proj.structureSheaf 𝒮)).property)
        (twistingSheaf 𝒮 ((d : ℤ) * n)) F)
      (Iso.refl (twistingSheaf 𝒮 m)))).isIso_hom
  have h3 : IsIso (Stacks.SheafOfModules.Invertible.tensorProductAssociator
      (ProjectiveSpectrum.Proj.structureSheaf 𝒮).obj
      (hO := ((sheafCompose (Opens.grothendieckTopology (ProjectiveSpectrum.top 𝒮))
        (forget₂ CommRingCat.{u} RingCat.{u})).obj
        (ProjectiveSpectrum.Proj.structureSheaf 𝒮)).property)
      F (twistingSheaf 𝒮 ((d : ℤ) * n)) (twistingSheaf 𝒮 m)).hom := inferInstance
  have h4 : IsIso ((Scheme.Modules.restrictFunctor
      (AlgebraicGeometry.Proj.basicOpen 𝒮 g).ι).map
      (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨(((AlgebraicGeometry.Proj 𝒮).toRingedSpace)).presheaf,
          (((AlgebraicGeometry.Proj 𝒮).toRingedSpace)).IsSheaf⟩)).map
        (((𝟙 F), (twistMultiplicationMap 𝒮 ((d : ℤ) * n) m)) : (_, _) ⟶ (_, _))))) :=
    isIso_restrictFunctor_map_tensorSheafMap _ _ _
      (((Scheme.Modules.restrictFunctor
        (AlgebraicGeometry.Proj.basicOpen 𝒮 g).ι).mapIso (Iso.refl F)).isIso_hom)
      (isIso_restrict_twistMultiplicationMap_basicOpen 𝒮 hg n m)
  change IsIso ((Scheme.Modules.restrictFunctor
    (AlgebraicGeometry.Proj.basicOpen 𝒮 g).ι).map (_ ≫ _ ≫ _ ≫ _))
  exact isIso_map_comp₄ _ _ _ _ _ h1 h2 h3 h4

end Stacks.AlgebraicGeometry.ModuleTwistIso

end
