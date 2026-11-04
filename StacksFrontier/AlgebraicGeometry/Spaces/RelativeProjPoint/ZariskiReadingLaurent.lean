module

public import StacksFrontier.AlgebraicGeometry.Spaces.BaseChangeModuleInvertible
public import StacksFrontier.AlgebraicGeometry.TwistTensor.GradedLaurentMul
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LaurentAlgebraToposPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjPoint.AlgebraHom
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjPoint.ZariskiReadingTensor

/-!
# The Zariski reading of a sheaf of graded algebras with invertible multiplications

Let `U` be an object of the big fppf site with underlying scheme `T`. The Zariski reading
`AlgebraicGeometry.Space.zariskiReading` reads a sheaf of graded algebras on the small étale site
of the algebraic space `yoneda.obj U` on the Zariski opens of `T`. This file shows that the
reading preserves invertibility of the multiplications of an algebra with quasi-coherent pieces
and invertibility of modules, and deduces that the reading of the Laurent algebra
`⨁_{n ∈ ℤ} 𝒩^{⊗ n}` of an invertible module `𝒩` is the Laurent algebra of the reading of `𝒩`.

## Main results

* `AlgebraicGeometry.Space.mulSheaf_zariskiReading`: the multiplication of the reading is the
  comparison of the reading with tensor products followed by the reading of the multiplication.
* `AlgebraicGeometry.Space.isIso_mulSheaf_zariskiReading`: if the multiplications of `ℰ` are
  isomorphisms and its pieces are quasi-coherent, so are those of the reading.
* `AlgebraicGeometry.Space.isInvertibleModule_zariskiReading`: the reading of an invertible
  module is invertible.
* `AlgebraicGeometry.Space.zariskiReadingLaurentIso`: **the reading of the Laurent algebra of an
  invertible module is the Laurent algebra of its degree-one piece**, by the recognition theorem
  `Stacks.AlgebraicGeometry.GradedLaurentRecognition.gradedIso`.
* `AlgebraicGeometry.Space.pointLine` and `isInvertible_pointLine`: the restriction `x^*ℒ` of an
  invertible module `ℒ` on an algebraic space `X` to a scheme point `x : T ⟶ X`, an invertible
  `𝒪_T`-module.
* `AlgebraicGeometry.Space.pointLaurentHom`: **the restriction of the Laurent algebra of `ℒ` to a
  scheme point is the Laurent algebra of `x^*ℒ`**, as a unital homomorphism of sheaves of graded
  algebras which is an isomorphism in every degree.

**No `@[stacks]` attribute.** These are steps of the construction of the restriction of
`(ℒ, ψ)` to a scheme point in Stacks 0D2Z.

## Implementation notes

`AlgebraicGeometry.Space.pointLine` is the one construction of the restriction `x^*ℒ`: the
restriction datum of a pair `(ℒ, ψ)` on `X`
(`AlgebraicGeometry.Space.RelativeProjSituation.InvertibleTwistingRestriction.ofUnitalHom`) takes
it as its field `line`.  It is marked irreducible once `pointLaurentHom` is built, and is reached
through `isInvertible_pointLine` and `pointLaurentHom`.

## References

* [Stacks Project, Tag 0D2Z](https://stacks.math.columbia.edu/tag/0D2Z)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped TensorProduct

namespace AlgebraicGeometry.Space

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (U : BigFppfOver B S hS)

/-- **The multiplication of the Zariski reading** of a sheaf of graded algebras `ℰ` with
quasi-coherent pieces is the comparison of the reading with tensor products followed by the
reading of the multiplication of `ℰ`. -/
theorem mulSheaf_zariskiReading
    (E : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf B S hS (yonedaSpace B S hS U)))
    (hE : ∀ n, (E.piece n).IsQuasicoherentOnSite) (i j : ℤ) :
    SheafOfModules.GradedAlgebra.mulSheaf (zariskiReading U E) i j =
      zariskiReadingTensorHom B S hS U (E.piece i) (E.piece j) (hE i) (hE j) ≫
        (SheafOfModules.pushforward.{u} (selfOpensStructureMap B S hS U)).map
          (SheafOfModules.GradedAlgebra.mulSheaf E i j) := by
  refine PresheafOfModules.tensorSheaf_hom_ext
    (Osharp := (chartScheme (idEtaleChart B S hS U)).sheaf) (fun V x y => ?_)
  refine (SheafOfModules.GradedAlgebra.mulSheaf_unit (zariskiReading U E) i j V x y).trans ?_
  refine Eq.trans ?_ (SheafOfModules.comp_val_app_apply _ _ V _).symm
  refine Eq.trans ?_ (congrArg _ (zariskiReadingTensorHom_val_app_unit_tmul B S hS U
    (E.piece i) (E.piece j) (hE i) (hE j) V x y).symm)
  exact (SheafOfModules.GradedAlgebra.mulSheaf_unit E i j _ x y).symm

/-- **The Zariski reading preserves invertibility of the multiplications** of a sheaf of graded
algebras with quasi-coherent pieces. -/
theorem isIso_mulSheaf_zariskiReading
    (E : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf B S hS (yonedaSpace B S hS U)))
    (hE : ∀ n, (E.piece n).IsQuasicoherentOnSite)
    (hmul : ∀ i j : ℤ, IsIso (SheafOfModules.GradedAlgebra.mulSheaf E i j)) (i j : ℤ) :
    IsIso (SheafOfModules.GradedAlgebra.mulSheaf (zariskiReading U E) i j) := by
  rw [mulSheaf_zariskiReading B S hS U E hE i j]
  exact IsIso.comp_isIso' (isIso_zariskiReadingTensorHom B S hS U _ _ (hE i) (hE j))
    (@Functor.map_isIso _ _ _ _ _ _ _ _ (hmul i j))

section Invertible

attribute [local instance] modulesMonoidalCategory

/-- **The Zariski reading of an invertible module is invertible**: for an invertible `𝒪`-module
`𝒩` on the small étale site of `yoneda.obj U`, its reading on the Zariski site of the scheme `T`
of `U` is an invertible `𝒪_T`-module.

A tensor inverse `𝒩'` of `𝒩` is invertible, hence quasi-coherent, and the reading is compatible
with tensor products of quasi-coherent modules
(`AlgebraicGeometry.Space.restrictToChartSchemeIdEtaleChartTensorIso`) and with the structure
sheaf (`AlgebraicGeometry.Space.restrictToChartSchemeUnitIso`), so the reading of `𝒩'` is a
tensor inverse of the reading of `𝒩`. -/
theorem isInvertibleModule_zariskiReading
    (N : Modules.{u, u} B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U))
    (hN : Stacks.SheafOfModules.IsInvertible (J := SmallEtale.topology B S hS (yoneda.obj U))
      (structurePresheaf B S hS (yoneda.obj U))
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U)).O)).property
      N) :
    Stacks.Ample.IsInvertibleModule ((BigFppfOver.toScheme B S hS).obj U)
      ((SheafOfModules.pushforward.{u} (selfOpensStructureMap B S hS U)).obj N) := by
  let U' : AlgebraicSpaces B S hS := ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩
  obtain ⟨N₀, ⟨e⟩⟩ := (Stacks.SheafOfModules.Invertible.isInvertible_iff_exists_tensor_iso_unit
    _ _ _).1 hN
  let N' : Modules.{u, u} B S hS U'.1 U'.2 := N₀
  have hN' := Stacks.SheafOfModules.Invertible.isInvertible_of_tensor_iso_unit _
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS U').O).property (N := N)
    ((modulesTensorObjIso B S hS _ _ N' N).symm ≪≫
      (modulesBraidedCategory B S hS U'.1 U'.2).braiding N' N ≪≫
      modulesTensorObjIso B S hS _ _ N N' ≪≫ e)
  have qN : N.IsQuasicoherentOnSite :=
    isQuasicoherentOnSite_of_isInvertible B S hS U' N (hN.toAlgebraicGeometry _ _ _)
  have qN' : N'.IsQuasicoherentOnSite :=
    isQuasicoherentOnSite_of_isInvertible B S hS _ _ (hN'.toAlgebraicGeometry _ _ _)
  let t := restrictToChartSchemeIdEtaleChartTensorIso B S hS U N N' qN qN'
  let r := restrictToChartSchemeFunctor B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U)
    (idEtaleChart B S hS U)
  let v := restrictToChartSchemeUnitIso B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U)
    (idEtaleChart B S hS U)
  let e' := t.symm ≪≫ r.mapIso (modulesTensorObjIso B S hS _ _ N N' ≪≫ e) ≪≫ v
  have h := (Stacks.SheafOfModules.Invertible.isInvertible_of_tensor_iso_unit _ _ e')
  exact Stacks.SheafOfModules.isInvertible_of_iso _ _
    (restrictToChartSchemeIdEtaleChartIso B S hS U N ≪≫ selfOpensPushforwardIso B S hS U N)

variable (N : Modules.{u, u} B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U))
  [hN : Stacks.SheafOfModules.IsInvertible (J := SmallEtale.topology B S hS (yoneda.obj U))
    (structurePresheaf B S hS (yoneda.obj U))
    ((Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B S hS (yoneda.obj U)
        (isAlgebraicSpace_yoneda B S hS U)).O)).property N]

/-- The integer tensor powers of an invertible `𝒪`-module on the small étale site of
`yoneda.obj U` are quasi-coherent. -/
theorem isQuasicoherentOnSite_laurentAlgebra_piece (n : ℤ) :
    ((Stacks.SheafOfModules.TensorPower.laurentAlgebra
      (J := SmallEtale.topology B S hS (yoneda.obj U)) (structurePresheaf B S hS (yoneda.obj U))
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS (yoneda.obj U)
          (isAlgebraicSpace_yoneda B S hS U)).O)).property N).piece n).IsQuasicoherentOnSite :=
  isQuasicoherentOnSite_of_isInvertible B S hS ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩ _
    ((@Stacks.SheafOfModules.TensorPower.isInvertible_tensorPower _ _
      (SmallEtale.topology B S hS (yoneda.obj U)) (structurePresheaf B S hS (yoneda.obj U))
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS (yoneda.obj U)
          (isAlgebraicSpace_yoneda B S hS U)).O)).property _ _ N hN n).toAlgebraicGeometry
      _ _ _)

/-- The Zariski reading of the Laurent algebra of an invertible `𝒪`-module has invertible
multiplications. -/
theorem isIso_mulSheaf_zariskiReading_laurentAlgebra (i j : ℤ) :
    IsIso (SheafOfModules.GradedAlgebra.mulSheaf (zariskiReading U
      (Stacks.SheafOfModules.TensorPower.laurentAlgebra
        (J := SmallEtale.topology B S hS (yoneda.obj U)) (structurePresheaf B S hS (yoneda.obj U))
        ((Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B S hS (yoneda.obj U)
            (isAlgebraicSpace_yoneda B S hS U)).O)).property N)) i j) :=
  isIso_mulSheaf_zariskiReading B S hS U _
    (isQuasicoherentOnSite_laurentAlgebra_piece B S hS U N)
    (fun i j => (congrArg IsIso (@Stacks.SheafOfModules.TensorPower.mulSheaf_laurentAlgebra _ _
      (SmallEtale.topology B S hS (yoneda.obj U)) _ _ _
      (structureSheaf B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U))
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS (yoneda.obj U)
          (isAlgebraicSpace_yoneda B S hS U)).O)).property N hN i j)).mpr
        (Iso.isIso_hom _)) i j

/-- The degree-`n` piece of the Zariski reading of the Laurent algebra of an invertible
`𝒪`-module is an invertible `𝒪_T`-module. -/
instance isInvertible_zariskiReading_laurentAlgebra_piece (n : ℤ) :
    Stacks.SheafOfModules.IsInvertible (chartScheme (idEtaleChart B S hS U)).toRingedSpace.presheaf
      (Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.isSheafStruct
        (chartScheme (idEtaleChart B S hS U)))
      ((zariskiReading U (Stacks.SheafOfModules.TensorPower.laurentAlgebra
        (J := SmallEtale.topology B S hS (yoneda.obj U)) (structurePresheaf B S hS (yoneda.obj U))
        ((Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B S hS (yoneda.obj U)
            (isAlgebraicSpace_yoneda B S hS U)).O)).property N)).piece n) :=
  isInvertibleModule_zariskiReading B S hS U _
    (@Stacks.SheafOfModules.TensorPower.isInvertible_tensorPower _ _
      (SmallEtale.topology B S hS (yoneda.obj U)) (structurePresheaf B S hS (yoneda.obj U))
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS (yoneda.obj U)
          (isAlgebraicSpace_yoneda B S hS U)).O)).property _ _ N hN n)

/-- **Stacks 0D2Z, piece (1)(a2): the Zariski reading of the Laurent algebra of an invertible
module is the Laurent algebra of the reading.** For an invertible `𝒪`-module `𝒩` on the small
étale site of `yoneda.obj U`, the Zariski reading of `⨁_{n ∈ ℤ} 𝒩^{⊗ n}` on the scheme `T` of `U`
is isomorphic, as a sheaf of graded algebras, to the Laurent algebra `⨁_{n ∈ ℤ} ℒ^{⊗ n}` of its
degree-one piece `ℒ = 𝒩|_T`. This is the recognition theorem
`Stacks.AlgebraicGeometry.GradedLaurentRecognition.gradedIso`: the multiplications of the reading
are invertible (`isIso_mulSheaf_zariskiReading_laurentAlgebra`) and its degree-zero piece is
invertible. -/
def zariskiReadingLaurentIso :
    (zariskiReading U (Stacks.SheafOfModules.TensorPower.laurentAlgebra
        (J := SmallEtale.topology B S hS (yoneda.obj U)) (structurePresheaf B S hS (yoneda.obj U))
        ((Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B S hS (yoneda.obj U)
            (isAlgebraicSpace_yoneda B S hS U)).O)).property N) :
      SheafOfModules.GradedAlgebra.{u, u}
        (Stacks.RingedSpace.structureRingSheaf
          (chartScheme (idEtaleChart B S hS U)).toRingedSpace)) ≅
      Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.laurent
        ((zariskiReading U (Stacks.SheafOfModules.TensorPower.laurentAlgebra
          (J := SmallEtale.topology B S hS (yoneda.obj U)) (structurePresheaf B S hS (yoneda.obj U))
          ((Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedSite B S hS (yoneda.obj U)
              (isAlgebraicSpace_yoneda B S hS U)).O)).property N)).piece 1) :=
  Stacks.AlgebraicGeometry.GradedLaurentRecognition.gradedIso _ _ (Iso.refl _)
    (isIso_mulSheaf_zariskiReading_laurentAlgebra B S hS U N)
    (isInvertible_zariskiReading_laurentAlgebra_piece B S hS U N 0)

end Invertible

section Point

variable {X : AlgebraicSpaces B S hS}
  (L : SheafOfModules.{u}
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS X).O))
  [hL : Stacks.SheafOfModules.IsInvertible (smallEtaleRingedTopos B S hS X).O.obj
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS X).O).property L]
  (T : BigFppfOver B S hS) (x : yoneda.obj T ⟶ X.1)

/-- The degree-`n` component of an isomorphism of sheaves of graded algebras is an isomorphism. -/
private theorem isIso_hom_app {C : Type*} [Category C] {J : GrothendieckTopology C}
    {R' : Sheaf J RingCat.{u}} {E₁ E₂ : SheafOfModules.GradedAlgebra.{u, u} R'} (e : E₁ ≅ E₂)
    (n : ℤ) : IsIso (e.hom.app n) :=
  ⟨e.inv.app n, congrArg (fun h => SheafOfModules.GradedAlgebra.Hom.app h n) e.hom_inv_id,
    congrArg (fun h => SheafOfModules.GradedAlgebra.Hom.app h n) e.inv_hom_id⟩

/-- The isomorphism of degree-zero pieces underlying an isomorphism of sheaves of graded
algebras is an isomorphism. -/
theorem isIso_hom_app_zero {C : Type*} [Category C] {J : GrothendieckTopology C}
    {R' : Sheaf J RingCat.{u}} {E₁ E₂ : SheafOfModules.GradedAlgebra.{u, u} R'} (e : E₁ ≅ E₂) :
    IsIso (e.hom.app 0) :=
  isIso_hom_app e 0

/-- The pullback of `ℒ` to the small étale site of a scheme point is invertible. -/
instance isInvertible_pointPullback :
    Stacks.SheafOfModules.IsInvertible (J := SmallEtale.topology B S hS (yoneda.obj T))
      (structurePresheaf B S hS (yoneda.obj T))
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T)).O)).property
      ((smallEtaleRingedToposModulesHom B S hS (pointHom x)).pullbackModules.obj L) :=
  Stacks.SheafOfModules.isInvertible_pullbackModules_obj
    (smallEtaleRingedToposModulesHom B S hS (pointHom x)) L

/-- **The restriction `x^*ℒ` of `ℒ` to a scheme point `x : T ⟶ X`**: the Zariski reading on `T`
of the degree-one piece of the Laurent algebra of the pullback of `ℒ` along the morphism of small
étale ringed topoi of `x`. -/
def pointLine : SheafOfModules.{u}
    (Stacks.RingedSpace.structureRingSheaf (chartScheme (idEtaleChart B S hS T)).toRingedSpace) :=
  (zariskiReading T (Stacks.SheafOfModules.TensorPower.laurentAlgebra
    (J := SmallEtale.topology B S hS (yoneda.obj T)) (structurePresheaf B S hS (yoneda.obj T))
    ((Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B S hS (yoneda.obj T)
        (isAlgebraicSpace_yoneda B S hS T)).O)).property
    ((smallEtaleRingedToposModulesHom B S hS (pointHom x)).pullbackModules.obj L))).piece 1

/-- The restriction of an invertible module to a scheme point is invertible. -/
instance isInvertible_pointLine :
    Stacks.SheafOfModules.IsInvertible (chartScheme (idEtaleChart B S hS T)).toRingedSpace.presheaf
      (Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.isSheafStruct
        (chartScheme (idEtaleChart B S hS T))) (pointLine B S hS L T x) :=
  @isInvertible_zariskiReading_laurentAlgebra_piece B S hS T _
    (isInvertible_pointPullback B S hS L T x) 1

/-- **Stacks 0D2Z, piece (1)(a), at a scheme point: the restriction of the Laurent algebra of `ℒ`
to a scheme point `x : T ⟶ X` is the Laurent algebra of the restriction of `ℒ`.** The Zariski
reading on `T` of the pullback of `⨁_{n ∈ ℤ} ℒ^{⊗ n}` along the morphism of small étale ringed
topoi of `x` is isomorphic, by a unital homomorphism of sheaves of graded algebras, to the Laurent
algebra of the reading of `x^*ℒ`: the pullback of the Laurent algebra is the Laurent algebra of the
pullback (`Stacks.SheafOfModules.RingedToposPullback.laurentToposPullbackIso`), and the reading of
a Laurent algebra is the Laurent algebra of the reading
(`AlgebraicGeometry.Space.zariskiReadingLaurentIso`). -/
def pointLaurentHom :
    SheafOfModules.GradedAlgebra.UnitalHom
      (zariskiReading T (etalePointAlgebra
        (Stacks.SheafOfModules.TensorPower.laurentAlgebra (smallEtaleRingedTopos B S hS X).O.obj
          (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS X).O).property L)
        T x))
      (Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.laurent (pointLine B S hS L T x)) :=
  (zariskiReadingHom T (@SheafOfModules.GradedAlgebra.UnitalHom.ofHomOfIsIso _ _ _ _ _ _
      (Stacks.SheafOfModules.RingedToposPullback.laurentToposPullbackIso
        (smallEtaleRingedToposModulesHom B S hS (pointHom x)) L).hom
      (isIso_hom_app_zero (Stacks.SheafOfModules.RingedToposPullback.laurentToposPullbackIso
        (smallEtaleRingedToposModulesHom B S hS (pointHom x)) L)))).comp
    (@SheafOfModules.GradedAlgebra.UnitalHom.ofHomOfIsIso _ _ _ _ _ _
      (zariskiReadingLaurentIso B S hS T
        ((smallEtaleRingedToposModulesHom B S hS (pointHom x)).pullbackModules.obj L)).hom
      (isIso_hom_app_zero (zariskiReadingLaurentIso B S hS T
        ((smallEtaleRingedToposModulesHom B S hS (pointHom x)).pullbackModules.obj L))))

/-- `AlgebraicGeometry.Space.pointLaurentHom` is an isomorphism in every degree. -/
theorem isIso_pointLaurentHom_app (n : ℤ) : IsIso ((pointLaurentHom B S hS L T x).app n) := by
  have h₁ := isIso_hom_app (Stacks.SheafOfModules.RingedToposPullback.laurentToposPullbackIso
    (smallEtaleRingedToposModulesHom B S hS (pointHom x)) L) n
  have h₂ := isIso_hom_app (zariskiReadingLaurentIso B S hS T
    ((smallEtaleRingedToposModulesHom B S hS (pointHom x)).pullbackModules.obj L)) n
  exact IsIso.comp_isIso' ((SheafOfModules.pushforward.{u} (selfOpensStructureMap B S hS T)).mapIso
    (@asIso _ _ _ _ _ h₁)).isIso_hom h₂

attribute [irreducible] pointLine

end Point

end AlgebraicGeometry.Space
