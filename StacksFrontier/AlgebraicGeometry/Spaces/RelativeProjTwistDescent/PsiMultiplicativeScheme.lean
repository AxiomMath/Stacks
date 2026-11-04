module

public import
  StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjTwistDescent.PsiMultiplicativeAssembly
public import StacksFrontier.AlgebraicGeometry.TwistTensor.PsiLegUnit

/-!
# `ψ` of Stacks 084D is multiplicative and unital

In Situation 0849 let `V ×_X P` be the base change of the relative Proj `P = Proj_X(𝒜)` to a
scheme point `v : V ⟶ X`, whose scheme is `Proj_V(v^*𝒜)`.  The map `ψ` of Stacks 01NR at that
point, in its adjoint form `π_V^*(v^*𝒜)_n ⟶ 𝒪(n)`
(`AlgebraicGeometry.Space.RelativeProjSituation.psiChartSchemeHomOfAdjoint`), carries the
pulled-back multiplication of `v^*𝒜` to the multiplication of the twists
(`RelativeProjSituation.pullbackTensorIso_inv_comp_psiChartSchemeHomOfAdjoint`).
This file proves the unit companion of that statement, reads both statements as identities of
morphisms of quasi-coherent modules on the scheme of `U ×_X P` for the atlas `u : U ⟶ X` of a
presentation, with `u^*𝒜` spelled as the Zariski reading of the restriction of `𝒜` to the small
étale site of `U` (`AlgebraicGeometry.Space.RelativeProjSituation.PsiChartSchemeMulCompat`,
`AlgebraicGeometry.Space.RelativeProjSituation.PsiChartSchemeUnitCompat`), and proves the statement
of Stacks 084D that `ψ : π^*𝒜 ⟶ ⨁_{n ≥ 0} 𝒪_P(n)` is a homomorphism of graded algebras.

## Main results

* `TwistData.oneHom_comp_psiTransposePullbackHom_app_zero`:
  **the transpose of the homogeneous-section map of Stacks 01NR carries the unit to the unit.**
* `AlgebraicGeometry.Space.pullbackUnitIso_inv_comp_map_oneHom_comp_psi`: the transpose of `ψ`,
  read on a scheme through `fh = k ≫ π`, carries the pulled-back unit of `𝒜` (through Stacks 03LU)
  to the unit of the twists.
* `RelativeProjSituation.pullbackUnitIso_inv_comp_psiChartSchemeHomOfAdjoint`:
  the same for `ψ` on the scheme of `V ×_X P`.
* `AlgebraicGeometry.Space.RelativeProjSituation.psiChartSchemeMulCompat`,
  `AlgebraicGeometry.Space.RelativeProjSituation.psiChartSchemeUnitCompat`: **`ψ` on the scheme of
  `U ×_X P` is multiplicative and unital as a family of morphisms of quasi-coherent modules.**
* `AlgebraicGeometry.Space.RelativeProjSituation.psiSourceMul_comp_psiTwistHom`,
  `AlgebraicGeometry.Space.RelativeProjSituation.psiSourceUnit_comp_psiTwistHom`: **`ψ` of
  Stacks 084D carries the multiplication and the unit of `π^*𝒜` to those of `⨁_{n ≥ 0} 𝒪_P(n)`.**

## References

* [Stacks Project, Tag 084D](https://stacks.math.columbia.edu/tag/084D)
* [Stacks Project, Tag 01NR](https://stacks.math.columbia.edu/tag/01NR)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
-/

@[expose] public noncomputable section

universe u m

open CategoryTheory AlgebraicGeometry Opposite
open Stacks.AlgebraicGeometry.RelativeProj (relativeProj)
open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf (situationAlgebra)
open Stacks.AlgebraicGeometry (Tag07ZGTwist.twistAlgebra GluedTwistAlgebra.twistDataOfGradedAlgebra)

namespace Stacks.AlgebraicGeometry.RelativeProjTwists.TwistData

variable {S : Scheme.{u}} {A : RelativeProjBridge.SheafGradedAlgebra.{u} S} (D : TwistData A)

/-- **The transpose of the homogeneous-section map of Stacks 01NR carries the unit to the unit**:
the unit `𝒪 ⟶ (π^*𝒜)_0` of the inverse image of `𝒜` followed by the transpose
`π^*𝒜_0 ⟶ 𝒪(0)` of `ψ_0` is the unit of `⨁_n 𝒪(n)`. -/
theorem oneHom_comp_psiTransposePullbackHom_app_zero :
    SheafOfModules.GradedAlgebra.oneHom (Stacks.RingedSpace.pullbackGradedAlgebra
        (relativeProj A).toBase.toLRSHom.toShHom (situationAlgebra A)) ≫
      D.psiTransposePullbackHom.app 0 =
    SheafOfModules.GradedAlgebra.oneHom D.algebra := by
  refine (D.algebra.piece 0).unitHomEquiv.injective ?_
  refine (SheafOfModules.unitHomEquiv_comp_apply _ _).trans ?_
  refine (congrArg (SheafOfModules.sectionsMap (D.psiTransposePullbackHom.app 0))
    (SheafOfModules.GradedAlgebra.unitHomEquiv_oneHom (Stacks.RingedSpace.pullbackGradedAlgebra
      (relativeProj A).toBase.toLRSHom.toShHom (situationAlgebra A)))).trans ?_
  refine Eq.trans ?_ (SheafOfModules.GradedAlgebra.unitHomEquiv_oneHom D.algebra).symm
  refine Stacks.AlgebraicGeometry.AffineTwisting.sections_eq_of_eval_top _ _ _ ?_
  exact (congrArg ((D.psiTranspose ((0 : ℕ) : ℤ)).val.app (op ⊤))
    (Stacks.RingedSpace.pullbackGradedAlgebra_one_eval
      (relativeProj A).toBase.toLRSHom.toShHom (situationAlgebra A) ⊤)).trans
    (D.psiTranspose_zero_unit ⊤)

end Stacks.AlgebraicGeometry.RelativeProjTwists.TwistData

namespace AlgebraicGeometry.Space

section Glue

variable {C : Type*} {_ : Category C} {P : ObjectProperty C}

/-- **An equation of composites in a full subcategory from an equation of the underlying
morphisms written in other spellings**: each underlying morphism of the conclusion is identified
with the corresponding morphism of `h` by its own equation. -/
theorem comp_comp_eq_comp_of_hom_eq {A B D E F : P.FullSubcategory} (x : A ⟶ B) (y : B ⟶ D)
    (z : D ⟶ E) (w : A ⟶ F) (t : F ⟶ E) {x' : A.obj ⟶ B.obj} {y' : B.obj ⟶ D.obj}
    {z' : D.obj ⟶ E.obj} {w' : A.obj ⟶ F.obj} {t' : F.obj ⟶ E.obj}
    (h : x' ≫ y' ≫ z' = w' ≫ t') (hx : x.hom = x') (hy : y.hom = y') (hz : z.hom = z')
    (hw : w.hom = w') (ht : t.hom = t') :
    (x ≫ y) ≫ z = w ≫ t := by
  subst hx hy hz hw ht
  rw [Category.assoc]
  exact ObjectProperty.hom_ext _ h

/-- The unit companion of `AlgebraicGeometry.Space.comp_comp_eq_comp_of_hom_eq`. -/
theorem comp_comp_eq_of_hom_eq {A B D E : P.FullSubcategory} (x : A ⟶ B) (y : B ⟶ D)
    (z : D ⟶ E) (t : A ⟶ E) {x' : A.obj ⟶ B.obj} {y' : B.obj ⟶ D.obj} {z' : D.obj ⟶ E.obj}
    {t' : A.obj ⟶ E.obj} (h : x' ≫ y' ≫ z' = t') (hx : x.hom = x') (hy : y.hom = y')
    (hz : z.hom = z') (ht : t.hom = t') :
    (x ≫ y) ≫ z = t := by
  subst hx hy hz ht
  rw [Category.assoc]
  exact ObjectProperty.hom_ext _ h

/-- The tensor product of two morphisms of a full subcategory, through a bifunctor on the ambient
category, is that of the underlying morphisms. -/
theorem map_app_comp_obj_map_homMk_hom_eq {E : Type*} {_ : Category E} (F : C ⥤ C ⥤ E)
    {M M' N N' : P.FullSubcategory} (a : M.obj ⟶ M'.obj) (b : N.obj ⟶ N'.obj)
    {w' : (F.obj M.obj).obj N.obj ⟶ (F.obj M'.obj).obj N'.obj}
    (hw : (F.map a).app N.obj ≫ (F.obj M'.obj).map b = w') :
    (F.map (ObjectProperty.homMk (P := P) a).hom).app N.obj ≫
        (F.obj M'.obj).map (ObjectProperty.homMk (P := P) b).hom = w' :=
  hw

/-- A bifunctor on a pair of morphisms, rewritten along equations of the morphisms. -/
theorem map_app_comp_obj_map_congr {D E : Type*} {_ : Category D} {_ : Category E}
    (F : C ⥤ D ⥤ E) {X X' : C} {Y Y' : D} {a a' : X ⟶ X'} {b b' : Y ⟶ Y'} (ha : a = a')
    (hb : b = b') :
    (F.map a).app Y ≫ (F.obj X').map b = (F.map a').app Y ≫ (F.obj X').map b' := by
  rw [ha, hb]

end Glue

/-- **A composite of comparisons of inverse images and of the inverse image of a unital
homomorphism of sheaves of graded algebras carries the pulled-back unit to the unit**: for
`fh = k ≫ h` and a homomorphism `φ : h^*G ⟶ D` of sheaves of graded algebras carrying the unit
to the unit, the family `fh^*G_n ≅ k^*h^*G_n ⟶ k^*D_n` carries the unit of `G`, pulled back along
`fh` and read through Stacks 03LU, to the unit of `k^*D`.  The unit companion of
`AlgebraicGeometry.Space.pullbackTensorIso_inv_comp_map_mulSheaf_comp_of_hom`. -/
theorem pullbackUnitIso_inv_comp_map_oneHom_comp_of_hom {W P' S' : Scheme.{u}}
    (fh : W ⟶ S') (k : W ⟶ P') (h : P' ⟶ S') (e : fh = k ≫ h)
    (G : SheafOfModules.GradedAlgebra.{u, u}
      (Stacks.RingedSpace.structureRingSheaf S'.toRingedSpace))
    (D' : Stacks.AlgebraicGeometry.RelativeProjTwists.SchemeGradedAlgebra P')
    (φ : Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist.pbAlgS h G ⟶ D')
    (hφ : SheafOfModules.GradedAlgebra.oneHom
        (Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist.pbAlgS h G) ≫ φ.app 0 =
      SheafOfModules.GradedAlgebra.oneHom D')
    (ψ' : ∀ n, (Scheme.Modules.pullback fh).obj (G.piece n) ⟶
      (Scheme.Modules.pullback k).obj (D'.piece n))
    (hψ' : ψ' = fun n => (Scheme.Modules.pullbackCongr e).hom.app (G.piece n) ≫
      (Scheme.Modules.pullbackComp k h).inv.app (G.piece n) ≫
        (Scheme.Modules.pullback k).map (φ.app n)) :
    (Scheme.Modules.pullbackUnitIso fh).inv ≫
        (Scheme.Modules.pullback fh).map (SheafOfModules.GradedAlgebra.oneHom G) ≫ ψ' 0 =
      SheafOfModules.GradedAlgebra.oneHom
        (Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist.pbAlgS k D') := by
  subst hψ'
  subst e
  have h0 := oneHom_pullbackGradedAlgebra_eq_pullbackUnitIso (k ≫ h) G
  have h1 := oneHom_comp_iso_hom_app_zero
    (Stacks.AlgebraicGeometry.GradedAlgebraPullbackComp.pullbackGradedAlgebraCongrIso G
      (rfl : k ≫ h = k ≫ h))
  have h2 := oneHom_comp_iso_hom_app_zero
    (Stacks.AlgebraicGeometry.GradedAlgebraPullbackComp.pullbackGradedAlgebraCompIso G k h).symm
  have h3 : SheafOfModules.GradedAlgebra.oneHom
        (Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist.pbAlgS k
          (Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist.pbAlgS h G)) ≫
        (Scheme.Modules.pullback k).map (φ.app 0) =
      SheafOfModules.GradedAlgebra.oneHom
        (Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist.pbAlgS k D') := by
    refine (congrArg (· ≫ (Scheme.Modules.pullback k).map (φ.app 0))
      (oneHom_pullbackGradedAlgebra_eq_pullbackUnitIso k
        (Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist.pbAlgS h G))).trans ?_
    refine (Category.assoc _ _ _).trans ?_
    refine (congrArg ((Scheme.Modules.pullbackUnitIso k).inv ≫ ·)
      (((Scheme.Modules.pullback k).map_comp _ _).symm.trans
        (congrArg (Scheme.Modules.pullback k).map hφ))).trans ?_
    exact (oneHom_pullbackGradedAlgebra_eq_pullbackUnitIso k D').symm
  beta_reduce
  refine ((Category.assoc _ _ _).symm.trans (congrArg (fun z => z ≫ _) h0.symm)).trans ?_
  refine ((reassoc_of% h1) _).trans ?_
  refine ((reassoc_of% h2) _).trans ?_
  exact h3

/-- **The transpose of Tag 01NR's `ψ`, read on a scheme `W` through `fh = k ≫ π`, carries the
pulled-back unit to the unit of the twists**: for a quasi-coherent graded algebra `𝒜` on `S'`,
twists `D` of `Proj_{S'}(𝒜)`, `k : W ⟶ Proj_{S'}(𝒜)` and `fh = k ≫ π`, the morphism
`fh^*𝒜_0 ≅ k^*π^*𝒜_0 ⟶ k^*𝒪(0)` of transposes of `ψ` carries the unit of `𝒜`, pulled back along
`fh` and read through Stacks 03LU, to the unit of `k^*⨁ 𝒪(n)`.  The unit companion of
`AlgebraicGeometry.Space.pullbackTensorIso_inv_comp_map_mulSheaf_comp_psi`. -/
theorem pullbackUnitIso_inv_comp_map_oneHom_comp_psi {S' W : Scheme.{u}}
    {A : Stacks.AlgebraicGeometry.RelativeProjBridge.SheafGradedAlgebra.{u} S'}
    (D : Stacks.AlgebraicGeometry.RelativeProjTwists.TwistData A) (fh : W ⟶ S')
    (k : W ⟶ (relativeProj A).scheme) (e : fh = k ≫ (relativeProj A).toBase)
    (χ : (Scheme.Modules.pullback fh).obj (A.piece ((0 : ℕ) : ℤ)) ⟶
      (Scheme.Modules.pullback k).obj (D.algebra.piece ((0 : ℕ) : ℤ)))
    (hχ : χ = (Scheme.Modules.pullbackCongr e).hom.app _ ≫
      (Scheme.Modules.pullbackComp k (relativeProj A).toBase).inv.app _ ≫
      (Scheme.Modules.pullback k).map
        (((Scheme.Modules.pullbackPushforwardAdjunction (relativeProj A).toBase).homEquiv _ _).symm
          (D.ψ 0))) :
    (Scheme.Modules.pullbackUnitIso fh).inv ≫
        (Scheme.Modules.pullback fh).map
          (SheafOfModules.GradedAlgebra.oneHom (situationAlgebra A)) ≫ χ =
      SheafOfModules.GradedAlgebra.oneHom
        (Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist.pbAlgS k D.algebra) := by
  subst hχ
  exact pullbackUnitIso_inv_comp_map_oneHom_comp_of_hom fh k (relativeProj A).toBase e
    (situationAlgebra A) D.algebra D.psiTransposePullbackHom
    D.oneHom_comp_psiTransposePullbackHom_app_zero _ rfl

/-- **Tag 01NR's `ψ` in adjoint form along a factorization carries the pulled-back unit to the
unit of the twists**: for `f = ι ≫ π`, `AlgebraicGeometry.Space.pullbackAdjointPsi A ι f hf 0`
carries the unit of `A`, pulled back along `f` and read through Stacks 03LU, to the unit of
`ι^*⨁ 𝒪(n)`. -/
theorem pullbackUnitIso_inv_comp_pullbackAdjointPsi {X Y : Scheme.{u}}
    (A : Stacks.AlgebraicGeometry.RelativeProjBridge.SheafGradedAlgebra.{u} Y)
    (ι : X ⟶ (relativeProj A).scheme) (f : X ⟶ Y) (hf : f = ι ≫ (relativeProj A).toBase) :
    (Scheme.Modules.pullbackUnitIso f).inv ≫
        (Scheme.Modules.pullback f).map
          (SheafOfModules.GradedAlgebra.oneHom (situationAlgebra A)) ≫
        pullbackAdjointPsi A ι f hf 0 =
      SheafOfModules.GradedAlgebra.oneHom
        (Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist.pbAlgS ι
          (Tag07ZGTwist.twistAlgebra A)) :=
  pullbackUnitIso_inv_comp_map_oneHom_comp_psi (GluedTwistAlgebra.twistDataOfGradedAlgebra A)
    f ι hf (pullbackAdjointPsi A ι f hf 0) rfl

/-- `AlgebraicGeometry.Space.pullbackTensorIso_inv_comp_pullbackAdjointPsi` with the tensor product
of `ψ_i` and `ψ_j` spelled through the tensor product of sheaves of modules on the Zariski ringed
site of `X`, and every composite taken in the category of sheaves of modules over
`X.ringCatSheaf` (the spelling of the quasi-coherent modules on schemes), at free variables. -/
theorem pullbackTensorIso_inv_comp_pullbackAdjointPsi_zariskiRingedSite {X Y : Scheme.{u}}
    (A : Stacks.AlgebraicGeometry.RelativeProjBridge.SheafGradedAlgebra.{u} Y)
    (ι : X ⟶ (relativeProj A).scheme) (f : X ⟶ Y) (hf : f = ι ≫ (relativeProj A).toBase)
    (i j : ℕ) :
    @CategoryStruct.comp (SheafOfModules X.ringCatSheaf) _ _ _ _
        (Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso f (A.piece (i : ℤ))
          (A.piece (j : ℤ))).inv
        (@CategoryStruct.comp (SheafOfModules X.ringCatSheaf) _ _ _ _
          ((Scheme.Modules.pullback f).map
            (SheafOfModules.GradedAlgebra.mulSheaf (situationAlgebra A) (i : ℤ) (j : ℤ)))
          (pullbackAdjointPsi A ι f hf (i + j))) =
      @CategoryStruct.comp (SheafOfModules X.ringCatSheaf) _ _ _ _
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
            X.zariskiRingedSite.toRingedTopos.O).map (pullbackAdjointPsi A ι f hf i)).app
              ((Scheme.Modules.pullback f).obj (A.piece (j : ℤ))) ≫
          ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
            X.zariskiRingedSite.toRingedTopos.O).obj
              ((Scheme.Modules.pullback ι).obj ((Tag07ZGTwist.twistAlgebra A).piece (i : ℤ)))).map
            (pullbackAdjointPsi A ι f hf j))
        (SheafOfModules.GradedAlgebra.mulSheaf
          (Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist.pbAlgS ι
              (Tag07ZGTwist.twistAlgebra A))
          (i : ℤ) (j : ℤ)) :=
  pullbackTensorIso_inv_comp_pullbackAdjointPsi A ι f hf i j

namespace RelativeProjSituation

variable (s : RelativeProjSituation.{u, m})

/-- **`ψ` on the scheme of `V ×_X P` carries the pulled-back unit of `v^*𝒜` to the unit of the
twists**: the identification of Stacks 03LU, followed by the pullback along `V ×_X P ⟶ V` of the
unit of `v^*𝒜` and by `ψ_0`
(`AlgebraicGeometry.Space.RelativeProjSituation.psiChartSchemeHomOfAdjoint`), is the unit
`𝒪 ⟶ 𝒪(0)` of the twists on `V ×_X P`. -/
theorem pullbackUnitIso_inv_comp_psiChartSchemeHomOfAdjoint
    (V : BigFppfOver s.site s.base s.containsBase) (v : yoneda.obj V ⟶ s.space.1) :
    type_of% (pullbackUnitIso_inv_comp_pullbackAdjointPsi (s.shrink.pointAlgebra V v)
      (s.toRelativeProj V v) (s.fibreToBase V v) (s.fibreToBase_eq V v)) :=
  pullbackUnitIso_inv_comp_pullbackAdjointPsi (s.shrink.pointAlgebra V v) (s.toRelativeProj V v)
    (s.fibreToBase V v) (s.fibreToBase_eq V v)

/-- `RelativeProjSituation.pullbackTensorIso_inv_comp_psiChartSchemeHomOfAdjoint`
with the tensor product of `ψ_i` and `ψ_j` spelled through the tensor product of sheaves of
modules on the Zariski ringed site of the scheme of `V ×_X P`. -/
theorem pullbackTensorIso_inv_comp_psiChartSchemeHomOfAdjoint_zariskiRingedSite
    (V : BigFppfOver s.site s.base s.containsBase) (v : yoneda.obj V ⟶ s.space.1) (i j : ℕ) :
    type_of% (pullbackTensorIso_inv_comp_pullbackAdjointPsi_zariskiRingedSite
      (s.shrink.pointAlgebra V v) (s.toRelativeProj V v) (s.fibreToBase V v)
      (s.fibreToBase_eq V v) i j) :=
  pullbackTensorIso_inv_comp_pullbackAdjointPsi_zariskiRingedSite (s.shrink.pointAlgebra V v)
    (s.toRelativeProj V v) (s.fibreToBase V v) (s.fibreToBase_eq V v) i j

/-- `AlgebraicGeometry.Space.RelativeProjSituation.psiChartSchemeHomOfAdjoint` is
`AlgebraicGeometry.Space.pullbackAdjointPsi` at the point, by definition. -/
theorem psiChartSchemeHomOfAdjoint_eq (V : BigFppfOver s.site s.base s.containsBase)
    (v : yoneda.obj V ⟶ s.space.1) (n : ℕ) :
    s.psiChartSchemeHomOfAdjoint V v n =
      pullbackAdjointPsi (s.shrink.pointAlgebra V v) (s.toRelativeProj V v) (s.fibreToBase V v)
        (s.fibreToBase_eq V v) n :=
  rfl

section ChartScheme

attribute [local irreducible] CategoryTheory.yoneda

/- The sheafification instances of the small étale site at the universe of the modules. -/
attribute [local instance 5000] SmallEtale.instHasSheafify SmallEtale.instWEqualsLocallyBijective

section Aux

/- The statements below spell the proof that the presentation's space is algebraic as a variable
`hX` in the projections of `Px`, so that they can be matched with statements whose elaboration
abstracted that proof into an auxiliary lemma. -/
variable {hX : IsAlgebraicSpace s.site s.base s.containsBase s.space.obj}
  (Px : Presentation s.site s.base s.containsBase s.space.obj s.space.property)

/-! The factors of the quasi-coherent statements, read in the scheme-level spelling. -/

/- The tensor product of sheaves of modules is compared through its arguments only. -/
attribute [local irreducible] Stacks.SheafOfModules.Tensor.sheafTensor

private theorem quasicoherentTensorHom_psiChartSchemeHomOfAdjoint_hom_eq (i j : ℕ) :
    (quasicoherentTensorHom s.site s.base s.containsBase
        (s.relativeProjPoints.fibre
            (@Presentation.U s.site s.base s.containsBase s.space.obj hX Px)
            (@Presentation.toSpace s.site s.base s.containsBase s.space.obj hX Px))
        (ObjectProperty.homMk (s.psiChartSchemeHomOfAdjoint
            (@Presentation.U s.site s.base s.containsBase s.space.obj hX Px)
            (@Presentation.toSpace s.site s.base s.containsBase s.space.obj hX Px) i) :
          quasicoherentPullbackObj s.site s.base s.containsBase (s.relativeProjPoints.fibreHom
              (@Presentation.U s.site s.base s.containsBase s.space.obj hX Px)
                  (@Presentation.toSpace s.site s.base s.containsBase s.space.obj hX Px))
              (presentationPointPieceQcoh Px s.shrink.algebra s.shrink.isQuasicoherent (i : ℤ)) ⟶
            s.twistPieceQcoh (@Presentation.U s.site s.base s.containsBase s.space.obj hX Px)
                (@Presentation.toSpace s.site s.base s.containsBase s.space.obj hX Px) (i : ℤ))
        (ObjectProperty.homMk (s.psiChartSchemeHomOfAdjoint
            (@Presentation.U s.site s.base s.containsBase s.space.obj hX Px)
            (@Presentation.toSpace s.site s.base s.containsBase s.space.obj hX Px) j) :
          quasicoherentPullbackObj s.site s.base s.containsBase (s.relativeProjPoints.fibreHom
              (@Presentation.U s.site s.base s.containsBase s.space.obj hX Px)
                  (@Presentation.toSpace s.site s.base s.containsBase s.space.obj hX Px))
              (presentationPointPieceQcoh Px s.shrink.algebra s.shrink.isQuasicoherent (j : ℤ)) ⟶
            s.twistPieceQcoh (@Presentation.U s.site s.base s.containsBase s.space.obj hX Px)
                (@Presentation.toSpace s.site s.base s.containsBase s.space.obj hX Px)
                (j : ℤ))).hom =
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ((BigFppfOver.toScheme s.site s.base s.containsBase).obj
          (s.relativeProjPoints.fibre
              (@Presentation.U s.site s.base s.containsBase s.space.obj hX Px)
              (@Presentation.toSpace s.site s.base s.containsBase s.space.obj hX
              Px))).zariskiRingedSite.toRingedTopos.O).map
          (pullbackAdjointPsi (s.shrink.pointAlgebra
              (@Presentation.U s.site s.base s.containsBase s.space.obj hX Px)
              (@Presentation.toSpace s.site s.base s.containsBase s.space.obj hX Px))
          (s.toRelativeProj (@Presentation.U s.site s.base s.containsBase s.space.obj hX Px)
              (@Presentation.toSpace s.site s.base s.containsBase s.space.obj hX Px))
              (s.fibreToBase (@Presentation.U s.site s.base s.containsBase s.space.obj hX Px)
              (@Presentation.toSpace s.site s.base s.containsBase s.space.obj hX Px))
          (s.fibreToBase_eq (@Presentation.U s.site s.base s.containsBase s.space.obj hX Px)
              (@Presentation.toSpace s.site s.base s.containsBase s.space.obj hX Px)) i)).app
          ((Scheme.Modules.pullback (s.fibreToBase
              (@Presentation.U s.site s.base s.containsBase s.space.obj hX Px)
              (@Presentation.toSpace s.site s.base s.containsBase s.space.obj hX Px))).obj
              ((s.shrink.pointAlgebra
              (@Presentation.U s.site s.base s.containsBase s.space.obj hX Px)
              (@Presentation.toSpace s.site s.base s.containsBase s.space.obj hX Px)).piece
              (j : ℤ))) ≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ((BigFppfOver.toScheme s.site s.base s.containsBase).obj
          (s.relativeProjPoints.fibre
              (@Presentation.U s.site s.base s.containsBase s.space.obj hX Px)
              (@Presentation.toSpace s.site s.base s.containsBase s.space.obj hX
              Px))).zariskiRingedSite.toRingedTopos.O).obj
          ((Scheme.Modules.pullback (s.toRelativeProj
              (@Presentation.U s.site s.base s.containsBase s.space.obj hX Px)
              (@Presentation.toSpace s.site s.base s.containsBase s.space.obj hX Px))).obj
            ((Tag07ZGTwist.twistAlgebra (s.shrink.pointAlgebra
                (@Presentation.U s.site s.base s.containsBase s.space.obj hX Px)
                (@Presentation.toSpace s.site s.base s.containsBase s.space.obj hX Px))).piece
                (i : ℤ)))).map
          (pullbackAdjointPsi (s.shrink.pointAlgebra
              (@Presentation.U s.site s.base s.containsBase s.space.obj hX Px)
              (@Presentation.toSpace s.site s.base s.containsBase s.space.obj hX Px))
          (s.toRelativeProj (@Presentation.U s.site s.base s.containsBase s.space.obj hX Px)
              (@Presentation.toSpace s.site s.base s.containsBase s.space.obj hX Px))
              (s.fibreToBase (@Presentation.U s.site s.base s.containsBase s.space.obj hX Px)
              (@Presentation.toSpace s.site s.base s.containsBase s.space.obj hX Px))
          (s.fibreToBase_eq (@Presentation.U s.site s.base s.containsBase s.space.obj hX Px)
              (@Presentation.toSpace s.site s.base s.containsBase s.space.obj hX Px)) j) := by
  refine (ObjectProperty.homMk_hom _).trans (map_app_comp_obj_map_homMk_hom_eq _ _ _ ?_)
  exact map_app_comp_obj_map_congr _ (s.psiChartSchemeHomOfAdjoint_eq
    (@Presentation.U s.site s.base s.containsBase s.space.obj hX Px)
    (@Presentation.toSpace s.site s.base s.containsBase s.space.obj hX Px) i)
    (s.psiChartSchemeHomOfAdjoint_eq
        (@Presentation.U s.site s.base s.containsBase s.space.obj hX Px)
        (@Presentation.toSpace s.site s.base s.containsBase s.space.obj hX Px) j)

private theorem psiChartSchemeMulCompat_aux (i j : ℕ) :
    ((quasicoherentPullbackTensorIso s.site s.base s.containsBase
        (s.relativeProjPoints.fibreHom
            (@Presentation.U s.site s.base s.containsBase s.space.obj hX Px)
            (@Presentation.toSpace s.site s.base s.containsBase s.space.obj hX Px))
        (presentationPointPieceQcoh Px s.shrink.algebra s.shrink.isQuasicoherent (i : ℤ))
        (presentationPointPieceQcoh Px s.shrink.algebra s.shrink.isQuasicoherent (j : ℤ))).inv ≫
      quasicoherentPullbackMap s.site s.base s.containsBase
        (s.relativeProjPoints.fibreHom
            (@Presentation.U s.site s.base s.containsBase s.space.obj hX Px)
            (@Presentation.toSpace s.site s.base s.containsBase s.space.obj hX Px))
        (ObjectProperty.homMk (SheafOfModules.GradedAlgebra.mulSheaf
            (zariskiReading (@Presentation.U s.site s.base s.containsBase s.space.obj hX Px)
              (etalePointAlgebra s.shrink.algebra
                  (@Presentation.U s.site s.base s.containsBase s.space.obj hX Px)
                  (@Presentation.toSpace s.site s.base s.containsBase s.space.obj hX Px)))
            (i : ℤ) (j : ℤ)) :
          quasicoherentTensorObj s.site s.base s.containsBase
              (@Presentation.U s.site s.base s.containsBase s.space.obj hX Px)
              (presentationPointPieceQcoh Px s.shrink.algebra s.shrink.isQuasicoherent (i : ℤ))
              (presentationPointPieceQcoh Px s.shrink.algebra s.shrink.isQuasicoherent (j : ℤ)) ⟶
            presentationPointPieceQcoh Px s.shrink.algebra s.shrink.isQuasicoherent
              ((i : ℤ) + (j : ℤ)))) ≫
      (ObjectProperty.homMk (s.psiChartSchemeHomOfAdjoint
          (@Presentation.U s.site s.base s.containsBase s.space.obj hX Px)
          (@Presentation.toSpace s.site s.base s.containsBase s.space.obj hX Px)
          (i + j)) :
        quasicoherentPullbackObj s.site s.base s.containsBase
            (s.relativeProjPoints.fibreHom
                (@Presentation.U s.site s.base s.containsBase s.space.obj hX Px)
                (@Presentation.toSpace s.site s.base s.containsBase s.space.obj hX Px))
            (presentationPointPieceQcoh Px s.shrink.algebra s.shrink.isQuasicoherent
              ((i + j : ℕ) : ℤ)) ⟶
          s.twistPieceQcoh (@Presentation.U s.site s.base s.containsBase s.space.obj hX Px)
              (@Presentation.toSpace s.site s.base s.containsBase s.space.obj hX Px)
              ((i + j : ℕ) : ℤ)) =
      quasicoherentTensorHom s.site s.base s.containsBase
          (s.relativeProjPoints.fibre
              (@Presentation.U s.site s.base s.containsBase s.space.obj hX Px)
              (@Presentation.toSpace s.site s.base s.containsBase s.space.obj hX Px))
          (ObjectProperty.homMk (s.psiChartSchemeHomOfAdjoint
              (@Presentation.U s.site s.base s.containsBase s.space.obj hX Px)
              (@Presentation.toSpace s.site s.base s.containsBase s.space.obj hX Px)
              i) :
            quasicoherentPullbackObj s.site s.base s.containsBase
                (s.relativeProjPoints.fibreHom
                    (@Presentation.U s.site s.base s.containsBase s.space.obj hX Px)
                    (@Presentation.toSpace s.site s.base s.containsBase s.space.obj hX Px))
                (presentationPointPieceQcoh Px s.shrink.algebra s.shrink.isQuasicoherent (i : ℤ)) ⟶
              s.twistPieceQcoh (@Presentation.U s.site s.base s.containsBase s.space.obj hX Px)
                  (@Presentation.toSpace s.site s.base s.containsBase s.space.obj hX Px) (i : ℤ))
          (ObjectProperty.homMk (s.psiChartSchemeHomOfAdjoint
              (@Presentation.U s.site s.base s.containsBase s.space.obj hX Px)
              (@Presentation.toSpace s.site s.base s.containsBase s.space.obj hX Px)
              j) :
            quasicoherentPullbackObj s.site s.base s.containsBase
                (s.relativeProjPoints.fibreHom
                    (@Presentation.U s.site s.base s.containsBase s.space.obj hX Px)
                    (@Presentation.toSpace s.site s.base s.containsBase s.space.obj hX Px))
                (presentationPointPieceQcoh Px s.shrink.algebra s.shrink.isQuasicoherent (j : ℤ)) ⟶
              s.twistPieceQcoh (@Presentation.U s.site s.base s.containsBase s.space.obj hX Px)
                  (@Presentation.toSpace s.site s.base s.containsBase s.space.obj hX Px) (j : ℤ)) ≫
        s.twistPieceMul (@Presentation.U s.site s.base s.containsBase s.space.obj hX Px)
            (@Presentation.toSpace s.site s.base s.containsBase s.space.obj hX Px) (i : ℤ)
            (j : ℤ) := by
  refine comp_comp_eq_comp_of_hom_eq _ _ _ _ _
    (s.pullbackTensorIso_inv_comp_psiChartSchemeHomOfAdjoint_zariskiRingedSite
        (@Presentation.U s.site s.base s.containsBase s.space.obj hX Px)
      (@Presentation.toSpace s.site s.base s.containsBase s.space.obj hX Px)
      i j)
    ?_ ?_ ?_ ?_ ?_
  · rfl
  · rfl
  · exact ObjectProperty.homMk_hom _
  · exact s.quasicoherentTensorHom_psiChartSchemeHomOfAdjoint_hom_eq Px i j
  · rfl

private theorem psiChartSchemeUnitCompat_aux :
    ((quasicoherentPullbackUnitIso s.site s.base s.containsBase
        (s.relativeProjPoints.fibreHom
            (@Presentation.U s.site s.base s.containsBase s.space.obj hX Px)
            (@Presentation.toSpace s.site s.base s.containsBase s.space.obj hX Px))).inv ≫
      quasicoherentPullbackMap s.site s.base s.containsBase
        (s.relativeProjPoints.fibreHom
            (@Presentation.U s.site s.base s.containsBase s.space.obj hX Px)
            (@Presentation.toSpace s.site s.base s.containsBase s.space.obj hX Px))
        (ObjectProperty.homMk (SheafOfModules.GradedAlgebra.oneHom
          (zariskiReading (@Presentation.U s.site s.base s.containsBase s.space.obj hX Px)
            (etalePointAlgebra s.shrink.algebra
                (@Presentation.U s.site s.base s.containsBase s.space.obj hX Px)
                (@Presentation.toSpace s.site s.base s.containsBase s.space.obj hX Px)))) :
          quasicoherentUnitObj s.site s.base s.containsBase
              (@Presentation.U s.site s.base s.containsBase s.space.obj hX Px) ⟶
            presentationPointPieceQcoh Px s.shrink.algebra s.shrink.isQuasicoherent 0)) ≫
      (ObjectProperty.homMk (s.psiChartSchemeHomOfAdjoint
          (@Presentation.U s.site s.base s.containsBase s.space.obj hX Px)
          (@Presentation.toSpace s.site s.base s.containsBase s.space.obj hX Px)
          0) :
          quasicoherentPullbackObj s.site s.base s.containsBase
              (s.relativeProjPoints.fibreHom
                  (@Presentation.U s.site s.base s.containsBase s.space.obj hX Px)
                  (@Presentation.toSpace s.site s.base s.containsBase s.space.obj hX Px))
              (presentationPointPieceQcoh Px s.shrink.algebra s.shrink.isQuasicoherent
                ((0 : ℕ) : ℤ)) ⟶
            s.twistPieceQcoh (@Presentation.U s.site s.base s.containsBase s.space.obj hX Px)
                (@Presentation.toSpace s.site s.base s.containsBase s.space.obj hX Px)
                ((0 : ℕ) : ℤ)) =
      s.twistPieceUnit (@Presentation.U s.site s.base s.containsBase s.space.obj hX Px)
          (@Presentation.toSpace s.site s.base s.containsBase s.space.obj hX Px) := by
  refine comp_comp_eq_of_hom_eq _ _ _ _
    (s.pullbackUnitIso_inv_comp_psiChartSchemeHomOfAdjoint
        (@Presentation.U s.site s.base s.containsBase s.space.obj hX Px)
      (@Presentation.toSpace s.site s.base s.containsBase s.space.obj hX Px))
    ?_ ?_ ?_ ?_
  · rfl
  · rfl
  · exact ObjectProperty.homMk_hom _
  · rfl

end Aux

variable (Px : Presentation s.site s.base s.containsBase s.space.obj s.space.property)

/-- **`ψ` of Tag 01NR on the scheme of `U ×_X P` is multiplicative, as morphisms of quasi-coherent
modules** (for the atlas `u : U ⟶ X` of a presentation): for the Zariski readings `Z_n` of
`u^*𝒜_n`, the inverse comparison of Stacks 01CD along `π_U : U ×_X P ⟶ U`, followed by the pullback
of the multiplication `Z_i ⊗ Z_j ⟶ Z_{i+j}` of the Zariski reading of `u^*𝒜` and by `ψ_{i+j}`, is
`ψ_i ⊗ ψ_j` followed by the multiplication of the twists. -/
theorem psiChartSchemeMulCompat (i j : ℕ) : s.PsiChartSchemeMulCompat Px i j := by
  unfold PsiChartSchemeMulCompat
  exact s.psiChartSchemeMulCompat_aux Px i j

/-- **`ψ` of Tag 01NR on the scheme of `U ×_X P` is unital, as morphisms of quasi-coherent
modules** (for the atlas `u : U ⟶ X` of a presentation): the identification `𝒪 ≅ π_U^*𝒪_U` of
Stacks 03LU, followed by the pullback along `π_U : U ×_X P ⟶ U` of the unit `𝒪_U ⟶ Z_0` of the
Zariski reading of `u^*𝒜` and by `ψ_0`, is the unit of the twists. -/
theorem psiChartSchemeUnitCompat : s.PsiChartSchemeUnitCompat Px := by
  unfold PsiChartSchemeUnitCompat
  exact s.psiChartSchemeUnitCompat_aux Px

section Psi

open MonoidalCategory

attribute [local instance] modulesMonoidalCategory

/-- **`ψ : π^*𝒜 ⟶ ⨁_{n ≥ 0} 𝒪_P(n)` of Stacks 084D is multiplicative**:
`π^*𝒜_i ⊗ π^*𝒜_j ≅ π^*(𝒜_i ⊗ 𝒜_j) ⟶ π^*𝒜_{i+j}` followed by `ψ_{i+j}` is `ψ_i ⊗ ψ_j` followed
by the multiplication `𝒪_P(i) ⊗ 𝒪_P(j) ⟶ 𝒪_P(i + j)` of the twists. -/
theorem psiSourceMul_comp_psiTwistHom (i j : ℕ) :
    s.psiSourceMul (i : ℤ) (j : ℤ) ≫ s.psiTwistHom Px (i + j) =
      (s.psiTwistHom Px i ⊗ₘ s.psiTwistHom Px j) ≫ s.twistAlgebraMul Px (i : ℤ) (j : ℤ) :=
  s.psiSourceMul_comp_psiTwistHom_of_psiChartSchemeMulCompat Px i j
    (s.psiChartSchemeMulCompat Px i j)

/-- **`ψ : π^*𝒜 ⟶ ⨁_{n ≥ 0} 𝒪_P(n)` of Stacks 084D is unital**: `𝒪_P ≅ π^*𝒪_X ⟶ π^*𝒜_0`
followed by `ψ_0` is the unit `𝒪_P ⟶ 𝒪_P(0)` of the twists. -/
theorem psiSourceUnit_comp_psiTwistHom :
    s.psiSourceUnit ≫ s.psiTwistHom Px 0 = s.twistAlgebraUnit Px :=
  s.psiSourceUnit_comp_psiTwistHom_of_psiChartSchemeUnitCompat Px (s.psiChartSchemeUnitCompat Px)

end Psi

end ChartScheme

end RelativeProjSituation

end AlgebraicGeometry.Space

end
