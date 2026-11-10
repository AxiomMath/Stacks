module

public import StacksFrontier.AlgebraicGeometry.DeRham.SmoothFormsLocalKunneth

/-!
# The dependence of the local Künneth decomposition of the forms on the splitting

Over an open `U` of `X` on which the differentials sequence
`0 ⟶ f^*Ω_{Y/S} ⟶ Ω_{X/S} ⟶ Ω_{X/Y} ⟶ 0` of a smooth morphism splits, the Künneth decomposition
of exterior powers along a splitting decomposes `Ω^n_{X/S}|_U`
(`AlgebraicGeometry.Scheme.Hom.exists_isIso_exteriorPowerProdHom_relativeDifferentials`).
The decomposition depends on the chosen section `Ω_{X/Y}|_U ⟶ Ω_{X/S}|_U`. This file records
the exact extent of that dependence: two splittings of a short complex are carried into one
another by a unipotent automorphism of the middle term which fixes the sub and the quotient, and
the two Künneth comparisons differ by postcomposition with its exterior power and by nothing
else.

## Main results

* `CategoryTheory.ShortComplex.Splitting.transition`: the unipotent automorphism
  `𝟙 - T.g ≫ (sp.s ≫ sp'.r) ≫ T.f` carrying one splitting to another, with
  `CategoryTheory.ShortComplex.Splitting.transition_sub_id`,
  `CategoryTheory.ShortComplex.Splitting.f_comp_transition`,
  `CategoryTheory.ShortComplex.Splitting.transition_comp_g`,
  `CategoryTheory.ShortComplex.Splitting.s_comp_transition` and
  `CategoryTheory.ShortComplex.Splitting.isIso_transition`.
* `SheafOfModules.GradedAlgebra.tensorSheafBifunctor_map_app_comp_mulSheaf`: a unital
  homomorphism of sheaves of graded algebras commutes with the morphism-level multiplications.
* `SheafOfModules.prodWedgeHom_comp_pieceMap` and
  `SheafOfModules.exteriorPowerProdHom_eq_of_comp`: the wedge-product component morphism and the
  Künneth comparison are natural in the ambient module.
* `AlgebraicGeometry.Scheme.Modules.exteriorPowerProdHom_splitting_eq` and
  `AlgebraicGeometry.Scheme.Hom.exteriorPowerProdHom_relativeDifferentials_splitting_eq`: two
  splittings give comparisons differing by `⋀^nθ` for the transition automorphism `θ`.

## References

* [Stacks Project, Tag 0FMK](https://stacks.math.columbia.edu/tag/0FMK)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open RingedSpaceModuleAdjunction

/-! `Stacks.SheafOfModules.Tensor.sheafTensor` is indexed by
`Stacks.SheafOfModules.Tensor.ringSheaf Osharp`, whereas the module sheaves and graded algebras
below are indexed by `CategoryTheory.Sheaf.toRingCat J Osharp`; the two are the same bundled
sheaf of rings, and `ringSheaf` is made instance-reducible so that the two spellings unify. -/
attribute [local instance_reducible] Stacks.SheafOfModules.Tensor.ringSheaf

universe v₁ u₁ w u

namespace CategoryTheory.ShortComplex.Splitting

variable {C : Type*} [Category C] [Preadditive C] {T : ShortComplex C}

/-- **The unipotent automorphism carrying one splitting to another.** For two splittings `sp`,
`sp'` of a short complex `T` this is `𝟙 - T.g ≫ (sp.s ≫ sp'.r) ≫ T.f`, the endomorphism of
`T.X₂` which fixes `T.f` and `T.g` and takes `sp.s` to `sp'.s`. -/
def transition (sp sp' : T.Splitting) : T.X₂ ⟶ T.X₂ :=
  𝟙 T.X₂ - T.g ≫ (sp.s ≫ sp'.r) ≫ T.f

/-- **The transition endomorphism is the identity modulo `T.f`**: it differs from the identity by
a morphism factoring through `T.f`, so it acts trivially on anything `T.f` is divided out of. -/
theorem transition_sub_id (sp sp' : T.Splitting) :
    sp.transition sp' - 𝟙 T.X₂ = (-(T.g ≫ sp.s ≫ sp'.r)) ≫ T.f := by
  rw [transition, sub_sub_cancel_left, Preadditive.neg_comp,
    Category.assoc T.g (sp.s ≫ sp'.r) T.f]

/-- The transition endomorphism fixes the inclusion of the sub. -/
@[reassoc]
theorem f_comp_transition (sp sp' : T.Splitting) : T.f ≫ sp.transition sp' = T.f := by
  rw [transition, Preadditive.comp_sub, Category.comp_id,
    ← Category.assoc T.f T.g ((sp.s ≫ sp'.r) ≫ T.f), T.zero, zero_comp, sub_zero]

/-- The transition endomorphism fixes the projection onto the quotient. -/
@[reassoc]
theorem transition_comp_g (sp sp' : T.Splitting) : sp.transition sp' ≫ T.g = T.g := by
  rw [transition, Preadditive.sub_comp, Category.id_comp, Category.assoc, Category.assoc, T.zero,
    comp_zero, comp_zero, sub_zero]

/-- The transition endomorphism takes one section to the other. -/
@[reassoc]
theorem s_comp_transition (sp sp' : T.Splitting) : sp.s ≫ sp.transition sp' = sp'.s := by
  rw [transition, Preadditive.comp_sub, Category.comp_id,
    ← Category.assoc sp.s T.g ((sp.s ≫ sp'.r) ≫ T.f), sp.s_g, Category.id_comp, ← s_sub_s sp sp',
    sub_sub_cancel]

/-- **The transition endomorphism is an automorphism**, with inverse
`𝟙 + T.g ≫ (sp.s ≫ sp'.r) ≫ T.f`. -/
theorem isIso_transition (sp sp' : T.Splitting) : IsIso (sp.transition sp') := by
  have hNN : (T.g ≫ (sp.s ≫ sp'.r) ≫ T.f) ≫ T.g ≫ (sp.s ≫ sp'.r) ≫ T.f = 0 := by
    rw [Category.assoc, Category.assoc, ← Category.assoc T.f T.g ((sp.s ≫ sp'.r) ≫ T.f), T.zero,
      zero_comp, comp_zero, comp_zero]
  refine ⟨𝟙 T.X₂ + T.g ≫ (sp.s ≫ sp'.r) ≫ T.f, ?_, ?_⟩
  · rw [transition, Preadditive.sub_comp, Category.id_comp, Preadditive.comp_add, Category.comp_id,
      hNN, add_zero, add_sub_cancel_right]
  · rw [transition, Preadditive.add_comp, Category.id_comp, Preadditive.comp_sub, Category.comp_id,
      hNN, sub_zero]
    abel

end CategoryTheory.ShortComplex.Splitting

namespace SheafOfModules.GradedAlgebra

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] {Osharp : Sheaf J CommRingCat.{w}}
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]

/-- **A unital homomorphism of sheaves of graded algebras commutes with the morphism-level
multiplications**: `(g_i ⊗ g_j) ≫ μ_B = μ_A ≫ g_{i+j}` as morphisms out of the tensor product
sheaf. -/
theorem tensorSheafBifunctor_map_app_comp_mulSheaf
    {A B : GradedAlgebra.{w, w} (Sheaf.toRingCat J Osharp)} (g : UnitalHom A B) (i j : ℤ) :
    (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor Osharp)).map
          ((g.app i, g.app j) : (A.piece i, A.piece j) ⟶ (B.piece i, B.piece j)) ≫
        mulSheaf B i j =
      mulSheaf A i j ≫ g.app (i + j) := by
  refine PresheafOfModules.tensorSheaf_hom_ext (Osharp := Osharp) fun U x y => ?_
  refine Eq.trans (congrArg ((mulSheaf B i j).val.app U)
    (Stacks.TensorSheafWorld.tensorSheafBifunctor_map_val_app_tensorSheafUnit Osharp
      (A.piece i) (A.piece j) (g.app i) (g.app j) U x y)) ?_
  exact (mulSheaf_unit B i j U _ _).trans
    ((g.map_mul i j U x y).symm.trans
      (congrArg ((g.app (i + j)).val.app U) (mulSheaf_unit A i j U x y).symm))

/-- **The map induced on exterior powers by a morphism of sheaves of modules intertwines the
multiplications of the two exterior algebras.** -/
theorem IsExteriorAlgebra.tensorSheafBifunctor_map_pieceMap_comp_mulSheaf
    {M N : SheafOfModules.{w} (Sheaf.toRingCat J Osharp)}
    {A B : GradedAlgebra.{w, w} (Sheaf.toRingCat J Osharp)} {ι : M ⟶ A.piece 1}
    {κ : N ⟶ B.piece 1} (hA : IsExteriorAlgebra A ι) (hB : IsExteriorAlgebra B κ) (θ : M ⟶ N)
    (i j : ℤ) :
    (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor Osharp)).map
          ((hA.pieceMap hB θ i, hA.pieceMap hB θ j) :
            (A.piece i, A.piece j) ⟶ (B.piece i, B.piece j)) ≫ mulSheaf B i j =
      mulSheaf A i j ≫ hA.pieceMap hB θ (i + j) :=
  tensorSheafBifunctor_map_app_comp_mulSheaf (hA.map hB θ) i j

end SheafOfModules.GradedAlgebra

namespace SheafOfModules

variable {Z : TopCat.{u}} {Osharp : Sheaf (Opens.grothendieckTopology ↥Z) CommRingCat.{u}}
  {F G H H' : SheafOfModules.{u} (Sheaf.toRingCat (Opens.grothendieckTopology ↥Z) Osharp)}
  (AF : TensorExteriorSymmetricAlgebras (Opens.grothendieckTopology ↥Z) F)
  (AG : TensorExteriorSymmetricAlgebras (Opens.grothendieckTopology ↥Z) G)
  (A : TensorExteriorSymmetricAlgebras (Opens.grothendieckTopology ↥Z) H)
  (A' : TensorExteriorSymmetricAlgebras (Opens.grothendieckTopology ↥Z) H')

/-- **The wedge-product component morphism is natural in the ambient module.** Replacing
`iF : F ⟶ H` and `iG : G ⟶ H` by `iF ≫ θ` and `iG ≫ θ` for `θ : H ⟶ H'` postcomposes the
component morphism with `⋀^{p+q} θ`. -/
theorem prodWedgeHom_comp_pieceMap (iF : F ⟶ H) (iG : G ⟶ H) (θ : H ⟶ H') (p q : ℕ) :
    prodWedgeHom AF AG A' (iF ≫ θ) (iG ≫ θ) p q =
      prodWedgeHom AF AG A iF iG p q ≫
        A.exterior_isExteriorAlgebra.pieceMap A'.exterior_isExteriorAlgebra θ
          ((p : ℤ) + (q : ℤ)) := by
  rw [prodWedgeHom, prodWedgeHom,
    AF.exterior_isExteriorAlgebra.pieceMap_comp A.exterior_isExteriorAlgebra
      A'.exterior_isExteriorAlgebra iF θ (p : ℤ),
    AG.exterior_isExteriorAlgebra.pieceMap_comp A.exterior_isExteriorAlgebra
      A'.exterior_isExteriorAlgebra iG θ (q : ℤ)]
  conv_rhs =>
    rw [Category.assoc,
      ← GradedAlgebra.IsExteriorAlgebra.tensorSheafBifunctor_map_pieceMap_comp_mulSheaf
        A.exterior_isExteriorAlgebra A'.exterior_isExteriorAlgebra θ (p : ℤ) (q : ℤ),
      ← Category.assoc]
  exact congrArg (· ≫ GradedAlgebra.mulSheaf A'.exterior (p : ℤ) (q : ℤ))
    ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor Osharp)).map_comp
      ((AF.exterior_isExteriorAlgebra.pieceMap A.exterior_isExteriorAlgebra iF (p : ℤ),
          AG.exterior_isExteriorAlgebra.pieceMap A.exterior_isExteriorAlgebra iG (q : ℤ)) :
        (AF.exteriorPower p, AG.exteriorPower q) ⟶ (A.exteriorPower p, A.exteriorPower q))
      ((A.exterior_isExteriorAlgebra.pieceMap A'.exterior_isExteriorAlgebra θ (p : ℤ),
          A.exterior_isExteriorAlgebra.pieceMap A'.exterior_isExteriorAlgebra θ (q : ℤ)) :
        (A.exteriorPower p, A.exteriorPower q) ⟶ (A'.exteriorPower p, A'.exteriorPower q)))

/-- `SheafOfModules.prodWedgeHom_comp_pieceMap`, transported along `p + q = n`. -/
theorem prodWedgeHomOfEq_comp_pieceMap (iF : F ⟶ H) (iG : G ⟶ H) (θ : H ⟶ H')
    (p q n : ℕ) (h : p + q = n) :
    prodWedgeHomOfEq AF AG A' (iF ≫ θ) (iG ≫ θ) p q n h =
      prodWedgeHomOfEq AF AG A iF iG p q n h ≫
        A.exterior_isExteriorAlgebra.pieceMap A'.exterior_isExteriorAlgebra θ (n : ℤ) := by
  subst h
  rw [prodWedgeHomOfEq_rfl, prodWedgeHomOfEq_rfl]
  exact prodWedgeHom_comp_pieceMap AF AG A A' iF iG θ p q

/-- **The Künneth comparison of exterior powers is natural in the ambient module**: replacing the
two structural maps by their composites with `θ : H ⟶ H'` postcomposes the comparison with
`⋀^n θ`. -/
theorem exteriorPowerProdHom_comp_pieceMap (iF : F ⟶ H) (iG : G ⟶ H) (θ : H ⟶ H')
    (n : ℕ) :
    exteriorPowerProdHom AF AG A' (iF ≫ θ) (iG ≫ θ) n =
      exteriorPowerProdHom AF AG A iF iG n ≫
        A.exterior_isExteriorAlgebra.pieceMap A'.exterior_isExteriorAlgebra θ (n : ℤ) := by
  refine Limits.Sigma.hom_ext _ _ fun i => ?_
  rw [exteriorPowerProdHom, Limits.Sigma.ι_comp_desc, exteriorPowerProdHom, ← Category.assoc,
    Limits.Sigma.ι_comp_desc]
  exact prodWedgeHomOfEq_comp_pieceMap AF AG A A' iF iG θ i.down.1.1 i.down.1.2 n
    i.down.2

/-- `SheafOfModules.exteriorPowerProdHom_comp_pieceMap` with the two composites named by
hypotheses. -/
theorem exteriorPowerProdHom_eq_of_comp (iF : F ⟶ H) (iG : G ⟶ H) (θ : H ⟶ H') (iF' : F ⟶ H')
    (iG' : G ⟶ H') (hF : iF ≫ θ = iF') (hG : iG ≫ θ = iG') (n : ℕ) :
    exteriorPowerProdHom AF AG A' iF' iG' n =
      exteriorPowerProdHom AF AG A iF iG n ≫
        A.exterior_isExteriorAlgebra.pieceMap A'.exterior_isExteriorAlgebra θ (n : ℤ) := by
  subst hF hG
  exact exteriorPowerProdHom_comp_pieceMap AF AG A A' iF iG θ n

end SheafOfModules

namespace AlgebraicGeometry.Scheme.Modules

/-- **The Künneth comparison of exterior powers depends on the chosen splitting only through an
automorphism of `⋀^n ℋ` which fixes the sub and the quotient.** For two splittings `sp`, `sp'`
of a short complex `0 ⟶ ℱ ⟶ ℋ ⟶ 𝒢 ⟶ 0` of `𝒪_X`-modules the two comparisons differ by
postcomposition with `⋀^n θ`, where `θ = 𝟙 - g ≫ (sp.s ≫ sp'.r) ≫ f` is the automorphism of `ℋ`
carrying `sp` to `sp'`.

This is the exact extent of the dependence: `θ` satisfies `f ≫ θ = f` and `θ ≫ g = g`, and
differs from the identity by a morphism factoring through `f`
(`CategoryTheory.ShortComplex.Splitting.transition_sub_id`). -/
theorem exteriorPowerProdHom_splitting_eq {Z : Scheme.{u}} {T : ShortComplex Z.Modules}
    (sp sp' : T.Splitting)
    (AF : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras
      (Opens.grothendieckTopology Z.carrier) T.X₁)
    (AG : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras
      (Opens.grothendieckTopology Z.carrier) T.X₃)
    (A : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras
      (Opens.grothendieckTopology Z.carrier) T.X₂) (n : ℕ) :
    _root_.SheafOfModules.exteriorPowerProdHom AF AG A T.f sp'.s n =
      _root_.SheafOfModules.exteriorPowerProdHom AF AG A T.f sp.s n ≫
        A.exterior_isExteriorAlgebra.pieceMap A.exterior_isExteriorAlgebra
          (sp.transition sp') (n : ℤ) :=
  _root_.SheafOfModules.exteriorPowerProdHom_eq_of_comp AF AG A A T.f sp.s
    (sp.transition sp') T.f sp'.s (sp.f_comp_transition sp') (sp.s_comp_transition sp') n

/-- The automorphism of `⋀^n ℋ` through which the Künneth comparison depends on the splitting
(`AlgebraicGeometry.Scheme.Modules.exteriorPowerProdHom_splitting_eq`) is an isomorphism. -/
theorem isIso_pieceMap_transition {Z : Scheme.{u}} {T : ShortComplex Z.Modules}
    (sp sp' : T.Splitting)
    (A : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras
      (Opens.grothendieckTopology Z.carrier) T.X₂) (n : ℤ) :
    IsIso (A.exterior_isExteriorAlgebra.pieceMap A.exterior_isExteriorAlgebra
      (sp.transition sp') n) :=
  A.exterior_isExteriorAlgebra.isIso_pieceMap A.exterior_isExteriorAlgebra _
    (sp.isIso_transition sp') n

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Hom

variable {X Y S : Scheme.{u}}

/-- **The local Künneth decomposition of the relative forms of a smooth morphism depends on the
chosen splitting only through the transition automorphism of `Ω_{X/S}|_U`.** Over an open `U` of
`X` any two splittings `sp`, `sp'` of `0 ⟶ f^*Ω_{Y/S} ⟶ Ω_{X/S} ⟶ Ω_{X/Y} ⟶ 0` give comparisons
differing by postcomposition with `⋀^nθ`, where

`θ = 𝟙 - (Ω_{X/S} ⟶ Ω_{X/Y}) ≫ (sp.s ≫ sp'.r) ≫ (f^*Ω_{Y/S} ⟶ Ω_{X/S})`

is the automorphism of `Ω_{X/S}|_U` carrying `sp` to `sp'`: it fixes `f^*Ω_{Y/S} ⟶ Ω_{X/S}` and
`Ω_{X/S} ⟶ Ω_{X/Y}` and differs from the identity by a morphism factoring through
`f^*Ω_{Y/S} ⟶ Ω_{X/S}`, i.e. through the first step of the filtration of Section 0FMK. -/
theorem exteriorPowerProdHom_relativeDifferentials_splitting_eq (f : X ⟶ Y) (g : Y ⟶ S)
    (U : X.Opens) (sp sp' : (relativeDifferentialsShortComplexRestrict f g U).Splitting)
    (n : ℕ) :
    _root_.SheafOfModules.exteriorPowerProdHom
        (_root_.SheafOfModules.ringedSpaceAlgebras (U : Scheme.{u}).toRingedSpace
          (relativeDifferentialsShortComplexRestrict f g U).X₁)
        (_root_.SheafOfModules.ringedSpaceAlgebras (U : Scheme.{u}).toRingedSpace
          (relativeDifferentialsShortComplexRestrict f g U).X₃)
        (_root_.SheafOfModules.ringedSpaceAlgebras (U : Scheme.{u}).toRingedSpace
          (relativeDifferentialsShortComplexRestrict f g U).X₂)
        (relativeDifferentialsShortComplexRestrict f g U).f sp'.s n =
      _root_.SheafOfModules.exteriorPowerProdHom
          (_root_.SheafOfModules.ringedSpaceAlgebras (U : Scheme.{u}).toRingedSpace
            (relativeDifferentialsShortComplexRestrict f g U).X₁)
          (_root_.SheafOfModules.ringedSpaceAlgebras (U : Scheme.{u}).toRingedSpace
            (relativeDifferentialsShortComplexRestrict f g U).X₃)
          (_root_.SheafOfModules.ringedSpaceAlgebras (U : Scheme.{u}).toRingedSpace
            (relativeDifferentialsShortComplexRestrict f g U).X₂)
          (relativeDifferentialsShortComplexRestrict f g U).f sp.s n ≫
        _root_.SheafOfModules.GradedAlgebra.IsExteriorAlgebra.pieceMap
          (_root_.SheafOfModules.ringedSpaceAlgebras (U : Scheme.{u}).toRingedSpace
            (relativeDifferentialsShortComplexRestrict f g U).X₂).exterior_isExteriorAlgebra
          (_root_.SheafOfModules.ringedSpaceAlgebras (U : Scheme.{u}).toRingedSpace
            (relativeDifferentialsShortComplexRestrict f g U).X₂).exterior_isExteriorAlgebra
          (sp.transition sp') (n : ℤ) :=
  Scheme.Modules.exteriorPowerProdHom_splitting_eq sp sp' _ _ _ n

end AlgebraicGeometry.Scheme.Hom

end
