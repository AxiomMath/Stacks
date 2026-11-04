module

public import StacksFrontier.AlgebraicGeometry.Quot.PicardFunctor
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionIdealCorrespondence
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InvertibleEquivalence
public import StacksFrontier.CategoryTheory.Adjunction.UnitIsoOfIntertwining

/-!
# The unit `N ⟶ g_*g^*N` at an invertible module

Let `g : W ⟶ V` be a morphism of algebraic spaces whose structure map `𝒪_V ⟶ g_*𝒪_W` is an
isomorphism.  The first paragraph of the proof of Stacks 0D27 observes that for every invertible
`𝒪_V`-module `N` the canonical map `N ⟶ g_*g^*N` — the unit of the adjunction `g^* ⊣ g_*` of
Stacks 03LU — is an isomorphism.  This file proves it, which is the assertion
`AlgebraicGeometry.Space.ModulePushforwardUnitIso`.

## Main results

* `AlgebraicGeometry.Space.isIso_pushforwardStructureProjection`: the structure map read as a
  map of `𝒪_V`-modules `𝒪_V ⟶ g_*𝒪_W` is an isomorphism when the structure map is one.
* `AlgebraicGeometry.Space.isIso_modulePullbackAdjunction_unit_app_unit`: the unit is then an
  isomorphism at `𝒪_V`.
* `AlgebraicGeometry.Space.modulePushforwardUnitIso`: **the unit is an isomorphism at every
  invertible module**, i.e. `ModulePushforwardUnitIso` holds.
* `AlgebraicGeometry.Space.bijective_modulePullback_map_of_isInvertibleModule`: consequently
  `g^*` is bijective on morphisms into an invertible module.
* `AlgebraicGeometry.Space.bijective_modulePullback_map_of_bijective_tensor` and
  `AlgebraicGeometry.Space.bijective_modulePullback_map_end_of_isInvertibleModule`: for any
  morphism `q`, bijectivity of `q^*` on hom sets transfers from `M ⊗ A ⟶ M ⊗ A'` to `A ⟶ A'`
  for `M` invertible, and from `End(𝒪_V)` to `End(L)` for `L` invertible.
* `Stacks.SheafOfModules.pullbackTensorIso_hom_app_naturality_right`: the comparison
  `f^*(F ⊗ G) ≅ f^*F ⊗ f^*G` of Stacks 03EL is natural in `G` for fixed `F`.

## Implementation notes

The source argues locally: `N` is locally trivial and the unit is an isomorphism at `𝒪_V`.  The
argument here is global and uses no local triviality.  The unit at `𝒪_V` is the structure map
composed with `g_*` of the identification `g^*𝒪_V ≅ 𝒪_W`
(`AlgebraicGeometry.Space.homEquiv_modulePullbackUnitIso_hom`), hence an isomorphism.  For an
invertible `N` choose a tensor inverse `N'`, so `N' ⊗ N ≅ 𝒪_V`.  Tensoring by `N'` is an
equivalence of `𝒪_V`-modules, tensoring by `g^*N'` (invertible by Stacks 0B8P) is an
equivalence of `𝒪_W`-modules, and `g^*` intertwines the two by Stacks 03EL.  The criterion
`CategoryTheory.Adjunction.isIso_unit_app_of_intertwining_of_iso` then moves invertibility of the
unit from `N' ⊗ N ≅ 𝒪_V` to `N`.

## References

* [Stacks Project, Tag 0D27](https://stacks.math.columbia.edu/tag/0D27)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
* [Stacks Project, Tag 0B8P](https://stacks.math.columbia.edu/tag/0B8P)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

section PullbackTensorNaturality

open AlgebraicGeometry Stacks.Sheaves.RingedToposModules

namespace Stacks.SheafOfModules

universe w w' v u v' u'

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w'}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w'})]
  [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify Y.J AddCommGrpCat.{w'}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}]

/-- The comparison `f^*(F ⊗ G) ≅ f^*F ⊗ f^*G` of Stacks 03EL is natural in the second factor,
in the form with the first factor fixed. -/
theorem pullbackTensorIso_hom_app_naturality_right
    (f : Stacks.Sheaves.RingedToposModules.RingedToposHom X Y)
    (F : SheafOfModules.{w'} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
    {G G' : SheafOfModules.{w'} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)} (φ : G ⟶ G') :
    f.pullbackModules.map
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{u', v', w', w', w'} Y.O).obj F).map φ) ≫
      (pullbackTensorIso f).hom.app (F, G') =
    (pullbackTensorIso f).hom.app (F, G) ≫
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} X.O).obj
        (f.pullbackModules.obj F)).map (f.pullbackModules.map φ) := by
  have := (pullbackTensorIso f).hom.naturality ((𝟙 F, φ) : (F, G) ⟶ (F, G'))
  simpa using this

end Stacks.SheafOfModules

end PullbackTensorNaturality

namespace AlgebraicGeometry.Space

universe u

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

attribute [local instance] Stacks.SheafOfModules.monoidalCategory

/-- The structure map `𝒪_V ⟶ g_*𝒪_W` of a morphism `g : W ⟶ V` of algebraic spaces, read as a
map of `𝒪_V`-modules, is an isomorphism when the structure map of sheaves of rings is one. -/
theorem isIso_pushforwardStructureProjection {V W : AlgebraicSpaces B S hS} (g : W ⟶ V)
    (hg : IsIso (structureSharp B S hS g)) :
    IsIso (pushforwardStructureProjection B S hS g) := by
  refine @isIso_of_reflects_iso _ _ _ _ _ _ (pushforwardStructureProjection B S hS g)
    (SheafOfModules.forget (structureRingSheaf B S hS V) ⋙ PresheafOfModules.toPresheaf _) ?_ _
  refine (NatTrans.isIso_iff_isIso_app _).mpr fun U ↦ ?_
  exact Functor.map_isIso (forget₂ RingCat AddCommGrpCat)
    (((sheafToPresheaf _ _).map (structureSharp B S hS g)).app U)

/-- **The unit `𝒪_V ⟶ g_*g^*𝒪_V` is an isomorphism** when the structure map `𝒪_V ⟶ g_*𝒪_W` is:
the unit composed with `g_*` of the identification `g^*𝒪_V ≅ 𝒪_W` is the structure map. -/
theorem isIso_modulePullbackAdjunction_unit_app_unit {V W : AlgebraicSpaces B S hS} (g : W ⟶ V)
    (hg : IsIso (structureSharp B S hS g)) :
    IsIso ((modulePullbackAdjunction B S hS g).unit.app
      (SheafOfModules.unit
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS V.1 V.2).O))) := by
  have h := homEquiv_modulePullbackUnitIso_hom B S hS g
  rw [Adjunction.homEquiv_unit] at h
  have := isIso_pushforwardStructureProjection g hg
  have : IsIso ((modulePullbackAdjunction B S hS g).unit.app
      (SheafOfModules.unit
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS V.1 V.2).O)) ≫
      (modulePushforward B S hS g).map (modulePullbackUnitIso B S hS g).hom) := by
    rw [h]
    exact isIso_pushforwardStructureProjection g hg
  exact IsIso.of_isIso_comp_right _
    ((modulePushforward B S hS g).map (modulePullbackUnitIso B S hS g).hom)

/-- An invertible module `N` has an invertible tensor inverse `N'` with `N' ⊗ N ≅ 𝒪_V`. -/
private theorem exists_invertible_tensor_iso_unit {V : AlgebraicSpaces B S hS}
    {N : Modules.{u, u} B S hS V.1 V.2} (hN : IsInvertibleModule V N) :
    ∃ N' : Modules.{u, u} B S hS V.1 V.2, IsInvertibleModule V N' ∧
      Nonempty (((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
        (structureSheaf B S hS V.1 V.2)).obj N').obj N ≅ SheafOfModules.unit
          (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS V.1 V.2).O)) := by
  have hV₁ : HasWeakSheafify (SmallEtale.topology B S hS V.1) AddCommGrpCat.{u} :=
    inferInstance
  have hV₂ : (SmallEtale.topology B S hS V.1).WEqualsLocallyBijective AddCommGrpCat.{u} :=
    inferInstance
  have := hN
  let hinv := Stacks.SheafOfModules.hasInverse_of_isInvertible
    (structureSheaf B S hS V.1 V.2).obj (structureRingPresheaf_isSheaf B S hS V.1 V.2) N
  exact ⟨hinv.inv,
    Stacks.SheafOfModules.isInvertible_of_hasInverse _ _ ⟨N, hinv.isoRight, hinv.isoLeft⟩,
    ⟨(Stacks.SheafOfModules.tensorObjIso (structureSheaf B S hS V.1 V.2).obj
      (structureRingPresheaf_isSheaf B S hS V.1 V.2) hinv.inv N).symm ≪≫ hinv.isoRight⟩⟩

/-- Tensoring by an invertible `M` and by its pullback `q^*M` are both equivalences. -/
private theorem isEquivalence_tensor_obj_of_isInvertibleModule {V W : AlgebraicSpaces B S hS}
    (q : W ⟶ V) {M : Modules.{u, u} B S hS V.1 V.2} (hM : IsInvertibleModule V M) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
        (structureSheaf B S hS V.1 V.2)).obj M).IsEquivalence ∧
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
        (structureSheaf B S hS W.1 W.2)).obj ((modulePullback B S hS q).obj M)).IsEquivalence :=
  ⟨(Stacks.SheafOfModules.isInvertible_iff_tensorLeftFunctor_isEquivalence _ _ M).mp hM,
    (Stacks.SheafOfModules.isInvertible_iff_tensorLeftFunctor_isEquivalence _ _ _).mp
      (modulePullbackInvertible q M hM)⟩

/-- **The unit `N ⟶ g_*g^*N` is an isomorphism at every invertible module** when the structure
map `𝒪_V ⟶ g_*𝒪_W` of `g : W ⟶ V` is an isomorphism.  This is the first paragraph of the proof
of Stacks 0D27, and it proves the assertion `AlgebraicGeometry.Space.ModulePushforwardUnitIso`
with no hypothesis. -/
theorem modulePushforwardUnitIso : ModulePushforwardUnitIso B S hS := by
  intro V W g hg N hN
  obtain ⟨N', hN', ⟨e⟩⟩ := exists_invertible_tensor_iso_unit hN
  let K : Modules.{u, u} B S hS V.1 V.2 ⥤ Modules.{u, u} B S hS V.1 V.2 :=
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
      (structureSheaf B S hS V.1 V.2)).obj N'
  let K' : Modules.{u, u} B S hS W.1 W.2 ⥤ Modules.{u, u} B S hS W.1 W.2 :=
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
      (structureSheaf B S hS W.1 W.2)).obj ((modulePullback B S hS g).obj N')
  have : K.IsEquivalence := (isEquivalence_tensor_obj_of_isInvertibleModule g hN').1
  have : K'.IsEquivalence := (isEquivalence_tensor_obj_of_isInvertibleModule g hN').2
  exact Adjunction.isIso_unit_app_of_intertwining_of_iso (modulePullbackAdjunction B S hS g)
    K K' (fun Y ↦ (Stacks.SheafOfModules.pullbackTensorIso
      (smallEtaleRingedToposModulesHom B S hS g)).app (N', Y))
    (fun f ↦ Stacks.SheafOfModules.pullbackTensorIso_hom_app_naturality_right
      (smallEtaleRingedToposModulesHom B S hS g) N' f) e
    (isIso_modulePullbackAdjunction_unit_app_unit g hg)

/-- **The inverse image along `g` is bijective on morphisms into an invertible module** when the
structure map `𝒪_V ⟶ g_*𝒪_W` is an isomorphism: for every `𝒪_V`-module `P` and invertible `N`,
`Hom(P, N) ⟶ Hom(g^*P, g^*N)` is a bijection. -/
theorem bijective_modulePullback_map_of_isInvertibleModule {V W : AlgebraicSpaces B S hS}
    (g : W ⟶ V) (hg : IsIso (structureSharp B S hS g)) (P : Modules.{u, u} B S hS V.1 V.2)
    {N : Modules.{u, u} B S hS V.1 V.2} (hN : IsInvertibleModule V N) :
    Function.Bijective (fun φ : P ⟶ N ↦ (modulePullback B S hS g).map φ) :=
  (Adjunction.isIso_unit_app_iff_bijective_map (modulePullbackAdjunction B S hS g) N).mp
    (modulePushforwardUnitIso g hg N hN) P

/-- **The inverse image is bijective on `A ⟶ B` when it is on `M ⊗ A ⟶ M ⊗ B`**, for any
morphism `q : W ⟶ V` of algebraic spaces and any invertible `𝒪_V`-module `M`.  Tensoring by `M`
and by `q^*M` are equivalences, and `q^*` intertwines them by Stacks 03EL. -/
theorem bijective_modulePullback_map_of_bijective_tensor {V W : AlgebraicSpaces B S hS}
    (q : W ⟶ V) {M : Modules.{u, u} B S hS V.1 V.2} (hM : IsInvertibleModule V M)
    (A A' : Modules.{u, u} B S hS V.1 V.2)
    (h : Function.Bijective (fun φ : ((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
        (structureSheaf B S hS V.1 V.2)).obj M).obj A ⟶
          ((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
            (structureSheaf B S hS V.1 V.2)).obj M).obj A' ↦
        (modulePullback B S hS q).map φ)) :
    Function.Bijective (fun φ : A ⟶ A' ↦ (modulePullback B S hS q).map φ) := by
  let K : Modules.{u, u} B S hS V.1 V.2 ⥤ Modules.{u, u} B S hS V.1 V.2 :=
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
      (structureSheaf B S hS V.1 V.2)).obj M
  let K' : Modules.{u, u} B S hS W.1 W.2 ⥤ Modules.{u, u} B S hS W.1 W.2 :=
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
      (structureSheaf B S hS W.1 W.2)).obj ((modulePullback B S hS q).obj M)
  have : K.IsEquivalence := (isEquivalence_tensor_obj_of_isInvertibleModule q hM).1
  have : K'.IsEquivalence := (isEquivalence_tensor_obj_of_isInvertibleModule q hM).2
  exact Functor.bijective_map_of_intertwining (modulePullback B S hS q) K K'
    (fun Y ↦ (Stacks.SheafOfModules.pullbackTensorIso
      (smallEtaleRingedToposModulesHom B S hS q)).app (M, Y))
    (fun f ↦ Stacks.SheafOfModules.pullbackTensorIso_hom_app_naturality_right
      (smallEtaleRingedToposModulesHom B S hS q) M f) A A' h

/-- **Bijectivity of the inverse image on endomorphisms of `𝒪_V` gives it on endomorphisms of
every invertible module.**  For any morphism `q : W ⟶ V` of algebraic spaces and invertible
`𝒪_V`-module `L`, if `q^*` is bijective on `End(𝒪_V)` then it is bijective on `End(L)`. -/
theorem bijective_modulePullback_map_end_of_isInvertibleModule {V W : AlgebraicSpaces B S hS}
    (q : W ⟶ V) {L : Modules.{u, u} B S hS V.1 V.2} (hL : IsInvertibleModule V L)
    (h : Function.Bijective (fun φ : SheafOfModules.unit
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS V.1 V.2).O) ⟶
          SheafOfModules.unit
            (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS V.1 V.2).O) ↦
        (modulePullback B S hS q).map φ)) :
    Function.Bijective (fun φ : L ⟶ L ↦ (modulePullback B S hS q).map φ) := by
  obtain ⟨L', hL', ⟨e⟩⟩ := exists_invertible_tensor_iso_unit hL
  exact bijective_modulePullback_map_of_bijective_tensor q hL' L L
    (((modulePullback B S hS q).bijective_map_iff_of_iso e e).mpr h)

end AlgebraicGeometry.Space

end
