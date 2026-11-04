module

public import StacksFrontier.AlgebraicGeometry.Quot.SmallEtaleDerivedPullbackTensorCompatibility
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartwiseBaseChangeTensorRight
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedPullbackLocallyFree
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineDerivedPushforwardPullbackTensor
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.CohomologyBaseChangeSheafHom
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.CohomologyBaseChangeSheafHomSupplement
public import StacksFrontier.CategoryTheory.Adjunction.PullbackInternalHomPushforward
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.DerivedPullbackRightUnitor

/-!
# The tensor pairing on algebraic spaces through the map of Stacks 08JF

Let `h : X' ⟶ X` be a morphism of algebraic spaces and `Π, G ∈ D(𝒪_X)`. In the proof of
Stacks 08JY a section `α : Lh^*𝒪_X ⟶ Lh^*R𝓗om(Π, G)` is turned into a morphism
`Lh^*Π ⟶ Lh^*G` by the tensor pairing `CategoryTheory.Functor.tensorPairing`:

`Lh^*Π ⟶ Lh^*(𝒪_X ⊗^L Π) ≅ Lh^*𝒪_X ⊗^L Lh^*Π ⟶ Lh^*R𝓗om(Π, G) ⊗^L Lh^*Π`
`≅ Lh^*(R𝓗om(Π, G) ⊗^L Π) ⟶ Lh^*G`.

This file identifies that pairing with the composite through the map of Stacks 08JF,
`φ : Lh^*R𝓗om(Π, G) ⟶ R𝓗om(Lh^*Π, Lh^*G)`: the pairing of `α` is the morphism
`Lh^*Π ≅ 𝒪_{X'} ⊗^L Lh^*Π ⟶ Lh^*G` adjoint, under Stacks 08J8 on `X'`, to
`𝒪_{X'} ≅ Lh^*𝒪_X ⟶ Lh^*R𝓗om(Π, G) ⟶ R𝓗om(Lh^*Π, Lh^*G)`. The input is the unit coherence of
the isomorphism of Stacks 07A4: `Lh^*` of the identification `Π ≅ 𝒪_X ⊗^L Π`, followed by
Stacks 07A4 and `Lh^*𝒪_X ≅ 𝒪_{X'}`, is the identification `Lh^*Π ≅ 𝒪_{X'} ⊗^L Lh^*Π`.

The identification `K ≅ 𝒪_X ⊗^L K` used here is the inverse of the unit law `K ⊗^L 𝒪_X ≅ K`
followed by the commutativity constraint of `⊗^L` (Tag 0FPT). Its unit coherence comes from the
two coherences of Stacks 07A4 already available on ringed topoi: with the right unit laws
(`Stacks.Cohomology.DerivedPullbackOfToposHom.derivedPullbackTensorIso_hom_app_unit`) and with the
commutativity constraints
(`AlgebraicGeometry.Space.smallEtaleDerivedPullbackTensorIso_braiding`).

## Main definitions

* `AlgebraicGeometry.Space.smallEtaleDerivedTensorStructureIso`: `K ≅ 𝒪_X ⊗^L K`.

## Main results

* `AlgebraicGeometry.Space.smallEtaleDerivedPullbackTensorIso_hom_app_structureDerived`: the
  right unit coherence of Stacks 07A4 on algebraic spaces.
* `AlgebraicGeometry.Space.smallEtaleDerivedPullbackTensorIso_structureIso`: the unit coherence
  of Stacks 07A4 for `K ≅ 𝒪_X ⊗^L K`.
* `AlgebraicGeometry.Space.smallEtaleDerivedTensorPairing_eq_homEquiv_symm`: the tensor pairing
  through the map of Stacks 08JF.
* `AlgebraicGeometry.Space.relHomTensorPairing_smallEtale_app`: the same, for the components of
  `CategoryTheory.PullbackData.relHomTensorPairing` on
  `AlgebraicGeometry.Space.toposDerivedPullbackData`.

## Implementation notes

Every categorical step is a generic lemma whose objects are variables
(`CategoryTheory.Functor.tensorPairing_eq_comp_homEquiv_symm`,
`CategoryTheory.Functor.map_unitBraiding_comp_tensorComparison`), instantiated by application, so
that no rewriting happens across the two spellings of the modules on an algebraic space.

## References

* [Stacks Project, Tag 08JY](https://stacks.math.columbia.edu/tag/08JY)
* [Stacks Project, Tag 08JF](https://stacks.math.columbia.edu/tag/08JF)
* [Stacks Project, Tag 08J8](https://stacks.math.columbia.edu/tag/08J8)
* [Stacks Project, Tag 07A4](https://stacks.math.columbia.edu/tag/07A4)
* [Stacks Project, Tag 0FPT](https://stacks.math.columbia.edu/tag/0FPT)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

namespace CategoryTheory.Functor

variable {C D : Type*} [Category C] [Category D]

/-- **The unit coherence of a tensor comparison, for the unit law composed with the braiding.**
Let `μ : F(A ⊗ B) ≅ F A ⊗ F B` be compatible with the right unit laws `ρ` through
`u : F O_C ≅ O_D`, and with the braidings `β`. Then `F` of `K ≅ K ⊗ O_C ≅ O_C ⊗ K`, followed by
`μ` and `u ⊗ 1`, is `F K ≅ F K ⊗ O_D ≅ O_D ⊗ F K`. -/
theorem map_unitBraiding_comp_tensorComparison (TC : C ⥤ C ⥤ C) (TD : D ⥤ D ⥤ D) {F : C ⥤ D}
    (μ : Functor.uncurry.obj TC ⋙ F ≅ F.prod F ⋙ Functor.uncurry.obj TD) {OC : C} {OD : D}
    (u : F.obj OC ≅ OD) (ρC : TC.flip.obj OC ≅ 𝟭 C) (ρD : TD.flip.obj OD ≅ 𝟭 D)
    (βC : ∀ A B : C, (TC.obj A).obj B ≅ (TC.obj B).obj A)
    (βD : ∀ A B : D, (TD.obj A).obj B ≅ (TD.obj B).obj A)
    (hρ : ∀ E : C, μ.hom.app (E, OC) ≫ (TD.obj (F.obj E)).map u.hom ≫ ρD.hom.app (F.obj E) =
      F.map (ρC.hom.app E))
    (hβ : ∀ A B : C, F.map (βC A B).hom ≫ μ.hom.app (B, A) =
      μ.hom.app (A, B) ≫ (βD (F.obj A) (F.obj B)).hom)
    (hβD : ∀ (A : D) {B B' : D} (b : B ⟶ B'),
      (TD.obj A).map b ≫ (βD A B').hom = (βD A B).hom ≫ (TD.map b).app A)
    (K : C) :
    F.map (ρC.inv.app K ≫ (βC K OC).hom) ≫ μ.hom.app (OC, K) ≫ (TD.map u.hom).app (F.obj K) =
      ρD.inv.app (F.obj K) ≫ (βD (F.obj K) OD).hom := by
  have hX : μ.hom.app (K, OC) ≫ (TD.obj (F.obj K)).map u.hom =
      F.map (ρC.hom.app K) ≫ ρD.inv.app (F.obj K) := by
    rw [← hρ K, Category.assoc, Category.assoc, Iso.hom_inv_id_app]
    exact congrArg (fun t => μ.hom.app (K, OC) ≫ t)
      (Category.comp_id ((TD.obj (F.obj K)).map u.hom)).symm
  rw [F.map_comp, Category.assoc, reassoc_of% (hβ K OC), ← hβD, reassoc_of% hX,
    ← F.map_comp_assoc, Iso.inv_hom_id_app, F.map_id, Category.id_comp]

variable {TC : C ⥤ C ⥤ C} {TD : D ⥤ D ⥤ D} {F : C ⥤ D}
  (μ : Functor.uncurry.obj TC ⋙ F ≅ F.prod F ⋙ Functor.uncurry.obj TD)
  {HC : Cᵒᵖ ⥤ C ⥤ C} {HD : Dᵒᵖ ⥤ D ⥤ D}
  (adjC : ∀ P : C, TC.flip.obj P ⊣ HC.obj (op P))
  (adjD : ∀ P : D, TD.flip.obj P ⊣ HD.obj (op P))

/-- **The tensor pairing for the evaluation is adjoint to the map of Stacks 08JF.** For
`ℓ : Π ⟶ O ⊗ Π` and the evaluation `ev : H(Π, G) ⊗ Π ⟶ G`, the tensor pairing of
`α : F O ⟶ F H(Π, G)` is `F ℓ` and `μ` followed by the adjoint of `α ≫ φ`, with
`φ : F H(Π, G) ⟶ H(F Π, F G)` the map of Stacks 08JF. -/
theorem tensorPairing_eq_map_comp_homEquiv_symm {O Pm G : C} (ℓ : Pm ⟶ (TC.obj O).obj Pm)
    (α : F.obj O ⟶ F.obj ((HC.obj (op Pm)).obj G)) :
    tensorPairing TC F TD (fun M N => μ.app (M, N)) (R := (HC.obj (op Pm)).obj G) ℓ
        ((adjC Pm).counit.app G) α =
      F.map ℓ ≫ μ.hom.app (O, Pm) ≫ ((adjD (F.obj Pm)).homEquiv _ _).symm
        (α ≫ PullbackInternalHom.pullbackHomMap TC TD μ HC HD adjC adjD Pm G) := by
  rw [Adjunction.homEquiv_naturality_left_symm, PullbackInternalHom.pullbackHomMap,
    Equiv.symm_apply_apply]
  rfl

/-- **The tensor pairing for the evaluation, through the map of Stacks 08JF and a unit.** If
`F ℓ_C`, followed by `μ` and `u ⊗ 1` for `u : F O ≅ O_D`, is `ℓ_D : F Π ⟶ O_D ⊗ F Π`, then the
tensor pairing of `α : F O ⟶ F H(Π, G)` is `ℓ_D` followed by the adjoint of
`u⁻¹ ≫ α ≫ φ : O_D ⟶ H(F Π, F G)`. -/
theorem tensorPairing_eq_comp_homEquiv_symm {O Pm G : C} {OD : D} (u : F.obj O ≅ OD)
    (ℓ : Pm ⟶ (TC.obj O).obj Pm) (ℓD : F.obj Pm ⟶ (TD.obj OD).obj (F.obj Pm))
    (hℓ : F.map ℓ ≫ μ.hom.app (O, Pm) ≫ (TD.map u.hom).app (F.obj Pm) = ℓD)
    (α : F.obj O ⟶ F.obj ((HC.obj (op Pm)).obj G)) :
    tensorPairing TC F TD (fun M N => μ.app (M, N)) (R := (HC.obj (op Pm)).obj G) ℓ
        ((adjC Pm).counit.app G) α =
      ℓD ≫ ((adjD (F.obj Pm)).homEquiv _ _).symm
        (u.inv ≫ α ≫ PullbackInternalHom.pullbackHomMap TC TD μ HC HD adjC adjD Pm G) := by
  rw [tensorPairing_eq_map_comp_homEquiv_symm μ adjC adjD ℓ α, ← hℓ,
    Adjunction.homEquiv_naturality_left_symm (adjD (F.obj Pm)) u.inv]
  simp only [Category.assoc, Functor.flip_obj_map]
  rw [← NatTrans.comp_app_assoc, ← TD.map_comp, Iso.hom_inv_id, TD.map_id, NatTrans.id_app,
    Category.id_comp]
  rfl

end CategoryTheory.Functor

namespace AlgebraicGeometry.Space

universe u

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

attribute [local instance] HasDerivedCategory.standard

attribute [local instance 20000] AddCommGrpCat.FilteredColimits.forget_preservesFilteredColimits

attribute [local instance 5000] SmallEtale.instHasSheafify SmallEtale.instWEqualsLocallyBijective

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X X' : AlgebraicSpaces B S hS}

/-- **The structure sheaf on the left of `⊗^L`**, `K ≅ 𝒪_X ⊗^L K` on an algebraic space: the
inverse of the unit law `K ⊗^L 𝒪_X ≅ K` followed by the commutativity constraint of Tag 0FPT. -/
def smallEtaleDerivedTensorStructureIso (X : AlgebraicSpaces B S hS) (K : toposDerived B S hS X) :
    K ≅ ((smallEtaleDerivedTensor B S hS X).obj (structureDerived X)).obj K :=
  ((smallEtaleDerivedTensorProduct B S hS X).unitNatIso.app K).symm ≪≫
    (smallEtaleDerivedTensorProduct B S hS X).braiding K (structureDerived X)

/-- **Stacks 07A4 on algebraic spaces is compatible with the right unit laws**: for
`h : X' ⟶ X` and `E ∈ D(𝒪_X)`, `Lh^*(E ⊗^L 𝒪_X) ≅ Lh^*E ⊗^L Lh^*𝒪_X`, followed by
`Lh^*𝒪_X ≅ 𝒪_{X'}` and the unit law of `Lh^*E`, is `Lh^*` of the unit law of `E`. -/
theorem smallEtaleDerivedPullbackTensorIso_hom_app_structureDerived (h : X' ⟶ X)
    (E : toposDerived B S hS X) :
    (smallEtaleDerivedPullbackTensorIso h).hom.app (E, structureDerived X) ≫
        ((smallEtaleDerivedTensor B S hS X').obj
          ((smallEtaleDerivedModulePullback B S hS h).obj E)).map
            (smallEtaleDerivedModulePullbackUnitIso h).hom ≫
        (smallEtaleDerivedTensorProduct B S hS X').unitNatIso.hom.app
          ((smallEtaleDerivedModulePullback B S hS h).obj E) =
      (smallEtaleDerivedModulePullback B S hS h).map
        ((smallEtaleDerivedTensorProduct B S hS X).unitNatIso.hom.app E) :=
  Stacks.Cohomology.DerivedPullbackOfToposHom.derivedPullbackTensorIso_hom_app_unit
    (smallEtaleRingedToposHom B S hS h) (smallEtaleDerivedTensorProduct B S hS X')
    (smallEtaleDerivedTensorProduct B S hS X) E

/-- **The unit coherence of Stacks 07A4 on algebraic spaces**: for `h : X' ⟶ X` and
`K ∈ D(𝒪_X)`, `Lh^*` of `K ≅ 𝒪_X ⊗^L K`, followed by `Lh^*(𝒪_X ⊗^L K) ≅ Lh^*𝒪_X ⊗^L Lh^*K`
and `Lh^*𝒪_X ≅ 𝒪_{X'}`, is `Lh^*K ≅ 𝒪_{X'} ⊗^L Lh^*K`. -/
theorem smallEtaleDerivedPullbackTensorIso_structureIso (h : X' ⟶ X) (K : toposDerived B S hS X) :
    (smallEtaleDerivedModulePullback B S hS h).map (smallEtaleDerivedTensorStructureIso X K).hom ≫
        (smallEtaleDerivedPullbackTensorIso h).hom.app (structureDerived X, K) ≫
        ((smallEtaleDerivedTensor B S hS X').map
          (smallEtaleDerivedModulePullbackUnitIso h).hom).app
            ((smallEtaleDerivedModulePullback B S hS h).obj K) =
      (smallEtaleDerivedTensorStructureIso X'
        ((smallEtaleDerivedModulePullback B S hS h).obj K)).hom :=
  Functor.map_unitBraiding_comp_tensorComparison _ _ (smallEtaleDerivedPullbackTensorIso h)
    (smallEtaleDerivedModulePullbackUnitIso h) (smallEtaleDerivedTensorProduct B S hS X).unitNatIso
    (smallEtaleDerivedTensorProduct B S hS X').unitNatIso
    (smallEtaleDerivedTensorProduct B S hS X).braiding
    (smallEtaleDerivedTensorProduct B S hS X').braiding
    (smallEtaleDerivedPullbackTensorIso_hom_app_structureDerived h)
    (smallEtaleDerivedPullbackTensorIso_braiding h)
    (fun A _ _ b => (smallEtaleDerivedTensorProduct B S hS X').braiding_hom_naturality_right A b) K

/-- **The tensor pairing on algebraic spaces through the map of Stacks 08JF.** For
`h : X' ⟶ X`, `Π, G ∈ D(𝒪_X)` and `α : Lh^*𝒪_X ⟶ Lh^*R𝓗om(Π, G)`, the tensor pairing of `α`
(for `Π ≅ 𝒪_X ⊗^L Π` and the evaluation) is `Lh^*Π ≅ 𝒪_{X'} ⊗^L Lh^*Π` followed by the adjoint,
under Stacks 08J8 on `X'`, of `𝒪_{X'} ≅ Lh^*𝒪_X ⟶ Lh^*R𝓗om(Π, G) ⟶ R𝓗om(Lh^*Π, Lh^*G)`, the
last map that of Stacks 08JF. -/
theorem smallEtaleDerivedTensorPairing_eq_homEquiv_symm (h : X' ⟶ X)
    (Pm G : toposDerived B S hS X)
    (α : (smallEtaleDerivedModulePullback B S hS h).obj (structureDerived X) ⟶
      (smallEtaleDerivedModulePullback B S hS h).obj
        (((smallEtaleDerivedSheafHom B S hS X).obj (op Pm)).obj G)) :
    Functor.tensorPairing (smallEtaleDerivedTensor B S hS X)
        (smallEtaleDerivedModulePullback B S hS h) (smallEtaleDerivedTensor B S hS X')
        (fun M N => (smallEtaleDerivedPullbackTensorIso h).app (M, N))
        (R := ((smallEtaleDerivedSheafHom B S hS X).obj (op Pm)).obj G)
        (smallEtaleDerivedTensorStructureIso X Pm).hom
        ((smallEtaleDerivedTensorSheafHomAdjunction B S hS X Pm).counit.app G) α =
      (smallEtaleDerivedTensorStructureIso X'
          ((smallEtaleDerivedModulePullback B S hS h).obj Pm)).hom ≫
        ((smallEtaleDerivedTensorSheafHomAdjunction B S hS X'
          ((smallEtaleDerivedModulePullback B S hS h).obj Pm)).homEquiv _ _).symm
          ((smallEtaleDerivedModulePullbackUnitIso h).inv ≫ α ≫
            smallEtaleDerivedPullbackSheafHomMap h Pm G) := by
  have e : smallEtaleDerivedPullbackSheafHomMap h Pm G =
      PullbackInternalHom.pullbackHomMap (smallEtaleDerivedTensor B S hS X)
        (smallEtaleDerivedTensor B S hS X') (smallEtaleDerivedPullbackTensorIso h)
        (smallEtaleDerivedSheafHom B S hS X) (smallEtaleDerivedSheafHom B S hS X')
        (smallEtaleDerivedTensorSheafHomAdjunction B S hS X)
        (smallEtaleDerivedTensorSheafHomAdjunction B S hS X') Pm G := by
    rw [smallEtaleDerivedPullbackSheafHomMap_eq_homEquiv_counit]
    unfold PullbackInternalHom.pullbackHomMap
    congr 1
  rw [e]
  exact Functor.tensorPairing_eq_comp_homEquiv_symm (TC := smallEtaleDerivedTensor B S hS X)
    (TD := smallEtaleDerivedTensor B S hS X') (F := smallEtaleDerivedModulePullback B S hS h)
    (HC := smallEtaleDerivedSheafHom B S hS X) (HD := smallEtaleDerivedSheafHom B S hS X')
    (smallEtaleDerivedPullbackTensorIso h)
    (fun P => smallEtaleDerivedTensorSheafHomAdjunction B S hS X P)
    (fun P => smallEtaleDerivedTensorSheafHomAdjunction B S hS X' P)
    (smallEtaleDerivedModulePullbackUnitIso h) (smallEtaleDerivedTensorStructureIso X Pm).hom
    (smallEtaleDerivedTensorStructureIso X' ((smallEtaleDerivedModulePullback B S hS h).obj Pm)).hom
    (smallEtaleDerivedPullbackTensorIso_structureIso h Pm) α

variable {I : Type*} [Category I] {π : I ⥤ AlgebraicSpaces B S hS}

/-- **The components of the tensor pairing on relative Hom functors over algebraic spaces**, for
`Π ≅ 𝒪_X ⊗^L Π` and the evaluation: at a test object `i` with structure morphism
`h = κ i : X_i ⟶ X`, a section `α : Lh^*𝒪_X ⟶ Lh^*R𝓗om(Π, G)` goes to the morphism
`Lh^*Π ⟶ Lh^*G` adjoint, through `Lh^*Π ≅ 𝒪_{X_i} ⊗^L Lh^*Π`, to
`𝒪_{X_i} ≅ Lh^*𝒪_X ⟶ Lh^*R𝓗om(Π, G) ⟶ R𝓗om(Lh^*Π, Lh^*G)`. -/
theorem relHomTensorPairing_smallEtale_app (hP : (toposDerivedPullbackData B S hS).IsCoherent)
    (κ : PullbackData.ConeTo π X) (Pm G : toposDerived B S hS X) (i : I)
    (α : (toposDerivedPullbackData B S hS).relHomObj κ (structureDerived X)
      (((smallEtaleDerivedSheafHom B S hS X).obj (op Pm)).obj G) i) :
    (PullbackData.relHomTensorPairing (smallEtaleDerivedTensorCompatibility B S hS) hP κ
        (smallEtaleDerivedTensorStructureIso X Pm).hom
        ((smallEtaleDerivedTensorSheafHomAdjunction B S hS X Pm).counit.app G)).app (op i) α =
      (smallEtaleDerivedTensorStructureIso (π.obj i)
          ((smallEtaleDerivedModulePullback B S hS (κ.leg i)).obj Pm)).hom ≫
        ((smallEtaleDerivedTensorSheafHomAdjunction B S hS (π.obj i)
          ((smallEtaleDerivedModulePullback B S hS (κ.leg i)).obj Pm)).homEquiv _ _).symm
          ((smallEtaleDerivedModulePullbackUnitIso (κ.leg i)).inv ≫ α ≫
            smallEtaleDerivedPullbackSheafHomMap (κ.leg i) Pm G) :=
  smallEtaleDerivedTensorPairing_eq_homEquiv_symm (κ.leg i) Pm G α

end AlgebraicGeometry.Space

end
