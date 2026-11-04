module

public import StacksFrontier.AlgebraicGeometry.Duality.ProjectionFormulaUnit
public import StacksFrontier.AlgebraicGeometry.QuasiCoherent.ReconstructionGlobalNatIso

/-!
# The reconstruction chart read at the structure sheaf

The remaining conjunct of [Stacks, Tag 0GPJ] is a single natural isomorphism `e(𝓕) ≅ g^*𝓕 ⊗ M`,
and it is obtained by glueing the per-chart comparisons `AlgebraicGeometry.chartComparisonIso`.
The glueing needs any two of them to agree over an affine open contained in both charts, and the
rigidity statement `AlgebraicGeometry.natIso_eq_of_app_unit_eq_of_iso` reduces that to agreement
at the structure sheaf.  This file assembles the identities that computation needs.

## The three coherences

Each of the two per-chart comparisons is, at `𝒪_X`, a composite of chart data with its own
inverse — but the two occurrences are separated by the right unitor `L ⊗ 𝒪_V ≅ L` and by the
transport of the tensor functor along an isomorphism of the twisting sheaf, so cancelling them is
not `CategoryTheory.Iso.hom_inv_id`.  Three statements bridge the gap, and the library had none
of them:

* `AlgebraicGeometry.tensorLeftFunctorObjUnitSchemeIso_naturality` — the right unitor is natural
  in the twisting sheaf, using `mapIso` of the native sheaf tensor bifunctor.  The library's
  unitor and its transport were both objectwise.
* `AlgebraicGeometry.restrictFunctorIsoPullback_inv_app_unit_comp_restrictUnitIso` — the
  comparison between restriction and inverse image carries the restriction of the structure sheaf
  to the structure sheaf, compatibly with
  `AlgebraicGeometry.Scheme.Modules.pullbackUnitIso`.  Both sides transpose along
  `pullback ⊣ pushforward` to the canonical `𝒪_X ⟶ f_*𝒪_W`.
* `AlgebraicGeometry.tensorLeftFunctorCompPullback_hom_app_unit` — **the comparison of
  [Stacks, Tag 01CD] is compatible with the right unitor.**  This is
  `Stacks.RingedSpace.comparison_rightUnitor`, reached by identifying the braiding-then-left-unitor
  presentation of `AlgebraicGeometry.tensorLeftFunctorObjUnitSchemeIso` with the sheafified
  presheaf right unitor `Stacks.RingedSpace.tensorSheafUnitRightIso`
  (`AlgebraicGeometry.tensorLeftFunctorObjUnitSchemeIso_hom`), which is
  `CategoryTheory.braiding_leftUnitor` on presheaves of modules.

## The chart's unit chain

`AlgebraicGeometry.chartUnitChain` is the one chart-level identity: the identification of
`(f ≫ U.ι)^*𝒪_X` with `𝒪_V` that the left-hand side of a chart produces — restriction read as
inverse image, then the two inverse images composed — is the canonical
`AlgebraicGeometry.Scheme.Modules.pullbackUnitIso`.  It is
`AlgebraicGeometry.Scheme.Modules.pullbackUnitIso_comp` together with the second bullet above.

## Implementation notes

The rest of the file reads each comparison isomorphism of
`StacksFrontier/AlgebraicGeometry/QuasiCoherent/ReconstructionGlobalNatIso.lean` at a single object.
Every one of them holds by `rfl`; they exist so that a consumer can rewrite with them instead of
unfolding a definition inside a term whose size makes `rw` time out.

## References

* [Stacks Project, Proposition 56.6.6 (Tag 0GPJ)](https://stacks.math.columbia.edu/tag/0GPJ)
* [Stacks Project, Lemma 01CD](https://stacks.math.columbia.edu/tag/01CD)
-/

@[expose] public noncomputable section

attribute [local implicit_reducible] Stacks.SheafOfModules.TensorSheafification.structureSheaf

open CategoryTheory CategoryTheory.Limits TopologicalSpace CategoryTheory.MonoidalCategory

universe v u w

namespace AlgebraicGeometry.ReconstructionUnitor

section Site

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (O : Cᵒᵖ ⥤ CommRingCat.{w})
  (hO : Presheaf.IsSheaf J (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf O))
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify J AddCommGrpCat.{w}]

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules

/-- The component of `Stacks.SheafOfModules.Invertible.sheafifyForgetIso` at a sheaf of modules
is `Stacks.SheafOfModules.sheafifyValIso`: both are the sheafification counit there, the former
preceded by an `eqToIso` of a `rfl`, which is the identity. -/
theorem sheafifyForgetIso_hom_app (F : SheafOfModules.{w}
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) :
    (Stacks.SheafOfModules.Invertible.sheafifyForgetIso O hO).hom.app F =
      (Stacks.SheafOfModules.sheafifyValIso O hO F).hom :=
  Category.id_comp _

/-- **The braiding followed by the left unitor is the right unitor**, for the sheafified tensor
product of Tag 01CA. The composite of the sheafified presheaf braiding with
`Stacks.SheafOfModules.Invertible.tensorLeftFunctorUnitIso` — which is how the right unitor
`F ⊗ 𝒪 ≅ F` is built when the structure sheaf sits in the *argument* slot of the tensor
functor — agrees with `Stacks.SheafOfModules.tensorSheafUnitRightIso`, the sheafification of the
presheaf right unitor, which is the one carrying the section formula `x ⊗ r ↦ r • x`.

Both sides are the sheafification of a presheaf-level morphism followed by the sheafification
counit, so the statement reduces to `CategoryTheory.braiding_leftUnitor` on presheaves of
modules. -/
theorem braidedLeftUnitor_eq_tensorSheafUnitRightIso (F : SheafOfModules.{w}
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) :
    ((Stacks.SheafOfModules.TensorSheafification.sheafify O hO).mapIso
          (β_ F.val (SheafOfModules.unit
            (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)).val) ≪≫
        (Stacks.SheafOfModules.Invertible.tensorLeftFunctorUnitIso O hO).app F).hom =
      (Stacks.SheafOfModules.tensorSheafUnitRightIso O hO F).hom := by
  show (Stacks.SheafOfModules.TensorSheafification.sheafify O hO).map
        (β_ F.val
          (𝟙_ (PresheafOfModules.{w}
            (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf O)))).hom ≫
      ((Stacks.SheafOfModules.TensorSheafification.sheafify O hO).map (λ_ F.val).hom ≫
        (Stacks.SheafOfModules.Invertible.sheafifyForgetIso O hO).hom.app F) =
    (Stacks.SheafOfModules.TensorSheafification.sheafify O hO).map (ρ_ F.val).hom ≫
      (Stacks.SheafOfModules.sheafifyValIso O hO F).hom
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun k ↦ k ≫
          (Stacks.SheafOfModules.Invertible.sheafifyForgetIso O hO).hom.app F)
        (((Stacks.SheafOfModules.TensorSheafification.sheafify O hO).map_comp
            (β_ F.val
              (𝟙_ (PresheafOfModules.{w}
                (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf O)))).hom
            (λ_ F.val).hom).symm)).trans
      ((congrArg (fun k ↦ (Stacks.SheafOfModules.TensorSheafification.sheafify O hO).map k ≫
            (Stacks.SheafOfModules.Invertible.sheafifyForgetIso O hO).hom.app F)
          (braiding_leftUnitor F.val)).trans
        (congrArg (fun k ↦
            (Stacks.SheafOfModules.TensorSheafification.sheafify O hO).map (ρ_ F.val).hom ≫ k)
          (sheafifyForgetIso_hom_app O hO F))))

end Site

section Aux

open CategoryTheory.MonoidalCategory

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules

/-- For an isomorphism `e : N ≅ N'` of sheaves of modules, the composite of the sheafified
braiding `N ⊗ 𝒪 ≅ 𝒪 ⊗ N` with the left unitor `𝒪 ⊗ N ≅ N` is natural with respect to `e`. -/
theorem swap_unitIso_naturality {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C} (O : Cᵒᵖ ⥤ CommRingCat.{w})
    (hO : Presheaf.IsSheaf J (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf O))
    [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]
    {N N' : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)}
    (e : N ≅ N') :
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat) hO⟩).mapIso
        (X := N) (Y := N') e).hom.app
          (SheafOfModules.unit (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) ≫
        (((Stacks.SheafOfModules.TensorSheafification.sheafify O hO).mapIso
              (β_ N'.val (SheafOfModules.unit
                (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)).val)).hom ≫
          (Stacks.SheafOfModules.Invertible.tensorLeftFunctorUnitIso O hO).hom.app N') =
      (((Stacks.SheafOfModules.TensorSheafification.sheafify O hO).mapIso
            (β_ N.val (SheafOfModules.unit
              (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)).val)).hom ≫
        (Stacks.SheafOfModules.Invertible.tensorLeftFunctorUnitIso O hO).hom.app N) ≫ e.hom := by
  have hbr := CategoryTheory.BraidedCategory.braiding_naturality_left e.hom.val
    (SheafOfModules.unit (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)).val
  have key := congrArg (Stacks.SheafOfModules.TensorSheafification.sheafify O hO).map hbr
  simp only [Functor.map_comp] at key
  have hnat := (Stacks.SheafOfModules.Invertible.tensorLeftFunctorUnitIso O hO).hom.naturality e.hom
  let sourceUnitor : (Stacks.SheafOfModules.TensorSheafification.sheafify O hO).obj
      ((SheafOfModules.unit
        (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)).val ⊗ N.val) ⟶ N :=
    (Stacks.SheafOfModules.Invertible.tensorLeftFunctorUnitIso O hO).hom.app N
  let targetUnitor : (Stacks.SheafOfModules.TensorSheafification.sheafify O hO).obj
      ((SheafOfModules.unit
        (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)).val ⊗ N'.val) ⟶ N' :=
    (Stacks.SheafOfModules.Invertible.tensorLeftFunctorUnitIso O hO).hom.app N'
  change (Stacks.SheafOfModules.TensorSheafification.sheafify O hO).map
        ((SheafOfModules.unit
          (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)).val ◁ e.hom.val) ≫
      targetUnitor = sourceUnitor ≫ e.hom at hnat
  show (Stacks.SheafOfModules.TensorSheafification.sheafify O hO).map
        (e.hom.val ▷ (SheafOfModules.unit
          (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)).val) ≫
      ((Stacks.SheafOfModules.TensorSheafification.sheafify O hO).map
          (β_ N'.val (SheafOfModules.unit
            (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)).val).hom ≫
        targetUnitor) =
    ((Stacks.SheafOfModules.TensorSheafification.sheafify O hO).map
        (β_ N.val (SheafOfModules.unit
          (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)).val).hom ≫
      sourceUnitor) ≫ e.hom
  rw [← Category.assoc, key, Category.assoc, hnat, Category.assoc]

end Aux
end AlgebraicGeometry.ReconstructionUnitor

namespace AlgebraicGeometry

/- One object is named through two chains of definitions — the structure sheaf of a scheme as
`AlgebraicGeometry.Scheme.ringCatSheaf` and as
`Stacks.SheafOfModules.TensorSheafification.structureSheaf` of its structure presheaf — and
instance search, which works at `reducible` transparency, sees through neither.  The same list
is declared in `StacksFrontier/AlgebraicGeometry/QuasiCoherent/AffineReconstruction.lean`;
`AlgebraicGeometry.Scheme.unitModule` is the third such chain, for the structure sheaf read as a
module over itself. -/
attribute [local implicit_reducible] AlgebraicGeometry.SheafedSpace.sheaf
  AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Hom
  AlgebraicGeometry.Scheme.Modules.instCategory CategoryTheory.sheafCompose TopCat.Sheaf
  TopCat.Presheaf.IsSheaf AlgebraicGeometry.Scheme.unitModule

/-- **The right unitor `L ⊗ 𝒪_Y ≅ L` is natural in `L`.**  For an isomorphism `e : N ≅ N'` of
sheaves of `𝒪_Y`-modules, the native tensor bifunctor's `mapIso e` read at the structure sheaf
commutes with the two unitors.

The library has the unitor and its transport only objectwise, so neither is a natural
transformation whose naturality could be quoted; this is that naturality, proved from the
naturality of the braiding and of `𝒪 ⊗ - ≅ 𝟭`. -/
theorem tensorLeftFunctorObjUnitSchemeIso_naturality {Y : Scheme.{u}} {N N' : Y.Modules}
    (e : N ≅ N') :
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.sheaf).mapIso
      (X := N) (Y := N') e).hom.app
          (SheafOfModules.unit Y.ringCatSheaf) ≫
        (tensorLeftFunctorObjUnitSchemeIso N').hom =
      (tensorLeftFunctorObjUnitSchemeIso N).hom ≫ e.hom :=
  ReconstructionUnitor.swap_unitIso_naturality Y.presheaf Y.ringCatSheaf.2 e

/-- **The comparison between restriction and inverse image carries the structure sheaf to the
structure sheaf.**  Along an open immersion `f`, identifying `f^*𝒪_X` with `𝒪_X|_W`
(`AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback`) and then `𝒪_X|_W` with `𝒪_W`
(`AlgebraicGeometry.Scheme.Modules.restrictUnitIso`) is the canonical identification
`AlgebraicGeometry.Scheme.Modules.pullbackUnitIso`.

Both sides transpose along `f^* ⊣ f_*` to the canonical morphism `𝒪_X ⟶ f_*𝒪_W`: the
restriction side by `CategoryTheory.Adjunction.unit_leftAdjointUniq_hom_app`, the inverse-image
side by `AlgebraicGeometry.Scheme.Modules.pullbackUnitIso_homEquiv`.  On sections both are the
restriction map of `𝒪_X` followed by `AlgebraicGeometry.Scheme.Hom.appIso`. -/
theorem restrictFunctorIsoPullback_inv_app_unit_comp_restrictUnitIso' {W X : Scheme.{u}}
    (f : W ⟶ X) [IsOpenImmersion f] :
    (Scheme.Modules.restrictFunctorIsoPullback f).inv.app (SheafOfModules.unit X.ringCatSheaf) ≫
        (Scheme.Modules.restrictUnitIso f).hom = (Scheme.Modules.pullbackUnitIso f).hom := by
  show (Scheme.Modules.restrictFunctorIsoPullback f).inv.app (Scheme.unitModule X) ≫
      (Scheme.Modules.restrictUnitIso f).hom = (Scheme.Modules.pullbackUnitIso f).hom
  apply ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv
    (Scheme.unitModule X) (Scheme.unitModule W)).injective
  rw [Scheme.Modules.pullbackUnitIso_homEquiv]
  have key : (Scheme.Modules.pullbackPushforwardAdjunction f).unit.app (Scheme.unitModule X) ≫
      (Scheme.Modules.pushforward f).map
        ((Scheme.Modules.restrictFunctorIsoPullback f).inv.app (Scheme.unitModule X)) =
      (Scheme.Modules.restrictAdjunction f).unit.app (Scheme.unitModule X) := by
    rw [← Adjunction.unit_leftAdjointUniq_hom_app (Scheme.Modules.restrictAdjunction f)
      (Scheme.Modules.pullbackPushforwardAdjunction f) (Scheme.unitModule X),
      Category.assoc, ← Functor.map_comp]
    simp [Scheme.Modules.restrictFunctorIsoPullback]
  rw [Adjunction.homEquiv_unit, Functor.map_comp, ← Category.assoc, key]
  ext U x
  have hring : X.presheaf.map (homOfLE (f.image_preimage_le U)).op ≫
      (f.appIso (f ⁻¹ᵁ U)).hom = f.app U := by
    rw [Scheme.Hom.appIso_hom', Scheme.Hom.map_appLE, Scheme.Hom.app_eq_appLE]
  exact congr($hring x)

/-- For an open `U` of `X`, identifying `(U.ι)^*𝒪_X` with `𝒪_X|_U` and then with `𝒪_U` is the
canonical identification `AlgebraicGeometry.Scheme.Modules.pullbackUnitIso U.ι`. -/
theorem restrictFunctorIsoPullback_inv_app_unit_comp_restrictUnitIso {X : Scheme.{u}}
    (U : X.Opens) :
    (Scheme.Modules.restrictFunctorIsoPullback U.ι).inv.app
          (SheafOfModules.unit X.ringCatSheaf) ≫
        (Scheme.Modules.restrictUnitIso U.ι).hom =
      (Scheme.Modules.pullbackUnitIso U.ι).hom :=
  restrictFunctorIsoPullback_inv_app_unit_comp_restrictUnitIso' U.ι

/-- **The right unitor `L ⊗ 𝒪_Y ≅ L` on a scheme is the unitor of the tensor product sheaf.**
`AlgebraicGeometry.tensorLeftFunctorObjUnitSchemeIso` is built as the braiding followed by the
left unitor, and `Stacks.RingedSpace.tensorSheafUnitRightIso` is the sheafified presheaf right
unitor.  This is `ReconstructionUnitor.braidedLeftUnitor_eq_tensorSheafUnitRightIso` read at
the ringed site of a scheme. -/
theorem tensorLeftFunctorObjUnitSchemeIso_hom {Y : Scheme.{u}} (L : Y.Modules) :
    (tensorLeftFunctorObjUnitSchemeIso L).hom =
      (Stacks.RingedSpace.tensorSheafUnitRightIso Y.toRingedSpace L).hom :=
  ReconstructionUnitor.braidedLeftUnitor_eq_tensorSheafUnitRightIso Y.presheaf Y.ringCatSheaf.2 L

/-- **The comparison of [Stacks, Tag 01CD] is compatible with the right unitor.**  For
`q : W ⟶ V` and a sheaf `M` of `𝒪_V`-modules, identifying `q^*(M ⊗ 𝒪_V)` with
`q^*M ⊗ q^*𝒪_V`, then `q^*𝒪_V` with `𝒪_W`, then cancelling the unit, is `q^*` applied to
`M ⊗ 𝒪_V ≅ M`.

This is `Stacks.RingedSpace.comparison_rightUnitor` using the native sheaf tensor bifunctor, the
bridge being `AlgebraicGeometry.tensorLeftFunctorObjUnitSchemeIso_hom`.

`Stacks.RingedSpace.comparison_rightUnitor` names the middle factor through the *uncurried*
bifunctor, applied to the pair `(𝟙, ν)`, whereas the statement here uses the partially applied
`(sheafTensor 𝒪_W).obj (q^*M)` — the form every consumer of this lemma rewrites with.  The two
are the same morphism, by `Stacks.SheafOfModules.Tensor.sheafTensor_uncurry_map` and
`Stacks.SheafOfModules.Tensor.sheafTensor_obj_map`, which both compute it as the sheafification
of one presheaf-level `tensorHom`; that identification is `bifunctor` below. -/
theorem tensorLeftFunctorCompPullback_hom_app_unit {V W : Scheme.{u}} (q : W ⟶ V)
    (M : V.Modules) :
    ((tensorLeftFunctorCompPullback q.toLRSHom.toShHom W.ringCatSheaf.2 V.ringCatSheaf.2
            M).hom.app (SheafOfModules.unit V.ringCatSheaf)) ≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} W.sheaf).obj
            ((Scheme.Modules.pullback q).obj M)).map
          (Scheme.Modules.pullbackUnitIso q).hom ≫
        (tensorLeftFunctorObjUnitSchemeIso ((Scheme.Modules.pullback q).obj M)).hom =
      (Scheme.Modules.pullback q).map (tensorLeftFunctorObjUnitSchemeIso M).hom := by
  have bifunctor := (Stacks.SheafOfModules.Tensor.sheafTensor_uncurry_map.{u, u, u, u, u} W.sheaf
      (𝟙 ((Scheme.Modules.pullback q).obj M)) (Scheme.Modules.pullbackUnitIso q).hom).trans
    (Stacks.SheafOfModules.Tensor.sheafTensor_obj_map.{u, u, u, u, u} W.sheaf
      ((Scheme.Modules.pullback q).obj M) (Scheme.Modules.pullbackUnitIso q).hom).symm
  exact (congrArg
      (fun k ↦ ((tensorLeftFunctorCompPullback q.toLRSHom.toShHom W.ringCatSheaf.2
            V.ringCatSheaf.2 M).hom.app (SheafOfModules.unit V.ringCatSheaf)) ≫
          ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} W.sheaf).obj
              ((Scheme.Modules.pullback q).obj M)).map
            (Scheme.Modules.pullbackUnitIso q).hom ≫ k)
      (tensorLeftFunctorObjUnitSchemeIso_hom ((Scheme.Modules.pullback q).obj M))).trans
    ((congrArg
        (fun k ↦ ((tensorLeftFunctorCompPullback q.toLRSHom.toShHom W.ringCatSheaf.2
              V.ringCatSheaf.2 M).hom.app (SheafOfModules.unit V.ringCatSheaf)) ≫ k ≫
            (Stacks.RingedSpace.tensorSheafUnitRightIso W.toRingedSpace
              ((Scheme.Modules.pullback q).obj M)).hom)
        bifunctor.symm).trans
      ((Stacks.RingedSpace.comparison_rightUnitor q.toLRSHom.toShHom M).trans
        (congrArg (fun k ↦ (Scheme.Modules.pullback q).map k)
          (tensorLeftFunctorObjUnitSchemeIso_hom M).symm)))

/-- The underlying sheaf of modules of the quasi-coherent unit `quasicoherentUnit X` is the
structure sheaf of `X`. -/
@[simp]
theorem quasicoherentUnit_obj (X : Scheme.{u}) :
    (quasicoherentUnit X).obj = SheafOfModules.unit X.ringCatSheaf :=
  rfl

/-- The component at `A` of the inverse of `quasicoherentRestrictionCompIotaIsoPullback V` is the
component at the underlying sheaf of `A` of the inverse of
`AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback V.ι`. -/
theorem quasicoherentRestrictionCompIotaIsoPullback_inv_app {Y : Scheme.{u}} (V : Y.Opens)
    (A : (SheafOfModules.isQuasicoherent Y.ringCatSheaf).FullSubcategory) :
    (quasicoherentRestrictionCompIotaIsoPullback V).inv.app A =
      (Scheme.Modules.restrictFunctorIsoPullback V.ι).inv.app A.obj := by
  rfl

/-- The component at `A` of `pullbackTensorFunctorQuasicoherentRestrictIso U b N` is `N ⊗ -`
applied to `b^*` of the identification of `A|_U` with `(U.ι)^*A`, followed by `N ⊗ -` applied to
the identification of `b^*(U.ι)^*A` with `(b ≫ U.ι)^*A`. -/
theorem pullbackTensorFunctorQuasicoherentRestrictIso_hom_app {W S : Scheme.{u}} (U : S.Opens)
    (b : W ⟶ U.toScheme) (N : SheafOfModules.{u} W.ringCatSheaf)
    (A : (SheafOfModules.isQuasicoherent S.ringCatSheaf).FullSubcategory) :
    (pullbackTensorFunctorQuasicoherentRestrictIso U b N).hom.app A =
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} W.sheaf).obj N).map
          ((Scheme.Modules.pullback b).map
            ((Scheme.Modules.restrictFunctorIsoPullback U.ι).hom.app A.obj)) ≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} W.sheaf).obj N).map
          ((Scheme.Modules.pullbackComp b U.ι).hom.app A.obj) := by
  have h : (pullbackTensorFunctorQuasicoherentRestrictIso U b N).hom.app A =
      (Scheme.Modules.pullback b ⋙
          (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} W.sheaf).obj N).map
          (𝟙 ((Scheme.Modules.restrictFunctor U.ι).obj A.obj)) ≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} W.sheaf).obj N).map
          ((Scheme.Modules.pullback b).map
            ((Scheme.Modules.restrictFunctorIsoPullback U.ι).hom.app A.obj)) ≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} W.sheaf).obj N).map
          ((Scheme.Modules.pullbackComp b U.ι).hom.app A.obj) := rfl
  rw [h, CategoryTheory.Functor.map_id, Category.id_comp]

/-- The component at `A` of `pullbackTensorFunctorPullbackIso g q L` is the comparison
`q^*(L ⊗ g^*A) ≅ q^*L ⊗ q^*g^*A` followed by `q^*L ⊗ -` applied to the identification of
`q^*g^*A` with `(q ≫ g)^*A`. -/
theorem pullbackTensorFunctorPullbackIso_hom_app {S V W : Scheme.{u}} (g : V ⟶ S) (q : W ⟶ V)
    (L : SheafOfModules.{u} V.ringCatSheaf)
    (A : (SheafOfModules.isQuasicoherent S.ringCatSheaf).FullSubcategory) :
    (pullbackTensorFunctorPullbackIso g q L).hom.app A =
      (tensorLeftFunctorCompPullback q.toLRSHom.toShHom W.ringCatSheaf.2 V.ringCatSheaf.2
            L).hom.app ((Scheme.Modules.pullback g).obj A.obj) ≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} W.sheaf).obj
            ((Scheme.Modules.pullback q).obj L)).map
          ((Scheme.Modules.pullbackComp q g).hom.app A.obj) := by
  rfl

/-- The component at `A` of `pullbackTensorFunctorIsoOfSheafIso g e` is the morphism
`N ⊗ g^*A ≅ N' ⊗ g^*A` induced by `e : N ≅ N'`. -/
theorem pullbackTensorFunctorIsoOfSheafIso_hom_app {X W : Scheme.{u}} (g : W ⟶ X)
    {N N' : SheafOfModules.{u} W.ringCatSheaf} (e : N ≅ N')
    (A : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory) :
    (pullbackTensorFunctorIsoOfSheafIso g e).hom.app A =
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} W.sheaf).mapIso
        (X := N) (Y := N') e).hom.app ((Scheme.Modules.pullback g).obj A.obj) := by
  rfl

/-- The component at `A` of `pullbackTensorFunctorCongr h N` is `N ⊗ -` applied to the
identification of `g^*A` with `g'^*A` induced by `h : g = g'`. -/
theorem pullbackTensorFunctorCongr_hom_app {X W : Scheme.{u}} {g g' : W ⟶ X} (h : g = g')
    (N : SheafOfModules.{u} W.ringCatSheaf)
    (A : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory) :
    (pullbackTensorFunctorCongr h N).hom.app A =
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} W.sheaf).obj N).map
        ((Scheme.Modules.pullbackCongr h).hom.app A.obj) :=
  rfl

/-- The component at `A` of `moduleChartPullbackIso g M f L hg hres` is the composite of the
components at `A` of `pullbackTensorFunctorPullbackIso`, `pullbackTensorFunctorCongr hg` and
`pullbackTensorFunctorIsoOfSheafIso` applied to the identification of `(V.ι)^*M` with `L`. -/
theorem moduleChartPullbackIso_hom_app {X Y : Scheme.{u}} (g : Y ≅ X) (M : Y.Modules)
    {V : Y.Opens} {U : X.Opens} (f : V.toScheme ≅ U.toScheme)
    (L : SheafOfModules.{u} V.toScheme.ringCatSheaf)
    (hg : V.ι ≫ g.hom = f.hom ≫ U.ι) (hres : Scheme.Modules.restrict M V.ι ≅ L)
    (A : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory) :
    (moduleChartPullbackIso g M f L hg hres).hom.app A =
      (pullbackTensorFunctorPullbackIso g.hom V.ι M).hom.app A ≫
        (pullbackTensorFunctorCongr hg ((Scheme.Modules.pullback V.ι).obj M)).hom.app A ≫
        (pullbackTensorFunctorIsoOfSheafIso (f.hom ≫ U.ι)
          (((Scheme.Modules.restrictFunctorIsoPullback V.ι).app M).symm ≪≫ hres)).hom.app A :=
  rfl

/-- The component at `A` of `chartComparisonPullbackIso` is the component at `A` of
`chartPullbackIso E f L α β` followed by that of the inverse of `moduleChartPullbackIso`. -/
theorem chartComparisonPullbackIso_hom_app {X Y : Scheme.{u}}
    (E : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory ⥤
      (SheafOfModules.isQuasicoherent Y.ringCatSheaf).FullSubcategory)
    (g : Y ≅ X) (M : Y.Modules) {V : Y.Opens} {U : X.Opens}
    {F : (SheafOfModules.isQuasicoherent U.toScheme.ringCatSheaf).FullSubcategory ⥤
      (SheafOfModules.isQuasicoherent V.toScheme.ringCatSheaf).FullSubcategory}
    (f : V.toScheme ≅ U.toScheme) (L : SheafOfModules.{u} V.toScheme.ringCatSheaf)
    (α : E ⋙ quasicoherentRestriction V.ι ≅ quasicoherentRestriction U.ι ⋙ F)
    (β : F ⋙ ObjectProperty.ι (SheafOfModules.isQuasicoherent V.toScheme.ringCatSheaf) ≅
      pullbackTensorFunctor f.hom L)
    (hg : V.ι ≫ g.hom = f.hom ≫ U.ι) (hres : Scheme.Modules.restrict M V.ι ≅ L)
    (A : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory) :
    (chartComparisonPullbackIso E g M f L α β hg hres).hom.app A =
      (chartPullbackIso E f L α β).hom.app A ≫
        (moduleChartPullbackIso g M f L hg hres).inv.app A :=
  rfl

/-- The component at `A` of `chartComparisonIso` is the component at `A` of
`chartComparisonPullbackIso`, conjugated by the identifications of restriction to `V` with
inverse image along `V.ι`. -/
theorem chartComparisonIso_hom_app {X Y : Scheme.{u}}
    (E : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory ⥤
      (SheafOfModules.isQuasicoherent Y.ringCatSheaf).FullSubcategory)
    (g : Y ≅ X) (M : Y.Modules) {V : Y.Opens} {U : X.Opens}
    {F : (SheafOfModules.isQuasicoherent U.toScheme.ringCatSheaf).FullSubcategory ⥤
      (SheafOfModules.isQuasicoherent V.toScheme.ringCatSheaf).FullSubcategory}
    (f : V.toScheme ≅ U.toScheme) (L : SheafOfModules.{u} V.toScheme.ringCatSheaf)
    (α : E ⋙ quasicoherentRestriction V.ι ≅ quasicoherentRestriction U.ι ⋙ F)
    (β : F ⋙ ObjectProperty.ι (SheafOfModules.isQuasicoherent V.toScheme.ringCatSheaf) ≅
      pullbackTensorFunctor f.hom L)
    (hg : V.ι ≫ g.hom = f.hom ≫ U.ι) (hres : Scheme.Modules.restrict M V.ι ≅ L)
    (A : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory) :
    (chartComparisonIso E g M f L α β hg hres).hom.app A =
      (Scheme.Modules.restrictFunctorIsoPullback V.ι).hom.app (E.obj A).obj ≫
        (chartComparisonPullbackIso E g M f L α β hg hres).hom.app A ≫
        (Scheme.Modules.restrictFunctorIsoPullback V.ι).inv.app
          ((pullbackTensorFunctor g.hom M).obj A) :=
  rfl

/-- The chart's identification of `(f ≫ U.ι)^*𝒪_X` with `𝒪_V` is the canonical one. -/
theorem chartUnitChain {X Y : Scheme.{u}} {V : Y.Opens} {U : X.Opens}
    (f : V.toScheme ≅ U.toScheme) :
    (Scheme.Modules.pullback f.hom).map
          ((Scheme.Modules.restrictFunctorIsoPullback U.ι).hom.app
            (SheafOfModules.unit X.ringCatSheaf)) ≫
        (Scheme.Modules.pullbackComp f.hom U.ι).hom.app (SheafOfModules.unit X.ringCatSheaf) ≫
        (Scheme.Modules.pullbackUnitIso (f.hom ≫ U.ι)).hom =
      (Scheme.Modules.pullback f.hom).map (Scheme.Modules.restrictUnitIso U.ι).hom ≫
        (Scheme.Modules.pullbackUnitIso f.hom).hom := by
  have hcomp : (Scheme.Modules.pullbackComp f.hom U.ι).inv.app
        (SheafOfModules.unit X.ringCatSheaf) ≫
        (Scheme.Modules.pullback f.hom).map (Scheme.Modules.pullbackUnitIso U.ι).hom ≫
        (Scheme.Modules.pullbackUnitIso f.hom).hom =
      (Scheme.Modules.pullbackUnitIso (f.hom ≫ U.ι)).hom :=
    Scheme.Modules.pullbackUnitIso_comp f.hom U.ι
  have hB1 := restrictFunctorIsoPullback_inv_app_unit_comp_restrictUnitIso U
  rw [← hcomp, ← hB1]
  simp

section Chart

variable {X Y : Scheme.{u}}
  (E : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory ⥤
    (SheafOfModules.isQuasicoherent Y.ringCatSheaf).FullSubcategory)
  {V : Y.Opens} {U : X.Opens}
  {F : (SheafOfModules.isQuasicoherent U.toScheme.ringCatSheaf).FullSubcategory ⥤
    (SheafOfModules.isQuasicoherent V.toScheme.ringCatSheaf).FullSubcategory}
  (f : V.toScheme ≅ U.toScheme) (L : SheafOfModules.{u} V.toScheme.ringCatSheaf)
  (α : E ⋙ quasicoherentRestriction V.ι ≅ quasicoherentRestriction U.ι ⋙ F)
  (β : F ⋙ ObjectProperty.ι (SheafOfModules.isQuasicoherent V.toScheme.ringCatSheaf) ≅
    pullbackTensorFunctor f.hom L)

/-- The component at `A` of `chartPullbackIso E f L α β` is the composite of the inverse of
`quasicoherentRestrictionCompIotaIsoPullback V` at `E.obj A`, the component of `α` at `A`, the
component of `β` at `A|_U`, and the component of `pullbackTensorFunctorQuasicoherentRestrictIso`
at `A`. -/
theorem chartPullbackIso_hom_app
    (A : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory) :
    (chartPullbackIso E f L α β).hom.app A =
      (quasicoherentRestrictionCompIotaIsoPullback V).inv.app (E.obj A) ≫
        (ObjectProperty.ι (SheafOfModules.isQuasicoherent V.toScheme.ringCatSheaf)).map
          (α.app A).hom ≫
        (β.app ((quasicoherentRestriction U.ι).obj A)).hom ≫
        (pullbackTensorFunctorQuasicoherentRestrictIso U f.hom L).hom.app A :=
  rfl

/-- The isomorphism `restrictMapUnitIsoOfChartIso E f L α β` is the composite of the component of
`α` at the unit, the component of `β` at `𝒪_X|_U`, `L ⊗ -` applied to the identification of
`f^*(𝒪_X|_U)` with `𝒪_V`, and the right unitor `L ⊗ 𝒪_V ≅ L`. -/
theorem restrictMapUnitIsoOfChartIso_hom :
    (restrictMapUnitIsoOfChartIso E f L α β).hom =
      (ObjectProperty.ι (SheafOfModules.isQuasicoherent V.toScheme.ringCatSheaf)).map
          (α.app (quasicoherentUnit X)).hom ≫
        (β.app ((quasicoherentRestriction U.ι).obj (quasicoherentUnit X))).hom ≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} V.toScheme.sheaf).obj L).map
          ((Scheme.Modules.pullback f.hom).map (Scheme.Modules.restrictUnitIso U.ι).hom ≫
            (Scheme.Modules.pullbackUnitIso f.hom).hom) ≫
        (tensorLeftFunctorObjUnitSchemeIso L).hom :=
  rfl

end Chart

end AlgebraicGeometry

end
