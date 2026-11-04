module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PushforwardSectionAction
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPullbackIdealAction
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.CoextensionModel
public import StacksFrontier.AlgebraicGeometry.Spaces.AffinePushforwardRightAdjoint
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentAdicExactnessLocal
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleLocalizationOfDirectImages

/-!
# The action of a section of `π_*𝒪_Y` after étale restriction, and the trace on its image

Let `π : Y ⟶ X` be a morphism of algebraic spaces with direct-image algebra `𝒜 = π_*𝒪_Y`, let
`g : U ⟶ X` be étale, and let `ε : 𝒪_U ⟶ g^*𝒜` be a global section of the restriction of `𝒜`
to `U`.  For every `𝒜`-module `ℳ` on `X`, multiplication by `ε(1)` is an endomorphism

`μ_ε : g^*ℳ ⟶ g^*ℳ`

of `𝒪_U`-modules, natural in `ℳ` along morphisms of `𝒜`-modules.

The main result is about the counit `c : 𝓗om_{𝒪_X}(𝒜, ℱ) ⟶ ℱ` of restriction and coextension of
scalars along `π♯ : 𝒪_X ⟶ 𝒜`, for the abstractly produced right adjoint
`AlgebraicGeometry.Space.directImageAlgebraCoextendScalars`:

* if `ε` is a **split** monomorphism, then `μ_ε` followed by the restriction of `c` is an
  **epimorphism** onto `g^*ℱ`.

That is, `c` is already surjective on the part of `Coext ℱ` cut out by the section `ε(1)`.

## Main definitions

* `etaleSectionAction`: the endomorphism `μ_ε`.
* `directImageCoextensionModel`: the sectionwise model of the coextension of scalars along `π♯`,
  at the module universe of the schemes.

## Main results

* `etaleSectionAction_naturality`: `μ_ε` is natural.
* `epi_etaleSectionAction_comp_map_counit`: the epimorphism above.

## References

* [Stacks Project, Tag 0GUZ](https://stacks.math.columbia.edu/tag/0GUZ)
* [Stacks Project, Tag 0932](https://stacks.math.columbia.edu/tag/0932)
* [Stacks Project, Tag 04M0](https://stacks.math.columbia.edu/tag/04M0)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

/-- The inverse of the slice transport of Stacks 04M0, evaluated at the image of the identity of
`W`, is the original local morphism evaluated at the identity. -/
theorem Stacks.SheafOfModules.InternalHom.sliceEquivSectionEquiv_symm_app_mk_map_id
    {X Y : AlgebraicGeometry.RingedSite.{u + 1, u, u}} (F : Y.C ⥤ X.C)
    [F.IsContinuous Y.J X.J] [F.IsCocontinuous Y.J X.J]
    [hF : ∀ W : Y.C, (Over.post (X := W) F).IsEquivalence]
    (φ : (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) ⟶
      (F.sheafPushforwardContinuous RingCat.{u} Y.J X.J).obj
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) [IsIso φ]
    (A B : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (W : Y.C)
    (hW : (restrFun Y.O.obj W).obj ((SheafOfModules.pushforward.{u} φ).obj A).val ⟶
      (restrFun Y.O.obj W).obj ((SheafOfModules.pushforward.{u} φ).obj B).val)
    (x : A.val.obj (op (F.obj W))) :
    (((Stacks.SheafOfModules.InternalHom.sliceEquivSectionEquiv F φ A B W).symm hW :
        (restrFun X.O.obj (F.obj W)).obj A.val ⟶ (restrFun X.O.obj (F.obj W)).obj B.val).app
          (op (Over.mk (F.map (𝟙 W))))).hom x =
      (hW.app (AlgebraicGeometry.RingedSite.overId Y W)).hom x :=
  congrArg (fun α : (restrFun Y.O.obj W).obj ((SheafOfModules.pushforward.{u} φ).obj A).val ⟶
      (restrFun Y.O.obj W).obj ((SheafOfModules.pushforward.{u} φ).obj B).val =>
        (α.app (AlgebraicGeometry.RingedSite.overId Y W)).hom x)
    ((Stacks.SheafOfModules.InternalHom.sliceEquivSectionEquiv F φ A B W).apply_symm_apply hW)

/-- The inverse of the slice transport of Stacks 04M0, evaluated at the identity of `F(W)`, is the
original local morphism evaluated at the identity of `W`. -/
theorem Stacks.SheafOfModules.InternalHom.sliceEquivSectionEquiv_symm_app_overId
    {X Y : AlgebraicGeometry.RingedSite.{u + 1, u, u}} (F : Y.C ⥤ X.C)
    [F.IsContinuous Y.J X.J] [F.IsCocontinuous Y.J X.J]
    [hF : ∀ W : Y.C, (Over.post (X := W) F).IsEquivalence]
    (φ : (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) ⟶
      (F.sheafPushforwardContinuous RingCat.{u} Y.J X.J).obj
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) [IsIso φ]
    (A B : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (W : Y.C)
    (hW : (restrFun Y.O.obj W).obj ((SheafOfModules.pushforward.{u} φ).obj A).val ⟶
      (restrFun Y.O.obj W).obj ((SheafOfModules.pushforward.{u} φ).obj B).val)
    (x : A.val.obj (op (F.obj W))) :
    (((Stacks.SheafOfModules.InternalHom.sliceEquivSectionEquiv F φ A B W).symm hW :
        (restrFun X.O.obj (F.obj W)).obj A.val ⟶ (restrFun X.O.obj (F.obj W)).obj B.val).app
          (AlgebraicGeometry.RingedSite.overId X (F.obj W))).hom x =
      (hW.app (AlgebraicGeometry.RingedSite.overId Y W)).hom x :=
  (AlgebraicGeometry.RingedSite.app_overId_eq_app_mk_map_id X F W _ x).trans
    (Stacks.SheafOfModules.InternalHom.sliceEquivSectionEquiv_symm_app_mk_map_id F φ A B W hW x)

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {Y X U : AlgebraicSpaces B S hS} (π : Y ⟶ X) (g : U ⟶ X) (hg : IsEtale B S hS g.hom)

/-- `𝒜 = π_*𝒪_Y` as an `𝒪_X`-module, in the spelling of restriction of scalars of the free
rank-one `𝒜`-module.  It is `AlgebraicGeometry.Space.pushforwardStructureModule` on the nose
(`AlgebraicGeometry.Space.restrictScalars_unit_structureRingSheafDirectImage`). -/
abbrev directImageAlgebraUnitModule : Modules.{u, u} B S hS X.1 X.2 :=
  (directImageAlgebraRestrictScalars B S hS π).obj
    (SheafOfModules.unit (structureRingSheafDirectImage B S hS π))

variable (ε : SheafOfModules.unit (structureRingSheaf B S hS U) ⟶
      (etaleModulePullback B S hS g hg).obj (directImageAlgebraUnitModule B S hS π))

/-- The value `ε(1)` of the global section `ε` over an étale chart `T` of `U`, as a section of
`𝒜 = π_*𝒪_Y` over the composite chart of `X`. -/
abbrev etaleSectionValue (T : (SmallEtale B S hS U.1)ᵒᵖ) :
    (structureRingSheafDirectImage B S hS π).obj.obj
      (op ((smallEtalePostcomp B S hS g hg).obj T.unop)) :=
  (ε.val.app T).hom (show (structureRingSheaf B S hS U).obj.obj T from 1)

/-- The values `ε(1)` are compatible with restriction along morphisms of étale charts of `U`. -/
theorem etaleSectionValue_map {T T' : (SmallEtale B S hS U.1)ᵒᵖ} (f : T ⟶ T') :
    ((structureRingSheafDirectImage B S hS π).obj.map
        ((smallEtalePostcomp B S hS g hg).map f.unop).op).hom
      (etaleSectionValue B S hS π g hg ε T) = etaleSectionValue B S hS π g hg ε T' := by
  have h := congrArg (fun φ => φ.hom (show (structureRingSheaf B S hS U).obj.obj T from 1))
    (ε.val.naturality f)
  have h1 : ((SheafOfModules.unit (structureRingSheaf B S hS U)).val.map f).hom
      (show (structureRingSheaf B S hS U).obj.obj T from 1) =
        (show (structureRingSheaf B S hS U).obj.obj T' from 1) :=
    map_one ((structureRingSheaf B S hS U).obj.map f).hom
  change (ε.val.app T').hom (((SheafOfModules.unit (structureRingSheaf B S hS U)).val.map f).hom
      (show (structureRingSheaf B S hS U).obj.obj T from 1)) =
    (((etaleModulePullback B S hS g hg).obj (directImageAlgebraUnitModule B S hS π)).val.map f).hom
      ((ε.val.app T).hom (show (structureRingSheaf B S hS U).obj.obj T from 1)) at h
  rw [h1] at h
  exact h.symm

variable (M : SheafOfModules.{u} (structureRingSheafDirectImage B S hS π))

/-- **Multiplication by the section `ε(1)`** on the restriction to `U` of an `𝒜`-module, as an
endomorphism of `𝒪_U`-modules. -/
def etaleSectionAction :
    (etaleModulePullback B S hS g hg).obj ((directImageAlgebraRestrictScalars B S hS π).obj M) ⟶
      (etaleModulePullback B S hS g hg).obj ((directImageAlgebraRestrictScalars B S hS π).obj M) :=
  Stacks.SheafOfModules.pushforwardSectionAction (J := SmallEtale.topology B S hS U.1)
    (K := SmallEtale.topology B S hS X.1)
    (𝒮 := Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS U.1 U.2).O)
    (ℛ := structureRingSheaf B S hS X) (𝒜 := structureRingSheafDirectImage B S hS π)
    (smallEtalePostcomp B S hS g hg)
    (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS U.1 U.2).O))
    (structureSharp B S hS π) (mul_comm_structureRingSheafDirectImage B S hS π)
    (etaleSectionValue B S hS π g hg ε) (etaleSectionValue_map B S hS π g hg ε) M

/-- On sections over an étale chart `T` of `U`, `μ_ε` is multiplication by `ε(1)`. -/
theorem etaleSectionAction_app_apply (T : (SmallEtale B S hS U.1)ᵒᵖ)
    (m : M.val.obj (op ((smallEtalePostcomp B S hS g hg).obj T.unop))) :
    ((etaleSectionAction B S hS π g hg ε M).val.app T).hom m =
      (etaleSectionValue B S hS π g hg ε T • m :
        M.val.obj (op ((smallEtalePostcomp B S hS g hg).obj T.unop))) := rfl

variable {M} in
/-- **`μ_ε` is natural** along morphisms of `𝒜`-modules. -/
theorem etaleSectionAction_naturality
    {M' : SheafOfModules.{u} (structureRingSheafDirectImage B S hS π)} (φ : M ⟶ M') :
    (etaleModulePullback B S hS g hg).map ((directImageAlgebraRestrictScalars B S hS π).map φ) ≫
        etaleSectionAction B S hS π g hg ε M' =
      etaleSectionAction B S hS π g hg ε M ≫
        (etaleModulePullback B S hS g hg).map
          ((directImageAlgebraRestrictScalars B S hS π).map φ) :=
  Stacks.SheafOfModules.pushforwardSectionAction_naturality (J := SmallEtale.topology B S hS U.1)
    (K := SmallEtale.topology B S hS X.1)
    (𝒮 := Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS U.1 U.2).O)
    (ℛ := structureRingSheaf B S hS X) (𝒜 := structureRingSheafDirectImage B S hS π)
    (smallEtalePostcomp B S hS g hg)
    (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS U.1 U.2).O))
    (structureSharp B S hS π) (mul_comm_structureRingSheafDirectImage B S hS π)
    (etaleSectionValue B S hS π g hg ε) (etaleSectionValue_map B S hS π g hg ε) φ

/-! ### The sectionwise model of the coextension, and the counit -/

variable (F : Modules.{u, u} B S hS X.1 X.2)

/-- **The sectionwise model `𝓗om_{𝒪_X}(π_*𝒪_Y, ℱ)` of the coextension of scalars along `π♯`**,
as a `π_*𝒪_Y`-module with sections in the universe of the schemes: an instance of
`AlgebraicGeometry.RingedSite.coextensionModel`. -/
abbrev directImageCoextensionModel : SheafOfModules.{u} (structureRingSheafDirectImage B S hS π) :=
  RingedSite.coextensionModel (smallEtaleRingedSite B S hS X.1 X.2) (structureSharp B S hS π)
    (mul_comm_structureRingSheafDirectImage B S hS π) F

/-- The evaluation `h ↦ h(1)` on the sectionwise model. -/
abbrev directImageCoextensionModelEval :
    (directImageAlgebraRestrictScalars B S hS π).obj (directImageCoextensionModel B S hS π F) ⟶
      F :=
  RingedSite.coextensionModelEval (smallEtaleRingedSite B S hS X.1 X.2) (structureSharp B S hS π)
    (mul_comm_structureRingSheafDirectImage B S hS π) F

/-- **The counit is surjective on the part cut out by `ε(1)` as soon as some `𝒜`-module is.**  If
`μ_ε ≫ g^*τ` is an epimorphism for an `𝒜`-module `𝒫` and an `𝒪_X`-linear map `τ : Res 𝒫 ⟶ ℱ`,
then so is `μ_ε ≫ g^*c`, for the counit `c` of restriction and coextension of scalars. -/
theorem epi_etaleSectionAction_comp_map_counit_of_epi
    (P : SheafOfModules.{u} (structureRingSheafDirectImage B S hS π))
    (τ : (directImageAlgebraRestrictScalars B S hS π).obj P ⟶ F)
    (hτ : Epi (etaleSectionAction B S hS π g hg ε P ≫ (etaleModulePullback B S hS g hg).map τ)) :
    Epi (etaleSectionAction B S hS π g hg ε ((directImageAlgebraCoextendScalars B S hS π).obj F) ≫
      (etaleModulePullback B S hS g hg).map
        ((directImageAlgebraRestrictCoextendAdjunction B S hS π).counit.app F)) := by
  set adj := directImageAlgebraRestrictCoextendAdjunction B S hS π
  have hfac : τ = (directImageAlgebraRestrictScalars B S hS π).map (adj.homEquiv P F τ) ≫
      adj.counit.app F := by
    have h := adj.homEquiv_counit (X := P) (Y := F) (g := adj.homEquiv P F τ)
    rwa [Equiv.symm_apply_apply] at h
  rw [hfac, Functor.map_comp, ← Category.assoc, ← etaleSectionAction_naturality,
    Category.assoc] at hτ
  exact epi_of_epi ((etaleModulePullback B S hS g hg).map
    ((directImageAlgebraRestrictScalars B S hS π).map (adj.homEquiv P F τ))) _

/-- **On the sectionwise model, `μ_ε` followed by the evaluation is an epimorphism**, for a split
section `ε`. -/
theorem epi_etaleSectionAction_comp_map_coextensionModelEval
    (pr : (etaleModulePullback B S hS g hg).obj (directImageAlgebraUnitModule B S hS π) ⟶
      SheafOfModules.unit (structureRingSheaf B S hS U))
    (hε : ε ≫ pr = 𝟙 _) :
    Epi (etaleSectionAction B S hS π g hg ε (directImageCoextensionModel B S hS π F) ≫
      (etaleModulePullback B S hS g hg).map (directImageCoextensionModelEval B S hS π F)) := by
  rw [modules_epi_iff_exists_covering B S hS U.1 U.2]
  intro T s
  refine ⟨⊤, (SmallEtale.topology B S hS U.1).top_mem T, fun V k _ => ?_⟩
  obtain ⟨f, hf⟩ : ∃ f : F.val.obj (op ((smallEtalePostcomp B S hS g hg).obj V)),
      f = (((etaleModulePullback B S hS g hg).obj F).val.map k.op).hom s := ⟨_, rfl⟩
  rw [← hf]
  let hV : (restrFun (smallEtaleRingedSite B S hS U.1 U.2).O.obj V).obj
        (RingedSite.valOf _ ((etaleModulePullback B S hS g hg).obj
          (directImageAlgebraUnitModule B S hS π))) ⟶
      (restrFun (smallEtaleRingedSite B S hS U.1 U.2).O.obj V).obj
        (RingedSite.valOf _ ((etaleModulePullback B S hS g hg).obj F)) :=
    (restrFun (smallEtaleRingedSite B S hS U.1 U.2).O.obj V).map (RingedSite.homOf _ pr) ≫
      RingedSite.restrFunSectionHom (smallEtaleRingedSite B S hS U.1 U.2)
        (N := (etaleModulePullback B S hS g hg).obj F) (U := V) f
  let e := @Stacks.SheafOfModules.InternalHom.sliceEquivSectionEquiv.{u + 1, u, u, u}
    (smallEtaleRingedSite B S hS X.1 X.2) (smallEtaleRingedSite B S hS U.1 U.2)
    (smallEtalePostcomp B S hS g hg)
    (smallEtaleRingedSite_isContinuous_smallEtalePostcomp B S hS g hg)
    (smallEtalePostcomp_isCocontinuous B S hS g hg)
    (fun W => SmallEtale.isEquivalence_overPostcomp B S hS g hg W)
    (𝟙 ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS U.1 U.2).O)))
    (IsIso.id _) (directImageAlgebraUnitModule B S hS π) F V
  let h := e.symm hV
  refine ⟨RingedSite.coextensionModelMk (smallEtaleRingedSite B S hS X.1 X.2)
    (structureSharp B S hS π) (mul_comm_structureRingSheafDirectImage B S hS π) F h, ?_⟩
  have key := RingedSite.coextensionModelEval_app_smul_mk (smallEtaleRingedSite B S hS X.1 X.2)
    (structureSharp B S hS π) (mul_comm_structureRingSheafDirectImage B S hS π) F
    ((smallEtalePostcomp B S hS g hg).obj V) (etaleSectionValue B S hS π g hg ε (op V)) h
  have h1 : ((pr.val.app (op V)).hom (etaleSectionValue B S hS π g hg ε (op V))) =
      (show (structureRingSheaf B S hS U).obj.obj (op V) from 1) :=
    congrArg (fun φ => (φ.val.app (op V)).hom
      (show (structureRingSheaf B S hS U).obj.obj (op V) from 1)) hε
  refine key.trans
    ((@Stacks.SheafOfModules.InternalHom.sliceEquivSectionEquiv_symm_app_overId _ _ _
      (smallEtaleRingedSite_isContinuous_smallEtalePostcomp B S hS g hg)
      (smallEtalePostcomp_isCocontinuous B S hS g hg)
      (fun W => SmallEtale.isEquivalence_overPostcomp B S hS g hg W) _ (IsIso.id _) _ _ _ hV
      (etaleSectionValue B S hS π g hg ε (op V))).trans ?_)
  exact RingedSite.restrFun_map_comp_restrFunSectionHom_app_overId
    (smallEtaleRingedSite B S hS U.1 U.2) (U := V)
    (A := (etaleModulePullback B S hS g hg).obj (directImageAlgebraUnitModule B S hS π))
    (N := (etaleModulePullback B S hS g hg).obj F) pr f
    (etaleSectionValue B S hS π g hg ε (op V)) h1

/-- **The counit of restriction and coextension of scalars is surjective on the part cut out by a
split section.**  For a split monomorphism `ε : 𝒪_U ⟶ g^*𝒜`, multiplication by `ε(1)` on the
restriction of `Coext ℱ` followed by the restriction of the counit `c : Res(Coext ℱ) ⟶ ℱ` is an
epimorphism onto `g^*ℱ`. -/
theorem epi_etaleSectionAction_comp_map_counit
    (pr : (etaleModulePullback B S hS g hg).obj (directImageAlgebraUnitModule B S hS π) ⟶
      SheafOfModules.unit (structureRingSheaf B S hS U))
    (hε : ε ≫ pr = 𝟙 _) :
    Epi (etaleSectionAction B S hS π g hg ε ((directImageAlgebraCoextendScalars B S hS π).obj F) ≫
      (etaleModulePullback B S hS g hg).map
        ((directImageAlgebraRestrictCoextendAdjunction B S hS π).counit.app F)) :=
  epi_etaleSectionAction_comp_map_counit_of_epi B S hS π g hg ε F
    (directImageCoextensionModel B S hS π F) (directImageCoextensionModelEval B S hS π F)
    (epi_etaleSectionAction_comp_map_coextensionModelEval B S hS π g hg ε F pr hε)

end AlgebraicGeometry.Space

/-! ### Vanishing of the action on a module killed by an ideal -/

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {Y X U : AlgebraicSpaces B S hS} (π : Y ⟶ X) (g : U ⟶ X) (hg : IsEtale B S hS g.hom)

/-- **A section of `π_*ℐ` acts by zero on `π_*𝒬` when `ℐ · 𝒬 = 0`**: if `ε` factors through the
restriction of `π_*ℐ ⟶ π_*𝒪_Y` for a sheaf of ideals `ℐ` killing `𝒬` sectionwise, then
multiplication by `ε(1)` on the restriction of `π_*𝒬` vanishes. -/
theorem etaleSectionAction_moduleDirectImage_eq_zero (Q : Modules.{u, u} B S hS Y.1 Y.2)
    (K : (SheafOfModules.unit
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O)).Submodule)
    (hK : ∀ (W : (smallEtaleRingedSite B S hS Y.1 Y.2).Cᵒᵖ)
      (r : (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS Y.1 Y.2).O).obj.obj W),
      r ∈ K.obj W → ∀ q : Q.val.obj W, r • q = 0)
    (εK : SheafOfModules.unit (structureRingSheaf B S hS U) ⟶
      (etaleModulePullback B S hS g hg).obj ((modulePushforward B S hS π).obj K.toSheafOfModules)) :
    etaleSectionAction B S hS π g hg
        (εK ≫ (etaleModulePullback B S hS g hg).map ((modulePushforward B S hS π).map K.ι) :
          SheafOfModules.unit (structureRingSheaf B S hS U) ⟶
            (etaleModulePullback B S hS g hg).obj (pushforwardStructureModule B S hS π))
        ((moduleDirectImage B S hS π).obj Q) = 0 := by
  ext T x
  exact CategoryTheory.Sheaf.moduleSMulObj_map_idealSetInclusion_of_smul_eq_zero
    (structureRingSheaf B S hS Y) Q K
    (smallEtaleDirectImage B S hS π ⋙
      CategoryTheory.Sheaf.sectionsFunctor _ (op ((smallEtalePostcomp B S hS g hg).obj T.unop))) hK
    ((εK.val.app T).hom (show (structureRingSheaf B S hS U).obj.obj T from 1)) x

end AlgebraicGeometry.Space

/-! ### Surjectivity from surjectivity on a part that lies in the image -/

/-- **Surjectivity from a surjective part lying in the image.**  If `μ ≫ c` is an epimorphism and
`μ` kills every morphism that kills `ψ`, then `ψ ≫ c` is an epimorphism. -/
theorem CategoryTheory.epi_comp_of_epi_comp_of_forall_comp_eq_zero {𝒞 : Type*} [Category 𝒞]
    [Preadditive 𝒞] {P G F : 𝒞} (ψ : P ⟶ G) (μ : G ⟶ G) (c : G ⟶ F)
    (hμc : Epi (μ ≫ c)) (hμ : ∀ ⦃Z : 𝒞⦄ (d : G ⟶ Z), ψ ≫ d = 0 → μ ≫ d = 0) :
    Epi (ψ ≫ c) := by
  refine Preadditive.epi_of_cancel_zero _ fun {Z} d hd => ?_
  have h := hμ (c ≫ d) (by rw [← Category.assoc, hd])
  rw [← Category.assoc] at h
  exact (cancel_epi (μ ≫ c)).1 (h.trans (Limits.comp_zero).symm)
